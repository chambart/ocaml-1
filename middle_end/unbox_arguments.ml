(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                       Pierre Chambart, OCamlPro                        *)
(*           Mark Shinwell and Leo White, Jane Street Europe              *)
(*                                                                        *)
(*   Copyright 2013--2017 OCamlPro SAS                                    *)
(*   Copyright 2014--2017 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

[@@@ocaml.warning "+a-4-9-30-40-41-42"]

module Argument = struct
  type t = Closure_id.t * int
  include Identifiable.Make(Identifiable.Pair(Closure_id)(Numbers.Int))
end

type variable_use =
  | Anything_else
  | Argument_of of Argument.Set.t
  | Only_unboxed
  | Unused

let union_use u1 u2 = match u1, u2 with
  | Unused, u | u, Unused -> u
  | Only_unboxed, u | u, Only_unboxed -> u
  | Anything_else, _ | _, Anything_else -> Anything_else
  | Argument_of s1, Argument_of s2 ->
    Argument_of (Argument.Set.union s1 s2)

type collection =
  { variable_usage : variable_use Variable.Tbl.t; }
[@@unboxed]

type argument_declaration =
  { variable_argument : (Argument.t * Flambda.param_type) Variable.Tbl.t }
[@@unboxed]

let add (c:collection) use v =
  let prev_use =
    match Variable.Tbl.find c.variable_usage v with
    | exception Not_found ->
      Unused
    | prev_use ->
      prev_use
  in
  Variable.Tbl.add c.variable_usage v (union_use use prev_use)

let collect_named (c:collection) (named:Flambda.named) =
  match named with
  | Prim (Punbox_float, [arg], _dbg) ->
    add c Only_unboxed arg
  | Prim (_prim, args, _dbg) ->
    List.iter (add c Anything_else) args
  | Expr _ ->
    ()
  | _ ->
    Variable.Set.iter (add c Anything_else)
      (Flambda.free_variables_named named)

let collect_expr (c:collection) (expr:Flambda.t) =
  match expr with
  | Apply { func; args; kind = Indirect } ->
    List.iter (add c Anything_else) args;
    add c Anything_else func
  | Apply { func; args; kind = Direct closure_id } ->
    List.iteri (fun i v ->
      add c (Argument_of (Argument.Set.singleton (closure_id, i))) v)
      args;
    add c Anything_else func
  | Var v ->
    add c Anything_else v
  | Let _ | Let_rec _ ->
    ()
  | Let_mutable { initial_value } ->
    add c Anything_else initial_value
  | Send { meth; obj; args } ->
    List.iter (add c Anything_else) args;
    add c Anything_else meth;
    add c Anything_else obj
  | Assign { new_value } ->
    add c Anything_else new_value
  | If_then_else (cond, _, _)
  | Switch (cond,_)
  | String_switch (cond, _, _) ->
    add c Anything_else cond
  | Static_raise (_, args) ->
    List.iter (add c Anything_else) args
  | Static_catch _
  | Try_with _
  | While _
  | Proved_unreachable ->
    ()
  | For { from_value; to_value } ->
    add c Anything_else from_value;
    add c Anything_else to_value

let collect_argument_use (a:argument_declaration)
    ~constant:_
    (set_of_closures:Flambda.set_of_closures) =
  Variable.Map.iter (fun fun_var (decl:Flambda.function_declaration) ->
    let closure_id = Closure_id.wrap fun_var in
    List.iteri (fun i (v, typ) ->
      Variable.Tbl.add a.variable_argument v ((closure_id, i), typ))
      decl.params)
    set_of_closures.function_decls.funs

let collect_usage program =
  let c = { variable_usage = Variable.Tbl.create 10; } in
  Flambda_iterators.iter_exprs_at_toplevel_of_program program
    ~f:(fun expr ->
      Flambda_iterators.iter
        (collect_expr c)
        (collect_named c)
        expr);
  let a = { variable_argument = Variable.Tbl.create 10 } in
  Flambda_iterators.iter_on_set_of_closures_of_program program
    ~f:(collect_argument_use a);
  c, a

let argument_to_var (c:collection) : Variable.Set.t Argument.Map.t =
  Variable.Tbl.fold (fun v use acc ->
    match use with
    | Argument_of arguments ->
      Argument.Set.fold (fun arg acc ->
        let set =
          match Argument.Map.find arg acc with
          | exception Not_found ->
            Variable.Set.singleton v
          | set ->
            Variable.Set.add v set
        in
        Argument.Map.add arg set acc)
        arguments acc
    | _ ->
      acc)
    c.variable_usage Argument.Map.empty

let fixpoint_step
    ({variable_argument}:argument_declaration)
    (argument_to_var:Variable.Set.t Argument.Map.t)
    (used_boxed:Variable.t Queue.t)
    (not_unboxable:Argument.Set.t) =
  let var = Queue.pop used_boxed in
  match Variable.Tbl.find variable_argument var with
  | exception Not_found ->
    not_unboxable
  | (arg, _typ) ->
    if Argument.Set.mem arg not_unboxable then
      not_unboxable
    else
      let not_unboxable = Argument.Set.add arg not_unboxable in
      (match Argument.Map.find arg argument_to_var with
       | exception Not_found ->
         ()
       | new_used_boxed ->
         Variable.Set.iter (fun v -> Queue.push v used_boxed) new_used_boxed);
      not_unboxable

let fixpoint usage declarations =
  let argument_to_var = argument_to_var usage in
  let used_boxed = Queue.create () in
  let rec loop not_unboxable =
    if Queue.is_empty used_boxed then
      not_unboxable
    else
      let not_unboxable =
        fixpoint_step declarations argument_to_var used_boxed not_unboxable
      in
      loop not_unboxable
  in
  Variable.Tbl.iter (fun v -> function
    | Anything_else ->
      Queue.push v used_boxed
    | _ -> ())
    usage.variable_usage;
  loop Argument.Set.empty

type unboxed =
  | No
  | Yes of
      { unboxed_function : Flambda.function_declaration;
        unboxed_function_name : Variable.t;
        stub : Flambda.function_declaration; }

(* CR pchambart: This should be using direct call surrogates, but for
   simplicity, to avoid complexity from freshening (as this is not run
   durring inline_and_simplify), this only generates a stub

   If we were to also unbox the return value, we would really need a
   surrogate as the additionnal boxing introduced by the stub might
   turn a tail call into a non-tail one
*)

(* CR pchambart:
   While duplicating a function, the internal parameters names are kept.
   There might be some problems related to specialised args (like lost
   ones when a parameter is unboxed).
*)

let unbox_function_declaration
    (unboxable:Argument.Set.t)
    (set_of_closures:Flambda.set_of_closures)
    (fun_var:Variable.t) (decl:Flambda.function_declaration) =
  let closure_id = Closure_id.wrap fun_var in
  let params =
    List.mapi (fun i (_var, _typ) -> (closure_id, i))
      decl.params
  in
  let has_some_unboxable_params =
    List.exists (fun arg -> Argument.Set.mem arg unboxable) params
  in
  let has_unboxable_result =
    (* This is really not sufficient to avoid increasing allocations,
       but this might still be a good heuristic *)
    match decl.return with
    | Val | Float Unboxed -> false
    | Float Boxed -> true
  in
  let has_a_surrogate =
    Variable.Map.mem fun_var set_of_closures.direct_call_surrogates
  in
  if not ((has_some_unboxable_params || has_unboxable_result) &&
          not decl.stub &&
          not has_a_surrogate) then
    No
  else begin
    let new_fun_var = Variable.rename fun_var in
    let params =
      List.mapi (fun i (var, _) ->
        if Argument.Set.mem (closure_id, i) unboxable then
          Variable.rename ~append:"_unboxed" var,
          Some (Variable.rename var)
        else
          Variable.rename var, None)
        decl.params
    in
    let return : Flambda.param_type =
      match decl.return with
      | Val | Float Unboxed -> decl.return
      | Float Boxed -> Float Unboxed
    in
    let stub =
      let apply : Flambda.expr =
        Apply {
          func = new_fun_var;
          args = List.map fst params;
          return;
          kind = Direct (Closure_id.wrap new_fun_var);
          dbg = Debuginfo.none;
          inline = Default_inline;
          specialise = Default_specialise;
        }
      in
      let body =
        match decl.return with
        | Val | Float Unboxed -> apply
        | Float Boxed ->
          (* CR: This makes the function not tail. This should be
             fixable by using surrogates instead *)
          let boxed = Variable.create "boxed" in
          let unboxed = Variable.create "unboxed" in
          Flambda.create_let unboxed (Expr apply)
            (Flambda.create_let boxed (Prim (Pbox_float, [unboxed], Debuginfo.none))
               (Var boxed))
      in
      let body =
        List.fold_left (fun body (var, pre_unboxed) ->
          match pre_unboxed with
          | None -> body
          | Some pre_unboxed ->
            Flambda.create_let var
              (Prim (Punbox_float, [pre_unboxed], Debuginfo.none))
              body)
          body params
      in
      let params =
        List.map2 (fun (var, pre_unboxed) (_, typ) ->
          match pre_unboxed with
          | None ->
            var, typ
          | Some pre_unboxed ->
            pre_unboxed, typ)
          params decl.params
      in
      Flambda.create_function_declaration
        ~params
        ~return:decl.return
        ~body
        ~stub:true
        ~dbg:decl.dbg
        ~inline:Default_inline
        ~specialise:Default_specialise
        ~is_a_functor:false
    in
    let unboxed_function =
      let params =
        List.mapi (fun i (param, typ) ->
          if Argument.Set.mem (closure_id, i) unboxable then
            (Variable.rename ~append:"_boxed" param, Flambda.Float Unboxed),
            Some param
          else
            (param, typ),
            None)
          decl.params
      in
      let body =
        match decl.return with
        | Val | Float Unboxed -> decl.body
        | Float Boxed ->
          (* CR: This makes recursive calls of this function not tail. *)
          let boxed = Variable.create "boxed" in
          let unboxed = Variable.create "unboxed" in
          Flambda.create_let boxed (Expr decl.body)
            (Flambda.create_let unboxed (Prim (Punbox_float, [boxed], Debuginfo.none))
               (Var unboxed))
      in
      let body =
        List.fold_left (fun body ((var, _typ), boxed) ->
          match boxed with
          | None -> body
          | Some boxed ->
            Flambda.create_let boxed
              (Prim (Pbox_float, [var], Debuginfo.none))
              body)
          body params
      in
      Flambda.create_function_declaration
        ~params:(List.map fst params)
        ~return
        ~body
        ~stub:decl.stub
        ~dbg:decl.dbg
        ~inline:decl.inline
        ~specialise:decl.specialise
        ~is_a_functor:decl.is_a_functor
    in
    (* Format.printf "unboxed:@ %a@." *)
    (*   Flambda.print_function_declaration (new_fun_var, unboxed_function); *)
    Yes { stub; unboxed_function; unboxed_function_name = new_fun_var }
  end

let unbox_set_of_closures (unboxable:Argument.Set.t)
    (set_of_closures:Flambda.set_of_closures)
  : Flambda.set_of_closures =
  let funs =
    Variable.Map.fold (fun fun_var function_declaration acc ->
      let unboxed_function =
        unbox_function_declaration unboxable set_of_closures
          fun_var function_declaration
      in
      match unboxed_function with
      | No ->
        Variable.Map.add fun_var function_declaration acc
      | Yes { unboxed_function;
              unboxed_function_name;
              stub } ->
        Variable.Map.add unboxed_function_name unboxed_function
          (Variable.Map.add fun_var stub acc))
      set_of_closures.function_decls.funs Variable.Map.empty
  in
  let function_decls =
    Flambda.update_function_declarations
      set_of_closures.function_decls
      ~funs
  in
  let set_of_closures =
    Flambda.create_set_of_closures
      ~function_decls
      ~free_vars:set_of_closures.free_vars
      ~specialised_args:set_of_closures.specialised_args
      ~direct_call_surrogates:set_of_closures.direct_call_surrogates
  in
  (* Format.printf "set:@ %a@." *)
  (*   Flambda.print_set_of_closures set_of_closures; *)
  set_of_closures


let unbox_function_arguments (program : Flambda.program) : Flambda.program =
  let usage, declarations = collect_usage program in
  let not_unboxable = fixpoint usage declarations in
  let unboxable =
    Variable.Tbl.fold (fun _v (arg, (typ : Flambda.param_type)) acc ->
      match typ with
      | Val | Float Unboxed -> acc
      | Float Boxed ->
        if Argument.Set.mem arg not_unboxable then
          acc
        else
          Argument.Set.add arg acc)
      declarations.variable_argument Argument.Set.empty
  in
  let program' =
    Flambda_iterators.map_sets_of_closures_of_program program
      ~f:(unbox_set_of_closures unboxable)
  in
  (* Format.printf "unboxable args:@ %a@.@.%a@.@.%a" *)
  (*   Argument.Set.print unboxable *)
  (*   Flambda.print_program program *)
  (*   Flambda.print_program program'; *)
  (* assert(program = program'); *)
  program'

