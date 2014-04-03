(**************************************************************************)
(*                                                                        *)
(*                                OCaml                                   *)
(*                                                                        *)
(*                      Pierre Chambart (OCamlPro)                        *)
(*                                                                        *)
(*   Copyright 2014 Institut National de Recherche en Informatique et     *)
(*   en Automatique.  All rights reserved.  This file is distributed      *)
(*   under the terms of the Q Public License version 1.0.                 *)
(*                                                                        *)
(**************************************************************************)

open Lambda
open Abstract_identifiers
open Flambda

let rec add_debug_info ev f =
  match ev.lev_kind with
  | Lev_after _ ->
    begin match f with
      | Fapply(ap,v) ->
        Fapply({ ap with ap_dbg = Debuginfo.from_call ev}, v)
      | Fprim(Praise, args, dinfo, v) ->
        Fprim(Praise, args, Debuginfo.from_call ev, v)
      | Fsend(kind, f1, f2, args, dinfo, v) ->
        Fsend(kind, f1, f2, args, Debuginfo.from_call ev, v)
      | Fsequence(f1, f2, v) ->
        Fsequence(f1, add_debug_info ev f2, v)
      | _ -> f
    end
  | _ -> f

let rec subst sb id =
  try subst sb (FidentMap.find id sb)
  with Not_found -> id

let add_subst sb ~replace ~by =
  FidentMap.add replace by sb

let nid = ExprId.create

type 'param_id function_declaration =
  { let_bound_var : Fident.t;
    closure_bound_var : Fident.t;
    kind : function_kind;
    params : 'param_id list;
    body : lambda }

let to_flambda
    ~for_bytecode
    ~current_compilation_unit ~current_unit_id
    ~symbol_for_global'
    lam =

  let wrap_id id = Fident.wrap_ident ~current_compilation_unit id in

  let rename_var var = Fident.rename ~current_compilation_unit var in

  let rec close sb = function
    | Lvar id ->
        let var = wrap_id id in
        Fvar (subst sb var,
              nid ~name:(Format.asprintf "var_%a" Fident.print var) ())
    | Lconst cst -> close_const sb cst
    | Llet(str, id, lam, body) ->
        let str =
          match str with
          | Variable -> Assigned
          | _ -> Not_assigned in
        let var = wrap_id id in
        Flet(str, var,
             close_named var sb lam,
             close sb body, nid ~name:"let" ())
    | Lfunction(kind, params, body) ->
        let let_bound_var = Fident.create ~current_compilation_unit "fun" in
        let closure_bound_var = rename_var let_bound_var in
        let decl = { let_bound_var; closure_bound_var; kind; params; body } in
        Ffunction(
          { fu_closure = close_functions sb [decl];
            fu_fun = Closure_function.wrap closure_bound_var;
            fu_relative_to = None },
          nid ~name:"function" ())
    | Lapply(funct, args, loc) ->
        Fapply(
          { ap_function = close sb funct;
            ap_arg = close_list sb args;
            ap_kind = Indirect;
            ap_dbg = Debuginfo.none },
          nid ~name:"apply" ())
    | Lletrec(defs, body) ->
        let defs = List.map (fun (id,lam) -> wrap_id id, lam) defs in
        let function_declarations =
          List.map (function
              | let_bound_var, Lfunction(kind, params, body) ->
                  let closure_bound_var = rename_var let_bound_var in
                  Some { let_bound_var; closure_bound_var; kind; params; body }
              | _ -> None)
            defs
        in
        begin match Misc.some_if_all_elements_are_some function_declarations with
        | Some function_declarations ->
            (* When all the binding are functions, we build a single closure
                 for all the functions *)
            let clos = close_functions sb function_declarations in
            let clos_var = Fident.create ~current_compilation_unit "clos" in
            let body = List.fold_left (fun body decl ->
                Flet(Not_assigned, decl.let_bound_var,
                     Ffunction(
                       { fu_closure = Fvar (clos_var, nid ());
                         fu_fun = Closure_function.wrap decl.closure_bound_var;
                         fu_relative_to = None },
                       nid ()),
                     body, nid ()))
                (close sb body) function_declarations in
            Flet(Not_assigned, clos_var, clos, body, nid ~name:"closure_letrec" ())
        | None ->
            let fdefs = List.map
                (fun (var,def) -> var, close_named var sb def) defs in
            Fletrec(fdefs, close sb body, nid ~name:"letrec" ())
        end
    | Lsend(kind, met, obj, args, _) ->
        Fsend(kind, close sb met, close sb obj,
              close_list sb args, Debuginfo.none, nid ())
    | Lprim(Pdirapply loc,[funct;arg])
    | Lprim(Prevapply loc,[arg;funct]) ->
        close sb (Lapply(funct, [arg], loc))
    | Lprim(Praise, [Levent(arg, ev)]) ->
        let arg = close sb arg in
        let arg = if for_bytecode then Fevent (arg, ev, nid ()) else arg in
        Fprim(Praise, [arg], Debuginfo.from_raise ev, nid ())
    | Lprim(Pfield i, [Lprim(Pgetglobal id, [])])
      when Ident.same id current_unit_id ->
        Fprim(Pgetglobalfield(id,i), [], Debuginfo.none,
              nid ~name:"getglobalfield" ())
    | Lprim(Psetfield(i,_), [Lprim(Pgetglobal id, []); lam]) ->
        assert(Ident.same id current_unit_id);
        Fprim(Psetglobalfield i, [close sb lam], Debuginfo.none,
              nid ~name:"setglobalfield" ())
    | Lprim(Pgetglobal id, [])
      when not (Ident.is_predef_exn id) &&
           not for_bytecode ->
        assert(not (Ident.same id current_unit_id));
        let symbol = symbol_for_global' id in
        Fsymbol (symbol,nid ~name:"external_global" ())
    | Lprim(p, args) ->
        Fprim(p, close_list sb args, Debuginfo.none,
              nid ~name:"prim" ())
    | Lswitch(arg, sw) ->
        let aux (i,lam) = i, close sb lam in
        let rec set n = (* set of integers {0, 1, ... n} *)
          if n < 0 then Ext_types.IntSet.empty
          else Ext_types.IntSet.add n (set (n-1)) in
        Fswitch(close sb arg,
                { fs_numconsts = set (sw.sw_numconsts - 1);
                  fs_consts = List.map aux sw.sw_consts;
                  fs_numblocks = set (sw.sw_numblocks - 1);
                  fs_blocks = List.map aux sw.sw_blocks;
                  fs_failaction = Misc.may_map (close sb) sw.sw_failaction },
                nid ~name:"switch" ())
    | Lstaticraise (i, args) ->
        Fstaticraise (Static_exception.of_int i, close_list sb args, nid ())
    | Lstaticcatch(body, (i, vars), handler) ->
        Fstaticcatch (Static_exception.of_int i, List.map wrap_id vars,
                close sb body, close sb handler, nid ())
    | Ltrywith(body, id, handler) ->
        Ftrywith(close sb body, wrap_id id, close sb handler, nid ())
    | Lifthenelse(arg, ifso, ifnot) ->
        Fifthenelse(close sb arg, close sb ifso, close sb ifnot,
                    nid ~name:"if" ())
    | Lsequence(lam1, lam2) ->
        Fsequence(close sb lam1, close sb lam2,
                  nid ~name:"seq" ())
    | Lwhile(cond, body) ->
        Fwhile(close sb cond, close sb body, nid ())
    | Lfor(id, lo, hi, dir, body) ->
        Ffor(wrap_id id, close sb lo, close sb hi, dir, close sb body, nid ())
    | Lassign(id, lam) ->
        Fassign(wrap_id id, close sb lam, nid ())
    | Levent(lam, ev) ->
        let lam = add_debug_info ev (close sb lam) in
        if for_bytecode then Fevent(lam, ev, nid ()) else lam
    | Lifused _ ->
        assert false

  and close_functions
      (original_substitution:Fident.t FidentMap.t) function_declarations =
    let function_declarations = List.map
        (fun decl -> { decl with params = List.map wrap_id decl.params })
        function_declarations in
    let used_variables_per_function =
      FidentMap.of_list
        (List.map (fun {closure_bound_var;body} ->
             closure_bound_var,
             FidentSet.of_ident_set ~current_compilation_unit (Lambda.free_variables body))
            function_declarations) in
    let all_functions_arguments =
      List.fold_right (fun {params} -> FidentSet.union (FidentSet.of_list params))
        function_declarations FidentSet.empty in
    let all_used_variables =
      FidentMap.fold (fun _ -> FidentSet.union)
        used_variables_per_function FidentSet.empty in
    let function_variables =
      FidentSet.of_list
        (List.map (fun {let_bound_var} -> let_bound_var)
           function_declarations) in
    let variables_in_closure =
      FidentSet.diff all_used_variables
        (FidentSet.union function_variables all_functions_arguments) in
    let sb =
      List.fold_right (fun {let_bound_var;closure_bound_var} ->
          add_subst ~replace:let_bound_var ~by:closure_bound_var)
        function_declarations original_substitution in
    let sb, free_variables_original_name =
      FidentSet.fold
        (fun var (sb,map) ->
           let renamed = rename_var var in
           add_subst sb ~replace:var ~by:renamed,
           FidentMap.add renamed var map)
        variables_in_closure (sb, FidentMap.empty) in

    let close_one_function map { closure_bound_var; kind; params; body } =
      let dbg = match body with
        | Levent (_,({lev_kind=Lev_function} as ev)) ->
            Debuginfo.from_call ev
        | _ -> Debuginfo.none in
      let ffunction =
        { stub = false; params; dbg;
          free_variables =
            FidentSet.map (subst sb)
              (FidentMap.find closure_bound_var used_variables_per_function);
          body = close sb body } in
      match kind with
      | Curried ->
          FidentMap.add closure_bound_var ffunction map
      | Tupled ->
          let tuplified_version = rename_var closure_bound_var in
          let generic_function_stub =
            tupled_function_call_stub
              closure_bound_var params tuplified_version in
          let map = FidentMap.add closure_bound_var generic_function_stub map in
          FidentMap.add tuplified_version ffunction map
    in
    let ffunctions =
      { ident = FunId.create current_compilation_unit;
        funs =
          List.fold_left close_one_function FidentMap.empty function_declarations;
        compilation_unit = current_compilation_unit } in
    let closure =
      { cl_fun = ffunctions;
        cl_free_var =
          FidentMap.map (fun var -> Fvar(subst original_substitution var, nid ()))
            free_variables_original_name;
        cl_specialised_arg = FidentMap.empty } in

    Fclosure (closure, nid ())

  and tupled_function_call_stub id original_params tuplified_version =
    let tuple_param = Fident.create ~current_compilation_unit "tupled_stub_param" in
    let params = List.map (fun p -> rename_var p) original_params in
    let call = Fapply(
        { ap_function = Fvar(tuplified_version,nid ());
          ap_arg = List.map (fun p' -> Fvar(p',nid ())) params;
          ap_kind = Direct (Closure_function.wrap tuplified_version);
          ap_dbg = Debuginfo.none },
        nid ()) in
    let _, body =
      List.fold_left (fun (pos,body) param ->
          let lam = Fprim(Pfield pos, [Fvar(tuple_param, nid ())],
                          Debuginfo.none, nid ()) in
          pos+1,
          Flet(Not_assigned,param,lam,body,nid ()))
        (0,call) params in
    { stub = true;
      params = [tuple_param];
      free_variables = FidentSet.of_list [tuple_param;tuplified_version];
      body;
      dbg = Debuginfo.none }

  and close_list sb l = List.map (close sb) l

  and close_named let_bound_var sb = function
    | Lfunction(kind, params, body) ->
        let closure_bound_var = rename_var let_bound_var in
        let function_declaration =
          { let_bound_var; closure_bound_var; kind; params; body } in
        Ffunction(
          { fu_closure = close_functions sb [function_declaration];
            fu_fun = Closure_function.wrap closure_bound_var;
            fu_relative_to = None },
          nid ())
    | lam ->
        close sb lam

  and close_const sb cst =
    let rec aux = function
      | Const_base c -> Fconst(Fconst_base c, nid ~name:"cst" ())
      | Const_pointer c -> Fconst(Fconst_pointer c, nid ~name:"cstptr" ())
      | Const_immstring c -> Fconst(Fconst_immstring c, nid ~name:"immstring" ())
      | Const_float_array c -> Fconst(Fconst_float_array c, nid ~name:"float" ())
      | Const_block (tag,l) ->
          Fprim(Pmakeblock(tag, Asttypes.Immutable),
                List.map aux l, Debuginfo.none, nid ~name:"cstblock" ())
    in
    aux cst
  in
  close FidentMap.empty lam

(** String lifting to toplevel of expressions *)

let rec lift_strings acc = function
    | Lvar _ as lam ->
        acc, lam
    | Lconst (Const_base (Asttypes.Const_string s)) ->
        let id = Ident.create "constant_string" in
        (id, s) :: acc, Lvar id
    | Lconst (Const_base (Asttypes.Const_nativeint _ | Asttypes.Const_char _ |
                          Asttypes.Const_float _ | Asttypes.Const_int32 _ |
                          Asttypes.Const_int64 _ | Asttypes.Const_int _) |
              Const_pointer _ | Const_block _ | Const_float_array _ |
              Const_immstring _) as lam ->
        acc, lam
    | Llet(str, id, lam, body) ->
        let acc, lam = lift_strings acc lam in
        let acc, body = lift_strings acc body in
        acc, Llet(str, id, lam, body)
    | Lfunction(kind, params, body) ->
        let acc, body = lift_strings acc body in
        acc, Lfunction(kind, params, body)
    | Lapply(funct, args, loc) ->
        let acc, funct = lift_strings acc funct in
        let acc, args = lift_strings_list acc args in
        acc, Lapply(funct, args, loc)
    | Lletrec(defs, body) ->
        let acc, defs = lift_strings_couple_list acc defs in
        acc, Lletrec(defs, body)
    | Lsend(kind, met, obj, args, loc) ->
        let acc, met = lift_strings acc met in
        let acc, obj = lift_strings acc obj in
        let acc, args = lift_strings_list acc args in
        acc, Lsend(kind, met, obj, args, loc)
    | Lprim(p, args) ->
        let acc, args = lift_strings_list acc args in
        acc, Lprim(p, args)
    | Lswitch(arg, sw) ->
        let acc, arg = lift_strings acc arg in
        let acc, sw_consts = lift_strings_couple_list acc sw.sw_consts in
        let acc, sw_blocks = lift_strings_couple_list acc sw.sw_blocks in
        let acc, sw_failaction =
          match sw.sw_failaction with
          | None -> acc, None
          | Some failaction ->
              let acc, failaction = lift_strings acc failaction in
              acc, Some failaction in
        acc, Lswitch(arg, { sw with sw_consts; sw_blocks; sw_failaction })
    | Lstaticraise (i, args) ->
        let acc, args = lift_strings_list acc args in
        acc, Lstaticraise (i, args)
    | Lstaticcatch(body, (i, vars), handler) ->
        let acc, body = lift_strings acc body in
        let acc, handler = lift_strings acc handler in
        acc, Lstaticcatch(body, (i, vars), handler)
    | Ltrywith(body, id, handler) ->
        let acc, body = lift_strings acc body in
        let acc, handler = lift_strings acc handler in
        acc, Ltrywith(body, id, handler)
    | Lifthenelse(arg, ifso, ifnot) ->
        let acc, arg = lift_strings acc arg in
        let acc, ifso = lift_strings acc ifso in
        let acc, ifnot = lift_strings acc ifnot in
        acc, Lifthenelse(arg, ifso, ifnot)
    | Lsequence(lam1, lam2) ->
        let acc, lam1 = lift_strings acc lam1 in
        let acc, lam2 = lift_strings acc lam2 in
        acc, Lsequence(lam1, lam2)
    | Lwhile(cond, body) ->
        let acc, cond = lift_strings acc cond in
        let acc, body = lift_strings acc body in
        acc, Lwhile(cond, body)
    | Lfor(id, lo, hi, dir, body) ->
        let acc, lo = lift_strings acc lo in
        let acc, hi = lift_strings acc hi in
        let acc, body = lift_strings acc body in
        acc, Lfor(id, lo, hi, dir, body)
    | Lassign(id, lam) ->
        let acc, lam = lift_strings acc lam in
        acc, Lassign(id, lam)
    | Levent(lam, ev) ->
        let acc, lam = lift_strings acc lam in
        acc, Levent(lam, ev)
    | Lifused _ ->
        assert false

and lift_strings_list acc lams =
  List.fold_right (fun lam (acc,lams) ->
      let acc, lam = lift_strings acc lam in
      acc, lam :: lams)
    lams (acc, [])

and lift_strings_couple_list :
  'a. 'acc -> ('a * Lambda.lambda) list -> 'acc * ('a * Lambda.lambda) list =
  fun acc lams ->
    List.fold_right (fun (v,lam) (acc,lams) ->
        let acc, lam = lift_strings acc lam in
        acc, (v,lam) :: lams)
      lams (acc, [])

let lift_strings_to_toplevel lam =
  let bindings, lam = lift_strings [] lam in
  List.fold_left (fun lam (id, string) ->
      Llet(Strict,id,
           Lconst (Const_base (Asttypes.Const_string string)),
           lam))
    lam bindings

let intro ?(for_bytecode = false) ~current_compilation_unit ~current_unit_id
    ~symbol_for_global' lam =
  (* Strings are the only expressions that can't be duplicated without
     changing the semantics. So we lift them to toplevel to avoid
     having to handle special cases later.
     There is no runtime cost to this transformation: strings are
     constants, they will not appear in the closures *)
  let lam = if for_bytecode then lam else lift_strings_to_toplevel lam in
  to_flambda ~for_bytecode ~current_compilation_unit ~current_unit_id
    ~symbol_for_global' lam
