(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                       Pierre Chambart, OCamlPro                        *)
(*           Mark Shinwell and Leo White, Jane Street Europe              *)
(*                                                                        *)
(*   Copyright 2013--2016 OCamlPro SAS                                    *)
(*   Copyright 2014--2016 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

[@@@ocaml.warning "+a-4-9-30-40-41-42"]

let find_declaration cf ({ funs } : Flambda.function_declarations) =
  Variable.Map.find (Closure_id.unwrap cf) funs

let find_declaration_variable cf ({ funs } : Flambda.function_declarations) =
  let var = Closure_id.unwrap cf in
  if not (Variable.Map.mem var funs)
  then raise Not_found
  else var

let find_free_variable cv ({ free_vars } : Flambda.set_of_closures) =
  let var : Flambda.specialised_to =
    Variable.Map.find (Var_within_closure.unwrap cv) free_vars
  in
  var.var

let function_arity (f : Flambda.function_declaration) = List.length f.params

let variables_bound_by_the_closure cf
      (decls : Flambda.function_declarations) =
  let func = find_declaration cf decls in
  let params = Variable.Set.of_list func.params in
  let functions = Variable.Map.keys decls.funs in
  Variable.Set.diff
    (Variable.Set.diff func.free_variables params)
    functions

let description_of_toplevel_node (expr : Flambda.t) =
  match expr with
  | Let { var; _ } -> Format.asprintf "let %a" Variable.print var
  | Let_mutable _ -> "let_mutable"
  | Let_cont  _ -> "catch"
  | Apply _ -> "apply"
  | Apply_cont  _ -> "staticraise"
  | Switch _ -> "switch"

let compare_const (c1 : Flambda.const) (c2 : Flambda.const) =
  match c1, c2 with
  | Int v1, Int v2 -> compare v1 v2
  | Char v1, Char v2 -> compare v1 v2
  | Const_pointer v1, Const_pointer v2 -> compare v1 v2
  | Int _, _ -> -1
  | _, Int _ -> 1
  | Char _, _ -> -1
  | _, Char _ -> 1

let trap_action_equal (trap1 : Flambda.trap_action option)
      (trap2 : Flambda.trap_action option) =
  match trap1, trap2 with
  | None, None -> true
  | Some (Push { id = id1; exn_handler = exn_handler1; }),
      Some (Push { id = id2; exn_handler = exn_handler2; }) ->
    Trap_id.equal id1 id2
      && Continuation.equal exn_handler1 exn_handler2
  | Some (Pop id1), Some (Pop id2) ->
    Trap_id.equal id1 id2
  | _, _ -> false

let rec same (l1 : Flambda.t) (l2 : Flambda.t) =
  l1 == l2 || (* it is ok for the string case: if they are physically the same,
                 it is the same original branch *)
  match (l1, l2) with
  | Apply a1 , Apply a2  ->
    a1.kind = a2.kind
      && Variable.equal a1.func a2.func
      && Misc.Stdlib.List.equal Variable.equal a1.args a2.args
  | Apply _, _ | _, Apply _ -> false
  | Let { var = var1; defining_expr = defining_expr1; body = body1; _ },
      Let { var = var2; defining_expr = defining_expr2; body = body2; _ } ->
    Variable.equal var1 var2 && same_named defining_expr1 defining_expr2
      && same body1 body2
  | Let _, _ | _, Let _ -> false
  | Let_mutable {var = mv1; initial_value = v1; contents_kind = ck1; body = b1},
    Let_mutable {var = mv2; initial_value = v2; contents_kind = ck2; body = b2}
    ->
    Mutable_variable.equal mv1 mv2
      && Variable.equal v1 v2
      && ck1 = ck2
      && same b1 b2
  | Let_mutable _, _ | _, Let_mutable _ -> false
  | Switch (a1, s1), Switch (a2, s2) ->
    Variable.equal a1 a2 && sameswitch s1 s2
  | Switch _, _ | _, Switch _ -> false
  | Apply_cont (e1, trap1, a1), Apply_cont (e2, trap2, a2) ->
    Continuation.equal e1 e2 && Misc.Stdlib.List.equal Variable.equal a1 a2
      && trap_action_equal trap1 trap2
  | Apply_cont _, _ | _, Apply_cont _ -> false
  | Let_cont { name = name1; body = body1; handler = handler1; },
    Let_cont { name = name2; body = body2; handler = handler2; } ->
    Continuation.equal name1 name2
      && same body1 body2
      && begin match handler1, handler2 with
        | Alias alias_of1, Alias alias_of2 ->
          Continuation.equal alias_of1 alias_of2
        | Handler
            { params = params1; recursive = recursive1; handler = handler1; },
          Handler
            { params = params2; recursive = recursive2; handler = handler2; } ->
          Misc.Stdlib.List.equal Variable.equal params1 params2
            && Pervasives.compare recursive1 recursive2 = 0
            && same handler1 handler2
        | Alias _, Handler _ | Handler _, Alias _ -> false
        end

and same_named (named1 : Flambda.named) (named2 : Flambda.named) =
  match named1, named2 with
  | Var var1, Var var2 -> Variable.equal var1 var2
  | Var _, _ | _, Var _ -> false
  | Symbol s1 , Symbol s2  -> Symbol.equal s1 s2
  | Symbol _, _ | _, Symbol _ -> false
  | Const c1, Const c2 -> compare_const c1 c2 = 0
  | Const _, _ | _, Const _ -> false
  | Allocated_const c1, Allocated_const c2 ->
    Allocated_const.compare c1 c2 = 0
  | Allocated_const _, _ | _, Allocated_const _ -> false
  | Read_mutable mv1, Read_mutable mv2 -> Mutable_variable.equal mv1 mv2
  | Read_mutable _, _ | _, Read_mutable _ -> false
  | Assign { being_assigned = being_assigned1; new_value = new_value1; },
    Assign { being_assigned = being_assigned2; new_value = new_value2; } ->
    Mutable_variable.equal being_assigned1 being_assigned2
      && Variable.equal new_value1 new_value2
  | Assign _, _ | _, Assign _ -> false
  | Read_symbol_field (s1, i1), Read_symbol_field (s2, i2) ->
    Symbol.equal s1 s2 && i1 = i2
  | Read_symbol_field _, _ | _, Read_symbol_field _ -> false
  | Set_of_closures s1, Set_of_closures s2 -> same_set_of_closures s1 s2
  | Set_of_closures _, _ | _, Set_of_closures _ -> false
  | Project_closure f1, Project_closure f2 -> same_project_closure f1 f2
  | Project_closure _, _ | _, Project_closure _ -> false
  | Project_var v1, Project_var v2 ->
    Variable.equal v1.closure v2.closure
      && Closure_id.Map.equal Var_within_closure.equal v1.var v2.var
  | Project_var _, _ | _, Project_var _ -> false
  | Move_within_set_of_closures m1, Move_within_set_of_closures m2 ->
    same_move_within_set_of_closures m1 m2
  | Move_within_set_of_closures _, _ | _, Move_within_set_of_closures _ ->
    false
  | Prim (p1, al1, _), Prim (p2, al2, _) ->
    p1 = p2 && Misc.Stdlib.List.equal Variable.equal al1 al2
  | Proved_unreachable, Proved_unreachable -> true
  | Proved_unreachable, _ | _, Proved_unreachable -> false

and sameclosure (c1 : Flambda.function_declaration)
      (c2 : Flambda.function_declaration) =
  Misc.Stdlib.List.equal Variable.equal c1.params c2.params
    && same c1.body c2.body

and same_set_of_closures (c1 : Flambda.set_of_closures)
      (c2 : Flambda.set_of_closures) =
  Variable.Map.equal sameclosure c1.function_decls.funs c2.function_decls.funs
    && Variable.Map.equal Flambda.equal_specialised_to
        c1.free_vars c2.free_vars
    && Variable.Map.equal Flambda.equal_specialised_to c1.specialised_args
        c2.specialised_args

and same_project_closure (s1 : Flambda.project_closure)
      (s2 : Flambda.project_closure) =
  Variable.equal s1.set_of_closures s2.set_of_closures
    && Closure_id.Set.equal s1.closure_id s2.closure_id

and same_move_within_set_of_closures (m1 : Flambda.move_within_set_of_closures)
      (m2 : Flambda.move_within_set_of_closures) =
  Variable.equal m1.closure m2.closure
    && Closure_id.Map.equal Closure_id.equal m1.move m2.move

and sameswitch (fs1 : Flambda.switch) (fs2 : Flambda.switch) =
  let samecase (n1, a1) (n2, a2) = n1 = n2 && Continuation.equal a1 a2 in
  fs1.numconsts = fs2.numconsts
    && fs1.numblocks = fs2.numblocks
    && Misc.Stdlib.List.equal samecase fs1.consts fs2.consts
    && Misc.Stdlib.List.equal samecase fs1.blocks fs2.blocks
    && Misc.Stdlib.Option.equal Continuation.equal fs1.failaction fs2.failaction

let can_be_merged = same

(* CR-soon mshinwell: this should use the explicit ignore functions *)
let toplevel_substitution sb tree =
  let sb' = sb in
  let sb v = try Variable.Map.find v sb with Not_found -> v in
  let aux (flam : Flambda.t) : Flambda.t =
    match flam with
    | Let_mutable mutable_let ->
      let initial_value = sb mutable_let.initial_value in
      Let_mutable { mutable_let with initial_value }
    | Apply { kind; func; args; continuation; call_kind; dbg; inline;
        specialise; } ->
      let kind : Flambda.apply_kind =
        match kind with
        | Function -> Function
        | Method { kind; obj; } -> Method { kind; obj = sb obj; }
      in
      let func = sb func in
      let args = List.map sb args in
      Apply { kind; func; args; continuation; call_kind; dbg; inline;
        specialise; }
    | Switch (cond, sw) ->
      let cond = sb cond in
      Switch (cond, sw)
    | Apply_cont (static_exn, trap_action, args) ->
      let args = List.map sb args in
      Apply_cont (static_exn, trap_action, args)
    | Let_cont _ | Let _ -> flam
  in
  let aux_named (named : Flambda.named) : Flambda.named =
    match named with
    | Var var ->
      let var' = sb var in
      if var == var' then named
      else Var var'
    | Symbol _ | Const _ -> named
    | Allocated_const _ | Read_mutable _ -> named
    | Assign { being_assigned; new_value; } ->
      let new_value = sb new_value in
      Assign { being_assigned; new_value; }
    | Read_symbol_field _ -> named
    | Set_of_closures set_of_closures ->
      let set_of_closures =
        Flambda.create_set_of_closures
          ~function_decls:set_of_closures.function_decls
          ~free_vars:
            (Variable.Map.map (fun (spec_to : Flambda.specialised_to) ->
                { spec_to with var = sb spec_to.var; })
              set_of_closures.free_vars)
          ~specialised_args:
            (Variable.Map.map (fun (spec_to : Flambda.specialised_to) ->
                { spec_to with var = sb spec_to.var; })
              set_of_closures.specialised_args)
          ~direct_call_surrogates:set_of_closures.direct_call_surrogates
      in
      Set_of_closures set_of_closures
    | Project_closure project_closure ->
      Project_closure {
        project_closure with
        set_of_closures = sb project_closure.set_of_closures;
      }
    | Move_within_set_of_closures move_within_set_of_closures ->
      Move_within_set_of_closures {
        move_within_set_of_closures with
        closure = sb move_within_set_of_closures.closure;
      }
    | Project_var project_var ->
      Project_var {
        project_var with
        closure = sb project_var.closure;
      }
    | Prim (prim, args, dbg) ->
      Prim (prim, List.map sb args, dbg)
    | Proved_unreachable -> Proved_unreachable
  in
  if Variable.Map.is_empty sb' then tree
  else Flambda_iterators.map_toplevel aux aux_named tree

(* CR-someday mshinwell: Fix [Flambda_iterators] so this can be implemented
   properly. *)
let toplevel_substitution_named sb named =
  let var = Variable.create "subst" in
  let cont = Continuation.create () in
  let expr : Flambda.t =
    Flambda.create_let var named (Apply_cont (cont, None, []))
  in
  match toplevel_substitution sb expr with
  | Let let_expr -> let_expr.defining_expr
  | _ -> assert false

let make_closure_declaration ~id ~body ~params ~continuation_param
      ~stub ~continuation : Flambda.t =
  let free_variables = Flambda.free_variables body in
  let param_set = Variable.Set.of_list params in
  if not (Variable.Set.subset param_set free_variables) then begin
    Misc.fatal_error "Flambda_utils.make_closure_declaration"
  end;
  let sb =
    Variable.Set.fold
      (fun id sb -> Variable.Map.add id (Variable.rename id) sb)
      free_variables Variable.Map.empty
  in
  (* CR-soon mshinwell: try to eliminate this [toplevel_substitution].  This
     function is only called from [Inline_and_simplify], so we should be able
     to do something similar to what happens in [Inlining_transforms] now. *)
  let body = toplevel_substitution sb body in
  let subst id = Variable.Map.find id sb in
  let function_declaration =
    Flambda.create_function_declaration ~params:(List.map subst params)
      ~continuation_param
      ~body ~stub ~dbg:Debuginfo.none ~inline:Default_inline
      ~specialise:Default_specialise ~is_a_functor:false
  in
  assert (Variable.Set.equal (Variable.Set.map subst free_variables)
    function_declaration.free_variables);
  let free_vars =
    Variable.Map.fold (fun id id' fv' ->
        let spec_to : Flambda.specialised_to =
          { var = id;
            projection = None;
          }
        in
        Variable.Map.add id' spec_to fv')
      (Variable.Map.filter
        (fun id _ -> not (Variable.Set.mem id param_set))
        sb)
      Variable.Map.empty
  in
  let compilation_unit = Compilation_unit.get_current_exn () in
  let set_of_closures_var =
    Variable.create "set_of_closures"
      ~current_compilation_unit:compilation_unit
  in
  let set_of_closures =
    let function_decls =
      Flambda.create_function_declarations
        ~funs:(Variable.Map.singleton id function_declaration)
    in
    Flambda.create_set_of_closures ~function_decls ~free_vars
      ~specialised_args:Variable.Map.empty
      ~direct_call_surrogates:Variable.Map.empty
  in
  let project_closure : Flambda.named =
    Project_closure {
        set_of_closures = set_of_closures_var;
        closure_id = Closure_id.Set.singleton (Closure_id.wrap id);
      }
  in
  let project_closure_var =
    Variable.create "project_closure"
      ~current_compilation_unit:compilation_unit
  in
  Flambda.create_let set_of_closures_var (Set_of_closures set_of_closures)
    (Flambda.create_let project_closure_var project_closure
      (Apply_cont (continuation, None, [project_closure_var])))

let bind ~bindings ~body =
  List.fold_left (fun expr (var, var_def) ->
      Flambda.create_let var var_def expr)
    body bindings

let all_lifted_constants (program : Flambda.program) =
  let rec loop (program : Flambda.program_body) =
    match program with
    | Let_symbol (symbol, decl, program) -> (symbol, decl) :: (loop program)
    | Let_rec_symbol (decls, program) ->
      List.fold_left (fun l (symbol, decl) -> (symbol, decl) :: l)
        (loop program)
        decls
    | Initialize_symbol (_, _, _, program)
    | Effect (_, _, program) -> loop program
    | End _ -> []
  in
  loop program.program_body

let all_lifted_constants_as_map program =
  Symbol.Map.of_list (all_lifted_constants program)

let initialize_symbols (program : Flambda.program) =
  let rec loop (program : Flambda.program_body) =
    match program with
    | Initialize_symbol (symbol, tag, fields, program) ->
      (symbol, tag, fields) :: (loop program)
    | Effect (_, _, program)
    | Let_symbol (_, _, program)
    | Let_rec_symbol (_, program) -> loop program
    | End _ -> []
  in
  loop program.program_body

let imported_symbols (program : Flambda.program) =
  program.imported_symbols

let needed_import_symbols (program : Flambda.program) =
  let dependencies = Flambda.free_symbols_program program in
  let defined_symbol =
    Symbol.Set.union
      (Symbol.Set.of_list
         (List.map fst (all_lifted_constants program)))
      (Symbol.Set.of_list
         (List.map (fun (s, _, _) -> s) (initialize_symbols program)))
  in
  Symbol.Set.diff dependencies defined_symbol

let introduce_needed_import_symbols program : Flambda.program =
  { program with
    imported_symbols = needed_import_symbols program;
  }

let root_symbol (program : Flambda.program) =
  let rec loop (program : Flambda.program_body) =
    match program with
    | Effect (_, _, program)
    | Let_symbol (_, _, program)
    | Let_rec_symbol (_, program)
    | Initialize_symbol (_, _, _, program) -> loop program
    | End root ->
      root
  in
  loop program.program_body

let make_closure_map program =
  let map = ref Closure_id.Map.empty in
  let add_set_of_closures ~constant:_ : Flambda.set_of_closures -> unit = fun
    { function_decls } ->
    Variable.Map.iter (fun var _ ->
        let closure_id = Closure_id.wrap var in
        map := Closure_id.Map.add closure_id function_decls !map)
      function_decls.funs
  in
  Flambda_iterators.iter_on_set_of_closures_of_program
    program
    ~f:add_set_of_closures;
  !map

let make_closure_map' input =
  let map = ref Closure_id.Map.empty in
  let add_set_of_closures _ (function_decls : Flambda.function_declarations) =
    Variable.Map.iter (fun var _ ->
        let closure_id = Closure_id.wrap var in
        map := Closure_id.Map.add closure_id function_decls !map)
      function_decls.funs
  in
  Set_of_closures_id.Map.iter add_set_of_closures input;
  !map

let all_lifted_constant_sets_of_closures program =
  let set = ref Set_of_closures_id.Set.empty in
  List.iter (function
      | (_, Flambda.Set_of_closures {
          function_decls = { set_of_closures_id } }) ->
        set := Set_of_closures_id.Set.add set_of_closures_id !set
      | _ -> ())
    (all_lifted_constants program);
  !set

let all_sets_of_closures program =
  let list = ref [] in
  Flambda_iterators.iter_on_set_of_closures_of_program program
    ~f:(fun ~constant:_ set_of_closures ->
        list := set_of_closures :: !list);
  !list

let all_sets_of_closures_map program =
  let r = ref Set_of_closures_id.Map.empty in
  Flambda_iterators.iter_on_set_of_closures_of_program program
    ~f:(fun ~constant:_ set_of_closures ->
      r := Set_of_closures_id.Map.add
          set_of_closures.function_decls.set_of_closures_id
          set_of_closures !r);
  !r

let all_function_decls_indexed_by_set_of_closures_id program =
  Set_of_closures_id.Map.map
    (fun { Flambda. function_decls; _ } -> function_decls)
    (all_sets_of_closures_map program)

let all_function_decls_indexed_by_closure_id program =
  let aux_fun function_decls fun_var _ map =
    let closure_id = Closure_id.wrap fun_var in
    Closure_id.Map.add closure_id function_decls map
  in
  let aux _ ({ function_decls; _ } : Flambda.set_of_closures) map =
    Variable.Map.fold (aux_fun function_decls) function_decls.funs map
  in
  Set_of_closures_id.Map.fold aux (all_sets_of_closures_map program)
    Closure_id.Map.empty

let make_variable_symbol var =
  Symbol.create (Compilation_unit.get_current_exn ())
    (Linkage_name.create
       (Variable.unique_name (Variable.rename var)))

let make_variables_symbol vars =
  let name =
    String.concat "_and_"
      (List.map (fun var -> Variable.unique_name (Variable.rename var)) vars)
  in
  Symbol.create (Compilation_unit.get_current_exn ()) (Linkage_name.create name)

(* CR-soon mshinwell: This function should be tidied up. *)
let substitute_read_symbol_field_for_variables
    (substitution : (Symbol.t * int option) Variable.Map.t)
    (expr : Flambda.t) =
  let bind var fresh_var (expr : Flambda.t) : Flambda.t =
    let symbol, path = Variable.Map.find var substitution in
    let make_named (path : int option) : Flambda.named =
      match path with
      | None -> Symbol symbol
      | Some i -> Read_symbol_field (symbol, i)
    in
    Flambda.create_let fresh_var (make_named path) expr
  in
  let substitute_named bindings (named : Flambda.named) : Flambda.named =
    let sb to_substitute =
      try Variable.Map.find to_substitute bindings
      with Not_found -> to_substitute
    in
    match named with
    | Var v when Variable.Map.mem v substitution -> Var (sb v)
(*
      let fresh = Variable.rename v in
      Expr (bind v fresh (Var fresh))
*)
    | Var _ -> named
    | Symbol _ | Const _ -> named
    | Allocated_const _ | Read_mutable _ -> named
    | Assign { being_assigned; new_value }
        when Variable.Map.mem new_value substitution ->
      Assign { being_assigned; new_value = sb new_value; }
(*
      let fresh = Variable.rename new_value in
      bind new_value fresh (Assign { being_assigned; new_value = fresh })
*)
    | Assign _ -> named
    | Read_symbol_field _ -> named
    | Set_of_closures set_of_closures ->
      let set_of_closures =
        Flambda.create_set_of_closures
          ~function_decls:set_of_closures.function_decls
          ~free_vars:
            (Variable.Map.map (fun (spec_to : Flambda.specialised_to) ->
                { spec_to with var = sb spec_to.var; })
              set_of_closures.free_vars)
          ~specialised_args:
            (Variable.Map.map (fun (spec_to : Flambda.specialised_to) ->
                { spec_to with var = sb spec_to.var; })
              set_of_closures.specialised_args)
          ~direct_call_surrogates:set_of_closures.direct_call_surrogates
      in
      Set_of_closures set_of_closures
    | Project_closure project_closure ->
      Project_closure {
        project_closure with
        set_of_closures = sb project_closure.set_of_closures;
      }
    | Move_within_set_of_closures move_within_set_of_closures ->
      Move_within_set_of_closures {
        move_within_set_of_closures with
        closure = sb move_within_set_of_closures.closure;
      }
    | Project_var project_var ->
      Project_var {
        project_var with
        closure = sb project_var.closure;
      }
    | Prim (prim, args, dbg) ->
      Prim (prim, List.map sb args, dbg)
    | Proved_unreachable -> named
  in
  let make_var_subst var =
    if Variable.Map.mem var substitution then
      let fresh = Variable.rename var in
      fresh, (fun expr -> bind var fresh expr)
    else
      var, (fun x -> x)
  in
  let make_apply_kind_subst (func : Flambda.apply_kind) =
    match func with
    | Function -> Flambda.Function, (fun x -> x)
    | Method { kind; obj; } ->
      if Variable.Map.mem obj substitution then
        let fresh = Variable.rename obj in
        Flambda.Method { kind; obj = fresh; }, (fun expr -> bind obj fresh expr)
      else
        Flambda.Method { kind; obj; }, (fun x -> x)
  in
  let f (expr:Flambda.t) : Flambda.t =
    match expr with
    | Let ({ var = v; defining_expr = named; _ } as let_expr) ->
      let to_substitute =
        Variable.Set.filter
          (fun v -> Variable.Map.mem v substitution)
          (Flambda.free_variables_named named)
      in
      if Variable.Set.is_empty to_substitute then
        expr
      else
        let bindings =
          Variable.Map.of_set (fun var -> Variable.rename var) to_substitute
        in
        let named =
          substitute_named bindings named
        in
        let expr =
          let module W = Flambda.With_free_variables in
          W.create_let_reusing_body v named (W.of_body_of_let let_expr)
        in
        Variable.Map.fold (fun to_substitute fresh expr ->
            bind to_substitute fresh expr)
          bindings expr
    | Let_mutable let_mutable when
        Variable.Map.mem let_mutable.initial_value substitution ->
      let fresh = Variable.rename let_mutable.initial_value in
      bind let_mutable.initial_value fresh
        (Let_mutable { let_mutable with initial_value = fresh })
    | Let_mutable _ ->
      expr
    | Switch (cond, sw) when Variable.Map.mem cond substitution ->
      let fresh = Variable.rename cond in
      bind cond fresh (Switch (fresh, sw))
    | Switch _ ->
      expr
    | Apply_cont (exn, trap_action, args) ->
      let args, bind_args =
        List.split (List.map make_var_subst args)
      in
      List.fold_right (fun f expr -> f expr) bind_args @@
        Flambda.Apply_cont (exn, trap_action, args)
    | Apply { kind; func; args; continuation; call_kind; dbg; inline;
        specialise } ->
      let kind, bind_kind = make_apply_kind_subst kind in
      let func, bind_func = make_var_subst func in
      let args, bind_args =
        List.split (List.map make_var_subst args)
      in
      bind_kind @@
        bind_func @@
          List.fold_right (fun f expr -> f expr) bind_args @@
          Flambda.Apply
            { kind; func; args; continuation; call_kind; dbg; inline;
              specialise;
            }
    | Let_cont _ ->
      (* No variables directly used in those expressions *)
      expr
  in
  Flambda_iterators.map_toplevel_expr f expr

type sharing_key = Continuation.t
let make_key cont = Some cont

module Switch_storer =
  Switch.Store
    (struct
      (* CR mshinwell: Check if this thing uses polymorphic comparison.
         Should be ok if so, at the moment, but should be fixed. *)
      type t = Continuation.t
      type key = sharing_key
      let make_key = make_key
    end)

let fun_vars_referenced_in_decls
      (function_decls : Flambda.function_declarations) ~backend =
  let fun_vars = Variable.Map.keys function_decls.funs in
  let symbols_to_fun_vars =
    let module Backend = (val backend : Backend_intf.S) in
    Variable.Set.fold (fun fun_var symbols_to_fun_vars ->
        let closure_id = Closure_id.wrap fun_var in
        let symbol = Backend.closure_symbol closure_id in
        Symbol.Map.add symbol fun_var symbols_to_fun_vars)
      fun_vars
      Symbol.Map.empty
  in
  Variable.Map.map (fun (func_decl : Flambda.function_declaration) ->
      let from_symbols =
        Symbol.Set.fold (fun symbol fun_vars' ->
            match Symbol.Map.find symbol symbols_to_fun_vars with
            | exception Not_found -> fun_vars'
            | fun_var ->
              assert (Variable.Set.mem fun_var fun_vars);
              Variable.Set.add fun_var fun_vars')
          func_decl.free_symbols
          Variable.Set.empty
      in
      let from_variables =
        Variable.Set.inter func_decl.free_variables fun_vars
      in
      Variable.Set.union from_symbols from_variables)
    function_decls.funs

let closures_required_by_entry_point ~(entry_point : Closure_id.t) ~backend
    (function_decls : Flambda.function_declarations) =
  let dependencies =
    fun_vars_referenced_in_decls function_decls ~backend
  in
  let set = ref Variable.Set.empty in
  let queue = Queue.create () in
  let add v =
    if not (Variable.Set.mem v !set) then begin
      set := Variable.Set.add v !set;
      Queue.push v queue
    end
  in
  add (Closure_id.unwrap entry_point);
  while not (Queue.is_empty queue) do
    let fun_var = Queue.pop queue in
    match Variable.Map.find fun_var dependencies with
    | exception Not_found -> ()
    | fun_dependencies ->
      Variable.Set.iter (fun dep ->
          if Variable.Map.mem dep function_decls.funs then
            add dep)
        fun_dependencies
  done;
  !set

let all_functions_parameters (function_decls : Flambda.function_declarations) =
  Variable.Map.fold (fun _ ({ params } : Flambda.function_declaration) set ->
      Variable.Set.union set (Variable.Set.of_list params))
    function_decls.funs Variable.Set.empty

let all_free_symbols (function_decls : Flambda.function_declarations) =
  Variable.Map.fold (fun _ (function_decl : Flambda.function_declaration)
          syms ->
      Symbol.Set.union syms function_decl.free_symbols)
    function_decls.funs Symbol.Set.empty

let contains_stub (fun_decls : Flambda.function_declarations) =
  let number_of_stub_functions =
    Variable.Map.cardinal
      (Variable.Map.filter (fun _ { Flambda.stub } -> stub)
         fun_decls.funs)
  in
  number_of_stub_functions > 0

let clean_projections ~which_variables =
  Variable.Map.map (fun (spec_to : Flambda.specialised_to) ->
      match spec_to.projection with
      | None -> spec_to
      | Some projection ->
        let from = Projection.projecting_from projection in
        if Variable.Map.mem from which_variables then
          spec_to
        else
          ({ spec_to with projection = None; } : Flambda.specialised_to))
    which_variables

let projection_to_named (projection : Projection.t) : Flambda.named =
  match projection with
  | Project_var project_var -> Project_var project_var
  | Project_closure project_closure -> Project_closure project_closure
  | Move_within_set_of_closures move -> Move_within_set_of_closures move
  | Field (field_index, var) ->
    Prim (Pfield field_index, [var], Debuginfo.none)
