(** Optimisations for some special use cases *)

open Abstract_identifiers
open Flambda

(*******************************************************)
(**
  {[
    let ref iter f l =
      match l with
      | [] -> ()
      | h :: t ->
          f h;
          iter f l
  ]}

    Rewritten to

  {[
    let ref iter' f l =
      match l with
      | [] -> ()
      | h :: t ->
          f h;
          iter' f l

    let iter f l = (* stub *)
      match l with
      | [] -> ()
      | _  -> iter' f l

  ]}
*)

let applied_variables expr =
  let set = ref VarSet.empty in
  let aux = function
    | Fapply({ ap_function = Fvar( var, _ ) }, _) ->
        set := VarSet.add var !set
    | _ -> ()
  in
  Flambdaiter.iter_toplevel aux expr;
  !set

let simple_primitive prim =
  let open Lambda in
  match prim with
  | Pisint | Pisout | Pbittest | Pfield _
  | Pintcomp _
  | Psequand | Psequor | Pnot -> true
  | _ -> false

(* pure and cheap *)
let rec simple_expression = function
  | Fvar _ -> true
  | Fconst _ -> true
  | Fprim(p, args, _, _) ->
      simple_primitive p &&
      List.for_all simple_expression args
  | _ -> false

let matching_pattern = function
  | Fifthenelse( cond, ifso, ifnot, _ ) ->
      simple_expression cond
      && (simple_expression ifso || simple_expression ifnot)
  | _ -> false

let should_apply { cl_fun = { funs } } =
  (VarMap.cardinal funs = 1)
  &&

  let fun_var, fun_def = VarMap.choose funs in
  let applied_params =
    VarSet.inter
      (applied_variables fun_def.body)
      (VarSet.of_list fun_def.params) in
  (not (VarSet.is_empty applied_params))
  &&

  matching_pattern fun_def.body

let new_var v =
  Variable.create
    ~current_compilation_unit:(Compilenv.current_unit ())
    v

let rename_var v =
  Variable.rename
    ~current_compilation_unit:(Compilenv.current_unit ())
    v

let nid () = ExprId.create ()

let substitute_closure closure =
  let subst_var =
    let map = ref VarMap.empty in
    fun var ->
      try VarMap.find var !map
      with Not_found ->
        let var' = rename_var var in
        map := VarMap.add var var' !map;
        var'
  in
  let subst_fun_decl fun_decl =
    let free_variables = VarSet.map subst_var fun_decl.free_variables in
    let subst = VarMap.of_set subst_var fun_decl.free_variables in
    { stub = fun_decl.stub;
      params = List.map subst_var fun_decl.params;
      free_variables;
      body = Flambdaiter.toplevel_substitution subst fun_decl.body;
      dbg = fun_decl.dbg }
  in
  let subst = VarMap.mapi (fun v _ -> subst_var v) closure.cl_fun.funs in
  let closure =
    { cl_fun =
        { ident = FunId.create (Compilenv.current_unit ());
          funs =
            VarMap.map subst_fun_decl
              (VarMap.map_keys subst_var closure.cl_fun.funs);
          compilation_unit = (Compilenv.current_unit ()) };
      cl_free_var =
        VarMap.map_keys subst_var closure.cl_free_var;
      cl_specialised_arg =
        VarMap.map_keys subst_var closure.cl_specialised_arg } in
  closure, subst

let add_indirection ({ cl_fun = { funs } as cl_fun } as closure) =
  match VarMap.bindings funs with
  | [] | _ :: _ :: _  -> assert false
  | [orig_fun_var, fun_def] ->
      let fun_var = rename_var orig_fun_var in

      let stub =
        let inner_fun_var = rename_var fun_var in
        let apply_orig () =
          Fapply({ap_function = Fvar(inner_fun_var, nid ());
                  ap_arg = List.map
                      (fun v -> Fvar(v, nid ()))
                      fun_def.params;
                  ap_kind = Indirect;
                  ap_dbg = fun_def.dbg}, nid ()) in

        let body = match fun_def.body with
          | Fifthenelse( cond, ifso, ifnot, d )
            when
              simple_expression cond
              && (simple_expression ifso || simple_expression ifnot) ->
              let replace_expr expr =
                if simple_expression expr
                then expr
                else apply_orig ()
              in
              Fifthenelse( cond,
                           replace_expr ifso,
                           replace_expr ifnot, d )
          | _ -> assert false
        in
        let stub_fun_def =
          { stub = true;
            params = fun_def.params;
            free_variables = Flambdaiter.free_variables body;
            body;
            dbg = fun_def.dbg } in
        let fun_defs =
          { ident = cl_fun.ident;
            funs = VarMap.singleton orig_fun_var stub_fun_def;
            compilation_unit = cl_fun.compilation_unit } in
        let closure =
          { cl_fun = fun_defs;
            cl_free_var =
              VarMap.add
                inner_fun_var (Fvar(fun_var, nid()))
                closure.cl_free_var;
            cl_specialised_arg = VarMap.empty } in
        Fclosure(closure, nid ())
      in

      let closure, subst_functions = substitute_closure closure in
      let new_fun_var = VarMap.find orig_fun_var subst_functions in

      Flet(Not_assigned, fun_var,
           Ffunction({ fu_closure = Fclosure(closure, nid ());
                       fu_fun = Closure_function.wrap new_fun_var;
                       fu_relative_to = None }, nid ()),
           stub,
           nid ())

let function_indirection tree =
  let aux expr = match expr with
    | Fclosure (closure, _ ) ->
        if should_apply closure
        then add_indirection closure
        else expr
    | _ -> expr
  in
  Flambdaiter.map aux tree

open Flambdapasses

let pass =
  (* TODO: find a name defining it... *)
  { name = "function indirection";
    pass = (fun expr _ -> function_indirection expr) }

let () =
  Flambdapasses.register_pass Before 10 pass

let passes = [pass]
