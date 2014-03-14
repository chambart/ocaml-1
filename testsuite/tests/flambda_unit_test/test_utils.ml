open Flambda

let compilation_unit =
  let sym_unit = Ident.create_persistent "unit" in
  Compilation_unit.create
    { sym_unit;
      sym_label = linkage_name (Compilenv.symbol_for_global sym_unit) }

let other_compilation_unit =
  let sym_unit = Ident.create_persistent "other" in
  Compilation_unit.create
    { sym_unit;
      sym_label = linkage_name (Compilenv.symbol_for_global sym_unit) }

let new_var name =
  let id = Ident.create name in
  Variable.create ~compilation_unit id

let new_var_other_unit name =
  let id = Ident.create name in
  Variable.create ~compilation_unit:other_compilation_unit id

let nid () = ExprId.create ()

let flet var def body =
  Flet(Not_assigned,var,def,body,nid ())

let fvar var = Fvar(var,nid ())

let int i = Fconst(Fconst_base(Asttypes.Const_int i),nid ())

let rec fseq = function
  | [] -> assert false
  | [e] -> e
  | h::t -> Fsequence(h,fseq t,nid ())

let ffor v lo hi body =
  Ffor(v,lo,hi,Asttypes.Upto,body,nid ())

let ftry body v handler =
  Ftrywith(body,v,handler,nid ())

let fcatch exn vars body handler =
  Fcatch(exn,vars,body,handler,nid ())

let fassign v exp =
  Fassign(v, exp, nid ())

let fun_decl params fv body =
  { stub = false;
    params;
    free_variables = VarSet.of_list (params @ fv);
    body;
    dbg = Debuginfo.none }

let fun_decls lst fv =
  let functs = List.map (fun (var,_,_) -> var) lst in
  let funs =
    List.fold_left (fun map (var,params,body) ->
        let decl = fun_decl params (fv@functs) body in
        VarMap.add var decl map)
      VarMap.empty lst in
  { ident = FunId.create compilation_unit;
    funs;
    compilation_unit;
    closed = false }

let fclosure lst fv =
  let fv_var = List.map fst fv in
  Fclosure
    ({ cl_fun = fun_decls lst fv_var;
       cl_free_var = VarMap.of_list fv;
       cl_specialised_arg = VarMap.empty },
     nid ())


type env =
  { var : variable VarMap.t }

let empty_env =
  { var = VarMap.empty }

let add_var v v' env =
  { var = VarMap.add v v' env.var }

let equal_var env v v' =
  try Variable.equal (VarMap.find v env.var) v'
  with Not_found -> false

let equal_let_kind k1 k2 = match k1, k2 with
  | Assigned, Assigned
  | Not_assigned, Not_assigned -> true
  | (Assigned | Not_assigned), (Assigned | Not_assigned) -> false

let rec equal env t1 t2 = match t1, t2 with
  | Fvar(v1, _), Fvar(v2, _) -> equal_var env v1 v2
  | Fsymbol(s1,_), Fsymbol(s2,_) -> Symbol.equal s1 s2
  | Fconst (c1, _), Fconst (c2, _) -> c1 = c2


  | Flet (k1, v1, def1, body1, _), Flet (k2, v2, def2, body2, _) ->
      equal_let_kind k1 k2 &&
      equal env def1 def2 &&
      equal (add_var v1 v2 env) body1 body2

  | Fprim (p1, args1, _, _), Fprim (p2, args2, _, _) ->
      p1 = p2 &&
      List.for_all2 (equal env) args1 args2

  | (Fvar _| Fsymbol _| Fconst _| Flet _ | Fprim _), _ ->
      false

  | (Fassign _ | Fclosure _
    | Fapply _ | Fletrec _ | Ffunction _ | Fvariable_in_closure _
    | Fswitch _ | Fstaticfail _ | Fcatch _
    | Ftrywith _ | Fifthenelse _ | Fsequence _
    | Fwhile _ | Ffor _ | Fsend _ | Funreachable _), _ ->
      let e = Format.asprintf "equal: Not implemented %a"
          Printflambda.flambda t1 in
      failwith e

let equal t1 t2 =
  equal empty_env t1 t2
