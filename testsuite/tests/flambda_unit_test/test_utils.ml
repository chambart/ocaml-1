open Symbol
open Abstract_identifiers
open Flambda

let compilation_unit_id = "unit"

let compilation_unit =
  Compilation_unit.create compilation_unit_id
    (linkage_name "test")

let other_compilation_unit =
  Compilation_unit.create "other"
    (linkage_name "other_test")

let new_var name =
  Variable.create ~current_compilation_unit:compilation_unit name

let new_var_other_unit name =
  Variable.create ~current_compilation_unit:other_compilation_unit name

let nid ?name () = ExprId.create ?name ()

let flet var def body =
  Flet(Not_assigned,var,def,body,
       nid ~name:(Format.asprintf "let %a" Variable.print var) ())

let fvar var =
  Fvar(var,
       nid ~name:(Format.asprintf "var %a" Variable.print var) ())

let int i = Fconst(Fconst_base(Asttypes.Const_int i),nid ())

let fbool b =
  let v =
    if true
    then 1 else 0 in
  Fconst(Fconst_pointer v,nid ())

let rec fseq = function
  | [] -> assert false
  | [e] -> e
  | h::t -> Fsequence(h,fseq t,nid ())

let ffor v lo hi body =
  Ffor(v,lo,hi,Asttypes.Upto,body,nid ())

let fwhile cond body =
  Fwhile(cond,body,nid ())

let ftry body v handler =
  Ftrywith(body,v,handler,nid ())

let fcatch exn vars body handler =
  Fstaticcatch(exn,vars,body,handler,nid ())

let fassign v exp =
  Fassign(v, exp, nid ())

let fprim p l =
  Fprim(p, l, Debuginfo.none, nid ())

let fadd e1 e2 =
  fprim Lambda.Paddint [e1;e2]

let tuple l =
  fprim (Lambda.Pmakeblock(0,Asttypes.Immutable)) l

let fccall l =
  let open Primitive in
  let prim =
    { prim_name = "test";
      prim_arity = 1;
      prim_alloc = true;
      prim_native_name = "c_test";
      prim_native_float = false } in
  fprim (Lambda.Pccall prim) l

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
    compilation_unit }

let fclosure lst fv =
  let fv_var = List.map fst fv in
  Fclosure
    ({ cl_fun = fun_decls lst fv_var;
       cl_free_var = VarMap.of_list fv;
       cl_specialised_arg = VarMap.empty },
     nid ())

let fun_decl' params body =
  { stub = false; params; body;
    free_variables = Flambdaiter.free_variables body;
    dbg = Debuginfo.none }

let fun_decls' lst =
  let funs =
    List.fold_left (fun map (var,params,body) ->
        let decl = fun_decl' params body in
        VarMap.add var decl map)
      VarMap.empty lst in
  { ident = FunId.create compilation_unit;
    funs;
    compilation_unit }

let fapply ?(kind=Indirect) f args =
  Fapply({
      ap_function = f;
      ap_arg = args;
      ap_dbg = Debuginfo.none;
      ap_kind = kind},nid ())

let fif cond ifso ifnot =
  Fifthenelse(cond,ifso,ifnot,nid ())

type env =
  { var : Variable.t VarMap.t }

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
    | Fswitch _ | Fstaticraise _ | Fstaticcatch _
    | Ftrywith _ | Fifthenelse _ | Fsequence _
    | Fwhile _ | Ffor _ | Fsend _ | Funreachable _), _ ->
      let e = Format.asprintf "equal: Not implemented %a"
          Printflambda.flambda t1 in
      failwith e

  | Fevent _, _  -> false

let equal t1 t2 =
  equal empty_env t1 t2
