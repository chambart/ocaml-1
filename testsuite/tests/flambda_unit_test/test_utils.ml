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
