open Abstract_identifiers
open Flambda

type env =
  { sb : Variable.t VarMap.t;
    exn : Static_exception.t StaticExceptionMap.t;
    comp_unit : Symbol.Compilation_unit.t }

let subst env var = try VarMap.find var env.sb with Not_found -> var

let new_subst env var =
  let new_var = Variable.rename env.comp_unit var in
  { env with sb = VarMap.add var new_var env.sb }, new_var

let subst_exn env exn =
  try StaticExceptionMap.find exn env.exn with Not_found -> exn

let new_subst_exn env exn =
  let new_exn = Static_exception.create () in
  { env with exn = StaticExceptionMap.add exn new_exn env.exn }, new_exn

let rec loop env expr = match expr with
  | Fvar(var,d) -> Fvar(subst env var,d)

  | Fassign(var,flam,d) ->
      let var = subst env var in
      let flam = loop env flam in
      Fassign(var,flam,d)

  | Flet(kind,var,def,body,d) ->
      let def = loop env def in
      let env, var = new_subst env var in
      let body = loop env body in
      Flet(kind,var,def,body,d)
  | Fletrec(defs,body,d) ->
      let aux (var,def) (env, defs) =
        let env, var = new_subst env var in
        env, (var,def) :: defs in
      let env, defs = List.fold_right aux defs (env, []) in
      let defs = List.map (fun (var,def) -> var, loop env def) defs in
      let body = loop env body in
      Fletrec(defs,body,d)

  | Ffor(var, lo, hi, dir, body, d) ->
      let lo = loop env lo in
      let hi = loop env hi in
      let env, var = new_subst env var in
      let body = loop env body in
      Ffor(var, lo, hi, dir, body, d)

  | Ftrywith(body, var, handler, d) ->
      let body = loop env body in
      let env, var = new_subst env var in
      let handler = loop env handler in
      Ftrywith(body, var, handler, d)

  | Fstaticcatch(exn, vars, body, handler, d) ->
      let body_env, exn = new_subst_exn env exn in
      let body = loop body_env body in
      let aux var (env, vars) =
        let env, var = new_subst env var in
        env, var::vars in
      let handler_env, vars =
        List.fold_right aux vars (env, []) in
      let handler = loop handler_env handler in
      Fstaticcatch(exn, vars, body, handler, d)

  | Fstaticraise(exn, args, d) ->
      let exn = subst_exn env exn in
      let args = List.map (loop env) args in
      Fstaticraise(exn, args, d)

  | Fclosure _ ->
      (* Not handled yet *)
      raise Exit

  (* | Fapply({ ap_function; ap_arg; ap_kind; ap_dbg}, d) -> *)
  (*     let ap_kind = match ap_kind with *)
  (*       | Indirect -> Indirect *)
  (*       | Direct func -> Direct (subst_cf env func) *)
  (*     in *)
  (*     let ap_function = loop env ap_function in *)
  (*     let ap_arg = List.map (loop env) ap_arg in *)
  (*     Fapply({ ap_function; ap_arg; ap_kind; ap_dbg}, d) *)

  (* | Ffunction({ fu_closure; fu_fun; fu_relative_to }, d) -> *)
  (*     let fu_closure = loop env fu_closure in *)
  (*     let fu_fun = subst_cf env fu_fun in *)
  (*     let fu_relative_to = Misc.may_map (subst_cf env) fu_relative_to in *)
  (*     Ffunction({ fu_closure; fu_fun; fu_relative_to }, d) *)

  (* | Fvariable_in_closure({ vc_closure; vc_fun; vc_var }, d) -> *)
  (*     let vc_closure = loop env vc_closure in *)
  (*     let vc_fun = subst_cf env vc_fun in *)
  (*     let vc_var = subst_cv env vc_var in *)
  (*     Fvariable_in_closure({ vc_closure; vc_fun; vc_var }, d) *)

  | Fapply _ | Ffunction _ | Fvariable_in_closure _


  | Fconst _ | Fsymbol _ | Funreachable _
  | Fprim _ | Fswitch _ | Fifthenelse _
  | Fsequence _ | Fwhile _ | Fsend _
  | Fevent _ ->
      let aux _acc bound expr =
        assert(VarSet.is_empty bound);
        _acc, loop env expr in
      snd (Flambdaiter.fold_subexpressions aux () expr)

let substitute_bound_variables comp_unit subst expr =
  try Some (loop { comp_unit; sb = subst; exn = StaticExceptionMap.empty } expr)
  with Exit -> None
