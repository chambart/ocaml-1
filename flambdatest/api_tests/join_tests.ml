(*
   Continuation k has three parameters, three uses.
   Variable x is defined after the fork but in all paths
   Use types:
   (=x, =x) { x : {0, 1} }
   ({0, 1, 2}, {0, 1, 2}) { x : {0, 1, 2} }
*)

module T = Flambda_type
module TE = Flambda_type.Typing_env

let test_join () =
  let env_at_fork =
    TE.create
      ~resolver:(fun _ -> None)
      ~get_imported_names:(fun () -> Name.Set.empty)
  in
  let param_a = Variable.create "a" in
  let param_b = Variable.create "b" in
  let param_c = Variable.create "c" in
  let n_a = Name.var param_a in
  let n_b = Name.var param_b in
  let n_c = Name.var param_c in
  let kind_ni = Flambda_kind.With_subkind.naked_immediate in
  let kp_a = Kinded_parameter.create param_a kind_ni in
  let kp_b = Kinded_parameter.create param_b kind_ni in
  let kp_c = Kinded_parameter.create param_c kind_ni in
  let params = [kp_c; kp_b; kp_a] in
  let env_at_fork = TE.add_definitions_of_params env_at_fork ~params in
  let var_x = Variable.create "x" in
  let n_x = Name.var var_x in
  let nb_x = Name_in_binding_pos.create n_x Name_mode.normal in
  let env = TE.add_definition env_at_fork nb_x Flambda_kind.naked_immediate in
  let alias name = T.alias_type_of Flambda_kind.naked_immediate (Simple.name name) in
  let imms_left =
    T.these_naked_immediates Target_imm.all_bools
  in
  let imms_right =
    T.these_naked_immediates Target_imm.zero_one_and_minus_one
  in
  let env_left = TE.add_equation env n_a imms_left in
  let env_left = TE.add_equation env_left n_b (alias n_x) in
  let env_left = TE.add_equation env_left n_c (alias n_x) in
  let env_left =
    TE.add_equation env_left n_x imms_left
  in
  let env_right =
    TE.add_equation env n_a (alias n_x)
  in
  let env_right =
    TE.add_equation env_right n_b imms_right
  in
  let env_right =
    TE.add_equation env_right n_c (alias n_x)
  in
  let env_right =
    TE.add_equation env_right n_x imms_right
  in
  let join_env =
    TE.cut_and_n_way_join
      env_at_fork
      [env_left, Obj.magic 0, Obj.magic 0;
       env_right, Obj.magic 0, Obj.magic 0]
      ~params
      ~unknown_if_defined_at_or_later_than:Scope.initial
      ~extra_lifted_consts_in_use_envs:Symbol.Set.empty
      ~extra_allowed_names:Name_occurrences.empty
  in
  Format.eprintf
    "Environments:@.\
     Env at fork:@ %a@.\
     Left env:@ %a@.\
     Right env:@ %a@.@.\
     Join env:@ %a@.@."
    TE.print env_at_fork
    TE.print env_left
    TE.print env_right
    TE.print join_env;
  ()

let _ =
  let comp_unit =
    let id = Ident.create_persistent "Test" in
    let linkage_name = Linkage_name.create "camlTest" in
    Compilation_unit.create id linkage_name
  in
  Compilation_unit.set_current comp_unit;
  test_join ()

