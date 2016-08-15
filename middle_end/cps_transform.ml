
[@@@ocaml.warning "+a-4-9-30-40-41-42"]

(* TODO: CPS style *)

(* let stbr body var cont : Flambda.t = *)
(*   let k = Static_exception.create () in *)
(*   Static_catch(k, [var], body (fun v -> Flambda.Static_raise (k, [v])), cont) *)

let letbr body cont : Flambda.t =
  let k = Static_exception.create () in
  Static_catch(k, [], body (Flambda.Static_raise (k, [])), cont)

let rec cps_expr (expr:Flambda.t) (k:Variable.t -> Flambda.t) : Flambda.t =
  match expr with
  | Var v ->
    k v
  | Let { var; defining_expr = Expr def_expr; body } ->
    let body = cps_expr body k in
    let let_k = Static_exception.create () in
    let kont v = Flambda.Static_raise (let_k, [v]) in
    let def_expr = cps_expr def_expr kont in
    Static_catch (let_k, [var], def_expr, body)
  | Let { var; defining_expr = Set_of_closures set; body } ->
    let defining_expr : Flambda.named =
      Set_of_closures (cps_set_of_closures set)
    in
    let body = cps_expr body k in
    Flambda.create_let var defining_expr body
  | Let { var; defining_expr; body } ->
    let body = cps_expr body k in
    Flambda.create_let var defining_expr body
  | Let_mutable { var; initial_value; contents_kind; body } ->
    let body = cps_expr body k in
    Let_mutable { var; initial_value; contents_kind; body }
  | If_then_else (var, ifso, ifnot) ->
    letbr (fun j_ifso ->
        letbr (fun j_ifnot ->
            If_then_else (var, j_ifso, j_ifnot))
          (cps_expr ifnot k))
      (cps_expr ifso k)
  | Switch (var, sw) ->
    let mk (n, lam) =
      let st = Static_exception.create () in
      (n, Flambda.Static_raise (st, [])),
      (st, cps_expr lam k)
    in
    let consts, st_consts = List.split (List.map mk sw.consts) in
    let blocks, st_blocks = List.split (List.map mk sw.blocks) in
    let failaction, st_failaction =
      match sw.failaction with
      | None -> None, []
      | Some failaction ->
        let st = Static_exception.create () in
        Some (Flambda.Static_raise (st, [])),
        [st, cps_expr failaction k]
    in
    List.fold_left (fun body (st, cont) -> Flambda.Static_catch(st, [], body, cont))
      (Flambda.Switch (var, { sw with consts; blocks; failaction }))
      (st_consts @ st_blocks @ st_failaction)
  | String_switch (cond, branches, failaction) ->
    let mk (n, lam) =
      let st = Static_exception.create () in
      (n, Flambda.Static_raise (st, [])),
      (st, cps_expr lam k)
    in
    let branches, st_branches =
      List.split (List.map mk branches)
    in
    let failaction, st_failaction =
      match failaction with
      | None -> None, []
      | Some failaction ->
        let st = Static_exception.create () in
        Some (Flambda.Static_raise (st, [])),
        [st, cps_expr failaction k]
    in
    List.fold_left (fun body (st, cont) -> Flambda.Static_catch(st, [], body, cont))
      (Flambda.String_switch (cond, branches, failaction))
      (st_failaction @ st_branches)
  | Try_with (body, var, handler) ->
    let st = Static_exception.create () in
    let var' = Variable.rename var in
    Static_catch(
      st, [var],
      Try_with (cps_expr body k, var', Static_raise (st, [var'])),
      cps_expr handler k)
  | Assign _
  | Apply _
  | Send _
  | Proved_unreachable
  | Static_raise _ ->
    expr
  | Static_catch (se, args, body, handler) ->
    Static_catch (se, args, cps_expr body k, cps_expr handler k)
  | For _ | While _
  | _
    ->
    let k_var = Variable.create "k_var" in
    Flambda.create_let k_var (Expr expr)
      (k k_var)

and cps_set_of_closures (set_of_closures:Flambda.set_of_closures) : Flambda.set_of_closures =
  Flambda_iterators.map_function_bodies set_of_closures
    ~f:(fun expr -> cps_expr expr (fun v -> Flambda.Var v))

(* let rec simplify_tail_jump tail env expr = *)
(*   match expr with *)
(*   | Static_catch (k, args, body, Static_raise (k', arg')) when Variableargs = arg' -> *)


(* let rec simplify_static_catch is_continue (expr:Flambda.t) : Flambda.t = *)
(*   match expr with *)
(*   | Static_catch (k, args, *)
(*   | Static_raise (k, [v]) -> *)

let simplify_static_catch (expr:Flambda.t) : Flambda.t =
  expr

let transform_expr (expr:Flambda.t) : Flambda.t =
  (* let k = Static_exception.create () in *)
  (* let ret_var = Variable.create "ret_var" in *)
  let k v = Flambda.Var v in
  let body = cps_expr expr k in
  let body = simplify_static_catch body in
  (* Static_catch (k, [ret_var], body, Var ret_var) *)
  body

let run (program:Flambda.program) : Flambda.program =
  Flambda_iterators.map_exprs_at_toplevel_of_program
    ~f:transform_expr program
