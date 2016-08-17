
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
  | Let_rec _
    ->
    let k_var = Variable.create "k_var" in
    Flambda.create_let k_var (Expr expr)
      (k k_var)

and cps_set_of_closures (set_of_closures:Flambda.set_of_closures) : Flambda.set_of_closures =
  Flambda_iterators.map_function_bodies set_of_closures
    ~f:(fun expr -> cps_expr expr (fun v -> Flambda.Var v))

let can_raise_prim (prim:Lambda.primitive) =
  match prim with
  (* TODO *)
  | _ -> true

let rec can_raise (expr:Flambda.t) =
  match expr with
  | Var _ -> false
  | Let _ -> begin
      try
        Flambda.iter_lets expr
          ~for_defining_expr:
            (fun _var named -> if can_raise_named named then raise Exit)
          ~for_last_body:
            (fun expr -> if can_raise expr then raise Exit)
          ~for_each_let:
            (fun _ -> ());
        false
      with Exit -> true
    end
  | Let_mutable { body } ->
    can_raise body
  | Let_rec (defs, body) ->
    List.fold_left (fun acc (_,named) -> acc || can_raise_named named) false defs
    || can_raise body
  | Static_raise _ ->
    false
  | Try_with (_body, _var, handler) ->
    can_raise handler
  | Static_catch (_, _, body, handler) ->
    can_raise body || can_raise handler
  | If_then_else (_cond, ifso, ifnot) ->
    can_raise ifso || can_raise ifnot
  | Switch (_, sw) ->
    List.fold_left (fun acc (_, e) -> acc || can_raise e) false sw.consts
    || List.fold_left (fun acc (_, e) -> acc || can_raise e) false sw.blocks
    || (match sw.failaction with None -> false | Some e -> can_raise e)
  | String_switch (_, branches, failaction) ->
    List.fold_left (fun acc (_, e) -> acc || can_raise e) false branches
    || (match failaction with None -> false | Some e -> can_raise e)
  | Proved_unreachable ->
    false
  | While (cond, body) ->
    can_raise cond || can_raise body
  | For { body } ->
    can_raise body
  | Assign _ ->
    false
  | Apply _ | Send _ ->
    true

and can_raise_named (named:Flambda.named) =
  match named with
  | Const _
  | Symbol _
  | Allocated_const _
  | Read_mutable _
  | Read_symbol_field _
  | Set_of_closures _
  | Project_closure _
  | Move_within_set_of_closures _
  | Project_var _ -> false
  | Expr expr ->
    can_raise expr
  | Prim (prim, _, _) ->
    can_raise_prim prim

let can_raise expr =
  let res = can_raise expr in
  Format.eprintf "can raise: %b@ %a@."
    res
    Flambda.print expr;
  res

let rec redirect_raise current_handler (expr:Flambda.t) : Flambda.t =
  match current_handler, expr with
  (* Only when backtrace are not propagated: this change the stack trace *)
  (* TODO: this could also be done when the handler never reraise *)
  | Some current_handler,
    Let { defining_expr = Prim (Praise _, [arg], _dbg) } when not !Clflags.debug ->
    Static_raise(current_handler, [arg])
  | Some current_handler,
    Let { defining_expr = Prim (Praise Raise_notrace, [arg], _dbg) } ->
    Static_raise(current_handler, [arg])
  | _, Try_with (body, var, handler) -> begin
      let body_handler =
        match handler with
        | Static_raise(k, [var']) when Variable.equal var var' ->
          Some k
        | _ ->
          None
      in
      let body = redirect_raise body_handler body in
      if can_raise body then
        Try_with (body, var,
                  redirect_raise current_handler handler)
      else
        let () = Format.eprintf "removed raise %a@." Flambda.print expr in
        body
    end
  | _ ->
    Flambda_iterators.map_subexpressions
      (redirect_raise current_handler)
      (redirect_raise_named current_handler)
      expr

and redirect_raise_named current_handler _var (named:Flambda.named) : Flambda.named =
  match named with
  | Expr expr ->
    Expr (redirect_raise current_handler expr)
  | Set_of_closures _set ->
    named
  | Symbol _ | Const _ | Allocated_const _ | Read_mutable _
  | Read_symbol_field (_, _) | Project_closure _ | Move_within_set_of_closures _
  | Project_var _ | Prim _ ->
    named

let get_static_exception_count count k =
  match Static_exception.Map.find k count with
  | exception Not_found -> 0
  | n -> n

(* let get_static_exception_count _count _k = *)
(*   15 *)

let count_static_exception_uses expr =
  let count = ref Static_exception.Map.empty in
  Flambda_iterators.iter_toplevel
    (fun (expr:Flambda.t) -> match expr with
       | Static_raise (k, _) ->
         count :=
           Static_exception.Map.add k
             (1 + get_static_exception_count !count k)
             !count
       | _ ->
         ())
    (fun _ -> ())
    expr;
  !count

type subst =
  | Static_exception of Static_exception.t
  | Expr of Variable.t list * Flambda.t

let empty_subst = Static_exception.Map.empty

let add_subst env ~subst ~to_ =
  Static_exception.Map.add subst to_ env

(* Ugly: to do differently *)
let inlined_static_exception = ref Static_exception.Map.empty
let clear () = inlined_static_exception := Static_exception.Map.empty
let incr_inlined_static_exception k =
  inlined_static_exception :=
    Static_exception.Map.add k
      (1 + get_static_exception_count !inlined_static_exception k)
      !inlined_static_exception

let rec simplify_tail_jump_count ~inline tail count env (expr:Flambda.t) : Flambda.t =
  let simplify_tail_jump tail env expr =
    simplify_tail_jump_count ~inline tail count env expr
  in
  match expr with
  | Static_raise (k, args) -> begin
      match Static_exception.Map.find k env with
      | exception Not_found -> expr
      | Static_exception subst -> Static_raise(subst, args)
      | Expr (params, expr) ->
        if tail then
          let subst =
            Variable.Map.of_list (List.combine params args)
          in
          incr_inlined_static_exception k;
          Flambda_utils.toplevel_substitution subst expr
        else
          expr
    end
  | Static_catch (k, params, Static_raise (k', args), handler) when
      Static_exception.equal k k'->
    let subst =
      Variable.Map.of_list (List.combine params args)
    in
    let handler = Flambda_utils.toplevel_substitution subst handler in
    simplify_tail_jump tail env handler
  | Static_catch (k, args, body, Static_raise (k', arg')) when
      Variable.List.equal args arg' ->
    simplify_tail_jump tail (add_subst env ~subst:k ~to_:(Static_exception k')) body
  | Static_catch (k, args, body, handler) -> begin
      let handler = simplify_tail_jump tail env handler in
      let uses = get_static_exception_count count k in
      let env =
        match uses, handler with
        | 1, _ when inline ->
          add_subst env ~subst:k ~to_:(Expr (args, handler))
        | _, Var _ ->
          add_subst env ~subst:k ~to_:(Expr (args, handler))
        | _ ->
          env
      in
      let body = simplify_tail_jump tail env body in
      if get_static_exception_count !inlined_static_exception k = uses then
        body
      else
        Static_catch (k, args, body, handler)
    end
  | Var _ | Apply _ | Proved_unreachable | Send _ | Assign _ -> expr
  | Let _ ->
    Flambda.map_lets expr
      ~for_defining_expr:(simplify_tail_named ~inline count env)
      ~for_last_body:(simplify_tail_jump tail env)
      ~after_rebuild:(fun x -> x)
  | Try_with (body, var, handler) ->
    Try_with (simplify_tail_jump false env body, var,
              simplify_tail_jump tail env handler)
  | If_then_else _ | Switch _ | String_switch _ | Let_mutable _
  | Let_rec _ ->
    Flambda_iterators.map_subexpressions
      (simplify_tail_jump tail env)
      (simplify_tail_named ~inline count env)
      expr
  | For _ | While _ ->
    Flambda_iterators.map_subexpressions
      (simplify_tail_jump false env)
      (simplify_tail_named ~inline count env)
      expr
  (* | _ -> *)
  (*   Format.eprintf "@.%a@." Flambda.print expr; *)
  (*   assert false *)

and simplify_tail_named ~inline count env (_var:Variable.t) (named:Flambda.named) : Flambda.named =
  match named with
  | Expr expr ->
    Expr (simplify_tail_jump_count ~inline false count env expr)
  | Set_of_closures set_of_closures ->
    Set_of_closures (simplify_tail_set_of_closures ~inline set_of_closures)
  | Prim _ | Const _ | Symbol _ | Project_closure _
  | Move_within_set_of_closures _ | Project_var _
  | Allocated_const _ | Read_mutable _ | Read_symbol_field _ ->
    named
  (* | _ -> *)
  (*   Format.eprintf "@.%a@." Flambda.print_named named; *)
  (*   assert false *)

and simplify_tail_set_of_closures ~inline (set_of_closures:Flambda.set_of_closures) =
  Flambda_iterators.map_function_bodies set_of_closures
    ~f:(simplify_tail_jump ~inline)

and simplify_tail_jump ~inline expr =
  let redirected = redirect_raise None expr in
  let count = count_static_exception_uses redirected in
  simplify_tail_jump_count ~inline true count empty_subst redirected

(* let rec simplify_static_catch is_continue (expr:Flambda.t) : Flambda.t = *)
(*   match expr with *)
(*   | Static_catch (k, args, *)
(*   | Static_raise (k, [v]) -> *)

let simplify_static_catch_noinline (expr:Flambda.t) : Flambda.t =
  clear ();
  let simplified = simplify_tail_jump ~inline:false expr in
  simplified

let simplify_static_catch (expr:Flambda.t) : Flambda.t =
  clear ();
  let simplified = simplify_tail_jump ~inline:true expr in
  simplified

let transform_expr (expr:Flambda.t) : Flambda.t =
  let k' = Static_exception.create () in
  let ret_var = Variable.create "ret_var" in
  let k v = Flambda.Static_raise (k', [v]) in
  (* let k v = Flambda.Var v in *)
  let body = cps_expr expr k in
  let body = Flambda.Static_catch (k', [ret_var], body, Var ret_var) in
  let _simplified_noinline = simplify_static_catch_noinline body in
  let simplified = simplify_static_catch body in
  Format.eprintf "original:@ %a@.@.cpsified:@ %a@.@.simplified noinline:@ %a@.@.simplified:@ %a@."
    Flambda.print expr
    Flambda.print body
    Flambda.print _simplified_noinline
    Flambda.print simplified;
  simplified

let run (program:Flambda.program) : Flambda.program =
  Flambda_iterators.map_exprs_at_toplevel_of_program
    ~f:transform_expr program
