(**************************************************************************)
(*                                                                        *)
(*                                OCaml                                   *)
(*                                                                        *)
(*                       Pierre Chambart, OCamlPro                        *)
(*                  Mark Shinwell, Jane Street Europe                     *)
(*                                                                        *)
(*   Copyright 2015 Institut National de Recherche en Informatique et     *)
(*   en Automatique.  All rights reserved.  This file is distributed      *)
(*   under the terms of the Q Public License version 1.0.                 *)
(*                                                                        *)
(**************************************************************************)

module A = Simple_value_approx
module C = Inlining_cost

type lifter = Flambda.program -> Flambda.program

let lift_lets_expr tree =
  let module W = Flambda.With_free_variables in
  let rec aux (expr : Flambda.t) : Flambda.t =
    match expr with
    | Let ({ var = v1;
        defining_expr = Expr (Let ({ var = v2; _ } as let2)); _ }  as let1) ->
      let body1 = W.of_body_of_let let1 in
      let body2 = W.of_body_of_let let2 in
      let inner_let = W.create_let_reusing_both v1 (W.expr body2) body1 in
      let def2 = W.of_defining_expr_of_let let2 in
      W.create_let_reusing_defining_expr v2 def2 (aux inner_let)
    | e -> e
  in
  Flambda_iterators.map aux (fun (named : Flambda.named) -> named) tree

let lift_lets program =
  Flambda_iterators.map_exprs_at_toplevel_of_program program ~f:lift_lets_expr

let rebuild_let
    (defs : (Variable.t * Flambda.named Flambda.With_free_variables.t) list)
    (body : Flambda.t) =
  let module W = Flambda.With_free_variables in
  List.fold_left (fun body (var, def) ->
      W.create_let_reusing_defining_expr var def body)
    body defs

let rec extract_lets
    (acc:(Variable.t * Flambda.named Flambda.With_free_variables.t) list)
    (let_expr:Flambda.let_expr) :
  (Variable.t * Flambda.named Flambda.With_free_variables.t) list *
  Flambda.t Flambda.With_free_variables.t =
  let module W = Flambda.With_free_variables in
  match let_expr with
  | { var = v1; defining_expr = Expr (Let let2); _ } ->
    let acc, body2 = extract_lets acc let2 in
    let acc = (v1, W.expr body2) :: acc in
    let body = W.of_body_of_let let_expr in
    extract acc body
  | { var = v; _ } ->
    let acc = (v, W.of_defining_expr_of_let let_expr) :: acc in
    let body = W.of_body_of_let let_expr in
    extract acc body

and extract acc (expr : Flambda.t Flambda.With_free_variables.t) =
  let module W = Flambda.With_free_variables in
  match W.contents expr with
  | Let let_expr ->
    extract_lets acc let_expr
  | _ ->
    acc, expr

let rec lift_lets_expr (expr:Flambda.t) : Flambda.t =
  let module W = Flambda.With_free_variables in
  match expr with
  | Let let_expr ->
    let defs, body = extract_lets [] let_expr in
    let defs = List.map lift_lets_named_with_free_variables defs in
    let body = lift_lets_expr (W.contents body) in
    rebuild_let defs body
  | e ->
    Flambda_iterators.map_subexpressions
      lift_lets_expr
      lift_lets_named
      e

and lift_lets_named_with_free_variables
    ((var, named):Variable.t * Flambda.named Flambda.With_free_variables.t) :
  Variable.t * Flambda.named Flambda.With_free_variables.t =
  let module W = Flambda.With_free_variables in
  match W.contents named with
  | Expr e ->
    var, W.expr (W.of_expr (lift_lets_expr e))
  | Set_of_closures set ->
    var,
    W.of_named
      (Set_of_closures
         (Flambda_iterators.map_function_bodies ~f:lift_lets_expr set))
  | Symbol _ | Const _ | Allocated_const _ | Read_mutable _
  | Read_symbol_field (_, _) | Project_closure _ | Move_within_set_of_closures _
  | Project_var _ | Prim _ ->
    var, named

and lift_lets_named _var (named:Flambda.named) : Flambda.named =
  let module W = Flambda.With_free_variables in
  match named with
  | Expr e ->
    Expr (lift_lets_expr e)
  | Set_of_closures set ->
    Set_of_closures
      (Flambda_iterators.map_function_bodies ~f:lift_lets_expr set)
  | Symbol _ | Const _ | Allocated_const _ | Read_mutable _
  | Read_symbol_field (_, _) | Project_closure _ | Move_within_set_of_closures _
  | Project_var _ | Prim _ ->
    named

let lift_lets program =
  let program'' =
    Flambda_iterators.map_exprs_at_toplevel_of_program program ~f:lift_lets_expr
  in
  if !Clflags.full_flambda_invariant_check then begin
    let program' = lift_lets program in
    assert(program' = program'')
  end;
  program''

let lifting_helper exprs ~evaluation_order ~create_body ~name =
  let vars, lets =
    (* [vars] corresponds elementwise to [exprs]; the order is unchanged. *)
    List.fold_right (fun (flam : Flambda.t) (vars, lets) ->
        match flam with
        | Var v ->
          (* Note that [v] is (statically) always an immutable variable. *)
          v::vars, lets
        | expr ->
          let v =
            Variable.create name ~current_compilation_unit:
                (Compilation_unit.get_current_exn ())
          in
          v::vars, (v, expr)::lets)
      exprs ([], [])
  in
  let lets =
    match evaluation_order with
    | `Right_to_left -> lets
    | `Left_to_right -> List.rev lets
  in
  List.fold_left (fun body (v, expr) ->
      Flambda.create_let v (Expr expr) body)
    (create_body vars) lets
