(***********************************************************************)
(*                                                                     *)
(*                                OCaml                                *)
(*                                                                     *)
(*                     Pierre Chambart, OCamlPro                       *)
(*                                                                     *)
(*  Copyright 2014 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the Q Public License version 1.0.               *)
(*                                                                     *)
(***********************************************************************)

(** This module declare two passes:

    * move_lets: find the optimal position in the tree for pure variable declarations.
    * remove_trivial_lets: simplifies expressions of the form {[let x = expr in x]}
      to {[expr]} (simplifications made obvious by move_lets)

    move_let tries to minimize computations by:
    - moving declarations inside branching expressions (if, match, ...) if
      it is used in a single branch.
    - moving declarations outside loops (for, while) if it is invariant in
      the loop.

    move_lets works in 2 passes:
    - remove every pure variable declarations from the expression
    - reinsert the declarations at the 'right' position:

    The 'right' position is as deep as possible in the tree such that it is:
    - at a correct position:
      * higher than every usage of the variable.
      * below than every referenced variable in the definition
    - higher than as much loop as possible

    The reinsertion is done by traversing the tree bottom up, adding a declaration when
    - every use (accounting for not yet reinserted declarations) is below the current point
    - and the current point is not in a loop or the variable is not constant for the current loop

*)

open Abstract_identifiers
open Flambda

let nid () = ExprId.create ()

type lets =
  { expr : ExprId.t flambda;
    kind : let_kind }

type links =
  { uses : ExprSet.t VarMap.t;
    lets : lets VarMap.t;
    lets_dep : VarSet.t VarMap.t;
    floating_lets : VarSet.t }

let empty_links = { lets = VarMap.empty; uses = VarMap.empty;
                    lets_dep = VarMap.empty; floating_lets = VarSet.empty }

let variables_connected_components lets =
  let let_dep { expr } =
    Flambdaiter.free_variables expr in
  let lets_dep = VarMap.map let_dep lets in
  let floating_vars = VarMap.keys lets in
  let lets_floating_dep = VarMap.map (VarSet.inter floating_vars) lets_dep in
  let components =
    Variable_connected_components.component_graph lets_floating_dep in
  let component_deps =
    Array.map (fun (comp, _) ->
        let deps = match comp with
          | Variable_connected_components.No_loop id ->
              VarMap.find id lets_dep
          | Variable_connected_components.Has_loop ids ->
              List.fold_left (fun set id ->
                  VarSet.union set (VarMap.find id lets_dep))
                VarSet.empty ids in
        VarSet.diff deps floating_vars)
      components in
  components, component_deps

let lets_dep lets =
  let components, component_deps =
    variables_connected_components lets in

  let let_deps = ref VarMap.empty in
  for i = Array.length components - 1 downto 0 do
    let comp, deps = components.(i) in
    let var_deps =
      List.fold_left (fun set dep -> VarSet.union set component_deps.(dep))
        component_deps.(i) deps in
    component_deps.(i) <- var_deps;
    let ids = match comp with
      | Variable_connected_components.No_loop id -> [id]
      | Variable_connected_components.Has_loop ids -> ids in
    let_deps :=
      List.fold_left (fun let_deps id -> VarMap.add id var_deps let_deps)
        !let_deps ids;
  done;
  !let_deps

(* like Flambdaiter.free_variables, except that it go throug closures *)
let unbound_variables tree =
  let rec loop (free,bound) bound_here expr =
    let free_vars = Flambdaiter.expression_free_variables expr in
    let free = VarSet.union free free_vars in
    let bound = VarSet.union bound bound_here in
    Flambdaiter.fold_subexpressions loop (free,bound) expr
  in
  let (free,bound), _ = loop (VarSet.empty, VarSet.empty) VarSet.empty tree in
  VarSet.diff free bound

(* Some simple dead code elimination:
   A variable is usefull if it is referenced in an usefull expression:
   - the base expression with pure variable declarations removed is usefull
   - if a variable is usefull its expression is usefull *)
let usefull_lets lets expr =
  let let_deps = VarMap.map (fun { expr } -> unbound_variables expr) lets in
  let roots = unbound_variables expr in
  let live = ref VarSet.empty in
  let queue = Queue.create () in
  let add_live v =
    if not (VarSet.mem v !live)
    then (live := VarSet.add v !live;
          Queue.push v queue)
  in
  VarSet.iter add_live roots;
  while not (Queue.is_empty queue) do
    let v = Queue.take queue in
    let deps = try VarMap.find v let_deps with Not_found -> VarSet.empty in
    VarSet.iter add_live deps
  done;
  VarMap.filter (fun v _ -> VarSet.mem v !live) lets

let mark_needs expr lets =
  let links = ref empty_links in

  let add_node expr =
    let eid = data_at_toplevel_node expr in
    let fv = Flambdaiter.expression_free_variables expr in

    let add_use v uses =
      let set =
        try VarMap.find v uses
        with Not_found -> ExprSet.empty in
      VarMap.add v (ExprSet.add eid set) uses in

    let uses = VarSet.fold add_use fv !links.uses in
    links := { !links with uses } in
  Flambdaiter.iter add_node expr;
  VarMap.iter (fun _ { expr } -> Flambdaiter.iter add_node expr) lets;

  { !links with lets }

let add_pure_var kind var env =
  match kind with
  | Assigned -> env
  | Not_assigned -> Flambdapurity.mark_unasigned_variable var env

let add_let kind var expr acc =
  VarMap.add var { expr; kind } acc

type ret = lets VarMap.t * ExprId.t flambda

(* Remove pure variable declarations from the expression
   and returns the set of removed declarations:

   if expr is some:

   [let x = let y = 2 in y + 1 in
    x + 2]

   returns

   [x + 2] and
   {x -> y + 1;
    y -> 2}
*)
let rec extract_pure_lets env acc expr : ret =
  match expr with
  | Flet(kind,var,def,body,eid) ->
      let body_env = add_pure_var kind var env in
      if Flambdapurity.pure_expression_toplevel env def
      then
        let acc, def = extract_pure_lets env acc def in
        let acc = add_let kind var def acc in
        extract_pure_lets body_env acc body
      else
        let acc, def = extract_pure_lets env acc def in
        let acc, body = extract_pure_lets body_env acc body in
        acc, Flet(kind,var,def,body,eid)

  (* TODO: letrec *)

  | e ->
      let aux acc bound expr =
        let env = VarSet.fold (add_pure_var Not_assigned) bound env in
        let acc, expr = extract_pure_lets env acc expr in
        acc, expr in
      let acc, e =
        Flambdaiter.fold_subexpressions aux acc e in
      acc, e

let prepare expr =

  let env =
    Flambdapurity.mark_pure_functions
      (Flambdapurity.pure_functions expr)
      Flambdapurity.empty_env in
  let lets, expr = extract_pure_lets env VarMap.empty expr in

  (* We remove useless lets to avoid problems when reinserting the
     declarations: The declarations are inserted as soon as every
     reference to them is already inserted in the tree. Variables that
     are never referenced will never be inserted, so they would
     prevent every variable referenced from their declaration to be
     inserted. *)
  let lets = usefull_lets lets expr in
  let links = mark_needs expr lets in
  let links = { links with lets_dep = lets_dep lets; floating_lets = VarMap.keys lets } in
  links, expr

type rebuild_ret = links * VarSet.t * ExprId.t flambda

let remove_bound_vars uses bound =
  (* remove need of variables bound by a non floating expression *)
  VarSet.fold (fun v uses -> VarMap.remove v uses) bound uses

let remove_use v eid uses =
  let eids = try VarMap.find v uses with Not_found -> assert false in
  assert(ExprSet.mem eid eids);
  if ExprSet.cardinal eids = 1
  then begin
    VarMap.remove v uses
  end
  else VarMap.add v (ExprSet.remove eid eids) uses

let add_use v eid uses =
  let set =
    try VarMap.find v uses
    with Not_found -> ExprSet.empty in
  VarMap.add v (ExprSet.add eid set) uses

let move_uses_to_parent parent eid uses needed =
  let aux v uses =
    uses
    |> remove_use v eid
    |> add_use v parent
  in
  VarSet.fold aux needed uses

let find_lets_to_add links loop_stack needed =
  let aux v set =
    let eids = try VarMap.find v links.uses with Not_found -> assert false in
    let card = ExprSet.cardinal eids in
    assert(card > 0);
    if ExprSet.cardinal eids = 1
    then match loop_stack with
        | [] -> (* no loop *)
            VarSet.add v set
        | loop_top :: _ ->
            let deps = VarMap.find v links.lets_dep in
            if VarSet.is_empty (VarSet.inter loop_top deps)
            then set (* if no needed var bound since the last loop: we move lets out of the loop *)
            else VarSet.add v set
    else set in
  VarSet.fold aux needed VarSet.empty

let is_loop = function
  | Fwhile _
  | Ffor _ -> true
  | _ -> false

type loop_stack = VarSet.t list

let rec rebuild links expr bound (loop_stack:loop_stack) : rebuild_ret =
  let current_eid = data_at_toplevel_node expr in
  let expr_needed = Flambdaiter.expression_free_variables expr in
  let links = { links with uses = remove_bound_vars links.uses bound } in
  let inner_loop_stack =
    if is_loop expr
    then VarSet.empty :: loop_stack
    else loop_stack
  in
  let (links, needed), expr =
    match expr with
    | Fclosure ({ cl_fun; cl_free_var } as closure, d) ->
        (* This can be simplified when free_variables are only variables *)
        let acc = (links, expr_needed) in
        let acc, funs =
          let f = continue current_eid [] in
          VarMap.fold (fun v fun_decl (acc, funs) ->
              let acc, body = f acc fun_decl.free_variables fun_decl.body in
            acc, VarMap.add v { fun_decl with body } funs)
            cl_fun.funs (acc, VarMap.empty)
        in
        let cl_fun = { cl_fun with funs } in
        let acc, cl_free_var =
          let f = continue current_eid inner_loop_stack in
          VarMap.fold (fun v flam (acc, free_vars) ->
              let acc, flam = f acc VarSet.empty flam in
              acc, VarMap.add v flam free_vars)
            cl_free_var (acc, VarMap.empty)
        in
        acc, Fclosure({ closure with cl_fun; cl_free_var }, d)
    | _ ->
        Flambdaiter.fold_subexpressions (continue current_eid inner_loop_stack) (links, expr_needed) expr
  in
  let needed = VarSet.inter needed links.floating_lets in
  let lets_to_add = find_lets_to_add links loop_stack needed in
  add_lets links lets_to_add needed loop_stack expr

and continue parent loop_stack (links,accum_needed) bound expr =
  let loop_stack = match loop_stack with
    | [] -> []
    | h::t -> VarSet.union bound h :: t in
  let (links, needed, expr) = rebuild links expr bound loop_stack in
  let eid = data_at_toplevel_node expr in
  let uses = move_uses_to_parent parent eid links.uses needed in
  ({ links with uses }, VarSet.union accum_needed needed), expr

and add_lets links lets_to_add needed loop_stack expr =
  if VarSet.is_empty lets_to_add
  then links, needed, expr
  else
    let added_let = VarSet.choose lets_to_add in
    let lets_to_add = VarSet.remove added_let lets_to_add in
    let lets =
      try Some (VarMap.find added_let links.lets)
      with Not_found -> None
    in
    match lets with
    | None ->
        (* not a floating let *)
        add_lets links lets_to_add needed loop_stack expr
    | Some { kind; expr = let_def } ->
        let links = { links with lets = VarMap.remove added_let links.lets } in
        let let_eid = nid () in
        let body_eid = data_at_toplevel_node expr in
        let links = { links with uses = remove_use added_let body_eid links.uses } in
        let needed = VarSet.remove added_let needed in
        let uses = move_uses_to_parent let_eid body_eid links.uses needed in
        let links = { links with uses } in
        let (links, needed), let_def = continue let_eid loop_stack (links, needed) VarSet.empty let_def in
        let expr = Flet(kind, added_let, let_def, expr, let_eid) in
        let lets_to_add = find_lets_to_add links loop_stack needed in
        add_lets links lets_to_add needed loop_stack expr

let move_lets expr =
  let expr = Flambdaiter.map_data (fun eid -> ExprId.create ?name:(ExprId.name eid) ()) expr in
  let links, expr = prepare expr in
  let links, needed, expr = rebuild links expr VarSet.empty [] in
  if not (VarSet.is_empty needed) || not (VarMap.is_empty links.uses) ||
     not (VarMap.is_empty links.lets)
  then Format.eprintf "%a@." Printflambda.flambda expr;
  if not (VarSet.is_empty needed)
  then Format.printf "not empty needed: %a@." VarSet.print needed;
  assert(VarSet.is_empty needed);
  if not (VarMap.is_empty links.uses)
  then Format.printf "not empty uses: %a@." (VarMap.print (ExprSet.print)) links.uses;
  assert(VarMap.is_empty links.uses);
  if not (VarMap.is_empty links.lets)
  then Format.printf "not empty lets: %a@." VarSet.print (VarMap.keys links.lets);
  assert(VarMap.is_empty links.lets);
  expr

let remove_trivial_lets expr =
  let aux = function
    | Flet(_,v,def,Fvar (v',_),_) when Variable.equal v v' -> def
    | e -> e
  in
  Flambdaiter.map aux expr

open Flambdapasses

let move_lets_pass =
  { name = "move_lets";
    pass = (fun expr _ -> move_lets expr) }

let remove_trivial_lets_pass =
  { name = "remove_trivial_lets";
    pass = (fun expr _ -> remove_trivial_lets expr) }

let () =
  if Clflags.experiments
  then Flambdapasses.register_pass Loop 12 move_lets_pass;
  Flambdapasses.register_pass Loop 13 remove_trivial_lets_pass

let passes = [move_lets_pass; remove_trivial_lets_pass]
