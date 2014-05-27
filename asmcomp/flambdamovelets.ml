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
    - remove every pure variable declarations from the expression:
      implemented in the 'prepare' function
    - reinsert the declarations at the 'right' position:
      implemented in the 'rebuild' function

    The 'right' position is as deep as possible in the tree such that it is:
    - at a correct position:
      * higher than every usage of the variable.
      * below than every referenced variable in the definition
    - higher than as much loop as possible

    The reinsertion is done by traversing the tree bottom up, adding a declaration when
    - every use (accounting for not yet reinserted declarations) is below the current point
    - and the current point is not in a loop or the variable is not constant for the current loop

    Note: in this file pure variable declarations are called floating lets.

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

(* O(n.log(n)) with n the sum of the sizes of expressions *)
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
                  (* complexity assumes that building an union of size n iteratively is of cost n.log(n)*)
                  VarSet.union set (VarMap.find id lets_dep))
                VarSet.empty ids in
        VarSet.diff deps floating_vars)
      components in
  components, component_deps

(* Build a map containing the transitive closure of variable dependencies.
   O(n.log(n)) with n the sum of the sizes of expressions *)
let lets_dep lets =
  let components, component_deps =
    variables_connected_components lets in

  let let_deps = ref VarMap.empty in
  (* Components are sorted in reverse topological order:
     components.(length - 1) has no dependencies
     nothing depends on components.(0).

     This means that when going from (length-1) to 0 all dependencies
     of components.(k) are handled when i = k *)
  for i = Array.length components - 1 downto 0 do
    let comp, deps = components.(i) in
    let var_deps =
      (* complexity assumes that building an union of size n iteratively is of cost n.log(n)*)
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

(*>>>>>>*)

module Multiset : sig
  type t
  val empty : t
  val cardinal : Variable.t -> t -> int
  val add : Variable.t -> int -> t -> t
  val union : t -> t -> t
  (** [union m1 m2] O((min |m1| |m2|).log(max |m1| |m2|)) *)
  val remove : Variable.t -> t -> t
  (** [t' = remove v t] is the multiset where
      For each v' <> v, [cardinal v' t = cardinal v' t']
      and [cardinal v t' = 0] *)
  val set : t -> VarSet.t
  (** O(n) *)
  val of_set : VarSet.t -> t
  (** O(n) *)
  val of_intmap : int VarMap.t -> t
  val union_check : check_level:t -> t -> t -> t * VarSet.t
  (** [(r,s) = union_check ~check_level m1 m2]
      r is the union of m1 and m2.
      for each v such that
      [cardinal v m1 > 0] and [cardinal v m2 > 0]
      if [cardinal v m1 + cardinal v m2 >= cardinal v check_level]
      then v is in s

      O((min |m1| |m2|).log(max |m1| |m2|))
  *)
  val equal : t -> t -> bool

  val print : Format.formatter -> t -> unit

end = struct

  type t =
    { count : int VarMap.t;
      cardinal : int;
      (* The cardinal of the map, for O(1) access.
         Needed for a reasonable union complexity *)
    }

  let empty = { count = VarMap.empty; cardinal = 0 }

  let cardinal v c =
    try VarMap.find v c.count
    with Not_found -> 0

  let add v n c =
    try
      let m = VarMap.find v c.count in
      { c with count = VarMap.add v (m+n) c.count }
    with Not_found ->
      { count = VarMap.add v n c.count;
        cardinal = c.cardinal + 1 }

  (* O((min |m1| |m2|).log(max |m1| |m2|)) *)
  let union c1 c2 =
    let min_c, max_c =
      if c1.cardinal < c2.cardinal
      then c1, c2
      else c2, c1 in
    VarMap.fold add min_c.count max_c

  let union_check ~check_level c1 c2 =
    let min_c, max_c =
      if c1.cardinal < c2.cardinal
      then c1, c2
      else c2, c1 in
    let aux v n (c,s) =
      try
        let m = VarMap.find v c.count in
        let s =
          if m + n >= cardinal v check_level
          then VarSet.add v s
          else s in
        { c with count = VarMap.add v (m+n) c.count }, s
      with Not_found ->
        { count = VarMap.add v n c.count;
          cardinal = c.cardinal + 1 }, s
    in
    VarMap.fold aux min_c.count (max_c, VarSet.empty)

  let remove v c =
    if VarMap.mem v c.count
    then
      { count = VarMap.remove v c.count;
        cardinal = c.cardinal - 1 }
    else c

  let equal v1 v2 =
    v1.cardinal = v2.cardinal &&
    VarMap.equal (fun (x:int) y -> x = y) v1.count v2.count

  let set c = VarMap.keys c.count

  let of_set s = VarSet.fold (fun v acc -> add v 1 acc) s empty

  let of_intmap m =
    let count = VarMap.filter
        (fun _ i ->
           assert(i >= 0);
           i > 0)
        m in
    { count; cardinal = VarMap.cardinal count }

  let print ppf c = VarMap.print Format.pp_print_int ppf c.count

end

module Tmp = struct

  let count_uses expr lets =
    let count = ref VarMap.empty in
    let add_node expr =
      let fv = Flambdaiter.expression_free_variables expr in
      let add_use v count =
        if VarMap.mem v lets (* only count floating lets *)
        then
          let c =
            try VarMap.find v count
            with Not_found -> 0 in
          VarMap.add v (c+1) count
        else count
      in
      count := VarSet.fold add_use fv !count
    in
    Flambdaiter.iter add_node expr;
    VarMap.iter (fun _ { expr } -> Flambdaiter.iter add_node expr) lets;
    Multiset.of_intmap !count

  type links =
    { uses : Multiset.t;
      lets : lets VarMap.t;
      lets_dep : VarSet.t VarMap.t;
      floating_lets : VarSet.t }

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
    let uses = count_uses expr lets in
    let links =
      { uses; lets;
        lets_dep = lets_dep lets;
        floating_lets = VarMap.keys lets } in
    links, expr

  type rebuild_state =
    { used_var : Multiset.t;
      waitings : VarSet.t;
      (* Variables waiting for a loop construct to be inserted *)
      needed : VarSet.t
      (* Variables that can be inserted at that point *) }

  let empty_state =
    { used_var = Multiset.empty;
      waitings = VarSet.empty;
      needed = VarSet.empty }

  type loop_stack =
    | Toplevel
    | Inside_loop of VarSet.t

  (** If the variable does not depend on anything fixed by the current
      loop, the variable is a constant for this loop and should be
      moved higher. *)
  let waiting_variable links loop_stack_vars v =
    let var_deps = VarMap.find v links.lets_dep in
    VarSet.is_empty (VarSet.inter loop_stack_vars var_deps)

  let split_needed links loop_stack set =
    match loop_stack with
    | Toplevel -> VarSet.empty, set
    | Inside_loop loop_stack_vars ->
        let waitings, needed =
          VarSet.partition (waiting_variable links loop_stack_vars) set in
          (* Format.printf "set: %a needed: %a waitings: %a loop_stack: %a@." *)
          (*   VarSet.print set *)
          (*   VarSet.print needed *)
          (*   VarSet.print waitings *)
          (*   VarSet.print loop_stack_vars; *)
        waitings, needed

  let state_union links (loop_stack:loop_stack) s1 s2 =
    let used_var, new_needed =
      Multiset.union_check ~check_level:links.uses s1.used_var s2.used_var in
    let waitings = VarSet.union s1.waitings s2.waitings in
    let needed = VarSet.union s1.needed s2.needed in
    let new_waitings, new_needed = split_needed links loop_stack new_needed in
    let waitings = VarSet.union waitings new_waitings in
    let needed = VarSet.union new_needed needed in
    { used_var; waitings; needed }

  let is_loop = function
    | Fwhile _
    | Ffor _ -> true
    | _ -> false

  (* list variables that appear only once in the tree,
     and precisely at this expression
     O(|set|.log(|set|)) *)
  let directly_needed links set =
    let uses = links.uses in
    let aux v acc =
      if Multiset.cardinal v uses = 1
      then VarSet.add v acc
      else acc in
    VarSet.fold aux set VarSet.empty

  (* O(|lets_dep(waitings)| + |waitings|.log(|needed| + |waitings|))
     where |lets_dep(waitings)| is the sum of the size of dependencies
     of the variables of waitings.
     |lets_dep(waitings)| is bounded by the size of the program *)
  let transfer_waitings links loop_stack state =
    let waitings, new_needed = split_needed links loop_stack state.waitings in
    let needed = VarSet.union state.needed new_needed in
    { state with needed; waitings }

  (* O(loop_nesting . |links.floating_lets| . log(|links.floating_lets|)) *)
  let rec rebuild links expr (loop_stack:loop_stack) : rebuild_state * 'a flambda =
    let expr_needed =
      VarSet.inter
        (Flambdaiter.expression_free_variables expr)
        links.floating_lets in
    let inner_loop_stack =
      if is_loop expr
      then Inside_loop VarSet.empty
      else loop_stack
    in
    let waitings, needed =
      split_needed links loop_stack (directly_needed links expr_needed)
    in
    let state =
      { used_var = Multiset.of_set expr_needed;
        waitings;
        needed } in
    let state, expr =
      match expr with
      | Fclosure ({ cl_fun; cl_free_var } as closure, d) ->
          (* This can be simplified when free_variables are only variables *)
          let used_var, funs =
            VarMap.fold (fun v fun_decl (used_var, funs) ->
                let state, body = rebuild links fun_decl.body Toplevel in
                assert(VarSet.is_empty state.waitings);
                assert(VarSet.is_empty state.needed);
                (* only pleasing the asserts *)
                Multiset.union used_var state.used_var,
                VarMap.add v { fun_decl with body } funs)
              cl_fun.funs (state.used_var, VarMap.empty)
          in
          let state = { state with used_var } in
          let cl_fun = { cl_fun with funs } in
          let state, cl_free_var =
            VarMap.fold (fun v flam (state, free_vars) ->
                let acc, flam = rebuild links flam inner_loop_stack in
                state, VarMap.add v flam free_vars)
              cl_free_var (state, VarMap.empty)
          in
          state, Fclosure({ closure with cl_fun; cl_free_var }, d)
      | _ ->
          Flambdaiter.fold_subexpressions (continue links inner_loop_stack) state expr
    in
    (* Format.printf "rebuild1 waitings %a needed %a@." *)
    (*   VarSet.print state.waitings *)
    (*   VarSet.print state.needed; *)

    (* Should do it only at loop expressions !
       It will be empty (?) everywhere else (and change the complexity) *)

    (* let state = transfer_waitings links loop_stack state in *)
    let state =
      if is_loop expr
      then transfer_waitings links loop_stack state
      else state in

    (* Format.printf "rebuild2 waitings %a needed %a@." *)
    (*   VarSet.print state.waitings *)
    (*   VarSet.print state.needed; *)
    add_lets links state loop_stack expr

  and continue links loop_stack acc_state bound expr =
    let loop_stack =
      match loop_stack with
      | Toplevel -> Toplevel
      | Inside_loop set -> Inside_loop (VarSet.union bound set) in
    let expr_state, expr = rebuild links expr loop_stack in
    let state = state_union links loop_stack expr_state acc_state in
    state, expr

  and add_lets links state loop_stack expr =
    if VarSet.is_empty state.needed
    then state, expr
    else
      let added_let = VarSet.choose state.needed in
      (* Format.printf "add let: %a waitings %a needed %a@." *)
      (*   Variable.print added_let *)
      (*   VarSet.print state.waitings *)
      (*   VarSet.print state.needed; *)
      let needed = VarSet.remove added_let state.needed in
      let state = { state with needed } in
      let { kind; expr = let_def } =
        try VarMap.find added_let links.lets
        with Not_found -> assert false in
      let let_state, let_def = rebuild links let_def loop_stack in
      let expr = Flet(kind, added_let, let_def, expr, nid ()) in
      let state = state_union links loop_stack let_state state in
      add_lets links state loop_stack expr

  let move_lets expr =
    let links, expr = prepare expr in
    let state, expr = rebuild links expr Toplevel in
    if not (VarSet.is_empty state.needed) || not (VarSet.is_empty state.waitings) ||
       not (Multiset.equal links.uses state.used_var)
    then begin
      Format.eprintf "%a@." Printflambda.flambda expr;
      if not (VarSet.is_empty state.needed)
      then Format.printf "not empty needed: %a@." VarSet.print state.needed;
      if not (VarSet.is_empty state.waitings)
      then Format.printf "not empty waitings: %a@." VarSet.print state.waitings;
      if not (Multiset.equal links.uses state.used_var)
      then Format.printf "not equal multisets @ uses:@ %a@ used_var@ %a@."
          Multiset.print links.uses Multiset.print state.used_var;
      assert false
    end;
    expr

end

(*<<<<<<*)


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

let move_lets = Tmp.move_lets

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
