(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*    Pierre Chambart and Guillaume Bury, OCamlPro                        *)
(*                                                                        *)
(*   Copyright 2021--2021 OCamlPro SAS                                    *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

[@@@ocaml.warning "+a-4-30-40-41-42"]

(* TODO:

 * ajouter à `elt` un champs : name -> code_id
 * on the way down dans les let_expr il faut différencier si on est dans
   une fonction ou pas (ce qui est un critère différent de "à unit toplevel"):
   - si dans une fonction : pas de let_symbols ou de code_id -> assert false
   - si pas dans une fonction: on enregistre la relation symbol -> code_id

 * pour les lifted constants:
   - si dans une fonction: rien à faire
   - si pas dans une fonction: rajouter le relation entre symbols et free_names/code_id
   -> à la fin de l'analyse du corps d'une fonction (après la simplification),
      il faut ajouter les lifted_constants au data_flow
      utiliser les free_names du corps de la fonction (qui ne seront que des symbols),
      pour enregistrer les dépendances de la fonction (i.e. code_id -> symbol)

 * lors de l'analyse du corps d'une fonction, calculer
   le set de code id utilisé par les name vivants/required
 * ce set est passé dans le uacc
 * une fois que le corps d'une fonciton est simplifié,
   ajouter au dacc du toplevel un binding
   new_code_id -> set de code_id utilisés dans la fonction
 * lors de l'analyse au toplevel, calculer en même temps les names
   reachable et les code_ids qui sont 1) reachables, et
   2) mentioné comme antécédant par le code_age_relation "Newer_version_of"
   d'un reachable
 * un code_id est reachable ssi:
   + il est reachable depuis un name reachable
   + il est antécédant d'au moins deux code_id qui sont reachable (dans des branches
     différentes)
 * les code_ids qui ne sont ni 1) ni 2) sont simplement éliminés
 * let code_ids 2) peuvent être "((newer_version_of ()) Deleted)"
 * naturellement les symbols bound à des code_ids unreachable sont supprimés
   parce que pas présents dans le required_names qui sort de l'analyze.



Notes:
 - la code_age relation est accessible dans le typing_env présent dans le dacc

*)

(* Typedefs *)
(* ******** *)

type elt = {
  continuation : Continuation.t;
  params : Variable.t list;
  used_in_handler : Name_occurrences.t;
  apply_result_conts : Continuation.Set.t;
  bindings : Name_occurrences.t Name.Map.t;
  bindings_in_sets_of_closures : Code_id.t Name.Map.t;
  apply_cont_args :
    Name_occurrences.t Numbers.Int.Map.t Continuation.Map.t;
}

type t = {
  stack : elt list;
  map : elt Continuation.Map.t;
  extra : Continuation_extra_params_and_args.t Continuation.Map.t;
}

(* Print *)
(* ***** *)

let print_elt ppf
      { continuation; params; used_in_handler;
        apply_result_conts; bindings; bindings_in_sets_of_closures;
        apply_cont_args; } =
  Format.fprintf ppf
    "@[<hov 1>(\
      @[<hov 1>(continuation %a)@]@ \
      @[<hov 1>(params %a)@]@ \
      @[<hov 1>(used_in_handler %a)@]@ \
      @[<hov 1>(apply_result_conts %a)@]@ \
      @[<hov 1>(bindings %a)@]@ \
      @[<hov 1>(bindings_in_socs %a)@]@ \
      @[<hov 1>(apply_cont_args %a)@]\
      )@]"
    Continuation.print continuation
    Variable.print_list params
    Name_occurrences.print used_in_handler
    Continuation.Set.print apply_result_conts
    (Name.Map.print Name_occurrences.print) bindings
    (Name.Map.print Code_id.print) bindings_in_sets_of_closures
    (Continuation.Map.print (Numbers.Int.Map.print Name_occurrences.print))
    apply_cont_args

let print_stack ppf stack =
  Format.fprintf ppf "@[<v 1>(%a)@]"
    (Format.pp_print_list print_elt ~pp_sep:Format.pp_print_space)
    stack

let print_map ppf map =
  Continuation.Map.print print_elt ppf map

let print_extra ppf extra =
  Continuation.Map.print Continuation_extra_params_and_args.print ppf extra

let print ppf { stack; map; extra } =
  Format.fprintf ppf
    "@[<hov 1>(\
      @[<hov 1>(stack %a)@]@ \
      @[<hov 1>(map %a)@]@ \
      @[<hov 1>(extra %a)@]\
      )@]"
    print_stack stack
    print_map map
    print_extra extra

(* Creation *)
(* ******** *)

let empty = {
  stack = [];
  map = Continuation.Map.empty;
  extra = Continuation.Map.empty;
}

(* Updates *)
(* ******* *)

let add_extra_params_and_args cont extra t =
  let extra =
    Continuation.Map.update cont (function
      | Some _ ->
        Misc.fatal_errorf "Continuation extended a second time"
      | None -> Some extra
    ) t.extra
  in
  { t with extra; }

let enter_continuation continuation params t =
  let elt = {
    continuation; params;
    bindings = Name.Map.empty;
    bindings_in_sets_of_closures = Name.Map.empty;
    used_in_handler = Name_occurrences.empty;
    apply_cont_args = Continuation.Map.empty;
    apply_result_conts = Continuation.Set.empty;
  }
  in
  { t with stack = elt :: t.stack; }

let init_toplevel continuation params _t =
  enter_continuation continuation params empty

let exit_continuation cont t =
  match t.stack with
  | [] -> Misc.fatal_errorf "Empty stack of variable uses"
  | ({ continuation; _ } as elt) :: stack ->
    assert (Continuation.equal cont continuation);
    let map = Continuation.Map.add cont elt t.map in
    { t with stack; map; }

let update_top_of_stack ~t ~f =
  match t.stack with
  | [] -> Misc.fatal_errorf "Empty stack of variable uses"
  | elt :: stack -> { t with stack = f elt :: stack; }

let record_var_binding var name_occurrences ~generate_phantom_lets t =
  update_top_of_stack ~t ~f:(fun elt ->
    let bindings =
      Name.Map.update (Name.var var) (function
        | None -> Some name_occurrences
        | Some _ ->
            Misc.fatal_errorf
              "The following variable has been bound twice: %a"
              Variable.print var
      ) elt.bindings
    in
    let used_in_handler =
      if Variable.user_visible var && generate_phantom_lets then
        Name_occurrences.add_variable elt.used_in_handler var Name_mode.phantom
      else
        elt.used_in_handler
    in
    { elt with bindings; used_in_handler; }
  )

let record_set_of_closures_binding names closure_id_lmap t =
  update_top_of_stack ~t ~f:(fun elt ->
    let bindings_in_sets_of_closures =
      List.fold_left2 (fun bindings_in_sets_of_closures name (_, fundecl)->
        let code_id = Function_declaration.code_id fundecl in
        Name.Map.update name (function
          | None -> Some code_id
          | Some _ ->
            Misc.fatal_errorf
              "The following name has been bound twice: %a"
              Name.print name
        ) bindings_in_sets_of_closures
      ) elt.bindings_in_sets_of_closures
        names (Closure_id.Lmap.bindings closure_id_lmap)
    in
    { elt with bindings_in_sets_of_closures; }
  )

let add_used_in_current_handler name_occurrences t =
  update_top_of_stack ~t ~f:(fun elt ->
    let used_in_handler =
      Name_occurrences.union elt.used_in_handler name_occurrences
    in
    { elt with used_in_handler; }
  )

let add_apply_result_cont k t =
  update_top_of_stack ~t ~f:(fun elt ->
    let apply_result_conts = Continuation.Set.add k elt.apply_result_conts in
    { elt with apply_result_conts; }
  )

let add_apply_cont_args cont arg_name_occurrences t =
  update_top_of_stack ~t ~f:(fun elt ->
    let apply_cont_args =
      Continuation.Map.update cont (fun map_opt ->
        let map = Option.value ~default:Numbers.Int.Map.empty map_opt in
        let map, _ = List.fold_left (fun (map, i) name_occurrences ->
          let map =
            Numbers.Int.Map.update i (fun old_opt ->
              let old = Option.value ~default:Name_occurrences.empty old_opt in
              Some (Name_occurrences.union old name_occurrences)
            ) map
          in
          map, i + 1
          ) (map, 0) arg_name_occurrences
        in
        Some map
      ) elt.apply_cont_args
    in
    { elt with apply_cont_args; }
  )

(* Name graph *)
(* ********** *)

module Name_graph = struct

  type t = Name.Set.t Name.Map.t

  let print ppf t =
    Name.Map.print Name.Set.print ppf t

  let empty : t = Name.Map.empty

  let add_edge ~src ~dst t =
    Name.Map.update src (function
      | None -> Some (Name.Set.singleton dst)
      | Some set -> Some (Name.Set.add dst set)
    ) t

  let edges ~src t =
    match Name.Map.find src t with
    | res -> res
    | exception Not_found -> Name.Set.empty

  (* breadth-first reachability analysis. *)
  let rec reachable code_id_deps t live_code_ids enqueued queue =
    match Queue.take queue with
    | exception Queue.Empty -> enqueued, live_code_ids
    | v ->
      let live_code_ids =
        match Name.Map.find v code_id_deps with
        | exception Not_found -> live_code_ids
        | code_id -> Code_id.Set.add code_id live_code_ids
      in
      let neighbours = edges t ~src:v in
      let new_neighbours = Name.Set.diff neighbours enqueued in
      Name.Set.iter (fun dst -> Queue.push dst queue) new_neighbours;
      reachable
        code_id_deps t live_code_ids
        (Name.Set.union enqueued new_neighbours) queue

end

(* Dependency graph *)
(* **************** *)

module Dependency_graph = struct

  type t = {
    dependencies : Name_graph.t;
    code_id_deps : Code_id.t Name.Map.t;
    unconditionally_used : Name.Set.t;
  }

  let empty = {
    dependencies = Name_graph.empty;
    code_id_deps = Name.Map.empty;
    unconditionally_used = Name.Set.empty;
  }

  let _print ppf { dependencies; code_id_deps; unconditionally_used; } =
    Format.fprintf ppf "@[<hov 1>(\
        @[<hov 1>(dependencies@ %a)@]@ \
        @[<hov 1>(code_id_deps@ %a)@]@ \
        @[<hov 1>(unconditionally_used@ %a)@]\
        )@]"
      Name_graph.print dependencies
      (Name.Map.print Code_id.print) code_id_deps
      Name.Set.print unconditionally_used

  (* Some auxiliary functions *)
  let add_code_id_dep ~src ~dst ({ code_id_deps; _ } as t) =
    let code_id_deps = Name.Map.update src (function
      | None -> Some dst
      | Some _ -> Misc.fatal_errorf "Same name bound multiple times"
    ) code_id_deps
    in
    { t with code_id_deps; }

  let add_dependency ~src ~dst ({ dependencies; _ } as t) =
    let dependencies = Name_graph.add_edge ~src ~dst dependencies in
    { t with dependencies; }

  let add_name_used ({ unconditionally_used; _ } as t) v =
    let unconditionally_used =  Name.Set.add v unconditionally_used in
    { t with unconditionally_used; }

  let add_var_used t v = add_name_used t (Name.var v)

  let add_name_occurrences name_occurrences
        ({ unconditionally_used = init; _ } as t) =
    let unconditionally_used =
      Name_occurrences.fold_names name_occurrences ~init
        ~f:(fun set name -> Name.Set.add name set)
    in
    { t with unconditionally_used; }

  let add_continuation_info map ~return_continuation ~exn_continuation
        _ { apply_cont_args; apply_result_conts; used_in_handler; bindings;
            bindings_in_sets_of_closures; continuation = _; params = _; } t =
    (* Add the vars used in the handler *)
    let t = add_name_occurrences used_in_handler t in
    (* Add the vars of continuation used as function call return as used *)
    let t =
      Continuation.Set.fold (fun k t ->
        match Continuation.Map.find k map with
        | elt -> List.fold_left add_var_used t elt.params
        | exception Not_found ->
          if Continuation.equal return_continuation k ||
             Continuation.equal exn_continuation k
          then t
          else
            Misc.fatal_errorf "Continuation not found during Data_flow: %a@."
              Continuation.print k
      ) apply_result_conts t
    in
    (* Build the graph of dependencies between names *)
    let t =
      Name.Map.fold (fun src name_occurrences graph ->
        Name_occurrences.fold_names name_occurrences ~init:graph
          ~f:(fun t dst -> add_dependency ~src ~dst t)
      ) bindings t
    in
    (* Build the graph of dependencies between names and sets of closures*)
    let t =
      Name.Map.fold (fun src code_id graph ->
        add_code_id_dep ~src ~dst:code_id graph
      ) bindings_in_sets_of_closures t
    in
    (* Build the graph of dependencies between continuation
       parameters and arguments. *)
    Continuation.Map.fold (fun k args t ->
      if Continuation.equal return_continuation k ||
         Continuation.equal exn_continuation k then begin
        Numbers.Int.Map.fold (fun _ name_occurrences t ->
          add_name_occurrences name_occurrences t
        ) args t
      end else begin
        let params =
          match Continuation.Map.find k map with
          | elt -> Array.of_list elt.params
          | exception Not_found ->
            Misc.fatal_errorf "Continuation not found during Data_flow: %a@."
              Continuation.print k
        in
        Numbers.Int.Map.fold (fun i name_occurrence t ->
          (* Note on the direction of the edge:
             We later do a reachability analysis to compute the
             transitive closure of the used variables.
             Therefore an edge from src to dst means: if src is used, then
             dst is also used.
             Applied here, this means : if the param of a continuation is used,
             then any argument provided for that param is also used.
             The other way wouldn't make much sense. *)
          let src = Name.var params.(i) in
          Name_occurrences.fold_names name_occurrence ~init:t
            ~f:(fun t dst -> add_dependency ~src ~dst t)
        ) args t
      end
    ) apply_cont_args t

  let create ~return_continuation ~exn_continuation map extra =
    (* Build the dependencies using the regular params and args of
       continuations, and the let-bindings in continuations handlers. *)
    let t =
      Continuation.Map.fold
        (add_continuation_info map
        ~return_continuation ~exn_continuation)
        map empty
    in
    (* Take into account the extra params and args. *)
    let t =
      Continuation.Map.fold (
        fun _ (extra_params_and_args : Continuation_extra_params_and_args.t) t
        ->
          Apply_cont_rewrite_id.Map.fold (fun _ extra_args t ->
            List.fold_left2 (fun t extra_param extra_arg ->
              let src = Name.var (Kinded_parameter.var extra_param) in
              match
                (extra_arg : Continuation_extra_params_and_args.Extra_arg.t)
              with
              | Already_in_scope simple ->
                Name_occurrences.fold_names (Simple.free_names simple)
                  ~init:t
                  ~f:(fun t dst -> add_dependency ~src ~dst t)
              | New_let_binding (src', prim) ->
                let src' = Name.var src' in
                Name_occurrences.fold_names
                  (Flambda_primitive.free_names prim)
                  ~f:(fun t dst -> add_dependency ~src:src' ~dst t)
                  ~init:(add_dependency ~src ~dst:src' t)
              | New_let_binding_with_named_args (_src', _prim_gen) ->
                (* In this case, the free_vars present in the result of
                   _prim_gen are fresh (and a subset of the simples given to
                   _prim_gen) and generated when going up while creating a
                   wrapper continuation for the return of a function
                   application.
                   In that case, the fresh parameters created for the wrapper
                   cannot introduce dependencies to other variables or
                   parameters of continuations.
                   Therefore, in this case, the data_flow analysis is
                   incomplete, and we instead rely on the free_names analysis
                   to eliminate the extra_let binding if it is unneeded. *)
                t
            ) t extra_params_and_args.extra_params extra_args
          ) extra_params_and_args.extra_args t
      ) extra t
    in
    t

  let required_names { dependencies; code_id_deps; unconditionally_used; } =
    let queue = Queue.create () in
    Name.Set.iter (fun v -> Queue.push v queue) unconditionally_used;
    Name_graph.reachable
      code_id_deps dependencies
      Code_id.Set.empty unconditionally_used queue

end

(* Analysis *)
(* ******** *)

type result = {
  required_names : Name.Set.t;
  live_code_ids : Code_id.Set.t;
}

let analyze ~return_continuation ~exn_continuation { stack; map; extra; } =
  Profile.record_call ~accumulate:true "data_flow" (fun () ->
    assert (stack = []);
    let deps =
      Dependency_graph.create ~return_continuation ~exn_continuation map extra
    in
    let required_names, live_code_ids = Dependency_graph.required_names deps in
    { required_names; live_code_ids; })

