open Ext_types

module Kosaraju : sig
  val sorted_connected_components : int list array -> int list array
end = struct

  let transpose graph =
    let size = Array.length graph in
    let transposed = Array.create size [] in
    let add src dst = transposed.(src) <- dst :: transposed.(src) in
    Array.iteri (fun src dsts -> List.iter (fun dst -> add dst src) dsts) graph;
    transposed

  let depth_first_order graph =
    let size = Array.length graph in
    let marked = Array.create size false in
    let stack = Array.create size ~-1 in
    let pos = ref 0 in
    let push i =
      stack.(!pos) <- i;
      incr pos
    in
    let rec aux node =
      if not marked.(node)
      then begin
        marked.(node) <- true;
        List.iter aux graph.(node);
        push node
      end
    in
    for i = 0 to size - 1 do
      aux i
    done;
    stack

  let mark order graph =
    let size = Array.length graph in
    let graph = transpose graph in

    let marked = Array.create size false in
    let id = Array.create size ~-1 in
    let count = ref 0 in

    let rec aux node =
      if not marked.(node)
      then begin
        marked.(node) <- true;
        id.(node) <- !count;
        List.iter aux graph.(node)
      end
    in

    for i = size - 1 downto 0 do
      let node = order.(i) in
      if not marked.(node)
      then begin
        aux order.(i);
        incr count
      end
    done;
    id, !count

  let kosaraju graph =
    let dfo = depth_first_order graph in
    let components, ncomponents = mark dfo graph in
    ncomponents, components

  let sorted_connected_components graph =
    let ncomponents, components = kosaraju graph in
    let id_scc = Array.create ncomponents [] in
    Array.iteri (fun node component ->
        id_scc.(component) <- node :: id_scc.(component))
      components;
    id_scc

end

module type S = sig
  module Id : PrintableHashOrdered
  type directed_graph = ExtSet(Id).t ExtMap(Id).t
  type component =
    | Has_loop of Id.t list
    | No_loop of Id.t
  val connected_components_sorted_from_roots_to_leaf :
    directed_graph -> component array
end

module Make(Id:PrintableHashOrdered) = struct
  module IdSet = ExtSet(Id)
  module IdMap = ExtMap(Id)

  type directed_graph = ExtSet(Id).t ExtMap(Id).t
  type component =
    | Has_loop of Id.t list
    | No_loop of Id.t

  (* ensure that the dependency graph does not have external dependencies *)
  let check dependencies =
    IdMap.iter (fun id set ->
        IdSet.iter (fun v ->
            if not (IdMap.mem v dependencies)
            then
              Misc.fatal_error
                (Format.asprintf "Flambdasort.check: the graph has external \
                                  dependencies (%a -> %a)"
                   Id.print id Id.print v))
          set)
      dependencies

  type numbering =
    { back : int IdMap.t;
      forth : Id.t array }

  let number graph =
    let size = IdMap.cardinal graph in
    let bindings = IdMap.bindings graph in
    let a = Array.of_list bindings in
    let forth = Array.map fst a in
    let back =
      let back = ref IdMap.empty in
      for i = 0 to size - 1 do
        back := IdMap.add forth.(i) i !back;
      done;
      !back in
    let integer_graph = Array.init size (fun i ->
        let _, dests = a.(i) in
        IdSet.fold (fun dest acc -> (IdMap.find dest back) :: acc) dests []) in
    { back; forth }, integer_graph

  let connected_components_sorted_from_roots_to_leaf graph =
    let numbering, integer_graph = number graph in
    let components = Kosaraju.sorted_connected_components integer_graph in
    Array.map (fun nodes ->
        match nodes with
        | [] -> assert false
        | [node] ->
            if List.mem node integer_graph.(node)
            then Has_loop [numbering.forth.(node)]
            else No_loop numbering.forth.(node)
        | _::_ ->
            Has_loop (List.map (fun node -> numbering.forth.(node)) nodes))
      components

end
