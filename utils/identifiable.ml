(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                       Pierre Chambart, OCamlPro                        *)
(*           Mark Shinwell and Leo White, Jane Street Europe              *)
(*                                                                        *)
(*   Copyright 2013--2016 OCamlPro SAS                                    *)
(*   Copyright 2014--2016 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

module Stdlib_map = Map
module Stdlib_set = Set

module type Thing = sig
  type t

  include Hashtbl.HashedType with type t := t
  include Map.OrderedType with type t := t

  val output : out_channel -> t -> unit
  val print : Format.formatter -> t -> unit
end

module Pair (A : Thing) (B : Thing) : Thing with type t = A.t * B.t = struct
  type t = A.t * B.t

  let compare (a1, b1) (a2, b2) =
    let c = A.compare a1 a2 in
    if c <> 0 then c
    else B.compare b1 b2

  let output oc (a, b) = Printf.fprintf oc " (%a, %a)" A.output a B.output b
  let hash (a, b) = Hashtbl.hash (A.hash a, B.hash b)
  let equal (a1, b1) (a2, b2) = A.equal a1 a2 && B.equal b1 b2
  let print ppf (a, b) = Format.fprintf ppf " (%a, @ %a)" A.print a B.print b
end

module Make_map (T : Thing) = struct
  include Map.Make (T)

  let filter_map t ~f =
    fold (fun id v map ->
        match f id v with
        | None -> map
        | Some r -> add id r map) t empty

  let of_list l =
    List.fold_left (fun map (id, v) -> add id v map) empty l

  let disjoint_union ?eq m1 m2 =
    union (fun id v1 v2 ->
        let ok = match eq with
          | None -> false
          | Some eq -> eq v1 v2
        in
        if not ok then
          let err = Format.asprintf "Map.disjoint_union %a" T.print id in
          Misc.fatal_error err
        else Some v1)
      m1 m2

  let union_right m1 m2 =
    merge (fun _id x y -> match x, y with
        | None, None -> None
        | None, Some v
        | Some v, None
        | Some _, Some v -> Some v)
      m1 m2

  let union_left m1 m2 = union_right m2 m1

  let union_merge f m1 m2 =
    let aux _ m1 m2 =
      match m1, m2 with
      | None, m | m, None -> m
      | Some m1, Some m2 -> Some (f m1 m2)
    in
    merge aux m1 m2

  let rename m v =
    try find v m
    with Not_found -> v

  let map_keys f m =
    of_list (List.map (fun (k, v) -> f k, v) (bindings m))

  let print f ppf s =
    let elts ppf s = iter (fun id v ->
        Format.fprintf ppf "@ (@[%a@ %a@])" T.print id f v) s in
    Format.fprintf ppf "@[<1>{@[%a@ @]}@]" elts s

  module T_set = Set.Make (T)

  let keys map = fold (fun k _ set -> T_set.add k set) map T_set.empty

  let data t = List.map snd (bindings t)

  let of_set f set = T_set.fold (fun e map -> add e (f e) map) set empty

  let transpose_keys_and_data map = fold (fun k v m -> add v k m) map empty

  let get_singleton s =
    (* CR pchambart: this should be done more efficiently, but
       this is probably the best we can do currently with the interface
       of map (It might be simplifiable through unrolling with CPS) *)
    try
      fold (fun k s acc ->
          match acc with
          | None -> Some (k, s)
          | Some _ -> raise Exit)
        s None
    with Exit -> None
end

module Make_set (T : Thing) = struct
  include Set.Make (T)

  let output oc s =
    Printf.fprintf oc " ( ";
    iter (fun v -> Printf.fprintf oc "%a " T.output v) s;
    Printf.fprintf oc ")"

  let print ppf s =
    let elts ppf s = iter (fun e -> Format.fprintf ppf "@ %a" T.print e) s in
    Format.fprintf ppf "@[<1>{@[%a@ @]}@]" elts s

  let to_string s = Format.asprintf "%a" print s

  let of_list l = match l with
    | [] -> empty
    | [t] -> singleton t
    | t :: q -> List.fold_left (fun acc e -> add e acc) (singleton t) q

  let map f s = of_list (List.map f (elements s))

  let filter_map t ~f = of_list (Misc.Stdlib.List.filter_map f (elements t))

  let get_singleton s =
    (* CR pchambart: this should be done more efficiently, but
       this is probably the best we can do currently with the interface
       of set *)
    try
      fold (fun s acc ->
          match acc with
          | None -> Some s
          | Some _ -> raise Exit)
        s None
    with Exit -> None
end

module Make_tbl (T : Thing) = struct
  include Hashtbl.Make (T)

  module T_map = Make_map (T)

  let to_list t =
    fold (fun key datum elts -> (key, datum)::elts) t []

  let of_list elts =
    let t = create 42 in
    List.iter (fun (key, datum) -> add t key datum) elts;
    t

  let to_map v = fold T_map.add v T_map.empty

  let of_map m =
    let t = create (T_map.cardinal m) in
    T_map.iter (fun k v -> add t k v) m;
    t

  let memoize t f = fun key ->
    try find t key with
    | Not_found ->
      let r = f key in
      add t key r;
      r

  let map t f =
    of_map (T_map.map f (to_map t))
end

module type S = sig
  type t

  module T : Thing with type t = t
  include Thing with type t := T.t

  module Set : sig
    include Stdlib_set.S
      with type elt = T.t
      and type t = Make_set (T).t

    val output : out_channel -> t -> unit
    val print : Format.formatter -> t -> unit
    val to_string : t -> string
    val of_list : elt list -> t
    val map : (elt -> elt) -> t -> t
    val filter_map : t -> f:(elt -> elt option) -> t
    val get_singleton : t -> elt option
  end

  module Map : sig
    include Stdlib_map.S
      with type key = T.t
      and type 'a t = 'a Make_map (T).t

    val filter_map : 'a t -> f:(key -> 'a -> 'b option) -> 'b t
    val of_list : (key * 'a) list -> 'a t
    val disjoint_union : ?eq:('a -> 'a -> bool) -> 'a t -> 'a t -> 'a t
    val union_right : 'a t -> 'a t -> 'a t
    val union_left : 'a t -> 'a t -> 'a t
    val union_merge : ('a -> 'a -> 'a) -> 'a t -> 'a t -> 'a t
    val rename : key t -> key -> key
    val map_keys : (key -> key) -> 'a t -> 'a t
    val keys : 'a t -> Make_set (T).t
    val data : 'a t -> 'a list
    val of_set : (key -> 'a) -> Make_set (T).t -> 'a t
    val transpose_keys_and_data : key t -> key t
    val get_singleton : 'a t -> (key * 'a) option
    val print :
      (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a t -> unit
  end

  module Tbl : sig
    include Hashtbl.S
      with type key = T.t
      and type 'a t = 'a Hashtbl.Make (T).t

    val to_list : 'a t -> (T.t * 'a) list
    val of_list : (T.t * 'a) list -> 'a t

    val to_map : 'a t -> 'a Make_map (T).t
    val of_map : 'a Make_map (T).t -> 'a t
    val memoize : 'a t -> (key -> 'a) -> key -> 'a
    val map : 'a t -> ('a -> 'b) -> 'b t
  end
end

module Make (T : Thing) = struct
  module T = T
  include T

  module Set = Make_set (T)
  module Map = Make_map (T)
  module Tbl = Make_tbl (T)
end
