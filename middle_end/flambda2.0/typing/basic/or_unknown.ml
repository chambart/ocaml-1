(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                       Pierre Chambart, OCamlPro                        *)
(*           Mark Shinwell and Leo White, Jane Street Europe              *)
(*                                                                        *)
(*   Copyright 2018 OCamlPro SAS                                          *)
(*   Copyright 2018 Jane Street Group LLC                                 *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

[@@@ocaml.warning "+a-4-30-40-41-42"]

type 'a t =
  | Known of 'a
  | Unknown

let print f ppf t =
  match t with
  | Known contents -> Format.fprintf ppf "@[<hov 1>(Known@ %a)@]" f contents
  | Unknown -> Format.pp_print_string ppf "Unknown"

let compare compare_contents t1 t2 =
  match t1, t2 with
  | Unknown, Unknown -> 0
  | Known contents1, Known contents2 -> compare_contents contents1 contents2
  | Unknown, Known _ -> -1
  | Known _, Unknown -> 1

let equal equal_contents t1 t2 =
  match t1, t2 with
  | Unknown, Unknown -> true
  | Known contents1, Known contents2 -> equal_contents contents1 contents2
  | Unknown, Known _
  | Known _, Unknown -> false

let map t ~f =
  match t with
  (* CR mshinwell: Add [map_sharing], same for [Or_bottom] *)
  | Known contents -> Known (f contents)
  | Unknown -> Unknown

let free_names free_names_contents t =
  match t with
  | Known contents -> free_names_contents contents
  | Unknown -> Name_occurrences.empty

module Lift (I : Identifiable.S) = struct
  type nonrec t = I.t t

  include Identifiable.Make (struct
    type nonrec t = t

    let print ppf t = print I.print ppf t

    let compare t1 t2 = compare I.compare t1 t2

    let equal t1 t2 = equal I.equal t1 t2

    let hash t =
      match t with
      | Unknown -> Hashtbl.hash 0
      | Known i -> Hashtbl.hash (1, I.hash i)

    let output _ _ = Misc.fatal_error "Not yet implemented"
  end)
end
