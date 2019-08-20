(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                       Pierre Chambart, OCamlPro                        *)
(*           Mark Shinwell and Leo White, Jane Street Europe              *)
(*                                                                        *)
(*   Copyright 2013--2019 OCamlPro SAS                                    *)
(*   Copyright 2014--2019 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

[@@@ocaml.warning "+a-4-30-40-41-42"]

include
  Row_like.Make (Closure_id) (Set_of_closures_contents)
    (Set_of_closures_contents.With_closure_id)
    (Set_of_closures_contents.With_closure_id_or_unknown)
    (Closures_entry)

let map_function_decl_types t ~f =
  map_maps_to t ~f:(fun closures_entry ->
    Closures_entry.map_function_decl_types closures_entry ~f)