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

(** Construction of meet and join operations for types of kind
    (Naked_number Float). *)

[@@@ocaml.warning "+a-4-30-40-41-42"]

include Meet_and_join_naked_number_intf.S
  with module Flambda_types := Flambda_types
  with module Join_env := Join_env
  with module Meet_env := Meet_env
  with module Naked_number := Float
  with module Typing_env_extension := Typing_env_extension