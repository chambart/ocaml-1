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

(** The external interface of the meet_and_join/ directory. *)

[@@@ocaml.warning "+a-4-30-40-41-42"]

(** Greatest lower bound of two types. *)
val meet
   : Meet_env.t
  -> Flambda_types.t
  -> Flambda_types.t
  -> Flambda_types.t * Typing_env_extension.t

(** Least upper bound of two types. *)
val join
   : ?bound_name:Name.t
  -> Join_env.t
  -> Flambda_types.t
  -> Flambda_types.t
  -> Flambda_types.t
