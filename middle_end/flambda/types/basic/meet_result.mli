(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                       Vincent Laviron, OCamlPro                        *)
(*                                                                        *)
(*   Copyright 2021 OCamlPro SAS                                          *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* Type for the result of meet operations *)

[@@@ocaml.warning "+a-4-30-40-41-42"]

type 'a return_value =
  | Left_input
  | Right_input
  | Both_inputs
  | New_result of 'a

type ('a, 'ext) t =
  | Bottom
  | Ok of 'a return_value * 'ext

val map_result
   : f:('a -> 'b)
  -> ('a, 'ext) t
  -> ('b, 'ext) t

(** Given a result and the inputs used to generate it,
    returns the corresponding value.
    In the Both_inputs case, the left input is returned. *)
val extract_value
   : 'a return_value
  -> 'a
  -> 'a
  -> 'a

val set_meet
   : no_extension:'ext
  -> (module Set.S with type t = 'a)
  -> 'a
  -> 'a
  -> ('a, 'ext) t
