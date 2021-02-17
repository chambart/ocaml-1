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

[@@@ocaml.warning "+a-4-30-40-41-42"]

type 'a return_value =
  | Left_input
  | Right_input
  | Both_inputs
  | New_result of 'a

type ('a, 'ext) t =
  | Bottom
  | Ok of 'a return_value * 'ext

let map_result ~f = function
  | Bottom -> Bottom
  | Ok (Left_input, ext) -> Ok (Left_input, ext)
  | Ok (Right_input, ext) -> Ok (Right_input, ext)
  | Ok (Both_inputs, ext) -> Ok (Both_inputs, ext)
  | Ok (New_result x, ext) -> Ok (New_result (f x), ext)

let extract_value res left right =
  match res with
  | Left_input -> left
  | Right_input -> right
  | Both_inputs -> left
  | New_result value -> value

let set_meet (type a) ~no_extension (module S : Set.S with type t = a)
      (s1 : a) (s2 : a) =
  match S.subset s1 s2, S.subset s2 s1 with
  | true, true -> Ok (Both_inputs, no_extension)
  | true, false -> Ok (Left_input, no_extension)
  | false, true -> Ok (Right_input, no_extension)
  | false, false ->
    let s = S.inter s1 s2 in
    if S.is_empty s then Bottom
    else Ok (New_result s, no_extension)
