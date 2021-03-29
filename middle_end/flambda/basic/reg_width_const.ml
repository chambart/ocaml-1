(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                       Pierre Chambart, OCamlPro                        *)
(*           Mark Shinwell and Leo White, Jane Street Europe              *)
(*                                                                        *)
(*   Copyright 2013--2020 OCamlPro SAS                                    *)
(*   Copyright 2014--2020 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

[@@@ocaml.warning "+a-30-40-41-42"]

include Reg_width_things.Const

let kind t =
  let module K = Flambda_kind in
  match descr t with
  | Naked_immediate _ -> K.naked_immediate
  | Tagged_immediate _ -> K.value
  | Naked_float _ -> K.naked_float
  | Naked_int32 _ -> K.naked_int32
  | Naked_int64 _ -> K.naked_int64
  | Naked_nativeint _ -> K.naked_nativeint

let of_descr (descr : Descr.t) =
  match descr with
  | Naked_immediate (Value, i) -> naked_immediate i
  | Tagged_immediate (Value, i) -> tagged_immediate i
  | Naked_float (Value, f) -> naked_float f
  | Naked_int32 (Value, i) -> naked_int32 i
  | Naked_int64 (Value, i) -> naked_int64 i
  | Naked_nativeint (Value, i) -> naked_nativeint i
  | Naked_immediate (Poison, _) -> naked_immediate_poison
  | Tagged_immediate (Poison, _) -> tagged_immediate_poison
  | Naked_float (Poison, _) -> naked_float_poison
  | Naked_int32 (Poison, _) -> naked_int32_poison
  | Naked_int64 (Poison, _) -> naked_int64_poison
  | Naked_nativeint (Poison, _) -> naked_nativeint_poison
