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

open! Flambda.Import

module E = Simplify_env_and_result.Env
module R = Simplify_env_and_result.Result
module T = Flambda_type

let create_static_part (to_lift : T.to_lift) : Flambda_static.Static_part.t =
  match to_lift with
  | Boxed_float f -> Boxed_float (Const f)
  | Boxed_int32 i -> Boxed_int32 (Const i)
  | Boxed_int64 i -> Boxed_int64 (Const i)
  | Boxed_nativeint i -> Boxed_nativeint (Const i)

let try_to_reify env r (term : Reachable.t) ~bound_to ~cannot_lift =
  let ty = E.find_variable env bound_to in
  match term with
  | Invalid _ -> 
    let ty = T.bottom_like ty in
    let env = E.add_equation_on_variable env bound_to ty in
    term, env, ty, r
  | Reachable _ ->
    match T.reify (E.typing_env env) ty ~allow_free_variables:true with
    | Term (simple, ty) ->
      let term = Named.create_simple simple in
      Reachable.reachable term, env, ty, r
    | Lift to_lift ->
      if cannot_lift then term, env, ty, r
      else
        let symbol, r =
          let name = Variable.unique_name bound_to in
          let static_part = create_static_part to_lift in
          R.new_lifted_constant r ~name ty static_part
        in
        let env = E.add_symbol env symbol ty in
        let symbol = Simple.symbol symbol in
        let term = Named.create_simple symbol in
        let ty = T.alias_type_of (T.kind ty) symbol in
        let env = E.add_equation_on_variable env bound_to ty in
        Reachable.reachable term, env, ty, r
    | Cannot_reify -> term, env, ty, r
    | Invalid ->
      let ty = T.bottom_like ty in
      let env = E.add_equation_on_variable env bound_to ty in
      Reachable.invalid (), env, ty, r