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

[@@@ocaml.warning "+a-4-9-30-40-41-42"]

open! Flambda.Import

module DA = Downwards_acc
module DE = Simplify_env_and_result.Downwards_env
module K = Flambda_kind
module S = Simplify_simple
module T = Flambda_type
module TEE = Flambda_type.Typing_env_extension

let simplify_make_block dacc _prim dbg
      ~(make_block_kind : Flambda_primitive.make_block_kind)
      ~(mutable_or_immutable : Flambda_primitive.mutable_or_immutable)
      args_with_tys ~result_var =
  let denv = DA.denv dacc in
  let args, _arg_tys = List.split args_with_tys in
  let invalid () =
    let ty = T.bottom K.value in
    let env_extension = TEE.one_equation (Name.var result_var) ty in
    Reachable.invalid (), env_extension, dacc
  in
  match make_block_kind with
  | Full_of_values (tag, value_kinds) ->
    if List.compare_lengths value_kinds args <> 0 then begin
      (* CR mshinwell: improve message *)
      Misc.fatal_errorf "GC value_kind indications in [Make_block] don't \
          match up 1:1 with arguments: %a"
        Simple.List.print args
    end;
    (* CR mshinwell: This could probably be done more neatly. *)
    let found_bottom = ref false in
    let fields =
      assert (List.compare_lengths value_kinds args_with_tys = 0);
      List.map2 (fun ((arg : Simple.t), arg_ty) _value_kind ->
          if T.is_bottom (DE.typing_env denv) arg_ty then begin
           found_bottom := true
          end;
          match Simple.descr arg with
          | Const _ -> T.force_to_kind_value arg_ty
          | Name name -> T.alias_type_of_as_ty_value (Simple.name name)
          | Discriminant _ -> assert false  (* CR mshinwell: proper error! *) )
        args_with_tys value_kinds
    in
    if !found_bottom then begin
      invalid ()
    end else begin
      assert (List.compare_lengths fields value_kinds = 0);
      let term : Named.t =
        Named.create_prim
          (Variadic (
            Make_block (Full_of_values (tag, value_kinds),
              mutable_or_immutable),
            args))
          dbg
      in
      let tag = Tag.Scannable.to_tag tag in
      let ty =
        match mutable_or_immutable with
        | Immutable -> T.immutable_block_of_values tag ~fields
        | Mutable -> Misc.fatal_error "Not yet implemented"
      in
      let env_extension = TEE.one_equation (Name.var result_var) ty in
      Reachable.reachable term, env_extension, dacc
    end
  | Full_of_naked_floats -> Misc.fatal_error "Not yet implemented"
  | Generic_array _spec -> Misc.fatal_error "Not yet implemented"

let simplify_variadic_primitive dacc
      (prim : Flambda_primitive.variadic_primitive) args dbg ~result_var =
  let min_occurrence_kind = Var_in_binding_pos.occurrence_kind result_var in
  let result_var = Var_in_binding_pos.var result_var in
  match S.simplify_simples dacc args ~min_occurrence_kind with
  | Bottom ->
    let kind = Flambda_primitive.result_kind_of_variadic_primitive' prim in
    let env_extension =
      TEE.one_equation (Name.var result_var) (T.bottom kind)
    in
    Reachable.invalid (), env_extension, dacc
  | Ok args_with_tys ->
    match prim with
    | Make_block (make_block_kind, mutable_or_immutable) ->
      simplify_make_block dacc prim dbg ~make_block_kind ~mutable_or_immutable
        args_with_tys ~result_var
    | Bigarray_set (_num_dims, _kind, _layout)
    | Bigarray_load (_num_dims, _kind, _layout) ->
      let named = Named.create_prim (Variadic (prim, args)) dbg in
      let kind = Flambda_primitive.result_kind_of_variadic_primitive' prim in
      let ty = T.unknown kind in
      let env_extension = TEE.one_equation (Name.var result_var) ty in
      Reachable.reachable named, env_extension, dacc