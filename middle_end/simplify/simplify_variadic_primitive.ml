(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                       Pierre Chambart, OCamlPro                        *)
(*           Mark Shinwell and Leo White, Jane Street Europe              *)
(*                                                                        *)
(*   Copyright 2013--2017 OCamlPro SAS                                    *)
(*   Copyright 2014--2017 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

[@@@ocaml.warning "+a-4-9-30-40-41-42"]

module B = Inlining_cost.Benefit
module E = Simplify_env_and_result.Env
module K = Flambda_kind
module R = Simplify_env_and_result.Result
module S = Simplify_simple
module T = Flambda_type

module Named = Flambda.Named
module Reachable = Flambda.Reachable

type 'a or_invalid = Ok of 'a | Invalid

let simplify_make_block env r prim dbg
      ~(make_block_kind : Flambda_primitive.make_block_kind)
      ~(mutable_or_immutable : Flambda_primitive.mutable_or_immutable)
      args =
  let original_args = args in
  let args_with_tys = S.simplify_simples env args in
  let args, arg_tys = List.split args_with_tys in
  let original_term () : Named.t = Prim (Variadic (prim, args), dbg) in
  let invalid () =
    Reachable.invalid (), T.bottom (K.value Definitely_pointer),
      R.map_benefit r (B.remove_primitive (Variadic prim))
  in
  match make_block_kind with
  | Full_of_values (tag, value_kinds) ->
    if List.compare_lengths value_kinds args <> 0 then begin
      (* CR mshinwell: improve message *)
      Misc.fatal_errorf "GC value_kind indications in [Make_block] don't \
          match up 1:1 with arguments: %a"
        Simple.List.print original_args
    end;
    (* CR mshinwell: This could probably be done more neatly. *)
    let found_bottom = ref false in
    let arg_ty_values =
      assert (List.compare_lengths value_kinds arg_tys = 0);
      List.map2 (fun arg_ty value_kind ->
          if (E.type_accessor env T.is_bottom) arg_ty then begin
             found_bottom := true;
          end;
          (E.type_accessor env T.prove_of_kind_value_with_expected_value_kind)
            arg_ty value_kind)
        arg_tys value_kinds
    in
    if !found_bottom then begin
      invalid ()
    end else begin
      assert (List.compare_lengths arg_ty_values value_kinds = 0);
      let term : Named.t =
        Prim (Variadic (
          Make_block (Full_of_values (tag, value_kinds),
            mutable_or_immutable),
          args), dbg)
      in
      let ty =
        match mutable_or_immutable with
        | Immutable ->
          let fields =
            List.map (fun arg_ty_value : _ T.mutable_or_immutable ->
                Immutable arg_ty_value)
              arg_ty_values
          in
          (* CR mshinwell: eliminate gratuitous array allocations *)
          T.block_of_values tag
            ~fields:(Array.of_list fields)
        | Mutable ->
          let fields =
            List.map (fun _arg_ty : _ T.mutable_or_immutable -> Mutable)
              arg_ty_values
          in
          T.block_of_values tag ~fields:(Array.of_list fields)
      in
      Reachable.reachable term, ty, r
    end
  | Full_of_naked_floats ->
    let found_bottom = ref false in
    let arg_ty_naked_numbers =
      List.map (fun arg_ty ->
          if (E.type_accessor env T.is_bottom) arg_ty then begin
             found_bottom := true;
          end;
          (E.type_accessor env T.prove_of_kind_naked_float) arg_ty)
        arg_tys
    in
    if !found_bottom then begin
      invalid ()
    end else begin
      let ty =
        match mutable_or_immutable with
        | Immutable ->
          T.immutable_float_array (Array.of_list arg_ty_naked_numbers)
        | Mutable ->
          T.mutable_float_array
            ~size:(Targetint.OCaml.of_int (List.length arg_ty_naked_numbers))
      in
      Reachable.reachable (original_term ()), ty, r
    end
  | Generic_array _spec -> Misc.fatal_error "Not yet implemented"
  (* CR mshinwell: Finish off
    Simplify_generic_array.simplify_make_block env r prim dbg spec
      ~mutable_or_immutable args
  *)

(* CR mshinwell: Could use [unit or_invalid] rather than [bool] *)
(* XXX this should be "for all" not "exists".  Also, take care: when the list
   is empty, this should return false *)
let bigarray_indexes_are_invalid env indexes =
  let index_proofs =
    List.map (fun index ->
        (E.type_accessor env T.prove_tagged_immediate) index)
      indexes
  in
  List.fold_left
    (fun (index_proof : T.tagged_immediate_proof) invalid ->
      if invalid then true
      else
        match index_proof with
        | Proved indexes ->
          List.fold_left (fun index invalid ->
              if invalid then true
              else
                let index = Immediate.to_targetint index in
                match layout with
                | Unknown | C ->
                  Targetint.OCaml.(<) index Targetint.OCaml.zero
                | Fortran ->
                  Targetint.OCaml.(<) index Targetint.OCaml.one)
            indexes
            false
        | Proved Not_all_values_known -> false
        | Invalid -> true)
    index_proofs
    false

(* XXX add "type_of_bigarray_kind" etc in this file. *)

let simplify_bigarray_set env r prim dbg ~num_dims ~kind ~layout ~args =
  let args_with_tys = S.simplify_simple env args in
  let args, _arg_tys = List.split args_with_tys in
  let original_term () : Named.t = Prim (Variadic (prim, args), dbg) in
  let element_kind = Flambda_primitive.kind_of_bigarray_kind kind in
  let result_kind = Flambda_kind.unit () in
  let invalid () = [], Reachable.invalid (), T.bottom result_kind, r in
  let wrong_number_of_args () =
    Misc.fatal_errorf "Wrong number of arguments for [Bigarray_set]: %a"
      Flambda_primitive.print prim
  in
  match args_with_tys with
  | (bigarray, bigarray_ty)::args_with_tys ->
    begin match List.first_n args_with_tys num_dims with
    | Some (indexes_with_tys, args_with_tys) ->
      begin match args_with_tys with
      | [new_value, new_value_ty] ->
        let bigarray_proof =
          (E.type_accessor env T.prove_of_kind_value_with_expected_value_kind
            Definitely_pointer) bigarray
        in
        begin match proof with
        | Proved _ ->
          let index_proofs =
            List.map (fun index ->
                (E.type_accessor env T.prove_tagged_immediate) index)
              indexes
          in
          let invalid = bigarray_indexes_are_invalid env indexes in
          if invalid then invalid ()
          else
            let new_value_proof =
              (E.type_accessor env T.prove_of_kind result_kind) new_value
            in
            begin match new_value_proof with
            | Proved _ ->
              [], Reachable.reachable (original_term ()),
                T.unknown result_kind Other, r
            | Invalid -> invalid ()
            end
        | Invalid -> invalid ()
        end
      | _ -> wrong_number_of_args ()
      end
    | None -> wrong_number_of_args ()
    end
  | [] -> wrong_number_of_args ()

let simplify_bigarray_load env r prim dbg ~num_dims
      ~(kind : Flambda_primitive.bigarray_kind)
      ~(layout : Flambda_primitive.bigarray_layout)
      args =
  let args_with_tys = S.simplify_simple env args in
  let args, arg_tys = List.split args_with_tys in
  let original_term () : Named.t = Prim (Variadic (prim, args), dbg) in
  let result_kind = Flambda_primitive.kind_of_bigarray_kind kind in
  let invalid () = [], Reachable.invalid (), T.bottom result_kind in
  let wrong_number_of_args () =
    Misc.fatal_errorf "Wrong number of arguments: %a"
      Flambda_primitive.print prim
  in
  match args_with_tys with
  | (bigarray, bigarray_ty)::args_with_tys ->
    begin match List.first_n args_with_tys num_dims with
    | Some (indexes_with_tys, args_with_tys) ->
      begin match args_with_tys with
      | [] ->
        let bigarray_proof =
          (E.type_accessor env T.prove_of_kind_value_with_expected_scanning
            Must_scan) bigarray
        in
        begin match proof with
        | Proved _ ->
          let index_proofs =
            List.map (fun index ->
                (E.type_accessor env T.prove_tagged_immediate) index)
              indexes
          in
          let invalid = bigarray_indexes_are_invalid env indexes in
          if invalid then invalid ()
          else
            [], Reachable.reachable (original_term ()),
              T.unknown result_kind Other, r
        | Invalid -> invalid ()
        end
      | _ -> wrong_number_of_args ()
      end
    | None -> wrong_number_of_args ()
    end
  | [] -> wrong_number_of_args ()

let simplify_variadic_primitive env r prim args dbg =
  match prim with
  | Make_block (make_block_kind, mutable_or_immutable) ->
    simplify_make_block env r prim dbg ~make_block_kind ~mutable_or_immutable
      args
  | Bigarray_set (num_dims, kind, layout) ->
    simplify_bigarray_set env r prim dbg ~num_dims ~kind ~layout ~args
  | Bigarray_load (num_dims, kind, layout) ->
    simplify_bigarray_load env r prim dbg ~num_dims ~kind ~layout args
