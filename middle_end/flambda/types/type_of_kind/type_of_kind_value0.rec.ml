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

[@@@ocaml.warning "+a-30-40-41-42"]

module T = Type_grammar
module TEE = Typing_env_extension

module Blocks = Row_like.For_blocks

type t =
  | Variant of Variant.t
  (* CR mshinwell: Add constructors for the following too so we can check
     they aren't bottom? *)
  | Boxed_float of T.t
  | Boxed_int32 of T.t
  | Boxed_int64 of T.t
  | Boxed_nativeint of T.t
  | Closures of {
      by_closure_id : Row_like.For_closures_entry_by_set_of_closures_contents.t;
    }
  | String of String_info.Set.t
  | Array of { length : T.t; }

let print_with_cache ~cache ppf t =
  match t with
  | Variant { blocks; immediates; is_unique } ->
    (* CR mshinwell: Improve so that we elide blocks and/or immediates when
       they're empty. *)
    Format.fprintf ppf
      "@[<hov 1>(Variant%s@ \
        @[<hov 1>(blocks@ %a)@]@ \
        @[<hov 1>(tagged_imms@ %a)@]\
        )@]"
      (if is_unique then " unique" else "")
      (Or_unknown.print (Blocks.print_with_cache ~cache)) blocks
      (Or_unknown.print (T.print_with_cache ~cache)) immediates
  | Boxed_float naked_ty ->
    Format.fprintf ppf "@[<hov 1>(Boxed_float@ %a)@]"
      (T.print_with_cache ~cache) naked_ty
  | Boxed_int32 naked_ty ->
    Format.fprintf ppf "@[<hov 1>(Boxed_int32@ %a)@]"
      (T.print_with_cache ~cache) naked_ty
  | Boxed_int64 naked_ty ->
    Format.fprintf ppf "@[<hov 1>(Boxed_int64@ %a)@]"
      (T.print_with_cache ~cache) naked_ty
  | Boxed_nativeint naked_ty ->
    Format.fprintf ppf "@[<hov 1>(Boxed_nativeint@ %a)@]"
      (T.print_with_cache ~cache) naked_ty
  | Closures { by_closure_id; } ->
    Row_like.For_closures_entry_by_set_of_closures_contents.print_with_cache ~cache
      ppf by_closure_id
  | String str_infos ->
    Format.fprintf ppf "@[<hov 1>(Strings@ (%a))@]"
      String_info.Set.print str_infos
  | Array { length; } ->
    Format.fprintf ppf "@[<hov 1>(Array@ (length@ %a))@]"
      (T.print_with_cache ~cache) length

let print ppf t = print_with_cache ~cache:(Printing_cache.create ()) ppf t

let apply_renaming_variant blocks immediates perm =
  let immediates' =
    Or_unknown.map immediates ~f:(fun immediates ->
      T.apply_renaming immediates perm)
  in
  let blocks' =
    Or_unknown.map blocks ~f:(fun blocks ->
      Blocks.apply_renaming blocks perm)
  in
  if immediates == immediates' && blocks == blocks' then
    None
  else
    Some (blocks', immediates')

let apply_renaming t perm =
  match t with
  | Variant { blocks; immediates; is_unique; } ->
    begin match
      apply_renaming_variant blocks immediates perm
    with
    | None -> t
    | Some (blocks, immediates) ->
      Variant (Variant.create ~is_unique ~blocks ~immediates)
    end
  | Boxed_float ty ->
    let ty' = T.apply_renaming ty perm in
    if ty == ty' then t
    else Boxed_float ty'
  | Boxed_int32 ty ->
    let ty' = T.apply_renaming ty perm in
    if ty == ty' then t
    else Boxed_int32 ty'
  | Boxed_int64 ty ->
    let ty' = T.apply_renaming ty perm in
    if ty == ty' then t
    else Boxed_int64 ty'
  | Boxed_nativeint ty ->
    let ty' = T.apply_renaming ty perm in
    if ty == ty' then t
    else Boxed_nativeint ty'
  | Closures { by_closure_id; } ->
    let by_closure_id' =
      Row_like.For_closures_entry_by_set_of_closures_contents.apply_renaming
        by_closure_id perm
    in
    if by_closure_id == by_closure_id' then t
    else Closures { by_closure_id = by_closure_id'; }
  | String _ -> t
  | Array { length; } ->
    let length' = T.apply_renaming length perm in
    if length == length' then t
    else Array { length = length'; }

let free_names t =
  match t with
  | Variant { blocks; immediates; is_unique = _; } ->
    Name_occurrences.union
      (Or_unknown.free_names Blocks.free_names blocks)
      (Or_unknown.free_names T.free_names immediates)
  | Boxed_float ty -> T.free_names ty
  | Boxed_int32 ty -> T.free_names ty
  | Boxed_int64 ty -> T.free_names ty
  | Boxed_nativeint ty -> T.free_names ty
  | Closures { by_closure_id; } ->
    Row_like.For_closures_entry_by_set_of_closures_contents.free_names by_closure_id
  | String _ -> Name_occurrences.empty
  | Array { length; } -> T.free_names length

let all_ids_for_export t =
  match t with
  | Variant { blocks; immediates; is_unique = _; } ->
    Ids_for_export.union
      (Or_unknown.all_ids_for_export Blocks.all_ids_for_export blocks)
      (Or_unknown.all_ids_for_export T.all_ids_for_export immediates)
  | Boxed_float ty -> T.all_ids_for_export ty
  | Boxed_int32 ty -> T.all_ids_for_export ty
  | Boxed_int64 ty -> T.all_ids_for_export ty
  | Boxed_nativeint ty -> T.all_ids_for_export ty
  | Closures { by_closure_id; } ->
    Row_like.For_closures_entry_by_set_of_closures_contents.all_ids_for_export
      by_closure_id
  | String _ -> Ids_for_export.empty
  | Array { length; } -> T.all_ids_for_export length

let apply_coercion t coercion : _ Or_bottom.t =
  match t with
  | Closures { by_closure_id; } ->
    Or_bottom.map
      (Row_like.For_closures_entry_by_set_of_closures_contents.
       map_function_decl_types
        by_closure_id
        ~f:(fun (decl : Function_declaration_type.t) : _ Or_bottom.t ->
          Function_declaration_type.apply_coercion decl coercion))
      ~f:(fun by_closure_id -> Closures { by_closure_id; })
  | Variant _
  | Boxed_float _
  | Boxed_int32 _
  | Boxed_int64 _
  | Boxed_nativeint _
  | String _
  | Array _ ->
    if Coercion.is_id coercion then Ok t
    else Bottom

let eviscerate t : _ Or_unknown.t =
  match t with
  | Boxed_float _ -> Known (Boxed_float (T.any_naked_float ()))
  | Boxed_int32 _ -> Known (Boxed_int32 (T.any_naked_int32 ()))
  | Boxed_int64 _ -> Known (Boxed_int64 (T.any_naked_int64 ()))
  | Boxed_nativeint _ -> Known (Boxed_nativeint (T.any_naked_nativeint ()))
  | Closures _
  | Variant _
  | String _
  | Array _ -> Unknown

let meet_unknown meet_contents ~contents_is_bottom env
    (or_unknown1 : _ Or_unknown.t) (or_unknown2 : _ Or_unknown.t)
    : (_ Or_unknown.t, TEE.t) Meet_result.t =
  match or_unknown1, or_unknown2 with
  | Unknown, Unknown -> Ok (Both_inputs, TEE.empty ())
  (* CR mshinwell: Think about the next two cases more *)
  (* vlaviron: When at least one of the inputs is bottom we
     will return a bottom value, but we can choose whether we want to
     return the Bottom constructor directly or merely which inputs
     are bottom. I chose the second version, because it allows the
     meet_variant function to correctly propagate which input is
     unchanged without calling is_bottom again. *)
  | Known contents, _ when contents_is_bottom contents ->
    begin match or_unknown2 with
    | Known contents when contents_is_bottom contents ->
      Ok (Both_inputs, TEE.empty ())
    | _ ->
      Ok (Left_input, TEE.empty ())
    end
  | _, Known contents when contents_is_bottom contents ->
    Ok (Right_input, TEE.empty ())
  | _, Unknown -> Ok (Left_input, TEE.empty ())
  | Unknown, _ -> Ok (Right_input, TEE.empty ())
  | Known contents1, Known contents2 ->
    Meet_result.map_result (meet_contents env contents1 contents2)
      ~f:(fun contents -> Or_unknown.Known contents)

let join_unknown join_contents (env : Join_env.t)
    (or_unknown1 : _ Or_unknown.t) (or_unknown2 : _ Or_unknown.t)
    : _ Or_unknown.t =
  match or_unknown1, or_unknown2 with
  | _, Unknown
  | Unknown, _ -> Unknown
  | Known contents1, Known contents2 ->
    join_contents env contents1 contents2

let meet_variant env
      ~blocks1 ~imms1 ~blocks2 ~imms2 : _ Meet_result.t =
  let blocks_is_bottom blocks =
    match (blocks : _ Or_unknown.t) with
    | Unknown -> false
    | Known blocks -> Blocks.is_bottom blocks
  in
  let immediates_is_bottom immediates =
    match (immediates : _ Or_unknown.t) with
    | Unknown -> false
    | Known imms -> T.is_obviously_bottom imms
  in
  let blocks =
    meet_unknown Blocks.meet ~contents_is_bottom:Blocks.is_bottom
      env blocks1 blocks2
  in
  let imms =
    meet_unknown T.meet ~contents_is_bottom:T.is_obviously_bottom
      env imms1 imms2
  in
  match blocks, imms with
  (* CR vlaviron: Note on the Bottom cases:
     We're only expecting the underlying meets to return Bottom if
     neither input was already Bottom (otherwise, we would have gotten
     one of Both_inputs, Left_input or Right_input).
     Since we want to return Bottom rather than New_result in the case
     where the returned type is bottom, we check for bottom results
     in the cases where it can occur.
  *)
  | Bottom, Bottom -> Bottom
  | Ok (blocks, env_extension), Bottom ->
    let immediates : _ Or_unknown.t = Known (T.bottom K.naked_immediate) in
    let blocks = Meet_result.extract_value blocks blocks1 blocks2 in
    if blocks_is_bottom blocks then
      Bottom
    else
      Ok (New_result (blocks, immediates), env_extension)
  | Bottom, Ok (immediates, env_extension) ->
    let blocks : _ Or_unknown.t = Known (Blocks.create_bottom ()) in
    let immediates = Meet_result.extract_value immediates imms1 imms2 in
    if immediates_is_bottom immediates then
      Bottom
    else
      Ok (New_result (blocks, immediates), env_extension)
  | Ok (blocks_res, env_extension1), Ok (immediates_res, env_extension2) ->
    let blocks = Meet_result.extract_value blocks_res blocks1 blocks2 in
    let immediates = Meet_result.extract_value immediates_res imms1 imms2 in
    let bottom_blocks = blocks_is_bottom blocks in
    let bottom_immediates = immediates_is_bottom immediates in
    let env_extension =
      if bottom_immediates then env_extension1
      else if bottom_blocks then env_extension2
      else
        let env = Meet_env.env env in
        let join_env =
          Join_env.create env ~left_env:env ~right_env:env
        in
        TEE.join join_env env_extension1 env_extension2
    in
    begin match blocks_res, immediates_res with
    | Both_inputs, Both_inputs ->
      Ok (Both_inputs, env_extension)
    | (Left_input | Both_inputs), (Left_input | Both_inputs) ->
      Ok (Left_input, env_extension)
    | (Right_input | Both_inputs), (Right_input | Both_inputs) ->
      Ok (Right_input, env_extension)
    | Left_input, Right_input
    | Right_input, Left_input
    | New_result _, _
    | _, New_result _ ->
      if bottom_blocks && bottom_immediates then
        Bottom
      else
        Ok (New_result (blocks, immediates), env_extension)
    end

let meet env t1 t2 : _ Meet_result.t =
  match t1, t2 with
  | Variant { blocks = blocks1; immediates = imms1; is_unique = is_unique1; },
    Variant { blocks = blocks2; immediates = imms2; is_unique = is_unique2; } ->
    Meet_result.map_result
      (meet_variant env ~blocks1 ~imms1 ~blocks2 ~imms2)
      ~f:(fun (blocks, immediates) ->
        (* Uniqueness tracks whether duplication/lifting is allowed.
           It must always be propagated, both for meet and join. *)
        let is_unique = is_unique1 || is_unique2 in
        Variant (Variant.create ~is_unique ~blocks ~immediates))
  | Boxed_float n1, Boxed_float n2 ->
    Meet_result.map_result
      (T.meet env n1 n2)
      ~f:(fun n -> Boxed_float n)
  | Boxed_int32 n1, Boxed_int32 n2 ->
    Meet_result.map_result
      (T.meet env n1 n2)
      ~f:(fun n -> Boxed_int32 n)
  | Boxed_int64 n1, Boxed_int64 n2 ->
    Meet_result.map_result
      (T.meet env n1 n2)
      ~f:(fun n -> Boxed_int64 n)
  | Boxed_nativeint n1, Boxed_nativeint n2 ->
    Meet_result.map_result
      (T.meet env n1 n2)
      ~f:(fun n -> Boxed_nativeint n)
  | Closures { by_closure_id = by_closure_id1; },
    Closures { by_closure_id = by_closure_id2; } ->
    let module C = Row_like.For_closures_entry_by_set_of_closures_contents in
    Meet_result.map_result
      (C.meet env by_closure_id1 by_closure_id2)
      ~f:(fun by_closure_id -> Closures { by_closure_id; })
  | String strs1, String strs2 ->
    Meet_result.map_result
      (Meet_result.set_meet ~no_extension:(TEE.empty ())
         (module String_info.Set) strs1 strs2)
      ~f:(fun strs -> String strs)
  | Array { length = length1; }, Array { length = length2; } ->
    Meet_result.map_result
      (T.meet env length1 length2)
      ~f:(fun length -> Array { length; })
  | (Variant _
    | Boxed_float _
    | Boxed_int32 _
    | Boxed_int64 _
    | Boxed_nativeint _
    | Closures _
    | String _
    | Array _), _ ->
    (* CR vlaviron: This assumes that all the different constructors are
       incompatible. This could break very hard for users of Obj. *)
    Bottom

let join_variant env
      ~blocks1 ~imms1 ~blocks2 ~imms2 : _ Or_unknown.t =
  let blocks_join env b1 b2 : _ Or_unknown.t =
    Known (Blocks.join env b1 b2)
  in
  let blocks =
    join_unknown blocks_join env blocks1 blocks2
  in
  let imms =
    join_unknown (T.join ?bound_name:None) env imms1 imms2
  in
  match blocks, imms with
  | Unknown, Unknown -> Unknown
  | Known _, Unknown | Unknown, Known _ | Known _, Known _ ->
    Known (blocks, imms)

let join env t1 t2 : _ Or_unknown.t =
  match t1, t2 with
  | Variant { blocks = blocks1; immediates = imms1; is_unique = is_unique1; },
    Variant { blocks = blocks2; immediates = imms2; is_unique = is_unique2; } ->
    Or_unknown.map
      (join_variant env ~blocks1 ~imms1 ~blocks2 ~imms2)
      ~f:(fun (blocks, immediates) ->
        (* Uniqueness tracks whether duplication/lifting is allowed.
           It must always be propagated, both for meet and join. *)
        let is_unique = is_unique1 || is_unique2 in
        Variant (Variant.create ~is_unique ~blocks ~immediates))
  | Boxed_float n1, Boxed_float n2 ->
    Or_unknown.map
      (T.join env n1 n2)
      ~f:(fun n -> Boxed_float n)
  | Boxed_int32 n1, Boxed_int32 n2 ->
    Or_unknown.map
      (T.join env n1 n2)
      ~f:(fun n -> Boxed_int32 n)
  | Boxed_int64 n1, Boxed_int64 n2 ->
    Or_unknown.map
      (T.join env n1 n2)
      ~f:(fun n -> Boxed_int64 n)
  | Boxed_nativeint n1, Boxed_nativeint n2 ->
    Or_unknown.map
      (T.join env n1 n2)
      ~f:(fun n -> Boxed_nativeint n)
  | Closures { by_closure_id = by_closure_id1; },
    Closures { by_closure_id = by_closure_id2; } ->
    let module C = Row_like.For_closures_entry_by_set_of_closures_contents in
    let by_closure_id = C.join env by_closure_id1 by_closure_id2 in
    Known (Closures { by_closure_id; })
  | String strs1, String strs2 ->
    let strs = String_info.Set.union strs1 strs2 in
    Known (String strs)
  | Array { length = length1; }, Array { length = length2; } ->
    Or_unknown.map
      (T.join env length1 length2)
      ~f:(fun length -> Array { length; })
  | (Variant _
    | Boxed_float _
    | Boxed_int32 _
    | Boxed_int64 _
    | Boxed_nativeint _
    | Closures _
    | String _
    | Array _), _ -> Unknown
