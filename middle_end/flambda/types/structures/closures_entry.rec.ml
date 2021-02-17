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

module FDT = Function_declaration_type
module PC = Product.Closure_id_indexed
module PV = Product.Var_within_closure_indexed
module TEE = Typing_env_extension

type t = {
  (* CR pchambart: This is exactly a Product with a different kind of fields
     Product should maybe be functorized once more to represent this.
     Maybe not because product also contains a kind which we don't want in that case.

     Also the closure_types and closure_var_types products shouldn't have to store the
     kind because it is always the same. *)
  function_decls : FDT.t Closure_id.Map.t;
  closure_types : PC.t;
  closure_var_types : PV.t;
}

let create ~function_decls ~closure_types ~closure_var_types =
  { function_decls;
    closure_types;
    closure_var_types;
  }

let print_with_cache ~cache ppf
      { function_decls; closure_types; closure_var_types; } =
  Format.fprintf ppf
    "@[<hov 1>(\
      @[<hov 1>(function_decls@ %a)@]@ \
      @[<hov 1>(closure_types@ %a)@]@ \
      @[<hov 1>(closure_var_types@ %a)@]\
      )@]"
    (Closure_id.Map.print (FDT.print_with_cache ~cache)) function_decls
    (PC.print_with_cache ~cache) closure_types
    (PV.print_with_cache ~cache) closure_var_types

let print ppf t = print_with_cache ~cache:(Printing_cache.create ()) ppf t

let meet env
      { function_decls = function_decls1;
        closure_types = closure_types1;
        closure_var_types = closure_var_types1;
      }
      { function_decls = function_decls2;
        closure_types = closure_types2;
        closure_var_types = closure_var_types2;
      } : _ Meet_result.t =
  let any_bottom = ref false in
  let all_left = ref true in
  let all_right = ref true in
  let env_extensions = ref (TEE.empty ()) in
  let function_decls =
    Closure_id.Map.merge (fun _closure_id func_decl1 func_decl2 ->
      match func_decl1, func_decl2 with
      | None, None -> None
      | Some func_decl, None | None, Some func_decl -> Some func_decl
      | Some func_decl1, Some func_decl2 ->
        match FDT.meet env func_decl1 func_decl2 with
        | Bottom ->
          any_bottom := true;
          None
        | Ok (meet_result, env_extension) ->
          begin match TEE.meet env !env_extensions env_extension with
          | Bottom ->
            any_bottom := true;
          | Ok env_extension ->
            env_extensions := env_extension
          end;
          begin match meet_result with
          | Left_input ->
            all_right := false;
            Some func_decl1
          | Right_input ->
            all_left := false;
            Some func_decl2
          | Both_inputs ->
            Some func_decl1
          | New_result func_decl ->
            all_left := false;
            all_right := false;
            Some func_decl
          end)
      function_decls1 function_decls2
  in
  if !any_bottom then
    Bottom
  else
    let closure_types_meet =
      PC.meet env closure_types1 closure_types2
    in
    let closure_var_types_meet =
      PV.meet env closure_var_types1 closure_var_types2
    in
    match closure_types_meet, closure_var_types_meet with
    | Bottom, _ | _, Bottom -> Bottom
    | Ok (closure_types_res, env_extension1),
      Ok (closure_var_types_res, env_extension2) ->
      match TEE.meet env !env_extensions env_extension1 with
      | Bottom -> Bottom
      | Ok env_extension ->
        match TEE.meet env env_extension env_extension2 with
        | Bottom -> Bottom
        | Ok env_extension ->
          begin match closure_types_res,
                      closure_var_types_res,
                      !all_left,
                      !all_right with
          | Both_inputs, Both_inputs, true, true ->
            Ok (Both_inputs, env_extension)
          | (Left_input | Both_inputs),
            (Left_input | Both_inputs),
            true, _ ->
            Ok (Left_input, env_extension)
          | (Right_input | Both_inputs),
            (Right_input | Both_inputs),
            _, true ->
            Ok (Right_input, env_extension)
          | New_result _, _, _, _
          | _, New_result _, _, _
          | _, _, false, false
          | Left_input, Right_input, _, _
          | Left_input, _, false, _
          | Right_input, Left_input, _, _
          | Right_input, _, _, false
          | _, Left_input, false, _
          | _, Right_input, _, false ->
            let closure_types =
              Meet_result.extract_value closure_types_res
                closure_types1 closure_types2
            in
            let closure_var_types =
              Meet_result.extract_value closure_var_types_res
                closure_var_types1 closure_var_types2
            in
            let closures_entry =
              { function_decls;
                closure_types;
                closure_var_types;
              }
            in
            Ok (New_result closures_entry, env_extension)
          end

let join env
      { function_decls = function_decls1;
        closure_types = closure_types1;
        closure_var_types = closure_var_types1;
      }
      { function_decls = function_decls2;
        closure_types = closure_types2;
        closure_var_types = closure_var_types2;
      } =
  let function_decls =
    Closure_id.Map.merge (fun _closure_id func_decl1 func_decl2 ->
        match func_decl1, func_decl2 with
        | None, None
        (* CR mshinwell: Are these next two cases right?  Don't we need to
           do the equivalent of make_suitable_for_environment? *)
        | Some _, None
        | None, Some _ -> None
        | Some func_decl1, Some func_decl2 ->
          Some (FDT.join env func_decl1 func_decl2))
      function_decls1 function_decls2
  in
  let closure_types =
    PC.join env closure_types1 closure_types2
  in
  let closure_var_types =
    PV.join env closure_var_types1 closure_var_types2
  in
  { function_decls;
    closure_types;
    closure_var_types;
  }

let apply_renaming
      { function_decls; closure_types; closure_var_types; } perm =
  { function_decls =
      Closure_id.Map.map_sharing (fun function_decl ->
          FDT.apply_renaming function_decl perm)
        function_decls;
    closure_types = PC.apply_renaming closure_types perm;
    closure_var_types = PV.apply_renaming closure_var_types perm;
  }

let free_names { function_decls; closure_types; closure_var_types; } =
  let function_decls_free_names =
    Closure_id.Map.fold (fun _closure_id function_decl free_names ->
        Name_occurrences.union free_names (FDT.free_names function_decl))
      function_decls
      Name_occurrences.empty
  in
  Name_occurrences.union function_decls_free_names
    (Name_occurrences.union (PC.free_names closure_types)
      (PV.free_names closure_var_types))

let all_ids_for_export { function_decls; closure_types; closure_var_types; } =
  let function_decls_ids =
    Closure_id.Map.fold (fun _closure_id function_decl ids ->
        Ids_for_export.union ids (FDT.all_ids_for_export function_decl))
      function_decls
      Ids_for_export.empty
  in
  Ids_for_export.union function_decls_ids
    (Ids_for_export.union (PC.all_ids_for_export closure_types)
      (PV.all_ids_for_export closure_var_types))

let function_decl_types t = t.function_decls
let closure_types t = PC.to_map t.closure_types
let closure_var_types t = PV.to_map t.closure_var_types

let find_function_declaration t closure_id : _ Or_bottom.t =
  match Closure_id.Map.find closure_id t.function_decls with
  | exception Not_found -> Bottom
  | func_decl -> Ok func_decl

let map_function_decl_types
      { function_decls; closure_types; closure_var_types; }
      ~(f : FDT.t -> FDT.t Or_bottom.t) : _ Or_bottom.t =
  (* CR mshinwell: This needs to deal with [closure_types] too.
     Deferring until new approach for [Rec_info] is sorted out. *)
  let bottom = ref false in
  let function_decls =
    Closure_id.Map.map (fun function_decl ->
        match f function_decl with
        | Ok function_decl -> function_decl
        | Bottom ->
          bottom := true;
          function_decl)
      function_decls
  in
  if !bottom then Bottom
  else
    let t =
      { function_decls;
        closure_types;
        closure_var_types;
      }
    in
    Ok t
