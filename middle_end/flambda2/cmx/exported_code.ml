(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                       Vincent Laviron, OCamlPro                        *)
(*                                                                        *)
(*   Copyright 2020 OCamlPro SAS                                          *)
(*   Copyright 2014--2021 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

[@@@ocaml.warning "+a-4-30-40-41-42"]

module C = Code

type t =
  { code : Code_or_metadata.t Code_id.Map.t;
  }

type raw = t

let [@ocamlformat "disable"] print ppf { code; } =
  Format.fprintf ppf "@[<hov 1>(\
      @[(code@ %a)@]@\
      @]"
  (Code_id.Map.print Code_or_metadata.print) code

let empty = { code = Code_id.Map.empty }

let add_code ~keep_code code_map t =
  let added_code =
    Code_id.Map.mapi
    (fun code_id code ->
      if not (Code_id.equal code_id (Code.code_id code))
      then
        Misc.fatal_errorf "Code ID key in map disagrees with [Code]:@ %a"
          (Code_id.Map.print Code.print)
          code_map;
      let code_or_metadata = Code_or_metadata.create code in
      if (not (keep_code code_id))
         && Function_decl_inlining_decision_type.cannot_be_inlined
              (C.inlining_decision code)
      then Code_or_metadata.remember_only_metadata code_or_metadata
      else code_or_metadata)
    code_map
  in
  { code = Code_id.Map.disjoint_union t.code added_code }

let mark_as_imported t =
  let code = Code_id.Map.map_sharing Code_or_metadata.remember_only_metadata t.code in
  { code; }

let merge
      { code = code1; }
      { code = code2; } =
  let code = Code_id.Map.union Code_or_metadata.merge code1 code2 in
  { code;
  }


let mem code_id t = Code_id.Map.mem code_id t.code

let find_exn t code_id = Code_id.Map.find code_id t.code

let find t code_id =
  match Code_id.Map.find code_id t.code with
  | exception Not_found ->
    (* In some cases a code ID is created, the corresponding closure stored into
       another closure, but the corresponding closure variable ends up never
       being used and so the initial code ID and closure are removed, but the
       type of the second closure still mentions its closure variable and its
       contents (eventually pointing to the code ID). Ideally the type should be
       patched to remove the unused closure variable before computing
       reachability, but for now this is done during import instead so we can
       end up with missing code IDs during the reachability computation, and
       have to assume that it fits the above case.

       The other situation where this returns [None] is when we are looking
       during the export reachability computation for a piece of deleted code.
       This can happen because the code ID might have been encountered via a
       "newer version of" field during reachability. *)
    None
  | code_or_metadata -> Some code_or_metadata

let remove_unreachable ~reachable_names t =
  let code =
  Code_id.Map.filter
    (fun code_id _code_or_metadata ->
      Name_occurrences.mem_code_id reachable_names code_id)
    t.code
  in
  { code }

let remove_unused_closure_vars_from_result_types ~used_closure_vars t =
  Code_id.Map.map
    (fun code_or_metadata ->
      Code_or_metadata.map_result_types code_or_metadata ~f:(fun result_ty ->
          Flambda2_types.remove_unused_closure_vars result_ty ~used_closure_vars))
    t

let all_ids_for_export t =
  Code_id.Map.fold
    (fun code_id code_or_metadata all_ids ->
      Ids_for_export.union
        (Ids_for_export.add_code_id all_ids code_id)
        (Code_or_metadata.all_ids_for_export code_or_metadata))
    t.code Ids_for_export.empty

let apply_renaming code_id_map renaming t =
  if Renaming.is_empty renaming && Code_id.Map.is_empty code_id_map
  then t
  else
    let code =
      Code_id.Map.fold
        (fun code_id code_or_metadata all_code ->
           let code_id =
             match Code_id.Map.find code_id code_id_map with
             | exception Not_found -> code_id
             | code_id -> code_id
           in
           let code_or_metadata =
             Code_or_metadata.apply_renaming code_or_metadata renaming
           in
           Code_id.Map.add code_id code_or_metadata all_code)
        t.code Code_id.Map.empty
    in
    { code }

let iter_code t ~f =
  Code_id.Map.iter
    (fun _code_id code_or_metadata ->
      Code_or_metadata.iter_code code_or_metadata ~f)
    t.code

let fold_for_cmx t ~init ~f =
  Code_id.Map.fold (fun code_id code_or_metadata acc ->
      Code_or_metadata.fold_code_for_cmx code_or_metadata ~init:acc
        ~f:(fun acc code_in_cmx -> f acc code_id (Obj.repr code_in_cmx)))
        t.code
        init

let prepare_for_cmx_header_section t =
  let code =
    Code_id.Map.map Code_or_metadata.prepare_for_cmx_header_section t.code
  in
  { code }

let associate_with_loaded_cmx_file t
      ~read_flambda_section_from_cmx_file ~code_sections_map
      ~used_closure_vars ~original_compilation_unit =
  let read_flambda_section_from_cmx_file ~index : Code_or_metadata.code_in_cmx =
    read_flambda_section_from_cmx_file ~index
    |> Obj.obj
  in
  let loader : Code_or_metadata.loader = {
    read_flambda_section_from_cmx_file;
    used_closure_vars;
    original_compilation_unit;
    code_sections_map;
    }
  in
  let code =
    Code_id.Map.mapi (fun code_id code_or_metadata ->
        Code_or_metadata.associate_with_loaded_cmx_file code_or_metadata code_id loader)
      t.code
  in
  { code; }
