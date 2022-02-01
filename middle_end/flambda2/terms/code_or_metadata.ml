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

[@@@ocaml.warning "+a-30-40-41-42"]

type code_in_cmx =
  { code : Code.t;
    table_data : Ids_for_export.Table_data.t
  }

type loader =
  { (* To avoid creating a new closure per piece of code, we record here a
       closure that is able to load from the correct .cmx file (values of type
       [t] may involve code from various different .cmx files), with the actual
       section index stored separately in the [code_sections_map] (which was
       already computed). *)
    read_flambda_section_from_cmx_file : index:int -> code_in_cmx;
    used_closure_vars : Var_within_closure.Set.t;
    original_compilation_unit : Compilation_unit.t;
    code_sections_map : int Code_id.Map.t
  }

[@@@ocaml.warning "-37"]

type code_status =
  | Loaded of Code.t
  | Not_loaded of
      { loader : loader;
        code_id : Code_id.t;
        metadata : Code_metadata.t
      }

module Present = struct
  type t =
    | Code_present
    | Metadata_only
end

type raw =
  { metadata : Code_metadata.t;
    present : Present.t
  }

type t =
  | Code_present of { mutable code : code_status }
  | Metadata_only of Code_metadata.t

module View = struct
  type t =
    | Code_present of Code.t
    | Metadata_only of Code_metadata.t
end

let [@ocamlformat "disable"] print ppf t =
  match t with
  | Code_present { code = Loaded code } ->
    Format.fprintf ppf "@[<hov 1>(Code_present@ (@[<hov 1>(code@ %a)@]))@]"
      Code.print code
  | Code_present { code = Not_loaded not_loaded } ->
    Format.fprintf ppf
      "@[<hov 1>(Present@ (\
         @[<hov 1>(code@ Not_loaded)@]\
         @[<hov 1>(metadata@ %a)@]\
       ))@]"
      Code_metadata.print not_loaded.metadata
  | Metadata_only code_metadata ->
    Format.fprintf ppf "@[<hov 1>(Metadata_only@ (code_metadata@ %a))@]"
      Code_metadata.print code_metadata

let create code = Code_present { code = Loaded code }

let load_code
    { code_sections_map;
      read_flambda_section_from_cmx_file;
      used_closure_vars;
      original_compilation_unit
    } code_id : Code.t =
  match Code_id.Map.find code_id code_sections_map with
  | exception Not_found ->
    Misc.fatal_errorf "Code ID %a not found in code sections map:@ %a"
      Code_id.print code_id
      (Code_id.Map.print Numbers.Int.print)
      code_sections_map
  | index ->
    (* This calls back into [Compilenv]. *)
    let { code; table_data } = read_flambda_section_from_cmx_file ~index in
    let renaming =
      Ids_for_export.Table_data.to_import_renaming table_data ~used_closure_vars
        ~original_compilation_unit
    in
    Code.apply_renaming code renaming

let load_code_if_necessary code =
  match code with
  | Loaded code -> code
  | Not_loaded { loader; code_id; metadata = _ } -> load_code loader code_id

let code_status_metadata = function
  | Loaded code -> Code.code_metadata code
  | Not_loaded { metadata; _ } -> metadata

let merge code_id t1 t2 =
  match t1, t2 with
  | Metadata_only cm1, Metadata_only cm2 ->
    if Code_metadata.approx_equal cm1 cm2
    then Some t1
    else
      Misc.fatal_errorf
        "Code id %a is imported with different code metadata (%a and %a)"
        Code_id.print code_id Code_metadata.print cm1 Code_metadata.print cm2
  | Code_present _, Code_present _ ->
    Misc.fatal_errorf "Cannot merge two definitions for code id %a"
      Code_id.print code_id
  | Metadata_only cm_imported, (Code_present { code } as t)
  | (Code_present { code } as t), Metadata_only cm_imported ->
    let cm_present = code_status_metadata code in
    if Code_metadata.approx_equal cm_present cm_imported
    then Some t
    else
      Misc.fatal_errorf
        "Code_id %a is present with code metadata@ %abut imported with code \
         metadata@ %a"
        Code_id.print code_id Code_metadata.print cm_present Code_metadata.print
        cm_imported

let free_names t =
  match t with
  | Code_present present ->
    let code = load_code_if_necessary present.code in
    present.code <- Loaded code;
    Code.free_names code
  | Metadata_only code_metadata -> Code_metadata.free_names code_metadata

let apply_renaming t renaming =
  match t with
  | Code_present present ->
    (* XXX In the original patch apply renaming does nothing on not loaded code
       Is that ok ? Why (parce qu'il n'y a pas de noms en commun ?) ? Qu'en
       est-t'il des metadata ? *)
    let code = load_code_if_necessary present.code in
    present.code <- Loaded code;
    let code = Code.apply_renaming code renaming in
    Code_present { code = Loaded code }
  | Metadata_only code_metadata ->
    let code_metadata = Code_metadata.apply_renaming code_metadata renaming in
    Metadata_only code_metadata

let all_ids_for_export t =
  match t with
  | Code_present present ->
    let code = load_code_if_necessary present.code in
    present.code <- Loaded code;
    Code.all_ids_for_export code
  | Metadata_only code_metadata ->
    Code_metadata.all_ids_for_export code_metadata

let code_metadata t =
  match t with
  | Code_present { code } -> code_status_metadata code
  | Metadata_only code_metadata -> code_metadata

let remember_only_metadata t =
  match t with
  | Code_present { code } -> Metadata_only (code_status_metadata code)
  | Metadata_only _ -> t

let iter_code t ~f =
  match t with
  | Code_present { code } ->
    let code = load_code_if_necessary code in
    f code
  | Metadata_only _ -> ()

let fold_code_for_cmx t ~init ~f =
  match t with
  | Code_present { code } ->
    let code = load_code_if_necessary code in
    let table_data =
      Code.all_ids_for_export code |> Ids_for_export.Table_data.create
    in
    let code_in_cmx = { code; table_data } in
    f init code_in_cmx
  | Metadata_only _ -> init

let map_result_types t ~f =
  match t with
  | Code_present { code = Not_loaded not_loaded } ->
    Code_present
      { code =
          Not_loaded
            { not_loaded with
              metadata = Code_metadata.map_result_types not_loaded.metadata ~f
            }
      }
  | Code_present { code = Loaded code } ->
    Code_present { code = Loaded (Code.map_result_types code ~f) }
  | Metadata_only code_metadata ->
    Metadata_only (Code_metadata.map_result_types code_metadata ~f)

let code_present t =
  match t with Code_present _ -> true | Metadata_only _ -> false

let view (t : t) : View.t =
  match t with
  | Code_present present ->
    let code = load_code_if_necessary present.code in
    present.code <- Loaded code;
    Code_present code
  | Metadata_only code_metadata -> Metadata_only code_metadata

let prepare_for_cmx_header_section t : raw =
  match t with
  | Code_present present ->
    let metadata = code_status_metadata present.code in
    { metadata; present = Code_present }
  | Metadata_only metadata -> { metadata; present = Metadata_only }

let associate_with_loaded_cmx_file { metadata; present } code_id loader =
  match present with
  | Code_present ->
    Code_present { code = Not_loaded { loader; code_id; metadata } }
  | Metadata_only -> Metadata_only metadata
