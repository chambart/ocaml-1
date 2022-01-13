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

type code_in_cmx

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

type t

module View : sig
  type t = private
    | Code_present of Code.t
    | Metadata_only of Code_metadata.t
end

val print : Format.formatter -> t -> unit

val merge : Code_id.t -> t -> t -> t option

val create : Code.t -> t

val remember_only_metadata : t -> t

val iter_code : t -> f:(Code.t -> unit) -> unit

val map_result_types : t -> f:(Flambda2_types.t -> Flambda2_types.t) -> t

val fold_code_for_cmx : t -> init:'a -> f:('a -> code_in_cmx -> 'a) -> 'a

val code_metadata : t -> Code_metadata.t

val code_present : t -> bool

val view : t -> View.t

val prepare_for_cmx_header_section : t -> t

val associate_with_loaded_cmx_file : t -> Code_id.t -> loader -> t

(** As for [Code_metadata], the free names of a value of type [t] do not include
    the code ID, which is only kept for convenience. *)
include Contains_names.S with type t := t

include Contains_ids.S with type t := t
