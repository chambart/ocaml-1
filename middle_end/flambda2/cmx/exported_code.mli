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

type t

include Contains_ids.S with type t := t

val apply_renaming : Code_id.t Code_id.Map.t -> Renaming.t -> t -> t

val print : Format.formatter -> t -> unit

val empty : t

val add_code : keep_code:(Code_id.t -> bool) -> Code.t Code_id.Map.t -> t -> t

val mark_as_imported : t -> t

val merge : t -> t -> t

val mem : Code_id.t -> t -> bool

(** This function raises an exception if the code ID is unbound. *)
val find_exn : t -> Code_id.t -> Code_or_metadata.t

(** This function is only really for use in unusual cases where there needs to
    be special handling if a code ID is unbound (see comment in the .ml file) *)
val find : t -> Code_id.t -> Code_or_metadata.t option

val remove_unreachable : reachable_names:Name_occurrences.t -> t -> t

val remove_unused_closure_vars_from_result_types :
  used_closure_vars:Var_within_closure.Set.t -> t -> t

val iter_code : t -> f:(Code.t -> unit) -> unit

(* val fold
 *    : t
 *   -> init:'a
 *   -> f:('a -> Code_id.t -> Code.t -> 'a)
 *   -> 'a *)

val fold_for_cmx
   : t
  -> init:'a
  -> f:('a -> Code_id.t -> Obj.t -> 'a)
  -> 'a

(** This function must be called _after_ all code from the value of type [t]
    has been marshalled to the .cmx file (e.g. by using [fold]).
    The returned value of type [t] should not be altered before it is
    marshalled to the .cmx file. *)
val prepare_for_cmx_header_section : t -> t

val associate_with_loaded_cmx_file
   : t
  -> read_flambda_section_from_cmx_file:(index:int -> Obj.t)
  -> code_sections_map:int Code_id.Map.t
  -> used_closure_vars:Var_within_closure.Set.t
  -> original_compilation_unit:Compilation_unit.t
  -> t
