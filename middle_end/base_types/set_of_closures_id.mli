(**************************************************************************)
(*                                                                        *)
(*                                OCaml                                   *)
(*                                                                        *)
(*                       Pierre Chambart, OCamlPro                        *)
(*                  Mark Shinwell, Jane Street Europe                     *)
(*                                                                        *)
(*   Copyright 2015 Institut National de Recherche en Informatique et     *)
(*   en Automatique.  All rights reserved.  This file is distributed      *)
(*   under the terms of the Q Public License version 1.0.                 *)
(*                                                                        *)
(**************************************************************************)

(** An identifier, unique across the whole program, that identifies a set
    of a closures (viz. [Set_of_closures]). *)

include Ext_types.Identifiable

val create : ?name:string -> Compilation_unit.t -> t
val get_compilation_unit : t -> Compilation_unit.t

val partition_set_by_compilation_unit
   : Set.t
  -> Set.t Compilation_unit.Map.t

val partition_map_by_compilation_unit
   : 'a Map.t
  -> 'a Map.t Compilation_unit.Map.t
