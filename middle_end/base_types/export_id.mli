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

include Ext_types.UnitId with module Compilation_unit := Compilation_unit
include Ext_types.Identifiable with type t := t

val get_compilation_unit : t -> Compilation_unit.t

val partition_map_by_compilation_unit
   : 'a Map.t
  -> 'a Map.t Compilation_unit.Map.t
