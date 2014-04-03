(***********************************************************************)
(*                                                                     *)
(*                                OCaml                                *)
(*                                                                     *)
(*                     Pierre Chambart, OCamlPro                       *)
(*                                                                     *)
(*  Copyright 2014 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the Q Public License version 1.0.               *)
(*                                                                     *)
(***********************************************************************)

open Ext_types

(** Un nom dans l'assembleur généré
    (en particulier il contient le préfixe -for-pack...) *)

type linkage_name
val linkage_name : string -> linkage_name
val string_of_linkage_name : linkage_name -> string

(** ... *)

type compilation_unit

module Compilation_unit : sig

  val create : string -> linkage_name -> compilation_unit

  val get_persistent_ident : compilation_unit -> Ident.t
  val get_linkage_name : compilation_unit -> linkage_name

  include PrintableHashOrdered with type t = compilation_unit

end

module CompilationUnitSet : ExtSet with module M := Compilation_unit
module CompilationUnitMap : ExtMap with module M := Compilation_unit
module CompilationUnitTbl : ExtHashtbl with module M := Compilation_unit


(** A symbol is an identifier of a constant provided by another
    compilation unit or of top level module.
    [sym_unit] is the compilation unit containing the value.
    [sym_lablel] is the linking name of the variable.
    The label must be globaly unique: two compilation units linked
    in the same program must not share labels *)

type t = { sym_unit : compilation_unit; sym_label : linkage_name }

module Printers : PrintableHashOrdered with type t = t

include (PrintableHashOrdered with type t := t)

module SymbolSet : ExtSet with module M := Printers
module SymbolMap : ExtMap with module M := Printers
module SymbolTbl : ExtHashtbl with module M := Printers
