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

type linkage_name

type static_exception

val linkage_name : string -> linkage_name

module Compilation_unit : sig
  include PrintableHashOrdered
  val create : Ident.t -> linkage_name -> t
end
type compilation_unit = Compilation_unit.t

val predefined_exception_compilation_unit: compilation_unit

type symbol = { sym_unit : compilation_unit; sym_label : linkage_name }
(** A symbol is an identifier of a constant provided by another
    compilation unit or of top level module.
    [sym_unit] is the compilation unit containing the value.
    [sym_lablel] is the linking name of the variable.
    The label must be globaly unique: two compilation units linked
    in the same program must not share labels *)

module Variable : sig
  include PrintableHashOrdered
  val create : compilation_unit:compilation_unit -> Ident.t -> t
  val make : compilation_unit:compilation_unit -> string -> t
  val compilation_unit : t -> compilation_unit
  val rename : compilation_unit:compilation_unit -> t -> t
  val make_ident : t -> Ident.t (* to go back to clambda *)
  val unique_name : t -> string
  val to_string : t -> string
  val to_ident : t -> Ident.t
end
type variable = Variable.t

module Closure_function : sig
  include PrintableHashOrdered
  val create : variable -> t
  val compilation_unit : t -> compilation_unit
  val unique_name : t -> string
  val to_var : t -> variable
end
type function_within_closure = Closure_function.t

module Closure_variable : sig
  include PrintableHashOrdered
  val create : variable -> t
  val compilation_unit : t -> compilation_unit
  val unique_name : t -> string
  val to_var : t -> variable
end
type variable_within_closure = Closure_variable.t

module Symbol : PrintableHashOrdered with type t = symbol

module ExprId : Id
module FunId : UnitId with module Compilation_unit := Compilation_unit

module Static_exception : sig
  include PrintableHashOrdered with type t = static_exception
  val of_int : int -> static_exception
  val to_int : static_exception -> int
  val create : unit -> static_exception
end

module VarSet : sig
  include ExtSet with module M := Variable
  val of_ident_set : compilation_unit:compilation_unit -> Lambda.IdentSet.t -> t
end
module VarMap : ExtMap with module M := Variable
module VarTbl : ExtHashtbl with module M := Variable

module SymbolSet : ExtSet with module M := Symbol
module SymbolMap : ExtMap with module M := Symbol
module SymbolTbl : ExtHashtbl with module M := Symbol

module ExprSet : ExtSet with module M := ExprId
module ExprMap : ExtMap with module M := ExprId
module ExprTbl : ExtHashtbl with module M := ExprId

module FunSet : ExtSet with module M := FunId
module FunMap : ExtMap with module M := FunId
module FunTbl : ExtHashtbl with module M := FunId

module ClosureFunctionSet : ExtSet with module M := Closure_function
module ClosureFunctionMap : ExtMap with module M := Closure_function
module ClosureFunctionTbl : ExtHashtbl with module M := Closure_function

module ClosureVariableSet : ExtSet with module M := Closure_variable
module ClosureVariableMap : ExtMap with module M := Closure_variable
module ClosureVariableTbl : ExtHashtbl with module M := Closure_variable

module StaticExceptionSet : ExtSet with module M := Static_exception
module StaticExceptionMap : ExtMap with module M := Static_exception
module StaticExceptionTbl : ExtHashtbl with module M := Static_exception

module CompilationUnitSet : ExtSet with module M := Compilation_unit
module CompilationUnitMap : ExtMap with module M := Compilation_unit
module CompilationUnitTbl : ExtHashtbl with module M := Compilation_unit

module IdentMap : ExtMap with module M := Ident

(**/**)

module Var_connected_components :
  Sort_connected_components.S with module Id := Variable

(* To be used only in Compilenv. This is declared here to avoid circular dependencies *)

val string_of_linkage_name : linkage_name -> string
val ident_of_compilation_unit : compilation_unit -> Ident.t
val linkage_name_of_compilation_unit : compilation_unit -> linkage_name
val ident_of_function_within_closure : function_within_closure -> Ident.t
