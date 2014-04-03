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
open Symbol


(** *)

module Fident : sig

  type t

  val create : current_compilation_unit:compilation_unit -> string ->  t
  val wrap_ident : current_compilation_unit:compilation_unit -> Ident.t -> t

  val unwrap : t -> Ident.t (* For bytecode debugger only *)
  val unique_ident : t -> Ident.t (* For clambdagen only *)
    (* Should we propagate Fident.t into clamba ??? *)

  val rename : current_compilation_unit:compilation_unit -> t -> t

  val in_compilation_unit : compilation_unit -> t -> bool

  include PrintableHashOrdered with type t := t

  val to_string : t -> string
  val unique_name : t -> string

end

module FidentSet : sig
  include ExtSet with module M := Fident
  val of_ident_set :
    current_compilation_unit:compilation_unit -> Lambda.IdentSet.t -> t
end
module FidentMap : ExtMap with module M := Fident
module FidentTbl : ExtHashtbl with module M := Fident

module IdentMap : ExtMap with module M := Ident


(** *)

module Closure_function : sig

  type t

  val wrap : Fident.t -> t
  val unwrap : t -> Fident.t

  val in_compilation_unit : compilation_unit -> t -> bool
  val get_compilation_unit : t -> compilation_unit

  include PrintableHashOrdered with type t := t

  val unique_name : t -> string

end

type function_within_closure = Closure_function.t

module ClosureFunctionSet : ExtSet with module M := Closure_function
module ClosureFunctionMap : ExtMap with module M := Closure_function
module ClosureFunctionTbl : ExtHashtbl with module M := Closure_function


(** *)

module Closure_variable : sig

  type t

  val wrap : Fident.t -> t
  val unwrap : t -> Fident.t

  val in_compilation_unit : compilation_unit -> t -> bool

  include PrintableHashOrdered with type t := t

  val unique_name : t -> string

end

type variable_within_closure = Closure_variable.t


module ClosureVariableSet : ExtSet with module M := Closure_variable
module ClosureVariableMap : ExtMap with module M := Closure_variable
module ClosureVariableTbl : ExtHashtbl with module M := Closure_variable


(** *)

module ExprId : Id
module FunId : UnitId with module Compilation_unit := Compilation_unit

module ExprSet : ExtSet with module M := ExprId
module ExprMap : ExtMap with module M := ExprId
module ExprTbl : ExtHashtbl with module M := ExprId

module FunSet : ExtSet with module M := FunId
module FunMap : ExtMap with module M := FunId
module FunTbl : ExtHashtbl with module M := FunId


(** *)

module Static_exception : sig

  type t

  val create : unit -> t

  val of_int : int -> t
  val to_int : t -> int

  include PrintableHashOrdered with type t := t

end

type static_exception = Static_exception.t

module StaticExceptionSet : ExtSet with module M := Static_exception
module StaticExceptionMap : ExtMap with module M := Static_exception
module StaticExceptionTbl : ExtHashtbl with module M := Static_exception

(**/**)

module Fident_connected_components :
  Sort_connected_components.S with module Id := Fident
