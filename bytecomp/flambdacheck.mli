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

open Symbol
open Abstract_identifiers
open Flambda


val check :
  current_compilation_unit:compilation_unit -> ?sym:bool -> 'a flambda -> unit
(** Run all tests, raises Fatal_error if a test fails *)

type 'a counter_example =
  | No_counter_example
  | Counter_example of 'a

val every_used_identifier_is_bound :
  'a flambda -> Variable.t counter_example

val function_free_variables_are_bound_in_the_closure_and_parameters :
  'a flambda -> VarSet.t counter_example

val no_identifier_bound_multiple_times :
  'a flambda -> Variable.t counter_example

val every_bound_variable_is_from_current_compilation_unit :
  current_compilation_unit:compilation_unit -> 'a flambda ->
  Variable.t counter_example

val no_assign_on_variable_of_kind_Not_assigned :
  'a flambda -> Variable.t counter_example

val no_variable_within_closure_is_bound_multiple_times :
  'a flambda -> variable_within_closure counter_example

val no_function_within_closure_is_bound_multiple_times :
  'a flambda -> function_within_closure counter_example

val every_declared_closure_is_from_current_compilation_unit :
  current_compilation_unit:compilation_unit -> 'a flambda ->
  compilation_unit counter_example

val every_used_function_from_current_compilation_unit_is_declared :
  current_compilation_unit:compilation_unit -> 'a flambda ->
  ClosureFunctionSet.t counter_example

val every_used_variable_in_closure_from_current_compilation_unit_is_declared :
  current_compilation_unit:compilation_unit -> 'a flambda ->
  ClosureVariableSet.t counter_example

val every_static_exception_is_caught :
  'a flambda -> static_exception counter_example

val every_static_exception_is_caught_at_a_single_position :
  'a flambda -> static_exception counter_example
