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

(* Pure expressions are expressions that can be:
   * added
   * removed if the result is not used
   * moved before any expression or
     after any expression not using its result
   without altering the semantics *)

open Abstract_identifiers
open Flambda

type env

val pure_expression : env -> 'a flambda -> bool

val pure_expression_toplevel : env -> 'a flambda -> bool
(* Same as [pure_expression] but does traverse local
   function to mark pure ones.
   This function is provided for efficiency reasons: it is faster
   to traverse one time a big expression, mark every pure function
   and use this function later on subexpressions than
   using [pure_expression] *)

val pure_functions : 'a flambda -> ClosureFunctionSet.t

(* Environment building functions *)

val empty_env : env

val mark_pure_functions : ClosureFunctionSet.t -> env -> env

val mark_unasigned_variable : Variable.t -> env -> env
