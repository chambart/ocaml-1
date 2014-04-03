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

open Abstract_identifiers
open Flambda

val apply_on_subexpressions : ('a flambda -> unit) ->
  'a flambda -> unit

val iter : ('a flambda -> unit) -> 'a flambda -> unit

val iter_toplevel : ('a flambda -> unit) -> 'a flambda -> unit
(** [iter_toplevel f t] Apply f on every toplevel subexpression of t,
    i.e. does not apply it on functions body *)

val iter_on_closures :
  ('a fclosure -> 'a -> unit) -> 'a flambda -> unit

val map : ('a flambda -> 'a flambda) ->
  'a flambda -> 'a flambda

val map_toplevel : ('a flambda -> 'a flambda) ->
  'a flambda -> 'a flambda

val free_variables : 'a flambda -> FidentSet.t

val map_data : ('a -> 'b) -> 'a flambda -> 'b flambda

val toplevel_substitution : Fident.t FidentMap.t ->
  'a flambda -> 'a flambda
