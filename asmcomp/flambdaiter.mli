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

val apply_on_subexpressions : ('a Flambda.flambda -> unit) ->
  'a Flambda.flambda -> unit

val iter : ('a Flambda.flambda -> unit) -> 'a Flambda.flambda -> unit

val iter_toplevel : ('a Flambda.flambda -> unit) -> 'a Flambda.flambda -> unit
(** [iter_toplevel f t] Apply f on every toplevel subexpression of t,
    i.e. does not apply it on functions body *)

val iter_on_closures :
  ('a Flambda.closure -> 'a -> unit) -> 'a Flambda.flambda -> unit

val map : ('a Flambda.flambda -> 'a Flambda.flambda) ->
  'a Flambda.flambda -> 'a Flambda.flambda

val map_toplevel : ('a Flambda.flambda -> 'a Flambda.flambda) ->
  'a Flambda.flambda -> 'a Flambda.flambda

val free_variables : 'a Flambda.flambda -> Flambda.VarSet.t
