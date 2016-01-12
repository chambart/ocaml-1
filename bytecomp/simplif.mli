(***********************************************************************)
(*                                                                     *)
(*                                OCaml                                *)
(*                                                                     *)
(*            Xavier Leroy, projet Cristal, INRIA Rocquencourt         *)
(*                                                                     *)
(*  Copyright 1996 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the Q Public License version 1.0.               *)
(*                                                                     *)
(***********************************************************************)

(* Elimination of useless Llet(Alias) bindings.
   Transformation of let-bound references into variables.
   Simplification over staticraise/staticcatch constructs.
   Generation of tail-call annotations if -annot is set. *)

open Lambda

val simplify_lambda: lambda -> lambda

val map: (lambda -> lambda) -> lambda -> lambda

val split_default_wrapper
   : ?create_wrapper_body:(lambda -> lambda)
  -> Ident.t
  -> function_kind
  -> Ident.t list
  -> lambda
  -> function_attribute
  -> (Ident.t * lambda) list

(* To be filled by asmcomp/selectgen.ml *)
val is_tail_native_heuristic: (int -> bool) ref
                          (* # arguments -> can tailcall *)
