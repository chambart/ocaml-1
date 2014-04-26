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

(* Passes moving subexpressions up in the tree using staticexception to
   try to eliminate them. The main focused patterns are.

   * multiple variables declared in a tuple deep inside a branch expression:
     the purpose of the transformation is to remove the tuple allocation.

   {[let (a,b) = if c then (1,2) else (3,4) in
     ...
   ]}

   * successive branch expressions:

   {[let v = if c then A (1,2) else B in
     match v with
     | A -> exprA
     | B -> exprB]}

   rewritten to

   {[catch
       if c
       then exit ex1 (1,2)
       else exit ex2
     with
     | ex1 (x,y) ->
       let v = A (x,y) in
       exprA
     | ex2 ->
       let v = B in
       exprB]}

   simplify_static_exceptions_pass is used to clean cases where the
   other passes didn't bring improvements or generated useless catch:

   {[catch
       if c
       then exit ex1 (1,2)
       else exit ex2
     with
     | ex1 (x,y) ->
       let v = A (x,y) in
       exprA
     | ex2 ->
       let v = B in
       exprB]}

   rewritten to

   {[if c
     then
       let v = A (1,2) in
       exprA
     else
       let v = B in
       exprB]}

*)

val if_static_raise_pass : Flambdapasses.pass

val move_in_exn_pass : Flambdapasses.pass

val simplify_static_exceptions_pass : Flambdapasses.pass

val passes : Flambdapasses.pass list
