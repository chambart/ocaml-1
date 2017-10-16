(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                       Pierre Chambart, OCamlPro                        *)
(*           Mark Shinwell and Leo White, Jane Street Europe              *)
(*                                                                        *)
(*   Copyright 2013--2016 OCamlPro SAS                                    *)
(*   Copyright 2014--2016 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

[@@@ocaml.warning "+a-4-9-30-40-41-42"]

(** Turn free variables of closures into specialised arguments.
    The aim is to cause the closure to become closed. *)

val rewrite_set_of_closures
   : env:Simplify_env.t
  (* CR-soon mshinwell: eliminate superfluous parameter *)
  -> duplicate_function:(
       env:Simplify_env.t
    -> set_of_closures:Flambda.Set_of_closures.t
    -> closure_id:Closure_id.t
    -> new_closure_id:Closure_id.t
    -> Flambda.Function_declaration.t)
  -> set_of_closures:Flambda.Set_of_closures.t
  -> ((Variable.t * Flambda.Named.t) list
    * Flambda.Set_of_closures.t * Inlining_cost.Benefit.t) option
