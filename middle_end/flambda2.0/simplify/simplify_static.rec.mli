(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                       Pierre Chambart, OCamlPro                        *)
(*           Mark Shinwell and Leo White, Jane Street Europe              *)
(*                                                                        *)
(*   Copyright 2013--2019 OCamlPro SAS                                    *)
(*   Copyright 2014--2019 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(** Simplification of toplevel definitions. *)

[@@@ocaml.warning "+a-4-30-40-41-42"]

val simplify_set_of_closures
    : Simplify_env_and_result.Env.t
   -> result_env:Simplify_env_and_result.Env.t
   -> Simplify_env_and_result.Result.t
   -> Flambda.Set_of_closures.t
   -> set_of_closures_symbol:Symbol.t
   -> closure_symbols:Symbol.t Closure_id.Map.t
   -> closure_elements_and_types:
        (Simple.t Var_within_closure.Map.t
          * Flambda_type.ty_value Var_within_closure.Map.t) option
   -> Flambda.Set_of_closures.t * Simplify_env_and_result.Env.t
        * Flambda_type.t * Simplify_env_and_result.Result.t
        * Flambda_type.t Symbol.Map.t
        * Flambda_static.Program_body.Static_structure.t

val simplify_program
   : Simplify_env_and_result.Env.t
  -> Flambda_static.Program.t
  -> Flambda_static.Program.t