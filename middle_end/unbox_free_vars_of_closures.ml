(**************************************************************************)
(*                                                                        *)
(*                                OCaml                                   *)
(*                                                                        *)
(*                       Pierre Chambart, OCamlPro                        *)
(*           Mark Shinwell and Leo White, Jane Street Europe              *)
(*                                                                        *)
(*   Copyright 2013--2016 OCamlPro SAS                                    *)
(*   Copyright 2014--2016 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file ../LICENSE.       *)
(*                                                                        *)
(**************************************************************************)

let pass_name = "unbox-free-vars-of-closures"
let () = Pass_wrapper.register ~pass_name

let run ~env ~(set_of_closures : Flambda.set_of_closures) =
  if !Clflags.classic_inlining then
    None
  else
    let funs, projection_defns, free_vars, total_benefit =
      Variable.Map.fold (fun fun_var
            (function_decl : Flambda.function_declaration)
            (funs, projection_defns, additional_free_vars, total_benefit) ->
          if function_decl.stub then
            funs, projection_defns, additional_free_vars, total_benefit
          else
            let extracted =
              Extract_projections.from_function_decl ~env ~function_decl
                ~which_variables:set_of_closures.free_vars
            in
            match extracted with
            | None ->
              funs, projection_defns, additional_free_vars, total_benefit
            | Some extracted ->
              let function_decl =
                Flambda.create_function_declaration
                  ~params:function_decl.params
                  ~body:extracted.new_function_body
                  ~stub:function_decl.stub
                  ~dbg:function_decl.dbg
                  ~inline:function_decl.inline
                  ~is_a_functor:function_decl.is_a_functor
              in
              let funs = Variable.Map.add fun_var function_decl funs in
              let projection_defns =
                projection_defns
                  @ extracted.projection_defns_indexed_by_outer_vars
              in
              let additional_free_vars =
                try
                  Variable.Map.disjoint_union additional_free_vars
                    extracted.new_inner_to_new_outer_vars
                    ~eq:Variable.equal
                with _exn ->
                  Misc.fatal_errorf "Unbox_free_vars_of_closures: non-disjoint \
                      [free_vars] sets: %a vs. %a"
                    (Variable.Map.print Variable.print) additional_free_vars
                    (Variable.Map.print Variable.print)
                      set_of_closures.free_vars
              in
              let total_benefit =
                Inlining_cost.Benefit.(+) total_benefit extracted.benefit
              in
              funs, projection_defns, additional_free_vars, total_benefit)
        set_of_closures.function_decls.funs
        (Variable.Map.empty, [], set_of_closures.free_vars,
          Inlining_cost.Benefit.zero)
    in
    let function_decls =
      Flambda.update_function_declarations set_of_closures.function_decls
        ~funs
    in
    let set_of_closures =
      Flambda.create_set_of_closures ~function_decls ~free_vars
        ~specialised_args:set_of_closures.specialised_args
    in
    let expr =
      List.fold_left (fun expr projection_defns ->
          Variable.Map.fold Flambda.create_let projection_defns expr)
        (Flambda_utils.name_expr (Set_of_closures set_of_closures)
          ~name:"unbox_free_vars_of_closures")
        projection_defns
    in
    Some (expr, total_benefit)

let run ~env ~set_of_closures =
  Pass_wrapper.with_dump ~pass_name ~input:set_of_closures
    ~print_input:Flambda.print_set_of_closures
    ~print_output:(fun ppf (expr, _benefit) -> Flambda.print ppf expr)
    ~f:(fun () -> run ~env ~set_of_closures)
