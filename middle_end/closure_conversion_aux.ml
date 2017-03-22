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

module IdentSet = Lambda.IdentSet

module Env = struct

  type variable_access =
    | Project_var of Var_within_closure.t
    | Move_within_set_of_closures of Closure_id.t
    | Variable of Variable.t

  type t = {
    variables : variable_access Ident.tbl;
    mutable_variables : Mutable_variable.t Ident.tbl;
    static_exceptions : Static_exception.t Numbers.Int.Map.t;
    globals : Symbol.t Numbers.Int.Map.t;
    current_closure : (Variable.t * Closure_id.t * Set_of_closures_id.t) option;
    at_toplevel : bool;
  }

  let empty = {
    variables = Ident.empty;
    mutable_variables = Ident.empty;
    static_exceptions = Numbers.Int.Map.empty;
    globals = Numbers.Int.Map.empty;
    current_closure = None;
    at_toplevel = true;
  }

  let clear_local_bindings env =
    { empty with globals = env.globals }

  let add_var t id var =
    { t with variables = Ident.add id (Variable var) t.variables }
  let add_vars t ids vars = List.fold_left2 add_var t ids vars

  let add_var_from_current_closure t id var =
    let variables =
      Ident.add id (Project_var var) t.variables
    in
    { t with variables }

  let add_closure_from_current_set t id closure_id =
    let variables =
      Ident.add id (Move_within_set_of_closures closure_id) t.variables
    in
    { t with variables }

  let find_var t id =
    try Ident.find_same id t.variables
    with Not_found ->
      Misc.fatal_errorf "Closure_conversion.Env.find_var: %s@ %s"
        (Ident.unique_name id)
        (Printexc.raw_backtrace_to_string (Printexc.get_callstack 42))

  let find_var_exn t id =
    Ident.find_same id t.variables

  let add_mutable_var t id mutable_var =
    { t with mutable_variables = Ident.add id mutable_var t.mutable_variables }

  let find_mutable_var_exn t id =
    Ident.find_same id t.mutable_variables

  let set_current_closure t var closure_id set_of_closures_id =
    { t with current_closure = Some (var, closure_id, set_of_closures_id) }

  let current_closure t =
    match t.current_closure with
    | None ->
      Misc.fatal_errorf "Closure_conversion.Env.current_closure_variable"
    | Some var ->
      var

  let add_static_exception t st_exn fresh_st_exn =
    { t with
      static_exceptions =
        Numbers.Int.Map.add st_exn fresh_st_exn t.static_exceptions }

  let find_static_exception t st_exn =
    try Numbers.Int.Map.find st_exn t.static_exceptions
    with Not_found ->
      Misc.fatal_error ("Closure_conversion.Env.find_static_exception: exn "
        ^ string_of_int st_exn)

  let add_global t pos symbol =
    { t with globals = Numbers.Int.Map.add pos symbol t.globals }

  let find_global t pos =
    try Numbers.Int.Map.find pos t.globals
    with Not_found ->
      Misc.fatal_error ("Closure_conversion.Env.find_global: global "
        ^ string_of_int pos)

  let at_toplevel t = t.at_toplevel

  let not_at_toplevel t = { t with at_toplevel = false; }
end

module Function_decls = struct
  module Function_decl = struct
    type t = {
      let_rec_ident : Ident.t;
      closure_id : Closure_id.t;
      closure_bound_var : Variable.t;
      kind : Lambda.function_kind;
      params : Ident.t list;
      body : Lambda.lambda;
      free_idents_of_body : IdentSet.t;
      attr : Lambda.function_attribute;
      loc : Location.t;
    }

    let create ~let_rec_ident ~closure_bound_var ~kind ~params ~body
        ~attr ~loc =
      let let_rec_ident =
        match let_rec_ident with
        | None -> Ident.create "unnamed_function"
        | Some let_rec_ident -> let_rec_ident
      in
      { let_rec_ident;
        closure_id = Closure_id.wrap closure_bound_var;
        closure_bound_var;
        kind;
        params;
        body;
        free_idents_of_body = Lambda.free_variables body;
        attr;
        loc;
      }

    let let_rec_ident t = t.let_rec_ident
    let closure_bound_var t = t.closure_bound_var
    let closure_id t = t.closure_id
    let kind t = t.kind
    let params t = t.params
    let body t = t.body
    let free_idents t = t.free_idents_of_body
    let inline t = t.attr.inline
    let specialise t = t.attr.specialise
    let is_a_functor t = t.attr.is_a_functor
    let stub t = t.attr.stub
    let loc t = t.loc

  end

  type t = {
    function_decls : Function_decl.t list;
    all_free_idents : IdentSet.t;
  }

  (* All identifiers free in the bodies of the given function declarations,
     indexed by the identifiers corresponding to the functions themselves. *)
  let free_idents_by_function function_decls =
    List.fold_right (fun decl map ->
        Variable.Map.add (Function_decl.closure_bound_var decl)
          (Function_decl.free_idents decl) map)
      function_decls Variable.Map.empty

  let all_free_idents function_decls =
    Variable.Map.fold (fun _ -> IdentSet.union)
      (free_idents_by_function function_decls) IdentSet.empty

  (* All identifiers of simultaneously-defined functions in [ts]. *)
  let let_rec_idents function_decls =
    List.map Function_decl.let_rec_ident function_decls

  (* All parameters of functions in [ts]. *)
  let all_params function_decls =
    List.concat (List.map Function_decl.params function_decls)

  let set_diff (from : IdentSet.t) (idents : Ident.t list) =
    List.fold_right IdentSet.remove idents from

  (* CR-someday lwhite: use a different name from above or explain the
     difference *)
  let all_free_idents function_decls =
    set_diff (set_diff (all_free_idents function_decls)
        (all_params function_decls))
      (let_rec_idents function_decls)

  let create function_decls =
    { function_decls;
      all_free_idents = all_free_idents function_decls;
    }

  let to_list t = t.function_decls

  let all_free_idents t = t.all_free_idents

  let closure_env_without_parameters_and_functions external_env t =
    let closure_env = Env.clear_local_bindings external_env in
    (* For free variables. *)
    IdentSet.fold (fun id (env, local_env) ->
        let variable =
          Var_within_closure.wrap (Variable.create (Ident.name id))
        in
        Env.add_var_from_current_closure env id variable,
        Ident.add id variable local_env)
      t.all_free_idents (closure_env, Ident.empty)

  let add_let_rec_bound_functions_to_env env decl t =
    let open Function_decl in
    List.fold_left (fun env fun_decl ->
        if Closure_id.equal fun_decl.closure_id decl.closure_id then
          Env.add_var env fun_decl.let_rec_ident fun_decl.closure_bound_var
        else
          Env.add_closure_from_current_set env fun_decl.let_rec_ident
            fun_decl.closure_id)
      env t.function_decls
end
