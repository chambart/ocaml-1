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

module Env = Closure_conversion_aux.Env
module Function_decls = Closure_conversion_aux.Function_decls
module Function_decl = Function_decls.Function_decl
module IdentSet = Lambda.IdentSet

type t = {
  current_unit_id : Ident.t;
  symbol_for_global' : (Ident.t -> Symbol.t);
  filename : string;
  mutable imported_symbols : Symbol.Set.t;
  mutable declared_symbols : (Symbol.t * Flambda.constant_defining_value) list;
}

(** Generate a wrapper ("stub") function that accepts a tuple argument and
    calls another function with arguments extracted in the obvious
    manner from the tuple. *)
let tupled_function_call_stub original_params unboxed_version
      : Flambda.function_declaration =
  let continuation_param = Continuation.create () in
  let tuple_param =
    Variable.rename ~append:"tupled_stub_param" unboxed_version
  in
  let params = List.map (fun p -> Variable.rename p) original_params in
  let call : Flambda.t =
    Apply ({
        kind = Function;
        continuation = continuation_param;
        func = unboxed_version;
        args = params;
        (* CR-someday mshinwell for mshinwell: investigate if there is some
           redundancy here (func is also unboxed_version) *)
        call_kind = Direct (Closure_id.wrap unboxed_version);
        dbg = Debuginfo.none;
        inline = Default_inline;
        specialise = Default_specialise;
      })
  in
  let _, body =
    List.fold_left (fun (pos, body) param ->
        let lam : Flambda.named =
          Prim (Pfield pos, [tuple_param], Debuginfo.none)
        in
        pos + 1, Flambda.create_let param lam body)
      (0, call) params
  in
  Flambda.create_function_declaration ~params:[tuple_param] ~continuation_param
    ~body ~stub:true ~dbg:Debuginfo.none ~inline:Default_inline
    ~specialise:Default_specialise ~is_a_functor:false

let register_const t (constant:Flambda.constant_defining_value) name
      : Flambda.constant_defining_value_block_field * string =
  let current_compilation_unit = Compilation_unit.get_current_exn () in
  (* Create a variable to ensure uniqueness of the symbol *)
  let var = Variable.create ~current_compilation_unit name in
  let symbol =
    Symbol.create current_compilation_unit
      (Linkage_name.create (Variable.unique_name var))
  in
  t.declared_symbols <- (symbol, constant) :: t.declared_symbols;
  Symbol symbol, name

let rec declare_const t (const : Lambda.structured_constant)
      : Flambda.constant_defining_value_block_field * string =
  match const with
  | Const_base (Const_int c) -> Const (Int c), "int"
  | Const_base (Const_char c) -> Const (Char c), "char"
  | Const_base (Const_string (s, _)) ->
    let const, name =
      if Config.safe_string then
        Flambda.Allocated_const (Immutable_string s), "immstring"
      else Flambda.Allocated_const (String s), "string"
    in
    register_const t const name
  | Const_base (Const_float c) ->
    register_const t
      (Allocated_const (Float (float_of_string c)))
      "float"
  | Const_base (Const_int32 c) ->
    register_const t (Allocated_const (Int32 c)) "int32"
  | Const_base (Const_int64 c) ->
    register_const t (Allocated_const (Int64 c)) "int64"
  | Const_base (Const_nativeint c) ->
    register_const t (Allocated_const (Nativeint c)) "nativeint"
  | Const_pointer c -> Const (Const_pointer c), "pointer"
  | Const_immstring c ->
    register_const t (Allocated_const (Immutable_string c)) "immstring"
  | Const_float_array c ->
    register_const t
      (Allocated_const (Immutable_float_array (List.map float_of_string c)))
      "float_array"
  | Const_block (tag, consts) ->
    let const : Flambda.constant_defining_value =
      Block (Tag.create_exn tag,
             List.map (fun c -> fst (declare_const t c)) consts)
    in
    register_const t const "const_block"

let close_const t (const : Lambda.structured_constant)
      : Flambda.named * string =
  match declare_const t const with
  | Const c, name ->
    Const c, name
  | Symbol s, name ->
    Symbol s, name

let rec close t env (lam : Ilambda.t) : Flambda.t =
  match lam with
  | Let (id, defining_expr, body) ->
    let body_env, var = Env.add_var_like env id in
    let defining_expr = close_named t env defining_expr in
    let body = close t body_env body in
    Flambda.create_let var defining_expr body
  | Let_mutable { id; initial_value; contents_kind; body; } ->
    (* See comment on [Pread_mutable] below. *)
    let var = Mutable_variable.of_ident id in
    let initial_value = Env.find_var env initial_value in
    let body = close t (Env.add_mutable_var env id var) body in
    Let_mutable {
      var;
      initial_value;
      body;
      contents_kind;
    }
  | Let_rec (defs, body) ->
    let env =
      List.fold_right (fun (id,  _) env ->
          let env, _var = Env.add_var_like env id in
          env)
        defs env
    in
    let function_declarations =
      (* Functions will be named after the corresponding identifier in the
         [let rec]. *)
      List.map (function
          | (let_rec_ident,
              ({ kind; continuation_param; params; body; attr; loc; stub;
                free_idents_of_body; } : Ilambda.function_declaration)) ->
            let closure_bound_var =
              Variable.create_with_same_name_as_ident let_rec_ident
            in
            let function_declaration =
              Function_decl.create ~let_rec_ident:(Some let_rec_ident)
                ~closure_bound_var ~kind ~params ~continuation_param ~body
                ~inline:attr.inline ~specialise:attr.specialise
                ~is_a_functor:attr.is_a_functor ~loc ~free_idents_of_body
                ~stub
            in
            function_declaration)
        defs
    in
    (* We eliminate the [let rec] construction, instead producing a normal
       [Let] that binds a set of closures containing all of the functions.
       ([let rec] on non-functions was removed in [Prepare_lambda].)
    *)
    let name =
      (* The Microsoft assembler has a 247-character limit on symbol
          names, so we keep them shorter to try not to hit this. *)
      if Sys.win32 then begin
        match defs with
        | (id, _)::_ -> (Ident.unique_name id) ^ "_let_rec"
        | _ -> "let_rec"
      end else begin
        String.concat "_and_"
          (List.map (fun (id, _) -> Ident.unique_name id) defs)
      end
    in
    let set_of_closures_var = Variable.create name in
    let set_of_closures =
      close_functions t env (Function_decls.create function_declarations)
    in
    let body =
      List.fold_left (fun body decl ->
          let let_rec_ident = Function_decl.let_rec_ident decl in
          let closure_bound_var = Function_decl.closure_bound_var decl in
          let let_bound_var = Env.find_var env let_rec_ident in
          let closure_id =
            Closure_id.Set.singleton (Closure_id.wrap closure_bound_var)
          in
          (* Inside the body of the [let], each function is referred to by
             a [Project_closure] expression, which projects from the set of
             closures. *)
          (Flambda.create_let let_bound_var
            (Project_closure {
              set_of_closures = set_of_closures_var;
              closure_id;
            })
            body))
        (close t env body) function_declarations
    in
    Flambda.create_let set_of_closures_var set_of_closures body
  | Let_cont let_cont ->
    (* Inline out administrative redexes. *)
    if let_cont.administrative then begin
      assert (let_cont.recursive = Asttypes.Nonrecursive);
      let body_env =
        Env.add_administrative_redex env let_cont.name ~params:let_cont.params
          ~handler:let_cont.handler
      in
      close t body_env let_cont.body
    end else begin
      let handler_env, params = Env.add_vars_like env let_cont.params in
      Let_cont {
        name = let_cont.name;
        body = close t env let_cont.body;
        handler = Handler {
          params;
          recursive = let_cont.recursive;
          handler = close t handler_env let_cont.handler;
        };
      }
    end
  | Apply { kind; func; args; continuation; loc; should_be_tailcall = _;
      inlined; specialised; } ->
    let kind : Flambda.apply_kind =
      match kind with
      | Function -> Function
      | Method { kind; obj; } ->
        Method {
          kind;
          obj = Env.find_var env obj;
        }
    in
    Apply ({
      kind;
      func = Env.find_var env func;
      args = Env.find_vars env args;
      continuation;
      call_kind = Indirect;
      dbg = Debuginfo.from_location loc;
      inline = inlined;
      specialise = specialised;
    })
  | Apply_cont (cont, trap_action, args) ->
    let args = Env.find_vars env args in
    begin match Env.find_administrative_redex env cont with
    | Some (params, handler) when trap_action = None ->
      let handler_env = Env.add_vars env params args in
      close t handler_env handler
    | _ ->
      let trap_action =
        Misc.Stdlib.Option.map (fun (trap_action : Ilambda.trap_action)
                  : Flambda.trap_action ->
            match trap_action with
            | Push { id; exn_handler; } -> Push { id; exn_handler; }
            | Pop id -> Pop id)
          trap_action
      in
      Apply_cont (cont, trap_action, args)
    end
  | Switch (scrutinee, sw) ->
    let zero_to_n = Numbers.Int.zero_to_n in
    Switch (Env.find_var env scrutinee,
      { numconsts = zero_to_n (sw.numconsts - 1);
        consts = sw.consts;
        numblocks = zero_to_n (sw.numblocks - 1);
        blocks = sw.blocks;
        failaction = sw.failaction;
      })
  | Event (ilam, _) -> close t env ilam

and close_named t env (named : Ilambda.named) : Flambda.named =
  match named with
  | Var id ->
    if Ident.is_predef_exn id then begin
      let symbol = t.symbol_for_global' id in 
      t.imported_symbols <- Symbol.Set.add symbol t.imported_symbols;
      Symbol symbol
    end else begin
      Var (Env.find_var env id)
    end
  | Const cst -> fst (close_const t cst)
  | Prim (Pread_mutable id, args, _) ->
    (* All occurrences of mutable variables bound by [Let_mutable] are
       identified by [Prim (Pread_mutable, ...)] in Ilambda. *)
    assert (args = []);
    Read_mutable (Env.find_mutable_var env id)
  | Prim (Pgetglobal id, [], _) when Ident.is_predef_exn id ->
    let symbol = t.symbol_for_global' id in
    t.imported_symbols <- Symbol.Set.add symbol t.imported_symbols;
    Symbol symbol
  | Prim (Pgetglobal id, [], _) ->
    assert (not (Ident.same id t.current_unit_id));
    let symbol = t.symbol_for_global' id in
    t.imported_symbols <- Symbol.Set.add symbol t.imported_symbols;
    Symbol symbol
  | Prim (p, args, loc) ->
    Prim (p, Env.find_vars env args, Debuginfo.from_location loc)
  | Assign { being_assigned; new_value; } ->
    Assign {
      being_assigned = Env.find_mutable_var env being_assigned;
      new_value = Env.find_var env new_value;
    }

(** Perform closure conversion on a set of function declarations, returning a
    set of closures.  (The set will often only contain a single function;
    the only case where it cannot is for "let rec".) *)
and close_functions t external_env function_declarations : Flambda.named =
  let closure_env_without_parameters =
    Function_decls.closure_env_without_parameters
      external_env function_declarations
  in
  let all_free_idents =
    (* Filter out predefined exception identifiers, since they will be
       turned into symbols when we closure-convert the body. *)
    IdentSet.filter (fun ident ->
        not (Ident.is_predef_exn ident))
      (Function_decls.all_free_idents function_declarations)
  in
  let close_one_function map decl =
    let body = Function_decl.body decl in
    let loc = Function_decl.loc decl in
    let dbg = Debuginfo.from_location loc in
    let params = Function_decl.params decl in
    (* Create fresh variables for the elements of the closure (cf.
       the comment on [Function_decl.closure_env_without_parameters], above).
       This induces a renaming on [Function_decl.free_idents]; the results of
       that renaming are stored in [free_variables]. *)
    let closure_env =
      List.fold_right (fun id env ->
          let env, _var = Env.add_var_like env id in
          env)
        params closure_env_without_parameters
    in
    (* If the function is the wrapper for a function with an optional
       argument with a default value, make sure it always gets inlined.
       CR-someday pchambart: eta-expansion wrapper for a primitive are
       not marked as stub but certainly should *)
    let stub = Function_decl.stub decl in
    let params = List.map (Env.find_var closure_env) params in
    let closure_bound_var = Function_decl.closure_bound_var decl in
    let body = close t closure_env body in
    let fun_decl =
      Flambda.create_function_declaration ~params
        ~continuation_param:(Function_decl.continuation_param decl)
        ~body ~stub ~dbg
        ~inline:(Function_decl.inline decl)
        ~specialise:(Function_decl.specialise decl)
        ~is_a_functor:(Function_decl.is_a_functor decl)
    in
    match Function_decl.kind decl with
    | Curried -> Variable.Map.add closure_bound_var fun_decl map
    | Tupled ->
      let unboxed_version = Variable.rename closure_bound_var in
      let generic_function_stub =
        tupled_function_call_stub params unboxed_version
      in
      Variable.Map.add unboxed_version fun_decl
        (Variable.Map.add closure_bound_var generic_function_stub map)
  in
  let function_decls =
    Flambda.create_function_declarations
      ~funs:
        (List.fold_left close_one_function Variable.Map.empty
          (Function_decls.to_list function_declarations))
  in
  (* The closed representation of a set of functions is a "set of closures".
     (For avoidance of doubt, the runtime representation of the *whole set* is
     a single block with tag [Closure_tag].) *)
  let set_of_closures =
    let free_vars =
      IdentSet.fold (fun var map ->
          let internal_var =
            Env.find_var closure_env_without_parameters var
          in
          let external_var : Flambda.specialised_to =
            { var = Env.find_var external_env var;
              projection = None;
            }
          in
          Variable.Map.add internal_var external_var map)
        all_free_idents Variable.Map.empty
    in
    Flambda.create_set_of_closures ~function_decls ~free_vars
      ~specialised_args:Variable.Map.empty
      ~direct_call_surrogates:Variable.Map.empty
  in
  Set_of_closures set_of_closures

let ilambda_to_flambda ~backend ~module_ident ~size ~filename
      (ilam, ilam_result_cont) : Flambda.program =
  let module Backend = (val backend : Backend_intf.S) in
  let compilation_unit = Compilation_unit.get_current_exn () in
  let t =
    { current_unit_id = Compilation_unit.get_persistent_ident compilation_unit;
      symbol_for_global' = Backend.symbol_for_global';
      filename;
      imported_symbols = Symbol.Set.empty;
      declared_symbols = [];
    }
  in
  let module_symbol = Backend.symbol_for_global' module_ident in
  let block_symbol =
    let linkage_name = Linkage_name.create "module_as_block" in
    Symbol.create compilation_unit linkage_name
  in
  (* The global module block is built by accessing the fields of all the
     introduced symbols. *)
  (* CR-soon mshinwell for mshinwell: Add a comment describing how modules are
     compiled. *)
  let fields =
    Array.init size (fun pos ->
      let pos_str = string_of_int pos in
      let sym_v = Variable.create ("block_symbol_" ^ pos_str) in
      let result_v = Variable.create ("block_symbol_get_" ^ pos_str) in
      let value_v = Variable.create ("block_symbol_get_field_" ^ pos_str) in
      let continuation = Continuation.create () in
      let flam =
        Flambda.create_let
          sym_v (Symbol block_symbol)
          (Flambda.create_let result_v
              (Prim (Pfield 0, [sym_v], Debuginfo.none))
              (Flambda.create_let value_v
                (Prim (Pfield pos, [result_v], Debuginfo.none))
                (Apply_cont (continuation, None, [value_v]))))
      in
      flam, continuation)
  in
  let module_initializer : Flambda.program_body =
    Initialize_symbol (
      block_symbol,
      Tag.create_exn 0,
      [close t Env.empty ilam, ilam_result_cont],
      Initialize_symbol (
        module_symbol,
        Tag.create_exn 0,
        Array.to_list fields,
        End module_symbol))
  in
  let program_body =
    List.fold_left
      (fun program_body (symbol, constant) : Flambda.program_body ->
         Let_symbol (symbol, constant, program_body))
      module_initializer
      t.declared_symbols
  in
  { imported_symbols = t.imported_symbols;
    program_body;
  }
