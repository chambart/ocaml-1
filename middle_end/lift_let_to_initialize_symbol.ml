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

type ('a, 'b) kind =
  | Initialisation of (Symbol.t * Tag.t * Flambda.t list)
  | Effect of 'b

let should_copy (named:Flambda.named) =
  match named with
  | Symbol _ | Read_symbol_field _ | Const _
  | Prim (Pbox_float, _, _)
  | Prim (Punbox_float, _, _) -> true
  | _ -> false

type var_with_type = Variable.t * Flambda.param_type

let named_return_type (named:Flambda.named) : Flambda.param_type =
  match named with
  | Prim (prim, _, _) when Lambda.returns_unboxed_value prim ->
    Float Unboxed
  | _ ->
    Val

type extracted =
  | Expr of var_with_type * Flambda.t
  | Exprs of var_with_type list * Flambda.t
  | Block of Variable.t * Tag.t * Variable.t list

type accumulated = {
  copied_lets : (Variable.t * Flambda.named) list;
  extracted_lets : extracted list;
  terminator : Flambda.expr;
}

let rec accumulate ~substitution ~copied_lets ~extracted_lets
      (expr : Flambda.t) =
  match expr with
  | Let { var; body = Var var'; _ } | Let_rec ([var, _], Var var')
    when Variable.equal var var' ->
    { copied_lets; extracted_lets;
      terminator = Flambda_utils.toplevel_substitution substitution expr;
    }
  (* If the pattern is what lifting let_rec generates, prevent it from being
     lifted again. *)
  | Let_rec (defs,
             Let { var; body = Var var';
                   defining_expr = Prim (Pmakeblock _, fields, _); })
    when
      Variable.equal var var'
      && List.for_all (fun field ->
          List.exists (fun (def_var, _) -> Variable.equal def_var field) defs)
      fields ->
    { copied_lets; extracted_lets;
      terminator = Flambda_utils.toplevel_substitution substitution expr;
    }
  | Let { var; defining_expr = Expr (Var alias); body; _ }
  | Let_rec ([var, Expr (Var alias)], body) ->
    let alias =
      match Variable.Map.find alias substitution with
      | exception Not_found -> alias
      | original_alias -> original_alias
    in
    accumulate
      ~substitution:(Variable.Map.add var alias substitution)
      ~copied_lets
      ~extracted_lets
      body
  | Let { var; defining_expr = named; body; _ }
  | Let_rec ([var, named], body)
    when should_copy named ->
    let named = Flambda_utils.toplevel_substitution_named substitution named in
      accumulate body
        ~substitution
        ~copied_lets:((var, named)::copied_lets)
        ~extracted_lets
  | Let { var; defining_expr = named; body; _ } ->
    let extracted =
      let renamed = Variable.rename var in
      match named with
      | Prim (Pmakeblock (tag, Asttypes.Immutable, _value_kind), args, _dbg) ->
        let tag = Tag.create_exn tag in
        let args =
          List.map (fun v ->
              try Variable.Map.find v substitution
              with Not_found -> v)
            args
        in
        Block (var, tag, args)
      | named ->
        let expr =
          Flambda_utils.toplevel_substitution substitution
            (Flambda.create_let renamed named (Var renamed))
        in
        let typ = named_return_type named in
        Expr ((var, typ), expr)
    in
    accumulate body
      ~substitution
      ~copied_lets
      ~extracted_lets:(extracted::extracted_lets)
  | Let_rec ([var, named], body) ->
    let renamed = Variable.rename var in
    let def_substitution = Variable.Map.add var renamed substitution in
    let expr =
      Flambda_utils.toplevel_substitution def_substitution
        (Let_rec ([renamed, named], Var renamed))
    in
    let typ = named_return_type named in
    let extracted = Expr ((var, typ), expr) in
    accumulate body
      ~substitution
      ~copied_lets
      ~extracted_lets:(extracted::extracted_lets)
  | Let_rec (defs, body) ->
    let renamed_defs, def_substitution =
      List.fold_right (fun (var, def) (acc, substitution) ->
          let new_var = Variable.rename var in
          (new_var, def) :: acc,
          Variable.Map.add var new_var substitution)
        defs ([], substitution)
    in
    let extracted =
      let fields, box =
        List.fold_right (fun (new_var, def) (fields, box) ->
          match named_return_type def with
          | Val | Float Boxed | Array _ ->
            new_var :: fields, box
          | Float Unboxed ->
            let boxed_var = Variable.rename new_var in
            let box body =
              Flambda.create_let boxed_var
                (Prim (Pbox_float, [new_var], Debuginfo.none))
                (box body)
            in
            boxed_var :: fields, box)
          renamed_defs ([],(fun x -> x))
      in
      let block =
        Flambda_utils.name_expr ~name:"lifted_let_rec_block"
          (Prim (Pmakeblock (0, Immutable, None),
                 fields,
                 Debuginfo.none))
      in
      let expr =
        Flambda_utils.toplevel_substitution def_substitution
          (Let_rec (renamed_defs, box block))
      in
      let defs_with_type =
        List.map (fun (var, def) -> var, named_return_type def) defs
      in
      Exprs (defs_with_type, expr)
    in
    accumulate body
      ~substitution
      ~copied_lets
      ~extracted_lets:(extracted::extracted_lets)
  | _ ->
  { copied_lets;
    extracted_lets;
    terminator = Flambda_utils.toplevel_substitution substitution expr;
  }

let rebuild_expr
    ~(extracted_definitions :
        (Symbol.t * int list * Flambda.param_type) Variable.Map.t)
      ~(copied_definitions : Flambda.named Variable.Map.t)
      ~(substitute : bool)
      (expr : Flambda.t) =
  let expr_with_read_symbols =
    Flambda_utils.substitute_read_symbol_field_for_variables
      extracted_definitions expr
  in
  let free_variables = Flambda.free_variables expr_with_read_symbols in
  let substitution =
    if substitute then
      Variable.Map.of_set (fun x -> Variable.rename x) free_variables
    else
      Variable.Map.of_set (fun x -> x) free_variables
  in
  let expr_with_read_symbols =
    Flambda_utils.toplevel_substitution substitution
      expr_with_read_symbols
  in
  let rec introduce_copied declarations substitution body =
    match declarations with
    | [] -> body
    | (var, declaration) :: declarations ->
      let substitution = Variable.Map.remove var substitution in
      let definition =
        try Variable.Map.find var copied_definitions
        with Not_found ->
          Misc.fatal_errorf "Missing declaration for variable %a"
            Variable.print var
      in
      let declarations, substitution =
        Variable.Set.fold (fun var (declarations, substitution) ->
          if Variable.Map.mem var substitution ||
             Variable.Map.mem var extracted_definitions then
            (declarations, substitution)
          else
            let renamed = Variable.rename var in
            (var, renamed) :: declarations,
            Variable.Map.add var renamed substitution)
          (Flambda.free_variables_named definition)
          (declarations, substitution)
      in
      let definition =
        Flambda_utils.toplevel_substitution_named
          substitution definition
      in
      let body = Flambda.create_let declaration definition body in
      introduce_copied declarations substitution body
  in

  let expr_with_copied =
    introduce_copied
      (Variable.Map.bindings substitution)
      substitution
      expr_with_read_symbols
  in

  (* CR pchambart: really ineficient copied definitions should be
     introduced before read symbols *)

  Flambda_utils.substitute_read_symbol_field_for_variables
    extracted_definitions expr_with_copied


let rebuild (used_variables:Variable.Set.t) (accumulated:accumulated) =
  let copied_definitions = Variable.Map.of_list accumulated.copied_lets in
  let accumulated_extracted_lets =
    List.map (fun decl ->
        match decl with
        | Block (var, _, _) | Expr ((var, _), _) ->
          Flambda_utils.make_variable_symbol var, decl
        | Exprs (vars, _) ->
          let vars = List.map fst vars in
          Flambda_utils.make_variables_symbol vars, decl)
      accumulated.extracted_lets
  in
  let extracted_definitions =
    (* Blocks are lifted to direct top-level Initialize_block:
         accessing the value be done directly through the symbol.
       Other let bound variables are initialized inside a size
       one static block:
         accessing the value is done directly through the field 0
         of the symbol.
       let rec of size more than one is represented as a block of
       all the bound variables allocated inside a size one static
       block:
         accessing the value is done directly through the right
         field of the field 0 of the symbol. *)
    List.fold_left (fun map (symbol, decl) ->
        match decl with
        | Block (var, _tag, _fields) ->
          Variable.Map.add var (symbol, [], Flambda.Val) map
        | Expr ((var, typ), _expr) ->
          Variable.Map.add var (symbol, [0], typ) map
        | Exprs (vars, _expr) ->
          let map, _ =
            List.fold_left (fun (map, field) (var, typ) ->
                Variable.Map.add var (symbol, [field; 0], typ) map,
                field + 1)
              (map, 0) vars
          in
          map)
      Variable.Map.empty accumulated_extracted_lets
  in
  let extracted =
    List.map (fun (symbol, decl) ->
        match decl with
        | Expr ((var, typ), decl) ->
          let expr =
            rebuild_expr ~extracted_definitions ~copied_definitions
              ~substitute:true decl
          in
          let expr =
            match typ with
            | Val | Float Boxed | Array _ ->
              expr
            | Float Unboxed ->
              let unboxed = Variable.rename var in
              let boxed = Variable.create "boxed" in
              Flambda.create_let unboxed (Expr expr)
                (Flambda.create_let boxed
                   (Prim (Pbox_float, [unboxed], Debuginfo.none))
                   (Var boxed))
          in
          if Variable.Set.mem var used_variables then
            Initialisation
              (symbol,
               Tag.create_exn 0,
               [expr])
          else
            Effect expr
        | Exprs (_vars, decl) ->
          let expr =
            rebuild_expr ~extracted_definitions ~copied_definitions
              ~substitute:true decl
          in
          Initialisation (symbol, Tag.create_exn 0, [expr])
        | Block (_var, tag, fields) ->
          let fields =
            List.map (fun var ->
                rebuild_expr ~extracted_definitions ~copied_definitions
                  ~substitute:true (Var var))
              fields
          in
          Initialisation (symbol, tag, fields))
      accumulated_extracted_lets
  in
  let terminator =
    (* We don't need to substitute the variables in the terminator, we
       suppose that we did for every other occurrence.  Avoiding this
       substitution allows this transformation to be idempotent. *)
    rebuild_expr ~extracted_definitions ~copied_definitions
      ~substitute:false accumulated.terminator
  in
  List.rev extracted, terminator

let introduce_symbols expr =
  let accumulated =
    accumulate expr
      ~substitution:Variable.Map.empty
      ~copied_lets:[] ~extracted_lets:[]
  in
  let used_variables = Flambda.used_variables expr in
  let extracted, terminator = rebuild used_variables accumulated in
  extracted, terminator

let add_extracted introduced program =
  List.fold_right (fun extracted program ->
      match extracted with
      | Initialisation (symbol, tag, def) ->
        Flambda.Initialize_symbol (symbol, tag, def, program)
      | Effect effect ->
        Flambda.Effect (effect, program))
    introduced program

let rec split_program (program : Flambda.program_body) : Flambda.program_body =
  match program with
  | End s -> End s
  | Let_symbol (s, def, program) ->
    Let_symbol (s, def, split_program program)
  | Let_rec_symbol (defs, program) ->
    Let_rec_symbol (defs, split_program program)
  | Effect (expr, program) ->
    let program = split_program program in
    let introduced, expr = introduce_symbols expr in
    add_extracted introduced (Flambda.Effect (expr, program))
  | Initialize_symbol (symbol, tag, ((_::_::_) as fields), program) ->
    (* CR-someday pchambart: currently the only initialize_symbol with more
       than 1 field is the module block. This could evolve, in that case
       this pattern should be handled properly. *)
    Initialize_symbol (symbol, tag, fields, split_program program)
  | Initialize_symbol (sym, tag, [], program) ->
    Let_symbol (sym, Block (tag, []), split_program program)
  | Initialize_symbol (symbol, tag, [field], program) ->
    let program = split_program program in
    let introduced, field = introduce_symbols field in
    add_extracted introduced
      (Flambda.Initialize_symbol (symbol, tag, [field], program))

let lift ~backend:_ (program : Flambda.program) =
  { program with
    program_body = split_program program.program_body;
  }
