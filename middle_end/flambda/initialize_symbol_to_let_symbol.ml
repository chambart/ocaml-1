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

[@@@ocaml.warning "+a-4-9-30-40-41-42-66"]
open! Int_replace_polymorphic_compare

let rec tail_var (expr:Flambda.t) =
  match expr with
  | Let { defining_expr = Phantom _; body ; _ } ->
    tail_var body
  | Var var ->
    Some var
  | _ -> None

let rec constant_field (expr:Flambda.t)
  : Flambda.constant_defining_value_block_field option =
  match expr with
  | Let { defining_expr = Phantom _; body ; _ } ->
    constant_field body
  | Let { var; defining_expr = Normal (Const c); body ; _ } ->
    begin match tail_var body with
    | None -> None
    | Some var' ->
      assert(Variable.equal var var');
      (* This must be true since var is the only variable in scope *)
      Some (Flambda.Const c)
    end
  | Let { var; defining_expr = Normal (Symbol s); body ; _ } ->
    begin match tail_var body with
    | None -> None
    | Some var' ->
      assert(Variable.equal var var');
      Some (Flambda.Symbol s)
    end
  | _ ->
    None

let rec loop (program : Flambda.program_body) : Flambda.program_body =
  match program with
  | Initialize_symbol (symbol, tag, fields, program) ->
    let constant_fields = List.map constant_field fields in
    begin
      match Misc.Stdlib.List.some_if_all_elements_are_some constant_fields
    with
    | None ->
      Initialize_symbol (symbol, tag, fields, loop program)
    | Some fields ->
      Let_symbol (symbol, Block (tag, fields), loop program)
    end
  | Let_symbol (symbol, const, program) ->
    Let_symbol (symbol, const, loop program)
  | Let_rec_symbol (defs, program) ->
    Let_rec_symbol (defs, loop program)
  | Effect (expr, program) ->
    Effect (expr, loop program)
  | End symbol ->
    End symbol

let run (program : Flambda.program) =
  { program with
    program_body = loop program.program_body;
  }
