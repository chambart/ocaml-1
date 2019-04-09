(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*           Mark Shinwell and Leo White, Jane Street Europe              *)
(*                                                                        *)
(*   Copyright 2016 Jane Street Group LLC                                 *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

type t = {
  mutable free_variables : Variable.Set.t;
  mutable variables_used_in_phantom_context : Variable.Set.t;
  mutable free_symbols : Symbol.Set.t;
  mutable symbols_used_in_phantom_context : Symbol.Set.t;
}

type free_names = t

let is_free_variable t var = Variable.Set.mem var t.free_variables
let is_variable_used_in_phantom_context t var =
  Variable.Set.mem var t.variables_used_in_phantom_context

let free_variables t = t.free_variables
let variables_used_in_phantom_context t =
  t.variables_used_in_phantom_context
let all_free_variables t =
  Variable.Set.union (free_variables t)
    (variables_used_in_phantom_context t)

let free_symbols t = t.free_symbols
let symbols_used_in_phantom_context t = t.symbols_used_in_phantom_context
let all_free_symbols t =
  Symbol.Set.union (free_symbols t)
    (symbols_used_in_phantom_context t)

let subset t1 t2 =
  Variable.Set.subset t1.free_variables t2.free_variables
    && Variable.Set.subset
      t1.variables_used_in_phantom_context
      t2.variables_used_in_phantom_context
    && Symbol.Set.subset t1.free_symbols t2.free_symbols
    && Symbol.Set.subset
      t1.symbols_used_in_phantom_context
      t2.symbols_used_in_phantom_context

let print ppf t =
  Format.fprintf ppf "{ free_variables = %a;@ free_phantom_variables = %a;@ \
      free_symbols = %a;@ free_phantom_symbols = %a; }"
    Variable.Set.print t.free_variables
    Variable.Set.print t.variables_used_in_phantom_context
    Symbol.Set.print t.free_symbols
    Symbol.Set.print t.symbols_used_in_phantom_context

module Mutable = struct
  type nonrec t = t

  let create () =
    { free_variables = Variable.Set.empty;
      variables_used_in_phantom_context = Variable.Set.empty;
      free_symbols = Symbol.Set.empty;
      symbols_used_in_phantom_context = Symbol.Set.empty;
    }

  let free_variable t var =
    t.free_variables <- Variable.Set.add var t.free_variables

  let variables_used_in_phantom_context t var =
    t.variables_used_in_phantom_context <-
      Variable.Set.add var t.variables_used_in_phantom_context

  let free_symbol t sym =
    t.free_symbols <- Symbol.Set.add sym t.free_symbols

  let free_symbols t syms =
    t.free_symbols <- Symbol.Set.union syms t.free_symbols

  let symbol_used_in_phantom_context t sym =
    t.symbols_used_in_phantom_context <-
      Symbol.Set.add sym t.symbols_used_in_phantom_context

  let union_free_symbols_only t t' =
    t.free_symbols <- Symbol.Set.union t.free_symbols t'.free_symbols;
    t.symbols_used_in_phantom_context
      <- Symbol.Set.union t.symbols_used_in_phantom_context
        t'.symbols_used_in_phantom_context

  let union t t' =
    t.free_variables
      <- Variable.Set.union t.free_variables t'.free_variables;
    t.variables_used_in_phantom_context
      <- Variable.Set.union
        t.variables_used_in_phantom_context
        t'.variables_used_in_phantom_context;
    union_free_symbols_only t t'

  let bound_variables t bound_vars =
    t.free_variables <- Variable.Set.diff t.free_variables bound_vars;
    t.variables_used_in_phantom_context
      <- Variable.Set.diff t.variables_used_in_phantom_context bound_vars

  let freeze t =
    { free_variables = t.free_variables;
      variables_used_in_phantom_context = t.variables_used_in_phantom_context;
      free_symbols = t.free_symbols;
      symbols_used_in_phantom_context = t.symbols_used_in_phantom_context;
    }
end
