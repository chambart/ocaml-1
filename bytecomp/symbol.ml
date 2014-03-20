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

open Ext_types

type linkage_name = string

type static_exception = int

module Compilation_unit : sig
  include PrintableHashOrdered
  val create : Ident.t -> linkage_name -> t
  val to_ident : t -> Ident.t
  (* Should be used only in Compilenv *)
  val name : t -> string
  val linkage_name : t -> linkage_name
end = struct
  type t =
    { id: Ident.t;
      linkage_name: linkage_name }
  (* multiple units can have the same id, if they are in different
     pack. To distinguish we also keep the linkage name which contains
     the pack name *)
  let compare v1 v2 =
    let c = Ident.compare v1.id v2.id in
    if c = 0
    then String.compare v1.linkage_name v2.linkage_name
    else c

  let equal x y = compare x y = 0

  let create id linkage_name =
    assert(Ident.persistent id);
    { id; linkage_name }

  let print ppf x = Ident.print ppf x.id
  let output oc x = Ident.output oc x.id
  let hash x = Ident.hash x.id

  let to_ident x = x.id
  let name x = x.id.Ident.name

  let linkage_name x = x.linkage_name
end

type compilation_unit = Compilation_unit.t

let predefined_exception_compilation_unit =
  Compilation_unit.create (Ident.create_persistent "__dummy__") "__dummy__"

type symbol = { sym_unit : compilation_unit; sym_label : linkage_name }

let ident_of_compilation_unit = Compilation_unit.to_ident
let linkage_name_of_compilation_unit = Compilation_unit.linkage_name

let linkage_name s = s
let string_of_linkage_name s = s

module Symbol = struct
  type t = symbol
  let compare s1 s2 = String.compare s1.sym_label s2.sym_label
  (** Labels are unique, so comparing them is sufficient. It also could
      uncover bugs to consider same labels from different modules equal *)
  let output c s = output_string c s.sym_label
  let hash s = Hashtbl.hash s.sym_label
  let equal s1 s2 = s1.sym_label = s2.sym_label
  let print ppf s =
    Format.fprintf ppf "%a - %s" Compilation_unit.print s.sym_unit s.sym_label
end

type variable = { var_unit : compilation_unit; var_var : Ident.t }

module Variable = struct
  type t = variable
  let compare v1 v2 =
    let c = Ident.compare v1.var_var v2.var_var in
    if c = 0
    then Compilation_unit.compare v1.var_unit v2.var_unit
    else c
  let output c v = Ident.output c v.var_var
  let hash v = Ident.hash v.var_var
  let equal v1 v2 =
    Ident.same v1.var_var v2.var_var &&
    Compilation_unit.equal v1.var_unit v2.var_unit
  let print ppf v =
    Format.fprintf ppf "%a.%a"
      Compilation_unit.print v.var_unit
      Ident.print v.var_var
  let create ~compilation_unit id =
    { var_unit = compilation_unit; var_var = id }
  let make ~compilation_unit name =
    { var_unit = compilation_unit; var_var = Ident.create name }
  let compilation_unit var = var.var_unit
  let rename ~compilation_unit var =
    { var_unit = compilation_unit;
      var_var = Ident.rename var.var_var }
  let to_string var = Format.asprintf "%a" print var
  let make_ident var =
    let open Ident in
    { var.var_var with
      name = Compilation_unit.name var.var_unit
             ^ "_" ^ var.var_var.name }

  let unique_name var = Ident.unique_name var.var_var
  let to_ident var = var.var_var
end

module SymbolSet = ExtSet(Symbol)
module SymbolMap = ExtMap(Symbol)
module SymbolTbl = ExtHashtbl(Symbol)

module VarSet = struct
  include ExtSet(Variable)
  let of_ident_set ~compilation_unit idset =
    Lambda.IdentSet.fold (fun id set ->
        add (Variable.create ~compilation_unit id) set)
      idset empty
end
module VarMap = ExtMap(Variable)
module VarTbl = ExtHashtbl(Variable)

module ExprId : Id = Id(struct end)
module ExprMap = ExtMap(ExprId)
module ExprSet = ExtSet(ExprId)
module ExprTbl = ExtHashtbl(ExprId)

module FunInnerid : Id = Id(struct end)
module FunId : UnitId with module Compilation_unit := Compilation_unit
  = UnitId(FunInnerid)(Compilation_unit)
module FunMap = ExtMap(FunId)
module FunSet = ExtSet(FunId)
module FunTbl = ExtHashtbl(FunId)

module Static_exception = struct
  include Int
  let of_int x = x
  let to_int x = x
  let create () = Lambda.next_raise_count ()
end

type closure_element = {
  ce_id : Ident.t;
  ce_unit : compilation_unit;
}

type function_within_closure = closure_element
type variable_within_closure = closure_element

module Closure_element = struct
  type t = closure_element
  let compare x y =
    let c = Ident.compare x.ce_id y.ce_id in
    if c = 0
    then Compilation_unit.compare x.ce_unit y.ce_unit
    else c
  let output oc x =
    Printf.fprintf oc "%a.%a"
      Compilation_unit.output x.ce_unit
      Ident.output x.ce_id
  let print ppf x =
    Format.fprintf ppf "%a.%a"
      Compilation_unit.print x.ce_unit
      Ident.print x.ce_id
  let hash off = Hashtbl.hash off
  let equal o1 o2 = compare o1 o2 = 0

  let create var = { ce_unit = var.var_unit; ce_id = var.var_var }
  let compilation_unit { ce_unit } = ce_unit

  let to_var { ce_unit; ce_id } = { var_unit = ce_unit; var_var = ce_id }

  let to_string t = Format.asprintf "%a" print t

  let unique_name ce = Ident.unique_name ce.ce_id
end

let ident_of_function_within_closure { ce_id } = ce_id

module Closure_function = Closure_element
module Closure_variable = Closure_element

module ClosureFunctionMap = ExtMap(Closure_function)
module ClosureFunctionSet = ExtSet(Closure_function)
module ClosureFunctionTbl = ExtHashtbl(Closure_function)

module ClosureVariableMap = ExtMap(Closure_variable)
module ClosureVariableSet = ExtSet(Closure_variable)
module ClosureVariableTbl = ExtHashtbl(Closure_variable)

module StaticExceptionSet = ExtSet(Static_exception)
module StaticExceptionMap = ExtMap(Static_exception)
module StaticExceptionTbl = ExtHashtbl(Static_exception)

module CompilationUnitSet = ExtSet(Compilation_unit)
module CompilationUnitMap = ExtMap(Compilation_unit)
module CompilationUnitTbl = ExtHashtbl(Compilation_unit)

module IdentMap = ExtMap(Ident)

module Var_connected_components =
  Sort_connected_components.Make(Variable)

