(**************************************************************************)
(*                                                                        *)
(*                                OCaml                                   *)
(*                                                                        *)
(*                       Pierre Chambart, OCamlPro                        *)
(*                  Mark Shinwell, Jane Street Europe                     *)
(*                                                                        *)
(*   Copyright 2015 Institut National de Recherche en Informatique et     *)
(*   en Automatique.  All rights reserved.  This file is distributed      *)
(*   under the terms of the Q Public License version 1.0.                 *)
(*                                                                        *)
(**************************************************************************)

type value_string_contents =
  | Contents of string
  | Unknown_or_mutable

type value_string = {
  contents : value_string_contents;
  size : int;
}

type value_float_array_contents =
  | Contents of float option array
  | Unknown_or_mutable

type value_float_array = {
  contents : value_float_array_contents;
  size : int;
}

type descr =
  | Value_block of Tag.t * approx array
  | Value_mutable_block of Tag.t * int
  | Value_int of int
  | Value_char of char
  | Value_constptr of int
  | Value_float of float
  | Value_float_array of value_float_array
  | Value_boxed_int : 'a Simple_value_approx.boxed_int * 'a -> descr
  | Value_string of value_string
  | Value_closure of value_closure
  | Value_set_of_closures of value_set_of_closures

and value_closure = {
  closure_id : Closure_id.t;
  set_of_closures : value_set_of_closures;
}

and value_set_of_closures = {
  set_of_closures_id : Set_of_closures_id.t;
  bound_vars : approx Var_within_closure.Map.t;
  results : approx Closure_id.Map.t;
  aliased_symbol : Symbol.t option;
}

and approx =
  | Value_unknown
  | Value_id of Export_id.t
  | Value_symbol of Symbol.t

let equal_approx (a1:approx) (a2:approx) =
  match a1, a2 with
  | Value_unknown, Value_unknown ->
    true
  | Value_id id1, Value_id id2 ->
    Export_id.equal id1 id2
  | Value_symbol s1, Value_symbol s2 ->
    Symbol.equal s1 s2
  | (Value_unknown | Value_symbol _ | Value_id _),
    (Value_unknown | Value_symbol _ | Value_id _) ->
    false

let equal_array eq a1 a2 =
  Array.length a1 = Array.length a2 &&
  try
    Array.iteri (fun i v1 -> if not (eq a2.(i) v1) then raise Exit) a1;
    true
  with Exit -> false

let equal_option eq o1 o2 =
  match o1, o2 with
  | None, None -> true
  | Some v1, Some v2 -> eq v1 v2
  | Some _, None | None, Some _ -> false

let equal_set_of_closures (s1:value_set_of_closures) (s2:value_set_of_closures) =
  Set_of_closures_id.equal s1.set_of_closures_id s2.set_of_closures_id &&
  Var_within_closure.Map.equal equal_approx s1.bound_vars s2.bound_vars &&
  Closure_id.Map.equal equal_approx s1.results s2.results &&
  equal_option Symbol.equal s1.aliased_symbol s2.aliased_symbol

let equal_descr (d1:descr) (d2:descr) : bool =
  match d1, d2 with
  | Value_block (t1, f1), Value_block (t2, f2) ->
    Tag.equal t1 t2 && equal_array equal_approx f1 f2
  | Value_mutable_block (t1, s1), Value_mutable_block (t2, s2) ->
    Tag.equal t1 t2 &&
    s1 = s2
  | Value_int i1, Value_int i2 ->
    i1 = i2
  | Value_char c1, Value_char c2 ->
    c1 = c2
  | Value_constptr i1, Value_constptr i2 ->
    i1 = i2
  | Value_float f1, Value_float f2 ->
    f1 = f2
  | Value_float_array s1, Value_float_array s2 ->
    s1 = s2
  | Value_boxed_int (t1, v1), Value_boxed_int (t2, v2) ->
    Simple_value_approx.equal_boxed_int t1 v1 t2 v2
  | Value_string s1, Value_string s2 ->
    s1 = s2
  | Value_closure c1, Value_closure c2 ->
    Closure_id.equal c1.closure_id c2.closure_id &&
    equal_set_of_closures c1.set_of_closures c2.set_of_closures
  | Value_set_of_closures s1, Value_set_of_closures s2 ->
    equal_set_of_closures s1 s2
  | ( Value_block (_, _) | Value_mutable_block (_, _) | Value_int _
    | Value_char _ | Value_constptr _ | Value_float _ | Value_float_array _
    | Value_boxed_int _ | Value_string _ | Value_closure _
    | Value_set_of_closures _ ),
    ( Value_block (_, _) | Value_mutable_block (_, _) | Value_int _
    | Value_char _ | Value_constptr _ | Value_float _ | Value_float_array _
    | Value_boxed_int _ | Value_string _ | Value_closure _
    | Value_set_of_closures _ ) ->
    false

type per_unit = {
  sets_of_closures : Flambda.function_declarations Set_of_closures_id.Map.t;
  closures : Flambda.function_declarations Closure_id.Map.t;
  values : descr Export_id.Map.t;
  globals : approx Ident.Map.t;
  symbol_id : Export_id.t Symbol.Map.t;
  offset_fun : int Closure_id.Map.t;
  offset_fv : int Var_within_closure.Map.t;
  constant_sets_of_closures : Set_of_closures_id.Set.t;
  invariant_params : Variable.Set.t Variable.Map.t Set_of_closures_id.Map.t;
}

type t = {
  per_unit : per_unit Compilation_unit.Map.t;
}

let empty_per_unit : per_unit = {
  sets_of_closures = Set_of_closures_id.Map.empty;
  closures = Closure_id.Map.empty;
  values = Export_id.Map.empty;
  globals = Ident.Map.empty;
  symbol_id = Symbol.Map.empty;
  offset_fun = Closure_id.Map.empty;
  offset_fv = Var_within_closure.Map.empty;
  constant_sets_of_closures = Set_of_closures_id.Set.empty;
  invariant_params = Set_of_closures_id.Map.empty;
}

let empty = {
  per_unit = Compilation_unit.Map.empty;
}

let empty_for_current_compilation_unit () = {
  per_unit =
    Compilation_unit.Map.add (Compilation_unit.get_current_exn ())
      empty_per_unit Compilation_unit.Map.empty;
}

let inject_sets_of_closures sets_of_closures : per_unit =
  { empty_per_unit with sets_of_closures; }

let inject_closures closures : per_unit =
  { empty_per_unit with closures; }

let inject_values values : per_unit =
  { empty_per_unit with values; }

let inject_symbol_id symbol_id : per_unit =
  { empty_per_unit with symbol_id; }

let inject_offset_fun offset_fun : per_unit =
  { empty_per_unit with offset_fun; }

let inject_offset_fv offset_fv : per_unit =
  { empty_per_unit with offset_fv; }

let inject_constant_sets_of_closures constant_sets_of_closures : per_unit =
  { empty_per_unit with constant_sets_of_closures; }

let inject_invariant_params invariant_params : per_unit =
  { empty_per_unit with invariant_params; }

let merge_per_unit (t1 : per_unit) (t2 : per_unit) : per_unit =
  let int_eq (i : int) j = i = j in
  { values = Export_id.Map.disjoint_union ~eq:equal_descr t1.values t2.values;
    globals = Ident.Map.disjoint_union t1.globals t2.globals;
    sets_of_closures =
      Set_of_closures_id.Map.disjoint_union t1.sets_of_closures
        t2.sets_of_closures;
    closures = Closure_id.Map.disjoint_union t1.closures t2.closures;
    symbol_id = Symbol.Map.disjoint_union t1.symbol_id t2.symbol_id;
    offset_fun = Closure_id.Map.disjoint_union
        ~eq:int_eq t1.offset_fun t2.offset_fun;
    offset_fv = Var_within_closure.Map.disjoint_union
        ~eq:int_eq t1.offset_fv t2.offset_fv;
    constant_sets_of_closures =
      Set_of_closures_id.Set.union t1.constant_sets_of_closures
        t2.constant_sets_of_closures;
    invariant_params =
      Set_of_closures_id.Map.disjoint_union
        ~eq:(Variable.Map.equal Variable.Set.equal)
        t1.invariant_params t2.invariant_params;
  }

let merge_per_unit_map map1 map2 =
  Compilation_unit.Map.merge (fun _compilation_unit per_unit1 per_unit2 ->
      match per_unit1, per_unit2 with
      | None, None -> None
      | None, Some per_unit
      | Some per_unit, None -> Some per_unit
      | Some per_unit1, Some per_unit2 ->
        Some (merge_per_unit per_unit1 per_unit2))
    map1 map2

let create ~sets_of_closures ~closures ~values ~globals ~symbol_id
      ~offset_fun ~offset_fv ~constant_sets_of_closures
      ~invariant_params : t =
  (* Do the hard work of partitioning by compilation unit now, rather than
     when we import, because in a large tree the number of imports may be
     very large.  The representation, being partitioned by compilation
     unit, also helps avoid enormous maps. *)
  let sets_of_closures =
    Set_of_closures_id.partition_map_by_compilation_unit sets_of_closures
    |> Compilation_unit.Map.map inject_sets_of_closures
  in
  let closures =
    Closure_id.partition_map_by_compilation_unit closures
    |> Compilation_unit.Map.map inject_closures
  in
  let values =
    Export_id.partition_map_by_compilation_unit values
    |> Compilation_unit.Map.map inject_values
  in
  let globals =
    (* The elements of [globals] always pertain to the current compilation
       unit. *)
    Compilation_unit.Map.add
      (Compilation_unit.get_current_exn ())
      { empty_per_unit with globals; }
      Compilation_unit.Map.empty
  in
  let symbol_id =
    Symbol.partition_map_by_compilation_unit symbol_id
    |> Compilation_unit.Map.map inject_symbol_id
  in
  let offset_fun =
    Closure_id.partition_map_by_compilation_unit offset_fun
    |> Compilation_unit.Map.map inject_offset_fun
  in
  let offset_fv =
    Var_within_closure.partition_map_by_compilation_unit offset_fv
    |> Compilation_unit.Map.map inject_offset_fv
  in
  let constant_sets_of_closures =
    Set_of_closures_id.partition_set_by_compilation_unit
      constant_sets_of_closures
    |> Compilation_unit.Map.map inject_constant_sets_of_closures
  in
  let invariant_params =
    Set_of_closures_id.partition_map_by_compilation_unit
      invariant_params
    |> Compilation_unit.Map.map inject_invariant_params
  in
  let per_unit =
    List.fold_left merge_per_unit_map Compilation_unit.Map.empty
      [sets_of_closures; closures; values; globals; symbol_id; offset_fun;
        offset_fv; constant_sets_of_closures; invariant_params;
      ]
  in
  { per_unit; }

let add_clambda_info t ~offset_fun ~offset_fv ~constant_sets_of_closures =
  Compilation_unit.Map.iter (fun _compilation_unit per_unit ->
      assert (Closure_id.Map.cardinal per_unit.offset_fun = 0);
      assert (Var_within_closure.Map.cardinal per_unit.offset_fv = 0);
      assert (Set_of_closures_id.Set.cardinal per_unit.
        constant_sets_of_closures = 0))
    t.per_unit;
  let offset_fun =
    Closure_id.partition_map_by_compilation_unit offset_fun
    |> Compilation_unit.Map.map inject_offset_fun
  in
  let offset_fv =
    Var_within_closure.partition_map_by_compilation_unit offset_fv
    |> Compilation_unit.Map.map inject_offset_fv
  in
  let constant_sets_of_closures =
    Set_of_closures_id.partition_set_by_compilation_unit
      constant_sets_of_closures
    |> Compilation_unit.Map.map inject_constant_sets_of_closures
  in
  let per_unit =
    List.fold_left merge_per_unit_map t.per_unit
      [offset_fun; offset_fv; constant_sets_of_closures]
  in
  { per_unit; }

(* CR mshinwell: resurrect printer and make it suitable for ocamlobjinfo *)
(*
let print_approx ppf (t : per_unit) =
  let values = t.values in
  let fprintf = Format.fprintf in
  let printed = ref Export_id.Set.empty in
  let recorded_symbol = ref Symbol.Set.empty in
  let symbols_to_print = Queue.create () in
  let printed_set_of_closures = ref Set_of_closures_id.Set.empty in
  let rec print_approx ppf (approx : approx) =
    match approx with
    | Value_unknown -> fprintf ppf "?"
    | Value_id id ->
      if Export_id.Set.mem id !printed then
        fprintf ppf "(%a: _)" Export_id.print id
      else begin
        try
          let descr = Export_id.Map.find id values in
          printed := Export_id.Set.add id !printed;
          fprintf ppf "@[<hov 2>(%a:@ %a)@]" Export_id.print id print_descr descr
        with Not_found ->
          fprintf ppf "(%a: Not available)" Export_id.print id
      end
    | Value_symbol sym ->
      if not (Symbol.Set.mem sym !recorded_symbol) then begin
        recorded_symbol := Symbol.Set.add sym !recorded_symbol;
        Queue.push sym symbols_to_print;
      end;
      Symbol.print ppf sym
  and print_descr ppf (descr : descr) =
    match descr with
    | Value_int i -> Format.pp_print_int ppf i
    | Value_char c -> fprintf ppf "%c" c
    | Value_constptr i -> fprintf ppf "%ip" i
    | Value_block (tag, fields) ->
      fprintf ppf "[%a:%a]" Tag.print tag print_fields fields
    | Value_mutable_block (tag, size) ->
      fprintf ppf "[mutable %a:%i]" Tag.print tag size
    | Value_closure {closure_id; set_of_closures} ->
      fprintf ppf "(closure %a, %a)" Closure_id.print closure_id
        print_set_of_closures set_of_closures
    | Value_set_of_closures set_of_closures ->
      fprintf ppf "(set_of_closures %a)" print_set_of_closures set_of_closures
    | Value_string { contents; size } ->
      begin match contents with
      | Unknown_or_mutable -> Format.fprintf ppf "string %i" size
      | Contents s ->
        let s =
          if size > 10
          then String.sub s 0 8 ^ "..."
          else s
        in
        Format.fprintf ppf "string %i %S" size s
      end
    | Value_float f -> Format.pp_print_float ppf f
    | Value_float_array float_array ->
      Format.fprintf ppf "float_array%s %i"
        (match float_array.contents with
          | Unknown_or_mutable -> ""
          | Contents _ -> "_imm")
        float_array.size
    | Value_boxed_int (t, i) ->
      let module A = Simple_value_approx in
      match t with
      | A.Int32 -> Format.fprintf ppf "%li" i
      | A.Int64 -> Format.fprintf ppf "%Li" i
      | A.Nativeint -> Format.fprintf ppf "%ni" i
  and print_fields ppf fields =
    Array.iter (fun approx -> fprintf ppf "%a@ " print_approx approx) fields
  and print_set_of_closures ppf
      { set_of_closures_id; bound_vars; aliased_symbol } =
    if Set_of_closures_id.Set.mem set_of_closures_id !printed_set_of_closures
    then fprintf ppf "%a" Set_of_closures_id.print set_of_closures_id
    else begin
      printed_set_of_closures :=
        Set_of_closures_id.Set.add set_of_closures_id !printed_set_of_closures;
      let print_alias ppf = function
        | None -> ()
        | Some symbol ->
          Format.fprintf ppf "@ (alias: %a)" Symbol.print symbol
      in
      fprintf ppf "{%a: %a%a}"
        Set_of_closures_id.print set_of_closures_id
        print_binding bound_vars
        print_alias aliased_symbol
    end
  and print_binding ppf bound_vars =
    Var_within_closure.Map.iter (fun clos_id approx ->
        fprintf ppf "%a -> %a,@ "
          Var_within_closure.print clos_id
          print_approx approx)
      bound_vars
  in
  let rec print_recorded_symbols () =
    if not (Queue.is_empty symbols_to_print) then begin
      let sym = Queue.pop symbols_to_print in
      begin match Symbol.Map.find sym t.symbol_id with
      | exception Not_found -> ()
      | id ->
        fprintf ppf "@[<hov 2>%a:@ %a@];@ "
          Symbol.print sym
          print_approx (Value_id id)
      end;
      print_recorded_symbols ();
    end
  in
  fprintf ppf "@]@ @[<hov 2>Symbols:@ ";
  print_recorded_symbols ();
  fprintf ppf "@]"

let print_approxs ppf id approx =
  Format.fprintf ppf "%a -> %a;@ " Ident.print id print_approx approx

let print_all ppf (t : t) =
  let fprintf = Format.fprintf in
  Compilation_unit.Map.iter (fun compilation_unit per_unit ->
      fprintf ppf "approxs@ %a@.@."
        print_approx per_unit;
      fprintf ppf "functions@ %a@.@."
        (Set_of_closures_id.Map.print Flambda.print_function_declarations)
        per_unit.sets_of_closures)
    t.per_unit;
  fprintf ppf "@[<hov 2>Globals:@ ";
  Ident.Map.iter print_approxs t.globals
*)
let print_all _ _ = failwith "Not implemented"
