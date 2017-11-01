(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                       Pierre Chambart, OCamlPro                        *)
(*           Mark Shinwell and Leo White, Jane Street Europe              *)
(*                                                                        *)
(*   Copyright 2013--2017 OCamlPro SAS                                    *)
(*   Copyright 2014--2017 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

[@@@ocaml.warning "+a-4-9-30-40-41-42"]

module Float = Numbers.Float
module Int32 = Numbers.Int32
module Int64 = Numbers.Int64

module K = Flambda_kind

module Make (Expr : sig
  type t
  val print : Format.formatter -> t -> unit
  val free_symbols : t -> Symbol.Set.t
end) = struct
  type expr = Expr.t

  type inline_attribute =
    | Always_inline
    | Never_inline
    | Unroll of int
    | Default_inline

  let print_inline_attribute ppf attr =
    let fprintf = Format.fprintf in
    match attr with
    | Always_inline -> fprintf ppf "Always_inline"
    | Never_inline -> fprintf ppf "Never_inline"
    | Unroll n -> fprintf ppf "@[(Unroll %d)@]" n
    | Default_inline -> fprintf ppf "Default_inline"

  type specialise_attribute =
    | Always_specialise
    | Never_specialise
    | Default_specialise

  let print_specialise_attribute ppf attr =
    let fprintf = Format.fprintf in
    match attr with
    | Always_specialise -> fprintf ppf "Always_specialise"
    | Never_specialise -> fprintf ppf "Never_specialise"
    | Default_specialise -> fprintf ppf "Default_specialise"

  type unresolved_value =
    | Set_of_closures_id of Set_of_closures_id.t
    | Export_id of Export_id.t
    | Symbol of Symbol.t

  type unknown_because_of =
    | Unresolved_value of unresolved_value
    | Other

  let join_unknown_because_of u1 u2 =
    match u1, u2 with
    | Unresolved_value (Set_of_closures_id s1),
        Unresolved_value (Set_of_closures_id s2) ->
      if Set_of_closures_id.equal s1 s2 then u1 else Other
    | Unresolved_value (Export_id s1), Unresolved_value (Export_id s2) ->
      if Export_id.equal s1 s2 then u1 else Other
    | Unresolved_value (Symbol s1), Unresolved_value (Symbol s2) ->
      if Symbol.equal s1 s2 then u1 else Other
    | _, _ -> Other

  (** Types from other compilation units are loaded lazily.  There are two
      kinds of cross-compilation unit reference to be resolved: via
      [Export_id.t] values and via [Symbol.t] values. *)
  type load_lazily =
    | Export_id of Export_id.t
    | Symbol of Symbol.t

  let print_load_lazily ppf (ll : load_lazily) =
    match ll with
    | Export_id id -> Format.fprintf ppf "(eid %a)" Export_id.print id
    | Symbol sym ->
      Format.fprintf ppf "(sym %a)" Symbol.print sym

  (* CR mshinwell: update comment *)
  (* A value of type [T.t] corresponds to an "approximation" of the result of
     a computation in the program being compiled.  That is to say, it
     represents what knowledge we have about such a result at compile time.
     The simplification pass exploits this information to partially evaluate
     computations.

     At a high level, an approximation for a value [v] has three parts:
     - the "description" (for example, "the constant integer 42");
     - an optional variable;
     - an optional symbol or symbol field.
     If the variable (resp. symbol) is present then that variable (resp.
     symbol) may be used to obtain the value [v].

     The exact semantics of the variable and symbol fields follows.

     Approximations are deduced at particular points in an expression tree,
     but may subsequently be propagated to other locations.

     At the point at which an approximation is built for some value [v], we can
     construct a set of variables (call the set [S]) that are known to alias the
     same value [v].  Each member of [S] will have the same or a more precise
     [descr] field in its approximation relative to the approximation for [v].
     (An increase in precision may currently be introduced for pattern
     matches.)  If [S] is non-empty then it is guaranteed that there is a
     unique member of [S] that was declared in a scope further out ("earlier")
     than all other members of [S].  If such a member exists then it is
     recorded in the [var] field.  Otherwise [var] is [None].

     Analogous to the construction of the set [S], we can construct a set [T]
     consisting of all symbols that are known to alias the value whose
     approximation is being constructed.  If [T] is non-empty then the
     [symbol] field is set to some member of [T]; it does not matter which
     one.  (There is no notion of scope for symbols.)

     Note about mutable blocks:

     Mutable blocks are always represented by [Unknown] or
     [Bottom].  Any other approximation could leave the door open to
     a miscompilation.   Such bad scenarios are most likely a user using
     [Obj.magic] or [Obj.set_field] in an inappropriate situation.
     Such a situation might be:
     [let x = (1, 1) in
     Obj.set_field (Obj.repr x) 0 (Obj.repr 2);
     assert(fst x = 2)]
     The user would probably expect the assertion to be true, but the
     compiler could in fact propagate the value of [x] across the
     [Obj.set_field].

     Insisting that mutable blocks have [Unknown] or [bottom]
     approximations certainly won't always prevent this kind of error, but
     should help catch many of them.

     It is possible that there may be some false positives, with correct
     but unreachable code causing this check to fail.  However the likelihood
     of this seems sufficiently low, especially compared to the advantages
     gained by performing the check, that we include it.

     An example of a pattern that might trigger a false positive is:
     [type a = { a : int }
     type b = { mutable b : int }
     type t =
       | A : a t
       | B : b t
     let f (type x) (v:x t) (r:x) =
       match v with
       | A -> r.a
       | B -> r.b <- 2; 3

     let v =
     let r =
       ref A in
       r := A; (* Some pattern that the compiler can't understand *)
       f !r { a = 1 }]
     When inlining [f], the B branch is unreachable, yet the compiler
     cannot prove it and must therefore keep it.
  *)

  type string_contents =
    | Contents of string
    | Unknown_or_mutable

  type string_ty = {
    contents : string_contents;
    size : int;
  }

  type 'a with_var_and_symbol = {
    descr : 'a;
    var : Variable.t option;


    symbol : (Symbol.t * int option) option;
  }

  type t =
    | Value of ty_value
    | Naked_immediate of ty_naked_immediate
    | Naked_float of ty_naked_float
    | Naked_int32 of ty_naked_int32
    | Naked_int64 of ty_naked_int64
    | Naked_nativeint of ty_naked_nativeint

  and flambda_type = t

  and ty_value = (of_kind_value, Flambda_kind.scanning) ty
  and ty_naked_immediate = (of_kind_naked_immediate, unit) ty
  and ty_naked_float = (of_kind_naked_float, unit) ty
  and ty_naked_int32 = (of_kind_naked_int32, unit) ty
  and ty_naked_int64 = (of_kind_naked_int64, unit) ty
  and ty_naked_nativeint = (of_kind_naked_nativeint, unit) ty

  and ('a, 'u) ty = ('a, 'u) maybe_unresolved with_var_and_symbol

  and resolved_t =
    | Value of resolved_ty_value
    | Naked_immediate of resolved_ty_naked_immediate
    | Naked_float of resolved_ty_naked_float
    | Naked_int32 of resolved_ty_naked_int32
    | Naked_int64 of resolved_ty_naked_int64
    | Naked_nativeint of resolved_ty_naked_nativeint

  and resolved_ty_value = (of_kind_value, Flambda_kind.scanning) resolved_ty
  and resolved_ty_naked_immediate = (of_kind_naked_immediate, unit) resolved_ty
  and resolved_ty_naked_float = (of_kind_naked_float, unit) resolved_ty
  and resolved_ty_naked_int32 = (of_kind_naked_int32, unit) resolved_ty
  and resolved_ty_naked_int64 = (of_kind_naked_int64, unit) resolved_ty
  and resolved_ty_naked_nativeint = (of_kind_naked_nativeint, unit) resolved_ty
  and resolved_ty_set_of_closures = (set_of_closures, unit) resolved_ty

  and ('a, 'u) resolved_ty = ('a, 'u) or_unknown_or_bottom with_var_and_symbol

  and ('a, 'u) maybe_unresolved =
    | Ok of ('a, 'u) or_unknown_or_bottom
    | Load_lazily of load_lazily

  and ('a, 'u) or_unknown_or_bottom =
    | Unknown of unknown_because_of * 'u
    | Ok of 'a
    | Bottom

  and of_kind_value =
    | Singleton of of_kind_value_singleton
    | Union of of_kind_value with_var_and_symbol
        * of_kind_value with_var_and_symbol

  and of_kind_value_singleton =
    | Tagged_immediate of ty_naked_immediate
    | Boxed_float of ty_naked_float
    | Boxed_int32 of ty_naked_int32
    | Boxed_int64 of ty_naked_int64
    | Boxed_nativeint of ty_naked_nativeint
    (* CR mshinwell: Add an [Immutable_array] module *)
    | Block of Tag.Scannable.t * (ty_value array)
    | Set_of_closures of set_of_closures
    | Closure of {
        set_of_closures : resolved_ty_set_of_closures;
        closure_id : Closure_id.t
      }
    | String of string_ty
    | Float_array of ty_naked_float array

  and inlinable_function_declaration = {
    closure_origin : Closure_origin.t;
    continuation_param : Continuation.t;
    is_classic_mode : bool;
    params : (Parameter.t * t) list;
    body : expr;
    free_symbols : Symbol.Set.t;
    result : t list;
    stub : bool;
    dbg : Debuginfo.t;
    inline : inline_attribute;
    specialise : specialise_attribute;
    is_a_functor : bool;
    invariant_params : Variable.Set.t lazy_t;
    size : int option lazy_t;
    direct_call_surrogate : Closure_id.t option;
  }

  and non_inlinable_function_declaration = {
    result : t list;
    direct_call_surrogate : Closure_id.t option;
  }

  and function_declaration =
    | Non_inlinable of non_inlinable_function_declaration
    | Inlinable of inlinable_function_declaration

  and set_of_closures = {
    set_of_closures_id : Set_of_closures_id.t;
    set_of_closures_origin : Set_of_closures_origin.t;
    function_decls : function_declaration Closure_id.Map.t;
    closure_elements : ty_value Var_within_closure.Map.t;
  }

  and of_kind_naked_immediate =
    | Naked_immediate of Immediate.t

  and of_kind_naked_float =
    | Naked_float of float

  and of_kind_naked_int32 =
    | Naked_int32 of Int32.t

  and of_kind_naked_int64 =
    | Naked_int64 of Int64.t

  and of_kind_naked_nativeint =
    | Naked_nativeint of Targetint.t

  let print_unresolved_value ppf (unresolved : unresolved_value) =
    match unresolved with
    | Set_of_closures_id set ->
      Format.fprintf ppf "Set_of_closures_id %a" Set_of_closures_id.print set
    | Symbol symbol ->
      Format.fprintf ppf "Symbol %a" Symbol.print symbol
    | Export_id id ->
      Format.fprintf ppf "Export_id %a" Export_id.print id

  let print_with_var_and_symbol print_descr ppf { descr; var; symbol; } =
    let print_symbol ppf = function
      | None -> Symbol.print_opt ppf None
      | Some (sym, None) -> Symbol.print ppf sym
      | Some (sym, Some field) ->
        Format.fprintf ppf "%a.(%i)" Symbol.print sym field
    in
    Format.fprintf ppf "{ descr=%a var=%a symbol=%a }"
      print_descr descr
      Variable.print_opt var
      print_symbol symbol

  let print_maybe_unresolved print_contents ppf (m : _ maybe_unresolved) =
    match m with
    | Ok contents -> print_contents ppf contents
    | Load_lazily ll -> Format.fprintf ppf "lazy(%a)" print_load_lazily ll

  let print_of_kind_naked_immediate ppf (o : of_kind_naked_immediate) =
    match o with
    | Naked_immediate i -> Format.fprintf ppf "%a" Immediate.print i

  let print_of_kind_naked_float ppf (o : of_kind_naked_float) =
    match o with
    | Naked_float f -> Format.fprintf ppf "%f" f

  let print_of_kind_naked_int32 ppf (o : of_kind_naked_int32) =
    match o with
    | Naked_int32 i -> Format.fprintf ppf "%a" Int32.print i

  let print_of_kind_naked_int64 ppf (o : of_kind_naked_int64) =
    match o with
    | Naked_int64 i -> Format.fprintf ppf "%a" Int64.print i

  let print_of_kind_naked_nativeint ppf (o : of_kind_naked_nativeint) =
    match o with
    | Naked_nativeint i -> Format.fprintf ppf "%a" Targetint.print i

  let print_or_unknown_or_bottom print_contents print_unknown_payload ppf
        (o : _ or_unknown_or_bottom) =
    match o with
    | Unknown (reason, payload) ->
      begin match reason with
      | Unresolved_value value ->
        Format.fprintf ppf "?%a(due to unresolved %a)"
          print_unknown_payload payload
          print_unresolved_value value
      | Other -> Format.fprintf ppf "?%a" print_unknown_payload payload
      end;
    | Ok contents -> print_contents ppf contents
    | Bottom -> Format.fprintf ppf "bottom"

  let print_ty_generic print_contents print_unknown_payload ppf ty =
    (print_with_var_and_symbol
      (print_maybe_unresolved
        (print_or_unknown_or_bottom print_contents print_unknown_payload)))
      ppf ty

  let print_resolved_ty_generic print_contents print_unknown_payload ppf ty =
    (print_with_var_and_symbol
       (print_or_unknown_or_bottom print_contents print_unknown_payload))
      ppf ty

  let rec print_of_kind_value ppf (o : of_kind_value) =
    match o with
    | Singleton singleton -> print_of_kind_value_singleton ppf singleton
    | Union (w1, w2) ->
      let print_part ppf w =
        print_with_var_and_symbol print_of_kind_value ppf w
      in
      Format.fprintf ppf "@[(Union (%a)(%a))@]"
        print_part w1 print_part w2

  and print_of_kind_value_singleton ppf (singleton : of_kind_value_singleton) =
    match singleton with
    | Tagged_immediate t ->
      Format.fprintf ppf "(tagged_imm %a)" print_ty_naked_immediate t
    | Boxed_float f ->
      Format.fprintf ppf "(boxed_float %a)" print_ty_naked_float f
    | Boxed_int32 n ->
      Format.fprintf ppf "(boxed_int32 %a)" print_ty_naked_int32 n
    | Boxed_int64 n ->
      Format.fprintf ppf "(boxed_int64 %a)" print_ty_naked_int64 n
    | Boxed_nativeint n ->
      Format.fprintf ppf "(boxed_nativeint %a)" print_ty_naked_nativeint n
    | Block (tag, fields) ->
      Format.fprintf ppf "@[[%a: %a]@]"
        Tag.Scannable.print tag
        (Format.pp_print_list ~pp_sep:(fun ppf () -> Format.fprintf ppf "; ")
          print_ty_value) (Array.to_list fields)
    | Set_of_closures set_of_closures ->
      print_set_of_closures ppf set_of_closures
    | Closure { set_of_closures; closure_id; } ->
      Format.fprintf ppf "(closure:@ @[<2>[@ %a @[<2>from@ %a@];@ ]@])"
        Closure_id.print closure_id
        print_resolved_ty_set_of_closures set_of_closures
    | String { contents; size; } ->
      begin match contents with
      | Unknown_or_mutable -> Format.fprintf ppf "string %i" size
      | Contents s ->
        let s =
          if size > 10 then String.sub s 0 8 ^ "..."
          else s
        in
        Format.fprintf ppf "string %i %S" size s
      end
    | Float_array fields ->
      Format.fprintf ppf "@[(float_array %a)@]"
        (Format.pp_print_list ~pp_sep:Format.pp_print_space
          print_ty_naked_float)
        (Array.to_list fields)

  and print_ty_value ppf (ty : ty_value) =
    let print_scanning ppf (scanning : K.scanning) =
      match scanning with
      | Must_scan -> Format.fprintf ppf "*"
      | Can_scan -> ()
    in
    print_ty_generic print_of_kind_value print_scanning ppf ty

  and _unused = Expr.print

  and print_inlinable_function_declaration ppf
        (decl : inlinable_function_declaration) =
    Format.fprintf ppf
      "@[(inlinable@ \
        @[(closure_origin %a)@]@,\
        @[(continuation_param %a)@]@,\
        @[(is_classic_mode %b)@]@,\
        @[(params (%a))@]@,\
        @[(body <elided>)@]@,\
        @[(free_symbols %a)@]@,\
        @[(result (%a))@]@,\
        @[(stub %b)@]@,\
        @[(dbg %a)@]@,\
        @[(inline %a)@]@,\
        @[(specialise %a)@]@,\
        @[(is_a_functor %b)@]@,\
        @[(invariant_params %a)@]@,\
        @[(size %a)@]@,\
        @[(direct_call_surrogate %a)@])@]"
      Closure_origin.print decl.closure_origin
      Continuation.print decl.continuation_param
      decl.is_classic_mode
      (Format.pp_print_list ~pp_sep:(fun ppf () -> Format.fprintf ppf ", ")
        (fun ppf (param, ty) ->
          Format.fprintf ppf "@[(%a@ :@ %a)@]"
            Parameter.print param
            print ty)) decl.params
      Symbol.Set.print decl.free_symbols
      (Format.pp_print_list ~pp_sep:(fun ppf () -> Format.fprintf ppf ", ")
        (fun ppf ty ->
          Format.fprintf ppf "%a"
            print ty)) decl.result
      decl.stub
      Debuginfo.print_compact decl.dbg
      print_inline_attribute decl.inline
      print_specialise_attribute decl.specialise
      decl.is_a_functor
      Variable.Set.print (Lazy.force decl.invariant_params)
      (Misc.Stdlib.Option.print Format.pp_print_int) (Lazy.force decl.size)
      (Misc.Stdlib.Option.print Closure_id.print) decl.direct_call_surrogate

  and print_non_inlinable_function_declaration ppf
        (decl : non_inlinable_function_declaration) =
    Format.fprintf ppf
      "@[(non_inlinable@ \
        @[(result (%a))@]@,\
        @[(direct_call_surrogate %a)@])@]"
      (Format.pp_print_list ~pp_sep:(fun ppf () -> Format.fprintf ppf ", ")
        (fun ppf ty ->
          Format.fprintf ppf "%a"
            print ty)) decl.result
      (Misc.Stdlib.Option.print Closure_id.print) decl.direct_call_surrogate

  and print_function_declaration ppf (decl : function_declaration) =
    match decl with
    | Inlinable decl -> print_inlinable_function_declaration ppf decl
    | Non_inlinable decl -> print_non_inlinable_function_declaration ppf decl

  and print_function_declarations ppf function_decls =
    Format.fprintf ppf "%a"
      (Closure_id.Map.print print_function_declaration)
      function_decls

  and print_set_of_closures ppf set =
    Format.fprintf ppf
      "@[(@[(set_of_closures_id@ %a)@]@,\
          @[(set_of_closures_origin@ %a)@]@,\
          @[(function_decls@ %a)@]@,\
          @[(closure_elements@ %a)@])@]"
      Set_of_closures_id.print set.set_of_closures_id
      Set_of_closures_origin.print set.set_of_closures_origin
      print_function_declarations set.function_decls
      (Var_within_closure.Map.print print_ty_value) set.closure_elements

  and print_ty_naked_immediate ppf (ty : ty_naked_immediate) =
    print_ty_generic print_of_kind_naked_immediate (fun _ () -> ()) ppf ty

  and print_ty_naked_float ppf (ty : ty_naked_float) =
    print_ty_generic print_of_kind_naked_float (fun _ () -> ()) ppf ty

  and print_ty_naked_int32 ppf (ty : ty_naked_int32) =
    print_ty_generic print_of_kind_naked_int32 (fun _ () -> ()) ppf ty

  and print_ty_naked_int64 ppf (ty : ty_naked_int64) =
    print_ty_generic print_of_kind_naked_int64 (fun _ () -> ()) ppf ty

  and print_ty_naked_nativeint ppf (ty : ty_naked_nativeint) =
    print_ty_generic print_of_kind_naked_nativeint (fun _ () -> ()) ppf ty

  and print_resolved_ty_set_of_closures ppf
        (ty : resolved_ty_set_of_closures) =
    print_resolved_ty_generic print_set_of_closures (fun _ () -> ()) ppf ty

  and print ppf (t : t) =
    match t with
    | Value ty ->
      Format.fprintf ppf "(Value (%a))" print_ty_value ty
    | Naked_immediate ty ->
      Format.fprintf ppf "(Naked_immediate (%a))" print_ty_naked_immediate ty
    | Naked_float ty ->
      Format.fprintf ppf "(Naked_float (%a))" print_ty_naked_float ty
    | Naked_int32 ty ->
      Format.fprintf ppf "(Naked_int32 (%a))" print_ty_naked_int32 ty
    | Naked_int64 ty ->
      Format.fprintf ppf "(Naked_int64 (%a))" print_ty_naked_int64 ty
    | Naked_nativeint ty ->
      Format.fprintf ppf "(Naked_nativeint (%a))" print_ty_naked_nativeint ty

  let augment_with_variable (t : t) var : t =
    match t with
    | Value ty ->
      begin match ty.var with
      | None -> Value { ty with var = Some var; }
      | Some _ -> t
      end
    | Naked_immediate ty ->
      begin match ty.var with
      | None -> Naked_immediate { ty with var = Some var; }
      | Some _ -> t
      end
    | Naked_float ty ->
      begin match ty.var with
      | None -> Naked_float { ty with var = Some var; }
      | Some _ -> t
      end
    | Naked_int32 ty ->
      begin match ty.var with
      | None -> Naked_int32 { ty with var = Some var; }
      | Some _ -> t
      end
    | Naked_int64 ty ->
      begin match ty.var with
      | None -> Naked_int64 { ty with var = Some var; }
      | Some _ -> t
      end
    | Naked_nativeint ty ->
      begin match ty.var with
      | None -> Naked_nativeint { ty with var = Some var; }
      | Some _ -> t
      end

  let augment_with_symbol_internal (t : t) symbol field : t =
    let symbol = Some (symbol, field) in
    match t with
    | Value ty -> Value { ty with symbol; }
    | Naked_immediate ty -> Naked_immediate { ty with symbol; }
    | Naked_float ty -> Naked_float { ty with symbol; }
    | Naked_int32 ty -> Naked_int32 { ty with symbol; }
    | Naked_int64 ty -> Naked_int64 { ty with symbol; }
    | Naked_nativeint ty -> Naked_nativeint { ty with symbol; }

  let augment_with_symbol t symbol =
    augment_with_symbol_internal t symbol None

  let augment_with_symbol_field t symbol ~field =
    augment_with_symbol_internal t symbol (Some field)

  let replace_variable (t : t) var : t =
    match t with
    | Value ty -> Value { ty with var; }
    | Naked_immediate ty -> Naked_immediate { ty with var; }
    | Naked_float ty -> Naked_float { ty with var; }
    | Naked_int32 ty -> Naked_int32 { ty with var; }
    | Naked_int64 ty -> Naked_int64 { ty with var; }
    | Naked_nativeint ty -> Naked_nativeint { ty with var; }

  let unknown_as_ty_value reason scanning : ty_value =
    { descr = Ok (Unknown (reason, scanning));
      var = None;
      symbol = None;
    }

  let unknown_as_resolved_ty_value reason scanning : resolved_ty_value =
    { descr = Unknown (reason, scanning);
      var = None;
      symbol = None;
    }

  let unknown_as_resolved_ty_naked_immediate reason scanning
        : resolved_ty_naked_immediate =
    { descr = Unknown (reason, scanning);
      var = None;
      symbol = None;
    }

  let unknown_as_resolved_ty_naked_float reason scanning
        : resolved_ty_naked_float =
    { descr = Unknown (reason, scanning);
      var = None;
      symbol = None;
    }

  let unknown_as_resolved_ty_naked_int32 reason scanning
        : resolved_ty_naked_int32 =
    { descr = Unknown (reason, scanning);
      var = None;
      symbol = None;
    }

  let unknown_as_resolved_ty_naked_int64 reason scanning
        : resolved_ty_naked_int64 =
    { descr = Unknown (reason, scanning);
      var = None;
      symbol = None;
    }

  let unknown_as_resolved_ty_naked_nativeint reason scanning
        : resolved_ty_naked_nativeint =
    { descr = Unknown (reason, scanning);
      var = None;
      symbol = None;
    }

  let bottom (kind : K.t) : t =
    match kind with
    | Value _ ->
      Value {
        descr = Ok Bottom;
        var = None;
        symbol = None;
      }
    | Naked_immediate ->
      Naked_immediate {
        descr = Ok Bottom;
        var = None;
        symbol = None;
      }
    | Naked_float ->
      Naked_float {
        descr = Ok Bottom;
        var = None;
        symbol = None;
      }
    | Naked_int32 ->
      Naked_int32 {
        descr = Ok Bottom;
        var = None;
        symbol = None;
      }
    | Naked_int64 ->
      Naked_int64 {
        descr = Ok Bottom;
        var = None;
        symbol = None;
      }
    | Naked_nativeint ->
      Naked_nativeint {
        descr = Ok Bottom;
        var = None;
        symbol = None;
      }

  let this_naked_immediate (i : Immediate.t) : t =
    let i : of_kind_naked_immediate = Naked_immediate i in
    Naked_immediate {
      descr = Ok (Ok i);
      var = None;
      symbol = None;
    }

  let this_naked_float f : t =
    let f : of_kind_naked_float = Naked_float f in
    Naked_float {
      descr = Ok (Ok f);
      var = None;
      symbol = None;
    }

  let this_naked_int32 n : t =
    let n : of_kind_naked_int32 = Naked_int32 n in
    Naked_int32 {
      descr = Ok (Ok n);
      var = None;
      symbol = None;
    }

  let this_naked_int64 n =
    let n : of_kind_naked_int64 = Naked_int64 n in
    Naked_int64 {
      descr = Ok (Ok n);
      var = None;
      symbol = None;
    }

  let this_naked_nativeint n : t =
    let n : of_kind_naked_nativeint = Naked_nativeint n in
    Naked_nativeint {
      descr = Ok (Ok n);
      var = None;
      symbol = None;
    }

  let tag_immediate (t : t) : t =
    match t with
    | Naked_immediate ty_naked_immediate ->
      Value {
        descr = Ok (Ok (Singleton (Tagged_immediate ty_naked_immediate)));
        var = None;
        symbol = None;
      }
    | Value _
    | Naked_float _
    | Naked_int32 _
    | Naked_int64 _
    | Naked_nativeint _ ->
      Misc.fatal_errorf "Expected type of kind [Naked_immediate] but got %a"
        print t

  let box_float (t : t) : t =
    match t with
    | Naked_float ty_naked_float ->
      Value {
        descr = Ok (Ok (Singleton (Boxed_float ty_naked_float)));
        var = None;
        symbol = None;
      }
    | Value _
    | Naked_immediate _
    | Naked_int32 _
    | Naked_int64 _
    | Naked_nativeint _ ->
      Misc.fatal_errorf "Expected type of kind [Naked_float] but got %a"
        print t

  let box_int32 (t : t) : t =
    match t with
    | Naked_int32 ty_naked_int32 ->
      Value {
        descr = Ok (Ok (Singleton (Boxed_int32 ty_naked_int32)));
        var = None;
        symbol = None;
      }
    | Value _
    | Naked_immediate _
    | Naked_float _
    | Naked_int64 _
    | Naked_nativeint _ ->
      Misc.fatal_errorf "Expected type of kind [Naked_int32] but got %a"
        print t

  let box_int64 (t : t) : t =
    match t with
    | Naked_int64 ty_naked_int64 ->
      Value {
        descr = Ok (Ok (Singleton (Boxed_int64 ty_naked_int64)));
        var = None;
        symbol = None;
      }
    | Value _
    | Naked_immediate _
    | Naked_float _
    | Naked_int32 _
    | Naked_nativeint _ ->
      Misc.fatal_errorf "Expected type of kind [Naked_int64] but got %a"
        print t

  let box_nativeint (t : t) : t =
    match t with
    | Naked_nativeint ty_naked_nativeint ->
      Value {
        descr = Ok (Ok (Singleton (Boxed_nativeint ty_naked_nativeint)));
        var = None;
        symbol = None;
      }
    | Value _
    | Naked_immediate _
    | Naked_float _
    | Naked_int32 _
    | Naked_int64 _ ->
      Misc.fatal_errorf "Expected type of kind [Naked_nativeint] but got %a"
        print t

  let this_tagged_immediate i : t =
    let i : ty_naked_immediate =
      let i : of_kind_naked_immediate = Naked_immediate i in
      { descr = Ok (Ok i);
        var = None;
        symbol = None;
      }
    in
    Value {
      descr = Ok (Ok (Singleton (Tagged_immediate i)));
      var = None;
      symbol = None;
    }

  let this_boxed_float f =
    let f : ty_naked_float =
      let f : of_kind_naked_float = Naked_float f in
      { descr = Ok (Ok f);
        var = None;
        symbol = None;
      }
    in
    Value {
      descr = Ok (Ok (Singleton (Boxed_float f)));
      var = None;
      symbol = None;
    }

  let this_boxed_int32 n =
    let n : ty_naked_int32 =
      let n : of_kind_naked_int32 = Naked_int32 n in
      { descr = Ok (Ok n);
        var = None;
        symbol = None;
      }
    in
    Value {
      descr = Ok (Ok (Singleton (Boxed_int32 n)));
      var = None;
      symbol = None;
    }

  let this_boxed_int64 n =
    let n : ty_naked_int64 =
      let n : of_kind_naked_int64 = Naked_int64 n in
      { descr = Ok (Ok n);
        var = None;
        symbol = None;
      }
    in
    Value {
      descr = Ok (Ok (Singleton (Boxed_int64 n)));
      var = None;
      symbol = None;
    }

  let this_boxed_nativeint n =
    let n : ty_naked_nativeint =
      let n : of_kind_naked_nativeint = Naked_nativeint n in
      { descr = Ok (Ok n);
        var = None;
        symbol = None;
      }
    in
    Value {
      descr = Ok (Ok (Singleton (Boxed_nativeint n)));
      var = None;
      symbol = None;
    }

  let this_immutable_string_as_ty_value str : ty_value =
    let string_ty : string_ty =
      { contents = Contents str;
        size = String.length str;
      }
    in
    { descr = Ok (Ok (Singleton (String string_ty)));
      var = None;
      symbol = None;
    }

  let this_immutable_string str : t =
    Value (this_immutable_string_as_ty_value str)

  let mutable_string ~size : t =
    let string_ty : string_ty =
      { contents = Unknown_or_mutable;
        size;
      }
    in
    Value {
      descr = Ok (Ok (Singleton (String string_ty)));
      var = None;
      symbol = None;
    }

  (* CR mshinwell: We need to think about these float array functions in
     conjunction with the 4.06 feature for disabling the float array
     optimisation *)

  let this_immutable_float_array fields : t =
    let make_field f : ty_naked_float =
      let f : of_kind_naked_float = Naked_float f in
      { descr = Ok (Ok f);
        var = None;
        symbol = None;
      }
    in
    let fields = Array.map make_field fields in
    Value {
      descr = Ok (Ok (Singleton (Float_array fields)));
      var = None;
      symbol = None;
    }

  let immutable_float_array fields : t =
    let fields =
      Array.map (fun (field : t) ->
          match field with
          | Naked_float ty_naked_float -> ty_naked_float
          | Value _ | Naked_immediate _ | Naked_int32 _ | Naked_int64 _
          | Naked_nativeint _ ->
            Misc.fatal_errorf "Can only form [Float_array] types with fields \
                of kind [Naked_float].  Wrong field type: %a"
              print field)
        fields
    in
    Value {
      descr = Ok (Ok (Singleton (Float_array fields)));
      var = None;
      symbol = None;
    }

  let mutable_float_array ~size : t =
    let make_field () : ty_naked_float =
      { descr = Ok (Unknown (Other, ()));
        var = None;
        symbol = None;
      }
    in
    let fields = Array.init size (fun _ -> make_field ()) in
    Value {
      descr = Ok (Ok (Singleton (Float_array fields)));
      var = None;
      symbol = None;
    }

  let block tag fields : t =
    let fields =
      Array.map (fun (field : t) ->
          match field with
          | Value ty_value -> ty_value
          | Naked_immediate _ | Naked_float _ | Naked_int32 _ | Naked_int64 _
          | Naked_nativeint _ ->
            Misc.fatal_errorf "Can only form [Block] types with fields of \
                kind [Value].  Wrong field type: %a"
              print field)
        fields
    in
    Value {
      descr = Ok (Ok (Singleton (Block (tag, fields))));
      var = None;
      symbol = None;
    }

  let export_id_loaded_lazily (kind : K.t) export_id : t =
    match kind with
    | Value _ ->
      Value {
        descr = Load_lazily (Export_id export_id);
        var = None;
        symbol = None;
      }
    | Naked_immediate ->
      Naked_immediate {
        descr = Load_lazily (Export_id export_id);
        var = None;
        symbol = None;
      }
    | Naked_float ->
      Naked_float {
        descr = Load_lazily (Export_id export_id);
        var = None;
        symbol = None;
      }
    | Naked_int32 ->
      Naked_int32 {
        descr = Load_lazily (Export_id export_id);
        var = None;
        symbol = None;
      }
    | Naked_int64 ->
      Naked_int64 {
        descr = Load_lazily (Export_id export_id);
        var = None;
        symbol = None;
      }
    | Naked_nativeint ->
      Naked_nativeint {
        descr = Load_lazily (Export_id export_id);
        var = None;
        symbol = None;
      }

  let symbol_loaded_lazily sym : t =
    Value {
      descr = Load_lazily (Symbol sym);
      var = None;
      symbol = None;
    }

  let any_naked_immediate () : t =
    Naked_immediate
      { descr = Ok (Unknown (Other, ()));
        var = None;
        symbol = None;
      }

  let any_naked_float () : t =
    Naked_float
      { descr = Ok (Unknown (Other, ()));
        var = None;
        symbol = None;
      }

  let any_naked_int32 () : t =
    Naked_int32
      { descr = Ok (Unknown (Other, ()));
        var = None;
        symbol = None;
      }

  let any_naked_int64 () : t =
    Naked_int64
      { descr = Ok (Unknown (Other, ()));
        var = None;
        symbol = None;
      }

  let any_naked_nativeint () : t =
    Naked_nativeint
      { descr = Ok (Unknown (Other, ()));
        var = None;
        symbol = None;
      }

  let any_value_as_ty_value scanning unknown_because_of : ty_value =
    { descr = Ok (Unknown (unknown_because_of, scanning));
      var = None;
      symbol = None;
    }

  let any_value scanning unknown_because_of : t =
    Value (any_value_as_ty_value scanning unknown_because_of)

  let unknown (kind : K.t) unknown_because_of =
    match kind with
    | Value scanning -> any_value scanning unknown_because_of
    | Naked_immediate -> any_naked_immediate ()
    | Naked_float -> any_naked_float ()
    | Naked_int32 -> any_naked_int32 ()
    | Naked_int64 -> any_naked_int64 ()
    | Naked_nativeint -> any_naked_nativeint ()

  let any_tagged_immediate () : t =
    let i : ty_naked_immediate =
      { descr = Ok (Unknown (Other, ()));
        var = None;
        symbol = None;
      }
    in
    Value {
      descr = Ok (Ok (Singleton (Tagged_immediate i)));
      var = None;
      symbol = None;
    }

  let any_boxed_float () =
    let f : ty_naked_float =
      { descr = Ok (Unknown (Other, ()));
        var = None;
        symbol = None;
      }
    in
    Value {
      descr = Ok (Ok (Singleton (Boxed_float f)));
      var = None;
      symbol = None;
    }

  let any_boxed_int32 () =
    let n : ty_naked_int32 =
      { descr = Ok (Unknown (Other, ()));
        var = None;
        symbol = None;
      }
    in
    Value {
      descr = Ok (Ok (Singleton (Boxed_int32 n)));
      var = None;
      symbol = None;
    }

  let any_boxed_int64 () =
    let n : ty_naked_int64 =
      { descr = Ok (Unknown (Other, ()));
        var = None;
        symbol = None;
      }
    in
    Value {
      descr = Ok (Ok (Singleton (Boxed_int64 n)));
      var = None;
      symbol = None;
    }

  let any_boxed_nativeint () =
    let n : ty_naked_nativeint =
      { descr = Ok (Unknown (Other, ()));
        var = None;
        symbol = None;
      }
    in
    Value {
      descr = Ok (Ok (Singleton (Boxed_nativeint n)));
      var = None;
      symbol = None;
    }

  let resolved_ty_value_for_predefined_exception ~name ~symbol
        : resolved_ty_value =
    let fields =
      [| this_immutable_string_as_ty_value name;
         unknown_as_ty_value Other Must_scan;
      |]
    in
    { descr = Ok (Singleton (Block (Tag.Scannable.object_tag, fields)));
      var = None;
      symbol = Some (symbol, None);
    }

  module type Importer = sig
    val import_value_type_as_resolved_ty_value
       : ty_value
      -> resolved_ty_value

    val import_naked_immediate_type_as_resolved_ty_naked_immediate
       : ty_naked_immediate
      -> resolved_ty_naked_immediate

    val import_naked_float_type_as_resolved_ty_naked_float
       : ty_naked_float
      -> resolved_ty_naked_float

    val import_naked_int32_type_as_resolved_ty_naked_int32
       : ty_naked_int32
      -> resolved_ty_naked_int32

    val import_naked_int64_type_as_resolved_ty_naked_int64
       : ty_naked_int64
      -> resolved_ty_naked_int64

    val import_naked_nativeint_type_as_resolved_ty_naked_nativeint
       : ty_naked_nativeint
      -> resolved_ty_naked_nativeint

    val import_value_type : ty_value -> resolved_t
    val import_naked_immediate_type : ty_naked_immediate -> resolved_t
    val import_naked_float_type : ty_naked_float -> resolved_t
    val import_naked_int32_type : ty_naked_int32 -> resolved_t
    val import_naked_int64_type : ty_naked_int64 -> resolved_t
    val import_naked_nativeint_type : ty_naked_nativeint -> resolved_t
  end

  module type Importer_intf = sig
    val import_export_id : Export_id.t -> t option
    val import_symbol : Symbol.t -> t option
    val symbol_is_predefined_exception : Symbol.t -> string option
  end

  type 'a with_importer = importer:(module Importer) -> 'a

  type 'a create_resolved_t_result =
    | Ok of 'a
    | Load_lazily_again of load_lazily

  module Make_importer (S : Importer_intf) : Importer = struct
    type 'a import_result =
      | Ok of 'a
      | Treat_as_unknown_must_scan of unknown_because_of

    let import_type (type a) ll
          ~(create_resolved_t : t -> a create_resolved_t_result)
          ~(resolve_predefined_exception : Symbol.t -> a option) =
      let rec import_type (ll : load_lazily) ~export_ids_seen ~symbols_seen
            : a import_result =
        match ll with
        | Export_id id ->
          if Export_id.Set.mem id export_ids_seen then begin
            Misc.fatal_errorf "Circularity whilst resolving export ID %a"
              Export_id.print id
          end;
          begin match S.import_export_id id with
          | None -> Treat_as_unknown_must_scan (Unresolved_value (Export_id id))
          | Some t ->
            match create_resolved_t t with
            | Ok resolved_t -> Ok resolved_t
            | Load_lazily_again ll ->
              let export_ids_seen = Export_id.Set.add id export_ids_seen in
              import_type ll ~export_ids_seen ~symbols_seen
          end
        | Symbol sym ->
          match resolve_predefined_exception sym with
          | Some resolved_t -> Ok resolved_t
          | None ->
            if Symbol.Set.mem sym symbols_seen then begin
              Misc.fatal_errorf "Circularity whilst resolving symbol %a"
                Symbol.print sym
            end;
            begin match S.import_symbol sym with
            | None -> Treat_as_unknown_must_scan (Unresolved_value (Symbol sym))
            | Some t ->
              match create_resolved_t t with
              (* CR mshinwell: We used to [augment_with_symbol] here but maybe
                 we don't need it any more? *)
              | Ok resolved_t -> Ok resolved_t
              | Load_lazily_again ll ->
                let symbols_seen =
                  Symbol.Set.add sym symbols_seen
                in
                import_type ll ~export_ids_seen ~symbols_seen
            end
      in
      import_type ll ~export_ids_seen:Export_id.Set.empty
        ~symbols_seen:Symbol.Set.empty

    let import_value_type_as_resolved_ty_value (ty : ty_value)
          : resolved_ty_value =
      match ty.descr with
      | Ok descr ->
        { descr;
          var = ty.var;
          symbol = ty.symbol;
        }
      | Load_lazily load_lazily ->
        let resolve_predefined_exception sym =
          match S.symbol_is_predefined_exception sym with
          | None -> None
          | Some name ->
            Some (resolved_ty_value_for_predefined_exception ~name ~symbol:sym)
        in
        let create_resolved_t t : resolved_ty_value create_resolved_t_result =
          match t with
          | Value ty ->
            begin match ty.descr with
            | Ok descr ->
              Ok {
                descr;
                var = ty.var;
                symbol = ty.symbol;
              }
            | Load_lazily ll -> Load_lazily_again ll
            end
          | Naked_immediate _
          | Naked_float _
          | Naked_int32 _
          | Naked_int64 _
          | Naked_nativeint _ ->
            Misc.fatal_errorf "Kind mismatch when importing %a; expected kind \
                [Value]"
              print_load_lazily load_lazily
        in
        let result =
          import_type load_lazily ~create_resolved_t
            ~resolve_predefined_exception
        in
        match result with
        | Ok result -> result
        | Treat_as_unknown_must_scan reason ->
          unknown_as_resolved_ty_value reason Must_scan

    let import_value_type ty : resolved_t =
      Value (import_value_type_as_resolved_ty_value ty)

    let import_naked_immediate_type_as_resolved_ty_naked_immediate
          (ty : ty_naked_immediate) : resolved_ty_naked_immediate =
      match ty.descr with
      | Ok descr ->
        { descr;
          var = ty.var;
          symbol = ty.symbol;
        }
      | Load_lazily load_lazily ->
        let resolve_predefined_exception _sym = None in
        let create_resolved_t t
              : resolved_ty_naked_immediate create_resolved_t_result =
          match t with
          | Naked_immediate ty ->
            begin match ty.descr with
            | Ok descr ->
              Ok {
                descr;
                var = ty.var;
                symbol = ty.symbol;
              }
            | Load_lazily ll -> Load_lazily_again ll
            end
          | Value _
          | Naked_float _
          | Naked_int32 _
          | Naked_int64 _
          | Naked_nativeint _ ->
            Misc.fatal_errorf "Kind mismatch when importing %a; expected kind \
                [Naked_immediate]"
              print_load_lazily load_lazily
        in
        let result =
          import_type load_lazily ~create_resolved_t
            ~resolve_predefined_exception
        in
        match result with
        | Ok result -> result
        | Treat_as_unknown_must_scan reason ->
          unknown_as_resolved_ty_naked_immediate reason ()

    let import_naked_immediate_type ty : resolved_t =
      Naked_immediate (
        import_naked_immediate_type_as_resolved_ty_naked_immediate ty)

    let import_naked_float_type_as_resolved_ty_naked_float
          (ty : ty_naked_float) : resolved_ty_naked_float =
      match ty.descr with
      | Ok descr ->
        { descr;
          var = ty.var;
          symbol = ty.symbol;
        }
      | Load_lazily load_lazily ->
        let resolve_predefined_exception _sym = None in
        let create_resolved_t t
              : resolved_ty_naked_float create_resolved_t_result =
          match t with
          | Naked_float ty ->
            begin match ty.descr with
            | Ok descr ->
              Ok {
                descr;
                var = ty.var;
                symbol = ty.symbol;
              }
            | Load_lazily ll -> Load_lazily_again ll
            end
          | Value _
          | Naked_immediate _
          | Naked_int32 _
          | Naked_int64 _
          | Naked_nativeint _ ->
            Misc.fatal_errorf "Kind mismatch when importing %a; expected kind \
                [Naked_float]"
              print_load_lazily load_lazily
        in
        let result =
          import_type load_lazily ~create_resolved_t
            ~resolve_predefined_exception
        in
        match result with
        | Ok result -> result
        | Treat_as_unknown_must_scan reason ->
          unknown_as_resolved_ty_naked_float reason ()

    let import_naked_float_type ty : resolved_t =
      Naked_float (import_naked_float_type_as_resolved_ty_naked_float ty)

    let import_naked_int32_type_as_resolved_ty_naked_int32
          (ty : ty_naked_int32) : resolved_ty_naked_int32 =
      match ty.descr with
      | Ok descr ->
        { descr;
          var = ty.var;
          symbol = ty.symbol;
        }
      | Load_lazily load_lazily ->
        let resolve_predefined_exception _sym = None in
        let create_resolved_t t
              : resolved_ty_naked_int32 create_resolved_t_result =
          match t with
          | Naked_int32 ty ->
            begin match ty.descr with
            | Ok descr ->
              Ok {
                descr;
                var = ty.var;
                symbol = ty.symbol;
              }
            | Load_lazily ll -> Load_lazily_again ll
            end
          | Value _
          | Naked_immediate _
          | Naked_float _
          | Naked_int64 _
          | Naked_nativeint _ ->
            Misc.fatal_errorf "Kind mismatch when importing %a; expected kind \
                [Naked_int32]"
              print_load_lazily load_lazily
        in
        let result =
          import_type load_lazily ~create_resolved_t
            ~resolve_predefined_exception
        in
        match result with
        | Ok result -> result
        | Treat_as_unknown_must_scan reason ->
          unknown_as_resolved_ty_naked_int32 reason ()

    let import_naked_int32_type ty : resolved_t =
      Naked_int32 (import_naked_int32_type_as_resolved_ty_naked_int32 ty)

    let import_naked_int64_type_as_resolved_ty_naked_int64
          (ty : ty_naked_int64) : resolved_ty_naked_int64 =
      match ty.descr with
      | Ok descr ->
        { descr;
          var = ty.var;
          symbol = ty.symbol;
        }
      | Load_lazily load_lazily ->
        let resolve_predefined_exception _sym = None in
        let create_resolved_t t
              : resolved_ty_naked_int64 create_resolved_t_result =
          match t with
          | Naked_int64 ty ->
            begin match ty.descr with
            | Ok descr ->
              Ok {
                descr;
                var = ty.var;
                symbol = ty.symbol;
              }
            | Load_lazily ll -> Load_lazily_again ll
            end
          | Value _
          | Naked_immediate _
          | Naked_float _
          | Naked_int32 _
          | Naked_nativeint _ ->
            Misc.fatal_errorf "Kind mismatch when importing %a; expected kind \
                [Naked_int64]"
              print_load_lazily load_lazily
        in
        let result =
          import_type load_lazily ~create_resolved_t
            ~resolve_predefined_exception
        in
        match result with
        | Ok result -> result
        | Treat_as_unknown_must_scan reason ->
          unknown_as_resolved_ty_naked_int64 reason ()

    let import_naked_int64_type ty : resolved_t =
      Naked_int64 (import_naked_int64_type_as_resolved_ty_naked_int64 ty)

    let import_naked_nativeint_type_as_resolved_ty_naked_nativeint
          (ty : ty_naked_nativeint) : resolved_ty_naked_nativeint =
      match ty.descr with
      | Ok descr ->
        { descr;
          var = ty.var;
          symbol = ty.symbol;
        }
      | Load_lazily load_lazily ->
        let resolve_predefined_exception _sym = None in
        let create_resolved_t t
              : resolved_ty_naked_nativeint create_resolved_t_result =
          match t with
          | Naked_nativeint ty ->
            begin match ty.descr with
            | Ok descr ->
              Ok {
                descr;
                var = ty.var;
                symbol = ty.symbol;
              }
            | Load_lazily ll -> Load_lazily_again ll
            end
          | Value _
          | Naked_immediate _
          | Naked_float _
          | Naked_int32 _
          | Naked_int64 _ ->
            Misc.fatal_errorf "Kind mismatch when importing %a; expected kind \
                [Naked_nativeint]"
              print_load_lazily load_lazily
        in
        let result =
          import_type load_lazily ~create_resolved_t
            ~resolve_predefined_exception
        in
        match result with
        | Ok result -> result
        | Treat_as_unknown_must_scan reason ->
          unknown_as_resolved_ty_naked_nativeint reason ()

    let import_naked_nativeint_type ty : resolved_t =
      Naked_nativeint (
        import_naked_nativeint_type_as_resolved_ty_naked_nativeint ty)
  end

  (* CR pchambart:  (This was written for the "join" case)
     merging the closure value might loose information in the
     case of one branch having the approximation and the other
     having 'Unknown'. We could imagine such as

     {[if ... then M1.f else M2.f]}

     where M1 is where the function is defined and M2 is

     {[let f = M3.f]}

     and M3 is

     {[let f = M1.f]}

     with the cmx for M3 missing

     Since we know that the approximation comes from the same
     value, we know that both version provide additional
     information on the value. Hence what we really want is an
     approximation intersection, not an union (that this join
     is).
     mshinwell: changed to meet *)

  let must_scan_of_kind_value_or_unknown_or_bottom
        (o : (of_kind_value, _) or_unknown_or_bottom) : K.scanning =
    match o with
    | Unknown _ -> Must_scan
    | Bottom -> Can_scan
    | Ok of_kind_value ->
      let rec must_scan_of_kind_value (o : of_kind_value) : K.scanning =
        match o with
        | Singleton (Tagged_immediate _) -> Can_scan
        | Singleton _ -> Must_scan
        | Union (w1, w2) ->
          K.join_scanning (must_scan_of_kind_value w1.descr)
            (must_scan_of_kind_value w2.descr)
      in
      must_scan_of_kind_value of_kind_value

  let scanning_ty_value ~importer (ty : ty_value) =
    let module I = (val importer : Importer) in
    let resolved_ty_value = I.import_value_type_as_resolved_ty_value ty in
    must_scan_of_kind_value_or_unknown_or_bottom resolved_ty_value.descr

  let kind_ty_value ~importer (ty : ty_value) =
    let scanning = scanning_ty_value ~importer (ty : ty_value) in
    K.value scanning

  let kind ~importer (t : t) =
    match t with
    | Naked_immediate _ -> K.naked_immediate ()
    | Naked_float _ -> K.naked_float ()
    | Naked_int32 _ -> K.naked_int32 ()
    | Naked_int64 _ -> K.naked_int64 ()
    | Naked_nativeint _ -> K.naked_nativeint ()
    | Value ty -> kind_ty_value ~importer ty

  let create_inlinable_function_declaration ~is_classic_mode ~closure_origin
        ~continuation_param ~params ~body ~result ~stub ~dbg ~inline
        ~specialise ~is_a_functor ~invariant_params ~size ~direct_call_surrogate
        : inlinable_function_declaration =
    { closure_origin;
      continuation_param;
      is_classic_mode;
      params;
      body;
      free_symbols = Expr.free_symbols body;
      result;
      stub;
      dbg;
      inline;
      specialise;
      is_a_functor;
      invariant_params;
      size;
      direct_call_surrogate;
    }

  let create_non_inlinable_function_declaration ~result ~direct_call_surrogate
        : non_inlinable_function_declaration =
    { result;
      direct_call_surrogate;
    }

  let create_set_of_closures ~set_of_closures_id ~set_of_closures_origin
        ~function_decls ~closure_elements : set_of_closures =
    { set_of_closures_id;
      set_of_closures_origin;
      function_decls;
      closure_elements;
    }

  let closure ?closure_var ?set_of_closures_var ?set_of_closures_symbol
        set_of_closures closure_id : t =
    let set_of_closures : resolved_ty_set_of_closures =
      let symbol =
        match set_of_closures_symbol with
        | None -> None
        | Some symbol ->
          Some (symbol, None)
      in
      { descr = Ok set_of_closures;
        var = set_of_closures_var;
        symbol;
      }
    in
    Value {
      descr = Ok (Ok (Singleton (Closure { set_of_closures; closure_id; })));
      var = closure_var;
      symbol = None;
    }

  let set_of_closures ?set_of_closures_var ?set_of_closures_symbol
        set_of_closures : t =
    let symbol =
      match set_of_closures_symbol with
      | None -> None
      | Some symbol ->
        Some (symbol, None)
    in
    Value {
      descr = Ok (Ok (Singleton (Set_of_closures set_of_closures)));
      var = set_of_closures_var;
      symbol;
    }

  let rec free_variables t acc =
    match t with
    | Value ty -> free_variables_ty_value ty acc
    | Naked_immediate ty -> free_variables_ty_naked_immediate ty acc
    | Naked_float ty -> free_variables_ty_naked_float ty acc
    | Naked_int32 ty -> free_variables_ty_naked_int32 ty acc
    | Naked_int64 ty -> free_variables_ty_naked_int64 ty acc
    | Naked_nativeint ty -> free_variables_ty_naked_nativeint ty acc

  and free_variables_ty_value ({ descr; var; _ } : ty_value) acc =
    let acc =
      match var with
      | None -> acc
      | Some var -> Variable.Set.add var acc
    in
    match descr with
    | Ok ((Unknown _) | Bottom) -> acc
    | Ok (Ok of_kind_value) ->
      free_variables_of_kind_value of_kind_value acc
    | Load_lazily _load_lazily ->
      (* Types saved in .cmx files cannot contain free variables. *)
      acc

  and free_variables_ty_naked_immediate ({ var; _ } : ty_naked_immediate) acc =
    match var with
    | None -> acc
    | Some var -> Variable.Set.add var acc

  and free_variables_ty_naked_float ({ var; _ } : ty_naked_float) acc =
    match var with
    | None -> acc
    | Some var -> Variable.Set.add var acc

  and free_variables_ty_naked_int32 ({ var; _ } : ty_naked_int32) acc =
    match var with
    | None -> acc
    | Some var -> Variable.Set.add var acc

  and free_variables_ty_naked_int64 ({ var; _ } : ty_naked_int64) acc =
    match var with
    | None -> acc
    | Some var -> Variable.Set.add var acc

  and free_variables_ty_naked_nativeint ({ var; _ } : ty_naked_nativeint) acc =
    match var with
    | None -> acc
    | Some var -> Variable.Set.add var acc

  and free_variables_set_of_closures (set_of_closures : set_of_closures) acc =
    let acc =
      Var_within_closure.Map.fold (fun _var ty_value acc ->
          free_variables_ty_value ty_value acc)
        set_of_closures.closure_elements acc
    in
    Closure_id.Map.fold
      (fun _closure_id (decl : function_declaration) acc ->
        match decl with
        | Inlinable decl ->
          let acc =
            List.fold_left (fun acc ty ->
              free_variables ty acc)
              acc
              decl.result
          in
          List.fold_left (fun acc (_param, ty) ->
              free_variables ty acc)
            acc
            decl.params
        | Non_inlinable decl ->
          List.fold_left (fun acc ty ->
            free_variables ty acc)
            acc
            decl.result)
      set_of_closures.function_decls
      acc

  and free_variables_resolved_ty_set_of_closures
        ({ descr; var; _ } : resolved_ty_set_of_closures) acc =
    let acc =
      match var with
      | None -> acc
      | Some var -> Variable.Set.add var acc
    in
    match descr with
    | (Unknown _) | Bottom -> acc
    | Ok (set_of_closures) ->
      free_variables_set_of_closures set_of_closures acc

  and free_variables_of_kind_value (o : of_kind_value) acc =
    match o with
    | Singleton singleton ->
      begin match singleton with
      | Tagged_immediate i ->
        free_variables_ty_naked_immediate i acc
      | Boxed_float f ->
        free_variables_ty_naked_float f acc
      | Boxed_int32 n ->
        free_variables_ty_naked_int32 n acc
      | Boxed_int64 n ->
        free_variables_ty_naked_int64 n acc
      | Boxed_nativeint n ->
        free_variables_ty_naked_nativeint n acc
      | Block (_tag, fields) ->
        Array.fold_left (fun acc t -> free_variables_ty_value t acc)
          acc fields
      | Set_of_closures set_of_closures ->
        free_variables_set_of_closures set_of_closures acc
      | Closure { set_of_closures; closure_id = _; } ->
        free_variables_resolved_ty_set_of_closures set_of_closures acc
      | String _ -> acc
      | Float_array fields ->
        Array.fold_left (fun acc field ->
            free_variables_ty_naked_float field acc)
          acc fields
      end
    | Union (w1, w2) ->
      let acc =
        match w1.var with
        | None -> acc
        | Some var -> Variable.Set.add var acc
      in
      let acc =
        match w2.var with
        | None -> acc
        | Some var -> Variable.Set.add var acc
      in
      free_variables_of_kind_value w2.descr
        (free_variables_of_kind_value w1.descr acc)

  let free_variables t =
    free_variables t Variable.Set.empty

  (* CR mshinwell: We need tests to check that [clean] matches up with
     [free_variables]. *)

  type cleaning_spec =
    | Available
    | Available_different_name of Variable.t
    | Unavailable

  let rec clean ~importer t classify =
    let clean_var var =
      match classify var with
      | Available -> Some var
      | Available_different_name new_var -> Some new_var
      | Unavailable -> None
    in
    let clean_var_opt var_opt =
      match var_opt with
      | None -> None
      | Some var ->
        match clean_var var with
        | None -> None
        | (Some var') as var_opt' ->
          if var == var' then var_opt
          else var_opt'
    in
    clean_t ~importer t clean_var_opt

  and clean_t ~importer (t : t) clean_var_opt : t =
    match t with
    | Value ty ->
      Value (clean_ty_value ~importer ty clean_var_opt)
    | Naked_immediate ty ->
      Naked_immediate (clean_ty_naked_immediate ~importer ty clean_var_opt)
    | Naked_float ty ->
      Naked_float (clean_ty_naked_float ~importer ty clean_var_opt)
    | Naked_int32 ty ->
      Naked_int32 (clean_ty_naked_int32 ~importer ty clean_var_opt)
    | Naked_int64 ty ->
      Naked_int64 (clean_ty_naked_int64 ~importer ty clean_var_opt)
    | Naked_nativeint ty ->
      Naked_nativeint (clean_ty_naked_nativeint ~importer ty clean_var_opt)

  and clean_ty_value ~importer ty_value clean_var_opt : ty_value =
    let module I = (val importer : Importer) in
    let ty_value = I.import_value_type_as_resolved_ty_value ty_value in
    let var = clean_var_opt ty_value.var in
    let descr : (of_kind_value, _) or_unknown_or_bottom =
      match ty_value.descr with
      | (Unknown _) | Bottom -> ty_value.descr
      | Ok of_kind_value ->
        Ok (clean_of_kind_value ~importer of_kind_value clean_var_opt)
    in
    { var;
      symbol = ty_value.symbol;
      descr = Ok descr;
    }

  and clean_resolved_ty_set_of_closures ~importer
        (resolved_ty_set_of_closures : resolved_ty_set_of_closures)
        clean_var_opt
        : resolved_ty_set_of_closures =
    let var = clean_var_opt resolved_ty_set_of_closures.var in
    let descr : (set_of_closures, _) or_unknown_or_bottom =
      match resolved_ty_set_of_closures.descr with
      | (Unknown _) | Bottom -> resolved_ty_set_of_closures.descr
      | Ok set_of_closures ->
        Ok (clean_set_of_closures ~importer set_of_closures clean_var_opt)
    in
    { var;
      symbol = resolved_ty_set_of_closures.symbol;
      descr = descr;
    }

  and clean_ty_naked_immediate ~importer ty_naked_immediate clean_var_opt
        : ty_naked_immediate =
    let module I = (val importer : Importer) in
    let ty_naked_immediate =
      I.import_naked_immediate_type_as_resolved_ty_naked_immediate
        ty_naked_immediate
    in
    let var = clean_var_opt ty_naked_immediate.var in
    { var;
      symbol = ty_naked_immediate.symbol;
      descr = Ok ty_naked_immediate.descr;
    }

  and clean_ty_naked_float ~importer ty_naked_float clean_var_opt
        : ty_naked_float =
    let module I = (val importer : Importer) in
    let ty_naked_float =
      I.import_naked_float_type_as_resolved_ty_naked_float ty_naked_float
    in
    let var = clean_var_opt ty_naked_float.var in
    { var;
      symbol = ty_naked_float.symbol;
      descr = Ok ty_naked_float.descr;
    }

  and clean_ty_naked_int32 ~importer ty_naked_int32 clean_var_opt
        : ty_naked_int32 =
    let module I = (val importer : Importer) in
    let ty_naked_int32 =
      I.import_naked_int32_type_as_resolved_ty_naked_int32 ty_naked_int32
    in
    let var = clean_var_opt ty_naked_int32.var in
    { var;
      symbol = ty_naked_int32.symbol;
      descr = Ok ty_naked_int32.descr;
    }

  and clean_ty_naked_int64 ~importer ty_naked_int64 clean_var_opt
        : ty_naked_int64 =
    let module I = (val importer : Importer) in
    let ty_naked_int64 =
      I.import_naked_int64_type_as_resolved_ty_naked_int64 ty_naked_int64
    in
    let var = clean_var_opt ty_naked_int64.var in
    { var;
      symbol = ty_naked_int64.symbol;
      descr = Ok ty_naked_int64.descr;
    }

  and clean_ty_naked_nativeint ~importer ty_naked_nativeint clean_var_opt
        : ty_naked_nativeint =
    let module I = (val importer : Importer) in
    let ty_naked_nativeint =
      I.import_naked_nativeint_type_as_resolved_ty_naked_nativeint
        ty_naked_nativeint
    in
    let var = clean_var_opt ty_naked_nativeint.var in
    { var;
      symbol = ty_naked_nativeint.symbol;
      descr = Ok ty_naked_nativeint.descr;
    }

  and clean_set_of_closures ~importer set_of_closures clean_var_opt =
    let closure_elements =
      Var_within_closure.Map.map (fun t ->
          clean_ty_value ~importer t clean_var_opt)
        set_of_closures.closure_elements
    in
    let function_decls =
      Closure_id.Map.map
        (fun (decl : function_declaration) : function_declaration ->
          match decl with
          | Inlinable decl ->
            let params =
              List.map (fun (param, t) ->
                  param, clean_t ~importer t clean_var_opt)
                decl.params
            in
            let result =
              List.map (fun ty ->
                clean_t ~importer ty clean_var_opt)
                decl.result
            in
            Inlinable { decl with params; result; }
          | Non_inlinable decl ->
            let result =
              List.map (fun ty ->
                clean_t ~importer ty clean_var_opt)
                decl.result
            in
            Non_inlinable { decl with result; })
        set_of_closures.function_decls
    in
    { set_of_closures with
      function_decls;
      closure_elements;
    }

  and clean_of_kind_value ~importer (o : of_kind_value) clean_var_opt
        : of_kind_value =
    match o with
    | Singleton singleton ->
      let singleton : of_kind_value_singleton =
        match singleton with
        | Tagged_immediate i ->
          Tagged_immediate (clean_ty_naked_immediate ~importer i clean_var_opt)
        | Boxed_float f ->
          Boxed_float (clean_ty_naked_float ~importer f clean_var_opt)
        | Boxed_int32 n ->
          Boxed_int32 (clean_ty_naked_int32 ~importer n clean_var_opt)
        | Boxed_int64 n ->
          Boxed_int64 (clean_ty_naked_int64 ~importer n clean_var_opt)
        | Boxed_nativeint n ->
          Boxed_nativeint (clean_ty_naked_nativeint ~importer n clean_var_opt)
        | Block (tag, fields) ->
          let fields =
            Array.map (fun t -> clean_ty_value ~importer t clean_var_opt)
              fields
          in
          Block (tag, fields)
        | Set_of_closures set_of_closures ->
          Set_of_closures
            (clean_set_of_closures ~importer set_of_closures clean_var_opt)
        | Closure { set_of_closures; closure_id; } ->
          let set_of_closures =
            clean_resolved_ty_set_of_closures ~importer set_of_closures
              clean_var_opt
          in
          Closure { set_of_closures; closure_id; }
        | String _ -> singleton
        | Float_array fields ->
          let fields =
            Array.map (fun field ->
                clean_ty_naked_float ~importer field clean_var_opt)
              fields
          in
          Float_array fields
      in
      Singleton singleton
    | Union (w1, w2) ->
      let w1 =
        { var = clean_var_opt w1.var;
          symbol = w1.symbol;
          descr = clean_of_kind_value ~importer w1.descr clean_var_opt;
        }
      in
      let w2 =
        { var = clean_var_opt w2.var;
          symbol = w2.symbol;
          descr = clean_of_kind_value ~importer w2.descr clean_var_opt;
        }
      in
      Union (w1, w2)

  module Join_or_meet (P : sig
    val description : string
    val is_join : bool
    val absorbing_element : ... -> ...
    val identity_element : ... -> ...
    val operation : ... -> ... -> ...
  end) = struct
    let join_unknown_payload_for_value _descr1 scanning1 descr2 scanning2_opt =
      let scanning2 : K.scanning =
        match scanning2_opt with
        | Some scanning2 -> scanning2
        | None -> must_scan_of_kind_value_or_unknown_or_bottom descr2
      in
      K.join_scanning scanning1 scanning2

    let join_unknown_payload_for_non_value _ty1 () _ty2 (_ : unit option) = ()

    type 'a or_combine =
      | Ok of 'a
      | Combine

    let combine_ty (type a) (type u) ~importer ~importer_this_kind
          ~type_of_var ~type_of_symbol env kind
          combine_contents combine_unknown_payload
          (ty1 : (a, u) ty) (ty2 : (a, u) ty) : (a, u) ty =
      let ty1 : (a, u) resolved_ty = importer_this_kind ty1 in
      let ty2 : (a, u) resolved_ty = importer_this_kind ty2 in
      let resolve_aliases (ty : (a, u) resolved_ty) =
        let rec resolve_aliases vars_seen syms_seen ty =
          match ty with
          | Normal ty -> ty
          | Var var ->
            if Variable.Set.mem var vars_seen then begin
              Misc.fatal_errorf "Loop on %a whilst resolving aliases: %a %s %a"
                Variable.print var
                print_resolved_ty ty1
                description
                print_resolved_ty ty2
            end;
            begin type_of_var env var with
            | None -> ty
            | Some ty ->
              let vars_seen = Variable.Set.add var vars_seen in
              resolve_aliases vars_seen syms_seen (importer_this_kind ty)
            end
          | Symbol sym ->
            if Symbol.Set.mem sym syms_seen then begin
              Misc.fatal_errorf "Loop on %a whilst resolving aliases: %a %s %a"
                Symbol.print sym
                print_resolved_ty ty1
                description
                print_resolved_ty ty2
            end;
            begin type_of_symbol env sym with
            | None -> ty
            | Some ty ->
              let syms_seen = Symbol.Set.add sym syms_seen in
              resolve_aliases vars_seen syms_seen (importer_this_kind ty)
            end
        in
        resolve_aliases Variable.Set.empty Symbol.Set.empty ty
      in
      let ty1 = resolve_aliases ty1 in
      let ty2 = resolve_aliases ty2 in
      match ty1, ty2 with
      | Var var1, Var var2 when Variable.equal var1 var2 -> Var var1
      | Symbol sym1, Symbol sym2 when Symbol.equal sym1 sym2 -> Symbol sym1
      | _, _ ->
        let unresolved_var_or_symbol_to_unknown ty =
          match ty with
          | Normal ty -> ty
          | Var _ | Symbol _ -> P.absorbing_element_of_kind kind
        in
        let ty1 = unresolved_var_or_symbol_to_unknown ty1 in
        let ty2 = unresolved_var_or_symbol_to_unknown ty2 in
        let ty =
          (* Care: we need to handle the payloads of [Unknown]. *)
          match ty1, ty2 with
          | Unknown (reason1, payload1), Unknown (reason2, payload2) ->
            Unknown (combine_unknown_because_of reason1 reason2,
              combine_unknown_payload ty1 payload1
                ty2 (Some payload2))
          | Ok contents1, Ok contents2 ->
            combine_contents ~importer ty1 contents1 ty2 contents2
          | Unknown (reason, payload), _ ->
            if P.is_join then
              Unknown (reason, combine_unknown_payload ty1 payload ty2 None)
            else
              ty2
          | _, Unknown (reason, payload) ->
            if P.is_join then
              Unknown (reason, combine_unknown_payload ty2 payload ty1 None)
            else
              ty1
          | Bottom, _ -> if P.is_join then ty2 else Bottom
          | _, Bottom -> if P.is_join then ty1 else Bottom
        in
        Normal (Ok ty)

    let rec combine_of_kind_value ~importer (t1 : of_kind_value) t2
          : (of_kind_value singleton_or_union, K.scanning)
            or_unknown_or_bottom or_combine =
      let singleton s =
        Ok ((Ok (Singleton s)) : _ or_unknown_or_bottom)
      in
      match t1, t2 with
      | Tagged_immediate ty1, Tagged_immediate ty2 ->
        singleton (Tagged_immediate (join_ty_naked_immediate ~importer ty1 ty2))
      | Boxed_float ty1, Boxed_float ty2 ->
        singleton (Boxed_float (join_ty_naked_float ~importer ty1 ty2))
      | Boxed_int32 ty1, Boxed_int32 ty2 ->
        singleton (Boxed_int32 (join_ty_naked_int32 ~importer ty1 ty2))
      | Boxed_int64 ty1, Boxed_int64 ty2 ->
        singleton (Boxed_int64 (join_ty_naked_int64 ~importer ty1 ty2))
      | Boxed_nativeint ty1, Boxed_nativeint ty2 ->
        singleton (Boxed_nativeint (join_ty_naked_nativeint ~importer ty1 ty2))
      | Block (tag1, fields1), Block (tag2, fields2) ->
          when Tag.Scannable.equal tag1 tag2
            && Array.length fields1 = Array.length fields2 ->
        let fields =
          Array.map2 (fun ty1 ty2 -> join_ty_value ~importer ty1 ty2)
            fields1 fields2
        in
        singleton (Block (tag1, fields))
      | String { contents = Contents str1; _ },
          String { contents = Contents str2; _ } ->
          when String.equal str1 str2 ->
        singleton t1
      | Float_array fields1, Float_array fields2
          when Array.length fields1 = Array.length fields2 ->
        let fields =
          Array.map2 (fun ty1 ty2 -> join_ty_naked_float ~importer ty1 ty2)
            fields1 fields2
        in
        singleton (Float_array fields)
      | _, _ -> Combine

    and join_singleton_or_combination (type k) ~importer ty1 (t1 : k) ty2 t2
          : (k, _) or_unknown_or_bottom =
      let combine () : (k, _) or_unknown_or_bottom =
        let w1 : k or_var_or_symbol =
          { descr = t1;
            var = ty1.var;
            symbol = ty1.symbol;
          }
        in
        let w2 : k or_var_or_symbol =
          { descr = t2;
            var = ty2.var;
            symbol = ty2.symbol;
          }
        in
        Ok (P.combining_op w1 w2)
      in
      match t1, t2 with
      | Singleton s1, Singleton s2 ->
        begin match combine_of_kind_value_singleton ~importer s1 s2 with
        | Ok result -> result
        | Combine -> combine ()
        end
      | Singleton _, Combination _
      | Combination _, Singleton _
      | Combination _, Combination _ -> combine ()

    and join_of_kind_naked_immediate ~importer:_
          ty1 (t1 : of_kind_naked_immediate)
          ty2 (t2 : of_kind_naked_immediate)
          : (of_kind_naked_immediate, _) or_unknown_or_bottom =
      match t1, t2 with
      | Naked_immediate i1, Naked_immediate i2 ->
        if not (Immediate.equal i1 i2) then
          Combine (P.combining_op, ty1, ty2)
        else
          Ok (Singleton ((Naked_immediate i1) : of_kind_naked_immediate))

    and join_of_kind_naked_float ~importer:_
          _ty1 (t1 : of_kind_naked_float) _ty2 (t2 : of_kind_naked_float)
          : (of_kind_naked_float, _) or_unknown_or_bottom =
      match t1, t2 with
      | Naked_float i1, Naked_float i2 ->
        if not (Float.equal i1 i2) then
          Combine (P.combining_op, ty1, ty2)
        else
          Ok (Singleton ((Naked_float i1) : of_kind_naked_float))

    and join_of_kind_naked_int32 ~importer:_
          _ty1 (t1 : of_kind_naked_int32) _ty2 (t2 : of_kind_naked_int32)
          : (of_kind_naked_int32, _) or_unknown_or_bottom =
      match t1, t2 with
      | Naked_int32 i1, Naked_int32 i2 ->
        if not (Int32.equal i1 i2) then
          Combine (P.combining_op, ty1, ty2)
        else
          Ok (Singleton (Naked_int32 i1) : of_kind_naked_int32))

    and join_of_kind_naked_int64 ~importer:_
          _ty1 (t1 : of_kind_naked_int64) _ty2 (t2 : of_kind_naked_int64)
          : (of_kind_naked_int64, _) or_unknown_or_bottom =
      match t1, t2 with
      | Naked_int64 i1, Naked_int64 i2 ->
        if not (Int64.equal i1 i2) then
          Combine (P.combining_op, ty1, ty2)
        else
          Ok (Singleton (Naked_int64 i1) : of_kind_naked_int64))

    and join_of_kind_naked_nativeint ~importer:_
          _ty1 (t1 : of_kind_naked_nativeint)
          _ty2 (t2 : of_kind_naked_nativeint)
          : (of_kind_naked_nativeint, _) or_unknown_or_bottom =
      match t1, t2 with
      | Naked_nativeint i1, Naked_nativeint i2 ->
        if not (Targetint.equal i1 i2) then
          Combine (P.combining_op, ty1, ty2)
        else
          Ok (Singleton ((Naked_nativeint i1) : of_kind_naked_nativeint))

    and join_ty_value ~importer ty1 ty2 =
      let module I = (val importer : Importer) in
      join_ty ~importer
        ~importer_this_kind:I.import_value_type_as_resolved_ty_value
        join_of_kind_value join_unknown_payload_for_value ty1 ty2

    and join_ty_naked_immediate ~importer ty1 ty2 =
      let module I = (val importer : Importer) in
      join_ty ~importer
        ~importer_this_kind:
          I.import_naked_immediate_type_as_resolved_ty_naked_immediate
        join_of_kind_naked_immediate join_unknown_payload_for_non_value ty1 ty2

    and join_ty_naked_float ~importer ty1 ty2 =
      let module I = (val importer : Importer) in
      join_ty ~importer
        ~importer_this_kind:I.import_naked_float_type_as_resolved_ty_naked_float
        join_of_kind_naked_float join_unknown_payload_for_non_value ty1 ty2

    and join_ty_naked_int32 ~importer ty1 ty2 =
      let module I = (val importer : Importer) in
      join_ty ~importer
        ~importer_this_kind:I.import_naked_int32_type_as_resolved_ty_naked_int32
        join_of_kind_naked_int32 join_unknown_payload_for_non_value ty1 ty2

    and join_ty_naked_int64 ~importer ty1 ty2 =
      let module I = (val importer : Importer) in
      join_ty ~importer
        ~importer_this_kind:I.import_naked_int64_type_as_resolved_ty_naked_int64
        join_of_kind_naked_int64 join_unknown_payload_for_non_value ty1 ty2

    and join_ty_naked_nativeint ~importer ty1 ty2 =
      let module I = (val importer : Importer) in
      join_ty ~importer
        ~importer_this_kind:
          I.import_naked_nativeint_type_as_resolved_ty_naked_nativeint
        join_of_kind_naked_nativeint join_unknown_payload_for_non_value ty1 ty2

    let join ~importer (t1 : t) (t2 : t) : t =
      if t1 == t2 then t1
      else
        match t1, t2 with
        | Value ty1, Value ty2 ->
          Value (join_ty_value ~importer ty1 ty2)
        | Naked_immediate ty1, Naked_immediate ty2 ->
          Naked_immediate (join_ty_naked_immediate ~importer ty1 ty2)
        | Naked_float ty1, Naked_float ty2 ->
          Naked_float (join_ty_naked_float ~importer ty1 ty2)
        | Naked_int32 ty1, Naked_int32 ty2 ->
          Naked_int32 (join_ty_naked_int32 ~importer ty1 ty2)
        | Naked_int64 ty1, Naked_int64 ty2 ->
          Naked_int64 (join_ty_naked_int64 ~importer ty1 ty2)
        | Naked_nativeint ty1, Naked_nativeint ty2 ->
          Naked_nativeint (join_ty_naked_nativeint ~importer ty1 ty2)
        | _, _ ->
          Misc.fatal_errorf "Cannot take the join of two types with different \
              kinds: %a and %a"
            print t1
            print t2
  end
end
