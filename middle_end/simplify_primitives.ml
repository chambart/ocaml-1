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

module A = Simple_value_approx
module C = Inlining_cost
module I = Simplify_boxed_integer_ops
module S = Simplify_common

let ccall_type_specialisation ccall prim expr (descrs:A.descr list) args dbg
      : Lambda.primitive * Flambda.named =
  let unboxed_compare name native_repr : Lambda.primitive =
    Pccall( Primitive.make ~name ~alloc:false
              ~native_name:(name^"_unboxed")
              ~native_repr_args:[native_repr;native_repr]
              ~native_repr_res:Untagged_int)
  in
  let return prim : Lambda.primitive * Flambda.named =
    prim, Prim(prim, args, dbg)
  in
  match ccall, descrs with
  | "caml_equal",       [Value_float _; Value_float _] ->
    return (Pfloatcomp (Ceq,Boxed))
  | "caml_notequal",    [Value_float _; Value_float _] ->
    return (Pfloatcomp (Cneq,Boxed))
  | "caml_lessthan",    [Value_float _; Value_float _] ->
    return (Pfloatcomp (Clt,Boxed))
  | "caml_greaterthan" ,[Value_float _; Value_float _] ->
    return (Pfloatcomp (Cgt,Boxed))
  | "caml_lessequal",   [Value_float _; Value_float _] ->
    return (Pfloatcomp (Cle,Boxed))
  | "caml_greaterequal",[Value_float _; Value_float _] ->
    return (Pfloatcomp (Cge,Boxed))
  | "caml_compare",     [Value_float _; Value_float _] ->
    return (unboxed_compare "caml_float_compare" Unboxed_float)
  | _ ->
    prim, expr

let type_specialisation (p : Lambda.primitive) args approxs expr dbg
      : Lambda.primitive * Flambda.named =
  match p with
  | Pccall { prim_name } ->
    ccall_type_specialisation prim_name p expr (A.descrs approxs) args dbg
  | _ ->
    p, expr

let phys_equal (approxs:A.t list) =
  match approxs with
  | [] | [_] | _ :: _ :: _ :: _ ->
      Misc.fatal_error "wrong number of arguments for equality"
  | [a1; a2] ->
    (* N.B. The following would be incorrect if the variables are not
       bound in the environment:
       match a1.var, a2.var with
       | Some v1, Some v2 when Variable.equal v1 v2 -> true
       | _ -> ...
    *)
    match a1.symbol, a2.symbol with
    | Some (s1, None), Some (s2, None) -> Symbol.equal s1 s2
    | Some (s1, Some f1), Some (s2, Some f2) -> Symbol.equal s1 s2 && f1 = f2
    | _ -> false

let primitive (p : Lambda.primitive) (args, approxs) expr dbg ~size_int
      ~big_endian : Flambda.named * A.t * Inlining_cost.Benefit.t =
  let fpc = !Clflags.float_const_prop in
  let p, expr = type_specialisation p args approxs expr dbg in
  match p with
  | Pmakeblock(tag_int, Asttypes.Immutable, shape) ->
    let tag = Tag.create_exn tag_int in
    let shape = match shape with
      | None -> List.map (fun _ -> Lambda.Pgenval) args
      | Some shape -> shape
    in
    let approxs = List.map2 A.augment_with_kind approxs shape in
    let shape = List.map2 A.augment_kind_with_approx approxs shape in
    Prim (Pmakeblock(tag_int, Asttypes.Immutable, Some shape), args, dbg),
    A.value_block tag (Array.of_list approxs), C.Benefit.zero
  | Praise _ ->
    expr, A.value_bottom, C.Benefit.zero
  | Pignore -> begin
      match args, A.descrs approxs with
      | [arg], [(Value_int 0 | Value_constptr 0)] ->
        S.const_ptr_expr (Flambda.Expr (Var arg)) 0
      | _ -> S.const_ptr_expr expr 0
    end
  | Pmakearray (Pfloatarray, Mutable) ->
      let approx =
        A.value_mutable_float_array ~size:(List.length args)
      in
      expr, approx, C.Benefit.zero
  | Pmakearray (Pfloatarray, Immutable) ->
      let approx =
        A.value_immutable_float_array (Array.of_list approxs)
      in
      expr, approx, C.Benefit.zero
  | Pintcomp Ceq when phys_equal approxs ->
    S.const_bool_expr expr true
  | Pintcomp Cneq when phys_equal approxs ->
    S.const_bool_expr expr false
    (* N.B. Having [not (phys_equal approxs)] would not on its own tell us
       anything about whether the two values concerned are unequal.  To judge
       that, it would be necessary to prove that the approximations are
       different, which would in turn entail them being completely known.

       It may seem that in the case where we have two approximations each
       annotated with a symbol that we should be able to judge inequality
       even if part of the approximation description(s) are unknown.  This is
       unfortunately not the case.  Here is an example:

         let a = f 1
         let b = f 1
         let c = a, a
         let d = a, a

       If [Share_constants] is run before [f] is completely inlined (assuming
       [f] always generates the same result; effects of [f] aren't in fact
       relevant) then [c] and [d] will not be shared.  However if [f] is
       inlined later, [a] and [b] could be shared and thus [c] and [d] could
       be too.  As such, any intermediate non-aliasing judgement would be
       invalid. *)
  | _ ->
    match A.descrs approxs with
    | [Value_int x] ->
      begin match p with
      | Pidentity -> S.const_int_expr expr x
      | Pnot -> S.const_bool_expr expr (x = 0)
      | Pnegint -> S.const_int_expr expr (-x)
      | Pbswap16 -> S.const_int_expr expr (S.swap16 x)
      | Poffsetint y -> S.const_int_expr expr (x + y)
      | Pfloatofint Boxed when fpc -> S.const_float_expr expr (float_of_int x)
      | Pfloatofint Unboxed when fpc -> S.const_unboxed_float_expr expr (float_of_int x)
      | Pbintofint Pnativeint ->
        S.const_boxed_int_expr expr Nativeint (Nativeint.of_int x)
      | Pbintofint Pint32 -> S.const_boxed_int_expr expr Int32 (Int32.of_int x)
      | Pbintofint Pint64 -> S.const_boxed_int_expr expr Int64 (Int64.of_int x)
      | _ -> expr, A.value_unknown Other, C.Benefit.zero
      end
    | [(Value_int x | Value_constptr x); (Value_int y | Value_constptr y)] ->
      let shift_precond = 0 <= y && y < 8 * size_int in
      begin match p with
      | Paddint -> S.const_int_expr expr (x + y)
      | Psubint -> S.const_int_expr expr (x - y)
      | Pmulint -> S.const_int_expr expr (x * y)
      | Pdivint _ when y <> 0 -> S.const_int_expr expr (x / y)
      | Pmodint _ when y <> 0 -> S.const_int_expr expr (x mod y)
      | Pandint -> S.const_int_expr expr (x land y)
      | Porint -> S.const_int_expr expr (x lor y)
      | Pxorint -> S.const_int_expr expr (x lxor y)
      | Plslint when shift_precond -> S.const_int_expr expr (x lsl y)
      | Plsrint when shift_precond -> S.const_int_expr expr (x lsr y)
      | Pasrint when shift_precond -> S.const_int_expr expr (x asr y)
      | Pintcomp cmp -> S.const_comparison_expr expr cmp x y
      | Pisout -> S.const_bool_expr expr (y > x || y < 0)
      | _ -> expr, A.value_unknown Other, C.Benefit.zero
      end
    | [Value_char x; Value_char y] ->
      begin match p with
      | Pintcomp cmp -> S.const_comparison_expr expr cmp x y
      | _ -> expr, A.value_unknown Other, C.Benefit.zero
      end
    | [Value_constptr x] ->
      begin match p with
      (* [Pidentity] should probably never appear, but is here for
         completeness. *)
      | Pidentity -> S.const_ptr_expr expr x
      | Pnot -> S.const_bool_expr expr (x = 0)
      | Pisint -> S.const_bool_expr expr true
      | Poffsetint y -> S.const_ptr_expr expr (x + y)
      | Pctconst c ->
        begin match c with
        | Big_endian -> S.const_bool_expr expr big_endian
        | Word_size -> S.const_int_expr expr (8*size_int)
        | Int_size -> S.const_int_expr expr (8*size_int - 1)
        | Max_wosize ->
          (* CR-someday mshinwell: this function should maybe not live here. *)
          S.const_int_expr expr ((1 lsl ((8*size_int) - 10)) - 1)
        | Ostype_unix -> S.const_bool_expr expr (Sys.os_type = "Unix")
        | Ostype_win32 -> S.const_bool_expr expr (Sys.os_type = "Win32")
        | Ostype_cygwin -> S.const_bool_expr expr (Sys.os_type = "Cygwin")
        | Backend_type ->
          S.const_ptr_expr expr 0 (* tag 0 is the same as Native *)
        end
      | _ -> expr, A.value_unknown Other, C.Benefit.zero
      end
    | [Value_float (Const x)] when fpc ->
      begin match p with
      | Pintoffloat Boxed -> S.const_int_expr expr (int_of_float x)
      | Pnegfloat Boxed -> S.const_float_expr expr (-. x)
      | Pabsfloat Boxed -> S.const_float_expr expr (abs_float x)
      | Punbox_float -> S.const_unboxed_float_expr expr x
      | _ -> expr, A.value_unknown Other, C.Benefit.zero
      end
    | [Value_unboxed_float (Const x)] when fpc ->
      begin match p with
      | Pintoffloat Unboxed -> S.const_int_expr expr (int_of_float x)
      | Pnegfloat Unboxed -> S.const_unboxed_float_expr expr (-. x)
      | Pabsfloat Unboxed -> S.const_unboxed_float_expr expr (abs_float x)
      | Pbox_float -> S.const_float_expr expr x
      | _ -> expr, A.value_unknown Other, C.Benefit.zero
      end
    | [Value_float (Const n1); Value_float (Const n2)] when fpc ->
      begin match p with
      | Paddfloat Boxed -> S.const_float_expr expr (n1 +. n2)
      | Psubfloat Boxed -> S.const_float_expr expr (n1 -. n2)
      | Pmulfloat Boxed -> S.const_float_expr expr (n1 *. n2)
      | Pdivfloat Boxed -> S.const_float_expr expr (n1 /. n2)
      | Pfloatcomp (c, Boxed) -> S.const_comparison_expr expr c n1 n2
      | _ -> expr, A.value_unknown Other, C.Benefit.zero
      end
    | [Value_unboxed_float (Const n1); Value_unboxed_float (Const n2)] when fpc ->
      begin match p with
      | Paddfloat Unboxed -> S.const_unboxed_float_expr expr (n1 +. n2)
      | Psubfloat Unboxed -> S.const_unboxed_float_expr expr (n1 -. n2)
      | Pmulfloat Unboxed -> S.const_unboxed_float_expr expr (n1 *. n2)
      | Pdivfloat Unboxed -> S.const_unboxed_float_expr expr (n1 /. n2)
      | Pfloatcomp (c, Unboxed) -> S.const_comparison_expr expr c n1 n2
      | _ -> expr, A.value_unknown Other, C.Benefit.zero
      end
    | [A.Value_boxed_int(A.Nativeint, n)] ->
      I.Simplify_boxed_nativeint.simplify_unop p Nativeint expr n
    | [A.Value_boxed_int(A.Int32, n)] ->
      I.Simplify_boxed_int32.simplify_unop p Int32 expr n
    | [A.Value_boxed_int(A.Int64, n)] ->
      I.Simplify_boxed_int64.simplify_unop p Int64 expr n
    | [A.Value_boxed_int(A.Nativeint, n1);
       A.Value_boxed_int(A.Nativeint, n2)] ->
      I.Simplify_boxed_nativeint.simplify_binop p Nativeint expr n1 n2
    | [A.Value_boxed_int(A.Int32, n1); A.Value_boxed_int(A.Int32, n2)] ->
      I.Simplify_boxed_int32.simplify_binop p Int32 expr n1 n2
    | [A.Value_boxed_int(A.Int64, n1); A.Value_boxed_int(A.Int64, n2)] ->
      I.Simplify_boxed_int64.simplify_binop p Int64 expr n1 n2
    | [A.Value_boxed_int(A.Nativeint, n1); Value_int n2] ->
      I.Simplify_boxed_nativeint.simplify_binop_int p Nativeint expr n1 n2
        ~size_int
    | [A.Value_boxed_int(A.Int32, n1); Value_int n2] ->
      I.Simplify_boxed_int32.simplify_binop_int p Int32 expr n1 n2
        ~size_int
    | [A.Value_boxed_int(A.Int64, n1); Value_int n2] ->
      I.Simplify_boxed_int64.simplify_binop_int p Int64 expr n1 n2
        ~size_int
    | [Value_block _] when p = Lambda.Pisint ->
      S.const_bool_expr expr false
    | [Value_string { size }]
      when (p = Lambda.Pstringlength || p = Lambda.Pbyteslength) ->
      S.const_int_expr expr size
    | [Value_string { size; contents = Some s };
       (Value_int x | Value_constptr x)] when x >= 0 && x < size ->
        begin match p with
        | Pstringrefu
        | Pstringrefs
        | Pbytesrefu
        | Pbytesrefs ->
          S.const_char_expr (Prim(Pstringrefu, args, dbg)) s.[x]
        | _ -> expr, A.value_unknown Other, C.Benefit.zero
        end
    | [Value_string { size; contents = None };
       (Value_int x | Value_constptr x)]
      when x >= 0 && x < size && p = Lambda.Pstringrefs ->
        Flambda.Prim (Pstringrefu, args, dbg),
          A.value_unknown Other,
          (* we improved it, but there is no way to account for that: *)
          C.Benefit.zero
    | [Value_string { size; contents = None };
       (Value_int x | Value_constptr x)]
      when x >= 0 && x < size && p = Lambda.Pbytesrefs ->
        Flambda.Prim (Pbytesrefu, args, dbg),
          A.value_unknown Other,
          (* we improved it, but there is no way to account for that: *)
          C.Benefit.zero

    | [Value_float_array { size; contents }] ->
        begin match p with
        | Parraylength _ -> S.const_int_expr expr size
        | Pfloatfield i ->
          begin match contents with
          | A.Contents a when i >= 0 && i < size ->
            begin match A.check_approx_for_float a.(i) with
            | None -> expr, a.(i), C.Benefit.zero
            | Some v -> S.const_float_expr expr v
            end
          | Contents _ | Unknown_or_mutable ->
            expr, A.value_unknown Other, C.Benefit.zero
          end
        | _ -> expr, A.value_unknown Other, C.Benefit.zero
        end
    | _ ->
      match Semantics_of_primitives.return_type_of_primitive p with
      | Float ->
        expr, A.value_any_float, C.Benefit.zero
      | Unboxed_float ->
        expr, A.value_any_unboxed_float, C.Benefit.zero
      | Other ->
        expr, A.value_unknown Other, C.Benefit.zero
