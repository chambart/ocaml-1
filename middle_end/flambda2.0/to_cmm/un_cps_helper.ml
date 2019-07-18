(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                        Guillaume Bury, OCamlPro                        *)
(*                                                                        *)
(*   Copyright 2019--2019 OCamlPro SAS                                    *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

[@@@ocaml.warning "+a-4-30-40-41-42"]

open Cmm_helpers

(* Are we compiling on/for a 32-bit architecture ? *)
let arch32 = Arch.size_int = 4

(* Useful shortcut *)
let typ_int64 =
  if arch32 then [| Cmm.Int; Cmm.Int |] else [| Cmm.Int |]


(* Void *)

let void = Cmm.Ctuple []
let unit ~dbg = Cmm.Cconst_pointer (1, dbg)

(* Data items *)

let cint i =
  Cmm.Cint i

let cfloat f =
  Cmm.Cdouble f

let symbol_address s =
  Cmm.Csymbol_address s

let define_symbol ~global s =
  if global then
    [Cmm.Cglobal_symbol s; Cmm.Cdefine_symbol s]
  else
    [Cmm.Cdefine_symbol s]

(* Constructors for constants *)

let var v = Cmm.Cvar v

let symbol ?(dbg=Debuginfo.none) s =
  Cmm.Cconst_symbol (s, dbg)

let float ?(dbg=Debuginfo.none) f =
  Cmm.Cconst_float (f, dbg)

(* CR Gbury: this conversion int -> nativeint is potentially unsafe
   when cross-compiling for 64-bit on a 32-bit host *)
let int ?(dbg=Debuginfo.none) i =
  natint_const_untagged dbg (Nativeint.of_int i)

let int32 ?(dbg=Debuginfo.none) i =
  natint_const_untagged dbg (Nativeint.of_int32 i)

(* CR Gbury: this conversion int64 -> nativeint is potentially unsafe
     when cross-compiling for 64-bit on a 32-bit host *)
let int64 ?(dbg=Debuginfo.none) i =
  natint_const_untagged dbg (Int64.to_nativeint i)

let targetint ?(dbg=Debuginfo.none) t =
  match Targetint.repr t with
  | Int32 i -> int32 ~dbg i
  | Int64 i -> int64 ~dbg i

(* Sequence *)

let sequence x y =
  match x, y with
  | Cmm.Ctuple [], _ -> y
  | _, Cmm.Ctuple [] -> x
  | _, _ -> Cmm.Csequence (x, y)

(* Boxing/unboxing *)

let primitive_boxed_int_of_boxable_number b =
  match (b : Flambda_kind.Boxable_number.t) with
  | Naked_float -> assert false
  | Naked_int32 -> Primitive.Pint32
  | Naked_int64 -> Primitive.Pint64
  | Naked_nativeint -> Primitive.Pnativeint

let unbox_number ?(dbg=Debuginfo.none) kind arg =
  match (kind : Flambda_kind.Boxable_number.t) with
  | Naked_float -> unbox_float dbg arg
  | _ ->
      let primitive_kind = primitive_boxed_int_of_boxable_number kind in
      unbox_int primitive_kind arg dbg

let box_number ?(dbg=Debuginfo.none) kind arg =
  match (kind : Flambda_kind.Boxable_number.t) with
  | Naked_float -> box_float dbg arg
  | _ ->
      let primitive_kind = primitive_boxed_int_of_boxable_number kind in
      box_int_gen dbg primitive_kind arg

let box_int64 ?dbg arg =
  box_number ?dbg Flambda_kind.Boxable_number.Naked_int64 arg


(* Constructors for operations *)

let unary op = (fun ?(dbg=Debuginfo.none) x -> Cmm.Cop (op, [x], dbg))
let binary op = (fun ?(dbg=Debuginfo.none) x y -> Cmm.Cop (op, [x; y], dbg))

let and_ = binary Cmm.Cand
let or_ = binary Cmm.Cor
let xor_ = binary Cmm.Cxor

let eq = binary Cmm.(Ccmpi Ceq)
let neq = binary Cmm.(Ccmpi Cne)

let lt = binary Cmm.(Ccmpi Clt)
let le = binary Cmm.(Ccmpi Cle)
let gt = binary Cmm.(Ccmpi Cgt)
let ge = binary Cmm.(Ccmpi Cgt)

let ult = binary Cmm.(Ccmpa Clt)
let ule = binary Cmm.(Ccmpa Cle)
let ugt = binary Cmm.(Ccmpa Cgt)
let uge = binary Cmm.(Ccmpa Cgt)

let float_abs = unary Cmm.Cabsf
let float_neg = unary Cmm.Cnegf

let float_add = binary Cmm.Caddf
let float_sub = binary Cmm.Csubf
let float_mul = binary Cmm.Cmulf
let float_div = binary Cmm.Cdivf

let float_eq = binary Cmm.(Ccmpf CFeq)
let float_neq = binary Cmm.(Ccmpf CFneq)
let float_lt = binary Cmm.(Ccmpf CFlt)
let float_le = binary Cmm.(Ccmpf CFle)
let float_gt = binary Cmm.(Ccmpf CFgt)
let float_ge = binary Cmm.(Ccmpf CFge)

let int_of_float = unary Cmm.Cintoffloat
let float_of_int = unary Cmm.Cfloatofint

let letin v e body = Cmm.Clet (v, e, body)

let ite
    ?(dbg=Debuginfo.none)
    ?(then_dbg=Debuginfo.none) ~then_
    ?(else_dbg=Debuginfo.none) ~else_ cond =
  Cmm.Cifthenelse(cond, then_dbg, then_, else_dbg, else_, dbg)

let load ?(dbg=Debuginfo.none) kind mut addr =
  Cmm.Cop (Cmm.Cload (kind, mut), [addr], dbg)

let store ?(dbg=Debuginfo.none) kind init addr value =
  Cmm.Cop (Cmm.Cstore (kind, init), [addr; value], dbg)

let extcall ?(dbg=Debuginfo.none) ?label ~alloc name typ_res args =
  Cmm.Cop (Cextcall (name, typ_res, alloc, label), args, dbg)

(* Block creation *)

let float_tag = function
  | [] -> assert false
  | [_] -> Tag.double_tag
  | _ -> Tag.double_array_tag

let make_block ?(dbg=Debuginfo.none) kind args =
  match (kind : Flambda_primitive.make_block_kind) with
  | Full_of_values (tag, _) ->
      make_alloc dbg (Tag.Scannable.to_int tag) args
  | Full_of_naked_floats
  | Generic_array Full_of_naked_floats ->
      make_float_alloc dbg (Tag.to_int (float_tag args)) args
  | _ ->
      make_alloc dbg 0 args

let make_closure_block ?(dbg=Debuginfo.none) l =
  let tag = Tag.(to_int closure_tag) in
  make_alloc dbg tag l

(* Block access *)

let array_kind_of_block_access kind =
  match (kind : Flambda_primitive.Block_access_kind.t) with
  (* Full naked float arrays *)
  | Block Naked_float
  | Array Naked_float
  | Generic_array Full_of_naked_floats -> Lambda.Pfloatarray
  (* Arrays (or accesses) to immediate integers *)
  | Block Value Definitely_immediate
  | Array Value Definitely_immediate
  | Generic_array Full_of_immediates -> Lambda.Pintarray
  (* Arrays of caml values (i.e specifically not naked floats) *)
  | Block Value (Anything|Definitely_pointer)
  | Array Value (Anything|Definitely_pointer)
  | Generic_array Full_of_arbitrary_values_but_not_floats -> Lambda.Paddrarray
  (* General case: the array might contain naked floats *)
  | _ -> Lambda.Pgenarray

let block_length ?(dbg=Debuginfo.none) block_access_kind block =
  arraylength (array_kind_of_block_access block_access_kind) block dbg

let block_load ?(dbg=Debuginfo.none) kind block index =
  match array_kind_of_block_access kind with
  | Lambda.Pintarray -> int_array_ref block index dbg
  | Lambda.Paddrarray -> addr_array_ref block index dbg
  | Lambda.Pfloatarray -> unboxed_float_array_ref block index dbg
  | Lambda.Pgenarray ->
      ite ~dbg (is_addr_array_ptr block dbg)
        ~then_:(addr_array_ref block index dbg) ~then_dbg:dbg
        ~else_:(float_array_ref block index dbg) ~else_dbg:dbg

let addr_array_store init block index value dbg =
  match (init : Flambda_primitive.init_or_assign) with
  | Assignment -> addr_array_set block index value dbg
  | Initialization -> addr_array_initialize block index value dbg

let block_set ?(dbg=Debuginfo.none) kind init block index value =
  match (array_kind_of_block_access kind : Lambda.array_kind) with
  | Pintarray ->
      return_unit dbg (int_array_set block index value dbg)
  | Pfloatarray ->
      return_unit dbg (float_array_set block index value dbg)
  | Paddrarray ->
      return_unit dbg (addr_array_store init block index value dbg)
  | Pgenarray ->
      return_unit dbg (
        ite ~dbg (is_addr_array_ptr block dbg)
          ~then_:(addr_array_store init block index value dbg) ~then_dbg:dbg
          ~else_:(float_array_set block index value dbg) ~else_dbg:dbg
      )


(* here, block and ptr are different only for bigstrings, because the
   extcall must apply to the whole bigstring block (variable [block]),
   whereas the loads apply to the bigstring data pointer (variable [ptr]).
   For regular strings, [block = ptr]. *)
let string_like_load_aux ~dbg kind width block ptr idx =
  match (width : Flambda_primitive.string_accessor_width) with
  | Eight ->
      let idx = untag_int idx dbg in
      load ~dbg Cmm.Byte_unsigned Asttypes.Mutable (add_int ptr idx dbg)
  | Sixteen ->
      let idx = untag_int idx dbg in
      unaligned_load_16 ptr idx dbg
  | Thirty_two ->
      let idx = untag_int idx dbg in
      unaligned_load_32 ptr idx dbg
  | Sixty_four ->
      if arch32 then
        begin match (kind : Flambda_primitive.string_like_value) with
        | String ->
            extcall ~alloc:false
              "caml_string_get_64" typ_int64 [block; idx]
        | Bytes ->
            extcall ~alloc:false
              "caml_bytes_get_64" typ_int64 [block; idx]
        | Bigstring ->
            extcall ~alloc:false
              "caml_ba_uint8_get64" typ_int64 [block; idx]
        end
      else
        unaligned_load_64 ptr idx dbg

let string_like_load ?(dbg=Debuginfo.none) kind width block index =
  match (kind : Flambda_primitive.string_like_value) with
  | String | Bytes ->
      string_like_load_aux ~dbg kind width block block index
  | Bigstring ->
      let ba_data_addr = field_address block 1 dbg in
      let ba_data = load ~dbg Cmm.Word_int Asttypes.Mutable ba_data_addr in
      bind "ba_data" ba_data (fun ptr ->
          string_like_load_aux ~dbg kind width block ptr index)

(* same as {string_like_load_aux} *)
let bytes_like_set_aux ~dbg kind width block ptr idx value =
  begin match (width : Flambda_primitive.string_accessor_width) with
  | Eight ->
      store ~dbg Cmm.Byte_unsigned Lambda.Assignment (add_int ptr idx dbg) value
  | Sixteen ->
      unaligned_set_16 ptr idx value dbg
  | Thirty_two ->
      unaligned_set_32 ptr idx value dbg
  | Sixty_four ->
      if arch32 then
        begin match (kind : Flambda_primitive.bytes_like_value) with
        | Bytes ->
            extcall ~alloc:false
              "caml_bytes_set_64" typ_int64 [block; idx; value]
        | Bigstring ->
            extcall ~alloc:false
              "caml_ba_uint8_set64" typ_int64 [block; idx; value]
        end
      else
        unaligned_set_64 ptr idx value dbg
  end

let bytes_like_set ?(dbg=Debuginfo.none) kind width block index value =
  match (kind : Flambda_primitive.bytes_like_value) with
  | Bytes ->
      bytes_like_set_aux ~dbg kind width block block index value
  | Bigstring ->
      let ba_data_addr = field_address block 1 dbg in
      let ba_data = load ~dbg Cmm.Word_int Asttypes.Mutable ba_data_addr in
      bind "ba_data" ba_data (fun ptr ->
          bytes_like_set_aux ~dbg kind width block ptr index value)

(* wrappers for bigarrays *)

let lambda_ba_layout layout =
  match (layout : Flambda_primitive.bigarray_layout) with
  | C -> Lambda.Pbigarray_c_layout
  | Fortran -> Lambda.Pbigarray_fortran_layout
  | Unknown -> Lambda.Pbigarray_unknown_layout

let lambda_ba_kind k =
  match (k : Flambda_primitive.bigarray_kind) with
  | Unknown -> Lambda.Pbigarray_unknown
  | Float32 -> Lambda.Pbigarray_float32
  | Float64 -> Lambda.Pbigarray_float64
  | Sint8   -> Lambda.Pbigarray_sint8
  | Uint8   -> Lambda.Pbigarray_uint8
  | Sint16  -> Lambda.Pbigarray_sint16
  | Uint16  -> Lambda.Pbigarray_uint16
  | Int32   -> Lambda.Pbigarray_int32
  | Int64   -> Lambda.Pbigarray_int64
  | Int_width_int -> Lambda.Pbigarray_caml_int
  | Targetint_width_int -> Lambda.Pbigarray_native_int
  | Complex32 -> Lambda.Pbigarray_complex32
  | Complex64 -> Lambda.Pbigarray_complex64

let bigarray_load ?(dbg=Debuginfo.none) _dims kind layout = function
  | ba :: args ->
      assert (List.length args = _dims); (* TODO: correct ? *)
      let kind = lambda_ba_kind kind in
      let layout = lambda_ba_layout layout in
      bigarray_get true kind layout ba args dbg
  | _ -> assert false

let bigarray_store ?(dbg=Debuginfo.none) _dims kind layout = function
  | ba :: args ->
      let indexes, value = Misc.split_last args in
      let kind = lambda_ba_kind kind in
      let layout = lambda_ba_layout layout in
      bigarray_set true kind layout ba indexes value dbg
  | _ -> assert false

(* try-with blocks *)

let trywith ?(dbg=Debuginfo.none) ~body ~exn_var ~handler =
  Cmm.Ctrywith (body, exn_var, handler, dbg)


(* Static jumps *)

type static_handler =
  int *
  ((Backend_var.With_provenance.t * Cmm.machtype) list) *
  Cmm.expression *
  Debuginfo.t
(* Alias for static handler *)

let handler ?(dbg=Debuginfo.none) id vars body =
  (id, vars, body, dbg)

let cexit id args =
  Cmm.Cexit (id, args)

let ccatch ~rec_flag ~handlers ~body =
  let rec_flag = if rec_flag then Cmm.Recursive else Cmm.Nonrecursive in
  Cmm.Ccatch (rec_flag, handlers, body)


(* Function calls *)

let direct_call ?(dbg=Debuginfo.none) ty f args =
  Cmm.Cop (Cmm.Capply ty, f :: args, dbg)

(* CR gbury:
   optimize the case where arity = 1 (see cmmgen_helpers' generic_apply) *)
let indirect_call ?(dbg=Debuginfo.none) ty f args =
  let arity = List.length args in
  let l = symbol (apply_function_sym arity) :: args @ [f] in
  Cmm.Cop (Cmm.Capply ty, l, dbg)


(* Cmm phrases *)

let cfunction decl =
  Cmm.Cfunction decl

let cdata d =
  Cmm.Cdata d

let fundecl fun_name fun_args fun_body fun_codegen_options fun_dbg =
  { Cmm.fun_name; fun_args; fun_body; fun_codegen_options; fun_dbg; }


(* Gc root table *)

let gc_root_table syms =
  let table_symbol = Compilenv.make_symbol (Some "gc_roots") in
  cdata (
    define_symbol ~global:true table_symbol @
    List.map symbol_address syms @
    [ cint 0n ]
  )
