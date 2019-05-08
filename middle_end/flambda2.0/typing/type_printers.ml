(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                       Pierre Chambart, OCamlPro                        *)
(*           Mark Shinwell and Leo White, Jane Street Europe              *)
(*                                                                        *)
(*   Copyright 2013--2019 OCamlPro SAS                                    *)
(*   Copyright 2014--2019 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

[@@@ocaml.warning "+a-4-30-40-41-42"]

let print_or_alias print_descr ppf (or_alias : _ Flambda_types.or_alias) =
  match or_alias with
  | No_alias descr -> print_descr ppf descr
  | Equals simple ->
    Format.fprintf ppf "@[(%s=%s %a)@]"
      (Misc_color.bold_red ())
      (Misc_color.reset ())
      Simple.print simple
  | Type export_id ->
    Format.fprintf ppf "@[(%s=export_id%s %a)@]"
      (Misc_color.bold_red ())
      (Misc_color.reset ())
      Export_id.print export_id

let unicode = true  (* CR mshinwell: move elsewhere *)

let print_unknown_or_join print_contents ppf
      (o : _ Flambda_types.unknown_or_join) =
  let colour = Misc_color.bold_red () in
  match o with
  | Unknown ->
    if unicode then
      Format.fprintf ppf "%s\u{22a4}%s" colour (Misc_color.reset ())
    else
      Format.fprintf ppf "%sT%s" colour (Misc_color.reset ())
  | Join [] ->
    if unicode then
      Format.fprintf ppf "%s\u{22a5}%s" colour (Misc_color.reset ())
    else
      Format.fprintf ppf "%s_|_%s" colour (Misc_color.reset ())
  | Join [contents] -> print_contents ppf contents
  | Join incompatibles ->
    Format.fprintf ppf "@[(Join_incompatible@ (%a))@]"
      (Format.pp_print_list print_contents) incompatibles

let print_ty_generic print_contents ppf ty =
  (print_or_alias (print_unknown_or_join print_contents)) ppf ty

let print_of_kind_naked_number (type n) ppf
      ((n : n Flambda_types.of_kind_naked_number), _perm) =
  match n with
  | Immediate i ->
    Format.fprintf ppf "@[(Naked_immediates@ (%a))@]"
      Immediate.Set.print i
  | Float f ->
    Format.fprintf ppf "@[(Naked_floats@ (%a))@]"
      Numbers.Float_by_bit_pattern.Set.print f
  | Int32 i ->
    Format.fprintf ppf "@[(Naked_int32s@ (%a))@]"
      Numbers.Int32.Set.print i
  | Int64 i ->
    Format.fprintf ppf "@[(Naked_int64s@ (%a))@]"
      Numbers.Int64.Set.print i
  | Nativeint i ->
    Format.fprintf ppf "@[(Naked_nativeints@ (%a))@]"
      Targetint.Set.print i

let print_ty_naked_number (type n) ppf
      (ty : n Flambda_types.ty_naked_number) =
  print_ty_generic print_of_kind_naked_number ppf ty

let _print_ty_naked_immediate_with_cache ~cache:_ ppf ty =
  print_ty_generic (print_of_kind_naked_number) ppf ty

let print_ty_naked_int32_with_cache ~cache:_ ppf ty =
  print_ty_generic (print_of_kind_naked_number) ppf ty

let print_ty_naked_int64_with_cache ~cache:_ ppf ty =
  print_ty_generic (print_of_kind_naked_number) ppf ty

let print_ty_naked_nativeint_with_cache ~cache:_ ppf ty =
  print_ty_generic (print_of_kind_naked_number) ppf ty

let print_ty_naked_float_with_cache ~cache:_ ppf ty =
  print_ty_generic (print_of_kind_naked_number) ppf ty

let print_ty_naked_immediate_with_cache ~cache:_ ppf ty =
  print_ty_generic (print_of_kind_naked_number) ppf ty

let print_ty_naked_int32 ppf ty =
  print_ty_naked_int32_with_cache ~cache:(Printing_cache.create ())
    ppf ty

let print_ty_naked_int64 ppf ty =
  print_ty_naked_int64_with_cache ~cache:(Printing_cache.create ())
    ppf ty

let print_ty_naked_nativeint ppf ty =
  print_ty_naked_nativeint_with_cache ~cache:(Printing_cache.create ())
    ppf ty

let print_ty_naked_float ppf ty =
  print_ty_naked_float_with_cache ~cache:(Printing_cache.create ())
    ppf ty

let print_ty_naked_immediate ppf ty =
  print_ty_naked_immediate_with_cache ~cache:(Printing_cache.create ())
    ppf ty

let print_of_kind_value_boxed_number (type n)
      ppf (n : n Flambda_types.of_kind_value_boxed_number) =
  match n with
  | Boxed_float f ->
    Format.fprintf ppf "@[(Boxed_float@ (%a))@]"
      print_ty_naked_number f
  | Boxed_int32 i ->
    Format.fprintf ppf "@[(Boxed_int32@ (%a))@]"
      print_ty_naked_number i
  | Boxed_int64 i ->
    Format.fprintf ppf "@[(Boxed_int64@ (%a))@]"
      print_ty_naked_number i
  | Boxed_nativeint i ->
    Format.fprintf ppf "@[(Boxed_nativeint@ (%a))@]"
      print_ty_naked_number i

let rec print_of_kind_value ~cache ppf
        ((of_kind_value : Flambda_types.of_kind_value), _) =
  match of_kind_value with
  | Blocks_and_tagged_immediates { blocks; immediates; } ->
    (* CR mshinwell: Improve so that we elide blocks and/or immediates when
       they're empty.  Similarly we can elide the extensions when empty. *)
    Format.fprintf ppf
      "(Blocks_and_immediates@ \
        @[<v>@[<hov 1>(blocks@ %a)@]@ \
        @[<hov 1>(immediates@ %a)@]@])"
      (Blocks.print_with_cache ~cache) blocks
      (Immediates.print ~cache) immediates
  | Boxed_number n ->
    Format.fprintf ppf "@[(Boxed_number %a)@]"
      print_of_kind_value_boxed_number n
  | Closures { by_closure_id; } ->
    Closures_entry_by_closure_id.print ~cache ppf by_closure_id
  | String str_infos ->
    Format.fprintf ppf "@[(Strings (%a))@]" String_info.Set.print str_infos

and print_ty_value_with_cache ~cache ppf (ty : Flambda_types.ty_value) =
  print_ty_generic (print_of_kind_value ~cache) ppf ty

and print_inlinable_function_declaration_with_cache ~cache ppf
      (({ function_decl;
          invariant_params;
          size;
          direct_call_surrogate;
        } : Flambda_types.inlinable_function_declaration) as decl) =
  Printing_cache.with_cache cache ppf "inlinable_fundecl" decl
    (fun ppf () ->
      Format.fprintf ppf
        "@[<hov 1>(Inlinable@ \
          @[<hov 1>(function_decl@ %a)@]@ \
          @[<hov 1>(invariant_params@ %a)@]@ \
          @[<hov 1>(size@ %a)@]@ \
          @[<hov 1>(direct_call_surrogate@ %a)@])@]"
        Term_language_function_declaration.print function_decl
        Variable.Set.print (Lazy.force invariant_params)
        (Misc.Stdlib.Option.print Format.pp_print_int) (Lazy.force size)
        (Misc.Stdlib.Option.print Closure_id.print) direct_call_surrogate)

and print_function_declaration_with_cache ~cache ppf
      (decl : Flambda_types.function_declaration) =
  match decl with
  | Inlinable decl ->
    print_inlinable_function_declaration_with_cache ~cache ppf decl
  | Non_inlinable -> Format.pp_print_string ppf "Non_inlinable"

and print_of_kind_fabricated ~cache ppf
      ((o : Flambda_types.of_kind_fabricated), _) =
  match o with
  | Discriminants discriminants ->
    Format.fprintf ppf "@[<hov 1>(Discriminants@ %a)@]"
      (Discriminants.print ~cache) discriminants
  | Set_of_closures { closures; } ->
    Closure_ids.print ~cache ppf closures

and print_ty_fabricated_with_cache ~cache ppf
      (ty : Flambda_types.ty_fabricated) =
  print_ty_generic (print_of_kind_fabricated ~cache) ppf ty

and print_with_cache ~cache ppf (t : Flambda_types.t) =
  match t with
  | Value ty ->
    Format.fprintf ppf "@[<hov 1>(Val %a)@]"
      (print_ty_value_with_cache ~cache) ty
  | Naked_number (ty, _kind) ->
    Format.fprintf ppf "@[<hov 1>(Naked %a)@]" print_ty_naked_number ty
  | Fabricated ty ->
    Format.fprintf ppf "@[<hov 1>(Fab %a)@]"
      (print_ty_fabricated_with_cache ~cache) ty

and print ppf t =
  let cache : Printing_cache.t = Printing_cache.create () in
  print_with_cache ~cache ppf t

let print_ty_value ppf ty =
  print_ty_value_with_cache ~cache:(Printing_cache.create ()) ppf ty

let print_ty_fabricated ppf ty =
  print_ty_fabricated_with_cache ~cache:(Printing_cache.create ()) ppf ty