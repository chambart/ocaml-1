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

[@@@ocaml.warning "+9"]
(* Warning 9 is enabled to ensure correct update of each function when
   a field is added to type parameter *)

type parameter = {
  var : Variable.t;
  inline_attribute : Lambda.inline_pattern;
}

let wrap ?(inline_attribute=Lambda.Default) var = {
  var;
  inline_attribute;
}

let var p = p.var

let inline_attribute p = p.inline_attribute

let has_default_inlining_attribute p =
  p.inline_attribute = Lambda.Default

module M =
  Identifiable.Make (struct
    type t = parameter

    let compare
        { var = var1; inline_attribute = _ }
        { var = var2; inline_attribute = _ } =
      Variable.compare var1 var2

    let equal
        { var = var1; inline_attribute = _ }
        { var = var2; inline_attribute = _ } =
      Variable.equal var1 var2

    let hash { var; inline_attribute = _ } =
      Variable.hash var

    let print ppf { var; inline_attribute } =
      match inline_attribute with
      | Default ->
        Variable.print ppf var
      | _ ->
        Format.fprintf ppf "%a[@@inline: %a]"
          Variable.print var
          Printlambda.inline_pattern inline_attribute

    let output o param =
      output_string o (Format.asprintf "%a" print param)
  end)

module T = M.T
include T

module Map = M.Map
module Tbl = M.Tbl
module Set = struct
  include M.Set
  let vars l = Variable.Set.of_list (List.map var l)
end

let rename ?current_compilation_unit ?append p = {
  var = Variable.rename ?current_compilation_unit ?append p.var;
  inline_attribute = p.inline_attribute;
}

let map_var f { var; inline_attribute } = {
  var = f var;
  inline_attribute;
}

module List = struct
  let vars params = List.map (fun param -> param.var) params
end
