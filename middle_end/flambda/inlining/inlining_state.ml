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

type t = {
  arguments: Inlining_arguments.t;
  depth: int
}

let increment_depth t = { t with depth = t.depth + 1 }

let default = {
    arguments = Inlining_arguments.unknown;
    depth = 0
  }

let create ~arguments ~depth = { arguments; depth }

let print ppf t =
  Format.fprintf ppf "@[<hov 1>(depth@ %d, arguments@ %a)@]"
    t.depth
    Inlining_arguments.print t.arguments

let is_depth_exceeded t =
  (* CR-soon lmaurer: Fix this once rec_info is functional again; hardcoding
     depth of 1 until then *)
  if true then t.depth >= 1 else
    t.depth >= (Inlining_arguments.max_inlining_depth t.arguments)
  
let meet t1 t2 = {
  depth = t1.depth + t2.depth;
  arguments = Inlining_arguments.meet t1.arguments t2.arguments
}

let equal t1 t2 =
  t1.depth = t2.depth
  && Inlining_arguments.equal t1.arguments t2.arguments

let invariant t = assert (t.depth >= 0)

let with_arguments arguments t = { t with arguments }

let arguments t = t.arguments
