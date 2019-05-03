(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                       Pierre Chambart, OCamlPro                        *)
(*           Mark Shinwell and Leo White, Jane Street Europe              *)
(*                                                                        *)
(*   Copyright 2018 OCamlPro SAS                                          *)
(*   Copyright 2018 Jane Street Group LLC                                 *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

[@@@ocaml.warning "+a-4-9-30-40-41-42"]

type t = {
  var : Variable.t;
  kind : Flambda_kind.t;
}

include Identifiable.Make (struct
  type nonrec t = t

  let compare 
        { var = var1; kind = kind1; }
        { var = var2; kind = kind2; } =
    let c = Variable.compare var1 var2 in
    if c <> 0 then c
    else Flambda_kind.compare kind1 kind2

  let equal t1 t2 = (compare t1 t2 = 0)

  let hash { var; kind; } =
    Hashtbl.hash (Variable.hash var, Flambda_kind.hash kind)

  let print ppf { var; kind; } =
    Format.fprintf ppf "@[@<0>%s(@<0>%s%a@<0>%s ::@ %a)@]"
      (Misc.Color.reset ())
      (Misc.Color.bold_green ())
      Variable.print var
      (Misc.Color.reset ())
      Flambda_kind.print kind

  let output chan t =
    print (Format.formatter_of_out_channel chan) t
end)

let create kind =
  { var = Variable.create "lv";
    kind;
  }

let kind t = t.kind

let rename t =
  { t with
    var = Variable.rename t.var;
  }

let in_compilation_unit t comp_unit =
  Variable.in_compilation_unit t.var comp_unit