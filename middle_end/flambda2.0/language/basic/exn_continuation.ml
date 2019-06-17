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
  exn_handler : Continuation.t;
  extra_args : (Simple.t * Flambda_kind.t) list;
}

include Identifiable.Make (struct
  type nonrec t = t

  let print_simple_and_kind ppf (simple, kind) =
    Format.fprintf ppf "@[<h>(%a@ \u{2237}@ %a)@]"
      Simple.print simple
      Flambda_kind.print kind

  let print ppf { exn_handler; extra_args; } =
    Format.fprintf ppf "@[<hov 1>(\
        @[<hov 1>(exn_handler@ %a)@]@ \
        @[<hov 1>@<0>%s(extra_args@ @<0>%s(%a)@<0>%s@<0>)@<0>%s@])@]"
      Continuation.print exn_handler
      (match extra_args with
       | [] -> Flambda_colours.elide ()
       | _ -> Flambda_colours.normal ())
      (Flambda_colours.normal ())
      (Format.pp_print_list ~pp_sep:Format.pp_print_space print_simple_and_kind)
      extra_args
      (match extra_args with
       | [] -> Flambda_colours.elide ()
       | _ -> Flambda_colours.normal ())
      (Flambda_colours.normal ())

  let compare_simple_and_kind (simple1, kind1) (simple2, kind2) =
    let c = Simple.compare simple1 simple2 in
    if c <> 0 then c
    else Flambda_kind.compare kind1 kind2

  let compare
        { exn_handler = exn_handler1; extra_args = extra_args1; }
        { exn_handler = exn_handler2; extra_args = extra_args2; } =
    let c = Continuation.compare exn_handler1 exn_handler2 in
    if c <> 0 then c
    else
      Misc.Stdlib.List.compare compare_simple_and_kind
        extra_args1 extra_args2

  let equal t1 t2 =
    compare t1 t2 = 0

  let output _ _ = Misc.fatal_error "Not yet implemented"

  let hash _ = Misc.fatal_error "Exn_continuation.hash not yet implemented"
end)

let print_with_cache ~cache:_ ppf t = print ppf t

let create ~exn_handler ~extra_args =
  { exn_handler;
    extra_args;
  }

let exn_handler t = t.exn_handler

let extra_args t = t.extra_args

let invariant _env _t = ()

let free_names { exn_handler; extra_args; } =
  let extra_args = List.map (fun (simple, _kind) -> simple) extra_args in
  Name_occurrences.union
    (Name_occurrences.singleton_continuation exn_handler)
    (Simple.List.free_names extra_args)

let apply_name_permutation ({ exn_handler; extra_args; } as t) perm =
  let exn_handler' = Name_permutation.apply_continuation perm exn_handler in
  let extra_args' =
    List.map (fun ((simple, kind) as extra_arg) ->
        let simple' = Simple.apply_name_permutation simple perm in
        if simple == simple' then extra_arg
        else simple', kind)
      extra_args
  in
  if exn_handler == exn_handler' && extra_args == extra_args' then t
  else { exn_handler = exn_handler'; extra_args = extra_args'; }

let arity t =
  let extra_args = List.map (fun (_simple, kind) -> kind) t.extra_args in
  Flambda_kind.value :: extra_args

let with_exn_handler t exn_handler =
  { t with exn_handler; }
