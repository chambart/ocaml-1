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

let create ~exn_handler ~extra_args =
  { exn_handler;
    extra_args;
  }

let exn_handler t = t.exn_handler

let extra_args t = t.extra_args

let invariant _env _t = ()

let print_simple_and_kind ppf (simple, kind) =
  Format.fprintf ppf "@[(%a :: %a)@]"
    Simple.print simple
    Flambda_kind.print kind

let print ppf { exn_handler; extra_args; } =
  Format.fprintf ppf "@[<hov 1>(\
      @[<hov 1>(exn_handler@ %a)@]@ \
      @[<hov 1>(extra_args@ (%a))@])@]"
    Continuation.print exn_handler
    (Format.pp_print_list ~pp_sep:Format.pp_print_space print_simple_and_kind)
    extra_args

let print_with_cache ~cache:_ ppf t = print ppf t

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
  (K.value ()) :: extra_args