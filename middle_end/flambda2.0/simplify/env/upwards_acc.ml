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

module DA = Downwards_acc
module R = Simplify_env_and_result.Result
module UE = Simplify_env_and_result.Upwards_env

type t = {
  uenv : UE.t;
  r : R.t;
}

let print ppf { uenv; r; } =
  Format.fprintf ppf "@[<hov 1>(\
      @[(uenv@ %a)@]@ \
      @[(r@ %a)@]\
      )@]"
    UE.print uenv
    R.print r

let create uenv r =
  { uenv;
    r;
  }

let of_dacc dacc =
  { uenv = UE.empty;
    r = DA.r dacc;
  }

let uenv t = t.uenv

let map_uenv t ~f =
  { t with
    uenv = f t.uenv;
  }

let with_uenv t uenv =
  { t with
    uenv;
  }

let r t = t.r

let with_r t r =
  { t with
    r;
  }
