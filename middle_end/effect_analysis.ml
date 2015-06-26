(**************************************************************************)
(*                                                                        *)
(*                                OCaml                                   *)
(*                                                                        *)
(*                       Pierre Chambart, OCamlPro                        *)
(*                  Mark Shinwell, Jane Street Europe                     *)
(*                                                                        *)
(*   Copyright 2015 Institut National de Recherche en Informatique et     *)
(*   en Automatique.  All rights reserved.  This file is distributed      *)
(*   under the terms of the Q Public License version 1.0.                 *)
(*                                                                        *)
(**************************************************************************)

(* CR mshinwell: I made this match exhaustive, but we still need to
   double-check that the assignment for each primitive is correct. *)
let no_effects_prim (prim : Lambda.primitive) =
  match prim with
  | Pidentity
  | Pignore
  | Ploc _
  | Pgetglobal _
  | Pgetglobalfield _
  | Pmakeblock _
  | Pfield _
  | Pfloatfield _
  | Pccall { prim_name =
               ( "caml_format_float" | "caml_format_int" |
                 "caml_int32_format" | "caml_nativeint_format" |
                 "caml_int64_format" ) }
  | Psequand | Psequor | Pnot
  | Pnegint | Paddint | Psubint | Pmulint
  | Pandint | Porint | Pxorint
  | Plslint | Plsrint | Pasrint
  | Pintcomp _
  | Poffsetint _
  | Pintoffloat | Pfloatofint
  | Pnegfloat | Pabsfloat
  | Paddfloat | Psubfloat | Pmulfloat | Pdivfloat
  | Pfloatcomp _
  | Pstringlength
  | Pstringrefu
  | Pmakearray _
  | Parraylength _
  | Parrayrefu _
  | Pisint
  | Pisout
  | Pbittest
  | Pbintofint _
  | Pintofbint _
  | Pcvtbint _
  | Pnegbint _
  | Paddbint _
  | Psubbint _
  | Pmulbint _
  | Pdivbint _
  | Pmodbint _
  | Pandbint _
  | Porbint _
  | Pxorbint _
  | Plslbint _
  | Plsrbint _
  | Pasrbint _
  | Pbintcomp _
  | Pbigarrayref (true, _, _, _)
  | Pbigarraydim _
  | Pstring_load_16 true
  | Pstring_load_32 true
  | Pstring_load_64 true
  | Pbigstring_load_16 true
  | Pbigstring_load_32 true
  | Pbigstring_load_64 true
  | Pctconst _
  | Pbswap16
  | Pbbswap _
  | Pduprecord _
  | Pint_as_pointer -> true

  | Pdivint | Pmodint (* can raise Division_by_zero *)

  | Pstringrefs | Parrayrefs _ | Pbigarrayref (false, _, _, _)
  | Pstring_load_16 false | Pstring_load_32 false | Pstring_load_64 false
  | Pbigstring_load_16 false | Pbigstring_load_32 false
  | Pbigstring_load_64 false (* can raise on index out of bound *)

  | Psetglobal _ | Psetfield _ | Psetfloatfield _
  | Pccall _ | Praise _ | Poffsetref _ | Pstringsetu | Pstringsets
  | Parraysetu _ | Parraysets _ | Pbigarrayset _
  | Psetglobalfield _
  | Pstring_set_16 _ | Pstring_set_32 _ | Pstring_set_64 _
  | Pbigstring_set_16 _ | Pbigstring_set_32 _ | Pbigstring_set_64 _ -> false

  (* removed by previous passes *)
  | Plazyforce
  | Prevapply _
  | Pdirapply _ -> assert false

let rec no_effects (flam : _ Flambda.t) =
  match flam with
  | Fvar _ | Fsymbol _ | Fconst _ -> true
  | Flet (_, _, def, body, _) -> no_effects def && no_effects body
  | Fletrec (defs, body, _) ->
    no_effects body && List.for_all (fun (_, def) -> no_effects def) defs
  | Fprim (p, args, _, _) ->
    no_effects_prim p && List.for_all no_effects args
  | Fset_of_closures ({ free_vars }, _) ->
    Variable.Map.for_all (fun _id def -> no_effects def) free_vars
  | Fselect_closure ({ set_of_closures }, _) -> no_effects set_of_closures
  | Fvar_within_closure ({ closure }, _) -> no_effects closure
  | Fifthenelse (cond, ifso, ifnot, _) ->
    no_effects cond && no_effects ifso && no_effects ifnot
  | Fswitch (lam, sw, _) ->
    let aux (_, lam) = no_effects lam in
    no_effects lam
      && List.for_all aux sw.blocks
      && List.for_all aux sw.consts
      && Misc.may_default no_effects sw.failaction true
  | Fstringswitch (lam, sw, def, _) ->
    no_effects lam
      && List.for_all (fun (_, lam) -> no_effects lam) sw
      && Misc.may_default no_effects def true
  | Fstaticcatch (_, _, body, _, _)
  | Ftrywith (body, _, _, _) ->
    (* If there is a [raise] in [body], the whole [Ftrywith] may have an
       effect, so there is no need to test the handler. *)
    no_effects body
  | Fsequence (l1, l2, _) -> no_effects l1 && no_effects l2
  (* CR mshinwell for pchambart: Is there something subtle here about the
     compilation of [Fwhile] and [Ffor] which means that even a
     non-side-effecting loop body does not imply that the loop itself has
     no effects? *)
  | Fwhile _ | Ffor _ | Fapply _ | Fsend _ | Fassign _
  | Fstaticraise _ -> false
  | Funreachable _ -> true

let sequence (l1 : _ Flambda.t) (l2 : _ Flambda.t) annot : _ Flambda.t =
  if no_effects l1 then
    l2
  else
    (* CR mshinwell for pchambart: Please add a comment explaining how
       these Fconst_pointer | Fconst_base ... sequences arise. *)
    match l2 with
    | Fconst ((Fconst_pointer 0 | Fconst_base (Asttypes.Const_int 0)), _) ->
      Flambda.Fprim (Pignore, [l1], Debuginfo.none, annot)
    | _ ->
      match l1 with
      | Fprim (Pignore, [arg], _, _) -> Fsequence (arg, l2, annot)
      | _ -> Fsequence (l1, l2, annot)
