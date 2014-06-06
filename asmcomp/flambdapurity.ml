(***********************************************************************)
(*                                                                     *)
(*                                OCaml                                *)
(*                                                                     *)
(*                     Pierre Chambart, OCamlPro                       *)
(*                                                                     *)
(*  Copyright 2014 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the Q Public License version 1.0.               *)
(*                                                                     *)
(***********************************************************************)

open Lambda
open Abstract_identifiers
open Flambda

module CFS = ClosureFunctionSet
module CFM = ClosureFunctionMap

let pure_primitive = function
  | Pidentity
  | Pgetglobal _
  | Pmakeblock (_, Asttypes.Immutable)
  | Psequand
  | Psequor
  | Pnot
  | Pnegint
  | Paddint
  | Psubint
  | Pmulint
  | Pmodint
  | Pandint
  | Porint
  | Pxorint
  | Plslint
  | Plsrint
  | Pasrint
  | Pintcomp _
  | Poffsetint _
  | Pintoffloat
  | Pfloatofint
  | Pnegfloat
  | Pabsfloat
  | Paddfloat
  | Psubfloat
  | Pmulfloat
  | Pdivfloat
  | Pfloatcomp _
  | Pstringlength
  | Parraylength _
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
  | Pmodbint _
  | Pandbint _
  | Porbint _
  | Pxorbint _
  | Plslbint _
  | Plsrbint _
  | Pasrbint _
  | Pbintcomp _
  | Pbigarraydim _
  | Pctconst _
  | Pbswap16
  | Pbbswap _ -> true

  | Pignore (* Not impure but it is used for effectful expression, so it is not
               a problem to mark it as impure.
               Marking it as impure simplify benchmarking by preventing some
               useless computation to be droped *)

  | Pmakeblock (_, Asttypes.Mutable) (* Moving mutables could change sharing *)
  | Prevapply _
  | Pdirapply _
  | Psetglobal _
  | Pgetglobalfield _ (* The order of getglobalfields are quite fixed *)
  | Psetglobalfield _
  | Pfield _
  | Psetfield _
  | Pfloatfield _
  | Psetfloatfield _
  | Pduprecord _
  | Plazyforce
  | Pccall _
  | Praise
  | Pdivbint _ | Pdivint (* Can raise divide by zero *)
  | Poffsetref _
  | Pstringrefu
  | Pstringsetu
  | Pstringrefs
  | Pstringsets
  | Pmakearray _ (* sharing *)
  | Parrayrefu _
  | Parraysetu _
  | Parrayrefs _
  | Parraysets _
  | Pbigarrayref _
  | Pbigarrayset _
  | Pstring_load_16 _
  | Pstring_load_32 _
  | Pstring_load_64 _
  | Pstring_set_16 _
  | Pstring_set_32 _
  | Pstring_set_64 _
  | Pbigstring_load_16 _
  | Pbigstring_load_32 _
  | Pbigstring_load_64 _
  | Pbigstring_set_16 _
  | Pbigstring_set_32 _
  | Pbigstring_set_64 _ -> false

type env =
  { pure_functions : ClosureFunctionSet.t;
    pure_variables : VarSet.t;
    bound_variables : VarSet.t;
    local_static_exn : StaticExceptionSet.t;
    exception_caugh : bool }

(* Environment building functions *)

let empty_env =
  { pure_functions = ClosureFunctionSet.empty;
    pure_variables = VarSet.empty;
    bound_variables = VarSet.empty;
    local_static_exn = StaticExceptionSet.empty;
    exception_caugh = false }

let mark_pure_functions pure_functions env =
  { env with pure_functions = CFS.union pure_functions env.pure_functions }

let mark_unasigned_variable var env =
  { env with pure_variables = VarSet.add var env.pure_variables }

(* Tree traversal *)

type pure =
  | Pure_if of ClosureFunctionSet.t
  | Impure

let is_pure env expr =
  let dep = ref ClosureFunctionSet.empty in
  let add_dep cf = dep := ClosureFunctionSet.add cf !dep in
  let rec pure env expr = match expr with
    | Fvar (v,_) ->
        VarSet.mem v env.bound_variables ||
        VarSet.mem v env.pure_variables
    | Fsymbol _
    | Fconst _ -> true

    | Flet (_,v,def,body,_) ->
        pure env def &&
        pure { env with bound_variables = VarSet.add v env.bound_variables } body

    | Fletrec (defs,body,_) ->
        let bound_variables =
          List.fold_left
            (fun set (v,_) -> VarSet.add v set)
            env.bound_variables
            defs
        in
        let env = { env with bound_variables } in
        pure env body &&
        List.for_all (fun (_,def) -> pure env def) defs

    | Fprim(Pfield _, args, _, _) ->
        (* TODO: special case *)
        false

    | Fprim(Praise, args, _, _) ->
        env.exception_caugh &&
        List.for_all (pure env) args

    | Fprim(p, args, _, _) ->
        pure_primitive p &&
        List.for_all (pure env) args

    | Fclosure ({ cl_free_var }, _) ->
        VarMap.for_all (fun id def -> pure env def) cl_free_var

    | Ffunction _
    | Fvariable_in_closure _
    | Fifthenelse _
    | Fswitch _
    | Fsequence _
    | Fwhile _
    | Ffor _ ->
        let aux (bound,expr) =
          let env = { env with pure_variables = VarSet.union bound env.pure_variables } in
          pure env expr
        in
        List.for_all aux (Flambdaiter.subexpression_bound_variables expr)

    | Fstaticcatch (exn,vars,body,handler,_) ->
        (let pure_variables = VarSet.union (env.pure_variables) (VarSet.of_list vars) in
         let env = { env with pure_variables } in
         pure env handler) &&
        let env =
          { env with
            local_static_exn =
              StaticExceptionSet.add exn env.local_static_exn } in
        pure env body

    | Ftrywith (body, var, handler, _) ->
        (let env = { env with pure_variables = VarSet.add var env.pure_variables } in
         pure env handler) &&
        let env = { env with exception_caugh = true } in
        pure env body

    | Fassign (var,flam,_) ->
        VarSet.mem var env.bound_variables &&
        pure env flam

    | Fstaticraise (exn,args, _) ->
        StaticExceptionSet.mem exn env.local_static_exn &&
        List.for_all (pure env) args

    | Fapply({ ap_kind = Indirect },_) ->
        false

    | Fapply({ ap_function; ap_arg; ap_kind = Direct direct },_) ->

        let res =
          pure env ap_function &&
          List.for_all (pure env) ap_arg in
        if res && not (ClosureFunctionSet.mem direct env.pure_functions)
        then add_dep direct;
        res

    | Fsend _ ->
        false

    | Funreachable _ -> true

    | Fevent _ -> assert false
  in
  let r = pure env expr in
  if r
  then Pure_if !dep
  else Impure

let pure_expression_toplevel env expr =
  match is_pure env expr with
  | Pure_if s -> ClosureFunctionSet.is_empty s
  | Impure -> false

let pure_function fun_decl =
  let env = { empty_env with bound_variables = fun_decl.free_variables } in
  is_pure env fun_decl.body

let collect_function_dep expr : pure CFM.t =
  let map = ref CFM.empty in
  let aux = function
    | Fclosure(closure, _) ->
        VarMap.iter
          (fun var fun_decl ->
             map :=
               CFM.add
                 (Closure_function.wrap var)
                 (pure_function fun_decl)
                 !map)
          closure.cl_fun.funs
    | _ -> ()
  in
  Flambdaiter.iter aux expr;
  !map

let reverse map =
  let impure = ref CFS.empty in
  let reversed = ref CFM.empty in
  CFM.iter (fun dst -> function
      | Impure ->
          impure := CFS.add dst !impure
      | Pure_if deps ->
          CFS.iter (fun src ->
              if CFM.mem src map
              then
                let s = try CFM.find src !reversed with
                  | Not_found -> CFS.empty in
                reversed := CFM.add src (CFS.add dst s) !reversed
              else
                impure := CFS.add dst !impure)
            deps)
    map;
  !impure, !reversed

let propagate map : CFS.t =
  let impure', dep = reverse map in
  let impure = ref impure' in
  let work_queue = ref impure' in
  while not (CFS.is_empty !work_queue) do
    let v = CFS.choose !work_queue in
    work_queue := CFS.remove v !work_queue;
    try
      let deps = CFM.find v dep in
      work_queue := CFS.union deps !work_queue;
      impure := CFS.union deps !impure
    with Not_found -> ()
  done;
  CFS.diff (CFM.keys map) !impure

let pure_functions expr =
  propagate (collect_function_dep expr)

(* Simple purity function *)

let pure_expression env expr =
  let env = mark_pure_functions (pure_functions expr) env in
  match is_pure env expr with
  | Pure_if s -> ClosureFunctionSet.is_empty s
  | Impure -> false
