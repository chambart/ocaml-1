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

open Abstract_identifiers
open Flambda

type 'a binds =
  | Simple of let_kind * Variable.t * 'a flambda
  | Rec of (Variable.t * 'a flambda) list

let anf current_compilation_unit tree =
  (* expressions are represented as a couple (binds, expr)
     if binds is [v1, e1; v2, e2; ...; vn, en ] it corresponds to
     {[let v1 = e1 in
       let v2 = e2 in
       ...
       let vn = en in
       expr]}
  *)
  let rec decompose binds = function
    | Fvar _ as expr -> binds, expr
    | Fconst _ as expr -> binds, expr
    | Fsymbol _ as expr -> binds, expr
    | Funreachable _ as expr -> binds, expr
    | Flet (kind, id, lam, body, _) ->
        let binds_lam, elam = decompose binds lam in
        let binds = Simple (kind,id,elam) :: binds_lam in
        decompose binds body
    | Fletrec (defs, body, _) ->
        let defs = List.map (fun (id, lam) -> id, decompose_recompose lam) defs in
        let binds = Rec defs :: binds in
        decompose binds body
    | Fprim(Lambda.Psequand | Lambda.Psequor as prim, [arg1; arg2], dbg, eid) ->
        (* seqand and seqor have a special evaluation order,
           to keep it correct we convert it to ifthenelse *)
        let binds, arg1 = decompose_tovar binds arg1 in
        let ifso, ifnot = match prim with
          | Lambda.Psequand -> anf arg2, Fconst (Fconst_pointer 0, ExprId.create ())
          | _ -> Fconst (Fconst_pointer 1, ExprId.create ()), anf arg2 in
        binds, Fifthenelse(arg1, ifso, ifnot, eid)
    | Fprim(prim, args, dbg, eid) ->
        let binds, args = decompose_tovar_list binds args in
        binds, Fprim(prim, args, dbg, eid)
    | Fsequence(e1,e2,eid) ->
        let binds = ignore_val binds e1 in
        let binds, ex2 = decompose_tovar binds e2 in
        binds, ex2
    | Fapply ({ ap_function; ap_arg; ap_kind; ap_dbg }, eid) ->
        let binds, ap_function = decompose_tovar binds ap_function in
        let binds, ap_arg = decompose_tovar_list binds ap_arg in
        binds, Fapply ({ ap_function; ap_arg; ap_kind; ap_dbg }, eid)
    | Fclosure ({cl_fun; cl_free_var; cl_specialised_arg}, eid) ->
        let binds, cl_free_var = decompose_tovar_idmap binds cl_free_var in
        let cl_fun =
          { cl_fun with
            funs = VarMap.map
                (fun ffun -> { ffun with body = anf ffun.body }) cl_fun.funs } in
        binds, Fclosure ({cl_fun; cl_free_var; cl_specialised_arg}, eid)
    | Ffunction({ fu_closure; fu_fun; fu_relative_to }, eid) ->
        let binds, fu_closure = decompose_tovar binds fu_closure in
        binds, Ffunction({ fu_closure; fu_fun; fu_relative_to }, eid)
    | Fvariable_in_closure ({ vc_closure; vc_fun; vc_var }, eid) ->
        let binds, vc_closure = decompose_tovar binds vc_closure in
        binds, Fvariable_in_closure ({ vc_closure; vc_fun; vc_var }, eid)
    | Fstaticraise (i, args, eid) ->
        let binds, args = decompose_tovar_list binds args in
        binds, Fstaticraise (i, args, eid)
    | Fifthenelse (econd, eso, enot, eid) ->
        let binds, econd = decompose_tovar binds econd in
        binds, Fifthenelse (econd, anf eso, anf enot, eid)
    | Fswitch (econd, sw, eid) ->
        let binds, econd = decompose_tovar binds econd in
        let sw = { sw with
                   fs_consts = List.map (fun (i,e) -> i, anf e) sw.fs_consts;
                   fs_blocks = List.map (fun (i,e) -> i, anf e) sw.fs_blocks;
                   fs_failaction = Misc.may_map anf sw.fs_failaction } in
        binds, Fswitch (econd, sw, eid)
    | Fstaticcatch (i, ids, body, handler, eid) ->
        binds, Fstaticcatch (i, ids, anf body, anf handler, eid)
    | Ftrywith (body, id, handler, eid) ->
        binds, Ftrywith (anf body, id, anf handler, eid)
    | Fwhile (cond, body, eid) ->
        binds, Fwhile (anf cond, anf body, eid)
    | Ffor (id, lo_expr, hi_expr, dir, body, eid) ->
        let binds, lo_expr = decompose_tovar binds lo_expr in
        let binds, hi_expr = decompose_tovar binds hi_expr in
        binds, Ffor (id, lo_expr, hi_expr, dir, anf body, eid)
    | Fassign (id, expr, eid) ->
        let binds, expr = decompose_tovar binds expr in
        binds, Fassign (id, expr, eid)
    | Fsend (kind, meth, obj, args, dbg, eid) ->
        (* TODO: check evaluation order ! *)
        let binds, meth = decompose_tovar binds meth in
        let binds, obj = decompose_tovar binds obj in
        let binds, args = decompose_tovar_list binds args in
        binds, Fsend (kind, meth, obj, args, dbg, eid)

    | Fevent (expr, ev, eid) ->
        assert false

  and tovar ?id binds = function
    | (Fvar _ | Fconst _ | Fsymbol _) as expr -> binds, expr
    | expr ->
        let id = match id with
          | None -> Variable.create ~current_compilation_unit "anf"
          | Some id -> Variable.rename ~current_compilation_unit id
        in
        Simple(Not_assigned, id, expr) :: binds, Fvar(id, ExprId.create ())

  and ignore_val binds expr =
    let binds, _ =
      decompose_tovar
        ~id:(Variable.create ~current_compilation_unit "ignore")
        binds expr in
    binds

  and decompose_tovar ?id binds expr =
    let binds, expr = decompose binds expr in
    tovar ?id binds expr

  and decompose_tovar_list binds l =
    let aux expr (binds,exprs) =
      let binds, expr = decompose_tovar binds expr in
      binds, expr :: exprs
    in
    List.fold_right aux l (binds, [])

  and decompose_tovar_idmap binds m =
    let aux id expr (binds,exprs) =
      let binds, expr = decompose_tovar ~id binds expr in
      binds, VarMap.add id expr exprs
    in
    VarMap.fold aux m (binds, VarMap.empty)

  and recompose binds body =
    let aux body = function
      | Simple (kind, id, lam) ->
          Flet (kind, id, lam, body, ExprId.create ())
      | Rec defs ->
          Fletrec (defs, body, ExprId.create ())
    in
    List.fold_left aux body binds

  and decompose_recompose expr =
    let binds, body = decompose [] expr in
    recompose binds body

  and simple_expr_tovar binds expr = match expr with
    (* control expression are kept as is, var and const also, everything
       else is converted to var *)
    | Fswitch _ | Fstaticcatch _ | Fstaticraise _ | Ftrywith _
    | Fifthenelse _ | Fwhile _ | Ffor _
    | Fprim (Lambda.Praise, _,_,_) -> binds, expr

    | Fsymbol _ | Fvar _ | Fconst _ | Fapply _
    | Fclosure _ | Ffunction _ | Fvariable_in_closure _
    | Flet _ | Fletrec _ | Fsequence _
    | Fassign _ | Fsend _ | Fevent _
    | Funreachable _
    | Fprim _ -> tovar binds expr

  and anf expr =
    let binds, body = decompose [] expr in
    let binds, body = simple_expr_tovar binds body in
    recompose binds body

  in
  anf tree


let is_simple = function
  | Fvar _
  | Fconst _
  | Fsymbol _ -> true

  | Fassign _ | Fclosure _ | Fapply _ | Ffunction _
  | Fvariable_in_closure _ | Flet _ | Fletrec _
  | Fprim _ | Fswitch _ | Fstaticraise _ | Fstaticcatch _
  | Ftrywith _ | Fifthenelse _ | Fsequence _
  | Fwhile _ | Ffor _ | Fsend _ | Funreachable _ -> false

  | Fevent _ -> assert false

let rec is_anf = function
  | Fvar _
  | Fconst _
  | Fsymbol _
  | Funreachable _ -> true

  | Flet (kind, id, Flet _, body, _)
  | Flet (kind, id, Fletrec _, body, _) ->
      false

  | Flet (kind, id, lam, body, _) ->
      is_anf lam &&
      is_anf body

  | Fletrec (defs, body, _) ->
      List.for_all (fun (_,expr) -> is_anf expr) defs &&
      is_anf body

  | Fprim( (Lambda.Psequand | Lambda.Psequor) , _, dbg, _) ->
      false

  | Fprim(_, args, _, _)
  | Fstaticraise (_, args, _) ->
      List.for_all is_simple args

  | Fsequence(e1,e2,_) ->
      false

  | Fapply ({ ap_function; ap_arg; ap_kind; ap_dbg }, _) ->
      is_simple ap_function &&
      List.for_all is_simple ap_arg

  | Fclosure ({cl_fun; cl_free_var; cl_specialised_arg}, _) ->
      VarMap.for_all (fun _ e -> is_simple e) cl_free_var &&
      VarMap.for_all (fun _ { body } -> is_anf body) cl_fun.funs

  | Ffunction({ fu_closure = expr }, _)
  | Fvariable_in_closure ({ vc_closure = expr }, _)
  | Fassign (_, expr, _) ->
      is_simple expr

  | Fifthenelse (econd, eso, enot, _) ->
      is_simple econd &&
      is_anf eso &&
      is_anf enot

  | Fswitch (econd, sw, _) ->
      is_simple econd &&
      List.for_all (fun (_,e) -> is_anf e) sw.fs_consts &&
      List.for_all (fun (_,e) -> is_anf e) sw.fs_blocks &&
      (match sw.fs_failaction with
       | None -> true
       | Some e -> is_anf e)

  | Fstaticcatch (_, _, body, handler, _)
  | Ftrywith (body, _, handler, _) ->
      is_anf body &&
      is_anf handler

  | Fwhile (cond, body, _) ->
      is_anf cond &&
      is_anf body

  | Ffor (id, lo_expr, hi_expr, dir, body, _) ->
      is_simple lo_expr &&
      is_simple hi_expr &&
      is_anf body

  | Fsend (kind, meth, obj, args, dbg, _) ->
      is_simple meth &&
      is_simple obj &&
      List.for_all is_simple args

  | Fevent (expr, ev, _) ->
      assert false

let anf current_compilation_unit expr =
  let r = anf current_compilation_unit expr in
  assert(is_anf r);
  r
