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

open Flambda

let apply_on_subexpressions f = function
  | Fsymbol _
  | Fvar _
  | Fconst _
  | Funreachable _ -> ()

  | Fassign (_,f1,_)
  | Ffunction({fu_closure = f1},_)
  | Fvariable_in_closure({vc_closure = f1},_) ->
    f f1

  | Flet ( _, _, f1, f2,_)
  | Ftrywith (f1,_,f2,_)
  | Fsequence (f1,f2,_)
  | Fwhile (f1,f2,_)
  | Fcatch (_,_,f1,f2,_) ->
    f f1; f f2;

  | Ffor (_,f1,f2,_,f3,_)
  | Fifthenelse (f1,f2,f3,_) ->
    f f1;f f2;f f3

  | Fstaticfail (_,l,_)
  | Fprim (_,l,_,_) ->
    List.iter f l

  | Fapply ({ap_function;ap_arg},_) ->
    List.iter f (ap_function::ap_arg)
  | Fclosure ({cl_fun;cl_free_var},_) ->
    VarMap.iter (fun _ v -> f v) cl_free_var;
    VarMap.iter (fun _ ffun -> f ffun.body) cl_fun.funs
  | Fletrec (defs, body,_) ->
    List.iter (fun (_,l) -> f l) defs;
    f body
  | Fswitch (arg,sw,_) ->
    f arg;
    List.iter (fun (_,l) -> f l) sw.fs_consts;
    List.iter (fun (_,l) -> f l) sw.fs_blocks;
    (match sw.fs_failaction with
     | None -> ()
     | Some f1 -> f f1)
  | Fsend (_,f1,f2,fl,_,_) ->
    List.iter f (f1::f2::fl)

let iter_general ~toplevel f t =
  let rec aux t =
    f t;
    match t with
    | Fsymbol _
    | Fvar _
    | Fconst _ -> ()

    | Fassign (_,f1,_)
    | Ffunction({fu_closure = f1},_)
    | Fvariable_in_closure({vc_closure = f1},_) ->
      aux f1

    | Flet ( _, _, f1, f2,_)
    | Ftrywith (f1,_,f2,_)
    | Fsequence (f1,f2,_)
    | Fwhile (f1,f2,_)
    | Fcatch (_,_,f1,f2,_) ->
      aux f1; aux f2;

    | Ffor (_,f1,f2,_,f3,_)
    | Fifthenelse (f1,f2,f3,_) ->
      aux f1;aux f2;aux f3

    | Fstaticfail (_,l,_)
    | Fprim (_,l,_,_) ->
      iter_list l

    | Fapply ({ap_function = f1; ap_arg = fl},_) ->
      iter_list (f1::fl)

    | Fclosure ({cl_fun = funcs; cl_free_var = fv},_) ->
      VarMap.iter (fun _ v -> aux v) fv;
      if not toplevel
      then VarMap.iter (fun _ ffun -> aux ffun.body) funcs.funs

    | Fletrec (defs, body,_) ->
      List.iter (fun (_,l) -> aux l) defs;
      aux body
    | Fswitch (arg,sw,_) ->
      aux arg;
      List.iter (fun (_,l) -> aux l) sw.fs_consts;
      List.iter (fun (_,l) -> aux l) sw.fs_blocks;
      (match sw.fs_failaction with
       | None -> ()
       | Some f -> aux f)
    | Fsend (_,f1,f2,fl,_,_) ->
      iter_list (f1::f2::fl)
    | Funreachable _ -> ()

  and iter_list l = List.iter aux l in
  aux t

let iter f t = iter_general ~toplevel:false f t
let iter_toplevel f t = iter_general ~toplevel:true f t

let iter_on_closures f t =
  let aux = function
    | Fclosure (clos,data) ->
        f clos data
    | Fassign _ | Fvar _
    | Fsymbol _ | Fconst _ | Fapply _ | Ffunction _
    | Fvariable_in_closure _ | Flet _ | Fletrec _
    | Fprim _ | Fswitch _ | Fstaticfail _ | Fcatch _
    | Ftrywith _ | Fifthenelse _ | Fsequence _
    | Fwhile _ | Ffor _ | Fsend _ | Funreachable _
      -> ()
  in
  iter aux t

let map_general ~toplevel f tree =
  let rec aux tree =
    let exp = match tree with
      | Fsymbol _ -> tree
      | Fvar (id,annot) -> tree
      | Fconst (cst,annot) -> tree
      | Fapply ({ ap_function; ap_arg; ap_kind; ap_dbg }, annot) ->
          Fapply ({ ap_function = aux ap_function;
                    ap_arg = List.map aux ap_arg;
                    ap_kind; ap_dbg }, annot)
      | Fclosure ({ cl_fun; cl_free_var;
                    cl_specialised_arg },annot) ->
          let cl_fun =
            if toplevel
            then cl_fun
            else
              { cl_fun with
                funs = VarMap.map
                    (fun ffun -> { ffun with body = aux ffun.body })
                    cl_fun.funs } in
          Fclosure ({ cl_fun;
                      cl_free_var = VarMap.map aux cl_free_var;
                      cl_specialised_arg }, annot)
      | Ffunction ({ fu_closure; fu_fun; fu_relative_to}, annot) ->
          Ffunction ({ fu_closure = aux fu_closure;
                       fu_fun; fu_relative_to}, annot)
      | Fvariable_in_closure (vc, annot) ->
          Fvariable_in_closure ({ vc with vc_closure = aux vc.vc_closure }, annot)
      | Flet(str, id, lam, body, annot) ->
          let lam = aux lam in
          let body = aux body in
          Flet (str, id, lam, body, annot)
      | Fletrec(defs, body, annot) ->
          let defs = List.map (fun (id,lam) -> id,aux lam) defs in
          let body = aux body in
          Fletrec (defs, body, annot)
      | Fprim(p, args, dbg, annot) ->
          let args = List.map aux args in
          Fprim (p, args, dbg, annot)
      | Fstaticfail(i, args, annot) ->
          let args = List.map aux args in
          Fstaticfail (i, args, annot)
      | Fcatch (i, vars, body, handler, annot) ->
          let body = aux body in
          let handler = aux handler in
          Fcatch (i, vars, body, handler, annot)
      | Ftrywith(body, id, handler, annot) ->
          let body = aux body in
          let handler = aux handler in
          Ftrywith(body, id, handler, annot)
      | Fifthenelse(arg, ifso, ifnot, annot) ->
          let arg = aux arg in
          let ifso = aux ifso in
          let ifnot = aux ifnot in
          Fifthenelse(arg, ifso, ifnot, annot)
      | Fsequence(lam1, lam2, annot) ->
          let lam1 = aux lam1 in
          let lam2 = aux lam2 in
          Fsequence(lam1, lam2, annot)
      | Fwhile(cond, body, annot) ->
          let cond = aux cond in
          let body = aux body in
          Fwhile(cond, body, annot)
      | Fsend(kind, met, obj, args, dbg, annot) ->
          let met = aux met in
          let obj = aux obj in
          let args = List.map aux args in
          Fsend(kind, met, obj, args, dbg, annot)
      | Ffor(id, lo, hi, dir, body, annot) ->
          let lo = aux lo in
          let hi = aux hi in
          let body = aux body in
          Ffor(id, lo, hi, dir, body, annot)
      | Fassign(id, lam, annot) ->
          let lam = aux lam in
          Fassign(id, lam, annot)
      | Fswitch(arg, sw, annot) ->
          let arg = aux arg in
          let sw =
            { sw with
              fs_failaction = Misc.may_map aux sw.fs_failaction;
              fs_consts = List.map (fun (i,v) -> i, aux v) sw.fs_consts;
              fs_blocks = List.map (fun (i,v) -> i, aux v) sw.fs_blocks; } in
          Fswitch(arg, sw, annot)
      | Funreachable _ -> tree
    in
    f exp
  in
  aux tree

let map f tree = map_general ~toplevel:false f tree
let map_toplevel f tree = map_general ~toplevel:true f tree

let free_variables tree =
  let free = ref VarSet.empty in
  let bound = ref VarSet.empty in
  let add id =
    if not (VarSet.mem id !free) then free := VarSet.add id !free in
  let aux = function
    | Fvar (id,_) -> add id
    | Fassign (id,_,_) -> add id
    | Fclosure ({cl_specialised_arg},_) ->
        VarMap.iter (fun _ id -> add id) cl_specialised_arg
    | Ftrywith(_,id,_,_)
    | Ffor(id, _, _, _, _, _)
    | Flet ( _, id, _, _,_) ->
        bound := VarSet.add id !bound
    | Fletrec (l, _,_) ->
        List.iter (fun (id,_) -> bound := VarSet.add id !bound) l
    | Fcatch (_,ids,_,_,_) ->
        List.iter (fun id -> bound := VarSet.add id !bound) ids
    | _ -> ()
  in
  iter_toplevel aux tree;
  VarSet.diff !free !bound
