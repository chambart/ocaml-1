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

let nid = ExprId.create

type block =
  { tag : int;
    size : int;
    mut : Asttypes.mutable_flag }

type case =
  | Cstptr of int
  | Block of block

let print_case ppf = function
  | Cstptr i ->
      Format.fprintf ppf "cst %i" i
  | Block {size; tag} ->
      Format.fprintf ppf "block %i %i" tag size

let print_cases ppf l =
  Format.fprintf ppf "@[{ ";
  List.iter (fun c -> Format.fprintf ppf "%a,@ " print_case c) l;
  Format.fprintf ppf "}@]"

type ret =
  | Cases of case list
  | Bottom (* not returning branch: e.g. static raise *)
  | Others

let union_equal ret1 ret2 = match ret1, ret2 with
  | Others, _ | _, Others -> Others
  | Bottom, r | r, Bottom -> r
  | Cases [Block b1], Cases [Block b2] ->
      if b1 = b2
      then ret1
      else Others
  | Cases _, Cases _ -> Others

let union_merge ret1 ret2 = match ret1, ret2 with
  | Others, _ | _, Others -> Others
  | Bottom, r | r, Bottom -> r
  | Cases l1, Cases l2 ->
      Cases (Misc.uniq_sort compare (l1 @ l2))

let union_accum ret1 ret2 = match ret1, ret2 with
  | Bottom, r | r, Bottom -> r
  | Cases l1, Cases l2 ->
      Cases (Misc.uniq_sort compare (l1 @ l2))
  | Cases l, Others
  | Others, Cases l -> Cases l
  | Others, Others -> Others

(****************************************************************

   Pass moving simple expression constructions up in the tree
   to allow further passes to simplify or eliminate them.
   This is not always a win, but it can easilly be reverted
   using simplify_static_exceptions

   More precisely, it transform expressions with multiple tail
   expressions (match/if/trywith/staticcatch) ending with only
   makeblock or const_pointers to a staticraise/staticcatch with a
   single expression in the handler:

   {[if c
     then (1,2)
     else (3,4)]}

   becomes

   {[scatch
       if c
       then sraise exn1(1,2)
       else sraise exn1(3,4)
   with exn1(a,b) -> (a,b)]}

   This patterns helps avoiding allocations with expressions like
   {[let (a,b) = if c then (1,2) else (3,4)]}

   In general it also transform

   {[if c1
     then A (1,2)
     else if c2
     then A (3,4)
     else B]}

   to

   {[scatch scatch
       if c1
       then sraise exn1(1,2)
       else if c2
       then sraise exn1(3,4)
       else sraise exn2
   with exn1(a,b) -> (a,b)
   with exn2 -> B]}

   This allows transforming expressions like
   {[let v = if c then A (1,2) else B in
     match v with
     | A -> exprA
     | B -> exprB]}

   to

   {[if c
     then
       let v = A (1,2) in
       exprA
     else
       let v = B in
       exprB]}

   Avoiding a switch and potential allocations.

   Notes: This pass merge allocation points, it potentially breaks
   memprof.

   Notes: is it a good idea to restrict to branch with only
   makeblocks ? For instance, it may be worth transforming
   if c then f x else (1,2) also. It could avoid allocating
   the tuple when c is false to the cost of some code
   duplication. Isn't the choice of whether to duplicate or
   not to be done at duplication time rather than here ?

 ****************************************************************)

type exception_builder = case -> Static_exception.t

let make_sexn () : exception_builder =
  let h = Hashtbl.create 1 in
  fun (b:case) ->
    try Hashtbl.find h b
    with Not_found ->
      let sexn = Static_exception.create () in
      Hashtbl.add h b sexn;
      sexn

(* In general, it is correct to move expressions to static exception
   handlers if:
   {expr} is transformed to
   {catch expr' with exn -> handler} where expr' is expr where some
   instances of expression handler are replaced by staticraise(exn,vars)

   - handler must always appear in tail position in expr
   - if handler is bellow a trywith in expr, handler must not raise
   - if handler is bellow a staticcatch exn', handler must not raise exn'
   - if handler is not bellow a Fclosure

   In this case the exceptions restriction is trivially respected: only
   integer constants and makeblock construction are moved.
*)

(* The returns values are
   Others: no tail expression was modified
   Bottom: no tail expression was modified and the expression is known not to return
   Cases l: some tail expressions where modified to raise an exception,
            l is the list of kind of expressions modified (Fconst(Fconst_pointer),
            or makeblock)

   union is a function to accumulate informations about modifieds tail: if it returns
   Others, modifications are dropped *)
let rec lift_tail_expression union make_exn expr = match expr with
  | Fconst(Fconst_pointer i, d) ->
      let case = Cstptr i in
      let sexn = make_exn case in
      Cases [case],
      Fstaticraise(sexn, [], d)
  | Fprim(Lambda.Pmakeblock(tag,mut), args, _, d) ->
      let case = Block { tag; mut; size = List.length args } in
      let sexn = make_exn case in
      Cases [case],
      Fstaticraise(sexn, args, d)
  | Fprim(Lambda.Praise, _, _, _) ->
      Bottom, expr
  | Fstaticraise _ ->
      Bottom, expr
  | Flet(kind, var, def, body, d) ->
      let ret, body = lift_tail_expression union make_exn body in
      ret, Flet(kind, var, def, body, d)
  | Fifthenelse(cond, ifso, ifnot, d) ->
      let r1, ifso = lift_tail_expression union make_exn ifso in
      let r2, ifnot = lift_tail_expression union make_exn ifnot in
      let ret = union r1 r2 in
      if ret = Others
      then Others, expr
      else ret, Fifthenelse(cond, ifso, ifnot, d)
  | Fsequence(e1,e2,d) ->
      let ret, e2 = lift_tail_expression union make_exn e2 in
      ret, Fsequence(e1,e2,d)
  | Fstaticcatch(sexn, vars, body, handler, d) ->
      let r1, body = lift_tail_expression union make_exn body in
      let r2, handler = lift_tail_expression union make_exn handler in
      let ret = union r1 r2 in
      if ret = Others
      then Others, expr
      else ret, Fstaticcatch(sexn, vars, body, handler, d)
  | Ftrywith(body, var, handler, d) ->
      let r1, body = lift_tail_expression union make_exn body in
      let r2, handler = lift_tail_expression union make_exn handler in
      let ret = union r1 r2 in
      if ret = Others
      then Others, expr
      else ret, Ftrywith(body, var, handler, d)
  | Fswitch(arg,sw,d) ->
      let aux (i,flam) (ret,l) =
        match ret with
        | Others -> Others, (i,flam) :: l
        | _ ->
            let r, flam = lift_tail_expression union make_exn flam in
            union r ret, (i, flam) :: l
      in
      let ret, fs_failaction = match sw.fs_failaction with
        | None -> Bottom, None
        | Some flam ->
            let ret, flam = lift_tail_expression union make_exn flam in
            ret, Some flam
      in
      let ret, fs_consts = List.fold_right aux sw.fs_consts (ret, []) in
      let ret, fs_blocks = List.fold_right aux sw.fs_blocks (ret, []) in
      if ret = Others
      then ret, expr
      else ret, Fswitch(arg,{sw with fs_failaction; fs_consts; fs_blocks},d)

  | _ -> Others, expr

let rec interval x y = (* [x; x+1; x+2; ... y] *)
  if x > y
  then []
  else x :: (interval (x+1) y)

let case_expression ~current_compilation_unit = function
  | Block { tag; size; mut } ->
      let free_vars =
        List.map (fun i ->
            Variable.create ~current_compilation_unit
              (Printf.sprintf "lift_block_%i" i))
          (interval 0 (size-1)) in
      let args = List.map (fun v -> Fvar(v, ExprId.create ())) free_vars in
      Fprim(Lambda.Pmakeblock(tag,mut),args,Debuginfo.none,ExprId.create ()),
      free_vars
  | Cstptr i ->
      Fconst(Fconst_pointer i, ExprId.create ()), []

let if_static_raise tree current_compilation_unit =
  let rec aux acc _bound expr =
    let expr = match expr with
      | Fstaticcatch _
      | Ftrywith _
      | Fifthenelse _
      | Fswitch _ ->
          let make_exn = make_sexn () in
          begin match lift_tail_expression union_merge make_exn expr with
          | Cases cases, body ->
              let add_handler case body =
                let handler, free_vars = case_expression ~current_compilation_unit case in
                Fstaticcatch(make_exn case,free_vars,body,handler,ExprId.create ())
              in
              let ret = List.fold_right add_handler cases body in
              ret
          | (Others | Bottom), _  -> expr
          end
      | e -> e
    in
    (* Use fold_subexpressions rather than map, to go top down, rather than bottom up *)
    Flambdaiter.fold_subexpressions aux acc expr in
  let (), e = aux () VarSet.empty tree in
  e


(******************************************************************
   Pass simplifying some recognised staticcatch/trywith patterns.
   See let_match comments for the list.
*******************************************************************)

let rec never_returns = function
  | Fstaticraise _
  | Fprim(Lambda.Praise, _, _, _) ->
      true
  | Fprim(_, [], _, d) -> false
  | Fprim(_, args, _, d) ->
      List.for_all never_returns args
  | Fsequence(e1,e2,_)
  | Flet(_, _, e1, e2, _) ->
      never_returns e1 || never_returns e2
  | Fifthenelse(cond, ifso, ifnot, _) ->
      never_returns cond ||
      (never_returns ifso && never_returns ifnot)
  | Ftrywith(body, _, handler, _)
  | Fstaticcatch(_, _, body, handler, _) ->
      never_returns body && never_returns handler
  | Fswitch(arg,sw,d) ->
      let aux (_,e) = never_returns e in
      never_returns arg ||
      (List.for_all aux sw.fs_consts &&
       List.for_all aux sw.fs_blocks &&
       match sw.fs_failaction with
       | None -> true
       | Some e -> never_returns e)
  | _ -> false

module Approx = struct

  type 'a env =
    { vars : ret VarMap.t;
      static_exn : (Variable.t list * 'a flambda) StaticExceptionMap.t }

  let empty_env =
    { vars = VarMap.empty;
      static_exn = StaticExceptionMap.empty }

  let add_var env var = function
    | Others -> env
    | e -> { env with vars = VarMap.add var e env.vars }

  let add_static_exn env exn vars expr =
    let static_exn =
      StaticExceptionMap.add exn (vars, expr) env.static_exn in
    { env with static_exn }

  let cases_ints cases =
    let aux acc case =
      match acc with
      | None -> None
      | Some acc_lst ->
          match case with
          | Cstptr i -> Some (i :: acc_lst)
          | Block _ -> None
    in
    List.fold_left aux (Some []) cases

  let eval_comparison comp cases1 cases2 =
    let test (i:int) j =
      let open Lambda in
      match comp with
      | Ceq -> i = j
      | Cneq -> i <> j
      | Clt -> i < j
      | Cgt -> i > j
      | Cle -> i <= j
      | Cge -> i >= j
    in
    match cases_ints cases1, cases_ints cases2 with
    | None, _ | _, None | Some [], _ | _, Some [] -> None
    | Some ((h1::_ ) as l1), Some ((h2::_) as l2) ->
        let base_case = test h1 h2 in
        let aux v =
          let aux2 v2 = test v v2 = base_case in
          List.for_all aux2 l2
        in
        if List.for_all aux l1
        then Some base_case
        else None

  let bool_case b =
    if b
    then Cases [Cstptr 1]
    else Cases [Cstptr 0]

  (* A simple approximation of potentially returned values: used to
     find if an expression correspond to a single match/if case *)
  let rec branch_returns union env = function
    | Fconst(Fconst_base (Asttypes.Const_int i), d)
    | Fconst(Fconst_pointer i, d) ->
        Cases [Cstptr i]
    | Fprim(Lambda.Pmakeblock(tag,mut), args, _, _) ->
        Cases [Block { tag; mut; size = List.length args }]
    | Fprim(Lambda.Praise, _, _, _) ->
        Bottom
    | Fprim(Lambda.Pintcomp cmp, [arg1; arg2], _, _) ->
        begin match branch_returns union env arg1,
                    branch_returns union env arg2 with
        | Cases cases1, Cases cases2 ->
            begin match eval_comparison cmp cases1 cases2 with
            | None -> Others
            | Some b -> bool_case b
            end
        | Bottom, _ | _, Bottom -> Bottom
        | _, _ -> Others
        end
    | Fprim(Lambda.Pisint, [arg], _, _) ->
        begin match branch_returns union env arg with
        | Bottom -> Bottom
        | Others | Cases [] -> Others
        | Cases ((_::_) as cases) ->
            let aux = function Cstptr _ -> true | Block _ -> false in
            let isint = List.for_all aux cases in
            let isblock = not (List.exists aux cases) in
            match isint, isblock with
            | true, true -> assert false
            | true, false -> bool_case true
            | false, true -> bool_case false
            | false, false -> Others
        end
    | Fvar(var, _) ->
        if VarMap.mem var env.vars
        then VarMap.find var env.vars
        else Others
    | Flet(Not_assigned, var, def, body, _) ->
        let env = add_var env var (branch_returns union env def) in
        branch_returns union env body
    | Fifthenelse(_cond, ifso, ifnot, _) ->
        union
          (branch_returns union env ifso)
          (branch_returns union env ifnot)
    | Fswitch(_arg,sw,_) ->
        let aux (i,flam) acc =
          match acc with
          | Others -> Others
          | _ -> union acc (branch_returns union env flam) in
        let fail = match sw.fs_failaction with
          | None -> Bottom
          | Some flam -> branch_returns union env flam in
        fail
        |> List.fold_right aux sw.fs_consts
        |> List.fold_right aux sw.fs_blocks
    | Fstaticcatch(exn, vars, body, handler, _) ->
        let env = add_static_exn env exn vars handler in
        branch_returns union env body
    | Fstaticraise(exn, args, _) ->
        if StaticExceptionMap.mem exn env.static_exn
        then
          let (vars, handler) = StaticExceptionMap.find exn env.static_exn in
          let args = List.map (branch_returns union env) args in
          let env = List.fold_left2 add_var env vars args in
          branch_returns union env handler
        else Bottom
    | Ftrywith(body, _, handler, _) ->
        union
          (branch_returns union env body)
          (branch_returns union env handler)
    | Fsequence(_,flam,_) ->
        branch_returns union env flam
    | _ -> Others

  let branch_returns' union var approx expr =
    let env = { empty_env with vars = VarMap.singleton var approx } in
    branch_returns union env expr

  let branch_returns union expr =
    branch_returns union empty_env expr

end

let bool_approx = function
  | Others | Bottom -> None
  | Cases [] -> assert false
  | Cases (h :: t) ->
      let case_to_bool = function
        | Block _ -> true
        | Cstptr i -> i <> 0 in
      let hb = case_to_bool h in
      if List.for_all (fun c -> case_to_bool c = hb) t
      then Some hb
      else None

let is_boolable var approx expr =
  bool_approx (Approx.branch_returns' union_merge var approx expr)

type matchings =
  | Single_case of ExprId.t flambda
  | Failaction
  | Other_case

(* [Some branch] if there is a single branch of the switch matching all the cases,
   [None] otherwise *)
let matching_switch_case returning_expr sw =
  let result_case =
    match Approx.branch_returns union_merge returning_expr with
    | Others | Bottom -> Other_case
    | Cases [] -> assert false
    | Cases (h::t) ->
        let find_case = function
          | Cstptr i ->
              (try
                 let _, expr = List.find (fun (j,_) -> i = j) sw.fs_consts in
                 Single_case expr
               with Not_found ->
                 Failaction)
          | Block {tag} ->
              (try
                 let _, expr = List.find (fun (j,_) -> tag = j) sw.fs_blocks in
                 Single_case expr
               with Not_found ->
                 Failaction)
        in
        let aux acc case =
          match acc with
          | Single_case _ | Other_case -> Other_case
          | Failaction ->
              match find_case case with
              | Failaction -> Failaction
              | Single_case _ | Other_case -> Other_case
        in
        List.fold_left aux (find_case h) t
  in
  match result_case with
  | Other_case -> None
  | Single_case expr -> Some expr
  | Failaction ->
      match sw.fs_failaction with
      | None ->
          Format.printf "unreachable staticraise@.";
          Some (Funreachable (nid ()))
      | Some expr -> Some expr

(* Common representation of both staticcatch and trywith to factorise
   code using only body and handler *)
type catch_descr =
  { body : ExprId.t flambda;
    handler : ExprId.t flambda;
    catch : catch }

and catch =
  | Static of Static_exception.t * Variable.t list * ExprId.t
  | Exn of Variable.t * ExprId.t

let catch_descr = function
  | Fstaticcatch(exn, vars, body, handler, d) ->
      Some { body; handler;
             catch = Static (exn, vars, d) }
  | Ftrywith(body, var, handler, d) ->
      Some { body; handler;
             catch = Exn (var, d) }
  | _ -> None

let catch_descr' e = match catch_descr e with
  | None -> assert false
  | Some e -> e

let rebuild = function
  | { body; handler; catch = Static (exn, vars, d) } ->
      Fstaticcatch(exn, vars, body, handler, d)
  | { body; handler; catch = Exn (var, d) } ->
      Ftrywith(body, var, handler, d)

let is_trywith = function
  | Static _ -> false
  | Exn _ -> true

(* simplify branching expressions when some informations are known
   about the potential return values *)

let rec let_match comp_unit expr =
  let let_match = let_match comp_unit in
  match expr with
  | Flet(_,_,def,_body,_) when never_returns def ->
      (* if def does not return, the body of the let is never
         evaluated and the binding is useless: we keep only def for
         its side effects *)
      Format.printf "elim don't return let @.";
      def

  | Fifthenelse (cond, _ifso, _ifnot, _) when never_returns cond ->
      (* if cond does not return, both cases ifso and ifnot are never
         evaluated: we keep only cond for its side effects *)
      Format.printf "elim don't return if@.";
      cond

  | Fswitch (cond, _, _) when never_returns cond ->
      (* if cond does not return, no branch is ever evaluated: we keep
         only cond for its side effects *)
      Format.printf "elim don't return switch@.";
      cond

  | Flet(kind, var, (Fstaticcatch(_, _, catch_body, _, _)
                    | Ftrywith(catch_body, _, _, _) as def),
         body, dlet) when never_returns catch_body ->
      (* if the body of the catch/trywith expression never returns,
         we can push the let inside the handler:
         {[let x = try raise E with e -> handler in continue]}
         can be transformed to
         {[try raise E with e -> let x = handler in continue]} *)

      let () = Format.printf "push let in exn handler@." in
      let { handler; catch } = catch_descr' def in
      let handler = Flet(kind, var, handler, body, dlet) in
      let handler = let_match handler in
      rebuild { body = catch_body; handler; catch }

  | Flet(kind, var, Fstaticcatch(exn, vars, catch_body, handler, d) , body, dlet) ->
      let rebuild_catch branch =
        let new_var = Variable.rename comp_unit var in
        let subst = VarMap.singleton var new_var in
        (* branch can be duplicated: bound variables must be substituted *)
        match Flambdasubst.substitute_bound_variables comp_unit subst branch with
        | None ->
            Format.printf "failed substitution@.";
            (* failed substitution *)
            expr
        | Some branch ->
            let handler = Flet(kind,new_var,handler,branch,nid ()) in
            let handler = let_match handler in
            let catch_body = Flet(kind,var,catch_body,body,dlet) in
            let catch_body = let_match catch_body in
            Fstaticcatch(exn, vars, catch_body, handler, d)
      in
      begin match body with
      | Fifthenelse (cond, ifso, ifnot, dif) ->
        (* {[let x = catch ... with true in
           if x then ifso else ifnot]}
           is transformed to
           {[catch let x = ... in
                   if x then ifso else ifnot
             with let x = true in ifso]}
        *)
          let approx = Approx.branch_returns union_merge handler in
          begin match is_boolable var approx cond with
          | None -> expr
          | Some b ->
              Format.printf "directly apply if let@.";
              let branch = if b then ifso else ifnot in
              rebuild_catch branch
          end
      | Fswitch (Fvar (var',dv), sw, dsw)
        when Variable.equal var var' ->
        (* {[let x = catch ... with (v,...) -> ... A (x,y) in
             match x with | ... | A (a,b) -> expr]}
           is transformed to
           {[catch let x = ... in
                   match x with | ... | A (a,b) -> expr
             with (v,...) ->
                  let x = ... A (x,y) in
                  expr]}
        *)
          begin match matching_switch_case handler sw with
          | None -> expr
          | Some branch ->
              Format.printf "directly apply switch let@.";
              rebuild_catch branch
          end
      | _ -> expr
      end

  | Fifthenelse (Fstaticcatch(exn, exn_vars, exn_body, handler, dexn), ifso, ifnot, dif) ->
      begin
        match bool_approx (Approx.branch_returns union_merge handler) with
        | None -> expr
        | Some b ->
            (* {[if catch ... with _ -> true then ifso else ifnot]}
               is transformed to
               {[catch if ... then ifso else ifnot with _ -> true; ifso]}
            *)
            Format.printf "directly apply if@.";
            let branch = if b then ifso else ifnot in
            (* branch can be duplicated: bound variables must be substituted *)
            match Flambdasubst.substitute_bound_variables comp_unit VarMap.empty branch with
            | None ->
                Format.printf "failed substitution@.";
                (* failed substitution *)
                expr
            | Some branch ->
                let exn_body = Fsequence(handler, Fifthenelse(exn_body,ifso,ifnot,dif), nid ()) in
                (* We could clean some simple cases where handler is pure here,
                   but other passes can do it also for us. *)
                let exn_body = let_match exn_body in
                let branch = let_match branch in
                Fstaticcatch(exn, exn_vars, exn_body, branch, dexn)
      end

  | expr -> expr

let move_in_exn tree comp_unit =
  Flambdaiter.map (let_match comp_unit) tree

(******************************************************************
   Pass simplifying non-optimal use of static exceptions:

   When an exception is
   - raised only once or trivial (a integer constant, a variable or a staticraise)
   - and is in tail position
   - and the raise is at the same trywith-depth as the catch
   -> move the handler at the raise position

   When an exception is never raised
   -> remove the handler

*******************************************************************)

type raise_info =
  { raise_count : int;
    raise_max_depth : int;
    raise_is_always_tail : bool }

let simplify_static_exceptions expr comp_unit =
  let catch_depth_tbl = StaticExceptionTbl.create 10 in
  let raise_tbl = StaticExceptionTbl.create 10 in
  let get exn =
    try StaticExceptionTbl.find raise_tbl exn
    with Not_found ->
      { raise_count = 0;
        raise_max_depth = -1;
        raise_is_always_tail = true }
  in
  (* Tail is the set of exception for which the expression is tail (in the catch).
     Level is the number of enclosing trywith. *)
  let rec count ~tail level = function
    | Fstaticraise(exn, args, _) ->
        List.iter (count ~tail:StaticExceptionSet.empty level) args;
        let { raise_count; raise_max_depth; raise_is_always_tail } = get exn in
        let is_tail = StaticExceptionSet.mem exn tail in
        StaticExceptionTbl.replace raise_tbl exn
          { raise_count = raise_count + 1;
            raise_max_depth = max level raise_max_depth;
            raise_is_always_tail = is_tail && raise_is_always_tail }
    | Fstaticcatch (exn,_,body,handler,_) ->
        let body_tail = StaticExceptionSet.add exn tail in
        StaticExceptionTbl.add catch_depth_tbl exn level;
        count ~tail level handler;
        count ~tail:body_tail level body
    | Ftrywith(body,_,handler,_) ->
        count ~tail level handler;
        count ~tail (level + 1) body
    | Fifthenelse(cond,ifso,ifnot,_) ->
        count ~tail:StaticExceptionSet.empty level cond;
        count ~tail level ifso;
        count ~tail level ifnot
    | Fswitch(arg,sw,_) ->
        count ~tail:StaticExceptionSet.empty level arg;
        let aux (_, expr) = count ~tail level expr in
        List.iter aux sw.fs_consts;
        List.iter aux sw.fs_blocks;
        Misc.may (count ~tail level) sw.fs_failaction
    | Fclosure ({cl_fun;cl_free_var},_) ->
        VarMap.iter (fun _ v -> count ~tail:StaticExceptionSet.empty level v) cl_free_var;
        VarMap.iter (fun _ ffun -> count ~tail:StaticExceptionSet.empty 0 ffun.Flambda.body)
          cl_fun.funs
    | Flet(_,_,e1,e2,_)
    | Fsequence(e1,e2,_) ->
        count ~tail:StaticExceptionSet.empty level e1;
        count ~tail level e2
    | expr ->
        Flambdaiter.apply_on_subexpressions
          (count ~tail:StaticExceptionSet.empty level) expr
  in
  count ~tail:StaticExceptionSet.empty 0 expr;

  let rec is_trivial = function
    | Fstaticraise (_, args, _) ->
        List.for_all is_trivial args
    | Fvar _
    | Fconst(Fconst_base (Asttypes.Const_int _), _)
    | Fconst(Fconst_pointer _, _) -> true
    | _ -> false in

  let rec remove env = function
    | Fstaticraise(exn, args, d) as expr ->
        begin match try Some (StaticExceptionMap.find exn env) with _ -> None with
        | None -> continue env expr
        | Some (vars, handler) ->
            let vars = List.map (fun v -> v, Variable.rename comp_unit v) vars in
            let subst = VarMap.of_list vars in
            let body = Flambdaiter.toplevel_substitution subst handler in
            let aux (_,var) arg body =
              Flet(Not_assigned, var, arg, body, nid ())
            in
            let res = List.fold_right2 aux vars args body in
            remove env res
        end

    | Fstaticcatch(exn, vars, body, handler, d) ->
        let { raise_count; raise_max_depth; raise_is_always_tail } = get exn in
        let catch_depth = StaticExceptionTbl.find catch_depth_tbl exn in
        let handler = remove env handler in
        if raise_count = 0
        then remove env body
        else
          if catch_depth = raise_max_depth &&
             raise_is_always_tail &&
             (raise_count = 1 || is_trivial handler)
          then
            (* if raise_count > 1 then the handler is copied multiple times,
               but this is not a problem since it is a trivial expression:
               i.e. there is no bound variables *)
            let env = StaticExceptionMap.add exn (vars, handler) env in
            remove env body
          else
            Fstaticcatch(exn, vars, remove env body, handler, d)

    | expr -> continue env expr

  and continue env expr =
    let _, expr =
      Flambdaiter.fold_subexpressions (fun _acc _bound expr -> _acc, remove env expr)
        () expr in
    expr in

  remove StaticExceptionMap.empty expr

open Flambdapasses

let if_static_raise_pass =
  { name = "if static raise";
    pass = if_static_raise }

let move_in_exn_pass =
  { name = "move_in_exn";
    pass = move_in_exn }

let simplify_static_exceptions_pass =
  { name = "simplify_static_exceptions";
    pass = simplify_static_exceptions }

let () = Flambdapasses.register_pass Loop 7 if_static_raise_pass
let () = Flambdapasses.register_pass Loop 8 move_in_exn_pass
let () = Flambdapasses.register_pass Loop 9 simplify_static_exceptions_pass

let passes = [if_static_raise_pass; move_in_exn_pass; simplify_static_exceptions_pass]
