(***********************************************************************)
(*                                                                     *)
(*                                OCaml                                *)
(*                                                                     *)
(*            Xavier Leroy, projet Cristal, INRIA Rocquencourt         *)
(*                                                                     *)
(*  Copyright 1996 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the Q Public License version 1.0.               *)
(*                                                                     *)
(***********************************************************************)

(* Liveness analysis.
   Annotate mach code with the set of regs live at each point. *)

open Mach

let live_at_exit = ref []
let find_live_at_exit k =
  try
    let (used, set) = List.assoc k !live_at_exit in
    used := true;
    set
  with
  | Not_found -> Misc.fatal_error "Spill.find_live_at_exit"

let live_at_break = ref Reg.Set.empty
let live_at_raise = ref Reg.Set.empty

let rec live i finally =
  (* finally is the set of registers live after execution of the
     instruction sequence.
     The result of the function is the set of registers live just
     before the instruction sequence.
     The instruction i is annotated by the set of registers live across
     the instruction. *)
  match i.desc with
    Iend ->
      i.live <- finally;
      finally
  | Ireturn | Iop(Itailcall_ind) | Iop(Itailcall_imm _) ->
      (* i.live remains empty since no regs are live across *)
      Reg.set_of_array i.arg
  | Iifthenelse(test, ifso, ifnot) ->
      let at_join = live i.next finally in
      let at_fork = Reg.Set.union (live ifso at_join) (live ifnot at_join) in
      i.live <- at_fork;
      Reg.add_set_array at_fork i.arg
  | Iswitch(index, cases) ->
      let at_join = live i.next finally in
      let at_fork = ref Reg.Set.empty in
      for i = 0 to Array.length cases - 1 do
        at_fork := Reg.Set.union !at_fork (live cases.(i) at_join)
      done;
      i.live <- !at_fork;
      Reg.add_set_array !at_fork i.arg
  | Iloop(body) ->
      let at_top = ref Reg.Set.empty in
      (* Yes, there are better algorithms, but we'll just iterate till
         reaching a fixpoint. *)
      begin try
        while true do
          let new_at_top = Reg.Set.union !at_top (live body !at_top) in
          if Reg.Set.equal !at_top new_at_top then raise Exit;
          at_top := new_at_top
        done
      with Exit -> ()
      end;
      i.live <- !at_top;
      !at_top
  | Icatch(nfail, body, handler) ->
      let at_join = live i.next finally in
      let rec fixpoint before_handler =
        let used = ref false in
        live_at_exit := (nfail,(used, before_handler)) :: !live_at_exit ;
        let before_handler' = live handler at_join in
        live_at_exit := List.tl !live_at_exit ;
        let before_handler' = Reg.Set.union before_handler before_handler' in
        if not !used || Reg.Set.equal before_handler before_handler'
        then before_handler'
        else fixpoint before_handler'
      in
      let before_handler = fixpoint Reg.Set.empty in
      (* We could use handler.live instead of Reg.Set.empty as the initialisation
         but we would need to clean the live field before doing the analysis
         (to remove remaining of previous passes) *)
      live_at_exit := (nfail,(ref false, before_handler)) :: !live_at_exit ;
      let before_body = live body at_join in
      live_at_exit := List.tl !live_at_exit ;
      i.live <- before_body;
      before_body
  | Iexit nfail ->
      let this_live = find_live_at_exit nfail in
      i.live <- this_live ;
      this_live
  | Itrywith(body, handler) ->
      let at_join = live i.next finally in
      let before_handler = live handler at_join in
      let saved_live_at_raise = !live_at_raise in
      live_at_raise := Reg.Set.remove Proc.loc_exn_bucket before_handler;
      let before_body = live body at_join in
      live_at_raise := saved_live_at_raise;
      i.live <- before_body;
      before_body
  | Iraise ->
      (* i.live remains empty since no regs are live across *)
      Reg.add_set_array !live_at_raise i.arg
  | _ ->
      let across_after = Reg.diff_set_array (live i.next finally) i.res in
      let across =
        match i.desc with
          Iop Icall_ind | Iop(Icall_imm _) | Iop(Iextcall _)
        | Iop(Iintop Icheckbound) | Iop(Iintop_imm(Icheckbound, _)) ->
            (* The function call may raise an exception, branching to the
               nearest enclosing try ... with. Similarly for bounds checks.
               Hence, everything that must be live at the beginning of
               the exception handler must also be live across this instr. *)
             Reg.Set.union across_after !live_at_raise
         | _ ->
             across_after in
      i.live <- across;
      Reg.add_set_array across i.arg

let fundecl ppf f =
  let initially_live = live f.fun_body Reg.Set.empty in
  (* Sanity check: only function parameters can be live at entrypoint *)
  let wrong_live = Reg.Set.diff initially_live (Reg.set_of_array f.fun_args) in
  if not (Reg.Set.is_empty wrong_live) then begin
    Format.fprintf ppf "%a@." Printmach.regset wrong_live;
    Misc.fatal_error "Liveness.fundecl"
  end
