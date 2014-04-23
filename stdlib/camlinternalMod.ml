(***********************************************************************)
(*                                                                     *)
(*                                OCaml                                *)
(*                                                                     *)
(*         Xavier Leroy, projet Cristal, INRIA Rocquencourt            *)
(*                                                                     *)
(*  Copyright 2004 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the GNU Library General Public License, with    *)
(*  the special exception on linking described in file ../LICENSE.     *)
(*                                                                     *)
(***********************************************************************)

type shape =
  | Function
  | Lazy
  | Class
  | Module of shape array

let rec init_mod loc shape =
  match shape with
  | Function ->
      let r = ref true in
      r := false;
      let pad1 = if !r then Some 1 else None in
      let pad2 = if !r then Some 1 else None in
      let pad3 = if !r then Some 1 else None in
      let pad4 = if !r then Some 1 else None in
      let pad5 = if !r then Some 1 else None in
      let pad6 = if !r then Some 1 else None in
      let pad7 = if !r then Some 1 else None in
      let pad8 = if !r then Some 1 else None in
      (* WARINING: those are constants, it will not be put in the
         closure, hence the closure will only contains one free
         variable (loc). This mean that a lot of function have an
         indirection when update_mod initialize them. It could be
         fixed by using references, but those would be useless
         allocations and it would be a bit fragile to further
         optimizations: We probably need a primitive to build dummy
         non dropable values *)
      Obj.repr(fun _ ->
        ignore pad1; ignore pad2; ignore pad3; ignore pad4;
        ignore pad5; ignore pad6; ignore pad7; ignore pad8;
        raise (Undefined_recursive_module loc))
  | Lazy ->
      Obj.repr (lazy (raise (Undefined_recursive_module loc)))
  | Class ->
      Obj.repr (CamlinternalOO.dummy_class loc)
  | Module comps ->
      Obj.repr (Array.map (init_mod loc) comps)

let overwrite o n =
  assert (Obj.size o >= Obj.size n);
  for i = 0 to Obj.size n - 1 do
    Obj.set_field o i (Obj.field n i)
  done

let rec update_mod shape o n =
  match shape with
  | Function ->
      if Obj.tag n = Obj.closure_tag && Obj.size n <= Obj.size o
      then begin overwrite o n; Obj.truncate o (Obj.size n) (* PR #4008 *) end
      else overwrite o (Obj.repr (fun x -> (Obj.obj n : _ -> _) x))
  | Lazy ->
      if Obj.tag n = Obj.lazy_tag then
        Obj.set_field o 0 (Obj.field n 0)
      else if Obj.tag n = Obj.forward_tag then begin (* PR#4316 *)
        Obj.set_tag o Obj.forward_tag;
        Obj.set_field o 0 (Obj.field n 0)
      end else begin
        (* forwarding pointer was shortcut by GC *)
        Obj.set_tag o Obj.forward_tag;
        Obj.set_field o 0 n
      end
  | Class ->
      assert (Obj.tag n = 0 && Obj.size n = 4);
      overwrite o n
  | Module comps ->
      assert (Obj.tag n = 0 && Obj.size n >= Array.length comps);
      for i = 0 to Array.length comps - 1 do
        update_mod comps.(i) (Obj.field o i) (Obj.field n i)
      done
