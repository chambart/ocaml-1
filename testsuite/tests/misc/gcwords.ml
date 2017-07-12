type t = Leaf of int | Branch of t * t

let a = [| 0.0 |]

let rec allocate_lots m = function
  | 0 -> Leaf m
  | n -> Branch (allocate_lots m (n-1), allocate_lots (m+1) (n-1))

(* Inlining is prevented to stop Flambda from lifting [a] and [c] to
   toplevel [Initialize_symbol] constructs, which would necessitate
   boxing of the floats therein. *)
let [@inline never] measure f =
  let a = Gc.minor_words () in
  f ();
  let c = Gc.minor_words () in
  c -. a

let () =
  let n = measure (fun () -> a.(0) <- Gc.minor_words ()) in
  (* Gc.minor_words should not allocate, although bytecode
     generally boxes the floats *)
  assert (n < 10.);
  if Sys.backend_type = Sys.Native then assert (n = 0.);
  let n = measure (fun () -> Sys.opaque_identity (allocate_lots 42 10)) in
  (* This should allocate > 3k words (varying slightly by unboxing) *)
  assert (n > 3000.);
  print_endline "ok"
