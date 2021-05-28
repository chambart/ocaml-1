(* TEST
   * flambda
   ** native
   ocamlopt_flags = "-g"
   ** native
   ocamlopt_flags = ""
*)

let h x =
  try
    if x then
      Sys.opaque_identity succ 1
    else raise Exit
  with
  (* This will ends up producing a switch where one branch is a reraise.
     But this only happens after simplification to inline intermediate
     continuation. So this is done in two function for the first one to
     be simplified before being used in a problematic context. *)
    Exit -> 5
[@@inline]

let g x =
  try
    h x
  with
    (* This exception continuation will be turned into a normal continuation
       in the non debug version of the test *)
    Not_found -> 33
[@@inline never]

let () = print_endline (string_of_int (g true))
let () = print_endline (string_of_int (g false))
