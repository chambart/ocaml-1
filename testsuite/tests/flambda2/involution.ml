(* TEST
* flambda
** native
*)

(* This test that involution are effectively detected.
   It checks that for an involution f, f (f x) == x
   This is is verified by testing that the result of the physical equality
   is a known constants, through an allocation test. *)

external minor_words : unit -> (float [@unboxed])
  = "caml_gc_minor_words" "caml_gc_minor_words_unboxed"

let[@inline never] check_no_alloc test_name f x =
  let before = minor_words () in
  let _ = Sys.opaque_identity ((f[@inlined never]) x) in
  let after = minor_words () in
  let diff = after -. before in
  if diff = 0. then
    Format.printf "No allocs for test '%s'@." test_name
  else
    Format.printf "Some allocs for test '%s'@." test_name

let () =
  let[@inline] test_known f =
    let tester x =
      let x = Sys.opaque_identity x in
      let n = if (f[@inlined hint]) ((f[@inlined hint]) x) == x then 1 else 0 in
      Int64.of_int n
    in
    let () = Sys.opaque_identity () in
    tester
  in

  (* Test the test: this should allocate *)
  check_no_alloc "not an involution" (test_known (succ)) 1;
  (* Actual tests *)
  check_no_alloc "not" (test_known (not)) true;
  check_no_alloc "~-?" (test_known (~-.)) 42.;
  check_no_alloc "~-" (test_known (~-)) 42;
  check_no_alloc "Int32.neg" (test_known Int32.neg) 42l;
  check_no_alloc "Int64.neg" (test_known Int64.neg) 42L;
  check_no_alloc "Nativeint.neg" (test_known Nativeint.neg) 42n;
  ()

