(* TEST
* flambda
** native
*)

(* Unboxing in loops

   This file contains tests related to unboxing inside loops.  Not every test
   in this file is necessarily meant to succesfully eliminate all (or most)
   allocations. Instead, the tests in this file should try and cover most
   situations where we could reasonably want flambda to unbox things.

   Then, once improvements to flambda make some of the tests in this file pass
   (i.e. make the tests not allocate, or not allocate too much), this will
   trigger an "error" in the testsuite, easily fixable by promoting the result
   file. That way, this test should represent the unboxing capabilities of
   flambda (including what is and is not unboxed).
*)

external minor_words : unit -> (float [@unboxed])
  = "caml_gc_minor_words" "caml_gc_minor_words_unboxed"

let[@inline never] check_no_alloc line f x y expected_res =
  let before = minor_words () in
  let b = (f[@inlined never]) x y expected_res in
  let after = minor_words () in
  let diff = after -. before in
  if not b then
    Format.printf "Bad assert at line %d@." line
  else if diff = 0. then
    Format.printf "No allocs at line %d@." line
  else
    Format.printf "Some allocs at line %d@." line

let[@inline never] check_not_many_allocs max line f x y expected_res =
  let before = minor_words () in
  let f_res = (f[@inlined never]) x y in
  let after = minor_words () in
  let diff = after -. before in
  let b = f_res = expected_res in
  if not b then
    Format.printf "Bad assert at line %d@." line
  else if diff <= max then
    Format.printf "Less than %f allocs at line %d@." max line
  else
    Format.printf "Too many allocs at line %d@." line

module Complex = struct
  type t = { re: float; im: float }
  let zero = { re = 0.0; im = 0.0 }
  let one = { re = 1.0; im = 0.0 }
  let[@inline] add x y = { re = x.re +. y.re; im = x.im +. y.im }

  let[@inline] arg x = atan2 x.im x.re

  let[@inline] norm x =
    (* Watch out for overflow in computing re^2 + im^2 *)
    let r = abs_float x.re and i = abs_float x.im in
    if r = 0.0 then i
    else if i = 0.0 then r
    else if r >= i then
      let q = i /. r in r *. sqrt(1.0 +. q *. q)
    else
      let q = r /. i in i *. sqrt(1.0 +. q *. q)
end

module T = struct

  type t =
    | A
    | B
    | C of int
    | D of int * int

end

let () =

  (* Check int32s *)
  let aux n y res =
    let r = ref y in
    for i = 0 to n do
      r := Int32.(add !r one)
    done;
    !r = res
  in
  check_no_alloc __LINE__ aux 0 1l 2l;
  check_no_alloc __LINE__ aux 5 1l 7l;
  (* Check int64s *)
  let aux n y res =
    let r = ref y in
    for i = 0 to n do
      r := Int64.(add !r one)
    done;
    !r = res
  in
  check_no_alloc __LINE__ aux 0 1L 2L;
  check_no_alloc __LINE__ aux 5 1L 7L;
  (* Check nativeints *)
  let aux n y res =
    let r = ref y in
    for i = 0 to n do
      r := Nativeint.(add !r one)
    done;
    !r = res
  in
  check_no_alloc __LINE__ aux 0 1n 2n;
  check_no_alloc __LINE__ aux 5 1n 7n;
  (* Check floats *)
  let aux n y res =
    let r = ref y in
    for i = 0 to n do
      r := !r +. 1.
    done;
    !r *. 2. = res
  in
  check_no_alloc __LINE__ aux 0 1. 4.;
  check_no_alloc __LINE__ aux 5 1. 14.;
  (* Check floats again,
     As of writing this test, floats in a loop are unboxed iff the first
     outisde *after* the loop can also make use of the unboxed version. This
     test is here to ascertain whether that limitation is still there. The
     point of this test is that at one point in the future, only the return
     value of [aux] should be allocated, and not any of the floats inside of
     the loop; thus by having a high loop count, we can check whether the float
     in the loop was unboxed by verifying that the number of words allocated is
  less than a small constant. *)
  let[@inline] aux n y =
    let r = ref y in
    for i = 0 to n - 1 do
      r := !r +. 1.
    done;
    !r
  in
  check_not_many_allocs 5. __LINE__ aux 1_000 0. 1_000.;
  check_not_many_allocs 5. __LINE__ aux 10_000 0. 10_000.;
  (* Check tuple *)
  let aux n ((_x, _y) as t) res =
    let r = ref t in
    for i = 0 to n do
      let x, y = !r in
      r := y, x
    done;
    let x, y = !r in
    x - y = res
  in
  check_no_alloc __LINE__ aux 0 (1,2) 1;
  check_no_alloc __LINE__ aux 1 (1,2) ~-1;
  (* Check nested tuples *)
  let aux n (((_x, _y), _z) as t) res =
    let r = ref t in
    for i = 0 to n do
      let ((x, y), z) = !r in
      r := (y, z), x
    done;
    let (x, y), z = !r in
    x + (y - z) = res
  in
  check_no_alloc __LINE__ aux 0 ((1,2),3) 4;
  check_no_alloc __LINE__ aux 1 ((1,2),3) 2;
  (* Check tuple+floats *)
  let aux n ((_x, _y) as t) res =
    let r = ref t in
    for i = 0 to n do
      let x, y = !r in
      r := x +. y, x -. y
    done;
    let x, y = !r in
    x +. y = res
  in
  check_no_alloc __LINE__ aux 0 (1.,2.) 2.;
  check_no_alloc __LINE__ aux 1 (1.,2.) 6.;
  (* Check blocks and floats *)
  let aux n (c1, c2) res =
    let r = ref c1 in
    for i = 0 to n do
      r := (Complex.add[@inlined]) !r c2;
    done;
    let f =
      if n mod 2 = 0
      then (Complex.arg[@inlined]) !r
      else (Complex.norm[@inlined]) !r
    in
    f = res
  in
  check_no_alloc __LINE__ aux 0 (Complex.zero, Complex.one) 0.;
  check_no_alloc __LINE__ aux 1 (Complex.zero, Complex.one) 2.;
  (* Check variants *)
  let aux n x res =
    let r = ref None in
    for i = 0 to n do
      match !r with
      | None -> r := Some x
      | Some _ -> r := None
    done;
    let r =
      match !r with
      | None -> 13
      | Some x -> x
    in
    r = res
  in
  check_no_alloc __LINE__ aux 0 0 0;
  check_no_alloc __LINE__ aux 1 0 13;
  (* Check more complicated variant *)
  let aux n (a, b) res =
    let r = ref T.A in
    for i = 0 to n do
      match (!r : T.t) with
      | A -> r := B
      | B -> r := C a
      | C _ -> r := D (a, b)
      | D _ -> r := A
    done;
    let e =
      match (!r : T.t) with
      | C a -> a
      | D (a, b) -> a + b
      | A -> 42
      | B -> 50
    in
    e = res
  in
  check_no_alloc __LINE__ aux 0 (1,2) 50;
  check_no_alloc __LINE__ aux 1 (1,2) 1;
  check_no_alloc __LINE__ aux 2 (1,2) 3;
  check_no_alloc __LINE__ aux 3 (1,2) 42;
  (* END *)
  ()

