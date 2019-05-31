(* let v =
 *   let rec a = 1
 *   and b =
 *     (((); ());
 *      ((); 2))
 *   in
 *   b *)


let r = ref 0

let rec a =
  r := !r + 1;
  let xa = !r in
  r := !r + 2;
  let xb = !r in
  xb :: xa :: b
and b =
  r := !r + 3;
  !r :: c
and c =
  r := !r + 4;
  !r :: a
