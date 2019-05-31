
let r = ref 0

let rec a =
  let b =
    incr r;
    print_endline "a";
    !r :: a
  in
  let c =
    r := !r * 3;
    print_endline "b";
    !r :: b
  in
  let rec e =
    incr r;
    print_endline "c";
    !r :: d
  and d =
    r := !r * 2;
    print_endline "d";
    c
  and f =
    r := !r + 2;
    print_endline "e";
    c
  in
  print_endline "f";
  incr r;
  !r :: e
