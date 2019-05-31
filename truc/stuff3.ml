let r = ref 0
let s = ref 0
let t = ref []

let rec l =
  incr r;
  1 :: m
and m =
  incr r;
  incr s;
  let toto =
    let _ = (l, l) in
    incr r
  in
  1 :: l
