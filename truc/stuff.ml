
let r = ref 0
let s = ref 0
let t = ref []
let rec l =
  incr r;
  1 :: m
and m =
  incr r;
  incr s;
  let v = 2 :: l in
  let rec a = 33 :: b
  and b = 44 :: a
  and sira_num = 3
  and sira x n =
    if x mod 2 = 0 then
      cuse x n
    else
      sira (sira_num * x + 1) (succ n)
  and cuse x n =
    if x = 2 then n
    else sira (x / 2) n
  in
  let rec w = 4 :: x
  and x = sira 3 0 :: v in
  s := 2 + !s;
  t := b;
  !r :: w
