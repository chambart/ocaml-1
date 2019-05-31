
type stuff =
  Cons of int * stuff * stuff

let rec a =
  Cons (1, a, b)
and b =
  let rec c =
    Cons (2, b, d)
  and d =
    Cons (3, c, a)
  in
  let e = Cons (4, c, d) in
  Cons (5, e, a)
