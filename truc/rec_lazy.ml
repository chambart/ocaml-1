
(* let rec a = lazy (1 :: (Lazy.force b)) *)
(* and b = lazy (2 :: (Lazy.force a)) *)

let rec a = lazy (Lazy.force b)
and b = lazy (Lazy.force a)


let rec a =
  let c x = b + x in
  c 33
and b = a
