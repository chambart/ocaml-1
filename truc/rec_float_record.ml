
type r = { a : float; b : float }

let rec a = 3.14
and b =
  let _ = { a; b = a } in
  ()
