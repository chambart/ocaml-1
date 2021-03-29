type ('a, 'b) t = A of int * 'a | B of 'b

let[@inline] f b y z g =
  let v =
    if b then
      A (42, g y)
    else
      B (g z)
  in
  match v with
  | A (_, a) -> a
  | B c -> c

let[@inline] g x = 12

let test b y z =
  f b y z g
