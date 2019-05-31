
type v = L of v list
let r = ref 0

let rec l =
  L [] :: m
and m =
  (incr r; L l) :: l
