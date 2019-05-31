
let r = ref 0

let rec f =
  incr r;
  let rec g x = h (x+1)
  and h x =
    ignore l;
    i x in
  fun x -> g x

and i x =
  if x > 33 then x
  else
    f x

and j =
  for i = 0 to 10 do
    let rec a = f
    and b = l
    and c = i
    and d = j
    and e = [c]
    in
    incr r;
  done


and l = (i, j) :: l
