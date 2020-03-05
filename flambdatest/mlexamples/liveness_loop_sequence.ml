type nonrec 'a ref = { mutable contents : 'a }
external ref : 'a -> 'a ref = "%makemutable"
external incr : int ref -> unit = "%incr"
external ( ! ) : 'a ref -> 'a = "%field0"

let f x y =
  let r = ref y in
  for i = 0 to x do incr r; done;
  for i = 0 to x do incr r; done;
  for i = 0 to x do incr r; done;
  for i = 0 to x do incr r; done;
  for i = 0 to x do incr r; done;
  for i = 0 to x do incr r; done;
  for i = 0 to x do incr r; done;
  for i = 0 to x do incr r; done;
  for i = 0 to x do incr r; done;
  for i = 0 to x do incr r; done;
  for i = 0 to x do incr r; done;
  for i = 0 to x do incr r; done;
  for i = 0 to x do incr r; done;
  for i = 0 to x do incr r; done;
  for i = 0 to x do incr r; done;
  for i = 0 to x do incr r; done;
  !r
