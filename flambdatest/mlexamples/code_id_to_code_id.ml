

let f y =
  let g x = x + y in
  Sys.opaque_identity ();
  g

