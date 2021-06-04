
let[@inline] g x =
  let x = x + 1 in
  let h y = x + y in
  let () = Sys.opaque_identity () in
  h


let f z =
  let h = (g[@inlined]) z in
  let () = Sys.opaque_identity () in
  h



