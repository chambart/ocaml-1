
let rec u =
  let v =
    if Sys.opaque_identity true then
      2 :: w
    else
      []
  in
  v
and w =
  let x =
    if Sys.opaque_identity true then
      1 :: u
    else
      []
  in
  x

let n = List.hd (List.tl (List.tl w))

let () = print_endline (string_of_int n)
