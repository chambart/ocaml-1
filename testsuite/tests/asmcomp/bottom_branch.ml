let f x =
  let a =
    if x then
      fun v -> v + 1
    else
      raise Not_found
  in
  (a [@inlined]) 1

let () = assert((f [@inlined never]) true = 2)

let g () =
  let a =
    try
      fun v -> v + 1
    with _ ->
      raise Not_found
  in
  (a [@inlined]) 1

let () = assert((g [@inlined never]) () = 2)
