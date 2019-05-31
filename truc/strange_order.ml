
let v =
  let rec a = 1
  and b =
    ((((); let c = a in let _ = c in print_endline "a"));
     ((print_endline "b"; print_endline "c"));
     2)
  in
  b
