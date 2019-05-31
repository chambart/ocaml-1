
(* let rec a = [1] *)
(* and b = *)
(*   let x = a in *)
(*   let y = x in *)
(*   let z = (x, y) in *)
(*   z *)



let rec b =
  let rec y = b in
  let z = 1 :: x in
  z
