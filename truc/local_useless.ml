
let rec a =
  let aa =
    for i = 0 to 1 do
      let _ = a :: b in
      ()
    done
  in
  let ab =
    for i = 0 to 1 do
      let _ = aa :: b in
      ()
    done
  in
  ab
and b = a :: b

