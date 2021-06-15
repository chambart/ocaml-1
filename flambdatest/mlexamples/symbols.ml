
let f x = x

let input = Sys.opaque_identity 0
let saucisse = Sys.opaque_identity 0
let input' = (saucisse, input)
let morteau = Sys.opaque_identity 13
let input'' = (morteau, input')

let g y = (1,2), (input + y)

let tuple = (1,2)

let h _ = (1 + 1,42)

let foo _ = (1 + 1, input)



(*
let t =
  if Sys.opaque_identity true then
    (1 + 1, 3)
  else
    (13,1 - 1)
*)

