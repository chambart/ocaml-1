
type a = A of b [@@unboxed]
and b =
    X of a
  | Y

let rec a =
  A
    (if Sys.opaque_identity true then
       X a
     else
       Y)

let v =
  match a with
  | A (X (A (X v))) ->
    v
  | _ -> a
