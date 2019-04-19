(* TEST
   flags = "-g"
   * flambda
   * native
*)

let rec init_tailrec_aux acc i n f =
  if i >= n then acc
  else init_tailrec_aux (f i :: acc) (i+1) n f

type t = floatarray

external length : t -> int = "%floatarray_length"
external unsafe_get : t -> int -> float = "%floatarray_unsafe_get"

let to_list a =
  (init_tailrec_aux [@specialised] [@unrolled 1]) [] 0 (length a) (unsafe_get a)
