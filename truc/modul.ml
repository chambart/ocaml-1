
module type A = sig
  val a : int
  val b : int
end

module type B = sig
  val b : int
end

let rec a = (module (struct let a = 33 let b = 44 end) : A)
and b =
  let module A = (val a) in
  let b = (module A : A) in
  (a,a)
