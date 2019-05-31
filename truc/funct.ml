
module type A = sig
  val a : int
  val b : int
end

module type B = sig
  val b : int
end

(* module F(A:A) = struct *)
(*   let b = A.a + A.b *)
(* end *)

module F(A:A) = struct
  let a = 1
  let b = A.a + A.b
end


let rec a =
  let _ = (a,a) in
  (module (F (struct let a = 33 let b = 44 end)) : A)
and b =
  let exception E : 'a -> exn in
  E b


(* let rec a = (module (F (val b : A)) : A) *)
(* and b = (module (F (struct let a = 33 let b = 44 end)) : A) *)

(* and b = *)
(*   let module A = (val a) in *)
(*   let b = (module A : B) in *)
(*   (a,b) *)

(* let rec a = (module (struct let a = 33 let b = 44 end) : A) *)


(* and b = *)
(*   let module A = (val a) in *)
(*   let b = (module A : A) in *)
(*   (a,a) *)
