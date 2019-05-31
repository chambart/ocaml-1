
class a =
  let () = Gc.full_major () in
  object
  end

let rec b =
  let x = (b,b) in
  let v = new a in
  let y = (x, x) in
  v

(* and c = b :: c *)
