
let r = ref 5
class stoff x =
  let _v = new stoff in
  object (self)
  method b s = print_endline s
  initializer
    if !r > 0 then begin
      decr r;
      ignore ((new stumm)#b "plop");
      self#b "plip"
    end
end
and stumm =
  (* let a = new stumm in *)
  stoff 12
(* let v = new stoff 5 3333 *)
and stimm =
  match None with
  | None ->
    (fun t -> stumm)
  | Some _ ->
    let a = 33 in
    (fun t -> stumm)

let v =
  new stumm
