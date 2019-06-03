
let r = ref 5

class stoff x =
  object (self)
    method plouf s =
      print_endline s
    initializer
      let v = !r in
      decr r;
      if v <= 0 then
        print_endline "end"
      else begin
        print_endline "plop";
        let a = new stumm () in
        a#plouf "coucou"
      end
  end
and stumm () =
  stoff 12

let () = flush stdout

let v =
  new stumm ()
