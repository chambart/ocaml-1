
module type A = sig class c : object method b : string -> unit end end

module rec A : A = struct

  class c =
    (* let v = new b in *)
    object (self)
      method b s = print_endline s
      initializer
        v#b "coucou"
    end
  and b = A.c
end
