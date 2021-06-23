
module Foobar : sig

  val foo : unit -> string * int

  val bar : int -> unit -> string * int

end = struct

  type t =
    | A
    | B
    | C

  let[@inline] f x =
    let init = Sys.opaque_identity () in
    let[@inline] g y =
      let h () =
        let () = Sys.opaque_identity init in
        match x with
        | A -> ("A", y)
        | B -> ("B", 1 + 0)
        | C -> ("C", 42 + 0)
      in
      let () = Sys.opaque_identity () in
      h
    in
    let () = Sys.opaque_identity () in
    g

  let foo =
    let g' = (f[@inlined]) A in
    (g'[@inlined]) 13

  let bar x = ((f[@inlined]) B) x

end
