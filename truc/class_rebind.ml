
class stoff (x:int) (y:int) =
  object (self)
  val z = x
  method a = x
  method b s = print_endline s
  initializer
    if z > 0 then
      ignore (new stoff (z-1) 2222)#a;
    self#b "plop"
end

let v = new stoff 5 3333
