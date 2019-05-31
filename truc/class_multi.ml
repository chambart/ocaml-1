class stuff = object (self)

  method a = 1
  method plop = self#a
end

and toto = object (self)

  method a = new stuff
  method plop = self#a
end
