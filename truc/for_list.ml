let rec a =
  for i = 0 to 10 do let _ = () :: b in () done
and b = a :: []
