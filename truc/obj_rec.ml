

let v =
  object
    val x = 3
    method y =
      let rec v = x in
      v
  end
