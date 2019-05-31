class c =
  object
    val x = 3
    method y =
      let rec t =
        for i = 0 to 3 do
          let _ = [u] in
          ()
        done
      and u =
        (t, v, w)
      and v =
        let rec y = [w] in
        x
      and w =
        let rec y = [u] in
        new c
      in
      v
  end
