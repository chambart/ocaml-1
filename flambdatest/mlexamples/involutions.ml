
let f x =
  not (not (not x))

let g x =
  ~- (~- (~- x))

let h x =
  Int64.(neg (neg (neg x)))

let i x =
  Int32.(neg (neg (neg x)))

let j x =
  Nativeint.(neg (neg (neg x)))

let k x =
  ~-. (~-. (~-. x))
