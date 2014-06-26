open Symbol
open Abstract_identifiers
open Flambda
open Test_utils
open Flambdareachability

let e1 =
  flet x (int 1) (fvar x)

let run () =
  let r = steps e1 10 in
  ()

