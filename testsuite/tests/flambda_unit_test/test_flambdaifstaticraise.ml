open Symbol
open Abstract_identifiers
open Flambda
open Test_utils

let check expr =
  Flambdacheck.check
    ~current_compilation_unit:compilation_unit
    expr

let v = new_var "v"
let f = new_var "f"
let g = new_var "g"
let x = new_var "x"
let y = new_var "y"
let z = new_var "z"
let a = new_var "a"
let b = new_var "b"

let expr1 = tuple [int 1;int 2]
let expr2 =
  fif (fbool true)
    (tuple [int 1;int 2])
    (tuple [int 3;int 4])
let expr3 =
  fif (fbool true)
    (fseq [
        int 33;
        tuple [int 4;int 5];
      ])
    (expr2)

let launch (s,e) =
  let e' = Flambdaifstaticraise.if_static_raise e compilation_unit in
  Format.printf "%s@ orig:@ %a@.converted:@ %a@."
    s
    Printflambda.flambda e
    Printflambda.flambda e';
  check e;
  check e'

let run () =
  List.iter launch
    [ "1", expr1;
      "2", expr2;
      "3", expr3; ]
