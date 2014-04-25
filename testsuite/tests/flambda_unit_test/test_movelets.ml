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

let impure_expr () = fccall []

let expr1 = flet v (int 1) (fvar v)
let expr2 = flet x (int 1) (flet v (int 1) (fvar v))
let expr3 = flet x (impure_expr ()) (int 1)
let expr4 =
  flet x (impure_expr ())
    (flet y (impure_expr ()) (int 1))
let expr5 =
  flet x
    (flet y (int 1) (fvar y))
    (fvar x)
let expr6 =
  flet x
    (int 1)
    (fif (fbool true)
       (int 1)
       (fvar x))
let expr7 =
  flet x
    (int 1)
    (fif (fbool true)
       (fvar x)
       (fvar x))
let expr8 =
  flet y
    (int 1)
    (flet x
       (fvar y)
       (fif (fbool true)
          (fvar y)
          (fvar x)))
let expr9 =
  flet y
    (int 1)
    (flet z
       (fvar y)
       (flet x
          (fvar y)
          (fif (fbool true)
             (fvar z)
             (fvar x))))
let expr10 =
  flet x (int 1)
    (fwhile (fbool true)
       (fvar x))
let expr11 =
    (fwhile (fbool true)
       (flet x (int 1)
          (fvar x)))
let expr12 =
    (fwhile (fbool true)
       (flet y (impure_expr ())
          (flet x (fvar y)
             (fvar x))))
let expr13 =
    (fwhile (fbool true)
       (flet y (impure_expr ())
          (flet x (fvar y)
             (flet z (int 1)
                (fadd (fvar x) (fvar z))))))
let expr14 =
  let inner_while =
    (fwhile (fbool true)
       (flet y (impure_expr ())
          (flet x (fvar y)
             (flet z (fvar b)
                (flet a (int 1)
                   (fadd
                      (fadd (fvar x) (fvar z))
                      (fadd (fvar a) (int 1))))))))
  in
  (fwhile (fbool true)
     (flet b (impure_expr ())
        inner_while))
let expr15 =
    (fwhile (fbool true)
       (flet y (impure_expr ())
          (flet a (int 1)
             (flet x (fvar a)
                (flet z (int 1)
                   (fadd (fvar x) (fvar z)))))))


let launch (s,e) =
  let e' = Flambdamovelets.move_lets e in
  Format.printf "%s@ orig:@ %a@.moved:@ %a@."
    s
    Printflambda.flambda e
    Printflambda.flambda e';
  check e;
  check e'

let run () =
  List.iter launch
    [ "1", expr1;
      "2", expr2;
      "3", expr3;
      "4", expr4;
      "5", expr5;
      "6", expr6;
      "7", expr7;
      "8", expr8;
      "9", expr9;
      "10", expr10;
      "11", expr11;
      "12", expr12;
      "13", expr13;
      "14", expr14;
      "15", expr15; ]
