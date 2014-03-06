open Flambda
open Test_utils
open Flambdacheck

let check_success f e =
  match f e with
  | No_counter_example -> ()
  | Counter_example _ -> assert false

let check_error f e =
  match f e with
  | No_counter_example -> assert false
  | Counter_example _ -> ()

let v = new_var "v"
let f = new_var "f"
let x = new_var "x"

let ext = new_var_other_unit "ext"

let static_exn = Static_exception.create ()

(* failing every_used_identifier_is_bound *)

let fail1 = fvar v
let fail2 = flet v (fvar v) (int 1)
let fail3 =
  flet v (int 1)
    (fclosure [f,[x],fvar v] [])

(* passing every_used_identifier_is_bound *)

let pass1 = int 1
let pass2 = flet v (int 1) (fvar v)
let pass3 = fclosure [f,[x],fvar v] [v, int 1]

let check_every_used_identifier_is_bound () =
  try
    check_error every_used_identifier_is_bound fail1;
    check_error every_used_identifier_is_bound fail2;
    check_error every_used_identifier_is_bound fail3;
    check_success every_used_identifier_is_bound pass1;
    check_success every_used_identifier_is_bound pass2;
    check_success every_used_identifier_is_bound pass3
  with e -> raise e (* ensure that the call appear in the stack trace *)

(* failing function_free_variables_are_bound_in_the_closure_and_parameters *)

let fail4 =
  Fclosure
    ({ cl_fun = fun_decls [f,[x],fvar v] [x;v];
       cl_free_var = VarMap.empty;
       cl_specialised_arg = VarMap.empty },
     nid ())

let fail5 =
  Fclosure
    ({ cl_fun = fun_decls [f,[],fvar v] [x;v];
       cl_free_var = VarMap.singleton v (int 1);
       cl_specialised_arg = VarMap.empty },
     nid ())

(* passing function_free_variables_are_bound_in_the_closure_and_parameters *)

let pass4 =
  Fclosure
    ({ cl_fun = fun_decls [f,[x],fvar v] [x;v];
       cl_free_var = VarMap.singleton v (int 1);
       cl_specialised_arg = VarMap.empty },
     nid ())

let check_function_free_variables_are_bound_in_the_closure_and_parameters () =
  try
    check_error function_free_variables_are_bound_in_the_closure_and_parameters fail4;
    check_error function_free_variables_are_bound_in_the_closure_and_parameters fail5;
    check_success function_free_variables_are_bound_in_the_closure_and_parameters pass4
  with e -> raise e

(* failing no_identifier_bound_multiple_times *)

let fail6 =
  fseq [
    flet v (int 1) (fvar v);
    flet v (int 1) (fvar v);
  ]

let fail7 =
  fseq [
    flet v (int 1) (fvar v);
    fclosure [f,[x],fvar v] [v, int 1]
  ]

let fail8 =
  fseq [
    flet x (int 1) (fvar x);
    fclosure [f,[x],int 1] []
  ]

let fail9 =
  fseq [
    flet v (int 1) (fvar v);
    ffor v (int 1) (int 2) (fvar v);
  ]

let fail10 =
  fseq [
    flet v (int 1) (fvar v);
    ftry (int 1) v (int 2);
  ]

let fail11 =
  fseq [
    flet v (int 1) (fvar v);
    ftry (int 1) v (int 2);
  ]

let fail12 =
  fseq [
    flet v (int 1) (fvar v);
    fcatch static_exn [v] (int 1) (int 2);
  ]

(* passing no_identifier_bound_multiple_times *)

let pass6 =
  fseq [
    flet v (int 1) (fvar v);
    flet x (int 1) (fvar x);
  ]

let check_no_identifier_bound_multiple_times () =
  try
    check_error no_identifier_bound_multiple_times fail6;
    check_error no_identifier_bound_multiple_times fail7;
    check_error no_identifier_bound_multiple_times fail8;
    check_error no_identifier_bound_multiple_times fail9;
    check_error no_identifier_bound_multiple_times fail10;
    check_error no_identifier_bound_multiple_times fail11;
    check_error no_identifier_bound_multiple_times fail12;
    check_success no_identifier_bound_multiple_times pass6;
  with e -> raise e

(* failing every_bound_variable_is_from_current_compilation_unit *)

let fail13 =
  flet ext (int 1) (int 1)

let fail14 =
  ffor ext (int 1) (int 1) (int 1)

let fail15 =
  fclosure [f,[ext],fvar v] [v, int 1]

let fail16 =
  fclosure [f,[x],fvar ext] [ext, int 1]

(* passing every_bound_variable_is_from_current_compilation_unit *)

let pass13 =
  flet v (int 1) (int 1)

let every_bound_variable_is_from_current_compilation_unit () =
  let test =
    every_bound_variable_is_from_current_compilation_unit
      ~current_compilation_unit:compilation_unit in
  try
    check_error test fail13;
    check_error test fail14;
    check_error test fail15;
    check_error test fail16;
    check_success test pass13;
  with e -> raise e

let run () =
  check_every_used_identifier_is_bound ();
  check_function_free_variables_are_bound_in_the_closure_and_parameters ();
  check_no_identifier_bound_multiple_times ();
  every_bound_variable_is_from_current_compilation_unit ()
