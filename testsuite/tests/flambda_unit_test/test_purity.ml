open Symbol
open Abstract_identifiers
open Flambda
open Test_utils
open Flambdapurity

type pure =
  | Pure
  | Impure

let static_exn = Static_exception.create ()
let static_exn' = Static_exception.create ()

let call_fibo =
  fapply
    ~kind:(Direct fibo_fun)
    fibonacci
    [int 5]

let g_func = Closure_function.wrap g
let f_var_g_func_env =
  mark_unasigned_variable f
    (mark_pure_functions
       (ClosureFunctionSet.singleton g_func)
       empty_env)

let tests =
  [ "pure1",
    Pure,
    empty_env,
    tuple [int 1;int 2];

    "pure2",
    Pure,
    empty_env,
    flet x (int 1) (fvar x);

    "pure3",
    Pure,
    empty_env,
    fcatch static_exn []
      (fstaticraise static_exn [])
      (int 1);

    "pure4",
    Pure,
    empty_env,
    call_fibo;

    "pure5",
    Pure,
    f_var_g_func_env,
    fapply
      ~kind:(Direct g_func)
      (fvar f)
      [int 5];

    "impure1",
    Impure,
    empty_env,
    fvar x;

    "impure2",
    Impure,
    empty_env,
    fcatch static_exn []
      (fstaticraise static_exn' [])
      (int 1);
  ]

let test (name, is_pure, env, expr) =
  let r = Flambdapurity.pure_expression env expr in
  let correct = match r, is_pure with
    | true, Pure
    | false, Impure -> true
    | true, Impure | false, Pure -> false in
  if not correct
  then failwith (Printf.sprintf "incorrect purity: %s" name)

let run () =
  List.iter test tests;
  Format.printf "purity passed@."
