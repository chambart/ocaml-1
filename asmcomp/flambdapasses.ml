open Abstract_identifiers
open Flambda

type pass =
  { name : string;
    pass : ExprId.t flambda -> Symbol.Compilation_unit.t -> ExprId.t flambda }

type position =
  | Before
  | Loop
  | After

let before : (int * pass) list ref = ref []
let loop : (int * pass) list ref = ref []
let after : (int * pass) list ref = ref []

let register_pass position weight pass =
  match position with
  | Before ->
      before := (weight, pass) :: !before
  | Loop ->
      loop := (weight, pass) :: !loop
  | After ->
      after := (weight, pass) :: !after

let sort_passes l =
  List.map snd
    (List.sort (fun (p1,_) (p2,_) -> compare p1 p2) l)

let before_passes () = sort_passes !before
let loop_passes () = sort_passes !loop
let after_passes () = sort_passes !after
