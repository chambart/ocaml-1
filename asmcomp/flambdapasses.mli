open Abstract_identifiers
open Flambda

type pass =
  { name : string;
    pass : ExprId.t flambda -> Symbol.Compilation_unit.t -> ExprId.t flambda }

type position =
  | Before
  | Loop
  | After

val register_pass : position -> int -> pass -> unit

val before_passes : unit -> pass list
val loop_passes : unit -> pass list
val after_passes : unit -> pass list
