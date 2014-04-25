open Abstract_identifiers
open Flambda

val move_lets : ExprId.t flambda -> ExprId.t flambda

val remove_trivial_lets : 'a flambda -> 'a flambda

val passes : Flambdapasses.pass list
