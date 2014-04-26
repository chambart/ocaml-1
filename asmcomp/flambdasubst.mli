open Abstract_identifiers
open Flambda

val substitute_bound_variables :
  Symbol.Compilation_unit.t ->
  Variable.t VarMap.t -> 'a flambda -> 'a flambda option
(* [substitute_bound_variables subst expr] renames every bound
   variable in expr. Can fail (return None) if Ffunction couldn't be
   matched with Fclosure. *)
