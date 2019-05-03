(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                       Pierre Chambart, OCamlPro                        *)
(*           Mark Shinwell and Leo White, Jane Street Europe              *)
(*                                                                        *)
(*   Copyright 2013--2017 OCamlPro SAS                                    *)
(*   Copyright 2014--2017 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

[@@@ocaml.warning "+a-4-9-30-40-41-42"]

module type Env = sig
  (** Environments, following the lexical scope of the program, used during
      simplification.  (See simplify.ml.) *)
  type t

  type result

  val invariant : t -> unit

  (** Create a new environment. *)
  val create
     : never_inline:bool
    -> allow_continuation_inlining:bool
    -> allow_continuation_specialisation:bool
    -> round:int
    -> backend:(module Backend_intf.S)
    -> scope_level_for_lifted_constants:Scope_level.t
    -> t

  (** Obtain the first-class module that gives information about the
      compiler backend being used for compilation. *)
  val backend : t -> (module Backend_intf.S)

  val resolver : t -> (Export_id.t -> Flambda_type.t option)

  (** Whether floating-point arithmetic operations may be evaluated by the
      compiler.  (Typically [false] when the user may change rounding modes
      at runtime.) *)
  val const_float_prop : t -> bool

  (** Which simplification round we are currently in. *)
  val round : t -> int

  val add_symbol_for_lifted_constant : t -> Symbol.t -> Flambda_type.t -> t

  val continuation_scope_level : t -> Scope_level.t

  val increment_continuation_scope_level : t -> t
  val increment_continuation_scope_level_by_half : t -> t
  val decrement_continuation_scope_level : t -> t
  val decrement_continuation_scope_level_by_half : t -> t

  val scope_level_for_lifted_constants : t -> Scope_level.t
  val set_scope_level_for_lifted_constants : t -> Scope_level.t -> t

  (* CR mshinwell: The [Continuation.t] is in the [Continuation.approx.t] *)
  val add_continuation : t -> Continuation.t -> Continuation_approx.t -> t

  val scope_level_of_continuation : t -> Continuation.t -> Scope_level.t

  val find_continuation : t -> Continuation.t -> Continuation_approx.t

  val mem_continuation : t -> Continuation.t -> bool

  val typing_env : t -> Flambda_type.Typing_env.t

  val with_typing_env
     : t
    -> f:(Flambda_type.Typing_env.t -> Flambda_type.Typing_env.t)
    -> t

  (** Erase all variable approximation information and freshening information
      from the given environment.  However, the freshening activation state
      is preserved.  This function is used when rewriting inside a function
      declaration, to avoid (due to a compiler bug) accidental use of
      variables from outer scopes that are not accessible. *)
  val local : t -> t

  (** Determine whether the inliner is currently inside a function body from
      the given set of closures.  This is used to detect whether a given
      function call refers to a function which exists somewhere on the current
      inlining stack. *)
  val inside_set_of_closures_declaration : Set_of_closures_origin.t -> t -> bool

  (** Not inside a closure declaration.
      Toplevel code is the one evaluated when the compilation unit is
      loaded *)
  val at_toplevel : t -> bool

  val is_inside_branch : t -> bool
  val branch_depth : t -> int
  val inside_branch : t -> t

  val increase_closure_depth : t -> t

  (** Mark that call sites contained within code rewritten using the given
      environment should never be replaced by inlined (or unrolled) versions
      of the callee(s). *)
  val set_never_inline : t -> t

  (** Equivalent to [set_never_inline] but only applies to code inside
      a set of closures. *)
  val set_never_inline_inside_closures : t -> t

  (** Unset the restriction from [set_never_inline_inside_closures] *)
  val unset_never_inline_inside_closures : t -> t

  (** Equivalent to [set_never_inline] but does not apply to code inside
      a set of closures. *)
  val set_never_inline_outside_closures : t -> t

  (** Unset the restriction from [set_never_inline_outside_closures] *)
  val unset_never_inline_outside_closures : t -> t

  (** Return whether [set_never_inline] is currently in effect on the given
      environment. *)
  val never_inline : t -> bool

  val never_inline_continuations : t -> bool
  val never_specialise_continuations : t -> bool
  val never_unbox_continuations : t -> bool

  val disallow_continuation_inlining : t -> t
  val disallow_continuation_specialisation : t -> t

  val inlining_level : t -> int

  (** Mark that this environment is used to rewrite code for inlining. This is
      used by the inlining heuristics to decide whether to continue.
      Unconditionally inlined does not take this into account. *)
  val inlining_level_up : t -> t

  (** Whether we are actively unrolling a given function. *)
  val actively_unrolling : t -> Set_of_closures_origin.t -> int option

  (** Start actively unrolling a given function [n] times. *)
  val start_actively_unrolling : t -> Set_of_closures_origin.t -> int -> t

  (** Unroll a function currently actively being unrolled. *)
  val continue_actively_unrolling : t -> Set_of_closures_origin.t -> t

  (** Whether it is permissible to unroll a call to a recursive function
      in the given environment. *)
  val unrolling_allowed : t -> Set_of_closures_origin.t -> bool

  (** Whether the given environment is currently being used to rewrite the
      body of an unrolled recursive function. *)
  val inside_unrolled_function : t -> Set_of_closures_origin.t -> t

  (** Whether it is permissible to inline a call to a function in the given
      environment. *)
  val inlining_allowed : t -> Closure_origin.t -> bool

  (** Whether the given environment is currently being used to rewrite the
      body of an inlined function. *)
  (* CR mshinwell: comment wrong? *)
  val inside_inlined_function : t -> Closure_origin.t -> t

  (** If collecting inlining statistics, record that the inliner is about to
      descend into [closure_id].  This information enables us to produce a
      stack of closures that form a kind of context around an inlining
      decision point. *)
  val note_entering_closure
     : t
    -> closure_id:Closure_id.t
    -> dbg:Debuginfo.t
    -> t

   (** If collecting inlining statistics, record that the inliner is about to
       descend into a call to [closure_id].  This information enables us to
       produce a stack of closures that form a kind of context around an
       inlining decision point. *)
  val note_entering_call
     : t
    -> closure_id:Closure_id.t
    -> dbg:Debuginfo.t
    -> t

   (** If collecting inlining statistics, record that the inliner is about to
       descend into an inlined function call.  This requires that the inliner
       has already entered the call with [note_entering_call]. *)
  val note_entering_inlined : t -> t

   (** If collecting inlining statistics, record that the inliner is about to
       descend into a specialised function definition.  This requires that the
       inliner has already entered the call with [note_entering_call]. *)
  val note_entering_specialised : t -> closure_ids:Closure_id.Set.t -> t

  val enter_set_of_closures_declaration : t -> Set_of_closures_origin.t -> t

  (** Update a given environment to record that the inliner is about to
      descend into [closure_id] and pass the resulting environment to [f].
      If [inline_inside] is [false] then the environment passed to [f] will be
      marked as [never_inline] (see above). *)
  val enter_closure
     : t
    -> closure_id:Closure_id.t
    -> inline_inside:bool
    -> dbg:Debuginfo.t
    -> f:(t -> 'a)
    -> 'a

   (** If collecting inlining statistics, record an inlining decision for the
       call at the top of the closure stack stored inside the given
       environment. *)
  val record_decision
     : t
    -> Inlining_stats_types.Decision.t
    -> unit

  (** Print a human-readable version of the given environment. *)
  val print : Format.formatter -> t -> unit

  (** The environment stores the call-site being inlined to produce
      precise location information. This function sets the current
      call-site being inlined.  *)
  val set_inline_debuginfo : t -> dbg:Debuginfo.t -> t

  (** Appends the locations of inlined call-sites to the [~dbg] argument *)
  val add_inlined_debuginfo : t -> dbg:Debuginfo.t -> Debuginfo.t

  val continuations_in_scope : t -> Continuation_approx.t Continuation.Map.t
end

module type Result = sig
  (** The result structure used during simplification.  (See simplify.ml.) *)

  type env

  module Roll_back_after_speculation : sig
    type t

    val continuations_defined_between_snapshots
       : before:t
      -> after:t
      -> Continuation.Set.t
  end

  type t

  val create : resolver:(Export_id.t -> Flambda_type.t option) -> t

  val union : Flambda_type.Typing_env.t -> t -> t -> t

  (** Check that [prepare_for_Continuation_uses.t] has been called on the given
      result structure. *)
  val is_used_continuation : t -> Continuation.t -> bool

  (** Mark that the given continuation has been used and provide
      an approximation for the arguments. *)
  val use_continuation
    : t
    -> env
    -> Continuation.t
    -> params:Kinded_parameter.t list
    -> Continuation_uses.Use.Kind.t
    -> t

  val snapshot_Continuation_uses : t -> Roll_back_after_speculation.t

  val snapshot_and_forget_continuation_uses
     : t
    -> Roll_back_after_speculation.t * t

  val roll_back_continuation_uses : t -> Roll_back_after_speculation.t -> t

  val continuation_unused : t -> Continuation.t -> bool
  val continuation_defined : t -> Continuation.t -> bool

  (** Return the types to be assigned to the parameters of the given
      continuation according to the usage information of such continuation
      seen thus far.  The typing environment that is to be used as the
      "environment of definition" of the continuation is also returned.
      In the event that no uses of the given continuation have yet been seen,
      [default_env] will be returned as the environment. *)
  (* CR mshinwell: rename [default_env] (or can we even remove it?) *)
  (* CR mshinwell: improve names of these functions.  Not least "parameters"
     not "arguments" *)
  val continuation_args_types
     : t
    -> Continuation.t
    -> arity:Flambda_arity.t
    -> default_env:Flambda_type.Typing_env.t
    -> Flambda_type.t list * Flambda_type.Typing_env.t

  val defined_continuation_args_types
     : t
    -> Continuation.t
    -> arity:Flambda_arity.t
    -> default_env:Flambda_type.Typing_env.t
    -> Flambda_type.t list * Flambda_type.Typing_env.t

  (** Continuation usage information for use after examining the body of
      a [Let_cont] but before [define_continuation] has been called. *)
  val continuation_uses : t -> Continuation_uses.t Continuation.Map.t

  val continuation_uses_for : t -> Continuation.t -> Continuation_uses.t

  val non_recursive_continuations_used_linearly_in_inlinable_position
     : t
    -> Continuation.Set.t

  (** Mark that we are moving up out of the scope of a continuation-binding
      construct. *)
  val exit_scope_of_let_cont
     : t
    -> env
    -> Continuation.t
    -> params:Kinded_parameter.t list
    -> t * Continuation_uses.t

  (** Record the post-simplification definition of a continuation. *)
  val define_continuation
     : t
    -> Continuation.t
    -> env
    -> Recursive.t
    -> Continuation_uses.t
    -> Continuation_approx.t
    -> t

  (** Update all use environments (both for "used" and "defined" continuations)
      such that if [is_present_in_env] is in such an environment then
      [then_add_to_env] will be added with the given approximation.

      This is used after wrappers have been added during continuation unboxing
      to keep [r] up to date. *)
  val update_all_continuation_use_environments
     : t
    -> if_present_in_env:Continuation.t
    -> then_add_to_env:(Continuation.t * Continuation_approx.t)
    -> t

  (* CR mshinwell: maybe combine with previous function? *)
  val update_continuation_parameters
     : t
    -> Continuation.t
    -> params:Kinded_parameter.t list
    -> t

  (** Update the approximation for a defined continuation. *)
  val update_defined_continuation_approx
     : t
    -> Continuation.t
    -> Continuation_approx.t
    -> t

  (** Continuation definition information for the inliner. *)
  val continuation_definitions_with_uses
     : t
    -> (Continuation_uses.t * Continuation_approx.t * env
      * Recursive.t) Continuation.Map.t

  val forget_continuation_definition
     : t
    -> Continuation.t
    -> t

  (** Check that there is no continuation binding construct in scope. *)
  val no_continuations_in_scope : t -> bool

  (** All continuations for which [Continuation_uses.t] has been
      called on the given result structure.  O(n*log(n)). *)
  val used_continuations : t -> Continuation.Set.t

  (** The benefit to be gained by inlining the subexpression whose
      simplification yielded the given result structure. *)
  val benefit : t -> Inlining_cost.Benefit.t

  (** Apply a transformation to the inlining benefit stored within the
      given result structure. *)
  val map_benefit
    : t
    -> (Inlining_cost.Benefit.t -> Inlining_cost.Benefit.t)
    -> t

  (** Add some benefit to the inlining benefit stored within the
      given result structure. *)
  val add_benefit : t -> Inlining_cost.Benefit.t -> t

  (** Set the benefit of inlining the subexpression corresponding to the
      given result structure to zero. *)
  val reset_benefit : t -> t

  val set_inlining_threshold :
    t -> Inlining_cost.Threshold.t option -> t
  val add_inlining_threshold :
    t -> Inlining_cost.Threshold.t -> t
  val sub_inlining_threshold :
    t -> Inlining_cost.Threshold.t -> t
  val inlining_threshold : t -> Inlining_cost.Threshold.t option

  val seen_direct_application : t -> t
  val num_direct_applications : t -> int

  val new_lifted_constant
     : t
    -> name:string
    -> Flambda_type.t
    -> Flambda_static.Static_part.t
    -> Symbol.t * t

  val get_lifted_constants
     : t
    -> (Flambda_type.t * Flambda_kind.t * Flambda_static.Static_part.t)
         Symbol.Map.t

  (* CR mshinwell: Should this be restructured so that [r] explicitly
     contains an [Typing_env_extension.t]? *)

  val clear_env_extension : t -> t

  val add_or_meet_equation : t -> Name.t -> Scope_level.t -> Flambda_type.t -> t

  val add_or_meet_env_extension
     : t
    -> Flambda_type.Typing_env.t
    -> Flambda_type.Typing_env_extension.t
    -> t

  val add_cse
     : t
    -> Flambda_primitive.With_fixed_value.t
    -> bound_to:Name.t
    -> t

  val get_env_extension : t -> Flambda_type.Typing_env_extension.t

  val newly_imported_symbols : t -> Flambda_kind.t Symbol.Map.t
end