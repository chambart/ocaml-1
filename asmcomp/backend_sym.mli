(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                  Mark Shinwell, Jane Street Europe                     *)
(*                                                                        *)
(*   Copyright 2018--2019 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(** Names of object file symbols (including OCaml-specific mangling
    conventions) together with knowledge about whether such symbols refer
    to code or data.

    Since we need to represent symbols that live in the startup files and
    external libraries, in addition to those within normal OCaml compilation
    units (i.e. those arising from OCaml source files), object file symbols
    are tied to [Object_file]s rather than [Compilation_unit]s.

    If you're looking for the place where symbol names are mangled using
    OCaml-specific (rather than target-specific) conventions, it's here.
*)

[@@@ocaml.warning "+a-4-30-40-41-42"]

(** The type of backend symbols. *)
type t
type backend_sym = t

(** Sets, maps, total ordering, etc.

    The [print] function sends a non-escaped version of the symbol to a
    formatter. This must not be used for assembly emission or similar
    (use [Asm_symbol] instead). *)
include Identifiable.S with type t := t

(** Like [print] but returns a string.  The returned name will be unique to
    the given symbol, but as for [print], such name is not for assembly
    emission or similar. *)
(* CR mshinwell: This is being used for [ndl_loadsym] *)
val to_string : t -> string

(** Whether a symbol points at executable code ("text") or data.

    Unlike [Asm_symbol]s, [Backend_sym]s of kind [Data] always point at
    correctly-structured OCaml values, just like [Symbol]s.
*)
type kind = Text | Data

(** Create a backend symbol, in the current compilation unit (translated
    to a [Backend_compilation_unit]) unless specified otherwise, given a base
    name.  The base name should not be escaped, prefixed or mangled in any
    way; such operations are performed by this module and then [Asm_symbol]. *)
val create
   : ?compilation_unit:Backend_compilation_unit.t
  -> base_name:string
  -> kind
  -> t

(** Create a backend symbol to refer to an external function. *)
val create_for_external_call : Primitive.description -> t

(** Create a backend symbol given the mangled form.  This function should not
    currently be used except in the Cmm testsuite. *)
val unsafe_create
   : ?compilation_unit:Backend_compilation_unit.t
  -> string
  -> kind
  -> t

(** Create a backend symbol from a middle end symbol.  (The resulting symbol
    will always be of kind [Data].) *)
val of_symbol : Symbol.t -> t

(** Create a symbol to correspond to a lifted constant that does not have a
    source-level name associated with it.  If [compilation_unit] is not provided
    then it is assumed that [Compilation_unit.set_current] has been called
    appropriately. *)
val for_lifted_anonymous_constant
   : ?compilation_unit:Backend_compilation_unit.t
  -> unit
  -> t

(** A description of where the given symbol is defined. *)
val object_file : t -> Object_file.t

(** The kind of the symbol. *)
val kind : t -> kind

(** Symbols either defined in the runtime or defined in (shared) startup
    files with standard names. *)
module Names : sig
  (** External variables from the C library. *)
  val sqrt : t

  (** Global variables in the OCaml runtime accessed by OCaml code. *)
  val caml_exception_pointer : t
  val caml_backtrace_pos : t
  val caml_exn_Division_by_zero : t
  val caml_nativeint_ops : t
  val caml_int32_ops : t
  val caml_int64_ops : t
  val caml_globals_inited : t

  (** Entry points to the OCaml runtime from OCaml code. *)
  val caml_call_gc : t
  val caml_modify : t
  val caml_initialize : t
  val caml_get_public_method : t
  val caml_alloc : t
  val caml_ml_array_bound_error : t
  val caml_raise_exn : t
  val caml_make_array : t
  val caml_bswap16_direct : t

  type bswap_arg = Int32 | Int64 | Nativeint
  val caml_direct_bswap : bswap_arg -> t

  val caml_alloc_dummy : t
  val caml_alloc_dummy_float : t
  val caml_update_dummy : t

  (** Bigarrays. *)
  val caml_ba_get : int -> t
  val caml_ba_set : int -> t

  (** AFL instrumentation. *)
  val caml_afl_area_ptr : t
  val caml_afl_prev_loc : t
  val caml_setup_afl : t

  (** Entry points to the Spacetime runtime from OCaml code. *)
  val caml_spacetime_allocate_node : t
  val caml_spacetime_indirect_node_hole_ptr : t
  val caml_spacetime_generate_profinfo : t

  (** Main OCaml entry point related functions. *)
  val caml_program : t
  val caml_startup : t

  (** Header of a dynamically-loaded library. *)
  val caml_plugin_header : t

  (** Various veneers generated in [Cmmgen]. *)
  val caml_send : int -> t
  val caml_curry_n : int -> t
  val caml_curry_m_to_n : int -> int -> t
  val caml_curry_m_to_n_app : int -> int -> t
  val caml_tuplify : int -> t
  val caml_apply : int -> t

  (** Master table of globals. *)
  val caml_globals : t
  val caml_globals_map : t

  (** Master table of module data and code segments. *)
  val caml_code_segments : t
  val caml_data_segments : t

  (** Standard OCaml auxiliary data structures. *)
  val caml_frametable : t
  val caml_spacetime_shapes : t
end

(** Convert the given symbol to a textual representation intended for assembly
    emission. The caller must provide the target-specific escaping function and
    symbol prefix.  The [symbol_prefix] is not subject to escaping.  The
    [suffix], which is also not subject to escaping, is appended to the
    resulting string if provided. (The [suffix] may be used to specify
    relocation information, e.g. "@GOTPLT".)

    Typically, this function is used via [Asm_symbol], and not called
    directly.
*)
val to_escaped_string
   : ?suffix:string
  -> symbol_prefix:string
  -> escape:(string -> string)
  -> t
  -> string
