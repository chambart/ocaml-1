let unsafe_mode = ref false

exception Not_a_closure

let flambda_repr (obj:Obj.t) : Flambda.set_of_closures =
  if Obj.is_int obj then
    raise Not_a_closure;
  let tag = Obj.tag obj in
  if tag <> Obj.closure_tag then
    raise Not_a_closure;
  let size = Obj.size obj in
  if size < 2 then
    raise Not_a_closure;
  let id = Obj.obj (Obj.field obj (size - 2)) in
  let marshalled = Obj.field obj (size - 1) in
  if not (Obj.is_int id && Obj.is_block marshalled && Obj.tag marshalled = Obj.string_tag) then
    raise Not_a_closure;
  let id : int = Obj.obj id in
  let marshalled : string = Obj.obj marshalled in
  let array = Marshal.from_string marshalled 0 in
  array.(id)

let phrase_count = ref 0
let symbol_count = ref 0

let fresh_symbol () =
  incr symbol_count;
  let n = !symbol_count in
  let c = Compilation_unit.get_current_exn () in
  let l = Linkage_name.create ("closure_root_"^string_of_int n) in
  Symbol.create c l


external ndl_loadsym: string -> Obj.t = "caml_natdynlink_loadsym"
let need_symbol sym =
  try ignore (ndl_loadsym sym); false
  with _ -> true

type res = Ok of Obj.t | Err of string
type evaluation_outcome = Result of Obj.t | Exception of exn

external ndl_run_toplevel: string -> string -> res
  = "caml_natdynlink_run_toplevel"

let dll_run dll entry =
  match (try Result (Obj.magic (ndl_run_toplevel dll entry))
         with exn -> Exception exn)
  with
    | Exception _ as r -> r
    | Result r ->
        match Obj.magic r with
          | Ok x -> Result x
          | Err s -> failwith ("dll_run " ^ s)

module Backend = struct
  (* See backend_intf.mli. *)

  let symbol_for_global' = Compilenv.symbol_for_global'
  let closure_symbol = Compilenv.closure_symbol

  let really_import_approx = Import_approx.really_import_approx
  let import_symbol = Import_approx.import_symbol

  let size_int = Arch.size_int
  let big_endian = Arch.big_endian

  let max_sensible_number_of_arguments =
    (* The "-1" is to allow for a potential closure environment parameter. *)
    Proc.max_arguments_for_tailcalls - 1
end
let backend = (module Backend : Backend_intf.S)

let load_code ppf ?(keep_asm_file=false) ~phrase_name ~required_globals flambda =
  assert(Config.flambda);
  let dll =
    if keep_asm_file then phrase_name ^ Config.ext_dll
    else Filename.temp_file ("caml" ^ phrase_name) Config.ext_dll
  in
  let fn = Filename.chop_extension dll in
  Asmgen.compile_implementation_flambda
    ~required_globals ~backend ~toplevel:need_symbol fn ppf
    flambda;
  Asmlink.call_linker_shared [fn ^ Config.ext_obj] dll;
  Sys.remove (fn ^ Config.ext_obj);

  let dll =
    if Filename.is_implicit dll
    then Filename.concat (Sys.getcwd ()) dll
    else dll in
  let res = dll_run dll phrase_name in
  (try Sys.remove dll with Sys_error _ -> ());
  res

let init_env () =
  incr phrase_count;
  let count = !phrase_count in
  let phrase_name = Printf.sprintf "Magic%i" count in
  Compilenv.reset ?packname:None phrase_name;
  phrase_name

let closure_field ~(closure_value : Obj.t) (field : Var_within_closure.t) : Obj.t =
  ignore (Compilenv.approx_for_global (Var_within_closure.get_compilation_unit field):Export_info.t);
  let imported = Compilenv.approx_env () in
  let table = imported.offset_fv in
  let field_pos = Var_within_closure.Map.find field table in
  let size = Obj.size closure_value in
  assert(size > field_pos);

  (* Heu c'est bien faux ça: c'est l'offset dans le set pas dans la cloture...
     Mais peut on vraiment savoir quelle fonction de la cloture c'est ???
     En comparant l'offset avec toutes les closure_id du set ! *)
  Obj.field closure_value field_pos

let closure_fields ~closure_value fields =
  Var_within_closure.wrap_map
    (Variable.Map.mapi (fun closure_var ({ var } : Flambda.specialised_to) ->
         closure_field ~closure_value (Var_within_closure.wrap closure_var))
        fields)

let print_value_set_of_closures ppf
    ({ function_decls = { funs }; invariant_params; freshening; bound_vars; _ } : Simple_value_approx.value_set_of_closures) =
  Format.fprintf ppf "(set_of_closures:@ %a invariant_params=%a freshening=%a bound=%a)"
    (fun ppf -> Variable.Map.iter (fun id _ -> Variable.print ppf id)) funs
    (Variable.Map.print Variable.Set.print) (Lazy.force invariant_params)
    Freshening.Project_var.print freshening
    (Var_within_closure.Map.print Simple_value_approx.print) bound_vars

let rec make_dyn_approx (v:Obj.t) : Simple_value_approx.t =
  if Obj.is_int v then
    let n : int = Obj.obj v in
    Simple_value_approx.value_int n
  else
    let tag = Obj.tag v in
    let size = Obj.size v in
    if tag < Obj.lazy_tag then
      (* Block *)
      if !unsafe_mode then
        Simple_value_approx.value_block (Tag.create_exn tag)
          (Array.init size (fun i -> make_dyn_approx (Obj.field v i)))
      else
        Simple_value_approx.value_unknown Other
    else
    if tag = Obj.double_tag then
      Simple_value_approx.value_float (Obj.magic v : float)
    else if tag = Obj.closure_tag then
      let () = Format.printf "Yooo une closure@." in
      let set = flambda_repr v in
      let fields_value = closure_fields ~closure_value:v set.free_vars in
      let bound_vars = Var_within_closure.Map.map make_dyn_approx fields_value in
      Format.printf "@.@.FREE VARS: %i@." (Var_within_closure.Map.cardinal bound_vars);
      let set_approx =
        Simple_value_approx.create_value_set_of_closures
          ~function_decls:set.function_decls
          ~bound_vars
          ~invariant_params:(lazy Variable.Map.empty) (* TODO ? *)
          ~specialised_args:set.specialised_args
          ~freshening:Freshening.Project_var.empty
          ~direct_call_surrogates:Closure_id.Map.empty (* TODO *)
          (* set.direct_call_surrogates *)
      in
      let closure_id =
        match Variable.Map.bindings set.function_decls.funs with
        | [closure_var, _] -> Closure_id.wrap closure_var
        | _ ->
          failwith "TODO muti closure id"
      in
      Format.printf "Closure_id: %a@.%a@.@."
        Closure_id.print closure_id
        print_value_set_of_closures set_approx;
      let closure_approx =
        Simple_value_approx.value_closure set_approx closure_id
      in
      closure_approx
      (* Simple_value_approx.value_unknown Other *)
    else
      Simple_value_approx.value_unknown Other


let build_closure (set_of_closures:Flambda.set_of_closures) ~(closure_value : Obj.t) =

  let orig_fun_var =
    let b = Variable.Map.bindings set_of_closures.function_decls.funs in
    match b with
    | [fun_var, _] -> fun_var
    | _ -> failwith "not singleton closure"
  in
  let orig_closure_id = Closure_id.wrap orig_fun_var in
  let fun_var = Variable.rename orig_fun_var in

  let init_env =
    Inline_and_simplify_aux.Env.create
              ~never_inline:false
              ~backend:backend
              ~round:0
  in
  let env =
    Variable.Map.fold (fun closure_var ({ var } : Flambda.specialised_to) env ->
        let closure_value =
          closure_field ~closure_value (Var_within_closure.wrap closure_var)
        in
        let approx = make_dyn_approx closure_value in
        Format.printf "Import env %a %a@."
          Variable.print var
          Simple_value_approx.print approx;
        Inline_and_simplify_aux.Env.add env var approx)
      set_of_closures.free_vars
      init_env
  in
  (* let env = Inline_and_simplify_aux.Env.activate_freshening env in *)

  Format.printf "@.Set @.%a@." Flambda.print_set_of_closures set_of_closures;

  let copied_function_decl, specialised_args =
    Inline_and_simplify.duplicate_function'
      ~env
      ~never_inline:false
      ~set_of_closures
      ~fun_var:orig_fun_var
  in

  let copied_fun_decls =
    Flambda.create_function_declarations
      ~funs:(Variable.Map.singleton fun_var copied_function_decl)
  in
  Format.printf "@.Copied fun_decls @.%a@." Flambda.print_function_declarations copied_fun_decls;

  (* let free_vars = Variable.Map.map_keys Variable.rename set_of_closures.free_vars in *)
  let free_vars = set_of_closures.free_vars in
  let copied_set =
    Flambda.create_set_of_closures
      ~function_decls:copied_fun_decls
      ~free_vars
      ~specialised_args:specialised_args
      ~direct_call_surrogates:Variable.Map.empty
  in
  let closure_id = Closure_id.wrap fun_var in
  let var_set = Variable.create "set_of_closures" in

  let body =
    Flambda.create_let var_set
      (Set_of_closures copied_set)
      (Flambda_utils.name_expr ~name:"closure"
         (Project_closure { set_of_closures = var_set;
                            closure_id }))
  in

  (* let env = Inline_and_simplify_aux.Env.set_never_inline env in *)
  let body, _r =
    Inline_and_simplify.simplify env (Inline_and_simplify_aux.Result.create ()) body
  in

  let set_param_var = Variable.create "input_closure" in
  let set_param = Parameter.wrap set_param_var in

  (* Inlining_stats.record_decision
   *   (Prevented Function_prevented_from_inlining)
   *   (Inlining_stats.Closure_stack.(note_entering_call ~closure_id:orig_closure_id ~dbg:Debuginfo.none (create ()))); *)
  Inlining_stats.save_then_forget_decisions ~output_prefix:"./report";

  let body =
    Variable.Map.fold (fun closure_var ({ var } : Flambda.specialised_to) body ->
        Flambda.create_let var
          (Flambda.Project_var
             { closure = set_param_var;
               closure_id = orig_closure_id;
               var = Var_within_closure.wrap closure_var })
          body)
      free_vars
      body
  in

  let fun_decl =
    Flambda.create_function_declaration
      ~params:[set_param]
      ~body:body
      ~stub:false
      ~dbg:Debuginfo.none
      ~inline:Lambda.Default_inline
      ~specialise:Lambda.Default_specialise
      ~is_a_functor:false
  in
  let new_fun_var = Variable.rename fun_var in
  let fun_decls =
    Flambda.create_function_declarations
      ~funs:(Variable.Map.singleton new_fun_var fun_decl)
  in
  let set =
    Flambda.create_set_of_closures
      ~function_decls:fun_decls
      ~free_vars:Variable.Map.empty
      ~specialised_args:Variable.Map.empty
      ~direct_call_surrogates:Variable.Map.empty
  in
  (* Ugly copy to rename stuff *)
  let fun_decl, _spec_arg =
    Inline_and_simplify.duplicate_function
      ~env:(Inline_and_simplify_aux.Env.activate_freshening init_env)
      ~set_of_closures:set
      ~fun_var:new_fun_var
  in
  let fun_decls =
    Flambda.create_function_declarations
      ~funs:(Variable.Map.singleton new_fun_var fun_decl)
  in
  let set =
    Flambda.create_set_of_closures
      ~function_decls:fun_decls
      ~free_vars:Variable.Map.empty
      ~specialised_args:Variable.Map.empty
      ~direct_call_surrogates:Variable.Map.empty
  in
  set, Closure_id.wrap new_fun_var

let expr (f : Flambda.set_of_closures) ~(closure_value:Obj.t) : Flambda.program_body =
  let symbol_set = fresh_symbol () in
  let re_set, closure_id = build_closure f ~closure_value in
  let symbol_closure = Compilenv.closure_symbol closure_id in
  Let_symbol
    (symbol_set, Set_of_closures re_set,
     Let_symbol
       (symbol_closure, Project_closure (symbol_set, closure_id),
        End symbol_closure))
  (* Let_symbol (symbol_set, Set_of_closures re_set, End symbol_set) *)


let import_globals symbols =
  let compilation_units =
    Symbol.Set.fold (fun symbol set ->
        let cu = Symbol.compilation_unit symbol in
        Compilation_unit.Set.add cu set)
      symbols
      Compilation_unit.Set.empty
  in
  Compilation_unit.Set.iter
    (fun cu -> ignore (Compilenv.approx_for_global cu:Export_info.t))
    compilation_units

let load_symbol sym =
  let lbl = Linkage_name.to_string (Symbol.label sym) in
  ndl_loadsym lbl

let build f ~closure_value =
  let ppf = Format.std_formatter in
  let phrase_name = init_env () in
  let fexpr = expr f ~closure_value in
  let flam : Flambda.program = {
    program_body = fexpr;
    imported_symbols = Symbol.Set.empty;
  } in
  let flam = Flambda_utils.introduce_needed_import_symbols flam in
  (* if !Clflags.dump_flambda then
   *   Format.fprintf ppf "@.Before inline and simplify@.%a@." Flambda.print_program flam; *)
  (* let flam =
   *   Inline_and_simplify.run ~never_inline:false ~backend
   *     ~prefixname:"Maaaaaagic" ~round:0 flam
   * in *)
  let flam = Lift_constants.lift_constants flam backend in
  let symb = Flambda_utils.root_symbol flam in
  import_globals flam.imported_symbols;
  if !Clflags.dump_flambda then
    Format.fprintf ppf "@.After inline and simplify@.%a@." Flambda.print_program flam;
  match load_code ~keep_asm_file:true ppf ~phrase_name ~required_globals:Ident.Set.empty flam with
  | Exception exn ->
    raise exn
  | Result obj ->
    assert(Obj.is_int obj);
    assert(Obj.repr 0 = obj);
    load_symbol symb

let this_is_the_right_time (f:'a -> 'b) : 'a -> 'b =
  let closure_value = Obj.repr f in
  let descr = flambda_repr closure_value in
  let built = build descr ~closure_value in
  let caster : ('a -> 'b) -> ('a -> 'b) = Obj.obj built in
  caster f

let () =
  Clflags.include_dirs := Config.standard_library :: !Clflags.include_dirs;
  Config.load_path := "." :: Config.standard_library :: !Config.load_path
let () =
  Clflags.use_inlining_arguments_set
    { Clflags.o3_arguments with inline_max_unroll = Some 3 }
