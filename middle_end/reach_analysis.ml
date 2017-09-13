[@@@ocaml.warning "+a-4-9-30-40-41-42"]

(* Analysis propagating the possibility for a value to reach a
   variable.

   We say that a variable x 'flow' to another variable y if there exists an
   execution where a value bound to x can later be bound to y.

   We define the partial order '<=' as the transitive closure of the
   'flow' relation. ('flow' is not necessarilly transitively closed,
   but is usualy quite close).

   For instance

   let f b x y =
   let v = if b then x else y in
   if b then
     let w = v in
     w
   else
     let z = v in
     z

   x and y flow to v,
   v flow to w and z
   x flow to w,
   y flow to z
   but x does not flow to z, yet z <= x

   This analysis computes an over-approximation of the '<=' relation.

   The main approximation point is about functions: ...
*)

module Int = Numbers.Int

type closure_descr = {
  closure_args : Variable.t list;
  closure_return : Variable.t list;
}

type descr =
  { mutable block : Variable.t Int.Map.t; (* Not empty: this can contain a block
                                             whose fields can come from those values *)
    (* variable option array ? *)
    (* metter un pointeur vers l'info directement pour ne pas avoir à aller le chercher aileurs ? *)
    mutable vars_within_closure : Variable.t Var_within_closure.Map.t;
    mutable closures : Variable.t Closure_id.Map.t;
    (* This is the value to which the projection is bound.
       If we want cross function analysis, we need to add the return continuation argument variable
       here to fetch it when applying. *)
    mutable const : Flambda.const option;
    mutable proj : Closure_id.t option;
    (* This can contain a closure projected using this closure_id from the original closure 'variable' *)
    mutable original_closure : Variable.t option;
    mutable closure_value : closure_descr option;
    created_as : Flambda.named option;
  }

  (* Pour rendre évident les cas constants:
  type redescr =
    | Block of { tag : int; fields : variable IntMap.t }
    | Other of descr

  let get_field descr i =
    match descr with
    | Block b -> IntMap.find i b.fields
    | Other descr -> IntMap.find i descr.block

  let add_field descr i var =
    match descr with
    | Block b -> failwith "add_field on a singleton block"
    | Other descr -> descr.block <- IntMap.add i var descr.block
  *)

  (* TODO: avoir des "représentants" pour les cas où des valeurs sont égales:
     si a <= b & b <= a alors
     c = repr (a, b)
     a = Link c
     b = Link c
  *)

type info = {
  var : Variable.t;
  descr : descr;
  (* Pour une analyse d'usage, il faudrait ajouter un "used" ici *)

  (* Pour être plus efficace, ça vaudrait sans doûte le coup de mettre un
     pointeur vers ces info directement *)
  mutable smaller_than : info Variable.Map.t; (* values greater than this one *)
  mutable greater_than : info Variable.Map.t; (* values smaller than this one *)
}

type env = {
  (* TODO: ne plus indexer les info avec des variables, mais un type somme:
     Var | Sym | Intermediate *)
  info : info Variable.Tbl.t;
  info_symbol : Variable.t Symbol.Tbl.t;
  cont : Variable.t list Continuation.Tbl.t;
  mut_var : info Mutable_variable.Tbl.t;
}

let find_info env var =
  try Variable.Tbl.find env.info var
  with _ ->
    Misc.fatal_errorf "Undefined variable %a" Variable.print var
let find_mut_info env var = Mutable_variable.Tbl.find env.mut_var var

let ext_comp_unit =
  let ln = Linkage_name.create "__dummy__" in
  Compilation_unit.create (Ident.create_persistent "__dummy__") ln
let external_world_source = Variable.create ~current_compilation_unit:ext_comp_unit "external_world_source"
let external_world_sink = Variable.create ~current_compilation_unit:ext_comp_unit "external_world_sink"

let fresh_variable name = Variable.create name

let fresh_info ?created_as var = {
  var;
  descr = {
    block = Int.Map.empty;
    vars_within_closure = Var_within_closure.Map.empty;
    closures = Closure_id.Map.empty;
    const = None;
    proj = None;
    original_closure = None;
    closure_value = None;
    created_as;
  };
  smaller_than = Variable.Map.empty;
  greater_than = Variable.Map.empty;
}

let init_fresh_info env ?created_as var =
  let info = fresh_info ?created_as var in
  Variable.Tbl.add env.info var info;
  info

let empty_env () =
  let tables = {
    info = Variable.Tbl.create 10;
    info_symbol = Symbol.Tbl.create 10;
    cont = Continuation.Tbl.create 10;
    mut_var = Mutable_variable.Tbl.create 3;
  } in
  Variable.Tbl.add tables.info external_world_source (fresh_info external_world_source);
  Variable.Tbl.add tables.info external_world_sink (fresh_info external_world_sink);
  tables

(* Be careful this reads in the other direction as one might expect:
   This is a comparison operator, not an arrow.

   a <== b means: The set of values reaching a is smaller than the set
   reaching b.

   for instance, `let b = a in` would produce such an inequality.
*)
let (<==) (v1, info1) (v2, info2) =
  (*Format.printf "cons %24s  <  %s@." v1 v2;*)
  let smaller_than = Variable.Map.add v2 info2 info1.smaller_than in
  let greater_than = Variable.Map.add v1 info1 info2.greater_than in
  if not (smaller_than == info1.smaller_than) then begin
    info1.smaller_than <- smaller_than;
    info2.greater_than <- greater_than
  end

let (<=|) info1 info2 =
  (info1.var, info1) <== (info2.var, info2)

let field env n arg ~assigned_to : info =
  let arg_info = Variable.Tbl.find env.info arg in
  let new_info = fresh_info assigned_to in
  (match Int.Map.find n arg_info.descr.block with
   | exception Not_found ->
     arg_info.descr.block <- Int.Map.add n assigned_to arg_info.descr.block
   | previous ->
     let previous_info = Variable.Tbl.find env.info previous in
     (*Format.printf "field(%i) %20s  <  %s@." n previous assigned_to;*)
     (previous, previous_info) <== (assigned_to, new_info));
  (* Si version direct: ajouter la propagation ici *)
  new_info

let block (_env:env) created_as args ~assigned_to : info =
  let new_info = fresh_info ?created_as assigned_to in
  let _, block =
    List.fold_left (fun (i, block) var -> i+1, Int.Map.add i var block)
      (0, Int.Map.empty) args
  in
  new_info.descr.block <- block;
  new_info

let jump env args k =
  let handle original_var jump_var =
    let info_original = Variable.Tbl.find env.info original_var in
    let info_jump = Variable.Tbl.find env.info jump_var in
    (jump_var, info_jump) <== (original_var, info_original)
  in
  let cont_args = Continuation.Tbl.find env.cont k in
  List.iter2 handle cont_args args

let const _env created_as i ~assigned_to =
  let new_info = fresh_info ~created_as assigned_to in
  new_info.descr.const <- Some i;
  new_info

let create_fresh_value env name =
  let var = fresh_variable name in
  let info = fresh_info var in
  Variable.Tbl.add env.info var info;
  (var, info)

let create_original_closure env closure_id var =
  let (original, info) = create_fresh_value env "original_closure" in
  (match closure_id with
   | None -> ()
   | Some closure_id ->
     info.descr.closures <- Closure_id.Map.singleton closure_id var);
  original, info

let get_original_closure env info =
  match info.descr.original_closure with
  | None ->
    let (original_closure_var, _) as original_closure =
      create_original_closure env info.descr.proj info.var
    in
    info.descr.original_closure <- Some original_closure_var;
    original_closure
  | Some original ->
    original, Variable.Tbl.find env.info original

let var_within_closure env var_within_closure ~arg ~assigned_to : info =
  let arg_info = Variable.Tbl.find env.info arg in
  let (_original_closure, original_closure_info) = get_original_closure env arg_info in
  let new_info = fresh_info assigned_to in
  (match Var_within_closure.Map.find var_within_closure original_closure_info.descr.vars_within_closure with
   | exception Not_found ->
     original_closure_info.descr.vars_within_closure <-
       Var_within_closure.Map.add var_within_closure assigned_to original_closure_info.descr.vars_within_closure
   | previous ->
     let previous_info = Variable.Tbl.find env.info previous in
     (previous, previous_info) <== (assigned_to, new_info));
  (* Si version direct: ajouter la propagation ici *)
  new_info


let proj env closure_id arg ~created_as ~assigned_to : info =
  let arg_info = Variable.Tbl.find env.info arg in
  let new_info = fresh_info ~created_as assigned_to in

  (* C'est sans doûte possible de ne pas recréer un nouveau quand la
     source de la projection a déjà un original_closure *)
  let (new_original_closure, new_original_info) = create_original_closure env (Some closure_id) assigned_to in
  new_info.descr.original_closure <- Some new_original_closure;
  new_info.descr.proj <- Some closure_id;
  (match Closure_id.Map.find closure_id arg_info.descr.closures with
   | exception Not_found ->
     arg_info.descr.closures <- Closure_id.Map.add closure_id assigned_to arg_info.descr.closures;
   | previous ->
     let previous_info = Variable.Tbl.find env.info previous in
     (previous, previous_info) <== (assigned_to, new_info));
  let arg_original_closure = get_original_closure env arg_info in
  arg_original_closure <== (new_original_closure, new_original_info);
  (* Si version direct: ajouter la propagation ici *)
  new_info

let leak env var info =
  let external_sink_info = Variable.Tbl.find env.info external_world_sink in
  (var, info) <== (external_world_sink, external_sink_info)

let from_external env var info =
  let external_info = Variable.Tbl.find env.info external_world_source in
  (external_world_source, external_info) <== (var, info)

let (-->) i j =
  let rec loop i j acc =
    if i > j then acc
    else loop i (j-1) (j :: acc)
  in
  loop i j []

let init_return env cont arity : Variable.t list =
  let results =
    List.map (fun i ->
      let result = Variable.create (Printf.sprintf "variable_from_cont_%i" i) in
      let result_info = fresh_info result in
      leak env result result_info;
      Variable.Tbl.add env.info result result_info;
      result)
      (1 --> arity)
  in
  Continuation.Tbl.add env.cont cont results;
  results

let closure env ~assigned_to functs (variables:Flambda.free_var Var_within_closure.Map.t) =
  let new_info = fresh_info assigned_to in
  new_info.descr.vars_within_closure <-
    Var_within_closure.Map.mapi (fun inner_var (free_var:Flambda.free_var) ->
      (* Quand les var_within_closure ne seront plus bindindés dans la
         fonction, ce sera simplement une variable fraiche quelconque *)
      let inner_var = Var_within_closure.unwrap inner_var in
      let inner_info = init_fresh_info env inner_var in
      let exter_info = find_info env free_var.var in
      exter_info <=| inner_info;
      free_var.var)
      variables;
  let functs =
    Closure_id.Map.mapi (fun closure_id (funct:Flambda.function_declaration) ->
      (* let var = funct.self in *)
      let var = Closure_id.unwrap closure_id in
      let info = init_fresh_info env var in
      info.descr.proj <- Some closure_id;
      let closure_return = init_return env funct.continuation_param funct.return_arity in
      info.descr.closure_value <- Some {
        closure_args = Parameter.List.vars funct.params;
        closure_return;
      };
      Variable.Tbl.add env.info var info;
      var
    ) functs
  in
  new_info.descr.closures <- functs;
  new_info.descr.original_closure <- Some assigned_to;
  new_info

let var env v ~assigned_to =
  let new_info = fresh_info assigned_to in
  let prev_info = Variable.Tbl.find env.info v in
  (v, prev_info) <== (assigned_to, new_info);
  new_info

let unit_info _env ~assigned_to =
  let created_as : Flambda.named = Const (Flambda.Const.Const_pointer 0) in
  let new_info = fresh_info ~created_as assigned_to in
  new_info

let symbol env v ~assigned_to =
  let prev_var =
    try Symbol.Tbl.find env.info_symbol v
    with _ ->
      Misc.fatal_errorf "Undefined symbol %a" Symbol.print v
  in
  var env prev_var ~assigned_to

let ext env args ~assigned_to =
  let new_info = fresh_info assigned_to in
  List.iter (fun arg ->
    let arg_info = Variable.Tbl.find env.info arg in
    leak env arg arg_info)
    args;
  leak env assigned_to new_info;
  from_external env assigned_to new_info;
  new_info

let apply env cont func args =
  let cont_arg =
    match Continuation.Tbl.find env.cont cont with
    | exception Not_found ->
      assert false
    | args -> args
  in

  (* TODO: on peut ne pas creer de nouvelle variable en regardant la tête de func.
     Mais ça fait un peu plus de cas *)
  let fresh_func_var = Variable.rename func in
  let fresh_func_info = fresh_info fresh_func_var in
  fresh_func_info.descr.closure_value <- Some {
    closure_return = cont_arg;
    closure_args = args;
  };
  Variable.Tbl.add env.info fresh_func_var fresh_func_info;
  let func_info = find_info env func in
  (func, func_info) <== (fresh_func_var, fresh_func_info)

let init_param env var =
  let info = fresh_info var in
  from_external env var info;
  Variable.Tbl.add env.info var info

let do_allocated_const _env ~(assigned_to:Variable.t) (constant:Allocated_const.t) : info =
  fresh_info ~created_as:(Allocated_const constant) assigned_to

let rec do_named env (assigned_to:Variable.t) (named:Flambda.named) : unit =
  let info =
    match named with
    | Var v ->
      var env v ~assigned_to
    | Const c ->
      const env named c ~assigned_to
    | Prim (Pmakeblock(_tag, Immutable, _), args, _dbg) ->
      block env (Some named) args ~assigned_to
    | Prim (Pfield i, [arg], _dbg) ->
      field env i arg ~assigned_to
    | Prim (_prim, args, _dbg) ->
      ext env args ~assigned_to
    | Assign { being_assigned; new_value } ->
      let being_assigned_info = find_mut_info env being_assigned in
      let new_value_info = find_info env new_value in
      new_value_info <=| being_assigned_info;
      unit_info env ~assigned_to
    | Read_mutable mut_var ->
      let read_info = find_mut_info env mut_var in
      var env read_info.var ~assigned_to
    | Symbol s ->
      symbol env s ~assigned_to
    | Read_symbol_field (symbol,i) ->
      let var = Symbol.Tbl.find env.info_symbol symbol in
      field env i var ~assigned_to
    | Allocated_const constant ->
      do_allocated_const env ~assigned_to constant
    | Set_of_closures set_of_closures ->
      do_set_of_closures env ~assigned_to set_of_closures
    | Project_closure { set_of_closures; closure_id } ->
      (* TODO (later): this won't be a set when the whole fix is done *)
      let closure_id =
        assert(Closure_id.Set.cardinal closure_id = 1);
        Closure_id.Set.min_elt closure_id
      in
      proj env closure_id set_of_closures ~created_as:named ~assigned_to
    | Move_within_set_of_closures { closure; move } ->
      (* TODO (later): this won't be a map when the whole fix is done *)
      let (_, closure_id) =
        assert(Closure_id.Map.cardinal move = 1);
        Closure_id.Map.min_binding move
      in
      proj env closure_id closure ~created_as:named ~assigned_to
    | Project_var { closure; var } ->
      (* TODO (later): this won't be a map when the whole fix is done *)
      let (_, var) =
        assert(Closure_id.Map.cardinal var = 1);
        Closure_id.Map.min_binding var
      in
      var_within_closure env var ~arg:closure ~assigned_to
  in
  Variable.Tbl.replace env.info assigned_to info

and do_set_of_closures env ~assigned_to (set_of_closures:Flambda.set_of_closures) =
  let functs = (Closure_id.wrap_map (set_of_closures.function_decls.funs)) in
  let info =
    closure env ~assigned_to
      functs
      (Var_within_closure.wrap_map set_of_closures.free_vars)
  in
  Variable.Tbl.add env.info assigned_to info;
  Closure_id.Map.iter (fun _ (funct:Flambda.function_declaration) ->
    List.iter (fun param -> init_param env (Parameter.var param)) funct.params;
    do_expr env funct.body) functs;
  info

and do_expr env (expr:Flambda.expr) : unit =
  match expr with
  | Let { var; defining_expr; body } ->
    do_named env var defining_expr;
    do_expr env body
  | Let_cont { body; handlers = Alias { name; alias_of } } ->
    let cont = Continuation.Tbl.find env.cont alias_of in
    Continuation.Tbl.add env.cont name cont;
    do_expr env body
  | Let_cont { body; handlers = Nonrecursive { name; handler } } ->
    declare_continuation env name handler;
    do_continuation env name handler;
    do_expr env body
  | Let_cont { body; handlers = Recursive handlers } ->
    Continuation.Map.iter (declare_continuation env) handlers;
    Continuation.Map.iter (do_continuation env) handlers;
    do_expr env body
  | Apply_cont (cont, _trap_action, args) ->
    jump env args cont
  | Let_mutable { var; initial_value; body } ->
    let assigned_to = fresh_variable "mutable_value" in
    let info = fresh_info assigned_to in
    Variable.Tbl.add env.info assigned_to info;
    Mutable_variable.Tbl.add env.mut_var var info;
    let initial_value_info = Variable.Tbl.find env.info initial_value in
    initial_value_info <=| info;
    do_expr env body
  | Apply { continuation; func; args } ->
    apply env continuation func args
  | Switch (_cond, {consts; failaction}) ->
    (* Switch branches have arity 0, if that ever changes,
       it needs to be propagated *)
    List.iter (fun (_, continutation) ->
      assert(Continuation.Tbl.find env.cont continutation = []))
      consts;
    Misc.may (fun continutation ->
      assert(Continuation.Tbl.find env.cont continutation = []))
      failaction
  | Proved_unreachable ->
    ()

and declare_continuation env name (handler:Flambda.continuation_handler) : unit =
  let params = Parameter.List.vars handler.params in
  Continuation.Tbl.add env.cont name params;
  let declare_var var =
    Variable.Tbl.add env.info var (fresh_info var)
  in
  List.iter declare_var params

and do_continuation env _name (handler:Flambda.continuation_handler) : unit =
  do_expr env handler.handler

and do_constant_to_variable env ~(assigned_to:Variable.t) (constant:Flambda.constant_defining_value) : info =
  match constant with
  | Allocated_const constant ->
    do_allocated_const env ~assigned_to constant
  | Block (_tag, fields) ->
    let fields =
      List.map (fun (field:Flambda.constant_defining_value_block_field) ->
        match field with
        | Symbol s ->
          Symbol.Tbl.find env.info_symbol s
        | Const c ->
          let assigned_to = fresh_variable "constant" in
          (* TODO: give real named definition *)
          let info = const env (Var assigned_to) c ~assigned_to in
          Variable.Tbl.add env.info assigned_to info;
          assigned_to)
        fields
    in
    block env None fields ~assigned_to
  | Set_of_closures set_of_closures ->
    do_set_of_closures env ~assigned_to set_of_closures
  | Project_closure (set_of_closures_sym, closure_id) ->
    let set_of_closures =
      (Symbol.Tbl.find env.info_symbol set_of_closures_sym)
    in
    let named : Flambda.named =
      Project_closure
        { set_of_closures;
          closure_id = Closure_id.Set.singleton closure_id
        }
    in
    proj env closure_id set_of_closures ~created_as:named ~assigned_to

and do_constant env ~(assigned_to_symbol:Symbol.t) (constant:Flambda.constant_defining_value) : unit =
  let assigned_to = fresh_variable "symbol" in
  let info = do_constant_to_variable env ~assigned_to constant in
  Symbol.Tbl.add env.info_symbol assigned_to_symbol assigned_to;
  Variable.Tbl.add env.info assigned_to info

and do_program env (prog:Flambda.program_body) : unit =
  match prog with
  | Let_symbol (s,const,body) ->
    do_constant env ~assigned_to_symbol:s const;
    do_program env body
  | Let_rec_symbol (defs,body) ->
    let declared_defs =
      List.map (fun (symbol, def) ->
        let assigned_to = fresh_variable "symbol" in
        let info = init_fresh_info env assigned_to in
        Symbol.Tbl.add env.info_symbol symbol assigned_to;
        def, info)
        defs
    in
    List.iter (fun (def, symbol_info) ->
      let assigned_to = fresh_variable "intermediate" in
      let value_info = do_constant_to_variable env ~assigned_to def in
      value_info <=| symbol_info
    ) declared_defs;
    do_program env body
  | Effect (expr,cont,body) ->
    (* Effect continuation arity should really be 0 *)
    let _var : Variable.t list = init_return env cont 1 in
    do_expr env expr;
    do_program env body
  | Initialize_symbol ( s, _tag, fields, body) ->

    let do_field (expr, cont) =
      let ret_var = init_return env cont 1 in
      do_expr env expr;
      ret_var
    in
    (* TODO factoriser *)
    let fields = List.flatten (List.map do_field fields) in
    let assigned_to = fresh_variable "symbol" in
    Symbol.Tbl.add env.info_symbol s assigned_to;

    (* TODO: donner une définition de la structure du bloc, pour
       l'analyse de constantes *)
    let info = block env None fields ~assigned_to in
    Variable.Tbl.replace env.info assigned_to info;

    do_program env body

  | End s ->
    let var = Symbol.Tbl.find env.info_symbol s in
    let info = Variable.Tbl.find env.info var in
    leak env var info

  (* Gestion des blocs uniquement pour l'instant *)
  let propagate env =
    (* TODO: propagation avec l'exterieur
       Si une valeur s'échape, tout ce qui est accessible depuis elle s'échape aussi *)
    let work_queue = Queue.create () in
    Variable.Tbl.iter (fun _small small_info ->
        Variable.Map.iter (fun _large large_info -> Queue.push (small_info, large_info) work_queue)
          small_info.smaller_than)
      env.info;

    let external_sink_info = Variable.Tbl.find env.info external_world_sink in
    let external_source_info = Variable.Tbl.find env.info external_world_source in

    let count = ref 0 in
    let add _s (info_small, info_large) =
      incr count;
      (*Format.printf "ad %4s %21s  <  %s@." _s small large;*)
      (*if not (Variable.Tbl.mem env.info small) then failwith small;*)
      let small = info_small.var in
      let large = info_large.var in
      (*let info_small = Variable.Tbl.find env.info small in
      let info_large = Variable.Tbl.find env.info large in*)
      if not (Variable.Map.mem small info_large.greater_than) then begin
        info_small.smaller_than <- Variable.Map.add large info_large info_small.smaller_than;
        info_large.greater_than <- Variable.Map.add small info_small info_large.greater_than;
        Queue.push (info_small, info_large) work_queue
      end
    in
    let add_var s (small, large) =
      let info_small = find_info env small in
      let info_large = find_info env large in
      add s (info_small, info_large)
    in
    while not (Queue.is_empty work_queue) do
      let (info_small, info_large) = Queue.pop work_queue in
      (* check that if this propagates *)

      let small = info_small.var in
      let large = info_large.var in
      (*let info_small = Variable.Tbl.find env.info small in
      let info_large = Variable.Tbl.find env.info large in*)

      if Variable.equal external_world_sink large then begin
        (*Format.printf "leak %24s  <  external_world_sink@." small;*)
        Int.Map.iter (fun _i field_small ->
            let info_field_small = Variable.Tbl.find env.info field_small in
            add "" (info_field_small, external_sink_info))
          info_small.descr.block;

        (* This is the important difference between closures and
           blocks. Blocks are usable from 'the external world'. It
           means that any block value leaking the current module or
           that can't be tracked can be used in any way. This is not
           the case of closures. The only way a closure can be used
           from 'the external world' is through a function call.

           This comes from the fact that the 'surface' language that
           we expect is not flambda, but lambda. In lambda, closures
           are only good for being called. They cannot be inspected,
           they contains a single closure, free variables are not
           reachable by any other mean that the function call.
        *)
        begin match info_small.descr.closure_value with
        | None -> ()
        | Some { closure_args; closure_return } ->
          List.iter (fun return ->
            let info_return = Variable.Tbl.find env.info return in
            add "leaking return value" (info_return, external_sink_info))
            closure_return;
          List.iter (fun arg ->
              let info_arg = Variable.Tbl.find env.info arg in
              add "argument from extern world" (external_source_info, info_arg))
            closure_args
        end
      end
      else if Variable.equal external_world_source small then begin
        (*Format.printf "snip %24s  >  external_world_source@." large;*)
        Int.Map.iter (fun _i field_large ->
            let info_field_large = Variable.Tbl.find env.info field_large in
            add "" (external_source_info, info_field_large))
          info_large.descr.block;

        begin match info_small.descr.closure_value with
        | None -> ()
        | Some { closure_args; closure_return } ->
          List.iter (fun arg ->
            let info_arg = Variable.Tbl.find env.info arg in
            add "leaking arguments" (info_arg, external_sink_info))
            closure_args;
          List.iter (fun return ->
              let info_return = Variable.Tbl.find env.info return in
              add "return value from extern world" (external_source_info, info_return))
            closure_return
        end

      end
      else
        begin
          Int.Map.iter
            (fun i field_small ->
               match Int.Map.find i info_large.descr.block with
               | exception Not_found ->
                 (* Réfléchir: Si small a un champ i, alors large en a forcement un
                     Par contre, ce n'est pas forcement indispensable (?) de le représenter.
                     Doit on générer une variable fraiche pour lui... ?
                     Je préfèrerais pouvoir éviter. Sinon la garantie de quadratique
                     est perdue *)
                 ()
               | field_large ->
                 add_var "" (field_small, field_large))
            info_small.descr.block
        end;

      (match info_small.descr.original_closure, info_large.descr.original_closure with
       | Some original_small, Some original_large ->
         add_var "" (original_small, original_large)
       | _, _ -> ());

      Closure_id.Map.iter
        (fun closure_id field_small ->
           match Closure_id.Map.find closure_id info_large.descr.closures with
           | exception Not_found -> ()
           | field_large -> add_var "" (field_small, field_large))
        info_small.descr.closures;

      Var_within_closure.Map.iter
        (fun var_within_closure field_small ->
           match Var_within_closure.Map.find var_within_closure info_large.descr.vars_within_closure with
           | exception Not_found -> ()
           | field_large -> add_var "" (field_small, field_large))
        info_small.descr.vars_within_closure;

      (match info_small.descr.closure_value, info_large.descr.closure_value with
       | Some closure_small, Some closure_large ->

         if List.length closure_small.closure_args = List.length closure_large.closure_args then begin
           if List.length closure_small.closure_return = List.length closure_large.closure_return then
             begin
               List.iter2 (fun small large -> add_var "return" (small, large))
                 closure_small.closure_return closure_large.closure_return;
             end
           else begin
             (* If the sizes doesn't match, leak. It would probably be safe to just ignore.
                The front language being type-safe, this kind of situations in fact represents
                unreachable values *)
             List.iter (fun small_return -> add_var "return_leak" (small_return, external_world_sink))
               closure_small.closure_return;
             List.iter (fun large_return -> add_var "return_any" (external_world_source, large_return))
               closure_large.closure_return;
           end;

           let fast = true in
           if fast then begin
             (* The applied values leak *)
             List.iter (fun large ->
               add_var "arg_leak" (large, external_world_sink))
               closure_large.closure_args;
             (* The function arguments can be anything *)
             List.iter (fun small ->
               add_var "arg_any" (external_world_source, small))
               closure_small.closure_args;
           end else begin
             List.iter2 (fun small large ->
               (* arguments flow in the other direction *)
               add_var "arg" (large, small);
             ) closure_small.closure_args closure_large.closure_args
           end
         end
         else begin
          (* TODO faire plus précis. Là ça leak tout *)
          (* Anything can be returned by the function *)
           List.iter (fun large_return -> add_var "return_any" (external_world_source, large_return))
             closure_large.closure_return;
           (* The function return value can go anywhere *)
           List.iter (fun small_return -> add_var "return_leak" (small_return, external_world_sink))
             closure_small.closure_return;
           (* The applied values leak *)
          List.iter (fun large ->
            add_var "arg_leak" (large, external_world_sink))
            closure_large.closure_args;
          (* The function arguments can be anything *)
          List.iter (fun small ->
            add_var "arg_any" (external_world_source, small))
            closure_small.closure_args;
         end
       | _, _ -> ());

      (* C'est pas terrible, il y a sans doûte moyen de faire ça implicitement *)
      Variable.Map.iter (fun _even_larger info_even_larger -> add "lt" (info_small, info_even_larger)) info_large.smaller_than;
      Variable.Map.iter (fun _even_smaller info_even_smaller -> add "gt" (info_even_smaller, info_large)) info_small.greater_than
    done;
    Format.printf "add count: %i@." !count

let define_imported_symbols env (program:Flambda.program) =
  Symbol.Set.iter (fun imported_symbol ->
    let assigned_to =
      fresh_variable
        (Format.asprintf "imported_symbol_%a" Symbol.print imported_symbol)
    in
    Symbol.Tbl.add env.info_symbol imported_symbol assigned_to;

    (* TODO: donner une définition de la structure de la valeur, pour
       l'analyse de constantes. Sinon, c'est aussi possible de faire
       ça à la propagation, pour éviter de charger des choses
       inutiles. *)
    let info = fresh_info assigned_to in
    Variable.Tbl.replace env.info assigned_to info;
  ) program.imported_symbols


type result = unit

let show env =
  let builded _ info = info.descr.created_as <> None in
  let show (env:env) =
    Format.printf "@[<2>%a@]@."
      (Variable.Map.print
         (fun ppf info ->
            Variable.Set.print ppf
              (Variable.Map.keys
                 (Variable.Map.filter builded info.greater_than))))
      (Variable.Tbl.to_map env.info);
  in
  let () = Format.printf "computation done@.@." in
  show env

let run (prog:Flambda.program) : result =
  let env = empty_env () in
  Profile.record ~accumulate:true "traverse" (fun () ->
    define_imported_symbols env prog;
    do_program env prog.program_body) ();
  Profile.record ~accumulate:true "propagate" propagate env;
  (* show env; *)
  let _ = show in
  ()
