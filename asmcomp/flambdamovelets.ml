open Lambda
open Abstract_identifiers
open Flambda

(* pure: can be moved without changing the semantics *)

let pure_primitive = function
  | Pidentity
  | Pignore
  | Pgetglobal _
  (* | Pgetglobalfield _ *) (* the order of getglobalfields are quite fixed *)
  | Pmakeblock (_, Asttypes.Immutable) (* moving mutables could change sharing *)
  | Psequand
  | Psequor
  | Pnot
  | Pnegint
  | Paddint
  | Psubint
  | Pmulint
  (* | Pdivint *) (* divide by zero *)
  | Pmodint
  | Pandint
  | Porint
  | Pxorint
  | Plslint
  | Plsrint
  | Pasrint
  | Pintcomp _
  | Poffsetint _
  | Pintoffloat
  | Pfloatofint
  | Pnegfloat
  | Pabsfloat
  | Paddfloat
  | Psubfloat
  | Pmulfloat
  | Pdivfloat
  | Pfloatcomp _
  | Pstringlength
  (* | Pmakearray _ *) (* sharing *)
  | Parraylength _
  | Pisint
  | Pisout
  | Pbittest
  | Pbintofint _
  | Pintofbint _
  | Pcvtbint _
  | Pnegbint _
  | Paddbint _
  | Psubbint _
  | Pmulbint _
  (* | Pdivbint _ *) (* divide by zero *)
  | Pmodbint _
  | Pandbint _
  | Porbint _
  | Pxorbint _
  | Plslbint _
  | Plsrbint _
  | Pasrbint _
  | Pbintcomp _
  | Pbigarraydim _
  | Pctconst _
  | Pbswap16
  | Pbbswap _ -> true
  | _ -> false

type pure_env =
  { pure_functions : ClosureFunctionSet.t;
    pure_variables : VarSet.t;
    bound_variables : VarSet.t;
    local_static_exn : StaticExceptionSet.t;
    exception_caugh : bool }

let empty_env =
  { pure_functions = ClosureFunctionSet.empty;
    pure_variables = VarSet.empty;
    bound_variables = VarSet.empty;
    local_static_exn = StaticExceptionSet.empty;
    exception_caugh = false }

type pure =
  | Pure_if of ClosureFunctionSet.t
  | Impure

let is_pure env expr =
  let dep = ref ClosureFunctionSet.empty in
  let add_dep cf = dep := ClosureFunctionSet.add cf !dep in
  let rec pure env expr = match expr with
    | Fvar (v,_) ->
        VarSet.mem v env.bound_variables ||
        VarSet.mem v env.pure_variables
    | Fsymbol _
    | Fconst _ -> true

    | Flet (_,v,def,body,_) ->
        pure env def &&
        pure { env with bound_variables = VarSet.add v env.bound_variables } body

    | Fletrec (defs,body,_) ->
        let bound_variables =
          List.fold_left
            (fun set (v,_) -> VarSet.add v set)
            env.bound_variables
            defs
        in
        let env = { env with bound_variables } in
        pure env body &&
        List.for_all (fun (_,def) -> pure env def) defs

    | Fprim(Pfield _, args, _, _) ->
        (* TODO: special case *)
        false

    | Fprim(Praise, args, _, _) ->
        env.exception_caugh &&
        List.for_all (pure env) args

    | Fprim(p, args, _, _) ->
        pure_primitive p &&
        List.for_all (pure env) args

    | Fclosure ({ cl_free_var }, _) ->
        VarMap.for_all (fun id def -> pure env def) cl_free_var

    | Ffunction _
    | Fvariable_in_closure _
    | Fifthenelse _
    | Fswitch _
    | Fsequence _
    | Fwhile _
    | Ffor _ ->
        let aux (bound,expr) =
          let env = { env with pure_variables = VarSet.union bound env.pure_variables } in
          pure env expr
        in
        List.for_all aux (Flambdaiter.subexpression_bound_variables expr)

    | Fstaticcatch (exn,vars,body,handler,_) ->
        (let pure_variables = VarSet.union (env.pure_variables) (VarSet.of_list vars) in
         let env = { env with pure_variables } in
         pure env handler) &&
        let env =
          { env with
            local_static_exn =
              StaticExceptionSet.add exn env.local_static_exn } in
        pure env body

    | Ftrywith (body, var, handler, _) ->
        (let env = { env with pure_variables = VarSet.add var env.pure_variables } in
         pure env handler) &&
        let env = { env with exception_caugh = true } in
        pure env body

    | Fassign (var,flam,_) ->
        VarSet.mem var env.bound_variables &&
        pure env flam

    | Fstaticraise (exn,args, _) ->
        StaticExceptionSet.mem exn env.local_static_exn &&
        List.for_all (pure env) args

    | Fapply({ ap_kind = Indirect },_) ->
        false

    | Fapply({ ap_function; ap_arg; ap_kind = Direct direct },_) ->

        let res =
          pure env ap_function &&
          List.for_all (pure env) ap_arg in
        if res && not (ClosureFunctionSet.mem direct env.pure_functions)
        then add_dep direct;
        res

    | Fsend _ ->
        false

    | Funreachable _ -> true

    | Fevent _ -> assert false
  in
  let r = pure env expr in
  if r
  then Pure_if !dep
  else Impure

let pure_expression env expr =
  match is_pure env expr with
  | Pure_if s -> ClosureFunctionSet.is_empty s
  | Impure -> false

let pure_function fun_decl =
  let env = { empty_env with bound_variables = fun_decl.free_variables } in
  is_pure env fun_decl.body

module CFS = ClosureFunctionSet
module CFM = ClosureFunctionMap

let collect_function_dep expr : pure CFM.t =
  let map = ref CFM.empty in
  let aux = function
    | Fclosure(closure, _) ->
        VarMap.iter
          (fun var fun_decl ->
             map :=
               CFM.add
                 (Closure_function.wrap var)
                 (pure_function fun_decl)
                 !map)
          closure.cl_fun.funs
    | _ -> ()
  in
  Flambdaiter.iter aux expr;
  !map

let propagate map : CFS.t =
  let map = ref map in
  let pure = ref CFS.empty in
  let rec aux seen v =
    if CFS.mem v seen || CFS.mem v !pure
    then true, seen
    else
      if CFM.mem v !map
      then match CFM.find v !map with
        | Impure -> false, seen
        | Pure_if deps ->
            let f v (res, seen) =
              let (res', seen) = aux (CFS.add v seen) v in
              res' && res, seen
            in
            let (res, _) as ret = CFS.fold f deps (true, seen) in
            if not res then map := CFM.add v Impure !map;
            ret
      else false, seen
  in
  let f v _ =
    let res, seen = aux (CFS.singleton v) v in
    if res then pure := CFS.union !pure seen
  in
  CFM.iter f !map;
  !pure

let pure_functions expr =
  propagate (collect_function_dep expr)

(**************************************)

let nid () = ExprId.create ()

type lets =
  { expr : ExprId.t flambda;
    kind : let_kind }

type links =
  { uses : ExprSet.t VarMap.t;
    lets : lets VarMap.t;
    lets_dep : VarSet.t VarMap.t;
    floating_lets : VarSet.t }

let empty_links = { lets = VarMap.empty; uses = VarMap.empty; lets_dep = VarMap.empty; floating_lets = VarSet.empty }

let lets_dep lets =
  let open Variable_connected_components in
  let let_dep { expr } =
    Flambdaiter.free_variables expr in
  let lets_dep = VarMap.map let_dep lets in
  let floating_vars = VarMap.keys lets in
  let lets_floating_dep = VarMap.map (VarSet.inter floating_vars) lets_dep in
  let components = component_graph lets_floating_dep in
  let component_deps = Array.map (fun (comp, _) ->
      let deps = match comp with
        | No_loop id -> VarMap.find id lets_dep
        | Has_loop ids ->
            List.fold_left (fun set id ->
                VarSet.union set (VarMap.find id lets_dep))
              VarSet.empty ids in
      VarSet.diff deps floating_vars)
      components
  in

  let let_deps = ref VarMap.empty in
  for i = Array.length components - 1 downto 0 do
    let comp, deps = components.(i) in
    let var_deps =
      List.fold_left (fun set dep -> VarSet.union set component_deps.(dep))
        component_deps.(i) deps in
    component_deps.(i) <- var_deps;
    let ids = match comp with
      | No_loop id -> [id]
      | Has_loop ids -> ids in
    let_deps :=
      List.fold_left (fun let_deps id -> VarMap.add id var_deps let_deps)
        !let_deps ids;
  done;
  !let_deps

(* like Flambdaiter.free_variables, except that it go throug closures *)
let not_bound_variables tree =
  let rec loop (free,bound) bound_here expr =
    let free_vars = Flambdaiter.expression_free_variables expr in
    let free = VarSet.union free free_vars in
    let bound = VarSet.union bound bound_here in
    Flambdaiter.fold_subexpressions loop (free,bound) expr
  in
  let (free,bound), _ = loop (VarSet.empty, VarSet.empty) VarSet.empty tree in
  VarSet.diff free bound

let live_lets lets expr =
  let let_deps = VarMap.map (fun { expr } -> not_bound_variables expr) lets in
  let roots = not_bound_variables expr in
  let live = ref VarSet.empty in
  let queue = Queue.create () in
  let add_live v =
    if not (VarSet.mem v !live)
    then (live := VarSet.add v !live;
          Queue.push v queue)
  in
  VarSet.iter add_live roots;
  while not (Queue.is_empty queue) do
    let v = Queue.take queue in
    let deps = try VarMap.find v let_deps with Not_found -> VarSet.empty in
    VarSet.iter add_live deps
  done;
  VarMap.filter (fun v _ -> VarSet.mem v !live) lets

let mark_needs expr lets =
  let links = ref empty_links in

  let add_node expr =
    let eid = data_at_toplevel_node expr in
    let fv = Flambdaiter.expression_free_variables expr in

    let add_use v uses =
      let set =
        try VarMap.find v uses
        with Not_found -> ExprSet.empty in
      VarMap.add v (ExprSet.add eid set) uses in

    let uses = VarSet.fold add_use fv !links.uses in
    links := { !links with uses } in
  Flambdaiter.iter add_node expr;
  VarMap.iter (fun _ { expr } -> Flambdaiter.iter add_node expr) lets;

  { !links with lets }

let add_pure_var kind var env =
  match kind with
  | Assigned -> env
  | Not_assigned ->
      { env with pure_variables = VarSet.add var env.pure_variables }

let add_let kind var expr acc =
  VarMap.add var { expr; kind } acc

type ret = lets VarMap.t * ExprId.t flambda

let rec remove_pure_lets env acc expr : ret =
  match expr with
  | Flet(kind,var,def,body,eid) ->
      let body_env = add_pure_var kind var env in
      if pure_expression env def
      then
        let acc, def = remove_pure_lets env acc def in
        let acc = add_let kind var def acc in
        remove_pure_lets body_env acc body
      else
        let acc, def = remove_pure_lets env acc def in
        let acc, body = remove_pure_lets body_env acc body in
        acc, Flet(kind,var,def,body,eid)

  (* TODO: letrec *)

  | e ->
      let aux acc bound expr =
        let env = VarSet.fold (add_pure_var Not_assigned) bound env in
        let acc, expr = remove_pure_lets env acc expr in
        acc, expr in
      let acc, e =
        Flambdaiter.fold_subexpressions aux acc e in
      acc, e

let prepare expr =

  (* let links = mark_needs expr VarMap.empty in *)
  let env = { empty_env with pure_functions = pure_functions expr } in
  let lets, expr = remove_pure_lets env VarMap.empty expr in
  (* let links = { links with lets; lets_dep = lets_dep lets; floating_lets = VarMap.keys lets } in *)

  let lets = live_lets lets expr in
  let links = mark_needs expr lets in
  let links = { links with lets_dep = lets_dep lets; floating_lets = VarMap.keys lets } in
  links, expr

type rebuild_ret = links * VarSet.t * ExprId.t flambda

let remove_bound_vars uses bound =
  (* remove need of variables bound by a non floating expression *)
  VarSet.fold (fun v uses -> VarMap.remove v uses) bound uses

let remove_use v eid uses =
  let eids = try VarMap.find v uses with Not_found -> assert false in
  assert(ExprSet.mem eid eids);
  if ExprSet.cardinal eids = 1
  then begin
    VarMap.remove v uses
  end
  else VarMap.add v (ExprSet.remove eid eids) uses

let add_use v eid uses =
  let set =
    try VarMap.find v uses
    with Not_found -> ExprSet.empty in
  VarMap.add v (ExprSet.add eid set) uses

let move_uses_to_parent parent eid uses needed =
  let aux v uses =
    uses
    |> remove_use v eid
    |> add_use v parent
  in
  VarSet.fold aux needed uses

let find_lets_to_add links loop_stack needed =
  let aux v set =
    let eids = try VarMap.find v links.uses with Not_found -> assert false in
    let card = ExprSet.cardinal eids in
    assert(card > 0);
    if ExprSet.cardinal eids = 1
    then match loop_stack with
        | [] -> (* no loop *)
            VarSet.add v set
        | loop_top :: _ ->
            let deps = VarMap.find v links.lets_dep in
            if VarSet.is_empty (VarSet.inter loop_top deps)
            then set (* if no needed var bound since the last loop: we move lets out of the loop *)
            else VarSet.add v set
    else set in
  VarSet.fold aux needed VarSet.empty

let is_loop = function
  | Fwhile _
  | Ffor _ -> true
  | _ -> false

type loop_stack = VarSet.t list

let rec rebuild links expr bound (loop_stack:loop_stack) : rebuild_ret =
  let current_eid = data_at_toplevel_node expr in
  let expr_needed = Flambdaiter.expression_free_variables expr in
  let links = { links with uses = remove_bound_vars links.uses bound } in
  let inner_loop_stack =
    if is_loop expr
    then VarSet.empty :: loop_stack
    else loop_stack
  in
  let (links, needed), expr =
    match expr with
    | Fclosure ({ cl_fun; cl_free_var } as closure, d) ->
        (* This can be simplified when free_variables are only variables *)
        let acc = (links, expr_needed) in
        let acc, funs =
          let f = continue current_eid [] in
          VarMap.fold (fun v fun_decl (acc, funs) ->
              let acc, body = f acc fun_decl.free_variables fun_decl.body in
            acc, VarMap.add v { fun_decl with body } funs)
            cl_fun.funs (acc, VarMap.empty)
        in
        let cl_fun = { cl_fun with funs } in
        let acc, cl_free_var =
          let f = continue current_eid inner_loop_stack in
          VarMap.fold (fun v flam (acc, free_vars) ->
              let acc, flam = f acc VarSet.empty flam in
              acc, VarMap.add v flam free_vars)
            cl_free_var (acc, VarMap.empty)
        in
        acc, Fclosure({ closure with cl_fun; cl_free_var }, d)
    | _ ->
        Flambdaiter.fold_subexpressions (continue current_eid inner_loop_stack) (links, expr_needed) expr
  in
  let needed = VarSet.inter needed links.floating_lets in
  let lets_to_add = find_lets_to_add links loop_stack needed in
  add_lets links lets_to_add needed loop_stack expr

and continue parent loop_stack (links,accum_needed) bound expr =
  let loop_stack = match loop_stack with
    | [] -> []
    | h::t -> VarSet.union bound h :: t in
  let (links, needed, expr) = rebuild links expr bound loop_stack in
  let eid = data_at_toplevel_node expr in
  let uses = move_uses_to_parent parent eid links.uses needed in
  ({ links with uses }, VarSet.union accum_needed needed), expr

and add_lets links lets_to_add needed loop_stack expr =
  if VarSet.is_empty lets_to_add
  then links, needed, expr
  else
    let added_let = VarSet.choose lets_to_add in
    let lets_to_add = VarSet.remove added_let lets_to_add in
    let lets =
      try Some (VarMap.find added_let links.lets)
      with Not_found -> None
    in
    match lets with
    | None ->
        (* not a floating let *)
        add_lets links lets_to_add needed loop_stack expr
    | Some { kind; expr = let_def } ->
        let links = { links with lets = VarMap.remove added_let links.lets } in
        let let_eid = nid () in
        let body_eid = data_at_toplevel_node expr in
        let links = { links with uses = remove_use added_let body_eid links.uses } in
        let needed = VarSet.remove added_let needed in
        let uses = move_uses_to_parent let_eid body_eid links.uses needed in
        let links = { links with uses } in
        let (links, needed), let_def = continue let_eid loop_stack (links, needed) VarSet.empty let_def in
        let expr = Flet(kind, added_let, let_def, expr, let_eid) in
        let lets_to_add = find_lets_to_add links loop_stack needed in
        add_lets links lets_to_add needed loop_stack expr

let move_lets expr =
  let expr = Flambdaiter.map_data (fun eid -> ExprId.create ?name:(ExprId.name eid) ()) expr in
  let links, expr = prepare expr in
  let links, needed, expr = rebuild links expr VarSet.empty [] in
  if not (VarSet.is_empty needed) || not (VarMap.is_empty links.uses) ||
     not (VarMap.is_empty links.lets)
  then Format.eprintf "%a@." Printflambda.flambda expr;
  if not (VarSet.is_empty needed)
  then Format.printf "not empty needed: %a@." VarSet.print needed;
  assert(VarSet.is_empty needed);
  if not (VarMap.is_empty links.uses)
  then Format.printf "not empty uses: %a@." (VarMap.print (ExprSet.print)) links.uses;
  assert(VarMap.is_empty links.uses);
  if not (VarMap.is_empty links.lets)
  then Format.printf "not empty lets: %a@." VarSet.print (VarMap.keys links.lets);
  assert(VarMap.is_empty links.lets);
  expr

let remove_trivial_lets expr =
  let aux = function
    | Flet(_,v,def,Fvar (v',_),_) when Variable.equal v v' -> def
    | e -> e
  in
  Flambdaiter.map aux expr

open Flambdapasses

let move_lets_pass =
  { name = "move_lets";
    pass = (fun expr _ -> move_lets expr) }

let remove_trivial_lets_pass =
  { name = "remove_trivial_lets";
    pass = (fun expr _ -> remove_trivial_lets expr) }

let () =
  if Clflags.experiments
  then Flambdapasses.register_pass Loop 12 move_lets_pass;
  Flambdapasses.register_pass Loop 13 remove_trivial_lets_pass

let passes = [move_lets_pass; remove_trivial_lets_pass]
