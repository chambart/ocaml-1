open Ext_types
open Abstract_identifiers
open Flambda

let compare_array c a1 a2 =
  let v = compare (Array.length a1) (Array.length a2) in
  if v <> 0
  then v
  else
    let rec aux i =
      if i < 0 then 0
      else
        let v = c a1.(i) a2.(i) in
        if v <> 0
        then v
        else aux (i-1)
    in
    aux (Array.length a1 - 1)

let equal_array eq a1 a2 =
  let rec aux eq i =
    if i < 0 then true
    else
      eq a1.(i) a2.(i)
      && aux eq (i-1)
  in
  Array.length a1 = Array.length a2 &&
  aux eq (Array.length a1 - 1)

module Value = struct

  type block = Variable.t (* allocation point *)
               * Asttypes.mutable_flag
               * VarSet.t array (* fields *)

  (* only functions of arity 1 *)
  type func = Variable.t (* argument *)
              * VarSet.t VarMap.t (* closure *)
              * (Variable.t list * ExprId.t flambda) (* missing arguments, code *)

  (* unspecified function *)
  type ufunc = func VarMap.t

  type t =
    | PBlock of block
    | PFun of func
    | PUfunc of ufunc
    | POther

  let compare_fun (id1, s1, (m1, b1)) (id2, s2, (m2, b2)) =
    let r = compare id1 id2 in
    if r <> 0
    then (assert(b1 == b2); r)
    else VarMap.compare VarSet.compare s1 s2

  let compare v1 v2 =
    match v1, v2 with
    | POther, POther -> 0
    | POther, (PBlock _ | PFun _ | PUfunc _) -> -1
    | (PBlock _ | PFun _ | PUfunc _), POther -> 1
    | PBlock (id1, mut1, l1), PBlock (id2, mut2, l2) ->
        let c = Variable.compare id1 id2 in
        if c <> 0
        then c
        else
          let c = compare mut1 mut2 in
          if c <> 0
          then c (* should always be equal if it is the same variable *)
          else compare_array VarSet.compare l1 l2
    | PBlock _, (PFun _ | PUfunc _) -> -1
    | (PFun _ | PUfunc _), PBlock _ -> 1
    | PFun f1, PFun f2 ->
        compare_fun f1 f2
    | PFun _, PUfunc _ -> -1
    | PUfunc _, PFun _ -> 1
    | PUfunc u1, PUfunc u2 ->
        VarMap.compare compare_fun u1 u2

  let block v mut args : block = v, mut, Array.map VarSet.singleton args

  let func arg clos n expr : func = arg, clos, (n, expr)

  let ufunc funs : ufunc = funs

end

module BlockSet : sig
  type t
  val empty : t
  val add : Value.block -> t -> t
  val union : t -> t -> t
  val equal : t -> t -> bool
  val is_empty : t -> bool

  val field : t -> int -> VarSet.t
  val fields : t -> VarSet.t
end = struct
  type t =
    { mut : VarSet.t array IntMap.t VarMap.t;
      immut : VarSet.t array IntMap.t VarMap.t }
  (* invariant: there is no block with an empty field
     t is empty iff the map is empty *)

  let empty = { mut = VarMap.empty; immut = VarMap.empty }

  let empty_block (_,_,v) =
    try
      for i = 0 to Array.length v - 1 do
        if VarSet.is_empty v.(i)
        then raise Exit
      done;
      false
    with Exit -> true

  let array_union a1 a2 =
    Array.mapi (fun i s -> VarSet.union s a2.(i)) a1

  let add' block set =
    let (id, mut, fields) = block in
    let size = Array.length fields in
    let s1 =
      try VarMap.find id set with
      | Not_found -> IntMap.empty in
    let fields =
      try
        let prev_block = IntMap.find size s1 in
        array_union fields prev_block
      with
      | Not_found -> fields in
    VarMap.add id
      (IntMap.add size fields s1)
      set

  let add (block:Value.block) (set:t) =
    if empty_block block
    then (* it is ok to drop a block with an empty field: it is not reachable *)
      set
    else
      let (_,mut,_) = block in
      match mut with
      | Asttypes.Mutable -> { set with mut = add' block set.mut }
      | Asttypes.Immutable -> { set with immut = add' block set.immut }

  let union (s1:t) (s2:t) : t =
    let f s1 s2 =
      VarMap.union_merge (IntMap.union_merge array_union) s1 s2
    in
    { mut = f s1.mut s2.mut;
      immut = f s1.immut s2.immut }

  let equal (s1:t) (s2:t) : bool =
    let f s1 s2 =
      VarMap.equal (IntMap.equal (equal_array VarSet.equal)) s1 s2
    in
    f s1.immut s2.immut &&
    f s1.mut s2.mut

  let is_empty t =
    VarMap.is_empty t.immut &&
    VarMap.is_empty t.mut

  (********************)

  let field' s i acc =
    VarMap.fold (fun _ m acc ->
        IntMap.fold (fun _ a acc ->
            if Array.length a > i && i >= 0
            then VarSet.union a.(i) acc
            else acc)
          m acc)
      s acc

  let field (s:t) i =
    field' s.immut i VarSet.empty
    |> field' s.mut i

  let fields' s acc =
    VarMap.fold (fun _ m acc ->
        IntMap.fold (fun _ a acc ->
            Array.fold_right VarSet.union a acc)
          m acc)
      s acc

  let fields (s:t) =
    fields' s.immut VarSet.empty
    |> fields' s.mut

end

module FuncSet : sig
  type t
  val empty : t
  val add : Value.func -> t -> t
  val union : t -> t -> t
  val equal : t -> t -> bool
  val is_empty : t -> bool
  val elements : t -> Value.func list

  val closure_variable : t -> Closure_variable.t -> VarSet.t
end = struct
  type t = (VarSet.t VarMap.t * (Variable.t list * ExprId.t flambda)) VarMap.t
  (* invariant: there is no function with an empty closure field
     t is empty iff the map is empty *)
  let empty = VarMap.empty

  let union_closure m1 m2 =
    VarMap.union_merge VarSet.union m1 m2

  let add' ((var, clos, (m,b)):Value.func) (s:t) =
    let f =
      try
        let (clos', (m',b')) = VarMap.find var s in
        assert(b == b');
        (union_closure clos clos', (m,b))
      with Not_found -> (clos, (m,b)) in
    VarMap.add var f s

  let add ((_, clos, _) as f) set =
    if VarMap.exists (fun _ s -> VarSet.is_empty s) clos
    then set
    else add' f set

  let union (s1:t) (s2:t) =
    let aux (s1,e) (s2,_) = union_closure s1 s2, e in
    VarMap.union_merge aux s1 s2

  let equal (s1:t) (s2:t) =
    let aux (s1,_) (s2,_) = VarMap.equal VarSet.equal s1 s2 in
    VarMap.equal aux s1 s2

  let is_empty s = VarMap.is_empty s

  let elements (s:t) : Value.func list =
    VarMap.fold (fun id (clos, e) acc -> (id, clos, e) :: acc) s []

  (**************************)

  let closure_variable (s:t) v =
    let v = Closure_variable.unwrap v in
    VarMap.fold (fun _ (clos, _) acc ->
        try VarSet.union (VarMap.find v clos) acc with
        | Not_found -> acc) (* assert false ? *)
      s VarSet.empty

end

module UFuncSet : sig
  type t
  val empty : t
  val add : Value.ufunc -> t -> t
  val union : t -> t -> t
  val equal : t -> t -> bool
  val is_empty : t -> bool

  val closure_function : t -> Closure_function.t -> FuncSet.t
end = struct
  type t = FuncSet.t VarMap.t
  let empty = VarMap.empty

  let add (f:Value.ufunc) (s:t) =
    VarMap.fold (fun var f acc ->
        let func =
          try VarMap.find var acc with
          | Not_found -> FuncSet.empty in
        let func = FuncSet.add f func in
        if FuncSet.is_empty func
        then acc
        else VarMap.add var func acc)
      f s

  let union (s1:t) (s2:t) =
    VarMap.union_merge FuncSet.union s1 s2

  let equal (s1:t) (s2:t) =
    VarMap.equal FuncSet.equal s1 s2

  let is_empty = VarMap.is_empty

  (************************)

  let closure_function (s:t) v =
    let v = Closure_function.unwrap v in
    try VarMap.find v s with
    | Not_found -> FuncSet.empty

end

type 'a result =
  { values : 'a;
    top : bool }

module ValueSet = struct

  type t =
      { other : bool;
        blocks : BlockSet.t;
        funcs : FuncSet.t;
        ufuncs : UFuncSet.t;
        top : bool }

  let empty =
    { other = false;
      blocks = BlockSet.empty;
      funcs = FuncSet.empty;
      ufuncs = UFuncSet.empty;
      top = false }

  let top = { empty with top = true }

  let add_other s = { s with other = true }
  let add_top s = { s with top = true }

  let add_block (b:Value.block) s =
    { s with blocks = BlockSet.add b s.blocks }

  let add_func (f:Value.func) s =
    { s with funcs = FuncSet.add f s.funcs }

  let union_func (f:FuncSet.t) s =
    { s with funcs = FuncSet.union f s.funcs }

  let add_ufunc (f:Value.ufunc) s =
    { s with ufuncs = UFuncSet.add f s.ufuncs }

  let union s1 s2 =
    { other = s1.other || s2.other;
      blocks = BlockSet.union s1.blocks s2.blocks;
      funcs = FuncSet.union s1.funcs s2.funcs;
      ufuncs = UFuncSet.union s1.ufuncs s2.ufuncs;
      top = s1.top || s2.top }

  let equal s1 s2 =
    s1.other = s2.other &&
    BlockSet.equal s1.blocks s2.blocks &&
    FuncSet.equal s1.funcs s2.funcs &&
    UFuncSet.equal s1.ufuncs s2.ufuncs &&
    s1.top = s2.top

  let is_empty s =
    s.top = false &&
    s.other = false &&
    BlockSet.is_empty s.blocks &&
    FuncSet.is_empty s.funcs &&
    UFuncSet.is_empty s.ufuncs

  (*********************)

  let field s i =
    { values = BlockSet.field s.blocks i;
      top = s.top }

  let closure_variable s v =
    { values = FuncSet.closure_variable s.funcs v;
      top = s.top }

  let closure_function s v =
    { values = UFuncSet.closure_function s.ufuncs v;
      top = s.top }

  let functions s =
    { values = FuncSet.elements s.funcs;
      top = s.top }

end

module CodeSet : sig
  type t
  val empty : t
  val add : ExprId.t flambda -> t -> t
end = struct
  type t = ExprId.t flambda ExprMap.t
  let empty = ExprMap.empty
  let add f s = ExprMap.add (data_at_toplevel_node f) f s
end

type stack (* TODO *)

type call_set = unit (* TODO *)

type state =
  { reached : CodeSet.t;
    env : ValueSet.t VarMap.t;
    globals : ValueSet.t IntMap.t;
    escape : VarSet.t;
    escape_fun : VarSet.t; (* last argument *)
  }

let push_stack (state:state) (stack:stack) (ret:Variable.t) (kont:ExprId.t flambda) =
  stack (* TODO *)

let call (state:state) (stack:stack) (body:ExprId.t flambda) =
  state (* TODO *)

let reached state expr =
  { state with reached = CodeSet.add expr state.reached }

let binding state v =
  try VarMap.find v state.env with
  | Not_found -> ValueSet.empty

let assign state v contents =
  let set =
    try
      let set = VarMap.find v state.env in
      ValueSet.union contents set
    with Not_found -> contents
  in
  { state with env = VarMap.add v set state.env }

let bound_or_empty state v =
  try VarMap.find v state.env
  with Not_found -> ValueSet.empty

let assign_block state v block =
  let set = bound_or_empty state v in
  let set = ValueSet.add_block block set in
  { state with env = VarMap.add v set state.env }

let assign_ufunc state v ufunc =
  let set = bound_or_empty state v in
  let set = ValueSet.add_ufunc ufunc set in
  { state with env = VarMap.add v set state.env }

let assign_func_r state v func =
  let set = bound_or_empty state v in
  let set = ValueSet.union_func func.values set in
  let set =
    if func.top
    then ValueSet.add_top set
    else set in
  { state with env = VarMap.add v set state.env }

let assign_other state v =
  let set = bound_or_empty state v in
  let set = ValueSet.add_other set in
  { state with env = VarMap.add v set state.env }

let ebinding state = function
  | Fvar (v, _) -> binding state v
  | _ -> assert false (* forbidden in ANF *)

let var = function
  | Fvar (v, _) -> v
  | _ -> assert false (* forbidden in ANF *)

let var_union state (vars: VarSet.t result) =
  let acc = if vars.top then ValueSet.top else ValueSet.empty in
  VarSet.fold (fun v -> ValueSet.union (binding state v))
    vars.values acc

let rec fp state stack = function
  | Flet(_, v, def, body, _) ->
      let stack = push_stack state stack v body in
      let state = fp_let state stack v def in
      if ValueSet.is_empty (binding state v)
      then state
      else
        let state = reached state body in
        fp state stack body
  | _ -> assert false

and fp_let state stack v = function
  | Fevent _
  | Fsequence _
  | Flet _ -> assert false

  | Fvar (v', _) ->
      let r = binding state v' in
      assign state v r

  | Fprim(prim, args, _, _) ->
      begin match prim, args with
      | Lambda.Pmakeblock(_tag,mut), _ ->
          let res = Value.block v mut (Array.map var (Array.of_list args)) in
          assign_block state v res
      | Lambda.Pfield i, [arg] ->
          let r = ebinding state arg in
          let res = var_union state (ValueSet.field r i) in
          assign state v res
      | _ -> assert false
      end

  | Fassign(x, Fvar (y,_), _) ->
      let r = binding state y in
      let state = assign state x r in
      if ValueSet.is_empty r
      then state
      else assign_other state v

  | Fassign(_, _, _) -> assert false

  | Fvariable_in_closure({vc_closure = f; vc_var = var},_) ->
      let f = ebinding state f in
      let r = ValueSet.closure_variable f var in
      assign state v (var_union state r)

  | Ffunction({fu_closure = f;fu_fun = var},_) ->
      let f = ebinding state f in
      assign_func_r state v (ValueSet.closure_function f var)

  | Fclosure ({cl_fun={funs};cl_free_var},_) ->
      let outer_closure = VarMap.map (fun e -> VarSet.singleton (var e)) cl_free_var in
      let prepare_function { body; params } : Value.func =
        match params with
        | [] -> assert false
        | h :: t -> Value.func h outer_closure t body
      in
      let functions = VarMap.map prepare_function funs in
      assign_ufunc state v (Value.ufunc functions)

  | Fapply ({ap_function = f;ap_arg = args; ap_kind},_) ->
      let f = ebinding state f in
      let state, res = match ap_kind with
        | Direct _ -> apply_direct state stack f args
        | Indirect ->
          match args with
            | [] | _::_::_ -> assert false (* ANF *)
            | [arg] -> apply_indirect state stack f arg
      in
      assign state v res

(* Fsymbol _ ->  *)
  (* | Fconst _ *)
  (* | Funreachable _ -> () *)


  (* | Flet ( _, _, f1, f2,_) *)
  (* | Ftrywith (f1,_,f2,_) *)
  (* | Fwhile (f1,f2,_) *)
  (* | Fstaticcatch (_,_,f1,f2,_) -> *)

  (* | Ffor (_,f1,f2,_,f3,_) *)
  (* | Fifthenelse (f1,f2,f3,_) -> *)

  (* | Fstaticraise (_,l,_) *)
  (* | Fprim (_,l,_,_) -> *)

  (* | Fletrec (defs, body,_) -> *)
  (* | Fswitch (arg,sw,_) -> *)
  (* | Fsend (_,f1,f2,fl,_,_) -> *)

  | _ -> assert false

and apply_indirect (state:state) (stack:stack) f arg =
  let apply_one (state,result) f =
    let (param, clos, (missing, body)) = f in
    let state = assign state param (ebinding state arg) in
    match missing with
    | [] ->
        (* completely applied function *)
        let state = call state stack body in
        state, result (* do not call directly *)
    | h::t ->
        let clos = VarMap.add param (VarSet.singleton (var arg)) clos in
        let next_f = Value.func h clos t body in
        let result = ValueSet.add_func next_f result in
        state, result
  in
  let funs = ValueSet.functions f in
  let result = if funs.top then ValueSet.top else ValueSet.empty in
  List.fold_left apply_one (state, result) funs.values

and apply_direct (state:state) (stack:stack) f args =
  let apply_one (state,result) f =
    let (param, clos, (missing, body)) = f in
    let state =
      List.fold_left2 (fun state param arg -> assign state param (ebinding state arg))
        state (param::missing) args in
    let state = call state stack body in
    state, result (* do not call directly *)
  in
  let funs = ValueSet.functions f in
  let result = if funs.top then ValueSet.top else ValueSet.empty in
  List.fold_left apply_one (state, result) funs.values
