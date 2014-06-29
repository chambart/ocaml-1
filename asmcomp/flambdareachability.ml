open Ext_types
open Abstract_identifiers
open Flambda

let print = try Sys.getenv "REACH" = "y" with _ -> false
let iprintf f =
  if print
  then Format.fprintf Format.std_formatter f
  else Format.ifprintf Format.std_formatter f

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

  let is_empty_block ((_,_,v):block) =
    try
      for i = 0 to Array.length v - 1 do
        if VarSet.is_empty v.(i)
        then raise Exit
      done;
      false
    with Exit -> true

  let block_id ((id, _, _):block) = id
  let is_mutable_block ((_,mut,_):block) = mut = Asttypes.Mutable

end

module ImmBlockSet : sig
  type t
  val empty : t
  val add : Value.block -> t -> t
  val union : t -> t -> t
  val equal : t -> t -> bool
  val is_empty : t -> bool

  val field : t -> int -> VarSet.t
  val fields : t -> VarSet.t

  val add_field : t -> int -> VarSet.t -> t
  val add_sub_field : t -> Variable.t -> int -> VarSet.t -> t

  (* used to implement HeapBlockSet *)
  val sub_field : t -> Variable.t -> int -> VarSet.t
  val sub_fields : t -> Variable.t -> VarSet.t
end = struct
  type t = VarSet.t array IntMap.t VarMap.t

  let empty = VarMap.empty

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

  let add = add'
  (* problem with recursive values if we do that: *)
  (* let add (block:Value.block) (set:t) = *)
  (*   if Value.is_empty_block block *)
  (*   then (\* it is ok to drop a block with an empty field: it is not reachable *\) *)
  (*     set *)
  (*   else *)
  (*     add' block set *)

  let union (s1:t) (s2:t) : t =
    VarMap.union_merge (IntMap.union_merge array_union) s1 s2

  let equal (s1:t) (s2:t) : bool =
    VarMap.equal (IntMap.equal (equal_array VarSet.equal)) s1 s2

  let is_empty t =
    VarMap.is_empty t

  (********************)

  let add_int_field m i contents =
    IntMap.mapi (fun size a ->
        if size <= i
        then a
        else
          let union = VarSet.union contents a.(i) in
          if VarSet.equal union a.(i)
          then a
          else
            let a = Array.copy a in
            a.(i) <- VarSet.union contents a.(i);
            a)
      m

  let add_field s i contents =
    if i >= 0
    then
      VarMap.map (fun m -> add_int_field m i contents) s
    else s

  let add_sub_field s v i contents =
    if i >= 0
    then
      try
        let m = VarMap.find v s in
        let m = add_int_field m i contents in
        VarMap.add v m s
      with Not_found -> s
    else s

  let int_field i s acc =
    IntMap.fold (fun _ a acc ->
        if Array.length a > i && i >= 0
        then VarSet.union a.(i) acc
        else acc)
      s acc

  let field' s i acc =
    VarMap.fold (fun _ m acc -> int_field i m acc) s acc

  let field (s:t) i =
    field' s i VarSet.empty

  let sub_field (s:t) v i =
    try int_field i (VarMap.find v s) VarSet.empty
    with Not_found -> VarSet.empty


  let int_fields s acc =
    IntMap.fold (fun _ a acc ->
        Array.fold_right VarSet.union a acc)
      s acc

  let fields' s acc =
    VarMap.fold (fun _ m acc -> int_fields m acc) s acc

  let fields (s:t) =
    fields' s VarSet.empty

  let sub_fields (s:t) v =
    try int_fields (VarMap.find v s) VarSet.empty
    with Not_found -> VarSet.empty

end

module HeapBlockSet : sig
  type t
  type heap
  val empty_heap : heap
  val empty : t
  val add : Value.block -> heap -> t -> heap * t
  val union : t -> t -> t
  val equal : t -> t -> bool
  val equal_heap : heap -> heap -> bool
  val is_empty : t -> bool

  val field : heap -> t -> int -> VarSet.t
  val fields : heap -> t -> VarSet.t
  val set_field : heap -> t -> int -> VarSet.t -> heap
end = struct
  type t = VarSet.t
  type heap = ImmBlockSet.t

  let empty = VarSet.empty
  let empty_heap = ImmBlockSet.empty

  let add' (block:Value.block) (heap:heap) (set:t) =
    let heap = ImmBlockSet.add block heap in
    let set = VarSet.add (Value.block_id block) set in
    heap, set

  let add = add'
  (* Problem with empty blocks if we do that: *)
  (* let add (block:Value.block) (heap:heap) (set:t) = *)
  (*   if Value.is_empty_block block *)
  (*   then heap, set *)
  (*   else add' block heap set *)

  let union s1 s2 = VarSet.union s1 s2
  let equal s1 s2 =
    VarSet.equal s1 s2
  let equal_heap h1 h2 =
    ImmBlockSet.equal h1 h2

  let is_empty s = VarSet.is_empty s

  let field heap s i =
    VarSet.fold (fun v acc ->
        VarSet.union (ImmBlockSet.sub_field heap v i) acc)
      s VarSet.empty

  let fields heap s =
    VarSet.fold (fun v acc ->
        VarSet.union (ImmBlockSet.sub_fields heap v) acc)
      s VarSet.empty

  let set_field heap s i contents =
    VarSet.fold (fun v heap ->
        ImmBlockSet.add_sub_field heap v i contents)
      s heap

end

module BlockSet : sig
  type t
  type heap
  val empty_heap : heap
  val empty : t
  val add : Value.block -> heap -> t -> heap * t
  val union : t -> t -> t
  val equal : t -> t -> bool
  val equal_heap : heap -> heap -> bool
  val is_empty : t -> bool

  val field : heap -> t -> int -> VarSet.t
  val fields : heap -> t -> VarSet.t
  val set_field : heap -> t -> int -> VarSet.t -> heap

end = struct

  type heap = HeapBlockSet.heap

  type t =
    { mut : HeapBlockSet.t;
      immut : ImmBlockSet.t }

  let empty_heap = HeapBlockSet.empty_heap

  let empty =
    { mut = HeapBlockSet.empty;
      immut = ImmBlockSet.empty }

  let add (block:Value.block) (heap:heap) (set:t) =
    if Value.is_mutable_block block
    then
      let heap, mut = HeapBlockSet.add block heap set.mut in
      heap, { set with mut}
    else
      heap, { set with immut = ImmBlockSet.add block set.immut }

  let union (s1:t) (s2:t) : t =
    { mut = HeapBlockSet.union s1.mut s2.mut;
      immut = ImmBlockSet.union s1.immut s2.immut }

  let equal (s1:t) (s2:t) : bool =
    ImmBlockSet.equal s1.immut s2.immut &&
    HeapBlockSet.equal s1.mut s2.mut

  let equal_heap h1 h2 =
    HeapBlockSet.equal_heap h1 h2

  let is_empty t =
    ImmBlockSet.is_empty t.immut &&
    HeapBlockSet.is_empty t.mut

  (********************)

  let field (heap:heap) (s:t) i =
    VarSet.union
      (ImmBlockSet.field s.immut i)
      (HeapBlockSet.field heap s.mut i)

  let fields (heap:heap) (s:t) =
    VarSet.union
      (ImmBlockSet.fields s.immut)
      (HeapBlockSet.fields heap s.mut)

  let set_field (heap:heap) (s:t) i contents =
    (* do we warn if immut isn't empty ?
       there are cases where this could occur with gadts... *)
    HeapBlockSet.set_field heap s.mut i contents

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

  let add = add'
  (* let add ((_, clos, _) as f) set = *)
  (*   if VarMap.exists (fun _ s -> VarSet.is_empty s) clos *)
  (*   then set *)
  (*   else add' f set *)

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
  val functions : t -> FuncSet.t
end = struct
  type t = FuncSet.t VarMap.t
  let empty = VarMap.empty

  let add (f:Value.ufunc) (s:t) =
    VarMap.fold (fun var f acc ->
        let func =
          try VarMap.find var acc with
          | Not_found -> FuncSet.empty in
        let func = FuncSet.add f func in
        (* if FuncSet.is_empty func *)
        (* then acc *)
        (* else *)
        VarMap.add var func acc)
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

  let functions (s:t) =
    VarMap.fold (fun _ -> FuncSet.union) s FuncSet.empty

end

type 'a result =
  { values : 'a;
    top : bool }

module ValueSet = struct

  type heap = BlockSet.heap

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

  let empty_heap = BlockSet.empty_heap

  let top = { empty with top = true }

  let add_other s = { s with other = true }
  let add_top s = { s with top = true }

  let add_block (b:Value.block) (heap:heap) s =
    let heap, blocks = BlockSet.add b heap s.blocks in
    heap, { s with blocks }

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

  let equal_heap h1 h2 =
    BlockSet.equal_heap h1 h2

  let is_empty s =
    s.top = false &&
    s.other = false &&
    BlockSet.is_empty s.blocks &&
    FuncSet.is_empty s.funcs &&
    UFuncSet.is_empty s.ufuncs

  (*********************)

  let is_top s = s.top

  let field heap s i =
    { values = BlockSet.field heap s.blocks i;
      top = s.top }

  let fields heap s =
    { values = BlockSet.fields heap s.blocks;
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

  let ufunctions s =
    { values = UFuncSet.functions s.ufuncs;
      top = s.top }

  let set_field (heap:heap) (s:t) i contents : heap =
    BlockSet.set_field heap s.blocks i contents

end

type code = ExprId.t flambda

module CodeSet : sig
  type t
  val empty : t
  val add : code -> t -> t
  val mem : code -> t -> bool
  val union : t -> t -> t
  val singleton : code -> t
  val fold : (code -> 'acc -> 'acc) -> t -> 'acc -> 'acc
  val equal : t -> t -> bool
  val subset : t -> t -> bool
end = struct
  type t = ExprId.t flambda ExprMap.t
  let empty = ExprMap.empty
  let add f s = ExprMap.add (data_at_toplevel_node f) f s
  let mem f s = ExprMap.mem (data_at_toplevel_node f) s
  let union s1 s2 = ExprMap.union_right s1 s2
  let singleton f = ExprMap.singleton (data_at_toplevel_node f) f
  let fold f s acc = ExprMap.fold (fun _ code acc -> f code acc) s acc
  let equal s1 s2 = ExprMap.equal (fun _ _ -> true) s1 s2
  let subset s1 s2 =
    let aux k _ =
      if not (ExprMap.mem k s2) then raise Exit
    in
    try ExprMap.iter aux s1; true with _ -> false
end

module CodeMap : sig
  type 'a t
  val empty : 'a t
  val add : code -> 'a -> 'a t -> 'a t
  val singleton : code -> 'a -> 'a t
  val find : code -> 'a t -> 'a
  val equal : ('a -> 'a -> bool) -> 'a t -> 'a t -> bool
end = struct
  type 'a t = 'a ExprMap.t
  let empty = ExprMap.empty
  let add f v s = ExprMap.add (data_at_toplevel_node f) v s
  let singleton f v = ExprMap.singleton (data_at_toplevel_node f) v
  let find f s = ExprMap.find (data_at_toplevel_node f) s
  let equal f s1 s2 = ExprMap.equal f s1 s2
end

type stack_part = { return_var : Variable.t; return_point : code }

module StackPart : sig
  type t
  val empty : t
  val add : stack_part -> t -> t
  val union : t -> t -> t
  val subset : t -> t -> bool
  val singleton : stack_part -> t
  val remove_return_var : t -> t
  val toplevel : Variable.t -> t
  val return_vars : t -> VarSet.t
  val return_points : t -> CodeSet.t
  val equal : t -> t -> bool
end = struct
  type t = { vars : VarSet.t; points : CodeSet.t }
  let empty = { vars = VarSet.empty; points = CodeSet.empty }
  let add { return_var; return_point } { vars; points } =
    { vars = VarSet.add return_var vars;
      points = CodeSet.add return_point points }
  let union s1 s2 =
    { vars = VarSet.union s1.vars s2.vars;
      points = CodeSet.union s1.points s2.points }
  let subset s1 s2 =
    VarSet.subset s1.vars s2.vars &&
    CodeSet.subset s1.points s2.points
  let singleton { return_var; return_point } =
    { vars = VarSet.singleton return_var;
      points = CodeSet.singleton return_point }
  let equal s1 s2 =
    VarSet.equal s1.vars s2.vars &&
    CodeSet.equal s1.points s2.points
  let return_vars { vars } = vars
  let return_points { points } = points
  let toplevel v = { vars = VarSet.singleton v; points = CodeSet.empty }
  let remove_return_var s =
    { vars = VarSet.empty; points = s.points }
end

module StackSet : sig
  type t
  val empty : t
  val add_call : stack_part -> t -> t
  val add_raise : stack_part -> t -> t
  val union : t -> t -> t
  val equal : t -> t -> bool
  val subset : t -> t -> bool
  val remove_return_var : t -> t
  val set_call : stack_part -> t -> t
  val set_raise : stack_part -> t -> t
  val return_vars : t -> VarSet.t
  val return_points : t -> CodeSet.t
  val exn_return_vars : t -> VarSet.t
  val exn_return_points : t -> CodeSet.t
  val toplevel : return:Variable.t -> uncaught:Variable.t -> t
end = struct
  type t = { calls : StackPart.t; raises : StackPart.t }
  let empty = { calls = StackPart.empty; raises = StackPart.empty }
  let add_call call s = { s with calls = StackPart.add call s.calls }
  let add_raise raisep s = { s with raises = StackPart.add raisep s.raises }
  let union s1 s2 =
    { calls = StackPart.union s1.calls s2.calls;
      raises = StackPart.union s1.raises s2.raises }
  let equal s1 s2 =
    StackPart.equal s1.calls s2.calls &&
    StackPart.equal s1.raises s2.raises
  let subset s1 s2 =
    StackPart.subset s1.calls s2.calls &&
    StackPart.subset s1.raises s2.raises
  let remove_return_var s =
    { s with calls = StackPart.remove_return_var s.calls }
  let set_call call s =
    { s with calls = StackPart.singleton call }
  let set_raise raises s =
    { s with raises = StackPart.singleton raises }

  let return_vars { calls } = StackPart.return_vars calls
  let return_points { calls } = StackPart.return_points calls

  let exn_return_vars { raises } = StackPart.return_vars raises
  let exn_return_points { raises } = StackPart.return_points raises

  let toplevel ~return ~uncaught =
    { calls = StackPart.toplevel return;
      raises = StackPart.toplevel uncaught }
end

type stack = StackSet.t

type kept_state =
  { current_unit_id : Ident.t;
    escape_stack : StackSet.t;
    static_handler : (Variable.t list * code) StaticExceptionMap.t;
    escape : VarSet.t;
    globals : ValueSet.t IntMap.t;
    reached : CodeSet.t }


type state =
  { stacks : StackSet.t CodeMap.t;
    env : ValueSet.t VarMap.t;
    heap : ValueSet.heap;
    k : kept_state }

let equal_state s1 s2 =
  CodeSet.equal s1.k.reached s2.k.reached &&
  CodeMap.equal StackSet.equal s1.stacks s2.stacks &&
  VarMap.equal ValueSet.equal s1.env s2.env &&
  IntMap.equal ValueSet.equal s1.k.globals s2.k.globals &&
  VarSet.equal s1.k.escape s2.k.escape &&
  ValueSet.equal_heap s1.heap s2.heap

let initial_state current_unit_id =
  let k = { reached = CodeSet.empty;
            globals = IntMap.empty;
            current_unit_id;
            escape = VarSet.empty;
            escape_stack = StackSet.empty;
            static_handler = StaticExceptionMap.empty }
  in
  { stacks = CodeMap.empty;
    env = VarMap.empty;
    heap = ValueSet.empty_heap;
    k }

let push_stack (stack:stack) (ret:Variable.t) (kont:ExprId.t flambda) =
  let spart = { return_var = ret; return_point = kont } in
  StackSet.set_call spart stack

let push_stack_exn (stack:stack) (ret:Variable.t) (kont:ExprId.t flambda) =
  let spart = { return_var = ret; return_point = kont } in
  StackSet.set_raise spart stack

let reached state expr =
  if CodeSet.mem expr state.k.reached
  then state
  else
    { state with k = { state.k with reached = CodeSet.add expr state.k.reached } }

let entry_point current_unit_id ~return ~uncaught expr =
  let state = reached (initial_state current_unit_id) expr in
  let escape_stack = StackSet.toplevel ~return ~uncaught in
  { state with
    stacks = CodeMap.singleton expr escape_stack;
    k =
      { state.k with
        escape = VarSet.of_list [return; uncaught];
        escape_stack = escape_stack } }

let add_stack state stack expr =
  (* iprintf "add_stack %a@." Printflambda.flambda expr; *)
  let stacks =
    try CodeMap.find expr state.stacks
    with Not_found -> StackSet.empty in
  if StackSet.subset stack stacks
  then state
  else
    { state with stacks = CodeMap.add expr (StackSet.union stack stacks) state.stacks }

let call (state:state) (stack:stack) (body:ExprId.t flambda) =
  let state = reached state body in
  add_stack state stack body

let goto_branch (state:state) (stack:stack) (expr:ExprId.t flambda) =
  let state = reached state expr in
  add_stack state stack expr

let goto_branch_no_return (state:state) (stack:stack) (expr:ExprId.t flambda) =
  let stack = StackSet.remove_return_var stack in
  let state = reached state expr in
  add_stack state stack expr

let goto_body (state:state) (stack:stack) (expr:ExprId.t flambda) =
  let state = reached state expr in
  add_stack state stack expr

let binding state v =
  try VarMap.find v state.env with
  | Not_found -> ValueSet.empty

let global state i =
  try IntMap.find i state.k.globals with
  | Not_found -> ValueSet.empty

let assign state v contents =
  let set =
    try
      let set = VarMap.find v state.env in
      ValueSet.union contents set
    with Not_found -> contents
  in
  { state with env = VarMap.add v set state.env }

let assign_global state pos contents =
  let set =
    try
      let set = IntMap.find pos state.k.globals in
      ValueSet.union contents set
    with Not_found -> contents
  in
  { state with k = { state.k with globals = IntMap.add pos set state.k.globals } }

let bound_or_empty state v =
  try VarMap.find v state.env
  with Not_found -> ValueSet.empty

let assign_block state v block =
  let set = bound_or_empty state v in
  let heap, set = ValueSet.add_block block state.heap set in
  { state with env = VarMap.add v set state.env; heap }

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

let assign_top state v =
  let set = bound_or_empty state v in
  let set = ValueSet.add_top set in
  { state with env = VarMap.add v set state.env }

let escapes state v =
  let set = VarSet.of_list v in
  if VarSet.subset set state.k.escape
  then state
  else
    { state with
      k = { state.k with escape = VarSet.union set state.k.escape } }

let ebinding state = function
  | Fvar (v, _) -> binding state v
  | f ->
      Format.eprintf "ebinding %a@." Printflambda.flambda f;
      assert false (* forbidden in ANF *)

let var = function
  | Fvar (v, _) -> v
  | f ->
      Format.eprintf "var %a@." Printflambda.flambda f;
      assert false (* forbidden in ANF *)

let var_union state (vars: VarSet.t result) =
  let acc = if vars.top then ValueSet.top else ValueSet.empty in
  VarSet.fold (fun v -> ValueSet.union (binding state v))
    vars.values acc

let var_union' state (vars: VarSet.t result) =
  VarSet.fold (fun v -> ValueSet.union (binding state v))
    vars.values ValueSet.empty

let return_other state stack =
  VarSet.fold (fun ret state -> assign_other state ret)
    (StackSet.return_vars stack) state

let rec step_expr state stack expr =
  (* iprintf "go: %a@." Printflambda.flambda expr; *)
  match expr with
  | Flet(_, v, def, body, _) ->
      step_let' state stack v def body

  | Fletrec (defs, body,_) ->
      let state =
        List.fold_left (fun state (v, def) ->
            step_let state (push_stack stack v body) v def)
          state defs in
      if List.exists (fun (v,_) -> ValueSet.is_empty (binding state v)) defs
      then state
      else
        let state = goto_body state stack body in
        step_expr state stack body

  | Fvar(v, _) ->
      let values = binding state v in
      if ValueSet.is_empty values
      then state
      else
        let state =
          VarSet.fold (fun ret state -> assign state ret values)
            (StackSet.return_vars stack) state in
        let state =
          CodeSet.fold (fun code state -> reached state code)
            (StackSet.return_points stack) state in
        state

  | Fifthenelse (cond,ifso,ifnot,_) ->
      step_if state stack cond ifso ifnot

  | Fprim(Lambda.Praise, [arg], _, _) ->
      step_raise state stack (Some arg)

  | Ftrywith (body,id,handler,_) ->
      step_trywith state stack body id handler

  | Fstaticcatch (sexn,vars,body,handler,_) ->
      step_staticcatch state stack sexn vars body handler

  | Fstaticraise (sexn,args,_) ->
      step_staticraise state stack sexn args

  | Fwhile (cond,body,_) ->
      step_while state stack cond body

  | Ffor (id,lo,hi,_,body,_) ->
      step_for state stack id lo hi body

  | Fswitch (arg,sw,_) ->
      step_switch state stack arg sw

  | _ ->
      Format.eprintf "not anf: %a@." Printflambda.flambda expr;
      assert false

and step_let' state stack v def body =
  let state = step_let state (push_stack stack v body) v def in
  if ValueSet.is_empty (binding state v)
  then state
  else
    let state = goto_body state stack body in
    step_expr state stack body

and step_let state stack v def =
  match def with
  | Fevent _
  | Fsequence _
  | Fletrec _ -> assert false

  | Flet(_, v, def, body, _) ->
      step_let' state stack v def body

  | Fsymbol _ ->
      assign_top state v

  | Fconst _ ->
      assign_other state v

  | Fvar (v', _) ->
      let r = binding state v' in
      assign state v r

  | Fprim(prim, args, _, _) ->
      let open Lambda in
      begin match prim, args with
      | Pmakeblock(_tag,mut), _ ->
          let res = Value.block v mut (Array.map var (Array.of_list args)) in
          assign_block state v res
      | Pfield i, [arg] ->
          let r = ebinding state arg in
          let res = var_union state (ValueSet.field state.heap r i) in
          assign state v res

      | Psetfield (i,_), [dst; contents] ->
          let r = ebinding state dst in
          let state =
            if ValueSet.is_top r
            then escapes state [var contents]
            else state in
          let contents = VarSet.singleton (var contents) in
          let heap = ValueSet.set_field state.heap r i contents in
          let state = { state with heap } in
          assign_other state v

      | (Pdivint | Pdivbint _ | Pstringrefs | Pstringsets), _ ->
          let state = step_raise state stack None in
          assign_other state v

      | (Pnegint | Paddint | Psubint | Pmulint | Pmodint
        | Pandint | Porint | Pxorint
        | Plslint | Plsrint | Pasrint
        | Pintcomp _ | Poffsetint _), _ ->
          iprintf "eval prim %a@." Printflambda.flambda def;
          assign_other state v

      | (Pintoffloat | Pfloatofint
        | Pnegfloat | Pabsfloat
        | Paddfloat | Psubfloat | Pmulfloat | Pdivfloat
        | Pfloatcomp _), _ ->
          iprintf "eval prim %a@." Printflambda.flambda def;
          assign_other state v


      | Poffsetref _n, [arg] ->
          let state = assign_other state (var arg) in
          assign_other state v

      | (Pbintofint _ | Pintofbint _ | Pcvtbint _ | Pnegbint _ | Paddbint _
        | Psubbint _ | Pmulbint _ | Pmodbint _ | Pandbint _
        | Porbint _ | Pxorbint _ | Plslbint _ | Plsrbint _ | Pasrbint _
        | Pbintcomp _), _ ->
          iprintf "eval bint prim@.";
          assign_other state v

      | (Pstringlength | Pstringrefu | Pstringsetu ), _ ->
          iprintf "eval string prim@.";
          assign_other state v

      | (Pisint | Pisout | Pbittest | Pnot), _ ->
          assign_other state v

      | Parraylength _, _ ->
          assign_other state v
      | Parrayrefu _, _ ->
          assign_top state v
      | Parraysetu _, [_array; _index; content]  ->
          let state = escapes state [var content] in
          assign_other state v
      | Parrayrefs _, _ ->
          let state = step_raise state stack None in
          assign_top state v
      | Parraysets _, [_array; _index; content] ->
          let state = step_raise state stack None in
          let state = escapes state [var content] in
          assign_other state v

      | (Pfloatfield _ | Psetfloatfield _), _ ->
          assign_other state v

      | Pidentity, [arg] ->
          assign state v (ebinding state arg)

      | Pgetglobal _, [] ->
          assign_top state v

      | Pgetglobalfield (id, pos), [] ->
          if Ident.same id state.k.current_unit_id
          then
            let r = global state pos in
            assign state v r
          else assign_top state v

      | Psetglobalfield pos, [arg] ->
          let r = ebinding state arg in
          let state = assign_global state pos r in
          let state = escapes state [var arg] in
          assign_other state v

      | Praise, [arg] ->
          step_raise state stack (Some arg)

      | Pccall _, args ->
          let state = step_raise state stack None in
          let state = escapes state (List.map var args) in
          assign_top state v

      | Pmakearray _, args ->
          let state = escapes state (List.map var args) in
          assign_top state v

      | (Pctconst _ | Pignore), _ ->
          assign_other state v

      | _ ->
          Format.eprintf "not implemented %a@." Printflambda.flambda def;
          assert false
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
        | Direct _ -> step_apply_direct state stack f args
        | Indirect ->
            match args with
            | [] | _::_::_ -> assert false (* ANF *)
            | [arg] -> step_apply_indirect state stack f arg
      in
      assign state v res

  | Fifthenelse (cond,ifso,ifnot,_) ->
      step_if state stack cond ifso ifnot

  | Ftrywith (body,id,handler,_) ->
      step_trywith state stack body id handler

  | Fwhile (cond,body,_) ->
      step_while state stack cond body

  | Ffor (id,lo,hi,_,body,_) ->
      step_for state stack id lo hi body

  | Fswitch (arg,sw,_) ->
      step_switch state stack arg sw

  | Fstaticcatch (sexn,vars,body,handler,_) ->
      step_staticcatch state stack sexn vars body handler

  | Fstaticraise (sexn,args,_) ->
      step_staticraise state stack sexn args

  | Fsend (_,met,obj,args,_,_) ->
      let state = step_raise state stack None in
      let state = escapes state (List.map var (met::obj::args)) in
      assign_top state v

  | Funreachable _ ->
      state

  (* | _ -> *)
  (*     Format.eprintf "not implemented %a@." Printflambda.flambda def; *)
  (*     assert false *)

and step_switch state stack arg sw =
  ignore(var arg); (* verify that it is a variables *)
  let branches =
    (List.map snd sw.fs_consts)
    @ (List.map snd sw.fs_blocks) in
  let branches = match sw.fs_failaction with
    | None -> branches
    | Some b -> b :: branches in
  List.fold_left (fun state branch -> goto_branch state stack branch)
    state branches

and step_while state stack cond body =
  let state = goto_branch_no_return state stack cond in
  let state = goto_branch_no_return state stack body in
  return_other state stack

and step_for state stack id lo hi body =
  ignore(var lo); ignore(var hi); (* verify that they are variables *)
  let state = assign_other state id in
  let state = goto_branch_no_return state stack body in
  return_other state stack

and step_staticraise state stack sexn args =
  let vars, handler = StaticExceptionMap.find sexn state.k.static_handler in
  let args = List.map (ebinding state) args in
  assert(List.length vars = List.length args);
  let state = List.fold_left2 assign state vars args in
  reached state handler

and step_staticcatch state stack sexn vars body handler =
  let state =
    { state with
      k = { state.k with
            static_handler =
              StaticExceptionMap.add sexn (vars, handler) state.k.static_handler }} in
  let state = goto_branch state stack body in
  add_stack state stack handler

and step_trywith state stack body id handler =
  let body_stack = push_stack_exn stack id handler in
  let state = goto_branch state body_stack body in
  goto_branch state stack handler

and step_raise state stack arg =
  let state =
    match arg with
    | Some arg ->
        let values = ebinding state arg in
        VarSet.fold (fun ret state -> assign state ret values)
          (StackSet.exn_return_vars stack) state
    | None ->
        VarSet.fold (fun ret state -> assign_top state ret)
          (StackSet.exn_return_vars stack) state
  in
  let state =
    CodeSet.fold (fun code state -> reached state code)
      (StackSet.exn_return_points stack) state in
  state

and step_if state stack cond ifso ifnot =
  let cond = ebinding state cond in
  if ValueSet.is_empty cond
  then state
  else
    let state = goto_branch state stack ifso in
    goto_branch state stack ifnot

and step_apply_indirect (state:state) (stack:stack) f arg =
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

and step_apply_direct (state:state) (stack:stack) f args =
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

let escape_variables state =
  let q = Queue.create () in
  let escaping = ref state.k.escape in
  VarSet.iter (fun v -> Queue.push v q) state.k.escape;

  while not (Queue.is_empty q) do
    let v = Queue.pop q in
    let value = binding state v in
    let { values = fields } = ValueSet.fields state.heap value in
    let new_escaping = VarSet.diff fields !escaping in
    escaping := VarSet.union fields !escaping;
    VarSet.iter (fun v -> Queue.push v q) new_escaping;
  done;
  { state with k = { state.k with escape = !escaping } }

let escape_functions state =
  let escape_function state ((arg, _, (other_args, code)):Value.func) =
    let state = List.fold_left assign_top state (arg :: other_args) in
    goto_branch state state.k.escape_stack code
  in
  let aux v state =
    let value = binding state v in
    let functions = ValueSet.functions value in
    let state = List.fold_left escape_function state functions.values in
    let ufunctions = ValueSet.ufunctions value in
    List.fold_left escape_function state
      (FuncSet.elements ufunctions.values)
  in
  VarSet.fold aux state.k.escape state

let step state =
  let aux code state =
    (* iprintf "step: %a@." Printflambda.flambda code; *)
    let stack = CodeMap.find code state.stacks in
    step_expr state stack code
  in
  let state = CodeSet.fold aux state.k.reached state in
  let state = escape_variables state in
  escape_functions state

let steps ~current_compilation_unit code i =
  let current_unit_id =
    Symbol.Compilation_unit.get_persistent_ident current_compilation_unit in
  let return = Variable.create ~current_compilation_unit "return" in
  let uncaught = Variable.create ~current_compilation_unit "uncaught" in
  let state = entry_point current_unit_id ~return ~uncaught code in
  let rec aux state n =
    if n <= 0
    then state
    else
      (* let () = iprintf "steps: %i@." n in *)
      let () = Format.printf "step: %i@." (i-n) in
      let st1 = Gc.quick_stat () in
      let state' = step state in
      let st2 = Gc.quick_stat () in
      let () = iprintf "escape %a@."
          VarSet.print state.k.escape in
      let () = Format.printf "minor: %f\nmajor: %f\npromoted_words: %f\ncompact:%i@."
          (st2.Gc.minor_words -. st1.Gc.minor_words)
          (st2.Gc.major_words -. st1.Gc.major_words)
          (st2.Gc.promoted_words -. st1.Gc.promoted_words)
          (st2.Gc.compactions - st1.Gc.compactions) in
      if equal_state state state'
      then
        let () = Format.printf "fixpoint: %i@." (i-n) in
        state
      else aux state' (n-1)
  in
  aux state i


let test ~current_compilation_unit expr =
  if Clflags.experiments
  then
    let expr = Flambdaanf.anf current_compilation_unit expr in
    iprintf "anf: %a@." Printflambda.flambda expr;
    ignore (steps ~current_compilation_unit expr 20)
