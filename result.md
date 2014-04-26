
Recent changes:
===============

Pluggable passes (Apr 26, 2014)
----------------

It is easy to play with it to add some transformation:
Just create a flambda***.ml file

As an example (augmenting the scope of lets)

```ocaml
let lift_lets tree compilation_unit =
  let rec aux = function
    | Flet(str1,v1,Flet(str2,v2,def2,body2,d2),body1,d1) ->
        Flet(str2,v2,def2,
             aux (Flet(str1,v1,body2,body1,d1)),d2)
    | e -> e in
  Flambdaiter.map aux tree

open Flambdapasses

let lift_let_pass =
  { name = "lift lets";
    pass = lift_lets }

let () = Flambdapasses.register_pass Loop 5 lift_let_pass
```

add it to the OPTSTART variable in the Makefile before optmain.cmo (to ensure that it is linked)

```Makefile
OPTSTART=asmcomp/flambda***.cmo \
  driver/optmain.cmo \
```

Experimental passes (Apr 26, 2014)
-------------------

Experimental passes that are activated by environment variables.
It is to allow testing without passes for which I am not certain of the robustness/interest or if it make simple benchmarking harder... (when dummy for loops are eliminated)

```
export EXPERIMENTS=true
ocamlopt ...
```

Moving lets to a better position (EXPERIMENTS) (Apr 26, 2014)
--------------------------------

Lets are pushed up or down to minimize the number of computations.
It also helps a bit with cmmgen pattern matchings.

### Moving down expression

```ocaml
let f b x =
  let a = x + 1 in
  if b
  then 1
  else a
```
is rewritten to
```ocaml
let f b x =
  if b
  then 1
  else let a = x + 1 in a
```

### Moving up in loops

```ocaml
let f y =
  while true do
    let x = y + y in
    x
  done
```
is rewritten to
```ocaml
let f y =
  let x = y + y in
  while true do
    x
  done
```

Trivial stub generation (EXPERIMENTS) (Apr 26, 2014)
-----------------------

For some functions it may be worth adding a test before running it.
The code is stable, but it is not obvious when this is a benefit

For instance:

```ocaml
let rec map f = function
  | [] -> []
  | h::t -> f h :: map f t

let g x l =
  let add y = x + y in
  map add l
```
Can be rewritten to
```ocaml
let rec map' f = function
  | [] -> []
  | h::t -> f h :: map' f t

let map f = function (* annotated with stub: hence always inlined *)
  | [] -> []
  | l -> map' f l

let g x l =
  let add y = x + y in
  map add l
```

Applying others rewriting (but no lambda lifting) leads to
```ocaml
let rec map' f = function
  | [] -> []
  | h::t -> f h :: map' f t

let g x l = 
  if l == [] then []
  else
    let add y = x + y in
    map add l
```
thus avoiding the allocation of the `add` closure when the list is empty.

Exemples of generated code (Apr 19, 2014)
==========================

Simple dead code elimination
----------------------------

```ocaml
for i = 0 to 100000000 do
  let x = (1,(i,i,i,i,i,i)) in
  ignore (fst x)
done
```

In this example,

```ocaml
let x = (1,(i,i,i,i,i,i)) in
ignore (fst x)
```

is rewritten to

```ocaml
let x_1 = 1 in
let x_2 = (i,i,i,i,i,i) in
let x = (x_1,x_2) in
ignore (x_1)
```

then the dead code is eliminated

```ocaml
let x_1 = 1 in
ignore (x_1)
```

For sake of test/benchmarking ignore is volontarily not eliminated

<table>
<tr><td>
<pre>
	movq	$1, %rax
	cmpq	$200000001, %rax
	jg	.L100
.L101:
	movq	$3, %rbx # correspond to 'ignore 1'
	movq	%rax, %rbx
	addq	$2, %rax
	cmpq	$200000001, %rbx
	jne	.L101
.L100:
        ...














</pre>
</td><td>
<pre>
	movq	$1, %rbx
	cmpq	$200000001, %rbx
	jg	.L100
.L101:
	movq	$80, %rax
	call	caml_allocN@PLT
.L103:
	leaq	8(%r15), %rax
	movq	$6144, -8(%rax)
	movq	%rbx, (%rax)
	movq	%rbx, 8(%rax)
	movq	%rbx, 16(%rax)
	movq	%rbx, 24(%rax)
	movq	%rbx, 32(%rax)
	movq	%rbx, 40(%rax)
	leaq	56(%rax), %rdi
	movq	$2048, -8(%rdi)
	movq	$3, (%rdi)
	movq	%rax, 8(%rdi)
	movq	$3, %rax
	movq	%rbx, %rax
	addq	$2, %rbx
	cmpq	$200000001, %rax
	jne	.L101
.L100:
</pre>
</td></tr>
</table>

Reference elimination after inlining
------------------------------------

```ocaml
type a = { mutable x : int; mutable y : int }

let swap a =
  let y = a.y in
  a.y <- a.x;
  a.x <- y

let f x y =
  let a = { x; y } in
  swap a;
  a.x + a.y
```

after inlining, `f` becomes:

```ocaml
let f x y =
  let a = { x; y } in
  let y = a.y in
  a.y <- a.x;
  a.x <- y
  a.x + a.y
```

Reference elimination can then take place

```ocaml
let f x y =
  let a_1 = x in
  let a_2 = y in
  let y = a_2 in
  a_2 <- a_1;
  a_1 <- y
  a_1 + a_2
```

<table>
<tr><td>

<pre>
camlElim_ref__f_1031:
	.cfi_startproc
.L101:
	movq	%rbx, %rdi
	movq	%rax, %rbx
	movq	%rdi, %rax
	leaq	-1(%rax, %rbx), %rax
	ret
	.cfi_endproc



















</pre>
</td><td>
<pre>
camlElim_ref__f_1014:
	.cfi_startproc
	subq	$8, %rsp
	.cfi_adjust_cfa_offset	8
.L101:
	movq	%rax, %rdi
.L102:	subq	$24, %r15
	movq	caml_young_limit@GOTPCREL(%rip), %rax
	cmpq	(%rax), %r15
	jb	.L103
	leaq	8(%r15), %rax
	movq	$2048, -8(%rax)
	movq	%rdi, (%rax)
	movq	%rbx, 8(%rax)
	movq	8(%rax), %rbx
	movq	(%rax), %rdi
	movq	%rdi, 8(%rax)
	movq	%rbx, (%rax)
	movq	8(%rax), %rbx
	movq	(%rax), %rax
	leaq	-1(%rax, %rbx), %rax
	addq	$8, %rsp
	.cfi_adjust_cfa_offset	-8
	ret
	.cfi_adjust_cfa_offset	8
.L103:	call	caml_call_gc@PLT
.L104:	jmp	.L102
	.cfi_endproc
</pre>
</td></tr>
</table>

Recursive function inlining
---------------------------

```ocaml
let plus x acc = x + acc

let rec fold f acc = function
  | [] -> acc
  | h :: t -> fold f (f h acc) t

let truc = fold plus 0
```

`fold` can be specialised to plus here giving

```ocaml
let truc =
  let rec fold f acc = function
    | [] -> acc
    | h :: t -> fold plus (plus h acc) t in
 fold plus 0
```

Further inlined to

```ocaml
let truc =
  let rec fold f acc = function
    | [] -> acc
    | h :: t -> fold plus (h + acc) t in
 fold plus 0
```

<table>
<tr><td>
<pre>
camlFold__fold_1484:
	.cfi_startproc
.L101:
	cmpq	$1, %rdi
	je	.L100
	movq	8(%rdi), %rdx
	movq	(%rdi), %rax
	leaq	-1(%rax, %rbx), %rbx
	movq	camlFold__plus_1037_closure@GOTPCREL(%rip), %rax

# useless load of the closure of plus: there is a
# need for a complete dead code elimination pass
# (handling function parameters)

	movq	%rdx, %rdi
	jmp	.L101
	.align	4
.L100:
	movq	%rbx, %rax
	ret
	.cfi_endproc

camlFold__sum_1027:
	.cfi_startproc
.L106:
	movq	%rax, %rdi
	movq	camlFold__10@GOTPCREL(%rip), %rsi
	movq	$1, %rbx
	movq	camlFold__plus_1037_closure@GOTPCREL(%rip), %rax
	jmp	camlFold__fold_1484@PLT
	.cfi_endproc













</pre>
</td><td>
<pre>
camlFold__plus_1008:
	.cfi_startproc
.L100:
	leaq	-1(%rax, %rbx), %rax
	ret
	.cfi_endproc

camlFold__fold_1011:
	.cfi_startproc
	subq	$24, %rsp
	.cfi_adjust_cfa_offset	24
.L102:
	movq	%rax, %rsi
	cmpq	$1, %rdi
	je	.L101
	movq	%rdi, 0(%rsp)
	movq	%rsi, 8(%rsp)
	movq	(%rdi), %rax
	movq	%rsi, %rdi
	call	caml_apply2@PLT
.L103:
	movq	%rax, %rbx
	movq	0(%rsp), %rax
	movq	8(%rax), %rdi
	movq	8(%rsp), %rax
	jmp	.L102
	.align	4
.L101:
	movq	%rbx, %rax
	addq	$24, %rsp
	.cfi_adjust_cfa_offset	-24
	ret
	.cfi_adjust_cfa_offset	24
	.cfi_endproc

camlFold__sum_1016:
	.cfi_startproc
.L104:
	movq	%rax, %rdi
	movq	$1, %rbx
	movq	camlFold@GOTPCREL(%rip), %rax
	movq	(%rax), %rax
	jmp	camlFold__fold_1011@PLT
	.cfi_endproc
</pre>
</td></tr>
</table>

Inlining of function arguments
------------------------------

```ocaml
let plus (x,y) = x + y

let f g x =
  g (x,x)

let h x = f plus x
```

is inlined to

```
let h x = plus (x,x)
```

then

```
let h x =
    let b = (x,x) in
    let (x,y) = b in
    x + y
```

then simplified to

```
let h x = x + x
```


<table>
<tr><td>
<pre>
camlFun_param__h_1026:
	.cfi_startproc
.L106:
	leaq	-1(%rax, %rax), %rax
	ret
	.cfi_endproc


















</pre>
</td><td>
<pre>
camlFun_param__h_1014:
	.cfi_startproc
	subq	$8, %rsp
	.cfi_adjust_cfa_offset	8
.L105:
	movq	%rax, %rdi
	movq	camlFun_param@GOTPCREL(%rip), %rax
	movq	(%rax), %rbx
.L106:	subq	$24, %r15
	movq	caml_young_limit@GOTPCREL(%rip), %rax
	cmpq	(%rax), %r15
	jb	.L107
	leaq	8(%r15), %rax
	movq	$2048, -8(%rax)
	movq	%rdi, (%rax)
	movq	%rdi, 8(%rax)
	movq	(%rbx), %rdi
	addq	$8, %rsp
	.cfi_adjust_cfa_offset	-8
	jmp	*%rdi
	.cfi_adjust_cfa_offset	8
.L107:	call	caml_call_gc@PLT
.L108:	jmp	.L106
	.cfi_endproc
</pre>
</td></tr>
</table>



Local functions
---------------

```ocaml
let f x =
  let g y = y + x in
  g x
```

The point here is to note that after inlining, the closure of g is not
allocated anymore.

<table>
<tr><td>
<pre>
camlLoc_fun__f_1020:
	.cfi_startproc
.L100:
	leaq	-1(%rax, %rax), %rax
	ret
	.cfi_endproc



















</pre>
</td><td>
<pre>
camlLoc_fun__f_1008:
	.cfi_startproc
	subq	$8, %rsp
	.cfi_adjust_cfa_offset	8
.L101:
	movq	%rax, %rbx
.L102:	subq	$32, %r15
	movq	caml_young_limit@GOTPCREL(%rip), %rax
	cmpq	(%rax), %r15
	jb	.L103
	leaq	8(%r15), %rax
	movq	$3319, -8(%rax)
	movq	camlLoc_fun__g_1010@GOTPCREL(%rip), %rdi
	movq	%rdi, (%rax)
	movq	$3, 8(%rax)
	movq	%rbx, 16(%rax)
	movq	16(%rax), %rax
	leaq	-1(%rbx, %rax), %rax
	addq	$8, %rsp
	.cfi_adjust_cfa_offset	-8
	ret
	.cfi_adjust_cfa_offset	8
.L103:	call	caml_call_gc@PLT
.L104:	jmp	.L102
	.cfi_endproc
</pre>
</td></tr>
</table>

Match elimination
-----------------

```ocaml
let f i =
  match Some (i,(i,i)) with
  | None -> 0
  | Some (i,_) -> i + i
```

<table>
<tr><td>
<pre>
camlMatch_elim__f_1027:
	.cfi_startproc
.L100:
	addq	$2, %rax
	ret
	.cfi_endproc




































</pre>
</td><td>
<pre>
camlMatch_elim__f_1012:
	.cfi_startproc
	subq	$8, %rsp
	.cfi_adjust_cfa_offset	8
.L103:
	movq	%rax, %rbx
.L104:	subq	$16, %r15
	movq	caml_young_limit@GOTPCREL(%rip), %rax
	cmpq	(%rax), %r15
	jb	.L105
	leaq	8(%r15), %rdi
	movq	$1025, -8(%rdi)
	movq	%rbx, (%rdi)
	movzbq	-8(%rdi), %rax
	cmpq	$1, %rax
	je	.L101
	jg	.L100
.L102:
	movq	(%rdi), %rax
	addq	$8, %rsp
	.cfi_adjust_cfa_offset	-8
	ret
	.cfi_adjust_cfa_offset	8
	.align	4
.L101:
	movq	(%rdi), %rax
	addq	$2, %rax
	addq	$8, %rsp
	.cfi_adjust_cfa_offset	-8
	ret
	.cfi_adjust_cfa_offset	8
	.align	4
.L100:
	movq	(%rdi), %rax
	leaq	-1(%rax, %rax), %rax
	addq	$8, %rsp
	.cfi_adjust_cfa_offset	-8
	ret
	.cfi_adjust_cfa_offset	8
.L105:	call	caml_call_gc@PLT
.L106:	jmp	.L104
	.cfi_endproc
</pre>
</td></tr>
</table>


........
--------

```ocaml
```

<table>
<tr><td>
<pre>
</pre>
</td><td>
<pre>
</pre>
</td></tr>
</table>
