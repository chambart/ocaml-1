
Exemples
========

Simple dead code elimination
----------------------------

```ocaml
for i = 0 to 100000000 do
  let x = (1,(i,i,i,i,i,i)) in
  ignore (fst x)
done
```

<table>
<tr><td>
<pre>
	movq	$1, %rax
	cmpq	$200000001, %rax
	jg	.L100
.L101:
	movq	$3, %rbx
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
