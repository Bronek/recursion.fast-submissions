	.file	"prover.c"
	.text
	.p2align 4
	.type	put_head, @function
put_head:
.LFB96:
	.cfi_startproc
	pushq	%rbp
	.cfi_def_cfa_offset 16
	.cfi_offset 6, -16
	movq	%rdx, %r10
	xorl	%edx, %edx
	movq	%rsp, %rbp
	.cfi_def_cfa_register 6
	.p2align 5
	.p2align 4
	.p2align 3
.L2:
	leal	0(,%rdx,8), %eax
	shrx	%rax, %rsi, %rax
	movb	%al, (%rdi,%rdx)
	addq	$1, %rdx
	cmpq	$8, %rdx
	jne	.L2
	vmovdqu	(%r10), %ymm0
	xorl	%edx, %edx
	vmovdqu	%ymm0, 8(%rdi)
	.p2align 5
	.p2align 4
	.p2align 3
.L3:
	leal	0(,%rdx,8), %eax
	shrx	%rax, %rcx, %rax
	movb	%al, 40(%rdi,%rdx)
	addq	$1, %rdx
	cmpq	$8, %rdx
	jne	.L3
	vmovdqu	(%r8), %ymm0
	xorl	%edx, %edx
	vmovdqu	%ymm0, 48(%rdi)
	.p2align 5
	.p2align 4
	.p2align 3
.L4:
	leal	0(,%rdx,8), %eax
	shrx	%rax, %r9, %rax
	movb	%al, 80(%rdi,%rdx)
	addq	$1, %rdx
	cmpq	$8, %rdx
	jne	.L4
	movq	16(%rbp), %rax
	movq	$1, 88(%rdi)
	vmovdqu	(%rax), %ymm0
	leaq	160(%rdi), %rax
	vmovdqu	%ymm0, 96(%rdi)
	vpxor	%xmm0, %xmm0, %xmm0
	vmovdqu	%ymm0, 128(%rdi)
	vzeroupper
	popq	%rbp
	.cfi_def_cfa 7, 8
	ret
	.cfi_endproc
.LFE96:
	.size	put_head, .-put_head
	.p2align 4
	.type	put_sig, @function
put_sig:
.LFB94:
	.cfi_startproc
	movl	(%rsi), %ecx
	movq	%rsi, %r8
	xorl	%eax, %eax
	.p2align 5
	.p2align 4
	.p2align 3
.L11:
	leal	0(,%rax,8), %edx
	shrx	%rdx, %rcx, %rdx
	movb	%dl, (%rdi,%rax)
	addq	$1, %rax
	cmpq	$8, %rax
	jne	.L11
	movq	4(%r8), %rax
	leaq	8(%rdi), %rcx
	leaq	4(%r8), %rsi
	movq	%rax, 8(%rdi)
	movq	4764(%r8), %rdx
	leaq	4776(%rdi), %rax
	addq	$16, %rdi
	movq	%rdx, 4752(%rdi)
	andq	$-8, %rdi
	subq	%rdi, %rcx
	subq	%rcx, %rsi
	addl	$4768, %ecx
	shrl	$3, %ecx
	rep movsq
	ret
	.cfi_endproc
.LFE94:
	.size	put_sig, .-put_sig
	.p2align 4
	.type	put_leaf, @function
put_leaf:
.LFB95:
	.cfi_startproc
	movq	%rsi, %r9
	movq	%rcx, %r8
	movq	%rdx, %rsi
	xorl	%eax, %eax
	movl	$48, %ecx
	.p2align 5
	.p2align 4
	.p2align 3
.L14:
	leal	0(,%rax,8), %edx
	shrx	%rdx, %rcx, %rdx
	movb	%dl, (%rdi,%rax)
	addq	$1, %rax
	cmpq	$8, %rax
	jne	.L14
	movq	$0, 8(%rdi)
	vmovdqu	(%r9), %ymm0
	xorl	%eax, %eax
	vmovdqu	%ymm0, 16(%rdi)
	.p2align 5
	.p2align 4
	.p2align 3
.L15:
	leal	0(,%rax,8), %edx
	shrx	%rdx, %rsi, %rdx
	movb	%dl, 48(%rdi,%rax)
	addq	$1, %rax
	cmpq	$8, %rax
	jne	.L15
	movq	$0, 56(%rdi)
	movq	%r8, %rsi
	addq	$64, %rdi
	vzeroupper
	jmp	put_sig
	.cfi_endproc
.LFE95:
	.size	put_leaf, .-put_leaf
	.section	.rodata.str1.1,"aMS",@progbits,1
.LC2:
	.string	"ws-leaf prover: %s\n"
	.text
	.p2align 4
	.type	die, @function
die:
.LFB83:
	.cfi_startproc
	pushq	%rax
	.cfi_def_cfa_offset 16
	popq	%rax
	.cfi_def_cfa_offset 8
	leaq	.LC2(%rip), %rdx
	movl	$2, %esi
	xorl	%eax, %eax
	subq	$8, %rsp
	.cfi_def_cfa_offset 16
	movq	%rdi, %rcx
	movq	stderr(%rip), %rdi
	call	__fprintf_chk@PLT
	movl	$1, %edi
	call	exit@PLT
	.cfi_endproc
.LFE83:
	.size	die, .-die
	.section	.rodata.str1.1
.LC3:
	.string	"out of memory"
	.text
	.p2align 4
	.type	readfile, @function
readfile:
.LFB86:
	.cfi_startproc
	pushq	%r14
	.cfi_def_cfa_offset 16
	.cfi_offset 14, -16
	xorl	%esi, %esi
	movq	%rdi, %r14
	pushq	%r13
	.cfi_def_cfa_offset 24
	.cfi_offset 13, -24
	pushq	%r12
	.cfi_def_cfa_offset 32
	.cfi_offset 12, -32
	pushq	%rbp
	.cfi_def_cfa_offset 40
	.cfi_offset 6, -40
	pushq	%rbx
	.cfi_def_cfa_offset 48
	.cfi_offset 3, -48
	subq	$176, %rsp
	.cfi_def_cfa_offset 224
	movq	%fs:40, %rax
	movq	%rax, 168(%rsp)
	xorl	%eax, %eax
	call	open@PLT
	testl	%eax, %eax
	js	.L22
	leaq	16(%rsp), %rsi
	movl	%eax, %edi
	movl	%eax, %r13d
	call	fstat@PLT
	testl	%eax, %eax
	jne	.L22
	movq	64(%rsp), %rdx
	leaq	1(%rdx), %rbp
	movq	%rdx, 8(%rsp)
	movq	%rbp, %rdi
	call	malloc@PLT
	movq	%rax, %r12
	testq	%rax, %rax
	je	.L23
	movq	8(%rsp), %rdx
	xorl	%ebx, %ebx
	testq	%rdx, %rdx
	je	.L25
	.p2align 4
	.p2align 3
.L24:
	cmpq	%rbx, %rbp
	movq	%rbx, %rcx
	leaq	(%r12,%rbx), %rsi
	movl	%r13d, %edi
	cmovnb	%rbp, %rcx
	subq	%rbx, %rdx
	subq	%rbx, %rcx
	call	__read_chk@PLT
	testq	%rax, %rax
	jle	.L22
	movq	64(%rsp), %rdx
	addq	%rax, %rbx
	cmpq	%rdx, %rbx
	jb	.L24
.L25:
	movl	%r13d, %edi
	call	close@PLT
	movb	$0, (%r12,%rbx)
	movq	%r12, %rax
	movq	%rbx, %rdx
	movq	168(%rsp), %rcx
	subq	%fs:40, %rcx
	jne	.L31
	addq	$176, %rsp
	.cfi_remember_state
	.cfi_def_cfa_offset 48
	popq	%rbx
	.cfi_def_cfa_offset 40
	popq	%rbp
	.cfi_def_cfa_offset 32
	popq	%r12
	.cfi_def_cfa_offset 24
	popq	%r13
	.cfi_def_cfa_offset 16
	popq	%r14
	.cfi_def_cfa_offset 8
	ret
.L22:
	.cfi_restore_state
	movq	%r14, %rdi
	call	die
.L31:
	call	__stack_chk_fail@PLT
.L23:
	leaq	.LC3(%rip), %rdi
	call	die
	.cfi_endproc
.LFE86:
	.size	readfile, .-readfile
	.section	.rodata.str1.1
.LC4:
	.string	"SIGN read"
	.text
	.p2align 4
	.type	read_all, @function
read_all:
.LFB92:
	.cfi_startproc
	pushq	%r13
	.cfi_def_cfa_offset 16
	.cfi_offset 13, -16
	movl	%edi, %r13d
	pushq	%r12
	.cfi_def_cfa_offset 24
	.cfi_offset 12, -24
	movq	%rsi, %r12
	pushq	%rbp
	.cfi_def_cfa_offset 32
	.cfi_offset 6, -32
	movq	%rdx, %rbp
	pushq	%rbx
	.cfi_def_cfa_offset 40
	.cfi_offset 3, -40
	xorl	%ebx, %ebx
	subq	$8, %rsp
	.cfi_def_cfa_offset 48
	.p2align 4
	.p2align 3
.L34:
	movq	%rbp, %rdx
	leaq	(%r12,%rbx), %rsi
	movl	%r13d, %edi
	subq	%rbx, %rdx
	call	read@PLT
	testq	%rax, %rax
	jle	.L37
	addq	%rax, %rbx
	cmpq	%rbp, %rbx
	jb	.L34
	addq	$8, %rsp
	.cfi_remember_state
	.cfi_def_cfa_offset 40
	popq	%rbx
	.cfi_def_cfa_offset 32
	popq	%rbp
	.cfi_def_cfa_offset 24
	popq	%r12
	.cfi_def_cfa_offset 16
	popq	%r13
	.cfi_def_cfa_offset 8
	ret
.L37:
	.cfi_restore_state
	leaq	.LC4(%rip), %rdi
	call	die
	.cfi_endproc
.LFE92:
	.size	read_all, .-read_all
	.section	.rodata.str1.1
.LC5:
	.string	"ready"
.LC6:
	.string	"go"
.LC7:
	.string	"no go"
	.text
	.p2align 4
	.type	handshake, @function
handshake:
.LFB97:
	.cfi_startproc
	subq	$88, %rsp
	.cfi_def_cfa_offset 96
	movq	%fs:40, %rdi
	movq	%rdi, 72(%rsp)
	leaq	.LC5(%rip), %rdi
	call	puts@PLT
	movq	stdout(%rip), %rdi
	call	fflush@PLT
	movq	stdin(%rip), %rdx
	movq	%rsp, %rdi
	movl	$64, %esi
	call	fgets@PLT
	testq	%rax, %rax
	je	.L39
	cmpw	$28519, (%rsp)
	je	.L50
.L39:
	leaq	.LC7(%rip), %rdi
	call	die
.L50:
	movq	72(%rsp), %rax
	subq	%fs:40, %rax
	jne	.L51
	addq	$88, %rsp
	.cfi_remember_state
	.cfi_def_cfa_offset 8
	ret
.L51:
	.cfi_restore_state
	call	__stack_chk_fail@PLT
	.cfi_endproc
.LFE97:
	.size	handshake, .-handshake
	.section	.rodata.str1.1
.LC8:
	.string	"RF_ORACLE"
.LC9:
	.string	"RF_ORACLE unset"
.LC10:
	.string	"cannot connect to the oracle"
.LC11:
	.string	"SIGN write"
	.text
	.p2align 4
	.type	sign_send, @function
sign_send:
.LFB91:
	.cfi_startproc
	pushq	%rbp
	.cfi_def_cfa_offset 16
	.cfi_offset 6, -16
	movq	%rsp, %rbp
	.cfi_def_cfa_register 6
	pushq	%r12
	pushq	%rbx
	subq	$144, %rsp
	.cfi_offset 12, -24
	.cfi_offset 3, -32
	movq	%fs:40, %rdi
	movq	%rdi, 136(%rsp)
	leaq	.LC8(%rip), %rdi
	call	getenv@PLT
	testq	%rax, %rax
	je	.L59
	movl	$1, %edx
	vpxor	%xmm0, %xmm0, %xmm0
	leaq	2(%rsp), %rdi
	movq	%rax, %rsi
	movw	%dx, (%rsp)
	movl	$107, %edx
	vmovdqu	%ymm0, 66(%rsp)
	vmovdqu	%ymm0, 2(%rsp)
	vmovdqu	%ymm0, 34(%rsp)
	vmovdqu	%xmm0, 94(%rsp)
	vzeroupper
	call	strncpy@PLT
	xorl	%edx, %edx
	movl	$1, %esi
	movl	$1, %edi
	call	socket@PLT
	movl	%eax, %ebx
	testl	%eax, %eax
	js	.L55
	movl	$110, %edx
	movq	%rsp, %rsi
	movl	%eax, %edi
	call	connect@PLT
	testl	%eax, %eax
	jne	.L55
	leaq	112(%rsp), %rsi
	movl	$16, %edx
	movl	%ebx, %edi
	movq	$2, 112(%rsp)
	movq	$0, 120(%rsp)
	call	write@PLT
	cmpq	$16, %rax
	jne	.L60
	movq	136(%rsp), %rax
	subq	%fs:40, %rax
	jne	.L61
	addq	$144, %rsp
	movl	%ebx, %eax
	popq	%rbx
	popq	%r12
	popq	%rbp
	.cfi_remember_state
	.cfi_def_cfa 7, 8
	ret
.L55:
	.cfi_restore_state
	leaq	.LC10(%rip), %rdi
	call	die
.L59:
	leaq	.LC9(%rip), %rdi
	call	die
.L61:
	call	__stack_chk_fail@PLT
.L60:
	leaq	.LC11(%rip), %rdi
	call	die
	.cfi_endproc
.LFE91:
	.size	sign_send, .-sign_send
	.section	.rodata.str1.1
.LC12:
	.string	"SIGN refused"
	.text
	.p2align 4
	.type	sign_recv, @function
sign_recv:
.LFB93:
	.cfi_startproc
	pushq	%r12
	.cfi_def_cfa_offset 16
	.cfi_offset 12, -16
	movl	$16, %edx
	pushq	%rbp
	.cfi_def_cfa_offset 24
	.cfi_offset 6, -24
	movl	%edi, %ebp
	pushq	%rbx
	.cfi_def_cfa_offset 32
	.cfi_offset 3, -32
	subq	$32, %rsp
	.cfi_def_cfa_offset 64
	movq	%fs:40, %r12
	movq	%r12, 24(%rsp)
	movq	%rsi, %r12
	movq	%rsp, %rsi
	call	read_all
	cmpb	$0, (%rsp)
	jne	.L63
	movq	%rsp, %rax
	leaq	-8(%rsp), %rsi
	xorl	%edx, %edx
	.p2align 5
	.p2align 4
	.p2align 3
.L64:
	movzbl	15(%rax), %ecx
	salq	$8, %rdx
	subq	$1, %rax
	orq	%rcx, %rdx
	cmpq	%rax, %rsi
	jne	.L64
	cmpq	$4772, %rdx
	jne	.L63
	movl	%ebp, %edi
	movl	$4772, %edx
	movq	%r12, %rsi
	call	read_all
	movl	%ebp, %edi
	call	close@PLT
	movq	24(%rsp), %rax
	subq	%fs:40, %rax
	jne	.L70
	addq	$32, %rsp
	.cfi_remember_state
	.cfi_def_cfa_offset 32
	popq	%rbx
	.cfi_def_cfa_offset 24
	popq	%rbp
	.cfi_def_cfa_offset 16
	popq	%r12
	.cfi_def_cfa_offset 8
	ret
.L63:
	.cfi_restore_state
	leaq	.LC12(%rip), %rdi
	call	die
.L70:
	call	__stack_chk_fail@PLT
	.cfi_endproc
.LFE93:
	.size	sign_recv, .-sign_recv
	.p2align 4
	.type	unhex.constprop.0, @function
unhex.constprop.0:
.LFB104:
	.cfi_startproc
	leaq	2(%rsi), %r8
	addq	$66, %rsi
	jmp	.L72
	.p2align 4,,10
	.p2align 3
.L81:
	subl	$48, %eax
.L74:
	sall	$4, %ecx
	addq	$1, %rdx
	orl	%eax, %ecx
	cmpq	%r8, %rdx
	jne	.L77
	leaq	2(%rdx), %r8
	movb	%cl, (%rdi)
	addq	$1, %rdi
	cmpq	%rsi, %r8
	je	.L79
.L72:
	leaq	-2(%r8), %rdx
	xorl	%ecx, %ecx
.L77:
	movsbl	(%rdx), %eax
	leal	-48(%rax), %r9d
	cmpb	$9, %r9b
	jbe	.L81
	leal	-97(%rax), %r9d
	cmpb	$5, %r9b
	ja	.L75
	subl	$87, %eax
	jmp	.L74
	.p2align 4,,10
	.p2align 3
.L75:
	leal	-65(%rax), %r9d
	cmpb	$5, %r9b
	ja	.L78
	subl	$55, %eax
	jmp	.L74
	.p2align 4,,10
	.p2align 3
.L79:
	xorl	%eax, %eax
	ret
.L78:
	movl	$-1, %eax
	ret
	.cfi_endproc
.LFE104:
	.size	unhex.constprop.0, .-unhex.constprop.0
	.section	.rodata.str1.1
.LC13:
	.string	"\"n\":"
.LC14:
	.string	"\"start\":"
	.text
	.p2align 4
	.type	read_chain, @function
read_chain:
.LFB89:
	.cfi_startproc
	pushq	%r14
	.cfi_def_cfa_offset 16
	.cfi_offset 14, -16
	movq	%rdx, %r14
	pushq	%r13
	.cfi_def_cfa_offset 24
	.cfi_offset 13, -24
	movq	%rsi, %r13
	pushq	%r12
	.cfi_def_cfa_offset 32
	.cfi_offset 12, -32
	movq	%rdi, %r12
	pushq	%rbp
	.cfi_def_cfa_offset 40
	.cfi_offset 6, -40
	pushq	%rbx
	.cfi_def_cfa_offset 48
	.cfi_offset 3, -48
	call	readfile
	leaq	.LC13(%rip), %rsi
	movq	%rax, %rdi
	movq	%rax, %rbp
	call	strstr@PLT
	leaq	.LC14(%rip), %rsi
	movq	%rbp, %rdi
	movq	%rax, %rbx
	call	strstr@PLT
	testq	%rbx, %rbx
	je	.L86
	testq	%rax, %rax
	je	.L86
	leaq	8(%rax), %rdi
	movl	$34, %esi
	call	strchr@PLT
	testq	%rax, %rax
	je	.L86
	leaq	1(%rax), %rsi
	movq	%r13, %rdi
	call	unhex.constprop.0
	testl	%eax, %eax
	jne	.L86
	leaq	4(%rbx), %rdi
	movl	$10, %edx
	xorl	%esi, %esi
	call	__isoc23_strtoull@PLT
	movq	%rbp, %rdi
	movq	%rax, (%r14)
	popq	%rbx
	.cfi_remember_state
	.cfi_def_cfa_offset 40
	popq	%rbp
	.cfi_def_cfa_offset 32
	popq	%r12
	.cfi_def_cfa_offset 24
	popq	%r13
	.cfi_def_cfa_offset 16
	popq	%r14
	.cfi_def_cfa_offset 8
	jmp	free@PLT
.L86:
	.cfi_restore_state
	movq	%r12, %rdi
	call	die
	.cfi_endproc
.LFE89:
	.size	read_chain, .-read_chain
	.section	.rodata.str1.1
.LC15:
	.string	"proof.bin"
	.text
	.p2align 4
	.type	emit, @function
emit:
.LFB98:
	.cfi_startproc
	pushq	%r12
	.cfi_def_cfa_offset 16
	.cfi_offset 12, -16
	xorl	%eax, %eax
	pushq	%rbp
	.cfi_def_cfa_offset 24
	.cfi_offset 6, -24
	movq	%rdi, %rbp
	pushq	%rbx
	.cfi_def_cfa_offset 32
	.cfi_offset 3, -32
	movq	%rsi, %rbx
	movq	%rdx, %rsi
	.p2align 5
	.p2align 4
	.p2align 3
.L90:
	leal	0(,%rax,8), %edx
	shrx	%rdx, %rbx, %rdx
	movb	%dl, 0(%rbp,%rax)
	addq	$1, %rax
	cmpq	$8, %rax
	jne	.L90
	movq	$0, 8(%rbp,%rbx)
	leaq	16(%rbp,%rbx), %rdi
	call	put_sig
	movl	$420, %edx
	movl	$577, %esi
	xorl	%eax, %eax
	leaq	.LC15(%rip), %rdi
	call	open@PLT
	movl	%eax, %r12d
	testl	%eax, %eax
	js	.L91
	addq	$4792, %rbx
	je	.L93
	.p2align 4
	.p2align 3
.L92:
	movq	%rbx, %rdx
	movq	%rbp, %rsi
	movl	%r12d, %edi
	call	write@PLT
	testq	%rax, %rax
	jle	.L91
	addq	%rax, %rbp
	subq	%rax, %rbx
	jne	.L92
.L93:
	movl	%r12d, %edi
	call	close@PLT
	testl	%eax, %eax
	jne	.L91
	popq	%rbx
	.cfi_remember_state
	.cfi_def_cfa_offset 24
	popq	%rbp
	.cfi_def_cfa_offset 16
	popq	%r12
	.cfi_def_cfa_offset 8
	ret
.L91:
	.cfi_restore_state
	leaq	.LC15(%rip), %rdi
	call	die
	.cfi_endproc
.LFE98:
	.size	emit, .-emit
	.section	.rodata.str1.1
.LC16:
	.string	"prev.stmt"
.LC17:
	.string	"chain.json"
.LC18:
	.string	"prev.bin"
.LC19:
	.string	"prev.bin: \317\200 not word-aligned"
.LC20:
	.string	"done"
	.text
	.p2align 4
	.type	mode_step.isra.0, @function
mode_step.isra.0:
.LFB106:
	.cfi_startproc
	pushq	%r15
	.cfi_def_cfa_offset 16
	.cfi_offset 15, -16
	pushq	%r14
	.cfi_def_cfa_offset 24
	.cfi_offset 14, -24
	pushq	%r13
	.cfi_def_cfa_offset 32
	.cfi_offset 13, -32
	pushq	%r12
	.cfi_def_cfa_offset 40
	.cfi_offset 12, -40
	pushq	%rbp
	.cfi_def_cfa_offset 48
	.cfi_offset 6, -48
	pushq	%rbx
	.cfi_def_cfa_offset 56
	.cfi_offset 3, -56
	subq	$4096, %rsp
	.cfi_def_cfa_offset 4152
	orq	$0, (%rsp)
	subq	$4096, %rsp
	.cfi_def_cfa_offset 8248
	orq	$0, (%rsp)
	subq	$1480, %rsp
	.cfi_def_cfa_offset 9728
	movq	%fs:40, %rax
	movq	%rax, 9656(%rsp)
	xorl	%eax, %eax
	call	handshake
	call	sign_send
	movl	%eax, %r15d
	call	sign_send
	leaq	.LC16(%rip), %rdi
	movl	%eax, (%rsp)
	call	readfile
	cmpq	$63, %rdx
	jbe	.L100
	leaq	32(%rsp), %r14
	movq	%rax, %rsi
	movq	%rax, %r10
	movq	%r14, %rdi
	call	unhex.constprop.0
	testl	%eax, %eax
	jne	.L100
	movq	%r10, %rdi
	leaq	64(%rsp), %r12
	call	free@PLT
	leaq	24(%rsp), %rdx
	movq	%r12, %rsi
	leaq	.LC17(%rip), %rdi
	call	read_chain
	leaq	.LC18(%rip), %rdi
	call	readfile
	movq	%rax, %r13
	movq	%rdx, %rbx
	cmpq	$7, %rdx
	jbe	.L101
	leaq	7(%rax), %rdx
	leaq	-1(%r13), %rsi
	xorl	%eax, %eax
	.p2align 5
	.p2align 4
	.p2align 3
.L102:
	movzbl	(%rdx), %ecx
	salq	$8, %rax
	subq	$1, %rdx
	orq	%rcx, %rax
	cmpq	%rdx, %rsi
	jne	.L102
	testb	$7, %al
	jne	.L101
	leaq	9792(%rbx), %rdi
	call	malloc@PLT
	movq	%rax, %rbp
	testq	%rax, %rax
	je	.L109
	leaq	96(%rsp), %r10
	movl	%r15d, %edi
	leaq	4880(%rsp), %r15
	movq	%r10, %rsi
	movq	%r10, 8(%rsp)
	call	sign_recv
	movl	(%rsp), %edi
	movq	%r15, %rsi
	call	sign_recv
	movq	24(%rsp), %r9
	subq	$8, %rsp
	.cfi_def_cfa_offset 9736
	xorl	%ecx, %ecx
	pushq	%r14
	.cfi_def_cfa_offset 9744
	movq	%r12, %r8
	leaq	8(%rbp), %rdi
	leaq	Z.0(%rip), %rdx
	movl	$2, %esi
	movq	%r9, 16(%rsp)
	call	put_head
	movq	%rbx, %rdx
	movq	%r13, %rsi
	movq	%rax, %rdi
	call	memcpy@PLT
	movq	16(%rsp), %rdx
	movq	%r15, %rcx
	movq	%r12, %rsi
	leaq	(%rax,%rbx), %rdi
	call	put_leaf
	movq	24(%rsp), %rdx
	leaq	5000(%rbx), %rsi
	movq	%rbp, %rdi
	call	emit
	leaq	.LC20(%rip), %rdi
	call	puts@PLT
	movq	stdout(%rip), %rdi
	call	fflush@PLT
	popq	%rax
	.cfi_def_cfa_offset 9736
	popq	%rdx
	.cfi_def_cfa_offset 9728
	movq	9656(%rsp), %rax
	subq	%fs:40, %rax
	jne	.L110
	addq	$9672, %rsp
	.cfi_remember_state
	.cfi_def_cfa_offset 56
	popq	%rbx
	.cfi_def_cfa_offset 48
	popq	%rbp
	.cfi_def_cfa_offset 40
	popq	%r12
	.cfi_def_cfa_offset 32
	popq	%r13
	.cfi_def_cfa_offset 24
	popq	%r14
	.cfi_def_cfa_offset 16
	popq	%r15
	.cfi_def_cfa_offset 8
	ret
.L100:
	.cfi_restore_state
	leaq	.LC16(%rip), %rdi
	call	die
.L101:
	leaq	.LC19(%rip), %rdi
	call	die
.L110:
	call	__stack_chk_fail@PLT
.L109:
	leaq	.LC3(%rip), %rdi
	call	die
	.cfi_endproc
.LFE106:
	.size	mode_step.isra.0, .-mode_step.isra.0
	.section	.rodata.str1.1
.LC21:
	.string	"chainA.json"
.LC22:
	.string	"chainB.json"
	.text
	.p2align 4
	.type	mode_first.isra.0, @function
mode_first.isra.0:
.LFB108:
	.cfi_startproc
	pushq	%r15
	.cfi_def_cfa_offset 16
	.cfi_offset 15, -16
	pushq	%r14
	.cfi_def_cfa_offset 24
	.cfi_offset 14, -24
	pushq	%r13
	.cfi_def_cfa_offset 32
	.cfi_offset 13, -32
	pushq	%r12
	.cfi_def_cfa_offset 40
	.cfi_offset 12, -40
	pushq	%rbp
	.cfi_def_cfa_offset 48
	.cfi_offset 6, -48
	pushq	%rbx
	.cfi_def_cfa_offset 56
	.cfi_offset 3, -56
	subq	$4096, %rsp
	.cfi_def_cfa_offset 4152
	orq	$0, (%rsp)
	subq	$4096, %rsp
	.cfi_def_cfa_offset 8248
	orq	$0, (%rsp)
	subq	$4096, %rsp
	.cfi_def_cfa_offset 12344
	orq	$0, (%rsp)
	subq	$2168, %rsp
	.cfi_def_cfa_offset 14512
	movq	%fs:40, %rax
	movq	%rax, 14440(%rsp)
	xorl	%eax, %eax
	leaq	32(%rsp), %r12
	leaq	64(%rsp), %rbp
	call	handshake
	call	sign_send
	movl	%eax, %r15d
	call	sign_send
	movl	%eax, %r14d
	call	sign_send
	leaq	16(%rsp), %rdx
	movq	%r12, %rsi
	leaq	.LC21(%rip), %rdi
	movl	%eax, %r13d
	call	read_chain
	leaq	.LC22(%rip), %rdi
	leaq	24(%rsp), %rdx
	movq	%rbp, %rsi
	call	read_chain
	movl	$14632, %edi
	call	malloc@PLT
	testq	%rax, %rax
	je	.L116
	leaq	96(%rsp), %r10
	movl	%r15d, %edi
	leaq	4880(%rsp), %r15
	movq	%rax, %rbx
	movq	%r10, %rsi
	movq	%r10, 8(%rsp)
	call	sign_recv
	movl	%r14d, %edi
	movq	%r15, %rsi
	leaq	9664(%rsp), %r14
	call	sign_recv
	movl	%r13d, %edi
	movq	%r14, %rsi
	call	sign_recv
	movq	24(%rsp), %r11
	movq	%rbp, %r8
	movq	%r12, %rdx
	movq	16(%rsp), %r13
	leaq	Z.1(%rip), %rax
	subq	$8, %rsp
	.cfi_def_cfa_offset 14520
	leaq	8(%rbx), %rdi
	pushq	%rax
	.cfi_def_cfa_offset 14528
	movq	%r11, %r9
	movl	$3, %esi
	movq	%r13, %rcx
	call	put_head
	movq	%r15, %rcx
	movq	%r13, %rdx
	movq	%r12, %rsi
	movq	%rax, %rdi
	call	put_leaf
	movq	%r11, %rdx
	movq	%r14, %rcx
	movq	%rbp, %rsi
	movq	%rax, %rdi
	call	put_leaf
	movq	24(%rsp), %rdx
	movl	$9840, %esi
	movq	%rbx, %rdi
	call	emit
	leaq	.LC20(%rip), %rdi
	call	puts@PLT
	movq	stdout(%rip), %rdi
	call	fflush@PLT
	popq	%rax
	.cfi_def_cfa_offset 14520
	popq	%rdx
	.cfi_def_cfa_offset 14512
	movq	14440(%rsp), %rax
	subq	%fs:40, %rax
	jne	.L117
	addq	$14456, %rsp
	.cfi_remember_state
	.cfi_def_cfa_offset 56
	popq	%rbx
	.cfi_def_cfa_offset 48
	popq	%rbp
	.cfi_def_cfa_offset 40
	popq	%r12
	.cfi_def_cfa_offset 32
	popq	%r13
	.cfi_def_cfa_offset 24
	popq	%r14
	.cfi_def_cfa_offset 16
	popq	%r15
	.cfi_def_cfa_offset 8
	ret
.L116:
	.cfi_restore_state
	leaq	.LC3(%rip), %rdi
	call	die
.L117:
	call	__stack_chk_fail@PLT
	.cfi_endproc
.LFE108:
	.size	mode_first.isra.0, .-mode_first.isra.0
	.section	.rodata.str1.8,"aMS",@progbits,1
	.align 8
.LC23:
	.string	"usage: prover setup|first|step DIR"
	.section	.rodata.str1.1
.LC24:
	.string	"cannot enter DIR"
.LC25:
	.string	"setup"
.LC26:
	.string	"first"
.LC27:
	.string	"step"
.LC28:
	.string	"unknown mode"
	.section	.text.startup,"ax",@progbits
	.p2align 4
	.globl	main
	.type	main, @function
main:
.LFB101:
	.cfi_startproc
	endbr64
	pushq	%rbx
	.cfi_def_cfa_offset 16
	.cfi_offset 3, -16
	cmpl	$3, %edi
	jne	.L128
	movq	16(%rsi), %rdi
	movq	%rsi, %rbx
	call	chdir@PLT
	testl	%eax, %eax
	jne	.L129
	movq	8(%rbx), %rbx
	leaq	.LC25(%rip), %rsi
	movq	%rbx, %rdi
	call	strcmp@PLT
	testl	%eax, %eax
	je	.L121
	leaq	.LC26(%rip), %rsi
	movq	%rbx, %rdi
	call	strcmp@PLT
	testl	%eax, %eax
	je	.L130
	leaq	.LC27(%rip), %rsi
	movq	%rbx, %rdi
	call	strcmp@PLT
	testl	%eax, %eax
	jne	.L123
	call	mode_step.isra.0
.L121:
	xorl	%eax, %eax
	popq	%rbx
	.cfi_remember_state
	.cfi_def_cfa_offset 8
	ret
.L130:
	.cfi_restore_state
	call	mode_first.isra.0
	jmp	.L121
.L128:
	leaq	.LC23(%rip), %rdi
	call	die
.L129:
	leaq	.LC24(%rip), %rdi
	call	die
.L123:
	leaq	.LC28(%rip), %rdi
	call	die
	.cfi_endproc
.LFE101:
	.size	main, .-main
	.section	.rodata
	.align 32
	.type	Z.0, @object
	.size	Z.0, 32
Z.0:
	.zero	32
	.align 32
	.type	Z.1, @object
	.size	Z.1, 32
Z.1:
	.zero	32
	.ident	"GCC: (Ubuntu 15.2.0-16ubuntu1) 15.2.0"
	.section	.note.GNU-stack,"",@progbits
	.section	.note.gnu.property,"a"
	.align 8
	.long	1f - 0f
	.long	4f - 1f
	.long	5
0:
	.string	"GNU"
1:
	.align 8
	.long	0xc0000002
	.long	3f - 2f
2:
	.long	0x3
3:
	.align 8
4:
