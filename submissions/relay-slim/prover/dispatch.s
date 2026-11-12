# dispatch.s: the program's `main` (hand-written; PROVER.md §1: "detect features at run time (cpuid) and keep
# a portable fallback. A SIGILL fails the run."). It reads cpuid and XCR0, then tail-calls one variant's
# `lvm_main_<v>(argc, argv, envp)` (build-asm.sh: each `prover-<v>.s` is the whole crate built for one CPU
# level, its symbols suffixed by tools/suffix-asm.py):
#
#   v4   x86-64-v4 (AVX-512 F/BW/CD/DQ/VL, AVX2, BMI1/2, FMA, F16C, LZCNT, MOVBE; OS-enabled ZMM/opmask state)
#        + PCLMULQDQ + VPCLMULQDQ + GFNI + AVX512VBMI                       (the evaluation machine, Zen 4)
#   v4p  x86-64-v4 + PCLMULQDQ, if linked (a development build only; weak)
#   v2   x86-64-v2 (SSE3, SSSE3, SSE4.1, SSE4.2, POPCNT, CMPXCHG16B, LAHF): the portable fallback
#
# `LVM_CPU=v2|v4p|v4` in the environment forces a variant (tests; the runner sets no such variable).
# Otherwise `prover setup`'s self-test may cap the choice (WP-15a): the file `$RF_SETUP/lvm-cpu` holding `v2` or
# `v4p` (written when the faster variant failed its known-answer tests or crashed on this machine) removes the
# variants above it; the stub never picks a variant cpuid does not allow, except v4p on an x86-64-v4 CPU whose
# cpuid hides PCLMULQDQ when the self-test ran v4p there successfully (the file says `v4p`).
# A CPU below x86-64-v2 gets a message on stderr and exit status 1, never a SIGILL.
# Only baseline x86-64 instructions here.

	.text
	.globl	main
	.type	main,@function
	.p2align	4
main:
	pushq	%rbx
	pushq	%r12
	pushq	%r13
	pushq	%r14
	pushq	%r15
	movq	%rdi, %r12			# argc
	movq	%rsi, %r13			# argv
	movq	%rdx, %r14			# envp
	xorl	%r15d, %r15d			# bit 0: v2, bit 1: v4 + pclmul, bit 2: v4 fast, bit 3: v4 (cpuid)

	xorl	%eax, %eax
	xorl	%ecx, %ecx
	cpuid
	movl	%eax, %r8d			# highest basic leaf
	movl	$0x80000000, %eax
	xorl	%ecx, %ecx
	cpuid
	movl	%eax, %r9d			# highest extended leaf
	movl	$1, %eax
	xorl	%ecx, %ecx
	cpuid
	movl	%ecx, %r10d			# leaf 1 ecx
	xorl	%r11d, %r11d
	cmpl	$0x80000001, %r9d
	jb	1f
	movl	$0x80000001, %eax
	xorl	%ecx, %ecx
	cpuid
	movl	%ecx, %r11d			# leaf 0x80000001 ecx
1:	xorl	%edi, %edi
	xorl	%esi, %esi
	cmpl	$7, %r8d
	jb	2f
	movl	$7, %eax
	xorl	%ecx, %ecx
	cpuid
	movl	%ebx, %edi			# leaf 7.0 ebx
	movl	%ecx, %esi			# leaf 7.0 ecx
2:	xorl	%r8d, %r8d
	btl	$27, %r10d			# OSXSAVE: xgetbv is allowed
	jnc	3f
	xorl	%ecx, %ecx
	xgetbv
	movl	%eax, %r8d			# XCR0 (low half)
3:
	# x86-64-v2: leaf 1 ecx SSE3 0, SSSE3 9, CX16 13, SSE4.1 19, SSE4.2 20, POPCNT 23; LAHF (ext ecx 0)
	movl	%r10d, %eax
	andl	$0x00982201, %eax
	cmpl	$0x00982201, %eax
	jne	.Lfeat_done
	testl	$1, %r11d
	jz	.Lfeat_done
	orl	$1, %r15d
	# x86-64-v3: leaf 1 ecx FMA 12, MOVBE 22, XSAVE 26, OSXSAVE 27, AVX 28, F16C 29; LZCNT (ext ecx 5);
	# leaf 7 ebx BMI1 3, AVX2 5, BMI2 8; XCR0 SSE and AVX state
	movl	%r10d, %eax
	andl	$0x3C401000, %eax
	cmpl	$0x3C401000, %eax
	jne	.Lfeat_done
	testl	$0x20, %r11d
	jz	.Lfeat_done
	movl	%edi, %eax
	andl	$0x128, %eax
	cmpl	$0x128, %eax
	jne	.Lfeat_done
	movl	%r8d, %eax
	andl	$0x6, %eax
	cmpl	$0x6, %eax
	jne	.Lfeat_done
	# x86-64-v4: leaf 7 ebx AVX512F 16, DQ 17, CD 28, BW 30, VL 31; XCR0 opmask, ZMM_Hi256, Hi16_ZMM
	movl	%edi, %eax
	andl	$0xD0030000, %eax
	cmpl	$0xD0030000, %eax
	jne	.Lfeat_done
	movl	%r8d, %eax
	andl	$0xE6, %eax
	cmpl	$0xE6, %eax
	jne	.Lfeat_done
	orl	$8, %r15d			# bit 3: x86-64-v4 itself (cpuid), PCLMULQDQ aside
	# PCLMULQDQ: leaf 1 ecx 1
	testl	$2, %r10d
	jz	.Lfeat_done
	orl	$2, %r15d
	# the fast variant: leaf 7 ecx AVX512VBMI 1, GFNI 8, VPCLMULQDQ 10
	movl	%esi, %eax
	andl	$0x502, %eax
	cmpl	$0x502, %eax
	jne	.Lfeat_done
	orl	$4, %r15d
.Lfeat_done:

	# LVM_CPU=… forces a variant
	movq	%r14, %rbx
.Lenv_next:
	movq	(%rbx), %rdx
	testq	%rdx, %rdx
	jz	.Lchoose
	addq	$8, %rbx
	leaq	.Lkey(%rip), %rcx
.Lkey_cmp:
	movzbl	(%rcx), %eax
	testb	%al, %al
	jz	.Lkey_matched
	cmpb	(%rdx), %al
	jne	.Lenv_next
	incq	%rcx
	incq	%rdx
	jmp	.Lkey_cmp
.Lkey_matched:					# %rdx: the value
	cmpb	$'v', (%rdx)
	jne	.Lenv_next
	cmpb	$'2', 1(%rdx)
	jne	4f
	cmpb	$0, 2(%rdx)
	je	.Lgo_v2
	jmp	.Lenv_next
4:	cmpb	$'4', 1(%rdx)
	jne	.Lenv_next
	cmpb	$0, 2(%rdx)
	je	.Lgo_v4
	cmpb	$'p', 2(%rdx)
	jne	.Lenv_next
	cmpb	$0, 3(%rdx)
	je	.Lgo_v4p
	jmp	.Lenv_next

.Lchoose:
	# `prover setup` always runs the portable variant: it is the self-test's parent, and must not depend on
	# the variants it tests
	cmpq	$2, %r12
	jl	7f
	movq	8(%r13), %rdx
	leaq	.Lsetup(%rip), %rcx
8:	movzbl	(%rcx), %eax
	cmpb	(%rdx), %al
	jne	7f
	testb	%al, %al
	jz	.Lgo_v2
	incq	%rcx
	incq	%rdx
	jmp	8b
7:
	# RF_SETUP=…: the self-test's cap in $RF_SETUP/lvm-cpu ("v2" or "v4p"); no file, no cap
	movq	%r14, %rbx
.Lsenv_next:
	movq	(%rbx), %rdx
	testq	%rdx, %rdx
	jz	.Lsel_done
	addq	$8, %rbx
	leaq	.Lskey(%rip), %rcx
.Lskey_cmp:
	movzbl	(%rcx), %eax
	testb	%al, %al
	jz	.Lskey_matched
	cmpb	(%rdx), %al
	jne	.Lsenv_next
	incq	%rcx
	incq	%rdx
	jmp	.Lskey_cmp
.Lskey_matched:					# %rdx: the directory
	subq	$512, %rsp
	xorl	%ecx, %ecx
.Lsel_cp:
	movzbl	(%rdx,%rcx), %eax
	testb	%al, %al
	jz	.Lsel_name
	cmpl	$480, %ecx
	jae	.Lsel_pop
	movb	%al, (%rsp,%rcx)
	incl	%ecx
	jmp	.Lsel_cp
.Lsel_name:
	leaq	.Lsfile(%rip), %rsi
	xorl	%edx, %edx
.Lsel_cp2:
	movzbl	(%rsi,%rdx), %eax
	movb	%al, (%rsp,%rcx)
	incl	%ecx
	incl	%edx
	testb	%al, %al
	jnz	.Lsel_cp2
	movl	$2, %eax			# open(path, O_RDONLY)
	movq	%rsp, %rdi
	xorl	%esi, %esi
	xorl	%edx, %edx
	syscall
	testq	%rax, %rax
	js	.Lsel_pop
	movq	%rax, %r9			# fd
	movl	$0, 496(%rsp)
	xorl	%eax, %eax			# read(fd, buf, 8)
	movq	%r9, %rdi
	leaq	496(%rsp), %rsi
	movl	$8, %edx
	syscall
	movq	%rax, %r10
	movl	$3, %eax			# close(fd)
	movq	%r9, %rdi
	syscall
	cmpq	$2, %r10
	jl	.Lsel_pop
	cmpb	$'v', 496(%rsp)
	jne	.Lsel_pop
	cmpb	$'2', 497(%rsp)
	jne	6f
	andl	$1, %r15d			# cap: v2
	jmp	.Lsel_pop
6:	cmpb	$'4', 497(%rsp)
	jne	.Lsel_pop
	cmpq	$3, %r10
	jl	.Lsel_pop
	cmpb	$'p', 498(%rsp)
	jne	.Lsel_pop
	# `v4p`: the self-test ran v4p (its PCLMULQDQ kernels included) on this CPU with v2's digest. A CPU that
	# executes PCLMULQDQ while cpuid does not list it (a hypervisor hiding the bit, e.g. QEMU's dev VM) may
	# then run v4p if cpuid shows x86-64-v4 itself; the stub never picks v4p otherwise
	testl	$8, %r15d
	jz	9f
	orl	$2, %r15d
9:	andl	$3, %r15d			# cap: v4p (or v2 when v4p is not linked)
.Lsel_pop:
	addq	$512, %rsp
.Lsel_done:
	testl	$4, %r15d
	jnz	.Lgo_v4
	testl	$2, %r15d
	jz	5f
	movq	lvm_main_v4p@GOTPCREL(%rip), %rax
	testq	%rax, %rax
	jnz	.Lgo_v4p
5:	testl	$1, %r15d
	jnz	.Lgo_v2
	# below x86-64-v2: say so and exit 1
	movl	$1, %eax			# write
	movl	$2, %edi
	leaq	.Lnocpu(%rip), %rsi
	movl	$.Lnocpu_end - .Lnocpu, %edx
	syscall
	movl	$231, %eax			# exit_group
	movl	$1, %edi
	syscall
	hlt

.Lgo_v4:
	leaq	lvm_main_v4(%rip), %rax
	jmp	.Lgo
.Lgo_v4p:
	movq	lvm_main_v4p@GOTPCREL(%rip), %rax
	testq	%rax, %rax
	jz	.Lgo_v2				# not linked: the portable one
	jmp	.Lgo
.Lgo_v2:
	leaq	lvm_main_v2(%rip), %rax
.Lgo:
	movq	%r12, %rdi
	movq	%r13, %rsi
	movq	%r14, %rdx
	popq	%r15
	popq	%r14
	popq	%r13
	popq	%r12
	popq	%rbx
	jmp	*%rax
	.size	main, .-main

	.weak	lvm_main_v4p

	.section	.rodata
.Lkey:
	.asciz	"LVM_CPU="
.Lskey:
	.asciz	"RF_SETUP="
.Lsfile:
	.asciz	"/lvm-cpu"
.Lsetup:
	.asciz	"setup"
.Lnocpu:
	.ascii	"lvm-prover: this CPU is below x86-64-v2 (SSE4.2, POPCNT, CMPXCHG16B, LAHF); no variant of the prover can run\n"
.Lnocpu_end:

	.section	.note.GNU-stack,"",@progbits
