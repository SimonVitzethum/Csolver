	vzeroupper
	vmovdqa %ymm0, %ymm1
	vpaddd %ymm2, %ymm3, %ymm4
	movdqa %xmm0, %xmm1
	pshufd $0x1b, %xmm0, %xmm1
	pcmpeqd %xmm2, %xmm3
	pandn %xmm4, %xmm5
	popcntq %rax, %rbx
	tzcnt %rcx, %rdx
	lzcnt %rsi, %rdi
	bsr %rax, %rbx
	bswap %rax
	cmovaeq %rax, %rbx
	setne %al
	movzbl %al, %eax
	movsbq %cl, %rdx
	cqto
	cdqe
	xchg %rax, %rbx
	lock incq (%rdi)
	cmpxchg %rbx, (%rax)
	rol $3, %rax
	ror %cl, %rbx
	sar $5, %rcx
	imul $17, %rax, %rbx
	test %al, %al
	neg %rax
	not %rbx
	movabs $0x1122334455667788, %rax
