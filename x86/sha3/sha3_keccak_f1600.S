// This file is generated from a similarly-named Perl script in the BoringSSL
// source tree. Do not edit by hand.
#include "_internal_s2n_bignum.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(sha3_keccak_f1600)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(sha3_keccak_f1600)
		.text	

S2N_BN_SYMBOL(sha3_keccak_f1600):
        _CET_ENDBR

#if WINDOWS_ABI
        push    rdi
        push    rsi
        mov     rdi, rcx
        mov     rsi, rdx
#endif

        push   rbx
        push   rbp
        push   r12
        push   r13
        push   r14
        push   r15 
		
		sub    rsp, 0xd0
		
		not    QWORD PTR [rdi+0x64-0x5c]
		not    QWORD PTR [rdi+0x64-0x54]
		not    QWORD PTR [rdi+0x64-0x24]
		not    QWORD PTR [rdi+0x64-0x4]
		not    QWORD PTR [rdi+0x64+0x24]
		not    QWORD PTR [rdi+0x64+0x3c]

		lea    r15, [rsp]
		mov    rax, QWORD PTR [rdi+0x64+0x3c]
		mov    rbx, QWORD PTR [rdi+0x64+0x44]
		mov    rcx, QWORD PTR [rdi+0x64+0x4c]
		mov    rdx, QWORD PTR [rdi+0x64+0x54]
		mov    rbp, QWORD PTR [rdi+0x64+0x5c]
		mov r8, 0x0
loop_keccak:
		 mov    QWORD PTR [rsp + 0xc8], r8
	     mov    r8, QWORD PTR [rdi]
		 mov    r9, QWORD PTR [rdi+0x64-0x34]
		 mov    r10, QWORD PTR [rdi+0x64-0x4]
		 mov    r11, QWORD PTR [rdi+0x64+0x2c]
		 xor    rcx, QWORD PTR [rdi+0x64-0x54]
		 xor    rdx, QWORD PTR [rdi+0x64-0x4c]
		 xor    rax, r8
		 xor    rbx, QWORD PTR [rdi+0x64-0x5c]
		 xor    rcx, QWORD PTR [rdi+0x64-0x2c]
		 xor    rax, QWORD PTR [rdi+0x64-0x3c]
		 mov    r12, rbp
		 xor    rbp, QWORD PTR [rdi+0x64-0x44]
		 xor    rcx, r10
		 xor    rax, QWORD PTR [rdi+0x64-0x14]
		 xor    rdx, QWORD PTR [rdi+0x64-0x24]
		 xor    rbx, r9
		 xor    rbp, QWORD PTR [rdi+0x64-0x1c]
		 xor    rcx, QWORD PTR [rdi+0x64+0x24]
		 xor    rax, QWORD PTR [rdi+0x64+0x14]
		 xor    rdx, QWORD PTR [rdi+0x64+0x4]
		 xor    rbx, QWORD PTR [rdi+0x64-0xc]
		 xor    rbp, QWORD PTR [rdi+0x64+0xc]
		 mov    r13, rcx
		 rol    rcx, 1
		 xor    rcx, rax
		 xor    rdx, r11
		 rol    rax, 1
		 xor    rax, rdx
		 xor    rbx, QWORD PTR [rdi+0x64+0x1c]
		 rol    rdx, 1
		 xor    rdx, rbx
		 xor    rbp, QWORD PTR [rdi+0x64+0x34]
		 rol    rbx, 1
		 xor    rbx, rbp
		 rol    rbp, 1
		 xor    rbp, r13
		 xor    r9, rcx
		 xor    r10, rdx
		 rol    r9, 0x2c
		 xor    r11, rbp
		 xor    r12, rax
		 rol    r10, 0x2b
		 xor    r8, rbx
		 mov    r13, r9
		 rol    r11, 0x15
		 or     r9, r10
		 xor    r9, r8
		 rol    r12, 0xe
		 xor    r9, QWORD PTR [rsi]
		 mov    r14, r12
		 and    r12, r11		 
		 mov    QWORD PTR [r15], r9
		 xor    r12, r10
		 not    r10
		 mov    QWORD PTR [r15+0x64-0x54], r12
		 or     r10, r11
		 mov    r12, QWORD PTR [rdi+0x64+0x4c]
		 xor    r10, r13
		 mov    QWORD PTR [r15+0x64-0x5c], r10
		 and    r13, r8
		 mov    r9, QWORD PTR [rdi+0x64-0x1c]
		 xor    r13, r14
		 mov    r10, QWORD PTR [rdi+0x64-0x14]
		 mov    QWORD PTR [r15+0x64-0x44], r13
		 or     r14, r8
		 mov    r8, QWORD PTR [rdi+0x64-0x4c]
		 xor    r14, r11
		 mov    r11, QWORD PTR [rdi+0x64+0x1c]
		 mov    QWORD PTR [r15+0x64-0x4c], r14
		 xor    r8, rbp
		 xor    r12, rdx
		 rol    r8, 0x1c
		 xor    r11, rcx
		 xor    r9, rax
		 rol    r12, 0x3d
		 rol    r11, 0x2d
		 xor    r10, rbx
		 rol    r9, 0x14
		 mov    r13, r8
		 or     r8, r12
		 rol    r10, 0x3
		 xor    r8, r11
		 mov    QWORD PTR [r15+0x64-0x24], r8
		 mov    r14, r9
		 and    r9, r13
		 mov    r8, QWORD PTR [rdi+0x64-0x5c]
		 xor    r9, r12
		 not    r12
		 mov    QWORD PTR [r15+0x64-0x1c], r9
		 or     r12, r11
		 mov    r9, QWORD PTR [rdi+0x64-0x2c]
		 xor    r12, r10
		 mov    QWORD PTR [r15+0x64-0x2c], r12
		 and    r11, r10
		 mov    r12, QWORD PTR [rdi+0x64+0x3c]
		 xor    r11, r14
		 mov    QWORD PTR [r15+0x64-0x34], r11
		 or     r14, r10
		 mov    r10, QWORD PTR [rdi+0x64+0x4]
		 xor    r14, r13
		 mov    r11, QWORD PTR [rdi+0x64+0x34]
		 mov    QWORD PTR [r15+0x64-0x3c], r14
		 xor    r10, rbp
		 xor    r11, rax
		 rol    r10, 0x19
		 xor    r9, rdx
		 rol    r11, 0x8
		 xor    r12, rbx
		 rol    r9, 0x6
		 xor    r8, rcx
		 rol    r12, 0x12
		 mov    r13, r10
		 and    r10, r11
		 rol    r8, 1
		 not    r11
		 xor    r10, r9
		 mov    QWORD PTR [r15+0x64-0xc], r10
		 mov    r14, r12
		 and    r12, r11
		 mov    r10, QWORD PTR [rdi+0x64-0xc]
		 xor    r12, r13
		 mov    QWORD PTR [r15+0x64-0x4], r12
		 or     r13, r9
		 mov    r12, QWORD PTR [rdi+0x64+0x54]
		 xor    r13, r8
		 mov    QWORD PTR [r15+0x64-0x14], r13
		 and    r9, r8
		 xor    r9, r14
		 mov    QWORD PTR [r15+0x64+0xc], r9
		 or     r14, r8
		 mov    r9, QWORD PTR [rdi+0x64-0x3c]
		 xor    r14, r11
		 mov    r11, QWORD PTR [rdi+0x64+0x24]
		 mov    QWORD PTR [r15+0x64+0x4], r14
		 mov    r8, QWORD PTR [rdi+0x64-0x44]
		 xor    r10, rcx
		 xor    r11, rdx
		 rol    r10, 0xa
		 xor    r9, rbx
		 rol    r11, 0xf
		 xor    r12, rbp
		 rol    r9, 0x24
		 xor    r8, rax
		 rol    r12, 0x38
		 mov    r13, r10
		 or     r10, r11
		 rol    r8, 0x1b
		 not    r11
		 xor    r10, r9
		 mov    QWORD PTR [r15+0x64+0x1c], r10
		 mov    r14, r12
		 or     r12, r11
		 xor    r12, r13
		 mov    QWORD PTR [r15+0x64+0x24], r12
		 and    r13, r9
		 xor    r13, r8
		 mov    QWORD PTR [r15+0x64+0x14], r13
		 or     r9, r8
		 xor    r9, r14
		 mov    QWORD PTR [r15+0x64+0x34], r9
		 and    r8, r14
		 xor    r8, r11
		 mov    QWORD PTR [r15+0x64+0x2c], r8
		 xor    rdx, QWORD PTR [rdi+0x64-0x54]
		 xor    rbp, QWORD PTR [rdi+0x64-0x24]
		 rol    rdx, 0x3e
		 xor    rcx, QWORD PTR [rdi+0x64+0x44]
		 rol    rbp, 0x37
		 xor    rax, QWORD PTR [rdi+0x64+0xc]
		 rol    rcx, 0x2
		 xor    rbx, QWORD PTR [rdi+0x64+0x14]
		 xchg   rdi, r15
		 rol    rax, 0x27
		 rol    rbx, 0x29
		 mov    r13, rdx
		 and    rdx, rbp
		 not    rbp
		 xor    rdx, rcx
		 mov    QWORD PTR [rdi+0x64+0x5c], rdx
		 mov    r14, rax
		 and    rax, rbp
		 xor    rax, r13
		 mov    QWORD PTR [rdi+0x64+0x3c], rax
		 or     r13, rcx
		 xor    r13, rbx
		 mov    QWORD PTR [rdi+0x64+0x54], r13
		 and    rcx, rbx
		 xor    rcx, r14
		 mov    QWORD PTR [rdi+0x64+0x4c], rcx
		 or     rbx, r14
		 xor    rbx, rbp
		 mov    QWORD PTR [rdi+0x64+0x44], rbx
		 mov    rbp, rdx
		 mov    rdx, r13
		 lea    rsi, [rsi+0x8]     // Second loop
		 mov    r8, QWORD PTR [rdi]
		 mov    r9, QWORD PTR [rdi+0x64-0x34]
		 mov    r10, QWORD PTR [rdi+0x64-0x4]
		 mov    r11, QWORD PTR [rdi+0x64+0x2c]
		 xor    rcx, QWORD PTR [rdi+0x64-0x54]
		 xor    rdx, QWORD PTR [rdi+0x64-0x4c]
		 xor    rax, r8
		 xor    rbx, QWORD PTR [rdi+0x64-0x5c]
		 xor    rcx, QWORD PTR [rdi+0x64-0x2c]
		 xor    rax, QWORD PTR [rdi+0x64-0x3c]
		 mov    r12, rbp
		 xor    rbp, QWORD PTR [rdi+0x64-0x44]
		 xor    rcx, r10
		 xor    rax, QWORD PTR [rdi+0x64-0x14]
		 xor    rdx, QWORD PTR [rdi+0x64-0x24]
		 xor    rbx, r9
		 xor    rbp, QWORD PTR [rdi+0x64-0x1c]
		 xor    rcx, QWORD PTR [rdi+0x64+0x24]
		 xor    rax, QWORD PTR [rdi+0x64+0x14]
		 xor    rdx, QWORD PTR [rdi+0x64+0x4]
		 xor    rbx, QWORD PTR [rdi+0x64-0xc]
		 xor    rbp, QWORD PTR [rdi+0x64+0xc]
		 mov    r13, rcx
		 rol    rcx, 1
		 xor    rcx, rax
		 xor    rdx, r11
		 rol    rax, 1
		 xor    rax, rdx
		 xor    rbx, QWORD PTR [rdi+0x64+0x1c]
		 rol    rdx, 1
		 xor    rdx, rbx
		 xor    rbp, QWORD PTR [rdi+0x64+0x34]
		 rol    rbx, 1
		 xor    rbx, rbp
		 rol    rbp, 1
		 xor    rbp, r13
		 xor    r9, rcx
		 xor    r10, rdx
		 rol    r9, 0x2c
		 xor    r11, rbp
		 xor    r12, rax
		 rol    r10, 0x2b
		 xor    r8, rbx
		 mov    r13, r9
		 rol    r11, 0x15
		 or     r9, r10
		 xor    r9, r8
		 rol    r12, 0xe
		 xor    r9, QWORD PTR [rsi]
		 mov    r14, r12
		 and    r12, r11		 
		 mov    QWORD PTR [r15], r9
		 xor    r12, r10
		 not    r10
		 mov    QWORD PTR [r15+0x64-0x54], r12
		 or     r10, r11
		 mov    r12, QWORD PTR [rdi+0x64+0x4c]
		 xor    r10, r13
		 mov    QWORD PTR [r15+0x64-0x5c], r10
		 and    r13, r8
		 mov    r9, QWORD PTR [rdi+0x64-0x1c]
		 xor    r13, r14
		 mov    r10, QWORD PTR [rdi+0x64-0x14]
		 mov    QWORD PTR [r15+0x64-0x44], r13
		 or     r14, r8
		 mov    r8, QWORD PTR [rdi+0x64-0x4c]
		 xor    r14, r11
		 mov    r11, QWORD PTR [rdi+0x64+0x1c]
		 mov    QWORD PTR [r15+0x64-0x4c], r14
		 xor    r8, rbp
		 xor    r12, rdx
		 rol    r8, 0x1c
		 xor    r11, rcx
		 xor    r9, rax
		 rol    r12, 0x3d
		 rol    r11, 0x2d
		 xor    r10, rbx
		 rol    r9, 0x14
		 mov    r13, r8
		 or     r8, r12
		 rol    r10, 0x3
		 xor    r8, r11
		 mov    QWORD PTR [r15+0x64-0x24], r8
		 mov    r14, r9
		 and    r9, r13
		 mov    r8, QWORD PTR [rdi+0x64-0x5c]
		 xor    r9, r12
		 not    r12
		 mov    QWORD PTR [r15+0x64-0x1c], r9
		 or     r12, r11
		 mov    r9, QWORD PTR [rdi+0x64-0x2c]
		 xor    r12, r10
		 mov    QWORD PTR [r15+0x64-0x2c], r12
		 and    r11, r10
		 mov    r12, QWORD PTR [rdi+0x64+0x3c]
		 xor    r11, r14
		 mov    QWORD PTR [r15+0x64-0x34], r11
		 or     r14, r10
		 mov    r10, QWORD PTR [rdi+0x64+0x4]
		 xor    r14, r13
		 mov    r11, QWORD PTR [rdi+0x64+0x34]
		 mov    QWORD PTR [r15+0x64-0x3c], r14
		 xor    r10, rbp
		 xor    r11, rax
		 rol    r10, 0x19
		 xor    r9, rdx
		 rol    r11, 0x8
		 xor    r12, rbx
		 rol    r9, 0x6
		 xor    r8, rcx
		 rol    r12, 0x12
		 mov    r13, r10
		 and    r10, r11
		 rol    r8, 1
		 not    r11
		 xor    r10, r9
		 mov    QWORD PTR [r15+0x64-0xc], r10
		 mov    r14, r12
		 and    r12, r11
		 mov    r10, QWORD PTR [rdi+0x64-0xc]
		 xor    r12, r13
		 mov    QWORD PTR [r15+0x64-0x4], r12
		 or     r13, r9
		 mov    r12, QWORD PTR [rdi+0x64+0x54]
		 xor    r13, r8
		 mov    QWORD PTR [r15+0x64-0x14], r13
		 and    r9, r8
		 xor    r9, r14
		 mov    QWORD PTR [r15+0x64+0xc], r9
		 or     r14, r8
		 mov    r9, QWORD PTR [rdi+0x64-0x3c]
		 xor    r14, r11
		 mov    r11, QWORD PTR [rdi+0x64+0x24]
		 mov    QWORD PTR [r15+0x64+0x4], r14
		 mov    r8, QWORD PTR [rdi+0x64-0x44]
		 xor    r10, rcx
		 xor    r11, rdx
		 rol    r10, 0xa
		 xor    r9, rbx
		 rol    r11, 0xf
		 xor    r12, rbp
		 rol    r9, 0x24
		 xor    r8, rax
		 rol    r12, 0x38
		 mov    r13, r10
		 or     r10, r11
		 rol    r8, 0x1b
		 not    r11
		 xor    r10, r9
		 mov    QWORD PTR [r15+0x64+0x1c], r10
		 mov    r14, r12
		 or     r12, r11
		 xor    r12, r13
		 mov    QWORD PTR [r15+0x64+0x24], r12
		 and    r13, r9
		 xor    r13, r8
		 mov    QWORD PTR [r15+0x64+0x14], r13
		 or     r9, r8
		 xor    r9, r14
		 mov    QWORD PTR [r15+0x64+0x34], r9
		 and    r8, r14
		 xor    r8, r11
		 mov    QWORD PTR [r15+0x64+0x2c], r8
		 xor    rdx, QWORD PTR [rdi+0x64-0x54]
		 xor    rbp, QWORD PTR [rdi+0x64-0x24]
		 rol    rdx, 0x3e
		 xor    rcx, QWORD PTR [rdi+0x64+0x44]
		 rol    rbp, 0x37
		 xor    rax, QWORD PTR [rdi+0x64+0xc]
		 rol    rcx, 0x2
		 xor    rbx, QWORD PTR [rdi+0x64+0x14]
		 xchg   rdi, r15
		 rol    rax, 0x27
		 rol    rbx, 0x29
		 mov    r13, rdx
		 and    rdx, rbp
		 not    rbp
		 xor    rdx, rcx
		 mov    QWORD PTR [rdi+0x64+0x5c], rdx
		 mov    r14, rax
		 and    rax, rbp
		 xor    rax, r13
		 mov    QWORD PTR [rdi+0x64+0x3c], rax
		 or     r13, rcx
		 xor    r13, rbx
		 mov    QWORD PTR [rdi+0x64+0x54], r13
		 and    rcx, rbx
		 xor    rcx, r14
		 mov    QWORD PTR [rdi+0x64+0x4c], rcx
		 or     rbx, r14
		 xor    rbx, rbp
		 mov    QWORD PTR [rdi+0x64+0x44], rbx
		 mov    rbp, rdx
		 mov    rdx, r13
		 lea    rsi, [rsi+0x8]
		mov   r8,  QWORD PTR [rsp + 0xc8]
		add r8, 0x2
		cmp r8,  24
		jne    loop_keccak
		lea    rsi, [rsi-0xc0]
		not    QWORD PTR [rdi+0x64-0x5c]
		not    QWORD PTR [rdi+0x64-0x54]
		not    QWORD PTR [rdi+0x64-0x24]
		not    QWORD PTR [rdi+0x64-0x4]
		not    QWORD PTR [rdi+0x64+0x24]
		not    QWORD PTR [rdi+0x64+0x3c]
		add    rsp, 0xd0
		pop    r15
		pop    r14
		pop    r13
		pop    r12
		pop    rbp
		pop    rbx
		
#if WINDOWS_ABI
        pop    rsi
        pop    rdi
#endif
		retq

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,  "",  %progbits
#endif