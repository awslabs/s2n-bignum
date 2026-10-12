// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
//
// Emitted by Ragamuffin transpiler.

// ----------------------------------------------------------------------------
// SHA-512 block compression (no SHA-NI or SIMD)
//
// extern void sha512_compress(uint64_t state[static 8],
//                                          const uint8_t *data,
//                                          size_t num_blocks);
//
// SysV: RDI = state, RSI = data, RDX = num_blocks. Win64 shim copies RCX,RDX,R8.
// ----------------------------------------------------------------------------


#include "_internal_s2n_bignum_x86_att.h"


        S2N_BN_SYM_VISIBILITY_DIRECTIVE(sha512_compress)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(sha512_compress)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(sha512_compress)
        .text

S2N_BN_SYMBOL(sha512_compress):
        CFI_START
        _CET_ENDBR

#if WINDOWS_ABI
        CFI_PUSH(%rdi)
        CFI_PUSH(%rsi)
        movq    %rcx, %rdi
        movq    %rdx, %rsi
        movq    %r8, %rdx
#endif

        mov %rsp, %rax
        CFI_PUSH(%rbx)
        CFI_PUSH(%rbp)
        CFI_PUSH(%r12)
        CFI_PUSH(%r13)
        CFI_PUSH(%r14)
        CFI_PUSH(%r15)
        shl $4, %rdx
        sub $128+32, %rsp
        lea (%rsi,%rdx,8), %rdx
        and $-64, %rsp
        mov %rdi, 128+0(%rsp)
        mov %rsi, 128+8(%rsp)
        mov %rdx, 128+16(%rsp)
        mov %rax, 152(%rsp)
#ifndef _WIN32
.cfi_escape 0x0f,0x06,0x77,0x98,0x01,0x06,0x23,0x08
#endif

Lsha512_compress_prologue:
        mov (%rdi), %rax
        mov 8(%rdi), %rbx
        mov 16(%rdi), %rcx
        mov 24(%rdi), %rdx
        mov 32(%rdi), %r8
        mov 40(%rdi), %r9
        mov 48(%rdi), %r10
        mov 56(%rdi), %r11
        jmp Lsha512_compress_loop

Lsha512_compress_loop:
        mov %rbx, %rdi
        lea K512(%rip), %rbp
        xor %rcx, %rdi
        mov (%rsi), %r12
        mov %r8, %r13
        mov %rax, %r14
        bswap %r12
        ror $23, %r13
        mov %r9, %r15
        xor %r8, %r13
        ror $5, %r14
        xor %r10, %r15
        mov %r12, (%rsp)
        xor %rax, %r14
        and %r8, %r15
        ror $4, %r13
        add %r11, %r12
        xor %r10, %r15
        ror $6, %r14
        xor %r8, %r13
        add %r15, %r12
        mov %rax, %r15
        add (%rbp), %r12
        xor %rax, %r14
        xor %rbx, %r15
        ror $14, %r13
        mov %rbx, %r11
        and %r15, %rdi
        ror $28, %r14
        add %r13, %r12
        xor %rdi, %r11
        add %r12, %rdx
        add %r12, %r11
        lea 8(%rbp), %rbp
        add %r14, %r11
        mov 8(%rsi), %r12
        mov %rdx, %r13
        mov %r11, %r14
        bswap %r12
        ror $23, %r13
        mov %r8, %rdi
        xor %rdx, %r13
        ror $5, %r14
        xor %r9, %rdi
        mov %r12, 8(%rsp)
        xor %r11, %r14
        and %rdx, %rdi
        ror $4, %r13
        add %r10, %r12
        xor %r9, %rdi
        ror $6, %r14
        xor %rdx, %r13
        add %rdi, %r12
        mov %r11, %rdi
        add (%rbp), %r12
        xor %r11, %r14
        xor %rax, %rdi
        ror $14, %r13
        mov %rax, %r10
        and %rdi, %r15
        ror $28, %r14
        add %r13, %r12
        xor %r15, %r10
        add %r12, %rcx
        add %r12, %r10
        lea 24(%rbp), %rbp
        add %r14, %r10
        mov 16(%rsi), %r12
        mov %rcx, %r13
        mov %r10, %r14
        bswap %r12
        ror $23, %r13
        mov %rdx, %r15
        xor %rcx, %r13
        ror $5, %r14
        xor %r8, %r15
        mov %r12, 16(%rsp)
        xor %r10, %r14
        and %rcx, %r15
        ror $4, %r13
        add %r9, %r12
        xor %r8, %r15
        ror $6, %r14
        xor %rcx, %r13
        add %r15, %r12
        mov %r10, %r15
        add (%rbp), %r12
        xor %r10, %r14
        xor %r11, %r15
        ror $14, %r13
        mov %r11, %r9
        and %r15, %rdi
        ror $28, %r14
        add %r13, %r12
        xor %rdi, %r9
        add %r12, %rbx
        add %r12, %r9
        lea 8(%rbp), %rbp
        add %r14, %r9
        mov 24(%rsi), %r12
        mov %rbx, %r13
        mov %r9, %r14
        bswap %r12
        ror $23, %r13
        mov %rcx, %rdi
        xor %rbx, %r13
        ror $5, %r14
        xor %rdx, %rdi
        mov %r12, 24(%rsp)
        xor %r9, %r14
        and %rbx, %rdi
        ror $4, %r13
        add %r8, %r12
        xor %rdx, %rdi
        ror $6, %r14
        xor %rbx, %r13
        add %rdi, %r12
        mov %r9, %rdi
        add (%rbp), %r12
        xor %r9, %r14
        xor %r10, %rdi
        ror $14, %r13
        mov %r10, %r8
        and %rdi, %r15
        ror $28, %r14
        add %r13, %r12
        xor %r15, %r8
        add %r12, %rax
        add %r12, %r8
        lea 24(%rbp), %rbp
        add %r14, %r8
        mov 32(%rsi), %r12
        mov %rax, %r13
        mov %r8, %r14
        bswap %r12
        ror $23, %r13
        mov %rbx, %r15
        xor %rax, %r13
        ror $5, %r14
        xor %rcx, %r15
        mov %r12, 32(%rsp)
        xor %r8, %r14
        and %rax, %r15
        ror $4, %r13
        add %rdx, %r12
        xor %rcx, %r15
        ror $6, %r14
        xor %rax, %r13
        add %r15, %r12
        mov %r8, %r15
        add (%rbp), %r12
        xor %r8, %r14
        xor %r9, %r15
        ror $14, %r13
        mov %r9, %rdx
        and %r15, %rdi
        ror $28, %r14
        add %r13, %r12
        xor %rdi, %rdx
        add %r12, %r11
        add %r12, %rdx
        lea 8(%rbp), %rbp
        add %r14, %rdx
        mov 40(%rsi), %r12
        mov %r11, %r13
        mov %rdx, %r14
        bswap %r12
        ror $23, %r13
        mov %rax, %rdi
        xor %r11, %r13
        ror $5, %r14
        xor %rbx, %rdi
        mov %r12, 40(%rsp)
        xor %rdx, %r14
        and %r11, %rdi
        ror $4, %r13
        add %rcx, %r12
        xor %rbx, %rdi
        ror $6, %r14
        xor %r11, %r13
        add %rdi, %r12
        mov %rdx, %rdi
        add (%rbp), %r12
        xor %rdx, %r14
        xor %r8, %rdi
        ror $14, %r13
        mov %r8, %rcx
        and %rdi, %r15
        ror $28, %r14
        add %r13, %r12
        xor %r15, %rcx
        add %r12, %r10
        add %r12, %rcx
        lea 24(%rbp), %rbp
        add %r14, %rcx
        mov 48(%rsi), %r12
        mov %r10, %r13
        mov %rcx, %r14
        bswap %r12
        ror $23, %r13
        mov %r11, %r15
        xor %r10, %r13
        ror $5, %r14
        xor %rax, %r15
        mov %r12, 48(%rsp)
        xor %rcx, %r14
        and %r10, %r15
        ror $4, %r13
        add %rbx, %r12
        xor %rax, %r15
        ror $6, %r14
        xor %r10, %r13
        add %r15, %r12
        mov %rcx, %r15
        add (%rbp), %r12
        xor %rcx, %r14
        xor %rdx, %r15
        ror $14, %r13
        mov %rdx, %rbx
        and %r15, %rdi
        ror $28, %r14
        add %r13, %r12
        xor %rdi, %rbx
        add %r12, %r9
        add %r12, %rbx
        lea 8(%rbp), %rbp
        add %r14, %rbx
        mov 56(%rsi), %r12
        mov %r9, %r13
        mov %rbx, %r14
        bswap %r12
        ror $23, %r13
        mov %r10, %rdi
        xor %r9, %r13
        ror $5, %r14
        xor %r11, %rdi
        mov %r12, 56(%rsp)
        xor %rbx, %r14
        and %r9, %rdi
        ror $4, %r13
        add %rax, %r12
        xor %r11, %rdi
        ror $6, %r14
        xor %r9, %r13
        add %rdi, %r12
        mov %rbx, %rdi
        add (%rbp), %r12
        xor %rbx, %r14
        xor %rcx, %rdi
        ror $14, %r13
        mov %rcx, %rax
        and %rdi, %r15
        ror $28, %r14
        add %r13, %r12
        xor %r15, %rax
        add %r12, %r8
        add %r12, %rax
        lea 24(%rbp), %rbp
        add %r14, %rax
        mov 64(%rsi), %r12
        mov %r8, %r13
        mov %rax, %r14
        bswap %r12
        ror $23, %r13
        mov %r9, %r15
        xor %r8, %r13
        ror $5, %r14
        xor %r10, %r15
        mov %r12, 64(%rsp)
        xor %rax, %r14
        and %r8, %r15
        ror $4, %r13
        add %r11, %r12
        xor %r10, %r15
        ror $6, %r14
        xor %r8, %r13
        add %r15, %r12
        mov %rax, %r15
        add (%rbp), %r12
        xor %rax, %r14
        xor %rbx, %r15
        ror $14, %r13
        mov %rbx, %r11
        and %r15, %rdi
        ror $28, %r14
        add %r13, %r12
        xor %rdi, %r11
        add %r12, %rdx
        add %r12, %r11
        lea 8(%rbp), %rbp
        add %r14, %r11
        mov 72(%rsi), %r12
        mov %rdx, %r13
        mov %r11, %r14
        bswap %r12
        ror $23, %r13
        mov %r8, %rdi
        xor %rdx, %r13
        ror $5, %r14
        xor %r9, %rdi
        mov %r12, 72(%rsp)
        xor %r11, %r14
        and %rdx, %rdi
        ror $4, %r13
        add %r10, %r12
        xor %r9, %rdi
        ror $6, %r14
        xor %rdx, %r13
        add %rdi, %r12
        mov %r11, %rdi
        add (%rbp), %r12
        xor %r11, %r14
        xor %rax, %rdi
        ror $14, %r13
        mov %rax, %r10
        and %rdi, %r15
        ror $28, %r14
        add %r13, %r12
        xor %r15, %r10
        add %r12, %rcx
        add %r12, %r10
        lea 24(%rbp), %rbp
        add %r14, %r10
        mov 80(%rsi), %r12
        mov %rcx, %r13
        mov %r10, %r14
        bswap %r12
        ror $23, %r13
        mov %rdx, %r15
        xor %rcx, %r13
        ror $5, %r14
        xor %r8, %r15
        mov %r12, 80(%rsp)
        xor %r10, %r14
        and %rcx, %r15
        ror $4, %r13
        add %r9, %r12
        xor %r8, %r15
        ror $6, %r14
        xor %rcx, %r13
        add %r15, %r12
        mov %r10, %r15
        add (%rbp), %r12
        xor %r10, %r14
        xor %r11, %r15
        ror $14, %r13
        mov %r11, %r9
        and %r15, %rdi
        ror $28, %r14
        add %r13, %r12
        xor %rdi, %r9
        add %r12, %rbx
        add %r12, %r9
        lea 8(%rbp), %rbp
        add %r14, %r9
        mov 88(%rsi), %r12
        mov %rbx, %r13
        mov %r9, %r14
        bswap %r12
        ror $23, %r13
        mov %rcx, %rdi
        xor %rbx, %r13
        ror $5, %r14
        xor %rdx, %rdi
        mov %r12, 88(%rsp)
        xor %r9, %r14
        and %rbx, %rdi
        ror $4, %r13
        add %r8, %r12
        xor %rdx, %rdi
        ror $6, %r14
        xor %rbx, %r13
        add %rdi, %r12
        mov %r9, %rdi
        add (%rbp), %r12
        xor %r9, %r14
        xor %r10, %rdi
        ror $14, %r13
        mov %r10, %r8
        and %rdi, %r15
        ror $28, %r14
        add %r13, %r12
        xor %r15, %r8
        add %r12, %rax
        add %r12, %r8
        lea 24(%rbp), %rbp
        add %r14, %r8
        mov 96(%rsi), %r12
        mov %rax, %r13
        mov %r8, %r14
        bswap %r12
        ror $23, %r13
        mov %rbx, %r15
        xor %rax, %r13
        ror $5, %r14
        xor %rcx, %r15
        mov %r12, 96(%rsp)
        xor %r8, %r14
        and %rax, %r15
        ror $4, %r13
        add %rdx, %r12
        xor %rcx, %r15
        ror $6, %r14
        xor %rax, %r13
        add %r15, %r12
        mov %r8, %r15
        add (%rbp), %r12
        xor %r8, %r14
        xor %r9, %r15
        ror $14, %r13
        mov %r9, %rdx
        and %r15, %rdi
        ror $28, %r14
        add %r13, %r12
        xor %rdi, %rdx
        add %r12, %r11
        add %r12, %rdx
        lea 8(%rbp), %rbp
        add %r14, %rdx
        mov 104(%rsi), %r12
        mov %r11, %r13
        mov %rdx, %r14
        bswap %r12
        ror $23, %r13
        mov %rax, %rdi
        xor %r11, %r13
        ror $5, %r14
        xor %rbx, %rdi
        mov %r12, 104(%rsp)
        xor %rdx, %r14
        and %r11, %rdi
        ror $4, %r13
        add %rcx, %r12
        xor %rbx, %rdi
        ror $6, %r14
        xor %r11, %r13
        add %rdi, %r12
        mov %rdx, %rdi
        add (%rbp), %r12
        xor %rdx, %r14
        xor %r8, %rdi
        ror $14, %r13
        mov %r8, %rcx
        and %rdi, %r15
        ror $28, %r14
        add %r13, %r12
        xor %r15, %rcx
        add %r12, %r10
        add %r12, %rcx
        lea 24(%rbp), %rbp
        add %r14, %rcx
        mov 112(%rsi), %r12
        mov %r10, %r13
        mov %rcx, %r14
        bswap %r12
        ror $23, %r13
        mov %r11, %r15
        xor %r10, %r13
        ror $5, %r14
        xor %rax, %r15
        mov %r12, 112(%rsp)
        xor %rcx, %r14
        and %r10, %r15
        ror $4, %r13
        add %rbx, %r12
        xor %rax, %r15
        ror $6, %r14
        xor %r10, %r13
        add %r15, %r12
        mov %rcx, %r15
        add (%rbp), %r12
        xor %rcx, %r14
        xor %rdx, %r15
        ror $14, %r13
        mov %rdx, %rbx
        and %r15, %rdi
        ror $28, %r14
        add %r13, %r12
        xor %rdi, %rbx
        add %r12, %r9
        add %r12, %rbx
        lea 8(%rbp), %rbp
        add %r14, %rbx
        mov 120(%rsi), %r12
        mov %r9, %r13
        mov %rbx, %r14
        bswap %r12
        ror $23, %r13
        mov %r10, %rdi
        xor %r9, %r13
        ror $5, %r14
        xor %r11, %rdi
        mov %r12, 120(%rsp)
        xor %rbx, %r14
        and %r9, %rdi
        ror $4, %r13
        add %rax, %r12
        xor %r11, %rdi
        ror $6, %r14
        xor %r9, %r13
        add %rdi, %r12
        mov %rbx, %rdi
        add (%rbp), %r12
        xor %rbx, %r14
        xor %rcx, %rdi
        ror $14, %r13
        mov %rcx, %rax
        and %rdi, %r15
        ror $28, %r14
        add %r13, %r12
        xor %r15, %rax
        add %r12, %r8
        add %r12, %rax
        lea 24(%rbp), %rbp
        jmp Lsha512_compress_rounds_16_xx

Lsha512_compress_rounds_16_xx:
        mov 8(%rsp), %r13
        mov 112(%rsp), %r15
        mov %r13, %r12
        ror $7, %r13
        add %r14, %rax
        mov %r15, %r14
        ror $42, %r15
        xor %r12, %r13
        shr $7, %r12
        ror $1, %r13
        xor %r14, %r15
        shr $6, %r14
        ror $19, %r15
        xor %r13, %r12
        xor %r14, %r15
        add 72(%rsp), %r12
        add (%rsp), %r12
        mov %r8, %r13
        add %r15, %r12
        mov %rax, %r14
        ror $23, %r13
        mov %r9, %r15
        xor %r8, %r13
        ror $5, %r14
        xor %r10, %r15
        mov %r12, (%rsp)
        xor %rax, %r14
        and %r8, %r15
        ror $4, %r13
        add %r11, %r12
        xor %r10, %r15
        ror $6, %r14
        xor %r8, %r13
        add %r15, %r12
        mov %rax, %r15
        add (%rbp), %r12
        xor %rax, %r14
        xor %rbx, %r15
        ror $14, %r13
        mov %rbx, %r11
        and %r15, %rdi
        ror $28, %r14
        add %r13, %r12
        xor %rdi, %r11
        add %r12, %rdx
        add %r12, %r11
        lea 8(%rbp), %rbp
        mov 16(%rsp), %r13
        mov 120(%rsp), %rdi
        mov %r13, %r12
        ror $7, %r13
        add %r14, %r11
        mov %rdi, %r14
        ror $42, %rdi
        xor %r12, %r13
        shr $7, %r12
        ror $1, %r13
        xor %r14, %rdi
        shr $6, %r14
        ror $19, %rdi
        xor %r13, %r12
        xor %r14, %rdi
        add 80(%rsp), %r12
        add 8(%rsp), %r12
        mov %rdx, %r13
        add %rdi, %r12
        mov %r11, %r14
        ror $23, %r13
        mov %r8, %rdi
        xor %rdx, %r13
        ror $5, %r14
        xor %r9, %rdi
        mov %r12, 8(%rsp)
        xor %r11, %r14
        and %rdx, %rdi
        ror $4, %r13
        add %r10, %r12
        xor %r9, %rdi
        ror $6, %r14
        xor %rdx, %r13
        add %rdi, %r12
        mov %r11, %rdi
        add (%rbp), %r12
        xor %r11, %r14
        xor %rax, %rdi
        ror $14, %r13
        mov %rax, %r10
        and %rdi, %r15
        ror $28, %r14
        add %r13, %r12
        xor %r15, %r10
        add %r12, %rcx
        add %r12, %r10
        lea 24(%rbp), %rbp
        mov 24(%rsp), %r13
        mov (%rsp), %r15
        mov %r13, %r12
        ror $7, %r13
        add %r14, %r10
        mov %r15, %r14
        ror $42, %r15
        xor %r12, %r13
        shr $7, %r12
        ror $1, %r13
        xor %r14, %r15
        shr $6, %r14
        ror $19, %r15
        xor %r13, %r12
        xor %r14, %r15
        add 88(%rsp), %r12
        add 16(%rsp), %r12
        mov %rcx, %r13
        add %r15, %r12
        mov %r10, %r14
        ror $23, %r13
        mov %rdx, %r15
        xor %rcx, %r13
        ror $5, %r14
        xor %r8, %r15
        mov %r12, 16(%rsp)
        xor %r10, %r14
        and %rcx, %r15
        ror $4, %r13
        add %r9, %r12
        xor %r8, %r15
        ror $6, %r14
        xor %rcx, %r13
        add %r15, %r12
        mov %r10, %r15
        add (%rbp), %r12
        xor %r10, %r14
        xor %r11, %r15
        ror $14, %r13
        mov %r11, %r9
        and %r15, %rdi
        ror $28, %r14
        add %r13, %r12
        xor %rdi, %r9
        add %r12, %rbx
        add %r12, %r9
        lea 8(%rbp), %rbp
        mov 32(%rsp), %r13
        mov 8(%rsp), %rdi
        mov %r13, %r12
        ror $7, %r13
        add %r14, %r9
        mov %rdi, %r14
        ror $42, %rdi
        xor %r12, %r13
        shr $7, %r12
        ror $1, %r13
        xor %r14, %rdi
        shr $6, %r14
        ror $19, %rdi
        xor %r13, %r12
        xor %r14, %rdi
        add 96(%rsp), %r12
        add 24(%rsp), %r12
        mov %rbx, %r13
        add %rdi, %r12
        mov %r9, %r14
        ror $23, %r13
        mov %rcx, %rdi
        xor %rbx, %r13
        ror $5, %r14
        xor %rdx, %rdi
        mov %r12, 24(%rsp)
        xor %r9, %r14
        and %rbx, %rdi
        ror $4, %r13
        add %r8, %r12
        xor %rdx, %rdi
        ror $6, %r14
        xor %rbx, %r13
        add %rdi, %r12
        mov %r9, %rdi
        add (%rbp), %r12
        xor %r9, %r14
        xor %r10, %rdi
        ror $14, %r13
        mov %r10, %r8
        and %rdi, %r15
        ror $28, %r14
        add %r13, %r12
        xor %r15, %r8
        add %r12, %rax
        add %r12, %r8
        lea 24(%rbp), %rbp
        mov 40(%rsp), %r13
        mov 16(%rsp), %r15
        mov %r13, %r12
        ror $7, %r13
        add %r14, %r8
        mov %r15, %r14
        ror $42, %r15
        xor %r12, %r13
        shr $7, %r12
        ror $1, %r13
        xor %r14, %r15
        shr $6, %r14
        ror $19, %r15
        xor %r13, %r12
        xor %r14, %r15
        add 104(%rsp), %r12
        add 32(%rsp), %r12
        mov %rax, %r13
        add %r15, %r12
        mov %r8, %r14
        ror $23, %r13
        mov %rbx, %r15
        xor %rax, %r13
        ror $5, %r14
        xor %rcx, %r15
        mov %r12, 32(%rsp)
        xor %r8, %r14
        and %rax, %r15
        ror $4, %r13
        add %rdx, %r12
        xor %rcx, %r15
        ror $6, %r14
        xor %rax, %r13
        add %r15, %r12
        mov %r8, %r15
        add (%rbp), %r12
        xor %r8, %r14
        xor %r9, %r15
        ror $14, %r13
        mov %r9, %rdx
        and %r15, %rdi
        ror $28, %r14
        add %r13, %r12
        xor %rdi, %rdx
        add %r12, %r11
        add %r12, %rdx
        lea 8(%rbp), %rbp
        mov 48(%rsp), %r13
        mov 24(%rsp), %rdi
        mov %r13, %r12
        ror $7, %r13
        add %r14, %rdx
        mov %rdi, %r14
        ror $42, %rdi
        xor %r12, %r13
        shr $7, %r12
        ror $1, %r13
        xor %r14, %rdi
        shr $6, %r14
        ror $19, %rdi
        xor %r13, %r12
        xor %r14, %rdi
        add 112(%rsp), %r12
        add 40(%rsp), %r12
        mov %r11, %r13
        add %rdi, %r12
        mov %rdx, %r14
        ror $23, %r13
        mov %rax, %rdi
        xor %r11, %r13
        ror $5, %r14
        xor %rbx, %rdi
        mov %r12, 40(%rsp)
        xor %rdx, %r14
        and %r11, %rdi
        ror $4, %r13
        add %rcx, %r12
        xor %rbx, %rdi
        ror $6, %r14
        xor %r11, %r13
        add %rdi, %r12
        mov %rdx, %rdi
        add (%rbp), %r12
        xor %rdx, %r14
        xor %r8, %rdi
        ror $14, %r13
        mov %r8, %rcx
        and %rdi, %r15
        ror $28, %r14
        add %r13, %r12
        xor %r15, %rcx
        add %r12, %r10
        add %r12, %rcx
        lea 24(%rbp), %rbp
        mov 56(%rsp), %r13
        mov 32(%rsp), %r15
        mov %r13, %r12
        ror $7, %r13
        add %r14, %rcx
        mov %r15, %r14
        ror $42, %r15
        xor %r12, %r13
        shr $7, %r12
        ror $1, %r13
        xor %r14, %r15
        shr $6, %r14
        ror $19, %r15
        xor %r13, %r12
        xor %r14, %r15
        add 120(%rsp), %r12
        add 48(%rsp), %r12
        mov %r10, %r13
        add %r15, %r12
        mov %rcx, %r14
        ror $23, %r13
        mov %r11, %r15
        xor %r10, %r13
        ror $5, %r14
        xor %rax, %r15
        mov %r12, 48(%rsp)
        xor %rcx, %r14
        and %r10, %r15
        ror $4, %r13
        add %rbx, %r12
        xor %rax, %r15
        ror $6, %r14
        xor %r10, %r13
        add %r15, %r12
        mov %rcx, %r15
        add (%rbp), %r12
        xor %rcx, %r14
        xor %rdx, %r15
        ror $14, %r13
        mov %rdx, %rbx
        and %r15, %rdi
        ror $28, %r14
        add %r13, %r12
        xor %rdi, %rbx
        add %r12, %r9
        add %r12, %rbx
        lea 8(%rbp), %rbp
        mov 64(%rsp), %r13
        mov 40(%rsp), %rdi
        mov %r13, %r12
        ror $7, %r13
        add %r14, %rbx
        mov %rdi, %r14
        ror $42, %rdi
        xor %r12, %r13
        shr $7, %r12
        ror $1, %r13
        xor %r14, %rdi
        shr $6, %r14
        ror $19, %rdi
        xor %r13, %r12
        xor %r14, %rdi
        add (%rsp), %r12
        add 56(%rsp), %r12
        mov %r9, %r13
        add %rdi, %r12
        mov %rbx, %r14
        ror $23, %r13
        mov %r10, %rdi
        xor %r9, %r13
        ror $5, %r14
        xor %r11, %rdi
        mov %r12, 56(%rsp)
        xor %rbx, %r14
        and %r9, %rdi
        ror $4, %r13
        add %rax, %r12
        xor %r11, %rdi
        ror $6, %r14
        xor %r9, %r13
        add %rdi, %r12
        mov %rbx, %rdi
        add (%rbp), %r12
        xor %rbx, %r14
        xor %rcx, %rdi
        ror $14, %r13
        mov %rcx, %rax
        and %rdi, %r15
        ror $28, %r14
        add %r13, %r12
        xor %r15, %rax
        add %r12, %r8
        add %r12, %rax
        lea 24(%rbp), %rbp
        mov 72(%rsp), %r13
        mov 48(%rsp), %r15
        mov %r13, %r12
        ror $7, %r13
        add %r14, %rax
        mov %r15, %r14
        ror $42, %r15
        xor %r12, %r13
        shr $7, %r12
        ror $1, %r13
        xor %r14, %r15
        shr $6, %r14
        ror $19, %r15
        xor %r13, %r12
        xor %r14, %r15
        add 8(%rsp), %r12
        add 64(%rsp), %r12
        mov %r8, %r13
        add %r15, %r12
        mov %rax, %r14
        ror $23, %r13
        mov %r9, %r15
        xor %r8, %r13
        ror $5, %r14
        xor %r10, %r15
        mov %r12, 64(%rsp)
        xor %rax, %r14
        and %r8, %r15
        ror $4, %r13
        add %r11, %r12
        xor %r10, %r15
        ror $6, %r14
        xor %r8, %r13
        add %r15, %r12
        mov %rax, %r15
        add (%rbp), %r12
        xor %rax, %r14
        xor %rbx, %r15
        ror $14, %r13
        mov %rbx, %r11
        and %r15, %rdi
        ror $28, %r14
        add %r13, %r12
        xor %rdi, %r11
        add %r12, %rdx
        add %r12, %r11
        lea 8(%rbp), %rbp
        mov 80(%rsp), %r13
        mov 56(%rsp), %rdi
        mov %r13, %r12
        ror $7, %r13
        add %r14, %r11
        mov %rdi, %r14
        ror $42, %rdi
        xor %r12, %r13
        shr $7, %r12
        ror $1, %r13
        xor %r14, %rdi
        shr $6, %r14
        ror $19, %rdi
        xor %r13, %r12
        xor %r14, %rdi
        add 16(%rsp), %r12
        add 72(%rsp), %r12
        mov %rdx, %r13
        add %rdi, %r12
        mov %r11, %r14
        ror $23, %r13
        mov %r8, %rdi
        xor %rdx, %r13
        ror $5, %r14
        xor %r9, %rdi
        mov %r12, 72(%rsp)
        xor %r11, %r14
        and %rdx, %rdi
        ror $4, %r13
        add %r10, %r12
        xor %r9, %rdi
        ror $6, %r14
        xor %rdx, %r13
        add %rdi, %r12
        mov %r11, %rdi
        add (%rbp), %r12
        xor %r11, %r14
        xor %rax, %rdi
        ror $14, %r13
        mov %rax, %r10
        and %rdi, %r15
        ror $28, %r14
        add %r13, %r12
        xor %r15, %r10
        add %r12, %rcx
        add %r12, %r10
        lea 24(%rbp), %rbp
        mov 88(%rsp), %r13
        mov 64(%rsp), %r15
        mov %r13, %r12
        ror $7, %r13
        add %r14, %r10
        mov %r15, %r14
        ror $42, %r15
        xor %r12, %r13
        shr $7, %r12
        ror $1, %r13
        xor %r14, %r15
        shr $6, %r14
        ror $19, %r15
        xor %r13, %r12
        xor %r14, %r15
        add 24(%rsp), %r12
        add 80(%rsp), %r12
        mov %rcx, %r13
        add %r15, %r12
        mov %r10, %r14
        ror $23, %r13
        mov %rdx, %r15
        xor %rcx, %r13
        ror $5, %r14
        xor %r8, %r15
        mov %r12, 80(%rsp)
        xor %r10, %r14
        and %rcx, %r15
        ror $4, %r13
        add %r9, %r12
        xor %r8, %r15
        ror $6, %r14
        xor %rcx, %r13
        add %r15, %r12
        mov %r10, %r15
        add (%rbp), %r12
        xor %r10, %r14
        xor %r11, %r15
        ror $14, %r13
        mov %r11, %r9
        and %r15, %rdi
        ror $28, %r14
        add %r13, %r12
        xor %rdi, %r9
        add %r12, %rbx
        add %r12, %r9
        lea 8(%rbp), %rbp
        mov 96(%rsp), %r13
        mov 72(%rsp), %rdi
        mov %r13, %r12
        ror $7, %r13
        add %r14, %r9
        mov %rdi, %r14
        ror $42, %rdi
        xor %r12, %r13
        shr $7, %r12
        ror $1, %r13
        xor %r14, %rdi
        shr $6, %r14
        ror $19, %rdi
        xor %r13, %r12
        xor %r14, %rdi
        add 32(%rsp), %r12
        add 88(%rsp), %r12
        mov %rbx, %r13
        add %rdi, %r12
        mov %r9, %r14
        ror $23, %r13
        mov %rcx, %rdi
        xor %rbx, %r13
        ror $5, %r14
        xor %rdx, %rdi
        mov %r12, 88(%rsp)
        xor %r9, %r14
        and %rbx, %rdi
        ror $4, %r13
        add %r8, %r12
        xor %rdx, %rdi
        ror $6, %r14
        xor %rbx, %r13
        add %rdi, %r12
        mov %r9, %rdi
        add (%rbp), %r12
        xor %r9, %r14
        xor %r10, %rdi
        ror $14, %r13
        mov %r10, %r8
        and %rdi, %r15
        ror $28, %r14
        add %r13, %r12
        xor %r15, %r8
        add %r12, %rax
        add %r12, %r8
        lea 24(%rbp), %rbp
        mov 104(%rsp), %r13
        mov 80(%rsp), %r15
        mov %r13, %r12
        ror $7, %r13
        add %r14, %r8
        mov %r15, %r14
        ror $42, %r15
        xor %r12, %r13
        shr $7, %r12
        ror $1, %r13
        xor %r14, %r15
        shr $6, %r14
        ror $19, %r15
        xor %r13, %r12
        xor %r14, %r15
        add 40(%rsp), %r12
        add 96(%rsp), %r12
        mov %rax, %r13
        add %r15, %r12
        mov %r8, %r14
        ror $23, %r13
        mov %rbx, %r15
        xor %rax, %r13
        ror $5, %r14
        xor %rcx, %r15
        mov %r12, 96(%rsp)
        xor %r8, %r14
        and %rax, %r15
        ror $4, %r13
        add %rdx, %r12
        xor %rcx, %r15
        ror $6, %r14
        xor %rax, %r13
        add %r15, %r12
        mov %r8, %r15
        add (%rbp), %r12
        xor %r8, %r14
        xor %r9, %r15
        ror $14, %r13
        mov %r9, %rdx
        and %r15, %rdi
        ror $28, %r14
        add %r13, %r12
        xor %rdi, %rdx
        add %r12, %r11
        add %r12, %rdx
        lea 8(%rbp), %rbp
        mov 112(%rsp), %r13
        mov 88(%rsp), %rdi
        mov %r13, %r12
        ror $7, %r13
        add %r14, %rdx
        mov %rdi, %r14
        ror $42, %rdi
        xor %r12, %r13
        shr $7, %r12
        ror $1, %r13
        xor %r14, %rdi
        shr $6, %r14
        ror $19, %rdi
        xor %r13, %r12
        xor %r14, %rdi
        add 48(%rsp), %r12
        add 104(%rsp), %r12
        mov %r11, %r13
        add %rdi, %r12
        mov %rdx, %r14
        ror $23, %r13
        mov %rax, %rdi
        xor %r11, %r13
        ror $5, %r14
        xor %rbx, %rdi
        mov %r12, 104(%rsp)
        xor %rdx, %r14
        and %r11, %rdi
        ror $4, %r13
        add %rcx, %r12
        xor %rbx, %rdi
        ror $6, %r14
        xor %r11, %r13
        add %rdi, %r12
        mov %rdx, %rdi
        add (%rbp), %r12
        xor %rdx, %r14
        xor %r8, %rdi
        ror $14, %r13
        mov %r8, %rcx
        and %rdi, %r15
        ror $28, %r14
        add %r13, %r12
        xor %r15, %rcx
        add %r12, %r10
        add %r12, %rcx
        lea 24(%rbp), %rbp
        mov 120(%rsp), %r13
        mov 96(%rsp), %r15
        mov %r13, %r12
        ror $7, %r13
        add %r14, %rcx
        mov %r15, %r14
        ror $42, %r15
        xor %r12, %r13
        shr $7, %r12
        ror $1, %r13
        xor %r14, %r15
        shr $6, %r14
        ror $19, %r15
        xor %r13, %r12
        xor %r14, %r15
        add 56(%rsp), %r12
        add 112(%rsp), %r12
        mov %r10, %r13
        add %r15, %r12
        mov %rcx, %r14
        ror $23, %r13
        mov %r11, %r15
        xor %r10, %r13
        ror $5, %r14
        xor %rax, %r15
        mov %r12, 112(%rsp)
        xor %rcx, %r14
        and %r10, %r15
        ror $4, %r13
        add %rbx, %r12
        xor %rax, %r15
        ror $6, %r14
        xor %r10, %r13
        add %r15, %r12
        mov %rcx, %r15
        add (%rbp), %r12
        xor %rcx, %r14
        xor %rdx, %r15
        ror $14, %r13
        mov %rdx, %rbx
        and %r15, %rdi
        ror $28, %r14
        add %r13, %r12
        xor %rdi, %rbx
        add %r12, %r9
        add %r12, %rbx
        lea 8(%rbp), %rbp
        mov (%rsp), %r13
        mov 104(%rsp), %rdi
        mov %r13, %r12
        ror $7, %r13
        add %r14, %rbx
        mov %rdi, %r14
        ror $42, %rdi
        xor %r12, %r13
        shr $7, %r12
        ror $1, %r13
        xor %r14, %rdi
        shr $6, %r14
        ror $19, %rdi
        xor %r13, %r12
        xor %r14, %rdi
        add 64(%rsp), %r12
        add 120(%rsp), %r12
        mov %r9, %r13
        add %rdi, %r12
        mov %rbx, %r14
        ror $23, %r13
        mov %r10, %rdi
        xor %r9, %r13
        ror $5, %r14
        xor %r11, %rdi
        mov %r12, 120(%rsp)
        xor %rbx, %r14
        and %r9, %rdi
        ror $4, %r13
        add %rax, %r12
        xor %r11, %rdi
        ror $6, %r14
        xor %r9, %r13
        add %rdi, %r12
        mov %rbx, %rdi
        add (%rbp), %r12
        xor %rbx, %r14
        xor %rcx, %rdi
        ror $14, %r13
        mov %rcx, %rax
        and %rdi, %r15
        ror $28, %r14
        add %r13, %r12
        xor %r15, %rax
        add %r12, %r8
        add %r12, %rax
        lea 24(%rbp), %rbp
        cmpb $0, 7(%rbp)
        jnz Lsha512_compress_rounds_16_xx
        mov 128+0(%rsp), %rdi
        add %r14, %rax
        lea 128(%rsi), %rsi
        add (%rdi), %rax
        add 8(%rdi), %rbx
        add 16(%rdi), %rcx
        add 24(%rdi), %rdx
        add 32(%rdi), %r8
        add 40(%rdi), %r9
        add 48(%rdi), %r10
        add 56(%rdi), %r11
        cmp 128+16(%rsp), %rsi
        mov %rax, (%rdi)
        mov %rbx, 8(%rdi)
        mov %rcx, 16(%rdi)
        mov %rdx, 24(%rdi)
        mov %r8, 32(%rdi)
        mov %r9, 40(%rdi)
        mov %r10, 48(%rdi)
        mov %r11, 56(%rdi)
        jb Lsha512_compress_loop
        mov 152(%rsp), %rsi
        mov -48(%rsi), %r15
        mov -40(%rsi), %r14
        mov -32(%rsi), %r13
        mov -24(%rsi), %r12
        mov -16(%rsi), %rbp
        mov -8(%rsi), %rbx
        lea (%rsi), %rsp

Lsha512_compress_epilogue:

#if WINDOWS_ABI
        CFI_POP(%rsi)
        CFI_POP(%rdi)
#endif
        CFI_RET


S2N_BN_SIZE_DIRECTIVE(sha512_compress)


#if defined(__ELF__)
.section .rodata
.align 64
.type K512,@object
K512:
.quad 0x428a2f98d728ae22,0x7137449123ef65cd
.quad 0x428a2f98d728ae22,0x7137449123ef65cd
.quad 0xb5c0fbcfec4d3b2f,0xe9b5dba58189dbbc
.quad 0xb5c0fbcfec4d3b2f,0xe9b5dba58189dbbc
.quad 0x3956c25bf348b538,0x59f111f1b605d019
.quad 0x3956c25bf348b538,0x59f111f1b605d019
.quad 0x923f82a4af194f9b,0xab1c5ed5da6d8118
.quad 0x923f82a4af194f9b,0xab1c5ed5da6d8118
.quad 0xd807aa98a3030242,0x12835b0145706fbe
.quad 0xd807aa98a3030242,0x12835b0145706fbe
.quad 0x243185be4ee4b28c,0x550c7dc3d5ffb4e2
.quad 0x243185be4ee4b28c,0x550c7dc3d5ffb4e2
.quad 0x72be5d74f27b896f,0x80deb1fe3b1696b1
.quad 0x72be5d74f27b896f,0x80deb1fe3b1696b1
.quad 0x9bdc06a725c71235,0xc19bf174cf692694
.quad 0x9bdc06a725c71235,0xc19bf174cf692694
.quad 0xe49b69c19ef14ad2,0xefbe4786384f25e3
.quad 0xe49b69c19ef14ad2,0xefbe4786384f25e3
.quad 0x0fc19dc68b8cd5b5,0x240ca1cc77ac9c65
.quad 0x0fc19dc68b8cd5b5,0x240ca1cc77ac9c65
.quad 0x2de92c6f592b0275,0x4a7484aa6ea6e483
.quad 0x2de92c6f592b0275,0x4a7484aa6ea6e483
.quad 0x5cb0a9dcbd41fbd4,0x76f988da831153b5
.quad 0x5cb0a9dcbd41fbd4,0x76f988da831153b5
.quad 0x983e5152ee66dfab,0xa831c66d2db43210
.quad 0x983e5152ee66dfab,0xa831c66d2db43210
.quad 0xb00327c898fb213f,0xbf597fc7beef0ee4
.quad 0xb00327c898fb213f,0xbf597fc7beef0ee4
.quad 0xc6e00bf33da88fc2,0xd5a79147930aa725
.quad 0xc6e00bf33da88fc2,0xd5a79147930aa725
.quad 0x06ca6351e003826f,0x142929670a0e6e70
.quad 0x06ca6351e003826f,0x142929670a0e6e70
.quad 0x27b70a8546d22ffc,0x2e1b21385c26c926
.quad 0x27b70a8546d22ffc,0x2e1b21385c26c926
.quad 0x4d2c6dfc5ac42aed,0x53380d139d95b3df
.quad 0x4d2c6dfc5ac42aed,0x53380d139d95b3df
.quad 0x650a73548baf63de,0x766a0abb3c77b2a8
.quad 0x650a73548baf63de,0x766a0abb3c77b2a8
.quad 0x81c2c92e47edaee6,0x92722c851482353b
.quad 0x81c2c92e47edaee6,0x92722c851482353b
.quad 0xa2bfe8a14cf10364,0xa81a664bbc423001
.quad 0xa2bfe8a14cf10364,0xa81a664bbc423001
.quad 0xc24b8b70d0f89791,0xc76c51a30654be30
.quad 0xc24b8b70d0f89791,0xc76c51a30654be30
.quad 0xd192e819d6ef5218,0xd69906245565a910
.quad 0xd192e819d6ef5218,0xd69906245565a910
.quad 0xf40e35855771202a,0x106aa07032bbd1b8
.quad 0xf40e35855771202a,0x106aa07032bbd1b8
.quad 0x19a4c116b8d2d0c8,0x1e376c085141ab53
.quad 0x19a4c116b8d2d0c8,0x1e376c085141ab53
.quad 0x2748774cdf8eeb99,0x34b0bcb5e19b48a8
.quad 0x2748774cdf8eeb99,0x34b0bcb5e19b48a8
.quad 0x391c0cb3c5c95a63,0x4ed8aa4ae3418acb
.quad 0x391c0cb3c5c95a63,0x4ed8aa4ae3418acb
.quad 0x5b9cca4f7763e373,0x682e6ff3d6b2b8a3
.quad 0x5b9cca4f7763e373,0x682e6ff3d6b2b8a3
.quad 0x748f82ee5defb2fc,0x78a5636f43172f60
.quad 0x748f82ee5defb2fc,0x78a5636f43172f60
.quad 0x84c87814a1f0ab72,0x8cc702081a6439ec
.quad 0x84c87814a1f0ab72,0x8cc702081a6439ec
.quad 0x90befffa23631e28,0xa4506cebde82bde9
.quad 0x90befffa23631e28,0xa4506cebde82bde9
.quad 0xbef9a3f7b2c67915,0xc67178f2e372532b
.quad 0xbef9a3f7b2c67915,0xc67178f2e372532b
.quad 0xca273eceea26619c,0xd186b8c721c0c207
.quad 0xca273eceea26619c,0xd186b8c721c0c207
.quad 0xeada7dd6cde0eb1e,0xf57d4f7fee6ed178
.quad 0xeada7dd6cde0eb1e,0xf57d4f7fee6ed178
.quad 0x06f067aa72176fba,0x0a637dc5a2c898a6
.quad 0x06f067aa72176fba,0x0a637dc5a2c898a6
.quad 0x113f9804bef90dae,0x1b710b35131c471b
.quad 0x113f9804bef90dae,0x1b710b35131c471b
.quad 0x28db77f523047d84,0x32caab7b40c72493
.quad 0x28db77f523047d84,0x32caab7b40c72493
.quad 0x3c9ebe0a15c9bebc,0x431d67c49c100d4c
.quad 0x3c9ebe0a15c9bebc,0x431d67c49c100d4c
.quad 0x4cc5d4becb3e42b6,0x597f299cfc657e2a
.quad 0x4cc5d4becb3e42b6,0x597f299cfc657e2a
.quad 0x5fcb6fab3ad6faec,0x6c44198c4a475817
.quad 0x5fcb6fab3ad6faec,0x6c44198c4a475817
.quad 0x0001020304050607,0x08090a0b0c0d0e0f
.quad 0x0001020304050607,0x08090a0b0c0d0e0f
.size K512,.-K512
#endif

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack, "", %progbits
#endif