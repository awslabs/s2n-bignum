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


#include "_internal_s2n_bignum_x86.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(sha512_compress)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(sha512_compress)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(sha512_compress)
        .text

S2N_BN_SYMBOL(sha512_compress):
        CFI_START
        _CET_ENDBR

#if WINDOWS_ABI
        CFI_PUSH(rdi)
        CFI_PUSH(rsi)
        mov     rdi, rcx
        mov     rsi, rdx
        mov     rdx, r8
#endif

        mov rax, rsp
        CFI_PUSH(rbx)
        CFI_PUSH(rbp)
        CFI_PUSH(r12)
        CFI_PUSH(r13)
        CFI_PUSH(r14)
        CFI_PUSH(r15)
        shl rdx, 4
        sub rsp, 128+32
        lea rdx, [rsi+8*rdx]
        and rsp, -64
        mov [rsp+128+0], rdi
        mov [rsp+128+8], rsi
        mov [rsp+128+16], rdx
        mov [rsp+152], rax
#ifndef _WIN32
.cfi_escape 0x0f,0x06,0x77,0x98,0x01,0x06,0x23,0x08
#endif

Lsha512_compress_prologue:
        mov rax, [rdi]
        mov rbx, [rdi+8]
        mov rcx, [rdi+16]
        mov rdx, [rdi+24]
        mov r8, [rdi+32]
        mov r9, [rdi+40]
        mov r10, [rdi+48]
        mov r11, [rdi+56]
        jmp Lsha512_compress_loop

Lsha512_compress_loop:
        mov rdi, rbx
        lea rbp, [rip+K512]
        xor rdi, rcx
        mov r12, [rsi]
        mov r13, r8
        mov r14, rax
        bswap r12
        ror r13, 23
        mov r15, r9
        xor r13, r8
        ror r14, 5
        xor r15, r10
        mov [rsp], r12
        xor r14, rax
        and r15, r8
        ror r13, 4
        add r12, r11
        xor r15, r10
        ror r14, 6
        xor r13, r8
        add r12, r15
        mov r15, rax
        add r12, [rbp]
        xor r14, rax
        xor r15, rbx
        ror r13, 14
        mov r11, rbx
        and rdi, r15
        ror r14, 28
        add r12, r13
        xor r11, rdi
        add rdx, r12
        add r11, r12
        lea rbp, [rbp+8]
        add r11, r14
        mov r12, [rsi+8]
        mov r13, rdx
        mov r14, r11
        bswap r12
        ror r13, 23
        mov rdi, r8
        xor r13, rdx
        ror r14, 5
        xor rdi, r9
        mov [rsp+8], r12
        xor r14, r11
        and rdi, rdx
        ror r13, 4
        add r12, r10
        xor rdi, r9
        ror r14, 6
        xor r13, rdx
        add r12, rdi
        mov rdi, r11
        add r12, [rbp]
        xor r14, r11
        xor rdi, rax
        ror r13, 14
        mov r10, rax
        and r15, rdi
        ror r14, 28
        add r12, r13
        xor r10, r15
        add rcx, r12
        add r10, r12
        lea rbp, [rbp+24]
        add r10, r14
        mov r12, [rsi+16]
        mov r13, rcx
        mov r14, r10
        bswap r12
        ror r13, 23
        mov r15, rdx
        xor r13, rcx
        ror r14, 5
        xor r15, r8
        mov [rsp+16], r12
        xor r14, r10
        and r15, rcx
        ror r13, 4
        add r12, r9
        xor r15, r8
        ror r14, 6
        xor r13, rcx
        add r12, r15
        mov r15, r10
        add r12, [rbp]
        xor r14, r10
        xor r15, r11
        ror r13, 14
        mov r9, r11
        and rdi, r15
        ror r14, 28
        add r12, r13
        xor r9, rdi
        add rbx, r12
        add r9, r12
        lea rbp, [rbp+8]
        add r9, r14
        mov r12, [rsi+24]
        mov r13, rbx
        mov r14, r9
        bswap r12
        ror r13, 23
        mov rdi, rcx
        xor r13, rbx
        ror r14, 5
        xor rdi, rdx
        mov [rsp+24], r12
        xor r14, r9
        and rdi, rbx
        ror r13, 4
        add r12, r8
        xor rdi, rdx
        ror r14, 6
        xor r13, rbx
        add r12, rdi
        mov rdi, r9
        add r12, [rbp]
        xor r14, r9
        xor rdi, r10
        ror r13, 14
        mov r8, r10
        and r15, rdi
        ror r14, 28
        add r12, r13
        xor r8, r15
        add rax, r12
        add r8, r12
        lea rbp, [rbp+24]
        add r8, r14
        mov r12, [rsi+32]
        mov r13, rax
        mov r14, r8
        bswap r12
        ror r13, 23
        mov r15, rbx
        xor r13, rax
        ror r14, 5
        xor r15, rcx
        mov [rsp+32], r12
        xor r14, r8
        and r15, rax
        ror r13, 4
        add r12, rdx
        xor r15, rcx
        ror r14, 6
        xor r13, rax
        add r12, r15
        mov r15, r8
        add r12, [rbp]
        xor r14, r8
        xor r15, r9
        ror r13, 14
        mov rdx, r9
        and rdi, r15
        ror r14, 28
        add r12, r13
        xor rdx, rdi
        add r11, r12
        add rdx, r12
        lea rbp, [rbp+8]
        add rdx, r14
        mov r12, [rsi+40]
        mov r13, r11
        mov r14, rdx
        bswap r12
        ror r13, 23
        mov rdi, rax
        xor r13, r11
        ror r14, 5
        xor rdi, rbx
        mov [rsp+40], r12
        xor r14, rdx
        and rdi, r11
        ror r13, 4
        add r12, rcx
        xor rdi, rbx
        ror r14, 6
        xor r13, r11
        add r12, rdi
        mov rdi, rdx
        add r12, [rbp]
        xor r14, rdx
        xor rdi, r8
        ror r13, 14
        mov rcx, r8
        and r15, rdi
        ror r14, 28
        add r12, r13
        xor rcx, r15
        add r10, r12
        add rcx, r12
        lea rbp, [rbp+24]
        add rcx, r14
        mov r12, [rsi+48]
        mov r13, r10
        mov r14, rcx
        bswap r12
        ror r13, 23
        mov r15, r11
        xor r13, r10
        ror r14, 5
        xor r15, rax
        mov [rsp+48], r12
        xor r14, rcx
        and r15, r10
        ror r13, 4
        add r12, rbx
        xor r15, rax
        ror r14, 6
        xor r13, r10
        add r12, r15
        mov r15, rcx
        add r12, [rbp]
        xor r14, rcx
        xor r15, rdx
        ror r13, 14
        mov rbx, rdx
        and rdi, r15
        ror r14, 28
        add r12, r13
        xor rbx, rdi
        add r9, r12
        add rbx, r12
        lea rbp, [rbp+8]
        add rbx, r14
        mov r12, [rsi+56]
        mov r13, r9
        mov r14, rbx
        bswap r12
        ror r13, 23
        mov rdi, r10
        xor r13, r9
        ror r14, 5
        xor rdi, r11
        mov [rsp+56], r12
        xor r14, rbx
        and rdi, r9
        ror r13, 4
        add r12, rax
        xor rdi, r11
        ror r14, 6
        xor r13, r9
        add r12, rdi
        mov rdi, rbx
        add r12, [rbp]
        xor r14, rbx
        xor rdi, rcx
        ror r13, 14
        mov rax, rcx
        and r15, rdi
        ror r14, 28
        add r12, r13
        xor rax, r15
        add r8, r12
        add rax, r12
        lea rbp, [rbp+24]
        add rax, r14
        mov r12, [rsi+64]
        mov r13, r8
        mov r14, rax
        bswap r12
        ror r13, 23
        mov r15, r9
        xor r13, r8
        ror r14, 5
        xor r15, r10
        mov [rsp+64], r12
        xor r14, rax
        and r15, r8
        ror r13, 4
        add r12, r11
        xor r15, r10
        ror r14, 6
        xor r13, r8
        add r12, r15
        mov r15, rax
        add r12, [rbp]
        xor r14, rax
        xor r15, rbx
        ror r13, 14
        mov r11, rbx
        and rdi, r15
        ror r14, 28
        add r12, r13
        xor r11, rdi
        add rdx, r12
        add r11, r12
        lea rbp, [rbp+8]
        add r11, r14
        mov r12, [rsi+72]
        mov r13, rdx
        mov r14, r11
        bswap r12
        ror r13, 23
        mov rdi, r8
        xor r13, rdx
        ror r14, 5
        xor rdi, r9
        mov [rsp+72], r12
        xor r14, r11
        and rdi, rdx
        ror r13, 4
        add r12, r10
        xor rdi, r9
        ror r14, 6
        xor r13, rdx
        add r12, rdi
        mov rdi, r11
        add r12, [rbp]
        xor r14, r11
        xor rdi, rax
        ror r13, 14
        mov r10, rax
        and r15, rdi
        ror r14, 28
        add r12, r13
        xor r10, r15
        add rcx, r12
        add r10, r12
        lea rbp, [rbp+24]
        add r10, r14
        mov r12, [rsi+80]
        mov r13, rcx
        mov r14, r10
        bswap r12
        ror r13, 23
        mov r15, rdx
        xor r13, rcx
        ror r14, 5
        xor r15, r8
        mov [rsp+80], r12
        xor r14, r10
        and r15, rcx
        ror r13, 4
        add r12, r9
        xor r15, r8
        ror r14, 6
        xor r13, rcx
        add r12, r15
        mov r15, r10
        add r12, [rbp]
        xor r14, r10
        xor r15, r11
        ror r13, 14
        mov r9, r11
        and rdi, r15
        ror r14, 28
        add r12, r13
        xor r9, rdi
        add rbx, r12
        add r9, r12
        lea rbp, [rbp+8]
        add r9, r14
        mov r12, [rsi+88]
        mov r13, rbx
        mov r14, r9
        bswap r12
        ror r13, 23
        mov rdi, rcx
        xor r13, rbx
        ror r14, 5
        xor rdi, rdx
        mov [rsp+88], r12
        xor r14, r9
        and rdi, rbx
        ror r13, 4
        add r12, r8
        xor rdi, rdx
        ror r14, 6
        xor r13, rbx
        add r12, rdi
        mov rdi, r9
        add r12, [rbp]
        xor r14, r9
        xor rdi, r10
        ror r13, 14
        mov r8, r10
        and r15, rdi
        ror r14, 28
        add r12, r13
        xor r8, r15
        add rax, r12
        add r8, r12
        lea rbp, [rbp+24]
        add r8, r14
        mov r12, [rsi+96]
        mov r13, rax
        mov r14, r8
        bswap r12
        ror r13, 23
        mov r15, rbx
        xor r13, rax
        ror r14, 5
        xor r15, rcx
        mov [rsp+96], r12
        xor r14, r8
        and r15, rax
        ror r13, 4
        add r12, rdx
        xor r15, rcx
        ror r14, 6
        xor r13, rax
        add r12, r15
        mov r15, r8
        add r12, [rbp]
        xor r14, r8
        xor r15, r9
        ror r13, 14
        mov rdx, r9
        and rdi, r15
        ror r14, 28
        add r12, r13
        xor rdx, rdi
        add r11, r12
        add rdx, r12
        lea rbp, [rbp+8]
        add rdx, r14
        mov r12, [rsi+104]
        mov r13, r11
        mov r14, rdx
        bswap r12
        ror r13, 23
        mov rdi, rax
        xor r13, r11
        ror r14, 5
        xor rdi, rbx
        mov [rsp+104], r12
        xor r14, rdx
        and rdi, r11
        ror r13, 4
        add r12, rcx
        xor rdi, rbx
        ror r14, 6
        xor r13, r11
        add r12, rdi
        mov rdi, rdx
        add r12, [rbp]
        xor r14, rdx
        xor rdi, r8
        ror r13, 14
        mov rcx, r8
        and r15, rdi
        ror r14, 28
        add r12, r13
        xor rcx, r15
        add r10, r12
        add rcx, r12
        lea rbp, [rbp+24]
        add rcx, r14
        mov r12, [rsi+112]
        mov r13, r10
        mov r14, rcx
        bswap r12
        ror r13, 23
        mov r15, r11
        xor r13, r10
        ror r14, 5
        xor r15, rax
        mov [rsp+112], r12
        xor r14, rcx
        and r15, r10
        ror r13, 4
        add r12, rbx
        xor r15, rax
        ror r14, 6
        xor r13, r10
        add r12, r15
        mov r15, rcx
        add r12, [rbp]
        xor r14, rcx
        xor r15, rdx
        ror r13, 14
        mov rbx, rdx
        and rdi, r15
        ror r14, 28
        add r12, r13
        xor rbx, rdi
        add r9, r12
        add rbx, r12
        lea rbp, [rbp+8]
        add rbx, r14
        mov r12, [rsi+120]
        mov r13, r9
        mov r14, rbx
        bswap r12
        ror r13, 23
        mov rdi, r10
        xor r13, r9
        ror r14, 5
        xor rdi, r11
        mov [rsp+120], r12
        xor r14, rbx
        and rdi, r9
        ror r13, 4
        add r12, rax
        xor rdi, r11
        ror r14, 6
        xor r13, r9
        add r12, rdi
        mov rdi, rbx
        add r12, [rbp]
        xor r14, rbx
        xor rdi, rcx
        ror r13, 14
        mov rax, rcx
        and r15, rdi
        ror r14, 28
        add r12, r13
        xor rax, r15
        add r8, r12
        add rax, r12
        lea rbp, [rbp+24]
        jmp Lsha512_compress_rounds_16_xx

Lsha512_compress_rounds_16_xx:
        mov r13, [rsp+8]
        mov r15, [rsp+112]
        mov r12, r13
        ror r13, 7
        add rax, r14
        mov r14, r15
        ror r15, 42
        xor r13, r12
        shr r12, 7
        ror r13, 1
        xor r15, r14
        shr r14, 6
        ror r15, 19
        xor r12, r13
        xor r15, r14
        add r12, [rsp+72]
        add r12, [rsp]
        mov r13, r8
        add r12, r15
        mov r14, rax
        ror r13, 23
        mov r15, r9
        xor r13, r8
        ror r14, 5
        xor r15, r10
        mov [rsp], r12
        xor r14, rax
        and r15, r8
        ror r13, 4
        add r12, r11
        xor r15, r10
        ror r14, 6
        xor r13, r8
        add r12, r15
        mov r15, rax
        add r12, [rbp]
        xor r14, rax
        xor r15, rbx
        ror r13, 14
        mov r11, rbx
        and rdi, r15
        ror r14, 28
        add r12, r13
        xor r11, rdi
        add rdx, r12
        add r11, r12
        lea rbp, [rbp+8]
        mov r13, [rsp+16]
        mov rdi, [rsp+120]
        mov r12, r13
        ror r13, 7
        add r11, r14
        mov r14, rdi
        ror rdi, 42
        xor r13, r12
        shr r12, 7
        ror r13, 1
        xor rdi, r14
        shr r14, 6
        ror rdi, 19
        xor r12, r13
        xor rdi, r14
        add r12, [rsp+80]
        add r12, [rsp+8]
        mov r13, rdx
        add r12, rdi
        mov r14, r11
        ror r13, 23
        mov rdi, r8
        xor r13, rdx
        ror r14, 5
        xor rdi, r9
        mov [rsp+8], r12
        xor r14, r11
        and rdi, rdx
        ror r13, 4
        add r12, r10
        xor rdi, r9
        ror r14, 6
        xor r13, rdx
        add r12, rdi
        mov rdi, r11
        add r12, [rbp]
        xor r14, r11
        xor rdi, rax
        ror r13, 14
        mov r10, rax
        and r15, rdi
        ror r14, 28
        add r12, r13
        xor r10, r15
        add rcx, r12
        add r10, r12
        lea rbp, [rbp+24]
        mov r13, [rsp+24]
        mov r15, [rsp]
        mov r12, r13
        ror r13, 7
        add r10, r14
        mov r14, r15
        ror r15, 42
        xor r13, r12
        shr r12, 7
        ror r13, 1
        xor r15, r14
        shr r14, 6
        ror r15, 19
        xor r12, r13
        xor r15, r14
        add r12, [rsp+88]
        add r12, [rsp+16]
        mov r13, rcx
        add r12, r15
        mov r14, r10
        ror r13, 23
        mov r15, rdx
        xor r13, rcx
        ror r14, 5
        xor r15, r8
        mov [rsp+16], r12
        xor r14, r10
        and r15, rcx
        ror r13, 4
        add r12, r9
        xor r15, r8
        ror r14, 6
        xor r13, rcx
        add r12, r15
        mov r15, r10
        add r12, [rbp]
        xor r14, r10
        xor r15, r11
        ror r13, 14
        mov r9, r11
        and rdi, r15
        ror r14, 28
        add r12, r13
        xor r9, rdi
        add rbx, r12
        add r9, r12
        lea rbp, [rbp+8]
        mov r13, [rsp+32]
        mov rdi, [rsp+8]
        mov r12, r13
        ror r13, 7
        add r9, r14
        mov r14, rdi
        ror rdi, 42
        xor r13, r12
        shr r12, 7
        ror r13, 1
        xor rdi, r14
        shr r14, 6
        ror rdi, 19
        xor r12, r13
        xor rdi, r14
        add r12, [rsp+96]
        add r12, [rsp+24]
        mov r13, rbx
        add r12, rdi
        mov r14, r9
        ror r13, 23
        mov rdi, rcx
        xor r13, rbx
        ror r14, 5
        xor rdi, rdx
        mov [rsp+24], r12
        xor r14, r9
        and rdi, rbx
        ror r13, 4
        add r12, r8
        xor rdi, rdx
        ror r14, 6
        xor r13, rbx
        add r12, rdi
        mov rdi, r9
        add r12, [rbp]
        xor r14, r9
        xor rdi, r10
        ror r13, 14
        mov r8, r10
        and r15, rdi
        ror r14, 28
        add r12, r13
        xor r8, r15
        add rax, r12
        add r8, r12
        lea rbp, [rbp+24]
        mov r13, [rsp+40]
        mov r15, [rsp+16]
        mov r12, r13
        ror r13, 7
        add r8, r14
        mov r14, r15
        ror r15, 42
        xor r13, r12
        shr r12, 7
        ror r13, 1
        xor r15, r14
        shr r14, 6
        ror r15, 19
        xor r12, r13
        xor r15, r14
        add r12, [rsp+104]
        add r12, [rsp+32]
        mov r13, rax
        add r12, r15
        mov r14, r8
        ror r13, 23
        mov r15, rbx
        xor r13, rax
        ror r14, 5
        xor r15, rcx
        mov [rsp+32], r12
        xor r14, r8
        and r15, rax
        ror r13, 4
        add r12, rdx
        xor r15, rcx
        ror r14, 6
        xor r13, rax
        add r12, r15
        mov r15, r8
        add r12, [rbp]
        xor r14, r8
        xor r15, r9
        ror r13, 14
        mov rdx, r9
        and rdi, r15
        ror r14, 28
        add r12, r13
        xor rdx, rdi
        add r11, r12
        add rdx, r12
        lea rbp, [rbp+8]
        mov r13, [rsp+48]
        mov rdi, [rsp+24]
        mov r12, r13
        ror r13, 7
        add rdx, r14
        mov r14, rdi
        ror rdi, 42
        xor r13, r12
        shr r12, 7
        ror r13, 1
        xor rdi, r14
        shr r14, 6
        ror rdi, 19
        xor r12, r13
        xor rdi, r14
        add r12, [rsp+112]
        add r12, [rsp+40]
        mov r13, r11
        add r12, rdi
        mov r14, rdx
        ror r13, 23
        mov rdi, rax
        xor r13, r11
        ror r14, 5
        xor rdi, rbx
        mov [rsp+40], r12
        xor r14, rdx
        and rdi, r11
        ror r13, 4
        add r12, rcx
        xor rdi, rbx
        ror r14, 6
        xor r13, r11
        add r12, rdi
        mov rdi, rdx
        add r12, [rbp]
        xor r14, rdx
        xor rdi, r8
        ror r13, 14
        mov rcx, r8
        and r15, rdi
        ror r14, 28
        add r12, r13
        xor rcx, r15
        add r10, r12
        add rcx, r12
        lea rbp, [rbp+24]
        mov r13, [rsp+56]
        mov r15, [rsp+32]
        mov r12, r13
        ror r13, 7
        add rcx, r14
        mov r14, r15
        ror r15, 42
        xor r13, r12
        shr r12, 7
        ror r13, 1
        xor r15, r14
        shr r14, 6
        ror r15, 19
        xor r12, r13
        xor r15, r14
        add r12, [rsp+120]
        add r12, [rsp+48]
        mov r13, r10
        add r12, r15
        mov r14, rcx
        ror r13, 23
        mov r15, r11
        xor r13, r10
        ror r14, 5
        xor r15, rax
        mov [rsp+48], r12
        xor r14, rcx
        and r15, r10
        ror r13, 4
        add r12, rbx
        xor r15, rax
        ror r14, 6
        xor r13, r10
        add r12, r15
        mov r15, rcx
        add r12, [rbp]
        xor r14, rcx
        xor r15, rdx
        ror r13, 14
        mov rbx, rdx
        and rdi, r15
        ror r14, 28
        add r12, r13
        xor rbx, rdi
        add r9, r12
        add rbx, r12
        lea rbp, [rbp+8]
        mov r13, [rsp+64]
        mov rdi, [rsp+40]
        mov r12, r13
        ror r13, 7
        add rbx, r14
        mov r14, rdi
        ror rdi, 42
        xor r13, r12
        shr r12, 7
        ror r13, 1
        xor rdi, r14
        shr r14, 6
        ror rdi, 19
        xor r12, r13
        xor rdi, r14
        add r12, [rsp]
        add r12, [rsp+56]
        mov r13, r9
        add r12, rdi
        mov r14, rbx
        ror r13, 23
        mov rdi, r10
        xor r13, r9
        ror r14, 5
        xor rdi, r11
        mov [rsp+56], r12
        xor r14, rbx
        and rdi, r9
        ror r13, 4
        add r12, rax
        xor rdi, r11
        ror r14, 6
        xor r13, r9
        add r12, rdi
        mov rdi, rbx
        add r12, [rbp]
        xor r14, rbx
        xor rdi, rcx
        ror r13, 14
        mov rax, rcx
        and r15, rdi
        ror r14, 28
        add r12, r13
        xor rax, r15
        add r8, r12
        add rax, r12
        lea rbp, [rbp+24]
        mov r13, [rsp+72]
        mov r15, [rsp+48]
        mov r12, r13
        ror r13, 7
        add rax, r14
        mov r14, r15
        ror r15, 42
        xor r13, r12
        shr r12, 7
        ror r13, 1
        xor r15, r14
        shr r14, 6
        ror r15, 19
        xor r12, r13
        xor r15, r14
        add r12, [rsp+8]
        add r12, [rsp+64]
        mov r13, r8
        add r12, r15
        mov r14, rax
        ror r13, 23
        mov r15, r9
        xor r13, r8
        ror r14, 5
        xor r15, r10
        mov [rsp+64], r12
        xor r14, rax
        and r15, r8
        ror r13, 4
        add r12, r11
        xor r15, r10
        ror r14, 6
        xor r13, r8
        add r12, r15
        mov r15, rax
        add r12, [rbp]
        xor r14, rax
        xor r15, rbx
        ror r13, 14
        mov r11, rbx
        and rdi, r15
        ror r14, 28
        add r12, r13
        xor r11, rdi
        add rdx, r12
        add r11, r12
        lea rbp, [rbp+8]
        mov r13, [rsp+80]
        mov rdi, [rsp+56]
        mov r12, r13
        ror r13, 7
        add r11, r14
        mov r14, rdi
        ror rdi, 42
        xor r13, r12
        shr r12, 7
        ror r13, 1
        xor rdi, r14
        shr r14, 6
        ror rdi, 19
        xor r12, r13
        xor rdi, r14
        add r12, [rsp+16]
        add r12, [rsp+72]
        mov r13, rdx
        add r12, rdi
        mov r14, r11
        ror r13, 23
        mov rdi, r8
        xor r13, rdx
        ror r14, 5
        xor rdi, r9
        mov [rsp+72], r12
        xor r14, r11
        and rdi, rdx
        ror r13, 4
        add r12, r10
        xor rdi, r9
        ror r14, 6
        xor r13, rdx
        add r12, rdi
        mov rdi, r11
        add r12, [rbp]
        xor r14, r11
        xor rdi, rax
        ror r13, 14
        mov r10, rax
        and r15, rdi
        ror r14, 28
        add r12, r13
        xor r10, r15
        add rcx, r12
        add r10, r12
        lea rbp, [rbp+24]
        mov r13, [rsp+88]
        mov r15, [rsp+64]
        mov r12, r13
        ror r13, 7
        add r10, r14
        mov r14, r15
        ror r15, 42
        xor r13, r12
        shr r12, 7
        ror r13, 1
        xor r15, r14
        shr r14, 6
        ror r15, 19
        xor r12, r13
        xor r15, r14
        add r12, [rsp+24]
        add r12, [rsp+80]
        mov r13, rcx
        add r12, r15
        mov r14, r10
        ror r13, 23
        mov r15, rdx
        xor r13, rcx
        ror r14, 5
        xor r15, r8
        mov [rsp+80], r12
        xor r14, r10
        and r15, rcx
        ror r13, 4
        add r12, r9
        xor r15, r8
        ror r14, 6
        xor r13, rcx
        add r12, r15
        mov r15, r10
        add r12, [rbp]
        xor r14, r10
        xor r15, r11
        ror r13, 14
        mov r9, r11
        and rdi, r15
        ror r14, 28
        add r12, r13
        xor r9, rdi
        add rbx, r12
        add r9, r12
        lea rbp, [rbp+8]
        mov r13, [rsp+96]
        mov rdi, [rsp+72]
        mov r12, r13
        ror r13, 7
        add r9, r14
        mov r14, rdi
        ror rdi, 42
        xor r13, r12
        shr r12, 7
        ror r13, 1
        xor rdi, r14
        shr r14, 6
        ror rdi, 19
        xor r12, r13
        xor rdi, r14
        add r12, [rsp+32]
        add r12, [rsp+88]
        mov r13, rbx
        add r12, rdi
        mov r14, r9
        ror r13, 23
        mov rdi, rcx
        xor r13, rbx
        ror r14, 5
        xor rdi, rdx
        mov [rsp+88], r12
        xor r14, r9
        and rdi, rbx
        ror r13, 4
        add r12, r8
        xor rdi, rdx
        ror r14, 6
        xor r13, rbx
        add r12, rdi
        mov rdi, r9
        add r12, [rbp]
        xor r14, r9
        xor rdi, r10
        ror r13, 14
        mov r8, r10
        and r15, rdi
        ror r14, 28
        add r12, r13
        xor r8, r15
        add rax, r12
        add r8, r12
        lea rbp, [rbp+24]
        mov r13, [rsp+104]
        mov r15, [rsp+80]
        mov r12, r13
        ror r13, 7
        add r8, r14
        mov r14, r15
        ror r15, 42
        xor r13, r12
        shr r12, 7
        ror r13, 1
        xor r15, r14
        shr r14, 6
        ror r15, 19
        xor r12, r13
        xor r15, r14
        add r12, [rsp+40]
        add r12, [rsp+96]
        mov r13, rax
        add r12, r15
        mov r14, r8
        ror r13, 23
        mov r15, rbx
        xor r13, rax
        ror r14, 5
        xor r15, rcx
        mov [rsp+96], r12
        xor r14, r8
        and r15, rax
        ror r13, 4
        add r12, rdx
        xor r15, rcx
        ror r14, 6
        xor r13, rax
        add r12, r15
        mov r15, r8
        add r12, [rbp]
        xor r14, r8
        xor r15, r9
        ror r13, 14
        mov rdx, r9
        and rdi, r15
        ror r14, 28
        add r12, r13
        xor rdx, rdi
        add r11, r12
        add rdx, r12
        lea rbp, [rbp+8]
        mov r13, [rsp+112]
        mov rdi, [rsp+88]
        mov r12, r13
        ror r13, 7
        add rdx, r14
        mov r14, rdi
        ror rdi, 42
        xor r13, r12
        shr r12, 7
        ror r13, 1
        xor rdi, r14
        shr r14, 6
        ror rdi, 19
        xor r12, r13
        xor rdi, r14
        add r12, [rsp+48]
        add r12, [rsp+104]
        mov r13, r11
        add r12, rdi
        mov r14, rdx
        ror r13, 23
        mov rdi, rax
        xor r13, r11
        ror r14, 5
        xor rdi, rbx
        mov [rsp+104], r12
        xor r14, rdx
        and rdi, r11
        ror r13, 4
        add r12, rcx
        xor rdi, rbx
        ror r14, 6
        xor r13, r11
        add r12, rdi
        mov rdi, rdx
        add r12, [rbp]
        xor r14, rdx
        xor rdi, r8
        ror r13, 14
        mov rcx, r8
        and r15, rdi
        ror r14, 28
        add r12, r13
        xor rcx, r15
        add r10, r12
        add rcx, r12
        lea rbp, [rbp+24]
        mov r13, [rsp+120]
        mov r15, [rsp+96]
        mov r12, r13
        ror r13, 7
        add rcx, r14
        mov r14, r15
        ror r15, 42
        xor r13, r12
        shr r12, 7
        ror r13, 1
        xor r15, r14
        shr r14, 6
        ror r15, 19
        xor r12, r13
        xor r15, r14
        add r12, [rsp+56]
        add r12, [rsp+112]
        mov r13, r10
        add r12, r15
        mov r14, rcx
        ror r13, 23
        mov r15, r11
        xor r13, r10
        ror r14, 5
        xor r15, rax
        mov [rsp+112], r12
        xor r14, rcx
        and r15, r10
        ror r13, 4
        add r12, rbx
        xor r15, rax
        ror r14, 6
        xor r13, r10
        add r12, r15
        mov r15, rcx
        add r12, [rbp]
        xor r14, rcx
        xor r15, rdx
        ror r13, 14
        mov rbx, rdx
        and rdi, r15
        ror r14, 28
        add r12, r13
        xor rbx, rdi
        add r9, r12
        add rbx, r12
        lea rbp, [rbp+8]
        mov r13, [rsp]
        mov rdi, [rsp+104]
        mov r12, r13
        ror r13, 7
        add rbx, r14
        mov r14, rdi
        ror rdi, 42
        xor r13, r12
        shr r12, 7
        ror r13, 1
        xor rdi, r14
        shr r14, 6
        ror rdi, 19
        xor r12, r13
        xor rdi, r14
        add r12, [rsp+64]
        add r12, [rsp+120]
        mov r13, r9
        add r12, rdi
        mov r14, rbx
        ror r13, 23
        mov rdi, r10
        xor r13, r9
        ror r14, 5
        xor rdi, r11
        mov [rsp+120], r12
        xor r14, rbx
        and rdi, r9
        ror r13, 4
        add r12, rax
        xor rdi, r11
        ror r14, 6
        xor r13, r9
        add r12, rdi
        mov rdi, rbx
        add r12, [rbp]
        xor r14, rbx
        xor rdi, rcx
        ror r13, 14
        mov rax, rcx
        and r15, rdi
        ror r14, 28
        add r12, r13
        xor rax, r15
        add r8, r12
        add rax, r12
        lea rbp, [rbp+24]
        cmp BYTE PTR [rbp+7], 0
        jnz Lsha512_compress_rounds_16_xx
        mov rdi, [rsp+128+0]
        add rax, r14
        lea rsi, [rsi+128]
        add rax, [rdi]
        add rbx, [rdi+8]
        add rcx, [rdi+16]
        add rdx, [rdi+24]
        add r8, [rdi+32]
        add r9, [rdi+40]
        add r10, [rdi+48]
        add r11, [rdi+56]
        cmp rsi, [rsp+128+16]
        mov [rdi], rax
        mov [rdi+8], rbx
        mov [rdi+16], rcx
        mov [rdi+24], rdx
        mov [rdi+32], r8
        mov [rdi+40], r9
        mov [rdi+48], r10
        mov [rdi+56], r11
        jb Lsha512_compress_loop
        mov rsi, [rsp+152]
        mov r15, [rsi-48]
        mov r14, [rsi-40]
        mov r13, [rsi-32]
        mov r12, [rsi-24]
        mov rbp, [rsi-16]
        mov rbx, [rsi-8]
        lea rsp, [rsi]

Lsha512_compress_epilogue:

#if WINDOWS_ABI
        CFI_POP(rsi)
        CFI_POP(rdi)
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