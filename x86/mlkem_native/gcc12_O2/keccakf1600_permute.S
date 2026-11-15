// Copyright (c) The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

// ----------------------------------------------------------------------------
// Keccak-f1600 permutation for SHA3
// Input a[25]; output a[25]
//
// Thinking of the input/output array a as a row-major flattening of a 5x5
// matrix of 64-bit words, this performs the Keccak-f1600 permutation, all 24
// rounds with the distinct round constants for each one. This is the same
// operation as sha3_keccak_f1600, but this is the code for
// mlkem_keccakf1600_permute from mlkem-native's portable C implementation as
// compiled by gcc 12.3.0 with -O2 for x86-64 (see README.md for details). It
// does two rounds in each iteration of its loop, and it uses its own table of
// round constants, which is the mlk_KeccakF_RoundConstants array in
// mlkem-native, instead of taking it as an argument.
//
// extern void mlkem_native_keccakf1600_permute_gcc12_O2
//   (uint64_t a[static 25]);
//
// Standard x86-64 ABI: RDI = a
// ----------------------------------------------------------------------------
#include "_internal_s2n_bignum_x86.h"

.intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(mlkem_native_keccakf1600_permute_gcc12_O2)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(mlkem_native_keccakf1600_permute_gcc12_O2)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(mlkem_native_keccakf1600_permute_gcc12_O2)
        .text
        .balign 4

S2N_BN_SYMBOL(mlkem_native_keccakf1600_permute_gcc12_O2):
        CFI_START

        push    r15
        mov     rax, rdi
        push    r14
        push    r13
        push    r12
        push    rbp
        push    rbx
        sub     rsp, 0x58
        mov     rdx, QWORD PTR [rdi+0x8]
        mov     r13, QWORD PTR [rdi+0x18]
        mov     r15, QWORD PTR [rdi]
        mov     r12, QWORD PTR [rdi+0x60]
        mov     QWORD PTR [rsp-0x70], rdx
        mov     rdx, QWORD PTR [rdi+0x10]
        mov     QWORD PTR [rsp-0x68], rdx
        mov     rdx, QWORD PTR [rdi+0x20]
        mov     QWORD PTR [rsp-0x60], rdx
        mov     rdx, QWORD PTR [rdi+0x28]
        mov     QWORD PTR [rsp-0x58], rdx
        mov     rdx, QWORD PTR [rdi+0x30]
        mov     QWORD PTR [rsp-0x50], rdx
        mov     rdx, QWORD PTR [rdi+0x38]
        mov     QWORD PTR [rsp-0x48], rdx
        mov     rdx, QWORD PTR [rdi+0x40]
        mov     QWORD PTR [rsp-0x40], rdx
        mov     rdx, QWORD PTR [rdi+0x48]
        mov     QWORD PTR [rsp-0x38], rdx
        mov     rdx, QWORD PTR [rdi+0x50]
        mov     QWORD PTR [rsp-0x30], rdx
        mov     rdx, QWORD PTR [rdi+0x58]
        mov     QWORD PTR [rsp-0x28], rdx
        mov     rdx, QWORD PTR [rdi+0x68]
        mov     QWORD PTR [rsp-0x20], rdx
        mov     rdx, QWORD PTR [rdi+0x70]
        mov     QWORD PTR [rsp+0x18], r13
        mov     r11, QWORD PTR [rax+0x90]
        mov     QWORD PTR [rsp-0x18], rdx
        mov     rdx, QWORD PTR [rdi+0x78]
        mov     QWORD PTR [rsp+0x50], rax
        mov     rdi, QWORD PTR [rdi+0x80]
        mov     QWORD PTR [rsp-0x10], rdx
        mov     rdx, QWORD PTR [rax+0x88]
        mov     r14, QWORD PTR [rax+0xa0]
        mov     r8, QWORD PTR [rax+0xb0]
        mov     QWORD PTR [rsp-0x8], rdx
        mov     rdx, QWORD PTR [rax+0x98]
        mov     rbx, QWORD PTR [rax+0xc0]
        mov     QWORD PTR [rsp], rdx
        mov     rdx, QWORD PTR [rax+0xa8]
        mov     QWORD PTR [rsp+0x8], rdx
        mov     rdx, QWORD PTR [rax+0xb8]
        mov     QWORD PTR [rsp+0x10], rdx
        lea     rdx, [rip+mlk_KeccakF_RoundConstants]
        mov     QWORD PTR [rsp-0x78], rdx
        // nop     DWORD PTR [rax+0x0]
        .byte   0x0f,0x1f,0x80,0x00,0x00,0x00,0x00
Lmlkem_native_keccakf1600_permute_gcc12_O2_100:
        mov     rcx, QWORD PTR [rsp-0x58]
        mov     rax, QWORD PTR [rsp-0x30]
        mov     rsi, QWORD PTR [rsp-0x10]
        mov     r13, QWORD PTR [rsp-0x70]
        xor     rcx, r15
        mov     rdx, QWORD PTR [rsp-0x28]
        mov     rbp, QWORD PTR [rsp+0x8]
        xor     rcx, rax
        mov     r9, QWORD PTR [rsp+0x18]
        mov     r10, QWORD PTR [rsp-0x68]
        xor     rcx, rsi
        mov     rsi, QWORD PTR [rsp-0x50]
        mov     rax, QWORD PTR [rsp-0x8]
        xor     rcx, r14
        xor     r13, rsi
        mov     rsi, QWORD PTR [rsp-0x20]
        xor     r13, rdx
        mov     rdx, QWORD PTR [rsp-0x40]
        xor     r13, rdi
        xor     r13, rbp
        xor     r9, rdx
        mov     rbp, QWORD PTR [rsp-0x48]
        mov     rdx, QWORD PTR [rsp+0x10]
        xor     r9, rsi
        xor     r10, rbp
        xor     r9, r11
        mov     rbp, QWORD PTR [rsp-0x38]
        xor     r9, rdx
        xor     r10, r12
        mov     rdx, QWORD PTR [rsp-0x60]
        xor     r10, rax
        mov     rax, QWORD PTR [rsp-0x18]
        xor     rdx, rbp
        mov     rbp, r13
        xor     r10, r8
        xor     rdx, rax
        mov     rax, QWORD PTR [rsp]
        rol     rbp, 1
        mov     rsi, r10
        rol     rsi, 1
        xor     rdx, rax
        xor     rsi, rcx
        mov     rax, r9
        rol     rcx, 1
        xor     rdx, rbx
        rol     rax, 1
        xor     rcx, r9
        xor     rbp, rdx
        rol     rdx, 1
        xor     rax, r13
        xor     rdx, r10
        mov     r10, QWORD PTR [rsp-0x50]
        xor     r15, rbp
        mov     r9, r15
        xor     r10, rsi
        ror     r10, 0x14
        xor     r12, rax
        xor     r11, rdx
        xor     rbx, rcx
        mov     r15, r10
        ror     r12, 0x15
        xor     rdi, rsi
        xor     r8, rax
        rol     r11, 0x15
        not     r15
        rol     rbx, 0xe
        ror     rdi, 0x13
        mov     r13, r15
        mov     r15, QWORD PTR [rsp-0x78]
        ror     r8, 0x3
        and     r13, r12
        mov     QWORD PTR [rsp-0x50], r13
        mov     r13, QWORD PTR [r15]
        xor     r13, r9
        mov     r15, r13
        mov     r13, QWORD PTR [rsp-0x50]
        xor     r15, r13
        mov     r13, r12
        not     r13
        and     r13, r11
        xor     r13, r10
        mov     QWORD PTR [rsp+0x20], r13
        mov     r13, r11
        not     r13
        and     r13, rbx
        xor     r13, r12
        mov     r12, rbx
        not     r12
        mov     QWORD PTR [rsp+0x28], r13
        and     r12, r9
        not     r9
        and     r9, r10
        xor     r12, r11
        mov     r11, QWORD PTR [rsp-0x30]
        mov     r10, r9
        mov     r9, QWORD PTR [rsp+0x18]
        mov     QWORD PTR [rsp-0x50], r12
        mov     r12, rdi
        xor     r10, rbx
        xor     r11, rbp
        not     r12
        mov     QWORD PTR [rsp+0x30], r10
        mov     r10, QWORD PTR [rsp-0x38]
        rol     r11, 0x3
        xor     r9, rdx
        rol     r9, 0x1c
        xor     r10, rcx
        rol     r10, 0x14
        mov     rbx, r10
        not     rbx
        and     rbx, r11
        xor     rbx, r9
        mov     QWORD PTR [rsp+0x38], rbx
        mov     rbx, r11
        not     rbx
        and     rbx, rdi
        xor     rbx, r10
        mov     QWORD PTR [rsp+0x18], rbx
        mov     rbx, r12
        and     rbx, r8
        xor     r14, rbp
        mov     r12, rbx
        rol     r14, 0x12
        xor     r12, r11
        mov     r11, r8
        not     r11
        mov     QWORD PTR [rsp-0x30], r12
        mov     rbx, QWORD PTR [rsp-0x58]
        and     r11, r9
        not     r9
        and     r9, r10
        xor     r11, rdi
        mov     rdi, QWORD PTR [rsp-0x70]
        xor     rbx, rbp
        xor     r9, r8
        mov     r8, QWORD PTR [rsp-0x48]
        mov     QWORD PTR [rsp+0x40], r11
        ror     rbx, 0x1c
        mov     r11, QWORD PTR [rsp-0x20]
        xor     rdi, rsi
        mov     QWORD PTR [rsp-0x38], r9
        xor     r8, rax
        mov     r9, QWORD PTR [rsp]
        rol     rdi, 1
        rol     r8, 0x6
        xor     r11, rdx
        mov     r10, r8
        rol     r11, 0x19
        xor     r9, rcx
        not     r10
        mov     r13, r11
        rol     r9, 0x8
        and     r10, r11
        not     r13
        xor     r10, rdi
        mov     QWORD PTR [rsp-0x48], r10
        mov     r10, r13
        mov     r13, r9
        and     r10, r9
        not     r13
        xor     r10, r8
        mov     QWORD PTR [rsp], r10
        mov     r10, r13
        and     r10, r14
        xor     r10, r11
        mov     r11, r14
        not     r11
        and     r11, rdi
        not     rdi
        and     rdi, r8
        xor     r11, r9
        mov     r8, QWORD PTR [rsp-0x60]
        mov     r9, QWORD PTR [rsp-0x28]
        xor     rdi, r14
        mov     QWORD PTR [rsp-0x20], r11
        mov     r14, QWORD PTR [rsp-0x68]
        mov     QWORD PTR [rsp+0x48], rdi
        mov     rdi, QWORD PTR [rsp-0x8]
        xor     r8, rcx
        xor     r9, rsi
        rol     r9, 0xa
        rol     r8, 0x1b
        xor     rdi, rax
        xor     rax, r14
        mov     r14, QWORD PTR [rsp-0x40]
        mov     r12, rdi
        mov     rdi, QWORD PTR [rsp+0x10]
        ror     rax, 0x2
        rol     r12, 0xf
        xor     rdi, rdx
        mov     r13, r12
        xor     rdx, r14
        mov     r14, QWORD PTR [rsp-0x18]
        mov     r11, rdi
        mov     rdi, rbx
        not     r13
        ror     rdx, 0x9
        not     rdi
        ror     r11, 0x8
        xor     rcx, r14
        and     rdi, r9
        and     r13, r11
        ror     rcx, 0x19
        xor     rdi, r8
        xor     r13, r9
        mov     QWORD PTR [rsp+0x10], rdi
        mov     rdi, r9
        mov     r9, r11
        not     r9
        not     rdi
        and     r9, r8
        not     r8
        and     rdi, r12
        and     r8, rbx
        xor     rdi, rbx
        xor     r9, r12
        mov     r12, QWORD PTR [rsp+0x20]
        xor     r8, r11
        mov     r11, rcx
        mov     rcx, QWORD PTR [rsp-0x10]
        mov     QWORD PTR [rsp-0x28], r8
        xor     rbp, rcx
        mov     rcx, QWORD PTR [rsp+0x8]
        ror     rbp, 0x17
        xor     rsi, rcx
        mov     rcx, rdx
        rol     rsi, 0x2
        not     rcx
        mov     r8, rsi
        mov     rsi, r11
        and     rcx, r11
        not     rsi
        mov     r14, r8
        xor     rcx, rax
        and     rsi, rbp
        not     r14
        mov     QWORD PTR [rsp-0x18], rcx
        xor     rsi, rdx
        mov     rbx, rsi
        mov     rsi, rbp
        not     rsi
        mov     QWORD PTR [rsp+0x8], rbx
        and     rsi, r8
        xor     rsi, r11
        mov     r11, r14
        and     r11, rax
        not     rax
        mov     r14, r11
        xor     r14, rbp
        and     rax, rdx
        mov     rbp, QWORD PTR [rsp+0x10]
        mov     rdx, QWORD PTR [rsp]
        xor     rax, r8
        mov     r8, QWORD PTR [rsp+0x38]
        mov     QWORD PTR [rsp-0x10], r14
        mov     r14, QWORD PTR [rsp-0x48]
        xor     r8, r15
        xor     r8, r14
        xor     r8, rbp
        mov     rbp, QWORD PTR [rsp+0x28]
        xor     r8, rcx
        mov     rcx, QWORD PTR [rsp+0x18]
        xor     r12, rcx
        xor     r12, rdx
        mov     rdx, QWORD PTR [rsp-0x30]
        mov     r11, QWORD PTR [rsp-0x50]
        mov     QWORD PTR [rsp-0x8], r13
        xor     r12, rdi
        mov     r14, QWORD PTR [rsp-0x10]
        xor     rbp, rdx
        xor     r12, rbx
        mov     rbx, QWORD PTR [rsp+0x40]
        mov     rdx, QWORD PTR [rsp-0x38]
        xor     rbp, r10
        xor     rbp, r13
        mov     r13, QWORD PTR [rsp-0x20]
        xor     r11, rbx
        mov     rbx, QWORD PTR [rsp+0x48]
        xor     rbp, rsi
        xor     r11, r13
        xor     rdx, rbx
        mov     rbx, QWORD PTR [rsp+0x30]
        mov     r13, rbp
        xor     r11, r9
        rol     r13, 1
        xor     r11, r14
        mov     r14, QWORD PTR [rsp-0x28]
        xor     rdx, rbx
        xor     r13, r8
        mov     rbx, r11
        rol     r8, 1
        xor     rdx, r14
        mov     r14, r12
        rol     rbx, 1
        xor     r8, r11
        xor     rdx, rax
        rol     r14, 1
        xor     rbx, r12
        xor     r14, rdx
        rol     rdx, 1
        xor     rdx, rbp
        mov     rbp, rcx
        xor     r15, r14
        xor     r10, rbx
        xor     rbp, r13
        mov     r11, r15
        ror     r10, 0x15
        xor     r9, rdx
        ror     rbp, 0x14
        rol     r9, 0x15
        xor     rax, r8
        xor     rdi, r13
        rol     rax, 0xe
        mov     r15, rbp
        ror     rdi, 0x13
        xor     rsi, rbx
        not     r15
        ror     rsi, 0x3
        mov     r12, r15
        mov     r15, QWORD PTR [rsp-0x78]
        and     r12, r10
        mov     rcx, QWORD PTR [r15+0x8]
        xor     rcx, r11
        mov     r15, rcx
        mov     rcx, QWORD PTR [rsp-0x18]
        xor     r15, r12
        mov     r12, r10
        not     r12
        and     r12, r9
        xor     r12, rbp
        mov     QWORD PTR [rsp-0x70], r12
        mov     r12, r9
        not     r12
        and     r12, rax
        xor     r12, r10
        mov     r10, rax
        not     r10
        mov     QWORD PTR [rsp-0x68], r12
        mov     r12, QWORD PTR [rsp+0x20]
        and     r10, r11
        not     r11
        and     r11, rbp
        xor     r10, r9
        mov     r9, QWORD PTR [rsp-0x38]
        xor     r11, rax
        mov     QWORD PTR [rsp+0x18], r10
        mov     r10, QWORD PTR [rsp-0x48]
        mov     QWORD PTR [rsp-0x60], r11
        mov     r11, QWORD PTR [rsp-0x50]
        xor     r9, r8
        rol     r9, 0x14
        xor     r10, r14
        xor     r11, rdx
        rol     r10, 0x3
        mov     rax, r11
        mov     r11, r9
        not     r11
        rol     rax, 0x1c
        and     r11, r10
        xor     r11, rax
        mov     QWORD PTR [rsp-0x58], r11
        mov     r11, r10
        not     r11
        and     r11, rdi
        xor     r12, r13
        xor     rcx, r14
        xor     r11, r9
        rol     rcx, 0x12
        mov     QWORD PTR [rsp-0x50], r11
        mov     r11, rdi
        not     r11
        and     r11, rsi
        xor     r11, r10
        mov     r10, rsi
        not     r10
        mov     QWORD PTR [rsp-0x48], r11
        and     r10, rax
        not     rax
        xor     r10, rdi
        and     rax, r9
        mov     rdi, QWORD PTR [rsp-0x20]
        mov     r11, rax
        mov     QWORD PTR [rsp-0x40], r10
        mov     rax, r12
        xor     r11, rsi
        xor     rdi, rdx
        mov     rsi, QWORD PTR [rsp-0x30]
        rol     rax, 1
        mov     r9, rdi
        mov     rdi, QWORD PTR [rsp-0x28]
        mov     QWORD PTR [rsp-0x38], r11
        xor     rsi, rbx
        rol     r9, 0x19
        rol     rsi, 0x6
        xor     rdi, r8
        rol     rdi, 0x8
        mov     r10, rsi
        mov     r12, rdi
        not     r10
        and     r10, r9
        not     r12
        xor     r10, rax
        and     r12, rcx
        mov     QWORD PTR [rsp-0x30], r10
        xor     r12, r9
        mov     r10, r9
        mov     r9, rcx
        not     r9
        not     r10
        and     r9, rax
        not     rax
        and     r10, rdi
        and     rax, rsi
        xor     r9, rdi
        xor     r10, rsi
        mov     rdi, rax
        mov     QWORD PTR [rsp-0x28], r10
        xor     rdi, rcx
        mov     QWORD PTR [rsp-0x20], r9
        mov     QWORD PTR [rsp-0x18], rdi
        mov     rax, QWORD PTR [rsp+0x30]
        mov     rsi, QWORD PTR [rsp+0x38]
        mov     r9, QWORD PTR [rsp]
        mov     r10, QWORD PTR [rsp-0x8]
        xor     rax, r8
        mov     rcx, QWORD PTR [rsp-0x10]
        xor     rsi, r14
        rol     rax, 0x1b
        mov     rbp, QWORD PTR [rsp+0x28]
        ror     rsi, 0x1c
        xor     r9, r13
        xor     r10, rbx
        xor     rcx, rdx
        rol     r10, 0xf
        ror     rcx, 0x8
        mov     rdi, rsi
        xor     rbx, rbp
        rol     r9, 0xa
        mov     r11, r10
        not     rdi
        ror     rbx, 0x2
        not     r11
        and     rdi, r9
        and     r11, rcx
        xor     rdi, rax
        xor     r11, r9
        mov     QWORD PTR [rsp-0x10], rdi
        mov     rdi, r9
        mov     QWORD PTR [rsp-0x8], r11
        mov     r11, rcx
        not     rdi
        not     r11
        and     rdi, r10
        and     r11, rax
        not     rax
        xor     rdi, rsi
        and     rax, rsi
        mov     rsi, QWORD PTR [rsp+0x8]
        xor     r11, r10
        mov     r9, rax
        mov     rax, QWORD PTR [rsp+0x40]
        xor     r9, rcx
        mov     rcx, QWORD PTR [rsp+0x48]
        xor     rsi, r13
        xor     rax, rdx
        mov     rdx, QWORD PTR [rsp+0x10]
        rol     rsi, 0x2
        mov     QWORD PTR [rsp], r9
        xor     rcx, r8
        ror     rax, 0x9
        ror     rcx, 0x19
        xor     rdx, r14
        mov     r14, rax
        mov     r8, rcx
        ror     rdx, 0x17
        not     r14
        not     r8
        and     r14, rcx
        and     r8, rdx
        xor     r14, rbx
        xor     r8, rax
        mov     QWORD PTR [rsp+0x8], r8
        mov     r8, rdx
        not     r8
        and     r8, rsi
        xor     r8, rcx
        mov     rcx, rsi
        not     rcx
        and     rcx, rbx
        not     rbx
        add     QWORD PTR [rsp-0x78], 0x10
        and     rbx, rax
        mov     rax, QWORD PTR [rsp-0x78]
        xor     rcx, rdx
        lea     rdx, [rip+mlk_KeccakF_RoundConstants+0xc0]
        mov     QWORD PTR [rsp+0x10], rcx
        xor     rbx, rsi
        cmp     rdx, rax
        jne     Lmlkem_native_keccakf1600_permute_gcc12_O2_100
        mov     rax, QWORD PTR [rsp+0x50]
        mov     rdx, QWORD PTR [rsp-0x70]
        mov     r13, QWORD PTR [rsp+0x18]
        mov     QWORD PTR [rax+0x8], rdx
        mov     rdx, QWORD PTR [rsp-0x68]
        mov     QWORD PTR [rax], r15
        mov     QWORD PTR [rax+0x10], rdx
        mov     rdx, QWORD PTR [rsp-0x60]
        mov     QWORD PTR [rax+0x18], r13
        mov     QWORD PTR [rax+0x20], rdx
        mov     rdx, QWORD PTR [rsp-0x58]
        mov     QWORD PTR [rax+0x60], r12
        mov     QWORD PTR [rax+0x28], rdx
        mov     rdx, QWORD PTR [rsp-0x50]
        mov     QWORD PTR [rax+0x80], rdi
        mov     QWORD PTR [rax+0x30], rdx
        mov     rdx, QWORD PTR [rsp-0x48]
        mov     QWORD PTR [rax+0x38], rdx
        mov     rdx, QWORD PTR [rsp-0x40]
        mov     QWORD PTR [rax+0x40], rdx
        mov     rdx, QWORD PTR [rsp-0x38]
        mov     QWORD PTR [rax+0x48], rdx
        mov     rdx, QWORD PTR [rsp-0x30]
        mov     QWORD PTR [rax+0x50], rdx
        mov     rdx, QWORD PTR [rsp-0x28]
        mov     QWORD PTR [rax+0x58], rdx
        mov     rdx, QWORD PTR [rsp-0x20]
        mov     QWORD PTR [rax+0x68], rdx
        mov     rdx, QWORD PTR [rsp-0x18]
        mov     QWORD PTR [rax+0x70], rdx
        mov     rdx, QWORD PTR [rsp-0x10]
        mov     QWORD PTR [rax+0x78], rdx
        mov     rdx, QWORD PTR [rsp-0x8]
        mov     QWORD PTR [rax+0x90], r11
        mov     QWORD PTR [rax+0x88], rdx
        mov     rdx, QWORD PTR [rsp+0x8]
        mov     QWORD PTR [rax+0x98], r9
        mov     QWORD PTR [rax+0xa0], r14
        mov     QWORD PTR [rax+0xa8], rdx
        mov     QWORD PTR [rax+0xb0], r8
        mov     QWORD PTR [rax+0xb8], rcx
        mov     QWORD PTR [rax+0xc0], rbx
        add     rsp, 0x58
        pop     rbx
        pop     rbp
        pop     r12
        pop     r13
        pop     r14
        pop     r15
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(mlkem_native_keccakf1600_permute_gcc12_O2)

// The table mlk_KeccakF_RoundConstants from mlkem-native

#if defined(__ELF__)
        .section .rodata
#elif defined(__APPLE__)
        .const_data
#endif
        .balign 32
#if defined(__ELF__)
        .type   mlk_KeccakF_RoundConstants, %object
        .size   mlk_KeccakF_RoundConstants, 192
#endif
mlk_KeccakF_RoundConstants:
        .quad   0x0000000000000001
        .quad   0x0000000000008082
        .quad   0x800000000000808a
        .quad   0x8000000080008000
        .quad   0x000000000000808b
        .quad   0x0000000080000001
        .quad   0x8000000080008081
        .quad   0x8000000000008009
        .quad   0x000000000000008a
        .quad   0x0000000000000088
        .quad   0x0000000080008009
        .quad   0x000000008000000a
        .quad   0x000000008000808b
        .quad   0x800000000000008b
        .quad   0x8000000000008089
        .quad   0x8000000000008003
        .quad   0x8000000000008002
        .quad   0x8000000000000080
        .quad   0x000000000000800a
        .quad   0x800000008000000a
        .quad   0x8000000080008081
        .quad   0x8000000000008080
        .quad   0x0000000080000001
        .quad   0x8000000080008008

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack, "", %progbits
#endif
