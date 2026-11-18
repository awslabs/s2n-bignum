// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Sample ML-KEM noise polynomials from a seed
// Inputs sigma[32], nonce0, n, n1, eta1, c; output r[256*n]
//
// For 0 <= i < n, the polynomial r[256 * i ...] is set to
// SamplePolyCBD_eta(PRF_eta(sigma, nonce0 + i)) as in FIPS 203 (Algorithms
// 8 and 9 and section 4.1), i.e. the centered binomial distribution with
// eta = eta1 for i < n1 and eta = 2 otherwise applied to the first
// 64 * eta bytes of SHAKE256(sigma || (nonce0 + i)). The parameter eta1
// must be 2 or 3 and nonce0 + n at most 256. This is mlkem-native's noise
// sampling: mlk_poly_getnoise_eta1_4x and its relatives.
//
// The polynomials are sampled in the lanes of the x4 permutation, each
// lane taking the next polynomial when it is free (a polynomial with
// eta = 3 needs two blocks), with the x1 permutation when only one lane
// is busy. The time taken depends only on n, n1 and eta1, and the Keccak
// state and buffers, which are secret, are zeroed before returning.
//
// extern void mlkem_getnoise(int16_t *r, const uint8_t sigma[32],
//                            uint64_t nonce0, uint64_t n, uint64_t n1,
//                            uint64_t eta1,
//                            const mlkem_native2_consts *c);
//
// Standard x86-64 ABI: RDI = r, RSI = sigma, RDX = nonce0, RCX = n,
// R8 = n1, R9 = eta1, [RSP+8] = c (the constants block: rc and the
// rho8 and rho56 tables of sha3_keccak4_f1600_alt are used)
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_x86.h"
#ifndef MLKEM_NATIVE2_CONSTS_H
#include "mlkem_native2_consts.h"
#endif
#ifndef MLKEM_NATIVE2_NAMES_H
#include "mlkem_native2_names.h"
#endif
#include "mlkem_native2_macros.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(N2(mlkem_getnoise))
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(N2(mlkem_getnoise))
        S2N_BN_SYM_PRIVACY_DIRECTIVE(N2(mlkem_getnoise))
        .text
        .balign 32

// The stack frame, 16-byte aligned after the six pushes: the x4 Keccak
// state (four 200-byte lanes), a 192-byte buffer for each lane (for
// eta = 3), for each lane the index of its current polynomial (-1 if
// none) and the number of its blocks done, and the arguments nonce0, n,
// n1 and eta1. The constants block c is above the frame, as the seventh
// argument.

#define ST 0
#define BUF 800
#define CUR 1568
#define BLK 1600
#define NONCE0 1632
#define NN 1640
#define N1 1648
#define ETA1 1656
#define FRAME 1672
#define ARG7 (FRAME + 56)

// Registers held across calls

#define r rbx
#define sigma rbp
#define next r12
#define lane r13
#define busy r14
#define nextd r12d
#define laned r13d
#define busyd r14d
#define c r15

#define SHAKE256_DS 0x1f

// initlane: set lane `lane` to the absorbed seed sigma || nonce (in al),
// the domain byte 0x1f, zeros and the final bit 0x80 in byte 135. This
// uses rax, rdx and ymm0-ymm1.

        .macro initlane
        imul    rdx, lane, 200
        lea     rdx, [rsp+ST+rdx]
        vmovdqu ymm1, [sigma]
        vmovdqu [rdx], ymm1
        movzx   eax, al
        or      eax, (SHAKE256_DS << 8)
        mov     [rdx+32], rax
        vpxor   xmm0, xmm0, xmm0
        vmovdqu [rdx+40], ymm0
        vmovdqu [rdx+72], ymm0
        vmovdqu [rdx+104], ymm0
        vmovdqu [rdx+136], ymm0
        vmovdqu [rdx+168], ymm0
        mov     BYTE PTR [rdx+135], 0x80
        .endm

S2N_BN_SYMBOL(N2(mlkem_getnoise)):
        CFI_START
        _CET_ENDBR
        CFI_PUSH(rbx)
        CFI_PUSH(rbp)
        CFI_PUSH(r12)
        CFI_PUSH(r13)
        CFI_PUSH(r14)
        CFI_PUSH(r15)
        CFI_DEC_RSP(FRAME)

        mov     r, rdi
        mov     sigma, rsi
        mov     [rsp+NONCE0], rdx
        mov     [rsp+NN], rcx
        mov     [rsp+N1], r8
        mov     [rsp+ETA1], r9
        mov     c, [rsp+ARG7]
        xor     nextd, nextd
        mov     rax, -1
        mov     [rsp+CUR], rax
        mov     [rsp+CUR+8], rax
        mov     [rsp+CUR+16], rax
        mov     [rsp+CUR+24], rax

// Each pass: give each free lane the next polynomial, initializing it with
// the absorbed seed, permute (x1 if only one lane is busy, otherwise x4),
// and then finish or advance each busy lane.

Lmlkem_getnoise_loop:
        xor     busyd, busyd
        xor     laned, laned
Lmlkem_getnoise_assign:
        mov     rax, [rsp+CUR+8*lane]
        test    rax, rax
        jns     Lmlkem_getnoise_assigned
        cmp     next, [rsp+NN]
        jae     Lmlkem_getnoise_nextlane
        mov     [rsp+CUR+8*lane], next
        mov     QWORD PTR [rsp+BLK+8*lane], 0
        mov     rax, [rsp+NONCE0]
        add     rax, next
        initlane
        inc     next
Lmlkem_getnoise_assigned:
        inc     busy
Lmlkem_getnoise_nextlane:
        inc     lane
        cmp     lane, 4
        jb      Lmlkem_getnoise_assign

        test    busy, busy
        jz      Lmlkem_getnoise_end
        cmp     busy, 1
        jne     Lmlkem_getnoise_x4

// Only one lane busy: find it and use the x1 permutation on it

        xor     laned, laned
Lmlkem_getnoise_find:
        cmp     QWORD PTR [rsp+CUR+8*lane], 0
        jge     Lmlkem_getnoise_found
        inc     lane
        jmp     Lmlkem_getnoise_find
Lmlkem_getnoise_found:
        imul    rdi, lane, 200
        lea     rdi, [rsp+ST+rdi]
        leadisp rsi, c, MLKEM_C_RC
        call    S2N_BN_SYMBOL(N2_KECCAK_X1)
        jmp     Lmlkem_getnoise_post
Lmlkem_getnoise_x4:
        leadisp rdi, rsp, ST
        leadisp rsi, c, MLKEM_C_RC
        lea     rdx, [c+MLKEM_C_KECCAK_RHO8]
        lea     rcx, [c+MLKEM_C_KECCAK_RHO56]
        call    S2N_BN_SYMBOL(N2_KECCAK_X4)

// For each busy lane: with eta = 2, the coefficients come from the first
// 128 bytes of the lane; with eta = 3, the first 136 bytes are saved and
// then, after the next permutation, 56 more, and the coefficients come
// from the buffer.

Lmlkem_getnoise_post:
        xor     laned, laned
Lmlkem_getnoise_postloop:
        mov     rax, [rsp+CUR+8*lane]
        test    rax, rax
        js      Lmlkem_getnoise_postnext
        mov     ecx, 2
        cmp     rax, [rsp+N1]
        cmovb   rcx, [rsp+ETA1]
        shl     rax, 9
        lea     rdi, [r+rax]
        imul    rsi, lane, 200
        lea     rsi, [rsp+ST+rsi]
        cmp     rcx, 2
        jne     Lmlkem_getnoise_eta3
        call    S2N_BN_SYMBOL(mlkem_cbd2)
        jmp     Lmlkem_getnoise_done
Lmlkem_getnoise_eta3:
        imul    rdx, lane, 192
        lea     rdx, [rsp+BUF+rdx]
        cmp     QWORD PTR [rsp+BLK+8*lane], 0
        jne     Lmlkem_getnoise_eta3_second
        vmovdqu ymm0, [rsi]
        vmovdqu [rdx], ymm0
        vmovdqu ymm0, [rsi+32]
        vmovdqu [rdx+32], ymm0
        vmovdqu ymm0, [rsi+64]
        vmovdqu [rdx+64], ymm0
        vmovdqu ymm0, [rsi+96]
        vmovdqu [rdx+96], ymm0
        mov     rax, [rsi+128]
        mov     [rdx+128], rax
        mov     QWORD PTR [rsp+BLK+8*lane], 1
        jmp     Lmlkem_getnoise_postnext
Lmlkem_getnoise_eta3_second:
        vmovdqu ymm0, [rsi]
        vmovdqu [rdx+136], ymm0
        vmovdqu xmm0, [rsi+32]
        vmovdqu [rdx+168], xmm0
        mov     rax, [rsi+48]
        mov     [rdx+184], rax
        mov     rsi, rdx
        call    S2N_BN_SYMBOL(mlkem_cbd3)
Lmlkem_getnoise_done:
        mov     QWORD PTR [rsp+CUR+8*lane], -1
Lmlkem_getnoise_postnext:
        inc     lane
        cmp     lane, 4
        jb      Lmlkem_getnoise_postloop
        jmp     Lmlkem_getnoise_loop

// Zero the state and buffers, which are secret, and return

Lmlkem_getnoise_end:
        vpxor   xmm0, xmm0, xmm0
        leadisp rdi, rsp, ST
        mov     ecx, ((CUR - ST) / 128)
Lmlkem_getnoise_zero:
        vmovdqu [rdi], ymm0
        vmovdqu [rdi+32], ymm0
        vmovdqu [rdi+64], ymm0
        vmovdqu [rdi+96], ymm0
        add     rdi, 128
        dec     ecx
        jnz     Lmlkem_getnoise_zero
        .if ((CUR - ST) % 32) != 0
        .error  "the state and buffers must be a multiple of 32 bytes"
        .endif
        .set    i, 0
        .rept   (((CUR - ST) % 128) / 32)
        vmovdqu [rdi+i], ymm0
        .set    i, i + 32
        .endr
        vzeroupper

        CFI_INC_RSP(FRAME)
        CFI_POP(r15)
        CFI_POP(r14)
        CFI_POP(r13)
        CFI_POP(r12)
        CFI_POP(rbp)
        CFI_POP(rbx)
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(N2(mlkem_getnoise))

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
