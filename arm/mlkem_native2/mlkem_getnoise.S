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
// Standard ARM ABI: X0 = r, X1 = sigma, X2 = nonce0, X3 = n, X4 = n1,
// X5 = eta1, X6 = c (the constants block: rc is used)
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_arm.h"
#include "mlkem_native2_consts.h"

        S2N_BN_SYM_VISIBILITY_DIRECTIVE(mlkem_getnoise)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(mlkem_getnoise)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(mlkem_getnoise)
        .text
        .balign 4

// The stack frame: the saved registers, the x4 Keccak state (four 200-byte
// lanes), a 192-byte buffer for each lane (for eta = 3), and for each lane
// the index of its current polynomial (-1 if none) and the number of its
// blocks done.

#define SAVE 0
#define ST 96
#define BUF 896
#define CUR 1664
#define BLK 1696
#define FRAME 1728

// Registers held across calls

#define r x19
#define sigma x20
#define nonce0 x21
#define n x22
#define n1 x23
#define eta1 x24
#define c x25
#define next x26
#define lane x27
#define busy x28

#define SHAKE256_DS 0x1f

// initlane l, nonce: set lane l (a register) to the absorbed seed
// sigma || nonce (a register), the domain byte 0x1f, zeros and the final
// bit 0x80 in byte 135. This uses x0-x2 and v0-v1.

        .macro initlane l, nonce
        mov     x0, #200
        mul     x0, \l, x0
        add     x0, x0, #ST
        add     x0, sp, x0
        and     x1, \nonce, #0xff
        orr     x1, x1, #(SHAKE256_DS << 8)
        ldp     q0, q1, [sigma]
        stp     q0, q1, [x0]
        stp     x1, xzr, [x0, #32]
        movi    v0.2d, #0
        stp     q0, q0, [x0, #48]
        stp     q0, q0, [x0, #80]
        stp     xzr, xzr, [x0, #112]
        mov     x1, #0x8000000000000000
        stp     x1, xzr, [x0, #128]
        stp     q0, q0, [x0, #144]
        stp     xzr, xzr, [x0, #176]
        str     xzr, [x0, #192]
        .endm

S2N_BN_SYMBOL(mlkem_getnoise):
        CFI_START
        AARCH64_VALID_CALL_TARGET
        CFI_DEC_SP(FRAME)
        CFI_STACKSAVE2X(x19,x20,SAVE,SAVE+8)
        CFI_STACKSAVE2X(x21,x22,SAVE+16,SAVE+24)
        CFI_STACKSAVE2X(x23,x24,SAVE+32,SAVE+40)
        CFI_STACKSAVE2X(x25,x26,SAVE+48,SAVE+56)
        CFI_STACKSAVE2X(x27,x28,SAVE+64,SAVE+72)
        CFI_STACKSAVE2X(x29,x30,SAVE+80,SAVE+88)

        mov     r, x0
        mov     sigma, x1
        mov     nonce0, x2
        mov     n, x3
        mov     n1, x4
        mov     eta1, x5
        mov     c, x6
        mov     next, #0

        mov     x0, #-1
        add     x9, sp, #CUR
        stp     x0, x0, [x9]
        stp     x0, x0, [x9, #16]

// Each pass: give each free lane the next polynomial, initializing it with
// the absorbed seed, permute (x1 if only one lane is busy, otherwise x4),
// and then finish or advance each busy lane.

Lmlkem_getnoise_loop:
        mov     busy, #0
        mov     lane, #0
Lmlkem_getnoise_assign:
        add     x9, sp, #CUR
        ldr     x0, [x9, lane, lsl #3]
        tbz     x0, #63, Lmlkem_getnoise_assigned
        cmp     next, n
        bcs     Lmlkem_getnoise_nextlane
        str     next, [x9, lane, lsl #3]
        add     x10, sp, #BLK
        str     xzr, [x10, lane, lsl #3]
        add     x2, nonce0, next
        initlane lane, x2
        add     next, next, #1
Lmlkem_getnoise_assigned:
        add     busy, busy, #1
Lmlkem_getnoise_nextlane:
        add     lane, lane, #1
        cmp     lane, #4
        bcc     Lmlkem_getnoise_assign

        cbz     busy, Lmlkem_getnoise_end
        cmp     busy, #1
        bne     Lmlkem_getnoise_x4

// Only one lane busy: find it and use the x1 permutation on it

        mov     lane, #0
        add     x9, sp, #CUR
Lmlkem_getnoise_find:
        ldr     x0, [x9, lane, lsl #3]
        tbz     x0, #63, Lmlkem_getnoise_found
        add     lane, lane, #1
        b       Lmlkem_getnoise_find
Lmlkem_getnoise_found:
        mov     x0, #200
        mul     x0, lane, x0
        add     x0, x0, #ST
        add     x0, sp, x0
        add     x1, c, #MLKEM_C_RC
        bl      S2N_BN_SYMBOL(sha3_keccak_f1600)
        b       Lmlkem_getnoise_post
Lmlkem_getnoise_x4:
        add     x0, sp, #ST
        add     x1, c, #MLKEM_C_RC
        bl      S2N_BN_SYMBOL(sha3_keccak4_f1600_alt2)

// For each busy lane: with eta = 2, the coefficients come from the first
// 128 bytes of the lane; with eta = 3, the first 136 bytes are saved and
// then, after the next permutation, 56 more, and the coefficients come
// from the buffer.

Lmlkem_getnoise_post:
        mov     lane, #0
Lmlkem_getnoise_postloop:
        add     x9, sp, #CUR
        ldr     x0, [x9, lane, lsl #3]
        tbnz    x0, #63, Lmlkem_getnoise_postnext
        mov     x1, #2
        cmp     x0, n1
        csel    x1, eta1, x1, cc
        mov     x2, #200
        mul     x2, lane, x2
        add     x2, x2, #ST
        add     x2, sp, x2
        add     x0, r, x0, lsl #9
        cmp     x1, #2
        bne     Lmlkem_getnoise_eta3
        mov     x1, x2
        bl      S2N_BN_SYMBOL(mlkem_cbd2)
        b       Lmlkem_getnoise_done
Lmlkem_getnoise_eta3:
        mov     x3, #192
        mul     x3, lane, x3
        add     x3, x3, #BUF
        add     x3, sp, x3
        add     x10, sp, #BLK
        ldr     x4, [x10, lane, lsl #3]
        cbnz    x4, Lmlkem_getnoise_eta3_second
        ldp     q0, q1, [x2]
        ldp     q2, q3, [x2, #32]
        ldp     q4, q5, [x2, #64]
        ldp     q6, q7, [x2, #96]
        ldr     d16, [x2, #128]
        stp     q0, q1, [x3]
        stp     q2, q3, [x3, #32]
        stp     q4, q5, [x3, #64]
        stp     q6, q7, [x3, #96]
        str     d16, [x3, #128]
        mov     x4, #1
        str     x4, [x10, lane, lsl #3]
        b       Lmlkem_getnoise_postnext
Lmlkem_getnoise_eta3_second:
        ldp     q0, q1, [x2]
        ldp     q2, q3, [x2, #32]
        add     x4, x3, #136
        stp     q0, q1, [x4]
        str     q2, [x4, #32]
        str     d3, [x4, #48]
        mov     x1, x3
        bl      S2N_BN_SYMBOL(mlkem_cbd3)
Lmlkem_getnoise_done:
        add     x9, sp, #CUR
        mov     x0, #-1
        str     x0, [x9, lane, lsl #3]
Lmlkem_getnoise_postnext:
        add     lane, lane, #1
        cmp     lane, #4
        bcc     Lmlkem_getnoise_postloop
        b       Lmlkem_getnoise_loop

// Zero the state and buffers, which are secret, and return

Lmlkem_getnoise_end:
        add     x0, sp, #ST
        mov     x1, #(CUR-ST)
Lmlkem_getnoise_zero:
        stp     xzr, xzr, [x0], #16
        subs    x1, x1, #16
        bne     Lmlkem_getnoise_zero

        CFI_STACKLOAD2(x19,x20,SAVE)
        CFI_STACKLOAD2(x21,x22,SAVE+16)
        CFI_STACKLOAD2(x23,x24,SAVE+32)
        CFI_STACKLOAD2(x25,x26,SAVE+48)
        CFI_STACKLOAD2(x27,x28,SAVE+64)
        CFI_STACKLOAD2(x29,x30,SAVE+80)
        CFI_INC_SP(FRAME)
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(mlkem_getnoise)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack, "", %progbits
#endif
