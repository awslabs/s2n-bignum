// Copyright (c) 2022 Arm Limited
// Copyright (c) 2022 Hanno Becker
// Copyright (c) 2023 Amin Abdulrahman, Matthias Kannwischer
// Copyright (c) 2024 The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT

// ----------------------------------------------------------------------------
// Inverse number-theoretic transform from ML-KEM
// Input a[256] (signed 16-bit words); output a[256] (signed 16-bit words).
//
// The transform is in-place, with the input in bitreversed order and the
// output mapped into the Montgomery domain via x |-> (2^16 * x) mod 3329.
//
// extern void mlkem_intt(int16_t a[256]);
//
// Standard ARM ABI: X0 = a
// ----------------------------------------------------------------------------
#include "_internal_s2n_bignum.h"

        S2N_BN_SYM_VISIBILITY_DIRECTIVE(mlkem_intt)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(mlkem_intt)
        .text
        .balign 4

S2N_BN_SYMBOL(mlkem_intt):

// This implementation is a slightly tweaked form of the code generated
// by SLOTHY, set up to optimize for the Neoverse N1 microarchitecture,
// starting from this clean version:
//
//   https://github.com/pq-code-package/mlkem-native/blob/main/mlkem/native/aarch64/intt_clean.S
//
// Relative to the original, the main changes are as follows:
//
// * Moved constants to the end (to match ELF parser expectations)
//
// * Changed "adrp" to plain "adr" (to avoid bringing in relocations)
//
// * Emulated ld1 and ld1r (to avoid formalizing them in the model).
//
// * Added the constants roots_... at the end too, from separate file
//
// * Used .hword in place of .short since it seems better defined

        sub     sp, sp, #0x40
        stp     d8, d9, [sp]
        stp     d10, d11, [sp, #16]
        stp     d12, d13, [sp, #32]
        stp     d14, d15, [sp, #48]

        adr     x1, roots_l34
        adr     x2, roots_l56
        dup     v7.8h, wzr
        mov     w5, 0x0d01
        mov     v7.h[0], w5
        mov     w5, 0x4ebf
        mov     v7.h[1], w5
        mov     w5, 0x0200
        dup     v29.8h, w5
        mov     w5, 0x13b0
        dup     v30.8h, w5
        mov     x3, x0
        mov     x4, #0x8

scale_start:
        ldr     q8, [x3]
        ldr     q9, [x3, #16]
        ldr     q10, [x3, #32]
        ldr     q11, [x3, #48]
        sqrdmulh v27.8h, v8.8h, v30.8h
        mul     v8.8h, v8.8h, v29.8h
        mls     v8.8h, v27.8h, v7.h[0]
        sqrdmulh v27.8h, v9.8h, v30.8h
        mul     v9.8h, v9.8h, v29.8h
        mls     v9.8h, v27.8h, v7.h[0]
        sqrdmulh v27.8h, v10.8h, v30.8h
        mul     v10.8h, v10.8h, v29.8h
        mls     v10.8h, v27.8h, v7.h[0]
        sqrdmulh v27.8h, v11.8h, v30.8h
        mul     v11.8h, v11.8h, v29.8h
        mls     v11.8h, v27.8h, v7.h[0]
        str     q8, [x3], #64
        stur    q9, [x3, #-48]
        stur    q10, [x3, #-32]
        stur    q11, [x3, #-16]
        subs    x4, x4, #0x1
        cbnz    x4, scale_start

        mov     x3, x0
        mov     x4, #0x8
        ldr     q27, [x3, #32]
        ldr     q13, [x3, #48]
        ldr     q2, [x3]
        ldr     q28, [x3, #16]
        ldr     q9, [x2, #48]
        ldr     q22, [x2, #16]
        ldr     q17, [x2, #64]
        ldr     q14, [x2, #80]
        trn1    v23.4s, v27.4s, v13.4s
        trn2    v27.4s, v27.4s, v13.4s
        trn1    v13.4s, v2.4s, v28.4s
        trn2    v2.4s, v2.4s, v28.4s
        ldr     q28, [x2, #32]
        ldr     q4, [x2], #96
        trn2    v24.2d, v13.2d, v23.2d
        trn2    v15.2d, v2.2d, v27.2d
        trn1    v13.2d, v13.2d, v23.2d
        trn1    v27.2d, v2.2d, v27.2d
        add     v2.8h, v24.8h, v15.8h
        sub     v23.8h, v24.8h, v15.8h
        add     v24.8h, v13.8h, v27.8h
        sub     v27.8h, v13.8h, v27.8h
        ldr     q15, [x1], #16
        mul     v17.8h, v23.8h, v17.8h
        sqrdmulh v13.8h, v27.8h, v9.8h
        sqrdmulh v14.8h, v23.8h, v14.8h
        mul     v27.8h, v27.8h, v28.8h
        mls     v27.8h, v13.8h, v7.h[0]
        sub     v9.8h, v24.8h, v2.8h
        mls     v17.8h, v14.8h, v7.h[0]
        sqrdmulh v13.8h, v9.8h, v22.8h
        add     v2.8h, v24.8h, v2.8h
        mul     v28.8h, v9.8h, v4.8h
        sub     v9.8h, v27.8h, v17.8h
        add     v27.8h, v27.8h, v17.8h
        sqrdmulh v22.8h, v9.8h, v22.8h
        trn1    v17.4s, v2.4s, v27.4s
        mul     v9.8h, v9.8h, v4.8h
        trn2    v10.4s, v2.4s, v27.4s
        mls     v28.8h, v13.8h, v7.h[0]
        mls     v9.8h, v22.8h, v7.h[0]
        trn2    v2.4s, v28.4s, v9.4s
        trn1    v13.4s, v28.4s, v9.4s
        trn2    v22.2d, v17.2d, v13.2d
        trn2    v28.2d, v10.2d, v2.2d
        trn1    v9.2d, v17.2d, v13.2d
        sub     v27.8h, v22.8h, v28.8h
        trn1    v18.2d, v10.2d, v2.2d
        add     v14.8h, v22.8h, v28.8h
        sqrdmulh v20.8h, v27.8h, v15.h[5]
        mul     v21.8h, v27.8h, v15.h[4]
        sub     x4, x4, #0x1

layer4567_start:
        sqdmulh v23.8h, v14.8h, v7.h[1]
        sub     v26.8h, v9.8h, v18.8h
        ldr     q6, [x3, #96]
        ldr     q28, [x3, #112]
        mls     v21.8h, v20.8h, v7.h[0]
        ldr     q11, [x3, #64]
        ldr     q5, [x3, #80]
        ldr     q25, [x2, #16]
        add     v13.8h, v9.8h, v18.8h
        sqrdmulh v10.8h, v26.8h, v15.h[3]
        trn1    v29.4s, v6.4s, v28.4s
        ldr     q16, [x2, #48]
        trn2    v1.4s, v6.4s, v28.4s
        mul     v17.8h, v26.8h, v15.h[2]
        trn1    v18.4s, v11.4s, v5.4s
        ldr     q9, [x2, #64]
        trn2    v30.4s, v11.4s, v5.4s
        sqdmulh v20.8h, v13.8h, v7.h[1]
        trn2    v26.2d, v18.2d, v29.2d
        ldr     q27, [x2, #80]
        mls     v17.8h, v10.8h, v7.h[0]
        trn2    v24.2d, v30.2d, v1.2d
        trn1    v31.2d, v18.2d, v29.2d
        ldr     q12, [x2, #32]
        sub     v19.8h, v26.8h, v24.8h
        sqdmulh v11.8h, v21.8h, v7.h[1]
        trn1    v0.2d, v30.2d, v1.2d
        sqrdmulh v6.8h, v19.8h, v27.8h
        sub     v10.8h, v31.8h, v0.8h
        srshr   v2.8h, v20.8h, #11
        sqdmulh v8.8h, v17.8h, v7.h[1]
        add     v31.8h, v31.8h, v0.8h
        ldr     q0, [x2], #96
        sqrdmulh v29.8h, v10.8h, v16.8h
        add     v27.8h, v26.8h, v24.8h
        srshr   v3.8h, v11.8h, #11
        mul     v22.8h, v10.8h, v12.8h
        sub     v28.8h, v31.8h, v27.8h
        add     v4.8h, v31.8h, v27.8h
        srshr   v8.8h, v8.8h, #11
        sqrdmulh v10.8h, v28.8h, v25.8h
        srshr   v12.8h, v23.8h, #11
        mls     v22.8h, v29.8h, v7.h[0]
        mls     v17.8h, v8.8h, v7.h[0]
        mls     v21.8h, v3.8h, v7.h[0]
        mul     v27.8h, v19.8h, v9.8h
        mls     v27.8h, v6.8h, v7.h[0]
        mls     v13.8h, v2.8h, v7.h[0]
        mls     v14.8h, v12.8h, v7.h[0]
        mul     v9.8h, v28.8h, v0.8h
        sub     v8.8h, v22.8h, v27.8h
        add     v23.8h, v22.8h, v27.8h
        sqrdmulh v5.8h, v8.8h, v25.8h
        sub     v1.8h, v13.8h, v14.8h
        mul     v25.8h, v8.8h, v0.8h
        add     v2.8h, v13.8h, v14.8h
        trn1    v0.4s, v4.4s, v23.4s
        mls     v9.8h, v10.8h, v7.h[0]
        trn2    v10.4s, v4.4s, v23.4s
        mls     v25.8h, v5.8h, v7.h[0]
        sqrdmulh v19.8h, v1.8h, v15.h[1]
        mul     v16.8h, v1.8h, v15.h[0]
        sub     v6.8h, v17.8h, v21.8h
        trn1    v31.4s, v9.4s, v25.4s
        trn2    v4.4s, v9.4s, v25.4s
        sqrdmulh v12.8h, v6.8h, v15.h[1]
        trn1    v9.2d, v0.2d, v31.2d
        mls     v16.8h, v19.8h, v7.h[0]
        trn2    v23.2d, v10.2d, v4.2d
        trn2    v8.2d, v0.2d, v31.2d
        mul     v27.8h, v6.8h, v15.h[0]
        ldr     q15, [x1], #16
        trn1    v18.2d, v10.2d, v4.2d
        mls     v27.8h, v12.8h, v7.h[0]
        sub     v6.8h, v8.8h, v23.8h
        add     v10.8h, v17.8h, v21.8h
        str     q16, [x3, #32]
        add     v14.8h, v8.8h, v23.8h
        sqrdmulh v20.8h, v6.8h, v15.h[5]
        str     q10, [x3, #16]
        str     q2, [x3], #64
        mul     v21.8h, v6.8h, v15.h[4]
        stur    q27, [x3, #-16]
        sub     x4, x4, #0x1
        cbnz    x4, layer4567_start

        mls     v21.8h, v20.8h, v7.h[0]
        sub     v27.8h, v9.8h, v18.8h
        add     v30.8h, v9.8h, v18.8h
        sqrdmulh v10.8h, v27.8h, v15.h[3]
        mul     v28.8h, v27.8h, v15.h[2]
        sqdmulh v27.8h, v14.8h, v7.h[1]
        mls     v28.8h, v10.8h, v7.h[0]
        sqdmulh v10.8h, v30.8h, v7.h[1]
        srshr   v27.8h, v27.8h, #11
        sqdmulh v13.8h, v21.8h, v7.h[1]
        sqdmulh v22.8h, v28.8h, v7.h[1]
        srshr   v25.8h, v10.8h, #11
        srshr   v24.8h, v13.8h, #11
        mls     v14.8h, v27.8h, v7.h[0]
        mls     v30.8h, v25.8h, v7.h[0]
        srshr   v2.8h, v22.8h, #11
        mls     v21.8h, v24.8h, v7.h[0]
        mls     v28.8h, v2.8h, v7.h[0]
        sub     v25.8h, v30.8h, v14.8h
        add     v27.8h, v30.8h, v14.8h
        sqrdmulh v3.8h, v25.8h, v15.h[1]
        str     q27, [x3], #64
        sub     v27.8h, v28.8h, v21.8h
        mul     v13.8h, v25.8h, v15.h[0]
        add     v2.8h, v28.8h, v21.8h
        sqrdmulh v31.8h, v27.8h, v15.h[1]
        mul     v27.8h, v27.8h, v15.h[0]
        mls     v13.8h, v3.8h, v7.h[0]
        mls     v27.8h, v31.8h, v7.h[0]
        stur    q2, [x3, #-48]
        stur    q13, [x3, #-32]
        stur    q27, [x3, #-16]
        mov     x4, #0x4
        ldr     q0, [x1], #32
        ldur    q1, [x1, #-16]
        ldr     q13, [x0, #448]
        ldr     q2, [x0, #384]
        ldr     q8, [x0, #192]
        ldr     q12, [x0, #256]
        ldr     q23, [x0, #64]
        sub     v26.8h, v2.8h, v13.8h
        ldr     q27, [x0, #320]
        add     v13.8h, v2.8h, v13.8h
        ldr     q20, [x0]
        sqrdmulh v28.8h, v26.8h, v1.h[5]
        ldr     q14, [x0, #128]
        mul     v18.8h, v26.8h, v1.h[4]
        sub     v2.8h, v12.8h, v27.8h
        add     v3.8h, v20.8h, v23.8h
        add     v26.8h, v14.8h, v8.8h
        sqrdmulh v31.8h, v2.8h, v1.h[3]
        sub     v11.8h, v3.8h, v26.8h
        mls     v18.8h, v28.8h, v7.h[0]
        mul     v29.8h, v2.8h, v1.h[2]
        mls     v29.8h, v31.8h, v7.h[0]
        mul     v22.8h, v11.8h, v0.h[2]
        sub     v31.8h, v29.8h, v18.8h
        sqrdmulh v28.8h, v31.8h, v0.h[5]
        mul     v4.8h, v31.8h, v0.h[4]
        sub     x4, x4, #0x1

layer123_start:
        sqrdmulh v15.8h, v11.8h, v0.h[3]
        sub     v31.8h, v20.8h, v23.8h
        sub     v2.8h, v14.8h, v8.8h
        mul     v9.8h, v31.8h, v0.h[6]
        ldr     q24, [x0, #400]
        add     v30.8h, v12.8h, v27.8h
        ldr     q17, [x0, #464]
        sqrdmulh v11.8h, v2.8h, v1.h[1]
        add     v6.8h, v30.8h, v13.8h
        add     v25.8h, v3.8h, v26.8h
        sqrdmulh v27.8h, v31.8h, v0.h[7]
        ldr     q8, [x0, #208]
        sub     v14.8h, v24.8h, v17.8h
        mul     v3.8h, v2.8h, v1.h[0]
        mls     v3.8h, v11.8h, v7.h[0]
        sub     v16.8h, v25.8h, v6.8h
        sub     v26.8h, v30.8h, v13.8h
        mls     v9.8h, v27.8h, v7.h[0]
        ldr     q27, [x0, #336]
        mul     v30.8h, v16.8h, v0.h[0]
        mls     v4.8h, v28.8h, v7.h[0]
        add     v28.8h, v29.8h, v18.8h
        add     v19.8h, v9.8h, v3.8h
        sub     v3.8h, v9.8h, v3.8h
        sqrdmulh v13.8h, v16.8h, v0.h[1]
        sub     v23.8h, v19.8h, v28.8h
        add     v16.8h, v19.8h, v28.8h
        sqrdmulh v12.8h, v3.8h, v0.h[3]
        mul     v10.8h, v3.8h, v0.h[2]
        str     q16, [x0, #64]
        mls     v30.8h, v13.8h, v7.h[0]
        mls     v10.8h, v12.8h, v7.h[0]
        ldr     q12, [x0, #272]
        mls     v22.8h, v15.8h, v7.h[0]
        str     q30, [x0, #256]
        sqrdmulh v2.8h, v14.8h, v1.h[5]
        sub     v15.8h, v12.8h, v27.8h
        add     v30.8h, v25.8h, v6.8h
        add     v25.8h, v10.8h, v4.8h
        sqrdmulh v9.8h, v26.8h, v0.h[5]
        sub     v13.8h, v10.8h, v4.8h
        str     q25, [x0, #192]
        mul     v18.8h, v14.8h, v1.h[4]
        mul     v31.8h, v23.8h, v0.h[0]
        sqrdmulh v10.8h, v23.8h, v0.h[1]
        ldr     q23, [x0, #80]
        sqrdmulh v20.8h, v13.8h, v0.h[1]
        mls     v18.8h, v2.8h, v7.h[0]
        mul     v5.8h, v26.8h, v0.h[4]
        mul     v14.8h, v13.8h, v0.h[0]
        mls     v14.8h, v20.8h, v7.h[0]
        mls     v5.8h, v9.8h, v7.h[0]
        sqrdmulh v9.8h, v15.8h, v1.h[3]
        ldr     q20, [x0, #16]
        mls     v31.8h, v10.8h, v7.h[0]
        str     q14, [x0, #448]
        ldr     q14, [x0, #144]
        sub     v10.8h, v22.8h, v5.8h
        mul     v29.8h, v15.8h, v1.h[2]
        add     v13.8h, v22.8h, v5.8h
        str     q30, [x0], #16
        mls     v29.8h, v9.8h, v7.h[0]
        str     q13, [x0, #112]
        str     q31, [x0, #304]
        add     v26.8h, v14.8h, v8.8h
        add     v3.8h, v20.8h, v23.8h
        sqrdmulh v28.8h, v10.8h, v0.h[1]
        mul     v21.8h, v10.8h, v0.h[0]
        sub     v11.8h, v3.8h, v26.8h
        sub     v13.8h, v29.8h, v18.8h
        mul     v22.8h, v11.8h, v0.h[2]
        mls     v21.8h, v28.8h, v7.h[0]
        sqrdmulh v28.8h, v13.8h, v0.h[5]
        mul     v4.8h, v13.8h, v0.h[4]
        add     v13.8h, v24.8h, v17.8h
        str     q21, [x0, #368]
        sub     x4, x4, #0x1
        cbnz    x4, layer123_start

        sqrdmulh v2.8h, v11.8h, v0.h[3]
        sub     v9.8h, v20.8h, v23.8h
        sub     v17.8h, v14.8h, v8.8h
        add     v27.8h, v12.8h, v27.8h
        mls     v4.8h, v28.8h, v7.h[0]
        add     v28.8h, v3.8h, v26.8h
        add     v14.8h, v29.8h, v18.8h
        mul     v23.8h, v9.8h, v0.h[6]
        add     v24.8h, v27.8h, v13.8h
        sub     v27.8h, v27.8h, v13.8h
        mls     v22.8h, v2.8h, v7.h[0]
        sub     v13.8h, v28.8h, v24.8h
        sqrdmulh v2.8h, v9.8h, v0.h[7]
        add     v28.8h, v28.8h, v24.8h
        str     q28, [x0], #16
        sqrdmulh v28.8h, v17.8h, v1.h[1]
        mul     v9.8h, v17.8h, v1.h[0]
        mul     v17.8h, v13.8h, v0.h[0]
        mls     v9.8h, v28.8h, v7.h[0]
        mls     v23.8h, v2.8h, v7.h[0]
        sqrdmulh v13.8h, v13.8h, v0.h[1]
        sqrdmulh v2.8h, v27.8h, v0.h[5]
        add     v28.8h, v23.8h, v9.8h
        mul     v27.8h, v27.8h, v0.h[4]
        sub     v9.8h, v23.8h, v9.8h
        sub     v23.8h, v28.8h, v14.8h
        add     v28.8h, v28.8h, v14.8h
        sqrdmulh v14.8h, v9.8h, v0.h[3]
        mls     v27.8h, v2.8h, v7.h[0]
        str     q28, [x0, #48]
        mul     v2.8h, v9.8h, v0.h[2]
        mls     v2.8h, v14.8h, v7.h[0]
        sub     v28.8h, v22.8h, v27.8h
        add     v27.8h, v22.8h, v27.8h
        mls     v17.8h, v13.8h, v7.h[0]
        str     q27, [x0, #112]
        mul     v27.8h, v23.8h, v0.h[0]
        add     v13.8h, v2.8h, v4.8h
        sub     v2.8h, v2.8h, v4.8h
        sqrdmulh v9.8h, v23.8h, v0.h[1]
        str     q17, [x0, #240]
        str     q13, [x0, #176]
        sqrdmulh v13.8h, v2.8h, v0.h[1]
        mul     v2.8h, v2.8h, v0.h[0]
        mls     v27.8h, v9.8h, v7.h[0]
        sqrdmulh v9.8h, v28.8h, v0.h[1]
        mls     v2.8h, v13.8h, v7.h[0]
        str     q27, [x0, #304]
        mul     v27.8h, v28.8h, v0.h[0]
        mls     v27.8h, v9.8h, v7.h[0]
        str     q2, [x0, #432]
        str     q27, [x0, #368]
        ldp     d8, d9, [sp]
        ldp     d10, d11, [sp, #16]
        ldp     d12, d13, [sp, #32]
        ldp     d14, d15, [sp, #48]
        add     sp, sp, #0x40
        ret

// This is from the file intt_123_45_67_twiddles.S

roots_l56:
          .hword -910
          .hword -910
          .hword -1227
          .hword -1227
          .hword 219
          .hword 219
          .hword 855
          .hword 855
          .hword -8957
          .hword -8957
          .hword -12078
          .hword -12078
          .hword 2156
          .hword 2156
          .hword 8416
          .hword 8416
          .hword 1175
          .hword 1175
          .hword 394
          .hword 394
          .hword -1029
          .hword -1029
          .hword -1212
          .hword -1212
          .hword 11566
          .hword 11566
          .hword 3878
          .hword 3878
          .hword -10129
          .hword -10129
          .hword -11930
          .hword -11930
          .hword -885
          .hword -885
          .hword 1219
          .hword 1219
          .hword 1455
          .hword 1455
          .hword 1607
          .hword 1607
          .hword -8711
          .hword -8711
          .hword 11999
          .hword 11999
          .hword 14322
          .hword 14322
          .hword 15818
          .hword 15818
          .hword -648
          .hword -648
          .hword -1481
          .hword -1481
          .hword 712
          .hword 712
          .hword 682
          .hword 682
          .hword -6378
          .hword -6378
          .hword -14578
          .hword -14578
          .hword 7008
          .hword 7008
          .hword 6713
          .hword 6713
          .hword -886
          .hword -886
          .hword 1179
          .hword 1179
          .hword -1026
          .hword -1026
          .hword -1092
          .hword -1092
          .hword -8721
          .hword -8721
          .hword 11605
          .hword 11605
          .hword -10099
          .hword -10099
          .hword -10749
          .hword -10749
          .hword 554
          .hword 554
          .hword -1143
          .hword -1143
          .hword -403
          .hword -403
          .hword 525
          .hword 525
          .hword 5453
          .hword 5453
          .hword -11251
          .hword -11251
          .hword -3967
          .hword -3967
          .hword 5168
          .hword 5168
          .hword 927
          .hword 927
          .hword -1534
          .hword -1534
          .hword 461
          .hword 461
          .hword -1438
          .hword -1438
          .hword 9125
          .hword 9125
          .hword -15099
          .hword -15099
          .hword 4538
          .hword 4538
          .hword -14155
          .hword -14155
          .hword 735
          .hword 735
          .hword -561
          .hword -561
          .hword -757
          .hword -757
          .hword -319
          .hword -319
          .hword 7235
          .hword 7235
          .hword -5522
          .hword -5522
          .hword -7451
          .hword -7451
          .hword -3140
          .hword -3140
          .hword 863
          .hword 863
          .hword 1230
          .hword 1230
          .hword 556
          .hword 556
          .hword -1063
          .hword -1063
          .hword 8495
          .hword 8495
          .hword 12107
          .hword 12107
          .hword 5473
          .hword 5473
          .hword -10463
          .hword -10463
          .hword -452
          .hword -452
          .hword -807
          .hword -807
          .hword -1435
          .hword -1435
          .hword 1010
          .hword 1010
          .hword -4449
          .hword -4449
          .hword -7943
          .hword -7943
          .hword -14125
          .hword -14125
          .hword 9942
          .hword 9942
          .hword -1645
          .hword -1645
          .hword 780
          .hword 780
          .hword 109
          .hword 109
          .hword 1031
          .hword 1031
          .hword -16192
          .hword -16192
          .hword 7678
          .hword 7678
          .hword 1073
          .hword 1073
          .hword 10148
          .hword 10148
          .hword 1239
          .hword 1239
          .hword -375
          .hword -375
          .hword 1292
          .hword 1292
          .hword -1584
          .hword -1584
          .hword 12196
          .hword 12196
          .hword -3691
          .hword -3691
          .hword 12717
          .hword 12717
          .hword -15592
          .hword -15592
          .hword 1414
          .hword 1414
          .hword -1320
          .hword -1320
          .hword -33
          .hword -33
          .hword 464
          .hword 464
          .hword 13918
          .hword 13918
          .hword -12993
          .hword -12993
          .hword -325
          .hword -325
          .hword 4567
          .hword 4567
          .hword -641
          .hword -641
          .hword 992
          .hword 992
          .hword 941
          .hword 941
          .hword 1021
          .hword 1021
          .hword -6309
          .hword -6309
          .hword 9764
          .hword 9764
          .hword 9262
          .hword 9262
          .hword 10050
          .hword 10050
          .hword -268
          .hword -268
          .hword -733
          .hword -733
          .hword 892
          .hword 892
          .hword -939
          .hword -939
          .hword -2638
          .hword -2638
          .hword -7215
          .hword -7215
          .hword 8780
          .hword 8780
          .hword -9243
          .hword -9243
          .hword -632
          .hword -632
          .hword 816
          .hword 816
          .hword 1352
          .hword 1352
          .hword -650
          .hword -650
          .hword -6221
          .hword -6221
          .hword 8032
          .hword 8032
          .hword 13308
          .hword 13308
          .hword -6398
          .hword -6398
          .hword 642
          .hword 642
          .hword -952
          .hword -952
          .hword 1540
          .hword 1540
          .hword -1651
          .hword -1651
          .hword 6319
          .hword 6319
          .hword -9371
          .hword -9371
          .hword 15159
          .hword 15159
          .hword -16251
          .hword -16251
          .hword -1461
          .hword -1461
          .hword 1482
          .hword 1482
          .hword 540
          .hword 540
          .hword 1626
          .hword 1626
          .hword -14381
          .hword -14381
          .hword 14588
          .hword 14588
          .hword 5315
          .hword 5315
          .hword 16005
          .hword 16005
          .hword 1274
          .hword 1274
          .hword 1052
          .hword 1052
          .hword 1025
          .hword 1025
          .hword -1197
          .hword -1197
          .hword 12540
          .hword 12540
          .hword 10355
          .hword 10355
          .hword 10089
          .hword 10089
          .hword -11782
          .hword -11782
          .hword 279
          .hword 279
          .hword 1173
          .hword 1173
          .hword -233
          .hword -233
          .hword 667
          .hword 667
          .hword 2746
          .hword 2746
          .hword 11546
          .hword 11546
          .hword -2293
          .hword -2293
          .hword 6565
          .hword 6565
          .hword 314
          .hword 314
          .hword -756
          .hword -756
          .hword 48
          .hword 48
          .hword -1409
          .hword -1409
          .hword 3091
          .hword 3091
          .hword -7441
          .hword -7441
          .hword 472
          .hword 472
          .hword -13869
          .hword -13869
          .hword 1573
          .hword 1573
          .hword 76
          .hword 76
          .hword -331
          .hword -331
          .hword -289
          .hword -289
          .hword 15483
          .hword 15483
          .hword 748
          .hword 748
          .hword -3258
          .hword -3258
          .hword -2845
          .hword -2845
          .hword -1100
          .hword -1100
          .hword -723
          .hword -723
          .hword 680
          .hword 680
          .hword 568
          .hword 568
          .hword -10828
          .hword -10828
          .hword -7117
          .hword -7117
          .hword 6693
          .hword 6693
          .hword 5591
          .hword 5591
          .hword 1041
          .hword 1041
          .hword -1637
          .hword -1637
          .hword -583
          .hword -583
          .hword -17
          .hword -17
          .hword 10247
          .hword 10247
          .hword -16113
          .hword -16113
          .hword -5739
          .hword -5739
          .hword -167
          .hword -167

roots_l34:
        .hword 1583
        .hword 15582
        .hword -821
        .hword -8081
        .hword 1355
        .hword 13338
        .hword 0
        .hword 0
        .hword -569
        .hword -5601
        .hword 450
        .hword 4429
        .hword 936
        .hword 9213
        .hword 0
        .hword 0
        .hword 69
        .hword 679
        .hword 447
        .hword 4400
        .hword -535
        .hword -5266
        .hword 0
        .hword 0
        .hword 543
        .hword 5345
        .hword 1235
        .hword 12156
        .hword -1426
        .hword -14036
        .hword 0
        .hword 0
        .hword -797
        .hword -7845
        .hword -1333
        .hword -13121
        .hword 1089
        .hword 10719
        .hword 0
        .hword 0
        .hword -193
        .hword -1900
        .hword -56
        .hword -551
        .hword 283
        .hword 2786
        .hword 0
        .hword 0
        .hword 1410
        .hword 13879
        .hword -1476
        .hword -14529
        .hword -1339
        .hword -13180
        .hword 0
        .hword 0
        .hword -1062
        .hword -10453
        .hword 882
        .hword 8682
        .hword -296
        .hword -2914
        .hword 0
        .hword 0

roots_l012:
        .hword 1600
        .hword 15749
        .hword 40
        .hword 394
        .hword 749
        .hword 7373
        .hword -848
        .hword -8347
        .hword 1432
        .hword 14095
        .hword -630
        .hword -6201
        .hword 687
        .hword 6762
        .hword 0
        .hword 0
