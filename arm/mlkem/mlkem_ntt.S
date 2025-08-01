// Copyright (c) 2022 Arm Limited
// Copyright (c) 2022 Hanno Becker
// Copyright (c) 2023 Amin Abdulrahman, Matthias Kannwischer
// Copyright (c) 2024 The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

// ----------------------------------------------------------------------------
// Forward number-theoretic transform from ML-KEM
// Input a[256], z_01234[80], z_56[384] (all signed 16-bit words); output a[256] (signed 16-bit words).
//
// The transform is in-place with input and output a[256], with the output
// in bitreversed order. The two other parameters are expected to point to
// tables of constants whose definitions can be found in the mlkem-native
// repo (mlkem/native/aarch64/src/aarch64_zetas.c) or our "tests/test.c".
//
// extern void mlkem_ntt(int16_t a[256],const int16_t z_01234[80],const int16_t z_56[384]);
//
// Standard ARM ABI: X0 = a, X1 = z_01234, X2 = z_56
// ----------------------------------------------------------------------------
#include "_internal_s2n_bignum.h"

        S2N_BN_SYM_VISIBILITY_DIRECTIVE(mlkem_ntt)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(mlkem_ntt)
        .text
        .balign 4

S2N_BN_SYMBOL(mlkem_ntt):

// This implementation is generated by SLOTHY, set up to optimize for
// the Neoverse N1 microarchitecture, starting from the clean version
//
//   https://github.com/pq-code-package/mlkem-native/blob/main/mlkem/native/aarch64/src/ntt_clean.S
//
// in the mlkem-native repository.

        sub     sp, sp, #0x40
        stp     d8, d9, [sp]
        stp     d10, d11, [sp, #16]
        stp     d12, d13, [sp, #32]
        stp     d14, d15, [sp, #48]
        mov     w5, #0xd01
        mov     v7.h[0], w5
        mov     w5, #0x4ebf
        mov     v7.h[1], w5
        mov     x3, x0
        mov     x4, #0x4
        ldr     q0, [x1], #32
        ldur    q1, [x1, #-16]
        ldr     q26, [x0, #384]
        ldr     q14, [x0, #256]
        ldr     q12, [x0, #64]
        ldr     q4, [x0, #192]
        ldr     q11, [x0]
        ldr     q22, [x0, #320]
        ldr     q10, [x0, #448]
        ldr     q28, [x0, #128]
        sqrdmulh        v23.8h, v26.8h, v0.h[1]
        mul     v26.8h, v26.8h, v0.h[0]
        sqrdmulh        v24.8h, v14.8h, v0.h[1]
        mul     v9.8h, v14.8h, v0.h[0]
        sqrdmulh        v14.8h, v22.8h, v0.h[1]
        mul     v22.8h, v22.8h, v0.h[0]
        sqrdmulh        v29.8h, v10.8h, v0.h[1]
        mls     v22.8h, v14.8h, v7.h[0]
        mls     v26.8h, v23.8h, v7.h[0]
        mul     v14.8h, v10.8h, v0.h[0]
        add     v10.8h, v12.8h, v22.8h
        sub     v12.8h, v12.8h, v22.8h
        mls     v14.8h, v29.8h, v7.h[0]
        sub     v22.8h, v28.8h, v26.8h
        add     v23.8h, v28.8h, v26.8h
        mls     v9.8h, v24.8h, v7.h[0]
        sqrdmulh        v26.8h, v22.8h, v0.h[5]
        sub     v28.8h, v4.8h, v14.8h
        add     v14.8h, v4.8h, v14.8h
        mul     v13.8h, v22.8h, v0.h[4]
        sub     v18.8h, v11.8h, v9.8h
        sqrdmulh        v4.8h, v28.8h, v0.h[5]
        sqrdmulh        v22.8h, v14.8h, v0.h[3]
        mul     v28.8h, v28.8h, v0.h[4]
        mls     v28.8h, v4.8h, v7.h[0]
        mul     v14.8h, v14.8h, v0.h[2]
        mls     v14.8h, v22.8h, v7.h[0]
        add     v4.8h, v12.8h, v28.8h
        sub     v12.8h, v12.8h, v28.8h
        mls     v13.8h, v26.8h, v7.h[0]
        sqrdmulh        v26.8h, v4.8h, v1.h[3]
        sub     v22.8h, v10.8h, v14.8h
        add     v19.8h, v10.8h, v14.8h
        mul     v3.8h, v4.8h, v1.h[2]
        sqrdmulh        v14.8h, v22.8h, v1.h[1]
        mul     v28.8h, v22.8h, v1.h[0]
        mls     v3.8h, v26.8h, v7.h[0]
        mls     v28.8h, v14.8h, v7.h[0]
        sqrdmulh        v14.8h, v12.8h, v1.h[5]
        mul     v26.8h, v12.8h, v1.h[4]
        sqrdmulh        v21.8h, v19.8h, v0.h[7]
        mls     v26.8h, v14.8h, v7.h[0]
        sub     x4, x4, #0x1

layer123_start:
        ldr     q17, [x0, #400]
        mul     v22.8h, v19.8h, v0.h[6]
        ldr     q24, [x0, #272]
        add     v19.8h, v18.8h, v13.8h
        mls     v22.8h, v21.8h, v7.h[0]
        sub     v21.8h, v18.8h, v13.8h
        ldr     q13, [x0, #208]
        ldr     q18, [x0, #80]
        sqrdmulh        v14.8h, v17.8h, v0.h[1]
        ldr     q30, [x0, #336]
        ldr     q4, [x0, #464]
        add     v2.8h, v11.8h, v9.8h
        sqrdmulh        v27.8h, v23.8h, v0.h[3]
        ldr     q11, [x0, #16]
        sub     v16.8h, v21.8h, v26.8h
        ldr     q6, [x0, #144]
        sub     v29.8h, v19.8h, v3.8h
        mul     v15.8h, v23.8h, v0.h[2]
        add     v12.8h, v21.8h, v26.8h
        sqrdmulh        v26.8h, v30.8h, v0.h[1]
        add     v3.8h, v19.8h, v3.8h
        str     q29, [x0, #320]
        mls     v15.8h, v27.8h, v7.h[0]
        str     q3, [x0, #256]
        str     q12, [x0, #384]
        mul     v10.8h, v17.8h, v0.h[0]
        str     q16, [x0, #448]
        mls     v10.8h, v14.8h, v7.h[0]
        sub     v17.8h, v2.8h, v15.8h
        mul     v12.8h, v30.8h, v0.h[0]
        sub     v16.8h, v17.8h, v28.8h
        mls     v12.8h, v26.8h, v7.h[0]
        sub     v25.8h, v6.8h, v10.8h
        str     q16, [x0, #192]
        sqrdmulh        v8.8h, v24.8h, v0.h[1]
        add     v23.8h, v6.8h, v10.8h
        sqrdmulh        v14.8h, v4.8h, v0.h[1]
        add     v16.8h, v18.8h, v12.8h
        mul     v9.8h, v24.8h, v0.h[0]
        sub     v5.8h, v18.8h, v12.8h
        add     v26.8h, v17.8h, v28.8h
        mul     v21.8h, v4.8h, v0.h[0]
        add     v27.8h, v2.8h, v15.8h
        str     q26, [x0, #128]
        mls     v21.8h, v14.8h, v7.h[0]
        sub     v12.8h, v27.8h, v22.8h
        add     v29.8h, v27.8h, v22.8h
        mls     v9.8h, v8.8h, v7.h[0]
        str     q12, [x0, #64]
        str     q29, [x0], #16
        sqrdmulh        v18.8h, v25.8h, v0.h[5]
        sub     v26.8h, v13.8h, v21.8h
        add     v21.8h, v13.8h, v21.8h
        mul     v13.8h, v25.8h, v0.h[4]
        sqrdmulh        v28.8h, v26.8h, v0.h[5]
        sqrdmulh        v15.8h, v21.8h, v0.h[3]
        mul     v31.8h, v26.8h, v0.h[4]
        mls     v31.8h, v28.8h, v7.h[0]
        mul     v27.8h, v21.8h, v0.h[2]
        mls     v27.8h, v15.8h, v7.h[0]
        add     v10.8h, v5.8h, v31.8h
        mls     v13.8h, v18.8h, v7.h[0]
        sub     v18.8h, v11.8h, v9.8h
        sub     v14.8h, v5.8h, v31.8h
        sqrdmulh        v25.8h, v10.8h, v1.h[3]
        sub     v26.8h, v16.8h, v27.8h
        add     v19.8h, v16.8h, v27.8h
        mul     v3.8h, v10.8h, v1.h[2]
        sqrdmulh        v29.8h, v26.8h, v1.h[1]
        mul     v28.8h, v26.8h, v1.h[0]
        mls     v3.8h, v25.8h, v7.h[0]
        mls     v28.8h, v29.8h, v7.h[0]
        sqrdmulh        v4.8h, v14.8h, v1.h[5]
        mul     v26.8h, v14.8h, v1.h[4]
        sqrdmulh        v21.8h, v19.8h, v0.h[7]
        mls     v26.8h, v4.8h, v7.h[0]
        sub     x4, x4, #0x1
        cbnz    x4, layer123_start

        add     v20.8h, v18.8h, v13.8h
        sqrdmulh        v16.8h, v23.8h, v0.h[3]
        sub     v8.8h, v18.8h, v13.8h
        sub     v5.8h, v20.8h, v3.8h
        mul     v27.8h, v23.8h, v0.h[2]
        add     v31.8h, v11.8h, v9.8h
        add     v14.8h, v8.8h, v26.8h
        sub     v26.8h, v8.8h, v26.8h
        str     q5, [x0, #320]
        mls     v27.8h, v16.8h, v7.h[0]
        str     q14, [x0, #384]
        mul     v25.8h, v19.8h, v0.h[6]
        str     q26, [x0, #448]
        mls     v25.8h, v21.8h, v7.h[0]
        sub     v26.8h, v31.8h, v27.8h
        add     v15.8h, v20.8h, v3.8h
        add     v29.8h, v31.8h, v27.8h
        sub     v22.8h, v26.8h, v28.8h
        str     q15, [x0, #256]
        add     v26.8h, v26.8h, v28.8h
        sub     v27.8h, v29.8h, v25.8h
        add     v20.8h, v29.8h, v25.8h
        str     q26, [x0, #128]
        str     q22, [x0, #192]
        str     q27, [x0, #64]
        str     q20, [x0], #16
        mov     x0, x3
        mov     x4, #0x8
        ldr     q11, [x1], #16
        ldr     q9, [x0, #48]
        ldr     q30, [x0, #32]
        ldr     q12, [x2], #96
        ldur    q5, [x2, #-64]
        sqrdmulh        v23.8h, v9.8h, v11.h[1]
        ldr     q15, [x0]
        mul     v6.8h, v9.8h, v11.h[0]
        ldr     q28, [x0, #16]
        sqrdmulh        v10.8h, v30.8h, v11.h[1]
        mls     v6.8h, v23.8h, v7.h[0]
        mul     v0.8h, v30.8h, v11.h[0]
        mls     v0.8h, v10.8h, v7.h[0]
        ldur    q21, [x2, #-48]
        add     v27.8h, v28.8h, v6.8h
        sub     v25.8h, v28.8h, v6.8h
        mul     v6.8h, v27.8h, v11.h[2]
        sqrdmulh        v17.8h, v27.8h, v11.h[3]
        sqrdmulh        v19.8h, v25.8h, v11.h[5]
        ldur    q18, [x2, #-80]
        mul     v22.8h, v25.8h, v11.h[4]
        mls     v6.8h, v17.8h, v7.h[0]
        mls     v22.8h, v19.8h, v7.h[0]
        sub     x4, x4, #0x1

layer4567_start:
        ldr     q27, [x0, #112]
        ldr     q4, [x1], #16
        sub     v1.8h, v15.8h, v0.8h
        ldr     q30, [x0, #96]
        add     v23.8h, v15.8h, v0.8h
        add     v11.8h, v1.8h, v22.8h
        ldur    q10, [x2, #-16]
        sub     v24.8h, v23.8h, v6.8h
        sqrdmulh        v25.8h, v27.8h, v4.h[1]
        add     v9.8h, v23.8h, v6.8h
        sub     v16.8h, v1.8h, v22.8h
        mul     v31.8h, v27.8h, v4.h[0]
        trn2    v14.4s, v9.4s, v24.4s
        sqrdmulh        v1.8h, v30.8h, v4.h[1]
        trn2    v8.4s, v11.4s, v16.4s
        trn1    v11.4s, v11.4s, v16.4s
        trn2    v19.2d, v14.2d, v8.2d
        mls     v31.8h, v25.8h, v7.h[0]
        ldr     q15, [x0, #80]
        trn1    v2.4s, v9.4s, v24.4s
        sqrdmulh        v17.8h, v19.8h, v18.8h
        trn1    v9.2d, v14.2d, v8.2d
        mul     v29.8h, v19.8h, v12.8h
        trn2    v27.2d, v2.2d, v11.2d
        add     v0.8h, v15.8h, v31.8h
        sub     v16.8h, v15.8h, v31.8h
        sqrdmulh        v13.8h, v27.8h, v18.8h
        mls     v29.8h, v17.8h, v7.h[0]
        ldur    q17, [x2, #-32]
        ldr     q15, [x0, #64]
        mul     v24.8h, v27.8h, v12.8h
        trn1    v19.2d, v2.2d, v11.2d
        ldr     q18, [x2, #16]
        mul     v6.8h, v0.8h, v4.h[2]
        ldr     q12, [x2], #96
        add     v25.8h, v9.8h, v29.8h
        mls     v24.8h, v13.8h, v7.h[0]
        sub     v20.8h, v9.8h, v29.8h
        sqrdmulh        v23.8h, v25.8h, v21.8h
        mul     v3.8h, v25.8h, v5.8h
        add     v13.8h, v19.8h, v24.8h
        sqrdmulh        v27.8h, v20.8h, v10.8h
        mls     v3.8h, v23.8h, v7.h[0]
        sub     v29.8h, v19.8h, v24.8h
        mul     v26.8h, v20.8h, v17.8h
        mls     v26.8h, v27.8h, v7.h[0]
        add     v27.8h, v13.8h, v3.8h
        sqrdmulh        v14.8h, v0.8h, v4.h[3]
        sub     v19.8h, v13.8h, v3.8h
        ldur    q5, [x2, #-64]
        mul     v0.8h, v30.8h, v4.h[0]
        trn1    v8.4s, v27.4s, v19.4s
        sub     v21.8h, v29.8h, v26.8h
        add     v11.8h, v29.8h, v26.8h
        trn2    v30.4s, v27.4s, v19.4s
        sqrdmulh        v19.8h, v16.8h, v4.h[5]
        trn2    v10.4s, v11.4s, v21.4s
        mul     v22.8h, v16.8h, v4.h[4]
        trn1    v28.4s, v11.4s, v21.4s
        trn1    v29.2d, v30.2d, v10.2d
        ldur    q21, [x2, #-48]
        mls     v0.8h, v1.8h, v7.h[0]
        trn2    v20.2d, v8.2d, v28.2d
        trn2    v26.2d, v30.2d, v10.2d
        str     q29, [x0, #16]
        trn1    v3.2d, v8.2d, v28.2d
        mls     v22.8h, v19.8h, v7.h[0]
        str     q20, [x0, #32]
        str     q26, [x0, #48]
        mls     v6.8h, v14.8h, v7.h[0]
        str     q3, [x0], #64
        sub     x4, x4, #0x1
        cbnz    x4, layer4567_start

        add     v4.8h, v15.8h, v0.8h
        sub     v14.8h, v15.8h, v0.8h
        ldur    q26, [x2, #-16]
        add     v8.8h, v14.8h, v22.8h
        sub     v27.8h, v14.8h, v22.8h
        sub     v13.8h, v4.8h, v6.8h
        add     v29.8h, v4.8h, v6.8h
        trn2    v11.4s, v8.4s, v27.4s
        trn2    v1.4s, v29.4s, v13.4s
        trn1    v27.4s, v8.4s, v27.4s
        trn1    v17.4s, v29.4s, v13.4s
        trn2    v28.2d, v1.2d, v11.2d
        trn1    v16.2d, v1.2d, v11.2d
        sqrdmulh        v0.8h, v28.8h, v18.8h
        trn2    v19.2d, v17.2d, v27.2d
        trn1    v1.2d, v17.2d, v27.2d
        mul     v27.8h, v28.8h, v12.8h
        sqrdmulh        v9.8h, v19.8h, v18.8h
        mls     v27.8h, v0.8h, v7.h[0]
        mul     v20.8h, v19.8h, v12.8h
        mls     v20.8h, v9.8h, v7.h[0]
        sub     v30.8h, v16.8h, v27.8h
        add     v25.8h, v16.8h, v27.8h
        sqrdmulh        v14.8h, v30.8h, v26.8h
        ldur    q26, [x2, #-32]
        sqrdmulh        v31.8h, v25.8h, v21.8h
        add     v27.8h, v1.8h, v20.8h
        mul     v15.8h, v30.8h, v26.8h
        mls     v15.8h, v14.8h, v7.h[0]
        sub     v26.8h, v1.8h, v20.8h
        mul     v12.8h, v25.8h, v5.8h
        mls     v12.8h, v31.8h, v7.h[0]
        sub     v2.8h, v26.8h, v15.8h
        add     v0.8h, v26.8h, v15.8h
        trn2    v14.4s, v0.4s, v2.4s
        sub     v26.8h, v27.8h, v12.8h
        add     v27.8h, v27.8h, v12.8h
        trn1    v17.4s, v0.4s, v2.4s
        trn1    v5.4s, v27.4s, v26.4s
        trn2    v26.4s, v27.4s, v26.4s
        trn1    v25.2d, v26.2d, v14.2d
        trn1    v0.2d, v5.2d, v17.2d
        trn2    v21.2d, v26.2d, v14.2d
        trn2    v26.2d, v5.2d, v17.2d
        str     q25, [x0, #16]
        str     q0, [x0], #64
        stur    q21, [x0, #-16]
        stur    q26, [x0, #-32]
        ldp     d8, d9, [sp]
        ldp     d10, d11, [sp, #16]
        ldp     d12, d13, [sp, #32]
        ldp     d14, d15, [sp, #48]
        add     sp, sp, #0x40
        ret
