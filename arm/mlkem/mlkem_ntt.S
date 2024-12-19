// Copyright (c) 2022 Arm Limited
// Copyright (c) 2022 Hanno Becker
// Copyright (c) 2023 Amin Abdulrahman, Matthias Kannwischer
// Copyright (c) 2024 The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: MIT

// ----------------------------------------------------------------------------
// Forward number-theoretic transform from ML-KEM
// Input a[256] (signed 16-bit words); output a[256] (signed 16-bit words).
//
// The transform is in-place, with the output in bitreversed order
//
// extern void mlkem_ntt(int16_t a[256]);
//
// Standard ARM ABI: X0 = a
// ----------------------------------------------------------------------------
#include "_internal_s2n_bignum.h"

        S2N_BN_SYM_VISIBILITY_DIRECTIVE(mlkem_ntt)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(mlkem_ntt)
        .text
        .balign 4

S2N_BN_SYMBOL(mlkem_ntt):

// This implementation is a slightly tweaked form of the code generated
// by SLOTHY, set up to optimize for the Neoverse N1 microarchitecture,
// starting from this clean version:
//
//   https://github.com/pq-code-package/mlkem-native/blob/main/mlkem/native/aarch64/src/ntt_clean.S
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

        adr     x1, roots_l012
        add     x1, x1, #0x0
        adr     x2, roots_l56
        add     x2, x2, #0x0
        dup     v7.8h, wzr
        mov     w5, 0x0d01
        mov     v7.h[0], w5
        mov     w5, 0x4ebf
        mov     v7.h[1], w5
        mov     x3, x0
        mov     x4, #0x4
        ldr     q0, [x1], #32
        ldur    q1, [x1, #-16]
        ldr     q23, [x0, #384]
        ldr     q25, [x0]
        ldr     q15, [x0, #256]
        ldr     q19, [x0, #192]
        ldr     q30, [x0, #448]
        ldr     q31, [x0, #128]
        ldr     q14, [x0, #320]
        ldr     q12, [x0, #64]
        sqrdmulh v18.8h, v23.8h, v0.h[1]
        mul     v23.8h, v23.8h, v0.h[0]
        sqrdmulh v2.8h, v15.8h, v0.h[1]
        mul     v3.8h, v15.8h, v0.h[0]
        sqrdmulh v15.8h, v30.8h, v0.h[1]
        mul     v30.8h, v30.8h, v0.h[0]
        mls     v23.8h, v18.8h, v7.h[0]
        mls     v30.8h, v15.8h, v7.h[0]
        mul     v5.8h, v14.8h, v0.h[0]
        add     v6.8h, v31.8h, v23.8h
        sub     v13.8h, v31.8h, v23.8h
        sqrdmulh v23.8h, v14.8h, v0.h[1]
        sub     v15.8h, v19.8h, v30.8h
        add     v24.8h, v19.8h, v30.8h
        mls     v3.8h, v2.8h, v7.h[0]
        sqrdmulh v19.8h, v15.8h, v0.h[5]
        mls     v5.8h, v23.8h, v7.h[0]
        add     v14.8h, v25.8h, v3.8h
        sqrdmulh v10.8h, v6.8h, v0.h[3]
        mul     v31.8h, v15.8h, v0.h[4]
        sub     v17.8h, v12.8h, v5.8h
        mls     v31.8h, v19.8h, v7.h[0]
        sqrdmulh v2.8h, v24.8h, v0.h[3]
        mul     v11.8h, v13.8h, v0.h[4]
        sub     x4, x4, #0x1

layer123_start:
        ldr     q18, [x0, #400]
        mul     v16.8h, v6.8h, v0.h[2]
        sub     v28.8h, v25.8h, v3.8h
        ldr     q25, [x0, #16]
        mls     v16.8h, v10.8h, v7.h[0]
        ldr     q23, [x0, #272]
        ldr     q9, [x0, #208]
        ldr     q19, [x0, #144]
        add     v8.8h, v12.8h, v5.8h
        sqrdmulh v29.8h, v18.8h, v0.h[1]
        ldr     q22, [x0, #464]
        add     v10.8h, v17.8h, v31.8h
        ldr     q4, [x0, #336]
        sqrdmulh v12.8h, v23.8h, v0.h[1]
        mul     v3.8h, v23.8h, v0.h[0]
        mul     v20.8h, v18.8h, v0.h[0]
        mls     v20.8h, v29.8h, v7.h[0]
        sqrdmulh v18.8h, v22.8h, v0.h[1]
        mul     v5.8h, v4.8h, v0.h[0]
        sqrdmulh v6.8h, v13.8h, v0.h[5]
        mul     v24.8h, v24.8h, v0.h[2]
        mls     v24.8h, v2.8h, v7.h[0]
        mul     v26.8h, v22.8h, v0.h[0]
        mls     v11.8h, v6.8h, v7.h[0]
        add     v2.8h, v8.8h, v24.8h
        mls     v26.8h, v18.8h, v7.h[0]
        mul     v13.8h, v2.8h, v0.h[6]
        add     v15.8h, v28.8h, v11.8h
        sqrdmulh v21.8h, v4.8h, v0.h[1]
        sub     v11.8h, v28.8h, v11.8h
        sub     v18.8h, v17.8h, v31.8h
        mul     v31.8h, v10.8h, v1.h[2]
        sqrdmulh v27.8h, v2.8h, v0.h[7]
        sqrdmulh v28.8h, v18.8h, v1.h[5]
        mul     v6.8h, v18.8h, v1.h[4]
        mls     v13.8h, v27.8h, v7.h[0]
        mls     v6.8h, v28.8h, v7.h[0]
        sqrdmulh v17.8h, v10.8h, v1.h[3]
        mls     v3.8h, v12.8h, v7.h[0]
        add     v10.8h, v11.8h, v6.8h
        sub     v27.8h, v8.8h, v24.8h
        mls     v5.8h, v21.8h, v7.h[0]
        str     q10, [x0, #384]
        add     v10.8h, v14.8h, v16.8h
        sqrdmulh v8.8h, v27.8h, v1.h[1]
        ldr     q12, [x0, #80]
        sub     v2.8h, v11.8h, v6.8h
        mls     v31.8h, v17.8h, v7.h[0]
        add     v11.8h, v10.8h, v13.8h
        sub     v10.8h, v10.8h, v13.8h
        str     q2, [x0, #448]
        mul     v21.8h, v27.8h, v1.h[0]
        sub     v17.8h, v12.8h, v5.8h
        str     q10, [x0, #64]
        add     v6.8h, v19.8h, v20.8h
        mls     v21.8h, v8.8h, v7.h[0]
        sub     v29.8h, v9.8h, v26.8h
        add     v4.8h, v15.8h, v31.8h
        sub     v22.8h, v14.8h, v16.8h
        sqrdmulh v13.8h, v29.8h, v0.h[5]
        str     q4, [x0, #256]
        add     v14.8h, v25.8h, v3.8h
        sqrdmulh v10.8h, v6.8h, v0.h[3]
        sub     v28.8h, v22.8h, v21.8h
        sub     v27.8h, v15.8h, v31.8h
        mul     v31.8h, v29.8h, v0.h[4]
        add     v30.8h, v22.8h, v21.8h
        add     v24.8h, v9.8h, v26.8h
        mls     v31.8h, v13.8h, v7.h[0]
        sub     v13.8h, v19.8h, v20.8h
        str     q30, [x0, #128]
        str     q27, [x0, #320]
        sqrdmulh v2.8h, v24.8h, v0.h[3]
        str     q28, [x0, #192]
        str     q11, [x0], #16
        mul     v11.8h, v13.8h, v0.h[4]
        sub     x4, x4, #0x1
        cbnz    x4, layer123_start

        sub     v29.8h, v17.8h, v31.8h
        mul     v4.8h, v6.8h, v0.h[2]
        sub     v19.8h, v25.8h, v3.8h
        add     v22.8h, v12.8h, v5.8h
        mls     v4.8h, v10.8h, v7.h[0]
        mul     v21.8h, v24.8h, v0.h[2]
        mls     v21.8h, v2.8h, v7.h[0]
        sub     v28.8h, v14.8h, v4.8h
        sqrdmulh v9.8h, v13.8h, v0.h[5]
        add     v23.8h, v14.8h, v4.8h
        sqrdmulh v8.8h, v29.8h, v1.h[5]
        mul     v20.8h, v29.8h, v1.h[4]
        add     v6.8h, v22.8h, v21.8h
        sqrdmulh v30.8h, v6.8h, v0.h[7]
        mls     v20.8h, v8.8h, v7.h[0]
        mul     v8.8h, v6.8h, v0.h[6]
        add     v25.8h, v17.8h, v31.8h
        mls     v8.8h, v30.8h, v7.h[0]
        sqrdmulh v26.8h, v25.8h, v1.h[3]
        sub     v5.8h, v22.8h, v21.8h
        mls     v11.8h, v9.8h, v7.h[0]
        add     v9.8h, v23.8h, v8.8h
        mul     v3.8h, v25.8h, v1.h[2]
        sub     v6.8h, v23.8h, v8.8h
        str     q9, [x0], #16
        str     q6, [x0, #48]
        sqrdmulh v31.8h, v5.8h, v1.h[1]
        add     v27.8h, v19.8h, v11.8h
        mls     v3.8h, v26.8h, v7.h[0]
        sub     v26.8h, v19.8h, v11.8h
        mul     v10.8h, v5.8h, v1.h[0]
        sub     v9.8h, v26.8h, v20.8h
        add     v15.8h, v26.8h, v20.8h
        mls     v10.8h, v31.8h, v7.h[0]
        str     q9, [x0, #432]
        add     v29.8h, v27.8h, v3.8h
        str     q15, [x0, #368]
        str     q29, [x0, #240]
        sub     v4.8h, v27.8h, v3.8h
        sub     v26.8h, v28.8h, v10.8h
        add     v15.8h, v28.8h, v10.8h
        str     q4, [x0, #304]
        str     q26, [x0, #176]
        str     q15, [x0, #112]
        mov     x0, x3
        mov     x4, #0x8
        ldr     q16, [x0, #48]
        ldr     q6, [x1], #16
        ldr     q20, [x0]
        sqrdmulh v13.8h, v16.8h, v6.h[1]
        ldr     q10, [x0, #32]
        ldr     q29, [x0, #16]
        ldr     q18, [x2, #48]
        mul     v27.8h, v16.8h, v6.h[0]
        ldr     q5, [x2, #64]
        sqrdmulh v26.8h, v10.8h, v6.h[1]
        mls     v27.8h, v13.8h, v7.h[0]
        mul     v14.8h, v10.8h, v6.h[0]
        mls     v14.8h, v26.8h, v7.h[0]
        sub     v13.8h, v29.8h, v27.8h
        sqrdmulh v22.8h, v13.8h, v6.h[5]
        add     v16.8h, v29.8h, v27.8h
        mul     v30.8h, v13.8h, v6.h[4]
        sub     v31.8h, v20.8h, v14.8h
        sqrdmulh v26.8h, v16.8h, v6.h[3]
        mls     v30.8h, v22.8h, v7.h[0]
        mul     v29.8h, v16.8h, v6.h[2]
        mls     v29.8h, v26.8h, v7.h[0]
        sub     x4, x4, #0x1

layer4567_start:
        ldr     q17, [x0, #96]
        ldr     q8, [x1], #16
        sub     v16.8h, v31.8h, v30.8h
        add     v23.8h, v31.8h, v30.8h
        add     v3.8h, v20.8h, v14.8h
        ldr     q9, [x0, #112]
        trn1    v12.4s, v23.4s, v16.4s
        ldr     q20, [x0, #64]
        sqrdmulh v2.8h, v17.8h, v8.h[1]
        sub     v30.8h, v3.8h, v29.8h
        ldr     q4, [x0, #80]
        add     v11.8h, v3.8h, v29.8h
        trn2    v3.4s, v23.4s, v16.4s
        sqrdmulh v0.8h, v9.8h, v8.h[1]
        ldr     q23, [x2, #16]
        trn2    v14.4s, v11.4s, v30.4s
        trn1    v13.4s, v11.4s, v30.4s
        ldr     q19, [x2], #96
        mul     v10.8h, v9.8h, v8.h[0]
        trn2    v15.2d, v14.2d, v3.2d
        ldur    q9, [x2, #-16]
        trn2    v30.2d, v13.2d, v12.2d
        sqrdmulh v31.8h, v15.8h, v23.8h
        trn1    v12.2d, v13.2d, v12.2d
        mul     v6.8h, v15.8h, v19.8h
        sqrdmulh v15.8h, v30.8h, v23.8h
        mls     v6.8h, v31.8h, v7.h[0]
        trn1    v23.2d, v14.2d, v3.2d
        mul     v30.8h, v30.8h, v19.8h
        mls     v30.8h, v15.8h, v7.h[0]
        ldur    q21, [x2, #-64]
        sub     v16.8h, v23.8h, v6.8h
        mls     v10.8h, v0.8h, v7.h[0]
        sqrdmulh v29.8h, v16.8h, v9.8h
        add     v9.8h, v23.8h, v6.8h
        sub     v3.8h, v12.8h, v30.8h
        add     v15.8h, v12.8h, v30.8h
        sqrdmulh v30.8h, v9.8h, v18.8h
        add     v11.8h, v4.8h, v10.8h
        mul     v13.8h, v16.8h, v5.8h
        mls     v13.8h, v29.8h, v7.h[0]
        mul     v12.8h, v9.8h, v21.8h
        mls     v12.8h, v30.8h, v7.h[0]
        sub     v1.8h, v3.8h, v13.8h
        mul     v14.8h, v17.8h, v8.h[0]
        add     v31.8h, v3.8h, v13.8h
        sub     v3.8h, v4.8h, v10.8h
        mls     v14.8h, v2.8h, v7.h[0]
        trn1    v19.4s, v31.4s, v1.4s
        sub     v29.8h, v15.8h, v12.8h
        add     v12.8h, v15.8h, v12.8h
        sqrdmulh v9.8h, v3.8h, v8.h[5]
        trn2    v16.4s, v31.4s, v1.4s
        sqrdmulh v26.8h, v11.8h, v8.h[3]
        trn2    v13.4s, v12.4s, v29.4s
        trn1    v12.4s, v12.4s, v29.4s
        ldr     q18, [x2, #48]
        mul     v30.8h, v3.8h, v8.h[4]
        trn2    v23.2d, v13.2d, v16.2d
        trn1    v0.2d, v13.2d, v16.2d
        ldr     q5, [x2, #64]
        mls     v30.8h, v9.8h, v7.h[0]
        str     q23, [x0, #48]
        str     q0, [x0, #16]
        trn1    v22.2d, v12.2d, v19.2d
        mul     v29.8h, v11.8h, v8.h[2]
        trn2    v15.2d, v12.2d, v19.2d
        str     q22, [x0], #64
        sub     v31.8h, v20.8h, v14.8h
        mls     v29.8h, v26.8h, v7.h[0]
        stur    q15, [x0, #-32]
        sub     x4, x4, #0x1
        cbnz    x4, layer4567_start

        add     v15.8h, v20.8h, v14.8h
        sub     v19.8h, v31.8h, v30.8h
        add     v12.8h, v31.8h, v30.8h
        ldr     q22, [x2, #80]
        add     v26.8h, v15.8h, v29.8h
        sub     v15.8h, v15.8h, v29.8h
        trn2    v2.4s, v12.4s, v19.4s
        trn1    v24.4s, v12.4s, v19.4s
        trn2    v0.4s, v26.4s, v15.4s
        ldr     q30, [x2, #16]
        ldr     q10, [x2], #96
        trn1    v14.4s, v26.4s, v15.4s
        ldur    q23, [x2, #-64]
        trn2    v8.2d, v0.2d, v2.2d
        trn2    v31.2d, v14.2d, v24.2d
        trn1    v12.2d, v14.2d, v24.2d
        sqrdmulh v15.8h, v8.8h, v30.8h
        trn1    v19.2d, v0.2d, v2.2d
        mul     v3.8h, v8.8h, v10.8h
        sqrdmulh v30.8h, v31.8h, v30.8h
        mls     v3.8h, v15.8h, v7.h[0]
        mul     v15.8h, v31.8h, v10.8h
        mls     v15.8h, v30.8h, v7.h[0]
        add     v6.8h, v19.8h, v3.8h
        sub     v3.8h, v19.8h, v3.8h
        sqrdmulh v30.8h, v6.8h, v18.8h
        mul     v19.8h, v6.8h, v23.8h
        add     v31.8h, v12.8h, v15.8h
        sub     v11.8h, v12.8h, v15.8h
        sqrdmulh v23.8h, v3.8h, v22.8h
        mls     v19.8h, v30.8h, v7.h[0]
        mul     v0.8h, v3.8h, v5.8h
        mls     v0.8h, v23.8h, v7.h[0]
        sub     v30.8h, v31.8h, v19.8h
        add     v15.8h, v31.8h, v19.8h
        trn2    v19.4s, v15.4s, v30.4s
        trn1    v15.4s, v15.4s, v30.4s
        sub     v23.8h, v11.8h, v0.8h
        add     v12.8h, v11.8h, v0.8h
        trn1    v3.4s, v12.4s, v23.4s
        trn2    v29.4s, v12.4s, v23.4s
        trn1    v13.2d, v15.2d, v3.2d
        trn2    v12.2d, v19.2d, v29.2d
        trn1    v23.2d, v19.2d, v29.2d
        trn2    v15.2d, v15.2d, v3.2d
        str     q13, [x0], #64
        stur    q12, [x0, #-16]
        stur    q15, [x0, #-32]
        stur    q23, [x0, #-48]
        ldp     d8, d9, [sp]
        ldp     d10, d11, [sp, #16]
        ldp     d12, d13, [sp, #32]
        ldp     d14, d15, [sp, #48]
        add     sp, sp, #0x40
        ret

roots_l012:
        .hword -1600
        .hword -15749
        .hword -749
        .hword -7373
        .hword -40
        .hword -394
        .hword -687
        .hword -6762
        .hword 630
        .hword 6201
        .hword -1432
        .hword -14095
        .hword 848
        .hword 8347
        .hword 0
        .hword 0

roots_l34:
        .hword 1062
        .hword 10453
        .hword 296
        .hword 2914
        .hword -882
        .hword -8682
        .hword 0
        .hword 0
        .hword -1410
        .hword -13879
        .hword 1339
        .hword 13180
        .hword 1476
        .hword 14529
        .hword 0
        .hword 0
        .hword 193
        .hword 1900
        .hword -283
        .hword -2786
        .hword 56
        .hword 551
        .hword 0
        .hword 0
        .hword 797
        .hword 7845
        .hword -1089
        .hword -10719
        .hword 1333
        .hword 13121
        .hword 0
        .hword 0
        .hword -543
        .hword -5345
        .hword 1426
        .hword 14036
        .hword -1235
        .hword -12156
        .hword 0
        .hword 0
        .hword -69
        .hword -679
        .hword 535
        .hword 5266
        .hword -447
        .hword -4400
        .hword 0
        .hword 0
        .hword 569
        .hword 5601
        .hword -936
        .hword -9213
        .hword -450
        .hword -4429
        .hword 0
        .hword 0
        .hword -1583
        .hword -15582
        .hword -1355
        .hword -13338
        .hword 821
        .hword 8081
        .hword 0
        .hword 0

roots_l56:
        .hword 289
        .hword 289
        .hword 331
        .hword 331
        .hword -76
        .hword -76
        .hword -1573
        .hword -1573
        .hword 2845
        .hword 2845
        .hword 3258
        .hword 3258
        .hword -748
        .hword -748
        .hword -15483
        .hword -15483
        .hword 17
        .hword 17
        .hword 583
        .hword 583
        .hword 1637
        .hword 1637
        .hword -1041
        .hword -1041
        .hword 167
        .hword 167
        .hword 5739
        .hword 5739
        .hword 16113
        .hword 16113
        .hword -10247
        .hword -10247
        .hword -568
        .hword -568
        .hword -680
        .hword -680
        .hword 723
        .hword 723
        .hword 1100
        .hword 1100
        .hword -5591
        .hword -5591
        .hword -6693
        .hword -6693
        .hword 7117
        .hword 7117
        .hword 10828
        .hword 10828
        .hword 1197
        .hword 1197
        .hword -1025
        .hword -1025
        .hword -1052
        .hword -1052
        .hword -1274
        .hword -1274
        .hword 11782
        .hword 11782
        .hword -10089
        .hword -10089
        .hword -10355
        .hword -10355
        .hword -12540
        .hword -12540
        .hword 1409
        .hword 1409
        .hword -48
        .hword -48
        .hword 756
        .hword 756
        .hword -314
        .hword -314
        .hword 13869
        .hword 13869
        .hword -472
        .hword -472
        .hword 7441
        .hword 7441
        .hword -3091
        .hword -3091
        .hword -667
        .hword -667
        .hword 233
        .hword 233
        .hword -1173
        .hword -1173
        .hword -279
        .hword -279
        .hword -6565
        .hword -6565
        .hword 2293
        .hword 2293
        .hword -11546
        .hword -11546
        .hword -2746
        .hword -2746
        .hword 650
        .hword 650
        .hword -1352
        .hword -1352
        .hword -816
        .hword -816
        .hword 632
        .hword 632
        .hword 6398
        .hword 6398
        .hword -13308
        .hword -13308
        .hword -8032
        .hword -8032
        .hword 6221
        .hword 6221
        .hword -1626
        .hword -1626
        .hword -540
        .hword -540
        .hword -1482
        .hword -1482
        .hword 1461
        .hword 1461
        .hword -16005
        .hword -16005
        .hword -5315
        .hword -5315
        .hword -14588
        .hword -14588
        .hword 14381
        .hword 14381
        .hword 1651
        .hword 1651
        .hword -1540
        .hword -1540
        .hword 952
        .hword 952
        .hword -642
        .hword -642
        .hword 16251
        .hword 16251
        .hword -15159
        .hword -15159
        .hword 9371
        .hword 9371
        .hword -6319
        .hword -6319
        .hword -464
        .hword -464
        .hword 33
        .hword 33
        .hword 1320
        .hword 1320
        .hword -1414
        .hword -1414
        .hword -4567
        .hword -4567
        .hword 325
        .hword 325
        .hword 12993
        .hword 12993
        .hword -13918
        .hword -13918
        .hword 939
        .hword 939
        .hword -892
        .hword -892
        .hword 733
        .hword 733
        .hword 268
        .hword 268
        .hword 9243
        .hword 9243
        .hword -8780
        .hword -8780
        .hword 7215
        .hword 7215
        .hword 2638
        .hword 2638
        .hword -1021
        .hword -1021
        .hword -941
        .hword -941
        .hword -992
        .hword -992
        .hword 641
        .hword 641
        .hword -10050
        .hword -10050
        .hword -9262
        .hword -9262
        .hword -9764
        .hword -9764
        .hword 6309
        .hword 6309
        .hword -1010
        .hword -1010
        .hword 1435
        .hword 1435
        .hword 807
        .hword 807
        .hword 452
        .hword 452
        .hword -9942
        .hword -9942
        .hword 14125
        .hword 14125
        .hword 7943
        .hword 7943
        .hword 4449
        .hword 4449
        .hword 1584
        .hword 1584
        .hword -1292
        .hword -1292
        .hword 375
        .hword 375
        .hword -1239
        .hword -1239
        .hword 15592
        .hword 15592
        .hword -12717
        .hword -12717
        .hword 3691
        .hword 3691
        .hword -12196
        .hword -12196
        .hword -1031
        .hword -1031
        .hword -109
        .hword -109
        .hword -780
        .hword -780
        .hword 1645
        .hword 1645
        .hword -10148
        .hword -10148
        .hword -1073
        .hword -1073
        .hword -7678
        .hword -7678
        .hword 16192
        .hword 16192
        .hword 1438
        .hword 1438
        .hword -461
        .hword -461
        .hword 1534
        .hword 1534
        .hword -927
        .hword -927
        .hword 14155
        .hword 14155
        .hword -4538
        .hword -4538
        .hword 15099
        .hword 15099
        .hword -9125
        .hword -9125
        .hword 1063
        .hword 1063
        .hword -556
        .hword -556
        .hword -1230
        .hword -1230
        .hword -863
        .hword -863
        .hword 10463
        .hword 10463
        .hword -5473
        .hword -5473
        .hword -12107
        .hword -12107
        .hword -8495
        .hword -8495
        .hword 319
        .hword 319
        .hword 757
        .hword 757
        .hword 561
        .hword 561
        .hword -735
        .hword -735
        .hword 3140
        .hword 3140
        .hword 7451
        .hword 7451
        .hword 5522
        .hword 5522
        .hword -7235
        .hword -7235
        .hword -682
        .hword -682
        .hword -712
        .hword -712
        .hword 1481
        .hword 1481
        .hword 648
        .hword 648
        .hword -6713
        .hword -6713
        .hword -7008
        .hword -7008
        .hword 14578
        .hword 14578
        .hword 6378
        .hword 6378
        .hword -525
        .hword -525
        .hword 403
        .hword 403
        .hword 1143
        .hword 1143
        .hword -554
        .hword -554
        .hword -5168
        .hword -5168
        .hword 3967
        .hword 3967
        .hword 11251
        .hword 11251
        .hword -5453
        .hword -5453
        .hword 1092
        .hword 1092
        .hword 1026
        .hword 1026
        .hword -1179
        .hword -1179
        .hword 886
        .hword 886
        .hword 10749
        .hword 10749
        .hword 10099
        .hword 10099
        .hword -11605
        .hword -11605
        .hword 8721
        .hword 8721
        .hword -855
        .hword -855
        .hword -219
        .hword -219
        .hword 1227
        .hword 1227
        .hword 910
        .hword 910
        .hword -8416
        .hword -8416
        .hword -2156
        .hword -2156
        .hword 12078
        .hword 12078
        .hword 8957
        .hword 8957
        .hword -1607
        .hword -1607
        .hword -1455
        .hword -1455
        .hword -1219
        .hword -1219
        .hword 885
        .hword 885
        .hword -15818
        .hword -15818
        .hword -14322
        .hword -14322
        .hword -11999
        .hword -11999
        .hword 8711
        .hword 8711
        .hword 1212
        .hword 1212
        .hword 1029
        .hword 1029
        .hword -394
        .hword -394
        .hword -1175
        .hword -1175
        .hword 11930
        .hword 11930
        .hword 10129
        .hword 10129
        .hword -3878
        .hword -3878
        .hword -11566
        .hword -11566
