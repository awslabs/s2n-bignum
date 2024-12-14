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

// This code is substantially a copy of the optimized output from SLOTHY:
//
//   https://github.com/pq-code-package/mlkem-native/blob/main/mlkem/native/aarch64/ntt_opt.S
//
// The high-level structure is clearer in the SLOTHY input source:
//
//   https://github.com/pq-code-package/mlkem-native/blob/main/mlkem/native/aarch64/ntt_clean.S
//
// Relative to these originals, the main changes are as follows:
//
// * Moved constants to the end (to match ELF parser expectations)
//
// * Changed "adrp" to plain "adr" (to avoid bringing in relocations)
//
// * Emulated st4, ld1 and ld1r (to avoid formalizing them in the model).
//
// * Added the constants roots_... at the end too, from separate file
//
// * Used .hword in place of .short since it seems better defined

#define MLKEM_NATIVE_VERSION 0
#define MLKEM_HYBRID_ORDER 0

        sub     sp, sp, #0x40
        stp     d8, d9, [sp]
        stp     d10, d11, [sp, #16]
        stp     d12, d13, [sp, #32]
        stp     d14, d15, [sp, #48]

        adr     x3, roots
        add     x3, x3, #0x0
        adr     x4, roots_l56
        add     x4, x4, #0x0
        adr     x5, const_addr

#if MLKEM_NATIVE_VERSION
        add     x5, x5, #0x0
        ld1     {v7.8h}, [x5]
#else
        dup   v7.8h, wzr
        mov   w5, 0x0d01
        mov   v7.h[0], w5
        mov   w5, 0x4ebf
        mov   v7.h[1], w5
#endif

        mov     x1, x0
        mov     x2, #0x4
        ldr     q0, [x3], #32
        ldur    q1, [x3, #-16]
        ldr     q20, [x0]
        ldr     q27, [x0, #64]
        ldr     q15, [x0, #128]
        ldr     q21, [x0, #192]
        ldr     q19, [x0, #256]
        ldr     q28, [x0, #448]
        mul     v6.8h, v19.8h, v0.h[0]
        ldr     q29, [x0, #320]
        mul     v3.8h, v28.8h, v0.h[0]
        ldr     q2, [x0, #384]
        sub     x2, x2, #0x1

layer123_start:
        sqrdmulh v30.8h, v19.8h, v0.h[1]
        sqrdmulh v19.8h, v29.8h, v0.h[1]
        mul     v29.8h, v29.8h, v0.h[0]
        sqrdmulh v23.8h, v2.8h, v0.h[1]
        mls     v6.8h, v30.8h, v7.h[0]
        mul     v30.8h, v2.8h, v0.h[0]
        mls     v29.8h, v19.8h, v7.h[0]
        sqrdmulh v19.8h, v28.8h, v0.h[1]
        sub     v28.8h, v20.8h, v6.8h
        mls     v30.8h, v23.8h, v7.h[0]
        sub     v23.8h, v27.8h, v29.8h
        add     v29.8h, v27.8h, v29.8h
        add     v6.8h, v20.8h, v6.8h
        sub     v2.8h, v15.8h, v30.8h
        add     v30.8h, v15.8h, v30.8h
        mls     v3.8h, v19.8h, v7.h[0]
        sqrdmulh v19.8h, v2.8h, v0.h[5]
        mul     v2.8h, v2.8h, v0.h[4]
        sqrdmulh v20.8h, v30.8h, v0.h[3]
        sub     v27.8h, v21.8h, v3.8h
        add     v3.8h, v21.8h, v3.8h
        mls     v2.8h, v19.8h, v7.h[0]
        sqrdmulh v19.8h, v27.8h, v0.h[5]
        mul     v27.8h, v27.8h, v0.h[4]
        mul     v30.8h, v30.8h, v0.h[2]
        sub     v15.8h, v28.8h, v2.8h
        add     v28.8h, v28.8h, v2.8h
        mls     v27.8h, v19.8h, v7.h[0]
        sqrdmulh v19.8h, v3.8h, v0.h[3]
        mul     v2.8h, v3.8h, v0.h[2]
        mls     v30.8h, v20.8h, v7.h[0]
        sub     v3.8h, v23.8h, v27.8h
        add     v23.8h, v23.8h, v27.8h
        mls     v2.8h, v19.8h, v7.h[0]
        sub     v19.8h, v6.8h, v30.8h
        add     v30.8h, v6.8h, v30.8h
        sqrdmulh v6.8h, v23.8h, v1.h[3]
        sub     v20.8h, v29.8h, v2.8h
        add     v29.8h, v29.8h, v2.8h
        mul     v23.8h, v23.8h, v1.h[2]
        sqrdmulh v2.8h, v20.8h, v1.h[1]
        sqrdmulh v27.8h, v29.8h, v0.h[7]
        mul     v29.8h, v29.8h, v0.h[6]
        mul     v20.8h, v20.8h, v1.h[0]
        mls     v23.8h, v6.8h, v7.h[0]
        sqrdmulh v6.8h, v3.8h, v1.h[5]
        mls     v29.8h, v27.8h, v7.h[0]
        mls     v20.8h, v2.8h, v7.h[0]
        sub     v2.8h, v28.8h, v23.8h
        add     v23.8h, v28.8h, v23.8h
        sub     v28.8h, v30.8h, v29.8h
        mul     v3.8h, v3.8h, v1.h[4]
        add     v30.8h, v30.8h, v29.8h
        sub     v29.8h, v19.8h, v20.8h
        add     v19.8h, v19.8h, v20.8h
        mls     v3.8h, v6.8h, v7.h[0]
        str     q30, [x0], #16
        ldr     q20, [x0]
        sub     v30.8h, v15.8h, v3.8h
        add     v6.8h, v15.8h, v3.8h
        str     q28, [x0, #48]
        ldr     q27, [x0, #64]
        str     q19, [x0, #112]
        ldr     q15, [x0, #128]
        str     q29, [x0, #176]
        ldr     q21, [x0, #192]
        str     q23, [x0, #240]
        ldr     q19, [x0, #256]
        str     q2, [x0, #304]
        ldr     q29, [x0, #320]
        str     q6, [x0, #368]
        mul     v6.8h, v19.8h, v0.h[0]
        str     q30, [x0, #432]
        ldr     q28, [x0, #448]
        ldr     q2, [x0, #384]
        mul     v3.8h, v28.8h, v0.h[0]
        sub     x2, x2, #0x1
        cbnz    x2, layer123_start
        sqrdmulh v23.8h, v28.8h, v0.h[1]
        sqrdmulh v28.8h, v2.8h, v0.h[1]
        mul     v5.8h, v29.8h, v0.h[0]
        mul     v2.8h, v2.8h, v0.h[0]
        mls     v3.8h, v23.8h, v7.h[0]
        sqrdmulh v13.8h, v29.8h, v0.h[1]
        sqrdmulh v30.8h, v19.8h, v0.h[1]
        mls     v2.8h, v28.8h, v7.h[0]
        sub     v23.8h, v21.8h, v3.8h
        mls     v5.8h, v13.8h, v7.h[0]
        mls     v6.8h, v30.8h, v7.h[0]
        mul     v29.8h, v23.8h, v0.h[4]
        sqrdmulh v30.8h, v23.8h, v0.h[5]
        add     v8.8h, v15.8h, v2.8h
        sub     v19.8h, v15.8h, v2.8h
        sub     v18.8h, v27.8h, v5.8h
        mls     v29.8h, v30.8h, v7.h[0]
        mul     v2.8h, v19.8h, v0.h[4]
        sqrdmulh v13.8h, v19.8h, v0.h[5]
        add     v31.8h, v20.8h, v6.8h
        sub     v30.8h, v18.8h, v29.8h
        sub     v12.8h, v20.8h, v6.8h
        sqrdmulh v23.8h, v8.8h, v0.h[3]
        sqrdmulh v19.8h, v30.8h, v1.h[5]
        mul     v28.8h, v30.8h, v1.h[4]
        mls     v2.8h, v13.8h, v7.h[0]
        mul     v15.8h, v8.8h, v0.h[2]
        add     v24.8h, v21.8h, v3.8h
        mls     v28.8h, v19.8h, v7.h[0]
        sub     v8.8h, v12.8h, v2.8h
        mls     v15.8h, v23.8h, v7.h[0]
        sqrdmulh v11.8h, v24.8h, v0.h[3]
        sub     v30.8h, v8.8h, v28.8h
        mul     v13.8h, v24.8h, v0.h[2]
        sub     v20.8h, v31.8h, v15.8h
        str     q30, [x0, #448]
        add     v24.8h, v8.8h, v28.8h
        mls     v13.8h, v11.8h, v7.h[0]
        add     v3.8h, v27.8h, v5.8h
        str     q24, [x0, #384]
        add     v4.8h, v31.8h, v15.8h
        sub     v11.8h, v3.8h, v13.8h
        add     v19.8h, v3.8h, v13.8h
        add     v10.8h, v18.8h, v29.8h
        sqrdmulh v30.8h, v11.8h, v1.h[1]
        mul     v13.8h, v11.8h, v1.h[0]
        mul     v6.8h, v19.8h, v0.h[6]
        sqrdmulh v26.8h, v19.8h, v0.h[7]
        mul     v23.8h, v10.8h, v1.h[2]
        mls     v13.8h, v30.8h, v7.h[0]
        sqrdmulh v19.8h, v10.8h, v1.h[3]
        mls     v6.8h, v26.8h, v7.h[0]
        add     v21.8h, v12.8h, v2.8h
        add     v30.8h, v20.8h, v13.8h
        mls     v23.8h, v19.8h, v7.h[0]
        sub     v29.8h, v20.8h, v13.8h
        str     q30, [x0, #128]
        add     v5.8h, v4.8h, v6.8h
        str     q29, [x0, #192]
        sub     v19.8h, v4.8h, v6.8h
        str     q5, [x0], #16
        sub     v30.8h, v21.8h, v23.8h
        str     q19, [x0, #48]
        add     v2.8h, v21.8h, v23.8h
        str     q30, [x0, #304]
        str     q2, [x0, #240]
        mov     x0, x1
        mov     x2, #0x8
        ldr     q19, [x0, #48]
        ldr     q9, [x3], #16
        ldr     q11, [x0, #32]
        sqrdmulh v30.8h, v19.8h, v9.h[1]
        mul     v4.8h, v19.8h, v9.h[0]
        sqrdmulh v12.8h, v11.8h, v9.h[1]
        ldr     q18, [x4, #32]
        mls     v4.8h, v30.8h, v7.h[0]
        ldr     q0, [x4, #64]
        sub     x2, x2, #0x1

layer4567_start:
        ldr     q20, [x4, #48]
        mul     v24.8h, v11.8h, v9.h[0]
        ldr     q16, [x0, #16]
        ldr     q17, [x4, #80]
        sub     v1.8h, v16.8h, v4.8h
        add     v23.8h, v16.8h, v4.8h
        mls     v24.8h, v12.8h, v7.h[0]
        sqrdmulh v4.8h, v1.8h, v9.h[5]
        sqrdmulh v28.8h, v23.8h, v9.h[3]
        mul     v22.8h, v23.8h, v9.h[2]
        mul     v5.8h, v1.8h, v9.h[4]
        ldr     q6, [x0]
        mls     v22.8h, v28.8h, v7.h[0]
        mls     v5.8h, v4.8h, v7.h[0]
        ldr     q4, [x4], #96
        add     v16.8h, v6.8h, v24.8h
        sub     v26.8h, v6.8h, v24.8h
        ldur    q10, [x4, #-80]
        sub     v19.8h, v16.8h, v22.8h
        add     v25.8h, v16.8h, v22.8h
        sub     v14.8h, v26.8h, v5.8h
        ldr     q8, [x0, #112]
        add     v2.8h, v26.8h, v5.8h
        trn1    v12.4s, v25.4s, v19.4s
        trn2    v26.4s, v25.4s, v19.4s
        trn2    v5.4s, v2.4s, v14.4s
        ldr     q9, [x3], #16
        trn2    v16.2d, v26.2d, v5.2d
        trn1    v29.4s, v2.4s, v14.4s
        trn1    v22.2d, v26.2d, v5.2d
        mul     v24.8h, v16.8h, v4.8h
        sqrdmulh v5.8h, v16.8h, v10.8h
        trn2    v16.2d, v12.2d, v29.2d
        sqrdmulh v31.8h, v8.8h, v9.h[1]
        mul     v26.8h, v16.8h, v4.8h
        sqrdmulh v4.8h, v16.8h, v10.8h
        trn1    v16.2d, v12.2d, v29.2d
        mls     v24.8h, v5.8h, v7.h[0]
        ldr     q11, [x0, #96]
        mls     v26.8h, v4.8h, v7.h[0]
        add     v5.8h, v22.8h, v24.8h
        sub     v14.8h, v22.8h, v24.8h
        sqrdmulh v12.8h, v11.8h, v9.h[1]
        sqrdmulh v25.8h, v5.8h, v20.8h
        mul     v10.8h, v5.8h, v18.8h
        add     v22.8h, v16.8h, v26.8h
        sqrdmulh v4.8h, v14.8h, v17.8h
        mul     v5.8h, v14.8h, v0.8h
        mls     v10.8h, v25.8h, v7.h[0]
        ldr     q18, [x4, #32]
        sub     v13.8h, v16.8h, v26.8h
        mls     v5.8h, v4.8h, v7.h[0]
        sub     v25.8h, v22.8h, v10.8h
        add     v24.8h, v22.8h, v10.8h
        mul     v4.8h, v8.8h, v9.h[0]
        sub     v27.8h, v13.8h, v5.8h
        add     v26.8h, v13.8h, v5.8h
        ldr     q0, [x4, #64]

#if MLKEM_NATIVE_VERSION
        st4     {v24.4s-v27.4s}, [x0], #64
#elif MLKEM_HYBRID_ORDER
        stp     q24, q25, [x0], #32
        stp     q26, q27, [x0], #32
#else
        zip1    v23.4s, v24.4s, v25.4s
        zip2    v25.4s, v24.4s, v25.4s
        zip1    v24.4s, v26.4s, v27.4s
        zip2    v27.4s, v26.4s, v27.4s

        zip1    v26.2d, v23.2d, v24.2d
        zip2    v24.2d, v23.2d, v24.2d
        stp     q26, q24, [x0]

        zip1    v26.2d, v25.2d, v27.2d
        zip2    v24.2d, v25.2d, v27.2d
        stp     q26, q24, [x0, #32]
        add     x0, x0, #64
#endif

        mls     v4.8h, v31.8h, v7.h[0]
        sub     x2, x2, #0x1
        cbnz    x2, layer4567_start
        ldr     q23, [x0, #16]
        ldr     q19, [x0]
        sub     v30.8h, v23.8h, v4.8h
        mul     v28.8h, v11.8h, v9.h[0]
        add     v23.8h, v23.8h, v4.8h
        mul     v29.8h, v30.8h, v9.h[4]
        sqrdmulh v30.8h, v30.8h, v9.h[5]
        mls     v28.8h, v12.8h, v7.h[0]
        mul     v6.8h, v23.8h, v9.h[2]
        sqrdmulh v2.8h, v23.8h, v9.h[3]
        mls     v29.8h, v30.8h, v7.h[0]
        sub     v30.8h, v19.8h, v28.8h
        add     v28.8h, v19.8h, v28.8h
        mls     v6.8h, v2.8h, v7.h[0]
        sub     v19.8h, v30.8h, v29.8h
        add     v30.8h, v30.8h, v29.8h
        ldr     q20, [x4], #96
        add     v23.8h, v28.8h, v6.8h
        sub     v29.8h, v28.8h, v6.8h
        trn1    v1.4s, v30.4s, v19.4s
        trn2    v6.4s, v30.4s, v19.4s
        trn2    v28.4s, v23.4s, v29.4s
        ldur    q2, [x4, #-80]
        trn2    v30.2d, v28.2d, v6.2d
        trn1    v3.4s, v23.4s, v29.4s
        sqrdmulh v19.8h, v30.8h, v2.8h
        mul     v29.8h, v30.8h, v20.8h
        ldur    q9, [x4, #-48]
        trn2    v30.2d, v3.2d, v1.2d
        mls     v29.8h, v19.8h, v7.h[0]
        sqrdmulh v23.8h, v30.8h, v2.8h
        trn1    v2.2d, v28.2d, v6.2d
        mul     v28.8h, v30.8h, v20.8h
        sub     v30.8h, v2.8h, v29.8h
        ldur    q20, [x4, #-16]
        mul     v19.8h, v30.8h, v0.8h
        add     v29.8h, v2.8h, v29.8h
        sqrdmulh v30.8h, v30.8h, v20.8h
        mls     v28.8h, v23.8h, v7.h[0]
        mul     v23.8h, v29.8h, v18.8h
        sqrdmulh v29.8h, v29.8h, v9.8h
        trn1    v6.2d, v3.2d, v1.2d
        mls     v19.8h, v30.8h, v7.h[0]
        sub     v30.8h, v6.8h, v28.8h
        mls     v23.8h, v29.8h, v7.h[0]
        add     v29.8h, v6.8h, v28.8h
        add     v20.8h, v30.8h, v19.8h
        sub     v21.8h, v30.8h, v19.8h
        add     v18.8h, v29.8h, v23.8h
        sub     v19.8h, v29.8h, v23.8h

#if MLKEM_NATIVE_VERSION
        st4     {v18.4s-v21.4s}, [x0], #64
#elif MLKEM_HYBRID_ORDER
        stp     q18, q19, [x0], #32
        stp     q20, q21, [x0], #32
#else
        zip1    v23.4s, v18.4s, v19.4s
        zip2    v19.4s, v18.4s, v19.4s
        zip1    v18.4s, v20.4s, v21.4s
        zip2    v21.4s, v20.4s, v21.4s
        zip1    v20.2d, v23.2d, v18.2d
        zip2    v18.2d, v23.2d, v18.2d
        stp     q20, q18, [x0]
        zip1    v20.2d, v19.2d, v21.2d
        zip2    v18.2d, v19.2d, v21.2d
        stp     q20, q18, [x0, #32]
        add     x0, x0, #64
#endif

        ldp     d8, d9, [sp]
        ldp     d10, d11, [sp, #16]
        ldp     d12, d13, [sp, #32]
        ldp     d14, d15, [sp, #48]
        add     sp, sp, #0x40
        ret

const_addr:
        .hword 3329
        .hword 20159
        .hword 0
        .hword 0
        .hword 0
        .hword 0
        .hword 0
        .hword 0

roots:

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
