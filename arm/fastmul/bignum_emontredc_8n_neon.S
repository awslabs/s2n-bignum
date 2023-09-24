// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

// ----------------------------------------------------------------------------
// Extend Montgomery reduce in 8-digit blocks, results in input-output buffer
// Inputs z[2*k], m[k], w;
// Outputs function return (extra result bit) and z[2*k]
// Temporary buffer m_precalc[12*(k/4-1)]
//
//    extern uint64_t bignum_emontredc_8n_neon
//     (uint64_t k, uint64_t *z, uint64_t *m, uint64_t w, uint64_t *m_precalc);
//
// Functionally equivalent to bignum_emontredc (see that file for more detail).
// But in general assumes that the input k is a multiple of 8.
//
// Standard ARM ABI: X0 = k, X1 = z, X2 = m, X3 = w, X4 = m_precalc
//                   returns X0
// ----------------------------------------------------------------------------
#include "_internal_s2n_bignum.h"

        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_emontredc_8n_neon)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_emontredc_8n_neon)
        .text
        .balign 4

/*
        // Computes two 64x64->128-bit multiplication a*x and a*y
        // v_in0: 128-bit input vector viewed as pair (x,y) of 64-bit numbers
        // x_in: 64-bit common multiplicand a
        // v_out0: 128-bit output vector to hold a*x
        // v_out1: 128-bit output vector to hold a*y
        //
        // Uses temporaries as indicated in the following defines:
        #define v_in0_p   v3
        #define v_in0_pp  v5
        #define v_in0_ppp v28
        #define v_in1 v0
        #define vtmp0 v4
        #define vtmp1 v6
        #define vtmp2 v7
        #define vtmp3 v16
        #define vtmp4 v2

        .macro vmul_2x_64_64_128 v_in0, x_in, v_out0, v_out1
          dup     v_in1.2d, \x_in
          uzp2    v_in0_p.4s, \v_in0\().4s, \v_in0\().4s
          xtn     vtmp0.2s, v_in1.2d
          xtn     v_in0_pp.2s, \v_in0\().2d
          rev64   v_in0_ppp.4s, \v_in0\().4s
          umull   vtmp1.2d, vtmp0.2s, v_in0_pp.2s
          umull   vtmp2.2d, vtmp0.2s, v_in0_p.2s
          uzp2    vtmp3.4s, v_in1.4s, v_in1.4s
          mul     v_in1.4s, v_in0_ppp.4s, v_in1.4s
          usra    vtmp2.2d, vtmp1.2d, #32
          umull   \v_out1\().2d, vtmp3.2s, v_in0_p.2s
          uaddlp  v_in1.2d, v_in1.4s
          and     vtmp4.16b, vtmp2.16b, v29.16b
          umlal   vtmp4.2d, vtmp3.2s, v_in0_pp.2s
          shl     \v_out0\().2d, v_in1.2d, #32
          usra    \v_out1\().2d, vtmp2.2d, #32
          umlal   \v_out0\().2d, vtmp0.2s, v_in0_pp.2s
          usra    \v_out1\().2d, vtmp4.2d, #32
        .endm
*/


#define count x27

// Helper macro for the pre-computations
#define cdiff(t, c, x, y) subs t, x, y; cneg t, t, cc; csetm c, cc

// Some immediate offsets for cached differences+carry used
// in the inner ADK multiplications
#define cache_a01 (32+0*16)
#define cache_a02 (32+1*16)
#define cache_a03 (32+2*16)
#define cache_a12 (32+3*16)
#define cache_a13 (32+4*16)
#define cache_a23 (32+5*16)
#define cache_m10 (0*16)
#define cache_m20 (1*16)
#define cache_m30 (2*16)
#define cache_m21 (3*16)
#define cache_m31 (4*16)
#define cache_m32 (5*16)

#define a0 x4
#define a1 x5
#define a2 x6
#define a3 x7

// Registers for precalculation
#define vpre00 v30
#define vpre01 v28
#define vpre02 v17
#define vpre10 v18
#define vpre11 v19
#define vpre12 v20

#define m x2

S2N_BN_SYMBOL(bignum_emontredc_8n_neon):

        sub sp, sp, #(14*16)
        stp x19, x20, [sp, #(13*16)]
        stp x21, x22, [sp, #(12*16)]
        stp x23, x24, [sp, #(11*16)]
        stp x25, x26, [sp, #(10*16)]
        stp x27, x28, [sp, #(9*16)]
        stp x29, x30, [sp, #(8*16)]
        str q8, [sp, #16*0]
        str q9, [sp, #16*1]
        str q10, [sp, #16*2]
        str q11, [sp, #16*3]
        str q12, [sp, #16*4]
        str q13, [sp, #16*5]
        str q14, [sp, #16*6]
        str q15, [sp, #16*7]

        // Leave space for cached differences of words of a in inner loop
        sub sp, sp, #(6*16)

        sub sp, sp, #32
        lsr x0, x0, #2
        mov x26, x0
        subs x12, x0, #1
        bcc bignum_emontredc_8n_neon_end

        //
        // Start of precomputation of m
        //
        // Precompute and cache signed differences of modulus components
        // used in the ADK multiplication in the inner loop.
        //
        // THIS SHOULD BE HOISTED OUT
        // (and until then, comment out for benchmarking to get accurate estimates)
        //

        // Number of extra limbs required:
        // 6 * (number of limbs / 4 - 1) * 2 = 12 * (number_of_limbs/4 - 1)
        //
        mov x24, x4
        mov x30, x4

        // Save modulus pointer
        mov x25, m

        mov count, x12

bignum_emontredc_8n_neon_precomp:
        ldp a0, a1, [m, #32]!
        ldp a2, a3, [m, #16]

#define t x28
#define c x29

        cdiff(t, c, a1, a0)
        stp   t, c, [x30, #cache_m10]
        cdiff(t, c, a2, a0)
        stp   t, c, [x30, #cache_m20]
        cdiff(t, c, a3, a0)
        stp   t, c, [x30, #cache_m30]
        cdiff(t, c, a2, a1)
        stp   t, c, [x30, #cache_m21]
        cdiff(t, c, a3, a1)
        stp   t, c, [x30, #cache_m31]
        cdiff(t, c, a3, a2)
        stp   t, c, [x30, #cache_m32]

        add x30, x30, #(6*16)

        subs count, count, #1
        cbnz count, bignum_emontredc_8n_neon_precomp

        // Set modulus pointer and buffer pointer back to its original value
        mov m, x25
        mov x30, x24

        //
        // End of precomputation
        //

        stp x3, x30, [sp]
        //stp x3, xzr, [sp]
        stp x26, xzr, [sp, #16]
        mov x28, xzr
        lsl x0, x12, #5

        movi    v29.2d, #0x000000ffffffff

bignum_emontredc_8n_neon_outerloop:
        ldp x15, x24, [x1, #0]
        ldr x3, [sp]                                 // gap(s) to follow
        ldr q7, [m, #48]                            // gap(s) to follow
        ldr q19, [m, #32]!                          // gap(s) to follow
        lsr x27, x0, #5                              // gap(s) to follow
        ldp x5, x13, [m, #-32]                      // gap(s) to follow
        mul x9, x15, x3                              // gap(s) to follow
        ldr q26, [m, #-16]                          // gap(s) to follow
        sub x27, x27, #1                             // gap(s) to follow
        dup v16.2D, x9                               // gap(s) to follow
        rev64 v11.4S, v26.4S
        uzp2 v13.4S, v26.4S, v26.4S
        mul x17, x9, x5                              // gap(s) to follow
        uzp2 v8.4S, v26.4S, v26.4S
        xtn v25.2S, v26.2D                           // gap(s) to follow
        mul v10.4S, v11.4S, v16.4S
        uzp2 v4.4S, v16.4S, v16.4S                   // gap(s) to follow
        xtn v31.2S, v16.2D                           // gap(s) to follow
        umulh x20, x9, x5
        umull v5.2D, v4.2S, v8.2S
        xtn v27.2S, v26.2D
        adds x17, x15, x17                           // gap(s) to follow
        umull v6.2D, v31.2S, v8.2S                   // gap(s) to follow
        ldp x15, x21, [x1, #16]                      // gap(s) to follow
        umull v8.2D, v31.2S, v25.2S                  // gap(s) to follow
        uaddlp v2.2D, v10.4S                         // gap(s) to follow
        mul x17, x9, x13                             // gap(s) to follow
        shl v21.2D, v2.2D, #32                       // gap(s) to follow
        usra v6.2D, v8.2D, #32                       // gap(s) to follow
        umulh x6, x9, x13                            // gap(s) to follow
        umlal v21.2D, v31.2S, v25.2S                 // gap(s) to follow
        adcs x11, x24, x17                           // gap(s) to follow
        and v8.16B, v6.16B, v29.16B                  // gap(s) to follow
        mov x29, v21.d[0]                            // gap(s) to follow
        umlal v8.2D, v4.2S, v25.2S
        mov x25, v21.d[1]                            // gap(s) to follow
        usra v5.2D, v6.2D, #32                       // gap(s) to follow
        adcs x7, x15, x29                            // gap(s) to follow
        adcs x4, x21, x25                            // gap(s) to follow
        adc x23, xzr, xzr
        adds x12, x11, x20
        rev64 v21.4S, v26.4S                         // gap(s) to follow
        mul x16, x12, x3                             // gap(s) to follow
        usra v5.2D, v8.2D, #32                       // gap(s) to follow
        uzp2 v8.4S, v26.4S, v26.4S                   // gap(s) to follow
        dup v3.2D, x16                               // gap(s) to follow
        stp x9, x16, [x1, #0]                       // gap(s) to follow
        mov x19, v5.d[0]                             // gap(s) to follow
        mov x15, v5.d[1]
        mul v6.4S, v21.4S, v3.4S
        mul x29, x16, x5
        adcs x17, x7, x6
        xtn v10.2S, v3.2D                            // gap(s) to follow
        adcs x24, x4, x19                            // gap(s) to follow
        ldr q30, [x1, #0]
        adc x15, x23, x15                            // gap(s) to follow
        uzp2 v3.4S, v3.4S, v3.4S
        umull v12.2D, v10.2S, v8.2S                  // gap(s) to follow
        xtn v15.2S, v26.2D
        adds x29, x12, x29                           // gap(s) to follow
        uaddlp v16.2D, v6.4S                         // gap(s) to follow
        mul x4, x16, x13
        umull v5.2D, v3.2S, v8.2S
        xtn v28.2S, v30.2D                           // gap(s) to follow
        shl v31.2D, v16.2D, #32
        umull v22.2D, v10.2S, v15.2S                 // gap(s) to follow
        rev64 v17.4S, v30.4S                         // gap(s) to follow
        umlal v31.2D, v10.2S, v15.2S
        rev64 v8.4S, v26.4S
        adcs x29, x17, x4                            // gap(s) to follow
        umulh x4, x16, x5                            // gap(s) to follow
        uzp2 v30.4S, v30.4S, v30.4S
        usra v12.2D, v22.2D, #32                     // gap(s) to follow
        mov x21, v31.d[0]                            // gap(s) to follow
        mov x22, v31.d[1]
        mul v22.4S, v17.4S, v19.4S                   // gap(s) to follow
        and v10.16B, v12.16B, v29.16B
        adcs x19, x24, x21                           // gap(s) to follow
        usra v5.2D, v12.2D, #32
        adcs x21, x15, x22                           // gap(s) to follow
        umlal v10.2D, v3.2S, v15.2S
        adc x14, xzr, xzr
        adds x4, x29, x4                             // gap(s) to follow
        mul x11, x4, x3                              // gap(s) to follow
        uaddlp v31.2D, v22.4S
        uzp2 v22.4S, v19.4S, v19.4S                  // gap(s) to follow
        shl v12.2D, v31.2D, #32
        umull v11.2D, v22.2S, v30.2S                 // gap(s) to follow
        usra v5.2D, v10.2D, #32
        dup v14.2D, x11                              // gap(s) to follow
        uzp2 v26.4S, v7.4S, v7.4S                    // gap(s) to follow
        umulh x6, x16, x13                           // gap(s) to follow
        mul v16.4S, v8.4S, v14.4S
        uzp2 v18.4S, v14.4S, v14.4S                  // gap(s) to follow
        mov x22, v5.d[1]                             // gap(s) to follow
        xtn v8.2S, v14.2D
        umull v24.2D, v18.2S, v13.2S                 // gap(s) to follow
        umull v9.2D, v8.2S, v13.2S
        uaddlp v6.2D, v16.4S
        adcs x23, x19, x6
        mul x19, x11, x5
        mov x24, v5.d[0]
        umull v0.2D, v8.2S, v27.2S                   // gap(s) to follow
        shl v6.2D, v6.2D, #32                        // gap(s) to follow
        xtn v5.2S, v19.2D
        adcs x10, x21, x24                           // gap(s) to follow
        mul x7, x11, x13
        umlal v6.2D, v8.2S, v27.2S
        adc x14, x14, x22                            // gap(s) to follow
        subs x24, x9, x16
        umlal v12.2D, v5.2S, v28.2S
        usra v9.2D, v0.2D, #32
        csetm x26, cc
        cneg x17, x24, cc
        umull v23.2D, v5.2S, v30.2S
        stp x17, x26, [sp, #cache_a01]
        adds x19, x4, x19
        umulh x20, x11, x5
        xtn v4.2S, v7.2D
        adcs x12, x23, x7
        ldp x25, x21, [m, #-16]                     // gap(s) to follow
        mov x17, v6.d[1]                             // gap(s) to follow
        and v31.16B, v9.16B, v29.16B
        mov x29, v6.d[0]                             // gap(s) to follow
        usra v24.2D, v9.2D, #32                      // gap(s) to follow
        umulh x24, x11, x13
        umlal v31.2D, v18.2S, v27.2S
        adcs x10, x10, x29                           // gap(s) to follow
        adcs x17, x14, x17                           // gap(s) to follow
        adc x19, xzr, xzr
        adds x22, x12, x20                           // gap(s) to follow
        mul x23, x22, x3                             // gap(s) to follow
        usra v24.2D, v31.2D, #32
        adcs x15, x10, x24                           // gap(s) to follow
        umull v19.2D, v5.2S, v28.2S                  // gap(s) to follow
        mul x10, x23, x5
        stp x11, x23, [x1, #16]                   // gap(s) to follow
        mov x14, v24.d[0]                            // gap(s) to follow
        ldr q8, [x1, #16]
        mov x20, v24.d[1]                            // gap(s) to follow
        usra v23.2D, v19.2D, #32
        umulh x5, x23, x5
        adcs x14, x17, x14                           // gap(s) to follow
        adc x8, x19, x20                             // gap(s) to follow
        mov x17, v12.d[1]                            // gap(s) to follow
        and v14.16B, v23.16B, v29.16B
        umulh x24, x23, x25
        ldp x29, x6, [x30], #96                      // gap(s) to follow
        xtn v19.2S, v8.2D                            // gap(s) to follow
        subs x7, x16, x11
        uzp2 v18.4S, v8.4S, v8.4S
        cneg x12, x7, cc                             // gap(s) to follow
        csetm x26, cc
        rev64 v20.4S, v8.4S
        umull v0.2D, v4.2S, v19.2S
        subs x4, x16, x23
        stp x12, x26, [sp, #cache_a12]
        usra v11.2D, v23.2D, #32
        umull v25.2D, v4.2S, v18.2S
        mul x7, x23, x25
        csetm x26, cc                                // gap(s) to follow
        mul v15.4S, v20.4S, v7.4S
        cneg x20, x4, cc
        subs x19, x9, x23                            // gap(s) to follow
        stp x20, x26, [sp, #cache_a13]
        csetm x26, cc
        cneg x25, x19, cc
        umlal v14.2D, v22.2S, v28.2S
        stp x25, x26, [sp, #cache_a03]
        mul x20, x23, x13
        subs x16, x9, x11
        usra v25.2D, v0.2D, #32
        csetm x26, cc
        cneg x16, x16, cc
        ldp x12, x25, [sp, #cache_a01]
        umull v13.2D, v26.2S, v18.2S
        stp x16, x26, [sp, #cache_a02]
        subs x16, x11, x23                           // gap(s) to follow
        uaddlp v27.2D, v15.4S
        csetm x26, cc
        mul x9, x23, x21                             // gap(s) to follow
        usra v11.2D, v14.2D, #32
        cneg x19, x16, cc
        adds x11, x22, x10                           // gap(s) to follow
        and v8.16B, v25.16B, v29.16B
        shl v3.2D, v27.2D, #32
        stp x19, x26, [sp, #cache_a23]
        adcs x22, x15, x20
        usra v13.2D, v25.2D, #32
        umulh x19, x23, x13
        adcs x11, x14, x7                            // gap(s) to follow
        umlal v8.2D, v26.2S, v19.2S
        adcs x14, x8, x9                             // gap(s) to follow
        mov x13, v12.d[0]
        umlal v3.2D, v4.2S, v19.2S                   // gap(s) to follow
        mov x7, v11.d[0]
        ldp x15, x20, [x1, #48]                      // gap(s) to follow
        mov x3, v11.d[1]
        umulh x23, x23, x21                          // gap(s) to follow
        adc x4, xzr, xzr
        usra v13.2D, v8.2D, #32                      // gap(s) to follow
        adds x22, x22, x5
        mov x9, v3.d[1]
        ldp x21, x5, [x1, #32]!
        adcs x11, x11, x19                           // gap(s) to follow
        adcs x14, x14, x24                           // gap(s) to follow
        mov x8, v3.d[0]
        umulh x16, x12, x29                          // gap(s) to follow
        mov x26, v13.d[0]
        adc x24, x4, x23
        adds x23, x17, x7                            // gap(s) to follow
        mov x4, v13.d[1]
        adcs x8, x8, x3                              // gap(s) to follow
        adcs x19, x9, x26                            // gap(s) to follow
        adc x17, x4, xzr
        adds x9, x23, x13                            // gap(s) to follow
        adcs x4, x8, x23                             // gap(s) to follow
        eor x7, x25, x6                              // gap(s) to follow
        adcs x6, x19, x8                             // gap(s) to follow
        adcs x19, x17, x19                           // gap(s) to follow
        adc x23, xzr, x17
        adds x22, x22, x21                           // gap(s) to follow
        adcs x8, x11, x5
        mul x29, x12, x29                            // gap(s) to follow
        adcs x11, x14, x15
        ldp x5, x21, [sp, #cache_a23]
        ldp x17, x14, [x30, #cache_m32 - 96]         // gap(s) to follow
        adcs x24, x24, x20                           // gap(s) to follow
        adc x12, xzr, xzr
        adds x20, x4, x13                            // gap(s) to follow
        adcs x15, x6, x9                             // gap(s) to follow
        eor x21, x21, x14
        adcs x4, x19, x4
        mul x25, x5, x17                             // gap(s) to follow
        adcs x6, x23, x6                             // gap(s) to follow
        adcs x19, xzr, x19                           // gap(s) to follow
        adc x23, xzr, x23
        adds x22, x13, x22
        eor x14, x16, x7                             // gap(s) to follow
        eor x10, x25, x21
        adcs x8, x9, x8
        ldp x16, x9, [sp, #cache_a13]                // gap(s) to follow

bignum_emontredc_8n_neon_maddloop_neon:

        ldr q27, [m, #32]!
        umulh x25, x5, x17
        adcs x11, x20, x11
        ldp x20, x5, [x30, #cache_m31 - 96]
        ldr q8, [m, #16]
        adcs x13, x15, x24                           // gap(s) to follow
        eor x17, x29, x7                             // gap(s) to follow
        adcs x29, x4, x12                            // gap(s) to follow
        ldp x12, x4, [x30, #cache_m20 - 96]          // gap(s) to follow
        adcs x6, x6, xzr
        xtn v12.2S, v27.2D
        uzp2 v7.4S, v27.4S, v27.4S
        mul x15, x16, x20
        adcs x19, x19, xzr
        xtn v23.2S, v8.2D
        adc x24, x23, xzr                            // gap(s) to follow
        adds xzr, x21, #1
        umull v24.2D, v7.2S, v30.2S
        eor x23, x25, x21
        adcs x10, x6, x10
        ldp x25, x6, [sp, #cache_a02]
        umull v11.2D, v23.2S, v18.2S
        umulh x20, x16, x20
        eor x16, x9, x5
        adcs x9, x19, x23
        mul v15.4S, v20.4S, v8.4S
        adc x23, x24, x21
        adds xzr, x7, #1                             // gap(s) to follow
        uzp2 v6.4S, v8.4S, v8.4S
        adcs x24, x8, x17
        ldp x5, x8, [x30, #cache_m30 - 96]           // gap(s) to follow
        mul v31.4S, v17.4S, v27.4S
        eor x6, x6, x4
        adcs x21, x11, x14                           // gap(s) to follow
        adcs x17, x13, x7
        eor x4, x15, x16
        mul x14, x25, x12
        adcs x19, x29, x7
        umulh x29, x25, x12
        ldp x11, x15, [sp, #cache_a03]               // gap(s) to follow
        adcs x12, x10, x7                            // gap(s) to follow
        umull v3.2D, v12.2S, v30.2S                  // gap(s) to follow
        adcs x9, x9, x7                              // gap(s) to follow
        umull v2.2D, v12.2S, v28.2S
        adc x10, x23, x7
        adds xzr, x16, #1                            // gap(s) to follow
        adcs x7, x19, x4
        eor x23, x20, x16
        umulh x13, x11, x5                           // gap(s) to follow
        umull v21.2D, v23.2S, v19.2S                 // gap(s) to follow
        adcs x25, x12, x23                           // gap(s) to follow
        adcs x4, x9, x16
        eor x19, x14, x6
        ldp x9, x14, [sp, #cache_a12]
        usra v3.2D, v2.2D, #32
        adc x10, x10, x16
        adds xzr, x6, #1
        ldp x20, x12, [x30, #cache_m21 - 96]         // gap(s) to follow
        mul x16, x11, x5
        adcs x23, x21, x19
        eor x29, x29, x6                             // gap(s) to follow
        usra v11.2D, v21.2D, #32                     // gap(s) to follow
        adcs x19, x17, x29                           // gap(s) to follow
        eor x5, x15, x8
        adcs x11, x7, x6
        and v21.16B, v3.16B, v29.16B
        umull v10.2D, v6.2S, v18.2S
        adcs x21, x25, x6
        mul x29, x9, x20
        usra v24.2D, v3.2D, #32
        uaddlp v8.2D, v31.4S
        adcs x8, x4, x6
        eor x15, x16, x5
        and v31.16B, v11.16B, v29.16B
        usra v10.2D, v11.2D, #32
        umlal v31.2D, v6.2S, v19.2S
        adc x25, x10, x6
        adds xzr, x5, #1                             // gap(s) to follow
        adcs x16, x19, x15
        eor x17, x13, x5
        umulh x7, x9, x20                            // gap(s) to follow
        umlal v21.2D, v7.2S, v28.2S                  // gap(s) to follow
        adcs x10, x11, x17                           // gap(s) to follow
        adcs x11, x21, x5                            // gap(s) to follow
        eor x9, x14, x12
        usra v10.2D, v31.2D, #32
        eor x17, x29, x9
        ldp x4, x19, [x1, #32]!
        adcs x21, x8, x5
        shl v8.2D, v8.2D, #32
        uaddlp v3.2D, v15.4S
        adc x25, x25, x5
        adds xzr, x9, #1                             // gap(s) to follow
        usra v24.2D, v21.2D, #32
        eor x14, x7, x9
        adcs x15, x16, x17
        umlal v8.2D, v12.2S, v28.2S
        shl v3.2D, v3.2D, #32                        // gap(s) to follow
        adcs x6, x10, x14                            // gap(s) to follow
        mov x26, v10.d[0]
        adcs x11, x11, x9
        ldp x10, x17, [x1, #16]
        umlal v3.2D, v23.2S, v19.2S
        mov x8, v10.d[1]
        adcs x7, x21, x9
        mov x21, x6
        mov x3, v24.d[1]                             // gap(s) to follow
        adc x12, x25, x9
        adds x25, x21, x4                            // gap(s) to follow
        mov x13, v8.d[1]                             // gap(s) to follow
        adcs x9, x11, x19                            // gap(s) to follow
        mov x5, v24.d[0]                             // gap(s) to follow
        adcs x11, x7, x10                            // gap(s) to follow
        mov x20, v3.d[0]
        stp x22, x24, [x1, #-32]
        adcs x24, x12, x17                           // gap(s) to follow
        mov x21, v3.d[1]
        adc x12, xzr, xzr
        adds x4, x13, x5
        mov x22, v8.d[0]
        adcs x16, x20, x3
        ldp x10, x13, [x30], #96
        ldp x29, x7, [sp, #cache_a01]                // gap(s) to follow
        adcs x19, x21, x26                           // gap(s) to follow
        adc x20, x8, xzr
        adds x8, x4, x22                             // gap(s) to follow
        adcs x4, x16, x4
        ldp x5, x6, [sp, #cache_a23]                 // gap(s) to follow
        adcs x14, x19, x16
        ldp x17, x21, [x30, #cache_m32 - 96]
        umulh x16, x29, x10                          // gap(s) to follow
        adcs x19, x20, x19                           // gap(s) to follow
        stp x23, x15, [x1, #-16]
        adc x23, xzr, x20
        adds x20, x4, x22                            // gap(s) to follow
        adcs x15, x14, x8                            // gap(s) to follow
        adcs x4, x19, x4
        eor x7, x7, x13
        mul x13, x5, x17                             // gap(s) to follow
        eor x21, x6, x21
        adcs x6, x23, x14                            // gap(s) to follow
        eor x14, x16, x7
        adcs x19, xzr, x19                           // gap(s) to follow
        mul x29, x29, x10
        adc x23, xzr, x23
        adds x22, x22, x25                           // gap(s) to follow
        adcs x8, x8, x9
        ldp x16, x9, [sp, #cache_a13]
        eor x10, x13, x21                            // gap(s) to follow
        sub count, count, #1
        cbnz count, bignum_emontredc_8n_neon_maddloop_neon

        umulh x5, x5, x17
        ldp x25, x13, [x30, #cache_m31 - 96]
        adcs x11, x20, x11
        adcs x17, x15, x24
        adcs x4, x4, x12
        umulh x15, x16, x25
        adcs x20, x6, xzr
        adcs x24, x19, xzr
        eor x9, x9, x13
        ldp x19, x6, [sp, #cache_a02]
        adc x13, x23, xzr
        adds xzr, x21, #1
        ldp x12, x23, [x30, #cache_m20 - 96]
        mul x16, x16, x25
        adcs x25, x20, x10
        eor x5, x5, x21
        eor x29, x29, x7
        adcs x24, x24, x5
        adc x10, x13, x21
        adds xzr, x7, #1
        adcs x5, x8, x29
        umulh x8, x19, x12
        adcs x13, x11, x14
        adcs x21, x17, x7
        adcs x17, x4, x7
        ldp x20, x4, [x30, #cache_m30 - 96]
        ldp x11, x14, [sp, #cache_a03]
        mul x12, x19, x12
        adcs x25, x25, x7
        eor x29, x16, x9
        adcs x19, x24, x7
        adc x16, x10, x7
        adds xzr, x9, #1
        adcs x29, x17, x29
        eor x15, x15, x9
        umulh x24, x11, x20
        adcs x7, x25, x15
        eor x25, x6, x23
        ldp x15, x23, [sp, #cache_a12]
        eor x17, x12, x25
        adcs x10, x19, x9
        adc x19, x16, x9
        adds xzr, x25, #1
        ldp x6, x16, [x30, #cache_m21 - 96]
        mul x12, x11, x20
        eor x11, x8, x25
        adcs x9, x13, x17
        adcs x17, x21, x11
        adcs x13, x29, x25
        adcs x20, x7, x25
        mul x7, x15, x6
        eor x29, x14, x4
        eor x4, x12, x29
        adcs x10, x10, x25
        adc x19, x19, x25
        adds xzr, x29, #1
        adcs x12, x17, x4
        eor x24, x24, x29
        umulh x21, x15, x6
        adcs x8, x13, x24
        adcs x14, x20, x29
        adcs x10, x10, x29
        eor x23, x23, x16
        adc x19, x19, x29
        adds xzr, x23, #1
        eor x17, x7, x23
        adcs x17, x12, x17
        eor x24, x21, x23
        adcs x24, x8, x24
        adcs x13, x14, x23
        stp x9, x17, [x1, #16]
        adcs x14, x10, x23
        mov x12, x24
        stp x22, x5, [x1, #0]
        adc x15, x19, x23

        ldp x17, x19, [x1, #32]
        ldp x20, x21, [x1, #48]
        ldp x26, xzr, [sp, #16]
        adds xzr, x28, x28
        adcs x17, x17, x12
        adcs x19, x19, x13
        adcs x20, x20, x14
        adcs x21, x21, x15
        csetm x28, cs
        stp x17, x19, [x1, #32]
        stp x20, x21, [x1, #48]
        sub x1, x1, x0
        sub m, m, x0
        add x1, x1, #32
        subs x26, x26, #1
        stp x26, xzr, [sp, #16]

        // Restore buffer base for cached modulus differences
        ldr x30, [sp, #8]

        bne bignum_emontredc_8n_neon_outerloop
        neg x0, x28

bignum_emontredc_8n_neon_end:
        add sp, sp, #32
        add sp, sp, #(6*16)

        ldr q8, [sp, #16*0]
        ldr q9, [sp, #16*1]
        ldr q10, [sp, #16*2]
        ldr q11, [sp, #16*3]
        ldr q12, [sp, #16*4]
        ldr q13, [sp, #16*5]
        ldr q14, [sp, #16*6]
        ldr q15, [sp, #16*7]
        ldp x29, x30, [sp, #(8*16)]
        ldp x27, x28, [sp, #(9*16)]
        ldp x25, x26, [sp, #(10*16)]
        ldp x23, x24, [sp, #(11*16)]
        ldp x21, x22, [sp, #(12*16)]
        ldp x19, x20, [sp, #(13*16)]
        add sp, sp, #(14*16)

        ret
