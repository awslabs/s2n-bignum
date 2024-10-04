// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC
// Inputs k, m[k];
// Output m_precalc[12*(k/4-1)]
//
//    extern void bignum_emontredc_8n_neon_precomp
//     (uint64_t k, uint64_t *m_precalc, uint64_t *m);
//
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum.h"

        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_emontredc_8n_neon_precomp)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_emontredc_8n_neon_precomp)
        .text
        .balign 4

#define cdiff(t, c, x, y) subs t, x, y; cneg t, t, cc; csetm c, cc
#define a0 x3
#define a1 x4
#define a2 x5
#define a3 x6
#define t x9
#define c x10

#define cache_m10 (0*16)
#define cache_m20 (1*16)
#define cache_m30 (2*16)
#define cache_m21 (3*16)
#define cache_m31 (4*16)
#define cache_m32 (5*16)

S2N_BN_SYMBOL(bignum_emontredc_8n_neon_precomp):

        //
        // Start of precomputation of m
        //
        // Precompute and cache signed differences of modulus limbs
        // used in the ADK multiplication in the inner loop.
        //

        // Number of extra limbs required:
        // 6 * (number of limbs / 4 - 1) * 2 = 12 * (number_of_limbs/4 - 1)
        //

        lsr x0, x0, 2
        subs x0, x0, #1
        bcc bignum_emontredc_8n_neon_precomp_loop_end

bignum_emontredc_8n_neon_precomp_loop:

        ldp a0, a1, [x2, #32]!
        ldp a2, a3, [x2, #16]

        cdiff(t, c, a1, a0)
        stp   t, c, [x1, #cache_m10]
        cdiff(t, c, a2, a0)
        stp   t, c, [x1, #cache_m20]
        cdiff(t, c, a3, a0)
        stp   t, c, [x1, #cache_m30]
        cdiff(t, c, a2, a1)
        stp   t, c, [x1, #cache_m21]
        cdiff(t, c, a3, a1)
        stp   t, c, [x1, #cache_m31]
        cdiff(t, c, a3, a2)
        stp   t, c, [x1, #cache_m32]

        add x1, x1, #(6*16)
        subs x0, x0, #1
        cbnz x0, bignum_emontredc_8n_neon_precomp_loop

bignum_emontredc_8n_neon_precomp_loop_end:
        ret
