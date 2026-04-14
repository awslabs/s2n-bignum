// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// GHASH polynomial multiply: Xi = H * Xi (mod x^128 + x^7 + x^2 + x + 1)
// Inputs Xi[2], Htable[4]; output Xi[2]
//
//    extern void gcm_gmult_v8
//      (uint64_t Xi[2], const uint64_t Htable[4]);
//
// Performs GHASH multiplication of the current hash value Xi by the
// authentication key H, reducing modulo the GHASH polynomial
// P = x^128 + x^7 + x^2 + x + 1.
//
// Uses Karatsuba multiplication followed by two-phase polynomial reduction.
// The Htable must be prepared by gcm_init_v8.
//
// Standard ARM ABI: X0 = Xi, X1 = Htable
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_arm.h"

        S2N_BN_SYM_VISIBILITY_DIRECTIVE(gcm_gmult_v8)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(gcm_gmult_v8)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(gcm_gmult_v8)
        .arch armv8-a+crypto
        .text
        .balign 4

// Register allocation uses only caller-saved NEON registers:
// v0-v7 and v16-v31 are caller-saved (scratch)
// v8-v15 are callee-saved (must be preserved)
//
// Xl=v0, Xm=v1, Xh=v2, IN=v3
// t1=v16, t2=v17, xC2=v20, H=v18, Hhl=v19

S2N_BN_SYMBOL(gcm_gmult_v8):
        CFI_START

// Load Xi
        ldr     q16, [x0]

// Prepare reduction constant: 0xc200000000000000
        mov     x2, #0xc200000000000000
        dup     v20.2d, x2

// Load twisted H and Hhl from Htable
        ldr     q18, [x1]
        ldr     q19, [x1, #16]

// Swap halves of H
        ext     v18.16b, v18.16b, v18.16b, #8

// Byte-reverse Xi for GHASH bit ordering (little-endian only)
#ifndef __AARCH64EB__
        rev64   v16.16b, v16.16b
#endif
        ext     v3.16b, v16.16b, v16.16b, #8

// Karatsuba multiplication: 3 polynomial multiplies
        pmull   v0.1q, v18.1d, v3.1d                 // H.lo * Xi.lo
        eor     v16.16b, v16.16b, v3.16b              // Karatsuba pre-processing
        pmull2  v2.1q, v18.2d, v3.2d                  // H.hi * Xi.hi
        pmull   v1.1q, v19.1d, v16.1d                 // (H.lo+H.hi) * (Xi.lo+Xi.hi)

// Karatsuba post-processing
        ext     v16.16b, v0.16b, v2.16b, #8
        eor     v17.16b, v0.16b, v2.16b
        eor     v1.16b, v1.16b, v16.16b
        eor     v1.16b, v1.16b, v17.16b

// 1st phase of reduction
        pmull   v17.1q, v0.1d, v20.1d
        mov     v2.d[0], v1.d[1]                      // Xh|Xm - 256-bit result
        mov     v1.d[1], v0.d[0]                      // Xm is rotated Xl
        eor     v0.16b, v1.16b, v17.16b

// 2nd phase of reduction
        ext     v17.16b, v0.16b, v0.16b, #8
        pmull   v0.1q, v0.1d, v20.1d
        eor     v17.16b, v17.16b, v2.16b
        eor     v0.16b, v0.16b, v17.16b

// Byte-reverse result back (little-endian only)
#ifndef __AARCH64EB__
        rev64   v0.16b, v0.16b
#endif
        ext     v0.16b, v0.16b, v0.16b, #8

// Store result
        str     q0, [x0]

        CFI_RET

S2N_BN_SIZE_DIRECTIVE(gcm_gmult_v8)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
