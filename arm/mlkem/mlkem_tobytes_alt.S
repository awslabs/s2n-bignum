// Copyright (c) The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

// ----------------------------------------------------------------------------
// Pack ML-KEM polynomial coefficients as 12-bit numbers
// Input a[256] (signed 16-bit words); output r[384] (bytes)
//
// The same function as mlkem_tobytes: the input coefficients are assumed
// to be in the range 0 <= a[i] < 2^12, and are packed as 12-bit unsigned
// numbers, two to each group of 3 bytes.
//
// extern void mlkem_tobytes_alt(uint8_t r[S2N_BIGNUM_STATIC 384],
//                               const int16_t a[S2N_BIGNUM_STATIC 256]);
//
// Standard ARM ABI: X0 = r, X1 = a
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_arm.h"

        S2N_BN_SYM_VISIBILITY_DIRECTIVE(mlkem_tobytes_alt)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(mlkem_tobytes_alt)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(mlkem_tobytes_alt)
        .text
        .balign 4

S2N_BN_SYMBOL(mlkem_tobytes_alt):
        CFI_START
        AARCH64_VALID_CALL_TARGET

// This is the code of mlkem-native's
// mlk_poly_tobytes_aarch64_asm,
// faster than that of the non-alt version on Neoverse-V2.

        mov x2, #0x10               // =16
        ldr q5, [x1, #0x10]
        ldr q3, [x1], #0x20
        ldr q29, [x1], #0x20
        ldur q2, [x1, #-0x10]
        ldr q27, [x1, #0x10]
        ldr q23, [x1, #0x30]
        ldr q17, [x1], #0x20
        ldr q16, [x1], #0x20
        uzp2 v26.8h, v3.8h, v5.8h
        uzp1 v19.8h, v3.8h, v5.8h
        uzp2 v0.8h, v29.8h, v2.8h
        uzp1 v1.8h, v29.8h, v2.8h
        xtn v5.8b, v26.8h
        shrn v3.8b, v19.8h, #0x8
        shrn v4.8b, v26.8h, #0x4
        xtn v18.8b, v0.8h
        shrn v30.8b, v0.8h, #0x4
        xtn v28.8b, v1.8h
        shrn v29.8b, v1.8h, #0x8
        sli v3.8b, v5.8b, #0x4
        xtn v2.8b, v19.8h
        sli v29.8b, v18.8b, #0x4
        lsr x2, x2, #1
        sub x2, x2, #0x2

Lmlkem_tobytes_alt_tobytes_loop_start:
        uzp1 v25.8h, v17.8h, v27.8h
        uzp2 v31.8h, v17.8h, v27.8h
        uzp1 v24.8h, v16.8h, v23.8h
        uzp2 v6.8h, v16.8h, v23.8h
        st3 { v2.8b, v3.8b, v4.8b }, [x0], #24
        shrn v3.8b, v25.8h, #0x8
        ldr q17, [x1], #0x20
        shrn v4.8b, v31.8h, #0x4
        xtn v21.8b, v6.8h
        ldr q23, [x1, #0x10]
        st3 { v28.8b, v29.8b, v30.8b }, [x0], #24
        shrn v29.8b, v24.8h, #0x8
        ldur q27, [x1, #-0x10]
        xtn v20.8b, v31.8h
        ldr q16, [x1], #0x20
        sli v29.8b, v21.8b, #0x4
        xtn v2.8b, v25.8h
        sli v3.8b, v20.8b, #0x4
        xtn v28.8b, v24.8h
        shrn v30.8b, v6.8h, #0x4
        subs x2, x2, #0x1
        cbnz x2, Lmlkem_tobytes_alt_tobytes_loop_start
        uzp2 v7.8h, v17.8h, v27.8h
        uzp1 v25.8h, v17.8h, v27.8h
        uzp2 v0.8h, v16.8h, v23.8h
        st3 { v2.8b, v3.8b, v4.8b }, [x0], #24
        st3 { v28.8b, v29.8b, v30.8b }, [x0], #24
        shrn v21.8b, v25.8h, #0x8
        uzp1 v2.8h, v16.8h, v23.8h
        shrn v22.8b, v7.8h, #0x4
        shrn v4.8b, v0.8h, #0x4
        xtn v28.8b, v7.8h
        xtn v27.8b, v0.8h
        shrn v3.8b, v2.8h, #0x8
        sli v21.8b, v28.8b, #0x4
        xtn v2.8b, v2.8h
        sli v3.8b, v27.8b, #0x4
        xtn v20.8b, v25.8h
        st3 { v20.8b, v21.8b, v22.8b }, [x0], #24
        st3 { v2.8b, v3.8b, v4.8b }, [x0], #24
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(mlkem_tobytes_alt)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack, "", %progbits
#endif
