// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// The hash H of ML-KEM, SHA3-256, with the x1 Keccak permutation
// Inputs in[len], c; output out[32]
//
// Sets out to SHA3-256(in), as in FIPS 202: the sponge with rate 136 bytes
// over Keccak-f1600 of the message padded with the domain bits 01 (byte
// 0x06) and the final bit (0x80 in the last byte of the block). This is
// H of FIPS 203 (section 4.1), and mlkem-native's mlk_sha3_256. The time
// taken depends only on len, and the Keccak state is zeroed before
// returning.
//
// extern void mlkem_hash_h(uint8_t out[S2N_BIGNUM_STATIC 32],
//                            const uint8_t *in, uint64_t len,
//                            const mlkem_native2_consts *c);
//
// Standard ARM ABI: X0 = out, X1 = in, X2 = len, X3 = c
// (the constants block: rc is used)
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_arm.h"
#include "mlkem_native2_consts.h"

        S2N_BN_SYM_VISIBILITY_DIRECTIVE(mlkem_hash_h)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(mlkem_hash_h)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(mlkem_hash_h)
        .text
        .balign 4

// The stack frame: the saved registers and the 200-byte Keccak state

#define SAVE 0
#define ST 48
#define FRAME 256

#define RATE 136

S2N_BN_SYMBOL(mlkem_hash_h):
        CFI_START
        AARCH64_VALID_CALL_TARGET
        CFI_DEC_SP(FRAME)
        CFI_STACKSAVE2X(x19,x20,SAVE,SAVE+8)
        CFI_STACKSAVE2X(x21,x22,SAVE+16,SAVE+24)
        CFI_STACKSAVE2X(x29,x30,SAVE+32,SAVE+40)

        mov     x19, x0
        mov     x20, x1
        mov     x21, x2
        mov     x22, x3

        add     x0, sp, #ST
        movi    v0.2d, #0
        stp     q0, q0, [x0]
        stp     q0, q0, [x0, #32]
        stp     q0, q0, [x0, #64]
        stp     q0, q0, [x0, #96]
        stp     q0, q0, [x0, #128]
        stp     q0, q0, [x0, #160]
        str     d0, [x0, #192]

// Absorb the full blocks: XOR in RATE bytes (unrolled) and permute

Lmlkem_hash_h_block:
        cmp     x21, #RATE
        bcc     Lmlkem_hash_h_last
        add     x0, sp, #ST
        ldp     x2, x3, [x20], #16
        ldp     x4, x5, [x0, #0]
        eor     x4, x4, x2
        eor     x5, x5, x3
        stp     x4, x5, [x0, #0]
        ldp     x2, x3, [x20], #16
        ldp     x4, x5, [x0, #16]
        eor     x4, x4, x2
        eor     x5, x5, x3
        stp     x4, x5, [x0, #16]
        ldp     x2, x3, [x20], #16
        ldp     x4, x5, [x0, #32]
        eor     x4, x4, x2
        eor     x5, x5, x3
        stp     x4, x5, [x0, #32]
        ldp     x2, x3, [x20], #16
        ldp     x4, x5, [x0, #48]
        eor     x4, x4, x2
        eor     x5, x5, x3
        stp     x4, x5, [x0, #48]
        ldp     x2, x3, [x20], #16
        ldp     x4, x5, [x0, #64]
        eor     x4, x4, x2
        eor     x5, x5, x3
        stp     x4, x5, [x0, #64]
        ldp     x2, x3, [x20], #16
        ldp     x4, x5, [x0, #80]
        eor     x4, x4, x2
        eor     x5, x5, x3
        stp     x4, x5, [x0, #80]
        ldp     x2, x3, [x20], #16
        ldp     x4, x5, [x0, #96]
        eor     x4, x4, x2
        eor     x5, x5, x3
        stp     x4, x5, [x0, #96]
        ldp     x2, x3, [x20], #16
        ldp     x4, x5, [x0, #112]
        eor     x4, x4, x2
        eor     x5, x5, x3
        stp     x4, x5, [x0, #112]
        ldr     x2, [x20], #8
        ldr     x4, [x0, #128]
        eor     x4, x4, x2
        str     x4, [x0, #128]
        add     x1, x22, #MLKEM_C_RC
        bl      S2N_BN_SYMBOL(sha3_keccak_f1600)
        sub     x21, x21, #RATE
        b       Lmlkem_hash_h_block

// The last block: XOR in the len < RATE remaining bytes, whole words and
// then single bytes, the domain byte 0x06 after them and 0x80 at the end,
// and permute

Lmlkem_hash_h_last:
        add     x0, sp, #ST
        lsr     x1, x21, #3
        cbz     x1, Lmlkem_hash_h_lastbytes
Lmlkem_hash_h_lastwords:
        ldr     x2, [x20], #8
        ldr     x3, [x0]
        eor     x3, x3, x2
        str     x3, [x0], #8
        subs    x1, x1, #1
        bne     Lmlkem_hash_h_lastwords
Lmlkem_hash_h_lastbytes:
        ands    x1, x21, #7
        beq     Lmlkem_hash_h_pad
Lmlkem_hash_h_lastbyte:
        ldrb    w2, [x20], #1
        ldrb    w3, [x0]
        eor     w3, w3, w2
        strb    w3, [x0], #1
        subs    x1, x1, #1
        bne     Lmlkem_hash_h_lastbyte
Lmlkem_hash_h_pad:
        ldrb    w3, [x0]
        eor     w3, w3, #0x06
        strb    w3, [x0]
        add     x0, sp, #ST
        ldrb    w3, [x0, #(RATE - 1)]
        eor     w3, w3, #0x80
        strb    w3, [x0, #(RATE - 1)]
        add     x1, x22, #MLKEM_C_RC
        bl      S2N_BN_SYMBOL(sha3_keccak_f1600)

// The digest, then zero the state

Lmlkem_hash_h_digest:
        add     x0, sp, #ST
        ldp     q0, q1, [x0]
        stp     q0, q1, [x19]
        movi    v0.2d, #0
        stp     q0, q0, [x0]
        stp     q0, q0, [x0, #32]
        stp     q0, q0, [x0, #64]
        stp     q0, q0, [x0, #96]
        stp     q0, q0, [x0, #128]
        stp     q0, q0, [x0, #160]
        str     d0, [x0, #192]

        CFI_STACKLOAD2(x19,x20,SAVE)
        CFI_STACKLOAD2(x21,x22,SAVE+16)
        CFI_STACKLOAD2(x29,x30,SAVE+32)
        CFI_INC_SP(FRAME)
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(mlkem_hash_h)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack, "", %progbits
#endif
