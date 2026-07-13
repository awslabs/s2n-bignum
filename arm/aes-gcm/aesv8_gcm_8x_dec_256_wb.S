// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// AESV8_GCM_8X_DEC_256_WB (AES-256-GCM decryption, whole blocks only)
// Inputs in[bit_len/8], bit_len, xi[16], ivec[16], key[244], htable[32];
// outputs function return (number of bytes processed), out[bit_len/8],
// xi[16], ivec[16]
//
//    extern size_t aesv8_gcm_8x_dec_256_wb(const uint8_t *in, size_t bit_len,
//                                          uint8_t *out,
//                                          uint8_t xi[static 16],
//                                          uint8_t ivec[static 16],
//                                          const s2n_bignum_AES_KEY *key,
//                                          const uint64_t htable[static 32]);
//
// Standard ARM ABI: X0 = in, X1 = bit_len, X2 = out, X3 = xi, X4 = ivec,
// X5 = key, X6 = htable
// ----------------------------------------------------------------------------

// WHOLE-BLOCKS-ONLY variant of aesv8_gcm_8x_dec_256 (derived from
// aesv8_gcm_8x_dec_256.S, itself extracted from aws-lc
// aesv8-gcm-armv8-unroll8.S).  Single function: aesv8_gcm_8x_dec_256_wb
//
// CONTRACT: bit_len (X1) MUST be a nonzero multiple of 128 (whole 16-byte
// blocks).  A guard at entry (tst x1,#127; b.ne ret) returns 0 having touched
// no memory otherwise; on success X0 = bit_len/8 = bytes processed (the same
// return convention as the original's zero-length path).  The aws-lc caller
// already satisfies the contract: crypto/fipsmodule/modes/gcm.c masks len to
// kSizeTWithoutLower4Bits and passes len_blocks*8.
//
// DIVERGENCE FROM aesv8_gcm_8x_dec_256.S (intentional):
//  1. The whole-blocks guard, inserted after the cbz zero-length check and
//     before the callee-saved stores (so the abort path needs no epilogue).
//     All subsequent offsets shift by +8; the post-saves proof entry point
//     (lsr x9,x1,#3, C arguments still in X0..X6) moves from pc+0x18 to
//     pc+0x20.
//  2. The partial-block masking machinery in L256_dec_blocks_less_than_1
//     is DELETED (dead under the contract): the ld1 of the existing output
//     bytes (a 16-byte OVERREAD of the output buffer in the original), the
//     bit_len%128 mask construction (mvn/lsr/csel chain), the GHASH-input
//     mask (and v9 &= mask) and the output bif blend.  The final block is a
//     plain full block: eor3 result stored with st1, unmasked GHASH
//     accumulation.  This removes the original's read-modify-write of the
//     last output block and its 16-byte input/output access beyond the
//     message length.
//
// The parent file's prologue reorder (saves-first, C_ARGUMENTS entry past the
// saves) is inherited unchanged.  Proofs: arm/proofs/aesv8_gcm_8x_dec_256_wb.ml.
#include "_internal_s2n_bignum_arm.h"

        .arch armv8.2-a+crypto+sha3
        .text

        S2N_BN_SYM_VISIBILITY_DIRECTIVE(aesv8_gcm_8x_dec_256_wb)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(aesv8_gcm_8x_dec_256_wb)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(aesv8_gcm_8x_dec_256_wb)
.align	4
S2N_BN_SYMBOL(aesv8_gcm_8x_dec_256_wb):
	CFI_START
	nop
	cbz	x1, L256_dec_ret
	tst	x1, #127				//whole-blocks contract: bit_len % 128 == 0
	b.ne	L256_dec_ret			//not whole blocks: process nothing, return 0
	CFI_PUSH2N(d8,d9,-80,80)
	CFI_STACKSAVE2X(d10,d11,16,24)
	CFI_STACKSAVE2X(d12,d13,32,40)
	CFI_STACKSAVE2X(d14,d15,48,56)
	lsr	x9, x1, #3
	mov	x16, x4
	mov	x11, x5
	mov	x5, #0xc200000000000000
	stp	x5, xzr, [sp, #64]
	add	x10, sp, #64

	ld1	{ v0.16b}, [x16]					//CTR block 0

	mov	x15, #0x100000000			//set up counter increment
	movi	v31.16b, #0x0
	mov	v31.d[1], x15
	mov	x5, x9

	sub	x5, x5, #1		//byte_len - 1

	rev32	v30.16b, v0.16b				//set up reversed counter

	add	v30.4s, v30.4s, v31.4s		//CTR block 0

	rev32	v1.16b, v30.16b				//CTR block 1
	add	v30.4s, v30.4s, v31.4s		//CTR block 1

	rev32	v2.16b, v30.16b				//CTR block 2
	add	v30.4s, v30.4s, v31.4s		//CTR block 2
	ldp	q26, q27, [x11, #0]				  	//load rk0, rk1

	rev32	v3.16b, v30.16b				//CTR block 3
	add	v30.4s, v30.4s, v31.4s		//CTR block 3

	rev32	v4.16b, v30.16b				//CTR block 4
	add	v30.4s, v30.4s, v31.4s		//CTR block 4

	aese	v0.16b, v26.16b
	aesmc	v0.16b, v0.16b			//AES block 0 - round 0

	rev32	v5.16b, v30.16b				//CTR block 5
	add	v30.4s, v30.4s, v31.4s		//CTR block 5

	aese	v1.16b, v26.16b
	aesmc	v1.16b, v1.16b			//AES block 1 - round 0
	aese	v2.16b, v26.16b
	aesmc	v2.16b, v2.16b			//AES block 2 - round 0

	rev32	v6.16b, v30.16b				//CTR block 6
	add	v30.4s, v30.4s, v31.4s		//CTR block 6

	rev32	v7.16b, v30.16b				//CTR block 7
	aese	v4.16b, v26.16b
	aesmc	v4.16b, v4.16b			//AES block 4 - round 0

	aese	v6.16b, v26.16b
	aesmc	v6.16b, v6.16b		        //AES block 6 - round 0
	aese	v5.16b, v26.16b
	aesmc	v5.16b, v5.16b			//AES block 5 - round 0

	aese	v3.16b, v26.16b
	aesmc	v3.16b, v3.16b			//AES block 3 - round 0
	aese	v7.16b, v26.16b
	aesmc	v7.16b, v7.16b		        //AES block 7 - round 0
	ldp	q28, q26, [x11, #32]				//load rk2, rk3

	aese	v6.16b, v27.16b
	aesmc	v6.16b, v6.16b		        //AES block 6 - round 1
	aese	v4.16b, v27.16b
	aesmc	v4.16b, v4.16b		        //AES block 4 - round 1
	aese	v0.16b, v27.16b
	aesmc	v0.16b, v0.16b		        //AES block 0 - round 1

	aese	v5.16b, v27.16b
	aesmc	v5.16b, v5.16b			//AES block 5 - round 1
	aese	v7.16b, v27.16b
	aesmc	v7.16b, v7.16b			//AES block 7 - round 1
	aese	v1.16b, v27.16b
	aesmc	v1.16b, v1.16b			//AES block 1 - round 1

	aese	v2.16b, v27.16b
	aesmc	v2.16b, v2.16b			//AES block 2 - round 1
	aese	v3.16b, v27.16b
	aesmc	v3.16b, v3.16b			//AES block 3 - round 1

	aese	v3.16b, v28.16b
	aesmc	v3.16b, v3.16b			//AES block 3 - round 2
	aese	v2.16b, v28.16b
	aesmc	v2.16b, v2.16b			//AES block 2 - round 2
	aese	v6.16b, v28.16b
	aesmc	v6.16b, v6.16b			//AES block 6 - round 2

	aese	v1.16b, v28.16b
	aesmc	v1.16b, v1.16b			//AES block 1 - round 2
	aese	v7.16b, v28.16b
	aesmc	v7.16b, v7.16b			//AES block 7 - round 2
	aese	v5.16b, v28.16b
	aesmc	v5.16b, v5.16b			//AES block 5 - round 2

	aese	v0.16b, v28.16b
	aesmc	v0.16b, v0.16b			//AES block 0 - round 2
	aese	v4.16b, v28.16b
	aesmc	v4.16b, v4.16b			//AES block 4 - round 2
	ldp	q27, q28, [x11, #64]				//load rk4, rk5

	aese	v1.16b, v26.16b
	aesmc	v1.16b, v1.16b			//AES block 1 - round 3
	aese	v2.16b, v26.16b
	aesmc	v2.16b, v2.16b			//AES block 2 - round 3

	aese	v3.16b, v26.16b
	aesmc	v3.16b, v3.16b			//AES block 3 - round 3
	aese	v4.16b, v26.16b
	aesmc	v4.16b, v4.16b			//AES block 4 - round 3

	aese	v5.16b, v26.16b
	aesmc	v5.16b, v5.16b			//AES block 5 - round 3
	aese	v7.16b, v26.16b
	aesmc	v7.16b, v7.16b			//AES block 7 - round 3
	aese	v0.16b, v26.16b
	aesmc	v0.16b, v0.16b			//AES block 0 - round 3

	aese	v6.16b, v26.16b
	aesmc	v6.16b, v6.16b			//AES block 6 - round 3

	aese	v7.16b, v27.16b
	aesmc	v7.16b, v7.16b			//AES block 7 - round 4
	aese	v3.16b, v27.16b
	aesmc	v3.16b, v3.16b			//AES block 3 - round 4

	aese	v6.16b, v27.16b
	aesmc	v6.16b, v6.16b			//AES block 6 - round 4
	aese	v2.16b, v27.16b
	aesmc	v2.16b, v2.16b			//AES block 2 - round 4
	aese	v0.16b, v27.16b
	aesmc	v0.16b, v0.16b			//AES block 0 - round 4

	aese	v4.16b, v27.16b
	aesmc	v4.16b, v4.16b			//AES block 4 - round 4
	aese	v1.16b, v27.16b
	aesmc	v1.16b, v1.16b			//AES block 1 - round 4
	aese	v5.16b, v27.16b
	aesmc	v5.16b, v5.16b			//AES block 5 - round 4

	aese	v0.16b, v28.16b
	aesmc	v0.16b, v0.16b			//AES block 0 - round 5
	aese	v6.16b, v28.16b
	aesmc	v6.16b, v6.16b			//AES block 6 - round 5

	ldp	q26, q27, [x11, #96]				//load rk6, rk7
	aese	v4.16b, v28.16b
	aesmc	v4.16b, v4.16b			//AES block 4 - round 5
	aese	v7.16b, v28.16b
	aesmc	v7.16b, v7.16b			//AES block 7 - round 5

	aese	v5.16b, v28.16b
	aesmc	v5.16b, v5.16b			//AES block 5 - round 5

	aese	v2.16b, v28.16b
	aesmc	v2.16b, v2.16b			//AES block 2 - round 5
	aese	v3.16b, v28.16b
	aesmc	v3.16b, v3.16b			//AES block 3 - round 5

	aese	v1.16b, v28.16b
	aesmc	v1.16b, v1.16b			//AES block 1 - round 5

	aese	v4.16b, v26.16b
	aesmc	v4.16b, v4.16b			//AES block 4 - round 6
	aese	v3.16b, v26.16b
	aesmc	v3.16b, v3.16b			//AES block 3 - round 6
	aese	v7.16b, v26.16b
	aesmc	v7.16b, v7.16b			//AES block 7 - round 6

	aese	v6.16b, v26.16b
	aesmc	v6.16b, v6.16b			//AES block 6 - round 6
	aese	v0.16b, v26.16b
	aesmc	v0.16b, v0.16b			//AES block 0 - round 6
	aese	v5.16b, v26.16b
	aesmc	v5.16b, v5.16b			//AES block 5 - round 6

	aese	v2.16b, v26.16b
	aesmc	v2.16b, v2.16b			//AES block 2 - round 6
	aese	v1.16b, v26.16b
	aesmc	v1.16b, v1.16b			//AES block 1 - round 6
	ldp	q28, q26, [x11, #128]				//load rk8, rk9

	aese	v5.16b, v27.16b
	aesmc	v5.16b, v5.16b			//AES block 5 - round 7
	aese	v0.16b, v27.16b
	aesmc	v0.16b, v0.16b			//AES block 0 - round 7

	aese	v3.16b, v27.16b
	aesmc	v3.16b, v3.16b			//AES block 3 - round 7
	aese	v2.16b, v27.16b
	aesmc	v2.16b, v2.16b			//AES block 2 - round 7
	aese	v7.16b, v27.16b
	aesmc	v7.16b, v7.16b			//AES block 7 - round 7

	aese	v4.16b, v27.16b
	aesmc	v4.16b, v4.16b			//AES block 4 - round 7
	aese	v1.16b, v27.16b
	aesmc	v1.16b, v1.16b			//AES block 1 - round 7
	aese	v6.16b, v27.16b
	aesmc	v6.16b, v6.16b			//AES block 6 - round 7

	and	x5, x5, #0xffffffffffffff80 //number of bytes to be processed in main loop (at least 1 byte must be handled by tail)
	aese	v7.16b, v28.16b
	aesmc	v7.16b, v7.16b			//AES block 7 - round 8
	aese	v5.16b, v28.16b
	aesmc	v5.16b, v5.16b			//AES block 5 - round 8

	aese	v0.16b, v28.16b
	aesmc	v0.16b, v0.16b			//AES block 0 - round 8
	aese	v1.16b, v28.16b
	aesmc	v1.16b, v1.16b			//AES block 1 - round 8
	aese	v2.16b, v28.16b
	aesmc	v2.16b, v2.16b			//AES block 2 - round 8

	aese	v4.16b, v28.16b
	aesmc	v4.16b, v4.16b			//AES block 4 - round 8
	aese	v3.16b, v28.16b
	aesmc	v3.16b, v3.16b			//AES block 3 - round 8
	aese	v6.16b, v28.16b
	aesmc	v6.16b, v6.16b			//AES block 6 - round 8

	aese	v2.16b, v26.16b
	aesmc	v2.16b, v2.16b			//AES block 2 - round 9

	ld1	{ v19.16b}, [x3]
	ext	v19.16b, v19.16b, v19.16b, #8
	rev64	v19.16b, v19.16b
	ldp	q27, q28, [x11, #160]				//load rk10, rk11
	add	x4, x0, x1, lsr #3 //end_input_ptr
	add	x5, x5, x0

	aese	v3.16b, v26.16b
	aesmc	v3.16b, v3.16b			//AES block 3 - round 9
	aese	v6.16b, v26.16b
	aesmc	v6.16b, v6.16b			//AES block 6 - round 9

	aese	v4.16b, v26.16b
	aesmc	v4.16b, v4.16b			//AES block 4 - round 9
	aese	v5.16b, v26.16b
	aesmc	v5.16b, v5.16b			//AES block 5 - round 9

	aese	v7.16b, v26.16b
	aesmc	v7.16b, v7.16b			//AES block 7 - round 9

	aese	v0.16b, v26.16b
	aesmc	v0.16b, v0.16b			//AES block 0 - round 9
	aese	v1.16b, v26.16b
	aesmc	v1.16b, v1.16b			//AES block 1 - round 9

	aese	v4.16b, v27.16b
	aesmc	v4.16b, v4.16b			//AES block 4 - round 10
	aese	v7.16b, v27.16b
	aesmc	v7.16b, v7.16b			//AES block 7 - round 10
	aese	v5.16b, v27.16b
	aesmc	v5.16b, v5.16b			//AES block 5 - round 10

	aese	v1.16b, v27.16b
	aesmc	v1.16b, v1.16b			//AES block 1 - round 10
	aese	v2.16b, v27.16b
	aesmc	v2.16b, v2.16b			//AES block 2 - round 10
	aese	v0.16b, v27.16b
	aesmc	v0.16b, v0.16b			//AES block 0 - round 10

	aese	v6.16b, v27.16b
	aesmc	v6.16b, v6.16b			//AES block 6 - round 10
	aese	v3.16b, v27.16b
	aesmc	v3.16b, v3.16b			//AES block 3 - round 10
	ldp	q26, q27, [x11, #192]				//load rk12, rk13

	aese	v0.16b, v28.16b
	aesmc	v0.16b, v0.16b			//AES block 0 - round 11
	add	v30.4s, v30.4s, v31.4s //CTR block 7

	aese	v7.16b, v28.16b
	aesmc	v7.16b, v7.16b			//AES block 7 - round 11
	aese	v3.16b, v28.16b
	aesmc	v3.16b, v3.16b			//AES block 3 - round 11
	aese	v1.16b, v28.16b
	aesmc	v1.16b, v1.16b			//AES block 1 - round 11

	aese	v5.16b, v28.16b
	aesmc	v5.16b, v5.16b			//AES block 5 - round 11
	aese	v4.16b, v28.16b
	aesmc	v4.16b, v4.16b			//AES block 4 - round 11
	aese	v2.16b, v28.16b
	aesmc	v2.16b, v2.16b			//AES block 2 - round 11

	aese	v6.16b, v28.16b
	aesmc	v6.16b, v6.16b			//AES block 6 - round 11
	ldr	q28, [x11, #224]					//load rk14

	aese	v1.16b, v26.16b
	aesmc	v1.16b, v1.16b			//AES block 1 - round 12
	aese	v4.16b, v26.16b
	aesmc	v4.16b, v4.16b			//AES block 4 - round 12
	aese	v5.16b, v26.16b
	aesmc	v5.16b, v5.16b			//AES block 5 - round 12

	cmp	x0, x5				//check if we have <= 8 blocks
	aese	v3.16b, v26.16b
	aesmc	v3.16b, v3.16b			//AES block 3 - round 12
	aese	v2.16b, v26.16b
	aesmc	v2.16b, v2.16b			//AES block 2 - round 12

	aese	v6.16b, v26.16b
	aesmc	v6.16b, v6.16b			//AES block 6 - round 12
	aese	v0.16b, v26.16b
	aesmc	v0.16b, v0.16b			//AES block 0 - round 12
	aese	v7.16b, v26.16b
	aesmc	v7.16b, v7.16b			//AES block 7 - round 12

	aese	v5.16b, v27.16b						//AES block 5 - round 13
	aese	v1.16b, v27.16b						//AES block 1 - round 13
	aese	v2.16b, v27.16b						//AES block 2 - round 13

	aese	v0.16b, v27.16b						//AES block 0 - round 13
	aese	v4.16b, v27.16b						//AES block 4 - round 13
	aese	v6.16b, v27.16b						//AES block 6 - round 13

	aese	v3.16b, v27.16b						//AES block 3 - round 13
	aese	v7.16b, v27.16b						//AES block 7 - round 13
	b.ge	L256_dec_tail						//handle tail

	ldp	q8, q9, [x0], #32			//AES block 0, 1 - load ciphertext

	ldp	q10, q11, [x0], #32			//AES block 2, 3 - load ciphertext

	ldp	q12, q13, [x0], #32			//AES block 4, 5 - load ciphertext

	ldp	q14, q15, [x0], #32			//AES block 6, 7 - load ciphertext
	cmp	x0, x5				//check if we have <= 8 blocks

	eor3	v1.16b, v9.16b, v1.16b, v28.16b	//eor3 v1.16b, v9.16b, v1.16b, v28.16b				//AES block 1 - result
	eor3	v0.16b, v8.16b, v0.16b, v28.16b	//eor3 v0.16b, v8.16b, v0.16b, v28.16b				//AES block 0 - result
	stp	q0, q1, [x2], #32			//AES block 0, 1 - store result

	rev32	v0.16b, v30.16b				//CTR block 8
	add	v30.4s, v30.4s, v31.4s		//CTR block 8
	eor3	v3.16b, v11.16b, v3.16b, v28.16b	//eor3 v3.16b, v11.16b, v3.16b, v28.16b				//AES block 3 - result

	eor3	v5.16b, v13.16b, v5.16b, v28.16b	//eor3 v5.16b, v13.16b, v5.16b, v28.16b				//AES block 5 - result

	eor3	v4.16b, v12.16b, v4.16b, v28.16b	//eor3 v4.16b, v12.16b, v4.16b, v28.16b				//AES block 4 - result
	rev32	v1.16b, v30.16b				//CTR block 9
	add	v30.4s, v30.4s, v31.4s		//CTR block 9

	eor3	v2.16b, v10.16b, v2.16b, v28.16b	//eor3 v2.16b, v10.16b, v2.16b, v28.16b				//AES block 2 - result
	stp	q2, q3, [x2], #32			//AES block 2, 3 - store result

	rev32	v2.16b, v30.16b				//CTR block 10
	add	v30.4s, v30.4s, v31.4s		//CTR block 10

	eor3	v6.16b, v14.16b, v6.16b, v28.16b	//eor3 v6.16b, v14.16b, v6.16b, v28.16b				//AES block 6 - result

	rev32	v3.16b, v30.16b				//CTR block 11
	add	v30.4s, v30.4s, v31.4s		//CTR block 11
	stp	q4, q5, [x2], #32			//AES block 4, 5 - store result

	eor3	v7.16b, v15.16b, v7.16b, v28.16b	//eor3 v7.16b, v15.16b, v7.16b, v28.16b				//AES block 7 - result
	stp	q6, q7, [x2], #32			//AES block 6, 7 - store result

	rev32	v4.16b, v30.16b				//CTR block 12
	add	v30.4s, v30.4s, v31.4s		//CTR block 12
	b.ge	L256_dec_prepretail					//do prepretail

L256_dec_main_loop:	//main	loop start
	rev32	v5.16b, v30.16b				//CTR block 8k+13
	ldp	q26, q27, [x11, #0]					//load rk0, rk1
	add	v30.4s, v30.4s, v31.4s		//CTR block 8k+13

	rev64	v9.16b, v9.16b						//GHASH block 8k+1
	ldr	q23, [x6, #144]				//load h7l | h7h
	ldr	q25, [x6, #176]				//load h8l | h8h

	rev32	v6.16b, v30.16b				//CTR block 8k+14
	add	v30.4s, v30.4s, v31.4s		//CTR block 8k+14
	rev64	v8.16b, v8.16b						//GHASH block 8k

	ext	v19.16b, v19.16b, v19.16b, #8				//PRE 0
	rev64	v12.16b, v12.16b						//GHASH block 8k+4
	rev64	v11.16b, v11.16b						//GHASH block 8k+3

	rev32	v7.16b, v30.16b				//CTR block 8k+15
	rev64	v15.16b, v15.16b						//GHASH block 8k+7

	aese	v3.16b, v26.16b
	aesmc	v3.16b, v3.16b			//AES block 8k+11 - round 0
	aese	v6.16b, v26.16b
	aesmc	v6.16b, v6.16b			//AES block 8k+14 - round 0
	aese	v2.16b, v26.16b
	aesmc	v2.16b, v2.16b			//AES block 8k+10 - round 0

	aese	v7.16b, v26.16b
	aesmc	v7.16b, v7.16b			//AES block 8k+15 - round 0
	aese	v0.16b, v26.16b
	aesmc	v0.16b, v0.16b			//AES block 8k+8 - round 0
	aese	v5.16b, v26.16b
	aesmc	v5.16b, v5.16b			//AES block 8k+13 - round 0

	aese	v4.16b, v26.16b
	aesmc	v4.16b, v4.16b			//AES block 8k+12 - round 0
	aese	v1.16b, v26.16b
	aesmc	v1.16b, v1.16b			//AES block 8k+9 - round 0
	ldp	q28, q26, [x11, #32]				//load rk2, rk3

	eor	v8.16b, v8.16b, v19.16b					//PRE 1
	ldr	q20, [x6, #96]				//load h5l | h5h
	ldr	q22, [x6, #128]				//load h6l | h6h
	aese	v6.16b, v27.16b
	aesmc	v6.16b, v6.16b			//AES block 8k+14 - round 1

	aese	v4.16b, v27.16b
	aesmc	v4.16b, v4.16b			//AES block 8k+12 - round 1
	rev64	v10.16b, v10.16b						//GHASH block 8k+2
	aese	v3.16b, v27.16b
	aesmc	v3.16b, v3.16b			//AES block 8k+11 - round 1

	aese	v0.16b, v27.16b
	aesmc	v0.16b, v0.16b			//AES block 8k+8 - round 1
	aese	v5.16b, v27.16b
	aesmc	v5.16b, v5.16b			//AES block 8k+13 - round 1
	aese	v2.16b, v27.16b
	aesmc	v2.16b, v2.16b			//AES block 8k+10 - round 1

	trn1	v18.2d, v9.2d, v8.2d				//GHASH block 8k, 8k+1 - mid
	aese	v7.16b, v27.16b
	aesmc	v7.16b, v7.16b			//AES block 8k+15 - round 1
	aese	v1.16b, v27.16b
	aesmc	v1.16b, v1.16b			//AES block 8k+9 - round 1

	aese	v4.16b, v28.16b
	aesmc	v4.16b, v4.16b			//AES block 8k+12 - round 2
	aese	v0.16b, v28.16b
	aesmc	v0.16b, v0.16b			//AES block 8k+8 - round 2
	aese	v3.16b, v28.16b
	aesmc	v3.16b, v3.16b			//AES block 8k+11 - round 2

	aese	v6.16b, v28.16b
	aesmc	v6.16b, v6.16b			//AES block 8k+14 - round 2
	aese	v7.16b, v28.16b
	aesmc	v7.16b, v7.16b			//AES block 8k+15 - round 2
	pmull	v19.1q, v8.1d, v25.1d				//GHASH block 8k - low

	aese	v5.16b, v28.16b
	aesmc	v5.16b, v5.16b			//AES block 8k+13 - round 2
	aese	v2.16b, v28.16b
	aesmc	v2.16b, v2.16b			//AES block 8k+10 - round 2
	aese	v1.16b, v28.16b
	aesmc	v1.16b, v1.16b			//AES block 8k+9 - round 2

	ldp	q27, q28, [x11, #64]				//load rk4, rk5
	pmull2	v29.1q, v10.2d, v22.2d				//GHASH block 8k+2 - high
	aese	v3.16b, v26.16b
	aesmc	v3.16b, v3.16b			//AES block 8k+11 - round 3

	aese	v0.16b, v26.16b
	aesmc	v0.16b, v0.16b			//AES block 8k+8 - round 3
	pmull2	v16.1q, v9.2d, v23.2d				//GHASH block 8k+1 - high
	pmull	v23.1q, v9.1d, v23.1d				//GHASH block 8k+1 - low

	aese	v5.16b, v26.16b
	aesmc	v5.16b, v5.16b			//AES block 8k+13 - round 3
	aese	v6.16b, v26.16b
	aesmc	v6.16b, v6.16b			//AES block 8k+14 - round 3
	pmull2	v17.1q, v8.2d, v25.2d				//GHASH block 8k - high

	aese	v4.16b, v26.16b
	aesmc	v4.16b, v4.16b			//AES block 8k+12 - round 3
	aese	v1.16b, v26.16b
	aesmc	v1.16b, v1.16b			//AES block 8k+9 - round 3
	trn2	v8.2d, v9.2d, v8.2d				//GHASH block 8k, 8k+1 - mid

	pmull2	v9.1q, v11.2d, v20.2d				//GHASH block 8k+3 - high
	aese	v2.16b, v26.16b
	aesmc	v2.16b, v2.16b			//AES block 8k+10 - round 3
	eor	v17.16b, v17.16b, v16.16b				//GHASH block 8k+1 - high

	aese	v5.16b, v27.16b
	aesmc	v5.16b, v5.16b			//AES block 8k+13 - round 4
	aese	v7.16b, v26.16b
	aesmc	v7.16b, v7.16b			//AES block 8k+15 - round 3
	aese	v3.16b, v27.16b
	aesmc	v3.16b, v3.16b			//AES block 8k+11 - round 4

	aese	v2.16b, v27.16b
	aesmc	v2.16b, v2.16b			//AES block 8k+10 - round 4
	aese	v0.16b, v27.16b
	aesmc	v0.16b, v0.16b			//AES block 8k+8 - round 4
	aese	v1.16b, v27.16b
	aesmc	v1.16b, v1.16b			//AES block 8k+9 - round 4

	aese	v6.16b, v27.16b
	aesmc	v6.16b, v6.16b			//AES block 8k+14 - round 4
	aese	v7.16b, v27.16b
	aesmc	v7.16b, v7.16b			//AES block 8k+15 - round 4
	aese	v4.16b, v27.16b
	aesmc	v4.16b, v4.16b			//AES block 8k+12 - round 4

	ldr	q21, [x6, #112]				//load h6k | h5k
	ldr	q24, [x6, #160]				//load h8k | h7k
	eor	v8.16b, v8.16b, v18.16b			//GHASH block 8k, 8k+1 - mid
	pmull	v22.1q, v10.1d, v22.1d				//GHASH block 8k+2 - low

	ldp	q26, q27, [x11, #96]				//load rk6, rk7
	aese	v5.16b, v28.16b
	aesmc	v5.16b, v5.16b			//AES block 8k+13 - round 5
	eor	v19.16b, v19.16b, v23.16b				//GHASH block 8k+1 - low

	aese	v0.16b, v28.16b
	aesmc	v0.16b, v0.16b			//AES block 8k+8 - round 5
	aese	v3.16b, v28.16b
	aesmc	v3.16b, v3.16b			//AES block 8k+11 - round 5
	aese	v7.16b, v28.16b
	aesmc	v7.16b, v7.16b			//AES block 8k+15 - round 5

	aese	v1.16b, v28.16b
	aesmc	v1.16b, v1.16b			//AES block 8k+9 - round 5
	aese	v2.16b, v28.16b
	aesmc	v2.16b, v2.16b			//AES block 8k+10 - round 5
	aese	v6.16b, v28.16b
	aesmc	v6.16b, v6.16b			//AES block 8k+14 - round 5

	eor3	v17.16b, v17.16b, v29.16b, v9.16b	//eor3 v17.16b, v17.16b, v29.16b, v9.16b			//GHASH block 8k+2, 8k+3 - high
	trn1	v29.2d, v11.2d, v10.2d				//GHASH block 8k+2, 8k+3 - mid
	rev64	v13.16b, v13.16b						//GHASH block 8k+5

	pmull2	v18.1q, v8.2d, v24.2d				//GHASH block 8k	- mid
	pmull	v24.1q, v8.1d, v24.1d				//GHASH block 8k+1 - mid
	trn2	v10.2d, v11.2d, v10.2d				//GHASH block 8k+2, 8k+3 - mid

	aese	v3.16b, v26.16b
	aesmc	v3.16b, v3.16b			//AES block 8k+11 - round 6
	aese	v0.16b, v26.16b
	aesmc	v0.16b, v0.16b			//AES block 8k+8 - round 6
	aese	v4.16b, v28.16b
	aesmc	v4.16b, v4.16b			//AES block 8k+12 - round 5

	trn1	v16.2d, v13.2d, v12.2d				//GHASH block 8k+4, 8k+5 - mid
	aese	v1.16b, v26.16b
	aesmc	v1.16b, v1.16b			//AES block 8k+9 - round 6
	aese	v6.16b, v26.16b
	aesmc	v6.16b, v6.16b			//AES block 8k+14 - round 6

	eor	v10.16b, v10.16b, v29.16b				//GHASH block 8k+2, 8k+3 - mid
	pmull	v20.1q, v11.1d, v20.1d				//GHASH block 8k+3 - low
	aese	v4.16b, v26.16b
	aesmc	v4.16b, v4.16b			//AES block 8k+12 - round 6

	aese	v2.16b, v26.16b
	aesmc	v2.16b, v2.16b			//AES block 8k+10 - round 6
	aese	v5.16b, v26.16b
	aesmc	v5.16b, v5.16b			//AES block 8k+13 - round 6
	aese	v7.16b, v26.16b
	aesmc	v7.16b, v7.16b			//AES block 8k+15 - round 6

	pmull2	v29.1q, v10.2d, v21.2d				//GHASH block 8k+2 - mid
	pmull	v21.1q, v10.1d, v21.1d				//GHASH block 8k+3 - mid
	eor3	v19.16b, v19.16b, v22.16b, v20.16b	//eor3 v19.16b, v19.16b, v22.16b, v20.16b			//GHASH block 8k+2, 8k+3 - low

	ldr	q23, [x6, #48]				//load h3l | h3h
	ldr	q25, [x6, #80]				//load h4l | h4h
	rev64	v14.16b, v14.16b						//GHASH block 8k+6
	eor	v18.16b, v18.16b, v24.16b				//GHASH block 8k+1 - mid

	aese	v2.16b, v27.16b
	aesmc	v2.16b, v2.16b			//AES block 8k+10 - round 7
	aese	v5.16b, v27.16b
	aesmc	v5.16b, v5.16b			//AES block 8k+13 - round 7
	ldp	q28, q26, [x11, #128]				//load rk8, rk9

	ldr	q20, [x6]				//load h1l | h1h
	ldr	q22, [x6, #32]				//load h2l | h2h
	eor3	v18.16b, v18.16b, v21.16b, v29.16b	//eor3 v18.16b, v18.16b, v21.16b, v29.16b			//GHASH block 8k+2, 8k+3 - mid
	aese	v7.16b, v27.16b
	aesmc	v7.16b, v7.16b			//AES block 8k+15 - round 7

	aese	v1.16b, v27.16b
	aesmc	v1.16b, v1.16b			//AES block 8k+9 - round 7
	aese	v3.16b, v27.16b
	aesmc	v3.16b, v3.16b			//AES block 8k+11 - round 7
	aese	v6.16b, v27.16b
	aesmc	v6.16b, v6.16b			//AES block 8k+14 - round 7

	ldr	q21, [x6, #16]				//load h2k | h1k
	ldr	q24, [x6, #64]				//load h4k | h3k
	aese	v0.16b, v27.16b
	aesmc	v0.16b, v0.16b			//AES block 8k+8 - round 7
	aese	v4.16b, v27.16b
	aesmc	v4.16b, v4.16b			//AES block 8k+12 - round 7

	pmull2	v8.1q, v12.2d, v25.2d				//GHASH block 8k+4 - high
	pmull	v25.1q, v12.1d, v25.1d				//GHASH block 8k+4 - low
	trn2	v12.2d, v13.2d, v12.2d				//GHASH block 8k+4, 8k+5 - mid

	aese	v5.16b, v28.16b
	aesmc	v5.16b, v5.16b			//AES block 8k+13 - round 8
	pmull2	v10.1q, v13.2d, v23.2d				//GHASH block 8k+5 - high
	aese	v2.16b, v28.16b
	aesmc	v2.16b, v2.16b			//AES block 8k+10 - round 8

	aese	v6.16b, v28.16b
	aesmc	v6.16b, v6.16b			//AES block 8k+14 - round 8
	pmull	v23.1q, v13.1d, v23.1d				//GHASH block 8k+5 - low
	aese	v1.16b, v28.16b
	aesmc	v1.16b, v1.16b			//AES block 8k+9 - round 8

	aese	v4.16b, v28.16b
	aesmc	v4.16b, v4.16b			//AES block 8k+12 - round 8
	aese	v0.16b, v28.16b
	aesmc	v0.16b, v0.16b			//AES block 8k+8 - round 8
	pmull2	v11.1q, v14.2d, v22.2d				//GHASH block 8k+6 - high

	trn1	v13.2d, v15.2d, v14.2d				//GHASH block 8k+6, 8k+7 - mid
	aese	v3.16b, v28.16b
	aesmc	v3.16b, v3.16b			//AES block 8k+11 - round 8
	aese	v7.16b, v28.16b
	aesmc	v7.16b, v7.16b			//AES block 8k+15 - round 8

	ldp	q27, q28, [x11, #160]				//load rk10, rk11
	pmull	v22.1q, v14.1d, v22.1d				//GHASH block 8k+6 - low
	trn2	v14.2d, v15.2d, v14.2d				//GHASH block 8k+6, 8k+7 - mid

	add	v30.4s, v30.4s, v31.4s		//CTR block 8k+15
	eor3	v17.16b, v17.16b, v8.16b, v10.16b	//eor3 v17.16b, v17.16b, v8.16b, v10.16b			//GHASH block 8k+4, 8k+5 - high
	aese	v3.16b, v26.16b
	aesmc	v3.16b, v3.16b			//AES block 8k+11 - round 9

	aese	v6.16b, v26.16b
	aesmc	v6.16b, v6.16b			//AES block 8k+14 - round 9
	eor	v14.16b, v14.16b, v13.16b				//GHASH block 8k+6, 8k+7 - mid
	aese	v5.16b, v26.16b
	aesmc	v5.16b, v5.16b			//AES block 8k+13 - round 9

	ldp	q8, q9, [x0], #32			//AES block 8k+8, 8k+9 - load ciphertext
	eor	v12.16b, v12.16b, v16.16b				//GHASH block 8k+4, 8k+5 - mid
	aese	v7.16b, v26.16b
	aesmc	v7.16b, v7.16b			//AES block 8k+15 - round 9

	pmull2	v13.1q, v14.2d, v21.2d				//GHASH block 8k+6 - mid
	aese	v2.16b, v26.16b
	aesmc	v2.16b, v2.16b			//AES block 8k+10 - round 9
	aese	v1.16b, v26.16b
	aesmc	v1.16b, v1.16b			//AES block 8k+9 - round 9

	pmull2	v16.1q, v12.2d, v24.2d				//GHASH block 8k+4 - mid
	pmull	v24.1q, v12.1d, v24.1d				//GHASH block 8k+5 - mid
	pmull2	v12.1q, v15.2d, v20.2d				//GHASH block 8k+7 - high

	pmull	v20.1q, v15.1d, v20.1d				//GHASH block 8k+7 - low
	aese	v3.16b, v27.16b
	aesmc	v3.16b, v3.16b			//AES block 8k+11 - round 10
	aese	v6.16b, v27.16b
	aesmc	v6.16b, v6.16b			//AES block 8k+14 - round 10

	pmull	v21.1q, v14.1d, v21.1d				//GHASH block 8k+7 - mid
	aese	v0.16b, v26.16b
	aesmc	v0.16b, v0.16b			//AES block 8k+8 - round 9
	eor3	v19.16b, v19.16b, v25.16b, v23.16b	//eor3 v19.16b, v19.16b, v25.16b, v23.16b			//GHASH block 8k+4, 8k+5 - low

	aese	v4.16b, v26.16b
	aesmc	v4.16b, v4.16b			//AES block 8k+12 - round 9
	eor3	v18.16b, v18.16b, v24.16b, v16.16b	//eor3 v18.16b, v18.16b, v24.16b, v16.16b			//GHASH block 8k+4, 8k+5 - mid
	eor3	v17.16b, v17.16b, v11.16b, v12.16b	//eor3 v17.16b, v17.16b, v11.16b, v12.16b			//GHASH block 8k+6, 8k+7 - high

	aese	v2.16b, v27.16b
	aesmc	v2.16b, v2.16b			//AES block 8k+10 - round 10
	aese	v5.16b, v27.16b
	aesmc	v5.16b, v5.16b			//AES block 8k+13 - round 10
	aese	v7.16b, v27.16b
	aesmc	v7.16b, v7.16b			//AES block 8k+15 - round 10

	aese	v1.16b, v27.16b
	aesmc	v1.16b, v1.16b			//AES block 8k+9 - round 10
	aese	v0.16b, v27.16b
	aesmc	v0.16b, v0.16b			//AES block 8k+8 - round 10
	aese	v4.16b, v27.16b
	aesmc	v4.16b, v4.16b			//AES block 8k+12 - round 10

	eor3	v19.16b, v19.16b, v22.16b, v20.16b	//eor3 v19.16b, v19.16b, v22.16b, v20.16b			//GHASH block 8k+6, 8k+7 - low
	rev32	v20.16b, v30.16b					//CTR block 8k+16
	ldr	d16, [x10]			//MODULO - load modulo constant

	add	v30.4s, v30.4s, v31.4s		//CTR block 8k+16
	aese	v1.16b, v28.16b
	aesmc	v1.16b, v1.16b			//AES block 8k+9 - round 11
	ldp	q26, q27, [x11, #192]				//load rk12, rk13

	aese	v0.16b, v28.16b
	aesmc	v0.16b, v0.16b			//AES block 8k+8 - round 11
	aese	v6.16b, v28.16b
	aesmc	v6.16b, v6.16b			//AES block 8k+14 - round 11

	eor3	v18.16b, v18.16b, v21.16b, v13.16b	//eor3 v18.16b, v18.16b, v21.16b, v13.16b			//GHASH block 8k+6, 8k+7 - mid
	rev32	v22.16b, v30.16b					//CTR block 8k+17
	aese	v2.16b, v28.16b
	aesmc	v2.16b, v2.16b			//AES block 8k+10 - round 11

	ldp	q10, q11, [x0], #32			//AES block 8k+10, 8k+11 - load ciphertext
	aese	v7.16b, v28.16b
	aesmc	v7.16b, v7.16b			//AES block 8k+15 - round 11
	ext	v21.16b, v17.16b, v17.16b, #8				 //MODULO - other top alignment

	aese	v5.16b, v28.16b
	aesmc	v5.16b, v5.16b			//AES block 8k+13 - round 11
	add	v30.4s, v30.4s, v31.4s		//CTR block 8k+17
	aese	v3.16b, v28.16b
	aesmc	v3.16b, v3.16b			//AES block 8k+11 - round 11

	aese	v2.16b, v26.16b
	aesmc	v2.16b, v2.16b			//AES block 8k+10 - round 12
	aese	v7.16b, v26.16b
	aesmc	v7.16b, v7.16b			//AES block 8k+15 - round 12
	aese	v6.16b, v26.16b
	aesmc	v6.16b, v6.16b			//AES block 8k+14 - round 12

	rev32	v23.16b, v30.16b					//CTR block 8k+18
	add	v30.4s, v30.4s, v31.4s		//CTR block 8k+18
	pmull	v29.1q, v17.1d, v16.1d			//MODULO - top 64b align with mid

	eor3	v18.16b, v18.16b, v17.16b, v19.16b	//eor3 v18.16b, v18.16b, v17.16b, v19.16b		 	//MODULO - karatsuba tidy up
	aese	v1.16b, v26.16b
	aesmc	v1.16b, v1.16b			//AES block 8k+9 - round 12
	aese	v4.16b, v28.16b
	aesmc	v4.16b, v4.16b			//AES block 8k+12 - round 11

	ldr	q28, [x11, #224]					//load rk14
	aese	v5.16b, v26.16b
	aesmc	v5.16b, v5.16b			//AES block 8k+13 - round 12
	aese	v3.16b, v26.16b
	aesmc	v3.16b, v3.16b			//AES block 8k+11 - round 12

	eor3	v18.16b, v18.16b, v29.16b, v21.16b	//eor3 v18.16b, v18.16b, v29.16b, v21.16b			//MODULO - fold into mid
	aese	v0.16b, v26.16b
	aesmc	v0.16b, v0.16b			//AES block 8k+8 - round 12
	aese	v4.16b, v26.16b
	aesmc	v4.16b, v4.16b			//AES block 8k+12 - round 12

	ldp	q12, q13, [x0], #32			//AES block 8k+12, 8k+13 - load ciphertext
	aese	v1.16b, v27.16b						//AES block 8k+9 - round 13
	aese	v2.16b, v27.16b						//AES block 8k+10 - round 13

	ldp	q14, q15, [x0], #32			//AES block 8k+14, 8k+15 - load ciphertext
	aese	v0.16b, v27.16b						//AES block 8k+8 - round 13
	aese	v5.16b, v27.16b						//AES block 8k+13 - round 13

	rev32	v25.16b, v30.16b					//CTR block 8k+19
	eor3	v2.16b, v10.16b, v2.16b, v28.16b	//eor3 v2.16b, v10.16b, v2.16b, v28.16b				//AES block 8k+10 - result
	eor3	v1.16b, v9.16b, v1.16b, v28.16b	//eor3 v1.16b, v9.16b, v1.16b, v28.16b				//AES block 8k+9 - result

	ext	v21.16b, v18.16b, v18.16b, #8				//MODULO - other mid alignment
	aese	v7.16b, v27.16b						//AES block 8k+15 - round 13

	add	v30.4s, v30.4s, v31.4s		//CTR block 8k+19
	pmull	v17.1q, v18.1d, v16.1d			//MODULO - mid 64b align with low
	aese	v4.16b, v27.16b						//AES block 8k+12 - round 13

	eor3	v5.16b, v13.16b, v5.16b, v28.16b	//eor3 v5.16b, v13.16b, v5.16b, v28.16b				//AES block 8k+13 - result
	eor3	v0.16b, v8.16b, v0.16b, v28.16b	//eor3 v0.16b, v8.16b, v0.16b, v28.16b				//AES block 8k+8 - result
	aese	v3.16b, v27.16b						//AES block 8k+11 - round 13

	stp	q0, q1, [x2], #32			//AES block 8k+8, 8k+9 - store result
	mov	v0.16b, v20.16b					//CTR block 8k+16
	eor3	v4.16b, v12.16b, v4.16b, v28.16b	//eor3 v4.16b, v12.16b, v4.16b, v28.16b				//AES block 8k+12 - result

	eor3	v19.16b, v19.16b, v21.16b, v17.16b	//eor3 v19.16b, v19.16b, v21.16b, v17.16b		 	//MODULO - fold into low
	eor3	v3.16b, v11.16b, v3.16b, v28.16b	//eor3 v3.16b, v11.16b, v3.16b, v28.16b				//AES block 8k+11 - result
	stp	q2, q3, [x2], #32			//AES block 8k+10, 8k+11 - store result

	mov	v3.16b, v25.16b					//CTR block 8k+19
	mov	v2.16b, v23.16b					//CTR block 8k+18
	aese	v6.16b, v27.16b						//AES block 8k+14 - round 13

	mov	v1.16b, v22.16b					//CTR block 8k+17
	stp	q4, q5, [x2], #32			//AES block 8k+12, 8k+13 - store result
	eor3	v7.16b, v15.16b, v7.16b, v28.16b	//eor3 v7.16b, v15.16b, v7.16b, v28.16b				//AES block 8k+15 - result

	eor3	v6.16b, v14.16b, v6.16b, v28.16b	//eor3 v6.16b, v14.16b, v6.16b, v28.16b				//AES block 8k+14 - result
	rev32	v4.16b, v30.16b				//CTR block 8k+20
	add	v30.4s, v30.4s, v31.4s		//CTR block 8k+20

	cmp	x0, x5				//.LOOP CONTROL
	stp	q6, q7, [x2], #32			//AES block 8k+14, 8k+15 - store result
	b.lt	L256_dec_main_loop

L256_dec_prepretail:	//PREPRETAIL
	ldp	q26, q27, [x11, #0]					//load rk0, rk1
	rev32	v5.16b, v30.16b				//CTR block 8k+13
	add	v30.4s, v30.4s, v31.4s		//CTR block 8k+13

	rev64	v12.16b, v12.16b						//GHASH block 8k+4
	ldr	q21, [x6, #112]				//load h6k | h5k
	ldr	q24, [x6, #160]				//load h8k | h7k

	rev32	v6.16b, v30.16b				//CTR block 8k+14
	rev64	v8.16b, v8.16b						//GHASH block 8k
	add	v30.4s, v30.4s, v31.4s		//CTR block 8k+14

	ext	v19.16b, v19.16b, v19.16b, #8				//PRE 0
	ldr	q23, [x6, #144]				//load h7l | h7h
	ldr	q25, [x6, #176]				//load h8l | h8h
	rev64	v9.16b, v9.16b						//GHASH block 8k+1

	rev32	v7.16b, v30.16b				//CTR block 8k+15
	rev64	v10.16b, v10.16b						//GHASH block 8k+2
	ldr	q20, [x6, #96]				//load h5l | h5h
	ldr	q22, [x6, #128]				//load h6l | h6h

	aese	v0.16b, v26.16b
	aesmc	v0.16b, v0.16b			//AES block 8k+8 - round 0
	aese	v1.16b, v26.16b
	aesmc	v1.16b, v1.16b			//AES block 8k+9 - round 0
	aese	v4.16b, v26.16b
	aesmc	v4.16b, v4.16b			//AES block 8k+12 - round 0

	aese	v3.16b, v26.16b
	aesmc	v3.16b, v3.16b			//AES block 8k+11 - round 0
	aese	v5.16b, v26.16b
	aesmc	v5.16b, v5.16b			//AES block 8k+13 - round 0
	aese	v6.16b, v26.16b
	aesmc	v6.16b, v6.16b			//AES block 8k+14 - round 0

	aese	v4.16b, v27.16b
	aesmc	v4.16b, v4.16b			//AES block 8k+12 - round 1
	aese	v7.16b, v26.16b
	aesmc	v7.16b, v7.16b			//AES block 8k+15 - round 0
	aese	v2.16b, v26.16b
	aesmc	v2.16b, v2.16b			//AES block 8k+10 - round 0

	ldp	q28, q26, [x11, #32]				//load rk2, rk3
	aese	v0.16b, v27.16b
	aesmc	v0.16b, v0.16b			//AES block 8k+8 - round 1
	eor	v8.16b, v8.16b, v19.16b					//PRE 1

	aese	v7.16b, v27.16b
	aesmc	v7.16b, v7.16b			//AES block 8k+15 - round 1
	aese	v6.16b, v27.16b
	aesmc	v6.16b, v6.16b			//AES block 8k+14 - round 1
	aese	v2.16b, v27.16b
	aesmc	v2.16b, v2.16b			//AES block 8k+10 - round 1

	aese	v3.16b, v27.16b
	aesmc	v3.16b, v3.16b			//AES block 8k+11 - round 1
	aese	v1.16b, v27.16b
	aesmc	v1.16b, v1.16b			//AES block 8k+9 - round 1
	aese	v5.16b, v27.16b
	aesmc	v5.16b, v5.16b			//AES block 8k+13 - round 1

	pmull2	v16.1q, v9.2d, v23.2d				//GHASH block 8k+1 - high
	trn1	v18.2d, v9.2d, v8.2d				//GHASH block 8k, 8k+1 - mid
	pmull	v19.1q, v8.1d, v25.1d				//GHASH block 8k - low

	rev64	v11.16b, v11.16b						//GHASH block 8k+3
	pmull	v23.1q, v9.1d, v23.1d				//GHASH block 8k+1 - low

	aese	v5.16b, v28.16b
	aesmc	v5.16b, v5.16b			//AES block 8k+13 - round 2
	aese	v7.16b, v28.16b
	aesmc	v7.16b, v7.16b			//AES block 8k+15 - round 2
	aese	v1.16b, v28.16b
	aesmc	v1.16b, v1.16b			//AES block 8k+9 - round 2

	aese	v3.16b, v28.16b
	aesmc	v3.16b, v3.16b			//AES block 8k+11 - round 2
	aese	v6.16b, v28.16b
	aesmc	v6.16b, v6.16b			//AES block 8k+14 - round 2
	pmull2	v17.1q, v8.2d, v25.2d				//GHASH block 8k - high

	aese	v0.16b, v28.16b
	aesmc	v0.16b, v0.16b			//AES block 8k+8 - round 2
	aese	v7.16b, v26.16b
	aesmc	v7.16b, v7.16b			//AES block 8k+15 - round 3

	aese	v5.16b, v26.16b
	aesmc	v5.16b, v5.16b			//AES block 8k+13 - round 3
	rev64	v14.16b, v14.16b						//GHASH block 8k+6

	aese	v0.16b, v26.16b
	aesmc	v0.16b, v0.16b			//AES block 8k+8 - round 3
	aese	v2.16b, v28.16b
	aesmc	v2.16b, v2.16b			//AES block 8k+10 - round 2
	aese	v6.16b, v26.16b
	aesmc	v6.16b, v6.16b			//AES block 8k+14 - round 3

	pmull2	v29.1q, v10.2d, v22.2d				//GHASH block 8k+2 - high
	trn2	v8.2d, v9.2d, v8.2d				//GHASH block 8k, 8k+1 - mid
	aese	v4.16b, v28.16b
	aesmc	v4.16b, v4.16b			//AES block 8k+12 - round 2

	ldp	q27, q28, [x11, #64]				//load rk4, rk5
	aese	v1.16b, v26.16b
	aesmc	v1.16b, v1.16b			//AES block 8k+9 - round 3
	pmull2	v9.1q, v11.2d, v20.2d				//GHASH block 8k+3 - high

	aese	v2.16b, v26.16b
	aesmc	v2.16b, v2.16b			//AES block 8k+10 - round 3
	eor	v17.16b, v17.16b, v16.16b				//GHASH block 8k+1 - high
	eor	v8.16b, v8.16b, v18.16b			//GHASH block 8k, 8k+1 - mid

	aese	v4.16b, v26.16b
	aesmc	v4.16b, v4.16b			//AES block 8k+12 - round 3
	pmull	v22.1q, v10.1d, v22.1d				//GHASH block 8k+2 - low
	aese	v3.16b, v26.16b
	aesmc	v3.16b, v3.16b			//AES block 8k+11 - round 3

	eor3	v17.16b, v17.16b, v29.16b, v9.16b	//eor3 v17.16b, v17.16b, v29.16b, v9.16b			//GHASH block 8k+2, 8k+3 - high
	trn1	v29.2d, v11.2d, v10.2d				//GHASH block 8k+2, 8k+3 - mid
	trn2	v10.2d, v11.2d, v10.2d				//GHASH block 8k+2, 8k+3 - mid

	pmull2	v18.1q, v8.2d, v24.2d				//GHASH block 8k	- mid
	pmull	v20.1q, v11.1d, v20.1d				//GHASH block 8k+3 - low
	eor	v19.16b, v19.16b, v23.16b				//GHASH block 8k+1 - low

	pmull	v24.1q, v8.1d, v24.1d				//GHASH block 8k+1 - mid
	aese	v5.16b, v27.16b
	aesmc	v5.16b, v5.16b			//AES block 8k+13 - round 4
	aese	v0.16b, v27.16b
	aesmc	v0.16b, v0.16b			//AES block 8k+8 - round 4

	eor3	v19.16b, v19.16b, v22.16b, v20.16b	//eor3 v19.16b, v19.16b, v22.16b, v20.16b			//GHASH block 8k+2, 8k+3 - low
	ldr	q20, [x6]				//load h1l | h1h
	ldr	q22, [x6, #32]				//load h2l | h2h
	aese	v7.16b, v27.16b
	aesmc	v7.16b, v7.16b			//AES block 8k+15 - round 4

	aese	v2.16b, v27.16b
	aesmc	v2.16b, v2.16b			//AES block 8k+10 - round 4
	aese	v6.16b, v27.16b
	aesmc	v6.16b, v6.16b			//AES block 8k+14 - round 4
	eor	v18.16b, v18.16b, v24.16b				//GHASH block 8k+1 - mid

	eor	v10.16b, v10.16b, v29.16b				//GHASH block 8k+2, 8k+3 - mid
	aese	v7.16b, v28.16b
	aesmc	v7.16b, v7.16b			//AES block 8k+15 - round 5
	aese	v1.16b, v27.16b
	aesmc	v1.16b, v1.16b			//AES block 8k+9 - round 4

	aese	v2.16b, v28.16b
	aesmc	v2.16b, v2.16b			//AES block 8k+10 - round 5
	aese	v3.16b, v27.16b
	aesmc	v3.16b, v3.16b			//AES block 8k+11 - round 4
	aese	v4.16b, v27.16b
	aesmc	v4.16b, v4.16b			//AES block 8k+12 - round 4

	aese	v1.16b, v28.16b
	aesmc	v1.16b, v1.16b			//AES block 8k+9 - round 5
	pmull2	v29.1q, v10.2d, v21.2d				//GHASH block 8k+2 - mid
	aese	v6.16b, v28.16b
	aesmc	v6.16b, v6.16b			//AES block 8k+14 - round 5

	aese	v4.16b, v28.16b
	aesmc	v4.16b, v4.16b			//AES block 8k+12 - round 5
	aese	v3.16b, v28.16b
	aesmc	v3.16b, v3.16b			//AES block 8k+11 - round 5
	pmull	v21.1q, v10.1d, v21.1d				//GHASH block 8k+3 - mid

	aese	v0.16b, v28.16b
	aesmc	v0.16b, v0.16b			//AES block 8k+8 - round 5
	aese	v5.16b, v28.16b
	aesmc	v5.16b, v5.16b			//AES block 8k+13 - round 5
	ldp	q26, q27, [x11, #96]				//load rk6, rk7

	ldr	q23, [x6, #48]				//load h3l | h3h
	ldr	q25, [x6, #80]				//load h4l | h4h
	rev64	v15.16b, v15.16b						//GHASH block 8k+7
	rev64	v13.16b, v13.16b						//GHASH block 8k+5

	eor3	v18.16b, v18.16b, v21.16b, v29.16b	//eor3 v18.16b, v18.16b, v21.16b, v29.16b			//GHASH block 8k+2, 8k+3 - mid

	trn1	v16.2d, v13.2d, v12.2d				//GHASH block 8k+4, 8k+5 - mid

	aese	v0.16b, v26.16b
	aesmc	v0.16b, v0.16b			//AES block 8k+8 - round 6
	ldr	q21, [x6, #16]				//load h2k | h1k
	ldr	q24, [x6, #64]				//load h4k | h3k
	aese	v6.16b, v26.16b
	aesmc	v6.16b, v6.16b			//AES block 8k+14 - round 6

	aese	v5.16b, v26.16b
	aesmc	v5.16b, v5.16b			//AES block 8k+13 - round 6
	aese	v7.16b, v26.16b
	aesmc	v7.16b, v7.16b			//AES block 8k+15 - round 6

	pmull2	v8.1q, v12.2d, v25.2d				//GHASH block 8k+4 - high
	pmull2	v10.1q, v13.2d, v23.2d				//GHASH block 8k+5 - high
	pmull	v25.1q, v12.1d, v25.1d				//GHASH block 8k+4 - low

	trn2	v12.2d, v13.2d, v12.2d				//GHASH block 8k+4, 8k+5 - mid
	pmull	v23.1q, v13.1d, v23.1d				//GHASH block 8k+5 - low
	trn1	v13.2d, v15.2d, v14.2d				//GHASH block 8k+6, 8k+7 - mid

	aese	v7.16b, v27.16b
	aesmc	v7.16b, v7.16b			//AES block 8k+15 - round 7
	pmull2	v11.1q, v14.2d, v22.2d				//GHASH block 8k+6 - high
	aese	v1.16b, v26.16b
	aesmc	v1.16b, v1.16b			//AES block 8k+9 - round 6

	aese	v2.16b, v26.16b
	aesmc	v2.16b, v2.16b			//AES block 8k+10 - round 6
	aese	v3.16b, v26.16b
	aesmc	v3.16b, v3.16b			//AES block 8k+11 - round 6
	aese	v4.16b, v26.16b
	aesmc	v4.16b, v4.16b			//AES block 8k+12 - round 6

	ldp	q28, q26, [x11, #128]				//load rk8, rk9
	pmull	v22.1q, v14.1d, v22.1d				//GHASH block 8k+6 - low
	aese	v5.16b, v27.16b
	aesmc	v5.16b, v5.16b			//AES block 8k+13 - round 7

	aese	v1.16b, v27.16b
	aesmc	v1.16b, v1.16b			//AES block 8k+9 - round 7
	aese	v4.16b, v27.16b
	aesmc	v4.16b, v4.16b			//AES block 8k+12 - round 7

	aese	v6.16b, v27.16b
	aesmc	v6.16b, v6.16b			//AES block 8k+14 - round 7
	aese	v2.16b, v27.16b
	aesmc	v2.16b, v2.16b			//AES block 8k+10 - round 7
	eor3	v17.16b, v17.16b, v8.16b, v10.16b	//eor3 v17.16b, v17.16b, v8.16b, v10.16b			//GHASH block 8k+4, 8k+5 - high

	aese	v0.16b, v27.16b
	aesmc	v0.16b, v0.16b			//AES block 8k+8 - round 7
	trn2	v14.2d, v15.2d, v14.2d				//GHASH block 8k+6, 8k+7 - mid
	aese	v3.16b, v27.16b
	aesmc	v3.16b, v3.16b			//AES block 8k+11 - round 7

	aese	v0.16b, v28.16b
	aesmc	v0.16b, v0.16b			//AES block 8k+8 - round 8
	aese	v7.16b, v28.16b
	aesmc	v7.16b, v7.16b			//AES block 8k+15 - round 8
	aese	v4.16b, v28.16b
	aesmc	v4.16b, v4.16b			//AES block 8k+12 - round 8

	aese	v1.16b, v28.16b
	aesmc	v1.16b, v1.16b			//AES block 8k+9 - round 8
	aese	v5.16b, v28.16b
	aesmc	v5.16b, v5.16b			//AES block 8k+13 - round 8
	aese	v6.16b, v28.16b
	aesmc	v6.16b, v6.16b			//AES block 8k+14 - round 8

	aese	v3.16b, v28.16b
	aesmc	v3.16b, v3.16b			//AES block 8k+11 - round 8
	aese	v4.16b, v26.16b
	aesmc	v4.16b, v4.16b			//AES block 8k+12 - round 9
	eor	v12.16b, v12.16b, v16.16b				//GHASH block 8k+4, 8k+5 - mid

	aese	v0.16b, v26.16b
	aesmc	v0.16b, v0.16b			//AES block 8k+8 - round 9
	aese	v1.16b, v26.16b
	aesmc	v1.16b, v1.16b			//AES block 8k+9 - round 9
	eor	v14.16b, v14.16b, v13.16b				//GHASH block 8k+6, 8k+7 - mid

	aese	v6.16b, v26.16b
	aesmc	v6.16b, v6.16b			//AES block 8k+14 - round 9
	aese	v7.16b, v26.16b
	aesmc	v7.16b, v7.16b			//AES block 8k+15 - round 9
	pmull2	v16.1q, v12.2d, v24.2d				//GHASH block 8k+4 - mid

	aese	v2.16b, v28.16b
	aesmc	v2.16b, v2.16b			//AES block 8k+10 - round 8
	pmull	v24.1q, v12.1d, v24.1d				//GHASH block 8k+5 - mid
	pmull2	v12.1q, v15.2d, v20.2d				//GHASH block 8k+7 - high

	pmull2	v13.1q, v14.2d, v21.2d				//GHASH block 8k+6 - mid
	pmull	v21.1q, v14.1d, v21.1d				//GHASH block 8k+7 - mid
	pmull	v20.1q, v15.1d, v20.1d				//GHASH block 8k+7 - low

	ldp	q27, q28, [x11, #160]				//load rk10, rk11
	eor3	v19.16b, v19.16b, v25.16b, v23.16b	//eor3 v19.16b, v19.16b, v25.16b, v23.16b			//GHASH block 8k+4, 8k+5 - low
	eor3	v18.16b, v18.16b, v24.16b, v16.16b	//eor3 v18.16b, v18.16b, v24.16b, v16.16b			//GHASH block 8k+4, 8k+5 - mid

	aese	v2.16b, v26.16b
	aesmc	v2.16b, v2.16b			//AES block 8k+10 - round 9
	aese	v3.16b, v26.16b
	aesmc	v3.16b, v3.16b			//AES block 8k+11 - round 9
	aese	v5.16b, v26.16b
	aesmc	v5.16b, v5.16b			//AES block 8k+13 - round 9

	eor3	v17.16b, v17.16b, v11.16b, v12.16b	//eor3 v17.16b, v17.16b, v11.16b, v12.16b			//GHASH block 8k+6, 8k+7 - high
	eor3	v19.16b, v19.16b, v22.16b, v20.16b	//eor3 v19.16b, v19.16b, v22.16b, v20.16b			//GHASH block 8k+6, 8k+7 - low
	ldr	d16, [x10]			//MODULO - load modulo constant

	eor3	v18.16b, v18.16b, v21.16b, v13.16b	//eor3 v18.16b, v18.16b, v21.16b, v13.16b			//GHASH block 8k+6, 8k+7 - mid

	aese	v4.16b, v27.16b
	aesmc	v4.16b, v4.16b			//AES block 8k+12 - round 10
	aese	v6.16b, v27.16b
	aesmc	v6.16b, v6.16b			//AES block 8k+14 - round 10
	aese	v5.16b, v27.16b
	aesmc	v5.16b, v5.16b			//AES block 8k+13 - round 10

	aese	v0.16b, v27.16b
	aesmc	v0.16b, v0.16b			//AES block 8k+8 - round 10
	aese	v2.16b, v27.16b
	aesmc	v2.16b, v2.16b			//AES block 8k+10 - round 10
	aese	v3.16b, v27.16b
	aesmc	v3.16b, v3.16b			//AES block 8k+11 - round 10

	eor3	v18.16b, v18.16b, v17.16b, v19.16b	//eor3 v18.16b, v18.16b, v17.16b, v19.16b		 	//MODULO - karatsuba tidy up

	aese	v7.16b, v27.16b
	aesmc	v7.16b, v7.16b			//AES block 8k+15 - round 10
	aese	v1.16b, v27.16b
	aesmc	v1.16b, v1.16b			//AES block 8k+9 - round 10
	ldp	q26, q27, [x11, #192]				//load rk12, rk13

	ext	v21.16b, v17.16b, v17.16b, #8				//MODULO - other top alignment

	aese	v2.16b, v28.16b
	aesmc	v2.16b, v2.16b			//AES block 8k+10 - round 11
	aese	v1.16b, v28.16b
	aesmc	v1.16b, v1.16b			//AES block 8k+9 - round 11
	aese	v0.16b, v28.16b
	aesmc	v0.16b, v0.16b			//AES block 8k+8 - round 11

	pmull	v29.1q, v17.1d, v16.1d			//MODULO - top 64b align with mid
	aese	v3.16b, v28.16b
	aesmc	v3.16b, v3.16b			//AES block 8k+11 - round 11

	aese	v7.16b, v28.16b
	aesmc	v7.16b, v7.16b			//AES block 8k+15 - round 11
	aese	v6.16b, v28.16b
	aesmc	v6.16b, v6.16b			//AES block 8k+14 - round 11
	aese	v4.16b, v28.16b
	aesmc	v4.16b, v4.16b			//AES block 8k+12 - round 11

	aese	v5.16b, v28.16b
	aesmc	v5.16b, v5.16b			//AES block 8k+13 - round 11
	aese	v3.16b, v26.16b
	aesmc	v3.16b, v3.16b			//AES block 8k+11 - round 12

	eor3	v18.16b, v18.16b, v29.16b, v21.16b	//eor3 v18.16b, v18.16b, v29.16b, v21.16b			//MODULO - fold into mid

	aese	v3.16b, v27.16b						//AES block 8k+11 - round 13
	aese	v2.16b, v26.16b
	aesmc	v2.16b, v2.16b			//AES block 8k+10 - round 12
	aese	v6.16b, v26.16b
	aesmc	v6.16b, v6.16b			//AES block 8k+14 - round 12

	pmull	v17.1q, v18.1d, v16.1d			//MODULO - mid 64b align with low
	aese	v4.16b, v26.16b
	aesmc	v4.16b, v4.16b			//AES block 8k+12 - round 12
	aese	v7.16b, v26.16b
	aesmc	v7.16b, v7.16b			//AES block 8k+15 - round 12

	aese	v0.16b, v26.16b
	aesmc	v0.16b, v0.16b			//AES block 8k+8 - round 12
	ldr	q28, [x11, #224]					//load rk14
	aese	v1.16b, v26.16b
	aesmc	v1.16b, v1.16b	        	//AES block 8k+9 - round 12

	aese	v4.16b, v27.16b						//AES block 8k+12 - round 13
	ext	v21.16b, v18.16b, v18.16b, #8			 	//MODULO - other mid alignment
	aese	v5.16b, v26.16b
	aesmc	v5.16b, v5.16b			//AES block 8k+13 - round 12

	aese	v6.16b, v27.16b						//AES block 8k+14 - round 13
	aese	v2.16b, v27.16b						//AES block 8k+10 - round 13
	aese	v1.16b, v27.16b						//AES block 8k+9 - round 13

	aese	v5.16b, v27.16b						//AES block 8k+13 - round 13
	eor3	v19.16b, v19.16b, v21.16b, v17.16b	//eor3 v19.16b, v19.16b, v21.16b, v17.16b		 	//MODULO - fold into low
	add	v30.4s, v30.4s, v31.4s		//CTR block 8k+15

	aese	v7.16b, v27.16b						//AES block 8k+15 - round 13
	aese	v0.16b, v27.16b						//AES block 8k+8 - round 13
L256_dec_tail:	//TAIL

	ext	v16.16b, v19.16b, v19.16b, #8				//prepare final partial tag
	sub	x5, x4, x0		//main_end_input_ptr is number of bytes left to process
	cmp	x5, #112

	ldr	q9, [x0], #16				//AES block 8k+8 - load ciphertext

	ldp	q24, q25, [x6, #160]			//load h8k | h7k
	mov	v29.16b, v28.16b

	ldp	q20, q21, [x6, #96]			//load h5l | h5h

	eor3	v12.16b, v9.16b, v0.16b, v29.16b	//eor3 v12.16b, v9.16b, v0.16b, v29.16b				//AES block 8k+8 - result
	ldp	q22, q23, [x6, #128]			//load h6l | h6h
	b.gt	L256_dec_blocks_more_than_7

	mov	v7.16b, v6.16b
	sub	v30.4s, v30.4s, v31.4s
	mov	v6.16b, v5.16b

	mov	v5.16b, v4.16b
	mov	v4.16b, v3.16b
	movi	v19.8b, #0

	movi	v17.8b, #0
	movi	v18.8b, #0
	mov	v3.16b, v2.16b

	cmp	x5, #96
	mov	v2.16b, v1.16b
	b.gt	L256_dec_blocks_more_than_6

	mov	v7.16b, v6.16b
	mov	v6.16b, v5.16b

	mov	v5.16b, v4.16b
	cmp	x5, #80
	sub	v30.4s, v30.4s, v31.4s

	mov	v4.16b, v3.16b
	mov	v3.16b, v1.16b
	b.gt	L256_dec_blocks_more_than_5

	cmp	x5, #64
	mov	v7.16b, v6.16b
	sub	v30.4s, v30.4s, v31.4s

	mov	v6.16b, v5.16b

	mov	v5.16b, v4.16b
	mov	v4.16b, v1.16b
	b.gt	L256_dec_blocks_more_than_4

	sub	v30.4s, v30.4s, v31.4s
	mov	v7.16b, v6.16b
	cmp	x5, #48

	mov	v6.16b, v5.16b
	mov	v5.16b, v1.16b
	b.gt	L256_dec_blocks_more_than_3

	ldr	q24, [x6, #64]				//load h4k | h3k
	sub	v30.4s, v30.4s, v31.4s
	mov	v7.16b, v6.16b

	cmp	x5, #32
	mov	v6.16b, v1.16b
	b.gt	L256_dec_blocks_more_than_2

	sub	v30.4s, v30.4s, v31.4s

	mov	v7.16b, v1.16b
	cmp	x5, #16
	b.gt	L256_dec_blocks_more_than_1

	sub	v30.4s, v30.4s, v31.4s
	ldr	q21, [x6, #16]				//load h2k | h1k
	b	L256_dec_blocks_less_than_1
L256_dec_blocks_more_than_7:	//blocks	left >  7
	rev64	v8.16b, v9.16b						//GHASH final-7 block
	ldr	q9, [x0], #16				//AES final-6 block - load ciphertext
	st1	{ v12.16b}, [x2], #16				//AES final-7 block  - store result

	ins	v18.d[0], v24.d[1]					//GHASH final-7 block - mid

	eor	v8.16b, v8.16b, v16.16b					//feed in partial tag

	ins	v27.d[0], v8.d[1]					//GHASH final-7 block - mid
	eor3	v12.16b, v9.16b, v1.16b, v29.16b	//eor3 v12.16b, v9.16b, v1.16b, v29.16b				//AES final-6 block - result

	pmull2	v17.1q, v8.2d, v25.2d				//GHASH final-7 block - high

	eor	v27.8b, v27.8b, v8.8b				//GHASH final-7 block - mid
	movi	v16.8b, #0						//supress further partial tag feed in

	pmull	v19.1q, v8.1d, v25.1d				//GHASH final-7 block - low
	pmull	v18.1q, v27.1d, v18.1d			 	//GHASH final-7 block - mid
L256_dec_blocks_more_than_6:	//blocks	left >  6

	rev64	v8.16b, v9.16b						//GHASH final-6 block

	eor	v8.16b, v8.16b, v16.16b					//feed in partial tag
	ldr	q9, [x0], #16				//AES final-5 block - load ciphertext
	movi	v16.8b, #0						//supress further partial tag feed in

	ins	v27.d[0], v8.d[1]					//GHASH final-6 block - mid
	st1	{ v12.16b}, [x2], #16				//AES final-6 block - store result
	pmull2	v28.1q, v8.2d, v23.2d				//GHASH final-6 block - high

	pmull	v26.1q, v8.1d, v23.1d				//GHASH final-6 block - low

	eor3	v12.16b, v9.16b, v2.16b, v29.16b	//eor3 v12.16b, v9.16b, v2.16b, v29.16b				//AES final-5 block - result
	eor	v19.16b, v19.16b, v26.16b					//GHASH final-6 block - low
	eor	v27.8b, v27.8b, v8.8b				//GHASH final-6 block - mid

	pmull	v27.1q, v27.1d, v24.1d				//GHASH final-6 block - mid

	eor	v18.16b, v18.16b, v27.16b				//GHASH final-6 block - mid
	eor	v17.16b, v17.16b, v28.16b					//GHASH final-6 block - high
L256_dec_blocks_more_than_5:	//blocks	left >  5

	rev64	v8.16b, v9.16b						//GHASH final-5 block

	eor	v8.16b, v8.16b, v16.16b					//feed in partial tag

	pmull2	v28.1q, v8.2d, v22.2d				//GHASH final-5 block - high
	ins	v27.d[0], v8.d[1]					//GHASH final-5 block - mid

	ldr	q9, [x0], #16				//AES final-4 block - load ciphertext

	eor	v27.8b, v27.8b, v8.8b				//GHASH final-5 block - mid
	st1	{ v12.16b}, [x2], #16			  	//AES final-5 block - store result

	pmull	v26.1q, v8.1d, v22.1d				//GHASH final-5 block - low
	ins	v27.d[1], v27.d[0]					//GHASH final-5 block - mid

	pmull2	v27.1q, v27.2d, v21.2d				//GHASH final-5 block - mid

	eor	v17.16b, v17.16b, v28.16b					//GHASH final-5 block - high
	eor3	v12.16b, v9.16b, v3.16b, v29.16b	//eor3 v12.16b, v9.16b, v3.16b, v29.16b				//AES final-4 block - result
	eor	v19.16b, v19.16b, v26.16b					//GHASH final-5 block - low

	eor	v18.16b, v18.16b, v27.16b				//GHASH final-5 block - mid
	movi	v16.8b, #0						//supress further partial tag feed in
L256_dec_blocks_more_than_4:	//blocks	left >  4

	rev64	v8.16b, v9.16b						//GHASH final-4 block

	eor	v8.16b, v8.16b, v16.16b					//feed in partial tag

	ins	v27.d[0], v8.d[1]					//GHASH final-4 block - mid
	ldr	q9, [x0], #16				//AES final-3 block - load ciphertext

	movi	v16.8b, #0						//supress further partial tag feed in

	pmull	v26.1q, v8.1d, v20.1d				//GHASH final-4 block - low
	pmull2	v28.1q, v8.2d, v20.2d				//GHASH final-4 block - high

	eor	v27.8b, v27.8b, v8.8b				//GHASH final-4 block - mid

	eor	v17.16b, v17.16b, v28.16b					//GHASH final-4 block - high

	pmull	v27.1q, v27.1d, v21.1d				//GHASH final-4 block - mid

	eor	v19.16b, v19.16b, v26.16b					//GHASH final-4 block - low
	st1	{ v12.16b}, [x2], #16			 	//AES final-4 block - store result

	eor	v18.16b, v18.16b, v27.16b				//GHASH final-4 block - mid
	eor3	v12.16b, v9.16b, v4.16b, v29.16b	//eor3 v12.16b, v9.16b, v4.16b, v29.16b				//AES final-3 block - result
L256_dec_blocks_more_than_3:	//blocks	left >  3

	ldr	q25, [x6, #80]				//load h4l | h4h
	rev64	v8.16b, v9.16b						//GHASH final-3 block

	eor	v8.16b, v8.16b, v16.16b					//feed in partial tag
	ldr	q9, [x0], #16				//AES final-2 block - load ciphertext
	ldr	q24, [x6, #64]				//load h4k | h3k

	ins	v27.d[0], v8.d[1]					//GHASH final-3 block - mid
	st1	{ v12.16b}, [x2], #16			 	//AES final-3 block - store result

	eor3	v12.16b, v9.16b, v5.16b, v29.16b	//eor3 v12.16b, v9.16b, v5.16b, v29.16b				//AES final-2 block - result

	eor	v27.8b, v27.8b, v8.8b				//GHASH final-3 block - mid

	ins	v27.d[1], v27.d[0]					//GHASH final-3 block - mid
	pmull	v26.1q, v8.1d, v25.1d				//GHASH final-3 block - low
	pmull2	v28.1q, v8.2d, v25.2d				//GHASH final-3 block - high

	movi	v16.8b, #0						//supress further partial tag feed in
	pmull2	v27.1q, v27.2d, v24.2d				//GHASH final-3 block - mid
	eor	v19.16b, v19.16b, v26.16b					//GHASH final-3 block - low

	eor	v17.16b, v17.16b, v28.16b					//GHASH final-3 block - high

	eor	v18.16b, v18.16b, v27.16b				//GHASH final-3 block - mid
L256_dec_blocks_more_than_2:	//blocks	left >  2

	rev64	v8.16b, v9.16b						//GHASH final-2 block

	ldr	q23, [x6, #48]				//load h3l | h3h
	ldr	q9, [x0], #16				//AES final-1 block - load ciphertext

	eor	v8.16b, v8.16b, v16.16b					//feed in partial tag

	ins	v27.d[0], v8.d[1]					//GHASH final-2 block - mid

	pmull	v26.1q, v8.1d, v23.1d				//GHASH final-2 block - low
	st1	{ v12.16b}, [x2], #16			  	//AES final-2 block - store result
	eor3	v12.16b, v9.16b, v6.16b, v29.16b	//eor3 v12.16b, v9.16b, v6.16b, v29.16b				//AES final-1 block - result

	eor	v27.8b, v27.8b, v8.8b				//GHASH final-2 block - mid
	eor	v19.16b, v19.16b, v26.16b					//GHASH final-2 block - low
	movi	v16.8b, #0						//supress further partial tag feed in

	pmull	v27.1q, v27.1d, v24.1d				//GHASH final-2 block - mid
	pmull2	v28.1q, v8.2d, v23.2d				//GHASH final-2 block - high

	eor	v18.16b, v18.16b, v27.16b				//GHASH final-2 block - mid
	eor	v17.16b, v17.16b, v28.16b					//GHASH final-2 block - high
L256_dec_blocks_more_than_1:	//blocks	left >  1

	rev64	v8.16b, v9.16b						//GHASH final-1 block

	eor	v8.16b, v8.16b, v16.16b					//feed in partial tag

	ins	v27.d[0], v8.d[1]					//GHASH final-1 block - mid
	ldr	q22, [x6, #32]				//load h2l | h2h

	eor	v27.8b, v27.8b, v8.8b				//GHASH final-1 block - mid
	ldr	q9, [x0], #16				//AES final block - load ciphertext
	st1	{ v12.16b}, [x2], #16			 	//AES final-1 block - store result

	ldr	q21, [x6, #16]				//load h2k | h1k
	pmull	v26.1q, v8.1d, v22.1d				//GHASH final-1 block - low

	ins	v27.d[1], v27.d[0]					//GHASH final-1 block - mid

	eor	v19.16b, v19.16b, v26.16b					//GHASH final-1 block - low

	eor3	v12.16b, v9.16b, v7.16b, v29.16b	//eor3 v12.16b, v9.16b, v7.16b, v29.16b				//AES final block - result
	pmull2	v28.1q, v8.2d, v22.2d				//GHASH final-1 block - high

	pmull2	v27.1q, v27.2d, v21.2d				//GHASH final-1 block - mid

	movi	v16.8b, #0						//supress further partial tag feed in
	eor	v17.16b, v17.16b, v28.16b					//GHASH final-1 block - high

	eor	v18.16b, v18.16b, v27.16b				//GHASH final-1 block - mid
L256_dec_blocks_less_than_1:	//final	whole block (whole-blocks contract: never partial)

	rev32	v30.16b, v30.16b
	str	q30, [x16]					//store the updated counter

	ldr	q20, [x6]				//load h1l | h1h

	rev64	v8.16b, v9.16b						//GHASH final block

	eor	v8.16b, v8.16b, v16.16b					//feed in partial tag

	ins	v16.d[0], v8.d[1]					//GHASH final block - mid
	pmull2	v28.1q, v8.2d, v20.2d				//GHASH final block - high

	eor	v16.8b, v16.8b, v8.8b				//GHASH final block - mid

	pmull	v26.1q, v8.1d, v20.1d				//GHASH final block - low
	eor	v17.16b, v17.16b, v28.16b					//GHASH final block - high

	pmull	v16.1q, v16.1d, v21.1d				//GHASH final block - mid

	eor	v18.16b, v18.16b, v16.16b				//GHASH final block - mid
	ldr	d16, [x10]			//MODULO - load modulo constant
	eor	v19.16b, v19.16b, v26.16b					//GHASH final block - low

	pmull	v21.1q, v17.1d, v16.1d		 	//MODULO - top 64b align with mid
	eor	v14.16b, v17.16b, v19.16b				//MODULO - karatsuba tidy up

	ext	v17.16b, v17.16b, v17.16b, #8				//MODULO - other top alignment
	st1	{ v12.16b}, [x2]				//store all 16B

	eor	v18.16b, v18.16b, v14.16b				//MODULO - karatsuba tidy up

	eor	v21.16b, v17.16b, v21.16b				//MODULO - fold into mid
	eor	v18.16b, v18.16b, v21.16b				//MODULO - fold into mid

	pmull	v17.1q, v18.1d, v16.1d			//MODULO - mid 64b align with low

	ext	v18.16b, v18.16b, v18.16b, #8				//MODULO - other mid alignment
	eor	v19.16b, v19.16b, v17.16b				//MODULO - fold into low

	eor	v19.16b, v19.16b, v18.16b				//MODULO - fold into low
	ext	v19.16b, v19.16b, v19.16b, #8
	rev64	v19.16b, v19.16b
	st1	{ v19.16b }, [x3]
	mov	x0, x9
	CFI_STACKLOAD2(d10,d11,16)
	CFI_STACKLOAD2(d12,d13,32)
	CFI_STACKLOAD2(d14,d15,48)
	CFI_POP2N(d8,d9,80)
	CFI_RET

L256_dec_ret:
	mov	w0, #0x0
	ret
S2N_BN_SIZE_DIRECTIVE(aesv8_gcm_8x_dec_256_wb)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack, "", %progbits
#endif
