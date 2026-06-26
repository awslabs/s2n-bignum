// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// AES-256-GCM encrypt — the COMPLETE aesv8_gcm_8x_enc_256 kernel (all paths).
//
// This is the full 8x-unrolled AES-256-GCM encrypt function from aws-lc's
// aesv8-gcm-armv8-unroll8.S, with NOTHING commented out: a single binary
// handling every input length via its internal length dispatch (the
// .L256_enc_blocks_{more,less}_than_* cascade), exactly like the upstream
// AES-XTS encrypt routine is one binary for all lengths.
//
//    extern size_t aes256_gcm
//      (const uint8_t *in, size_t bit_len, uint8_t *out,
//       uint8_t *xi, uint8_t ivec[16], const void *key,
//       const u128 htable[16]);
//
//   x0 = input_ptr   x1 = bit_length   x2 = output_ptr   x3 = current_tag
//   x4 = counter     x5 = key          x6 = Htable
//   Returns: x0 = byte_length
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_arm.h"

        S2N_BN_SYM_VISIBILITY_DIRECTIVE(aes256_gcm)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(aes256_gcm)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(aes256_gcm)
        .arch armv8.2-a+crypto+sha3
        .text
        .balign 4

S2N_BN_SYMBOL(aes256_gcm):
        CFI_START
	nop
	cbz	x1, .L256_enc_ret
	stp	d8, d9, [sp, #-80]!
	lsr	x9, x1, #3
	mov	x16, x4
	mov	x11, x5
	stp	d10, d11, [sp, #16]
	stp	d12, d13, [sp, #32]
	stp	d14, d15, [sp, #48]
	mov	x5, #0xc200000000000000
	stp	x5, xzr, [sp, #64]
	add	x10, sp, #64

	ld1	{ v0.16b}, [x16]					//CTR block 0

	mov	x5, x9

	mov	x15, #0x100000000			//set up counter increment
	movi	v31.16b, #0x0
	mov	v31.d[1], x15
	sub	x5, x5, #1		//byte_len - 1

	and	x5, x5, #0xffffffffffffff80	//number of bytes to be processed in main loop (at least 1 byte must be handled by tail)

	add	x5, x5, x0

	rev32	v30.16b, v0.16b				//set up reversed counter

	add	v30.4s, v30.4s, v31.4s		//CTR block 0

	rev32	v1.16b, v30.16b				//CTR block 1
	add	v30.4s, v30.4s, v31.4s		//CTR block 1

	rev32	v2.16b, v30.16b				//CTR block 2
	add	v30.4s, v30.4s, v31.4s		//CTR block 2

	rev32	v3.16b, v30.16b				//CTR block 3
	add	v30.4s, v30.4s, v31.4s		//CTR block 3

	rev32	v4.16b, v30.16b				//CTR block 4
	add	v30.4s, v30.4s, v31.4s		//CTR block 4

	rev32	v5.16b, v30.16b				//CTR block 5
	add	v30.4s, v30.4s, v31.4s		//CTR block 5
	ldp	q26, q27, [x11, #0]				 	//load rk0, rk1

	rev32	v6.16b, v30.16b				//CTR block 6
	add	v30.4s, v30.4s, v31.4s		//CTR block 6

	rev32	v7.16b, v30.16b				//CTR block 7

	aese	v3.16b, v26.16b
	aesmc	v3.16b, v3.16b			//AES block 3 - round 0
	aese	v4.16b, v26.16b
	aesmc	v4.16b, v4.16b			//AES block 4 - round 0
	aese	v2.16b, v26.16b
	aesmc	v2.16b, v2.16b			//AES block 2 - round 0

	aese	v0.16b, v26.16b
	aesmc	v0.16b, v0.16b			//AES block 0 - round 0
	aese	v1.16b, v26.16b
	aesmc	v1.16b, v1.16b			//AES block 1 - round 0
	aese	v6.16b, v26.16b
	aesmc	v6.16b, v6.16b			//AES block 6 - round 0

	aese	v5.16b, v26.16b
	aesmc	v5.16b, v5.16b			//AES block 5 - round 0
	aese	v7.16b, v26.16b
	aesmc	v7.16b, v7.16b			//AES block 7 - round 0
	ldp	q28, q26, [x11, #32]				//load rk2, rk3

	aese	v4.16b, v27.16b
	aesmc	v4.16b, v4.16b			//AES block 4 - round 1
	aese	v1.16b, v27.16b
	aesmc	v1.16b, v1.16b			//AES block 1 - round 1
	aese	v3.16b, v27.16b
	aesmc	v3.16b, v3.16b			//AES block 3 - round 1

	aese	v6.16b, v27.16b
	aesmc	v6.16b, v6.16b			//AES block 6 - round 1
	aese	v5.16b, v27.16b
	aesmc	v5.16b, v5.16b			//AES block 5 - round 1

	aese	v2.16b, v27.16b
	aesmc	v2.16b, v2.16b			//AES block 2 - round 1

	aese	v7.16b, v27.16b
	aesmc	v7.16b, v7.16b			//AES block 7 - round 1

	aese	v2.16b, v28.16b
	aesmc	v2.16b, v2.16b			//AES block 2 - round 2
	aese	v3.16b, v28.16b
	aesmc	v3.16b, v3.16b			//AES block 3 - round 2
	aese	v0.16b, v27.16b
	aesmc	v0.16b, v0.16b			//AES block 0 - round 1

	aese	v7.16b, v28.16b
	aesmc	v7.16b, v7.16b			//AES block 7 - round 2
	aese	v6.16b, v28.16b
	aesmc	v6.16b, v6.16b			//AES block 6 - round 2
	aese	v5.16b, v28.16b
	aesmc	v5.16b, v5.16b			//AES block 5 - round 2

	aese	v4.16b, v28.16b
	aesmc	v4.16b, v4.16b			//AES block 4 - round 2
	aese	v0.16b, v28.16b
	aesmc	v0.16b, v0.16b			//AES block 0 - round 2
	aese	v1.16b, v28.16b
	aesmc	v1.16b, v1.16b			//AES block 1 - round 2

	aese	v5.16b, v26.16b
	aesmc	v5.16b, v5.16b			//AES block 5 - round 3
	aese	v3.16b, v26.16b
	aesmc	v3.16b, v3.16b			//AES block 3 - round 3
	ldp	q27, q28, [x11, #64]				//load rk4, rk5

	aese	v4.16b, v26.16b
	aesmc	v4.16b, v4.16b			//AES block 4 - round 3

	aese	v1.16b, v26.16b
	aesmc	v1.16b, v1.16b			//AES block 1 - round 3
	aese	v6.16b, v26.16b
	aesmc	v6.16b, v6.16b			//AES block 6 - round 3
	aese	v7.16b, v26.16b
	aesmc	v7.16b, v7.16b			//AES block 7 - round 3

	aese	v2.16b, v26.16b
	aesmc	v2.16b, v2.16b			//AES block 2 - round 3
	aese	v0.16b, v26.16b
	aesmc	v0.16b, v0.16b			//AES block 0 - round 3

	aese	v4.16b, v27.16b
	aesmc	v4.16b, v4.16b			//AES block 4 - round 4
	aese	v6.16b, v27.16b
	aesmc	v6.16b, v6.16b			//AES block 6 - round 4
	aese	v1.16b, v27.16b
	aesmc	v1.16b, v1.16b			//AES block 1 - round 4

	aese	v2.16b, v27.16b
	aesmc	v2.16b, v2.16b			//AES block 2 - round 4
	aese	v0.16b, v27.16b
	aesmc	v0.16b, v0.16b			//AES block 0 - round 4

	aese	v3.16b, v27.16b
	aesmc	v3.16b, v3.16b			//AES block 3 - round 4
	aese	v7.16b, v27.16b
	aesmc	v7.16b, v7.16b			//AES block 7 - round 4
	aese	v5.16b, v27.16b
	aesmc	v5.16b, v5.16b			//AES block 5 - round 4

	aese	v0.16b, v28.16b
	aesmc	v0.16b, v0.16b			//AES block 0 - round 5
	aese	v2.16b, v28.16b
	aesmc	v2.16b, v2.16b			//AES block 2 - round 5
	ldp	q26, q27, [x11, #96]				//load rk6, rk7

	aese	v1.16b, v28.16b
	aesmc	v1.16b, v1.16b			//AES block 1 - round 5
	aese	v4.16b, v28.16b
	aesmc	v4.16b, v4.16b			//AES block 4 - round 5
	aese	v5.16b, v28.16b
	aesmc	v5.16b, v5.16b			//AES block 5 - round 5

	aese	v3.16b, v28.16b
	aesmc	v3.16b, v3.16b			//AES block 3 - round 5
	aese	v6.16b, v28.16b
	aesmc	v6.16b, v6.16b			//AES block 6 - round 5
	aese	v7.16b, v28.16b
	aesmc	v7.16b, v7.16b			//AES block 7 - round 5

	aese	v1.16b, v26.16b
	aesmc	v1.16b, v1.16b			//AES block 1 - round 6
	aese	v5.16b, v26.16b
	aesmc	v5.16b, v5.16b			//AES block 5 - round 6
	aese	v4.16b, v26.16b
	aesmc	v4.16b, v4.16b			//AES block 4 - round 6

	aese	v2.16b, v26.16b
	aesmc	v2.16b, v2.16b			//AES block 2 - round 6
	aese	v6.16b, v26.16b
	aesmc	v6.16b, v6.16b			//AES block 6 - round 6
	aese	v0.16b, v26.16b
	aesmc	v0.16b, v0.16b			//AES block 0 - round 6

	aese	v7.16b, v26.16b
	aesmc	v7.16b, v7.16b			//AES block 7 - round 6
	aese	v3.16b, v26.16b
	aesmc	v3.16b, v3.16b			//AES block 3 - round 6
	ldp	q28, q26, [x11, #128]				//load rk8, rk9

	aese	v2.16b, v27.16b
	aesmc	v2.16b, v2.16b			//AES block 2 - round 7
	aese	v0.16b, v27.16b
	aesmc	v0.16b, v0.16b			//AES block 0 - round 7

	aese	v7.16b, v27.16b
	aesmc	v7.16b, v7.16b			//AES block 7 - round 7
	aese	v6.16b, v27.16b
	aesmc	v6.16b, v6.16b			//AES block 6 - round 7
	aese	v1.16b, v27.16b
	aesmc	v1.16b, v1.16b			//AES block 1 - round 7

	aese	v5.16b, v27.16b
	aesmc	v5.16b, v5.16b			//AES block 5 - round 7
	aese	v3.16b, v27.16b
	aesmc	v3.16b, v3.16b			//AES block 3 - round 7

	aese	v4.16b, v27.16b
	aesmc	v4.16b, v4.16b			//AES block 4 - round 7

	aese	v6.16b, v28.16b
	aesmc	v6.16b, v6.16b			//AES block 6 - round 8
	aese	v1.16b, v28.16b
	aesmc	v1.16b, v1.16b			//AES block 1 - round 8

	aese	v3.16b, v28.16b
	aesmc	v3.16b, v3.16b			//AES block 3 - round 8
	aese	v0.16b, v28.16b
	aesmc	v0.16b, v0.16b			//AES block 0 - round 8
	aese	v7.16b, v28.16b
	aesmc	v7.16b, v7.16b			//AES block 7 - round 8

	aese	v5.16b, v28.16b
	aesmc	v5.16b, v5.16b			//AES block 5 - round 8
	aese	v4.16b, v28.16b
	aesmc	v4.16b, v4.16b			//AES block 4 - round 8
	aese	v2.16b, v28.16b
	aesmc	v2.16b, v2.16b			//AES block 2 - round 8

	ld1	{ v19.16b}, [x3]
	ext	v19.16b, v19.16b, v19.16b, #8
	rev64	v19.16b, v19.16b
	ldp	q27, q28, [x11, #160]				//load rk10, rk11

	aese	v6.16b, v26.16b
	aesmc	v6.16b, v6.16b			//AES block 6 - round 9
	aese	v7.16b, v26.16b
	aesmc	v7.16b, v7.16b			//AES block 7 - round 9
	aese	v3.16b, v26.16b
	aesmc	v3.16b, v3.16b			//AES block 3 - round 9

	aese	v4.16b, v26.16b
	aesmc	v4.16b, v4.16b			//AES block 4 - round 9
	aese	v5.16b, v26.16b
	aesmc	v5.16b, v5.16b			//AES block 5 - round 9
	aese	v2.16b, v26.16b
	aesmc	v2.16b, v2.16b			//AES block 2 - round 9

	aese	v1.16b, v26.16b
	aesmc	v1.16b, v1.16b			//AES block 1 - round 9

	aese	v7.16b, v27.16b
	aesmc	v7.16b, v7.16b			//AES block 7 - round 10
	aese	v4.16b, v27.16b
	aesmc	v4.16b, v4.16b			//AES block 4 - round 10
	aese	v0.16b, v26.16b
	aesmc	v0.16b, v0.16b			//AES block 0 - round 9

	aese	v1.16b, v27.16b
	aesmc	v1.16b, v1.16b			//AES block 1 - round 10
	aese	v5.16b, v27.16b
	aesmc	v5.16b, v5.16b			//AES block 5 - round 10
	aese	v3.16b, v27.16b
	aesmc	v3.16b, v3.16b			//AES block 3 - round 10

	aese	v2.16b, v27.16b
	aesmc	v2.16b, v2.16b			//AES block 2 - round 10
	aese	v0.16b, v27.16b
	aesmc	v0.16b, v0.16b			//AES block 0 - round 10
	aese	v6.16b, v27.16b
	aesmc	v6.16b, v6.16b			//AES block 6 - round 10

	aese	v4.16b, v28.16b
	aesmc	v4.16b, v4.16b			//AES block 4 - round 11
	ldp	q26, q27, [x11, #192]				//load rk12, rk13
	aese	v5.16b, v28.16b
	aesmc	v5.16b, v5.16b			//AES block 5 - round 11

	aese	v2.16b, v28.16b
	aesmc	v2.16b, v2.16b			//AES block 2 - round 11
	aese	v6.16b, v28.16b
	aesmc	v6.16b, v6.16b			//AES block 6 - round 11
	aese	v1.16b, v28.16b
	aesmc	v1.16b, v1.16b			//AES block 1 - round 11

	aese	v0.16b, v28.16b
	aesmc	v0.16b, v0.16b			//AES block 0 - round 11
	aese	v3.16b, v28.16b
	aesmc	v3.16b, v3.16b			//AES block 3 - round 11
	aese	v7.16b, v28.16b
	aesmc	v7.16b, v7.16b			//AES block 7 - round 11

	add	v30.4s, v30.4s, v31.4s		//CTR block 7
	ldr	q28, [x11, #224]					//load rk14

	aese	v4.16b, v26.16b
	aesmc	v4.16b, v4.16b			//AES block 4 - round 12
	aese	v2.16b, v26.16b
	aesmc	v2.16b, v2.16b			//AES block 2 - round 12
	aese	v1.16b, v26.16b
	aesmc	v1.16b, v1.16b			//AES block 1 - round 12

	aese	v0.16b, v26.16b
	aesmc	v0.16b, v0.16b			//AES block 0 - round 12
	aese	v5.16b, v26.16b
	aesmc	v5.16b, v5.16b			//AES block 5 - round 12
	aese	v3.16b, v26.16b
	aesmc	v3.16b, v3.16b			//AES block 3 - round 12

	aese	v2.16b, v27.16b						//AES block 2 - round 13
	aese	v1.16b, v27.16b						//AES block 1 - round 13
	aese	v4.16b, v27.16b						//AES block 4 - round 13

	aese	v6.16b, v26.16b
	aesmc	v6.16b, v6.16b			//AES block 6 - round 12
	aese	v7.16b, v26.16b
	aesmc	v7.16b, v7.16b			//AES block 7 - round 12

	aese	v0.16b, v27.16b						//AES block 0 - round 13
	aese	v5.16b, v27.16b						//AES block 5 - round 13

	aese	v6.16b, v27.16b						//AES block 6 - round 13
	aese	v7.16b, v27.16b						//AES block 7 - round 13
	aese	v3.16b, v27.16b						//AES block 3 - round 13

	add	x4, x0, x1, lsr #3		//end_input_ptr
	cmp	x0, x5				//check if we have <= 8 blocks
	b.ge	.L256_enc_tail						//handle tail

	ldp	q8, q9, [x0], #32			//AES block 0, 1 - load plaintext

	ldp	q10, q11, [x0], #32			//AES block 2, 3 - load plaintext

.inst	0xce007108	//eor3 v8.16b, v8.16b, v0.16b, v28.16b				//AES block 0 - result
	rev32	v0.16b, v30.16b				//CTR block 8
	add	v30.4s, v30.4s, v31.4s		//CTR block 8

.inst	0xce017129	//eor3 v9.16b, v9.16b, v1.16b, v28.16b				//AES block 1 - result
.inst	0xce03716b	//eor3 v11.16b, v11.16b, v3.16b, v28.16b				//AES block 3 - result

	rev32	v1.16b, v30.16b				//CTR block 9
	add	v30.4s, v30.4s, v31.4s		//CTR block 9
	ldp	q12, q13, [x0], #32			//AES block 4, 5 - load plaintext

	ldp	q14, q15, [x0], #32			//AES block 6, 7 - load plaintext
.inst	0xce02714a	//eor3 v10.16b, v10.16b, v2.16b, v28.16b				//AES block 2 - result
	cmp	x0, x5				//check if we have <= 8 blocks

	rev32	v2.16b, v30.16b				//CTR block 10
	add	v30.4s, v30.4s, v31.4s		//CTR block 10
	stp	q8, q9, [x2], #32			//AES block 0, 1 - store result

	stp	q10, q11, [x2], #32			//AES block 2, 3 - store result

	rev32	v3.16b, v30.16b				//CTR block 11
	add	v30.4s, v30.4s, v31.4s		//CTR block 11

.inst	0xce04718c	//eor3 v12.16b, v12.16b, v4.16b, v28.16b				//AES block 4 - result

.inst	0xce0771ef	//eor3 v15.16b, v15.16b, v7.16b, v28.16b				//AES block 7 - result
.inst	0xce0671ce	//eor3 v14.16b, v14.16b, v6.16b, v28.16b				//AES block 6 - result
.inst	0xce0571ad	//eor3 v13.16b, v13.16b, v5.16b, v28.16b				//AES block 5 - result

	stp	q12, q13, [x2], #32			//AES block 4, 5 - store result
	rev32	v4.16b, v30.16b				//CTR block 12

	stp	q14, q15, [x2], #32			//AES block 6, 7 - store result
	add	v30.4s, v30.4s, v31.4s		//CTR block 12
	b.ge	.L256_enc_prepretail					//do prepretail

.L256_enc_main_loop:	//main	loop start
	ldp	q26, q27, [x11, #0]					//load rk0, rk1

	rev32	v5.16b, v30.16b				//CTR block 8k+13
	add	v30.4s, v30.4s, v31.4s		//CTR block 8k+13
	ldr	q21, [x6, #112]				//load h6k | h5k
	ldr	q24, [x6, #160]				//load h8k | h7k

	rev64	v11.16b, v11.16b						//GHASH block 8k+3
	ldr	q20, [x6, #96]				//load h5l | h5h
	ldr	q22, [x6, #128]				//load h6l | h6h
	rev64	v9.16b, v9.16b						//GHASH block 8k+1

	rev32	v6.16b, v30.16b				//CTR block 8k+14
	add	v30.4s, v30.4s, v31.4s		//CTR block 8k+14
	rev64	v8.16b, v8.16b						//GHASH block 8k

	rev64	v12.16b, v12.16b						//GHASH block 8k+4
	ext	v19.16b, v19.16b, v19.16b, #8				//PRE 0
	ldr	q23, [x6, #144]				//load h7l | h7h
	ldr	q25, [x6, #176]				//load h8l | h8h

	aese	v3.16b, v26.16b
	aesmc	v3.16b, v3.16b			//AES block 8k+11 - round 0
	aese	v5.16b, v26.16b
	aesmc	v5.16b, v5.16b			//AES block 8k+13 - round 0
	rev32	v7.16b, v30.16b				//CTR block 8k+15

	aese	v0.16b, v26.16b
	aesmc	v0.16b, v0.16b			//AES block 8k+8 - round 0
	aese	v1.16b, v26.16b
	aesmc	v1.16b, v1.16b			//AES block 8k+9 - round 0
	aese	v6.16b, v26.16b
	aesmc	v6.16b, v6.16b			//AES block 8k+14 - round 0

	aese	v7.16b, v26.16b
	aesmc	v7.16b, v7.16b			//AES block 8k+15 - round 0
	aese	v2.16b, v26.16b
	aesmc	v2.16b, v2.16b			//AES block 8k+10 - round 0
	aese	v4.16b, v26.16b
	aesmc	v4.16b, v4.16b			//AES block 8k+12 - round 0

	ldp	q28, q26, [x11, #32]				//load rk2, rk3
	eor	v8.16b, v8.16b, v19.16b				 	//PRE 1
	aese	v6.16b, v27.16b
	aesmc	v6.16b, v6.16b			//AES block 8k+14 - round 1

	aese	v2.16b, v27.16b
	aesmc	v2.16b, v2.16b			//AES block 8k+10 - round 1
	aese	v1.16b, v27.16b
	aesmc	v1.16b, v1.16b			//AES block 8k+9 - round 1
	aese	v0.16b, v27.16b
	aesmc	v0.16b, v0.16b			//AES block 8k+8 - round 1

	aese	v4.16b, v27.16b
	aesmc	v4.16b, v4.16b			//AES block 8k+12 - round 1
	aese	v3.16b, v27.16b
	aesmc	v3.16b, v3.16b			//AES block 8k+11 - round 1
	aese	v5.16b, v27.16b
	aesmc	v5.16b, v5.16b			//AES block 8k+13 - round 1

	pmull2	v17.1q, v8.2d, v25.2d				//GHASH block 8k - high
	pmull	v19.1q, v8.1d, v25.1d				//GHASH block 8k - low
	pmull2	v16.1q, v9.2d, v23.2d				//GHASH block 8k+1 - high

	trn1	v18.2d, v9.2d, v8.2d				//GHASH block 8k, 8k+1 - mid
	trn2	v8.2d, v9.2d, v8.2d				//GHASH block 8k, 8k+1 - mid
	aese	v7.16b, v27.16b
	aesmc	v7.16b, v7.16b			//AES block 8k+15 - round 1

	aese	v1.16b, v28.16b
	aesmc	v1.16b, v1.16b			//AES block 8k+9 - round 2
	aese	v5.16b, v28.16b
	aesmc	v5.16b, v5.16b			//AES block 8k+13 - round 2
	aese	v6.16b, v28.16b
	aesmc	v6.16b, v6.16b			//AES block 8k+14 - round 2

	aese	v2.16b, v28.16b
	aesmc	v2.16b, v2.16b			//AES block 8k+10 - round 2
	pmull	v23.1q, v9.1d, v23.1d				//GHASH block 8k+1 - low
	aese	v4.16b, v28.16b
	aesmc	v4.16b, v4.16b			//AES block 8k+12 - round 2

	aese	v5.16b, v26.16b
	aesmc	v5.16b, v5.16b			//AES block 8k+13 - round 3
	aese	v6.16b, v26.16b
	aesmc	v6.16b, v6.16b			//AES block 8k+14 - round 3
	aese	v0.16b, v28.16b
	aesmc	v0.16b, v0.16b			//AES block 8k+8 - round 2

	aese	v1.16b, v26.16b
	aesmc	v1.16b, v1.16b			//AES block 8k+9 - round 3
	aese	v7.16b, v28.16b
	aesmc	v7.16b, v7.16b			//AES block 8k+15 - round 2
	aese	v3.16b, v28.16b
	aesmc	v3.16b, v3.16b			//AES block 8k+11 - round 2

	aese	v4.16b, v26.16b
	aesmc	v4.16b, v4.16b			//AES block 8k+12 - round 3
	rev64	v14.16b, v14.16b						//GHASH block 8k+6
	pmull2	v9.1q, v11.2d, v20.2d				//GHASH block 8k+3 - high

	aese	v3.16b, v26.16b
	aesmc	v3.16b, v3.16b			//AES block 8k+11 - round 3
	ldp	q27, q28, [x11, #64]				//load rk4, rk5
	rev64	v10.16b, v10.16b						//GHASH block 8k+2

	aese	v2.16b, v26.16b
	aesmc	v2.16b, v2.16b			//AES block 8k+10 - round 3
	aese	v7.16b, v26.16b
	aesmc	v7.16b, v7.16b			//AES block 8k+15 - round 3
	aese	v0.16b, v26.16b
	aesmc	v0.16b, v0.16b			//AES block 8k+8 - round 3

	eor	v17.16b, v17.16b, v16.16b				//GHASH block 8k+1 - high
	pmull2	v29.1q, v10.2d, v22.2d				//GHASH block 8k+2 - high
	rev64	v13.16b, v13.16b						//GHASH block 8k+5

	pmull	v20.1q, v11.1d, v20.1d				//GHASH block 8k+3 - low
	eor	v19.16b, v19.16b, v23.16b				//GHASH block 8k+1 - low
	ldr	q23, [x6, #48]				//load h3l | h3h
	ldr	q25, [x6, #80]				//load h4l | h4h

	trn1	v16.2d, v13.2d, v12.2d				//GHASH block 8k+4, 8k+5 - mid
.inst	0xce1d2631	//eor3 v17.16b, v17.16b, v29.16b, v9.16b			//GHASH block 8k+2, 8k+3 - high
	pmull	v22.1q, v10.1d, v22.1d				//GHASH block 8k+2 - low

	aese	v4.16b, v27.16b
	aesmc	v4.16b, v4.16b			//AES block 8k+12 - round 4
	aese	v1.16b, v27.16b
	aesmc	v1.16b, v1.16b			//AES block 8k+9 - round 4
	aese	v5.16b, v27.16b
	aesmc	v5.16b, v5.16b			//AES block 8k+13 - round 4

	aese	v7.16b, v27.16b
	aesmc	v7.16b, v7.16b			//AES block 8k+15 - round 4
	aese	v3.16b, v27.16b
	aesmc	v3.16b, v3.16b			//AES block 8k+11 - round 4
	aese	v2.16b, v27.16b
	aesmc	v2.16b, v2.16b			//AES block 8k+10 - round 4

	trn1	v29.2d, v11.2d, v10.2d				//GHASH block 8k+2, 8k+3 - mid
	aese	v6.16b, v27.16b
	aesmc	v6.16b, v6.16b			//AES block 8k+14 - round 4
	aese	v0.16b, v27.16b
	aesmc	v0.16b, v0.16b			//AES block 8k+8 - round 4

	trn2	v10.2d, v11.2d, v10.2d				//GHASH block 8k+2, 8k+3 - mid
	eor	v8.16b, v8.16b, v18.16b			//GHASH block 8k, 8k+1 - mid
	ldp	q26, q27, [x11, #96]				//load rk6, rk7

	aese	v5.16b, v28.16b
	aesmc	v5.16b, v5.16b			//AES block 8k+13 - round 5
	aese	v7.16b, v28.16b
	aesmc	v7.16b, v7.16b			//AES block 8k+15 - round 5
	aese	v4.16b, v28.16b
	aesmc	v4.16b, v4.16b			//AES block 8k+12 - round 5

	eor	v10.16b, v10.16b, v29.16b				//GHASH block 8k+2, 8k+3 - mid
	aese	v2.16b, v28.16b
	aesmc	v2.16b, v2.16b			//AES block 8k+10 - round 5
	rev64	v15.16b, v15.16b						//GHASH block 8k+7

	aese	v3.16b, v28.16b
	aesmc	v3.16b, v3.16b			//AES block 8k+11 - round 5
	aese	v6.16b, v28.16b
	aesmc	v6.16b, v6.16b			//AES block 8k+14 - round 5
	aese	v1.16b, v28.16b
	aesmc	v1.16b, v1.16b			//AES block 8k+9 - round 5

	pmull2	v29.1q, v10.2d, v21.2d				//GHASH block 8k+2 - mid
	pmull2	v18.1q, v8.2d, v24.2d				//GHASH block 8k	- mid
	aese	v0.16b, v28.16b
	aesmc	v0.16b, v0.16b			//AES block 8k+8 - round 5

	pmull	v24.1q, v8.1d, v24.1d				//GHASH block 8k+1 - mid
	aese	v4.16b, v26.16b
	aesmc	v4.16b, v4.16b			//AES block 8k+12 - round 6
	aese	v2.16b, v26.16b
	aesmc	v2.16b, v2.16b			//AES block 8k+10 - round 6

	aese	v6.16b, v26.16b
	aesmc	v6.16b, v6.16b			//AES block 8k+14 - round 6
	aese	v1.16b, v26.16b
	aesmc	v1.16b, v1.16b			//AES block 8k+9 - round 6
	aese	v7.16b, v26.16b
	aesmc	v7.16b, v7.16b			//AES block 8k+15 - round 6

	eor	v18.16b, v18.16b, v24.16b				//GHASH block 8k+1 - mid
	pmull	v21.1q, v10.1d, v21.1d				//GHASH block 8k+3 - mid
	aese	v5.16b, v26.16b
	aesmc	v5.16b, v5.16b			//AES block 8k+13 - round 6

.inst	0xce165273	//eor3 v19.16b, v19.16b, v22.16b, v20.16b			//GHASH block 8k+2, 8k+3 - low
	aese	v3.16b, v26.16b
	aesmc	v3.16b, v3.16b			//AES block 8k+11 - round 6
	aese	v0.16b, v26.16b
	aesmc	v0.16b, v0.16b			//AES block 8k+8 - round 6

	ldp	q28, q26, [x11, #128]				//load rk8, rk9
	pmull2	v8.1q, v12.2d, v25.2d				//GHASH block 8k+4 - high
	aese	v5.16b, v27.16b
	aesmc	v5.16b, v5.16b			//AES block 8k+13 - round 7

	ldr	q20, [x6]				//load h1l | h1h
	ldr	q22, [x6, #32]				//load h2l | h2h
	aese	v2.16b, v27.16b
	aesmc	v2.16b, v2.16b			//AES block 8k+10 - round 7
.inst	0xce157652	//eor3 v18.16b, v18.16b, v21.16b, v29.16b			//GHASH block 8k+2, 8k+3 - mid

	ldr	q21, [x6, #16]				//load h2k | h1k
	ldr	q24, [x6, #64]				//load h4k | h3k
	aese	v6.16b, v27.16b
	aesmc	v6.16b, v6.16b			//AES block 8k+14 - round 7
	aese	v3.16b, v27.16b
	aesmc	v3.16b, v3.16b			//AES block 8k+11 - round 7

	aese	v0.16b, v27.16b
	aesmc	v0.16b, v0.16b			//AES block 8k+8 - round 7
	aese	v7.16b, v27.16b
	aesmc	v7.16b, v7.16b			//AES block 8k+15 - round 7
	pmull	v25.1q, v12.1d, v25.1d				//GHASH block 8k+4 - low

	trn2	v12.2d, v13.2d, v12.2d				//GHASH block 8k+4, 8k+5 - mid
	aese	v4.16b, v27.16b
	aesmc	v4.16b, v4.16b			//AES block 8k+12 - round 7
	aese	v1.16b, v27.16b
	aesmc	v1.16b, v1.16b			//AES block 8k+9 - round 7

	pmull2	v10.1q, v13.2d, v23.2d				//GHASH block 8k+5 - high
	aese	v7.16b, v28.16b
	aesmc	v7.16b, v7.16b			//AES block 8k+15 - round 8
	aese	v0.16b, v28.16b
	aesmc	v0.16b, v0.16b			//AES block 8k+8 - round 8

	pmull	v23.1q, v13.1d, v23.1d				//GHASH block 8k+5 - low
	trn1	v13.2d, v15.2d, v14.2d				//GHASH block 8k+6, 8k+7 - mid
	eor	v12.16b, v12.16b, v16.16b				//GHASH block 8k+4, 8k+5 - mid

	aese	v3.16b, v28.16b
	aesmc	v3.16b, v3.16b			//AES block 8k+11 - round 8
	aese	v0.16b, v26.16b
	aesmc	v0.16b, v0.16b			//AES block 8k+8 - round 9
	aese	v1.16b, v28.16b
	aesmc	v1.16b, v1.16b			//AES block 8k+9 - round 8

	pmull2	v16.1q, v12.2d, v24.2d				//GHASH block 8k+4 - mid
	pmull	v24.1q, v12.1d, v24.1d				//GHASH block 8k+5 - mid
	aese	v2.16b, v28.16b
	aesmc	v2.16b, v2.16b			//AES block 8k+10 - round 8

	aese	v5.16b, v28.16b
	aesmc	v5.16b, v5.16b			//AES block 8k+13 - round 8
	pmull2	v11.1q, v14.2d, v22.2d				//GHASH block 8k+6 - high
	pmull	v22.1q, v14.1d, v22.1d				//GHASH block 8k+6 - low

	aese	v6.16b, v28.16b
	aesmc	v6.16b, v6.16b			//AES block 8k+14 - round 8
	trn2	v14.2d, v15.2d, v14.2d				//GHASH block 8k+6, 8k+7 - mid
	aese	v4.16b, v28.16b
	aesmc	v4.16b, v4.16b			//AES block 8k+12 - round 8

.inst	0xce184252	//eor3 v18.16b, v18.16b, v24.16b, v16.16b			//GHASH block 8k+4, 8k+5 - mid
	aese	v7.16b, v26.16b
	aesmc	v7.16b, v7.16b			//AES block 8k+15 - round 9
	aese	v5.16b, v26.16b
	aesmc	v5.16b, v5.16b			//AES block 8k+13 - round 9

	eor	v14.16b, v14.16b, v13.16b				//GHASH block 8k+6, 8k+7 - mid
	aese	v6.16b, v26.16b
	aesmc	v6.16b, v6.16b			//AES block 8k+14 - round 9
	aese	v4.16b, v26.16b
	aesmc	v4.16b, v4.16b			//AES block 8k+12 - round 9

	ldp	q27, q28, [x11, #160]				//load rk10, rk11
	aese	v2.16b, v26.16b
	aesmc	v2.16b, v2.16b			//AES block 8k+10 - round 9
	aese	v3.16b, v26.16b
	aesmc	v3.16b, v3.16b			//AES block 8k+11 - round 9

	pmull2	v12.1q, v15.2d, v20.2d				//GHASH block 8k+7 - high
.inst	0xce195e73	//eor3 v19.16b, v19.16b, v25.16b, v23.16b			//GHASH block 8k+4, 8k+5 - low
	pmull	v20.1q, v15.1d, v20.1d				//GHASH block 8k+7 - low

	ldr	d16, [x10]			//MODULO - load modulo constant
	pmull2	v13.1q, v14.2d, v21.2d				//GHASH block 8k+6 - mid
	pmull	v21.1q, v14.1d, v21.1d				//GHASH block 8k+7 - mid

	aese	v1.16b, v26.16b
	aesmc	v1.16b, v1.16b			//AES block 8k+9 - round 9

.inst	0xce153652	//eor3 v18.16b, v18.16b, v21.16b, v13.16b			//GHASH block 8k+6, 8k+7 - mid
.inst	0xce165273	//eor3 v19.16b, v19.16b, v22.16b, v20.16b			//GHASH block 8k+6, 8k+7 - low
.inst	0xce082a31	//eor3 v17.16b, v17.16b, v8.16b, v10.16b			//GHASH block 8k+4, 8k+5 - high

	aese	v4.16b, v27.16b
	aesmc	v4.16b, v4.16b			//AES block 8k+12 - round 10
	aese	v3.16b, v27.16b
	aesmc	v3.16b, v3.16b			//AES block 8k+11 - round 10
	aese	v5.16b, v27.16b
	aesmc	v5.16b, v5.16b			//AES block 8k+13 - round 10

	aese	v0.16b, v27.16b
	aesmc	v0.16b, v0.16b			//AES block 8k+8 - round 10
	aese	v2.16b, v27.16b
	aesmc	v2.16b, v2.16b			//AES block 8k+10 - round 10
	add	v30.4s, v30.4s, v31.4s		//CTR block 8k+15

	aese	v1.16b, v27.16b
	aesmc	v1.16b, v1.16b			//AES block 8k+9 - round 10
	aese	v7.16b, v27.16b
	aesmc	v7.16b, v7.16b			//AES block 8k+15 - round 10
	aese	v6.16b, v27.16b
	aesmc	v6.16b, v6.16b			//AES block 8k+14 - round 10

.inst	0xce0b3231	//eor3 v17.16b, v17.16b, v11.16b, v12.16b			//GHASH block 8k+6, 8k+7 - high

	ldp	q26, q27, [x11, #192]				//load rk12, rk13
	rev32	v20.16b, v30.16b					//CTR block 8k+16

	ext	v21.16b, v17.16b, v17.16b, #8			 	//MODULO - other top alignment
	ldp	q8, q9, [x0], #32			//AES block 8k+8, 8k+9 - load plaintext
	aese	v2.16b, v28.16b
	aesmc	v2.16b, v2.16b			//AES block 8k+10 - round 11

	aese	v6.16b, v28.16b
	aesmc	v6.16b, v6.16b			//AES block 8k+14 - round 11
	add	v30.4s, v30.4s, v31.4s		//CTR block 8k+16
	aese	v3.16b, v28.16b
	aesmc	v3.16b, v3.16b			//AES block 8k+11 - round 11

	aese	v0.16b, v28.16b
	aesmc	v0.16b, v0.16b			//AES block 8k+8 - round 11
	aese	v7.16b, v28.16b
	aesmc	v7.16b, v7.16b			//AES block 8k+15 - round 11

	pmull	v29.1q, v17.1d, v16.1d		 	//MODULO - top 64b align with mid
	aese	v1.16b, v28.16b
	aesmc	v1.16b, v1.16b			//AES block 8k+9 - round 11

	aese	v7.16b, v26.16b
	aesmc	v7.16b, v7.16b			//AES block 8k+15 - round 12
	aese	v5.16b, v28.16b
	aesmc	v5.16b, v5.16b			//AES block 8k+13 - round 11

	aese	v3.16b, v26.16b
	aesmc	v3.16b, v3.16b			//AES block 8k+11 - round 12
	aese	v6.16b, v26.16b
	aesmc	v6.16b, v6.16b			//AES block 8k+14 - round 12
	rev32	v22.16b, v30.16b					//CTR block 8k+17

	add	v30.4s, v30.4s, v31.4s		//CTR block 8k+17
	aese	v4.16b, v28.16b
	aesmc	v4.16b, v4.16b			//AES block 8k+12 - round 11
.inst	0xce114e52	//eor3 v18.16b, v18.16b, v17.16b, v19.16b		 	//MODULO - karatsuba tidy up

	aese	v5.16b, v26.16b
	aesmc	v5.16b, v5.16b			//AES block 8k+13 - round 12
	ldr	q28, [x11, #224]					//load rk14
	aese	v7.16b, v27.16b						//AES block 8k+15 - round 13

	ldp	q10, q11, [x0], #32			//AES block 8k+10, 8k+11 - load plaintext
	aese	v2.16b, v26.16b
	aesmc	v2.16b, v2.16b			//AES block 8k+10 - round 12
	aese	v4.16b, v26.16b
	aesmc	v4.16b, v4.16b			//AES block 8k+12 - round 12

.inst	0xce1d5652	//eor3 v18.16b, v18.16b, v29.16b, v21.16b			//MODULO - fold into mid
	aese	v1.16b, v26.16b
	aesmc	v1.16b, v1.16b			//AES block 8k+9 - round 12
	ldp	q12, q13, [x0], #32			//AES block 4, 5 - load plaintext

	ldp	q14, q15, [x0], #32			//AES block 6, 7 - load plaintext
	aese	v2.16b, v27.16b						//AES block 8k+10 - round 13
	aese	v4.16b, v27.16b						//AES block 8k+12 - round 13

	rev32	v23.16b, v30.16b					//CTR block 8k+18
	add	v30.4s, v30.4s, v31.4s		//CTR block 8k+18
	aese	v5.16b, v27.16b						//AES block 8k+13 - round 13

	aese	v0.16b, v26.16b
	aesmc	v0.16b, v0.16b			//AES block 8k+8 - round 12
	aese	v3.16b, v27.16b						//AES block 8k+11 - round 13
	cmp	x0, x5				//.LOOP CONTROL

.inst	0xce02714a	//eor3 v10.16b, v10.16b, v2.16b, v28.16b				//AES block 8k+10 - result
	rev32	v25.16b, v30.16b					//CTR block 8k+19
	add	v30.4s, v30.4s, v31.4s		//CTR block 8k+19

	aese	v0.16b, v27.16b						//AES block 8k+8 - round 13
	aese	v6.16b, v27.16b						//AES block 8k+14 - round 13
.inst	0xce0571ad	//eor3 v13.16b, v13.16b, v5.16b, v28.16b				//AES block 5 - result

	ext	v21.16b, v18.16b, v18.16b, #8				//MODULO - other mid alignment
	pmull	v17.1q, v18.1d, v16.1d			//MODULO - mid 64b align with low
	aese	v1.16b, v27.16b						//AES block 8k+9 - round 13

.inst	0xce04718c	//eor3 v12.16b, v12.16b, v4.16b, v28.16b				//AES block 4 - result
	rev32	v4.16b, v30.16b				//CTR block 8k+20
.inst	0xce03716b	//eor3 v11.16b, v11.16b, v3.16b, v28.16b				//AES block 8k+11 - result

	mov	v3.16b, v25.16b					//CTR block 8k+19
.inst	0xce017129	//eor3 v9.16b, v9.16b, v1.16b, v28.16b				//AES block 8k+9 - result
.inst	0xce007108	//eor3 v8.16b, v8.16b, v0.16b, v28.16b				//AES block 8k+8 - result

	add	v30.4s, v30.4s, v31.4s		//CTR block 8k+20
	stp	q8, q9, [x2], #32			//AES block 8k+8, 8k+9 - store result
	mov	v2.16b, v23.16b					//CTR block 8k+18

.inst	0xce0771ef	//eor3 v15.16b, v15.16b, v7.16b, v28.16b				//AES block 7 - result
.inst	0xce154673	//eor3 v19.16b, v19.16b, v21.16b, v17.16b		 	//MODULO - fold into low
	stp	q10, q11, [x2], #32			//AES block 8k+10, 8k+11 - store result

.inst	0xce0671ce	//eor3 v14.16b, v14.16b, v6.16b, v28.16b				//AES block 6 - result
	mov	v1.16b, v22.16b					//CTR block 8k+17
	stp	q12, q13, [x2], #32			//AES block 4, 5 - store result

	stp	q14, q15, [x2], #32			//AES block 6, 7 - store result
	mov	v0.16b, v20.16b					//CTR block 8k+16
	b.lt	.L256_enc_main_loop

.L256_enc_prepretail:	//PREPRETAIL
	rev32	v5.16b, v30.16b				//CTR block 8k+13
	ldp	q26, q27, [x11, #0]					//load rk0, rk1
	add	v30.4s, v30.4s, v31.4s		//CTR block 8k+13

	rev64	v10.16b, v10.16b						//GHASH block 8k+2

	rev32	v6.16b, v30.16b				//CTR block 8k+14
	add	v30.4s, v30.4s, v31.4s		//CTR block 8k+14

	rev64	v13.16b, v13.16b						//GHASH block 8k+5
	ldr	q21, [x6, #112]				//load h6k | h5k
	ldr	q24, [x6, #160]				//load h8k | h7k

	rev32	v7.16b, v30.16b				//CTR block 8k+15

	aese	v6.16b, v26.16b
	aesmc	v6.16b, v6.16b			//AES block 8k+14 - round 0
	aese	v4.16b, v26.16b
	aesmc	v4.16b, v4.16b			//AES block 8k+12 - round 0
	aese	v1.16b, v26.16b
	aesmc	v1.16b, v1.16b			//AES block 8k+9 - round 0

	aese	v5.16b, v26.16b
	aesmc	v5.16b, v5.16b			//AES block 8k+13 - round 0
	aese	v0.16b, v26.16b
	aesmc	v0.16b, v0.16b			//AES block 8k+8 - round 0

	aese	v2.16b, v26.16b
	aesmc	v2.16b, v2.16b			//AES block 8k+10 - round 0
	aese	v7.16b, v26.16b
	aesmc	v7.16b, v7.16b			//AES block 8k+15 - round 0
	aese	v3.16b, v26.16b
	aesmc	v3.16b, v3.16b			//AES block 8k+11 - round 0

	ext	v19.16b, v19.16b, v19.16b, #8				//PRE 0
	rev64	v8.16b, v8.16b						//GHASH block 8k
	aese	v1.16b, v27.16b
	aesmc	v1.16b, v1.16b			//AES block 8k+9 - round 1

	rev64	v9.16b, v9.16b						//GHASH block 8k+1
	ldp	q28, q26, [x11, #32]				//load rk2, rk3
	aese	v3.16b, v27.16b
	aesmc	v3.16b, v3.16b			//AES block 8k+11 - round 1

	ldr	q23, [x6, #144]				//load h7l | h7h
	ldr	q25, [x6, #176]				//load h8l | h8h
	aese	v2.16b, v27.16b
	aesmc	v2.16b, v2.16b			//AES block 8k+10 - round 1

	ldr	q20, [x6, #96]				//load h5l | h5h
	ldr	q22, [x6, #128]				//load h6l | h6h
	aese	v0.16b, v27.16b
	aesmc	v0.16b, v0.16b			//AES block 8k+8 - round 1
	aese	v5.16b, v27.16b
	aesmc	v5.16b, v5.16b			//AES block 8k+13 - round 1

	aese	v4.16b, v27.16b
	aesmc	v4.16b, v4.16b			//AES block 8k+12 - round 1
	eor	v8.16b, v8.16b, v19.16b					//PRE 1

	rev64	v11.16b, v11.16b						//GHASH block 8k+3
	aese	v6.16b, v27.16b
	aesmc	v6.16b, v6.16b			//AES block 8k+14 - round 1

	aese	v1.16b, v28.16b
	aesmc	v1.16b, v1.16b			//AES block 8k+9 - round 2
	aese	v2.16b, v28.16b
	aesmc	v2.16b, v2.16b			//AES block 8k+10 - round 2
	aese	v7.16b, v27.16b
	aesmc	v7.16b, v7.16b			//AES block 8k+15 - round 1

	aese	v4.16b, v28.16b
	aesmc	v4.16b, v4.16b			//AES block 8k+12 - round 2
	aese	v0.16b, v28.16b
	aesmc	v0.16b, v0.16b			//AES block 8k+8 - round 2
	aese	v6.16b, v28.16b
	aesmc	v6.16b, v6.16b			//AES block 8k+14 - round 2

	aese	v5.16b, v28.16b
	aesmc	v5.16b, v5.16b			//AES block 8k+13 - round 2
	aese	v7.16b, v28.16b
	aesmc	v7.16b, v7.16b			//AES block 8k+15 - round 2
	aese	v3.16b, v28.16b
	aesmc	v3.16b, v3.16b			//AES block 8k+11 - round 2

	ldp	q27, q28, [x11, #64]				//load rk4, rk5
	trn1	v18.2d, v9.2d, v8.2d				//GHASH block 8k, 8k+1 - mid
	pmull2	v17.1q, v8.2d, v25.2d				//GHASH block 8k - high

	rev64	v14.16b, v14.16b						//GHASH block 8k+6
	aese	v4.16b, v26.16b
	aesmc	v4.16b, v4.16b			//AES block 8k+12 - round 3
	pmull2	v16.1q, v9.2d, v23.2d				//GHASH block 8k+1 - high

	aese	v7.16b, v26.16b
	aesmc	v7.16b, v7.16b			//AES block 8k+15 - round 3
	pmull	v19.1q, v8.1d, v25.1d				//GHASH block 8k - low
	trn2	v8.2d, v9.2d, v8.2d				//GHASH block 8k, 8k+1 - mid

	pmull2	v29.1q, v10.2d, v22.2d				//GHASH block 8k+2 - high
	aese	v6.16b, v26.16b
	aesmc	v6.16b, v6.16b			//AES block 8k+14 - round 3

	aese	v2.16b, v26.16b
	aesmc	v2.16b, v2.16b			//AES block 8k+10 - round 3
	aese	v3.16b, v26.16b
	aesmc	v3.16b, v3.16b			//AES block 8k+11 - round 3
	eor	v17.16b, v17.16b, v16.16b				//GHASH block 8k+1 - high

	pmull	v23.1q, v9.1d, v23.1d				//GHASH block 8k+1 - low
	pmull2	v9.1q, v11.2d, v20.2d				//GHASH block 8k+3 - high
	aese	v1.16b, v26.16b
	aesmc	v1.16b, v1.16b			//AES block 8k+9 - round 3

	aese	v0.16b, v26.16b
	aesmc	v0.16b, v0.16b			//AES block 8k+8 - round 3
	eor	v8.16b, v8.16b, v18.16b			//GHASH block 8k, 8k+1 - mid
	aese	v5.16b, v26.16b
	aesmc	v5.16b, v5.16b			//AES block 8k+13 - round 3

	pmull	v22.1q, v10.1d, v22.1d				//GHASH block 8k+2 - low
	aese	v1.16b, v27.16b
	aesmc	v1.16b, v1.16b			//AES block 8k+9 - round 4
	aese	v6.16b, v27.16b
	aesmc	v6.16b, v6.16b			//AES block 8k+14 - round 4

	aese	v0.16b, v27.16b
	aesmc	v0.16b, v0.16b			//AES block 8k+8 - round 4
	aese	v2.16b, v27.16b
	aesmc	v2.16b, v2.16b			//AES block 8k+10 - round 4
	aese	v4.16b, v27.16b
	aesmc	v4.16b, v4.16b			//AES block 8k+12 - round 4

	aese	v6.16b, v28.16b
	aesmc	v6.16b, v6.16b			//AES block 8k+14 - round 5
	pmull2	v18.1q, v8.2d, v24.2d				//GHASH block 8k	- mid
.inst	0xce1d2631	//eor3 v17.16b, v17.16b, v29.16b, v9.16b			//GHASH block 8k+2, 8k+3 - high

	aese	v7.16b, v27.16b
	aesmc	v7.16b, v7.16b			//AES block 8k+15 - round 4
	trn1	v29.2d, v11.2d, v10.2d				//GHASH block 8k+2, 8k+3 - mid
	trn2	v10.2d, v11.2d, v10.2d				//GHASH block 8k+2, 8k+3 - mid

	aese	v5.16b, v27.16b
	aesmc	v5.16b, v5.16b			//AES block 8k+13 - round 4
	eor	v19.16b, v19.16b, v23.16b				//GHASH block 8k+1 - low
	aese	v3.16b, v27.16b
	aesmc	v3.16b, v3.16b			//AES block 8k+11 - round 4

	pmull	v20.1q, v11.1d, v20.1d				//GHASH block 8k+3 - low
	pmull	v24.1q, v8.1d, v24.1d				//GHASH block 8k+1 - mid
	eor	v10.16b, v10.16b, v29.16b				//GHASH block 8k+2, 8k+3 - mid

	rev64	v12.16b, v12.16b						//GHASH block 8k+4
	aese	v1.16b, v28.16b
	aesmc	v1.16b, v1.16b			//AES block 8k+9 - round 5
	aese	v0.16b, v28.16b
	aesmc	v0.16b, v0.16b			//AES block 8k+8 - round 5

	aese	v7.16b, v28.16b
	aesmc	v7.16b, v7.16b			//AES block 8k+15 - round 5
	aese	v4.16b, v28.16b
	aesmc	v4.16b, v4.16b			//AES block 8k+12 - round 5
	ldp	q26, q27, [x11, #96]				//load rk6, rk7

	ldr	q23, [x6, #48]				//load h3l | h3h
	ldr	q25, [x6, #80]				//load h4l | h4h
	pmull2	v29.1q, v10.2d, v21.2d				//GHASH block 8k+2 - mid
	pmull	v21.1q, v10.1d, v21.1d				//GHASH block 8k+3 - mid

.inst	0xce165273	//eor3 v19.16b, v19.16b, v22.16b, v20.16b			//GHASH block 8k+2, 8k+3 - low
	eor	v18.16b, v18.16b, v24.16b				//GHASH block 8k+1 - mid

	aese	v5.16b, v28.16b
	aesmc	v5.16b, v5.16b			//AES block 8k+13 - round 5
	rev64	v15.16b, v15.16b						//GHASH block 8k+7
	trn1	v16.2d, v13.2d, v12.2d				//GHASH block 8k+4, 8k+5 - mid

	aese	v3.16b, v28.16b
	aesmc	v3.16b, v3.16b			//AES block 8k+11 - round 5
	aese	v2.16b, v28.16b
	aesmc	v2.16b, v2.16b			//AES block 8k+10 - round 5
.inst	0xce157652	//eor3 v18.16b, v18.16b, v21.16b, v29.16b			//GHASH block 8k+2, 8k+3 - mid

	aese	v7.16b, v26.16b
	aesmc	v7.16b, v7.16b			//AES block 8k+15 - round 6
	aese	v4.16b, v26.16b
	aesmc	v4.16b, v4.16b			//AES block 8k+12 - round 6
	aese	v6.16b, v26.16b
	aesmc	v6.16b, v6.16b			//AES block 8k+14 - round 6

	ldr	q21, [x6, #16]				//load h2k | h1k
	ldr	q24, [x6, #64]				//load h4k | h3k
	aese	v5.16b, v26.16b
	aesmc	v5.16b, v5.16b			//AES block 8k+13 - round 6
	aese	v3.16b, v26.16b
	aesmc	v3.16b, v3.16b			//AES block 8k+11 - round 6

	aese	v0.16b, v26.16b
	aesmc	v0.16b, v0.16b			//AES block 8k+8 - round 6
	aese	v1.16b, v26.16b
	aesmc	v1.16b, v1.16b			//AES block 8k+9 - round 6
	aese	v2.16b, v26.16b
	aesmc	v2.16b, v2.16b			//AES block 8k+10 - round 6

	pmull2	v8.1q, v12.2d, v25.2d				//GHASH block 8k+4 - high
	pmull	v25.1q, v12.1d, v25.1d				//GHASH block 8k+4 - low
	ldr	q20, [x6]				//load h1l | h1h
	ldr	q22, [x6, #32]				//load h2l | h2h

	ldp	q28, q26, [x11, #128]				//load rk8, rk9
	aese	v1.16b, v27.16b
	aesmc	v1.16b, v1.16b			//AES block 8k+9 - round 7
	aese	v4.16b, v27.16b
	aesmc	v4.16b, v4.16b			//AES block 8k+12 - round 7

	pmull2	v10.1q, v13.2d, v23.2d				//GHASH block 8k+5 - high
	trn2	v12.2d, v13.2d, v12.2d				//GHASH block 8k+4, 8k+5 - mid

	aese	v5.16b, v27.16b
	aesmc	v5.16b, v5.16b			//AES block 8k+13 - round 7
	aese	v6.16b, v27.16b
	aesmc	v6.16b, v6.16b			//AES block 8k+14 - round 7
	pmull	v23.1q, v13.1d, v23.1d				//GHASH block 8k+5 - low

	aese	v7.16b, v27.16b
	aesmc	v7.16b, v7.16b			//AES block 8k+15 - round 7
	aese	v3.16b, v27.16b
	aesmc	v3.16b, v3.16b			//AES block 8k+11 - round 7
	eor	v12.16b, v12.16b, v16.16b				//GHASH block 8k+4, 8k+5 - mid

	pmull2	v11.1q, v14.2d, v22.2d				//GHASH block 8k+6 - high
	pmull	v22.1q, v14.1d, v22.1d				//GHASH block 8k+6 - low
	aese	v2.16b, v27.16b
	aesmc	v2.16b, v2.16b			//AES block 8k+10 - round 7

	trn1	v13.2d, v15.2d, v14.2d				//GHASH block 8k+6, 8k+7 - mid
	trn2	v14.2d, v15.2d, v14.2d				//GHASH block 8k+6, 8k+7 - mid
	aese	v0.16b, v27.16b
	aesmc	v0.16b, v0.16b			//AES block 8k+8 - round 7

	aese	v7.16b, v28.16b
	aesmc	v7.16b, v7.16b			//AES block 8k+15 - round 8
.inst	0xce195e73	//eor3 v19.16b, v19.16b, v25.16b, v23.16b			//GHASH block 8k+4, 8k+5 - low
	aese	v2.16b, v28.16b
	aesmc	v2.16b, v2.16b			//AES block 8k+10 - round 8

	aese	v6.16b, v28.16b
	aesmc	v6.16b, v6.16b			//AES block 8k+14 - round 8
	aese	v4.16b, v28.16b
	aesmc	v4.16b, v4.16b			//AES block 8k+12 - round 8
	aese	v3.16b, v28.16b
	aesmc	v3.16b, v3.16b			//AES block 8k+11 - round 8

	aese	v5.16b, v28.16b
	aesmc	v5.16b, v5.16b			//AES block 8k+13 - round 8
	eor	v14.16b, v14.16b, v13.16b				//GHASH block 8k+6, 8k+7 - mid
	aese	v0.16b, v28.16b
	aesmc	v0.16b, v0.16b			//AES block 8k+8 - round 8

	pmull2	v16.1q, v12.2d, v24.2d				//GHASH block 8k+4 - mid
	pmull	v24.1q, v12.1d, v24.1d				//GHASH block 8k+5 - mid
	aese	v1.16b, v28.16b
	aesmc	v1.16b, v1.16b			//AES block 8k+9 - round 8

	pmull2	v12.1q, v15.2d, v20.2d				//GHASH block 8k+7 - high
	pmull2	v13.1q, v14.2d, v21.2d				//GHASH block 8k+6 - mid
	pmull	v21.1q, v14.1d, v21.1d				//GHASH block 8k+7 - mid

	pmull	v20.1q, v15.1d, v20.1d				//GHASH block 8k+7 - low
.inst	0xce184252	//eor3 v18.16b, v18.16b, v24.16b, v16.16b			//GHASH block 8k+4, 8k+5 - mid
.inst	0xce082a31	//eor3 v17.16b, v17.16b, v8.16b, v10.16b			//GHASH block 8k+4, 8k+5 - high

	ldp	q27, q28, [x11, #160]				//load rk10, rk11
	aese	v1.16b, v26.16b
	aesmc	v1.16b, v1.16b			//AES block 8k+9 - round 9
	aese	v0.16b, v26.16b
	aesmc	v0.16b, v0.16b			//AES block 8k+8 - round 9

.inst	0xce0b3231	//eor3 v17.16b, v17.16b, v11.16b, v12.16b			//GHASH block 8k+6, 8k+7 - high
.inst	0xce153652	//eor3 v18.16b, v18.16b, v21.16b, v13.16b			//GHASH block 8k+6, 8k+7 - mid
	ldr	d16, [x10]			//MODULO - load modulo constant

.inst	0xce165273	//eor3 v19.16b, v19.16b, v22.16b, v20.16b			//GHASH block 8k+6, 8k+7 - low

	aese	v3.16b, v26.16b
	aesmc	v3.16b, v3.16b			//AES block 8k+11 - round 9
	aese	v7.16b, v26.16b
	aesmc	v7.16b, v7.16b			//AES block 8k+15 - round 9
	aese	v5.16b, v26.16b
	aesmc	v5.16b, v5.16b			//AES block 8k+13 - round 9

	aese	v2.16b, v26.16b
	aesmc	v2.16b, v2.16b			//AES block 8k+10 - round 9
	aese	v6.16b, v26.16b
	aesmc	v6.16b, v6.16b			//AES block 8k+14 - round 9

	aese	v5.16b, v27.16b
	aesmc	v5.16b, v5.16b			//AES block 8k+13 - round 10
	aese	v1.16b, v27.16b
	aesmc	v1.16b, v1.16b			//AES block 8k+9 - round 10
	aese	v4.16b, v26.16b
	aesmc	v4.16b, v4.16b			//AES block 8k+12 - round 9

	aese	v7.16b, v27.16b
	aesmc	v7.16b, v7.16b			//AES block 8k+15 - round 10
	aese	v6.16b, v27.16b
	aesmc	v6.16b, v6.16b			//AES block 8k+14 - round 10
	aese	v3.16b, v27.16b
	aesmc	v3.16b, v3.16b			//AES block 8k+11 - round 10

	aese	v4.16b, v27.16b
	aesmc	v4.16b, v4.16b			//AES block 8k+12 - round 10
	aese	v0.16b, v27.16b
	aesmc	v0.16b, v0.16b			//AES block 8k+8 - round 10
	aese	v2.16b, v27.16b
	aesmc	v2.16b, v2.16b			//AES block 8k+10 - round 10

	pmull	v29.1q, v17.1d, v16.1d		 	//MODULO - top 64b align with mid
.inst	0xce114e52	//eor3 v18.16b, v18.16b, v17.16b, v19.16b		 	//MODULO - karatsuba tidy up
	aese	v7.16b, v28.16b
	aesmc	v7.16b, v7.16b			//AES block 8k+15 - round 11

	ldp	q26, q27, [x11, #192]				//load rk12, rk13
	ext	v21.16b, v17.16b, v17.16b, #8			 	//MODULO - other top alignment
	aese	v2.16b, v28.16b
	aesmc	v2.16b, v2.16b			//AES block 8k+10 - round 11

.inst	0xce1d5652	//eor3 v18.16b, v18.16b, v29.16b, v21.16b			//MODULO - fold into mid
	aese	v1.16b, v28.16b
	aesmc	v1.16b, v1.16b			//AES block 8k+9 - round 11
	aese	v6.16b, v28.16b
	aesmc	v6.16b, v6.16b			//AES block 8k+14 - round 11

	aese	v0.16b, v28.16b
	aesmc	v0.16b, v0.16b			//AES block 8k+8 - round 11
	aese	v4.16b, v28.16b
	aesmc	v4.16b, v4.16b			//AES block 8k+12 - round 11
	aese	v5.16b, v28.16b
	aesmc	v5.16b, v5.16b			//AES block 8k+13 - round 11

	pmull	v17.1q, v18.1d, v16.1d			//MODULO - mid 64b align with low
	aese	v3.16b, v28.16b
	aesmc	v3.16b, v3.16b			//AES block 8k+11 - round 11
	ldr	q28, [x11, #224]					//load rk14

	aese	v1.16b, v26.16b
	aesmc	v1.16b, v1.16b			//AES block 8k+9 - round 12
	aese	v2.16b, v26.16b
	aesmc	v2.16b, v2.16b			//AES block 8k+10 - round 12
	aese	v0.16b, v26.16b
	aesmc	v0.16b, v0.16b			//AES block 8k+8 - round 12

	aese	v6.16b, v26.16b
	aesmc	v6.16b, v6.16b			//AES block 8k+14 - round 12
	aese	v5.16b, v26.16b
	aesmc	v5.16b, v5.16b			//AES block 8k+13 - round 12
	ext	v21.16b, v18.16b, v18.16b, #8			 	//MODULO - other mid alignment

	aese	v4.16b, v26.16b
	aesmc	v4.16b, v4.16b			//AES block 8k+12 - round 12
	add	v30.4s, v30.4s, v31.4s		//CTR block 8k+15

	aese	v3.16b, v26.16b
	aesmc	v3.16b, v3.16b			//AES block 8k+11 - round 12
	aese	v7.16b, v26.16b
	aesmc	v7.16b, v7.16b			//AES block 8k+15 - round 12
	aese	v0.16b, v27.16b						//AES block 8k+8 - round 13

.inst	0xce154673	//eor3 v19.16b, v19.16b, v21.16b, v17.16b		 	//MODULO - fold into low
	aese	v5.16b, v27.16b						//AES block 8k+13 - round 13
	aese	v1.16b, v27.16b						//AES block 8k+9 - round 13

	aese	v3.16b, v27.16b						//AES block 8k+11 - round 13
	aese	v4.16b, v27.16b						//AES block 8k+12 - round 13
	aese	v7.16b, v27.16b						//AES block 8k+15 - round 13

	aese	v2.16b, v27.16b						//AES block 8k+10 - round 13
	aese	v6.16b, v27.16b						//AES block 8k+14 - round 13
.L256_enc_tail:	//TAIL

	ldp	q24, q25, [x6, #160]			//load h8l | h8h
	sub	x5, x4, x0		//main_end_input_ptr is number of bytes left to process

	ldr	q8, [x0], #16				//AES block 8k+8 - load plaintext

	ldp	q20, q21, [x6, #96]			//load h5l | h5h

	ext	v16.16b, v19.16b, v19.16b, #8				//prepare final partial tag
	ldp	q22, q23, [x6, #128]			//load h6l | h6h
	mov	v29.16b, v28.16b

	cmp	x5, #112
.inst	0xce007509	//eor3 v9.16b, v8.16b, v0.16b, v29.16b				//AES block 8k+8 - result
	b.gt	.L256_enc_blocks_more_than_7

	movi	v19.8b, #0
	mov	v7.16b, v6.16b
	movi	v17.8b, #0

	mov	v6.16b, v5.16b
	mov	v5.16b, v4.16b
	mov	v4.16b, v3.16b

	mov	v3.16b, v2.16b
	sub	v30.4s, v30.4s, v31.4s
	mov	v2.16b, v1.16b

	movi	v18.8b, #0
	cmp	x5, #96
	b.gt	.L256_enc_blocks_more_than_6

	mov	v7.16b, v6.16b
	mov	v6.16b, v5.16b
	cmp	x5, #80

	mov	v5.16b, v4.16b
	mov	v4.16b, v3.16b
	mov	v3.16b, v1.16b

	sub	v30.4s, v30.4s, v31.4s
	b.gt	.L256_enc_blocks_more_than_5

	mov	v7.16b, v6.16b
	sub	v30.4s, v30.4s, v31.4s

	mov	v6.16b, v5.16b
	mov	v5.16b, v4.16b

	cmp	x5, #64
	mov	v4.16b, v1.16b
	b.gt	.L256_enc_blocks_more_than_4

	cmp	x5, #48
	mov	v7.16b, v6.16b
	mov	v6.16b, v5.16b

	mov	v5.16b, v1.16b
	sub	v30.4s, v30.4s, v31.4s
	b.gt	.L256_enc_blocks_more_than_3

	cmp	x5, #32
	mov	v7.16b, v6.16b
	ldr	q24, [x6, #64]				//load h4k | h3k

	mov	v6.16b, v1.16b
	sub	v30.4s, v30.4s, v31.4s
	b.gt	.L256_enc_blocks_more_than_2

	mov	v7.16b, v1.16b

	sub	v30.4s, v30.4s, v31.4s
	cmp	x5, #16
	b.gt	.L256_enc_blocks_more_than_1

	sub	v30.4s, v30.4s, v31.4s
	ldr	q21, [x6, #16]				//load h2k | h1k
	b	.L256_enc_blocks_less_than_1
.L256_enc_blocks_more_than_7:	//blocks	left >  7
	st1	{ v9.16b}, [x2], #16				//AES final-7 block  - store result

	rev64	v8.16b, v9.16b						//GHASH final-7 block

	eor	v8.16b, v8.16b, v16.16b					//feed in partial tag

	ldr	q9, [x0], #16				//AES final-6 block - load plaintext

	pmull2	v17.1q, v8.2d, v25.2d				//GHASH final-7 block - high
	ins	v27.d[0], v8.d[1]					//GHASH final-7 block - mid
	ins	v18.d[0], v24.d[1]					//GHASH final-7 block - mid

	movi	v16.8b, #0						//supress further partial tag feed in

	eor	v27.8b, v27.8b, v8.8b				//GHASH final-7 block - mid
.inst	0xce017529	//eor3 v9.16b, v9.16b, v1.16b, v29.16b			//AES final-6 block - result

	pmull	v18.1q, v27.1d, v18.1d				//GHASH final-7 block - mid
	pmull	v19.1q, v8.1d, v25.1d				//GHASH final-7 block - low
.L256_enc_blocks_more_than_6:	//blocks	left >  6

	st1	{ v9.16b}, [x2], #16				//AES final-6 block - store result

	rev64	v8.16b, v9.16b						//GHASH final-6 block

	eor	v8.16b, v8.16b, v16.16b					//feed in partial tag

	pmull	v26.1q, v8.1d, v23.1d				//GHASH final-6 block - low
	ins	v27.d[0], v8.d[1]					//GHASH final-6 block - mid
	pmull2	v28.1q, v8.2d, v23.2d				//GHASH final-6 block - high

	ldr	q9, [x0], #16				//AES final-5 block - load plaintext

	eor	v19.16b, v19.16b, v26.16b					//GHASH final-6 block - low

	eor	v27.8b, v27.8b, v8.8b				//GHASH final-6 block - mid

	pmull	v27.1q, v27.1d, v24.1d				//GHASH final-6 block - mid
.inst	0xce027529	//eor3 v9.16b, v9.16b, v2.16b, v29.16b			//AES final-5 block - result

	movi	v16.8b, #0						//supress further partial tag feed in

	eor	v18.16b, v18.16b, v27.16b				//GHASH final-6 block - mid
	eor	v17.16b, v17.16b, v28.16b					//GHASH final-6 block - high
.L256_enc_blocks_more_than_5:	//blocks	left >  5

	st1	{ v9.16b}, [x2], #16				//AES final-5 block - store result

	rev64	v8.16b, v9.16b						//GHASH final-5 block

	eor	v8.16b, v8.16b, v16.16b					//feed in partial tag

	ins	v27.d[0], v8.d[1]					//GHASH final-5 block - mid

	pmull2	v28.1q, v8.2d, v22.2d				//GHASH final-5 block - high

	eor	v17.16b, v17.16b, v28.16b					//GHASH final-5 block - high
	eor	v27.8b, v27.8b, v8.8b				//GHASH final-5 block - mid

	ins	v27.d[1], v27.d[0]					//GHASH final-5 block - mid

	ldr	q9, [x0], #16				//AES final-4 block - load plaintext
	pmull	v26.1q, v8.1d, v22.1d				//GHASH final-5 block - low

	pmull2	v27.1q, v27.2d, v21.2d				//GHASH final-5 block - mid
	movi	v16.8b, #0						//supress further partial tag feed in
	eor	v19.16b, v19.16b, v26.16b					//GHASH final-5 block - low

	eor	v18.16b, v18.16b, v27.16b				//GHASH final-5 block - mid
.inst	0xce037529	//eor3 v9.16b, v9.16b, v3.16b, v29.16b			//AES final-4 block - result
.L256_enc_blocks_more_than_4:	//blocks	left >  4

	st1	{ v9.16b}, [x2], #16				//AES final-4 block - store result

	rev64	v8.16b, v9.16b						//GHASH final-4 block

	ldr	q9, [x0], #16				//AES final-3 block - load plaintext

	eor	v8.16b, v8.16b, v16.16b					//feed in partial tag

	ins	v27.d[0], v8.d[1]					//GHASH final-4 block - mid
	pmull2	v28.1q, v8.2d, v20.2d				//GHASH final-4 block - high

.inst	0xce047529	//eor3 v9.16b, v9.16b, v4.16b, v29.16b			//AES final-3 block - result
	pmull	v26.1q, v8.1d, v20.1d				//GHASH final-4 block - low

	eor	v27.8b, v27.8b, v8.8b				//GHASH final-4 block - mid
	eor	v19.16b, v19.16b, v26.16b					//GHASH final-4 block - low

	pmull	v27.1q, v27.1d, v21.1d				//GHASH final-4 block - mid

	movi	v16.8b, #0						//supress further partial tag feed in

	eor	v18.16b, v18.16b, v27.16b				//GHASH final-4 block - mid
	eor	v17.16b, v17.16b, v28.16b					//GHASH final-4 block - high
.L256_enc_blocks_more_than_3:	//blocks	left >  3

	st1	{ v9.16b}, [x2], #16				//AES final-3 block - store result

	ldr	q25, [x6, #80]				//load h4l | h4h
	rev64	v8.16b, v9.16b						//GHASH final-3 block

	eor	v8.16b, v8.16b, v16.16b					//feed in partial tag

	ins	v27.d[0], v8.d[1]					//GHASH final-3 block - mid
	pmull2	v28.1q, v8.2d, v25.2d				//GHASH final-3 block - high

	eor	v17.16b, v17.16b, v28.16b					//GHASH final-3 block - high
	eor	v27.8b, v27.8b, v8.8b				//GHASH final-3 block - mid
	ldr	q24, [x6, #64]				//load h4k | h3k

	ins	v27.d[1], v27.d[0]					//GHASH final-3 block - mid
	ldr	q9, [x0], #16				//AES final-2 block - load plaintext

	pmull2	v27.1q, v27.2d, v24.2d				//GHASH final-3 block - mid
	pmull	v26.1q, v8.1d, v25.1d				//GHASH final-3 block - low

.inst	0xce057529	//eor3 v9.16b, v9.16b, v5.16b, v29.16b			//AES final-2 block - result
	movi	v16.8b, #0						//supress further partial tag feed in

	eor	v18.16b, v18.16b, v27.16b				//GHASH final-3 block - mid
	eor	v19.16b, v19.16b, v26.16b					//GHASH final-3 block - low
.L256_enc_blocks_more_than_2:	//blocks	left >  2

	ldr	q23, [x6, #48]				//load h3l | h3h

	st1	{ v9.16b}, [x2], #16			 	//AES final-2 block - store result

	rev64	v8.16b, v9.16b						//GHASH final-2 block
	ldr	q9, [x0], #16				//AES final-1 block - load plaintext

	eor	v8.16b, v8.16b, v16.16b					//feed in partial tag

	ins	v27.d[0], v8.d[1]					//GHASH final-2 block - mid

	movi	v16.8b, #0						//supress further partial tag feed in

	pmull2	v28.1q, v8.2d, v23.2d				//GHASH final-2 block - high
.inst	0xce067529	//eor3 v9.16b, v9.16b, v6.16b, v29.16b			//AES final-1 block - result

	eor	v27.8b, v27.8b, v8.8b				//GHASH final-2 block - mid

	eor	v17.16b, v17.16b, v28.16b					//GHASH final-2 block - high

	pmull	v27.1q, v27.1d, v24.1d				//GHASH final-2 block - mid
	pmull	v26.1q, v8.1d, v23.1d				//GHASH final-2 block - low

	eor	v18.16b, v18.16b, v27.16b				//GHASH final-2 block - mid
	eor	v19.16b, v19.16b, v26.16b					//GHASH final-2 block - low
.L256_enc_blocks_more_than_1:	//blocks	left >  1

	st1	{ v9.16b}, [x2], #16				//AES final-1 block - store result

	ldr	q22, [x6, #32]				//load h2l | h2h
	rev64	v8.16b, v9.16b						//GHASH final-1 block
	ldr	q9, [x0], #16				//AES final block - load plaintext

	eor	v8.16b, v8.16b, v16.16b					//feed in partial tag
	movi	v16.8b, #0						//supress further partial tag feed in

	ins	v27.d[0], v8.d[1]					//GHASH final-1 block - mid
	pmull2	v28.1q, v8.2d, v22.2d				//GHASH final-1 block - high

.inst	0xce077529	//eor3 v9.16b, v9.16b, v7.16b, v29.16b			//AES final block - result
	eor	v17.16b, v17.16b, v28.16b					//GHASH final-1 block - high

	pmull	v26.1q, v8.1d, v22.1d				//GHASH final-1 block - low
	eor	v27.8b, v27.8b, v8.8b				//GHASH final-1 block - mid

	ldr	q21, [x6, #16]				//load h2k | h1k

	eor	v19.16b, v19.16b, v26.16b					//GHASH final-1 block - low
	ins	v27.d[1], v27.d[0]					//GHASH final-1 block - mid

	pmull2	v27.1q, v27.2d, v21.2d				//GHASH final-1 block - mid

	eor	v18.16b, v18.16b, v27.16b				//GHASH final-1 block - mid
.L256_enc_blocks_less_than_1:	//blocks	left <= 1

	and	x1, x1, #127				//bit_length %= 128

	sub	x1, x1, #128				//bit_length -= 128

	neg	x1, x1				//bit_length = 128 - #bits in input (in range [1,128])

	mvn	x7, xzr						//temp0_x = 0xffffffffffffffff
	and	x1, x1, #127				//bit_length %= 128

	lsr	x7, x7, x1				//temp0_x is mask for top 64b of last block
	cmp	x1, #64
	mvn	x8, xzr						//temp1_x = 0xffffffffffffffff

	csel	x14, x7, xzr, lt
	csel	x13, x8, x7, lt

	mov	v0.d[0], x13					//ctr0b is mask for last block
	ldr	q20, [x6]				//load h1l | h1h

	ld1	{ v26.16b}, [x2]					//load existing bytes where the possibly partial last block is to be stored
	mov	v0.d[1], x14

	and	v9.16b, v9.16b, v0.16b					//possibly partial last block has zeroes in highest bits

	rev64	v8.16b, v9.16b						//GHASH final block

	rev32	v30.16b, v30.16b
	bif	v9.16b, v26.16b, v0.16b					//insert existing bytes in top end of result before storing
	str	q30, [x16]					//store the updated counter

	eor	v8.16b, v8.16b, v16.16b					//feed in partial tag
	st1	{ v9.16b}, [x2]				//store all 16B

	ins	v16.d[0], v8.d[1]					//GHASH final block - mid
	pmull2	v28.1q, v8.2d, v20.2d				//GHASH final block - high
	pmull	v26.1q, v8.1d, v20.1d				//GHASH final block - low

	eor	v17.16b, v17.16b, v28.16b					//GHASH final block - high
	eor	v19.16b, v19.16b, v26.16b					//GHASH final block - low

	eor	v16.8b, v16.8b, v8.8b				//GHASH final block - mid

	pmull	v16.1q, v16.1d, v21.1d				//GHASH final block - mid

	eor	v18.16b, v18.16b, v16.16b				//GHASH final block - mid
	ldr	d16, [x10]			//MODULO - load modulo constant

	ext	v21.16b, v17.16b, v17.16b, #8				//MODULO - other top alignment

.inst	0xce114e52	//eor3 v18.16b, v18.16b, v17.16b, v19.16b		 	//MODULO - karatsuba tidy up
	pmull	v29.1q, v17.1d, v16.1d			//MODULO - top 64b align with mid

.inst	0xce1d5652	//eor3 v18.16b, v18.16b, v29.16b, v21.16b			//MODULO - fold into mid

	pmull	v17.1q, v18.1d, v16.1d			//MODULO - mid 64b align with low
	ext	v21.16b, v18.16b, v18.16b, #8				//MODULO - other mid alignment

.inst	0xce115673	//eor3 v19.16b, v19.16b, v17.16b, v21.16b		 	//MODULO - fold into low
	ext	v19.16b, v19.16b, v19.16b, #8
	rev64	v19.16b, v19.16b
	st1	{ v19.16b }, [x3]
	mov	x0, x9					//return sizes

	ldp	d10, d11, [sp, #16]
	ldp	d12, d13, [sp, #32]
	ldp	d14, d15, [sp, #48]
	ldp	d8, d9, [sp], #80
	ret

.L256_enc_ret:
	mov	w0, #0x0
	ret
        .cfi_endproc
S2N_BN_SIZE_DIRECTIVE(aes256_gcm)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
