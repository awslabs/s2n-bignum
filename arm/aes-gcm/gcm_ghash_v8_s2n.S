// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// GCM_GHASH_V8_S2N (GHASH over whole 16-byte blocks, AArch64 NEON/PMULL)
// Inputs xi[16], htable[32], inp[len], len; output xi[16]
//
//    extern void gcm_ghash_v8_s2n(uint8_t xi[static 16], const uint64_t htable[static 32],
//                             const uint8_t *inp, size_t len);
//
// The accumulator xi is both an input and the output.
// Standard ARM ABI: X0 = xi, X1 = htable, X2 = inp, X3 = len
// ----------------------------------------------------------------------------

// Imported from aws-lc generated-src/linux-aarch64/crypto/fipsmodule/ghashv8-armx.S
// (generator crypto/fipsmodule/modes/asm/ghashv8-armx.pl) at commit 83e7c97c6.
// The imported region is the concatenation of aws-lc's gcm_ghash_v8_s2n and its
// fallthrough target gcm_ghash_v8_4x: the entry's "cmp x3,#64 / b.hs
// .Lgcm_ghash_v8_4x" makes the two a single control flow graph, so they are one
// s2n-bignum function here.
//
// "len" (X3) is in BYTES and must be a positive multiple of 16, which every
// aws-lc call site satisfies (gcm.c masks with kSizeTWithoutLower4Bits).  Two
// paths are selected by length: len < 64 uses the 2x-modulo-scheduled loop and
// reads Htable[0..2] (48 bytes); len >= 64 branches to .Lgcm_ghash_v8_4x, which
// reads Htable[0..5] (96 bytes).  Only the 16 bytes at Xi are written.  All
// input reads stay within inp[0..len); on the len < 64 path the post-increment
// register x12 is zeroed just in time so that the last block(s) are re-read
// rather than stepping past inp[len].
//
// Leaf function: no stack frame and no callee-saved register is touched, so the
// CFI annotation is just the CFI_START / CFI_RET bracket (the CFA never moves,
// and the early "ret" on the len < 64 path needs no annotation of its own).
//
// DIVERGENCE FROM the aws-lc source (all non-semantic):
//  1. AARCH64_VALID_CALL_TARGET (an aws-lc BTI macro, empty in this build) is
//     dropped, so the first instruction of the object is "cmp x3,#64".
//  2. The "#ifndef __AARCH64EB__" guards are dropped and their little-endian
//     rev64 bodies kept unconditionally, matching the LE-only convention of the
//     other arm/aes-gcm sources.
//  3. The separate ".globl / .type / .size gcm_ghash_v8_s2n" and
//     ".type gcm_ghash_v8_4x" directives collapse into the single s2n-bignum
//     symbol macro block below; ".Lgcm_ghash_v8_4x" is kept as a local label.
// The instruction sequence is otherwise byte-for-byte the aws-lc sequence.
#include "_internal_s2n_bignum_arm.h"

        .arch	armv8-a+crypto
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(gcm_ghash_v8_s2n)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(gcm_ghash_v8_s2n)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(gcm_ghash_v8_s2n)
        .text
        .balign 16

S2N_BN_SYMBOL(gcm_ghash_v8_s2n):
	CFI_START
	cmp	x3,#64
	b.hs	.Lgcm_ghash_v8_4x
	ld1	{v0.2d},[x0]		//load [rotated] Xi
						//"[rotated]" means that
						//loaded value would have
						//to be rotated in order to
						//make it appear as in
						//algorithm specification
	subs	x3,x3,#32		//see if x3 is 32 or larger
	mov	x12,#16		//x12 is used as post-
						//increment for input pointer;
						//as loop is modulo-scheduled
						//x12 is zeroed just in time
						//to preclude overstepping
						//inp[len], which means that
						//last block[s] are actually
						//loaded twice, but last
						//copy is not processed
	ld1	{v20.2d,v21.2d},[x1],#32	//load twisted H, ..., H^2
	ext	v20.16b,v20.16b,v20.16b,#8
	movi	v19.16b,#0xe1
	ld1	{v22.2d},[x1]
	ext	v22.16b,v22.16b,v22.16b,#8
	csel	x12,xzr,x12,eq			//is it time to zero x12?
	ext	v0.16b,v0.16b,v0.16b,#8		//rotate Xi
	ld1	{v16.2d},[x2],#16	//load [rotated] I[0]
	shl	v19.2d,v19.2d,#57		//compose 0xc2.0 constant
	rev64	v16.16b,v16.16b
	rev64	v0.16b,v0.16b
	ext	v3.16b,v16.16b,v16.16b,#8		//rotate I[0]
	b.lo	.Lodd_tail_v8		//x3 was less than 32
	ld1	{v17.2d},[x2],x12	//load [rotated] I[1]
	rev64	v17.16b,v17.16b
	ext	v7.16b,v17.16b,v17.16b,#8
	eor	v3.16b,v3.16b,v0.16b		//I[i]^=Xi
	pmull	v4.1q,v20.1d,v7.1d		//H·Ii+1
	eor	v17.16b,v17.16b,v7.16b		//Karatsuba pre-processing
	pmull2	v6.1q,v20.2d,v7.2d
	b	.Loop_mod2x_v8

.align	4
.Loop_mod2x_v8:
	ext	v18.16b,v3.16b,v3.16b,#8
	subs	x3,x3,#32		//is there more data?
	pmull	v0.1q,v22.1d,v3.1d		//H^2.lo·Xi.lo
	csel	x12,xzr,x12,lo			//is it time to zero x12?

	pmull	v5.1q,v21.1d,v17.1d
	eor	v18.16b,v18.16b,v3.16b		//Karatsuba pre-processing
	pmull2	v2.1q,v22.2d,v3.2d		//H^2.hi·Xi.hi
	eor	v0.16b,v0.16b,v4.16b		//accumulate
	pmull2	v1.1q,v21.2d,v18.2d		//(H^2.lo+H^2.hi)·(Xi.lo+Xi.hi)
	ld1	{v16.2d},[x2],x12	//load [rotated] I[i+2]

	eor	v2.16b,v2.16b,v6.16b
	csel	x12,xzr,x12,eq			//is it time to zero x12?
	eor	v1.16b,v1.16b,v5.16b

	ext	v17.16b,v0.16b,v2.16b,#8		//Karatsuba post-processing
	eor	v18.16b,v0.16b,v2.16b
	eor	v1.16b,v1.16b,v17.16b
	ld1	{v17.2d},[x2],x12	//load [rotated] I[i+3]
	rev64	v16.16b,v16.16b
	eor	v1.16b,v1.16b,v18.16b
	pmull	v18.1q,v0.1d,v19.1d		//1st phase of reduction

	rev64	v17.16b,v17.16b
	ins	v2.d[0],v1.d[1]
	ins	v1.d[1],v0.d[0]
	ext	v7.16b,v17.16b,v17.16b,#8
	ext	v3.16b,v16.16b,v16.16b,#8
	eor	v0.16b,v1.16b,v18.16b
	pmull	v4.1q,v20.1d,v7.1d		//H·Ii+1
	eor	v3.16b,v3.16b,v2.16b		//accumulate v3.16b early

	ext	v18.16b,v0.16b,v0.16b,#8		//2nd phase of reduction
	pmull	v0.1q,v0.1d,v19.1d
	eor	v3.16b,v3.16b,v18.16b
	eor	v17.16b,v17.16b,v7.16b		//Karatsuba pre-processing
	eor	v3.16b,v3.16b,v0.16b
	pmull2	v6.1q,v20.2d,v7.2d
	b.hs	.Loop_mod2x_v8		//there was at least 32 more bytes

	eor	v2.16b,v2.16b,v18.16b
	ext	v3.16b,v16.16b,v16.16b,#8		//re-construct v3.16b
	adds	x3,x3,#32		//re-construct x3
	eor	v0.16b,v0.16b,v2.16b		//re-construct v0.16b
	b.eq	.Ldone_v8		//is x3 zero?
.Lodd_tail_v8:
	ext	v18.16b,v0.16b,v0.16b,#8
	eor	v3.16b,v3.16b,v0.16b		//inp^=Xi
	eor	v17.16b,v16.16b,v18.16b		//v17.16b is rotated inp^Xi

	pmull	v0.1q,v20.1d,v3.1d		//H.lo·Xi.lo
	eor	v17.16b,v17.16b,v3.16b		//Karatsuba pre-processing
	pmull2	v2.1q,v20.2d,v3.2d		//H.hi·Xi.hi
	pmull	v1.1q,v21.1d,v17.1d		//(H.lo+H.hi)·(Xi.lo+Xi.hi)

	ext	v17.16b,v0.16b,v2.16b,#8		//Karatsuba post-processing
	eor	v18.16b,v0.16b,v2.16b
	eor	v1.16b,v1.16b,v17.16b
	eor	v1.16b,v1.16b,v18.16b
	pmull	v18.1q,v0.1d,v19.1d		//1st phase of reduction

	ins	v2.d[0],v1.d[1]
	ins	v1.d[1],v0.d[0]
	eor	v0.16b,v1.16b,v18.16b

	ext	v18.16b,v0.16b,v0.16b,#8		//2nd phase of reduction
	pmull	v0.1q,v0.1d,v19.1d
	eor	v18.16b,v18.16b,v2.16b
	eor	v0.16b,v0.16b,v18.16b

.Ldone_v8:
	rev64	v0.16b,v0.16b
	ext	v0.16b,v0.16b,v0.16b,#8
	st1	{v0.2d},[x0]		//write out Xi

	ret
.align	4
.Lgcm_ghash_v8_4x:
	ld1	{v0.2d},[x0]		//load [rotated] Xi
	ld1	{v20.2d,v21.2d,v22.2d},[x1],#48	//load twisted H, ..., H^2
	ext	v20.16b,v20.16b,v20.16b,#8
	ext	v22.16b,v22.16b,v22.16b,#8
	movi	v19.16b,#0xe1
	ld1	{v26.2d,v27.2d,v28.2d},[x1]	//load twisted H^3, ..., H^4
	ext	v26.16b,v26.16b,v26.16b,#8
	ext	v28.16b,v28.16b,v28.16b,#8
	shl	v19.2d,v19.2d,#57		//compose 0xc2.0 constant

	ld1	{v4.2d,v5.2d,v6.2d,v7.2d},[x2],#64
	rev64	v0.16b,v0.16b
	rev64	v5.16b,v5.16b
	rev64	v6.16b,v6.16b
	rev64	v7.16b,v7.16b
	rev64	v4.16b,v4.16b
	ext	v25.16b,v7.16b,v7.16b,#8
	ext	v24.16b,v6.16b,v6.16b,#8
	ext	v23.16b,v5.16b,v5.16b,#8

	pmull	v29.1q,v20.1d,v25.1d		//H·Ii+3
	eor	v7.16b,v7.16b,v25.16b
	pmull2	v31.1q,v20.2d,v25.2d
	pmull	v30.1q,v21.1d,v7.1d

	pmull	v16.1q,v22.1d,v24.1d		//H^2·Ii+2
	eor	v6.16b,v6.16b,v24.16b
	pmull2	v24.1q,v22.2d,v24.2d
	pmull2	v6.1q,v21.2d,v6.2d

	eor	v29.16b,v29.16b,v16.16b
	eor	v31.16b,v31.16b,v24.16b
	eor	v30.16b,v30.16b,v6.16b

	pmull	v7.1q,v26.1d,v23.1d		//H^3·Ii+1
	eor	v5.16b,v5.16b,v23.16b
	pmull2	v23.1q,v26.2d,v23.2d
	pmull	v5.1q,v27.1d,v5.1d

	eor	v29.16b,v29.16b,v7.16b
	eor	v31.16b,v31.16b,v23.16b
	eor	v30.16b,v30.16b,v5.16b

	subs	x3,x3,#128
	b.lo	.Ltail4x

	b	.Loop4x

.align	4
.Loop4x:
	eor	v16.16b,v4.16b,v0.16b
	ld1	{v4.2d,v5.2d,v6.2d,v7.2d},[x2],#64
	ext	v3.16b,v16.16b,v16.16b,#8
	rev64	v5.16b,v5.16b
	rev64	v6.16b,v6.16b
	rev64	v7.16b,v7.16b
	rev64	v4.16b,v4.16b

	pmull	v0.1q,v28.1d,v3.1d		//H^4·(Xi+Ii)
	eor	v16.16b,v16.16b,v3.16b
	pmull2	v2.1q,v28.2d,v3.2d
	ext	v25.16b,v7.16b,v7.16b,#8
	pmull2	v1.1q,v27.2d,v16.2d

	eor	v0.16b,v0.16b,v29.16b
	eor	v2.16b,v2.16b,v31.16b
	ext	v24.16b,v6.16b,v6.16b,#8
	eor	v1.16b,v1.16b,v30.16b
	ext	v23.16b,v5.16b,v5.16b,#8

	ext	v17.16b,v0.16b,v2.16b,#8		//Karatsuba post-processing
	eor	v18.16b,v0.16b,v2.16b
	pmull	v29.1q,v20.1d,v25.1d		//H·Ii+3
	eor	v7.16b,v7.16b,v25.16b
	eor	v1.16b,v1.16b,v17.16b
	pmull2	v31.1q,v20.2d,v25.2d
	eor	v1.16b,v1.16b,v18.16b
	pmull	v30.1q,v21.1d,v7.1d

	pmull	v18.1q,v0.1d,v19.1d		//1st phase of reduction
	ins	v2.d[0],v1.d[1]
	ins	v1.d[1],v0.d[0]
	pmull	v16.1q,v22.1d,v24.1d		//H^2·Ii+2
	eor	v6.16b,v6.16b,v24.16b
	pmull2	v24.1q,v22.2d,v24.2d
	eor	v0.16b,v1.16b,v18.16b
	pmull2	v6.1q,v21.2d,v6.2d

	eor	v29.16b,v29.16b,v16.16b
	eor	v31.16b,v31.16b,v24.16b
	eor	v30.16b,v30.16b,v6.16b

	ext	v18.16b,v0.16b,v0.16b,#8		//2nd phase of reduction
	pmull	v0.1q,v0.1d,v19.1d
	pmull	v7.1q,v26.1d,v23.1d		//H^3·Ii+1
	eor	v5.16b,v5.16b,v23.16b
	eor	v18.16b,v18.16b,v2.16b
	pmull2	v23.1q,v26.2d,v23.2d
	pmull	v5.1q,v27.1d,v5.1d

	eor	v0.16b,v0.16b,v18.16b
	eor	v29.16b,v29.16b,v7.16b
	eor	v31.16b,v31.16b,v23.16b
	ext	v0.16b,v0.16b,v0.16b,#8
	eor	v30.16b,v30.16b,v5.16b

	subs	x3,x3,#64
	b.hs	.Loop4x

.Ltail4x:
	eor	v16.16b,v4.16b,v0.16b
	ext	v3.16b,v16.16b,v16.16b,#8

	pmull	v0.1q,v28.1d,v3.1d		//H^4·(Xi+Ii)
	eor	v16.16b,v16.16b,v3.16b
	pmull2	v2.1q,v28.2d,v3.2d
	pmull2	v1.1q,v27.2d,v16.2d

	eor	v0.16b,v0.16b,v29.16b
	eor	v2.16b,v2.16b,v31.16b
	eor	v1.16b,v1.16b,v30.16b

	adds	x3,x3,#64
	b.eq	.Ldone4x

	cmp	x3,#32
	b.lo	.Lone
	b.eq	.Ltwo
.Lthree:
	ext	v17.16b,v0.16b,v2.16b,#8		//Karatsuba post-processing
	eor	v18.16b,v0.16b,v2.16b
	eor	v1.16b,v1.16b,v17.16b
	ld1	{v4.2d,v5.2d,v6.2d},[x2]
	eor	v1.16b,v1.16b,v18.16b
	rev64	v5.16b,v5.16b
	rev64	v6.16b,v6.16b
	rev64	v4.16b,v4.16b

	pmull	v18.1q,v0.1d,v19.1d		//1st phase of reduction
	ins	v2.d[0],v1.d[1]
	ins	v1.d[1],v0.d[0]
	ext	v24.16b,v6.16b,v6.16b,#8
	ext	v23.16b,v5.16b,v5.16b,#8
	eor	v0.16b,v1.16b,v18.16b

	pmull	v29.1q,v20.1d,v24.1d		//H·Ii+2
	eor	v6.16b,v6.16b,v24.16b

	ext	v18.16b,v0.16b,v0.16b,#8		//2nd phase of reduction
	pmull	v0.1q,v0.1d,v19.1d
	eor	v18.16b,v18.16b,v2.16b
	pmull2	v31.1q,v20.2d,v24.2d
	pmull	v30.1q,v21.1d,v6.1d
	eor	v0.16b,v0.16b,v18.16b
	pmull	v7.1q,v22.1d,v23.1d		//H^2·Ii+1
	eor	v5.16b,v5.16b,v23.16b
	ext	v0.16b,v0.16b,v0.16b,#8

	pmull2	v23.1q,v22.2d,v23.2d
	eor	v16.16b,v4.16b,v0.16b
	pmull2	v5.1q,v21.2d,v5.2d
	ext	v3.16b,v16.16b,v16.16b,#8

	eor	v29.16b,v29.16b,v7.16b
	eor	v31.16b,v31.16b,v23.16b
	eor	v30.16b,v30.16b,v5.16b

	pmull	v0.1q,v26.1d,v3.1d		//H^3·(Xi+Ii)
	eor	v16.16b,v16.16b,v3.16b
	pmull2	v2.1q,v26.2d,v3.2d
	pmull	v1.1q,v27.1d,v16.1d

	eor	v0.16b,v0.16b,v29.16b
	eor	v2.16b,v2.16b,v31.16b
	eor	v1.16b,v1.16b,v30.16b
	b	.Ldone4x

.align	4
.Ltwo:
	ext	v17.16b,v0.16b,v2.16b,#8		//Karatsuba post-processing
	eor	v18.16b,v0.16b,v2.16b
	eor	v1.16b,v1.16b,v17.16b
	ld1	{v4.2d,v5.2d},[x2]
	eor	v1.16b,v1.16b,v18.16b
	rev64	v5.16b,v5.16b
	rev64	v4.16b,v4.16b

	pmull	v18.1q,v0.1d,v19.1d		//1st phase of reduction
	ins	v2.d[0],v1.d[1]
	ins	v1.d[1],v0.d[0]
	ext	v23.16b,v5.16b,v5.16b,#8
	eor	v0.16b,v1.16b,v18.16b

	ext	v18.16b,v0.16b,v0.16b,#8		//2nd phase of reduction
	pmull	v0.1q,v0.1d,v19.1d
	eor	v18.16b,v18.16b,v2.16b
	eor	v0.16b,v0.16b,v18.16b
	ext	v0.16b,v0.16b,v0.16b,#8

	pmull	v29.1q,v20.1d,v23.1d		//H·Ii+1
	eor	v5.16b,v5.16b,v23.16b

	eor	v16.16b,v4.16b,v0.16b
	ext	v3.16b,v16.16b,v16.16b,#8

	pmull2	v31.1q,v20.2d,v23.2d
	pmull	v30.1q,v21.1d,v5.1d

	pmull	v0.1q,v22.1d,v3.1d		//H^2·(Xi+Ii)
	eor	v16.16b,v16.16b,v3.16b
	pmull2	v2.1q,v22.2d,v3.2d
	pmull2	v1.1q,v21.2d,v16.2d

	eor	v0.16b,v0.16b,v29.16b
	eor	v2.16b,v2.16b,v31.16b
	eor	v1.16b,v1.16b,v30.16b
	b	.Ldone4x

.align	4
.Lone:
	ext	v17.16b,v0.16b,v2.16b,#8		//Karatsuba post-processing
	eor	v18.16b,v0.16b,v2.16b
	eor	v1.16b,v1.16b,v17.16b
	ld1	{v4.2d},[x2]
	eor	v1.16b,v1.16b,v18.16b
	rev64	v4.16b,v4.16b

	pmull	v18.1q,v0.1d,v19.1d		//1st phase of reduction
	ins	v2.d[0],v1.d[1]
	ins	v1.d[1],v0.d[0]
	eor	v0.16b,v1.16b,v18.16b

	ext	v18.16b,v0.16b,v0.16b,#8		//2nd phase of reduction
	pmull	v0.1q,v0.1d,v19.1d
	eor	v18.16b,v18.16b,v2.16b
	eor	v0.16b,v0.16b,v18.16b
	ext	v0.16b,v0.16b,v0.16b,#8

	eor	v16.16b,v4.16b,v0.16b
	ext	v3.16b,v16.16b,v16.16b,#8

	pmull	v0.1q,v20.1d,v3.1d
	eor	v16.16b,v16.16b,v3.16b
	pmull2	v2.1q,v20.2d,v3.2d
	pmull	v1.1q,v21.1d,v16.1d

.Ldone4x:
	ext	v17.16b,v0.16b,v2.16b,#8		//Karatsuba post-processing
	eor	v18.16b,v0.16b,v2.16b
	eor	v1.16b,v1.16b,v17.16b
	eor	v1.16b,v1.16b,v18.16b

	pmull	v18.1q,v0.1d,v19.1d		//1st phase of reduction
	ins	v2.d[0],v1.d[1]
	ins	v1.d[1],v0.d[0]
	eor	v0.16b,v1.16b,v18.16b

	ext	v18.16b,v0.16b,v0.16b,#8		//2nd phase of reduction
	pmull	v0.1q,v0.1d,v19.1d
	eor	v18.16b,v18.16b,v2.16b
	eor	v0.16b,v0.16b,v18.16b
	ext	v0.16b,v0.16b,v0.16b,#8

	rev64	v0.16b,v0.16b
	st1	{v0.2d},[x0]		//write out Xi

	CFI_RET
S2N_BN_SIZE_DIRECTIVE(gcm_ghash_v8_s2n)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack, "", %progbits
#endif
