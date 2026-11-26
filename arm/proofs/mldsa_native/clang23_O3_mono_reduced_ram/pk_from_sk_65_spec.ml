(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The public key of a secret key: the statement. This is the code for       *)
(* mldsa65_pk_from_sk (mld_sign_pk_from_sk in sign.c) from mldsa-native's    *)
(* portable C implementation compiled by clang 23 with -O3 as one            *)
(* translation unit with MLD_CONFIG_REDUCE_RAM (see mldsa_native/README.md). *)
(* It copies rho, the key and tr from the secret key to the stack, unpacks   *)
(* the five polynomials of s1 with inlined vector code (ML-DSA-65 has eta =  *)
(* 4, with four bits per coefficient, and no function for it) and checks     *)
(* them with mldsa65_polyvecl_chknorm, unpacks the six polynomials of s2 one *)
(* at a time with the same code and checks each with an inlined loop,        *)
(* transforms s1 with mldsa_poly_ntt, recomputes t1 into the public key and  *)
(* t0 into a buffer with mld_compute_pack_t0_t165, compares t0 with that in  *)
(* the secret key with an inlined constant-time comparison (a loop of 78     *)
(* passes of vector instructions), hashes the public key with an inlined     *)
(* SHAKE256 (fifteen calls of mldsa_keccakf1600_permute) and compares the    *)
(* hash with tr, all in constant time, and then zeroes the public key with   *)
(* memset if a check failed and its buffers with memset and stores. It is    *)
(* verified in the whole image (see libmldsa.ml) against mld_pk_from_sk_pk   *)
(* and mld_pk_from_sk_valid of common/mldsa_native_sign.ml, using the        *)
(* theorems for the callees and the contracts memset_full_contract and       *)
(* memcpy_full_contract of utils/mlkem_native_libc_full.ml (memcpy is used   *)
(* by compute_pack through the expansion of the matrix), assuming that the   *)
(* expansion of the matrix terminates (mld_matrix_terminates), and shown to  *)
(* be constant time and memory safe, with the events depending on rho, which *)
(* is part of the public key, and on the result of the checks, which the C   *)
(* code declassifies. The stack is the 9216 bytes of the function and the    *)
(* 5312 of the callees below them.                                           *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native.ml";;
needs "arm/proofs/utils/mlkem_native_libc_full.ml";;
needs "common/mldsa_native_sign.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/polyvecl_chknorm_65_spec.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/compute_pack_t0_t1_65_spec.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/libmldsa.ml";;

(*** The code in the image, and the PLT stub for memset:

    mldsa65_pk_from_sk:
       +0x0: stp     x29, x30, [sp, #-96]!
       +0x4: stp     x28, x27, [sp, #16]
       +0x8: stp     x26, x25, [sp, #32]
       +0xc: stp     x24, x23, [sp, #48]
      +0x10: stp     x22, x21, [sp, #64]
      +0x14: stp     x20, x19, [sp, #80]
      +0x18: mov     x29, sp
      +0x1c: sub     x9, sp, #0x2, lsl #12
      +0x20: sub     x9, x9, #0x380
      +0x24: and     x9, x9, #0xffffffffffffffe0
      +0x28: sub     sp, sp, #0x1, lsl #12
      +0x2c: cmp     sp, x9
      +0x30: b.le    <mldsa65_pk_from_sk+0x44>
      +0x34: ldr     xzr, [sp]
      +0x38: sub     sp, sp, #0x1, lsl #12
      +0x3c: cmp     sp, x9
      +0x40: b.gt    <mldsa65_pk_from_sk+0x34>
      +0x44: mov     sp, x9
      +0x48: adrp    x8, <page>
      +0x4c: ldr     xzr, [sp]
      +0x50: movi    v19.16b, #0xf
      +0x54: ldr     x8, [x8, #4088]
      +0x58: movi    v18.4s, #0x4
      +0x5c: mov     x20, x1
      +0x60: mov     x19, x0
      +0x64: add     x0, sp, #0xde0
      +0x68: ldr     x8, [x8]
      +0x6c: str     x8, [sp, #9080]
      +0x70: add     x8, sp, #0xde0
      +0x74: ldp     q0, q1, [x1, #128]
      +0x78: and     v2.16b, v0.16b, v19.16b
      +0x7c: ushr    v0.16b, v0.16b, #4
      +0x80: uxtl    v3.8h, v2.8b
      +0x84: uxtl    v4.8h, v0.8b
      +0x88: uxtl2   v2.8h, v2.16b
      +0x8c: uxtl2   v0.8h, v0.16b
      +0x90: usubw   v5.4s, v18.4s, v3.4h
      +0x94: usubw2  v16.4s, v18.4s, v3.8h
      +0x98: usubw   v6.4s, v18.4s, v4.4h
      +0x9c: usubw2  v17.4s, v18.4s, v4.8h
      +0xa0: usubw   v3.4s, v18.4s, v2.4h
      +0xa4: usubw   v4.4s, v18.4s, v0.4h
      +0xa8: st2     {v5.4s-v6.4s}, [x8], #32
      +0xac: and     v5.16b, v1.16b, v19.16b
      +0xb0: ushr    v1.16b, v1.16b, #4
      +0xb4: usubw2  v6.4s, v18.4s, v2.8h
      +0xb8: usubw2  v7.4s, v18.4s, v0.8h
      +0xbc: uxtl    v2.8h, v5.8b
      +0xc0: st2     {v16.4s-v17.4s}, [x8]
      +0xc4: add     x8, sp, #0xde0
      +0xc8: uxtl    v0.8h, v1.8b
      +0xcc: add     x9, x8, #0x40
      +0xd0: add     x10, x8, #0x400
      +0xd4: add     x24, x8, #0xc00
      +0xd8: add     x25, x8, #0x1, lsl #12
      +0xdc: st2     {v3.4s-v4.4s}, [x9]
      +0xe0: add     x9, x8, #0x60
      +0xe4: usubw   v3.4s, v18.4s, v2.4h
      +0xe8: usubw   v4.4s, v18.4s, v0.4h
      +0xec: st2     {v6.4s-v7.4s}, [x9]
      +0xf0: usubw2  v6.4s, v18.4s, v2.8h
      +0xf4: uxtl2   v2.8h, v5.16b
      +0xf8: usubw2  v7.4s, v18.4s, v0.8h
      +0xfc: uxtl2   v0.8h, v1.16b
     +0x100: add     x9, x8, #0x80
     +0x104: ldp     q1, q5, [x1, #160]
     +0x108: usubw2  v16.4s, v18.4s, v2.8h
     +0x10c: st2     {v3.4s-v4.4s}, [x9]
     +0x110: add     x9, x8, #0xa0
     +0x114: usubw   v3.4s, v18.4s, v2.4h
     +0x118: usubw   v4.4s, v18.4s, v0.4h
     +0x11c: usubw2  v17.4s, v18.4s, v0.8h
     +0x120: st2     {v6.4s-v7.4s}, [x9]
     +0x124: and     v6.16b, v1.16b, v19.16b
     +0x128: ushr    v1.16b, v1.16b, #4
     +0x12c: add     x9, x8, #0xc0
     +0x130: uxtl    v0.8h, v6.8b
     +0x134: uxtl    v2.8h, v1.8b
     +0x138: uxtl2   v1.8h, v1.16b
     +0x13c: st2     {v3.4s-v4.4s}, [x9]
     +0x140: add     x9, x8, #0xe0
     +0x144: usubw   v3.4s, v18.4s, v0.4h
     +0x148: usubw   v4.4s, v18.4s, v2.4h
     +0x14c: st2     {v16.4s-v17.4s}, [x9]
     +0x150: add     x9, x8, #0x100
     +0x154: usubw2  v16.4s, v18.4s, v0.8h
     +0x158: uxtl2   v0.8h, v6.16b
     +0x15c: usubw2  v17.4s, v18.4s, v2.8h
     +0x160: st2     {v3.4s-v4.4s}, [x9]
     +0x164: and     v4.16b, v5.16b, v19.16b
     +0x168: ushr    v5.16b, v5.16b, #4
     +0x16c: usubw   v2.4s, v18.4s, v0.4h
     +0x170: usubw2  v6.4s, v18.4s, v0.8h
     +0x174: add     x9, x8, #0x120
     +0x178: usubw   v3.4s, v18.4s, v1.4h
     +0x17c: usubw2  v7.4s, v18.4s, v1.8h
     +0x180: uxtl    v0.8h, v4.8b
     +0x184: uxtl    v1.8h, v5.8b
     +0x188: st2     {v16.4s-v17.4s}, [x9]
     +0x18c: add     x9, x8, #0x140
     +0x190: st2     {v2.4s-v3.4s}, [x9]
     +0x194: add     x9, x8, #0x160
     +0x198: usubw   v2.4s, v18.4s, v0.4h
     +0x19c: usubw   v3.4s, v18.4s, v1.4h
     +0x1a0: st2     {v6.4s-v7.4s}, [x9]
     +0x1a4: usubw2  v6.4s, v18.4s, v0.8h
     +0x1a8: uxtl2   v0.8h, v4.16b
     +0x1ac: usubw2  v7.4s, v18.4s, v1.8h
     +0x1b0: uxtl2   v1.8h, v5.16b
     +0x1b4: add     x9, x8, #0x180
     +0x1b8: ldp     q4, q5, [x1, #192]
     +0x1bc: usubw2  v16.4s, v18.4s, v0.8h
     +0x1c0: st2     {v2.4s-v3.4s}, [x9]
     +0x1c4: add     x9, x8, #0x1a0
     +0x1c8: usubw   v2.4s, v18.4s, v0.4h
     +0x1cc: usubw   v3.4s, v18.4s, v1.4h
     +0x1d0: usubw2  v17.4s, v18.4s, v1.8h
     +0x1d4: st2     {v6.4s-v7.4s}, [x9]
     +0x1d8: and     v6.16b, v4.16b, v19.16b
     +0x1dc: ushr    v4.16b, v4.16b, #4
     +0x1e0: add     x9, x8, #0x1c0
     +0x1e4: uxtl    v0.8h, v6.8b
     +0x1e8: uxtl    v1.8h, v4.8b
     +0x1ec: st2     {v2.4s-v3.4s}, [x9]
     +0x1f0: add     x9, x8, #0x1e0
     +0x1f4: usubw   v2.4s, v18.4s, v0.4h
     +0x1f8: usubw   v3.4s, v18.4s, v1.4h
     +0x1fc: st2     {v16.4s-v17.4s}, [x9]
     +0x200: usubw2  v16.4s, v18.4s, v0.8h
     +0x204: uxtl2   v0.8h, v6.16b
     +0x208: usubw2  v17.4s, v18.4s, v1.8h
     +0x20c: uxtl2   v1.8h, v4.16b
     +0x210: and     v4.16b, v5.16b, v19.16b
     +0x214: add     x9, x8, #0x200
     +0x218: ushr    v5.16b, v5.16b, #4
     +0x21c: usubw2  v6.4s, v18.4s, v0.8h
     +0x220: st2     {v2.4s-v3.4s}, [x9]
     +0x224: usubw   v2.4s, v18.4s, v0.4h
     +0x228: uxtl    v0.8h, v4.8b
     +0x22c: usubw   v3.4s, v18.4s, v1.4h
     +0x230: add     x9, x8, #0x220
     +0x234: usubw2  v7.4s, v18.4s, v1.8h
     +0x238: uxtl    v1.8h, v5.8b
     +0x23c: st2     {v16.4s-v17.4s}, [x9]
     +0x240: add     x9, x8, #0x240
     +0x244: st2     {v2.4s-v3.4s}, [x9]
     +0x248: add     x9, x8, #0x260
     +0x24c: usubw   v2.4s, v18.4s, v0.4h
     +0x250: usubw   v3.4s, v18.4s, v1.4h
     +0x254: st2     {v6.4s-v7.4s}, [x9]
     +0x258: usubw2  v6.4s, v18.4s, v0.8h
     +0x25c: uxtl2   v0.8h, v4.16b
     +0x260: usubw2  v7.4s, v18.4s, v1.8h
     +0x264: uxtl2   v1.8h, v5.16b
     +0x268: add     x9, x8, #0x280
     +0x26c: ldp     q4, q5, [x1, #224]
     +0x270: usubw2  v16.4s, v18.4s, v0.8h
     +0x274: st2     {v2.4s-v3.4s}, [x9]
     +0x278: add     x9, x8, #0x2a0
     +0x27c: usubw   v2.4s, v18.4s, v0.4h
     +0x280: usubw   v3.4s, v18.4s, v1.4h
     +0x284: usubw2  v17.4s, v18.4s, v1.8h
     +0x288: st2     {v6.4s-v7.4s}, [x9]
     +0x28c: and     v6.16b, v4.16b, v19.16b
     +0x290: ushr    v4.16b, v4.16b, #4
     +0x294: add     x9, x8, #0x2c0
     +0x298: uxtl    v0.8h, v6.8b
     +0x29c: uxtl    v1.8h, v4.8b
     +0x2a0: st2     {v2.4s-v3.4s}, [x9]
     +0x2a4: add     x9, x8, #0x2e0
     +0x2a8: usubw   v2.4s, v18.4s, v0.4h
     +0x2ac: usubw   v3.4s, v18.4s, v1.4h
     +0x2b0: st2     {v16.4s-v17.4s}, [x9]
     +0x2b4: usubw2  v16.4s, v18.4s, v0.8h
     +0x2b8: uxtl2   v0.8h, v6.16b
     +0x2bc: usubw2  v17.4s, v18.4s, v1.8h
     +0x2c0: uxtl2   v1.8h, v4.16b
     +0x2c4: and     v4.16b, v5.16b, v19.16b
     +0x2c8: add     x9, x8, #0x300
     +0x2cc: ushr    v5.16b, v5.16b, #4
     +0x2d0: usubw2  v6.4s, v18.4s, v0.8h
     +0x2d4: st2     {v2.4s-v3.4s}, [x9]
     +0x2d8: usubw   v2.4s, v18.4s, v0.4h
     +0x2dc: uxtl    v0.8h, v4.8b
     +0x2e0: usubw   v3.4s, v18.4s, v1.4h
     +0x2e4: add     x9, x8, #0x320
     +0x2e8: usubw2  v7.4s, v18.4s, v1.8h
     +0x2ec: uxtl    v1.8h, v5.8b
     +0x2f0: st2     {v16.4s-v17.4s}, [x9]
     +0x2f4: add     x9, x8, #0x340
     +0x2f8: st2     {v2.4s-v3.4s}, [x9]
     +0x2fc: add     x9, x8, #0x360
     +0x300: usubw   v2.4s, v18.4s, v0.4h
     +0x304: usubw   v3.4s, v18.4s, v1.4h
     +0x308: st2     {v6.4s-v7.4s}, [x9]
     +0x30c: usubw2  v6.4s, v18.4s, v0.8h
     +0x310: uxtl2   v0.8h, v4.16b
     +0x314: usubw2  v7.4s, v18.4s, v1.8h
     +0x318: uxtl2   v1.8h, v5.16b
     +0x31c: add     x9, x8, #0x380
     +0x320: ldp     q4, q5, [x1, #256]
     +0x324: usubw2  v16.4s, v18.4s, v0.8h
     +0x328: st2     {v2.4s-v3.4s}, [x9]
     +0x32c: add     x9, x8, #0x3a0
     +0x330: usubw   v2.4s, v18.4s, v0.4h
     +0x334: usubw   v3.4s, v18.4s, v1.4h
     +0x338: usubw2  v17.4s, v18.4s, v1.8h
     +0x33c: st2     {v6.4s-v7.4s}, [x9]
     +0x340: and     v6.16b, v4.16b, v19.16b
     +0x344: ushr    v4.16b, v4.16b, #4
     +0x348: add     x9, x8, #0x3c0
     +0x34c: uxtl    v0.8h, v6.8b
     +0x350: uxtl    v1.8h, v4.8b
     +0x354: st2     {v2.4s-v3.4s}, [x9]
     +0x358: add     x9, x8, #0x3e0
     +0x35c: usubw   v2.4s, v18.4s, v0.4h
     +0x360: usubw   v3.4s, v18.4s, v1.4h
     +0x364: st2     {v16.4s-v17.4s}, [x9]
     +0x368: usubw2  v16.4s, v18.4s, v0.8h
     +0x36c: uxtl2   v0.8h, v6.16b
     +0x370: usubw2  v17.4s, v18.4s, v1.8h
     +0x374: uxtl2   v1.8h, v4.16b
     +0x378: and     v4.16b, v5.16b, v19.16b
     +0x37c: ushr    v5.16b, v5.16b, #4
     +0x380: add     x9, x8, #0x400
     +0x384: usubw2  v6.4s, v18.4s, v0.8h
     +0x388: st2     {v2.4s-v3.4s}, [x10]
     +0x38c: usubw   v2.4s, v18.4s, v0.4h
     +0x390: uxtl    v0.8h, v4.8b
     +0x394: usubw   v3.4s, v18.4s, v1.4h
     +0x398: usubw2  v7.4s, v18.4s, v1.8h
     +0x39c: uxtl    v1.8h, v5.8b
     +0x3a0: add     x10, x8, #0x800
     +0x3a4: str     x9, [sp, #24]
     +0x3a8: add     x9, x8, #0x420
     +0x3ac: st2     {v16.4s-v17.4s}, [x9]
     +0x3b0: add     x9, x8, #0x440
     +0x3b4: st2     {v2.4s-v3.4s}, [x9]
     +0x3b8: add     x9, x8, #0x460
     +0x3bc: usubw   v2.4s, v18.4s, v0.4h
     +0x3c0: usubw   v3.4s, v18.4s, v1.4h
     +0x3c4: st2     {v6.4s-v7.4s}, [x9]
     +0x3c8: usubw2  v6.4s, v18.4s, v0.8h
     +0x3cc: uxtl2   v0.8h, v4.16b
     +0x3d0: usubw2  v7.4s, v18.4s, v1.8h
     +0x3d4: uxtl2   v1.8h, v5.16b
     +0x3d8: add     x9, x8, #0x480
     +0x3dc: ldp     q4, q5, [x1, #288]
     +0x3e0: usubw2  v16.4s, v18.4s, v0.8h
     +0x3e4: st2     {v2.4s-v3.4s}, [x9]
     +0x3e8: add     x9, x8, #0x4a0
     +0x3ec: usubw   v2.4s, v18.4s, v0.4h
     +0x3f0: usubw   v3.4s, v18.4s, v1.4h
     +0x3f4: usubw2  v17.4s, v18.4s, v1.8h
     +0x3f8: st2     {v6.4s-v7.4s}, [x9]
     +0x3fc: and     v6.16b, v4.16b, v19.16b
     +0x400: ushr    v4.16b, v4.16b, #4
     +0x404: add     x9, x8, #0x4c0
     +0x408: uxtl    v0.8h, v6.8b
     +0x40c: uxtl    v1.8h, v4.8b
     +0x410: st2     {v2.4s-v3.4s}, [x9]
     +0x414: add     x9, x8, #0x4e0
     +0x418: usubw   v2.4s, v18.4s, v0.4h
     +0x41c: usubw   v3.4s, v18.4s, v1.4h
     +0x420: st2     {v16.4s-v17.4s}, [x9]
     +0x424: usubw2  v16.4s, v18.4s, v0.8h
     +0x428: uxtl2   v0.8h, v6.16b
     +0x42c: usubw2  v17.4s, v18.4s, v1.8h
     +0x430: uxtl2   v1.8h, v4.16b
     +0x434: and     v4.16b, v5.16b, v19.16b
     +0x438: add     x9, x8, #0x500
     +0x43c: ushr    v5.16b, v5.16b, #4
     +0x440: usubw2  v6.4s, v18.4s, v0.8h
     +0x444: st2     {v2.4s-v3.4s}, [x9]
     +0x448: usubw   v2.4s, v18.4s, v0.4h
     +0x44c: uxtl    v0.8h, v4.8b
     +0x450: usubw   v3.4s, v18.4s, v1.4h
     +0x454: add     x9, x8, #0x520
     +0x458: usubw2  v7.4s, v18.4s, v1.8h
     +0x45c: uxtl    v1.8h, v5.8b
     +0x460: st2     {v16.4s-v17.4s}, [x9]
     +0x464: add     x9, x8, #0x540
     +0x468: st2     {v2.4s-v3.4s}, [x9]
     +0x46c: add     x9, x8, #0x560
     +0x470: usubw   v2.4s, v18.4s, v0.4h
     +0x474: usubw   v3.4s, v18.4s, v1.4h
     +0x478: st2     {v6.4s-v7.4s}, [x9]
     +0x47c: usubw2  v6.4s, v18.4s, v0.8h
     +0x480: uxtl2   v0.8h, v4.16b
     +0x484: usubw2  v7.4s, v18.4s, v1.8h
     +0x488: uxtl2   v1.8h, v5.16b
     +0x48c: add     x9, x8, #0x580
     +0x490: ldp     q4, q5, [x1, #320]
     +0x494: usubw2  v16.4s, v18.4s, v0.8h
     +0x498: st2     {v2.4s-v3.4s}, [x9]
     +0x49c: add     x9, x8, #0x5a0
     +0x4a0: usubw   v2.4s, v18.4s, v0.4h
     +0x4a4: usubw   v3.4s, v18.4s, v1.4h
     +0x4a8: usubw2  v17.4s, v18.4s, v1.8h
     +0x4ac: st2     {v6.4s-v7.4s}, [x9]
     +0x4b0: and     v6.16b, v4.16b, v19.16b
     +0x4b4: ushr    v4.16b, v4.16b, #4
     +0x4b8: add     x9, x8, #0x5c0
     +0x4bc: uxtl    v0.8h, v6.8b
     +0x4c0: uxtl    v1.8h, v4.8b
     +0x4c4: st2     {v2.4s-v3.4s}, [x9]
     +0x4c8: add     x9, x8, #0x5e0
     +0x4cc: usubw   v2.4s, v18.4s, v0.4h
     +0x4d0: usubw   v3.4s, v18.4s, v1.4h
     +0x4d4: st2     {v16.4s-v17.4s}, [x9]
     +0x4d8: usubw2  v16.4s, v18.4s, v0.8h
     +0x4dc: uxtl2   v0.8h, v6.16b
     +0x4e0: usubw2  v17.4s, v18.4s, v1.8h
     +0x4e4: uxtl2   v1.8h, v4.16b
     +0x4e8: and     v4.16b, v5.16b, v19.16b
     +0x4ec: add     x9, x8, #0x600
     +0x4f0: ushr    v5.16b, v5.16b, #4
     +0x4f4: usubw2  v6.4s, v18.4s, v0.8h
     +0x4f8: st2     {v2.4s-v3.4s}, [x9]
     +0x4fc: usubw   v2.4s, v18.4s, v0.4h
     +0x500: uxtl    v0.8h, v4.8b
     +0x504: usubw   v3.4s, v18.4s, v1.4h
     +0x508: add     x9, x8, #0x620
     +0x50c: usubw2  v7.4s, v18.4s, v1.8h
     +0x510: uxtl    v1.8h, v5.8b
     +0x514: st2     {v16.4s-v17.4s}, [x9]
     +0x518: add     x9, x8, #0x640
     +0x51c: st2     {v2.4s-v3.4s}, [x9]
     +0x520: add     x9, x8, #0x660
     +0x524: usubw   v2.4s, v18.4s, v0.4h
     +0x528: usubw   v3.4s, v18.4s, v1.4h
     +0x52c: st2     {v6.4s-v7.4s}, [x9]
     +0x530: usubw2  v6.4s, v18.4s, v0.8h
     +0x534: uxtl2   v0.8h, v4.16b
     +0x538: usubw2  v7.4s, v18.4s, v1.8h
     +0x53c: uxtl2   v1.8h, v5.16b
     +0x540: add     x9, x8, #0x680
     +0x544: ldp     q4, q5, [x1, #352]
     +0x548: usubw2  v16.4s, v18.4s, v0.8h
     +0x54c: st2     {v2.4s-v3.4s}, [x9]
     +0x550: add     x9, x8, #0x6a0
     +0x554: usubw   v2.4s, v18.4s, v0.4h
     +0x558: usubw   v3.4s, v18.4s, v1.4h
     +0x55c: usubw2  v17.4s, v18.4s, v1.8h
     +0x560: st2     {v6.4s-v7.4s}, [x9]
     +0x564: and     v6.16b, v4.16b, v19.16b
     +0x568: ushr    v4.16b, v4.16b, #4
     +0x56c: add     x9, x8, #0x6c0
     +0x570: uxtl    v0.8h, v6.8b
     +0x574: uxtl    v1.8h, v4.8b
     +0x578: st2     {v2.4s-v3.4s}, [x9]
     +0x57c: add     x9, x8, #0x6e0
     +0x580: usubw   v2.4s, v18.4s, v0.4h
     +0x584: usubw   v3.4s, v18.4s, v1.4h
     +0x588: st2     {v16.4s-v17.4s}, [x9]
     +0x58c: usubw2  v16.4s, v18.4s, v0.8h
     +0x590: uxtl2   v0.8h, v6.16b
     +0x594: usubw2  v17.4s, v18.4s, v1.8h
     +0x598: uxtl2   v1.8h, v4.16b
     +0x59c: and     v4.16b, v5.16b, v19.16b
     +0x5a0: add     x9, x8, #0x700
     +0x5a4: ushr    v5.16b, v5.16b, #4
     +0x5a8: usubw2  v6.4s, v18.4s, v0.8h
     +0x5ac: st2     {v2.4s-v3.4s}, [x9]
     +0x5b0: usubw   v2.4s, v18.4s, v0.4h
     +0x5b4: uxtl    v0.8h, v4.8b
     +0x5b8: usubw   v3.4s, v18.4s, v1.4h
     +0x5bc: add     x9, x8, #0x720
     +0x5c0: usubw2  v7.4s, v18.4s, v1.8h
     +0x5c4: uxtl    v1.8h, v5.8b
     +0x5c8: st2     {v16.4s-v17.4s}, [x9]
     +0x5cc: add     x9, x8, #0x740
     +0x5d0: st2     {v2.4s-v3.4s}, [x9]
     +0x5d4: add     x9, x8, #0x760
     +0x5d8: usubw   v2.4s, v18.4s, v0.4h
     +0x5dc: usubw   v3.4s, v18.4s, v1.4h
     +0x5e0: st2     {v6.4s-v7.4s}, [x9]
     +0x5e4: usubw2  v6.4s, v18.4s, v0.8h
     +0x5e8: uxtl2   v0.8h, v4.16b
     +0x5ec: usubw2  v7.4s, v18.4s, v1.8h
     +0x5f0: uxtl2   v1.8h, v5.16b
     +0x5f4: add     x9, x8, #0x780
     +0x5f8: ldp     q4, q5, [x1, #384]
     +0x5fc: usubw2  v16.4s, v18.4s, v0.8h
     +0x600: st2     {v2.4s-v3.4s}, [x9]
     +0x604: add     x9, x8, #0x7a0
     +0x608: usubw   v2.4s, v18.4s, v0.4h
     +0x60c: usubw   v3.4s, v18.4s, v1.4h
     +0x610: usubw2  v17.4s, v18.4s, v1.8h
     +0x614: st2     {v6.4s-v7.4s}, [x9]
     +0x618: and     v6.16b, v4.16b, v19.16b
     +0x61c: ushr    v4.16b, v4.16b, #4
     +0x620: add     x9, x8, #0x7c0
     +0x624: uxtl    v0.8h, v6.8b
     +0x628: uxtl    v1.8h, v4.8b
     +0x62c: st2     {v2.4s-v3.4s}, [x9]
     +0x630: add     x9, x8, #0x7e0
     +0x634: usubw   v2.4s, v18.4s, v0.4h
     +0x638: usubw   v3.4s, v18.4s, v1.4h
     +0x63c: st2     {v16.4s-v17.4s}, [x9]
     +0x640: usubw2  v16.4s, v18.4s, v0.8h
     +0x644: uxtl2   v0.8h, v6.16b
     +0x648: usubw2  v17.4s, v18.4s, v1.8h
     +0x64c: uxtl2   v1.8h, v4.16b
     +0x650: and     v4.16b, v5.16b, v19.16b
     +0x654: ushr    v5.16b, v5.16b, #4
     +0x658: add     x9, x8, #0x800
     +0x65c: usubw2  v6.4s, v18.4s, v0.8h
     +0x660: st2     {v2.4s-v3.4s}, [x10]
     +0x664: usubw   v2.4s, v18.4s, v0.4h
     +0x668: uxtl    v0.8h, v4.8b
     +0x66c: usubw   v3.4s, v18.4s, v1.4h
     +0x670: usubw2  v7.4s, v18.4s, v1.8h
     +0x674: uxtl    v1.8h, v5.8b
     +0x678: str     x9, [sp, #8]
     +0x67c: add     x9, x8, #0x820
     +0x680: st2     {v16.4s-v17.4s}, [x9]
     +0x684: add     x9, x8, #0x840
     +0x688: st2     {v2.4s-v3.4s}, [x9]
     +0x68c: add     x9, x8, #0x860
     +0x690: usubw   v2.4s, v18.4s, v0.4h
     +0x694: usubw   v3.4s, v18.4s, v1.4h
     +0x698: st2     {v6.4s-v7.4s}, [x9]
     +0x69c: usubw2  v6.4s, v18.4s, v0.8h
     +0x6a0: uxtl2   v0.8h, v4.16b
     +0x6a4: usubw2  v7.4s, v18.4s, v1.8h
     +0x6a8: uxtl2   v1.8h, v5.16b
     +0x6ac: add     x9, x8, #0x880
     +0x6b0: ldp     q4, q5, [x1, #416]
     +0x6b4: usubw2  v16.4s, v18.4s, v0.8h
     +0x6b8: st2     {v2.4s-v3.4s}, [x9]
     +0x6bc: add     x9, x8, #0x8a0
     +0x6c0: usubw   v2.4s, v18.4s, v0.4h
     +0x6c4: usubw   v3.4s, v18.4s, v1.4h
     +0x6c8: usubw2  v17.4s, v18.4s, v1.8h
     +0x6cc: st2     {v6.4s-v7.4s}, [x9]
     +0x6d0: and     v6.16b, v4.16b, v19.16b
     +0x6d4: ushr    v4.16b, v4.16b, #4
     +0x6d8: add     x9, x8, #0x8c0
     +0x6dc: uxtl    v0.8h, v6.8b
     +0x6e0: uxtl    v1.8h, v4.8b
     +0x6e4: st2     {v2.4s-v3.4s}, [x9]
     +0x6e8: add     x9, x8, #0x8e0
     +0x6ec: usubw   v2.4s, v18.4s, v0.4h
     +0x6f0: usubw   v3.4s, v18.4s, v1.4h
     +0x6f4: st2     {v16.4s-v17.4s}, [x9]
     +0x6f8: usubw2  v16.4s, v18.4s, v0.8h
     +0x6fc: uxtl2   v0.8h, v6.16b
     +0x700: usubw2  v17.4s, v18.4s, v1.8h
     +0x704: uxtl2   v1.8h, v4.16b
     +0x708: and     v4.16b, v5.16b, v19.16b
     +0x70c: add     x9, x8, #0x900
     +0x710: ushr    v5.16b, v5.16b, #4
     +0x714: usubw2  v6.4s, v18.4s, v0.8h
     +0x718: st2     {v2.4s-v3.4s}, [x9]
     +0x71c: usubw   v2.4s, v18.4s, v0.4h
     +0x720: uxtl    v0.8h, v4.8b
     +0x724: usubw   v3.4s, v18.4s, v1.4h
     +0x728: add     x9, x8, #0x920
     +0x72c: usubw2  v7.4s, v18.4s, v1.8h
     +0x730: uxtl    v1.8h, v5.8b
     +0x734: st2     {v16.4s-v17.4s}, [x9]
     +0x738: add     x9, x8, #0x940
     +0x73c: st2     {v2.4s-v3.4s}, [x9]
     +0x740: add     x9, x8, #0x960
     +0x744: usubw   v2.4s, v18.4s, v0.4h
     +0x748: usubw   v3.4s, v18.4s, v1.4h
     +0x74c: st2     {v6.4s-v7.4s}, [x9]
     +0x750: usubw2  v6.4s, v18.4s, v0.8h
     +0x754: uxtl2   v0.8h, v4.16b
     +0x758: usubw2  v7.4s, v18.4s, v1.8h
     +0x75c: uxtl2   v1.8h, v5.16b
     +0x760: add     x9, x8, #0x980
     +0x764: ldp     q4, q5, [x1, #448]
     +0x768: usubw2  v16.4s, v18.4s, v0.8h
     +0x76c: st2     {v2.4s-v3.4s}, [x9]
     +0x770: add     x9, x8, #0x9a0
     +0x774: usubw   v2.4s, v18.4s, v0.4h
     +0x778: usubw   v3.4s, v18.4s, v1.4h
     +0x77c: usubw2  v17.4s, v18.4s, v1.8h
     +0x780: st2     {v6.4s-v7.4s}, [x9]
     +0x784: and     v6.16b, v4.16b, v19.16b
     +0x788: ushr    v4.16b, v4.16b, #4
     +0x78c: add     x9, x8, #0x9c0
     +0x790: uxtl    v0.8h, v6.8b
     +0x794: uxtl    v1.8h, v4.8b
     +0x798: st2     {v2.4s-v3.4s}, [x9]
     +0x79c: add     x9, x8, #0x9e0
     +0x7a0: usubw   v2.4s, v18.4s, v0.4h
     +0x7a4: usubw   v3.4s, v18.4s, v1.4h
     +0x7a8: st2     {v16.4s-v17.4s}, [x9]
     +0x7ac: usubw2  v16.4s, v18.4s, v0.8h
     +0x7b0: uxtl2   v0.8h, v6.16b
     +0x7b4: usubw2  v17.4s, v18.4s, v1.8h
     +0x7b8: uxtl2   v1.8h, v4.16b
     +0x7bc: and     v4.16b, v5.16b, v19.16b
     +0x7c0: add     x9, x8, #0xa00
     +0x7c4: ushr    v5.16b, v5.16b, #4
     +0x7c8: usubw2  v6.4s, v18.4s, v0.8h
     +0x7cc: st2     {v2.4s-v3.4s}, [x9]
     +0x7d0: usubw   v2.4s, v18.4s, v0.4h
     +0x7d4: uxtl    v0.8h, v4.8b
     +0x7d8: usubw   v3.4s, v18.4s, v1.4h
     +0x7dc: add     x9, x8, #0xa20
     +0x7e0: usubw2  v7.4s, v18.4s, v1.8h
     +0x7e4: uxtl    v1.8h, v5.8b
     +0x7e8: st2     {v16.4s-v17.4s}, [x9]
     +0x7ec: add     x9, x8, #0xa40
     +0x7f0: st2     {v2.4s-v3.4s}, [x9]
     +0x7f4: add     x9, x8, #0xa60
     +0x7f8: usubw   v2.4s, v18.4s, v0.4h
     +0x7fc: usubw   v3.4s, v18.4s, v1.4h
     +0x800: st2     {v6.4s-v7.4s}, [x9]
     +0x804: usubw2  v6.4s, v18.4s, v0.8h
     +0x808: uxtl2   v0.8h, v4.16b
     +0x80c: usubw2  v7.4s, v18.4s, v1.8h
     +0x810: uxtl2   v1.8h, v5.16b
     +0x814: add     x9, x8, #0xa80
     +0x818: ldp     q4, q5, [x1, #480]
     +0x81c: usubw2  v16.4s, v18.4s, v0.8h
     +0x820: st2     {v2.4s-v3.4s}, [x9]
     +0x824: add     x9, x8, #0xaa0
     +0x828: usubw   v2.4s, v18.4s, v0.4h
     +0x82c: usubw   v3.4s, v18.4s, v1.4h
     +0x830: usubw2  v17.4s, v18.4s, v1.8h
     +0x834: st2     {v6.4s-v7.4s}, [x9]
     +0x838: and     v6.16b, v4.16b, v19.16b
     +0x83c: ushr    v4.16b, v4.16b, #4
     +0x840: add     x9, x8, #0xac0
     +0x844: uxtl    v0.8h, v6.8b
     +0x848: uxtl    v1.8h, v4.8b
     +0x84c: st2     {v2.4s-v3.4s}, [x9]
     +0x850: add     x9, x8, #0xae0
     +0x854: usubw   v2.4s, v18.4s, v0.4h
     +0x858: usubw   v3.4s, v18.4s, v1.4h
     +0x85c: st2     {v16.4s-v17.4s}, [x9]
     +0x860: usubw2  v16.4s, v18.4s, v0.8h
     +0x864: uxtl2   v0.8h, v6.16b
     +0x868: usubw2  v17.4s, v18.4s, v1.8h
     +0x86c: uxtl2   v1.8h, v4.16b
     +0x870: and     v4.16b, v5.16b, v19.16b
     +0x874: add     x9, x8, #0xb00
     +0x878: ushr    v5.16b, v5.16b, #4
     +0x87c: usubw2  v6.4s, v18.4s, v0.8h
     +0x880: st2     {v2.4s-v3.4s}, [x9]
     +0x884: usubw   v2.4s, v18.4s, v0.4h
     +0x888: uxtl    v0.8h, v4.8b
     +0x88c: usubw   v3.4s, v18.4s, v1.4h
     +0x890: add     x9, x8, #0xb20
     +0x894: usubw2  v7.4s, v18.4s, v1.8h
     +0x898: uxtl    v1.8h, v5.8b
     +0x89c: st2     {v16.4s-v17.4s}, [x9]
     +0x8a0: add     x9, x8, #0xb40
     +0x8a4: st2     {v2.4s-v3.4s}, [x9]
     +0x8a8: add     x9, x8, #0xb60
     +0x8ac: usubw   v2.4s, v18.4s, v0.4h
     +0x8b0: usubw   v3.4s, v18.4s, v1.4h
     +0x8b4: st2     {v6.4s-v7.4s}, [x9]
     +0x8b8: usubw2  v6.4s, v18.4s, v0.8h
     +0x8bc: uxtl2   v0.8h, v4.16b
     +0x8c0: usubw2  v7.4s, v18.4s, v1.8h
     +0x8c4: uxtl2   v1.8h, v5.16b
     +0x8c8: add     x9, x8, #0xb80
     +0x8cc: ldp     q4, q5, [x1, #512]
     +0x8d0: usubw2  v16.4s, v18.4s, v0.8h
     +0x8d4: st2     {v2.4s-v3.4s}, [x9]
     +0x8d8: add     x9, x8, #0xba0
     +0x8dc: usubw   v2.4s, v18.4s, v0.4h
     +0x8e0: usubw   v3.4s, v18.4s, v1.4h
     +0x8e4: usubw2  v17.4s, v18.4s, v1.8h
     +0x8e8: st2     {v6.4s-v7.4s}, [x9]
     +0x8ec: and     v6.16b, v4.16b, v19.16b
     +0x8f0: ushr    v4.16b, v4.16b, #4
     +0x8f4: add     x9, x8, #0xbc0
     +0x8f8: uxtl    v0.8h, v6.8b
     +0x8fc: uxtl    v1.8h, v4.8b
     +0x900: st2     {v2.4s-v3.4s}, [x9]
     +0x904: add     x9, x8, #0xbe0
     +0x908: usubw   v2.4s, v18.4s, v0.4h
     +0x90c: usubw   v3.4s, v18.4s, v1.4h
     +0x910: st2     {v16.4s-v17.4s}, [x9]
     +0x914: usubw2  v16.4s, v18.4s, v0.8h
     +0x918: uxtl2   v0.8h, v6.16b
     +0x91c: usubw2  v17.4s, v18.4s, v1.8h
     +0x920: uxtl2   v1.8h, v4.16b
     +0x924: and     v4.16b, v5.16b, v19.16b
     +0x928: ushr    v5.16b, v5.16b, #4
     +0x92c: add     x9, x8, #0xc20
     +0x930: usubw2  v6.4s, v18.4s, v0.8h
     +0x934: st2     {v2.4s-v3.4s}, [x24]
     +0x938: usubw   v2.4s, v18.4s, v0.4h
     +0x93c: uxtl    v0.8h, v4.8b
     +0x940: usubw   v3.4s, v18.4s, v1.4h
     +0x944: usubw2  v7.4s, v18.4s, v1.8h
     +0x948: uxtl    v1.8h, v5.8b
     +0x94c: st2     {v16.4s-v17.4s}, [x9]
     +0x950: add     x9, x8, #0xc40
     +0x954: st2     {v2.4s-v3.4s}, [x9]
     +0x958: add     x9, x8, #0xc60
     +0x95c: usubw   v2.4s, v18.4s, v0.4h
     +0x960: usubw   v3.4s, v18.4s, v1.4h
     +0x964: st2     {v6.4s-v7.4s}, [x9]
     +0x968: usubw2  v6.4s, v18.4s, v0.8h
     +0x96c: uxtl2   v0.8h, v4.16b
     +0x970: usubw2  v7.4s, v18.4s, v1.8h
     +0x974: uxtl2   v1.8h, v5.16b
     +0x978: add     x9, x8, #0xc80
     +0x97c: ldp     q4, q5, [x1, #544]
     +0x980: usubw2  v16.4s, v18.4s, v0.8h
     +0x984: st2     {v2.4s-v3.4s}, [x9]
     +0x988: add     x9, x8, #0xca0
     +0x98c: usubw   v2.4s, v18.4s, v0.4h
     +0x990: usubw   v3.4s, v18.4s, v1.4h
     +0x994: usubw2  v17.4s, v18.4s, v1.8h
     +0x998: st2     {v6.4s-v7.4s}, [x9]
     +0x99c: and     v6.16b, v4.16b, v19.16b
     +0x9a0: ushr    v4.16b, v4.16b, #4
     +0x9a4: add     x9, x8, #0xcc0
     +0x9a8: uxtl    v0.8h, v6.8b
     +0x9ac: uxtl    v1.8h, v4.8b
     +0x9b0: st2     {v2.4s-v3.4s}, [x9]
     +0x9b4: add     x9, x8, #0xce0
     +0x9b8: usubw   v2.4s, v18.4s, v0.4h
     +0x9bc: usubw   v3.4s, v18.4s, v1.4h
     +0x9c0: st2     {v16.4s-v17.4s}, [x9]
     +0x9c4: usubw2  v16.4s, v18.4s, v0.8h
     +0x9c8: uxtl2   v0.8h, v6.16b
     +0x9cc: usubw2  v17.4s, v18.4s, v1.8h
     +0x9d0: uxtl2   v1.8h, v4.16b
     +0x9d4: and     v4.16b, v5.16b, v19.16b
     +0x9d8: add     x9, x8, #0xd00
     +0x9dc: ushr    v5.16b, v5.16b, #4
     +0x9e0: usubw2  v6.4s, v18.4s, v0.8h
     +0x9e4: st2     {v2.4s-v3.4s}, [x9]
     +0x9e8: usubw   v2.4s, v18.4s, v0.4h
     +0x9ec: uxtl    v0.8h, v4.8b
     +0x9f0: usubw   v3.4s, v18.4s, v1.4h
     +0x9f4: add     x9, x8, #0xd20
     +0x9f8: usubw2  v7.4s, v18.4s, v1.8h
     +0x9fc: uxtl    v1.8h, v5.8b
     +0xa00: st2     {v16.4s-v17.4s}, [x9]
     +0xa04: add     x9, x8, #0xd40
     +0xa08: st2     {v2.4s-v3.4s}, [x9]
     +0xa0c: add     x9, x8, #0xd60
     +0xa10: usubw   v2.4s, v18.4s, v0.4h
     +0xa14: usubw   v3.4s, v18.4s, v1.4h
     +0xa18: st2     {v6.4s-v7.4s}, [x9]
     +0xa1c: usubw2  v6.4s, v18.4s, v0.8h
     +0xa20: uxtl2   v0.8h, v4.16b
     +0xa24: usubw2  v7.4s, v18.4s, v1.8h
     +0xa28: uxtl2   v1.8h, v5.16b
     +0xa2c: add     x9, x8, #0xd80
     +0xa30: ldp     q4, q5, [x1, #576]
     +0xa34: usubw2  v16.4s, v18.4s, v0.8h
     +0xa38: st2     {v2.4s-v3.4s}, [x9]
     +0xa3c: add     x9, x8, #0xda0
     +0xa40: usubw   v2.4s, v18.4s, v0.4h
     +0xa44: usubw   v3.4s, v18.4s, v1.4h
     +0xa48: usubw2  v17.4s, v18.4s, v1.8h
     +0xa4c: st2     {v6.4s-v7.4s}, [x9]
     +0xa50: and     v6.16b, v4.16b, v19.16b
     +0xa54: ushr    v4.16b, v4.16b, #4
     +0xa58: add     x9, x8, #0xdc0
     +0xa5c: uxtl    v0.8h, v6.8b
     +0xa60: uxtl    v1.8h, v4.8b
     +0xa64: st2     {v2.4s-v3.4s}, [x9]
     +0xa68: add     x9, x8, #0xde0
     +0xa6c: usubw   v2.4s, v18.4s, v0.4h
     +0xa70: usubw   v3.4s, v18.4s, v1.4h
     +0xa74: st2     {v16.4s-v17.4s}, [x9]
     +0xa78: usubw2  v16.4s, v18.4s, v0.8h
     +0xa7c: uxtl2   v0.8h, v6.16b
     +0xa80: usubw2  v17.4s, v18.4s, v1.8h
     +0xa84: uxtl2   v1.8h, v4.16b
     +0xa88: and     v4.16b, v5.16b, v19.16b
     +0xa8c: add     x9, x8, #0xe00
     +0xa90: ushr    v5.16b, v5.16b, #4
     +0xa94: usubw2  v6.4s, v18.4s, v0.8h
     +0xa98: st2     {v2.4s-v3.4s}, [x9]
     +0xa9c: usubw   v2.4s, v18.4s, v0.4h
     +0xaa0: uxtl    v0.8h, v4.8b
     +0xaa4: usubw   v3.4s, v18.4s, v1.4h
     +0xaa8: add     x9, x8, #0xe20
     +0xaac: usubw2  v7.4s, v18.4s, v1.8h
     +0xab0: uxtl    v1.8h, v5.8b
     +0xab4: st2     {v16.4s-v17.4s}, [x9]
     +0xab8: add     x9, x8, #0xe40
     +0xabc: st2     {v2.4s-v3.4s}, [x9]
     +0xac0: add     x9, x8, #0xe60
     +0xac4: usubw   v2.4s, v18.4s, v0.4h
     +0xac8: usubw   v3.4s, v18.4s, v1.4h
     +0xacc: st2     {v6.4s-v7.4s}, [x9]
     +0xad0: usubw2  v6.4s, v18.4s, v0.8h
     +0xad4: uxtl2   v0.8h, v4.16b
     +0xad8: usubw2  v7.4s, v18.4s, v1.8h
     +0xadc: uxtl2   v1.8h, v5.16b
     +0xae0: add     x9, x8, #0xe80
     +0xae4: ldp     q4, q5, [x1, #608]
     +0xae8: usubw2  v16.4s, v18.4s, v0.8h
     +0xaec: st2     {v2.4s-v3.4s}, [x9]
     +0xaf0: add     x9, x8, #0xea0
     +0xaf4: usubw   v2.4s, v18.4s, v0.4h
     +0xaf8: usubw   v3.4s, v18.4s, v1.4h
     +0xafc: usubw2  v17.4s, v18.4s, v1.8h
     +0xb00: st2     {v6.4s-v7.4s}, [x9]
     +0xb04: and     v6.16b, v4.16b, v19.16b
     +0xb08: ushr    v4.16b, v4.16b, #4
     +0xb0c: add     x9, x8, #0xec0
     +0xb10: uxtl    v0.8h, v6.8b
     +0xb14: uxtl    v1.8h, v4.8b
     +0xb18: st2     {v2.4s-v3.4s}, [x9]
     +0xb1c: add     x9, x8, #0xee0
     +0xb20: usubw   v2.4s, v18.4s, v0.4h
     +0xb24: usubw   v3.4s, v18.4s, v1.4h
     +0xb28: st2     {v16.4s-v17.4s}, [x9]
     +0xb2c: usubw2  v16.4s, v18.4s, v0.8h
     +0xb30: uxtl2   v0.8h, v6.16b
     +0xb34: usubw2  v17.4s, v18.4s, v1.8h
     +0xb38: uxtl2   v1.8h, v4.16b
     +0xb3c: and     v4.16b, v5.16b, v19.16b
     +0xb40: add     x9, x8, #0xf00
     +0xb44: ushr    v5.16b, v5.16b, #4
     +0xb48: usubw2  v6.4s, v18.4s, v0.8h
     +0xb4c: st2     {v2.4s-v3.4s}, [x9]
     +0xb50: usubw   v2.4s, v18.4s, v0.4h
     +0xb54: uxtl    v0.8h, v4.8b
     +0xb58: usubw   v3.4s, v18.4s, v1.4h
     +0xb5c: add     x9, x8, #0xf20
     +0xb60: usubw2  v7.4s, v18.4s, v1.8h
     +0xb64: uxtl    v1.8h, v5.8b
     +0xb68: st2     {v16.4s-v17.4s}, [x9]
     +0xb6c: add     x9, x8, #0xf40
     +0xb70: st2     {v2.4s-v3.4s}, [x9]
     +0xb74: add     x9, x8, #0xf60
     +0xb78: usubw   v2.4s, v18.4s, v0.4h
     +0xb7c: usubw   v3.4s, v18.4s, v1.4h
     +0xb80: st2     {v6.4s-v7.4s}, [x9]
     +0xb84: usubw2  v6.4s, v18.4s, v0.8h
     +0xb88: uxtl2   v0.8h, v4.16b
     +0xb8c: usubw2  v7.4s, v18.4s, v1.8h
     +0xb90: uxtl2   v1.8h, v5.16b
     +0xb94: add     x9, x8, #0xf80
     +0xb98: ldp     q4, q5, [x1, #640]
     +0xb9c: usubw2  v16.4s, v18.4s, v0.8h
     +0xba0: st2     {v2.4s-v3.4s}, [x9]
     +0xba4: add     x9, x8, #0xfa0
     +0xba8: usubw   v2.4s, v18.4s, v0.4h
     +0xbac: usubw   v3.4s, v18.4s, v1.4h
     +0xbb0: usubw2  v17.4s, v18.4s, v1.8h
     +0xbb4: st2     {v6.4s-v7.4s}, [x9]
     +0xbb8: and     v6.16b, v4.16b, v19.16b
     +0xbbc: ushr    v4.16b, v4.16b, #4
     +0xbc0: add     x9, x8, #0xfc0
     +0xbc4: uxtl    v0.8h, v6.8b
     +0xbc8: uxtl    v1.8h, v4.8b
     +0xbcc: st2     {v2.4s-v3.4s}, [x9]
     +0xbd0: add     x9, x8, #0xfe0
     +0xbd4: usubw   v2.4s, v18.4s, v0.4h
     +0xbd8: usubw   v3.4s, v18.4s, v1.4h
     +0xbdc: st2     {v16.4s-v17.4s}, [x9]
     +0xbe0: usubw2  v16.4s, v18.4s, v0.8h
     +0xbe4: uxtl2   v0.8h, v6.16b
     +0xbe8: usubw2  v17.4s, v18.4s, v1.8h
     +0xbec: uxtl2   v1.8h, v4.16b
     +0xbf0: and     v4.16b, v5.16b, v19.16b
     +0xbf4: ushr    v5.16b, v5.16b, #4
     +0xbf8: mov     w9, #0x1020
     +0xbfc: add     x9, x8, x9
     +0xc00: usubw2  v6.4s, v18.4s, v0.8h
     +0xc04: st2     {v2.4s-v3.4s}, [x25]
     +0xc08: usubw   v2.4s, v18.4s, v0.4h
     +0xc0c: uxtl    v0.8h, v4.8b
     +0xc10: usubw   v3.4s, v18.4s, v1.4h
     +0xc14: usubw2  v7.4s, v18.4s, v1.8h
     +0xc18: uxtl    v1.8h, v5.8b
     +0xc1c: st2     {v16.4s-v17.4s}, [x9]
     +0xc20: mov     w9, #0x1040
     +0xc24: add     x9, x8, x9
     +0xc28: st2     {v2.4s-v3.4s}, [x9]
     +0xc2c: mov     w9, #0x1060
     +0xc30: usubw   v2.4s, v18.4s, v0.4h
     +0xc34: add     x9, x8, x9
     +0xc38: usubw   v3.4s, v18.4s, v1.4h
     +0xc3c: st2     {v6.4s-v7.4s}, [x9]
     +0xc40: mov     w9, #0x1080
     +0xc44: usubw2  v6.4s, v18.4s, v0.8h
     +0xc48: add     x9, x8, x9
     +0xc4c: uxtl2   v0.8h, v4.16b
     +0xc50: usubw2  v7.4s, v18.4s, v1.8h
     +0xc54: uxtl2   v1.8h, v5.16b
     +0xc58: ldp     q4, q5, [x1, #672]
     +0xc5c: st2     {v2.4s-v3.4s}, [x9]
     +0xc60: mov     w9, #0x10a0
     +0xc64: usubw   v2.4s, v18.4s, v0.4h
     +0xc68: add     x9, x8, x9
     +0xc6c: usubw   v3.4s, v18.4s, v1.4h
     +0xc70: usubw2  v16.4s, v18.4s, v0.8h
     +0xc74: usubw2  v17.4s, v18.4s, v1.8h
     +0xc78: st2     {v6.4s-v7.4s}, [x9]
     +0xc7c: and     v6.16b, v4.16b, v19.16b
     +0xc80: ushr    v4.16b, v4.16b, #4
     +0xc84: mov     w9, #0x10c0
     +0xc88: add     x9, x8, x9
     +0xc8c: uxtl    v0.8h, v6.8b
     +0xc90: uxtl    v1.8h, v4.8b
     +0xc94: st2     {v2.4s-v3.4s}, [x9]
     +0xc98: mov     w9, #0x10e0
     +0xc9c: add     x9, x8, x9
     +0xca0: usubw   v2.4s, v18.4s, v0.4h
     +0xca4: usubw   v3.4s, v18.4s, v1.4h
     +0xca8: st2     {v16.4s-v17.4s}, [x9]
     +0xcac: usubw2  v16.4s, v18.4s, v0.8h
     +0xcb0: uxtl2   v0.8h, v6.16b
     +0xcb4: mov     w9, #0x1100
     +0xcb8: usubw2  v17.4s, v18.4s, v1.8h
     +0xcbc: uxtl2   v1.8h, v4.16b
     +0xcc0: and     v4.16b, v5.16b, v19.16b
     +0xcc4: add     x9, x8, x9
     +0xcc8: ushr    v5.16b, v5.16b, #4
     +0xccc: usubw2  v6.4s, v18.4s, v0.8h
     +0xcd0: st2     {v2.4s-v3.4s}, [x9]
     +0xcd4: mov     w9, #0x1120
     +0xcd8: usubw   v2.4s, v18.4s, v0.4h
     +0xcdc: add     x9, x8, x9
     +0xce0: usubw   v3.4s, v18.4s, v1.4h
     +0xce4: uxtl    v0.8h, v4.8b
     +0xce8: usubw2  v7.4s, v18.4s, v1.8h
     +0xcec: uxtl    v1.8h, v5.8b
     +0xcf0: st2     {v16.4s-v17.4s}, [x9]
     +0xcf4: mov     w9, #0x1140
     +0xcf8: add     x9, x8, x9
     +0xcfc: st2     {v2.4s-v3.4s}, [x9]
     +0xd00: mov     w9, #0x1160
     +0xd04: usubw   v2.4s, v18.4s, v0.4h
     +0xd08: add     x9, x8, x9
     +0xd0c: usubw   v3.4s, v18.4s, v1.4h
     +0xd10: st2     {v6.4s-v7.4s}, [x9]
     +0xd14: mov     w9, #0x1180
     +0xd18: usubw2  v6.4s, v18.4s, v0.8h
     +0xd1c: add     x9, x8, x9
     +0xd20: uxtl2   v0.8h, v4.16b
     +0xd24: usubw2  v7.4s, v18.4s, v1.8h
     +0xd28: uxtl2   v1.8h, v5.16b
     +0xd2c: ldp     q4, q5, [x1, #704]
     +0xd30: st2     {v2.4s-v3.4s}, [x9]
     +0xd34: mov     w9, #0x11a0
     +0xd38: usubw   v2.4s, v18.4s, v0.4h
     +0xd3c: add     x9, x8, x9
     +0xd40: usubw   v3.4s, v18.4s, v1.4h
     +0xd44: usubw2  v16.4s, v18.4s, v0.8h
     +0xd48: usubw2  v17.4s, v18.4s, v1.8h
     +0xd4c: st2     {v6.4s-v7.4s}, [x9]
     +0xd50: and     v6.16b, v4.16b, v19.16b
     +0xd54: ushr    v4.16b, v4.16b, #4
     +0xd58: mov     w9, #0x11c0
     +0xd5c: add     x9, x8, x9
     +0xd60: uxtl    v0.8h, v6.8b
     +0xd64: uxtl    v1.8h, v4.8b
     +0xd68: st2     {v2.4s-v3.4s}, [x9]
     +0xd6c: mov     w9, #0x11e0
     +0xd70: add     x9, x8, x9
     +0xd74: usubw   v2.4s, v18.4s, v0.4h
     +0xd78: usubw   v3.4s, v18.4s, v1.4h
     +0xd7c: st2     {v16.4s-v17.4s}, [x9]
     +0xd80: usubw2  v16.4s, v18.4s, v0.8h
     +0xd84: uxtl2   v0.8h, v6.16b
     +0xd88: mov     w9, #0x1200
     +0xd8c: usubw2  v17.4s, v18.4s, v1.8h
     +0xd90: uxtl2   v1.8h, v4.16b
     +0xd94: and     v4.16b, v5.16b, v19.16b
     +0xd98: add     x9, x8, x9
     +0xd9c: ushr    v5.16b, v5.16b, #4
     +0xda0: usubw2  v6.4s, v18.4s, v0.8h
     +0xda4: st2     {v2.4s-v3.4s}, [x9]
     +0xda8: mov     w9, #0x1220
     +0xdac: usubw   v2.4s, v18.4s, v0.4h
     +0xdb0: add     x9, x8, x9
     +0xdb4: usubw   v3.4s, v18.4s, v1.4h
     +0xdb8: uxtl    v0.8h, v4.8b
     +0xdbc: usubw2  v7.4s, v18.4s, v1.8h
     +0xdc0: uxtl    v1.8h, v5.8b
     +0xdc4: st2     {v16.4s-v17.4s}, [x9]
     +0xdc8: mov     w9, #0x1240
     +0xdcc: add     x9, x8, x9
     +0xdd0: st2     {v2.4s-v3.4s}, [x9]
     +0xdd4: mov     w9, #0x1260
     +0xdd8: usubw   v2.4s, v18.4s, v0.4h
     +0xddc: add     x9, x8, x9
     +0xde0: usubw   v3.4s, v18.4s, v1.4h
     +0xde4: st2     {v6.4s-v7.4s}, [x9]
     +0xde8: mov     w9, #0x1280
     +0xdec: usubw2  v6.4s, v18.4s, v0.8h
     +0xdf0: add     x9, x8, x9
     +0xdf4: uxtl2   v0.8h, v4.16b
     +0xdf8: usubw2  v7.4s, v18.4s, v1.8h
     +0xdfc: uxtl2   v1.8h, v5.16b
     +0xe00: ldp     q4, q5, [x1, #736]
     +0xe04: st2     {v2.4s-v3.4s}, [x9]
     +0xe08: mov     w9, #0x12a0
     +0xe0c: usubw   v2.4s, v18.4s, v0.4h
     +0xe10: add     x9, x8, x9
     +0xe14: usubw   v3.4s, v18.4s, v1.4h
     +0xe18: usubw2  v16.4s, v18.4s, v0.8h
     +0xe1c: usubw2  v17.4s, v18.4s, v1.8h
     +0xe20: st2     {v6.4s-v7.4s}, [x9]
     +0xe24: and     v6.16b, v4.16b, v19.16b
     +0xe28: ushr    v4.16b, v4.16b, #4
     +0xe2c: mov     w9, #0x12c0
     +0xe30: add     x9, x8, x9
     +0xe34: uxtl    v0.8h, v6.8b
     +0xe38: uxtl    v1.8h, v4.8b
     +0xe3c: st2     {v2.4s-v3.4s}, [x9]
     +0xe40: mov     w9, #0x12e0
     +0xe44: add     x9, x8, x9
     +0xe48: usubw   v2.4s, v18.4s, v0.4h
     +0xe4c: usubw   v3.4s, v18.4s, v1.4h
     +0xe50: st2     {v16.4s-v17.4s}, [x9]
     +0xe54: usubw2  v16.4s, v18.4s, v0.8h
     +0xe58: uxtl2   v0.8h, v6.16b
     +0xe5c: mov     w9, #0x1300
     +0xe60: usubw2  v17.4s, v18.4s, v1.8h
     +0xe64: uxtl2   v1.8h, v4.16b
     +0xe68: add     x9, x8, x9
     +0xe6c: and     v4.16b, v5.16b, v19.16b
     +0xe70: ushr    v5.16b, v5.16b, #4
     +0xe74: usubw2  v6.4s, v18.4s, v0.8h
     +0xe78: st2     {v2.4s-v3.4s}, [x9]
     +0xe7c: mov     w9, #0x1320
     +0xe80: usubw   v2.4s, v18.4s, v0.4h
     +0xe84: add     x9, x8, x9
     +0xe88: usubw   v3.4s, v18.4s, v1.4h
     +0xe8c: uxtl    v0.8h, v4.8b
     +0xe90: usubw2  v7.4s, v18.4s, v1.8h
     +0xe94: uxtl    v1.8h, v5.8b
     +0xe98: st2     {v16.4s-v17.4s}, [x9]
     +0xe9c: mov     w9, #0x1340
     +0xea0: add     x9, x8, x9
     +0xea4: st2     {v2.4s-v3.4s}, [x9]
     +0xea8: mov     w9, #0x1360
     +0xeac: usubw   v2.4s, v18.4s, v0.4h
     +0xeb0: add     x9, x8, x9
     +0xeb4: usubw   v3.4s, v18.4s, v1.4h
     +0xeb8: st2     {v6.4s-v7.4s}, [x9]
     +0xebc: usubw2  v6.4s, v18.4s, v0.8h
     +0xec0: uxtl2   v0.8h, v4.16b
     +0xec4: mov     w9, #0x1380
     +0xec8: usubw2  v7.4s, v18.4s, v1.8h
     +0xecc: uxtl2   v1.8h, v5.16b
     +0xed0: add     x9, x8, x9
     +0xed4: st2     {v2.4s-v3.4s}, [x9]
     +0xed8: mov     w9, #0x13a0
     +0xedc: usubw   v2.4s, v18.4s, v0.4h
     +0xee0: add     x9, x8, x9
     +0xee4: usubw   v3.4s, v18.4s, v1.4h
     +0xee8: st2     {v6.4s-v7.4s}, [x9]
     +0xeec: mov     w9, #0x13c0
     +0xef0: usubw2  v5.4s, v18.4s, v0.8h
     +0xef4: add     x9, x8, x9
     +0xef8: usubw2  v6.4s, v18.4s, v1.8h
     +0xefc: st2     {v2.4s-v3.4s}, [x9]
     +0xf00: ldp     q2, q3, [x1]
     +0xf04: mov     w9, #0x13e0
     +0xf08: add     x8, x8, x9
     +0xf0c: str     q2, [sp, #8832]
     +0xf10: ldp     q4, q2, [x1, #32]
     +0xf14: str     q3, [sp, #8848]
     +0xf18: st2     {v5.4s-v6.4s}, [x8]
     +0xf1c: str     q4, [sp, #8672]
     +0xf20: ldp     q0, q4, [x1, #64]
     +0xf24: str     q2, [sp, #8688]
     +0xf28: ldp     q2, q3, [x1, #96]
     +0xf2c: mov     w1, #0x5
     +0xf30: str     q4, [sp, #8784]
     +0xf34: str     q3, [sp, #8816]
     +0xf38: str     q2, [sp, #8800]
     +0xf3c: str     q0, [sp, #8768]
     +0xf40: bl      <mldsa65_polyvecl_chknorm>
     +0xf44: movi    v19.16b, #0xf
     +0xf48: ldp     q0, q1, [x20, #768]
     +0xf4c: movi    v7.4s, #0x4
     +0xf50: add     x9, sp, #0x9e0
     +0xf54: movi    v18.4s, #0x4
     +0xf58: mov     x8, xzr
     +0xf5c: mov     w26, wzr
     +0xf60: str     w0, [sp, #20]
     +0xf64: and     v2.16b, v0.16b, v19.16b
     +0xf68: ushr    v0.16b, v0.16b, #4
     +0xf6c: uxtl    v3.8h, v2.8b
     +0xf70: uxtl    v4.8h, v0.8b
     +0xf74: uxtl2   v2.8h, v2.16b
     +0xf78: uxtl2   v0.8h, v0.16b
     +0xf7c: usubw   v5.4s, v7.4s, v3.4h
     +0xf80: usubw2  v16.4s, v7.4s, v3.8h
     +0xf84: usubw   v6.4s, v7.4s, v4.4h
     +0xf88: usubw2  v17.4s, v7.4s, v4.8h
     +0xf8c: usubw   v3.4s, v7.4s, v2.4h
     +0xf90: usubw   v4.4s, v7.4s, v0.4h
     +0xf94: st2     {v5.4s-v6.4s}, [x9], #32
     +0xf98: and     v5.16b, v1.16b, v19.16b
     +0xf9c: ushr    v1.16b, v1.16b, #4
     +0xfa0: usubw2  v6.4s, v18.4s, v2.8h
     +0xfa4: usubw2  v7.4s, v18.4s, v0.8h
     +0xfa8: uxtl    v2.8h, v5.8b
     +0xfac: st2     {v16.4s-v17.4s}, [x9]
     +0xfb0: add     x9, sp, #0x9e0
     +0xfb4: uxtl    v0.8h, v1.8b
     +0xfb8: add     x10, x9, #0x40
     +0xfbc: st2     {v3.4s-v4.4s}, [x10]
     +0xfc0: add     x10, x9, #0x60
     +0xfc4: usubw   v3.4s, v18.4s, v2.4h
     +0xfc8: usubw   v4.4s, v18.4s, v0.4h
     +0xfcc: st2     {v6.4s-v7.4s}, [x10]
     +0xfd0: usubw2  v6.4s, v18.4s, v2.8h
     +0xfd4: uxtl2   v2.8h, v5.16b
     +0xfd8: usubw2  v7.4s, v18.4s, v0.8h
     +0xfdc: uxtl2   v0.8h, v1.16b
     +0xfe0: add     x10, x9, #0x80
     +0xfe4: ldp     q1, q5, [x20, #800]
     +0xfe8: usubw2  v16.4s, v18.4s, v2.8h
     +0xfec: st2     {v3.4s-v4.4s}, [x10]
     +0xff0: add     x10, x9, #0xa0
     +0xff4: usubw   v3.4s, v18.4s, v2.4h
     +0xff8: usubw   v4.4s, v18.4s, v0.4h
     +0xffc: usubw2  v17.4s, v18.4s, v0.8h
    +0x1000: st2     {v6.4s-v7.4s}, [x10]
    +0x1004: and     v6.16b, v1.16b, v19.16b
    +0x1008: ushr    v1.16b, v1.16b, #4
    +0x100c: add     x10, x9, #0xc0
    +0x1010: uxtl    v0.8h, v6.8b
    +0x1014: uxtl    v2.8h, v1.8b
    +0x1018: uxtl2   v1.8h, v1.16b
    +0x101c: st2     {v3.4s-v4.4s}, [x10]
    +0x1020: add     x10, x9, #0xe0
    +0x1024: usubw   v3.4s, v18.4s, v0.4h
    +0x1028: usubw   v4.4s, v18.4s, v2.4h
    +0x102c: st2     {v16.4s-v17.4s}, [x10]
    +0x1030: add     x10, x9, #0x100
    +0x1034: usubw2  v16.4s, v18.4s, v0.8h
    +0x1038: uxtl2   v0.8h, v6.16b
    +0x103c: usubw2  v17.4s, v18.4s, v2.8h
    +0x1040: st2     {v3.4s-v4.4s}, [x10]
    +0x1044: and     v4.16b, v5.16b, v19.16b
    +0x1048: ushr    v5.16b, v5.16b, #4
    +0x104c: usubw   v2.4s, v18.4s, v0.4h
    +0x1050: usubw2  v6.4s, v18.4s, v0.8h
    +0x1054: add     x10, x9, #0x120
    +0x1058: usubw   v3.4s, v18.4s, v1.4h
    +0x105c: usubw2  v7.4s, v18.4s, v1.8h
    +0x1060: uxtl    v0.8h, v4.8b
    +0x1064: uxtl    v1.8h, v5.8b
    +0x1068: st2     {v16.4s-v17.4s}, [x10]
    +0x106c: add     x10, x9, #0x140
    +0x1070: st2     {v2.4s-v3.4s}, [x10]
    +0x1074: add     x10, x9, #0x160
    +0x1078: usubw   v2.4s, v18.4s, v0.4h
    +0x107c: usubw   v3.4s, v18.4s, v1.4h
    +0x1080: st2     {v6.4s-v7.4s}, [x10]
    +0x1084: usubw2  v6.4s, v18.4s, v0.8h
    +0x1088: uxtl2   v0.8h, v4.16b
    +0x108c: usubw2  v7.4s, v18.4s, v1.8h
    +0x1090: uxtl2   v1.8h, v5.16b
    +0x1094: add     x10, x9, #0x180
    +0x1098: ldp     q4, q5, [x20, #832]
    +0x109c: usubw2  v16.4s, v18.4s, v0.8h
    +0x10a0: st2     {v2.4s-v3.4s}, [x10]
    +0x10a4: add     x10, x9, #0x1a0
    +0x10a8: usubw   v2.4s, v18.4s, v0.4h
    +0x10ac: usubw   v3.4s, v18.4s, v1.4h
    +0x10b0: usubw2  v17.4s, v18.4s, v1.8h
    +0x10b4: st2     {v6.4s-v7.4s}, [x10]
    +0x10b8: and     v6.16b, v4.16b, v19.16b
    +0x10bc: ushr    v4.16b, v4.16b, #4
    +0x10c0: add     x10, x9, #0x1c0
    +0x10c4: uxtl    v0.8h, v6.8b
    +0x10c8: uxtl    v1.8h, v4.8b
    +0x10cc: st2     {v2.4s-v3.4s}, [x10]
    +0x10d0: add     x10, x9, #0x1e0
    +0x10d4: usubw   v2.4s, v18.4s, v0.4h
    +0x10d8: usubw   v3.4s, v18.4s, v1.4h
    +0x10dc: st2     {v16.4s-v17.4s}, [x10]
    +0x10e0: usubw2  v16.4s, v18.4s, v0.8h
    +0x10e4: uxtl2   v0.8h, v6.16b
    +0x10e8: usubw2  v17.4s, v18.4s, v1.8h
    +0x10ec: uxtl2   v1.8h, v4.16b
    +0x10f0: and     v4.16b, v5.16b, v19.16b
    +0x10f4: add     x10, x9, #0x200
    +0x10f8: ushr    v5.16b, v5.16b, #4
    +0x10fc: usubw2  v6.4s, v18.4s, v0.8h
    +0x1100: st2     {v2.4s-v3.4s}, [x10]
    +0x1104: usubw   v2.4s, v18.4s, v0.4h
    +0x1108: uxtl    v0.8h, v4.8b
    +0x110c: usubw   v3.4s, v18.4s, v1.4h
    +0x1110: add     x10, x9, #0x220
    +0x1114: usubw2  v7.4s, v18.4s, v1.8h
    +0x1118: uxtl    v1.8h, v5.8b
    +0x111c: st2     {v16.4s-v17.4s}, [x10]
    +0x1120: add     x10, x9, #0x240
    +0x1124: st2     {v2.4s-v3.4s}, [x10]
    +0x1128: add     x10, x9, #0x260
    +0x112c: usubw   v2.4s, v18.4s, v0.4h
    +0x1130: usubw   v3.4s, v18.4s, v1.4h
    +0x1134: st2     {v6.4s-v7.4s}, [x10]
    +0x1138: usubw2  v6.4s, v18.4s, v0.8h
    +0x113c: uxtl2   v0.8h, v4.16b
    +0x1140: usubw2  v7.4s, v18.4s, v1.8h
    +0x1144: uxtl2   v1.8h, v5.16b
    +0x1148: add     x10, x9, #0x280
    +0x114c: ldp     q4, q5, [x20, #864]
    +0x1150: usubw2  v16.4s, v18.4s, v0.8h
    +0x1154: st2     {v2.4s-v3.4s}, [x10]
    +0x1158: add     x10, x9, #0x2a0
    +0x115c: usubw   v2.4s, v18.4s, v0.4h
    +0x1160: usubw   v3.4s, v18.4s, v1.4h
    +0x1164: usubw2  v17.4s, v18.4s, v1.8h
    +0x1168: st2     {v6.4s-v7.4s}, [x10]
    +0x116c: and     v6.16b, v4.16b, v19.16b
    +0x1170: ushr    v4.16b, v4.16b, #4
    +0x1174: add     x10, x9, #0x2c0
    +0x1178: uxtl    v0.8h, v6.8b
    +0x117c: uxtl    v1.8h, v4.8b
    +0x1180: st2     {v2.4s-v3.4s}, [x10]
    +0x1184: add     x10, x9, #0x2e0
    +0x1188: usubw   v2.4s, v18.4s, v0.4h
    +0x118c: usubw   v3.4s, v18.4s, v1.4h
    +0x1190: st2     {v16.4s-v17.4s}, [x10]
    +0x1194: usubw2  v16.4s, v18.4s, v0.8h
    +0x1198: uxtl2   v0.8h, v6.16b
    +0x119c: usubw2  v17.4s, v18.4s, v1.8h
    +0x11a0: uxtl2   v1.8h, v4.16b
    +0x11a4: and     v4.16b, v5.16b, v19.16b
    +0x11a8: add     x10, x9, #0x300
    +0x11ac: ushr    v5.16b, v5.16b, #4
    +0x11b0: usubw2  v6.4s, v18.4s, v0.8h
    +0x11b4: st2     {v2.4s-v3.4s}, [x10]
    +0x11b8: usubw   v2.4s, v18.4s, v0.4h
    +0x11bc: uxtl    v0.8h, v4.8b
    +0x11c0: usubw   v3.4s, v18.4s, v1.4h
    +0x11c4: add     x10, x9, #0x320
    +0x11c8: usubw2  v7.4s, v18.4s, v1.8h
    +0x11cc: uxtl    v1.8h, v5.8b
    +0x11d0: st2     {v16.4s-v17.4s}, [x10]
    +0x11d4: add     x10, x9, #0x340
    +0x11d8: st2     {v2.4s-v3.4s}, [x10]
    +0x11dc: add     x10, x9, #0x360
    +0x11e0: usubw   v2.4s, v18.4s, v0.4h
    +0x11e4: usubw   v3.4s, v18.4s, v1.4h
    +0x11e8: st2     {v6.4s-v7.4s}, [x10]
    +0x11ec: usubw2  v6.4s, v18.4s, v0.8h
    +0x11f0: uxtl2   v0.8h, v4.16b
    +0x11f4: usubw2  v7.4s, v18.4s, v1.8h
    +0x11f8: uxtl2   v1.8h, v5.16b
    +0x11fc: add     x10, x9, #0x380
    +0x1200: usubw2  v4.4s, v18.4s, v0.8h
    +0x1204: st2     {v2.4s-v3.4s}, [x10]
    +0x1208: usubw   v2.4s, v18.4s, v0.4h
    +0x120c: add     x10, x9, #0x3a0
    +0x1210: usubw   v3.4s, v18.4s, v1.4h
    +0x1214: usubw2  v5.4s, v18.4s, v1.8h
    +0x1218: st2     {v6.4s-v7.4s}, [x10]
    +0x121c: add     x10, x9, #0x3c0
    +0x1220: st2     {v2.4s-v3.4s}, [x10]
    +0x1224: add     x10, x9, #0x3e0
    +0x1228: st2     {v4.4s-v5.4s}, [x10]
    +0x122c: mov     w10, #0x4
    +0x1230: ldrsw   x11, [x9, x8]
    +0x1234: add     x8, x8, #0x4
    +0x1238: cmp     x8, #0x400
    +0x123c: mov     w12, w11
    +0x1240: lsr     x11, x11, #31
    +0x1244: neg     w13, w12
    +0x1248: bic     w12, w12, w11
    +0x124c: and     w11, w13, w11
    +0x1250: orr     w11, w11, w12
    +0x1254: sub     w11, w10, w11
    +0x1258: sxtw    x11, w11
    +0x125c: lsr     x11, x11, #31
    +0x1260: orr     w26, w26, w11
    +0x1264: b.ne    <mldsa65_pk_from_sk+0x1230>
    +0x1268: movi    v1.16b, #0xf
    +0x126c: ldp     q0, q2, [x20, #896]
    +0x1270: add     x9, sp, #0x9e0
    +0x1274: mov     x8, xzr
    +0x1278: mov     w28, wzr
    +0x127c: ushr    v4.16b, v0.16b, #4
    +0x1280: and     v3.16b, v0.16b, v1.16b
    +0x1284: movi    v0.4s, #0x4
    +0x1288: and     v7.16b, v2.16b, v1.16b
    +0x128c: ushr    v2.16b, v2.16b, #4
    +0x1290: uxtl    v6.8h, v4.8b
    +0x1294: uxtl2   v4.8h, v4.16b
    +0x1298: uxtl    v5.8h, v3.8b
    +0x129c: uxtl2   v3.8h, v3.16b
    +0x12a0: usubw   v16.4s, v0.4s, v5.4h
    +0x12a4: usubw2  v18.4s, v0.4s, v5.8h
    +0x12a8: usubw   v17.4s, v0.4s, v6.4h
    +0x12ac: usubw2  v19.4s, v0.4s, v6.8h
    +0x12b0: usubw   v5.4s, v0.4s, v3.4h
    +0x12b4: usubw   v6.4s, v0.4s, v4.4h
    +0x12b8: st2     {v16.4s-v17.4s}, [x9], #32
    +0x12bc: usubw2  v16.4s, v0.4s, v3.8h
    +0x12c0: uxtl    v3.8h, v7.8b
    +0x12c4: usubw2  v17.4s, v0.4s, v4.8h
    +0x12c8: uxtl    v4.8h, v2.8b
    +0x12cc: uxtl2   v2.8h, v2.16b
    +0x12d0: st2     {v18.4s-v19.4s}, [x9]
    +0x12d4: add     x9, sp, #0x9e0
    +0x12d8: add     x10, x9, #0x40
    +0x12dc: st2     {v5.4s-v6.4s}, [x10]
    +0x12e0: usubw   v5.4s, v0.4s, v3.4h
    +0x12e4: add     x10, x9, #0x60
    +0x12e8: usubw   v6.4s, v0.4s, v4.4h
    +0x12ec: st2     {v16.4s-v17.4s}, [x10]
    +0x12f0: add     x10, x9, #0x80
    +0x12f4: usubw2  v16.4s, v0.4s, v3.8h
    +0x12f8: uxtl2   v3.8h, v7.16b
    +0x12fc: usubw2  v17.4s, v0.4s, v4.8h
    +0x1300: st2     {v5.4s-v6.4s}, [x10]
    +0x1304: ldp     q6, q7, [x20, #928]
    +0x1308: add     x10, x9, #0xa0
    +0x130c: usubw   v4.4s, v0.4s, v3.4h
    +0x1310: usubw   v5.4s, v0.4s, v2.4h
    +0x1314: st2     {v16.4s-v17.4s}, [x10]
    +0x1318: and     v16.16b, v6.16b, v1.16b
    +0x131c: ushr    v6.16b, v6.16b, #4
    +0x1320: usubw2  v17.4s, v0.4s, v3.8h
    +0x1324: add     x10, x9, #0xc0
    +0x1328: usubw2  v18.4s, v0.4s, v2.8h
    +0x132c: uxtl    v2.8h, v16.8b
    +0x1330: uxtl    v3.8h, v6.8b
    +0x1334: st2     {v4.4s-v5.4s}, [x10]
    +0x1338: add     x10, x9, #0xe0
    +0x133c: usubw   v4.4s, v0.4s, v2.4h
    +0x1340: usubw   v5.4s, v0.4s, v3.4h
    +0x1344: st2     {v17.4s-v18.4s}, [x10]
    +0x1348: usubw2  v17.4s, v0.4s, v2.8h
    +0x134c: uxtl2   v2.8h, v16.16b
    +0x1350: usubw2  v18.4s, v0.4s, v3.8h
    +0x1354: uxtl2   v3.8h, v6.16b
    +0x1358: and     v6.16b, v7.16b, v1.16b
    +0x135c: add     x10, x9, #0x100
    +0x1360: ushr    v7.16b, v7.16b, #4
    +0x1364: st2     {v4.4s-v5.4s}, [x10]
    +0x1368: add     x10, x9, #0x120
    +0x136c: usubw   v4.4s, v0.4s, v2.4h
    +0x1370: usubw   v5.4s, v0.4s, v3.4h
    +0x1374: st2     {v17.4s-v18.4s}, [x10]
    +0x1378: usubw2  v16.4s, v0.4s, v2.8h
    +0x137c: uxtl    v2.8h, v6.8b
    +0x1380: usubw2  v17.4s, v0.4s, v3.8h
    +0x1384: uxtl    v3.8h, v7.8b
    +0x1388: add     x10, x9, #0x140
    +0x138c: st2     {v4.4s-v5.4s}, [x10]
    +0x1390: add     x10, x9, #0x160
    +0x1394: usubw   v4.4s, v0.4s, v2.4h
    +0x1398: usubw   v5.4s, v0.4s, v3.4h
    +0x139c: st2     {v16.4s-v17.4s}, [x10]
    +0x13a0: usubw2  v16.4s, v0.4s, v2.8h
    +0x13a4: uxtl2   v2.8h, v6.16b
    +0x13a8: usubw2  v17.4s, v0.4s, v3.8h
    +0x13ac: uxtl2   v3.8h, v7.16b
    +0x13b0: add     x10, x9, #0x180
    +0x13b4: ldp     q6, q7, [x20, #960]
    +0x13b8: st2     {v4.4s-v5.4s}, [x10]
    +0x13bc: add     x10, x9, #0x1a0
    +0x13c0: usubw   v4.4s, v0.4s, v2.4h
    +0x13c4: usubw   v5.4s, v0.4s, v3.4h
    +0x13c8: st2     {v16.4s-v17.4s}, [x10]
    +0x13cc: and     v16.16b, v6.16b, v1.16b
    +0x13d0: ushr    v6.16b, v6.16b, #4
    +0x13d4: usubw2  v17.4s, v0.4s, v2.8h
    +0x13d8: add     x10, x9, #0x1c0
    +0x13dc: usubw2  v18.4s, v0.4s, v3.8h
    +0x13e0: uxtl    v2.8h, v16.8b
    +0x13e4: uxtl    v3.8h, v6.8b
    +0x13e8: st2     {v4.4s-v5.4s}, [x10]
    +0x13ec: add     x10, x9, #0x1e0
    +0x13f0: usubw   v4.4s, v0.4s, v2.4h
    +0x13f4: usubw   v5.4s, v0.4s, v3.4h
    +0x13f8: st2     {v17.4s-v18.4s}, [x10]
    +0x13fc: usubw2  v17.4s, v0.4s, v2.8h
    +0x1400: uxtl2   v2.8h, v16.16b
    +0x1404: usubw2  v18.4s, v0.4s, v3.8h
    +0x1408: uxtl2   v3.8h, v6.16b
    +0x140c: and     v6.16b, v7.16b, v1.16b
    +0x1410: add     x10, x9, #0x200
    +0x1414: ushr    v7.16b, v7.16b, #4
    +0x1418: st2     {v4.4s-v5.4s}, [x10]
    +0x141c: add     x10, x9, #0x220
    +0x1420: usubw   v4.4s, v0.4s, v2.4h
    +0x1424: usubw   v5.4s, v0.4s, v3.4h
    +0x1428: st2     {v17.4s-v18.4s}, [x10]
    +0x142c: usubw2  v16.4s, v0.4s, v2.8h
    +0x1430: uxtl    v2.8h, v6.8b
    +0x1434: usubw2  v17.4s, v0.4s, v3.8h
    +0x1438: uxtl    v3.8h, v7.8b
    +0x143c: add     x10, x9, #0x240
    +0x1440: st2     {v4.4s-v5.4s}, [x10]
    +0x1444: add     x10, x9, #0x260
    +0x1448: usubw   v4.4s, v0.4s, v2.4h
    +0x144c: usubw   v5.4s, v0.4s, v3.4h
    +0x1450: st2     {v16.4s-v17.4s}, [x10]
    +0x1454: usubw2  v16.4s, v0.4s, v2.8h
    +0x1458: uxtl2   v2.8h, v6.16b
    +0x145c: usubw2  v17.4s, v0.4s, v3.8h
    +0x1460: uxtl2   v3.8h, v7.16b
    +0x1464: add     x10, x9, #0x280
    +0x1468: ldp     q6, q7, [x20, #992]
    +0x146c: st2     {v4.4s-v5.4s}, [x10]
    +0x1470: add     x10, x9, #0x2a0
    +0x1474: usubw   v4.4s, v0.4s, v2.4h
    +0x1478: usubw   v5.4s, v0.4s, v3.4h
    +0x147c: st2     {v16.4s-v17.4s}, [x10]
    +0x1480: and     v16.16b, v6.16b, v1.16b
    +0x1484: ushr    v6.16b, v6.16b, #4
    +0x1488: usubw2  v17.4s, v0.4s, v2.8h
    +0x148c: add     x10, x9, #0x2c0
    +0x1490: and     v1.16b, v7.16b, v1.16b
    +0x1494: usubw2  v18.4s, v0.4s, v3.8h
    +0x1498: uxtl    v2.8h, v16.8b
    +0x149c: uxtl    v3.8h, v6.8b
    +0x14a0: st2     {v4.4s-v5.4s}, [x10]
    +0x14a4: add     x10, x9, #0x2e0
    +0x14a8: usubw   v4.4s, v0.4s, v2.4h
    +0x14ac: usubw   v5.4s, v0.4s, v3.4h
    +0x14b0: st2     {v17.4s-v18.4s}, [x10]
    +0x14b4: usubw2  v17.4s, v0.4s, v2.8h
    +0x14b8: uxtl2   v2.8h, v16.16b
    +0x14bc: usubw2  v18.4s, v0.4s, v3.8h
    +0x14c0: uxtl2   v3.8h, v6.16b
    +0x14c4: add     x10, x9, #0x300
    +0x14c8: ushr    v6.16b, v7.16b, #4
    +0x14cc: st2     {v4.4s-v5.4s}, [x10]
    +0x14d0: add     x10, x9, #0x320
    +0x14d4: usubw   v4.4s, v0.4s, v2.4h
    +0x14d8: usubw   v5.4s, v0.4s, v3.4h
    +0x14dc: st2     {v17.4s-v18.4s}, [x10]
    +0x14e0: usubw2  v16.4s, v0.4s, v2.8h
    +0x14e4: uxtl    v2.8h, v1.8b
    +0x14e8: usubw2  v17.4s, v0.4s, v3.8h
    +0x14ec: uxtl    v3.8h, v6.8b
    +0x14f0: add     x10, x9, #0x340
    +0x14f4: uxtl2   v1.8h, v1.16b
    +0x14f8: st2     {v4.4s-v5.4s}, [x10]
    +0x14fc: usubw   v4.4s, v0.4s, v2.4h
    +0x1500: add     x10, x9, #0x360
    +0x1504: usubw   v5.4s, v0.4s, v3.4h
    +0x1508: st2     {v16.4s-v17.4s}, [x10]
    +0x150c: usubw2  v16.4s, v0.4s, v2.8h
    +0x1510: uxtl2   v2.8h, v6.16b
    +0x1514: add     x10, x9, #0x380
    +0x1518: usubw2  v17.4s, v0.4s, v3.8h
    +0x151c: st2     {v4.4s-v5.4s}, [x10]
    +0x1520: usubw   v3.4s, v0.4s, v1.4h
    +0x1524: usubw2  v5.4s, v0.4s, v1.8h
    +0x1528: usubw   v4.4s, v0.4s, v2.4h
    +0x152c: add     x10, x9, #0x3a0
    +0x1530: usubw2  v6.4s, v0.4s, v2.8h
    +0x1534: st2     {v16.4s-v17.4s}, [x10]
    +0x1538: add     x10, x9, #0x3c0
    +0x153c: st2     {v3.4s-v4.4s}, [x10]
    +0x1540: add     x10, x9, #0x3e0
    +0x1544: st2     {v5.4s-v6.4s}, [x10]
    +0x1548: mov     w10, #0x4
    +0x154c: ldrsw   x11, [x9, x8]
    +0x1550: add     x8, x8, #0x4
    +0x1554: cmp     x8, #0x400
    +0x1558: mov     w12, w11
    +0x155c: lsr     x11, x11, #31
    +0x1560: neg     w13, w12
    +0x1564: bic     w12, w12, w11
    +0x1568: and     w11, w13, w11
    +0x156c: orr     w11, w11, w12
    +0x1570: sub     w11, w10, w11
    +0x1574: sxtw    x11, w11
    +0x1578: lsr     x11, x11, #31
    +0x157c: orr     w28, w28, w11
    +0x1580: b.ne    <mldsa65_pk_from_sk+0x154c>
    +0x1584: movi    v1.16b, #0xf
    +0x1588: ldr     q0, [x20, #1024]
    +0x158c: add     x9, sp, #0x9e0
    +0x1590: mov     x8, xzr
    +0x1594: mov     w22, wzr
    +0x1598: ushr    v3.16b, v0.16b, #4
    +0x159c: and     v2.16b, v0.16b, v1.16b
    +0x15a0: movi    v0.4s, #0x4
    +0x15a4: uxtl    v5.8h, v3.8b
    +0x15a8: uxtl2   v3.8h, v3.16b
    +0x15ac: uxtl    v4.8h, v2.8b
    +0x15b0: uxtl2   v2.8h, v2.16b
    +0x15b4: usubw   v6.4s, v0.4s, v4.4h
    +0x15b8: usubw2  v16.4s, v0.4s, v4.8h
    +0x15bc: ldr     q4, [x20, #1040]
    +0x15c0: usubw   v7.4s, v0.4s, v5.4h
    +0x15c4: usubw2  v17.4s, v0.4s, v5.8h
    +0x15c8: st2     {v6.4s-v7.4s}, [x9], #32
    +0x15cc: and     v7.16b, v4.16b, v1.16b
    +0x15d0: ushr    v4.16b, v4.16b, #4
    +0x15d4: usubw   v5.4s, v0.4s, v2.4h
    +0x15d8: usubw   v6.4s, v0.4s, v3.4h
    +0x15dc: st2     {v16.4s-v17.4s}, [x9]
    +0x15e0: usubw2  v16.4s, v0.4s, v2.8h
    +0x15e4: uxtl    v2.8h, v7.8b
    +0x15e8: add     x9, sp, #0x9e0
    +0x15ec: usubw2  v17.4s, v0.4s, v3.8h
    +0x15f0: uxtl    v3.8h, v4.8b
    +0x15f4: add     x10, x9, #0x40
    +0x15f8: st2     {v5.4s-v6.4s}, [x10]
    +0x15fc: usubw   v5.4s, v0.4s, v2.4h
    +0x1600: add     x10, x9, #0x60
    +0x1604: usubw   v6.4s, v0.4s, v3.4h
    +0x1608: st2     {v16.4s-v17.4s}, [x10]
    +0x160c: add     x10, x9, #0x80
    +0x1610: usubw2  v16.4s, v0.4s, v2.8h
    +0x1614: uxtl2   v2.8h, v7.16b
    +0x1618: usubw2  v17.4s, v0.4s, v3.8h
    +0x161c: uxtl2   v3.8h, v4.16b
    +0x1620: st2     {v5.4s-v6.4s}, [x10]
    +0x1624: ldr     q6, [x20, #1056]
    +0x1628: add     x10, x9, #0xa0
    +0x162c: usubw   v4.4s, v0.4s, v2.4h
    +0x1630: and     v7.16b, v6.16b, v1.16b
    +0x1634: ushr    v6.16b, v6.16b, #4
    +0x1638: usubw   v5.4s, v0.4s, v3.4h
    +0x163c: st2     {v16.4s-v17.4s}, [x10]
    +0x1640: usubw2  v16.4s, v0.4s, v2.8h
    +0x1644: add     x10, x9, #0xc0
    +0x1648: usubw2  v17.4s, v0.4s, v3.8h
    +0x164c: uxtl    v2.8h, v7.8b
    +0x1650: uxtl    v3.8h, v6.8b
    +0x1654: st2     {v4.4s-v5.4s}, [x10]
    +0x1658: add     x10, x9, #0xe0
    +0x165c: usubw   v4.4s, v0.4s, v2.4h
    +0x1660: usubw   v5.4s, v0.4s, v3.4h
    +0x1664: st2     {v16.4s-v17.4s}, [x10]
    +0x1668: usubw2  v16.4s, v0.4s, v2.8h
    +0x166c: uxtl2   v2.8h, v7.16b
    +0x1670: usubw2  v17.4s, v0.4s, v3.8h
    +0x1674: uxtl2   v3.8h, v6.16b
    +0x1678: ldr     q6, [x20, #1072]
    +0x167c: add     x10, x9, #0x100
    +0x1680: and     v7.16b, v6.16b, v1.16b
    +0x1684: ushr    v6.16b, v6.16b, #4
    +0x1688: st2     {v4.4s-v5.4s}, [x10]
    +0x168c: add     x10, x9, #0x120
    +0x1690: usubw   v4.4s, v0.4s, v2.4h
    +0x1694: usubw   v5.4s, v0.4s, v3.4h
    +0x1698: st2     {v16.4s-v17.4s}, [x10]
    +0x169c: usubw2  v16.4s, v0.4s, v2.8h
    +0x16a0: uxtl    v2.8h, v7.8b
    +0x16a4: usubw2  v17.4s, v0.4s, v3.8h
    +0x16a8: add     x10, x9, #0x140
    +0x16ac: uxtl    v3.8h, v6.8b
    +0x16b0: st2     {v4.4s-v5.4s}, [x10]
    +0x16b4: add     x10, x9, #0x160
    +0x16b8: usubw   v4.4s, v0.4s, v2.4h
    +0x16bc: usubw   v5.4s, v0.4s, v3.4h
    +0x16c0: st2     {v16.4s-v17.4s}, [x10]
    +0x16c4: usubw2  v16.4s, v0.4s, v2.8h
    +0x16c8: uxtl2   v2.8h, v7.16b
    +0x16cc: usubw2  v17.4s, v0.4s, v3.8h
    +0x16d0: uxtl2   v3.8h, v6.16b
    +0x16d4: ldr     q6, [x20, #1088]
    +0x16d8: add     x10, x9, #0x180
    +0x16dc: and     v7.16b, v6.16b, v1.16b
    +0x16e0: ushr    v6.16b, v6.16b, #4
    +0x16e4: st2     {v4.4s-v5.4s}, [x10]
    +0x16e8: add     x10, x9, #0x1a0
    +0x16ec: usubw   v4.4s, v0.4s, v2.4h
    +0x16f0: usubw   v5.4s, v0.4s, v3.4h
    +0x16f4: st2     {v16.4s-v17.4s}, [x10]
    +0x16f8: usubw2  v16.4s, v0.4s, v2.8h
    +0x16fc: uxtl    v2.8h, v7.8b
    +0x1700: usubw2  v17.4s, v0.4s, v3.8h
    +0x1704: add     x10, x9, #0x1c0
    +0x1708: uxtl    v3.8h, v6.8b
    +0x170c: st2     {v4.4s-v5.4s}, [x10]
    +0x1710: add     x10, x9, #0x1e0
    +0x1714: usubw   v4.4s, v0.4s, v2.4h
    +0x1718: usubw   v5.4s, v0.4s, v3.4h
    +0x171c: st2     {v16.4s-v17.4s}, [x10]
    +0x1720: usubw2  v16.4s, v0.4s, v2.8h
    +0x1724: uxtl2   v2.8h, v7.16b
    +0x1728: usubw2  v17.4s, v0.4s, v3.8h
    +0x172c: uxtl2   v3.8h, v6.16b
    +0x1730: ldr     q6, [x20, #1104]
    +0x1734: add     x10, x9, #0x200
    +0x1738: and     v7.16b, v6.16b, v1.16b
    +0x173c: ushr    v6.16b, v6.16b, #4
    +0x1740: st2     {v4.4s-v5.4s}, [x10]
    +0x1744: add     x10, x9, #0x220
    +0x1748: usubw   v4.4s, v0.4s, v2.4h
    +0x174c: usubw   v5.4s, v0.4s, v3.4h
    +0x1750: st2     {v16.4s-v17.4s}, [x10]
    +0x1754: usubw2  v16.4s, v0.4s, v2.8h
    +0x1758: uxtl    v2.8h, v7.8b
    +0x175c: usubw2  v17.4s, v0.4s, v3.8h
    +0x1760: add     x10, x9, #0x240
    +0x1764: uxtl    v3.8h, v6.8b
    +0x1768: st2     {v4.4s-v5.4s}, [x10]
    +0x176c: add     x10, x9, #0x260
    +0x1770: usubw   v4.4s, v0.4s, v2.4h
    +0x1774: usubw   v5.4s, v0.4s, v3.4h
    +0x1778: st2     {v16.4s-v17.4s}, [x10]
    +0x177c: usubw2  v16.4s, v0.4s, v2.8h
    +0x1780: uxtl2   v2.8h, v7.16b
    +0x1784: usubw2  v17.4s, v0.4s, v3.8h
    +0x1788: uxtl2   v3.8h, v6.16b
    +0x178c: ldr     q6, [x20, #1120]
    +0x1790: add     x10, x9, #0x280
    +0x1794: and     v7.16b, v6.16b, v1.16b
    +0x1798: ushr    v6.16b, v6.16b, #4
    +0x179c: st2     {v4.4s-v5.4s}, [x10]
    +0x17a0: add     x10, x9, #0x2a0
    +0x17a4: usubw   v4.4s, v0.4s, v2.4h
    +0x17a8: usubw   v5.4s, v0.4s, v3.4h
    +0x17ac: st2     {v16.4s-v17.4s}, [x10]
    +0x17b0: usubw2  v16.4s, v0.4s, v2.8h
    +0x17b4: uxtl    v2.8h, v7.8b
    +0x17b8: usubw2  v17.4s, v0.4s, v3.8h
    +0x17bc: add     x10, x9, #0x2c0
    +0x17c0: uxtl    v3.8h, v6.8b
    +0x17c4: st2     {v4.4s-v5.4s}, [x10]
    +0x17c8: add     x10, x9, #0x2e0
    +0x17cc: usubw   v4.4s, v0.4s, v2.4h
    +0x17d0: usubw   v5.4s, v0.4s, v3.4h
    +0x17d4: st2     {v16.4s-v17.4s}, [x10]
    +0x17d8: usubw2  v16.4s, v0.4s, v2.8h
    +0x17dc: uxtl2   v2.8h, v7.16b
    +0x17e0: usubw2  v17.4s, v0.4s, v3.8h
    +0x17e4: uxtl2   v3.8h, v6.16b
    +0x17e8: ldr     q6, [x20, #1136]
    +0x17ec: add     x10, x9, #0x300
    +0x17f0: and     v1.16b, v6.16b, v1.16b
    +0x17f4: ushr    v6.16b, v6.16b, #4
    +0x17f8: st2     {v4.4s-v5.4s}, [x10]
    +0x17fc: add     x10, x9, #0x320
    +0x1800: usubw   v4.4s, v0.4s, v2.4h
    +0x1804: usubw   v5.4s, v0.4s, v3.4h
    +0x1808: st2     {v16.4s-v17.4s}, [x10]
    +0x180c: usubw2  v16.4s, v0.4s, v2.8h
    +0x1810: uxtl    v2.8h, v1.8b
    +0x1814: usubw2  v17.4s, v0.4s, v3.8h
    +0x1818: uxtl    v3.8h, v6.8b
    +0x181c: add     x10, x9, #0x340
    +0x1820: uxtl2   v1.8h, v1.16b
    +0x1824: st2     {v4.4s-v5.4s}, [x10]
    +0x1828: usubw   v4.4s, v0.4s, v2.4h
    +0x182c: add     x10, x9, #0x360
    +0x1830: usubw   v5.4s, v0.4s, v3.4h
    +0x1834: st2     {v16.4s-v17.4s}, [x10]
    +0x1838: usubw2  v16.4s, v0.4s, v2.8h
    +0x183c: uxtl2   v2.8h, v6.16b
    +0x1840: add     x10, x9, #0x380
    +0x1844: usubw2  v17.4s, v0.4s, v3.8h
    +0x1848: st2     {v4.4s-v5.4s}, [x10]
    +0x184c: usubw   v3.4s, v0.4s, v1.4h
    +0x1850: usubw2  v5.4s, v0.4s, v1.8h
    +0x1854: usubw   v4.4s, v0.4s, v2.4h
    +0x1858: add     x10, x9, #0x3a0
    +0x185c: usubw2  v6.4s, v0.4s, v2.8h
    +0x1860: st2     {v16.4s-v17.4s}, [x10]
    +0x1864: add     x10, x9, #0x3c0
    +0x1868: st2     {v3.4s-v4.4s}, [x10]
    +0x186c: add     x10, x9, #0x3e0
    +0x1870: st2     {v5.4s-v6.4s}, [x10]
    +0x1874: mov     w10, #0x4
    +0x1878: ldrsw   x11, [x9, x8]
    +0x187c: add     x8, x8, #0x4
    +0x1880: cmp     x8, #0x400
    +0x1884: mov     w12, w11
    +0x1888: lsr     x11, x11, #31
    +0x188c: neg     w13, w12
    +0x1890: bic     w12, w12, w11
    +0x1894: and     w11, w13, w11
    +0x1898: orr     w11, w11, w12
    +0x189c: sub     w11, w10, w11
    +0x18a0: sxtw    x11, w11
    +0x18a4: lsr     x11, x11, #31
    +0x18a8: orr     w22, w22, w11
    +0x18ac: b.ne    <mldsa65_pk_from_sk+0x1878>
    +0x18b0: movi    v1.16b, #0xf
    +0x18b4: ldr     q0, [x20, #1152]
    +0x18b8: add     x9, sp, #0x9e0
    +0x18bc: mov     x8, xzr
    +0x18c0: mov     w21, wzr
    +0x18c4: ushr    v3.16b, v0.16b, #4
    +0x18c8: and     v2.16b, v0.16b, v1.16b
    +0x18cc: movi    v0.4s, #0x4
    +0x18d0: uxtl    v5.8h, v3.8b
    +0x18d4: uxtl2   v3.8h, v3.16b
    +0x18d8: uxtl    v4.8h, v2.8b
    +0x18dc: uxtl2   v2.8h, v2.16b
    +0x18e0: usubw   v6.4s, v0.4s, v4.4h
    +0x18e4: usubw2  v16.4s, v0.4s, v4.8h
    +0x18e8: ldr     q4, [x20, #1168]
    +0x18ec: usubw   v7.4s, v0.4s, v5.4h
    +0x18f0: usubw2  v17.4s, v0.4s, v5.8h
    +0x18f4: st2     {v6.4s-v7.4s}, [x9], #32
    +0x18f8: and     v7.16b, v4.16b, v1.16b
    +0x18fc: ushr    v4.16b, v4.16b, #4
    +0x1900: usubw   v5.4s, v0.4s, v2.4h
    +0x1904: usubw   v6.4s, v0.4s, v3.4h
    +0x1908: st2     {v16.4s-v17.4s}, [x9]
    +0x190c: usubw2  v16.4s, v0.4s, v2.8h
    +0x1910: uxtl    v2.8h, v7.8b
    +0x1914: add     x9, sp, #0x9e0
    +0x1918: usubw2  v17.4s, v0.4s, v3.8h
    +0x191c: uxtl    v3.8h, v4.8b
    +0x1920: add     x10, x9, #0x40
    +0x1924: st2     {v5.4s-v6.4s}, [x10]
    +0x1928: usubw   v5.4s, v0.4s, v2.4h
    +0x192c: add     x10, x9, #0x60
    +0x1930: usubw   v6.4s, v0.4s, v3.4h
    +0x1934: st2     {v16.4s-v17.4s}, [x10]
    +0x1938: add     x10, x9, #0x80
    +0x193c: usubw2  v16.4s, v0.4s, v2.8h
    +0x1940: uxtl2   v2.8h, v7.16b
    +0x1944: usubw2  v17.4s, v0.4s, v3.8h
    +0x1948: uxtl2   v3.8h, v4.16b
    +0x194c: st2     {v5.4s-v6.4s}, [x10]
    +0x1950: ldr     q6, [x20, #1184]
    +0x1954: add     x10, x9, #0xa0
    +0x1958: usubw   v4.4s, v0.4s, v2.4h
    +0x195c: and     v7.16b, v6.16b, v1.16b
    +0x1960: ushr    v6.16b, v6.16b, #4
    +0x1964: usubw   v5.4s, v0.4s, v3.4h
    +0x1968: st2     {v16.4s-v17.4s}, [x10]
    +0x196c: usubw2  v16.4s, v0.4s, v2.8h
    +0x1970: add     x10, x9, #0xc0
    +0x1974: usubw2  v17.4s, v0.4s, v3.8h
    +0x1978: uxtl    v2.8h, v7.8b
    +0x197c: uxtl    v3.8h, v6.8b
    +0x1980: st2     {v4.4s-v5.4s}, [x10]
    +0x1984: add     x10, x9, #0xe0
    +0x1988: usubw   v4.4s, v0.4s, v2.4h
    +0x198c: usubw   v5.4s, v0.4s, v3.4h
    +0x1990: st2     {v16.4s-v17.4s}, [x10]
    +0x1994: usubw2  v16.4s, v0.4s, v2.8h
    +0x1998: uxtl2   v2.8h, v7.16b
    +0x199c: usubw2  v17.4s, v0.4s, v3.8h
    +0x19a0: uxtl2   v3.8h, v6.16b
    +0x19a4: ldr     q6, [x20, #1200]
    +0x19a8: add     x10, x9, #0x100
    +0x19ac: and     v7.16b, v6.16b, v1.16b
    +0x19b0: ushr    v6.16b, v6.16b, #4
    +0x19b4: st2     {v4.4s-v5.4s}, [x10]
    +0x19b8: add     x10, x9, #0x120
    +0x19bc: usubw   v4.4s, v0.4s, v2.4h
    +0x19c0: usubw   v5.4s, v0.4s, v3.4h
    +0x19c4: st2     {v16.4s-v17.4s}, [x10]
    +0x19c8: usubw2  v16.4s, v0.4s, v2.8h
    +0x19cc: uxtl    v2.8h, v7.8b
    +0x19d0: usubw2  v17.4s, v0.4s, v3.8h
    +0x19d4: add     x10, x9, #0x140
    +0x19d8: uxtl    v3.8h, v6.8b
    +0x19dc: st2     {v4.4s-v5.4s}, [x10]
    +0x19e0: add     x10, x9, #0x160
    +0x19e4: usubw   v4.4s, v0.4s, v2.4h
    +0x19e8: usubw   v5.4s, v0.4s, v3.4h
    +0x19ec: st2     {v16.4s-v17.4s}, [x10]
    +0x19f0: usubw2  v16.4s, v0.4s, v2.8h
    +0x19f4: uxtl2   v2.8h, v7.16b
    +0x19f8: usubw2  v17.4s, v0.4s, v3.8h
    +0x19fc: uxtl2   v3.8h, v6.16b
    +0x1a00: ldr     q6, [x20, #1216]
    +0x1a04: add     x10, x9, #0x180
    +0x1a08: and     v7.16b, v6.16b, v1.16b
    +0x1a0c: ushr    v6.16b, v6.16b, #4
    +0x1a10: st2     {v4.4s-v5.4s}, [x10]
    +0x1a14: add     x10, x9, #0x1a0
    +0x1a18: usubw   v4.4s, v0.4s, v2.4h
    +0x1a1c: usubw   v5.4s, v0.4s, v3.4h
    +0x1a20: st2     {v16.4s-v17.4s}, [x10]
    +0x1a24: usubw2  v16.4s, v0.4s, v2.8h
    +0x1a28: uxtl    v2.8h, v7.8b
    +0x1a2c: usubw2  v17.4s, v0.4s, v3.8h
    +0x1a30: add     x10, x9, #0x1c0
    +0x1a34: uxtl    v3.8h, v6.8b
    +0x1a38: st2     {v4.4s-v5.4s}, [x10]
    +0x1a3c: add     x10, x9, #0x1e0
    +0x1a40: usubw   v4.4s, v0.4s, v2.4h
    +0x1a44: usubw   v5.4s, v0.4s, v3.4h
    +0x1a48: st2     {v16.4s-v17.4s}, [x10]
    +0x1a4c: usubw2  v16.4s, v0.4s, v2.8h
    +0x1a50: uxtl2   v2.8h, v7.16b
    +0x1a54: usubw2  v17.4s, v0.4s, v3.8h
    +0x1a58: uxtl2   v3.8h, v6.16b
    +0x1a5c: ldr     q6, [x20, #1232]
    +0x1a60: add     x10, x9, #0x200
    +0x1a64: and     v7.16b, v6.16b, v1.16b
    +0x1a68: ushr    v6.16b, v6.16b, #4
    +0x1a6c: st2     {v4.4s-v5.4s}, [x10]
    +0x1a70: add     x10, x9, #0x220
    +0x1a74: usubw   v4.4s, v0.4s, v2.4h
    +0x1a78: usubw   v5.4s, v0.4s, v3.4h
    +0x1a7c: st2     {v16.4s-v17.4s}, [x10]
    +0x1a80: usubw2  v16.4s, v0.4s, v2.8h
    +0x1a84: uxtl    v2.8h, v7.8b
    +0x1a88: usubw2  v17.4s, v0.4s, v3.8h
    +0x1a8c: add     x10, x9, #0x240
    +0x1a90: uxtl    v3.8h, v6.8b
    +0x1a94: st2     {v4.4s-v5.4s}, [x10]
    +0x1a98: add     x10, x9, #0x260
    +0x1a9c: usubw   v4.4s, v0.4s, v2.4h
    +0x1aa0: usubw   v5.4s, v0.4s, v3.4h
    +0x1aa4: st2     {v16.4s-v17.4s}, [x10]
    +0x1aa8: usubw2  v16.4s, v0.4s, v2.8h
    +0x1aac: uxtl2   v2.8h, v7.16b
    +0x1ab0: usubw2  v17.4s, v0.4s, v3.8h
    +0x1ab4: uxtl2   v3.8h, v6.16b
    +0x1ab8: ldr     q6, [x20, #1248]
    +0x1abc: add     x10, x9, #0x280
    +0x1ac0: and     v7.16b, v6.16b, v1.16b
    +0x1ac4: ushr    v6.16b, v6.16b, #4
    +0x1ac8: st2     {v4.4s-v5.4s}, [x10]
    +0x1acc: add     x10, x9, #0x2a0
    +0x1ad0: usubw   v4.4s, v0.4s, v2.4h
    +0x1ad4: usubw   v5.4s, v0.4s, v3.4h
    +0x1ad8: st2     {v16.4s-v17.4s}, [x10]
    +0x1adc: usubw2  v16.4s, v0.4s, v2.8h
    +0x1ae0: uxtl    v2.8h, v7.8b
    +0x1ae4: usubw2  v17.4s, v0.4s, v3.8h
    +0x1ae8: add     x10, x9, #0x2c0
    +0x1aec: uxtl    v3.8h, v6.8b
    +0x1af0: st2     {v4.4s-v5.4s}, [x10]
    +0x1af4: add     x10, x9, #0x2e0
    +0x1af8: usubw   v4.4s, v0.4s, v2.4h
    +0x1afc: usubw   v5.4s, v0.4s, v3.4h
    +0x1b00: st2     {v16.4s-v17.4s}, [x10]
    +0x1b04: usubw2  v16.4s, v0.4s, v2.8h
    +0x1b08: uxtl2   v2.8h, v7.16b
    +0x1b0c: usubw2  v17.4s, v0.4s, v3.8h
    +0x1b10: uxtl2   v3.8h, v6.16b
    +0x1b14: ldr     q6, [x20, #1264]
    +0x1b18: add     x10, x9, #0x300
    +0x1b1c: and     v1.16b, v6.16b, v1.16b
    +0x1b20: ushr    v6.16b, v6.16b, #4
    +0x1b24: st2     {v4.4s-v5.4s}, [x10]
    +0x1b28: add     x10, x9, #0x320
    +0x1b2c: usubw   v4.4s, v0.4s, v2.4h
    +0x1b30: usubw   v5.4s, v0.4s, v3.4h
    +0x1b34: st2     {v16.4s-v17.4s}, [x10]
    +0x1b38: usubw2  v16.4s, v0.4s, v2.8h
    +0x1b3c: uxtl    v2.8h, v1.8b
    +0x1b40: usubw2  v17.4s, v0.4s, v3.8h
    +0x1b44: uxtl    v3.8h, v6.8b
    +0x1b48: add     x10, x9, #0x340
    +0x1b4c: uxtl2   v1.8h, v1.16b
    +0x1b50: st2     {v4.4s-v5.4s}, [x10]
    +0x1b54: usubw   v4.4s, v0.4s, v2.4h
    +0x1b58: add     x10, x9, #0x360
    +0x1b5c: usubw   v5.4s, v0.4s, v3.4h
    +0x1b60: st2     {v16.4s-v17.4s}, [x10]
    +0x1b64: usubw2  v16.4s, v0.4s, v2.8h
    +0x1b68: uxtl2   v2.8h, v6.16b
    +0x1b6c: add     x10, x9, #0x380
    +0x1b70: usubw2  v17.4s, v0.4s, v3.8h
    +0x1b74: st2     {v4.4s-v5.4s}, [x10]
    +0x1b78: usubw   v3.4s, v0.4s, v1.4h
    +0x1b7c: usubw2  v5.4s, v0.4s, v1.8h
    +0x1b80: usubw   v4.4s, v0.4s, v2.4h
    +0x1b84: add     x10, x9, #0x3a0
    +0x1b88: usubw2  v6.4s, v0.4s, v2.8h
    +0x1b8c: st2     {v16.4s-v17.4s}, [x10]
    +0x1b90: add     x10, x9, #0x3c0
    +0x1b94: st2     {v3.4s-v4.4s}, [x10]
    +0x1b98: add     x10, x9, #0x3e0
    +0x1b9c: st2     {v5.4s-v6.4s}, [x10]
    +0x1ba0: mov     w10, #0x4
    +0x1ba4: ldrsw   x11, [x9, x8]
    +0x1ba8: add     x8, x8, #0x4
    +0x1bac: cmp     x8, #0x400
    +0x1bb0: mov     w12, w11
    +0x1bb4: lsr     x11, x11, #31
    +0x1bb8: neg     w13, w12
    +0x1bbc: bic     w12, w12, w11
    +0x1bc0: and     w11, w13, w11
    +0x1bc4: orr     w11, w11, w12
    +0x1bc8: sub     w11, w10, w11
    +0x1bcc: sxtw    x11, w11
    +0x1bd0: lsr     x11, x11, #31
    +0x1bd4: orr     w21, w21, w11
    +0x1bd8: b.ne    <mldsa65_pk_from_sk+0x1ba4>
    +0x1bdc: movi    v1.16b, #0xf
    +0x1be0: ldr     q0, [x20, #1280]
    +0x1be4: add     x9, sp, #0x9e0
    +0x1be8: mov     x8, xzr
    +0x1bec: mov     w27, wzr
    +0x1bf0: ushr    v3.16b, v0.16b, #4
    +0x1bf4: and     v2.16b, v0.16b, v1.16b
    +0x1bf8: movi    v0.4s, #0x4
    +0x1bfc: uxtl    v5.8h, v3.8b
    +0x1c00: uxtl2   v3.8h, v3.16b
    +0x1c04: uxtl    v4.8h, v2.8b
    +0x1c08: uxtl2   v2.8h, v2.16b
    +0x1c0c: usubw   v6.4s, v0.4s, v4.4h
    +0x1c10: usubw2  v16.4s, v0.4s, v4.8h
    +0x1c14: ldr     q4, [x20, #1296]
    +0x1c18: usubw   v7.4s, v0.4s, v5.4h
    +0x1c1c: usubw2  v17.4s, v0.4s, v5.8h
    +0x1c20: st2     {v6.4s-v7.4s}, [x9], #32
    +0x1c24: and     v7.16b, v4.16b, v1.16b
    +0x1c28: ushr    v4.16b, v4.16b, #4
    +0x1c2c: usubw   v5.4s, v0.4s, v2.4h
    +0x1c30: usubw   v6.4s, v0.4s, v3.4h
    +0x1c34: st2     {v16.4s-v17.4s}, [x9]
    +0x1c38: usubw2  v16.4s, v0.4s, v2.8h
    +0x1c3c: uxtl    v2.8h, v7.8b
    +0x1c40: add     x9, sp, #0x9e0
    +0x1c44: usubw2  v17.4s, v0.4s, v3.8h
    +0x1c48: uxtl    v3.8h, v4.8b
    +0x1c4c: add     x10, x9, #0x40
    +0x1c50: st2     {v5.4s-v6.4s}, [x10]
    +0x1c54: usubw   v5.4s, v0.4s, v2.4h
    +0x1c58: add     x10, x9, #0x60
    +0x1c5c: usubw   v6.4s, v0.4s, v3.4h
    +0x1c60: st2     {v16.4s-v17.4s}, [x10]
    +0x1c64: add     x10, x9, #0x80
    +0x1c68: usubw2  v16.4s, v0.4s, v2.8h
    +0x1c6c: uxtl2   v2.8h, v7.16b
    +0x1c70: usubw2  v17.4s, v0.4s, v3.8h
    +0x1c74: uxtl2   v3.8h, v4.16b
    +0x1c78: st2     {v5.4s-v6.4s}, [x10]
    +0x1c7c: ldr     q6, [x20, #1312]
    +0x1c80: add     x10, x9, #0xa0
    +0x1c84: usubw   v4.4s, v0.4s, v2.4h
    +0x1c88: and     v7.16b, v6.16b, v1.16b
    +0x1c8c: ushr    v6.16b, v6.16b, #4
    +0x1c90: usubw   v5.4s, v0.4s, v3.4h
    +0x1c94: st2     {v16.4s-v17.4s}, [x10]
    +0x1c98: usubw2  v16.4s, v0.4s, v2.8h
    +0x1c9c: add     x10, x9, #0xc0
    +0x1ca0: usubw2  v17.4s, v0.4s, v3.8h
    +0x1ca4: uxtl    v2.8h, v7.8b
    +0x1ca8: uxtl    v3.8h, v6.8b
    +0x1cac: st2     {v4.4s-v5.4s}, [x10]
    +0x1cb0: add     x10, x9, #0xe0
    +0x1cb4: usubw   v4.4s, v0.4s, v2.4h
    +0x1cb8: usubw   v5.4s, v0.4s, v3.4h
    +0x1cbc: st2     {v16.4s-v17.4s}, [x10]
    +0x1cc0: usubw2  v16.4s, v0.4s, v2.8h
    +0x1cc4: uxtl2   v2.8h, v7.16b
    +0x1cc8: usubw2  v17.4s, v0.4s, v3.8h
    +0x1ccc: uxtl2   v3.8h, v6.16b
    +0x1cd0: ldr     q6, [x20, #1328]
    +0x1cd4: add     x10, x9, #0x100
    +0x1cd8: and     v7.16b, v6.16b, v1.16b
    +0x1cdc: ushr    v6.16b, v6.16b, #4
    +0x1ce0: st2     {v4.4s-v5.4s}, [x10]
    +0x1ce4: add     x10, x9, #0x120
    +0x1ce8: usubw   v4.4s, v0.4s, v2.4h
    +0x1cec: usubw   v5.4s, v0.4s, v3.4h
    +0x1cf0: st2     {v16.4s-v17.4s}, [x10]
    +0x1cf4: usubw2  v16.4s, v0.4s, v2.8h
    +0x1cf8: uxtl    v2.8h, v7.8b
    +0x1cfc: usubw2  v17.4s, v0.4s, v3.8h
    +0x1d00: add     x10, x9, #0x140
    +0x1d04: uxtl    v3.8h, v6.8b
    +0x1d08: st2     {v4.4s-v5.4s}, [x10]
    +0x1d0c: add     x10, x9, #0x160
    +0x1d10: usubw   v4.4s, v0.4s, v2.4h
    +0x1d14: usubw   v5.4s, v0.4s, v3.4h
    +0x1d18: st2     {v16.4s-v17.4s}, [x10]
    +0x1d1c: usubw2  v16.4s, v0.4s, v2.8h
    +0x1d20: uxtl2   v2.8h, v7.16b
    +0x1d24: usubw2  v17.4s, v0.4s, v3.8h
    +0x1d28: uxtl2   v3.8h, v6.16b
    +0x1d2c: ldr     q6, [x20, #1344]
    +0x1d30: add     x10, x9, #0x180
    +0x1d34: and     v7.16b, v6.16b, v1.16b
    +0x1d38: ushr    v6.16b, v6.16b, #4
    +0x1d3c: st2     {v4.4s-v5.4s}, [x10]
    +0x1d40: add     x10, x9, #0x1a0
    +0x1d44: usubw   v4.4s, v0.4s, v2.4h
    +0x1d48: usubw   v5.4s, v0.4s, v3.4h
    +0x1d4c: st2     {v16.4s-v17.4s}, [x10]
    +0x1d50: usubw2  v16.4s, v0.4s, v2.8h
    +0x1d54: uxtl    v2.8h, v7.8b
    +0x1d58: usubw2  v17.4s, v0.4s, v3.8h
    +0x1d5c: add     x10, x9, #0x1c0
    +0x1d60: uxtl    v3.8h, v6.8b
    +0x1d64: st2     {v4.4s-v5.4s}, [x10]
    +0x1d68: add     x10, x9, #0x1e0
    +0x1d6c: usubw   v4.4s, v0.4s, v2.4h
    +0x1d70: usubw   v5.4s, v0.4s, v3.4h
    +0x1d74: st2     {v16.4s-v17.4s}, [x10]
    +0x1d78: usubw2  v16.4s, v0.4s, v2.8h
    +0x1d7c: uxtl2   v2.8h, v7.16b
    +0x1d80: usubw2  v17.4s, v0.4s, v3.8h
    +0x1d84: uxtl2   v3.8h, v6.16b
    +0x1d88: ldr     q6, [x20, #1360]
    +0x1d8c: add     x10, x9, #0x200
    +0x1d90: and     v7.16b, v6.16b, v1.16b
    +0x1d94: ushr    v6.16b, v6.16b, #4
    +0x1d98: st2     {v4.4s-v5.4s}, [x10]
    +0x1d9c: add     x10, x9, #0x220
    +0x1da0: usubw   v4.4s, v0.4s, v2.4h
    +0x1da4: usubw   v5.4s, v0.4s, v3.4h
    +0x1da8: st2     {v16.4s-v17.4s}, [x10]
    +0x1dac: usubw2  v16.4s, v0.4s, v2.8h
    +0x1db0: uxtl    v2.8h, v7.8b
    +0x1db4: usubw2  v17.4s, v0.4s, v3.8h
    +0x1db8: add     x10, x9, #0x240
    +0x1dbc: uxtl    v3.8h, v6.8b
    +0x1dc0: st2     {v4.4s-v5.4s}, [x10]
    +0x1dc4: add     x10, x9, #0x260
    +0x1dc8: usubw   v4.4s, v0.4s, v2.4h
    +0x1dcc: usubw   v5.4s, v0.4s, v3.4h
    +0x1dd0: st2     {v16.4s-v17.4s}, [x10]
    +0x1dd4: usubw2  v16.4s, v0.4s, v2.8h
    +0x1dd8: uxtl2   v2.8h, v7.16b
    +0x1ddc: usubw2  v17.4s, v0.4s, v3.8h
    +0x1de0: uxtl2   v3.8h, v6.16b
    +0x1de4: ldr     q6, [x20, #1376]
    +0x1de8: add     x10, x9, #0x280
    +0x1dec: and     v7.16b, v6.16b, v1.16b
    +0x1df0: ushr    v6.16b, v6.16b, #4
    +0x1df4: st2     {v4.4s-v5.4s}, [x10]
    +0x1df8: add     x10, x9, #0x2a0
    +0x1dfc: usubw   v4.4s, v0.4s, v2.4h
    +0x1e00: usubw   v5.4s, v0.4s, v3.4h
    +0x1e04: st2     {v16.4s-v17.4s}, [x10]
    +0x1e08: usubw2  v16.4s, v0.4s, v2.8h
    +0x1e0c: uxtl    v2.8h, v7.8b
    +0x1e10: usubw2  v17.4s, v0.4s, v3.8h
    +0x1e14: add     x10, x9, #0x2c0
    +0x1e18: uxtl    v3.8h, v6.8b
    +0x1e1c: st2     {v4.4s-v5.4s}, [x10]
    +0x1e20: add     x10, x9, #0x2e0
    +0x1e24: usubw   v4.4s, v0.4s, v2.4h
    +0x1e28: usubw   v5.4s, v0.4s, v3.4h
    +0x1e2c: st2     {v16.4s-v17.4s}, [x10]
    +0x1e30: usubw2  v16.4s, v0.4s, v2.8h
    +0x1e34: uxtl2   v2.8h, v7.16b
    +0x1e38: usubw2  v17.4s, v0.4s, v3.8h
    +0x1e3c: uxtl2   v3.8h, v6.16b
    +0x1e40: ldr     q6, [x20, #1392]
    +0x1e44: add     x10, x9, #0x300
    +0x1e48: and     v1.16b, v6.16b, v1.16b
    +0x1e4c: ushr    v6.16b, v6.16b, #4
    +0x1e50: st2     {v4.4s-v5.4s}, [x10]
    +0x1e54: add     x10, x9, #0x320
    +0x1e58: usubw   v4.4s, v0.4s, v2.4h
    +0x1e5c: usubw   v5.4s, v0.4s, v3.4h
    +0x1e60: st2     {v16.4s-v17.4s}, [x10]
    +0x1e64: usubw2  v16.4s, v0.4s, v2.8h
    +0x1e68: uxtl    v2.8h, v1.8b
    +0x1e6c: usubw2  v17.4s, v0.4s, v3.8h
    +0x1e70: uxtl    v3.8h, v6.8b
    +0x1e74: add     x10, x9, #0x340
    +0x1e78: uxtl2   v1.8h, v1.16b
    +0x1e7c: st2     {v4.4s-v5.4s}, [x10]
    +0x1e80: usubw   v4.4s, v0.4s, v2.4h
    +0x1e84: add     x10, x9, #0x360
    +0x1e88: usubw   v5.4s, v0.4s, v3.4h
    +0x1e8c: st2     {v16.4s-v17.4s}, [x10]
    +0x1e90: usubw2  v16.4s, v0.4s, v2.8h
    +0x1e94: uxtl2   v2.8h, v6.16b
    +0x1e98: add     x10, x9, #0x380
    +0x1e9c: usubw2  v17.4s, v0.4s, v3.8h
    +0x1ea0: st2     {v4.4s-v5.4s}, [x10]
    +0x1ea4: usubw   v3.4s, v0.4s, v1.4h
    +0x1ea8: usubw2  v5.4s, v0.4s, v1.8h
    +0x1eac: usubw   v4.4s, v0.4s, v2.4h
    +0x1eb0: add     x10, x9, #0x3a0
    +0x1eb4: usubw2  v6.4s, v0.4s, v2.8h
    +0x1eb8: st2     {v16.4s-v17.4s}, [x10]
    +0x1ebc: add     x10, x9, #0x3c0
    +0x1ec0: st2     {v3.4s-v4.4s}, [x10]
    +0x1ec4: add     x10, x9, #0x3e0
    +0x1ec8: st2     {v5.4s-v6.4s}, [x10]
    +0x1ecc: mov     w10, #0x4
    +0x1ed0: ldrsw   x11, [x9, x8]
    +0x1ed4: add     x8, x8, #0x4
    +0x1ed8: cmp     x8, #0x400
    +0x1edc: mov     w12, w11
    +0x1ee0: lsr     x11, x11, #31
    +0x1ee4: neg     w13, w12
    +0x1ee8: bic     w12, w12, w11
    +0x1eec: and     w11, w13, w11
    +0x1ef0: orr     w11, w11, w12
    +0x1ef4: sub     w11, w10, w11
    +0x1ef8: sxtw    x11, w11
    +0x1efc: lsr     x11, x11, #31
    +0x1f00: orr     w27, w27, w11
    +0x1f04: b.ne    <mldsa65_pk_from_sk+0x1ed0>
    +0x1f08: movi    v1.16b, #0xf
    +0x1f0c: ldr     q0, [x20, #1408]
    +0x1f10: add     x9, sp, #0x9e0
    +0x1f14: mov     x8, xzr
    +0x1f18: mov     w23, wzr
    +0x1f1c: ushr    v3.16b, v0.16b, #4
    +0x1f20: and     v2.16b, v0.16b, v1.16b
    +0x1f24: movi    v0.4s, #0x4
    +0x1f28: uxtl    v5.8h, v3.8b
    +0x1f2c: uxtl2   v3.8h, v3.16b
    +0x1f30: uxtl    v4.8h, v2.8b
    +0x1f34: uxtl2   v2.8h, v2.16b
    +0x1f38: usubw   v6.4s, v0.4s, v4.4h
    +0x1f3c: usubw2  v16.4s, v0.4s, v4.8h
    +0x1f40: ldr     q4, [x20, #1424]
    +0x1f44: usubw   v7.4s, v0.4s, v5.4h
    +0x1f48: usubw2  v17.4s, v0.4s, v5.8h
    +0x1f4c: st2     {v6.4s-v7.4s}, [x9], #32
    +0x1f50: and     v7.16b, v4.16b, v1.16b
    +0x1f54: ushr    v4.16b, v4.16b, #4
    +0x1f58: usubw   v5.4s, v0.4s, v2.4h
    +0x1f5c: usubw   v6.4s, v0.4s, v3.4h
    +0x1f60: st2     {v16.4s-v17.4s}, [x9]
    +0x1f64: usubw2  v16.4s, v0.4s, v2.8h
    +0x1f68: uxtl    v2.8h, v7.8b
    +0x1f6c: add     x9, sp, #0x9e0
    +0x1f70: usubw2  v17.4s, v0.4s, v3.8h
    +0x1f74: uxtl    v3.8h, v4.8b
    +0x1f78: add     x10, x9, #0x40
    +0x1f7c: st2     {v5.4s-v6.4s}, [x10]
    +0x1f80: usubw   v5.4s, v0.4s, v2.4h
    +0x1f84: add     x10, x9, #0x60
    +0x1f88: usubw   v6.4s, v0.4s, v3.4h
    +0x1f8c: st2     {v16.4s-v17.4s}, [x10]
    +0x1f90: add     x10, x9, #0x80
    +0x1f94: usubw2  v16.4s, v0.4s, v2.8h
    +0x1f98: uxtl2   v2.8h, v7.16b
    +0x1f9c: usubw2  v17.4s, v0.4s, v3.8h
    +0x1fa0: uxtl2   v3.8h, v4.16b
    +0x1fa4: st2     {v5.4s-v6.4s}, [x10]
    +0x1fa8: ldr     q6, [x20, #1440]
    +0x1fac: add     x10, x9, #0xa0
    +0x1fb0: usubw   v4.4s, v0.4s, v2.4h
    +0x1fb4: and     v7.16b, v6.16b, v1.16b
    +0x1fb8: ushr    v6.16b, v6.16b, #4
    +0x1fbc: usubw   v5.4s, v0.4s, v3.4h
    +0x1fc0: st2     {v16.4s-v17.4s}, [x10]
    +0x1fc4: usubw2  v16.4s, v0.4s, v2.8h
    +0x1fc8: add     x10, x9, #0xc0
    +0x1fcc: usubw2  v17.4s, v0.4s, v3.8h
    +0x1fd0: uxtl    v2.8h, v7.8b
    +0x1fd4: uxtl    v3.8h, v6.8b
    +0x1fd8: st2     {v4.4s-v5.4s}, [x10]
    +0x1fdc: add     x10, x9, #0xe0
    +0x1fe0: usubw   v4.4s, v0.4s, v2.4h
    +0x1fe4: usubw   v5.4s, v0.4s, v3.4h
    +0x1fe8: st2     {v16.4s-v17.4s}, [x10]
    +0x1fec: usubw2  v16.4s, v0.4s, v2.8h
    +0x1ff0: uxtl2   v2.8h, v7.16b
    +0x1ff4: usubw2  v17.4s, v0.4s, v3.8h
    +0x1ff8: uxtl2   v3.8h, v6.16b
    +0x1ffc: ldr     q6, [x20, #1456]
    +0x2000: add     x10, x9, #0x100
    +0x2004: and     v7.16b, v6.16b, v1.16b
    +0x2008: ushr    v6.16b, v6.16b, #4
    +0x200c: st2     {v4.4s-v5.4s}, [x10]
    +0x2010: add     x10, x9, #0x120
    +0x2014: usubw   v4.4s, v0.4s, v2.4h
    +0x2018: usubw   v5.4s, v0.4s, v3.4h
    +0x201c: st2     {v16.4s-v17.4s}, [x10]
    +0x2020: usubw2  v16.4s, v0.4s, v2.8h
    +0x2024: uxtl    v2.8h, v7.8b
    +0x2028: usubw2  v17.4s, v0.4s, v3.8h
    +0x202c: add     x10, x9, #0x140
    +0x2030: uxtl    v3.8h, v6.8b
    +0x2034: st2     {v4.4s-v5.4s}, [x10]
    +0x2038: add     x10, x9, #0x160
    +0x203c: usubw   v4.4s, v0.4s, v2.4h
    +0x2040: usubw   v5.4s, v0.4s, v3.4h
    +0x2044: st2     {v16.4s-v17.4s}, [x10]
    +0x2048: usubw2  v16.4s, v0.4s, v2.8h
    +0x204c: uxtl2   v2.8h, v7.16b
    +0x2050: usubw2  v17.4s, v0.4s, v3.8h
    +0x2054: uxtl2   v3.8h, v6.16b
    +0x2058: ldr     q6, [x20, #1472]
    +0x205c: add     x10, x9, #0x180
    +0x2060: and     v7.16b, v6.16b, v1.16b
    +0x2064: ushr    v6.16b, v6.16b, #4
    +0x2068: st2     {v4.4s-v5.4s}, [x10]
    +0x206c: add     x10, x9, #0x1a0
    +0x2070: usubw   v4.4s, v0.4s, v2.4h
    +0x2074: usubw   v5.4s, v0.4s, v3.4h
    +0x2078: st2     {v16.4s-v17.4s}, [x10]
    +0x207c: usubw2  v16.4s, v0.4s, v2.8h
    +0x2080: uxtl    v2.8h, v7.8b
    +0x2084: usubw2  v17.4s, v0.4s, v3.8h
    +0x2088: add     x10, x9, #0x1c0
    +0x208c: uxtl    v3.8h, v6.8b
    +0x2090: st2     {v4.4s-v5.4s}, [x10]
    +0x2094: add     x10, x9, #0x1e0
    +0x2098: usubw   v4.4s, v0.4s, v2.4h
    +0x209c: usubw   v5.4s, v0.4s, v3.4h
    +0x20a0: st2     {v16.4s-v17.4s}, [x10]
    +0x20a4: usubw2  v16.4s, v0.4s, v2.8h
    +0x20a8: uxtl2   v2.8h, v7.16b
    +0x20ac: usubw2  v17.4s, v0.4s, v3.8h
    +0x20b0: uxtl2   v3.8h, v6.16b
    +0x20b4: ldr     q6, [x20, #1488]
    +0x20b8: add     x10, x9, #0x200
    +0x20bc: and     v7.16b, v6.16b, v1.16b
    +0x20c0: ushr    v6.16b, v6.16b, #4
    +0x20c4: st2     {v4.4s-v5.4s}, [x10]
    +0x20c8: add     x10, x9, #0x220
    +0x20cc: usubw   v4.4s, v0.4s, v2.4h
    +0x20d0: usubw   v5.4s, v0.4s, v3.4h
    +0x20d4: st2     {v16.4s-v17.4s}, [x10]
    +0x20d8: usubw2  v16.4s, v0.4s, v2.8h
    +0x20dc: uxtl    v2.8h, v7.8b
    +0x20e0: usubw2  v17.4s, v0.4s, v3.8h
    +0x20e4: add     x10, x9, #0x240
    +0x20e8: uxtl    v3.8h, v6.8b
    +0x20ec: st2     {v4.4s-v5.4s}, [x10]
    +0x20f0: add     x10, x9, #0x260
    +0x20f4: usubw   v4.4s, v0.4s, v2.4h
    +0x20f8: usubw   v5.4s, v0.4s, v3.4h
    +0x20fc: st2     {v16.4s-v17.4s}, [x10]
    +0x2100: usubw2  v16.4s, v0.4s, v2.8h
    +0x2104: uxtl2   v2.8h, v7.16b
    +0x2108: usubw2  v17.4s, v0.4s, v3.8h
    +0x210c: uxtl2   v3.8h, v6.16b
    +0x2110: ldr     q6, [x20, #1504]
    +0x2114: add     x10, x9, #0x280
    +0x2118: and     v7.16b, v6.16b, v1.16b
    +0x211c: ushr    v6.16b, v6.16b, #4
    +0x2120: st2     {v4.4s-v5.4s}, [x10]
    +0x2124: add     x10, x9, #0x2a0
    +0x2128: usubw   v4.4s, v0.4s, v2.4h
    +0x212c: usubw   v5.4s, v0.4s, v3.4h
    +0x2130: st2     {v16.4s-v17.4s}, [x10]
    +0x2134: usubw2  v16.4s, v0.4s, v2.8h
    +0x2138: uxtl    v2.8h, v7.8b
    +0x213c: usubw2  v17.4s, v0.4s, v3.8h
    +0x2140: add     x10, x9, #0x2c0
    +0x2144: uxtl    v3.8h, v6.8b
    +0x2148: st2     {v4.4s-v5.4s}, [x10]
    +0x214c: add     x10, x9, #0x2e0
    +0x2150: usubw   v4.4s, v0.4s, v2.4h
    +0x2154: usubw   v5.4s, v0.4s, v3.4h
    +0x2158: st2     {v16.4s-v17.4s}, [x10]
    +0x215c: usubw2  v16.4s, v0.4s, v2.8h
    +0x2160: uxtl2   v2.8h, v7.16b
    +0x2164: usubw2  v17.4s, v0.4s, v3.8h
    +0x2168: uxtl2   v3.8h, v6.16b
    +0x216c: ldr     q6, [x20, #1520]
    +0x2170: add     x10, x9, #0x300
    +0x2174: and     v1.16b, v6.16b, v1.16b
    +0x2178: ushr    v6.16b, v6.16b, #4
    +0x217c: st2     {v4.4s-v5.4s}, [x10]
    +0x2180: add     x10, x9, #0x320
    +0x2184: usubw   v4.4s, v0.4s, v2.4h
    +0x2188: usubw   v5.4s, v0.4s, v3.4h
    +0x218c: st2     {v16.4s-v17.4s}, [x10]
    +0x2190: usubw2  v16.4s, v0.4s, v2.8h
    +0x2194: uxtl    v2.8h, v1.8b
    +0x2198: usubw2  v17.4s, v0.4s, v3.8h
    +0x219c: uxtl    v3.8h, v6.8b
    +0x21a0: add     x10, x9, #0x340
    +0x21a4: uxtl2   v1.8h, v1.16b
    +0x21a8: st2     {v4.4s-v5.4s}, [x10]
    +0x21ac: usubw   v4.4s, v0.4s, v2.4h
    +0x21b0: add     x10, x9, #0x360
    +0x21b4: usubw   v5.4s, v0.4s, v3.4h
    +0x21b8: st2     {v16.4s-v17.4s}, [x10]
    +0x21bc: usubw2  v16.4s, v0.4s, v2.8h
    +0x21c0: uxtl2   v2.8h, v6.16b
    +0x21c4: add     x10, x9, #0x380
    +0x21c8: usubw2  v17.4s, v0.4s, v3.8h
    +0x21cc: st2     {v4.4s-v5.4s}, [x10]
    +0x21d0: usubw   v3.4s, v0.4s, v1.4h
    +0x21d4: usubw2  v5.4s, v0.4s, v1.8h
    +0x21d8: usubw   v4.4s, v0.4s, v2.4h
    +0x21dc: add     x10, x9, #0x3a0
    +0x21e0: usubw2  v6.4s, v0.4s, v2.8h
    +0x21e4: st2     {v16.4s-v17.4s}, [x10]
    +0x21e8: add     x10, x9, #0x3c0
    +0x21ec: st2     {v3.4s-v4.4s}, [x10]
    +0x21f0: add     x10, x9, #0x3e0
    +0x21f4: st2     {v5.4s-v6.4s}, [x10]
    +0x21f8: mov     w10, #0x4
    +0x21fc: ldrsw   x11, [x9, x8]
    +0x2200: add     x8, x8, #0x4
    +0x2204: cmp     x8, #0x400
    +0x2208: mov     w12, w11
    +0x220c: lsr     x11, x11, #31
    +0x2210: neg     w13, w12
    +0x2214: bic     w12, w12, w11
    +0x2218: and     w11, w13, w11
    +0x221c: orr     w11, w11, w12
    +0x2220: sub     w11, w10, w11
    +0x2224: sxtw    x11, w11
    +0x2228: lsr     x11, x11, #31
    +0x222c: orr     w23, w23, w11
    +0x2230: b.ne    <mldsa65_pk_from_sk+0x21fc>
    +0x2234: add     x0, sp, #0xde0
    +0x2238: bl      <mldsa_poly_ntt>
    +0x223c: ldr     x0, [sp, #24]
    +0x2240: bl      <mldsa_poly_ntt>
    +0x2244: ldr     x0, [sp, #8]
    +0x2248: bl      <mldsa_poly_ntt>
    +0x224c: mov     x0, x24
    +0x2250: bl      <mldsa_poly_ntt>
    +0x2254: mov     x0, x25
    +0x2258: bl      <mldsa_poly_ntt>
    +0x225c: ldr     q0, [sp, #8832]
    +0x2260: ldr     q1, [sp, #8848]
    +0x2264: add     x4, sp, #0x2, lsl #12
    +0x2268: add     x0, x19, #0x20
    +0x226c: add     x1, sp, #0x20
    +0x2270: add     x2, sp, #0xde0
    +0x2274: add     x3, x20, #0x300
    +0x2278: add     x4, x4, #0x280
    +0x227c: stp     q0, q1, [x19]
    +0x2280: add     x24, sp, #0x20
    +0x2284: bl      <mld_compute_pack_t0_t165>
    +0x2288: movi    v0.2d, #0x0
    +0x228c: adrp    x8, <page>
    +0x2290: movi    v1.2d, #0x0
    +0x2294: movi    v3.2d, #0x0
    +0x2298: movi    v2.2d, #0x0
    +0x229c: ldr     q17, [x8, #1472]
    +0x22a0: movi    v4.2d, #0x0
    +0x22a4: movi    v5.2d, #0x0
    +0x22a8: adrp    x8, <page>
    +0x22ac: movi    v7.2d, #0x0
    +0x22b0: movi    v6.2d, #0x0
    +0x22b4: adrp    x9, <page>
    +0x22b8: movi    v16.2d, #0x0
    +0x22bc: movi    v18.2d, #0x0
    +0x22c0: adrp    x10, <page>
    +0x22c4: ldr     q19, [x8, #1488]
    +0x22c8: ldr     q20, [x9, #1504]
    +0x22cc: ldr     q21, [x10, #1520]
    +0x22d0: add     x8, x20, #0x610
    +0x22d4: mov     w9, #0x610
    +0x22d8: add     x10, x24, x9
    +0x22dc: ldp     q23, q24, [x8, #-16]
    +0x22e0: sub     x11, x10, #0x610
    +0x22e4: sub     x10, x10, #0x600
    +0x22e8: add     x9, x9, #0x20
    +0x22ec: ldr     q22, [x11]
    +0x22f0: ldr     q25, [x10]
    +0x22f4: cmp     x9, #0xfd0
    +0x22f8: add     x8, x8, #0x20
    +0x22fc: eor     v22.16b, v23.16b, v22.16b
    +0x2300: eor     v23.16b, v24.16b, v25.16b
    +0x2304: tbl     v24.16b, {v22.16b}, v19.16b
    +0x2308: tbl     v25.16b, {v22.16b}, v20.16b
    +0x230c: tbl     v26.16b, {v22.16b}, v21.16b
    +0x2310: tbl     v27.16b, {v22.16b}, v17.16b
    +0x2314: tbl     v28.16b, {v23.16b}, v20.16b
    +0x2318: tbl     v29.16b, {v23.16b}, v21.16b
    +0x231c: tbl     v30.16b, {v23.16b}, v17.16b
    +0x2320: tbl     v31.16b, {v23.16b}, v19.16b
    +0x2324: orr     v0.16b, v22.16b, v0.16b
    +0x2328: orr     v18.16b, v23.16b, v18.16b
    +0x232c: eor     v4.16b, v4.16b, v26.16b
    +0x2330: eor     v2.16b, v2.16b, v25.16b
    +0x2334: eor     v3.16b, v3.16b, v24.16b
    +0x2338: eor     v1.16b, v1.16b, v27.16b
    +0x233c: eor     v16.16b, v16.16b, v29.16b
    +0x2340: eor     v6.16b, v6.16b, v28.16b
    +0x2344: eor     v7.16b, v7.16b, v31.16b
    +0x2348: eor     v5.16b, v5.16b, v30.16b
    +0x234c: b.ne    <mldsa65_pk_from_sk+0x22d8>
    +0x2350: orr     v0.16b, v18.16b, v0.16b
    +0x2354: eor     v3.16b, v7.16b, v3.16b
    +0x2358: mov     x10, xzr
    +0x235c: eor     v4.16b, v16.16b, v4.16b
    +0x2360: eor     v1.16b, v5.16b, v1.16b
    +0x2364: str     xzr, [sp, #24]
    +0x2368: eor     v2.16b, v6.16b, v2.16b
    +0x236c: movi    v17.2d, #0x0
    +0x2370: add     x20, sp, #0x2, lsl #12
    +0x2374: mov     d5, v0.d[1]
    +0x2378: add     x20, x20, #0x2a0
    +0x237c: add     x0, sp, #0x2, lsl #12
    +0x2380: add     x0, x0, #0x2a0
    +0x2384: eor     v1.16b, v1.16b, v2.16b
    +0x2388: eor     v2.16b, v3.16b, v4.16b
    +0x238c: orr     v0.8b, v0.8b, v5.8b
    +0x2390: eor     v1.16b, v1.16b, v2.16b
    +0x2394: fmov    x8, d0
    +0x2398: mov     d0, v1.d[1]
    +0x239c: orr     x8, x8, x8, lsr #32
    +0x23a0: lsr     x9, x8, #16
    +0x23a4: eor     v0.8b, v1.8b, v0.8b
    +0x23a8: orr     w8, w8, w9
    +0x23ac: orr     w8, w8, w8, lsr #8
    +0x23b0: fmov    x9, d0
    +0x23b4: sub     x8, x10, w8, uxtb
    +0x23b8: lsr     x10, x9, #32
    +0x23bc: lsr     x8, x8, #32
    +0x23c0: eor     w24, w9, w10
    +0x23c4: eor     w25, w8, w24
    +0x23c8: str     q17, [sp, #8864]
    +0x23cc: stur    q17, [x20, #188]
    +0x23d0: ldp     d0, d1, [x19]
    +0x23d4: str     q17, [sp, #8896]
    +0x23d8: ldp     d2, d3, [x19, #16]
    +0x23dc: ldr     d4, [sp, #8872]
    +0x23e0: ldp     d5, d6, [x19, #32]
    +0x23e4: str     q17, [sp, #8880]
    +0x23e8: ldr     d16, [sp, #8896]
    +0x23ec: str     q17, [sp, #8912]
    +0x23f0: ldr     d7, [sp, #8888]
    +0x23f4: eor     v1.8b, v4.8b, v1.8b
    +0x23f8: str     d0, [sp, #8864]
    +0x23fc: ldp     d0, d4, [x19, #48]
    +0x2400: str     d2, [sp, #8880]
    +0x2404: eor     v2.8b, v16.8b, v5.8b
    +0x2408: ldr     d5, [sp, #8912]
    +0x240c: ldr     d16, [sp, #8920]
    +0x2410: eor     v3.8b, v7.8b, v3.8b
    +0x2414: ldr     d7, [sp, #8904]
    +0x2418: str     q17, [sp, #8928]
    +0x241c: eor     v0.8b, v5.8b, v0.8b
    +0x2420: eor     v4.8b, v16.8b, v4.8b
    +0x2424: ldp     d5, d16, [x19, #64]
    +0x2428: eor     v6.8b, v7.8b, v6.8b
    +0x242c: ldr     d7, [sp, #8928]
    +0x2430: str     q17, [sp, #8944]
    +0x2434: str     d1, [sp, #8872]
    +0x2438: ldr     d1, [sp, #8936]
    +0x243c: eor     v5.8b, v7.8b, v5.8b
    +0x2440: str     d3, [sp, #8888]
    +0x2444: ldp     d3, d7, [x19, #80]
    +0x2448: str     d2, [sp, #8896]
    +0x244c: ldr     d2, [sp, #8944]
    +0x2450: eor     v1.8b, v1.8b, v16.8b
    +0x2454: str     d0, [sp, #8912]
    +0x2458: ldr     d0, [sp, #8952]
    +0x245c: str     q17, [sp, #8960]
    +0x2460: str     d6, [sp, #8904]
    +0x2464: ldp     d6, d16, [x19, #96]
    +0x2468: eor     v2.8b, v2.8b, v3.8b
    +0x246c: str     q17, [sp, #8976]
    +0x2470: eor     v0.8b, v0.8b, v7.8b
    +0x2474: str     d4, [sp, #8920]
    +0x2478: ldr     d7, [sp, #8968]
    +0x247c: ldr     d3, [sp, #8960]
    +0x2480: str     d5, [sp, #8928]
    +0x2484: ldp     d4, d5, [x19, #112]
    +0x2488: str     d1, [sp, #8936]
    +0x248c: ldr     d1, [sp, #8976]
    +0x2490: eor     v3.8b, v3.8b, v6.8b
    +0x2494: str     q17, [sp, #8992]
    +0x2498: str     d2, [sp, #8944]
    +0x249c: eor     v2.8b, v7.8b, v16.8b
    +0x24a0: eor     v1.8b, v1.8b, v4.8b
    +0x24a4: str     d0, [sp, #8952]
    +0x24a8: ldr     d0, [sp, #8984]
    +0x24ac: ldr     d4, [x19, #128]
    +0x24b0: ldr     d6, [sp, #8992]
    +0x24b4: str     q17, [sp, #9040]
    +0x24b8: eor     v0.8b, v0.8b, v5.8b
    +0x24bc: str     d2, [sp, #8968]
    +0x24c0: eor     v2.8b, v6.8b, v4.8b
    +0x24c4: str     q17, [sp, #9024]
    +0x24c8: str     q17, [sp, #9008]
    +0x24cc: str     d3, [sp, #8960]
    +0x24d0: str     d1, [sp, #8976]
    +0x24d4: str     d0, [sp, #8984]
    +0x24d8: str     d2, [sp, #8992]
    +0x24dc: bl      <mldsa_keccakf1600_permute>
    +0x24e0: ldp     d1, d2, [x19, #136]
    +0x24e4: add     x0, sp, #0x2, lsl #12
    +0x24e8: ldr     d0, [sp, #8864]
    +0x24ec: ldr     d3, [sp, #8872]
    +0x24f0: add     x0, x0, #0x2a0
    +0x24f4: ldr     d5, [sp, #8880]
    +0x24f8: ldr     d6, [sp, #8896]
    +0x24fc: ldr     d7, [sp, #8904]
    +0x2500: eor     v0.8b, v0.8b, v1.8b
    +0x2504: eor     v1.8b, v3.8b, v2.8b
    +0x2508: ldr     d3, [sp, #8888]
    +0x250c: ldp     d4, d2, [x19, #152]
    +0x2510: ldr     d16, [sp, #8912]
    +0x2514: ldr     d17, [sp, #8920]
    +0x2518: ldr     d18, [sp, #8928]
    +0x251c: str     d0, [sp, #8864]
    +0x2520: eor     v4.8b, v5.8b, v4.8b
    +0x2524: eor     v2.8b, v3.8b, v2.8b
    +0x2528: str     d1, [sp, #8872]
    +0x252c: ldp     d5, d3, [x19, #168]
    +0x2530: str     d2, [sp, #8888]
    +0x2534: ldp     d1, d2, [x19, #216]
    +0x2538: eor     v5.8b, v6.8b, v5.8b
    +0x253c: eor     v3.8b, v7.8b, v3.8b
    +0x2540: str     d4, [sp, #8880]
    +0x2544: ldp     d6, d7, [x19, #184]
    +0x2548: ldr     d4, [sp, #8944]
    +0x254c: str     d5, [sp, #8896]
    +0x2550: eor     v1.8b, v4.8b, v1.8b
    +0x2554: ldr     d4, [sp, #8960]
    +0x2558: eor     v6.8b, v16.8b, v6.8b
    +0x255c: ldp     d16, d0, [x19, #200]
    +0x2560: eor     v7.8b, v17.8b, v7.8b
    +0x2564: ldr     d17, [sp, #8936]
    +0x2568: str     d3, [sp, #8904]
    +0x256c: ldp     d3, d5, [x19, #232]
    +0x2570: str     d1, [sp, #8944]
    +0x2574: eor     v0.8b, v17.8b, v0.8b
    +0x2578: ldr     d17, [sp, #8952]
    +0x257c: str     d6, [sp, #8912]
    +0x2580: ldr     d6, [sp, #8968]
    +0x2584: str     d7, [sp, #8920]
    +0x2588: ldr     d7, [sp, #8976]
    +0x258c: eor     v2.8b, v17.8b, v2.8b
    +0x2590: eor     v3.8b, v4.8b, v3.8b
    +0x2594: ldr     d1, [x19, #264]
    +0x2598: str     d0, [sp, #8936]
    +0x259c: ldp     d4, d0, [x19, #248]
    +0x25a0: eor     v5.8b, v6.8b, v5.8b
    +0x25a4: ldr     d6, [sp, #8984]
    +0x25a8: eor     v16.8b, v18.8b, v16.8b
    +0x25ac: str     d2, [sp, #8952]
    +0x25b0: ldr     d2, [sp, #8992]
    +0x25b4: eor     v4.8b, v7.8b, v4.8b
    +0x25b8: eor     v0.8b, v6.8b, v0.8b
    +0x25bc: str     d3, [sp, #8960]
    +0x25c0: eor     v1.8b, v2.8b, v1.8b
    +0x25c4: str     d16, [sp, #8928]
    +0x25c8: str     d5, [sp, #8968]
    +0x25cc: str     d4, [sp, #8976]
    +0x25d0: str     d0, [sp, #8984]
    +0x25d4: str     d1, [sp, #8992]
    +0x25d8: bl      <mldsa_keccakf1600_permute>
    +0x25dc: ldp     d1, d2, [x19, #272]
    +0x25e0: add     x0, sp, #0x2, lsl #12
    +0x25e4: ldr     d0, [sp, #8864]
    +0x25e8: ldr     d3, [sp, #8872]
    +0x25ec: add     x0, x0, #0x2a0
    +0x25f0: ldr     d5, [sp, #8880]
    +0x25f4: ldr     d6, [sp, #8896]
    +0x25f8: ldr     d7, [sp, #8904]
    +0x25fc: eor     v0.8b, v0.8b, v1.8b
    +0x2600: eor     v1.8b, v3.8b, v2.8b
    +0x2604: ldr     d3, [sp, #8888]
    +0x2608: ldp     d4, d2, [x19, #288]
    +0x260c: ldr     d16, [sp, #8912]
    +0x2610: ldr     d17, [sp, #8920]
    +0x2614: ldr     d18, [sp, #8928]
    +0x2618: str     d0, [sp, #8864]
    +0x261c: eor     v4.8b, v5.8b, v4.8b
    +0x2620: eor     v2.8b, v3.8b, v2.8b
    +0x2624: str     d1, [sp, #8872]
    +0x2628: ldp     d5, d3, [x19, #304]
    +0x262c: str     d2, [sp, #8888]
    +0x2630: ldp     d1, d2, [x19, #352]
    +0x2634: eor     v5.8b, v6.8b, v5.8b
    +0x2638: eor     v3.8b, v7.8b, v3.8b
    +0x263c: str     d4, [sp, #8880]
    +0x2640: ldp     d6, d7, [x19, #320]
    +0x2644: ldr     d4, [sp, #8944]
    +0x2648: str     d5, [sp, #8896]
    +0x264c: eor     v1.8b, v4.8b, v1.8b
    +0x2650: ldr     d4, [sp, #8960]
    +0x2654: eor     v6.8b, v16.8b, v6.8b
    +0x2658: ldp     d16, d0, [x19, #336]
    +0x265c: eor     v7.8b, v17.8b, v7.8b
    +0x2660: ldr     d17, [sp, #8936]
    +0x2664: str     d3, [sp, #8904]
    +0x2668: ldp     d3, d5, [x19, #368]
    +0x266c: str     d1, [sp, #8944]
    +0x2670: eor     v0.8b, v17.8b, v0.8b
    +0x2674: ldr     d17, [sp, #8952]
    +0x2678: str     d6, [sp, #8912]
    +0x267c: ldr     d6, [sp, #8968]
    +0x2680: str     d7, [sp, #8920]
    +0x2684: ldr     d7, [sp, #8976]
    +0x2688: eor     v2.8b, v17.8b, v2.8b
    +0x268c: eor     v3.8b, v4.8b, v3.8b
    +0x2690: ldr     d1, [x19, #400]
    +0x2694: str     d0, [sp, #8936]
    +0x2698: ldp     d4, d0, [x19, #384]
    +0x269c: eor     v5.8b, v6.8b, v5.8b
    +0x26a0: ldr     d6, [sp, #8984]
    +0x26a4: eor     v16.8b, v18.8b, v16.8b
    +0x26a8: str     d2, [sp, #8952]
    +0x26ac: ldr     d2, [sp, #8992]
    +0x26b0: eor     v4.8b, v7.8b, v4.8b
    +0x26b4: eor     v0.8b, v6.8b, v0.8b
    +0x26b8: str     d3, [sp, #8960]
    +0x26bc: eor     v1.8b, v2.8b, v1.8b
    +0x26c0: str     d16, [sp, #8928]
    +0x26c4: str     d5, [sp, #8968]
    +0x26c8: str     d4, [sp, #8976]
    +0x26cc: str     d0, [sp, #8984]
    +0x26d0: str     d1, [sp, #8992]
    +0x26d4: bl      <mldsa_keccakf1600_permute>
    +0x26d8: ldp     d1, d2, [x19, #408]
    +0x26dc: add     x0, sp, #0x2, lsl #12
    +0x26e0: ldr     d0, [sp, #8864]
    +0x26e4: ldr     d3, [sp, #8872]
    +0x26e8: add     x0, x0, #0x2a0
    +0x26ec: ldr     d5, [sp, #8880]
    +0x26f0: ldr     d6, [sp, #8896]
    +0x26f4: ldr     d7, [sp, #8904]
    +0x26f8: eor     v0.8b, v0.8b, v1.8b
    +0x26fc: eor     v1.8b, v3.8b, v2.8b
    +0x2700: ldr     d3, [sp, #8888]
    +0x2704: ldp     d4, d2, [x19, #424]
    +0x2708: ldr     d16, [sp, #8912]
    +0x270c: ldr     d17, [sp, #8920]
    +0x2710: ldr     d18, [sp, #8928]
    +0x2714: str     d0, [sp, #8864]
    +0x2718: eor     v4.8b, v5.8b, v4.8b
    +0x271c: eor     v2.8b, v3.8b, v2.8b
    +0x2720: str     d1, [sp, #8872]
    +0x2724: ldp     d5, d3, [x19, #440]
    +0x2728: str     d2, [sp, #8888]
    +0x272c: ldp     d1, d2, [x19, #488]
    +0x2730: eor     v5.8b, v6.8b, v5.8b
    +0x2734: eor     v3.8b, v7.8b, v3.8b
    +0x2738: str     d4, [sp, #8880]
    +0x273c: ldp     d6, d7, [x19, #456]
    +0x2740: ldr     d4, [sp, #8944]
    +0x2744: eor     v1.8b, v4.8b, v1.8b
    +0x2748: str     d5, [sp, #8896]
    +0x274c: ldr     d4, [sp, #8960]
    +0x2750: eor     v6.8b, v16.8b, v6.8b
    +0x2754: ldp     d16, d0, [x19, #472]
    +0x2758: eor     v7.8b, v17.8b, v7.8b
    +0x275c: ldr     d17, [sp, #8936]
    +0x2760: str     d3, [sp, #8904]
    +0x2764: ldp     d3, d5, [x19, #504]
    +0x2768: str     d1, [sp, #8944]
    +0x276c: eor     v0.8b, v17.8b, v0.8b
    +0x2770: ldr     d17, [sp, #8952]
    +0x2774: str     d6, [sp, #8912]
    +0x2778: ldr     d6, [sp, #8968]
    +0x277c: str     d7, [sp, #8920]
    +0x2780: ldr     d7, [sp, #8976]
    +0x2784: eor     v2.8b, v17.8b, v2.8b
    +0x2788: eor     v3.8b, v4.8b, v3.8b
    +0x278c: ldr     d4, [x19, #520]
    +0x2790: eor     v5.8b, v6.8b, v5.8b
    +0x2794: str     d0, [sp, #8936]
    +0x2798: ldr     d0, [sp, #8984]
    +0x279c: ldr     d6, [x19, #528]
    +0x27a0: ldr     d1, [x19, #536]
    +0x27a4: eor     v16.8b, v18.8b, v16.8b
    +0x27a8: str     d2, [sp, #8952]
    +0x27ac: ldr     d2, [sp, #8992]
    +0x27b0: eor     v4.8b, v7.8b, v4.8b
    +0x27b4: eor     v0.8b, v0.8b, v6.8b
    +0x27b8: str     d3, [sp, #8960]
    +0x27bc: eor     v1.8b, v2.8b, v1.8b
    +0x27c0: str     d16, [sp, #8928]
    +0x27c4: str     d5, [sp, #8968]
    +0x27c8: str     d4, [sp, #8976]
    +0x27cc: str     d0, [sp, #8984]
    +0x27d0: str     d1, [sp, #8992]
    +0x27d4: bl      <mldsa_keccakf1600_permute>
    +0x27d8: ldr     d0, [x19, #544]
    +0x27dc: ldr     d1, [sp, #8864]
    +0x27e0: add     x0, sp, #0x2, lsl #12
    +0x27e4: ldr     d2, [x19, #552]
    +0x27e8: ldr     d3, [sp, #8872]
    +0x27ec: add     x0, x0, #0x2a0
    +0x27f0: eor     v0.8b, v1.8b, v0.8b
    +0x27f4: ldr     d4, [x19, #560]
    +0x27f8: ldr     d5, [sp, #8880]
    +0x27fc: eor     v1.8b, v3.8b, v2.8b
    +0x2800: ldr     d2, [x19, #568]
    +0x2804: ldr     d3, [sp, #8888]
    +0x2808: ldr     d7, [sp, #8904]
    +0x280c: eor     v4.8b, v5.8b, v4.8b
    +0x2810: ldr     d5, [x19, #576]
    +0x2814: eor     v2.8b, v3.8b, v2.8b
    +0x2818: ldr     d3, [x19, #584]
    +0x281c: ldr     d6, [sp, #8896]
    +0x2820: ldr     d17, [sp, #8920]
    +0x2824: ldr     d16, [sp, #8912]
    +0x2828: str     d0, [sp, #8864]
    +0x282c: eor     v3.8b, v7.8b, v3.8b
    +0x2830: ldr     d7, [x19, #600]
    +0x2834: eor     v5.8b, v6.8b, v5.8b
    +0x2838: ldr     d6, [x19, #592]
    +0x283c: ldr     d0, [sp, #8936]
    +0x2840: str     d1, [sp, #8872]
    +0x2844: eor     v7.8b, v17.8b, v7.8b
    +0x2848: ldr     d1, [x19, #616]
    +0x284c: str     d4, [sp, #8880]
    +0x2850: ldr     d4, [x19, #624]
    +0x2854: eor     v6.8b, v16.8b, v6.8b
    +0x2858: ldr     d17, [sp, #8944]
    +0x285c: eor     v0.8b, v0.8b, v1.8b
    +0x2860: str     d2, [sp, #8888]
    +0x2864: ldr     d1, [sp, #8952]
    +0x2868: eor     v2.8b, v17.8b, v4.8b
    +0x286c: ldr     d4, [x19, #632]
    +0x2870: str     d5, [sp, #8896]
    +0x2874: str     d3, [sp, #8904]
    +0x2878: ldr     d3, [x19, #640]
    +0x287c: ldr     d5, [sp, #8960]
    +0x2880: eor     v1.8b, v1.8b, v4.8b
    +0x2884: str     d6, [sp, #8912]
    +0x2888: ldr     d4, [sp, #8968]
    +0x288c: eor     v3.8b, v5.8b, v3.8b
    +0x2890: str     d7, [sp, #8920]
    +0x2894: ldr     d5, [x19, #648]
    +0x2898: ldr     d6, [x19, #656]
    +0x289c: ldr     d7, [sp, #8976]
    +0x28a0: ldr     d16, [x19, #608]
    +0x28a4: eor     v4.8b, v4.8b, v5.8b
    +0x28a8: ldr     d18, [sp, #8928]
    +0x28ac: str     d0, [sp, #8936]
    +0x28b0: eor     v5.8b, v7.8b, v6.8b
    +0x28b4: ldr     d0, [sp, #8984]
    +0x28b8: ldr     d6, [x19, #664]
    +0x28bc: eor     v16.8b, v18.8b, v16.8b
    +0x28c0: str     d2, [sp, #8944]
    +0x28c4: ldr     d2, [sp, #8992]
    +0x28c8: eor     v0.8b, v0.8b, v6.8b
    +0x28cc: str     d1, [sp, #8952]
    +0x28d0: ldr     d1, [x19, #672]
    +0x28d4: str     d3, [sp, #8960]
    +0x28d8: eor     v1.8b, v2.8b, v1.8b
    +0x28dc: str     d16, [sp, #8928]
    +0x28e0: str     d4, [sp, #8968]
    +0x28e4: str     d5, [sp, #8976]
    +0x28e8: str     d0, [sp, #8984]
    +0x28ec: str     d1, [sp, #8992]
    +0x28f0: bl      <mldsa_keccakf1600_permute>
    +0x28f4: ldr     d0, [x19, #680]
    +0x28f8: ldr     d1, [sp, #8864]
    +0x28fc: add     x0, sp, #0x2, lsl #12
    +0x2900: ldr     d2, [x19, #688]
    +0x2904: ldr     d3, [sp, #8872]
    +0x2908: add     x0, x0, #0x2a0
    +0x290c: eor     v0.8b, v1.8b, v0.8b
    +0x2910: ldr     d4, [x19, #696]
    +0x2914: ldr     d5, [sp, #8880]
    +0x2918: eor     v1.8b, v3.8b, v2.8b
    +0x291c: ldr     d2, [x19, #704]
    +0x2920: ldr     d3, [sp, #8888]
    +0x2924: ldr     d7, [sp, #8904]
    +0x2928: eor     v4.8b, v5.8b, v4.8b
    +0x292c: ldr     d5, [x19, #712]
    +0x2930: eor     v2.8b, v3.8b, v2.8b
    +0x2934: ldr     d3, [x19, #720]
    +0x2938: ldr     d6, [sp, #8896]
    +0x293c: ldr     d17, [sp, #8920]
    +0x2940: ldr     d16, [sp, #8912]
    +0x2944: str     d0, [sp, #8864]
    +0x2948: eor     v3.8b, v7.8b, v3.8b
    +0x294c: ldr     d7, [x19, #736]
    +0x2950: eor     v5.8b, v6.8b, v5.8b
    +0x2954: ldr     d6, [x19, #728]
    +0x2958: ldr     d0, [sp, #8936]
    +0x295c: str     d1, [sp, #8872]
    +0x2960: eor     v7.8b, v17.8b, v7.8b
    +0x2964: ldr     d1, [x19, #752]
    +0x2968: str     d4, [sp, #8880]
    +0x296c: ldr     d4, [x19, #760]
    +0x2970: eor     v6.8b, v16.8b, v6.8b
    +0x2974: ldr     d17, [sp, #8944]
    +0x2978: eor     v0.8b, v0.8b, v1.8b
    +0x297c: str     d2, [sp, #8888]
    +0x2980: ldr     d1, [sp, #8952]
    +0x2984: eor     v2.8b, v17.8b, v4.8b
    +0x2988: ldr     d4, [x19, #768]
    +0x298c: str     d5, [sp, #8896]
    +0x2990: str     d3, [sp, #8904]
    +0x2994: ldr     d3, [x19, #776]
    +0x2998: ldr     d5, [sp, #8960]
    +0x299c: eor     v1.8b, v1.8b, v4.8b
    +0x29a0: str     d6, [sp, #8912]
    +0x29a4: ldr     d4, [sp, #8968]
    +0x29a8: eor     v3.8b, v5.8b, v3.8b
    +0x29ac: str     d7, [sp, #8920]
    +0x29b0: ldr     d5, [x19, #784]
    +0x29b4: ldr     d6, [x19, #792]
    +0x29b8: ldr     d7, [sp, #8976]
    +0x29bc: ldr     d16, [x19, #744]
    +0x29c0: eor     v4.8b, v4.8b, v5.8b
    +0x29c4: ldr     d18, [sp, #8928]
    +0x29c8: str     d0, [sp, #8936]
    +0x29cc: eor     v5.8b, v7.8b, v6.8b
    +0x29d0: ldr     d0, [sp, #8984]
    +0x29d4: ldr     d6, [x19, #800]
    +0x29d8: eor     v16.8b, v18.8b, v16.8b
    +0x29dc: str     d2, [sp, #8944]
    +0x29e0: ldr     d2, [sp, #8992]
    +0x29e4: eor     v0.8b, v0.8b, v6.8b
    +0x29e8: str     d1, [sp, #8952]
    +0x29ec: ldr     d1, [x19, #808]
    +0x29f0: str     d3, [sp, #8960]
    +0x29f4: eor     v1.8b, v2.8b, v1.8b
    +0x29f8: str     d16, [sp, #8928]
    +0x29fc: str     d4, [sp, #8968]
    +0x2a00: str     d5, [sp, #8976]
    +0x2a04: str     d0, [sp, #8984]
    +0x2a08: str     d1, [sp, #8992]
    +0x2a0c: bl      <mldsa_keccakf1600_permute>
    +0x2a10: ldr     d0, [x19, #816]
    +0x2a14: ldr     d1, [sp, #8864]
    +0x2a18: add     x0, sp, #0x2, lsl #12
    +0x2a1c: ldr     d2, [x19, #824]
    +0x2a20: ldr     d3, [sp, #8872]
    +0x2a24: add     x0, x0, #0x2a0
    +0x2a28: eor     v0.8b, v1.8b, v0.8b
    +0x2a2c: ldr     d4, [x19, #832]
    +0x2a30: ldr     d5, [sp, #8880]
    +0x2a34: eor     v1.8b, v3.8b, v2.8b
    +0x2a38: ldr     d2, [x19, #840]
    +0x2a3c: ldr     d3, [sp, #8888]
    +0x2a40: ldr     d7, [sp, #8904]
    +0x2a44: eor     v4.8b, v5.8b, v4.8b
    +0x2a48: ldr     d5, [x19, #848]
    +0x2a4c: eor     v2.8b, v3.8b, v2.8b
    +0x2a50: ldr     d3, [x19, #856]
    +0x2a54: ldr     d6, [sp, #8896]
    +0x2a58: ldr     d17, [sp, #8920]
    +0x2a5c: ldr     d16, [sp, #8912]
    +0x2a60: str     d0, [sp, #8864]
    +0x2a64: eor     v3.8b, v7.8b, v3.8b
    +0x2a68: ldr     d7, [x19, #872]
    +0x2a6c: eor     v5.8b, v6.8b, v5.8b
    +0x2a70: ldr     d6, [x19, #864]
    +0x2a74: ldr     d0, [sp, #8936]
    +0x2a78: str     d1, [sp, #8872]
    +0x2a7c: eor     v7.8b, v17.8b, v7.8b
    +0x2a80: ldr     d1, [x19, #888]
    +0x2a84: str     d4, [sp, #8880]
    +0x2a88: ldr     d4, [x19, #896]
    +0x2a8c: eor     v6.8b, v16.8b, v6.8b
    +0x2a90: ldr     d17, [sp, #8944]
    +0x2a94: eor     v0.8b, v0.8b, v1.8b
    +0x2a98: str     d2, [sp, #8888]
    +0x2a9c: ldr     d1, [sp, #8952]
    +0x2aa0: eor     v2.8b, v17.8b, v4.8b
    +0x2aa4: ldr     d4, [x19, #904]
    +0x2aa8: str     d5, [sp, #8896]
    +0x2aac: str     d3, [sp, #8904]
    +0x2ab0: ldr     d3, [x19, #912]
    +0x2ab4: ldr     d5, [sp, #8960]
    +0x2ab8: eor     v1.8b, v1.8b, v4.8b
    +0x2abc: str     d6, [sp, #8912]
    +0x2ac0: ldr     d4, [sp, #8968]
    +0x2ac4: eor     v3.8b, v5.8b, v3.8b
    +0x2ac8: str     d7, [sp, #8920]
    +0x2acc: ldr     d5, [x19, #920]
    +0x2ad0: ldr     d6, [x19, #928]
    +0x2ad4: ldr     d7, [sp, #8976]
    +0x2ad8: ldr     d16, [x19, #880]
    +0x2adc: eor     v4.8b, v4.8b, v5.8b
    +0x2ae0: ldr     d18, [sp, #8928]
    +0x2ae4: str     d0, [sp, #8936]
    +0x2ae8: eor     v5.8b, v7.8b, v6.8b
    +0x2aec: ldr     d0, [sp, #8984]
    +0x2af0: ldr     d6, [x19, #936]
    +0x2af4: eor     v16.8b, v18.8b, v16.8b
    +0x2af8: str     d2, [sp, #8944]
    +0x2afc: ldr     d2, [sp, #8992]
    +0x2b00: eor     v0.8b, v0.8b, v6.8b
    +0x2b04: str     d1, [sp, #8952]
    +0x2b08: ldr     d1, [x19, #944]
    +0x2b0c: str     d3, [sp, #8960]
    +0x2b10: eor     v1.8b, v2.8b, v1.8b
    +0x2b14: str     d16, [sp, #8928]
    +0x2b18: str     d4, [sp, #8968]
    +0x2b1c: str     d5, [sp, #8976]
    +0x2b20: str     d0, [sp, #8984]
    +0x2b24: str     d1, [sp, #8992]
    +0x2b28: bl      <mldsa_keccakf1600_permute>
    +0x2b2c: ldr     d0, [x19, #952]
    +0x2b30: ldr     d1, [sp, #8864]
    +0x2b34: add     x0, sp, #0x2, lsl #12
    +0x2b38: ldr     d2, [x19, #960]
    +0x2b3c: ldr     d3, [sp, #8872]
    +0x2b40: add     x0, x0, #0x2a0
    +0x2b44: eor     v0.8b, v1.8b, v0.8b
    +0x2b48: ldr     d4, [x19, #968]
    +0x2b4c: ldr     d5, [sp, #8880]
    +0x2b50: eor     v1.8b, v3.8b, v2.8b
    +0x2b54: ldr     d2, [x19, #976]
    +0x2b58: ldr     d3, [sp, #8888]
    +0x2b5c: ldr     d7, [sp, #8904]
    +0x2b60: eor     v4.8b, v5.8b, v4.8b
    +0x2b64: ldr     d5, [x19, #984]
    +0x2b68: eor     v2.8b, v3.8b, v2.8b
    +0x2b6c: ldr     d3, [x19, #992]
    +0x2b70: ldr     d6, [sp, #8896]
    +0x2b74: ldr     d17, [sp, #8920]
    +0x2b78: ldr     d16, [sp, #8912]
    +0x2b7c: str     d0, [sp, #8864]
    +0x2b80: eor     v3.8b, v7.8b, v3.8b
    +0x2b84: ldr     d7, [x19, #1008]
    +0x2b88: eor     v5.8b, v6.8b, v5.8b
    +0x2b8c: ldr     d6, [x19, #1000]
    +0x2b90: ldr     d0, [sp, #8936]
    +0x2b94: str     d1, [sp, #8872]
    +0x2b98: eor     v7.8b, v17.8b, v7.8b
    +0x2b9c: ldr     d1, [x19, #1024]
    +0x2ba0: str     d4, [sp, #8880]
    +0x2ba4: ldr     d4, [x19, #1032]
    +0x2ba8: eor     v6.8b, v16.8b, v6.8b
    +0x2bac: ldr     d17, [sp, #8944]
    +0x2bb0: eor     v0.8b, v0.8b, v1.8b
    +0x2bb4: str     d2, [sp, #8888]
    +0x2bb8: ldr     d1, [sp, #8952]
    +0x2bbc: eor     v2.8b, v17.8b, v4.8b
    +0x2bc0: ldr     d4, [x19, #1040]
    +0x2bc4: str     d5, [sp, #8896]
    +0x2bc8: str     d3, [sp, #8904]
    +0x2bcc: ldr     d3, [x19, #1048]
    +0x2bd0: ldr     d5, [sp, #8960]
    +0x2bd4: eor     v1.8b, v1.8b, v4.8b
    +0x2bd8: str     d6, [sp, #8912]
    +0x2bdc: ldr     d4, [sp, #8968]
    +0x2be0: eor     v3.8b, v5.8b, v3.8b
    +0x2be4: str     d7, [sp, #8920]
    +0x2be8: ldr     d5, [x19, #1056]
    +0x2bec: ldr     d6, [x19, #1064]
    +0x2bf0: ldr     d7, [sp, #8976]
    +0x2bf4: ldr     d16, [x19, #1016]
    +0x2bf8: eor     v4.8b, v4.8b, v5.8b
    +0x2bfc: ldr     d18, [sp, #8928]
    +0x2c00: str     d0, [sp, #8936]
    +0x2c04: eor     v5.8b, v7.8b, v6.8b
    +0x2c08: ldr     d0, [sp, #8984]
    +0x2c0c: ldr     d6, [x19, #1072]
    +0x2c10: eor     v16.8b, v18.8b, v16.8b
    +0x2c14: str     d2, [sp, #8944]
    +0x2c18: ldr     d2, [sp, #8992]
    +0x2c1c: eor     v0.8b, v0.8b, v6.8b
    +0x2c20: str     d1, [sp, #8952]
    +0x2c24: ldr     d1, [x19, #1080]
    +0x2c28: str     d3, [sp, #8960]
    +0x2c2c: eor     v1.8b, v2.8b, v1.8b
    +0x2c30: str     d16, [sp, #8928]
    +0x2c34: str     d4, [sp, #8968]
    +0x2c38: str     d5, [sp, #8976]
    +0x2c3c: str     d0, [sp, #8984]
    +0x2c40: str     d1, [sp, #8992]
    +0x2c44: bl      <mldsa_keccakf1600_permute>
    +0x2c48: ldr     d0, [x19, #1088]
    +0x2c4c: ldr     d1, [sp, #8864]
    +0x2c50: add     x0, sp, #0x2, lsl #12
    +0x2c54: ldr     d2, [x19, #1096]
    +0x2c58: ldr     d3, [sp, #8872]
    +0x2c5c: add     x0, x0, #0x2a0
    +0x2c60: eor     v0.8b, v1.8b, v0.8b
    +0x2c64: ldr     d4, [x19, #1104]
    +0x2c68: ldr     d5, [sp, #8880]
    +0x2c6c: eor     v1.8b, v3.8b, v2.8b
    +0x2c70: ldr     d2, [x19, #1112]
    +0x2c74: ldr     d3, [sp, #8888]
    +0x2c78: ldr     d7, [sp, #8904]
    +0x2c7c: eor     v4.8b, v5.8b, v4.8b
    +0x2c80: ldr     d5, [x19, #1120]
    +0x2c84: eor     v2.8b, v3.8b, v2.8b
    +0x2c88: ldr     d3, [x19, #1128]
    +0x2c8c: ldr     d6, [sp, #8896]
    +0x2c90: ldr     d17, [sp, #8920]
    +0x2c94: ldr     d16, [sp, #8912]
    +0x2c98: str     d0, [sp, #8864]
    +0x2c9c: eor     v3.8b, v7.8b, v3.8b
    +0x2ca0: ldr     d7, [x19, #1144]
    +0x2ca4: eor     v5.8b, v6.8b, v5.8b
    +0x2ca8: ldr     d6, [x19, #1136]
    +0x2cac: ldr     d0, [sp, #8936]
    +0x2cb0: str     d1, [sp, #8872]
    +0x2cb4: eor     v7.8b, v17.8b, v7.8b
    +0x2cb8: ldr     d1, [x19, #1160]
    +0x2cbc: str     d4, [sp, #8880]
    +0x2cc0: ldr     d4, [x19, #1168]
    +0x2cc4: eor     v6.8b, v16.8b, v6.8b
    +0x2cc8: ldr     d17, [sp, #8944]
    +0x2ccc: eor     v0.8b, v0.8b, v1.8b
    +0x2cd0: str     d2, [sp, #8888]
    +0x2cd4: ldr     d1, [sp, #8952]
    +0x2cd8: eor     v2.8b, v17.8b, v4.8b
    +0x2cdc: ldr     d4, [x19, #1176]
    +0x2ce0: str     d5, [sp, #8896]
    +0x2ce4: str     d3, [sp, #8904]
    +0x2ce8: ldr     d3, [x19, #1184]
    +0x2cec: ldr     d5, [sp, #8960]
    +0x2cf0: eor     v1.8b, v1.8b, v4.8b
    +0x2cf4: str     d6, [sp, #8912]
    +0x2cf8: ldr     d4, [sp, #8968]
    +0x2cfc: eor     v3.8b, v5.8b, v3.8b
    +0x2d00: str     d7, [sp, #8920]
    +0x2d04: ldr     d5, [x19, #1192]
    +0x2d08: ldr     d6, [x19, #1200]
    +0x2d0c: ldr     d7, [sp, #8976]
    +0x2d10: ldr     d16, [x19, #1152]
    +0x2d14: eor     v4.8b, v4.8b, v5.8b
    +0x2d18: ldr     d18, [sp, #8928]
    +0x2d1c: str     d0, [sp, #8936]
    +0x2d20: eor     v5.8b, v7.8b, v6.8b
    +0x2d24: ldr     d0, [sp, #8984]
    +0x2d28: ldr     d6, [x19, #1208]
    +0x2d2c: eor     v16.8b, v18.8b, v16.8b
    +0x2d30: str     d2, [sp, #8944]
    +0x2d34: ldr     d2, [sp, #8992]
    +0x2d38: eor     v0.8b, v0.8b, v6.8b
    +0x2d3c: str     d1, [sp, #8952]
    +0x2d40: ldr     d1, [x19, #1216]
    +0x2d44: str     d3, [sp, #8960]
    +0x2d48: eor     v1.8b, v2.8b, v1.8b
    +0x2d4c: str     d16, [sp, #8928]
    +0x2d50: str     d4, [sp, #8968]
    +0x2d54: str     d5, [sp, #8976]
    +0x2d58: str     d0, [sp, #8984]
    +0x2d5c: str     d1, [sp, #8992]
    +0x2d60: bl      <mldsa_keccakf1600_permute>
    +0x2d64: ldr     d0, [x19, #1224]
    +0x2d68: ldr     d1, [sp, #8864]
    +0x2d6c: add     x0, sp, #0x2, lsl #12
    +0x2d70: ldr     d2, [x19, #1232]
    +0x2d74: ldr     d3, [sp, #8872]
    +0x2d78: add     x0, x0, #0x2a0
    +0x2d7c: eor     v0.8b, v1.8b, v0.8b
    +0x2d80: ldr     d4, [x19, #1240]
    +0x2d84: ldr     d5, [sp, #8880]
    +0x2d88: eor     v1.8b, v3.8b, v2.8b
    +0x2d8c: ldr     d2, [x19, #1248]
    +0x2d90: ldr     d3, [sp, #8888]
    +0x2d94: ldr     d7, [sp, #8904]
    +0x2d98: eor     v4.8b, v5.8b, v4.8b
    +0x2d9c: ldr     d5, [x19, #1256]
    +0x2da0: eor     v2.8b, v3.8b, v2.8b
    +0x2da4: ldr     d3, [x19, #1264]
    +0x2da8: ldr     d6, [sp, #8896]
    +0x2dac: ldr     d17, [sp, #8920]
    +0x2db0: ldr     d16, [sp, #8912]
    +0x2db4: str     d0, [sp, #8864]
    +0x2db8: eor     v3.8b, v7.8b, v3.8b
    +0x2dbc: ldr     d7, [x19, #1280]
    +0x2dc0: eor     v5.8b, v6.8b, v5.8b
    +0x2dc4: ldr     d6, [x19, #1272]
    +0x2dc8: ldr     d0, [sp, #8936]
    +0x2dcc: str     d1, [sp, #8872]
    +0x2dd0: eor     v7.8b, v17.8b, v7.8b
    +0x2dd4: ldr     d1, [x19, #1296]
    +0x2dd8: str     d4, [sp, #8880]
    +0x2ddc: ldr     d4, [x19, #1304]
    +0x2de0: eor     v6.8b, v16.8b, v6.8b
    +0x2de4: ldr     d17, [sp, #8944]
    +0x2de8: eor     v0.8b, v0.8b, v1.8b
    +0x2dec: str     d2, [sp, #8888]
    +0x2df0: ldr     d1, [sp, #8952]
    +0x2df4: eor     v2.8b, v17.8b, v4.8b
    +0x2df8: ldr     d4, [x19, #1312]
    +0x2dfc: str     d5, [sp, #8896]
    +0x2e00: str     d3, [sp, #8904]
    +0x2e04: ldr     d3, [x19, #1320]
    +0x2e08: ldr     d5, [sp, #8960]
    +0x2e0c: eor     v1.8b, v1.8b, v4.8b
    +0x2e10: str     d6, [sp, #8912]
    +0x2e14: ldr     d4, [sp, #8968]
    +0x2e18: eor     v3.8b, v5.8b, v3.8b
    +0x2e1c: str     d7, [sp, #8920]
    +0x2e20: ldr     d5, [x19, #1328]
    +0x2e24: ldr     d6, [x19, #1336]
    +0x2e28: ldr     d7, [sp, #8976]
    +0x2e2c: ldr     d16, [x19, #1288]
    +0x2e30: eor     v4.8b, v4.8b, v5.8b
    +0x2e34: ldr     d18, [sp, #8928]
    +0x2e38: str     d0, [sp, #8936]
    +0x2e3c: eor     v5.8b, v7.8b, v6.8b
    +0x2e40: ldr     d0, [sp, #8984]
    +0x2e44: ldr     d6, [x19, #1344]
    +0x2e48: eor     v16.8b, v18.8b, v16.8b
    +0x2e4c: str     d2, [sp, #8944]
    +0x2e50: ldr     d2, [sp, #8992]
    +0x2e54: eor     v0.8b, v0.8b, v6.8b
    +0x2e58: str     d1, [sp, #8952]
    +0x2e5c: ldr     d1, [x19, #1352]
    +0x2e60: str     d3, [sp, #8960]
    +0x2e64: eor     v1.8b, v2.8b, v1.8b
    +0x2e68: str     d16, [sp, #8928]
    +0x2e6c: str     d4, [sp, #8968]
    +0x2e70: str     d5, [sp, #8976]
    +0x2e74: str     d0, [sp, #8984]
    +0x2e78: str     d1, [sp, #8992]
    +0x2e7c: bl      <mldsa_keccakf1600_permute>
    +0x2e80: ldr     d0, [x19, #1360]
    +0x2e84: ldr     d1, [sp, #8864]
    +0x2e88: add     x0, sp, #0x2, lsl #12
    +0x2e8c: ldr     d2, [x19, #1368]
    +0x2e90: ldr     d3, [sp, #8872]
    +0x2e94: add     x0, x0, #0x2a0
    +0x2e98: eor     v0.8b, v1.8b, v0.8b
    +0x2e9c: ldr     d4, [x19, #1376]
    +0x2ea0: ldr     d5, [sp, #8880]
    +0x2ea4: eor     v1.8b, v3.8b, v2.8b
    +0x2ea8: ldr     d2, [x19, #1384]
    +0x2eac: ldr     d3, [sp, #8888]
    +0x2eb0: ldr     d7, [sp, #8904]
    +0x2eb4: eor     v4.8b, v5.8b, v4.8b
    +0x2eb8: ldr     d5, [x19, #1392]
    +0x2ebc: eor     v2.8b, v3.8b, v2.8b
    +0x2ec0: ldr     d3, [x19, #1400]
    +0x2ec4: ldr     d6, [sp, #8896]
    +0x2ec8: ldr     d17, [sp, #8920]
    +0x2ecc: ldr     d16, [sp, #8912]
    +0x2ed0: str     d0, [sp, #8864]
    +0x2ed4: eor     v3.8b, v7.8b, v3.8b
    +0x2ed8: ldr     d7, [x19, #1416]
    +0x2edc: eor     v5.8b, v6.8b, v5.8b
    +0x2ee0: ldr     d6, [x19, #1408]
    +0x2ee4: ldr     d0, [sp, #8936]
    +0x2ee8: str     d1, [sp, #8872]
    +0x2eec: eor     v7.8b, v17.8b, v7.8b
    +0x2ef0: ldr     d1, [x19, #1432]
    +0x2ef4: str     d4, [sp, #8880]
    +0x2ef8: ldr     d4, [x19, #1440]
    +0x2efc: eor     v6.8b, v16.8b, v6.8b
    +0x2f00: ldr     d17, [sp, #8944]
    +0x2f04: eor     v0.8b, v0.8b, v1.8b
    +0x2f08: str     d2, [sp, #8888]
    +0x2f0c: ldr     d1, [sp, #8952]
    +0x2f10: eor     v2.8b, v17.8b, v4.8b
    +0x2f14: ldr     d4, [x19, #1448]
    +0x2f18: str     d5, [sp, #8896]
    +0x2f1c: str     d3, [sp, #8904]
    +0x2f20: ldr     d3, [x19, #1456]
    +0x2f24: ldr     d5, [sp, #8960]
    +0x2f28: eor     v1.8b, v1.8b, v4.8b
    +0x2f2c: str     d6, [sp, #8912]
    +0x2f30: ldr     d4, [sp, #8968]
    +0x2f34: eor     v3.8b, v5.8b, v3.8b
    +0x2f38: str     d7, [sp, #8920]
    +0x2f3c: ldr     d5, [x19, #1464]
    +0x2f40: ldr     d6, [x19, #1472]
    +0x2f44: ldr     d7, [sp, #8976]
    +0x2f48: ldr     d16, [x19, #1424]
    +0x2f4c: eor     v4.8b, v4.8b, v5.8b
    +0x2f50: ldr     d18, [sp, #8928]
    +0x2f54: str     d0, [sp, #8936]
    +0x2f58: eor     v5.8b, v7.8b, v6.8b
    +0x2f5c: ldr     d0, [sp, #8984]
    +0x2f60: ldr     d6, [x19, #1480]
    +0x2f64: eor     v16.8b, v18.8b, v16.8b
    +0x2f68: str     d2, [sp, #8944]
    +0x2f6c: ldr     d2, [sp, #8992]
    +0x2f70: eor     v0.8b, v0.8b, v6.8b
    +0x2f74: str     d1, [sp, #8952]
    +0x2f78: ldr     d1, [x19, #1488]
    +0x2f7c: str     d3, [sp, #8960]
    +0x2f80: eor     v1.8b, v2.8b, v1.8b
    +0x2f84: str     d16, [sp, #8928]
    +0x2f88: str     d4, [sp, #8968]
    +0x2f8c: str     d5, [sp, #8976]
    +0x2f90: str     d0, [sp, #8984]
    +0x2f94: str     d1, [sp, #8992]
    +0x2f98: bl      <mldsa_keccakf1600_permute>
    +0x2f9c: ldr     d0, [x19, #1496]
    +0x2fa0: ldr     d1, [sp, #8864]
    +0x2fa4: add     x0, sp, #0x2, lsl #12
    +0x2fa8: ldr     d2, [x19, #1504]
    +0x2fac: ldr     d3, [sp, #8872]
    +0x2fb0: add     x0, x0, #0x2a0
    +0x2fb4: eor     v0.8b, v1.8b, v0.8b
    +0x2fb8: ldr     d4, [x19, #1512]
    +0x2fbc: ldr     d5, [sp, #8880]
    +0x2fc0: eor     v1.8b, v3.8b, v2.8b
    +0x2fc4: ldr     d2, [x19, #1520]
    +0x2fc8: ldr     d3, [sp, #8888]
    +0x2fcc: ldr     d7, [sp, #8904]
    +0x2fd0: eor     v4.8b, v5.8b, v4.8b
    +0x2fd4: ldr     d5, [x19, #1528]
    +0x2fd8: eor     v2.8b, v3.8b, v2.8b
    +0x2fdc: ldr     d3, [x19, #1536]
    +0x2fe0: ldr     d6, [sp, #8896]
    +0x2fe4: ldr     d17, [sp, #8920]
    +0x2fe8: ldr     d16, [sp, #8912]
    +0x2fec: str     d0, [sp, #8864]
    +0x2ff0: eor     v3.8b, v7.8b, v3.8b
    +0x2ff4: ldr     d7, [x19, #1552]
    +0x2ff8: eor     v5.8b, v6.8b, v5.8b
    +0x2ffc: ldr     d6, [x19, #1544]
    +0x3000: ldr     d0, [sp, #8936]
    +0x3004: str     d1, [sp, #8872]
    +0x3008: eor     v7.8b, v17.8b, v7.8b
    +0x300c: ldr     d1, [x19, #1568]
    +0x3010: str     d4, [sp, #8880]
    +0x3014: ldr     d4, [x19, #1576]
    +0x3018: eor     v6.8b, v16.8b, v6.8b
    +0x301c: ldr     d17, [sp, #8944]
    +0x3020: eor     v0.8b, v0.8b, v1.8b
    +0x3024: str     d2, [sp, #8888]
    +0x3028: ldr     d1, [sp, #8952]
    +0x302c: eor     v2.8b, v17.8b, v4.8b
    +0x3030: ldr     d4, [x19, #1584]
    +0x3034: str     d5, [sp, #8896]
    +0x3038: str     d3, [sp, #8904]
    +0x303c: ldr     d3, [x19, #1592]
    +0x3040: ldr     d5, [sp, #8960]
    +0x3044: eor     v1.8b, v1.8b, v4.8b
    +0x3048: str     d6, [sp, #8912]
    +0x304c: ldr     d4, [sp, #8968]
    +0x3050: eor     v3.8b, v5.8b, v3.8b
    +0x3054: str     d7, [sp, #8920]
    +0x3058: ldr     d5, [x19, #1600]
    +0x305c: ldr     d6, [x19, #1608]
    +0x3060: ldr     d7, [sp, #8976]
    +0x3064: ldr     d16, [x19, #1560]
    +0x3068: eor     v4.8b, v4.8b, v5.8b
    +0x306c: ldr     d18, [sp, #8928]
    +0x3070: str     d0, [sp, #8936]
    +0x3074: eor     v5.8b, v7.8b, v6.8b
    +0x3078: ldr     d0, [sp, #8984]
    +0x307c: ldr     d6, [x19, #1616]
    +0x3080: eor     v16.8b, v18.8b, v16.8b
    +0x3084: str     d2, [sp, #8944]
    +0x3088: ldr     d2, [sp, #8992]
    +0x308c: eor     v0.8b, v0.8b, v6.8b
    +0x3090: str     d1, [sp, #8952]
    +0x3094: ldr     d1, [x19, #1624]
    +0x3098: str     d3, [sp, #8960]
    +0x309c: eor     v1.8b, v2.8b, v1.8b
    +0x30a0: str     d16, [sp, #8928]
    +0x30a4: str     d4, [sp, #8968]
    +0x30a8: str     d5, [sp, #8976]
    +0x30ac: str     d0, [sp, #8984]
    +0x30b0: str     d1, [sp, #8992]
    +0x30b4: bl      <mldsa_keccakf1600_permute>
    +0x30b8: ldr     d0, [x19, #1632]
    +0x30bc: ldr     d1, [sp, #8864]
    +0x30c0: add     x0, sp, #0x2, lsl #12
    +0x30c4: ldr     d2, [x19, #1640]
    +0x30c8: ldr     d3, [sp, #8872]
    +0x30cc: add     x0, x0, #0x2a0
    +0x30d0: eor     v0.8b, v1.8b, v0.8b
    +0x30d4: ldr     d4, [x19, #1648]
    +0x30d8: ldr     d5, [sp, #8880]
    +0x30dc: eor     v1.8b, v3.8b, v2.8b
    +0x30e0: ldr     d2, [x19, #1656]
    +0x30e4: ldr     d3, [sp, #8888]
    +0x30e8: ldr     d7, [sp, #8904]
    +0x30ec: eor     v4.8b, v5.8b, v4.8b
    +0x30f0: ldr     d5, [x19, #1664]
    +0x30f4: eor     v2.8b, v3.8b, v2.8b
    +0x30f8: ldr     d3, [x19, #1672]
    +0x30fc: ldr     d6, [sp, #8896]
    +0x3100: ldr     d17, [sp, #8920]
    +0x3104: ldr     d16, [sp, #8912]
    +0x3108: str     d0, [sp, #8864]
    +0x310c: eor     v3.8b, v7.8b, v3.8b
    +0x3110: ldr     d7, [x19, #1688]
    +0x3114: eor     v5.8b, v6.8b, v5.8b
    +0x3118: ldr     d6, [x19, #1680]
    +0x311c: ldr     d0, [sp, #8936]
    +0x3120: str     d1, [sp, #8872]
    +0x3124: eor     v7.8b, v17.8b, v7.8b
    +0x3128: ldr     d1, [x19, #1704]
    +0x312c: str     d4, [sp, #8880]
    +0x3130: ldr     d4, [x19, #1712]
    +0x3134: eor     v6.8b, v16.8b, v6.8b
    +0x3138: ldr     d17, [sp, #8944]
    +0x313c: eor     v0.8b, v0.8b, v1.8b
    +0x3140: str     d2, [sp, #8888]
    +0x3144: ldr     d1, [sp, #8952]
    +0x3148: eor     v2.8b, v17.8b, v4.8b
    +0x314c: ldr     d4, [x19, #1720]
    +0x3150: str     d5, [sp, #8896]
    +0x3154: str     d3, [sp, #8904]
    +0x3158: ldr     d3, [x19, #1728]
    +0x315c: ldr     d5, [sp, #8960]
    +0x3160: eor     v1.8b, v1.8b, v4.8b
    +0x3164: str     d6, [sp, #8912]
    +0x3168: ldr     d4, [sp, #8968]
    +0x316c: eor     v3.8b, v5.8b, v3.8b
    +0x3170: str     d7, [sp, #8920]
    +0x3174: ldr     d5, [x19, #1736]
    +0x3178: ldr     d6, [x19, #1744]
    +0x317c: ldr     d7, [sp, #8976]
    +0x3180: ldr     d16, [x19, #1696]
    +0x3184: eor     v4.8b, v4.8b, v5.8b
    +0x3188: ldr     d18, [sp, #8928]
    +0x318c: str     d0, [sp, #8936]
    +0x3190: eor     v5.8b, v7.8b, v6.8b
    +0x3194: ldr     d0, [sp, #8984]
    +0x3198: ldr     d6, [x19, #1752]
    +0x319c: eor     v16.8b, v18.8b, v16.8b
    +0x31a0: str     d2, [sp, #8944]
    +0x31a4: ldr     d2, [sp, #8992]
    +0x31a8: eor     v0.8b, v0.8b, v6.8b
    +0x31ac: str     d1, [sp, #8952]
    +0x31b0: ldr     d1, [x19, #1760]
    +0x31b4: str     d3, [sp, #8960]
    +0x31b8: eor     v1.8b, v2.8b, v1.8b
    +0x31bc: str     d16, [sp, #8928]
    +0x31c0: str     d4, [sp, #8968]
    +0x31c4: str     d5, [sp, #8976]
    +0x31c8: str     d0, [sp, #8984]
    +0x31cc: str     d1, [sp, #8992]
    +0x31d0: bl      <mldsa_keccakf1600_permute>
    +0x31d4: ldr     d0, [x19, #1768]
    +0x31d8: ldr     d1, [sp, #8864]
    +0x31dc: add     x0, sp, #0x2, lsl #12
    +0x31e0: ldr     d2, [x19, #1776]
    +0x31e4: ldr     d3, [sp, #8872]
    +0x31e8: add     x0, x0, #0x2a0
    +0x31ec: eor     v0.8b, v1.8b, v0.8b
    +0x31f0: ldr     d4, [x19, #1784]
    +0x31f4: ldr     d5, [sp, #8880]
    +0x31f8: eor     v1.8b, v3.8b, v2.8b
    +0x31fc: ldr     d2, [x19, #1792]
    +0x3200: ldr     d3, [sp, #8888]
    +0x3204: ldr     d7, [sp, #8904]
    +0x3208: eor     v4.8b, v5.8b, v4.8b
    +0x320c: ldr     d5, [x19, #1800]
    +0x3210: eor     v2.8b, v3.8b, v2.8b
    +0x3214: ldr     d3, [x19, #1808]
    +0x3218: ldr     d6, [sp, #8896]
    +0x321c: ldr     d17, [sp, #8920]
    +0x3220: ldr     d16, [sp, #8912]
    +0x3224: str     d0, [sp, #8864]
    +0x3228: eor     v3.8b, v7.8b, v3.8b
    +0x322c: ldr     d7, [x19, #1824]
    +0x3230: eor     v5.8b, v6.8b, v5.8b
    +0x3234: ldr     d6, [x19, #1816]
    +0x3238: ldr     d0, [sp, #8936]
    +0x323c: str     d1, [sp, #8872]
    +0x3240: eor     v7.8b, v17.8b, v7.8b
    +0x3244: ldr     d1, [x19, #1840]
    +0x3248: str     d4, [sp, #8880]
    +0x324c: ldr     d4, [x19, #1848]
    +0x3250: eor     v6.8b, v16.8b, v6.8b
    +0x3254: ldr     d17, [sp, #8944]
    +0x3258: eor     v0.8b, v0.8b, v1.8b
    +0x325c: str     d2, [sp, #8888]
    +0x3260: ldr     d1, [sp, #8952]
    +0x3264: eor     v2.8b, v17.8b, v4.8b
    +0x3268: ldr     d4, [x19, #1856]
    +0x326c: str     d5, [sp, #8896]
    +0x3270: str     d3, [sp, #8904]
    +0x3274: ldr     d3, [x19, #1864]
    +0x3278: ldr     d5, [sp, #8960]
    +0x327c: eor     v1.8b, v1.8b, v4.8b
    +0x3280: str     d6, [sp, #8912]
    +0x3284: ldr     d4, [sp, #8968]
    +0x3288: eor     v3.8b, v5.8b, v3.8b
    +0x328c: str     d7, [sp, #8920]
    +0x3290: ldr     d5, [x19, #1872]
    +0x3294: ldr     d6, [x19, #1880]
    +0x3298: ldr     d7, [sp, #8976]
    +0x329c: ldr     d16, [x19, #1832]
    +0x32a0: eor     v4.8b, v4.8b, v5.8b
    +0x32a4: ldr     d18, [sp, #8928]
    +0x32a8: str     d0, [sp, #8936]
    +0x32ac: eor     v5.8b, v7.8b, v6.8b
    +0x32b0: ldr     d0, [sp, #8984]
    +0x32b4: ldr     d6, [x19, #1888]
    +0x32b8: eor     v16.8b, v18.8b, v16.8b
    +0x32bc: str     d2, [sp, #8944]
    +0x32c0: ldr     d2, [sp, #8992]
    +0x32c4: eor     v0.8b, v0.8b, v6.8b
    +0x32c8: str     d1, [sp, #8952]
    +0x32cc: ldr     d1, [x19, #1896]
    +0x32d0: str     d3, [sp, #8960]
    +0x32d4: eor     v1.8b, v2.8b, v1.8b
    +0x32d8: str     d16, [sp, #8928]
    +0x32dc: str     d4, [sp, #8968]
    +0x32e0: str     d5, [sp, #8976]
    +0x32e4: str     d0, [sp, #8984]
    +0x32e8: str     d1, [sp, #8992]
    +0x32ec: bl      <mldsa_keccakf1600_permute>
    +0x32f0: ldr     q0, [x19, #1904]
    +0x32f4: ldr     q1, [sp, #8864]
    +0x32f8: add     x0, sp, #0x2, lsl #12
    +0x32fc: ldr     q2, [x19, #1920]
    +0x3300: ldrb    w8, [x20, #48]
    +0x3304: add     x0, x0, #0x2a0
    +0x3308: ldr     q3, [sp, #8880]
    +0x330c: eor     v0.16b, v1.16b, v0.16b
    +0x3310: ldr     q1, [x19, #1936]
    +0x3314: ldr     q4, [sp, #8896]
    +0x3318: ldrb    w9, [x20, #135]
    +0x331c: eor     w8, w8, #0x1f
    +0x3320: eor     v2.16b, v3.16b, v2.16b
    +0x3324: strb    w8, [x20, #48]
    +0x3328: eor     v1.16b, v4.16b, v1.16b
    +0x332c: eor     w8, w9, #0x80
    +0x3330: str     q0, [sp, #8864]
    +0x3334: strb    w8, [x20, #135]
    +0x3338: mov     w8, #0x88
    +0x333c: str     q2, [sp, #8880]
    +0x3340: str     q1, [sp, #8896]
    +0x3344: str     w8, [sp, #9064]
    +0x3348: bl      <mldsa_keccakf1600_permute>
    +0x334c: ldr     q0, [sp, #8864]
    +0x3350: ldr     q1, [sp, #8880]
    +0x3354: add     x8, sp, #0x2, lsl #12
    +0x3358: ldr     q2, [sp, #8912]
    +0x335c: add     x8, x8, #0x2a0
    +0x3360: orr     w11, w28, w22
    +0x3364: str     q0, [sp, #8704]
    +0x3368: ldr     q0, [sp, #8896]
    +0x336c: orr     w12, w21, w27
    +0x3370: str     q1, [sp, #8720]
    +0x3374: str     q0, [sp, #8736]
    +0x3378: movi    v0.2d, #0x0
    +0x337c: str     q2, [sp, #8752]
    +0x3380: str     q0, [sp, #8928]
    +0x3384: str     q0, [sp, #8944]
    +0x3388: str     q0, [sp, #8960]
    +0x338c: str     q0, [sp, #8976]
    +0x3390: str     q0, [sp, #8992]
    +0x3394: str     q0, [sp, #9008]
    +0x3398: str     q0, [sp, #9024]
    +0x339c: str     q0, [sp, #9040]
    +0x33a0: str     q0, [sp, #9056]
    +0x33a4: str     q0, [sp, #8864]
    +0x33a8: str     q0, [sp, #8880]
    +0x33ac: str     q0, [sp, #8896]
    +0x33b0: str     q0, [sp, #8912]
    +0x33b4: ldr     q0, [sp, #8768]
    +0x33b8: ldr     q1, [sp, #8784]
    +0x33bc: ldr     q2, [sp, #8704]
    +0x33c0: ldr     q3, [sp, #8720]
    +0x33c4: ldr     q4, [sp, #8800]
    +0x33c8: ldr     q5, [sp, #8816]
    +0x33cc: ldr     q6, [sp, #8736]
    +0x33d0: ldr     q7, [sp, #8752]
    +0x33d4: eor     v0.16b, v2.16b, v0.16b
    +0x33d8: eor     v1.16b, v3.16b, v1.16b
    +0x33dc: ldr     x10, [sp, #24]
    +0x33e0: eor     v2.16b, v6.16b, v4.16b
    +0x33e4: eor     v3.16b, v7.16b, v5.16b
    +0x33e8: orr     v4.16b, v2.16b, v0.16b
    +0x33ec: orr     v5.16b, v1.16b, v3.16b
    +0x33f0: eor     v0.16b, v0.16b, v2.16b
    +0x33f4: eor     v1.16b, v3.16b, v1.16b
    +0x33f8: orr     v4.16b, v5.16b, v4.16b
    +0x33fc: eor     v0.16b, v1.16b, v0.16b
    +0x3400: mov     d2, v4.d[1]
    +0x3404: orr     v1.8b, v4.8b, v2.8b
    +0x3408: mov     d2, v0.d[1]
    +0x340c: fmov    x8, d1
    +0x3410: eor     v0.8b, v0.8b, v2.8b
    +0x3414: orr     x8, x8, x8, lsr #32
    +0x3418: lsr     x9, x8, #16
    +0x341c: orr     w8, w8, w9
    +0x3420: fmov    x9, d0
    +0x3424: orr     w8, w8, w8, lsr #8
    +0x3428: eor     x9, x9, x9, lsr #32
    +0x342c: sub     x8, x10, w8, uxtb
    +0x3430: eor     x9, x9, x9, lsr #16
    +0x3434: lsr     x8, x8, #32
    +0x3438: lsr     x10, x9, #8
    +0x343c: eor     w9, w9, w10
    +0x3440: and     w10, w9, #0xff
    +0x3444: eor     w8, w8, w9
    +0x3448: ldr     w9, [sp, #20]
    +0x344c: orr     w9, w26, w9
    +0x3450: eor     w8, w8, w10
    +0x3454: eor     w10, w25, w24
    +0x3458: orr     w9, w9, w11
    +0x345c: orr     w11, w12, w23
    +0x3460: orr     w9, w9, w11
    +0x3464: orr     w8, w9, w8
    +0x3468: orr     w8, w10, w8
    +0x346c: tst     w8, #0xff
    +0x3470: b.eq    <mldsa65_pk_from_sk+0x348c>
    +0x3474: mov     x0, x19
    +0x3478: mov     w1, wzr
    +0x347c: mov     w2, #0x7a0
    +0x3480: bl      <memset>
    +0x3484: mov     w19, #0xfffffff9
    +0x3488: b       <mldsa65_pk_from_sk+0x3490>
    +0x348c: mov     w19, wzr
    +0x3490: add     x0, sp, #0x20
    +0x3494: mov     w1, wzr
    +0x3498: mov     w2, #0x9c0
    +0x349c: add     x20, sp, #0x20
    +0x34a0: bl      <memset>
    +0x34a4: add     x0, sp, #0x9e0
    +0x34a8: mov     w1, wzr
    +0x34ac: mov     w2, #0x400
    +0x34b0: add     x20, sp, #0x9e0
    +0x34b4: bl      <memset>
    +0x34b8: add     x0, sp, #0xde0
    +0x34bc: mov     w1, wzr
    +0x34c0: mov     w2, #0x1400
    +0x34c4: add     x20, sp, #0xde0
    +0x34c8: bl      <memset>
    +0x34cc: movi    v0.2d, #0x0
    +0x34d0: add     x8, sp, #0x2, lsl #12
    +0x34d4: add     x8, x8, #0x1e0
    +0x34d8: str     q0, [sp, #8688]
    +0x34dc: str     q0, [sp, #8672]
    +0x34e0: add     x8, sp, #0x2, lsl #12
    +0x34e4: str     q0, [sp, #8752]
    +0x34e8: str     q0, [sp, #8736]
    +0x34ec: add     x8, x8, #0x200
    +0x34f0: str     q0, [sp, #8720]
    +0x34f4: str     q0, [sp, #8704]
    +0x34f8: add     x8, sp, #0x2, lsl #12
    +0x34fc: str     q0, [sp, #8816]
    +0x3500: str     q0, [sp, #8800]
    +0x3504: add     x8, x8, #0x240
    +0x3508: str     q0, [sp, #8784]
    +0x350c: str     q0, [sp, #8768]
    +0x3510: add     x8, sp, #0x2, lsl #12
    +0x3514: str     q0, [sp, #8848]
    +0x3518: add     x8, x8, #0x280
    +0x351c: str     q0, [sp, #8832]
    +0x3520: adrp    x8, <page>
    +0x3524: ldr     x8, [x8, #4088]
    +0x3528: ldr     x9, [sp, #9080]
    +0x352c: ldr     x8, [x8]
    +0x3530: cmp     x8, x9
    +0x3534: b.ne    <mldsa65_pk_from_sk+0x3584>
    +0x3538: mov     w0, w19
    +0x353c: mov     sp, x29
    +0x3540: ldp     x20, x19, [sp, #80]
    +0x3544: ldp     x22, x21, [sp, #64]
    +0x3548: ldp     x24, x23, [sp, #48]
    +0x354c: ldp     x26, x25, [sp, #32]
    +0x3550: ldp     x28, x27, [sp, #16]
    +0x3554: ldp     x29, x30, [sp], #96
    +0x3558: mov     x1, #0x0
    +0x355c: mov     x2, #0x0
    +0x3560: mov     x3, #0x0
    +0x3564: mov     x4, #0x0
    +0x3568: mov     x8, #0x0
    +0x356c: mov     x9, #0x0
    +0x3570: mov     x10, #0x0
    +0x3574: mov     x11, #0x0
    +0x3578: mov     x12, #0x0
    +0x357c: mov     x13, #0x0
    +0x3580: ret     
    +0x3584: bl      <__stack_chk_fail>

    memset@plt:
       +0x0: adrp    x16, <page>
       +0x4: ldr     x17, [x16, #4072]
       +0x8: add     x16, x16, #0xfe8
       +0xc: br      x17
 ***)

let MLDSA_NATIVE_PK_FROM_SK_65_CLANG23_O3_MONO_REDUCED_RAM_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
   [layout_range "mldsa65_pk_from_sk";
    layout_range "plt_memset"];;

(* ------------------------------------------------------------------------- *)
(* Correctness, assuming the contracts for memset and memcpy. The secret key at sk is    *)
(* the 4032 bytes skb; if it passes the checks, mld_pk_from_sk_valid, the    *)
(* public key at pk becomes mld_pk_from_sk_pk and the result is 0, and       *)
(* otherwise the public key is zeroed and the result is MLD_ERR_INVALID_KEY  *)
(* (-7 as a 32-bit integer). The expansion of the matrix from rho is assumed *)
(* to terminate. The stack is the 9216 bytes of the function and the 5312   *)
(* of the callees below them.                                                *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_PK_FROM_SK_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!mf mc ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev
     ==> !pk sk skb guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          32768 <= val stackpointer /\ val(stackpointer:int64) < 2 EXP 63 /\
          mld_matrix_terminates 6 5 (mld_sk_rho skb) /\
          nonoverlapping (pk,1952) (word_sub stackpointer (word 14528),14528) /\
          ALLPAIRS nonoverlapping
           [(pk,1952); (word_sub stackpointer (word 14528),14528)]
           [(sk,4032); (word pc,libmldsa_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                    read PC s = word (pc + mldsa65_pk_from_sk) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [pk; sk] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    (!j. j < 4032
                         ==> read(memory :> bytes8(word_add sk (word j))) s =
                             skb j))
               (\s. read PC s = returnaddress /\
                    C_RETURN s =
                    (if mld_pk_from_sk_valid 6 5 4 mld_polyeta_unpack_4 128
                          skb
                     then word 0 else word 4294967289) /\
                    (!j. j < 1952
                         ==> read(memory :> bytes8(word_add pk (word j))) s =
                             if mld_pk_from_sk_valid 6 5 4
                                  mld_polyeta_unpack_4 128 skb
                             then mld_pk_from_sk_pk 5 mld_polyeta_unpack_4 128
                                   skb j
                             else word 0))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(pk,1952);
                  memory :> bytes(word_sub stackpointer (word 14528),14528)])`;;

let MLDSA_NATIVE_PK_FROM_SK_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLDSA_NATIVE_PK_FROM_SK_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, rho, the result of the checks,    *)
(* the address of memset and the stack, with all accesses within the         *)
(* arguments, the stack, the GOT entries and the stack guard, the region     *)
(* (ea,el) that memset may read and the constants of the callees, and the    *)
(* writes within the public key and the stack.                               *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_PK_FROM_SK_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT =
  `!mf mc ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev
     ==> exists f_events.
          forall e pk sk skb guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          32768 <= val stackpointer /\ val(stackpointer:int64) < 2 EXP 63 /\
          mld_matrix_terminates 6 5 (mld_sk_rho skb) /\
          nonoverlapping (pk,1952) (word_sub stackpointer (word 14528),14528) /\
          ALLPAIRS nonoverlapping
           [(pk,1952); (word_sub stackpointer (word 14528),14528)]
           [(sk,4032); (word pc,libmldsa_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                    read PC s = word (pc + mldsa65_pk_from_sk) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [pk; sk] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    (!j. j < 4032
                         ==> read(memory :> bytes8(word_add sk (word j))) s =
                             skb j) /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    C_RETURN s =
                    (if mld_pk_from_sk_valid 6 5 4 mld_polyeta_unpack_4 128
                          skb
                     then word 0 else word 4294967289) /\
                    (!j. j < 1952
                         ==> read(memory :> bytes8(word_add pk (word j))) s =
                             if mld_pk_from_sk_valid 6 5 4
                                  mld_polyeta_unpack_4 128 skb
                             then mld_pk_from_sk_pk 5 mld_polyeta_unpack_4 128
                                   skb j
                             else word 0) /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events pk sk (mld_sk_rho skb)
                              (mld_pk_from_sk_valid 6 5 4 mld_polyeta_unpack_4
                                128 skb)
                              guard mf mc pc (word_sub stackpointer (word 14528))
                              returnaddress /\
                       memaccess_inbounds e2
                        [sk,4032; pk,1952;
                         word_sub stackpointer (word 14528),14528;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; word(pc + got_memcpy),8; ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192;
                         word(pc + rodata_mld_zetas),1024;
                         word(pc + mldsa65_pk_from_sk_consts),64;
                         word(pc + mld_compute_pack_t0_t165_consts),272]
                        [pk,1952; word_sub stackpointer (word 14528),14528]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(pk,1952);
                  memory :> bytes(word_sub stackpointer (word 14528),14528)])`;;

let MLDSA_NATIVE_PK_FROM_SK_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_PK_FROM_SK_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_PK_FROM_SK_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT =
  `!mf mc ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev
     ==> exists f_events.
          forall e pk sk skb guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          32768 <= val stackpointer /\ val(stackpointer:int64) < 2 EXP 63 /\
          mld_matrix_terminates 6 5 (mld_sk_rho skb) /\
          nonoverlapping (pk,1952) (word_sub stackpointer (word 14528),14528) /\
          ALLPAIRS nonoverlapping
           [(pk,1952); (word_sub stackpointer (word 14528),14528)]
           [(sk,4032); (word pc,libmldsa_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                    read PC s = word (pc + mldsa65_pk_from_sk) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [pk; sk] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    (!j. j < 4032
                         ==> read(memory :> bytes8(word_add sk (word j))) s =
                             skb j) /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events pk sk (mld_sk_rho skb)
                              (mld_pk_from_sk_valid 6 5 4 mld_polyeta_unpack_4
                                128 skb)
                              guard mf mc pc (word_sub stackpointer (word 14528))
                              returnaddress /\
                       memaccess_inbounds e2
                        [sk,4032; pk,1952;
                         word_sub stackpointer (word 14528),14528;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; word(pc + got_memcpy),8; ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192;
                         word(pc + rodata_mld_zetas),1024;
                         word(pc + mldsa65_pk_from_sk_consts),64;
                         word(pc + mld_compute_pack_t0_t165_consts),272]
                        [pk,1952; word_sub stackpointer (word 14528),14528]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(pk,1952);
                  memory :> bytes(word_sub stackpointer (word 14528),14528)])`;;

let MLDSA_NATIVE_PK_FROM_SK_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_PK_FROM_SK_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT;;
