(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The public key of a secret key: the statement. This is the code for       *)
(* mldsa87_pk_from_sk (mld_sign_pk_from_sk in sign.c) from mldsa-native's    *)
(* portable C implementation compiled by clang 23 with -O3 as one            *)
(* translation unit with MLD_CONFIG_REDUCE_RAM (see mldsa_native/README.md). *)
(* It copies rho, the key and tr from the secret key to the stack, unpacks   *)
(* the seven polynomials of s1 with mldsa87_polyeta_unpack and checks them   *)
(* with mldsa87_polyvecl_chknorm, unpacks the eight polynomials of s2 one at *)
(* a time and checks each with an inlined loop, transforms s1 with           *)
(* mldsa_poly_ntt, recomputes t1 into the public key and t0 into a buffer    *)
(* with mld_compute_pack_t0_t187, compares t0 with that in the secret key    *)
(* with an inlined constant-time comparison (a loop of 104 passes of vector  *)
(* instructions), hashes the public key with an inlined SHAKE256 (twenty     *)
(* calls of mldsa_keccakf1600_permute) and compares the hash with tr, all in *)
(* constant time, and then zeroes the public key with memset if a check      *)
(* failed and its buffers with memset and stores. It is verified in the      *)
(* whole image (see libmldsa.ml) against mld_pk_from_sk_pk and               *)
(* mld_pk_from_sk_valid of common/mldsa_native_sign.ml, using the theorems   *)
(* for the callees and the contracts memset_full_contract and                *)
(* memcpy_full_contract of utils/mlkem_native_libc_full.ml (memcpy is used   *)
(* by compute_pack through the expansion of the matrix), assuming that the   *)
(* expansion of the matrix terminates (mld_matrix_terminates), and shown to  *)
(* be constant time and memory safe, with the events depending on rho, which *)
(* is part of the public key, and on the result of the checks, which the C   *)
(* code declassifies. The stack is the 12096 bytes of the function and the   *)
(* 5312 of the callees below them.                                           *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native.ml";;
needs "arm/proofs/utils/mlkem_native_libc_full.ml";;
needs "common/mldsa_native_sign.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/polyvecl_chknorm_87_spec.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/compute_pack_t0_t1_87_spec.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/libmldsa.ml";;

(*** The code in the image, and the PLT stub for memset:

    mldsa87_pk_from_sk:
       +0x0: stp     x29, x30, [sp, #-96]!
       +0x4: stp     x28, x27, [sp, #16]
       +0x8: stp     x26, x25, [sp, #32]
       +0xc: stp     x24, x23, [sp, #48]
      +0x10: stp     x22, x21, [sp, #64]
      +0x14: stp     x20, x19, [sp, #80]
      +0x18: mov     x29, sp
      +0x1c: sub     x9, sp, #0x2, lsl #12
      +0x20: sub     x9, x9, #0xec0
      +0x24: and     x9, x9, #0xffffffffffffffe0
      +0x28: sub     sp, sp, #0x1, lsl #12
      +0x2c: cmp     sp, x9
      +0x30: b.le    <mldsa87_pk_from_sk+0x44>
      +0x34: ldr     xzr, [sp]
      +0x38: sub     sp, sp, #0x1, lsl #12
      +0x3c: cmp     sp, x9
      +0x40: b.gt    <mldsa87_pk_from_sk+0x34>
      +0x44: mov     sp, x9
      +0x48: adrp    x8, <page>
      +0x4c: ldr     xzr, [sp]
      +0x50: mov     x19, x0
      +0x54: ldr     x8, [x8, #4088]
      +0x58: add     x0, sp, #0x1, lsl #12
      +0x5c: mov     x21, x1
      +0x60: add     x0, x0, #0x120
      +0x64: add     x20, sp, #0x1, lsl #12
      +0x68: ldr     x8, [x8]
      +0x6c: add     x20, x20, #0x120
      +0x70: str     x8, [sp, #11960]
      +0x74: ldp     q0, q1, [x1]
      +0x78: str     q0, [sp, #11712]
      +0x7c: ldp     q0, q2, [x1, #32]
      +0x80: str     q1, [sp, #11728]
      +0x84: str     q0, [sp, #11552]
      +0x88: ldp     q1, q0, [x1, #96]
      +0x8c: str     q2, [sp, #11568]
      +0x90: str     q0, [sp, #11696]
      +0x94: ldp     q0, q2, [x1, #64]
      +0x98: add     x1, x1, #0x80
      +0x9c: str     q1, [sp, #11680]
      +0xa0: str     q2, [sp, #11664]
      +0xa4: str     q0, [sp, #11648]
      +0xa8: bl      <mldsa87_polyeta_unpack>
      +0xac: add     x0, x20, #0x400
      +0xb0: add     x1, x21, #0xe0
      +0xb4: bl      <mldsa87_polyeta_unpack>
      +0xb8: add     x0, x20, #0x800
      +0xbc: add     x1, x21, #0x140
      +0xc0: bl      <mldsa87_polyeta_unpack>
      +0xc4: add     x0, x20, #0xc00
      +0xc8: add     x1, x21, #0x1a0
      +0xcc: bl      <mldsa87_polyeta_unpack>
      +0xd0: add     x0, x20, #0x1, lsl #12
      +0xd4: add     x1, x21, #0x200
      +0xd8: bl      <mldsa87_polyeta_unpack>
      +0xdc: mov     w8, #0x1400
      +0xe0: add     x1, x21, #0x260
      +0xe4: add     x0, x20, x8
      +0xe8: bl      <mldsa87_polyeta_unpack>
      +0xec: mov     w8, #0x1800
      +0xf0: add     x1, x21, #0x2c0
      +0xf4: add     x0, x20, x8
      +0xf8: bl      <mldsa87_polyeta_unpack>
      +0xfc: add     x0, sp, #0x1, lsl #12
     +0x100: mov     w1, #0x3
     +0x104: add     x0, x0, #0x120
     +0x108: bl      <mldsa87_polyvecl_chknorm>
     +0x10c: str     w0, [sp, #28]
     +0x110: add     x0, sp, #0xd20
     +0x114: add     x1, x21, #0x320
     +0x118: add     x20, sp, #0xd20
     +0x11c: bl      <mldsa87_polyeta_unpack>
     +0x120: mov     x8, xzr
     +0x124: mov     w13, wzr
     +0x128: mov     w9, #0x2
     +0x12c: ldrsw   x10, [x20, x8]
     +0x130: add     x8, x8, #0x4
     +0x134: cmp     x8, #0x400
     +0x138: mov     w11, w10
     +0x13c: lsr     x10, x10, #31
     +0x140: neg     w12, w11
     +0x144: bic     w11, w11, w10
     +0x148: and     w10, w12, w10
     +0x14c: orr     w10, w10, w11
     +0x150: sub     w10, w9, w10
     +0x154: sxtw    x10, w10
     +0x158: lsr     x10, x10, #31
     +0x15c: orr     w13, w13, w10
     +0x160: b.ne    <mldsa87_pk_from_sk+0x12c>
     +0x164: add     x0, sp, #0xd20
     +0x168: add     x1, x21, #0x380
     +0x16c: str     w13, [sp, #24]
     +0x170: add     x20, sp, #0xd20
     +0x174: bl      <mldsa87_polyeta_unpack>
     +0x178: mov     x8, xzr
     +0x17c: mov     w24, wzr
     +0x180: mov     w9, #0x2
     +0x184: ldrsw   x10, [x20, x8]
     +0x188: add     x8, x8, #0x4
     +0x18c: cmp     x8, #0x400
     +0x190: mov     w11, w10
     +0x194: lsr     x10, x10, #31
     +0x198: neg     w12, w11
     +0x19c: bic     w11, w11, w10
     +0x1a0: and     w10, w12, w10
     +0x1a4: orr     w10, w10, w11
     +0x1a8: sub     w10, w9, w10
     +0x1ac: sxtw    x10, w10
     +0x1b0: lsr     x10, x10, #31
     +0x1b4: orr     w24, w24, w10
     +0x1b8: b.ne    <mldsa87_pk_from_sk+0x184>
     +0x1bc: add     x0, sp, #0xd20
     +0x1c0: add     x1, x21, #0x3e0
     +0x1c4: add     x20, sp, #0xd20
     +0x1c8: bl      <mldsa87_polyeta_unpack>
     +0x1cc: mov     x8, xzr
     +0x1d0: mov     w25, wzr
     +0x1d4: mov     w9, #0x2
     +0x1d8: ldrsw   x10, [x20, x8]
     +0x1dc: add     x8, x8, #0x4
     +0x1e0: cmp     x8, #0x400
     +0x1e4: mov     w11, w10
     +0x1e8: lsr     x10, x10, #31
     +0x1ec: neg     w12, w11
     +0x1f0: bic     w11, w11, w10
     +0x1f4: and     w10, w12, w10
     +0x1f8: orr     w10, w10, w11
     +0x1fc: sub     w10, w9, w10
     +0x200: sxtw    x10, w10
     +0x204: lsr     x10, x10, #31
     +0x208: orr     w25, w25, w10
     +0x20c: b.ne    <mldsa87_pk_from_sk+0x1d8>
     +0x210: add     x0, sp, #0xd20
     +0x214: add     x1, x21, #0x440
     +0x218: add     x20, sp, #0xd20
     +0x21c: bl      <mldsa87_polyeta_unpack>
     +0x220: mov     x8, xzr
     +0x224: mov     w26, wzr
     +0x228: mov     w9, #0x2
     +0x22c: ldrsw   x10, [x20, x8]
     +0x230: add     x8, x8, #0x4
     +0x234: cmp     x8, #0x400
     +0x238: mov     w11, w10
     +0x23c: lsr     x10, x10, #31
     +0x240: neg     w12, w11
     +0x244: bic     w11, w11, w10
     +0x248: and     w10, w12, w10
     +0x24c: orr     w10, w10, w11
     +0x250: sub     w10, w9, w10
     +0x254: sxtw    x10, w10
     +0x258: lsr     x10, x10, #31
     +0x25c: orr     w26, w26, w10
     +0x260: b.ne    <mldsa87_pk_from_sk+0x22c>
     +0x264: add     x0, sp, #0xd20
     +0x268: add     x1, x21, #0x4a0
     +0x26c: add     x20, sp, #0xd20
     +0x270: bl      <mldsa87_polyeta_unpack>
     +0x274: mov     x8, xzr
     +0x278: mov     w27, wzr
     +0x27c: mov     w9, #0x2
     +0x280: ldrsw   x10, [x20, x8]
     +0x284: add     x8, x8, #0x4
     +0x288: cmp     x8, #0x400
     +0x28c: mov     w11, w10
     +0x290: lsr     x10, x10, #31
     +0x294: neg     w12, w11
     +0x298: bic     w11, w11, w10
     +0x29c: and     w10, w12, w10
     +0x2a0: orr     w10, w10, w11
     +0x2a4: sub     w10, w9, w10
     +0x2a8: sxtw    x10, w10
     +0x2ac: lsr     x10, x10, #31
     +0x2b0: orr     w27, w27, w10
     +0x2b4: b.ne    <mldsa87_pk_from_sk+0x280>
     +0x2b8: add     x0, sp, #0xd20
     +0x2bc: add     x1, x21, #0x500
     +0x2c0: add     x20, sp, #0xd20
     +0x2c4: bl      <mldsa87_polyeta_unpack>
     +0x2c8: mov     x8, xzr
     +0x2cc: mov     w28, wzr
     +0x2d0: mov     w9, #0x2
     +0x2d4: ldrsw   x10, [x20, x8]
     +0x2d8: add     x8, x8, #0x4
     +0x2dc: cmp     x8, #0x400
     +0x2e0: mov     w11, w10
     +0x2e4: lsr     x10, x10, #31
     +0x2e8: neg     w12, w11
     +0x2ec: bic     w11, w11, w10
     +0x2f0: and     w10, w12, w10
     +0x2f4: orr     w10, w10, w11
     +0x2f8: sub     w10, w9, w10
     +0x2fc: sxtw    x10, w10
     +0x300: lsr     x10, x10, #31
     +0x304: orr     w28, w28, w10
     +0x308: b.ne    <mldsa87_pk_from_sk+0x2d4>
     +0x30c: add     x0, sp, #0xd20
     +0x310: add     x1, x21, #0x560
     +0x314: add     x22, sp, #0xd20
     +0x318: bl      <mldsa87_polyeta_unpack>
     +0x31c: mov     x8, xzr
     +0x320: mov     w20, wzr
     +0x324: mov     w9, #0x2
     +0x328: ldrsw   x10, [x22, x8]
     +0x32c: add     x8, x8, #0x4
     +0x330: cmp     x8, #0x400
     +0x334: mov     w11, w10
     +0x338: lsr     x10, x10, #31
     +0x33c: neg     w12, w11
     +0x340: bic     w11, w11, w10
     +0x344: and     w10, w12, w10
     +0x348: orr     w10, w10, w11
     +0x34c: sub     w10, w9, w10
     +0x350: sxtw    x10, w10
     +0x354: lsr     x10, x10, #31
     +0x358: orr     w20, w20, w10
     +0x35c: b.ne    <mldsa87_pk_from_sk+0x328>
     +0x360: add     x0, sp, #0xd20
     +0x364: add     x1, x21, #0x5c0
     +0x368: add     x22, sp, #0xd20
     +0x36c: bl      <mldsa87_polyeta_unpack>
     +0x370: mov     x8, xzr
     +0x374: mov     w23, wzr
     +0x378: mov     w9, #0x2
     +0x37c: ldrsw   x10, [x22, x8]
     +0x380: add     x8, x8, #0x4
     +0x384: cmp     x8, #0x400
     +0x388: mov     w11, w10
     +0x38c: lsr     x10, x10, #31
     +0x390: neg     w12, w11
     +0x394: bic     w11, w11, w10
     +0x398: and     w10, w12, w10
     +0x39c: orr     w10, w10, w11
     +0x3a0: sub     w10, w9, w10
     +0x3a4: sxtw    x10, w10
     +0x3a8: lsr     x10, x10, #31
     +0x3ac: orr     w23, w23, w10
     +0x3b0: b.ne    <mldsa87_pk_from_sk+0x37c>
     +0x3b4: add     x0, sp, #0x1, lsl #12
     +0x3b8: add     x0, x0, #0x120
     +0x3bc: bl      <mldsa_poly_ntt>
     +0x3c0: add     x22, sp, #0x1, lsl #12
     +0x3c4: add     x22, x22, #0x120
     +0x3c8: add     x0, x22, #0x400
     +0x3cc: bl      <mldsa_poly_ntt>
     +0x3d0: add     x0, x22, #0x800
     +0x3d4: bl      <mldsa_poly_ntt>
     +0x3d8: add     x0, x22, #0xc00
     +0x3dc: bl      <mldsa_poly_ntt>
     +0x3e0: add     x0, x22, #0x1, lsl #12
     +0x3e4: bl      <mldsa_poly_ntt>
     +0x3e8: mov     w8, #0x1400
     +0x3ec: add     x0, x22, x8
     +0x3f0: bl      <mldsa_poly_ntt>
     +0x3f4: mov     w8, #0x1800
     +0x3f8: add     x0, x22, x8
     +0x3fc: bl      <mldsa_poly_ntt>
     +0x400: ldr     q0, [sp, #11712]
     +0x404: ldr     q1, [sp, #11728]
     +0x408: add     x2, sp, #0x1, lsl #12
     +0x40c: add     x4, sp, #0x2, lsl #12
     +0x410: add     x0, x19, #0x20
     +0x414: add     x1, sp, #0x20
     +0x418: add     x2, x2, #0x120
     +0x41c: add     x3, x21, #0x320
     +0x420: add     x4, x4, #0xdc0
     +0x424: stp     q0, q1, [x19]
     +0x428: add     x22, sp, #0x20
     +0x42c: bl      <mld_compute_pack_t0_t187>
     +0x430: movi    v2.2d, #0x0
     +0x434: adrp    x8, <page>
     +0x438: movi    v0.2d, #0x0
     +0x43c: movi    v3.2d, #0x0
     +0x440: movi    v1.2d, #0x0
     +0x444: ldr     q17, [x8, #1472]
     +0x448: movi    v4.2d, #0x0
     +0x44c: movi    v5.2d, #0x0
     +0x450: adrp    x8, <page>
     +0x454: movi    v7.2d, #0x0
     +0x458: movi    v6.2d, #0x0
     +0x45c: adrp    x9, <page>
     +0x460: movi    v16.2d, #0x0
     +0x464: movi    v18.2d, #0x0
     +0x468: adrp    x10, <page>
     +0x46c: ldr     q19, [x8, #1488]
     +0x470: ldr     q20, [x9, #1504]
     +0x474: ldr     q21, [x10, #1520]
     +0x478: mov     x8, xzr
     +0x47c: add     x9, x22, x8
     +0x480: add     x10, x21, x8
     +0x484: add     x8, x8, #0x20
     +0x488: ldp     q23, q24, [x9]
     +0x48c: ldr     q22, [x10, #1568]
     +0x490: ldr     q25, [x10, #1584]
     +0x494: cmp     x8, #0xd00
     +0x498: eor     v22.16b, v22.16b, v23.16b
     +0x49c: eor     v23.16b, v25.16b, v24.16b
     +0x4a0: tbl     v24.16b, {v22.16b}, v19.16b
     +0x4a4: tbl     v25.16b, {v22.16b}, v20.16b
     +0x4a8: tbl     v26.16b, {v22.16b}, v21.16b
     +0x4ac: tbl     v27.16b, {v22.16b}, v17.16b
     +0x4b0: tbl     v28.16b, {v23.16b}, v20.16b
     +0x4b4: tbl     v29.16b, {v23.16b}, v21.16b
     +0x4b8: tbl     v30.16b, {v23.16b}, v17.16b
     +0x4bc: tbl     v31.16b, {v23.16b}, v19.16b
     +0x4c0: orr     v2.16b, v22.16b, v2.16b
     +0x4c4: orr     v18.16b, v23.16b, v18.16b
     +0x4c8: eor     v4.16b, v4.16b, v26.16b
     +0x4cc: eor     v1.16b, v1.16b, v25.16b
     +0x4d0: eor     v3.16b, v3.16b, v24.16b
     +0x4d4: eor     v0.16b, v0.16b, v27.16b
     +0x4d8: eor     v16.16b, v16.16b, v29.16b
     +0x4dc: eor     v6.16b, v6.16b, v28.16b
     +0x4e0: eor     v7.16b, v7.16b, v31.16b
     +0x4e4: eor     v5.16b, v5.16b, v30.16b
     +0x4e8: b.ne    <mldsa87_pk_from_sk+0x47c>
     +0x4ec: orr     v2.16b, v18.16b, v2.16b
     +0x4f0: eor     v3.16b, v7.16b, v3.16b
     +0x4f4: mov     x10, xzr
     +0x4f8: eor     v4.16b, v16.16b, v4.16b
     +0x4fc: eor     v0.16b, v5.16b, v0.16b
     +0x500: str     xzr, [sp, #8]
     +0x504: eor     v1.16b, v6.16b, v1.16b
     +0x508: movi    v17.2d, #0x0
     +0x50c: add     x22, sp, #0x2, lsl #12
     +0x510: mov     d5, v2.d[1]
     +0x514: add     x22, x22, #0xde0
     +0x518: add     x0, sp, #0x2, lsl #12
     +0x51c: add     x0, x0, #0xde0
     +0x520: eor     v0.16b, v0.16b, v1.16b
     +0x524: eor     v1.16b, v3.16b, v4.16b
     +0x528: orr     v2.8b, v2.8b, v5.8b
     +0x52c: eor     v0.16b, v0.16b, v1.16b
     +0x530: fmov    x8, d2
     +0x534: mov     d1, v0.d[1]
     +0x538: orr     x8, x8, x8, lsr #32
     +0x53c: lsr     x9, x8, #16
     +0x540: eor     v0.8b, v0.8b, v1.8b
     +0x544: orr     w8, w8, w9
     +0x548: orr     w8, w8, w8, lsr #8
     +0x54c: fmov    x9, d0
     +0x550: sub     x8, x10, w8, uxtb
     +0x554: lsr     x10, x9, #32
     +0x558: lsr     x8, x8, #32
     +0x55c: eor     w9, w9, w10
     +0x560: eor     w21, w8, w9
     +0x564: str     w9, [sp, #20]
     +0x568: str     q17, [sp, #11744]
     +0x56c: stur    q17, [x22, #188]
     +0x570: ldp     d0, d1, [x19]
     +0x574: str     q17, [sp, #11776]
     +0x578: ldp     d2, d3, [x19, #16]
     +0x57c: ldr     d4, [sp, #11752]
     +0x580: ldp     d5, d6, [x19, #32]
     +0x584: str     q17, [sp, #11760]
     +0x588: ldr     d16, [sp, #11776]
     +0x58c: str     q17, [sp, #11792]
     +0x590: ldr     d7, [sp, #11768]
     +0x594: eor     v1.8b, v4.8b, v1.8b
     +0x598: str     d0, [sp, #11744]
     +0x59c: ldp     d0, d4, [x19, #48]
     +0x5a0: str     d2, [sp, #11760]
     +0x5a4: eor     v2.8b, v16.8b, v5.8b
     +0x5a8: ldr     d5, [sp, #11792]
     +0x5ac: ldr     d16, [sp, #11800]
     +0x5b0: eor     v3.8b, v7.8b, v3.8b
     +0x5b4: ldr     d7, [sp, #11784]
     +0x5b8: str     q17, [sp, #11808]
     +0x5bc: eor     v0.8b, v5.8b, v0.8b
     +0x5c0: eor     v4.8b, v16.8b, v4.8b
     +0x5c4: ldp     d5, d16, [x19, #64]
     +0x5c8: eor     v6.8b, v7.8b, v6.8b
     +0x5cc: ldr     d7, [sp, #11808]
     +0x5d0: str     q17, [sp, #11824]
     +0x5d4: str     d1, [sp, #11752]
     +0x5d8: ldr     d1, [sp, #11816]
     +0x5dc: eor     v5.8b, v7.8b, v5.8b
     +0x5e0: str     d3, [sp, #11768]
     +0x5e4: ldp     d3, d7, [x19, #80]
     +0x5e8: str     d2, [sp, #11776]
     +0x5ec: ldr     d2, [sp, #11824]
     +0x5f0: eor     v1.8b, v1.8b, v16.8b
     +0x5f4: str     d0, [sp, #11792]
     +0x5f8: ldr     d0, [sp, #11832]
     +0x5fc: str     q17, [sp, #11840]
     +0x600: str     d6, [sp, #11784]
     +0x604: ldp     d6, d16, [x19, #96]
     +0x608: eor     v2.8b, v2.8b, v3.8b
     +0x60c: str     q17, [sp, #11856]
     +0x610: eor     v0.8b, v0.8b, v7.8b
     +0x614: str     d4, [sp, #11800]
     +0x618: ldr     d7, [sp, #11848]
     +0x61c: ldr     d3, [sp, #11840]
     +0x620: str     d5, [sp, #11808]
     +0x624: ldp     d4, d5, [x19, #112]
     +0x628: str     d1, [sp, #11816]
     +0x62c: ldr     d1, [sp, #11856]
     +0x630: eor     v3.8b, v3.8b, v6.8b
     +0x634: str     q17, [sp, #11872]
     +0x638: str     d2, [sp, #11824]
     +0x63c: eor     v2.8b, v7.8b, v16.8b
     +0x640: eor     v1.8b, v1.8b, v4.8b
     +0x644: str     d0, [sp, #11832]
     +0x648: ldr     d0, [sp, #11864]
     +0x64c: ldr     d4, [x19, #128]
     +0x650: ldr     d6, [sp, #11872]
     +0x654: str     q17, [sp, #11920]
     +0x658: eor     v0.8b, v0.8b, v5.8b
     +0x65c: str     d2, [sp, #11848]
     +0x660: eor     v2.8b, v6.8b, v4.8b
     +0x664: str     q17, [sp, #11904]
     +0x668: str     q17, [sp, #11888]
     +0x66c: str     d3, [sp, #11840]
     +0x670: str     d1, [sp, #11856]
     +0x674: str     d0, [sp, #11864]
     +0x678: str     d2, [sp, #11872]
     +0x67c: bl      <mldsa_keccakf1600_permute>
     +0x680: ldp     d1, d2, [x19, #136]
     +0x684: add     x0, sp, #0x2, lsl #12
     +0x688: ldr     d0, [sp, #11744]
     +0x68c: ldr     d3, [sp, #11752]
     +0x690: add     x0, x0, #0xde0
     +0x694: ldr     d5, [sp, #11760]
     +0x698: ldr     d6, [sp, #11776]
     +0x69c: ldr     d7, [sp, #11784]
     +0x6a0: eor     v0.8b, v0.8b, v1.8b
     +0x6a4: eor     v1.8b, v3.8b, v2.8b
     +0x6a8: ldr     d3, [sp, #11768]
     +0x6ac: ldp     d4, d2, [x19, #152]
     +0x6b0: ldr     d16, [sp, #11792]
     +0x6b4: ldr     d17, [sp, #11800]
     +0x6b8: ldr     d18, [sp, #11808]
     +0x6bc: str     d0, [sp, #11744]
     +0x6c0: eor     v4.8b, v5.8b, v4.8b
     +0x6c4: eor     v2.8b, v3.8b, v2.8b
     +0x6c8: str     d1, [sp, #11752]
     +0x6cc: ldp     d5, d3, [x19, #168]
     +0x6d0: str     d2, [sp, #11768]
     +0x6d4: ldp     d1, d2, [x19, #216]
     +0x6d8: eor     v5.8b, v6.8b, v5.8b
     +0x6dc: eor     v3.8b, v7.8b, v3.8b
     +0x6e0: str     d4, [sp, #11760]
     +0x6e4: ldp     d6, d7, [x19, #184]
     +0x6e8: ldr     d4, [sp, #11824]
     +0x6ec: str     d5, [sp, #11776]
     +0x6f0: eor     v1.8b, v4.8b, v1.8b
     +0x6f4: ldr     d4, [sp, #11840]
     +0x6f8: eor     v6.8b, v16.8b, v6.8b
     +0x6fc: ldp     d16, d0, [x19, #200]
     +0x700: eor     v7.8b, v17.8b, v7.8b
     +0x704: ldr     d17, [sp, #11816]
     +0x708: str     d3, [sp, #11784]
     +0x70c: ldp     d3, d5, [x19, #232]
     +0x710: str     d1, [sp, #11824]
     +0x714: eor     v0.8b, v17.8b, v0.8b
     +0x718: ldr     d17, [sp, #11832]
     +0x71c: str     d6, [sp, #11792]
     +0x720: ldr     d6, [sp, #11848]
     +0x724: str     d7, [sp, #11800]
     +0x728: ldr     d7, [sp, #11856]
     +0x72c: eor     v2.8b, v17.8b, v2.8b
     +0x730: eor     v3.8b, v4.8b, v3.8b
     +0x734: ldr     d1, [x19, #264]
     +0x738: str     d0, [sp, #11816]
     +0x73c: ldp     d4, d0, [x19, #248]
     +0x740: eor     v5.8b, v6.8b, v5.8b
     +0x744: ldr     d6, [sp, #11864]
     +0x748: eor     v16.8b, v18.8b, v16.8b
     +0x74c: str     d2, [sp, #11832]
     +0x750: ldr     d2, [sp, #11872]
     +0x754: eor     v4.8b, v7.8b, v4.8b
     +0x758: eor     v0.8b, v6.8b, v0.8b
     +0x75c: str     d3, [sp, #11840]
     +0x760: eor     v1.8b, v2.8b, v1.8b
     +0x764: str     d16, [sp, #11808]
     +0x768: str     d5, [sp, #11848]
     +0x76c: str     d4, [sp, #11856]
     +0x770: str     d0, [sp, #11864]
     +0x774: str     d1, [sp, #11872]
     +0x778: bl      <mldsa_keccakf1600_permute>
     +0x77c: ldp     d1, d2, [x19, #272]
     +0x780: add     x0, sp, #0x2, lsl #12
     +0x784: ldr     d0, [sp, #11744]
     +0x788: ldr     d3, [sp, #11752]
     +0x78c: add     x0, x0, #0xde0
     +0x790: ldr     d5, [sp, #11760]
     +0x794: ldr     d6, [sp, #11776]
     +0x798: ldr     d7, [sp, #11784]
     +0x79c: eor     v0.8b, v0.8b, v1.8b
     +0x7a0: eor     v1.8b, v3.8b, v2.8b
     +0x7a4: ldr     d3, [sp, #11768]
     +0x7a8: ldp     d4, d2, [x19, #288]
     +0x7ac: ldr     d16, [sp, #11792]
     +0x7b0: ldr     d17, [sp, #11800]
     +0x7b4: ldr     d18, [sp, #11808]
     +0x7b8: str     d0, [sp, #11744]
     +0x7bc: eor     v4.8b, v5.8b, v4.8b
     +0x7c0: eor     v2.8b, v3.8b, v2.8b
     +0x7c4: str     d1, [sp, #11752]
     +0x7c8: ldp     d5, d3, [x19, #304]
     +0x7cc: str     d2, [sp, #11768]
     +0x7d0: ldp     d1, d2, [x19, #352]
     +0x7d4: eor     v5.8b, v6.8b, v5.8b
     +0x7d8: eor     v3.8b, v7.8b, v3.8b
     +0x7dc: str     d4, [sp, #11760]
     +0x7e0: ldp     d6, d7, [x19, #320]
     +0x7e4: ldr     d4, [sp, #11824]
     +0x7e8: str     d5, [sp, #11776]
     +0x7ec: eor     v1.8b, v4.8b, v1.8b
     +0x7f0: ldr     d4, [sp, #11840]
     +0x7f4: eor     v6.8b, v16.8b, v6.8b
     +0x7f8: ldp     d16, d0, [x19, #336]
     +0x7fc: eor     v7.8b, v17.8b, v7.8b
     +0x800: ldr     d17, [sp, #11816]
     +0x804: str     d3, [sp, #11784]
     +0x808: ldp     d3, d5, [x19, #368]
     +0x80c: str     d1, [sp, #11824]
     +0x810: eor     v0.8b, v17.8b, v0.8b
     +0x814: ldr     d17, [sp, #11832]
     +0x818: str     d6, [sp, #11792]
     +0x81c: ldr     d6, [sp, #11848]
     +0x820: str     d7, [sp, #11800]
     +0x824: ldr     d7, [sp, #11856]
     +0x828: eor     v2.8b, v17.8b, v2.8b
     +0x82c: eor     v3.8b, v4.8b, v3.8b
     +0x830: ldr     d1, [x19, #400]
     +0x834: str     d0, [sp, #11816]
     +0x838: ldp     d4, d0, [x19, #384]
     +0x83c: eor     v5.8b, v6.8b, v5.8b
     +0x840: ldr     d6, [sp, #11864]
     +0x844: eor     v16.8b, v18.8b, v16.8b
     +0x848: str     d2, [sp, #11832]
     +0x84c: ldr     d2, [sp, #11872]
     +0x850: eor     v4.8b, v7.8b, v4.8b
     +0x854: eor     v0.8b, v6.8b, v0.8b
     +0x858: str     d3, [sp, #11840]
     +0x85c: eor     v1.8b, v2.8b, v1.8b
     +0x860: str     d16, [sp, #11808]
     +0x864: str     d5, [sp, #11848]
     +0x868: str     d4, [sp, #11856]
     +0x86c: str     d0, [sp, #11864]
     +0x870: str     d1, [sp, #11872]
     +0x874: bl      <mldsa_keccakf1600_permute>
     +0x878: ldp     d1, d2, [x19, #408]
     +0x87c: add     x0, sp, #0x2, lsl #12
     +0x880: ldr     d0, [sp, #11744]
     +0x884: ldr     d3, [sp, #11752]
     +0x888: add     x0, x0, #0xde0
     +0x88c: ldr     d5, [sp, #11760]
     +0x890: ldr     d6, [sp, #11776]
     +0x894: ldr     d7, [sp, #11784]
     +0x898: eor     v0.8b, v0.8b, v1.8b
     +0x89c: eor     v1.8b, v3.8b, v2.8b
     +0x8a0: ldr     d3, [sp, #11768]
     +0x8a4: ldp     d4, d2, [x19, #424]
     +0x8a8: ldr     d16, [sp, #11792]
     +0x8ac: ldr     d17, [sp, #11800]
     +0x8b0: ldr     d18, [sp, #11808]
     +0x8b4: str     d0, [sp, #11744]
     +0x8b8: eor     v4.8b, v5.8b, v4.8b
     +0x8bc: eor     v2.8b, v3.8b, v2.8b
     +0x8c0: str     d1, [sp, #11752]
     +0x8c4: ldp     d5, d3, [x19, #440]
     +0x8c8: str     d2, [sp, #11768]
     +0x8cc: ldp     d1, d2, [x19, #488]
     +0x8d0: eor     v5.8b, v6.8b, v5.8b
     +0x8d4: eor     v3.8b, v7.8b, v3.8b
     +0x8d8: str     d4, [sp, #11760]
     +0x8dc: ldp     d6, d7, [x19, #456]
     +0x8e0: ldr     d4, [sp, #11824]
     +0x8e4: eor     v1.8b, v4.8b, v1.8b
     +0x8e8: str     d5, [sp, #11776]
     +0x8ec: ldr     d4, [sp, #11840]
     +0x8f0: eor     v6.8b, v16.8b, v6.8b
     +0x8f4: ldp     d16, d0, [x19, #472]
     +0x8f8: eor     v7.8b, v17.8b, v7.8b
     +0x8fc: ldr     d17, [sp, #11816]
     +0x900: str     d3, [sp, #11784]
     +0x904: ldp     d3, d5, [x19, #504]
     +0x908: str     d1, [sp, #11824]
     +0x90c: eor     v0.8b, v17.8b, v0.8b
     +0x910: ldr     d17, [sp, #11832]
     +0x914: str     d6, [sp, #11792]
     +0x918: ldr     d6, [sp, #11848]
     +0x91c: str     d7, [sp, #11800]
     +0x920: ldr     d7, [sp, #11856]
     +0x924: eor     v2.8b, v17.8b, v2.8b
     +0x928: eor     v3.8b, v4.8b, v3.8b
     +0x92c: ldr     d4, [x19, #520]
     +0x930: eor     v5.8b, v6.8b, v5.8b
     +0x934: str     d0, [sp, #11816]
     +0x938: ldr     d0, [sp, #11864]
     +0x93c: ldr     d6, [x19, #528]
     +0x940: ldr     d1, [x19, #536]
     +0x944: eor     v16.8b, v18.8b, v16.8b
     +0x948: str     d2, [sp, #11832]
     +0x94c: ldr     d2, [sp, #11872]
     +0x950: eor     v4.8b, v7.8b, v4.8b
     +0x954: eor     v0.8b, v0.8b, v6.8b
     +0x958: str     d3, [sp, #11840]
     +0x95c: eor     v1.8b, v2.8b, v1.8b
     +0x960: str     d16, [sp, #11808]
     +0x964: str     d5, [sp, #11848]
     +0x968: str     d4, [sp, #11856]
     +0x96c: str     d0, [sp, #11864]
     +0x970: str     d1, [sp, #11872]
     +0x974: bl      <mldsa_keccakf1600_permute>
     +0x978: ldr     d0, [x19, #544]
     +0x97c: ldr     d1, [sp, #11744]
     +0x980: add     x0, sp, #0x2, lsl #12
     +0x984: ldr     d2, [x19, #552]
     +0x988: ldr     d3, [sp, #11752]
     +0x98c: add     x0, x0, #0xde0
     +0x990: eor     v0.8b, v1.8b, v0.8b
     +0x994: ldr     d4, [x19, #560]
     +0x998: ldr     d5, [sp, #11760]
     +0x99c: eor     v1.8b, v3.8b, v2.8b
     +0x9a0: ldr     d2, [x19, #568]
     +0x9a4: ldr     d3, [sp, #11768]
     +0x9a8: ldr     d7, [sp, #11784]
     +0x9ac: eor     v4.8b, v5.8b, v4.8b
     +0x9b0: ldr     d5, [x19, #576]
     +0x9b4: eor     v2.8b, v3.8b, v2.8b
     +0x9b8: ldr     d3, [x19, #584]
     +0x9bc: ldr     d6, [sp, #11776]
     +0x9c0: ldr     d17, [sp, #11800]
     +0x9c4: ldr     d16, [sp, #11792]
     +0x9c8: str     d0, [sp, #11744]
     +0x9cc: eor     v3.8b, v7.8b, v3.8b
     +0x9d0: ldr     d7, [x19, #600]
     +0x9d4: eor     v5.8b, v6.8b, v5.8b
     +0x9d8: ldr     d6, [x19, #592]
     +0x9dc: ldr     d0, [sp, #11816]
     +0x9e0: str     d1, [sp, #11752]
     +0x9e4: eor     v7.8b, v17.8b, v7.8b
     +0x9e8: ldr     d1, [x19, #616]
     +0x9ec: str     d4, [sp, #11760]
     +0x9f0: ldr     d4, [x19, #624]
     +0x9f4: eor     v6.8b, v16.8b, v6.8b
     +0x9f8: ldr     d17, [sp, #11824]
     +0x9fc: eor     v0.8b, v0.8b, v1.8b
     +0xa00: str     d2, [sp, #11768]
     +0xa04: ldr     d1, [sp, #11832]
     +0xa08: eor     v2.8b, v17.8b, v4.8b
     +0xa0c: ldr     d4, [x19, #632]
     +0xa10: str     d5, [sp, #11776]
     +0xa14: str     d3, [sp, #11784]
     +0xa18: ldr     d3, [x19, #640]
     +0xa1c: ldr     d5, [sp, #11840]
     +0xa20: eor     v1.8b, v1.8b, v4.8b
     +0xa24: str     d6, [sp, #11792]
     +0xa28: ldr     d4, [sp, #11848]
     +0xa2c: eor     v3.8b, v5.8b, v3.8b
     +0xa30: str     d7, [sp, #11800]
     +0xa34: ldr     d5, [x19, #648]
     +0xa38: ldr     d6, [x19, #656]
     +0xa3c: ldr     d7, [sp, #11856]
     +0xa40: ldr     d16, [x19, #608]
     +0xa44: eor     v4.8b, v4.8b, v5.8b
     +0xa48: ldr     d18, [sp, #11808]
     +0xa4c: str     d0, [sp, #11816]
     +0xa50: eor     v5.8b, v7.8b, v6.8b
     +0xa54: ldr     d0, [sp, #11864]
     +0xa58: ldr     d6, [x19, #664]
     +0xa5c: eor     v16.8b, v18.8b, v16.8b
     +0xa60: str     d2, [sp, #11824]
     +0xa64: ldr     d2, [sp, #11872]
     +0xa68: eor     v0.8b, v0.8b, v6.8b
     +0xa6c: str     d1, [sp, #11832]
     +0xa70: ldr     d1, [x19, #672]
     +0xa74: str     d3, [sp, #11840]
     +0xa78: eor     v1.8b, v2.8b, v1.8b
     +0xa7c: str     d16, [sp, #11808]
     +0xa80: str     d4, [sp, #11848]
     +0xa84: str     d5, [sp, #11856]
     +0xa88: str     d0, [sp, #11864]
     +0xa8c: str     d1, [sp, #11872]
     +0xa90: bl      <mldsa_keccakf1600_permute>
     +0xa94: ldr     d0, [x19, #680]
     +0xa98: ldr     d1, [sp, #11744]
     +0xa9c: add     x0, sp, #0x2, lsl #12
     +0xaa0: ldr     d2, [x19, #688]
     +0xaa4: ldr     d3, [sp, #11752]
     +0xaa8: add     x0, x0, #0xde0
     +0xaac: eor     v0.8b, v1.8b, v0.8b
     +0xab0: ldr     d4, [x19, #696]
     +0xab4: ldr     d5, [sp, #11760]
     +0xab8: eor     v1.8b, v3.8b, v2.8b
     +0xabc: ldr     d2, [x19, #704]
     +0xac0: ldr     d3, [sp, #11768]
     +0xac4: ldr     d7, [sp, #11784]
     +0xac8: eor     v4.8b, v5.8b, v4.8b
     +0xacc: ldr     d5, [x19, #712]
     +0xad0: eor     v2.8b, v3.8b, v2.8b
     +0xad4: ldr     d3, [x19, #720]
     +0xad8: ldr     d6, [sp, #11776]
     +0xadc: ldr     d17, [sp, #11800]
     +0xae0: ldr     d16, [sp, #11792]
     +0xae4: str     d0, [sp, #11744]
     +0xae8: eor     v3.8b, v7.8b, v3.8b
     +0xaec: ldr     d7, [x19, #736]
     +0xaf0: eor     v5.8b, v6.8b, v5.8b
     +0xaf4: ldr     d6, [x19, #728]
     +0xaf8: ldr     d0, [sp, #11816]
     +0xafc: str     d1, [sp, #11752]
     +0xb00: eor     v7.8b, v17.8b, v7.8b
     +0xb04: ldr     d1, [x19, #752]
     +0xb08: str     d4, [sp, #11760]
     +0xb0c: ldr     d4, [x19, #760]
     +0xb10: eor     v6.8b, v16.8b, v6.8b
     +0xb14: ldr     d17, [sp, #11824]
     +0xb18: eor     v0.8b, v0.8b, v1.8b
     +0xb1c: str     d2, [sp, #11768]
     +0xb20: ldr     d1, [sp, #11832]
     +0xb24: eor     v2.8b, v17.8b, v4.8b
     +0xb28: ldr     d4, [x19, #768]
     +0xb2c: str     d5, [sp, #11776]
     +0xb30: str     d3, [sp, #11784]
     +0xb34: ldr     d3, [x19, #776]
     +0xb38: ldr     d5, [sp, #11840]
     +0xb3c: eor     v1.8b, v1.8b, v4.8b
     +0xb40: str     d6, [sp, #11792]
     +0xb44: ldr     d4, [sp, #11848]
     +0xb48: eor     v3.8b, v5.8b, v3.8b
     +0xb4c: str     d7, [sp, #11800]
     +0xb50: ldr     d5, [x19, #784]
     +0xb54: ldr     d6, [x19, #792]
     +0xb58: ldr     d7, [sp, #11856]
     +0xb5c: ldr     d16, [x19, #744]
     +0xb60: eor     v4.8b, v4.8b, v5.8b
     +0xb64: ldr     d18, [sp, #11808]
     +0xb68: str     d0, [sp, #11816]
     +0xb6c: eor     v5.8b, v7.8b, v6.8b
     +0xb70: ldr     d0, [sp, #11864]
     +0xb74: ldr     d6, [x19, #800]
     +0xb78: eor     v16.8b, v18.8b, v16.8b
     +0xb7c: str     d2, [sp, #11824]
     +0xb80: ldr     d2, [sp, #11872]
     +0xb84: eor     v0.8b, v0.8b, v6.8b
     +0xb88: str     d1, [sp, #11832]
     +0xb8c: ldr     d1, [x19, #808]
     +0xb90: str     d3, [sp, #11840]
     +0xb94: eor     v1.8b, v2.8b, v1.8b
     +0xb98: str     d16, [sp, #11808]
     +0xb9c: str     d4, [sp, #11848]
     +0xba0: str     d5, [sp, #11856]
     +0xba4: str     d0, [sp, #11864]
     +0xba8: str     d1, [sp, #11872]
     +0xbac: bl      <mldsa_keccakf1600_permute>
     +0xbb0: ldr     d0, [x19, #816]
     +0xbb4: ldr     d1, [sp, #11744]
     +0xbb8: add     x0, sp, #0x2, lsl #12
     +0xbbc: ldr     d2, [x19, #824]
     +0xbc0: ldr     d3, [sp, #11752]
     +0xbc4: add     x0, x0, #0xde0
     +0xbc8: eor     v0.8b, v1.8b, v0.8b
     +0xbcc: ldr     d4, [x19, #832]
     +0xbd0: ldr     d5, [sp, #11760]
     +0xbd4: eor     v1.8b, v3.8b, v2.8b
     +0xbd8: ldr     d2, [x19, #840]
     +0xbdc: ldr     d3, [sp, #11768]
     +0xbe0: ldr     d7, [sp, #11784]
     +0xbe4: eor     v4.8b, v5.8b, v4.8b
     +0xbe8: ldr     d5, [x19, #848]
     +0xbec: eor     v2.8b, v3.8b, v2.8b
     +0xbf0: ldr     d3, [x19, #856]
     +0xbf4: ldr     d6, [sp, #11776]
     +0xbf8: ldr     d17, [sp, #11800]
     +0xbfc: ldr     d16, [sp, #11792]
     +0xc00: str     d0, [sp, #11744]
     +0xc04: eor     v3.8b, v7.8b, v3.8b
     +0xc08: ldr     d7, [x19, #872]
     +0xc0c: eor     v5.8b, v6.8b, v5.8b
     +0xc10: ldr     d6, [x19, #864]
     +0xc14: ldr     d0, [sp, #11816]
     +0xc18: str     d1, [sp, #11752]
     +0xc1c: eor     v7.8b, v17.8b, v7.8b
     +0xc20: ldr     d1, [x19, #888]
     +0xc24: str     d4, [sp, #11760]
     +0xc28: ldr     d4, [x19, #896]
     +0xc2c: eor     v6.8b, v16.8b, v6.8b
     +0xc30: ldr     d17, [sp, #11824]
     +0xc34: eor     v0.8b, v0.8b, v1.8b
     +0xc38: str     d2, [sp, #11768]
     +0xc3c: ldr     d1, [sp, #11832]
     +0xc40: eor     v2.8b, v17.8b, v4.8b
     +0xc44: ldr     d4, [x19, #904]
     +0xc48: str     d5, [sp, #11776]
     +0xc4c: str     d3, [sp, #11784]
     +0xc50: ldr     d3, [x19, #912]
     +0xc54: ldr     d5, [sp, #11840]
     +0xc58: eor     v1.8b, v1.8b, v4.8b
     +0xc5c: str     d6, [sp, #11792]
     +0xc60: ldr     d4, [sp, #11848]
     +0xc64: eor     v3.8b, v5.8b, v3.8b
     +0xc68: str     d7, [sp, #11800]
     +0xc6c: ldr     d5, [x19, #920]
     +0xc70: ldr     d6, [x19, #928]
     +0xc74: ldr     d7, [sp, #11856]
     +0xc78: ldr     d16, [x19, #880]
     +0xc7c: eor     v4.8b, v4.8b, v5.8b
     +0xc80: ldr     d18, [sp, #11808]
     +0xc84: str     d0, [sp, #11816]
     +0xc88: eor     v5.8b, v7.8b, v6.8b
     +0xc8c: ldr     d0, [sp, #11864]
     +0xc90: ldr     d6, [x19, #936]
     +0xc94: eor     v16.8b, v18.8b, v16.8b
     +0xc98: str     d2, [sp, #11824]
     +0xc9c: ldr     d2, [sp, #11872]
     +0xca0: eor     v0.8b, v0.8b, v6.8b
     +0xca4: str     d1, [sp, #11832]
     +0xca8: ldr     d1, [x19, #944]
     +0xcac: str     d3, [sp, #11840]
     +0xcb0: eor     v1.8b, v2.8b, v1.8b
     +0xcb4: str     d16, [sp, #11808]
     +0xcb8: str     d4, [sp, #11848]
     +0xcbc: str     d5, [sp, #11856]
     +0xcc0: str     d0, [sp, #11864]
     +0xcc4: str     d1, [sp, #11872]
     +0xcc8: bl      <mldsa_keccakf1600_permute>
     +0xccc: ldr     d0, [x19, #952]
     +0xcd0: ldr     d1, [sp, #11744]
     +0xcd4: add     x0, sp, #0x2, lsl #12
     +0xcd8: ldr     d2, [x19, #960]
     +0xcdc: ldr     d3, [sp, #11752]
     +0xce0: add     x0, x0, #0xde0
     +0xce4: eor     v0.8b, v1.8b, v0.8b
     +0xce8: ldr     d4, [x19, #968]
     +0xcec: ldr     d5, [sp, #11760]
     +0xcf0: eor     v1.8b, v3.8b, v2.8b
     +0xcf4: ldr     d2, [x19, #976]
     +0xcf8: ldr     d3, [sp, #11768]
     +0xcfc: ldr     d7, [sp, #11784]
     +0xd00: eor     v4.8b, v5.8b, v4.8b
     +0xd04: ldr     d5, [x19, #984]
     +0xd08: eor     v2.8b, v3.8b, v2.8b
     +0xd0c: ldr     d3, [x19, #992]
     +0xd10: ldr     d6, [sp, #11776]
     +0xd14: ldr     d17, [sp, #11800]
     +0xd18: ldr     d16, [sp, #11792]
     +0xd1c: str     d0, [sp, #11744]
     +0xd20: eor     v3.8b, v7.8b, v3.8b
     +0xd24: ldr     d7, [x19, #1008]
     +0xd28: eor     v5.8b, v6.8b, v5.8b
     +0xd2c: ldr     d6, [x19, #1000]
     +0xd30: ldr     d0, [sp, #11816]
     +0xd34: str     d1, [sp, #11752]
     +0xd38: eor     v7.8b, v17.8b, v7.8b
     +0xd3c: ldr     d1, [x19, #1024]
     +0xd40: str     d4, [sp, #11760]
     +0xd44: ldr     d4, [x19, #1032]
     +0xd48: eor     v6.8b, v16.8b, v6.8b
     +0xd4c: ldr     d17, [sp, #11824]
     +0xd50: eor     v0.8b, v0.8b, v1.8b
     +0xd54: str     d2, [sp, #11768]
     +0xd58: ldr     d1, [sp, #11832]
     +0xd5c: eor     v2.8b, v17.8b, v4.8b
     +0xd60: ldr     d4, [x19, #1040]
     +0xd64: str     d5, [sp, #11776]
     +0xd68: str     d3, [sp, #11784]
     +0xd6c: ldr     d3, [x19, #1048]
     +0xd70: ldr     d5, [sp, #11840]
     +0xd74: eor     v1.8b, v1.8b, v4.8b
     +0xd78: str     d6, [sp, #11792]
     +0xd7c: ldr     d4, [sp, #11848]
     +0xd80: eor     v3.8b, v5.8b, v3.8b
     +0xd84: str     d7, [sp, #11800]
     +0xd88: ldr     d5, [x19, #1056]
     +0xd8c: ldr     d6, [x19, #1064]
     +0xd90: ldr     d7, [sp, #11856]
     +0xd94: ldr     d16, [x19, #1016]
     +0xd98: eor     v4.8b, v4.8b, v5.8b
     +0xd9c: ldr     d18, [sp, #11808]
     +0xda0: str     d0, [sp, #11816]
     +0xda4: eor     v5.8b, v7.8b, v6.8b
     +0xda8: ldr     d0, [sp, #11864]
     +0xdac: ldr     d6, [x19, #1072]
     +0xdb0: eor     v16.8b, v18.8b, v16.8b
     +0xdb4: str     d2, [sp, #11824]
     +0xdb8: ldr     d2, [sp, #11872]
     +0xdbc: eor     v0.8b, v0.8b, v6.8b
     +0xdc0: str     d1, [sp, #11832]
     +0xdc4: ldr     d1, [x19, #1080]
     +0xdc8: str     d3, [sp, #11840]
     +0xdcc: eor     v1.8b, v2.8b, v1.8b
     +0xdd0: str     d16, [sp, #11808]
     +0xdd4: str     d4, [sp, #11848]
     +0xdd8: str     d5, [sp, #11856]
     +0xddc: str     d0, [sp, #11864]
     +0xde0: str     d1, [sp, #11872]
     +0xde4: bl      <mldsa_keccakf1600_permute>
     +0xde8: ldr     d0, [x19, #1088]
     +0xdec: ldr     d1, [sp, #11744]
     +0xdf0: add     x0, sp, #0x2, lsl #12
     +0xdf4: ldr     d2, [x19, #1096]
     +0xdf8: ldr     d3, [sp, #11752]
     +0xdfc: add     x0, x0, #0xde0
     +0xe00: eor     v0.8b, v1.8b, v0.8b
     +0xe04: ldr     d4, [x19, #1104]
     +0xe08: ldr     d5, [sp, #11760]
     +0xe0c: eor     v1.8b, v3.8b, v2.8b
     +0xe10: ldr     d2, [x19, #1112]
     +0xe14: ldr     d3, [sp, #11768]
     +0xe18: ldr     d7, [sp, #11784]
     +0xe1c: eor     v4.8b, v5.8b, v4.8b
     +0xe20: ldr     d5, [x19, #1120]
     +0xe24: eor     v2.8b, v3.8b, v2.8b
     +0xe28: ldr     d3, [x19, #1128]
     +0xe2c: ldr     d6, [sp, #11776]
     +0xe30: ldr     d17, [sp, #11800]
     +0xe34: ldr     d16, [sp, #11792]
     +0xe38: str     d0, [sp, #11744]
     +0xe3c: eor     v3.8b, v7.8b, v3.8b
     +0xe40: ldr     d7, [x19, #1144]
     +0xe44: eor     v5.8b, v6.8b, v5.8b
     +0xe48: ldr     d6, [x19, #1136]
     +0xe4c: ldr     d0, [sp, #11816]
     +0xe50: str     d1, [sp, #11752]
     +0xe54: eor     v7.8b, v17.8b, v7.8b
     +0xe58: ldr     d1, [x19, #1160]
     +0xe5c: str     d4, [sp, #11760]
     +0xe60: ldr     d4, [x19, #1168]
     +0xe64: eor     v6.8b, v16.8b, v6.8b
     +0xe68: ldr     d17, [sp, #11824]
     +0xe6c: eor     v0.8b, v0.8b, v1.8b
     +0xe70: str     d2, [sp, #11768]
     +0xe74: ldr     d1, [sp, #11832]
     +0xe78: eor     v2.8b, v17.8b, v4.8b
     +0xe7c: ldr     d4, [x19, #1176]
     +0xe80: str     d5, [sp, #11776]
     +0xe84: str     d3, [sp, #11784]
     +0xe88: ldr     d3, [x19, #1184]
     +0xe8c: ldr     d5, [sp, #11840]
     +0xe90: eor     v1.8b, v1.8b, v4.8b
     +0xe94: str     d6, [sp, #11792]
     +0xe98: ldr     d4, [sp, #11848]
     +0xe9c: eor     v3.8b, v5.8b, v3.8b
     +0xea0: str     d7, [sp, #11800]
     +0xea4: ldr     d5, [x19, #1192]
     +0xea8: ldr     d6, [x19, #1200]
     +0xeac: ldr     d7, [sp, #11856]
     +0xeb0: ldr     d16, [x19, #1152]
     +0xeb4: eor     v4.8b, v4.8b, v5.8b
     +0xeb8: ldr     d18, [sp, #11808]
     +0xebc: str     d0, [sp, #11816]
     +0xec0: eor     v5.8b, v7.8b, v6.8b
     +0xec4: ldr     d0, [sp, #11864]
     +0xec8: ldr     d6, [x19, #1208]
     +0xecc: eor     v16.8b, v18.8b, v16.8b
     +0xed0: str     d2, [sp, #11824]
     +0xed4: ldr     d2, [sp, #11872]
     +0xed8: eor     v0.8b, v0.8b, v6.8b
     +0xedc: str     d1, [sp, #11832]
     +0xee0: ldr     d1, [x19, #1216]
     +0xee4: str     d3, [sp, #11840]
     +0xee8: eor     v1.8b, v2.8b, v1.8b
     +0xeec: str     d16, [sp, #11808]
     +0xef0: str     d4, [sp, #11848]
     +0xef4: str     d5, [sp, #11856]
     +0xef8: str     d0, [sp, #11864]
     +0xefc: str     d1, [sp, #11872]
     +0xf00: bl      <mldsa_keccakf1600_permute>
     +0xf04: ldr     d0, [x19, #1224]
     +0xf08: ldr     d1, [sp, #11744]
     +0xf0c: add     x0, sp, #0x2, lsl #12
     +0xf10: ldr     d2, [x19, #1232]
     +0xf14: ldr     d3, [sp, #11752]
     +0xf18: add     x0, x0, #0xde0
     +0xf1c: eor     v0.8b, v1.8b, v0.8b
     +0xf20: ldr     d4, [x19, #1240]
     +0xf24: ldr     d5, [sp, #11760]
     +0xf28: eor     v1.8b, v3.8b, v2.8b
     +0xf2c: ldr     d2, [x19, #1248]
     +0xf30: ldr     d3, [sp, #11768]
     +0xf34: ldr     d7, [sp, #11784]
     +0xf38: eor     v4.8b, v5.8b, v4.8b
     +0xf3c: ldr     d5, [x19, #1256]
     +0xf40: eor     v2.8b, v3.8b, v2.8b
     +0xf44: ldr     d3, [x19, #1264]
     +0xf48: ldr     d6, [sp, #11776]
     +0xf4c: ldr     d17, [sp, #11800]
     +0xf50: ldr     d16, [sp, #11792]
     +0xf54: str     d0, [sp, #11744]
     +0xf58: eor     v3.8b, v7.8b, v3.8b
     +0xf5c: ldr     d7, [x19, #1280]
     +0xf60: eor     v5.8b, v6.8b, v5.8b
     +0xf64: ldr     d6, [x19, #1272]
     +0xf68: ldr     d0, [sp, #11816]
     +0xf6c: str     d1, [sp, #11752]
     +0xf70: eor     v7.8b, v17.8b, v7.8b
     +0xf74: ldr     d1, [x19, #1296]
     +0xf78: str     d4, [sp, #11760]
     +0xf7c: ldr     d4, [x19, #1304]
     +0xf80: eor     v6.8b, v16.8b, v6.8b
     +0xf84: ldr     d17, [sp, #11824]
     +0xf88: eor     v0.8b, v0.8b, v1.8b
     +0xf8c: str     d2, [sp, #11768]
     +0xf90: ldr     d1, [sp, #11832]
     +0xf94: eor     v2.8b, v17.8b, v4.8b
     +0xf98: ldr     d4, [x19, #1312]
     +0xf9c: str     d5, [sp, #11776]
     +0xfa0: str     d3, [sp, #11784]
     +0xfa4: ldr     d3, [x19, #1320]
     +0xfa8: ldr     d5, [sp, #11840]
     +0xfac: eor     v1.8b, v1.8b, v4.8b
     +0xfb0: str     d6, [sp, #11792]
     +0xfb4: ldr     d4, [sp, #11848]
     +0xfb8: eor     v3.8b, v5.8b, v3.8b
     +0xfbc: str     d7, [sp, #11800]
     +0xfc0: ldr     d5, [x19, #1328]
     +0xfc4: ldr     d6, [x19, #1336]
     +0xfc8: ldr     d7, [sp, #11856]
     +0xfcc: ldr     d16, [x19, #1288]
     +0xfd0: eor     v4.8b, v4.8b, v5.8b
     +0xfd4: ldr     d18, [sp, #11808]
     +0xfd8: str     d0, [sp, #11816]
     +0xfdc: eor     v5.8b, v7.8b, v6.8b
     +0xfe0: ldr     d0, [sp, #11864]
     +0xfe4: ldr     d6, [x19, #1344]
     +0xfe8: eor     v16.8b, v18.8b, v16.8b
     +0xfec: str     d2, [sp, #11824]
     +0xff0: ldr     d2, [sp, #11872]
     +0xff4: eor     v0.8b, v0.8b, v6.8b
     +0xff8: str     d1, [sp, #11832]
     +0xffc: ldr     d1, [x19, #1352]
    +0x1000: str     d3, [sp, #11840]
    +0x1004: eor     v1.8b, v2.8b, v1.8b
    +0x1008: str     d16, [sp, #11808]
    +0x100c: str     d4, [sp, #11848]
    +0x1010: str     d5, [sp, #11856]
    +0x1014: str     d0, [sp, #11864]
    +0x1018: str     d1, [sp, #11872]
    +0x101c: bl      <mldsa_keccakf1600_permute>
    +0x1020: ldr     d0, [x19, #1360]
    +0x1024: ldr     d1, [sp, #11744]
    +0x1028: add     x0, sp, #0x2, lsl #12
    +0x102c: ldr     d2, [x19, #1368]
    +0x1030: ldr     d3, [sp, #11752]
    +0x1034: add     x0, x0, #0xde0
    +0x1038: eor     v0.8b, v1.8b, v0.8b
    +0x103c: ldr     d4, [x19, #1376]
    +0x1040: ldr     d5, [sp, #11760]
    +0x1044: eor     v1.8b, v3.8b, v2.8b
    +0x1048: ldr     d2, [x19, #1384]
    +0x104c: ldr     d3, [sp, #11768]
    +0x1050: ldr     d7, [sp, #11784]
    +0x1054: eor     v4.8b, v5.8b, v4.8b
    +0x1058: ldr     d5, [x19, #1392]
    +0x105c: eor     v2.8b, v3.8b, v2.8b
    +0x1060: ldr     d3, [x19, #1400]
    +0x1064: ldr     d6, [sp, #11776]
    +0x1068: ldr     d17, [sp, #11800]
    +0x106c: ldr     d16, [sp, #11792]
    +0x1070: str     d0, [sp, #11744]
    +0x1074: eor     v3.8b, v7.8b, v3.8b
    +0x1078: ldr     d7, [x19, #1416]
    +0x107c: eor     v5.8b, v6.8b, v5.8b
    +0x1080: ldr     d6, [x19, #1408]
    +0x1084: ldr     d0, [sp, #11816]
    +0x1088: str     d1, [sp, #11752]
    +0x108c: eor     v7.8b, v17.8b, v7.8b
    +0x1090: ldr     d1, [x19, #1432]
    +0x1094: str     d4, [sp, #11760]
    +0x1098: ldr     d4, [x19, #1440]
    +0x109c: eor     v6.8b, v16.8b, v6.8b
    +0x10a0: ldr     d17, [sp, #11824]
    +0x10a4: eor     v0.8b, v0.8b, v1.8b
    +0x10a8: str     d2, [sp, #11768]
    +0x10ac: ldr     d1, [sp, #11832]
    +0x10b0: eor     v2.8b, v17.8b, v4.8b
    +0x10b4: ldr     d4, [x19, #1448]
    +0x10b8: str     d5, [sp, #11776]
    +0x10bc: str     d3, [sp, #11784]
    +0x10c0: ldr     d3, [x19, #1456]
    +0x10c4: ldr     d5, [sp, #11840]
    +0x10c8: eor     v1.8b, v1.8b, v4.8b
    +0x10cc: str     d6, [sp, #11792]
    +0x10d0: ldr     d4, [sp, #11848]
    +0x10d4: eor     v3.8b, v5.8b, v3.8b
    +0x10d8: str     d7, [sp, #11800]
    +0x10dc: ldr     d5, [x19, #1464]
    +0x10e0: ldr     d6, [x19, #1472]
    +0x10e4: ldr     d7, [sp, #11856]
    +0x10e8: ldr     d16, [x19, #1424]
    +0x10ec: eor     v4.8b, v4.8b, v5.8b
    +0x10f0: ldr     d18, [sp, #11808]
    +0x10f4: str     d0, [sp, #11816]
    +0x10f8: eor     v5.8b, v7.8b, v6.8b
    +0x10fc: ldr     d0, [sp, #11864]
    +0x1100: ldr     d6, [x19, #1480]
    +0x1104: eor     v16.8b, v18.8b, v16.8b
    +0x1108: str     d2, [sp, #11824]
    +0x110c: ldr     d2, [sp, #11872]
    +0x1110: eor     v0.8b, v0.8b, v6.8b
    +0x1114: str     d1, [sp, #11832]
    +0x1118: ldr     d1, [x19, #1488]
    +0x111c: str     d3, [sp, #11840]
    +0x1120: eor     v1.8b, v2.8b, v1.8b
    +0x1124: str     d16, [sp, #11808]
    +0x1128: str     d4, [sp, #11848]
    +0x112c: str     d5, [sp, #11856]
    +0x1130: str     d0, [sp, #11864]
    +0x1134: str     d1, [sp, #11872]
    +0x1138: bl      <mldsa_keccakf1600_permute>
    +0x113c: ldr     d0, [x19, #1496]
    +0x1140: ldr     d1, [sp, #11744]
    +0x1144: add     x0, sp, #0x2, lsl #12
    +0x1148: ldr     d2, [x19, #1504]
    +0x114c: ldr     d3, [sp, #11752]
    +0x1150: add     x0, x0, #0xde0
    +0x1154: eor     v0.8b, v1.8b, v0.8b
    +0x1158: ldr     d4, [x19, #1512]
    +0x115c: ldr     d5, [sp, #11760]
    +0x1160: eor     v1.8b, v3.8b, v2.8b
    +0x1164: ldr     d2, [x19, #1520]
    +0x1168: ldr     d3, [sp, #11768]
    +0x116c: ldr     d7, [sp, #11784]
    +0x1170: eor     v4.8b, v5.8b, v4.8b
    +0x1174: ldr     d5, [x19, #1528]
    +0x1178: eor     v2.8b, v3.8b, v2.8b
    +0x117c: ldr     d3, [x19, #1536]
    +0x1180: ldr     d6, [sp, #11776]
    +0x1184: ldr     d17, [sp, #11800]
    +0x1188: ldr     d16, [sp, #11792]
    +0x118c: str     d0, [sp, #11744]
    +0x1190: eor     v3.8b, v7.8b, v3.8b
    +0x1194: ldr     d7, [x19, #1552]
    +0x1198: eor     v5.8b, v6.8b, v5.8b
    +0x119c: ldr     d6, [x19, #1544]
    +0x11a0: ldr     d0, [sp, #11816]
    +0x11a4: str     d1, [sp, #11752]
    +0x11a8: eor     v7.8b, v17.8b, v7.8b
    +0x11ac: ldr     d1, [x19, #1568]
    +0x11b0: str     d4, [sp, #11760]
    +0x11b4: ldr     d4, [x19, #1576]
    +0x11b8: eor     v6.8b, v16.8b, v6.8b
    +0x11bc: ldr     d17, [sp, #11824]
    +0x11c0: eor     v0.8b, v0.8b, v1.8b
    +0x11c4: str     d2, [sp, #11768]
    +0x11c8: ldr     d1, [sp, #11832]
    +0x11cc: eor     v2.8b, v17.8b, v4.8b
    +0x11d0: ldr     d4, [x19, #1584]
    +0x11d4: str     d5, [sp, #11776]
    +0x11d8: str     d3, [sp, #11784]
    +0x11dc: ldr     d3, [x19, #1592]
    +0x11e0: ldr     d5, [sp, #11840]
    +0x11e4: eor     v1.8b, v1.8b, v4.8b
    +0x11e8: str     d6, [sp, #11792]
    +0x11ec: ldr     d4, [sp, #11848]
    +0x11f0: eor     v3.8b, v5.8b, v3.8b
    +0x11f4: str     d7, [sp, #11800]
    +0x11f8: ldr     d5, [x19, #1600]
    +0x11fc: ldr     d6, [x19, #1608]
    +0x1200: ldr     d7, [sp, #11856]
    +0x1204: ldr     d16, [x19, #1560]
    +0x1208: eor     v4.8b, v4.8b, v5.8b
    +0x120c: ldr     d18, [sp, #11808]
    +0x1210: str     d0, [sp, #11816]
    +0x1214: eor     v5.8b, v7.8b, v6.8b
    +0x1218: ldr     d0, [sp, #11864]
    +0x121c: ldr     d6, [x19, #1616]
    +0x1220: eor     v16.8b, v18.8b, v16.8b
    +0x1224: str     d2, [sp, #11824]
    +0x1228: ldr     d2, [sp, #11872]
    +0x122c: eor     v0.8b, v0.8b, v6.8b
    +0x1230: str     d1, [sp, #11832]
    +0x1234: ldr     d1, [x19, #1624]
    +0x1238: str     d3, [sp, #11840]
    +0x123c: eor     v1.8b, v2.8b, v1.8b
    +0x1240: str     d16, [sp, #11808]
    +0x1244: str     d4, [sp, #11848]
    +0x1248: str     d5, [sp, #11856]
    +0x124c: str     d0, [sp, #11864]
    +0x1250: str     d1, [sp, #11872]
    +0x1254: bl      <mldsa_keccakf1600_permute>
    +0x1258: ldr     d0, [x19, #1632]
    +0x125c: ldr     d1, [sp, #11744]
    +0x1260: add     x0, sp, #0x2, lsl #12
    +0x1264: ldr     d2, [x19, #1640]
    +0x1268: ldr     d3, [sp, #11752]
    +0x126c: add     x0, x0, #0xde0
    +0x1270: eor     v0.8b, v1.8b, v0.8b
    +0x1274: ldr     d4, [x19, #1648]
    +0x1278: ldr     d5, [sp, #11760]
    +0x127c: eor     v1.8b, v3.8b, v2.8b
    +0x1280: ldr     d2, [x19, #1656]
    +0x1284: ldr     d3, [sp, #11768]
    +0x1288: ldr     d7, [sp, #11784]
    +0x128c: eor     v4.8b, v5.8b, v4.8b
    +0x1290: ldr     d5, [x19, #1664]
    +0x1294: eor     v2.8b, v3.8b, v2.8b
    +0x1298: ldr     d3, [x19, #1672]
    +0x129c: ldr     d6, [sp, #11776]
    +0x12a0: ldr     d17, [sp, #11800]
    +0x12a4: ldr     d16, [sp, #11792]
    +0x12a8: str     d0, [sp, #11744]
    +0x12ac: eor     v3.8b, v7.8b, v3.8b
    +0x12b0: ldr     d7, [x19, #1688]
    +0x12b4: eor     v5.8b, v6.8b, v5.8b
    +0x12b8: ldr     d6, [x19, #1680]
    +0x12bc: ldr     d0, [sp, #11816]
    +0x12c0: str     d1, [sp, #11752]
    +0x12c4: eor     v7.8b, v17.8b, v7.8b
    +0x12c8: ldr     d1, [x19, #1704]
    +0x12cc: str     d4, [sp, #11760]
    +0x12d0: ldr     d4, [x19, #1712]
    +0x12d4: eor     v6.8b, v16.8b, v6.8b
    +0x12d8: ldr     d17, [sp, #11824]
    +0x12dc: eor     v0.8b, v0.8b, v1.8b
    +0x12e0: str     d2, [sp, #11768]
    +0x12e4: ldr     d1, [sp, #11832]
    +0x12e8: eor     v2.8b, v17.8b, v4.8b
    +0x12ec: ldr     d4, [x19, #1720]
    +0x12f0: str     d5, [sp, #11776]
    +0x12f4: str     d3, [sp, #11784]
    +0x12f8: ldr     d3, [x19, #1728]
    +0x12fc: ldr     d5, [sp, #11840]
    +0x1300: eor     v1.8b, v1.8b, v4.8b
    +0x1304: str     d6, [sp, #11792]
    +0x1308: ldr     d4, [sp, #11848]
    +0x130c: eor     v3.8b, v5.8b, v3.8b
    +0x1310: str     d7, [sp, #11800]
    +0x1314: ldr     d5, [x19, #1736]
    +0x1318: ldr     d6, [x19, #1744]
    +0x131c: ldr     d7, [sp, #11856]
    +0x1320: ldr     d16, [x19, #1696]
    +0x1324: eor     v4.8b, v4.8b, v5.8b
    +0x1328: ldr     d18, [sp, #11808]
    +0x132c: str     d0, [sp, #11816]
    +0x1330: eor     v5.8b, v7.8b, v6.8b
    +0x1334: ldr     d0, [sp, #11864]
    +0x1338: ldr     d6, [x19, #1752]
    +0x133c: eor     v16.8b, v18.8b, v16.8b
    +0x1340: str     d2, [sp, #11824]
    +0x1344: ldr     d2, [sp, #11872]
    +0x1348: eor     v0.8b, v0.8b, v6.8b
    +0x134c: str     d1, [sp, #11832]
    +0x1350: ldr     d1, [x19, #1760]
    +0x1354: str     d3, [sp, #11840]
    +0x1358: eor     v1.8b, v2.8b, v1.8b
    +0x135c: str     d16, [sp, #11808]
    +0x1360: str     d4, [sp, #11848]
    +0x1364: str     d5, [sp, #11856]
    +0x1368: str     d0, [sp, #11864]
    +0x136c: str     d1, [sp, #11872]
    +0x1370: bl      <mldsa_keccakf1600_permute>
    +0x1374: ldr     d0, [x19, #1768]
    +0x1378: ldr     d1, [sp, #11744]
    +0x137c: add     x0, sp, #0x2, lsl #12
    +0x1380: ldr     d2, [x19, #1776]
    +0x1384: ldr     d3, [sp, #11752]
    +0x1388: add     x0, x0, #0xde0
    +0x138c: eor     v0.8b, v1.8b, v0.8b
    +0x1390: ldr     d4, [x19, #1784]
    +0x1394: ldr     d5, [sp, #11760]
    +0x1398: eor     v1.8b, v3.8b, v2.8b
    +0x139c: ldr     d2, [x19, #1792]
    +0x13a0: ldr     d3, [sp, #11768]
    +0x13a4: ldr     d7, [sp, #11784]
    +0x13a8: eor     v4.8b, v5.8b, v4.8b
    +0x13ac: ldr     d5, [x19, #1800]
    +0x13b0: eor     v2.8b, v3.8b, v2.8b
    +0x13b4: ldr     d3, [x19, #1808]
    +0x13b8: ldr     d6, [sp, #11776]
    +0x13bc: ldr     d17, [sp, #11800]
    +0x13c0: ldr     d16, [sp, #11792]
    +0x13c4: str     d0, [sp, #11744]
    +0x13c8: eor     v3.8b, v7.8b, v3.8b
    +0x13cc: ldr     d7, [x19, #1824]
    +0x13d0: eor     v5.8b, v6.8b, v5.8b
    +0x13d4: ldr     d6, [x19, #1816]
    +0x13d8: ldr     d0, [sp, #11816]
    +0x13dc: str     d1, [sp, #11752]
    +0x13e0: eor     v7.8b, v17.8b, v7.8b
    +0x13e4: ldr     d1, [x19, #1840]
    +0x13e8: str     d4, [sp, #11760]
    +0x13ec: ldr     d4, [x19, #1848]
    +0x13f0: eor     v6.8b, v16.8b, v6.8b
    +0x13f4: ldr     d17, [sp, #11824]
    +0x13f8: eor     v0.8b, v0.8b, v1.8b
    +0x13fc: str     d2, [sp, #11768]
    +0x1400: ldr     d1, [sp, #11832]
    +0x1404: eor     v2.8b, v17.8b, v4.8b
    +0x1408: ldr     d4, [x19, #1856]
    +0x140c: str     d5, [sp, #11776]
    +0x1410: str     d3, [sp, #11784]
    +0x1414: ldr     d3, [x19, #1864]
    +0x1418: ldr     d5, [sp, #11840]
    +0x141c: eor     v1.8b, v1.8b, v4.8b
    +0x1420: str     d6, [sp, #11792]
    +0x1424: ldr     d4, [sp, #11848]
    +0x1428: eor     v3.8b, v5.8b, v3.8b
    +0x142c: str     d7, [sp, #11800]
    +0x1430: ldr     d5, [x19, #1872]
    +0x1434: ldr     d6, [x19, #1880]
    +0x1438: ldr     d7, [sp, #11856]
    +0x143c: ldr     d16, [x19, #1832]
    +0x1440: eor     v4.8b, v4.8b, v5.8b
    +0x1444: ldr     d18, [sp, #11808]
    +0x1448: str     d0, [sp, #11816]
    +0x144c: eor     v5.8b, v7.8b, v6.8b
    +0x1450: ldr     d0, [sp, #11864]
    +0x1454: ldr     d6, [x19, #1888]
    +0x1458: eor     v16.8b, v18.8b, v16.8b
    +0x145c: str     d2, [sp, #11824]
    +0x1460: ldr     d2, [sp, #11872]
    +0x1464: eor     v0.8b, v0.8b, v6.8b
    +0x1468: str     d1, [sp, #11832]
    +0x146c: ldr     d1, [x19, #1896]
    +0x1470: str     d3, [sp, #11840]
    +0x1474: eor     v1.8b, v2.8b, v1.8b
    +0x1478: str     d16, [sp, #11808]
    +0x147c: str     d4, [sp, #11848]
    +0x1480: str     d5, [sp, #11856]
    +0x1484: str     d0, [sp, #11864]
    +0x1488: str     d1, [sp, #11872]
    +0x148c: bl      <mldsa_keccakf1600_permute>
    +0x1490: ldr     d0, [x19, #1904]
    +0x1494: ldr     d1, [sp, #11744]
    +0x1498: add     x0, sp, #0x2, lsl #12
    +0x149c: ldr     d2, [x19, #1912]
    +0x14a0: ldr     d3, [sp, #11752]
    +0x14a4: add     x0, x0, #0xde0
    +0x14a8: eor     v0.8b, v1.8b, v0.8b
    +0x14ac: ldr     d4, [x19, #1920]
    +0x14b0: ldr     d5, [sp, #11760]
    +0x14b4: eor     v1.8b, v3.8b, v2.8b
    +0x14b8: ldr     d2, [x19, #1928]
    +0x14bc: ldr     d3, [sp, #11768]
    +0x14c0: ldr     d7, [sp, #11784]
    +0x14c4: eor     v4.8b, v5.8b, v4.8b
    +0x14c8: ldr     d5, [x19, #1936]
    +0x14cc: eor     v2.8b, v3.8b, v2.8b
    +0x14d0: ldr     d3, [x19, #1944]
    +0x14d4: ldr     d6, [sp, #11776]
    +0x14d8: ldr     d17, [sp, #11800]
    +0x14dc: ldr     d16, [sp, #11792]
    +0x14e0: str     d0, [sp, #11744]
    +0x14e4: eor     v3.8b, v7.8b, v3.8b
    +0x14e8: ldr     d7, [x19, #1960]
    +0x14ec: eor     v5.8b, v6.8b, v5.8b
    +0x14f0: ldr     d6, [x19, #1952]
    +0x14f4: ldr     d0, [sp, #11816]
    +0x14f8: str     d1, [sp, #11752]
    +0x14fc: eor     v7.8b, v17.8b, v7.8b
    +0x1500: ldr     d1, [x19, #1976]
    +0x1504: str     d4, [sp, #11760]
    +0x1508: ldr     d4, [x19, #1984]
    +0x150c: eor     v6.8b, v16.8b, v6.8b
    +0x1510: ldr     d17, [sp, #11824]
    +0x1514: eor     v0.8b, v0.8b, v1.8b
    +0x1518: str     d2, [sp, #11768]
    +0x151c: ldr     d1, [sp, #11832]
    +0x1520: eor     v2.8b, v17.8b, v4.8b
    +0x1524: ldr     d4, [x19, #1992]
    +0x1528: str     d5, [sp, #11776]
    +0x152c: str     d3, [sp, #11784]
    +0x1530: ldr     d3, [x19, #2000]
    +0x1534: ldr     d5, [sp, #11840]
    +0x1538: eor     v1.8b, v1.8b, v4.8b
    +0x153c: str     d6, [sp, #11792]
    +0x1540: ldr     d4, [sp, #11848]
    +0x1544: eor     v3.8b, v5.8b, v3.8b
    +0x1548: str     d7, [sp, #11800]
    +0x154c: ldr     d5, [x19, #2008]
    +0x1550: ldr     d6, [x19, #2016]
    +0x1554: ldr     d7, [sp, #11856]
    +0x1558: ldr     d16, [x19, #1968]
    +0x155c: eor     v4.8b, v4.8b, v5.8b
    +0x1560: ldr     d18, [sp, #11808]
    +0x1564: str     d0, [sp, #11816]
    +0x1568: eor     v5.8b, v7.8b, v6.8b
    +0x156c: ldr     d0, [sp, #11864]
    +0x1570: ldr     d6, [x19, #2024]
    +0x1574: eor     v16.8b, v18.8b, v16.8b
    +0x1578: str     d2, [sp, #11824]
    +0x157c: ldr     d2, [sp, #11872]
    +0x1580: eor     v0.8b, v0.8b, v6.8b
    +0x1584: str     d1, [sp, #11832]
    +0x1588: ldr     d1, [x19, #2032]
    +0x158c: str     d3, [sp, #11840]
    +0x1590: eor     v1.8b, v2.8b, v1.8b
    +0x1594: str     d16, [sp, #11808]
    +0x1598: str     d4, [sp, #11848]
    +0x159c: str     d5, [sp, #11856]
    +0x15a0: str     d0, [sp, #11864]
    +0x15a4: str     d1, [sp, #11872]
    +0x15a8: bl      <mldsa_keccakf1600_permute>
    +0x15ac: ldr     d0, [x19, #2040]
    +0x15b0: ldr     d1, [sp, #11744]
    +0x15b4: add     x0, sp, #0x2, lsl #12
    +0x15b8: ldr     d2, [x19, #2048]
    +0x15bc: ldr     d3, [sp, #11752]
    +0x15c0: add     x0, x0, #0xde0
    +0x15c4: eor     v0.8b, v1.8b, v0.8b
    +0x15c8: ldr     d4, [x19, #2056]
    +0x15cc: ldr     d5, [sp, #11760]
    +0x15d0: eor     v1.8b, v3.8b, v2.8b
    +0x15d4: ldr     d2, [x19, #2064]
    +0x15d8: ldr     d3, [sp, #11768]
    +0x15dc: ldr     d7, [sp, #11784]
    +0x15e0: eor     v4.8b, v5.8b, v4.8b
    +0x15e4: ldr     d5, [x19, #2072]
    +0x15e8: eor     v2.8b, v3.8b, v2.8b
    +0x15ec: ldr     d3, [x19, #2080]
    +0x15f0: ldr     d6, [sp, #11776]
    +0x15f4: ldr     d17, [sp, #11800]
    +0x15f8: ldr     d16, [sp, #11792]
    +0x15fc: str     d0, [sp, #11744]
    +0x1600: eor     v3.8b, v7.8b, v3.8b
    +0x1604: ldr     d7, [x19, #2096]
    +0x1608: eor     v5.8b, v6.8b, v5.8b
    +0x160c: ldr     d6, [x19, #2088]
    +0x1610: ldr     d0, [sp, #11816]
    +0x1614: str     d1, [sp, #11752]
    +0x1618: eor     v7.8b, v17.8b, v7.8b
    +0x161c: ldr     d1, [x19, #2112]
    +0x1620: str     d4, [sp, #11760]
    +0x1624: ldr     d4, [x19, #2120]
    +0x1628: eor     v6.8b, v16.8b, v6.8b
    +0x162c: ldr     d17, [sp, #11824]
    +0x1630: eor     v0.8b, v0.8b, v1.8b
    +0x1634: str     d2, [sp, #11768]
    +0x1638: ldr     d1, [sp, #11832]
    +0x163c: eor     v2.8b, v17.8b, v4.8b
    +0x1640: ldr     d4, [x19, #2128]
    +0x1644: str     d5, [sp, #11776]
    +0x1648: str     d3, [sp, #11784]
    +0x164c: ldr     d3, [x19, #2136]
    +0x1650: ldr     d5, [sp, #11840]
    +0x1654: eor     v1.8b, v1.8b, v4.8b
    +0x1658: str     d6, [sp, #11792]
    +0x165c: ldr     d4, [sp, #11848]
    +0x1660: eor     v3.8b, v5.8b, v3.8b
    +0x1664: str     d7, [sp, #11800]
    +0x1668: ldr     d5, [x19, #2144]
    +0x166c: ldr     d6, [x19, #2152]
    +0x1670: ldr     d7, [sp, #11856]
    +0x1674: ldr     d16, [x19, #2104]
    +0x1678: eor     v4.8b, v4.8b, v5.8b
    +0x167c: ldr     d18, [sp, #11808]
    +0x1680: str     d0, [sp, #11816]
    +0x1684: eor     v5.8b, v7.8b, v6.8b
    +0x1688: ldr     d0, [sp, #11864]
    +0x168c: ldr     d6, [x19, #2160]
    +0x1690: eor     v16.8b, v18.8b, v16.8b
    +0x1694: str     d2, [sp, #11824]
    +0x1698: ldr     d2, [sp, #11872]
    +0x169c: eor     v0.8b, v0.8b, v6.8b
    +0x16a0: str     d1, [sp, #11832]
    +0x16a4: ldr     d1, [x19, #2168]
    +0x16a8: str     d3, [sp, #11840]
    +0x16ac: eor     v1.8b, v2.8b, v1.8b
    +0x16b0: str     d16, [sp, #11808]
    +0x16b4: str     d4, [sp, #11848]
    +0x16b8: str     d5, [sp, #11856]
    +0x16bc: str     d0, [sp, #11864]
    +0x16c0: str     d1, [sp, #11872]
    +0x16c4: bl      <mldsa_keccakf1600_permute>
    +0x16c8: ldr     d0, [x19, #2176]
    +0x16cc: ldr     d1, [sp, #11744]
    +0x16d0: add     x0, sp, #0x2, lsl #12
    +0x16d4: ldr     d2, [x19, #2184]
    +0x16d8: ldr     d3, [sp, #11752]
    +0x16dc: add     x0, x0, #0xde0
    +0x16e0: eor     v0.8b, v1.8b, v0.8b
    +0x16e4: ldr     d4, [x19, #2192]
    +0x16e8: ldr     d5, [sp, #11760]
    +0x16ec: eor     v1.8b, v3.8b, v2.8b
    +0x16f0: ldr     d2, [x19, #2200]
    +0x16f4: ldr     d3, [sp, #11768]
    +0x16f8: ldr     d7, [sp, #11784]
    +0x16fc: eor     v4.8b, v5.8b, v4.8b
    +0x1700: ldr     d5, [x19, #2208]
    +0x1704: eor     v2.8b, v3.8b, v2.8b
    +0x1708: ldr     d3, [x19, #2216]
    +0x170c: ldr     d6, [sp, #11776]
    +0x1710: ldr     d17, [sp, #11800]
    +0x1714: ldr     d16, [sp, #11792]
    +0x1718: str     d0, [sp, #11744]
    +0x171c: eor     v3.8b, v7.8b, v3.8b
    +0x1720: ldr     d7, [x19, #2232]
    +0x1724: eor     v5.8b, v6.8b, v5.8b
    +0x1728: ldr     d6, [x19, #2224]
    +0x172c: ldr     d0, [sp, #11816]
    +0x1730: str     d1, [sp, #11752]
    +0x1734: eor     v7.8b, v17.8b, v7.8b
    +0x1738: ldr     d1, [x19, #2248]
    +0x173c: str     d4, [sp, #11760]
    +0x1740: ldr     d4, [x19, #2256]
    +0x1744: eor     v6.8b, v16.8b, v6.8b
    +0x1748: ldr     d17, [sp, #11824]
    +0x174c: eor     v0.8b, v0.8b, v1.8b
    +0x1750: str     d2, [sp, #11768]
    +0x1754: ldr     d1, [sp, #11832]
    +0x1758: eor     v2.8b, v17.8b, v4.8b
    +0x175c: ldr     d4, [x19, #2264]
    +0x1760: str     d5, [sp, #11776]
    +0x1764: str     d3, [sp, #11784]
    +0x1768: ldr     d3, [x19, #2272]
    +0x176c: ldr     d5, [sp, #11840]
    +0x1770: eor     v1.8b, v1.8b, v4.8b
    +0x1774: str     d6, [sp, #11792]
    +0x1778: ldr     d4, [sp, #11848]
    +0x177c: eor     v3.8b, v5.8b, v3.8b
    +0x1780: str     d7, [sp, #11800]
    +0x1784: ldr     d5, [x19, #2280]
    +0x1788: ldr     d6, [x19, #2288]
    +0x178c: ldr     d7, [sp, #11856]
    +0x1790: ldr     d16, [x19, #2240]
    +0x1794: eor     v4.8b, v4.8b, v5.8b
    +0x1798: ldr     d18, [sp, #11808]
    +0x179c: str     d0, [sp, #11816]
    +0x17a0: eor     v5.8b, v7.8b, v6.8b
    +0x17a4: ldr     d0, [sp, #11864]
    +0x17a8: ldr     d6, [x19, #2296]
    +0x17ac: eor     v16.8b, v18.8b, v16.8b
    +0x17b0: str     d2, [sp, #11824]
    +0x17b4: ldr     d2, [sp, #11872]
    +0x17b8: eor     v0.8b, v0.8b, v6.8b
    +0x17bc: str     d1, [sp, #11832]
    +0x17c0: ldr     d1, [x19, #2304]
    +0x17c4: str     d3, [sp, #11840]
    +0x17c8: eor     v1.8b, v2.8b, v1.8b
    +0x17cc: str     d16, [sp, #11808]
    +0x17d0: str     d4, [sp, #11848]
    +0x17d4: str     d5, [sp, #11856]
    +0x17d8: str     d0, [sp, #11864]
    +0x17dc: str     d1, [sp, #11872]
    +0x17e0: bl      <mldsa_keccakf1600_permute>
    +0x17e4: ldr     d0, [x19, #2312]
    +0x17e8: ldr     d1, [sp, #11744]
    +0x17ec: add     x0, sp, #0x2, lsl #12
    +0x17f0: ldr     d2, [x19, #2320]
    +0x17f4: ldr     d3, [sp, #11752]
    +0x17f8: add     x0, x0, #0xde0
    +0x17fc: eor     v0.8b, v1.8b, v0.8b
    +0x1800: ldr     d4, [x19, #2328]
    +0x1804: ldr     d5, [sp, #11760]
    +0x1808: eor     v1.8b, v3.8b, v2.8b
    +0x180c: ldr     d2, [x19, #2336]
    +0x1810: ldr     d3, [sp, #11768]
    +0x1814: ldr     d7, [sp, #11784]
    +0x1818: eor     v4.8b, v5.8b, v4.8b
    +0x181c: ldr     d5, [x19, #2344]
    +0x1820: eor     v2.8b, v3.8b, v2.8b
    +0x1824: ldr     d3, [x19, #2352]
    +0x1828: ldr     d6, [sp, #11776]
    +0x182c: ldr     d17, [sp, #11800]
    +0x1830: ldr     d16, [sp, #11792]
    +0x1834: str     d0, [sp, #11744]
    +0x1838: eor     v3.8b, v7.8b, v3.8b
    +0x183c: ldr     d7, [x19, #2368]
    +0x1840: eor     v5.8b, v6.8b, v5.8b
    +0x1844: ldr     d6, [x19, #2360]
    +0x1848: ldr     d0, [sp, #11816]
    +0x184c: str     d1, [sp, #11752]
    +0x1850: eor     v7.8b, v17.8b, v7.8b
    +0x1854: ldr     d1, [x19, #2384]
    +0x1858: str     d4, [sp, #11760]
    +0x185c: ldr     d4, [x19, #2392]
    +0x1860: eor     v6.8b, v16.8b, v6.8b
    +0x1864: ldr     d17, [sp, #11824]
    +0x1868: eor     v0.8b, v0.8b, v1.8b
    +0x186c: str     d2, [sp, #11768]
    +0x1870: ldr     d1, [sp, #11832]
    +0x1874: eor     v2.8b, v17.8b, v4.8b
    +0x1878: ldr     d4, [x19, #2400]
    +0x187c: str     d5, [sp, #11776]
    +0x1880: str     d3, [sp, #11784]
    +0x1884: ldr     d3, [x19, #2408]
    +0x1888: ldr     d5, [sp, #11840]
    +0x188c: eor     v1.8b, v1.8b, v4.8b
    +0x1890: str     d6, [sp, #11792]
    +0x1894: ldr     d4, [sp, #11848]
    +0x1898: eor     v3.8b, v5.8b, v3.8b
    +0x189c: str     d7, [sp, #11800]
    +0x18a0: ldr     d5, [x19, #2416]
    +0x18a4: ldr     d6, [x19, #2424]
    +0x18a8: ldr     d7, [sp, #11856]
    +0x18ac: ldr     d16, [x19, #2376]
    +0x18b0: eor     v4.8b, v4.8b, v5.8b
    +0x18b4: ldr     d18, [sp, #11808]
    +0x18b8: str     d0, [sp, #11816]
    +0x18bc: eor     v5.8b, v7.8b, v6.8b
    +0x18c0: ldr     d0, [sp, #11864]
    +0x18c4: ldr     d6, [x19, #2432]
    +0x18c8: eor     v16.8b, v18.8b, v16.8b
    +0x18cc: str     d2, [sp, #11824]
    +0x18d0: ldr     d2, [sp, #11872]
    +0x18d4: eor     v0.8b, v0.8b, v6.8b
    +0x18d8: str     d1, [sp, #11832]
    +0x18dc: ldr     d1, [x19, #2440]
    +0x18e0: str     d3, [sp, #11840]
    +0x18e4: eor     v1.8b, v2.8b, v1.8b
    +0x18e8: str     d16, [sp, #11808]
    +0x18ec: str     d4, [sp, #11848]
    +0x18f0: str     d5, [sp, #11856]
    +0x18f4: str     d0, [sp, #11864]
    +0x18f8: str     d1, [sp, #11872]
    +0x18fc: bl      <mldsa_keccakf1600_permute>
    +0x1900: ldr     d0, [x19, #2448]
    +0x1904: ldr     d1, [sp, #11744]
    +0x1908: add     x0, sp, #0x2, lsl #12
    +0x190c: ldr     d2, [x19, #2456]
    +0x1910: ldr     d3, [sp, #11752]
    +0x1914: add     x0, x0, #0xde0
    +0x1918: eor     v0.8b, v1.8b, v0.8b
    +0x191c: ldr     d4, [x19, #2464]
    +0x1920: ldr     d5, [sp, #11760]
    +0x1924: eor     v1.8b, v3.8b, v2.8b
    +0x1928: ldr     d2, [x19, #2472]
    +0x192c: ldr     d3, [sp, #11768]
    +0x1930: ldr     d7, [sp, #11784]
    +0x1934: eor     v4.8b, v5.8b, v4.8b
    +0x1938: ldr     d5, [x19, #2480]
    +0x193c: eor     v2.8b, v3.8b, v2.8b
    +0x1940: ldr     d3, [x19, #2488]
    +0x1944: ldr     d6, [sp, #11776]
    +0x1948: ldr     d17, [sp, #11800]
    +0x194c: ldr     d16, [sp, #11792]
    +0x1950: str     d0, [sp, #11744]
    +0x1954: eor     v3.8b, v7.8b, v3.8b
    +0x1958: ldr     d7, [x19, #2504]
    +0x195c: eor     v5.8b, v6.8b, v5.8b
    +0x1960: ldr     d6, [x19, #2496]
    +0x1964: ldr     d0, [sp, #11816]
    +0x1968: str     d1, [sp, #11752]
    +0x196c: eor     v7.8b, v17.8b, v7.8b
    +0x1970: ldr     d1, [x19, #2520]
    +0x1974: str     d4, [sp, #11760]
    +0x1978: ldr     d4, [x19, #2528]
    +0x197c: eor     v6.8b, v16.8b, v6.8b
    +0x1980: ldr     d17, [sp, #11824]
    +0x1984: eor     v0.8b, v0.8b, v1.8b
    +0x1988: str     d2, [sp, #11768]
    +0x198c: ldr     d1, [sp, #11832]
    +0x1990: eor     v2.8b, v17.8b, v4.8b
    +0x1994: ldr     d4, [x19, #2536]
    +0x1998: str     d5, [sp, #11776]
    +0x199c: str     d3, [sp, #11784]
    +0x19a0: ldr     d3, [x19, #2544]
    +0x19a4: ldr     d5, [sp, #11840]
    +0x19a8: eor     v1.8b, v1.8b, v4.8b
    +0x19ac: str     d6, [sp, #11792]
    +0x19b0: ldr     d4, [sp, #11848]
    +0x19b4: eor     v3.8b, v5.8b, v3.8b
    +0x19b8: str     d7, [sp, #11800]
    +0x19bc: ldr     d5, [x19, #2552]
    +0x19c0: ldr     d6, [x19, #2560]
    +0x19c4: ldr     d7, [sp, #11856]
    +0x19c8: ldr     d16, [x19, #2512]
    +0x19cc: eor     v4.8b, v4.8b, v5.8b
    +0x19d0: ldr     d18, [sp, #11808]
    +0x19d4: str     d0, [sp, #11816]
    +0x19d8: eor     v5.8b, v7.8b, v6.8b
    +0x19dc: ldr     d0, [sp, #11864]
    +0x19e0: ldr     d6, [x19, #2568]
    +0x19e4: eor     v16.8b, v18.8b, v16.8b
    +0x19e8: str     d2, [sp, #11824]
    +0x19ec: ldr     d2, [sp, #11872]
    +0x19f0: eor     v0.8b, v0.8b, v6.8b
    +0x19f4: str     d1, [sp, #11832]
    +0x19f8: ldr     d1, [x19, #2576]
    +0x19fc: str     d3, [sp, #11840]
    +0x1a00: eor     v1.8b, v2.8b, v1.8b
    +0x1a04: str     d16, [sp, #11808]
    +0x1a08: str     d4, [sp, #11848]
    +0x1a0c: str     d5, [sp, #11856]
    +0x1a10: str     d0, [sp, #11864]
    +0x1a14: str     d1, [sp, #11872]
    +0x1a18: bl      <mldsa_keccakf1600_permute>
    +0x1a1c: ldr     d0, [x19, #2584]
    +0x1a20: ldr     d1, [sp, #11744]
    +0x1a24: add     x0, sp, #0x2, lsl #12
    +0x1a28: ldrb    w8, [x22, #8]
    +0x1a2c: ldrb    w9, [x22, #135]
    +0x1a30: add     x0, x0, #0xde0
    +0x1a34: eor     v0.8b, v1.8b, v0.8b
    +0x1a38: eor     w8, w8, #0x1f
    +0x1a3c: eor     w9, w9, #0x80
    +0x1a40: strb    w8, [x22, #8]
    +0x1a44: mov     w8, #0x88
    +0x1a48: strb    w9, [x22, #135]
    +0x1a4c: str     d0, [sp, #11744]
    +0x1a50: str     w8, [sp, #11944]
    +0x1a54: bl      <mldsa_keccakf1600_permute>
    +0x1a58: ldr     q0, [sp, #11744]
    +0x1a5c: ldr     q1, [sp, #11760]
    +0x1a60: add     x8, sp, #0x2, lsl #12
    +0x1a64: ldr     q2, [sp, #11792]
    +0x1a68: add     x8, x8, #0xde0
    +0x1a6c: orr     w13, w26, w27
    +0x1a70: str     q0, [sp, #11584]
    +0x1a74: ldr     q0, [sp, #11776]
    +0x1a78: str     q1, [sp, #11600]
    +0x1a7c: str     q0, [sp, #11616]
    +0x1a80: movi    v0.2d, #0x0
    +0x1a84: str     q2, [sp, #11632]
    +0x1a88: str     q0, [sp, #11808]
    +0x1a8c: str     q0, [sp, #11824]
    +0x1a90: str     q0, [sp, #11840]
    +0x1a94: str     q0, [sp, #11856]
    +0x1a98: str     q0, [sp, #11872]
    +0x1a9c: str     q0, [sp, #11888]
    +0x1aa0: str     q0, [sp, #11904]
    +0x1aa4: str     q0, [sp, #11920]
    +0x1aa8: str     q0, [sp, #11936]
    +0x1aac: str     q0, [sp, #11744]
    +0x1ab0: str     q0, [sp, #11760]
    +0x1ab4: str     q0, [sp, #11776]
    +0x1ab8: str     q0, [sp, #11792]
    +0x1abc: ldr     q0, [sp, #11648]
    +0x1ac0: ldr     q1, [sp, #11664]
    +0x1ac4: ldr     q2, [sp, #11584]
    +0x1ac8: ldr     q3, [sp, #11600]
    +0x1acc: ldr     q4, [sp, #11680]
    +0x1ad0: ldr     q5, [sp, #11696]
    +0x1ad4: ldr     q6, [sp, #11616]
    +0x1ad8: ldr     q7, [sp, #11632]
    +0x1adc: eor     v0.16b, v2.16b, v0.16b
    +0x1ae0: eor     v1.16b, v3.16b, v1.16b
    +0x1ae4: eor     v2.16b, v6.16b, v4.16b
    +0x1ae8: eor     v3.16b, v7.16b, v5.16b
    +0x1aec: orr     v4.16b, v2.16b, v0.16b
    +0x1af0: orr     v5.16b, v1.16b, v3.16b
    +0x1af4: eor     v0.16b, v0.16b, v2.16b
    +0x1af8: eor     v1.16b, v3.16b, v1.16b
    +0x1afc: orr     v2.16b, v5.16b, v4.16b
    +0x1b00: eor     v0.16b, v1.16b, v0.16b
    +0x1b04: mov     d3, v2.d[1]
    +0x1b08: mov     d1, v0.d[1]
    +0x1b0c: orr     v2.8b, v2.8b, v3.8b
    +0x1b10: eor     v0.8b, v0.8b, v1.8b
    +0x1b14: fmov    x8, d2
    +0x1b18: fmov    x10, d0
    +0x1b1c: orr     x8, x8, x8, lsr #32
    +0x1b20: eor     x10, x10, x10, lsr #32
    +0x1b24: lsr     x9, x8, #16
    +0x1b28: orr     w8, w8, w9
    +0x1b2c: eor     x9, x10, x10, lsr #16
    +0x1b30: ldr     x10, [sp, #8]
    +0x1b34: orr     w8, w8, w8, lsr #8
    +0x1b38: sub     x8, x10, w8, uxtb
    +0x1b3c: lsr     x10, x9, #8
    +0x1b40: ldp     w12, w11, [sp, #24]
    +0x1b44: lsr     x8, x8, #32
    +0x1b48: eor     w9, w9, w10
    +0x1b4c: and     w10, w9, #0xff
    +0x1b50: orr     w11, w12, w11
    +0x1b54: orr     w12, w24, w25
    +0x1b58: eor     w8, w8, w9
    +0x1b5c: orr     w9, w11, w12
    +0x1b60: orr     w11, w13, w28
    +0x1b64: orr     w9, w9, w11
    +0x1b68: orr     w11, w20, w23
    +0x1b6c: eor     w8, w8, w10
    +0x1b70: ldr     w10, [sp, #20]
    +0x1b74: orr     w9, w9, w11
    +0x1b78: orr     w8, w9, w8
    +0x1b7c: eor     w10, w21, w10
    +0x1b80: orr     w8, w10, w8
    +0x1b84: tst     w8, #0xff
    +0x1b88: b.eq    <mldsa87_pk_from_sk+0x1ba4>
    +0x1b8c: mov     x0, x19
    +0x1b90: mov     w1, wzr
    +0x1b94: mov     w2, #0xa20
    +0x1b98: bl      <memset>
    +0x1b9c: mov     w19, #0xfffffff9
    +0x1ba0: b       <mldsa87_pk_from_sk+0x1ba8>
    +0x1ba4: mov     w19, wzr
    +0x1ba8: add     x0, sp, #0x20
    +0x1bac: mov     w1, wzr
    +0x1bb0: mov     w2, #0xd00
    +0x1bb4: add     x20, sp, #0x20
    +0x1bb8: bl      <memset>
    +0x1bbc: add     x0, sp, #0xd20
    +0x1bc0: mov     w1, wzr
    +0x1bc4: mov     w2, #0x400
    +0x1bc8: add     x20, sp, #0xd20
    +0x1bcc: bl      <memset>
    +0x1bd0: add     x0, sp, #0x1, lsl #12
    +0x1bd4: mov     w1, wzr
    +0x1bd8: add     x0, x0, #0x120
    +0x1bdc: mov     w2, #0x1c00
    +0x1be0: add     x20, sp, #0x1, lsl #12
    +0x1be4: add     x20, x20, #0x120
    +0x1be8: bl      <memset>
    +0x1bec: movi    v0.2d, #0x0
    +0x1bf0: add     x8, sp, #0x2, lsl #12
    +0x1bf4: add     x8, x8, #0xd20
    +0x1bf8: str     q0, [sp, #11568]
    +0x1bfc: str     q0, [sp, #11552]
    +0x1c00: add     x8, sp, #0x2, lsl #12
    +0x1c04: str     q0, [sp, #11632]
    +0x1c08: str     q0, [sp, #11616]
    +0x1c0c: add     x8, x8, #0xd40
    +0x1c10: str     q0, [sp, #11600]
    +0x1c14: str     q0, [sp, #11584]
    +0x1c18: add     x8, sp, #0x2, lsl #12
    +0x1c1c: str     q0, [sp, #11696]
    +0x1c20: str     q0, [sp, #11680]
    +0x1c24: add     x8, x8, #0xd80
    +0x1c28: str     q0, [sp, #11664]
    +0x1c2c: str     q0, [sp, #11648]
    +0x1c30: add     x8, sp, #0x2, lsl #12
    +0x1c34: str     q0, [sp, #11728]
    +0x1c38: add     x8, x8, #0xdc0
    +0x1c3c: str     q0, [sp, #11712]
    +0x1c40: adrp    x8, <page>
    +0x1c44: ldr     x8, [x8, #4088]
    +0x1c48: ldr     x9, [sp, #11960]
    +0x1c4c: ldr     x8, [x8]
    +0x1c50: cmp     x8, x9
    +0x1c54: b.ne    <mldsa87_pk_from_sk+0x1ca4>
    +0x1c58: mov     w0, w19
    +0x1c5c: mov     sp, x29
    +0x1c60: ldp     x20, x19, [sp, #80]
    +0x1c64: ldp     x22, x21, [sp, #64]
    +0x1c68: ldp     x24, x23, [sp, #48]
    +0x1c6c: ldp     x26, x25, [sp, #32]
    +0x1c70: ldp     x28, x27, [sp, #16]
    +0x1c74: ldp     x29, x30, [sp], #96
    +0x1c78: mov     x1, #0x0
    +0x1c7c: mov     x2, #0x0
    +0x1c80: mov     x3, #0x0
    +0x1c84: mov     x4, #0x0
    +0x1c88: mov     x8, #0x0
    +0x1c8c: mov     x9, #0x0
    +0x1c90: mov     x10, #0x0
    +0x1c94: mov     x11, #0x0
    +0x1c98: mov     x12, #0x0
    +0x1c9c: mov     x13, #0x0
    +0x1ca0: ret     
    +0x1ca4: bl      <__stack_chk_fail>

    memset@plt:
       +0x0: adrp    x16, <page>
       +0x4: ldr     x17, [x16, #4072]
       +0x8: add     x16, x16, #0xfe8
       +0xc: br      x17
 ***)

let MLDSA_NATIVE_PK_FROM_SK_87_CLANG23_O3_MONO_REDUCED_RAM_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
   [layout_range "mldsa87_pk_from_sk";
    layout_range "plt_memset"];;

(* ------------------------------------------------------------------------- *)
(* Correctness, assuming the contracts for memset and memcpy. The secret key at sk is    *)
(* the 4896 bytes skb; if it passes the checks, mld_pk_from_sk_valid, the    *)
(* public key at pk becomes mld_pk_from_sk_pk and the result is 0, and       *)
(* otherwise the public key is zeroed and the result is MLD_ERR_INVALID_KEY  *)
(* (-7 as a 32-bit integer). The expansion of the matrix from rho is assumed *)
(* to terminate. The stack is the 12096 bytes of the function and the 5312  *)
(* of the callees below them.                                                *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_PK_FROM_SK_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!mf mc ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev
     ==> !pk sk skb guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          32768 <= val stackpointer /\ val(stackpointer:int64) < 2 EXP 63 /\
          mld_matrix_terminates 8 7 (mld_sk_rho skb) /\
          nonoverlapping (pk,2592) (word_sub stackpointer (word 17408),17408) /\
          ALLPAIRS nonoverlapping
           [(pk,2592); (word_sub stackpointer (word 17408),17408)]
           [(sk,4896); (word pc,libmldsa_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                    read PC s = word (pc + mldsa87_pk_from_sk) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [pk; sk] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    (!j. j < 4896
                         ==> read(memory :> bytes8(word_add sk (word j))) s =
                             skb j))
               (\s. read PC s = returnaddress /\
                    C_RETURN s =
                    (if mld_pk_from_sk_valid 8 7 2 mld_polyeta_unpack_2 96
                          skb
                     then word 0 else word 4294967289) /\
                    (!j. j < 2592
                         ==> read(memory :> bytes8(word_add pk (word j))) s =
                             if mld_pk_from_sk_valid 8 7 2
                                  mld_polyeta_unpack_2 96 skb
                             then mld_pk_from_sk_pk 7 mld_polyeta_unpack_2 96
                                   skb j
                             else word 0))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(pk,2592);
                  memory :> bytes(word_sub stackpointer (word 17408),17408)])`;;

let MLDSA_NATIVE_PK_FROM_SK_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLDSA_NATIVE_PK_FROM_SK_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, rho, the result of the checks,    *)
(* the address of memset and the stack, with all accesses within the         *)
(* arguments, the stack, the GOT entries and the stack guard, the region     *)
(* (ea,el) that memset may read and the constants of the callees, and the    *)
(* writes within the public key and the stack.                               *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_PK_FROM_SK_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT =
  `!mf mc ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev
     ==> exists f_events.
          forall e pk sk skb guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          32768 <= val stackpointer /\ val(stackpointer:int64) < 2 EXP 63 /\
          mld_matrix_terminates 8 7 (mld_sk_rho skb) /\
          nonoverlapping (pk,2592) (word_sub stackpointer (word 17408),17408) /\
          ALLPAIRS nonoverlapping
           [(pk,2592); (word_sub stackpointer (word 17408),17408)]
           [(sk,4896); (word pc,libmldsa_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                    read PC s = word (pc + mldsa87_pk_from_sk) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [pk; sk] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    (!j. j < 4896
                         ==> read(memory :> bytes8(word_add sk (word j))) s =
                             skb j) /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    C_RETURN s =
                    (if mld_pk_from_sk_valid 8 7 2 mld_polyeta_unpack_2 96
                          skb
                     then word 0 else word 4294967289) /\
                    (!j. j < 2592
                         ==> read(memory :> bytes8(word_add pk (word j))) s =
                             if mld_pk_from_sk_valid 8 7 2
                                  mld_polyeta_unpack_2 96 skb
                             then mld_pk_from_sk_pk 7 mld_polyeta_unpack_2 96
                                   skb j
                             else word 0) /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events pk sk (mld_sk_rho skb)
                              (mld_pk_from_sk_valid 8 7 2 mld_polyeta_unpack_2
                                96 skb)
                              guard mf mc pc (word_sub stackpointer (word 17408))
                              returnaddress /\
                       memaccess_inbounds e2
                        [sk,4896; pk,2592;
                         word_sub stackpointer (word 17408),17408;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; word(pc + got_memcpy),8; ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192;
                         word(pc + rodata_mld_zetas),1024;
                         word(pc + mldsa87_pk_from_sk_consts),128;
                         word(pc + mldsa87_polyeta_unpack_consts),128;
                         word(pc + mld_compute_pack_t0_t187_consts),272]
                        [pk,2592; word_sub stackpointer (word 17408),17408]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(pk,2592);
                  memory :> bytes(word_sub stackpointer (word 17408),17408)])`;;

let MLDSA_NATIVE_PK_FROM_SK_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_PK_FROM_SK_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_PK_FROM_SK_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT =
  `!mf mc ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev
     ==> exists f_events.
          forall e pk sk skb guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          32768 <= val stackpointer /\ val(stackpointer:int64) < 2 EXP 63 /\
          mld_matrix_terminates 8 7 (mld_sk_rho skb) /\
          nonoverlapping (pk,2592) (word_sub stackpointer (word 17408),17408) /\
          ALLPAIRS nonoverlapping
           [(pk,2592); (word_sub stackpointer (word 17408),17408)]
           [(sk,4896); (word pc,libmldsa_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                    read PC s = word (pc + mldsa87_pk_from_sk) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [pk; sk] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    (!j. j < 4896
                         ==> read(memory :> bytes8(word_add sk (word j))) s =
                             skb j) /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events pk sk (mld_sk_rho skb)
                              (mld_pk_from_sk_valid 8 7 2 mld_polyeta_unpack_2
                                96 skb)
                              guard mf mc pc (word_sub stackpointer (word 17408))
                              returnaddress /\
                       memaccess_inbounds e2
                        [sk,4896; pk,2592;
                         word_sub stackpointer (word 17408),17408;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; word(pc + got_memcpy),8; ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192;
                         word(pc + rodata_mld_zetas),1024;
                         word(pc + mldsa87_pk_from_sk_consts),128;
                         word(pc + mldsa87_polyeta_unpack_consts),128;
                         word(pc + mld_compute_pack_t0_t187_consts),272]
                        [pk,2592; word_sub stackpointer (word 17408),17408]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(pk,2592);
                  memory :> bytes(word_sub stackpointer (word 17408),17408)])`;;

let MLDSA_NATIVE_PK_FROM_SK_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_PK_FROM_SK_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT;;
