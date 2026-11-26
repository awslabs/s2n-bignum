(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The public key of a secret key: the statement. This is the code for       *)
(* mldsa44_pk_from_sk (mld_sign_pk_from_sk in sign.c) from mldsa-native's    *)
(* portable C implementation compiled by clang 23 with -O3 as one            *)
(* translation unit with MLD_CONFIG_REDUCE_RAM (see mldsa_native/README.md). *)
(* It copies rho, the key and tr from the secret key to the stack, unpacks   *)
(* the four polynomials of s1 with mldsa44_polyeta_unpack and checks them    *)
(* with mldsa44_polyvecl_chknorm, unpacks the four polynomials of s2 one at  *)
(* a time and checks each with an inlined loop, transforms s1 with           *)
(* mldsa_poly_ntt, recomputes t1 into the public key and t0 into a buffer    *)
(* with mld_compute_pack_t0_t144, compares t0 with that in the secret key    *)
(* with an inlined constant-time comparison (a loop of 52 passes of vector   *)
(* instructions), hashes the public key with an inlined SHAKE256 (ten calls  *)
(* of mldsa_keccakf1600_permute) and compares the hash with tr, all in       *)
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
(* code declassifies. The stack is the 7344 bytes of the function and the    *)
(* 5328 of the callees below them.                                           *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native.ml";;
needs "arm/proofs/utils/mlkem_native_libc_full.ml";;
needs "common/mldsa_native_sign.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/polyvecl_chknorm_44_spec.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/compute_pack_t0_t1_44_spec.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/libmldsa.ml";;

(*** The code in the image, and the PLT stub for memset:

    mldsa44_pk_from_sk:
       +0x0: stp     x29, x30, [sp, #-96]!
       +0x4: stp     x28, x27, [sp, #16]
       +0x8: stp     x26, x25, [sp, #32]
       +0xc: stp     x24, x23, [sp, #48]
      +0x10: stp     x22, x21, [sp, #64]
      +0x14: stp     x20, x19, [sp, #80]
      +0x18: mov     x29, sp
      +0x1c: sub     x9, sp, #0x1, lsl #12
      +0x20: sub     x9, x9, #0xc40
      +0x24: and     x9, x9, #0xffffffffffffffe0
      +0x28: sub     sp, sp, #0x1, lsl #12
      +0x2c: cmp     sp, x9
      +0x30: b.le    <mldsa44_pk_from_sk+0x44>
      +0x34: ldr     xzr, [sp]
      +0x38: sub     sp, sp, #0x1, lsl #12
      +0x3c: cmp     sp, x9
      +0x40: b.gt    <mldsa44_pk_from_sk+0x34>
      +0x44: mov     sp, x9
      +0x48: adrp    x8, <page>
      +0x4c: ldr     xzr, [sp]
      +0x50: mov     x21, x1
      +0x54: ldr     x8, [x8, #4088]
      +0x58: mov     x19, x0
      +0x5c: add     x24, sp, #0x1, lsl #12
      +0x60: add     x0, sp, #0xaa0
      +0x64: add     x24, x24, #0xb60
      +0x68: add     x27, sp, #0xaa0
      +0x6c: ldr     x8, [x8]
      +0x70: str     x8, [sp, #7224]
      +0x74: ldp     q0, q1, [x1]
      +0x78: str     q0, [sp, #6976]
      +0x7c: ldp     q0, q2, [x1, #32]
      +0x80: str     q1, [sp, #6992]
      +0x84: str     q0, [sp, #6816]
      +0x88: ldp     q1, q0, [x1, #96]
      +0x8c: str     q2, [sp, #6832]
      +0x90: str     q0, [sp, #6960]
      +0x94: ldp     q0, q2, [x1, #64]
      +0x98: add     x1, x1, #0x80
      +0x9c: str     q1, [sp, #6944]
      +0xa0: str     q2, [sp, #6928]
      +0xa4: str     q0, [sp, #6912]
      +0xa8: bl      <mldsa44_polyeta_unpack>
      +0xac: add     x0, x27, #0x400
      +0xb0: add     x1, x21, #0xe0
      +0xb4: bl      <mldsa44_polyeta_unpack>
      +0xb8: add     x0, x27, #0x800
      +0xbc: add     x1, x21, #0x140
      +0xc0: bl      <mldsa44_polyeta_unpack>
      +0xc4: add     x0, x27, #0xc00
      +0xc8: add     x1, x21, #0x1a0
      +0xcc: bl      <mldsa44_polyeta_unpack>
      +0xd0: add     x0, sp, #0xaa0
      +0xd4: mov     w1, #0x3
      +0xd8: bl      <mldsa44_polyvecl_chknorm>
      +0xdc: mov     w20, w0
      +0xe0: add     x0, sp, #0x6a0
      +0xe4: add     x1, x21, #0x200
      +0xe8: add     x23, sp, #0x6a0
      +0xec: bl      <mldsa44_polyeta_unpack>
      +0xf0: mov     x8, xzr
      +0xf4: mov     w22, wzr
      +0xf8: mov     w9, #0x2
      +0xfc: ldrsw   x10, [x23, x8]
     +0x100: add     x8, x8, #0x4
     +0x104: cmp     x8, #0x400
     +0x108: mov     w11, w10
     +0x10c: lsr     x10, x10, #31
     +0x110: neg     w12, w11
     +0x114: bic     w11, w11, w10
     +0x118: and     w10, w12, w10
     +0x11c: orr     w10, w10, w11
     +0x120: sub     w10, w9, w10
     +0x124: sxtw    x10, w10
     +0x128: lsr     x10, x10, #31
     +0x12c: orr     w22, w22, w10
     +0x130: b.ne    <mldsa44_pk_from_sk+0xfc>
     +0x134: add     x0, sp, #0x6a0
     +0x138: add     x1, x21, #0x260
     +0x13c: add     x25, sp, #0x6a0
     +0x140: bl      <mldsa44_polyeta_unpack>
     +0x144: mov     x8, xzr
     +0x148: mov     w23, wzr
     +0x14c: mov     w9, #0x2
     +0x150: ldrsw   x10, [x25, x8]
     +0x154: add     x8, x8, #0x4
     +0x158: cmp     x8, #0x400
     +0x15c: mov     w11, w10
     +0x160: lsr     x10, x10, #31
     +0x164: neg     w12, w11
     +0x168: bic     w11, w11, w10
     +0x16c: and     w10, w12, w10
     +0x170: orr     w10, w10, w11
     +0x174: sub     w10, w9, w10
     +0x178: sxtw    x10, w10
     +0x17c: lsr     x10, x10, #31
     +0x180: orr     w23, w23, w10
     +0x184: b.ne    <mldsa44_pk_from_sk+0x150>
     +0x188: add     x0, sp, #0x6a0
     +0x18c: add     x1, x21, #0x2c0
     +0x190: add     x26, sp, #0x6a0
     +0x194: bl      <mldsa44_polyeta_unpack>
     +0x198: mov     x8, xzr
     +0x19c: mov     w25, wzr
     +0x1a0: mov     w9, #0x2
     +0x1a4: ldrsw   x10, [x26, x8]
     +0x1a8: add     x8, x8, #0x4
     +0x1ac: cmp     x8, #0x400
     +0x1b0: mov     w11, w10
     +0x1b4: lsr     x10, x10, #31
     +0x1b8: neg     w12, w11
     +0x1bc: bic     w11, w11, w10
     +0x1c0: and     w10, w12, w10
     +0x1c4: orr     w10, w10, w11
     +0x1c8: sub     w10, w9, w10
     +0x1cc: sxtw    x10, w10
     +0x1d0: lsr     x10, x10, #31
     +0x1d4: orr     w25, w25, w10
     +0x1d8: b.ne    <mldsa44_pk_from_sk+0x1a4>
     +0x1dc: add     x0, sp, #0x6a0
     +0x1e0: add     x1, x21, #0x320
     +0x1e4: add     x28, sp, #0x6a0
     +0x1e8: bl      <mldsa44_polyeta_unpack>
     +0x1ec: mov     x8, xzr
     +0x1f0: mov     w26, wzr
     +0x1f4: mov     w9, #0x2
     +0x1f8: ldrsw   x10, [x28, x8]
     +0x1fc: add     x8, x8, #0x4
     +0x200: cmp     x8, #0x400
     +0x204: mov     w11, w10
     +0x208: lsr     x10, x10, #31
     +0x20c: neg     w12, w11
     +0x210: bic     w11, w11, w10
     +0x214: and     w10, w12, w10
     +0x218: orr     w10, w10, w11
     +0x21c: sub     w10, w9, w10
     +0x220: sxtw    x10, w10
     +0x224: lsr     x10, x10, #31
     +0x228: orr     w26, w26, w10
     +0x22c: b.ne    <mldsa44_pk_from_sk+0x1f8>
     +0x230: add     x0, sp, #0xaa0
     +0x234: bl      <mldsa_poly_ntt>
     +0x238: add     x0, x27, #0x400
     +0x23c: bl      <mldsa_poly_ntt>
     +0x240: add     x0, x27, #0x800
     +0x244: bl      <mldsa_poly_ntt>
     +0x248: add     x0, x27, #0xc00
     +0x24c: bl      <mldsa_poly_ntt>
     +0x250: ldr     q0, [sp, #6976]
     +0x254: ldr     q1, [sp, #6992]
     +0x258: add     x4, sp, #0x1, lsl #12
     +0x25c: add     x0, x19, #0x20
     +0x260: add     x1, sp, #0x20
     +0x264: add     x2, sp, #0xaa0
     +0x268: add     x3, x21, #0x200
     +0x26c: add     x4, x4, #0xb40
     +0x270: stp     q0, q1, [x19]
     +0x274: add     x27, sp, #0x20
     +0x278: bl      <mld_compute_pack_t0_t144>
     +0x27c: movi    v0.2d, #0x0
     +0x280: adrp    x8, <page>
     +0x284: movi    v1.2d, #0x0
     +0x288: movi    v3.2d, #0x0
     +0x28c: movi    v2.2d, #0x0
     +0x290: ldr     q17, [x8, #1472]
     +0x294: movi    v4.2d, #0x0
     +0x298: movi    v5.2d, #0x0
     +0x29c: adrp    x8, <page>
     +0x2a0: movi    v7.2d, #0x0
     +0x2a4: movi    v6.2d, #0x0
     +0x2a8: adrp    x9, <page>
     +0x2ac: movi    v16.2d, #0x0
     +0x2b0: movi    v18.2d, #0x0
     +0x2b4: adrp    x10, <page>
     +0x2b8: ldr     q19, [x8, #1488]
     +0x2bc: ldr     q20, [x9, #1504]
     +0x2c0: ldr     q21, [x10, #1520]
     +0x2c4: add     x8, x21, #0x390
     +0x2c8: mov     w9, #0x390
     +0x2cc: add     x10, x27, x9
     +0x2d0: ldp     q23, q24, [x8, #-16]
     +0x2d4: sub     x11, x10, #0x390
     +0x2d8: sub     x10, x10, #0x380
     +0x2dc: add     x9, x9, #0x20
     +0x2e0: ldr     q22, [x11]
     +0x2e4: ldr     q25, [x10]
     +0x2e8: cmp     x9, #0xa10
     +0x2ec: add     x8, x8, #0x20
     +0x2f0: eor     v22.16b, v23.16b, v22.16b
     +0x2f4: eor     v23.16b, v24.16b, v25.16b
     +0x2f8: tbl     v24.16b, {v22.16b}, v19.16b
     +0x2fc: tbl     v25.16b, {v22.16b}, v20.16b
     +0x300: tbl     v26.16b, {v22.16b}, v21.16b
     +0x304: tbl     v27.16b, {v22.16b}, v17.16b
     +0x308: tbl     v28.16b, {v23.16b}, v20.16b
     +0x30c: tbl     v29.16b, {v23.16b}, v21.16b
     +0x310: tbl     v30.16b, {v23.16b}, v17.16b
     +0x314: tbl     v31.16b, {v23.16b}, v19.16b
     +0x318: orr     v0.16b, v22.16b, v0.16b
     +0x31c: orr     v18.16b, v23.16b, v18.16b
     +0x320: eor     v4.16b, v4.16b, v26.16b
     +0x324: eor     v2.16b, v2.16b, v25.16b
     +0x328: eor     v3.16b, v3.16b, v24.16b
     +0x32c: eor     v1.16b, v1.16b, v27.16b
     +0x330: eor     v16.16b, v16.16b, v29.16b
     +0x334: eor     v6.16b, v6.16b, v28.16b
     +0x338: eor     v7.16b, v7.16b, v31.16b
     +0x33c: eor     v5.16b, v5.16b, v30.16b
     +0x340: b.ne    <mldsa44_pk_from_sk+0x2cc>
     +0x344: orr     v0.16b, v18.16b, v0.16b
     +0x348: eor     v3.16b, v7.16b, v3.16b
     +0x34c: mov     x21, xzr
     +0x350: eor     v4.16b, v16.16b, v4.16b
     +0x354: eor     v1.16b, v5.16b, v1.16b
     +0x358: add     x0, sp, #0x1, lsl #12
     +0x35c: eor     v2.16b, v6.16b, v2.16b
     +0x360: movi    v17.2d, #0x0
     +0x364: add     x0, x0, #0xb60
     +0x368: mov     d5, v0.d[1]
     +0x36c: eor     v1.16b, v1.16b, v2.16b
     +0x370: eor     v2.16b, v3.16b, v4.16b
     +0x374: orr     v0.8b, v0.8b, v5.8b
     +0x378: eor     v1.16b, v1.16b, v2.16b
     +0x37c: fmov    x8, d0
     +0x380: mov     d0, v1.d[1]
     +0x384: orr     x8, x8, x8, lsr #32
     +0x388: lsr     x9, x8, #16
     +0x38c: eor     v0.8b, v1.8b, v0.8b
     +0x390: orr     w8, w8, w9
     +0x394: orr     w8, w8, w8, lsr #8
     +0x398: fmov    x9, d0
     +0x39c: sub     x8, x21, w8, uxtb
     +0x3a0: lsr     x10, x9, #32
     +0x3a4: lsr     x8, x8, #32
     +0x3a8: eor     w27, w9, w10
     +0x3ac: eor     w28, w8, w27
     +0x3b0: str     q17, [sp, #7008]
     +0x3b4: stur    q17, [x24, #188]
     +0x3b8: ldp     d0, d1, [x19]
     +0x3bc: str     q17, [sp, #7040]
     +0x3c0: ldp     d2, d3, [x19, #16]
     +0x3c4: ldr     d4, [sp, #7016]
     +0x3c8: ldp     d5, d6, [x19, #32]
     +0x3cc: str     q17, [sp, #7024]
     +0x3d0: ldr     d16, [sp, #7040]
     +0x3d4: str     q17, [sp, #7056]
     +0x3d8: ldr     d7, [sp, #7032]
     +0x3dc: eor     v1.8b, v4.8b, v1.8b
     +0x3e0: str     d0, [sp, #7008]
     +0x3e4: ldp     d0, d4, [x19, #48]
     +0x3e8: str     d2, [sp, #7024]
     +0x3ec: eor     v2.8b, v16.8b, v5.8b
     +0x3f0: ldr     d5, [sp, #7056]
     +0x3f4: ldr     d16, [sp, #7064]
     +0x3f8: eor     v3.8b, v7.8b, v3.8b
     +0x3fc: ldr     d7, [sp, #7048]
     +0x400: str     q17, [sp, #7072]
     +0x404: eor     v0.8b, v5.8b, v0.8b
     +0x408: eor     v4.8b, v16.8b, v4.8b
     +0x40c: ldp     d5, d16, [x19, #64]
     +0x410: eor     v6.8b, v7.8b, v6.8b
     +0x414: ldr     d7, [sp, #7072]
     +0x418: str     q17, [sp, #7088]
     +0x41c: str     d1, [sp, #7016]
     +0x420: ldr     d1, [sp, #7080]
     +0x424: eor     v5.8b, v7.8b, v5.8b
     +0x428: str     d3, [sp, #7032]
     +0x42c: ldp     d3, d7, [x19, #80]
     +0x430: str     d2, [sp, #7040]
     +0x434: ldr     d2, [sp, #7088]
     +0x438: eor     v1.8b, v1.8b, v16.8b
     +0x43c: str     d0, [sp, #7056]
     +0x440: ldr     d0, [sp, #7096]
     +0x444: str     q17, [sp, #7104]
     +0x448: str     d6, [sp, #7048]
     +0x44c: ldp     d6, d16, [x19, #96]
     +0x450: eor     v2.8b, v2.8b, v3.8b
     +0x454: str     q17, [sp, #7120]
     +0x458: eor     v0.8b, v0.8b, v7.8b
     +0x45c: str     d4, [sp, #7064]
     +0x460: ldr     d7, [sp, #7112]
     +0x464: ldr     d3, [sp, #7104]
     +0x468: str     d5, [sp, #7072]
     +0x46c: ldp     d4, d5, [x19, #112]
     +0x470: str     d1, [sp, #7080]
     +0x474: ldr     d1, [sp, #7120]
     +0x478: eor     v3.8b, v3.8b, v6.8b
     +0x47c: str     q17, [sp, #7136]
     +0x480: str     d2, [sp, #7088]
     +0x484: eor     v2.8b, v7.8b, v16.8b
     +0x488: eor     v1.8b, v1.8b, v4.8b
     +0x48c: str     d0, [sp, #7096]
     +0x490: ldr     d0, [sp, #7128]
     +0x494: ldr     d4, [x19, #128]
     +0x498: ldr     d6, [sp, #7136]
     +0x49c: str     q17, [sp, #7184]
     +0x4a0: eor     v0.8b, v0.8b, v5.8b
     +0x4a4: str     d2, [sp, #7112]
     +0x4a8: eor     v2.8b, v6.8b, v4.8b
     +0x4ac: str     q17, [sp, #7168]
     +0x4b0: str     q17, [sp, #7152]
     +0x4b4: str     d3, [sp, #7104]
     +0x4b8: str     d1, [sp, #7120]
     +0x4bc: str     d0, [sp, #7128]
     +0x4c0: str     d2, [sp, #7136]
     +0x4c4: bl      <mldsa_keccakf1600_permute>
     +0x4c8: ldp     d1, d2, [x19, #136]
     +0x4cc: add     x0, sp, #0x1, lsl #12
     +0x4d0: ldr     d0, [sp, #7008]
     +0x4d4: ldr     d3, [sp, #7016]
     +0x4d8: add     x0, x0, #0xb60
     +0x4dc: ldr     d5, [sp, #7024]
     +0x4e0: ldr     d6, [sp, #7040]
     +0x4e4: ldr     d7, [sp, #7048]
     +0x4e8: eor     v0.8b, v0.8b, v1.8b
     +0x4ec: eor     v1.8b, v3.8b, v2.8b
     +0x4f0: ldr     d3, [sp, #7032]
     +0x4f4: ldp     d4, d2, [x19, #152]
     +0x4f8: ldr     d16, [sp, #7056]
     +0x4fc: ldr     d17, [sp, #7064]
     +0x500: ldr     d18, [sp, #7072]
     +0x504: str     d0, [sp, #7008]
     +0x508: eor     v4.8b, v5.8b, v4.8b
     +0x50c: eor     v2.8b, v3.8b, v2.8b
     +0x510: str     d1, [sp, #7016]
     +0x514: ldp     d5, d3, [x19, #168]
     +0x518: str     d2, [sp, #7032]
     +0x51c: ldp     d1, d2, [x19, #216]
     +0x520: eor     v5.8b, v6.8b, v5.8b
     +0x524: eor     v3.8b, v7.8b, v3.8b
     +0x528: str     d4, [sp, #7024]
     +0x52c: ldp     d6, d7, [x19, #184]
     +0x530: ldr     d4, [sp, #7088]
     +0x534: str     d5, [sp, #7040]
     +0x538: eor     v1.8b, v4.8b, v1.8b
     +0x53c: ldr     d4, [sp, #7104]
     +0x540: eor     v6.8b, v16.8b, v6.8b
     +0x544: ldp     d16, d0, [x19, #200]
     +0x548: eor     v7.8b, v17.8b, v7.8b
     +0x54c: ldr     d17, [sp, #7080]
     +0x550: str     d3, [sp, #7048]
     +0x554: ldp     d3, d5, [x19, #232]
     +0x558: str     d1, [sp, #7088]
     +0x55c: eor     v0.8b, v17.8b, v0.8b
     +0x560: ldr     d17, [sp, #7096]
     +0x564: str     d6, [sp, #7056]
     +0x568: ldr     d6, [sp, #7112]
     +0x56c: str     d7, [sp, #7064]
     +0x570: ldr     d7, [sp, #7120]
     +0x574: eor     v2.8b, v17.8b, v2.8b
     +0x578: eor     v3.8b, v4.8b, v3.8b
     +0x57c: ldr     d1, [x19, #264]
     +0x580: str     d0, [sp, #7080]
     +0x584: ldp     d4, d0, [x19, #248]
     +0x588: eor     v5.8b, v6.8b, v5.8b
     +0x58c: ldr     d6, [sp, #7128]
     +0x590: eor     v16.8b, v18.8b, v16.8b
     +0x594: str     d2, [sp, #7096]
     +0x598: ldr     d2, [sp, #7136]
     +0x59c: eor     v4.8b, v7.8b, v4.8b
     +0x5a0: eor     v0.8b, v6.8b, v0.8b
     +0x5a4: str     d3, [sp, #7104]
     +0x5a8: eor     v1.8b, v2.8b, v1.8b
     +0x5ac: str     d16, [sp, #7072]
     +0x5b0: str     d5, [sp, #7112]
     +0x5b4: str     d4, [sp, #7120]
     +0x5b8: str     d0, [sp, #7128]
     +0x5bc: str     d1, [sp, #7136]
     +0x5c0: bl      <mldsa_keccakf1600_permute>
     +0x5c4: ldp     d1, d2, [x19, #272]
     +0x5c8: add     x0, sp, #0x1, lsl #12
     +0x5cc: ldr     d0, [sp, #7008]
     +0x5d0: ldr     d3, [sp, #7016]
     +0x5d4: add     x0, x0, #0xb60
     +0x5d8: ldr     d5, [sp, #7024]
     +0x5dc: ldr     d6, [sp, #7040]
     +0x5e0: ldr     d7, [sp, #7048]
     +0x5e4: eor     v0.8b, v0.8b, v1.8b
     +0x5e8: eor     v1.8b, v3.8b, v2.8b
     +0x5ec: ldr     d3, [sp, #7032]
     +0x5f0: ldp     d4, d2, [x19, #288]
     +0x5f4: ldr     d16, [sp, #7056]
     +0x5f8: ldr     d17, [sp, #7064]
     +0x5fc: ldr     d18, [sp, #7072]
     +0x600: str     d0, [sp, #7008]
     +0x604: eor     v4.8b, v5.8b, v4.8b
     +0x608: eor     v2.8b, v3.8b, v2.8b
     +0x60c: str     d1, [sp, #7016]
     +0x610: ldp     d5, d3, [x19, #304]
     +0x614: str     d2, [sp, #7032]
     +0x618: ldp     d1, d2, [x19, #352]
     +0x61c: eor     v5.8b, v6.8b, v5.8b
     +0x620: eor     v3.8b, v7.8b, v3.8b
     +0x624: str     d4, [sp, #7024]
     +0x628: ldp     d6, d7, [x19, #320]
     +0x62c: ldr     d4, [sp, #7088]
     +0x630: str     d5, [sp, #7040]
     +0x634: eor     v1.8b, v4.8b, v1.8b
     +0x638: ldr     d4, [sp, #7104]
     +0x63c: eor     v6.8b, v16.8b, v6.8b
     +0x640: ldp     d16, d0, [x19, #336]
     +0x644: eor     v7.8b, v17.8b, v7.8b
     +0x648: ldr     d17, [sp, #7080]
     +0x64c: str     d3, [sp, #7048]
     +0x650: ldp     d3, d5, [x19, #368]
     +0x654: str     d1, [sp, #7088]
     +0x658: eor     v0.8b, v17.8b, v0.8b
     +0x65c: ldr     d17, [sp, #7096]
     +0x660: str     d6, [sp, #7056]
     +0x664: ldr     d6, [sp, #7112]
     +0x668: str     d7, [sp, #7064]
     +0x66c: ldr     d7, [sp, #7120]
     +0x670: eor     v2.8b, v17.8b, v2.8b
     +0x674: eor     v3.8b, v4.8b, v3.8b
     +0x678: ldr     d1, [x19, #400]
     +0x67c: str     d0, [sp, #7080]
     +0x680: ldp     d4, d0, [x19, #384]
     +0x684: eor     v5.8b, v6.8b, v5.8b
     +0x688: ldr     d6, [sp, #7128]
     +0x68c: eor     v16.8b, v18.8b, v16.8b
     +0x690: str     d2, [sp, #7096]
     +0x694: ldr     d2, [sp, #7136]
     +0x698: eor     v4.8b, v7.8b, v4.8b
     +0x69c: eor     v0.8b, v6.8b, v0.8b
     +0x6a0: str     d3, [sp, #7104]
     +0x6a4: eor     v1.8b, v2.8b, v1.8b
     +0x6a8: str     d16, [sp, #7072]
     +0x6ac: str     d5, [sp, #7112]
     +0x6b0: str     d4, [sp, #7120]
     +0x6b4: str     d0, [sp, #7128]
     +0x6b8: str     d1, [sp, #7136]
     +0x6bc: bl      <mldsa_keccakf1600_permute>
     +0x6c0: ldp     d1, d2, [x19, #408]
     +0x6c4: add     x0, sp, #0x1, lsl #12
     +0x6c8: ldr     d0, [sp, #7008]
     +0x6cc: ldr     d3, [sp, #7016]
     +0x6d0: add     x0, x0, #0xb60
     +0x6d4: ldr     d5, [sp, #7024]
     +0x6d8: ldr     d6, [sp, #7040]
     +0x6dc: ldr     d7, [sp, #7048]
     +0x6e0: eor     v0.8b, v0.8b, v1.8b
     +0x6e4: eor     v1.8b, v3.8b, v2.8b
     +0x6e8: ldr     d3, [sp, #7032]
     +0x6ec: ldp     d4, d2, [x19, #424]
     +0x6f0: ldr     d16, [sp, #7056]
     +0x6f4: ldr     d17, [sp, #7064]
     +0x6f8: ldr     d18, [sp, #7072]
     +0x6fc: str     d0, [sp, #7008]
     +0x700: eor     v4.8b, v5.8b, v4.8b
     +0x704: eor     v2.8b, v3.8b, v2.8b
     +0x708: str     d1, [sp, #7016]
     +0x70c: ldp     d5, d3, [x19, #440]
     +0x710: str     d2, [sp, #7032]
     +0x714: ldp     d1, d2, [x19, #488]
     +0x718: eor     v5.8b, v6.8b, v5.8b
     +0x71c: eor     v3.8b, v7.8b, v3.8b
     +0x720: str     d4, [sp, #7024]
     +0x724: ldp     d6, d7, [x19, #456]
     +0x728: ldr     d4, [sp, #7088]
     +0x72c: eor     v1.8b, v4.8b, v1.8b
     +0x730: str     d5, [sp, #7040]
     +0x734: ldr     d4, [sp, #7104]
     +0x738: eor     v6.8b, v16.8b, v6.8b
     +0x73c: ldp     d16, d0, [x19, #472]
     +0x740: eor     v7.8b, v17.8b, v7.8b
     +0x744: ldr     d17, [sp, #7080]
     +0x748: str     d3, [sp, #7048]
     +0x74c: ldp     d3, d5, [x19, #504]
     +0x750: str     d1, [sp, #7088]
     +0x754: eor     v0.8b, v17.8b, v0.8b
     +0x758: ldr     d17, [sp, #7096]
     +0x75c: str     d6, [sp, #7056]
     +0x760: ldr     d6, [sp, #7112]
     +0x764: str     d7, [sp, #7064]
     +0x768: ldr     d7, [sp, #7120]
     +0x76c: eor     v2.8b, v17.8b, v2.8b
     +0x770: eor     v3.8b, v4.8b, v3.8b
     +0x774: ldr     d4, [x19, #520]
     +0x778: eor     v5.8b, v6.8b, v5.8b
     +0x77c: str     d0, [sp, #7080]
     +0x780: ldr     d0, [sp, #7128]
     +0x784: ldr     d6, [x19, #528]
     +0x788: ldr     d1, [x19, #536]
     +0x78c: eor     v16.8b, v18.8b, v16.8b
     +0x790: str     d2, [sp, #7096]
     +0x794: ldr     d2, [sp, #7136]
     +0x798: eor     v4.8b, v7.8b, v4.8b
     +0x79c: eor     v0.8b, v0.8b, v6.8b
     +0x7a0: str     d3, [sp, #7104]
     +0x7a4: eor     v1.8b, v2.8b, v1.8b
     +0x7a8: str     d16, [sp, #7072]
     +0x7ac: str     d5, [sp, #7112]
     +0x7b0: str     d4, [sp, #7120]
     +0x7b4: str     d0, [sp, #7128]
     +0x7b8: str     d1, [sp, #7136]
     +0x7bc: bl      <mldsa_keccakf1600_permute>
     +0x7c0: ldr     d0, [x19, #544]
     +0x7c4: ldr     d1, [sp, #7008]
     +0x7c8: add     x0, sp, #0x1, lsl #12
     +0x7cc: ldr     d2, [x19, #552]
     +0x7d0: ldr     d3, [sp, #7016]
     +0x7d4: add     x0, x0, #0xb60
     +0x7d8: eor     v0.8b, v1.8b, v0.8b
     +0x7dc: ldr     d4, [x19, #560]
     +0x7e0: ldr     d5, [sp, #7024]
     +0x7e4: eor     v1.8b, v3.8b, v2.8b
     +0x7e8: ldr     d2, [x19, #568]
     +0x7ec: ldr     d3, [sp, #7032]
     +0x7f0: ldr     d7, [sp, #7048]
     +0x7f4: eor     v4.8b, v5.8b, v4.8b
     +0x7f8: ldr     d5, [x19, #576]
     +0x7fc: eor     v2.8b, v3.8b, v2.8b
     +0x800: ldr     d3, [x19, #584]
     +0x804: ldr     d6, [sp, #7040]
     +0x808: ldr     d17, [sp, #7064]
     +0x80c: ldr     d16, [sp, #7056]
     +0x810: str     d0, [sp, #7008]
     +0x814: eor     v3.8b, v7.8b, v3.8b
     +0x818: ldr     d7, [x19, #600]
     +0x81c: eor     v5.8b, v6.8b, v5.8b
     +0x820: ldr     d6, [x19, #592]
     +0x824: ldr     d0, [sp, #7080]
     +0x828: str     d1, [sp, #7016]
     +0x82c: eor     v7.8b, v17.8b, v7.8b
     +0x830: ldr     d1, [x19, #616]
     +0x834: str     d4, [sp, #7024]
     +0x838: ldr     d4, [x19, #624]
     +0x83c: eor     v6.8b, v16.8b, v6.8b
     +0x840: ldr     d17, [sp, #7088]
     +0x844: eor     v0.8b, v0.8b, v1.8b
     +0x848: str     d2, [sp, #7032]
     +0x84c: ldr     d1, [sp, #7096]
     +0x850: eor     v2.8b, v17.8b, v4.8b
     +0x854: ldr     d4, [x19, #632]
     +0x858: str     d5, [sp, #7040]
     +0x85c: str     d3, [sp, #7048]
     +0x860: ldr     d3, [x19, #640]
     +0x864: ldr     d5, [sp, #7104]
     +0x868: eor     v1.8b, v1.8b, v4.8b
     +0x86c: str     d6, [sp, #7056]
     +0x870: ldr     d4, [sp, #7112]
     +0x874: eor     v3.8b, v5.8b, v3.8b
     +0x878: str     d7, [sp, #7064]
     +0x87c: ldr     d5, [x19, #648]
     +0x880: ldr     d6, [x19, #656]
     +0x884: ldr     d7, [sp, #7120]
     +0x888: ldr     d16, [x19, #608]
     +0x88c: eor     v4.8b, v4.8b, v5.8b
     +0x890: ldr     d18, [sp, #7072]
     +0x894: str     d0, [sp, #7080]
     +0x898: eor     v5.8b, v7.8b, v6.8b
     +0x89c: ldr     d0, [sp, #7128]
     +0x8a0: ldr     d6, [x19, #664]
     +0x8a4: eor     v16.8b, v18.8b, v16.8b
     +0x8a8: str     d2, [sp, #7088]
     +0x8ac: ldr     d2, [sp, #7136]
     +0x8b0: eor     v0.8b, v0.8b, v6.8b
     +0x8b4: str     d1, [sp, #7096]
     +0x8b8: ldr     d1, [x19, #672]
     +0x8bc: str     d3, [sp, #7104]
     +0x8c0: eor     v1.8b, v2.8b, v1.8b
     +0x8c4: str     d16, [sp, #7072]
     +0x8c8: str     d4, [sp, #7112]
     +0x8cc: str     d5, [sp, #7120]
     +0x8d0: str     d0, [sp, #7128]
     +0x8d4: str     d1, [sp, #7136]
     +0x8d8: bl      <mldsa_keccakf1600_permute>
     +0x8dc: ldr     d0, [x19, #680]
     +0x8e0: ldr     d1, [sp, #7008]
     +0x8e4: add     x0, sp, #0x1, lsl #12
     +0x8e8: ldr     d2, [x19, #688]
     +0x8ec: ldr     d3, [sp, #7016]
     +0x8f0: add     x0, x0, #0xb60
     +0x8f4: eor     v0.8b, v1.8b, v0.8b
     +0x8f8: ldr     d4, [x19, #696]
     +0x8fc: ldr     d5, [sp, #7024]
     +0x900: eor     v1.8b, v3.8b, v2.8b
     +0x904: ldr     d2, [x19, #704]
     +0x908: ldr     d3, [sp, #7032]
     +0x90c: ldr     d7, [sp, #7048]
     +0x910: eor     v4.8b, v5.8b, v4.8b
     +0x914: ldr     d5, [x19, #712]
     +0x918: eor     v2.8b, v3.8b, v2.8b
     +0x91c: ldr     d3, [x19, #720]
     +0x920: ldr     d6, [sp, #7040]
     +0x924: ldr     d17, [sp, #7064]
     +0x928: ldr     d16, [sp, #7056]
     +0x92c: str     d0, [sp, #7008]
     +0x930: eor     v3.8b, v7.8b, v3.8b
     +0x934: ldr     d7, [x19, #736]
     +0x938: eor     v5.8b, v6.8b, v5.8b
     +0x93c: ldr     d6, [x19, #728]
     +0x940: ldr     d0, [sp, #7080]
     +0x944: str     d1, [sp, #7016]
     +0x948: eor     v7.8b, v17.8b, v7.8b
     +0x94c: ldr     d1, [x19, #752]
     +0x950: str     d4, [sp, #7024]
     +0x954: ldr     d4, [x19, #760]
     +0x958: eor     v6.8b, v16.8b, v6.8b
     +0x95c: ldr     d17, [sp, #7088]
     +0x960: eor     v0.8b, v0.8b, v1.8b
     +0x964: str     d2, [sp, #7032]
     +0x968: ldr     d1, [sp, #7096]
     +0x96c: eor     v2.8b, v17.8b, v4.8b
     +0x970: ldr     d4, [x19, #768]
     +0x974: str     d5, [sp, #7040]
     +0x978: str     d3, [sp, #7048]
     +0x97c: ldr     d3, [x19, #776]
     +0x980: ldr     d5, [sp, #7104]
     +0x984: eor     v1.8b, v1.8b, v4.8b
     +0x988: str     d6, [sp, #7056]
     +0x98c: ldr     d4, [sp, #7112]
     +0x990: eor     v3.8b, v5.8b, v3.8b
     +0x994: str     d7, [sp, #7064]
     +0x998: ldr     d5, [x19, #784]
     +0x99c: ldr     d6, [x19, #792]
     +0x9a0: ldr     d7, [sp, #7120]
     +0x9a4: ldr     d16, [x19, #744]
     +0x9a8: eor     v4.8b, v4.8b, v5.8b
     +0x9ac: ldr     d18, [sp, #7072]
     +0x9b0: str     d0, [sp, #7080]
     +0x9b4: eor     v5.8b, v7.8b, v6.8b
     +0x9b8: ldr     d0, [sp, #7128]
     +0x9bc: ldr     d6, [x19, #800]
     +0x9c0: eor     v16.8b, v18.8b, v16.8b
     +0x9c4: str     d2, [sp, #7088]
     +0x9c8: ldr     d2, [sp, #7136]
     +0x9cc: eor     v0.8b, v0.8b, v6.8b
     +0x9d0: str     d1, [sp, #7096]
     +0x9d4: ldr     d1, [x19, #808]
     +0x9d8: str     d3, [sp, #7104]
     +0x9dc: eor     v1.8b, v2.8b, v1.8b
     +0x9e0: str     d16, [sp, #7072]
     +0x9e4: str     d4, [sp, #7112]
     +0x9e8: str     d5, [sp, #7120]
     +0x9ec: str     d0, [sp, #7128]
     +0x9f0: str     d1, [sp, #7136]
     +0x9f4: bl      <mldsa_keccakf1600_permute>
     +0x9f8: ldr     d0, [x19, #816]
     +0x9fc: ldr     d1, [sp, #7008]
     +0xa00: add     x0, sp, #0x1, lsl #12
     +0xa04: ldr     d2, [x19, #824]
     +0xa08: ldr     d3, [sp, #7016]
     +0xa0c: add     x0, x0, #0xb60
     +0xa10: eor     v0.8b, v1.8b, v0.8b
     +0xa14: ldr     d4, [x19, #832]
     +0xa18: ldr     d5, [sp, #7024]
     +0xa1c: eor     v1.8b, v3.8b, v2.8b
     +0xa20: ldr     d2, [x19, #840]
     +0xa24: ldr     d3, [sp, #7032]
     +0xa28: ldr     d7, [sp, #7048]
     +0xa2c: eor     v4.8b, v5.8b, v4.8b
     +0xa30: ldr     d5, [x19, #848]
     +0xa34: eor     v2.8b, v3.8b, v2.8b
     +0xa38: ldr     d3, [x19, #856]
     +0xa3c: ldr     d6, [sp, #7040]
     +0xa40: ldr     d17, [sp, #7064]
     +0xa44: ldr     d16, [sp, #7056]
     +0xa48: str     d0, [sp, #7008]
     +0xa4c: eor     v3.8b, v7.8b, v3.8b
     +0xa50: ldr     d7, [x19, #872]
     +0xa54: eor     v5.8b, v6.8b, v5.8b
     +0xa58: ldr     d6, [x19, #864]
     +0xa5c: ldr     d0, [sp, #7080]
     +0xa60: str     d1, [sp, #7016]
     +0xa64: eor     v7.8b, v17.8b, v7.8b
     +0xa68: ldr     d1, [x19, #888]
     +0xa6c: str     d4, [sp, #7024]
     +0xa70: ldr     d4, [x19, #896]
     +0xa74: eor     v6.8b, v16.8b, v6.8b
     +0xa78: ldr     d17, [sp, #7088]
     +0xa7c: eor     v0.8b, v0.8b, v1.8b
     +0xa80: str     d2, [sp, #7032]
     +0xa84: ldr     d1, [sp, #7096]
     +0xa88: eor     v2.8b, v17.8b, v4.8b
     +0xa8c: ldr     d4, [x19, #904]
     +0xa90: str     d5, [sp, #7040]
     +0xa94: str     d3, [sp, #7048]
     +0xa98: ldr     d3, [x19, #912]
     +0xa9c: ldr     d5, [sp, #7104]
     +0xaa0: eor     v1.8b, v1.8b, v4.8b
     +0xaa4: str     d6, [sp, #7056]
     +0xaa8: ldr     d4, [sp, #7112]
     +0xaac: eor     v3.8b, v5.8b, v3.8b
     +0xab0: str     d7, [sp, #7064]
     +0xab4: ldr     d5, [x19, #920]
     +0xab8: ldr     d6, [x19, #928]
     +0xabc: ldr     d7, [sp, #7120]
     +0xac0: ldr     d16, [x19, #880]
     +0xac4: eor     v4.8b, v4.8b, v5.8b
     +0xac8: ldr     d18, [sp, #7072]
     +0xacc: str     d0, [sp, #7080]
     +0xad0: eor     v5.8b, v7.8b, v6.8b
     +0xad4: ldr     d0, [sp, #7128]
     +0xad8: ldr     d6, [x19, #936]
     +0xadc: eor     v16.8b, v18.8b, v16.8b
     +0xae0: str     d2, [sp, #7088]
     +0xae4: ldr     d2, [sp, #7136]
     +0xae8: eor     v0.8b, v0.8b, v6.8b
     +0xaec: str     d1, [sp, #7096]
     +0xaf0: ldr     d1, [x19, #944]
     +0xaf4: str     d3, [sp, #7104]
     +0xaf8: eor     v1.8b, v2.8b, v1.8b
     +0xafc: str     d16, [sp, #7072]
     +0xb00: str     d4, [sp, #7112]
     +0xb04: str     d5, [sp, #7120]
     +0xb08: str     d0, [sp, #7128]
     +0xb0c: str     d1, [sp, #7136]
     +0xb10: bl      <mldsa_keccakf1600_permute>
     +0xb14: ldr     d0, [x19, #952]
     +0xb18: ldr     d1, [sp, #7008]
     +0xb1c: add     x0, sp, #0x1, lsl #12
     +0xb20: ldr     d2, [x19, #960]
     +0xb24: ldr     d3, [sp, #7016]
     +0xb28: add     x0, x0, #0xb60
     +0xb2c: eor     v0.8b, v1.8b, v0.8b
     +0xb30: ldr     d4, [x19, #968]
     +0xb34: ldr     d5, [sp, #7024]
     +0xb38: eor     v1.8b, v3.8b, v2.8b
     +0xb3c: ldr     d2, [x19, #976]
     +0xb40: ldr     d3, [sp, #7032]
     +0xb44: ldr     d7, [sp, #7048]
     +0xb48: eor     v4.8b, v5.8b, v4.8b
     +0xb4c: ldr     d5, [x19, #984]
     +0xb50: eor     v2.8b, v3.8b, v2.8b
     +0xb54: ldr     d3, [x19, #992]
     +0xb58: ldr     d6, [sp, #7040]
     +0xb5c: ldr     d17, [sp, #7064]
     +0xb60: ldr     d16, [sp, #7056]
     +0xb64: str     d0, [sp, #7008]
     +0xb68: eor     v3.8b, v7.8b, v3.8b
     +0xb6c: ldr     d7, [x19, #1008]
     +0xb70: eor     v5.8b, v6.8b, v5.8b
     +0xb74: ldr     d6, [x19, #1000]
     +0xb78: ldr     d0, [sp, #7080]
     +0xb7c: str     d1, [sp, #7016]
     +0xb80: eor     v7.8b, v17.8b, v7.8b
     +0xb84: ldr     d1, [x19, #1024]
     +0xb88: str     d4, [sp, #7024]
     +0xb8c: ldr     d4, [x19, #1032]
     +0xb90: eor     v6.8b, v16.8b, v6.8b
     +0xb94: ldr     d17, [sp, #7088]
     +0xb98: eor     v0.8b, v0.8b, v1.8b
     +0xb9c: str     d2, [sp, #7032]
     +0xba0: ldr     d1, [sp, #7096]
     +0xba4: eor     v2.8b, v17.8b, v4.8b
     +0xba8: ldr     d4, [x19, #1040]
     +0xbac: str     d5, [sp, #7040]
     +0xbb0: str     d3, [sp, #7048]
     +0xbb4: ldr     d3, [x19, #1048]
     +0xbb8: ldr     d5, [sp, #7104]
     +0xbbc: eor     v1.8b, v1.8b, v4.8b
     +0xbc0: str     d6, [sp, #7056]
     +0xbc4: ldr     d4, [sp, #7112]
     +0xbc8: eor     v3.8b, v5.8b, v3.8b
     +0xbcc: str     d7, [sp, #7064]
     +0xbd0: ldr     d5, [x19, #1056]
     +0xbd4: ldr     d6, [x19, #1064]
     +0xbd8: ldr     d7, [sp, #7120]
     +0xbdc: ldr     d16, [x19, #1016]
     +0xbe0: eor     v4.8b, v4.8b, v5.8b
     +0xbe4: ldr     d18, [sp, #7072]
     +0xbe8: str     d0, [sp, #7080]
     +0xbec: eor     v5.8b, v7.8b, v6.8b
     +0xbf0: ldr     d0, [sp, #7128]
     +0xbf4: ldr     d6, [x19, #1072]
     +0xbf8: eor     v16.8b, v18.8b, v16.8b
     +0xbfc: str     d2, [sp, #7088]
     +0xc00: ldr     d2, [sp, #7136]
     +0xc04: eor     v0.8b, v0.8b, v6.8b
     +0xc08: str     d1, [sp, #7096]
     +0xc0c: ldr     d1, [x19, #1080]
     +0xc10: str     d3, [sp, #7104]
     +0xc14: eor     v1.8b, v2.8b, v1.8b
     +0xc18: str     d16, [sp, #7072]
     +0xc1c: str     d4, [sp, #7112]
     +0xc20: str     d5, [sp, #7120]
     +0xc24: str     d0, [sp, #7128]
     +0xc28: str     d1, [sp, #7136]
     +0xc2c: bl      <mldsa_keccakf1600_permute>
     +0xc30: ldr     d0, [x19, #1088]
     +0xc34: ldr     d1, [sp, #7008]
     +0xc38: add     x0, sp, #0x1, lsl #12
     +0xc3c: ldr     d2, [x19, #1096]
     +0xc40: ldr     d3, [sp, #7016]
     +0xc44: add     x0, x0, #0xb60
     +0xc48: eor     v0.8b, v1.8b, v0.8b
     +0xc4c: ldr     d4, [x19, #1104]
     +0xc50: ldr     d5, [sp, #7024]
     +0xc54: eor     v1.8b, v3.8b, v2.8b
     +0xc58: ldr     d2, [x19, #1112]
     +0xc5c: ldr     d3, [sp, #7032]
     +0xc60: ldr     d7, [sp, #7048]
     +0xc64: eor     v4.8b, v5.8b, v4.8b
     +0xc68: ldr     d5, [x19, #1120]
     +0xc6c: eor     v2.8b, v3.8b, v2.8b
     +0xc70: ldr     d3, [x19, #1128]
     +0xc74: ldr     d6, [sp, #7040]
     +0xc78: ldr     d17, [sp, #7064]
     +0xc7c: ldr     d16, [sp, #7056]
     +0xc80: str     d0, [sp, #7008]
     +0xc84: eor     v3.8b, v7.8b, v3.8b
     +0xc88: ldr     d7, [x19, #1144]
     +0xc8c: eor     v5.8b, v6.8b, v5.8b
     +0xc90: ldr     d6, [x19, #1136]
     +0xc94: ldr     d0, [sp, #7080]
     +0xc98: str     d1, [sp, #7016]
     +0xc9c: eor     v7.8b, v17.8b, v7.8b
     +0xca0: ldr     d1, [x19, #1160]
     +0xca4: str     d4, [sp, #7024]
     +0xca8: ldr     d4, [x19, #1168]
     +0xcac: eor     v6.8b, v16.8b, v6.8b
     +0xcb0: ldr     d17, [sp, #7088]
     +0xcb4: eor     v0.8b, v0.8b, v1.8b
     +0xcb8: str     d2, [sp, #7032]
     +0xcbc: ldr     d1, [sp, #7096]
     +0xcc0: eor     v2.8b, v17.8b, v4.8b
     +0xcc4: ldr     d4, [x19, #1176]
     +0xcc8: str     d5, [sp, #7040]
     +0xccc: str     d3, [sp, #7048]
     +0xcd0: ldr     d3, [x19, #1184]
     +0xcd4: ldr     d5, [sp, #7104]
     +0xcd8: eor     v1.8b, v1.8b, v4.8b
     +0xcdc: str     d6, [sp, #7056]
     +0xce0: ldr     d4, [sp, #7112]
     +0xce4: eor     v3.8b, v5.8b, v3.8b
     +0xce8: str     d7, [sp, #7064]
     +0xcec: ldr     d5, [x19, #1192]
     +0xcf0: ldr     d6, [x19, #1200]
     +0xcf4: ldr     d7, [sp, #7120]
     +0xcf8: ldr     d16, [x19, #1152]
     +0xcfc: eor     v4.8b, v4.8b, v5.8b
     +0xd00: ldr     d18, [sp, #7072]
     +0xd04: str     d0, [sp, #7080]
     +0xd08: eor     v5.8b, v7.8b, v6.8b
     +0xd0c: ldr     d0, [sp, #7128]
     +0xd10: ldr     d6, [x19, #1208]
     +0xd14: eor     v16.8b, v18.8b, v16.8b
     +0xd18: str     d2, [sp, #7088]
     +0xd1c: ldr     d2, [sp, #7136]
     +0xd20: eor     v0.8b, v0.8b, v6.8b
     +0xd24: str     d1, [sp, #7096]
     +0xd28: ldr     d1, [x19, #1216]
     +0xd2c: str     d3, [sp, #7104]
     +0xd30: eor     v1.8b, v2.8b, v1.8b
     +0xd34: str     d16, [sp, #7072]
     +0xd38: str     d4, [sp, #7112]
     +0xd3c: str     d5, [sp, #7120]
     +0xd40: str     d0, [sp, #7128]
     +0xd44: str     d1, [sp, #7136]
     +0xd48: bl      <mldsa_keccakf1600_permute>
     +0xd4c: ldr     d0, [x19, #1224]
     +0xd50: ldr     d1, [sp, #7008]
     +0xd54: add     x0, sp, #0x1, lsl #12
     +0xd58: ldr     d2, [x19, #1232]
     +0xd5c: ldr     d3, [sp, #7016]
     +0xd60: add     x0, x0, #0xb60
     +0xd64: ldr     d4, [x19, #1240]
     +0xd68: ldr     d5, [sp, #7024]
     +0xd6c: eor     v0.8b, v1.8b, v0.8b
     +0xd70: eor     v1.8b, v3.8b, v2.8b
     +0xd74: ldr     d2, [x19, #1248]
     +0xd78: ldr     d3, [sp, #7032]
     +0xd7c: eor     v4.8b, v5.8b, v4.8b
     +0xd80: ldr     d5, [x19, #1256]
     +0xd84: ldr     d6, [sp, #7040]
     +0xd88: eor     v2.8b, v3.8b, v2.8b
     +0xd8c: ldr     d3, [x19, #1264]
     +0xd90: ldr     d7, [sp, #7048]
     +0xd94: eor     v5.8b, v6.8b, v5.8b
     +0xd98: str     d0, [sp, #7008]
     +0xd9c: ldrb    w8, [x24, #88]
     +0xda0: eor     v3.8b, v7.8b, v3.8b
     +0xda4: ldr     d0, [sp, #7064]
     +0xda8: str     d1, [sp, #7016]
     +0xdac: ldr     d1, [x19, #1280]
     +0xdb0: str     d4, [sp, #7024]
     +0xdb4: eor     w8, w8, #0x1f
     +0xdb8: str     d2, [sp, #7032]
     +0xdbc: ldr     d2, [x19, #1288]
     +0xdc0: ldr     d4, [sp, #7072]
     +0xdc4: ldr     d6, [x19, #1272]
     +0xdc8: eor     v0.8b, v0.8b, v1.8b
     +0xdcc: ldr     d16, [sp, #7056]
     +0xdd0: ldr     d1, [sp, #7080]
     +0xdd4: eor     v2.8b, v4.8b, v2.8b
     +0xdd8: str     d5, [sp, #7040]
     +0xddc: str     d3, [sp, #7048]
     +0xde0: eor     v6.8b, v16.8b, v6.8b
     +0xde4: ldr     d3, [x19, #1296]
     +0xde8: ldr     d4, [x19, #1304]
     +0xdec: ldr     d5, [sp, #7088]
     +0xdf0: strb    w8, [x24, #88]
     +0xdf4: eor     v1.8b, v1.8b, v3.8b
     +0xdf8: ldrb    w8, [x24, #135]
     +0xdfc: str     d0, [sp, #7064]
     +0xe00: eor     v3.8b, v5.8b, v4.8b
     +0xe04: str     d6, [sp, #7056]
     +0xe08: eor     w8, w8, #0x80
     +0xe0c: str     d2, [sp, #7072]
     +0xe10: strb    w8, [x24, #135]
     +0xe14: mov     w8, #0x88
     +0xe18: eor     w24, w28, w27
     +0xe1c: str     d1, [sp, #7080]
     +0xe20: str     d3, [sp, #7088]
     +0xe24: str     w8, [sp, #7208]
     +0xe28: bl      <mldsa_keccakf1600_permute>
     +0xe2c: ldr     q0, [sp, #7008]
     +0xe30: ldr     q1, [sp, #7024]
     +0xe34: add     x8, sp, #0x1, lsl #12
     +0xe38: ldr     q2, [sp, #7056]
     +0xe3c: add     x8, x8, #0xb60
     +0xe40: orr     w11, w23, w25
     +0xe44: str     q0, [sp, #6848]
     +0xe48: ldr     q0, [sp, #7040]
     +0xe4c: str     q1, [sp, #6864]
     +0xe50: str     q0, [sp, #6880]
     +0xe54: movi    v0.2d, #0x0
     +0xe58: str     q2, [sp, #6896]
     +0xe5c: str     q0, [sp, #7072]
     +0xe60: str     q0, [sp, #7088]
     +0xe64: str     q0, [sp, #7104]
     +0xe68: str     q0, [sp, #7120]
     +0xe6c: str     q0, [sp, #7136]
     +0xe70: str     q0, [sp, #7152]
     +0xe74: str     q0, [sp, #7168]
     +0xe78: str     q0, [sp, #7184]
     +0xe7c: str     q0, [sp, #7200]
     +0xe80: str     q0, [sp, #7008]
     +0xe84: str     q0, [sp, #7024]
     +0xe88: str     q0, [sp, #7040]
     +0xe8c: str     q0, [sp, #7056]
     +0xe90: ldr     q0, [sp, #6912]
     +0xe94: ldr     q1, [sp, #6928]
     +0xe98: ldr     q2, [sp, #6848]
     +0xe9c: ldr     q3, [sp, #6864]
     +0xea0: ldr     q4, [sp, #6944]
     +0xea4: ldr     q5, [sp, #6960]
     +0xea8: ldr     q6, [sp, #6880]
     +0xeac: ldr     q7, [sp, #6896]
     +0xeb0: eor     v0.16b, v2.16b, v0.16b
     +0xeb4: eor     v1.16b, v3.16b, v1.16b
     +0xeb8: eor     v2.16b, v6.16b, v4.16b
     +0xebc: eor     v3.16b, v7.16b, v5.16b
     +0xec0: orr     v4.16b, v2.16b, v0.16b
     +0xec4: orr     v5.16b, v1.16b, v3.16b
     +0xec8: eor     v0.16b, v0.16b, v2.16b
     +0xecc: eor     v1.16b, v3.16b, v1.16b
     +0xed0: orr     v4.16b, v5.16b, v4.16b
     +0xed4: eor     v0.16b, v1.16b, v0.16b
     +0xed8: mov     d2, v4.d[1]
     +0xedc: orr     v1.8b, v4.8b, v2.8b
     +0xee0: mov     d2, v0.d[1]
     +0xee4: fmov    x8, d1
     +0xee8: eor     v0.8b, v0.8b, v2.8b
     +0xeec: orr     x8, x8, x8, lsr #32
     +0xef0: lsr     x9, x8, #16
     +0xef4: orr     w8, w8, w9
     +0xef8: fmov    x9, d0
     +0xefc: orr     w8, w8, w8, lsr #8
     +0xf00: eor     x9, x9, x9, lsr #32
     +0xf04: sub     x8, x21, w8, uxtb
     +0xf08: eor     x9, x9, x9, lsr #16
     +0xf0c: lsr     x8, x8, #32
     +0xf10: lsr     x10, x9, #8
     +0xf14: eor     w9, w9, w10
     +0xf18: orr     w10, w22, w20
     +0xf1c: eor     w8, w8, w9
     +0xf20: and     w9, w9, #0xff
     +0xf24: orr     w10, w10, w11
     +0xf28: eor     w8, w8, w9
     +0xf2c: orr     w9, w10, w26
     +0xf30: orr     w8, w9, w8
     +0xf34: orr     w8, w24, w8
     +0xf38: tst     w8, #0xff
     +0xf3c: b.eq    <mldsa44_pk_from_sk+0xf58>
     +0xf40: mov     x0, x19
     +0xf44: mov     w1, wzr
     +0xf48: mov     w2, #0x520
     +0xf4c: bl      <memset>
     +0xf50: mov     w19, #0xfffffff9
     +0xf54: b       <mldsa44_pk_from_sk+0xf5c>
     +0xf58: mov     w19, wzr
     +0xf5c: add     x0, sp, #0x20
     +0xf60: mov     w1, wzr
     +0xf64: mov     w2, #0x680
     +0xf68: add     x20, sp, #0x20
     +0xf6c: bl      <memset>
     +0xf70: add     x0, sp, #0x6a0
     +0xf74: mov     w1, wzr
     +0xf78: mov     w2, #0x400
     +0xf7c: add     x20, sp, #0x6a0
     +0xf80: bl      <memset>
     +0xf84: add     x0, sp, #0xaa0
     +0xf88: mov     w1, wzr
     +0xf8c: mov     w2, #0x1000
     +0xf90: add     x20, sp, #0xaa0
     +0xf94: bl      <memset>
     +0xf98: movi    v0.2d, #0x0
     +0xf9c: add     x8, sp, #0x1, lsl #12
     +0xfa0: add     x8, x8, #0xaa0
     +0xfa4: str     q0, [sp, #6832]
     +0xfa8: str     q0, [sp, #6816]
     +0xfac: add     x8, sp, #0x1, lsl #12
     +0xfb0: str     q0, [sp, #6896]
     +0xfb4: str     q0, [sp, #6880]
     +0xfb8: add     x8, x8, #0xac0
     +0xfbc: str     q0, [sp, #6864]
     +0xfc0: str     q0, [sp, #6848]
     +0xfc4: add     x8, sp, #0x1, lsl #12
     +0xfc8: str     q0, [sp, #6960]
     +0xfcc: str     q0, [sp, #6944]
     +0xfd0: add     x8, x8, #0xb00
     +0xfd4: str     q0, [sp, #6928]
     +0xfd8: str     q0, [sp, #6912]
     +0xfdc: add     x8, sp, #0x1, lsl #12
     +0xfe0: str     q0, [sp, #6992]
     +0xfe4: add     x8, x8, #0xb40
     +0xfe8: str     q0, [sp, #6976]
     +0xfec: adrp    x8, <page>
     +0xff0: ldr     x8, [x8, #4088]
     +0xff4: ldr     x9, [sp, #7224]
     +0xff8: ldr     x8, [x8]
     +0xffc: cmp     x8, x9
    +0x1000: b.ne    <mldsa44_pk_from_sk+0x104c>
    +0x1004: mov     w0, w19
    +0x1008: mov     sp, x29
    +0x100c: ldp     x20, x19, [sp, #80]
    +0x1010: ldp     x22, x21, [sp, #64]
    +0x1014: ldp     x24, x23, [sp, #48]
    +0x1018: ldp     x26, x25, [sp, #32]
    +0x101c: ldp     x28, x27, [sp, #16]
    +0x1020: ldp     x29, x30, [sp], #96
    +0x1024: mov     x1, #0x0
    +0x1028: mov     x2, #0x0
    +0x102c: mov     x3, #0x0
    +0x1030: mov     x4, #0x0
    +0x1034: mov     x8, #0x0
    +0x1038: mov     x9, #0x0
    +0x103c: mov     x10, #0x0
    +0x1040: mov     x11, #0x0
    +0x1044: mov     x12, #0x0
    +0x1048: ret     
    +0x104c: bl      <__stack_chk_fail>

    memset@plt:
       +0x0: adrp    x16, <page>
       +0x4: ldr     x17, [x16, #4072]
       +0x8: add     x16, x16, #0xfe8
       +0xc: br      x17
 ***)

let MLDSA_NATIVE_PK_FROM_SK_44_CLANG23_O3_MONO_REDUCED_RAM_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
   [layout_range "mldsa44_pk_from_sk";
    layout_range "plt_memset"];;

(* ------------------------------------------------------------------------- *)
(* Correctness, assuming the contracts for memset and memcpy. The secret    *)
(* key at sk is the 2560 bytes skb; if it passes the checks,                 *)
(* mld_pk_from_sk_valid, the public key at pk becomes mld_pk_from_sk_pk and  *)
(* the result is 0, and otherwise the public key is zeroed and the result is *)
(* MLD_ERR_INVALID_KEY (-7 as a 32-bit integer). The expansion of the matrix *)
(* from rho is assumed to terminate. The stack is the 12672 bytes of the     *)
(* function and its callees, 7344 of them for the function.                  *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_PK_FROM_SK_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!mf mc ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev
     ==> !pk sk skb guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          32768 <= val stackpointer /\ val(stackpointer:int64) < 2 EXP 63 /\
          mld_matrix_terminates 4 4 (mld_sk_rho skb) /\
          nonoverlapping (pk,1312) (word_sub stackpointer (word 12672),12672) /\
          ALLPAIRS nonoverlapping
           [(pk,1312); (word_sub stackpointer (word 12672),12672)]
           [(sk,2560); (word pc,libmldsa_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                    read PC s = word (pc + mldsa44_pk_from_sk) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [pk; sk] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    (!j. j < 2560
                         ==> read(memory :> bytes8(word_add sk (word j))) s =
                             skb j))
               (\s. read PC s = returnaddress /\
                    C_RETURN s =
                    (if mld_pk_from_sk_valid 4 4 2 mld_polyeta_unpack_2 96
                          skb
                     then word 0 else word 4294967289) /\
                    (!j. j < 1312
                         ==> read(memory :> bytes8(word_add pk (word j))) s =
                             if mld_pk_from_sk_valid 4 4 2
                                  mld_polyeta_unpack_2 96 skb
                             then mld_pk_from_sk_pk 4 mld_polyeta_unpack_2 96
                                   skb j
                             else word 0))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(pk,1312);
                  memory :> bytes(word_sub stackpointer (word 12672),12672)])`;;

let MLDSA_NATIVE_PK_FROM_SK_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLDSA_NATIVE_PK_FROM_SK_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, rho, the result of the checks,    *)
(* the address of memset and the stack, with all accesses within the         *)
(* arguments, the stack, the GOT entries and the stack guard, the region     *)
(* (ea,el) that memset may read and the constants of the callees, and the    *)
(* writes within the public key and the stack.                               *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_PK_FROM_SK_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT =
  `!mf mc ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev
     ==> exists f_events.
          forall e pk sk skb guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          32768 <= val stackpointer /\ val(stackpointer:int64) < 2 EXP 63 /\
          mld_matrix_terminates 4 4 (mld_sk_rho skb) /\
          nonoverlapping (pk,1312) (word_sub stackpointer (word 12672),12672) /\
          ALLPAIRS nonoverlapping
           [(pk,1312); (word_sub stackpointer (word 12672),12672)]
           [(sk,2560); (word pc,libmldsa_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                    read PC s = word (pc + mldsa44_pk_from_sk) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [pk; sk] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    (!j. j < 2560
                         ==> read(memory :> bytes8(word_add sk (word j))) s =
                             skb j) /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    C_RETURN s =
                    (if mld_pk_from_sk_valid 4 4 2 mld_polyeta_unpack_2 96
                          skb
                     then word 0 else word 4294967289) /\
                    (!j. j < 1312
                         ==> read(memory :> bytes8(word_add pk (word j))) s =
                             if mld_pk_from_sk_valid 4 4 2
                                  mld_polyeta_unpack_2 96 skb
                             then mld_pk_from_sk_pk 4 mld_polyeta_unpack_2 96
                                   skb j
                             else word 0) /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events pk sk (mld_sk_rho skb)
                              (mld_pk_from_sk_valid 4 4 2 mld_polyeta_unpack_2
                                96 skb)
                              guard mf mc pc (word_sub stackpointer (word 12672))
                              returnaddress /\
                       memaccess_inbounds e2
                        [sk,2560; pk,1312;
                         word_sub stackpointer (word 12672),12672;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; word(pc + got_memcpy),8; ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192;
                         word(pc + rodata_mld_zetas),1024;
                         word(pc + mldsa44_pk_from_sk_consts),64;
                         word(pc + mldsa44_polyeta_unpack_consts),128;
                         word(pc + mld_compute_pack_t0_t144_consts),272]
                        [pk,1312; word_sub stackpointer (word 12672),12672]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(pk,1312);
                  memory :> bytes(word_sub stackpointer (word 12672),12672)])`;;

let MLDSA_NATIVE_PK_FROM_SK_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_PK_FROM_SK_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_PK_FROM_SK_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT =
  `!mf mc ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev
     ==> exists f_events.
          forall e pk sk skb guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          32768 <= val stackpointer /\ val(stackpointer:int64) < 2 EXP 63 /\
          mld_matrix_terminates 4 4 (mld_sk_rho skb) /\
          nonoverlapping (pk,1312) (word_sub stackpointer (word 12672),12672) /\
          ALLPAIRS nonoverlapping
           [(pk,1312); (word_sub stackpointer (word 12672),12672)]
           [(sk,2560); (word pc,libmldsa_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                    read PC s = word (pc + mldsa44_pk_from_sk) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [pk; sk] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    (!j. j < 2560
                         ==> read(memory :> bytes8(word_add sk (word j))) s =
                             skb j) /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events pk sk (mld_sk_rho skb)
                              (mld_pk_from_sk_valid 4 4 2 mld_polyeta_unpack_2
                                96 skb)
                              guard mf mc pc (word_sub stackpointer (word 12672))
                              returnaddress /\
                       memaccess_inbounds e2
                        [sk,2560; pk,1312;
                         word_sub stackpointer (word 12672),12672;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; word(pc + got_memcpy),8; ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192;
                         word(pc + rodata_mld_zetas),1024;
                         word(pc + mldsa44_pk_from_sk_consts),64;
                         word(pc + mldsa44_polyeta_unpack_consts),128;
                         word(pc + mld_compute_pack_t0_t144_consts),272]
                        [pk,1312; word_sub stackpointer (word 12672),12672]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(pk,1312);
                  memory :> bytes(word_sub stackpointer (word 12672),12672)])`;;

let MLDSA_NATIVE_PK_FROM_SK_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_PK_FROM_SK_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT;;
