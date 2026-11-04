(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Conversion of a polynomial to a 32-byte message. This is the code for     *)
(* mlkem_poly_tomsg from mlkem-native's portable C implementation compiled   *)
(* by gcc 12 with -O3 (see mlkem_native/README.md). It is verified in the    *)
(* whole image (see libmlkem.ml).                                            *)
(*                                                                           *)
(* The compiler has vectorized the loop, 128 coefficients and 16 bytes per   *)
(* iteration with 32-bit lanes, after a check that the input and the output  *)
(* do not overlap; if they do, the code falls back to a scalar loop. Since   *)
(* the specification requires them not to overlap, only the vector code     *)
(* runs. It saves D8 to D15 in a 64-byte frame on the stack, so unlike those *)
(* of gcc12_O2 the specifications have the stack pointer and this frame. The *)
(* two iterations of the loop are simulated one after the other.             *)
(* ========================================================================= *)

needs "arm/proofs/utils/mlkem_native.ml";;
needs "arm/proofs/utils/mlkem_native_overlap.ml";;
needs "arm/proofs/mlkem_native/gcc12_O3/libmlkem.ml";;

(*** The code in the image:

    mlkem_poly_tomsg:
       +0x0: mov     x2, x0
       +0x4: mov     x0, x1
       +0x8: add     x1, x2, #0x20
       +0xc: add     x6, x0, #0x200
      +0x10: cmp     x0, x1
      +0x14: ccmp    x2, x6, #0x2, cc
      +0x18: b.cc    <mlkem_poly_tomsg+0x3e4>
      +0x1c: adrp    x3, <page>
      +0x20: mov     x1, #0x0
      +0x24: movi    v7.4s, #0x0
      +0x28: stp     d8, d9, [sp, #-64]!
      +0x2c: ldr     q1, [x3, #2384]  // mlkem_poly_tomsg_consts
      +0x30: stp     d10, d11, [sp, #16]
      +0x34: movi    v0.4s, #0x40, lsl #24
      +0x38: stp     d12, d13, [sp, #32]
      +0x3c: stp     d14, d15, [sp, #48]
      +0x40: str     q7, [x2, x1]
      +0x44: ldp     q25, q19, [x0]
      +0x48: ldp     q4, q11, [x0, #32]
      +0x4c: ldp     q20, q18, [x0, #64]
      +0x50: ldp     q6, q16, [x0, #96]
      +0x54: ldp     q23, q12, [x0, #128]
      +0x58: ldp     q5, q10, [x0, #160]
      +0x5c: ldp     q3, q9, [x0, #192]
      +0x60: ldp     q2, q8, [x0, #224]
      +0x64: add     x0, x0, #0x100
      +0x68: uzp2    v15.8h, v6.8h, v16.8h
      +0x6c: uzp2    v28.8h, v25.8h, v19.8h
      +0x70: uzp2    v17.8h, v4.8h, v11.8h
      +0x74: uzp2    v22.8h, v20.8h, v18.8h
      +0x78: uzp2    v13.8h, v2.8h, v8.8h
      +0x7c: uzp2    v27.8h, v23.8h, v12.8h
      +0x80: uzp2    v14.8h, v5.8h, v10.8h
      +0x84: uzp2    v21.8h, v3.8h, v9.8h
      +0x88: uzp1    v4.8h, v4.8h, v11.8h
      +0x8c: uzp1    v26.8h, v22.8h, v15.8h
      +0x90: uzp1    v11.8h, v28.8h, v17.8h
      +0x94: uzp1    v6.8h, v6.8h, v16.8h
      +0x98: uzp1    v5.8h, v5.8h, v10.8h
      +0x9c: uzp1    v2.8h, v2.8h, v8.8h
      +0xa0: uzp1    v10.8h, v27.8h, v14.8h
      +0xa4: uzp1    v24.8h, v21.8h, v13.8h
      +0xa8: uzp1    v25.8h, v25.8h, v19.8h
      +0xac: uzp1    v20.8h, v20.8h, v18.8h
      +0xb0: uzp1    v23.8h, v23.8h, v12.8h
      +0xb4: uzp1    v3.8h, v3.8h, v9.8h
      +0xb8: uzp1    v12.8h, v11.8h, v26.8h
      +0xbc: uzp1    v8.8h, v10.8h, v24.8h
      +0xc0: uzp1    v16.8h, v25.8h, v4.8h
      +0xc4: uzp1    v9.8h, v3.8h, v2.8h
      +0xc8: uzp2    v25.8h, v25.8h, v4.8h
      +0xcc: uzp2    v27.8h, v27.8h, v14.8h
      +0xd0: uzp1    v4.8h, v20.8h, v6.8h
      +0xd4: mov     v14.16b, v0.16b
      +0xd8: uzp2    v20.8h, v20.8h, v6.8h
      +0xdc: uzp1    v6.8h, v23.8h, v5.8h
      +0xe0: uzp2    v23.8h, v23.8h, v5.8h
      +0xe4: sxtl    v5.4s, v12.4h
      +0xe8: uzp2    v3.8h, v3.8h, v2.8h
      +0xec: uzp2    v28.8h, v28.8h, v17.8h
      +0xf0: sxtl2   v2.4s, v8.8h
      +0xf4: sxtl    v17.4s, v8.4h
      +0xf8: mla     v14.4s, v5.4s, v1.4s
      +0xfc: uzp1    v8.8h, v6.8h, v9.8h
     +0x100: mov     v5.16b, v0.16b
     +0x104: uzp2    v6.8h, v6.8h, v9.8h
     +0x108: mov     v9.16b, v0.16b
     +0x10c: uzp1    v31.8h, v25.8h, v20.8h
     +0x110: mla     v5.4s, v2.4s, v1.4s
     +0x114: sxtl    v2.4s, v8.4h
     +0x118: uzp2    v21.8h, v21.8h, v13.8h
     +0x11c: sxtl2   v8.4s, v8.8h
     +0x120: mov     v13.16b, v0.16b
     +0x124: mla     v9.4s, v2.4s, v1.4s
     +0x128: mov     v2.16b, v0.16b
     +0x12c: uzp1    v29.8h, v16.8h, v4.8h
     +0x130: mla     v13.4s, v17.4s, v1.4s
     +0x134: sxtl    v17.4s, v31.4h
     +0x138: mla     v2.4s, v8.4s, v1.4s
     +0x13c: mov     v8.16b, v0.16b
     +0x140: uzp2    v22.8h, v22.8h, v15.8h
     +0x144: sxtl2   v12.4s, v12.8h
     +0x148: uzp1    v15.8h, v23.8h, v3.8h
     +0x14c: sxtl2   v31.4s, v31.8h
     +0x150: mla     v8.4s, v17.4s, v1.4s
     +0x154: mov     v19.16b, v0.16b
     +0x158: mov     v17.16b, v0.16b
     +0x15c: sxtl    v18.4s, v29.4h
     +0x160: uzp2    v16.8h, v16.8h, v4.8h
     +0x164: mla     v19.4s, v12.4s, v1.4s
     +0x168: sxtl    v4.4s, v15.4h
     +0x16c: mla     v17.4s, v31.4s, v1.4s
     +0x170: mov     v12.16b, v0.16b
     +0x174: mov     v31.16b, v0.16b
     +0x178: sxtl2   v29.4s, v29.8h
     +0x17c: ushr    v13.4s, v13.4s, #31
     +0x180: sxtl2   v15.4s, v15.8h
     +0x184: mla     v12.4s, v18.4s, v1.4s
     +0x188: uzp1    v30.8h, v28.8h, v22.8h
     +0x18c: mla     v31.4s, v4.4s, v1.4s
     +0x190: ushr    v5.4s, v5.4s, #31
     +0x194: mov     v18.16b, v0.16b
     +0x198: mov     v4.16b, v0.16b
     +0x19c: uzp2    v26.8h, v11.8h, v26.8h
     +0x1a0: ushr    v14.4s, v14.4s, #31
     +0x1a4: sxtl    v11.4s, v30.4h
     +0x1a8: mla     v18.4s, v29.4s, v1.4s
     +0x1ac: mla     v4.4s, v15.4s, v1.4s
     +0x1b0: uzp1    v29.8h, v27.8h, v21.8h
     +0x1b4: uzp1    v5.8h, v13.8h, v5.8h
     +0x1b8: ushr    v19.4s, v19.4s, #31
     +0x1bc: mov     v13.16b, v0.16b
     +0x1c0: uzp2    v24.8h, v10.8h, v24.8h
     +0x1c4: ushr    v9.4s, v9.4s, #31
     +0x1c8: uzp1    v19.8h, v14.8h, v19.8h
     +0x1cc: sxtl    v10.4s, v29.4h
     +0x1d0: ushr    v8.4s, v8.4s, #31
     +0x1d4: ushr    v17.4s, v17.4s, #31
     +0x1d8: mla     v13.4s, v11.4s, v1.4s
     +0x1dc: sxtl2   v30.4s, v30.8h
     +0x1e0: ushr    v2.4s, v2.4s, #31
     +0x1e4: ushr    v31.4s, v31.4s, #31
     +0x1e8: ushr    v4.4s, v4.4s, #31
     +0x1ec: mov     v11.16b, v0.16b
     +0x1f0: mov     v14.16b, v0.16b
     +0x1f4: sxtl    v15.4s, v16.4h
     +0x1f8: uzp1    v5.16b, v19.16b, v5.16b
     +0x1fc: uzp2    v3.8h, v23.8h, v3.8h
     +0x200: sxtl    v19.4s, v6.4h
     +0x204: ushr    v12.4s, v12.4s, #31
     +0x208: mla     v14.4s, v10.4s, v1.4s
     +0x20c: uzp1    v2.8h, v9.8h, v2.8h
     +0x210: sxtl2   v29.4s, v29.8h
     +0x214: uzp1    v9.8h, v8.8h, v17.8h
     +0x218: ushr    v18.4s, v18.4s, #31
     +0x21c: mla     v11.4s, v30.4s, v1.4s
     +0x220: mov     v10.16b, v0.16b
     +0x224: uzp1    v4.8h, v31.8h, v4.8h
     +0x228: mov     v23.16b, v0.16b
     +0x22c: mov     v8.16b, v0.16b
     +0x230: uzp1    v18.8h, v12.8h, v18.8h
     +0x234: uzp2    v20.8h, v25.8h, v20.8h
     +0x238: uzp1    v4.16b, v9.16b, v4.16b
     +0x23c: mla     v8.4s, v19.4s, v1.4s
     +0x240: sxtl2   v16.4s, v16.8h
     +0x244: sxtl    v19.4s, v26.4h
     +0x248: sxtl2   v6.4s, v6.8h
     +0x24c: ushr    v13.4s, v13.4s, #31
     +0x250: mla     v23.4s, v15.4s, v1.4s
     +0x254: shl     v25.16b, v5.16b, #1
     +0x258: mla     v10.4s, v29.4s, v1.4s
     +0x25c: ushr    v11.4s, v11.4s, #31
     +0x260: mov     v17.16b, v0.16b
     +0x264: mov     v15.16b, v0.16b
     +0x268: sxtl2   v26.4s, v26.8h
     +0x26c: mov     v5.16b, v0.16b
     +0x270: mov     v9.16b, v0.16b
     +0x274: uzp1    v11.8h, v13.8h, v11.8h
     +0x278: ushr    v14.4s, v14.4s, #31
     +0x27c: mla     v17.4s, v16.4s, v1.4s
     +0x280: mla     v15.4s, v6.4s, v1.4s
     +0x284: sxtl    v16.4s, v24.4h
     +0x288: uzp1    v2.16b, v18.16b, v2.16b
     +0x28c: ushr    v13.4s, v8.4s, #31
     +0x290: mla     v5.4s, v19.4s, v1.4s
     +0x294: ushr    v10.4s, v10.4s, #31
     +0x298: sxtl2   v24.4s, v24.8h
     +0x29c: mla     v9.4s, v26.4s, v1.4s
     +0x2a0: mov     v18.16b, v0.16b
     +0x2a4: mov     v8.16b, v0.16b
     +0x2a8: uzp1    v10.8h, v14.8h, v10.8h
     +0x2ac: uzp2    v6.8h, v28.8h, v22.8h
     +0x2b0: ushr    v15.4s, v15.4s, #31
     +0x2b4: mla     v18.4s, v16.4s, v1.4s
     +0x2b8: shl     v19.16b, v4.16b, #2
     +0x2bc: sxtl    v16.4s, v20.4h
     +0x2c0: ushr    v9.4s, v9.4s, #31
     +0x2c4: mla     v8.4s, v24.4s, v1.4s
     +0x2c8: ushr    v5.4s, v5.4s, #31
     +0x2cc: mov     v4.16b, v0.16b
     +0x2d0: sxtl    v14.4s, v3.4h
     +0x2d4: uzp1    v12.16b, v11.16b, v10.16b
     +0x2d8: uzp2    v21.8h, v27.8h, v21.8h
     +0x2dc: sxtl2   v3.4s, v3.8h
     +0x2e0: uzp1    v13.8h, v13.8h, v15.8h
     +0x2e4: ushr    v8.4s, v8.4s, #31
     +0x2e8: mla     v4.4s, v16.4s, v1.4s
     +0x2ec: sxtl    v15.4s, v6.4h
     +0x2f0: uzp1    v5.8h, v5.8h, v9.8h
     +0x2f4: sxtl2   v6.4s, v6.8h
     +0x2f8: ushr    v23.4s, v23.4s, #31
     +0x2fc: ushr    v17.4s, v17.4s, #31
     +0x300: sxtl2   v20.4s, v20.8h
     +0x304: ushr    v18.4s, v18.4s, #31
     +0x308: mov     v11.16b, v0.16b
     +0x30c: mov     v16.16b, v0.16b
     +0x310: mov     v10.16b, v0.16b
     +0x314: mov     v9.16b, v0.16b
     +0x318: uzp1    v18.8h, v18.8h, v8.8h
     +0x31c: mla     v16.4s, v14.4s, v1.4s
     +0x320: mla     v10.4s, v3.4s, v1.4s
     +0x324: sxtl    v14.4s, v21.4h
     +0x328: mla     v9.4s, v6.4s, v1.4s
     +0x32c: orr     v2.16b, v25.16b, v2.16b
     +0x330: uzp1    v17.8h, v23.8h, v17.8h
     +0x334: mla     v11.4s, v20.4s, v1.4s
     +0x338: sxtl2   v21.4s, v21.8h
     +0x33c: mov     v3.16b, v0.16b
     +0x340: mov     v6.16b, v0.16b
     +0x344: mov     v8.16b, v0.16b
     +0x348: orr     v2.16b, v2.16b, v19.16b
     +0x34c: shl     v12.16b, v12.16b, #3
     +0x350: uzp1    v17.16b, v17.16b, v13.16b
     +0x354: ushr    v4.4s, v4.4s, #31
     +0x358: ushr    v11.4s, v11.4s, #31
     +0x35c: ushr    v16.4s, v16.4s, #31
     +0x360: ushr    v10.4s, v10.4s, #31
     +0x364: mla     v3.4s, v15.4s, v1.4s
     +0x368: mla     v6.4s, v14.4s, v1.4s
     +0x36c: mla     v8.4s, v21.4s, v1.4s
     +0x370: orr     v2.16b, v2.16b, v12.16b
     +0x374: shl     v17.16b, v17.16b, #4
     +0x378: uzp1    v5.16b, v5.16b, v18.16b
     +0x37c: uzp1    v4.8h, v4.8h, v11.8h
     +0x380: uzp1    v16.8h, v16.8h, v10.8h
     +0x384: ushr    v3.4s, v3.4s, #31
     +0x388: ushr    v9.4s, v9.4s, #31
     +0x38c: ushr    v6.4s, v6.4s, #31
     +0x390: ushr    v8.4s, v8.4s, #31
     +0x394: orr     v2.16b, v2.16b, v17.16b
     +0x398: shl     v5.16b, v5.16b, #5
     +0x39c: uzp1    v4.16b, v4.16b, v16.16b
     +0x3a0: uzp1    v3.8h, v3.8h, v9.8h
     +0x3a4: uzp1    v6.8h, v6.8h, v8.8h
     +0x3a8: orr     v2.16b, v2.16b, v5.16b
     +0x3ac: shl     v4.16b, v4.16b, #6
     +0x3b0: uzp1    v3.16b, v3.16b, v6.16b
     +0x3b4: orr     v2.16b, v2.16b, v4.16b
     +0x3b8: shl     v3.16b, v3.16b, #7
     +0x3bc: orr     v2.16b, v2.16b, v3.16b
     +0x3c0: str     q2, [x2, x1]
     +0x3c4: cbnz    x1, <mlkem_poly_tomsg+0x3d0>
     +0x3c8: mov     x1, #0x10
     +0x3cc: b       <mlkem_poly_tomsg+0x40>
     +0x3d0: ldp     d10, d11, [sp, #16]
     +0x3d4: ldp     d12, d13, [sp, #32]
     +0x3d8: ldp     d14, d15, [sp, #48]
     +0x3dc: ldp     d8, d9, [sp], #64
     +0x3e0: ret
     +0x3e4: mov     w5, #0xafb8
     +0x3e8: mov     x1, x2
     +0x3ec: movk    w5, #0x13, lsl #16
     +0x3f0: mov     w4, #0x40000000
     +0x3f4: nop
     +0x3f8: strb    wzr, [x1]
     +0x3fc: add     x0, x0, #0x10
     +0x400: ldursh  w2, [x0, #-16]
     +0x404: madd    w2, w2, w5, w4
     +0x408: lsr     w2, w2, #31
     +0x40c: strb    w2, [x1]
     +0x410: ldursh  w3, [x0, #-14]
     +0x414: madd    w3, w3, w5, w4
     +0x418: lsr     w3, w3, #31
     +0x41c: orr     w3, w2, w3, lsl #1
     +0x420: strb    w3, [x1]
     +0x424: ldursh  w2, [x0, #-12]
     +0x428: madd    w2, w2, w5, w4
     +0x42c: lsr     w2, w2, #31
     +0x430: orr     w2, w3, w2, lsl #2
     +0x434: strb    w2, [x1]
     +0x438: ldursh  w3, [x0, #-10]
     +0x43c: madd    w3, w3, w5, w4
     +0x440: lsr     w3, w3, #31
     +0x444: orr     w3, w2, w3, lsl #3
     +0x448: strb    w3, [x1]
     +0x44c: ldursh  w2, [x0, #-8]
     +0x450: madd    w2, w2, w5, w4
     +0x454: lsr     w2, w2, #31
     +0x458: orr     w2, w3, w2, lsl #4
     +0x45c: strb    w2, [x1]
     +0x460: ldursh  w3, [x0, #-6]
     +0x464: madd    w3, w3, w5, w4
     +0x468: lsr     w3, w3, #31
     +0x46c: orr     w3, w2, w3, lsl #5
     +0x470: strb    w3, [x1]
     +0x474: ldursh  w2, [x0, #-4]
     +0x478: madd    w2, w2, w5, w4
     +0x47c: lsr     w2, w2, #31
     +0x480: orr     w2, w3, w2, lsl #6
     +0x484: strb    w2, [x1]
     +0x488: ldursh  w3, [x0, #-2]
     +0x48c: madd    w3, w3, w5, w4
     +0x490: lsr     w3, w3, #31
     +0x494: orr     w2, w2, w3, lsl #7
     +0x498: strb    w2, [x1], #1
     +0x49c: cmp     x0, x6
     +0x4a0: b.ne    <mlkem_poly_tomsg+0x3f8>
     +0x4a4: ret
 ***)

let MLKEM_NATIVE_POLY_TOMSG_GCC12_O3_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O3_mc
   [layout_range "mlkem_poly_tomsg"];;

(*** The vector of 32-bit lanes 1290168 ***)

let MLKEM_NATIVE_POLY_TOMSG_GCC12_O3_CONSTANTS =
  MLKEM_NATIVE_IMAGE_CONST_RULE (layout "mlkem_poly_tomsg_consts") 128;;

(* ------------------------------------------------------------------------- *)
(* The compression of a coefficient to one bit, as computed in a 32-bit lane *)
(* (COMPRESS_D1_ARITH is that of gcc12_O2), and the 32 bytes of the result   *)
(* from the eight bits in each.                                              *)
(* ------------------------------------------------------------------------- *)

let COMPRESS_D1_ARITH = prove
 (`!v. v < 3329
       ==> (1073741824 + v * 1290168) DIV 2147483648 =
           (4 * v + 3329) DIV 6658`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`4 * v + 3329`; `6658`] DIVISION) THEN
  REWRITE_TAC[ARITH_EQ] THEN
  SPEC_TAC(`(4 * v + 3329) MOD 6658`,`r:num`) THEN
  SPEC_TAC(`(4 * v + 3329) DIV 6658`,`q:num`) THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC DIV_UNIQ THEN
  EXISTS_TAC `(1073741824 + v * 1290168) - q * 2147483648` THEN
  ASM_ARITH_TAC);;

let TOMSG_LANE = prove
 (`!y:int16.
        val y < 3329
        ==> word_subword (word_add (word 1073741824)
                                   (word_mul (word_sx y) (word 1290168)):int32)
                         (31,1):1 word =
            word((4 * val y + 3329) DIV 6658)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[WORD_SX_SMALL; ARITH_RULE `y < 3329 ==> y < 32768`] THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_SUBWORD; VAL_WORD_ADD; VAL_WORD_MUL;
              VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_32; DIMINDEX_16;
              DIMINDEX_1] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE `y < 3329 ==> y < 4294967296`;
               ARITH_RULE `y < 3329 ==> y * 1290168 < 4294967296`] THEN
  REWRITE_TAC[ARITH_RULE `4294967296 = 2147483648 * 2`; GSYM DIV_MOD] THEN
  REWRITE_TAC[MOD_MOD_REFL] THEN ASM_SIMP_TAC[COMPRESS_D1_ARITH]);;

let TOMSG_PACK = prove
 (`!r s (c:num->num).
     (!j. j < 32
          ==> read (memory :> bytes8 (word_add r (word j))) s =
              (word_join
                (word_join
                  (word_join (word(c(8 * j + 7)):1 word)
                             (word(c(8 * j + 6)):1 word):2 word)
                  (word_join (word(c(8 * j + 5)):1 word)
                             (word(c(8 * j + 4)):1 word):2 word):4 word)
                (word_join
                  (word_join (word(c(8 * j + 3)):1 word)
                             (word(c(8 * j + 2)):1 word):2 word)
                  (word_join (word(c(8 * j + 1)):1 word)
                             (word(c(8 * j)):1 word):2 word):4 word)):byte)
     ==> read (memory :> bytes(r,32)) s =
         nsum {i | i < 256} (\i. c i MOD 2 * 2 EXP i)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!k. k <= 32
        ==> read (memory :> bytes(r,k)) s =
            nsum {i | i < 8 * k} (\i. (c:num->num) i MOD 2 * 2 EXP i)`
   (MP_TAC o SPEC `32`) THENL
   [ALL_TAC; CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]] THEN
  INDUCT_TAC THENL
   [REWRITE_TAC[MULT_CLAUSES; NSUM_CLAUSES_NUMSEG_LT;
                READ_MEMORY_BYTES_TRIVIAL];
    DISCH_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ANTS_TAC THENL [UNDISCH_TAC `SUC k <= 32` THEN ARITH_TAC; DISCH_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o check (is_forall o concl)) THEN
  ANTS_TAC THENL [UNDISCH_TAC `SUC k <= 32` THEN ARITH_TAC; DISCH_TAC] THEN
  ASM_REWRITE_TAC[ADD1; READ_MEMORY_BYTES_SNOC] THEN
  REWRITE_TAC[ARITH_RULE
   `8 * (k + 1) = SUC(SUC(SUC(SUC(SUC(SUC(SUC(SUC(8 * k))))))))`] THEN
  REWRITE_TAC[NSUM_CLAUSES_NUMSEG_LT] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[ADD1; GSYM ADD_ASSOC] THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
  SIMP_TAC[VAL_WORD_JOIN_SIMPLE; DIMINDEX_1; DIMINDEX_2; DIMINDEX_4;
           DIMINDEX_8; ARITH] THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_1; EXP_ADD] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SPEC_TAC(`nsum {i | i < 8 * k} (\i. (c:num->num) i MOD 2 * 2 EXP i)`,
           `n:num`) THEN
  CONV_TAC NUM_RING);;

(*** The 256 coefficients, merged into the 128-bit parts that the loads
 *** read ***)

let TOMSG_MERGES = map (fun k ->
  let addr = if k = 0 then `a:int64` else
    mk_comb(mk_comb(`word_add:int64->int64->int64`,`a:int64`),
            mk_comb(`word:num->int64`, mk_small_numeral(16 * k))) in
  READ_MEMORY_MERGE_CONV 3
   (vsubst [addr,`x:int64`] `read (memory :> bytes128 x) s0`)) (0--31);;

let TOMSG_INPUT_TAC =
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    is_forall(concl th) && free_in `x:num->int16` (concl th))) THEN
  CONV_TAC(LAND_CONV EXPAND_CASES_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[WORD_ADD_0] THEN STRIP_TAC THEN
  MAP_EVERY MP_TAC TOMSG_MERGES THEN ASM_REWRITE_TAC[] THEN
  REPEAT DISCH_TAC THEN
  DISCARD_MATCHING_ASSUMPTIONS [`read (memory :> bytes16 a) s = x`];;

(*** The restored D registers, as zero extensions of the 64 bits saved ***)

let TOMSG_DREG = prove
 (`!x:int64. word_zx(word_zx x:int128):int64 = x`,
  BITBLAST_TAC);;

(*** The loop branch, on the offset 0 or 16 of the output ***)

let TOMSG_BRANCH_TAC =
  RULE_ASSUM_TAC(fun th ->
    if can (term_match [] `read PC s = if p then x else y`) (concl th)
    then CONV_RULE(RAND_CONV
          (DEPTH_CONV(WORD_RED_CONV ORELSEC NUM_RED_CONV) THENC
           REWRITE_CONV[])) th
    else th);;

let TOMSG_STEPS_TAC k =
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_TOMSG_GCC12_O3_EXEC [k] THEN
  SIMD_SIMPLIFY_TAC[];;

(*** After the simulation, the subwords of the stores taken through AND and
 *** OR to the lanes ***)

let TOMSG_SIMPLIFY_CONV =
  TOP_DEPTH_CONV
   (REWR_CONV WORD_SUBWORD_AND ORELSEC REWR_CONV WORD_SUBWORD_OR ORELSEC
    WORD_SIMPLE_SUBWORD_CONV) THENC
  DEPTH_CONV WORD_NUM_RED_CONV;;

(*** Each stored byte as the bits 31 of the eight lanes for it, found by
 *** bit-blasting with the lanes, multiply-accumulates, as variables ***)

let tomsg_lanepat =
  `word_add (word 1073741824)
            (word_mul (word_shl (word_sx (y:int16)) 0) (word 1290168)):int32`;;

let TOMSG_BYTE_RULE th =
  let v = rand(concl th) in
  let ms = setify(find_terms (can (term_match [] tomsg_lanepat)) v) in
  let idx m = dest_small_numeral(rand(find_term
    (fun t -> is_comb t && rator t = `x:num->int16`) m)) in
  let ims = sort (fun (i,_) (j,_) -> i < j) (map (fun m -> idx m,m) ms) in
  if length ims <> 8 then
    (print_term v; Format.print_newline(); failwith "TOMSG_BYTE_RULE") else
  let gs = map (fun _ -> genvar `:int32`) ims in
  let v' = subst (zip gs (map snd ims)) v in
  let bit g = mk_comb(mk_comb(`word_subword:int32->num#num->1 word`,g),
                      `(31,1)`) in
  let j2 a b = mk_comb(mk_comb(`word_join:1 word->1 word->2 word`,a),b)
  and j4 a b = mk_comb(mk_comb(`word_join:2 word->2 word->4 word`,a),b)
  and j8 a b = mk_comb(mk_comb(`word_join:4 word->4 word->byte`,a),b) in
  let b k = bit(el k gs) in
  let tgt = j8 (j4 (j2 (b 7) (b 6)) (j2 (b 5) (b 4)))
               (j4 (j2 (b 3) (b 2)) (j2 (b 1) (b 0))) in
  let bth = BITBLAST_RULE(mk_eq(v',tgt)) in
  CONV_RULE(RAND_CONV(REWRITE_CONV[WORD_SHL_ZERO]))
   (TRANS th (INST (zip (map snd ims) gs) bth));;

(*** The stored bytes, from the 2 stores of 16 bytes ***)

let TOMSG_STORES_TAC =
  REPEAT(FIRST_X_ASSUM(MP_TAC o CONV_RULE(READ_MEMORY_SPLIT_CONV 4) o
    check (fun th -> can (term_match []
                     `read (memory :> bytes128 a) s = x`) (concl th) &&
                     free_in `r:int64` (concl th)))) THEN
  REPEAT(DISCH_THEN(fun th ->
    MAP_EVERY (ASSUME_TAC o TOMSG_BYTE_RULE o
      CONV_RULE(RAND_CONV TOMSG_SIMPLIFY_CONV) o
      CONV_RULE(LAND_CONV(REWRITE_CONV[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD;
                                       WORD_ADD_0]
                          THENC NUM_REDUCE_CONV)))
     (CONJUNCTS th)));;

(*** The bit of each coefficient, given the bounds ***)

let TOMSG_BITS_TAC =
  DISCH_THEN(fun bth ->
    let lths = map (fun k ->
      let kt = mk_small_numeral k in
      MP (SPEC (mk_comb(`x:num->int16`,kt)) TOMSG_LANE)
         (MP (SPEC kt bth)
             (EQT_ELIM(NUM_LT_CONV(mk_binop `(<):num->num->bool` kt
                                            `256`))))) (0--255) in
    RULE_ASSUM_TAC(REWRITE_RULE lths));;

(* ------------------------------------------------------------------------- *)
(* Correctness proof. As for mlkem_compress 1 in common/fips203.ml, the bit  *)
(* for a coefficient x in [0,3329) is the integer closest to 2 * x / 3329,   *)
(* rounding up on ties, modulo 2, i.e. ((4 * x + 3329) DIV 6658) MOD 2, and  *)
(* as for mlkem_encode 1 the bits are put together little-endian. Like the   *)
(* C code, this relies on the coefficients being in [0,3329).                *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_POLY_TOMSG_GCC12_O3_IMAGE_SUBROUTINE_CORRECT = prove
 (`!r a x pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        ALL (nonoverlapping (r,32)) [(word pc,libmlkem_size); (a,512)] /\
        ALL (nonoverlapping (word_sub stackpointer (word 64),64))
            [(word pc,libmlkem_size); (a,512); (r,32)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O3_mc /\
                  read PC s = word (pc + mlkem_poly_tomsg) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  !i. i < 256
                      ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                          x i)
             (\s. read PC s = returnaddress /\
                  ((!i. i < 256 ==> val(x i) < 3329)
                   ==> read(memory :> bytes(r,32)) s =
                       nsum {i | i < 256}
                            (\i. ((4 * val(x i) + 3329) DIV 6658) MOD 2 *
                                 2 EXP i)))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,32);
                         memory :> bytes(word_sub stackpointer
                                                 (word 64),64)])`,
  MAP_EVERY X_GEN_TAC
   [`r:int64`; `a:int64`; `x:num->int16`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 64 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; ALL] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  MAP_EVERY (fun (n,d) -> ENSURES_PRESERVED_DREG_TAC n d)
   [("d8_init",`D8`); ("d9_init",`D9`); ("d10_init",`D10`);
    ("d11_init",`D11`); ("d12_init",`D12`); ("d13_init",`D13`);
    ("d14_init",`D14`); ("d15_init",`D15`)] THEN
  ENSURES_INIT_TAC "s0" THEN
  TOMSG_INPUT_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o
    MATCH_MP MLKEM_NATIVE_POLY_TOMSG_GCC12_O3_CONSTANTS) THEN

  (*** The overlap check, the setup, the two iterations and the exit ***)

  ARM_STEPS_TAC MLKEM_NATIVE_POLY_TOMSG_GCC12_O3_EXEC (1--7) THEN
  ALIAS_BRANCH_TAC `r:int64` `32` `a:int64` `512` THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_TOMSG_GCC12_O3_EXEC (8--8) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_TOMSG_GCC12_O3_EXEC (9--16) THEN
  MAP_EVERY TOMSG_STEPS_TAC (17--242) THEN TOMSG_BRANCH_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_TOMSG_GCC12_O3_EXEC (243--244) THEN
  MAP_EVERY TOMSG_STEPS_TAC (245--470) THEN TOMSG_BRANCH_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_TOMSG_GCC12_O3_EXEC (471--475) THEN
  TOMSG_STORES_TAC THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[TOMSG_DREG] THEN

  (*** Each byte from the bits of its eight coefficients ***)

  TOMSG_BITS_TAC THEN
  W(fun (_,w) ->
    MP_TAC(ISPECL [`r:int64`; rand(lhand w);
                   `\i. (4 * val((x:num->int16) i) + 3329) DIV 6658`]
                  TOMSG_PACK)) THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN DISCH_THEN MATCH_MP_TAC THEN
  CONV_TAC EXPAND_CASES_CONV THEN
  CONV_TAC(DEPTH_CONV(NUM_MULT_CONV ORELSEC NUM_ADD_CONV)) THEN
  REWRITE_TAC[WORD_ADD_0] THEN ASM_REWRITE_TAC[]);;


(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let MLKEM_NATIVE_POLY_TOMSG_GCC12_O3_IMAGE_SUBROUTINE_SAFE = time prove
 (`exists f_events.
       forall e r a pc stackpointer returnaddress.
           aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
           aligned 16 stackpointer /\
           ALL (nonoverlapping (r,32)) [word pc,libmlkem_size; a,512] /\
           ALL (nonoverlapping (word_sub stackpointer (word 64),64))
               [word pc,libmlkem_size; a,512; r,32]
           ==> ensures arm
               (\s.
                    aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O3_mc /\
                    read PC s = word (pc + mlkem_poly_tomsg) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [r; a] s /\
                    read events s = e)
               (\s.
                    read PC s = returnaddress /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events a r pc (word_sub stackpointer (word 64))
                                       returnaddress /\
                         memaccess_inbounds e2
                          [a,512; r,32;
                           word (pc + mlkem_poly_tomsg_consts),16;
                           word_sub stackpointer (word 64),64]
                          [r,32; word_sub stackpointer (word 64),64]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes (r,32);
                           memory :> bytes(word_sub stackpointer
                                                   (word 64),64)])`,
  CONCRETIZE_F_EVENTS_TAC
    `\(a:int64) (r:int64) (pc:num) (stackpointer:int64) (returnaddress:int64).
      f_ev a r pc stackpointer returnaddress:(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; NONOVERLAPPING_CLAUSES; ALL;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              fst MLKEM_NATIVE_POLY_TOMSG_GCC12_O3_EXEC] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  MAP_EVERY (fun (n,d) -> ENSURES_PRESERVED_DREG_TAC n d)
   [("d8_init",`D8`); ("d9_init",`D9`); ("d10_init",`D10`);
    ("d11_init",`D11`); ("d12_init",`D12`); ("d13_init",`D13`);
    ("d14_init",`D14`); ("d15_init",`D15`)] THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_TOMSG_GCC12_O3_EXEC (1--7) THEN
  ALIAS_BRANCH_TAC `r:int64` `32` `a:int64` `512` THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_TOMSG_GCC12_O3_EXEC (8--8) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_TOMSG_GCC12_O3_EXEC (9--242) THEN
  TOMSG_BRANCH_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_TOMSG_GCC12_O3_EXEC (243--470) THEN
  TOMSG_BRANCH_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_TOMSG_GCC12_O3_EXEC (471--475) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[TOMSG_DREG] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;
