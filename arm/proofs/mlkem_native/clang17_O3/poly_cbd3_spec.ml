(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Centered binomial distribution with eta = 3. This is the code for         *)
(* mlkem_poly_cbd3 from mlkem-native's portable C implementation compiled by *)
(* clang 17 with -O3 (see mlkem_native/README.md). It is verified in the     *)
(* whole image (see libmlkem.ml).                                            *)
(*                                                                           *)
(* The compiler has vectorized the loop completely, 64 coefficients for each *)
(* LD3 and two ST4, after a check that the input and the output do not       *)
(* overlap, with one branch for each of the two orders of the arrays; if     *)
(* they overlap, the code falls back to a loop that handles one group of     *)
(* three bytes at a time. Since the specification requires them not to       *)
(* overlap, only the vector code runs. Unlike that of gcc -O3, it saves no   *)
(* registers on the stack and reads no constants from the read-only data     *)
(* (the mask 0x249249 is made with MOV and MOVK), so as at gcc -O2 the       *)
(* specifications have no stack frame, and the safety theorem has no         *)
(* read-only region. The four copies of the code for 64 coefficients are     *)
(* simulated one after the other.                                            *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mlkem_native.ml";;
needs "arm/proofs/mlkem_native/overlap.ml";;
needs "arm/proofs/mlkem_native/interleave.ml";;
needs "arm/proofs/mlkem_native/clang17_O3/libmlkem.ml";;

(*** The code in the image:

    mlkem_poly_cbd3:
        +0x0: add     x8, x1, #0xc0
        +0x4: cmp     x8, x0
        +0x8: b.ls    join1
        +0xc: add     x8, x0, #0x200
       +0x10: cmp     x8, x1
       +0x14: b.ls    join1
       +0x18: adrp    x10, <page>
       +0x1c: adrp    x11, <page>
       +0x20: mov     w9, #0x9249
       +0x24: movi    v0.2s, #0x7
       +0x28: mov     x8, xzr
       +0x2c: movk    w9, #0x24, lsl #16
       +0x30: ldr     d1, [x10, #1904]
                    // mlkem_poly_cbd3_const1
       +0x34: add     x10, x1, #0x1
       +0x38: ldr     d2, [x11, #1912]
                    // mlkem_poly_cbd3_const2
       +0x3c: ldurh   w11, [x10, #-1]
       +0x40: add     x14, x0, x8
       +0x44: ldrb    w12, [x10, #1]
       +0x48: add     x8, x8, #0x8
       +0x4c: add     x10, x10, #0x3
       +0x50: cmp     x8, #0x200
       +0x54: orr     w11, w11, w12, lsl #16
       +0x58: and     w12, w11, w9
       +0x5c: and     w13, w9, w11, lsr #1
       +0x60: and     w11, w9, w11, lsr #2
       +0x64: add     w12, w13, w12
       +0x68: add     w11, w12, w11
       +0x6c: and     w12, w11, #0x7
       +0x70: ubfx    w13, w11, #3, #3
       +0x74: sub     w12, w12, w13
       +0x78: dup     v3.2s, w11
       +0x7c: strh    w12, [x14]
       +0x80: ubfx    w12, w11, #18, #3
       +0x84: sub     w11, w12, w11, lsr #21
       +0x88: ushl    v4.2s, v3.2s, v1.2s
       +0x8c: ushl    v3.2s, v3.2s, v2.2s
       +0x90: and     v4.8b, v4.8b, v0.8b
       +0x94: and     v3.8b, v3.8b, v0.8b
       +0x98: sub     v3.2s, v4.2s, v3.2s
       +0x9c: strh    w11, [x14, #6]
       +0xa0: mov     w15, v3.s[1]
       +0xa4: fmov    w13, s3
       +0xa8: strh    w13, [x14, #2]
       +0xac: strh    w15, [x14, #4]
       +0xb0: b.ne    loop1
       +0xb4: ret
       +0xb8: mov     x8, x1
       +0xbc: mov     w9, #0x9249
       +0xc0: movk    w9, #0x24, lsl #16
       +0xc4: ld3     {v0.16b-v2.16b}, [x8], #48
       +0xc8: uxtl2   v3.8h, v0.16b
       +0xcc: uxtl2   v7.8h, v1.16b
       +0xd0: uxtl    v5.4s, v3.4h
       +0xd4: uxtl2   v3.4s, v3.8h
       +0xd8: ushll   v17.4s, v7.4h, #8
       +0xdc: ushll2  v7.4s, v7.8h, #8
       +0xe0: uxtl    v4.8h, v0.8b
       +0xe4: uxtl    v16.8h, v1.8b
       +0xe8: orr     v3.16b, v7.16b, v3.16b
       +0xec: uxtl    v7.8h, v2.8b
       +0xf0: uxtl2   v0.8h, v2.16b
       +0xf4: uxtl    v6.4s, v4.4h
       +0xf8: uxtl2   v4.4s, v4.8h
       +0xfc: ushll2  v18.4s, v16.8h, #8
      +0x100: ushll   v16.4s, v16.4h, #8
      +0x104: shll2   v2.4s, v7.8h, #16
      +0x108: shll    v1.4s, v7.4h, #16
      +0x10c: shll    v7.4s, v0.4h, #16
      +0x110: shll2   v0.4s, v0.8h, #16
      +0x114: orr     v4.16b, v18.16b, v4.16b
      +0x118: orr     v6.16b, v16.16b, v6.16b
      +0x11c: orr     v5.16b, v17.16b, v5.16b
      +0x120: orr     v5.16b, v5.16b, v7.16b
      +0x124: orr     v0.16b, v3.16b, v0.16b
      +0x128: orr     v3.16b, v6.16b, v1.16b
      +0x12c: orr     v2.16b, v4.16b, v2.16b
      +0x130: dup     v1.4s, w9
      +0x134: mov     x9, x0
      +0x138: ushr    v17.4s, v5.4s, #1
      +0x13c: ushr    v18.4s, v2.4s, #1
      +0x140: ushr    v19.4s, v0.4s, #1
      +0x144: ushr    v20.4s, v3.4s, #1
      +0x148: and     v4.16b, v2.16b, v1.16b
      +0x14c: ushr    v2.4s, v2.4s, #2
      +0x150: and     v6.16b, v3.16b, v1.16b
      +0x154: and     v7.16b, v0.16b, v1.16b
      +0x158: and     v16.16b, v5.16b, v1.16b
      +0x15c: and     v18.16b, v18.16b, v1.16b
      +0x160: and     v20.16b, v20.16b, v1.16b
      +0x164: and     v19.16b, v19.16b, v1.16b
      +0x168: and     v17.16b, v17.16b, v1.16b
      +0x16c: ushr    v5.4s, v5.4s, #2
      +0x170: ushr    v3.4s, v3.4s, #2
      +0x174: ushr    v0.4s, v0.4s, #2
      +0x178: add     v16.4s, v17.4s, v16.4s
      +0x17c: add     v7.4s, v19.4s, v7.4s
      +0x180: add     v6.4s, v20.4s, v6.4s
      +0x184: add     v4.4s, v18.4s, v4.4s
      +0x188: and     v5.16b, v5.16b, v1.16b
      +0x18c: and     v17.16b, v0.16b, v1.16b
      +0x190: and     v3.16b, v3.16b, v1.16b
      +0x194: and     v0.16b, v2.16b, v1.16b
      +0x198: add     v2.4s, v4.4s, v0.4s
      +0x19c: movi    v0.4s, #0x7
      +0x1a0: add     v4.4s, v6.4s, v3.4s
      +0x1a4: add     v3.4s, v16.4s, v5.4s
      +0x1a8: add     v5.4s, v7.4s, v17.4s
      +0x1ac: ushr    v19.4s, v3.4s, #3
      +0x1b0: ushr    v21.4s, v5.4s, #3
      +0x1b4: ushr    v18.4s, v2.4s, #3
      +0x1b8: and     v6.16b, v3.16b, v0.16b
      +0x1bc: ushr    v20.4s, v4.4s, #3
      +0x1c0: and     v7.16b, v5.16b, v0.16b
      +0x1c4: and     v19.16b, v19.16b, v0.16b
      +0x1c8: and     v21.16b, v21.16b, v0.16b
      +0x1cc: sub     v7.4s, v7.4s, v21.4s
      +0x1d0: sub     v6.4s, v6.4s, v19.4s
      +0x1d4: ushr    v21.4s, v3.4s, #6
      +0x1d8: and     v16.16b, v4.16b, v0.16b
      +0x1dc: ushr    v23.4s, v5.4s, #9
      +0x1e0: and     v17.16b, v2.16b, v0.16b
      +0x1e4: and     v20.16b, v20.16b, v0.16b
      +0x1e8: and     v18.16b, v18.16b, v0.16b
      +0x1ec: sub     v22.4s, v17.4s, v18.4s
      +0x1f0: sub     v20.4s, v16.4s, v20.4s
      +0x1f4: uzp1    v16.8h, v6.8h, v7.8h
      +0x1f8: ushr    v6.4s, v5.4s, #6
      +0x1fc: and     v7.16b, v21.16b, v0.16b
      +0x200: ushr    v21.4s, v3.4s, #9
      +0x204: and     v6.16b, v6.16b, v0.16b
      +0x208: and     v21.16b, v21.16b, v0.16b
      +0x20c: and     v23.16b, v23.16b, v0.16b
      +0x210: sub     v6.4s, v6.4s, v23.4s
      +0x214: ushr    v23.4s, v3.4s, #12
      +0x218: sub     v7.4s, v7.4s, v21.4s
      +0x21c: ushr    v21.4s, v5.4s, #12
      +0x220: ushr    v24.4s, v3.4s, #15
      +0x224: ushr    v25.4s, v5.4s, #15
      +0x228: ushr    v26.4s, v2.4s, #9
      +0x22c: and     v23.16b, v23.16b, v0.16b
      +0x230: and     v21.16b, v21.16b, v0.16b
      +0x234: and     v24.16b, v24.16b, v0.16b
      +0x238: and     v25.16b, v25.16b, v0.16b
      +0x23c: sub     v21.4s, v21.4s, v25.4s
      +0x240: sub     v23.4s, v23.4s, v24.4s
      +0x244: uzp1    v17.8h, v7.8h, v6.8h
      +0x248: ushr    v7.4s, v4.4s, #6
      +0x24c: ushr    v24.4s, v2.4s, #6
      +0x250: ushr    v25.4s, v4.4s, #9
      +0x254: and     v7.16b, v7.16b, v0.16b
      +0x258: ushr    v6.4s, v3.4s, #18
      +0x25c: and     v24.16b, v24.16b, v0.16b
      +0x260: and     v25.16b, v25.16b, v0.16b
      +0x264: and     v26.16b, v26.16b, v0.16b
      +0x268: sub     v24.4s, v24.4s, v26.4s
      +0x26c: sub     v7.4s, v7.4s, v25.4s
      +0x270: uzp1    v18.8h, v23.8h, v21.8h
      +0x274: uzp1    v20.8h, v20.8h, v22.8h
      +0x278: uzp1    v21.8h, v7.8h, v24.8h
      +0x27c: ushr    v7.4s, v2.4s, #12
      +0x280: ushr    v24.4s, v2.4s, #15
      +0x284: ushr    v26.4s, v4.4s, #15
      +0x288: and     v7.16b, v7.16b, v0.16b
      +0x28c: ushr    v25.4s, v5.4s, #18
      +0x290: and     v24.16b, v24.16b, v0.16b
      +0x294: sub     v7.4s, v7.4s, v24.4s
      +0x298: ushr    v24.4s, v4.4s, #12
      +0x29c: and     v26.16b, v26.16b, v0.16b
      +0x2a0: ushr    v5.4s, v5.4s, #21
      +0x2a4: and     v24.16b, v24.16b, v0.16b
      +0x2a8: sub     v24.4s, v24.4s, v26.4s
      +0x2ac: ushr    v26.4s, v2.4s, #18
      +0x2b0: ushr    v2.4s, v2.4s, #21
      +0x2b4: bic     v26.4s, #0x38
      +0x2b8: sub     v2.4s, v26.4s, v2.4s
      +0x2bc: ushr    v26.4s, v4.4s, #18
      +0x2c0: ushr    v4.4s, v4.4s, #21
      +0x2c4: bic     v26.4s, #0x38
      +0x2c8: sub     v4.4s, v26.4s, v4.4s
      +0x2cc: uzp1    v22.8h, v24.8h, v7.8h
      +0x2d0: uzp1    v23.8h, v4.8h, v2.8h
      +0x2d4: ushr    v2.4s, v3.4s, #21
      +0x2d8: bic     v6.4s, #0x38
      +0x2dc: bic     v25.4s, #0x38
      +0x2e0: sub     v3.4s, v25.4s, v5.4s
      +0x2e4: sub     v2.4s, v6.4s, v2.4s
      +0x2e8: st4     {v20.8h-v23.8h}, [x9], #64
      +0x2ec: uzp1    v19.8h, v2.8h, v3.8h
      +0x2f0: st4     {v16.8h-v19.8h}, [x9]
      +0x2f4: add     x9, x1, #0x60
      +0x2f8: ld3     {v2.16b-v4.16b}, [x8]
      +0x2fc: add     x8, x0, #0x80
      +0x300: uxtl2   v5.8h, v2.16b
      +0x304: uxtl2   v17.8h, v3.16b
      +0x308: uxtl    v6.4s, v5.4h
      +0x30c: uxtl2   v5.4s, v5.8h
      +0x310: ushll   v19.4s, v17.4h, #8
      +0x314: ushll2  v17.4s, v17.8h, #8
      +0x318: uxtl    v7.8h, v2.8b
      +0x31c: uxtl    v18.8h, v3.8b
      +0x320: orr     v5.16b, v17.16b, v5.16b
      +0x324: uxtl    v17.8h, v4.8b
      +0x328: uxtl2   v2.8h, v4.16b
      +0x32c: uxtl    v16.4s, v7.4h
      +0x330: uxtl2   v7.4s, v7.8h
      +0x334: ushll2  v20.4s, v18.8h, #8
      +0x338: shll2   v3.4s, v17.8h, #16
      +0x33c: shll    v4.4s, v17.4h, #16
      +0x340: shll    v17.4s, v2.4h, #16
      +0x344: shll2   v2.4s, v2.8h, #16
      +0x348: ushll   v18.4s, v18.4h, #8
      +0x34c: orr     v7.16b, v20.16b, v7.16b
      +0x350: orr     v6.16b, v19.16b, v6.16b
      +0x354: orr     v6.16b, v6.16b, v17.16b
      +0x358: orr     v2.16b, v5.16b, v2.16b
      +0x35c: orr     v3.16b, v7.16b, v3.16b
      +0x360: orr     v16.16b, v18.16b, v16.16b
      +0x364: ushr    v18.4s, v6.4s, #1
      +0x368: ushr    v19.4s, v3.4s, #1
      +0x36c: ushr    v20.4s, v2.4s, #1
      +0x370: orr     v4.16b, v16.16b, v4.16b
      +0x374: and     v5.16b, v3.16b, v1.16b
      +0x378: and     v16.16b, v2.16b, v1.16b
      +0x37c: and     v17.16b, v6.16b, v1.16b
      +0x380: ushr    v21.4s, v4.4s, #1
      +0x384: and     v19.16b, v19.16b, v1.16b
      +0x388: ushr    v3.4s, v3.4s, #2
      +0x38c: and     v20.16b, v20.16b, v1.16b
      +0x390: and     v18.16b, v18.16b, v1.16b
      +0x394: ushr    v6.4s, v6.4s, #2
      +0x398: ushr    v2.4s, v2.4s, #2
      +0x39c: and     v7.16b, v4.16b, v1.16b
      +0x3a0: ushr    v4.4s, v4.4s, #2
      +0x3a4: add     v17.4s, v18.4s, v17.4s
      +0x3a8: add     v16.4s, v20.4s, v16.4s
      +0x3ac: add     v5.4s, v19.4s, v5.4s
      +0x3b0: and     v21.16b, v21.16b, v1.16b
      +0x3b4: and     v6.16b, v6.16b, v1.16b
      +0x3b8: and     v18.16b, v2.16b, v1.16b
      +0x3bc: and     v3.16b, v3.16b, v1.16b
      +0x3c0: add     v7.4s, v21.4s, v7.4s
      +0x3c4: and     v2.16b, v4.16b, v1.16b
      +0x3c8: add     v5.4s, v5.4s, v3.4s
      +0x3cc: add     v4.4s, v17.4s, v6.4s
      +0x3d0: add     v3.4s, v16.4s, v18.4s
      +0x3d4: add     v2.4s, v7.4s, v2.4s
      +0x3d8: ushr    v19.4s, v4.4s, #3
      +0x3dc: ushr    v21.4s, v3.4s, #3
      +0x3e0: ushr    v18.4s, v5.4s, #3
      +0x3e4: and     v6.16b, v4.16b, v0.16b
      +0x3e8: ushr    v20.4s, v2.4s, #3
      +0x3ec: and     v7.16b, v3.16b, v0.16b
      +0x3f0: and     v19.16b, v19.16b, v0.16b
      +0x3f4: and     v21.16b, v21.16b, v0.16b
      +0x3f8: sub     v7.4s, v7.4s, v21.4s
      +0x3fc: sub     v6.4s, v6.4s, v19.4s
      +0x400: ushr    v21.4s, v4.4s, #6
      +0x404: and     v16.16b, v2.16b, v0.16b
      +0x408: ushr    v23.4s, v3.4s, #9
      +0x40c: and     v17.16b, v5.16b, v0.16b
      +0x410: and     v20.16b, v20.16b, v0.16b
      +0x414: and     v18.16b, v18.16b, v0.16b
      +0x418: sub     v22.4s, v17.4s, v18.4s
      +0x41c: sub     v20.4s, v16.4s, v20.4s
      +0x420: uzp1    v16.8h, v6.8h, v7.8h
      +0x424: ushr    v6.4s, v3.4s, #6
      +0x428: and     v7.16b, v21.16b, v0.16b
      +0x42c: ushr    v21.4s, v4.4s, #9
      +0x430: and     v6.16b, v6.16b, v0.16b
      +0x434: and     v21.16b, v21.16b, v0.16b
      +0x438: and     v23.16b, v23.16b, v0.16b
      +0x43c: sub     v6.4s, v6.4s, v23.4s
      +0x440: sub     v7.4s, v7.4s, v21.4s
      +0x444: ushr    v21.4s, v4.4s, #15
      +0x448: uzp1    v17.8h, v7.8h, v6.8h
      +0x44c: ushr    v6.4s, v4.4s, #12
      +0x450: ushr    v7.4s, v3.4s, #12
      +0x454: ushr    v23.4s, v3.4s, #15
      +0x458: ushr    v24.4s, v2.4s, #9
      +0x45c: and     v6.16b, v6.16b, v0.16b
      +0x460: ushr    v25.4s, v5.4s, #9
      +0x464: and     v7.16b, v7.16b, v0.16b
      +0x468: and     v21.16b, v21.16b, v0.16b
      +0x46c: and     v23.16b, v23.16b, v0.16b
      +0x470: sub     v7.4s, v7.4s, v23.4s
      +0x474: sub     v6.4s, v6.4s, v21.4s
      +0x478: ushr    v21.4s, v2.4s, #6
      +0x47c: ushr    v23.4s, v5.4s, #6
      +0x480: and     v21.16b, v21.16b, v0.16b
      +0x484: and     v23.16b, v23.16b, v0.16b
      +0x488: and     v24.16b, v24.16b, v0.16b
      +0x48c: and     v25.16b, v25.16b, v0.16b
      +0x490: sub     v23.4s, v23.4s, v25.4s
      +0x494: sub     v21.4s, v21.4s, v24.4s
      +0x498: uzp1    v24.8h, v20.8h, v22.8h
      +0x49c: ushr    v20.4s, v5.4s, #12
      +0x4a0: ushr    v22.4s, v5.4s, #15
      +0x4a4: and     v20.16b, v20.16b, v0.16b
      +0x4a8: and     v22.16b, v22.16b, v0.16b
      +0x4ac: uzp1    v25.8h, v21.8h, v23.8h
      +0x4b0: ushr    v21.4s, v2.4s, #12
      +0x4b4: sub     v20.4s, v20.4s, v22.4s
      +0x4b8: ushr    v22.4s, v2.4s, #15
      +0x4bc: and     v21.16b, v21.16b, v0.16b
      +0x4c0: and     v22.16b, v22.16b, v0.16b
      +0x4c4: sub     v21.4s, v21.4s, v22.4s
      +0x4c8: ushr    v22.4s, v4.4s, #18
      +0x4cc: uzp1    v26.8h, v21.8h, v20.8h
      +0x4d0: ushr    v21.4s, v5.4s, #18
      +0x4d4: ushr    v5.4s, v5.4s, #21
      +0x4d8: bic     v21.4s, #0x38
      +0x4dc: ushr    v20.4s, v3.4s, #18
      +0x4e0: sub     v5.4s, v21.4s, v5.4s
      +0x4e4: ushr    v21.4s, v2.4s, #18
      +0x4e8: ushr    v2.4s, v2.4s, #21
      +0x4ec: ushr    v4.4s, v4.4s, #21
      +0x4f0: bic     v21.4s, #0x38
      +0x4f4: ushr    v3.4s, v3.4s, #21
      +0x4f8: sub     v2.4s, v21.4s, v2.4s
      +0x4fc: bic     v22.4s, #0x38
      +0x500: bic     v20.4s, #0x38
      +0x504: uzp1    v27.8h, v2.8h, v5.8h
      +0x508: sub     v2.4s, v20.4s, v3.4s
      +0x50c: sub     v3.4s, v22.4s, v4.4s
      +0x510: uzp1    v18.8h, v6.8h, v7.8h
      +0x514: uzp1    v19.8h, v3.8h, v2.8h
      +0x518: st4     {v24.8h-v27.8h}, [x8]
      +0x51c: add     x8, x0, #0xc0
      +0x520: st4     {v16.8h-v19.8h}, [x8]
      +0x524: add     x8, x0, #0x100
      +0x528: ld3     {v2.16b-v4.16b}, [x9]
      +0x52c: add     x9, x1, #0x90
      +0x530: uxtl2   v5.8h, v2.16b
      +0x534: uxtl2   v17.8h, v3.16b
      +0x538: uxtl    v6.4s, v5.4h
      +0x53c: uxtl2   v5.4s, v5.8h
      +0x540: ushll   v19.4s, v17.4h, #8
      +0x544: ushll2  v17.4s, v17.8h, #8
      +0x548: uxtl    v7.8h, v2.8b
      +0x54c: uxtl    v18.8h, v3.8b
      +0x550: orr     v5.16b, v17.16b, v5.16b
      +0x554: uxtl    v17.8h, v4.8b
      +0x558: uxtl2   v2.8h, v4.16b
      +0x55c: uxtl    v16.4s, v7.4h
      +0x560: uxtl2   v7.4s, v7.8h
      +0x564: ushll2  v20.4s, v18.8h, #8
      +0x568: ushll   v18.4s, v18.4h, #8
      +0x56c: shll2   v3.4s, v17.8h, #16
      +0x570: shll    v4.4s, v17.4h, #16
      +0x574: shll    v17.4s, v2.4h, #16
      +0x578: shll2   v2.4s, v2.8h, #16
      +0x57c: orr     v7.16b, v20.16b, v7.16b
      +0x580: orr     v16.16b, v18.16b, v16.16b
      +0x584: orr     v6.16b, v19.16b, v6.16b
      +0x588: orr     v6.16b, v6.16b, v17.16b
      +0x58c: orr     v2.16b, v5.16b, v2.16b
      +0x590: orr     v4.16b, v16.16b, v4.16b
      +0x594: orr     v3.16b, v7.16b, v3.16b
      +0x598: ushr    v18.4s, v6.4s, #1
      +0x59c: ushr    v19.4s, v3.4s, #1
      +0x5a0: ushr    v20.4s, v2.4s, #1
      +0x5a4: ushr    v21.4s, v4.4s, #1
      +0x5a8: and     v5.16b, v3.16b, v1.16b
      +0x5ac: ushr    v3.4s, v3.4s, #2
      +0x5b0: and     v7.16b, v4.16b, v1.16b
      +0x5b4: and     v16.16b, v2.16b, v1.16b
      +0x5b8: and     v17.16b, v6.16b, v1.16b
      +0x5bc: and     v19.16b, v19.16b, v1.16b
      +0x5c0: and     v21.16b, v21.16b, v1.16b
      +0x5c4: and     v20.16b, v20.16b, v1.16b
      +0x5c8: and     v18.16b, v18.16b, v1.16b
      +0x5cc: ushr    v6.4s, v6.4s, #2
      +0x5d0: ushr    v4.4s, v4.4s, #2
      +0x5d4: ushr    v2.4s, v2.4s, #2
      +0x5d8: add     v17.4s, v18.4s, v17.4s
      +0x5dc: add     v16.4s, v20.4s, v16.4s
      +0x5e0: add     v7.4s, v21.4s, v7.4s
      +0x5e4: add     v5.4s, v19.4s, v5.4s
      +0x5e8: and     v6.16b, v6.16b, v1.16b
      +0x5ec: and     v18.16b, v2.16b, v1.16b
      +0x5f0: and     v2.16b, v4.16b, v1.16b
      +0x5f4: and     v3.16b, v3.16b, v1.16b
      +0x5f8: add     v5.4s, v5.4s, v3.4s
      +0x5fc: add     v4.4s, v7.4s, v2.4s
      +0x600: add     v2.4s, v17.4s, v6.4s
      +0x604: add     v3.4s, v16.4s, v18.4s
      +0x608: ushr    v19.4s, v2.4s, #3
      +0x60c: ushr    v21.4s, v3.4s, #3
      +0x610: ushr    v18.4s, v5.4s, #3
      +0x614: and     v6.16b, v2.16b, v0.16b
      +0x618: ushr    v20.4s, v4.4s, #3
      +0x61c: and     v7.16b, v3.16b, v0.16b
      +0x620: and     v19.16b, v19.16b, v0.16b
      +0x624: and     v21.16b, v21.16b, v0.16b
      +0x628: sub     v7.4s, v7.4s, v21.4s
      +0x62c: sub     v6.4s, v6.4s, v19.4s
      +0x630: and     v16.16b, v4.16b, v0.16b
      +0x634: and     v17.16b, v5.16b, v0.16b
      +0x638: and     v20.16b, v20.16b, v0.16b
      +0x63c: and     v18.16b, v18.16b, v0.16b
      +0x640: sub     v22.4s, v17.4s, v18.4s
      +0x644: sub     v20.4s, v16.4s, v20.4s
      +0x648: uzp1    v16.8h, v6.8h, v7.8h
      +0x64c: ushr    v6.4s, v2.4s, #6
      +0x650: ushr    v7.4s, v3.4s, #6
      +0x654: ushr    v21.4s, v2.4s, #9
      +0x658: ushr    v23.4s, v3.4s, #9
      +0x65c: ushr    v24.4s, v5.4s, #6
      +0x660: ushr    v26.4s, v5.4s, #9
      +0x664: ushr    v25.4s, v4.4s, #6
      +0x668: and     v6.16b, v6.16b, v0.16b
      +0x66c: and     v7.16b, v7.16b, v0.16b
      +0x670: and     v21.16b, v21.16b, v0.16b
      +0x674: and     v23.16b, v23.16b, v0.16b
      +0x678: sub     v7.4s, v7.4s, v23.4s
      +0x67c: sub     v6.4s, v6.4s, v21.4s
      +0x680: ushr    v21.4s, v2.4s, #12
      +0x684: and     v24.16b, v24.16b, v0.16b
      +0x688: ushr    v23.4s, v3.4s, #15
      +0x68c: and     v26.16b, v26.16b, v0.16b
      +0x690: sub     v24.4s, v24.4s, v26.4s
      +0x694: ushr    v26.4s, v4.4s, #9
      +0x698: uzp1    v17.8h, v6.8h, v7.8h
      +0x69c: ushr    v6.4s, v3.4s, #12
      +0x6a0: and     v7.16b, v21.16b, v0.16b
      +0x6a4: ushr    v21.4s, v2.4s, #15
      +0x6a8: and     v25.16b, v25.16b, v0.16b
      +0x6ac: and     v26.16b, v26.16b, v0.16b
      +0x6b0: and     v6.16b, v6.16b, v0.16b
      +0x6b4: and     v21.16b, v21.16b, v0.16b
      +0x6b8: and     v23.16b, v23.16b, v0.16b
      +0x6bc: sub     v25.4s, v25.4s, v26.4s
      +0x6c0: sub     v6.4s, v6.4s, v23.4s
      +0x6c4: sub     v7.4s, v7.4s, v21.4s
      +0x6c8: uzp1    v20.8h, v20.8h, v22.8h
      +0x6cc: ushr    v26.4s, v5.4s, #12
      +0x6d0: uzp1    v21.8h, v25.8h, v24.8h
      +0x6d4: ushr    v24.4s, v5.4s, #15
      +0x6d8: and     v25.16b, v26.16b, v0.16b
      +0x6dc: and     v24.16b, v24.16b, v0.16b
      +0x6e0: ushr    v26.4s, v4.4s, #12
      +0x6e4: sub     v24.4s, v25.4s, v24.4s
      +0x6e8: ushr    v25.4s, v4.4s, #15
      +0x6ec: and     v26.16b, v26.16b, v0.16b
      +0x6f0: and     v25.16b, v25.16b, v0.16b
      +0x6f4: sub     v25.4s, v26.4s, v25.4s
      +0x6f8: uzp1    v18.8h, v7.8h, v6.8h
      +0x6fc: uzp1    v22.8h, v25.8h, v24.8h
      +0x700: ushr    v24.4s, v5.4s, #18
      +0x704: ushr    v25.4s, v4.4s, #18
      +0x708: ushr    v5.4s, v5.4s, #21
      +0x70c: ushr    v4.4s, v4.4s, #21
      +0x710: bic     v24.4s, #0x38
      +0x714: bic     v25.4s, #0x38
      +0x718: sub     v5.4s, v24.4s, v5.4s
      +0x71c: sub     v4.4s, v25.4s, v4.4s
      +0x720: ushr    v24.4s, v2.4s, #18
      +0x724: uzp1    v23.8h, v4.8h, v5.8h
      +0x728: ushr    v4.4s, v3.4s, #18
      +0x72c: ushr    v3.4s, v3.4s, #21
      +0x730: ushr    v2.4s, v2.4s, #21
      +0x734: bic     v24.4s, #0x38
      +0x738: bic     v4.4s, #0x38
      +0x73c: st4     {v20.8h-v23.8h}, [x8]
      +0x740: sub     v3.4s, v4.4s, v3.4s
      +0x744: add     x8, x0, #0x140
      +0x748: sub     v2.4s, v24.4s, v2.4s
      +0x74c: uzp1    v19.8h, v2.8h, v3.8h
      +0x750: st4     {v16.8h-v19.8h}, [x8]
      +0x754: add     x8, x0, #0x180
      +0x758: ld3     {v2.16b-v4.16b}, [x9]
      +0x75c: uxtl2   v5.8h, v2.16b
      +0x760: uxtl2   v17.8h, v3.16b
      +0x764: uxtl    v6.4s, v5.4h
      +0x768: uxtl2   v5.4s, v5.8h
      +0x76c: ushll   v19.4s, v17.4h, #8
      +0x770: ushll2  v17.4s, v17.8h, #8
      +0x774: uxtl    v7.8h, v2.8b
      +0x778: uxtl    v18.8h, v3.8b
      +0x77c: orr     v5.16b, v17.16b, v5.16b
      +0x780: uxtl    v17.8h, v4.8b
      +0x784: uxtl2   v2.8h, v4.16b
      +0x788: uxtl    v16.4s, v7.4h
      +0x78c: uxtl2   v7.4s, v7.8h
      +0x790: ushll2  v20.4s, v18.8h, #8
      +0x794: ushll   v18.4s, v18.4h, #8
      +0x798: shll2   v3.4s, v17.8h, #16
      +0x79c: shll    v4.4s, v17.4h, #16
      +0x7a0: shll    v17.4s, v2.4h, #16
      +0x7a4: orr     v7.16b, v20.16b, v7.16b
      +0x7a8: orr     v16.16b, v18.16b, v16.16b
      +0x7ac: orr     v6.16b, v19.16b, v6.16b
      +0x7b0: shll2   v2.4s, v2.8h, #16
      +0x7b4: orr     v6.16b, v6.16b, v17.16b
      +0x7b8: orr     v4.16b, v16.16b, v4.16b
      +0x7bc: orr     v3.16b, v7.16b, v3.16b
      +0x7c0: ushr    v18.4s, v6.4s, #1
      +0x7c4: ushr    v19.4s, v3.4s, #1
      +0x7c8: ushr    v21.4s, v4.4s, #1
      +0x7cc: orr     v2.16b, v5.16b, v2.16b
      +0x7d0: and     v5.16b, v3.16b, v1.16b
      +0x7d4: and     v7.16b, v4.16b, v1.16b
      +0x7d8: and     v16.16b, v2.16b, v1.16b
      +0x7dc: and     v17.16b, v6.16b, v1.16b
      +0x7e0: ushr    v20.4s, v2.4s, #1
      +0x7e4: and     v19.16b, v19.16b, v1.16b
      +0x7e8: ushr    v3.4s, v3.4s, #2
      +0x7ec: and     v21.16b, v21.16b, v1.16b
      +0x7f0: and     v18.16b, v18.16b, v1.16b
      +0x7f4: ushr    v6.4s, v6.4s, #2
      +0x7f8: ushr    v4.4s, v4.4s, #2
      +0x7fc: ushr    v2.4s, v2.4s, #2
      +0x800: add     v17.4s, v18.4s, v17.4s
      +0x804: add     v7.4s, v21.4s, v7.4s
      +0x808: add     v5.4s, v19.4s, v5.4s
      +0x80c: and     v20.16b, v20.16b, v1.16b
      +0x810: and     v6.16b, v6.16b, v1.16b
      +0x814: and     v18.16b, v2.16b, v1.16b
      +0x818: and     v2.16b, v4.16b, v1.16b
      +0x81c: and     v1.16b, v3.16b, v1.16b
      +0x820: add     v16.4s, v20.4s, v16.4s
      +0x824: add     v4.4s, v5.4s, v1.4s
      +0x828: add     v3.4s, v7.4s, v2.4s
      +0x82c: add     v2.4s, v17.4s, v6.4s
      +0x830: add     v1.4s, v16.4s, v18.4s
      +0x834: ushr    v17.4s, v4.4s, #3
      +0x838: ushr    v18.4s, v2.4s, #3
      +0x83c: ushr    v19.4s, v3.4s, #3
      +0x840: and     v5.16b, v2.16b, v0.16b
      +0x844: ushr    v20.4s, v1.4s, #3
      +0x848: and     v7.16b, v3.16b, v0.16b
      +0x84c: and     v16.16b, v4.16b, v0.16b
      +0x850: and     v18.16b, v18.16b, v0.16b
      +0x854: and     v19.16b, v19.16b, v0.16b
      +0x858: and     v17.16b, v17.16b, v0.16b
      +0x85c: sub     v21.4s, v16.4s, v17.4s
      +0x860: sub     v7.4s, v7.4s, v19.4s
      +0x864: ushr    v16.4s, v2.4s, #6
      +0x868: sub     v5.4s, v5.4s, v18.4s
      +0x86c: ushr    v17.4s, v1.4s, #6
      +0x870: ushr    v18.4s, v2.4s, #9
      +0x874: ushr    v19.4s, v1.4s, #9
      +0x878: ushr    v24.4s, v4.4s, #9
      +0x87c: and     v6.16b, v1.16b, v0.16b
      +0x880: and     v20.16b, v20.16b, v0.16b
      +0x884: sub     v6.4s, v6.4s, v20.4s
      +0x888: and     v16.16b, v16.16b, v0.16b
      +0x88c: and     v17.16b, v17.16b, v0.16b
      +0x890: and     v18.16b, v18.16b, v0.16b
      +0x894: and     v19.16b, v19.16b, v0.16b
      +0x898: sub     v20.4s, v17.4s, v19.4s
      +0x89c: sub     v22.4s, v16.4s, v18.4s
      +0x8a0: uzp1    v16.8h, v5.8h, v6.8h
      +0x8a4: uzp1    v17.8h, v22.8h, v20.8h
      +0x8a8: uzp1    v20.8h, v7.8h, v21.8h
      +0x8ac: ushr    v5.4s, v3.4s, #6
      +0x8b0: ushr    v6.4s, v4.4s, #6
      +0x8b4: ushr    v7.4s, v3.4s, #9
      +0x8b8: and     v5.16b, v5.16b, v0.16b
      +0x8bc: and     v6.16b, v6.16b, v0.16b
      +0x8c0: and     v7.16b, v7.16b, v0.16b
      +0x8c4: and     v24.16b, v24.16b, v0.16b
      +0x8c8: sub     v6.4s, v6.4s, v24.4s
      +0x8cc: sub     v5.4s, v5.4s, v7.4s
      +0x8d0: ushr    v7.4s, v3.4s, #12
      +0x8d4: uzp1    v21.8h, v5.8h, v6.8h
      +0x8d8: ushr    v5.4s, v4.4s, #12
      +0x8dc: and     v6.16b, v7.16b, v0.16b
      +0x8e0: ushr    v7.4s, v3.4s, #15
      +0x8e4: ushr    v24.4s, v4.4s, #15
      +0x8e8: and     v5.16b, v5.16b, v0.16b
      +0x8ec: and     v7.16b, v7.16b, v0.16b
      +0x8f0: and     v24.16b, v24.16b, v0.16b
      +0x8f4: sub     v5.4s, v5.4s, v24.4s
      +0x8f8: sub     v6.4s, v6.4s, v7.4s
      +0x8fc: ushr    v7.4s, v1.4s, #12
      +0x900: uzp1    v22.8h, v6.8h, v5.8h
      +0x904: ushr    v5.4s, v4.4s, #18
      +0x908: ushr    v4.4s, v4.4s, #21
      +0x90c: bic     v5.4s, #0x38
      +0x910: ushr    v24.4s, v2.4s, #12
      +0x914: sub     v4.4s, v5.4s, v4.4s
      +0x918: ushr    v5.4s, v3.4s, #18
      +0x91c: ushr    v3.4s, v3.4s, #21
      +0x920: bic     v5.4s, #0x38
      +0x924: sub     v3.4s, v5.4s, v3.4s
      +0x928: and     v6.16b, v7.16b, v0.16b
      +0x92c: ushr    v7.4s, v2.4s, #15
      +0x930: ushr    v5.4s, v1.4s, #15
      +0x934: uzp1    v23.8h, v3.8h, v4.8h
      +0x938: ushr    v3.4s, v1.4s, #18
      +0x93c: ushr    v4.4s, v2.4s, #18
      +0x940: and     v24.16b, v24.16b, v0.16b
      +0x944: ushr    v2.4s, v2.4s, #21
      +0x948: and     v7.16b, v7.16b, v0.16b
      +0x94c: and     v0.16b, v5.16b, v0.16b
      +0x950: st4     {v20.8h-v23.8h}, [x8]
      +0x954: ushr    v1.4s, v1.4s, #21
      +0x958: add     x8, x0, #0x1c0
      +0x95c: sub     v0.4s, v6.4s, v0.4s
      +0x960: sub     v5.4s, v24.4s, v7.4s
      +0x964: bic     v4.4s, #0x38
      +0x968: bic     v3.4s, #0x38
      +0x96c: sub     v1.4s, v3.4s, v1.4s
      +0x970: sub     v2.4s, v4.4s, v2.4s
      +0x974: uzp1    v18.8h, v5.8h, v0.8h
      +0x978: uzp1    v19.8h, v2.8h, v1.8h
      +0x97c: st4     {v16.8h-v19.8h}, [x8]
      +0x980: ret
 ***)

let MLKEM_NATIVE_POLY_CBD3_CLANG17_O3_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_clang17_O3_mc
   [layout_range "mlkem_poly_cbd3"];;

(*** The three bytes for four coefficients, as parts of a 24-bit word ***)

let CBD3_BYTES_STMT =
  `!a n i s j.
        read (memory :> bytes(a,192)) s = n /\ i < 64 /\ j < 3
        ==> read (memory :> bytes8(word_add a (word(3 * i + j)))) s =
            word_subword (word(n DIV 2 EXP (24 * i)):24 word) (8 * j,8)`;;

let CBD3_BYTES = assume_spec CBD3_BYTES_STMT;;

(* ------------------------------------------------------------------------- *)
(* As at -O2, coefficient j of 4 for a 24-bit word t comes from the 6-bit    *)
(* field j of t (CBD3_LANE, with the lemmas of gcc12_O2). Here each 32-bit   *)
(* lane of the vector code holds the 24 bits of one group of three bytes,    *)
(* adds its groups of three bits with the mask 0x249249, and the fields are  *)
(* then taken out with SHRN, USHR, UZP1 and AND with 7 and subtracted.       *)
(* ------------------------------------------------------------------------- *)

let SIXBIT_BIT_STMT =
  `!n m k. k < 6
           ==> (n DIV 2 EXP (m + k)) MOD 2 =
               (((n DIV 2 EXP m) MOD 64) DIV 2 EXP k) MOD 2`;;

let SIXBIT_BIT = assume_spec SIXBIT_BIT_STMT;;

let CBD3_FIELD_STMT =
  `!m. m < 64
       ==> word_sub
            (word_zx (word_add (word_add (word_and (word m:6 word) (word 1))
                                         (word_and (word_ushr (word m) 1)
                                                   (word 1)))
                               (word_and (word_ushr (word m) 2) (word 1))))
            (word_zx (word_add (word_add (word_and (word_ushr (word m:6 word)
                                                              3) (word 1))
                                         (word_and (word_ushr (word m) 4)
                                                   (word 1)))
                               (word_ushr (word m) 5))):int16 =
           iword(&(m MOD 2 + (m DIV 2) MOD 2 + (m DIV 4) MOD 2) -
                 &((m DIV 8) MOD 2 + (m DIV 16) MOD 2 + (m DIV 32) MOD 2))`;;

let CBD3_FIELD = assume_spec CBD3_FIELD_STMT;;

let CBD3_LANE_STMT =
  `!n i j w:24 word.
      j < 4 /\ word(n DIV 2 EXP (24 * i)) = w
      ==> let x:6 word = word_subword w (6 * j,6) in
          word_sub
            (word_zx (word_add (word_add (word_and x (word 1))
                                         (word_and (word_ushr x 1) (word 1)))
                               (word_and (word_ushr x 2) (word 1))))
            (word_zx (word_add (word_add (word_and (word_ushr x 3) (word 1))
                                         (word_and (word_ushr x 4) (word 1)))
                               (word_ushr x 5))):int16 =
          iword(&((n DIV 2 EXP (6 * (4 * i + j))) MOD 2 +
                  (n DIV 2 EXP (6 * (4 * i + j) + 1)) MOD 2 +
                  (n DIV 2 EXP (6 * (4 * i + j) + 2)) MOD 2) -
                &((n DIV 2 EXP (6 * (4 * i + j) + 3)) MOD 2 +
                  (n DIV 2 EXP (6 * (4 * i + j) + 4)) MOD 2 +
                  (n DIV 2 EXP (6 * (4 * i + j) + 5)) MOD 2))`;;

let CBD3_LANE = assume_spec CBD3_LANE_STMT;;

(*** The input as 64 words of 24 bits w k, and the 128-bit parts of it that
 *** LD3 reads as joins of their bytes ***)

let CBD3_MERGES = map (fun k ->
  let addr = if k = 0 then `a:int64` else
    mk_comb(mk_comb(`word_add:int64->int64->int64`,`a:int64`),
            mk_comb(`word:num->int64`, mk_small_numeral(16 * k))) in
  READ_MEMORY_MERGE_CONV 4
   (vsubst [addr,`x:int64`] `read (memory :> bytes128 x) s0`)) (0--11);;

let CBD3_INPUT_TAC =
  SUBGOAL_THEN `?w:num->24 word. !k. word(n DIV 2 EXP (24 * k)) = w k`
   STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `\k. word(n DIV 2 EXP (24 * k)):24 word` THEN REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!k. k < 64
        ==> read (memory :> bytes8 (word_add a (word(3 * k)))) s0 =
            word_subword ((w:num->24 word) k) (0,8) /\
            read (memory :> bytes8 (word_add a (word(3 * k + 1)))) s0 =
            word_subword (w k) (8,8) /\
            read (memory :> bytes8 (word_add a (word(3 * k + 2)))) s0 =
            word_subword (w k) (16,8)`
   MP_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(fun th ->
      if is_forall(concl th) && free_in `w:num->24 word` (concl th)
      then REWRITE_TAC[GSYM th] THEN ASSUME_TAC th else NO_TAC) THEN
    MP_TAC(CONV_RULE(NUM_REDUCE_CONV THENC REWRITE_CONV[ADD_CLAUSES])
     (SPECL [`a:int64`; `n:num`; `k:num`; `s0:armstate`; `0`] CBD3_BYTES)) THEN
    MP_TAC(CONV_RULE NUM_REDUCE_CONV
     (SPECL [`a:int64`; `n:num`; `k:num`; `s0:armstate`; `1`] CBD3_BYTES)) THEN
    MP_TAC(CONV_RULE NUM_REDUCE_CONV
     (SPECL [`a:int64`; `n:num`; `k:num`; `s0:armstate`; `2`] CBD3_BYTES)) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  CONV_TAC(LAND_CONV EXPAND_CASES_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[WORD_ADD_0] THEN STRIP_TAC THEN
  MAP_EVERY MP_TAC CBD3_MERGES THEN ASM_REWRITE_TAC[] THEN
  REPEAT DISCH_TAC THEN
  DISCARD_MATCHING_ASSUMPTIONS [`read (memory :> bytes8 a) s = x`];;

(*** After each step: the registers loaded by LD3 and the 128-bit parts of
 *** the memory written by ST4 as joins, and the subwords taken through
 *** AND and OR to the lanes of single groups ***)

let CBD3_SIMPLIFY_CONV =
  TOP_DEPTH_CONV
   (REWR_CONV WORD_SUBWORD_AND ORELSEC REWR_CONV WORD_SUBWORD_OR ORELSEC
    WORD_SIMPLE_SUBWORD_CONV) THENC
  DEPTH_CONV WORD_NUM_RED_CONV;;

let CBD3_SIMD_TAC =
  RULE_ASSUM_TAC(fun th ->
    if can (find_term (fun t -> match t with
              Const(("word_subdeinterleave"|"word_interleave"),_) -> true
            | _ -> false)) (concl th)
    then CONV_RULE(RAND_CONV CBD3_SIMPLIFY_CONV)
          (CONV_RULE(TOP_DEPTH_CONV MLKEM_NATIVE_INTERLEAVE_CONV) th)
    else th) THEN
  TRY(FIRST_X_ASSUM(ASSUME_TAC o CONV_RULE(RAND_CONV CBD3_SIMPLIFY_CONV) o
    check (can (term_match [] `read X (s:armstate):int128 = whatever`) o
           concl)));;

(* ------------------------------------------------------------------------- *)
(* The check for overlap has one branch for each order of the arrays: with   *)
(* the input a (192 bytes) and the output r (512 bytes), the scalar loop is  *)
(* taken unless a + 192 <= r or r + 512 <= a. In either case the vector code *)
(* is entered at the same instruction, after 3 or 6 steps respectively.      *)
(* ------------------------------------------------------------------------- *)

let CBD3_RESOLVE_TAC =
  RULE_ASSUM_TAC(REWRITE_RULE[VAL_WORD_SUB_FLAG; VAL_WORD_SUB_EQ_0]) THEN
  FIRST_X_ASSUM(fun th ->
    let c = concl th in
    if can (term_match [] `read PC s = if p then x else y`) c then
      let p = rand(rator(rator(rand c))) in
      let decide q = SUBGOAL_THEN q (fun th' ->
        ASSUME_TAC(REWRITE_RULE[th'] th)) THENL [ASM_ARITH_TAC; ALL_TAC] in
      decide p ORELSE decide (mk_neg p)
    else failwith "CBD3_RESOLVE_TAC");;

let CBD3_CHECK_TAC (body:int->tactic) =
  MP_TAC(SPECL [`r:int64`; `a:int64`; `512`; `192`]
                NONOVERLAPPING_ALIAS_CHECK) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[NONOVERLAPPING_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  DISCH_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_CBD3_CLANG17_O3_EXEC (1--3) THEN
  ASM_CASES_TAC `val(word_add a (word 192):int64) <= val(r:int64)` THENL
   [CBD3_RESOLVE_TAC THEN body 3;
    CBD3_RESOLVE_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_CBD3_CLANG17_O3_EXEC (4--6) THEN
    CBD3_RESOLVE_TAC THEN body 6];;

(*** The vector code from join1 on: 562 steps and the return ***)

let CBD3_BODY_TAC (simp:tactic) off =
  MAP_EVERY (fun k ->
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_CBD3_CLANG17_O3_EXEC [k + off] THEN
    simp) (1--563);;

(*** The stored coefficients, from the 32 stores of 16 bytes ***)

let CBD3_STORES_TAC =
  REPEAT(FIRST_X_ASSUM(MP_TAC o CONV_RULE(READ_MEMORY_SPLIT_CONV 3) o
    check (fun th -> can (term_match []
                     `read (memory :> bytes128 a) s = x`) (concl th) &&
                     free_in `r:int64` (concl th)))) THEN
  REPEAT(DISCH_THEN(fun th ->
    MAP_EVERY (ASSUME_TAC o
      CONV_RULE(RAND_CONV CBD3_SIMPLIFY_CONV) o
      CONV_RULE(LAND_CONV(REWRITE_CONV[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD])))
     (CONJUNCTS th)));;

(*** Each coefficient i = 4 * g + c in the canonical form of CBD3_LANE for
 *** the field c of w g, to be bit-blasted against the stored value ***)

let CBD3_FIELDS_TAC =
  let norm = CONV_RULE(DEPTH_CONV(NUM_MULT_CONV ORELSEC NUM_ADD_CONV)) in
  FIRST_ASSUM(fun def ->
    if is_forall(concl def) && free_in `w:num->24 word` (concl def) &&
       not(is_imp(snd(dest_forall(concl def))))
    then
      let ths = map (fun i ->
        let g = i / 4 and c = i mod 4 in
        let gt = mk_small_numeral g and ct = mk_small_numeral c in
        let wg = mk_comb(`w:num->24 word`,gt) in
        let th = MP (SPECL [`n:num`; gt; ct; wg] CBD3_LANE)
                    (CONJ (EQT_ELIM(NUM_LT_CONV(mk_binop
                             `(<):num->num->bool` ct `4`)))
                          (SPEC gt def)) in
        GSYM(norm(CONV_RULE(TOP_DEPTH_CONV let_CONV) th))) (0--255) in
      REWRITE_TAC ths
    else NO_TAC);;


(* ------------------------------------------------------------------------- *)
(* Correctness proof. As for mlkem_cbd 3 in common/fips203.ml, coefficient i *)
(* of the result is the number of 1 bits among bits 6 * i to 6 * i + 2 of    *)
(* the 192 bytes as a number n, minus the number among bits 6 * i + 3 to     *)
(* 6 * i + 5, here as a 16-bit integer rather than modulo 3329.              *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_POLY_CBD3_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!r a n pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        ALL (nonoverlapping (r,512)) [(word pc,libmlkem_size); (a,192)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_clang17_O3_mc /\
                  read PC s = word (pc + mlkem_poly_cbd3) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  read (memory :> bytes(a,192)) s = n)
             (\s. read PC s = returnaddress /\
                  !i. i < 256
                      ==> read(memory :> bytes16(word_add r (word(2 * i)))) s =
                          iword(&((n DIV 2 EXP (6 * i)) MOD 2 +
                                  (n DIV 2 EXP (6 * i + 1)) MOD 2 +
                                  (n DIV 2 EXP (6 * i + 2)) MOD 2) -
                                &((n DIV 2 EXP (6 * i + 3)) MOD 2 +
                                  (n DIV 2 EXP (6 * i + 4)) MOD 2 +
                                  (n DIV 2 EXP (6 * i + 5)) MOD 2)))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,512)])`;;

let MLKEM_NATIVE_POLY_CBD3_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_POLY_CBD3_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let mlkem_native_poly_cbd3_signature =
  ([("r", "int16_t[static 256]", "false");
    ("a", "uint8_t[static 192]", "true")],
   "void",
   [("a", "192", 1)],
   [("r", "256", 2)],
   []);;

let full_spec,public_vars = mk_safety_spec
    ~keep_maychanges:true
    mlkem_native_poly_cbd3_signature
    MLKEM_NATIVE_POLY_CBD3_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT
    MLKEM_NATIVE_POLY_CBD3_CLANG17_O3_EXEC;;

let MLKEM_NATIVE_POLY_CBD3_CLANG17_O3_IMAGE_SUBROUTINE_SAFE_STMT =
  `exists f_events.
       forall e r a pc returnaddress.
           aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
           ALL (nonoverlapping (r,512)) [word pc,libmlkem_size; a,192]
           ==> ensures arm
               (\s.
                    aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_clang17_O3_mc /\
                    read PC s = word (pc + mlkem_poly_cbd3) /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [r; a] s /\
                    read events s = e)
               (\s.
                    read PC s = returnaddress /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events a r pc returnaddress /\
                         memaccess_inbounds e2 [a,192; r,512] [r,512]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes (r,512)])`;;

let MLKEM_NATIVE_POLY_CBD3_CLANG17_O3_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_POLY_CBD3_CLANG17_O3_IMAGE_SUBROUTINE_SAFE_STMT;;
