(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The encapsulation of ML-KEM-512 (FIPS 203 Algorithm 17, with the input  *)
(* check of Algorithm 20). This is the code for mlkem512_enc_derand from   *)
(* mlkem-native's portable C implementation compiled by clang 17 with -O3  *)
(* (see mlkem_native/README.md). The compiler has inlined                  *)
(* mlkem512_check_pk: the function decodes the key with                    *)
(* mlkem512_polyvec_frombytes into a buffer on the stack, reduces it with  *)
(* mlkem512_polyvec_reduce, encodes it again with                          *)
(* mlkem512_polyvec_tobytes, compares the result with the key in straight- *)
(* line code of 24 steps of 32 bytes, and zeroes the two buffers with      *)
(* memset. If the comparison fails it returns -4. Otherwise it hashes the  *)
(* key with mlkem_sha3_256, computes K and r as G of the message m (the 32 *)
(* bytes at coins) followed by that hash with mlkem_sha3_512, encrypts m   *)
(* with r by mlkem512_indcpa_enc into the ciphertext, and writes K as the  *)
(* shared secret. In both cases it zeroes its buffers. The statements are  *)
(* those of the gcc 12 -O2 image, except for the stack: the function saves *)
(* its registers (including d8-d15), aligns the buffers to 32 bytes below  *)
(* them, and the frame also includes the 11792 bytes of                    *)
(* mlkem512_indcpa_enc below the buffers. It is verified in the whole      *)
(* image (see libmlkem.ml), using the theorems for                         *)
(* mlkem512_polyvec_frombytes, mlkem512_polyvec_reduce,                    *)
(* mlkem512_polyvec_tobytes, mlkem_sha3_256, mlkem_sha3_512 and            *)
(* mlkem512_indcpa_enc in the image and the contracts for memset.          *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mlkem_native_libc.ml";;
needs "arm/proofs/mlkem_native/clang17_O3/polyvec_frombytes_k2_spec.ml";;
needs "arm/proofs/mlkem_native/clang17_O3/polyvec_reduce_k2_spec.ml";;
needs "arm/proofs/mlkem_native/clang17_O3/polyvec_tobytes_k2_spec.ml";;
needs "arm/proofs/mlkem_native/clang17_O3/sha3_256_spec.ml";;
needs "arm/proofs/mlkem_native/clang17_O3/sha3_512_spec.ml";;
needs "arm/proofs/mlkem_native/clang17_O3/indcpa_enc_k2_spec.ml";;
needs "arm/proofs/utils/mlkem_native_kem.ml";;

(*** The code in the image, and the PLT stub for memset:

    mlkem512_enc_derand:
       +0x0: stp     d15, d14, [sp, #-160]!
       +0x4: stp     d13, d12, [sp, #16]
       +0x8: stp     d11, d10, [sp, #32]
       +0xc: stp     d9, d8, [sp, #48]
      +0x10: stp     x29, x30, [sp, #64]
      +0x14: stp     x28, x27, [sp, #80]
      +0x18: stp     x26, x25, [sp, #96]
      +0x1c: stp     x24, x23, [sp, #112]
      +0x20: stp     x22, x21, [sp, #128]
      +0x24: stp     x20, x19, [sp, #144]
      +0x28: add     x29, sp, #0x40
      +0x2c: sub     x9, sp, #0x720
      +0x30: and     sp, x9, #0xffffffffffffffe0
      +0x34: adrp    x8, <page>
      +0x38: mov     x19, x1
      +0x3c: mov     x21, x0
      +0x40: add     x0, sp, #0x300
      +0x44: mov     x1, x2
      +0x48: mov     x22, x3
      +0x4c: ldr     x8, [x8, #4088]  // got_stack_chk_guard
      +0x50: mov     x20, x2
      +0x54: add     x25, sp, #0x300
      +0x58: ldr     x8, [x8]
      +0x5c: str     x8, [sp, #1816]
      +0x60: bl      <mlkem512_polyvec_frombytes>
      +0x64: add     x0, sp, #0x300
      +0x68: bl      <mlkem512_polyvec_reduce>
      +0x6c: mov     x0, sp
      +0x70: add     x1, sp, #0x300
      +0x74: mov     x24, sp
      +0x78: bl      <mlkem512_polyvec_tobytes>
      +0x7c: ldp     q0, q1, [x20]
      +0x80: mov     w23, wzr
      +0x84: mov     x0, sp
      +0x88: mov     w1, wzr
      +0x8c: mov     w2, #0x300
      +0x90: ldp     q2, q3, [sp]
      +0x94: eor     v2.16b, v2.16b, v0.16b
      +0x98: ldp     q4, q5, [x20, #32]
      +0x9c: eor     v0.16b, v3.16b, v1.16b
      +0xa0: ldp     q6, q7, [sp, #32]
      +0xa4: eor     v4.16b, v6.16b, v4.16b
      +0xa8: ldp     q16, q17, [x20, #64]
      +0xac: eor     v1.16b, v7.16b, v5.16b
      +0xb0: orr     v7.16b, v4.16b, v2.16b
      +0xb4: eor     v4.16b, v4.16b, v2.16b
      +0xb8: ldp     q18, q3, [sp, #64]
      +0xbc: eor     v16.16b, v18.16b, v16.16b
      +0xc0: eor     v4.16b, v16.16b, v4.16b
      +0xc4: ldp     q6, q5, [x20, #96]
      +0xc8: eor     v2.16b, v3.16b, v17.16b
      +0xcc: ldp     q19, q20, [sp, #96]
      +0xd0: eor     v6.16b, v19.16b, v6.16b
      +0xd4: orr     v16.16b, v6.16b, v16.16b
      +0xd8: ldp     q18, q17, [x20, #128]
      +0xdc: eor     v3.16b, v20.16b, v5.16b
      +0xe0: orr     v7.16b, v16.16b, v7.16b
      +0xe4: eor     v6.16b, v6.16b, v4.16b
      +0xe8: ldp     q21, q19, [sp, #128]
      +0xec: eor     v18.16b, v21.16b, v18.16b
      +0xf0: eor     v6.16b, v18.16b, v6.16b
      +0xf4: ldp     q5, q20, [x20, #160]
      +0xf8: eor     v4.16b, v19.16b, v17.16b
      +0xfc: ldp     q16, q22, [sp, #160]
     +0x100: eor     v16.16b, v16.16b, v5.16b
     +0x104: orr     v18.16b, v16.16b, v18.16b
     +0x108: ldp     q21, q17, [x20, #192]
     +0x10c: eor     v5.16b, v22.16b, v20.16b
     +0x110: eor     v16.16b, v16.16b, v6.16b
     +0x114: ldp     q19, q23, [sp, #192]
     +0x118: eor     v19.16b, v19.16b, v21.16b
     +0x11c: orr     v18.16b, v19.16b, v18.16b
     +0x120: ldp     q20, q22, [x20, #224]
     +0x124: eor     v6.16b, v23.16b, v17.16b
     +0x128: orr     v25.16b, v18.16b, v7.16b
     +0x12c: eor     v16.16b, v19.16b, v16.16b
     +0x130: ldp     q24, q21, [sp, #224]
     +0x134: eor     v20.16b, v24.16b, v20.16b
     +0x138: ldp     q17, q23, [x20, #256]
     +0x13c: eor     v7.16b, v21.16b, v22.16b
     +0x140: eor     v22.16b, v20.16b, v16.16b
     +0x144: ldp     q18, q19, [sp, #256]
     +0x148: eor     v17.16b, v18.16b, v17.16b
     +0x14c: orr     v20.16b, v17.16b, v20.16b
     +0x150: ldp     q24, q21, [x20, #288]
     +0x154: eor     v16.16b, v19.16b, v23.16b
     +0x158: eor     v22.16b, v17.16b, v22.16b
     +0x15c: ldp     q26, q18, [sp, #288]
     +0x160: eor     v24.16b, v26.16b, v24.16b
     +0x164: orr     v20.16b, v24.16b, v20.16b
     +0x168: ldp     q19, q23, [x20, #320]
     +0x16c: eor     v17.16b, v18.16b, v21.16b
     +0x170: eor     v22.16b, v24.16b, v22.16b
     +0x174: ldp     q27, q26, [sp, #320]
     +0x178: eor     v19.16b, v27.16b, v19.16b
     +0x17c: orr     v20.16b, v19.16b, v20.16b
     +0x180: ldp     q21, q28, [x20, #352]
     +0x184: eor     v18.16b, v26.16b, v23.16b
     +0x188: orr     v25.16b, v20.16b, v25.16b
     +0x18c: eor     v22.16b, v19.16b, v22.16b
     +0x190: ldp     q24, q27, [sp, #352]
     +0x194: eor     v21.16b, v24.16b, v21.16b
     +0x198: eor     v22.16b, v21.16b, v22.16b
     +0x19c: ldp     q23, q26, [x20, #384]
     +0x1a0: eor     v19.16b, v27.16b, v28.16b
     +0x1a4: ldp     q20, q29, [sp, #384]
     +0x1a8: eor     v23.16b, v20.16b, v23.16b
     +0x1ac: eor     v22.16b, v23.16b, v22.16b
     +0x1b0: ldp     q24, q27, [x20, #416]
     +0x1b4: eor     v20.16b, v29.16b, v26.16b
     +0x1b8: orr     v29.16b, v23.16b, v21.16b
     +0x1bc: ldp     q28, q30, [sp, #416]
     +0x1c0: eor     v24.16b, v28.16b, v24.16b
     +0x1c4: orr     v29.16b, v24.16b, v29.16b
     +0x1c8: ldp     q26, q31, [x20, #448]
     +0x1cc: eor     v21.16b, v30.16b, v27.16b
     +0x1d0: eor     v24.16b, v24.16b, v22.16b
     +0x1d4: ldp     q23, q28, [sp, #448]
     +0x1d8: eor     v23.16b, v23.16b, v26.16b
     +0x1dc: orr     v29.16b, v23.16b, v29.16b
     +0x1e0: ldp     q27, q30, [x20, #480]
     +0x1e4: eor     v22.16b, v28.16b, v31.16b
     +0x1e8: eor     v24.16b, v23.16b, v24.16b
     +0x1ec: ldp     q8, q26, [sp, #480]
     +0x1f0: eor     v27.16b, v8.16b, v27.16b
     +0x1f4: orr     v29.16b, v27.16b, v29.16b
     +0x1f8: ldp     q28, q31, [x20, #512]
     +0x1fc: eor     v23.16b, v26.16b, v30.16b
     +0x200: orr     v10.16b, v29.16b, v25.16b
     +0x204: eor     v27.16b, v27.16b, v24.16b
     +0x208: ldp     q9, q8, [sp, #512]
     +0x20c: eor     v28.16b, v9.16b, v28.16b
     +0x210: eor     v27.16b, v28.16b, v27.16b
     +0x214: ldp     q26, q30, [x20, #544]
     +0x218: eor     v24.16b, v8.16b, v31.16b
     +0x21c: ldp     q25, q29, [sp, #544]
     +0x220: eor     v26.16b, v25.16b, v26.16b
     +0x224: orr     v28.16b, v26.16b, v28.16b
     +0x228: ldp     q9, q31, [x20, #576]
     +0x22c: eor     v25.16b, v29.16b, v30.16b
     +0x230: eor     v27.16b, v26.16b, v27.16b
     +0x234: ldp     q8, q11, [sp, #576]
     +0x238: eor     v8.16b, v8.16b, v9.16b
     +0x23c: orr     v28.16b, v8.16b, v28.16b
     +0x240: ldp     q29, q30, [x20, #608]
     +0x244: eor     v26.16b, v11.16b, v31.16b
     +0x248: eor     v8.16b, v8.16b, v27.16b
     +0x24c: ldp     q12, q9, [sp, #608]
     +0x250: eor     v29.16b, v12.16b, v29.16b
     +0x254: ldp     q31, q11, [x20, #640]
     +0x258: eor     v27.16b, v9.16b, v30.16b
     +0x25c: orr     v9.16b, v29.16b, v28.16b
     +0x260: eor     v29.16b, v29.16b, v8.16b
     +0x264: ldp     q13, q12, [sp, #640]
     +0x268: eor     v31.16b, v13.16b, v31.16b
     +0x26c: orr     v9.16b, v31.16b, v9.16b
     +0x270: ldp     q30, q14, [x20, #672]
     +0x274: eor     v28.16b, v12.16b, v11.16b
     +0x278: eor     v31.16b, v31.16b, v29.16b
     +0x27c: ldp     q8, q13, [sp, #672]
     +0x280: eor     v30.16b, v8.16b, v30.16b
     +0x284: orr     v9.16b, v30.16b, v9.16b
     +0x288: ldp     q11, q12, [x20, #704]
     +0x28c: eor     v29.16b, v13.16b, v14.16b
     +0x290: orr     v9.16b, v9.16b, v10.16b
     +0x294: eor     v30.16b, v30.16b, v31.16b
     +0x298: ldp     q15, q8, [sp, #704]
     +0x29c: eor     v11.16b, v15.16b, v11.16b
     +0x2a0: eor     v30.16b, v11.16b, v30.16b
     +0x2a4: ldp     q13, q14, [x20, #736]
     +0x2a8: eor     v8.16b, v8.16b, v12.16b
     +0x2ac: ldp     q10, q15, [sp, #736]
     +0x2b0: eor     v10.16b, v10.16b, v13.16b
     +0x2b4: orr     v13.16b, v10.16b, v11.16b
     +0x2b8: orr     v13.16b, v0.16b, v13.16b
     +0x2bc: orr     v13.16b, v13.16b, v1.16b
     +0x2c0: orr     v13.16b, v13.16b, v2.16b
     +0x2c4: orr     v13.16b, v13.16b, v3.16b
     +0x2c8: eor     v0.16b, v0.16b, v1.16b
     +0x2cc: orr     v13.16b, v13.16b, v4.16b
     +0x2d0: eor     v0.16b, v0.16b, v2.16b
     +0x2d4: orr     v9.16b, v13.16b, v9.16b
     +0x2d8: orr     v13.16b, v5.16b, v6.16b
     +0x2dc: eor     v0.16b, v0.16b, v3.16b
     +0x2e0: orr     v13.16b, v13.16b, v7.16b
     +0x2e4: eor     v0.16b, v0.16b, v4.16b
     +0x2e8: orr     v13.16b, v13.16b, v16.16b
     +0x2ec: eor     v0.16b, v0.16b, v5.16b
     +0x2f0: orr     v13.16b, v13.16b, v17.16b
     +0x2f4: eor     v0.16b, v0.16b, v6.16b
     +0x2f8: orr     v13.16b, v13.16b, v18.16b
     +0x2fc: eor     v0.16b, v0.16b, v7.16b
     +0x300: orr     v13.16b, v13.16b, v19.16b
     +0x304: eor     v0.16b, v0.16b, v16.16b
     +0x308: orr     v13.16b, v13.16b, v20.16b
     +0x30c: eor     v0.16b, v0.16b, v17.16b
     +0x310: orr     v9.16b, v9.16b, v13.16b
     +0x314: orr     v13.16b, v21.16b, v22.16b
     +0x318: eor     v0.16b, v0.16b, v18.16b
     +0x31c: orr     v13.16b, v13.16b, v23.16b
     +0x320: eor     v0.16b, v0.16b, v19.16b
     +0x324: orr     v13.16b, v13.16b, v24.16b
     +0x328: eor     v0.16b, v0.16b, v20.16b
     +0x32c: orr     v13.16b, v13.16b, v25.16b
     +0x330: eor     v0.16b, v0.16b, v21.16b
     +0x334: orr     v13.16b, v13.16b, v26.16b
     +0x338: eor     v0.16b, v0.16b, v22.16b
     +0x33c: orr     v13.16b, v13.16b, v27.16b
     +0x340: eor     v0.16b, v0.16b, v23.16b
     +0x344: orr     v13.16b, v13.16b, v28.16b
     +0x348: eor     v0.16b, v0.16b, v24.16b
     +0x34c: eor     v12.16b, v15.16b, v14.16b
     +0x350: orr     v13.16b, v13.16b, v29.16b
     +0x354: eor     v0.16b, v0.16b, v25.16b
     +0x358: orr     v9.16b, v9.16b, v13.16b
     +0x35c: orr     v13.16b, v8.16b, v12.16b
     +0x360: eor     v0.16b, v0.16b, v26.16b
     +0x364: orr     v9.16b, v9.16b, v13.16b
     +0x368: eor     v0.16b, v0.16b, v27.16b
     +0x36c: ext     v13.16b, v9.16b, v9.16b, #8
     +0x370: eor     v0.16b, v0.16b, v28.16b
     +0x374: eor     v0.16b, v0.16b, v29.16b
     +0x378: eor     v0.16b, v0.16b, v8.16b
     +0x37c: eor     v30.16b, v10.16b, v30.16b
     +0x380: eor     v0.16b, v0.16b, v12.16b
     +0x384: orr     v31.8b, v9.8b, v13.8b
     +0x388: eor     v0.16b, v0.16b, v30.16b
     +0x38c: fmov    x8, d31
     +0x390: ext     v1.16b, v0.16b, v0.16b, #8
     +0x394: orr     x8, x8, x8, lsr #32
     +0x398: lsr     x9, x8, #16
     +0x39c: eor     v0.8b, v0.8b, v1.8b
     +0x3a0: orr     w8, w8, w9
     +0x3a4: fmov    x9, d0
     +0x3a8: orr     w8, w8, w8, lsr #8
     +0x3ac: sub     w8, w23, w8, uxtb
     +0x3b0: eor     x9, x9, x9, lsr #32
     +0x3b4: eor     x9, x9, x9, lsr #16
     +0x3b8: lsr     x10, x9, #8
     +0x3bc: eor     w26, w9, w10
     +0x3c0: eor     w8, w26, w8, lsr #16
     +0x3c4: and     w27, w8, #0xff
     +0x3c8: bl      <memset@plt>
     +0x3cc: add     x0, sp, #0x300
     +0x3d0: mov     w1, wzr
     +0x3d4: mov     w2, #0x400
     +0x3d8: bl      <memset@plt>
     +0x3dc: cmp     w27, w26, uxtb
     +0x3e0: b.ne    <mlkem512_enc_derand+0x430>
     +0x3e4: ldp     q0, q1, [x22]
     +0x3e8: add     x0, x25, #0x20
     +0x3ec: mov     x1, x20
     +0x3f0: mov     w2, #0x320
     +0x3f4: stp     q0, q1, [sp, #768]
     +0x3f8: bl      <mlkem_sha3_256>
     +0x3fc: mov     x0, sp
     +0x400: add     x1, sp, #0x300
     +0x404: mov     w2, #0x40
     +0x408: bl      <mlkem_sha3_512>
     +0x40c: add     x3, x24, #0x20
     +0x410: add     x1, sp, #0x300
     +0x414: mov     x0, x21
     +0x418: mov     x2, x20
     +0x41c: bl      <mlkem512_indcpa_enc>
     +0x420: cbnz    w0, <mlkem512_enc_derand+0x434>
     +0x424: ldp     q0, q1, [sp]
     +0x428: stp     q0, q1, [x19]
     +0x42c: b       <mlkem512_enc_derand+0x434>
     +0x430: mov     w0, #0xfffffffc
     +0x434: movi    v0.2d, #0x0
     +0x438: mov     x8, sp
     +0x43c: stp     q0, q0, [sp]
     +0x440: stp     q0, q0, [sp, #32]
     +0x444: stp     q0, q0, [sp, #800]
     +0x448: add     x8, sp, #0x300
     +0x44c: stp     q0, q0, [sp, #768]
     +0x450: adrp    x8, <page>
     +0x454: ldr     x8, [x8, #4088]  // got_stack_chk_guard
     +0x458: ldr     x9, [sp, #1816]
     +0x45c: ldr     x8, [x8]
     +0x460: cmp     x8, x9
     +0x464: b.ne    <mlkem512_enc_derand+0x498>
     +0x468: sub     sp, x29, #0x40
     +0x46c: ldp     x20, x19, [sp, #144]
     +0x470: ldp     x22, x21, [sp, #128]
     +0x474: ldp     x24, x23, [sp, #112]
     +0x478: ldp     x26, x25, [sp, #96]
     +0x47c: ldp     x28, x27, [sp, #80]
     +0x480: ldp     x29, x30, [sp, #64]
     +0x484: ldp     d9, d8, [sp, #48]
     +0x488: ldp     d11, d10, [sp, #32]
     +0x48c: ldp     d13, d12, [sp, #16]
     +0x490: ldp     d15, d14, [sp], #160
     +0x494: ret
     +0x498: bl      <__stack_chk_fail@plt>

    memset@plt:
      +0x0: adrp    x16, <page>
      +0x4: ldr     x17, [x16, #4072]  // got_memset
      +0x8: add     x16, x16, #0xfe8  // got_memset
      +0xc: br      x17
 ***)

let MLKEM_NATIVE_ENC_DERAND_K2_CLANG17_O3_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_clang17_O3_mc
   [layout_range "mlkem512_enc_derand"; layout_range "plt_memset"];;

let KE2_EXEC = MLKEM_NATIVE_ENC_DERAND_K2_CLANG17_O3_EXEC;;

(* ------------------------------------------------------------------------- *)
(* The input check of FIPS 203 for ML-KEM-512 in terms of the result of      *)
(* mlkem512_check_pk, and the address of the buffers, which are aligned to   *)
(* 32 bytes within the stack frame.                                          *)
(* ------------------------------------------------------------------------- *)

let MLKEM_EK_CHECK_512_STMT =
  `!ek. LENGTH ek = 800
        ==> (mlkem_ek_check mlkem512 ek <=>
             !i. i < 512
                 ==> (num_of_bytelist ek DIV 2 EXP (12 * i)) MOD 2 EXP 12
                     < 3329)`;;

let MLKEM_EK_CHECK_512 = assume_spec MLKEM_EK_CHECK_512_STMT;;

let KE2_CHECK_EQ_STMT =
  `!n. (!i. i < 512
            ==> ((n MOD 2 EXP (8 * 768)) DIV 2 EXP (12 * i)) MOD 2 EXP 12
                < 3329) <=>
       (!i. i < 512 ==> (n DIV 2 EXP (12 * i)) MOD 2 EXP 12 < 3329)`;;

let KE2_CHECK_EQ = assume_spec KE2_CHECK_EQ_STMT;;

let KE2_BUFFER_ADDRESS_STMT =
  `!sp:int64.
        aligned 16 sp
        ==> word_and (word_add sp (word 11808)) (word 18446744073709551584) =
            word_add sp (word(if aligned 32 sp then 11808 else 11792))`;;

let KE2_BUFFER_ADDRESS = assume_spec KE2_BUFFER_ADDRESS_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof, assuming the contracts for memset and memcpy (for the  *)
(* callees). The encapsulation key ek of 800 bytes is at pk and the message  *)
(* m of 32 bytes at coins, and if ek passes the check of FIPS 203, the       *)
(* shared secret of 32 bytes written at ss and the ciphertext of 768 bytes   *)
(* written at ct are those of mlkem_encaps_internal mlkem512 ek m in         *)
(* common/fips203/fips203.ml and the function returns 0, and otherwise it    *)
(* returns -4. The theorem assumes that SampleNTT terminates for each entry  *)
(* of the matrix, as for mlkem512_indcpa_enc. The stack is the 160 bytes of  *)
(* the saved registers, the buffers of 1824 bytes aligned to 32 bytes below  *)
(* them (with up to 16 bytes of padding) and the 11792 used by               *)
(* mlkem512_indcpa_enc below the buffers.                                    *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_ENC_DERAND_K2_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!ct ss pk coins (ek:byte list) (m:byte list) guard mf mc ea el
    ev pc stackpointer returnaddress.
        memset_contract mf ea el ev /\ memcpy_contract mc ea el ev /\
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\ LENGTH ek = 800 /\ LENGTH m = 32 /\
        (!i j. i < 2 /\ j < 2
               ==> mlkem_samplentt_terminates
                    (APPEND (mlkem_slice 768 32 ek) [word j; word i])) /\
        nonoverlapping (pk,800) (word pc,libmlkem_size) /\
        PAIRWISE nonoverlapping
         [(ct,768); (ss,32); (word_sub stackpointer (word 13792),13792)] /\
        ALLPAIRS nonoverlapping
         [(ct,768); (ss,32); (word_sub stackpointer (word 13792),13792)]
         [(pk,800); (coins,32); (word pc,libmlkem_size);
          (word(pc + got_stack_chk_guard),8);
          (guard,8); (word(pc + got_memset),8); (word(pc + got_memcpy),8);
          (ea,el)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_clang17_O3_mc /\
                  read PC s = word (pc + mlkem512_enc_derand) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [ct; ss; pk; coins] s /\
                  read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                    guard /\
                  read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                  read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                  read (memory :> bytes(ea,el)) s = ev /\
                  read (memory :> bytes(pk,800)) s = num_of_bytelist ek /\
                  read (memory :> bytes(coins,32)) s = num_of_bytelist m)
             (\s. read PC s = returnaddress /\
                  (mlkem_ek_check mlkem512 ek
                   ==> read (memory :> bytes(ss,32)) s =
                       num_of_bytelist
                        (FST(mlkem_encaps_internal mlkem512 ek m)) /\
                       read (memory :> bytes(ct,768)) s =
                       num_of_bytelist
                        (SND(mlkem_encaps_internal mlkem512 ek m))) /\
                  C_RETURN s =
                  (if mlkem_ek_check mlkem512 ek then word 0
                   else word 0xfffffffc))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
              MAYCHANGE
               [memory :> bytes(ct,768); memory :> bytes(ss,32);
                memory :> bytes(word_sub stackpointer (word 13792),13792)])`;;

let MLKEM_NATIVE_ENC_DERAND_K2_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_ENC_DERAND_K2_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof, assuming the combined contract   *)
(* for memset (for mlkem512_indcpa_enc and the memset calls of this        *)
(* function) and the safety contract for memcpy. The events depend only on *)
(* the addresses and on the encapsulation key, which is public: the        *)
(* function branches on the result of the comparison of the key with its   *)
(* re-encoding, which is the check of the key, and the events of the       *)
(* encryption depend on rho.                                               *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let MLKEM_NATIVE_ENC_DERAND_K2_CLANG17_O3_IMAGE_SUBROUTINE_SAFE_STMT =
  `!mf mc ea el ev.
   memset_full_contract mf ea el ev /\ memcpy_safety_contract mc ea el ev
   ==> exists f_events.
        forall e ct ss pk coins (ek:byte list) guard pc stackpointer
               returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\ LENGTH ek = 800 /\
          (!i j. i < 2 /\ j < 2
                 ==> mlkem_samplentt_terminates
                      (APPEND (mlkem_slice 768 32 ek) [word j; word i])) /\
          nonoverlapping (pk,800) (word pc,libmlkem_size) /\
          PAIRWISE nonoverlapping
           [(ct,768); (ss,32); (word_sub stackpointer (word 13792),13792)] /\
          ALLPAIRS nonoverlapping
           [(ct,768); (ss,32); (word_sub stackpointer (word 13792),13792)]
           [(pk,800); (coins,32); (word pc,libmlkem_size);
            (word(pc + got_stack_chk_guard),8);
            (guard,8); (word(pc + got_memset),8); (word(pc + got_memcpy),8);
            (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mlkem_native_libmlkem_clang17_O3_mc /\
                    read PC s = word (pc + mlkem512_enc_derand) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [ct; ss; pk; coins] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s
                     = guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(pk,800)) s = num_of_bytelist ek /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    C_RETURN s =
                    (if mlkem_ek_check mlkem512 ek then word 0
                     else word 0xfffffffc) /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events ct ss pk coins guard mf mc pc
                              (word_sub stackpointer (word 13792))
                              returnaddress ek /\
                       memaccess_inbounds e2
                        [pk,800; coins,32; ct,768; ss,32;
                         word_sub stackpointer (word 13792),13792;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8;
                         word(pc + got_memcpy),8; ea,el;
                         word(pc + rodata_mlk_KeccakF_RoundConstants),192;
                         word(pc + mlkem_poly_cbd2_consts),
                         mlkem_poly_cbd2_consts_size;
                         word(pc + rodata_mlk_zetas),256;
                         word(pc + mlkem_poly_ntt_consts),
                         mlkem_poly_ntt_consts_size;
                         word(pc + mlkem_poly_mulcache_compute_consts),
                         mlkem_poly_mulcache_compute_consts_size;
                         word(pc + mlkem_poly_invntt_tomont_consts),
                         mlkem_poly_invntt_tomont_consts_size;
                         word(pc + mlkem_poly_compress_d4_consts),
                         mlkem_poly_compress_d4_consts_size]
                        [ct,768; ss,32;
                         word_sub stackpointer (word 13792),13792]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(ct,768); memory :> bytes(ss,32);
                  memory :> bytes(word_sub stackpointer (word 13792),13792)])`;;

let MLKEM_NATIVE_ENC_DERAND_K2_CLANG17_O3_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_ENC_DERAND_K2_CLANG17_O3_IMAGE_SUBROUTINE_SAFE_STMT;;
