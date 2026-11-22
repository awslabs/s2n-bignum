(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The decapsulation of ML-KEM-512 (FIPS 203 Algorithm 18, with the input    *)
(* check of Algorithm 21). This is the code for mlkem512_dec from mlkem-     *)
(* native's portable C implementation compiled by clang 17 with -O3 (see     *)
(* mlkem_native/README.md). It checks the decapsulation key with             *)
(* mlkem512_check_sk, and returns -5 if the check fails. Otherwise it        *)
(* decrypts the ciphertext into m' with mlkem512_indcpa_dec, computes K' and *)
(* r' as G of m' followed by the hash h in the key with mlkem_sha3_512,      *)
(* encrypts m' with r' again by mlkem512_indcpa_enc, compares the result     *)
(* with the ciphertext in constant time (straight-line code over 24 blocks   *)
(* of 32 bytes, which also saves and restores d8-d15), computes J of z (in   *)
(* the key) followed by the ciphertext into the shared secret with           *)
(* mlkem_shake256, and replaces it by K' if the ciphertexts are equal,       *)
(* again in constant time. In both cases it zeroes its buffers. The          *)
(* statements are those of the gcc 12 -O2 image, except for the stack: the   *)
(* function saves its registers, aligns the buffers to 32 bytes below them,  *)
(* and the frame also includes the 11792 bytes of mlkem512_indcpa_enc below  *)
(* the buffers. It is verified in the whole image (see libmlkem.ml), using   *)
(* the theorems for mlkem512_check_sk, mlkem512_indcpa_dec, mlkem_sha3_512,  *)
(* mlkem512_indcpa_enc and mlkem_shake256 in the image and the contracts for *)
(* memset and memcpy.                                                        *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/mlkem_native/clang17_O3/check_sk_k2_spec.ml";;
needs "arm/proofs/mlkem_native/clang17_O3/indcpa_dec_k2_spec.ml";;
needs "arm/proofs/mlkem_native/clang17_O3/sha3_512_spec.ml";;
needs "arm/proofs/mlkem_native/clang17_O3/indcpa_enc_k2_spec.ml";;
needs "arm/proofs/mlkem_native/clang17_O3/shake256_spec.ml";;
needs "arm/proofs/utils/mlkem_native_kem.ml";;

(*** The code in the image:

    mlkem512_dec:
       +0x0: stp     d15, d14, [sp, #-144]!
       +0x4: stp     d13, d12, [sp, #16]
       +0x8: stp     d11, d10, [sp, #32]
       +0xc: stp     d9, d8, [sp, #48]
      +0x10: stp     x29, x30, [sp, #64]
      +0x14: str     x28, [sp, #80]
      +0x18: stp     x24, x23, [sp, #96]
      +0x1c: stp     x22, x21, [sp, #112]
      +0x20: stp     x20, x19, [sp, #128]
      +0x24: add     x29, sp, #0x40
      +0x28: sub     x9, sp, #0x3b0
      +0x2c: and     sp, x9, #0xffffffffffffffe0
      +0x30: adrp    x8, <page>
      +0x34: mov     x19, x0
      +0x38: mov     x0, x2
      +0x3c: mov     x21, x2
      +0x40: mov     x20, x1
      +0x44: ldr     x8, [x8, #4088]
      +0x48: ldr     x8, [x8]
      +0x4c: str     x8, [sp, #936]
      +0x50: bl      <mlkem512_check_sk>
      +0x54: mov     w22, w0
      +0x58: cbnz    w0, <mlkem512_dec+0x45c>
      +0x5c: add     x0, sp, #0x360
      +0x60: mov     x1, x20
      +0x64: mov     x2, x21
      +0x68: bl      <mlkem512_indcpa_dec>
      +0x6c: mov     w22, w0
      +0x70: cbnz    w0, <mlkem512_dec+0x45c>
      +0x74: ldr     q0, [x21, #1568]
      +0x78: add     x0, sp, #0x320
      +0x7c: ldr     q1, [x21, #1584]
      +0x80: add     x1, sp, #0x360
      +0x84: mov     w2, #0x40
      +0x88: add     x22, x21, #0x300
      +0x8c: add     x23, sp, #0x320
      +0x90: stp     q0, q1, [sp, #896]
      +0x94: bl      <mlkem_sha3_512>
      +0x98: add     x3, x23, #0x20
      +0x9c: mov     x0, sp
      +0xa0: add     x1, sp, #0x360
      +0xa4: mov     x2, x22
      +0xa8: mov     x24, sp
      +0xac: bl      <mlkem512_indcpa_enc>
      +0xb0: mov     w22, w0
      +0xb4: cbnz    w0, <mlkem512_dec+0x45c>
      +0xb8: ldp     q0, q1, [x20]
      +0xbc: add     x0, x24, #0x20
      +0xc0: mov     x1, x20
      +0xc4: mov     w2, #0x300
      +0xc8: ldp     q2, q3, [sp]
      +0xcc: eor     v2.16b, v2.16b, v0.16b
      +0xd0: ldp     q4, q5, [x20, #32]
      +0xd4: eor     v0.16b, v3.16b, v1.16b
      +0xd8: ldp     q6, q7, [sp, #32]
      +0xdc: eor     v4.16b, v6.16b, v4.16b
      +0xe0: ldp     q16, q17, [x20, #64]
      +0xe4: eor     v1.16b, v7.16b, v5.16b
      +0xe8: orr     v7.16b, v4.16b, v2.16b
      +0xec: eor     v4.16b, v4.16b, v2.16b
      +0xf0: ldp     q18, q3, [sp, #64]
      +0xf4: eor     v16.16b, v18.16b, v16.16b
      +0xf8: eor     v4.16b, v16.16b, v4.16b
      +0xfc: ldp     q6, q5, [x20, #96]
     +0x100: eor     v2.16b, v3.16b, v17.16b
     +0x104: ldp     q19, q20, [sp, #96]
     +0x108: eor     v6.16b, v19.16b, v6.16b
     +0x10c: orr     v16.16b, v6.16b, v16.16b
     +0x110: ldp     q18, q17, [x20, #128]
     +0x114: eor     v3.16b, v20.16b, v5.16b
     +0x118: orr     v7.16b, v16.16b, v7.16b
     +0x11c: eor     v6.16b, v6.16b, v4.16b
     +0x120: ldp     q21, q19, [sp, #128]
     +0x124: eor     v18.16b, v21.16b, v18.16b
     +0x128: eor     v6.16b, v18.16b, v6.16b
     +0x12c: ldp     q5, q20, [x20, #160]
     +0x130: eor     v4.16b, v19.16b, v17.16b
     +0x134: ldp     q16, q22, [sp, #160]
     +0x138: eor     v16.16b, v16.16b, v5.16b
     +0x13c: orr     v18.16b, v16.16b, v18.16b
     +0x140: ldp     q21, q17, [x20, #192]
     +0x144: eor     v5.16b, v22.16b, v20.16b
     +0x148: eor     v16.16b, v16.16b, v6.16b
     +0x14c: ldp     q19, q23, [sp, #192]
     +0x150: eor     v19.16b, v19.16b, v21.16b
     +0x154: orr     v18.16b, v19.16b, v18.16b
     +0x158: ldp     q20, q22, [x20, #224]
     +0x15c: eor     v6.16b, v23.16b, v17.16b
     +0x160: orr     v25.16b, v18.16b, v7.16b
     +0x164: eor     v16.16b, v19.16b, v16.16b
     +0x168: ldp     q24, q21, [sp, #224]
     +0x16c: eor     v20.16b, v24.16b, v20.16b
     +0x170: ldp     q17, q23, [x20, #256]
     +0x174: eor     v7.16b, v21.16b, v22.16b
     +0x178: eor     v22.16b, v20.16b, v16.16b
     +0x17c: ldp     q18, q19, [sp, #256]
     +0x180: eor     v17.16b, v18.16b, v17.16b
     +0x184: orr     v20.16b, v17.16b, v20.16b
     +0x188: ldp     q24, q21, [x20, #288]
     +0x18c: eor     v16.16b, v19.16b, v23.16b
     +0x190: eor     v22.16b, v17.16b, v22.16b
     +0x194: ldp     q26, q18, [sp, #288]
     +0x198: eor     v24.16b, v26.16b, v24.16b
     +0x19c: orr     v20.16b, v24.16b, v20.16b
     +0x1a0: ldp     q19, q23, [x20, #320]
     +0x1a4: eor     v17.16b, v18.16b, v21.16b
     +0x1a8: eor     v22.16b, v24.16b, v22.16b
     +0x1ac: ldp     q27, q26, [sp, #320]
     +0x1b0: eor     v19.16b, v27.16b, v19.16b
     +0x1b4: orr     v20.16b, v19.16b, v20.16b
     +0x1b8: ldp     q21, q28, [x20, #352]
     +0x1bc: eor     v18.16b, v26.16b, v23.16b
     +0x1c0: orr     v25.16b, v20.16b, v25.16b
     +0x1c4: eor     v22.16b, v19.16b, v22.16b
     +0x1c8: ldp     q24, q27, [sp, #352]
     +0x1cc: eor     v21.16b, v24.16b, v21.16b
     +0x1d0: eor     v22.16b, v21.16b, v22.16b
     +0x1d4: ldp     q23, q26, [x20, #384]
     +0x1d8: eor     v19.16b, v27.16b, v28.16b
     +0x1dc: ldp     q20, q29, [sp, #384]
     +0x1e0: eor     v23.16b, v20.16b, v23.16b
     +0x1e4: eor     v22.16b, v23.16b, v22.16b
     +0x1e8: ldp     q24, q27, [x20, #416]
     +0x1ec: eor     v20.16b, v29.16b, v26.16b
     +0x1f0: orr     v29.16b, v23.16b, v21.16b
     +0x1f4: ldp     q28, q30, [sp, #416]
     +0x1f8: eor     v24.16b, v28.16b, v24.16b
     +0x1fc: orr     v29.16b, v24.16b, v29.16b
     +0x200: ldp     q26, q31, [x20, #448]
     +0x204: eor     v21.16b, v30.16b, v27.16b
     +0x208: eor     v24.16b, v24.16b, v22.16b
     +0x20c: ldp     q23, q28, [sp, #448]
     +0x210: eor     v23.16b, v23.16b, v26.16b
     +0x214: orr     v29.16b, v23.16b, v29.16b
     +0x218: ldp     q27, q30, [x20, #480]
     +0x21c: eor     v22.16b, v28.16b, v31.16b
     +0x220: eor     v24.16b, v23.16b, v24.16b
     +0x224: ldp     q8, q26, [sp, #480]
     +0x228: eor     v27.16b, v8.16b, v27.16b
     +0x22c: orr     v29.16b, v27.16b, v29.16b
     +0x230: ldp     q28, q31, [x20, #512]
     +0x234: eor     v23.16b, v26.16b, v30.16b
     +0x238: orr     v10.16b, v29.16b, v25.16b
     +0x23c: eor     v27.16b, v27.16b, v24.16b
     +0x240: ldp     q9, q8, [sp, #512]
     +0x244: eor     v28.16b, v9.16b, v28.16b
     +0x248: eor     v27.16b, v28.16b, v27.16b
     +0x24c: ldp     q26, q30, [x20, #544]
     +0x250: eor     v24.16b, v8.16b, v31.16b
     +0x254: ldp     q25, q29, [sp, #544]
     +0x258: eor     v26.16b, v25.16b, v26.16b
     +0x25c: orr     v28.16b, v26.16b, v28.16b
     +0x260: ldp     q9, q31, [x20, #576]
     +0x264: eor     v25.16b, v29.16b, v30.16b
     +0x268: eor     v27.16b, v26.16b, v27.16b
     +0x26c: ldp     q8, q11, [sp, #576]
     +0x270: eor     v8.16b, v8.16b, v9.16b
     +0x274: orr     v28.16b, v8.16b, v28.16b
     +0x278: ldp     q29, q30, [x20, #608]
     +0x27c: eor     v26.16b, v11.16b, v31.16b
     +0x280: eor     v8.16b, v8.16b, v27.16b
     +0x284: ldp     q12, q9, [sp, #608]
     +0x288: eor     v29.16b, v12.16b, v29.16b
     +0x28c: ldp     q31, q11, [x20, #640]
     +0x290: eor     v27.16b, v9.16b, v30.16b
     +0x294: orr     v9.16b, v29.16b, v28.16b
     +0x298: eor     v29.16b, v29.16b, v8.16b
     +0x29c: ldp     q13, q12, [sp, #640]
     +0x2a0: eor     v31.16b, v13.16b, v31.16b
     +0x2a4: orr     v9.16b, v31.16b, v9.16b
     +0x2a8: ldp     q30, q14, [x20, #672]
     +0x2ac: eor     v28.16b, v12.16b, v11.16b
     +0x2b0: eor     v31.16b, v31.16b, v29.16b
     +0x2b4: ldp     q8, q13, [sp, #672]
     +0x2b8: eor     v30.16b, v8.16b, v30.16b
     +0x2bc: orr     v9.16b, v30.16b, v9.16b
     +0x2c0: ldp     q11, q12, [x20, #704]
     +0x2c4: eor     v29.16b, v13.16b, v14.16b
     +0x2c8: orr     v9.16b, v9.16b, v10.16b
     +0x2cc: eor     v30.16b, v30.16b, v31.16b
     +0x2d0: ldp     q15, q8, [sp, #704]
     +0x2d4: eor     v11.16b, v15.16b, v11.16b
     +0x2d8: eor     v30.16b, v11.16b, v30.16b
     +0x2dc: ldp     q13, q14, [x20, #736]
     +0x2e0: eor     v8.16b, v8.16b, v12.16b
     +0x2e4: ldp     q10, q15, [sp, #736]
     +0x2e8: eor     v10.16b, v10.16b, v13.16b
     +0x2ec: orr     v13.16b, v10.16b, v11.16b
     +0x2f0: orr     v13.16b, v0.16b, v13.16b
     +0x2f4: orr     v13.16b, v13.16b, v1.16b
     +0x2f8: orr     v13.16b, v13.16b, v2.16b
     +0x2fc: orr     v13.16b, v13.16b, v3.16b
     +0x300: eor     v0.16b, v0.16b, v1.16b
     +0x304: orr     v13.16b, v13.16b, v4.16b
     +0x308: eor     v0.16b, v0.16b, v2.16b
     +0x30c: orr     v9.16b, v13.16b, v9.16b
     +0x310: orr     v13.16b, v5.16b, v6.16b
     +0x314: eor     v0.16b, v0.16b, v3.16b
     +0x318: orr     v13.16b, v13.16b, v7.16b
     +0x31c: eor     v0.16b, v0.16b, v4.16b
     +0x320: orr     v13.16b, v13.16b, v16.16b
     +0x324: eor     v0.16b, v0.16b, v5.16b
     +0x328: orr     v13.16b, v13.16b, v17.16b
     +0x32c: eor     v0.16b, v0.16b, v6.16b
     +0x330: orr     v13.16b, v13.16b, v18.16b
     +0x334: eor     v0.16b, v0.16b, v7.16b
     +0x338: orr     v13.16b, v13.16b, v19.16b
     +0x33c: eor     v0.16b, v0.16b, v16.16b
     +0x340: orr     v13.16b, v13.16b, v20.16b
     +0x344: eor     v0.16b, v0.16b, v17.16b
     +0x348: orr     v9.16b, v9.16b, v13.16b
     +0x34c: orr     v13.16b, v21.16b, v22.16b
     +0x350: eor     v0.16b, v0.16b, v18.16b
     +0x354: orr     v13.16b, v13.16b, v23.16b
     +0x358: eor     v0.16b, v0.16b, v19.16b
     +0x35c: orr     v13.16b, v13.16b, v24.16b
     +0x360: eor     v0.16b, v0.16b, v20.16b
     +0x364: orr     v13.16b, v13.16b, v25.16b
     +0x368: eor     v0.16b, v0.16b, v21.16b
     +0x36c: orr     v13.16b, v13.16b, v26.16b
     +0x370: eor     v0.16b, v0.16b, v22.16b
     +0x374: orr     v13.16b, v13.16b, v27.16b
     +0x378: eor     v0.16b, v0.16b, v23.16b
     +0x37c: orr     v13.16b, v13.16b, v28.16b
     +0x380: eor     v0.16b, v0.16b, v24.16b
     +0x384: eor     v12.16b, v15.16b, v14.16b
     +0x388: orr     v13.16b, v13.16b, v29.16b
     +0x38c: eor     v0.16b, v0.16b, v25.16b
     +0x390: orr     v9.16b, v9.16b, v13.16b
     +0x394: orr     v13.16b, v8.16b, v12.16b
     +0x398: eor     v0.16b, v0.16b, v26.16b
     +0x39c: orr     v9.16b, v9.16b, v13.16b
     +0x3a0: eor     v0.16b, v0.16b, v27.16b
     +0x3a4: ext     v13.16b, v9.16b, v9.16b, #8
     +0x3a8: eor     v0.16b, v0.16b, v28.16b
     +0x3ac: eor     v0.16b, v0.16b, v29.16b
     +0x3b0: eor     v0.16b, v0.16b, v8.16b
     +0x3b4: eor     v30.16b, v10.16b, v30.16b
     +0x3b8: eor     v0.16b, v0.16b, v12.16b
     +0x3bc: orr     v31.8b, v9.8b, v13.8b
     +0x3c0: eor     v0.16b, v0.16b, v30.16b
     +0x3c4: fmov    x8, d31
     +0x3c8: ext     v1.16b, v0.16b, v0.16b, #8
     +0x3cc: orr     x8, x8, x8, lsr #32
     +0x3d0: lsr     x9, x8, #16
     +0x3d4: eor     v0.8b, v0.8b, v1.8b
     +0x3d8: orr     w8, w8, w9
     +0x3dc: fmov    x9, d0
     +0x3e0: orr     w8, w8, w8, lsr #8
     +0x3e4: sub     w8, w22, w8, uxtb
     +0x3e8: eor     x9, x9, x9, lsr #32
     +0x3ec: eor     x9, x9, x9, lsr #16
     +0x3f0: lsr     x10, x9, #8
     +0x3f4: eor     w9, w9, w10
     +0x3f8: eor     w8, w9, w8, lsr #16
     +0x3fc: ldr     q0, [x21, #1600]
     +0x400: ldr     q1, [x21, #1616]
     +0x404: eor     w21, w8, w9
     +0x408: stp     q0, q1, [sp]
     +0x40c: bl      <memcpy>
     +0x410: mov     x2, sp
     +0x414: mov     x0, x19
     +0x418: mov     w1, #0x20
     +0x41c: mov     w3, #0x320
     +0x420: bl      <mlkem_shake256>
     +0x424: mov     x8, xzr
     +0x428: sub     w9, w22, w21, uxtb
     +0x42c: ldrb    w10, [x19, x8]
     +0x430: mov     w11, w9
     +0x434: ldrb    w12, [x23, x8]
     +0x438: lsr     w11, w11, #16
     +0x43c: and     w10, w10, w11
     +0x440: bic     w12, w12, w11
     +0x444: orr     w10, w10, w12
     +0x448: strb    w10, [x19, x8]
     +0x44c: add     x8, x8, #0x1
     +0x450: cmp     x8, #0x20
     +0x454: b.ne    <mlkem512_dec+0x42c>
     +0x458: mov     w22, wzr
     +0x45c: mov     x0, sp
     +0x460: mov     w1, wzr
     +0x464: mov     w2, #0x320
     +0x468: mov     x19, sp
     +0x46c: bl      <memset>
     +0x470: movi    v0.2d, #0x0
     +0x474: add     x8, sp, #0x320
     +0x478: stp     q0, q0, [sp, #800]
     +0x47c: stp     q0, q0, [sp, #832]
     +0x480: stp     q0, q0, [sp, #896]
     +0x484: add     x8, sp, #0x360
     +0x488: stp     q0, q0, [sp, #864]
     +0x48c: adrp    x8, <page>
     +0x490: ldr     x8, [x8, #4088]
     +0x494: ldr     x9, [sp, #936]
     +0x498: ldr     x8, [x8]
     +0x49c: cmp     x8, x9
     +0x4a0: b.ne    <mlkem512_dec+0x4d4>
     +0x4a4: mov     w0, w22
     +0x4a8: sub     sp, x29, #0x40
     +0x4ac: ldp     x20, x19, [sp, #128]
     +0x4b0: ldp     x22, x21, [sp, #112]
     +0x4b4: ldp     x24, x23, [sp, #96]
     +0x4b8: ldp     x29, x30, [sp, #64]
     +0x4bc: ldp     d9, d8, [sp, #48]
     +0x4c0: ldp     d11, d10, [sp, #32]
     +0x4c4: ldp     d13, d12, [sp, #16]
     +0x4c8: ldr     x28, [sp, #80]
     +0x4cc: ldp     d15, d14, [sp], #144
     +0x4d0: ret
     +0x4d4: bl      <stack_chk_fail>
 ***)

let MLKEM_NATIVE_DEC_K2_CLANG17_O3_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_clang17_O3_mc
   [layout_range "plt_memcpy"; layout_range "plt_memset";
    layout_range "mlkem512_dec"];;

let KD2_EXEC = MLKEM_NATIVE_DEC_K2_CLANG17_O3_EXEC;;

(* ------------------------------------------------------------------------- *)
(* The lengths of the results of K-PKE for ML-KEM-512, the input check of    *)
(* FIPS 203 in terms of the result of mlkem512_check_sk, and the address of  *)
(* the buffers, which are aligned to 32 bytes within the stack frame.        *)
(* ------------------------------------------------------------------------- *)

let KPKE_ENCRYPT_LENGTH_512_STMT =
  `!ek m r. LENGTH(kpke_encrypt mlkem512 ek m r) = 768`;;

let KPKE_ENCRYPT_LENGTH_512 = assume_spec KPKE_ENCRYPT_LENGTH_512_STMT;;

let KPKE_DECRYPT_LENGTH_512_STMT =
  `!dk c. LENGTH(kpke_decrypt mlkem512 dk c) = 32`;;

let KPKE_DECRYPT_LENGTH_512 = assume_spec KPKE_DECRYPT_LENGTH_512_STMT;;

let KD2_CHECK_STMT =
  `!dk c. LENGTH dk = 1632 /\ LENGTH c = 768
          ==> (mlkem_decaps_check mlkem512 dk c <=>
               num_of_bytelist(mlkem_slice 1568 32 dk) =
               num_of_bytelist(sha3_256(mlkem_slice 768 800 dk)))`;;

let KD2_CHECK = assume_spec KD2_CHECK_STMT;;

let KD2_ALIGNED_16_32_STMT =
  `(!x:int64. aligned 16 x <=> word_and x (word 15) = word 0) /\
   (!x:int64. aligned 32 x <=> word_and x (word 31) = word 0)`;;

let KD2_ALIGNED_16_32 = assume_spec KD2_ALIGNED_16_32_STMT;;

let KD2_BUFFER_ADDRESS_STMT =
  `!sp:int64.
        aligned 16 sp
        ==> word_and (word_add sp (word 11808)) (word 18446744073709551584) =
            word_add sp (word(if aligned 32 sp then 11808 else 11792))`;;

let KD2_BUFFER_ADDRESS = assume_spec KD2_BUFFER_ADDRESS_STMT;;

let KD2_BUFFER_TAC =
  FIRST_ASSUM(fun th ->
    if concl th = `aligned 32 (stackpointer:int64)` ||
       concl th = `~aligned 32 (stackpointer:int64)`
    then SUBST_ALL_TAC
          (REWRITE_RULE[th; ASSUME `aligned 16 (stackpointer:int64)`]
            (SPEC `stackpointer:int64` KD2_BUFFER_ADDRESS))
    else NO_TAC);;

(* ------------------------------------------------------------------------- *)
(* The callees, the slices of the decapsulation key, and the failure of the  *)
(* check of the key, after which the function only zeroes its buffers.       *)
(* ------------------------------------------------------------------------- *)

let LOCAL_CHECK_SK_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_clang17_O3_mc,KD2_EXEC,
    0x0,mlkem_native_libmlkem_clang17_O3_mc,
    MLKEM_NATIVE_CHECK_SK_K2_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_INDCPA_DEC_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_clang17_O3_mc,KD2_EXEC,
    0x0,mlkem_native_libmlkem_clang17_O3_mc,
    MLKEM_NATIVE_INDCPA_DEC_K2_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_SHA3_512_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_clang17_O3_mc,KD2_EXEC,
    0x0,mlkem_native_libmlkem_clang17_O3_mc,
    MLKEM_NATIVE_SHA3_512_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_INDCPA_ENC_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_clang17_O3_mc,KD2_EXEC,
    0x0,mlkem_native_libmlkem_clang17_O3_mc,
    MLKEM_NATIVE_INDCPA_ENC_K2_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_SHAKE256_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_clang17_O3_mc,KD2_EXEC,
    0x0,mlkem_native_libmlkem_clang17_O3_mc,
    MLKEM_NATIVE_SHAKE256_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT);;

let KD2_SK_TAC =
  FIRST_ASSUM(fun th ->
    if can (term_match []
         `read (memory :> bytes(sk,1632)) s = num_of_bytelist dk`) (concl th)
    then
      let s = rand(lhand(concl th)) in
      MAP_EVERY (fun (k,n) ->
        MP_TAC(SPECL [`sk:int64`; `dk:byte list`; mk_small_numeral k;
                      mk_small_numeral n; s] READ_MEMORY_BYTES_SLICE) THEN
        ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
        REWRITE_TAC[WORD_ADD_0] THEN DISCH_TAC)
       [0,768; 768,800; 1568,32; 1600,32]
    else NO_TAC);;

let KD2_CHECK_TAC =
  LOCAL_CHECK_SK_TAC
   [`read X0 s`; `mlkem_slice 768 800 (dk:byte list)`;
    `num_of_bytelist(mlkem_slice 1568 32 (dk:byte list))`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 22;;

let KD2_DREG_STMT =
  `!x:int64. word_zx(word_zx x:int128):int64 = x`;;

let KD2_DREG = assume_spec KD2_DREG_STMT;;

let KD2_FAIL_TAC =
  ARM_STEPS_TAC KD2_EXEC (23--29) THEN LIBC_PLT_TAC KD2_EXEC 29 THEN
  LIBC_CALL_TAC "H_MEMSET" KD2_EXEC
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X30 s`] 34 THEN
  ARM_STEPS_TAC KD2_EXEC (35--42) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC KD2_EXEC (43--59) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[KD2_DREG];;

(* ------------------------------------------------------------------------- *)
(* The values computed: m', G of m' and h, K' and r', the reencryption c' of *)
(* m', z, the result of J, and whether c' is the ciphertext. The invariant   *)
(* of the comparison loop at iteration i states that the OR accumulator Q3   *)
(* is zero if and only if the first 16 * i bytes of the ciphertext and of c' *)
(* are equal, and the invariant of the conditional move at iteration i that  *)
(* the first i bytes at ss are those of K' if the ciphertexts are equal and  *)
(* those of the result of J otherwise, and the others still those of the     *)
(* result of J. The frame has the facts needed after both loops.             *)
(* ------------------------------------------------------------------------- *)

let KD2_MP = `kpke_decrypt mlkem512 (mlkem_slice 0 768 dk) c`;;

let KD2_GG =
 `sha3_512 (APPEND (kpke_decrypt mlkem512 (mlkem_slice 0 768 dk) c)
                  (mlkem_slice 1568 32 dk))`;;

let KD2_KP = mk_comb(`mlkem_slice 0 32`,KD2_GG);;

let KD2_RR = mk_comb(`mlkem_slice 32 32`,KD2_GG);;

let KD2_CP = list_mk_comb(`kpke_encrypt mlkem512`,
  [`mlkem_slice 768 800 (dk:byte list)`; KD2_MP; KD2_RR]);;

let KD2_ZZ = `mlkem_slice 1600 32 (dk:byte list)`;;

let KD2_KB = `list_of_seq (shake256 (APPEND (mlkem_slice 1600 32 dk) c)) 32`;;

let KD2_EQ = mk_eq(`num_of_bytelist c`,mk_comb(`num_of_bytelist`,KD2_CP));;

let KD2_SUBST tm =
  subst [mk_comb(`num_of_bytelist`,KD2_CP),`CP:num`;
         mk_comb(`num_of_bytelist`,KD2_KP),`KP:num`;
         mk_comb(`num_of_bytelist`,KD2_KB),`KB:num`;
         mk_comb(`num_of_bytelist`,KD2_ZZ),`ZZ:num`;
         KD2_EQ,`EQ:bool`] tm;;

let KD2_FRAME_FMT = Printf.sprintf
 "read SP s = word_add stackpointer (word %d) /\\
  read X29 s = word_add stackpointer (word 12816) /\\
  read X25 s = x25_init /\\ read X26 s = x26_init /\\
  read X27 s = x27_init /\\ read X28 s = x28_init /\\
  read (memory :> bytes64 (word_add stackpointer (word 12752))) s = d15_init /\\
  read (memory :> bytes64 (word_add stackpointer (word 12760))) s = d14_init /\\
  read (memory :> bytes64 (word_add stackpointer (word 12768))) s = d13_init /\\
  read (memory :> bytes64 (word_add stackpointer (word 12776))) s = d12_init /\\
  read (memory :> bytes64 (word_add stackpointer (word 12784))) s = d11_init /\\
  read (memory :> bytes64 (word_add stackpointer (word 12792))) s = d10_init /\\
  read (memory :> bytes64 (word_add stackpointer (word 12800))) s = d9_init /\\
  read (memory :> bytes64 (word_add stackpointer (word 12808))) s = d8_init /\\
  read (memory :> bytes64 (word_add stackpointer (word 12816))) s = x29_init /\\
  read (memory :> bytes64 (word_add stackpointer (word 12824))) s =
  returnaddress /\\
  read (memory :> bytes64 (word_add stackpointer (word 12832))) s = x28_init /\\
  read (memory :> bytes64 (word_add stackpointer (word 12848))) s = x24_init /\\
  read (memory :> bytes64 (word_add stackpointer (word 12856))) s = x23_init /\\
  read (memory :> bytes64 (word_add stackpointer (word 12864))) s = x22_init /\\
  read (memory :> bytes64 (word_add stackpointer (word 12872))) s = x21_init /\\
  read (memory :> bytes64 (word_add stackpointer (word 12880))) s = x20_init /\\
  read (memory :> bytes64 (word_add stackpointer (word 12888))) s = x19_init /\\
  read (memory :> bytes64 (word_add stackpointer (word %d))) s = canary /\\
  read (memory :> bytes64 (word_add (word pc) (word 196600))) s = guard /\\
  read (memory :> bytes64 guard) s = canary /\\
  read (memory :> bytes64 (word_add (word pc) (word 196584))) s = mf /\\
  read (memory :> bytes64 (word_add (word pc) (word 196560))) s = mc /\\
  read (memory :> bytes(ea,el)) s = ev";;

let KD2_FRAME b = KD2_SUBST(parse_term(
  KD2_FRAME_FMT b (b + 936) ^ " /\\
  read (memory :> bytes(word_add stackpointer (word " ^ string_of_int (b + 800) ^ "),32)) s = KP"));;

let KD2_CMOV_INV b = KD2_SUBST(parse_term(Printf.sprintf
 "\\i s. read X8 s = word i /\\
        read X9 s = (if EQ then word 0 else word 4294967041) /\\
        read X23 s = word_add stackpointer (word %d) /\\
        read X19 s = ss /\\
        read (memory :> bytes(ss,i)) s =
        (if EQ then KP else KB) MOD 2 EXP (8 * i) /\\
        read (memory :> bytes(word_add ss (word i),32 - i)) s =
        KB DIV 2 EXP (8 * i) /\\ FRAME"
  (b + 800)));;

let KD2_CMOV_INV_FRAME b =
  let inv = KD2_CMOV_INV b in
  let vs,bod = strip_abs inv in
  list_mk_abs(vs,subst [KD2_FRAME b,`FRAME:bool`] bod);;

(* ------------------------------------------------------------------------- *)
(* From the start to the comparison loop: the check of the key, the          *)
(* decryption, G of m' and h, and the reencryption.                          *)
(* ------------------------------------------------------------------------- *)

let KD2_G_INPUT_TAC b s =
  let st = mk_var(s,`:armstate`) in
  SUBGOAL_THEN
   (subst [st,`s:armstate`; KEM_SP(b + 864),`a:int64`;
           KD2_MP,`mm:byte list`]
     `read (memory :> bytes(a,64)) s =
      num_of_bytelist(APPEND (mm:byte list) (mlkem_slice 1568 32 dk))`)
  ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `64 = 32 + 32`; READ_COMPONENT_COMPOSE;
                READ_BYTES_COMBINE] THEN
    REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN
    CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
    ASM_REWRITE_TAC[FIPS203_NUM_OF_BYTELIST_APPEND; KPKE_DECRYPT_LENGTH_512];
    ALL_TAC] THEN
  SUBGOAL_THEN
   (subst [KD2_MP,`mm:byte list`]
     `LENGTH(APPEND (mm:byte list) (mlkem_slice 1568 32 dk)) = 64`)
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[LENGTH_APPEND; KPKE_DECRYPT_LENGTH_512] THEN ARITH_TAC;
    ALL_TAC];;

let KD2_KR_TAC b s =
  let st = mk_var(s,`:armstate`) and a = KEM_SP(b + 800) in
  FIRST_ASSUM(fun th ->
    if can (term_match [] (subst [a,`a:int64`; st,`s:armstate`]
         `read (memory :> bytes(a,64)) s = num_of_bytelist(sha3_512 x)`))
         (concl th)
    then
      MP_TAC(SPECL [a; KD2_GG; `0`; `32`; st] READ_MEMORY_BYTES_SLICE) THEN
      MP_TAC(SPECL [a; KD2_GG; `32`; `32`; st] READ_MEMORY_BYTES_SLICE) THEN
      ASM_REWRITE_TAC[LENGTH_SHA3_512] THEN CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC[WORD_ADD_0] THEN
      CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
      CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN
      REPEAT DISCH_TAC
    else NO_TAC) THEN
  SUBGOAL_THEN
   (mk_conj(mk_eq(mk_comb(`LENGTH:byte list->num`,KD2_KP),`32`),
            mk_eq(mk_comb(`LENGTH:byte list->num`,KD2_RR),`32`)))
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[mlkem_slice; LENGTH_LIST_OF_SEQ]; ALL_TAC];;

(* ------------------------------------------------------------------------- *)
(* One iteration of the comparison, with the loop test.                      *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* From the comparison loop to the conditional move: the result of the       *)
(* comparison as a mask of 0 or 255, J of z and the ciphertext copied after  *)
(* z with memcpy, and the mask for the bytes.                                *)
(* ------------------------------------------------------------------------- *)

let KD2_J_INPUT_TAC b s =
  let st = mk_var(s,`:armstate`) in
  SUBGOAL_THEN
   (subst [st,`s:armstate`; KEM_SP b,`a:int64`]
     `read (memory :> bytes(a,800)) s =
      num_of_bytelist(APPEND (mlkem_slice 1600 32 (dk:byte list)) c)`)
  ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `800 = 32 + 768`; READ_COMPONENT_COMPOSE;
                READ_BYTES_COMBINE] THEN
    REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN
    CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
    ASM_REWRITE_TAC[FIPS203_NUM_OF_BYTELIST_APPEND];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `LENGTH(APPEND (mlkem_slice 1600 32 (dk:byte list)) c) = 800`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[LENGTH_APPEND] THEN ARITH_TAC; ALL_TAC];;

(* ------------------------------------------------------------------------- *)
(* The comparison is straight-line code: the 48 blocks of 16 bytes of the    *)
(* ciphertext and of c' are the 128-bit words at the addresses of the loads, *)
(* and the OR of their XORs is zero if and only if all of them agree.        *)
(* ------------------------------------------------------------------------- *)

let KD2_MOD_ALL_STMT =
 `!n m k. n MOD 2 EXP (128 * k) = m MOD 2 EXP (128 * k) <=>
          !j. j < k ==> (n DIV 2 EXP (128 * j)) MOD 2 EXP 128 =
                        (m DIV 2 EXP (128 * j)) MOD 2 EXP 128`;;

let KD2_MOD_ALL = assume_spec KD2_MOD_ALL_STMT;;

let KD2_CHUNK_TAC norm a v k =
  FIRST_ASSUM(fun th ->
    match concl th with
      Comb(Comb(Const("=",_),
                Comb(Comb(Const("read",_),Comb(_,Comb(Const("bytes",_),aa))),
                     s)),vv)
        when aa = mk_pair(a,`768`) && vv = v ->
          let kt = mk_small_numeral k in
          let bth = EQT_ELIM(NUM_REDUCE_CONV (subst [kt,`k:num`]
                      `16 * k + 16 <= 768`)) in
          let lth = SPECL [a; `768`; kt; v; s] KEM_BYTES128 in
          let fth = MP lth (CONJ th bth) in
          let fth = CONV_RULE (DEPTH_CONV NUM_MULT_CONV) fth in
          let fth = REWRITE_RULE[WORD_ADD_0] fth in
          ASSUME_TAC(if norm then CONV_RULE(ONCE_DEPTH_CONV
                                    NORMALIZE_RELATIVE_ADDRESS_CONV) fth
                     else fth)
    | _ -> NO_TAC);;

let KD2_EXP_THS =
  NUM_REDUCE_CONV `2 EXP 128` ::
  map (fun k -> NUM_REDUCE_CONV (subst [mk_small_numeral k,`k:num`]
                                  `2 EXP (128 * k)`)) (0--47);;

(*** An accumulator after the code that computes it, as a variable ***)

let KD2_ABBREV_TAC reg nm var =
  W(fun (asl,w) ->
    let big = rhs(concl(snd(find (fun (_,th) ->
      let c = concl th in
      is_eq c &&
      (let l = lhs c in
       (try fst(dest_const(rator(rator l))) = "read" with Failure _ -> false) &&
       rand(rator l) = reg && rand l = mk_var(nm,`:armstate`))) asl))) in
    ABBREV_TAC(mk_eq(mk_var(var,`:int128`),big)));;

(*** The OR accumulator is zero if and only if the 48 blocks agree ***)

let KD2_CHUNK_IFF_TAC =
  REWRITE_TAC[KD2_MOD_ALL] THEN
  CONV_TAC(RAND_CONV EXPAND_CASES_CONV) THEN
  REWRITE_TAC[WORD_OR_EQ_0; WORD_XOR_EQ_0] THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD; DIMINDEX_128] THEN
  REWRITE_TAC KD2_EXP_THS THEN
  REWRITE_TAC[MOD_MOD_REFL] THEN
  EQ_TAC THEN DISCH_THEN(fun th ->
    let ths = CONJUNCTS th in
    REPEAT CONJ_TAC THEN FIRST (map ACCEPT_TAC ths));;

let KD2_IFF_TAC =
  SUBGOAL_THEN
   (mk_iff(`q9:int128 = word 0`,
    `num_of_bytelist c MOD 2 EXP (128 * 48) =
     num_of_bytelist(kpke_encrypt mlkem512 (mlkem_slice 768 800 (dk:byte list))
                      (kpke_decrypt mlkem512 (mlkem_slice 0 768 dk) c)
                      (mlkem_slice 32 32
                        (sha3_512 (APPEND (kpke_decrypt mlkem512
                                            (mlkem_slice 0 768 dk) c)
                                          (mlkem_slice 1568 32 dk))))) MOD
     2 EXP (128 * 48)`)) ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th ->
      if is_eq(concl th) && rand(concl th) = `q9:int128`
      then SUBST1_TAC(SYM th) else NO_TAC) THEN
    KD2_CHUNK_IFF_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN (mk_iff(`q9:int128 = word 0`,KD2_EQ)) ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th ->
      if is_iff(concl th) && lhand(concl th) = `q9:int128 = word 0`
      then REWRITE_TAC[th] else NO_TAC) THEN
    MP_TAC(ISPEC `c:byte list` NUM_OF_BYTELIST_BOUND) THEN
    MP_TAC(ISPEC KD2_CP NUM_OF_BYTELIST_BOUND) THEN
    ASM_REWRITE_TAC[KPKE_ENCRYPT_LENGTH_512] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[MOD_LT];
    ALL_TAC];;

(*** The big terms of the accumulators and the 128-bit words are not
     needed once the facts about the accumulators are derived ***)

let KD2_CLEAN_TAC =
  DISCARD_ASSUMPTIONS_TAC(fun th ->
    let c = concl th in
    (is_eq c && (rand c = `q9:int128` || rand c = `q0:int128`) &&
     not(is_var(lhand c)) &&
     not(try fst(dest_const(rator(rator(lhand c)))) = "read"
         with Failure _ -> false)) ||
    (is_iff c && lhand c = `q9:int128 = word 0` &&
     not(is_eq(rand c) && lhand(rand c) = `num_of_bytelist c`)) ||
    (can (term_match [] `read (memory :> bytes128 a) s = x`) c &&
     not(free_in `sk:int64` c)));;

let KD2_MASK_TAC s =
  let x21 = mk_comb(`read X21`,mk_var(s,`:armstate`)) in
  FIRST_X_ASSUM(fun th ->
    let c = concl th in
    if is_eq c && lhand c = x21 then
      let e = rand c in
      let eth = BITBLAST_RULE
        (mk_eq(e,`if q9:int128 = word 0 then word 0:int64 else word 65535`)) in
      ASSUME_TAC(TRANS th eth)
    else NO_TAC) THEN
  FIRST_X_ASSUM(fun th ->
    let c = concl th in
    if is_eq c && lhand c = x21 then
      FIRST_ASSUM(fun th' ->
        if is_iff(concl th') &&
           lhand(concl th') = `q9:int128 = word 0` &&
           rand(concl th') = KD2_EQ
        then ASSUME_TAC(REWRITE_RULE[th'] th) else NO_TAC)
    else NO_TAC);;

let KD2_PART_A_TAC b =
  let st n = "s"^string_of_int n in
  ENSURES_INIT_TAC "s0" THEN KD2_SK_TAC THEN
  KEM_HALVES_TAC `word_add sk (word 1568):int64` THEN
  KEM_HALVES_TAC `word_add sk (word 1600):int64` THEN
  ARM_STEPS_TAC KD2_EXEC (1--12) THEN KD2_BUFFER_TAC THEN
  ARM_STEPS_TAC KD2_EXEC (13--13) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC KD2_EXEC (14--21) THEN KEM_GOT_TAC THEN
  KD2_CHECK_TAC THEN

  (*** The decryption, G and the reencryption ***)

  ARM_STEPS_TAC KD2_EXEC (23--28) THEN KEM_GOT_TAC THEN
  LOCAL_INDCPA_DEC_TAC
   [`read X0 s`; `read X1 s`; `read X2 s`;
    `mlkem_slice 0 768 (dk:byte list)`; `c:byte list`; `guard:int64`;
    `mf:int64`; `ea:int64`; `el:num`; `ev:num`; `pc:num`; `read SP s`;
    `read X30 s`] 29 THEN
  ARM_STEPS_TAC KD2_EXEC (30--40) THEN
  KEM_JOIN_TAC (KEM_SP(b + 896)) `mlkem_slice 1568 32 (dk:byte list)`
    (st 40) THEN
  KD2_G_INPUT_TAC b (st 40) THEN KEM_GOT_TAC THEN
  LOCAL_SHA3_512_TAC
   [`read X0 s`; `read X1 s`;
    mk_comb(mk_comb(`APPEND:byte list->byte list->byte list`,KD2_MP),
            `mlkem_slice 1568 32 (dk:byte list)`);
    `guard:int64`; `pc:num`; `read SP s`; `read X30 s`] 41 THEN
  KD2_KR_TAC b (st 41) THEN
  ARM_STEPS_TAC KD2_EXEC (42--47) THEN KEM_GOT_TAC THEN
  SUBGOAL_THEN (mk_eq(mk_comb(`LENGTH:byte list->num`,KD2_MP),`32`))
  ASSUME_TAC THENL [REWRITE_TAC[KPKE_DECRYPT_LENGTH_512]; ALL_TAC] THEN
  LOCAL_INDCPA_ENC_TAC
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X3 s`;
    `mlkem_slice 768 800 (dk:byte list)`; KD2_MP; KD2_RR;
    `guard:int64`; `mf:int64`; `mc:int64`; `ea:int64`; `el:num`; `ev:num`;
    `pc:num`; `read SP s`; `read X30 s`] 48 THEN
  ARM_STEPS_TAC KD2_EXEC (49--50) THEN

  (*** The comparison: 48 blocks of the ciphertext and of c' ***)

  MAP_EVERY (fun k ->
    KD2_CHUNK_TAC false `ct:int64` `num_of_bytelist(c:byte list)` k) (0--47) THEN
  MAP_EVERY (fun k ->
    KD2_CHUNK_TAC true (KEM_SP b) (mk_comb(`num_of_bytelist`,KD2_CP)) k)
   (0--47) THEN
  MAP_EVERY (fun k ->
    ARM_STEPS_TAC KD2_EXEC [k] THEN SIMD_SIMPLIFY_TAC[]) (51--236) THEN
  KD2_ABBREV_TAC `Q9` "s236" "q9" THEN
  KD2_IFF_TAC THEN
  KD2_CLEAN_TAC THEN
  MAP_EVERY (fun k ->
    ARM_STEPS_TAC KD2_EXEC [k] THEN SIMD_SIMPLIFY_TAC[]) (237--245) THEN
  KD2_ABBREV_TAC `Q0` "s245" "q0" THEN
  KD2_CLEAN_TAC THEN
  MAP_EVERY (fun k ->
    ARM_STEPS_TAC KD2_EXEC [k] THEN SIMD_SIMPLIFY_TAC[]) (246--262) THEN
  KD2_MASK_TAC (st 262) THEN
  ARM_STEPS_TAC KD2_EXEC (263--264) THEN
  KEM_JOIN_TAC (KEM_SP b) KD2_ZZ (st 264) THEN
  LIBC_PLT_TAC KD2_EXEC 264 THEN
  LIBC_CALL_TAC "H_MEMCPY" KD2_EXEC
   [`read X0 s`; `read X1 s`; `read X2 s`; `num_of_bytelist(c:byte list)`;
    `read X30 s`] 269 THEN
  KD2_J_INPUT_TAC b (st 269) THEN
  ARM_STEPS_TAC KD2_EXEC (270--274) THEN KEM_GOT_TAC THEN
  LOCAL_SHAKE256_TAC
   [`read X0 s`; `32`; `read X2 s`;
    `APPEND (mlkem_slice 1600 32 (dk:byte list)) c`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 275 THEN
  ARM_STEPS_TAC KD2_EXEC (276--277) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[MULT_CLAUSES; EXP; MOD_1; DIV_1; SUB_0; WORD_ADD_0;
              READ_MEMORY_BYTES_TRIVIAL] THEN
  ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC KD2_EQ THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(NUM_REDUCE_CONV THENC WORD_REDUCE_CONV);;

(* ------------------------------------------------------------------------- *)
(* One iteration of the conditional move, and the end: the zeroing of the    *)
(* buffers, the stack guard and the result in terms of FIPS 203.             *)
(* ------------------------------------------------------------------------- *)

let KD2_CMOV_TEST_STMT =
  `!i. i < 32
       ==> (val(word_add (word i) (word 18446744073709551585):int64) = 0 <=>
            ~(i + 1 < 32))`;;

let KD2_CMOV_TEST = assume_spec KD2_CMOV_TEST_STMT;;

let KD2_CMOV_BODY_TAC b =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
  MP_TAC(SPECL [KEM_SP(b + 800); `32`; mk_comb(`num_of_bytelist`,KD2_KP);
                `i:num`; `s0:armstate`] READ_MEMORY_BYTES8_OF_NUM) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(ASSUME_TAC o REWRITE_RULE[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD]) THEN
  SUBGOAL_THEN
   (KD2_SUBST `read (memory :> bytes(word_add ss (word i),(31 - i) + 1)) s0 =
               KB DIV 2 EXP (8 * i)`)
  MP_TAC THENL
   [SIMP_TAC[ARITH_RULE `i < 32 ==> (31 - i) + 1 = 32 - i`;
             ASSUME `i < 32`] THEN ASM_REWRITE_TAC[];
    DISCH_THEN(fun th ->
      let th1,th2 = CONJ_PAIR(MATCH_MP KEM_SPLIT1 th) in
      ASSUME_TAC th1 THEN ASSUME_TAC th2)] THEN
  ARM_STEPS_TAC KD2_EXEC (1--11) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [MP (SPEC `i:num` KD2_CMOV_TEST) (ASSUME `i < 32`)]) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [ASM_CASES_TAC `i + 1 < 32` THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[GSYM WORD_ADD];
    REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE] THEN
    REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE; READ_MEMORY_BYTES_1] THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[KEM_MOD_BYTE] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN
    ASM_CASES_TAC KD2_EQ THEN ASM_REWRITE_TAC[] THEN
    GEN_REWRITE_TAC RAND_CONV [KEM_VAL_BYTE] THEN
    SPEC_TAC(KD2_SUBST `word((KP DIV 2 EXP (8 * i)) MOD 256):byte`,
             `x:byte`) THEN
    SPEC_TAC(KD2_SUBST `word((KB DIV 2 EXP (8 * i)) MOD 256):byte`,
             `y:byte`) THEN
    REPEAT GEN_TAC THEN AP_TERM_TAC THEN BITBLAST_TAC;
    REWRITE_TAC[ARITH_RULE `32 - (i + 1) = 31 - i`; WORD_ADD; WORD_ADD_ASSOC;
                KEM_DIV_BYTE] THEN
    ASM_REWRITE_TAC[]];;

let KD2_FINAL_TAC =
  REWRITE_TAC[mlkem512; MLKEM_DECAPS_ALT] THEN REWRITE_TAC[GSYM mlkem512] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN (mk_iff(mk_eq(KD2_CP,`c:byte list`),KD2_EQ)) SUBST1_TAC THENL
   [CONV_TAC(LAND_CONV SYM_CONV) THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC NUM_OF_BYTELIST_INJ THEN
    ASM_REWRITE_TAC[KPKE_ENCRYPT_LENGTH_512];
    ALL_TAC] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOD_LT THEN
  W(fun (_,w) -> MP_TAC(ISPEC (rand(lhand w)) NUM_OF_BYTELIST_BOUND)) THEN
  REWRITE_TAC[mlkem_slice; LENGTH_LIST_OF_SEQ] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];;

let KD2_EXIT_B_TAC =
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC KD2_EXEC (1--6) THEN
  LIBC_PLT_TAC KD2_EXEC 6 THEN
  LIBC_CALL_TAC "H_MEMSET" KD2_EXEC
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X30 s`] 11 THEN
  ARM_STEPS_TAC KD2_EXEC (12--19) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC KD2_EXEC (20--36) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[KD2_DREG] THEN KD2_FINAL_TAC;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof, assuming the contracts for memset and memcpy. The      *)
(* decapsulation key dk of 1632 bytes is at sk and the ciphertext c of 768  *)
(* bytes at ct, and if they pass the check of FIPS 203, the shared secret of *)
(* 32 bytes written at ss is that of mlkem_decaps_internal mlkem512 dk c in  *)
(* common/fips203/fips203.ml and the function returns 0, and otherwise it    *)
(* returns -5. The theorem assumes that SampleNTT terminates for each entry  *)
(* of the matrix from the seed in the key and that the stack does not        *)
(* contain address 0, for mlkem512_indcpa_enc. The stack is the 64 bytes of  *)
(* saved registers, the buffers of 1280 bytes aligned to 32 bytes below them *)
(* (with up to 16 bytes of padding) and the 11792 used by                    *)
(* mlkem512_indcpa_enc below the buffers. The proof is by cases on whether   *)
(* the stack pointer is a multiple of 32, which gives the address b of the   *)
(* buffers, at offsets 0 (c' and then z and the ciphertext), 800 (K' and    *)
(* r') and 800 (m' and h), and on the check of the key.                     *)
(* ------------------------------------------------------------------------- *)

let KD2_INTRO_TAC =
  MAP_EVERY X_GEN_TAC
   [`ss:int64`; `ct:int64`; `sk:int64`; `dk:byte list`; `c:byte list`;
    `guard:int64`; `mf:int64`; `mc:int64`; `ea:int64`; `el:num`; `ev:num`;
    `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 12896 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE] THEN
  REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NONOVERLAPPING_CLAUSES]) THEN
  SUBGOAL_THEN `aligned 16 (stackpointer:int64)` ASSUME_TAC THENL
   [UNDISCH_TAC `aligned 16 (word_add stackpointer (word 12896):int64)` THEN
    CONV_TAC(LAND_CONV NORMALIZE_ALIGNED_WORD_CONV) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  SIMP_TAC[KD2_CHECK; ASSUME `LENGTH(dk:byte list) = 1632`;
           ASSUME `LENGTH(c:byte list) = 768`] THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_stack_chk_guard:num`] WORD_ADD;
              SPECL [`pc:num`; `got_memset:num`] WORD_ADD;
              SPECL [`pc:num`; `got_memcpy:num`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`;
                                     `got_stack_chk_guard:num`] WORD_ADD;
                              SPECL [`pc:num`; `got_memset:num`] WORD_ADD;
                              SPECL [`pc:num`;
                                     `got_memcpy:num`] WORD_ADD]) THEN
  GHOST_INTRO_TAC `canary:int64` `read (memory :> bytes64 guard)` THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  MAP_EVERY (fun n ->
    ENSURES_PRESERVED_TAC ("x"^string_of_int n^"_init")
     (parse_term("X"^string_of_int n))) (19--29) THEN
  MAP_EVERY (fun (n,d) -> ENSURES_PRESERVED_DREG_TAC n d)
   [("d8_init",`D8`); ("d9_init",`D9`); ("d10_init",`D10`);
    ("d11_init",`D11`); ("d12_init",`D12`); ("d13_init",`D13`);
    ("d14_init",`D14`); ("d15_init",`D15`)] THEN
  SUBGOAL_THEN
   `LENGTH(mlkem_slice 0 768 (dk:byte list)) = 768 /\
    LENGTH(mlkem_slice 768 800 (dk:byte list)) = 800 /\
    LENGTH(mlkem_slice 1568 32 (dk:byte list)) = 32 /\
    LENGTH(mlkem_slice 1600 32 (dk:byte list)) = 32`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[mlkem_slice; LENGTH_LIST_OF_SEQ]; ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o REWRITE_RULE
   [SYM(CONV_RULE NUM_REDUCE_CONV
     (MP (SPECL [`768`; `32`; `768`; `800`; `dk:byte list`]
                MLKEM_SLICE_SLICE)
         (ARITH_RULE `768 + 32 <= 800`)))] o
   check (fun th -> is_forall(concl th) &&
                    KEM_HAS_CONST "mlkem_samplentt_terminates"
                     (concl th)));;

let KD2_OK_TAC b =
  ENSURES_WHILE_UP2_TAC `32` `pc + mlkem512_dec_loop1`
   `pc + mlkem512_dec_loop1_exit`
   (KD2_CMOV_INV_FRAME b) THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC; KD2_PART_A_TAC b; KD2_CMOV_BODY_TAC b; KD2_EXIT_B_TAC];;

let KD2_BAD_TAC =
  ENSURES_INIT_TAC "s0" THEN KD2_SK_TAC THEN
  ARM_STEPS_TAC KD2_EXEC (1--12) THEN KD2_BUFFER_TAC THEN
  ARM_STEPS_TAC KD2_EXEC (13--13) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC KD2_EXEC (14--21) THEN KEM_GOT_TAC THEN
  KD2_CHECK_TAC THEN KD2_FAIL_TAC;;

let KD2_CASE_TAC b =
  KEM_LABELS_TAC THEN
  ASM_CASES_TAC
   `num_of_bytelist(mlkem_slice 1568 32 (dk:byte list)) =
    num_of_bytelist(sha3_256(mlkem_slice 768 800 dk))` THEN
  ASM_REWRITE_TAC[] THENL [KD2_OK_TAC b; KD2_BAD_TAC];;

let MLKEM_NATIVE_DEC_K2_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!ss ct sk (dk:byte list) (c:byte list) guard mf mc ea el ev pc
    stackpointer returnaddress.
        memset_contract mf ea el ev /\ memcpy_contract mc ea el ev /\
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\ LENGTH dk = 1632 /\ LENGTH c = 768 /\
        (!i j. i < 2 /\ j < 2
               ==> mlkem_samplentt_terminates
                    (APPEND (mlkem_slice 1536 32 dk) [word j; word i])) /\
        nonoverlapping (ct,768) (word pc,libmlkem_size) /\
        nonoverlapping (sk,1632) (word pc,libmlkem_size) /\
        nonoverlapping (ss,32) (word_sub stackpointer (word 12896),12896) /\
        ALLPAIRS nonoverlapping
         [(ss,32); (word_sub stackpointer (word 12896),12896)]
         [(ct,768); (sk,1632); (word pc,libmlkem_size);
          (word(pc + got_stack_chk_guard),8);
          (guard,8); (word(pc + got_memset),8); (word(pc + got_memcpy),8);
          (ea,el)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_clang17_O3_mc /\
                  read PC s = word (pc + mlkem512_dec) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [ss; ct; sk] s /\
                  read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                    guard /\
                  read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                  read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                  read (memory :> bytes(ea,el)) s = ev /\
                  read (memory :> bytes(ct,768)) s = num_of_bytelist c /\
                  read (memory :> bytes(sk,1632)) s = num_of_bytelist dk)
             (\s. read PC s = returnaddress /\
                  (mlkem_decaps_check mlkem512 dk c
                   ==> read (memory :> bytes(ss,32)) s =
                       num_of_bytelist(mlkem_decaps_internal mlkem512 dk c)) /\
                  C_RETURN s =
                  (if mlkem_decaps_check mlkem512 dk c then word 0
                   else word 0xfffffffb))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
              MAYCHANGE
               [memory :> bytes(ss,32);
                memory :> bytes(word_sub stackpointer (word 12896),12896)])`;;

let MLKEM_NATIVE_DEC_K2_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_DEC_K2_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof, assuming the combined contract for *)
(* memset (for mlkem512_indcpa_enc) and the safety contract for memcpy. The  *)
(* events depend only on the addresses and on the encapsulation key ek in    *)
(* the decapsulation key and the hash h stored with it, through the check of *)
(* the hash, given by the combined theorem for mlkem512_check_sk, and the    *)
(* reencryption, but not on the secret key, z or the ciphertext: the         *)
(* comparison of the ciphertexts and the selection of the shared secret are  *)
(* loops in constant time. The buffers are kept at their offset from the     *)
(* stack pointer as a conditional, and the invariants of the loops have only *)
(* the pointers and the frame.                                               *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let KD2_SAFE_TEMPLATE =
 `\(ss:int64) (ct:int64) (sk:int64) (guard:int64) (mf:int64) (mc:int64)
   (pc:num) (sp:int64) (ra:int64) (ek:byte list) (h:byte list).
   if aligned 32 sp
   then (if num_of_bytelist h = num_of_bytelist(sha3_256 ek)
         then APPEND (f_ev_exitb_a ss ct sk guard mf mc pc sp ra)
               (APPEND (ENUMERATEL 32
                         (\i. f_ev_cmov_a ss ct sk guard mf mc pc sp ra i))
                       (f_ev_prol_a ss ct sk guard mf mc pc sp ra ek h))
         else f_ev_bad_a ss ct sk guard mf mc pc sp ra ek h)
   else (if num_of_bytelist h = num_of_bytelist(sha3_256 ek)
         then APPEND (f_ev_exitb_u ss ct sk guard mf mc pc sp ra)
               (APPEND (ENUMERATEL 32
                         (\i. f_ev_cmov_u ss ct sk guard mf mc pc sp ra i))
                       (f_ev_prol_u ss ct sk guard mf mc pc sp ra ek h))
         else f_ev_bad_u ss ct sk guard mf mc pc sp ra ek h)
   :(uarch_event)list`;;

let KD2_SAFE_ALLOWED =
  [`pc:num`; `ss:int64`; `ct:int64`; `sk:int64`; `guard:int64`;
   `mf:int64`; `mc:int64`; `stackpointer:int64`; `returnaddress:int64`;
   `ekk:byte list`; `hh:byte list`; `i:num`;
   `f_ev_cmov_a:int64->int64->int64->int64->int64->int64->num->int64->
                 int64->num->(uarch_event)list`;
   `f_ev_cmov_u:int64->int64->int64->int64->int64->int64->num->int64->
                 int64->num->(uarch_event)list`];;

let KD2_EV_CONV =
  REWRITE_CONV[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD; GSYM ADD_ASSOC] THENC
  DEPTH_CONV NUM_ADD_CONV;;

let KD2_SAFE_NORMALIZE_TAC =
  RULE_ASSUM_TAC(fun th ->
    if free_in `stackpointer:int64` (concl th)
    then CONV_RULE KD2_EV_CONV th else th);;

(*** The events of the goal are normalized in the same way as those of the
     assumptions before the events of the loop are unified. ***)

let KD2_DISCHARGE_EXIT_TAC =
  SAFE_META_EXISTS_TAC allowed_vars_e THEN
  CONJ_TAC THENL [EXISTS_E2_TAC allowed_vars_e; ALL_TAC] THEN
  CONJ_TAC THENL
   [CONV_TAC(RAND_CONV KD2_EV_CONV) THEN FULL_UNIFY_F_EVENTS_TAC;
    ALL_TAC] THEN
  DISCHARGE_MEMACCESS_INBOUNDS_TAC;;

let KD2_SAFE_CALL_TAC name ilist n =
  KD2_SAFE_NORMALIZE_TAC THEN
  REMOVE_THEN name (fun safety_th ->
    ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_clang17_O3_mc,KD2_EXEC,
       0x0,mlkem_native_libmlkem_clang17_O3_mc,safety_th)
      ilist n THENL
     [EXISTS_E2_TAC (ref KD2_SAFE_ALLOWED); LABEL_TAC name safety_th]);;

let KD2_SAFE_FRAME b = parse_term(KD2_FRAME_FMT b (b + 936));;

let KD2_SAFE_WITH_FRAME b inv =
  let vs,bod = strip_abs inv in
  list_mk_abs(vs,subst [KD2_SAFE_FRAME b,`FRAME:bool`] bod);;

let KD2_SAFE_CMOV_INV b = KD2_SAFE_WITH_FRAME b (parse_term(Printf.sprintf
 "\\i s. read X8 s = word i /\\
        read X23 s = word_add stackpointer (word %d) /\\
        read X19 s = ss /\\ FRAME" (b + 800)));;

let KD2_SAFE_INTRO_TAC =
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
  FIRST_X_ASSUM(fun th1 ->
    if can (term_match [] `memset_full_contract mf ea el ev`) (concl th1)
    then FIRST_X_ASSUM(fun th2 ->
      let sth = CONJUNCT2(MATCH_MP MEMSET_FULL_CONTRACT th1) in
      ASSUME_CALLEE_SAFETY_TAILED_TAC
       (MATCH_MP MLKEM_NATIVE_INDCPA_ENC_K2_CLANG17_O3_IMAGE_SUBROUTINE_SAFE
                 (CONJ th1 th2)) "H_ENC" THEN
      ASSUME_CALLEE_SAFETY_TAILED_TAC
       (MATCH_MP
         MLKEM_NATIVE_INDCPA_DEC_K2_CLANG17_O3_IMAGE_SUBROUTINE_SAFE
         sth) "H_DEC" THEN
      ASSUME_CALLEE_SAFETY_TAILED_TAC
       (REWRITE_RULE[memset_safety_contract] sth) "H_MEMSET" THEN
      ASSUME_CALLEE_SAFETY_TAILED_TAC
       (REWRITE_RULE[memcpy_safety_contract] th2) "H_MEMCPY")
    else NO_TAC) THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_CHECK_SK_K2_CLANG17_O3_IMAGE_SUBROUTINE_FULL "H_CHECK" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_SHA3_512_CLANG17_O3_IMAGE_SUBROUTINE_SAFE "H_SHA3_512" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_SHAKE256_CLANG17_O3_IMAGE_SUBROUTINE_SAFE "H_SHAKE256" THEN
  CONCRETIZE_F_EVENTS_TAC KD2_SAFE_TEMPLATE THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NONOVERLAPPING_CLAUSES]) THEN
  SUBGOAL_THEN `aligned 16 (stackpointer:int64)` ASSUME_TAC THENL
   [UNDISCH_TAC `aligned 16 (word_add stackpointer (word 12896):int64)` THEN
    CONV_TAC(LAND_CONV NORMALIZE_ALIGNED_WORD_CONV) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_stack_chk_guard:num`] WORD_ADD;
              SPECL [`pc:num`; `got_memset:num`] WORD_ADD;
              SPECL [`pc:num`; `got_memcpy:num`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`;
                                     `got_stack_chk_guard:num`] WORD_ADD;
                              SPECL [`pc:num`; `got_memset:num`] WORD_ADD;
                              SPECL [`pc:num`;
                                     `got_memcpy:num`] WORD_ADD]) THEN
  GHOST_INTRO_TAC `canary:int64` `read (memory :> bytes64 guard)` THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  MAP_EVERY (fun n ->
    ENSURES_PRESERVED_TAC ("x"^string_of_int n^"_init")
     (parse_term("X"^string_of_int n))) (19--29) THEN
  MAP_EVERY (fun (n,d) -> ENSURES_PRESERVED_DREG_TAC n d)
   [("d8_init",`D8`); ("d9_init",`D9`); ("d10_init",`D10`);
    ("d11_init",`D11`); ("d12_init",`D12`); ("d13_init",`D13`);
    ("d14_init",`D14`); ("d15_init",`D15`)] THEN
  SUBGOAL_THEN
   `LENGTH(mlkem_slice 0 768 (dk:byte list)) = 768 /\
    LENGTH(mlkem_slice 768 800 (dk:byte list)) = 800 /\
    LENGTH(mlkem_slice 1568 32 (dk:byte list)) = 32 /\
    LENGTH(mlkem_slice 1600 32 (dk:byte list)) = 32`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[mlkem_slice; LENGTH_LIST_OF_SEQ]; ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o REWRITE_RULE
   [SYM(CONV_RULE NUM_REDUCE_CONV
     (MP (SPECL [`768`; `32`; `768`; `800`; `dk:byte list`]
                MLKEM_SLICE_SLICE)
         (ARITH_RULE `768 + 32 <= 800`)))] o
   check (fun th -> is_forall(concl th) &&
                    KEM_HAS_CONST "mlkem_samplentt_terminates"
                     (concl th))) THEN
  ABBREV_TAC `ekk = mlkem_slice 768 800 (dk:byte list)` THEN
  ABBREV_TAC `hh = mlkem_slice 1568 32 (dk:byte list)`;;

let KD2_SAFE_START_TAC =
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  KD2_SK_TAC THEN
  ARM_STEPS_TAC KD2_EXEC (1--12) THEN KD2_BUFFER_TAC THEN
  ARM_STEPS_TAC KD2_EXEC (13--13) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC KD2_EXEC (14--21) THEN KEM_GOT_TAC THEN
  KD2_SAFE_CALL_TAC "H_CHECK"
   [`e:(uarch_event)list`; `read X0 s`; `ekk:byte list`;
    `num_of_bytelist(hh:byte list)`; `guard:int64`; `pc:num`; `read SP s`;
    `read X30 s`] 22;;

let KD2_SAFE_PART_A_TAC =
  KD2_SAFE_START_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[EQT_INTRO(ASSUME
   `num_of_bytelist(hh:byte list) = num_of_bytelist(sha3_256 ekk)`)]) THEN
  ARM_STEPS_TAC KD2_EXEC (23--28) THEN KEM_GOT_TAC THEN
  KD2_SAFE_CALL_TAC "H_DEC"
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`;
    `guard:int64`; `pc:num`; `read SP s`; `read X30 s`] 29 THEN
  ARM_STEPS_TAC KD2_EXEC (30--40) THEN KEM_GOT_TAC THEN
  KD2_SAFE_CALL_TAC "H_SHA3_512"
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `64`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 41 THEN
  ARM_STEPS_TAC KD2_EXEC (42--47) THEN KEM_GOT_TAC THEN
  KD2_SAFE_CALL_TAC "H_ENC"
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`;
    `read X3 s`; `ekk:byte list`; `guard:int64`; `pc:num`; `read SP s`;
    `read X30 s`] 48 THEN
  MAP_EVERY (fun k ->
    ARM_STEPS_TAC KD2_EXEC [k] THEN SIMD_SIMPLIFY_TAC[]) (49--264) THEN
  LIBC_PLT_TAC KD2_EXEC 264 THEN
  KD2_SAFE_NORMALIZE_TAC THEN LIBC_SAFE_CALL_TAC "H_MEMCPY" KD2_EXEC
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`;
    `read X30 s`] (ref KD2_SAFE_ALLOWED) 269 THEN
  ARM_STEPS_TAC KD2_EXEC (270--274) THEN KEM_GOT_TAC THEN
  KD2_SAFE_CALL_TAC "H_SHAKE256"
   [`e:(uarch_event)list`; `read X0 s`; `32`; `read X2 s`; `800`;
    `guard:int64`; `pc:num`; `read SP s`; `read X30 s`] 275 THEN
  ARM_STEPS_TAC KD2_EXEC (276--277) THEN
  KD2_SAFE_NORMALIZE_TAC THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  KD2_DISCHARGE_EXIT_TAC;;

let KD2_SAFE_CMOV_BODY_TAC =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  ARM_STEPS_TAC KD2_EXEC (1--11) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [MP (SPEC `i:num` KD2_CMOV_TEST) (ASSUME `i < 32`)]) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL [REWRITE_TAC[GSYM WORD_ADD]; ALL_TAC] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let KD2_SAFE_EXIT_B_TAC =
  REWRITE_TAC[] THEN REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  ARM_STEPS_TAC KD2_EXEC (1--6) THEN LIBC_PLT_TAC KD2_EXEC 6 THEN
  KD2_SAFE_NORMALIZE_TAC THEN LIBC_SAFE_CALL_TAC "H_MEMSET" KD2_EXEC
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`;
    `read X30 s`] (ref KD2_SAFE_ALLOWED) 11 THEN
  ARM_STEPS_TAC KD2_EXEC (12--19) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC KD2_EXEC (20--36) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[KD2_DREG] THEN
  KD2_DISCHARGE_EXIT_TAC;;

let KD2_SAFE_BAD_TAC =
  KD2_SAFE_START_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[EQF_INTRO(ASSUME
   `~(num_of_bytelist(hh:byte list) = num_of_bytelist(sha3_256 ekk))`)]) THEN
  ARM_STEPS_TAC KD2_EXEC (23--29) THEN LIBC_PLT_TAC KD2_EXEC 29 THEN
  KD2_SAFE_NORMALIZE_TAC THEN LIBC_SAFE_CALL_TAC "H_MEMSET" KD2_EXEC
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`;
    `read X30 s`] (ref KD2_SAFE_ALLOWED) 34 THEN
  ARM_STEPS_TAC KD2_EXEC (35--42) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC KD2_EXEC (43--59) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[KD2_DREG] THEN
  KD2_DISCHARGE_EXIT_TAC;;

let KD2_SAFE_CASE_TAC b =
  SUBGOAL_THEN (subst [mk_small_numeral b,`b:num`]
   `aligned 16 (word_add stackpointer (word b):int64)`)
  ASSUME_TAC THENL
   [UNDISCH_TAC `aligned 16 (stackpointer:int64)` THEN
    CONV_TAC(LAND_CONV NORMALIZE_ALIGNED_WORD_CONV) THEN
    CONV_TAC(RAND_CONV NORMALIZE_ALIGNED_WORD_CONV) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC
   `num_of_bytelist(hh:byte list) = num_of_bytelist(sha3_256 ekk)` THEN
  ASM_REWRITE_TAC[] THENL
   [ENSURES_EVENTS_WHILE_UP2_TAC `32` `pc + mlkem512_dec_loop1`
     `pc + mlkem512_dec_loop1_exit`
     (KD2_SAFE_CMOV_INV b) THEN
    REPEAT CONJ_TAC THENL
     [ARITH_TAC; KD2_SAFE_PART_A_TAC; KD2_SAFE_CMOV_BODY_TAC;
      KD2_SAFE_EXIT_B_TAC];
    KD2_SAFE_BAD_TAC];;

let MLKEM_NATIVE_DEC_K2_CLANG17_O3_IMAGE_SUBROUTINE_SAFE_STMT =
  `!mf mc ea el ev.
   memset_full_contract mf ea el ev /\ memcpy_safety_contract mc ea el ev
   ==> exists f_events.
        forall e ss ct sk (dk:byte list) guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\ LENGTH dk = 1632 /\
          (!i j. i < 2 /\ j < 2
                 ==> mlkem_samplentt_terminates
                      (APPEND (mlkem_slice 1536 32 dk) [word j; word i])) /\
          nonoverlapping (ct,768) (word pc,libmlkem_size) /\
          nonoverlapping (sk,1632) (word pc,libmlkem_size) /\
          nonoverlapping (ss,32)
           (word_sub stackpointer (word 12896),12896) /\
          ALLPAIRS nonoverlapping
           [(ss,32); (word_sub stackpointer (word 12896),12896)]
           [(ct,768); (sk,1632); (word pc,libmlkem_size);
            (word(pc + got_stack_chk_guard),8);
            (guard,8); (word(pc + got_memset),8); (word(pc + got_memcpy),8);
            (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mlkem_native_libmlkem_clang17_O3_mc /\
                    read PC s = word (pc + mlkem512_dec) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [ss; ct; sk] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s
                     = guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(sk,1632)) s = num_of_bytelist dk /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events ss ct sk guard mf mc pc
                              (word_sub stackpointer (word 12896))
                              returnaddress
                              (mlkem_slice 768 800 dk)
                              (mlkem_slice 1568 32 dk) /\
                       memaccess_inbounds e2
                        [ct,768; sk,1632; ss,32;
                         word_sub stackpointer (word 12896),12896;
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
                         mlkem_poly_compress_d4_consts_size;
                         word(pc + mlkem_poly_decompress_d10_consts),
                         mlkem_poly_decompress_d10_consts_size;
                         word(pc + mlkem_poly_tomsg_consts),
                         mlkem_poly_tomsg_consts_size]
                        [ss,32; word_sub stackpointer (word 12896),12896]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(ss,32);
                  memory :> bytes(word_sub stackpointer (word 12896),12896)])`;;

let MLKEM_NATIVE_DEC_K2_CLANG17_O3_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_DEC_K2_CLANG17_O3_IMAGE_SUBROUTINE_SAFE_STMT;;
