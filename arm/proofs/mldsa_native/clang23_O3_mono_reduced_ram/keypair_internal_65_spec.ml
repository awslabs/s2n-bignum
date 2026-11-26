(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Key generation: the statement. This is the code for                       *)
(* mldsa65_keypair_internal (mld_sign_keypair_internal in sign.c, with       *)
(* mld_sample_pack_s1_s2 inlined) from mldsa-native's portable C             *)
(* implementation compiled by clang 23 with -O3 as one translation unit      *)
(* with MLD_CONFIG_REDUCE_RAM (see mldsa_native/README.md). It expands the   *)
(* seed into rho, rho' and the key with an inlined SHAKE256 (one call of     *)
(* mldsa_keccakf1600_permute), samples s2 and s1 from rho' with calls of     *)
(* mldsa65_poly_uniform_eta_4x (three times, four polynomials each), packs   *)
(* each polynomial into the secret key with inlined code (four bits per      *)
(* coefficient), transforms s1 to the NTT domain with five calls of          *)
(* mldsa_poly_ntt, copies rho into the public key, computes t and packs t1   *)
(* into the public key and t0 into the secret key with                       *)
(* mld_compute_pack_t0_t165, hashes the public key into tr with an inlined   *)
(* SHAKE256 (fifteen calls of mldsa_keccakf1600_permute), packs rho, the     *)
(* key and tr into the secret key, and zeroes its buffers with memset and    *)
(* stores. It is verified in the whole image (see libmldsa.ml) against       *)
(* mld_keypair_pk_65 and mld_keypair_sk_65 of common/mldsa_native_sign.ml,   *)
(* using the theorems for the callees and the contracts                      *)
(* memset_full_contract and memcpy_full_contract of                          *)
(* utils/mlkem_native_libc_full.ml (memcpy is used by compute_pack through   *)
(* the expansion of the matrix), assuming that the expansion of the matrix   *)
(* and the sampling of each polynomial terminate, and shown to be constant   *)
(* time and memory safe, with the events depending only on the addresses     *)
(* and the values that the C code declassifies (rho and                      *)
(* mld_keypair_declass_65). The stack is the 11296 bytes of the function     *)
(* and of its callees.                                                       *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native.ml";;
needs "arm/proofs/utils/mlkem_native_libc_full.ml";;
needs "common/mldsa_native_sign.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/poly_uniform_eta_4x_65_spec.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/compute_pack_t0_t1_65_spec.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/libmldsa.ml";;

(*** The code in the image, and the PLT stub for memset:

    mldsa65_keypair_internal:
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
      +0x2c: sub     x9, sp, #0x1, lsl #12
      +0x30: sub     x9, x9, #0x6a0
      +0x34: and     x9, x9, #0xffffffffffffffe0
      +0x38: sub     sp, sp, #0x1, lsl #12
      +0x3c: cmp     sp, x9
      +0x40: b.le    <mldsa65_keypair_internal+0x54>
      +0x44: ldr     xzr, [sp]
      +0x48: sub     sp, sp, #0x1, lsl #12
      +0x4c: cmp     sp, x9
      +0x50: b.gt    <mldsa65_keypair_internal+0x44>
      +0x54: mov     sp, x9
      +0x58: adrp    x8, <page>
      +0x5c: ldr     xzr, [sp]
      +0x60: movi    v3.2d, #0x0
      +0x64: ldr     x8, [x8, #4088]
      +0x68: add     x10, sp, #0x1, lsl #12
      +0x6c: add     x9, sp, #0xc0
      +0x70: add     x10, x10, #0x500
      +0x74: add     x11, sp, #0x1, lsl #12
      +0x78: mov     x20, x0
      +0x7c: ldr     x8, [x8]
      +0x80: add     x11, x11, #0x500
      +0x84: add     x0, sp, #0xc0
      +0x88: mov     x19, x1
      +0x8c: add     x22, sp, #0xc0
      +0x90: str     x8, [sp, #5784]
      +0x94: orr     x8, x10, #0x18
      +0x98: ldp     q1, q0, [x2]
      +0x9c: stur    q3, [x9, #184]
      +0xa0: stur    q3, [x9, #168]
      +0xa4: stur    q3, [x9, #152]
      +0xa8: stur    q3, [x9, #136]
      +0xac: stur    q3, [sp, #216]
      +0xb0: str     q0, [sp, #5392]
      +0xb4: ldrb    w9, [sp, #217]
      +0xb8: ldrb    w10, [x10, #25]
      +0xbc: ld1     {v0.b}[8], [x8]
      +0xc0: str     q1, [sp, #5376]
      +0xc4: ldr     s1, [sp, #220]
      +0xc8: ldr     s2, [sp, #5404]
      +0xcc: str     wzr, [sp, #392]
      +0xd0: eor     w8, w9, w10
      +0xd4: ldrb    w9, [x11, #26]
      +0xd8: ldrb    w10, [sp, #219]
      +0xdc: mov     v0.b[9], w8
      +0xe0: ldrb    w8, [sp, #218]
      +0xe4: zip1    v1.8b, v1.8b, v1.8b
      +0xe8: zip1    v2.8b, v2.8b, v2.8b
      +0xec: stur    q3, [sp, #248]
      +0xf0: eor     w8, w8, w9
      +0xf4: mov     w9, #0x506
      +0xf8: stur    q3, [sp, #232]
      +0xfc: strh    w9, [sp, #5408]
     +0x100: add     x9, sp, #0x39
     +0x104: mov     v0.b[10], w8
     +0x108: ldrb    w8, [x11, #27]
     +0x10c: stur    q3, [x9, #255]
     +0x110: eor     v1.8b, v1.8b, v2.8b
     +0x114: ldr     q2, [sp, #5392]
     +0x118: eor     w8, w10, w8
     +0x11c: ldrb    w10, [x11, #33]
     +0x120: mov     v0.b[11], w8
     +0x124: add     x8, sp, #0x29
     +0x128: stur    q3, [x8, #255]
     +0x12c: add     x8, sp, #0x19
     +0x130: stur    q3, [x8, #255]
     +0x134: add     x8, sp, #0x9
     +0x138: stur    q3, [x8, #255]
     +0x13c: ldrb    w8, [x11, #32]
     +0x140: uzp1    v1.8b, v1.8b, v0.8b
     +0x144: mov     v2.s[2], v0.s[2]
     +0x148: ldrb    w9, [sp, #224]
     +0x14c: ldrb    w12, [sp, #226]
     +0x150: ldrb    w11, [sp, #225]
     +0x154: ldr     q0, [sp, #5376]
     +0x158: eor     w8, w9, w8
     +0x15c: ldrb    w9, [sp, #327]
     +0x160: strb    w8, [sp, #224]
     +0x164: eor     w8, w12, #0x1f
     +0x168: eor     w10, w11, w10
     +0x16c: mov     v2.s[3], v1.s[0]
     +0x170: eor     w9, w9, #0x80
     +0x174: strb    w8, [sp, #226]
     +0x178: mov     w8, #0x88
     +0x17c: strb    w10, [sp, #225]
     +0x180: strb    w9, [sp, #327]
     +0x184: str     w8, [sp, #392]
     +0x188: stp     q0, q2, [sp, #192]
     +0x18c: bl      <mldsa_keccakf1600_permute>
     +0x190: ldp     q0, q1, [sp, #256]
     +0x194: add     x9, sp, #0x1, lsl #12
     +0x198: add     x9, x9, #0x540
     +0x19c: mov     w8, #0xa
     +0x1a0: add     x0, sp, #0xc0
     +0x1a4: add     x1, x22, #0x400
     +0x1a8: add     x2, x22, #0x800
     +0x1ac: add     x3, x22, #0xc00
     +0x1b0: str     q0, [sp, #5504]
     +0x1b4: ldp     q0, q2, [sp, #288]
     +0x1b8: str     q1, [sp, #5520]
     +0x1bc: add     x4, x9, #0x20
     +0x1c0: mov     w5, #0x7
     +0x1c4: mov     w6, #0x8
     +0x1c8: mov     w7, #0x9
     +0x1cc: add     x25, x22, #0x400
     +0x1d0: str     q0, [sp, #5536]
     +0x1d4: ldp     q1, q0, [sp, #192]
     +0x1d8: str     q2, [sp, #5552]
     +0x1dc: add     x28, x22, #0x800
     +0x1e0: add     x21, x22, #0xc00
     +0x1e4: str     q0, [sp, #5456]
     +0x1e8: ldp     q2, q0, [sp, #224]
     +0x1ec: str     q1, [sp, #5440]
     +0x1f0: str     q0, [sp, #5488]
     +0x1f4: movi    v0.2d, #0x0
     +0x1f8: str     q2, [sp, #5472]
     +0x1fc: stp     q0, q0, [sp, #192]
     +0x200: stp     q0, q0, [sp, #224]
     +0x204: stp     q0, q0, [sp, #256]
     +0x208: stp     q0, q0, [sp, #288]
     +0x20c: stp     q0, q0, [sp, #320]
     +0x210: stp     q0, q0, [sp, #352]
     +0x214: str     q0, [sp, #384]
     +0x218: strb    w8, [sp]
     +0x21c: bl      <mldsa65_poly_uniform_eta_4x>
     +0x220: add     x8, x22, #0x40
     +0x224: add     x9, x22, #0x60
     +0x228: add     x10, x22, #0x80
     +0x22c: add     x23, sp, #0xc0
     +0x230: ld2     {v4.4s-v5.4s}, [x8]
     +0x234: add     x8, x22, #0xa0
     +0x238: ld2     {v6.4s-v7.4s}, [x9]
     +0x23c: add     x9, x22, #0xc0
     +0x240: add     x11, x22, #0x1e0
     +0x244: add     x0, x22, #0x1, lsl #12
     +0x248: add     x1, sp, #0xc0
     +0x24c: add     x2, x22, #0x400
     +0x250: ld2     {v16.4s-v17.4s}, [x10]
     +0x254: add     x10, x22, #0xe0
     +0x258: add     x3, x22, #0x800
     +0x25c: mov     w5, #0x4
     +0x260: mov     w6, #0x5
     +0x264: mov     w7, #0x6
     +0x268: ld2     {v0.4s-v1.4s}, [x23], #32
     +0x26c: uzp1    v24.8h, v5.8h, v7.8h
     +0x270: uzp1    v4.8h, v4.8h, v6.8h
     +0x274: movi    v6.16b, #0x40
     +0x278: str     xzr, [sp, #5568]
     +0x27c: ld2     {v2.4s-v3.4s}, [x23]
     +0x280: ld2     {v18.4s-v19.4s}, [x8]
     +0x284: add     x8, x22, #0x100
     +0x288: ld2     {v20.4s-v21.4s}, [x9]
     +0x28c: add     x9, x22, #0x140
     +0x290: ld2     {v22.4s-v23.4s}, [x10]
     +0x294: add     x10, x22, #0x160
     +0x298: uzp1    v25.8h, v1.8h, v3.8h
     +0x29c: uzp1    v27.8h, v17.8h, v19.8h
     +0x2a0: uzp1    v0.8h, v0.8h, v2.8h
     +0x2a4: uzp1    v26.8h, v21.8h, v23.8h
     +0x2a8: uzp1    v1.8h, v20.8h, v22.8h
     +0x2ac: uzp1    v2.8h, v16.8h, v18.8h
     +0x2b0: ld2     {v18.4s-v19.4s}, [x9]
     +0x2b4: add     x9, x22, #0x180
     +0x2b8: ld2     {v20.4s-v21.4s}, [x10]
     +0x2bc: add     x10, x22, #0x1a0
     +0x2c0: uzp1    v3.16b, v25.16b, v24.16b
     +0x2c4: uzp1    v0.16b, v0.16b, v4.16b
     +0x2c8: movi    v4.16b, #0x4
     +0x2cc: uzp1    v5.16b, v27.16b, v26.16b
     +0x2d0: uzp1    v1.16b, v2.16b, v1.16b
     +0x2d4: ld2     {v24.4s-v25.4s}, [x11]
     +0x2d8: add     x11, x22, #0xfe0
     +0x2dc: ld2     {v26.4s-v27.4s}, [x9]
     +0x2e0: add     x9, x22, #0x220
     +0x2e4: ld2     {v28.4s-v29.4s}, [x10]
     +0x2e8: add     x10, x22, #0x240
     +0x2ec: ld2     {v8.4s-v9.4s}, [x9]
     +0x2f0: shl     v2.16b, v3.16b, #4
     +0x2f4: sub     v0.16b, v4.16b, v0.16b
     +0x2f8: add     x9, x22, #0x2c0
     +0x2fc: shl     v3.16b, v5.16b, #4
     +0x300: sub     v4.16b, v4.16b, v1.16b
     +0x304: ld2     {v14.4s-v15.4s}, [x9]
     +0x308: add     x9, x22, #0x280
     +0x30c: ld2     {v10.4s-v11.4s}, [x10]
     +0x310: add     x10, x22, #0x340
     +0x314: sub     v1.16b, v6.16b, v2.16b
     +0x318: uzp1    v7.8h, v26.8h, v28.8h
     +0x31c: sub     v2.16b, v6.16b, v3.16b
     +0x320: ld2     {v5.4s-v6.4s}, [x8]
     +0x324: add     x8, x22, #0x120
     +0x328: ld2     {v16.4s-v17.4s}, [x8]
     +0x32c: add     x8, x22, #0x1c0
     +0x330: orr     v3.16b, v1.16b, v0.16b
     +0x334: ld2     {v22.4s-v23.4s}, [x8]
     +0x338: add     x8, x22, #0x200
     +0x33c: orr     v0.16b, v2.16b, v4.16b
     +0x340: ld2     {v30.4s-v31.4s}, [x8]
     +0x344: add     x8, x22, #0x260
     +0x348: ld2     {v12.4s-v13.4s}, [x8]
     +0x34c: add     x8, x22, #0x2e0
     +0x350: uzp1    v1.8h, v5.8h, v16.8h
     +0x354: str     q0, [sp, #160]
     +0x358: uzp1    v0.8h, v18.8h, v20.8h
     +0x35c: stp     q0, q3, [sp, #112]
     +0x360: uzp1    v0.8h, v19.8h, v21.8h
     +0x364: uzp1    v20.8h, v23.8h, v25.8h
     +0x368: uzp1    v21.8h, v31.8h, v9.8h
     +0x36c: uzp1    v19.8h, v11.8h, v13.8h
     +0x370: stp     q0, q1, [sp, #80]
     +0x374: uzp1    v0.8h, v6.8h, v17.8h
     +0x378: uzp1    v6.8h, v22.8h, v24.8h
     +0x37c: uzp1    v22.8h, v27.8h, v29.8h
     +0x380: uzp1    v17.8h, v30.8h, v8.8h
     +0x384: uzp1    v16.8h, v10.8h, v12.8h
     +0x388: uzp1    v19.16b, v21.16b, v19.16b
     +0x38c: ldp     q4, q5, [sp, #112]
     +0x390: ld2     {v23.4s-v24.4s}, [x9]
     +0x394: add     x9, x22, #0x300
     +0x398: ld2     {v8.4s-v9.4s}, [x10]
     +0x39c: add     x10, x22, #0x3e0
     +0x3a0: uzp1    v6.16b, v7.16b, v6.16b
     +0x3a4: str     q0, [sp, #64]
     +0x3a8: uzp1    v20.16b, v22.16b, v20.16b
     +0x3ac: str     q5, [x19, #1024]
     +0x3b0: ldr     q5, [sp, #96]
     +0x3b4: shl     v19.16b, v19.16b, #4
     +0x3b8: ld2     {v0.4s-v1.4s}, [x8]
     +0x3bc: add     x8, x22, #0x2a0
     +0x3c0: uzp1    v5.16b, v5.16b, v4.16b
     +0x3c4: ld2     {v25.4s-v26.4s}, [x8]
     +0x3c8: add     x8, x22, #0x320
     +0x3cc: ld2     {v27.4s-v28.4s}, [x9]
     +0x3d0: add     x9, x22, #0x380
     +0x3d4: ld2     {v29.4s-v30.4s}, [x8]
     +0x3d8: add     x8, x22, #0x360
     +0x3dc: ld2     {v12.4s-v13.4s}, [x9]
     +0x3e0: add     x9, x22, #0x3c0
     +0x3e4: uzp1    v18.8h, v14.8h, v0.8h
     +0x3e8: uzp1    v31.8h, v15.8h, v1.8h
     +0x3ec: ld2     {v10.4s-v11.4s}, [x8]
     +0x3f0: uzp1    v4.8h, v24.8h, v26.8h
     +0x3f4: uzp1    v23.8h, v23.8h, v25.8h
     +0x3f8: add     x8, x22, #0x3a0
     +0x3fc: uzp1    v27.8h, v27.8h, v29.8h
     +0x400: ldr     q24, [sp, #160]
     +0x404: ld2     {v14.4s-v15.4s}, [x8]
     +0x408: add     x8, sp, #0x1, lsl #12
     +0x40c: ld2     {v2.4s-v3.4s}, [x9]
     +0x410: add     x9, x22, #0x460
     +0x414: uzp1    v7.8h, v9.8h, v11.8h
     +0x418: add     x8, x8, #0x5c0
     +0x41c: str     q24, [x19, #1040]
     +0x420: uzp1    v4.16b, v4.16b, v31.16b
     +0x424: movi    v31.16b, #0x4
     +0x428: uzp1    v18.16b, v23.16b, v18.16b
     +0x42c: uzp1    v26.8h, v13.8h, v15.8h
     +0x430: ldp     q25, q24, [sp, #64]
     +0x434: ld2     {v0.4s-v1.4s}, [x10]
     +0x438: add     x10, x22, #0x480
     +0x43c: uzp1    v24.16b, v25.16b, v24.16b
     +0x440: uzp1    v25.8h, v28.8h, v30.8h
     +0x444: sub     v5.16b, v31.16b, v5.16b
     +0x448: sub     v6.16b, v31.16b, v6.16b
     +0x44c: shl     v4.16b, v4.16b, #4
     +0x450: movi    v28.16b, #0x40
     +0x454: uzp1    v22.8h, v3.8h, v1.8h
     +0x458: uzp1    v0.8h, v2.8h, v0.8h
     +0x45c: uzp1    v1.8h, v12.8h, v14.8h
     +0x460: uzp1    v3.16b, v17.16b, v16.16b
     +0x464: shl     v2.16b, v20.16b, #4
     +0x468: shl     v21.16b, v24.16b, #4
     +0x46c: uzp1    v24.8h, v8.8h, v10.8h
     +0x470: uzp1    v7.16b, v25.16b, v7.16b
     +0x474: uzp1    v16.16b, v26.16b, v22.16b
     +0x478: movi    v22.16b, #0x40
     +0x47c: uzp1    v0.16b, v1.16b, v0.16b
     +0x480: sub     v1.16b, v31.16b, v3.16b
     +0x484: uzp1    v20.16b, v27.16b, v24.16b
     +0x488: shl     v7.16b, v7.16b, #4
     +0x48c: sub     v17.16b, v22.16b, v21.16b
     +0x490: sub     v2.16b, v22.16b, v2.16b
     +0x494: sub     v3.16b, v22.16b, v19.16b
     +0x498: shl     v16.16b, v16.16b, #4
     +0x49c: sub     v4.16b, v22.16b, v4.16b
     +0x4a0: sub     v7.16b, v22.16b, v7.16b
     +0x4a4: sub     v0.16b, v31.16b, v0.16b
     +0x4a8: orr     v5.16b, v17.16b, v5.16b
     +0x4ac: sub     v17.16b, v31.16b, v18.16b
     +0x4b0: orr     v2.16b, v2.16b, v6.16b
     +0x4b4: sub     v6.16b, v31.16b, v20.16b
     +0x4b8: orr     v1.16b, v3.16b, v1.16b
     +0x4bc: sub     v3.16b, v22.16b, v16.16b
     +0x4c0: orr     v4.16b, v4.16b, v17.16b
     +0x4c4: str     q2, [x19, #1072]
     +0x4c8: orr     v2.16b, v7.16b, v6.16b
     +0x4cc: orr     v0.16b, v3.16b, v0.16b
     +0x4d0: str     q5, [x19, #1056]
     +0x4d4: str     q1, [x19, #1088]
     +0x4d8: str     q4, [x19, #1104]
     +0x4dc: str     q2, [x19, #1120]
     +0x4e0: str     q0, [x19, #1136]
     +0x4e4: add     x8, x22, #0x420
     +0x4e8: str     xzr, [sp, #5568]
     +0x4ec: ld2     {v2.4s-v3.4s}, [x8]
     +0x4f0: add     x8, x22, #0x440
     +0x4f4: ld2     {v6.4s-v7.4s}, [x9]
     +0x4f8: ld2     {v4.4s-v5.4s}, [x8]
     +0x4fc: ld2     {v16.4s-v17.4s}, [x10]
     +0x500: add     x8, x22, #0x4a0
     +0x504: add     x9, x22, #0x4c0
     +0x508: add     x10, x22, #0x4e0
     +0x50c: ld2     {v0.4s-v1.4s}, [x25]
     +0x510: ld2     {v18.4s-v19.4s}, [x8]
     +0x514: add     x8, x22, #0x540
     +0x518: ld2     {v20.4s-v21.4s}, [x9]
     +0x51c: add     x9, x22, #0x500
     +0x520: ld2     {v22.4s-v23.4s}, [x10]
     +0x524: add     x10, x22, #0x580
     +0x528: uzp1    v24.8h, v5.8h, v7.8h
     +0x52c: uzp1    v4.8h, v4.8h, v6.8h
     +0x530: uzp1    v25.8h, v1.8h, v3.8h
     +0x534: uzp1    v0.8h, v0.8h, v2.8h
     +0x538: uzp1    v27.8h, v17.8h, v19.8h
     +0x53c: uzp1    v2.8h, v16.8h, v18.8h
     +0x540: ld2     {v16.4s-v17.4s}, [x9]
     +0x544: uzp1    v26.8h, v21.8h, v23.8h
     +0x548: uzp1    v1.8h, v20.8h, v22.8h
     +0x54c: add     x9, x22, #0x5c0
     +0x550: uzp1    v3.16b, v25.16b, v24.16b
     +0x554: uzp1    v0.16b, v0.16b, v4.16b
     +0x558: movi    v4.16b, #0x4
     +0x55c: ld2     {v24.4s-v25.4s}, [x10]
     +0x560: add     x10, x22, #0x640
     +0x564: uzp1    v5.16b, v27.16b, v26.16b
     +0x568: uzp1    v1.16b, v2.16b, v1.16b
     +0x56c: ld2     {v8.4s-v9.4s}, [x10]
     +0x570: add     x10, x22, #0x740
     +0x574: shl     v2.16b, v3.16b, #4
     +0x578: sub     v0.16b, v4.16b, v0.16b
     +0x57c: shl     v3.16b, v5.16b, #4
     +0x580: sub     v20.16b, v4.16b, v1.16b
     +0x584: ld2     {v4.4s-v5.4s}, [x8]
     +0x588: sub     v2.16b, v28.16b, v2.16b
     +0x58c: add     x8, x22, #0x560
     +0x590: ld2     {v6.4s-v7.4s}, [x8]
     +0x594: add     x8, x22, #0x520
     +0x598: sub     v3.16b, v28.16b, v3.16b
     +0x59c: ld2     {v18.4s-v19.4s}, [x8]
     +0x5a0: add     x8, x22, #0x5e0
     +0x5a4: orr     v1.16b, v2.16b, v0.16b
     +0x5a8: ld2     {v22.4s-v23.4s}, [x8]
     +0x5ac: add     x8, x22, #0x600
     +0x5b0: ld2     {v28.4s-v29.4s}, [x8]
     +0x5b4: add     x8, x22, #0x660
     +0x5b8: orr     v0.16b, v3.16b, v20.16b
     +0x5bc: ld2     {v20.4s-v21.4s}, [x9]
     +0x5c0: add     x9, x22, #0x5a0
     +0x5c4: ld2     {v26.4s-v27.4s}, [x9]
     +0x5c8: add     x9, x22, #0x620
     +0x5cc: ld2     {v10.4s-v11.4s}, [x8]
     +0x5d0: add     x8, x22, #0x6e0
     +0x5d4: ld2     {v30.4s-v31.4s}, [x9]
     +0x5d8: add     x9, x22, #0x6c0
     +0x5dc: str     q0, [sp, #160]
     +0x5e0: uzp1    v0.8h, v4.8h, v6.8h
     +0x5e4: ld2     {v12.4s-v13.4s}, [x9]
     +0x5e8: add     x9, x22, #0x680
     +0x5ec: ld2     {v14.4s-v15.4s}, [x8]
     +0x5f0: add     x8, x22, #0x6a0
     +0x5f4: stp     q0, q1, [sp, #112]
     +0x5f8: uzp1    v1.8h, v16.8h, v18.8h
     +0x5fc: uzp1    v0.8h, v5.8h, v7.8h
     +0x600: uzp1    v6.8h, v20.8h, v22.8h
     +0x604: uzp1    v7.8h, v24.8h, v26.8h
     +0x608: uzp1    v20.8h, v21.8h, v23.8h
     +0x60c: uzp1    v22.8h, v25.8h, v27.8h
     +0x610: uzp1    v21.8h, v29.8h, v31.8h
     +0x614: uzp1    v27.8h, v13.8h, v15.8h
     +0x618: ldr     q4, [sp, #128]
     +0x61c: ld2     {v23.4s-v24.4s}, [x9]
     +0x620: add     x9, x22, #0x700
     +0x624: stp     q0, q1, [sp, #80]
     +0x628: uzp1    v1.8h, v17.8h, v19.8h
     +0x62c: uzp1    v0.8h, v12.8h, v14.8h
     +0x630: uzp1    v17.8h, v28.8h, v30.8h
     +0x634: uzp1    v16.8h, v8.8h, v10.8h
     +0x638: uzp1    v19.8h, v9.8h, v11.8h
     +0x63c: uzp1    v20.16b, v22.16b, v20.16b
     +0x640: str     q4, [x19, #1152]
     +0x644: ld2     {v25.4s-v26.4s}, [x8]
     +0x648: add     x8, x22, #0x720
     +0x64c: ldp     q5, q4, [sp, #96]
     +0x650: stp     q0, q1, [sp, #48]
     +0x654: ld2     {v28.4s-v29.4s}, [x9]
     +0x658: add     x9, x22, #0x780
     +0x65c: uzp1    v19.16b, v21.16b, v19.16b
     +0x660: ld2     {v30.4s-v31.4s}, [x8]
     +0x664: add     x8, x22, #0x760
     +0x668: uzp1    v18.8h, v23.8h, v25.8h
     +0x66c: uzp1    v5.16b, v5.16b, v4.16b
     +0x670: uzp1    v4.8h, v24.8h, v26.8h
     +0x674: ldr     q23, [sp, #160]
     +0x678: ld2     {v8.4s-v9.4s}, [x10]
     +0x67c: add     x10, x22, #0x7e0
     +0x680: ld2     {v10.4s-v11.4s}, [x8]
     +0x684: add     x8, x22, #0x7a0
     +0x688: ld2     {v12.4s-v13.4s}, [x9]
     +0x68c: add     x9, x22, #0x7c0
     +0x690: uzp1    v25.8h, v29.8h, v31.8h
     +0x694: shl     v19.16b, v19.16b, #4
     +0x698: uzp1    v4.16b, v4.16b, v27.16b
     +0x69c: uzp1    v27.8h, v28.8h, v30.8h
     +0x6a0: movi    v28.16b, #0x40
     +0x6a4: str     q23, [x19, #1168]
     +0x6a8: ldp     q24, q23, [sp, #64]
     +0x6ac: ld2     {v14.4s-v15.4s}, [x8]
     +0x6b0: add     x8, sp, #0x1, lsl #12
     +0x6b4: ld2     {v2.4s-v3.4s}, [x9]
     +0x6b8: add     x8, x8, #0x5c0
     +0x6bc: add     x9, x22, #0x860
     +0x6c0: ld2     {v0.4s-v1.4s}, [x10]
     +0x6c4: uzp1    v24.16b, v24.16b, v23.16b
     +0x6c8: uzp1    v23.16b, v7.16b, v6.16b
     +0x6cc: uzp1    v7.8h, v9.8h, v11.8h
     +0x6d0: movi    v6.16b, #0x4
     +0x6d4: shl     v4.16b, v4.16b, #4
     +0x6d8: add     x10, x22, #0x880
     +0x6dc: uzp1    v26.8h, v13.8h, v15.8h
     +0x6e0: uzp1    v22.8h, v3.8h, v1.8h
     +0x6e4: uzp1    v0.8h, v2.8h, v0.8h
     +0x6e8: uzp1    v3.16b, v17.16b, v16.16b
     +0x6ec: shl     v21.16b, v24.16b, #4
     +0x6f0: shl     v2.16b, v20.16b, #4
     +0x6f4: uzp1    v24.8h, v8.8h, v10.8h
     +0x6f8: uzp1    v1.8h, v12.8h, v14.8h
     +0x6fc: sub     v5.16b, v6.16b, v5.16b
     +0x700: uzp1    v7.16b, v25.16b, v7.16b
     +0x704: ldr     q20, [sp, #48]
     +0x708: uzp1    v16.16b, v26.16b, v22.16b
     +0x70c: movi    v22.16b, #0x40
     +0x710: uzp1    v18.16b, v18.16b, v20.16b
     +0x714: uzp1    v20.16b, v27.16b, v24.16b
     +0x718: uzp1    v0.16b, v1.16b, v0.16b
     +0x71c: shl     v7.16b, v7.16b, #4
     +0x720: sub     v1.16b, v6.16b, v3.16b
     +0x724: sub     v17.16b, v22.16b, v21.16b
     +0x728: sub     v21.16b, v6.16b, v23.16b
     +0x72c: sub     v2.16b, v22.16b, v2.16b
     +0x730: sub     v3.16b, v22.16b, v19.16b
     +0x734: shl     v16.16b, v16.16b, #4
     +0x738: sub     v4.16b, v22.16b, v4.16b
     +0x73c: sub     v7.16b, v22.16b, v7.16b
     +0x740: orr     v5.16b, v17.16b, v5.16b
     +0x744: sub     v17.16b, v6.16b, v18.16b
     +0x748: movi    v18.16b, #0x4
     +0x74c: orr     v2.16b, v2.16b, v21.16b
     +0x750: sub     v6.16b, v6.16b, v20.16b
     +0x754: orr     v1.16b, v3.16b, v1.16b
     +0x758: sub     v3.16b, v22.16b, v16.16b
     +0x75c: orr     v4.16b, v4.16b, v17.16b
     +0x760: str     q5, [x19, #1184]
     +0x764: sub     v0.16b, v18.16b, v0.16b
     +0x768: str     q2, [x19, #1200]
     +0x76c: orr     v2.16b, v7.16b, v6.16b
     +0x770: str     q1, [x19, #1216]
     +0x774: str     q4, [x19, #1232]
     +0x778: orr     v0.16b, v3.16b, v0.16b
     +0x77c: str     q2, [x19, #1248]
     +0x780: str     q0, [x19, #1264]
     +0x784: add     x8, x22, #0x820
     +0x788: str     xzr, [sp, #5568]
     +0x78c: ld2     {v2.4s-v3.4s}, [x8]
     +0x790: add     x8, x22, #0x840
     +0x794: ld2     {v6.4s-v7.4s}, [x9]
     +0x798: ld2     {v4.4s-v5.4s}, [x8]
     +0x79c: ld2     {v16.4s-v17.4s}, [x10]
     +0x7a0: add     x8, x22, #0x8a0
     +0x7a4: add     x9, x22, #0x8c0
     +0x7a8: add     x10, x22, #0x8e0
     +0x7ac: ld2     {v0.4s-v1.4s}, [x28]
     +0x7b0: add     x28, x22, #0x1, lsl #12
     +0x7b4: ld2     {v18.4s-v19.4s}, [x8]
     +0x7b8: add     x8, x22, #0x940
     +0x7bc: ld2     {v20.4s-v21.4s}, [x9]
     +0x7c0: add     x9, x22, #0x900
     +0x7c4: ld2     {v22.4s-v23.4s}, [x10]
     +0x7c8: uzp1    v24.8h, v5.8h, v7.8h
     +0x7cc: uzp1    v4.8h, v4.8h, v6.8h
     +0x7d0: add     x10, x22, #0x980
     +0x7d4: uzp1    v25.8h, v1.8h, v3.8h
     +0x7d8: uzp1    v0.8h, v0.8h, v2.8h
     +0x7dc: uzp1    v27.8h, v17.8h, v19.8h
     +0x7e0: uzp1    v2.8h, v16.8h, v18.8h
     +0x7e4: ld2     {v16.4s-v17.4s}, [x9]
     +0x7e8: uzp1    v26.8h, v21.8h, v23.8h
     +0x7ec: uzp1    v1.8h, v20.8h, v22.8h
     +0x7f0: add     x9, x22, #0x9c0
     +0x7f4: uzp1    v3.16b, v25.16b, v24.16b
     +0x7f8: uzp1    v0.16b, v0.16b, v4.16b
     +0x7fc: movi    v4.16b, #0x4
     +0x800: ld2     {v24.4s-v25.4s}, [x10]
     +0x804: add     x10, x22, #0xa40
     +0x808: uzp1    v5.16b, v27.16b, v26.16b
     +0x80c: uzp1    v1.16b, v2.16b, v1.16b
     +0x810: ld2     {v8.4s-v9.4s}, [x10]
     +0x814: add     x10, x22, #0xb40
     +0x818: shl     v2.16b, v3.16b, #4
     +0x81c: sub     v0.16b, v4.16b, v0.16b
     +0x820: shl     v3.16b, v5.16b, #4
     +0x824: sub     v20.16b, v4.16b, v1.16b
     +0x828: ld2     {v4.4s-v5.4s}, [x8]
     +0x82c: sub     v2.16b, v28.16b, v2.16b
     +0x830: add     x8, x22, #0x960
     +0x834: ld2     {v6.4s-v7.4s}, [x8]
     +0x838: add     x8, x22, #0x920
     +0x83c: sub     v3.16b, v28.16b, v3.16b
     +0x840: ld2     {v18.4s-v19.4s}, [x8]
     +0x844: add     x8, x22, #0x9e0
     +0x848: orr     v1.16b, v2.16b, v0.16b
     +0x84c: ld2     {v22.4s-v23.4s}, [x8]
     +0x850: add     x8, x22, #0xa00
     +0x854: ld2     {v28.4s-v29.4s}, [x8]
     +0x858: add     x8, x22, #0xa60
     +0x85c: orr     v0.16b, v3.16b, v20.16b
     +0x860: ld2     {v20.4s-v21.4s}, [x9]
     +0x864: add     x9, x22, #0x9a0
     +0x868: ld2     {v26.4s-v27.4s}, [x9]
     +0x86c: add     x9, x22, #0xa20
     +0x870: ld2     {v10.4s-v11.4s}, [x8]
     +0x874: add     x8, x22, #0xae0
     +0x878: ld2     {v30.4s-v31.4s}, [x9]
     +0x87c: add     x9, x22, #0xac0
     +0x880: str     q0, [sp, #160]
     +0x884: uzp1    v0.8h, v4.8h, v6.8h
     +0x888: ld2     {v12.4s-v13.4s}, [x9]
     +0x88c: add     x9, x22, #0xa80
     +0x890: ld2     {v14.4s-v15.4s}, [x8]
     +0x894: add     x8, x22, #0xaa0
     +0x898: stp     q0, q1, [sp, #112]
     +0x89c: uzp1    v1.8h, v16.8h, v18.8h
     +0x8a0: uzp1    v0.8h, v5.8h, v7.8h
     +0x8a4: uzp1    v6.8h, v20.8h, v22.8h
     +0x8a8: uzp1    v7.8h, v24.8h, v26.8h
     +0x8ac: uzp1    v20.8h, v21.8h, v23.8h
     +0x8b0: uzp1    v22.8h, v25.8h, v27.8h
     +0x8b4: uzp1    v21.8h, v29.8h, v31.8h
     +0x8b8: uzp1    v27.8h, v13.8h, v15.8h
     +0x8bc: ldr     q4, [sp, #128]
     +0x8c0: ld2     {v23.4s-v24.4s}, [x9]
     +0x8c4: add     x9, x22, #0xb00
     +0x8c8: stp     q0, q1, [sp, #80]
     +0x8cc: uzp1    v1.8h, v17.8h, v19.8h
     +0x8d0: uzp1    v0.8h, v12.8h, v14.8h
     +0x8d4: uzp1    v17.8h, v28.8h, v30.8h
     +0x8d8: uzp1    v16.8h, v8.8h, v10.8h
     +0x8dc: uzp1    v19.8h, v9.8h, v11.8h
     +0x8e0: uzp1    v20.16b, v22.16b, v20.16b
     +0x8e4: str     q4, [x19, #1280]
     +0x8e8: ld2     {v25.4s-v26.4s}, [x8]
     +0x8ec: add     x8, x22, #0xb20
     +0x8f0: ldp     q5, q4, [sp, #96]
     +0x8f4: stp     q0, q1, [sp, #48]
     +0x8f8: ld2     {v28.4s-v29.4s}, [x9]
     +0x8fc: add     x9, x22, #0xb80
     +0x900: uzp1    v19.16b, v21.16b, v19.16b
     +0x904: ld2     {v30.4s-v31.4s}, [x8]
     +0x908: add     x8, x22, #0xb60
     +0x90c: uzp1    v18.8h, v23.8h, v25.8h
     +0x910: uzp1    v5.16b, v5.16b, v4.16b
     +0x914: uzp1    v4.8h, v24.8h, v26.8h
     +0x918: ldr     q23, [sp, #160]
     +0x91c: ld2     {v8.4s-v9.4s}, [x10]
     +0x920: add     x10, x22, #0xbe0
     +0x924: ld2     {v10.4s-v11.4s}, [x8]
     +0x928: add     x8, x22, #0xba0
     +0x92c: ld2     {v12.4s-v13.4s}, [x9]
     +0x930: add     x9, x22, #0xbc0
     +0x934: uzp1    v25.8h, v29.8h, v31.8h
     +0x938: shl     v19.16b, v19.16b, #4
     +0x93c: uzp1    v4.16b, v4.16b, v27.16b
     +0x940: uzp1    v27.8h, v28.8h, v30.8h
     +0x944: str     q23, [x19, #1296]
     +0x948: ldp     q24, q23, [sp, #64]
     +0x94c: ld2     {v14.4s-v15.4s}, [x8]
     +0x950: add     x8, sp, #0x1, lsl #12
     +0x954: ld2     {v2.4s-v3.4s}, [x9]
     +0x958: add     x9, x22, #0xc40
     +0x95c: add     x8, x8, #0x5c0
     +0x960: ld2     {v0.4s-v1.4s}, [x10]
     +0x964: add     x10, x22, #0xc60
     +0x968: uzp1    v24.16b, v24.16b, v23.16b
     +0x96c: uzp1    v23.16b, v7.16b, v6.16b
     +0x970: uzp1    v7.8h, v9.8h, v11.8h
     +0x974: uzp1    v26.8h, v13.8h, v15.8h
     +0x978: movi    v6.16b, #0x4
     +0x97c: shl     v4.16b, v4.16b, #4
     +0x980: uzp1    v22.8h, v3.8h, v1.8h
     +0x984: uzp1    v0.8h, v2.8h, v0.8h
     +0x988: uzp1    v3.16b, v17.16b, v16.16b
     +0x98c: shl     v21.16b, v24.16b, #4
     +0x990: shl     v2.16b, v20.16b, #4
     +0x994: uzp1    v24.8h, v8.8h, v10.8h
     +0x998: uzp1    v1.8h, v12.8h, v14.8h
     +0x99c: sub     v5.16b, v6.16b, v5.16b
     +0x9a0: uzp1    v7.16b, v25.16b, v7.16b
     +0x9a4: ldr     q20, [sp, #48]
     +0x9a8: uzp1    v16.16b, v26.16b, v22.16b
     +0x9ac: movi    v22.16b, #0x40
     +0x9b0: uzp1    v18.16b, v18.16b, v20.16b
     +0x9b4: uzp1    v20.16b, v27.16b, v24.16b
     +0x9b8: uzp1    v0.16b, v1.16b, v0.16b
     +0x9bc: shl     v7.16b, v7.16b, #4
     +0x9c0: sub     v1.16b, v6.16b, v3.16b
     +0x9c4: sub     v17.16b, v22.16b, v21.16b
     +0x9c8: sub     v21.16b, v6.16b, v23.16b
     +0x9cc: sub     v2.16b, v22.16b, v2.16b
     +0x9d0: sub     v3.16b, v22.16b, v19.16b
     +0x9d4: shl     v16.16b, v16.16b, #4
     +0x9d8: sub     v4.16b, v22.16b, v4.16b
     +0x9dc: sub     v7.16b, v22.16b, v7.16b
     +0x9e0: orr     v5.16b, v17.16b, v5.16b
     +0x9e4: sub     v17.16b, v6.16b, v18.16b
     +0x9e8: movi    v18.16b, #0x4
     +0x9ec: orr     v2.16b, v2.16b, v21.16b
     +0x9f0: sub     v6.16b, v6.16b, v20.16b
     +0x9f4: orr     v1.16b, v3.16b, v1.16b
     +0x9f8: sub     v3.16b, v22.16b, v16.16b
     +0x9fc: orr     v4.16b, v4.16b, v17.16b
     +0xa00: str     q5, [x19, #1312]
     +0xa04: sub     v0.16b, v18.16b, v0.16b
     +0xa08: str     q2, [x19, #1328]
     +0xa0c: orr     v2.16b, v7.16b, v6.16b
     +0xa10: str     q1, [x19, #1344]
     +0xa14: str     q4, [x19, #1360]
     +0xa18: orr     v0.16b, v3.16b, v0.16b
     +0xa1c: str     q2, [x19, #1376]
     +0xa20: str     q0, [x19, #1392]
     +0xa24: add     x8, x22, #0xc20
     +0xa28: str     xzr, [sp, #5568]
     +0xa2c: ld2     {v4.4s-v5.4s}, [x9]
     +0xa30: add     x9, x22, #0xca0
     +0xa34: ld2     {v6.4s-v7.4s}, [x10]
     +0xa38: ld2     {v26.4s-v27.4s}, [x9]
     +0xa3c: add     x9, x22, #0xcc0
     +0xa40: add     x10, x22, #0xce0
     +0xa44: ld2     {v0.4s-v1.4s}, [x21]
     +0xa48: ld2     {v2.4s-v3.4s}, [x8]
     +0xa4c: add     x8, x22, #0xc80
     +0xa50: ld2     {v28.4s-v29.4s}, [x9]
     +0xa54: add     x9, x22, #0xd40
     +0xa58: ld2     {v30.4s-v31.4s}, [x10]
     +0xa5c: add     x10, x22, #0xd60
     +0xa60: uzp1    v18.8h, v4.8h, v6.8h
     +0xa64: uzp1    v20.8h, v5.8h, v7.8h
     +0xa68: ld2     {v24.4s-v25.4s}, [x8]
     +0xa6c: add     x8, x22, #0xd00
     +0xa70: ld2     {v8.4s-v9.4s}, [x9]
     +0xa74: uzp1    v19.8h, v0.8h, v2.8h
     +0xa78: uzp1    v21.8h, v1.8h, v3.8h
     +0xa7c: add     x9, x22, #0xde0
     +0xa80: uzp1    v0.8h, v28.8h, v30.8h
     +0xa84: uzp1    v4.8h, v29.8h, v31.8h
     +0xa88: ld2     {v10.4s-v11.4s}, [x10]
     +0xa8c: add     x10, x22, #0xee0
     +0xa90: ld2     {v16.4s-v17.4s}, [x8]
     +0xa94: add     x8, x22, #0xd20
     +0xa98: uzp1    v2.8h, v24.8h, v26.8h
     +0xa9c: ld2     {v22.4s-v23.4s}, [x8]
     +0xaa0: add     x8, x22, #0xd80
     +0xaa4: str     q0, [sp, #160]
     +0xaa8: uzp1    v0.8h, v25.8h, v27.8h
     +0xaac: uzp1    v26.16b, v19.16b, v18.16b
     +0xab0: ld2     {v24.4s-v25.4s}, [x8]
     +0xab4: add     x8, x22, #0xda0
     +0xab8: uzp1    v6.8h, v17.8h, v23.8h
     +0xabc: ld2     {v27.4s-v28.4s}, [x8]
     +0xac0: add     x8, x22, #0xdc0
     +0xac4: ld2     {v29.4s-v30.4s}, [x8]
     +0xac8: add     x8, x22, #0xe00
     +0xacc: stp     q0, q4, [sp, #64]
     +0xad0: uzp1    v0.8h, v8.8h, v10.8h
     +0xad4: uzp1    v7.8h, v24.8h, v27.8h
     +0xad8: stp     q0, q2, [sp, #112]
     +0xadc: uzp1    v0.8h, v16.8h, v22.8h
     +0xae0: ld2     {v22.4s-v23.4s}, [x10]
     +0xae4: add     x10, x22, #0xfc0
     +0xae8: str     q0, [sp, #96]
     +0xaec: uzp1    v0.8h, v9.8h, v11.8h
     +0xaf0: ld2     {v8.4s-v9.4s}, [x9]
     +0xaf4: add     x9, x22, #0xe40
     +0xaf8: ld2     {v10.4s-v11.4s}, [x8]
     +0xafc: add     x8, x22, #0xe20
     +0xb00: ld2     {v14.4s-v15.4s}, [x9]
     +0xb04: add     x9, x22, #0xec0
     +0xb08: ld2     {v12.4s-v13.4s}, [x8]
     +0xb0c: add     x8, x22, #0xe60
     +0xb10: ld2     {v2.4s-v3.4s}, [x9]
     +0xb14: add     x9, x22, #0xf40
     +0xb18: uzp1    v4.8h, v29.8h, v8.8h
     +0xb1c: uzp1    v30.8h, v30.8h, v9.8h
     +0xb20: uzp1    v29.16b, v21.16b, v20.16b
     +0xb24: uzp1    v20.8h, v25.8h, v28.8h
     +0xb28: str     q0, [sp, #48]
     +0xb2c: ld2     {v0.4s-v1.4s}, [x8]
     +0xb30: add     x8, x22, #0xe80
     +0xb34: uzp1    v19.8h, v10.8h, v12.8h
     +0xb38: uzp1    v24.8h, v11.8h, v13.8h
     +0xb3c: uzp1    v16.8h, v2.8h, v22.8h
     +0xb40: uzp1    v25.8h, v3.8h, v23.8h
     +0xb44: ld2     {v17.4s-v18.4s}, [x8]
     +0xb48: add     x8, x22, #0xea0
     +0xb4c: shl     v29.16b, v29.16b, #4
     +0xb50: stp     q6, q4, [sp, #16]
     +0xb54: uzp1    v31.8h, v14.8h, v0.8h
     +0xb58: uzp1    v21.8h, v15.8h, v1.8h
     +0xb5c: ld2     {v22.4s-v23.4s}, [x8]
     +0xb60: add     x8, x22, #0xf00
     +0xb64: ld2     {v8.4s-v9.4s}, [x9]
     +0xb68: add     x9, x22, #0xf20
     +0xb6c: ld2     {v27.4s-v28.4s}, [x8]
     +0xb70: add     x8, x22, #0xf60
     +0xb74: ld2     {v12.4s-v13.4s}, [x9]
     +0xb78: add     x9, x22, #0xfa0
     +0xb7c: ld2     {v10.4s-v11.4s}, [x8]
     +0xb80: add     x8, x22, #0xf80
     +0xb84: uzp1    v6.8h, v17.8h, v22.8h
     +0xb88: uzp1    v17.8h, v18.8h, v23.8h
     +0xb8c: uzp1    v21.16b, v24.16b, v21.16b
     +0xb90: uzp1    v19.16b, v19.16b, v31.16b
     +0xb94: ld2     {v14.4s-v15.4s}, [x10]
     +0xb98: ld2     {v0.4s-v1.4s}, [x11]
     +0xb9c: uzp1    v23.8h, v27.8h, v12.8h
     +0xba0: uzp1    v27.8h, v28.8h, v13.8h
     +0xba4: ld2     {v4.4s-v5.4s}, [x8]
     +0xba8: uzp1    v18.8h, v8.8h, v10.8h
     +0xbac: uzp1    v22.8h, v9.8h, v11.8h
     +0xbb0: movi    v10.16b, #0x40
     +0xbb4: movi    v9.16b, #0x4
     +0xbb8: uzp1    v6.16b, v6.16b, v16.16b
     +0xbbc: uzp1    v16.16b, v17.16b, v25.16b
     +0xbc0: add     x8, sp, #0x1, lsl #12
     +0xbc4: ld2     {v2.4s-v3.4s}, [x9]
     +0xbc8: add     x9, sp, #0x1, lsl #12
     +0xbcc: add     x8, x8, #0x5c0
     +0xbd0: add     x9, x9, #0x540
     +0xbd4: sub     v28.16b, v10.16b, v29.16b
     +0xbd8: uzp1    v29.8h, v14.8h, v0.8h
     +0xbdc: uzp1    v0.8h, v15.8h, v1.8h
     +0xbe0: sub     v26.16b, v9.16b, v26.16b
     +0xbe4: uzp1    v17.16b, v23.16b, v18.16b
     +0xbe8: uzp1    v18.16b, v27.16b, v22.16b
     +0xbec: shl     v16.16b, v16.16b, #4
     +0xbf0: sub     v19.16b, v9.16b, v19.16b
     +0xbf4: sub     v6.16b, v9.16b, v6.16b
     +0xbf8: add     x4, x9, #0x20
     +0xbfc: ldp     q8, q1, [sp, #64]
     +0xc00: shl     v18.16b, v18.16b, #4
     +0xc04: uzp1    v1.16b, v8.16b, v1.16b
     +0xc08: uzp1    v8.8h, v4.8h, v2.8h
     +0xc0c: uzp1    v2.8h, v5.8h, v3.8h
     +0xc10: orr     v5.16b, v28.16b, v26.16b
     +0xc14: ldr     q3, [sp, #48]
     +0xc18: ldr     q4, [sp, #16]
     +0xc1c: ldr     q26, [sp, #128]
     +0xc20: uzp1    v3.16b, v4.16b, v3.16b
     +0xc24: uzp1    v4.16b, v20.16b, v30.16b
     +0xc28: ldr     q20, [sp, #160]
     +0xc2c: shl     v1.16b, v1.16b, #4
     +0xc30: uzp1    v0.16b, v2.16b, v0.16b
     +0xc34: shl     v2.16b, v21.16b, #4
     +0xc38: uzp1    v20.16b, v26.16b, v20.16b
     +0xc3c: str     q5, [x19, #1408]
     +0xc40: sub     v5.16b, v9.16b, v17.16b
     +0xc44: ldp     q26, q24, [sp, #96]
     +0xc48: sub     v1.16b, v10.16b, v1.16b
     +0xc4c: shl     v3.16b, v3.16b, #4
     +0xc50: shl     v4.16b, v4.16b, #4
     +0xc54: shl     v0.16b, v0.16b, #4
     +0xc58: sub     v2.16b, v10.16b, v2.16b
     +0xc5c: uzp1    v24.16b, v26.16b, v24.16b
     +0xc60: sub     v20.16b, v9.16b, v20.16b
     +0xc64: ldr     q26, [sp, #32]
     +0xc68: sub     v3.16b, v10.16b, v3.16b
     +0xc6c: sub     v4.16b, v10.16b, v4.16b
     +0xc70: uzp1    v7.16b, v7.16b, v26.16b
     +0xc74: sub     v0.16b, v10.16b, v0.16b
     +0xc78: orr     v2.16b, v2.16b, v19.16b
     +0xc7c: orr     v1.16b, v1.16b, v20.16b
     +0xc80: uzp1    v20.16b, v8.16b, v29.16b
     +0xc84: sub     v21.16b, v9.16b, v24.16b
     +0xc88: str     q2, [x19, #1472]
     +0xc8c: sub     v7.16b, v9.16b, v7.16b
     +0xc90: str     q1, [x19, #1424]
     +0xc94: orr     v3.16b, v3.16b, v21.16b
     +0xc98: sub     v17.16b, v9.16b, v20.16b
     +0xc9c: orr     v4.16b, v4.16b, v7.16b
     +0xca0: sub     v7.16b, v10.16b, v16.16b
     +0xca4: sub     v16.16b, v10.16b, v18.16b
     +0xca8: orr     v0.16b, v0.16b, v17.16b
     +0xcac: str     q3, [x19, #1440]
     +0xcb0: orr     v1.16b, v7.16b, v6.16b
     +0xcb4: orr     v3.16b, v16.16b, v5.16b
     +0xcb8: str     q4, [x19, #1456]
     +0xcbc: str     q0, [x19, #1520]
     +0xcc0: str     q1, [x19, #1488]
     +0xcc4: str     q3, [x19, #1504]
     +0xcc8: mov     w8, #0xff
     +0xccc: strb    w8, [sp]
     +0xcd0: bl      <mldsa65_poly_uniform_eta_4x>
     +0xcd4: mov     w8, #0x1020
     +0xcd8: mov     w9, #0x1060
     +0xcdc: mov     w10, #0x1080
     +0xce0: add     x8, x22, x8
     +0xce4: add     x9, x22, x9
     +0xce8: add     x10, x22, x10
     +0xcec: ld2     {v2.4s-v3.4s}, [x8]
     +0xcf0: mov     w8, #0x1040
     +0xcf4: ld2     {v6.4s-v7.4s}, [x9]
     +0xcf8: add     x8, x22, x8
     +0xcfc: mov     w9, #0x10c0
     +0xd00: add     x21, x22, #0x100
     +0xd04: ld2     {v4.4s-v5.4s}, [x8]
     +0xd08: mov     w8, #0x10a0
     +0xd0c: add     x9, x22, x9
     +0xd10: add     x8, x22, x8
     +0xd14: add     x24, x22, #0x180
     +0xd18: add     x25, x22, #0x1a0
     +0xd1c: ld2     {v16.4s-v17.4s}, [x10]
     +0xd20: mov     w10, #0x10e0
     +0xd24: add     x26, x22, #0x1c0
     +0xd28: add     x10, x22, x10
     +0xd2c: add     x27, x22, #0x1e0
     +0xd30: add     x0, sp, #0xc0
     +0xd34: ld2     {v0.4s-v1.4s}, [x28]
     +0xd38: uzp1    v4.8h, v4.8h, v6.8h
     +0xd3c: uzp1    v24.8h, v5.8h, v7.8h
     +0xd40: add     x28, x22, #0x120
     +0xd44: add     x1, x22, #0x400
     +0xd48: add     x2, x22, #0x800
     +0xd4c: ld2     {v18.4s-v19.4s}, [x8]
     +0xd50: mov     w8, #0x1140
     +0xd54: add     x3, x22, #0xc00
     +0xd58: add     x8, x22, x8
     +0xd5c: mov     w5, wzr
     +0xd60: mov     w6, #0x1
     +0xd64: ld2     {v20.4s-v21.4s}, [x9]
     +0xd68: uzp1    v25.8h, v1.8h, v3.8h
     +0xd6c: uzp1    v0.8h, v0.8h, v2.8h
     +0xd70: mov     w9, #0x1160
     +0xd74: mov     w7, #0x2
     +0xd78: str     xzr, [sp, #5568]
     +0xd7c: ld2     {v22.4s-v23.4s}, [x10]
     +0xd80: uzp1    v2.8h, v16.8h, v18.8h
     +0xd84: uzp1    v27.8h, v17.8h, v19.8h
     +0xd88: add     x9, x22, x9
     +0xd8c: mov     w10, #0x1100
     +0xd90: uzp1    v0.16b, v0.16b, v4.16b
     +0xd94: movi    v4.16b, #0x4
     +0xd98: uzp1    v3.16b, v25.16b, v24.16b
     +0xd9c: ld2     {v16.4s-v17.4s}, [x9]
     +0xda0: mov     w9, #0x1180
     +0xda4: add     x10, x22, x10
     +0xda8: uzp1    v1.8h, v20.8h, v22.8h
     +0xdac: uzp1    v26.8h, v21.8h, v23.8h
     +0xdb0: ld2     {v18.4s-v19.4s}, [x10]
     +0xdb4: mov     w10, #0x11e0
     +0xdb8: sub     v0.16b, v4.16b, v0.16b
     +0xdbc: uzp1    v1.16b, v2.16b, v1.16b
     +0xdc0: uzp1    v5.16b, v27.16b, v26.16b
     +0xdc4: shl     v2.16b, v3.16b, #4
     +0xdc8: sub     v1.16b, v4.16b, v1.16b
     +0xdcc: movi    v4.16b, #0x40
     +0xdd0: shl     v3.16b, v5.16b, #4
     +0xdd4: sub     v2.16b, v4.16b, v2.16b
     +0xdd8: sub     v5.16b, v4.16b, v3.16b
     +0xddc: ld2     {v3.4s-v4.4s}, [x8]
     +0xde0: mov     w8, #0x1120
     +0xde4: add     x8, x22, x8
     +0xde8: ld2     {v20.4s-v21.4s}, [x8]
     +0xdec: add     x8, x22, x9
     +0xdf0: mov     w9, #0x11c0
     +0xdf4: ld2     {v22.4s-v23.4s}, [x8]
     +0xdf8: mov     w8, #0x11a0
     +0xdfc: orr     v0.16b, v2.16b, v0.16b
     +0xe00: add     x8, x22, x8
     +0xe04: orr     v2.16b, v5.16b, v1.16b
     +0xe08: ld2     {v24.4s-v25.4s}, [x8]
     +0xe0c: add     x8, x22, x9
     +0xe10: add     x9, x22, x10
     +0xe14: ld2     {v26.4s-v27.4s}, [x8]
     +0xe18: mov     w8, #0x1240
     +0xe1c: ld2     {v28.4s-v29.4s}, [x9]
     +0xe20: add     x8, x22, x8
     +0xe24: mov     w9, #0x1200
     +0xe28: mov     w10, #0x1260
     +0xe2c: ld2     {v30.4s-v31.4s}, [x8]
     +0xe30: mov     w8, #0x1220
     +0xe34: add     x9, x22, x9
     +0xe38: add     x8, x22, x8
     +0xe3c: add     x10, x22, x10
     +0xe40: ld2     {v10.4s-v11.4s}, [x9]
     +0xe44: ld2     {v12.4s-v13.4s}, [x8]
     +0xe48: mov     w8, #0x12c0
     +0xe4c: mov     w9, #0x12e0
     +0xe50: ld2     {v8.4s-v9.4s}, [x10]
     +0xe54: add     x8, x22, x8
     +0xe58: add     x9, x22, x9
     +0xe5c: mov     w10, #0x1280
     +0xe60: str     q0, [sp, #160]
     +0xe64: uzp1    v0.8h, v3.8h, v16.8h
     +0xe68: uzp1    v16.8h, v4.8h, v17.8h
     +0xe6c: uzp1    v7.8h, v26.8h, v28.8h
     +0xe70: uzp1    v4.8h, v27.8h, v29.8h
     +0xe74: ld2     {v27.4s-v28.4s}, [x8]
     +0xe78: ld2     {v14.4s-v15.4s}, [x9]
     +0xe7c: add     x8, x22, x10
     +0xe80: mov     w9, #0x12a0
     +0xe84: uzp1    v17.8h, v22.8h, v24.8h
     +0xe88: uzp1    v5.8h, v23.8h, v25.8h
     +0xe8c: ld2     {v23.4s-v24.4s}, [x8]
     +0xe90: add     x8, x22, x9
     +0xe94: mov     w9, #0x1320
     +0xe98: ld2     {v25.4s-v26.4s}, [x8]
     +0xe9c: mov     w8, #0x1300
     +0xea0: add     x9, x22, x9
     +0xea4: add     x8, x22, x8
     +0xea8: uzp1    v6.8h, v18.8h, v20.8h
     +0xeac: uzp1    v18.8h, v19.8h, v21.8h
     +0xeb0: uzp1    v1.8h, v30.8h, v8.8h
     +0xeb4: uzp1    v20.8h, v31.8h, v9.8h
     +0xeb8: uzp1    v22.8h, v27.8h, v14.8h
     +0xebc: uzp1    v29.8h, v28.8h, v15.8h
     +0xec0: ld2     {v27.4s-v28.4s}, [x8]
     +0xec4: ld2     {v30.4s-v31.4s}, [x9]
     +0xec8: mov     w8, #0x1340
     +0xecc: mov     w9, #0x1360
     +0xed0: uzp1    v21.8h, v11.8h, v13.8h
     +0xed4: stp     q0, q2, [sp, #112]
     +0xed8: add     x8, x22, x8
     +0xedc: add     x9, x22, x9
     +0xee0: uzp1    v0.8h, v10.8h, v12.8h
     +0xee4: mov     w10, #0x1380
     +0xee8: ld2     {v8.4s-v9.4s}, [x8]
     +0xeec: ld2     {v10.4s-v11.4s}, [x9]
     +0xef0: add     x10, x22, x10
     +0xef4: mov     w8, #0x13a0
     +0xef8: mov     w9, #0x13c0
     +0xefc: uzp1    v16.16b, v18.16b, v16.16b
     +0xf00: add     x8, x22, x8
     +0xf04: ldp     q19, q18, [sp, #112]
     +0xf08: add     x9, x22, x9
     +0xf0c: uzp1    v4.16b, v5.16b, v4.16b
     +0xf10: ld2     {v12.4s-v13.4s}, [x10]
     +0xf14: mov     w10, #0x13e0
     +0xf18: uzp1    v20.16b, v21.16b, v20.16b
     +0xf1c: uzp1    v6.16b, v6.16b, v19.16b
     +0xf20: add     x10, x22, x10
     +0xf24: uzp1    v21.8h, v8.8h, v10.8h
     +0xf28: ldr     q19, [sp, #160]
     +0xf2c: shl     v16.16b, v16.16b, #4
     +0xf30: stp     q0, q1, [sp, #80]
     +0xf34: ld2     {v14.4s-v15.4s}, [x8]
     +0xf38: add     x8, sp, #0x1, lsl #12
     +0xf3c: add     x8, x8, #0x5c0
     +0xf40: stp     q19, q18, [x19, #640]
     +0xf44: uzp1    v19.16b, v17.16b, v7.16b
     +0xf48: uzp1    v17.8h, v24.8h, v26.8h
     +0xf4c: uzp1    v18.8h, v23.8h, v25.8h
     +0xf50: uzp1    v23.8h, v9.8h, v11.8h
     +0xf54: ld2     {v2.4s-v3.4s}, [x9]
     +0xf58: uzp1    v24.8h, v28.8h, v31.8h
     +0xf5c: movi    v7.16b, #0x4
     +0xf60: uzp1    v25.8h, v13.8h, v15.8h
     +0xf64: uzp1    v26.8h, v27.8h, v30.8h
     +0xf68: movi    v28.16b, #0x40
     +0xf6c: ld2     {v0.4s-v1.4s}, [x10]
     +0xf70: add     x9, sp, #0x1, lsl #12
     +0xf74: uzp1    v18.16b, v18.16b, v22.16b
     +0xf78: uzp1    v17.16b, v17.16b, v29.16b
     +0xf7c: add     x9, x9, #0x540
     +0xf80: uzp1    v23.16b, v24.16b, v23.16b
     +0xf84: movi    v24.16b, #0x40
     +0xf88: sub     v6.16b, v7.16b, v6.16b
     +0xf8c: sub     v22.16b, v7.16b, v19.16b
     +0xf90: uzp1    v19.16b, v26.16b, v21.16b
     +0xf94: add     x4, x9, #0x20
     +0xf98: uzp1    v5.8h, v3.8h, v1.8h
     +0xf9c: uzp1    v0.8h, v2.8h, v0.8h
     +0xfa0: shl     v2.16b, v4.16b, #4
     +0xfa4: ldp     q4, q3, [sp, #80]
     +0xfa8: uzp1    v1.8h, v12.8h, v14.8h
     +0xfac: shl     v17.16b, v17.16b, #4
     +0xfb0: sub     v2.16b, v24.16b, v2.16b
     +0xfb4: uzp1    v3.16b, v4.16b, v3.16b
     +0xfb8: uzp1    v4.16b, v25.16b, v5.16b
     +0xfbc: sub     v5.16b, v24.16b, v16.16b
     +0xfc0: shl     v16.16b, v20.16b, #4
     +0xfc4: uzp1    v0.16b, v1.16b, v0.16b
     +0xfc8: shl     v20.16b, v23.16b, #4
     +0xfcc: orr     v2.16b, v2.16b, v22.16b
     +0xfd0: orr     v5.16b, v5.16b, v6.16b
     +0xfd4: sub     v6.16b, v7.16b, v18.16b
     +0xfd8: movi    v18.16b, #0x4
     +0xfdc: sub     v1.16b, v7.16b, v3.16b
     +0xfe0: sub     v3.16b, v24.16b, v16.16b
     +0xfe4: shl     v4.16b, v4.16b, #4
     +0xfe8: sub     v16.16b, v24.16b, v17.16b
     +0xfec: sub     v7.16b, v7.16b, v19.16b
     +0xff0: sub     v17.16b, v24.16b, v20.16b
     +0xff4: stp     q5, q2, [x19, #672]
     +0xff8: orr     v1.16b, v3.16b, v1.16b
     +0xffc: sub     v0.16b, v18.16b, v0.16b
    +0x1000: sub     v3.16b, v24.16b, v4.16b
    +0x1004: orr     v4.16b, v16.16b, v6.16b
    +0x1008: orr     v2.16b, v17.16b, v7.16b
    +0x100c: orr     v0.16b, v3.16b, v0.16b
    +0x1010: stp     q1, q4, [x19, #704]
    +0x1014: stp     q2, q0, [x19, #736]
    +0x1018: add     x8, x22, #0x40
    +0x101c: str     xzr, [sp, #5568]
    +0x1020: ld2     {v4.4s-v5.4s}, [x8]
    +0x1024: add     x8, x22, #0x60
    +0x1028: ld2     {v0.4s-v1.4s}, [x22]
    +0x102c: ld2     {v6.4s-v7.4s}, [x8]
    +0x1030: add     x8, x22, #0x80
    +0x1034: ld2     {v2.4s-v3.4s}, [x23]
    +0x1038: ld2     {v16.4s-v17.4s}, [x8]
    +0x103c: add     x8, x22, #0xa0
    +0x1040: ld2     {v18.4s-v19.4s}, [x8]
    +0x1044: add     x8, x22, #0xc0
    +0x1048: ld2     {v20.4s-v21.4s}, [x8]
    +0x104c: add     x8, x22, #0xe0
    +0x1050: ld2     {v22.4s-v23.4s}, [x8]
    +0x1054: uzp1    v24.8h, v5.8h, v7.8h
    +0x1058: uzp1    v25.8h, v1.8h, v3.8h
    +0x105c: uzp1    v4.8h, v4.8h, v6.8h
    +0x1060: uzp1    v0.8h, v0.8h, v2.8h
    +0x1064: add     x8, x22, #0x140
    +0x1068: uzp1    v27.8h, v17.8h, v19.8h
    +0x106c: uzp1    v2.8h, v16.8h, v18.8h
    +0x1070: ld2     {v16.4s-v17.4s}, [x28]
    +0x1074: ld2     {v18.4s-v19.4s}, [x24]
    +0x1078: uzp1    v26.8h, v21.8h, v23.8h
    +0x107c: uzp1    v1.8h, v20.8h, v22.8h
    +0x1080: uzp1    v3.16b, v25.16b, v24.16b
    +0x1084: uzp1    v0.16b, v0.16b, v4.16b
    +0x1088: movi    v4.16b, #0x4
    +0x108c: ld2     {v20.4s-v21.4s}, [x8]
    +0x1090: add     x8, x22, #0x160
    +0x1094: ld2     {v24.4s-v25.4s}, [x25]
    +0x1098: ld2     {v22.4s-v23.4s}, [x8]
    +0x109c: add     x8, x22, #0x240
    +0x10a0: uzp1    v5.16b, v27.16b, v26.16b
    +0x10a4: uzp1    v1.16b, v2.16b, v1.16b
    +0x10a8: shl     v2.16b, v3.16b, #4
    +0x10ac: sub     v0.16b, v4.16b, v0.16b
    +0x10b0: ld2     {v30.4s-v31.4s}, [x8]
    +0x10b4: add     x8, x22, #0x260
    +0x10b8: ld2     {v7.4s-v8.4s}, [x8]
    +0x10bc: add     x8, x22, #0x200
    +0x10c0: ld2     {v26.4s-v27.4s}, [x26]
    +0x10c4: sub     v2.16b, v28.16b, v2.16b
    +0x10c8: ld2     {v9.4s-v10.4s}, [x8]
    +0x10cc: add     x8, x22, #0x220
    +0x10d0: shl     v3.16b, v5.16b, #4
    +0x10d4: sub     v1.16b, v4.16b, v1.16b
    +0x10d8: ld2     {v5.4s-v6.4s}, [x21]
    +0x10dc: ld2     {v11.4s-v12.4s}, [x8]
    +0x10e0: add     x8, x22, #0x2c0
    +0x10e4: uzp1    v4.8h, v20.8h, v22.8h
    +0x10e8: orr     v0.16b, v2.16b, v0.16b
    +0x10ec: uzp1    v15.8h, v18.8h, v24.8h
    +0x10f0: uzp1    v18.8h, v19.8h, v25.8h
    +0x10f4: sub     v3.16b, v28.16b, v3.16b
    +0x10f8: ld2     {v28.4s-v29.4s}, [x27]
    +0x10fc: uzp1    v31.8h, v31.8h, v8.8h
    +0x1100: uzp1    v13.8h, v6.8h, v17.8h
    +0x1104: str     q0, [sp, #160]
    +0x1108: uzp1    v0.8h, v5.8h, v16.8h
    +0x110c: uzp1    v16.8h, v30.8h, v7.8h
    +0x1110: orr     v2.16b, v3.16b, v1.16b
    +0x1114: uzp1    v1.8h, v21.8h, v23.8h
    +0x1118: ld2     {v20.4s-v21.4s}, [x8]
    +0x111c: add     x8, x22, #0x2e0
    +0x1120: uzp1    v14.8h, v26.8h, v28.8h
    +0x1124: uzp1    v26.8h, v27.8h, v29.8h
    +0x1128: ld2     {v22.4s-v23.4s}, [x8]
    +0x112c: add     x8, x22, #0x280
    +0x1130: uzp1    v12.8h, v10.8h, v12.8h
    +0x1134: ld2     {v24.4s-v25.4s}, [x8]
    +0x1138: add     x8, x22, #0x2a0
    +0x113c: stp     q0, q2, [sp, #112]
    +0x1140: uzp1    v0.8h, v9.8h, v11.8h
    +0x1144: ldr     q17, [sp, #112]
    +0x1148: ld2     {v27.4s-v28.4s}, [x8]
    +0x114c: add     x8, x22, #0x300
    +0x1150: uzp1    v14.16b, v15.16b, v14.16b
    +0x1154: uzp1    v18.16b, v18.16b, v26.16b
    +0x1158: uzp1    v7.8h, v20.8h, v22.8h
    +0x115c: uzp1    v19.8h, v21.8h, v23.8h
    +0x1160: uzp1    v4.16b, v17.16b, v4.16b
    +0x1164: uzp1    v31.16b, v12.16b, v31.16b
    +0x1168: ld2     {v20.4s-v21.4s}, [x8]
    +0x116c: add     x8, x22, #0x320
    +0x1170: uzp1    v15.8h, v25.8h, v28.8h
    +0x1174: uzp1    v24.8h, v24.8h, v27.8h
    +0x1178: stp     q0, q1, [sp, #80]
    +0x117c: ldr     q17, [sp, #96]
    +0x1180: ld2     {v22.4s-v23.4s}, [x8]
    +0x1184: add     x8, x22, #0x340
    +0x1188: ld2     {v29.4s-v30.4s}, [x8]
    +0x118c: add     x8, x22, #0x360
    +0x1190: uzp1    v13.16b, v13.16b, v17.16b
    +0x1194: ldr     q0, [sp, #160]
    +0x1198: ld2     {v8.4s-v9.4s}, [x8]
    +0x119c: add     x8, x22, #0x380
    +0x11a0: uzp1    v19.16b, v15.16b, v19.16b
    +0x11a4: uzp1    v7.16b, v24.16b, v7.16b
    +0x11a8: uzp1    v27.8h, v21.8h, v23.8h
    +0x11ac: uzp1    v20.8h, v20.8h, v22.8h
    +0x11b0: movi    v22.16b, #0x40
    +0x11b4: ldr     q17, [sp, #128]
    +0x11b8: ld2     {v10.4s-v11.4s}, [x8]
    +0x11bc: add     x8, x22, #0x3a0
    +0x11c0: uzp1    v25.8h, v30.8h, v9.8h
    +0x11c4: shl     v13.16b, v13.16b, #4
    +0x11c8: uzp1    v29.8h, v29.8h, v8.8h
    +0x11cc: stp     q0, q17, [x19, #768]
    +0x11d0: movi    v17.16b, #0x4
    +0x11d4: ld2     {v2.4s-v3.4s}, [x8]
    +0x11d8: add     x8, x22, #0x3c0
    +0x11dc: ld2     {v5.4s-v6.4s}, [x8]
    +0x11e0: add     x8, x22, #0x3e0
    +0x11e4: uzp1    v21.16b, v27.16b, v25.16b
    +0x11e8: ld2     {v0.4s-v1.4s}, [x8]
    +0x11ec: add     x8, sp, #0x1, lsl #12
    +0x11f0: sub     v4.16b, v17.16b, v4.16b
    +0x11f4: sub     v23.16b, v17.16b, v14.16b
    +0x11f8: add     x8, x8, #0x5c0
    +0x11fc: uzp1    v28.8h, v11.8h, v3.8h
    +0x1200: uzp1    v26.8h, v6.8h, v1.8h
    +0x1204: uzp1    v0.8h, v5.8h, v0.8h
    +0x1208: uzp1    v1.8h, v10.8h, v2.8h
    +0x120c: shl     v2.16b, v18.16b, #4
    +0x1210: sub     v6.16b, v22.16b, v13.16b
    +0x1214: shl     v18.16b, v19.16b, #4
    +0x1218: uzp1    v19.16b, v20.16b, v29.16b
    +0x121c: shl     v20.16b, v21.16b, #4
    +0x1220: ldr     q3, [sp, #80]
    +0x1224: uzp1    v3.16b, v3.16b, v16.16b
    +0x1228: uzp1    v5.16b, v28.16b, v26.16b
    +0x122c: shl     v16.16b, v31.16b, #4
    +0x1230: uzp1    v0.16b, v1.16b, v0.16b
    +0x1234: orr     v4.16b, v6.16b, v4.16b
    +0x1238: sub     v6.16b, v17.16b, v7.16b
    +0x123c: sub     v7.16b, v22.16b, v18.16b
    +0x1240: movi    v18.16b, #0x4
    +0x1244: sub     v2.16b, v22.16b, v2.16b
    +0x1248: sub     v1.16b, v17.16b, v3.16b
    +0x124c: sub     v3.16b, v22.16b, v16.16b
    +0x1250: shl     v5.16b, v5.16b, #4
    +0x1254: orr     v2.16b, v2.16b, v23.16b
    +0x1258: sub     v16.16b, v17.16b, v19.16b
    +0x125c: sub     v17.16b, v22.16b, v20.16b
    +0x1260: sub     v0.16b, v18.16b, v0.16b
    +0x1264: orr     v1.16b, v3.16b, v1.16b
    +0x1268: sub     v3.16b, v22.16b, v5.16b
    +0x126c: orr     v5.16b, v7.16b, v6.16b
    +0x1270: stp     q4, q2, [x19, #800]
    +0x1274: orr     v2.16b, v17.16b, v16.16b
    +0x1278: orr     v0.16b, v3.16b, v0.16b
    +0x127c: stp     q1, q5, [x19, #832]
    +0x1280: stp     q2, q0, [x19, #864]
    +0x1284: add     x8, x22, #0x400
    +0x1288: str     xzr, [sp, #5568]
    +0x128c: ld2     {v0.4s-v1.4s}, [x8]
    +0x1290: add     x8, x22, #0x420
    +0x1294: ld2     {v2.4s-v3.4s}, [x8]
    +0x1298: add     x8, x22, #0x440
    +0x129c: ld2     {v4.4s-v5.4s}, [x8]
    +0x12a0: add     x8, x22, #0x460
    +0x12a4: ld2     {v16.4s-v17.4s}, [x8]
    +0x12a8: add     x8, x22, #0x4c0
    +0x12ac: ld2     {v19.4s-v20.4s}, [x8]
    +0x12b0: add     x8, x22, #0x4e0
    +0x12b4: ld2     {v21.4s-v22.4s}, [x8]
    +0x12b8: add     x8, x22, #0x480
    +0x12bc: uzp1    v7.8h, v0.8h, v2.8h
    +0x12c0: ld2     {v23.4s-v24.4s}, [x8]
    +0x12c4: add     x8, x22, #0x4a0
    +0x12c8: uzp1    v18.8h, v1.8h, v3.8h
    +0x12cc: ld2     {v25.4s-v26.4s}, [x8]
    +0x12d0: add     x8, x22, #0x540
    +0x12d4: uzp1    v6.8h, v4.8h, v16.8h
    +0x12d8: ld2     {v27.4s-v28.4s}, [x8]
    +0x12dc: add     x8, x22, #0x560
    +0x12e0: uzp1    v17.8h, v5.8h, v17.8h
    +0x12e4: uzp1    v0.8h, v19.8h, v21.8h
    +0x12e8: ld2     {v29.4s-v30.4s}, [x8]
    +0x12ec: uzp1    v4.8h, v20.8h, v22.8h
    +0x12f0: add     x8, x22, #0x500
    +0x12f4: uzp1    v2.8h, v23.8h, v25.8h
    +0x12f8: ld2     {v19.4s-v20.4s}, [x8]
    +0x12fc: add     x8, x22, #0x520
    +0x1300: ld2     {v21.4s-v22.4s}, [x8]
    +0x1304: add     x8, x22, #0x5c0
    +0x1308: str     q0, [sp, #160]
    +0x130c: uzp1    v0.8h, v24.8h, v26.8h
    +0x1310: ld2     {v23.4s-v24.4s}, [x8]
    +0x1314: add     x8, x22, #0x5e0
    +0x1318: ld2     {v25.4s-v26.4s}, [x8]
    +0x131c: add     x8, x22, #0x580
    +0x1320: uzp1    v20.8h, v20.8h, v22.8h
    +0x1324: stp     q0, q4, [sp, #80]
    +0x1328: uzp1    v0.8h, v27.8h, v29.8h
    +0x132c: uzp1    v4.16b, v18.16b, v17.16b
    +0x1330: uzp1    v18.16b, v7.16b, v6.16b
    +0x1334: uzp1    v6.8h, v23.8h, v25.8h
    +0x1338: uzp1    v22.8h, v24.8h, v26.8h
    +0x133c: stp     q0, q2, [sp, #112]
    +0x1340: uzp1    v2.8h, v28.8h, v30.8h
    +0x1344: ld2     {v27.4s-v28.4s}, [x8]
    +0x1348: add     x8, x22, #0x5a0
    +0x134c: uzp1    v0.8h, v19.8h, v21.8h
    +0x1350: shl     v4.16b, v4.16b, #4
    +0x1354: ld2     {v29.4s-v30.4s}, [x8]
    +0x1358: add     x8, x22, #0x600
    +0x135c: ld2     {v8.4s-v9.4s}, [x8]
    +0x1360: add     x8, x22, #0x620
    +0x1364: ld2     {v10.4s-v11.4s}, [x8]
    +0x1368: add     x8, x22, #0x640
    +0x136c: ld2     {v12.4s-v13.4s}, [x8]
    +0x1370: add     x8, x22, #0x660
    +0x1374: stp     q0, q2, [sp, #48]
    +0x1378: uzp1    v5.8h, v27.8h, v29.8h
    +0x137c: uzp1    v23.8h, v28.8h, v30.8h
    +0x1380: ld2     {v14.4s-v15.4s}, [x8]
    +0x1384: add     x8, x22, #0x6c0
    +0x1388: uzp1    v21.8h, v8.8h, v10.8h
    +0x138c: uzp1    v26.8h, v9.8h, v11.8h
    +0x1390: ld2     {v2.4s-v3.4s}, [x8]
    +0x1394: add     x8, x22, #0x6e0
    +0x1398: uzp1    v31.8h, v12.8h, v14.8h
    +0x139c: uzp1    v24.8h, v13.8h, v15.8h
    +0x13a0: stp     q5, q6, [sp, #16]
    +0x13a4: ld2     {v0.4s-v1.4s}, [x8]
    +0x13a8: add     x8, x22, #0x680
    +0x13ac: ld2     {v27.4s-v28.4s}, [x8]
    +0x13b0: add     x8, x22, #0x6a0
    +0x13b4: ld2     {v29.4s-v30.4s}, [x8]
    +0x13b8: add     x8, x22, #0x740
    +0x13bc: uzp1    v21.16b, v21.16b, v31.16b
    +0x13c0: ld2     {v8.4s-v9.4s}, [x8]
    +0x13c4: add     x8, x22, #0x760
    +0x13c8: uzp1    v25.8h, v2.8h, v0.8h
    +0x13cc: uzp1    v19.8h, v3.8h, v1.8h
    +0x13d0: ld2     {v10.4s-v11.4s}, [x8]
    +0x13d4: add     x8, x22, #0x700
    +0x13d8: uzp1    v5.8h, v27.8h, v29.8h
    +0x13dc: uzp1    v27.8h, v28.8h, v30.8h
    +0x13e0: ld2     {v16.4s-v17.4s}, [x8]
    +0x13e4: add     x8, x22, #0x720
    +0x13e8: uzp1    v28.8h, v8.8h, v10.8h
    +0x13ec: uzp1    v29.8h, v9.8h, v11.8h
    +0x13f0: movi    v10.16b, #0x4
    +0x13f4: movi    v9.16b, #0x40
    +0x13f8: ld2     {v12.4s-v13.4s}, [x8]
    +0x13fc: add     x8, x22, #0x7c0
    +0x1400: uzp1    v19.16b, v27.16b, v19.16b
    +0x1404: uzp1    v5.16b, v5.16b, v25.16b
    +0x1408: ld2     {v6.4s-v7.4s}, [x8]
    +0x140c: add     x8, x22, #0x7e0
    +0x1410: sub     v21.16b, v10.16b, v21.16b
    +0x1414: ld2     {v14.4s-v15.4s}, [x8]
    +0x1418: add     x8, x22, #0x780
    +0x141c: uzp1    v30.8h, v16.8h, v12.8h
    +0x1420: uzp1    v16.8h, v17.8h, v13.8h
    +0x1424: sub     v17.16b, v10.16b, v18.16b
    +0x1428: sub     v4.16b, v9.16b, v4.16b
    +0x142c: shl     v19.16b, v19.16b, #4
    +0x1430: sub     v5.16b, v10.16b, v5.16b
    +0x1434: ld2     {v2.4s-v3.4s}, [x8]
    +0x1438: add     x8, x22, #0x7a0
    +0x143c: uzp1    v18.8h, v6.8h, v14.8h
    +0x1440: uzp1    v6.8h, v7.8h, v15.8h
    +0x1444: ld2     {v0.4s-v1.4s}, [x8]
    +0x1448: uzp1    v16.16b, v16.16b, v29.16b
    +0x144c: add     x8, sp, #0x1, lsl #12
    +0x1450: add     x8, x8, #0x5c0
    +0x1454: ldp     q8, q7, [sp, #80]
    +0x1458: uzp1    v7.16b, v8.16b, v7.16b
    +0x145c: uzp1    v8.8h, v2.8h, v0.8h
    +0x1460: uzp1    v0.8h, v3.8h, v1.8h
    +0x1464: orr     v3.16b, v4.16b, v17.16b
    +0x1468: uzp1    v2.16b, v23.16b, v22.16b
    +0x146c: shl     v16.16b, v16.16b, #4
    +0x1470: ldr     q1, [sp, #64]
    +0x1474: ldr     q4, [sp, #160]
    +0x1478: ldp     q22, q23, [sp, #32]
    +0x147c: uzp1    v1.16b, v20.16b, v1.16b
    +0x1480: shl     v7.16b, v7.16b, #4
    +0x1484: uzp1    v0.16b, v0.16b, v6.16b
    +0x1488: ldp     q20, q17, [sp, #112]
    +0x148c: shl     v2.16b, v2.16b, #4
    +0x1490: sub     v16.16b, v9.16b, v16.16b
    +0x1494: sub     v7.16b, v9.16b, v7.16b
    +0x1498: uzp1    v4.16b, v17.16b, v4.16b
    +0x149c: uzp1    v20.16b, v23.16b, v20.16b
    +0x14a0: ldr     q23, [sp, #16]
    +0x14a4: uzp1    v17.16b, v26.16b, v24.16b
    +0x14a8: shl     v1.16b, v1.16b, #4
    +0x14ac: sub     v2.16b, v9.16b, v2.16b
    +0x14b0: uzp1    v22.16b, v23.16b, v22.16b
    +0x14b4: uzp1    v23.16b, v30.16b, v28.16b
    +0x14b8: shl     v0.16b, v0.16b, #4
    +0x14bc: sub     v4.16b, v10.16b, v4.16b
    +0x14c0: sub     v1.16b, v9.16b, v1.16b
    +0x14c4: shl     v6.16b, v17.16b, #4
    +0x14c8: sub     v17.16b, v10.16b, v20.16b
    +0x14cc: sub     v0.16b, v9.16b, v0.16b
    +0x14d0: sub     v20.16b, v10.16b, v22.16b
    +0x14d4: orr     v4.16b, v7.16b, v4.16b
    +0x14d8: uzp1    v7.16b, v8.16b, v18.16b
    +0x14dc: sub     v6.16b, v9.16b, v6.16b
    +0x14e0: orr     v1.16b, v1.16b, v17.16b
    +0x14e4: sub     v17.16b, v9.16b, v19.16b
    +0x14e8: orr     v2.16b, v2.16b, v20.16b
    +0x14ec: stp     q3, q4, [x19, #896]
    +0x14f0: sub     v3.16b, v10.16b, v23.16b
    +0x14f4: sub     v7.16b, v10.16b, v7.16b
    +0x14f8: orr     v6.16b, v6.16b, v21.16b
    +0x14fc: orr     v4.16b, v17.16b, v5.16b
    +0x1500: stp     q1, q2, [x19, #928]
    +0x1504: orr     v1.16b, v16.16b, v3.16b
    +0x1508: orr     v0.16b, v0.16b, v7.16b
    +0x150c: stp     q6, q4, [x19, #960]
    +0x1510: stp     q1, q0, [x19, #992]
    +0x1514: mov     w8, #0x3
    +0x1518: strb    w8, [sp]
    +0x151c: bl      <mldsa65_poly_uniform_eta_4x>
    +0x1520: add     x8, x22, #0x40
    +0x1524: ld2     {v0.4s-v1.4s}, [x24]
    +0x1528: add     x0, sp, #0xc0
    +0x152c: str     xzr, [sp, #5568]
    +0x1530: ld2     {v9.4s-v10.4s}, [x8]
    +0x1534: add     x8, x22, #0x60
    +0x1538: ld2     {v11.4s-v12.4s}, [x8]
    +0x153c: add     x8, x22, #0x80
    +0x1540: ld2     {v29.4s-v30.4s}, [x23]
    +0x1544: ld2     {v25.4s-v26.4s}, [x8]
    +0x1548: add     x8, x22, #0xa0
    +0x154c: ld2     {v16.4s-v17.4s}, [x21]
    +0x1550: ld2     {v27.4s-v28.4s}, [x8]
    +0x1554: add     x8, x22, #0xc0
    +0x1558: ld2     {v18.4s-v19.4s}, [x28]
    +0x155c: ld2     {v13.4s-v14.4s}, [x8]
    +0x1560: add     x8, x22, #0xe0
    +0x1564: ld2     {v4.4s-v5.4s}, [x26]
    +0x1568: uzp1    v15.8h, v9.8h, v11.8h
    +0x156c: uzp1    v31.8h, v10.8h, v12.8h
    +0x1570: ld2     {v2.4s-v3.4s}, [x8]
    +0x1574: add     x8, x22, #0x140
    +0x1578: ld2     {v6.4s-v7.4s}, [x27]
    +0x157c: uzp1    v12.8h, v26.8h, v28.8h
    +0x1580: ld2     {v21.4s-v22.4s}, [x8]
    +0x1584: add     x8, x22, #0x160
    +0x1588: ld2     {v23.4s-v24.4s}, [x8]
    +0x158c: add     x8, sp, #0xa0
    +0x1590: uzp1    v9.8h, v14.8h, v3.8h
    +0x1594: st1     {v0.2d-v1.2d}, [x8]
    +0x1598: add     x8, sp, #0x80
    +0x159c: ld2     {v0.4s-v1.4s}, [x25]
    +0x15a0: st1     {v0.2d-v1.2d}, [x8]
    +0x15a4: add     x8, x22, #0x200
    +0x15a8: ld2     {v0.4s-v1.4s}, [x22]
    +0x15ac: ld2     {v10.4s-v11.4s}, [x8]
    +0x15b0: add     x8, x22, #0x220
    +0x15b4: uzp1    v8.8h, v1.8h, v30.8h
    +0x15b8: uzp1    v30.8h, v0.8h, v29.8h
    +0x15bc: uzp1    v29.8h, v13.8h, v2.8h
    +0x15c0: uzp1    v3.8h, v21.8h, v23.8h
    +0x15c4: uzp1    v2.8h, v22.8h, v24.8h
    +0x15c8: uzp1    v0.8h, v25.8h, v27.8h
    +0x15cc: uzp1    v25.8h, v4.8h, v6.8h
    +0x15d0: uzp1    v4.8h, v5.8h, v7.8h
    +0x15d4: movi    v28.16b, #0x4
    +0x15d8: ld2     {v26.4s-v27.4s}, [x8]
    +0x15dc: add     x8, x22, #0x240
    +0x15e0: uzp1    v1.16b, v8.16b, v31.16b
    +0x15e4: ld2     {v13.4s-v14.4s}, [x8]
    +0x15e8: add     x8, x22, #0x260
    +0x15ec: uzp1    v29.16b, v0.16b, v29.16b
    +0x15f0: stp     q3, q2, [sp, #96]
    +0x15f4: uzp1    v3.8h, v16.8h, v18.8h
    +0x15f8: uzp1    v2.16b, v12.16b, v9.16b
    +0x15fc: stp     q4, q3, [sp, #48]
    +0x1600: ld2     {v20.4s-v21.4s}, [x8]
    +0x1604: add     x8, x22, #0x280
    +0x1608: uzp1    v12.8h, v10.8h, v26.8h
    +0x160c: uzp1    v26.8h, v11.8h, v27.8h
    +0x1610: shl     v8.16b, v1.16b, #4
    +0x1614: uzp1    v3.8h, v17.8h, v19.8h
    +0x1618: ld2     {v17.4s-v18.4s}, [x8]
    +0x161c: add     x8, x22, #0x2a0
    +0x1620: shl     v9.16b, v2.16b, #4
    +0x1624: uzp1    v22.8h, v14.8h, v21.8h
    +0x1628: ld2     {v23.4s-v24.4s}, [x8]
    +0x162c: add     x8, x22, #0x2c0
    +0x1630: str     q3, [sp, #80]
    +0x1634: uzp1    v3.16b, v30.16b, v15.16b
    +0x1638: ld2     {v30.4s-v31.4s}, [x8]
    +0x163c: add     x8, sp, #0xa0
    +0x1640: uzp1    v22.16b, v26.16b, v22.16b
    +0x1644: uzp1    v17.8h, v17.8h, v23.8h
    +0x1648: ldr     q23, [sp, #80]
    +0x164c: ld1     {v0.2d-v1.2d}, [x8]
    +0x1650: add     x8, sp, #0x80
    +0x1654: ld1     {v4.2d-v5.2d}, [x8]
    +0x1658: add     x8, x22, #0x2e0
    +0x165c: ld2     {v15.4s-v16.4s}, [x8]
    +0x1660: add     x8, x22, #0x300
    +0x1664: ld2     {v6.4s-v7.4s}, [x8]
    +0x1668: add     x8, x22, #0x320
    +0x166c: uzp1    v2.8h, v0.8h, v4.8h
    +0x1670: uzp1    v19.8h, v1.8h, v5.8h
    +0x1674: uzp1    v0.8h, v13.8h, v20.8h
    +0x1678: movi    v1.16b, #0x40
    +0x167c: uzp1    v11.8h, v31.8h, v16.8h
    +0x1680: str     q0, [sp, #160]
    +0x1684: movi    v0.16b, #0x4
    +0x1688: sub     v21.16b, v1.16b, v8.16b
    +0x168c: sub     v8.16b, v1.16b, v9.16b
    +0x1690: str     q2, [sp, #32]
    +0x1694: ld2     {v9.4s-v10.4s}, [x8]
    +0x1698: add     x8, x22, #0x340
    +0x169c: ld2     {v13.4s-v14.4s}, [x8]
    +0x16a0: add     x8, x22, #0x360
    +0x16a4: sub     v20.16b, v0.16b, v3.16b
    +0x16a8: sub     v29.16b, v0.16b, v29.16b
    +0x16ac: uzp1    v6.8h, v6.8h, v9.8h
    +0x16b0: orr     v20.16b, v21.16b, v20.16b
    +0x16b4: orr     v27.16b, v8.16b, v29.16b
    +0x16b8: uzp1    v21.8h, v30.8h, v15.8h
    +0x16bc: ld2     {v30.4s-v31.4s}, [x8]
    +0x16c0: add     x8, x22, #0x380
    +0x16c4: ld2     {v4.4s-v5.4s}, [x8]
    +0x16c8: add     x8, x22, #0x3a0
    +0x16cc: stp     q20, q27, [x19, #128]
    +0x16d0: ldr     q20, [sp, #96]
    +0x16d4: ld2     {v15.4s-v16.4s}, [x8]
    +0x16d8: add     x8, x22, #0x3c0
    +0x16dc: uzp1    v17.16b, v17.16b, v21.16b
    +0x16e0: ldp     q27, q29, [sp, #48]
    +0x16e4: ld2     {v2.4s-v3.4s}, [x8]
    +0x16e8: add     x8, x22, #0x3e0
    +0x16ec: uzp1    v8.8h, v5.8h, v16.8h
    +0x16f0: ld2     {v0.4s-v1.4s}, [x8]
    +0x16f4: add     x8, sp, #0x1, lsl #12
    +0x16f8: uzp1    v20.16b, v29.16b, v20.16b
    +0x16fc: uzp1    v29.8h, v18.8h, v24.8h
    +0x1700: uzp1    v24.8h, v14.8h, v31.8h
    +0x1704: uzp1    v19.16b, v19.16b, v27.16b
    +0x1708: add     x8, x8, #0x5c0
    +0x170c: ldr     q18, [sp, #112]
    +0x1710: uzp1    v18.16b, v23.16b, v18.16b
    +0x1714: uzp1    v27.8h, v3.8h, v1.8h
    +0x1718: uzp1    v0.8h, v2.8h, v0.8h
    +0x171c: uzp1    v26.16b, v29.16b, v11.16b
    +0x1720: uzp1    v29.8h, v13.8h, v30.8h
    +0x1724: uzp1    v1.8h, v4.8h, v15.8h
    +0x1728: shl     v2.16b, v19.16b, #4
    +0x172c: shl     v16.16b, v22.16b, #4
    +0x1730: sub     v20.16b, v28.16b, v20.16b
    +0x1734: ldr     q23, [sp, #32]
    +0x1738: ldr     q3, [sp, #160]
    +0x173c: uzp1    v4.16b, v8.16b, v27.16b
    +0x1740: shl     v18.16b, v18.16b, #4
    +0x1744: uzp1    v23.16b, v23.16b, v25.16b
    +0x1748: uzp1    v25.8h, v7.8h, v10.8h
    +0x174c: uzp1    v3.16b, v12.16b, v3.16b
    +0x1750: uzp1    v6.16b, v6.16b, v29.16b
    +0x1754: uzp1    v0.16b, v1.16b, v0.16b
    +0x1758: shl     v19.16b, v26.16b, #4
    +0x175c: shl     v4.16b, v4.16b, #4
    +0x1760: uzp1    v7.16b, v25.16b, v24.16b
    +0x1764: movi    v24.16b, #0x40
    +0x1768: sub     v1.16b, v28.16b, v3.16b
    +0x176c: sub     v6.16b, v28.16b, v6.16b
    +0x1770: sub     v0.16b, v28.16b, v0.16b
    +0x1774: sub     v5.16b, v24.16b, v18.16b
    +0x1778: sub     v18.16b, v28.16b, v23.16b
    +0x177c: sub     v2.16b, v24.16b, v2.16b
    +0x1780: shl     v7.16b, v7.16b, #4
    +0x1784: sub     v3.16b, v24.16b, v16.16b
    +0x1788: sub     v16.16b, v28.16b, v17.16b
    +0x178c: sub     v17.16b, v24.16b, v19.16b
    +0x1790: orr     v5.16b, v5.16b, v20.16b
    +0x1794: orr     v2.16b, v2.16b, v18.16b
    +0x1798: sub     v7.16b, v24.16b, v7.16b
    +0x179c: orr     v1.16b, v3.16b, v1.16b
    +0x17a0: sub     v3.16b, v24.16b, v4.16b
    +0x17a4: orr     v4.16b, v17.16b, v16.16b
    +0x17a8: stp     q5, q2, [x19, #160]
    +0x17ac: orr     v2.16b, v7.16b, v6.16b
    +0x17b0: orr     v0.16b, v3.16b, v0.16b
    +0x17b4: stp     q1, q4, [x19, #192]
    +0x17b8: stp     q2, q0, [x19, #224]
    +0x17bc: add     x8, x22, #0x400
    +0x17c0: str     xzr, [sp, #5568]
    +0x17c4: ld2     {v0.4s-v1.4s}, [x8]
    +0x17c8: add     x8, x22, #0x440
    +0x17cc: ld2     {v16.4s-v17.4s}, [x8]
    +0x17d0: add     x8, x22, #0x460
    +0x17d4: ld2     {v25.4s-v26.4s}, [x8]
    +0x17d8: add     x8, x22, #0x420
    +0x17dc: ld2     {v6.4s-v7.4s}, [x8]
    +0x17e0: add     x8, x22, #0x480
    +0x17e4: ld2     {v2.4s-v3.4s}, [x8]
    +0x17e8: add     x8, x22, #0x4a0
    +0x17ec: ld2     {v4.4s-v5.4s}, [x8]
    +0x17f0: add     x8, x22, #0x4c0
    +0x17f4: ld2     {v29.4s-v30.4s}, [x8]
    +0x17f8: add     x8, x22, #0x4e0
    +0x17fc: uzp1    v18.8h, v16.8h, v25.8h
    +0x1800: ld2     {v8.4s-v9.4s}, [x8]
    +0x1804: add     x8, x22, #0x500
    +0x1808: uzp1    v16.8h, v17.8h, v26.8h
    +0x180c: ld2     {v23.4s-v24.4s}, [x8]
    +0x1810: add     x8, x22, #0x520
    +0x1814: uzp1    v17.8h, v1.8h, v7.8h
    +0x1818: ld2     {v27.4s-v28.4s}, [x8]
    +0x181c: add     x8, x22, #0x540
    +0x1820: uzp1    v31.8h, v0.8h, v6.8h
    +0x1824: ld2     {v10.4s-v11.4s}, [x8]
    +0x1828: add     x8, x22, #0x560
    +0x182c: uzp1    v7.8h, v3.8h, v5.8h
    +0x1830: uzp1    v6.8h, v30.8h, v9.8h
    +0x1834: uzp1    v8.8h, v29.8h, v8.8h
    +0x1838: uzp1    v4.8h, v2.8h, v4.8h
    +0x183c: ld2     {v12.4s-v13.4s}, [x8]
    +0x1840: add     x8, x22, #0x580
    +0x1844: uzp1    v5.16b, v17.16b, v16.16b
    +0x1848: str     q18, [sp, #80]
    +0x184c: ld2     {v19.4s-v20.4s}, [x8]
    +0x1850: add     x8, x22, #0x5a0
    +0x1854: ld2     {v21.4s-v22.4s}, [x8]
    +0x1858: add     x8, x22, #0x5c0
    +0x185c: uzp1    v8.16b, v4.16b, v8.16b
    +0x1860: ld2     {v14.4s-v15.4s}, [x8]
    +0x1864: add     x8, x22, #0x5e0
    +0x1868: uzp1    v16.8h, v11.8h, v13.8h
    +0x186c: uzp1    v17.8h, v10.8h, v12.8h
    +0x1870: shl     v5.16b, v5.16b, #4
    +0x1874: ld2     {v0.4s-v1.4s}, [x8]
    +0x1878: add     x8, x22, #0x600
    +0x187c: uzp1    v4.8h, v20.8h, v22.8h
    +0x1880: movi    v22.16b, #0x4
    +0x1884: ld2     {v25.4s-v26.4s}, [x8]
    +0x1888: add     x8, x22, #0x620
    +0x188c: str     q16, [sp, #160]
    +0x1890: uzp1    v16.16b, v7.16b, v6.16b
    +0x1894: uzp1    v6.8h, v23.8h, v27.8h
    +0x1898: uzp1    v9.8h, v14.8h, v0.8h
    +0x189c: uzp1    v10.8h, v15.8h, v1.8h
    +0x18a0: movi    v1.16b, #0x40
    +0x18a4: ld2     {v29.4s-v30.4s}, [x8]
    +0x18a8: add     x8, x22, #0x640
    +0x18ac: ld2     {v2.4s-v3.4s}, [x8]
    +0x18b0: add     x8, x22, #0x660
    +0x18b4: shl     v16.16b, v16.16b, #4
    +0x18b8: str     q6, [sp, #96]
    +0x18bc: uzp1    v6.8h, v24.8h, v28.8h
    +0x18c0: sub     v5.16b, v1.16b, v5.16b
    +0x18c4: uzp1    v24.8h, v19.8h, v21.8h
    +0x18c8: ldr     q23, [sp, #80]
    +0x18cc: ld2     {v12.4s-v13.4s}, [x8]
    +0x18d0: add     x8, x22, #0x680
    +0x18d4: uzp1    v23.16b, v31.16b, v23.16b
    +0x18d8: sub     v16.16b, v1.16b, v16.16b
    +0x18dc: stp     q6, q17, [sp, #112]
    +0x18e0: ld2     {v6.4s-v7.4s}, [x8]
    +0x18e4: add     x8, x22, #0x6a0
    +0x18e8: ld2     {v17.4s-v18.4s}, [x8]
    +0x18ec: add     x8, x22, #0x6c0
    +0x18f0: uzp1    v0.8h, v2.8h, v12.8h
    +0x18f4: uzp1    v11.8h, v3.8h, v13.8h
    +0x18f8: ld2     {v14.4s-v15.4s}, [x8]
    +0x18fc: add     x8, x22, #0x6e0
    +0x1900: ld2     {v19.4s-v20.4s}, [x8]
    +0x1904: add     x8, x22, #0x700
    +0x1908: uzp1    v6.8h, v6.8h, v17.8h
    +0x190c: ld2     {v27.4s-v28.4s}, [x8]
    +0x1910: add     x8, x22, #0x720
    +0x1914: stp     q4, q0, [sp, #64]
    +0x1918: movi    v0.16b, #0x4
    +0x191c: uzp1    v4.8h, v26.8h, v30.8h
    +0x1920: uzp1    v31.8h, v14.8h, v19.8h
    +0x1924: uzp1    v19.8h, v15.8h, v20.8h
    +0x1928: sub     v3.16b, v0.16b, v23.16b
    +0x192c: sub     v23.16b, v0.16b, v8.16b
    +0x1930: uzp1    v8.8h, v25.8h, v29.8h
    +0x1934: uzp1    v4.16b, v4.16b, v11.16b
    +0x1938: ld2     {v29.4s-v30.4s}, [x8]
    +0x193c: add     x8, x22, #0x740
    +0x1940: uzp1    v6.16b, v6.16b, v31.16b
    +0x1944: ld2     {v12.4s-v13.4s}, [x8]
    +0x1948: add     x8, x22, #0x760
    +0x194c: orr     v5.16b, v5.16b, v3.16b
    +0x1950: orr     v16.16b, v16.16b, v23.16b
    +0x1954: ldr     q23, [sp, #96]
    +0x1958: ld2     {v14.4s-v15.4s}, [x8]
    +0x195c: add     x8, x22, #0x780
    +0x1960: uzp1    v27.8h, v27.8h, v29.8h
    +0x1964: shl     v4.16b, v4.16b, #4
    +0x1968: ld2     {v2.4s-v3.4s}, [x8]
    +0x196c: add     x8, x22, #0x7a0
    +0x1970: sub     v6.16b, v22.16b, v6.16b
    +0x1974: stp     q5, q16, [x19, #256]
    +0x1978: ldp     q16, q5, [sp, #112]
    +0x197c: ld2     {v20.4s-v21.4s}, [x8]
    +0x1980: add     x8, x22, #0x7c0
    +0x1984: uzp1    v17.8h, v13.8h, v15.8h
    +0x1988: ld2     {v25.4s-v26.4s}, [x8]
    +0x198c: add     x8, x22, #0x7e0
    +0x1990: uzp1    v5.16b, v23.16b, v5.16b
    +0x1994: uzp1    v23.8h, v7.8h, v18.8h
    +0x1998: uzp1    v18.8h, v28.8h, v30.8h
    +0x199c: ldr     q7, [sp, #160]
    +0x19a0: ld2     {v0.4s-v1.4s}, [x8]
    +0x19a4: add     x8, sp, #0x1, lsl #12
    +0x19a8: add     x8, x8, #0x5c0
    +0x19ac: uzp1    v7.16b, v16.16b, v7.16b
    +0x19b0: uzp1    v16.16b, v24.16b, v9.16b
    +0x19b4: ldr     q24, [sp, #64]
    +0x19b8: uzp1    v19.16b, v23.16b, v19.16b
    +0x19bc: uzp1    v23.8h, v12.8h, v14.8h
    +0x19c0: uzp1    v17.16b, v18.16b, v17.16b
    +0x19c4: uzp1    v24.16b, v24.16b, v10.16b
    +0x19c8: uzp1    v9.8h, v26.8h, v1.8h
    +0x19cc: uzp1    v10.8h, v3.8h, v21.8h
    +0x19d0: uzp1    v0.8h, v25.8h, v0.8h
    +0x19d4: uzp1    v1.8h, v2.8h, v20.8h
    +0x19d8: movi    v21.16b, #0x40
    +0x19dc: shl     v7.16b, v7.16b, #4
    +0x19e0: sub     v5.16b, v22.16b, v5.16b
    +0x19e4: sub     v16.16b, v22.16b, v16.16b
    +0x19e8: uzp1    v20.16b, v27.16b, v23.16b
    +0x19ec: shl     v19.16b, v19.16b, #4
    +0x19f0: shl     v17.16b, v17.16b, #4
    +0x19f4: uzp1    v18.16b, v10.16b, v9.16b
    +0x19f8: shl     v2.16b, v24.16b, #4
    +0x19fc: ldr     q3, [sp, #80]
    +0x1a00: uzp1    v0.16b, v1.16b, v0.16b
    +0x1a04: sub     v7.16b, v21.16b, v7.16b
    +0x1a08: uzp1    v3.16b, v8.16b, v3.16b
    +0x1a0c: sub     v17.16b, v21.16b, v17.16b
    +0x1a10: sub     v2.16b, v21.16b, v2.16b
    +0x1a14: orr     v5.16b, v7.16b, v5.16b
    +0x1a18: sub     v7.16b, v21.16b, v19.16b
    +0x1a1c: sub     v0.16b, v22.16b, v0.16b
    +0x1a20: sub     v1.16b, v22.16b, v3.16b
    +0x1a24: sub     v3.16b, v21.16b, v4.16b
    +0x1a28: shl     v4.16b, v18.16b, #4
    +0x1a2c: orr     v2.16b, v2.16b, v16.16b
    +0x1a30: sub     v16.16b, v22.16b, v20.16b
    +0x1a34: orr     v1.16b, v3.16b, v1.16b
    +0x1a38: sub     v3.16b, v21.16b, v4.16b
    +0x1a3c: orr     v4.16b, v7.16b, v6.16b
    +0x1a40: stp     q5, q2, [x19, #288]
    +0x1a44: orr     v2.16b, v17.16b, v16.16b
    +0x1a48: orr     v0.16b, v3.16b, v0.16b
    +0x1a4c: stp     q1, q4, [x19, #320]
    +0x1a50: stp     q2, q0, [x19, #352]
    +0x1a54: add     x8, x22, #0x800
    +0x1a58: str     xzr, [sp, #5568]
    +0x1a5c: ld2     {v0.4s-v1.4s}, [x8]
    +0x1a60: add     x8, x22, #0x840
    +0x1a64: ld2     {v16.4s-v17.4s}, [x8]
    +0x1a68: add     x8, x22, #0x860
    +0x1a6c: ld2     {v25.4s-v26.4s}, [x8]
    +0x1a70: add     x8, x22, #0x820
    +0x1a74: ld2     {v6.4s-v7.4s}, [x8]
    +0x1a78: add     x8, x22, #0x880
    +0x1a7c: ld2     {v2.4s-v3.4s}, [x8]
    +0x1a80: add     x8, x22, #0x8a0
    +0x1a84: ld2     {v4.4s-v5.4s}, [x8]
    +0x1a88: add     x8, x22, #0x8c0
    +0x1a8c: ld2     {v29.4s-v30.4s}, [x8]
    +0x1a90: add     x8, x22, #0x8e0
    +0x1a94: uzp1    v18.8h, v16.8h, v25.8h
    +0x1a98: ld2     {v8.4s-v9.4s}, [x8]
    +0x1a9c: add     x8, x22, #0x900
    +0x1aa0: uzp1    v16.8h, v17.8h, v26.8h
    +0x1aa4: ld2     {v23.4s-v24.4s}, [x8]
    +0x1aa8: add     x8, x22, #0x920
    +0x1aac: uzp1    v17.8h, v1.8h, v7.8h
    +0x1ab0: ld2     {v27.4s-v28.4s}, [x8]
    +0x1ab4: add     x8, x22, #0x940
    +0x1ab8: uzp1    v31.8h, v0.8h, v6.8h
    +0x1abc: ld2     {v10.4s-v11.4s}, [x8]
    +0x1ac0: add     x8, x22, #0x960
    +0x1ac4: uzp1    v7.8h, v3.8h, v5.8h
    +0x1ac8: ld2     {v12.4s-v13.4s}, [x8]
    +0x1acc: add     x8, x22, #0x980
    +0x1ad0: uzp1    v6.8h, v30.8h, v9.8h
    +0x1ad4: uzp1    v8.8h, v29.8h, v8.8h
    +0x1ad8: uzp1    v4.8h, v2.8h, v4.8h
    +0x1adc: uzp1    v5.16b, v17.16b, v16.16b
    +0x1ae0: ld2     {v19.4s-v20.4s}, [x8]
    +0x1ae4: add     x8, x22, #0x9a0
    +0x1ae8: str     q18, [sp, #80]
    +0x1aec: ld2     {v21.4s-v22.4s}, [x8]
    +0x1af0: add     x8, x22, #0x9c0
    +0x1af4: uzp1    v16.8h, v11.8h, v13.8h
    +0x1af8: uzp1    v17.8h, v10.8h, v12.8h
    +0x1afc: ld2     {v14.4s-v15.4s}, [x8]
    +0x1b00: add     x8, x22, #0x9e0
    +0x1b04: uzp1    v8.16b, v4.16b, v8.16b
    +0x1b08: shl     v5.16b, v5.16b, #4
    +0x1b0c: ld2     {v0.4s-v1.4s}, [x8]
    +0x1b10: add     x8, x22, #0xa00
    +0x1b14: uzp1    v4.8h, v20.8h, v22.8h
    +0x1b18: movi    v22.16b, #0x4
    +0x1b1c: ld2     {v25.4s-v26.4s}, [x8]
    +0x1b20: add     x8, x22, #0xa20
    +0x1b24: str     q16, [sp, #160]
    +0x1b28: uzp1    v16.16b, v7.16b, v6.16b
    +0x1b2c: uzp1    v6.8h, v23.8h, v27.8h
    +0x1b30: ld2     {v29.4s-v30.4s}, [x8]
    +0x1b34: add     x8, x22, #0xa40
    +0x1b38: uzp1    v9.8h, v14.8h, v0.8h
    +0x1b3c: uzp1    v10.8h, v15.8h, v1.8h
    +0x1b40: movi    v1.16b, #0x40
    +0x1b44: ld2     {v2.4s-v3.4s}, [x8]
    +0x1b48: add     x8, x22, #0xa60
    +0x1b4c: shl     v16.16b, v16.16b, #4
    +0x1b50: ld2     {v12.4s-v13.4s}, [x8]
    +0x1b54: add     x8, x22, #0xa80
    +0x1b58: str     q6, [sp, #96]
    +0x1b5c: uzp1    v6.8h, v24.8h, v28.8h
    +0x1b60: uzp1    v24.8h, v19.8h, v21.8h
    +0x1b64: sub     v5.16b, v1.16b, v5.16b
    +0x1b68: ldr     q23, [sp, #80]
    +0x1b6c: sub     v16.16b, v1.16b, v16.16b
    +0x1b70: uzp1    v0.8h, v2.8h, v12.8h
    +0x1b74: uzp1    v23.16b, v31.16b, v23.16b
    +0x1b78: uzp1    v11.8h, v3.8h, v13.8h
    +0x1b7c: stp     q6, q17, [sp, #112]
    +0x1b80: ld2     {v6.4s-v7.4s}, [x8]
    +0x1b84: add     x8, x22, #0xaa0
    +0x1b88: ld2     {v17.4s-v18.4s}, [x8]
    +0x1b8c: add     x8, x22, #0xac0
    +0x1b90: ld2     {v14.4s-v15.4s}, [x8]
    +0x1b94: add     x8, x22, #0xae0
    +0x1b98: stp     q4, q0, [sp, #64]
    +0x1b9c: movi    v0.16b, #0x4
    +0x1ba0: uzp1    v4.8h, v26.8h, v30.8h
    +0x1ba4: ld2     {v19.4s-v20.4s}, [x8]
    +0x1ba8: add     x8, x22, #0xb00
    +0x1bac: uzp1    v6.8h, v6.8h, v17.8h
    +0x1bb0: ld2     {v27.4s-v28.4s}, [x8]
    +0x1bb4: add     x8, x22, #0xb20
    +0x1bb8: sub     v3.16b, v0.16b, v23.16b
    +0x1bbc: sub     v23.16b, v0.16b, v8.16b
    +0x1bc0: uzp1    v8.8h, v25.8h, v29.8h
    +0x1bc4: uzp1    v31.8h, v14.8h, v19.8h
    +0x1bc8: uzp1    v19.8h, v15.8h, v20.8h
    +0x1bcc: uzp1    v4.16b, v4.16b, v11.16b
    +0x1bd0: ld2     {v29.4s-v30.4s}, [x8]
    +0x1bd4: add     x8, x22, #0xb40
    +0x1bd8: orr     v5.16b, v5.16b, v3.16b
    +0x1bdc: orr     v16.16b, v16.16b, v23.16b
    +0x1be0: ldr     q23, [sp, #96]
    +0x1be4: ld2     {v12.4s-v13.4s}, [x8]
    +0x1be8: add     x8, x22, #0xb60
    +0x1bec: shl     v4.16b, v4.16b, #4
    +0x1bf0: uzp1    v6.16b, v6.16b, v31.16b
    +0x1bf4: ld2     {v14.4s-v15.4s}, [x8]
    +0x1bf8: add     x8, x22, #0xb80
    +0x1bfc: uzp1    v27.8h, v27.8h, v29.8h
    +0x1c00: stp     q5, q16, [x19, #384]
    +0x1c04: ldp     q16, q5, [sp, #112]
    +0x1c08: ld2     {v2.4s-v3.4s}, [x8]
    +0x1c0c: add     x8, x22, #0xba0
    +0x1c10: uzp1    v17.8h, v13.8h, v15.8h
    +0x1c14: sub     v6.16b, v22.16b, v6.16b
    +0x1c18: ld2     {v20.4s-v21.4s}, [x8]
    +0x1c1c: add     x8, x22, #0xbc0
    +0x1c20: uzp1    v5.16b, v23.16b, v5.16b
    +0x1c24: uzp1    v23.8h, v7.8h, v18.8h
    +0x1c28: uzp1    v18.8h, v28.8h, v30.8h
    +0x1c2c: ldr     q7, [sp, #160]
    +0x1c30: ld2     {v25.4s-v26.4s}, [x8]
    +0x1c34: add     x8, x22, #0xbe0
    +0x1c38: uzp1    v7.16b, v16.16b, v7.16b
    +0x1c3c: uzp1    v16.16b, v24.16b, v9.16b
    +0x1c40: ldr     q24, [sp, #64]
    +0x1c44: uzp1    v19.16b, v23.16b, v19.16b
    +0x1c48: uzp1    v23.8h, v12.8h, v14.8h
    +0x1c4c: sub     v5.16b, v22.16b, v5.16b
    +0x1c50: uzp1    v24.16b, v24.16b, v10.16b
    +0x1c54: uzp1    v10.8h, v3.8h, v21.8h
    +0x1c58: uzp1    v17.16b, v18.16b, v17.16b
    +0x1c5c: ld2     {v0.4s-v1.4s}, [x8]
    +0x1c60: add     x8, sp, #0x1, lsl #12
    +0x1c64: shl     v7.16b, v7.16b, #4
    +0x1c68: sub     v16.16b, v22.16b, v16.16b
    +0x1c6c: add     x8, x8, #0x5c0
    +0x1c70: shl     v19.16b, v19.16b, #4
    +0x1c74: shl     v17.16b, v17.16b, #4
    +0x1c78: uzp1    v9.8h, v26.8h, v1.8h
    +0x1c7c: uzp1    v0.8h, v25.8h, v0.8h
    +0x1c80: uzp1    v1.8h, v2.8h, v20.8h
    +0x1c84: movi    v21.16b, #0x40
    +0x1c88: shl     v2.16b, v24.16b, #4
    +0x1c8c: uzp1    v20.16b, v27.16b, v23.16b
    +0x1c90: ldr     q3, [sp, #80]
    +0x1c94: uzp1    v3.16b, v8.16b, v3.16b
    +0x1c98: uzp1    v18.16b, v10.16b, v9.16b
    +0x1c9c: uzp1    v0.16b, v1.16b, v0.16b
    +0x1ca0: sub     v7.16b, v21.16b, v7.16b
    +0x1ca4: sub     v2.16b, v21.16b, v2.16b
    +0x1ca8: sub     v17.16b, v21.16b, v17.16b
    +0x1cac: sub     v1.16b, v22.16b, v3.16b
    +0x1cb0: sub     v3.16b, v21.16b, v4.16b
    +0x1cb4: shl     v4.16b, v18.16b, #4
    +0x1cb8: orr     v5.16b, v7.16b, v5.16b
    +0x1cbc: sub     v7.16b, v21.16b, v19.16b
    +0x1cc0: orr     v2.16b, v2.16b, v16.16b
    +0x1cc4: sub     v16.16b, v22.16b, v20.16b
    +0x1cc8: sub     v0.16b, v22.16b, v0.16b
    +0x1ccc: orr     v1.16b, v3.16b, v1.16b
    +0x1cd0: sub     v3.16b, v21.16b, v4.16b
    +0x1cd4: orr     v4.16b, v7.16b, v6.16b
    +0x1cd8: stp     q5, q2, [x19, #416]
    +0x1cdc: orr     v2.16b, v17.16b, v16.16b
    +0x1ce0: orr     v0.16b, v3.16b, v0.16b
    +0x1ce4: stp     q1, q4, [x19, #448]
    +0x1ce8: stp     q2, q0, [x19, #480]
    +0x1cec: add     x8, x22, #0xc00
    +0x1cf0: str     xzr, [sp, #5568]
    +0x1cf4: ld2     {v0.4s-v1.4s}, [x8]
    +0x1cf8: add     x8, x22, #0xc20
    +0x1cfc: ld2     {v2.4s-v3.4s}, [x8]
    +0x1d00: add     x8, x22, #0xc40
    +0x1d04: ld2     {v4.4s-v5.4s}, [x8]
    +0x1d08: add     x8, x22, #0xc60
    +0x1d0c: ld2     {v16.4s-v17.4s}, [x8]
    +0x1d10: add     x8, x22, #0xcc0
    +0x1d14: ld2     {v20.4s-v21.4s}, [x8]
    +0x1d18: add     x8, x22, #0xce0
    +0x1d1c: ld2     {v22.4s-v23.4s}, [x8]
    +0x1d20: add     x8, x22, #0xc80
    +0x1d24: uzp1    v7.8h, v0.8h, v2.8h
    +0x1d28: ld2     {v24.4s-v25.4s}, [x8]
    +0x1d2c: add     x8, x22, #0xca0
    +0x1d30: uzp1    v19.8h, v1.8h, v3.8h
    +0x1d34: ld2     {v26.4s-v27.4s}, [x8]
    +0x1d38: add     x8, x22, #0xd40
    +0x1d3c: uzp1    v6.8h, v4.8h, v16.8h
    +0x1d40: ld2     {v28.4s-v29.4s}, [x8]
    +0x1d44: add     x8, x22, #0xd60
    +0x1d48: uzp1    v18.8h, v5.8h, v17.8h
    +0x1d4c: uzp1    v0.8h, v20.8h, v22.8h
    +0x1d50: ld2     {v30.4s-v31.4s}, [x8]
    +0x1d54: uzp1    v4.8h, v21.8h, v23.8h
    +0x1d58: add     x8, x22, #0xd00
    +0x1d5c: uzp1    v2.8h, v24.8h, v26.8h
    +0x1d60: ld2     {v20.4s-v21.4s}, [x8]
    +0x1d64: add     x8, x22, #0xd20
    +0x1d68: ld2     {v22.4s-v23.4s}, [x8]
    +0x1d6c: add     x8, x22, #0xdc0
    +0x1d70: uzp1    v5.16b, v7.16b, v6.16b
    +0x1d74: str     q0, [sp, #160]
    +0x1d78: uzp1    v0.8h, v25.8h, v27.8h
    +0x1d7c: ld2     {v24.4s-v25.4s}, [x8]
    +0x1d80: add     x8, x22, #0xde0
    +0x1d84: ld2     {v26.4s-v27.4s}, [x8]
    +0x1d88: add     x8, x22, #0xd80
    +0x1d8c: stp     q0, q4, [sp, #80]
    +0x1d90: uzp1    v0.8h, v28.8h, v30.8h
    +0x1d94: uzp1    v4.8h, v24.8h, v26.8h
    +0x1d98: stp     q0, q2, [sp, #112]
    +0x1d9c: uzp1    v2.8h, v29.8h, v31.8h
    +0x1da0: ld2     {v28.4s-v29.4s}, [x8]
    +0x1da4: add     x8, x22, #0xda0
    +0x1da8: uzp1    v0.8h, v20.8h, v22.8h
    +0x1dac: uzp1    v20.8h, v21.8h, v23.8h
    +0x1db0: ld2     {v30.4s-v31.4s}, [x8]
    +0x1db4: add     x8, x22, #0xe00
    +0x1db8: str     q4, [sp, #32]
    +0x1dbc: ld2     {v8.4s-v9.4s}, [x8]
    +0x1dc0: add     x8, x22, #0xe20
    +0x1dc4: uzp1    v22.8h, v25.8h, v27.8h
    +0x1dc8: ld2     {v10.4s-v11.4s}, [x8]
    +0x1dcc: add     x8, x22, #0xe40
    +0x1dd0: uzp1    v27.16b, v19.16b, v18.16b
    +0x1dd4: ld2     {v12.4s-v13.4s}, [x8]
    +0x1dd8: add     x8, x22, #0xe60
    +0x1ddc: stp     q0, q2, [sp, #48]
    +0x1de0: uzp1    v4.8h, v28.8h, v30.8h
    +0x1de4: uzp1    v23.8h, v29.8h, v31.8h
    +0x1de8: ld2     {v14.4s-v15.4s}, [x8]
    +0x1dec: add     x8, x22, #0xec0
    +0x1df0: uzp1    v21.8h, v8.8h, v10.8h
    +0x1df4: uzp1    v26.8h, v9.8h, v11.8h
    +0x1df8: shl     v27.16b, v27.16b, #4
    +0x1dfc: ld2     {v2.4s-v3.4s}, [x8]
    +0x1e00: add     x8, x22, #0xee0
    +0x1e04: uzp1    v19.8h, v12.8h, v14.8h
    +0x1e08: uzp1    v24.8h, v13.8h, v15.8h
    +0x1e0c: str     q4, [sp, #16]
    +0x1e10: ld2     {v0.4s-v1.4s}, [x8]
    +0x1e14: add     x8, x22, #0xe80
    +0x1e18: ld2     {v28.4s-v29.4s}, [x8]
    +0x1e1c: add     x8, x22, #0xea0
    +0x1e20: ld2     {v30.4s-v31.4s}, [x8]
    +0x1e24: add     x8, x22, #0xf40
    +0x1e28: uzp1    v19.16b, v21.16b, v19.16b
    +0x1e2c: ld2     {v8.4s-v9.4s}, [x8]
    +0x1e30: add     x8, x22, #0xf60
    +0x1e34: uzp1    v25.8h, v2.8h, v0.8h
    +0x1e38: uzp1    v18.8h, v3.8h, v1.8h
    +0x1e3c: ld2     {v10.4s-v11.4s}, [x8]
    +0x1e40: add     x8, x22, #0xf00
    +0x1e44: uzp1    v4.8h, v28.8h, v30.8h
    +0x1e48: uzp1    v28.8h, v29.8h, v31.8h
    +0x1e4c: ld2     {v16.4s-v17.4s}, [x8]
    +0x1e50: add     x8, x22, #0xf20
    +0x1e54: uzp1    v29.8h, v8.8h, v10.8h
    +0x1e58: uzp1    v30.8h, v9.8h, v11.8h
    +0x1e5c: movi    v10.16b, #0x40
    +0x1e60: movi    v9.16b, #0x4
    +0x1e64: ld2     {v12.4s-v13.4s}, [x8]
    +0x1e68: add     x8, x22, #0xfc0
    +0x1e6c: uzp1    v18.16b, v28.16b, v18.16b
    +0x1e70: uzp1    v4.16b, v4.16b, v25.16b
    +0x1e74: ld2     {v6.4s-v7.4s}, [x8]
    +0x1e78: add     x8, x22, #0xfe0
    +0x1e7c: ld2     {v14.4s-v15.4s}, [x8]
    +0x1e80: add     x8, x22, #0xf80
    +0x1e84: uzp1    v31.8h, v16.8h, v12.8h
    +0x1e88: uzp1    v16.8h, v17.8h, v13.8h
    +0x1e8c: sub     v17.16b, v10.16b, v27.16b
    +0x1e90: sub     v5.16b, v9.16b, v5.16b
    +0x1e94: shl     v18.16b, v18.16b, #4
    +0x1e98: sub     v19.16b, v9.16b, v19.16b
    +0x1e9c: sub     v4.16b, v9.16b, v4.16b
    +0x1ea0: ld2     {v2.4s-v3.4s}, [x8]
    +0x1ea4: add     x8, x22, #0xfa0
    +0x1ea8: uzp1    v27.8h, v6.8h, v14.8h
    +0x1eac: uzp1    v6.8h, v7.8h, v15.8h
    +0x1eb0: ld2     {v0.4s-v1.4s}, [x8]
    +0x1eb4: uzp1    v16.16b, v16.16b, v30.16b
    +0x1eb8: uzp1    v21.16b, v31.16b, v29.16b
    +0x1ebc: add     x8, sp, #0x1, lsl #12
    +0x1ec0: add     x8, x8, #0x5c0
    +0x1ec4: ldp     q8, q7, [sp, #80]
    +0x1ec8: uzp1    v7.16b, v8.16b, v7.16b
    +0x1ecc: uzp1    v8.8h, v2.8h, v0.8h
    +0x1ed0: uzp1    v0.8h, v3.8h, v1.8h
    +0x1ed4: orr     v3.16b, v17.16b, v5.16b
    +0x1ed8: uzp1    v2.16b, v23.16b, v22.16b
    +0x1edc: shl     v16.16b, v16.16b, #4
    +0x1ee0: ldr     q1, [sp, #64]
    +0x1ee4: ldr     q5, [sp, #160]
    +0x1ee8: ldp     q22, q23, [sp, #32]
    +0x1eec: uzp1    v1.16b, v20.16b, v1.16b
    +0x1ef0: ldp     q20, q17, [sp, #112]
    +0x1ef4: shl     v7.16b, v7.16b, #4
    +0x1ef8: uzp1    v0.16b, v0.16b, v6.16b
    +0x1efc: shl     v2.16b, v2.16b, #4
    +0x1f00: sub     v16.16b, v10.16b, v16.16b
    +0x1f04: uzp1    v5.16b, v17.16b, v5.16b
    +0x1f08: uzp1    v20.16b, v23.16b, v20.16b
    +0x1f0c: ldr     q23, [sp, #16]
    +0x1f10: uzp1    v17.16b, v26.16b, v24.16b
    +0x1f14: sub     v7.16b, v10.16b, v7.16b
    +0x1f18: shl     v1.16b, v1.16b, #4
    +0x1f1c: uzp1    v22.16b, v23.16b, v22.16b
    +0x1f20: sub     v2.16b, v10.16b, v2.16b
    +0x1f24: shl     v0.16b, v0.16b, #4
    +0x1f28: sub     v5.16b, v9.16b, v5.16b
    +0x1f2c: sub     v1.16b, v10.16b, v1.16b
    +0x1f30: shl     v6.16b, v17.16b, #4
    +0x1f34: sub     v17.16b, v9.16b, v20.16b
    +0x1f38: sub     v0.16b, v10.16b, v0.16b
    +0x1f3c: sub     v20.16b, v9.16b, v22.16b
    +0x1f40: orr     v5.16b, v7.16b, v5.16b
    +0x1f44: uzp1    v7.16b, v8.16b, v27.16b
    +0x1f48: sub     v6.16b, v10.16b, v6.16b
    +0x1f4c: orr     v1.16b, v1.16b, v17.16b
    +0x1f50: sub     v17.16b, v10.16b, v18.16b
    +0x1f54: orr     v2.16b, v2.16b, v20.16b
    +0x1f58: stp     q3, q5, [x19, #512]
    +0x1f5c: sub     v3.16b, v9.16b, v21.16b
    +0x1f60: sub     v7.16b, v9.16b, v7.16b
    +0x1f64: orr     v6.16b, v6.16b, v19.16b
    +0x1f68: orr     v4.16b, v17.16b, v4.16b
    +0x1f6c: stp     q1, q2, [x19, #544]
    +0x1f70: orr     v1.16b, v16.16b, v3.16b
    +0x1f74: orr     v0.16b, v0.16b, v7.16b
    +0x1f78: stp     q6, q4, [x19, #576]
    +0x1f7c: stp     q1, q0, [x19, #608]
    +0x1f80: bl      <mldsa_poly_ntt>
    +0x1f84: add     x0, x22, #0x400
    +0x1f88: bl      <mldsa_poly_ntt>
    +0x1f8c: add     x0, x22, #0x800
    +0x1f90: bl      <mldsa_poly_ntt>
    +0x1f94: add     x0, x22, #0xc00
    +0x1f98: bl      <mldsa_poly_ntt>
    +0x1f9c: add     x0, x22, #0x1, lsl #12
    +0x1fa0: bl      <mldsa_poly_ntt>
    +0x1fa4: ldr     q0, [sp, #5440]
    +0x1fa8: ldr     q1, [sp, #5456]
    +0x1fac: add     x4, sp, #0x1, lsl #12
    +0x1fb0: add     x0, x20, #0x20
    +0x1fb4: add     x1, x19, #0x600
    +0x1fb8: add     x2, sp, #0xc0
    +0x1fbc: add     x3, x19, #0x300
    +0x1fc0: add     x4, x4, #0x540
    +0x1fc4: stp     q0, q1, [x20]
    +0x1fc8: bl      <mld_compute_pack_t0_t165>
    +0x1fcc: movi    v18.2d, #0x0
    +0x1fd0: add     x8, sp, #0x1, lsl #12
    +0x1fd4: add     x0, sp, #0x1, lsl #12
    +0x1fd8: add     x8, x8, #0x5c0
    +0x1fdc: ldp     d0, d1, [x20]
    +0x1fe0: ldp     d6, d7, [x20, #32]
    +0x1fe4: add     x0, x0, #0x5c0
    +0x1fe8: ldp     d2, d3, [x20, #16]
    +0x1fec: add     x21, sp, #0x1, lsl #12
    +0x1ff0: str     q18, [sp, #5568]
    +0x1ff4: add     x21, x21, #0x5c0
    +0x1ff8: stur    q18, [x8, #188]
    +0x1ffc: str     q18, [sp, #5600]
    +0x2000: ldr     d4, [sp, #5576]
    +0x2004: str     q18, [sp, #5584]
    +0x2008: ldr     d16, [sp, #5600]
    +0x200c: ldr     d17, [sp, #5608]
    +0x2010: ldr     d5, [sp, #5592]
    +0x2014: str     q18, [sp, #5616]
    +0x2018: eor     v1.8b, v4.8b, v1.8b
    +0x201c: eor     v4.8b, v16.8b, v6.8b
    +0x2020: str     d0, [sp, #5568]
    +0x2024: ldr     d16, [sp, #5624]
    +0x2028: ldp     d6, d0, [x20, #48]
    +0x202c: eor     v3.8b, v5.8b, v3.8b
    +0x2030: eor     v5.8b, v17.8b, v7.8b
    +0x2034: ldr     d7, [sp, #5616]
    +0x2038: str     q18, [sp, #5648]
    +0x203c: str     d2, [sp, #5584]
    +0x2040: eor     v0.8b, v16.8b, v0.8b
    +0x2044: str     d4, [sp, #5600]
    +0x2048: eor     v6.8b, v7.8b, v6.8b
    +0x204c: ldp     d2, d4, [x20, #80]
    +0x2050: str     q18, [sp, #5632]
    +0x2054: str     d1, [sp, #5576]
    +0x2058: ldp     d7, d1, [x20, #64]
    +0x205c: str     d3, [sp, #5592]
    +0x2060: ldr     d3, [sp, #5648]
    +0x2064: ldr     d16, [sp, #5640]
    +0x2068: str     q18, [sp, #5664]
    +0x206c: ldr     d17, [sp, #5632]
    +0x2070: eor     v2.8b, v3.8b, v2.8b
    +0x2074: str     d0, [sp, #5624]
    +0x2078: eor     v1.8b, v16.8b, v1.8b
    +0x207c: ldp     d3, d0, [x20, #96]
    +0x2080: ldr     d16, [sp, #5656]
    +0x2084: str     d5, [sp, #5608]
    +0x2088: ldr     d5, [sp, #5664]
    +0x208c: eor     v7.8b, v17.8b, v7.8b
    +0x2090: eor     v4.8b, v16.8b, v4.8b
    +0x2094: str     d6, [sp, #5616]
    +0x2098: ldr     d6, [sp, #5672]
    +0x209c: eor     v3.8b, v5.8b, v3.8b
    +0x20a0: str     q18, [sp, #5696]
    +0x20a4: str     q18, [sp, #5680]
    +0x20a8: eor     v0.8b, v6.8b, v0.8b
    +0x20ac: str     d1, [sp, #5640]
    +0x20b0: ldr     d5, [sp, #5680]
    +0x20b4: ldr     d6, [sp, #5688]
    +0x20b8: str     d2, [sp, #5648]
    +0x20bc: ldp     d1, d2, [x20, #112]
    +0x20c0: str     d4, [sp, #5656]
    +0x20c4: ldr     d4, [sp, #5696]
    +0x20c8: str     d3, [sp, #5664]
    +0x20cc: ldr     d3, [x20, #128]
    +0x20d0: eor     v1.8b, v5.8b, v1.8b
    +0x20d4: eor     v2.8b, v6.8b, v2.8b
    +0x20d8: str     q18, [sp, #5744]
    +0x20dc: eor     v3.8b, v4.8b, v3.8b
    +0x20e0: str     q18, [sp, #5712]
    +0x20e4: str     d7, [sp, #5632]
    +0x20e8: str     q18, [sp, #5728]
    +0x20ec: str     d0, [sp, #5672]
    +0x20f0: str     d1, [sp, #5680]
    +0x20f4: str     d2, [sp, #5688]
    +0x20f8: str     d3, [sp, #5696]
    +0x20fc: bl      <mldsa_keccakf1600_permute>
    +0x2100: ldp     d1, d2, [x20, #136]
    +0x2104: add     x0, sp, #0x1, lsl #12
    +0x2108: ldr     d0, [sp, #5568]
    +0x210c: ldr     d3, [sp, #5576]
    +0x2110: add     x0, x0, #0x5c0
    +0x2114: ldr     d5, [sp, #5584]
    +0x2118: ldr     d6, [sp, #5600]
    +0x211c: ldr     d7, [sp, #5608]
    +0x2120: eor     v0.8b, v0.8b, v1.8b
    +0x2124: eor     v1.8b, v3.8b, v2.8b
    +0x2128: ldr     d3, [sp, #5592]
    +0x212c: ldp     d4, d2, [x20, #152]
    +0x2130: ldr     d16, [sp, #5616]
    +0x2134: ldr     d17, [sp, #5624]
    +0x2138: ldr     d18, [sp, #5632]
    +0x213c: str     d0, [sp, #5568]
    +0x2140: eor     v4.8b, v5.8b, v4.8b
    +0x2144: eor     v2.8b, v3.8b, v2.8b
    +0x2148: str     d1, [sp, #5576]
    +0x214c: ldp     d5, d3, [x20, #168]
    +0x2150: str     d2, [sp, #5592]
    +0x2154: ldp     d1, d2, [x20, #216]
    +0x2158: eor     v5.8b, v6.8b, v5.8b
    +0x215c: eor     v3.8b, v7.8b, v3.8b
    +0x2160: str     d4, [sp, #5584]
    +0x2164: ldp     d6, d7, [x20, #184]
    +0x2168: ldr     d4, [sp, #5648]
    +0x216c: str     d5, [sp, #5600]
    +0x2170: eor     v1.8b, v4.8b, v1.8b
    +0x2174: ldr     d4, [sp, #5664]
    +0x2178: eor     v6.8b, v16.8b, v6.8b
    +0x217c: ldp     d16, d0, [x20, #200]
    +0x2180: eor     v7.8b, v17.8b, v7.8b
    +0x2184: ldr     d17, [sp, #5640]
    +0x2188: str     d3, [sp, #5608]
    +0x218c: ldp     d3, d5, [x20, #232]
    +0x2190: str     d1, [sp, #5648]
    +0x2194: eor     v0.8b, v17.8b, v0.8b
    +0x2198: ldr     d17, [sp, #5656]
    +0x219c: str     d6, [sp, #5616]
    +0x21a0: ldr     d6, [sp, #5672]
    +0x21a4: str     d7, [sp, #5624]
    +0x21a8: ldr     d7, [sp, #5680]
    +0x21ac: eor     v2.8b, v17.8b, v2.8b
    +0x21b0: eor     v3.8b, v4.8b, v3.8b
    +0x21b4: ldr     d1, [x20, #264]
    +0x21b8: str     d0, [sp, #5640]
    +0x21bc: ldp     d4, d0, [x20, #248]
    +0x21c0: eor     v5.8b, v6.8b, v5.8b
    +0x21c4: ldr     d6, [sp, #5688]
    +0x21c8: eor     v16.8b, v18.8b, v16.8b
    +0x21cc: str     d2, [sp, #5656]
    +0x21d0: ldr     d2, [sp, #5696]
    +0x21d4: eor     v4.8b, v7.8b, v4.8b
    +0x21d8: eor     v0.8b, v6.8b, v0.8b
    +0x21dc: str     d3, [sp, #5664]
    +0x21e0: eor     v1.8b, v2.8b, v1.8b
    +0x21e4: str     d16, [sp, #5632]
    +0x21e8: str     d5, [sp, #5672]
    +0x21ec: str     d4, [sp, #5680]
    +0x21f0: str     d0, [sp, #5688]
    +0x21f4: str     d1, [sp, #5696]
    +0x21f8: bl      <mldsa_keccakf1600_permute>
    +0x21fc: ldp     d1, d2, [x20, #272]
    +0x2200: add     x0, sp, #0x1, lsl #12
    +0x2204: ldr     d0, [sp, #5568]
    +0x2208: ldr     d3, [sp, #5576]
    +0x220c: add     x0, x0, #0x5c0
    +0x2210: ldr     d5, [sp, #5584]
    +0x2214: ldr     d6, [sp, #5600]
    +0x2218: ldr     d7, [sp, #5608]
    +0x221c: eor     v0.8b, v0.8b, v1.8b
    +0x2220: eor     v1.8b, v3.8b, v2.8b
    +0x2224: ldr     d3, [sp, #5592]
    +0x2228: ldp     d4, d2, [x20, #288]
    +0x222c: ldr     d16, [sp, #5616]
    +0x2230: ldr     d17, [sp, #5624]
    +0x2234: ldr     d18, [sp, #5632]
    +0x2238: str     d0, [sp, #5568]
    +0x223c: eor     v4.8b, v5.8b, v4.8b
    +0x2240: eor     v2.8b, v3.8b, v2.8b
    +0x2244: str     d1, [sp, #5576]
    +0x2248: ldp     d5, d3, [x20, #304]
    +0x224c: str     d2, [sp, #5592]
    +0x2250: ldp     d1, d2, [x20, #352]
    +0x2254: eor     v5.8b, v6.8b, v5.8b
    +0x2258: eor     v3.8b, v7.8b, v3.8b
    +0x225c: str     d4, [sp, #5584]
    +0x2260: ldp     d6, d7, [x20, #320]
    +0x2264: ldr     d4, [sp, #5648]
    +0x2268: str     d5, [sp, #5600]
    +0x226c: eor     v1.8b, v4.8b, v1.8b
    +0x2270: ldr     d4, [sp, #5664]
    +0x2274: eor     v6.8b, v16.8b, v6.8b
    +0x2278: ldp     d16, d0, [x20, #336]
    +0x227c: eor     v7.8b, v17.8b, v7.8b
    +0x2280: ldr     d17, [sp, #5640]
    +0x2284: str     d3, [sp, #5608]
    +0x2288: ldp     d3, d5, [x20, #368]
    +0x228c: str     d1, [sp, #5648]
    +0x2290: eor     v0.8b, v17.8b, v0.8b
    +0x2294: ldr     d17, [sp, #5656]
    +0x2298: str     d6, [sp, #5616]
    +0x229c: ldr     d6, [sp, #5672]
    +0x22a0: str     d7, [sp, #5624]
    +0x22a4: ldr     d7, [sp, #5680]
    +0x22a8: eor     v2.8b, v17.8b, v2.8b
    +0x22ac: eor     v3.8b, v4.8b, v3.8b
    +0x22b0: ldr     d1, [x20, #400]
    +0x22b4: str     d0, [sp, #5640]
    +0x22b8: ldp     d4, d0, [x20, #384]
    +0x22bc: eor     v5.8b, v6.8b, v5.8b
    +0x22c0: ldr     d6, [sp, #5688]
    +0x22c4: eor     v16.8b, v18.8b, v16.8b
    +0x22c8: str     d2, [sp, #5656]
    +0x22cc: ldr     d2, [sp, #5696]
    +0x22d0: eor     v4.8b, v7.8b, v4.8b
    +0x22d4: eor     v0.8b, v6.8b, v0.8b
    +0x22d8: str     d3, [sp, #5664]
    +0x22dc: eor     v1.8b, v2.8b, v1.8b
    +0x22e0: str     d16, [sp, #5632]
    +0x22e4: str     d5, [sp, #5672]
    +0x22e8: str     d4, [sp, #5680]
    +0x22ec: str     d0, [sp, #5688]
    +0x22f0: str     d1, [sp, #5696]
    +0x22f4: bl      <mldsa_keccakf1600_permute>
    +0x22f8: ldp     d1, d2, [x20, #408]
    +0x22fc: add     x0, sp, #0x1, lsl #12
    +0x2300: ldr     d0, [sp, #5568]
    +0x2304: ldr     d3, [sp, #5576]
    +0x2308: add     x0, x0, #0x5c0
    +0x230c: ldr     d5, [sp, #5584]
    +0x2310: ldr     d6, [sp, #5600]
    +0x2314: ldr     d7, [sp, #5608]
    +0x2318: eor     v0.8b, v0.8b, v1.8b
    +0x231c: eor     v1.8b, v3.8b, v2.8b
    +0x2320: ldr     d3, [sp, #5592]
    +0x2324: ldp     d4, d2, [x20, #424]
    +0x2328: ldr     d16, [sp, #5616]
    +0x232c: ldr     d17, [sp, #5624]
    +0x2330: ldr     d18, [sp, #5632]
    +0x2334: str     d0, [sp, #5568]
    +0x2338: eor     v4.8b, v5.8b, v4.8b
    +0x233c: eor     v2.8b, v3.8b, v2.8b
    +0x2340: str     d1, [sp, #5576]
    +0x2344: ldp     d5, d3, [x20, #440]
    +0x2348: str     d2, [sp, #5592]
    +0x234c: ldp     d1, d2, [x20, #488]
    +0x2350: eor     v5.8b, v6.8b, v5.8b
    +0x2354: eor     v3.8b, v7.8b, v3.8b
    +0x2358: str     d4, [sp, #5584]
    +0x235c: ldp     d6, d7, [x20, #456]
    +0x2360: ldr     d4, [sp, #5648]
    +0x2364: eor     v1.8b, v4.8b, v1.8b
    +0x2368: str     d5, [sp, #5600]
    +0x236c: ldr     d4, [sp, #5664]
    +0x2370: eor     v6.8b, v16.8b, v6.8b
    +0x2374: ldp     d16, d0, [x20, #472]
    +0x2378: eor     v7.8b, v17.8b, v7.8b
    +0x237c: ldr     d17, [sp, #5640]
    +0x2380: str     d3, [sp, #5608]
    +0x2384: ldp     d3, d5, [x20, #504]
    +0x2388: str     d1, [sp, #5648]
    +0x238c: eor     v0.8b, v17.8b, v0.8b
    +0x2390: ldr     d17, [sp, #5656]
    +0x2394: str     d6, [sp, #5616]
    +0x2398: ldr     d6, [sp, #5672]
    +0x239c: str     d7, [sp, #5624]
    +0x23a0: ldr     d7, [sp, #5680]
    +0x23a4: eor     v2.8b, v17.8b, v2.8b
    +0x23a8: eor     v3.8b, v4.8b, v3.8b
    +0x23ac: ldr     d4, [x20, #520]
    +0x23b0: eor     v5.8b, v6.8b, v5.8b
    +0x23b4: str     d0, [sp, #5640]
    +0x23b8: ldr     d0, [sp, #5688]
    +0x23bc: ldr     d6, [x20, #528]
    +0x23c0: ldr     d1, [x20, #536]
    +0x23c4: eor     v16.8b, v18.8b, v16.8b
    +0x23c8: str     d2, [sp, #5656]
    +0x23cc: ldr     d2, [sp, #5696]
    +0x23d0: eor     v4.8b, v7.8b, v4.8b
    +0x23d4: eor     v0.8b, v0.8b, v6.8b
    +0x23d8: str     d3, [sp, #5664]
    +0x23dc: eor     v1.8b, v2.8b, v1.8b
    +0x23e0: str     d16, [sp, #5632]
    +0x23e4: str     d5, [sp, #5672]
    +0x23e8: str     d4, [sp, #5680]
    +0x23ec: str     d0, [sp, #5688]
    +0x23f0: str     d1, [sp, #5696]
    +0x23f4: bl      <mldsa_keccakf1600_permute>
    +0x23f8: ldr     d0, [x20, #544]
    +0x23fc: ldr     d1, [sp, #5568]
    +0x2400: add     x0, sp, #0x1, lsl #12
    +0x2404: ldr     d2, [x20, #552]
    +0x2408: ldr     d3, [sp, #5576]
    +0x240c: add     x0, x0, #0x5c0
    +0x2410: eor     v0.8b, v1.8b, v0.8b
    +0x2414: ldr     d4, [x20, #560]
    +0x2418: ldr     d5, [sp, #5584]
    +0x241c: eor     v1.8b, v3.8b, v2.8b
    +0x2420: ldr     d2, [x20, #568]
    +0x2424: ldr     d3, [sp, #5592]
    +0x2428: ldr     d7, [sp, #5608]
    +0x242c: eor     v4.8b, v5.8b, v4.8b
    +0x2430: ldr     d5, [x20, #576]
    +0x2434: eor     v2.8b, v3.8b, v2.8b
    +0x2438: ldr     d3, [x20, #584]
    +0x243c: ldr     d6, [sp, #5600]
    +0x2440: ldr     d17, [sp, #5624]
    +0x2444: ldr     d16, [sp, #5616]
    +0x2448: str     d0, [sp, #5568]
    +0x244c: eor     v3.8b, v7.8b, v3.8b
    +0x2450: ldr     d7, [x20, #600]
    +0x2454: eor     v5.8b, v6.8b, v5.8b
    +0x2458: ldr     d6, [x20, #592]
    +0x245c: ldr     d0, [sp, #5640]
    +0x2460: str     d1, [sp, #5576]
    +0x2464: eor     v7.8b, v17.8b, v7.8b
    +0x2468: ldr     d1, [x20, #616]
    +0x246c: str     d4, [sp, #5584]
    +0x2470: ldr     d4, [x20, #624]
    +0x2474: eor     v6.8b, v16.8b, v6.8b
    +0x2478: ldr     d17, [sp, #5648]
    +0x247c: eor     v0.8b, v0.8b, v1.8b
    +0x2480: str     d2, [sp, #5592]
    +0x2484: ldr     d1, [sp, #5656]
    +0x2488: eor     v2.8b, v17.8b, v4.8b
    +0x248c: ldr     d4, [x20, #632]
    +0x2490: str     d5, [sp, #5600]
    +0x2494: str     d3, [sp, #5608]
    +0x2498: ldr     d3, [x20, #640]
    +0x249c: ldr     d5, [sp, #5664]
    +0x24a0: eor     v1.8b, v1.8b, v4.8b
    +0x24a4: str     d6, [sp, #5616]
    +0x24a8: ldr     d4, [sp, #5672]
    +0x24ac: eor     v3.8b, v5.8b, v3.8b
    +0x24b0: str     d7, [sp, #5624]
    +0x24b4: ldr     d5, [x20, #648]
    +0x24b8: ldr     d6, [x20, #656]
    +0x24bc: ldr     d7, [sp, #5680]
    +0x24c0: ldr     d16, [x20, #608]
    +0x24c4: eor     v4.8b, v4.8b, v5.8b
    +0x24c8: ldr     d18, [sp, #5632]
    +0x24cc: str     d0, [sp, #5640]
    +0x24d0: eor     v5.8b, v7.8b, v6.8b
    +0x24d4: ldr     d0, [sp, #5688]
    +0x24d8: ldr     d6, [x20, #664]
    +0x24dc: eor     v16.8b, v18.8b, v16.8b
    +0x24e0: str     d2, [sp, #5648]
    +0x24e4: ldr     d2, [sp, #5696]
    +0x24e8: eor     v0.8b, v0.8b, v6.8b
    +0x24ec: str     d1, [sp, #5656]
    +0x24f0: ldr     d1, [x20, #672]
    +0x24f4: str     d3, [sp, #5664]
    +0x24f8: eor     v1.8b, v2.8b, v1.8b
    +0x24fc: str     d16, [sp, #5632]
    +0x2500: str     d4, [sp, #5672]
    +0x2504: str     d5, [sp, #5680]
    +0x2508: str     d0, [sp, #5688]
    +0x250c: str     d1, [sp, #5696]
    +0x2510: bl      <mldsa_keccakf1600_permute>
    +0x2514: ldr     d0, [x20, #680]
    +0x2518: ldr     d1, [sp, #5568]
    +0x251c: add     x0, sp, #0x1, lsl #12
    +0x2520: ldr     d2, [x20, #688]
    +0x2524: ldr     d3, [sp, #5576]
    +0x2528: add     x0, x0, #0x5c0
    +0x252c: eor     v0.8b, v1.8b, v0.8b
    +0x2530: ldr     d4, [x20, #696]
    +0x2534: ldr     d5, [sp, #5584]
    +0x2538: eor     v1.8b, v3.8b, v2.8b
    +0x253c: ldr     d2, [x20, #704]
    +0x2540: ldr     d3, [sp, #5592]
    +0x2544: ldr     d7, [sp, #5608]
    +0x2548: eor     v4.8b, v5.8b, v4.8b
    +0x254c: ldr     d5, [x20, #712]
    +0x2550: eor     v2.8b, v3.8b, v2.8b
    +0x2554: ldr     d3, [x20, #720]
    +0x2558: ldr     d6, [sp, #5600]
    +0x255c: ldr     d17, [sp, #5624]
    +0x2560: ldr     d16, [sp, #5616]
    +0x2564: str     d0, [sp, #5568]
    +0x2568: eor     v3.8b, v7.8b, v3.8b
    +0x256c: ldr     d7, [x20, #736]
    +0x2570: eor     v5.8b, v6.8b, v5.8b
    +0x2574: ldr     d6, [x20, #728]
    +0x2578: ldr     d0, [sp, #5640]
    +0x257c: str     d1, [sp, #5576]
    +0x2580: eor     v7.8b, v17.8b, v7.8b
    +0x2584: ldr     d1, [x20, #752]
    +0x2588: str     d4, [sp, #5584]
    +0x258c: ldr     d4, [x20, #760]
    +0x2590: eor     v6.8b, v16.8b, v6.8b
    +0x2594: ldr     d17, [sp, #5648]
    +0x2598: eor     v0.8b, v0.8b, v1.8b
    +0x259c: str     d2, [sp, #5592]
    +0x25a0: ldr     d1, [sp, #5656]
    +0x25a4: eor     v2.8b, v17.8b, v4.8b
    +0x25a8: ldr     d4, [x20, #768]
    +0x25ac: str     d5, [sp, #5600]
    +0x25b0: str     d3, [sp, #5608]
    +0x25b4: ldr     d3, [x20, #776]
    +0x25b8: ldr     d5, [sp, #5664]
    +0x25bc: eor     v1.8b, v1.8b, v4.8b
    +0x25c0: str     d6, [sp, #5616]
    +0x25c4: ldr     d4, [sp, #5672]
    +0x25c8: eor     v3.8b, v5.8b, v3.8b
    +0x25cc: str     d7, [sp, #5624]
    +0x25d0: ldr     d5, [x20, #784]
    +0x25d4: ldr     d6, [x20, #792]
    +0x25d8: ldr     d7, [sp, #5680]
    +0x25dc: ldr     d16, [x20, #744]
    +0x25e0: eor     v4.8b, v4.8b, v5.8b
    +0x25e4: ldr     d18, [sp, #5632]
    +0x25e8: str     d0, [sp, #5640]
    +0x25ec: eor     v5.8b, v7.8b, v6.8b
    +0x25f0: ldr     d0, [sp, #5688]
    +0x25f4: ldr     d6, [x20, #800]
    +0x25f8: eor     v16.8b, v18.8b, v16.8b
    +0x25fc: str     d2, [sp, #5648]
    +0x2600: ldr     d2, [sp, #5696]
    +0x2604: eor     v0.8b, v0.8b, v6.8b
    +0x2608: str     d1, [sp, #5656]
    +0x260c: ldr     d1, [x20, #808]
    +0x2610: str     d3, [sp, #5664]
    +0x2614: eor     v1.8b, v2.8b, v1.8b
    +0x2618: str     d16, [sp, #5632]
    +0x261c: str     d4, [sp, #5672]
    +0x2620: str     d5, [sp, #5680]
    +0x2624: str     d0, [sp, #5688]
    +0x2628: str     d1, [sp, #5696]
    +0x262c: bl      <mldsa_keccakf1600_permute>
    +0x2630: ldr     d0, [x20, #816]
    +0x2634: ldr     d1, [sp, #5568]
    +0x2638: add     x0, sp, #0x1, lsl #12
    +0x263c: ldr     d2, [x20, #824]
    +0x2640: ldr     d3, [sp, #5576]
    +0x2644: add     x0, x0, #0x5c0
    +0x2648: eor     v0.8b, v1.8b, v0.8b
    +0x264c: ldr     d4, [x20, #832]
    +0x2650: ldr     d5, [sp, #5584]
    +0x2654: eor     v1.8b, v3.8b, v2.8b
    +0x2658: ldr     d2, [x20, #840]
    +0x265c: ldr     d3, [sp, #5592]
    +0x2660: ldr     d7, [sp, #5608]
    +0x2664: eor     v4.8b, v5.8b, v4.8b
    +0x2668: ldr     d5, [x20, #848]
    +0x266c: eor     v2.8b, v3.8b, v2.8b
    +0x2670: ldr     d3, [x20, #856]
    +0x2674: ldr     d6, [sp, #5600]
    +0x2678: ldr     d17, [sp, #5624]
    +0x267c: ldr     d16, [sp, #5616]
    +0x2680: str     d0, [sp, #5568]
    +0x2684: eor     v3.8b, v7.8b, v3.8b
    +0x2688: ldr     d7, [x20, #872]
    +0x268c: eor     v5.8b, v6.8b, v5.8b
    +0x2690: ldr     d6, [x20, #864]
    +0x2694: ldr     d0, [sp, #5640]
    +0x2698: str     d1, [sp, #5576]
    +0x269c: eor     v7.8b, v17.8b, v7.8b
    +0x26a0: ldr     d1, [x20, #888]
    +0x26a4: str     d4, [sp, #5584]
    +0x26a8: ldr     d4, [x20, #896]
    +0x26ac: eor     v6.8b, v16.8b, v6.8b
    +0x26b0: ldr     d17, [sp, #5648]
    +0x26b4: eor     v0.8b, v0.8b, v1.8b
    +0x26b8: str     d2, [sp, #5592]
    +0x26bc: ldr     d1, [sp, #5656]
    +0x26c0: eor     v2.8b, v17.8b, v4.8b
    +0x26c4: ldr     d4, [x20, #904]
    +0x26c8: str     d5, [sp, #5600]
    +0x26cc: str     d3, [sp, #5608]
    +0x26d0: ldr     d3, [x20, #912]
    +0x26d4: ldr     d5, [sp, #5664]
    +0x26d8: eor     v1.8b, v1.8b, v4.8b
    +0x26dc: str     d6, [sp, #5616]
    +0x26e0: ldr     d4, [sp, #5672]
    +0x26e4: eor     v3.8b, v5.8b, v3.8b
    +0x26e8: str     d7, [sp, #5624]
    +0x26ec: ldr     d5, [x20, #920]
    +0x26f0: ldr     d6, [x20, #928]
    +0x26f4: ldr     d7, [sp, #5680]
    +0x26f8: ldr     d16, [x20, #880]
    +0x26fc: eor     v4.8b, v4.8b, v5.8b
    +0x2700: ldr     d18, [sp, #5632]
    +0x2704: str     d0, [sp, #5640]
    +0x2708: eor     v5.8b, v7.8b, v6.8b
    +0x270c: ldr     d0, [sp, #5688]
    +0x2710: ldr     d6, [x20, #936]
    +0x2714: eor     v16.8b, v18.8b, v16.8b
    +0x2718: str     d2, [sp, #5648]
    +0x271c: ldr     d2, [sp, #5696]
    +0x2720: eor     v0.8b, v0.8b, v6.8b
    +0x2724: str     d1, [sp, #5656]
    +0x2728: ldr     d1, [x20, #944]
    +0x272c: str     d3, [sp, #5664]
    +0x2730: eor     v1.8b, v2.8b, v1.8b
    +0x2734: str     d16, [sp, #5632]
    +0x2738: str     d4, [sp, #5672]
    +0x273c: str     d5, [sp, #5680]
    +0x2740: str     d0, [sp, #5688]
    +0x2744: str     d1, [sp, #5696]
    +0x2748: bl      <mldsa_keccakf1600_permute>
    +0x274c: ldr     d0, [x20, #952]
    +0x2750: ldr     d1, [sp, #5568]
    +0x2754: add     x0, sp, #0x1, lsl #12
    +0x2758: ldr     d2, [x20, #960]
    +0x275c: ldr     d3, [sp, #5576]
    +0x2760: add     x0, x0, #0x5c0
    +0x2764: eor     v0.8b, v1.8b, v0.8b
    +0x2768: ldr     d4, [x20, #968]
    +0x276c: ldr     d5, [sp, #5584]
    +0x2770: eor     v1.8b, v3.8b, v2.8b
    +0x2774: ldr     d2, [x20, #976]
    +0x2778: ldr     d3, [sp, #5592]
    +0x277c: ldr     d7, [sp, #5608]
    +0x2780: eor     v4.8b, v5.8b, v4.8b
    +0x2784: ldr     d5, [x20, #984]
    +0x2788: eor     v2.8b, v3.8b, v2.8b
    +0x278c: ldr     d3, [x20, #992]
    +0x2790: ldr     d6, [sp, #5600]
    +0x2794: ldr     d17, [sp, #5624]
    +0x2798: ldr     d16, [sp, #5616]
    +0x279c: str     d0, [sp, #5568]
    +0x27a0: eor     v3.8b, v7.8b, v3.8b
    +0x27a4: ldr     d7, [x20, #1008]
    +0x27a8: eor     v5.8b, v6.8b, v5.8b
    +0x27ac: ldr     d6, [x20, #1000]
    +0x27b0: ldr     d0, [sp, #5640]
    +0x27b4: str     d1, [sp, #5576]
    +0x27b8: eor     v7.8b, v17.8b, v7.8b
    +0x27bc: ldr     d1, [x20, #1024]
    +0x27c0: str     d4, [sp, #5584]
    +0x27c4: ldr     d4, [x20, #1032]
    +0x27c8: eor     v6.8b, v16.8b, v6.8b
    +0x27cc: ldr     d17, [sp, #5648]
    +0x27d0: eor     v0.8b, v0.8b, v1.8b
    +0x27d4: str     d2, [sp, #5592]
    +0x27d8: ldr     d1, [sp, #5656]
    +0x27dc: eor     v2.8b, v17.8b, v4.8b
    +0x27e0: ldr     d4, [x20, #1040]
    +0x27e4: str     d5, [sp, #5600]
    +0x27e8: str     d3, [sp, #5608]
    +0x27ec: ldr     d3, [x20, #1048]
    +0x27f0: ldr     d5, [sp, #5664]
    +0x27f4: eor     v1.8b, v1.8b, v4.8b
    +0x27f8: str     d6, [sp, #5616]
    +0x27fc: ldr     d4, [sp, #5672]
    +0x2800: eor     v3.8b, v5.8b, v3.8b
    +0x2804: str     d7, [sp, #5624]
    +0x2808: ldr     d5, [x20, #1056]
    +0x280c: ldr     d6, [x20, #1064]
    +0x2810: ldr     d7, [sp, #5680]
    +0x2814: ldr     d16, [x20, #1016]
    +0x2818: eor     v4.8b, v4.8b, v5.8b
    +0x281c: ldr     d18, [sp, #5632]
    +0x2820: str     d0, [sp, #5640]
    +0x2824: eor     v5.8b, v7.8b, v6.8b
    +0x2828: ldr     d0, [sp, #5688]
    +0x282c: ldr     d6, [x20, #1072]
    +0x2830: eor     v16.8b, v18.8b, v16.8b
    +0x2834: str     d2, [sp, #5648]
    +0x2838: ldr     d2, [sp, #5696]
    +0x283c: eor     v0.8b, v0.8b, v6.8b
    +0x2840: str     d1, [sp, #5656]
    +0x2844: ldr     d1, [x20, #1080]
    +0x2848: str     d3, [sp, #5664]
    +0x284c: eor     v1.8b, v2.8b, v1.8b
    +0x2850: str     d16, [sp, #5632]
    +0x2854: str     d4, [sp, #5672]
    +0x2858: str     d5, [sp, #5680]
    +0x285c: str     d0, [sp, #5688]
    +0x2860: str     d1, [sp, #5696]
    +0x2864: bl      <mldsa_keccakf1600_permute>
    +0x2868: ldr     d0, [x20, #1088]
    +0x286c: ldr     d1, [sp, #5568]
    +0x2870: add     x0, sp, #0x1, lsl #12
    +0x2874: ldr     d2, [x20, #1096]
    +0x2878: ldr     d3, [sp, #5576]
    +0x287c: add     x0, x0, #0x5c0
    +0x2880: eor     v0.8b, v1.8b, v0.8b
    +0x2884: ldr     d4, [x20, #1104]
    +0x2888: ldr     d5, [sp, #5584]
    +0x288c: eor     v1.8b, v3.8b, v2.8b
    +0x2890: ldr     d2, [x20, #1112]
    +0x2894: ldr     d3, [sp, #5592]
    +0x2898: ldr     d7, [sp, #5608]
    +0x289c: eor     v4.8b, v5.8b, v4.8b
    +0x28a0: ldr     d5, [x20, #1120]
    +0x28a4: eor     v2.8b, v3.8b, v2.8b
    +0x28a8: ldr     d3, [x20, #1128]
    +0x28ac: ldr     d6, [sp, #5600]
    +0x28b0: ldr     d17, [sp, #5624]
    +0x28b4: ldr     d16, [sp, #5616]
    +0x28b8: str     d0, [sp, #5568]
    +0x28bc: eor     v3.8b, v7.8b, v3.8b
    +0x28c0: ldr     d7, [x20, #1144]
    +0x28c4: eor     v5.8b, v6.8b, v5.8b
    +0x28c8: ldr     d6, [x20, #1136]
    +0x28cc: ldr     d0, [sp, #5640]
    +0x28d0: str     d1, [sp, #5576]
    +0x28d4: eor     v7.8b, v17.8b, v7.8b
    +0x28d8: ldr     d1, [x20, #1160]
    +0x28dc: str     d4, [sp, #5584]
    +0x28e0: ldr     d4, [x20, #1168]
    +0x28e4: eor     v6.8b, v16.8b, v6.8b
    +0x28e8: ldr     d17, [sp, #5648]
    +0x28ec: eor     v0.8b, v0.8b, v1.8b
    +0x28f0: str     d2, [sp, #5592]
    +0x28f4: ldr     d1, [sp, #5656]
    +0x28f8: eor     v2.8b, v17.8b, v4.8b
    +0x28fc: ldr     d4, [x20, #1176]
    +0x2900: str     d5, [sp, #5600]
    +0x2904: str     d3, [sp, #5608]
    +0x2908: ldr     d3, [x20, #1184]
    +0x290c: ldr     d5, [sp, #5664]
    +0x2910: eor     v1.8b, v1.8b, v4.8b
    +0x2914: str     d6, [sp, #5616]
    +0x2918: ldr     d4, [sp, #5672]
    +0x291c: eor     v3.8b, v5.8b, v3.8b
    +0x2920: str     d7, [sp, #5624]
    +0x2924: ldr     d5, [x20, #1192]
    +0x2928: ldr     d6, [x20, #1200]
    +0x292c: ldr     d7, [sp, #5680]
    +0x2930: ldr     d16, [x20, #1152]
    +0x2934: eor     v4.8b, v4.8b, v5.8b
    +0x2938: ldr     d18, [sp, #5632]
    +0x293c: str     d0, [sp, #5640]
    +0x2940: eor     v5.8b, v7.8b, v6.8b
    +0x2944: ldr     d0, [sp, #5688]
    +0x2948: ldr     d6, [x20, #1208]
    +0x294c: eor     v16.8b, v18.8b, v16.8b
    +0x2950: str     d2, [sp, #5648]
    +0x2954: ldr     d2, [sp, #5696]
    +0x2958: eor     v0.8b, v0.8b, v6.8b
    +0x295c: str     d1, [sp, #5656]
    +0x2960: ldr     d1, [x20, #1216]
    +0x2964: str     d3, [sp, #5664]
    +0x2968: eor     v1.8b, v2.8b, v1.8b
    +0x296c: str     d16, [sp, #5632]
    +0x2970: str     d4, [sp, #5672]
    +0x2974: str     d5, [sp, #5680]
    +0x2978: str     d0, [sp, #5688]
    +0x297c: str     d1, [sp, #5696]
    +0x2980: bl      <mldsa_keccakf1600_permute>
    +0x2984: ldr     d0, [x20, #1224]
    +0x2988: ldr     d1, [sp, #5568]
    +0x298c: add     x0, sp, #0x1, lsl #12
    +0x2990: ldr     d2, [x20, #1232]
    +0x2994: ldr     d3, [sp, #5576]
    +0x2998: add     x0, x0, #0x5c0
    +0x299c: eor     v0.8b, v1.8b, v0.8b
    +0x29a0: ldr     d4, [x20, #1240]
    +0x29a4: ldr     d5, [sp, #5584]
    +0x29a8: eor     v1.8b, v3.8b, v2.8b
    +0x29ac: ldr     d2, [x20, #1248]
    +0x29b0: ldr     d3, [sp, #5592]
    +0x29b4: ldr     d7, [sp, #5608]
    +0x29b8: eor     v4.8b, v5.8b, v4.8b
    +0x29bc: ldr     d5, [x20, #1256]
    +0x29c0: eor     v2.8b, v3.8b, v2.8b
    +0x29c4: ldr     d3, [x20, #1264]
    +0x29c8: ldr     d6, [sp, #5600]
    +0x29cc: ldr     d17, [sp, #5624]
    +0x29d0: ldr     d16, [sp, #5616]
    +0x29d4: str     d0, [sp, #5568]
    +0x29d8: eor     v3.8b, v7.8b, v3.8b
    +0x29dc: ldr     d7, [x20, #1280]
    +0x29e0: eor     v5.8b, v6.8b, v5.8b
    +0x29e4: ldr     d6, [x20, #1272]
    +0x29e8: ldr     d0, [sp, #5640]
    +0x29ec: str     d1, [sp, #5576]
    +0x29f0: eor     v7.8b, v17.8b, v7.8b
    +0x29f4: ldr     d1, [x20, #1296]
    +0x29f8: str     d4, [sp, #5584]
    +0x29fc: ldr     d4, [x20, #1304]
    +0x2a00: eor     v6.8b, v16.8b, v6.8b
    +0x2a04: ldr     d17, [sp, #5648]
    +0x2a08: eor     v0.8b, v0.8b, v1.8b
    +0x2a0c: str     d2, [sp, #5592]
    +0x2a10: ldr     d1, [sp, #5656]
    +0x2a14: eor     v2.8b, v17.8b, v4.8b
    +0x2a18: ldr     d4, [x20, #1312]
    +0x2a1c: str     d5, [sp, #5600]
    +0x2a20: str     d3, [sp, #5608]
    +0x2a24: ldr     d3, [x20, #1320]
    +0x2a28: ldr     d5, [sp, #5664]
    +0x2a2c: eor     v1.8b, v1.8b, v4.8b
    +0x2a30: str     d6, [sp, #5616]
    +0x2a34: ldr     d4, [sp, #5672]
    +0x2a38: eor     v3.8b, v5.8b, v3.8b
    +0x2a3c: str     d7, [sp, #5624]
    +0x2a40: ldr     d5, [x20, #1328]
    +0x2a44: ldr     d6, [x20, #1336]
    +0x2a48: ldr     d7, [sp, #5680]
    +0x2a4c: ldr     d16, [x20, #1288]
    +0x2a50: eor     v4.8b, v4.8b, v5.8b
    +0x2a54: ldr     d18, [sp, #5632]
    +0x2a58: str     d0, [sp, #5640]
    +0x2a5c: eor     v5.8b, v7.8b, v6.8b
    +0x2a60: ldr     d0, [sp, #5688]
    +0x2a64: ldr     d6, [x20, #1344]
    +0x2a68: eor     v16.8b, v18.8b, v16.8b
    +0x2a6c: str     d2, [sp, #5648]
    +0x2a70: ldr     d2, [sp, #5696]
    +0x2a74: eor     v0.8b, v0.8b, v6.8b
    +0x2a78: str     d1, [sp, #5656]
    +0x2a7c: ldr     d1, [x20, #1352]
    +0x2a80: str     d3, [sp, #5664]
    +0x2a84: eor     v1.8b, v2.8b, v1.8b
    +0x2a88: str     d16, [sp, #5632]
    +0x2a8c: str     d4, [sp, #5672]
    +0x2a90: str     d5, [sp, #5680]
    +0x2a94: str     d0, [sp, #5688]
    +0x2a98: str     d1, [sp, #5696]
    +0x2a9c: bl      <mldsa_keccakf1600_permute>
    +0x2aa0: ldr     d0, [x20, #1360]
    +0x2aa4: ldr     d1, [sp, #5568]
    +0x2aa8: add     x0, sp, #0x1, lsl #12
    +0x2aac: ldr     d2, [x20, #1368]
    +0x2ab0: ldr     d3, [sp, #5576]
    +0x2ab4: add     x0, x0, #0x5c0
    +0x2ab8: eor     v0.8b, v1.8b, v0.8b
    +0x2abc: ldr     d4, [x20, #1376]
    +0x2ac0: ldr     d5, [sp, #5584]
    +0x2ac4: eor     v1.8b, v3.8b, v2.8b
    +0x2ac8: ldr     d2, [x20, #1384]
    +0x2acc: ldr     d3, [sp, #5592]
    +0x2ad0: ldr     d7, [sp, #5608]
    +0x2ad4: eor     v4.8b, v5.8b, v4.8b
    +0x2ad8: ldr     d5, [x20, #1392]
    +0x2adc: eor     v2.8b, v3.8b, v2.8b
    +0x2ae0: ldr     d3, [x20, #1400]
    +0x2ae4: ldr     d6, [sp, #5600]
    +0x2ae8: ldr     d17, [sp, #5624]
    +0x2aec: ldr     d16, [sp, #5616]
    +0x2af0: str     d0, [sp, #5568]
    +0x2af4: eor     v3.8b, v7.8b, v3.8b
    +0x2af8: ldr     d7, [x20, #1416]
    +0x2afc: eor     v5.8b, v6.8b, v5.8b
    +0x2b00: ldr     d6, [x20, #1408]
    +0x2b04: ldr     d0, [sp, #5640]
    +0x2b08: str     d1, [sp, #5576]
    +0x2b0c: eor     v7.8b, v17.8b, v7.8b
    +0x2b10: ldr     d1, [x20, #1432]
    +0x2b14: str     d4, [sp, #5584]
    +0x2b18: ldr     d4, [x20, #1440]
    +0x2b1c: eor     v6.8b, v16.8b, v6.8b
    +0x2b20: ldr     d17, [sp, #5648]
    +0x2b24: eor     v0.8b, v0.8b, v1.8b
    +0x2b28: str     d2, [sp, #5592]
    +0x2b2c: ldr     d1, [sp, #5656]
    +0x2b30: eor     v2.8b, v17.8b, v4.8b
    +0x2b34: ldr     d4, [x20, #1448]
    +0x2b38: str     d5, [sp, #5600]
    +0x2b3c: str     d3, [sp, #5608]
    +0x2b40: ldr     d3, [x20, #1456]
    +0x2b44: ldr     d5, [sp, #5664]
    +0x2b48: eor     v1.8b, v1.8b, v4.8b
    +0x2b4c: str     d6, [sp, #5616]
    +0x2b50: ldr     d4, [sp, #5672]
    +0x2b54: eor     v3.8b, v5.8b, v3.8b
    +0x2b58: str     d7, [sp, #5624]
    +0x2b5c: ldr     d5, [x20, #1464]
    +0x2b60: ldr     d6, [x20, #1472]
    +0x2b64: ldr     d7, [sp, #5680]
    +0x2b68: ldr     d16, [x20, #1424]
    +0x2b6c: eor     v4.8b, v4.8b, v5.8b
    +0x2b70: ldr     d18, [sp, #5632]
    +0x2b74: str     d0, [sp, #5640]
    +0x2b78: eor     v5.8b, v7.8b, v6.8b
    +0x2b7c: ldr     d0, [sp, #5688]
    +0x2b80: ldr     d6, [x20, #1480]
    +0x2b84: eor     v16.8b, v18.8b, v16.8b
    +0x2b88: str     d2, [sp, #5648]
    +0x2b8c: ldr     d2, [sp, #5696]
    +0x2b90: eor     v0.8b, v0.8b, v6.8b
    +0x2b94: str     d1, [sp, #5656]
    +0x2b98: ldr     d1, [x20, #1488]
    +0x2b9c: str     d3, [sp, #5664]
    +0x2ba0: eor     v1.8b, v2.8b, v1.8b
    +0x2ba4: str     d16, [sp, #5632]
    +0x2ba8: str     d4, [sp, #5672]
    +0x2bac: str     d5, [sp, #5680]
    +0x2bb0: str     d0, [sp, #5688]
    +0x2bb4: str     d1, [sp, #5696]
    +0x2bb8: bl      <mldsa_keccakf1600_permute>
    +0x2bbc: ldr     d0, [x20, #1496]
    +0x2bc0: ldr     d1, [sp, #5568]
    +0x2bc4: add     x0, sp, #0x1, lsl #12
    +0x2bc8: ldr     d2, [x20, #1504]
    +0x2bcc: ldr     d3, [sp, #5576]
    +0x2bd0: add     x0, x0, #0x5c0
    +0x2bd4: eor     v0.8b, v1.8b, v0.8b
    +0x2bd8: ldr     d4, [x20, #1512]
    +0x2bdc: ldr     d5, [sp, #5584]
    +0x2be0: eor     v1.8b, v3.8b, v2.8b
    +0x2be4: ldr     d2, [x20, #1520]
    +0x2be8: ldr     d3, [sp, #5592]
    +0x2bec: ldr     d7, [sp, #5608]
    +0x2bf0: eor     v4.8b, v5.8b, v4.8b
    +0x2bf4: ldr     d5, [x20, #1528]
    +0x2bf8: eor     v2.8b, v3.8b, v2.8b
    +0x2bfc: ldr     d3, [x20, #1536]
    +0x2c00: ldr     d6, [sp, #5600]
    +0x2c04: ldr     d17, [sp, #5624]
    +0x2c08: ldr     d16, [sp, #5616]
    +0x2c0c: str     d0, [sp, #5568]
    +0x2c10: eor     v3.8b, v7.8b, v3.8b
    +0x2c14: ldr     d7, [x20, #1552]
    +0x2c18: eor     v5.8b, v6.8b, v5.8b
    +0x2c1c: ldr     d6, [x20, #1544]
    +0x2c20: ldr     d0, [sp, #5640]
    +0x2c24: str     d1, [sp, #5576]
    +0x2c28: eor     v7.8b, v17.8b, v7.8b
    +0x2c2c: ldr     d1, [x20, #1568]
    +0x2c30: str     d4, [sp, #5584]
    +0x2c34: ldr     d4, [x20, #1576]
    +0x2c38: eor     v6.8b, v16.8b, v6.8b
    +0x2c3c: ldr     d17, [sp, #5648]
    +0x2c40: eor     v0.8b, v0.8b, v1.8b
    +0x2c44: str     d2, [sp, #5592]
    +0x2c48: ldr     d1, [sp, #5656]
    +0x2c4c: eor     v2.8b, v17.8b, v4.8b
    +0x2c50: ldr     d4, [x20, #1584]
    +0x2c54: str     d5, [sp, #5600]
    +0x2c58: str     d3, [sp, #5608]
    +0x2c5c: ldr     d3, [x20, #1592]
    +0x2c60: ldr     d5, [sp, #5664]
    +0x2c64: eor     v1.8b, v1.8b, v4.8b
    +0x2c68: str     d6, [sp, #5616]
    +0x2c6c: ldr     d4, [sp, #5672]
    +0x2c70: eor     v3.8b, v5.8b, v3.8b
    +0x2c74: str     d7, [sp, #5624]
    +0x2c78: ldr     d5, [x20, #1600]
    +0x2c7c: ldr     d6, [x20, #1608]
    +0x2c80: ldr     d7, [sp, #5680]
    +0x2c84: ldr     d16, [x20, #1560]
    +0x2c88: eor     v4.8b, v4.8b, v5.8b
    +0x2c8c: ldr     d18, [sp, #5632]
    +0x2c90: str     d0, [sp, #5640]
    +0x2c94: eor     v5.8b, v7.8b, v6.8b
    +0x2c98: ldr     d0, [sp, #5688]
    +0x2c9c: ldr     d6, [x20, #1616]
    +0x2ca0: eor     v16.8b, v18.8b, v16.8b
    +0x2ca4: str     d2, [sp, #5648]
    +0x2ca8: ldr     d2, [sp, #5696]
    +0x2cac: eor     v0.8b, v0.8b, v6.8b
    +0x2cb0: str     d1, [sp, #5656]
    +0x2cb4: ldr     d1, [x20, #1624]
    +0x2cb8: str     d3, [sp, #5664]
    +0x2cbc: eor     v1.8b, v2.8b, v1.8b
    +0x2cc0: str     d16, [sp, #5632]
    +0x2cc4: str     d4, [sp, #5672]
    +0x2cc8: str     d5, [sp, #5680]
    +0x2ccc: str     d0, [sp, #5688]
    +0x2cd0: str     d1, [sp, #5696]
    +0x2cd4: bl      <mldsa_keccakf1600_permute>
    +0x2cd8: ldr     d0, [x20, #1632]
    +0x2cdc: ldr     d1, [sp, #5568]
    +0x2ce0: add     x0, sp, #0x1, lsl #12
    +0x2ce4: ldr     d2, [x20, #1640]
    +0x2ce8: ldr     d3, [sp, #5576]
    +0x2cec: add     x0, x0, #0x5c0
    +0x2cf0: eor     v0.8b, v1.8b, v0.8b
    +0x2cf4: ldr     d4, [x20, #1648]
    +0x2cf8: ldr     d5, [sp, #5584]
    +0x2cfc: eor     v1.8b, v3.8b, v2.8b
    +0x2d00: ldr     d2, [x20, #1656]
    +0x2d04: ldr     d3, [sp, #5592]
    +0x2d08: ldr     d7, [sp, #5608]
    +0x2d0c: eor     v4.8b, v5.8b, v4.8b
    +0x2d10: ldr     d5, [x20, #1664]
    +0x2d14: eor     v2.8b, v3.8b, v2.8b
    +0x2d18: ldr     d3, [x20, #1672]
    +0x2d1c: ldr     d6, [sp, #5600]
    +0x2d20: ldr     d17, [sp, #5624]
    +0x2d24: ldr     d16, [sp, #5616]
    +0x2d28: str     d0, [sp, #5568]
    +0x2d2c: eor     v3.8b, v7.8b, v3.8b
    +0x2d30: ldr     d7, [x20, #1688]
    +0x2d34: eor     v5.8b, v6.8b, v5.8b
    +0x2d38: ldr     d6, [x20, #1680]
    +0x2d3c: ldr     d0, [sp, #5640]
    +0x2d40: str     d1, [sp, #5576]
    +0x2d44: eor     v7.8b, v17.8b, v7.8b
    +0x2d48: ldr     d1, [x20, #1704]
    +0x2d4c: str     d4, [sp, #5584]
    +0x2d50: ldr     d4, [x20, #1712]
    +0x2d54: eor     v6.8b, v16.8b, v6.8b
    +0x2d58: ldr     d17, [sp, #5648]
    +0x2d5c: eor     v0.8b, v0.8b, v1.8b
    +0x2d60: str     d2, [sp, #5592]
    +0x2d64: ldr     d1, [sp, #5656]
    +0x2d68: eor     v2.8b, v17.8b, v4.8b
    +0x2d6c: ldr     d4, [x20, #1720]
    +0x2d70: str     d5, [sp, #5600]
    +0x2d74: str     d3, [sp, #5608]
    +0x2d78: ldr     d3, [x20, #1728]
    +0x2d7c: ldr     d5, [sp, #5664]
    +0x2d80: eor     v1.8b, v1.8b, v4.8b
    +0x2d84: str     d6, [sp, #5616]
    +0x2d88: ldr     d4, [sp, #5672]
    +0x2d8c: eor     v3.8b, v5.8b, v3.8b
    +0x2d90: str     d7, [sp, #5624]
    +0x2d94: ldr     d5, [x20, #1736]
    +0x2d98: ldr     d6, [x20, #1744]
    +0x2d9c: ldr     d7, [sp, #5680]
    +0x2da0: ldr     d16, [x20, #1696]
    +0x2da4: eor     v4.8b, v4.8b, v5.8b
    +0x2da8: ldr     d18, [sp, #5632]
    +0x2dac: str     d0, [sp, #5640]
    +0x2db0: eor     v5.8b, v7.8b, v6.8b
    +0x2db4: ldr     d0, [sp, #5688]
    +0x2db8: ldr     d6, [x20, #1752]
    +0x2dbc: eor     v16.8b, v18.8b, v16.8b
    +0x2dc0: str     d2, [sp, #5648]
    +0x2dc4: ldr     d2, [sp, #5696]
    +0x2dc8: eor     v0.8b, v0.8b, v6.8b
    +0x2dcc: str     d1, [sp, #5656]
    +0x2dd0: ldr     d1, [x20, #1760]
    +0x2dd4: str     d3, [sp, #5664]
    +0x2dd8: eor     v1.8b, v2.8b, v1.8b
    +0x2ddc: str     d16, [sp, #5632]
    +0x2de0: str     d4, [sp, #5672]
    +0x2de4: str     d5, [sp, #5680]
    +0x2de8: str     d0, [sp, #5688]
    +0x2dec: str     d1, [sp, #5696]
    +0x2df0: bl      <mldsa_keccakf1600_permute>
    +0x2df4: ldr     d0, [x20, #1768]
    +0x2df8: ldr     d1, [sp, #5568]
    +0x2dfc: add     x0, sp, #0x1, lsl #12
    +0x2e00: ldr     d2, [x20, #1776]
    +0x2e04: ldr     d3, [sp, #5576]
    +0x2e08: add     x0, x0, #0x5c0
    +0x2e0c: eor     v0.8b, v1.8b, v0.8b
    +0x2e10: ldr     d4, [x20, #1784]
    +0x2e14: ldr     d5, [sp, #5584]
    +0x2e18: eor     v1.8b, v3.8b, v2.8b
    +0x2e1c: ldr     d2, [x20, #1792]
    +0x2e20: ldr     d3, [sp, #5592]
    +0x2e24: ldr     d7, [sp, #5608]
    +0x2e28: eor     v4.8b, v5.8b, v4.8b
    +0x2e2c: ldr     d5, [x20, #1800]
    +0x2e30: eor     v2.8b, v3.8b, v2.8b
    +0x2e34: ldr     d3, [x20, #1808]
    +0x2e38: ldr     d6, [sp, #5600]
    +0x2e3c: ldr     d17, [sp, #5624]
    +0x2e40: ldr     d16, [sp, #5616]
    +0x2e44: str     d0, [sp, #5568]
    +0x2e48: eor     v3.8b, v7.8b, v3.8b
    +0x2e4c: ldr     d7, [x20, #1824]
    +0x2e50: eor     v5.8b, v6.8b, v5.8b
    +0x2e54: ldr     d6, [x20, #1816]
    +0x2e58: ldr     d0, [sp, #5640]
    +0x2e5c: str     d1, [sp, #5576]
    +0x2e60: eor     v7.8b, v17.8b, v7.8b
    +0x2e64: ldr     d1, [x20, #1840]
    +0x2e68: str     d4, [sp, #5584]
    +0x2e6c: ldr     d4, [x20, #1848]
    +0x2e70: eor     v6.8b, v16.8b, v6.8b
    +0x2e74: ldr     d17, [sp, #5648]
    +0x2e78: eor     v0.8b, v0.8b, v1.8b
    +0x2e7c: str     d2, [sp, #5592]
    +0x2e80: ldr     d1, [sp, #5656]
    +0x2e84: eor     v2.8b, v17.8b, v4.8b
    +0x2e88: ldr     d4, [x20, #1856]
    +0x2e8c: str     d5, [sp, #5600]
    +0x2e90: str     d3, [sp, #5608]
    +0x2e94: ldr     d3, [x20, #1864]
    +0x2e98: ldr     d5, [sp, #5664]
    +0x2e9c: eor     v1.8b, v1.8b, v4.8b
    +0x2ea0: str     d6, [sp, #5616]
    +0x2ea4: ldr     d4, [sp, #5672]
    +0x2ea8: eor     v3.8b, v5.8b, v3.8b
    +0x2eac: str     d7, [sp, #5624]
    +0x2eb0: ldr     d5, [x20, #1872]
    +0x2eb4: ldr     d6, [x20, #1880]
    +0x2eb8: ldr     d7, [sp, #5680]
    +0x2ebc: ldr     d16, [x20, #1832]
    +0x2ec0: eor     v4.8b, v4.8b, v5.8b
    +0x2ec4: ldr     d18, [sp, #5632]
    +0x2ec8: str     d0, [sp, #5640]
    +0x2ecc: eor     v5.8b, v7.8b, v6.8b
    +0x2ed0: ldr     d0, [sp, #5688]
    +0x2ed4: ldr     d6, [x20, #1888]
    +0x2ed8: eor     v16.8b, v18.8b, v16.8b
    +0x2edc: str     d2, [sp, #5648]
    +0x2ee0: ldr     d2, [sp, #5696]
    +0x2ee4: eor     v0.8b, v0.8b, v6.8b
    +0x2ee8: str     d1, [sp, #5656]
    +0x2eec: ldr     d1, [x20, #1896]
    +0x2ef0: str     d3, [sp, #5664]
    +0x2ef4: eor     v1.8b, v2.8b, v1.8b
    +0x2ef8: str     d16, [sp, #5632]
    +0x2efc: str     d4, [sp, #5672]
    +0x2f00: str     d5, [sp, #5680]
    +0x2f04: str     d0, [sp, #5688]
    +0x2f08: str     d1, [sp, #5696]
    +0x2f0c: bl      <mldsa_keccakf1600_permute>
    +0x2f10: add     x9, sp, #0x1, lsl #12
    +0x2f14: ldr     q0, [x20, #1904]
    +0x2f18: ldr     q1, [sp, #5568]
    +0x2f1c: add     x9, x9, #0x5c0
    +0x2f20: ldr     q2, [x20, #1920]
    +0x2f24: ldr     q3, [sp, #5584]
    +0x2f28: ldrb    w8, [x9, #48]
    +0x2f2c: ldr     q4, [x20, #1936]
    +0x2f30: eor     v0.16b, v1.16b, v0.16b
    +0x2f34: ldr     q1, [sp, #5600]
    +0x2f38: eor     v2.16b, v3.16b, v2.16b
    +0x2f3c: add     x0, sp, #0x1, lsl #12
    +0x2f40: eor     w8, w8, #0x1f
    +0x2f44: add     x0, x0, #0x5c0
    +0x2f48: strb    w8, [x9, #48]
    +0x2f4c: ldrb    w8, [x9, #135]
    +0x2f50: eor     v1.16b, v1.16b, v4.16b
    +0x2f54: add     x9, sp, #0x1, lsl #12
    +0x2f58: str     q0, [sp, #5568]
    +0x2f5c: add     x9, x9, #0x5c0
    +0x2f60: eor     w8, w8, #0x80
    +0x2f64: str     q2, [sp, #5584]
    +0x2f68: strb    w8, [x9, #135]
    +0x2f6c: mov     w8, #0x88
    +0x2f70: str     q1, [sp, #5600]
    +0x2f74: str     w8, [sp, #5768]
    +0x2f78: bl      <mldsa_keccakf1600_permute>
    +0x2f7c: ldr     q0, [sp, #5568]
    +0x2f80: ldr     q1, [sp, #5584]
    +0x2f84: add     x0, sp, #0xc0
    +0x2f88: ldr     q2, [sp, #5616]
    +0x2f8c: mov     w1, wzr
    +0x2f90: mov     w2, #0x1400
    +0x2f94: str     q0, [sp, #5312]
    +0x2f98: ldr     q0, [sp, #5600]
    +0x2f9c: str     q1, [sp, #5328]
    +0x2fa0: str     q0, [sp, #5344]
    +0x2fa4: movi    v0.2d, #0x0
    +0x2fa8: str     q2, [sp, #5360]
    +0x2fac: str     q0, [sp, #5632]
    +0x2fb0: str     q0, [sp, #5648]
    +0x2fb4: str     q0, [sp, #5664]
    +0x2fb8: str     q0, [sp, #5680]
    +0x2fbc: str     q0, [sp, #5696]
    +0x2fc0: str     q0, [sp, #5712]
    +0x2fc4: str     q0, [sp, #5728]
    +0x2fc8: str     q0, [sp, #5744]
    +0x2fcc: str     q0, [sp, #5760]
    +0x2fd0: str     q0, [sp, #5568]
    +0x2fd4: str     q0, [sp, #5584]
    +0x2fd8: str     q0, [sp, #5600]
    +0x2fdc: str     q0, [sp, #5616]
    +0x2fe0: ldr     q0, [sp, #5440]
    +0x2fe4: ldr     q1, [sp, #5456]
    +0x2fe8: ldr     q2, [sp, #5536]
    +0x2fec: stp     q0, q1, [x19]
    +0x2ff0: ldr     q0, [sp, #5552]
    +0x2ff4: ldr     q1, [sp, #5312]
    +0x2ff8: stp     q2, q0, [x19, #32]
    +0x2ffc: ldr     q0, [sp, #5328]
    +0x3000: ldr     q2, [sp, #5344]
    +0x3004: stp     q1, q0, [x19, #64]
    +0x3008: ldr     q0, [sp, #5360]
    +0x300c: stp     q2, q0, [x19, #96]
    +0x3010: bl      <memset>
    +0x3014: movi    v0.2d, #0x0
    +0x3018: add     x8, sp, #0x1, lsl #12
    +0x301c: add     x8, x8, #0x4c0
    +0x3020: str     q0, [sp, #5360]
    +0x3024: str     q0, [sp, #5344]
    +0x3028: str     q0, [sp, #5328]
    +0x302c: str     q0, [sp, #5312]
    +0x3030: add     x8, sp, #0x1, lsl #12
    +0x3034: strh    wzr, [sp, #5408]
    +0x3038: str     q0, [sp, #5392]
    +0x303c: add     x8, x8, #0x500
    +0x3040: str     q0, [sp, #5376]
    +0x3044: add     x8, sp, #0x1, lsl #12
    +0x3048: str     q0, [sp, #5552]
    +0x304c: str     q0, [sp, #5536]
    +0x3050: add     x8, x8, #0x540
    +0x3054: str     q0, [sp, #5520]
    +0x3058: str     q0, [sp, #5504]
    +0x305c: str     q0, [sp, #5488]
    +0x3060: str     q0, [sp, #5472]
    +0x3064: str     q0, [sp, #5456]
    +0x3068: str     q0, [sp, #5440]
    +0x306c: adrp    x8, <page>
    +0x3070: ldr     x8, [x8, #4088]
    +0x3074: ldr     x9, [sp, #5784]
    +0x3078: ldr     x8, [x8]
    +0x307c: cmp     x8, x9
    +0x3080: b.ne    <mldsa65_keypair_internal+0x30e8>
    +0x3084: mov     w0, wzr
    +0x3088: sub     sp, x29, #0x40
    +0x308c: ldp     x20, x19, [sp, #144]
    +0x3090: ldp     x22, x21, [sp, #128]
    +0x3094: ldp     x24, x23, [sp, #112]
    +0x3098: ldp     x26, x25, [sp, #96]
    +0x309c: ldp     x28, x27, [sp, #80]
    +0x30a0: ldp     x29, x30, [sp, #64]
    +0x30a4: ldp     d9, d8, [sp, #48]
    +0x30a8: ldp     d11, d10, [sp, #32]
    +0x30ac: ldp     d13, d12, [sp, #16]
    +0x30b0: ldp     d15, d14, [sp], #160
    +0x30b4: mov     x1, #0x0
    +0x30b8: mov     x2, #0x0
    +0x30bc: mov     x3, #0x0
    +0x30c0: mov     x4, #0x0
    +0x30c4: mov     x5, #0x0
    +0x30c8: mov     x6, #0x0
    +0x30cc: mov     x7, #0x0
    +0x30d0: mov     x8, #0x0
    +0x30d4: mov     x9, #0x0
    +0x30d8: mov     x10, #0x0
    +0x30dc: mov     x11, #0x0
    +0x30e0: mov     x12, #0x0
    +0x30e4: ret     
    +0x30e8: bl      <__stack_chk_fail>

    memset@plt:
       +0x0: adrp    x16, <page>
       +0x4: ldr     x17, [x16, #4072]
       +0x8: add     x16, x16, #0xfe8
       +0xc: br      x17
 ***)

let MLDSA_NATIVE_KEYPAIR_INTERNAL_65_CLANG23_O3_MONO_REDUCED_RAM_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
   [layout_range "mldsa65_keypair_internal";
    layout_range "plt_memset"];;

(* ------------------------------------------------------------------------- *)
(* Correctness, assuming the contracts for memset and memcpy. From the seed SEED (32     *)
(* bytes at seed), the public key at pk (1952 bytes) becomes                 *)
(* mld_keypair_pk_65 SEED and the secret key at sk (4032 bytes)              *)
(* mld_keypair_sk_65 SEED, and the result is 0. The stack is the 11296 bytes *)
(* below the stack pointer: the frame of the function, of up to 5968 bytes,  *)
(* and the stacks of its callees.                                            *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_KEYPAIR_INTERNAL_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!mf mc ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev
     ==> !pk sk seed SEED guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          32768 <= val stackpointer /\ val(stackpointer:int64) < 2 EXP 63 /\
          mld_matrix_terminates 6 5 (mld_keypair_rho 6 5 SEED) /\
          mld_keypair_terminates_65 SEED /\
          PAIRWISE nonoverlapping
           [(pk,1952); (sk,4032);
            (word_sub stackpointer (word 11296),11296)] /\
          ALLPAIRS nonoverlapping
           [(pk,1952); (sk,4032);
            (word_sub stackpointer (word 11296),11296)]
           [(seed,32); (word pc,libmldsa_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                    read PC s = word (pc + mldsa65_keypair_internal) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [pk; sk; seed] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(seed,32)) s = SEED)
               (\s. read PC s = returnaddress /\
                    C_RETURN s = word 0 /\
                    (!j. j < 1952
                         ==> read(memory :> bytes8(word_add pk (word j))) s =
                             mld_keypair_pk_65 SEED j) /\
                    (!j. j < 4032
                         ==> read(memory :> bytes8(word_add sk (word j))) s =
                             mld_keypair_sk_65 SEED j))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(pk,1952); memory :> bytes(sk,4032);
                  memory :> bytes(word_sub stackpointer (word 11296),11296)])`;;

let MLDSA_NATIVE_KEYPAIR_INTERNAL_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLDSA_NATIVE_KEYPAIR_INTERNAL_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, rho, whether each nibble read by  *)
(* the sampling of each polynomial is accepted (mld_keypair_declass_65), the *)
(* address of memset and the stack, with all accesses within the arguments,  *)
(* the stack, the GOT entries and the stack guard, the region (ea,el) that   *)
(* memset may read and the constants of the callees, and the writes within   *)
(* the keys and the stack.                                                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_KEYPAIR_INTERNAL_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT =
  `!mf mc ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev
     ==> exists f_events.
          forall e pk sk seed SEED guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          32768 <= val stackpointer /\ val(stackpointer:int64) < 2 EXP 63 /\
          mld_matrix_terminates 6 5 (mld_keypair_rho 6 5 SEED) /\
          mld_keypair_terminates_65 SEED /\
          PAIRWISE nonoverlapping
           [(pk,1952); (sk,4032);
            (word_sub stackpointer (word 11296),11296)] /\
          ALLPAIRS nonoverlapping
           [(pk,1952); (sk,4032);
            (word_sub stackpointer (word 11296),11296)]
           [(seed,32); (word pc,libmldsa_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                    read PC s = word (pc + mldsa65_keypair_internal) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [pk; sk; seed] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(seed,32)) s = SEED /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    C_RETURN s = word 0 /\
                    (!j. j < 1952
                         ==> read(memory :> bytes8(word_add pk (word j))) s =
                             mld_keypair_pk_65 SEED j) /\
                    (!j. j < 4032
                         ==> read(memory :> bytes8(word_add sk (word j))) s =
                             mld_keypair_sk_65 SEED j) /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events pk sk seed (mld_keypair_rho 6 5 SEED)
                             (mld_keypair_declass_65 SEED) guard mf mc pc
                             (word_sub stackpointer (word 11296))
                             returnaddress /\
                       memaccess_inbounds e2
                        [seed,32; pk,1952; sk,4032;
                         word_sub stackpointer (word 11296),11296;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; word(pc + got_memcpy),8; ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192;
                         word(pc + rodata_mld_zetas),1024;
                         word(pc + mld_compute_pack_t0_t165_consts),272]
                        [pk,1952; sk,4032;
                         word_sub stackpointer (word 11296),11296]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(pk,1952); memory :> bytes(sk,4032);
                  memory :> bytes(word_sub stackpointer (word 11296),11296)])`;;

let MLDSA_NATIVE_KEYPAIR_INTERNAL_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_KEYPAIR_INTERNAL_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_KEYPAIR_INTERNAL_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT =
  `!mf mc ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev
     ==> exists f_events.
          forall e pk sk seed SEED guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          32768 <= val stackpointer /\ val(stackpointer:int64) < 2 EXP 63 /\
          mld_matrix_terminates 6 5 (mld_keypair_rho 6 5 SEED) /\
          mld_keypair_terminates_65 SEED /\
          PAIRWISE nonoverlapping
           [(pk,1952); (sk,4032);
            (word_sub stackpointer (word 11296),11296)] /\
          ALLPAIRS nonoverlapping
           [(pk,1952); (sk,4032);
            (word_sub stackpointer (word 11296),11296)]
           [(seed,32); (word pc,libmldsa_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                    read PC s = word (pc + mldsa65_keypair_internal) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [pk; sk; seed] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(seed,32)) s = SEED /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events pk sk seed (mld_keypair_rho 6 5 SEED)
                             (mld_keypair_declass_65 SEED) guard mf mc pc
                             (word_sub stackpointer (word 11296))
                             returnaddress /\
                       memaccess_inbounds e2
                        [seed,32; pk,1952; sk,4032;
                         word_sub stackpointer (word 11296),11296;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; word(pc + got_memcpy),8; ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192;
                         word(pc + rodata_mld_zetas),1024;
                         word(pc + mld_compute_pack_t0_t165_consts),272]
                        [pk,1952; sk,4032;
                         word_sub stackpointer (word 11296),11296]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(pk,1952); memory :> bytes(sk,4032);
                  memory :> bytes(word_sub stackpointer (word 11296),11296)])`;;

let MLDSA_NATIVE_KEYPAIR_INTERNAL_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_KEYPAIR_INTERNAL_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT;;
