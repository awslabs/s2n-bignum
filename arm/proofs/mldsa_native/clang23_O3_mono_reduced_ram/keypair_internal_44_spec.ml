(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Key generation: the statement. This is the code for                       *)
(* mldsa44_keypair_internal (mld_sign_keypair_internal in sign.c, with       *)
(* mld_sample_pack_s1_s2 inlined) from mldsa-native's portable C             *)
(* implementation compiled by clang 23 with -O3 as one translation unit      *)
(* with MLD_CONFIG_REDUCE_RAM (see mldsa_native/README.md). It expands the   *)
(* seed into rho, rho' and the key with an inlined SHAKE256 (one call of     *)
(* mldsa_keccakf1600_permute), samples s2 and s1 from rho' with calls of     *)
(* mldsa44_poly_uniform_eta_4x (twice, four polynomials each), packs each    *)
(* polynomial into the secret key with inlined code (three bits per          *)
(* coefficient), transforms s1 to the NTT domain with four calls of          *)
(* mldsa_poly_ntt, copies rho into the public key, computes t and packs t1   *)
(* into the public key and t0 into the secret key with                       *)
(* mld_compute_pack_t0_t144, hashes the public key into tr with an inlined   *)
(* SHAKE256 (ten calls of mldsa_keccakf1600_permute), packs rho, the key     *)
(* and tr into the secret key, and zeroes its buffers with memset and        *)
(* stores. It is verified in the whole image (see libmldsa.ml) against       *)
(* mld_keypair_pk_44 and mld_keypair_sk_44 of common/mldsa_native_sign.ml,   *)
(* using the theorems for the callees and the contracts                      *)
(* memset_full_contract and memcpy_full_contract of                          *)
(* utils/mlkem_native_libc_full.ml (memcpy is used by compute_pack through   *)
(* the expansion of the matrix), assuming that the expansion of the matrix   *)
(* and the sampling of each polynomial terminate, and shown to be constant   *)
(* time and memory safe, with the events depending only on the addresses     *)
(* and the values that the C code declassifies (rho and                      *)
(* mld_keypair_declass_44). The stack is the 10112 bytes of the function     *)
(* and of its callees.                                                       *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native.ml";;
needs "arm/proofs/utils/mlkem_native_libc_full.ml";;
needs "common/mldsa_native_sign.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/poly_uniform_eta_4x_44_spec.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/compute_pack_t0_t1_44_spec.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/libmldsa.ml";;

(*** The code in the image, and the PLT stub for memset:

    mldsa44_keypair_internal:
       +0x0: stp     d15, d14, [sp, #-160]!
       +0x4: stp     d13, d12, [sp, #16]
       +0x8: stp     d11, d10, [sp, #32]
       +0xc: stp     d9, d8, [sp, #48]
      +0x10: stp     x29, x30, [sp, #64]
      +0x14: str     x28, [sp, #80]
      +0x18: stp     x26, x25, [sp, #96]
      +0x1c: stp     x24, x23, [sp, #112]
      +0x20: stp     x22, x21, [sp, #128]
      +0x24: stp     x20, x19, [sp, #144]
      +0x28: add     x29, sp, #0x40
      +0x2c: sub     x9, sp, #0x1, lsl #12
      +0x30: sub     x9, x9, #0x200
      +0x34: and     x9, x9, #0xffffffffffffffe0
      +0x38: sub     sp, sp, #0x1, lsl #12
      +0x3c: cmp     sp, x9
      +0x40: b.le    <mldsa44_keypair_internal+0x54>
      +0x44: ldr     xzr, [sp]
      +0x48: sub     sp, sp, #0x1, lsl #12
      +0x4c: cmp     sp, x9
      +0x50: b.gt    <mldsa44_keypair_internal+0x44>
      +0x54: mov     sp, x9
      +0x58: adrp    x8, <page>
      +0x5c: ldr     xzr, [sp]
      +0x60: movi    v1.2d, #0x0
      +0x64: ldr     x8, [x8, #4088]
      +0x68: add     x21, sp, #0x1, lsl #12
      +0x6c: mov     x20, x0
      +0x70: add     x21, x21, #0x120
      +0x74: add     x0, sp, #0x1, lsl #12
      +0x78: add     x23, sp, #0x1, lsl #12
      +0x7c: ldr     x8, [x8]
      +0x80: add     x0, x0, #0x120
      +0x84: mov     x19, x1
      +0x88: add     x22, sp, #0x20
      +0x8c: add     x23, x23, #0x120
      +0x90: str     x8, [sp, #4600]
      +0x94: add     x8, sp, #0x1, lsl #12
      +0x98: ldr     q0, [x2, #16]
      +0x9c: add     x8, x8, #0x60
      +0xa0: str     wzr, [sp, #4584]
      +0xa4: orr     x9, x8, #0x18
      +0xa8: stur    q1, [x21, #24]
      +0xac: str     q0, [sp, #4208]
      +0xb0: ldrb    w10, [x21, #25]
      +0xb4: ldrb    w12, [x21, #34]
      +0xb8: ldrb    w11, [x8, #25]
      +0xbc: ld1     {v0.b}[8], [x9]
      +0xc0: stur    q1, [x21, #184]
      +0xc4: stur    q1, [x21, #168]
      +0xc8: ldr     s2, [sp, #4220]
      +0xcc: ldr     q3, [sp, #4208]
      +0xd0: eor     w9, w10, w11
      +0xd4: ldrb    w10, [x8, #26]
      +0xd8: stur    q1, [x21, #152]
      +0xdc: mov     v0.b[9], w9
      +0xe0: ldrb    w9, [x21, #26]
      +0xe4: stur    q1, [x21, #136]
      +0xe8: stur    q1, [x21, #120]
      +0xec: zip1    v2.8b, v2.8b, v2.8b
      +0xf0: ldrb    w11, [x21, #33]
      +0xf4: stur    q1, [x21, #104]
      +0xf8: eor     w9, w9, w10
      +0xfc: ldrb    w10, [x8, #27]
     +0x100: stur    q1, [x21, #88]
     +0x104: stur    q1, [x21, #72]
     +0x108: mov     v0.b[10], w9
     +0x10c: ldrb    w9, [x21, #27]
     +0x110: stur    q1, [x21, #56]
     +0x114: stur    q1, [x21, #40]
     +0x118: eor     w9, w9, w10
     +0x11c: ldrb    w10, [x21, #32]
     +0x120: ldr     s1, [sp, #4412]
     +0x124: mov     v0.b[11], w9
     +0x128: mov     w9, #0x404
     +0x12c: zip1    v1.8b, v1.8b, v1.8b
     +0x130: strh    w9, [sp, #4224]
     +0x134: ldrb    w9, [x8, #32]
     +0x138: ldrb    w8, [x8, #33]
     +0x13c: mov     v3.s[2], v0.s[2]
     +0x140: eor     w9, w10, w9
     +0x144: ldrb    w10, [x21, #135]
     +0x148: eor     v1.8b, v1.8b, v2.8b
     +0x14c: ldr     q2, [x2]
     +0x150: eor     w8, w11, w8
     +0x154: strb    w8, [x21, #33]
     +0x158: eor     w8, w10, #0x80
     +0x15c: str     q2, [sp, #4192]
     +0x160: uzp1    v0.8b, v1.8b, v0.8b
     +0x164: strb    w9, [x21, #32]
     +0x168: eor     w9, w12, #0x1f
     +0x16c: strb    w8, [x21, #135]
     +0x170: mov     w8, #0x88
     +0x174: strb    w9, [x21, #34]
     +0x178: str     w8, [sp, #4584]
     +0x17c: mov     v3.s[3], v0.s[0]
     +0x180: ldr     q0, [sp, #4192]
     +0x184: str     q0, [sp, #4384]
     +0x188: str     q3, [sp, #4400]
     +0x18c: bl      <mldsa_keccakf1600_permute>
     +0x190: ldr     q0, [sp, #4448]
     +0x194: ldr     q1, [sp, #4464]
     +0x198: add     x26, sp, #0x1, lsl #12
     +0x19c: ldr     q2, [sp, #4496]
     +0x1a0: add     x26, x26, #0xa0
     +0x1a4: mov     w8, #0x7
     +0x1a8: str     q0, [sp, #4320]
     +0x1ac: ldr     q0, [sp, #4480]
     +0x1b0: add     x0, sp, #0x20
     +0x1b4: str     q1, [sp, #4336]
     +0x1b8: ldr     q1, [sp, #4384]
     +0x1bc: add     x1, x22, #0x400
     +0x1c0: str     q0, [sp, #4352]
     +0x1c4: ldr     q0, [sp, #4400]
     +0x1c8: add     x2, x22, #0x800
     +0x1cc: str     q2, [sp, #4368]
     +0x1d0: ldr     q2, [sp, #4416]
     +0x1d4: add     x3, x22, #0xc00
     +0x1d8: str     q0, [sp, #4272]
     +0x1dc: ldr     q0, [sp, #4432]
     +0x1e0: add     x4, x26, #0x20
     +0x1e4: str     q1, [sp, #4256]
     +0x1e8: mov     w5, #0x4
     +0x1ec: mov     w6, #0x5
     +0x1f0: str     q0, [sp, #4304]
     +0x1f4: movi    v0.2d, #0x0
     +0x1f8: mov     w7, #0x6
     +0x1fc: str     q2, [sp, #4288]
     +0x200: add     x25, x22, #0x400
     +0x204: add     x24, x22, #0x800
     +0x208: str     q0, [sp, #4512]
     +0x20c: str     q0, [sp, #4528]
     +0x210: str     q0, [sp, #4544]
     +0x214: str     q0, [sp, #4560]
     +0x218: str     q0, [sp, #4576]
     +0x21c: str     q0, [sp, #4384]
     +0x220: str     q0, [sp, #4400]
     +0x224: str     q0, [sp, #4416]
     +0x228: str     q0, [sp, #4432]
     +0x22c: str     q0, [sp, #4448]
     +0x230: str     q0, [sp, #4464]
     +0x234: str     q0, [sp, #4480]
     +0x238: str     q0, [sp, #4496]
     +0x23c: add     x23, x22, #0xc00
     +0x240: strb    w8, [sp]
     +0x244: bl      <mldsa44_poly_uniform_eta_4x>
     +0x248: movi    v0.16b, #0x2
     +0x24c: movi    v5.16b, #0x20
     +0x250: adrp    x8, <page>
     +0x254: ldr     q20, [x8, #1200]
     +0x258: add     x8, x22, #0x100
     +0x25c: mov     w9, #0x200
     +0x260: ldp     s16, s1, [x8, #-240]
     +0x264: sub     x10, x8, #0xd0
     +0x268: sub     x11, x8, #0xcc
     +0x26c: sub     x12, x8, #0xac
     +0x270: sub     x15, x8, #0x90
     +0x274: sub     x16, x8, #0x8c
     +0x278: mov     v15.16b, v20.16b
     +0x27c: sub     x14, x8, #0xdc
     +0x280: ld1     {v16.s}[1], [x10]
     +0x284: ld1     {v1.s}[1], [x11]
     +0x288: sub     x11, x8, #0xb0
     +0x28c: ldp     s20, s24, [x8, #-256]
     +0x290: sub     x10, x8, #0xe0
     +0x294: sub     x13, x8, #0xc0
     +0x298: add     x0, x8, #0xf4
     +0x29c: add     x17, x8, #0xa4
     +0x2a0: ld1     {v16.s}[2], [x11]
     +0x2a4: ld1     {v1.s}[2], [x12]
     +0x2a8: sub     x11, x8, #0xa0
     +0x2ac: ld1     {v20.s}[1], [x10]
     +0x2b0: sub     x10, x8, #0x50
     +0x2b4: ld1     {v24.s}[1], [x14]
     +0x2b8: sub     x12, x8, #0x60
     +0x2bc: sub     x14, x8, #0x40
     +0x2c0: sub     x18, x8, #0xd8
     +0x2c4: ld1     {v16.s}[3], [x15]
     +0x2c8: ld1     {v1.s}[3], [x16]
     +0x2cc: sub     x15, x8, #0x4c
     +0x2d0: ldp     s17, s2, [x8, #-112]
     +0x2d4: ld1     {v20.s}[2], [x13]
     +0x2d8: sub     x13, x8, #0x30
     +0x2dc: sub     x16, x8, #0x2c
     +0x2e0: ldp     s28, s6, [x8, #-248]
     +0x2e4: ld1     {v17.s}[1], [x10]
     +0x2e8: ld1     {v2.s}[1], [x15]
     +0x2ec: sub     x15, x8, #0xbc
     +0x2f0: ld1     {v24.s}[2], [x15]
     +0x2f4: sub     x15, x8, #0x9c
     +0x2f8: ld1     {v20.s}[3], [x11]
     +0x2fc: sub     x11, x8, #0xc
     +0x300: sub     x10, x8, #0x20
     +0x304: ld1     {v28.s}[1], [x18]
     +0x308: ld1     {v17.s}[2], [x13]
     +0x30c: ld1     {v2.s}[2], [x16]
     +0x310: sub     x16, x8, #0x10
     +0x314: ld1     {v24.s}[3], [x15]
     +0x318: sub     x13, x8, #0x5c
     +0x31c: add     x15, x8, #0x54
     +0x320: ldp     s21, s25, [x8, #-128]
     +0x324: ld1     {v17.s}[3], [x16]
     +0x328: ld1     {v2.s}[3], [x11]
     +0x32c: add     x11, x8, #0x30
     +0x330: ldp     s18, s3, [x8, #16]
     +0x334: add     x16, x8, #0x60
     +0x338: ld1     {v21.s}[1], [x12]
     +0x33c: add     x12, x8, #0x34
     +0x340: ld1     {v25.s}[1], [x13]
     +0x344: add     x13, x8, #0x20
     +0x348: ld1     {v18.s}[1], [x11]
     +0x34c: ld1     {v3.s}[1], [x12]
     +0x350: sub     x11, x8, #0x3c
     +0x354: ld1     {v21.s}[2], [x14]
     +0x358: add     x14, x8, #0x50
     +0x35c: ld1     {v25.s}[2], [x11]
     +0x360: sub     x11, x8, #0x1c
     +0x364: add     x12, x8, #0x40
     +0x368: ld1     {v18.s}[2], [x14]
     +0x36c: ld1     {v3.s}[2], [x15]
     +0x370: add     x14, x8, #0x70
     +0x374: ld1     {v21.s}[3], [x10]
     +0x378: add     x10, x8, #0x74
     +0x37c: ld1     {v25.s}[3], [x11]
     +0x380: ldp     s22, s26, [x8]
     +0x384: add     x15, x8, #0xa0
     +0x388: ld1     {v18.s}[3], [x14]
     +0x38c: ld1     {v3.s}[3], [x10]
     +0x390: add     x10, x8, #0x24
     +0x394: ldp     s19, s4, [x8, #144]
     +0x398: add     x14, x8, #0xb4
     +0x39c: ld1     {v22.s}[1], [x13]
     +0x3a0: ld1     {v26.s}[1], [x10]
     +0x3a4: add     x10, x8, #0x44
     +0x3a8: add     x13, x8, #0x64
     +0x3ac: add     x11, x8, #0xc0
     +0x3b0: ld1     {v4.s}[1], [x14]
     +0x3b4: add     x14, x8, #0xd4
     +0x3b8: ld1     {v22.s}[2], [x12]
     +0x3bc: ld1     {v26.s}[2], [x10]
     +0x3c0: add     x12, x8, #0xc4
     +0x3c4: add     x10, x8, #0xe4
     +0x3c8: ld1     {v4.s}[2], [x14]
     +0x3cc: sub     x14, x8, #0xb8
     +0x3d0: ld1     {v22.s}[3], [x16]
     +0x3d4: ld1     {v26.s}[3], [x13]
     +0x3d8: sub     x16, x8, #0xc8
     +0x3dc: ldp     s23, s27, [x8, #128]
     +0x3e0: ld1     {v28.s}[2], [x14]
     +0x3e4: ld1     {v4.s}[3], [x0]
     +0x3e8: sub     x14, x8, #0xc4
     +0x3ec: sub     x13, x8, #0x98
     +0x3f0: ld1     {v23.s}[1], [x15]
     +0x3f4: ld1     {v27.s}[1], [x17]
     +0x3f8: sub     x15, x8, #0xd4
     +0x3fc: tbl     v10.16b, {v1.16b-v4.16b}, v15.16b
     +0x400: ldp     s11, s1, [x8, #-232]
     +0x404: ld1     {v6.s}[1], [x15]
     +0x408: ld1     {v28.s}[3], [x13]
     +0x40c: sub     x13, x8, #0xa4
     +0x410: ld1     {v27.s}[2], [x12]
     +0x414: sub     x12, x8, #0xb4
     +0x418: ld1     {v23.s}[2], [x11]
     +0x41c: ld1     {v11.s}[1], [x16]
     +0x420: ld1     {v1.s}[1], [x14]
     +0x424: sub     x11, x8, #0x58
     +0x428: ld1     {v6.s}[2], [x12]
     +0x42c: sub     x12, x8, #0xa8
     +0x430: sub     x14, x8, #0x38
     +0x434: ld1     {v27.s}[3], [x10]
     +0x438: sub     x10, x8, #0x14
     +0x43c: add     x15, x8, #0x78
     +0x440: ld1     {v11.s}[2], [x12]
     +0x444: sub     x12, x8, #0x94
     +0x448: ld1     {v1.s}[2], [x13]
     +0x44c: ld1     {v6.s}[3], [x12]
     +0x450: sub     x12, x8, #0x88
     +0x454: sub     x13, x8, #0x44
     +0x458: ldp     s29, s7, [x8, #-120]
     +0x45c: tbl     v24.16b, {v24.16b-v27.16b}, v15.16b
     +0x460: ld1     {v11.s}[3], [x12]
     +0x464: sub     x12, x8, #0x84
     +0x468: ld1     {v1.s}[3], [x12]
     +0x46c: sub     x12, x8, #0x34
     +0x470: ld1     {v29.s}[1], [x11]
     +0x474: ldp     s12, s2, [x8, #-104]
     +0x478: sub     x11, x8, #0x54
     +0x47c: ld1     {v7.s}[1], [x11]
     +0x480: sub     x11, x8, #0x48
     +0x484: ld1     {v29.s}[2], [x14]
     +0x488: ld1     {v12.s}[1], [x11]
     +0x48c: ld1     {v2.s}[1], [x13]
     +0x490: sub     x11, x8, #0x18
     +0x494: add     x13, x8, #0x4c
     +0x498: add     x14, x8, #0x58
     +0x49c: ld1     {v7.s}[2], [x12]
     +0x4a0: sub     x12, x8, #0x28
     +0x4a4: ld1     {v29.s}[3], [x11]
     +0x4a8: ld1     {v12.s}[2], [x12]
     +0x4ac: sub     x11, x8, #0x24
     +0x4b0: ld1     {v2.s}[2], [x11]
     +0x4b4: add     x11, x8, #0x28
     +0x4b8: add     x12, x8, #0x38
     +0x4bc: ld1     {v7.s}[3], [x10]
     +0x4c0: sub     x10, x8, #0x8
     +0x4c4: ld1     {v12.s}[3], [x10]
     +0x4c8: sub     x10, x8, #0x4
     +0x4cc: ldp     s30, s8, [x8, #8]
     +0x4d0: ld1     {v2.s}[3], [x10]
     +0x4d4: ldp     s13, s3, [x8, #24]
     +0x4d8: add     x10, x8, #0x48
     +0x4dc: ld1     {v30.s}[1], [x11]
     +0x4e0: add     x11, x8, #0x2c
     +0x4e4: ld1     {v8.s}[1], [x11]
     +0x4e8: ld1     {v13.s}[1], [x12]
     +0x4ec: add     x12, x8, #0x3c
     +0x4f0: ld1     {v3.s}[1], [x12]
     +0x4f4: add     x11, x8, #0x68
     +0x4f8: add     x12, x8, #0xc8
     +0x4fc: ld1     {v30.s}[2], [x10]
     +0x500: add     x10, x8, #0xa8
     +0x504: ld1     {v8.s}[2], [x13]
     +0x508: add     x13, x8, #0x5c
     +0x50c: ld1     {v13.s}[2], [x14]
     +0x510: ld1     {v3.s}[2], [x13]
     +0x514: add     x14, x8, #0x6c
     +0x518: add     x13, x8, #0xb8
     +0x51c: ld1     {v30.s}[3], [x11]
     +0x520: add     x11, x8, #0x7c
     +0x524: ld1     {v13.s}[3], [x15]
     +0x528: ld1     {v8.s}[3], [x14]
     +0x52c: ld1     {v3.s}[3], [x11]
     +0x530: ldp     s31, s9, [x8, #136]
     +0x534: ldp     s14, s4, [x8, #152]
     +0x538: add     x11, x8, #0xac
     +0x53c: ld1     {v31.s}[1], [x10]
     +0x540: add     x10, x8, #0xb0
     +0x544: ld1     {v9.s}[1], [x11]
     +0x548: ld1     {v14.s}[1], [x13]
     +0x54c: ld1     {v19.s}[1], [x10]
     +0x550: add     x10, x8, #0xd8
     +0x554: add     x11, x8, #0xbc
     +0x558: add     x13, x8, #0xcc
     +0x55c: ld1     {v4.s}[1], [x11]
     +0x560: ld1     {v9.s}[2], [x13]
     +0x564: add     x11, x8, #0xdc
     +0x568: ld1     {v14.s}[2], [x10]
     +0x56c: add     x10, x8, #0xd0
     +0x570: ld1     {v31.s}[2], [x12]
     +0x574: ld1     {v19.s}[2], [x10]
     +0x578: add     x10, x8, #0xf8
     +0x57c: add     x12, x8, #0xe8
     +0x580: ld1     {v4.s}[2], [x11]
     +0x584: add     x11, x8, #0xf0
     +0x588: ld1     {v14.s}[3], [x10]
     +0x58c: add     x10, x8, #0xec
     +0x590: ld1     {v31.s}[3], [x12]
     +0x594: ld1     {v9.s}[3], [x10]
     +0x598: ld1     {v19.s}[3], [x11]
     +0x59c: add     x10, x8, #0xfc
     +0x5a0: ld1     {v4.s}[3], [x10]
     +0x5a4: add     x11, x8, #0xe0
     +0x5a8: add     x10, x19, x9
     +0x5ac: tbl     v11.16b, {v11.16b-v14.16b}, v15.16b
     +0x5b0: ld1     {v23.s}[3], [x11]
     +0x5b4: tbl     v25.16b, {v28.16b-v31.16b}, v15.16b
     +0x5b8: tbl     v6.16b, {v6.16b-v9.16b}, v15.16b
     +0x5bc: tbl     v7.16b, {v16.16b-v19.16b}, v15.16b
     +0x5c0: movi    v19.16b, #0x8
     +0x5c4: tbl     v1.16b, {v1.16b-v4.16b}, v15.16b
     +0x5c8: sub     v3.16b, v0.16b, v10.16b
     +0x5cc: shl     v17.16b, v24.16b, #3
     +0x5d0: tbl     v2.16b, {v20.16b-v23.16b}, v15.16b
     +0x5d4: movi    v21.16b, #0x4
     +0x5d8: mov     v20.16b, v15.16b
     +0x5dc: shl     v4.16b, v11.16b, #2
     +0x5e0: sub     v16.16b, v0.16b, v25.16b
     +0x5e4: add     x9, x9, #0x30
     +0x5e8: ushr    v18.16b, v3.16b, #1
     +0x5ec: add     v6.16b, v6.16b, v6.16b
     +0x5f0: shl     v7.16b, v7.16b, #4
     +0x5f4: shl     v1.16b, v1.16b, #5
     +0x5f8: shl     v3.16b, v3.16b, #7
     +0x5fc: cmp     x9, #0x260
     +0x600: sub     v4.16b, v19.16b, v4.16b
     +0x604: movi    v19.16b, #0x10
     +0x608: sub     v2.16b, v0.16b, v2.16b
     +0x60c: sub     v6.16b, v21.16b, v6.16b
     +0x610: sub     v7.16b, v5.16b, v7.16b
     +0x614: add     x8, x8, #0x200
     +0x618: orr     v4.16b, v4.16b, v18.16b
     +0x61c: movi    v18.16b, #0x40
     +0x620: sub     v17.16b, v19.16b, v17.16b
     +0x624: ushr    v19.16b, v16.16b, #2
     +0x628: shl     v16.16b, v16.16b, #6
     +0x62c: orr     v3.16b, v7.16b, v3.16b
     +0x630: sub     v1.16b, v18.16b, v1.16b
     +0x634: orr     v2.16b, v17.16b, v2.16b
     +0x638: orr     v6.16b, v6.16b, v19.16b
     +0x63c: orr     v19.16b, v4.16b, v1.16b
     +0x640: orr     v17.16b, v2.16b, v16.16b
     +0x644: orr     v18.16b, v6.16b, v3.16b
     +0x648: st3     {v17.16b-v19.16b}, [x10]
     +0x64c: b.ne    <mldsa44_keypair_internal+0x260>
     +0x650: movi    v0.16b, #0x2
     +0x654: movi    v5.16b, #0x20
     +0x658: str     xzr, [sp, #4384]
     +0x65c: add     x8, sp, #0x1, lsl #12
     +0x660: add     x9, x22, #0x400
     +0x664: add     x8, x8, #0x120
     +0x668: mov     w8, #0x260
     +0x66c: ldp     s16, s1, [x9, #16]
     +0x670: add     x10, x9, #0x30
     +0x674: add     x11, x9, #0x34
     +0x678: add     x13, x9, #0x50
     +0x67c: add     x14, x9, #0x54
     +0x680: ldp     s20, s24, [x9]
     +0x684: add     x15, x9, #0x70
     +0x688: ld1     {v16.s}[1], [x10]
     +0x68c: ld1     {v1.s}[1], [x11]
     +0x690: add     x10, x9, #0x20
     +0x694: add     x16, x9, #0x74
     +0x698: add     x11, x9, #0x40
     +0x69c: add     x12, x9, #0x60
     +0x6a0: ld1     {v20.s}[1], [x10]
     +0x6a4: add     x10, x9, #0x44
     +0x6a8: add     x18, x9, #0xd4
     +0x6ac: ld1     {v16.s}[2], [x13]
     +0x6b0: ld1     {v1.s}[2], [x14]
     +0x6b4: add     x13, x9, #0x24
     +0x6b8: ld1     {v24.s}[1], [x13]
     +0x6bc: add     x13, x9, #0xb4
     +0x6c0: add     x1, x9, #0xf4
     +0x6c4: ld1     {v20.s}[2], [x11]
     +0x6c8: add     x0, x9, #0xc4
     +0x6cc: add     x14, x9, #0xa0
     +0x6d0: ld1     {v16.s}[3], [x15]
     +0x6d4: ld1     {v1.s}[3], [x16]
     +0x6d8: add     x17, x9, #0xc0
     +0x6dc: ldp     s17, s2, [x9, #144]
     +0x6e0: ld1     {v24.s}[2], [x10]
     +0x6e4: add     x10, x9, #0x64
     +0x6e8: ld1     {v20.s}[3], [x12]
     +0x6ec: add     x15, x9, #0xe0
     +0x6f0: ldp     s28, s6, [x9, #8]
     +0x6f4: add     x16, x9, #0x120
     +0x6f8: ld1     {v2.s}[1], [x13]
     +0x6fc: ld1     {v24.s}[3], [x10]
     +0x700: add     x2, x9, #0x124
     +0x704: ldp     s21, s25, [x9, #128]
     +0x708: add     x13, x9, #0x140
     +0x70c: add     x11, x9, #0x160
     +0x710: add     x12, x9, #0x1a0
     +0x714: add     x10, x9, #0x1c0
     +0x718: ld1     {v2.s}[2], [x18]
     +0x71c: add     x18, x9, #0xa4
     +0x720: ld1     {v25.s}[1], [x18]
     +0x724: ld1     {v21.s}[1], [x14]
     +0x728: add     x18, x9, #0xe4
     +0x72c: add     x14, x9, #0x164
     +0x730: ld1     {v2.s}[3], [x1]
     +0x734: add     x1, x9, #0x144
     +0x738: ldr     s3, [x9, #276]
     +0x73c: ld1     {v25.s}[2], [x0]
     +0x740: add     x0, x9, #0x134
     +0x744: ld1     {v21.s}[2], [x17]
     +0x748: add     x17, x9, #0x48
     +0x74c: ld1     {v3.s}[1], [x0]
     +0x750: add     x0, x9, #0x28
     +0x754: ld1     {v28.s}[1], [x0]
     +0x758: add     x0, x9, #0x154
     +0x75c: ld1     {v25.s}[3], [x18]
     +0x760: ld1     {v21.s}[3], [x15]
     +0x764: add     x15, x9, #0x174
     +0x768: ldr     s26, [x9, #260]
     +0x76c: ld1     {v3.s}[2], [x0]
     +0x770: add     x0, x9, #0x2c
     +0x774: ldr     s22, [x9, #256]
     +0x778: ld1     {v6.s}[1], [x0]
     +0x77c: ld1     {v28.s}[2], [x17]
     +0x780: add     x17, x9, #0x4c
     +0x784: add     x18, x9, #0x68
     +0x788: ld1     {v26.s}[1], [x2]
     +0x78c: ld1     {v22.s}[1], [x16]
     +0x790: ld1     {v3.s}[3], [x15]
     +0x794: add     x15, x9, #0x6c
     +0x798: add     x16, x9, #0x1b4
     +0x79c: ld1     {v6.s}[2], [x17]
     +0x7a0: ldr     s4, [x9, #404]
     +0x7a4: ld1     {v28.s}[3], [x18]
     +0x7a8: ld1     {v26.s}[2], [x1]
     +0x7ac: ld1     {v22.s}[2], [x13]
     +0x7b0: add     x13, x9, #0x1d4
     +0x7b4: ld1     {v4.s}[1], [x16]
     +0x7b8: add     x16, x9, #0xa8
     +0x7bc: ld1     {v6.s}[3], [x15]
     +0x7c0: add     x15, x9, #0x1a4
     +0x7c4: ldp     s29, s7, [x9, #136]
     +0x7c8: ld1     {v26.s}[3], [x14]
     +0x7cc: ld1     {v4.s}[2], [x13]
     +0x7d0: add     x13, x9, #0xc8
     +0x7d4: ld1     {v22.s}[3], [x11]
     +0x7d8: add     x11, x9, #0x1f4
     +0x7dc: ldr     s27, [x9, #388]
     +0x7e0: ldr     s23, [x9, #384]
     +0x7e4: ld1     {v29.s}[1], [x16]
     +0x7e8: add     x14, x9, #0xe8
     +0x7ec: ld1     {v4.s}[3], [x11]
     +0x7f0: ld1     {v27.s}[1], [x15]
     +0x7f4: ld1     {v23.s}[1], [x12]
     +0x7f8: add     x11, x9, #0x128
     +0x7fc: add     x12, x9, #0x38
     +0x800: ld1     {v29.s}[2], [x13]
     +0x804: add     x13, x9, #0x1c4
     +0x808: tbl     v10.16b, {v1.16b-v4.16b}, v15.16b
     +0x80c: ldp     s11, s1, [x9, #24]
     +0x810: ld1     {v27.s}[2], [x13]
     +0x814: ld1     {v23.s}[2], [x10]
     +0x818: add     x10, x9, #0x1e4
     +0x81c: ld1     {v29.s}[3], [x14]
     +0x820: add     x14, x9, #0x78
     +0x824: add     x13, x9, #0x1a8
     +0x828: ldr     s30, [x9, #264]
     +0x82c: ld1     {v11.s}[1], [x12]
     +0x830: add     x12, x9, #0x168
     +0x834: ld1     {v27.s}[3], [x10]
     +0x838: add     x10, x9, #0x58
     +0x83c: ld1     {v30.s}[1], [x11]
     +0x840: add     x11, x9, #0x3c
     +0x844: ld1     {v1.s}[1], [x11]
     +0x848: ld1     {v11.s}[2], [x10]
     +0x84c: add     x10, x9, #0x5c
     +0x850: add     x11, x9, #0x148
     +0x854: tbl     v24.16b, {v24.16b-v27.16b}, v15.16b
     +0x858: ld1     {v30.s}[2], [x11]
     +0x85c: add     x11, x9, #0xac
     +0x860: ld1     {v1.s}[2], [x10]
     +0x864: ld1     {v7.s}[1], [x11]
     +0x868: add     x11, x9, #0x7c
     +0x86c: ld1     {v11.s}[3], [x14]
     +0x870: add     x14, x9, #0xb8
     +0x874: add     x10, x9, #0x1c8
     +0x878: ld1     {v30.s}[3], [x12]
     +0x87c: add     x12, x9, #0xcc
     +0x880: ld1     {v1.s}[3], [x11]
     +0x884: ld1     {v7.s}[2], [x12]
     +0x888: add     x12, x9, #0xb0
     +0x88c: ldp     s12, s2, [x9, #152]
     +0x890: ld1     {v17.s}[1], [x12]
     +0x894: add     x12, x9, #0xd8
     +0x898: add     x11, x9, #0xec
     +0x89c: ldr     s31, [x9, #392]
     +0x8a0: ld1     {v7.s}[3], [x11]
     +0x8a4: add     x11, x9, #0xd0
     +0x8a8: ld1     {v12.s}[1], [x14]
     +0x8ac: add     x14, x9, #0xbc
     +0x8b0: ld1     {v17.s}[2], [x11]
     +0x8b4: ld1     {v2.s}[1], [x14]
     +0x8b8: add     x11, x9, #0xf8
     +0x8bc: ldr     s8, [x9, #268]
     +0x8c0: ld1     {v31.s}[1], [x13]
     +0x8c4: add     x13, x9, #0x12c
     +0x8c8: add     x14, x9, #0x15c
     +0x8cc: ld1     {v12.s}[2], [x12]
     +0x8d0: add     x12, x9, #0xdc
     +0x8d4: ld1     {v8.s}[1], [x13]
     +0x8d8: ld1     {v2.s}[2], [x12]
     +0x8dc: add     x12, x9, #0xfc
     +0x8e0: add     x13, x9, #0x13c
     +0x8e4: ld1     {v31.s}[2], [x10]
     +0x8e8: add     x10, x9, #0x1d0
     +0x8ec: ld1     {v12.s}[3], [x11]
     +0x8f0: add     x11, x9, #0xf0
     +0x8f4: ldr     s13, [x9, #280]
     +0x8f8: ld1     {v17.s}[3], [x11]
     +0x8fc: add     x11, x9, #0x138
     +0x900: ldr     s18, [x9, #272]
     +0x904: ld1     {v2.s}[3], [x12]
     +0x908: add     x12, x9, #0x130
     +0x90c: ld1     {v13.s}[1], [x11]
     +0x910: ldr     s3, [x9, #284]
     +0x914: add     x11, x9, #0x14c
     +0x918: ld1     {v18.s}[1], [x12]
     +0x91c: add     x12, x9, #0x158
     +0x920: ld1     {v8.s}[2], [x11]
     +0x924: ld1     {v3.s}[1], [x13]
     +0x928: add     x13, x9, #0x150
     +0x92c: add     x11, x9, #0x16c
     +0x930: ld1     {v13.s}[2], [x12]
     +0x934: add     x12, x9, #0x1ac
     +0x938: ld1     {v18.s}[2], [x13]
     +0x93c: add     x13, x9, #0x178
     +0x940: ld1     {v8.s}[3], [x11]
     +0x944: ld1     {v3.s}[2], [x14]
     +0x948: add     x11, x9, #0x170
     +0x94c: ldr     s9, [x9, #396]
     +0x950: ld1     {v13.s}[3], [x13]
     +0x954: add     x13, x9, #0x17c
     +0x958: ldr     s14, [x9, #408]
     +0x95c: ld1     {v18.s}[3], [x11]
     +0x960: add     x11, x9, #0x1b8
     +0x964: ldr     s19, [x9, #400]
     +0x968: ld1     {v3.s}[3], [x13]
     +0x96c: ld1     {v9.s}[1], [x12]
     +0x970: ld1     {v14.s}[1], [x11]
     +0x974: add     x11, x9, #0x1b0
     +0x978: ldr     s4, [x9, #412]
     +0x97c: ld1     {v19.s}[1], [x11]
     +0x980: add     x11, x9, #0x1d8
     +0x984: add     x12, x9, #0x1bc
     +0x988: ld1     {v4.s}[1], [x12]
     +0x98c: add     x13, x9, #0x1cc
     +0x990: add     x12, x9, #0x1e8
     +0x994: ld1     {v14.s}[2], [x11]
     +0x998: ld1     {v9.s}[2], [x13]
     +0x99c: add     x11, x9, #0x1dc
     +0x9a0: ld1     {v19.s}[2], [x10]
     +0x9a4: add     x10, x9, #0x1f8
     +0x9a8: ld1     {v31.s}[3], [x12]
     +0x9ac: ld1     {v4.s}[2], [x11]
     +0x9b0: add     x11, x9, #0x1f0
     +0x9b4: ld1     {v14.s}[3], [x10]
     +0x9b8: add     x10, x9, #0x1ec
     +0x9bc: ld1     {v9.s}[3], [x10]
     +0x9c0: ld1     {v19.s}[3], [x11]
     +0x9c4: add     x10, x9, #0x1fc
     +0x9c8: ld1     {v4.s}[3], [x10]
     +0x9cc: add     x11, x9, #0x1e0
     +0x9d0: tbl     v25.16b, {v28.16b-v31.16b}, v15.16b
     +0x9d4: tbl     v11.16b, {v11.16b-v14.16b}, v15.16b
     +0x9d8: ld1     {v23.s}[3], [x11]
     +0x9dc: add     x10, x19, x8
     +0x9e0: tbl     v6.16b, {v6.16b-v9.16b}, v15.16b
     +0x9e4: tbl     v7.16b, {v16.16b-v19.16b}, v15.16b
     +0x9e8: movi    v19.16b, #0x8
     +0x9ec: tbl     v1.16b, {v1.16b-v4.16b}, v15.16b
     +0x9f0: sub     v3.16b, v0.16b, v10.16b
     +0x9f4: shl     v17.16b, v24.16b, #3
     +0x9f8: tbl     v2.16b, {v20.16b-v23.16b}, v15.16b
     +0x9fc: movi    v20.16b, #0x4
     +0xa00: sub     v16.16b, v0.16b, v25.16b
     +0xa04: shl     v4.16b, v11.16b, #2
     +0xa08: add     x8, x8, #0x30
     +0xa0c: add     x9, x9, #0x200
     +0xa10: ushr    v18.16b, v3.16b, #1
     +0xa14: add     v6.16b, v6.16b, v6.16b
     +0xa18: shl     v7.16b, v7.16b, #4
     +0xa1c: shl     v1.16b, v1.16b, #5
     +0xa20: shl     v3.16b, v3.16b, #7
     +0xa24: cmp     x8, #0x2c0
     +0xa28: sub     v4.16b, v19.16b, v4.16b
     +0xa2c: movi    v19.16b, #0x10
     +0xa30: sub     v2.16b, v0.16b, v2.16b
     +0xa34: sub     v6.16b, v20.16b, v6.16b
     +0xa38: sub     v7.16b, v5.16b, v7.16b
     +0xa3c: orr     v4.16b, v4.16b, v18.16b
     +0xa40: movi    v18.16b, #0x40
     +0xa44: sub     v17.16b, v19.16b, v17.16b
     +0xa48: ushr    v19.16b, v16.16b, #2
     +0xa4c: shl     v16.16b, v16.16b, #6
     +0xa50: orr     v3.16b, v7.16b, v3.16b
     +0xa54: sub     v1.16b, v18.16b, v1.16b
     +0xa58: orr     v2.16b, v17.16b, v2.16b
     +0xa5c: orr     v6.16b, v6.16b, v19.16b
     +0xa60: orr     v19.16b, v4.16b, v1.16b
     +0xa64: orr     v17.16b, v2.16b, v16.16b
     +0xa68: orr     v18.16b, v6.16b, v3.16b
     +0xa6c: st3     {v17.16b-v19.16b}, [x10]
     +0xa70: b.ne    <mldsa44_keypair_internal+0x66c>
     +0xa74: movi    v0.16b, #0x2
     +0xa78: movi    v5.16b, #0x20
     +0xa7c: str     xzr, [sp, #4384]
     +0xa80: add     x8, sp, #0x1, lsl #12
     +0xa84: add     x9, x22, #0x800
     +0xa88: add     x8, x8, #0x120
     +0xa8c: mov     w8, #0x2c0
     +0xa90: ldp     s16, s1, [x9, #16]
     +0xa94: add     x10, x9, #0x30
     +0xa98: add     x11, x9, #0x34
     +0xa9c: add     x13, x9, #0x50
     +0xaa0: add     x14, x9, #0x54
     +0xaa4: ldp     s20, s24, [x9]
     +0xaa8: add     x15, x9, #0x70
     +0xaac: ld1     {v16.s}[1], [x10]
     +0xab0: ld1     {v1.s}[1], [x11]
     +0xab4: add     x10, x9, #0x20
     +0xab8: add     x16, x9, #0x74
     +0xabc: add     x11, x9, #0x40
     +0xac0: add     x12, x9, #0x60
     +0xac4: ld1     {v20.s}[1], [x10]
     +0xac8: add     x10, x9, #0x44
     +0xacc: add     x18, x9, #0xd4
     +0xad0: ld1     {v16.s}[2], [x13]
     +0xad4: ld1     {v1.s}[2], [x14]
     +0xad8: add     x13, x9, #0x24
     +0xadc: ld1     {v24.s}[1], [x13]
     +0xae0: add     x13, x9, #0xb4
     +0xae4: add     x1, x9, #0xf4
     +0xae8: ld1     {v20.s}[2], [x11]
     +0xaec: add     x0, x9, #0xc4
     +0xaf0: add     x14, x9, #0xa0
     +0xaf4: ld1     {v16.s}[3], [x15]
     +0xaf8: ld1     {v1.s}[3], [x16]
     +0xafc: add     x17, x9, #0xc0
     +0xb00: ldp     s17, s2, [x9, #144]
     +0xb04: ld1     {v24.s}[2], [x10]
     +0xb08: add     x10, x9, #0x64
     +0xb0c: ld1     {v20.s}[3], [x12]
     +0xb10: add     x15, x9, #0xe0
     +0xb14: ldp     s28, s6, [x9, #8]
     +0xb18: add     x16, x9, #0x120
     +0xb1c: ld1     {v2.s}[1], [x13]
     +0xb20: ld1     {v24.s}[3], [x10]
     +0xb24: add     x2, x9, #0x124
     +0xb28: ldp     s21, s25, [x9, #128]
     +0xb2c: add     x13, x9, #0x140
     +0xb30: add     x11, x9, #0x160
     +0xb34: add     x12, x9, #0x1a0
     +0xb38: add     x10, x9, #0x1c0
     +0xb3c: ld1     {v2.s}[2], [x18]
     +0xb40: add     x18, x9, #0xa4
     +0xb44: ld1     {v25.s}[1], [x18]
     +0xb48: ld1     {v21.s}[1], [x14]
     +0xb4c: add     x18, x9, #0xe4
     +0xb50: add     x14, x9, #0x164
     +0xb54: ld1     {v2.s}[3], [x1]
     +0xb58: add     x1, x9, #0x144
     +0xb5c: ldr     s3, [x9, #276]
     +0xb60: ld1     {v25.s}[2], [x0]
     +0xb64: add     x0, x9, #0x134
     +0xb68: ld1     {v21.s}[2], [x17]
     +0xb6c: add     x17, x9, #0x48
     +0xb70: ld1     {v3.s}[1], [x0]
     +0xb74: add     x0, x9, #0x28
     +0xb78: ld1     {v28.s}[1], [x0]
     +0xb7c: add     x0, x9, #0x154
     +0xb80: ld1     {v25.s}[3], [x18]
     +0xb84: ld1     {v21.s}[3], [x15]
     +0xb88: add     x15, x9, #0x174
     +0xb8c: ldr     s26, [x9, #260]
     +0xb90: ld1     {v3.s}[2], [x0]
     +0xb94: add     x0, x9, #0x2c
     +0xb98: ldr     s22, [x9, #256]
     +0xb9c: ld1     {v6.s}[1], [x0]
     +0xba0: ld1     {v28.s}[2], [x17]
     +0xba4: add     x17, x9, #0x4c
     +0xba8: add     x18, x9, #0x68
     +0xbac: ld1     {v26.s}[1], [x2]
     +0xbb0: ld1     {v22.s}[1], [x16]
     +0xbb4: ld1     {v3.s}[3], [x15]
     +0xbb8: add     x15, x9, #0x6c
     +0xbbc: add     x16, x9, #0x1b4
     +0xbc0: ld1     {v6.s}[2], [x17]
     +0xbc4: ldr     s4, [x9, #404]
     +0xbc8: ld1     {v28.s}[3], [x18]
     +0xbcc: ld1     {v26.s}[2], [x1]
     +0xbd0: ld1     {v22.s}[2], [x13]
     +0xbd4: add     x13, x9, #0x1d4
     +0xbd8: ld1     {v4.s}[1], [x16]
     +0xbdc: add     x16, x9, #0xa8
     +0xbe0: ld1     {v6.s}[3], [x15]
     +0xbe4: add     x15, x9, #0x1a4
     +0xbe8: ldp     s29, s7, [x9, #136]
     +0xbec: ld1     {v26.s}[3], [x14]
     +0xbf0: ld1     {v4.s}[2], [x13]
     +0xbf4: add     x13, x9, #0xc8
     +0xbf8: ld1     {v22.s}[3], [x11]
     +0xbfc: add     x11, x9, #0x1f4
     +0xc00: ldr     s27, [x9, #388]
     +0xc04: ldr     s23, [x9, #384]
     +0xc08: ld1     {v29.s}[1], [x16]
     +0xc0c: add     x14, x9, #0xe8
     +0xc10: ld1     {v4.s}[3], [x11]
     +0xc14: ld1     {v27.s}[1], [x15]
     +0xc18: ld1     {v23.s}[1], [x12]
     +0xc1c: add     x11, x9, #0x128
     +0xc20: add     x12, x9, #0x38
     +0xc24: ld1     {v29.s}[2], [x13]
     +0xc28: add     x13, x9, #0x1c4
     +0xc2c: tbl     v10.16b, {v1.16b-v4.16b}, v15.16b
     +0xc30: ldp     s11, s1, [x9, #24]
     +0xc34: ld1     {v27.s}[2], [x13]
     +0xc38: ld1     {v23.s}[2], [x10]
     +0xc3c: add     x10, x9, #0x1e4
     +0xc40: ld1     {v29.s}[3], [x14]
     +0xc44: add     x14, x9, #0x78
     +0xc48: add     x13, x9, #0x1a8
     +0xc4c: ldr     s30, [x9, #264]
     +0xc50: ld1     {v11.s}[1], [x12]
     +0xc54: add     x12, x9, #0x168
     +0xc58: ld1     {v27.s}[3], [x10]
     +0xc5c: add     x10, x9, #0x58
     +0xc60: ld1     {v30.s}[1], [x11]
     +0xc64: add     x11, x9, #0x3c
     +0xc68: ld1     {v1.s}[1], [x11]
     +0xc6c: ld1     {v11.s}[2], [x10]
     +0xc70: add     x10, x9, #0x5c
     +0xc74: add     x11, x9, #0x148
     +0xc78: tbl     v24.16b, {v24.16b-v27.16b}, v15.16b
     +0xc7c: ld1     {v30.s}[2], [x11]
     +0xc80: add     x11, x9, #0xac
     +0xc84: ld1     {v1.s}[2], [x10]
     +0xc88: ld1     {v7.s}[1], [x11]
     +0xc8c: add     x11, x9, #0x7c
     +0xc90: ld1     {v11.s}[3], [x14]
     +0xc94: add     x14, x9, #0xb8
     +0xc98: add     x10, x9, #0x1c8
     +0xc9c: ld1     {v30.s}[3], [x12]
     +0xca0: add     x12, x9, #0xcc
     +0xca4: ld1     {v1.s}[3], [x11]
     +0xca8: ld1     {v7.s}[2], [x12]
     +0xcac: add     x12, x9, #0xb0
     +0xcb0: ldp     s12, s2, [x9, #152]
     +0xcb4: ld1     {v17.s}[1], [x12]
     +0xcb8: add     x12, x9, #0xd8
     +0xcbc: add     x11, x9, #0xec
     +0xcc0: ldr     s31, [x9, #392]
     +0xcc4: ld1     {v7.s}[3], [x11]
     +0xcc8: add     x11, x9, #0xd0
     +0xccc: ld1     {v12.s}[1], [x14]
     +0xcd0: add     x14, x9, #0xbc
     +0xcd4: ld1     {v17.s}[2], [x11]
     +0xcd8: ld1     {v2.s}[1], [x14]
     +0xcdc: add     x11, x9, #0xf8
     +0xce0: ldr     s8, [x9, #268]
     +0xce4: ld1     {v31.s}[1], [x13]
     +0xce8: add     x13, x9, #0x12c
     +0xcec: add     x14, x9, #0x15c
     +0xcf0: ld1     {v12.s}[2], [x12]
     +0xcf4: add     x12, x9, #0xdc
     +0xcf8: ld1     {v8.s}[1], [x13]
     +0xcfc: ld1     {v2.s}[2], [x12]
     +0xd00: add     x12, x9, #0xfc
     +0xd04: add     x13, x9, #0x13c
     +0xd08: ld1     {v31.s}[2], [x10]
     +0xd0c: add     x10, x9, #0x1d0
     +0xd10: ld1     {v12.s}[3], [x11]
     +0xd14: add     x11, x9, #0xf0
     +0xd18: ldr     s13, [x9, #280]
     +0xd1c: ld1     {v17.s}[3], [x11]
     +0xd20: add     x11, x9, #0x138
     +0xd24: ldr     s18, [x9, #272]
     +0xd28: ld1     {v2.s}[3], [x12]
     +0xd2c: add     x12, x9, #0x130
     +0xd30: ld1     {v13.s}[1], [x11]
     +0xd34: ldr     s3, [x9, #284]
     +0xd38: add     x11, x9, #0x14c
     +0xd3c: ld1     {v18.s}[1], [x12]
     +0xd40: add     x12, x9, #0x158
     +0xd44: ld1     {v8.s}[2], [x11]
     +0xd48: ld1     {v3.s}[1], [x13]
     +0xd4c: add     x13, x9, #0x150
     +0xd50: add     x11, x9, #0x16c
     +0xd54: ld1     {v13.s}[2], [x12]
     +0xd58: add     x12, x9, #0x1ac
     +0xd5c: ld1     {v18.s}[2], [x13]
     +0xd60: add     x13, x9, #0x178
     +0xd64: ld1     {v8.s}[3], [x11]
     +0xd68: ld1     {v3.s}[2], [x14]
     +0xd6c: add     x11, x9, #0x170
     +0xd70: ldr     s9, [x9, #396]
     +0xd74: ld1     {v13.s}[3], [x13]
     +0xd78: add     x13, x9, #0x17c
     +0xd7c: ldr     s14, [x9, #408]
     +0xd80: ld1     {v18.s}[3], [x11]
     +0xd84: add     x11, x9, #0x1b8
     +0xd88: ldr     s19, [x9, #400]
     +0xd8c: ld1     {v3.s}[3], [x13]
     +0xd90: ld1     {v9.s}[1], [x12]
     +0xd94: ld1     {v14.s}[1], [x11]
     +0xd98: add     x11, x9, #0x1b0
     +0xd9c: ldr     s4, [x9, #412]
     +0xda0: ld1     {v19.s}[1], [x11]
     +0xda4: add     x11, x9, #0x1d8
     +0xda8: add     x12, x9, #0x1bc
     +0xdac: ld1     {v4.s}[1], [x12]
     +0xdb0: add     x13, x9, #0x1cc
     +0xdb4: add     x12, x9, #0x1e8
     +0xdb8: ld1     {v14.s}[2], [x11]
     +0xdbc: ld1     {v9.s}[2], [x13]
     +0xdc0: add     x11, x9, #0x1dc
     +0xdc4: ld1     {v19.s}[2], [x10]
     +0xdc8: add     x10, x9, #0x1f8
     +0xdcc: ld1     {v31.s}[3], [x12]
     +0xdd0: ld1     {v4.s}[2], [x11]
     +0xdd4: add     x11, x9, #0x1f0
     +0xdd8: ld1     {v14.s}[3], [x10]
     +0xddc: add     x10, x9, #0x1ec
     +0xde0: ld1     {v9.s}[3], [x10]
     +0xde4: ld1     {v19.s}[3], [x11]
     +0xde8: add     x10, x9, #0x1fc
     +0xdec: ld1     {v4.s}[3], [x10]
     +0xdf0: add     x11, x9, #0x1e0
     +0xdf4: tbl     v25.16b, {v28.16b-v31.16b}, v15.16b
     +0xdf8: tbl     v11.16b, {v11.16b-v14.16b}, v15.16b
     +0xdfc: ld1     {v23.s}[3], [x11]
     +0xe00: add     x10, x19, x8
     +0xe04: tbl     v6.16b, {v6.16b-v9.16b}, v15.16b
     +0xe08: tbl     v7.16b, {v16.16b-v19.16b}, v15.16b
     +0xe0c: movi    v19.16b, #0x8
     +0xe10: tbl     v1.16b, {v1.16b-v4.16b}, v15.16b
     +0xe14: sub     v3.16b, v0.16b, v10.16b
     +0xe18: shl     v17.16b, v24.16b, #3
     +0xe1c: tbl     v2.16b, {v20.16b-v23.16b}, v15.16b
     +0xe20: movi    v21.16b, #0x4
     +0xe24: sub     v16.16b, v0.16b, v25.16b
     +0xe28: shl     v4.16b, v11.16b, #2
     +0xe2c: add     x8, x8, #0x30
     +0xe30: add     x9, x9, #0x200
     +0xe34: ushr    v18.16b, v3.16b, #1
     +0xe38: add     v6.16b, v6.16b, v6.16b
     +0xe3c: shl     v7.16b, v7.16b, #4
     +0xe40: shl     v1.16b, v1.16b, #5
     +0xe44: shl     v3.16b, v3.16b, #7
     +0xe48: cmp     x8, #0x320
     +0xe4c: sub     v4.16b, v19.16b, v4.16b
     +0xe50: movi    v19.16b, #0x10
     +0xe54: sub     v2.16b, v0.16b, v2.16b
     +0xe58: sub     v6.16b, v21.16b, v6.16b
     +0xe5c: sub     v7.16b, v5.16b, v7.16b
     +0xe60: orr     v4.16b, v4.16b, v18.16b
     +0xe64: movi    v18.16b, #0x40
     +0xe68: sub     v17.16b, v19.16b, v17.16b
     +0xe6c: ushr    v19.16b, v16.16b, #2
     +0xe70: shl     v16.16b, v16.16b, #6
     +0xe74: orr     v3.16b, v7.16b, v3.16b
     +0xe78: sub     v1.16b, v18.16b, v1.16b
     +0xe7c: orr     v2.16b, v17.16b, v2.16b
     +0xe80: orr     v6.16b, v6.16b, v19.16b
     +0xe84: orr     v19.16b, v4.16b, v1.16b
     +0xe88: orr     v17.16b, v2.16b, v16.16b
     +0xe8c: orr     v18.16b, v6.16b, v3.16b
     +0xe90: st3     {v17.16b-v19.16b}, [x10]
     +0xe94: b.ne    <mldsa44_keypair_internal+0xa90>
     +0xe98: str     xzr, [sp, #4384]
     +0xe9c: add     x8, sp, #0x1, lsl #12
     +0xea0: movi    v0.16b, #0x2
     +0xea4: movi    v5.16b, #0x20
     +0xea8: add     x8, x8, #0x120
     +0xeac: str     q15, [sp, #16]
     +0xeb0: mov     w8, #0x320
     +0xeb4: add     x9, x22, #0xc00
     +0xeb8: ldr     q15, [sp, #16]
     +0xebc: ldp     s16, s1, [x9, #16]
     +0xec0: add     x10, x9, #0x30
     +0xec4: add     x11, x9, #0x34
     +0xec8: add     x13, x9, #0x50
     +0xecc: add     x14, x9, #0x54
     +0xed0: ldp     s20, s24, [x9]
     +0xed4: add     x15, x9, #0x70
     +0xed8: ld1     {v16.s}[1], [x10]
     +0xedc: ld1     {v1.s}[1], [x11]
     +0xee0: add     x10, x9, #0x20
     +0xee4: add     x16, x9, #0x74
     +0xee8: add     x11, x9, #0x40
     +0xeec: add     x12, x9, #0x60
     +0xef0: ld1     {v20.s}[1], [x10]
     +0xef4: add     x10, x9, #0x44
     +0xef8: add     x18, x9, #0xd4
     +0xefc: ld1     {v16.s}[2], [x13]
     +0xf00: ld1     {v1.s}[2], [x14]
     +0xf04: add     x13, x9, #0x24
     +0xf08: ld1     {v24.s}[1], [x13]
     +0xf0c: add     x13, x9, #0xb4
     +0xf10: add     x1, x9, #0xf4
     +0xf14: ld1     {v20.s}[2], [x11]
     +0xf18: add     x0, x9, #0xc4
     +0xf1c: add     x14, x9, #0xa0
     +0xf20: ld1     {v16.s}[3], [x15]
     +0xf24: ld1     {v1.s}[3], [x16]
     +0xf28: add     x17, x9, #0xc0
     +0xf2c: ldp     s17, s2, [x9, #144]
     +0xf30: ld1     {v24.s}[2], [x10]
     +0xf34: add     x10, x9, #0x64
     +0xf38: ld1     {v20.s}[3], [x12]
     +0xf3c: add     x15, x9, #0xe0
     +0xf40: ldp     s28, s6, [x9, #8]
     +0xf44: add     x16, x9, #0x120
     +0xf48: ld1     {v2.s}[1], [x13]
     +0xf4c: ld1     {v24.s}[3], [x10]
     +0xf50: add     x2, x9, #0x124
     +0xf54: ldp     s21, s25, [x9, #128]
     +0xf58: add     x13, x9, #0x140
     +0xf5c: add     x11, x9, #0x160
     +0xf60: add     x12, x9, #0x1a0
     +0xf64: add     x10, x9, #0x1c0
     +0xf68: ld1     {v2.s}[2], [x18]
     +0xf6c: add     x18, x9, #0xa4
     +0xf70: ld1     {v25.s}[1], [x18]
     +0xf74: ld1     {v21.s}[1], [x14]
     +0xf78: add     x18, x9, #0xe4
     +0xf7c: add     x14, x9, #0x164
     +0xf80: ld1     {v2.s}[3], [x1]
     +0xf84: add     x1, x9, #0x144
     +0xf88: ldr     s3, [x9, #276]
     +0xf8c: ld1     {v25.s}[2], [x0]
     +0xf90: add     x0, x9, #0x134
     +0xf94: ld1     {v21.s}[2], [x17]
     +0xf98: add     x17, x9, #0x48
     +0xf9c: ld1     {v3.s}[1], [x0]
     +0xfa0: add     x0, x9, #0x28
     +0xfa4: ld1     {v28.s}[1], [x0]
     +0xfa8: add     x0, x9, #0x154
     +0xfac: ld1     {v25.s}[3], [x18]
     +0xfb0: ld1     {v21.s}[3], [x15]
     +0xfb4: add     x15, x9, #0x174
     +0xfb8: ldr     s26, [x9, #260]
     +0xfbc: ld1     {v3.s}[2], [x0]
     +0xfc0: add     x0, x9, #0x2c
     +0xfc4: ldr     s22, [x9, #256]
     +0xfc8: ld1     {v6.s}[1], [x0]
     +0xfcc: ld1     {v28.s}[2], [x17]
     +0xfd0: add     x17, x9, #0x4c
     +0xfd4: add     x18, x9, #0x68
     +0xfd8: ld1     {v26.s}[1], [x2]
     +0xfdc: ld1     {v22.s}[1], [x16]
     +0xfe0: ld1     {v3.s}[3], [x15]
     +0xfe4: add     x15, x9, #0x6c
     +0xfe8: add     x16, x9, #0x1b4
     +0xfec: ld1     {v6.s}[2], [x17]
     +0xff0: ldr     s4, [x9, #404]
     +0xff4: ld1     {v28.s}[3], [x18]
     +0xff8: ld1     {v26.s}[2], [x1]
     +0xffc: ld1     {v22.s}[2], [x13]
    +0x1000: add     x13, x9, #0x1d4
    +0x1004: ld1     {v4.s}[1], [x16]
    +0x1008: add     x16, x9, #0xa8
    +0x100c: ld1     {v6.s}[3], [x15]
    +0x1010: add     x15, x9, #0x1a4
    +0x1014: ldp     s29, s7, [x9, #136]
    +0x1018: ld1     {v26.s}[3], [x14]
    +0x101c: ld1     {v4.s}[2], [x13]
    +0x1020: add     x13, x9, #0xc8
    +0x1024: ld1     {v22.s}[3], [x11]
    +0x1028: add     x11, x9, #0x1f4
    +0x102c: ldr     s27, [x9, #388]
    +0x1030: ldr     s23, [x9, #384]
    +0x1034: ld1     {v29.s}[1], [x16]
    +0x1038: add     x14, x9, #0xe8
    +0x103c: ld1     {v4.s}[3], [x11]
    +0x1040: ld1     {v27.s}[1], [x15]
    +0x1044: ld1     {v23.s}[1], [x12]
    +0x1048: add     x11, x9, #0x128
    +0x104c: add     x12, x9, #0x38
    +0x1050: ld1     {v29.s}[2], [x13]
    +0x1054: add     x13, x9, #0x1c4
    +0x1058: tbl     v10.16b, {v1.16b-v4.16b}, v15.16b
    +0x105c: ldp     s11, s1, [x9, #24]
    +0x1060: ld1     {v27.s}[2], [x13]
    +0x1064: ld1     {v23.s}[2], [x10]
    +0x1068: add     x10, x9, #0x1e4
    +0x106c: ld1     {v29.s}[3], [x14]
    +0x1070: add     x14, x9, #0x78
    +0x1074: add     x13, x9, #0x1a8
    +0x1078: ldr     s30, [x9, #264]
    +0x107c: ld1     {v11.s}[1], [x12]
    +0x1080: add     x12, x9, #0x168
    +0x1084: ld1     {v27.s}[3], [x10]
    +0x1088: add     x10, x9, #0x58
    +0x108c: ld1     {v30.s}[1], [x11]
    +0x1090: add     x11, x9, #0x3c
    +0x1094: ld1     {v1.s}[1], [x11]
    +0x1098: ld1     {v11.s}[2], [x10]
    +0x109c: add     x10, x9, #0x5c
    +0x10a0: add     x11, x9, #0x148
    +0x10a4: tbl     v24.16b, {v24.16b-v27.16b}, v15.16b
    +0x10a8: ld1     {v30.s}[2], [x11]
    +0x10ac: add     x11, x9, #0xac
    +0x10b0: ld1     {v1.s}[2], [x10]
    +0x10b4: ld1     {v7.s}[1], [x11]
    +0x10b8: add     x11, x9, #0x7c
    +0x10bc: ld1     {v11.s}[3], [x14]
    +0x10c0: add     x14, x9, #0xb8
    +0x10c4: add     x10, x9, #0x1c8
    +0x10c8: ld1     {v30.s}[3], [x12]
    +0x10cc: add     x12, x9, #0xcc
    +0x10d0: ld1     {v1.s}[3], [x11]
    +0x10d4: ld1     {v7.s}[2], [x12]
    +0x10d8: add     x12, x9, #0xb0
    +0x10dc: ldp     s12, s2, [x9, #152]
    +0x10e0: ld1     {v17.s}[1], [x12]
    +0x10e4: add     x12, x9, #0xd8
    +0x10e8: add     x11, x9, #0xec
    +0x10ec: ldr     s31, [x9, #392]
    +0x10f0: ld1     {v7.s}[3], [x11]
    +0x10f4: add     x11, x9, #0xd0
    +0x10f8: ld1     {v12.s}[1], [x14]
    +0x10fc: add     x14, x9, #0xbc
    +0x1100: ld1     {v17.s}[2], [x11]
    +0x1104: ld1     {v2.s}[1], [x14]
    +0x1108: add     x11, x9, #0xf8
    +0x110c: ldr     s8, [x9, #268]
    +0x1110: ld1     {v31.s}[1], [x13]
    +0x1114: add     x13, x9, #0x12c
    +0x1118: add     x14, x9, #0x15c
    +0x111c: ld1     {v12.s}[2], [x12]
    +0x1120: add     x12, x9, #0xdc
    +0x1124: ld1     {v8.s}[1], [x13]
    +0x1128: ld1     {v2.s}[2], [x12]
    +0x112c: add     x12, x9, #0xfc
    +0x1130: add     x13, x9, #0x13c
    +0x1134: ld1     {v31.s}[2], [x10]
    +0x1138: add     x10, x9, #0x1d0
    +0x113c: ld1     {v12.s}[3], [x11]
    +0x1140: add     x11, x9, #0xf0
    +0x1144: ldr     s13, [x9, #280]
    +0x1148: ld1     {v17.s}[3], [x11]
    +0x114c: add     x11, x9, #0x138
    +0x1150: ldr     s18, [x9, #272]
    +0x1154: ld1     {v2.s}[3], [x12]
    +0x1158: add     x12, x9, #0x130
    +0x115c: ld1     {v13.s}[1], [x11]
    +0x1160: ldr     s3, [x9, #284]
    +0x1164: add     x11, x9, #0x14c
    +0x1168: ld1     {v18.s}[1], [x12]
    +0x116c: add     x12, x9, #0x158
    +0x1170: ld1     {v8.s}[2], [x11]
    +0x1174: ld1     {v3.s}[1], [x13]
    +0x1178: add     x13, x9, #0x150
    +0x117c: add     x11, x9, #0x16c
    +0x1180: ld1     {v13.s}[2], [x12]
    +0x1184: add     x12, x9, #0x1ac
    +0x1188: ld1     {v18.s}[2], [x13]
    +0x118c: add     x13, x9, #0x178
    +0x1190: ld1     {v8.s}[3], [x11]
    +0x1194: ld1     {v3.s}[2], [x14]
    +0x1198: add     x11, x9, #0x170
    +0x119c: ldr     s9, [x9, #396]
    +0x11a0: ld1     {v13.s}[3], [x13]
    +0x11a4: add     x13, x9, #0x17c
    +0x11a8: ldr     s14, [x9, #408]
    +0x11ac: ld1     {v18.s}[3], [x11]
    +0x11b0: add     x11, x9, #0x1b8
    +0x11b4: ldr     s19, [x9, #400]
    +0x11b8: ld1     {v3.s}[3], [x13]
    +0x11bc: ld1     {v9.s}[1], [x12]
    +0x11c0: ld1     {v14.s}[1], [x11]
    +0x11c4: add     x11, x9, #0x1b0
    +0x11c8: ldr     s4, [x9, #412]
    +0x11cc: ld1     {v19.s}[1], [x11]
    +0x11d0: add     x11, x9, #0x1d8
    +0x11d4: add     x12, x9, #0x1bc
    +0x11d8: ld1     {v4.s}[1], [x12]
    +0x11dc: add     x13, x9, #0x1cc
    +0x11e0: add     x12, x9, #0x1e8
    +0x11e4: ld1     {v14.s}[2], [x11]
    +0x11e8: ld1     {v9.s}[2], [x13]
    +0x11ec: add     x11, x9, #0x1dc
    +0x11f0: ld1     {v19.s}[2], [x10]
    +0x11f4: add     x10, x9, #0x1f8
    +0x11f8: ld1     {v31.s}[3], [x12]
    +0x11fc: ld1     {v4.s}[2], [x11]
    +0x1200: add     x11, x9, #0x1f0
    +0x1204: ld1     {v14.s}[3], [x10]
    +0x1208: add     x10, x9, #0x1ec
    +0x120c: ld1     {v9.s}[3], [x10]
    +0x1210: ld1     {v19.s}[3], [x11]
    +0x1214: add     x10, x9, #0x1fc
    +0x1218: ld1     {v4.s}[3], [x10]
    +0x121c: add     x11, x9, #0x1e0
    +0x1220: tbl     v25.16b, {v28.16b-v31.16b}, v15.16b
    +0x1224: tbl     v11.16b, {v11.16b-v14.16b}, v15.16b
    +0x1228: ld1     {v23.s}[3], [x11]
    +0x122c: add     x10, x19, x8
    +0x1230: tbl     v6.16b, {v6.16b-v9.16b}, v15.16b
    +0x1234: tbl     v7.16b, {v16.16b-v19.16b}, v15.16b
    +0x1238: movi    v19.16b, #0x8
    +0x123c: tbl     v1.16b, {v1.16b-v4.16b}, v15.16b
    +0x1240: sub     v3.16b, v0.16b, v10.16b
    +0x1244: shl     v17.16b, v24.16b, #3
    +0x1248: tbl     v2.16b, {v20.16b-v23.16b}, v15.16b
    +0x124c: movi    v20.16b, #0x4
    +0x1250: sub     v16.16b, v0.16b, v25.16b
    +0x1254: shl     v4.16b, v11.16b, #2
    +0x1258: add     x8, x8, #0x30
    +0x125c: add     x9, x9, #0x200
    +0x1260: ushr    v18.16b, v3.16b, #1
    +0x1264: add     v6.16b, v6.16b, v6.16b
    +0x1268: shl     v7.16b, v7.16b, #4
    +0x126c: shl     v1.16b, v1.16b, #5
    +0x1270: shl     v3.16b, v3.16b, #7
    +0x1274: cmp     x8, #0x380
    +0x1278: sub     v4.16b, v19.16b, v4.16b
    +0x127c: movi    v19.16b, #0x10
    +0x1280: sub     v2.16b, v0.16b, v2.16b
    +0x1284: sub     v6.16b, v20.16b, v6.16b
    +0x1288: sub     v7.16b, v5.16b, v7.16b
    +0x128c: orr     v4.16b, v4.16b, v18.16b
    +0x1290: movi    v18.16b, #0x40
    +0x1294: sub     v17.16b, v19.16b, v17.16b
    +0x1298: ushr    v19.16b, v16.16b, #2
    +0x129c: shl     v16.16b, v16.16b, #6
    +0x12a0: orr     v3.16b, v7.16b, v3.16b
    +0x12a4: sub     v1.16b, v18.16b, v1.16b
    +0x12a8: orr     v2.16b, v17.16b, v2.16b
    +0x12ac: orr     v6.16b, v6.16b, v19.16b
    +0x12b0: orr     v19.16b, v4.16b, v1.16b
    +0x12b4: orr     v17.16b, v2.16b, v16.16b
    +0x12b8: orr     v18.16b, v6.16b, v3.16b
    +0x12bc: st3     {v17.16b-v19.16b}, [x10]
    +0x12c0: b.ne    <mldsa44_keypair_internal+0xebc>
    +0x12c4: str     xzr, [sp, #4384]
    +0x12c8: add     x8, sp, #0x1, lsl #12
    +0x12cc: add     x0, sp, #0x20
    +0x12d0: add     x8, x8, #0x120
    +0x12d4: add     x1, x22, #0x400
    +0x12d8: mov     w8, #0x3
    +0x12dc: add     x2, x22, #0x800
    +0x12e0: add     x3, x22, #0xc00
    +0x12e4: add     x4, x26, #0x20
    +0x12e8: mov     w5, wzr
    +0x12ec: mov     w6, #0x1
    +0x12f0: mov     w7, #0x2
    +0x12f4: strb    w8, [sp]
    +0x12f8: bl      <mldsa44_poly_uniform_eta_4x>
    +0x12fc: movi    v0.16b, #0x2
    +0x1300: movi    v5.16b, #0x20
    +0x1304: add     x8, sp, #0x20
    +0x1308: ldr     q15, [sp, #16]
    +0x130c: add     x8, x8, #0x100
    +0x1310: mov     w9, #0x80
    +0x1314: ldp     s16, s1, [x8, #-240]
    +0x1318: sub     x10, x8, #0xd0
    +0x131c: sub     x11, x8, #0xcc
    +0x1320: sub     x12, x8, #0xac
    +0x1324: sub     x15, x8, #0x90
    +0x1328: sub     x16, x8, #0x8c
    +0x132c: ldp     s20, s24, [x8, #-256]
    +0x1330: ld1     {v16.s}[1], [x10]
    +0x1334: ld1     {v1.s}[1], [x11]
    +0x1338: sub     x11, x8, #0xb0
    +0x133c: sub     x10, x8, #0xe0
    +0x1340: sub     x14, x8, #0xdc
    +0x1344: sub     x13, x8, #0xc0
    +0x1348: ld1     {v20.s}[1], [x10]
    +0x134c: sub     x10, x8, #0x50
    +0x1350: ld1     {v24.s}[1], [x14]
    +0x1354: ld1     {v16.s}[2], [x11]
    +0x1358: ld1     {v1.s}[2], [x12]
    +0x135c: sub     x11, x8, #0xa0
    +0x1360: sub     x12, x8, #0x60
    +0x1364: sub     x14, x8, #0x40
    +0x1368: add     x0, x8, #0xf4
    +0x136c: ld1     {v20.s}[2], [x13]
    +0x1370: sub     x13, x8, #0x30
    +0x1374: add     x17, x8, #0xa4
    +0x1378: ld1     {v16.s}[3], [x15]
    +0x137c: ld1     {v1.s}[3], [x16]
    +0x1380: sub     x15, x8, #0x4c
    +0x1384: ldp     s17, s2, [x8, #-112]
    +0x1388: sub     x16, x8, #0x2c
    +0x138c: ld1     {v20.s}[3], [x11]
    +0x1390: sub     x11, x8, #0xc
    +0x1394: sub     x18, x8, #0xd8
    +0x1398: ldp     s28, s6, [x8, #-248]
    +0x139c: ld1     {v17.s}[1], [x10]
    +0x13a0: ld1     {v2.s}[1], [x15]
    +0x13a4: sub     x15, x8, #0xbc
    +0x13a8: ld1     {v24.s}[2], [x15]
    +0x13ac: sub     x15, x8, #0x9c
    +0x13b0: sub     x10, x8, #0x20
    +0x13b4: ld1     {v28.s}[1], [x18]
    +0x13b8: ld1     {v17.s}[2], [x13]
    +0x13bc: ld1     {v2.s}[2], [x16]
    +0x13c0: sub     x16, x8, #0x10
    +0x13c4: ld1     {v24.s}[3], [x15]
    +0x13c8: sub     x13, x8, #0x5c
    +0x13cc: add     x15, x8, #0x54
    +0x13d0: ldp     s21, s25, [x8, #-128]
    +0x13d4: ld1     {v17.s}[3], [x16]
    +0x13d8: ld1     {v2.s}[3], [x11]
    +0x13dc: add     x11, x8, #0x30
    +0x13e0: ldp     s18, s3, [x8, #16]
    +0x13e4: add     x16, x8, #0x60
    +0x13e8: ld1     {v21.s}[1], [x12]
    +0x13ec: add     x12, x8, #0x34
    +0x13f0: ld1     {v25.s}[1], [x13]
    +0x13f4: add     x13, x8, #0x20
    +0x13f8: ld1     {v18.s}[1], [x11]
    +0x13fc: ld1     {v3.s}[1], [x12]
    +0x1400: sub     x11, x8, #0x3c
    +0x1404: ld1     {v21.s}[2], [x14]
    +0x1408: add     x14, x8, #0x50
    +0x140c: ld1     {v25.s}[2], [x11]
    +0x1410: sub     x11, x8, #0x1c
    +0x1414: add     x12, x8, #0x40
    +0x1418: ld1     {v18.s}[2], [x14]
    +0x141c: ld1     {v3.s}[2], [x15]
    +0x1420: add     x14, x8, #0x70
    +0x1424: ld1     {v21.s}[3], [x10]
    +0x1428: add     x10, x8, #0x74
    +0x142c: ld1     {v25.s}[3], [x11]
    +0x1430: ldp     s22, s26, [x8]
    +0x1434: add     x15, x8, #0xa0
    +0x1438: ld1     {v18.s}[3], [x14]
    +0x143c: ld1     {v3.s}[3], [x10]
    +0x1440: add     x10, x8, #0x24
    +0x1444: ldp     s19, s4, [x8, #144]
    +0x1448: add     x14, x8, #0xb4
    +0x144c: ld1     {v22.s}[1], [x13]
    +0x1450: ld1     {v26.s}[1], [x10]
    +0x1454: add     x10, x8, #0x44
    +0x1458: add     x13, x8, #0x64
    +0x145c: add     x11, x8, #0xc0
    +0x1460: ld1     {v4.s}[1], [x14]
    +0x1464: add     x14, x8, #0xd4
    +0x1468: ld1     {v22.s}[2], [x12]
    +0x146c: ld1     {v26.s}[2], [x10]
    +0x1470: add     x12, x8, #0xc4
    +0x1474: add     x10, x8, #0xe4
    +0x1478: ld1     {v4.s}[2], [x14]
    +0x147c: sub     x14, x8, #0xb8
    +0x1480: ld1     {v22.s}[3], [x16]
    +0x1484: ld1     {v26.s}[3], [x13]
    +0x1488: sub     x16, x8, #0xc8
    +0x148c: ldp     s23, s27, [x8, #128]
    +0x1490: ld1     {v28.s}[2], [x14]
    +0x1494: ld1     {v4.s}[3], [x0]
    +0x1498: sub     x14, x8, #0xc4
    +0x149c: sub     x13, x8, #0x98
    +0x14a0: ld1     {v23.s}[1], [x15]
    +0x14a4: ld1     {v27.s}[1], [x17]
    +0x14a8: sub     x15, x8, #0xd4
    +0x14ac: tbl     v10.16b, {v1.16b-v4.16b}, v15.16b
    +0x14b0: ldp     s11, s1, [x8, #-232]
    +0x14b4: ld1     {v6.s}[1], [x15]
    +0x14b8: ld1     {v28.s}[3], [x13]
    +0x14bc: sub     x13, x8, #0xa4
    +0x14c0: ld1     {v27.s}[2], [x12]
    +0x14c4: sub     x12, x8, #0xb4
    +0x14c8: ld1     {v23.s}[2], [x11]
    +0x14cc: ld1     {v11.s}[1], [x16]
    +0x14d0: ld1     {v1.s}[1], [x14]
    +0x14d4: sub     x11, x8, #0x58
    +0x14d8: ld1     {v6.s}[2], [x12]
    +0x14dc: sub     x12, x8, #0xa8
    +0x14e0: sub     x14, x8, #0x38
    +0x14e4: ld1     {v27.s}[3], [x10]
    +0x14e8: sub     x10, x8, #0x14
    +0x14ec: add     x15, x8, #0x78
    +0x14f0: ld1     {v11.s}[2], [x12]
    +0x14f4: sub     x12, x8, #0x94
    +0x14f8: ld1     {v1.s}[2], [x13]
    +0x14fc: ld1     {v6.s}[3], [x12]
    +0x1500: sub     x12, x8, #0x88
    +0x1504: sub     x13, x8, #0x44
    +0x1508: ldp     s29, s7, [x8, #-120]
    +0x150c: tbl     v24.16b, {v24.16b-v27.16b}, v15.16b
    +0x1510: ld1     {v11.s}[3], [x12]
    +0x1514: sub     x12, x8, #0x84
    +0x1518: ld1     {v1.s}[3], [x12]
    +0x151c: sub     x12, x8, #0x34
    +0x1520: ld1     {v29.s}[1], [x11]
    +0x1524: ldp     s12, s2, [x8, #-104]
    +0x1528: sub     x11, x8, #0x54
    +0x152c: ld1     {v7.s}[1], [x11]
    +0x1530: sub     x11, x8, #0x48
    +0x1534: ld1     {v29.s}[2], [x14]
    +0x1538: ld1     {v12.s}[1], [x11]
    +0x153c: ld1     {v2.s}[1], [x13]
    +0x1540: sub     x11, x8, #0x18
    +0x1544: add     x13, x8, #0x4c
    +0x1548: add     x14, x8, #0x58
    +0x154c: ld1     {v7.s}[2], [x12]
    +0x1550: sub     x12, x8, #0x28
    +0x1554: ld1     {v29.s}[3], [x11]
    +0x1558: ld1     {v12.s}[2], [x12]
    +0x155c: sub     x11, x8, #0x24
    +0x1560: ld1     {v2.s}[2], [x11]
    +0x1564: add     x11, x8, #0x28
    +0x1568: add     x12, x8, #0x38
    +0x156c: ld1     {v7.s}[3], [x10]
    +0x1570: sub     x10, x8, #0x8
    +0x1574: ld1     {v12.s}[3], [x10]
    +0x1578: sub     x10, x8, #0x4
    +0x157c: ldp     s30, s8, [x8, #8]
    +0x1580: ld1     {v2.s}[3], [x10]
    +0x1584: ldp     s13, s3, [x8, #24]
    +0x1588: add     x10, x8, #0x48
    +0x158c: ld1     {v30.s}[1], [x11]
    +0x1590: add     x11, x8, #0x2c
    +0x1594: ld1     {v8.s}[1], [x11]
    +0x1598: ld1     {v13.s}[1], [x12]
    +0x159c: add     x12, x8, #0x3c
    +0x15a0: ld1     {v3.s}[1], [x12]
    +0x15a4: add     x11, x8, #0x68
    +0x15a8: add     x12, x8, #0xc8
    +0x15ac: ld1     {v30.s}[2], [x10]
    +0x15b0: add     x10, x8, #0xa8
    +0x15b4: ld1     {v8.s}[2], [x13]
    +0x15b8: add     x13, x8, #0x5c
    +0x15bc: ld1     {v13.s}[2], [x14]
    +0x15c0: ld1     {v3.s}[2], [x13]
    +0x15c4: add     x14, x8, #0x6c
    +0x15c8: add     x13, x8, #0xb8
    +0x15cc: ld1     {v30.s}[3], [x11]
    +0x15d0: add     x11, x8, #0x7c
    +0x15d4: ld1     {v13.s}[3], [x15]
    +0x15d8: ld1     {v8.s}[3], [x14]
    +0x15dc: ld1     {v3.s}[3], [x11]
    +0x15e0: ldp     s31, s9, [x8, #136]
    +0x15e4: ldp     s14, s4, [x8, #152]
    +0x15e8: add     x11, x8, #0xac
    +0x15ec: ld1     {v31.s}[1], [x10]
    +0x15f0: add     x10, x8, #0xb0
    +0x15f4: ld1     {v9.s}[1], [x11]
    +0x15f8: ld1     {v14.s}[1], [x13]
    +0x15fc: ld1     {v19.s}[1], [x10]
    +0x1600: add     x10, x8, #0xd8
    +0x1604: add     x11, x8, #0xbc
    +0x1608: add     x13, x8, #0xcc
    +0x160c: ld1     {v4.s}[1], [x11]
    +0x1610: ld1     {v9.s}[2], [x13]
    +0x1614: add     x11, x8, #0xdc
    +0x1618: ld1     {v14.s}[2], [x10]
    +0x161c: add     x10, x8, #0xd0
    +0x1620: ld1     {v31.s}[2], [x12]
    +0x1624: ld1     {v19.s}[2], [x10]
    +0x1628: add     x10, x8, #0xf8
    +0x162c: add     x12, x8, #0xe8
    +0x1630: ld1     {v4.s}[2], [x11]
    +0x1634: add     x11, x8, #0xf0
    +0x1638: ld1     {v14.s}[3], [x10]
    +0x163c: add     x10, x8, #0xec
    +0x1640: ld1     {v31.s}[3], [x12]
    +0x1644: ld1     {v9.s}[3], [x10]
    +0x1648: ld1     {v19.s}[3], [x11]
    +0x164c: add     x10, x8, #0xfc
    +0x1650: ld1     {v4.s}[3], [x10]
    +0x1654: add     x11, x8, #0xe0
    +0x1658: add     x10, x19, x9
    +0x165c: tbl     v11.16b, {v11.16b-v14.16b}, v15.16b
    +0x1660: ld1     {v23.s}[3], [x11]
    +0x1664: tbl     v25.16b, {v28.16b-v31.16b}, v15.16b
    +0x1668: tbl     v6.16b, {v6.16b-v9.16b}, v15.16b
    +0x166c: tbl     v7.16b, {v16.16b-v19.16b}, v15.16b
    +0x1670: movi    v19.16b, #0x8
    +0x1674: tbl     v1.16b, {v1.16b-v4.16b}, v15.16b
    +0x1678: sub     v3.16b, v0.16b, v10.16b
    +0x167c: shl     v17.16b, v24.16b, #3
    +0x1680: tbl     v2.16b, {v20.16b-v23.16b}, v15.16b
    +0x1684: movi    v20.16b, #0x4
    +0x1688: add     x9, x9, #0x30
    +0x168c: shl     v4.16b, v11.16b, #2
    +0x1690: sub     v16.16b, v0.16b, v25.16b
    +0x1694: cmp     x9, #0xe0
    +0x1698: ushr    v18.16b, v3.16b, #1
    +0x169c: add     v6.16b, v6.16b, v6.16b
    +0x16a0: shl     v7.16b, v7.16b, #4
    +0x16a4: shl     v1.16b, v1.16b, #5
    +0x16a8: shl     v3.16b, v3.16b, #7
    +0x16ac: add     x8, x8, #0x200
    +0x16b0: sub     v4.16b, v19.16b, v4.16b
    +0x16b4: movi    v19.16b, #0x10
    +0x16b8: sub     v2.16b, v0.16b, v2.16b
    +0x16bc: sub     v6.16b, v20.16b, v6.16b
    +0x16c0: sub     v7.16b, v5.16b, v7.16b
    +0x16c4: orr     v4.16b, v4.16b, v18.16b
    +0x16c8: movi    v18.16b, #0x40
    +0x16cc: sub     v17.16b, v19.16b, v17.16b
    +0x16d0: ushr    v19.16b, v16.16b, #2
    +0x16d4: shl     v16.16b, v16.16b, #6
    +0x16d8: orr     v3.16b, v7.16b, v3.16b
    +0x16dc: sub     v1.16b, v18.16b, v1.16b
    +0x16e0: orr     v2.16b, v17.16b, v2.16b
    +0x16e4: orr     v6.16b, v6.16b, v19.16b
    +0x16e8: orr     v19.16b, v4.16b, v1.16b
    +0x16ec: orr     v17.16b, v2.16b, v16.16b
    +0x16f0: orr     v18.16b, v6.16b, v3.16b
    +0x16f4: st3     {v17.16b-v19.16b}, [x10]
    +0x16f8: b.ne    <mldsa44_keypair_internal+0x1314>
    +0x16fc: str     xzr, [sp, #4384]
    +0x1700: add     x8, sp, #0x1, lsl #12
    +0x1704: movi    v0.16b, #0x2
    +0x1708: movi    v5.16b, #0x20
    +0x170c: add     x8, x8, #0x120
    +0x1710: ldr     q15, [sp, #16]
    +0x1714: mov     w8, #0xe0
    +0x1718: ldp     s16, s1, [x25, #16]
    +0x171c: add     x9, x25, #0x30
    +0x1720: add     x10, x25, #0x34
    +0x1724: add     x12, x25, #0x50
    +0x1728: add     x13, x25, #0x54
    +0x172c: ldp     s20, s24, [x25]
    +0x1730: add     x14, x25, #0x70
    +0x1734: ld1     {v16.s}[1], [x9]
    +0x1738: ld1     {v1.s}[1], [x10]
    +0x173c: add     x9, x25, #0x20
    +0x1740: add     x15, x25, #0x74
    +0x1744: add     x10, x25, #0x40
    +0x1748: add     x11, x25, #0x60
    +0x174c: ld1     {v20.s}[1], [x9]
    +0x1750: add     x9, x25, #0x44
    +0x1754: add     x17, x25, #0xd4
    +0x1758: ld1     {v16.s}[2], [x12]
    +0x175c: ld1     {v1.s}[2], [x13]
    +0x1760: add     x12, x25, #0x24
    +0x1764: ld1     {v24.s}[1], [x12]
    +0x1768: add     x12, x25, #0xb4
    +0x176c: add     x0, x25, #0xf4
    +0x1770: ld1     {v20.s}[2], [x10]
    +0x1774: add     x18, x25, #0xc4
    +0x1778: add     x13, x25, #0xa0
    +0x177c: ld1     {v16.s}[3], [x14]
    +0x1780: ld1     {v1.s}[3], [x15]
    +0x1784: add     x16, x25, #0xc0
    +0x1788: ldp     s17, s2, [x25, #144]
    +0x178c: ld1     {v24.s}[2], [x9]
    +0x1790: add     x9, x25, #0x64
    +0x1794: ld1     {v20.s}[3], [x11]
    +0x1798: add     x14, x25, #0xe0
    +0x179c: ldp     s28, s6, [x25, #8]
    +0x17a0: add     x15, x25, #0x120
    +0x17a4: ld1     {v2.s}[1], [x12]
    +0x17a8: ld1     {v24.s}[3], [x9]
    +0x17ac: add     x1, x25, #0x124
    +0x17b0: ldp     s21, s25, [x25, #128]
    +0x17b4: add     x12, x25, #0x140
    +0x17b8: add     x10, x25, #0x160
    +0x17bc: add     x11, x25, #0x1a0
    +0x17c0: add     x9, x25, #0x1c0
    +0x17c4: ld1     {v2.s}[2], [x17]
    +0x17c8: add     x17, x25, #0xa4
    +0x17cc: ld1     {v25.s}[1], [x17]
    +0x17d0: ld1     {v21.s}[1], [x13]
    +0x17d4: add     x17, x25, #0xe4
    +0x17d8: add     x13, x25, #0x164
    +0x17dc: ld1     {v2.s}[3], [x0]
    +0x17e0: add     x0, x25, #0x144
    +0x17e4: ldr     s3, [x25, #276]
    +0x17e8: ld1     {v25.s}[2], [x18]
    +0x17ec: add     x18, x25, #0x134
    +0x17f0: ld1     {v21.s}[2], [x16]
    +0x17f4: add     x16, x25, #0x48
    +0x17f8: ld1     {v3.s}[1], [x18]
    +0x17fc: add     x18, x25, #0x28
    +0x1800: ld1     {v28.s}[1], [x18]
    +0x1804: add     x18, x25, #0x154
    +0x1808: ld1     {v25.s}[3], [x17]
    +0x180c: ld1     {v21.s}[3], [x14]
    +0x1810: add     x14, x25, #0x174
    +0x1814: ldr     s26, [x25, #260]
    +0x1818: ld1     {v3.s}[2], [x18]
    +0x181c: add     x18, x25, #0x2c
    +0x1820: ldr     s22, [x25, #256]
    +0x1824: ld1     {v6.s}[1], [x18]
    +0x1828: ld1     {v28.s}[2], [x16]
    +0x182c: add     x16, x25, #0x4c
    +0x1830: add     x17, x25, #0x68
    +0x1834: ld1     {v26.s}[1], [x1]
    +0x1838: ld1     {v22.s}[1], [x15]
    +0x183c: ld1     {v3.s}[3], [x14]
    +0x1840: add     x14, x25, #0x6c
    +0x1844: add     x15, x25, #0x1b4
    +0x1848: ld1     {v6.s}[2], [x16]
    +0x184c: ldr     s4, [x25, #404]
    +0x1850: ld1     {v28.s}[3], [x17]
    +0x1854: ld1     {v26.s}[2], [x0]
    +0x1858: ld1     {v22.s}[2], [x12]
    +0x185c: add     x12, x25, #0x1d4
    +0x1860: ld1     {v4.s}[1], [x15]
    +0x1864: add     x15, x25, #0xa8
    +0x1868: ld1     {v6.s}[3], [x14]
    +0x186c: add     x14, x25, #0x1a4
    +0x1870: ldp     s29, s7, [x25, #136]
    +0x1874: ld1     {v26.s}[3], [x13]
    +0x1878: ld1     {v4.s}[2], [x12]
    +0x187c: add     x12, x25, #0xc8
    +0x1880: ld1     {v22.s}[3], [x10]
    +0x1884: add     x10, x25, #0x1f4
    +0x1888: ldr     s27, [x25, #388]
    +0x188c: ldr     s23, [x25, #384]
    +0x1890: ld1     {v29.s}[1], [x15]
    +0x1894: add     x13, x25, #0xe8
    +0x1898: ld1     {v4.s}[3], [x10]
    +0x189c: ld1     {v27.s}[1], [x14]
    +0x18a0: ld1     {v23.s}[1], [x11]
    +0x18a4: add     x10, x25, #0x128
    +0x18a8: add     x11, x25, #0x38
    +0x18ac: ld1     {v29.s}[2], [x12]
    +0x18b0: add     x12, x25, #0x1c4
    +0x18b4: tbl     v10.16b, {v1.16b-v4.16b}, v15.16b
    +0x18b8: ldp     s11, s1, [x25, #24]
    +0x18bc: ld1     {v27.s}[2], [x12]
    +0x18c0: ld1     {v23.s}[2], [x9]
    +0x18c4: add     x9, x25, #0x1e4
    +0x18c8: ld1     {v29.s}[3], [x13]
    +0x18cc: add     x13, x25, #0x78
    +0x18d0: add     x12, x25, #0x1a8
    +0x18d4: ldr     s30, [x25, #264]
    +0x18d8: ld1     {v11.s}[1], [x11]
    +0x18dc: add     x11, x25, #0x168
    +0x18e0: ld1     {v27.s}[3], [x9]
    +0x18e4: add     x9, x25, #0x58
    +0x18e8: ld1     {v30.s}[1], [x10]
    +0x18ec: add     x10, x25, #0x3c
    +0x18f0: ld1     {v1.s}[1], [x10]
    +0x18f4: ld1     {v11.s}[2], [x9]
    +0x18f8: add     x9, x25, #0x5c
    +0x18fc: add     x10, x25, #0x148
    +0x1900: tbl     v24.16b, {v24.16b-v27.16b}, v15.16b
    +0x1904: ld1     {v30.s}[2], [x10]
    +0x1908: add     x10, x25, #0xac
    +0x190c: ld1     {v1.s}[2], [x9]
    +0x1910: ld1     {v7.s}[1], [x10]
    +0x1914: add     x10, x25, #0x7c
    +0x1918: ld1     {v11.s}[3], [x13]
    +0x191c: add     x13, x25, #0xb8
    +0x1920: add     x9, x25, #0x1c8
    +0x1924: ld1     {v30.s}[3], [x11]
    +0x1928: add     x11, x25, #0xcc
    +0x192c: ld1     {v1.s}[3], [x10]
    +0x1930: ld1     {v7.s}[2], [x11]
    +0x1934: add     x11, x25, #0xb0
    +0x1938: ldp     s12, s2, [x25, #152]
    +0x193c: ld1     {v17.s}[1], [x11]
    +0x1940: add     x11, x25, #0xd8
    +0x1944: add     x10, x25, #0xec
    +0x1948: ldr     s31, [x25, #392]
    +0x194c: ld1     {v7.s}[3], [x10]
    +0x1950: add     x10, x25, #0xd0
    +0x1954: ld1     {v12.s}[1], [x13]
    +0x1958: add     x13, x25, #0xbc
    +0x195c: ld1     {v17.s}[2], [x10]
    +0x1960: ld1     {v2.s}[1], [x13]
    +0x1964: add     x10, x25, #0xf8
    +0x1968: ldr     s8, [x25, #268]
    +0x196c: ld1     {v31.s}[1], [x12]
    +0x1970: add     x12, x25, #0x12c
    +0x1974: add     x13, x25, #0x15c
    +0x1978: ld1     {v12.s}[2], [x11]
    +0x197c: add     x11, x25, #0xdc
    +0x1980: ld1     {v8.s}[1], [x12]
    +0x1984: ld1     {v2.s}[2], [x11]
    +0x1988: add     x11, x25, #0xfc
    +0x198c: add     x12, x25, #0x13c
    +0x1990: ld1     {v31.s}[2], [x9]
    +0x1994: add     x9, x25, #0x1d0
    +0x1998: ld1     {v12.s}[3], [x10]
    +0x199c: add     x10, x25, #0xf0
    +0x19a0: ldr     s13, [x25, #280]
    +0x19a4: ld1     {v17.s}[3], [x10]
    +0x19a8: add     x10, x25, #0x138
    +0x19ac: ldr     s18, [x25, #272]
    +0x19b0: ld1     {v2.s}[3], [x11]
    +0x19b4: add     x11, x25, #0x130
    +0x19b8: ld1     {v13.s}[1], [x10]
    +0x19bc: ldr     s3, [x25, #284]
    +0x19c0: add     x10, x25, #0x14c
    +0x19c4: ld1     {v18.s}[1], [x11]
    +0x19c8: add     x11, x25, #0x158
    +0x19cc: ld1     {v8.s}[2], [x10]
    +0x19d0: ld1     {v3.s}[1], [x12]
    +0x19d4: add     x12, x25, #0x150
    +0x19d8: add     x10, x25, #0x16c
    +0x19dc: ld1     {v13.s}[2], [x11]
    +0x19e0: add     x11, x25, #0x1ac
    +0x19e4: ld1     {v18.s}[2], [x12]
    +0x19e8: add     x12, x25, #0x178
    +0x19ec: ld1     {v8.s}[3], [x10]
    +0x19f0: ld1     {v3.s}[2], [x13]
    +0x19f4: add     x10, x25, #0x170
    +0x19f8: ldr     s9, [x25, #396]
    +0x19fc: ld1     {v13.s}[3], [x12]
    +0x1a00: add     x12, x25, #0x17c
    +0x1a04: ldr     s14, [x25, #408]
    +0x1a08: ld1     {v18.s}[3], [x10]
    +0x1a0c: add     x10, x25, #0x1b8
    +0x1a10: ldr     s19, [x25, #400]
    +0x1a14: ld1     {v3.s}[3], [x12]
    +0x1a18: ld1     {v9.s}[1], [x11]
    +0x1a1c: ld1     {v14.s}[1], [x10]
    +0x1a20: add     x10, x25, #0x1b0
    +0x1a24: ldr     s4, [x25, #412]
    +0x1a28: ld1     {v19.s}[1], [x10]
    +0x1a2c: add     x10, x25, #0x1d8
    +0x1a30: add     x11, x25, #0x1bc
    +0x1a34: ld1     {v4.s}[1], [x11]
    +0x1a38: add     x12, x25, #0x1cc
    +0x1a3c: add     x11, x25, #0x1e8
    +0x1a40: ld1     {v14.s}[2], [x10]
    +0x1a44: ld1     {v9.s}[2], [x12]
    +0x1a48: add     x10, x25, #0x1dc
    +0x1a4c: ld1     {v19.s}[2], [x9]
    +0x1a50: add     x9, x25, #0x1f8
    +0x1a54: ld1     {v31.s}[3], [x11]
    +0x1a58: ld1     {v4.s}[2], [x10]
    +0x1a5c: add     x10, x25, #0x1f0
    +0x1a60: ld1     {v14.s}[3], [x9]
    +0x1a64: add     x9, x25, #0x1ec
    +0x1a68: ld1     {v9.s}[3], [x9]
    +0x1a6c: ld1     {v19.s}[3], [x10]
    +0x1a70: add     x9, x25, #0x1fc
    +0x1a74: ld1     {v4.s}[3], [x9]
    +0x1a78: add     x10, x25, #0x1e0
    +0x1a7c: tbl     v25.16b, {v28.16b-v31.16b}, v15.16b
    +0x1a80: tbl     v11.16b, {v11.16b-v14.16b}, v15.16b
    +0x1a84: ld1     {v23.s}[3], [x10]
    +0x1a88: add     x9, x19, x8
    +0x1a8c: tbl     v6.16b, {v6.16b-v9.16b}, v15.16b
    +0x1a90: tbl     v7.16b, {v16.16b-v19.16b}, v15.16b
    +0x1a94: movi    v19.16b, #0x8
    +0x1a98: tbl     v1.16b, {v1.16b-v4.16b}, v15.16b
    +0x1a9c: sub     v3.16b, v0.16b, v10.16b
    +0x1aa0: shl     v17.16b, v24.16b, #3
    +0x1aa4: tbl     v2.16b, {v20.16b-v23.16b}, v15.16b
    +0x1aa8: movi    v20.16b, #0x4
    +0x1aac: sub     v16.16b, v0.16b, v25.16b
    +0x1ab0: shl     v4.16b, v11.16b, #2
    +0x1ab4: add     x8, x8, #0x30
    +0x1ab8: add     x25, x25, #0x200
    +0x1abc: ushr    v18.16b, v3.16b, #1
    +0x1ac0: add     v6.16b, v6.16b, v6.16b
    +0x1ac4: shl     v7.16b, v7.16b, #4
    +0x1ac8: shl     v1.16b, v1.16b, #5
    +0x1acc: shl     v3.16b, v3.16b, #7
    +0x1ad0: cmp     x8, #0x140
    +0x1ad4: sub     v4.16b, v19.16b, v4.16b
    +0x1ad8: movi    v19.16b, #0x10
    +0x1adc: sub     v2.16b, v0.16b, v2.16b
    +0x1ae0: sub     v6.16b, v20.16b, v6.16b
    +0x1ae4: sub     v7.16b, v5.16b, v7.16b
    +0x1ae8: orr     v4.16b, v4.16b, v18.16b
    +0x1aec: movi    v18.16b, #0x40
    +0x1af0: sub     v17.16b, v19.16b, v17.16b
    +0x1af4: ushr    v19.16b, v16.16b, #2
    +0x1af8: shl     v16.16b, v16.16b, #6
    +0x1afc: orr     v3.16b, v7.16b, v3.16b
    +0x1b00: sub     v1.16b, v18.16b, v1.16b
    +0x1b04: orr     v2.16b, v17.16b, v2.16b
    +0x1b08: orr     v6.16b, v6.16b, v19.16b
    +0x1b0c: orr     v19.16b, v4.16b, v1.16b
    +0x1b10: orr     v17.16b, v2.16b, v16.16b
    +0x1b14: orr     v18.16b, v6.16b, v3.16b
    +0x1b18: st3     {v17.16b-v19.16b}, [x9]
    +0x1b1c: b.ne    <mldsa44_keypair_internal+0x1718>
    +0x1b20: str     xzr, [sp, #4384]
    +0x1b24: add     x8, sp, #0x1, lsl #12
    +0x1b28: movi    v0.16b, #0x2
    +0x1b2c: movi    v5.16b, #0x20
    +0x1b30: add     x8, x8, #0x120
    +0x1b34: ldr     q15, [sp, #16]
    +0x1b38: mov     w8, #0x140
    +0x1b3c: ldp     s16, s1, [x24, #16]
    +0x1b40: add     x9, x24, #0x30
    +0x1b44: add     x10, x24, #0x34
    +0x1b48: add     x12, x24, #0x50
    +0x1b4c: add     x13, x24, #0x54
    +0x1b50: ldp     s20, s24, [x24]
    +0x1b54: add     x14, x24, #0x70
    +0x1b58: ld1     {v16.s}[1], [x9]
    +0x1b5c: ld1     {v1.s}[1], [x10]
    +0x1b60: add     x9, x24, #0x20
    +0x1b64: add     x15, x24, #0x74
    +0x1b68: add     x10, x24, #0x40
    +0x1b6c: add     x11, x24, #0x60
    +0x1b70: ld1     {v20.s}[1], [x9]
    +0x1b74: add     x9, x24, #0x44
    +0x1b78: add     x17, x24, #0xd4
    +0x1b7c: ld1     {v16.s}[2], [x12]
    +0x1b80: ld1     {v1.s}[2], [x13]
    +0x1b84: add     x12, x24, #0x24
    +0x1b88: ld1     {v24.s}[1], [x12]
    +0x1b8c: add     x12, x24, #0xb4
    +0x1b90: add     x0, x24, #0xf4
    +0x1b94: ld1     {v20.s}[2], [x10]
    +0x1b98: add     x18, x24, #0xc4
    +0x1b9c: add     x13, x24, #0xa0
    +0x1ba0: ld1     {v16.s}[3], [x14]
    +0x1ba4: ld1     {v1.s}[3], [x15]
    +0x1ba8: add     x16, x24, #0xc0
    +0x1bac: ldp     s17, s2, [x24, #144]
    +0x1bb0: ld1     {v24.s}[2], [x9]
    +0x1bb4: add     x9, x24, #0x64
    +0x1bb8: ld1     {v20.s}[3], [x11]
    +0x1bbc: add     x14, x24, #0xe0
    +0x1bc0: ldp     s28, s6, [x24, #8]
    +0x1bc4: add     x15, x24, #0x120
    +0x1bc8: ld1     {v2.s}[1], [x12]
    +0x1bcc: ld1     {v24.s}[3], [x9]
    +0x1bd0: add     x1, x24, #0x124
    +0x1bd4: ldp     s21, s25, [x24, #128]
    +0x1bd8: add     x12, x24, #0x140
    +0x1bdc: add     x10, x24, #0x160
    +0x1be0: add     x11, x24, #0x1a0
    +0x1be4: add     x9, x24, #0x1c0
    +0x1be8: ld1     {v2.s}[2], [x17]
    +0x1bec: add     x17, x24, #0xa4
    +0x1bf0: ld1     {v25.s}[1], [x17]
    +0x1bf4: ld1     {v21.s}[1], [x13]
    +0x1bf8: add     x17, x24, #0xe4
    +0x1bfc: add     x13, x24, #0x164
    +0x1c00: ld1     {v2.s}[3], [x0]
    +0x1c04: add     x0, x24, #0x144
    +0x1c08: ldr     s3, [x24, #276]
    +0x1c0c: ld1     {v25.s}[2], [x18]
    +0x1c10: add     x18, x24, #0x134
    +0x1c14: ld1     {v21.s}[2], [x16]
    +0x1c18: add     x16, x24, #0x48
    +0x1c1c: ld1     {v3.s}[1], [x18]
    +0x1c20: add     x18, x24, #0x28
    +0x1c24: ld1     {v28.s}[1], [x18]
    +0x1c28: add     x18, x24, #0x154
    +0x1c2c: ld1     {v25.s}[3], [x17]
    +0x1c30: ld1     {v21.s}[3], [x14]
    +0x1c34: add     x14, x24, #0x174
    +0x1c38: ldr     s26, [x24, #260]
    +0x1c3c: ld1     {v3.s}[2], [x18]
    +0x1c40: add     x18, x24, #0x2c
    +0x1c44: ldr     s22, [x24, #256]
    +0x1c48: ld1     {v6.s}[1], [x18]
    +0x1c4c: ld1     {v28.s}[2], [x16]
    +0x1c50: add     x16, x24, #0x4c
    +0x1c54: add     x17, x24, #0x68
    +0x1c58: ld1     {v26.s}[1], [x1]
    +0x1c5c: ld1     {v22.s}[1], [x15]
    +0x1c60: ld1     {v3.s}[3], [x14]
    +0x1c64: add     x14, x24, #0x6c
    +0x1c68: add     x15, x24, #0x1b4
    +0x1c6c: ld1     {v6.s}[2], [x16]
    +0x1c70: ldr     s4, [x24, #404]
    +0x1c74: ld1     {v28.s}[3], [x17]
    +0x1c78: ld1     {v26.s}[2], [x0]
    +0x1c7c: ld1     {v22.s}[2], [x12]
    +0x1c80: add     x12, x24, #0x1d4
    +0x1c84: ld1     {v4.s}[1], [x15]
    +0x1c88: add     x15, x24, #0xa8
    +0x1c8c: ld1     {v6.s}[3], [x14]
    +0x1c90: add     x14, x24, #0x1a4
    +0x1c94: ldp     s29, s7, [x24, #136]
    +0x1c98: ld1     {v26.s}[3], [x13]
    +0x1c9c: ld1     {v4.s}[2], [x12]
    +0x1ca0: add     x12, x24, #0xc8
    +0x1ca4: ld1     {v22.s}[3], [x10]
    +0x1ca8: add     x10, x24, #0x1f4
    +0x1cac: ldr     s27, [x24, #388]
    +0x1cb0: ldr     s23, [x24, #384]
    +0x1cb4: ld1     {v29.s}[1], [x15]
    +0x1cb8: add     x13, x24, #0xe8
    +0x1cbc: ld1     {v4.s}[3], [x10]
    +0x1cc0: ld1     {v27.s}[1], [x14]
    +0x1cc4: ld1     {v23.s}[1], [x11]
    +0x1cc8: add     x10, x24, #0x128
    +0x1ccc: add     x11, x24, #0x38
    +0x1cd0: ld1     {v29.s}[2], [x12]
    +0x1cd4: add     x12, x24, #0x1c4
    +0x1cd8: tbl     v10.16b, {v1.16b-v4.16b}, v15.16b
    +0x1cdc: ldp     s11, s1, [x24, #24]
    +0x1ce0: ld1     {v27.s}[2], [x12]
    +0x1ce4: ld1     {v23.s}[2], [x9]
    +0x1ce8: add     x9, x24, #0x1e4
    +0x1cec: ld1     {v29.s}[3], [x13]
    +0x1cf0: add     x13, x24, #0x78
    +0x1cf4: add     x12, x24, #0x1a8
    +0x1cf8: ldr     s30, [x24, #264]
    +0x1cfc: ld1     {v11.s}[1], [x11]
    +0x1d00: add     x11, x24, #0x168
    +0x1d04: ld1     {v27.s}[3], [x9]
    +0x1d08: add     x9, x24, #0x58
    +0x1d0c: ld1     {v30.s}[1], [x10]
    +0x1d10: add     x10, x24, #0x3c
    +0x1d14: ld1     {v1.s}[1], [x10]
    +0x1d18: ld1     {v11.s}[2], [x9]
    +0x1d1c: add     x9, x24, #0x5c
    +0x1d20: add     x10, x24, #0x148
    +0x1d24: tbl     v24.16b, {v24.16b-v27.16b}, v15.16b
    +0x1d28: ld1     {v30.s}[2], [x10]
    +0x1d2c: add     x10, x24, #0xac
    +0x1d30: ld1     {v1.s}[2], [x9]
    +0x1d34: ld1     {v7.s}[1], [x10]
    +0x1d38: add     x10, x24, #0x7c
    +0x1d3c: ld1     {v11.s}[3], [x13]
    +0x1d40: add     x13, x24, #0xb8
    +0x1d44: add     x9, x24, #0x1c8
    +0x1d48: ld1     {v30.s}[3], [x11]
    +0x1d4c: add     x11, x24, #0xcc
    +0x1d50: ld1     {v1.s}[3], [x10]
    +0x1d54: ld1     {v7.s}[2], [x11]
    +0x1d58: add     x11, x24, #0xb0
    +0x1d5c: ldp     s12, s2, [x24, #152]
    +0x1d60: ld1     {v17.s}[1], [x11]
    +0x1d64: add     x11, x24, #0xd8
    +0x1d68: add     x10, x24, #0xec
    +0x1d6c: ldr     s31, [x24, #392]
    +0x1d70: ld1     {v7.s}[3], [x10]
    +0x1d74: add     x10, x24, #0xd0
    +0x1d78: ld1     {v12.s}[1], [x13]
    +0x1d7c: add     x13, x24, #0xbc
    +0x1d80: ld1     {v17.s}[2], [x10]
    +0x1d84: ld1     {v2.s}[1], [x13]
    +0x1d88: add     x10, x24, #0xf8
    +0x1d8c: ldr     s8, [x24, #268]
    +0x1d90: ld1     {v31.s}[1], [x12]
    +0x1d94: add     x12, x24, #0x12c
    +0x1d98: add     x13, x24, #0x15c
    +0x1d9c: ld1     {v12.s}[2], [x11]
    +0x1da0: add     x11, x24, #0xdc
    +0x1da4: ld1     {v8.s}[1], [x12]
    +0x1da8: ld1     {v2.s}[2], [x11]
    +0x1dac: add     x11, x24, #0xfc
    +0x1db0: add     x12, x24, #0x13c
    +0x1db4: ld1     {v31.s}[2], [x9]
    +0x1db8: add     x9, x24, #0x1d0
    +0x1dbc: ld1     {v12.s}[3], [x10]
    +0x1dc0: add     x10, x24, #0xf0
    +0x1dc4: ldr     s13, [x24, #280]
    +0x1dc8: ld1     {v17.s}[3], [x10]
    +0x1dcc: add     x10, x24, #0x138
    +0x1dd0: ldr     s18, [x24, #272]
    +0x1dd4: ld1     {v2.s}[3], [x11]
    +0x1dd8: add     x11, x24, #0x130
    +0x1ddc: ld1     {v13.s}[1], [x10]
    +0x1de0: ldr     s3, [x24, #284]
    +0x1de4: add     x10, x24, #0x14c
    +0x1de8: ld1     {v18.s}[1], [x11]
    +0x1dec: add     x11, x24, #0x158
    +0x1df0: ld1     {v8.s}[2], [x10]
    +0x1df4: ld1     {v3.s}[1], [x12]
    +0x1df8: add     x12, x24, #0x150
    +0x1dfc: add     x10, x24, #0x16c
    +0x1e00: ld1     {v13.s}[2], [x11]
    +0x1e04: add     x11, x24, #0x1ac
    +0x1e08: ld1     {v18.s}[2], [x12]
    +0x1e0c: add     x12, x24, #0x178
    +0x1e10: ld1     {v8.s}[3], [x10]
    +0x1e14: ld1     {v3.s}[2], [x13]
    +0x1e18: add     x10, x24, #0x170
    +0x1e1c: ldr     s9, [x24, #396]
    +0x1e20: ld1     {v13.s}[3], [x12]
    +0x1e24: add     x12, x24, #0x17c
    +0x1e28: ldr     s14, [x24, #408]
    +0x1e2c: ld1     {v18.s}[3], [x10]
    +0x1e30: add     x10, x24, #0x1b8
    +0x1e34: ldr     s19, [x24, #400]
    +0x1e38: ld1     {v3.s}[3], [x12]
    +0x1e3c: ld1     {v9.s}[1], [x11]
    +0x1e40: ld1     {v14.s}[1], [x10]
    +0x1e44: add     x10, x24, #0x1b0
    +0x1e48: ldr     s4, [x24, #412]
    +0x1e4c: ld1     {v19.s}[1], [x10]
    +0x1e50: add     x10, x24, #0x1d8
    +0x1e54: add     x11, x24, #0x1bc
    +0x1e58: ld1     {v4.s}[1], [x11]
    +0x1e5c: add     x12, x24, #0x1cc
    +0x1e60: add     x11, x24, #0x1e8
    +0x1e64: ld1     {v14.s}[2], [x10]
    +0x1e68: ld1     {v9.s}[2], [x12]
    +0x1e6c: add     x10, x24, #0x1dc
    +0x1e70: ld1     {v19.s}[2], [x9]
    +0x1e74: add     x9, x24, #0x1f8
    +0x1e78: ld1     {v31.s}[3], [x11]
    +0x1e7c: ld1     {v4.s}[2], [x10]
    +0x1e80: add     x10, x24, #0x1f0
    +0x1e84: ld1     {v14.s}[3], [x9]
    +0x1e88: add     x9, x24, #0x1ec
    +0x1e8c: ld1     {v9.s}[3], [x9]
    +0x1e90: ld1     {v19.s}[3], [x10]
    +0x1e94: add     x9, x24, #0x1fc
    +0x1e98: ld1     {v4.s}[3], [x9]
    +0x1e9c: add     x10, x24, #0x1e0
    +0x1ea0: tbl     v25.16b, {v28.16b-v31.16b}, v15.16b
    +0x1ea4: tbl     v11.16b, {v11.16b-v14.16b}, v15.16b
    +0x1ea8: ld1     {v23.s}[3], [x10]
    +0x1eac: add     x9, x19, x8
    +0x1eb0: tbl     v6.16b, {v6.16b-v9.16b}, v15.16b
    +0x1eb4: tbl     v7.16b, {v16.16b-v19.16b}, v15.16b
    +0x1eb8: movi    v19.16b, #0x8
    +0x1ebc: tbl     v1.16b, {v1.16b-v4.16b}, v15.16b
    +0x1ec0: sub     v3.16b, v0.16b, v10.16b
    +0x1ec4: shl     v17.16b, v24.16b, #3
    +0x1ec8: tbl     v2.16b, {v20.16b-v23.16b}, v15.16b
    +0x1ecc: movi    v20.16b, #0x4
    +0x1ed0: sub     v16.16b, v0.16b, v25.16b
    +0x1ed4: shl     v4.16b, v11.16b, #2
    +0x1ed8: add     x8, x8, #0x30
    +0x1edc: add     x24, x24, #0x200
    +0x1ee0: ushr    v18.16b, v3.16b, #1
    +0x1ee4: add     v6.16b, v6.16b, v6.16b
    +0x1ee8: shl     v7.16b, v7.16b, #4
    +0x1eec: shl     v1.16b, v1.16b, #5
    +0x1ef0: shl     v3.16b, v3.16b, #7
    +0x1ef4: cmp     x8, #0x1a0
    +0x1ef8: sub     v4.16b, v19.16b, v4.16b
    +0x1efc: movi    v19.16b, #0x10
    +0x1f00: sub     v2.16b, v0.16b, v2.16b
    +0x1f04: sub     v6.16b, v20.16b, v6.16b
    +0x1f08: sub     v7.16b, v5.16b, v7.16b
    +0x1f0c: orr     v4.16b, v4.16b, v18.16b
    +0x1f10: movi    v18.16b, #0x40
    +0x1f14: sub     v17.16b, v19.16b, v17.16b
    +0x1f18: ushr    v19.16b, v16.16b, #2
    +0x1f1c: shl     v16.16b, v16.16b, #6
    +0x1f20: orr     v3.16b, v7.16b, v3.16b
    +0x1f24: sub     v1.16b, v18.16b, v1.16b
    +0x1f28: orr     v2.16b, v17.16b, v2.16b
    +0x1f2c: orr     v6.16b, v6.16b, v19.16b
    +0x1f30: orr     v19.16b, v4.16b, v1.16b
    +0x1f34: orr     v17.16b, v2.16b, v16.16b
    +0x1f38: orr     v18.16b, v6.16b, v3.16b
    +0x1f3c: st3     {v17.16b-v19.16b}, [x9]
    +0x1f40: b.ne    <mldsa44_keypair_internal+0x1b3c>
    +0x1f44: str     xzr, [sp, #4384]
    +0x1f48: add     x8, sp, #0x1, lsl #12
    +0x1f4c: movi    v0.16b, #0x2
    +0x1f50: movi    v5.16b, #0x20
    +0x1f54: add     x8, x8, #0x120
    +0x1f58: ldr     q15, [sp, #16]
    +0x1f5c: mov     w8, #0x1a0
    +0x1f60: ldp     s16, s1, [x23, #16]
    +0x1f64: add     x9, x23, #0x30
    +0x1f68: add     x10, x23, #0x34
    +0x1f6c: add     x12, x23, #0x50
    +0x1f70: add     x13, x23, #0x54
    +0x1f74: ldp     s20, s24, [x23]
    +0x1f78: add     x14, x23, #0x70
    +0x1f7c: ld1     {v16.s}[1], [x9]
    +0x1f80: ld1     {v1.s}[1], [x10]
    +0x1f84: add     x9, x23, #0x20
    +0x1f88: add     x15, x23, #0x74
    +0x1f8c: add     x10, x23, #0x40
    +0x1f90: add     x11, x23, #0x60
    +0x1f94: ld1     {v20.s}[1], [x9]
    +0x1f98: add     x9, x23, #0x44
    +0x1f9c: add     x17, x23, #0xd4
    +0x1fa0: ld1     {v16.s}[2], [x12]
    +0x1fa4: ld1     {v1.s}[2], [x13]
    +0x1fa8: add     x12, x23, #0x24
    +0x1fac: ld1     {v24.s}[1], [x12]
    +0x1fb0: add     x12, x23, #0xb4
    +0x1fb4: add     x0, x23, #0xf4
    +0x1fb8: ld1     {v20.s}[2], [x10]
    +0x1fbc: add     x18, x23, #0xc4
    +0x1fc0: add     x13, x23, #0xa0
    +0x1fc4: ld1     {v16.s}[3], [x14]
    +0x1fc8: ld1     {v1.s}[3], [x15]
    +0x1fcc: add     x16, x23, #0xc0
    +0x1fd0: ldp     s17, s2, [x23, #144]
    +0x1fd4: ld1     {v24.s}[2], [x9]
    +0x1fd8: add     x9, x23, #0x64
    +0x1fdc: ld1     {v20.s}[3], [x11]
    +0x1fe0: add     x14, x23, #0xe0
    +0x1fe4: ldp     s28, s6, [x23, #8]
    +0x1fe8: add     x15, x23, #0x120
    +0x1fec: ld1     {v2.s}[1], [x12]
    +0x1ff0: ld1     {v24.s}[3], [x9]
    +0x1ff4: add     x1, x23, #0x124
    +0x1ff8: ldp     s21, s25, [x23, #128]
    +0x1ffc: add     x12, x23, #0x140
    +0x2000: add     x10, x23, #0x160
    +0x2004: add     x11, x23, #0x1a0
    +0x2008: add     x9, x23, #0x1c0
    +0x200c: ld1     {v2.s}[2], [x17]
    +0x2010: add     x17, x23, #0xa4
    +0x2014: ld1     {v25.s}[1], [x17]
    +0x2018: ld1     {v21.s}[1], [x13]
    +0x201c: add     x17, x23, #0xe4
    +0x2020: add     x13, x23, #0x164
    +0x2024: ld1     {v2.s}[3], [x0]
    +0x2028: add     x0, x23, #0x144
    +0x202c: ldr     s3, [x23, #276]
    +0x2030: ld1     {v25.s}[2], [x18]
    +0x2034: add     x18, x23, #0x134
    +0x2038: ld1     {v21.s}[2], [x16]
    +0x203c: add     x16, x23, #0x48
    +0x2040: ld1     {v3.s}[1], [x18]
    +0x2044: add     x18, x23, #0x28
    +0x2048: ld1     {v28.s}[1], [x18]
    +0x204c: add     x18, x23, #0x154
    +0x2050: ld1     {v25.s}[3], [x17]
    +0x2054: ld1     {v21.s}[3], [x14]
    +0x2058: add     x14, x23, #0x174
    +0x205c: ldr     s26, [x23, #260]
    +0x2060: ld1     {v3.s}[2], [x18]
    +0x2064: add     x18, x23, #0x2c
    +0x2068: ldr     s22, [x23, #256]
    +0x206c: ld1     {v6.s}[1], [x18]
    +0x2070: ld1     {v28.s}[2], [x16]
    +0x2074: add     x16, x23, #0x4c
    +0x2078: add     x17, x23, #0x68
    +0x207c: ld1     {v26.s}[1], [x1]
    +0x2080: ld1     {v22.s}[1], [x15]
    +0x2084: ld1     {v3.s}[3], [x14]
    +0x2088: add     x14, x23, #0x6c
    +0x208c: add     x15, x23, #0x1b4
    +0x2090: ld1     {v6.s}[2], [x16]
    +0x2094: ldr     s4, [x23, #404]
    +0x2098: ld1     {v28.s}[3], [x17]
    +0x209c: ld1     {v26.s}[2], [x0]
    +0x20a0: ld1     {v22.s}[2], [x12]
    +0x20a4: add     x12, x23, #0x1d4
    +0x20a8: ld1     {v4.s}[1], [x15]
    +0x20ac: add     x15, x23, #0xa8
    +0x20b0: ld1     {v6.s}[3], [x14]
    +0x20b4: add     x14, x23, #0x1a4
    +0x20b8: ldp     s29, s7, [x23, #136]
    +0x20bc: ld1     {v26.s}[3], [x13]
    +0x20c0: ld1     {v4.s}[2], [x12]
    +0x20c4: add     x12, x23, #0xc8
    +0x20c8: ld1     {v22.s}[3], [x10]
    +0x20cc: add     x10, x23, #0x1f4
    +0x20d0: ldr     s27, [x23, #388]
    +0x20d4: ldr     s23, [x23, #384]
    +0x20d8: ld1     {v29.s}[1], [x15]
    +0x20dc: add     x13, x23, #0xe8
    +0x20e0: ld1     {v4.s}[3], [x10]
    +0x20e4: ld1     {v27.s}[1], [x14]
    +0x20e8: ld1     {v23.s}[1], [x11]
    +0x20ec: add     x10, x23, #0x128
    +0x20f0: add     x11, x23, #0x38
    +0x20f4: ld1     {v29.s}[2], [x12]
    +0x20f8: add     x12, x23, #0x1c4
    +0x20fc: tbl     v10.16b, {v1.16b-v4.16b}, v15.16b
    +0x2100: ldp     s11, s1, [x23, #24]
    +0x2104: ld1     {v27.s}[2], [x12]
    +0x2108: ld1     {v23.s}[2], [x9]
    +0x210c: add     x9, x23, #0x1e4
    +0x2110: ld1     {v29.s}[3], [x13]
    +0x2114: add     x13, x23, #0x78
    +0x2118: add     x12, x23, #0x1a8
    +0x211c: ldr     s30, [x23, #264]
    +0x2120: ld1     {v11.s}[1], [x11]
    +0x2124: add     x11, x23, #0x168
    +0x2128: ld1     {v27.s}[3], [x9]
    +0x212c: add     x9, x23, #0x58
    +0x2130: ld1     {v30.s}[1], [x10]
    +0x2134: add     x10, x23, #0x3c
    +0x2138: ld1     {v1.s}[1], [x10]
    +0x213c: ld1     {v11.s}[2], [x9]
    +0x2140: add     x9, x23, #0x5c
    +0x2144: add     x10, x23, #0x148
    +0x2148: tbl     v24.16b, {v24.16b-v27.16b}, v15.16b
    +0x214c: ld1     {v30.s}[2], [x10]
    +0x2150: add     x10, x23, #0xac
    +0x2154: ld1     {v1.s}[2], [x9]
    +0x2158: ld1     {v7.s}[1], [x10]
    +0x215c: add     x10, x23, #0x7c
    +0x2160: ld1     {v11.s}[3], [x13]
    +0x2164: add     x13, x23, #0xb8
    +0x2168: add     x9, x23, #0x1c8
    +0x216c: ld1     {v30.s}[3], [x11]
    +0x2170: add     x11, x23, #0xcc
    +0x2174: ld1     {v1.s}[3], [x10]
    +0x2178: ld1     {v7.s}[2], [x11]
    +0x217c: add     x11, x23, #0xb0
    +0x2180: ldp     s12, s2, [x23, #152]
    +0x2184: ld1     {v17.s}[1], [x11]
    +0x2188: add     x11, x23, #0xd8
    +0x218c: add     x10, x23, #0xec
    +0x2190: ldr     s31, [x23, #392]
    +0x2194: ld1     {v7.s}[3], [x10]
    +0x2198: add     x10, x23, #0xd0
    +0x219c: ld1     {v12.s}[1], [x13]
    +0x21a0: add     x13, x23, #0xbc
    +0x21a4: ld1     {v17.s}[2], [x10]
    +0x21a8: ld1     {v2.s}[1], [x13]
    +0x21ac: add     x10, x23, #0xf8
    +0x21b0: ldr     s8, [x23, #268]
    +0x21b4: ld1     {v31.s}[1], [x12]
    +0x21b8: add     x12, x23, #0x12c
    +0x21bc: add     x13, x23, #0x15c
    +0x21c0: ld1     {v12.s}[2], [x11]
    +0x21c4: add     x11, x23, #0xdc
    +0x21c8: ld1     {v8.s}[1], [x12]
    +0x21cc: ld1     {v2.s}[2], [x11]
    +0x21d0: add     x11, x23, #0xfc
    +0x21d4: add     x12, x23, #0x13c
    +0x21d8: ld1     {v31.s}[2], [x9]
    +0x21dc: add     x9, x23, #0x1d0
    +0x21e0: ld1     {v12.s}[3], [x10]
    +0x21e4: add     x10, x23, #0xf0
    +0x21e8: ldr     s13, [x23, #280]
    +0x21ec: ld1     {v17.s}[3], [x10]
    +0x21f0: add     x10, x23, #0x138
    +0x21f4: ldr     s18, [x23, #272]
    +0x21f8: ld1     {v2.s}[3], [x11]
    +0x21fc: add     x11, x23, #0x130
    +0x2200: ld1     {v13.s}[1], [x10]
    +0x2204: ldr     s3, [x23, #284]
    +0x2208: add     x10, x23, #0x14c
    +0x220c: ld1     {v18.s}[1], [x11]
    +0x2210: add     x11, x23, #0x158
    +0x2214: ld1     {v8.s}[2], [x10]
    +0x2218: ld1     {v3.s}[1], [x12]
    +0x221c: add     x12, x23, #0x150
    +0x2220: add     x10, x23, #0x16c
    +0x2224: ld1     {v13.s}[2], [x11]
    +0x2228: add     x11, x23, #0x1ac
    +0x222c: ld1     {v18.s}[2], [x12]
    +0x2230: add     x12, x23, #0x178
    +0x2234: ld1     {v8.s}[3], [x10]
    +0x2238: ld1     {v3.s}[2], [x13]
    +0x223c: add     x10, x23, #0x170
    +0x2240: ldr     s9, [x23, #396]
    +0x2244: ld1     {v13.s}[3], [x12]
    +0x2248: add     x12, x23, #0x17c
    +0x224c: ldr     s14, [x23, #408]
    +0x2250: ld1     {v18.s}[3], [x10]
    +0x2254: add     x10, x23, #0x1b8
    +0x2258: ldr     s19, [x23, #400]
    +0x225c: ld1     {v3.s}[3], [x12]
    +0x2260: ld1     {v9.s}[1], [x11]
    +0x2264: ld1     {v14.s}[1], [x10]
    +0x2268: add     x10, x23, #0x1b0
    +0x226c: ldr     s4, [x23, #412]
    +0x2270: ld1     {v19.s}[1], [x10]
    +0x2274: add     x10, x23, #0x1d8
    +0x2278: add     x11, x23, #0x1bc
    +0x227c: ld1     {v4.s}[1], [x11]
    +0x2280: add     x12, x23, #0x1cc
    +0x2284: add     x11, x23, #0x1e8
    +0x2288: ld1     {v14.s}[2], [x10]
    +0x228c: ld1     {v9.s}[2], [x12]
    +0x2290: add     x10, x23, #0x1dc
    +0x2294: ld1     {v19.s}[2], [x9]
    +0x2298: add     x9, x23, #0x1f8
    +0x229c: ld1     {v31.s}[3], [x11]
    +0x22a0: ld1     {v4.s}[2], [x10]
    +0x22a4: add     x10, x23, #0x1f0
    +0x22a8: ld1     {v14.s}[3], [x9]
    +0x22ac: add     x9, x23, #0x1ec
    +0x22b0: ld1     {v9.s}[3], [x9]
    +0x22b4: ld1     {v19.s}[3], [x10]
    +0x22b8: add     x9, x23, #0x1fc
    +0x22bc: ld1     {v4.s}[3], [x9]
    +0x22c0: add     x10, x23, #0x1e0
    +0x22c4: tbl     v25.16b, {v28.16b-v31.16b}, v15.16b
    +0x22c8: tbl     v11.16b, {v11.16b-v14.16b}, v15.16b
    +0x22cc: ld1     {v23.s}[3], [x10]
    +0x22d0: add     x9, x19, x8
    +0x22d4: tbl     v6.16b, {v6.16b-v9.16b}, v15.16b
    +0x22d8: tbl     v7.16b, {v16.16b-v19.16b}, v15.16b
    +0x22dc: movi    v19.16b, #0x8
    +0x22e0: tbl     v1.16b, {v1.16b-v4.16b}, v15.16b
    +0x22e4: sub     v3.16b, v0.16b, v10.16b
    +0x22e8: shl     v17.16b, v24.16b, #3
    +0x22ec: tbl     v2.16b, {v20.16b-v23.16b}, v15.16b
    +0x22f0: movi    v20.16b, #0x4
    +0x22f4: sub     v16.16b, v0.16b, v25.16b
    +0x22f8: shl     v4.16b, v11.16b, #2
    +0x22fc: add     x8, x8, #0x30
    +0x2300: add     x23, x23, #0x200
    +0x2304: ushr    v18.16b, v3.16b, #1
    +0x2308: add     v6.16b, v6.16b, v6.16b
    +0x230c: shl     v7.16b, v7.16b, #4
    +0x2310: shl     v1.16b, v1.16b, #5
    +0x2314: shl     v3.16b, v3.16b, #7
    +0x2318: cmp     x8, #0x200
    +0x231c: sub     v4.16b, v19.16b, v4.16b
    +0x2320: movi    v19.16b, #0x10
    +0x2324: sub     v2.16b, v0.16b, v2.16b
    +0x2328: sub     v6.16b, v20.16b, v6.16b
    +0x232c: sub     v7.16b, v5.16b, v7.16b
    +0x2330: orr     v4.16b, v4.16b, v18.16b
    +0x2334: movi    v18.16b, #0x40
    +0x2338: sub     v17.16b, v19.16b, v17.16b
    +0x233c: ushr    v19.16b, v16.16b, #2
    +0x2340: shl     v16.16b, v16.16b, #6
    +0x2344: orr     v3.16b, v7.16b, v3.16b
    +0x2348: sub     v1.16b, v18.16b, v1.16b
    +0x234c: orr     v2.16b, v17.16b, v2.16b
    +0x2350: orr     v6.16b, v6.16b, v19.16b
    +0x2354: orr     v19.16b, v4.16b, v1.16b
    +0x2358: orr     v17.16b, v2.16b, v16.16b
    +0x235c: orr     v18.16b, v6.16b, v3.16b
    +0x2360: st3     {v17.16b-v19.16b}, [x9]
    +0x2364: b.ne    <mldsa44_keypair_internal+0x1f60>
    +0x2368: str     xzr, [sp, #4384]
    +0x236c: add     x8, sp, #0x1, lsl #12
    +0x2370: add     x0, sp, #0x20
    +0x2374: add     x8, x8, #0x120
    +0x2378: bl      <mldsa_poly_ntt>
    +0x237c: add     x0, x22, #0x400
    +0x2380: bl      <mldsa_poly_ntt>
    +0x2384: add     x0, x22, #0x800
    +0x2388: bl      <mldsa_poly_ntt>
    +0x238c: add     x0, x22, #0xc00
    +0x2390: bl      <mldsa_poly_ntt>
    +0x2394: ldr     q0, [sp, #4256]
    +0x2398: ldr     q1, [sp, #4272]
    +0x239c: add     x4, sp, #0x1, lsl #12
    +0x23a0: add     x0, x20, #0x20
    +0x23a4: add     x1, x19, #0x380
    +0x23a8: add     x2, sp, #0x20
    +0x23ac: add     x3, x19, #0x200
    +0x23b0: add     x4, x4, #0xa0
    +0x23b4: add     x23, sp, #0x1, lsl #12
    +0x23b8: stp     q0, q1, [x20]
    +0x23bc: add     x23, x23, #0xa0
    +0x23c0: bl      <mld_compute_pack_t0_t144>
    +0x23c4: movi    v18.2d, #0x0
    +0x23c8: ldp     d0, d1, [x20]
    +0x23cc: ldp     d6, d7, [x20, #32]
    +0x23d0: add     x0, sp, #0x1, lsl #12
    +0x23d4: ldp     d2, d3, [x20, #16]
    +0x23d8: add     x0, x0, #0x120
    +0x23dc: add     x24, sp, #0x1, lsl #12
    +0x23e0: str     q18, [sp, #4384]
    +0x23e4: add     x24, x24, #0x120
    +0x23e8: stur    q18, [x21, #188]
    +0x23ec: str     q18, [sp, #4416]
    +0x23f0: ldr     d4, [sp, #4392]
    +0x23f4: str     q18, [sp, #4400]
    +0x23f8: ldr     d16, [sp, #4416]
    +0x23fc: ldr     d17, [sp, #4424]
    +0x2400: ldr     d5, [sp, #4408]
    +0x2404: str     q18, [sp, #4432]
    +0x2408: eor     v1.8b, v4.8b, v1.8b
    +0x240c: eor     v4.8b, v16.8b, v6.8b
    +0x2410: str     d0, [sp, #4384]
    +0x2414: ldr     d16, [sp, #4440]
    +0x2418: ldp     d6, d0, [x20, #48]
    +0x241c: eor     v3.8b, v5.8b, v3.8b
    +0x2420: eor     v5.8b, v17.8b, v7.8b
    +0x2424: ldr     d7, [sp, #4432]
    +0x2428: str     q18, [sp, #4464]
    +0x242c: str     d2, [sp, #4400]
    +0x2430: eor     v0.8b, v16.8b, v0.8b
    +0x2434: str     d4, [sp, #4416]
    +0x2438: eor     v6.8b, v7.8b, v6.8b
    +0x243c: ldp     d2, d4, [x20, #80]
    +0x2440: str     q18, [sp, #4448]
    +0x2444: str     d1, [sp, #4392]
    +0x2448: ldp     d7, d1, [x20, #64]
    +0x244c: str     d3, [sp, #4408]
    +0x2450: ldr     d3, [sp, #4464]
    +0x2454: ldr     d16, [sp, #4456]
    +0x2458: str     q18, [sp, #4480]
    +0x245c: ldr     d17, [sp, #4448]
    +0x2460: eor     v2.8b, v3.8b, v2.8b
    +0x2464: str     d0, [sp, #4440]
    +0x2468: eor     v1.8b, v16.8b, v1.8b
    +0x246c: ldp     d3, d0, [x20, #96]
    +0x2470: ldr     d16, [sp, #4472]
    +0x2474: str     d5, [sp, #4424]
    +0x2478: ldr     d5, [sp, #4480]
    +0x247c: eor     v7.8b, v17.8b, v7.8b
    +0x2480: eor     v4.8b, v16.8b, v4.8b
    +0x2484: str     d6, [sp, #4432]
    +0x2488: ldr     d6, [sp, #4488]
    +0x248c: eor     v3.8b, v5.8b, v3.8b
    +0x2490: str     q18, [sp, #4512]
    +0x2494: str     q18, [sp, #4496]
    +0x2498: eor     v0.8b, v6.8b, v0.8b
    +0x249c: str     d1, [sp, #4456]
    +0x24a0: ldr     d5, [sp, #4496]
    +0x24a4: ldr     d6, [sp, #4504]
    +0x24a8: str     d2, [sp, #4464]
    +0x24ac: ldp     d1, d2, [x20, #112]
    +0x24b0: str     d4, [sp, #4472]
    +0x24b4: ldr     d4, [sp, #4512]
    +0x24b8: str     d3, [sp, #4480]
    +0x24bc: ldr     d3, [x20, #128]
    +0x24c0: eor     v1.8b, v5.8b, v1.8b
    +0x24c4: eor     v2.8b, v6.8b, v2.8b
    +0x24c8: str     q18, [sp, #4560]
    +0x24cc: eor     v3.8b, v4.8b, v3.8b
    +0x24d0: str     q18, [sp, #4528]
    +0x24d4: str     d7, [sp, #4448]
    +0x24d8: str     q18, [sp, #4544]
    +0x24dc: str     d0, [sp, #4488]
    +0x24e0: str     d1, [sp, #4496]
    +0x24e4: str     d2, [sp, #4504]
    +0x24e8: str     d3, [sp, #4512]
    +0x24ec: bl      <mldsa_keccakf1600_permute>
    +0x24f0: ldp     d1, d2, [x20, #136]
    +0x24f4: add     x0, sp, #0x1, lsl #12
    +0x24f8: ldr     d0, [sp, #4384]
    +0x24fc: ldr     d3, [sp, #4392]
    +0x2500: add     x0, x0, #0x120
    +0x2504: ldr     d5, [sp, #4400]
    +0x2508: ldr     d6, [sp, #4416]
    +0x250c: ldr     d7, [sp, #4424]
    +0x2510: eor     v0.8b, v0.8b, v1.8b
    +0x2514: eor     v1.8b, v3.8b, v2.8b
    +0x2518: ldr     d3, [sp, #4408]
    +0x251c: ldp     d4, d2, [x20, #152]
    +0x2520: ldr     d16, [sp, #4432]
    +0x2524: ldr     d17, [sp, #4440]
    +0x2528: ldr     d18, [sp, #4448]
    +0x252c: str     d0, [sp, #4384]
    +0x2530: eor     v4.8b, v5.8b, v4.8b
    +0x2534: eor     v2.8b, v3.8b, v2.8b
    +0x2538: str     d1, [sp, #4392]
    +0x253c: ldp     d5, d3, [x20, #168]
    +0x2540: str     d2, [sp, #4408]
    +0x2544: ldp     d1, d2, [x20, #216]
    +0x2548: eor     v5.8b, v6.8b, v5.8b
    +0x254c: eor     v3.8b, v7.8b, v3.8b
    +0x2550: str     d4, [sp, #4400]
    +0x2554: ldp     d6, d7, [x20, #184]
    +0x2558: ldr     d4, [sp, #4464]
    +0x255c: str     d5, [sp, #4416]
    +0x2560: eor     v1.8b, v4.8b, v1.8b
    +0x2564: ldr     d4, [sp, #4480]
    +0x2568: eor     v6.8b, v16.8b, v6.8b
    +0x256c: ldp     d16, d0, [x20, #200]
    +0x2570: eor     v7.8b, v17.8b, v7.8b
    +0x2574: ldr     d17, [sp, #4456]
    +0x2578: str     d3, [sp, #4424]
    +0x257c: ldp     d3, d5, [x20, #232]
    +0x2580: str     d1, [sp, #4464]
    +0x2584: eor     v0.8b, v17.8b, v0.8b
    +0x2588: ldr     d17, [sp, #4472]
    +0x258c: str     d6, [sp, #4432]
    +0x2590: ldr     d6, [sp, #4488]
    +0x2594: str     d7, [sp, #4440]
    +0x2598: ldr     d7, [sp, #4496]
    +0x259c: eor     v2.8b, v17.8b, v2.8b
    +0x25a0: eor     v3.8b, v4.8b, v3.8b
    +0x25a4: ldr     d1, [x20, #264]
    +0x25a8: str     d0, [sp, #4456]
    +0x25ac: ldp     d4, d0, [x20, #248]
    +0x25b0: eor     v5.8b, v6.8b, v5.8b
    +0x25b4: ldr     d6, [sp, #4504]
    +0x25b8: eor     v16.8b, v18.8b, v16.8b
    +0x25bc: str     d2, [sp, #4472]
    +0x25c0: ldr     d2, [sp, #4512]
    +0x25c4: eor     v4.8b, v7.8b, v4.8b
    +0x25c8: eor     v0.8b, v6.8b, v0.8b
    +0x25cc: str     d3, [sp, #4480]
    +0x25d0: eor     v1.8b, v2.8b, v1.8b
    +0x25d4: str     d16, [sp, #4448]
    +0x25d8: str     d5, [sp, #4488]
    +0x25dc: str     d4, [sp, #4496]
    +0x25e0: str     d0, [sp, #4504]
    +0x25e4: str     d1, [sp, #4512]
    +0x25e8: bl      <mldsa_keccakf1600_permute>
    +0x25ec: ldp     d1, d2, [x20, #272]
    +0x25f0: add     x0, sp, #0x1, lsl #12
    +0x25f4: ldr     d0, [sp, #4384]
    +0x25f8: ldr     d3, [sp, #4392]
    +0x25fc: add     x0, x0, #0x120
    +0x2600: ldr     d5, [sp, #4400]
    +0x2604: ldr     d6, [sp, #4416]
    +0x2608: ldr     d7, [sp, #4424]
    +0x260c: eor     v0.8b, v0.8b, v1.8b
    +0x2610: eor     v1.8b, v3.8b, v2.8b
    +0x2614: ldr     d3, [sp, #4408]
    +0x2618: ldp     d4, d2, [x20, #288]
    +0x261c: ldr     d16, [sp, #4432]
    +0x2620: ldr     d17, [sp, #4440]
    +0x2624: ldr     d18, [sp, #4448]
    +0x2628: str     d0, [sp, #4384]
    +0x262c: eor     v4.8b, v5.8b, v4.8b
    +0x2630: eor     v2.8b, v3.8b, v2.8b
    +0x2634: str     d1, [sp, #4392]
    +0x2638: ldp     d5, d3, [x20, #304]
    +0x263c: str     d2, [sp, #4408]
    +0x2640: ldp     d1, d2, [x20, #352]
    +0x2644: eor     v5.8b, v6.8b, v5.8b
    +0x2648: eor     v3.8b, v7.8b, v3.8b
    +0x264c: str     d4, [sp, #4400]
    +0x2650: ldp     d6, d7, [x20, #320]
    +0x2654: ldr     d4, [sp, #4464]
    +0x2658: str     d5, [sp, #4416]
    +0x265c: eor     v1.8b, v4.8b, v1.8b
    +0x2660: ldr     d4, [sp, #4480]
    +0x2664: eor     v6.8b, v16.8b, v6.8b
    +0x2668: ldp     d16, d0, [x20, #336]
    +0x266c: eor     v7.8b, v17.8b, v7.8b
    +0x2670: ldr     d17, [sp, #4456]
    +0x2674: str     d3, [sp, #4424]
    +0x2678: ldp     d3, d5, [x20, #368]
    +0x267c: str     d1, [sp, #4464]
    +0x2680: eor     v0.8b, v17.8b, v0.8b
    +0x2684: ldr     d17, [sp, #4472]
    +0x2688: str     d6, [sp, #4432]
    +0x268c: ldr     d6, [sp, #4488]
    +0x2690: str     d7, [sp, #4440]
    +0x2694: ldr     d7, [sp, #4496]
    +0x2698: eor     v2.8b, v17.8b, v2.8b
    +0x269c: eor     v3.8b, v4.8b, v3.8b
    +0x26a0: ldr     d1, [x20, #400]
    +0x26a4: str     d0, [sp, #4456]
    +0x26a8: ldp     d4, d0, [x20, #384]
    +0x26ac: eor     v5.8b, v6.8b, v5.8b
    +0x26b0: ldr     d6, [sp, #4504]
    +0x26b4: eor     v16.8b, v18.8b, v16.8b
    +0x26b8: str     d2, [sp, #4472]
    +0x26bc: ldr     d2, [sp, #4512]
    +0x26c0: eor     v4.8b, v7.8b, v4.8b
    +0x26c4: eor     v0.8b, v6.8b, v0.8b
    +0x26c8: str     d3, [sp, #4480]
    +0x26cc: eor     v1.8b, v2.8b, v1.8b
    +0x26d0: str     d16, [sp, #4448]
    +0x26d4: str     d5, [sp, #4488]
    +0x26d8: str     d4, [sp, #4496]
    +0x26dc: str     d0, [sp, #4504]
    +0x26e0: str     d1, [sp, #4512]
    +0x26e4: bl      <mldsa_keccakf1600_permute>
    +0x26e8: ldp     d1, d2, [x20, #408]
    +0x26ec: add     x0, sp, #0x1, lsl #12
    +0x26f0: ldr     d0, [sp, #4384]
    +0x26f4: ldr     d3, [sp, #4392]
    +0x26f8: add     x0, x0, #0x120
    +0x26fc: ldr     d5, [sp, #4400]
    +0x2700: ldr     d6, [sp, #4416]
    +0x2704: ldr     d7, [sp, #4424]
    +0x2708: eor     v0.8b, v0.8b, v1.8b
    +0x270c: eor     v1.8b, v3.8b, v2.8b
    +0x2710: ldr     d3, [sp, #4408]
    +0x2714: ldp     d4, d2, [x20, #424]
    +0x2718: ldr     d16, [sp, #4432]
    +0x271c: ldr     d17, [sp, #4440]
    +0x2720: ldr     d18, [sp, #4448]
    +0x2724: str     d0, [sp, #4384]
    +0x2728: eor     v4.8b, v5.8b, v4.8b
    +0x272c: eor     v2.8b, v3.8b, v2.8b
    +0x2730: str     d1, [sp, #4392]
    +0x2734: ldp     d5, d3, [x20, #440]
    +0x2738: str     d2, [sp, #4408]
    +0x273c: ldp     d1, d2, [x20, #488]
    +0x2740: eor     v5.8b, v6.8b, v5.8b
    +0x2744: eor     v3.8b, v7.8b, v3.8b
    +0x2748: str     d4, [sp, #4400]
    +0x274c: ldp     d6, d7, [x20, #456]
    +0x2750: ldr     d4, [sp, #4464]
    +0x2754: eor     v1.8b, v4.8b, v1.8b
    +0x2758: str     d5, [sp, #4416]
    +0x275c: ldr     d4, [sp, #4480]
    +0x2760: eor     v6.8b, v16.8b, v6.8b
    +0x2764: ldp     d16, d0, [x20, #472]
    +0x2768: eor     v7.8b, v17.8b, v7.8b
    +0x276c: ldr     d17, [sp, #4456]
    +0x2770: str     d3, [sp, #4424]
    +0x2774: ldp     d3, d5, [x20, #504]
    +0x2778: str     d1, [sp, #4464]
    +0x277c: eor     v0.8b, v17.8b, v0.8b
    +0x2780: ldr     d17, [sp, #4472]
    +0x2784: str     d6, [sp, #4432]
    +0x2788: ldr     d6, [sp, #4488]
    +0x278c: str     d7, [sp, #4440]
    +0x2790: ldr     d7, [sp, #4496]
    +0x2794: eor     v2.8b, v17.8b, v2.8b
    +0x2798: eor     v3.8b, v4.8b, v3.8b
    +0x279c: ldr     d4, [x20, #520]
    +0x27a0: eor     v5.8b, v6.8b, v5.8b
    +0x27a4: str     d0, [sp, #4456]
    +0x27a8: ldr     d0, [sp, #4504]
    +0x27ac: ldr     d6, [x20, #528]
    +0x27b0: ldr     d1, [x20, #536]
    +0x27b4: eor     v16.8b, v18.8b, v16.8b
    +0x27b8: str     d2, [sp, #4472]
    +0x27bc: ldr     d2, [sp, #4512]
    +0x27c0: eor     v4.8b, v7.8b, v4.8b
    +0x27c4: eor     v0.8b, v0.8b, v6.8b
    +0x27c8: str     d3, [sp, #4480]
    +0x27cc: eor     v1.8b, v2.8b, v1.8b
    +0x27d0: str     d16, [sp, #4448]
    +0x27d4: str     d5, [sp, #4488]
    +0x27d8: str     d4, [sp, #4496]
    +0x27dc: str     d0, [sp, #4504]
    +0x27e0: str     d1, [sp, #4512]
    +0x27e4: bl      <mldsa_keccakf1600_permute>
    +0x27e8: ldr     d0, [x20, #544]
    +0x27ec: ldr     d1, [sp, #4384]
    +0x27f0: add     x0, sp, #0x1, lsl #12
    +0x27f4: ldr     d2, [x20, #552]
    +0x27f8: ldr     d3, [sp, #4392]
    +0x27fc: add     x0, x0, #0x120
    +0x2800: eor     v0.8b, v1.8b, v0.8b
    +0x2804: ldr     d4, [x20, #560]
    +0x2808: ldr     d5, [sp, #4400]
    +0x280c: eor     v1.8b, v3.8b, v2.8b
    +0x2810: ldr     d2, [x20, #568]
    +0x2814: ldr     d3, [sp, #4408]
    +0x2818: ldr     d7, [sp, #4424]
    +0x281c: eor     v4.8b, v5.8b, v4.8b
    +0x2820: ldr     d5, [x20, #576]
    +0x2824: eor     v2.8b, v3.8b, v2.8b
    +0x2828: ldr     d3, [x20, #584]
    +0x282c: ldr     d6, [sp, #4416]
    +0x2830: ldr     d17, [sp, #4440]
    +0x2834: ldr     d16, [sp, #4432]
    +0x2838: str     d0, [sp, #4384]
    +0x283c: eor     v3.8b, v7.8b, v3.8b
    +0x2840: ldr     d7, [x20, #600]
    +0x2844: eor     v5.8b, v6.8b, v5.8b
    +0x2848: ldr     d6, [x20, #592]
    +0x284c: ldr     d0, [sp, #4456]
    +0x2850: str     d1, [sp, #4392]
    +0x2854: eor     v7.8b, v17.8b, v7.8b
    +0x2858: ldr     d1, [x20, #616]
    +0x285c: str     d4, [sp, #4400]
    +0x2860: ldr     d4, [x20, #624]
    +0x2864: eor     v6.8b, v16.8b, v6.8b
    +0x2868: ldr     d17, [sp, #4464]
    +0x286c: eor     v0.8b, v0.8b, v1.8b
    +0x2870: str     d2, [sp, #4408]
    +0x2874: ldr     d1, [sp, #4472]
    +0x2878: eor     v2.8b, v17.8b, v4.8b
    +0x287c: ldr     d4, [x20, #632]
    +0x2880: str     d5, [sp, #4416]
    +0x2884: str     d3, [sp, #4424]
    +0x2888: ldr     d3, [x20, #640]
    +0x288c: ldr     d5, [sp, #4480]
    +0x2890: eor     v1.8b, v1.8b, v4.8b
    +0x2894: str     d6, [sp, #4432]
    +0x2898: ldr     d4, [sp, #4488]
    +0x289c: eor     v3.8b, v5.8b, v3.8b
    +0x28a0: str     d7, [sp, #4440]
    +0x28a4: ldr     d5, [x20, #648]
    +0x28a8: ldr     d6, [x20, #656]
    +0x28ac: ldr     d7, [sp, #4496]
    +0x28b0: ldr     d16, [x20, #608]
    +0x28b4: eor     v4.8b, v4.8b, v5.8b
    +0x28b8: ldr     d18, [sp, #4448]
    +0x28bc: str     d0, [sp, #4456]
    +0x28c0: eor     v5.8b, v7.8b, v6.8b
    +0x28c4: ldr     d0, [sp, #4504]
    +0x28c8: ldr     d6, [x20, #664]
    +0x28cc: eor     v16.8b, v18.8b, v16.8b
    +0x28d0: str     d2, [sp, #4464]
    +0x28d4: ldr     d2, [sp, #4512]
    +0x28d8: eor     v0.8b, v0.8b, v6.8b
    +0x28dc: str     d1, [sp, #4472]
    +0x28e0: ldr     d1, [x20, #672]
    +0x28e4: str     d3, [sp, #4480]
    +0x28e8: eor     v1.8b, v2.8b, v1.8b
    +0x28ec: str     d16, [sp, #4448]
    +0x28f0: str     d4, [sp, #4488]
    +0x28f4: str     d5, [sp, #4496]
    +0x28f8: str     d0, [sp, #4504]
    +0x28fc: str     d1, [sp, #4512]
    +0x2900: bl      <mldsa_keccakf1600_permute>
    +0x2904: ldr     d0, [x20, #680]
    +0x2908: ldr     d1, [sp, #4384]
    +0x290c: add     x0, sp, #0x1, lsl #12
    +0x2910: ldr     d2, [x20, #688]
    +0x2914: ldr     d3, [sp, #4392]
    +0x2918: add     x0, x0, #0x120
    +0x291c: eor     v0.8b, v1.8b, v0.8b
    +0x2920: ldr     d4, [x20, #696]
    +0x2924: ldr     d5, [sp, #4400]
    +0x2928: eor     v1.8b, v3.8b, v2.8b
    +0x292c: ldr     d2, [x20, #704]
    +0x2930: ldr     d3, [sp, #4408]
    +0x2934: ldr     d7, [sp, #4424]
    +0x2938: eor     v4.8b, v5.8b, v4.8b
    +0x293c: ldr     d5, [x20, #712]
    +0x2940: eor     v2.8b, v3.8b, v2.8b
    +0x2944: ldr     d3, [x20, #720]
    +0x2948: ldr     d6, [sp, #4416]
    +0x294c: ldr     d17, [sp, #4440]
    +0x2950: ldr     d16, [sp, #4432]
    +0x2954: str     d0, [sp, #4384]
    +0x2958: eor     v3.8b, v7.8b, v3.8b
    +0x295c: ldr     d7, [x20, #736]
    +0x2960: eor     v5.8b, v6.8b, v5.8b
    +0x2964: ldr     d6, [x20, #728]
    +0x2968: ldr     d0, [sp, #4456]
    +0x296c: str     d1, [sp, #4392]
    +0x2970: eor     v7.8b, v17.8b, v7.8b
    +0x2974: ldr     d1, [x20, #752]
    +0x2978: str     d4, [sp, #4400]
    +0x297c: ldr     d4, [x20, #760]
    +0x2980: eor     v6.8b, v16.8b, v6.8b
    +0x2984: ldr     d17, [sp, #4464]
    +0x2988: eor     v0.8b, v0.8b, v1.8b
    +0x298c: str     d2, [sp, #4408]
    +0x2990: ldr     d1, [sp, #4472]
    +0x2994: eor     v2.8b, v17.8b, v4.8b
    +0x2998: ldr     d4, [x20, #768]
    +0x299c: str     d5, [sp, #4416]
    +0x29a0: str     d3, [sp, #4424]
    +0x29a4: ldr     d3, [x20, #776]
    +0x29a8: ldr     d5, [sp, #4480]
    +0x29ac: eor     v1.8b, v1.8b, v4.8b
    +0x29b0: str     d6, [sp, #4432]
    +0x29b4: ldr     d4, [sp, #4488]
    +0x29b8: eor     v3.8b, v5.8b, v3.8b
    +0x29bc: str     d7, [sp, #4440]
    +0x29c0: ldr     d5, [x20, #784]
    +0x29c4: ldr     d6, [x20, #792]
    +0x29c8: ldr     d7, [sp, #4496]
    +0x29cc: ldr     d16, [x20, #744]
    +0x29d0: eor     v4.8b, v4.8b, v5.8b
    +0x29d4: ldr     d18, [sp, #4448]
    +0x29d8: str     d0, [sp, #4456]
    +0x29dc: eor     v5.8b, v7.8b, v6.8b
    +0x29e0: ldr     d0, [sp, #4504]
    +0x29e4: ldr     d6, [x20, #800]
    +0x29e8: eor     v16.8b, v18.8b, v16.8b
    +0x29ec: str     d2, [sp, #4464]
    +0x29f0: ldr     d2, [sp, #4512]
    +0x29f4: eor     v0.8b, v0.8b, v6.8b
    +0x29f8: str     d1, [sp, #4472]
    +0x29fc: ldr     d1, [x20, #808]
    +0x2a00: str     d3, [sp, #4480]
    +0x2a04: eor     v1.8b, v2.8b, v1.8b
    +0x2a08: str     d16, [sp, #4448]
    +0x2a0c: str     d4, [sp, #4488]
    +0x2a10: str     d5, [sp, #4496]
    +0x2a14: str     d0, [sp, #4504]
    +0x2a18: str     d1, [sp, #4512]
    +0x2a1c: bl      <mldsa_keccakf1600_permute>
    +0x2a20: ldr     d0, [x20, #816]
    +0x2a24: ldr     d1, [sp, #4384]
    +0x2a28: add     x0, sp, #0x1, lsl #12
    +0x2a2c: ldr     d2, [x20, #824]
    +0x2a30: ldr     d3, [sp, #4392]
    +0x2a34: add     x0, x0, #0x120
    +0x2a38: eor     v0.8b, v1.8b, v0.8b
    +0x2a3c: ldr     d4, [x20, #832]
    +0x2a40: ldr     d5, [sp, #4400]
    +0x2a44: eor     v1.8b, v3.8b, v2.8b
    +0x2a48: ldr     d2, [x20, #840]
    +0x2a4c: ldr     d3, [sp, #4408]
    +0x2a50: ldr     d7, [sp, #4424]
    +0x2a54: eor     v4.8b, v5.8b, v4.8b
    +0x2a58: ldr     d5, [x20, #848]
    +0x2a5c: eor     v2.8b, v3.8b, v2.8b
    +0x2a60: ldr     d3, [x20, #856]
    +0x2a64: ldr     d6, [sp, #4416]
    +0x2a68: ldr     d17, [sp, #4440]
    +0x2a6c: ldr     d16, [sp, #4432]
    +0x2a70: str     d0, [sp, #4384]
    +0x2a74: eor     v3.8b, v7.8b, v3.8b
    +0x2a78: ldr     d7, [x20, #872]
    +0x2a7c: eor     v5.8b, v6.8b, v5.8b
    +0x2a80: ldr     d6, [x20, #864]
    +0x2a84: ldr     d0, [sp, #4456]
    +0x2a88: str     d1, [sp, #4392]
    +0x2a8c: eor     v7.8b, v17.8b, v7.8b
    +0x2a90: ldr     d1, [x20, #888]
    +0x2a94: str     d4, [sp, #4400]
    +0x2a98: ldr     d4, [x20, #896]
    +0x2a9c: eor     v6.8b, v16.8b, v6.8b
    +0x2aa0: ldr     d17, [sp, #4464]
    +0x2aa4: eor     v0.8b, v0.8b, v1.8b
    +0x2aa8: str     d2, [sp, #4408]
    +0x2aac: ldr     d1, [sp, #4472]
    +0x2ab0: eor     v2.8b, v17.8b, v4.8b
    +0x2ab4: ldr     d4, [x20, #904]
    +0x2ab8: str     d5, [sp, #4416]
    +0x2abc: str     d3, [sp, #4424]
    +0x2ac0: ldr     d3, [x20, #912]
    +0x2ac4: ldr     d5, [sp, #4480]
    +0x2ac8: eor     v1.8b, v1.8b, v4.8b
    +0x2acc: str     d6, [sp, #4432]
    +0x2ad0: ldr     d4, [sp, #4488]
    +0x2ad4: eor     v3.8b, v5.8b, v3.8b
    +0x2ad8: str     d7, [sp, #4440]
    +0x2adc: ldr     d5, [x20, #920]
    +0x2ae0: ldr     d6, [x20, #928]
    +0x2ae4: ldr     d7, [sp, #4496]
    +0x2ae8: ldr     d16, [x20, #880]
    +0x2aec: eor     v4.8b, v4.8b, v5.8b
    +0x2af0: ldr     d18, [sp, #4448]
    +0x2af4: str     d0, [sp, #4456]
    +0x2af8: eor     v5.8b, v7.8b, v6.8b
    +0x2afc: ldr     d0, [sp, #4504]
    +0x2b00: ldr     d6, [x20, #936]
    +0x2b04: eor     v16.8b, v18.8b, v16.8b
    +0x2b08: str     d2, [sp, #4464]
    +0x2b0c: ldr     d2, [sp, #4512]
    +0x2b10: eor     v0.8b, v0.8b, v6.8b
    +0x2b14: str     d1, [sp, #4472]
    +0x2b18: ldr     d1, [x20, #944]
    +0x2b1c: str     d3, [sp, #4480]
    +0x2b20: eor     v1.8b, v2.8b, v1.8b
    +0x2b24: str     d16, [sp, #4448]
    +0x2b28: str     d4, [sp, #4488]
    +0x2b2c: str     d5, [sp, #4496]
    +0x2b30: str     d0, [sp, #4504]
    +0x2b34: str     d1, [sp, #4512]
    +0x2b38: bl      <mldsa_keccakf1600_permute>
    +0x2b3c: ldr     d0, [x20, #952]
    +0x2b40: ldr     d1, [sp, #4384]
    +0x2b44: add     x0, sp, #0x1, lsl #12
    +0x2b48: ldr     d2, [x20, #960]
    +0x2b4c: ldr     d3, [sp, #4392]
    +0x2b50: add     x0, x0, #0x120
    +0x2b54: eor     v0.8b, v1.8b, v0.8b
    +0x2b58: ldr     d4, [x20, #968]
    +0x2b5c: ldr     d5, [sp, #4400]
    +0x2b60: eor     v1.8b, v3.8b, v2.8b
    +0x2b64: ldr     d2, [x20, #976]
    +0x2b68: ldr     d3, [sp, #4408]
    +0x2b6c: ldr     d7, [sp, #4424]
    +0x2b70: eor     v4.8b, v5.8b, v4.8b
    +0x2b74: ldr     d5, [x20, #984]
    +0x2b78: eor     v2.8b, v3.8b, v2.8b
    +0x2b7c: ldr     d3, [x20, #992]
    +0x2b80: ldr     d6, [sp, #4416]
    +0x2b84: ldr     d17, [sp, #4440]
    +0x2b88: ldr     d16, [sp, #4432]
    +0x2b8c: str     d0, [sp, #4384]
    +0x2b90: eor     v3.8b, v7.8b, v3.8b
    +0x2b94: ldr     d7, [x20, #1008]
    +0x2b98: eor     v5.8b, v6.8b, v5.8b
    +0x2b9c: ldr     d6, [x20, #1000]
    +0x2ba0: ldr     d0, [sp, #4456]
    +0x2ba4: str     d1, [sp, #4392]
    +0x2ba8: eor     v7.8b, v17.8b, v7.8b
    +0x2bac: ldr     d1, [x20, #1024]
    +0x2bb0: str     d4, [sp, #4400]
    +0x2bb4: ldr     d4, [x20, #1032]
    +0x2bb8: eor     v6.8b, v16.8b, v6.8b
    +0x2bbc: ldr     d17, [sp, #4464]
    +0x2bc0: eor     v0.8b, v0.8b, v1.8b
    +0x2bc4: str     d2, [sp, #4408]
    +0x2bc8: ldr     d1, [sp, #4472]
    +0x2bcc: eor     v2.8b, v17.8b, v4.8b
    +0x2bd0: ldr     d4, [x20, #1040]
    +0x2bd4: str     d5, [sp, #4416]
    +0x2bd8: str     d3, [sp, #4424]
    +0x2bdc: ldr     d3, [x20, #1048]
    +0x2be0: ldr     d5, [sp, #4480]
    +0x2be4: eor     v1.8b, v1.8b, v4.8b
    +0x2be8: str     d6, [sp, #4432]
    +0x2bec: ldr     d4, [sp, #4488]
    +0x2bf0: eor     v3.8b, v5.8b, v3.8b
    +0x2bf4: str     d7, [sp, #4440]
    +0x2bf8: ldr     d5, [x20, #1056]
    +0x2bfc: ldr     d6, [x20, #1064]
    +0x2c00: ldr     d7, [sp, #4496]
    +0x2c04: ldr     d16, [x20, #1016]
    +0x2c08: eor     v4.8b, v4.8b, v5.8b
    +0x2c0c: ldr     d18, [sp, #4448]
    +0x2c10: str     d0, [sp, #4456]
    +0x2c14: eor     v5.8b, v7.8b, v6.8b
    +0x2c18: ldr     d0, [sp, #4504]
    +0x2c1c: ldr     d6, [x20, #1072]
    +0x2c20: eor     v16.8b, v18.8b, v16.8b
    +0x2c24: str     d2, [sp, #4464]
    +0x2c28: ldr     d2, [sp, #4512]
    +0x2c2c: eor     v0.8b, v0.8b, v6.8b
    +0x2c30: str     d1, [sp, #4472]
    +0x2c34: ldr     d1, [x20, #1080]
    +0x2c38: str     d3, [sp, #4480]
    +0x2c3c: eor     v1.8b, v2.8b, v1.8b
    +0x2c40: str     d16, [sp, #4448]
    +0x2c44: str     d4, [sp, #4488]
    +0x2c48: str     d5, [sp, #4496]
    +0x2c4c: str     d0, [sp, #4504]
    +0x2c50: str     d1, [sp, #4512]
    +0x2c54: bl      <mldsa_keccakf1600_permute>
    +0x2c58: ldr     d0, [x20, #1088]
    +0x2c5c: ldr     d1, [sp, #4384]
    +0x2c60: add     x0, sp, #0x1, lsl #12
    +0x2c64: ldr     d2, [x20, #1096]
    +0x2c68: ldr     d3, [sp, #4392]
    +0x2c6c: add     x0, x0, #0x120
    +0x2c70: eor     v0.8b, v1.8b, v0.8b
    +0x2c74: ldr     d4, [x20, #1104]
    +0x2c78: ldr     d5, [sp, #4400]
    +0x2c7c: eor     v1.8b, v3.8b, v2.8b
    +0x2c80: ldr     d2, [x20, #1112]
    +0x2c84: ldr     d3, [sp, #4408]
    +0x2c88: ldr     d7, [sp, #4424]
    +0x2c8c: eor     v4.8b, v5.8b, v4.8b
    +0x2c90: ldr     d5, [x20, #1120]
    +0x2c94: eor     v2.8b, v3.8b, v2.8b
    +0x2c98: ldr     d3, [x20, #1128]
    +0x2c9c: ldr     d6, [sp, #4416]
    +0x2ca0: ldr     d17, [sp, #4440]
    +0x2ca4: ldr     d16, [sp, #4432]
    +0x2ca8: str     d0, [sp, #4384]
    +0x2cac: eor     v3.8b, v7.8b, v3.8b
    +0x2cb0: ldr     d7, [x20, #1144]
    +0x2cb4: eor     v5.8b, v6.8b, v5.8b
    +0x2cb8: ldr     d6, [x20, #1136]
    +0x2cbc: ldr     d0, [sp, #4456]
    +0x2cc0: str     d1, [sp, #4392]
    +0x2cc4: eor     v7.8b, v17.8b, v7.8b
    +0x2cc8: ldr     d1, [x20, #1160]
    +0x2ccc: str     d4, [sp, #4400]
    +0x2cd0: ldr     d4, [x20, #1168]
    +0x2cd4: eor     v6.8b, v16.8b, v6.8b
    +0x2cd8: ldr     d17, [sp, #4464]
    +0x2cdc: eor     v0.8b, v0.8b, v1.8b
    +0x2ce0: str     d2, [sp, #4408]
    +0x2ce4: ldr     d1, [sp, #4472]
    +0x2ce8: eor     v2.8b, v17.8b, v4.8b
    +0x2cec: ldr     d4, [x20, #1176]
    +0x2cf0: str     d5, [sp, #4416]
    +0x2cf4: str     d3, [sp, #4424]
    +0x2cf8: ldr     d3, [x20, #1184]
    +0x2cfc: ldr     d5, [sp, #4480]
    +0x2d00: eor     v1.8b, v1.8b, v4.8b
    +0x2d04: str     d6, [sp, #4432]
    +0x2d08: ldr     d4, [sp, #4488]
    +0x2d0c: eor     v3.8b, v5.8b, v3.8b
    +0x2d10: str     d7, [sp, #4440]
    +0x2d14: ldr     d5, [x20, #1192]
    +0x2d18: ldr     d6, [x20, #1200]
    +0x2d1c: ldr     d7, [sp, #4496]
    +0x2d20: ldr     d16, [x20, #1152]
    +0x2d24: eor     v4.8b, v4.8b, v5.8b
    +0x2d28: ldr     d18, [sp, #4448]
    +0x2d2c: str     d0, [sp, #4456]
    +0x2d30: eor     v5.8b, v7.8b, v6.8b
    +0x2d34: ldr     d0, [sp, #4504]
    +0x2d38: ldr     d6, [x20, #1208]
    +0x2d3c: eor     v16.8b, v18.8b, v16.8b
    +0x2d40: str     d2, [sp, #4464]
    +0x2d44: ldr     d2, [sp, #4512]
    +0x2d48: eor     v0.8b, v0.8b, v6.8b
    +0x2d4c: str     d1, [sp, #4472]
    +0x2d50: ldr     d1, [x20, #1216]
    +0x2d54: str     d3, [sp, #4480]
    +0x2d58: eor     v1.8b, v2.8b, v1.8b
    +0x2d5c: str     d16, [sp, #4448]
    +0x2d60: str     d4, [sp, #4488]
    +0x2d64: str     d5, [sp, #4496]
    +0x2d68: str     d0, [sp, #4504]
    +0x2d6c: str     d1, [sp, #4512]
    +0x2d70: bl      <mldsa_keccakf1600_permute>
    +0x2d74: ldr     d0, [x20, #1224]
    +0x2d78: ldr     d1, [sp, #4384]
    +0x2d7c: add     x0, sp, #0x1, lsl #12
    +0x2d80: ldr     d2, [x20, #1232]
    +0x2d84: ldr     d3, [sp, #4392]
    +0x2d88: add     x0, x0, #0x120
    +0x2d8c: eor     v0.8b, v1.8b, v0.8b
    +0x2d90: ldr     d4, [x20, #1240]
    +0x2d94: ldr     d1, [x20, #1248]
    +0x2d98: ldr     d5, [sp, #4400]
    +0x2d9c: ldr     d6, [sp, #4408]
    +0x2da0: eor     v2.8b, v3.8b, v2.8b
    +0x2da4: ldr     d7, [x20, #1256]
    +0x2da8: ldr     d17, [sp, #4432]
    +0x2dac: ldr     d18, [sp, #4440]
    +0x2db0: eor     v3.8b, v5.8b, v4.8b
    +0x2db4: eor     v1.8b, v6.8b, v1.8b
    +0x2db8: str     d0, [sp, #4384]
    +0x2dbc: ldr     d0, [sp, #4416]
    +0x2dc0: ldr     d5, [x20, #1272]
    +0x2dc4: str     d2, [sp, #4392]
    +0x2dc8: ldr     d6, [x20, #1280]
    +0x2dcc: ldrb    w8, [x21, #88]
    +0x2dd0: ldr     d16, [x20, #1264]
    +0x2dd4: eor     v0.8b, v0.8b, v7.8b
    +0x2dd8: eor     v2.8b, v17.8b, v5.8b
    +0x2ddc: str     d3, [sp, #4400]
    +0x2de0: str     d1, [sp, #4408]
    +0x2de4: eor     v5.8b, v18.8b, v6.8b
    +0x2de8: eor     w8, w8, #0x1f
    +0x2dec: ldr     d1, [x20, #1288]
    +0x2df0: ldr     d3, [sp, #4448]
    +0x2df4: ldr     d4, [sp, #4424]
    +0x2df8: str     d0, [sp, #4416]
    +0x2dfc: ldr     d0, [x20, #1296]
    +0x2e00: ldr     d6, [sp, #4456]
    +0x2e04: eor     v1.8b, v3.8b, v1.8b
    +0x2e08: eor     v4.8b, v4.8b, v16.8b
    +0x2e0c: str     d2, [sp, #4432]
    +0x2e10: ldr     d2, [x20, #1304]
    +0x2e14: eor     v0.8b, v6.8b, v0.8b
    +0x2e18: ldr     d3, [sp, #4464]
    +0x2e1c: strb    w8, [x21, #88]
    +0x2e20: ldrb    w8, [x21, #135]
    +0x2e24: eor     v2.8b, v3.8b, v2.8b
    +0x2e28: str     d4, [sp, #4424]
    +0x2e2c: eor     w8, w8, #0x80
    +0x2e30: str     d5, [sp, #4440]
    +0x2e34: strb    w8, [x21, #135]
    +0x2e38: mov     w8, #0x88
    +0x2e3c: str     d1, [sp, #4448]
    +0x2e40: str     d0, [sp, #4456]
    +0x2e44: str     d2, [sp, #4464]
    +0x2e48: str     w8, [sp, #4584]
    +0x2e4c: bl      <mldsa_keccakf1600_permute>
    +0x2e50: ldr     q0, [sp, #4384]
    +0x2e54: ldr     q1, [sp, #4400]
    +0x2e58: add     x0, sp, #0x20
    +0x2e5c: ldr     q2, [sp, #4432]
    +0x2e60: mov     w1, wzr
    +0x2e64: mov     w2, #0x1000
    +0x2e68: str     q0, [sp, #4128]
    +0x2e6c: ldr     q0, [sp, #4416]
    +0x2e70: str     q1, [sp, #4144]
    +0x2e74: str     q0, [sp, #4160]
    +0x2e78: movi    v0.2d, #0x0
    +0x2e7c: str     q2, [sp, #4176]
    +0x2e80: str     q0, [sp, #4448]
    +0x2e84: str     q0, [sp, #4464]
    +0x2e88: str     q0, [sp, #4480]
    +0x2e8c: str     q0, [sp, #4496]
    +0x2e90: str     q0, [sp, #4512]
    +0x2e94: str     q0, [sp, #4528]
    +0x2e98: str     q0, [sp, #4544]
    +0x2e9c: str     q0, [sp, #4560]
    +0x2ea0: str     q0, [sp, #4576]
    +0x2ea4: str     q0, [sp, #4384]
    +0x2ea8: str     q0, [sp, #4400]
    +0x2eac: str     q0, [sp, #4416]
    +0x2eb0: str     q0, [sp, #4432]
    +0x2eb4: ldr     q0, [sp, #4256]
    +0x2eb8: ldr     q1, [sp, #4272]
    +0x2ebc: ldr     q2, [sp, #4352]
    +0x2ec0: stp     q0, q1, [x19]
    +0x2ec4: ldr     q0, [sp, #4368]
    +0x2ec8: ldr     q1, [sp, #4128]
    +0x2ecc: stp     q2, q0, [x19, #32]
    +0x2ed0: ldr     q0, [sp, #4144]
    +0x2ed4: ldr     q2, [sp, #4160]
    +0x2ed8: stp     q1, q0, [x19, #64]
    +0x2edc: ldr     q0, [sp, #4176]
    +0x2ee0: stp     q2, q0, [x19, #96]
    +0x2ee4: bl      <memset>
    +0x2ee8: movi    v0.2d, #0x0
    +0x2eec: add     x8, sp, #0x1, lsl #12
    +0x2ef0: add     x8, x8, #0x20
    +0x2ef4: str     q0, [sp, #4176]
    +0x2ef8: str     q0, [sp, #4160]
    +0x2efc: str     q0, [sp, #4144]
    +0x2f00: str     q0, [sp, #4128]
    +0x2f04: strh    wzr, [sp, #4224]
    +0x2f08: add     x8, sp, #0x1, lsl #12
    +0x2f0c: str     q0, [sp, #4208]
    +0x2f10: add     x8, x8, #0x60
    +0x2f14: str     q0, [sp, #4192]
    +0x2f18: str     q0, [sp, #4368]
    +0x2f1c: adrp    x8, <page>
    +0x2f20: str     q0, [sp, #4352]
    +0x2f24: str     q0, [sp, #4336]
    +0x2f28: str     q0, [sp, #4320]
    +0x2f2c: str     q0, [sp, #4304]
    +0x2f30: str     q0, [sp, #4288]
    +0x2f34: str     q0, [sp, #4272]
    +0x2f38: str     q0, [sp, #4256]
    +0x2f3c: ldr     x8, [x8, #4088]
    +0x2f40: ldr     x9, [sp, #4600]
    +0x2f44: ldr     x8, [x8]
    +0x2f48: cmp     x8, x9
    +0x2f4c: b.ne    <mldsa44_keypair_internal+0x2fcc>
    +0x2f50: mov     w0, wzr
    +0x2f54: sub     sp, x29, #0x40
    +0x2f58: ldp     x20, x19, [sp, #144]
    +0x2f5c: ldr     x28, [sp, #80]
    +0x2f60: ldp     x22, x21, [sp, #128]
    +0x2f64: ldp     x24, x23, [sp, #112]
    +0x2f68: ldp     x26, x25, [sp, #96]
    +0x2f6c: ldp     x29, x30, [sp, #64]
    +0x2f70: ldp     d9, d8, [sp, #48]
    +0x2f74: ldp     d11, d10, [sp, #32]
    +0x2f78: ldp     d13, d12, [sp, #16]
    +0x2f7c: ldp     d15, d14, [sp], #160
    +0x2f80: mov     x1, #0x0
    +0x2f84: mov     x2, #0x0
    +0x2f88: mov     x3, #0x0
    +0x2f8c: mov     x4, #0x0
    +0x2f90: mov     x5, #0x0
    +0x2f94: mov     x6, #0x0
    +0x2f98: mov     x7, #0x0
    +0x2f9c: mov     x8, #0x0
    +0x2fa0: mov     x9, #0x0
    +0x2fa4: mov     x10, #0x0
    +0x2fa8: mov     x11, #0x0
    +0x2fac: mov     x12, #0x0
    +0x2fb0: mov     x13, #0x0
    +0x2fb4: mov     x14, #0x0
    +0x2fb8: mov     x15, #0x0
    +0x2fbc: mov     x16, #0x0
    +0x2fc0: mov     x17, #0x0
    +0x2fc4: mov     x18, #0x0
    +0x2fc8: ret     
    +0x2fcc: bl      <__stack_chk_fail>

    memset@plt:
       +0x0: adrp    x16, <page>
       +0x4: ldr     x17, [x16, #4072]
       +0x8: add     x16, x16, #0xfe8
       +0xc: br      x17
 ***)

let MLDSA_NATIVE_KEYPAIR_INTERNAL_44_CLANG23_O3_MONO_REDUCED_RAM_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
   [layout_range "mldsa44_keypair_internal";
    layout_range "plt_memset"];;

(* ------------------------------------------------------------------------- *)
(* Correctness, assuming the contracts for memset and memcpy. From the seed SEED (32     *)
(* bytes at seed), the public key at pk (1312 bytes) becomes                 *)
(* mld_keypair_pk_44 SEED and the secret key at sk (2560 bytes)              *)
(* mld_keypair_sk_44 SEED, and the result is 0. The stack is the 10112 bytes *)
(* below the stack pointer: the frame of the function, of up to 4784 bytes,  *)
(* and the stacks of its callees.                                            *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_KEYPAIR_INTERNAL_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!mf mc ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev
     ==> !pk sk seed SEED guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          32768 <= val stackpointer /\ val(stackpointer:int64) < 2 EXP 63 /\
          mld_matrix_terminates 4 4 (mld_keypair_rho 4 4 SEED) /\
          mld_keypair_terminates_44 SEED /\
          PAIRWISE nonoverlapping
           [(pk,1312); (sk,2560);
            (word_sub stackpointer (word 10112),10112)] /\
          ALLPAIRS nonoverlapping
           [(pk,1312); (sk,2560);
            (word_sub stackpointer (word 10112),10112)]
           [(seed,32); (word pc,libmldsa_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                    read PC s = word (pc + mldsa44_keypair_internal) /\
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
                    (!j. j < 1312
                         ==> read(memory :> bytes8(word_add pk (word j))) s =
                             mld_keypair_pk_44 SEED j) /\
                    (!j. j < 2560
                         ==> read(memory :> bytes8(word_add sk (word j))) s =
                             mld_keypair_sk_44 SEED j))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(pk,1312); memory :> bytes(sk,2560);
                  memory :> bytes(word_sub stackpointer (word 10112),10112)])`;;

let MLDSA_NATIVE_KEYPAIR_INTERNAL_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLDSA_NATIVE_KEYPAIR_INTERNAL_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, rho, whether each nibble read by  *)
(* the sampling of each polynomial is accepted (mld_keypair_declass_44), the *)
(* address of memset and the stack, with all accesses within the arguments,  *)
(* the stack, the GOT entries and the stack guard, the region (ea,el) that   *)
(* memset may read and the constants of the callees, and the writes within   *)
(* the keys and the stack.                                                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_KEYPAIR_INTERNAL_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT =
  `!mf mc ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev
     ==> exists f_events.
          forall e pk sk seed SEED guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          32768 <= val stackpointer /\ val(stackpointer:int64) < 2 EXP 63 /\
          mld_matrix_terminates 4 4 (mld_keypair_rho 4 4 SEED) /\
          mld_keypair_terminates_44 SEED /\
          PAIRWISE nonoverlapping
           [(pk,1312); (sk,2560);
            (word_sub stackpointer (word 10112),10112)] /\
          ALLPAIRS nonoverlapping
           [(pk,1312); (sk,2560);
            (word_sub stackpointer (word 10112),10112)]
           [(seed,32); (word pc,libmldsa_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                    read PC s = word (pc + mldsa44_keypair_internal) /\
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
                    (!j. j < 1312
                         ==> read(memory :> bytes8(word_add pk (word j))) s =
                             mld_keypair_pk_44 SEED j) /\
                    (!j. j < 2560
                         ==> read(memory :> bytes8(word_add sk (word j))) s =
                             mld_keypair_sk_44 SEED j) /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events pk sk seed (mld_keypair_rho 4 4 SEED)
                             (mld_keypair_declass_44 SEED) guard mf mc pc
                             (word_sub stackpointer (word 10112))
                             returnaddress /\
                       memaccess_inbounds e2
                        [seed,32; pk,1312; sk,2560;
                         word_sub stackpointer (word 10112),10112;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; word(pc + got_memcpy),8; ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192;
                         word(pc + rodata_mld_zetas),1024;
                         word(pc + mldsa44_keypair_internal_consts),16;
                         word(pc + mld_compute_pack_t0_t144_consts),272;
                         word(pc + mldsa44_polyeta_unpack_consts),128]
                        [pk,1312; sk,2560;
                         word_sub stackpointer (word 10112),10112]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(pk,1312); memory :> bytes(sk,2560);
                  memory :> bytes(word_sub stackpointer (word 10112),10112)])`;;

let MLDSA_NATIVE_KEYPAIR_INTERNAL_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_KEYPAIR_INTERNAL_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_KEYPAIR_INTERNAL_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT =
  `!mf mc ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev
     ==> exists f_events.
          forall e pk sk seed SEED guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          32768 <= val stackpointer /\ val(stackpointer:int64) < 2 EXP 63 /\
          mld_matrix_terminates 4 4 (mld_keypair_rho 4 4 SEED) /\
          mld_keypair_terminates_44 SEED /\
          PAIRWISE nonoverlapping
           [(pk,1312); (sk,2560);
            (word_sub stackpointer (word 10112),10112)] /\
          ALLPAIRS nonoverlapping
           [(pk,1312); (sk,2560);
            (word_sub stackpointer (word 10112),10112)]
           [(seed,32); (word pc,libmldsa_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                    read PC s = word (pc + mldsa44_keypair_internal) /\
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
                       e2 = f_events pk sk seed (mld_keypair_rho 4 4 SEED)
                             (mld_keypair_declass_44 SEED) guard mf mc pc
                             (word_sub stackpointer (word 10112))
                             returnaddress /\
                       memaccess_inbounds e2
                        [seed,32; pk,1312; sk,2560;
                         word_sub stackpointer (word 10112),10112;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; word(pc + got_memcpy),8; ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192;
                         word(pc + rodata_mld_zetas),1024;
                         word(pc + mldsa44_keypair_internal_consts),16;
                         word(pc + mld_compute_pack_t0_t144_consts),272;
                         word(pc + mldsa44_polyeta_unpack_consts),128]
                        [pk,1312; sk,2560;
                         word_sub stackpointer (word 10112),10112]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(pk,1312); memory :> bytes(sk,2560);
                  memory :> bytes(word_sub stackpointer (word 10112),10112)])`;;

let MLDSA_NATIVE_KEYPAIR_INTERNAL_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_KEYPAIR_INTERNAL_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT;;
