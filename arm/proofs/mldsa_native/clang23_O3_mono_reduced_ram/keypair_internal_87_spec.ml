(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Key generation: the statement. This is the code for                       *)
(* mldsa87_keypair_internal (mld_sign_keypair_internal in sign.c, with       *)
(* mld_sample_pack_s1_s2 inlined) from mldsa-native's portable C             *)
(* implementation compiled by clang 23 with -O3 as one translation unit      *)
(* with MLD_CONFIG_REDUCE_RAM (see mldsa_native/README.md). It expands the   *)
(* seed into rho, rho' and the key with an inlined SHAKE256 (one call of     *)
(* mldsa_keccakf1600_permute), samples s2 and s1 from rho' with calls of     *)
(* mldsa87_poly_uniform_eta_4x (four times, four polynomials each), packs    *)
(* each polynomial into the secret key with inlined code (three bits per     *)
(* coefficient), transforms s1 to the NTT domain with seven calls of         *)
(* mldsa_poly_ntt, copies rho into the public key, computes t and packs t1   *)
(* into the public key and t0 into the secret key with                       *)
(* mld_compute_pack_t0_t187, hashes the public key into tr with an inlined   *)
(* SHAKE256 (twenty calls of mldsa_keccakf1600_permute), packs rho, the      *)
(* key and tr into the secret key, and zeroes its buffers with memset and    *)
(* stores. It is verified in the whole image (see libmldsa.ml) against       *)
(* mld_keypair_pk_87 and mld_keypair_sk_87 of common/mldsa_native_sign.ml,   *)
(* using the theorems for the callees and the contracts                      *)
(* memset_full_contract and memcpy_full_contract of                          *)
(* utils/mlkem_native_libc_full.ml (memcpy is used by compute_pack through   *)
(* the expansion of the matrix), assuming that the expansion of the matrix   *)
(* and the sampling of each polynomial terminate, and shown to be constant   *)
(* time and memory safe, with the events depending only on the addresses     *)
(* and the values that the C code declassifies (rho and                      *)
(* mld_keypair_declass_87). The stack is the 13504 bytes of the function     *)
(* and of its callees.                                                       *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native.ml";;
needs "arm/proofs/utils/mlkem_native_libc_full.ml";;
needs "common/mldsa_native_sign.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/poly_uniform_eta_4x_87_spec.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/compute_pack_t0_t1_87_spec.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/libmldsa.ml";;

(*** The code in the image, and the PLT stub for memset:

    mldsa87_keypair_internal:
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
      +0x30: sub     x9, x9, #0xf40
      +0x34: and     x9, x9, #0xffffffffffffffe0
      +0x38: sub     sp, sp, #0x1, lsl #12
      +0x3c: cmp     sp, x9
      +0x40: b.le    <mldsa87_keypair_internal+0x54>
      +0x44: ldr     xzr, [sp]
      +0x48: sub     sp, sp, #0x1, lsl #12
      +0x4c: cmp     sp, x9
      +0x50: b.gt    <mldsa87_keypair_internal+0x44>
      +0x54: mov     sp, x9
      +0x58: adrp    x8, <page>
      +0x5c: ldr     xzr, [sp]
      +0x60: movi    v1.2d, #0x0
      +0x64: ldr     x8, [x8, #4088]
      +0x68: add     x21, sp, #0x1, lsl #12
      +0x6c: mov     x20, x0
      +0x70: add     x21, x21, #0xe60
      +0x74: add     x0, sp, #0x1, lsl #12
      +0x78: add     x23, sp, #0x1, lsl #12
      +0x7c: ldr     x8, [x8]
      +0x80: add     x0, x0, #0xe60
      +0x84: mov     x19, x1
      +0x88: add     x22, sp, #0x160
      +0x8c: add     x23, x23, #0xe60
      +0x90: str     x8, [sp, #7992]
      +0x94: add     x8, sp, #0x1, lsl #12
      +0x98: ldr     q0, [x2, #16]
      +0x9c: add     x8, x8, #0xda0
      +0xa0: str     wzr, [sp, #7976]
      +0xa4: orr     x9, x8, #0x18
      +0xa8: stur    q1, [x21, #24]
      +0xac: str     q0, [sp, #7600]
      +0xb0: ldrb    w10, [x21, #25]
      +0xb4: ldrb    w12, [x21, #34]
      +0xb8: ldrb    w11, [x8, #25]
      +0xbc: ld1     {v0.b}[8], [x9]
      +0xc0: stur    q1, [x21, #184]
      +0xc4: stur    q1, [x21, #168]
      +0xc8: ldr     s2, [sp, #7612]
      +0xcc: ldr     q3, [sp, #7600]
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
     +0x120: ldr     s1, [sp, #7804]
     +0x124: mov     v0.b[11], w9
     +0x128: mov     w9, #0x708
     +0x12c: zip1    v1.8b, v1.8b, v1.8b
     +0x130: strh    w9, [sp, #7616]
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
     +0x15c: str     q2, [sp, #7584]
     +0x160: uzp1    v0.8b, v1.8b, v0.8b
     +0x164: strb    w9, [x21, #32]
     +0x168: eor     w9, w12, #0x1f
     +0x16c: strb    w8, [x21, #135]
     +0x170: mov     w8, #0x88
     +0x174: strb    w9, [x21, #34]
     +0x178: str     w8, [sp, #7976]
     +0x17c: mov     v3.s[3], v0.s[0]
     +0x180: ldr     q0, [sp, #7584]
     +0x184: str     q0, [sp, #7776]
     +0x188: str     q3, [sp, #7792]
     +0x18c: bl      <mldsa_keccakf1600_permute>
     +0x190: ldr     q0, [sp, #7840]
     +0x194: ldr     q1, [sp, #7856]
     +0x198: add     x26, sp, #0x1, lsl #12
     +0x19c: ldr     q2, [sp, #7888]
     +0x1a0: add     x26, x26, #0xde0
     +0x1a4: mov     w8, #0xe
     +0x1a8: str     q0, [sp, #7712]
     +0x1ac: ldr     q0, [sp, #7872]
     +0x1b0: add     x0, sp, #0x160
     +0x1b4: str     q1, [sp, #7728]
     +0x1b8: ldr     q1, [sp, #7776]
     +0x1bc: add     x1, x22, #0x400
     +0x1c0: str     q0, [sp, #7744]
     +0x1c4: ldr     q0, [sp, #7792]
     +0x1c8: add     x2, x22, #0x800
     +0x1cc: str     q2, [sp, #7760]
     +0x1d0: ldr     q2, [sp, #7808]
     +0x1d4: add     x3, x22, #0xc00
     +0x1d8: str     q0, [sp, #7664]
     +0x1dc: ldr     q0, [sp, #7824]
     +0x1e0: add     x4, x26, #0x20
     +0x1e4: str     q1, [sp, #7648]
     +0x1e8: mov     w5, #0xb
     +0x1ec: mov     w6, #0xc
     +0x1f0: str     q0, [sp, #7696]
     +0x1f4: movi    v0.2d, #0x0
     +0x1f8: mov     w7, #0xd
     +0x1fc: str     q2, [sp, #7680]
     +0x200: add     x25, x22, #0x400
     +0x204: add     x24, x22, #0x800
     +0x208: str     q0, [sp, #7904]
     +0x20c: str     q0, [sp, #7920]
     +0x210: str     q0, [sp, #7936]
     +0x214: str     q0, [sp, #7952]
     +0x218: str     q0, [sp, #7968]
     +0x21c: str     q0, [sp, #7776]
     +0x220: str     q0, [sp, #7792]
     +0x224: str     q0, [sp, #7808]
     +0x228: str     q0, [sp, #7824]
     +0x22c: str     q0, [sp, #7840]
     +0x230: str     q0, [sp, #7856]
     +0x234: str     q0, [sp, #7872]
     +0x238: str     q0, [sp, #7888]
     +0x23c: add     x23, x22, #0xc00
     +0x240: strb    w8, [sp]
     +0x244: bl      <mldsa87_poly_uniform_eta_4x>
     +0x248: movi    v0.16b, #0x2
     +0x24c: movi    v5.16b, #0x20
     +0x250: adrp    x8, <page>
     +0x254: ldr     q26, [x8, #1200]
     +0x258: add     x8, x22, #0x100
     +0x25c: mov     w9, #0x4a0
     +0x260: ldp     s16, s1, [x8, #-240]
     +0x264: sub     x10, x8, #0xd0
     +0x268: sub     x11, x8, #0xcc
     +0x26c: sub     x12, x8, #0xac
     +0x270: sub     x15, x8, #0x90
     +0x274: sub     x16, x8, #0x8c
     +0x278: ldp     s20, s24, [x8, #-256]
     +0x27c: ld1     {v16.s}[1], [x10]
     +0x280: ld1     {v1.s}[1], [x11]
     +0x284: sub     x11, x8, #0xb0
     +0x288: sub     x10, x8, #0xe0
     +0x28c: sub     x14, x8, #0xdc
     +0x290: mov     v15.16b, v26.16b
     +0x294: ld1     {v20.s}[1], [x10]
     +0x298: sub     x10, x8, #0x50
     +0x29c: ld1     {v24.s}[1], [x14]
     +0x2a0: ld1     {v16.s}[2], [x11]
     +0x2a4: ld1     {v1.s}[2], [x12]
     +0x2a8: sub     x13, x8, #0xc0
     +0x2ac: sub     x11, x8, #0xa0
     +0x2b0: sub     x12, x8, #0x60
     +0x2b4: sub     x14, x8, #0x40
     +0x2b8: ld1     {v20.s}[2], [x13]
     +0x2bc: sub     x13, x8, #0x30
     +0x2c0: add     x0, x8, #0xf4
     +0x2c4: ld1     {v16.s}[3], [x15]
     +0x2c8: ld1     {v1.s}[3], [x16]
     +0x2cc: sub     x15, x8, #0x4c
     +0x2d0: ldp     s17, s2, [x8, #-112]
     +0x2d4: sub     x16, x8, #0x2c
     +0x2d8: ld1     {v20.s}[3], [x11]
     +0x2dc: sub     x11, x8, #0xc
     +0x2e0: add     x17, x8, #0xa4
     +0x2e4: ldp     s28, s6, [x8, #-248]
     +0x2e8: sub     x18, x8, #0xd8
     +0x2ec: ld1     {v17.s}[1], [x10]
     +0x2f0: ld1     {v2.s}[1], [x15]
     +0x2f4: sub     x15, x8, #0xbc
     +0x2f8: ld1     {v24.s}[2], [x15]
     +0x2fc: sub     x15, x8, #0x9c
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
     +0x468: mov     v26.16b, v15.16b
     +0x46c: ld1     {v1.s}[3], [x12]
     +0x470: sub     x12, x8, #0x34
     +0x474: ld1     {v29.s}[1], [x11]
     +0x478: ldp     s12, s2, [x8, #-104]
     +0x47c: sub     x11, x8, #0x54
     +0x480: ld1     {v7.s}[1], [x11]
     +0x484: sub     x11, x8, #0x48
     +0x488: ld1     {v29.s}[2], [x14]
     +0x48c: ld1     {v12.s}[1], [x11]
     +0x490: ld1     {v2.s}[1], [x13]
     +0x494: sub     x11, x8, #0x18
     +0x498: add     x13, x8, #0x4c
     +0x49c: add     x14, x8, #0x58
     +0x4a0: ld1     {v7.s}[2], [x12]
     +0x4a4: sub     x12, x8, #0x28
     +0x4a8: ld1     {v29.s}[3], [x11]
     +0x4ac: ld1     {v12.s}[2], [x12]
     +0x4b0: sub     x11, x8, #0x24
     +0x4b4: ld1     {v2.s}[2], [x11]
     +0x4b8: add     x11, x8, #0x28
     +0x4bc: add     x12, x8, #0x38
     +0x4c0: ld1     {v7.s}[3], [x10]
     +0x4c4: sub     x10, x8, #0x8
     +0x4c8: ld1     {v12.s}[3], [x10]
     +0x4cc: sub     x10, x8, #0x4
     +0x4d0: ldp     s30, s8, [x8, #8]
     +0x4d4: ld1     {v2.s}[3], [x10]
     +0x4d8: ldp     s13, s3, [x8, #24]
     +0x4dc: add     x10, x8, #0x48
     +0x4e0: ld1     {v30.s}[1], [x11]
     +0x4e4: add     x11, x8, #0x2c
     +0x4e8: ld1     {v8.s}[1], [x11]
     +0x4ec: ld1     {v13.s}[1], [x12]
     +0x4f0: add     x12, x8, #0x3c
     +0x4f4: ld1     {v3.s}[1], [x12]
     +0x4f8: add     x11, x8, #0x68
     +0x4fc: add     x12, x8, #0xc8
     +0x500: ld1     {v30.s}[2], [x10]
     +0x504: add     x10, x8, #0xa8
     +0x508: ld1     {v8.s}[2], [x13]
     +0x50c: add     x13, x8, #0x5c
     +0x510: ld1     {v13.s}[2], [x14]
     +0x514: ld1     {v3.s}[2], [x13]
     +0x518: add     x14, x8, #0x6c
     +0x51c: add     x13, x8, #0xb8
     +0x520: ld1     {v30.s}[3], [x11]
     +0x524: add     x11, x8, #0x7c
     +0x528: ld1     {v13.s}[3], [x15]
     +0x52c: ld1     {v8.s}[3], [x14]
     +0x530: ld1     {v3.s}[3], [x11]
     +0x534: ldp     s31, s9, [x8, #136]
     +0x538: ldp     s14, s4, [x8, #152]
     +0x53c: add     x11, x8, #0xac
     +0x540: ld1     {v31.s}[1], [x10]
     +0x544: add     x10, x8, #0xb0
     +0x548: ld1     {v9.s}[1], [x11]
     +0x54c: ld1     {v14.s}[1], [x13]
     +0x550: ld1     {v19.s}[1], [x10]
     +0x554: add     x10, x8, #0xd8
     +0x558: add     x11, x8, #0xbc
     +0x55c: add     x13, x8, #0xcc
     +0x560: ld1     {v4.s}[1], [x11]
     +0x564: ld1     {v9.s}[2], [x13]
     +0x568: add     x11, x8, #0xdc
     +0x56c: ld1     {v14.s}[2], [x10]
     +0x570: add     x10, x8, #0xd0
     +0x574: ld1     {v31.s}[2], [x12]
     +0x578: ld1     {v19.s}[2], [x10]
     +0x57c: add     x10, x8, #0xf8
     +0x580: add     x12, x8, #0xe8
     +0x584: ld1     {v4.s}[2], [x11]
     +0x588: add     x11, x8, #0xf0
     +0x58c: ld1     {v14.s}[3], [x10]
     +0x590: add     x10, x8, #0xec
     +0x594: ld1     {v31.s}[3], [x12]
     +0x598: ld1     {v9.s}[3], [x10]
     +0x59c: ld1     {v19.s}[3], [x11]
     +0x5a0: add     x10, x8, #0xfc
     +0x5a4: ld1     {v4.s}[3], [x10]
     +0x5a8: add     x11, x8, #0xe0
     +0x5ac: add     x10, x19, x9
     +0x5b0: tbl     v11.16b, {v11.16b-v14.16b}, v15.16b
     +0x5b4: ld1     {v23.s}[3], [x11]
     +0x5b8: tbl     v25.16b, {v28.16b-v31.16b}, v15.16b
     +0x5bc: tbl     v6.16b, {v6.16b-v9.16b}, v15.16b
     +0x5c0: tbl     v7.16b, {v16.16b-v19.16b}, v15.16b
     +0x5c4: movi    v19.16b, #0x8
     +0x5c8: tbl     v1.16b, {v1.16b-v4.16b}, v15.16b
     +0x5cc: sub     v3.16b, v0.16b, v10.16b
     +0x5d0: shl     v17.16b, v24.16b, #3
     +0x5d4: tbl     v2.16b, {v20.16b-v23.16b}, v15.16b
     +0x5d8: movi    v20.16b, #0x4
     +0x5dc: add     x9, x9, #0x30
     +0x5e0: shl     v4.16b, v11.16b, #2
     +0x5e4: sub     v16.16b, v0.16b, v25.16b
     +0x5e8: cmp     x9, #0x500
     +0x5ec: ushr    v18.16b, v3.16b, #1
     +0x5f0: add     v6.16b, v6.16b, v6.16b
     +0x5f4: shl     v7.16b, v7.16b, #4
     +0x5f8: shl     v1.16b, v1.16b, #5
     +0x5fc: shl     v3.16b, v3.16b, #7
     +0x600: add     x8, x8, #0x200
     +0x604: sub     v4.16b, v19.16b, v4.16b
     +0x608: movi    v19.16b, #0x10
     +0x60c: sub     v2.16b, v0.16b, v2.16b
     +0x610: sub     v6.16b, v20.16b, v6.16b
     +0x614: sub     v7.16b, v5.16b, v7.16b
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
     +0x64c: b.ne    <mldsa87_keypair_internal+0x260>
     +0x650: movi    v0.16b, #0x2
     +0x654: movi    v5.16b, #0x20
     +0x658: str     xzr, [sp, #7776]
     +0x65c: add     x8, sp, #0x1, lsl #12
     +0x660: add     x9, x22, #0x400
     +0x664: add     x8, x8, #0xe60
     +0x668: mov     w8, #0x500
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
     +0xa24: cmp     x8, #0x560
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
     +0xa70: b.ne    <mldsa87_keypair_internal+0x66c>
     +0xa74: movi    v0.16b, #0x2
     +0xa78: movi    v5.16b, #0x20
     +0xa7c: str     xzr, [sp, #7776]
     +0xa80: add     x8, sp, #0x1, lsl #12
     +0xa84: add     x9, x22, #0x800
     +0xa88: add     x8, x8, #0xe60
     +0xa8c: mov     w8, #0x560
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
     +0xe20: movi    v20.16b, #0x4
     +0xe24: sub     v16.16b, v0.16b, v25.16b
     +0xe28: shl     v4.16b, v11.16b, #2
     +0xe2c: add     x8, x8, #0x30
     +0xe30: add     x9, x9, #0x200
     +0xe34: ushr    v18.16b, v3.16b, #1
     +0xe38: add     v6.16b, v6.16b, v6.16b
     +0xe3c: shl     v7.16b, v7.16b, #4
     +0xe40: shl     v1.16b, v1.16b, #5
     +0xe44: shl     v3.16b, v3.16b, #7
     +0xe48: cmp     x8, #0x5c0
     +0xe4c: sub     v4.16b, v19.16b, v4.16b
     +0xe50: movi    v19.16b, #0x10
     +0xe54: sub     v2.16b, v0.16b, v2.16b
     +0xe58: sub     v6.16b, v20.16b, v6.16b
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
     +0xe94: b.ne    <mldsa87_keypair_internal+0xa90>
     +0xe98: str     xzr, [sp, #7776]
     +0xe9c: add     x8, sp, #0x1, lsl #12
     +0xea0: movi    v0.16b, #0x2
     +0xea4: movi    v5.16b, #0x20
     +0xea8: add     x8, x8, #0xe60
     +0xeac: str     q15, [sp, #336]
     +0xeb0: mov     w8, #0x5c0
     +0xeb4: add     x9, x22, #0xc00
     +0xeb8: ldr     q15, [sp, #336]
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
    +0x1274: cmp     x8, #0x620
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
    +0x12c0: b.ne    <mldsa87_keypair_internal+0xebc>
    +0x12c4: str     xzr, [sp, #7776]
    +0x12c8: add     x8, sp, #0x1, lsl #12
    +0x12cc: add     x0, sp, #0x160
    +0x12d0: add     x8, x8, #0xe60
    +0x12d4: add     x1, x22, #0x400
    +0x12d8: mov     w8, #0xa
    +0x12dc: add     x2, x22, #0x800
    +0x12e0: add     x3, x22, #0xc00
    +0x12e4: add     x4, x26, #0x20
    +0x12e8: mov     w5, #0x7
    +0x12ec: mov     w6, #0x8
    +0x12f0: mov     w7, #0x9
    +0x12f4: strb    w8, [sp]
    +0x12f8: bl      <mldsa87_poly_uniform_eta_4x>
    +0x12fc: movi    v0.16b, #0x2
    +0x1300: movi    v5.16b, #0x20
    +0x1304: add     x8, sp, #0x160
    +0x1308: ldr     q15, [sp, #336]
    +0x130c: add     x8, x8, #0x100
    +0x1310: mov     w9, #0x320
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
    +0x1694: cmp     x9, #0x380
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
    +0x16f8: b.ne    <mldsa87_keypair_internal+0x1314>
    +0x16fc: str     xzr, [sp, #7776]
    +0x1700: add     x8, sp, #0x1, lsl #12
    +0x1704: movi    v0.16b, #0x2
    +0x1708: movi    v5.16b, #0x20
    +0x170c: add     x8, x8, #0xe60
    +0x1710: ldr     q15, [sp, #336]
    +0x1714: mov     w8, #0x380
    +0x1718: add     x9, x22, #0x400
    +0x171c: ldp     s16, s1, [x9, #16]
    +0x1720: add     x10, x9, #0x30
    +0x1724: add     x11, x9, #0x34
    +0x1728: add     x13, x9, #0x50
    +0x172c: add     x14, x9, #0x54
    +0x1730: ldp     s20, s24, [x9]
    +0x1734: add     x15, x9, #0x70
    +0x1738: ld1     {v16.s}[1], [x10]
    +0x173c: ld1     {v1.s}[1], [x11]
    +0x1740: add     x10, x9, #0x20
    +0x1744: add     x16, x9, #0x74
    +0x1748: add     x11, x9, #0x40
    +0x174c: add     x12, x9, #0x60
    +0x1750: ld1     {v20.s}[1], [x10]
    +0x1754: add     x10, x9, #0x44
    +0x1758: add     x18, x9, #0xd4
    +0x175c: ld1     {v16.s}[2], [x13]
    +0x1760: ld1     {v1.s}[2], [x14]
    +0x1764: add     x13, x9, #0x24
    +0x1768: ld1     {v24.s}[1], [x13]
    +0x176c: add     x13, x9, #0xb4
    +0x1770: add     x1, x9, #0xf4
    +0x1774: ld1     {v20.s}[2], [x11]
    +0x1778: add     x0, x9, #0xc4
    +0x177c: add     x14, x9, #0xa0
    +0x1780: ld1     {v16.s}[3], [x15]
    +0x1784: ld1     {v1.s}[3], [x16]
    +0x1788: add     x17, x9, #0xc0
    +0x178c: ldp     s17, s2, [x9, #144]
    +0x1790: ld1     {v24.s}[2], [x10]
    +0x1794: add     x10, x9, #0x64
    +0x1798: ld1     {v20.s}[3], [x12]
    +0x179c: add     x15, x9, #0xe0
    +0x17a0: ldp     s28, s6, [x9, #8]
    +0x17a4: add     x16, x9, #0x120
    +0x17a8: ld1     {v2.s}[1], [x13]
    +0x17ac: ld1     {v24.s}[3], [x10]
    +0x17b0: add     x2, x9, #0x124
    +0x17b4: ldp     s21, s25, [x9, #128]
    +0x17b8: add     x13, x9, #0x140
    +0x17bc: add     x11, x9, #0x160
    +0x17c0: add     x12, x9, #0x1a0
    +0x17c4: add     x10, x9, #0x1c0
    +0x17c8: ld1     {v2.s}[2], [x18]
    +0x17cc: add     x18, x9, #0xa4
    +0x17d0: ld1     {v25.s}[1], [x18]
    +0x17d4: ld1     {v21.s}[1], [x14]
    +0x17d8: add     x18, x9, #0xe4
    +0x17dc: add     x14, x9, #0x164
    +0x17e0: ld1     {v2.s}[3], [x1]
    +0x17e4: add     x1, x9, #0x144
    +0x17e8: ldr     s3, [x9, #276]
    +0x17ec: ld1     {v25.s}[2], [x0]
    +0x17f0: add     x0, x9, #0x134
    +0x17f4: ld1     {v21.s}[2], [x17]
    +0x17f8: add     x17, x9, #0x48
    +0x17fc: ld1     {v3.s}[1], [x0]
    +0x1800: add     x0, x9, #0x28
    +0x1804: ld1     {v28.s}[1], [x0]
    +0x1808: add     x0, x9, #0x154
    +0x180c: ld1     {v25.s}[3], [x18]
    +0x1810: ld1     {v21.s}[3], [x15]
    +0x1814: add     x15, x9, #0x174
    +0x1818: ldr     s26, [x9, #260]
    +0x181c: ld1     {v3.s}[2], [x0]
    +0x1820: add     x0, x9, #0x2c
    +0x1824: ldr     s22, [x9, #256]
    +0x1828: ld1     {v6.s}[1], [x0]
    +0x182c: ld1     {v28.s}[2], [x17]
    +0x1830: add     x17, x9, #0x4c
    +0x1834: add     x18, x9, #0x68
    +0x1838: ld1     {v26.s}[1], [x2]
    +0x183c: ld1     {v22.s}[1], [x16]
    +0x1840: ld1     {v3.s}[3], [x15]
    +0x1844: add     x15, x9, #0x6c
    +0x1848: add     x16, x9, #0x1b4
    +0x184c: ld1     {v6.s}[2], [x17]
    +0x1850: ldr     s4, [x9, #404]
    +0x1854: ld1     {v28.s}[3], [x18]
    +0x1858: ld1     {v26.s}[2], [x1]
    +0x185c: ld1     {v22.s}[2], [x13]
    +0x1860: add     x13, x9, #0x1d4
    +0x1864: ld1     {v4.s}[1], [x16]
    +0x1868: add     x16, x9, #0xa8
    +0x186c: ld1     {v6.s}[3], [x15]
    +0x1870: add     x15, x9, #0x1a4
    +0x1874: ldp     s29, s7, [x9, #136]
    +0x1878: ld1     {v26.s}[3], [x14]
    +0x187c: ld1     {v4.s}[2], [x13]
    +0x1880: add     x13, x9, #0xc8
    +0x1884: ld1     {v22.s}[3], [x11]
    +0x1888: add     x11, x9, #0x1f4
    +0x188c: ldr     s27, [x9, #388]
    +0x1890: ldr     s23, [x9, #384]
    +0x1894: ld1     {v29.s}[1], [x16]
    +0x1898: add     x14, x9, #0xe8
    +0x189c: ld1     {v4.s}[3], [x11]
    +0x18a0: ld1     {v27.s}[1], [x15]
    +0x18a4: ld1     {v23.s}[1], [x12]
    +0x18a8: add     x11, x9, #0x128
    +0x18ac: add     x12, x9, #0x38
    +0x18b0: ld1     {v29.s}[2], [x13]
    +0x18b4: add     x13, x9, #0x1c4
    +0x18b8: tbl     v10.16b, {v1.16b-v4.16b}, v15.16b
    +0x18bc: ldp     s11, s1, [x9, #24]
    +0x18c0: ld1     {v27.s}[2], [x13]
    +0x18c4: ld1     {v23.s}[2], [x10]
    +0x18c8: add     x10, x9, #0x1e4
    +0x18cc: ld1     {v29.s}[3], [x14]
    +0x18d0: add     x14, x9, #0x78
    +0x18d4: add     x13, x9, #0x1a8
    +0x18d8: ldr     s30, [x9, #264]
    +0x18dc: ld1     {v11.s}[1], [x12]
    +0x18e0: add     x12, x9, #0x168
    +0x18e4: ld1     {v27.s}[3], [x10]
    +0x18e8: add     x10, x9, #0x58
    +0x18ec: ld1     {v30.s}[1], [x11]
    +0x18f0: add     x11, x9, #0x3c
    +0x18f4: ld1     {v1.s}[1], [x11]
    +0x18f8: ld1     {v11.s}[2], [x10]
    +0x18fc: add     x10, x9, #0x5c
    +0x1900: add     x11, x9, #0x148
    +0x1904: tbl     v24.16b, {v24.16b-v27.16b}, v15.16b
    +0x1908: ld1     {v30.s}[2], [x11]
    +0x190c: add     x11, x9, #0xac
    +0x1910: ld1     {v1.s}[2], [x10]
    +0x1914: ld1     {v7.s}[1], [x11]
    +0x1918: add     x11, x9, #0x7c
    +0x191c: ld1     {v11.s}[3], [x14]
    +0x1920: add     x14, x9, #0xb8
    +0x1924: add     x10, x9, #0x1c8
    +0x1928: ld1     {v30.s}[3], [x12]
    +0x192c: add     x12, x9, #0xcc
    +0x1930: ld1     {v1.s}[3], [x11]
    +0x1934: ld1     {v7.s}[2], [x12]
    +0x1938: add     x12, x9, #0xb0
    +0x193c: ldp     s12, s2, [x9, #152]
    +0x1940: ld1     {v17.s}[1], [x12]
    +0x1944: add     x12, x9, #0xd8
    +0x1948: add     x11, x9, #0xec
    +0x194c: ldr     s31, [x9, #392]
    +0x1950: ld1     {v7.s}[3], [x11]
    +0x1954: add     x11, x9, #0xd0
    +0x1958: ld1     {v12.s}[1], [x14]
    +0x195c: add     x14, x9, #0xbc
    +0x1960: ld1     {v17.s}[2], [x11]
    +0x1964: ld1     {v2.s}[1], [x14]
    +0x1968: add     x11, x9, #0xf8
    +0x196c: ldr     s8, [x9, #268]
    +0x1970: ld1     {v31.s}[1], [x13]
    +0x1974: add     x13, x9, #0x12c
    +0x1978: add     x14, x9, #0x15c
    +0x197c: ld1     {v12.s}[2], [x12]
    +0x1980: add     x12, x9, #0xdc
    +0x1984: ld1     {v8.s}[1], [x13]
    +0x1988: ld1     {v2.s}[2], [x12]
    +0x198c: add     x12, x9, #0xfc
    +0x1990: add     x13, x9, #0x13c
    +0x1994: ld1     {v31.s}[2], [x10]
    +0x1998: add     x10, x9, #0x1d0
    +0x199c: ld1     {v12.s}[3], [x11]
    +0x19a0: add     x11, x9, #0xf0
    +0x19a4: ldr     s13, [x9, #280]
    +0x19a8: ld1     {v17.s}[3], [x11]
    +0x19ac: add     x11, x9, #0x138
    +0x19b0: ldr     s18, [x9, #272]
    +0x19b4: ld1     {v2.s}[3], [x12]
    +0x19b8: add     x12, x9, #0x130
    +0x19bc: ld1     {v13.s}[1], [x11]
    +0x19c0: ldr     s3, [x9, #284]
    +0x19c4: add     x11, x9, #0x14c
    +0x19c8: ld1     {v18.s}[1], [x12]
    +0x19cc: add     x12, x9, #0x158
    +0x19d0: ld1     {v8.s}[2], [x11]
    +0x19d4: ld1     {v3.s}[1], [x13]
    +0x19d8: add     x13, x9, #0x150
    +0x19dc: add     x11, x9, #0x16c
    +0x19e0: ld1     {v13.s}[2], [x12]
    +0x19e4: add     x12, x9, #0x1ac
    +0x19e8: ld1     {v18.s}[2], [x13]
    +0x19ec: add     x13, x9, #0x178
    +0x19f0: ld1     {v8.s}[3], [x11]
    +0x19f4: ld1     {v3.s}[2], [x14]
    +0x19f8: add     x11, x9, #0x170
    +0x19fc: ldr     s9, [x9, #396]
    +0x1a00: ld1     {v13.s}[3], [x13]
    +0x1a04: add     x13, x9, #0x17c
    +0x1a08: ldr     s14, [x9, #408]
    +0x1a0c: ld1     {v18.s}[3], [x11]
    +0x1a10: add     x11, x9, #0x1b8
    +0x1a14: ldr     s19, [x9, #400]
    +0x1a18: ld1     {v3.s}[3], [x13]
    +0x1a1c: ld1     {v9.s}[1], [x12]
    +0x1a20: ld1     {v14.s}[1], [x11]
    +0x1a24: add     x11, x9, #0x1b0
    +0x1a28: ldr     s4, [x9, #412]
    +0x1a2c: ld1     {v19.s}[1], [x11]
    +0x1a30: add     x11, x9, #0x1d8
    +0x1a34: add     x12, x9, #0x1bc
    +0x1a38: ld1     {v4.s}[1], [x12]
    +0x1a3c: add     x13, x9, #0x1cc
    +0x1a40: add     x12, x9, #0x1e8
    +0x1a44: ld1     {v14.s}[2], [x11]
    +0x1a48: ld1     {v9.s}[2], [x13]
    +0x1a4c: add     x11, x9, #0x1dc
    +0x1a50: ld1     {v19.s}[2], [x10]
    +0x1a54: add     x10, x9, #0x1f8
    +0x1a58: ld1     {v31.s}[3], [x12]
    +0x1a5c: ld1     {v4.s}[2], [x11]
    +0x1a60: add     x11, x9, #0x1f0
    +0x1a64: ld1     {v14.s}[3], [x10]
    +0x1a68: add     x10, x9, #0x1ec
    +0x1a6c: ld1     {v9.s}[3], [x10]
    +0x1a70: ld1     {v19.s}[3], [x11]
    +0x1a74: add     x10, x9, #0x1fc
    +0x1a78: ld1     {v4.s}[3], [x10]
    +0x1a7c: add     x11, x9, #0x1e0
    +0x1a80: tbl     v25.16b, {v28.16b-v31.16b}, v15.16b
    +0x1a84: tbl     v11.16b, {v11.16b-v14.16b}, v15.16b
    +0x1a88: ld1     {v23.s}[3], [x11]
    +0x1a8c: add     x10, x19, x8
    +0x1a90: tbl     v6.16b, {v6.16b-v9.16b}, v15.16b
    +0x1a94: tbl     v7.16b, {v16.16b-v19.16b}, v15.16b
    +0x1a98: movi    v19.16b, #0x8
    +0x1a9c: tbl     v1.16b, {v1.16b-v4.16b}, v15.16b
    +0x1aa0: sub     v3.16b, v0.16b, v10.16b
    +0x1aa4: shl     v17.16b, v24.16b, #3
    +0x1aa8: tbl     v2.16b, {v20.16b-v23.16b}, v15.16b
    +0x1aac: movi    v20.16b, #0x4
    +0x1ab0: sub     v16.16b, v0.16b, v25.16b
    +0x1ab4: shl     v4.16b, v11.16b, #2
    +0x1ab8: add     x8, x8, #0x30
    +0x1abc: add     x9, x9, #0x200
    +0x1ac0: ushr    v18.16b, v3.16b, #1
    +0x1ac4: add     v6.16b, v6.16b, v6.16b
    +0x1ac8: shl     v7.16b, v7.16b, #4
    +0x1acc: shl     v1.16b, v1.16b, #5
    +0x1ad0: shl     v3.16b, v3.16b, #7
    +0x1ad4: cmp     x8, #0x3e0
    +0x1ad8: sub     v4.16b, v19.16b, v4.16b
    +0x1adc: movi    v19.16b, #0x10
    +0x1ae0: sub     v2.16b, v0.16b, v2.16b
    +0x1ae4: sub     v6.16b, v20.16b, v6.16b
    +0x1ae8: sub     v7.16b, v5.16b, v7.16b
    +0x1aec: orr     v4.16b, v4.16b, v18.16b
    +0x1af0: movi    v18.16b, #0x40
    +0x1af4: sub     v17.16b, v19.16b, v17.16b
    +0x1af8: ushr    v19.16b, v16.16b, #2
    +0x1afc: shl     v16.16b, v16.16b, #6
    +0x1b00: orr     v3.16b, v7.16b, v3.16b
    +0x1b04: sub     v1.16b, v18.16b, v1.16b
    +0x1b08: orr     v2.16b, v17.16b, v2.16b
    +0x1b0c: orr     v6.16b, v6.16b, v19.16b
    +0x1b10: orr     v19.16b, v4.16b, v1.16b
    +0x1b14: orr     v17.16b, v2.16b, v16.16b
    +0x1b18: orr     v18.16b, v6.16b, v3.16b
    +0x1b1c: st3     {v17.16b-v19.16b}, [x10]
    +0x1b20: b.ne    <mldsa87_keypair_internal+0x171c>
    +0x1b24: str     xzr, [sp, #7776]
    +0x1b28: add     x8, sp, #0x1, lsl #12
    +0x1b2c: movi    v0.16b, #0x2
    +0x1b30: movi    v5.16b, #0x20
    +0x1b34: add     x8, x8, #0xe60
    +0x1b38: ldr     q15, [sp, #336]
    +0x1b3c: mov     w8, #0x3e0
    +0x1b40: add     x9, x22, #0x800
    +0x1b44: ldp     s16, s1, [x9, #16]
    +0x1b48: add     x10, x9, #0x30
    +0x1b4c: add     x11, x9, #0x34
    +0x1b50: add     x13, x9, #0x50
    +0x1b54: add     x14, x9, #0x54
    +0x1b58: ldp     s20, s24, [x9]
    +0x1b5c: add     x15, x9, #0x70
    +0x1b60: ld1     {v16.s}[1], [x10]
    +0x1b64: ld1     {v1.s}[1], [x11]
    +0x1b68: add     x10, x9, #0x20
    +0x1b6c: add     x16, x9, #0x74
    +0x1b70: add     x11, x9, #0x40
    +0x1b74: add     x12, x9, #0x60
    +0x1b78: ld1     {v20.s}[1], [x10]
    +0x1b7c: add     x10, x9, #0x44
    +0x1b80: add     x18, x9, #0xd4
    +0x1b84: ld1     {v16.s}[2], [x13]
    +0x1b88: ld1     {v1.s}[2], [x14]
    +0x1b8c: add     x13, x9, #0x24
    +0x1b90: ld1     {v24.s}[1], [x13]
    +0x1b94: add     x13, x9, #0xb4
    +0x1b98: add     x1, x9, #0xf4
    +0x1b9c: ld1     {v20.s}[2], [x11]
    +0x1ba0: add     x0, x9, #0xc4
    +0x1ba4: add     x14, x9, #0xa0
    +0x1ba8: ld1     {v16.s}[3], [x15]
    +0x1bac: ld1     {v1.s}[3], [x16]
    +0x1bb0: add     x17, x9, #0xc0
    +0x1bb4: ldp     s17, s2, [x9, #144]
    +0x1bb8: ld1     {v24.s}[2], [x10]
    +0x1bbc: add     x10, x9, #0x64
    +0x1bc0: ld1     {v20.s}[3], [x12]
    +0x1bc4: add     x15, x9, #0xe0
    +0x1bc8: ldp     s28, s6, [x9, #8]
    +0x1bcc: add     x16, x9, #0x120
    +0x1bd0: ld1     {v2.s}[1], [x13]
    +0x1bd4: ld1     {v24.s}[3], [x10]
    +0x1bd8: add     x2, x9, #0x124
    +0x1bdc: ldp     s21, s25, [x9, #128]
    +0x1be0: add     x13, x9, #0x140
    +0x1be4: add     x11, x9, #0x160
    +0x1be8: add     x12, x9, #0x1a0
    +0x1bec: add     x10, x9, #0x1c0
    +0x1bf0: ld1     {v2.s}[2], [x18]
    +0x1bf4: add     x18, x9, #0xa4
    +0x1bf8: ld1     {v25.s}[1], [x18]
    +0x1bfc: ld1     {v21.s}[1], [x14]
    +0x1c00: add     x18, x9, #0xe4
    +0x1c04: add     x14, x9, #0x164
    +0x1c08: ld1     {v2.s}[3], [x1]
    +0x1c0c: add     x1, x9, #0x144
    +0x1c10: ldr     s3, [x9, #276]
    +0x1c14: ld1     {v25.s}[2], [x0]
    +0x1c18: add     x0, x9, #0x134
    +0x1c1c: ld1     {v21.s}[2], [x17]
    +0x1c20: add     x17, x9, #0x48
    +0x1c24: ld1     {v3.s}[1], [x0]
    +0x1c28: add     x0, x9, #0x28
    +0x1c2c: ld1     {v28.s}[1], [x0]
    +0x1c30: add     x0, x9, #0x154
    +0x1c34: ld1     {v25.s}[3], [x18]
    +0x1c38: ld1     {v21.s}[3], [x15]
    +0x1c3c: add     x15, x9, #0x174
    +0x1c40: ldr     s26, [x9, #260]
    +0x1c44: ld1     {v3.s}[2], [x0]
    +0x1c48: add     x0, x9, #0x2c
    +0x1c4c: ldr     s22, [x9, #256]
    +0x1c50: ld1     {v6.s}[1], [x0]
    +0x1c54: ld1     {v28.s}[2], [x17]
    +0x1c58: add     x17, x9, #0x4c
    +0x1c5c: add     x18, x9, #0x68
    +0x1c60: ld1     {v26.s}[1], [x2]
    +0x1c64: ld1     {v22.s}[1], [x16]
    +0x1c68: ld1     {v3.s}[3], [x15]
    +0x1c6c: add     x15, x9, #0x6c
    +0x1c70: add     x16, x9, #0x1b4
    +0x1c74: ld1     {v6.s}[2], [x17]
    +0x1c78: ldr     s4, [x9, #404]
    +0x1c7c: ld1     {v28.s}[3], [x18]
    +0x1c80: ld1     {v26.s}[2], [x1]
    +0x1c84: ld1     {v22.s}[2], [x13]
    +0x1c88: add     x13, x9, #0x1d4
    +0x1c8c: ld1     {v4.s}[1], [x16]
    +0x1c90: add     x16, x9, #0xa8
    +0x1c94: ld1     {v6.s}[3], [x15]
    +0x1c98: add     x15, x9, #0x1a4
    +0x1c9c: ldp     s29, s7, [x9, #136]
    +0x1ca0: ld1     {v26.s}[3], [x14]
    +0x1ca4: ld1     {v4.s}[2], [x13]
    +0x1ca8: add     x13, x9, #0xc8
    +0x1cac: ld1     {v22.s}[3], [x11]
    +0x1cb0: add     x11, x9, #0x1f4
    +0x1cb4: ldr     s27, [x9, #388]
    +0x1cb8: ldr     s23, [x9, #384]
    +0x1cbc: ld1     {v29.s}[1], [x16]
    +0x1cc0: add     x14, x9, #0xe8
    +0x1cc4: ld1     {v4.s}[3], [x11]
    +0x1cc8: ld1     {v27.s}[1], [x15]
    +0x1ccc: ld1     {v23.s}[1], [x12]
    +0x1cd0: add     x11, x9, #0x128
    +0x1cd4: add     x12, x9, #0x38
    +0x1cd8: ld1     {v29.s}[2], [x13]
    +0x1cdc: add     x13, x9, #0x1c4
    +0x1ce0: tbl     v10.16b, {v1.16b-v4.16b}, v15.16b
    +0x1ce4: ldp     s11, s1, [x9, #24]
    +0x1ce8: ld1     {v27.s}[2], [x13]
    +0x1cec: ld1     {v23.s}[2], [x10]
    +0x1cf0: add     x10, x9, #0x1e4
    +0x1cf4: ld1     {v29.s}[3], [x14]
    +0x1cf8: add     x14, x9, #0x78
    +0x1cfc: add     x13, x9, #0x1a8
    +0x1d00: ldr     s30, [x9, #264]
    +0x1d04: ld1     {v11.s}[1], [x12]
    +0x1d08: add     x12, x9, #0x168
    +0x1d0c: ld1     {v27.s}[3], [x10]
    +0x1d10: add     x10, x9, #0x58
    +0x1d14: ld1     {v30.s}[1], [x11]
    +0x1d18: add     x11, x9, #0x3c
    +0x1d1c: ld1     {v1.s}[1], [x11]
    +0x1d20: ld1     {v11.s}[2], [x10]
    +0x1d24: add     x10, x9, #0x5c
    +0x1d28: add     x11, x9, #0x148
    +0x1d2c: tbl     v24.16b, {v24.16b-v27.16b}, v15.16b
    +0x1d30: ld1     {v30.s}[2], [x11]
    +0x1d34: add     x11, x9, #0xac
    +0x1d38: ld1     {v1.s}[2], [x10]
    +0x1d3c: ld1     {v7.s}[1], [x11]
    +0x1d40: add     x11, x9, #0x7c
    +0x1d44: ld1     {v11.s}[3], [x14]
    +0x1d48: add     x14, x9, #0xb8
    +0x1d4c: add     x10, x9, #0x1c8
    +0x1d50: ld1     {v30.s}[3], [x12]
    +0x1d54: add     x12, x9, #0xcc
    +0x1d58: ld1     {v1.s}[3], [x11]
    +0x1d5c: ld1     {v7.s}[2], [x12]
    +0x1d60: add     x12, x9, #0xb0
    +0x1d64: ldp     s12, s2, [x9, #152]
    +0x1d68: ld1     {v17.s}[1], [x12]
    +0x1d6c: add     x12, x9, #0xd8
    +0x1d70: add     x11, x9, #0xec
    +0x1d74: ldr     s31, [x9, #392]
    +0x1d78: ld1     {v7.s}[3], [x11]
    +0x1d7c: add     x11, x9, #0xd0
    +0x1d80: ld1     {v12.s}[1], [x14]
    +0x1d84: add     x14, x9, #0xbc
    +0x1d88: ld1     {v17.s}[2], [x11]
    +0x1d8c: ld1     {v2.s}[1], [x14]
    +0x1d90: add     x11, x9, #0xf8
    +0x1d94: ldr     s8, [x9, #268]
    +0x1d98: ld1     {v31.s}[1], [x13]
    +0x1d9c: add     x13, x9, #0x12c
    +0x1da0: add     x14, x9, #0x15c
    +0x1da4: ld1     {v12.s}[2], [x12]
    +0x1da8: add     x12, x9, #0xdc
    +0x1dac: ld1     {v8.s}[1], [x13]
    +0x1db0: ld1     {v2.s}[2], [x12]
    +0x1db4: add     x12, x9, #0xfc
    +0x1db8: add     x13, x9, #0x13c
    +0x1dbc: ld1     {v31.s}[2], [x10]
    +0x1dc0: add     x10, x9, #0x1d0
    +0x1dc4: ld1     {v12.s}[3], [x11]
    +0x1dc8: add     x11, x9, #0xf0
    +0x1dcc: ldr     s13, [x9, #280]
    +0x1dd0: ld1     {v17.s}[3], [x11]
    +0x1dd4: add     x11, x9, #0x138
    +0x1dd8: ldr     s18, [x9, #272]
    +0x1ddc: ld1     {v2.s}[3], [x12]
    +0x1de0: add     x12, x9, #0x130
    +0x1de4: ld1     {v13.s}[1], [x11]
    +0x1de8: ldr     s3, [x9, #284]
    +0x1dec: add     x11, x9, #0x14c
    +0x1df0: ld1     {v18.s}[1], [x12]
    +0x1df4: add     x12, x9, #0x158
    +0x1df8: ld1     {v8.s}[2], [x11]
    +0x1dfc: ld1     {v3.s}[1], [x13]
    +0x1e00: add     x13, x9, #0x150
    +0x1e04: add     x11, x9, #0x16c
    +0x1e08: ld1     {v13.s}[2], [x12]
    +0x1e0c: add     x12, x9, #0x1ac
    +0x1e10: ld1     {v18.s}[2], [x13]
    +0x1e14: add     x13, x9, #0x178
    +0x1e18: ld1     {v8.s}[3], [x11]
    +0x1e1c: ld1     {v3.s}[2], [x14]
    +0x1e20: add     x11, x9, #0x170
    +0x1e24: ldr     s9, [x9, #396]
    +0x1e28: ld1     {v13.s}[3], [x13]
    +0x1e2c: add     x13, x9, #0x17c
    +0x1e30: ldr     s14, [x9, #408]
    +0x1e34: ld1     {v18.s}[3], [x11]
    +0x1e38: add     x11, x9, #0x1b8
    +0x1e3c: ldr     s19, [x9, #400]
    +0x1e40: ld1     {v3.s}[3], [x13]
    +0x1e44: ld1     {v9.s}[1], [x12]
    +0x1e48: ld1     {v14.s}[1], [x11]
    +0x1e4c: add     x11, x9, #0x1b0
    +0x1e50: ldr     s4, [x9, #412]
    +0x1e54: ld1     {v19.s}[1], [x11]
    +0x1e58: add     x11, x9, #0x1d8
    +0x1e5c: add     x12, x9, #0x1bc
    +0x1e60: ld1     {v4.s}[1], [x12]
    +0x1e64: add     x13, x9, #0x1cc
    +0x1e68: add     x12, x9, #0x1e8
    +0x1e6c: ld1     {v14.s}[2], [x11]
    +0x1e70: ld1     {v9.s}[2], [x13]
    +0x1e74: add     x11, x9, #0x1dc
    +0x1e78: ld1     {v19.s}[2], [x10]
    +0x1e7c: add     x10, x9, #0x1f8
    +0x1e80: ld1     {v31.s}[3], [x12]
    +0x1e84: ld1     {v4.s}[2], [x11]
    +0x1e88: add     x11, x9, #0x1f0
    +0x1e8c: ld1     {v14.s}[3], [x10]
    +0x1e90: add     x10, x9, #0x1ec
    +0x1e94: ld1     {v9.s}[3], [x10]
    +0x1e98: ld1     {v19.s}[3], [x11]
    +0x1e9c: add     x10, x9, #0x1fc
    +0x1ea0: ld1     {v4.s}[3], [x10]
    +0x1ea4: add     x11, x9, #0x1e0
    +0x1ea8: tbl     v25.16b, {v28.16b-v31.16b}, v15.16b
    +0x1eac: tbl     v11.16b, {v11.16b-v14.16b}, v15.16b
    +0x1eb0: ld1     {v23.s}[3], [x11]
    +0x1eb4: add     x10, x19, x8
    +0x1eb8: tbl     v6.16b, {v6.16b-v9.16b}, v15.16b
    +0x1ebc: tbl     v7.16b, {v16.16b-v19.16b}, v15.16b
    +0x1ec0: movi    v19.16b, #0x8
    +0x1ec4: tbl     v1.16b, {v1.16b-v4.16b}, v15.16b
    +0x1ec8: sub     v3.16b, v0.16b, v10.16b
    +0x1ecc: shl     v17.16b, v24.16b, #3
    +0x1ed0: tbl     v2.16b, {v20.16b-v23.16b}, v15.16b
    +0x1ed4: movi    v20.16b, #0x4
    +0x1ed8: sub     v16.16b, v0.16b, v25.16b
    +0x1edc: shl     v4.16b, v11.16b, #2
    +0x1ee0: add     x8, x8, #0x30
    +0x1ee4: add     x9, x9, #0x200
    +0x1ee8: ushr    v18.16b, v3.16b, #1
    +0x1eec: add     v6.16b, v6.16b, v6.16b
    +0x1ef0: shl     v7.16b, v7.16b, #4
    +0x1ef4: shl     v1.16b, v1.16b, #5
    +0x1ef8: shl     v3.16b, v3.16b, #7
    +0x1efc: cmp     x8, #0x440
    +0x1f00: sub     v4.16b, v19.16b, v4.16b
    +0x1f04: movi    v19.16b, #0x10
    +0x1f08: sub     v2.16b, v0.16b, v2.16b
    +0x1f0c: sub     v6.16b, v20.16b, v6.16b
    +0x1f10: sub     v7.16b, v5.16b, v7.16b
    +0x1f14: orr     v4.16b, v4.16b, v18.16b
    +0x1f18: movi    v18.16b, #0x40
    +0x1f1c: sub     v17.16b, v19.16b, v17.16b
    +0x1f20: ushr    v19.16b, v16.16b, #2
    +0x1f24: shl     v16.16b, v16.16b, #6
    +0x1f28: orr     v3.16b, v7.16b, v3.16b
    +0x1f2c: sub     v1.16b, v18.16b, v1.16b
    +0x1f30: orr     v2.16b, v17.16b, v2.16b
    +0x1f34: orr     v6.16b, v6.16b, v19.16b
    +0x1f38: orr     v19.16b, v4.16b, v1.16b
    +0x1f3c: orr     v17.16b, v2.16b, v16.16b
    +0x1f40: orr     v18.16b, v6.16b, v3.16b
    +0x1f44: st3     {v17.16b-v19.16b}, [x10]
    +0x1f48: b.ne    <mldsa87_keypair_internal+0x1b44>
    +0x1f4c: str     xzr, [sp, #7776]
    +0x1f50: add     x8, sp, #0x1, lsl #12
    +0x1f54: movi    v0.16b, #0x2
    +0x1f58: movi    v5.16b, #0x20
    +0x1f5c: add     x8, x8, #0xe60
    +0x1f60: ldr     q15, [sp, #336]
    +0x1f64: mov     w8, #0x440
    +0x1f68: add     x9, x22, #0xc00
    +0x1f6c: ldp     s16, s1, [x9, #16]
    +0x1f70: add     x10, x9, #0x30
    +0x1f74: add     x11, x9, #0x34
    +0x1f78: add     x13, x9, #0x50
    +0x1f7c: add     x14, x9, #0x54
    +0x1f80: ldp     s20, s24, [x9]
    +0x1f84: add     x15, x9, #0x70
    +0x1f88: ld1     {v16.s}[1], [x10]
    +0x1f8c: ld1     {v1.s}[1], [x11]
    +0x1f90: add     x10, x9, #0x20
    +0x1f94: add     x16, x9, #0x74
    +0x1f98: add     x11, x9, #0x40
    +0x1f9c: add     x12, x9, #0x60
    +0x1fa0: ld1     {v20.s}[1], [x10]
    +0x1fa4: add     x10, x9, #0x44
    +0x1fa8: add     x18, x9, #0xd4
    +0x1fac: ld1     {v16.s}[2], [x13]
    +0x1fb0: ld1     {v1.s}[2], [x14]
    +0x1fb4: add     x13, x9, #0x24
    +0x1fb8: ld1     {v24.s}[1], [x13]
    +0x1fbc: add     x13, x9, #0xb4
    +0x1fc0: add     x1, x9, #0xf4
    +0x1fc4: ld1     {v20.s}[2], [x11]
    +0x1fc8: add     x0, x9, #0xc4
    +0x1fcc: add     x14, x9, #0xa0
    +0x1fd0: ld1     {v16.s}[3], [x15]
    +0x1fd4: ld1     {v1.s}[3], [x16]
    +0x1fd8: add     x17, x9, #0xc0
    +0x1fdc: ldp     s17, s2, [x9, #144]
    +0x1fe0: ld1     {v24.s}[2], [x10]
    +0x1fe4: add     x10, x9, #0x64
    +0x1fe8: ld1     {v20.s}[3], [x12]
    +0x1fec: add     x15, x9, #0xe0
    +0x1ff0: ldp     s28, s6, [x9, #8]
    +0x1ff4: add     x16, x9, #0x120
    +0x1ff8: ld1     {v2.s}[1], [x13]
    +0x1ffc: ld1     {v24.s}[3], [x10]
    +0x2000: add     x2, x9, #0x124
    +0x2004: ldp     s21, s25, [x9, #128]
    +0x2008: add     x13, x9, #0x140
    +0x200c: add     x11, x9, #0x160
    +0x2010: add     x12, x9, #0x1a0
    +0x2014: add     x10, x9, #0x1c0
    +0x2018: ld1     {v2.s}[2], [x18]
    +0x201c: add     x18, x9, #0xa4
    +0x2020: ld1     {v25.s}[1], [x18]
    +0x2024: ld1     {v21.s}[1], [x14]
    +0x2028: add     x18, x9, #0xe4
    +0x202c: add     x14, x9, #0x164
    +0x2030: ld1     {v2.s}[3], [x1]
    +0x2034: add     x1, x9, #0x144
    +0x2038: ldr     s3, [x9, #276]
    +0x203c: ld1     {v25.s}[2], [x0]
    +0x2040: add     x0, x9, #0x134
    +0x2044: ld1     {v21.s}[2], [x17]
    +0x2048: add     x17, x9, #0x48
    +0x204c: ld1     {v3.s}[1], [x0]
    +0x2050: add     x0, x9, #0x28
    +0x2054: ld1     {v28.s}[1], [x0]
    +0x2058: add     x0, x9, #0x154
    +0x205c: ld1     {v25.s}[3], [x18]
    +0x2060: ld1     {v21.s}[3], [x15]
    +0x2064: add     x15, x9, #0x174
    +0x2068: ldr     s26, [x9, #260]
    +0x206c: ld1     {v3.s}[2], [x0]
    +0x2070: add     x0, x9, #0x2c
    +0x2074: ldr     s22, [x9, #256]
    +0x2078: ld1     {v6.s}[1], [x0]
    +0x207c: ld1     {v28.s}[2], [x17]
    +0x2080: add     x17, x9, #0x4c
    +0x2084: add     x18, x9, #0x68
    +0x2088: ld1     {v26.s}[1], [x2]
    +0x208c: ld1     {v22.s}[1], [x16]
    +0x2090: ld1     {v3.s}[3], [x15]
    +0x2094: add     x15, x9, #0x6c
    +0x2098: add     x16, x9, #0x1b4
    +0x209c: ld1     {v6.s}[2], [x17]
    +0x20a0: ldr     s4, [x9, #404]
    +0x20a4: ld1     {v28.s}[3], [x18]
    +0x20a8: ld1     {v26.s}[2], [x1]
    +0x20ac: ld1     {v22.s}[2], [x13]
    +0x20b0: add     x13, x9, #0x1d4
    +0x20b4: ld1     {v4.s}[1], [x16]
    +0x20b8: add     x16, x9, #0xa8
    +0x20bc: ld1     {v6.s}[3], [x15]
    +0x20c0: add     x15, x9, #0x1a4
    +0x20c4: ldp     s29, s7, [x9, #136]
    +0x20c8: ld1     {v26.s}[3], [x14]
    +0x20cc: ld1     {v4.s}[2], [x13]
    +0x20d0: add     x13, x9, #0xc8
    +0x20d4: ld1     {v22.s}[3], [x11]
    +0x20d8: add     x11, x9, #0x1f4
    +0x20dc: ldr     s27, [x9, #388]
    +0x20e0: ldr     s23, [x9, #384]
    +0x20e4: ld1     {v29.s}[1], [x16]
    +0x20e8: add     x14, x9, #0xe8
    +0x20ec: ld1     {v4.s}[3], [x11]
    +0x20f0: ld1     {v27.s}[1], [x15]
    +0x20f4: ld1     {v23.s}[1], [x12]
    +0x20f8: add     x11, x9, #0x128
    +0x20fc: add     x12, x9, #0x38
    +0x2100: ld1     {v29.s}[2], [x13]
    +0x2104: add     x13, x9, #0x1c4
    +0x2108: tbl     v10.16b, {v1.16b-v4.16b}, v15.16b
    +0x210c: ldp     s11, s1, [x9, #24]
    +0x2110: ld1     {v27.s}[2], [x13]
    +0x2114: ld1     {v23.s}[2], [x10]
    +0x2118: add     x10, x9, #0x1e4
    +0x211c: ld1     {v29.s}[3], [x14]
    +0x2120: add     x14, x9, #0x78
    +0x2124: add     x13, x9, #0x1a8
    +0x2128: ldr     s30, [x9, #264]
    +0x212c: ld1     {v11.s}[1], [x12]
    +0x2130: add     x12, x9, #0x168
    +0x2134: ld1     {v27.s}[3], [x10]
    +0x2138: add     x10, x9, #0x58
    +0x213c: ld1     {v30.s}[1], [x11]
    +0x2140: add     x11, x9, #0x3c
    +0x2144: ld1     {v1.s}[1], [x11]
    +0x2148: ld1     {v11.s}[2], [x10]
    +0x214c: add     x10, x9, #0x5c
    +0x2150: add     x11, x9, #0x148
    +0x2154: tbl     v24.16b, {v24.16b-v27.16b}, v15.16b
    +0x2158: ld1     {v30.s}[2], [x11]
    +0x215c: add     x11, x9, #0xac
    +0x2160: ld1     {v1.s}[2], [x10]
    +0x2164: ld1     {v7.s}[1], [x11]
    +0x2168: add     x11, x9, #0x7c
    +0x216c: ld1     {v11.s}[3], [x14]
    +0x2170: add     x14, x9, #0xb8
    +0x2174: add     x10, x9, #0x1c8
    +0x2178: ld1     {v30.s}[3], [x12]
    +0x217c: add     x12, x9, #0xcc
    +0x2180: ld1     {v1.s}[3], [x11]
    +0x2184: ld1     {v7.s}[2], [x12]
    +0x2188: add     x12, x9, #0xb0
    +0x218c: ldp     s12, s2, [x9, #152]
    +0x2190: ld1     {v17.s}[1], [x12]
    +0x2194: add     x12, x9, #0xd8
    +0x2198: add     x11, x9, #0xec
    +0x219c: ldr     s31, [x9, #392]
    +0x21a0: ld1     {v7.s}[3], [x11]
    +0x21a4: add     x11, x9, #0xd0
    +0x21a8: ld1     {v12.s}[1], [x14]
    +0x21ac: add     x14, x9, #0xbc
    +0x21b0: ld1     {v17.s}[2], [x11]
    +0x21b4: ld1     {v2.s}[1], [x14]
    +0x21b8: add     x11, x9, #0xf8
    +0x21bc: ldr     s8, [x9, #268]
    +0x21c0: ld1     {v31.s}[1], [x13]
    +0x21c4: add     x13, x9, #0x12c
    +0x21c8: add     x14, x9, #0x15c
    +0x21cc: ld1     {v12.s}[2], [x12]
    +0x21d0: add     x12, x9, #0xdc
    +0x21d4: ld1     {v8.s}[1], [x13]
    +0x21d8: ld1     {v2.s}[2], [x12]
    +0x21dc: add     x12, x9, #0xfc
    +0x21e0: add     x13, x9, #0x13c
    +0x21e4: ld1     {v31.s}[2], [x10]
    +0x21e8: add     x10, x9, #0x1d0
    +0x21ec: ld1     {v12.s}[3], [x11]
    +0x21f0: add     x11, x9, #0xf0
    +0x21f4: ldr     s13, [x9, #280]
    +0x21f8: ld1     {v17.s}[3], [x11]
    +0x21fc: add     x11, x9, #0x138
    +0x2200: ldr     s18, [x9, #272]
    +0x2204: ld1     {v2.s}[3], [x12]
    +0x2208: add     x12, x9, #0x130
    +0x220c: ld1     {v13.s}[1], [x11]
    +0x2210: ldr     s3, [x9, #284]
    +0x2214: add     x11, x9, #0x14c
    +0x2218: ld1     {v18.s}[1], [x12]
    +0x221c: add     x12, x9, #0x158
    +0x2220: ld1     {v8.s}[2], [x11]
    +0x2224: ld1     {v3.s}[1], [x13]
    +0x2228: add     x13, x9, #0x150
    +0x222c: add     x11, x9, #0x16c
    +0x2230: ld1     {v13.s}[2], [x12]
    +0x2234: add     x12, x9, #0x1ac
    +0x2238: ld1     {v18.s}[2], [x13]
    +0x223c: add     x13, x9, #0x178
    +0x2240: ld1     {v8.s}[3], [x11]
    +0x2244: ld1     {v3.s}[2], [x14]
    +0x2248: add     x11, x9, #0x170
    +0x224c: ldr     s9, [x9, #396]
    +0x2250: ld1     {v13.s}[3], [x13]
    +0x2254: add     x13, x9, #0x17c
    +0x2258: ldr     s14, [x9, #408]
    +0x225c: ld1     {v18.s}[3], [x11]
    +0x2260: add     x11, x9, #0x1b8
    +0x2264: ldr     s19, [x9, #400]
    +0x2268: ld1     {v3.s}[3], [x13]
    +0x226c: ld1     {v9.s}[1], [x12]
    +0x2270: ld1     {v14.s}[1], [x11]
    +0x2274: add     x11, x9, #0x1b0
    +0x2278: ldr     s4, [x9, #412]
    +0x227c: ld1     {v19.s}[1], [x11]
    +0x2280: add     x11, x9, #0x1d8
    +0x2284: add     x12, x9, #0x1bc
    +0x2288: ld1     {v4.s}[1], [x12]
    +0x228c: add     x13, x9, #0x1cc
    +0x2290: add     x12, x9, #0x1e8
    +0x2294: ld1     {v14.s}[2], [x11]
    +0x2298: ld1     {v9.s}[2], [x13]
    +0x229c: add     x11, x9, #0x1dc
    +0x22a0: ld1     {v19.s}[2], [x10]
    +0x22a4: add     x10, x9, #0x1f8
    +0x22a8: ld1     {v31.s}[3], [x12]
    +0x22ac: ld1     {v4.s}[2], [x11]
    +0x22b0: add     x11, x9, #0x1f0
    +0x22b4: ld1     {v14.s}[3], [x10]
    +0x22b8: add     x10, x9, #0x1ec
    +0x22bc: ld1     {v9.s}[3], [x10]
    +0x22c0: ld1     {v19.s}[3], [x11]
    +0x22c4: add     x10, x9, #0x1fc
    +0x22c8: ld1     {v4.s}[3], [x10]
    +0x22cc: add     x11, x9, #0x1e0
    +0x22d0: tbl     v25.16b, {v28.16b-v31.16b}, v15.16b
    +0x22d4: tbl     v11.16b, {v11.16b-v14.16b}, v15.16b
    +0x22d8: ld1     {v23.s}[3], [x11]
    +0x22dc: add     x10, x19, x8
    +0x22e0: tbl     v6.16b, {v6.16b-v9.16b}, v15.16b
    +0x22e4: tbl     v7.16b, {v16.16b-v19.16b}, v15.16b
    +0x22e8: movi    v19.16b, #0x8
    +0x22ec: tbl     v1.16b, {v1.16b-v4.16b}, v15.16b
    +0x22f0: sub     v3.16b, v0.16b, v10.16b
    +0x22f4: shl     v17.16b, v24.16b, #3
    +0x22f8: tbl     v2.16b, {v20.16b-v23.16b}, v15.16b
    +0x22fc: movi    v20.16b, #0x4
    +0x2300: sub     v16.16b, v0.16b, v25.16b
    +0x2304: shl     v4.16b, v11.16b, #2
    +0x2308: add     x8, x8, #0x30
    +0x230c: add     x9, x9, #0x200
    +0x2310: ushr    v18.16b, v3.16b, #1
    +0x2314: add     v6.16b, v6.16b, v6.16b
    +0x2318: shl     v7.16b, v7.16b, #4
    +0x231c: shl     v1.16b, v1.16b, #5
    +0x2320: shl     v3.16b, v3.16b, #7
    +0x2324: cmp     x8, #0x4a0
    +0x2328: sub     v4.16b, v19.16b, v4.16b
    +0x232c: movi    v19.16b, #0x10
    +0x2330: sub     v2.16b, v0.16b, v2.16b
    +0x2334: sub     v6.16b, v20.16b, v6.16b
    +0x2338: sub     v7.16b, v5.16b, v7.16b
    +0x233c: orr     v4.16b, v4.16b, v18.16b
    +0x2340: movi    v18.16b, #0x40
    +0x2344: sub     v17.16b, v19.16b, v17.16b
    +0x2348: ushr    v19.16b, v16.16b, #2
    +0x234c: shl     v16.16b, v16.16b, #6
    +0x2350: orr     v3.16b, v7.16b, v3.16b
    +0x2354: sub     v1.16b, v18.16b, v1.16b
    +0x2358: orr     v2.16b, v17.16b, v2.16b
    +0x235c: orr     v6.16b, v6.16b, v19.16b
    +0x2360: orr     v19.16b, v4.16b, v1.16b
    +0x2364: orr     v17.16b, v2.16b, v16.16b
    +0x2368: orr     v18.16b, v6.16b, v3.16b
    +0x236c: st3     {v17.16b-v19.16b}, [x10]
    +0x2370: b.ne    <mldsa87_keypair_internal+0x1f6c>
    +0x2374: str     xzr, [sp, #7776]
    +0x2378: add     x8, sp, #0x1, lsl #12
    +0x237c: add     x27, sp, #0x160
    +0x2380: add     x8, x8, #0xe60
    +0x2384: mov     w28, #0x1400
    +0x2388: mov     w9, #0x1800
    +0x238c: mov     w8, #0xff
    +0x2390: add     x0, x27, #0x1, lsl #12
    +0x2394: add     x1, x27, x28
    +0x2398: add     x2, x27, x9
    +0x239c: add     x3, sp, #0x160
    +0x23a0: add     x4, x26, #0x20
    +0x23a4: mov     w5, #0x4
    +0x23a8: mov     w6, #0x5
    +0x23ac: mov     w7, #0x6
    +0x23b0: strb    w8, [sp]
    +0x23b4: bl      <mldsa87_poly_uniform_eta_4x>
    +0x23b8: mov     w8, #0x1000
    +0x23bc: mov     w9, #0x200
    +0x23c0: add     x10, x27, x8
    +0x23c4: add     x8, x8, #0x200
    +0x23c8: ldp     s6, s5, [x10, #128]
    +0x23cc: add     x15, x10, #0x40
    +0x23d0: add     x12, x10, #0xa0
    +0x23d4: add     x16, x10, #0xc0
    +0x23d8: ldr     s2, [x15]
    +0x23dc: ldp     s1, s0, [x10]
    +0x23e0: ldr     s3, [x16]
    +0x23e4: ld1     {v6.s}[1], [x12]
    +0x23e8: add     x12, x10, #0x44
    +0x23ec: add     x11, x10, #0x60
    +0x23f0: add     x13, x10, #0xe0
    +0x23f4: add     x15, x10, #0xc4
    +0x23f8: ldr     s7, [x12]
    +0x23fc: add     x14, x10, #0x20
    +0x2400: ld1     {v2.s}[1], [x11]
    +0x2404: ld1     {v3.s}[1], [x13]
    +0x2408: add     x11, x10, #0x24
    +0x240c: add     x13, x10, #0x64
    +0x2410: add     x18, x10, #0x144
    +0x2414: ldr     s16, [x15]
    +0x2418: ld1     {v1.s}[1], [x14]
    +0x241c: add     x14, x10, #0xa4
    +0x2420: add     x16, x10, #0xe4
    +0x2424: add     x1, x10, #0x1c4
    +0x2428: ld1     {v0.s}[1], [x11]
    +0x242c: ld1     {v7.s}[1], [x13]
    +0x2430: ldr     s17, [x10, #260]
    +0x2434: ldr     s18, [x18]
    +0x2438: add     x17, x10, #0x124
    +0x243c: add     x12, x10, #0x164
    +0x2440: ld1     {v5.s}[1], [x14]
    +0x2444: ld1     {v16.s}[1], [x16]
    +0x2448: ldr     s19, [x10, #388]
    +0x244c: ldr     s24, [x1]
    +0x2450: add     x0, x10, #0x1a4
    +0x2454: add     x11, x10, #0x1e4
    +0x2458: ld1     {v17.s}[1], [x17]
    +0x245c: ld1     {v18.s}[1], [x12]
    +0x2460: zip1    v25.2d, v0.2d, v7.2d
    +0x2464: ld1     {v19.s}[1], [x0]
    +0x2468: ld1     {v24.s}[1], [x11]
    +0x246c: zip1    v26.2d, v5.2d, v16.2d
    +0x2470: zip1    v20.2d, v1.2d, v2.2d
    +0x2474: zip1    v21.2d, v6.2d, v3.2d
    +0x2478: add     x15, x10, #0x48
    +0x247c: add     x18, x10, #0xc8
    +0x2480: zip1    v27.2d, v17.2d, v18.2d
    +0x2484: ldp     s0, s5, [x10, #8]
    +0x2488: zip1    v28.2d, v19.2d, v24.2d
    +0x248c: ldr     s1, [x15]
    +0x2490: add     x11, sp, #0x90
    +0x2494: ldp     s2, s16, [x10, #136]
    +0x2498: add     x16, x10, #0x28
    +0x249c: add     x17, x10, #0x68
    +0x24a0: ldr     s3, [x18]
    +0x24a4: st1     {v20.2d-v23.2d}, [x11]
    +0x24a8: add     x11, sp, #0xd0
    +0x24ac: add     x12, x10, #0xa8
    +0x24b0: add     x14, x10, #0xe8
    +0x24b4: add     x13, x10, #0x148
    +0x24b8: ld1     {v0.s}[1], [x16]
    +0x24bc: ld1     {v1.s}[1], [x17]
    +0x24c0: ldr     s17, [x10, #264]
    +0x24c4: ld1     {v2.s}[1], [x12]
    +0x24c8: ld1     {v3.s}[1], [x14]
    +0x24cc: st1     {v25.2d-v28.2d}, [x11]
    +0x24d0: add     x11, x10, #0x128
    +0x24d4: ldr     s18, [x13]
    +0x24d8: add     x15, x10, #0x168
    +0x24dc: ld1     {v17.s}[1], [x11]
    +0x24e0: add     x11, x10, #0x4c
    +0x24e4: add     x13, x10, #0x1c8
    +0x24e8: zip1    v19.2d, v0.2d, v1.2d
    +0x24ec: ld1     {v18.s}[1], [x15]
    +0x24f0: add     x15, x10, #0xcc
    +0x24f4: ldr     s0, [x11]
    +0x24f8: zip1    v20.2d, v2.2d, v3.2d
    +0x24fc: ldr     s7, [x13]
    +0x2500: add     x13, x10, #0x2c
    +0x2504: add     x11, x10, #0x6c
    +0x2508: ldr     s3, [x15]
    +0x250c: add     x16, x10, #0xac
    +0x2510: add     x15, x10, #0xec
    +0x2514: ld1     {v5.s}[1], [x13]
    +0x2518: ld1     {v0.s}[1], [x11]
    +0x251c: ld1     {v16.s}[1], [x16]
    +0x2520: ld1     {v3.s}[1], [x15]
    +0x2524: add     x14, x10, #0x1e8
    +0x2528: ldr     s6, [x10, #392]
    +0x252c: add     x11, x10, #0x14c
    +0x2530: add     x12, x10, #0x1a8
    +0x2534: zip1    v21.2d, v17.2d, v18.2d
    +0x2538: ld1     {v7.s}[1], [x14]
    +0x253c: zip1    v23.2d, v5.2d, v0.2d
    +0x2540: ldr     s2, [x11]
    +0x2544: add     x14, x10, #0x50
    +0x2548: ldp     s0, s17, [x10, #16]
    +0x254c: ld1     {v6.s}[1], [x12]
    +0x2550: ldr     s1, [x10, #268]
    +0x2554: add     x12, x10, #0x16c
    +0x2558: zip1    v24.2d, v16.2d, v3.2d
    +0x255c: add     x15, x10, #0xd0
    +0x2560: ldr     s3, [x14]
    +0x2564: ldp     s5, s18, [x10, #144]
    +0x2568: add     x11, x10, #0x12c
    +0x256c: ld1     {v2.s}[1], [x12]
    +0x2570: add     x12, x10, #0x30
    +0x2574: add     x13, x10, #0x70
    +0x2578: ldr     s16, [x15]
    +0x257c: ld1     {v1.s}[1], [x11]
    +0x2580: add     x11, x10, #0xb0
    +0x2584: add     x14, x10, #0xf0
    +0x2588: ld1     {v0.s}[1], [x12]
    +0x258c: ld1     {v3.s}[1], [x13]
    +0x2590: ld1     {v5.s}[1], [x11]
    +0x2594: ld1     {v16.s}[1], [x14]
    +0x2598: zip1    v22.2d, v6.2d, v7.2d
    +0x259c: zip1    v25.2d, v1.2d, v2.2d
    +0x25a0: add     x11, sp, #0x50
    +0x25a4: add     x12, x10, #0x150
    +0x25a8: zip1    v0.2d, v0.2d, v3.2d
    +0x25ac: ldr     s14, [x10, #272]
    +0x25b0: add     x14, sp, #0x110
    +0x25b4: zip1    v1.2d, v5.2d, v16.2d
    +0x25b8: ldr     s15, [x12]
    +0x25bc: add     x12, x10, #0x54
    +0x25c0: st1     {v19.2d-v22.2d}, [x11]
    +0x25c4: add     x11, sp, #0x10
    +0x25c8: add     x16, x10, #0xd4
    +0x25cc: add     x15, x10, #0xb4
    +0x25d0: add     x17, x10, #0xf4
    +0x25d4: add     x18, x10, #0x134
    +0x25d8: ld1     {v18.s}[1], [x15]
    +0x25dc: ldp     s20, s6, [x10, #24]
    +0x25e0: add     x0, x10, #0xd8
    +0x25e4: ldp     s19, s21, [x10, #152]
    +0x25e8: st1     {v23.2d-v26.2d}, [x11]
    +0x25ec: add     x11, x10, #0x130
    +0x25f0: ldr     s24, [x10, #404]
    +0x25f4: ld1     {v14.s}[1], [x11]
    +0x25f8: add     x11, x10, #0x34
    +0x25fc: ldr     s4, [x0]
    +0x2600: ld1     {v17.s}[1], [x11]
    +0x2604: add     x11, x10, #0x174
    +0x2608: add     x13, x10, #0x170
    +0x260c: ld1     {v15.s}[1], [x13]
    +0x2610: add     x1, x10, #0x158
    +0x2614: ldr     s5, [x10, #280]
    +0x2618: st1     {v0.2d-v3.2d}, [x14]
    +0x261c: ldr     s0, [x12]
    +0x2620: add     x14, x10, #0x74
    +0x2624: ldr     s1, [x16]
    +0x2628: add     x12, x10, #0x154
    +0x262c: ldr     s2, [x10, #276]
    +0x2630: ld1     {v0.s}[1], [x14]
    +0x2634: ldr     s3, [x12]
    +0x2638: add     x12, x10, #0x1b4
    +0x263c: ld1     {v1.s}[1], [x17]
    +0x2640: ld1     {v2.s}[1], [x18]
    +0x2644: add     x18, x10, #0x58
    +0x2648: ld1     {v3.s}[1], [x11]
    +0x264c: add     x11, x10, #0x1d4
    +0x2650: add     x17, x10, #0x38
    +0x2654: zip1    v10.2d, v17.2d, v0.2d
    +0x2658: ldr     s16, [x11]
    +0x265c: add     x11, x10, #0x1f4
    +0x2660: zip1    v11.2d, v18.2d, v1.2d
    +0x2664: ldr     s1, [x18]
    +0x2668: add     x16, x10, #0x78
    +0x266c: ld1     {v24.s}[1], [x12]
    +0x2670: ld1     {v16.s}[1], [x11]
    +0x2674: add     x11, x10, #0xb8
    +0x2678: add     x12, x10, #0xf8
    +0x267c: ld1     {v20.s}[1], [x17]
    +0x2680: ld1     {v1.s}[1], [x16]
    +0x2684: zip1    v12.2d, v2.2d, v3.2d
    +0x2688: ld1     {v19.s}[1], [x11]
    +0x268c: ld1     {v4.s}[1], [x12]
    +0x2690: ldr     s2, [x10, #408]
    +0x2694: add     x11, x10, #0x1b8
    +0x2698: add     x14, x10, #0x1d8
    +0x269c: zip1    v28.2d, v20.2d, v1.2d
    +0x26a0: ldr     s3, [x1]
    +0x26a4: add     x13, x10, #0x138
    +0x26a8: ld1     {v2.s}[1], [x11]
    +0x26ac: add     x11, sp, #0x110
    +0x26b0: zip1    v29.2d, v19.2d, v4.2d
    +0x26b4: ld1     {v17.2d-v20.2d}, [x11]
    +0x26b8: add     x15, x10, #0x178
    +0x26bc: ldr     s0, [x14]
    +0x26c0: zip1    v19.2d, v14.2d, v15.2d
    +0x26c4: add     x11, sp, #0x110
    +0x26c8: ld1     {v5.s}[1], [x13]
    +0x26cc: ld1     {v3.s}[1], [x15]
    +0x26d0: add     x12, x10, #0x1f8
    +0x26d4: zip1    v13.2d, v24.2d, v16.2d
    +0x26d8: ld1     {v0.s}[1], [x12]
    +0x26dc: add     x14, x10, #0x160
    +0x26e0: add     x17, x10, #0x1d0
    +0x26e4: ldr     s9, [x17]
    +0x26e8: add     x13, x10, #0x120
    +0x26ec: ldr     s8, [x10, #400]
    +0x26f0: st1     {v17.2d-v20.2d}, [x11]
    +0x26f4: add     x11, x10, #0x140
    +0x26f8: zip1    v30.2d, v5.2d, v3.2d
    +0x26fc: ldr     s16, [x11]
    +0x2700: ldr     s17, [x10, #256]
    +0x2704: zip1    v31.2d, v2.2d, v0.2d
    +0x2708: ldr     s0, [x10, #396]
    +0x270c: add     x16, x10, #0x1ec
    +0x2710: add     x18, x10, #0xdc
    +0x2714: ld1     {v16.s}[1], [x14]
    +0x2718: add     x14, x10, #0x1cc
    +0x271c: ld1     {v17.s}[1], [x13]
    +0x2720: ldr     s1, [x14]
    +0x2724: add     x14, x10, #0x1f0
    +0x2728: add     x13, x10, #0x1ac
    +0x272c: ld1     {v9.s}[1], [x14]
    +0x2730: add     x14, x10, #0x5c
    +0x2734: ld1     {v0.s}[1], [x13]
    +0x2738: add     x13, x10, #0x1b0
    +0x273c: ldr     s4, [x14]
    +0x2740: ld1     {v1.s}[1], [x16]
    +0x2744: ld1     {v8.s}[1], [x13]
    +0x2748: add     x13, x10, #0x3c
    +0x274c: add     x16, x10, #0x7c
    +0x2750: ldr     s19, [x18]
    +0x2754: add     x17, x10, #0xbc
    +0x2758: add     x0, x10, #0xfc
    +0x275c: add     x2, x10, #0x15c
    +0x2760: ld1     {v6.s}[1], [x13]
    +0x2764: ld1     {v4.s}[1], [x16]
    +0x2768: ldr     s2, [x10, #284]
    +0x276c: ld1     {v21.s}[1], [x17]
    +0x2770: ld1     {v19.s}[1], [x0]
    +0x2774: ldr     s3, [x2]
    +0x2778: add     x15, x10, #0x1c0
    +0x277c: add     x1, x10, #0x13c
    +0x2780: add     x3, x10, #0x17c
    +0x2784: add     x11, x10, #0x1a0
    +0x2788: add     x12, x10, #0x1e0
    +0x278c: add     x4, x10, #0x1bc
    +0x2790: add     x13, x10, #0x1dc
    +0x2794: add     x14, x10, #0x1fc
    +0x2798: ld1     {v2.s}[1], [x1]
    +0x279c: ldr     s18, [x10, #412]
    +0x27a0: ld1     {v3.s}[1], [x3]
    +0x27a4: ldr     s14, [x10, #384]
    +0x27a8: ldr     s15, [x15]
    +0x27ac: zip1    v4.2d, v6.2d, v4.2d
    +0x27b0: add     x10, sp, #0x10
    +0x27b4: zip1    v5.2d, v21.2d, v19.2d
    +0x27b8: ldr     s27, [x13]
    +0x27bc: ld1     {v19.2d-v22.2d}, [x10]
    +0x27c0: add     x10, sp, #0x110
    +0x27c4: ld1     {v14.s}[1], [x11]
    +0x27c8: ld1     {v15.s}[1], [x12]
    +0x27cc: ld1     {v23.2d-v26.2d}, [x10]
    +0x27d0: add     x10, sp, #0x90
    +0x27d4: zip1    v22.2d, v0.2d, v1.2d
    +0x27d8: zip1    v6.2d, v2.2d, v3.2d
    +0x27dc: ld1     {v0.2d-v3.2d}, [x10]
    +0x27e0: ld1     {v18.s}[1], [x4]
    +0x27e4: ld1     {v27.s}[1], [x14]
    +0x27e8: zip1    v2.2d, v17.2d, v16.2d
    +0x27ec: zip1    v3.2d, v14.2d, v15.2d
    +0x27f0: add     x10, sp, #0xd0
    +0x27f4: zip1    v26.2d, v8.2d, v9.2d
    +0x27f8: mov     v8.16b, v0.16b
    +0x27fc: mov     v9.16b, v1.16b
    +0x2800: zip1    v7.2d, v18.2d, v27.2d
    +0x2804: ldr     q18, [sp, #336]
    +0x2808: tbl     v27.16b, {v10.16b-v13.16b}, v18.16b
    +0x280c: mov     v10.16b, v2.16b
    +0x2810: mov     v11.16b, v3.16b
    +0x2814: ld1     {v0.2d-v3.2d}, [x10]
    +0x2818: add     x10, sp, #0x50
    +0x281c: tbl     v28.16b, {v28.16b-v31.16b}, v18.16b
    +0x2820: tbl     v17.16b, {v23.16b-v26.16b}, v18.16b
    +0x2824: tbl     v16.16b, {v19.16b-v22.16b}, v18.16b
    +0x2828: tbl     v29.16b, {v0.16b-v3.16b}, v18.16b
    +0x282c: ld1     {v0.2d-v3.2d}, [x10]
    +0x2830: add     x10, x19, x9
    +0x2834: add     x9, x9, #0x30
    +0x2838: cmp     x9, #0x260
    +0x283c: tbl     v30.16b, {v0.16b-v3.16b}, v18.16b
    +0x2840: tbl     v0.16b, {v4.16b-v7.16b}, v18.16b
    +0x2844: tbl     v1.16b, {v8.16b-v11.16b}, v18.16b
    +0x2848: movi    v18.16b, #0x2
    +0x284c: shl     v7.16b, v17.16b, #4
    +0x2850: movi    v17.16b, #0x8
    +0x2854: shl     v3.16b, v28.16b, #2
    +0x2858: add     v6.16b, v16.16b, v16.16b
    +0x285c: shl     v5.16b, v29.16b, #3
    +0x2860: shl     v0.16b, v0.16b, #5
    +0x2864: sub     v2.16b, v18.16b, v27.16b
    +0x2868: sub     v4.16b, v18.16b, v30.16b
    +0x286c: sub     v1.16b, v18.16b, v1.16b
    +0x2870: movi    v18.16b, #0x4
    +0x2874: sub     v3.16b, v17.16b, v3.16b
    +0x2878: movi    v17.16b, #0x10
    +0x287c: ushr    v16.16b, v2.16b, #1
    +0x2880: shl     v2.16b, v2.16b, #7
    +0x2884: sub     v6.16b, v18.16b, v6.16b
    +0x2888: movi    v18.16b, #0x20
    +0x288c: sub     v5.16b, v17.16b, v5.16b
    +0x2890: orr     v3.16b, v3.16b, v16.16b
    +0x2894: movi    v16.16b, #0x40
    +0x2898: ushr    v17.16b, v4.16b, #2
    +0x289c: shl     v4.16b, v4.16b, #6
    +0x28a0: orr     v1.16b, v5.16b, v1.16b
    +0x28a4: sub     v7.16b, v18.16b, v7.16b
    +0x28a8: orr     v5.16b, v6.16b, v17.16b
    +0x28ac: sub     v0.16b, v16.16b, v0.16b
    +0x28b0: orr     v2.16b, v7.16b, v2.16b
    +0x28b4: orr     v18.16b, v3.16b, v0.16b
    +0x28b8: orr     v16.16b, v1.16b, v4.16b
    +0x28bc: orr     v17.16b, v5.16b, v2.16b
    +0x28c0: st3     {v16.16b-v18.16b}, [x10]
    +0x28c4: b.ne    <mldsa87_keypair_internal+0x23c0>
    +0x28c8: str     xzr, [sp, #7776]
    +0x28cc: add     x8, sp, #0x1, lsl #12
    +0x28d0: add     x10, sp, #0x160
    +0x28d4: add     x8, x8, #0xe60
    +0x28d8: mov     w8, #0x1400
    +0x28dc: add     x11, x10, x8
    +0x28e0: add     x8, x8, #0x200
    +0x28e4: ldp     s6, s5, [x11, #128]
    +0x28e8: add     x16, x11, #0x40
    +0x28ec: add     x13, x11, #0xa0
    +0x28f0: add     x17, x11, #0xc0
    +0x28f4: ldr     s2, [x16]
    +0x28f8: ldp     s1, s0, [x11]
    +0x28fc: ldr     s3, [x17]
    +0x2900: ld1     {v6.s}[1], [x13]
    +0x2904: add     x13, x11, #0x44
    +0x2908: add     x12, x11, #0x60
    +0x290c: add     x14, x11, #0xe0
    +0x2910: add     x16, x11, #0xc4
    +0x2914: ldr     s7, [x13]
    +0x2918: add     x15, x11, #0x20
    +0x291c: ld1     {v2.s}[1], [x12]
    +0x2920: ld1     {v3.s}[1], [x14]
    +0x2924: add     x12, x11, #0x24
    +0x2928: add     x14, x11, #0x64
    +0x292c: add     x0, x11, #0x144
    +0x2930: ldr     s16, [x16]
    +0x2934: ld1     {v1.s}[1], [x15]
    +0x2938: add     x15, x11, #0xa4
    +0x293c: add     x17, x11, #0xe4
    +0x2940: add     x2, x11, #0x1c4
    +0x2944: ld1     {v0.s}[1], [x12]
    +0x2948: ld1     {v7.s}[1], [x14]
    +0x294c: ldr     s17, [x11, #260]
    +0x2950: ldr     s18, [x0]
    +0x2954: add     x18, x11, #0x124
    +0x2958: add     x13, x11, #0x164
    +0x295c: ld1     {v5.s}[1], [x15]
    +0x2960: ld1     {v16.s}[1], [x17]
    +0x2964: ldr     s19, [x11, #388]
    +0x2968: ldr     s24, [x2]
    +0x296c: add     x1, x11, #0x1a4
    +0x2970: add     x12, x11, #0x1e4
    +0x2974: ld1     {v17.s}[1], [x18]
    +0x2978: ld1     {v18.s}[1], [x13]
    +0x297c: zip1    v25.2d, v0.2d, v7.2d
    +0x2980: ld1     {v19.s}[1], [x1]
    +0x2984: ld1     {v24.s}[1], [x12]
    +0x2988: zip1    v26.2d, v5.2d, v16.2d
    +0x298c: zip1    v20.2d, v1.2d, v2.2d
    +0x2990: zip1    v21.2d, v6.2d, v3.2d
    +0x2994: add     x16, x11, #0x48
    +0x2998: add     x0, x11, #0xc8
    +0x299c: zip1    v27.2d, v17.2d, v18.2d
    +0x29a0: ldp     s0, s5, [x11, #8]
    +0x29a4: zip1    v28.2d, v19.2d, v24.2d
    +0x29a8: ldr     s1, [x16]
    +0x29ac: add     x12, sp, #0x90
    +0x29b0: ldp     s2, s16, [x11, #136]
    +0x29b4: add     x17, x11, #0x28
    +0x29b8: add     x18, x11, #0x68
    +0x29bc: ldr     s3, [x0]
    +0x29c0: st1     {v20.2d-v23.2d}, [x12]
    +0x29c4: add     x12, sp, #0xd0
    +0x29c8: add     x13, x11, #0xa8
    +0x29cc: add     x15, x11, #0xe8
    +0x29d0: add     x14, x11, #0x148
    +0x29d4: ld1     {v0.s}[1], [x17]
    +0x29d8: ld1     {v1.s}[1], [x18]
    +0x29dc: ldr     s17, [x11, #264]
    +0x29e0: ld1     {v2.s}[1], [x13]
    +0x29e4: ld1     {v3.s}[1], [x15]
    +0x29e8: st1     {v25.2d-v28.2d}, [x12]
    +0x29ec: add     x12, x11, #0x128
    +0x29f0: ldr     s18, [x14]
    +0x29f4: add     x16, x11, #0x168
    +0x29f8: ld1     {v17.s}[1], [x12]
    +0x29fc: add     x12, x11, #0x4c
    +0x2a00: add     x14, x11, #0x1c8
    +0x2a04: zip1    v19.2d, v0.2d, v1.2d
    +0x2a08: ld1     {v18.s}[1], [x16]
    +0x2a0c: add     x16, x11, #0xcc
    +0x2a10: ldr     s0, [x12]
    +0x2a14: zip1    v20.2d, v2.2d, v3.2d
    +0x2a18: ldr     s7, [x14]
    +0x2a1c: add     x14, x11, #0x2c
    +0x2a20: add     x12, x11, #0x6c
    +0x2a24: ldr     s3, [x16]
    +0x2a28: add     x17, x11, #0xac
    +0x2a2c: add     x16, x11, #0xec
    +0x2a30: ld1     {v5.s}[1], [x14]
    +0x2a34: ld1     {v0.s}[1], [x12]
    +0x2a38: ld1     {v16.s}[1], [x17]
    +0x2a3c: ld1     {v3.s}[1], [x16]
    +0x2a40: add     x15, x11, #0x1e8
    +0x2a44: ldr     s6, [x11, #392]
    +0x2a48: add     x12, x11, #0x14c
    +0x2a4c: add     x13, x11, #0x1a8
    +0x2a50: zip1    v21.2d, v17.2d, v18.2d
    +0x2a54: ld1     {v7.s}[1], [x15]
    +0x2a58: zip1    v23.2d, v5.2d, v0.2d
    +0x2a5c: ldr     s2, [x12]
    +0x2a60: add     x15, x11, #0x50
    +0x2a64: ldp     s0, s17, [x11, #16]
    +0x2a68: ld1     {v6.s}[1], [x13]
    +0x2a6c: ldr     s1, [x11, #268]
    +0x2a70: add     x13, x11, #0x16c
    +0x2a74: zip1    v24.2d, v16.2d, v3.2d
    +0x2a78: add     x16, x11, #0xd0
    +0x2a7c: ldr     s3, [x15]
    +0x2a80: ldp     s5, s18, [x11, #144]
    +0x2a84: add     x12, x11, #0x12c
    +0x2a88: ld1     {v2.s}[1], [x13]
    +0x2a8c: add     x13, x11, #0x30
    +0x2a90: add     x14, x11, #0x70
    +0x2a94: ldr     s16, [x16]
    +0x2a98: ld1     {v1.s}[1], [x12]
    +0x2a9c: add     x12, x11, #0xb0
    +0x2aa0: add     x15, x11, #0xf0
    +0x2aa4: ld1     {v0.s}[1], [x13]
    +0x2aa8: ld1     {v3.s}[1], [x14]
    +0x2aac: ld1     {v5.s}[1], [x12]
    +0x2ab0: ld1     {v16.s}[1], [x15]
    +0x2ab4: zip1    v22.2d, v6.2d, v7.2d
    +0x2ab8: zip1    v25.2d, v1.2d, v2.2d
    +0x2abc: add     x12, sp, #0x50
    +0x2ac0: add     x13, x11, #0x150
    +0x2ac4: zip1    v0.2d, v0.2d, v3.2d
    +0x2ac8: ldr     s14, [x11, #272]
    +0x2acc: add     x15, sp, #0x110
    +0x2ad0: zip1    v1.2d, v5.2d, v16.2d
    +0x2ad4: ldr     s15, [x13]
    +0x2ad8: add     x13, x11, #0x54
    +0x2adc: st1     {v19.2d-v22.2d}, [x12]
    +0x2ae0: add     x12, sp, #0x10
    +0x2ae4: add     x17, x11, #0xd4
    +0x2ae8: add     x16, x11, #0xb4
    +0x2aec: add     x18, x11, #0xf4
    +0x2af0: add     x0, x11, #0x134
    +0x2af4: ld1     {v18.s}[1], [x16]
    +0x2af8: ldp     s20, s6, [x11, #24]
    +0x2afc: add     x1, x11, #0xd8
    +0x2b00: ldp     s19, s21, [x11, #152]
    +0x2b04: st1     {v23.2d-v26.2d}, [x12]
    +0x2b08: add     x12, x11, #0x130
    +0x2b0c: ldr     s24, [x11, #404]
    +0x2b10: ld1     {v14.s}[1], [x12]
    +0x2b14: add     x12, x11, #0x34
    +0x2b18: ldr     s4, [x1]
    +0x2b1c: ld1     {v17.s}[1], [x12]
    +0x2b20: add     x12, x11, #0x174
    +0x2b24: add     x14, x11, #0x170
    +0x2b28: ld1     {v15.s}[1], [x14]
    +0x2b2c: add     x2, x11, #0x158
    +0x2b30: ldr     s5, [x11, #280]
    +0x2b34: st1     {v0.2d-v3.2d}, [x15]
    +0x2b38: ldr     s0, [x13]
    +0x2b3c: add     x15, x11, #0x74
    +0x2b40: ldr     s1, [x17]
    +0x2b44: add     x13, x11, #0x154
    +0x2b48: ldr     s2, [x11, #276]
    +0x2b4c: ld1     {v0.s}[1], [x15]
    +0x2b50: ldr     s3, [x13]
    +0x2b54: add     x13, x11, #0x1b4
    +0x2b58: ld1     {v1.s}[1], [x18]
    +0x2b5c: ld1     {v2.s}[1], [x0]
    +0x2b60: add     x0, x11, #0x58
    +0x2b64: ld1     {v3.s}[1], [x12]
    +0x2b68: add     x12, x11, #0x1d4
    +0x2b6c: add     x18, x11, #0x38
    +0x2b70: zip1    v10.2d, v17.2d, v0.2d
    +0x2b74: ldr     s16, [x12]
    +0x2b78: add     x12, x11, #0x1f4
    +0x2b7c: zip1    v11.2d, v18.2d, v1.2d
    +0x2b80: ldr     s1, [x0]
    +0x2b84: add     x17, x11, #0x78
    +0x2b88: ld1     {v24.s}[1], [x13]
    +0x2b8c: ld1     {v16.s}[1], [x12]
    +0x2b90: add     x12, x11, #0xb8
    +0x2b94: add     x13, x11, #0xf8
    +0x2b98: ld1     {v20.s}[1], [x18]
    +0x2b9c: ld1     {v1.s}[1], [x17]
    +0x2ba0: zip1    v12.2d, v2.2d, v3.2d
    +0x2ba4: ld1     {v19.s}[1], [x12]
    +0x2ba8: ld1     {v4.s}[1], [x13]
    +0x2bac: ldr     s2, [x11, #408]
    +0x2bb0: add     x12, x11, #0x1b8
    +0x2bb4: add     x15, x11, #0x1d8
    +0x2bb8: zip1    v28.2d, v20.2d, v1.2d
    +0x2bbc: ldr     s3, [x2]
    +0x2bc0: add     x14, x11, #0x138
    +0x2bc4: ld1     {v2.s}[1], [x12]
    +0x2bc8: add     x12, sp, #0x110
    +0x2bcc: zip1    v29.2d, v19.2d, v4.2d
    +0x2bd0: ld1     {v17.2d-v20.2d}, [x12]
    +0x2bd4: add     x16, x11, #0x178
    +0x2bd8: ldr     s0, [x15]
    +0x2bdc: zip1    v19.2d, v14.2d, v15.2d
    +0x2be0: add     x12, sp, #0x110
    +0x2be4: ld1     {v5.s}[1], [x14]
    +0x2be8: ld1     {v3.s}[1], [x16]
    +0x2bec: add     x13, x11, #0x1f8
    +0x2bf0: zip1    v13.2d, v24.2d, v16.2d
    +0x2bf4: ld1     {v0.s}[1], [x13]
    +0x2bf8: add     x15, x11, #0x160
    +0x2bfc: add     x18, x11, #0x1d0
    +0x2c00: ldr     s9, [x18]
    +0x2c04: add     x14, x11, #0x120
    +0x2c08: ldr     s8, [x11, #400]
    +0x2c0c: st1     {v17.2d-v20.2d}, [x12]
    +0x2c10: add     x12, x11, #0x140
    +0x2c14: zip1    v30.2d, v5.2d, v3.2d
    +0x2c18: ldr     s16, [x12]
    +0x2c1c: ldr     s17, [x11, #256]
    +0x2c20: zip1    v31.2d, v2.2d, v0.2d
    +0x2c24: ldr     s0, [x11, #396]
    +0x2c28: add     x17, x11, #0x1ec
    +0x2c2c: add     x0, x11, #0xdc
    +0x2c30: ld1     {v16.s}[1], [x15]
    +0x2c34: add     x15, x11, #0x1cc
    +0x2c38: ld1     {v17.s}[1], [x14]
    +0x2c3c: ldr     s1, [x15]
    +0x2c40: add     x15, x11, #0x1f0
    +0x2c44: add     x14, x11, #0x1ac
    +0x2c48: ld1     {v9.s}[1], [x15]
    +0x2c4c: add     x15, x11, #0x5c
    +0x2c50: ld1     {v0.s}[1], [x14]
    +0x2c54: add     x14, x11, #0x1b0
    +0x2c58: ldr     s4, [x15]
    +0x2c5c: ld1     {v1.s}[1], [x17]
    +0x2c60: ld1     {v8.s}[1], [x14]
    +0x2c64: add     x14, x11, #0x3c
    +0x2c68: add     x17, x11, #0x7c
    +0x2c6c: ldr     s19, [x0]
    +0x2c70: add     x18, x11, #0xbc
    +0x2c74: add     x1, x11, #0xfc
    +0x2c78: add     x3, x11, #0x15c
    +0x2c7c: ld1     {v6.s}[1], [x14]
    +0x2c80: ld1     {v4.s}[1], [x17]
    +0x2c84: ldr     s2, [x11, #284]
    +0x2c88: ld1     {v21.s}[1], [x18]
    +0x2c8c: ld1     {v19.s}[1], [x1]
    +0x2c90: ldr     s3, [x3]
    +0x2c94: add     x16, x11, #0x1c0
    +0x2c98: add     x2, x11, #0x13c
    +0x2c9c: add     x4, x11, #0x17c
    +0x2ca0: add     x12, x11, #0x1a0
    +0x2ca4: add     x13, x11, #0x1e0
    +0x2ca8: add     x5, x11, #0x1bc
    +0x2cac: add     x14, x11, #0x1dc
    +0x2cb0: add     x15, x11, #0x1fc
    +0x2cb4: ld1     {v2.s}[1], [x2]
    +0x2cb8: ldr     s18, [x11, #412]
    +0x2cbc: ld1     {v3.s}[1], [x4]
    +0x2cc0: ldr     s14, [x11, #384]
    +0x2cc4: ldr     s15, [x16]
    +0x2cc8: zip1    v4.2d, v6.2d, v4.2d
    +0x2ccc: add     x11, sp, #0x10
    +0x2cd0: zip1    v5.2d, v21.2d, v19.2d
    +0x2cd4: ldr     s27, [x14]
    +0x2cd8: ld1     {v19.2d-v22.2d}, [x11]
    +0x2cdc: add     x11, sp, #0x110
    +0x2ce0: ld1     {v14.s}[1], [x12]
    +0x2ce4: ld1     {v15.s}[1], [x13]
    +0x2ce8: ld1     {v23.2d-v26.2d}, [x11]
    +0x2cec: add     x11, sp, #0x90
    +0x2cf0: zip1    v22.2d, v0.2d, v1.2d
    +0x2cf4: zip1    v6.2d, v2.2d, v3.2d
    +0x2cf8: ld1     {v0.2d-v3.2d}, [x11]
    +0x2cfc: ld1     {v18.s}[1], [x5]
    +0x2d00: ld1     {v27.s}[1], [x15]
    +0x2d04: zip1    v2.2d, v17.2d, v16.2d
    +0x2d08: zip1    v3.2d, v14.2d, v15.2d
    +0x2d0c: add     x11, sp, #0xd0
    +0x2d10: zip1    v26.2d, v8.2d, v9.2d
    +0x2d14: mov     v8.16b, v0.16b
    +0x2d18: mov     v9.16b, v1.16b
    +0x2d1c: zip1    v7.2d, v18.2d, v27.2d
    +0x2d20: ldr     q18, [sp, #336]
    +0x2d24: tbl     v27.16b, {v10.16b-v13.16b}, v18.16b
    +0x2d28: mov     v10.16b, v2.16b
    +0x2d2c: mov     v11.16b, v3.16b
    +0x2d30: ld1     {v0.2d-v3.2d}, [x11]
    +0x2d34: add     x11, sp, #0x50
    +0x2d38: tbl     v28.16b, {v28.16b-v31.16b}, v18.16b
    +0x2d3c: tbl     v17.16b, {v23.16b-v26.16b}, v18.16b
    +0x2d40: tbl     v16.16b, {v19.16b-v22.16b}, v18.16b
    +0x2d44: tbl     v29.16b, {v0.16b-v3.16b}, v18.16b
    +0x2d48: ld1     {v0.2d-v3.2d}, [x11]
    +0x2d4c: add     x11, x19, x9
    +0x2d50: add     x9, x9, #0x30
    +0x2d54: cmp     x9, #0x2c0
    +0x2d58: tbl     v30.16b, {v0.16b-v3.16b}, v18.16b
    +0x2d5c: tbl     v0.16b, {v4.16b-v7.16b}, v18.16b
    +0x2d60: tbl     v1.16b, {v8.16b-v11.16b}, v18.16b
    +0x2d64: movi    v18.16b, #0x2
    +0x2d68: shl     v7.16b, v17.16b, #4
    +0x2d6c: movi    v17.16b, #0x8
    +0x2d70: shl     v3.16b, v28.16b, #2
    +0x2d74: add     v6.16b, v16.16b, v16.16b
    +0x2d78: shl     v5.16b, v29.16b, #3
    +0x2d7c: shl     v0.16b, v0.16b, #5
    +0x2d80: sub     v2.16b, v18.16b, v27.16b
    +0x2d84: sub     v4.16b, v18.16b, v30.16b
    +0x2d88: sub     v1.16b, v18.16b, v1.16b
    +0x2d8c: movi    v18.16b, #0x4
    +0x2d90: sub     v3.16b, v17.16b, v3.16b
    +0x2d94: movi    v17.16b, #0x10
    +0x2d98: ushr    v16.16b, v2.16b, #1
    +0x2d9c: shl     v2.16b, v2.16b, #7
    +0x2da0: sub     v6.16b, v18.16b, v6.16b
    +0x2da4: movi    v18.16b, #0x20
    +0x2da8: sub     v5.16b, v17.16b, v5.16b
    +0x2dac: orr     v3.16b, v3.16b, v16.16b
    +0x2db0: movi    v16.16b, #0x40
    +0x2db4: ushr    v17.16b, v4.16b, #2
    +0x2db8: shl     v4.16b, v4.16b, #6
    +0x2dbc: orr     v1.16b, v5.16b, v1.16b
    +0x2dc0: sub     v7.16b, v18.16b, v7.16b
    +0x2dc4: orr     v5.16b, v6.16b, v17.16b
    +0x2dc8: sub     v0.16b, v16.16b, v0.16b
    +0x2dcc: orr     v2.16b, v7.16b, v2.16b
    +0x2dd0: orr     v18.16b, v3.16b, v0.16b
    +0x2dd4: orr     v16.16b, v1.16b, v4.16b
    +0x2dd8: orr     v17.16b, v5.16b, v2.16b
    +0x2ddc: st3     {v16.16b-v18.16b}, [x11]
    +0x2de0: b.ne    <mldsa87_keypair_internal+0x28dc>
    +0x2de4: str     xzr, [sp, #7776]
    +0x2de8: add     x8, sp, #0x1, lsl #12
    +0x2dec: add     x10, sp, #0x160
    +0x2df0: add     x8, x8, #0xe60
    +0x2df4: mov     w8, #0x1800
    +0x2df8: add     x11, x10, x8
    +0x2dfc: add     x8, x8, #0x200
    +0x2e00: ldp     s6, s5, [x11, #128]
    +0x2e04: add     x16, x11, #0x40
    +0x2e08: add     x13, x11, #0xa0
    +0x2e0c: add     x17, x11, #0xc0
    +0x2e10: ldr     s2, [x16]
    +0x2e14: ldp     s1, s0, [x11]
    +0x2e18: ldr     s3, [x17]
    +0x2e1c: ld1     {v6.s}[1], [x13]
    +0x2e20: add     x13, x11, #0x44
    +0x2e24: add     x12, x11, #0x60
    +0x2e28: add     x14, x11, #0xe0
    +0x2e2c: add     x16, x11, #0xc4
    +0x2e30: ldr     s7, [x13]
    +0x2e34: add     x15, x11, #0x20
    +0x2e38: ld1     {v2.s}[1], [x12]
    +0x2e3c: ld1     {v3.s}[1], [x14]
    +0x2e40: add     x12, x11, #0x24
    +0x2e44: add     x14, x11, #0x64
    +0x2e48: add     x0, x11, #0x144
    +0x2e4c: ldr     s16, [x16]
    +0x2e50: ld1     {v1.s}[1], [x15]
    +0x2e54: add     x15, x11, #0xa4
    +0x2e58: add     x17, x11, #0xe4
    +0x2e5c: add     x2, x11, #0x1c4
    +0x2e60: ld1     {v0.s}[1], [x12]
    +0x2e64: ld1     {v7.s}[1], [x14]
    +0x2e68: ldr     s17, [x11, #260]
    +0x2e6c: ldr     s18, [x0]
    +0x2e70: add     x18, x11, #0x124
    +0x2e74: add     x13, x11, #0x164
    +0x2e78: ld1     {v5.s}[1], [x15]
    +0x2e7c: ld1     {v16.s}[1], [x17]
    +0x2e80: ldr     s19, [x11, #388]
    +0x2e84: ldr     s24, [x2]
    +0x2e88: add     x1, x11, #0x1a4
    +0x2e8c: add     x12, x11, #0x1e4
    +0x2e90: ld1     {v17.s}[1], [x18]
    +0x2e94: ld1     {v18.s}[1], [x13]
    +0x2e98: zip1    v25.2d, v0.2d, v7.2d
    +0x2e9c: ld1     {v19.s}[1], [x1]
    +0x2ea0: ld1     {v24.s}[1], [x12]
    +0x2ea4: zip1    v26.2d, v5.2d, v16.2d
    +0x2ea8: zip1    v20.2d, v1.2d, v2.2d
    +0x2eac: zip1    v21.2d, v6.2d, v3.2d
    +0x2eb0: add     x16, x11, #0x48
    +0x2eb4: add     x0, x11, #0xc8
    +0x2eb8: zip1    v27.2d, v17.2d, v18.2d
    +0x2ebc: ldp     s0, s5, [x11, #8]
    +0x2ec0: zip1    v28.2d, v19.2d, v24.2d
    +0x2ec4: ldr     s1, [x16]
    +0x2ec8: add     x12, sp, #0x90
    +0x2ecc: ldp     s2, s16, [x11, #136]
    +0x2ed0: add     x17, x11, #0x28
    +0x2ed4: add     x18, x11, #0x68
    +0x2ed8: ldr     s3, [x0]
    +0x2edc: st1     {v20.2d-v23.2d}, [x12]
    +0x2ee0: add     x12, sp, #0xd0
    +0x2ee4: add     x13, x11, #0xa8
    +0x2ee8: add     x15, x11, #0xe8
    +0x2eec: add     x14, x11, #0x148
    +0x2ef0: ld1     {v0.s}[1], [x17]
    +0x2ef4: ld1     {v1.s}[1], [x18]
    +0x2ef8: ldr     s17, [x11, #264]
    +0x2efc: ld1     {v2.s}[1], [x13]
    +0x2f00: ld1     {v3.s}[1], [x15]
    +0x2f04: st1     {v25.2d-v28.2d}, [x12]
    +0x2f08: add     x12, x11, #0x128
    +0x2f0c: ldr     s18, [x14]
    +0x2f10: add     x16, x11, #0x168
    +0x2f14: ld1     {v17.s}[1], [x12]
    +0x2f18: add     x12, x11, #0x4c
    +0x2f1c: add     x14, x11, #0x1c8
    +0x2f20: zip1    v19.2d, v0.2d, v1.2d
    +0x2f24: ld1     {v18.s}[1], [x16]
    +0x2f28: add     x16, x11, #0xcc
    +0x2f2c: ldr     s0, [x12]
    +0x2f30: zip1    v20.2d, v2.2d, v3.2d
    +0x2f34: ldr     s7, [x14]
    +0x2f38: add     x14, x11, #0x2c
    +0x2f3c: add     x12, x11, #0x6c
    +0x2f40: ldr     s3, [x16]
    +0x2f44: add     x17, x11, #0xac
    +0x2f48: add     x16, x11, #0xec
    +0x2f4c: ld1     {v5.s}[1], [x14]
    +0x2f50: ld1     {v0.s}[1], [x12]
    +0x2f54: ld1     {v16.s}[1], [x17]
    +0x2f58: ld1     {v3.s}[1], [x16]
    +0x2f5c: add     x15, x11, #0x1e8
    +0x2f60: ldr     s6, [x11, #392]
    +0x2f64: add     x12, x11, #0x14c
    +0x2f68: add     x13, x11, #0x1a8
    +0x2f6c: zip1    v21.2d, v17.2d, v18.2d
    +0x2f70: ld1     {v7.s}[1], [x15]
    +0x2f74: zip1    v23.2d, v5.2d, v0.2d
    +0x2f78: ldr     s2, [x12]
    +0x2f7c: add     x15, x11, #0x50
    +0x2f80: ldp     s0, s17, [x11, #16]
    +0x2f84: ld1     {v6.s}[1], [x13]
    +0x2f88: ldr     s1, [x11, #268]
    +0x2f8c: add     x13, x11, #0x16c
    +0x2f90: zip1    v24.2d, v16.2d, v3.2d
    +0x2f94: add     x16, x11, #0xd0
    +0x2f98: ldr     s3, [x15]
    +0x2f9c: ldp     s5, s18, [x11, #144]
    +0x2fa0: add     x12, x11, #0x12c
    +0x2fa4: ld1     {v2.s}[1], [x13]
    +0x2fa8: add     x13, x11, #0x30
    +0x2fac: add     x14, x11, #0x70
    +0x2fb0: ldr     s16, [x16]
    +0x2fb4: ld1     {v1.s}[1], [x12]
    +0x2fb8: add     x12, x11, #0xb0
    +0x2fbc: add     x15, x11, #0xf0
    +0x2fc0: ld1     {v0.s}[1], [x13]
    +0x2fc4: ld1     {v3.s}[1], [x14]
    +0x2fc8: ld1     {v5.s}[1], [x12]
    +0x2fcc: ld1     {v16.s}[1], [x15]
    +0x2fd0: zip1    v22.2d, v6.2d, v7.2d
    +0x2fd4: zip1    v25.2d, v1.2d, v2.2d
    +0x2fd8: add     x12, sp, #0x50
    +0x2fdc: add     x13, x11, #0x150
    +0x2fe0: zip1    v0.2d, v0.2d, v3.2d
    +0x2fe4: ldr     s14, [x11, #272]
    +0x2fe8: add     x15, sp, #0x110
    +0x2fec: zip1    v1.2d, v5.2d, v16.2d
    +0x2ff0: ldr     s15, [x13]
    +0x2ff4: add     x13, x11, #0x54
    +0x2ff8: st1     {v19.2d-v22.2d}, [x12]
    +0x2ffc: add     x12, sp, #0x10
    +0x3000: add     x17, x11, #0xd4
    +0x3004: add     x16, x11, #0xb4
    +0x3008: add     x18, x11, #0xf4
    +0x300c: add     x0, x11, #0x134
    +0x3010: ld1     {v18.s}[1], [x16]
    +0x3014: ldp     s20, s6, [x11, #24]
    +0x3018: add     x1, x11, #0xd8
    +0x301c: ldp     s19, s21, [x11, #152]
    +0x3020: st1     {v23.2d-v26.2d}, [x12]
    +0x3024: add     x12, x11, #0x130
    +0x3028: ldr     s24, [x11, #404]
    +0x302c: ld1     {v14.s}[1], [x12]
    +0x3030: add     x12, x11, #0x34
    +0x3034: ldr     s4, [x1]
    +0x3038: ld1     {v17.s}[1], [x12]
    +0x303c: add     x12, x11, #0x174
    +0x3040: add     x14, x11, #0x170
    +0x3044: ld1     {v15.s}[1], [x14]
    +0x3048: add     x2, x11, #0x158
    +0x304c: ldr     s5, [x11, #280]
    +0x3050: st1     {v0.2d-v3.2d}, [x15]
    +0x3054: ldr     s0, [x13]
    +0x3058: add     x15, x11, #0x74
    +0x305c: ldr     s1, [x17]
    +0x3060: add     x13, x11, #0x154
    +0x3064: ldr     s2, [x11, #276]
    +0x3068: ld1     {v0.s}[1], [x15]
    +0x306c: ldr     s3, [x13]
    +0x3070: add     x13, x11, #0x1b4
    +0x3074: ld1     {v1.s}[1], [x18]
    +0x3078: ld1     {v2.s}[1], [x0]
    +0x307c: add     x0, x11, #0x58
    +0x3080: ld1     {v3.s}[1], [x12]
    +0x3084: add     x12, x11, #0x1d4
    +0x3088: add     x18, x11, #0x38
    +0x308c: zip1    v10.2d, v17.2d, v0.2d
    +0x3090: ldr     s16, [x12]
    +0x3094: add     x12, x11, #0x1f4
    +0x3098: zip1    v11.2d, v18.2d, v1.2d
    +0x309c: ldr     s1, [x0]
    +0x30a0: add     x17, x11, #0x78
    +0x30a4: ld1     {v24.s}[1], [x13]
    +0x30a8: ld1     {v16.s}[1], [x12]
    +0x30ac: add     x12, x11, #0xb8
    +0x30b0: add     x13, x11, #0xf8
    +0x30b4: ld1     {v20.s}[1], [x18]
    +0x30b8: ld1     {v1.s}[1], [x17]
    +0x30bc: zip1    v12.2d, v2.2d, v3.2d
    +0x30c0: ld1     {v19.s}[1], [x12]
    +0x30c4: ld1     {v4.s}[1], [x13]
    +0x30c8: ldr     s2, [x11, #408]
    +0x30cc: add     x12, x11, #0x1b8
    +0x30d0: add     x15, x11, #0x1d8
    +0x30d4: zip1    v28.2d, v20.2d, v1.2d
    +0x30d8: ldr     s3, [x2]
    +0x30dc: add     x14, x11, #0x138
    +0x30e0: ld1     {v2.s}[1], [x12]
    +0x30e4: add     x12, sp, #0x110
    +0x30e8: zip1    v29.2d, v19.2d, v4.2d
    +0x30ec: ld1     {v17.2d-v20.2d}, [x12]
    +0x30f0: add     x16, x11, #0x178
    +0x30f4: ldr     s0, [x15]
    +0x30f8: zip1    v19.2d, v14.2d, v15.2d
    +0x30fc: add     x12, sp, #0x110
    +0x3100: ld1     {v5.s}[1], [x14]
    +0x3104: ld1     {v3.s}[1], [x16]
    +0x3108: add     x13, x11, #0x1f8
    +0x310c: zip1    v13.2d, v24.2d, v16.2d
    +0x3110: ld1     {v0.s}[1], [x13]
    +0x3114: add     x15, x11, #0x160
    +0x3118: add     x18, x11, #0x1d0
    +0x311c: ldr     s9, [x18]
    +0x3120: add     x14, x11, #0x120
    +0x3124: ldr     s8, [x11, #400]
    +0x3128: st1     {v17.2d-v20.2d}, [x12]
    +0x312c: add     x12, x11, #0x140
    +0x3130: zip1    v30.2d, v5.2d, v3.2d
    +0x3134: ldr     s16, [x12]
    +0x3138: ldr     s17, [x11, #256]
    +0x313c: zip1    v31.2d, v2.2d, v0.2d
    +0x3140: ldr     s0, [x11, #396]
    +0x3144: add     x17, x11, #0x1ec
    +0x3148: add     x0, x11, #0xdc
    +0x314c: ld1     {v16.s}[1], [x15]
    +0x3150: add     x15, x11, #0x1cc
    +0x3154: ld1     {v17.s}[1], [x14]
    +0x3158: ldr     s1, [x15]
    +0x315c: add     x15, x11, #0x1f0
    +0x3160: add     x14, x11, #0x1ac
    +0x3164: ld1     {v9.s}[1], [x15]
    +0x3168: add     x15, x11, #0x5c
    +0x316c: ld1     {v0.s}[1], [x14]
    +0x3170: add     x14, x11, #0x1b0
    +0x3174: ldr     s4, [x15]
    +0x3178: ld1     {v1.s}[1], [x17]
    +0x317c: ld1     {v8.s}[1], [x14]
    +0x3180: add     x14, x11, #0x3c
    +0x3184: add     x17, x11, #0x7c
    +0x3188: ldr     s19, [x0]
    +0x318c: add     x18, x11, #0xbc
    +0x3190: add     x1, x11, #0xfc
    +0x3194: add     x3, x11, #0x15c
    +0x3198: ld1     {v6.s}[1], [x14]
    +0x319c: ld1     {v4.s}[1], [x17]
    +0x31a0: ldr     s2, [x11, #284]
    +0x31a4: ld1     {v21.s}[1], [x18]
    +0x31a8: ld1     {v19.s}[1], [x1]
    +0x31ac: ldr     s3, [x3]
    +0x31b0: add     x16, x11, #0x1c0
    +0x31b4: add     x2, x11, #0x13c
    +0x31b8: add     x4, x11, #0x17c
    +0x31bc: add     x12, x11, #0x1a0
    +0x31c0: add     x13, x11, #0x1e0
    +0x31c4: add     x5, x11, #0x1bc
    +0x31c8: add     x14, x11, #0x1dc
    +0x31cc: add     x15, x11, #0x1fc
    +0x31d0: ld1     {v2.s}[1], [x2]
    +0x31d4: ldr     s18, [x11, #412]
    +0x31d8: ld1     {v3.s}[1], [x4]
    +0x31dc: ldr     s14, [x11, #384]
    +0x31e0: ldr     s15, [x16]
    +0x31e4: zip1    v4.2d, v6.2d, v4.2d
    +0x31e8: add     x11, sp, #0x10
    +0x31ec: zip1    v5.2d, v21.2d, v19.2d
    +0x31f0: ldr     s27, [x14]
    +0x31f4: ld1     {v19.2d-v22.2d}, [x11]
    +0x31f8: add     x11, sp, #0x110
    +0x31fc: ld1     {v14.s}[1], [x12]
    +0x3200: ld1     {v15.s}[1], [x13]
    +0x3204: ld1     {v23.2d-v26.2d}, [x11]
    +0x3208: add     x11, sp, #0x90
    +0x320c: zip1    v22.2d, v0.2d, v1.2d
    +0x3210: zip1    v6.2d, v2.2d, v3.2d
    +0x3214: ld1     {v0.2d-v3.2d}, [x11]
    +0x3218: ld1     {v18.s}[1], [x5]
    +0x321c: ld1     {v27.s}[1], [x15]
    +0x3220: zip1    v2.2d, v17.2d, v16.2d
    +0x3224: zip1    v3.2d, v14.2d, v15.2d
    +0x3228: add     x11, sp, #0xd0
    +0x322c: zip1    v26.2d, v8.2d, v9.2d
    +0x3230: mov     v8.16b, v0.16b
    +0x3234: mov     v9.16b, v1.16b
    +0x3238: zip1    v7.2d, v18.2d, v27.2d
    +0x323c: ldr     q18, [sp, #336]
    +0x3240: tbl     v27.16b, {v10.16b-v13.16b}, v18.16b
    +0x3244: mov     v10.16b, v2.16b
    +0x3248: mov     v11.16b, v3.16b
    +0x324c: ld1     {v0.2d-v3.2d}, [x11]
    +0x3250: add     x11, sp, #0x50
    +0x3254: tbl     v28.16b, {v28.16b-v31.16b}, v18.16b
    +0x3258: tbl     v17.16b, {v23.16b-v26.16b}, v18.16b
    +0x325c: tbl     v16.16b, {v19.16b-v22.16b}, v18.16b
    +0x3260: tbl     v29.16b, {v0.16b-v3.16b}, v18.16b
    +0x3264: ld1     {v0.2d-v3.2d}, [x11]
    +0x3268: add     x11, x19, x9
    +0x326c: add     x9, x9, #0x30
    +0x3270: cmp     x9, #0x320
    +0x3274: tbl     v30.16b, {v0.16b-v3.16b}, v18.16b
    +0x3278: tbl     v0.16b, {v4.16b-v7.16b}, v18.16b
    +0x327c: tbl     v1.16b, {v8.16b-v11.16b}, v18.16b
    +0x3280: movi    v18.16b, #0x2
    +0x3284: shl     v7.16b, v17.16b, #4
    +0x3288: movi    v17.16b, #0x8
    +0x328c: shl     v3.16b, v28.16b, #2
    +0x3290: add     v6.16b, v16.16b, v16.16b
    +0x3294: shl     v5.16b, v29.16b, #3
    +0x3298: shl     v0.16b, v0.16b, #5
    +0x329c: sub     v2.16b, v18.16b, v27.16b
    +0x32a0: sub     v4.16b, v18.16b, v30.16b
    +0x32a4: sub     v1.16b, v18.16b, v1.16b
    +0x32a8: movi    v18.16b, #0x4
    +0x32ac: sub     v3.16b, v17.16b, v3.16b
    +0x32b0: movi    v17.16b, #0x10
    +0x32b4: ushr    v16.16b, v2.16b, #1
    +0x32b8: shl     v2.16b, v2.16b, #7
    +0x32bc: sub     v6.16b, v18.16b, v6.16b
    +0x32c0: movi    v18.16b, #0x20
    +0x32c4: sub     v5.16b, v17.16b, v5.16b
    +0x32c8: orr     v3.16b, v3.16b, v16.16b
    +0x32cc: movi    v16.16b, #0x40
    +0x32d0: ushr    v17.16b, v4.16b, #2
    +0x32d4: shl     v4.16b, v4.16b, #6
    +0x32d8: orr     v1.16b, v5.16b, v1.16b
    +0x32dc: sub     v7.16b, v18.16b, v7.16b
    +0x32e0: orr     v5.16b, v6.16b, v17.16b
    +0x32e4: sub     v0.16b, v16.16b, v0.16b
    +0x32e8: orr     v2.16b, v7.16b, v2.16b
    +0x32ec: orr     v18.16b, v3.16b, v0.16b
    +0x32f0: orr     v16.16b, v1.16b, v4.16b
    +0x32f4: orr     v17.16b, v5.16b, v2.16b
    +0x32f8: st3     {v16.16b-v18.16b}, [x11]
    +0x32fc: b.ne    <mldsa87_keypair_internal+0x2df8>
    +0x3300: str     xzr, [sp, #7776]
    +0x3304: add     x8, sp, #0x1, lsl #12
    +0x3308: add     x0, sp, #0x160
    +0x330c: add     x8, x8, #0xe60
    +0x3310: add     x1, x22, #0x400
    +0x3314: mov     w8, #0x3
    +0x3318: add     x2, x22, #0x800
    +0x331c: add     x3, x22, #0xc00
    +0x3320: add     x4, x26, #0x20
    +0x3324: mov     w5, wzr
    +0x3328: mov     w6, #0x1
    +0x332c: mov     w7, #0x2
    +0x3330: strb    w8, [sp]
    +0x3334: bl      <mldsa87_poly_uniform_eta_4x>
    +0x3338: movi    v0.16b, #0x2
    +0x333c: movi    v5.16b, #0x20
    +0x3340: add     x8, sp, #0x160
    +0x3344: ldr     q15, [sp, #336]
    +0x3348: add     x8, x8, #0x100
    +0x334c: mov     w9, #0x80
    +0x3350: ldp     s16, s1, [x8, #-240]
    +0x3354: sub     x10, x8, #0xd0
    +0x3358: sub     x11, x8, #0xcc
    +0x335c: sub     x12, x8, #0xac
    +0x3360: sub     x15, x8, #0x90
    +0x3364: sub     x16, x8, #0x8c
    +0x3368: ldp     s20, s24, [x8, #-256]
    +0x336c: ld1     {v16.s}[1], [x10]
    +0x3370: ld1     {v1.s}[1], [x11]
    +0x3374: sub     x11, x8, #0xb0
    +0x3378: sub     x10, x8, #0xe0
    +0x337c: sub     x14, x8, #0xdc
    +0x3380: sub     x13, x8, #0xc0
    +0x3384: ld1     {v20.s}[1], [x10]
    +0x3388: sub     x10, x8, #0x50
    +0x338c: ld1     {v24.s}[1], [x14]
    +0x3390: ld1     {v16.s}[2], [x11]
    +0x3394: ld1     {v1.s}[2], [x12]
    +0x3398: sub     x11, x8, #0xa0
    +0x339c: sub     x12, x8, #0x60
    +0x33a0: sub     x14, x8, #0x40
    +0x33a4: add     x0, x8, #0xf4
    +0x33a8: ld1     {v20.s}[2], [x13]
    +0x33ac: sub     x13, x8, #0x30
    +0x33b0: add     x17, x8, #0xa4
    +0x33b4: ld1     {v16.s}[3], [x15]
    +0x33b8: ld1     {v1.s}[3], [x16]
    +0x33bc: sub     x15, x8, #0x4c
    +0x33c0: ldp     s17, s2, [x8, #-112]
    +0x33c4: sub     x16, x8, #0x2c
    +0x33c8: ld1     {v20.s}[3], [x11]
    +0x33cc: sub     x11, x8, #0xc
    +0x33d0: sub     x18, x8, #0xd8
    +0x33d4: ldp     s28, s6, [x8, #-248]
    +0x33d8: ld1     {v17.s}[1], [x10]
    +0x33dc: ld1     {v2.s}[1], [x15]
    +0x33e0: sub     x15, x8, #0xbc
    +0x33e4: ld1     {v24.s}[2], [x15]
    +0x33e8: sub     x15, x8, #0x9c
    +0x33ec: sub     x10, x8, #0x20
    +0x33f0: ld1     {v28.s}[1], [x18]
    +0x33f4: ld1     {v17.s}[2], [x13]
    +0x33f8: ld1     {v2.s}[2], [x16]
    +0x33fc: sub     x16, x8, #0x10
    +0x3400: ld1     {v24.s}[3], [x15]
    +0x3404: sub     x13, x8, #0x5c
    +0x3408: add     x15, x8, #0x54
    +0x340c: ldp     s21, s25, [x8, #-128]
    +0x3410: ld1     {v17.s}[3], [x16]
    +0x3414: ld1     {v2.s}[3], [x11]
    +0x3418: add     x11, x8, #0x30
    +0x341c: ldp     s18, s3, [x8, #16]
    +0x3420: add     x16, x8, #0x60
    +0x3424: ld1     {v21.s}[1], [x12]
    +0x3428: add     x12, x8, #0x34
    +0x342c: ld1     {v25.s}[1], [x13]
    +0x3430: add     x13, x8, #0x20
    +0x3434: ld1     {v18.s}[1], [x11]
    +0x3438: ld1     {v3.s}[1], [x12]
    +0x343c: sub     x11, x8, #0x3c
    +0x3440: ld1     {v21.s}[2], [x14]
    +0x3444: add     x14, x8, #0x50
    +0x3448: ld1     {v25.s}[2], [x11]
    +0x344c: sub     x11, x8, #0x1c
    +0x3450: add     x12, x8, #0x40
    +0x3454: ld1     {v18.s}[2], [x14]
    +0x3458: ld1     {v3.s}[2], [x15]
    +0x345c: add     x14, x8, #0x70
    +0x3460: ld1     {v21.s}[3], [x10]
    +0x3464: add     x10, x8, #0x74
    +0x3468: ld1     {v25.s}[3], [x11]
    +0x346c: ldp     s22, s26, [x8]
    +0x3470: add     x15, x8, #0xa0
    +0x3474: ld1     {v18.s}[3], [x14]
    +0x3478: ld1     {v3.s}[3], [x10]
    +0x347c: add     x10, x8, #0x24
    +0x3480: ldp     s19, s4, [x8, #144]
    +0x3484: add     x14, x8, #0xb4
    +0x3488: ld1     {v22.s}[1], [x13]
    +0x348c: ld1     {v26.s}[1], [x10]
    +0x3490: add     x10, x8, #0x44
    +0x3494: add     x13, x8, #0x64
    +0x3498: add     x11, x8, #0xc0
    +0x349c: ld1     {v4.s}[1], [x14]
    +0x34a0: add     x14, x8, #0xd4
    +0x34a4: ld1     {v22.s}[2], [x12]
    +0x34a8: ld1     {v26.s}[2], [x10]
    +0x34ac: add     x12, x8, #0xc4
    +0x34b0: add     x10, x8, #0xe4
    +0x34b4: ld1     {v4.s}[2], [x14]
    +0x34b8: sub     x14, x8, #0xb8
    +0x34bc: ld1     {v22.s}[3], [x16]
    +0x34c0: ld1     {v26.s}[3], [x13]
    +0x34c4: sub     x16, x8, #0xc8
    +0x34c8: ldp     s23, s27, [x8, #128]
    +0x34cc: ld1     {v28.s}[2], [x14]
    +0x34d0: ld1     {v4.s}[3], [x0]
    +0x34d4: sub     x14, x8, #0xc4
    +0x34d8: sub     x13, x8, #0x98
    +0x34dc: ld1     {v23.s}[1], [x15]
    +0x34e0: ld1     {v27.s}[1], [x17]
    +0x34e4: sub     x15, x8, #0xd4
    +0x34e8: tbl     v10.16b, {v1.16b-v4.16b}, v15.16b
    +0x34ec: ldp     s11, s1, [x8, #-232]
    +0x34f0: ld1     {v6.s}[1], [x15]
    +0x34f4: ld1     {v28.s}[3], [x13]
    +0x34f8: sub     x13, x8, #0xa4
    +0x34fc: ld1     {v27.s}[2], [x12]
    +0x3500: sub     x12, x8, #0xb4
    +0x3504: ld1     {v23.s}[2], [x11]
    +0x3508: ld1     {v11.s}[1], [x16]
    +0x350c: ld1     {v1.s}[1], [x14]
    +0x3510: sub     x11, x8, #0x58
    +0x3514: ld1     {v6.s}[2], [x12]
    +0x3518: sub     x12, x8, #0xa8
    +0x351c: sub     x14, x8, #0x38
    +0x3520: ld1     {v27.s}[3], [x10]
    +0x3524: sub     x10, x8, #0x14
    +0x3528: add     x15, x8, #0x78
    +0x352c: ld1     {v11.s}[2], [x12]
    +0x3530: sub     x12, x8, #0x94
    +0x3534: ld1     {v1.s}[2], [x13]
    +0x3538: ld1     {v6.s}[3], [x12]
    +0x353c: sub     x12, x8, #0x88
    +0x3540: sub     x13, x8, #0x44
    +0x3544: ldp     s29, s7, [x8, #-120]
    +0x3548: tbl     v24.16b, {v24.16b-v27.16b}, v15.16b
    +0x354c: ld1     {v11.s}[3], [x12]
    +0x3550: sub     x12, x8, #0x84
    +0x3554: ld1     {v1.s}[3], [x12]
    +0x3558: sub     x12, x8, #0x34
    +0x355c: ld1     {v29.s}[1], [x11]
    +0x3560: ldp     s12, s2, [x8, #-104]
    +0x3564: sub     x11, x8, #0x54
    +0x3568: ld1     {v7.s}[1], [x11]
    +0x356c: sub     x11, x8, #0x48
    +0x3570: ld1     {v29.s}[2], [x14]
    +0x3574: ld1     {v12.s}[1], [x11]
    +0x3578: ld1     {v2.s}[1], [x13]
    +0x357c: sub     x11, x8, #0x18
    +0x3580: add     x13, x8, #0x4c
    +0x3584: add     x14, x8, #0x58
    +0x3588: ld1     {v7.s}[2], [x12]
    +0x358c: sub     x12, x8, #0x28
    +0x3590: ld1     {v29.s}[3], [x11]
    +0x3594: ld1     {v12.s}[2], [x12]
    +0x3598: sub     x11, x8, #0x24
    +0x359c: ld1     {v2.s}[2], [x11]
    +0x35a0: add     x11, x8, #0x28
    +0x35a4: add     x12, x8, #0x38
    +0x35a8: ld1     {v7.s}[3], [x10]
    +0x35ac: sub     x10, x8, #0x8
    +0x35b0: ld1     {v12.s}[3], [x10]
    +0x35b4: sub     x10, x8, #0x4
    +0x35b8: ldp     s30, s8, [x8, #8]
    +0x35bc: ld1     {v2.s}[3], [x10]
    +0x35c0: ldp     s13, s3, [x8, #24]
    +0x35c4: add     x10, x8, #0x48
    +0x35c8: ld1     {v30.s}[1], [x11]
    +0x35cc: add     x11, x8, #0x2c
    +0x35d0: ld1     {v8.s}[1], [x11]
    +0x35d4: ld1     {v13.s}[1], [x12]
    +0x35d8: add     x12, x8, #0x3c
    +0x35dc: ld1     {v3.s}[1], [x12]
    +0x35e0: add     x11, x8, #0x68
    +0x35e4: add     x12, x8, #0xc8
    +0x35e8: ld1     {v30.s}[2], [x10]
    +0x35ec: add     x10, x8, #0xa8
    +0x35f0: ld1     {v8.s}[2], [x13]
    +0x35f4: add     x13, x8, #0x5c
    +0x35f8: ld1     {v13.s}[2], [x14]
    +0x35fc: ld1     {v3.s}[2], [x13]
    +0x3600: add     x14, x8, #0x6c
    +0x3604: add     x13, x8, #0xb8
    +0x3608: ld1     {v30.s}[3], [x11]
    +0x360c: add     x11, x8, #0x7c
    +0x3610: ld1     {v13.s}[3], [x15]
    +0x3614: ld1     {v8.s}[3], [x14]
    +0x3618: ld1     {v3.s}[3], [x11]
    +0x361c: ldp     s31, s9, [x8, #136]
    +0x3620: ldp     s14, s4, [x8, #152]
    +0x3624: add     x11, x8, #0xac
    +0x3628: ld1     {v31.s}[1], [x10]
    +0x362c: add     x10, x8, #0xb0
    +0x3630: ld1     {v9.s}[1], [x11]
    +0x3634: ld1     {v14.s}[1], [x13]
    +0x3638: ld1     {v19.s}[1], [x10]
    +0x363c: add     x10, x8, #0xd8
    +0x3640: add     x11, x8, #0xbc
    +0x3644: add     x13, x8, #0xcc
    +0x3648: ld1     {v4.s}[1], [x11]
    +0x364c: ld1     {v9.s}[2], [x13]
    +0x3650: add     x11, x8, #0xdc
    +0x3654: ld1     {v14.s}[2], [x10]
    +0x3658: add     x10, x8, #0xd0
    +0x365c: ld1     {v31.s}[2], [x12]
    +0x3660: ld1     {v19.s}[2], [x10]
    +0x3664: add     x10, x8, #0xf8
    +0x3668: add     x12, x8, #0xe8
    +0x366c: ld1     {v4.s}[2], [x11]
    +0x3670: add     x11, x8, #0xf0
    +0x3674: ld1     {v14.s}[3], [x10]
    +0x3678: add     x10, x8, #0xec
    +0x367c: ld1     {v31.s}[3], [x12]
    +0x3680: ld1     {v9.s}[3], [x10]
    +0x3684: ld1     {v19.s}[3], [x11]
    +0x3688: add     x10, x8, #0xfc
    +0x368c: ld1     {v4.s}[3], [x10]
    +0x3690: add     x11, x8, #0xe0
    +0x3694: add     x10, x19, x9
    +0x3698: tbl     v11.16b, {v11.16b-v14.16b}, v15.16b
    +0x369c: ld1     {v23.s}[3], [x11]
    +0x36a0: tbl     v25.16b, {v28.16b-v31.16b}, v15.16b
    +0x36a4: tbl     v6.16b, {v6.16b-v9.16b}, v15.16b
    +0x36a8: tbl     v7.16b, {v16.16b-v19.16b}, v15.16b
    +0x36ac: movi    v19.16b, #0x8
    +0x36b0: tbl     v1.16b, {v1.16b-v4.16b}, v15.16b
    +0x36b4: sub     v3.16b, v0.16b, v10.16b
    +0x36b8: shl     v17.16b, v24.16b, #3
    +0x36bc: tbl     v2.16b, {v20.16b-v23.16b}, v15.16b
    +0x36c0: movi    v20.16b, #0x4
    +0x36c4: add     x9, x9, #0x30
    +0x36c8: shl     v4.16b, v11.16b, #2
    +0x36cc: sub     v16.16b, v0.16b, v25.16b
    +0x36d0: cmp     x9, #0xe0
    +0x36d4: ushr    v18.16b, v3.16b, #1
    +0x36d8: add     v6.16b, v6.16b, v6.16b
    +0x36dc: shl     v7.16b, v7.16b, #4
    +0x36e0: shl     v1.16b, v1.16b, #5
    +0x36e4: shl     v3.16b, v3.16b, #7
    +0x36e8: add     x8, x8, #0x200
    +0x36ec: sub     v4.16b, v19.16b, v4.16b
    +0x36f0: movi    v19.16b, #0x10
    +0x36f4: sub     v2.16b, v0.16b, v2.16b
    +0x36f8: sub     v6.16b, v20.16b, v6.16b
    +0x36fc: sub     v7.16b, v5.16b, v7.16b
    +0x3700: orr     v4.16b, v4.16b, v18.16b
    +0x3704: movi    v18.16b, #0x40
    +0x3708: sub     v17.16b, v19.16b, v17.16b
    +0x370c: ushr    v19.16b, v16.16b, #2
    +0x3710: shl     v16.16b, v16.16b, #6
    +0x3714: orr     v3.16b, v7.16b, v3.16b
    +0x3718: sub     v1.16b, v18.16b, v1.16b
    +0x371c: orr     v2.16b, v17.16b, v2.16b
    +0x3720: orr     v6.16b, v6.16b, v19.16b
    +0x3724: orr     v19.16b, v4.16b, v1.16b
    +0x3728: orr     v17.16b, v2.16b, v16.16b
    +0x372c: orr     v18.16b, v6.16b, v3.16b
    +0x3730: st3     {v17.16b-v19.16b}, [x10]
    +0x3734: b.ne    <mldsa87_keypair_internal+0x3350>
    +0x3738: str     xzr, [sp, #7776]
    +0x373c: add     x8, sp, #0x1, lsl #12
    +0x3740: movi    v0.16b, #0x2
    +0x3744: movi    v5.16b, #0x20
    +0x3748: add     x8, x8, #0xe60
    +0x374c: ldr     q15, [sp, #336]
    +0x3750: mov     w8, #0xe0
    +0x3754: ldp     s16, s1, [x25, #16]
    +0x3758: add     x9, x25, #0x30
    +0x375c: add     x10, x25, #0x34
    +0x3760: add     x12, x25, #0x50
    +0x3764: add     x13, x25, #0x54
    +0x3768: ldp     s20, s24, [x25]
    +0x376c: add     x14, x25, #0x70
    +0x3770: ld1     {v16.s}[1], [x9]
    +0x3774: ld1     {v1.s}[1], [x10]
    +0x3778: add     x9, x25, #0x20
    +0x377c: add     x15, x25, #0x74
    +0x3780: add     x10, x25, #0x40
    +0x3784: add     x11, x25, #0x60
    +0x3788: ld1     {v20.s}[1], [x9]
    +0x378c: add     x9, x25, #0x44
    +0x3790: add     x17, x25, #0xd4
    +0x3794: ld1     {v16.s}[2], [x12]
    +0x3798: ld1     {v1.s}[2], [x13]
    +0x379c: add     x12, x25, #0x24
    +0x37a0: ld1     {v24.s}[1], [x12]
    +0x37a4: add     x12, x25, #0xb4
    +0x37a8: add     x0, x25, #0xf4
    +0x37ac: ld1     {v20.s}[2], [x10]
    +0x37b0: add     x18, x25, #0xc4
    +0x37b4: add     x13, x25, #0xa0
    +0x37b8: ld1     {v16.s}[3], [x14]
    +0x37bc: ld1     {v1.s}[3], [x15]
    +0x37c0: add     x16, x25, #0xc0
    +0x37c4: ldp     s17, s2, [x25, #144]
    +0x37c8: ld1     {v24.s}[2], [x9]
    +0x37cc: add     x9, x25, #0x64
    +0x37d0: ld1     {v20.s}[3], [x11]
    +0x37d4: add     x14, x25, #0xe0
    +0x37d8: ldp     s28, s6, [x25, #8]
    +0x37dc: add     x15, x25, #0x120
    +0x37e0: ld1     {v2.s}[1], [x12]
    +0x37e4: ld1     {v24.s}[3], [x9]
    +0x37e8: add     x1, x25, #0x124
    +0x37ec: ldp     s21, s25, [x25, #128]
    +0x37f0: add     x12, x25, #0x140
    +0x37f4: add     x10, x25, #0x160
    +0x37f8: add     x11, x25, #0x1a0
    +0x37fc: add     x9, x25, #0x1c0
    +0x3800: ld1     {v2.s}[2], [x17]
    +0x3804: add     x17, x25, #0xa4
    +0x3808: ld1     {v25.s}[1], [x17]
    +0x380c: ld1     {v21.s}[1], [x13]
    +0x3810: add     x17, x25, #0xe4
    +0x3814: add     x13, x25, #0x164
    +0x3818: ld1     {v2.s}[3], [x0]
    +0x381c: add     x0, x25, #0x144
    +0x3820: ldr     s3, [x25, #276]
    +0x3824: ld1     {v25.s}[2], [x18]
    +0x3828: add     x18, x25, #0x134
    +0x382c: ld1     {v21.s}[2], [x16]
    +0x3830: add     x16, x25, #0x48
    +0x3834: ld1     {v3.s}[1], [x18]
    +0x3838: add     x18, x25, #0x28
    +0x383c: ld1     {v28.s}[1], [x18]
    +0x3840: add     x18, x25, #0x154
    +0x3844: ld1     {v25.s}[3], [x17]
    +0x3848: ld1     {v21.s}[3], [x14]
    +0x384c: add     x14, x25, #0x174
    +0x3850: ldr     s26, [x25, #260]
    +0x3854: ld1     {v3.s}[2], [x18]
    +0x3858: add     x18, x25, #0x2c
    +0x385c: ldr     s22, [x25, #256]
    +0x3860: ld1     {v6.s}[1], [x18]
    +0x3864: ld1     {v28.s}[2], [x16]
    +0x3868: add     x16, x25, #0x4c
    +0x386c: add     x17, x25, #0x68
    +0x3870: ld1     {v26.s}[1], [x1]
    +0x3874: ld1     {v22.s}[1], [x15]
    +0x3878: ld1     {v3.s}[3], [x14]
    +0x387c: add     x14, x25, #0x6c
    +0x3880: add     x15, x25, #0x1b4
    +0x3884: ld1     {v6.s}[2], [x16]
    +0x3888: ldr     s4, [x25, #404]
    +0x388c: ld1     {v28.s}[3], [x17]
    +0x3890: ld1     {v26.s}[2], [x0]
    +0x3894: ld1     {v22.s}[2], [x12]
    +0x3898: add     x12, x25, #0x1d4
    +0x389c: ld1     {v4.s}[1], [x15]
    +0x38a0: add     x15, x25, #0xa8
    +0x38a4: ld1     {v6.s}[3], [x14]
    +0x38a8: add     x14, x25, #0x1a4
    +0x38ac: ldp     s29, s7, [x25, #136]
    +0x38b0: ld1     {v26.s}[3], [x13]
    +0x38b4: ld1     {v4.s}[2], [x12]
    +0x38b8: add     x12, x25, #0xc8
    +0x38bc: ld1     {v22.s}[3], [x10]
    +0x38c0: add     x10, x25, #0x1f4
    +0x38c4: ldr     s27, [x25, #388]
    +0x38c8: ldr     s23, [x25, #384]
    +0x38cc: ld1     {v29.s}[1], [x15]
    +0x38d0: add     x13, x25, #0xe8
    +0x38d4: ld1     {v4.s}[3], [x10]
    +0x38d8: ld1     {v27.s}[1], [x14]
    +0x38dc: ld1     {v23.s}[1], [x11]
    +0x38e0: add     x10, x25, #0x128
    +0x38e4: add     x11, x25, #0x38
    +0x38e8: ld1     {v29.s}[2], [x12]
    +0x38ec: add     x12, x25, #0x1c4
    +0x38f0: tbl     v10.16b, {v1.16b-v4.16b}, v15.16b
    +0x38f4: ldp     s11, s1, [x25, #24]
    +0x38f8: ld1     {v27.s}[2], [x12]
    +0x38fc: ld1     {v23.s}[2], [x9]
    +0x3900: add     x9, x25, #0x1e4
    +0x3904: ld1     {v29.s}[3], [x13]
    +0x3908: add     x13, x25, #0x78
    +0x390c: add     x12, x25, #0x1a8
    +0x3910: ldr     s30, [x25, #264]
    +0x3914: ld1     {v11.s}[1], [x11]
    +0x3918: add     x11, x25, #0x168
    +0x391c: ld1     {v27.s}[3], [x9]
    +0x3920: add     x9, x25, #0x58
    +0x3924: ld1     {v30.s}[1], [x10]
    +0x3928: add     x10, x25, #0x3c
    +0x392c: ld1     {v1.s}[1], [x10]
    +0x3930: ld1     {v11.s}[2], [x9]
    +0x3934: add     x9, x25, #0x5c
    +0x3938: add     x10, x25, #0x148
    +0x393c: tbl     v24.16b, {v24.16b-v27.16b}, v15.16b
    +0x3940: ld1     {v30.s}[2], [x10]
    +0x3944: add     x10, x25, #0xac
    +0x3948: ld1     {v1.s}[2], [x9]
    +0x394c: ld1     {v7.s}[1], [x10]
    +0x3950: add     x10, x25, #0x7c
    +0x3954: ld1     {v11.s}[3], [x13]
    +0x3958: add     x13, x25, #0xb8
    +0x395c: add     x9, x25, #0x1c8
    +0x3960: ld1     {v30.s}[3], [x11]
    +0x3964: add     x11, x25, #0xcc
    +0x3968: ld1     {v1.s}[3], [x10]
    +0x396c: ld1     {v7.s}[2], [x11]
    +0x3970: add     x11, x25, #0xb0
    +0x3974: ldp     s12, s2, [x25, #152]
    +0x3978: ld1     {v17.s}[1], [x11]
    +0x397c: add     x11, x25, #0xd8
    +0x3980: add     x10, x25, #0xec
    +0x3984: ldr     s31, [x25, #392]
    +0x3988: ld1     {v7.s}[3], [x10]
    +0x398c: add     x10, x25, #0xd0
    +0x3990: ld1     {v12.s}[1], [x13]
    +0x3994: add     x13, x25, #0xbc
    +0x3998: ld1     {v17.s}[2], [x10]
    +0x399c: ld1     {v2.s}[1], [x13]
    +0x39a0: add     x10, x25, #0xf8
    +0x39a4: ldr     s8, [x25, #268]
    +0x39a8: ld1     {v31.s}[1], [x12]
    +0x39ac: add     x12, x25, #0x12c
    +0x39b0: add     x13, x25, #0x15c
    +0x39b4: ld1     {v12.s}[2], [x11]
    +0x39b8: add     x11, x25, #0xdc
    +0x39bc: ld1     {v8.s}[1], [x12]
    +0x39c0: ld1     {v2.s}[2], [x11]
    +0x39c4: add     x11, x25, #0xfc
    +0x39c8: add     x12, x25, #0x13c
    +0x39cc: ld1     {v31.s}[2], [x9]
    +0x39d0: add     x9, x25, #0x1d0
    +0x39d4: ld1     {v12.s}[3], [x10]
    +0x39d8: add     x10, x25, #0xf0
    +0x39dc: ldr     s13, [x25, #280]
    +0x39e0: ld1     {v17.s}[3], [x10]
    +0x39e4: add     x10, x25, #0x138
    +0x39e8: ldr     s18, [x25, #272]
    +0x39ec: ld1     {v2.s}[3], [x11]
    +0x39f0: add     x11, x25, #0x130
    +0x39f4: ld1     {v13.s}[1], [x10]
    +0x39f8: ldr     s3, [x25, #284]
    +0x39fc: add     x10, x25, #0x14c
    +0x3a00: ld1     {v18.s}[1], [x11]
    +0x3a04: add     x11, x25, #0x158
    +0x3a08: ld1     {v8.s}[2], [x10]
    +0x3a0c: ld1     {v3.s}[1], [x12]
    +0x3a10: add     x12, x25, #0x150
    +0x3a14: add     x10, x25, #0x16c
    +0x3a18: ld1     {v13.s}[2], [x11]
    +0x3a1c: add     x11, x25, #0x1ac
    +0x3a20: ld1     {v18.s}[2], [x12]
    +0x3a24: add     x12, x25, #0x178
    +0x3a28: ld1     {v8.s}[3], [x10]
    +0x3a2c: ld1     {v3.s}[2], [x13]
    +0x3a30: add     x10, x25, #0x170
    +0x3a34: ldr     s9, [x25, #396]
    +0x3a38: ld1     {v13.s}[3], [x12]
    +0x3a3c: add     x12, x25, #0x17c
    +0x3a40: ldr     s14, [x25, #408]
    +0x3a44: ld1     {v18.s}[3], [x10]
    +0x3a48: add     x10, x25, #0x1b8
    +0x3a4c: ldr     s19, [x25, #400]
    +0x3a50: ld1     {v3.s}[3], [x12]
    +0x3a54: ld1     {v9.s}[1], [x11]
    +0x3a58: ld1     {v14.s}[1], [x10]
    +0x3a5c: add     x10, x25, #0x1b0
    +0x3a60: ldr     s4, [x25, #412]
    +0x3a64: ld1     {v19.s}[1], [x10]
    +0x3a68: add     x10, x25, #0x1d8
    +0x3a6c: add     x11, x25, #0x1bc
    +0x3a70: ld1     {v4.s}[1], [x11]
    +0x3a74: add     x12, x25, #0x1cc
    +0x3a78: add     x11, x25, #0x1e8
    +0x3a7c: ld1     {v14.s}[2], [x10]
    +0x3a80: ld1     {v9.s}[2], [x12]
    +0x3a84: add     x10, x25, #0x1dc
    +0x3a88: ld1     {v19.s}[2], [x9]
    +0x3a8c: add     x9, x25, #0x1f8
    +0x3a90: ld1     {v31.s}[3], [x11]
    +0x3a94: ld1     {v4.s}[2], [x10]
    +0x3a98: add     x10, x25, #0x1f0
    +0x3a9c: ld1     {v14.s}[3], [x9]
    +0x3aa0: add     x9, x25, #0x1ec
    +0x3aa4: ld1     {v9.s}[3], [x9]
    +0x3aa8: ld1     {v19.s}[3], [x10]
    +0x3aac: add     x9, x25, #0x1fc
    +0x3ab0: ld1     {v4.s}[3], [x9]
    +0x3ab4: add     x10, x25, #0x1e0
    +0x3ab8: tbl     v25.16b, {v28.16b-v31.16b}, v15.16b
    +0x3abc: tbl     v11.16b, {v11.16b-v14.16b}, v15.16b
    +0x3ac0: ld1     {v23.s}[3], [x10]
    +0x3ac4: add     x9, x19, x8
    +0x3ac8: tbl     v6.16b, {v6.16b-v9.16b}, v15.16b
    +0x3acc: tbl     v7.16b, {v16.16b-v19.16b}, v15.16b
    +0x3ad0: movi    v19.16b, #0x8
    +0x3ad4: tbl     v1.16b, {v1.16b-v4.16b}, v15.16b
    +0x3ad8: sub     v3.16b, v0.16b, v10.16b
    +0x3adc: shl     v17.16b, v24.16b, #3
    +0x3ae0: tbl     v2.16b, {v20.16b-v23.16b}, v15.16b
    +0x3ae4: movi    v20.16b, #0x4
    +0x3ae8: sub     v16.16b, v0.16b, v25.16b
    +0x3aec: shl     v4.16b, v11.16b, #2
    +0x3af0: add     x8, x8, #0x30
    +0x3af4: add     x25, x25, #0x200
    +0x3af8: ushr    v18.16b, v3.16b, #1
    +0x3afc: add     v6.16b, v6.16b, v6.16b
    +0x3b00: shl     v7.16b, v7.16b, #4
    +0x3b04: shl     v1.16b, v1.16b, #5
    +0x3b08: shl     v3.16b, v3.16b, #7
    +0x3b0c: cmp     x8, #0x140
    +0x3b10: sub     v4.16b, v19.16b, v4.16b
    +0x3b14: movi    v19.16b, #0x10
    +0x3b18: sub     v2.16b, v0.16b, v2.16b
    +0x3b1c: sub     v6.16b, v20.16b, v6.16b
    +0x3b20: sub     v7.16b, v5.16b, v7.16b
    +0x3b24: orr     v4.16b, v4.16b, v18.16b
    +0x3b28: movi    v18.16b, #0x40
    +0x3b2c: sub     v17.16b, v19.16b, v17.16b
    +0x3b30: ushr    v19.16b, v16.16b, #2
    +0x3b34: shl     v16.16b, v16.16b, #6
    +0x3b38: orr     v3.16b, v7.16b, v3.16b
    +0x3b3c: sub     v1.16b, v18.16b, v1.16b
    +0x3b40: orr     v2.16b, v17.16b, v2.16b
    +0x3b44: orr     v6.16b, v6.16b, v19.16b
    +0x3b48: orr     v19.16b, v4.16b, v1.16b
    +0x3b4c: orr     v17.16b, v2.16b, v16.16b
    +0x3b50: orr     v18.16b, v6.16b, v3.16b
    +0x3b54: st3     {v17.16b-v19.16b}, [x9]
    +0x3b58: b.ne    <mldsa87_keypair_internal+0x3754>
    +0x3b5c: str     xzr, [sp, #7776]
    +0x3b60: add     x8, sp, #0x1, lsl #12
    +0x3b64: movi    v0.16b, #0x2
    +0x3b68: movi    v5.16b, #0x20
    +0x3b6c: add     x8, x8, #0xe60
    +0x3b70: ldr     q15, [sp, #336]
    +0x3b74: mov     w8, #0x140
    +0x3b78: ldp     s16, s1, [x24, #16]
    +0x3b7c: add     x9, x24, #0x30
    +0x3b80: add     x10, x24, #0x34
    +0x3b84: add     x12, x24, #0x50
    +0x3b88: add     x13, x24, #0x54
    +0x3b8c: ldp     s20, s24, [x24]
    +0x3b90: add     x14, x24, #0x70
    +0x3b94: ld1     {v16.s}[1], [x9]
    +0x3b98: ld1     {v1.s}[1], [x10]
    +0x3b9c: add     x9, x24, #0x20
    +0x3ba0: add     x15, x24, #0x74
    +0x3ba4: add     x10, x24, #0x40
    +0x3ba8: add     x11, x24, #0x60
    +0x3bac: ld1     {v20.s}[1], [x9]
    +0x3bb0: add     x9, x24, #0x44
    +0x3bb4: add     x17, x24, #0xd4
    +0x3bb8: ld1     {v16.s}[2], [x12]
    +0x3bbc: ld1     {v1.s}[2], [x13]
    +0x3bc0: add     x12, x24, #0x24
    +0x3bc4: ld1     {v24.s}[1], [x12]
    +0x3bc8: add     x12, x24, #0xb4
    +0x3bcc: add     x0, x24, #0xf4
    +0x3bd0: ld1     {v20.s}[2], [x10]
    +0x3bd4: add     x18, x24, #0xc4
    +0x3bd8: add     x13, x24, #0xa0
    +0x3bdc: ld1     {v16.s}[3], [x14]
    +0x3be0: ld1     {v1.s}[3], [x15]
    +0x3be4: add     x16, x24, #0xc0
    +0x3be8: ldp     s17, s2, [x24, #144]
    +0x3bec: ld1     {v24.s}[2], [x9]
    +0x3bf0: add     x9, x24, #0x64
    +0x3bf4: ld1     {v20.s}[3], [x11]
    +0x3bf8: add     x14, x24, #0xe0
    +0x3bfc: ldp     s28, s6, [x24, #8]
    +0x3c00: add     x15, x24, #0x120
    +0x3c04: ld1     {v2.s}[1], [x12]
    +0x3c08: ld1     {v24.s}[3], [x9]
    +0x3c0c: add     x1, x24, #0x124
    +0x3c10: ldp     s21, s25, [x24, #128]
    +0x3c14: add     x12, x24, #0x140
    +0x3c18: add     x10, x24, #0x160
    +0x3c1c: add     x11, x24, #0x1a0
    +0x3c20: add     x9, x24, #0x1c0
    +0x3c24: ld1     {v2.s}[2], [x17]
    +0x3c28: add     x17, x24, #0xa4
    +0x3c2c: ld1     {v25.s}[1], [x17]
    +0x3c30: ld1     {v21.s}[1], [x13]
    +0x3c34: add     x17, x24, #0xe4
    +0x3c38: add     x13, x24, #0x164
    +0x3c3c: ld1     {v2.s}[3], [x0]
    +0x3c40: add     x0, x24, #0x144
    +0x3c44: ldr     s3, [x24, #276]
    +0x3c48: ld1     {v25.s}[2], [x18]
    +0x3c4c: add     x18, x24, #0x134
    +0x3c50: ld1     {v21.s}[2], [x16]
    +0x3c54: add     x16, x24, #0x48
    +0x3c58: ld1     {v3.s}[1], [x18]
    +0x3c5c: add     x18, x24, #0x28
    +0x3c60: ld1     {v28.s}[1], [x18]
    +0x3c64: add     x18, x24, #0x154
    +0x3c68: ld1     {v25.s}[3], [x17]
    +0x3c6c: ld1     {v21.s}[3], [x14]
    +0x3c70: add     x14, x24, #0x174
    +0x3c74: ldr     s26, [x24, #260]
    +0x3c78: ld1     {v3.s}[2], [x18]
    +0x3c7c: add     x18, x24, #0x2c
    +0x3c80: ldr     s22, [x24, #256]
    +0x3c84: ld1     {v6.s}[1], [x18]
    +0x3c88: ld1     {v28.s}[2], [x16]
    +0x3c8c: add     x16, x24, #0x4c
    +0x3c90: add     x17, x24, #0x68
    +0x3c94: ld1     {v26.s}[1], [x1]
    +0x3c98: ld1     {v22.s}[1], [x15]
    +0x3c9c: ld1     {v3.s}[3], [x14]
    +0x3ca0: add     x14, x24, #0x6c
    +0x3ca4: add     x15, x24, #0x1b4
    +0x3ca8: ld1     {v6.s}[2], [x16]
    +0x3cac: ldr     s4, [x24, #404]
    +0x3cb0: ld1     {v28.s}[3], [x17]
    +0x3cb4: ld1     {v26.s}[2], [x0]
    +0x3cb8: ld1     {v22.s}[2], [x12]
    +0x3cbc: add     x12, x24, #0x1d4
    +0x3cc0: ld1     {v4.s}[1], [x15]
    +0x3cc4: add     x15, x24, #0xa8
    +0x3cc8: ld1     {v6.s}[3], [x14]
    +0x3ccc: add     x14, x24, #0x1a4
    +0x3cd0: ldp     s29, s7, [x24, #136]
    +0x3cd4: ld1     {v26.s}[3], [x13]
    +0x3cd8: ld1     {v4.s}[2], [x12]
    +0x3cdc: add     x12, x24, #0xc8
    +0x3ce0: ld1     {v22.s}[3], [x10]
    +0x3ce4: add     x10, x24, #0x1f4
    +0x3ce8: ldr     s27, [x24, #388]
    +0x3cec: ldr     s23, [x24, #384]
    +0x3cf0: ld1     {v29.s}[1], [x15]
    +0x3cf4: add     x13, x24, #0xe8
    +0x3cf8: ld1     {v4.s}[3], [x10]
    +0x3cfc: ld1     {v27.s}[1], [x14]
    +0x3d00: ld1     {v23.s}[1], [x11]
    +0x3d04: add     x10, x24, #0x128
    +0x3d08: add     x11, x24, #0x38
    +0x3d0c: ld1     {v29.s}[2], [x12]
    +0x3d10: add     x12, x24, #0x1c4
    +0x3d14: tbl     v10.16b, {v1.16b-v4.16b}, v15.16b
    +0x3d18: ldp     s11, s1, [x24, #24]
    +0x3d1c: ld1     {v27.s}[2], [x12]
    +0x3d20: ld1     {v23.s}[2], [x9]
    +0x3d24: add     x9, x24, #0x1e4
    +0x3d28: ld1     {v29.s}[3], [x13]
    +0x3d2c: add     x13, x24, #0x78
    +0x3d30: add     x12, x24, #0x1a8
    +0x3d34: ldr     s30, [x24, #264]
    +0x3d38: ld1     {v11.s}[1], [x11]
    +0x3d3c: add     x11, x24, #0x168
    +0x3d40: ld1     {v27.s}[3], [x9]
    +0x3d44: add     x9, x24, #0x58
    +0x3d48: ld1     {v30.s}[1], [x10]
    +0x3d4c: add     x10, x24, #0x3c
    +0x3d50: ld1     {v1.s}[1], [x10]
    +0x3d54: ld1     {v11.s}[2], [x9]
    +0x3d58: add     x9, x24, #0x5c
    +0x3d5c: add     x10, x24, #0x148
    +0x3d60: tbl     v24.16b, {v24.16b-v27.16b}, v15.16b
    +0x3d64: ld1     {v30.s}[2], [x10]
    +0x3d68: add     x10, x24, #0xac
    +0x3d6c: ld1     {v1.s}[2], [x9]
    +0x3d70: ld1     {v7.s}[1], [x10]
    +0x3d74: add     x10, x24, #0x7c
    +0x3d78: ld1     {v11.s}[3], [x13]
    +0x3d7c: add     x13, x24, #0xb8
    +0x3d80: add     x9, x24, #0x1c8
    +0x3d84: ld1     {v30.s}[3], [x11]
    +0x3d88: add     x11, x24, #0xcc
    +0x3d8c: ld1     {v1.s}[3], [x10]
    +0x3d90: ld1     {v7.s}[2], [x11]
    +0x3d94: add     x11, x24, #0xb0
    +0x3d98: ldp     s12, s2, [x24, #152]
    +0x3d9c: ld1     {v17.s}[1], [x11]
    +0x3da0: add     x11, x24, #0xd8
    +0x3da4: add     x10, x24, #0xec
    +0x3da8: ldr     s31, [x24, #392]
    +0x3dac: ld1     {v7.s}[3], [x10]
    +0x3db0: add     x10, x24, #0xd0
    +0x3db4: ld1     {v12.s}[1], [x13]
    +0x3db8: add     x13, x24, #0xbc
    +0x3dbc: ld1     {v17.s}[2], [x10]
    +0x3dc0: ld1     {v2.s}[1], [x13]
    +0x3dc4: add     x10, x24, #0xf8
    +0x3dc8: ldr     s8, [x24, #268]
    +0x3dcc: ld1     {v31.s}[1], [x12]
    +0x3dd0: add     x12, x24, #0x12c
    +0x3dd4: add     x13, x24, #0x15c
    +0x3dd8: ld1     {v12.s}[2], [x11]
    +0x3ddc: add     x11, x24, #0xdc
    +0x3de0: ld1     {v8.s}[1], [x12]
    +0x3de4: ld1     {v2.s}[2], [x11]
    +0x3de8: add     x11, x24, #0xfc
    +0x3dec: add     x12, x24, #0x13c
    +0x3df0: ld1     {v31.s}[2], [x9]
    +0x3df4: add     x9, x24, #0x1d0
    +0x3df8: ld1     {v12.s}[3], [x10]
    +0x3dfc: add     x10, x24, #0xf0
    +0x3e00: ldr     s13, [x24, #280]
    +0x3e04: ld1     {v17.s}[3], [x10]
    +0x3e08: add     x10, x24, #0x138
    +0x3e0c: ldr     s18, [x24, #272]
    +0x3e10: ld1     {v2.s}[3], [x11]
    +0x3e14: add     x11, x24, #0x130
    +0x3e18: ld1     {v13.s}[1], [x10]
    +0x3e1c: ldr     s3, [x24, #284]
    +0x3e20: add     x10, x24, #0x14c
    +0x3e24: ld1     {v18.s}[1], [x11]
    +0x3e28: add     x11, x24, #0x158
    +0x3e2c: ld1     {v8.s}[2], [x10]
    +0x3e30: ld1     {v3.s}[1], [x12]
    +0x3e34: add     x12, x24, #0x150
    +0x3e38: add     x10, x24, #0x16c
    +0x3e3c: ld1     {v13.s}[2], [x11]
    +0x3e40: add     x11, x24, #0x1ac
    +0x3e44: ld1     {v18.s}[2], [x12]
    +0x3e48: add     x12, x24, #0x178
    +0x3e4c: ld1     {v8.s}[3], [x10]
    +0x3e50: ld1     {v3.s}[2], [x13]
    +0x3e54: add     x10, x24, #0x170
    +0x3e58: ldr     s9, [x24, #396]
    +0x3e5c: ld1     {v13.s}[3], [x12]
    +0x3e60: add     x12, x24, #0x17c
    +0x3e64: ldr     s14, [x24, #408]
    +0x3e68: ld1     {v18.s}[3], [x10]
    +0x3e6c: add     x10, x24, #0x1b8
    +0x3e70: ldr     s19, [x24, #400]
    +0x3e74: ld1     {v3.s}[3], [x12]
    +0x3e78: ld1     {v9.s}[1], [x11]
    +0x3e7c: ld1     {v14.s}[1], [x10]
    +0x3e80: add     x10, x24, #0x1b0
    +0x3e84: ldr     s4, [x24, #412]
    +0x3e88: ld1     {v19.s}[1], [x10]
    +0x3e8c: add     x10, x24, #0x1d8
    +0x3e90: add     x11, x24, #0x1bc
    +0x3e94: ld1     {v4.s}[1], [x11]
    +0x3e98: add     x12, x24, #0x1cc
    +0x3e9c: add     x11, x24, #0x1e8
    +0x3ea0: ld1     {v14.s}[2], [x10]
    +0x3ea4: ld1     {v9.s}[2], [x12]
    +0x3ea8: add     x10, x24, #0x1dc
    +0x3eac: ld1     {v19.s}[2], [x9]
    +0x3eb0: add     x9, x24, #0x1f8
    +0x3eb4: ld1     {v31.s}[3], [x11]
    +0x3eb8: ld1     {v4.s}[2], [x10]
    +0x3ebc: add     x10, x24, #0x1f0
    +0x3ec0: ld1     {v14.s}[3], [x9]
    +0x3ec4: add     x9, x24, #0x1ec
    +0x3ec8: ld1     {v9.s}[3], [x9]
    +0x3ecc: ld1     {v19.s}[3], [x10]
    +0x3ed0: add     x9, x24, #0x1fc
    +0x3ed4: ld1     {v4.s}[3], [x9]
    +0x3ed8: add     x10, x24, #0x1e0
    +0x3edc: tbl     v25.16b, {v28.16b-v31.16b}, v15.16b
    +0x3ee0: tbl     v11.16b, {v11.16b-v14.16b}, v15.16b
    +0x3ee4: ld1     {v23.s}[3], [x10]
    +0x3ee8: add     x9, x19, x8
    +0x3eec: tbl     v6.16b, {v6.16b-v9.16b}, v15.16b
    +0x3ef0: tbl     v7.16b, {v16.16b-v19.16b}, v15.16b
    +0x3ef4: movi    v19.16b, #0x8
    +0x3ef8: tbl     v1.16b, {v1.16b-v4.16b}, v15.16b
    +0x3efc: sub     v3.16b, v0.16b, v10.16b
    +0x3f00: shl     v17.16b, v24.16b, #3
    +0x3f04: tbl     v2.16b, {v20.16b-v23.16b}, v15.16b
    +0x3f08: movi    v20.16b, #0x4
    +0x3f0c: sub     v16.16b, v0.16b, v25.16b
    +0x3f10: shl     v4.16b, v11.16b, #2
    +0x3f14: add     x8, x8, #0x30
    +0x3f18: add     x24, x24, #0x200
    +0x3f1c: ushr    v18.16b, v3.16b, #1
    +0x3f20: add     v6.16b, v6.16b, v6.16b
    +0x3f24: shl     v7.16b, v7.16b, #4
    +0x3f28: shl     v1.16b, v1.16b, #5
    +0x3f2c: shl     v3.16b, v3.16b, #7
    +0x3f30: cmp     x8, #0x1a0
    +0x3f34: sub     v4.16b, v19.16b, v4.16b
    +0x3f38: movi    v19.16b, #0x10
    +0x3f3c: sub     v2.16b, v0.16b, v2.16b
    +0x3f40: sub     v6.16b, v20.16b, v6.16b
    +0x3f44: sub     v7.16b, v5.16b, v7.16b
    +0x3f48: orr     v4.16b, v4.16b, v18.16b
    +0x3f4c: movi    v18.16b, #0x40
    +0x3f50: sub     v17.16b, v19.16b, v17.16b
    +0x3f54: ushr    v19.16b, v16.16b, #2
    +0x3f58: shl     v16.16b, v16.16b, #6
    +0x3f5c: orr     v3.16b, v7.16b, v3.16b
    +0x3f60: sub     v1.16b, v18.16b, v1.16b
    +0x3f64: orr     v2.16b, v17.16b, v2.16b
    +0x3f68: orr     v6.16b, v6.16b, v19.16b
    +0x3f6c: orr     v19.16b, v4.16b, v1.16b
    +0x3f70: orr     v17.16b, v2.16b, v16.16b
    +0x3f74: orr     v18.16b, v6.16b, v3.16b
    +0x3f78: st3     {v17.16b-v19.16b}, [x9]
    +0x3f7c: b.ne    <mldsa87_keypair_internal+0x3b78>
    +0x3f80: str     xzr, [sp, #7776]
    +0x3f84: add     x8, sp, #0x1, lsl #12
    +0x3f88: movi    v0.16b, #0x2
    +0x3f8c: movi    v5.16b, #0x20
    +0x3f90: add     x8, x8, #0xe60
    +0x3f94: ldr     q15, [sp, #336]
    +0x3f98: mov     w8, #0x1a0
    +0x3f9c: ldp     s16, s1, [x23, #16]
    +0x3fa0: add     x9, x23, #0x30
    +0x3fa4: add     x10, x23, #0x34
    +0x3fa8: add     x12, x23, #0x50
    +0x3fac: add     x13, x23, #0x54
    +0x3fb0: ldp     s20, s24, [x23]
    +0x3fb4: add     x14, x23, #0x70
    +0x3fb8: ld1     {v16.s}[1], [x9]
    +0x3fbc: ld1     {v1.s}[1], [x10]
    +0x3fc0: add     x9, x23, #0x20
    +0x3fc4: add     x15, x23, #0x74
    +0x3fc8: add     x10, x23, #0x40
    +0x3fcc: add     x11, x23, #0x60
    +0x3fd0: ld1     {v20.s}[1], [x9]
    +0x3fd4: add     x9, x23, #0x44
    +0x3fd8: add     x17, x23, #0xd4
    +0x3fdc: ld1     {v16.s}[2], [x12]
    +0x3fe0: ld1     {v1.s}[2], [x13]
    +0x3fe4: add     x12, x23, #0x24
    +0x3fe8: ld1     {v24.s}[1], [x12]
    +0x3fec: add     x12, x23, #0xb4
    +0x3ff0: add     x0, x23, #0xf4
    +0x3ff4: ld1     {v20.s}[2], [x10]
    +0x3ff8: add     x18, x23, #0xc4
    +0x3ffc: add     x13, x23, #0xa0
    +0x4000: ld1     {v16.s}[3], [x14]
    +0x4004: ld1     {v1.s}[3], [x15]
    +0x4008: add     x16, x23, #0xc0
    +0x400c: ldp     s17, s2, [x23, #144]
    +0x4010: ld1     {v24.s}[2], [x9]
    +0x4014: add     x9, x23, #0x64
    +0x4018: ld1     {v20.s}[3], [x11]
    +0x401c: add     x14, x23, #0xe0
    +0x4020: ldp     s28, s6, [x23, #8]
    +0x4024: add     x15, x23, #0x120
    +0x4028: ld1     {v2.s}[1], [x12]
    +0x402c: ld1     {v24.s}[3], [x9]
    +0x4030: add     x1, x23, #0x124
    +0x4034: ldp     s21, s25, [x23, #128]
    +0x4038: add     x12, x23, #0x140
    +0x403c: add     x10, x23, #0x160
    +0x4040: add     x11, x23, #0x1a0
    +0x4044: add     x9, x23, #0x1c0
    +0x4048: ld1     {v2.s}[2], [x17]
    +0x404c: add     x17, x23, #0xa4
    +0x4050: ld1     {v25.s}[1], [x17]
    +0x4054: ld1     {v21.s}[1], [x13]
    +0x4058: add     x17, x23, #0xe4
    +0x405c: add     x13, x23, #0x164
    +0x4060: ld1     {v2.s}[3], [x0]
    +0x4064: add     x0, x23, #0x144
    +0x4068: ldr     s3, [x23, #276]
    +0x406c: ld1     {v25.s}[2], [x18]
    +0x4070: add     x18, x23, #0x134
    +0x4074: ld1     {v21.s}[2], [x16]
    +0x4078: add     x16, x23, #0x48
    +0x407c: ld1     {v3.s}[1], [x18]
    +0x4080: add     x18, x23, #0x28
    +0x4084: ld1     {v28.s}[1], [x18]
    +0x4088: add     x18, x23, #0x154
    +0x408c: ld1     {v25.s}[3], [x17]
    +0x4090: ld1     {v21.s}[3], [x14]
    +0x4094: add     x14, x23, #0x174
    +0x4098: ldr     s26, [x23, #260]
    +0x409c: ld1     {v3.s}[2], [x18]
    +0x40a0: add     x18, x23, #0x2c
    +0x40a4: ldr     s22, [x23, #256]
    +0x40a8: ld1     {v6.s}[1], [x18]
    +0x40ac: ld1     {v28.s}[2], [x16]
    +0x40b0: add     x16, x23, #0x4c
    +0x40b4: add     x17, x23, #0x68
    +0x40b8: ld1     {v26.s}[1], [x1]
    +0x40bc: ld1     {v22.s}[1], [x15]
    +0x40c0: ld1     {v3.s}[3], [x14]
    +0x40c4: add     x14, x23, #0x6c
    +0x40c8: add     x15, x23, #0x1b4
    +0x40cc: ld1     {v6.s}[2], [x16]
    +0x40d0: ldr     s4, [x23, #404]
    +0x40d4: ld1     {v28.s}[3], [x17]
    +0x40d8: ld1     {v26.s}[2], [x0]
    +0x40dc: ld1     {v22.s}[2], [x12]
    +0x40e0: add     x12, x23, #0x1d4
    +0x40e4: ld1     {v4.s}[1], [x15]
    +0x40e8: add     x15, x23, #0xa8
    +0x40ec: ld1     {v6.s}[3], [x14]
    +0x40f0: add     x14, x23, #0x1a4
    +0x40f4: ldp     s29, s7, [x23, #136]
    +0x40f8: ld1     {v26.s}[3], [x13]
    +0x40fc: ld1     {v4.s}[2], [x12]
    +0x4100: add     x12, x23, #0xc8
    +0x4104: ld1     {v22.s}[3], [x10]
    +0x4108: add     x10, x23, #0x1f4
    +0x410c: ldr     s27, [x23, #388]
    +0x4110: ldr     s23, [x23, #384]
    +0x4114: ld1     {v29.s}[1], [x15]
    +0x4118: add     x13, x23, #0xe8
    +0x411c: ld1     {v4.s}[3], [x10]
    +0x4120: ld1     {v27.s}[1], [x14]
    +0x4124: ld1     {v23.s}[1], [x11]
    +0x4128: add     x10, x23, #0x128
    +0x412c: add     x11, x23, #0x38
    +0x4130: ld1     {v29.s}[2], [x12]
    +0x4134: add     x12, x23, #0x1c4
    +0x4138: tbl     v10.16b, {v1.16b-v4.16b}, v15.16b
    +0x413c: ldp     s11, s1, [x23, #24]
    +0x4140: ld1     {v27.s}[2], [x12]
    +0x4144: ld1     {v23.s}[2], [x9]
    +0x4148: add     x9, x23, #0x1e4
    +0x414c: ld1     {v29.s}[3], [x13]
    +0x4150: add     x13, x23, #0x78
    +0x4154: add     x12, x23, #0x1a8
    +0x4158: ldr     s30, [x23, #264]
    +0x415c: ld1     {v11.s}[1], [x11]
    +0x4160: add     x11, x23, #0x168
    +0x4164: ld1     {v27.s}[3], [x9]
    +0x4168: add     x9, x23, #0x58
    +0x416c: ld1     {v30.s}[1], [x10]
    +0x4170: add     x10, x23, #0x3c
    +0x4174: ld1     {v1.s}[1], [x10]
    +0x4178: ld1     {v11.s}[2], [x9]
    +0x417c: add     x9, x23, #0x5c
    +0x4180: add     x10, x23, #0x148
    +0x4184: tbl     v24.16b, {v24.16b-v27.16b}, v15.16b
    +0x4188: ld1     {v30.s}[2], [x10]
    +0x418c: add     x10, x23, #0xac
    +0x4190: ld1     {v1.s}[2], [x9]
    +0x4194: ld1     {v7.s}[1], [x10]
    +0x4198: add     x10, x23, #0x7c
    +0x419c: ld1     {v11.s}[3], [x13]
    +0x41a0: add     x13, x23, #0xb8
    +0x41a4: add     x9, x23, #0x1c8
    +0x41a8: ld1     {v30.s}[3], [x11]
    +0x41ac: add     x11, x23, #0xcc
    +0x41b0: ld1     {v1.s}[3], [x10]
    +0x41b4: ld1     {v7.s}[2], [x11]
    +0x41b8: add     x11, x23, #0xb0
    +0x41bc: ldp     s12, s2, [x23, #152]
    +0x41c0: ld1     {v17.s}[1], [x11]
    +0x41c4: add     x11, x23, #0xd8
    +0x41c8: add     x10, x23, #0xec
    +0x41cc: ldr     s31, [x23, #392]
    +0x41d0: ld1     {v7.s}[3], [x10]
    +0x41d4: add     x10, x23, #0xd0
    +0x41d8: ld1     {v12.s}[1], [x13]
    +0x41dc: add     x13, x23, #0xbc
    +0x41e0: ld1     {v17.s}[2], [x10]
    +0x41e4: ld1     {v2.s}[1], [x13]
    +0x41e8: add     x10, x23, #0xf8
    +0x41ec: ldr     s8, [x23, #268]
    +0x41f0: ld1     {v31.s}[1], [x12]
    +0x41f4: add     x12, x23, #0x12c
    +0x41f8: add     x13, x23, #0x15c
    +0x41fc: ld1     {v12.s}[2], [x11]
    +0x4200: add     x11, x23, #0xdc
    +0x4204: ld1     {v8.s}[1], [x12]
    +0x4208: ld1     {v2.s}[2], [x11]
    +0x420c: add     x11, x23, #0xfc
    +0x4210: add     x12, x23, #0x13c
    +0x4214: ld1     {v31.s}[2], [x9]
    +0x4218: add     x9, x23, #0x1d0
    +0x421c: ld1     {v12.s}[3], [x10]
    +0x4220: add     x10, x23, #0xf0
    +0x4224: ldr     s13, [x23, #280]
    +0x4228: ld1     {v17.s}[3], [x10]
    +0x422c: add     x10, x23, #0x138
    +0x4230: ldr     s18, [x23, #272]
    +0x4234: ld1     {v2.s}[3], [x11]
    +0x4238: add     x11, x23, #0x130
    +0x423c: ld1     {v13.s}[1], [x10]
    +0x4240: ldr     s3, [x23, #284]
    +0x4244: add     x10, x23, #0x14c
    +0x4248: ld1     {v18.s}[1], [x11]
    +0x424c: add     x11, x23, #0x158
    +0x4250: ld1     {v8.s}[2], [x10]
    +0x4254: ld1     {v3.s}[1], [x12]
    +0x4258: add     x12, x23, #0x150
    +0x425c: add     x10, x23, #0x16c
    +0x4260: ld1     {v13.s}[2], [x11]
    +0x4264: add     x11, x23, #0x1ac
    +0x4268: ld1     {v18.s}[2], [x12]
    +0x426c: add     x12, x23, #0x178
    +0x4270: ld1     {v8.s}[3], [x10]
    +0x4274: ld1     {v3.s}[2], [x13]
    +0x4278: add     x10, x23, #0x170
    +0x427c: ldr     s9, [x23, #396]
    +0x4280: ld1     {v13.s}[3], [x12]
    +0x4284: add     x12, x23, #0x17c
    +0x4288: ldr     s14, [x23, #408]
    +0x428c: ld1     {v18.s}[3], [x10]
    +0x4290: add     x10, x23, #0x1b8
    +0x4294: ldr     s19, [x23, #400]
    +0x4298: ld1     {v3.s}[3], [x12]
    +0x429c: ld1     {v9.s}[1], [x11]
    +0x42a0: ld1     {v14.s}[1], [x10]
    +0x42a4: add     x10, x23, #0x1b0
    +0x42a8: ldr     s4, [x23, #412]
    +0x42ac: ld1     {v19.s}[1], [x10]
    +0x42b0: add     x10, x23, #0x1d8
    +0x42b4: add     x11, x23, #0x1bc
    +0x42b8: ld1     {v4.s}[1], [x11]
    +0x42bc: add     x12, x23, #0x1cc
    +0x42c0: add     x11, x23, #0x1e8
    +0x42c4: ld1     {v14.s}[2], [x10]
    +0x42c8: ld1     {v9.s}[2], [x12]
    +0x42cc: add     x10, x23, #0x1dc
    +0x42d0: ld1     {v19.s}[2], [x9]
    +0x42d4: add     x9, x23, #0x1f8
    +0x42d8: ld1     {v31.s}[3], [x11]
    +0x42dc: ld1     {v4.s}[2], [x10]
    +0x42e0: add     x10, x23, #0x1f0
    +0x42e4: ld1     {v14.s}[3], [x9]
    +0x42e8: add     x9, x23, #0x1ec
    +0x42ec: ld1     {v9.s}[3], [x9]
    +0x42f0: ld1     {v19.s}[3], [x10]
    +0x42f4: add     x9, x23, #0x1fc
    +0x42f8: ld1     {v4.s}[3], [x9]
    +0x42fc: add     x10, x23, #0x1e0
    +0x4300: tbl     v25.16b, {v28.16b-v31.16b}, v15.16b
    +0x4304: tbl     v11.16b, {v11.16b-v14.16b}, v15.16b
    +0x4308: ld1     {v23.s}[3], [x10]
    +0x430c: add     x9, x19, x8
    +0x4310: tbl     v6.16b, {v6.16b-v9.16b}, v15.16b
    +0x4314: tbl     v7.16b, {v16.16b-v19.16b}, v15.16b
    +0x4318: movi    v19.16b, #0x8
    +0x431c: tbl     v1.16b, {v1.16b-v4.16b}, v15.16b
    +0x4320: sub     v3.16b, v0.16b, v10.16b
    +0x4324: shl     v17.16b, v24.16b, #3
    +0x4328: tbl     v2.16b, {v20.16b-v23.16b}, v15.16b
    +0x432c: movi    v20.16b, #0x4
    +0x4330: sub     v16.16b, v0.16b, v25.16b
    +0x4334: shl     v4.16b, v11.16b, #2
    +0x4338: add     x8, x8, #0x30
    +0x433c: add     x23, x23, #0x200
    +0x4340: ushr    v18.16b, v3.16b, #1
    +0x4344: add     v6.16b, v6.16b, v6.16b
    +0x4348: shl     v7.16b, v7.16b, #4
    +0x434c: shl     v1.16b, v1.16b, #5
    +0x4350: shl     v3.16b, v3.16b, #7
    +0x4354: cmp     x8, #0x200
    +0x4358: sub     v4.16b, v19.16b, v4.16b
    +0x435c: movi    v19.16b, #0x10
    +0x4360: sub     v2.16b, v0.16b, v2.16b
    +0x4364: sub     v6.16b, v20.16b, v6.16b
    +0x4368: sub     v7.16b, v5.16b, v7.16b
    +0x436c: orr     v4.16b, v4.16b, v18.16b
    +0x4370: movi    v18.16b, #0x40
    +0x4374: sub     v17.16b, v19.16b, v17.16b
    +0x4378: ushr    v19.16b, v16.16b, #2
    +0x437c: shl     v16.16b, v16.16b, #6
    +0x4380: orr     v3.16b, v7.16b, v3.16b
    +0x4384: sub     v1.16b, v18.16b, v1.16b
    +0x4388: orr     v2.16b, v17.16b, v2.16b
    +0x438c: orr     v6.16b, v6.16b, v19.16b
    +0x4390: orr     v19.16b, v4.16b, v1.16b
    +0x4394: orr     v17.16b, v2.16b, v16.16b
    +0x4398: orr     v18.16b, v6.16b, v3.16b
    +0x439c: st3     {v17.16b-v19.16b}, [x9]
    +0x43a0: b.ne    <mldsa87_keypair_internal+0x3f9c>
    +0x43a4: str     xzr, [sp, #7776]
    +0x43a8: add     x8, sp, #0x1, lsl #12
    +0x43ac: add     x0, sp, #0x160
    +0x43b0: add     x8, x8, #0xe60
    +0x43b4: bl      <mldsa_poly_ntt>
    +0x43b8: add     x0, x22, #0x400
    +0x43bc: bl      <mldsa_poly_ntt>
    +0x43c0: add     x0, x22, #0x800
    +0x43c4: bl      <mldsa_poly_ntt>
    +0x43c8: add     x0, x22, #0xc00
    +0x43cc: bl      <mldsa_poly_ntt>
    +0x43d0: add     x0, x27, #0x1, lsl #12
    +0x43d4: bl      <mldsa_poly_ntt>
    +0x43d8: add     x0, x27, x28
    +0x43dc: bl      <mldsa_poly_ntt>
    +0x43e0: mov     w8, #0x1800
    +0x43e4: add     x0, x27, x8
    +0x43e8: bl      <mldsa_poly_ntt>
    +0x43ec: ldr     q0, [sp, #7648]
    +0x43f0: ldr     q1, [sp, #7664]
    +0x43f4: add     x4, sp, #0x1, lsl #12
    +0x43f8: add     x0, x20, #0x20
    +0x43fc: add     x1, x19, #0x620
    +0x4400: add     x2, sp, #0x160
    +0x4404: add     x3, x19, #0x320
    +0x4408: add     x4, x4, #0xde0
    +0x440c: add     x23, sp, #0x1, lsl #12
    +0x4410: stp     q0, q1, [x20]
    +0x4414: add     x23, x23, #0xde0
    +0x4418: bl      <mld_compute_pack_t0_t187>
    +0x441c: movi    v18.2d, #0x0
    +0x4420: ldp     d0, d1, [x20]
    +0x4424: ldp     d6, d7, [x20, #32]
    +0x4428: add     x0, sp, #0x1, lsl #12
    +0x442c: ldp     d2, d3, [x20, #16]
    +0x4430: add     x0, x0, #0xe60
    +0x4434: add     x24, sp, #0x1, lsl #12
    +0x4438: str     q18, [sp, #7776]
    +0x443c: add     x24, x24, #0xe60
    +0x4440: stur    q18, [x21, #188]
    +0x4444: str     q18, [sp, #7808]
    +0x4448: ldr     d4, [sp, #7784]
    +0x444c: str     q18, [sp, #7792]
    +0x4450: ldr     d16, [sp, #7808]
    +0x4454: ldr     d17, [sp, #7816]
    +0x4458: ldr     d5, [sp, #7800]
    +0x445c: str     q18, [sp, #7824]
    +0x4460: eor     v1.8b, v4.8b, v1.8b
    +0x4464: eor     v4.8b, v16.8b, v6.8b
    +0x4468: str     d0, [sp, #7776]
    +0x446c: ldr     d16, [sp, #7832]
    +0x4470: ldp     d6, d0, [x20, #48]
    +0x4474: eor     v3.8b, v5.8b, v3.8b
    +0x4478: eor     v5.8b, v17.8b, v7.8b
    +0x447c: ldr     d7, [sp, #7824]
    +0x4480: str     q18, [sp, #7856]
    +0x4484: str     d2, [sp, #7792]
    +0x4488: eor     v0.8b, v16.8b, v0.8b
    +0x448c: str     d4, [sp, #7808]
    +0x4490: eor     v6.8b, v7.8b, v6.8b
    +0x4494: ldp     d2, d4, [x20, #80]
    +0x4498: str     q18, [sp, #7840]
    +0x449c: str     d1, [sp, #7784]
    +0x44a0: ldp     d7, d1, [x20, #64]
    +0x44a4: str     d3, [sp, #7800]
    +0x44a8: ldr     d3, [sp, #7856]
    +0x44ac: ldr     d16, [sp, #7848]
    +0x44b0: str     q18, [sp, #7872]
    +0x44b4: ldr     d17, [sp, #7840]
    +0x44b8: eor     v2.8b, v3.8b, v2.8b
    +0x44bc: str     d0, [sp, #7832]
    +0x44c0: eor     v1.8b, v16.8b, v1.8b
    +0x44c4: ldp     d3, d0, [x20, #96]
    +0x44c8: ldr     d16, [sp, #7864]
    +0x44cc: str     d5, [sp, #7816]
    +0x44d0: ldr     d5, [sp, #7872]
    +0x44d4: eor     v7.8b, v17.8b, v7.8b
    +0x44d8: eor     v4.8b, v16.8b, v4.8b
    +0x44dc: str     d6, [sp, #7824]
    +0x44e0: ldr     d6, [sp, #7880]
    +0x44e4: eor     v3.8b, v5.8b, v3.8b
    +0x44e8: str     q18, [sp, #7904]
    +0x44ec: str     q18, [sp, #7888]
    +0x44f0: eor     v0.8b, v6.8b, v0.8b
    +0x44f4: str     d1, [sp, #7848]
    +0x44f8: ldr     d5, [sp, #7888]
    +0x44fc: ldr     d6, [sp, #7896]
    +0x4500: str     d2, [sp, #7856]
    +0x4504: ldp     d1, d2, [x20, #112]
    +0x4508: str     d4, [sp, #7864]
    +0x450c: ldr     d4, [sp, #7904]
    +0x4510: str     d3, [sp, #7872]
    +0x4514: ldr     d3, [x20, #128]
    +0x4518: eor     v1.8b, v5.8b, v1.8b
    +0x451c: eor     v2.8b, v6.8b, v2.8b
    +0x4520: str     q18, [sp, #7952]
    +0x4524: eor     v3.8b, v4.8b, v3.8b
    +0x4528: str     q18, [sp, #7920]
    +0x452c: str     d7, [sp, #7840]
    +0x4530: str     q18, [sp, #7936]
    +0x4534: str     d0, [sp, #7880]
    +0x4538: str     d1, [sp, #7888]
    +0x453c: str     d2, [sp, #7896]
    +0x4540: str     d3, [sp, #7904]
    +0x4544: bl      <mldsa_keccakf1600_permute>
    +0x4548: ldp     d1, d2, [x20, #136]
    +0x454c: add     x0, sp, #0x1, lsl #12
    +0x4550: ldr     d0, [sp, #7776]
    +0x4554: ldr     d3, [sp, #7784]
    +0x4558: add     x0, x0, #0xe60
    +0x455c: ldr     d5, [sp, #7792]
    +0x4560: ldr     d6, [sp, #7808]
    +0x4564: ldr     d7, [sp, #7816]
    +0x4568: eor     v0.8b, v0.8b, v1.8b
    +0x456c: eor     v1.8b, v3.8b, v2.8b
    +0x4570: ldr     d3, [sp, #7800]
    +0x4574: ldp     d4, d2, [x20, #152]
    +0x4578: ldr     d16, [sp, #7824]
    +0x457c: ldr     d17, [sp, #7832]
    +0x4580: ldr     d18, [sp, #7840]
    +0x4584: str     d0, [sp, #7776]
    +0x4588: eor     v4.8b, v5.8b, v4.8b
    +0x458c: eor     v2.8b, v3.8b, v2.8b
    +0x4590: str     d1, [sp, #7784]
    +0x4594: ldp     d5, d3, [x20, #168]
    +0x4598: str     d2, [sp, #7800]
    +0x459c: ldp     d1, d2, [x20, #216]
    +0x45a0: eor     v5.8b, v6.8b, v5.8b
    +0x45a4: eor     v3.8b, v7.8b, v3.8b
    +0x45a8: str     d4, [sp, #7792]
    +0x45ac: ldp     d6, d7, [x20, #184]
    +0x45b0: ldr     d4, [sp, #7856]
    +0x45b4: str     d5, [sp, #7808]
    +0x45b8: eor     v1.8b, v4.8b, v1.8b
    +0x45bc: ldr     d4, [sp, #7872]
    +0x45c0: eor     v6.8b, v16.8b, v6.8b
    +0x45c4: ldp     d16, d0, [x20, #200]
    +0x45c8: eor     v7.8b, v17.8b, v7.8b
    +0x45cc: ldr     d17, [sp, #7848]
    +0x45d0: str     d3, [sp, #7816]
    +0x45d4: ldp     d3, d5, [x20, #232]
    +0x45d8: str     d1, [sp, #7856]
    +0x45dc: eor     v0.8b, v17.8b, v0.8b
    +0x45e0: ldr     d17, [sp, #7864]
    +0x45e4: str     d6, [sp, #7824]
    +0x45e8: ldr     d6, [sp, #7880]
    +0x45ec: str     d7, [sp, #7832]
    +0x45f0: ldr     d7, [sp, #7888]
    +0x45f4: eor     v2.8b, v17.8b, v2.8b
    +0x45f8: eor     v3.8b, v4.8b, v3.8b
    +0x45fc: ldr     d1, [x20, #264]
    +0x4600: str     d0, [sp, #7848]
    +0x4604: ldp     d4, d0, [x20, #248]
    +0x4608: eor     v5.8b, v6.8b, v5.8b
    +0x460c: ldr     d6, [sp, #7896]
    +0x4610: eor     v16.8b, v18.8b, v16.8b
    +0x4614: str     d2, [sp, #7864]
    +0x4618: ldr     d2, [sp, #7904]
    +0x461c: eor     v4.8b, v7.8b, v4.8b
    +0x4620: eor     v0.8b, v6.8b, v0.8b
    +0x4624: str     d3, [sp, #7872]
    +0x4628: eor     v1.8b, v2.8b, v1.8b
    +0x462c: str     d16, [sp, #7840]
    +0x4630: str     d5, [sp, #7880]
    +0x4634: str     d4, [sp, #7888]
    +0x4638: str     d0, [sp, #7896]
    +0x463c: str     d1, [sp, #7904]
    +0x4640: bl      <mldsa_keccakf1600_permute>
    +0x4644: ldp     d1, d2, [x20, #272]
    +0x4648: add     x0, sp, #0x1, lsl #12
    +0x464c: ldr     d0, [sp, #7776]
    +0x4650: ldr     d3, [sp, #7784]
    +0x4654: add     x0, x0, #0xe60
    +0x4658: ldr     d5, [sp, #7792]
    +0x465c: ldr     d6, [sp, #7808]
    +0x4660: ldr     d7, [sp, #7816]
    +0x4664: eor     v0.8b, v0.8b, v1.8b
    +0x4668: eor     v1.8b, v3.8b, v2.8b
    +0x466c: ldr     d3, [sp, #7800]
    +0x4670: ldp     d4, d2, [x20, #288]
    +0x4674: ldr     d16, [sp, #7824]
    +0x4678: ldr     d17, [sp, #7832]
    +0x467c: ldr     d18, [sp, #7840]
    +0x4680: str     d0, [sp, #7776]
    +0x4684: eor     v4.8b, v5.8b, v4.8b
    +0x4688: eor     v2.8b, v3.8b, v2.8b
    +0x468c: str     d1, [sp, #7784]
    +0x4690: ldp     d5, d3, [x20, #304]
    +0x4694: str     d2, [sp, #7800]
    +0x4698: ldp     d1, d2, [x20, #352]
    +0x469c: eor     v5.8b, v6.8b, v5.8b
    +0x46a0: eor     v3.8b, v7.8b, v3.8b
    +0x46a4: str     d4, [sp, #7792]
    +0x46a8: ldp     d6, d7, [x20, #320]
    +0x46ac: ldr     d4, [sp, #7856]
    +0x46b0: str     d5, [sp, #7808]
    +0x46b4: eor     v1.8b, v4.8b, v1.8b
    +0x46b8: ldr     d4, [sp, #7872]
    +0x46bc: eor     v6.8b, v16.8b, v6.8b
    +0x46c0: ldp     d16, d0, [x20, #336]
    +0x46c4: eor     v7.8b, v17.8b, v7.8b
    +0x46c8: ldr     d17, [sp, #7848]
    +0x46cc: str     d3, [sp, #7816]
    +0x46d0: ldp     d3, d5, [x20, #368]
    +0x46d4: str     d1, [sp, #7856]
    +0x46d8: eor     v0.8b, v17.8b, v0.8b
    +0x46dc: ldr     d17, [sp, #7864]
    +0x46e0: str     d6, [sp, #7824]
    +0x46e4: ldr     d6, [sp, #7880]
    +0x46e8: str     d7, [sp, #7832]
    +0x46ec: ldr     d7, [sp, #7888]
    +0x46f0: eor     v2.8b, v17.8b, v2.8b
    +0x46f4: eor     v3.8b, v4.8b, v3.8b
    +0x46f8: ldr     d1, [x20, #400]
    +0x46fc: str     d0, [sp, #7848]
    +0x4700: ldp     d4, d0, [x20, #384]
    +0x4704: eor     v5.8b, v6.8b, v5.8b
    +0x4708: ldr     d6, [sp, #7896]
    +0x470c: eor     v16.8b, v18.8b, v16.8b
    +0x4710: str     d2, [sp, #7864]
    +0x4714: ldr     d2, [sp, #7904]
    +0x4718: eor     v4.8b, v7.8b, v4.8b
    +0x471c: eor     v0.8b, v6.8b, v0.8b
    +0x4720: str     d3, [sp, #7872]
    +0x4724: eor     v1.8b, v2.8b, v1.8b
    +0x4728: str     d16, [sp, #7840]
    +0x472c: str     d5, [sp, #7880]
    +0x4730: str     d4, [sp, #7888]
    +0x4734: str     d0, [sp, #7896]
    +0x4738: str     d1, [sp, #7904]
    +0x473c: bl      <mldsa_keccakf1600_permute>
    +0x4740: ldp     d1, d2, [x20, #408]
    +0x4744: add     x0, sp, #0x1, lsl #12
    +0x4748: ldr     d0, [sp, #7776]
    +0x474c: ldr     d3, [sp, #7784]
    +0x4750: add     x0, x0, #0xe60
    +0x4754: ldr     d5, [sp, #7792]
    +0x4758: ldr     d6, [sp, #7808]
    +0x475c: ldr     d7, [sp, #7816]
    +0x4760: eor     v0.8b, v0.8b, v1.8b
    +0x4764: eor     v1.8b, v3.8b, v2.8b
    +0x4768: ldr     d3, [sp, #7800]
    +0x476c: ldp     d4, d2, [x20, #424]
    +0x4770: ldr     d16, [sp, #7824]
    +0x4774: ldr     d17, [sp, #7832]
    +0x4778: ldr     d18, [sp, #7840]
    +0x477c: str     d0, [sp, #7776]
    +0x4780: eor     v4.8b, v5.8b, v4.8b
    +0x4784: eor     v2.8b, v3.8b, v2.8b
    +0x4788: str     d1, [sp, #7784]
    +0x478c: ldp     d5, d3, [x20, #440]
    +0x4790: str     d2, [sp, #7800]
    +0x4794: ldp     d1, d2, [x20, #488]
    +0x4798: eor     v5.8b, v6.8b, v5.8b
    +0x479c: eor     v3.8b, v7.8b, v3.8b
    +0x47a0: str     d4, [sp, #7792]
    +0x47a4: ldp     d6, d7, [x20, #456]
    +0x47a8: ldr     d4, [sp, #7856]
    +0x47ac: eor     v1.8b, v4.8b, v1.8b
    +0x47b0: str     d5, [sp, #7808]
    +0x47b4: ldr     d4, [sp, #7872]
    +0x47b8: eor     v6.8b, v16.8b, v6.8b
    +0x47bc: ldp     d16, d0, [x20, #472]
    +0x47c0: eor     v7.8b, v17.8b, v7.8b
    +0x47c4: ldr     d17, [sp, #7848]
    +0x47c8: str     d3, [sp, #7816]
    +0x47cc: ldp     d3, d5, [x20, #504]
    +0x47d0: str     d1, [sp, #7856]
    +0x47d4: eor     v0.8b, v17.8b, v0.8b
    +0x47d8: ldr     d17, [sp, #7864]
    +0x47dc: str     d6, [sp, #7824]
    +0x47e0: ldr     d6, [sp, #7880]
    +0x47e4: str     d7, [sp, #7832]
    +0x47e8: ldr     d7, [sp, #7888]
    +0x47ec: eor     v2.8b, v17.8b, v2.8b
    +0x47f0: eor     v3.8b, v4.8b, v3.8b
    +0x47f4: ldr     d4, [x20, #520]
    +0x47f8: eor     v5.8b, v6.8b, v5.8b
    +0x47fc: str     d0, [sp, #7848]
    +0x4800: ldr     d0, [sp, #7896]
    +0x4804: ldr     d6, [x20, #528]
    +0x4808: ldr     d1, [x20, #536]
    +0x480c: eor     v16.8b, v18.8b, v16.8b
    +0x4810: str     d2, [sp, #7864]
    +0x4814: ldr     d2, [sp, #7904]
    +0x4818: eor     v4.8b, v7.8b, v4.8b
    +0x481c: eor     v0.8b, v0.8b, v6.8b
    +0x4820: str     d3, [sp, #7872]
    +0x4824: eor     v1.8b, v2.8b, v1.8b
    +0x4828: str     d16, [sp, #7840]
    +0x482c: str     d5, [sp, #7880]
    +0x4830: str     d4, [sp, #7888]
    +0x4834: str     d0, [sp, #7896]
    +0x4838: str     d1, [sp, #7904]
    +0x483c: bl      <mldsa_keccakf1600_permute>
    +0x4840: ldr     d0, [x20, #544]
    +0x4844: ldr     d1, [sp, #7776]
    +0x4848: add     x0, sp, #0x1, lsl #12
    +0x484c: ldr     d2, [x20, #552]
    +0x4850: ldr     d3, [sp, #7784]
    +0x4854: add     x0, x0, #0xe60
    +0x4858: eor     v0.8b, v1.8b, v0.8b
    +0x485c: ldr     d4, [x20, #560]
    +0x4860: ldr     d5, [sp, #7792]
    +0x4864: eor     v1.8b, v3.8b, v2.8b
    +0x4868: ldr     d2, [x20, #568]
    +0x486c: ldr     d3, [sp, #7800]
    +0x4870: ldr     d7, [sp, #7816]
    +0x4874: eor     v4.8b, v5.8b, v4.8b
    +0x4878: ldr     d5, [x20, #576]
    +0x487c: eor     v2.8b, v3.8b, v2.8b
    +0x4880: ldr     d3, [x20, #584]
    +0x4884: ldr     d6, [sp, #7808]
    +0x4888: ldr     d17, [sp, #7832]
    +0x488c: ldr     d16, [sp, #7824]
    +0x4890: str     d0, [sp, #7776]
    +0x4894: eor     v3.8b, v7.8b, v3.8b
    +0x4898: ldr     d7, [x20, #600]
    +0x489c: eor     v5.8b, v6.8b, v5.8b
    +0x48a0: ldr     d6, [x20, #592]
    +0x48a4: ldr     d0, [sp, #7848]
    +0x48a8: str     d1, [sp, #7784]
    +0x48ac: eor     v7.8b, v17.8b, v7.8b
    +0x48b0: ldr     d1, [x20, #616]
    +0x48b4: str     d4, [sp, #7792]
    +0x48b8: ldr     d4, [x20, #624]
    +0x48bc: eor     v6.8b, v16.8b, v6.8b
    +0x48c0: ldr     d17, [sp, #7856]
    +0x48c4: eor     v0.8b, v0.8b, v1.8b
    +0x48c8: str     d2, [sp, #7800]
    +0x48cc: ldr     d1, [sp, #7864]
    +0x48d0: eor     v2.8b, v17.8b, v4.8b
    +0x48d4: ldr     d4, [x20, #632]
    +0x48d8: str     d5, [sp, #7808]
    +0x48dc: str     d3, [sp, #7816]
    +0x48e0: ldr     d3, [x20, #640]
    +0x48e4: ldr     d5, [sp, #7872]
    +0x48e8: eor     v1.8b, v1.8b, v4.8b
    +0x48ec: str     d6, [sp, #7824]
    +0x48f0: ldr     d4, [sp, #7880]
    +0x48f4: eor     v3.8b, v5.8b, v3.8b
    +0x48f8: str     d7, [sp, #7832]
    +0x48fc: ldr     d5, [x20, #648]
    +0x4900: ldr     d6, [x20, #656]
    +0x4904: ldr     d7, [sp, #7888]
    +0x4908: ldr     d16, [x20, #608]
    +0x490c: eor     v4.8b, v4.8b, v5.8b
    +0x4910: ldr     d18, [sp, #7840]
    +0x4914: str     d0, [sp, #7848]
    +0x4918: eor     v5.8b, v7.8b, v6.8b
    +0x491c: ldr     d0, [sp, #7896]
    +0x4920: ldr     d6, [x20, #664]
    +0x4924: eor     v16.8b, v18.8b, v16.8b
    +0x4928: str     d2, [sp, #7856]
    +0x492c: ldr     d2, [sp, #7904]
    +0x4930: eor     v0.8b, v0.8b, v6.8b
    +0x4934: str     d1, [sp, #7864]
    +0x4938: ldr     d1, [x20, #672]
    +0x493c: str     d3, [sp, #7872]
    +0x4940: eor     v1.8b, v2.8b, v1.8b
    +0x4944: str     d16, [sp, #7840]
    +0x4948: str     d4, [sp, #7880]
    +0x494c: str     d5, [sp, #7888]
    +0x4950: str     d0, [sp, #7896]
    +0x4954: str     d1, [sp, #7904]
    +0x4958: bl      <mldsa_keccakf1600_permute>
    +0x495c: ldr     d0, [x20, #680]
    +0x4960: ldr     d1, [sp, #7776]
    +0x4964: add     x0, sp, #0x1, lsl #12
    +0x4968: ldr     d2, [x20, #688]
    +0x496c: ldr     d3, [sp, #7784]
    +0x4970: add     x0, x0, #0xe60
    +0x4974: eor     v0.8b, v1.8b, v0.8b
    +0x4978: ldr     d4, [x20, #696]
    +0x497c: ldr     d5, [sp, #7792]
    +0x4980: eor     v1.8b, v3.8b, v2.8b
    +0x4984: ldr     d2, [x20, #704]
    +0x4988: ldr     d3, [sp, #7800]
    +0x498c: ldr     d7, [sp, #7816]
    +0x4990: eor     v4.8b, v5.8b, v4.8b
    +0x4994: ldr     d5, [x20, #712]
    +0x4998: eor     v2.8b, v3.8b, v2.8b
    +0x499c: ldr     d3, [x20, #720]
    +0x49a0: ldr     d6, [sp, #7808]
    +0x49a4: ldr     d17, [sp, #7832]
    +0x49a8: ldr     d16, [sp, #7824]
    +0x49ac: str     d0, [sp, #7776]
    +0x49b0: eor     v3.8b, v7.8b, v3.8b
    +0x49b4: ldr     d7, [x20, #736]
    +0x49b8: eor     v5.8b, v6.8b, v5.8b
    +0x49bc: ldr     d6, [x20, #728]
    +0x49c0: ldr     d0, [sp, #7848]
    +0x49c4: str     d1, [sp, #7784]
    +0x49c8: eor     v7.8b, v17.8b, v7.8b
    +0x49cc: ldr     d1, [x20, #752]
    +0x49d0: str     d4, [sp, #7792]
    +0x49d4: ldr     d4, [x20, #760]
    +0x49d8: eor     v6.8b, v16.8b, v6.8b
    +0x49dc: ldr     d17, [sp, #7856]
    +0x49e0: eor     v0.8b, v0.8b, v1.8b
    +0x49e4: str     d2, [sp, #7800]
    +0x49e8: ldr     d1, [sp, #7864]
    +0x49ec: eor     v2.8b, v17.8b, v4.8b
    +0x49f0: ldr     d4, [x20, #768]
    +0x49f4: str     d5, [sp, #7808]
    +0x49f8: str     d3, [sp, #7816]
    +0x49fc: ldr     d3, [x20, #776]
    +0x4a00: ldr     d5, [sp, #7872]
    +0x4a04: eor     v1.8b, v1.8b, v4.8b
    +0x4a08: str     d6, [sp, #7824]
    +0x4a0c: ldr     d4, [sp, #7880]
    +0x4a10: eor     v3.8b, v5.8b, v3.8b
    +0x4a14: str     d7, [sp, #7832]
    +0x4a18: ldr     d5, [x20, #784]
    +0x4a1c: ldr     d6, [x20, #792]
    +0x4a20: ldr     d7, [sp, #7888]
    +0x4a24: ldr     d16, [x20, #744]
    +0x4a28: eor     v4.8b, v4.8b, v5.8b
    +0x4a2c: ldr     d18, [sp, #7840]
    +0x4a30: str     d0, [sp, #7848]
    +0x4a34: eor     v5.8b, v7.8b, v6.8b
    +0x4a38: ldr     d0, [sp, #7896]
    +0x4a3c: ldr     d6, [x20, #800]
    +0x4a40: eor     v16.8b, v18.8b, v16.8b
    +0x4a44: str     d2, [sp, #7856]
    +0x4a48: ldr     d2, [sp, #7904]
    +0x4a4c: eor     v0.8b, v0.8b, v6.8b
    +0x4a50: str     d1, [sp, #7864]
    +0x4a54: ldr     d1, [x20, #808]
    +0x4a58: str     d3, [sp, #7872]
    +0x4a5c: eor     v1.8b, v2.8b, v1.8b
    +0x4a60: str     d16, [sp, #7840]
    +0x4a64: str     d4, [sp, #7880]
    +0x4a68: str     d5, [sp, #7888]
    +0x4a6c: str     d0, [sp, #7896]
    +0x4a70: str     d1, [sp, #7904]
    +0x4a74: bl      <mldsa_keccakf1600_permute>
    +0x4a78: ldr     d0, [x20, #816]
    +0x4a7c: ldr     d1, [sp, #7776]
    +0x4a80: add     x0, sp, #0x1, lsl #12
    +0x4a84: ldr     d2, [x20, #824]
    +0x4a88: ldr     d3, [sp, #7784]
    +0x4a8c: add     x0, x0, #0xe60
    +0x4a90: eor     v0.8b, v1.8b, v0.8b
    +0x4a94: ldr     d4, [x20, #832]
    +0x4a98: ldr     d5, [sp, #7792]
    +0x4a9c: eor     v1.8b, v3.8b, v2.8b
    +0x4aa0: ldr     d2, [x20, #840]
    +0x4aa4: ldr     d3, [sp, #7800]
    +0x4aa8: ldr     d7, [sp, #7816]
    +0x4aac: eor     v4.8b, v5.8b, v4.8b
    +0x4ab0: ldr     d5, [x20, #848]
    +0x4ab4: eor     v2.8b, v3.8b, v2.8b
    +0x4ab8: ldr     d3, [x20, #856]
    +0x4abc: ldr     d6, [sp, #7808]
    +0x4ac0: ldr     d17, [sp, #7832]
    +0x4ac4: ldr     d16, [sp, #7824]
    +0x4ac8: str     d0, [sp, #7776]
    +0x4acc: eor     v3.8b, v7.8b, v3.8b
    +0x4ad0: ldr     d7, [x20, #872]
    +0x4ad4: eor     v5.8b, v6.8b, v5.8b
    +0x4ad8: ldr     d6, [x20, #864]
    +0x4adc: ldr     d0, [sp, #7848]
    +0x4ae0: str     d1, [sp, #7784]
    +0x4ae4: eor     v7.8b, v17.8b, v7.8b
    +0x4ae8: ldr     d1, [x20, #888]
    +0x4aec: str     d4, [sp, #7792]
    +0x4af0: ldr     d4, [x20, #896]
    +0x4af4: eor     v6.8b, v16.8b, v6.8b
    +0x4af8: ldr     d17, [sp, #7856]
    +0x4afc: eor     v0.8b, v0.8b, v1.8b
    +0x4b00: str     d2, [sp, #7800]
    +0x4b04: ldr     d1, [sp, #7864]
    +0x4b08: eor     v2.8b, v17.8b, v4.8b
    +0x4b0c: ldr     d4, [x20, #904]
    +0x4b10: str     d5, [sp, #7808]
    +0x4b14: str     d3, [sp, #7816]
    +0x4b18: ldr     d3, [x20, #912]
    +0x4b1c: ldr     d5, [sp, #7872]
    +0x4b20: eor     v1.8b, v1.8b, v4.8b
    +0x4b24: str     d6, [sp, #7824]
    +0x4b28: ldr     d4, [sp, #7880]
    +0x4b2c: eor     v3.8b, v5.8b, v3.8b
    +0x4b30: str     d7, [sp, #7832]
    +0x4b34: ldr     d5, [x20, #920]
    +0x4b38: ldr     d6, [x20, #928]
    +0x4b3c: ldr     d7, [sp, #7888]
    +0x4b40: ldr     d16, [x20, #880]
    +0x4b44: eor     v4.8b, v4.8b, v5.8b
    +0x4b48: ldr     d18, [sp, #7840]
    +0x4b4c: str     d0, [sp, #7848]
    +0x4b50: eor     v5.8b, v7.8b, v6.8b
    +0x4b54: ldr     d0, [sp, #7896]
    +0x4b58: ldr     d6, [x20, #936]
    +0x4b5c: eor     v16.8b, v18.8b, v16.8b
    +0x4b60: str     d2, [sp, #7856]
    +0x4b64: ldr     d2, [sp, #7904]
    +0x4b68: eor     v0.8b, v0.8b, v6.8b
    +0x4b6c: str     d1, [sp, #7864]
    +0x4b70: ldr     d1, [x20, #944]
    +0x4b74: str     d3, [sp, #7872]
    +0x4b78: eor     v1.8b, v2.8b, v1.8b
    +0x4b7c: str     d16, [sp, #7840]
    +0x4b80: str     d4, [sp, #7880]
    +0x4b84: str     d5, [sp, #7888]
    +0x4b88: str     d0, [sp, #7896]
    +0x4b8c: str     d1, [sp, #7904]
    +0x4b90: bl      <mldsa_keccakf1600_permute>
    +0x4b94: ldr     d0, [x20, #952]
    +0x4b98: ldr     d1, [sp, #7776]
    +0x4b9c: add     x0, sp, #0x1, lsl #12
    +0x4ba0: ldr     d2, [x20, #960]
    +0x4ba4: ldr     d3, [sp, #7784]
    +0x4ba8: add     x0, x0, #0xe60
    +0x4bac: eor     v0.8b, v1.8b, v0.8b
    +0x4bb0: ldr     d4, [x20, #968]
    +0x4bb4: ldr     d5, [sp, #7792]
    +0x4bb8: eor     v1.8b, v3.8b, v2.8b
    +0x4bbc: ldr     d2, [x20, #976]
    +0x4bc0: ldr     d3, [sp, #7800]
    +0x4bc4: ldr     d7, [sp, #7816]
    +0x4bc8: eor     v4.8b, v5.8b, v4.8b
    +0x4bcc: ldr     d5, [x20, #984]
    +0x4bd0: eor     v2.8b, v3.8b, v2.8b
    +0x4bd4: ldr     d3, [x20, #992]
    +0x4bd8: ldr     d6, [sp, #7808]
    +0x4bdc: ldr     d17, [sp, #7832]
    +0x4be0: ldr     d16, [sp, #7824]
    +0x4be4: str     d0, [sp, #7776]
    +0x4be8: eor     v3.8b, v7.8b, v3.8b
    +0x4bec: ldr     d7, [x20, #1008]
    +0x4bf0: eor     v5.8b, v6.8b, v5.8b
    +0x4bf4: ldr     d6, [x20, #1000]
    +0x4bf8: ldr     d0, [sp, #7848]
    +0x4bfc: str     d1, [sp, #7784]
    +0x4c00: eor     v7.8b, v17.8b, v7.8b
    +0x4c04: ldr     d1, [x20, #1024]
    +0x4c08: str     d4, [sp, #7792]
    +0x4c0c: ldr     d4, [x20, #1032]
    +0x4c10: eor     v6.8b, v16.8b, v6.8b
    +0x4c14: ldr     d17, [sp, #7856]
    +0x4c18: eor     v0.8b, v0.8b, v1.8b
    +0x4c1c: str     d2, [sp, #7800]
    +0x4c20: ldr     d1, [sp, #7864]
    +0x4c24: eor     v2.8b, v17.8b, v4.8b
    +0x4c28: ldr     d4, [x20, #1040]
    +0x4c2c: str     d5, [sp, #7808]
    +0x4c30: str     d3, [sp, #7816]
    +0x4c34: ldr     d3, [x20, #1048]
    +0x4c38: ldr     d5, [sp, #7872]
    +0x4c3c: eor     v1.8b, v1.8b, v4.8b
    +0x4c40: str     d6, [sp, #7824]
    +0x4c44: ldr     d4, [sp, #7880]
    +0x4c48: eor     v3.8b, v5.8b, v3.8b
    +0x4c4c: str     d7, [sp, #7832]
    +0x4c50: ldr     d5, [x20, #1056]
    +0x4c54: ldr     d6, [x20, #1064]
    +0x4c58: ldr     d7, [sp, #7888]
    +0x4c5c: ldr     d16, [x20, #1016]
    +0x4c60: eor     v4.8b, v4.8b, v5.8b
    +0x4c64: ldr     d18, [sp, #7840]
    +0x4c68: str     d0, [sp, #7848]
    +0x4c6c: eor     v5.8b, v7.8b, v6.8b
    +0x4c70: ldr     d0, [sp, #7896]
    +0x4c74: ldr     d6, [x20, #1072]
    +0x4c78: eor     v16.8b, v18.8b, v16.8b
    +0x4c7c: str     d2, [sp, #7856]
    +0x4c80: ldr     d2, [sp, #7904]
    +0x4c84: eor     v0.8b, v0.8b, v6.8b
    +0x4c88: str     d1, [sp, #7864]
    +0x4c8c: ldr     d1, [x20, #1080]
    +0x4c90: str     d3, [sp, #7872]
    +0x4c94: eor     v1.8b, v2.8b, v1.8b
    +0x4c98: str     d16, [sp, #7840]
    +0x4c9c: str     d4, [sp, #7880]
    +0x4ca0: str     d5, [sp, #7888]
    +0x4ca4: str     d0, [sp, #7896]
    +0x4ca8: str     d1, [sp, #7904]
    +0x4cac: bl      <mldsa_keccakf1600_permute>
    +0x4cb0: ldr     d0, [x20, #1088]
    +0x4cb4: ldr     d1, [sp, #7776]
    +0x4cb8: add     x0, sp, #0x1, lsl #12
    +0x4cbc: ldr     d2, [x20, #1096]
    +0x4cc0: ldr     d3, [sp, #7784]
    +0x4cc4: add     x0, x0, #0xe60
    +0x4cc8: eor     v0.8b, v1.8b, v0.8b
    +0x4ccc: ldr     d4, [x20, #1104]
    +0x4cd0: ldr     d5, [sp, #7792]
    +0x4cd4: eor     v1.8b, v3.8b, v2.8b
    +0x4cd8: ldr     d2, [x20, #1112]
    +0x4cdc: ldr     d3, [sp, #7800]
    +0x4ce0: ldr     d7, [sp, #7816]
    +0x4ce4: eor     v4.8b, v5.8b, v4.8b
    +0x4ce8: ldr     d5, [x20, #1120]
    +0x4cec: eor     v2.8b, v3.8b, v2.8b
    +0x4cf0: ldr     d3, [x20, #1128]
    +0x4cf4: ldr     d6, [sp, #7808]
    +0x4cf8: ldr     d17, [sp, #7832]
    +0x4cfc: ldr     d16, [sp, #7824]
    +0x4d00: str     d0, [sp, #7776]
    +0x4d04: eor     v3.8b, v7.8b, v3.8b
    +0x4d08: ldr     d7, [x20, #1144]
    +0x4d0c: eor     v5.8b, v6.8b, v5.8b
    +0x4d10: ldr     d6, [x20, #1136]
    +0x4d14: ldr     d0, [sp, #7848]
    +0x4d18: str     d1, [sp, #7784]
    +0x4d1c: eor     v7.8b, v17.8b, v7.8b
    +0x4d20: ldr     d1, [x20, #1160]
    +0x4d24: str     d4, [sp, #7792]
    +0x4d28: ldr     d4, [x20, #1168]
    +0x4d2c: eor     v6.8b, v16.8b, v6.8b
    +0x4d30: ldr     d17, [sp, #7856]
    +0x4d34: eor     v0.8b, v0.8b, v1.8b
    +0x4d38: str     d2, [sp, #7800]
    +0x4d3c: ldr     d1, [sp, #7864]
    +0x4d40: eor     v2.8b, v17.8b, v4.8b
    +0x4d44: ldr     d4, [x20, #1176]
    +0x4d48: str     d5, [sp, #7808]
    +0x4d4c: str     d3, [sp, #7816]
    +0x4d50: ldr     d3, [x20, #1184]
    +0x4d54: ldr     d5, [sp, #7872]
    +0x4d58: eor     v1.8b, v1.8b, v4.8b
    +0x4d5c: str     d6, [sp, #7824]
    +0x4d60: ldr     d4, [sp, #7880]
    +0x4d64: eor     v3.8b, v5.8b, v3.8b
    +0x4d68: str     d7, [sp, #7832]
    +0x4d6c: ldr     d5, [x20, #1192]
    +0x4d70: ldr     d6, [x20, #1200]
    +0x4d74: ldr     d7, [sp, #7888]
    +0x4d78: ldr     d16, [x20, #1152]
    +0x4d7c: eor     v4.8b, v4.8b, v5.8b
    +0x4d80: ldr     d18, [sp, #7840]
    +0x4d84: str     d0, [sp, #7848]
    +0x4d88: eor     v5.8b, v7.8b, v6.8b
    +0x4d8c: ldr     d0, [sp, #7896]
    +0x4d90: ldr     d6, [x20, #1208]
    +0x4d94: eor     v16.8b, v18.8b, v16.8b
    +0x4d98: str     d2, [sp, #7856]
    +0x4d9c: ldr     d2, [sp, #7904]
    +0x4da0: eor     v0.8b, v0.8b, v6.8b
    +0x4da4: str     d1, [sp, #7864]
    +0x4da8: ldr     d1, [x20, #1216]
    +0x4dac: str     d3, [sp, #7872]
    +0x4db0: eor     v1.8b, v2.8b, v1.8b
    +0x4db4: str     d16, [sp, #7840]
    +0x4db8: str     d4, [sp, #7880]
    +0x4dbc: str     d5, [sp, #7888]
    +0x4dc0: str     d0, [sp, #7896]
    +0x4dc4: str     d1, [sp, #7904]
    +0x4dc8: bl      <mldsa_keccakf1600_permute>
    +0x4dcc: ldr     d0, [x20, #1224]
    +0x4dd0: ldr     d1, [sp, #7776]
    +0x4dd4: add     x0, sp, #0x1, lsl #12
    +0x4dd8: ldr     d2, [x20, #1232]
    +0x4ddc: ldr     d3, [sp, #7784]
    +0x4de0: add     x0, x0, #0xe60
    +0x4de4: eor     v0.8b, v1.8b, v0.8b
    +0x4de8: ldr     d4, [x20, #1240]
    +0x4dec: ldr     d5, [sp, #7792]
    +0x4df0: eor     v1.8b, v3.8b, v2.8b
    +0x4df4: ldr     d2, [x20, #1248]
    +0x4df8: ldr     d3, [sp, #7800]
    +0x4dfc: ldr     d7, [sp, #7816]
    +0x4e00: eor     v4.8b, v5.8b, v4.8b
    +0x4e04: ldr     d5, [x20, #1256]
    +0x4e08: eor     v2.8b, v3.8b, v2.8b
    +0x4e0c: ldr     d3, [x20, #1264]
    +0x4e10: ldr     d6, [sp, #7808]
    +0x4e14: ldr     d17, [sp, #7832]
    +0x4e18: ldr     d16, [sp, #7824]
    +0x4e1c: str     d0, [sp, #7776]
    +0x4e20: eor     v3.8b, v7.8b, v3.8b
    +0x4e24: ldr     d7, [x20, #1280]
    +0x4e28: eor     v5.8b, v6.8b, v5.8b
    +0x4e2c: ldr     d6, [x20, #1272]
    +0x4e30: ldr     d0, [sp, #7848]
    +0x4e34: str     d1, [sp, #7784]
    +0x4e38: eor     v7.8b, v17.8b, v7.8b
    +0x4e3c: ldr     d1, [x20, #1296]
    +0x4e40: str     d4, [sp, #7792]
    +0x4e44: ldr     d4, [x20, #1304]
    +0x4e48: eor     v6.8b, v16.8b, v6.8b
    +0x4e4c: ldr     d17, [sp, #7856]
    +0x4e50: eor     v0.8b, v0.8b, v1.8b
    +0x4e54: str     d2, [sp, #7800]
    +0x4e58: ldr     d1, [sp, #7864]
    +0x4e5c: eor     v2.8b, v17.8b, v4.8b
    +0x4e60: ldr     d4, [x20, #1312]
    +0x4e64: str     d5, [sp, #7808]
    +0x4e68: str     d3, [sp, #7816]
    +0x4e6c: ldr     d3, [x20, #1320]
    +0x4e70: ldr     d5, [sp, #7872]
    +0x4e74: eor     v1.8b, v1.8b, v4.8b
    +0x4e78: str     d6, [sp, #7824]
    +0x4e7c: ldr     d4, [sp, #7880]
    +0x4e80: eor     v3.8b, v5.8b, v3.8b
    +0x4e84: str     d7, [sp, #7832]
    +0x4e88: ldr     d5, [x20, #1328]
    +0x4e8c: ldr     d6, [x20, #1336]
    +0x4e90: ldr     d7, [sp, #7888]
    +0x4e94: ldr     d16, [x20, #1288]
    +0x4e98: eor     v4.8b, v4.8b, v5.8b
    +0x4e9c: ldr     d18, [sp, #7840]
    +0x4ea0: str     d0, [sp, #7848]
    +0x4ea4: eor     v5.8b, v7.8b, v6.8b
    +0x4ea8: ldr     d0, [sp, #7896]
    +0x4eac: ldr     d6, [x20, #1344]
    +0x4eb0: eor     v16.8b, v18.8b, v16.8b
    +0x4eb4: str     d2, [sp, #7856]
    +0x4eb8: ldr     d2, [sp, #7904]
    +0x4ebc: eor     v0.8b, v0.8b, v6.8b
    +0x4ec0: str     d1, [sp, #7864]
    +0x4ec4: ldr     d1, [x20, #1352]
    +0x4ec8: str     d3, [sp, #7872]
    +0x4ecc: eor     v1.8b, v2.8b, v1.8b
    +0x4ed0: str     d16, [sp, #7840]
    +0x4ed4: str     d4, [sp, #7880]
    +0x4ed8: str     d5, [sp, #7888]
    +0x4edc: str     d0, [sp, #7896]
    +0x4ee0: str     d1, [sp, #7904]
    +0x4ee4: bl      <mldsa_keccakf1600_permute>
    +0x4ee8: ldr     d0, [x20, #1360]
    +0x4eec: ldr     d1, [sp, #7776]
    +0x4ef0: add     x0, sp, #0x1, lsl #12
    +0x4ef4: ldr     d2, [x20, #1368]
    +0x4ef8: ldr     d3, [sp, #7784]
    +0x4efc: add     x0, x0, #0xe60
    +0x4f00: eor     v0.8b, v1.8b, v0.8b
    +0x4f04: ldr     d4, [x20, #1376]
    +0x4f08: ldr     d5, [sp, #7792]
    +0x4f0c: eor     v1.8b, v3.8b, v2.8b
    +0x4f10: ldr     d2, [x20, #1384]
    +0x4f14: ldr     d3, [sp, #7800]
    +0x4f18: ldr     d7, [sp, #7816]
    +0x4f1c: eor     v4.8b, v5.8b, v4.8b
    +0x4f20: ldr     d5, [x20, #1392]
    +0x4f24: eor     v2.8b, v3.8b, v2.8b
    +0x4f28: ldr     d3, [x20, #1400]
    +0x4f2c: ldr     d6, [sp, #7808]
    +0x4f30: ldr     d17, [sp, #7832]
    +0x4f34: ldr     d16, [sp, #7824]
    +0x4f38: str     d0, [sp, #7776]
    +0x4f3c: eor     v3.8b, v7.8b, v3.8b
    +0x4f40: ldr     d7, [x20, #1416]
    +0x4f44: eor     v5.8b, v6.8b, v5.8b
    +0x4f48: ldr     d6, [x20, #1408]
    +0x4f4c: ldr     d0, [sp, #7848]
    +0x4f50: str     d1, [sp, #7784]
    +0x4f54: eor     v7.8b, v17.8b, v7.8b
    +0x4f58: ldr     d1, [x20, #1432]
    +0x4f5c: str     d4, [sp, #7792]
    +0x4f60: ldr     d4, [x20, #1440]
    +0x4f64: eor     v6.8b, v16.8b, v6.8b
    +0x4f68: ldr     d17, [sp, #7856]
    +0x4f6c: eor     v0.8b, v0.8b, v1.8b
    +0x4f70: str     d2, [sp, #7800]
    +0x4f74: ldr     d1, [sp, #7864]
    +0x4f78: eor     v2.8b, v17.8b, v4.8b
    +0x4f7c: ldr     d4, [x20, #1448]
    +0x4f80: str     d5, [sp, #7808]
    +0x4f84: str     d3, [sp, #7816]
    +0x4f88: ldr     d3, [x20, #1456]
    +0x4f8c: ldr     d5, [sp, #7872]
    +0x4f90: eor     v1.8b, v1.8b, v4.8b
    +0x4f94: str     d6, [sp, #7824]
    +0x4f98: ldr     d4, [sp, #7880]
    +0x4f9c: eor     v3.8b, v5.8b, v3.8b
    +0x4fa0: str     d7, [sp, #7832]
    +0x4fa4: ldr     d5, [x20, #1464]
    +0x4fa8: ldr     d6, [x20, #1472]
    +0x4fac: ldr     d7, [sp, #7888]
    +0x4fb0: ldr     d16, [x20, #1424]
    +0x4fb4: eor     v4.8b, v4.8b, v5.8b
    +0x4fb8: ldr     d18, [sp, #7840]
    +0x4fbc: str     d0, [sp, #7848]
    +0x4fc0: eor     v5.8b, v7.8b, v6.8b
    +0x4fc4: ldr     d0, [sp, #7896]
    +0x4fc8: ldr     d6, [x20, #1480]
    +0x4fcc: eor     v16.8b, v18.8b, v16.8b
    +0x4fd0: str     d2, [sp, #7856]
    +0x4fd4: ldr     d2, [sp, #7904]
    +0x4fd8: eor     v0.8b, v0.8b, v6.8b
    +0x4fdc: str     d1, [sp, #7864]
    +0x4fe0: ldr     d1, [x20, #1488]
    +0x4fe4: str     d3, [sp, #7872]
    +0x4fe8: eor     v1.8b, v2.8b, v1.8b
    +0x4fec: str     d16, [sp, #7840]
    +0x4ff0: str     d4, [sp, #7880]
    +0x4ff4: str     d5, [sp, #7888]
    +0x4ff8: str     d0, [sp, #7896]
    +0x4ffc: str     d1, [sp, #7904]
    +0x5000: bl      <mldsa_keccakf1600_permute>
    +0x5004: ldr     d0, [x20, #1496]
    +0x5008: ldr     d1, [sp, #7776]
    +0x500c: add     x0, sp, #0x1, lsl #12
    +0x5010: ldr     d2, [x20, #1504]
    +0x5014: ldr     d3, [sp, #7784]
    +0x5018: add     x0, x0, #0xe60
    +0x501c: eor     v0.8b, v1.8b, v0.8b
    +0x5020: ldr     d4, [x20, #1512]
    +0x5024: ldr     d5, [sp, #7792]
    +0x5028: eor     v1.8b, v3.8b, v2.8b
    +0x502c: ldr     d2, [x20, #1520]
    +0x5030: ldr     d3, [sp, #7800]
    +0x5034: ldr     d7, [sp, #7816]
    +0x5038: eor     v4.8b, v5.8b, v4.8b
    +0x503c: ldr     d5, [x20, #1528]
    +0x5040: eor     v2.8b, v3.8b, v2.8b
    +0x5044: ldr     d3, [x20, #1536]
    +0x5048: ldr     d6, [sp, #7808]
    +0x504c: ldr     d17, [sp, #7832]
    +0x5050: ldr     d16, [sp, #7824]
    +0x5054: str     d0, [sp, #7776]
    +0x5058: eor     v3.8b, v7.8b, v3.8b
    +0x505c: ldr     d7, [x20, #1552]
    +0x5060: eor     v5.8b, v6.8b, v5.8b
    +0x5064: ldr     d6, [x20, #1544]
    +0x5068: ldr     d0, [sp, #7848]
    +0x506c: str     d1, [sp, #7784]
    +0x5070: eor     v7.8b, v17.8b, v7.8b
    +0x5074: ldr     d1, [x20, #1568]
    +0x5078: str     d4, [sp, #7792]
    +0x507c: ldr     d4, [x20, #1576]
    +0x5080: eor     v6.8b, v16.8b, v6.8b
    +0x5084: ldr     d17, [sp, #7856]
    +0x5088: eor     v0.8b, v0.8b, v1.8b
    +0x508c: str     d2, [sp, #7800]
    +0x5090: ldr     d1, [sp, #7864]
    +0x5094: eor     v2.8b, v17.8b, v4.8b
    +0x5098: ldr     d4, [x20, #1584]
    +0x509c: str     d5, [sp, #7808]
    +0x50a0: str     d3, [sp, #7816]
    +0x50a4: ldr     d3, [x20, #1592]
    +0x50a8: ldr     d5, [sp, #7872]
    +0x50ac: eor     v1.8b, v1.8b, v4.8b
    +0x50b0: str     d6, [sp, #7824]
    +0x50b4: ldr     d4, [sp, #7880]
    +0x50b8: eor     v3.8b, v5.8b, v3.8b
    +0x50bc: str     d7, [sp, #7832]
    +0x50c0: ldr     d5, [x20, #1600]
    +0x50c4: ldr     d6, [x20, #1608]
    +0x50c8: ldr     d7, [sp, #7888]
    +0x50cc: ldr     d16, [x20, #1560]
    +0x50d0: eor     v4.8b, v4.8b, v5.8b
    +0x50d4: ldr     d18, [sp, #7840]
    +0x50d8: str     d0, [sp, #7848]
    +0x50dc: eor     v5.8b, v7.8b, v6.8b
    +0x50e0: ldr     d0, [sp, #7896]
    +0x50e4: ldr     d6, [x20, #1616]
    +0x50e8: eor     v16.8b, v18.8b, v16.8b
    +0x50ec: str     d2, [sp, #7856]
    +0x50f0: ldr     d2, [sp, #7904]
    +0x50f4: eor     v0.8b, v0.8b, v6.8b
    +0x50f8: str     d1, [sp, #7864]
    +0x50fc: ldr     d1, [x20, #1624]
    +0x5100: str     d3, [sp, #7872]
    +0x5104: eor     v1.8b, v2.8b, v1.8b
    +0x5108: str     d16, [sp, #7840]
    +0x510c: str     d4, [sp, #7880]
    +0x5110: str     d5, [sp, #7888]
    +0x5114: str     d0, [sp, #7896]
    +0x5118: str     d1, [sp, #7904]
    +0x511c: bl      <mldsa_keccakf1600_permute>
    +0x5120: ldr     d0, [x20, #1632]
    +0x5124: ldr     d1, [sp, #7776]
    +0x5128: add     x0, sp, #0x1, lsl #12
    +0x512c: ldr     d2, [x20, #1640]
    +0x5130: ldr     d3, [sp, #7784]
    +0x5134: add     x0, x0, #0xe60
    +0x5138: eor     v0.8b, v1.8b, v0.8b
    +0x513c: ldr     d4, [x20, #1648]
    +0x5140: ldr     d5, [sp, #7792]
    +0x5144: eor     v1.8b, v3.8b, v2.8b
    +0x5148: ldr     d2, [x20, #1656]
    +0x514c: ldr     d3, [sp, #7800]
    +0x5150: ldr     d7, [sp, #7816]
    +0x5154: eor     v4.8b, v5.8b, v4.8b
    +0x5158: ldr     d5, [x20, #1664]
    +0x515c: eor     v2.8b, v3.8b, v2.8b
    +0x5160: ldr     d3, [x20, #1672]
    +0x5164: ldr     d6, [sp, #7808]
    +0x5168: ldr     d17, [sp, #7832]
    +0x516c: ldr     d16, [sp, #7824]
    +0x5170: str     d0, [sp, #7776]
    +0x5174: eor     v3.8b, v7.8b, v3.8b
    +0x5178: ldr     d7, [x20, #1688]
    +0x517c: eor     v5.8b, v6.8b, v5.8b
    +0x5180: ldr     d6, [x20, #1680]
    +0x5184: ldr     d0, [sp, #7848]
    +0x5188: str     d1, [sp, #7784]
    +0x518c: eor     v7.8b, v17.8b, v7.8b
    +0x5190: ldr     d1, [x20, #1704]
    +0x5194: str     d4, [sp, #7792]
    +0x5198: ldr     d4, [x20, #1712]
    +0x519c: eor     v6.8b, v16.8b, v6.8b
    +0x51a0: ldr     d17, [sp, #7856]
    +0x51a4: eor     v0.8b, v0.8b, v1.8b
    +0x51a8: str     d2, [sp, #7800]
    +0x51ac: ldr     d1, [sp, #7864]
    +0x51b0: eor     v2.8b, v17.8b, v4.8b
    +0x51b4: ldr     d4, [x20, #1720]
    +0x51b8: str     d5, [sp, #7808]
    +0x51bc: str     d3, [sp, #7816]
    +0x51c0: ldr     d3, [x20, #1728]
    +0x51c4: ldr     d5, [sp, #7872]
    +0x51c8: eor     v1.8b, v1.8b, v4.8b
    +0x51cc: str     d6, [sp, #7824]
    +0x51d0: ldr     d4, [sp, #7880]
    +0x51d4: eor     v3.8b, v5.8b, v3.8b
    +0x51d8: str     d7, [sp, #7832]
    +0x51dc: ldr     d5, [x20, #1736]
    +0x51e0: ldr     d6, [x20, #1744]
    +0x51e4: ldr     d7, [sp, #7888]
    +0x51e8: ldr     d16, [x20, #1696]
    +0x51ec: eor     v4.8b, v4.8b, v5.8b
    +0x51f0: ldr     d18, [sp, #7840]
    +0x51f4: str     d0, [sp, #7848]
    +0x51f8: eor     v5.8b, v7.8b, v6.8b
    +0x51fc: ldr     d0, [sp, #7896]
    +0x5200: ldr     d6, [x20, #1752]
    +0x5204: eor     v16.8b, v18.8b, v16.8b
    +0x5208: str     d2, [sp, #7856]
    +0x520c: ldr     d2, [sp, #7904]
    +0x5210: eor     v0.8b, v0.8b, v6.8b
    +0x5214: str     d1, [sp, #7864]
    +0x5218: ldr     d1, [x20, #1760]
    +0x521c: str     d3, [sp, #7872]
    +0x5220: eor     v1.8b, v2.8b, v1.8b
    +0x5224: str     d16, [sp, #7840]
    +0x5228: str     d4, [sp, #7880]
    +0x522c: str     d5, [sp, #7888]
    +0x5230: str     d0, [sp, #7896]
    +0x5234: str     d1, [sp, #7904]
    +0x5238: bl      <mldsa_keccakf1600_permute>
    +0x523c: ldr     d0, [x20, #1768]
    +0x5240: ldr     d1, [sp, #7776]
    +0x5244: add     x0, sp, #0x1, lsl #12
    +0x5248: ldr     d2, [x20, #1776]
    +0x524c: ldr     d3, [sp, #7784]
    +0x5250: add     x0, x0, #0xe60
    +0x5254: eor     v0.8b, v1.8b, v0.8b
    +0x5258: ldr     d4, [x20, #1784]
    +0x525c: ldr     d5, [sp, #7792]
    +0x5260: eor     v1.8b, v3.8b, v2.8b
    +0x5264: ldr     d2, [x20, #1792]
    +0x5268: ldr     d3, [sp, #7800]
    +0x526c: ldr     d7, [sp, #7816]
    +0x5270: eor     v4.8b, v5.8b, v4.8b
    +0x5274: ldr     d5, [x20, #1800]
    +0x5278: eor     v2.8b, v3.8b, v2.8b
    +0x527c: ldr     d3, [x20, #1808]
    +0x5280: ldr     d6, [sp, #7808]
    +0x5284: ldr     d17, [sp, #7832]
    +0x5288: ldr     d16, [sp, #7824]
    +0x528c: str     d0, [sp, #7776]
    +0x5290: eor     v3.8b, v7.8b, v3.8b
    +0x5294: ldr     d7, [x20, #1824]
    +0x5298: eor     v5.8b, v6.8b, v5.8b
    +0x529c: ldr     d6, [x20, #1816]
    +0x52a0: ldr     d0, [sp, #7848]
    +0x52a4: str     d1, [sp, #7784]
    +0x52a8: eor     v7.8b, v17.8b, v7.8b
    +0x52ac: ldr     d1, [x20, #1840]
    +0x52b0: str     d4, [sp, #7792]
    +0x52b4: ldr     d4, [x20, #1848]
    +0x52b8: eor     v6.8b, v16.8b, v6.8b
    +0x52bc: ldr     d17, [sp, #7856]
    +0x52c0: eor     v0.8b, v0.8b, v1.8b
    +0x52c4: str     d2, [sp, #7800]
    +0x52c8: ldr     d1, [sp, #7864]
    +0x52cc: eor     v2.8b, v17.8b, v4.8b
    +0x52d0: ldr     d4, [x20, #1856]
    +0x52d4: str     d5, [sp, #7808]
    +0x52d8: str     d3, [sp, #7816]
    +0x52dc: ldr     d3, [x20, #1864]
    +0x52e0: ldr     d5, [sp, #7872]
    +0x52e4: eor     v1.8b, v1.8b, v4.8b
    +0x52e8: str     d6, [sp, #7824]
    +0x52ec: ldr     d4, [sp, #7880]
    +0x52f0: eor     v3.8b, v5.8b, v3.8b
    +0x52f4: str     d7, [sp, #7832]
    +0x52f8: ldr     d5, [x20, #1872]
    +0x52fc: ldr     d6, [x20, #1880]
    +0x5300: ldr     d7, [sp, #7888]
    +0x5304: ldr     d16, [x20, #1832]
    +0x5308: eor     v4.8b, v4.8b, v5.8b
    +0x530c: ldr     d18, [sp, #7840]
    +0x5310: str     d0, [sp, #7848]
    +0x5314: eor     v5.8b, v7.8b, v6.8b
    +0x5318: ldr     d0, [sp, #7896]
    +0x531c: ldr     d6, [x20, #1888]
    +0x5320: eor     v16.8b, v18.8b, v16.8b
    +0x5324: str     d2, [sp, #7856]
    +0x5328: ldr     d2, [sp, #7904]
    +0x532c: eor     v0.8b, v0.8b, v6.8b
    +0x5330: str     d1, [sp, #7864]
    +0x5334: ldr     d1, [x20, #1896]
    +0x5338: str     d3, [sp, #7872]
    +0x533c: eor     v1.8b, v2.8b, v1.8b
    +0x5340: str     d16, [sp, #7840]
    +0x5344: str     d4, [sp, #7880]
    +0x5348: str     d5, [sp, #7888]
    +0x534c: str     d0, [sp, #7896]
    +0x5350: str     d1, [sp, #7904]
    +0x5354: bl      <mldsa_keccakf1600_permute>
    +0x5358: ldr     d0, [x20, #1904]
    +0x535c: ldr     d1, [sp, #7776]
    +0x5360: add     x0, sp, #0x1, lsl #12
    +0x5364: ldr     d2, [x20, #1912]
    +0x5368: ldr     d3, [sp, #7784]
    +0x536c: add     x0, x0, #0xe60
    +0x5370: eor     v0.8b, v1.8b, v0.8b
    +0x5374: ldr     d4, [x20, #1920]
    +0x5378: ldr     d5, [sp, #7792]
    +0x537c: eor     v1.8b, v3.8b, v2.8b
    +0x5380: ldr     d2, [x20, #1928]
    +0x5384: ldr     d3, [sp, #7800]
    +0x5388: ldr     d7, [sp, #7816]
    +0x538c: eor     v4.8b, v5.8b, v4.8b
    +0x5390: ldr     d5, [x20, #1936]
    +0x5394: eor     v2.8b, v3.8b, v2.8b
    +0x5398: ldr     d3, [x20, #1944]
    +0x539c: ldr     d6, [sp, #7808]
    +0x53a0: ldr     d17, [sp, #7832]
    +0x53a4: ldr     d16, [sp, #7824]
    +0x53a8: str     d0, [sp, #7776]
    +0x53ac: eor     v3.8b, v7.8b, v3.8b
    +0x53b0: ldr     d7, [x20, #1960]
    +0x53b4: eor     v5.8b, v6.8b, v5.8b
    +0x53b8: ldr     d6, [x20, #1952]
    +0x53bc: ldr     d0, [sp, #7848]
    +0x53c0: str     d1, [sp, #7784]
    +0x53c4: eor     v7.8b, v17.8b, v7.8b
    +0x53c8: ldr     d1, [x20, #1976]
    +0x53cc: str     d4, [sp, #7792]
    +0x53d0: ldr     d4, [x20, #1984]
    +0x53d4: eor     v6.8b, v16.8b, v6.8b
    +0x53d8: ldr     d17, [sp, #7856]
    +0x53dc: eor     v0.8b, v0.8b, v1.8b
    +0x53e0: str     d2, [sp, #7800]
    +0x53e4: ldr     d1, [sp, #7864]
    +0x53e8: eor     v2.8b, v17.8b, v4.8b
    +0x53ec: ldr     d4, [x20, #1992]
    +0x53f0: str     d5, [sp, #7808]
    +0x53f4: str     d3, [sp, #7816]
    +0x53f8: ldr     d3, [x20, #2000]
    +0x53fc: ldr     d5, [sp, #7872]
    +0x5400: eor     v1.8b, v1.8b, v4.8b
    +0x5404: str     d6, [sp, #7824]
    +0x5408: ldr     d4, [sp, #7880]
    +0x540c: eor     v3.8b, v5.8b, v3.8b
    +0x5410: str     d7, [sp, #7832]
    +0x5414: ldr     d5, [x20, #2008]
    +0x5418: ldr     d6, [x20, #2016]
    +0x541c: ldr     d7, [sp, #7888]
    +0x5420: ldr     d16, [x20, #1968]
    +0x5424: eor     v4.8b, v4.8b, v5.8b
    +0x5428: ldr     d18, [sp, #7840]
    +0x542c: str     d0, [sp, #7848]
    +0x5430: eor     v5.8b, v7.8b, v6.8b
    +0x5434: ldr     d0, [sp, #7896]
    +0x5438: ldr     d6, [x20, #2024]
    +0x543c: eor     v16.8b, v18.8b, v16.8b
    +0x5440: str     d2, [sp, #7856]
    +0x5444: ldr     d2, [sp, #7904]
    +0x5448: eor     v0.8b, v0.8b, v6.8b
    +0x544c: str     d1, [sp, #7864]
    +0x5450: ldr     d1, [x20, #2032]
    +0x5454: str     d3, [sp, #7872]
    +0x5458: eor     v1.8b, v2.8b, v1.8b
    +0x545c: str     d16, [sp, #7840]
    +0x5460: str     d4, [sp, #7880]
    +0x5464: str     d5, [sp, #7888]
    +0x5468: str     d0, [sp, #7896]
    +0x546c: str     d1, [sp, #7904]
    +0x5470: bl      <mldsa_keccakf1600_permute>
    +0x5474: ldr     d0, [x20, #2040]
    +0x5478: ldr     d1, [sp, #7776]
    +0x547c: add     x0, sp, #0x1, lsl #12
    +0x5480: ldr     d2, [x20, #2048]
    +0x5484: ldr     d3, [sp, #7784]
    +0x5488: add     x0, x0, #0xe60
    +0x548c: eor     v0.8b, v1.8b, v0.8b
    +0x5490: ldr     d4, [x20, #2056]
    +0x5494: ldr     d5, [sp, #7792]
    +0x5498: eor     v1.8b, v3.8b, v2.8b
    +0x549c: ldr     d2, [x20, #2064]
    +0x54a0: ldr     d3, [sp, #7800]
    +0x54a4: ldr     d7, [sp, #7816]
    +0x54a8: eor     v4.8b, v5.8b, v4.8b
    +0x54ac: ldr     d5, [x20, #2072]
    +0x54b0: eor     v2.8b, v3.8b, v2.8b
    +0x54b4: ldr     d3, [x20, #2080]
    +0x54b8: ldr     d6, [sp, #7808]
    +0x54bc: ldr     d17, [sp, #7832]
    +0x54c0: ldr     d16, [sp, #7824]
    +0x54c4: str     d0, [sp, #7776]
    +0x54c8: eor     v3.8b, v7.8b, v3.8b
    +0x54cc: ldr     d7, [x20, #2096]
    +0x54d0: eor     v5.8b, v6.8b, v5.8b
    +0x54d4: ldr     d6, [x20, #2088]
    +0x54d8: ldr     d0, [sp, #7848]
    +0x54dc: str     d1, [sp, #7784]
    +0x54e0: eor     v7.8b, v17.8b, v7.8b
    +0x54e4: ldr     d1, [x20, #2112]
    +0x54e8: str     d4, [sp, #7792]
    +0x54ec: ldr     d4, [x20, #2120]
    +0x54f0: eor     v6.8b, v16.8b, v6.8b
    +0x54f4: ldr     d17, [sp, #7856]
    +0x54f8: eor     v0.8b, v0.8b, v1.8b
    +0x54fc: str     d2, [sp, #7800]
    +0x5500: ldr     d1, [sp, #7864]
    +0x5504: eor     v2.8b, v17.8b, v4.8b
    +0x5508: ldr     d4, [x20, #2128]
    +0x550c: str     d5, [sp, #7808]
    +0x5510: str     d3, [sp, #7816]
    +0x5514: ldr     d3, [x20, #2136]
    +0x5518: ldr     d5, [sp, #7872]
    +0x551c: eor     v1.8b, v1.8b, v4.8b
    +0x5520: str     d6, [sp, #7824]
    +0x5524: ldr     d4, [sp, #7880]
    +0x5528: eor     v3.8b, v5.8b, v3.8b
    +0x552c: str     d7, [sp, #7832]
    +0x5530: ldr     d5, [x20, #2144]
    +0x5534: ldr     d6, [x20, #2152]
    +0x5538: ldr     d7, [sp, #7888]
    +0x553c: ldr     d16, [x20, #2104]
    +0x5540: eor     v4.8b, v4.8b, v5.8b
    +0x5544: ldr     d18, [sp, #7840]
    +0x5548: str     d0, [sp, #7848]
    +0x554c: eor     v5.8b, v7.8b, v6.8b
    +0x5550: ldr     d0, [sp, #7896]
    +0x5554: ldr     d6, [x20, #2160]
    +0x5558: eor     v16.8b, v18.8b, v16.8b
    +0x555c: str     d2, [sp, #7856]
    +0x5560: ldr     d2, [sp, #7904]
    +0x5564: eor     v0.8b, v0.8b, v6.8b
    +0x5568: str     d1, [sp, #7864]
    +0x556c: ldr     d1, [x20, #2168]
    +0x5570: str     d3, [sp, #7872]
    +0x5574: eor     v1.8b, v2.8b, v1.8b
    +0x5578: str     d16, [sp, #7840]
    +0x557c: str     d4, [sp, #7880]
    +0x5580: str     d5, [sp, #7888]
    +0x5584: str     d0, [sp, #7896]
    +0x5588: str     d1, [sp, #7904]
    +0x558c: bl      <mldsa_keccakf1600_permute>
    +0x5590: ldr     d0, [x20, #2176]
    +0x5594: ldr     d1, [sp, #7776]
    +0x5598: add     x0, sp, #0x1, lsl #12
    +0x559c: ldr     d2, [x20, #2184]
    +0x55a0: ldr     d3, [sp, #7784]
    +0x55a4: add     x0, x0, #0xe60
    +0x55a8: eor     v0.8b, v1.8b, v0.8b
    +0x55ac: ldr     d4, [x20, #2192]
    +0x55b0: ldr     d5, [sp, #7792]
    +0x55b4: eor     v1.8b, v3.8b, v2.8b
    +0x55b8: ldr     d2, [x20, #2200]
    +0x55bc: ldr     d3, [sp, #7800]
    +0x55c0: ldr     d7, [sp, #7816]
    +0x55c4: eor     v4.8b, v5.8b, v4.8b
    +0x55c8: ldr     d5, [x20, #2208]
    +0x55cc: eor     v2.8b, v3.8b, v2.8b
    +0x55d0: ldr     d3, [x20, #2216]
    +0x55d4: ldr     d6, [sp, #7808]
    +0x55d8: ldr     d17, [sp, #7832]
    +0x55dc: ldr     d16, [sp, #7824]
    +0x55e0: str     d0, [sp, #7776]
    +0x55e4: eor     v3.8b, v7.8b, v3.8b
    +0x55e8: ldr     d7, [x20, #2232]
    +0x55ec: eor     v5.8b, v6.8b, v5.8b
    +0x55f0: ldr     d6, [x20, #2224]
    +0x55f4: ldr     d0, [sp, #7848]
    +0x55f8: str     d1, [sp, #7784]
    +0x55fc: eor     v7.8b, v17.8b, v7.8b
    +0x5600: ldr     d1, [x20, #2248]
    +0x5604: str     d4, [sp, #7792]
    +0x5608: ldr     d4, [x20, #2256]
    +0x560c: eor     v6.8b, v16.8b, v6.8b
    +0x5610: ldr     d17, [sp, #7856]
    +0x5614: eor     v0.8b, v0.8b, v1.8b
    +0x5618: str     d2, [sp, #7800]
    +0x561c: ldr     d1, [sp, #7864]
    +0x5620: eor     v2.8b, v17.8b, v4.8b
    +0x5624: ldr     d4, [x20, #2264]
    +0x5628: str     d5, [sp, #7808]
    +0x562c: str     d3, [sp, #7816]
    +0x5630: ldr     d3, [x20, #2272]
    +0x5634: ldr     d5, [sp, #7872]
    +0x5638: eor     v1.8b, v1.8b, v4.8b
    +0x563c: str     d6, [sp, #7824]
    +0x5640: ldr     d4, [sp, #7880]
    +0x5644: eor     v3.8b, v5.8b, v3.8b
    +0x5648: str     d7, [sp, #7832]
    +0x564c: ldr     d5, [x20, #2280]
    +0x5650: ldr     d6, [x20, #2288]
    +0x5654: ldr     d7, [sp, #7888]
    +0x5658: ldr     d16, [x20, #2240]
    +0x565c: eor     v4.8b, v4.8b, v5.8b
    +0x5660: ldr     d18, [sp, #7840]
    +0x5664: str     d0, [sp, #7848]
    +0x5668: eor     v5.8b, v7.8b, v6.8b
    +0x566c: ldr     d0, [sp, #7896]
    +0x5670: ldr     d6, [x20, #2296]
    +0x5674: eor     v16.8b, v18.8b, v16.8b
    +0x5678: str     d2, [sp, #7856]
    +0x567c: ldr     d2, [sp, #7904]
    +0x5680: eor     v0.8b, v0.8b, v6.8b
    +0x5684: str     d1, [sp, #7864]
    +0x5688: ldr     d1, [x20, #2304]
    +0x568c: str     d3, [sp, #7872]
    +0x5690: eor     v1.8b, v2.8b, v1.8b
    +0x5694: str     d16, [sp, #7840]
    +0x5698: str     d4, [sp, #7880]
    +0x569c: str     d5, [sp, #7888]
    +0x56a0: str     d0, [sp, #7896]
    +0x56a4: str     d1, [sp, #7904]
    +0x56a8: bl      <mldsa_keccakf1600_permute>
    +0x56ac: ldr     d0, [x20, #2312]
    +0x56b0: ldr     d1, [sp, #7776]
    +0x56b4: add     x0, sp, #0x1, lsl #12
    +0x56b8: ldr     d2, [x20, #2320]
    +0x56bc: ldr     d3, [sp, #7784]
    +0x56c0: add     x0, x0, #0xe60
    +0x56c4: eor     v0.8b, v1.8b, v0.8b
    +0x56c8: ldr     d4, [x20, #2328]
    +0x56cc: ldr     d5, [sp, #7792]
    +0x56d0: eor     v1.8b, v3.8b, v2.8b
    +0x56d4: ldr     d2, [x20, #2336]
    +0x56d8: ldr     d3, [sp, #7800]
    +0x56dc: ldr     d7, [sp, #7816]
    +0x56e0: eor     v4.8b, v5.8b, v4.8b
    +0x56e4: ldr     d5, [x20, #2344]
    +0x56e8: eor     v2.8b, v3.8b, v2.8b
    +0x56ec: ldr     d3, [x20, #2352]
    +0x56f0: ldr     d6, [sp, #7808]
    +0x56f4: ldr     d17, [sp, #7832]
    +0x56f8: ldr     d16, [sp, #7824]
    +0x56fc: str     d0, [sp, #7776]
    +0x5700: eor     v3.8b, v7.8b, v3.8b
    +0x5704: ldr     d7, [x20, #2368]
    +0x5708: eor     v5.8b, v6.8b, v5.8b
    +0x570c: ldr     d6, [x20, #2360]
    +0x5710: ldr     d0, [sp, #7848]
    +0x5714: str     d1, [sp, #7784]
    +0x5718: eor     v7.8b, v17.8b, v7.8b
    +0x571c: ldr     d1, [x20, #2384]
    +0x5720: str     d4, [sp, #7792]
    +0x5724: ldr     d4, [x20, #2392]
    +0x5728: eor     v6.8b, v16.8b, v6.8b
    +0x572c: ldr     d17, [sp, #7856]
    +0x5730: eor     v0.8b, v0.8b, v1.8b
    +0x5734: str     d2, [sp, #7800]
    +0x5738: ldr     d1, [sp, #7864]
    +0x573c: eor     v2.8b, v17.8b, v4.8b
    +0x5740: ldr     d4, [x20, #2400]
    +0x5744: str     d5, [sp, #7808]
    +0x5748: str     d3, [sp, #7816]
    +0x574c: ldr     d3, [x20, #2408]
    +0x5750: ldr     d5, [sp, #7872]
    +0x5754: eor     v1.8b, v1.8b, v4.8b
    +0x5758: str     d6, [sp, #7824]
    +0x575c: ldr     d4, [sp, #7880]
    +0x5760: eor     v3.8b, v5.8b, v3.8b
    +0x5764: str     d7, [sp, #7832]
    +0x5768: ldr     d5, [x20, #2416]
    +0x576c: ldr     d6, [x20, #2424]
    +0x5770: ldr     d7, [sp, #7888]
    +0x5774: ldr     d16, [x20, #2376]
    +0x5778: eor     v4.8b, v4.8b, v5.8b
    +0x577c: ldr     d18, [sp, #7840]
    +0x5780: str     d0, [sp, #7848]
    +0x5784: eor     v5.8b, v7.8b, v6.8b
    +0x5788: ldr     d0, [sp, #7896]
    +0x578c: ldr     d6, [x20, #2432]
    +0x5790: eor     v16.8b, v18.8b, v16.8b
    +0x5794: str     d2, [sp, #7856]
    +0x5798: ldr     d2, [sp, #7904]
    +0x579c: eor     v0.8b, v0.8b, v6.8b
    +0x57a0: str     d1, [sp, #7864]
    +0x57a4: ldr     d1, [x20, #2440]
    +0x57a8: str     d3, [sp, #7872]
    +0x57ac: eor     v1.8b, v2.8b, v1.8b
    +0x57b0: str     d16, [sp, #7840]
    +0x57b4: str     d4, [sp, #7880]
    +0x57b8: str     d5, [sp, #7888]
    +0x57bc: str     d0, [sp, #7896]
    +0x57c0: str     d1, [sp, #7904]
    +0x57c4: bl      <mldsa_keccakf1600_permute>
    +0x57c8: ldr     d0, [x20, #2448]
    +0x57cc: ldr     d1, [sp, #7776]
    +0x57d0: add     x0, sp, #0x1, lsl #12
    +0x57d4: ldr     d2, [x20, #2456]
    +0x57d8: ldr     d3, [sp, #7784]
    +0x57dc: add     x0, x0, #0xe60
    +0x57e0: eor     v0.8b, v1.8b, v0.8b
    +0x57e4: ldr     d4, [x20, #2464]
    +0x57e8: ldr     d5, [sp, #7792]
    +0x57ec: eor     v1.8b, v3.8b, v2.8b
    +0x57f0: ldr     d2, [x20, #2472]
    +0x57f4: ldr     d3, [sp, #7800]
    +0x57f8: ldr     d7, [sp, #7816]
    +0x57fc: eor     v4.8b, v5.8b, v4.8b
    +0x5800: ldr     d5, [x20, #2480]
    +0x5804: eor     v2.8b, v3.8b, v2.8b
    +0x5808: ldr     d3, [x20, #2488]
    +0x580c: ldr     d6, [sp, #7808]
    +0x5810: ldr     d17, [sp, #7832]
    +0x5814: ldr     d16, [sp, #7824]
    +0x5818: str     d0, [sp, #7776]
    +0x581c: eor     v3.8b, v7.8b, v3.8b
    +0x5820: ldr     d7, [x20, #2504]
    +0x5824: eor     v5.8b, v6.8b, v5.8b
    +0x5828: ldr     d6, [x20, #2496]
    +0x582c: ldr     d0, [sp, #7848]
    +0x5830: str     d1, [sp, #7784]
    +0x5834: eor     v7.8b, v17.8b, v7.8b
    +0x5838: ldr     d1, [x20, #2520]
    +0x583c: str     d4, [sp, #7792]
    +0x5840: ldr     d4, [x20, #2528]
    +0x5844: eor     v6.8b, v16.8b, v6.8b
    +0x5848: ldr     d17, [sp, #7856]
    +0x584c: eor     v0.8b, v0.8b, v1.8b
    +0x5850: str     d2, [sp, #7800]
    +0x5854: ldr     d1, [sp, #7864]
    +0x5858: eor     v2.8b, v17.8b, v4.8b
    +0x585c: ldr     d4, [x20, #2536]
    +0x5860: str     d5, [sp, #7808]
    +0x5864: str     d3, [sp, #7816]
    +0x5868: ldr     d3, [x20, #2544]
    +0x586c: ldr     d5, [sp, #7872]
    +0x5870: eor     v1.8b, v1.8b, v4.8b
    +0x5874: str     d6, [sp, #7824]
    +0x5878: ldr     d4, [sp, #7880]
    +0x587c: eor     v3.8b, v5.8b, v3.8b
    +0x5880: str     d7, [sp, #7832]
    +0x5884: ldr     d5, [x20, #2552]
    +0x5888: ldr     d6, [x20, #2560]
    +0x588c: ldr     d7, [sp, #7888]
    +0x5890: ldr     d16, [x20, #2512]
    +0x5894: eor     v4.8b, v4.8b, v5.8b
    +0x5898: ldr     d18, [sp, #7840]
    +0x589c: str     d0, [sp, #7848]
    +0x58a0: eor     v5.8b, v7.8b, v6.8b
    +0x58a4: ldr     d0, [sp, #7896]
    +0x58a8: ldr     d6, [x20, #2568]
    +0x58ac: eor     v16.8b, v18.8b, v16.8b
    +0x58b0: str     d2, [sp, #7856]
    +0x58b4: ldr     d2, [sp, #7904]
    +0x58b8: eor     v0.8b, v0.8b, v6.8b
    +0x58bc: str     d1, [sp, #7864]
    +0x58c0: ldr     d1, [x20, #2576]
    +0x58c4: str     d3, [sp, #7872]
    +0x58c8: eor     v1.8b, v2.8b, v1.8b
    +0x58cc: str     d16, [sp, #7840]
    +0x58d0: str     d4, [sp, #7880]
    +0x58d4: str     d5, [sp, #7888]
    +0x58d8: str     d0, [sp, #7896]
    +0x58dc: str     d1, [sp, #7904]
    +0x58e0: bl      <mldsa_keccakf1600_permute>
    +0x58e4: ldr     d0, [x20, #2584]
    +0x58e8: ldr     d1, [sp, #7776]
    +0x58ec: add     x0, sp, #0x1, lsl #12
    +0x58f0: ldrb    w8, [x21, #8]
    +0x58f4: ldrb    w9, [x21, #135]
    +0x58f8: add     x0, x0, #0xe60
    +0x58fc: eor     v0.8b, v1.8b, v0.8b
    +0x5900: eor     w8, w8, #0x1f
    +0x5904: eor     w9, w9, #0x80
    +0x5908: strb    w8, [x21, #8]
    +0x590c: mov     w8, #0x88
    +0x5910: strb    w9, [x21, #135]
    +0x5914: str     d0, [sp, #7776]
    +0x5918: str     w8, [sp, #7976]
    +0x591c: bl      <mldsa_keccakf1600_permute>
    +0x5920: ldr     q0, [sp, #7776]
    +0x5924: ldr     q1, [sp, #7792]
    +0x5928: add     x0, sp, #0x160
    +0x592c: ldr     q2, [sp, #7824]
    +0x5930: mov     w1, wzr
    +0x5934: mov     w2, #0x1c00
    +0x5938: str     q0, [sp, #7520]
    +0x593c: ldr     q0, [sp, #7808]
    +0x5940: str     q1, [sp, #7536]
    +0x5944: str     q0, [sp, #7552]
    +0x5948: movi    v0.2d, #0x0
    +0x594c: str     q2, [sp, #7568]
    +0x5950: str     q0, [sp, #7840]
    +0x5954: str     q0, [sp, #7856]
    +0x5958: str     q0, [sp, #7872]
    +0x595c: str     q0, [sp, #7888]
    +0x5960: str     q0, [sp, #7904]
    +0x5964: str     q0, [sp, #7920]
    +0x5968: str     q0, [sp, #7936]
    +0x596c: str     q0, [sp, #7952]
    +0x5970: str     q0, [sp, #7968]
    +0x5974: str     q0, [sp, #7776]
    +0x5978: str     q0, [sp, #7792]
    +0x597c: str     q0, [sp, #7808]
    +0x5980: str     q0, [sp, #7824]
    +0x5984: ldr     q0, [sp, #7648]
    +0x5988: ldr     q1, [sp, #7664]
    +0x598c: ldr     q2, [sp, #7744]
    +0x5990: stp     q0, q1, [x19]
    +0x5994: ldr     q0, [sp, #7760]
    +0x5998: ldr     q1, [sp, #7520]
    +0x599c: stp     q2, q0, [x19, #32]
    +0x59a0: ldr     q0, [sp, #7536]
    +0x59a4: ldr     q2, [sp, #7552]
    +0x59a8: stp     q1, q0, [x19, #64]
    +0x59ac: ldr     q0, [sp, #7568]
    +0x59b0: stp     q2, q0, [x19, #96]
    +0x59b4: bl      <memset>
    +0x59b8: movi    v0.2d, #0x0
    +0x59bc: add     x8, sp, #0x1, lsl #12
    +0x59c0: add     x8, x8, #0xd60
    +0x59c4: str     q0, [sp, #7568]
    +0x59c8: str     q0, [sp, #7552]
    +0x59cc: str     q0, [sp, #7536]
    +0x59d0: str     q0, [sp, #7520]
    +0x59d4: strh    wzr, [sp, #7616]
    +0x59d8: add     x8, sp, #0x1, lsl #12
    +0x59dc: str     q0, [sp, #7600]
    +0x59e0: add     x8, x8, #0xda0
    +0x59e4: str     q0, [sp, #7584]
    +0x59e8: str     q0, [sp, #7760]
    +0x59ec: adrp    x8, <page>
    +0x59f0: str     q0, [sp, #7744]
    +0x59f4: str     q0, [sp, #7728]
    +0x59f8: str     q0, [sp, #7712]
    +0x59fc: str     q0, [sp, #7696]
    +0x5a00: str     q0, [sp, #7680]
    +0x5a04: str     q0, [sp, #7664]
    +0x5a08: str     q0, [sp, #7648]
    +0x5a0c: ldr     x8, [x8, #4088]
    +0x5a10: ldr     x9, [sp, #7992]
    +0x5a14: ldr     x8, [x8]
    +0x5a18: cmp     x8, x9
    +0x5a1c: b.ne    <mldsa87_keypair_internal+0x5a9c>
    +0x5a20: mov     w0, wzr
    +0x5a24: sub     sp, x29, #0x40
    +0x5a28: ldp     x20, x19, [sp, #144]
    +0x5a2c: ldp     x22, x21, [sp, #128]
    +0x5a30: ldp     x24, x23, [sp, #112]
    +0x5a34: ldp     x26, x25, [sp, #96]
    +0x5a38: ldp     x28, x27, [sp, #80]
    +0x5a3c: ldp     x29, x30, [sp, #64]
    +0x5a40: ldp     d9, d8, [sp, #48]
    +0x5a44: ldp     d11, d10, [sp, #32]
    +0x5a48: ldp     d13, d12, [sp, #16]
    +0x5a4c: ldp     d15, d14, [sp], #160
    +0x5a50: mov     x1, #0x0
    +0x5a54: mov     x2, #0x0
    +0x5a58: mov     x3, #0x0
    +0x5a5c: mov     x4, #0x0
    +0x5a60: mov     x5, #0x0
    +0x5a64: mov     x6, #0x0
    +0x5a68: mov     x7, #0x0
    +0x5a6c: mov     x8, #0x0
    +0x5a70: mov     x9, #0x0
    +0x5a74: mov     x10, #0x0
    +0x5a78: mov     x11, #0x0
    +0x5a7c: mov     x12, #0x0
    +0x5a80: mov     x13, #0x0
    +0x5a84: mov     x14, #0x0
    +0x5a88: mov     x15, #0x0
    +0x5a8c: mov     x16, #0x0
    +0x5a90: mov     x17, #0x0
    +0x5a94: mov     x18, #0x0
    +0x5a98: ret     
    +0x5a9c: bl      <__stack_chk_fail>

    memset@plt:
       +0x0: adrp    x16, <page>
       +0x4: ldr     x17, [x16, #4072]
       +0x8: add     x16, x16, #0xfe8
       +0xc: br      x17
 ***)

let MLDSA_NATIVE_KEYPAIR_INTERNAL_87_CLANG23_O3_MONO_REDUCED_RAM_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
   [layout_range "mldsa87_keypair_internal";
    layout_range "plt_memset"];;

(* ------------------------------------------------------------------------- *)
(* Correctness, assuming the contracts for memset and memcpy. From the seed SEED (32     *)
(* bytes at seed), the public key at pk (2592 bytes) becomes                 *)
(* mld_keypair_pk_87 SEED and the secret key at sk (4896 bytes)              *)
(* mld_keypair_sk_87 SEED, and the result is 0. The stack is the 13504 bytes *)
(* below the stack pointer: the frame of the function, of up to 8176 bytes,  *)
(* and the stacks of its callees.                                            *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_KEYPAIR_INTERNAL_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!mf mc ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev
     ==> !pk sk seed SEED guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          32768 <= val stackpointer /\ val(stackpointer:int64) < 2 EXP 63 /\
          mld_matrix_terminates 8 7 (mld_keypair_rho 8 7 SEED) /\
          mld_keypair_terminates_87 SEED /\
          PAIRWISE nonoverlapping
           [(pk,2592); (sk,4896);
            (word_sub stackpointer (word 13504),13504)] /\
          ALLPAIRS nonoverlapping
           [(pk,2592); (sk,4896);
            (word_sub stackpointer (word 13504),13504)]
           [(seed,32); (word pc,libmldsa_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                    read PC s = word (pc + mldsa87_keypair_internal) /\
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
                    (!j. j < 2592
                         ==> read(memory :> bytes8(word_add pk (word j))) s =
                             mld_keypair_pk_87 SEED j) /\
                    (!j. j < 4896
                         ==> read(memory :> bytes8(word_add sk (word j))) s =
                             mld_keypair_sk_87 SEED j))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(pk,2592); memory :> bytes(sk,4896);
                  memory :> bytes(word_sub stackpointer (word 13504),13504)])`;;

let MLDSA_NATIVE_KEYPAIR_INTERNAL_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLDSA_NATIVE_KEYPAIR_INTERNAL_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, rho, whether each nibble read by  *)
(* the sampling of each polynomial is accepted (mld_keypair_declass_87), the *)
(* address of memset and the stack, with all accesses within the arguments,  *)
(* the stack, the GOT entries and the stack guard, the region (ea,el) that   *)
(* memset may read and the constants of the callees, and the writes within   *)
(* the keys and the stack.                                                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_KEYPAIR_INTERNAL_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT =
  `!mf mc ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev
     ==> exists f_events.
          forall e pk sk seed SEED guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          32768 <= val stackpointer /\ val(stackpointer:int64) < 2 EXP 63 /\
          mld_matrix_terminates 8 7 (mld_keypair_rho 8 7 SEED) /\
          mld_keypair_terminates_87 SEED /\
          PAIRWISE nonoverlapping
           [(pk,2592); (sk,4896);
            (word_sub stackpointer (word 13504),13504)] /\
          ALLPAIRS nonoverlapping
           [(pk,2592); (sk,4896);
            (word_sub stackpointer (word 13504),13504)]
           [(seed,32); (word pc,libmldsa_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                    read PC s = word (pc + mldsa87_keypair_internal) /\
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
                    (!j. j < 2592
                         ==> read(memory :> bytes8(word_add pk (word j))) s =
                             mld_keypair_pk_87 SEED j) /\
                    (!j. j < 4896
                         ==> read(memory :> bytes8(word_add sk (word j))) s =
                             mld_keypair_sk_87 SEED j) /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events pk sk seed (mld_keypair_rho 8 7 SEED)
                             (mld_keypair_declass_87 SEED) guard mf mc pc
                             (word_sub stackpointer (word 13504))
                             returnaddress /\
                       memaccess_inbounds e2
                        [seed,32; pk,2592; sk,4896;
                         word_sub stackpointer (word 13504),13504;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; word(pc + got_memcpy),8; ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192;
                         word(pc + rodata_mld_zetas),1024;
                         word(pc + mldsa87_keypair_internal_consts),16;
                         word(pc + mld_compute_pack_t0_t187_consts),272;
                         word(pc + mldsa87_polyeta_unpack_consts),128]
                        [pk,2592; sk,4896;
                         word_sub stackpointer (word 13504),13504]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(pk,2592); memory :> bytes(sk,4896);
                  memory :> bytes(word_sub stackpointer (word 13504),13504)])`;;

let MLDSA_NATIVE_KEYPAIR_INTERNAL_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_KEYPAIR_INTERNAL_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_KEYPAIR_INTERNAL_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT =
  `!mf mc ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev
     ==> exists f_events.
          forall e pk sk seed SEED guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          32768 <= val stackpointer /\ val(stackpointer:int64) < 2 EXP 63 /\
          mld_matrix_terminates 8 7 (mld_keypair_rho 8 7 SEED) /\
          mld_keypair_terminates_87 SEED /\
          PAIRWISE nonoverlapping
           [(pk,2592); (sk,4896);
            (word_sub stackpointer (word 13504),13504)] /\
          ALLPAIRS nonoverlapping
           [(pk,2592); (sk,4896);
            (word_sub stackpointer (word 13504),13504)]
           [(seed,32); (word pc,libmldsa_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                    read PC s = word (pc + mldsa87_keypair_internal) /\
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
                       e2 = f_events pk sk seed (mld_keypair_rho 8 7 SEED)
                             (mld_keypair_declass_87 SEED) guard mf mc pc
                             (word_sub stackpointer (word 13504))
                             returnaddress /\
                       memaccess_inbounds e2
                        [seed,32; pk,2592; sk,4896;
                         word_sub stackpointer (word 13504),13504;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; word(pc + got_memcpy),8; ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192;
                         word(pc + rodata_mld_zetas),1024;
                         word(pc + mldsa87_keypair_internal_consts),16;
                         word(pc + mld_compute_pack_t0_t187_consts),272;
                         word(pc + mldsa87_polyeta_unpack_consts),128]
                        [pk,2592; sk,4896;
                         word_sub stackpointer (word 13504),13504]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(pk,2592); memory :> bytes(sk,4896);
                  memory :> bytes(word_sub stackpointer (word 13504),13504)])`;;

let MLDSA_NATIVE_KEYPAIR_INTERNAL_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_KEYPAIR_INTERNAL_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT;;
