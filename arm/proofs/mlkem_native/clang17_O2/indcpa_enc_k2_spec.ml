(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The encryption of K-PKE for ML-KEM-512 (FIPS 203 Algorithm 14). This is   *)
(* the code for mlkem512_indcpa_enc from mlkem-native's portable C           *)
(* implementation compiled by clang 17 with -O2 (see mlkem_native/README.md).*)
(* It decodes the vector t in the NTT domain from the encryption key and the *)
(* message m from its 32 bytes, generates the transposed matrix from rho     *)
(* (the last 32 bytes of the key), samples y (with eta = 3), e1 and e2 (with *)
(* eta = 2) from the randomness r, and computes u = NTT^-1(A^T NTT(y)) + e1  *)
(* and v = NTT^-1(t^T NTT(y)) + e2 + mu, where mu is m decompressed. It      *)
(* writes the compressions of u and v as the ciphertext, zeroing its         *)
(* buffers. It is verified in the whole image (see                           *)
(* libmlkem.ml), using the theorems for                                      *)
(* mlkem512_polyvec_frombytes, mlkem_poly_frommsg,                           *)
(* mlkem_poly_rej_uniform_x4 (the matrix generation is inlined),             *)
(* mlkem512_poly_getnoise_eta1122_4x, mlkem512_poly_getnoise_eta2,           *)
(* mlkem512_polyvec_ntt, mlkem512_polyvec_mulcache_compute,                  *)
(* mlkem512_polyvec_basemul_acc_montgomery_cached,                           *)
(* mlkem512_polyvec_invntt_tomont, mlkem_poly_invntt_tomont,                 *)
(* mlkem512_polyvec_add, mlkem_poly_add, mlkem512_polyvec_reduce,            *)
(* mlkem_poly_reduce, mlkem512_polyvec_compress_du and                       *)
(* mlkem_poly_compress_d4 in the image, and the contract for memset.         *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/mlkem_native/clang17_O2/polyvec_frombytes_k2_spec.ml";;
needs "arm/proofs/mlkem_native/clang17_O2/poly_frommsg_spec.ml";;
needs "arm/proofs/mlkem_native/clang17_O2/poly_rej_uniform_x4_spec.ml";;
needs "arm/proofs/mlkem_native/clang17_O2/gen_matrix_k2_spec.ml";;
needs "arm/proofs/mlkem_native/clang17_O2/poly_getnoise_eta1122_4x_k2_spec.ml";;
needs "arm/proofs/mlkem_native/clang17_O2/poly_getnoise_eta2_k2_spec.ml";;
needs "arm/proofs/mlkem_native/clang17_O2/polyvec_ntt_k2_spec.ml";;
needs "arm/proofs/mlkem_native/clang17_O2/polyvec_mulcache_compute_k2_spec.ml";;
needs "arm/proofs/mlkem_native/clang17_O2/basemul_k2_spec.ml";;
needs "arm/proofs/mlkem_native/clang17_O2/polyvec_invntt_tomont_k2_spec.ml";;
needs "arm/proofs/mlkem_native/clang17_O2/poly_invntt_tomont_spec.ml";;
needs "arm/proofs/mlkem_native/clang17_O2/polyvec_add_k2_spec.ml";;
needs "arm/proofs/mlkem_native/clang17_O2/poly_add_spec.ml";;
needs "arm/proofs/mlkem_native/clang17_O2/polyvec_reduce_k2_spec.ml";;
needs "arm/proofs/mlkem_native/clang17_O2/poly_reduce_spec.ml";;
needs "arm/proofs/mlkem_native/clang17_O2/polyvec_compress_du_k2_spec.ml";;
needs "arm/proofs/mlkem_native/clang17_O2/poly_compress_d4_spec.ml";;
needs "arm/proofs/utils/mlkem_native_indcpa.ml";;

(*** The code in the image:

    mlkem512_indcpa_enc:
       +0x0: stp     x29, x30, [sp, #-96]!
       +0x4: stp     x28, x27, [sp, #16]
       +0x8: stp     x26, x25, [sp, #32]
       +0xc: stp     x24, x23, [sp, #48]
      +0x10: stp     x22, x21, [sp, #64]
      +0x14: stp     x20, x19, [sp, #80]
      +0x18: mov     x29, sp
      +0x1c: sub     x9, sp, #0x2, lsl #12
      +0x20: sub     x9, x9, #0x60
      +0x24: and     sp, x9, #0xffffffffffffffe0
      +0x28: adrp    x8, <page>
      +0x2c: mov     x19, x0
      +0x30: add     x0, sp, #0x1, lsl #12
      +0x34: mov     x22, x1
      +0x38: add     x0, x0, #0x20
      +0x3c: mov     x1, x2
      +0x40: ldr     x8, [x8, #4088]  // got_stack_chk_guard
      +0x44: add     x23, sp, #0x1, lsl #12
      +0x48: mov     x20, x3
      +0x4c: mov     x21, x2
      +0x50: add     x23, x23, #0x20
      +0x54: ldr     x8, [x8]
      +0x58: str     x8, [sp, #8280]
      +0x5c: bl      <mlkem512_polyvec_frombytes>
      +0x60: ldp     q0, q1, [x21, #768]
      +0x64: add     x0, sp, #0x420
      +0x68: mov     x1, x22
      +0x6c: add     x25, sp, #0x420
      +0x70: str     q0, [sp, #8224]
      +0x74: str     q1, [sp, #8240]
      +0x78: bl      <mlkem_poly_frommsg>
      +0x7c: add     x22, sp, #0x1, lsl #12
      +0x80: add     x0, sp, #0x1, lsl #12
      +0x84: add     x22, x22, #0x820
      +0x88: add     x4, sp, #0x1, lsl #12
      +0x8c: add     x21, x22, #0x400
      +0x90: ldr     q0, [sp, #8224]
      +0x94: ldr     q1, [sp, #8240]
      +0x98: mov     w8, #0x100
      +0x9c: mov     w9, #0x1
      +0xa0: mov     w10, #0x101
      +0xa4: add     x1, x22, #0x200
      +0xa8: add     x3, x22, #0x600
      +0xac: add     x0, x0, #0x820
      +0xb0: add     x4, x4, #0x420
      +0xb4: mov     x2, x21
      +0xb8: add     x24, sp, #0x1, lsl #12
      +0xbc: str     q0, [sp, #5152]
      +0xc0: add     x24, x24, #0x420
      +0xc4: str     q1, [sp, #5168]
      +0xc8: str     q0, [sp, #5216]
      +0xcc: str     q1, [sp, #5232]
      +0xd0: str     q0, [sp, #5280]
      +0xd4: str     q1, [sp, #5296]
      +0xd8: strh    w8, [sp, #5248]
      +0xdc: strh    w9, [sp, #5312]
      +0xe0: strh    w10, [sp, #5376]
      +0xe4: str     q1, [sp, #5360]
      +0xe8: str     q0, [sp, #5344]
      +0xec: strh    wzr, [sp, #5184]
      +0xf0: bl      <mlkem_poly_rej_uniform_x4>
      +0xf4: movi    v0.2d, #0x0
      +0xf8: add     x26, sp, #0xc20
      +0xfc: add     x0, sp, #0x1, lsl #12
     +0x100: add     x1, x24, #0x200
     +0x104: add     x3, x26, #0x200
     +0x108: mov     w8, #0x3
     +0x10c: add     x0, x0, #0x420
     +0x110: add     x2, sp, #0xc20
     +0x114: str     q0, [sp, #5392]
     +0x118: mov     x4, x20
     +0x11c: str     q0, [sp, #5376]
     +0x120: mov     w5, wzr
     +0x124: str     q0, [sp, #5360]
     +0x128: mov     w6, #0x1
     +0x12c: str     q0, [sp, #5344]
     +0x130: mov     w7, #0x2
     +0x134: str     q0, [sp, #5328]
     +0x138: str     q0, [sp, #5312]
     +0x13c: str     q0, [sp, #5296]
     +0x140: str     q0, [sp, #5280]
     +0x144: str     q0, [sp, #5264]
     +0x148: str     q0, [sp, #5248]
     +0x14c: str     q0, [sp, #5232]
     +0x150: str     q0, [sp, #5216]
     +0x154: str     q0, [sp, #5200]
     +0x158: str     q0, [sp, #5184]
     +0x15c: str     q0, [sp, #5168]
     +0x160: str     q0, [sp, #5152]
     +0x164: strb    w8, [sp]
     +0x168: bl      <mlkem512_poly_getnoise_eta1122_4x>
     +0x16c: add     x0, sp, #0x220
     +0x170: mov     x1, x20
     +0x174: mov     w2, #0x4
     +0x178: add     x27, sp, #0x220
     +0x17c: bl      <mlkem512_poly_getnoise_eta2>
     +0x180: add     x0, sp, #0x1, lsl #12
     +0x184: add     x0, x0, #0x420
     +0x188: bl      <mlkem512_polyvec_ntt>
     +0x18c: add     x1, sp, #0x1, lsl #12
     +0x190: add     x0, sp, #0x20
     +0x194: add     x1, x1, #0x420
     +0x198: add     x28, sp, #0x20
     +0x19c: bl      <mlkem512_polyvec_mulcache_compute>
     +0x1a0: add     x1, sp, #0x1, lsl #12
     +0x1a4: add     x2, sp, #0x1, lsl #12
     +0x1a8: add     x0, sp, #0x820
     +0x1ac: add     x1, x1, #0x820
     +0x1b0: add     x2, x2, #0x420
     +0x1b4: add     x3, sp, #0x20
     +0x1b8: add     x20, sp, #0x820
     +0x1bc: bl      <mlkem512_polyvec_basemul_acc_montgomery_cached>
     +0x1c0: add     x2, sp, #0x1, lsl #12
     +0x1c4: add     x0, x20, #0x200
     +0x1c8: add     x2, x2, #0x420
     +0x1cc: add     x3, sp, #0x20
     +0x1d0: mov     x1, x21
     +0x1d4: bl      <mlkem512_polyvec_basemul_acc_montgomery_cached>
     +0x1d8: add     x1, sp, #0x1, lsl #12
     +0x1dc: add     x2, sp, #0x1, lsl #12
     +0x1e0: add     x0, sp, #0x620
     +0x1e4: add     x1, x1, #0x20
     +0x1e8: add     x2, x2, #0x420
     +0x1ec: add     x3, sp, #0x20
     +0x1f0: add     x21, sp, #0x620
     +0x1f4: bl      <mlkem512_polyvec_basemul_acc_montgomery_cached>
     +0x1f8: add     x0, sp, #0x820
     +0x1fc: bl      <mlkem512_polyvec_invntt_tomont>
     +0x200: add     x0, sp, #0x620
     +0x204: bl      <mlkem_poly_invntt_tomont>
     +0x208: add     x0, sp, #0x820
     +0x20c: add     x1, sp, #0xc20
     +0x210: bl      <mlkem512_polyvec_add>
     +0x214: add     x0, sp, #0x620
     +0x218: add     x1, sp, #0x220
     +0x21c: bl      <mlkem_poly_add>
     +0x220: add     x0, sp, #0x620
     +0x224: add     x1, sp, #0x420
     +0x228: bl      <mlkem_poly_add>
     +0x22c: add     x0, sp, #0x820
     +0x230: bl      <mlkem512_polyvec_reduce>
     +0x234: add     x0, sp, #0x620
     +0x238: bl      <mlkem_poly_reduce>
     +0x23c: add     x1, sp, #0x820
     +0x240: mov     x0, x19
     +0x244: bl      <mlkem512_polyvec_compress_du>
     +0x248: add     x0, x19, #0x280
     +0x24c: add     x1, sp, #0x620
     +0x250: bl      <mlkem_poly_compress_d4>
     +0x254: movi    v0.2d, #0x0
     +0x258: add     x0, sp, #0x820
     +0x25c: mov     w1, wzr
     +0x260: mov     w2, #0x400
     +0x264: stp     q0, q0, [sp, #32]
     +0x268: stp     q0, q0, [sp, #64]
     +0x26c: stp     q0, q0, [sp, #96]
     +0x270: stp     q0, q0, [sp, #128]
     +0x274: stp     q0, q0, [sp, #160]
     +0x278: stp     q0, q0, [sp, #192]
     +0x27c: stp     q0, q0, [sp, #224]
     +0x280: stp     q0, q0, [sp, #256]
     +0x284: stp     q0, q0, [sp, #288]
     +0x288: stp     q0, q0, [sp, #320]
     +0x28c: stp     q0, q0, [sp, #352]
     +0x290: stp     q0, q0, [sp, #384]
     +0x294: stp     q0, q0, [sp, #416]
     +0x298: stp     q0, q0, [sp, #448]
     +0x29c: stp     q0, q0, [sp, #480]
     +0x2a0: stp     q0, q0, [sp, #512]
     +0x2a4: str     q0, [sp, #1040]
     +0x2a8: stp     q0, q0, [sp, #560]
     +0x2ac: stp     q0, q0, [sp, #592]
     +0x2b0: stp     q0, q0, [sp, #624]
     +0x2b4: stp     q0, q0, [sp, #656]
     +0x2b8: stp     q0, q0, [sp, #688]
     +0x2bc: stp     q0, q0, [sp, #720]
     +0x2c0: stp     q0, q0, [sp, #752]
     +0x2c4: stp     q0, q0, [sp, #784]
     +0x2c8: stp     q0, q0, [sp, #816]
     +0x2cc: stp     q0, q0, [sp, #848]
     +0x2d0: stp     q0, q0, [sp, #880]
     +0x2d4: stp     q0, q0, [sp, #912]
     +0x2d8: stp     q0, q0, [sp, #944]
     +0x2dc: stp     q0, q0, [sp, #976]
     +0x2e0: stp     q0, q0, [sp, #1008]
     +0x2e4: str     q0, [sp, #544]
     +0x2e8: str     q0, [sp, #1552]
     +0x2ec: str     q0, [sp, #1536]
     +0x2f0: str     q0, [sp, #1520]
     +0x2f4: str     q0, [sp, #1504]
     +0x2f8: str     q0, [sp, #1488]
     +0x2fc: str     q0, [sp, #1472]
     +0x300: str     q0, [sp, #1456]
     +0x304: str     q0, [sp, #1440]
     +0x308: str     q0, [sp, #1424]
     +0x30c: str     q0, [sp, #1408]
     +0x310: str     q0, [sp, #1392]
     +0x314: str     q0, [sp, #1376]
     +0x318: str     q0, [sp, #1360]
     +0x31c: str     q0, [sp, #1344]
     +0x320: str     q0, [sp, #1328]
     +0x324: str     q0, [sp, #1312]
     +0x328: str     q0, [sp, #1296]
     +0x32c: str     q0, [sp, #1280]
     +0x330: str     q0, [sp, #1264]
     +0x334: str     q0, [sp, #1248]
     +0x338: str     q0, [sp, #1232]
     +0x33c: str     q0, [sp, #1216]
     +0x340: str     q0, [sp, #1200]
     +0x344: str     q0, [sp, #1184]
     +0x348: str     q0, [sp, #1168]
     +0x34c: str     q0, [sp, #1152]
     +0x350: str     q0, [sp, #1136]
     +0x354: str     q0, [sp, #1120]
     +0x358: str     q0, [sp, #1104]
     +0x35c: str     q0, [sp, #1088]
     +0x360: str     q0, [sp, #1072]
     +0x364: str     q0, [sp, #1056]
     +0x368: str     q0, [sp, #2064]
     +0x36c: str     q0, [sp, #2048]
     +0x370: str     q0, [sp, #2032]
     +0x374: str     q0, [sp, #2016]
     +0x378: str     q0, [sp, #2000]
     +0x37c: str     q0, [sp, #1984]
     +0x380: str     q0, [sp, #1968]
     +0x384: str     q0, [sp, #1952]
     +0x388: str     q0, [sp, #1936]
     +0x38c: str     q0, [sp, #1920]
     +0x390: str     q0, [sp, #1904]
     +0x394: str     q0, [sp, #1888]
     +0x398: str     q0, [sp, #1872]
     +0x39c: str     q0, [sp, #1856]
     +0x3a0: str     q0, [sp, #1840]
     +0x3a4: str     q0, [sp, #1824]
     +0x3a8: str     q0, [sp, #1808]
     +0x3ac: str     q0, [sp, #1792]
     +0x3b0: str     q0, [sp, #1776]
     +0x3b4: str     q0, [sp, #1760]
     +0x3b8: str     q0, [sp, #1744]
     +0x3bc: str     q0, [sp, #1728]
     +0x3c0: str     q0, [sp, #1712]
     +0x3c4: str     q0, [sp, #1696]
     +0x3c8: str     q0, [sp, #1680]
     +0x3cc: str     q0, [sp, #1664]
     +0x3d0: str     q0, [sp, #1648]
     +0x3d4: str     q0, [sp, #1632]
     +0x3d8: str     q0, [sp, #1616]
     +0x3dc: str     q0, [sp, #1600]
     +0x3e0: str     q0, [sp, #1584]
     +0x3e4: str     q0, [sp, #1568]
     +0x3e8: bl      <memset@plt>
     +0x3ec: add     x0, sp, #0xc20
     +0x3f0: mov     w1, wzr
     +0x3f4: mov     w2, #0x400
     +0x3f8: bl      <memset@plt>
     +0x3fc: add     x0, sp, #0x1, lsl #12
     +0x400: add     x0, x0, #0x20
     +0x404: mov     w1, wzr
     +0x408: mov     w2, #0x400
     +0x40c: bl      <memset@plt>
     +0x410: add     x0, sp, #0x1, lsl #12
     +0x414: add     x0, x0, #0x420
     +0x418: mov     w1, wzr
     +0x41c: mov     w2, #0x400
     +0x420: bl      <memset@plt>
     +0x424: add     x0, sp, #0x1, lsl #12
     +0x428: add     x0, x0, #0x820
     +0x42c: mov     w1, wzr
     +0x430: mov     w2, #0x800
     +0x434: bl      <memset@plt>
     +0x438: movi    v0.2d, #0x0
     +0x43c: add     x8, sp, #0x2, lsl #12
     +0x440: add     x8, x8, #0x20
     +0x444: str     q0, [sp, #8240]
     +0x448: str     q0, [sp, #8224]
     +0x44c: adrp    x8, <page>
     +0x450: ldr     x8, [x8, #4088]  // got_stack_chk_guard
     +0x454: ldr     x9, [sp, #8280]
     +0x458: ldr     x8, [x8]
     +0x45c: cmp     x8, x9
     +0x460: b.ne    <mlkem512_indcpa_enc+0x488>
     +0x464: mov     w0, wzr
     +0x468: mov     sp, x29
     +0x46c: ldp     x20, x19, [sp, #80]
     +0x470: ldp     x22, x21, [sp, #64]
     +0x474: ldp     x24, x23, [sp, #48]
     +0x478: ldp     x26, x25, [sp, #32]
     +0x47c: ldp     x28, x27, [sp, #16]
     +0x480: ldp     x29, x30, [sp], #96
     +0x484: ret
     +0x488: bl      <__stack_chk_fail>
 ***)

let MLKEM_NATIVE_INDCPA_ENC_K2_CLANG17_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_clang17_O2_mc
   [layout_range "plt_memset"; layout_range "mlkem512_indcpa_enc"];;

let EN2_EXEC = MLKEM_NATIVE_INDCPA_ENC_K2_CLANG17_O2_EXEC;;

(* ------------------------------------------------------------------------- *)
(* The encryption in FIPS 203 in terms of the values computed by the code:   *)
(* the 12-bit fields of the encryption key as decoded (which may be >= q),   *)
(* the NTT of y and its multiplication cache, the noise e1 and e2, the       *)
(* decompressed message, the products with the transposed matrix and with t  *)
(* in Montgomery form, their inverse NTTs, and the results after adding the  *)
(* noise and the message and reducing, whose compressions are encoded in the *)
(* ciphertext.                                                               *)
(* ------------------------------------------------------------------------- *)

let KPKE_ENCRYPT_K2_RESULT_STMT =
  `!ek m r (TT:num->int16) (YH:num->int16) (MC:num->int16) (E1:num->int16)
    (E2:num->int16) (MU:num->int16) (U0:num->int16) (V0:num->int16)
    (U1:num->int16) (V1:num->int16) (U3:num->int16) (V4:num->int16).
     (!i j n. i < 2 /\ j < 2 /\ n < 256
              ==> mlkem_sample_ntt
                   (APPEND (mlkem_slice 768 32 ek) [word j; word i]) n
                  < &3329) /\
     (!i. i < 512
          ==> TT i = word((num_of_bytelist ek DIV 2 EXP (12 * i)) MOD
                          2 EXP 12)) /\
     (!j i. j < 2 /\ i < 256
            ==> (ival(YH(256 * j + i)) ==
                 mlkem_ntt (mlkem_cbd 3 (mlkem_prf 3 r (word j))) i)
                (mod &3329) /\
                abs(ival(YH(256 * j + i))) <= &23594) /\
     (!j p. j < 2 /\ p < 128
            ==> (ival(MC(128 * j + p)) ==
                 ival(YH(256 * j + 2 * p + 1)) *
                 &17 pow (2 * bitreverse7 p + 1)) (mod &3329)) /\
     (!j i. j < 2 /\ i < 256
            ==> (ival(E1(256 * j + i)) ==
                 coeff i (mlkem_cbd 2 (mlkem_prf 2 r (word(2 + j)))))
                (mod &3329) /\
                abs(ival(E1(256 * j + i))) <= &2) /\
     (!i. i < 256
          ==> (ival(E2 i) == coeff i (mlkem_cbd 2 (mlkem_prf 2 r (word 4))))
              (mod &3329) /\
              abs(ival(E2 i)) <= &2) /\
     (!i. i < 256
          ==> MU i = word((3329 * (num_of_bytelist m DIV 2 EXP i) MOD 2 + 1)
                          DIV 2)) /\
     (!q p. q < 2 /\ p < 128
            ==> (ival(U0(256 * q + 2 * p)) ==
                 &169 *
                 ((mlkem_sample_ntt (APPEND (mlkem_slice 768 32 ek)
                                       [word q; word 1]) (2 * p + 1) *
                   ival(MC(128 + p)) +
                   mlkem_sample_ntt (APPEND (mlkem_slice 768 32 ek)
                                       [word q; word 1]) (2 * p) *
                   ival(YH(256 + 2 * p))) +
                  (mlkem_sample_ntt (APPEND (mlkem_slice 768 32 ek)
                                       [word q; word 0]) (2 * p + 1) *
                   ival(MC p) +
                   mlkem_sample_ntt (APPEND (mlkem_slice 768 32 ek)
                                       [word q; word 0]) (2 * p) *
                   ival(YH(2 * p))))) (mod &3329) /\
                (ival(U0(256 * q + 2 * p + 1)) ==
                 &169 *
                 ((mlkem_sample_ntt (APPEND (mlkem_slice 768 32 ek)
                                       [word q; word 1]) (2 * p + 1) *
                   ival(YH(256 + 2 * p)) +
                   mlkem_sample_ntt (APPEND (mlkem_slice 768 32 ek)
                                       [word q; word 1]) (2 * p) *
                   ival(YH(256 + 2 * p + 1))) +
                  (mlkem_sample_ntt (APPEND (mlkem_slice 768 32 ek)
                                       [word q; word 0]) (2 * p + 1) *
                   ival(YH(2 * p)) +
                   mlkem_sample_ntt (APPEND (mlkem_slice 768 32 ek)
                                       [word q; word 0]) (2 * p) *
                   ival(YH(2 * p + 1))))) (mod &3329)) /\
     (!p. p < 128
          ==> (ival(V0(2 * p)) ==
               &169 *
               ((ival(TT(256 + 2 * p + 1)) * ival(MC(128 + p)) +
                 ival(TT(256 + 2 * p)) * ival(YH(256 + 2 * p))) +
                (ival(TT(2 * p + 1)) * ival(MC p) +
                 ival(TT(2 * p)) * ival(YH(2 * p))))) (mod &3329) /\
              (ival(V0(2 * p + 1)) ==
               &169 *
               ((ival(TT(256 + 2 * p + 1)) * ival(YH(256 + 2 * p)) +
                 ival(TT(256 + 2 * p)) * ival(YH(256 + 2 * p + 1))) +
                (ival(TT(2 * p + 1)) * ival(YH(2 * p)) +
                 ival(TT(2 * p)) * ival(YH(2 * p + 1))))) (mod &3329)) /\
     (!j i. j < 2 /\ i < 256
            ==> (ival(U1(256 * j + i)) ==
                 inverse_ntt (\n. ival(U0(256 * j + n))) i) (mod &3329) /\
                abs(ival(U1(256 * j + i))) <= &26624) /\
     (!i. i < 256
          ==> (ival(V1 i) == inverse_ntt (\n. ival(V0 n)) i) (mod &3329) /\
              abs(ival(V1 i)) <= &26624) /\
     (!i. i < 512 ==> ival(U3 i) = ival(word_add (U1 i) (E1 i)) rem &3329) /\
     (!i. i < 256
          ==> ival(V4 i) =
              ival(word_add (word_add (V1 i) (E2 i)) (MU i)) rem &3329)
     ==> nsum {i | i < 512}
              (\i. ((2048 * val(U3 i) + 3329) DIV 6658) MOD 1024 *
                   2 EXP (10 * i)) +
         2 EXP (8 * 640) *
         nsum {i | i < 256}
              (\i. ((32 * val(V4 i) + 3329) DIV 6658) MOD 16 * 2 EXP (4 * i)) =
         num_of_bytelist(kpke_encrypt mlkem512 ek m r)`;;

let KPKE_ENCRYPT_K2_RESULT = assume_spec KPKE_ENCRYPT_K2_RESULT_STMT;;

(* ------------------------------------------------------------------------- *)
(* The buffers are aligned to 32 bytes within the stack frame, so their      *)
(* addresses depend on whether the stack pointer is a multiple of 32 or just *)
(* of 16. The first 768 bytes of the encryption key are decoded by           *)
(* mlkem512_polyvec_frombytes and its last 32, rho, are copied as two        *)
(* 128-bit words to the four seeds for mlkem_poly_rej_uniform_x4. The        *)
(* message is decoded and decompressed by mlkem_poly_frommsg.                *)
(* ------------------------------------------------------------------------- *)

let EN2_BUFFER_ADDRESS_STMT =
  `!sp:int64.
        aligned 16 sp
        ==> word_and (word_add sp (word 3408)) (word 18446744073709551584) =
            word_add sp (word(if aligned 32 sp then 3392 else 3408))`;;

let EN2_BUFFER_ADDRESS = assume_spec EN2_BUFFER_ADDRESS_STMT;;

let EN2_BUFFER_TAC =
  FIRST_ASSUM(fun th ->
    if concl th = `aligned 32 (stackpointer:int64)` ||
       concl th = `~aligned 32 (stackpointer:int64)`
    then SUBST_ALL_TAC
          (REWRITE_RULE[th; ASSUME `aligned 16 (stackpointer:int64)`]
            (SPEC `stackpointer:int64` EN2_BUFFER_ADDRESS))
    else NO_TAC);;

let EN2_PK_TAC =
  FIRST_ASSUM(fun th ->
    if can (term_match []
         `read (memory :> bytes(pk,800)) s = num_of_bytelist ek`) (concl th)
    then
      ASSUME_TAC(REWRITE_RULE[GSYM READ_COMPONENT_COMPOSE]
       (REWRITE_RULE[READ_COMPONENT_COMPOSE; READ_BYTES_MOD;
                     ARITH_RULE `MIN 800 768 = 768`]
        (AP_THM(AP_TERM `(MOD):num->num->num`
                 (REWRITE_RULE[READ_COMPONENT_COMPOSE] th))
           `2 EXP (8 * 768)`))) THEN
      MP_TAC(SPECL [`pk:int64`; `ek:byte list`; `768`; `32`;
                    rand(lhand(concl th))] READ_MEMORY_BYTES_SLICE) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN ARITH_TAC;
        ASM_REWRITE_TAC[] THEN
        DISCH_THEN(fun th -> ASSUME_TAC th THEN
          STRIP_ASSUME_TAC(CONV_RULE(ONCE_DEPTH_CONV
             NORMALIZE_RELATIVE_ADDRESS_CONV THENC
             ONCE_DEPTH_CONV NUM_ADD_CONV)
           (MATCH_MP GENMAT_BYTES128_HALVES th)))]
    else NO_TAC);;

let EN2_TT_TAC b s =
  INDCPA_GHOST_TAC "TT" (b + 4128) 512 s THEN
  SUBGOAL_THEN
   `!i. i < 512
        ==> (TT:num->int16) i =
            word((num_of_bytelist ek DIV 2 EXP (12 * i)) MOD 2 EXP 12)`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN INDCPA_UNGHOST_TAC "TT" THEN
    FIRST_ASSUM(MP_TAC o SPEC `i:num` o check (fun th ->
      mem (mk_var(s,`:armstate`)) (frees(concl th)) &&
      INDCPA_HAS_CONST "MOD" (concl th) && is_forall(concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    CONV_TAC(ONCE_DEPTH_CONV INDCPA_CANON_CONV) THEN
    DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC DIV_MOD_EXP_LOW THEN UNDISCH_TAC `i < 512` THEN ARITH_TAC;
    ALL_TAC];;

let EN2_MU_TAC b s =
  INDCPA_GHOST_TAC "MU" (b + 1056) 256 s THEN
  SUBGOAL_THEN
   `!i. i < 256
        ==> (MU:num->int16) i =
            word((3329 * (num_of_bytelist msg DIV 2 EXP i) MOD 2 + 1) DIV 2)`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN INDCPA_UNGHOST_TAC "MU" THEN
    FIRST_ASSUM(MP_TAC o SPEC `i:num` o check (fun th ->
      mem (mk_var(s,`:armstate`)) (frees(concl th)) &&
      can (find_term (fun t -> t = `3329`)) (concl th) &&
      is_forall(concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    CONV_TAC(ONCE_DEPTH_CONV INDCPA_CANON_CONV) THEN SIMP_TAC[];
    ALL_TAC];;

(* ------------------------------------------------------------------------- *)
(* The callees. The matrix is generated with transposition: the four seeds   *)
(* are rho followed by the indices (0,0), (0,1), (1,0) and (1,1), and        *)
(* mlkem_poly_rej_uniform_x4 samples the four entries. The noise y and e1 is *)
(* sampled by one call of mlkem512_poly_getnoise_eta1122_4x (its fourth      *)
(* nonce is at the bottom of the stack), and e2 by                           *)
(* mlkem512_poly_getnoise_eta2. The theorems with hypotheses of the form ALL *)
(* P l are used with them as conjunctions.                                   *)
(* ------------------------------------------------------------------------- *)

let LOCAL_POLYVEC_FROMBYTES_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_clang17_O2_mc,EN2_EXEC,
    0x0,mlkem_native_libmlkem_clang17_O2_mc,
    MLKEM_NATIVE_POLYVEC_FROMBYTES_K2_CLANG17_O2_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_POLY_FROMMSG_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_clang17_O2_mc,EN2_EXEC,
    0x0,mlkem_native_libmlkem_clang17_O2_mc,
    MLKEM_NATIVE_POLY_FROMMSG_CLANG17_O2_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_REJ_UNIFORM_X4_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_clang17_O2_mc,EN2_EXEC,
    0x0,mlkem_native_libmlkem_clang17_O2_mc,
    REWRITE_RULE[ALL]
     MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_CLANG17_O2_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_GETNOISE_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_clang17_O2_mc,EN2_EXEC,
    0x0,mlkem_native_libmlkem_clang17_O2_mc,
    MLKEM_NATIVE_POLY_GETNOISE_ETA1122_4X_K2_CLANG17_O2_IMAGE_SUBROUTINE_CORRECT
   );;

let LOCAL_GETNOISE_ETA2_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_clang17_O2_mc,EN2_EXEC,
    0x0,mlkem_native_libmlkem_clang17_O2_mc,
    MLKEM_NATIVE_POLY_GETNOISE_ETA2_K2_CLANG17_O2_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_POLYVEC_NTT_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_clang17_O2_mc,EN2_EXEC,
    0x0,mlkem_native_libmlkem_clang17_O2_mc,
    MLKEM_NATIVE_POLYVEC_NTT_K2_CLANG17_O2_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_POLYVEC_MULCACHE_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_clang17_O2_mc,EN2_EXEC,
    0x0,mlkem_native_libmlkem_clang17_O2_mc,
    MLKEM_NATIVE_POLYVEC_MULCACHE_COMPUTE_K2_CLANG17_O2_IMAGE_SUBROUTINE_CORRECT
   );;

let LOCAL_BASEMUL_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_clang17_O2_mc,EN2_EXEC,
    0x0,mlkem_native_libmlkem_clang17_O2_mc,
    REWRITE_RULE[ALL]
      MLKEM_NATIVE_BASEMUL_K2_CLANG17_O2_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_POLYVEC_INVNTT_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_clang17_O2_mc,EN2_EXEC,
    0x0,mlkem_native_libmlkem_clang17_O2_mc,
    MLKEM_NATIVE_POLYVEC_INVNTT_TOMONT_K2_CLANG17_O2_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_POLY_INVNTT_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_clang17_O2_mc,EN2_EXEC,
    0x0,mlkem_native_libmlkem_clang17_O2_mc,
    REWRITE_RULE[ALL]
      MLKEM_NATIVE_POLY_INVNTT_TOMONT_CLANG17_O2_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_POLYVEC_ADD_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_clang17_O2_mc,EN2_EXEC,
    0x0,mlkem_native_libmlkem_clang17_O2_mc,
    MLKEM_NATIVE_POLYVEC_ADD_K2_CLANG17_O2_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_POLY_ADD_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_clang17_O2_mc,EN2_EXEC,
    0x0,mlkem_native_libmlkem_clang17_O2_mc,
    REWRITE_RULE[ALL]
      MLKEM_NATIVE_POLY_ADD_CLANG17_O2_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_POLYVEC_REDUCE_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_clang17_O2_mc,EN2_EXEC,
    0x0,mlkem_native_libmlkem_clang17_O2_mc,
    MLKEM_NATIVE_POLYVEC_REDUCE_K2_CLANG17_O2_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_POLY_REDUCE_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_clang17_O2_mc,EN2_EXEC,
    0x0,mlkem_native_libmlkem_clang17_O2_mc,
    MLKEM_NATIVE_POLY_REDUCE_CLANG17_O2_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_POLYVEC_COMPRESS_DU_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_clang17_O2_mc,EN2_EXEC,
    0x0,mlkem_native_libmlkem_clang17_O2_mc,
    MLKEM_NATIVE_POLYVEC_COMPRESS_DU_K2_CLANG17_O2_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_POLY_COMPRESS_D4_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_clang17_O2_mc,EN2_EXEC,
    0x0,mlkem_native_libmlkem_clang17_O2_mc,
    MLKEM_NATIVE_POLY_COMPRESS_D4_CLANG17_O2_IMAGE_SUBROUTINE_CORRECT);;

(* ------------------------------------------------------------------------- *)
(* The facts about the stages of the computation other than those given by   *)
(* the tactics in mlkem_native_indcpa.ml: the coefficients of the transposed *)
(* matrix as given by SampleNTT, the bounds on the inputs of the             *)
(* multiplications, the products with the rows of the transposed matrix and  *)
(* with t, and the bounds on the inputs of the compressions.                 *)
(* ------------------------------------------------------------------------- *)

let EN2_WORDLISTS_TAC b s =
  let addr = Printf.sprintf
    "word_add stackpointer (word (%d + 512 * (2 * i + j))):int64" b in
  SUBGOAL_THEN
   (parse_term(Printf.sprintf
     "!i j. i < 2 /\\ j < 2
            ==> wordlist_from_memory(%s,256) (%s:armstate) =
                SUB_LIST(0,256)
                 (FILTER (\\x. val x < 3329)
                   (MAP (word_zx:12 word->16 word)
                     (wordlist_of_num (336 + 112 * k)
                       (num_of_bytelist
                         (list_of_seq
                           (shake128 (APPEND (rho:byte list)
                                             [word i; word j]))
                           (504 + 168 * k))))))" addr s))
  ASSUME_TAC THENL [GENMAT_FINAL_TAC; ALL_TAC];;

let EN2_MATRIX_TAC b sname =
  let s = mk_var(sname,`:armstate`) in
  let addr = parse_term(Printf.sprintf
    "word_add stackpointer (word (%d + 512 * (2 * q + j))):int64" b) in
  EN2_WORDLISTS_TAC b sname THEN
  SUBGOAL_THEN
   `!q j n. q < 2 /\ j < 2 /\ n < 256
            ==> &0 <= mlkem_sample_ntt (APPEND rho [word q; word j]) n /\
                mlkem_sample_ntt (APPEND rho [word q; word j]) n < &3329`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    MATCH_MP_TAC MLKEM_SAMPLE_NTT_REJ_BOUND THEN
    EXISTS_TAC `k:num` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!q j n. q < 2 /\ j < 2 /\ n < 256
            ==> ival((AM:num->int16)(512 * q + 256 * j + n)) =
                mlkem_sample_ntt (APPEND rho [word q; word j]) n`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    INDCPA_GHOST_SPEC_TAC "AM" `512 * q + 256 * j + n` THEN
    MP_TAC(SPECL [addr; s; `APPEND (rho:byte list) [word q; word j]`;
                  `k:num`; `n:num`] MLKEM_NATIVE_SAMPLE_COEFF) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
    AP_TERM_TAC THEN REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    MATCH_MP_TAC READ16_OFFSET_EQ THEN ARITH_TAC;
    ALL_TAC];;

let EN2_AM_INST r j =
  let th = SPECL [mk_small_numeral r; mk_small_numeral j]
    (ASSUME `!q j n. q < 2 /\ j < 2 /\ n < 256
                     ==> ival((AM:num->int16)(512 * q + 256 * j + n)) =
                         mlkem_sample_ntt (APPEND rho [word q; word j]) n`) in
  CONV_RULE(NUM_REDUCE_CONV THENC REWRITE_CONV[ADD_CLAUSES; ADD_ASSOC] THENC
            NUM_REDUCE_CONV) th;;

let EN2_AM_BOUND_TAC =
  SUBGOAL_THEN `!m. m < 1024 ==> abs(ival((AM:num->int16) m)) <= &2 pow 12`
  (LABEL_TAC "ambound") THENL
   [X_GEN_TAC `m':num` THEN DISCH_TAC THEN
    MP_TAC(SPECL [`512`; `2`; `m':num`] EXISTS_DIV_MOD_LT) THEN
    ASM_REWRITE_TAC[ARITH_RULE `512 * 2 = 1024`; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`q:num`; `x:num`] THEN STRIP_TAC THEN
    MP_TAC(SPECL [`256`; `2`; `x:num`] EXISTS_DIV_MOD_LT) THEN
    ASM_REWRITE_TAC[ARITH_RULE `256 * 2 = 512`; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`j:num`; `n:num`] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC(INT_ARITH
     `&0 <= x /\ x < &3329 ==> abs(x:int) <= &2 pow 12`) THEN
    ASM_SIMP_TAC[];
    ALL_TAC];;

let EN2_BASEMUL_DEFS =
  [basemul2_even; basemul2_odd; pmul_acc2; pmull_acc2; pmull];;

let EN2_U0_GOAL = `!q p. q < 2 /\ p < 128
       ==> (ival((U0:num->int16)(256 * q + 2 * p)) ==
            &169 *
            ((mlkem_sample_ntt (APPEND rho [word q; word 1]) (2 * p + 1) *
              ival((MC:num->int16)(128 + p)) +
              mlkem_sample_ntt (APPEND rho [word q; word 1]) (2 * p) *
              ival((YH:num->int16)(256 + 2 * p))) +
             (mlkem_sample_ntt (APPEND rho [word q; word 0]) (2 * p + 1) *
              ival(MC p) +
              mlkem_sample_ntt (APPEND rho [word q; word 0]) (2 * p) *
              ival(YH(2 * p))))) (mod &3329) /\
           (ival(U0(256 * q + 2 * p + 1)) ==
            &169 *
            ((mlkem_sample_ntt (APPEND rho [word q; word 1]) (2 * p + 1) *
              ival(YH(256 + 2 * p)) +
              mlkem_sample_ntt (APPEND rho [word q; word 1]) (2 * p) *
              ival(YH(256 + 2 * p + 1))) +
             (mlkem_sample_ntt (APPEND rho [word q; word 0]) (2 * p + 1) *
              ival(YH(2 * p)) +
              mlkem_sample_ntt (APPEND rho [word q; word 0]) (2 * p) *
              ival(YH(2 * p + 1))))) (mod &3329)`;;

let EN2_U0_TAC b s =
  INDCPA_GHOST_TAC "U0" (b + 2080) 512 s THEN
  SUBGOAL_THEN EN2_U0_GOAL ASSUME_TAC THENL
   [REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
    CONV_TAC EXPAND_CASES_CONV THEN REPEAT CONJ_TAC THENL
     (map (fun q -> INDCPA_BASEMULK_ROW_TAC 2 "U0" (b + 2080 + 512 * q)
                     "ambound" (map (EN2_AM_INST q) [0;1])
                     EN2_BASEMUL_DEFS) [0;1]);
    ALL_TAC];;

let EN2_TT_BOUND_TAC =
  SUBGOAL_THEN `!m. m < 512 ==> abs(ival((TT:num->int16) m)) <= &2 pow 12`
  (LABEL_TAC "ttbound") THENL
   [X_GEN_TAC `m':num` THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN
    SUBGOAL_THEN `(num_of_bytelist ek DIV 2 EXP (12 * m')) MOD 2 EXP 12 < 4096`
    MP_TAC THENL [REWRITE_TAC[ARITH_RULE `4096 = 2 EXP 12`; MOD_LT_EQ] THEN
                  CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
    SPEC_TAC(`(num_of_bytelist ek DIV 2 EXP (12 * m')) MOD 2 EXP 12`,
             `f:num`) THEN
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `ival(word f:int16) = &f` SUBST1_TAC THENL
     [MATCH_MP_TAC IVAL_WORD_SMALL THEN UNDISCH_TAC `f < 4096` THEN ARITH_TAC;
      REWRITE_TAC[INT_ABS_NUM; INT_OF_NUM_POW; INT_OF_NUM_LE] THEN
      UNDISCH_TAC `f < 4096` THEN ARITH_TAC];
    ALL_TAC];;

let EN2_V0_GOAL = `!p. p < 128
       ==> (ival((V0:num->int16)(2 * p)) ==
            &169 *
            ((ival((TT:num->int16)(256 + 2 * p + 1)) *
              ival((MC:num->int16)(128 + p)) +
              ival(TT(256 + 2 * p)) * ival((YH:num->int16)(256 + 2 * p))) +
             (ival(TT(2 * p + 1)) * ival(MC p) +
              ival(TT(2 * p)) * ival(YH(2 * p))))) (mod &3329) /\
           (ival(V0(2 * p + 1)) ==
            &169 *
            ((ival(TT(256 + 2 * p + 1)) * ival(YH(256 + 2 * p)) +
              ival(TT(256 + 2 * p)) * ival(YH(256 + 2 * p + 1))) +
             (ival(TT(2 * p + 1)) * ival(YH(2 * p)) +
              ival(TT(2 * p)) * ival(YH(2 * p + 1))))) (mod &3329)`;;

let EN2_V0_TAC b s =
  INDCPA_GHOST_TAC "V0" (b + 1568) 256 s THEN
  SUBGOAL_THEN EN2_V0_GOAL ASSUME_TAC THENL
   [INDCPA_BASEMULK_ROW_TAC 2 "V0" (b + 1568) "ttbound" [] EN2_BASEMUL_DEFS;
    ALL_TAC];;

let EN2_COMPRESS_POST_TAC v y =
  let vt = mk_var(v,`:num->int16`) in
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    is_imp(concl th) && mem vt (frees(concl th)) &&
    INDCPA_HAS_CONST "nsum" (concl th))) THEN
  ANTS_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC VAL_LT_OF_IVAL_REM THEN EXISTS_TAC y THEN ASM_SIMP_TAC[];
    DISCH_TAC];;

let EN2_FINAL_TAC =
  REWRITE_TAC[ARITH_RULE `768 = 640 + 128`; READ_COMPONENT_COMPOSE;
              READ_BYTES_COMBINE] THEN
  REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`ek:byte list`; `msg:byte list`; `r:byte list`;
                `TT:num->int16`; `YH:num->int16`; `MC:num->int16`;
                `E1:num->int16`; `E2:num->int16`; `MU:num->int16`;
                `U0:num->int16`; `V0:num->int16`; `U1:num->int16`;
                `V1:num->int16`; `U3:num->int16`; `V4:num->int16`]
          (REWRITE_RULE[ASSUME `mlkem_slice 768 32 ek = rho`]
            KPKE_ENCRYPT_K2_RESULT)) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN
    FIRST [ASM_REWRITE_TAC[] THEN NO_TAC;
           REPEAT STRIP_TAC THEN ASM_SIMP_TAC[]];
    SIMP_TAC[]];;

(* ------------------------------------------------------------------------- *)
(* Correctness proof, assuming the contracts for memset and memcpy (the      *)
(* latter for the callees). The encryption key ek of 800 bytes is at pk, the *)
(* message msg of 32 bytes at m and the randomness r of 32 bytes at coins,   *)
(* and the ciphertext of 768 bytes written at c is that of kpke_encrypt      *)
(* mlkem512 ek msg r in common/fips203/fips203.ml, for any ek (FIPS 203      *)
(* decodes t modulo q, while the code multiplies by the 12-bit fields, which *)
(* are congruent). The theorem assumes that SampleNTT terminates for each    *)
(* entry of the matrix, as for mlkem512_gen_matrix. The stack is the 8400    *)
(* bytes of the function (96 saved, 8288 for the buffers, 16 for alignment)  *)
(* and the 3392 used by mlkem_poly_rej_uniform_x4 below them. The proof is   *)
(* by cases on whether the stack pointer is a multiple of 32, which gives    *)
(* the address b of the buffers, at offsets 32 (the multiplication cache of  *)
(* y), 544 (e2), 1056 (the message), 1568 (v), 2080 (u), 3104 (e1), 4128     *)
(* (t), 5152 (y), 6176 (the matrix) and 8224 (rho, and the seeds above y).   *)
(* ------------------------------------------------------------------------- *)

let EN2_INTRO_TAC =
  MAP_EVERY X_GEN_TAC
   [`c:int64`; `m:int64`; `pk:int64`; `coins:int64`; `ek:byte list`;
    `msg:byte list`; `r:byte list`; `guard:int64`; `mf:int64`; `mc:int64`;
    `ea:int64`; `el:num`; `ev:num`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 11792 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE] THEN
  REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NONOVERLAPPING_CLAUSES]) THEN
  SUBGOAL_THEN `aligned 16 (stackpointer:int64)` ASSUME_TAC THENL
   [UNDISCH_TAC `aligned 16 (word_add stackpointer (word 11792):int64)` THEN
    CONV_TAC(LAND_CONV NORMALIZE_ALIGNED_WORD_CONV) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_stack_chk_guard:num`] WORD_ADD;
              SPECL [`pc:num`; `got_memset:num`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`;
                                     `got_stack_chk_guard:num`] WORD_ADD;
                              SPECL [`pc:num`;
                                     `got_memset:num`] WORD_ADD]) THEN
  GHOST_INTRO_TAC `canary:int64` `read (memory :> bytes64 guard)` THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  MAP_EVERY (fun n ->
    ENSURES_PRESERVED_TAC ("x"^string_of_int n^"_init")
     (parse_term("X"^string_of_int n))) (19--29) THEN
  UNDISCH_TAC
   `!i j. i < 2 /\ j < 2
          ==> mlkem_samplentt_terminates
               (APPEND (mlkem_slice 768 32 ek) [word j; word i])` THEN
  ABBREV_TAC `rho = mlkem_slice 768 32 ek` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`2`; `\i j. APPEND (rho:byte list) [word j; word (i:num)]`]
                MLKEM_SAMPLENTT_TERMINATES_UNIFORM) THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `k:num`) THEN
  SUBGOAL_THEN
   `!i j. i < 2 /\ j < 2
          ==> 256 <= LENGTH(FILTER (\x. val x < 3329)
                      (MAP (word_zx:12 word->16 word)
                        (wordlist_of_num (336 + 112 * k)
                          (num_of_bytelist
                            (list_of_seq
                              (shake128 (APPEND rho [word i; word j]))
                              (504 + 168 * k))))))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL [`j:num`; `i:num`]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH(rho:byte list) = 32` ASSUME_TAC THENL
   [EXPAND_TAC "rho" THEN REWRITE_TAC[mlkem_slice; LENGTH_LIST_OF_SEQ];
    ALL_TAC];;

let EN2_SEED_INP_TAC off x y s =
  GENMAT_INPUT_TAC off x y (mk_var(s,`:armstate`));;

(*** Instance (i,j) of the hypothesis on the samples of SHAKE128 ***)

let EN2_HYP_TAC i j =
  W(fun (asl,_) ->
    let hth = find (fun th ->
      match concl th with
        Comb(Const("!",_),Abs(Var("i",_),
          Comb(Const("!",_),Abs(Var("j",_),b)))) ->
            (try let _,r = dest_imp b in
                 fst(strip_comb r) = `(<=):num->num->bool` &&
                 can (find_term (fun t -> t = `[word i:byte; word j]`)) r
             with Failure _ -> false)
      | _ -> false) (map snd asl) in
    let th1 = SPECL [mk_small_numeral i; mk_small_numeral j] hth in
    ASSUME_TAC(MP th1 (EQT_ELIM(NUM_REDUCE_CONV(lhand(concl th1))))));;

let EN2_CASE_TAC b =
  ENSURES_INIT_TAC "s0" THEN
  EN2_PK_TAC THEN
  ARM_STEPS_TAC EN2_EXEC (1--10) THEN
  EN2_BUFFER_TAC THEN
  ARM_STEPS_TAC EN2_EXEC (11--11) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC EN2_EXEC (12--24) THEN
  LOCAL_POLYVEC_FROMBYTES_TAC
   [`read X0 s`; `read X1 s`; `num_of_bytelist ek MOD 2 EXP (8 * 768)`;
    `pc:num`; `read SP s`; `read X30 s`] 25 THEN
  EN2_TT_TAC b "s25" THEN
  ARM_STEPS_TAC EN2_EXEC (26--32) THEN
  LOCAL_POLY_FROMMSG_TAC
   [`read X0 s`; `read X1 s`; `num_of_bytelist msg`; `pc:num`;
    `read X30 s`] 33 THEN
  EN2_MU_TAC b "s33" THEN
  ARM_STEPS_TAC EN2_EXEC (34--62) THEN
  INDCPA_GOT_TAC THEN
  EN2_SEED_INP_TAC (b + 5152) 0 0 "s62" THEN
  EN2_SEED_INP_TAC (b + 5216) 0 1 "s62" THEN
  EN2_SEED_INP_TAC (b + 5280) 1 0 "s62" THEN
  EN2_SEED_INP_TAC (b + 5344) 1 1 "s62" THEN
  ARM_STEPS_TAC EN2_EXEC [63] THEN
  EN2_HYP_TAC 0 0 THEN
  EN2_HYP_TAC 0 1 THEN
  EN2_HYP_TAC 1 0 THEN
  EN2_HYP_TAC 1 1 THEN
  LOCAL_REJ_UNIFORM_X4_TAC
   ([`read X0 s`; `read X1 s`; `read X2 s`; `read X3 s`; `read X4 s`] @
    [`APPEND (rho:byte list) [word 0; word 0]`; `APPEND (rho:byte list) [word 0; word 1]`; `APPEND (rho:byte list) [word 1; word 0]`; `APPEND (rho:byte list) [word 1; word 1]`] @
    [`k:num`; `guard:int64`; `mf:int64`; `ea:int64`; `el:num`; `ev:num`;
     `pc:num`; `read SP s`; `read X30 s`]) 64 THEN
  GENMAT_TOBYTES_TAC THEN
  INDCPA_GHOST_TAC "AM" (b + 6176) 1024 "s64" THEN
  EN2_MATRIX_TAC (b + 6176) "s64" THEN
  ARM_STEPS_TAC EN2_EXEC (65--93) THEN
  INDCPA_NONCE_TAC 3 THEN
  ARM_STEPS_TAC EN2_EXEC [94] THEN
  LOCAL_GETNOISE_TAC
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X3 s`; `read X4 s`;
    `r:byte list`; `read X5 s`; `read X6 s`; `read X7 s`;
    `word 3:int64`; `guard:int64`; `mf:int64`; `mc:int64`; `ea:int64`;
    `el:num`; `ev:num`; `pc:num`; `read SP s`; `read X30 s`] 95 THEN
  INDCPA_NOISE_ETA_TAC 3 "YS" (b + 5152) 2 "r" "word j" "s95" THEN
  INDCPA_NOISE_ETA_TAC 2 "E1" (b + 3104) 2 "r" "word(2 + j)" "s95" THEN
  INDCPA_DISCARD_LETS_TAC THEN
  ARM_STEPS_TAC EN2_EXEC (96--99) THEN
  INDCPA_GOT_TAC THEN
  ARM_STEPS_TAC EN2_EXEC [100] THEN
  LOCAL_GETNOISE_ETA2_TAC
   [`read X0 s`; `read X1 s`; `r:byte list`; `read X2 s`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 101 THEN
  INDCPA_NOISE1_TAC "E2" (b + 544) "r" "word 4" "s101" THEN
  INDCPA_DISCARD_LETS_TAC THEN
  ARM_STEPS_TAC EN2_EXEC (102--104) THEN
  LOCAL_POLYVEC_NTT_TAC
   [`read X0 s`; `YS:num->int16`; `pc:num`; `read SP s`; `read X30 s`] 105 THEN
  INDCPA_NTT_ETA_TAC 3 "YH" (b + 5152) 2 "YS" "r" "word j" "s105" THEN
  ARM_STEPS_TAC EN2_EXEC (106--110) THEN
  LOCAL_POLYVEC_MULCACHE_TAC
   [`read X0 s`; `read X1 s`; `YH:num->int16`; `pc:num`; `read SP s`;
    `read X30 s`] 111 THEN
  INDCPA_MULCACHE_TAC "MC" (b + 32) 2 "YH" "s111" THEN
  ARM_STEPS_TAC EN2_EXEC (112--119) THEN
  INDCPA_BASEMULK_PRE_TAC 2 (b + 6176,"AM",0) (b + 5152,"YH") (b + 32,"MC") "s119" THEN
  LOCAL_BASEMUL_TAC (INDCPA_BASEMULK_ARGS 2 ("AM",256 * 2 * 0) "YH" "MC") 120 THEN
  INDCPA_BASEMULK_DROP_PRE_TAC 2 (b + 6176,"AM",0) (b + 5152,"YH") (b + 32,"MC") THEN
  ARM_STEPS_TAC EN2_EXEC (121--126) THEN
  INDCPA_BASEMULK_PRE_TAC 2 (b + 7200,"AM",512) (b + 5152,"YH") (b + 32,"MC") "s126" THEN
  LOCAL_BASEMUL_TAC (INDCPA_BASEMULK_ARGS 2 ("AM",256 * 2 * 1) "YH" "MC") 127 THEN
  INDCPA_BASEMULK_DROP_PRE_TAC 2 (b + 7200,"AM",512) (b + 5152,"YH") (b + 32,"MC") THEN
  EN2_AM_BOUND_TAC THEN
  EN2_U0_TAC b "s127" THEN
  ARM_STEPS_TAC EN2_EXEC (128--135) THEN
  INDCPA_BASEMULK_PRE_TAC 2 (b + 4128,"TT",0) (b + 5152,"YH") (b + 32,"MC") "s135" THEN
  LOCAL_BASEMUL_TAC (INDCPA_BASEMULK_ARGS 2 ("TT",0) "YH" "MC") 136 THEN
  INDCPA_BASEMULK_DROP_PRE_TAC 2 (b + 4128,"TT",0) (b + 5152,"YH") (b + 32,"MC") THEN
  EN2_TT_BOUND_TAC THEN
  EN2_V0_TAC b "s136" THEN
  ARM_STEPS_TAC EN2_EXEC (137--138) THEN
  LOCAL_POLYVEC_INVNTT_TAC
   [`read X0 s`; `U0:num->int16`; `pc:num`; `read SP s`; `read X30 s`] 139 THEN
  INDCPA_INVNTT_TAC "U1" (b + 2080) 2 "U0" "s139" THEN
  ARM_STEPS_TAC EN2_EXEC (140--141) THEN
  LOCAL_POLY_INVNTT_TAC
   [`read X0 s`; `V0:num->int16`; `pc:num`; `read SP s`; `read X30 s`] 142 THEN
  INDCPA_INVNTT1_TAC "V1" (b + 1568) "V0" "s142" THEN
  ARM_STEPS_TAC EN2_EXEC (143--145) THEN
  LOCAL_POLYVEC_ADD_TAC
   [`read X0 s`; `read X1 s`; `U1:num->int16`; `E1:num->int16`; `pc:num`;
    `read SP s`; `read X30 s`] 146 THEN
  ARM_STEPS_TAC EN2_EXEC (147--149) THEN
  LOCAL_POLY_ADD_TAC
   [`read X0 s`; `read X1 s`; `V1:num->int16`; `E2:num->int16`; `pc:num`;
    `read X30 s`] 150 THEN
  ARM_STEPS_TAC EN2_EXEC (151--153) THEN
  LOCAL_POLY_ADD_TAC
   [`read X0 s`; `read X1 s`;
    `\i. word_add ((V1:num->int16) i) ((E2:num->int16) i)`;
    `MU:num->int16`; `pc:num`; `read X30 s`] 154 THEN
  ARM_STEPS_TAC EN2_EXEC (155--156) THEN
  LOCAL_POLYVEC_REDUCE_TAC
   [`read X0 s`; `\i. word_add ((U1:num->int16) i) ((E1:num->int16) i)`;
    `pc:num`; `read SP s`; `read X30 s`] 157 THEN
  INDCPA_REDUCE_TAC "U3" (b + 2080) 512
    "word_add ((U1:num->int16) i) ((E1:num->int16) i)" "s157" THEN
  ARM_STEPS_TAC EN2_EXEC (158--159) THEN
  LOCAL_POLY_REDUCE_TAC
   [`read X0 s`;
    `\i. word_add (word_add ((V1:num->int16) i) ((E2:num->int16) i))
                  ((MU:num->int16) i)`;
    `pc:num`; `read X30 s`] 160 THEN
  INDCPA_REDUCE_TAC "V4" (b + 1568) 256
    "word_add (word_add ((V1:num->int16) i) ((E2:num->int16) i)) \
     ((MU:num->int16) i)" "s160" THEN
  ARM_STEPS_TAC EN2_EXEC (161--162) THEN
  INDCPA_GOT_TAC THEN
  ARM_STEPS_TAC EN2_EXEC [163] THEN
  LOCAL_POLYVEC_COMPRESS_DU_TAC
   [`read X0 s`; `read X1 s`; `U3:num->int16`; `guard:int64`; `pc:num`;
    `read SP s`; `read X30 s`] 164 THEN
  EN2_COMPRESS_POST_TAC "U3"
   `ival(word_add ((U1:num->int16) i) ((E1:num->int16) i))` THEN
  ARM_STEPS_TAC EN2_EXEC (165--167) THEN
  LOCAL_POLY_COMPRESS_D4_TAC
   [`read X0 s`; `read X1 s`; `V4:num->int16`; `pc:num`;
    `read SP s`; `read X30 s`] 168 THEN
  EN2_COMPRESS_POST_TAC "V4"
   `ival(word_add (word_add ((V1:num->int16) i) ((E2:num->int16) i))
                  ((MU:num->int16) i))` THEN
  INDCPA_MEMSET_LABEL_TAC THEN
  INDCPA_MEMSETS_TAC EN2_EXEC
   [169,270; 276,279; 285,289; 295,299; 305,309] THEN
  ARM_STEPS_TAC EN2_EXEC (315--320) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC EN2_EXEC (321--334) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN EN2_FINAL_TAC;;

let MLKEM_NATIVE_INDCPA_ENC_K2_CLANG17_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!c m pk coins (ek:byte list) (msg:byte list) (r:byte list)
    guard mf mc ea el ev pc stackpointer returnaddress.
        memset_contract mf ea el ev /\ memcpy_contract mc ea el ev /\
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        LENGTH ek = 800 /\ LENGTH msg = 32 /\ LENGTH r = 32 /\
        (!i j. i < 2 /\ j < 2
               ==> mlkem_samplentt_terminates
                    (APPEND (mlkem_slice 768 32 ek) [word j; word i])) /\
        nonoverlapping (c,768) (word_sub stackpointer (word 11792),11792) /\
        nonoverlapping (pk,800) (word pc,libmlkem_size) /\
        ALLPAIRS nonoverlapping
         [(c,768); (word_sub stackpointer (word 11792),11792)]
         [(m,32); (pk,800); (coins,32); (word pc,libmlkem_size);
          (word(pc + got_stack_chk_guard),8); (guard,8);
          (word(pc + got_memset),8);
          (word(pc + got_memcpy),8); (ea,el)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_clang17_O2_mc /\
                  read PC s = word (pc + mlkem512_indcpa_enc) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [c; m; pk; coins] s /\
                  read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                    guard /\
                  read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                  read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                  read (memory :> bytes(ea,el)) s = ev /\
                  read (memory :> bytes(m,32)) s = num_of_bytelist msg /\
                  read (memory :> bytes(pk,800)) s = num_of_bytelist ek /\
                  read (memory :> bytes(coins,32)) s = num_of_bytelist r)
             (\s. read PC s = returnaddress /\
                  read (memory :> bytes(c,768)) s =
                  num_of_bytelist(kpke_encrypt mlkem512 ek msg r) /\
                  C_RETURN s = word 0)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
              MAYCHANGE
               [memory :> bytes(c,768);
                memory :> bytes(word_sub stackpointer (word 11792),11792)])`;;

let MLKEM_NATIVE_INDCPA_ENC_K2_CLANG17_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_INDCPA_ENC_K2_CLANG17_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof, assuming the combined contract for *)
(* memset (for mlkem_poly_rej_uniform_x4) and the safety contract for        *)
(* memcpy. The events depend only on the addresses and on rho, the last 32   *)
(* bytes of the public key, through the samples of SampleNTT for the         *)
(* transposed matrix, but not on the message or the randomness. As for the   *)
(* correctness proof, the proof is by cases on whether the stack pointer is  *)
(* a multiple of 32, with the events in the two cases as the two branches of *)
(* the template.                                                             *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let EN_SAFE_TEMPLATE =
 `\(c:int64) (m:int64) (pk:int64) (coins:int64) (guard:int64) (mf:int64)
   (mc:int64) (pc:num) (stackpointer:int64) (returnaddress:int64)
   (rho:byte list).
   if aligned 32 stackpointer
   then f_ev_a c m pk coins guard mf mc pc stackpointer returnaddress rho
   else f_ev_u c m pk coins guard mf mc pc stackpointer returnaddress rho
   :(uarch_event)list`;;

let EN_SAFE_ALLOWED =
  [`pc:num`; `c:int64`; `m:int64`; `pk:int64`; `coins:int64`;
   `guard:int64`; `mf:int64`; `mc:int64`; `stackpointer:int64`;
   `returnaddress:int64`; `rho:byte list`];;

let EN2_SAFE_INTRO_TAC =
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
  FIRST_X_ASSUM(fun th ->
    if can (term_match [] `memset_full_contract mf ea el ev`) (concl th)
    then ASSUME_CALLEE_SAFETY_TAILED_TAC
          (REWRITE_RULE[ALL]
            (MATCH_MP
              MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_CLANG17_O2_IMAGE_SUBROUTINE_SAFE
              th)) "H_X4" THEN
         ASSUME_TAC(CONJUNCT2(MATCH_MP MEMSET_FULL_CONTRACT th))
    else NO_TAC) THEN
  FIRST_ASSUM(fun th ->
    if can (term_match [] `memset_safety_contract mf ea el ev`) (concl th)
    then ASSUME_CALLEE_SAFETY_TAILED_TAC
          (REWRITE_RULE[memset_safety_contract] th) "H_MEMSET"
    else NO_TAC) THEN
  FIRST_X_ASSUM(fun th1 ->
    if can (term_match [] `memset_safety_contract mf ea el ev`) (concl th1)
    then FIRST_X_ASSUM(fun th2 ->
      let gth = MATCH_MP
        MLKEM_NATIVE_POLY_GETNOISE_ETA1122_4X_K2_CLANG17_O2_IMAGE_SUBROUTINE_SAFE
        (CONJ th1 th2) in
      ASSUME_CALLEE_SAFETY_TAILED_ALT_TAC gth "H_GETNOISE")
    else NO_TAC) THEN
  ASSUME_CALLEE_SAFETY_TAILED_ALT_TAC
    MLKEM_NATIVE_POLY_GETNOISE_ETA2_K2_CLANG17_O2_IMAGE_SUBROUTINE_SAFE
    "H_ETA2" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_POLYVEC_FROMBYTES_K2_CLANG17_O2_IMAGE_SUBROUTINE_SAFE
    "H_FROMBYTES" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    (REWRITE_RULE[ALL]
      MLKEM_NATIVE_POLY_FROMMSG_CLANG17_O2_IMAGE_SUBROUTINE_SAFE)
    "H_FROMMSG" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_POLYVEC_NTT_K2_CLANG17_O2_IMAGE_SUBROUTINE_SAFE "H_NTT" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_POLYVEC_MULCACHE_COMPUTE_K2_CLANG17_O2_IMAGE_SUBROUTINE_SAFE
    "H_MULCACHE" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_BASEMUL_K2_CLANG17_O2_IMAGE_SUBROUTINE_SAFE "H_BASEMUL" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_POLYVEC_INVNTT_TOMONT_K2_CLANG17_O2_IMAGE_SUBROUTINE_SAFE
    "H_INVNTT" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    (REWRITE_RULE[ALL]
      MLKEM_NATIVE_POLY_INVNTT_TOMONT_CLANG17_O2_IMAGE_SUBROUTINE_SAFE)
    "H_POLY_INVNTT" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_POLYVEC_ADD_K2_CLANG17_O2_IMAGE_SUBROUTINE_SAFE "H_ADD" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    (REWRITE_RULE[ALL]
      MLKEM_NATIVE_POLY_ADD_CLANG17_O2_IMAGE_SUBROUTINE_SAFE)
    "H_POLY_ADD" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_POLYVEC_REDUCE_K2_CLANG17_O2_IMAGE_SUBROUTINE_SAFE
    "H_REDUCE" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_POLY_REDUCE_CLANG17_O2_IMAGE_SUBROUTINE_SAFE
    "H_POLY_REDUCE" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_POLYVEC_COMPRESS_DU_K2_CLANG17_O2_IMAGE_SUBROUTINE_SAFE
    "H_COMPRESS_DU" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_POLY_COMPRESS_D4_CLANG17_O2_IMAGE_SUBROUTINE_SAFE
    "H_COMPRESS_DV" THEN
  CONCRETIZE_F_EVENTS_TAC EN_SAFE_TEMPLATE THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NONOVERLAPPING_CLAUSES]) THEN
  SUBGOAL_THEN `aligned 16 (stackpointer:int64)` ASSUME_TAC THENL
   [UNDISCH_TAC `aligned 16 (word_add stackpointer (word 11792):int64)` THEN
    CONV_TAC(LAND_CONV NORMALIZE_ALIGNED_WORD_CONV) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_stack_chk_guard:num`] WORD_ADD;
              SPECL [`pc:num`; `got_memset:num`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`;
                                     `got_stack_chk_guard:num`] WORD_ADD;
                              SPECL [`pc:num`;
                                     `got_memset:num`] WORD_ADD]) THEN
  GHOST_INTRO_TAC `canary:int64` `read (memory :> bytes64 guard)` THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  MAP_EVERY (fun n ->
    ENSURES_PRESERVED_TAC ("x"^string_of_int n^"_init")
     (parse_term("X"^string_of_int n))) (19--29) THEN
  UNDISCH_TAC
   `!i j. i < 2 /\ j < 2
          ==> mlkem_samplentt_terminates
               (APPEND (mlkem_slice 768 32 ek) [word j; word i])` THEN
  ABBREV_TAC `rho = mlkem_slice 768 32 ek` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`2`; `\i j. APPEND (rho:byte list) [word j; word (i:num)]`]
                MLKEM_SAMPLENTT_TERMINATES_UNIFORM) THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `k:num`) THEN
  SUBGOAL_THEN
   `!i j. i < 2 /\ j < 2
          ==> 256 <= LENGTH(FILTER (\x. val x < 3329)
                      (MAP (word_zx:12 word->16 word)
                        (wordlist_of_num (336 + 112 * k)
                          (num_of_bytelist
                            (list_of_seq
                              (shake128 (APPEND rho [word i; word j]))
                              (504 + 168 * k))))))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL [`j:num`; `i:num`]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH(rho:byte list) = 32` ASSUME_TAC THENL
   [EXPAND_TAC "rho" THEN REWRITE_TAC[mlkem_slice; LENGTH_LIST_OF_SEQ];
    ALL_TAC];;

let EN2_SAFE_CALL_TAC name ilist n =
  REMOVE_THEN name (fun safety_th ->
    ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_clang17_O2_mc,EN2_EXEC,
       0x0,mlkem_native_libmlkem_clang17_O2_mc,safety_th)
      ilist n THENL
     [EXISTS_E2_TAC (ref EN_SAFE_ALLOWED); LABEL_TAC name safety_th]);;

let EN2_SAFE_CASE_TAC b =
  let e = `e:(uarch_event)list` in
  let x n = mk_comb(mk_comb(`read:(armstate,int64)component->armstate->int64`,
                            mk_const("X"^string_of_int n,[])),`s:armstate`) in
  let rest = [`pc:num`; `read SP s`; `read X30 s`] in
  ENSURES_INIT_TAC "s0" THEN
  EN2_PK_TAC THEN
  ARM_STEPS_TAC EN2_EXEC (1--10) THEN
  EN2_BUFFER_TAC THEN
  ARM_STEPS_TAC EN2_EXEC (11--11) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC EN2_EXEC (12--24) THEN
  EN2_SAFE_CALL_TAC "H_FROMBYTES" ([e; x 0; x 1] @ rest) 25 THEN
  ARM_STEPS_TAC EN2_EXEC (26--32) THEN
  EN2_SAFE_CALL_TAC "H_FROMMSG" [e; x 0; x 1; `pc:num`; `read X30 s`] 33 THEN
  ARM_STEPS_TAC EN2_EXEC (34--62) THEN
  INDCPA_GOT_TAC THEN
  EN2_SEED_INP_TAC (b + 5152) 0 0 "s62" THEN
  EN2_SEED_INP_TAC (b + 5216) 0 1 "s62" THEN
  EN2_SEED_INP_TAC (b + 5280) 1 0 "s62" THEN
  EN2_SEED_INP_TAC (b + 5344) 1 1 "s62" THEN
  ARM_STEPS_TAC EN2_EXEC [63] THEN
  EN2_HYP_TAC 0 0 THEN
  EN2_HYP_TAC 0 1 THEN
  EN2_HYP_TAC 1 0 THEN
  EN2_HYP_TAC 1 1 THEN
  EN2_SAFE_CALL_TAC "H_X4" ([e; x 0; x 1; x 2; x 3; x 4] @ [`APPEND (rho:byte list) [word 0; word 0]`; `APPEND (rho:byte list) [word 0; word 1]`; `APPEND (rho:byte list) [word 1; word 0]`; `APPEND (rho:byte list) [word 1; word 1]`] @ [`k:num`; `guard:int64`] @ rest) 64 THEN
  ARM_STEPS_TAC EN2_EXEC (65--93) THEN
  INDCPA_NONCE_TAC 3 THEN
  ARM_STEPS_TAC EN2_EXEC [94] THEN
  EN2_SAFE_CALL_TAC "H_GETNOISE" ([e; x 0; x 1; x 2; x 3; x 4; `guard:int64`] @ rest) 95 THEN
  ARM_STEPS_TAC EN2_EXEC (96--99) THEN
  INDCPA_GOT_TAC THEN
  ARM_STEPS_TAC EN2_EXEC [100] THEN
  EN2_SAFE_CALL_TAC "H_ETA2" ([e; x 0; x 1; x 2; `guard:int64`] @ rest) 101 THEN
  ARM_STEPS_TAC EN2_EXEC (102--104) THEN
  EN2_SAFE_CALL_TAC "H_NTT" ([e; x 0] @ rest) 105 THEN
  ARM_STEPS_TAC EN2_EXEC (106--110) THEN
  EN2_SAFE_CALL_TAC "H_MULCACHE" ([e; x 0; x 1] @ rest) 111 THEN
  ARM_STEPS_TAC EN2_EXEC (112--119) THEN
  EN2_SAFE_CALL_TAC "H_BASEMUL" [e; x 1; x 2; x 3; x 0; `pc:num`; `read X30 s`] 120 THEN
  ARM_STEPS_TAC EN2_EXEC (121--126) THEN
  EN2_SAFE_CALL_TAC "H_BASEMUL" [e; x 1; x 2; x 3; x 0; `pc:num`; `read X30 s`] 127 THEN
  ARM_STEPS_TAC EN2_EXEC (128--135) THEN
  EN2_SAFE_CALL_TAC "H_BASEMUL" [e; x 1; x 2; x 3; x 0; `pc:num`; `read X30 s`] 136 THEN
  ARM_STEPS_TAC EN2_EXEC (137--138) THEN
  EN2_SAFE_CALL_TAC "H_INVNTT" ([e; x 0] @ rest) 139 THEN
  ARM_STEPS_TAC EN2_EXEC (140--141) THEN
  EN2_SAFE_CALL_TAC "H_POLY_INVNTT" ([e; x 0] @ rest) 142 THEN
  ARM_STEPS_TAC EN2_EXEC (143--145) THEN
  EN2_SAFE_CALL_TAC "H_ADD" ([e; x 0; x 1] @ rest) 146 THEN
  ARM_STEPS_TAC EN2_EXEC (147--149) THEN
  EN2_SAFE_CALL_TAC "H_POLY_ADD" [e; x 0; x 1; `pc:num`; `read X30 s`] 150 THEN
  ARM_STEPS_TAC EN2_EXEC (151--153) THEN
  EN2_SAFE_CALL_TAC "H_POLY_ADD" [e; x 0; x 1; `pc:num`; `read X30 s`] 154 THEN
  ARM_STEPS_TAC EN2_EXEC (155--156) THEN
  EN2_SAFE_CALL_TAC "H_REDUCE" ([e; x 0] @ rest) 157 THEN
  ARM_STEPS_TAC EN2_EXEC (158--159) THEN
  EN2_SAFE_CALL_TAC "H_POLY_REDUCE" [e; x 0; `pc:num`; `read X30 s`] 160 THEN
  ARM_STEPS_TAC EN2_EXEC (161--162) THEN
  INDCPA_GOT_TAC THEN
  ARM_STEPS_TAC EN2_EXEC [163] THEN
  EN2_SAFE_CALL_TAC "H_COMPRESS_DU" ([e; x 0; x 1; `guard:int64`] @ rest) 164 THEN
  ARM_STEPS_TAC EN2_EXEC (165--167) THEN
  EN2_SAFE_CALL_TAC "H_COMPRESS_DV" ([e; x 0; x 1] @ rest) 168 THEN
  MAP_EVERY (fun (k0,k) ->
    ARM_STEPS_TAC EN2_EXEC (k0--k) THEN LIBC_PLT_TAC EN2_EXEC k THEN
    LIBC_SAFE_CALL_TAC "H_MEMSET" EN2_EXEC
     [e; x 0; x 1; x 2; `read X30 s`] (ref EN_SAFE_ALLOWED) (k + 5))
   [169,270; 276,279; 285,289; 295,299; 305,309] THEN
  ARM_STEPS_TAC EN2_EXEC (315--320) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC EN2_EXEC (321--334) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_TAC;;

let MLKEM_NATIVE_INDCPA_ENC_K2_CLANG17_O2_IMAGE_SUBROUTINE_SAFE_STMT =
  `!mf mc ea el ev.
   memset_full_contract mf ea el ev /\ memcpy_safety_contract mc ea el ev
   ==> exists f_events.
        forall e c m pk coins (ek:byte list) guard pc stackpointer
               returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\ LENGTH ek = 800 /\
          (!i j. i < 2 /\ j < 2
                 ==> mlkem_samplentt_terminates
                      (APPEND (mlkem_slice 768 32 ek) [word j; word i])) /\
          nonoverlapping (c,768)
           (word_sub stackpointer (word 11792),11792) /\
          nonoverlapping (pk,800) (word pc,libmlkem_size) /\
          ALLPAIRS nonoverlapping
           [(c,768); (word_sub stackpointer (word 11792),11792)]
           [(m,32); (pk,800); (coins,32); (word pc,libmlkem_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8);
            (word(pc + got_memcpy),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mlkem_native_libmlkem_clang17_O2_mc /\
                    read PC s = word (pc + mlkem512_indcpa_enc) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [c; m; pk; coins] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s
                     = guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(pk,800)) s = num_of_bytelist ek /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    C_RETURN s = word 0 /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events c m pk coins guard mf mc pc
                              (word_sub stackpointer (word 11792))
                              returnaddress (mlkem_slice 768 32 ek) /\
                       memaccess_inbounds e2
                        [m,32; pk,800; coins,32; c,768;
                         word_sub stackpointer (word 11792),11792;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8;
                         word(pc + got_memcpy),8; ea,el;
                         word(pc + rodata_mlk_KeccakF_RoundConstants),192;
                         word(pc + mlkem_poly_cbd3_consts),
                         mlkem_poly_cbd3_consts_size;
                         word(pc + mlkem_poly_cbd2_consts),
                         mlkem_poly_cbd2_consts_size;
                         word(pc + rodata_mlk_zetas),256;
                         word(pc + mlkem_poly_mulcache_compute_consts),
                         mlkem_poly_mulcache_compute_consts_size;
                         word(pc + mlkem_poly_compress_d4_consts),
                         mlkem_poly_compress_d4_consts_size]
                        [c,768; word_sub stackpointer (word 11792),11792]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(c,768);
                  memory :> bytes(word_sub stackpointer (word 11792),11792)])`;;

let MLKEM_NATIVE_INDCPA_ENC_K2_CLANG17_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_INDCPA_ENC_K2_CLANG17_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
