(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The encryption of K-PKE for ML-KEM-768 (FIPS 203 Algorithm 14). This is   *)
(* the code for mlkem768_indcpa_enc from mlkem-native's portable C           *)
(* implementation compiled by clang 17 with -O3 (see mlkem_native/README.md). *)
(* It decodes the vector t in the NTT domain from the encryption key and the *)
(* message m from its 32 bytes, generates the transposed matrix from rho     *)
(* (the last 32 bytes of the key), samples y, e1 and e2 from the randomness  *)
(* r, and computes u = NTT^-1(A^T NTT(y)) + e1 and v = NTT^-1(t^T NTT(y)) +  *)
(* e2 + mu, where mu is m decompressed. It writes the compressions of u and  *)
(* v as the ciphertext, zeroing its buffers. It is verified in the whole     *)
(* image (see libmlkem.ml), using the theorems for                           *)
(* mlkem768_polyvec_frombytes, mlkem_poly_frommsg,                         *)
(* mlkem_poly_rej_uniform_x4 and mlkem_poly_rej_uniform (the matrix        *)
(* generation is inlined),                                                 *)
(* mlkem768_poly_getnoise_eta1_4x, mlkem768_polyvec_ntt,                     *)
(* mlkem768_polyvec_mulcache_compute,                                        *)
(* mlkem768_polyvec_basemul_acc_montgomery_cached,                           *)
(* mlkem768_polyvec_invntt_tomont, mlkem_poly_invntt_tomont,                 *)
(* mlkem768_polyvec_add, mlkem_poly_add, mlkem768_polyvec_reduce,            *)
(* mlkem_poly_reduce, mlkem768_polyvec_compress_du and                       *)
(* mlkem_poly_compress_d4 in the image, and the contract for memset.         *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/mlkem_native/clang17_O2/polyvec_frombytes_k3_spec.ml";;
needs "arm/proofs/mlkem_native/clang17_O2/poly_frommsg_spec.ml";;
needs "arm/proofs/mlkem_native/clang17_O2/gen_matrix_k3_spec.ml";;
needs "arm/proofs/mlkem_native/clang17_O2/poly_getnoise_eta1_4x_k3_spec.ml";;
needs "arm/proofs/mlkem_native/clang17_O2/polyvec_ntt_k3_spec.ml";;
needs "arm/proofs/mlkem_native/clang17_O2/polyvec_mulcache_compute_k3_spec.ml";;
needs "arm/proofs/mlkem_native/clang17_O2/basemul_k3_spec.ml";;
needs "arm/proofs/mlkem_native/clang17_O2/polyvec_invntt_tomont_k3_spec.ml";;
needs "arm/proofs/mlkem_native/clang17_O2/poly_invntt_tomont_spec.ml";;
needs "arm/proofs/mlkem_native/clang17_O2/polyvec_add_k3_spec.ml";;
needs "arm/proofs/mlkem_native/clang17_O2/poly_add_spec.ml";;
needs "arm/proofs/mlkem_native/clang17_O2/polyvec_reduce_k3_spec.ml";;
needs "arm/proofs/mlkem_native/clang17_O2/poly_reduce_spec.ml";;
needs "arm/proofs/mlkem_native/clang17_O2/polyvec_compress_du_k3_spec.ml";;
needs "arm/proofs/mlkem_native/clang17_O2/poly_compress_d4_spec.ml";;
needs "arm/proofs/utils/mlkem_native_indcpa.ml";;

(*** The code in the image:

    mlkem768_indcpa_enc:
       +0x0: stp     x29, x30, [sp, #-96]!
       +0x4: stp     x28, x27, [sp, #16]
       +0x8: stp     x26, x25, [sp, #32]
       +0xc: stp     x24, x23, [sp, #48]
      +0x10: stp     x22, x21, [sp, #64]
      +0x14: stp     x20, x19, [sp, #80]
      +0x18: mov     x29, sp
      +0x1c: sub     x9, sp, #0x3, lsl #12
      +0x20: sub     x9, x9, #0x360
      +0x24: and     sp, x9, #0xffffffffffffffe0
      +0x28: adrp    x8, <page>
      +0x2c: mov     x19, x0
      +0x30: add     x0, sp, #0x1, lsl #12
      +0x34: mov     x22, x1
      +0x38: add     x0, x0, #0x520
      +0x3c: mov     x1, x2
      +0x40: ldr     x8, [x8, #4088]  // got_stack_chk_guard
      +0x44: add     x23, sp, #0x1, lsl #12
      +0x48: mov     x20, x3
      +0x4c: mov     x21, x2
      +0x50: add     x23, x23, #0x520
      +0x54: ldr     x8, [x8]
      +0x58: str     x8, [sp, #13144]
      +0x5c: bl      <mlkem768_polyvec_frombytes>
      +0x60: ldr     q0, [x21, #1152]
      +0x64: add     x0, sp, #0x520
      +0x68: ldr     q1, [x21, #1168]
      +0x6c: mov     x1, x22
      +0x70: add     x26, sp, #0x520
      +0x74: str     q0, [sp, #13088]
      +0x78: str     q1, [sp, #13104]
      +0x7c: bl      <mlkem_poly_frommsg>
      +0x80: add     x0, sp, #0x2, lsl #12
      +0x84: add     x1, sp, #0x3, lsl #12
      +0x88: add     x0, x0, #0x120
      +0x8c: add     x1, x1, #0x320
      +0x90: mov     w2, #0x1
      +0x94: add     x22, sp, #0x2, lsl #12
      +0x98: add     x22, x22, #0x120
      +0x9c: bl      <mlkem768_gen_matrix>
      +0xa0: add     x24, sp, #0x1, lsl #12
      +0xa4: add     x0, sp, #0x1, lsl #12
      +0xa8: add     x24, x24, #0xb20
      +0xac: mov     w8, #0xff
      +0xb0: add     x1, x24, #0x200
      +0xb4: add     x2, x24, #0x400
      +0xb8: add     x0, x0, #0xb20
      +0xbc: mov     x3, xzr
      +0xc0: mov     x4, x20
      +0xc4: mov     w5, wzr
      +0xc8: mov     w6, #0x1
      +0xcc: mov     w7, #0x2
      +0xd0: strb    w8, [sp]
      +0xd4: bl      <mlkem768_poly_getnoise_eta1_4x>
      +0xd8: add     x25, sp, #0xf20
      +0xdc: mov     w8, #0x6
      +0xe0: add     x1, x25, #0x200
      +0xe4: add     x2, x25, #0x400
      +0xe8: add     x0, sp, #0xf20
      +0xec: add     x3, sp, #0x320
      +0xf0: mov     x4, x20
      +0xf4: mov     w5, #0x3
      +0xf8: mov     w6, #0x4
      +0xfc: mov     w7, #0x5
     +0x100: add     x28, sp, #0x320
     +0x104: strb    w8, [sp]
     +0x108: bl      <mlkem768_poly_getnoise_eta1_4x>
     +0x10c: add     x0, sp, #0x1, lsl #12
     +0x110: add     x0, x0, #0xb20
     +0x114: bl      <mlkem768_polyvec_ntt>
     +0x118: add     x1, sp, #0x1, lsl #12
     +0x11c: add     x0, sp, #0x20
     +0x120: add     x1, x1, #0xb20
     +0x124: add     x21, sp, #0x20
     +0x128: bl      <mlkem768_polyvec_mulcache_compute>
     +0x12c: add     x1, sp, #0x2, lsl #12
     +0x130: add     x2, sp, #0x1, lsl #12
     +0x134: add     x0, sp, #0x920
     +0x138: add     x1, x1, #0x120
     +0x13c: add     x2, x2, #0xb20
     +0x140: add     x3, sp, #0x20
     +0x144: add     x20, sp, #0x920
     +0x148: bl      <mlkem768_polyvec_basemul_acc_montgomery_cached>
     +0x14c: add     x2, sp, #0x1, lsl #12
     +0x150: add     x0, x20, #0x200
     +0x154: add     x1, x22, #0x600
     +0x158: add     x2, x2, #0xb20
     +0x15c: add     x3, sp, #0x20
     +0x160: bl      <mlkem768_polyvec_basemul_acc_montgomery_cached>
     +0x164: add     x2, sp, #0x1, lsl #12
     +0x168: add     x0, x20, #0x400
     +0x16c: add     x1, x22, #0xc00
     +0x170: add     x2, x2, #0xb20
     +0x174: add     x3, sp, #0x20
     +0x178: bl      <mlkem768_polyvec_basemul_acc_montgomery_cached>
     +0x17c: add     x1, sp, #0x1, lsl #12
     +0x180: add     x2, sp, #0x1, lsl #12
     +0x184: add     x0, sp, #0x720
     +0x188: add     x1, x1, #0x520
     +0x18c: add     x2, x2, #0xb20
     +0x190: add     x3, sp, #0x20
     +0x194: add     x27, sp, #0x720
     +0x198: bl      <mlkem768_polyvec_basemul_acc_montgomery_cached>
     +0x19c: add     x0, sp, #0x920
     +0x1a0: bl      <mlkem768_polyvec_invntt_tomont>
     +0x1a4: add     x0, sp, #0x720
     +0x1a8: bl      <mlkem_poly_invntt_tomont>
     +0x1ac: add     x0, sp, #0x920
     +0x1b0: add     x1, sp, #0xf20
     +0x1b4: bl      <mlkem768_polyvec_add>
     +0x1b8: add     x0, sp, #0x720
     +0x1bc: add     x1, sp, #0x320
     +0x1c0: bl      <mlkem_poly_add>
     +0x1c4: add     x0, sp, #0x720
     +0x1c8: add     x1, sp, #0x520
     +0x1cc: bl      <mlkem_poly_add>
     +0x1d0: add     x0, sp, #0x920
     +0x1d4: bl      <mlkem768_polyvec_reduce>
     +0x1d8: add     x0, sp, #0x720
     +0x1dc: bl      <mlkem_poly_reduce>
     +0x1e0: add     x1, sp, #0x920
     +0x1e4: mov     x0, x19
     +0x1e8: bl      <mlkem768_polyvec_compress_du>
     +0x1ec: add     x0, x19, #0x3c0
     +0x1f0: add     x1, sp, #0x720
     +0x1f4: bl      <mlkem_poly_compress_d4>
     +0x1f8: add     x0, sp, #0x20
     +0x1fc: mov     w1, wzr
     +0x200: mov     w2, #0x300
     +0x204: bl      <memset@plt>
     +0x208: movi    v0.2d, #0x0
     +0x20c: add     x0, sp, #0x920
     +0x210: mov     w1, wzr
     +0x214: mov     w2, #0x600
     +0x218: str     q0, [sp, #1296]
     +0x21c: str     q0, [sp, #1280]
     +0x220: str     q0, [sp, #1264]
     +0x224: str     q0, [sp, #1248]
     +0x228: str     q0, [sp, #1232]
     +0x22c: str     q0, [sp, #1216]
     +0x230: str     q0, [sp, #1200]
     +0x234: str     q0, [sp, #1184]
     +0x238: str     q0, [sp, #1168]
     +0x23c: str     q0, [sp, #1152]
     +0x240: str     q0, [sp, #1136]
     +0x244: str     q0, [sp, #1120]
     +0x248: str     q0, [sp, #1104]
     +0x24c: str     q0, [sp, #1088]
     +0x250: str     q0, [sp, #1072]
     +0x254: str     q0, [sp, #1056]
     +0x258: str     q0, [sp, #1040]
     +0x25c: stp     q0, q0, [sp, #816]
     +0x260: stp     q0, q0, [sp, #848]
     +0x264: stp     q0, q0, [sp, #880]
     +0x268: stp     q0, q0, [sp, #912]
     +0x26c: stp     q0, q0, [sp, #944]
     +0x270: stp     q0, q0, [sp, #976]
     +0x274: stp     q0, q0, [sp, #1008]
     +0x278: str     q0, [sp, #800]
     +0x27c: str     q0, [sp, #1808]
     +0x280: str     q0, [sp, #1792]
     +0x284: str     q0, [sp, #1776]
     +0x288: str     q0, [sp, #1760]
     +0x28c: str     q0, [sp, #1744]
     +0x290: str     q0, [sp, #1728]
     +0x294: str     q0, [sp, #1712]
     +0x298: str     q0, [sp, #1696]
     +0x29c: str     q0, [sp, #1680]
     +0x2a0: str     q0, [sp, #1664]
     +0x2a4: str     q0, [sp, #1648]
     +0x2a8: str     q0, [sp, #1632]
     +0x2ac: str     q0, [sp, #1616]
     +0x2b0: str     q0, [sp, #1600]
     +0x2b4: str     q0, [sp, #1584]
     +0x2b8: str     q0, [sp, #1568]
     +0x2bc: str     q0, [sp, #1552]
     +0x2c0: str     q0, [sp, #1536]
     +0x2c4: str     q0, [sp, #1520]
     +0x2c8: str     q0, [sp, #1504]
     +0x2cc: str     q0, [sp, #1488]
     +0x2d0: str     q0, [sp, #1472]
     +0x2d4: str     q0, [sp, #1456]
     +0x2d8: str     q0, [sp, #1440]
     +0x2dc: str     q0, [sp, #1424]
     +0x2e0: str     q0, [sp, #1408]
     +0x2e4: str     q0, [sp, #1392]
     +0x2e8: str     q0, [sp, #1376]
     +0x2ec: str     q0, [sp, #1360]
     +0x2f0: str     q0, [sp, #1344]
     +0x2f4: str     q0, [sp, #1328]
     +0x2f8: str     q0, [sp, #1312]
     +0x2fc: str     q0, [sp, #2320]
     +0x300: str     q0, [sp, #2304]
     +0x304: str     q0, [sp, #2288]
     +0x308: str     q0, [sp, #2272]
     +0x30c: str     q0, [sp, #2256]
     +0x310: str     q0, [sp, #2240]
     +0x314: str     q0, [sp, #2224]
     +0x318: str     q0, [sp, #2208]
     +0x31c: str     q0, [sp, #2192]
     +0x320: str     q0, [sp, #2176]
     +0x324: str     q0, [sp, #2160]
     +0x328: str     q0, [sp, #2144]
     +0x32c: str     q0, [sp, #2128]
     +0x330: str     q0, [sp, #2112]
     +0x334: str     q0, [sp, #2096]
     +0x338: str     q0, [sp, #2080]
     +0x33c: str     q0, [sp, #2064]
     +0x340: str     q0, [sp, #2048]
     +0x344: str     q0, [sp, #2032]
     +0x348: str     q0, [sp, #2016]
     +0x34c: str     q0, [sp, #2000]
     +0x350: str     q0, [sp, #1984]
     +0x354: str     q0, [sp, #1968]
     +0x358: str     q0, [sp, #1952]
     +0x35c: str     q0, [sp, #1936]
     +0x360: str     q0, [sp, #1920]
     +0x364: str     q0, [sp, #1904]
     +0x368: str     q0, [sp, #1888]
     +0x36c: str     q0, [sp, #1872]
     +0x370: str     q0, [sp, #1856]
     +0x374: str     q0, [sp, #1840]
     +0x378: str     q0, [sp, #1824]
     +0x37c: bl      <memset@plt>
     +0x380: add     x0, sp, #0xf20
     +0x384: mov     w1, wzr
     +0x388: mov     w2, #0x600
     +0x38c: bl      <memset@plt>
     +0x390: add     x0, sp, #0x1, lsl #12
     +0x394: add     x0, x0, #0x520
     +0x398: mov     w1, wzr
     +0x39c: mov     w2, #0x600
     +0x3a0: bl      <memset@plt>
     +0x3a4: add     x0, sp, #0x1, lsl #12
     +0x3a8: add     x0, x0, #0xb20
     +0x3ac: mov     w1, wzr
     +0x3b0: mov     w2, #0x600
     +0x3b4: bl      <memset@plt>
     +0x3b8: add     x0, sp, #0x2, lsl #12
     +0x3bc: add     x0, x0, #0x120
     +0x3c0: mov     w1, wzr
     +0x3c4: mov     w2, #0x1200
     +0x3c8: bl      <memset@plt>
     +0x3cc: movi    v0.2d, #0x0
     +0x3d0: add     x8, sp, #0x3, lsl #12
     +0x3d4: add     x8, x8, #0x320
     +0x3d8: str     q0, [sp, #13104]
     +0x3dc: str     q0, [sp, #13088]
     +0x3e0: adrp    x8, <page>
     +0x3e4: ldr     x8, [x8, #4088]  // got_stack_chk_guard
     +0x3e8: ldr     x9, [sp, #13144]
     +0x3ec: ldr     x8, [x8]
     +0x3f0: cmp     x8, x9
     +0x3f4: b.ne    <mlkem768_indcpa_enc+0x41c>
     +0x3f8: mov     w0, wzr
     +0x3fc: mov     sp, x29
     +0x400: ldp     x20, x19, [sp, #80]
     +0x404: ldp     x22, x21, [sp, #64]
     +0x408: ldp     x24, x23, [sp, #48]
     +0x40c: ldp     x26, x25, [sp, #32]
     +0x410: ldp     x28, x27, [sp, #16]
     +0x414: ldp     x29, x30, [sp], #96
     +0x418: ret
     +0x41c: bl      <__stack_chk_fail>
 ***)

let MLKEM_NATIVE_INDCPA_ENC_K3_CLANG17_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_clang17_O2_mc
   [layout_range "plt_memset"; layout_range "mlkem768_indcpa_enc"];;

let EN3_EXEC = MLKEM_NATIVE_INDCPA_ENC_K3_CLANG17_O2_EXEC;;

(* ------------------------------------------------------------------------- *)
(* The encryption in FIPS 203 in terms of the values computed by the code:   *)
(* the 12-bit fields of the encryption key as decoded (which may be >= q),   *)
(* the NTT of y and its multiplication cache, the noise e1 and e2, the       *)
(* decompressed message, the products with the transposed matrix and with t  *)
(* in Montgomery form, their inverse NTTs, and the results after adding the  *)
(* noise and the message and reducing, whose compressions are encoded in the *)
(* ciphertext.                                                               *)
(* ------------------------------------------------------------------------- *)

let KPKE_ENCRYPT_K3_RESULT_STMT =
  `!ek m r (TT:num->int16) (YH:num->int16) (MC:num->int16) (E1:num->int16)
    (E2:num->int16) (MU:num->int16) (U0:num->int16) (V0:num->int16)
    (U1:num->int16) (V1:num->int16) (U3:num->int16) (V4:num->int16).
     (!i j n. i < 3 /\ j < 3 /\ n < 256
              ==> mlkem_sample_ntt
                   (APPEND (mlkem_slice 1152 32 ek) [word j; word i]) n
                  < &3329) /\
     (!i. i < 768
          ==> TT i = word((num_of_bytelist ek DIV 2 EXP (12 * i)) MOD
                          2 EXP 12)) /\
     (!j i. j < 3 /\ i < 256
            ==> (ival(YH(256 * j + i)) ==
                 mlkem_ntt (mlkem_cbd 2 (mlkem_prf 2 r (word j))) i)
                (mod &3329) /\
                abs(ival(YH(256 * j + i))) <= &23594) /\
     (!j p. j < 3 /\ p < 128
            ==> (ival(MC(128 * j + p)) ==
                 ival(YH(256 * j + 2 * p + 1)) *
                 &17 pow (2 * bitreverse7 p + 1)) (mod &3329)) /\
     (!j i. j < 3 /\ i < 256
            ==> (ival(E1(256 * j + i)) ==
                 coeff i (mlkem_cbd 2 (mlkem_prf 2 r (word(3 + j)))))
                (mod &3329) /\
                abs(ival(E1(256 * j + i))) <= &2) /\
     (!i. i < 256
          ==> (ival(E2 i) == coeff i (mlkem_cbd 2 (mlkem_prf 2 r (word 6))))
              (mod &3329) /\
              abs(ival(E2 i)) <= &2) /\
     (!i. i < 256
          ==> MU i = word((3329 * (num_of_bytelist m DIV 2 EXP i) MOD 2 + 1)
                          DIV 2)) /\
     (!q p. q < 3 /\ p < 128
            ==> (ival(U0(256 * q + 2 * p)) ==
                 &169 *
                 ((mlkem_sample_ntt (APPEND (mlkem_slice 1152 32 ek)
                                       [word q; word 2]) (2 * p + 1) *
                   ival(MC(256 + p)) +
                   mlkem_sample_ntt (APPEND (mlkem_slice 1152 32 ek)
                                       [word q; word 2]) (2 * p) *
                   ival(YH(512 + 2 * p))) +
                  (mlkem_sample_ntt (APPEND (mlkem_slice 1152 32 ek)
                                       [word q; word 1]) (2 * p + 1) *
                   ival(MC(128 + p)) +
                   mlkem_sample_ntt (APPEND (mlkem_slice 1152 32 ek)
                                       [word q; word 1]) (2 * p) *
                   ival(YH(256 + 2 * p))) +
                  (mlkem_sample_ntt (APPEND (mlkem_slice 1152 32 ek)
                                       [word q; word 0]) (2 * p + 1) *
                   ival(MC p) +
                   mlkem_sample_ntt (APPEND (mlkem_slice 1152 32 ek)
                                       [word q; word 0]) (2 * p) *
                   ival(YH(2 * p))))) (mod &3329) /\
                (ival(U0(256 * q + 2 * p + 1)) ==
                 &169 *
                 ((mlkem_sample_ntt (APPEND (mlkem_slice 1152 32 ek)
                                       [word q; word 2]) (2 * p + 1) *
                   ival(YH(512 + 2 * p)) +
                   mlkem_sample_ntt (APPEND (mlkem_slice 1152 32 ek)
                                       [word q; word 2]) (2 * p) *
                   ival(YH(512 + 2 * p + 1))) +
                  (mlkem_sample_ntt (APPEND (mlkem_slice 1152 32 ek)
                                       [word q; word 1]) (2 * p + 1) *
                   ival(YH(256 + 2 * p)) +
                   mlkem_sample_ntt (APPEND (mlkem_slice 1152 32 ek)
                                       [word q; word 1]) (2 * p) *
                   ival(YH(256 + 2 * p + 1))) +
                  (mlkem_sample_ntt (APPEND (mlkem_slice 1152 32 ek)
                                       [word q; word 0]) (2 * p + 1) *
                   ival(YH(2 * p)) +
                   mlkem_sample_ntt (APPEND (mlkem_slice 1152 32 ek)
                                       [word q; word 0]) (2 * p) *
                   ival(YH(2 * p + 1))))) (mod &3329)) /\
     (!p. p < 128
          ==> (ival(V0(2 * p)) ==
               &169 *
               ((ival(TT(512 + 2 * p + 1)) * ival(MC(256 + p)) +
                 ival(TT(512 + 2 * p)) * ival(YH(512 + 2 * p))) +
                (ival(TT(256 + 2 * p + 1)) * ival(MC(128 + p)) +
                 ival(TT(256 + 2 * p)) * ival(YH(256 + 2 * p))) +
                (ival(TT(2 * p + 1)) * ival(MC p) +
                 ival(TT(2 * p)) * ival(YH(2 * p))))) (mod &3329) /\
              (ival(V0(2 * p + 1)) ==
               &169 *
               ((ival(TT(512 + 2 * p + 1)) * ival(YH(512 + 2 * p)) +
                 ival(TT(512 + 2 * p)) * ival(YH(512 + 2 * p + 1))) +
                (ival(TT(256 + 2 * p + 1)) * ival(YH(256 + 2 * p)) +
                 ival(TT(256 + 2 * p)) * ival(YH(256 + 2 * p + 1))) +
                (ival(TT(2 * p + 1)) * ival(YH(2 * p)) +
                 ival(TT(2 * p)) * ival(YH(2 * p + 1))))) (mod &3329)) /\
     (!j i. j < 3 /\ i < 256
            ==> (ival(U1(256 * j + i)) ==
                 inverse_ntt (\n. ival(U0(256 * j + n))) i) (mod &3329) /\
                abs(ival(U1(256 * j + i))) <= &26624) /\
     (!i. i < 256
          ==> (ival(V1 i) == inverse_ntt (\n. ival(V0 n)) i) (mod &3329) /\
              abs(ival(V1 i)) <= &26624) /\
     (!i. i < 768 ==> ival(U3 i) = ival(word_add (U1 i) (E1 i)) rem &3329) /\
     (!i. i < 256
          ==> ival(V4 i) =
              ival(word_add (word_add (V1 i) (E2 i)) (MU i)) rem &3329)
     ==> nsum {i | i < 768}
              (\i. ((2048 * val(U3 i) + 3329) DIV 6658) MOD 1024 *
                   2 EXP (10 * i)) +
         2 EXP (8 * 960) *
         nsum {i | i < 256}
              (\i. ((32 * val(V4 i) + 3329) DIV 6658) MOD 16 * 2 EXP (4 * i)) =
         num_of_bytelist(kpke_encrypt mlkem768 ek m r)`;;

let KPKE_ENCRYPT_K3_RESULT = assume_spec KPKE_ENCRYPT_K3_RESULT_STMT;;

(* ------------------------------------------------------------------------- *)
(* The buffers are aligned to 32 bytes within the stack frame, so their      *)
(* addresses depend on whether the stack pointer is a multiple of 32 or just *)
(* of 16. The first 1152 bytes of the encryption key are decoded by          *)
(* mlkem768_polyvec_frombytes and its last 32, rho, are copied as two        *)
(* 128-bit words to the seed for mlkem768_gen_matrix. The message is decoded *)
(* and decompressed by mlkem_poly_frommsg.                                   *)
(* ------------------------------------------------------------------------- *)

let EN3_BUFFER_ADDRESS_STMT =
  `!sp:int64.
        aligned 16 sp
        ==> word_and (word_add sp (word 3776)) (word 18446744073709551584) =
            word_add sp (word(if aligned 32 sp then 3776 else 3760))`;;

let EN3_BUFFER_ADDRESS = assume_spec EN3_BUFFER_ADDRESS_STMT;;

let EN3_BUFFER_TAC =
  FIRST_ASSUM(fun th ->
    if concl th = `aligned 32 (stackpointer:int64)` ||
       concl th = `~aligned 32 (stackpointer:int64)`
    then SUBST_ALL_TAC
          (REWRITE_RULE[th; ASSUME `aligned 16 (stackpointer:int64)`]
            (SPEC `stackpointer:int64` EN3_BUFFER_ADDRESS))
    else NO_TAC);;

let EN3_PK_TAC =
  FIRST_ASSUM(fun th ->
    if can (term_match []
         `read (memory :> bytes(pk,1184)) s = num_of_bytelist ek`) (concl th)
    then
      ASSUME_TAC(REWRITE_RULE[GSYM READ_COMPONENT_COMPOSE]
       (REWRITE_RULE[READ_COMPONENT_COMPOSE; READ_BYTES_MOD;
                     ARITH_RULE `MIN 1184 1152 = 1152`]
        (AP_THM(AP_TERM `(MOD):num->num->num`
                 (REWRITE_RULE[READ_COMPONENT_COMPOSE] th))
           `2 EXP (8 * 1152)`))) THEN
      MP_TAC(SPECL [`pk:int64`; `ek:byte list`; `1152`; `32`;
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

let EN3_TT_TAC b s =
  INDCPA_GHOST_TAC "TT" (b + 5408) 768 s THEN
  SUBGOAL_THEN
   `!i. i < 768
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
    MATCH_MP_TAC DIV_MOD_EXP_LOW THEN UNDISCH_TAC `i < 768` THEN ARITH_TAC;
    ALL_TAC];;

let EN3_MU_TAC b s =
  INDCPA_GHOST_TAC "MU" (b + 1312) 256 s THEN
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
(* The callees. The matrix is generated with transposition, and the fourth   *)
(* output of the first call of mlkem768_poly_getnoise_eta1_4x is a null      *)
(* pointer (its fourth nonce, at the bottom of the stack, is 255), so the    *)
(* theorems are specialized to those cases. In the second call, the fourth   *)
(* output is e2, which is not null since the stack frame does not contain    *)
(* address 0. The theorems with hypotheses of the form ALL P l are used with *)
(* them as conjunctions.                                                     *)
(* ------------------------------------------------------------------------- *)

let LOCAL_POLYVEC_FROMBYTES_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_clang17_O2_mc,EN3_EXEC,
    0x0,mlkem_native_libmlkem_clang17_O2_mc,
    MLKEM_NATIVE_POLYVEC_FROMBYTES_K3_CLANG17_O2_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_POLY_FROMMSG_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_clang17_O2_mc,EN3_EXEC,
    0x0,mlkem_native_libmlkem_clang17_O2_mc,
    MLKEM_NATIVE_POLY_FROMMSG_CLANG17_O2_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_GEN_MATRIX_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_clang17_O2_mc,EN3_EXEC,
    0x0,mlkem_native_libmlkem_clang17_O2_mc,
    INDCPA_GEN_MATRIX_SPEC
      MLKEM_NATIVE_GEN_MATRIX_K3_CLANG17_O2_IMAGE_SUBROUTINE_CORRECT
      `word 1:int64`);;

let LOCAL_GETNOISE3_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_clang17_O2_mc,EN3_EXEC,
    0x0,mlkem_native_libmlkem_clang17_O2_mc,
    INDCPA_GETNOISE_NULL
     MLKEM_NATIVE_POLY_GETNOISE_ETA1_4X_K3_CLANG17_O2_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_GETNOISE4_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_clang17_O2_mc,EN3_EXEC,
    0x0,mlkem_native_libmlkem_clang17_O2_mc,
    MLKEM_NATIVE_POLY_GETNOISE_ETA1_4X_K3_CLANG17_O2_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_POLYVEC_NTT_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_clang17_O2_mc,EN3_EXEC,
    0x0,mlkem_native_libmlkem_clang17_O2_mc,
    MLKEM_NATIVE_POLYVEC_NTT_K3_CLANG17_O2_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_POLYVEC_MULCACHE_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_clang17_O2_mc,EN3_EXEC,
    0x0,mlkem_native_libmlkem_clang17_O2_mc,
    MLKEM_NATIVE_POLYVEC_MULCACHE_COMPUTE_K3_CLANG17_O2_IMAGE_SUBROUTINE_CORRECT
   );;

let LOCAL_BASEMUL_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_clang17_O2_mc,EN3_EXEC,
    0x0,mlkem_native_libmlkem_clang17_O2_mc,
    REWRITE_RULE[ALL]
      MLKEM_NATIVE_BASEMUL_K3_CLANG17_O2_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_POLYVEC_INVNTT_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_clang17_O2_mc,EN3_EXEC,
    0x0,mlkem_native_libmlkem_clang17_O2_mc,
    MLKEM_NATIVE_POLYVEC_INVNTT_TOMONT_K3_CLANG17_O2_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_POLY_INVNTT_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_clang17_O2_mc,EN3_EXEC,
    0x0,mlkem_native_libmlkem_clang17_O2_mc,
    REWRITE_RULE[ALL]
      MLKEM_NATIVE_POLY_INVNTT_TOMONT_CLANG17_O2_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_POLYVEC_ADD_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_clang17_O2_mc,EN3_EXEC,
    0x0,mlkem_native_libmlkem_clang17_O2_mc,
    MLKEM_NATIVE_POLYVEC_ADD_K3_CLANG17_O2_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_POLY_ADD_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_clang17_O2_mc,EN3_EXEC,
    0x0,mlkem_native_libmlkem_clang17_O2_mc,
    REWRITE_RULE[ALL]
      MLKEM_NATIVE_POLY_ADD_CLANG17_O2_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_POLYVEC_REDUCE_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_clang17_O2_mc,EN3_EXEC,
    0x0,mlkem_native_libmlkem_clang17_O2_mc,
    MLKEM_NATIVE_POLYVEC_REDUCE_K3_CLANG17_O2_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_POLY_REDUCE_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_clang17_O2_mc,EN3_EXEC,
    0x0,mlkem_native_libmlkem_clang17_O2_mc,
    MLKEM_NATIVE_POLY_REDUCE_CLANG17_O2_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_POLYVEC_COMPRESS_DU_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_clang17_O2_mc,EN3_EXEC,
    0x0,mlkem_native_libmlkem_clang17_O2_mc,
    MLKEM_NATIVE_POLYVEC_COMPRESS_DU_K3_CLANG17_O2_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_POLY_COMPRESS_D4_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_clang17_O2_mc,EN3_EXEC,
    0x0,mlkem_native_libmlkem_clang17_O2_mc,
    MLKEM_NATIVE_POLY_COMPRESS_D4_CLANG17_O2_IMAGE_SUBROUTINE_CORRECT);;

(* ------------------------------------------------------------------------- *)
(* The facts about the stages of the computation other than those given by   *)
(* the tactics in mlkem_native_indcpa.ml: the coefficients of the transposed *)
(* matrix as given by SampleNTT, the bounds on the inputs of the             *)
(* multiplications, the products with the rows of the transposed matrix and  *)
(* with t, and the bounds on the inputs of the compressions.                 *)
(* ------------------------------------------------------------------------- *)

let EN3_MATRIX_TAC b s =
  let addr = parse_term(Printf.sprintf
    "word_add stackpointer (word (%d + 512 * (3 * q + j))):int64" b) in
  SUBGOAL_THEN
   `!q j n. q < 3 /\ j < 3 /\ n < 256
            ==> &0 <= mlkem_sample_ntt (APPEND rho [word q; word j]) n /\
                mlkem_sample_ntt (APPEND rho [word q; word j]) n < &3329`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    MATCH_MP_TAC MLKEM_SAMPLE_NTT_REJ_BOUND THEN
    EXISTS_TAC `k:num` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!q j n. q < 3 /\ j < 3 /\ n < 256
            ==> ival((AM:num->int16)(768 * q + 256 * j + n)) =
                mlkem_sample_ntt (APPEND rho [word q; word j]) n`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    INDCPA_GHOST_SPEC_TAC "AM" `768 * q + 256 * j + n` THEN
    MP_TAC(SPECL [addr; s; `APPEND (rho:byte list) [word q; word j]`;
                  `k:num`; `n:num`] MLKEM_NATIVE_SAMPLE_COEFF) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
    AP_TERM_TAC THEN REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    MATCH_MP_TAC READ16_OFFSET_EQ THEN ARITH_TAC;
    ALL_TAC];;

let EN3_AM_INST r j =
  let th = SPECL [mk_small_numeral r; mk_small_numeral j]
    (ASSUME `!q j n. q < 3 /\ j < 3 /\ n < 256
                     ==> ival((AM:num->int16)(768 * q + 256 * j + n)) =
                         mlkem_sample_ntt (APPEND rho [word q; word j]) n`) in
  CONV_RULE(NUM_REDUCE_CONV THENC REWRITE_CONV[ADD_CLAUSES; ADD_ASSOC] THENC
            NUM_REDUCE_CONV) th;;

let EN3_AM_BOUND_TAC =
  SUBGOAL_THEN `!m. m < 2304 ==> abs(ival((AM:num->int16) m)) <= &2 pow 12`
  (LABEL_TAC "ambound") THENL
   [X_GEN_TAC `m':num` THEN DISCH_TAC THEN
    MP_TAC(SPECL [`768`; `3`; `m':num`] EXISTS_DIV_MOD_LT) THEN
    ASM_REWRITE_TAC[ARITH_RULE `768 * 3 = 2304`; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`q:num`; `x:num`] THEN STRIP_TAC THEN
    MP_TAC(SPECL [`256`; `3`; `x:num`] EXISTS_DIV_MOD_LT) THEN
    ASM_REWRITE_TAC[ARITH_RULE `256 * 3 = 768`; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`j:num`; `n:num`] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC(INT_ARITH
     `&0 <= x /\ x < &3329 ==> abs(x:int) <= &2 pow 12`) THEN
    ASM_SIMP_TAC[];
    ALL_TAC];;

let EN3_BASEMUL_DEFS =
  [basemul3_even; basemul3_odd; pmul_acc3; pmull_acc3; pmull];;

let EN3_U0_GOAL = `!q p. q < 3 /\ p < 128
       ==> (ival((U0:num->int16)(256 * q + 2 * p)) ==
            &169 *
            ((mlkem_sample_ntt (APPEND rho [word q; word 2]) (2 * p + 1) *
              ival((MC:num->int16)(256 + p)) +
              mlkem_sample_ntt (APPEND rho [word q; word 2]) (2 * p) *
              ival((YH:num->int16)(512 + 2 * p))) +
             (mlkem_sample_ntt (APPEND rho [word q; word 1]) (2 * p + 1) *
              ival(MC(128 + p)) +
              mlkem_sample_ntt (APPEND rho [word q; word 1]) (2 * p) *
              ival(YH(256 + 2 * p))) +
             (mlkem_sample_ntt (APPEND rho [word q; word 0]) (2 * p + 1) *
              ival(MC p) +
              mlkem_sample_ntt (APPEND rho [word q; word 0]) (2 * p) *
              ival(YH(2 * p))))) (mod &3329) /\
           (ival(U0(256 * q + 2 * p + 1)) ==
            &169 *
            ((mlkem_sample_ntt (APPEND rho [word q; word 2]) (2 * p + 1) *
              ival(YH(512 + 2 * p)) +
              mlkem_sample_ntt (APPEND rho [word q; word 2]) (2 * p) *
              ival(YH(512 + 2 * p + 1))) +
             (mlkem_sample_ntt (APPEND rho [word q; word 1]) (2 * p + 1) *
              ival(YH(256 + 2 * p)) +
              mlkem_sample_ntt (APPEND rho [word q; word 1]) (2 * p) *
              ival(YH(256 + 2 * p + 1))) +
             (mlkem_sample_ntt (APPEND rho [word q; word 0]) (2 * p + 1) *
              ival(YH(2 * p)) +
              mlkem_sample_ntt (APPEND rho [word q; word 0]) (2 * p) *
              ival(YH(2 * p + 1))))) (mod &3329)`;;

let EN3_U0_TAC b s =
  INDCPA_GHOST_TAC "U0" (b + 2336) 768 s THEN
  SUBGOAL_THEN EN3_U0_GOAL ASSUME_TAC THENL
   [REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
    CONV_TAC EXPAND_CASES_CONV THEN REPEAT CONJ_TAC THENL
     (map (fun q -> INDCPA_BASEMUL3_ROW_TAC "U0" (b + 2336 + 512 * q)
                     "ambound" (map (EN3_AM_INST q) [0;1;2])
                     EN3_BASEMUL_DEFS) [0;1;2]);
    ALL_TAC];;

let EN3_TT_BOUND_TAC =
  SUBGOAL_THEN `!m. m < 768 ==> abs(ival((TT:num->int16) m)) <= &2 pow 12`
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

let EN3_V0_GOAL = `!p. p < 128
       ==> (ival((V0:num->int16)(2 * p)) ==
            &169 *
            ((ival((TT:num->int16)(512 + 2 * p + 1)) *
              ival((MC:num->int16)(256 + p)) +
              ival(TT(512 + 2 * p)) * ival((YH:num->int16)(512 + 2 * p))) +
             (ival(TT(256 + 2 * p + 1)) * ival(MC(128 + p)) +
              ival(TT(256 + 2 * p)) * ival(YH(256 + 2 * p))) +
             (ival(TT(2 * p + 1)) * ival(MC p) +
              ival(TT(2 * p)) * ival(YH(2 * p))))) (mod &3329) /\
           (ival(V0(2 * p + 1)) ==
            &169 *
            ((ival(TT(512 + 2 * p + 1)) * ival(YH(512 + 2 * p)) +
              ival(TT(512 + 2 * p)) * ival(YH(512 + 2 * p + 1))) +
             (ival(TT(256 + 2 * p + 1)) * ival(YH(256 + 2 * p)) +
              ival(TT(256 + 2 * p)) * ival(YH(256 + 2 * p + 1))) +
             (ival(TT(2 * p + 1)) * ival(YH(2 * p)) +
              ival(TT(2 * p)) * ival(YH(2 * p + 1))))) (mod &3329)`;;

let EN3_V0_TAC b s =
  INDCPA_GHOST_TAC "V0" (b + 1824) 256 s THEN
  SUBGOAL_THEN EN3_V0_GOAL ASSUME_TAC THENL
   [INDCPA_BASEMUL3_ROW_TAC "V0" (b + 1824) "ttbound" [] EN3_BASEMUL_DEFS;
    ALL_TAC];;

let EN3_COMPRESS_POST_TAC v y =
  let vt = mk_var(v,`:num->int16`) in
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    is_imp(concl th) && mem vt (frees(concl th)) &&
    INDCPA_HAS_CONST "nsum" (concl th))) THEN
  ANTS_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC VAL_LT_OF_IVAL_REM THEN EXISTS_TAC y THEN ASM_SIMP_TAC[];
    DISCH_TAC];;

let EN3_FINAL_TAC =
  REWRITE_TAC[ARITH_RULE `1088 = 960 + 128`; READ_COMPONENT_COMPOSE;
              READ_BYTES_COMBINE] THEN
  REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`ek:byte list`; `msg:byte list`; `r:byte list`;
                `TT:num->int16`; `YH:num->int16`; `MC:num->int16`;
                `E1:num->int16`; `E2:num->int16`; `MU:num->int16`;
                `U0:num->int16`; `V0:num->int16`; `U1:num->int16`;
                `V1:num->int16`; `U3:num->int16`; `V4:num->int16`]
          (REWRITE_RULE[ASSUME `mlkem_slice 1152 32 ek = rho`]
            KPKE_ENCRYPT_K3_RESULT)) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN
    FIRST [ASM_REWRITE_TAC[] THEN NO_TAC;
           REPEAT STRIP_TAC THEN ASM_SIMP_TAC[]];
    SIMP_TAC[]];;

(* ------------------------------------------------------------------------- *)
(* Correctness proof, assuming the contracts for memset and memcpy (the      *)
(* latter for the callees). The encryption key ek of 1184 bytes is at pk,    *)
(* the message msg of 32 bytes at m and the randomness r of 32 bytes at      *)
(* coins, and the ciphertext of 1088 bytes written at c is that of           *)
(* kpke_encrypt mlkem768 ek msg r in common/fips203/fips203.ml, for any ek   *)
(* (FIPS 203 decodes t modulo q, while the code multiplies by the 12-bit     *)
(* fields, which are congruent). The theorem assumes that SampleNTT          *)
(* terminates for each entry of the matrix, as for mlkem768_gen_matrix, and  *)
(* that the stack does not contain address 0. The stack is the 13264 bytes   *)
(* of the function and the 3632 used by mlkem768_gen_matrix below them. The  *)
(* proof is by cases on whether the stack pointer is a multiple of 32, which *)
(* gives the address b of the buffers, at offsets 0 (the matrix), 4608 (u),  *)
(* 6144 (e1), 7680 (t), 9216 (y), 10752 (its multiplication cache), 11520    *)
(* (e2), 12032 (the message), 12544 (v) and 13056 (rho).                     *)
(* ------------------------------------------------------------------------- *)

let EN3_INTRO_TAC =
  MAP_EVERY X_GEN_TAC
   [`c:int64`; `m:int64`; `pk:int64`; `coins:int64`; `ek:byte list`;
    `msg:byte list`; `r:byte list`; `guard:int64`; `mf:int64`; `mc:int64`;
    `ea:int64`; `el:num`; `ev:num`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 17024 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE] THEN
  REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NONOVERLAPPING_CLAUSES]) THEN
  SUBGOAL_THEN `aligned 16 (stackpointer:int64)` ASSUME_TAC THENL
   [UNDISCH_TAC `aligned 16 (word_add stackpointer (word 17024):int64)` THEN
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
   `!i j. i < 3 /\ j < 3
          ==> mlkem_samplentt_terminates
               (APPEND (mlkem_slice 1152 32 ek) [word j; word i])` THEN
  ABBREV_TAC `rho = mlkem_slice 1152 32 ek` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`3`; `\i j. APPEND (rho:byte list) [word j; word (i:num)]`]
                MLKEM_SAMPLENTT_TERMINATES_UNIFORM) THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `k:num`) THEN
  SUBGOAL_THEN
   `!i j. i < 3 /\ j < 3
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

let EN3_SEED_TAC b s =
  MP_TAC(SPECL [INDCPA_SP(b + 13088); `num_of_bytelist rho`;
                mk_var(s,`:armstate`)] GENMAT_BYTES_32_OF_HALVES) THEN
  ANTS_TAC THENL
   [CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `rho:byte list` NUM_OF_BYTELIST_BOUND) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];
    DISCH_TAC];;


let EN3_CASE_TAC b =
  ENSURES_INIT_TAC "s0" THEN
  EN3_PK_TAC THEN
  ARM_STEPS_TAC EN3_EXEC (1--10) THEN
  EN3_BUFFER_TAC THEN
  ARM_STEPS_TAC EN3_EXEC (11--11) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC EN3_EXEC (12--24) THEN
  LOCAL_POLYVEC_FROMBYTES_TAC
   [`read X0 s`; `read X1 s`; `num_of_bytelist ek MOD 2 EXP (8 * 1152)`;
    `pc:num`; `read SP s`; `read X30 s`] 25 THEN
  EN3_TT_TAC b "s25" THEN
  ARM_STEPS_TAC EN3_EXEC (26--33) THEN
  LOCAL_POLY_FROMMSG_TAC
   [`read X0 s`; `read X1 s`; `num_of_bytelist msg`; `pc:num`;
    `read X30 s`] 34 THEN
  EN3_MU_TAC b "s34" THEN
  EN3_SEED_TAC b "s34" THEN
  ARM_STEPS_TAC EN3_EXEC (35--41) THEN
  INDCPA_GOT_TAC THEN
  ARM_STEPS_TAC EN3_EXEC [42] THEN
  LOCAL_GEN_MATRIX_TAC
   [`read X0 s`; `read X1 s`; `rho:byte list`; `k:num`; `guard:int64`;
    `mf:int64`; `ea:int64`; `el:num`; `ev:num`; `pc:num`; `read SP s`;
    `read X30 s`] 43 THEN
  INDCPA_GHOST_TAC "AM" (b + 8480) 2304 "s43" THEN
  EN3_MATRIX_TAC (b + 8480) `s43:armstate` THEN
  ARM_STEPS_TAC EN3_EXEC (44--56) THEN
  INDCPA_NONCE_TAC 255 THEN
  ARM_STEPS_TAC EN3_EXEC [57] THEN
  LOCAL_GETNOISE3_TAC
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X4 s`;
    `r:byte list`; `read X5 s`; `read X6 s`; `read X7 s`;
    `word 255:int64`; `guard:int64`; `mf:int64`; `mc:int64`; `ea:int64`;
    `el:num`; `ev:num`; `pc:num`; `read SP s`; `read X30 s`] 58 THEN
  INDCPA_NOISE_TAC "YS" (b + 6944) 3 "r" "word j" "s58" THEN
  INDCPA_DISCARD_LETS_TAC THEN
  ARM_STEPS_TAC EN3_EXEC (59--70) THEN
  INDCPA_NONZERO_TAC 17024 (b + 800) THEN INDCPA_NONCE_TAC 6 THEN
  ARM_STEPS_TAC EN3_EXEC [71] THEN
  LOCAL_GETNOISE4_TAC
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X3 s`; `read X4 s`;
    `r:byte list`; `read X5 s`; `read X6 s`; `read X7 s`;
    `word 6:int64`; `guard:int64`; `mf:int64`; `mc:int64`; `ea:int64`;
    `el:num`; `ev:num`; `pc:num`; `read SP s`; `read X30 s`] 72 THEN
  INDCPA_NOISE_TAC "E1" (b + 3872) 3 "r" "word(3 + j)" "s72" THEN
  INDCPA_NOISE1_TAC "E2" (b + 800) "r" "word 6" "s72" THEN
  INDCPA_DISCARD_LETS_TAC THEN
  ARM_STEPS_TAC EN3_EXEC (73--75) THEN
  LOCAL_POLYVEC_NTT_TAC
   [`read X0 s`; `YS:num->int16`; `pc:num`; `read SP s`; `read X30 s`] 76 THEN
  INDCPA_NTT_TAC "YH" (b + 6944) 3 "YS" "r" "word j" "s76" THEN
  ARM_STEPS_TAC EN3_EXEC (77--81) THEN
  LOCAL_POLYVEC_MULCACHE_TAC
   [`read X0 s`; `read X1 s`; `YH:num->int16`; `pc:num`; `read SP s`;
    `read X30 s`] 82 THEN
  INDCPA_MULCACHE_TAC "MC" (b + 32) 3 "YH" "s82" THEN
  ARM_STEPS_TAC EN3_EXEC (83--90) THEN
  INDCPA_BASEMULK_PRE_TAC 3 (b + 8480,"AM",0) (b + 6944,"YH") (b + 32,"MC") "s90" THEN
  LOCAL_BASEMUL_TAC (INDCPA_BASEMULK_ARGS 3 ("AM",256 * 3 * 0) "YH" "MC") 91 THEN
  INDCPA_BASEMULK_DROP_PRE_TAC 3 (b + 8480,"AM",0) (b + 6944,"YH") (b + 32,"MC") THEN
  ARM_STEPS_TAC EN3_EXEC (92--97) THEN
  INDCPA_BASEMULK_PRE_TAC 3 (b + 10016,"AM",768) (b + 6944,"YH") (b + 32,"MC") "s97" THEN
  LOCAL_BASEMUL_TAC (INDCPA_BASEMULK_ARGS 3 ("AM",256 * 3 * 1) "YH" "MC") 98 THEN
  INDCPA_BASEMULK_DROP_PRE_TAC 3 (b + 10016,"AM",768) (b + 6944,"YH") (b + 32,"MC") THEN
  ARM_STEPS_TAC EN3_EXEC (99--104) THEN
  INDCPA_BASEMULK_PRE_TAC 3 (b + 11552,"AM",1536) (b + 6944,"YH") (b + 32,"MC") "s104" THEN
  LOCAL_BASEMUL_TAC (INDCPA_BASEMULK_ARGS 3 ("AM",256 * 3 * 2) "YH" "MC") 105 THEN
  INDCPA_BASEMULK_DROP_PRE_TAC 3 (b + 11552,"AM",1536) (b + 6944,"YH") (b + 32,"MC") THEN
  EN3_AM_BOUND_TAC THEN
  EN3_U0_TAC b "s105" THEN
  ARM_STEPS_TAC EN3_EXEC (106--113) THEN
  INDCPA_BASEMULK_PRE_TAC 3 (b + 5408,"TT",0) (b + 6944,"YH") (b + 32,"MC") "s113" THEN
  LOCAL_BASEMUL_TAC (INDCPA_BASEMULK_ARGS 3 ("TT",0) "YH" "MC") 114 THEN
  INDCPA_BASEMULK_DROP_PRE_TAC 3 (b + 5408,"TT",0) (b + 6944,"YH") (b + 32,"MC") THEN
  EN3_TT_BOUND_TAC THEN
  EN3_V0_TAC b "s114" THEN
  ARM_STEPS_TAC EN3_EXEC (115--116) THEN
  LOCAL_POLYVEC_INVNTT_TAC
   [`read X0 s`; `U0:num->int16`; `pc:num`; `read SP s`; `read X30 s`] 117 THEN
  INDCPA_INVNTT_TAC "U1" (b + 2336) 3 "U0" "s117" THEN
  ARM_STEPS_TAC EN3_EXEC (118--119) THEN
  LOCAL_POLY_INVNTT_TAC
   [`read X0 s`; `V0:num->int16`; `pc:num`; `read SP s`; `read X30 s`] 120 THEN
  INDCPA_INVNTT1_TAC "V1" (b + 1824) "V0" "s120" THEN
  ARM_STEPS_TAC EN3_EXEC (121--123) THEN
  LOCAL_POLYVEC_ADD_TAC
   [`read X0 s`; `read X1 s`; `U1:num->int16`; `E1:num->int16`; `pc:num`;
    `read SP s`; `read X30 s`] 124 THEN
  ARM_STEPS_TAC EN3_EXEC (125--127) THEN
  LOCAL_POLY_ADD_TAC
   [`read X0 s`; `read X1 s`; `V1:num->int16`; `E2:num->int16`; `pc:num`;
    `read X30 s`] 128 THEN
  ARM_STEPS_TAC EN3_EXEC (129--131) THEN
  LOCAL_POLY_ADD_TAC
   [`read X0 s`; `read X1 s`;
    `\i. word_add ((V1:num->int16) i) ((E2:num->int16) i)`;
    `MU:num->int16`; `pc:num`; `read X30 s`] 132 THEN
  ARM_STEPS_TAC EN3_EXEC (133--134) THEN
  LOCAL_POLYVEC_REDUCE_TAC
   [`read X0 s`; `\i. word_add ((U1:num->int16) i) ((E1:num->int16) i)`;
    `pc:num`; `read SP s`; `read X30 s`] 135 THEN
  INDCPA_REDUCE_TAC "U3" (b + 2336) 768
    "word_add ((U1:num->int16) i) ((E1:num->int16) i)" "s135" THEN
  ARM_STEPS_TAC EN3_EXEC (136--137) THEN
  LOCAL_POLY_REDUCE_TAC
   [`read X0 s`;
    `\i. word_add (word_add ((V1:num->int16) i) ((E2:num->int16) i))
                  ((MU:num->int16) i)`;
    `pc:num`; `read X30 s`] 138 THEN
  INDCPA_REDUCE_TAC "V4" (b + 1824) 256
    "word_add (word_add ((V1:num->int16) i) ((E2:num->int16) i)) \
     ((MU:num->int16) i)" "s138" THEN
  ARM_STEPS_TAC EN3_EXEC (139--140) THEN
  INDCPA_GOT_TAC THEN
  ARM_STEPS_TAC EN3_EXEC [141] THEN
  LOCAL_POLYVEC_COMPRESS_DU_TAC
   [`read X0 s`; `read X1 s`; `U3:num->int16`; `guard:int64`; `pc:num`;
    `read SP s`; `read X30 s`] 142 THEN
  EN3_COMPRESS_POST_TAC "U3"
   `ival(word_add ((U1:num->int16) i) ((E1:num->int16) i))` THEN
  ARM_STEPS_TAC EN3_EXEC (143--145) THEN
  LOCAL_POLY_COMPRESS_D4_TAC
   [`read X0 s`; `read X1 s`; `V4:num->int16`; `pc:num`;
    `read SP s`; `read X30 s`] 146 THEN
  EN3_COMPRESS_POST_TAC "V4"
   `ival(word_add (word_add ((V1:num->int16) i) ((E2:num->int16) i))
                  ((MU:num->int16) i))` THEN
  INDCPA_MEMSET_LABEL_TAC THEN
  INDCPA_MEMSETS_TAC EN3_EXEC
   [147,150; 156,249; 255,258; 264,268; 274,278; 284,288] THEN
  ARM_STEPS_TAC EN3_EXEC (294--299) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC EN3_EXEC (300--313) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN EN3_FINAL_TAC;;

let MLKEM_NATIVE_INDCPA_ENC_K3_CLANG17_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!c m pk coins (ek:byte list) (msg:byte list) (r:byte list)
    guard mf mc ea el ev pc stackpointer returnaddress.
        memset_contract mf ea el ev /\ memcpy_contract mc ea el ev /\
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        LENGTH ek = 1184 /\ LENGTH msg = 32 /\ LENGTH r = 32 /\
        (!i j. i < 3 /\ j < 3
               ==> mlkem_samplentt_terminates
                    (APPEND (mlkem_slice 1152 32 ek) [word j; word i])) /\
        nonoverlapping (word 0,1) (word_sub stackpointer (word 17024),17024) /\
        nonoverlapping (c,1088) (word_sub stackpointer (word 17024),17024) /\
        nonoverlapping (pk,1184) (word pc,libmlkem_size) /\
        ALLPAIRS nonoverlapping
         [(c,1088); (word_sub stackpointer (word 17024),17024)]
         [(m,32); (pk,1184); (coins,32); (word pc,libmlkem_size);
          (word(pc + got_stack_chk_guard),8); (guard,8);
          (word(pc + got_memset),8);
          (word(pc + got_memcpy),8); (ea,el)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_clang17_O2_mc /\
                  read PC s = word (pc + mlkem768_indcpa_enc) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [c; m; pk; coins] s /\
                  read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                    guard /\
                  read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                  read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                  read (memory :> bytes(ea,el)) s = ev /\
                  read (memory :> bytes(m,32)) s = num_of_bytelist msg /\
                  read (memory :> bytes(pk,1184)) s = num_of_bytelist ek /\
                  read (memory :> bytes(coins,32)) s = num_of_bytelist r)
             (\s. read PC s = returnaddress /\
                  read (memory :> bytes(c,1088)) s =
                  num_of_bytelist(kpke_encrypt mlkem768 ek msg r) /\
                  C_RETURN s = word 0)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
              MAYCHANGE
               [memory :> bytes(c,1088);
                memory :> bytes(word_sub stackpointer (word 17024),17024)])`;;

let MLKEM_NATIVE_INDCPA_ENC_K3_CLANG17_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_INDCPA_ENC_K3_CLANG17_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof, assuming the combined contract for *)
(* memset (for mlkem768_gen_matrix) and the safety contract for memcpy. The  *)
(* events depend only on the addresses and on rho, the last 32 bytes of the  *)
(* public key, through the samples of SampleNTT for the transposed matrix,   *)
(* but not on the message or the randomness. As for the correctness proof,   *)
(* the proof is by cases on whether the stack pointer is a multiple of 32,   *)
(* with the events in the two cases as the two branches of the template.     *)
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

let EN3_SAFE_INTRO_TAC =
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
  FIRST_X_ASSUM(fun th ->
    if can (term_match [] `memset_full_contract mf ea el ev`) (concl th)
    then ASSUME_CALLEE_SAFETY_TAILED_TAC
          (INDCPA_GEN_MATRIX_SAFE_SPEC
            (MATCH_MP MLKEM_NATIVE_GEN_MATRIX_K3_CLANG17_O2_IMAGE_SUBROUTINE_SAFE
                      th) `word 1:int64`) "H_GM" THEN
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
        MLKEM_NATIVE_POLY_GETNOISE_ETA1_4X_K3_CLANG17_O2_IMAGE_SUBROUTINE_SAFE
        (CONJ th1 th2) in
      ASSUME_CALLEE_SAFETY_TAILED_TAC (INDCPA_GETNOISE_NULL_SAFE gth)
       "H_GETNOISE3" THEN
      ASSUME_CALLEE_SAFETY_TAILED_ALT_TAC gth "H_GETNOISE")
    else NO_TAC) THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_POLYVEC_FROMBYTES_K3_CLANG17_O2_IMAGE_SUBROUTINE_SAFE
    "H_FROMBYTES" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    (REWRITE_RULE[ALL]
      MLKEM_NATIVE_POLY_FROMMSG_CLANG17_O2_IMAGE_SUBROUTINE_SAFE)
    "H_FROMMSG" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_POLYVEC_NTT_K3_CLANG17_O2_IMAGE_SUBROUTINE_SAFE "H_NTT" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_POLYVEC_MULCACHE_COMPUTE_K3_CLANG17_O2_IMAGE_SUBROUTINE_SAFE
    "H_MULCACHE" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_BASEMUL_K3_CLANG17_O2_IMAGE_SUBROUTINE_SAFE "H_BASEMUL" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_POLYVEC_INVNTT_TOMONT_K3_CLANG17_O2_IMAGE_SUBROUTINE_SAFE
    "H_INVNTT" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    (REWRITE_RULE[ALL]
      MLKEM_NATIVE_POLY_INVNTT_TOMONT_CLANG17_O2_IMAGE_SUBROUTINE_SAFE)
    "H_POLY_INVNTT" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_POLYVEC_ADD_K3_CLANG17_O2_IMAGE_SUBROUTINE_SAFE "H_ADD" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    (REWRITE_RULE[ALL]
      MLKEM_NATIVE_POLY_ADD_CLANG17_O2_IMAGE_SUBROUTINE_SAFE)
    "H_POLY_ADD" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_POLYVEC_REDUCE_K3_CLANG17_O2_IMAGE_SUBROUTINE_SAFE
    "H_REDUCE" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_POLY_REDUCE_CLANG17_O2_IMAGE_SUBROUTINE_SAFE
    "H_POLY_REDUCE" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_POLYVEC_COMPRESS_DU_K3_CLANG17_O2_IMAGE_SUBROUTINE_SAFE
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
   [UNDISCH_TAC `aligned 16 (word_add stackpointer (word 17024):int64)` THEN
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
   `!i j. i < 3 /\ j < 3
          ==> mlkem_samplentt_terminates
               (APPEND (mlkem_slice 1152 32 ek) [word j; word i])` THEN
  ABBREV_TAC `rho = mlkem_slice 1152 32 ek` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`3`; `\i j. APPEND (rho:byte list) [word j; word (i:num)]`]
                MLKEM_SAMPLENTT_TERMINATES_UNIFORM) THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `k:num`) THEN
  SUBGOAL_THEN
   `!i j. i < 3 /\ j < 3
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

let EN3_SAFE_CALL_TAC name ilist n =
  REMOVE_THEN name (fun safety_th ->
    ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_clang17_O2_mc,EN3_EXEC,
       0x0,mlkem_native_libmlkem_clang17_O2_mc,safety_th)
      ilist n THENL
     [EXISTS_E2_TAC (ref EN_SAFE_ALLOWED); LABEL_TAC name safety_th]);;

let EN3_SAFE_CASE_TAC b =
  let e = `e:(uarch_event)list` in
  let x n = mk_comb(mk_comb(`read:(armstate,int64)component->armstate->int64`,
                            mk_const("X"^string_of_int n,[])),`s:armstate`) in
  let rest = [`pc:num`; `read SP s`; `read X30 s`] in
  ENSURES_INIT_TAC "s0" THEN
  EN3_PK_TAC THEN
  ARM_STEPS_TAC EN3_EXEC (1--10) THEN
  EN3_BUFFER_TAC THEN
  ARM_STEPS_TAC EN3_EXEC (11--11) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC EN3_EXEC (12--24) THEN
  EN3_SAFE_CALL_TAC "H_FROMBYTES" ([e; x 0; x 1] @ rest) 25 THEN
  ARM_STEPS_TAC EN3_EXEC (26--33) THEN
  EN3_SAFE_CALL_TAC "H_FROMMSG" [e; x 0; x 1; `pc:num`; `read X30 s`] 34 THEN
  EN3_SEED_TAC b "s34" THEN
  ARM_STEPS_TAC EN3_EXEC (35--41) THEN
  INDCPA_GOT_TAC THEN
  ARM_STEPS_TAC EN3_EXEC [42] THEN
  EN3_SAFE_CALL_TAC "H_GM" ([e; x 0; x 1; `rho:byte list`; `k:num`; `guard:int64`] @ rest) 43 THEN
  ARM_STEPS_TAC EN3_EXEC (44--56) THEN
  INDCPA_NONCE_TAC 255 THEN
  ARM_STEPS_TAC EN3_EXEC [57] THEN
  EN3_SAFE_CALL_TAC "H_GETNOISE3" ([e; x 0; x 1; x 2; x 4; `guard:int64`] @ rest) 58 THEN
  ARM_STEPS_TAC EN3_EXEC (59--70) THEN
  INDCPA_NONZERO_TAC 17024 (b + 800) THEN INDCPA_NONCE_TAC 6 THEN
  ARM_STEPS_TAC EN3_EXEC [71] THEN
  EN3_SAFE_CALL_TAC "H_GETNOISE" ([e; x 0; x 1; x 2; x 3; x 4; `guard:int64`] @ rest) 72 THEN
  ARM_STEPS_TAC EN3_EXEC (73--75) THEN
  EN3_SAFE_CALL_TAC "H_NTT" ([e; x 0] @ rest) 76 THEN
  ARM_STEPS_TAC EN3_EXEC (77--81) THEN
  EN3_SAFE_CALL_TAC "H_MULCACHE" ([e; x 0; x 1] @ rest) 82 THEN
  ARM_STEPS_TAC EN3_EXEC (83--90) THEN
  EN3_SAFE_CALL_TAC "H_BASEMUL" [e; x 1; x 2; x 3; x 0; `pc:num`; `read X30 s`] 91 THEN
  ARM_STEPS_TAC EN3_EXEC (92--97) THEN
  EN3_SAFE_CALL_TAC "H_BASEMUL" [e; x 1; x 2; x 3; x 0; `pc:num`; `read X30 s`] 98 THEN
  ARM_STEPS_TAC EN3_EXEC (99--104) THEN
  EN3_SAFE_CALL_TAC "H_BASEMUL" [e; x 1; x 2; x 3; x 0; `pc:num`; `read X30 s`] 105 THEN
  ARM_STEPS_TAC EN3_EXEC (106--113) THEN
  EN3_SAFE_CALL_TAC "H_BASEMUL" [e; x 1; x 2; x 3; x 0; `pc:num`; `read X30 s`] 114 THEN
  ARM_STEPS_TAC EN3_EXEC (115--116) THEN
  EN3_SAFE_CALL_TAC "H_INVNTT" ([e; x 0] @ rest) 117 THEN
  ARM_STEPS_TAC EN3_EXEC (118--119) THEN
  EN3_SAFE_CALL_TAC "H_POLY_INVNTT" ([e; x 0] @ rest) 120 THEN
  ARM_STEPS_TAC EN3_EXEC (121--123) THEN
  EN3_SAFE_CALL_TAC "H_ADD" ([e; x 0; x 1] @ rest) 124 THEN
  ARM_STEPS_TAC EN3_EXEC (125--127) THEN
  EN3_SAFE_CALL_TAC "H_POLY_ADD" [e; x 0; x 1; `pc:num`; `read X30 s`] 128 THEN
  ARM_STEPS_TAC EN3_EXEC (129--131) THEN
  EN3_SAFE_CALL_TAC "H_POLY_ADD" [e; x 0; x 1; `pc:num`; `read X30 s`] 132 THEN
  ARM_STEPS_TAC EN3_EXEC (133--134) THEN
  EN3_SAFE_CALL_TAC "H_REDUCE" ([e; x 0] @ rest) 135 THEN
  ARM_STEPS_TAC EN3_EXEC (136--137) THEN
  EN3_SAFE_CALL_TAC "H_POLY_REDUCE" [e; x 0; `pc:num`; `read X30 s`] 138 THEN
  ARM_STEPS_TAC EN3_EXEC (139--140) THEN
  INDCPA_GOT_TAC THEN
  ARM_STEPS_TAC EN3_EXEC [141] THEN
  EN3_SAFE_CALL_TAC "H_COMPRESS_DU" ([e; x 0; x 1; `guard:int64`] @ rest) 142 THEN
  ARM_STEPS_TAC EN3_EXEC (143--145) THEN
  EN3_SAFE_CALL_TAC "H_COMPRESS_DV" ([e; x 0; x 1] @ rest) 146 THEN
  MAP_EVERY (fun (k0,k) ->
    ARM_STEPS_TAC EN3_EXEC (k0--k) THEN LIBC_PLT_TAC EN3_EXEC k THEN
    LIBC_SAFE_CALL_TAC "H_MEMSET" EN3_EXEC
     [e; x 0; x 1; x 2; `read X30 s`] (ref EN_SAFE_ALLOWED) (k + 5))
   [147,150; 156,249; 255,258; 264,268; 274,278; 284,288] THEN
  ARM_STEPS_TAC EN3_EXEC (294--299) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC EN3_EXEC (300--313) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN MEMACCESS_DROP_ZERO_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC;;

let MLKEM_NATIVE_INDCPA_ENC_K3_CLANG17_O2_IMAGE_SUBROUTINE_SAFE_STMT =
  `!mf mc ea el ev.
   memset_full_contract mf ea el ev /\ memcpy_safety_contract mc ea el ev
   ==> exists f_events.
        forall e c m pk coins (ek:byte list) guard pc stackpointer
               returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\ LENGTH ek = 1184 /\
          (!i j. i < 3 /\ j < 3
                 ==> mlkem_samplentt_terminates
                      (APPEND (mlkem_slice 1152 32 ek) [word j; word i])) /\
          nonoverlapping (word 0,1)
           (word_sub stackpointer (word 17024),17024) /\
          nonoverlapping (c,1088)
           (word_sub stackpointer (word 17024),17024) /\
          nonoverlapping (pk,1184) (word pc,libmlkem_size) /\
          ALLPAIRS nonoverlapping
           [(c,1088); (word_sub stackpointer (word 17024),17024)]
           [(m,32); (pk,1184); (coins,32); (word pc,libmlkem_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8);
            (word(pc + got_memcpy),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mlkem_native_libmlkem_clang17_O2_mc /\
                    read PC s = word (pc + mlkem768_indcpa_enc) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [c; m; pk; coins] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s
                     = guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(pk,1184)) s = num_of_bytelist ek /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    C_RETURN s = word 0 /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events c m pk coins guard mf mc pc
                              (word_sub stackpointer (word 17024))
                              returnaddress (mlkem_slice 1152 32 ek) /\
                       memaccess_inbounds e2
                        [m,32; pk,1184; coins,32; c,1088;
                         word_sub stackpointer (word 17024),17024;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8;
                         word(pc + got_memcpy),8; ea,el;
                         word(pc + rodata_mlk_KeccakF_RoundConstants),192;
                         word(pc + mlkem_poly_cbd2_consts),
                         mlkem_poly_cbd2_consts_size;
                         word(pc + rodata_mlk_zetas),256;
                         word(pc + mlkem_poly_mulcache_compute_consts),
                         mlkem_poly_mulcache_compute_consts_size;
                         word(pc + mlkem_poly_compress_d4_consts),
                         mlkem_poly_compress_d4_consts_size]
                        [c,1088; word_sub stackpointer (word 17024),17024]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(c,1088);
                  memory :> bytes(word_sub stackpointer (word 17024),17024)])`;;

let MLKEM_NATIVE_INDCPA_ENC_K3_CLANG17_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_INDCPA_ENC_K3_CLANG17_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
