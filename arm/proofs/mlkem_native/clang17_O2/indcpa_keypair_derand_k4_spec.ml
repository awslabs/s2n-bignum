(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The key generation of K-PKE for ML-KEM-1024 (FIPS 203 Algorithm 13).    *)
(* This is the code for mlkem1024_indcpa_keypair_derand from mlkem-        *)
(* native's portable C implementation compiled by clang 17 with -O2 (see   *)
(* mlkem_native/README.md). It hashes the 32-byte seed d followed by the   *)
(* byte 4 with SHA3-512 into the seeds rho and sigma, generates the matrix *)
(* in NTT form from rho (mlkem1024_gen_matrix is inlined: the code copies  *)
(* rho with the indices of the four entries of a row into four buffers of  *)
(* 64 bytes and calls mlkem_poly_rej_uniform_x4 once per row), samples the *)
(* secret s and the error e from sigma and transforms them, computes t = A *)
(* s + e in the NTT domain (one call of                                    *)
(* mlkem1024_polyvec_basemul_acc_montgomery_cached per row of A), and      *)
(* writes the encoding of t followed by rho as the public key and the      *)
(* encoding of s as the secret key, zeroing its buffers. The buffers are   *)
(* 32-byte aligned within the stack frame, which the code makes by         *)
(* rounding the stack pointer down, so the proof is by cases on whether    *)
(* the incoming stack pointer is a multiple of 32. It is verified in the   *)
(* whole image (see libmlkem.ml), using the theorems for mlkem_sha3_512,   *)
(* mlkem_poly_rej_uniform_x4, mlkem1024_poly_getnoise_eta1_4x,             *)
(* mlkem1024_polyvec_ntt, mlkem1024_polyvec_mulcache_compute,              *)
(* mlkem1024_polyvec_basemul_acc_montgomery_cached,                        *)
(* mlkem1024_polyvec_tomont, mlkem1024_polyvec_add,                        *)
(* mlkem1024_polyvec_reduce and mlkem1024_polyvec_tobytes in the image,    *)
(* and the contract for memset.                                            *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/mlkem_native/clang17_O2/sha3_512_spec.ml";;
needs "arm/proofs/mlkem_native/clang17_O2/poly_rej_uniform_x4_spec.ml";;
needs "arm/proofs/mlkem_native/clang17_O2/gen_matrix_k4_spec.ml";;
needs "arm/proofs/mlkem_native/clang17_O2/poly_getnoise_eta1_4x_k4_spec.ml";;
needs "arm/proofs/mlkem_native/clang17_O2/polyvec_ntt_k4_spec.ml";;
needs "arm/proofs/mlkem_native/clang17_O2/polyvec_mulcache_compute_k4_spec.ml";;
needs "arm/proofs/mlkem_native/clang17_O2/basemul_k4_spec.ml";;
needs "arm/proofs/mlkem_native/clang17_O2/polyvec_tomont_k4_spec.ml";;
needs "arm/proofs/mlkem_native/clang17_O2/polyvec_add_k4_spec.ml";;
needs "arm/proofs/mlkem_native/clang17_O2/polyvec_reduce_k4_spec.ml";;
needs "arm/proofs/mlkem_native/clang17_O2/polyvec_tobytes_k4_spec.ml";;
needs "arm/proofs/utils/mlkem_native_indcpa.ml";;

(*** The code in the image:

    mlkem1024_indcpa_keypair_derand:
       +0x0: stp     x29, x30, [sp, #-96]!
       +0x4: stp     x28, x27, [sp, #16]
       +0x8: stp     x26, x25, [sp, #32]
       +0xc: stp     x24, x23, [sp, #48]
      +0x10: stp     x22, x21, [sp, #64]
      +0x14: stp     x20, x19, [sp, #80]
      +0x18: mov     x29, sp
      +0x1c: sub     x9, sp, #0x3, lsl #12
      +0x20: sub     x9, x9, #0xcc0
      +0x24: and     sp, x9, #0xffffffffffffffe0
      +0x28: adrp    x8, <page>
      +0x2c: mov     x20, x1
      +0x30: mov     x19, x0
      +0x34: add     x9, sp, #0x3, lsl #12
      +0x38: add     x0, sp, #0x3, lsl #12
      +0x3c: add     x1, sp, #0x3, lsl #12
      +0x40: ldr     x8, [x8, #4088]
      +0x44: add     x9, x9, #0xc20
      +0x48: add     x0, x0, #0xc60
      +0x4c: add     x1, x1, #0xc20
      +0x50: add     x24, sp, #0x3, lsl #12
      +0x54: ldr     x8, [x8]
      +0x58: add     x24, x24, #0xc60
      +0x5c: str     x8, [sp, #15544]
      +0x60: mov     w8, #0x4
      +0x64: ldp     q0, q1, [x2]
      +0x68: mov     w2, #0x21
      +0x6c: strb    w8, [x9, #32]
      +0x70: str     q0, [sp, #15392]
      +0x74: str     q1, [sp, #15408]
      +0x78: bl      <mlkem_sha3_512>
      +0x7c: add     x28, sp, #0x1, lsl #12
      +0x80: add     x0, sp, #0x1, lsl #12
      +0x84: add     x28, x28, #0xc20
      +0x88: add     x4, sp, #0x1, lsl #12
      +0x8c: ldr     q0, [sp, #15456]
      +0x90: mov     w8, #0x1
      +0x94: ldr     q1, [sp, #15472]
      +0x98: mov     w9, #0x2
      +0x9c: mov     w26, #0x3
      +0xa0: add     x1, x28, #0x200
      +0xa4: add     x2, x28, #0x400
      +0xa8: add     x3, x28, #0x600
      +0xac: add     x0, x0, #0xc20
      +0xb0: add     x4, x4, #0x420
      +0xb4: add     x27, sp, #0x1, lsl #12
      +0xb8: str     q0, [sp, #5152]
      +0xbc: str     q1, [sp, #5168]
      +0xc0: add     x27, x27, #0x420
      +0xc4: str     q0, [sp, #5216]
      +0xc8: str     q1, [sp, #5232]
      +0xcc: str     q0, [sp, #5280]
      +0xd0: str     q1, [sp, #5296]
      +0xd4: str     q1, [sp, #5360]
      +0xd8: str     q0, [sp, #5344]
      +0xdc: strh    w8, [sp, #5248]
      +0xe0: strh    w9, [sp, #5312]
      +0xe4: strh    wzr, [sp, #5184]
      +0xe8: strh    w26, [sp, #5376]
      +0xec: bl      <mlkem_poly_rej_uniform_x4>
      +0xf0: add     x21, x28, #0x800
      +0xf4: add     x4, sp, #0x1, lsl #12
      +0xf8: mov     w8, #0x100
      +0xfc: mov     w9, #0x101
     +0x100: mov     w10, #0x102
     +0x104: mov     w11, #0x103
     +0x108: add     x1, x28, #0xa00
     +0x10c: add     x2, x28, #0xc00
     +0x110: add     x3, x28, #0xe00
     +0x114: add     x4, x4, #0x420
     +0x118: mov     x0, x21
     +0x11c: strh    w8, [sp, #5184]
     +0x120: strh    w9, [sp, #5248]
     +0x124: strh    w10, [sp, #5312]
     +0x128: strh    w11, [sp, #5376]
     +0x12c: bl      <mlkem_poly_rej_uniform_x4>
     +0x130: mov     w8, #0x200
     +0x134: mov     w9, #0x201
     +0x138: add     x22, x28, #0x1, lsl #12
     +0x13c: mov     w12, #0x1200
     +0x140: add     x4, sp, #0x1, lsl #12
     +0x144: mov     w10, #0x202
     +0x148: strh    w8, [sp, #5184]
     +0x14c: mov     w8, #0x1400
     +0x150: strh    w9, [sp, #5248]
     +0x154: mov     w9, #0x1600
     +0x158: mov     w11, #0x203
     +0x15c: add     x1, x28, x12
     +0x160: add     x2, x28, x8
     +0x164: add     x3, x28, x9
     +0x168: add     x4, x4, #0x420
     +0x16c: mov     x0, x22
     +0x170: strh    w10, [sp, #5312]
     +0x174: strh    w11, [sp, #5376]
     +0x178: bl      <mlkem_poly_rej_uniform_x4>
     +0x17c: mov     w8, #0x300
     +0x180: mov     w9, #0x301
     +0x184: mov     w12, #0x1800
     +0x188: add     x4, sp, #0x1, lsl #12
     +0x18c: add     x23, x28, x12
     +0x190: mov     w10, #0x302
     +0x194: strh    w8, [sp, #5184]
     +0x198: mov     w8, #0x1a00
     +0x19c: strh    w9, [sp, #5248]
     +0x1a0: add     x1, x28, x8
     +0x1a4: mov     w8, #0x1c00
     +0x1a8: mov     w9, #0x1e00
     +0x1ac: mov     w11, #0x303
     +0x1b0: add     x2, x28, x8
     +0x1b4: add     x3, x28, x9
     +0x1b8: add     x4, x4, #0x420
     +0x1bc: mov     x0, x23
     +0x1c0: strh    w10, [sp, #5312]
     +0x1c4: strh    w11, [sp, #5376]
     +0x1c8: bl      <mlkem_poly_rej_uniform_x4>
     +0x1cc: movi    v0.2d, #0x0
     +0x1d0: add     x24, x24, #0x20
     +0x1d4: add     x25, sp, #0x420
     +0x1d8: add     x0, sp, #0x420
     +0x1dc: add     x1, x25, #0x200
     +0x1e0: add     x2, x25, #0x400
     +0x1e4: add     x3, x25, #0x600
     +0x1e8: mov     x4, x24
     +0x1ec: str     q0, [sp, #5392]
     +0x1f0: mov     w5, wzr
     +0x1f4: str     q0, [sp, #5376]
     +0x1f8: mov     w6, #0x1
     +0x1fc: str     q0, [sp, #5360]
     +0x200: mov     w7, #0x2
     +0x204: str     q0, [sp, #5344]
     +0x208: str     q0, [sp, #5328]
     +0x20c: str     q0, [sp, #5312]
     +0x210: str     q0, [sp, #5296]
     +0x214: str     q0, [sp, #5280]
     +0x218: str     q0, [sp, #5264]
     +0x21c: str     q0, [sp, #5248]
     +0x220: str     q0, [sp, #5232]
     +0x224: str     q0, [sp, #5216]
     +0x228: str     q0, [sp, #5200]
     +0x22c: str     q0, [sp, #5184]
     +0x230: str     q0, [sp, #5168]
     +0x234: str     q0, [sp, #5152]
     +0x238: strb    w26, [sp]
     +0x23c: bl      <mlkem1024_poly_getnoise_eta1_4x>
     +0x240: add     x0, sp, #0x1, lsl #12
     +0x244: add     x1, x27, #0x200
     +0x248: add     x2, x27, #0x400
     +0x24c: add     x3, x27, #0x600
     +0x250: mov     w8, #0x7
     +0x254: add     x0, x0, #0x420
     +0x258: mov     x4, x24
     +0x25c: mov     w5, #0x4
     +0x260: mov     w6, #0x5
     +0x264: mov     w7, #0x6
     +0x268: strb    w8, [sp]
     +0x26c: bl      <mlkem1024_poly_getnoise_eta1_4x>
     +0x270: add     x0, sp, #0x420
     +0x274: bl      <mlkem1024_polyvec_ntt>
     +0x278: add     x0, sp, #0x1, lsl #12
     +0x27c: add     x0, x0, #0x420
     +0x280: bl      <mlkem1024_polyvec_ntt>
     +0x284: add     x0, sp, #0x20
     +0x288: add     x1, sp, #0x420
     +0x28c: add     x26, sp, #0x20
     +0x290: bl      <mlkem1024_polyvec_mulcache_compute>
     +0x294: add     x1, sp, #0x1, lsl #12
     +0x298: add     x0, sp, #0xc20
     +0x29c: add     x1, x1, #0xc20
     +0x2a0: add     x2, sp, #0x420
     +0x2a4: add     x3, sp, #0x20
     +0x2a8: add     x24, sp, #0xc20
     +0x2ac: bl      <mlkem1024_polyvec_basemul_acc_montgomery_cached>
     +0x2b0: add     x0, x24, #0x200
     +0x2b4: add     x2, sp, #0x420
     +0x2b8: add     x3, sp, #0x20
     +0x2bc: mov     x1, x21
     +0x2c0: bl      <mlkem1024_polyvec_basemul_acc_montgomery_cached>
     +0x2c4: add     x0, x24, #0x400
     +0x2c8: add     x2, sp, #0x420
     +0x2cc: add     x3, sp, #0x20
     +0x2d0: mov     x1, x22
     +0x2d4: bl      <mlkem1024_polyvec_basemul_acc_montgomery_cached>
     +0x2d8: add     x0, x24, #0x600
     +0x2dc: add     x2, sp, #0x420
     +0x2e0: add     x3, sp, #0x20
     +0x2e4: mov     x1, x23
     +0x2e8: bl      <mlkem1024_polyvec_basemul_acc_montgomery_cached>
     +0x2ec: add     x0, sp, #0xc20
     +0x2f0: bl      <mlkem1024_polyvec_tomont>
     +0x2f4: add     x1, sp, #0x1, lsl #12
     +0x2f8: add     x0, sp, #0xc20
     +0x2fc: add     x1, x1, #0x420
     +0x300: bl      <mlkem1024_polyvec_add>
     +0x304: add     x0, sp, #0xc20
     +0x308: bl      <mlkem1024_polyvec_reduce>
     +0x30c: add     x0, sp, #0x420
     +0x310: bl      <mlkem1024_polyvec_reduce>
     +0x314: add     x1, sp, #0x420
     +0x318: mov     x0, x20
     +0x31c: bl      <mlkem1024_polyvec_tobytes>
     +0x320: add     x1, sp, #0xc20
     +0x324: mov     x0, x19
     +0x328: bl      <mlkem1024_polyvec_tobytes>
     +0x32c: ldr     q0, [sp, #15456]
     +0x330: add     x0, sp, #0x20
     +0x334: ldr     q1, [sp, #15472]
     +0x338: mov     w1, wzr
     +0x33c: mov     w2, #0x400
     +0x340: str     q0, [x19, #1536]
     +0x344: str     q1, [x19, #1552]
     +0x348: bl      <memset@plt>
     +0x34c: add     x0, sp, #0x420
     +0x350: mov     w1, wzr
     +0x354: mov     w2, #0x800
     +0x358: bl      <memset@plt>
     +0x35c: add     x0, sp, #0xc20
     +0x360: mov     w1, wzr
     +0x364: mov     w2, #0x800
     +0x368: bl      <memset@plt>
     +0x36c: add     x0, sp, #0x1, lsl #12
     +0x370: add     x0, x0, #0x420
     +0x374: mov     w1, wzr
     +0x378: mov     w2, #0x800
     +0x37c: bl      <memset@plt>
     +0x380: add     x0, sp, #0x1, lsl #12
     +0x384: add     x0, x0, #0xc20
     +0x388: mov     w1, wzr
     +0x38c: mov     w2, #0x2000
     +0x390: bl      <memset@plt>
     +0x394: add     x8, sp, #0x3, lsl #12
     +0x398: add     x8, x8, #0xc20
     +0x39c: movi    v0.2d, #0x0
     +0x3a0: strb    wzr, [x8, #32]
     +0x3a4: add     x8, sp, #0x3, lsl #12
     +0x3a8: add     x8, x8, #0xc20
     +0x3ac: str     q0, [sp, #15408]
     +0x3b0: str     q0, [sp, #15392]
     +0x3b4: add     x8, sp, #0x3, lsl #12
     +0x3b8: str     q0, [sp, #15504]
     +0x3bc: add     x8, x8, #0xc60
     +0x3c0: str     q0, [sp, #15488]
     +0x3c4: str     q0, [sp, #15472]
     +0x3c8: str     q0, [sp, #15456]
     +0x3cc: adrp    x8, <page>
     +0x3d0: ldr     x8, [x8, #4088]
     +0x3d4: ldr     x9, [sp, #15544]
     +0x3d8: ldr     x8, [x8]
     +0x3dc: cmp     x8, x9
     +0x3e0: b.ne    <mlkem1024_indcpa_keypair_derand+0x408>
     +0x3e4: mov     w0, wzr
     +0x3e8: mov     sp, x29
     +0x3ec: ldp     x20, x19, [sp, #80]
     +0x3f0: ldp     x22, x21, [sp, #64]
     +0x3f4: ldp     x24, x23, [sp, #48]
     +0x3f8: ldp     x26, x25, [sp, #32]
     +0x3fc: ldp     x28, x27, [sp, #16]
     +0x400: ldp     x29, x30, [sp], #96
     +0x404: ret
     +0x408: bl      <__stack_chk_fail@plt>
 ***)

let MLKEM_NATIVE_INDCPA_KEYPAIR_DERAND_K4_CLANG17_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_clang17_O2_mc
   [layout_range "plt_memset";
    layout_range "mlkem1024_indcpa_keypair_derand"];;

let KP4_EXEC = MLKEM_NATIVE_INDCPA_KEYPAIR_DERAND_K4_CLANG17_O2_EXEC;;

(* ------------------------------------------------------------------------- *)
(* The key generation in FIPS 203 in terms of the coefficients computed by   *)
(* the code: those of the NTTs of s and e, those of the multiplication       *)
(* cache, those of the matrix-vector product in Montgomery form, and those   *)
(* of the final results after Montgomery conversion, addition and reduction. *)
(* The two lemmas on single coefficients relate the computation of the code  *)
(* to MultiplyNTTs and the addition of e in the NTT domain, for even and odd *)
(* coefficients.                                                             *)
(* ------------------------------------------------------------------------- *)

let KPKE_KEYGEN_COEFF_EVEN_K4_STMT =
  `!(A:num->num->int) (Y:num->num->int) (YT:num->int) (SH:num->num->int)
    (t:int) (u:int) (e:int) (eh:int) p.
     (!j. j < 4 ==> (Y j (2 * p) == SH j (2 * p)) (mod &3329) /\
                    (Y j (2 * p + 1) == SH j (2 * p + 1)) (mod &3329) /\
                    (YT j == Y j (2 * p + 1) *
                             &17 pow (2 * bitreverse7 p + 1)) (mod &3329)) /\
     (t == &169 * ((A 3 (2 * p + 1) * YT 3 + A 3 (2 * p) * Y 3 (2 * p)) +
                   (A 2 (2 * p + 1) * YT 2 + A 2 (2 * p) * Y 2 (2 * p)) +
                   (A 1 (2 * p + 1) * YT 1 + A 1 (2 * p) * Y 1 (2 * p)) +
                   (A 0 (2 * p + 1) * YT 0 + A 0 (2 * p) * Y 0 (2 * p))))
     (mod &3329) /\
     (u == &65536 * t) (mod &3329) /\
     (e == eh) (mod &3329)
     ==> (u + e) rem &3329 =
         ring_add mlkem_zq
          (ring_sum mlkem_zq {j | j < 4}
             (\j. fips203_multiply_ntts (A j) (SH j) (2 * p)))
          eh`;;

let KPKE_KEYGEN_COEFF_EVEN_K4 = assume_spec KPKE_KEYGEN_COEFF_EVEN_K4_STMT;;

let KPKE_KEYGEN_COEFF_ODD_K4_STMT =
  `!(A:num->num->int) (Y:num->num->int) (SH:num->num->int)
    (t:int) (u:int) (e:int) (eh:int) p.
     (!j. j < 4 ==> (Y j (2 * p) == SH j (2 * p)) (mod &3329) /\
                    (Y j (2 * p + 1) == SH j (2 * p + 1)) (mod &3329)) /\
     (t == &169 *
           ((A 3 (2 * p + 1) * Y 3 (2 * p) + A 3 (2 * p) * Y 3 (2 * p + 1)) +
            (A 2 (2 * p + 1) * Y 2 (2 * p) + A 2 (2 * p) * Y 2 (2 * p + 1)) +
            (A 1 (2 * p + 1) * Y 1 (2 * p) + A 1 (2 * p) * Y 1 (2 * p + 1)) +
            (A 0 (2 * p + 1) * Y 0 (2 * p) + A 0 (2 * p) * Y 0 (2 * p + 1))))
     (mod &3329) /\
     (u == &65536 * t) (mod &3329) /\
     (e == eh) (mod &3329)
     ==> (u + e) rem &3329 =
         ring_add mlkem_zq
          (ring_sum mlkem_zq {j | j < 4}
             (\j. fips203_multiply_ntts (A j) (SH j) (2 * p + 1)))
          eh`;;

let KPKE_KEYGEN_COEFF_ODD_K4 = assume_spec KPKE_KEYGEN_COEFF_ODD_K4_STMT;;

let KPKE_KEYGEN_K4_RESULT_STMT =
  `!d rho sigma (sh:num->int16) (eh:num->int16) (mc:num->int16)
    (pt:num->int16) (pt2:num->int16) (tr:num->int16) (sr:num->int16).
     mlkem_g(APPEND d [word 4]) = rho,sigma /\
     (!i j n. i < 4 /\ j < 4 /\ n < 256
              ==> mlkem_sample_ntt (APPEND rho [word j; word i]) n < &3329) /\
     (!j i. j < 4 /\ i < 256
            ==> (ival(sh(256 * j + i)) ==
                 mlkem_ntt (mlkem_cbd 2 (mlkem_prf 2 sigma (word j))) i)
                (mod &3329) /\
                abs(ival(sh(256 * j + i))) <= &23594) /\
     (!j i. j < 4 /\ i < 256
            ==> (ival(eh(256 * j + i)) ==
                 mlkem_ntt (mlkem_cbd 2 (mlkem_prf 2 sigma (word(4 + j)))) i)
                (mod &3329) /\
                abs(ival(eh(256 * j + i))) <= &23594) /\
     (!j p. j < 4 /\ p < 128
            ==> (ival(mc(128 * j + p)) ==
                 ival(sh(256 * j + 2 * p + 1)) *
                 &17 pow (2 * bitreverse7 p + 1)) (mod &3329)) /\
     (!r p. r < 4 /\ p < 128
            ==> (ival(pt(256 * r + 2 * p)) ==
                 &169 *
                 ((mlkem_sample_ntt (APPEND rho [word 3; word r]) (2 * p + 1) *
                   ival(mc(384 + p)) +
                   mlkem_sample_ntt (APPEND rho [word 3; word r]) (2 * p) *
                   ival(sh(768 + 2 * p))) +
                  (mlkem_sample_ntt (APPEND rho [word 2; word r]) (2 * p + 1) *
                   ival(mc(256 + p)) +
                   mlkem_sample_ntt (APPEND rho [word 2; word r]) (2 * p) *
                   ival(sh(512 + 2 * p))) +
                  (mlkem_sample_ntt (APPEND rho [word 1; word r]) (2 * p + 1) *
                   ival(mc(128 + p)) +
                   mlkem_sample_ntt (APPEND rho [word 1; word r]) (2 * p) *
                   ival(sh(256 + 2 * p))) +
                  (mlkem_sample_ntt (APPEND rho [word 0; word r]) (2 * p + 1) *
                   ival(mc p) +
                   mlkem_sample_ntt (APPEND rho [word 0; word r]) (2 * p) *
                   ival(sh(2 * p))))) (mod &3329) /\
                (ival(pt(256 * r + 2 * p + 1)) ==
                 &169 *
                 ((mlkem_sample_ntt (APPEND rho [word 3; word r]) (2 * p + 1) *
                   ival(sh(768 + 2 * p)) +
                   mlkem_sample_ntt (APPEND rho [word 3; word r]) (2 * p) *
                   ival(sh(768 + 2 * p + 1))) +
                  (mlkem_sample_ntt (APPEND rho [word 2; word r]) (2 * p + 1) *
                   ival(sh(512 + 2 * p)) +
                   mlkem_sample_ntt (APPEND rho [word 2; word r]) (2 * p) *
                   ival(sh(512 + 2 * p + 1))) +
                  (mlkem_sample_ntt (APPEND rho [word 1; word r]) (2 * p + 1) *
                   ival(sh(256 + 2 * p)) +
                   mlkem_sample_ntt (APPEND rho [word 1; word r]) (2 * p) *
                   ival(sh(256 + 2 * p + 1))) +
                  (mlkem_sample_ntt (APPEND rho [word 0; word r]) (2 * p + 1) *
                   ival(sh(2 * p)) +
                   mlkem_sample_ntt (APPEND rho [word 0; word r]) (2 * p) *
                   ival(sh(2 * p + 1))))) (mod &3329)) /\
     (!i. i < 1024 ==> (ival(pt2 i) == &65536 * ival(pt i)) (mod &3329) /\
                      abs(ival(pt2 i)) <= &3328) /\
     (!i. i < 1024 ==> ival(tr i) = ival(word_add (pt2 i) (eh i)) rem &3329) /\
     (!i. i < 1024 ==> ival(sr i) = ival(sh i) rem &3329)
     ==> num_of_wordlist(MAP (word_zx:int16->12 word) (list_of_seq tr 1024)) +
         2 EXP (8 * 1536) * num_of_bytelist rho =
         num_of_bytelist(FST(kpke_keygen mlkem1024 d)) /\
         num_of_wordlist(MAP (word_zx:int16->12 word) (list_of_seq sr 1024)) =
         num_of_bytelist(SND(kpke_keygen mlkem1024 d))`;;

let KPKE_KEYGEN_K4_RESULT = assume_spec KPKE_KEYGEN_K4_RESULT_STMT;;

(* ------------------------------------------------------------------------- *)
(* The buffers are aligned to 32 bytes within the stack frame, so their      *)
(* addresses depend on whether the stack pointer is a multiple of 32 or just *)
(* of 16. The input to SHA3-512 is the seed copied as two 128-bit words and  *)
(* the byte 4 (the parameter k), and its output is the two seeds rho and     *)
(* sigma as in mlkem_g.                                                      *)
(* ------------------------------------------------------------------------- *)

let KP4_BUFFER_ADDRESS_STMT =
  `!sp:int64.
        aligned 16 sp
        ==> word_and (word_add sp (word 3408)) (word 18446744073709551584) =
            word_add sp (word(if aligned 32 sp then 3392 else 3408))`;;

let KP4_BUFFER_ADDRESS = assume_spec KP4_BUFFER_ADDRESS_STMT;;

let KP4_BUFFER_TAC =
  FIRST_ASSUM(fun th ->
    if concl th = `aligned 32 (stackpointer:int64)` ||
       concl th = `~aligned 32 (stackpointer:int64)`
    then SUBST_ALL_TAC
          (REWRITE_RULE[th; ASSUME `aligned 16 (stackpointer:int64)`]
            (SPEC `stackpointer:int64` KP4_BUFFER_ADDRESS))
    else NO_TAC);;

let KP4_INPUT_STMT =
  `!a:int64 (d:byte list) c s:armstate.
        LENGTH d = 32 /\ c < 256 /\
        read (memory :> bytes128 a) s =
        word(num_of_bytelist d MOD 2 EXP 128) /\
        read (memory :> bytes128(word_add a (word 16))) s =
        word(num_of_bytelist d DIV 2 EXP 128) /\
        read (memory :> bytes8(word_add a (word 32))) s = word c
        ==> LENGTH(APPEND d [word c:byte]) = 33 /\
            read (memory :> bytes(a,33)) s =
            num_of_bytelist(APPEND d [word c])`;;

let KP4_INPUT = assume_spec KP4_INPUT_STMT;;

let KP4_INPUT_TAC b s =
  MP_TAC(SPECL [INDCPA_SP(b + 15392); `d:byte list`; `4`; s] KP4_INPUT) THEN
  ANTS_TAC THENL
   [CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[];
    STRIP_TAC];;

let KP4_G_TAC =
  FIRST_ASSUM(fun th ->
    if can (term_match []
             `read (memory :> bytes(a,64)) s = num_of_bytelist(sha3_512 c)`)
           (concl th)
    then ASSUME_TAC th THEN
         MP_TAC(CONV_RULE(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)
                 (REWRITE_RULE
                   [ASSUME `FST(mlkem_g(APPEND d [word 4])) = rho`;
                    ASSUME `SND(mlkem_g(APPEND d [word 4])) = sigma`]
                   (MATCH_MP MLKEM_G_BYTES th))) THEN
         CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN STRIP_TAC
    else NO_TAC);;

(* ------------------------------------------------------------------------- *)
(* The callees. The sixteen entries of the matrix are the outputs of four  *)
(* calls of mlkem_poly_rej_uniform_x4, one per row, with the buffers of 64 *)
(* bytes for the seeds reused by the calls. The two calls of               *)
(* mlkem1024_poly_getnoise_eta1_4x (for s and e) have buffers in the stack *)
(* frame as their fourth outputs, which are not null since the frame does  *)
(* not contain address 0, and their fourth nonces at the bottom of the     *)
(* stack. The theorem for mlkem1024_polyvec_basemul_acc_montgomery_cached  *)
(* is used with its hypotheses as conjunctions.                            *)
(* ------------------------------------------------------------------------- *)

let LOCAL_SHA3_512_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_clang17_O2_mc,KP4_EXEC,
    0x0,mlkem_native_libmlkem_clang17_O2_mc,
    MLKEM_NATIVE_SHA3_512_CLANG17_O2_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_REJ_UNIFORM_X4_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_clang17_O2_mc,KP4_EXEC,
    0x0,mlkem_native_libmlkem_clang17_O2_mc,
    REWRITE_RULE[ALL]
     MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_CLANG17_O2_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_GETNOISE_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_clang17_O2_mc,KP4_EXEC,
    0x0,mlkem_native_libmlkem_clang17_O2_mc,
    MLKEM_NATIVE_POLY_GETNOISE_ETA1_4X_K4_CLANG17_O2_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_POLYVEC_NTT_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_clang17_O2_mc,KP4_EXEC,
    0x0,mlkem_native_libmlkem_clang17_O2_mc,
    MLKEM_NATIVE_POLYVEC_NTT_K4_CLANG17_O2_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_POLYVEC_MULCACHE_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_clang17_O2_mc,KP4_EXEC,
    0x0,mlkem_native_libmlkem_clang17_O2_mc,
    MLKEM_NATIVE_POLYVEC_MULCACHE_COMPUTE_K4_CLANG17_O2_IMAGE_SUBROUTINE_CORRECT
   );;

let LOCAL_BASEMUL_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_clang17_O2_mc,KP4_EXEC,
    0x0,mlkem_native_libmlkem_clang17_O2_mc,
    REWRITE_RULE[ALL]
      MLKEM_NATIVE_BASEMUL_K4_CLANG17_O2_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_POLYVEC_TOMONT_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_clang17_O2_mc,KP4_EXEC,
    0x0,mlkem_native_libmlkem_clang17_O2_mc,
    MLKEM_NATIVE_POLYVEC_TOMONT_K4_CLANG17_O2_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_POLYVEC_ADD_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_clang17_O2_mc,KP4_EXEC,
    0x0,mlkem_native_libmlkem_clang17_O2_mc,
    MLKEM_NATIVE_POLYVEC_ADD_K4_CLANG17_O2_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_POLYVEC_REDUCE_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_clang17_O2_mc,KP4_EXEC,
    0x0,mlkem_native_libmlkem_clang17_O2_mc,
    MLKEM_NATIVE_POLYVEC_REDUCE_K4_CLANG17_O2_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_POLYVEC_TOBYTES_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_clang17_O2_mc,KP4_EXEC,
    0x0,mlkem_native_libmlkem_clang17_O2_mc,
    MLKEM_NATIVE_POLYVEC_TOBYTES_K4_CLANG17_O2_IMAGE_SUBROUTINE_CORRECT);;

(* ------------------------------------------------------------------------- *)
(* The facts about the stages of the computation other than those given by   *)
(* the tactics in mlkem_native_indcpa.ml: the coefficients of the matrix as  *)
(* given by SampleNTT, the bounds on the inputs of the multiplications, the  *)
(* rows of the matrix-vector product, and rho in the public key, and the     *)
(* test of the loop over the rows, whose pointers are at constant offsets    *)
(* from the stack pointer, so the loop is simply unrolled.                   *)
(* ------------------------------------------------------------------------- *)

let KP4_SEED x y =
  let b n = mk_comb(`word:num->byte`,mk_small_numeral n) in
  mk_comb(mk_comb(`APPEND:byte list->byte list->byte list`,`rho:byte list`),
          mk_list([b x; b y],`:byte`));;

let KP4_SEED_TAC off x y s =
  GENMAT_INPUT_TAC off x y (mk_var(s,`:armstate`));;

(*** Instance (i,j) of the hypothesis on the samples of SHAKE128 ***)

let KP4_HYP_TAC i j =
  W(fun (asl,_) ->
    let hth = find (fun th ->
      match concl th with
        Comb(Const("!",_),Abs(Var("i",_),
        Comb(Const("!",_),Abs(Var("j",_),b)))) ->
            (try let _,r = dest_imp b in
                 fst(strip_comb r) = `(<=):num->num->bool`
             with Failure _ -> false)
      | _ -> false) (map snd asl) in
    let th1 = SPECL [mk_small_numeral i; mk_small_numeral j] hth in
    ASSUME_TAC(MP th1 (EQT_ELIM(NUM_REDUCE_CONV(lhand(concl th1))))));;

let KP4_WORDLISTS_TAC b s =
  let addr = Printf.sprintf
    "word_add stackpointer (word (%d + 512 * (4 * i + j))):int64" b in
  SUBGOAL_THEN
   (parse_term(Printf.sprintf
     "!i j. i < 4 /\\ j < 4
            ==> wordlist_from_memory(%s,256) (%s:armstate) =
                SUB_LIST(0,256)
                 (FILTER (\\x. val x < 3329)
                   (MAP (word_zx:12 word->16 word)
                     (wordlist_of_num (336 + 112 * k)
                       (num_of_bytelist
                         (list_of_seq
                           (shake128 (APPEND (rho:byte list)
                                             [word j; word i]))
                           (504 + 168 * k))))))" addr s))
  ASSUME_TAC THENL [GENMAT_FINAL_TAC; ALL_TAC];;

let KP4_MATRIX_TAC b sname =
  let s = mk_var(sname,`:armstate`) in
  let addr = parse_term(Printf.sprintf
    "word_add stackpointer (word (%d + 512 * (4 * r + j))):int64" b) in
  KP4_WORDLISTS_TAC b sname THEN
  SUBGOAL_THEN
   `!r j n. r < 4 /\ j < 4 /\ n < 256
            ==> &0 <= mlkem_sample_ntt (APPEND rho [word j; word r]) n /\
                mlkem_sample_ntt (APPEND rho [word j; word r]) n < &3329`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    MATCH_MP_TAC MLKEM_SAMPLE_NTT_REJ_BOUND THEN
    EXISTS_TAC `k:num` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!r j n. r < 4 /\ j < 4 /\ n < 256
            ==> ival((AM:num->int16)(1024 * r + 256 * j + n)) =
                mlkem_sample_ntt (APPEND rho [word j; word r]) n`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    INDCPA_GHOST_SPEC_TAC "AM" `1024 * r + 256 * j + n` THEN
    MP_TAC(SPECL [addr; s; `APPEND (rho:byte list) [word j; word r]`;
                  `k:num`; `n:num`]
                 MLKEM_NATIVE_SAMPLE_COEFF) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
    AP_TERM_TAC THEN REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    MATCH_MP_TAC READ16_OFFSET_EQ THEN ARITH_TAC;
    ALL_TAC];;

let KP4_AM_INST r j =
  let th = SPECL [mk_small_numeral r; mk_small_numeral j]
    (ASSUME `!r j n. r < 4 /\ j < 4 /\ n < 256
                     ==> ival((AM:num->int16)(1024 * r + 256 * j + n)) =
                         mlkem_sample_ntt (APPEND rho [word j; word r]) n`) in
  CONV_RULE(NUM_REDUCE_CONV THENC REWRITE_CONV[ADD_CLAUSES; ADD_ASSOC] THENC
            NUM_REDUCE_CONV) th;;

let KP4_PT_GOAL = `!r p. r < 4 /\ p < 128
            ==> (ival((PT:num->int16)(256 * r + 2 * p)) ==
                 &169 *
                 ((mlkem_sample_ntt (APPEND rho [word 3; word r]) (2 * p + 1) *
                   ival((MC:num->int16)(384 + p)) +
                   mlkem_sample_ntt (APPEND rho [word 3; word r]) (2 * p) *
                   ival((SH:num->int16)(768 + 2 * p))) +
                  (mlkem_sample_ntt (APPEND rho [word 2; word r]) (2 * p + 1) *
                   ival(MC(256 + p)) +
                   mlkem_sample_ntt (APPEND rho [word 2; word r]) (2 * p) *
                   ival(SH(512 + 2 * p))) +
                  (mlkem_sample_ntt (APPEND rho [word 1; word r]) (2 * p + 1) *
                   ival(MC(128 + p)) +
                   mlkem_sample_ntt (APPEND rho [word 1; word r]) (2 * p) *
                   ival(SH(256 + 2 * p))) +
                  (mlkem_sample_ntt (APPEND rho [word 0; word r]) (2 * p + 1) *
                   ival(MC p) +
                   mlkem_sample_ntt (APPEND rho [word 0; word r]) (2 * p) *
                   ival(SH(2 * p))))) (mod &3329) /\
                (ival(PT(256 * r + 2 * p + 1)) ==
                 &169 *
                 ((mlkem_sample_ntt (APPEND rho [word 3; word r]) (2 * p + 1) *
                   ival(SH(768 + 2 * p)) +
                   mlkem_sample_ntt (APPEND rho [word 3; word r]) (2 * p) *
                   ival(SH(768 + 2 * p + 1))) +
                  (mlkem_sample_ntt (APPEND rho [word 2; word r]) (2 * p + 1) *
                   ival(SH(512 + 2 * p)) +
                   mlkem_sample_ntt (APPEND rho [word 2; word r]) (2 * p) *
                   ival(SH(512 + 2 * p + 1))) +
                  (mlkem_sample_ntt (APPEND rho [word 1; word r]) (2 * p + 1) *
                   ival(SH(256 + 2 * p)) +
                   mlkem_sample_ntt (APPEND rho [word 1; word r]) (2 * p) *
                   ival(SH(256 + 2 * p + 1))) +
                  (mlkem_sample_ntt (APPEND rho [word 0; word r]) (2 * p + 1) *
                   ival(SH(2 * p)) +
                   mlkem_sample_ntt (APPEND rho [word 0; word r]) (2 * p) *
                   ival(SH(2 * p + 1))))) (mod &3329)`;;

let KP4_AM_BOUND_TAC =
  SUBGOAL_THEN `!m. m < 4096 ==> abs(ival((AM:num->int16) m)) <= &2 pow 12`
  (LABEL_TAC "ambound") THENL
   [X_GEN_TAC `m:num` THEN DISCH_TAC THEN
    MP_TAC(SPECL [`1024`; `4`; `m:num`] EXISTS_DIV_MOD_LT) THEN
    ASM_REWRITE_TAC[ARITH_RULE `1024 * 4 = 4096`; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`r:num`; `q:num`] THEN STRIP_TAC THEN
    MP_TAC(SPECL [`256`; `4`; `q:num`] EXISTS_DIV_MOD_LT) THEN
    ASM_REWRITE_TAC[ARITH_RULE `256 * 4 = 1024`; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`j:num`; `n:num`] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC(INT_ARITH
     `&0 <= x /\ x < &3329 ==> abs(x:int) <= &2 pow 12`) THEN
    ASM_SIMP_TAC[];
    ALL_TAC];;

let KP4_BASEMUL_DEFS =
  [basemul4_even; basemul4_odd; pmul_acc4; pmull_acc4; pmull];;

let KP4_PT_TAC b =
  INDCPA_GHOST_TAC "PT" (b + 3104) 1024 "s201" THEN
  SUBGOAL_THEN KP4_PT_GOAL ASSUME_TAC THENL
   [REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
    CONV_TAC EXPAND_CASES_CONV THEN REPEAT CONJ_TAC THENL
     (map (fun r -> INDCPA_BASEMULK_ROW_TAC 4 "PT" (b + 3104 + 512 * r)
                     "ambound" (map (KP4_AM_INST r) [0;1;2;3])
                     KP4_BASEMUL_DEFS) [0;1;2;3]);
    ALL_TAC];;

let KP4_PC_TAC s =
  let pcs = mk_comb(`read PC`,mk_var(s,`:armstate`)) in
  FIRST_X_ASSUM(fun th ->
    if is_eq(concl th) && lhand(concl th) = pcs then
      ASSUME_TAC(CONV_RULE(RAND_CONV
       (REWRITE_CONV
         [WORD_RULE `word_sub (word_add (s:int64) x) (word_add s y) =
                     word_sub x y`] THENC
        ONCE_DEPTH_CONV WORD_REDUCE_CONV THENC NUM_REDUCE_CONV THENC
        REWRITE_CONV[])) th)
    else NO_TAC);;

let KP4_RHO_HALVES_TAC b =
  FIRST_ASSUM(MP_TAC o MATCH_MP GENMAT_BYTES128_HALVES o check (fun th ->
    can (term_match [] (subst [INDCPA_SP(b + 15456),`a:int64`]
      `read (memory :> bytes(a,32)) s = num_of_bytelist rho`))
      (concl th))) THEN
  CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN STRIP_TAC;;

let KP4_RHO_TAC s =
  MP_TAC(SPECL [`word_add pk (word 1536):int64`; `num_of_bytelist rho`;
                mk_var(s,`:armstate`)] GENMAT_BYTES_32_OF_HALVES) THEN
  ANTS_TAC THENL
   [CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `rho:byte list` NUM_OF_BYTELIST_BOUND) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];
    DISCH_TAC];;

let KP4_FINAL_TAC =
  REWRITE_TAC[ARITH_RULE `1568 = 1536 + 32`; READ_COMPONENT_COMPOSE;
              READ_BYTES_COMBINE] THEN
  REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`d:byte list`; `rho:byte list`; `sigma:byte list`;
                `SH:num->int16`; `EH:num->int16`; `MC:num->int16`;
                `PT:num->int16`; `PT2:num->int16`; `TR:num->int16`;
                `SR:num->int16`] KPKE_KEYGEN_K4_RESULT) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REWRITE_TAC[GSYM(ASSUME `FST(mlkem_g(APPEND d [word 4])) = rho`);
                  GSYM(ASSUME `SND(mlkem_g(APPEND d [word 4])) = sigma`);
                  PAIR];
      REPEAT STRIP_TAC THEN ASM_SIMP_TAC[];
      ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[]];
    SIMP_TAC[]];;

(* ------------------------------------------------------------------------- *)
(* Correctness proof, assuming the contracts for memset and memcpy (the    *)
(* latter for the callees). The seed d is 32 bytes at coins, and the       *)
(* public key of 1568 bytes at pk and the secret key of 1536 bytes at sk   *)
(* are those of kpke_keygen mlkem1024 d in common/fips203/fips203.ml. The  *)
(* theorem assumes that SampleNTT terminates for each entry of the matrix, *)
(* which means that the output of SHAKE128 for it has 256 fields < q, as   *)
(* for mlkem1024_gen_matrix, and that the stack does not contain address   *)
(* 0. The stack is the 15664 bytes of the function (96 of saved registers, *)
(* the buffers and the canary, and 16 for the alignment) and the 3392 used *)
(* by mlkem_poly_rej_uniform_x4 below them. The proof is by cases on       *)
(* whether the stack pointer is a multiple of 32, which gives the address  *)
(* b of the buffers, at offsets 0 (the fourth nonce), 32 (the              *)
(* multiplication cache), 1056 (s), 3104 (t), 5152 (e), 7200 (the matrix), *)
(* 15392 (the input of SHA3-512) and 15456 (rho and sigma).                *)
(* ------------------------------------------------------------------------- *)

let KP4_INTRO_TAC =
  MAP_EVERY X_GEN_TAC
   [`pk:int64`; `sk:int64`; `coins:int64`; `d:byte list`; `guard:int64`;
    `mf:int64`; `mc:int64`; `ea:int64`; `el:num`; `ev:num`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 19056 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE] THEN
  REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NONOVERLAPPING_CLAUSES]) THEN
  SUBGOAL_THEN `aligned 16 (stackpointer:int64)` ASSUME_TAC THENL
   [UNDISCH_TAC `aligned 16 (word_add stackpointer (word 19056):int64)` THEN
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
   `!i j. i < 4 /\ j < 4
          ==> mlkem_samplentt_terminates
               (APPEND (FST(mlkem_g(APPEND d [word 4])))
                       [word j; word i])` THEN
  ABBREV_TAC `rho = FST(mlkem_g(APPEND d [word 4]))` THEN
  ABBREV_TAC `sigma = SND(mlkem_g(APPEND d [word 4]))` THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`4`; `\i j. APPEND (rho:byte list) [word j; word (i:num)]`]
                MLKEM_SAMPLENTT_TERMINATES_UNIFORM) THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `k:num`) THEN
  SUBGOAL_THEN `LENGTH(rho:byte list) = 32 /\ LENGTH(sigma:byte list) = 32`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["rho"; "sigma"] THEN REWRITE_TAC[LENGTH_MLKEM_G];
    ALL_TAC];;

let KP4_CASE_TAC b =
  let st n = "s"^string_of_int n in
  ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP GENMAT_BYTES128_HALVES o check
   (can (term_match [] `read (memory :> bytes(coins,32)) s = n`) o concl)) THEN
  STRIP_TAC THEN

  (*** The setup, the input to SHA3-512 and the call ***)

  ARM_STEPS_TAC KP4_EXEC (1--10) THEN KP4_BUFFER_TAC THEN
  ARM_STEPS_TAC KP4_EXEC (11--11) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC KP4_EXEC (12--30) THEN
  KP4_INPUT_TAC b `s30:armstate` THEN INDCPA_GOT_TAC THEN
  ARM_STEPS_TAC KP4_EXEC [31] THEN
  LOCAL_SHA3_512_TAC
   [`read X0 s`; `read X1 s`; `APPEND d [word 4]:byte list`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 32 THEN
  KP4_G_TAC THEN KP4_RHO_HALVES_TAC b THEN

  (*** The matrix: four calls of mlkem_poly_rej_uniform_x4, one per row ***)

  ARM_STEPS_TAC KP4_EXEC (33--60) THEN
  MAP_EVERY (fun m -> KP4_SEED_TAC (b + 5152 + 64 * m) m 0 (st 60)) (0--3) THEN
  MAP_EVERY (fun e -> KP4_HYP_TAC (e / 4) (e mod 4)) (0--15) THEN
  ARM_STEPS_TAC KP4_EXEC [61] THEN
  LOCAL_REJ_UNIFORM_X4_TAC
    ([`read X0 s`; `read X1 s`; `read X2 s`; `read X3 s`; `read X4 s`] @
     map (fun m -> KP4_SEED m 0) (0--3) @
     [`k:num`; `guard:int64`; `mf:int64`; `ea:int64`; `el:num`; `ev:num`;
      `pc:num`; `read SP s`; `read X30 s`]) 62 THEN
  GENMAT_TOBYTES_TAC THEN
  ARM_STEPS_TAC KP4_EXEC (63--77) THEN
  MAP_EVERY (fun m -> KP4_SEED_TAC (b + 5152 + 64 * m) m 1 (st 77)) (0--3) THEN
  ARM_STEPS_TAC KP4_EXEC [78] THEN
  LOCAL_REJ_UNIFORM_X4_TAC
    ([`read X0 s`; `read X1 s`; `read X2 s`; `read X3 s`; `read X4 s`] @
     map (fun m -> KP4_SEED m 1) (0--3) @
     [`k:num`; `guard:int64`; `mf:int64`; `ea:int64`; `el:num`; `ev:num`;
      `pc:num`; `read SP s`; `read X30 s`]) 79 THEN
  GENMAT_TOBYTES_TAC THEN
  ARM_STEPS_TAC KP4_EXEC (80--97) THEN
  MAP_EVERY (fun m -> KP4_SEED_TAC (b + 5152 + 64 * m) m 2 (st 97)) (0--3) THEN
  ARM_STEPS_TAC KP4_EXEC [98] THEN
  LOCAL_REJ_UNIFORM_X4_TAC
    ([`read X0 s`; `read X1 s`; `read X2 s`; `read X3 s`; `read X4 s`] @
     map (fun m -> KP4_SEED m 2) (0--3) @
     [`k:num`; `guard:int64`; `mf:int64`; `ea:int64`; `el:num`; `ev:num`;
      `pc:num`; `read SP s`; `read X30 s`]) 99 THEN
  GENMAT_TOBYTES_TAC THEN
  ARM_STEPS_TAC KP4_EXEC (100--118) THEN
  MAP_EVERY (fun m -> KP4_SEED_TAC (b + 5152 + 64 * m) m 3 (st 118)) (0--3) THEN
  ARM_STEPS_TAC KP4_EXEC [119] THEN
  LOCAL_REJ_UNIFORM_X4_TAC
    ([`read X0 s`; `read X1 s`; `read X2 s`; `read X3 s`; `read X4 s`] @
     map (fun m -> KP4_SEED m 3) (0--3) @
     [`k:num`; `guard:int64`; `mf:int64`; `ea:int64`; `el:num`; `ev:num`;
      `pc:num`; `read SP s`; `read X30 s`]) 120 THEN
  GENMAT_TOBYTES_TAC THEN
  INDCPA_GHOST_TAC "AM" (b + 7200) 4096 (st 120) THEN
  KP4_MATRIX_TAC (b + 7200) "s120" THEN

  (*** The noise, s and e from two calls with four outputs ***)

  ARM_STEPS_TAC KP4_EXEC (121--148) THEN
  INDCPA_NONZERO_TAC 19056 (b + 2592) THEN INDCPA_NONCE_TAC 3 THEN
  ARM_STEPS_TAC KP4_EXEC [149] THEN
  LOCAL_GETNOISE_TAC
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X3 s`; `read X4 s`;
    `sigma:byte list`; `read X5 s`; `read X6 s`; `read X7 s`;
    `word 3:int64`; `guard:int64`; `mf:int64`; `mc:int64`; `ea:int64`;
    `el:num`; `ev:num`; `pc:num`; `read SP s`; `read X30 s`] 150 THEN
  INDCPA_NOISE_TAC "S0" (b + 1056) 4 "sigma" "word j" (st 150) THEN
  INDCPA_DISCARD_LETS_TAC THEN
  ARM_STEPS_TAC KP4_EXEC (151--161) THEN
  INDCPA_NONZERO_TAC 19056 (b + 6688) THEN INDCPA_NONCE_TAC 7 THEN
  ARM_STEPS_TAC KP4_EXEC [162] THEN
  LOCAL_GETNOISE_TAC
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X3 s`; `read X4 s`;
    `sigma:byte list`; `read X5 s`; `read X6 s`; `read X7 s`;
    `word 7:int64`; `guard:int64`; `mf:int64`; `mc:int64`; `ea:int64`;
    `el:num`; `ev:num`; `pc:num`; `read SP s`; `read X30 s`] 163 THEN
  INDCPA_NOISE_TAC "E0" (b + 5152) 4 "sigma" "word(4 + j)" (st 163) THEN
  INDCPA_DISCARD_LETS_TAC THEN

  (*** The NTTs and the multiplication cache ***)

  ARM_STEPS_TAC KP4_EXEC (164--165) THEN
  LOCAL_POLYVEC_NTT_TAC
   [`read X0 s`; `S0:num->int16`; `pc:num`; `read SP s`; `read X30 s`] 166 THEN
  INDCPA_NTT_TAC "SH" (b + 1056) 4 "S0" "sigma" "word j" (st 166) THEN
  ARM_STEPS_TAC KP4_EXEC (167--169) THEN
  LOCAL_POLYVEC_NTT_TAC
   [`read X0 s`; `E0:num->int16`; `pc:num`; `read SP s`; `read X30 s`] 170 THEN
  INDCPA_NTT_TAC "EH" (b + 5152) 4 "E0" "sigma" "word(4 + j)" (st 170) THEN
  ARM_STEPS_TAC KP4_EXEC (171--174) THEN
  LOCAL_POLYVEC_MULCACHE_TAC
   [`read X0 s`; `read X1 s`; `SH:num->int16`; `pc:num`; `read SP s`;
    `read X30 s`] 175 THEN
  INDCPA_MULCACHE_TAC "MC" (b + 32) 4 "SH" (st 175) THEN

  (*** The matrix-vector product, one row per call ***)

  MAP_EVERY (fun (q,s0,s1) ->
    let a = (b + 7200 + 2048 * q,"AM",1024 * q)
    and y = (b + 1056,"SH") and t = (b + 32,"MC") in
    ARM_STEPS_TAC KP4_EXEC (s0--s1) THEN
    INDCPA_BASEMULK_PRE_TAC 4 a y t (st s1) THEN
    LOCAL_BASEMUL_TAC (INDCPA_BASEMULK_ARGS 4 ("AM",1024 * q) "SH" "MC")
      (s1 + 1) THEN
    INDCPA_BASEMULK_DROP_PRE_TAC 4 a y t) [0,176,182; 1,184,188; 2,190,194; 3,196,200] THEN
  KP4_AM_BOUND_TAC THEN KP4_PT_TAC b THEN

  (*** Montgomery form, adding the noise, the reductions ***)

  ARM_STEPS_TAC KP4_EXEC (202--203) THEN
  LOCAL_POLYVEC_TOMONT_TAC
   [`read X0 s`; `PT:num->int16`; `pc:num`; `read SP s`; `read X30 s`] 204 THEN
  INDCPA_TOMONT_TAC "PT2" (b + 3104) 1024 "PT" (st 204) THEN
  ARM_STEPS_TAC KP4_EXEC (205--208) THEN
  LOCAL_POLYVEC_ADD_TAC
   [`read X0 s`; `read X1 s`; `PT2:num->int16`; `EH:num->int16`; `pc:num`;
    `read SP s`; `read X30 s`] 209 THEN
  ARM_STEPS_TAC KP4_EXEC (210--211) THEN
  LOCAL_POLYVEC_REDUCE_TAC
   [`read X0 s`; `\i. word_add ((PT2:num->int16) i) ((EH:num->int16) i)`;
    `pc:num`; `read SP s`; `read X30 s`] 212 THEN
  INDCPA_REDUCE_TAC "TR" (b + 3104) 1024
    "word_add ((PT2:num->int16) i) ((EH:num->int16) i)" (st 212) THEN
  ARM_STEPS_TAC KP4_EXEC (213--214) THEN
  LOCAL_POLYVEC_REDUCE_TAC
   [`read X0 s`; `SH:num->int16`; `pc:num`; `read SP s`; `read X30 s`] 215 THEN
  INDCPA_REDUCE_TAC "SR" (b + 1056) 1024 "(SH:num->int16) i" (st 215) THEN

  (*** The encodings of the keys ***)

  ARM_STEPS_TAC KP4_EXEC (216--218) THEN
  INDCPA_TOBYTES_PRE_TAC "SR" (b + 1056) 1024 (st 218) THEN
  LOCAL_POLYVEC_TOBYTES_TAC
   [`read X0 s`; `read X1 s`; `list_of_seq (SR:num->int16) 1024`; `pc:num`;
    `read SP s`; `read X30 s`] 219 THEN
  INDCPA_TOBYTES_POST_TAC "SR" 1024 `\i. ival((SH:num->int16) i)` THEN
  ARM_STEPS_TAC KP4_EXEC (220--222) THEN
  INDCPA_TOBYTES_PRE_TAC "TR" (b + 3104) 1024 (st 222) THEN
  LOCAL_POLYVEC_TOBYTES_TAC
   [`read X0 s`; `read X1 s`; `list_of_seq (TR:num->int16) 1024`; `pc:num`;
    `read SP s`; `read X30 s`] 223 THEN
  INDCPA_TOBYTES_POST_TAC "TR" 1024
    `\i. ival(word_add ((PT2:num->int16) i) ((EH:num->int16) i))` THEN
  ARM_STEPS_TAC KP4_EXEC (224--230) THEN KP4_RHO_TAC (st 230) THEN

  (*** Zeroing the buffers, the stack guard, the return ***)

  INDCPA_MEMSET_LABEL_TAC THEN
  INDCPA_MEMSETS_TAC KP4_EXEC
   [231,231; 237,240; 246,249; 255,259; 265,269] THEN
  ARM_STEPS_TAC KP4_EXEC (275--289) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC KP4_EXEC (290--303) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN KP4_FINAL_TAC;;

let MLKEM_NATIVE_INDCPA_KEYPAIR_DERAND_K4_CLANG17_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!pk sk coins (d:byte list) guard mf mc ea el ev pc stackpointer
    returnaddress.
        memset_contract mf ea el ev /\ memcpy_contract mc ea el ev /\
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\ LENGTH d = 32 /\
        (!i j. i < 4 /\ j < 4
               ==> mlkem_samplentt_terminates
                    (APPEND (FST(mlkem_g(APPEND d [word 4])))
                            [word j; word i])) /\
        nonoverlapping (word 0,1) (word_sub stackpointer (word 19056),19056) /\
        PAIRWISE nonoverlapping
         [(pk,1568); (sk,1536); (word_sub stackpointer (word 19056),19056)] /\
        ALLPAIRS nonoverlapping
         [(pk,1568); (sk,1536); (word_sub stackpointer (word 19056),19056)]
         [(coins,32); (word pc,libmlkem_size);
          (word(pc + got_stack_chk_guard),8); (guard,8);
          (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_clang17_O2_mc /\
                  read PC s = word (pc + mlkem1024_indcpa_keypair_derand) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [pk; sk; coins] s /\
                  read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                    guard /\
                  read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                  read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                  read (memory :> bytes(ea,el)) s = ev /\
                  read (memory :> bytes(coins,32)) s = num_of_bytelist d)
             (\s. read PC s = returnaddress /\
                  read (memory :> bytes(pk,1568)) s =
                  num_of_bytelist(FST(kpke_keygen mlkem1024 d)) /\
                  read (memory :> bytes(sk,1536)) s =
                  num_of_bytelist(SND(kpke_keygen mlkem1024 d)) /\
                  C_RETURN s = word 0)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
              MAYCHANGE
               [memory :> bytes(pk,1568); memory :> bytes(sk,1536);
                memory :> bytes(word_sub stackpointer (word 19056),19056)])`;;

let MLKEM_NATIVE_INDCPA_KEYPAIR_DERAND_K4_CLANG17_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_INDCPA_KEYPAIR_DERAND_K4_CLANG17_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof, assuming the combined contract   *)
(* for memset (for mlkem_poly_rej_uniform_x4) and the safety contract for  *)
(* memcpy. The events depend only on the addresses and on rho, the seed of *)
(* the matrix, which is part of the public key, through the samples of     *)
(* SampleNTT: they are given as a function of rho, which is the first half *)
(* of the result of SHA3-512, given by its combined theorem, and the       *)
(* theorem also states that rho is the end of the public key. As for the   *)
(* correctness proof, the proof is by cases on whether the stack pointer   *)
(* is a multiple of 32, with the events in the two cases as the two        *)
(* branches of the template.                                               *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let KP_SAFE_TEMPLATE =
 `\(pk:int64) (sk:int64) (coins:int64) (guard:int64) (mf:int64) (mc:int64)
   (pc:num) (stackpointer:int64) (returnaddress:int64) (rho:byte list).
   if aligned 32 stackpointer
   then f_ev_a pk sk coins guard mf mc pc stackpointer returnaddress rho
   else f_ev_u pk sk coins guard mf mc pc stackpointer returnaddress rho
   :(uarch_event)list`;;

let KP_SAFE_ALLOWED =
  [`pc:num`; `pk:int64`; `sk:int64`; `coins:int64`; `guard:int64`;
   `mf:int64`; `mc:int64`; `stackpointer:int64`; `returnaddress:int64`;
   `rho:byte list`];;

let KP4_SAFE_INTRO_TAC =
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
        MLKEM_NATIVE_POLY_GETNOISE_ETA1_4X_K4_CLANG17_O2_IMAGE_SUBROUTINE_SAFE
        (CONJ th1 th2) in
      ASSUME_CALLEE_SAFETY_TAILED_ALT_TAC gth "H_GETNOISE")
    else NO_TAC) THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_SHA3_512_CLANG17_O2_IMAGE_SUBROUTINE_FULL "H_SHA3" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_POLYVEC_NTT_K4_CLANG17_O2_IMAGE_SUBROUTINE_SAFE "H_NTT" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_POLYVEC_MULCACHE_COMPUTE_K4_CLANG17_O2_IMAGE_SUBROUTINE_SAFE
    "H_MULCACHE" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_BASEMUL_K4_CLANG17_O2_IMAGE_SUBROUTINE_SAFE "H_BASEMUL" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_POLYVEC_TOMONT_K4_CLANG17_O2_IMAGE_SUBROUTINE_SAFE
    "H_TOMONT" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_POLYVEC_ADD_K4_CLANG17_O2_IMAGE_SUBROUTINE_SAFE "H_ADD" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_POLYVEC_REDUCE_K4_CLANG17_O2_IMAGE_SUBROUTINE_SAFE
    "H_REDUCE" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_POLYVEC_TOBYTES_K4_CLANG17_O2_IMAGE_SUBROUTINE_SAFE
    "H_TOBYTES" THEN
  CONCRETIZE_F_EVENTS_TAC KP_SAFE_TEMPLATE THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NONOVERLAPPING_CLAUSES]) THEN
  SUBGOAL_THEN `aligned 16 (stackpointer:int64)` ASSUME_TAC THENL
   [UNDISCH_TAC `aligned 16 (word_add stackpointer (word 19056):int64)` THEN
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
   `!i j. i < 4 /\ j < 4
          ==> mlkem_samplentt_terminates
               (APPEND (FST(mlkem_g(APPEND d [word 4])))
                       [word j; word i])` THEN
  ABBREV_TAC `rho = FST(mlkem_g(APPEND d [word 4]))` THEN
  ABBREV_TAC `sigma = SND(mlkem_g(APPEND d [word 4]))` THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`4`; `\i j. APPEND (rho:byte list) [word j; word (i:num)]`]
                MLKEM_SAMPLENTT_TERMINATES_UNIFORM) THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `k:num`) THEN
  SUBGOAL_THEN `LENGTH(rho:byte list) = 32 /\ LENGTH(sigma:byte list) = 32`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["rho"; "sigma"] THEN REWRITE_TAC[LENGTH_MLKEM_G];
    ALL_TAC];;

let KP4_SAFE_CALL_TAC name ilist n =
  REMOVE_THEN name (fun safety_th ->
    ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_clang17_O2_mc,KP4_EXEC,
       0x0,mlkem_native_libmlkem_clang17_O2_mc,safety_th)
      ilist n THENL
     [EXISTS_E2_TAC (ref KP_SAFE_ALLOWED); LABEL_TAC name safety_th]);;

let KP4_SAFE_CASE_TAC b =
  let st n = "s"^string_of_int n in
  let e = `e:(uarch_event)list` in
  let x n = mk_comb(mk_comb(`read:(armstate,int64)component->armstate->int64`,
                            mk_const("X"^string_of_int n,[])),`s:armstate`) in
  let rest = [`pc:num`; `read SP s`; `read X30 s`] in
  ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP GENMAT_BYTES128_HALVES o check
   (can (term_match [] `read (memory :> bytes(coins,32)) s = n`) o concl)) THEN
  STRIP_TAC THEN
  ARM_STEPS_TAC KP4_EXEC (1--10) THEN KP4_BUFFER_TAC THEN
  ARM_STEPS_TAC KP4_EXEC (11--11) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC KP4_EXEC (12--30) THEN
  KP4_INPUT_TAC b `s30:armstate` THEN INDCPA_GOT_TAC THEN
  ARM_STEPS_TAC KP4_EXEC [31] THEN
  KP4_SAFE_CALL_TAC "H_SHA3"
   ([e; x 0; x 1; `APPEND d [word 4]:byte list`; `33`; `guard:int64`] @
    rest) 32 THEN
  KP4_G_TAC THEN KP4_RHO_HALVES_TAC b THEN
  ARM_STEPS_TAC KP4_EXEC (33--60) THEN
  MAP_EVERY (fun m -> KP4_SEED_TAC (b + 5152 + 64 * m) m 0 (st 60)) (0--3) THEN
  MAP_EVERY (fun e -> KP4_HYP_TAC (e / 4) (e mod 4)) (0--15) THEN
  ARM_STEPS_TAC KP4_EXEC [61] THEN
  KP4_SAFE_CALL_TAC "H_X4"
    ([e; x 0; x 1; x 2; x 3; x 4] @ map (fun m -> KP4_SEED m 0) (0--3) @
     [`k:num`; `guard:int64`] @ rest) 62 THEN
  ARM_STEPS_TAC KP4_EXEC (63--77) THEN
  MAP_EVERY (fun m -> KP4_SEED_TAC (b + 5152 + 64 * m) m 1 (st 77)) (0--3) THEN
  ARM_STEPS_TAC KP4_EXEC [78] THEN
  KP4_SAFE_CALL_TAC "H_X4"
    ([e; x 0; x 1; x 2; x 3; x 4] @ map (fun m -> KP4_SEED m 1) (0--3) @
     [`k:num`; `guard:int64`] @ rest) 79 THEN
  ARM_STEPS_TAC KP4_EXEC (80--97) THEN
  MAP_EVERY (fun m -> KP4_SEED_TAC (b + 5152 + 64 * m) m 2 (st 97)) (0--3) THEN
  ARM_STEPS_TAC KP4_EXEC [98] THEN
  KP4_SAFE_CALL_TAC "H_X4"
    ([e; x 0; x 1; x 2; x 3; x 4] @ map (fun m -> KP4_SEED m 2) (0--3) @
     [`k:num`; `guard:int64`] @ rest) 99 THEN
  ARM_STEPS_TAC KP4_EXEC (100--118) THEN
  MAP_EVERY (fun m -> KP4_SEED_TAC (b + 5152 + 64 * m) m 3 (st 118)) (0--3) THEN
  ARM_STEPS_TAC KP4_EXEC [119] THEN
  KP4_SAFE_CALL_TAC "H_X4"
    ([e; x 0; x 1; x 2; x 3; x 4] @ map (fun m -> KP4_SEED m 3) (0--3) @
     [`k:num`; `guard:int64`] @ rest) 120 THEN
  ARM_STEPS_TAC KP4_EXEC (121--149) THEN
  INDCPA_NONZERO_TAC 19056 (b + 2592) THEN
  KP4_SAFE_CALL_TAC "H_GETNOISE"
   ([e; x 0; x 1; x 2; x 3; x 4; `guard:int64`] @ rest) 150 THEN
  ARM_STEPS_TAC KP4_EXEC (151--162) THEN
  INDCPA_NONZERO_TAC 19056 (b + 6688) THEN
  KP4_SAFE_CALL_TAC "H_GETNOISE"
   ([e; x 0; x 1; x 2; x 3; x 4; `guard:int64`] @ rest) 163 THEN
  ARM_STEPS_TAC KP4_EXEC (164--165) THEN
  KP4_SAFE_CALL_TAC "H_NTT" ([e; x 0] @ rest) 166 THEN
  ARM_STEPS_TAC KP4_EXEC (167--169) THEN
  KP4_SAFE_CALL_TAC "H_NTT" ([e; x 0] @ rest) 170 THEN
  ARM_STEPS_TAC KP4_EXEC (171--174) THEN
  KP4_SAFE_CALL_TAC "H_MULCACHE" ([e; x 0; x 1] @ rest) 175 THEN
  MAP_EVERY (fun (s0,s1) ->
    ARM_STEPS_TAC KP4_EXEC (s0--s1) THEN
    KP4_SAFE_CALL_TAC "H_BASEMUL"
     [e; x 1; x 2; x 3; x 0; `pc:num`; `read X30 s`] (s1 + 1))
   [176,182; 184,188; 190,194; 196,200] THEN
  ARM_STEPS_TAC KP4_EXEC (202--203) THEN
  KP4_SAFE_CALL_TAC "H_TOMONT" ([e; x 0] @ rest) 204 THEN
  ARM_STEPS_TAC KP4_EXEC (205--208) THEN
  KP4_SAFE_CALL_TAC "H_ADD" ([e; x 0; x 1] @ rest) 209 THEN
  ARM_STEPS_TAC KP4_EXEC (210--211) THEN
  KP4_SAFE_CALL_TAC "H_REDUCE" ([e; x 0] @ rest) 212 THEN
  ARM_STEPS_TAC KP4_EXEC (213--214) THEN
  KP4_SAFE_CALL_TAC "H_REDUCE" ([e; x 0] @ rest) 215 THEN
  ARM_STEPS_TAC KP4_EXEC (216--218) THEN
  KP4_SAFE_CALL_TAC "H_TOBYTES" ([e; x 0; x 1] @ rest) 219 THEN
  ARM_STEPS_TAC KP4_EXEC (220--222) THEN
  KP4_SAFE_CALL_TAC "H_TOBYTES" ([e; x 0; x 1] @ rest) 223 THEN
  ARM_STEPS_TAC KP4_EXEC (224--230) THEN
  KP4_RHO_TAC "s230" THEN
  MAP_EVERY (fun (k0,k) ->
    ARM_STEPS_TAC KP4_EXEC (k0--k) THEN LIBC_PLT_TAC KP4_EXEC k THEN
    LIBC_SAFE_CALL_TAC "H_MEMSET" KP4_EXEC
     [e; x 0; x 1; x 2; `read X30 s`] (ref KP_SAFE_ALLOWED) (k + 5))
   [231,231; 237,240; 246,249; 255,259; 265,269] THEN
  ARM_STEPS_TAC KP4_EXEC (275--289) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC KP4_EXEC (290--303) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  MEMACCESS_DROP_ZERO_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC;;

let MLKEM_NATIVE_INDCPA_KEYPAIR_DERAND_K4_CLANG17_O2_IMAGE_SUBROUTINE_SAFE_STMT =
  `!mf mc ea el ev.
   memset_full_contract mf ea el ev /\ memcpy_safety_contract mc ea el ev
   ==> exists f_events.
        forall e pk sk coins (d:byte list) guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\ LENGTH d = 32 /\
          (!i j. i < 4 /\ j < 4
                 ==> mlkem_samplentt_terminates
                      (APPEND (FST(mlkem_g(APPEND d [word 4])))
                              [word j; word i])) /\
          nonoverlapping (word 0,1)
           (word_sub stackpointer (word 19056),19056) /\
          PAIRWISE nonoverlapping
           [(pk,1568); (sk,1536);
            (word_sub stackpointer (word 19056),19056)] /\
          ALLPAIRS nonoverlapping
           [(pk,1568); (sk,1536);
            (word_sub stackpointer (word 19056),19056)]
           [(coins,32); (word pc,libmlkem_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mlkem_native_libmlkem_clang17_O2_mc /\
                    read PC s = word (pc + mlkem1024_indcpa_keypair_derand) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [pk; sk; coins] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s
                     = guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(coins,32)) s = num_of_bytelist d /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    C_RETURN s = word 0 /\
                    read (memory :> bytes(word_add pk (word 1536),32)) s =
                    num_of_bytelist(FST(mlkem_g(APPEND d [word 4]))) /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events pk sk coins guard mf mc pc
                              (word_sub stackpointer (word 19056))
                              returnaddress
                              (FST(mlkem_g(APPEND d [word 4]))) /\
                       memaccess_inbounds e2
                        [coins,32; pk,1568; sk,1536;
                         word_sub stackpointer (word 19056),19056;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8;
                         word(pc + got_memcpy),8; ea,el;
                         word(pc + rodata_mlk_KeccakF_RoundConstants),192;
                         word(pc + rodata_mlk_zetas),256;
                         word(pc + mlkem_poly_cbd2_consts),
                         mlkem_poly_cbd2_consts_size;
                         word(pc + mlkem_poly_mulcache_compute_consts),
                         mlkem_poly_mulcache_compute_consts_size]
                        [pk,1568; sk,1536;
                         word_sub stackpointer (word 19056),19056]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(pk,1568); memory :> bytes(sk,1536);
                  memory :> bytes(word_sub stackpointer (word 19056),19056)])`;;

let MLKEM_NATIVE_INDCPA_KEYPAIR_DERAND_K4_CLANG17_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_INDCPA_KEYPAIR_DERAND_K4_CLANG17_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
