(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The key generation of K-PKE for ML-KEM-768 (FIPS 203 Algorithm 13).     *)
(* This is the code for mlkem768_indcpa_keypair_derand from mlkem-native's *)
(* portable C implementation compiled by clang 17 with -O2 (see            *)
(* mlkem_native/README.md). It hashes the 32-byte seed d followed by the   *)
(* byte 3 with SHA3-512 into the seeds rho and sigma, generates the matrix *)
(* in NTT form from rho with mlkem768_gen_matrix, which the code calls,    *)
(* samples the secret s and the error e from sigma and transforms them,    *)
(* computes t = A s + e in the NTT domain (one call of                     *)
(* mlkem768_polyvec_basemul_acc_montgomery_cached per row of A), and       *)
(* writes the encoding of t followed by rho as the public key and the      *)
(* encoding of s as the secret key, zeroing its buffers. The buffers are   *)
(* 32-byte aligned within the stack frame, which the code makes by         *)
(* rounding the stack pointer down, so the proof is by cases on whether    *)
(* the incoming stack pointer is a multiple of 32. It is verified in the   *)
(* whole image (see libmlkem.ml), using the theorems for mlkem_sha3_512,   *)
(* mlkem768_gen_matrix, mlkem768_poly_getnoise_eta1_4x,                    *)
(* mlkem768_polyvec_ntt, mlkem768_polyvec_mulcache_compute,                *)
(* mlkem768_polyvec_basemul_acc_montgomery_cached,                         *)
(* mlkem768_polyvec_tomont, mlkem768_polyvec_add, mlkem768_polyvec_reduce  *)
(* and mlkem768_polyvec_tobytes in the image, and the contract for memset. *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/mlkem_native/clang17_O2/sha3_512_spec.ml";;
needs "arm/proofs/mlkem_native/clang17_O2/gen_matrix_k3_spec.ml";;
needs "arm/proofs/mlkem_native/clang17_O2/poly_getnoise_eta1_4x_k3_spec.ml";;
needs "arm/proofs/mlkem_native/clang17_O2/polyvec_ntt_k3_spec.ml";;
needs "arm/proofs/mlkem_native/clang17_O2/polyvec_mulcache_compute_k3_spec.ml";;
needs "arm/proofs/mlkem_native/clang17_O2/basemul_k3_spec.ml";;
needs "arm/proofs/mlkem_native/clang17_O2/polyvec_tomont_k3_spec.ml";;
needs "arm/proofs/mlkem_native/clang17_O2/polyvec_add_k3_spec.ml";;
needs "arm/proofs/mlkem_native/clang17_O2/polyvec_reduce_k3_spec.ml";;
needs "arm/proofs/mlkem_native/clang17_O2/polyvec_tobytes_k3_spec.ml";;
needs "arm/proofs/utils/mlkem_native_indcpa.ml";;

(*** The code in the image:

    mlkem768_indcpa_keypair_derand:
       +0x0: stp     x29, x30, [sp, #-96]!
       +0x4: stp     x28, x27, [sp, #16]
       +0x8: stp     x26, x25, [sp, #32]
       +0xc: stp     x24, x23, [sp, #48]
      +0x10: stp     x22, x21, [sp, #64]
      +0x14: stp     x20, x19, [sp, #80]
      +0x18: mov     x29, sp
      +0x1c: sub     x9, sp, #0x2, lsl #12
      +0x20: sub     x9, x9, #0x7c0
      +0x24: and     sp, x9, #0xffffffffffffffe0
      +0x28: adrp    x8, <page>
      +0x2c: mov     x20, x1
      +0x30: mov     x19, x0
      +0x34: add     x23, sp, #0x2, lsl #12
      +0x38: add     x0, sp, #0x2, lsl #12
      +0x3c: add     x1, sp, #0x2, lsl #12
      +0x40: ldr     x8, [x8, #4088]
      +0x44: add     x23, x23, #0x720
      +0x48: add     x0, x0, #0x760
      +0x4c: add     x1, x1, #0x720
      +0x50: add     x22, sp, #0x2, lsl #12
      +0x54: add     x24, sp, #0x2, lsl #12
      +0x58: ldr     x8, [x8]
      +0x5c: add     x22, x22, #0x760
      +0x60: add     x21, x22, #0x20
      +0x64: add     x24, x24, #0x720
      +0x68: str     x8, [sp, #10168]
      +0x6c: mov     w8, #0x3
      +0x70: ldp     q0, q1, [x2]
      +0x74: mov     w2, #0x21
      +0x78: strb    w8, [x23, #32]
      +0x7c: str     q0, [sp, #10016]
      +0x80: str     q1, [sp, #10032]
      +0x84: bl      <mlkem_sha3_512>
      +0x88: add     x0, sp, #0x1, lsl #12
      +0x8c: add     x1, sp, #0x2, lsl #12
      +0x90: add     x0, x0, #0x520
      +0x94: add     x1, x1, #0x760
      +0x98: mov     w2, wzr
      +0x9c: add     x25, sp, #0x1, lsl #12
      +0xa0: add     x25, x25, #0x520
      +0xa4: bl      <mlkem768_gen_matrix>
      +0xa8: add     x26, sp, #0x320
      +0xac: mov     w28, #0xff
      +0xb0: add     x1, x26, #0x200
      +0xb4: add     x2, x26, #0x400
      +0xb8: add     x0, sp, #0x320
      +0xbc: mov     x3, xzr
      +0xc0: mov     x4, x21
      +0xc4: mov     w5, wzr
      +0xc8: mov     w6, #0x1
      +0xcc: mov     w7, #0x2
      +0xd0: strb    w28, [sp]
      +0xd4: bl      <mlkem768_poly_getnoise_eta1_4x>
      +0xd8: add     x27, sp, #0xf20
      +0xdc: add     x0, sp, #0xf20
      +0xe0: add     x1, x27, #0x200
      +0xe4: add     x2, x27, #0x400
      +0xe8: mov     x3, xzr
      +0xec: mov     x4, x21
      +0xf0: mov     w5, #0x3
      +0xf4: mov     w6, #0x4
      +0xf8: mov     w7, #0x5
      +0xfc: strb    w28, [sp]
     +0x100: bl      <mlkem768_poly_getnoise_eta1_4x>
     +0x104: add     x0, sp, #0x320
     +0x108: bl      <mlkem768_polyvec_ntt>
     +0x10c: add     x0, sp, #0xf20
     +0x110: bl      <mlkem768_polyvec_ntt>
     +0x114: add     x0, sp, #0x20
     +0x118: add     x1, sp, #0x320
     +0x11c: add     x28, sp, #0x20
     +0x120: bl      <mlkem768_polyvec_mulcache_compute>
     +0x124: add     x1, sp, #0x1, lsl #12
     +0x128: add     x0, sp, #0x920
     +0x12c: add     x1, x1, #0x520
     +0x130: add     x2, sp, #0x320
     +0x134: add     x3, sp, #0x20
     +0x138: add     x21, sp, #0x920
     +0x13c: bl      <mlkem768_polyvec_basemul_acc_montgomery_cached>
     +0x140: add     x0, x21, #0x200
     +0x144: add     x1, x25, #0x600
     +0x148: add     x2, sp, #0x320
     +0x14c: add     x3, sp, #0x20
     +0x150: bl      <mlkem768_polyvec_basemul_acc_montgomery_cached>
     +0x154: add     x0, x21, #0x400
     +0x158: add     x1, x25, #0xc00
     +0x15c: add     x2, sp, #0x320
     +0x160: add     x3, sp, #0x20
     +0x164: bl      <mlkem768_polyvec_basemul_acc_montgomery_cached>
     +0x168: add     x0, sp, #0x920
     +0x16c: bl      <mlkem768_polyvec_tomont>
     +0x170: add     x0, sp, #0x920
     +0x174: add     x1, sp, #0xf20
     +0x178: bl      <mlkem768_polyvec_add>
     +0x17c: add     x0, sp, #0x920
     +0x180: bl      <mlkem768_polyvec_reduce>
     +0x184: add     x0, sp, #0x320
     +0x188: bl      <mlkem768_polyvec_reduce>
     +0x18c: add     x1, sp, #0x320
     +0x190: mov     x0, x20
     +0x194: bl      <mlkem768_polyvec_tobytes>
     +0x198: add     x1, sp, #0x920
     +0x19c: mov     x0, x19
     +0x1a0: bl      <mlkem768_polyvec_tobytes>
     +0x1a4: ldr     q0, [sp, #10080]
     +0x1a8: add     x0, sp, #0x20
     +0x1ac: ldr     q1, [sp, #10096]
     +0x1b0: mov     w1, wzr
     +0x1b4: mov     w2, #0x300
     +0x1b8: str     q0, [x19, #1152]
     +0x1bc: str     q1, [x19, #1168]
     +0x1c0: bl      <memset@plt>
     +0x1c4: add     x0, sp, #0x320
     +0x1c8: mov     w1, wzr
     +0x1cc: mov     w2, #0x600
     +0x1d0: bl      <memset@plt>
     +0x1d4: add     x0, sp, #0x920
     +0x1d8: mov     w1, wzr
     +0x1dc: mov     w2, #0x600
     +0x1e0: bl      <memset@plt>
     +0x1e4: add     x0, sp, #0xf20
     +0x1e8: mov     w1, wzr
     +0x1ec: mov     w2, #0x600
     +0x1f0: bl      <memset@plt>
     +0x1f4: add     x0, sp, #0x1, lsl #12
     +0x1f8: add     x0, x0, #0x520
     +0x1fc: mov     w1, wzr
     +0x200: mov     w2, #0x1200
     +0x204: bl      <memset@plt>
     +0x208: movi    v0.2d, #0x0
     +0x20c: strb    wzr, [x23, #32]
     +0x210: adrp    x8, <page>
     +0x214: str     q0, [sp, #10032]
     +0x218: str     q0, [sp, #10016]
     +0x21c: str     q0, [sp, #10128]
     +0x220: str     q0, [sp, #10112]
     +0x224: str     q0, [sp, #10096]
     +0x228: str     q0, [sp, #10080]
     +0x22c: ldr     x8, [x8, #4088]
     +0x230: ldr     x9, [sp, #10168]
     +0x234: ldr     x8, [x8]
     +0x238: cmp     x8, x9
     +0x23c: b.ne    <mlkem768_indcpa_keypair_derand+0x264>
     +0x240: mov     w0, wzr
     +0x244: mov     sp, x29
     +0x248: ldp     x20, x19, [sp, #80]
     +0x24c: ldp     x22, x21, [sp, #64]
     +0x250: ldp     x24, x23, [sp, #48]
     +0x254: ldp     x26, x25, [sp, #32]
     +0x258: ldp     x28, x27, [sp, #16]
     +0x25c: ldp     x29, x30, [sp], #96
     +0x260: ret
     +0x264: bl      <__stack_chk_fail@plt>
 ***)

let MLKEM_NATIVE_INDCPA_KEYPAIR_DERAND_K3_CLANG17_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_clang17_O2_mc
   [layout_range "plt_memset"; layout_range "mlkem768_indcpa_keypair_derand"];;

let KP3_EXEC = MLKEM_NATIVE_INDCPA_KEYPAIR_DERAND_K3_CLANG17_O2_EXEC;;

(* ------------------------------------------------------------------------- *)
(* The key generation in FIPS 203 in terms of the coefficients computed by   *)
(* the code: those of the NTTs of s and e, those of the multiplication       *)
(* cache, those of the matrix-vector product in Montgomery form, and those   *)
(* of the final results after Montgomery conversion, addition and reduction. *)
(* The two lemmas on single coefficients relate the computation of the code  *)
(* to MultiplyNTTs and the addition of e in the NTT domain, for even and odd *)
(* coefficients.                                                             *)
(* ------------------------------------------------------------------------- *)

let KPKE_KEYGEN_COEFF_EVEN_K3_STMT =
  `!(A:num->num->int) (Y:num->num->int) (YT:num->int) (SH:num->num->int)
    (t:int) (u:int) (e:int) (eh:int) p.
     (!j. j < 3 ==> (Y j (2 * p) == SH j (2 * p)) (mod &3329) /\
                    (Y j (2 * p + 1) == SH j (2 * p + 1)) (mod &3329) /\
                    (YT j == Y j (2 * p + 1) *
                             &17 pow (2 * bitreverse7 p + 1)) (mod &3329)) /\
     (t == &169 * ((A 2 (2 * p + 1) * YT 2 + A 2 (2 * p) * Y 2 (2 * p)) +
                   (A 1 (2 * p + 1) * YT 1 + A 1 (2 * p) * Y 1 (2 * p)) +
                   (A 0 (2 * p + 1) * YT 0 + A 0 (2 * p) * Y 0 (2 * p))))
     (mod &3329) /\
     (u == &65536 * t) (mod &3329) /\
     (e == eh) (mod &3329)
     ==> (u + e) rem &3329 =
         ring_add mlkem_zq
          (ring_sum mlkem_zq {j | j < 3}
             (\j. fips203_multiply_ntts (A j) (SH j) (2 * p)))
          eh`;;

let KPKE_KEYGEN_COEFF_EVEN_K3 = assume_spec KPKE_KEYGEN_COEFF_EVEN_K3_STMT;;

let KPKE_KEYGEN_COEFF_ODD_K3_STMT =
  `!(A:num->num->int) (Y:num->num->int) (SH:num->num->int)
    (t:int) (u:int) (e:int) (eh:int) p.
     (!j. j < 3 ==> (Y j (2 * p) == SH j (2 * p)) (mod &3329) /\
                    (Y j (2 * p + 1) == SH j (2 * p + 1)) (mod &3329)) /\
     (t == &169 *
           ((A 2 (2 * p + 1) * Y 2 (2 * p) + A 2 (2 * p) * Y 2 (2 * p + 1)) +
            (A 1 (2 * p + 1) * Y 1 (2 * p) + A 1 (2 * p) * Y 1 (2 * p + 1)) +
            (A 0 (2 * p + 1) * Y 0 (2 * p) + A 0 (2 * p) * Y 0 (2 * p + 1))))
     (mod &3329) /\
     (u == &65536 * t) (mod &3329) /\
     (e == eh) (mod &3329)
     ==> (u + e) rem &3329 =
         ring_add mlkem_zq
          (ring_sum mlkem_zq {j | j < 3}
             (\j. fips203_multiply_ntts (A j) (SH j) (2 * p + 1)))
          eh`;;

let KPKE_KEYGEN_COEFF_ODD_K3 = assume_spec KPKE_KEYGEN_COEFF_ODD_K3_STMT;;

let KPKE_KEYGEN_K3_RESULT_STMT =
  `!d rho sigma (sh:num->int16) (eh:num->int16) (mc:num->int16)
    (pt:num->int16) (pt2:num->int16) (tr:num->int16) (sr:num->int16).
     mlkem_g(APPEND d [word 3]) = rho,sigma /\
     (!i j n. i < 3 /\ j < 3 /\ n < 256
              ==> mlkem_sample_ntt (APPEND rho [word j; word i]) n < &3329) /\
     (!j i. j < 3 /\ i < 256
            ==> (ival(sh(256 * j + i)) ==
                 mlkem_ntt (mlkem_cbd 2 (mlkem_prf 2 sigma (word j))) i)
                (mod &3329) /\
                abs(ival(sh(256 * j + i))) <= &23594) /\
     (!j i. j < 3 /\ i < 256
            ==> (ival(eh(256 * j + i)) ==
                 mlkem_ntt (mlkem_cbd 2 (mlkem_prf 2 sigma (word(3 + j)))) i)
                (mod &3329) /\
                abs(ival(eh(256 * j + i))) <= &23594) /\
     (!j p. j < 3 /\ p < 128
            ==> (ival(mc(128 * j + p)) ==
                 ival(sh(256 * j + 2 * p + 1)) *
                 &17 pow (2 * bitreverse7 p + 1)) (mod &3329)) /\
     (!r p. r < 3 /\ p < 128
            ==> (ival(pt(256 * r + 2 * p)) ==
                 &169 *
                 ((mlkem_sample_ntt (APPEND rho [word 2; word r]) (2 * p + 1) *
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
                 ((mlkem_sample_ntt (APPEND rho [word 2; word r]) (2 * p + 1) *
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
     (!i. i < 768 ==> (ival(pt2 i) == &65536 * ival(pt i)) (mod &3329) /\
                      abs(ival(pt2 i)) <= &3328) /\
     (!i. i < 768 ==> ival(tr i) = ival(word_add (pt2 i) (eh i)) rem &3329) /\
     (!i. i < 768 ==> ival(sr i) = ival(sh i) rem &3329)
     ==> num_of_wordlist(MAP (word_zx:int16->12 word) (list_of_seq tr 768)) +
         2 EXP (8 * 1152) * num_of_bytelist rho =
         num_of_bytelist(FST(kpke_keygen mlkem768 d)) /\
         num_of_wordlist(MAP (word_zx:int16->12 word) (list_of_seq sr 768)) =
         num_of_bytelist(SND(kpke_keygen mlkem768 d))`;;

let KPKE_KEYGEN_K3_RESULT = assume_spec KPKE_KEYGEN_K3_RESULT_STMT;;

(* ------------------------------------------------------------------------- *)
(* The buffers are aligned to 32 bytes within the stack frame, so their      *)
(* addresses depend on whether the stack pointer is a multiple of 32 or just *)
(* of 16. The input to SHA3-512 is the seed copied as two 128-bit words and  *)
(* the byte 3 (the parameter k), and its output is the two seeds rho and     *)
(* sigma as in mlkem_g.                                                      *)
(* ------------------------------------------------------------------------- *)

let KP3_BUFFER_ADDRESS_STMT =
  `!sp:int64.
        aligned 16 sp
        ==> word_and (word_add sp (word 3776)) (word 18446744073709551584) =
            word_add sp (word(if aligned 32 sp then 3776 else 3760))`;;

let KP3_BUFFER_ADDRESS = assume_spec KP3_BUFFER_ADDRESS_STMT;;

let KP3_BUFFER_TAC =
  FIRST_ASSUM(fun th ->
    if concl th = `aligned 32 (stackpointer:int64)` ||
       concl th = `~aligned 32 (stackpointer:int64)`
    then SUBST_ALL_TAC
          (REWRITE_RULE[th; ASSUME `aligned 16 (stackpointer:int64)`]
            (SPEC `stackpointer:int64` KP3_BUFFER_ADDRESS))
    else NO_TAC);;

let KP3_INPUT_STMT =
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

let KP3_INPUT = assume_spec KP3_INPUT_STMT;;

let KP3_INPUT_TAC b s =
  MP_TAC(SPECL [INDCPA_SP(b + 10016); `d:byte list`; `3`; s] KP3_INPUT) THEN
  ANTS_TAC THENL
   [CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[];
    STRIP_TAC];;

let KP3_G_TAC =
  FIRST_ASSUM(fun th ->
    if can (term_match []
             `read (memory :> bytes(a,64)) s = num_of_bytelist(sha3_512 c)`)
           (concl th)
    then ASSUME_TAC th THEN
         MP_TAC(CONV_RULE(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)
                 (REWRITE_RULE
                   [ASSUME `FST(mlkem_g(APPEND d [word 3])) = rho`;
                    ASSUME `SND(mlkem_g(APPEND d [word 3])) = sigma`]
                   (MATCH_MP MLKEM_G_BYTES th))) THEN
         CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN STRIP_TAC
    else NO_TAC);;

(* ------------------------------------------------------------------------- *)
(* The callees. The matrix is generated without transposition, and the       *)
(* fourth output of mlkem768_poly_getnoise_eta1_4x is a null pointer (its    *)
(* fourth nonce, at the bottom of the stack, is 255), so the theorems are    *)
(* specialized to those cases. The theorem for                               *)
(* mlkem768_polyvec_basemul_acc_montgomery_cached is used with its           *)
(* hypotheses as conjunctions.                                               *)
(* ------------------------------------------------------------------------- *)

let LOCAL_SHA3_512_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_clang17_O2_mc,KP3_EXEC,
    0x0,mlkem_native_libmlkem_clang17_O2_mc,
    MLKEM_NATIVE_SHA3_512_CLANG17_O2_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_GEN_MATRIX_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_clang17_O2_mc,KP3_EXEC,
    0x0,mlkem_native_libmlkem_clang17_O2_mc,
    INDCPA_GEN_MATRIX_SPEC
      MLKEM_NATIVE_GEN_MATRIX_K3_CLANG17_O2_IMAGE_SUBROUTINE_CORRECT
      `word 0:int64`);;

let LOCAL_GETNOISE_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_clang17_O2_mc,KP3_EXEC,
    0x0,mlkem_native_libmlkem_clang17_O2_mc,
    INDCPA_GETNOISE_NULL
     MLKEM_NATIVE_POLY_GETNOISE_ETA1_4X_K3_CLANG17_O2_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_POLYVEC_NTT_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_clang17_O2_mc,KP3_EXEC,
    0x0,mlkem_native_libmlkem_clang17_O2_mc,
    MLKEM_NATIVE_POLYVEC_NTT_K3_CLANG17_O2_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_POLYVEC_MULCACHE_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_clang17_O2_mc,KP3_EXEC,
    0x0,mlkem_native_libmlkem_clang17_O2_mc,
    MLKEM_NATIVE_POLYVEC_MULCACHE_COMPUTE_K3_CLANG17_O2_IMAGE_SUBROUTINE_CORRECT
   );;

let LOCAL_BASEMUL_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_clang17_O2_mc,KP3_EXEC,
    0x0,mlkem_native_libmlkem_clang17_O2_mc,
    REWRITE_RULE[ALL]
      MLKEM_NATIVE_BASEMUL_K3_CLANG17_O2_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_POLYVEC_TOMONT_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_clang17_O2_mc,KP3_EXEC,
    0x0,mlkem_native_libmlkem_clang17_O2_mc,
    MLKEM_NATIVE_POLYVEC_TOMONT_K3_CLANG17_O2_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_POLYVEC_ADD_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_clang17_O2_mc,KP3_EXEC,
    0x0,mlkem_native_libmlkem_clang17_O2_mc,
    MLKEM_NATIVE_POLYVEC_ADD_K3_CLANG17_O2_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_POLYVEC_REDUCE_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_clang17_O2_mc,KP3_EXEC,
    0x0,mlkem_native_libmlkem_clang17_O2_mc,
    MLKEM_NATIVE_POLYVEC_REDUCE_K3_CLANG17_O2_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_POLYVEC_TOBYTES_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_clang17_O2_mc,KP3_EXEC,
    0x0,mlkem_native_libmlkem_clang17_O2_mc,
    MLKEM_NATIVE_POLYVEC_TOBYTES_K3_CLANG17_O2_IMAGE_SUBROUTINE_CORRECT);;

(* ------------------------------------------------------------------------- *)
(* The facts about the stages of the computation other than those given by   *)
(* the tactics in mlkem_native_indcpa.ml: the coefficients of the matrix as  *)
(* given by SampleNTT, the bounds on the inputs of the multiplications, the  *)
(* rows of the matrix-vector product, and rho in the public key.             *)
(* ------------------------------------------------------------------------- *)

let KP3_MATRIX_TAC b s =
  let addr = parse_term(Printf.sprintf
    "word_add stackpointer (word (%d + 512 * (3 * r + j))):int64" b) in
  SUBGOAL_THEN
   `!r j n. r < 3 /\ j < 3 /\ n < 256
            ==> &0 <= mlkem_sample_ntt (APPEND rho [word j; word r]) n /\
                mlkem_sample_ntt (APPEND rho [word j; word r]) n < &3329`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    MATCH_MP_TAC MLKEM_SAMPLE_NTT_REJ_BOUND THEN
    EXISTS_TAC `k:num` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!r j n. r < 3 /\ j < 3 /\ n < 256
            ==> ival((AM:num->int16)(768 * r + 256 * j + n)) =
                mlkem_sample_ntt (APPEND rho [word j; word r]) n`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    INDCPA_GHOST_SPEC_TAC "AM" `768 * r + 256 * j + n` THEN
    MP_TAC(SPECL [addr; s; `APPEND (rho:byte list) [word j; word r]`;
                  `k:num`; `n:num`]
                 MLKEM_NATIVE_SAMPLE_COEFF) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
    AP_TERM_TAC THEN REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    MATCH_MP_TAC READ16_OFFSET_EQ THEN ARITH_TAC;
    ALL_TAC];;

let KP3_AM_INST r j =
  let th = SPECL [mk_small_numeral r; mk_small_numeral j]
    (ASSUME `!r j n. r < 3 /\ j < 3 /\ n < 256
                     ==> ival((AM:num->int16)(768 * r + 256 * j + n)) =
                         mlkem_sample_ntt (APPEND rho [word j; word r]) n`) in
  CONV_RULE(NUM_REDUCE_CONV THENC REWRITE_CONV[ADD_CLAUSES; ADD_ASSOC] THENC
            NUM_REDUCE_CONV) th;;

let KP3_PT_GOAL = `!r p. r < 3 /\ p < 128
            ==> (ival((PT:num->int16)(256 * r + 2 * p)) ==
                 &169 *
                 ((mlkem_sample_ntt (APPEND rho [word 2; word r]) (2 * p + 1) *
                   ival((MC:num->int16)(256 + p)) +
                   mlkem_sample_ntt (APPEND rho [word 2; word r]) (2 * p) *
                   ival((SH:num->int16)(512 + 2 * p))) +
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
                 ((mlkem_sample_ntt (APPEND rho [word 2; word r]) (2 * p + 1) *
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

let KP3_AM_BOUND_TAC =
  SUBGOAL_THEN `!m. m < 2304 ==> abs(ival((AM:num->int16) m)) <= &2 pow 12`
  (LABEL_TAC "ambound") THENL
   [X_GEN_TAC `m:num` THEN DISCH_TAC THEN
    MP_TAC(SPECL [`768`; `3`; `m:num`] EXISTS_DIV_MOD_LT) THEN
    ASM_REWRITE_TAC[ARITH_RULE `768 * 3 = 2304`; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`r:num`; `q:num`] THEN STRIP_TAC THEN
    MP_TAC(SPECL [`256`; `3`; `q:num`] EXISTS_DIV_MOD_LT) THEN
    ASM_REWRITE_TAC[ARITH_RULE `256 * 3 = 768`; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`j:num`; `n:num`] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC(INT_ARITH
     `&0 <= x /\ x < &3329 ==> abs(x:int) <= &2 pow 12`) THEN
    ASM_SIMP_TAC[];
    ALL_TAC];;

let KP3_BASEMUL_DEFS =
  [basemul3_even; basemul3_odd; pmul_acc3; pmull_acc3; pmull];;

let KP3_PT_TAC b =
  INDCPA_GHOST_TAC "PT" (b + 2336) 768 "s100" THEN
  SUBGOAL_THEN KP3_PT_GOAL ASSUME_TAC THENL
   [REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
    CONV_TAC EXPAND_CASES_CONV THEN REPEAT CONJ_TAC THENL
     (map (fun r -> INDCPA_BASEMUL3_ROW_TAC "PT" (b + 2336 + 512 * r)
                     "ambound" (map (KP3_AM_INST r) [0;1;2])
                     KP3_BASEMUL_DEFS) [0;1;2]);
    ALL_TAC];;

let KP3_RHO_HALVES_TAC b =
  FIRST_ASSUM(MP_TAC o MATCH_MP GENMAT_BYTES128_HALVES o check (fun th ->
    can (term_match [] (subst [INDCPA_SP(b + 10080),`a:int64`]
      `read (memory :> bytes(a,32)) s = num_of_bytelist rho`))
      (concl th))) THEN
  CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN STRIP_TAC;;

let KP3_RHO_TAC s =
  MP_TAC(SPECL [`word_add pk (word 1152):int64`; `num_of_bytelist rho`;
                mk_var(s,`:armstate`)] GENMAT_BYTES_32_OF_HALVES) THEN
  ANTS_TAC THENL
   [CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `rho:byte list` NUM_OF_BYTELIST_BOUND) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];
    DISCH_TAC];;

let KP3_FINAL_TAC =
  REWRITE_TAC[ARITH_RULE `1184 = 1152 + 32`; READ_COMPONENT_COMPOSE;
              READ_BYTES_COMBINE] THEN
  REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`d:byte list`; `rho:byte list`; `sigma:byte list`;
                `SH:num->int16`; `EH:num->int16`; `MC:num->int16`;
                `PT:num->int16`; `PT2:num->int16`; `TR:num->int16`;
                `SR:num->int16`] KPKE_KEYGEN_K3_RESULT) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REWRITE_TAC[GSYM(ASSUME `FST(mlkem_g(APPEND d [word 3])) = rho`);
                  GSYM(ASSUME `SND(mlkem_g(APPEND d [word 3])) = sigma`);
                  PAIR];
      REPEAT STRIP_TAC THEN ASM_SIMP_TAC[];
      ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[]];
    SIMP_TAC[]];;

(* ------------------------------------------------------------------------- *)
(* Correctness proof, assuming the contracts for memset and memcpy (the    *)
(* latter for the callees). The seed d is 32 bytes at coins, and the       *)
(* public key of 1184 bytes at pk and the secret key of 1152 bytes at sk   *)
(* are those of kpke_keygen mlkem768 d in common/fips203/fips203.ml. The   *)
(* theorem assumes that SampleNTT terminates for each entry of the matrix, *)
(* which means that the output of SHAKE128 for it has 256 fields < q, as   *)
(* for mlkem768_gen_matrix, and that the stack does not contain address 0. *)
(* The stack is the 10288 bytes of the function (96 of saved registers,    *)
(* the buffers and the canary, and 16 for the alignment) and the 3760 used *)
(* by mlkem768_gen_matrix below them. The proof is by cases on whether the *)
(* stack pointer is a multiple of 32, which gives the address b of the     *)
(* buffers, at offsets 0 (the fourth nonce), 32 (the multiplication        *)
(* cache), 800 (s), 2336 (t), 3872 (e), 5408 (the matrix), 10016 (the      *)
(* input of SHA3-512) and 10080 (rho and sigma).                           *)
(* ------------------------------------------------------------------------- *)

let KP3_INTRO_TAC =
  MAP_EVERY X_GEN_TAC
   [`pk:int64`; `sk:int64`; `coins:int64`; `d:byte list`; `guard:int64`;
    `mf:int64`; `mc:int64`; `ea:int64`; `el:num`; `ev:num`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 14048 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `aligned 16 (stackpointer:int64)` ASSUME_TAC THENL
   [UNDISCH_TAC `aligned 16 (word_add stackpointer (word 14048):int64)` THEN
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
               (APPEND (FST(mlkem_g(APPEND d [word 3])))
                       [word j; word i])` THEN
  ABBREV_TAC `rho = FST(mlkem_g(APPEND d [word 3]))` THEN
  ABBREV_TAC `sigma = SND(mlkem_g(APPEND d [word 3]))` THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`3`; `\i j. APPEND (rho:byte list) [word j; word (i:num)]`]
                MLKEM_SAMPLENTT_TERMINATES_UNIFORM) THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `k:num`) THEN
  SUBGOAL_THEN `LENGTH(rho:byte list) = 32 /\ LENGTH(sigma:byte list) = 32`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["rho"; "sigma"] THEN REWRITE_TAC[LENGTH_MLKEM_G];
    ALL_TAC];;

let KP3_CASE_TAC b =
  let st n = "s"^string_of_int n in
  ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP GENMAT_BYTES128_HALVES o check
   (can (term_match [] `read (memory :> bytes(coins,32)) s = n`) o concl)) THEN
  STRIP_TAC THEN

  (*** The setup, the input to SHA3-512 and the call ***)

  ARM_STEPS_TAC KP3_EXEC (1--10) THEN KP3_BUFFER_TAC THEN
  ARM_STEPS_TAC KP3_EXEC (11--11) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC KP3_EXEC (12--33) THEN
  KP3_INPUT_TAC b `s33:armstate` THEN INDCPA_GOT_TAC THEN
  ARM_STEPS_TAC KP3_EXEC [34] THEN
  LOCAL_SHA3_512_TAC
   [`read X0 s`; `read X1 s`; `APPEND d [word 3]:byte list`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 35 THEN
  KP3_G_TAC THEN KP3_RHO_HALVES_TAC b THEN

  (*** The matrix ***)

  ARM_STEPS_TAC KP3_EXEC (36--43) THEN
  LOCAL_GEN_MATRIX_TAC
   [`read X0 s`; `read X1 s`; `rho:byte list`; `k:num`; `guard:int64`;
    `mf:int64`; `ea:int64`; `el:num`; `ev:num`; `pc:num`; `read SP s`;
    `read X30 s`] 44 THEN
  INDCPA_GHOST_TAC "AM" (b + 5408) 2304 (st 44) THEN
  KP3_MATRIX_TAC (b + 5408) `s44:armstate` THEN

  (*** The noise ***)

  ARM_STEPS_TAC KP3_EXEC (45--55) THEN INDCPA_NONCE_TAC 255 THEN
  ARM_STEPS_TAC KP3_EXEC [56] THEN
  LOCAL_GETNOISE_TAC
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X4 s`;
    `sigma:byte list`; `read X5 s`; `read X6 s`; `read X7 s`;
    `word 255:int64`; `guard:int64`; `mf:int64`; `mc:int64`; `ea:int64`;
    `el:num`; `ev:num`; `pc:num`; `read SP s`; `read X30 s`] 57 THEN
  INDCPA_NOISE_TAC "S0" (b + 800) 3 "sigma" "word j" (st 57) THEN
  ARM_STEPS_TAC KP3_EXEC (58--68) THEN
  LOCAL_GETNOISE_TAC
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X4 s`;
    `sigma:byte list`; `read X5 s`; `read X6 s`; `read X7 s`;
    `word 255:int64`; `guard:int64`; `mf:int64`; `mc:int64`; `ea:int64`;
    `el:num`; `ev:num`; `pc:num`; `read SP s`; `read X30 s`] 69 THEN
  INDCPA_NOISE_TAC "E0" (b + 3872) 3 "sigma" "word(3 + j)" (st 69) THEN
  INDCPA_DISCARD_LETS_TAC THEN

  (*** The NTTs and the multiplication cache ***)

  ARM_STEPS_TAC KP3_EXEC (70--71) THEN
  LOCAL_POLYVEC_NTT_TAC
   [`read X0 s`; `S0:num->int16`; `pc:num`; `read SP s`; `read X30 s`] 72 THEN
  INDCPA_NTT_TAC "SH" (b + 800) 3 "S0" "sigma" "word j" (st 72) THEN
  ARM_STEPS_TAC KP3_EXEC (73--74) THEN
  LOCAL_POLYVEC_NTT_TAC
   [`read X0 s`; `E0:num->int16`; `pc:num`; `read SP s`; `read X30 s`] 75 THEN
  INDCPA_NTT_TAC "EH" (b + 3872) 3 "E0" "sigma" "word(3 + j)"
    (st 75) THEN
  ARM_STEPS_TAC KP3_EXEC (76--79) THEN
  LOCAL_POLYVEC_MULCACHE_TAC
   [`read X0 s`; `read X1 s`; `SH:num->int16`; `pc:num`; `read SP s`;
    `read X30 s`] 80 THEN
  INDCPA_MULCACHE_TAC "MC" (b + 32) 3 "SH" (st 80) THEN

  (*** The matrix-vector product, one row per call ***)

  MAP_EVERY (fun (r,s0,s1) ->
    let a = (b + 5408 + 1536 * r,"AM",768 * r)
    and y = (b + 800,"SH") and t = (b + 32,"MC") in
    ARM_STEPS_TAC KP3_EXEC (s0--s1) THEN
    INDCPA_BASEMUL3_PRE_TAC a y t (st s1) THEN
    LOCAL_BASEMUL_TAC (INDCPA_BASEMUL3_ARGS ("AM",768 * r) "SH" "MC")
      (s1 + 1) THEN
    INDCPA_BASEMUL3_DROP_PRE_TAC a y t) [0,81,87; 1,89,93; 2,95,99] THEN
  KP3_AM_BOUND_TAC THEN KP3_PT_TAC b THEN

  (*** Montgomery form, adding the noise, the reductions ***)

  ARM_STEPS_TAC KP3_EXEC (101--102) THEN
  LOCAL_POLYVEC_TOMONT_TAC
   [`read X0 s`; `PT:num->int16`; `pc:num`; `read SP s`; `read X30 s`] 103 THEN
  INDCPA_TOMONT_TAC "PT2" (b + 2336) 768 "PT" (st 103) THEN
  ARM_STEPS_TAC KP3_EXEC (104--106) THEN
  LOCAL_POLYVEC_ADD_TAC
   [`read X0 s`; `read X1 s`; `PT2:num->int16`; `EH:num->int16`; `pc:num`;
    `read SP s`; `read X30 s`] 107 THEN
  ARM_STEPS_TAC KP3_EXEC (108--109) THEN
  LOCAL_POLYVEC_REDUCE_TAC
   [`read X0 s`; `\i. word_add ((PT2:num->int16) i) ((EH:num->int16) i)`;
    `pc:num`; `read SP s`; `read X30 s`] 110 THEN
  INDCPA_REDUCE_TAC "TR" (b + 2336) 768
    "word_add ((PT2:num->int16) i) ((EH:num->int16) i)" (st 110) THEN
  ARM_STEPS_TAC KP3_EXEC (111--112) THEN
  LOCAL_POLYVEC_REDUCE_TAC
   [`read X0 s`; `SH:num->int16`; `pc:num`; `read SP s`; `read X30 s`] 113 THEN
  INDCPA_REDUCE_TAC "SR" (b + 800) 768 "(SH:num->int16) i" (st 113) THEN

  (*** The encodings of the keys ***)

  ARM_STEPS_TAC KP3_EXEC (114--116) THEN
  INDCPA_TOBYTES_PRE_TAC "SR" (b + 800) 768 (st 116) THEN
  LOCAL_POLYVEC_TOBYTES_TAC
   [`read X0 s`; `read X1 s`; `list_of_seq (SR:num->int16) 768`; `pc:num`;
    `read SP s`; `read X30 s`] 117 THEN
  INDCPA_TOBYTES_POST_TAC "SR" 768 `\i. ival((SH:num->int16) i)` THEN
  ARM_STEPS_TAC KP3_EXEC (118--120) THEN
  INDCPA_TOBYTES_PRE_TAC "TR" (b + 2336) 768 (st 120) THEN
  LOCAL_POLYVEC_TOBYTES_TAC
   [`read X0 s`; `read X1 s`; `list_of_seq (TR:num->int16) 768`; `pc:num`;
    `read SP s`; `read X30 s`] 121 THEN
  INDCPA_TOBYTES_POST_TAC "TR" 768
    `\i. ival(word_add ((PT2:num->int16) i) ((EH:num->int16) i))` THEN
  ARM_STEPS_TAC KP3_EXEC (122--128) THEN KP3_RHO_TAC (st 128) THEN

  (*** Zeroing the buffers, the stack guard, the return ***)

  INDCPA_MEMSET_LABEL_TAC THEN
  INDCPA_MEMSETS_TAC KP3_EXEC
   [129,129; 135,138; 144,147; 153,156; 162,166] THEN
  ARM_STEPS_TAC KP3_EXEC (172--174) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC KP3_EXEC (175--194) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN KP3_FINAL_TAC;;

let MLKEM_NATIVE_INDCPA_KEYPAIR_DERAND_K3_CLANG17_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!pk sk coins (d:byte list) guard mf mc ea el ev pc stackpointer
    returnaddress.
        memset_contract mf ea el ev /\ memcpy_contract mc ea el ev /\
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\ LENGTH d = 32 /\
        (!i j. i < 3 /\ j < 3
               ==> mlkem_samplentt_terminates
                    (APPEND (FST(mlkem_g(APPEND d [word 3])))
                            [word j; word i])) /\
        PAIRWISE nonoverlapping
         [(pk,1184); (sk,1152); (word_sub stackpointer (word 14048),14048)] /\
        ALLPAIRS nonoverlapping
         [(pk,1184); (sk,1152); (word_sub stackpointer (word 14048),14048)]
         [(coins,32); (word pc,libmlkem_size);
          (word(pc + got_stack_chk_guard),8); (guard,8);
          (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_clang17_O2_mc /\
                  read PC s = word (pc + mlkem768_indcpa_keypair_derand) /\
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
                  read (memory :> bytes(pk,1184)) s =
                  num_of_bytelist(FST(kpke_keygen mlkem768 d)) /\
                  read (memory :> bytes(sk,1152)) s =
                  num_of_bytelist(SND(kpke_keygen mlkem768 d)) /\
                  C_RETURN s = word 0)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
              MAYCHANGE
               [memory :> bytes(pk,1184); memory :> bytes(sk,1152);
                memory :> bytes(word_sub stackpointer (word 14048),14048)])`;;

let MLKEM_NATIVE_INDCPA_KEYPAIR_DERAND_K3_CLANG17_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_INDCPA_KEYPAIR_DERAND_K3_CLANG17_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof, assuming the combined contract   *)
(* for memset (for mlkem768_gen_matrix) and the safety contract for        *)
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

let KP3_SAFE_INTRO_TAC =
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
  FIRST_X_ASSUM(fun th ->
    if can (term_match [] `memset_full_contract mf ea el ev`) (concl th)
    then ASSUME_CALLEE_SAFETY_TAILED_TAC
          (INDCPA_GEN_MATRIX_SAFE_SPEC
            (MATCH_MP MLKEM_NATIVE_GEN_MATRIX_K3_CLANG17_O2_IMAGE_SUBROUTINE_SAFE
                      th) `word 0:int64`) "H_GM" THEN
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
       "H_GETNOISE")
    else NO_TAC) THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_SHA3_512_CLANG17_O2_IMAGE_SUBROUTINE_FULL "H_SHA3" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_POLYVEC_NTT_K3_CLANG17_O2_IMAGE_SUBROUTINE_SAFE "H_NTT" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_POLYVEC_MULCACHE_COMPUTE_K3_CLANG17_O2_IMAGE_SUBROUTINE_SAFE
    "H_MULCACHE" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_BASEMUL_K3_CLANG17_O2_IMAGE_SUBROUTINE_SAFE "H_BASEMUL" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_POLYVEC_TOMONT_K3_CLANG17_O2_IMAGE_SUBROUTINE_SAFE
    "H_TOMONT" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_POLYVEC_ADD_K3_CLANG17_O2_IMAGE_SUBROUTINE_SAFE "H_ADD" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_POLYVEC_REDUCE_K3_CLANG17_O2_IMAGE_SUBROUTINE_SAFE
    "H_REDUCE" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_POLYVEC_TOBYTES_K3_CLANG17_O2_IMAGE_SUBROUTINE_SAFE
    "H_TOBYTES" THEN
  CONCRETIZE_F_EVENTS_TAC KP_SAFE_TEMPLATE THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `aligned 16 (stackpointer:int64)` ASSUME_TAC THENL
   [UNDISCH_TAC `aligned 16 (word_add stackpointer (word 14048):int64)` THEN
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
               (APPEND (FST(mlkem_g(APPEND d [word 3])))
                       [word j; word i])` THEN
  ABBREV_TAC `rho = FST(mlkem_g(APPEND d [word 3]))` THEN
  ABBREV_TAC `sigma = SND(mlkem_g(APPEND d [word 3]))` THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`3`; `\i j. APPEND (rho:byte list) [word j; word (i:num)]`]
                MLKEM_SAMPLENTT_TERMINATES_UNIFORM) THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `k:num`) THEN
  SUBGOAL_THEN `LENGTH(rho:byte list) = 32 /\ LENGTH(sigma:byte list) = 32`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["rho"; "sigma"] THEN REWRITE_TAC[LENGTH_MLKEM_G];
    ALL_TAC];;

let KP3_SAFE_CALL_TAC name ilist n =
  REMOVE_THEN name (fun safety_th ->
    ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_clang17_O2_mc,KP3_EXEC,
       0x0,mlkem_native_libmlkem_clang17_O2_mc,safety_th)
      ilist n THENL
     [EXISTS_E2_TAC (ref KP_SAFE_ALLOWED); LABEL_TAC name safety_th]);;

let KP3_SAFE_CASE_TAC b =
  let e = `e:(uarch_event)list` in
  let x n = mk_comb(mk_comb(`read:(armstate,int64)component->armstate->int64`,
                            mk_const("X"^string_of_int n,[])),`s:armstate`) in
  let rest = [`pc:num`; `read SP s`; `read X30 s`] in
  ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP GENMAT_BYTES128_HALVES o check
   (can (term_match [] `read (memory :> bytes(coins,32)) s = n`) o concl)) THEN
  STRIP_TAC THEN
  ARM_STEPS_TAC KP3_EXEC (1--10) THEN KP3_BUFFER_TAC THEN
  ARM_STEPS_TAC KP3_EXEC (11--11) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC KP3_EXEC (12--33) THEN
  KP3_INPUT_TAC b `s33:armstate` THEN INDCPA_GOT_TAC THEN
  ARM_STEPS_TAC KP3_EXEC [34] THEN
  KP3_SAFE_CALL_TAC "H_SHA3"
   ([e; x 0; x 1; `APPEND d [word 3]:byte list`; `33`; `guard:int64`] @
    rest) 35 THEN
  KP3_G_TAC THEN KP3_RHO_HALVES_TAC b THEN
  ARM_STEPS_TAC KP3_EXEC (36--43) THEN
  KP3_SAFE_CALL_TAC "H_GM"
   ([e; x 0; x 1; `rho:byte list`; `k:num`; `guard:int64`] @ rest) 44 THEN
  ARM_STEPS_TAC KP3_EXEC (45--56) THEN
  KP3_SAFE_CALL_TAC "H_GETNOISE"
   ([e; x 0; x 1; x 2; x 4; `guard:int64`] @ rest) 57 THEN
  ARM_STEPS_TAC KP3_EXEC (58--68) THEN
  KP3_SAFE_CALL_TAC "H_GETNOISE"
   ([e; x 0; x 1; x 2; x 4; `guard:int64`] @ rest) 69 THEN
  ARM_STEPS_TAC KP3_EXEC (70--71) THEN
  KP3_SAFE_CALL_TAC "H_NTT" ([e; x 0] @ rest) 72 THEN
  ARM_STEPS_TAC KP3_EXEC (73--74) THEN
  KP3_SAFE_CALL_TAC "H_NTT" ([e; x 0] @ rest) 75 THEN
  ARM_STEPS_TAC KP3_EXEC (76--79) THEN
  KP3_SAFE_CALL_TAC "H_MULCACHE" ([e; x 0; x 1] @ rest) 80 THEN
  MAP_EVERY (fun (s0,s1) ->
    ARM_STEPS_TAC KP3_EXEC (s0--s1) THEN
    KP3_SAFE_CALL_TAC "H_BASEMUL"
     [e; x 1; x 2; x 3; x 0; `pc:num`; `read X30 s`] (s1 + 1))
   [81,87; 89,93; 95,99] THEN
  ARM_STEPS_TAC KP3_EXEC (101--102) THEN
  KP3_SAFE_CALL_TAC "H_TOMONT" ([e; x 0] @ rest) 103 THEN
  ARM_STEPS_TAC KP3_EXEC (104--106) THEN
  KP3_SAFE_CALL_TAC "H_ADD" ([e; x 0; x 1] @ rest) 107 THEN
  ARM_STEPS_TAC KP3_EXEC (108--109) THEN
  KP3_SAFE_CALL_TAC "H_REDUCE" ([e; x 0] @ rest) 110 THEN
  ARM_STEPS_TAC KP3_EXEC (111--112) THEN
  KP3_SAFE_CALL_TAC "H_REDUCE" ([e; x 0] @ rest) 113 THEN
  ARM_STEPS_TAC KP3_EXEC (114--116) THEN
  KP3_SAFE_CALL_TAC "H_TOBYTES" ([e; x 0; x 1] @ rest) 117 THEN
  ARM_STEPS_TAC KP3_EXEC (118--120) THEN
  KP3_SAFE_CALL_TAC "H_TOBYTES" ([e; x 0; x 1] @ rest) 121 THEN
  ARM_STEPS_TAC KP3_EXEC (122--128) THEN
  KP3_RHO_TAC "s128" THEN
  MAP_EVERY (fun (k0,k) ->
    ARM_STEPS_TAC KP3_EXEC (k0--k) THEN LIBC_PLT_TAC KP3_EXEC k THEN
    LIBC_SAFE_CALL_TAC "H_MEMSET" KP3_EXEC
     [e; x 0; x 1; x 2; `read X30 s`] (ref KP_SAFE_ALLOWED) (k + 5))
   [129,129; 135,138; 144,147; 153,156; 162,166] THEN
  ARM_STEPS_TAC KP3_EXEC (172--174) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC KP3_EXEC (175--194) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  MEMACCESS_DROP_ZERO_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC;;

let MLKEM_NATIVE_INDCPA_KEYPAIR_DERAND_K3_CLANG17_O2_IMAGE_SUBROUTINE_SAFE_STMT =
  `!mf mc ea el ev.
   memset_full_contract mf ea el ev /\ memcpy_safety_contract mc ea el ev
   ==> exists f_events.
        forall e pk sk coins (d:byte list) guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\ LENGTH d = 32 /\
          (!i j. i < 3 /\ j < 3
                 ==> mlkem_samplentt_terminates
                      (APPEND (FST(mlkem_g(APPEND d [word 3])))
                              [word j; word i])) /\
          PAIRWISE nonoverlapping
           [(pk,1184); (sk,1152);
            (word_sub stackpointer (word 14048),14048)] /\
          ALLPAIRS nonoverlapping
           [(pk,1184); (sk,1152);
            (word_sub stackpointer (word 14048),14048)]
           [(coins,32); (word pc,libmlkem_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mlkem_native_libmlkem_clang17_O2_mc /\
                    read PC s = word (pc + mlkem768_indcpa_keypair_derand) /\
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
                    read (memory :> bytes(word_add pk (word 1152),32)) s =
                    num_of_bytelist(FST(mlkem_g(APPEND d [word 3]))) /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events pk sk coins guard mf mc pc
                              (word_sub stackpointer (word 14048))
                              returnaddress
                              (FST(mlkem_g(APPEND d [word 3]))) /\
                       memaccess_inbounds e2
                        [coins,32; pk,1184; sk,1152;
                         word_sub stackpointer (word 14048),14048;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8;
                         word(pc + got_memcpy),8; ea,el;
                         word(pc + rodata_mlk_KeccakF_RoundConstants),192;
                         word(pc + rodata_mlk_zetas),256;
                         word(pc + mlkem_poly_cbd2_consts),
                         mlkem_poly_cbd2_consts_size;
                         word(pc + mlkem_poly_mulcache_compute_consts),
                         mlkem_poly_mulcache_compute_consts_size]
                        [pk,1184; sk,1152;
                         word_sub stackpointer (word 14048),14048]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(pk,1184); memory :> bytes(sk,1152);
                  memory :> bytes(word_sub stackpointer (word 14048),14048)])`;;

let MLKEM_NATIVE_INDCPA_KEYPAIR_DERAND_K3_CLANG17_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_INDCPA_KEYPAIR_DERAND_K3_CLANG17_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
