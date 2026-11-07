(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The key generation of K-PKE for ML-KEM-1024 (FIPS 203 Algorithm 13). This *)
(* is the code for mlkem1024_indcpa_keypair_derand from mlkem-native's       *)
(* portable C implementation compiled by gcc 12 with -O3 (see                *)
(* mlkem_native/README.md). It hashes the 32-byte seed d followed by the     *)
(* byte 4 with SHA3-512 into the seeds rho and sigma, generates the matrix   *)
(* in NTT form from rho, samples the secret s and the error e from sigma and *)
(* transforms them, computes t = A s + e in the NTT domain (the products of  *)
(* the rows of A and s in a loop), and writes the encoding of t followed by  *)
(* rho as the public key and the encoding of s as the secret key, zeroing    *)
(* its buffers. It is verified in the whole image (see                       *)
(* libmlkem.ml), using the theorems for                                      *)
(* mlkem_sha3_512, mlkem1024_gen_matrix, mlkem1024_poly_getnoise_eta1_4x,    *)
(* mlkem1024_polyvec_ntt, mlkem1024_polyvec_mulcache_compute,                *)
(* mlkem1024_polyvec_basemul_acc_montgomery_cached,                          *)
(* mlkem1024_polyvec_tomont, mlkem1024_polyvec_add, mlkem1024_polyvec_reduce *)
(* and mlkem1024_polyvec_tobytes in the image, and the contract for memset.  *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/mlkem_native/gcc12_O3/sha3_512_spec.ml";;
needs "arm/proofs/mlkem_native/gcc12_O3/gen_matrix_k4_spec.ml";;
needs "arm/proofs/mlkem_native/gcc12_O3/poly_getnoise_eta1_4x_k4_spec.ml";;
needs "arm/proofs/mlkem_native/gcc12_O3/polyvec_ntt_k4_spec.ml";;
needs "arm/proofs/mlkem_native/gcc12_O3/polyvec_mulcache_compute_k4_spec.ml";;
needs "arm/proofs/mlkem_native/gcc12_O3/basemul_k4_spec.ml";;
needs "arm/proofs/mlkem_native/gcc12_O3/polyvec_tomont_k4_spec.ml";;
needs "arm/proofs/mlkem_native/gcc12_O3/polyvec_add_k4_spec.ml";;
needs "arm/proofs/mlkem_native/gcc12_O3/polyvec_reduce_k4_spec.ml";;
needs "arm/proofs/mlkem_native/gcc12_O3/polyvec_tobytes_k4_spec.ml";;
needs "arm/proofs/utils/mlkem_native_indcpa.ml";;

(*** The code in the image:

    mlkem1024_indcpa_keypair_derand:
        +0x0: mov     x12, #0x3d10
        +0x4: sub     sp, sp, x12
        +0x8: mov     x3, #0x3c40
        +0xc: mov     x4, #0x3c00
       +0x10: mov     x5, #0x3800
       +0x14: stp     x19, x20, [sp, #16]
       +0x18: mov     w19, #0x4
       +0x1c: stp     x21, x22, [sp, #32]
       +0x20: add     x21, sp, #0x9f
       +0x24: and     x21, x21, #0xffffffffffffffe0
       +0x28: stp     x23, x24, [sp, #48]
       +0x2c: add     x24, x21, x3
       +0x30: add     x23, x21, #0x3, lsl #12
       +0x34: stp     x25, x26, [sp, #64]
       +0x38: add     x22, x21, x4
       +0x3c: add     x26, x21, x5
       +0x40: stp     x27, x28, [sp, #80]
       +0x44: mov     x27, x0
       +0x48: add     x20, x21, #0x2, lsl #12
       +0x4c: str     x30, [sp, #96]
       +0x50: add     x25, x22, #0x20
       +0x54: str     x1, [sp, #120]
       +0x58: mov     x1, x24
       +0x5c: ldp     q0, q1, [x2]
       +0x60: mov     x28, x21
       +0x64: adrp    x2, <page>
       +0x68: ldr     x2, [x2, #4088]  // got_stack_chk_guard
       +0x6c: ldr     x0, [x2]
       +0x70: str     x0, [sp, #15624]
       +0x74: mov     x0, #0x0
       +0x78: stp     q0, q1, [x24]
       +0x7c: mov     x0, x22
       +0x80: mov     x2, #0x21
       +0x84: strb    w19, [x23, #3168]
       +0x88: bl      <mlkem_sha3_512>
       +0x8c: mov     x1, x22
       +0x90: mov     x0, x21
       +0x94: mov     w2, #0x0
       +0x98: bl      <mlkem1024_gen_matrix>
       +0x9c: mov     w0, #0x3
       +0xa0: strb    w0, [sp]
       +0xa4: mov     x4, x25
       +0xa8: add     x3, x20, #0x600
       +0xac: add     x2, x20, #0x400
       +0xb0: add     x1, x20, #0x200
       +0xb4: mov     x0, x20
       +0xb8: mov     w7, #0x2
       +0xbc: mov     w6, #0x1
       +0xc0: mov     w5, #0x0
       +0xc4: bl      <mlkem1024_poly_getnoise_eta1_4x>
       +0xc8: mov     x4, x25
       +0xcc: mov     w5, w19
       +0xd0: add     x1, x23, #0x200
       +0xd4: add     x3, x23, #0x600
       +0xd8: add     x2, x23, #0x400
       +0xdc: mov     x6, #0x2800
       +0xe0: mov     w0, #0x7
       +0xe4: strb    w0, [sp]
       +0xe8: mov     w7, #0x6
       +0xec: add     x25, x21, x6
       +0xf0: mov     w6, #0x5
       +0xf4: mov     x0, x23
       +0xf8: bl      <mlkem1024_poly_getnoise_eta1_4x>
       +0xfc: mov     x19, x25
      +0x100: mov     x0, x20
      +0x104: bl      <mlkem1024_polyvec_ntt>
      +0x108: mov     x0, x23
      +0x10c: bl      <mlkem1024_polyvec_ntt>
      +0x110: mov     x1, x20
      +0x114: mov     x0, x26
      +0x118: bl      <mlkem1024_polyvec_mulcache_compute>
      +0x11c: mov     x1, x28
      +0x120: mov     x0, x19
      +0x124: mov     x3, x26
      +0x128: mov     x2, x20
      +0x12c: add     x19, x19, #0x200
      +0x130: bl      <mlkem1024_polyvec_basemul_acc_montgomery_cached>
      +0x134: add     x28, x28, #0x800
      +0x138: cmp     x19, x23
      +0x13c: b.ne    <mlkem1024_indcpa_keypair_derand+0x11c>
      +0x140: mov     x0, x25
      +0x144: bl      <mlkem1024_polyvec_tomont>
      +0x148: mov     x1, x19
      +0x14c: mov     x0, x25
      +0x150: bl      <mlkem1024_polyvec_add>
      +0x154: mov     x0, x25
      +0x158: bl      <mlkem1024_polyvec_reduce>
      +0x15c: mov     x0, x20
      +0x160: bl      <mlkem1024_polyvec_reduce>
      +0x164: ldr     x0, [sp, #120]
      +0x168: mov     x1, x20
      +0x16c: bl      <mlkem1024_polyvec_tobytes>
      +0x170: mov     x1, x25
      +0x174: mov     x0, x27
      +0x178: bl      <mlkem1024_polyvec_tobytes>
      +0x17c: add     x27, x27, #0x600
      +0x180: ldp     q0, q1, [x22]
      +0x184: mov     x0, x26
      +0x188: mov     x2, #0x400
      +0x18c: mov     w1, #0x0
      +0x190: stp     q0, q1, [x27]
      +0x194: bl      <memset@plt>
      +0x198: mov     x2, #0x800
      +0x19c: mov     x0, x20
      +0x1a0: mov     w1, #0x0
      +0x1a4: bl      <memset@plt>
      +0x1a8: mov     x2, #0x800
      +0x1ac: mov     x0, x25
      +0x1b0: mov     w1, #0x0
      +0x1b4: bl      <memset@plt>
      +0x1b8: mov     x2, #0x800
      +0x1bc: mov     x0, x19
      +0x1c0: mov     w1, #0x0
      +0x1c4: bl      <memset@plt>
      +0x1c8: mov     x2, #0x2000
      +0x1cc: mov     x0, x21
      +0x1d0: mov     w1, #0x0
      +0x1d4: bl      <memset@plt>
      +0x1d8: stp     xzr, xzr, [x24]
      +0x1dc: stp     xzr, xzr, [x24, #16]
      +0x1e0: strb    wzr, [x24, #32]
      +0x1e4: movi    v0.4s, #0x0
      +0x1e8: stp     q0, q0, [x22]
      +0x1ec: stp     q0, q0, [x22, #32]
      +0x1f0: adrp    x0, <page>
      +0x1f4: ldr     x0, [x0, #4088]  // got_stack_chk_guard
      +0x1f8: ldr     x2, [sp, #15624]
      +0x1fc: ldr     x1, [x0]
      +0x200: subs    x2, x2, x1
      +0x204: mov     x1, #0x0
      +0x208: b.ne    <mlkem1024_indcpa_keypair_derand+0x234>
      +0x20c: ldp     x19, x20, [sp, #16]
      +0x210: mov     w0, #0x0
      +0x214: ldp     x21, x22, [sp, #32]
      +0x218: mov     x12, #0x3d10
      +0x21c: ldp     x23, x24, [sp, #48]
      +0x220: ldp     x25, x26, [sp, #64]
      +0x224: ldp     x27, x28, [sp, #80]
      +0x228: ldr     x30, [sp, #96]
      +0x22c: add     sp, sp, x12
      +0x230: ret
      +0x234: bl      <__stack_chk_fail@plt>
 ***)

let MLKEM_NATIVE_INDCPA_KEYPAIR_DERAND_K4_GCC12_O3_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O3_mc
   [layout_range "plt_memset";
    layout_range "mlkem1024_indcpa_keypair_derand"];;

let KP4_EXEC = MLKEM_NATIVE_INDCPA_KEYPAIR_DERAND_K4_GCC12_O3_EXEC;;

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
        ==> word_and (word_add sp (word 3839)) (word 18446744073709551584) =
            word_add sp (word(if aligned 32 sp then 3808 else 3824))`;;

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
  MP_TAC(SPECL [INDCPA_SP(b + 15424); `d:byte list`; `4`; s] KP4_INPUT) THEN
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
(* The callees. The matrix is generated without transposition, so the        *)
(* theorem for mlkem1024_gen_matrix is specialized to that case. The two     *)
(* calls of mlkem1024_poly_getnoise_eta1_4x (for s and e) have buffers in    *)
(* the stack frame as their fourth outputs, which are not null since the     *)
(* frame does not contain address 0, and their fourth nonces at the bottom   *)
(* of the stack. The theorem for                                             *)
(* mlkem1024_polyvec_basemul_acc_montgomery_cached is used with its          *)
(* hypotheses as conjunctions.                                               *)
(* ------------------------------------------------------------------------- *)

let LOCAL_SHA3_512_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O3_mc,KP4_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O3_mc,
    MLKEM_NATIVE_SHA3_512_GCC12_O3_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_GEN_MATRIX_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O3_mc,KP4_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O3_mc,
    INDCPA_GEN_MATRIX_SPEC
      MLKEM_NATIVE_GEN_MATRIX_K4_GCC12_O3_IMAGE_SUBROUTINE_CORRECT
      `word 0:int64`);;

let LOCAL_GETNOISE_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O3_mc,KP4_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O3_mc,
    MLKEM_NATIVE_POLY_GETNOISE_ETA1_4X_K4_GCC12_O3_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_POLYVEC_NTT_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O3_mc,KP4_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O3_mc,
    MLKEM_NATIVE_POLYVEC_NTT_K4_GCC12_O3_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_POLYVEC_MULCACHE_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O3_mc,KP4_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O3_mc,
    MLKEM_NATIVE_POLYVEC_MULCACHE_COMPUTE_K4_GCC12_O3_IMAGE_SUBROUTINE_CORRECT
   );;

(*** The arguments of basemul_k as INDCPA_BASEMULK_ARGS, with the stack
 *** pointer before the return address, since the theorems of basemul_k4
 *** at -O3 quantify over it ***)

let INDCPA_BASEMULK_SP_ARGS k a b t =
  let r = List.rev (INDCPA_BASEMULK_ARGS k a b t) in
  List.rev (List.hd r :: `read SP s` :: List.tl r);;

let LOCAL_BASEMUL_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O3_mc,KP4_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O3_mc,
    REWRITE_RULE[ALL]
      MLKEM_NATIVE_BASEMUL_K4_GCC12_O3_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_POLYVEC_TOMONT_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O3_mc,KP4_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O3_mc,
    MLKEM_NATIVE_POLYVEC_TOMONT_K4_GCC12_O3_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_POLYVEC_ADD_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O3_mc,KP4_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O3_mc,
    MLKEM_NATIVE_POLYVEC_ADD_K4_GCC12_O3_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_POLYVEC_REDUCE_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O3_mc,KP4_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O3_mc,
    MLKEM_NATIVE_POLYVEC_REDUCE_K4_GCC12_O3_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_POLYVEC_TOBYTES_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O3_mc,KP4_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O3_mc,
    MLKEM_NATIVE_POLYVEC_TOBYTES_K4_GCC12_O3_IMAGE_SUBROUTINE_CORRECT);;

(* ------------------------------------------------------------------------- *)
(* The facts about the stages of the computation other than those given by   *)
(* the tactics in mlkem_native_indcpa.ml: the coefficients of the matrix as  *)
(* given by SampleNTT, the bounds on the inputs of the multiplications, the  *)
(* rows of the matrix-vector product, and rho in the public key, and the     *)
(* test of the loop over the rows, whose pointers are at constant offsets    *)
(* from the stack pointer, so the loop is simply unrolled.                   *)
(* ------------------------------------------------------------------------- *)

let KP4_MATRIX_TAC b s =
  let addr = parse_term(Printf.sprintf
    "word_add stackpointer (word (%d + 512 * (4 * r + j))):int64" b) in
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
  INDCPA_GHOST_TAC "PT" (b + 10240) 1024 "s118" THEN
  SUBGOAL_THEN KP4_PT_GOAL ASSUME_TAC THENL
   [REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
    CONV_TAC EXPAND_CASES_CONV THEN REPEAT CONJ_TAC THENL
     (map (fun r -> INDCPA_BASEMULK_ROW_TAC 4 "PT" (b + 10240 + 512 * r)
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
    can (term_match [] (subst [INDCPA_SP(b + 15360),`a:int64`]
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
(* Correctness proof, assuming the contracts for memset and memcpy (the      *)
(* latter for the callees). The seed d is 32 bytes at coins, and the public  *)
(* key of 1568 bytes at pk and the secret key of 1536 bytes at sk are those  *)
(* of kpke_keygen mlkem1024 d in common/fips203.ml. The theorem assumes that *)
(* SampleNTT terminates for each entry of the matrix, which means that the   *)
(* output of SHAKE128 for it has 256 fields < q, as for                      *)
(* mlkem1024_gen_matrix, and that the stack does not contain address 0. The  *)
(* stack is the 15632 bytes of the function and the 3680 used by             *)
(* mlkem1024_gen_matrix below them. The proof is by cases on whether the     *)
(* stack pointer is a multiple of 32, which gives the address b of the       *)
(* buffers, at offsets 0 (the matrix), 8192 (s), 10240 (t), 12288 (e), 14336 *)
(* (the multiplication cache), 15360 (rho and sigma) and 15424 (the input of *)
(* SHA3-512).                                                                *)
(* ------------------------------------------------------------------------- *)

let KP4_INTRO_TAC =
  MAP_EVERY X_GEN_TAC
   [`pk:int64`; `sk:int64`; `coins:int64`; `d:byte list`; `guard:int64`;
    `mf:int64`; `mc:int64`; `ea:int64`; `el:num`; `ev:num`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 19312 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE] THEN
  REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NONOVERLAPPING_CLAUSES]) THEN
  SUBGOAL_THEN `aligned 16 (stackpointer:int64)` ASSUME_TAC THENL
   [UNDISCH_TAC `aligned 16 (word_add stackpointer (word 19312):int64)` THEN
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
     (parse_term("X"^string_of_int n))) (19--28) THEN
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
  ARM_STEPS_TAC KP4_EXEC (11--26) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC KP4_EXEC (27--34) THEN
  KP4_INPUT_TAC b `s34:armstate` THEN INDCPA_GOT_TAC THEN
  ARM_STEPS_TAC KP4_EXEC [35] THEN
  LOCAL_SHA3_512_TAC
   [`read X0 s`; `read X1 s`; `APPEND d [word 4]:byte list`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 36 THEN
  KP4_G_TAC THEN

  (*** The matrix ***)

  ARM_STEPS_TAC KP4_EXEC (37--40) THEN
  LOCAL_GEN_MATRIX_TAC
   [`read X0 s`; `read X1 s`; `rho:byte list`; `k:num`; `guard:int64`;
    `mf:int64`; `ea:int64`; `el:num`; `ev:num`; `pc:num`; `read SP s`;
    `read X30 s`] 41 THEN
  INDCPA_GHOST_TAC "AM" b 4096 (st 41) THEN
  KP4_MATRIX_TAC b `s41:armstate` THEN

  (*** The noise, s and e from two calls with four outputs ***)

  ARM_STEPS_TAC KP4_EXEC (42--52) THEN
  INDCPA_NONZERO_TAC 19312 (b + 9728) THEN INDCPA_NONCE_TAC 3 THEN
  LOCAL_GETNOISE_TAC
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X3 s`; `read X4 s`;
    `sigma:byte list`; `read X5 s`; `read X6 s`; `read X7 s`;
    `word 3:int64`; `guard:int64`; `mf:int64`; `mc:int64`; `ea:int64`;
    `el:num`; `ev:num`; `pc:num`; `read SP s`; `read X30 s`] 53 THEN
  INDCPA_NOISE_TAC "S0" (b + 8192) 4 "sigma" "word j" (st 53) THEN
  INDCPA_DISCARD_LETS_TAC THEN
  ARM_STEPS_TAC KP4_EXEC (54--66) THEN
  INDCPA_NONZERO_TAC 19312 (b + 13824) THEN INDCPA_NONCE_TAC 7 THEN
  LOCAL_GETNOISE_TAC
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X3 s`; `read X4 s`;
    `sigma:byte list`; `read X5 s`; `read X6 s`; `read X7 s`;
    `word 7:int64`; `guard:int64`; `mf:int64`; `mc:int64`; `ea:int64`;
    `el:num`; `ev:num`; `pc:num`; `read SP s`; `read X30 s`] 67 THEN
  INDCPA_NOISE_TAC "E0" (b + 12288) 4 "sigma" "word(4 + j)" (st 67) THEN
  INDCPA_DISCARD_LETS_TAC THEN

  (*** The NTTs and the multiplication cache ***)

  ARM_STEPS_TAC KP4_EXEC (68--70) THEN
  LOCAL_POLYVEC_NTT_TAC
   [`read X0 s`; `S0:num->int16`; `pc:num`; `read SP s`; `read X30 s`] 71 THEN
  INDCPA_NTT_TAC "SH" (b + 8192) 4 "S0" "sigma" "word j" (st 71) THEN
  ARM_STEPS_TAC KP4_EXEC (72--73) THEN
  LOCAL_POLYVEC_NTT_TAC
   [`read X0 s`; `E0:num->int16`; `pc:num`; `read SP s`; `read X30 s`] 74 THEN
  INDCPA_NTT_TAC "EH" (b + 12288) 4 "E0" "sigma" "word(4 + j)" (st 74) THEN
  ARM_STEPS_TAC KP4_EXEC (75--77) THEN
  LOCAL_POLYVEC_MULCACHE_TAC
   [`read X0 s`; `read X1 s`; `SH:num->int16`; `pc:num`; `read SP s`;
    `read X30 s`] 78 THEN
  INDCPA_MULCACHE_TAC "MC" (b + 14336) 4 "SH" (st 78) THEN

  (*** The matrix-vector product, one row per iteration of the loop ***)

  MAP_EVERY (fun q ->
    let a = (b + 2048 * q,"AM",1024 * q)
    and y = (b + 8192,"SH") and t = (b + 14336,"MC") in
    ARM_STEPS_TAC KP4_EXEC ((79 + 10 * q)--(84 + 10 * q)) THEN
    INDCPA_BASEMULK_PRE_TAC 4 a y t (st(84 + 10 * q)) THEN
    LOCAL_BASEMUL_TAC (INDCPA_BASEMULK_SP_ARGS 4 ("AM",1024 * q) "SH" "MC")
      (85 + 10 * q) THEN
    INDCPA_BASEMULK_DROP_PRE_TAC 4 a y t THEN
    ARM_STEPS_TAC KP4_EXEC ((86 + 10 * q)--(88 + 10 * q)) THEN
    KP4_PC_TAC (st(88 + 10 * q))) [0;1;2;3] THEN
  KP4_AM_BOUND_TAC THEN KP4_PT_TAC b THEN

  (*** Montgomery form, adding the noise, the reductions ***)

  ARM_STEPS_TAC KP4_EXEC (119--120) THEN
  LOCAL_POLYVEC_TOMONT_TAC
   [`read X0 s`; `PT:num->int16`; `pc:num`; `read SP s`; `read X30 s`] 121 THEN
  INDCPA_TOMONT_TAC "PT2" (b + 10240) 1024 "PT" (st 121) THEN
  ARM_STEPS_TAC KP4_EXEC (122--124) THEN
  LOCAL_POLYVEC_ADD_TAC
   [`read X0 s`; `read X1 s`; `PT2:num->int16`; `EH:num->int16`; `pc:num`;
    `read SP s`; `read X30 s`] 125 THEN
  ARM_STEPS_TAC KP4_EXEC (126--127) THEN
  LOCAL_POLYVEC_REDUCE_TAC
   [`read X0 s`; `\i. word_add ((PT2:num->int16) i) ((EH:num->int16) i)`;
    `pc:num`; `read SP s`; `read X30 s`] 128 THEN
  INDCPA_REDUCE_TAC "TR" (b + 10240) 1024
    "word_add ((PT2:num->int16) i) ((EH:num->int16) i)" (st 128) THEN
  ARM_STEPS_TAC KP4_EXEC (129--130) THEN
  LOCAL_POLYVEC_REDUCE_TAC
   [`read X0 s`; `SH:num->int16`; `pc:num`; `read SP s`; `read X30 s`] 131 THEN
  INDCPA_REDUCE_TAC "SR" (b + 8192) 1024 "(SH:num->int16) i" (st 131) THEN

  (*** The encodings of the keys ***)

  ARM_STEPS_TAC KP4_EXEC (132--134) THEN
  INDCPA_TOBYTES_PRE_TAC "SR" (b + 8192) 1024 (st 134) THEN
  LOCAL_POLYVEC_TOBYTES_TAC
   [`read X0 s`; `read X1 s`; `list_of_seq (SR:num->int16) 1024`; `pc:num`;
    `read SP s`; `read X30 s`] 135 THEN
  INDCPA_TOBYTES_POST_TAC "SR" 1024 `\i. ival((SH:num->int16) i)` THEN
  ARM_STEPS_TAC KP4_EXEC (136--138) THEN
  INDCPA_TOBYTES_PRE_TAC "TR" (b + 10240) 1024 (st 138) THEN
  LOCAL_POLYVEC_TOBYTES_TAC
   [`read X0 s`; `read X1 s`; `list_of_seq (TR:num->int16) 1024`; `pc:num`;
    `read SP s`; `read X30 s`] 139 THEN
  INDCPA_TOBYTES_POST_TAC "TR" 1024
    `\i. ival(word_add ((PT2:num->int16) i) ((EH:num->int16) i))` THEN
  KP4_RHO_HALVES_TAC b THEN
  ARM_STEPS_TAC KP4_EXEC (140--145) THEN KP4_RHO_TAC (st 145) THEN

  (*** Zeroing the buffers, the stack guard, the return ***)

  INDCPA_MEMSET_LABEL_TAC THEN
  INDCPA_MEMSETS_TAC KP4_EXEC
   [146,146; 152,155; 161,164; 170,173; 179,182] THEN
  ARM_STEPS_TAC KP4_EXEC (188--194) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC KP4_EXEC (195--210) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN KP4_FINAL_TAC;;

let MLKEM_NATIVE_INDCPA_KEYPAIR_DERAND_K4_GCC12_O3_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!pk sk coins (d:byte list) guard mf mc ea el ev pc stackpointer
    returnaddress.
        memset_contract mf ea el ev /\ memcpy_contract mc ea el ev /\
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\ LENGTH d = 32 /\
        (!i j. i < 4 /\ j < 4
               ==> mlkem_samplentt_terminates
                    (APPEND (FST(mlkem_g(APPEND d [word 4])))
                            [word j; word i])) /\
        nonoverlapping (word 0,1) (word_sub stackpointer (word 19312),19312) /\
        PAIRWISE nonoverlapping
         [(pk,1568); (sk,1536); (word_sub stackpointer (word 19312),19312)] /\
        ALLPAIRS nonoverlapping
         [(pk,1568); (sk,1536); (word_sub stackpointer (word 19312),19312)]
         [(coins,32); (word pc,libmlkem_size);
          (word(pc + got_stack_chk_guard),8); (guard,8);
          (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O3_mc /\
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
                memory :> bytes(word_sub stackpointer (word 19312),19312)])`;;

let MLKEM_NATIVE_INDCPA_KEYPAIR_DERAND_K4_GCC12_O3_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_INDCPA_KEYPAIR_DERAND_K4_GCC12_O3_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof, assuming the combined contract for *)
(* memset (for mlkem1024_gen_matrix) and the safety contract for memcpy. The *)
(* events depend only on the addresses and on rho, the seed of the matrix,   *)
(* which is part of the public key, through the samples of SampleNTT: they   *)
(* are given as a function of rho, which is the first half of the result of  *)
(* SHA3-512, given by its combined theorem, and the theorem also states that *)
(* rho is the end of the public key. As for the correctness proof, the proof *)
(* is by cases on whether the stack pointer is a multiple of 32, with the    *)
(* events in the two cases as the two branches of the template.              *)
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
          (INDCPA_GEN_MATRIX_SAFE_SPEC
            (MATCH_MP MLKEM_NATIVE_GEN_MATRIX_K4_GCC12_O3_IMAGE_SUBROUTINE_SAFE
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
        MLKEM_NATIVE_POLY_GETNOISE_ETA1_4X_K4_GCC12_O3_IMAGE_SUBROUTINE_SAFE
        (CONJ th1 th2) in
      ASSUME_CALLEE_SAFETY_TAILED_ALT_TAC gth "H_GETNOISE")
    else NO_TAC) THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_SHA3_512_GCC12_O3_IMAGE_SUBROUTINE_FULL "H_SHA3" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_POLYVEC_NTT_K4_GCC12_O3_IMAGE_SUBROUTINE_SAFE "H_NTT" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_POLYVEC_MULCACHE_COMPUTE_K4_GCC12_O3_IMAGE_SUBROUTINE_SAFE
    "H_MULCACHE" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_BASEMUL_K4_GCC12_O3_IMAGE_SUBROUTINE_SAFE "H_BASEMUL" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_POLYVEC_TOMONT_K4_GCC12_O3_IMAGE_SUBROUTINE_SAFE
    "H_TOMONT" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_POLYVEC_ADD_K4_GCC12_O3_IMAGE_SUBROUTINE_SAFE "H_ADD" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_POLYVEC_REDUCE_K4_GCC12_O3_IMAGE_SUBROUTINE_SAFE
    "H_REDUCE" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_POLYVEC_TOBYTES_K4_GCC12_O3_IMAGE_SUBROUTINE_SAFE
    "H_TOBYTES" THEN
  CONCRETIZE_F_EVENTS_TAC KP_SAFE_TEMPLATE THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NONOVERLAPPING_CLAUSES]) THEN
  SUBGOAL_THEN `aligned 16 (stackpointer:int64)` ASSUME_TAC THENL
   [UNDISCH_TAC `aligned 16 (word_add stackpointer (word 19312):int64)` THEN
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
     (parse_term("X"^string_of_int n))) (19--28) THEN
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
      (mlkem_native_libmlkem_gcc12_O3_mc,KP4_EXEC,
       0x0,mlkem_native_libmlkem_gcc12_O3_mc,safety_th)
      ilist n THENL
     [EXISTS_E2_TAC (ref KP_SAFE_ALLOWED); LABEL_TAC name safety_th]);;

let KP4_SAFE_CASE_TAC b =
  let e = `e:(uarch_event)list` in
  let x n = mk_comb(mk_comb(`read:(armstate,int64)component->armstate->int64`,
                            mk_const("X"^string_of_int n,[])),`s:armstate`) in
  let rest = [`pc:num`; `read SP s`; `read X30 s`] in
  ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP GENMAT_BYTES128_HALVES o check
   (can (term_match [] `read (memory :> bytes(coins,32)) s = n`) o concl)) THEN
  STRIP_TAC THEN
  ARM_STEPS_TAC KP4_EXEC (1--10) THEN KP4_BUFFER_TAC THEN
  ARM_STEPS_TAC KP4_EXEC (11--26) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC KP4_EXEC (27--34) THEN
  KP4_INPUT_TAC b `s34:armstate` THEN INDCPA_GOT_TAC THEN
  ARM_STEPS_TAC KP4_EXEC [35] THEN
  KP4_SAFE_CALL_TAC "H_SHA3"
   ([e; x 0; x 1; `APPEND d [word 4]:byte list`; `33`; `guard:int64`] @
    rest) 36 THEN
  KP4_G_TAC THEN
  ARM_STEPS_TAC KP4_EXEC (37--40) THEN
  KP4_SAFE_CALL_TAC "H_GM"
   ([e; x 0; x 1; `rho:byte list`; `k:num`; `guard:int64`] @ rest) 41 THEN
  ARM_STEPS_TAC KP4_EXEC (42--52) THEN
  INDCPA_NONZERO_TAC 19312 (b + 9728) THEN
  KP4_SAFE_CALL_TAC "H_GETNOISE"
   ([e; x 0; x 1; x 2; x 3; x 4; `guard:int64`] @ rest) 53 THEN
  ARM_STEPS_TAC KP4_EXEC (54--66) THEN
  INDCPA_NONZERO_TAC 19312 (b + 13824) THEN
  KP4_SAFE_CALL_TAC "H_GETNOISE"
   ([e; x 0; x 1; x 2; x 3; x 4; `guard:int64`] @ rest) 67 THEN
  ARM_STEPS_TAC KP4_EXEC (68--70) THEN
  KP4_SAFE_CALL_TAC "H_NTT" ([e; x 0] @ rest) 71 THEN
  ARM_STEPS_TAC KP4_EXEC (72--73) THEN
  KP4_SAFE_CALL_TAC "H_NTT" ([e; x 0] @ rest) 74 THEN
  ARM_STEPS_TAC KP4_EXEC (75--77) THEN
  KP4_SAFE_CALL_TAC "H_MULCACHE" ([e; x 0; x 1] @ rest) 78 THEN
  MAP_EVERY (fun q ->
    ARM_STEPS_TAC KP4_EXEC ((79 + 10 * q)--(84 + 10 * q)) THEN
    KP4_SAFE_CALL_TAC "H_BASEMUL"
     [e; x 1; x 2; x 3; x 0; `pc:num`; `read SP s`; `read X30 s`] (85 + 10 * q) THEN
    ARM_STEPS_TAC KP4_EXEC ((86 + 10 * q)--(88 + 10 * q)) THEN
    KP4_PC_TAC ("s"^string_of_int(88 + 10 * q))) [0;1;2;3] THEN
  ARM_STEPS_TAC KP4_EXEC (119--120) THEN
  KP4_SAFE_CALL_TAC "H_TOMONT" ([e; x 0] @ rest) 121 THEN
  ARM_STEPS_TAC KP4_EXEC (122--124) THEN
  KP4_SAFE_CALL_TAC "H_ADD" ([e; x 0; x 1] @ rest) 125 THEN
  ARM_STEPS_TAC KP4_EXEC (126--127) THEN
  KP4_SAFE_CALL_TAC "H_REDUCE" ([e; x 0] @ rest) 128 THEN
  ARM_STEPS_TAC KP4_EXEC (129--130) THEN
  KP4_SAFE_CALL_TAC "H_REDUCE" ([e; x 0] @ rest) 131 THEN
  ARM_STEPS_TAC KP4_EXEC (132--134) THEN
  KP4_SAFE_CALL_TAC "H_TOBYTES" ([e; x 0; x 1] @ rest) 135 THEN
  ARM_STEPS_TAC KP4_EXEC (136--138) THEN
  KP4_SAFE_CALL_TAC "H_TOBYTES" ([e; x 0; x 1] @ rest) 139 THEN
  KP4_RHO_HALVES_TAC b THEN
  ARM_STEPS_TAC KP4_EXEC (140--145) THEN
  KP4_RHO_TAC "s145" THEN
  MAP_EVERY (fun (k0,k) ->
    ARM_STEPS_TAC KP4_EXEC (k0--k) THEN LIBC_PLT_TAC KP4_EXEC k THEN
    LIBC_SAFE_CALL_TAC "H_MEMSET" KP4_EXEC
     [e; x 0; x 1; x 2; `read X30 s`] (ref KP_SAFE_ALLOWED) (k + 5))
   [146,146; 152,155; 161,164; 170,173; 179,182] THEN
  ARM_STEPS_TAC KP4_EXEC (188--194) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC KP4_EXEC (195--210) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let MLKEM_NATIVE_INDCPA_KEYPAIR_DERAND_K4_GCC12_O3_IMAGE_SUBROUTINE_SAFE_STMT =
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
           (word_sub stackpointer (word 19312),19312) /\
          PAIRWISE nonoverlapping
           [(pk,1568); (sk,1536);
            (word_sub stackpointer (word 19312),19312)] /\
          ALLPAIRS nonoverlapping
           [(pk,1568); (sk,1536);
            (word_sub stackpointer (word 19312),19312)]
           [(coins,32); (word pc,libmlkem_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mlkem_native_libmlkem_gcc12_O3_mc /\
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
                              (word_sub stackpointer (word 19312))
                              returnaddress
                              (FST(mlkem_g(APPEND d [word 4]))) /\
                       memaccess_inbounds e2
                        [coins,32; pk,1568; sk,1536;
                         word_sub stackpointer (word 19312),19312;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8;
                         word(pc + got_memcpy),8; ea,el;
                         word(pc + rodata_mlk_KeccakF_RoundConstants),192;
                         word(pc + rodata_mlk_zetas),256;
                         word(pc + mlkem_poly_ntt_consts),mlkem_poly_ntt_consts_size;
                         word(pc + mlkem_poly_mulcache_compute_consts),mlkem_poly_mulcache_compute_consts_size;
                         word(pc + mlkem1024_polyvec_basemul_acc_montgomery_cached_consts),mlkem1024_polyvec_basemul_acc_montgomery_cached_consts_size;
                         word(pc + mlkem_poly_tomont_consts),32]
                        [pk,1568; sk,1536;
                         word_sub stackpointer (word 19312),19312]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(pk,1568); memory :> bytes(sk,1536);
                  memory :> bytes(word_sub stackpointer (word 19312),19312)])`;;

let MLKEM_NATIVE_INDCPA_KEYPAIR_DERAND_K4_GCC12_O3_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_INDCPA_KEYPAIR_DERAND_K4_GCC12_O3_IMAGE_SUBROUTINE_SAFE_STMT;;
