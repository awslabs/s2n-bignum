(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The key generation of K-PKE for ML-KEM-768 (FIPS 203 Algorithm 13). This  *)
(* is the code for mlkem768_indcpa_keypair_derand from mlkem-native's        *)
(* portable C implementation compiled by gcc 12 with -O2 (see                *)
(* mlkem_native/README.md). It hashes the 32-byte seed d followed by the     *)
(* byte 3 with SHA3-512 into the seeds rho and sigma, generates the matrix   *)
(* in NTT form from rho, samples the secret s and the error e from sigma and *)
(* transforms them, computes t = A s + e in the NTT domain, and writes the   *)
(* encoding of t followed by rho as the public key and the encoding of s as  *)
(* the secret key, zeroing its buffers. It is verified in the whole image    *)
(* (see mlkem_native_libmlkem_gcc12_O2.ml), where it is at address 0x50c0,   *)
(* using the theorems for mlkem_sha3_512, mlkem768_gen_matrix,               *)
(* mlkem768_poly_getnoise_eta1_4x, mlkem768_polyvec_ntt,                     *)
(* mlkem768_polyvec_mulcache_compute,                                        *)
(* mlkem768_polyvec_basemul_acc_montgomery_cached, mlkem768_polyvec_tomont,  *)
(* mlkem768_polyvec_add, mlkem768_polyvec_reduce and                         *)
(* mlkem768_polyvec_tobytes in the image, and the contract for memset.       *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native_sha3_512_gcc12_O2.ml";;
needs "arm/proofs/mlkem_native_gen_matrix_k3_gcc12_O2.ml";;
needs "arm/proofs/mlkem_native_poly_getnoise_eta1_4x_k3_gcc12_O2.ml";;
needs "arm/proofs/mlkem_native_polyvec_ntt_k3_gcc12_O2.ml";;
needs "arm/proofs/mlkem_native_polyvec_mulcache_compute_k3_gcc12_O2.ml";;
needs "arm/proofs/mlkem_native_basemul_k3_gcc12_O2.ml";;
needs "arm/proofs/mlkem_native_polyvec_tomont_k3_gcc12_O2.ml";;
needs "arm/proofs/mlkem_native_polyvec_add_k3_gcc12_O2.ml";;
needs "arm/proofs/mlkem_native_polyvec_reduce_k3_gcc12_O2.ml";;
needs "arm/proofs/mlkem_native_polyvec_tobytes_k3_gcc12_O2.ml";;
needs "arm/proofs/utils/mlkem_native_indcpa.ml";;

(*** The code in the image:

    50c0: mov     x12, #0x2810
    50c4: sub     sp, sp, x12
    50c8: mov     x3, #0x2740
    50cc: mov     x4, #0x2700
    50d0: mov     x5, #0x1200
    50d4: mov     x6, #0x1e00
    50d8: stp     x19, x20, [sp, #16]
    50dc: add     x19, sp, #0x9f
    50e0: and     x19, x19, #0xffffffffffffffe0
    50e4: stp     x21, x22, [sp, #32]
    50e8: mov     x7, #0x1800
    50ec: add     x21, x19, x4
    50f0: stp     x23, x24, [sp, #48]
    50f4: add     x23, x19, x3
    50f8: add     x20, x19, x5
    50fc: stp     x25, x26, [sp, #64]
    5100: add     x25, x19, #0x2, lsl #12
    5104: add     x26, x19, x6
    5108: stp     x27, x28, [sp, #80]
    510c: add     x24, x19, x7
    5110: mov     w27, #0x3
    5114: str     x30, [sp, #96]
    5118: mov     w22, #0xffffffff
    511c: stp     x0, x1, [sp, #112]
    5120: mov     x1, x23
    5124: add     x28, x21, #0x20
    5128: ldp     q0, q1, [x2]
    512c: adrp    x2, 1f000 <mlk_zetas+0x18c80>
    5130: ldr     x2, [x2, #4088]
    5134: ldr     x0, [x2]
    5138: str     x0, [sp, #10248]
    513c: mov     x0, #0x0
    5140: stp     q0, q1, [x23]
    5144: mov     x0, x21
    5148: mov     x2, #0x21
    514c: strb    w27, [x25, #1888]
    5150: bl      26f4 <mlkem_sha3_512>
    5154: mov     x1, x21
    5158: mov     x0, x19
    515c: mov     w2, #0x0
    5160: bl      4f50 <mlkem768_gen_matrix>
    5164: strb    w22, [sp]
    5168: mov     x4, x28
    516c: add     x2, x20, #0x400
    5170: add     x1, x20, #0x200
    5174: mov     x0, x20
    5178: mov     w7, #0x2
    517c: mov     w6, #0x1
    5180: mov     w5, #0x0
    5184: mov     x3, #0x0
    5188: bl      60a0 <mlkem768_poly_getnoise_eta1_4x>
    518c: mov     x1, x25
    5190: mov     x4, x28
    5194: mov     w5, w27
    5198: mov     x8, #0x2400
    519c: add     x2, x26, #0x400
    51a0: strb    w22, [sp]
    51a4: mov     w7, #0x5
    51a8: mov     w6, #0x4
    51ac: mov     x3, #0x0
    51b0: add     x27, x19, x8
    51b4: mov     x0, x26
    51b8: bl      60a0 <mlkem768_poly_getnoise_eta1_4x>
    51bc: mov     x0, x20
    51c0: bl      5f00 <mlkem768_polyvec_ntt>
    51c4: mov     x0, x26
    51c8: bl      5f00 <mlkem768_polyvec_ntt>
    51cc: mov     x25, x24
    51d0: mov     x28, x19
    51d4: mov     x1, x20
    51d8: mov     x0, x27
    51dc: mov     w22, #0x0
    51e0: bl      5ff0 <mlkem768_polyvec_mulcache_compute>
    51e4: mov     x1, x28
    51e8: mov     x0, x25
    51ec: mov     x3, x27
    51f0: mov     x2, x20
    51f4: add     w22, w22, #0x1
    51f8: bl      5f40 <mlkem768_polyvec_basemul_acc_montgomery_cached>
    51fc: add     x28, x28, #0x600
    5200: add     x25, x25, #0x200
    5204: cmp     w22, #0x3
    5208: b.ne    51e4 <mlkem768_indcpa_keypair_derand+0x124>
    520c: mov     x0, x24
    5210: bl      6080 <mlkem768_polyvec_tomont>
    5214: mov     x1, x26
    5218: mov     x0, x24
    521c: bl      6044 <mlkem768_polyvec_add>
    5220: mov     x0, x24
    5224: bl      6024 <mlkem768_polyvec_reduce>
    5228: mov     x0, x20
    522c: bl      6024 <mlkem768_polyvec_reduce>
    5230: ldr     x0, [sp, #120]
    5234: mov     x1, x20
    5238: bl      5e90 <mlkem768_polyvec_tobytes>
    523c: ldr     x22, [sp, #112]
    5240: mov     x1, x24
    5244: mov     x0, x22
    5248: bl      5e90 <mlkem768_polyvec_tobytes>
    524c: ldp     q0, q1, [x21]
    5250: add     x25, x22, #0x480
    5254: mov     x0, x27
    5258: mov     x2, #0x300
    525c: mov     w1, #0x0
    5260: stp     q0, q1, [x25]
    5264: bl      840 <memset@plt>
    5268: mov     x2, #0x600
    526c: mov     x0, x20
    5270: mov     w1, #0x0
    5274: bl      840 <memset@plt>
    5278: mov     x2, #0x600
    527c: mov     x0, x24
    5280: mov     w1, #0x0
    5284: bl      840 <memset@plt>
    5288: mov     x2, #0x600
    528c: mov     x0, x26
    5290: mov     w1, #0x0
    5294: bl      840 <memset@plt>
    5298: mov     x2, #0x1200
    529c: mov     x0, x19
    52a0: mov     w1, #0x0
    52a4: bl      840 <memset@plt>
    52a8: stp     xzr, xzr, [x23]
    52ac: stp     xzr, xzr, [x23, #16]
    52b0: strb    wzr, [x23, #32]
    52b4: movi    v0.4s, #0x0
    52b8: stp     q0, q0, [x21]
    52bc: stp     q0, q0, [x21, #32]
    52c0: adrp    x0, 1f000 <mlk_zetas+0x18c80>
    52c4: ldr     x0, [x0, #4088]
    52c8: ldr     x2, [sp, #10248]
    52cc: ldr     x1, [x0]
    52d0: subs    x2, x2, x1
    52d4: mov     x1, #0x0
    52d8: b.ne    5304 <mlkem768_indcpa_keypair_derand+0x244>
    52dc: ldp     x19, x20, [sp, #16]
    52e0: mov     w0, #0x0
    52e4: ldp     x21, x22, [sp, #32]
    52e8: mov     x12, #0x2810
    52ec: ldp     x23, x24, [sp, #48]
    52f0: ldp     x25, x26, [sp, #64]
    52f4: ldp     x27, x28, [sp, #80]
    52f8: ldr     x30, [sp, #96]
    52fc: add     sp, sp, x12
    5300: ret
    5304: bl      830 <__stack_chk_fail@plt>
 ***)

let MLKEM_NATIVE_INDCPA_KEYPAIR_DERAND_K3_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc
   [0x840,0x850; 0x50c0,0x5308];;

let KP3_EXEC = MLKEM_NATIVE_INDCPA_KEYPAIR_DERAND_K3_GCC12_O2_EXEC;;

(* ------------------------------------------------------------------------- *)
(* The key generation in FIPS 203 in terms of the coefficients computed by   *)
(* the code: those of the NTTs of s and e, those of the multiplication       *)
(* cache, those of the matrix-vector product in Montgomery form, and those   *)
(* of the final results after Montgomery conversion, addition and reduction. *)
(* The two lemmas on single coefficients relate the computation of the code  *)
(* to MultiplyNTTs and the addition of e in the NTT domain, for even and odd *)
(* coefficients.                                                             *)
(* ------------------------------------------------------------------------- *)

let KPKE_KEYGEN_COEFF_EVEN_K3 = prove
 (`!(A:num->num->int) (Y:num->num->int) (YT:num->int) (SH:num->num->int)
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
          eh`,
  REPEAT GEN_TAC THEN
  CONV_TAC(ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN STRIP_TAC THEN
  REWRITE_TAC[mlkem_zq] THEN
  SIMP_TAC[RING_SUM_INTEGER_MOD_RING; FINITE_NUMSEG_LT; ARITH_EQ;
           REWRITE_RULE[mlkem_zq] FIPS203_MULTIPLY_NTTS_IN_ZQ] THEN
  REWRITE_TAC[INTEGER_MOD_RING_CLAUSES; ISUM_LT_3;
              FIPS203_MULTIPLY_NTTS_INT] THEN
  REWRITE_TAC[EVEN_DOUBLE; ARITH_RULE `(2 * p) DIV 2 = p`] THEN
  CONV_TAC INT_REM_DOWN_CONV THEN REWRITE_TAC[INT_REM_EQ] THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
  SPEC_TAC(`(&17:int) pow (2 * bitreverse7 p + 1)`,`z:int`) THEN GEN_TAC THEN
  MP_TAC(prove(`(&65536 * &169:int == &1) (mod &3329)`,
               REWRITE_TAC[int_congruent] THEN EXISTS_TAC `&3327:int` THEN
               INT_ARITH_TAC)) THEN
  SPEC_TAC(`&3329:int`,`q:int`) THEN SPEC_TAC(`&169:int`,`ri:int`) THEN
  SPEC_TAC(`&65536:int`,`r:int`) THEN REPEAT GEN_TAC THEN
  CONV_TAC INTEGER_RULE);;

let KPKE_KEYGEN_COEFF_ODD_K3 = prove
 (`!(A:num->num->int) (Y:num->num->int) (SH:num->num->int)
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
          eh`,
  REPEAT GEN_TAC THEN
  CONV_TAC(ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN STRIP_TAC THEN
  REWRITE_TAC[mlkem_zq] THEN
  SIMP_TAC[RING_SUM_INTEGER_MOD_RING; FINITE_NUMSEG_LT; ARITH_EQ;
           REWRITE_RULE[mlkem_zq] FIPS203_MULTIPLY_NTTS_IN_ZQ] THEN
  REWRITE_TAC[INTEGER_MOD_RING_CLAUSES; ISUM_LT_3;
              FIPS203_MULTIPLY_NTTS_INT] THEN
  REWRITE_TAC[EVEN_ADD; EVEN_MULT; ARITH_EVEN; ADD_SUB] THEN
  CONV_TAC INT_REM_DOWN_CONV THEN REWRITE_TAC[INT_REM_EQ] THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
  MP_TAC(prove(`(&65536 * &169:int == &1) (mod &3329)`,
               REWRITE_TAC[int_congruent] THEN EXISTS_TAC `&3327:int` THEN
               INT_ARITH_TAC)) THEN
  SPEC_TAC(`&3329:int`,`q:int`) THEN SPEC_TAC(`&169:int`,`ri:int`) THEN
  SPEC_TAC(`&65536:int`,`r:int`) THEN REPEAT GEN_TAC THEN
  CONV_TAC INTEGER_RULE);;

let KPKE_KEYGEN_K3_RESULT = prove
 (`!d rho sigma (sh:num->int16) (eh:num->int16) (mc:num->int16)
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
         num_of_bytelist(SND(kpke_keygen mlkem768 d))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[mlkem768] THEN
  MP_TAC(SPECL [`3`; `2`; `2`; `10`; `4`; `d:byte list`] KPKE_KEYGEN_FIPS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[FIPS203_NUM_OF_BYTELIST_APPEND; MLKEM_ENCODE_LENGTH] THEN
  REWRITE_TAC[ARITH_RULE `256 * 3 = 768`;
              ARITH_RULE `(12 * 768) DIV 8 = 1152`] THEN
  W(fun (_,w) ->
    let encs = find_terms (fun t -> match strip_comb t with
       (Const("mlkem_encode",_),[_;_;_]) -> true | _ -> false) w in
    MAP_EVERY (fun enc ->
      MP_TAC(PART_MATCH (lhand o rand) MLKEM_ENCODE_12_LIST
              (mk_comb(`num_of_bytelist`,enc)))) encs) THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[ARITH_RULE `EVEN 768`; MLKEM_NTT_CBD_BOUNDS] THEN
  SIMP_TAC[GSYM IN_MLKEM_ZQ; RING_ADD; RING_SUM; MLKEM_NTT_CBD_IN_ZQ] THEN
  REPEAT(DISCH_THEN SUBST1_TAC) THEN
  CONJ_TAC THENL
   [AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC;
    AP_TERM_TAC THEN AP_TERM_TAC] THEN
  MATCH_MP_TAC LIST_OF_SEQ_EQ THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[GSYM IWORD_IVAL] THEN AP_TERM_TAC THEN
  REWRITE_TAC[IWORD_IVAL] THEN
  MP_TAC(SPECL [`256`; `3`; `i:num`] EXISTS_DIV_MOD_LT) THEN
  ASM_REWRITE_TAC[ARITH_RULE `256 * 3 = 768`] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`r:num`; `n:num`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_SIMP_TAC[DIV_MOD_ADD_LT] THENL
   [ALL_TAC;
    TRANS_TAC EQ_TRANS
     `(mlkem_ntt (mlkem_cbd 2 (mlkem_prf 2 sigma (word r))) n) rem &3329` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[INT_REM_EQ] THEN ASM_SIMP_TAC[];
      MATCH_MP_TAC INT_REM_LT THEN REWRITE_TAC[MLKEM_NTT_CBD_BOUNDS]]] THEN
  SUBGOAL_THEN `?p. p < 128 /\ (n = 2 * p \/ n = 2 * p + 1)` MP_TAC THENL
   [MP_TAC(SPECL [`2`; `128`; `n:num`] EXISTS_DIV_MOD_LT) THEN
    ASM_REWRITE_TAC[ARITH_RULE `2 * 128 = 256`] THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`q:num`; `m:num`] THEN
    REWRITE_TAC[ARITH_RULE `m < 2 <=> m = 0 \/ m = 1`] THEN
    STRIP_TAC THEN EXISTS_TAC `q:num` THEN ASM_REWRITE_TAC[ADD_CLAUSES];
    ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC `p:num` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (DISJ_CASES_THEN SUBST_ALL_TAC)) THEN
  (SUBGOAL_THEN `2 * p < 256 /\ 2 * p + 1 < 256` STRIP_ASSUME_TAC THENL
    [ASM_ARITH_TAC; ALL_TAC]) THEN
  W(fun (_,w) ->
    let t = find_term (fun t -> match t with
      Comb(Const("ival",_),Comb(Comb(Const("word_add",_),_),_)) -> true
      | _ -> false) w in
    MP_TAC(PART_MATCH (lhand o rand) IVAL_WORD_ADD_SMALL t)) THEN
  ASM_SIMP_TAC[] THEN DISCH_THEN SUBST1_TAC THENL
   [MP_TAC(SPECL
     [`\j. mlkem_sample_ntt (APPEND rho [word j; word r])`;
      `\j n. ival((sh:num->int16)(256 * j + n))`;
      `\j. ival((mc:num->int16)(128 * j + p))`;
      `\j. mlkem_ntt (mlkem_cbd 2 (mlkem_prf 2 sigma (word j)))`;
      `ival((pt:num->int16)(256 * r + 2 * p))`;
      `ival((pt2:num->int16)(256 * r + 2 * p))`;
      `ival((eh:num->int16)(256 * r + 2 * p))`;
      `mlkem_ntt (mlkem_cbd 2 (mlkem_prf 2 sigma (word(3 + r)))) (2 * p)`;
      `p:num`] KPKE_KEYGEN_COEFF_EVEN_K3);
    MP_TAC(SPECL
     [`\j. mlkem_sample_ntt (APPEND rho [word j; word r])`;
      `\j n. ival((sh:num->int16)(256 * j + n))`;
      `\j. mlkem_ntt (mlkem_cbd 2 (mlkem_prf 2 sigma (word j)))`;
      `ival((pt:num->int16)(256 * r + 2 * p + 1))`;
      `ival((pt2:num->int16)(256 * r + 2 * p + 1))`;
      `ival((eh:num->int16)(256 * r + 2 * p + 1))`;
      `mlkem_ntt (mlkem_cbd 2 (mlkem_prf 2 sigma (word(3 + r))))
                 (2 * p + 1)`;
      `p:num`] KPKE_KEYGEN_COEFF_ODD_K3)] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[ADD_CLAUSES] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The buffers are aligned to 32 bytes within the stack frame, so their      *)
(* addresses depend on whether the stack pointer is a multiple of 32 or just *)
(* of 16. The input to SHA3-512 is the seed copied as two 128-bit words and  *)
(* the byte 3 (the parameter k), and its output is the two seeds rho and     *)
(* sigma as in mlkem_g.                                                      *)
(* ------------------------------------------------------------------------- *)

let KP3_BUFFER_ADDRESS = prove
 (`!sp:int64.
        aligned 16 sp
        ==> word_and (word_add sp (word 3791)) (word 18446744073709551584) =
            word_add sp (word(if aligned 32 sp then 3776 else 3760))`,
  REWRITE_TAC[REJ_ALIGNED_16_32] THEN GEN_TAC THEN
  COND_CASES_TAC THEN POP_ASSUM MP_TAC THEN
  W(fun (_,w) -> ACCEPT_TAC(BITBLAST_RULE w)));;

let KP3_BUFFER_TAC =
  FIRST_ASSUM(fun th ->
    if concl th = `aligned 32 (stackpointer:int64)` ||
       concl th = `~aligned 32 (stackpointer:int64)`
    then SUBST_ALL_TAC
          (REWRITE_RULE[th; ASSUME `aligned 16 (stackpointer:int64)`]
            (SPEC `stackpointer:int64` KP3_BUFFER_ADDRESS))
    else NO_TAC);;

let KP3_INPUT = prove
 (`!a:int64 (d:byte list) c s:armstate.
        LENGTH d = 32 /\ c < 256 /\
        read (memory :> bytes128 a) s =
        word(num_of_bytelist d MOD 2 EXP 128) /\
        read (memory :> bytes128(word_add a (word 16))) s =
        word(num_of_bytelist d DIV 2 EXP 128) /\
        read (memory :> bytes8(word_add a (word 32))) s = word c
        ==> LENGTH(APPEND d [word c:byte]) = 33 /\
            read (memory :> bytes(a,33)) s =
            num_of_bytelist(APPEND d [word c])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `read (memory :> bytes(a,32)) s = num_of_bytelist d`
  ASSUME_TAC THENL
   [MATCH_MP_TAC GENMAT_BYTES_32_OF_HALVES THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `d:byte list` NUM_OF_BYTELIST_BOUND) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[LENGTH_APPEND; LENGTH; NUM_OF_BYTELIST_APPEND] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[ARITH_RULE `33 = 32 + 1`; READ_COMPONENT_COMPOSE;
              READ_BYTES_COMBINE] THEN
  REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE; READ_MEMORY_BYTES_1] THEN
  ASM_REWRITE_TAC[num_of_bytelist; VAL_WORD; DIMINDEX_8] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_SIMP_TAC[MOD_LT] THEN ARITH_TAC);;

let KP3_INPUT_TAC b s =
  MP_TAC(SPECL [INDCPA_SP(b + 10048); `d:byte list`; `3`; s] KP3_INPUT) THEN
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
   (mlkem_native_libmlkem_gcc12_O2_mc,KP3_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_SHA3_512_GCC12_O2_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_GEN_MATRIX_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,KP3_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
    INDCPA_GEN_MATRIX_SPEC
      MLKEM_NATIVE_GEN_MATRIX_K3_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
      `word 0:int64`);;

let LOCAL_GETNOISE_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,KP3_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
    INDCPA_GETNOISE_NULL
     MLKEM_NATIVE_POLY_GETNOISE_ETA1_4X_K3_GCC12_O2_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_POLYVEC_NTT_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,KP3_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_POLYVEC_NTT_K3_GCC12_O2_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_POLYVEC_MULCACHE_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,KP3_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_POLYVEC_MULCACHE_COMPUTE_K3_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
   );;

let LOCAL_BASEMUL_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,KP3_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
    REWRITE_RULE[ALL]
      MLKEM_NATIVE_BASEMUL_K3_GCC12_O2_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_POLYVEC_TOMONT_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,KP3_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_POLYVEC_TOMONT_K3_GCC12_O2_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_POLYVEC_ADD_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,KP3_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_POLYVEC_ADD_K3_GCC12_O2_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_POLYVEC_REDUCE_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,KP3_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_POLYVEC_REDUCE_K3_GCC12_O2_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_POLYVEC_TOBYTES_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,KP3_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_POLYVEC_TOBYTES_K3_GCC12_O2_IMAGE_SUBROUTINE_CORRECT);;

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
  INDCPA_GHOST_TAC "PT" (b + 6144) 768 "s113" THEN
  SUBGOAL_THEN KP3_PT_GOAL ASSUME_TAC THENL
   [REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
    CONV_TAC EXPAND_CASES_CONV THEN REPEAT CONJ_TAC THENL
     (map (fun r -> INDCPA_BASEMUL3_ROW_TAC "PT" (b + 6144 + 512 * r)
                     "ambound" (map (KP3_AM_INST r) [0;1;2])
                     KP3_BASEMUL_DEFS) [0;1;2]);
    ALL_TAC];;

let KP3_RHO_HALVES_TAC b =
  FIRST_ASSUM(MP_TAC o MATCH_MP GENMAT_BYTES128_HALVES o check (fun th ->
    can (term_match [] (subst [INDCPA_SP(b + 9984),`a:int64`]
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
(* Correctness proof, assuming the contracts for memset and memcpy (the      *)
(* latter for the callees). The seed d is 32 bytes at coins, and the public  *)
(* key of 1184 bytes at pk and the secret key of 1152 bytes at sk are those  *)
(* of kpke_keygen mlkem768 d in common/fips203.ml. The theorem assumes that  *)
(* SampleNTT terminates for each entry of the matrix, which means that the   *)
(* output of SHAKE128 for it has 256 fields < q, as for mlkem768_gen_matrix. *)
(* The stack is the 10256 bytes of the function and the 3632 used by         *)
(* mlkem768_gen_matrix below them. The proof is by cases on whether the      *)
(* stack pointer is a multiple of 32, which gives the address b of the       *)
(* buffers, at offsets 0 (the matrix), 4608 (s), 6144 (t), 7680 (e), 9216    *)
(* (the multiplication cache), 9984 (rho and sigma) and 10048 (the input of  *)
(* SHA3-512).                                                                *)
(* ------------------------------------------------------------------------- *)

let KP3_INTRO_TAC =
  MAP_EVERY X_GEN_TAC
   [`pk:int64`; `sk:int64`; `coins:int64`; `d:byte list`; `guard:int64`;
    `mf:int64`; `mc:int64`; `ea:int64`; `el:num`; `ev:num`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 13888 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `aligned 16 (stackpointer:int64)` ASSUME_TAC THENL
   [UNDISCH_TAC `aligned 16 (word_add stackpointer (word 13888):int64)` THEN
    CONV_TAC(LAND_CONV NORMALIZE_ALIGNED_WORD_CONV) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SPECL [`pc:num`; `0x1fff8`] WORD_ADD;
              SPECL [`pc:num`; `0x1ffe8`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`; `0x1fff8`] WORD_ADD;
                              SPECL [`pc:num`; `0x1ffe8`] WORD_ADD]) THEN
  GHOST_INTRO_TAC `canary:int64` `read (memory :> bytes64 guard)` THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  MAP_EVERY (fun n ->
    ENSURES_PRESERVED_TAC ("x"^string_of_int n^"_init")
     (parse_term("X"^string_of_int n))) (19--28) THEN
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

  ARM_STEPS_TAC KP3_EXEC (1--9) THEN KP3_BUFFER_TAC THEN
  ARM_STEPS_TAC KP3_EXEC (10--28) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC KP3_EXEC (29--36) THEN
  KP3_INPUT_TAC b `s36:armstate` THEN INDCPA_GOT_TAC THEN
  ARM_STEPS_TAC KP3_EXEC [37] THEN
  LOCAL_SHA3_512_TAC
   [`read X0 s`; `read X1 s`; `APPEND d [word 3]:byte list`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 38 THEN
  KP3_G_TAC THEN

  (*** The matrix ***)

  ARM_STEPS_TAC KP3_EXEC (39--42) THEN
  LOCAL_GEN_MATRIX_TAC
   [`read X0 s`; `read X1 s`; `rho:byte list`; `k:num`; `guard:int64`;
    `mf:int64`; `ea:int64`; `el:num`; `ev:num`; `pc:num`; `read SP s`;
    `read X30 s`] 43 THEN
  INDCPA_GHOST_TAC "AM" b 2304 (st 43) THEN
  KP3_MATRIX_TAC b `s43:armstate` THEN

  (*** The noise ***)

  ARM_STEPS_TAC KP3_EXEC (44--53) THEN INDCPA_NONCE_TAC 255 THEN
  LOCAL_GETNOISE_TAC
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X4 s`;
    `sigma:byte list`; `read X5 s`; `read X6 s`; `read X7 s`;
    `word 255:int64`; `guard:int64`; `mf:int64`; `mc:int64`; `ea:int64`;
    `el:num`; `ev:num`; `pc:num`; `read SP s`; `read X30 s`] 54 THEN
  INDCPA_NOISE_TAC "S0" (b + 4608) 3 "sigma" "word j" (st 54) THEN
  ARM_STEPS_TAC KP3_EXEC (55--66) THEN
  LOCAL_GETNOISE_TAC
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X4 s`;
    `sigma:byte list`; `read X5 s`; `read X6 s`; `read X7 s`;
    `word 255:int64`; `guard:int64`; `mf:int64`; `mc:int64`; `ea:int64`;
    `el:num`; `ev:num`; `pc:num`; `read SP s`; `read X30 s`] 67 THEN
  INDCPA_NOISE_TAC "E0" (b + 7680) 3 "sigma" "word(3 + j)" (st 67) THEN
  INDCPA_DISCARD_LETS_TAC THEN

  (*** The NTTs and the multiplication cache ***)

  ARM_STEPS_TAC KP3_EXEC (68--69) THEN
  LOCAL_POLYVEC_NTT_TAC
   [`read X0 s`; `S0:num->int16`; `pc:num`; `read SP s`; `read X30 s`] 70 THEN
  INDCPA_NTT_TAC "SH" (b + 4608) 3 "S0" "sigma" "word j" (st 70) THEN
  ARM_STEPS_TAC KP3_EXEC (71--72) THEN
  LOCAL_POLYVEC_NTT_TAC
   [`read X0 s`; `E0:num->int16`; `pc:num`; `read SP s`; `read X30 s`] 73 THEN
  INDCPA_NTT_TAC "EH" (b + 7680) 3 "E0" "sigma" "word(3 + j)"
    (st 73) THEN
  ARM_STEPS_TAC KP3_EXEC (74--79) THEN
  LOCAL_POLYVEC_MULCACHE_TAC
   [`read X0 s`; `read X1 s`; `SH:num->int16`; `pc:num`; `read SP s`;
    `read X30 s`] 80 THEN
  INDCPA_MULCACHE_TAC "MC" (b + 9216) 3 "SH" (st 80) THEN

  (*** The matrix-vector product, one row per iteration ***)

  MAP_EVERY (fun r ->
    let a = (b + 1536 * r,"AM",768 * r)
    and y = (b + 4608,"SH") and t = (b + 9216,"MC") in
    ARM_STEPS_TAC KP3_EXEC ((81 + 11 * r)--(86 + 11 * r)) THEN
    INDCPA_BASEMUL3_PRE_TAC a y t (st(86 + 11 * r)) THEN
    LOCAL_BASEMUL_TAC (INDCPA_BASEMUL3_ARGS ("AM",768 * r) "SH" "MC")
      (87 + 11 * r) THEN
    INDCPA_BASEMUL3_DROP_PRE_TAC a y t THEN
    ARM_STEPS_TAC KP3_EXEC ((88 + 11 * r)--(91 + 11 * r))) [0;1;2] THEN
  KP3_AM_BOUND_TAC THEN KP3_PT_TAC b THEN

  (*** Montgomery form, adding the noise, the reductions ***)

  ARM_STEPS_TAC KP3_EXEC (114--115) THEN
  LOCAL_POLYVEC_TOMONT_TAC
   [`read X0 s`; `PT:num->int16`; `pc:num`; `read SP s`; `read X30 s`] 116 THEN
  INDCPA_TOMONT_TAC "PT2" (b + 6144) 768 "PT" (st 116) THEN
  ARM_STEPS_TAC KP3_EXEC (117--119) THEN
  LOCAL_POLYVEC_ADD_TAC
   [`read X0 s`; `read X1 s`; `PT2:num->int16`; `EH:num->int16`; `pc:num`;
    `read SP s`; `read X30 s`] 120 THEN
  ARM_STEPS_TAC KP3_EXEC (121--122) THEN
  LOCAL_POLYVEC_REDUCE_TAC
   [`read X0 s`; `\i. word_add ((PT2:num->int16) i) ((EH:num->int16) i)`;
    `pc:num`; `read SP s`; `read X30 s`] 123 THEN
  INDCPA_REDUCE_TAC "TR" (b + 6144) 768
    "word_add ((PT2:num->int16) i) ((EH:num->int16) i)" (st 123) THEN
  ARM_STEPS_TAC KP3_EXEC (124--125) THEN
  LOCAL_POLYVEC_REDUCE_TAC
   [`read X0 s`; `SH:num->int16`; `pc:num`; `read SP s`; `read X30 s`] 126 THEN
  INDCPA_REDUCE_TAC "SR" (b + 4608) 768 "(SH:num->int16) i" (st 126) THEN

  (*** The encodings of the keys ***)

  ARM_STEPS_TAC KP3_EXEC (127--129) THEN
  INDCPA_TOBYTES_PRE_TAC "SR" (b + 4608) 768 (st 129) THEN
  LOCAL_POLYVEC_TOBYTES_TAC
   [`read X0 s`; `read X1 s`; `list_of_seq (SR:num->int16) 768`; `pc:num`;
    `read SP s`; `read X30 s`] 130 THEN
  INDCPA_TOBYTES_POST_TAC "SR" 768 `\i. ival((SH:num->int16) i)` THEN
  ARM_STEPS_TAC KP3_EXEC (131--134) THEN
  INDCPA_TOBYTES_PRE_TAC "TR" (b + 6144) 768 (st 134) THEN
  LOCAL_POLYVEC_TOBYTES_TAC
   [`read X0 s`; `read X1 s`; `list_of_seq (TR:num->int16) 768`; `pc:num`;
    `read SP s`; `read X30 s`] 135 THEN
  INDCPA_TOBYTES_POST_TAC "TR" 768
    `\i. ival(word_add ((PT2:num->int16) i) ((EH:num->int16) i))` THEN
  KP3_RHO_HALVES_TAC b THEN
  ARM_STEPS_TAC KP3_EXEC (136--141) THEN KP3_RHO_TAC (st 141) THEN

  (*** Zeroing the buffers, the stack guard, the return ***)

  INDCPA_MEMSET_LABEL_TAC THEN
  INDCPA_MEMSETS_TAC KP3_EXEC
   [142,142; 148,151; 157,160; 166,169; 175,178] THEN
  ARM_STEPS_TAC KP3_EXEC (184--190) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC KP3_EXEC (191--206) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN KP3_FINAL_TAC;;

let MLKEM_NATIVE_INDCPA_KEYPAIR_DERAND_K3_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  prove
 (`!pk sk coins (d:byte list) guard mf mc ea el ev pc stackpointer
    returnaddress.
        memset_contract mf ea el ev /\ memcpy_contract mc ea el ev /\
        aligned 4096 (word pc:int64) /\ pc + 0x6480 <= 2 EXP 64 /\
        aligned 16 stackpointer /\ LENGTH d = 32 /\
        (!i j. i < 3 /\ j < 3
               ==> mlkem_samplentt_terminates
                    (APPEND (FST(mlkem_g(APPEND d [word 3])))
                            [word j; word i])) /\
        PAIRWISE nonoverlapping
         [(pk,1184); (sk,1152); (word_sub stackpointer (word 13888),13888)] /\
        ALLPAIRS nonoverlapping
         [(pk,1184); (sk,1152); (word_sub stackpointer (word 13888),13888)]
         [(coins,32); (word pc,0x6480); (word(pc + 0x1fff8),8); (guard,8);
          (word(pc + 0x1ffe8),8); (word(pc + 0x1ffd0),8); (ea,el)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                  read PC s = word (pc + 0x50c0) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [pk; sk; coins] s /\
                  read (memory :> bytes64(word(pc + 0x1fff8))) s = guard /\
                  read (memory :> bytes64(word(pc + 0x1ffe8))) s = mf /\
                  read (memory :> bytes64(word(pc + 0x1ffd0))) s = mc /\
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
                memory :> bytes(word_sub stackpointer (word 13888),13888)])`,
  KP3_INTRO_TAC THEN ASM_CASES_TAC `aligned 32 (stackpointer:int64)` THENL
   [KP3_CASE_TAC 3776; KP3_CASE_TAC 3760]);;
