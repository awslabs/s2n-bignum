(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The encryption of K-PKE for ML-KEM-768 (FIPS 203 Algorithm 14). This is   *)
(* the code for mlkem768_indcpa_enc from mlkem-native's portable C           *)
(* implementation compiled by gcc 12 with -O2 as one translation unit (see   *)
(* mlkem_native/README.md). It decodes the vector t in the NTT domain from   *)
(* the encryption key and the message m from its 32 bytes, generates the     *)
(* transposed matrix from rho (the last 32 bytes of the key), samples y, e1  *)
(* and e2 from the randomness r, and computes u = NTT^-1(A^T NTT(y)) + e1    *)
(* and v = NTT^-1(t^T NTT(y)) + e2 + mu, where mu is m decompressed. It      *)
(* writes the compressions of u and v as the ciphertext, zeroing its         *)
(* buffers. It is verified in the whole image (see libmlkem.ml), using the   *)
(* theorems for mlk_poly_frombytes_c, mlkem_poly_frommsg,                    *)
(* mlkem768_gen_matrix, mlkem768_poly_getnoise_eta1_4x, mlk_poly_ntt_c,      *)
(* mlk_poly_mulcache_compute_c,                                              *)
(* mlk_polyvec_basemul_acc_montgomery_cached_c768,                           *)
(* mlk_poly_invntt_tomont_c, mlk_poly_reduce_c, mlk_poly_compress_d10_c and  *)
(* mlk_poly_compress_d4_c in the image, and the contracts for memset and     *)
(* memcpy.                                                                   *)
(*                                                                           *)
(* Differences from the gcc 12 -O2 proof. gcc has inlined all the polyvec    *)
(* functions and poly_add:                                                   *)
(*                                                                           *)
(*  - polyvec_frombytes, polyvec_ntt, polyvec_mulcache_compute,              *)
(*    polyvec_invntt_tomont, polyvec_reduce and polyvec_compress_du: the     *)
(*    kernel is called for each polynomial, and the postcondition of the     *)
(*    polyvec function is proved from those of the calls                     *)
(*    (mlkem_native/indcpa_inline.ml);                                       *)
(*  - polyvec_basemul: a loop over the rows calling the c768 kernel, as the  *)
(*    gcc 12 -O2 code does with mlkem768_polyvec_basemul_acc_montgomery_     *)
(*    cached;                                                                *)
(*  - polyvec_add and the two calls of poly_add: the vector code of poly_add *)
(*    is inlined, in a loop over the three polynomials of u (unrolled in the *)
(*    proof) and twice for v. The inner loops are proved as lemmas from      *)
(*    their head to their exit, with the events                              *)
(*    (mlkem_native/inline_loops.ml).                                        *)
(*                                                                           *)
(* The buffers are at the same offsets from each other as with gcc 12 -O2;   *)
(* the frame is the 13280 bytes of the function and the 4400 of              *)
(* mlkem768_gen_matrix below them, 17680 in all.                             *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/gcc12_O2_mono/poly_frombytes_proof.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2_mono/poly_frommsg_proof.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2_mono/gen_matrix_k3_proof.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2_mono/poly_getnoise_eta1_4x_k3_proof.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2_mono/poly_ntt_proof.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2_mono/poly_mulcache_compute_proof.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2_mono/basemul_k3_proof.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2_mono/poly_invntt_tomont_proof.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2_mono/poly_reduce_proof.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2_mono/poly_compress_d10_proof.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2_mono/poly_compress_d4_proof.ml";;
needs "arm/proofs/mlkem_native/indcpa_inline.ml";;
needs "arm/proofs/mlkem_native/inline_loops.ml";;

(*** The code in the image is listed at the end of layout.ml, with the
     labels of the inlined calls. ***)

let MLKEM_NATIVE_INDCPA_ENC_K3_GCC12_O2_MONO_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mono_mc
   [layout_range "plt_memset"; layout_range "mlkem768_indcpa_enc"];;

let EN3_EXEC = MLKEM_NATIVE_INDCPA_ENC_K3_GCC12_O2_MONO_EXEC;;

(* ------------------------------------------------------------------------- *)
(* The encryption in FIPS 203 in terms of the values computed by the code:   *)
(* the 12-bit fields of the encryption key as decoded (which may be >= q),   *)
(* the NTT of y and its multiplication cache, the noise e1 and e2, the       *)
(* decompressed message, the products with the transposed matrix and with t  *)
(* in Montgomery form, their inverse NTTs, and the results after adding the  *)
(* noise and the message and reducing, whose compressions are encoded in the *)
(* ciphertext.                                                               *)
(* ------------------------------------------------------------------------- *)

let KPKE_ENCRYPT_K3_RESULT = prove
 (`!ek m r (TT:num->int16) (YH:num->int16) (MC:num->int16) (E1:num->int16)
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
         num_of_bytelist(kpke_encrypt mlkem768 ek m r)`,
  let inv_tac ui k =
    W(fun (_,w) ->
      let pinv = find_term (fun t -> match t with
        Comb(Const("mlkem_ntt_inv",_),_) -> true | _ -> false) w in
      SUBGOAL_THEN
       (mk_comb(mk_comb(`(IN):((1->num)->int)->(((1->num)->int)->bool)->bool`,
                        pinv),`ring_carrier mlkem_rq`)) ASSUME_TAC THENL
       [MATCH_MP_TAC MLKEM_NTT_INV_IN_RQ THEN
        REWRITE_TAC[GSYM IN_MLKEM_ZQ; RING_SUM];
        ALL_TAC] THEN
      MP_TAC(ISPECL [rand pinv; ui; `&169:int`; k] MLKEM_NTT_INV_CONG_MUL) THEN
      ANTS_TAC THENL
       [CONV_TAC(DEPTH_CONV BETA_CONV) THEN
        ASM_SIMP_TAC[GSYM IN_MLKEM_ZQ; RING_SUM];
        DISCH_TAC])
  and digit_tac =
    AP_THM_TAC THEN AP_TERM_TAC THEN
    W(fun (_,w) ->
      let t = find_term (fun t -> match t with
        Comb(Const("num_of_int",_),
             Comb(Comb(Const("rem",_),
                  Comb(Comb(Const("mlkem_compress",_),_),_)),_)) -> true
        | _ -> false) w in
      MP_TAC(PART_MATCH (lhand o rand) MLKEM_COMPRESS_DIGIT t)) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC MLKEM_COEFF_POS THEN
      REPEAT(MATCH_MP_TAC RING_ADD THEN
             REWRITE_TAC[MLKEM_CBD_IN_RQ; MLKEM_POLY_IN_RQ]) THEN
      MATCH_MP_TAC MLKEM_NTT_INV_IN_RQ THEN
      REWRITE_TAC[GSYM IN_MLKEM_ZQ; RING_SUM];
      DISCH_THEN SUBST1_TAC] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC VAL_EQ_NUM_OF_INT_IVAL THEN CONJ_TAC THENL
     [MATCH_MP_TAC MLKEM_COEFF_POS THEN
      REPEAT(MATCH_MP_TAC RING_ADD THEN
             REWRITE_TAC[MLKEM_CBD_IN_RQ; MLKEM_POLY_IN_RQ]) THEN
      MATCH_MP_TAC MLKEM_NTT_INV_IN_RQ THEN
      REWRITE_TAC[GSYM IN_MLKEM_ZQ; RING_SUM];
      ALL_TAC]
  and parity_tac =
    X_GEN_TAC `n':num` THEN DISCH_TAC THEN
    MP_TAC(SPECL [`2`; `128`; `n':num`] EXISTS_DIV_MOD_LT) THEN
    ASM_REWRITE_TAC[ARITH_RULE `2 * 128 = 256`; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`p:num`; `b:num`] THEN
    REWRITE_TAC[ARITH_RULE `b < 2 <=> b = 0 \/ b = 1`] THEN
    STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[ADD_CLAUSES] THEN
    (SUBGOAL_THEN `2 * p < 256 /\ 2 * p + 1 < 256` STRIP_ASSUME_TAC THENL
      [UNDISCH_TAC `p < 128` THEN ARITH_TAC; ALL_TAC])
  and row_tac =
    CONV_TAC(DEPTH_CONV BETA_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[ADD_CLAUSES; INT_CONG_REFL] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[] in
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[mlkem768] THEN
  MP_TAC(SPECL [`3`; `2`; `2`; `10`; `4`; `ek:byte list`; `m:byte list`;
                `r:byte list`] KPKE_ENCRYPT_FIPS) THEN
  REWRITE_TAC[ARITH_RULE `384 * 3 = 1152`] THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[FIPS203_NUM_OF_BYTELIST_APPEND; MLKEM_ENCODE_LENGTH] THEN
  REWRITE_TAC[ARITH_RULE `256 * 3 = 768`; ARITH_RULE `2 * 3 = 6`;
              ARITH_RULE `(10 * 768) DIV 8 = 960`] THEN
  W(fun (_,w) ->
    let encs = find_terms (fun t -> match strip_comb t with
       (Const("mlkem_encode",_),[_;_;_]) -> true | _ -> false) w in
    MAP_EVERY (fun enc ->
      MP_TAC(PART_MATCH (lhand o rand) NUM_OF_BYTELIST_MLKEM_ENCODE
              (mk_comb(`num_of_bytelist`,enc)))) encs) THEN
  REPEAT(ANTS_TAC THENL
   [CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV THENC DIVIDES_CONV);
    DISCH_THEN SUBST1_TAC]) THEN
  BINOP_TAC THENL [ALL_TAC; AP_TERM_TAC] THEN MATCH_MP_TAC NSUM_EQ THEN
  REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  digit_tac THENL
   [MP_TAC(SPECL [`256`; `3`; `i:num`] EXISTS_DIV_MOD_LT) THEN
    ASM_REWRITE_TAC[ARITH_RULE `256 * 3 = 768`; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`j:num`; `n:num`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_SIMP_TAC[DIV_MOD_ADD_LT] THEN
    SUBGOAL_THEN
     `!n'. n' < 256
           ==> (ival((U0:num->int16)(256 * j + n')) ==
                &169 * ring_sum mlkem_zq {j' | j' < 3}
                        (\j'. fips203_multiply_ntts
                               (mlkem_sample_ntt
                                 (APPEND (mlkem_slice 1152 32 ek)
                                         [word j; word j']))
                               (mlkem_ntt
                                 (mlkem_cbd 2 (mlkem_prf 2 r (word j'))))
                               n')) (mod &3329)`
    ASSUME_TAC THENL
     [parity_tac THENL
       [MP_TAC(SPECL
         [`\j'. mlkem_sample_ntt
                 (APPEND (mlkem_slice 1152 32 ek) [word j; word j'])`;
          `\j'. mlkem_sample_ntt
                 (APPEND (mlkem_slice 1152 32 ek) [word j; word j'])`;
          `\j' n. ival((YH:num->int16)(256 * j' + n))`;
          `\j'. ival((MC:num->int16)(128 * j' + p))`;
          `\j'. mlkem_ntt (mlkem_cbd 2 (mlkem_prf 2 r (word j')))`;
          `ival((U0:num->int16)(256 * j + 2 * p))`; `p:num`]
         BASEMUL3_ROW_EVEN);
        MP_TAC(SPECL
         [`\j'. mlkem_sample_ntt
                 (APPEND (mlkem_slice 1152 32 ek) [word j; word j'])`;
          `\j'. mlkem_sample_ntt
                 (APPEND (mlkem_slice 1152 32 ek) [word j; word j'])`;
          `\j' n. ival((YH:num->int16)(256 * j' + n))`;
          `\j'. mlkem_ntt (mlkem_cbd 2 (mlkem_prf 2 r (word j')))`;
          `ival((U0:num->int16)(256 * j + 2 * p + 1))`; `p:num`]
         BASEMUL3_ROW_ODD)] THEN
      row_tac;
      ALL_TAC] THEN
    W(fun (_,w) ->
      let t = find_term (fun t -> match t with
        Comb(Const("ival",_),Comb(Comb(Const("word_add",_),_),_)) -> true
        | _ -> false) w in
      MP_TAC(PART_MATCH (lhand o rand) IVAL_WORD_ADD_BOUNDED t)) THEN
    ANTS_TAC THENL
     [SUBGOAL_THEN `abs(ival((U1:num->int16)(256 * j + n))) <= &26624 /\
                    abs(ival((E1:num->int16)(256 * j + n))) <= &2`
      MP_TAC THENL [ASM_SIMP_TAC[]; INT_ARITH_TAC];
      DISCH_THEN SUBST1_TAC] THEN
    inv_tac `\n'. ival((U0:num->int16)(256 * j + n'))` `n:num` THEN
    ASM_SIMP_TAC[MLKEM_RQ_COEFF_ADD; MLKEM_CBD_IN_RQ] THEN
    REWRITE_TAC[MLKEM_ZQ_ADD; INT_REM_EQ] THEN
    MATCH_MP_TAC(INTEGER_RULE
     `(a:int == c) (mod q) /\ (b == d) (mod q)
      ==> (a + b == c + d) (mod q)`) THEN
    CONJ_TAC THENL [ALL_TAC; ASM_SIMP_TAC[]] THEN
    MATCH_MP_TAC INT_CONG_MONT_CANCEL THEN
    EXISTS_TAC `inverse_ntt (\n'. ival((U0:num->int16)(256 * j + n'))) n` THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n'. n' < 256
         ==> (ival((V0:num->int16) n') ==
              &169 * ring_sum mlkem_zq {j' | j' < 3}
                      (\j'. fips203_multiply_ntts
                             (\n. mlkem_decode 12 ek (256 * j' + n))
                             (mlkem_ntt
                               (mlkem_cbd 2 (mlkem_prf 2 r (word j'))))
                             n')) (mod &3329)`
  ASSUME_TAC THENL
   [parity_tac THEN
    (SUBGOAL_THEN
      `!j' x. j' < 3 /\ x < 256
              ==> (ival((TT:num->int16)(256 * j' + x)) ==
                   mlkem_decode 12 ek (256 * j' + x)) (mod &3329)`
     ASSUME_TAC THENL
      [REPEAT STRIP_TAC THEN MATCH_MP_TAC TT_DECODE_CONG THEN
       FIRST_X_ASSUM MATCH_MP_TAC THEN
       UNDISCH_TAC `j' < 3` THEN UNDISCH_TAC `x < 256` THEN ARITH_TAC;
       ALL_TAC])
    THENL
     [MP_TAC(SPECL
       [`\j' n. mlkem_decode 12 ek (256 * j' + n)`;
        `\j' n. ival((TT:num->int16)(256 * j' + n))`;
        `\j' n. ival((YH:num->int16)(256 * j' + n))`;
        `\j'. ival((MC:num->int16)(128 * j' + p))`;
        `\j'. mlkem_ntt (mlkem_cbd 2 (mlkem_prf 2 r (word j')))`;
        `ival((V0:num->int16)(2 * p))`; `p:num`] BASEMUL3_ROW_EVEN);
      MP_TAC(SPECL
       [`\j' n. mlkem_decode 12 ek (256 * j' + n)`;
        `\j' n. ival((TT:num->int16)(256 * j' + n))`;
        `\j' n. ival((YH:num->int16)(256 * j' + n))`;
        `\j'. mlkem_ntt (mlkem_cbd 2 (mlkem_prf 2 r (word j')))`;
        `ival((V0:num->int16)(2 * p + 1))`; `p:num`] BASEMUL3_ROW_ODD)] THEN
    row_tac;
    ALL_TAC] THEN
  SUBGOAL_THEN `(num_of_bytelist m DIV 2 EXP i) MOD 2 < 2` ASSUME_TAC THENL
   [REWRITE_TAC[MOD_LT_EQ] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  SUBGOAL_THEN
   `ival((MU:num->int16) i) =
    &((3329 * (num_of_bytelist m DIV 2 EXP i) MOD 2 + 1) DIV 2)`
  ASSUME_TAC THENL [ASM_SIMP_TAC[MU_IVAL]; ALL_TAC] THEN
  SUBGOAL_THEN `abs(ival((V1:num->int16) i)) <= &26624 /\
                abs(ival((E2:num->int16) i)) <= &2`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `ival(word_add ((V1:num->int16) i) ((E2:num->int16) i)) =
    ival(V1 i) + ival(E2 i)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC IVAL_WORD_ADD_BOUNDED THEN
    POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o fst o chop_list 2) THEN
    INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ival(word_add (word_add ((V1:num->int16) i) ((E2:num->int16) i))
                  ((MU:num->int16) i)) =
    ival(word_add (V1 i) (E2 i)) + ival(MU i)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC IVAL_WORD_ADD_BOUNDED THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ARITH_RULE
     `(3329 * (num_of_bytelist m DIV 2 EXP i) MOD 2 + 1) DIV 2 <= 1665`) THEN
    REWRITE_TAC[GSYM INT_OF_NUM_LE] THEN
    UNDISCH_TAC `abs(ival((V1:num->int16) i)) <= &26624` THEN
    UNDISCH_TAC `abs(ival((E2:num->int16) i)) <= &2` THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN
  inv_tac `\n. ival((V0:num->int16) n)` `i:num` THEN
  ASM_SIMP_TAC[MLKEM_RQ_COEFF_ADD; MLKEM_CBD_IN_RQ; MLKEM_POLY_IN_RQ;
               RING_ADD] THEN
  ASM_REWRITE_TAC[COEFF_MLKEM_POLY; MLKEM_DECODE_1] THEN
  ASM_SIMP_TAC[MLKEM_DECOMPRESS_1] THEN
  REWRITE_TAC[MLKEM_ZQ_ADD; INT_REM_EQ] THEN
  MATCH_MP_TAC INT_CONG_ADD3_REM_ALT THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC INT_CONG_MONT_CANCEL THEN
    EXISTS_TAC `inverse_ntt (\n. ival((V0:num->int16) n)) i` THEN
    ASM_SIMP_TAC[];
    ASM_SIMP_TAC[];
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC INT_REM_LT THEN
    REWRITE_TAC[INT_POS; INT_OF_NUM_LT] THEN
    MP_TAC(ARITH_RULE
     `(3329 * (num_of_bytelist m DIV 2 EXP i) MOD 2 + 1) DIV 2 <= 1665`) THEN
    ARITH_TAC]);;


(* ------------------------------------------------------------------------- *)
(* The buffers are aligned to 32 bytes within the stack frame, so their      *)
(* addresses depend on whether the stack pointer is a multiple of 32 or just *)
(* of 16. They are at the same offsets from each other as with gcc 12 -O2:   *)
(* 0 (the matrix), 4608 (u), 6144 (e1), 7680 (t), 9216 (y), 10752 (its       *)
(* multiplication cache), 11520 (e2), 12032 (the message), 12544 (v) and     *)
(* 13056 (rho).                                                              *)
(* ------------------------------------------------------------------------- *)

let EN3_ALIGNED_16_32 = prove
 (`(!x:int64. aligned 16 x <=> word_and x (word 15) = word 0) /\
   (!x:int64. aligned 32 x <=> word_and x (word 31) = word 0)`,
  CONJ_TAC THEN GEN_TAC THEN REWRITE_TAC[aligned; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC(ONCE_DEPTH_CONV DIVIDES_CONV) THEN REWRITE_TAC[] THENL
   [MP_TAC(ISPECL [`x:int64`; `4`] (CONJUNCT1 WORD_AND_MASK_WORD));
    MP_TAC(ISPECL [`x:int64`; `5`] (CONJUNCT1 WORD_AND_MASK_WORD))] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[DIVIDES_MOD; GSYM VAL_EQ_0; VAL_WORD; DIMINDEX_64] THEN
  SIMP_TAC[MOD_LT; ARITH_RULE `x MOD 16 < 16`; ARITH_RULE `x MOD 32 < 32`;
           ARITH_RULE `x < 16 ==> x < 2 EXP 64`;
           ARITH_RULE `x < 32 ==> x < 2 EXP 64`]);;

let EN3_BUFFER_ADDRESS = prove
 (`!sp:int64.
        aligned 16 sp
        ==> word_and (word_add sp (word 4591)) (word 18446744073709551584) =
            word_add sp (word(if aligned 32 sp then 4576 else 4560))`,
  REWRITE_TAC[EN3_ALIGNED_16_32] THEN GEN_TAC THEN
  COND_CASES_TAC THEN POP_ASSUM MP_TAC THEN
  W(fun (_,w) -> ACCEPT_TAC(BITBLAST_RULE w)));;

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
           (MATCH_MP INLINE_BYTES128_HALVES th)))]
    else NO_TAC);;

(*** The decoded t: the postcondition of polyvec_frombytes from the three
     calls of the kernel (with ekt the first 1152 bytes of the key as a
     number), then as for gcc 12 -O2 ***)

let EN3_TT_TAC b s =
  INDCPA_GHOST_TAC "TT" (b + 7680) 768 s THEN
  SUBGOAL_THEN
   `!i. i < 768
        ==> (TT:num->int16) i =
            word((num_of_bytelist ek DIV 2 EXP (12 * i)) MOD 2 EXP 12)`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN INDCPA_UNGHOST_TAC "TT" THEN
    FIRST_ASSUM(MP_TAC o SPEC `i:num` o check (fun th ->
      mem (mk_var(s,`:armstate`)) (frees(concl th)) &&
      INDCPA_HAS_CONST "MOD" (concl th) && is_forall(concl th) &&
      can (find_term (fun t -> t = `768`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    CONV_TAC(ONCE_DEPTH_CONV INDCPA_CANON_CONV) THEN
    DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN EXPAND_TAC "ekt" THEN
    MATCH_MP_TAC DIV_MOD_EXP_LOW THEN UNDISCH_TAC `i < 768` THEN ARITH_TAC;
    ALL_TAC];;

let EN3_MU_TAC b s =
  INDCPA_GHOST_TAC "MU" (b + 12032) 256 s THEN
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

let EN3_SEED_TAC b s =
  MP_TAC(SPECL [INDCPA_SP(b + 13056); `num_of_bytelist rho`;
                mk_var(s,`:armstate`)] INLINE_BYTES_32_OF_HALVES) THEN
  ANTS_TAC THENL
   [CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `rho:byte list` NUM_OF_BYTELIST_BOUND) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];
    DISCH_TAC];;

(*** The compressed u: the postcondition of polyvec_compress_du from those
     of the three calls of mlk_poly_compress_d10_c ***)

let NSUM_SHIFT_EXP_INLINE = prove
 (`!f m n d. nsum {i | i < n} (\i. f(m + i) * 2 EXP (d * (m + i))) =
             2 EXP (d * m) * nsum {i | i < n} (\i. f(m + i) * 2 EXP (d * i))`,
  REWRITE_TAC[LEFT_ADD_DISTRIB; EXP_ADD; GSYM NSUM_LMUL] THEN
  REPEAT GEN_TAC THEN MATCH_MP_TAC NSUM_EQ THEN REWRITE_TAC[MULT_AC]);;

let EN3_COMPRESS_DU_JOIN2 = prove
 (`!r s (g:num->num).
     read (memory :> bytes(r,320)) s =
     nsum {i | i < 256} (\i. g i * 2 EXP (10 * i)) /\
     read (memory :> bytes(word_add r (word 320),320)) s =
     nsum {i | i < 256} (\i. g(256 + i) * 2 EXP (10 * i))
     ==> read (memory :> bytes(r,640)) s =
         nsum {i | i < 512} (\i. g i * 2 EXP (10 * i))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[ARITH_RULE `640 = 320 + 320`;
              ARITH_RULE `512 = 256 + 256`] THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE; NSUM_LT_ADD] THEN
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD; ADD_ASSOC] THEN
  CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
  REWRITE_TAC[NSUM_SHIFT_EXP_INLINE] THEN
  CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[EXP_ADD] THEN
  SPEC_TAC(`2 EXP 2560`,`e:num`) THEN CONV_TAC NUM_RING);;

let EN3_COMPRESS_DU_JOIN = prove
 (`!r s (g:num->num).
     read (memory :> bytes(r,320)) s =
     nsum {i | i < 256} (\i. g i * 2 EXP (10 * i)) /\
     read (memory :> bytes(word_add r (word 320),320)) s =
     nsum {i | i < 256} (\i. g(256 + i) * 2 EXP (10 * i)) /\
     read (memory :> bytes(word_add r (word 640),320)) s =
     nsum {i | i < 256} (\i. g(512 + i) * 2 EXP (10 * i))
     ==> read (memory :> bytes(r,960)) s =
         nsum {i | i < 768} (\i. g i * 2 EXP (10 * i))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th ->
    MP_TAC(MATCH_MP EN3_COMPRESS_DU_JOIN2
            (CONJ (CONJUNCT1 th) (CONJUNCT1(CONJUNCT2 th)))) THEN
    MP_TAC(CONJUNCT2(CONJUNCT2 th))) THEN
  REWRITE_TAC[ARITH_RULE `960 = 640 + 320`; ARITH_RULE `768 = 512 + 256`] THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE; NSUM_LT_ADD] THEN
  REWRITE_TAC[NSUM_SHIFT_EXP_INLINE] THEN
  CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]);;

let EN3_COMPRESS_DU_TAC s =
  SUBGOAL_THEN (subst [mk_var(s,`:armstate`),`s:armstate`]
   `(!i. i < 768 ==> val((U3:num->int16) i) < 3329)
    ==> read(memory :> bytes(c,960)) s =
        nsum {i | i < 768}
             (\i. ((2048 * val(U3 i) + 3329) DIV 6658) MOD 1024 *
                  2 EXP (10 * i))`)
  ASSUME_TAC THENL
   [DISCH_THEN(fun hyp ->
      REPEAT(FIRST_X_ASSUM(fun th ->
        if is_imp(concl th) && INDCPA_HAS_CONST "nsum" (concl th) &&
           free_in `U3:num->int16` (concl th)
        then MP_TAC th THEN ANTS_TAC THENL
              [X_GEN_TAC `i:num` THEN DISCH_TAC THEN MATCH_MP_TAC hyp THEN
               UNDISCH_TAC `i < 256` THEN ARITH_TAC;
               DISCH_TAC]
        else NO_TAC))) THEN
    MATCH_MP_TAC EN3_COMPRESS_DU_JOIN THEN
    CONV_TAC(DEPTH_CONV BETA_CONV) THEN
    REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC];;


(* ------------------------------------------------------------------------- *)
(* The inlined loops of poly_add, as lemmas from their head to their exit,   *)
(* with the events (mlkem_native/inline_loops.ml): u += e1 is a loop over    *)
(* the three polynomials around ADD1 (an index added to two bases), then v   *)
(* += e2 and v += mu (pointers).                                             *)
(* ------------------------------------------------------------------------- *)

let EN3_ADD1 = INLINE_REG_IDX_LOOP "mlkem_native_libmlkem_gcc12_O2_mono_mc"
  EN3_EXEC "add" "mlkem768_indcpa_enc_loop3" "mlkem768_indcpa_enc_loop3_exit"
  "X28" "X1" "X0";;

let EN3_ADD2 = INLINE_PTR_LOOP "mlkem_native_libmlkem_gcc12_O2_mono_mc"
  EN3_EXEC "add" "mlkem768_indcpa_enc_loop4" "mlkem768_indcpa_enc_loop4_exit"
  "X1" "X3" "X2";;

let EN3_ADD3 = INLINE_PTR_LOOP "mlkem_native_libmlkem_gcc12_O2_mono_mc"
  EN3_EXEC "add" "mlkem768_indcpa_enc_loop5" "mlkem768_indcpa_enc_loop5_exit"
  "X0" "X1" "X2";;

(* ------------------------------------------------------------------------- *)
(* The callees. The matrix is generated with transposition, and the first    *)
(* call of mlkem768_poly_getnoise_eta1_4x has a null fourth output, as for   *)
(* gcc 12 -O2.                                                               *)
(* ------------------------------------------------------------------------- *)

let EN3_SUB_TAC th =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mono_mc,EN3_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mono_mc,th);;

let LOCAL_FROMBYTES_TAC =
  EN3_SUB_TAC MLKEM_NATIVE_POLY_FROMBYTES_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT;;

let LOCAL_POLY_FROMMSG_TAC =
  EN3_SUB_TAC
   (REWRITE_RULE[ALL]
     MLKEM_NATIVE_POLY_FROMMSG_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_GEN_MATRIX_TAC =
  EN3_SUB_TAC
   (INDCPA_GEN_MATRIX_SPEC
     MLKEM_NATIVE_GEN_MATRIX_K3_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT
     `word 1:int64`);;

let LOCAL_GETNOISE3_TAC =
  EN3_SUB_TAC
   (INDCPA_GETNOISE_NULL
     MLKEM_NATIVE_POLY_GETNOISE_ETA1_4X_K3_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_GETNOISE4_TAC =
  EN3_SUB_TAC
   MLKEM_NATIVE_POLY_GETNOISE_ETA1_4X_K3_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT;;

let LOCAL_NTT_TAC =
  EN3_SUB_TAC MLKEM_NATIVE_POLY_NTT_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT;;

let LOCAL_MULCACHE_TAC =
  EN3_SUB_TAC
   MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT;;

let LOCAL_BASEMUL_TAC =
  EN3_SUB_TAC
   (REWRITE_RULE[ALL]
     MLKEM_NATIVE_BASEMUL_K3_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_INVNTT_TAC =
  EN3_SUB_TAC
   (REWRITE_RULE[ALL]
     MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_REDUCE_TAC =
  EN3_SUB_TAC MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT;;

let LOCAL_COMPRESS_D10_TAC =
  EN3_SUB_TAC
   (REWRITE_RULE[ALL]
     MLKEM_NATIVE_POLY_COMPRESS_D10_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_COMPRESS_D4_TAC =
  EN3_SUB_TAC
   (REWRITE_RULE[ALL]
     MLKEM_NATIVE_POLY_COMPRESS_D4_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT);;

let EN3_LEMMA_TAC name ilist n =
  USE_THEN name (fun th -> EN3_SUB_TAC th ilist n);;

let EN3_SP n = Printf.sprintf "word_add stackpointer (word %d)" n;;

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
  INDCPA_GHOST_TAC "U0" (b + 4608) 768 s THEN
  SUBGOAL_THEN EN3_U0_GOAL ASSUME_TAC THENL
   [REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
    CONV_TAC EXPAND_CASES_CONV THEN REPEAT CONJ_TAC THENL
     (map (fun q -> INDCPA_BASEMUL3_ROW_TAC "U0" (b + 4608 + 512 * q)
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
  INDCPA_GHOST_TAC "V0" (b + 12544) 256 s THEN
  SUBGOAL_THEN EN3_V0_GOAL ASSUME_TAC THENL
   [INDCPA_BASEMUL3_ROW_TAC "V0" (b + 12544) "ttbound" [] EN3_BASEMUL_DEFS;
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
(* latter for the callees), as for gcc 12 -O2, with the frame of this code:  *)
(* the 13280 bytes of the function and the 4400 of mlkem768_gen_matrix below *)
(* them. The proof is by cases on whether the stack pointer is a multiple of *)
(* 32, which gives the address b of the buffers.                             *)
(* ------------------------------------------------------------------------- *)

let EN3_INTRO_TAC =
  MAP_EVERY X_GEN_TAC
   [`c:int64`; `m:int64`; `pk:int64`; `coins:int64`; `ek:byte list`;
    `msg:byte list`; `r:byte list`; `guard:int64`; `mf:int64`; `mc:int64`;
    `ea:int64`; `el:num`; `ev:num`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 17680 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE] THEN
  REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NONOVERLAPPING_CLAUSES]) THEN
  SUBGOAL_THEN `aligned 16 (stackpointer:int64)` ASSUME_TAC THENL
   [UNDISCH_TAC `aligned 16 (word_add stackpointer (word 17680):int64)` THEN
    CONV_TAC(LAND_CONV NORMALIZE_ALIGNED_WORD_CONV) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_stack_chk_guard:num`] WORD_ADD;
              SPECL [`pc:num`; `got_memset:num`] WORD_ADD;
              SPECL [`pc:num`; `got_memcpy:num`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`;
                                     `got_stack_chk_guard:num`] WORD_ADD;
                              SPECL [`pc:num`; `got_memset:num`] WORD_ADD;
                              SPECL [`pc:num`; `got_memcpy:num`] WORD_ADD]) THEN
  GHOST_INTRO_TAC `canary:int64` `read (memory :> bytes64 guard)` THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  MAP_EVERY (fun n ->
    ENSURES_PRESERVED_TAC ("x"^string_of_int n^"_init")
     (parse_term("X"^string_of_int n))) (19--28) THEN
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
    ALL_TAC] THEN
  X_CHOOSE_THEN `fa1:int64->int64->num->(uarch_event)list`
    (LABEL_TAC "H_ADD1") EN3_ADD1 THEN
  X_CHOOSE_THEN `fa2:int64->int64->num->(uarch_event)list`
    (LABEL_TAC "H_ADD2") EN3_ADD2 THEN
  X_CHOOSE_THEN `fa3:int64->int64->num->(uarch_event)list`
    (LABEL_TAC "H_ADD3") EN3_ADD3;;

let EN3_CASE_TAC b =
  let st n = "s"^string_of_int n in
  let sp n = EN3_SP n in
  let part v j = if j = 0 then mk_var(v,`:num->int16`) else
                 subst [mk_small_numeral(256 * j),`n:num`;
                        mk_var(v,`:num->int16`),`v:num->int16`]
                  `\i. (v:num->int16)(n + i)` in
  ENSURES_INIT_TAC "s0" THEN EN3_PK_TAC THEN
  POLYVEC_INLINE_SPLIT_TAC POLYVEC_FROMBYTES_SPLIT_GEN `pk:int64` 3 THEN
  ABBREV_TAC `ekt = num_of_bytelist ek MOD 2 EXP 9216` THEN
  POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN

  (*** The setup, the public vector t and the message ***)

  ARM_STEPS_TAC EN3_EXEC (1--3) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC EN3_EXEC (4--8) THEN EN3_BUFFER_TAC THEN
  MAP_EVERY (fun (j,k0,k1) ->
    ARM_STEPS_TAC EN3_EXEC (k0--k1) THEN
    LOCAL_FROMBYTES_TAC
     [`read X0 s`; `read X1 s`;
      subst [mk_small_numeral(3072 * j),`n:num`]
       `(ekt DIV 2 EXP n) MOD 2 EXP 3072`; `pc:num`; `read X30 s`] (k1 + 1))
   [0,9,34; 1,36,38; 2,40,43] THEN
  POLYVEC_INLINE_JOIN_TAC 3
   [POLYVEC_FROMBYTES_FIELD_GEN; ADD_CLAUSES; ARITH_RULE `4096 = 2 EXP 12`]
   (PV_FROMBYTES_POST 3 (sp(b + 7680)) "ekt" (st 44)) THEN
  EN3_TT_TAC b (st 44) THEN
  ARM_STEPS_TAC EN3_EXEC (45--53) THEN
  LOCAL_POLY_FROMMSG_TAC
   [`read X0 s`; `read X1 s`; `num_of_bytelist msg`; `pc:num`;
    `read X30 s`] 54 THEN
  EN3_MU_TAC b (st 54) THEN

  (*** The transposed matrix ***)

  EN3_SEED_TAC b (st 54) THEN
  ARM_STEPS_TAC EN3_EXEC (55--58) THEN INLINE_GOT_TAC THEN
  LOCAL_GEN_MATRIX_TAC
   [`read X0 s`; `read X1 s`; `rho:byte list`; `k:num`; `guard:int64`;
    `mf:int64`; `ea:int64`; `el:num`; `ev:num`; `pc:num`; `read SP s`;
    `read X30 s`] 59 THEN
  INDCPA_GHOST_TAC "AM" b 2304 (st 59) THEN
  EN3_MATRIX_TAC b `s59:armstate` THEN

  (*** The noise ***)

  ARM_STEPS_TAC EN3_EXEC (60--74) THEN INDCPA_NONCE_TAC 255 THEN
  INLINE_GOT_TAC THEN
  LOCAL_GETNOISE3_TAC
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X4 s`;
    `r:byte list`; `read X5 s`; `read X6 s`; `read X7 s`;
    `word 255:int64`; `guard:int64`; `mf:int64`; `mc:int64`; `ea:int64`;
    `el:num`; `ev:num`; `pc:num`; `read SP s`; `read X30 s`] 75 THEN
  INDCPA_NOISE_TAC "YS" (b + 9216) 3 "r" "word j" (st 75) THEN
  INDCPA_DISCARD_LETS_TAC THEN
  INDCPA_NONZERO_TAC 17680 (b + 11520) THEN
  ARM_STEPS_TAC EN3_EXEC (76--90) THEN INDCPA_NONCE_TAC 6 THEN
  INLINE_GOT_TAC THEN
  LOCAL_GETNOISE4_TAC
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X3 s`; `read X4 s`;
    `r:byte list`; `read X5 s`; `read X6 s`; `read X7 s`;
    `word 6:int64`; `guard:int64`; `mf:int64`; `mc:int64`; `ea:int64`;
    `el:num`; `ev:num`; `pc:num`; `read SP s`; `read X30 s`] 91 THEN
  INDCPA_NOISE_TAC "E1" (b + 6144) 3 "r" "word(3 + j)" (st 91) THEN
  INDCPA_NOISE1_TAC "E2" (b + 11520) "r" "word 6" (st 91) THEN
  INDCPA_DISCARD_LETS_TAC THEN

  (*** The NTT of y and its multiplication cache ***)

  POLYVEC_GHOST_SPLIT_TAC "YS" (b + 9216) 3 (st 91) THEN
  MAP_EVERY (fun (j,k0,k1) ->
    ARM_STEPS_TAC EN3_EXEC (k0--k1) THEN
    LOCAL_NTT_TAC [`read X0 s`; part "YS" j; `pc:num`; `read X30 s`]
      (k1 + 1)) [0,92,94; 1,96,98; 2,100,102] THEN
  POLYVEC_INLINE_JOIN_TAC 3 [] (PV_NTT_POST 3 (sp(b + 9216)) "YS" (st 103))
  THEN
  INDCPA_NTT_TAC "YH" (b + 9216) 3 "YS" "r" "word j" (st 103) THEN
  POLYVEC_GHOST_DROP_ALL_TAC "YS" 768 THEN
  POLYVEC_GHOST_SPLIT_TAC "YH" (b + 9216) 3 (st 103) THEN
  MAP_EVERY (fun (j,k0,k1) ->
    ARM_STEPS_TAC EN3_EXEC (k0--k1) THEN
    LOCAL_MULCACHE_TAC [`read X0 s`; `read X1 s`; part "YH" j; `pc:num`;
                        `read X30 s`] (k1 + 1))
   [0,104,106; 1,108,112; 2,114,116] THEN
  POLYVEC_INLINE_JOIN_TAC 3 []
   (PV_MULCACHE_POST 3 (sp(b + 10752)) "YH" (st 117)) THEN
  INDCPA_MULCACHE_TAC "MC" (b + 10752) 3 "YH" (st 117) THEN
  POLYVEC_GHOST_DROP_ALL_TAC "YH" 768 THEN

  (*** The products with the transposed matrix, one row per iteration, and
       with t ***)

  MAP_EVERY (fun q ->
    let a = (b + 1536 * q,"AM",768 * q)
    and y = (b + 9216,"YH") and t = (b + 10752,"MC") in
    ARM_STEPS_TAC EN3_EXEC ((118 + 10 * q)--(122 + 10 * q)) THEN
    INDCPA_BASEMUL3_PRE_TAC a y t (st(122 + 10 * q)) THEN
    LOCAL_BASEMUL_TAC (INDCPA_BASEMUL3_ARGS ("AM",768 * q) "YH" "MC")
      (123 + 10 * q) THEN
    INDCPA_BASEMUL3_DROP_PRE_TAC a y t THEN
    ARM_STEPS_TAC EN3_EXEC ((124 + 10 * q)--(127 + 10 * q))) [0;1;2] THEN
  EN3_AM_BOUND_TAC THEN EN3_U0_TAC b (st 147) THEN
  ARM_STEPS_TAC EN3_EXEC (148--154) THEN
  INDCPA_BASEMUL3_PRE_TAC (b + 7680,"TT",0) (b + 9216,"YH")
    (b + 10752,"MC") (st 154) THEN
  LOCAL_BASEMUL_TAC (INDCPA_BASEMUL3_ARGS ("TT",0) "YH" "MC") 155 THEN
  INDCPA_BASEMUL3_DROP_PRE_TAC (b + 7680,"TT",0) (b + 9216,"YH")
    (b + 10752,"MC") THEN
  EN3_TT_BOUND_TAC THEN EN3_V0_TAC b (st 155) THEN

  (*** The inverse NTTs ***)

  POLYVEC_GHOST_SPLIT_TAC "U0" (b + 4608) 3 (st 155) THEN
  MAP_EVERY (fun (j,k0,k1) ->
    ARM_STEPS_TAC EN3_EXEC (k0--k1) THEN
    LOCAL_INVNTT_TAC [`read X0 s`; part "U0" j; `pc:num`; `read SP s`;
                      `read X30 s`] (k1 + 1))
   [0,156,157; 1,159,160; 2,162,163] THEN
  POLYVEC_INLINE_JOIN_TAC 3 [] (PV_INVNTT_POST 3 (sp(b + 4608)) "U0" (st 164))
  THEN
  INDCPA_INVNTT_TAC "U1" (b + 4608) 3 "U0" (st 164) THEN
  POLYVEC_GHOST_DROP_ALL_TAC "U0" 768 THEN
  ARM_STEPS_TAC EN3_EXEC (165--166) THEN
  LOCAL_INVNTT_TAC [`read X0 s`; `V0:num->int16`; `pc:num`; `read SP s`;
                    `read X30 s`] 167 THEN
  INDCPA_INVNTT1_TAC "V1" (b + 12544) "V0" (st 167) THEN

  (*** Adding the noise and the message, in the inlined loops ***)

  POLYVEC_GHOST_SPLIT_TAC "U1" (b + 4608) 3 (st 167) THEN
  POLYVEC_GHOST_SPLIT_TAC "E1" (b + 6144) 3 (st 167) THEN
  ARM_STEPS_TAC EN3_EXEC (168--168) THEN
  MAP_EVERY (fun j ->
    let k0 = 169 + 7 * j in
    ARM_STEPS_TAC EN3_EXEC (k0--k0) THEN
    EN3_LEMMA_TAC "H_ADD1"
     [`read events s`; `read X28 s`; `read X1 s`; part "U1" j; part "E1" j;
      `pc:num`] (k0 + 1) THEN
    ARM_STEPS_TAC EN3_EXEC ((k0 + 2)--(k0 + 6))) [0;1;2] THEN
  POLYVEC_GHOST_DROP_ALL_TAC "U1" 768 THEN
  POLYVEC_GHOST_DROP_ALL_TAC "E1" 768 THEN
  ARM_STEPS_TAC EN3_EXEC (190--193) THEN
  EN3_LEMMA_TAC "H_ADD2"
   [`read events s`; `read X1 s`; `read X3 s`; `V1:num->int16`;
    `E2:num->int16`; `pc:num`] 194 THEN
  ARM_STEPS_TAC EN3_EXEC (195--196) THEN
  EN3_LEMMA_TAC "H_ADD3"
   [`read events s`; `read X0 s`; `read X1 s`;
    `\i. word_add ((V1:num->int16) i) ((E2:num->int16) i)`;
    `MU:num->int16`; `pc:num`] 197 THEN

  (*** The reductions ***)

  MAP_EVERY (fun (j,k0,k1) ->
    let x = if j = 0 then
      `\i. word_add ((U1:num->int16) i) ((E1:num->int16) i)` else
      subst [mk_small_numeral(256 * j),`n:num`]
       `\i. word_add ((U1:num->int16)(n + i)) ((E1:num->int16)(n + i))` in
    ARM_STEPS_TAC EN3_EXEC (k0--k1) THEN
    LOCAL_REDUCE_TAC [`read X0 s`; x; `pc:num`; `read X30 s`] (k1 + 1))
   [0,198,200; 1,202,204; 2,206,207] THEN
  POLYVEC_INLINE_JOIN_TAC 3 []
   (PV_REDUCE_POST 3 (sp(b + 4608))
     "\\i. word_add ((U1:num->int16) i) ((E1:num->int16) i)" (st 208)) THEN
  INDCPA_REDUCE_TAC "U3" (b + 4608) 768
    "word_add ((U1:num->int16) i) ((E1:num->int16) i)" (st 208) THEN
  ARM_STEPS_TAC EN3_EXEC (209--210) THEN
  LOCAL_REDUCE_TAC
   [`read X0 s`;
    `\i. word_add (word_add ((V1:num->int16) i) ((E2:num->int16) i))
                  ((MU:num->int16) i)`;
    `pc:num`; `read X30 s`] 211 THEN
  INDCPA_REDUCE_TAC "V4" (b + 12544) 256
    "word_add (word_add ((V1:num->int16) i) ((E2:num->int16) i)) \
     ((MU:num->int16) i)" (st 211) THEN

  (*** The compression and encoding of u and v ***)

  POLYVEC_GHOST_SPLIT_TAC "U3" (b + 4608) 3 (st 211) THEN
  INLINE_GOT_TAC THEN
  MAP_EVERY (fun (j,k0,k1) ->
    ARM_STEPS_TAC EN3_EXEC (k0--k1) THEN
    LOCAL_COMPRESS_D10_TAC
     [`read X0 s`; `read X1 s`; part "U3" j; `guard:int64`; `pc:num`;
      `read SP s`; `read X30 s`] (k1 + 1))
   [0,212,215; 1,217,219; 2,221,223] THEN
  EN3_COMPRESS_DU_TAC (st 224) THEN
  POLYVEC_GHOST_DROP_ALL_TAC "U3" 768 THEN
  EN3_COMPRESS_POST_TAC "U3"
   `ival(word_add ((U1:num->int16) i) ((E1:num->int16) i))` THEN
  ARM_STEPS_TAC EN3_EXEC (225--227) THEN
  LOCAL_COMPRESS_D4_TAC
   [`read X0 s`; `read X1 s`; `V4:num->int16`; `guard:int64`; `pc:num`;
    `read SP s`; `read X30 s`] 228 THEN
  EN3_COMPRESS_POST_TAC "V4"
   `ival(word_add (word_add ((V1:num->int16) i) ((E2:num->int16) i))
                  ((MU:num->int16) i))` THEN

  (*** Zeroing the buffers, the stack guard, the return ***)

  INDCPA_MEMSET_LABEL_TAC THEN
  INDCPA_MEMSETS_TAC EN3_EXEC
   [229,232; 238,242; 248,252; 258,261; 267,270; 276,279; 285,288;
    294,297; 303,306] THEN
  ARM_STEPS_TAC EN3_EXEC (312--315) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC EN3_EXEC (316--331) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN EN3_FINAL_TAC;;

let MLKEM_NATIVE_INDCPA_ENC_K3_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT =
  prove
 (`!c m pk coins (ek:byte list) (msg:byte list) (r:byte list)
    guard mf mc ea el ev pc stackpointer returnaddress.
        memset_contract mf ea el ev /\ memcpy_contract mc ea el ev /\
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        LENGTH ek = 1184 /\ LENGTH msg = 32 /\ LENGTH r = 32 /\
        (!i j. i < 3 /\ j < 3
               ==> mlkem_samplentt_terminates
                    (APPEND (mlkem_slice 1152 32 ek) [word j; word i])) /\
        nonoverlapping (word 0,1) (word_sub stackpointer (word 17680),17680) /\
        nonoverlapping (c,1088) (word_sub stackpointer (word 17680),17680) /\
        nonoverlapping (pk,1184) (word pc,libmlkem_size) /\
        ALLPAIRS nonoverlapping
         [(c,1088); (word_sub stackpointer (word 17680),17680)]
         [(m,32); (pk,1184); (coins,32); (word pc,libmlkem_size);
          (word(pc + got_stack_chk_guard),8); (guard,8);
          (word(pc + got_memset),8);
          (word(pc + got_memcpy),8); (ea,el)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mono_mc /\
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
                memory :> bytes(word_sub stackpointer (word 17680),17680)])`,
  EN3_INTRO_TAC THEN ASM_CASES_TAC `aligned 32 (stackpointer:int64)` THENL
   [EN3_CASE_TAC 4576; EN3_CASE_TAC 4560]);;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof, assuming the combined contract for *)
(* memset (for mlkem768_gen_matrix) and the safety contract for memcpy, as   *)
(* for gcc 12 -O2. The events depend only on the addresses and on rho, the   *)
(* last 32 bytes of the public key, through the samples of SampleNTT for the *)
(* transposed matrix, but not on the message or the randomness. The inlined  *)
(* loops use the same lemmas as the correctness proof, with the contents of  *)
(* the memory as the data.                                                   *)
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
            (MATCH_MP
              MLKEM_NATIVE_GEN_MATRIX_K3_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE
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
        MLKEM_NATIVE_POLY_GETNOISE_ETA1_4X_K3_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE
        (CONJ th1 th2) in
      ASSUME_CALLEE_SAFETY_TAILED_TAC (INDCPA_GETNOISE_NULL_SAFE gth)
       "H_GETNOISE3" THEN
      ASSUME_CALLEE_SAFETY_TAILED_ALT_TAC gth "H_GETNOISE")
    else NO_TAC) THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_POLY_FROMBYTES_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE
    "H_FROMBYTES" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    (REWRITE_RULE[ALL]
      MLKEM_NATIVE_POLY_FROMMSG_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE)
    "H_FROMMSG" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_POLY_NTT_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE "H_NTT" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE
    "H_MULCACHE" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_BASEMUL_K3_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE "H_BASEMUL" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    (REWRITE_RULE[ALL]
      MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE)
    "H_INVNTT" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC EN3_ADD1 "H_ADD1" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC EN3_ADD2 "H_ADD2" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC EN3_ADD3 "H_ADD3" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE "H_REDUCE" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_POLY_COMPRESS_D10_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE
    "H_COMPRESS_D10" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_POLY_COMPRESS_D4_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE
    "H_COMPRESS_D4" THEN
  CONCRETIZE_F_EVENTS_TAC EN_SAFE_TEMPLATE THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NONOVERLAPPING_CLAUSES]) THEN
  SUBGOAL_THEN `aligned 16 (stackpointer:int64)` ASSUME_TAC THENL
   [UNDISCH_TAC `aligned 16 (word_add stackpointer (word 17680):int64)` THEN
    CONV_TAC(LAND_CONV NORMALIZE_ALIGNED_WORD_CONV) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_stack_chk_guard:num`] WORD_ADD;
              SPECL [`pc:num`; `got_memset:num`] WORD_ADD;
              SPECL [`pc:num`; `got_memcpy:num`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`;
                                     `got_stack_chk_guard:num`] WORD_ADD;
                              SPECL [`pc:num`; `got_memset:num`] WORD_ADD;
                              SPECL [`pc:num`; `got_memcpy:num`] WORD_ADD]) THEN
  GHOST_INTRO_TAC `canary:int64` `read (memory :> bytes64 guard)` THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  MAP_EVERY (fun n ->
    ENSURES_PRESERVED_TAC ("x"^string_of_int n^"_init")
     (parse_term("X"^string_of_int n))) (19--28) THEN
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
      (mlkem_native_libmlkem_gcc12_O2_mono_mc,EN3_EXEC,
       0x0,mlkem_native_libmlkem_gcc12_O2_mono_mc,safety_th)
      ilist n THENL
     [EXISTS_E2_TAC (ref EN_SAFE_ALLOWED); LABEL_TAC name safety_th]);;

(*** The contents of a polynomial at the address in a register, or at 512
     bytes from it, as the data of the lemmas for the loops ***)

let EN3_CONTENTS r =
  let a = mk_comb(mk_comb(`read:(armstate,int64)component->armstate->int64`,
                          r),`s:armstate`) in
  vsubst [a,`a:int64`]
   `\i. read(memory :> bytes16(word_add a (word(2 * i)))) (s:armstate)`;;

let EN3_CONTENTS_OFF r =
  let a = mk_comb(mk_comb(`read:(armstate,int64)component->armstate->int64`,
                          r),`s:armstate`) in
  vsubst [a,`a:int64`]
   `\i. read(memory :> bytes16(word_add (word_add a (word 512))
                                (word(2 * i)))) (s:armstate)`;;

let EN3_SAFE_CASE_TAC b =
  let e = `e:(uarch_event)list` in
  let x n = mk_comb(mk_comb(`read:(armstate,int64)component->armstate->int64`,
                            mk_const("X"^string_of_int n,[])),`s:armstate`) in
  let rest = [`pc:num`; `read SP s`; `read X30 s`] in
  let rest0 = [`pc:num`; `read X30 s`] in
  let call = EN3_SAFE_CALL_TAC in
  ENSURES_INIT_TAC "s0" THEN EN3_PK_TAC THEN
  ARM_STEPS_TAC EN3_EXEC (1--3) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC EN3_EXEC (4--8) THEN EN3_BUFFER_TAC THEN
  MAP_EVERY (fun (k0,k1) ->
    ARM_STEPS_TAC EN3_EXEC (k0--k1) THEN
    call "H_FROMBYTES" ([e; x 0; x 1] @ rest0) (k1 + 1))
   [9,34; 36,38; 40,43] THEN
  ARM_STEPS_TAC EN3_EXEC (45--53) THEN
  call "H_FROMMSG" ([e; x 0; x 1] @ rest0) 54 THEN
  EN3_SEED_TAC b "s54" THEN
  ARM_STEPS_TAC EN3_EXEC (55--58) THEN INLINE_GOT_TAC THEN
  call "H_GM" ([e; x 0; x 1; `rho:byte list`; `k:num`; `guard:int64`] @ rest)
   59 THEN
  ARM_STEPS_TAC EN3_EXEC (60--74) THEN INLINE_GOT_TAC THEN
  call "H_GETNOISE3" ([e; x 0; x 1; x 2; x 4; `guard:int64`] @ rest) 75 THEN
  INDCPA_NONZERO_TAC 17680 (b + 11520) THEN
  ARM_STEPS_TAC EN3_EXEC (76--90) THEN INLINE_GOT_TAC THEN
  call "H_GETNOISE" ([e; x 0; x 1; x 2; x 3; x 4; `guard:int64`] @ rest)
   91 THEN
  MAP_EVERY (fun (k0,k1) ->
    ARM_STEPS_TAC EN3_EXEC (k0--k1) THEN
    call "H_NTT" ([e; x 0] @ rest0) (k1 + 1)) [92,94; 96,98; 100,102] THEN
  MAP_EVERY (fun (k0,k1) ->
    ARM_STEPS_TAC EN3_EXEC (k0--k1) THEN
    call "H_MULCACHE" ([e; x 0; x 1] @ rest0) (k1 + 1))
   [104,106; 108,112; 114,116] THEN
  MAP_EVERY (fun q ->
    ARM_STEPS_TAC EN3_EXEC ((118 + 10 * q)--(122 + 10 * q)) THEN
    call "H_BASEMUL" ([e; x 1; x 2; x 3; x 0] @ rest0) (123 + 10 * q) THEN
    ARM_STEPS_TAC EN3_EXEC ((124 + 10 * q)--(127 + 10 * q))) [0;1;2] THEN
  ARM_STEPS_TAC EN3_EXEC (148--154) THEN
  call "H_BASEMUL" ([e; x 1; x 2; x 3; x 0] @ rest0) 155 THEN
  MAP_EVERY (fun (k0,k1) ->
    ARM_STEPS_TAC EN3_EXEC (k0--k1) THEN
    call "H_INVNTT" ([e; x 0] @ rest) (k1 + 1))
   [156,157; 159,160; 162,163; 165,166] THEN
  ARM_STEPS_TAC EN3_EXEC (168--168) THEN
  MAP_EVERY (fun j ->
    let k0 = 169 + 7 * j in
    ARM_STEPS_TAC EN3_EXEC (k0--k0) THEN
    call "H_ADD1"
     [e; x 28; x 1; EN3_CONTENTS `X28`; EN3_CONTENTS `X1`; `pc:num`]
     (k0 + 1) THEN
    ARM_STEPS_TAC EN3_EXEC ((k0 + 2)--(k0 + 6))) [0;1;2] THEN
  ARM_STEPS_TAC EN3_EXEC (190--193) THEN
  call "H_ADD2" [e; x 1; x 3; EN3_CONTENTS `X1`; EN3_CONTENTS `X3`; `pc:num`]
   194 THEN
  ARM_STEPS_TAC EN3_EXEC (195--196) THEN
  call "H_ADD3" [e; x 0; x 1; EN3_CONTENTS `X0`; EN3_CONTENTS `X1`; `pc:num`]
   197 THEN
  MAP_EVERY (fun (k0,k1) ->
    ARM_STEPS_TAC EN3_EXEC (k0--k1) THEN
    call "H_REDUCE" ([e; x 0] @ rest0) (k1 + 1))
   [198,200; 202,204; 206,207; 209,210] THEN
  INLINE_GOT_TAC THEN
  MAP_EVERY (fun (k0,k1) ->
    ARM_STEPS_TAC EN3_EXEC (k0--k1) THEN
    call "H_COMPRESS_D10" ([e; x 0; x 1; `guard:int64`] @ rest) (k1 + 1))
   [212,215; 217,219; 221,223] THEN
  ARM_STEPS_TAC EN3_EXEC (225--227) THEN
  call "H_COMPRESS_D4" ([e; x 0; x 1; `guard:int64`] @ rest) 228 THEN
  MAP_EVERY (fun (k0,k) ->
    ARM_STEPS_TAC EN3_EXEC (k0--k) THEN LIBC_PLT_TAC EN3_EXEC k THEN
    LIBC_SAFE_CALL_TAC "H_MEMSET" EN3_EXEC
     [e; x 0; x 1; x 2; `read X30 s`] (ref EN_SAFE_ALLOWED) (k + 5))
   [229,232; 238,242; 248,252; 258,261; 267,270; 276,279; 285,288;
    294,297; 303,306] THEN
  ARM_STEPS_TAC EN3_EXEC (312--315) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC EN3_EXEC (316--331) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  MEMACCESS_DROP_ZERO_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC;;

let MLKEM_NATIVE_INDCPA_ENC_K3_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE =
  prove
 (`!mf mc ea el ev.
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
           (word_sub stackpointer (word 17680),17680) /\
          nonoverlapping (c,1088)
           (word_sub stackpointer (word 17680),17680) /\
          nonoverlapping (pk,1184) (word pc,libmlkem_size) /\
          ALLPAIRS nonoverlapping
           [(c,1088); (word_sub stackpointer (word 17680),17680)]
           [(m,32); (pk,1184); (coins,32); (word pc,libmlkem_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8);
            (word(pc + got_memcpy),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mlkem_native_libmlkem_gcc12_O2_mono_mc /\
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
                              (word_sub stackpointer (word 17680))
                              returnaddress (mlkem_slice 1152 32 ek) /\
                       memaccess_inbounds e2
                        [m,32; pk,1184; coins,32; c,1088;
                         word_sub stackpointer (word 17680),17680;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8;
                         word(pc + got_memcpy),8; ea,el;
                         word(pc + rodata_mlk_KeccakF_RoundConstants),192;
                         word(pc + mlkem_poly_cbd2_consts),64;
                         word(pc + rodata_mlk_zetas),256;
                         word(pc + mlk_poly_invntt_tomont_c_consts),32]
                        [c,1088; word_sub stackpointer (word 17680),17680]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(c,1088);
                  memory :> bytes(word_sub stackpointer (word 17680),17680)])`,
  EN3_SAFE_INTRO_TAC THEN ASM_CASES_TAC `aligned 32 (stackpointer:int64)` THENL
   [EN3_SAFE_CASE_TAC 4576; EN3_SAFE_CASE_TAC 4560]);;
