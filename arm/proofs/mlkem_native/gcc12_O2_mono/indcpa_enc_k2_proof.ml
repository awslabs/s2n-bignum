(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The encryption of K-PKE for ML-KEM-512 (FIPS 203 Algorithm 14). This is   *)
(* the code for mlkem512_indcpa_enc from mlkem-native's portable C           *)
(* implementation compiled by gcc 12 with -O2 as one translation unit (see   *)
(* mlkem_native/README.md). It decodes the vector t in the NTT domain from   *)
(* the encryption key and the message m from its 32 bytes, generates the     *)
(* transposed matrix from rho (the last 32 bytes of the key), samples y      *)
(* (with eta = 3), e1 and e2 (with eta = 2) from the randomness r, and       *)
(* computes u = NTT^-1(A^T NTT(y)) + e1 and v = NTT^-1(t^T NTT(y)) + e2 +    *)
(* mu, where mu is m decompressed. It writes the compressions of u and v as  *)
(* the ciphertext, zeroing its buffers. It is verified in the whole image    *)
(* (see libmlkem.ml), using the theorems for mlk_poly_frombytes_c,           *)
(* mlkem_poly_frommsg, mlkem512_gen_matrix, mlkem_shake256x4,                *)
(* mlkem_poly_cbd3, mlkem_poly_cbd2, mlkem512_poly_getnoise_eta2,            *)
(* mlk_poly_ntt_c, mlk_poly_mulcache_compute_c,                              *)
(* mlk_polyvec_basemul_acc_montgomery_cached_c512,                           *)
(* mlk_poly_invntt_tomont_c, mlk_poly_reduce_c, mlk_poly_compress_d10_c and  *)
(* mlk_poly_compress_d4_c in the image, and the contracts for memset and     *)
(* memcpy.                                                                   *)
(*                                                                           *)
(* Differences from the gcc 12 -O2 proof. gcc has inlined                    *)
(* mlkem512_poly_getnoise_eta1122_4x and all the polyvec functions:          *)
(*                                                                           *)
(*  - getnoise_eta1122_4x: the setup of its registers is interleaved with    *)
(*    the prologue and the decoding of t, and its body (after the matrix)    *)
(*    copies r and the nonces into four inputs, calls mlkem_shake256x4, then *)
(*    mlkem_poly_cbd3 twice for y and mlkem_poly_cbd2 twice for e1 (on the   *)
(*    first 128 of the 192 bytes of each output), and zeroes its buffers. It *)
(*    is simulated in place and its postcondition is then restated, so that  *)
(*    the rest of the proof is that of the gcc 12 -O2 code;                  *)
(*  - polyvec_frombytes, polyvec_ntt, polyvec_mulcache_compute,              *)
(*    polyvec_invntt_tomont, polyvec_reduce and polyvec_compress_du: the     *)
(*    kernel is called for each polynomial, and the postcondition of the     *)
(*    polyvec function is proved from those of the calls                     *)
(*    (mlkem_native/indcpa_inline.ml);                                       *)
(*  - polyvec_add and the two calls of poly_add: the vector code of poly_add *)
(*    is inlined as four loops (two for u, one for v += e2 and one for v +=  *)
(*    mu), which are proved as lemmas from their head to their exit, with    *)
(*    the events (mlkem_native/inline_loops.ml).                             *)
(*                                                                           *)
(* The buffers are at the same offsets from each other as with gcc 12 -O2;   *)
(* the frame is the 8400 bytes of the function and the 3616 of               *)
(* mlkem512_gen_matrix below them, 12016 in all.                             *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/gcc12_O2_mono/poly_frombytes_proof.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2_mono/poly_frommsg_proof.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2_mono/gen_matrix_k2_proof.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2_mono/shake256x4_proof.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2_mono/poly_cbd3_proof.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2_mono/poly_cbd2_proof.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2_mono/poly_getnoise_eta2_k2_proof.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2_mono/poly_ntt_proof.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2_mono/poly_mulcache_compute_proof.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2_mono/basemul_k2_proof.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2_mono/poly_invntt_tomont_proof.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2_mono/poly_reduce_proof.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2_mono/poly_compress_d10_proof.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2_mono/poly_compress_d4_proof.ml";;
needs "arm/proofs/mlkem_native/indcpa_inline.ml";;
needs "arm/proofs/mlkem_native/inline_loops.ml";;

(*** The code in the image is listed at the end of layout.ml, with the
     labels of the inlined calls. ***)

let MLKEM_NATIVE_INDCPA_ENC_K2_GCC12_O2_MONO_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mono_mc
   [layout_range "plt_memset"; layout_range "mlkem512_indcpa_enc"];;

let EN2_EXEC = MLKEM_NATIVE_INDCPA_ENC_K2_GCC12_O2_MONO_EXEC;;

(* ------------------------------------------------------------------------- *)
(* The encryption in FIPS 203 in terms of the values computed by the code:   *)
(* the 12-bit fields of the encryption key as decoded (which may be >= q),   *)
(* the NTT of y and its multiplication cache, the noise e1 and e2, the       *)
(* decompressed message, the products with the transposed matrix and with t  *)
(* in Montgomery form, their inverse NTTs, and the results after adding the  *)
(* noise and the message and reducing, whose compressions are encoded in the *)
(* ciphertext.                                                               *)
(* ------------------------------------------------------------------------- *)

let KPKE_ENCRYPT_K2_RESULT = prove
 (`!ek m r (TT:num->int16) (YH:num->int16) (MC:num->int16) (E1:num->int16)
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
         num_of_bytelist(kpke_encrypt mlkem512 ek m r)`,
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
    DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    FIRST_X_ASSUM(DISJ_CASES_THEN SUBST_ALL_TAC o
      MATCH_MP(ARITH_RULE `b < 2 ==> b = 0 \/ b = 1`)) THEN
    REWRITE_TAC[ADD_CLAUSES] THEN
    (SUBGOAL_THEN `2 * p < 256 /\ 2 * p + 1 < 256` STRIP_ASSUME_TAC THENL
      [UNDISCH_TAC `p < 128` THEN ARITH_TAC; ALL_TAC])
  and row_tac =
    CONV_TAC(DEPTH_CONV BETA_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[ADD_CLAUSES; INT_CONG_REFL] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[] in
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[mlkem512] THEN
  MP_TAC(SPECL [`2`; `3`; `2`; `10`; `4`; `ek:byte list`; `m:byte list`;
                `r:byte list`] KPKE_ENCRYPT_FIPS) THEN
  REWRITE_TAC[ARITH_RULE `384 * 2 = 768`] THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[FIPS203_NUM_OF_BYTELIST_APPEND; MLKEM_ENCODE_LENGTH] THEN
  REWRITE_TAC[ARITH_RULE `256 * 2 = 512`; ARITH_RULE `2 * 2 = 4`;
              ARITH_RULE `(10 * 512) DIV 8 = 640`] THEN
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
   [MP_TAC(SPECL [`256`; `2`; `i:num`] EXISTS_DIV_MOD_LT) THEN
    ASM_REWRITE_TAC[ARITH_RULE `256 * 2 = 512`; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`j:num`; `n:num`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_SIMP_TAC[DIV_MOD_ADD_LT] THEN
    SUBGOAL_THEN
     `!n'. n' < 256
           ==> (ival((U0:num->int16)(256 * j + n')) ==
                &169 * ring_sum mlkem_zq {j' | j' < 2}
                        (\j'. fips203_multiply_ntts
                               (mlkem_sample_ntt
                                 (APPEND (mlkem_slice 768 32 ek)
                                         [word j; word j']))
                               (mlkem_ntt
                                 (mlkem_cbd 3 (mlkem_prf 3 r (word j'))))
                               n')) (mod &3329)`
    ASSUME_TAC THENL
     [parity_tac THENL
       [MP_TAC(SPECL
         [`\j'. mlkem_sample_ntt
                 (APPEND (mlkem_slice 768 32 ek) [word j; word j'])`;
          `\j'. mlkem_sample_ntt
                 (APPEND (mlkem_slice 768 32 ek) [word j; word j'])`;
          `\j' n. ival((YH:num->int16)(256 * j' + n))`;
          `\j'. ival((MC:num->int16)(128 * j' + p))`;
          `\j'. mlkem_ntt (mlkem_cbd 3 (mlkem_prf 3 r (word j')))`;
          `ival((U0:num->int16)(256 * j + 2 * p))`; `p:num`]
         BASEMUL2_ROW_EVEN);
        MP_TAC(SPECL
         [`\j'. mlkem_sample_ntt
                 (APPEND (mlkem_slice 768 32 ek) [word j; word j'])`;
          `\j'. mlkem_sample_ntt
                 (APPEND (mlkem_slice 768 32 ek) [word j; word j'])`;
          `\j' n. ival((YH:num->int16)(256 * j' + n))`;
          `\j'. mlkem_ntt (mlkem_cbd 3 (mlkem_prf 3 r (word j')))`;
          `ival((U0:num->int16)(256 * j + 2 * p + 1))`; `p:num`]
         BASEMUL2_ROW_ODD)] THEN
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
              &169 * ring_sum mlkem_zq {j' | j' < 2}
                      (\j'. fips203_multiply_ntts
                             (\n. mlkem_decode 12 ek (256 * j' + n))
                             (mlkem_ntt
                               (mlkem_cbd 3 (mlkem_prf 3 r (word j'))))
                             n')) (mod &3329)`
  ASSUME_TAC THENL
   [parity_tac THEN
    (SUBGOAL_THEN
      `!j' x. j' < 2 /\ x < 256
              ==> (ival((TT:num->int16)(256 * j' + x)) ==
                   mlkem_decode 12 ek (256 * j' + x)) (mod &3329)`
     ASSUME_TAC THENL
      [REPEAT STRIP_TAC THEN MATCH_MP_TAC TT_DECODE_CONG THEN
       FIRST_X_ASSUM MATCH_MP_TAC THEN
       UNDISCH_TAC `j' < 2` THEN UNDISCH_TAC `x < 256` THEN ARITH_TAC;
       ALL_TAC])
    THENL
     [MP_TAC(SPECL
       [`\j' n. mlkem_decode 12 ek (256 * j' + n)`;
        `\j' n. ival((TT:num->int16)(256 * j' + n))`;
        `\j' n. ival((YH:num->int16)(256 * j' + n))`;
        `\j'. ival((MC:num->int16)(128 * j' + p))`;
        `\j'. mlkem_ntt (mlkem_cbd 3 (mlkem_prf 3 r (word j')))`;
        `ival((V0:num->int16)(2 * p))`; `p:num`] BASEMUL2_ROW_EVEN);
      MP_TAC(SPECL
       [`\j' n. mlkem_decode 12 ek (256 * j' + n)`;
        `\j' n. ival((TT:num->int16)(256 * j' + n))`;
        `\j' n. ival((YH:num->int16)(256 * j' + n))`;
        `\j'. mlkem_ntt (mlkem_cbd 3 (mlkem_prf 3 r (word j')))`;
        `ival((V0:num->int16)(2 * p + 1))`; `p:num`] BASEMUL2_ROW_ODD)] THEN
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
(* 0 (the matrix), 2048 (u), 3072 (e1), 4096 (t), 5120 (y), 6144 (its        *)
(* multiplication cache), 6656 (e2), 7168 (the message), 7680 (v) and 8192   *)
(* (rho). The four outputs of SHAKE256 for the noise y and e1 are in the     *)
(* buffer of u, 192 bytes each, and its four inputs in that of the cache.    *)
(* ------------------------------------------------------------------------- *)

let EN2_ALIGNED_16_32 = prove
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

let EN2_BUFFER_ADDRESS = prove
 (`!sp:int64.
        aligned 16 sp
        ==> word_and (word_add sp (word 3791)) (word 18446744073709551584) =
            word_add sp (word(if aligned 32 sp then 3776 else 3760))`,
  REWRITE_TAC[EN2_ALIGNED_16_32] THEN GEN_TAC THEN
  COND_CASES_TAC THEN POP_ASSUM MP_TAC THEN
  W(fun (_,w) -> ACCEPT_TAC(BITBLAST_RULE w)));;

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
           (MATCH_MP INLINE_BYTES128_HALVES th)))]
    else NO_TAC);;

(*** The decoded t: the postcondition of polyvec_frombytes from the two
     calls of the kernel, then as for gcc 12 -O2 ***)

let EN2_TT_TAC b s =
  INDCPA_GHOST_TAC "TT" (b + 4096) 512 s THEN
  SUBGOAL_THEN
   `!i. i < 512
        ==> (TT:num->int16) i =
            word((num_of_bytelist ek DIV 2 EXP (12 * i)) MOD 2 EXP 12)`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN INDCPA_UNGHOST_TAC "TT" THEN
    FIRST_ASSUM(MP_TAC o SPEC `i:num` o check (fun th ->
      mem (mk_var(s,`:armstate`)) (frees(concl th)) &&
      INDCPA_HAS_CONST "MOD" (concl th) && is_forall(concl th) &&
      can (find_term (fun t -> t = `512`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    CONV_TAC(ONCE_DEPTH_CONV INDCPA_CANON_CONV) THEN
    DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN EXPAND_TAC "ekt" THEN
    MATCH_MP_TAC DIV_MOD_EXP_LOW THEN UNDISCH_TAC `i < 512` THEN ARITH_TAC;
    ALL_TAC];;

let EN2_MU_TAC b s =
  INDCPA_GHOST_TAC "MU" (b + 7168) 256 s THEN
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

let EN2_SEED_TAC b s =
  MP_TAC(SPECL [INDCPA_SP(b + 8192); `num_of_bytelist rho`;
                mk_var(s,`:armstate`)] INLINE_BYTES_32_OF_HALVES) THEN
  ANTS_TAC THENL
   [CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `rho:byte list` NUM_OF_BYTELIST_BOUND) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];
    DISCH_TAC];;

(*** The inputs of SHAKE256 for the noise: r and the nonces ***)

let EN2_SEED_INPUT_TAC a sd c s =
  MP_TAC(SPECL [a; sd; mk_small_numeral c; s] INLINE_SEED_INPUT) THEN
  ANTS_TAC THENL
   [CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC WORD_REDUCE_CONV;
    STRIP_TAC];;

let EN2_HALVES_TAC a v =
  let pat = subst [a,`a:int64`]
   (parse_term(Printf.sprintf
     "read (memory :> bytes(a,32)) s = num_of_bytelist %s" v)) in
  let avoid = subtract (frees pat) [`s:armstate`] in
  FIRST_ASSUM(MP_TAC o MATCH_MP INLINE_BYTES128_HALVES o check (fun th ->
    can (term_match avoid pat) (concl th))) THEN
  STRIP_TAC;;

(*** The first 128 of the 192 bytes of SHAKE256, for mlkem_poly_cbd2 ***)

let EN2_PREFIX = prove
 (`!a (f:num->byte) s:armstate.
        read (memory :> bytes(a,192)) s = num_of_bytelist(list_of_seq f 192)
        ==> read (memory :> bytes(a,128)) s =
            num_of_bytelist(list_of_seq f 128)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`a:int64`; `192`; `128`; `read memory s`] READ_BYTES_MOD) THEN
  REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ARITH_RULE `MIN 192 128 = 128`] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[ARITH_RULE `192 = 128 + 64`;
              NUM_OF_BYTELIST_LIST_OF_SEQ_ADD] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `x + n * y:num = y * n + x`] THEN
  REWRITE_TAC[MOD_MULT_ADD] THEN MATCH_MP_TAC MOD_LT THEN
  MP_TAC(ISPEC `list_of_seq (f:num->byte) 128` NUM_OF_BYTELIST_BOUND) THEN
  REWRITE_TAC[LENGTH_LIST_OF_SEQ] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[]);;

let EN2_PREFIX_TAC off =
  let a = INDCPA_SP off in
  FIRST_ASSUM(fun th ->
    match concl th with
      Comb(Comb(Const("=",_),
                Comb(Comb(Const("read",_),
                          Comb(Comb(Const(":>",_),Const("memory",_)),
                               Comb(Const("bytes",_),aa))),_)),_)
        when aa = mk_pair(a,`192`) ->
          ASSUME_TAC(MATCH_MP EN2_PREFIX th)
    | _ -> NO_TAC);;

(*** The postconditions of mlkem512_poly_getnoise_eta1122_4x in the gcc 12
     -O2 build, for the outputs at off (cbd3 for y, cbd2 for e1), from those
     of the calls of mlkem_poly_cbd3 and mlkem_poly_cbd2 ***)

let EN2_NOISE_LET_TAC s =
  MAP_EVERY (fun (off,k,eta) ->
    let len = 64 * eta in
    let body = if eta = 3 then
      "iword(&((n DIV 2 EXP (6 * i)) MOD 2 + \
               (n DIV 2 EXP (6 * i + 1)) MOD 2 + \
               (n DIV 2 EXP (6 * i + 2)) MOD 2) - \
             &((n DIV 2 EXP (6 * i + 3)) MOD 2 + \
               (n DIV 2 EXP (6 * i + 4)) MOD 2 + \
               (n DIV 2 EXP (6 * i + 5)) MOD 2))"
     else
      "iword(&((n DIV 2 EXP (4 * i)) MOD 2 + \
               (n DIV 2 EXP (4 * i + 1)) MOD 2) - \
             &((n DIV 2 EXP (4 * i + 2)) MOD 2 + \
               (n DIV 2 EXP (4 * i + 3)) MOD 2))" in
    let tm = parse_term(Printf.sprintf
     "let n = num_of_bytelist
              (list_of_seq (shake256 (APPEND r [word %d:byte])) %d) in
      !i. i < 256
          ==> read(memory :> bytes16(word_add stackpointer
                                      (word(%d + 2 * i)))) (%s:armstate) =
              %s" k len off s body) in
    SUBGOAL_THEN tm ASSUME_TAC THENL
     [CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
      FIRST_ASSUM MATCH_ACCEPT_TAC;
      ALL_TAC]);;

(*** The compressed u: the postcondition of polyvec_compress_du from those
     of the two calls of mlk_poly_compress_d10_c ***)

let NSUM_SHIFT_EXP_INLINE = prove
 (`!f m n d. nsum {i | i < n} (\i. f(m + i) * 2 EXP (d * (m + i))) =
             2 EXP (d * m) * nsum {i | i < n} (\i. f(m + i) * 2 EXP (d * i))`,
  REWRITE_TAC[LEFT_ADD_DISTRIB; EXP_ADD; GSYM NSUM_LMUL] THEN
  REPEAT GEN_TAC THEN MATCH_MP_TAC NSUM_EQ THEN REWRITE_TAC[MULT_AC]);;

let EN2_COMPRESS_DU_JOIN = prove
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

let EN2_COMPRESS_DU_TAC s =
  SUBGOAL_THEN (subst [mk_var(s,`:armstate`),`s:armstate`]
   `(!i. i < 512 ==> val((U3:num->int16) i) < 3329)
    ==> read(memory :> bytes(c,640)) s =
        nsum {i | i < 512}
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
    MATCH_MP_TAC EN2_COMPRESS_DU_JOIN THEN
    CONV_TAC(DEPTH_CONV BETA_CONV) THEN
    CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC];;

(* ------------------------------------------------------------------------- *)
(* The inlined loops of poly_add, as lemmas from their head to their exit,   *)
(* with the events (mlkem_native/inline_loops.ml): u += e1 in two loops (one *)
(* with pointers, one with an offset), v += e2 and v += mu.                  *)
(* ------------------------------------------------------------------------- *)

let EN2_ADD1 = INLINE_PTR_LOOP "mlkem_native_libmlkem_gcc12_O2_mono_mc"
  EN2_EXEC "add" "mlkem512_indcpa_enc_loop1" "mlkem512_indcpa_enc_loop1_exit"
  "X1" "X0" "X26";;

let EN2_ADD2 = INLINE_IDX_ADD_LOOP "mlkem_native_libmlkem_gcc12_O2_mono_mc"
  EN2_EXEC "mlkem512_indcpa_enc_loop2" "mlkem512_indcpa_enc_loop2_exit"
  "X25" "X24" "X1" "X0" "X2";;

let EN2_ADD3 = INLINE_PTR_LOOP "mlkem_native_libmlkem_gcc12_O2_mono_mc"
  EN2_EXEC "add" "mlkem512_indcpa_enc_loop3" "mlkem512_indcpa_enc_loop3_exit"
  "X0" "X1" "X28";;

let EN2_ADD4 = INLINE_PTR_LOOP "mlkem_native_libmlkem_gcc12_O2_mono_mc"
  EN2_EXEC "add" "mlkem512_indcpa_enc_loop4" "mlkem512_indcpa_enc_loop4_exit"
  "X19" "X0" "X28";;

(* ------------------------------------------------------------------------- *)
(* The callees. The matrix is generated with transposition, so the theorem   *)
(* for mlkem512_gen_matrix is specialized to that case. The theorems with    *)
(* hypotheses of the form ALL P l are used with them as conjunctions.        *)
(* ------------------------------------------------------------------------- *)

let EN2_SUB_TAC th =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mono_mc,EN2_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mono_mc,th);;

let LOCAL_FROMBYTES_TAC =
  EN2_SUB_TAC MLKEM_NATIVE_POLY_FROMBYTES_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT;;

let LOCAL_POLY_FROMMSG_TAC =
  EN2_SUB_TAC
   (REWRITE_RULE[ALL]
     MLKEM_NATIVE_POLY_FROMMSG_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_GEN_MATRIX_TAC =
  EN2_SUB_TAC
   (INDCPA_GEN_MATRIX_SPEC
     MLKEM_NATIVE_GEN_MATRIX_K2_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT
     `word 1:int64`);;

let LOCAL_SHAKE256X4_TAC =
  EN2_SUB_TAC MLKEM_NATIVE_SHAKE256X4_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT;;

let LOCAL_CBD3_TAC =
  EN2_SUB_TAC MLKEM_NATIVE_POLY_CBD3_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT;;

let LOCAL_CBD2_TAC =
  EN2_SUB_TAC MLKEM_NATIVE_POLY_CBD2_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT;;

let LOCAL_GETNOISE_ETA2_TAC =
  EN2_SUB_TAC
   MLKEM_NATIVE_POLY_GETNOISE_ETA2_K2_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT;;

let LOCAL_NTT_TAC =
  EN2_SUB_TAC MLKEM_NATIVE_POLY_NTT_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT;;

let LOCAL_MULCACHE_TAC =
  EN2_SUB_TAC
   MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT;;

let LOCAL_BASEMUL_TAC =
  EN2_SUB_TAC
   (REWRITE_RULE[ALL]
     MLKEM_NATIVE_BASEMUL_K2_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_INVNTT_TAC =
  EN2_SUB_TAC
   (REWRITE_RULE[ALL]
     MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_REDUCE_TAC =
  EN2_SUB_TAC MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT;;

let LOCAL_COMPRESS_D10_TAC =
  EN2_SUB_TAC
   (REWRITE_RULE[ALL]
     MLKEM_NATIVE_POLY_COMPRESS_D10_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_COMPRESS_D4_TAC =
  EN2_SUB_TAC
   (REWRITE_RULE[ALL]
     MLKEM_NATIVE_POLY_COMPRESS_D4_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT);;

let EN2_LEMMA_TAC name ilist n =
  USE_THEN name (fun th -> EN2_SUB_TAC th ilist n);;

let EN2_SP n = Printf.sprintf "word_add stackpointer (word %d)" n;;
(* ------------------------------------------------------------------------- *)
(* The facts about the stages of the computation other than those given by   *)
(* the tactics in mlkem_native_indcpa.ml: the coefficients of the transposed *)
(* matrix as given by SampleNTT, the bounds on the inputs of the             *)
(* multiplications, the products with the rows of the transposed matrix and  *)
(* with t, and the bounds on the inputs of the compressions.                 *)
(* ------------------------------------------------------------------------- *)

let EN2_MATRIX_TAC b s =
  let addr = parse_term(Printf.sprintf
    "word_add stackpointer (word (%d + 512 * (2 * q + j))):int64" b) in
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
  INDCPA_GHOST_TAC "U0" (b + 2048) 512 s THEN
  SUBGOAL_THEN EN2_U0_GOAL ASSUME_TAC THENL
   [REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
    CONV_TAC EXPAND_CASES_CONV THEN REPEAT CONJ_TAC THENL
     (map (fun q -> INDCPA_BASEMULK_ROW_TAC 2 "U0" (b + 2048 + 512 * q)
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
  INDCPA_GHOST_TAC "V0" (b + 7680) 256 s THEN
  SUBGOAL_THEN EN2_V0_GOAL ASSUME_TAC THENL
   [INDCPA_BASEMULK_ROW_TAC 2 "V0" (b + 7680) "ttbound" [] EN2_BASEMUL_DEFS;
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
(* latter for mlkem_shake256x4 and getnoise). The statement is that of gcc   *)
(* 12 -O2 with the frame of this code: the 8400 bytes of the function and    *)
(* the 3616 of mlkem512_gen_matrix below them. The proof is by cases on      *)
(* whether the stack pointer is a multiple of 32, which gives the address b  *)
(* of the buffers.                                                           *)
(* ------------------------------------------------------------------------- *)

let EN2_INTRO_TAC =
  MAP_EVERY X_GEN_TAC
   [`c:int64`; `m:int64`; `pk:int64`; `coins:int64`; `ek:byte list`;
    `msg:byte list`; `r:byte list`; `guard:int64`; `mf:int64`; `mc:int64`;
    `ea:int64`; `el:num`; `ev:num`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 12016 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE] THEN
  REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NONOVERLAPPING_CLAUSES]) THEN
  SUBGOAL_THEN `aligned 16 (stackpointer:int64)` ASSUME_TAC THENL
   [UNDISCH_TAC `aligned 16 (word_add stackpointer (word 12016):int64)` THEN
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
    ALL_TAC] THEN
  X_CHOOSE_THEN `fa1:int64->int64->num->(uarch_event)list`
    (LABEL_TAC "H_ADD1") EN2_ADD1 THEN
  X_CHOOSE_THEN `fa2:int64->int64->num->(uarch_event)list`
    (LABEL_TAC "H_ADD2") EN2_ADD2 THEN
  X_CHOOSE_THEN `fa3:int64->int64->num->(uarch_event)list`
    (LABEL_TAC "H_ADD3") EN2_ADD3 THEN
  X_CHOOSE_THEN `fa4:int64->int64->num->(uarch_event)list`
    (LABEL_TAC "H_ADD4") EN2_ADD4;;

let EN2_NOISE_N k len = parse_term(Printf.sprintf
  "num_of_bytelist(list_of_seq (shake256 (APPEND r [word %d:byte])) %d)"
  k len);;

let EN2_CASE_TAC b =
  let st n = "s"^string_of_int n in
  let sp n = EN2_SP n in
  ENSURES_INIT_TAC "s0" THEN EN2_PK_TAC THEN
  POLYVEC_INLINE_SPLIT_TAC POLYVEC_FROMBYTES_SPLIT_GEN `pk:int64` 2 THEN
  ABBREV_TAC `ekt = num_of_bytelist ek MOD 2 EXP 6144` THEN
  POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN

  (*** The setup (with that of getnoise), the public vector t ***)

  ARM_STEPS_TAC EN2_EXEC (1--3) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC EN2_EXEC (4--8) THEN EN2_BUFFER_TAC THEN
  ARM_STEPS_TAC EN2_EXEC (9--32) THEN
  LOCAL_FROMBYTES_TAC
   [`read X0 s`; `read X1 s`;
    `(ekt DIV 2 EXP 0) MOD 2 EXP 3072`;
    `pc:num`; `read X30 s`] 33 THEN
  ARM_STEPS_TAC EN2_EXEC (34--36) THEN
  LOCAL_FROMBYTES_TAC
   [`read X0 s`; `read X1 s`;
    `(ekt DIV 2 EXP 3072) MOD 2 EXP 3072`;
    `pc:num`; `read X30 s`] 37 THEN
  POLYVEC_INLINE_JOIN_TAC 2
   [POLYVEC_FROMBYTES_FIELD_GEN; ADD_CLAUSES; ARITH_RULE `4096 = 2 EXP 12`]
   (PV_FROMBYTES_POST 2 (sp(b + 4096))
     "ekt" (st 37)) THEN
  EN2_TT_TAC b (st 37) THEN

  (*** The message and the seed of the matrix ***)

  ARM_STEPS_TAC EN2_EXEC (38--44) THEN
  LOCAL_POLY_FROMMSG_TAC
   [`read X0 s`; `read X1 s`; `num_of_bytelist msg`; `pc:num`;
    `read X30 s`] 45 THEN
  EN2_MU_TAC b (st 45) THEN
  EN2_SEED_TAC b (st 45) THEN

  (*** The transposed matrix ***)

  ARM_STEPS_TAC EN2_EXEC (46--49) THEN INLINE_GOT_TAC THEN
  LOCAL_GEN_MATRIX_TAC
   [`read X0 s`; `read X1 s`; `rho:byte list`; `k:num`; `guard:int64`;
    `mf:int64`; `ea:int64`; `el:num`; `ev:num`; `pc:num`; `read SP s`;
    `read X30 s`] 50 THEN
  INDCPA_GHOST_TAC "AM" b 1024 (st 50) THEN
  EN2_MATRIX_TAC b `s50:armstate` THEN

  (*** The inlined getnoise_eta1122_4x: the inputs (r and the nonces 0 to
       3), SHAKE256, mlkem_poly_cbd3 for y and mlkem_poly_cbd2 for e1 (on the
       first 128 of the 192 bytes), zeroing the buffers ***)

  EN2_HALVES_TAC `coins:int64` "r" THEN
  ARM_STEPS_TAC EN2_EXEC (51--73) THEN
  MAP_EVERY (fun k ->
    EN2_SEED_INPUT_TAC (INDCPA_SP(b + 6144 + 64 * k)) `r:byte list` k
      `s73:armstate`) [0;1;2;3] THEN
  INLINE_GOT_TAC THEN
  ARM_STEPS_TAC EN2_EXEC [74] THEN
  LOCAL_SHAKE256X4_TAC
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X3 s`; `192`;
    `read X5 s`; `read X6 s`; `read X7 s`; INDCPA_SP(b + 6336); `33`;
    `APPEND r [word 0:byte]`; `APPEND r [word 1:byte]`;
    `APPEND r [word 2:byte]`; `APPEND r [word 3:byte]`;
    `guard:int64`; `mf:int64`; `mc:int64`; `ea:int64`; `el:num`; `ev:num`;
    `pc:num`; `read SP s`; `read X30 s`] 75 THEN
  ARM_STEPS_TAC EN2_EXEC (76--78) THEN
  LOCAL_CBD3_TAC [`read X0 s`; `read X1 s`; EN2_NOISE_N 0 192; `pc:num`;
                  `read X30 s`] 79 THEN
  ARM_STEPS_TAC EN2_EXEC (80--82) THEN
  LOCAL_CBD3_TAC [`read X0 s`; `read X1 s`; EN2_NOISE_N 1 192; `pc:num`;
                  `read X30 s`] 83 THEN
  EN2_PREFIX_TAC (b + 2432) THEN EN2_PREFIX_TAC (b + 2624) THEN
  ARM_STEPS_TAC EN2_EXEC (84--88) THEN
  LOCAL_CBD2_TAC [`read X0 s`; `read X1 s`; EN2_NOISE_N 2 128; `pc:num`;
                  `read X30 s`] 89 THEN
  ARM_STEPS_TAC EN2_EXEC (90--92) THEN
  LOCAL_CBD2_TAC [`read X0 s`; `read X1 s`; EN2_NOISE_N 3 128; `pc:num`;
                  `read X30 s`] 93 THEN
  INDCPA_MEMSET_LABEL_TAC THEN
  ARM_STEPS_TAC EN2_EXEC (94--97) THEN LIBC_PLT_TAC EN2_EXEC 97 THEN
  LIBC_CALL_TAC "H_MEMSET" EN2_EXEC
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X30 s`] 102 THEN
  INDCPA_DROP_MEMSET_TAC THEN
  ARM_STEPS_TAC EN2_EXEC (103--111) THEN
  EN2_NOISE_LET_TAC (st 111)
   [b + 5120,0,3; b + 5632,1,3; b + 3072,2,2; b + 3584,3,2] THEN
  INDCPA_NOISE_ETA_TAC 3 "YS" (b + 5120) 2 "r" "word j" (st 111) THEN
  INDCPA_NOISE_ETA_TAC 2 "E1" (b + 3072) 2 "r" "word(2 + j)" (st 111) THEN
  INDCPA_DISCARD_LETS_TAC THEN

  (*** e2, by mlkem512_poly_getnoise_eta2 ***)

  ARM_STEPS_TAC EN2_EXEC (112--117) THEN INLINE_GOT_TAC THEN
  LOCAL_GETNOISE_ETA2_TAC
   [`read X0 s`; `read X1 s`; `r:byte list`; `read X2 s`; `guard:int64`;
    `mc:int64`; `ea:int64`; `el:num`; `ev:num`; `pc:num`; `read SP s`;
    `read X30 s`] 118 THEN
  INDCPA_NOISE1_TAC "E2" (b + 6656) "r" "word 4" (st 118) THEN
  INDCPA_DISCARD_LETS_TAC THEN

  (*** The NTT of y and its multiplication cache ***)

  POLYVEC_GHOST_SPLIT_TAC "YS" (b + 5120) 2 (st 118) THEN
  ARM_STEPS_TAC EN2_EXEC (119--120) THEN
  LOCAL_NTT_TAC [`read X0 s`; `YS:num->int16`; `pc:num`; `read X30 s`] 121 THEN
  ARM_STEPS_TAC EN2_EXEC (122--123) THEN
  LOCAL_NTT_TAC [`read X0 s`; `\i. (YS:num->int16)(256 + i)`; `pc:num`;
                 `read X30 s`] 124 THEN
  POLYVEC_INLINE_JOIN_TAC 2 [] (PV_NTT_POST 2 (sp(b + 5120)) "YS" (st 124)) THEN
  INDCPA_NTT_ETA_TAC 3 "YH" (b + 5120) 2 "YS" "r" "word j" (st 124) THEN
  POLYVEC_GHOST_DROP_ALL_TAC "YS" 512 THEN
  POLYVEC_GHOST_SPLIT_TAC "YH" (b + 5120) 2 (st 124) THEN
  ARM_STEPS_TAC EN2_EXEC (125--127) THEN
  LOCAL_MULCACHE_TAC [`read X0 s`; `read X1 s`; `YH:num->int16`; `pc:num`;
                      `read X30 s`] 128 THEN
  ARM_STEPS_TAC EN2_EXEC (129--132) THEN
  LOCAL_MULCACHE_TAC [`read X0 s`; `read X1 s`; `\i. (YH:num->int16)(256 + i)`;
                      `pc:num`; `read X30 s`] 133 THEN
  POLYVEC_INLINE_JOIN_TAC 2 []
   (PV_MULCACHE_POST 2 (sp(b + 6144)) "YH" (st 133)) THEN
  INDCPA_MULCACHE_TAC "MC" (b + 6144) 2 "YH" (st 133) THEN
  POLYVEC_GHOST_DROP_ALL_TAC "YH" 512 THEN

  (*** The products with the transposed matrix and with t ***)

  MAP_EVERY (fun (q,k0,k1) ->
    let a = (b + 1024 * q,"AM",512 * q)
    and y = (b + 5120,"YH") and t = (b + 6144,"MC") in
    ARM_STEPS_TAC EN2_EXEC (k0--k1) THEN
    INDCPA_BASEMULK_PRE_TAC 2 a y t (st k1) THEN
    LOCAL_BASEMUL_TAC (INDCPA_BASEMULK_ARGS 2 ("AM",512 * q) "YH" "MC")
      (k1 + 1) THEN
    INDCPA_BASEMULK_DROP_PRE_TAC 2 a y t) [0,134,138; 1,140,146] THEN
  EN2_AM_BOUND_TAC THEN EN2_U0_TAC b (st 147) THEN
  ARM_STEPS_TAC EN2_EXEC (148--152) THEN
  INDCPA_BASEMULK_PRE_TAC 2 (b + 4096,"TT",0) (b + 5120,"YH")
    (b + 6144,"MC") (st 152) THEN
  LOCAL_BASEMUL_TAC (INDCPA_BASEMULK_ARGS 2 ("TT",0) "YH" "MC") 153 THEN
  INDCPA_BASEMULK_DROP_PRE_TAC 2 (b + 4096,"TT",0) (b + 5120,"YH")
    (b + 6144,"MC") THEN
  EN2_TT_BOUND_TAC THEN EN2_V0_TAC b (st 153) THEN

  (*** The inverse NTTs ***)

  POLYVEC_GHOST_SPLIT_TAC "U0" (b + 2048) 2 (st 153) THEN
  ARM_STEPS_TAC EN2_EXEC (154--155) THEN
  LOCAL_INVNTT_TAC [`read X0 s`; `U0:num->int16`; `pc:num`; `read SP s`;
                    `read X30 s`] 156 THEN
  ARM_STEPS_TAC EN2_EXEC (157--158) THEN
  LOCAL_INVNTT_TAC [`read X0 s`; `\i. (U0:num->int16)(256 + i)`; `pc:num`;
                    `read SP s`; `read X30 s`] 159 THEN
  POLYVEC_INLINE_JOIN_TAC 2 [] (PV_INVNTT_POST 2 (sp(b + 2048)) "U0" (st 159))
  THEN
  INDCPA_INVNTT_TAC "U1" (b + 2048) 2 "U0" (st 159) THEN
  POLYVEC_GHOST_DROP_ALL_TAC "U0" 512 THEN
  ARM_STEPS_TAC EN2_EXEC (160--161) THEN
  LOCAL_INVNTT_TAC [`read X0 s`; `V0:num->int16`; `pc:num`; `read SP s`;
                    `read X30 s`] 162 THEN
  INDCPA_INVNTT1_TAC "V1" (b + 7680) "V0" (st 162) THEN

  (*** Adding the noise and the message, in the inlined loops ***)

  POLYVEC_GHOST_SPLIT_TAC "U1" (b + 2048) 2 (st 162) THEN
  POLYVEC_GHOST_SPLIT_TAC "E1" (b + 3072) 2 (st 162) THEN
  POLYVEC_GHOST_OFF_TAC "U1" (b + 2048) 512 1 (st 162) THEN
  POLYVEC_GHOST_OFF_TAC "E1" (b + 3072) 512 1 (st 162) THEN
  ARM_STEPS_TAC EN2_EXEC (163--165) THEN
  EN2_LEMMA_TAC "H_ADD1"
   [`read events s`; `read X1 s`; `read X0 s`; `U1:num->int16`;
    `E1:num->int16`; `pc:num`] 166 THEN
  ARM_STEPS_TAC EN2_EXEC (167--168) THEN
  EN2_LEMMA_TAC "H_ADD2"
   [`read events s`; `read X25 s`; `read X24 s`;
    `\i. (U1:num->int16)(256 + i)`; `\i. (E1:num->int16)(256 + i)`;
    `pc:num`] 169 THEN
  INLINE_SP_FOLD_TAC THEN
  POLYVEC_GHOST_DROP_ALL_TAC "U1" 512 THEN
  POLYVEC_GHOST_DROP_ALL_TAC "E1" 512 THEN
  ARM_STEPS_TAC EN2_EXEC (170--172) THEN
  EN2_LEMMA_TAC "H_ADD3"
   [`read events s`; `read X0 s`; `read X1 s`; `V1:num->int16`;
    `E2:num->int16`; `pc:num`] 173 THEN
  ARM_STEPS_TAC EN2_EXEC (174--175) THEN
  EN2_LEMMA_TAC "H_ADD4"
   [`read events s`; `read X19 s`; `read X0 s`;
    `\i. word_add ((V1:num->int16) i) ((E2:num->int16) i)`;
    `MU:num->int16`; `pc:num`] 176 THEN

  (*** The reductions ***)

  ARM_STEPS_TAC EN2_EXEC (177--178) THEN
  LOCAL_REDUCE_TAC
   [`read X0 s`; `\i. word_add ((U1:num->int16) i) ((E1:num->int16) i)`;
    `pc:num`; `read X30 s`] 179 THEN
  ARM_STEPS_TAC EN2_EXEC (180--181) THEN
  LOCAL_REDUCE_TAC
   [`read X0 s`;
    `\i. word_add ((U1:num->int16)(256 + i)) ((E1:num->int16)(256 + i))`;
    `pc:num`; `read X30 s`] 182 THEN
  POLYVEC_INLINE_JOIN_TAC 2 []
   (PV_REDUCE_POST 2 (sp(b + 2048))
     "\\i. word_add ((U1:num->int16) i) ((E1:num->int16) i)" (st 182)) THEN
  INDCPA_REDUCE_TAC "U3" (b + 2048) 512
    "word_add ((U1:num->int16) i) ((E1:num->int16) i)" (st 182) THEN
  ARM_STEPS_TAC EN2_EXEC (183--184) THEN
  LOCAL_REDUCE_TAC
   [`read X0 s`;
    `\i. word_add (word_add ((V1:num->int16) i) ((E2:num->int16) i))
                  ((MU:num->int16) i)`;
    `pc:num`; `read X30 s`] 185 THEN
  INDCPA_REDUCE_TAC "V4" (b + 7680) 256
    "word_add (word_add ((V1:num->int16) i) ((E2:num->int16) i)) \
     ((MU:num->int16) i)" (st 185) THEN

  (*** The compression and encoding of u and v ***)

  POLYVEC_GHOST_SPLIT_TAC "U3" (b + 2048) 2 (st 185) THEN
  ARM_STEPS_TAC EN2_EXEC (186--189) THEN INLINE_GOT_TAC THEN
  LOCAL_COMPRESS_D10_TAC
   [`read X0 s`; `read X1 s`; `U3:num->int16`; `guard:int64`; `pc:num`;
    `read SP s`; `read X30 s`] 190 THEN
  ARM_STEPS_TAC EN2_EXEC (191--193) THEN
  LOCAL_COMPRESS_D10_TAC
   [`read X0 s`; `read X1 s`; `\i. (U3:num->int16)(256 + i)`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 194 THEN
  EN2_COMPRESS_DU_TAC (st 194) THEN
  POLYVEC_GHOST_DROP_ALL_TAC "U3" 512 THEN
  EN2_COMPRESS_POST_TAC "U3"
   `ival(word_add ((U1:num->int16) i) ((E1:num->int16) i))` THEN
  ARM_STEPS_TAC EN2_EXEC (195--197) THEN
  LOCAL_COMPRESS_D4_TAC
   [`read X0 s`; `read X1 s`; `V4:num->int16`; `guard:int64`; `pc:num`;
    `read SP s`; `read X30 s`] 198 THEN
  EN2_COMPRESS_POST_TAC "V4"
   `ival(word_add (word_add ((V1:num->int16) i) ((E2:num->int16) i))
                  ((MU:num->int16) i))` THEN

  (*** Zeroing the buffers, the stack guard, the return ***)

  INDCPA_MEMSETS_TAC EN2_EXEC
   [199,202; 208,212; 218,222; 228,231; 237,240; 246,249; 255,258;
    264,267; 273,276] THEN
  ARM_STEPS_TAC EN2_EXEC (282--284) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC EN2_EXEC (285--300) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN EN2_FINAL_TAC;;

let MLKEM_NATIVE_INDCPA_ENC_K2_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT =
  prove
 (`!c m pk coins (ek:byte list) (msg:byte list) (r:byte list)
    guard mf mc ea el ev pc stackpointer returnaddress.
        memset_contract mf ea el ev /\ memcpy_contract mc ea el ev /\
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        LENGTH ek = 800 /\ LENGTH msg = 32 /\ LENGTH r = 32 /\
        (!i j. i < 2 /\ j < 2
               ==> mlkem_samplentt_terminates
                    (APPEND (mlkem_slice 768 32 ek) [word j; word i])) /\
        nonoverlapping (c,768) (word_sub stackpointer (word 12016),12016) /\
        nonoverlapping (pk,800) (word pc,libmlkem_size) /\
        ALLPAIRS nonoverlapping
         [(c,768); (word_sub stackpointer (word 12016),12016)]
         [(m,32); (pk,800); (coins,32); (word pc,libmlkem_size);
          (word(pc + got_stack_chk_guard),8); (guard,8);
          (word(pc + got_memset),8);
          (word(pc + got_memcpy),8); (ea,el)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mono_mc /\
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
                memory :> bytes(word_sub stackpointer (word 12016),12016)])`,
  EN2_INTRO_TAC THEN ASM_CASES_TAC `aligned 32 (stackpointer:int64)` THENL
   [EN2_CASE_TAC 3776; EN2_CASE_TAC 3760]);;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof, assuming the combined contract for *)
(* memset (for mlkem512_gen_matrix) and the safety contract for memcpy, as   *)
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

let EN2_SAFE_INTRO_TAC =
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
  FIRST_X_ASSUM(fun th ->
    if can (term_match [] `memset_full_contract mf ea el ev`) (concl th)
    then ASSUME_CALLEE_SAFETY_TAILED_TAC
          (INDCPA_GEN_MATRIX_SAFE_SPEC
            (MATCH_MP
              MLKEM_NATIVE_GEN_MATRIX_K2_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE
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
        MLKEM_NATIVE_SHAKE256X4_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE
        (CONJ th1 th2) in
      ASSUME_CALLEE_SAFETY_TAILED_ALT_TAC gth "H_SHAKE" THEN
      ASSUME_CALLEE_SAFETY_TAILED_ALT_TAC
       (MATCH_MP
         MLKEM_NATIVE_POLY_GETNOISE_ETA2_K2_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE
         th2) "H_ETA2")
    else NO_TAC) THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_POLY_FROMBYTES_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE
    "H_FROMBYTES" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    (REWRITE_RULE[ALL]
      MLKEM_NATIVE_POLY_FROMMSG_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE)
    "H_FROMMSG" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_POLY_CBD3_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE "H_CBD3" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_POLY_CBD2_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE "H_CBD2" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_POLY_NTT_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE "H_NTT" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE
    "H_MULCACHE" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_BASEMUL_K2_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE "H_BASEMUL" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    (REWRITE_RULE[ALL]
      MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE)
    "H_INVNTT" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC EN2_ADD1 "H_ADD1" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC EN2_ADD2 "H_ADD2" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC EN2_ADD3 "H_ADD3" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC EN2_ADD4 "H_ADD4" THEN
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
   [UNDISCH_TAC `aligned 16 (word_add stackpointer (word 12016):int64)` THEN
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
      (mlkem_native_libmlkem_gcc12_O2_mono_mc,EN2_EXEC,
       0x0,mlkem_native_libmlkem_gcc12_O2_mono_mc,safety_th)
      ilist n THENL
     [EXISTS_E2_TAC (ref EN_SAFE_ALLOWED); LABEL_TAC name safety_th]);;

(*** The contents of a polynomial at the address in a register, or at 512
     bytes from it, as the data of the lemmas for the loops ***)

let EN2_CONTENTS r =
  let a = mk_comb(mk_comb(`read:(armstate,int64)component->armstate->int64`,
                          r),`s:armstate`) in
  vsubst [a,`a:int64`]
   `\i. read(memory :> bytes16(word_add a (word(2 * i)))) (s:armstate)`;;

let EN2_CONTENTS_OFF r =
  let a = mk_comb(mk_comb(`read:(armstate,int64)component->armstate->int64`,
                          r),`s:armstate`) in
  vsubst [a,`a:int64`]
   `\i. read(memory :> bytes16(word_add (word_add a (word 512))
                                (word(2 * i)))) (s:armstate)`;;

let EN2_SAFE_CASE_TAC b =
  let e = `e:(uarch_event)list` in
  let x n = mk_comb(mk_comb(`read:(armstate,int64)component->armstate->int64`,
                            mk_const("X"^string_of_int n,[])),`s:armstate`) in
  let rest = [`pc:num`; `read SP s`; `read X30 s`] in
  let rest0 = [`pc:num`; `read X30 s`] in
  let call = EN2_SAFE_CALL_TAC in
  ENSURES_INIT_TAC "s0" THEN EN2_PK_TAC THEN
  ARM_STEPS_TAC EN2_EXEC (1--3) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC EN2_EXEC (4--8) THEN EN2_BUFFER_TAC THEN
  ARM_STEPS_TAC EN2_EXEC (9--32) THEN
  call "H_FROMBYTES" ([e; x 0; x 1] @ rest0) 33 THEN
  ARM_STEPS_TAC EN2_EXEC (34--36) THEN
  call "H_FROMBYTES" ([e; x 0; x 1] @ rest0) 37 THEN
  ARM_STEPS_TAC EN2_EXEC (38--44) THEN
  call "H_FROMMSG" ([e; x 0; x 1] @ rest0) 45 THEN
  EN2_SEED_TAC b "s45" THEN
  ARM_STEPS_TAC EN2_EXEC (46--49) THEN INLINE_GOT_TAC THEN
  call "H_GM" ([e; x 0; x 1; `rho:byte list`; `k:num`; `guard:int64`] @ rest)
   50 THEN
  ARM_STEPS_TAC EN2_EXEC (51--73) THEN INLINE_GOT_TAC THEN
  ARM_STEPS_TAC EN2_EXEC [74] THEN
  call "H_SHAKE"
   ([e; x 0; x 1; x 2; x 3; `192`; x 5; x 6; x 7; INDCPA_SP(b + 6336);
     `33`; `guard:int64`] @ rest) 75 THEN
  MAP_EVERY (fun (k0,k1) ->
    ARM_STEPS_TAC EN2_EXEC (k0--k1) THEN
    call "H_CBD3" ([e; x 0; x 1] @ rest0) (k1 + 1)) [76,78; 80,82] THEN
  MAP_EVERY (fun (k0,k1) ->
    ARM_STEPS_TAC EN2_EXEC (k0--k1) THEN
    call "H_CBD2" ([e; x 0; x 1] @ rest0) (k1 + 1)) [84,88; 90,92] THEN
  ARM_STEPS_TAC EN2_EXEC (94--97) THEN LIBC_PLT_TAC EN2_EXEC 97 THEN
  LIBC_SAFE_CALL_TAC "H_MEMSET" EN2_EXEC
   [e; x 0; x 1; x 2; `read X30 s`] (ref EN_SAFE_ALLOWED) 102 THEN
  ARM_STEPS_TAC EN2_EXEC (103--117) THEN INLINE_GOT_TAC THEN
  call "H_ETA2" ([e; x 0; x 1; x 2; `guard:int64`] @ rest) 118 THEN
  MAP_EVERY (fun (k0,k1) ->
    ARM_STEPS_TAC EN2_EXEC (k0--k1) THEN
    call "H_NTT" ([e; x 0] @ rest0) (k1 + 1)) [119,120; 122,123] THEN
  MAP_EVERY (fun (k0,k1) ->
    ARM_STEPS_TAC EN2_EXEC (k0--k1) THEN
    call "H_MULCACHE" ([e; x 0; x 1] @ rest0) (k1 + 1)) [125,127; 129,132]
  THEN
  MAP_EVERY (fun (k0,k1) ->
    ARM_STEPS_TAC EN2_EXEC (k0--k1) THEN
    call "H_BASEMUL" ([e; x 1; x 2; x 3; x 0] @ rest0) (k1 + 1))
   [134,138; 140,146; 148,152] THEN
  MAP_EVERY (fun (k0,k1) ->
    ARM_STEPS_TAC EN2_EXEC (k0--k1) THEN
    call "H_INVNTT" ([e; x 0] @ rest) (k1 + 1))
   [154,155; 157,158; 160,161] THEN
  ARM_STEPS_TAC EN2_EXEC (163--165) THEN
  call "H_ADD1" [e; x 1; x 0; EN2_CONTENTS `X1`; EN2_CONTENTS `X0`; `pc:num`]
   166 THEN
  ARM_STEPS_TAC EN2_EXEC (167--168) THEN
  call "H_ADD2"
   [e; x 25; x 24; EN2_CONTENTS_OFF `X25`; EN2_CONTENTS_OFF `X24`; `pc:num`]
   169 THEN
  ARM_STEPS_TAC EN2_EXEC (170--172) THEN
  call "H_ADD3" [e; x 0; x 1; EN2_CONTENTS `X0`; EN2_CONTENTS `X1`; `pc:num`]
   173 THEN
  ARM_STEPS_TAC EN2_EXEC (174--175) THEN
  call "H_ADD4"
   [e; x 19; x 0; EN2_CONTENTS `X19`; EN2_CONTENTS `X0`; `pc:num`] 176 THEN
  MAP_EVERY (fun (k0,k1) ->
    ARM_STEPS_TAC EN2_EXEC (k0--k1) THEN
    call "H_REDUCE" ([e; x 0] @ rest0) (k1 + 1))
   [177,178; 180,181; 183,184] THEN
  ARM_STEPS_TAC EN2_EXEC (186--189) THEN INLINE_GOT_TAC THEN
  call "H_COMPRESS_D10" ([e; x 0; x 1; `guard:int64`] @ rest) 190 THEN
  ARM_STEPS_TAC EN2_EXEC (191--193) THEN
  call "H_COMPRESS_D10" ([e; x 0; x 1; `guard:int64`] @ rest) 194 THEN
  ARM_STEPS_TAC EN2_EXEC (195--197) THEN
  call "H_COMPRESS_D4" ([e; x 0; x 1; `guard:int64`] @ rest) 198 THEN
  MAP_EVERY (fun (k0,k) ->
    ARM_STEPS_TAC EN2_EXEC (k0--k) THEN LIBC_PLT_TAC EN2_EXEC k THEN
    LIBC_SAFE_CALL_TAC "H_MEMSET" EN2_EXEC
     [e; x 0; x 1; x 2; `read X30 s`] (ref EN_SAFE_ALLOWED) (k + 5))
   [199,202; 208,212; 218,222; 228,231; 237,240; 246,249; 255,258;
    264,267; 273,276] THEN
  ARM_STEPS_TAC EN2_EXEC (282--284) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC EN2_EXEC (285--300) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let MLKEM_NATIVE_INDCPA_ENC_K2_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE =
  prove
 (`!mf mc ea el ev.
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
           (word_sub stackpointer (word 12016),12016) /\
          nonoverlapping (pk,800) (word pc,libmlkem_size) /\
          ALLPAIRS nonoverlapping
           [(c,768); (word_sub stackpointer (word 12016),12016)]
           [(m,32); (pk,800); (coins,32); (word pc,libmlkem_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8);
            (word(pc + got_memcpy),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mlkem_native_libmlkem_gcc12_O2_mono_mc /\
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
                              (word_sub stackpointer (word 12016))
                              returnaddress (mlkem_slice 768 32 ek) /\
                       memaccess_inbounds e2
                        [m,32; pk,800; coins,32; c,768;
                         word_sub stackpointer (word 12016),12016;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8;
                         word(pc + got_memcpy),8; ea,el;
                         word(pc + rodata_mlk_KeccakF_RoundConstants),192;
                         word(pc + mlkem_poly_cbd3_consts),32;
                         word(pc + mlkem_poly_cbd2_consts),64;
                         word(pc + rodata_mlk_zetas),256;
                         word(pc + mlk_poly_invntt_tomont_c_consts),32]
                        [c,768; word_sub stackpointer (word 12016),12016]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(c,768);
                  memory :> bytes(word_sub stackpointer (word 12016),12016)])`,
  EN2_SAFE_INTRO_TAC THEN ASM_CASES_TAC `aligned 32 (stackpointer:int64)` THENL
   [EN2_SAFE_CASE_TAC 3776; EN2_SAFE_CASE_TAC 3760]);;
