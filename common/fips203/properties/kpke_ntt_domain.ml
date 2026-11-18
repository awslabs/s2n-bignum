(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The K-PKE algorithms in the NTT-domain form of FIPS 203 Algorithms 13,     *)
(* 14 and 15.                                                                 *)
(* ========================================================================= *)

needs "common/fips203/properties/encoding.ml";;

type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The K-PKE algorithms in the NTT-domain form of FIPS 203 Algorithms 13, 14 *)
(* and 15. Key generation and encryption need the assumption that the        *)
(* SampleNTT values used are < q, which holds whenever SampleNTT is          *)
(* well-defined, i.e. whenever the loop of FIPS 203 Algorithm 7 terminates.  *)
(* ------------------------------------------------------------------------- *)

let MLKEM_ENCODE_EQ = prove
 (`!d n f g. (!i. i < n ==> f i = g i)
             ==> mlkem_encode d n f = mlkem_encode d n g`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mlkem_encode] THEN AP_TERM_TAC THEN
  MATCH_MP_TAC NSUM_EQ THEN ASM_SIMP_TAC[IN_ELIM_THM]);;

let MLKEM_NTT_INV_EQ = prove
 (`!a b. (!i. i < 256 ==> a i = b i) ==> mlkem_ntt_inv a = mlkem_ntt_inv b`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mlkem_ntt_inv] THEN
  AP_TERM_TAC THEN ABS_TAC THEN ASM_MESON_TAC[]);;

let FIPS203_MULTIPLY_NTTS_EQ = prove
 (`!a a' b b' n.
        (!i. i < 256 ==> a i = a' i /\ b i = b' i) /\ n < 256
        ==> fips203_multiply_ntts a b n = fips203_multiply_ntts a' b' n`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[fips203_multiply_ntts] THEN
  COND_CASES_TAC THENL
   [FIRST_X_ASSUM(CHOOSE_THEN SUBST_ALL_TAC o REWRITE_RULE[EVEN_EXISTS]) THEN
    SUBGOAL_THEN `m < 128` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[ARITH_RULE `m < 128 ==> 2 * m + 1 < 256`];
    ASM_SIMP_TAC[ARITH_RULE `n < 256 ==> n - 1 < 256`]]);;

let MLKEM_CBD_IN_RQ = prove
 (`!eta b. mlkem_cbd eta b IN ring_carrier mlkem_rq`,
  REWRITE_TAC[mlkem_cbd] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[MLKEM_POLY_IN_RQ]);;

let MLKEM_DOT_IN_RQ = prove
 (`!k u v. mlkem_dot k u v IN ring_carrier mlkem_rq`,
  REWRITE_TAC[mlkem_dot; RING_SUM]);;

let MLKEM_SAMPLE_NTT_POS = prove
 (`!b i. &0 <= mlkem_sample_ntt b i`,
  REWRITE_TAC[mlkem_sample_ntt] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[INT_POS]);;

let MLKEM_DECODE_12_BOUNDS = prove
 (`!b i. &0 <= mlkem_decode 12 b i /\ mlkem_decode 12 b i < &3329`,
  REWRITE_TAC[mlkem_decode] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[INT_REM_POS_EQ; INT_LT_REM_EQ] THEN CONV_TAC INT_REDUCE_CONV);;

let MLKEM_RQ_COEFF_ADD = prove
 (`!p q k. p IN ring_carrier mlkem_rq /\ q IN ring_carrier mlkem_rq
           ==> coeff k (ring_add mlkem_rq p q) =
               ring_add mlkem_zq (coeff k p) (coeff k q)`,
  SIMP_TAC[MLKEM_RQ; mlkem_zqx; POLY_RING_CLAUSES; COEFF_POLY_ADD]);;

let MLKEM_RQ_COEFF_SUB = prove
 (`!p q k. p IN ring_carrier mlkem_rq /\ q IN ring_carrier mlkem_rq
           ==> coeff k (ring_sub mlkem_rq p q) =
               ring_sub mlkem_zq (coeff k p) (coeff k q)`,
  SIMP_TAC[MLKEM_RQ_SUB; mlkem_zqx; POLY_RING_CLAUSES; COEFF_POLY_SUB]);;

let MLKEM_NTT_DOT = prove
 (`!k u v n.
        (!j. j < k ==> u j IN ring_carrier mlkem_rq /\
                       v j IN ring_carrier mlkem_rq)
        ==> mlkem_ntt (mlkem_dot k u v) n =
            ring_sum mlkem_zq {j | j < k}
             (\j. fips203_multiply_ntts (mlkem_ntt (u j))
                                         (mlkem_ntt (v j)) n)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mlkem_dot] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) MLKEM_NTT_SUM o lhand o snd) THEN
  ASM_SIMP_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM; RING_MUL] THEN
  DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC RING_SUM_EQ THEN
  ASM_SIMP_TAC[IN_ELIM_THM; MLKEM_NTT_MULTIPLY]);;

let MLKEM_DOT_NTT_INV = prove
 (`!k a v.
        (!j n. j < k /\ n < 256 ==> &0 <= a j n /\ a j n < &3329) /\
        (!j. j < k ==> v j IN ring_carrier mlkem_rq)
        ==> mlkem_dot k (\j. mlkem_ntt_inv (a j)) v =
            mlkem_ntt_inv
             (\n. ring_sum mlkem_zq {j | j < k}
                   (\j. fips203_multiply_ntts (a j) (mlkem_ntt (v j)) n))`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC LAND_CONV
   [GSYM(MATCH_MP MLKEM_NTT_INV_NTT (SPEC_ALL MLKEM_DOT_IN_RQ))] THEN
  MATCH_MP_TAC MLKEM_NTT_INV_EQ THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  REWRITE_TAC[] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) MLKEM_NTT_DOT o lhand o snd) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[MLKEM_NTT_INV]; DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC `j:num` THEN
  REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
  MATCH_MP_TAC FIPS203_MULTIPLY_NTTS_EQ THEN ASM_SIMP_TAC[MLKEM_NTT_INV]);;

let KPKE_KEYGEN_FIPS = prove
 (`!k eta1 eta2 du dv d.
        (!i j n. i < k /\ j < k /\ n < 256
                 ==> mlkem_sample_ntt
                      (APPEND (FST(mlkem_g(APPEND d [word k])))
                              [word j; word i]) n < &3329)
        ==> kpke_keygen (k,eta1,eta2,du,dv) d =
            let rho,sigma = mlkem_g (APPEND d [word k]) in
            let Ahat = \i j. mlkem_sample_ntt (APPEND rho [word j; word i]) in
            let shat = \i. mlkem_ntt
                            (mlkem_cbd eta1 (mlkem_prf eta1 sigma (word i))) in
            let ehat = \i. mlkem_ntt
                            (mlkem_cbd eta1
                              (mlkem_prf eta1 sigma (word(k + i)))) in
            let that = \i n. ring_add mlkem_zq
                              (ring_sum mlkem_zq {j | j < k}
                                (\j. fips203_multiply_ntts
                                      (Ahat i j) (shat j) n))
                              (ehat i n) in
            APPEND (mlkem_encode 12 (256 * k)
                     (\n. that (n DIV 256) (n MOD 256))) rho,
            mlkem_encode 12 (256 * k) (\n. shat (n DIV 256) (n MOD 256))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[kpke_keygen] THEN
  SPEC_TAC(`mlkem_g (APPEND d [word k])`,`p:byte list#byte list`) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`rho:byte list`; `sigma:byte list`] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[] THEN DISCH_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC MLKEM_ENCODE_EQ THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  ABBREV_TAC `i = n DIV 256` THEN ABBREV_TAC `m = n MOD 256` THEN
  SUBGOAL_THEN `i < k /\ m < 256` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["i"; "m"] THEN
    ASM_SIMP_TAC[RDIV_LT_EQ; MOD_LT_EQ; ARITH_EQ];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!j. j < k
        ==> mlkem_ntt_inv (mlkem_sample_ntt (APPEND rho [word j; word i]))
            IN ring_carrier mlkem_rq /\
            !n'. n' < 256
                 ==> mlkem_ntt (mlkem_ntt_inv
                       (mlkem_sample_ntt (APPEND rho [word j; word i]))) n' =
                     mlkem_sample_ntt (APPEND rho [word j; word i]) n'`
  ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC MLKEM_NTT_INV THEN
    ASM_SIMP_TAC[MLKEM_SAMPLE_NTT_POS];
    ALL_TAC] THEN
  ASM_SIMP_TAC[MLKEM_NTT_ADD; MLKEM_DOT_IN_RQ; MLKEM_CBD_IN_RQ] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) MLKEM_NTT_DOT o lhand o snd) THEN
  ASM_SIMP_TAC[MLKEM_CBD_IN_RQ] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC `j:num` THEN
  REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
  MATCH_MP_TAC FIPS203_MULTIPLY_NTTS_EQ THEN ASM_SIMP_TAC[]);;

let KPKE_ENCRYPT_FIPS = prove
 (`!k eta1 eta2 du dv ek m r.
        (!i j n. i < k /\ j < k /\ n < 256
                 ==> mlkem_sample_ntt
                      (APPEND (mlkem_slice (384 * k) 32 ek) [word j; word i])
                      n < &3329)
        ==> kpke_encrypt (k,eta1,eta2,du,dv) ek m r =
            let that = \i n. mlkem_decode 12 ek (256 * i + n) in
            let rho = mlkem_slice (384 * k) 32 ek in
            let Ahat = \i j. mlkem_sample_ntt (APPEND rho [word j; word i]) in
            let y = \i. mlkem_cbd eta1 (mlkem_prf eta1 r (word i)) in
            let e1 = \i. mlkem_cbd eta2 (mlkem_prf eta2 r (word(k + i))) in
            let e2 = mlkem_cbd eta2 (mlkem_prf eta2 r (word(2 * k))) in
            let yhat = \i. mlkem_ntt (y i) in
            let u = \i. ring_add mlkem_rq
                         (mlkem_ntt_inv
                           (\n. ring_sum mlkem_zq {j | j < k}
                                 (\j. fips203_multiply_ntts
                                       (Ahat j i) (yhat j) n)))
                         (e1 i) in
            let mu = mlkem_poly(\j. mlkem_decompress 1 (mlkem_decode 1 m j)) in
            let v = ring_add mlkem_rq
                     (ring_add mlkem_rq
                       (mlkem_ntt_inv
                         (\n. ring_sum mlkem_zq {j | j < k}
                               (\j. fips203_multiply_ntts
                                     (that j) (yhat j) n)))
                       e2) mu in
            APPEND
             (mlkem_encode du (256 * k)
               (\n. mlkem_compress du (coeff (n MOD 256) (u(n DIV 256)))))
             (mlkem_encode dv 256 (\n. mlkem_compress dv (coeff n v)))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[kpke_encrypt] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[] THEN
  SIMP_TAC[MLKEM_DOT_NTT_INV; MLKEM_DECODE_12_BOUNDS; MLKEM_CBD_IN_RQ] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC MLKEM_ENCODE_EQ THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC MLKEM_DOT_NTT_INV THEN REWRITE_TAC[MLKEM_CBD_IN_RQ] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[MLKEM_SAMPLE_NTT_POS] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[RDIV_LT_EQ; ARITH_EQ]);;

let KPKE_DECRYPT_FIPS = prove
 (`!k eta1 eta2 du dv dk c.
        kpke_decrypt (k,eta1,eta2,du,dv) dk c =
        let c2 = mlkem_slice (32 * du * k) (32 * dv) c in
        let u = \i. mlkem_poly
                     (\j. mlkem_decompress du
                           (mlkem_decode du c (256 * i + j))) in
        let v = mlkem_poly(\j. mlkem_decompress dv (mlkem_decode dv c2 j)) in
        let shat = \i n. mlkem_decode 12 dk (256 * i + n) in
        let w = ring_sub mlkem_rq v
                 (mlkem_ntt_inv
                   (\n. ring_sum mlkem_zq {j | j < k}
                         (\j. fips203_multiply_ntts
                               (shat j) (mlkem_ntt (u j)) n))) in
        mlkem_encode 1 256 (\j. mlkem_compress 1 (coeff j w))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[kpke_decrypt] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[] THEN
  SIMP_TAC[MLKEM_DOT_NTT_INV; MLKEM_DECODE_12_BOUNDS; MLKEM_POLY_IN_RQ]);;

(* ------------------------------------------------------------------------- *)
(* The message that K-PKE decryption returns has 32 bytes.                   *)
(* ------------------------------------------------------------------------- *)

let MLKEM_KPKE_DECRYPT_LENGTH = prove
 (`!p dk c. LENGTH (kpke_decrypt p dk c) = 32`,
  REWRITE_TAC[FORALL_PAIR_THM; kpke_decrypt] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[MLKEM_ENCODE_LENGTH] THEN CONV_TAC NUM_REDUCE_CONV);;

(* Restore the default setting for anything loaded later.                    *)

type_invention_error := false;;
