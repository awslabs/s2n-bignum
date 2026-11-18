(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Z_q and R_q: R_q is (isomorphic to) Z_q[X]/(X^256 + 1).                    *)
(* ========================================================================= *)

needs "common/fips203/properties/poly_remainder.ml";;

type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Z_q and R_q: R_q consists of the polynomials of degree < 256, which are   *)
(* in bijection with their coefficient arrays.                               *)
(* ------------------------------------------------------------------------- *)

let PRIME_3329 = prove
 (`prime 3329`,
  CONV_TAC PRIME_CONV);;

let MLKEM_ZQ = prove
 (`field mlkem_zq /\ ~trivial_ring mlkem_zq /\
   ring_carrier mlkem_zq = {x | &0 <= x /\ x < &3329} /\
   ring_0 mlkem_zq = &0 /\ ring_1 mlkem_zq = &1 /\
   ring_neg mlkem_zq = (\a. --a rem &3329) /\
   ring_add mlkem_zq = (\a b. (a + b) rem &3329) /\
   ring_sub mlkem_zq = (\a b. (a - b) rem &3329) /\
   ring_mul mlkem_zq = (\a b. (a * b) rem &3329) /\
   ring_pow mlkem_zq = (\a k. a pow k rem &3329)`,
  REWRITE_TAC[mlkem_zq; FIELD_INTEGER_MOD_RING; TRIVIAL_INTEGER_MOD_RING;
              PRIME_3329] THEN
  SIMP_TAC[INTEGER_MOD_RING_CLAUSES; ARITH_RULE `0 < 3329`] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC INT_REDUCE_CONV);;

let IN_MLKEM_ZQ = prove
 (`!x. x IN ring_carrier mlkem_zq <=> &0 <= x /\ x < &3329`,
  REWRITE_TAC[MLKEM_ZQ; IN_ELIM_THM]);;

let MLKEM_ZQ_UNIT_1 = prove
 (`ring_unit mlkem_zq (&1)`,
  MESON_TAC[RING_UNIT_1; MLKEM_ZQ]);;

let POLY_REM_SMALL = prove
 (`!(r:A ring) p m.
        p IN ring_carrier(poly_ring r (:1)) /\
        m IN ring_carrier(poly_ring r (:1)) /\
        (poly_deg r p < poly_deg r m \/ p = ring_0(poly_ring r (:1)))
        ==> poly_rem r p m = p`,
  REPEAT STRIP_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) POLY_REM_UNIQUE o snd) THEN
  ASM_SIMP_TAC[RING_SUB_REFL; RING_DIVIDES_0; COND_ID]);;

let POLY_XN_PLUS_1 = prove
 (`!(r:A ring) n.
        ~trivial_ring r /\ ~(n = 0)
        ==> ring_add (poly_ring r (:1))
              (ring_pow (poly_ring r (:1)) (poly_var r one) n)
              (ring_1 (poly_ring r (:1)))
            IN ring_carrier(poly_ring r (:1)) /\
            poly_deg r (ring_add (poly_ring r (:1))
              (ring_pow (poly_ring r (:1)) (poly_var r one) n)
              (ring_1 (poly_ring r (:1)))) = n /\
            coeff n (ring_add (poly_ring r (:1))
              (ring_pow (poly_ring r (:1)) (poly_var r one) n)
              (ring_1 (poly_ring r (:1)))) = ring_1 r`,
  REPEAT GEN_TAC THEN REWRITE_TAC[TRIVIAL_RING_10] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[RING_ADD; RING_POW; POLY_VAR_UNIV; RING_1] THEN
  MATCH_MP_TAC(TAUT `q /\ (q ==> p) ==> p /\ q`) THEN CONJ_TAC THENL
   [REWRITE_TAC[POLY_RING_CLAUSES; COEFF_POLY_ADD; COEFF_POLY_VARPOW;
                COEFF_POLY_1] THEN
    ASM_SIMP_TAC[RING_ADD_RZERO; RING_1];
    DISCH_TAC THEN MATCH_MP_TAC POLY_DEG_EQ_COEFF THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC RING_POLYNOMIAL_IMP_POWERSERIES THEN
      ASM_SIMP_TAC[RING_POLYNOMIAL; RING_ADD; RING_POW; POLY_VAR_UNIV; RING_1];
      X_GEN_TAC `d:num` THEN
      REWRITE_TAC[POLY_RING_CLAUSES; COEFF_POLY_ADD; COEFF_POLY_VARPOW;
                  COEFF_POLY_1] THEN
      ASM_CASES_TAC `d = 0` THEN ASM_REWRITE_TAC[] THENL
       [ARITH_TAC; ALL_TAC] THEN
      ASM_CASES_TAC `d:num = n` THEN ASM_REWRITE_TAC[LE_REFL] THEN
      ASM_SIMP_TAC[RING_ADD_RZERO; RING_0]]]);;

let MLKEM_RQ_MODULUS = prove
 (`ring_add mlkem_zqx (ring_pow mlkem_zqx mlkem_X 256) (ring_1 mlkem_zqx)
   IN ring_carrier mlkem_zqx /\
   poly_deg mlkem_zq
    (ring_add mlkem_zqx (ring_pow mlkem_zqx mlkem_X 256) (ring_1 mlkem_zqx)) =
   256 /\
   coeff 256
    (ring_add mlkem_zqx (ring_pow mlkem_zqx mlkem_X 256) (ring_1 mlkem_zqx)) =
   &1`,
  REWRITE_TAC[mlkem_zqx; mlkem_X] THEN
  MP_TAC(ISPECL [`mlkem_zq`; `256`] POLY_XN_PLUS_1) THEN
  REWRITE_TAC[MLKEM_ZQ; ARITH_EQ]);;

(* So R_q is (isomorphic to) Z_q[X]/(X^256 + 1).                             *)

let MLKEM_RQ_ISOMORPHIC_QUOTIENT = prove
 (`quotient_ring mlkem_zqx
     (ideal_generated mlkem_zqx
       {ring_add mlkem_zqx (ring_pow mlkem_zqx mlkem_X 256)
                 (ring_1 mlkem_zqx)})
   isomorphic_ring mlkem_rq`,
  REWRITE_TAC[mlkem_rq] THEN REWRITE_TAC[mlkem_zqx] THEN
  MATCH_MP_TAC POLY_MOD_RING_ISOMORPHIC_QUOTIENT THEN
  REWRITE_TAC[GSYM mlkem_zqx; MLKEM_RQ_MODULUS] THEN
  MP_TAC(ISPEC `mlkem_zq` RING_UNIT_1) THEN REWRITE_TAC[MLKEM_ZQ]);;

let MLKEM_RQ_REM = prove
 (`!p. p IN ring_carrier mlkem_zqx
       ==> (poly_rem mlkem_zq p
              (ring_add mlkem_zqx (ring_pow mlkem_zqx mlkem_X 256)
                                  (ring_1 mlkem_zqx)) = p <=>
            poly_deg mlkem_zq p < 256)`,
  REPEAT STRIP_TAC THEN MP_TAC MLKEM_RQ_MODULUS THEN
  ABBREV_TAC `m = ring_add mlkem_zqx (ring_pow mlkem_zqx mlkem_X 256)
                                     (ring_1 mlkem_zqx)` THEN
  STRIP_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) POLY_REM_UNIQUE o lhand o snd) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[mlkem_zqx]) THEN
  ASM_SIMP_TAC[RING_SUB_REFL; RING_DIVIDES_0; MLKEM_ZQ_UNIT_1] THEN
  DISCH_THEN SUBST1_TAC THEN EQ_TAC THEN SIMP_TAC[] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[POLY_DEG_0; POLY_RING_CLAUSES] THEN
  ARITH_TAC);;

let MLKEM_RQ_CARRIER = prove
 (`ring_carrier mlkem_rq =
     {p | p IN ring_carrier mlkem_zqx /\ poly_deg mlkem_zq p < 256}`,
  MP_TAC(ISPECL [`mlkem_zq`;
                 `ring_add mlkem_zqx (ring_pow mlkem_zqx mlkem_X 256)
                                     (ring_1 mlkem_zqx)`] POLY_MOD_RING) THEN
  REWRITE_TAC[GSYM mlkem_zqx; GSYM mlkem_rq; MLKEM_RQ_MODULUS] THEN
  DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN MESON_TAC[MLKEM_RQ_REM]);;

let IN_MLKEM_RQ = prove
 (`!p. p IN ring_carrier mlkem_rq <=>
       p IN ring_carrier mlkem_zqx /\ poly_deg mlkem_zq p < 256`,
  REWRITE_TAC[MLKEM_RQ_CARRIER; IN_ELIM_THM]);;

let MLKEM_RQ = prove
 (`ring_0 mlkem_rq = ring_0 mlkem_zqx /\
   ring_1 mlkem_rq = ring_1 mlkem_zqx /\
   (!p. p IN ring_carrier mlkem_rq
        ==> ring_neg mlkem_rq p = ring_neg mlkem_zqx p) /\
   (!p q. p IN ring_carrier mlkem_rq /\ q IN ring_carrier mlkem_rq
          ==> ring_add mlkem_rq p q = ring_add mlkem_zqx p q) /\
   (!p q. ring_mul mlkem_rq p q =
          poly_rem mlkem_zq (ring_mul mlkem_zqx p q)
            (ring_add mlkem_zqx (ring_pow mlkem_zqx mlkem_X 256)
                                (ring_1 mlkem_zqx)))`,
  MP_TAC(ISPECL [`mlkem_zq`;
                 `ring_add mlkem_zqx (ring_pow mlkem_zqx mlkem_X 256)
                                     (ring_1 mlkem_zqx)`] POLY_MOD_RING) THEN
  REWRITE_TAC[GSYM mlkem_zqx; GSYM mlkem_rq; MLKEM_RQ_MODULUS] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[IN_MLKEM_RQ] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[MLKEM_RQ_REM; RING_0; RING_1; RING_NEG;
                                     RING_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[mlkem_zqx; GSYM RING_POLYNOMIAL]) THEN
  REWRITE_TAC[mlkem_zqx; POLY_RING_CLAUSES; POLY_DEG_0; POLY_DEG_1] THEN
  ASM_SIMP_TAC[POLY_DEG_NEG; ARITH] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) POLY_DEG_ADD_LE o lhand o snd) THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let COEFF_MLKEM_POLY = prove
 (`!a i. coeff i (mlkem_poly a) = if i < 256 then a i rem &3329 else &0`,
  REWRITE_TAC[coeff; mlkem_poly]);;

let MLKEM_POLY_IN_RQ = prove
 (`!a. mlkem_poly a IN ring_carrier mlkem_rq`,
  GEN_TAC THEN
  SUBGOAL_THEN `ring_polynomial mlkem_zq (mlkem_poly a)` ASSUME_TAC THENL
   [REWRITE_TAC[ring_polynomial; ring_powerseries; FINITE_MONOMIAL_VARS_1;
                INFINITE; IN_MLKEM_ZQ] THEN
    REWRITE_TAC[mlkem_poly] THEN CONJ_TAC THENL
     [GEN_TAC THEN COND_CASES_TAC THEN
      REWRITE_TAC[INT_LE_REFL; INT_REM_POS_EQ; INT_LT_REM_EQ] THEN
      CONV_TAC INT_REDUCE_CONV;
      MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `IMAGE (\i (v:1). i) {i | i < 256}` THEN
      SIMP_TAC[FINITE_IMAGE; FINITE_NUMSEG_LT; SUBSET; IN_ELIM_THM] THEN
      REWRITE_TAC[FORALL_FUN_FROM_1; IN_IMAGE; IN_ELIM_THM; MLKEM_ZQ] THEN
      X_GEN_TAC `i:num` THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
      DISCH_TAC THEN EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[IN_MLKEM_RQ; mlkem_zqx; POLY_RING; SUBSET_UNIV;
                  IN_ELIM_THM] THEN
  MATCH_MP_TAC(ARITH_RULE `x <= 255 ==> x < 256`) THEN
  ASM_SIMP_TAC[POLY_DEG_LE_COEFF_EQ; COEFF_MLKEM_POLY; MLKEM_ZQ] THEN
  GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let MLKEM_POLY_COEFF = prove
 (`!p. p IN ring_carrier mlkem_rq ==> mlkem_poly (\i. coeff i p) = p`,
  REWRITE_TAC[IN_MLKEM_RQ; mlkem_zqx; POLY_RING; IN_ELIM_THM] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[FUN_EQ_THM; FORALL_FUN_FROM_1] THEN
  X_GEN_TAC `i:num` THEN REWRITE_TAC[mlkem_poly] THEN
  REWRITE_TAC[GSYM COEFF] THEN COND_CASES_TAC THENL
   [MATCH_MP_TAC INT_REM_LT THEN
    MP_TAC(ISPECL [`mlkem_zq`; `p:(1->num)->int`; `i:num`]
                  COEFF_IN_CARRIER_ALT) THEN
    ASM_REWRITE_TAC[IN_MLKEM_ZQ] THEN INT_ARITH_TAC;
    MP_TAC(ISPECL [`mlkem_zq`; `p:(1->num)->int`; `i:num`]
                  COEFF_ABOVE_DEG) THEN
    ASM_REWRITE_TAC[MLKEM_ZQ] THEN ANTS_TAC THENL
     [ASM_ARITH_TAC; DISCH_THEN(SUBST1_TAC o SYM) THEN REFL_TAC]]);;

let MLKEM_RQ_EQ = prove
 (`!p q. p IN ring_carrier mlkem_rq /\ q IN ring_carrier mlkem_rq
         ==> (p = q <=> !i. i < 256 ==> coeff i p = coeff i q)`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN SIMP_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPEC `p:(1->num)->int` MLKEM_POLY_COEFF) THEN
  MP_TAC(SPEC `q:(1->num)->int` MLKEM_POLY_COEFF) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[mlkem_poly; FUN_EQ_THM] THEN GEN_TAC THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[]);;


(* ------------------------------------------------------------------------- *)
(* zeta = 17 is a primitive 256-th root of unity mod q, so the 128 values    *)
(* zeta^(2 * BitRev7(i) + 1) are distinct.                                   *)
(* ------------------------------------------------------------------------- *)

let BITREVERSE7_BOUND = prove
 (`!i. i < 128 ==> bitreverse7 i < 128`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[BITREVERSE7_ALT] THEN
  MP_TAC(ISPEC `word_reversefields 1 (word i:7 word)` VAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_CONV `dimindex(:7)`] THEN ARITH_TAC);;

let BITREVERSE7_INJ = prove
 (`!i j. i < 128 /\ j < 128 /\ bitreverse7 i = bitreverse7 j ==> i = j`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `val(word_reversefields 1 (word i:7 word)) =
    val(word_reversefields 1 (word j:7 word))`
  MP_TAC THENL [ASM_MESON_TAC[BITREVERSE7_ALT]; ALL_TAC] THEN
  REWRITE_TAC[VAL_EQ] THEN
  DISCH_THEN(MP_TAC o AP_TERM `word_reversefields 1:7 word->7 word`) THEN
  REWRITE_TAC[WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
  REWRITE_TAC[WORD_EQ; DIMINDEX_CONV `dimindex(:7)`; CONG] THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE `x < 128 ==> x < 2 EXP 7`]);;

let MLKEM_ZETA_ORDER = prove
 (`order 3329 17 = 256`,
  MP_TAC(SPECL [`3329`; `17`; `256`] ORDER_DIVIDES) THEN
  MP_TAC(SPECL [`3329`; `17`; `128`] ORDER_DIVIDES) THEN
  REWRITE_TAC[CONG] THEN CONV_TAC(ONCE_DEPTH_CONV EXP_MOD_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN
  REWRITE_TAC[ARITH_RULE `256 = 2 EXP 8`; ARITH_RULE `128 = 2 EXP 7`] THEN
  SIMP_TAC[DIVIDES_PRIMEPOW; PRIME_2] THEN
  DISCH_TAC THEN DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o REWRITE_RULE[NOT_EXISTS_THM]) THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let MLKEM_ZETA_EXP_INJ = prove
 (`!a b. a < 256 /\ b < 256 /\ (17 EXP a == 17 EXP b) (mod 3329)
         ==> a = b`,
  let lemma = prove
   (`!a b. a <= b /\ b < 256 /\ (17 EXP a == 17 EXP b) (mod 3329)
           ==> a = b`,
    REPEAT STRIP_TAC THEN
    UNDISCH_TAC `(17 EXP a == 17 EXP b) (mod 3329)` THEN
    SUBGOAL_THEN `17 EXP b = 17 EXP a * 17 EXP (b - a)` SUBST1_TAC THENL
     [REWRITE_TAC[GSYM EXP_ADD] THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `coprime(17 EXP a,3329)` MP_TAC THENL
     [ONCE_REWRITE_TAC[COPRIME_SYM] THEN MATCH_MP_TAC COPRIME_EXP THEN
      CONV_TAC COPRIME_CONV;
      ALL_TAC] THEN
    REWRITE_TAC[IMP_IMP] THEN
    DISCH_THEN(MP_TAC o MATCH_MP (NUMBER_RULE
     `!a x n. coprime(a,n) /\ (a == a * x) (mod n) ==> (x == 1) (mod n)`)) THEN
    REWRITE_TAC[ORDER_DIVIDES; MLKEM_ZETA_ORDER] THEN
    DISCH_THEN(MP_TAC o MATCH_MP DIVIDES_LE) THEN ASM_ARITH_TAC) in
  REPEAT STRIP_TAC THEN
  DISJ_CASES_TAC(ARITH_RULE `a:num <= b \/ b <= a`) THEN
  ASM_MESON_TAC[lemma; CONG_SYM]);;

let MLKEM_GAMMA_INJ = prove
 (`!i j. i < 128 /\ j < 128 /\
         ring_pow mlkem_zq (&17) (2 * bitreverse7 i + 1) =
         ring_pow mlkem_zq (&17) (2 * bitreverse7 j + 1)
         ==> i = j`,
  REWRITE_TAC[MLKEM_ZQ; INT_OF_NUM_POW; INT_OF_NUM_REM; INT_OF_NUM_EQ] THEN
  REWRITE_TAC[GSYM CONG] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC BITREVERSE7_INJ THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(ARITH_RULE `2 * x + 1 = 2 * y + 1 ==> x = y`) THEN
  MATCH_MP_TAC MLKEM_ZETA_EXP_INJ THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPEC `i:num` BITREVERSE7_BOUND) THEN
  MP_TAC(SPEC `j:num` BITREVERSE7_BOUND) THEN ASM_REWRITE_TAC[] THEN
  ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Values of Z_q and coefficients of R_q lie in [0, q), and                  *)
(* mlkem_poly a depends only on a 0, ..., a 255.                             *)
(* ------------------------------------------------------------------------- *)

let COEFF_RQ_BOUNDS = prove
 (`!p i. p IN ring_carrier mlkem_rq
         ==> &0 <= coeff i p /\ coeff i p < &3329`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `coeff i p = coeff i (mlkem_poly (\j. coeff j p))`
   SUBST1_TAC THENL
   [ASM_SIMP_TAC[MLKEM_POLY_COEFF]; ALL_TAC] THEN
  REWRITE_TAC[COEFF_MLKEM_POLY] THEN
  COND_CASES_TAC THEN CONV_TAC INT_REDUCE_CONV THEN
  REWRITE_TAC[INT_REM_POS_EQ; INT_LT_REM_EQ] THEN
  CONV_TAC INT_REDUCE_CONV);;

let KPKE_ZQ_BOUNDS = prove
 (`!x. x IN ring_carrier mlkem_zq ==> &0 <= x /\ x < &3329`,
  REWRITE_TAC[IN_MLKEM_ZQ]);;

let KPKE_RING_SUM_BOUNDS = prove
 (`!(s:A->bool) f. &0 <= ring_sum mlkem_zq s f /\
                   ring_sum mlkem_zq s f < &3329`,
  REWRITE_TAC[GSYM IN_MLKEM_ZQ; RING_SUM]);;

let KPKE_ZQ_ADD_BOUNDS = prove
 (`!x y. (&0 <= x /\ x < &3329) /\ (&0 <= y /\ y < &3329)
         ==> &0 <= ring_add mlkem_zq x y /\ ring_add mlkem_zq x y < &3329`,
  REWRITE_TAC[GSYM IN_MLKEM_ZQ] THEN SIMP_TAC[RING_ADD]);;

let KPKE_MLKEM_POLY_EQ = prove
 (`!a b. (!i. i < 256 ==> a i = b i) ==> mlkem_poly a = mlkem_poly b`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[mlkem_poly; FUN_EQ_THM; FORALL_FUN_FROM_1] THEN
  X_GEN_TAC `i:num` THEN REWRITE_TAC[] THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[]);;

(* Restore the default setting for anything loaded later.                    *)

type_invention_error := false;;
