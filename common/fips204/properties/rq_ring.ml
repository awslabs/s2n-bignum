(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Properties of the handwritten FIPS 204 specification                      *)
(* (common/fips204/fips204.ml), part 1: the rings Z_q and R_q and their      *)
(* arithmetic on coefficient arrays. The generic lemmas about polynomial     *)
(* rings are in common/poly_mod_ring.ml.                                     *)
(* ========================================================================= *)

needs "common/fips204/fips204.ml";;
needs "Library/isum.ml";;
needs "common/poly_mod_ring.ml";;

type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Z_q and R_q: Z_q is the field of integers mod q = 8380417, represented by *)
(* [0,q), and R_q consists of the polynomials of degree < 256 over it, which *)
(* are in bijection with their coefficient arrays (mldsa_poly).              *)
(* ------------------------------------------------------------------------- *)

let PRIME_8380417 = prove
 (`prime 8380417`,
  CONV_TAC PRIME_CONV);;

let MLDSA_ZQ = prove
 (`field mldsa_zq /\ ~trivial_ring mldsa_zq /\
   ring_carrier mldsa_zq = {x | &0 <= x /\ x < &8380417} /\
   ring_0 mldsa_zq = &0 /\ ring_1 mldsa_zq = &1 /\
   ring_neg mldsa_zq = (\a. --a rem &8380417) /\
   ring_add mldsa_zq = (\a b. (a + b) rem &8380417) /\
   ring_sub mldsa_zq = (\a b. (a - b) rem &8380417) /\
   ring_mul mldsa_zq = (\a b. (a * b) rem &8380417) /\
   ring_pow mldsa_zq = (\a k. a pow k rem &8380417)`,
  REWRITE_TAC[mldsa_zq; FIELD_INTEGER_MOD_RING; TRIVIAL_INTEGER_MOD_RING;
              PRIME_8380417] THEN
  SIMP_TAC[INTEGER_MOD_RING_CLAUSES; ARITH_RULE `0 < 8380417`] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC INT_REDUCE_CONV);;

let IN_MLDSA_ZQ = prove
 (`!x. x IN ring_carrier mldsa_zq <=> &0 <= x /\ x < &8380417`,
  REWRITE_TAC[MLDSA_ZQ; IN_ELIM_THM]);;

let MLDSA_ZQ_UNIT_1 = prove
 (`ring_unit mldsa_zq (&1)`,
  MESON_TAC[RING_UNIT_1; MLDSA_ZQ]);;

let MLDSA_RQ_MODULUS = prove
 (`ring_add mldsa_zqx (ring_pow mldsa_zqx mldsa_X 256) (ring_1 mldsa_zqx)
   IN ring_carrier mldsa_zqx /\
   poly_deg mldsa_zq
    (ring_add mldsa_zqx (ring_pow mldsa_zqx mldsa_X 256) (ring_1 mldsa_zqx)) =
   256 /\
   coeff 256
    (ring_add mldsa_zqx (ring_pow mldsa_zqx mldsa_X 256) (ring_1 mldsa_zqx)) =
   &1`,
  REWRITE_TAC[mldsa_zqx; mldsa_X] THEN
  MP_TAC(ISPECL [`mldsa_zq`; `256`] POLY_XN_PLUS_1) THEN
  REWRITE_TAC[MLDSA_ZQ; ARITH_EQ]);;

(* So R_q is (isomorphic to) Z_q[X]/(X^256 + 1).                             *)

let MLDSA_RQ_ISOMORPHIC_QUOTIENT = prove
 (`quotient_ring mldsa_zqx
     (ideal_generated mldsa_zqx
       {ring_add mldsa_zqx (ring_pow mldsa_zqx mldsa_X 256)
                 (ring_1 mldsa_zqx)})
   isomorphic_ring mldsa_rq`,
  REWRITE_TAC[mldsa_rq] THEN REWRITE_TAC[mldsa_zqx] THEN
  MATCH_MP_TAC POLY_MOD_RING_ISOMORPHIC_QUOTIENT THEN
  REWRITE_TAC[GSYM mldsa_zqx; MLDSA_RQ_MODULUS] THEN
  MP_TAC(ISPEC `mldsa_zq` RING_UNIT_1) THEN REWRITE_TAC[MLDSA_ZQ]);;

let MLDSA_RQ_REM = prove
 (`!p. p IN ring_carrier mldsa_zqx
       ==> (poly_rem mldsa_zq p
              (ring_add mldsa_zqx (ring_pow mldsa_zqx mldsa_X 256)
                                  (ring_1 mldsa_zqx)) = p <=>
            poly_deg mldsa_zq p < 256)`,
  REPEAT STRIP_TAC THEN MP_TAC MLDSA_RQ_MODULUS THEN
  ABBREV_TAC `m = ring_add mldsa_zqx (ring_pow mldsa_zqx mldsa_X 256)
                                     (ring_1 mldsa_zqx)` THEN
  STRIP_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) POLY_REM_UNIQUE o lhand o snd) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[mldsa_zqx]) THEN
  ASM_SIMP_TAC[RING_SUB_REFL; RING_DIVIDES_0; MLDSA_ZQ_UNIT_1] THEN
  DISCH_THEN SUBST1_TAC THEN EQ_TAC THEN SIMP_TAC[] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[POLY_DEG_0; POLY_RING_CLAUSES] THEN
  ARITH_TAC);;

let MLDSA_RQ_CARRIER = prove
 (`ring_carrier mldsa_rq =
     {p | p IN ring_carrier mldsa_zqx /\ poly_deg mldsa_zq p < 256}`,
  MP_TAC(ISPECL [`mldsa_zq`;
                 `ring_add mldsa_zqx (ring_pow mldsa_zqx mldsa_X 256)
                                     (ring_1 mldsa_zqx)`] POLY_MOD_RING) THEN
  REWRITE_TAC[GSYM mldsa_zqx; GSYM mldsa_rq; MLDSA_RQ_MODULUS] THEN
  DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN MESON_TAC[MLDSA_RQ_REM]);;

let IN_MLDSA_RQ = prove
 (`!p. p IN ring_carrier mldsa_rq <=>
       p IN ring_carrier mldsa_zqx /\ poly_deg mldsa_zq p < 256`,
  REWRITE_TAC[MLDSA_RQ_CARRIER; IN_ELIM_THM]);;

let MLDSA_RQ = prove
 (`ring_0 mldsa_rq = ring_0 mldsa_zqx /\
   ring_1 mldsa_rq = ring_1 mldsa_zqx /\
   (!p. p IN ring_carrier mldsa_rq
        ==> ring_neg mldsa_rq p = ring_neg mldsa_zqx p) /\
   (!p q. p IN ring_carrier mldsa_rq /\ q IN ring_carrier mldsa_rq
          ==> ring_add mldsa_rq p q = ring_add mldsa_zqx p q) /\
   (!p q. ring_mul mldsa_rq p q =
          poly_rem mldsa_zq (ring_mul mldsa_zqx p q)
            (ring_add mldsa_zqx (ring_pow mldsa_zqx mldsa_X 256)
                                (ring_1 mldsa_zqx)))`,
  MP_TAC(ISPECL [`mldsa_zq`;
                 `ring_add mldsa_zqx (ring_pow mldsa_zqx mldsa_X 256)
                                     (ring_1 mldsa_zqx)`] POLY_MOD_RING) THEN
  REWRITE_TAC[GSYM mldsa_zqx; GSYM mldsa_rq; MLDSA_RQ_MODULUS] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[IN_MLDSA_RQ] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[MLDSA_RQ_REM; RING_0; RING_1; RING_NEG;
                                     RING_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[mldsa_zqx; GSYM RING_POLYNOMIAL]) THEN
  REWRITE_TAC[mldsa_zqx; POLY_RING_CLAUSES; POLY_DEG_0; POLY_DEG_1] THEN
  ASM_SIMP_TAC[POLY_DEG_NEG; ARITH] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) POLY_DEG_ADD_LE o lhand o snd) THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let MLDSA_RQ_SUB = prove
 (`!p q. p IN ring_carrier mldsa_rq /\ q IN ring_carrier mldsa_rq
         ==> ring_sub mldsa_rq p q = ring_sub mldsa_zqx p q`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ring_sub] THEN
  ASM_SIMP_TAC[MLDSA_RQ; RING_NEG]);;

let COEFF_MLDSA_POLY = prove
 (`!a i. coeff i (mldsa_poly a) = if i < 256 then a i rem &8380417 else &0`,
  REWRITE_TAC[coeff; mldsa_poly]);;

let MLDSA_POLY_IN_RQ = prove
 (`!a. mldsa_poly a IN ring_carrier mldsa_rq`,
  GEN_TAC THEN
  SUBGOAL_THEN `ring_polynomial mldsa_zq (mldsa_poly a)` ASSUME_TAC THENL
   [REWRITE_TAC[ring_polynomial; ring_powerseries; FINITE_MONOMIAL_VARS_1;
                INFINITE; IN_MLDSA_ZQ] THEN
    REWRITE_TAC[mldsa_poly] THEN CONJ_TAC THENL
     [GEN_TAC THEN COND_CASES_TAC THEN
      REWRITE_TAC[INT_LE_REFL; INT_REM_POS_EQ; INT_LT_REM_EQ] THEN
      CONV_TAC INT_REDUCE_CONV;
      MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `IMAGE (\i (v:1). i) {i | i < 256}` THEN
      SIMP_TAC[FINITE_IMAGE; FINITE_NUMSEG_LT; SUBSET; IN_ELIM_THM] THEN
      REWRITE_TAC[FORALL_FUN_FROM_1; IN_IMAGE; IN_ELIM_THM; MLDSA_ZQ] THEN
      X_GEN_TAC `i:num` THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
      DISCH_TAC THEN EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[IN_MLDSA_RQ; mldsa_zqx; POLY_RING; SUBSET_UNIV;
                  IN_ELIM_THM] THEN
  MATCH_MP_TAC(ARITH_RULE `x <= 255 ==> x < 256`) THEN
  ASM_SIMP_TAC[POLY_DEG_LE_COEFF_EQ; COEFF_MLDSA_POLY; MLDSA_ZQ] THEN
  GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let MLDSA_POLY_IN_ZQX = prove
 (`!a. mldsa_poly a IN ring_carrier mldsa_zqx`,
  MESON_TAC[MLDSA_POLY_IN_RQ; IN_MLDSA_RQ]);;

let MLDSA_RQ_COEFF = prove
 (`!p k. p IN ring_carrier mldsa_rq
         ==> &0 <= coeff k p /\ coeff k p < &8380417`,
  REWRITE_TAC[IN_MLDSA_RQ; mldsa_zqx] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`mldsa_zq`; `p:(1->num)->int`; `k:num`]
                COEFF_POLY_IN_CARRIER) THEN
  ASM_REWRITE_TAC[IN_MLDSA_ZQ] THEN SIMP_TAC[]);;

let MLDSA_RQ_COEFF_ZERO = prove
 (`!p k. p IN ring_carrier mldsa_rq /\ 256 <= k ==> coeff k p = &0`,
  REWRITE_TAC[IN_MLDSA_RQ; mldsa_zqx] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`mldsa_zq`; `p:(1->num)->int`; `k:num`] COEFF_ABOVE_DEG) THEN
  ASM_REWRITE_TAC[RING_POLYNOMIAL; MLDSA_ZQ] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC);;

let MLDSA_POLY_COEFF = prove
 (`!p. p IN ring_carrier mldsa_rq ==> mldsa_poly (\i. coeff i p) = p`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[FUN_EQ_THM; FORALL_FUN_FROM_1] THEN
  X_GEN_TAC `i:num` THEN REWRITE_TAC[mldsa_poly] THEN
  REWRITE_TAC[GSYM COEFF] THEN COND_CASES_TAC THENL
   [MATCH_MP_TAC INT_REM_LT THEN ASM_SIMP_TAC[MLDSA_RQ_COEFF];
    RULE_ASSUM_TAC(REWRITE_RULE[IN_MLDSA_RQ; mldsa_zqx; POLY_RING;
                                IN_ELIM_THM]) THEN
    MP_TAC(ISPECL [`mldsa_zq`; `p:(1->num)->int`; `i:num`]
                  COEFF_ABOVE_DEG) THEN
    ASM_REWRITE_TAC[MLDSA_ZQ] THEN ANTS_TAC THENL
     [ASM_ARITH_TAC; DISCH_THEN(SUBST1_TAC o SYM) THEN REFL_TAC]]);;

let MLDSA_RQ_EQ = prove
 (`!p q. p IN ring_carrier mldsa_rq /\ q IN ring_carrier mldsa_rq
         ==> (p = q <=> !i. i < 256 ==> coeff i p = coeff i q)`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN SIMP_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPEC `p:(1->num)->int` MLDSA_POLY_COEFF) THEN
  MP_TAC(SPEC `q:(1->num)->int` MLDSA_POLY_COEFF) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[mldsa_poly; FUN_EQ_THM] THEN GEN_TAC THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[]);;

let MLDSA_POLY_EQ = prove
 (`!a f. f IN ring_carrier mldsa_rq
         ==> (mldsa_poly a = f <=>
              !i. i < 256 ==> (a i == coeff i f) (mod &8380417))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[MLDSA_RQ_EQ; MLDSA_POLY_IN_RQ] THEN
  SIMP_TAC[COEFF_MLDSA_POLY; GSYM INT_REM_EQ] THEN
  ASM_SIMP_TAC[INT_REM_LT; MLDSA_RQ_COEFF]);;

(* ------------------------------------------------------------------------- *)
(* The ring operations of R_q on coefficients: addition, subtraction and     *)
(* negation are coefficientwise mod q, and multiplication is the negacyclic  *)
(* convolution, since X^256 = -1 in R_q. Also sums, and the products         *)
(* u^T v = sum_{j < n} u[j] * v[j] of mldsa_dot.                             *)
(* ------------------------------------------------------------------------- *)

let MLDSA_RQ_COEFF_ADD = prove
 (`!p q k. p IN ring_carrier mldsa_rq /\ q IN ring_carrier mldsa_rq
           ==> coeff k (ring_add mldsa_rq p q) =
               (coeff k p + coeff k q) rem &8380417`,
  SIMP_TAC[MLDSA_RQ; mldsa_zqx; POLY_RING_CLAUSES; COEFF_POLY_ADD] THEN
  REWRITE_TAC[MLDSA_ZQ]);;

let MLDSA_RQ_COEFF_SUB = prove
 (`!p q k. p IN ring_carrier mldsa_rq /\ q IN ring_carrier mldsa_rq
           ==> coeff k (ring_sub mldsa_rq p q) =
               (coeff k p - coeff k q) rem &8380417`,
  SIMP_TAC[MLDSA_RQ_SUB; mldsa_zqx; POLY_RING_CLAUSES; COEFF_POLY_SUB] THEN
  REWRITE_TAC[MLDSA_ZQ]);;

let MLDSA_RQ_COEFF_NEG = prove
 (`!p k. p IN ring_carrier mldsa_rq
         ==> coeff k (ring_neg mldsa_rq p) = --(coeff k p) rem &8380417`,
  SIMP_TAC[MLDSA_RQ; mldsa_zqx; POLY_RING_CLAUSES; COEFF_POLY_NEG] THEN
  REWRITE_TAC[MLDSA_ZQ]);;

let MLDSA_ZQ_RING_SUM = prove
 (`!(s:K->bool) f.
        FINITE s
        ==> ring_sum mldsa_zq s (\i. f i rem &8380417) =
            isum s f rem &8380417`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mldsa_zq] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) RING_SUM_INTEGER_MOD_RING o
    lhand o snd) THEN
  ASM_REWRITE_TAC[ARITH_EQ; GSYM mldsa_zq; IN_MLDSA_ZQ] THEN
  REWRITE_TAC[INT_REM_POS_EQ; INT_LT_REM_EQ] THEN
  CONV_TAC INT_REDUCE_CONV THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[INT_REM_EQ] THEN MATCH_MP_TAC INT_CONG_ISUM THEN
  ASM_REWRITE_TAC[INT_CONG_LREM; INTEGER_RULE `(x:int == x) (mod n)`]);;

let MLDSA_RQ_COEFF_SUM = prove
 (`!(s:K->bool) f k.
        FINITE s /\ (!i. i IN s ==> f i IN ring_carrier mldsa_rq)
        ==> coeff k (ring_sum mldsa_rq s f) =
            isum s (\i. coeff k (f i)) rem &8380417`,
  REWRITE_TAC[RIGHT_FORALL_IMP_THM; IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[RING_SUM_CLAUSES; ISUM_CLAUSES; FORALL_IN_INSERT] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[MLDSA_RQ; mldsa_zqx; POLY_RING_CLAUSES; COEFF_POLY_0] THEN
    REWRITE_TAC[MLDSA_ZQ; INT_REM_ZERO];
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC[MLDSA_RQ_COEFF_ADD; RING_SUM] THEN
    CONV_TAC INT_REM_DOWN_CONV THEN REFL_TAC]);;

(* Reduction mod X^256 + 1 of a polynomial of degree < 512.                  *)

let MLDSA_RQ_REM_COEFF = prove
 (`!p k. p IN ring_carrier mldsa_zqx /\ poly_deg mldsa_zq p < 512 /\ k < 256
         ==> coeff k (poly_rem mldsa_zq p
                       (ring_add mldsa_zqx (ring_pow mldsa_zqx mldsa_X 256)
                                           (ring_1 mldsa_zqx))) =
             (coeff k p - coeff (k + 256) p) rem &8380417`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `poly_rem mldsa_zq p
     (ring_add mldsa_zqx (ring_pow mldsa_zqx mldsa_X 256)
                         (ring_1 mldsa_zqx)) =
    mldsa_poly (\k. coeff k p - coeff (k + 256) p)`
  SUBST1_TAC THENL
   [ALL_TAC;
    ASM_REWRITE_TAC[COEFF_MLDSA_POLY] THEN CONV_TAC INT_REM_DOWN_CONV THEN
    REFL_TAC] THEN
  MP_TAC MLDSA_RQ_MODULUS THEN
  ABBREV_TAC `m = ring_add mldsa_zqx (ring_pow mldsa_zqx mldsa_X 256)
                                     (ring_1 mldsa_zqx)` THEN
  STRIP_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) POLY_REM_UNIQUE o snd) THEN
  REWRITE_TAC[GSYM mldsa_zqx] THEN
  ASM_REWRITE_TAC[MLDSA_POLY_IN_ZQX; MLDSA_ZQ_UNIT_1] THEN
  DISCH_THEN SUBST1_TAC THEN CONJ_TAC THENL
   [DISJ1_TAC THEN MESON_TAC[MLDSA_POLY_IN_RQ; IN_MLDSA_RQ]; ALL_TAC] THEN
  REWRITE_TAC[ring_divides] THEN
  ASM_SIMP_TAC[RING_SUB; MLDSA_POLY_IN_ZQX] THEN
  EXISTS_TAC `mldsa_poly (\k. coeff (k + 256) p)` THEN
  REWRITE_TAC[MLDSA_POLY_IN_ZQX] THEN EXPAND_TAC "m" THEN
  SIMP_TAC[RING_ADD_RDISTRIB; RING_POW; RING_1; MLDSA_POLY_IN_ZQX;
           RING_MUL_LID; mldsa_X; mldsa_zqx; POLY_VAR_UNIV] THEN
  REWRITE_TAC[FUN_EQ_THM; FORALL_FUN_FROM_1; GSYM COEFF] THEN
  X_GEN_TAC `d:num` THEN
  REWRITE_TAC[POLY_RING_CLAUSES; COEFF_POLY_SUB; COEFF_POLY_ADD] THEN
  SIMP_TAC[COEFF_POLY_VARPOW_MUL; RING_POLYNOMIAL_IMP_POWERSERIES;
           RING_POLYNOMIAL; GSYM mldsa_zqx; MLDSA_POLY_IN_ZQX] THEN
  REWRITE_TAC[COEFF_MLDSA_POLY; MLDSA_ZQ] THEN
  SUBGOAL_THEN `!e. 512 <= e ==> coeff e (p:(1->num)->int) = &0`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`mldsa_zq`; `p:(1->num)->int`; `e:num`]
                  COEFF_ABOVE_DEG) THEN
    ASM_REWRITE_TAC[RING_POLYNOMIAL; GSYM mldsa_zqx; MLDSA_ZQ] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `d < 256` THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC INT_REM_DOWN_CONV THENL
   [AP_THM_TAC THEN AP_TERM_TAC THEN INT_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[SUB_ADD; ARITH_RULE `~(d < 256) ==> 256 <= d`] THEN
  COND_CASES_TAC THEN REWRITE_TAC[INT_SUB_RZERO; INT_ADD_RID] THEN
  CONV_TAC INT_REM_DOWN_CONV THEN REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `d:num`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; SIMP_TAC[]]);;

let MLDSA_RQ_COEFF_MUL = prove
 (`!f g k.
        f IN ring_carrier mldsa_rq /\ g IN ring_carrier mldsa_rq /\ k < 256
        ==> coeff k (ring_mul mldsa_rq f g) =
            (isum (0..k) (\i. coeff i f * coeff (k - i) g) -
             isum (k+1..255) (\i. coeff i f * coeff (k + 256 - i) g))
            rem &8380417`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[MLDSA_RQ] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) MLDSA_RQ_REM_COEFF o lhand o snd) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN_MLDSA_RQ]) THEN
    ASM_SIMP_TAC[RING_MUL] THEN
    REWRITE_TAC[mldsa_zqx; POLY_RING_CLAUSES] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) POLY_DEG_MUL_LE o lhand o snd) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[mldsa_zqx; GSYM RING_POLYNOMIAL]) THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[mldsa_zqx; POLY_RING_CLAUSES; COEFF_POLY_MUL] THEN
  REWRITE_TAC[MLDSA_ZQ] THEN
  SIMP_TAC[MLDSA_ZQ_RING_SUM; FINITE_NUMSEG] THEN
  CONV_TAC INT_REM_DOWN_CONV THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  AP_TERM_TAC THEN TRANS_TAC EQ_TRANS
   `isum (k+1..255) (\i. coeff i f * coeff ((k + 256) - i) g)` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC ISUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC[] THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    ASM_ARITH_TAC] THEN
  MATCH_MP_TAC ISUM_SUPERSET THEN
  REWRITE_TAC[SUBSET; IN_NUMSEG] THEN
  CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  REWRITE_TAC[INT_ENTIRE] THEN
  ASM_CASES_TAC `i <= k` THENL
   [DISJ2_TAC; DISJ1_TAC] THEN
  MATCH_MP_TAC MLDSA_RQ_COEFF_ZERO THEN ASM_REWRITE_TAC[] THEN
  ASM_ARITH_TAC);;

let MLDSA_DOT_IN_RQ = prove
 (`!n u v. mldsa_dot n u v IN ring_carrier mldsa_rq`,
  REWRITE_TAC[mldsa_dot; RING_SUM]);;

let MLDSA_DOT_COEFF = prove
 (`!n u v k.
        (!j. j < n ==> u j IN ring_carrier mldsa_rq /\
                       v j IN ring_carrier mldsa_rq) /\
        k < 256
        ==> coeff k (mldsa_dot n u v) =
            isum {j | j < n}
             (\j. isum (0..k) (\i. coeff i (u j) * coeff (k - i) (v j)) -
                  isum (k+1..255)
                   (\i. coeff i (u j) * coeff (k + 256 - i) (v j)))
            rem &8380417`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mldsa_dot] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) MLDSA_RQ_COEFF_SUM o lhand o snd) THEN
  ASM_SIMP_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM; RING_MUL] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[INT_REM_EQ] THEN
  MATCH_MP_TAC INT_CONG_ISUM THEN
  ASM_SIMP_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM; MLDSA_RQ_COEFF_MUL] THEN
  REWRITE_TAC[INT_CONG_LREM; INTEGER_RULE `(x:int == x) (mod n)`]);;

type_invention_error := false;;
