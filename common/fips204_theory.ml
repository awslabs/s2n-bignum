(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Supporting theory for the ML-DSA specification in common/fips204.ml: the  *)
(* rings Z_q and R_q and their arithmetic on coefficient arrays, the roots   *)
(* zeta^(2 * BitRev8(i) + 1) of X^256 + 1, the NTT as an isomorphism from    *)
(* R_q onto Z_q^256 with pointwise operations, the NTT and its inverse as    *)
(* explicit sums, the bit packings, the NTT-domain forms of FIPS 204         *)
(* Algorithms 6, 7 and 8, the rounding functions, and the equivalence of the *)
(* alternative way of checking the low bits and computing the hints of       *)
(* Section 5.1 of the Round 3 Dilithium specification. The generic lemmas of *)
(* common/fips203_theory.ml (POLY_MOD_RING_ISOMORPHIC_QUOTIENT,              *)
(* POLY_ROOTS_IMP_ZERO, ...) are used as they are.                           *)
(* ========================================================================= *)

needs "common/fips204.ml";;

(* common/fips203_theory.ml uses Library/isum.ml without loading it.         *)

needs "Library/isum.ml";;
needs "common/fips203_theory.ml";;

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

(* ------------------------------------------------------------------------- *)
(* zeta = 1753 has order 512 mod q and BitRev8 is a bijection of [0,256), so *)
(* the 256 values zeta^(2 * BitRev8(i) + 1) are distinct. They are roots of  *)
(* X^256 + 1, since zeta^256 = -1.                                           *)
(* ------------------------------------------------------------------------- *)

let BITREVERSE8_BOUND = prove
 (`!i. bitreverse8 i < 256`,
  GEN_TAC THEN REWRITE_TAC[bitreverse8] THEN
  MP_TAC(ISPEC `word_reversefields 1 (word i:8 word)` VAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_CONV `dimindex(:8)`] THEN ARITH_TAC);;

let BITREVERSE8_BITREVERSE8 = prove
 (`!i. i < 256 ==> bitreverse8(bitreverse8 i) = i`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[bitreverse8; WORD_VAL] THEN
  REWRITE_TAC[WORD_REVERSEFIELDS_REVERSEFIELDS; VAL_WORD] THEN
  REWRITE_TAC[DIMINDEX_CONV `dimindex(:8)`] THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE `i < 256 ==> i < 2 EXP 8`]);;

let BITREVERSE8_INJ = prove
 (`!i j. i < 256 /\ j < 256 /\ bitreverse8 i = bitreverse8 j ==> i = j`,
  MESON_TAC[BITREVERSE8_BITREVERSE8]);;

let MLDSA_ZETA_ORDER = prove
 (`order 8380417 1753 = 512`,
  MP_TAC(SPECL [`8380417`; `1753`; `512`] ORDER_DIVIDES) THEN
  MP_TAC(SPECL [`8380417`; `1753`; `256`] ORDER_DIVIDES) THEN
  REWRITE_TAC[CONG] THEN CONV_TAC(ONCE_DEPTH_CONV EXP_MOD_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN
  REWRITE_TAC[ARITH_RULE `512 = 2 EXP 9`; ARITH_RULE `256 = 2 EXP 8`] THEN
  SIMP_TAC[DIVIDES_PRIMEPOW; PRIME_2] THEN
  DISCH_TAC THEN DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o REWRITE_RULE[NOT_EXISTS_THM]) THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let MLDSA_ZETA_EXP_INJ = prove
 (`!a b. a < 512 /\ b < 512 /\ (1753 EXP a == 1753 EXP b) (mod 8380417)
         ==> a = b`,
  let lemma = prove
   (`!a b. a <= b /\ b < 512 /\ (1753 EXP a == 1753 EXP b) (mod 8380417)
           ==> a = b`,
    REPEAT STRIP_TAC THEN
    UNDISCH_TAC `(1753 EXP a == 1753 EXP b) (mod 8380417)` THEN
    SUBGOAL_THEN `1753 EXP b = 1753 EXP a * 1753 EXP (b - a)` SUBST1_TAC THENL
     [REWRITE_TAC[GSYM EXP_ADD] THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `coprime(1753 EXP a,8380417)` MP_TAC THENL
     [ONCE_REWRITE_TAC[COPRIME_SYM] THEN MATCH_MP_TAC COPRIME_EXP THEN
      CONV_TAC COPRIME_CONV;
      ALL_TAC] THEN
    REWRITE_TAC[IMP_IMP] THEN
    DISCH_THEN(MP_TAC o MATCH_MP (NUMBER_RULE
     `!a x n. coprime(a,n) /\ (a == a * x) (mod n) ==> (x == 1) (mod n)`)) THEN
    REWRITE_TAC[ORDER_DIVIDES; MLDSA_ZETA_ORDER] THEN
    DISCH_THEN(MP_TAC o MATCH_MP DIVIDES_LE) THEN ASM_ARITH_TAC) in
  REPEAT STRIP_TAC THEN
  DISJ_CASES_TAC(ARITH_RULE `a:num <= b \/ b <= a`) THEN
  ASM_MESON_TAC[lemma; CONG_SYM]);;

let MLDSA_ROOT_IN_ZQ = prove
 (`!i. ring_pow mldsa_zq (&1753) (2 * bitreverse8 i + 1)
       IN ring_carrier mldsa_zq`,
  GEN_TAC THEN MATCH_MP_TAC RING_POW THEN
  REWRITE_TAC[IN_MLDSA_ZQ] THEN INT_ARITH_TAC);;

let MLDSA_ROOT_INJ = prove
 (`!i j. i < 256 /\ j < 256 /\
         ring_pow mldsa_zq (&1753) (2 * bitreverse8 i + 1) =
         ring_pow mldsa_zq (&1753) (2 * bitreverse8 j + 1)
         ==> i = j`,
  REWRITE_TAC[MLDSA_ZQ; INT_OF_NUM_POW; INT_OF_NUM_REM; INT_OF_NUM_EQ] THEN
  REWRITE_TAC[GSYM CONG] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC BITREVERSE8_INJ THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(ARITH_RULE `2 * x + 1 = 2 * y + 1 ==> x = y`) THEN
  MATCH_MP_TAC MLDSA_ZETA_EXP_INJ THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPEC `i:num` BITREVERSE8_BOUND) THEN
  MP_TAC(SPEC `j:num` BITREVERSE8_BOUND) THEN ARITH_TAC);;

let MLDSA_ROOT_POW_256 = prove
 (`!i. ring_pow mldsa_zq
        (ring_pow mldsa_zq (&1753) (2 * bitreverse8 i + 1)) 256 =
       ring_neg mldsa_zq (ring_1 mldsa_zq)`,
  GEN_TAC THEN REWRITE_TAC[MLDSA_ZQ] THEN CONV_TAC INT_REDUCE_CONV THEN
  REWRITE_TAC[INT_POW_REM; INT_POW_POW] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `(2 * n + 1) * 256 = 256 * (2 * n + 1)`] THEN
  REWRITE_TAC[GSYM INT_POW_POW] THEN
  ONCE_REWRITE_TAC[GSYM INT_POW_REM] THEN
  CONV_TAC(LAND_CONV(LAND_CONV(LAND_CONV INT_REDUCE_CONV))) THEN
  SUBGOAL_THEN `&8380416:int = --(&1) rem &8380417` SUBST1_TAC THENL
   [CONV_TAC INT_REDUCE_CONV; ALL_TAC] THEN
  REWRITE_TAC[INT_POW_REM; INT_POW_NEG; INT_POW_ONE] THEN
  REWRITE_TAC[EVEN_ADD; EVEN_MULT; ARITH]);;

let MLDSA_ROOT_MODULUS = prove
 (`!i. poly_eval mldsa_zq
        (ring_add mldsa_zqx (ring_pow mldsa_zqx mldsa_X 256) (ring_1 mldsa_zqx))
        (ring_pow mldsa_zq (&1753) (2 * bitreverse8 i + 1)) =
       ring_0 mldsa_zq`,
  GEN_TAC THEN REWRITE_TAC[mldsa_zqx; mldsa_X; POLY_RING_CLAUSES] THEN
  SIMP_TAC[POLY_EVAL_ADD; POLY_EVAL_POW; POLY_EVAL_VAR; POLY_EVAL_1;
           RING_POLYNOMIAL_POW; RING_POLYNOMIAL_VAR; RING_POLYNOMIAL_1;
           MLDSA_ROOT_IN_ZQ; MLDSA_ROOT_POW_256] THEN
  MATCH_MP_TAC RING_ADD_LNEG THEN REWRITE_TAC[RING_1]);;

(* ------------------------------------------------------------------------- *)
(* The NTT of FIPS 204 equation (2.1) as an explicit sum over the            *)
(* coefficients, and as a bijection from R_q onto the arrays of 256 elements *)
(* of Z_q, since a nonzero polynomial of degree < 256 has fewer than 256     *)
(* roots. So mldsa_ntt_inv really is its inverse.                            *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NTT_IN_ZQ = prove
 (`!f k. mldsa_ntt f k IN ring_carrier mldsa_zq`,
  REWRITE_TAC[mldsa_ntt; POLY_EVAL]);;

let MLDSA_NTT_BOUND = prove
 (`!f k. &0 <= mldsa_ntt f k /\ mldsa_ntt f k < &8380417`,
  REWRITE_TAC[GSYM IN_MLDSA_ZQ; MLDSA_NTT_IN_ZQ]);;

let MLDSA_NTT_EXPLICIT = prove
 (`!f k. f IN ring_carrier mldsa_rq
         ==> mldsa_ntt f k =
             ring_sum mldsa_zq {j | j < 256}
              (\j. ring_mul mldsa_zq (coeff j f)
                     (ring_pow mldsa_zq
                        (ring_pow mldsa_zq (&1753) (2 * bitreverse8 k + 1))
                        j))`,
  REWRITE_TAC[IN_MLDSA_RQ] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[mldsa_ntt] THEN
  MP_TAC(SPEC `k:num` MLDSA_ROOT_IN_ZQ) THEN
  SPEC_TAC(`ring_pow mldsa_zq (&1753) (2 * bitreverse8 k + 1)`,`x:int`) THEN
  REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[mldsa_zqx]) THEN
  ASM_SIMP_TAC[POLY_EVAL_EXPAND] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC RING_SUM_SUPERSET THEN
  REWRITE_TAC[SUBSET; IN_NUMSEG; IN_ELIM_THM] THEN
  CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`mldsa_zq`; `f:(1->num)->int`; `j:num`] COEFF_ABOVE_DEG) THEN
  ASM_SIMP_TAC[RING_POLYNOMIAL] THEN ANTS_TAC THENL
   [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC RING_MUL_LZERO THEN ASM_SIMP_TAC[RING_POW]);;

let MLDSA_NTT_INJ = prove
 (`!f g. f IN ring_carrier mldsa_rq /\ g IN ring_carrier mldsa_rq /\
         (!k. k < 256 ==> mldsa_ntt f k = mldsa_ntt g k)
         ==> f = g`,
  REWRITE_TAC[IN_MLDSA_RQ; mldsa_zqx] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`poly_ring mldsa_zq (:1)`; `f:(1->num)->int`;
                 `g:(1->num)->int`] RING_SUB_EQ_0) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC POLY_ROOTS_IMP_ZERO THEN
  MAP_EVERY EXISTS_TAC
   [`256`; `\i. ring_pow mldsa_zq (&1753) (2 * bitreverse8 i + 1)`] THEN
  REWRITE_TAC[MLDSA_ROOT_INJ; MLDSA_ROOT_IN_ZQ] THEN
  REWRITE_TAC[MATCH_MP FIELD_IMP_INTEGRAL_DOMAIN (CONJUNCT1 MLDSA_ZQ)] THEN
  ASM_SIMP_TAC[RING_SUB] THEN CONJ_TAC THENL
   [REWRITE_TAC[POLY_RING_CLAUSES] THEN
    MP_TAC(ISPECL [`mldsa_zq`; `f:(1->num)->int`; `g:(1->num)->int`]
                  POLY_DEG_SUB_LE) THEN
    ASM_REWRITE_TAC[RING_POLYNOMIAL] THEN ASM_ARITH_TAC;
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    REWRITE_TAC[POLY_RING_CLAUSES] THEN
    ASM_SIMP_TAC[POLY_EVAL_SUB; RING_POLYNOMIAL] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) RING_SUB_EQ_0 o snd) THEN
    REWRITE_TAC[POLY_EVAL] THEN DISCH_THEN SUBST1_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[mldsa_ntt]) THEN ASM_SIMP_TAC[]]);;

let MLDSA_NTT_SURJ = prove
 (`!a. (!k. k < 256 ==> &0 <= a k /\ a k < &8380417)
       ==> ?f. f IN ring_carrier mldsa_rq /\
               !k. k < 256 ==> mldsa_ntt f k = a k`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `t = {a:num->int | (!k. k IN {k | k < 256}
                                     ==> a k IN ring_carrier mldsa_zq) /\
                                (!k. ~(k IN {k | k < 256}) ==> a k = &0)}` THEN
  SUBGOAL_THEN `FINITE(t:(num->int)->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "t" THEN MATCH_MP_TAC FINITE_FUNSPACE THEN
    REWRITE_TAC[FINITE_NUMSEG_LT; mldsa_zq; FINITE_INTEGER_MOD_RING; ARITH_EQ];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ring_carrier mldsa_rq = IMAGE mldsa_poly t /\
    (!x y. x IN t /\ y IN t /\ mldsa_poly x = mldsa_poly y ==> x = y)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_IMAGE] THEN X_GEN_TAC `p:(1->num)->int` THEN
      EQ_TAC THENL
       [DISCH_TAC THEN
        EXISTS_TAC `\k. if k < 256 then coeff k (p:(1->num)->int) else &0` THEN
        CONJ_TAC THENL
         [FIRST_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV
           [SYM(MATCH_MP MLDSA_POLY_COEFF th)]) THEN
          REWRITE_TAC[mldsa_poly; FUN_EQ_THM] THEN GEN_TAC THEN
          COND_CASES_TAC THEN ASM_REWRITE_TAC[];
          EXPAND_TAC "t" THEN REWRITE_TAC[IN_ELIM_THM; IN_MLDSA_ZQ] THEN
          ASM_SIMP_TAC[MLDSA_RQ_COEFF]];
        STRIP_TAC THEN ASM_REWRITE_TAC[MLDSA_POLY_IN_RQ]];
      EXPAND_TAC "t" THEN REWRITE_TAC[IN_ELIM_THM; IN_MLDSA_ZQ] THEN
      REPEAT STRIP_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `k:num` THEN
      ASM_CASES_TAC `k < 256` THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
      FIRST_X_ASSUM(MP_TAC o AP_TERM `coeff (k:num):((1->num)->int)->int`) THEN
      ASM_REWRITE_TAC[COEFF_MLDSA_POLY] THEN
      ASM_SIMP_TAC[INT_REM_LT]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (\f k. if k < 256 then mldsa_ntt f k else &0)
          (ring_carrier mldsa_rq) = t`
  MP_TAC THENL
   [MATCH_MP_TAC CARD_SUBSET_EQ THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN EXPAND_TAC "t" THEN
      REWRITE_TAC[IN_ELIM_THM] THEN
      X_GEN_TAC `x:num->int` THEN DISCH_TAC THEN SIMP_TAC[] THEN
      REWRITE_TAC[MLDSA_NTT_IN_ZQ];
      ALL_TAC] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) CARD_IMAGE_INJ o lhand o snd) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [MAP_EVERY X_GEN_TAC [`p:(1->num)->int`; `q:(1->num)->int`] THEN
        STRIP_TAC THEN MATCH_MP_TAC MLDSA_NTT_INJ THEN
        ASM_REWRITE_TAC[] THEN
        X_GEN_TAC `k:num` THEN DISCH_TAC THEN
        FIRST_X_ASSUM(MP_TAC o C AP_THM `k:num` o
          check (fun th -> is_eq(concl th) && not(is_var(lhs(concl th))))) THEN
        ASM_REWRITE_TAC[];
        ASM_SIMP_TAC[FINITE_IMAGE]];
      DISCH_THEN SUBST1_TAC] THEN
    MATCH_MP_TAC CARD_IMAGE_INJ THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE] THEN
  DISCH_THEN(MP_TAC o SPEC `\k. if k < 256 then (a:num->int) k else &0`) THEN
  MATCH_MP_TAC(TAUT `q /\ (p ==> r) ==> (p <=> q) ==> r`) THEN CONJ_TAC THENL
   [EXPAND_TAC "t" THEN REWRITE_TAC[IN_ELIM_THM; IN_MLDSA_ZQ] THEN
    ASM_SIMP_TAC[];
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `p:(1->num)->int` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `k:num` THEN
    DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o C AP_THM `k:num`) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[EQ_SYM_EQ]]);;

let MLDSA_NTT_INV = prove
 (`!a. (!k. k < 256 ==> &0 <= a k /\ a k < &8380417)
       ==> mldsa_ntt_inv a IN ring_carrier mldsa_rq /\
           !k. k < 256 ==> mldsa_ntt (mldsa_ntt_inv a) k = a k`,
  GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP MLDSA_NTT_SURJ) THEN
  REWRITE_TAC[mldsa_ntt_inv] THEN CONV_TAC(ONCE_DEPTH_CONV SELECT_CONV) THEN
  REWRITE_TAC[]);;

let MLDSA_NTT_INV_NTT = prove
 (`!f. f IN ring_carrier mldsa_rq ==> mldsa_ntt_inv (mldsa_ntt f) = f`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MLDSA_NTT_INJ THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MLDSA_NTT_INV THEN
  REWRITE_TAC[MLDSA_NTT_BOUND]);;

let MLDSA_NTT_INV_EQ = prove
 (`!a b. (!i. i < 256 ==> a i = b i) ==> mldsa_ntt_inv a = mldsa_ntt_inv b`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mldsa_ntt_inv] THEN
  AP_TERM_TAC THEN ABS_TAC THEN ASM_MESON_TAC[]);;

let MLDSA_NTT_INV_UNIQUE = prove
 (`!f a. f IN ring_carrier mldsa_rq /\ (!k. k < 256 ==> mldsa_ntt f k = a k)
         ==> mldsa_ntt_inv a = f`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV
   [GSYM(MATCH_MP MLDSA_NTT_INV_NTT th)]) THEN
  MATCH_MP_TAC MLDSA_NTT_INV_EQ THEN ASM_SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The NTT is a ring homomorphism from R_q to T_q = Z_q^256 with pointwise   *)
(* operations, since evaluation at a root of X^256 + 1 is one. So the        *)
(* pointwise products of FIPS 204 equation (2.2) and Algorithm 45            *)
(* (MultiplyNTT), and the sums of products of Algorithm 48                   *)
(* (MatrixVectorNTT), followed by NTT^-1, give the products in R_q.          *)
(* ------------------------------------------------------------------------- *)

let POLY_EVAL_REM_ROOT = prove
 (`!(r:A ring) p m x.
        p IN ring_carrier(poly_ring r (:1)) /\
        m IN ring_carrier(poly_ring r (:1)) /\
        x IN ring_carrier r /\ poly_eval r m x = ring_0 r
        ==> poly_eval r (poly_rem r p m) x = poly_eval r p x`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`r:A ring`; `p:(1->num)->A`; `m:(1->num)->A`]
                POLY_REM_DIVIDES_SUB) THEN
  ASM_REWRITE_TAC[ring_divides] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:(1->num)->A` STRIP_ASSUME_TAC o
             last o CONJUNCTS) THEN
  FIRST_X_ASSUM(MP_TAC o AP_TERM `\q. poly_eval (r:A ring) q x`) THEN
  MP_TAC(ISPECL [`r:A ring`; `p:(1->num)->A`; `m:(1->num)->A`] POLY_REM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM RING_POLYNOMIAL]) THEN
  ASM_SIMP_TAC[POLY_RING_CLAUSES; POLY_EVAL_SUB; POLY_EVAL_MUL;
               RING_MUL_LZERO; POLY_EVAL; RING_SUB_EQ_0] THEN
  SIMP_TAC[EQ_SYM_EQ]);;

let MLDSA_NTT_ADD = prove
 (`!f g k. f IN ring_carrier mldsa_rq /\ g IN ring_carrier mldsa_rq
           ==> mldsa_ntt (ring_add mldsa_rq f g) k =
               ring_add mldsa_zq (mldsa_ntt f k) (mldsa_ntt g k)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[MLDSA_RQ; mldsa_ntt] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IN_MLDSA_RQ; mldsa_zqx;
                              GSYM RING_POLYNOMIAL]) THEN
  ASM_SIMP_TAC[mldsa_zqx; POLY_RING_CLAUSES; POLY_EVAL_ADD]);;

let MLDSA_NTT_SUB = prove
 (`!f g k. f IN ring_carrier mldsa_rq /\ g IN ring_carrier mldsa_rq
           ==> mldsa_ntt (ring_sub mldsa_rq f g) k =
               ring_sub mldsa_zq (mldsa_ntt f k) (mldsa_ntt g k)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[MLDSA_RQ_SUB; mldsa_ntt] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IN_MLDSA_RQ; mldsa_zqx;
                              GSYM RING_POLYNOMIAL]) THEN
  ASM_SIMP_TAC[mldsa_zqx; POLY_RING_CLAUSES; POLY_EVAL_SUB]);;

let MLDSA_NTT_NEG = prove
 (`!f k. f IN ring_carrier mldsa_rq
         ==> mldsa_ntt (ring_neg mldsa_rq f) k =
             ring_neg mldsa_zq (mldsa_ntt f k)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[MLDSA_RQ; mldsa_ntt] THEN
  MP_TAC(ISPECL [`mldsa_zq`; `(:1)`;
                 `ring_pow mldsa_zq (&1753) (2 * bitreverse8 k + 1)`]
                RING_HOMOMORPHISM_POLY_EVAL) THEN
  REWRITE_TAC[MLDSA_ROOT_IN_ZQ; GSYM mldsa_zqx] THEN
  DISCH_THEN(MP_TAC o BETA_RULE o MATCH_MP RING_HOMOMORPHISM_NEG) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IN_MLDSA_RQ]) THEN ASM_SIMP_TAC[]);;

let MLDSA_NTT_MUL = prove
 (`!f g k. f IN ring_carrier mldsa_rq /\ g IN ring_carrier mldsa_rq
           ==> mldsa_ntt (ring_mul mldsa_rq f g) k =
               ring_mul mldsa_zq (mldsa_ntt f k) (mldsa_ntt g k)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[MLDSA_RQ; mldsa_ntt] THEN
  MP_TAC MLDSA_RQ_MODULUS THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IN_MLDSA_RQ]) THEN
  W(MP_TAC o PART_MATCH (lhand o rand) POLY_EVAL_REM_ROOT o lhand o snd) THEN
  REWRITE_TAC[GSYM mldsa_zqx] THEN
  ASM_SIMP_TAC[RING_MUL; MLDSA_ROOT_IN_ZQ; MLDSA_ROOT_MODULUS] THEN
  DISCH_THEN SUBST1_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[mldsa_zqx; GSYM RING_POLYNOMIAL]) THEN
  ASM_SIMP_TAC[mldsa_zqx; POLY_RING_CLAUSES; POLY_EVAL_MUL; MLDSA_ROOT_IN_ZQ]);;

let MLDSA_NTT_0 = prove
 (`!k. mldsa_ntt (ring_0 mldsa_rq) k = ring_0 mldsa_zq`,
  REWRITE_TAC[MLDSA_RQ; mldsa_ntt; mldsa_zqx; POLY_RING_CLAUSES; POLY_EVAL_0]);;

let MLDSA_NTT_1 = prove
 (`!k. mldsa_ntt (ring_1 mldsa_rq) k = ring_1 mldsa_zq`,
  REWRITE_TAC[MLDSA_RQ; mldsa_ntt; mldsa_zqx; POLY_RING_CLAUSES; POLY_EVAL_1]);;

let MLDSA_NTT_SUM = prove
 (`!(s:K->bool) f k.
        FINITE s /\ (!j. j IN s ==> f j IN ring_carrier mldsa_rq)
        ==> mldsa_ntt (ring_sum mldsa_rq s f) k =
            ring_sum mldsa_zq s (\j. mldsa_ntt (f j) k)`,
  REWRITE_TAC[RIGHT_FORALL_IMP_THM; IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[RING_SUM_CLAUSES; MLDSA_NTT_0; FORALL_IN_INSERT] THEN
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[MLDSA_NTT_ADD; RING_SUM; MLDSA_NTT_IN_ZQ]);;

let MLDSA_NTT_DOT = prove
 (`!n u v k.
        (!j. j < n ==> u j IN ring_carrier mldsa_rq /\
                       v j IN ring_carrier mldsa_rq)
        ==> mldsa_ntt (mldsa_dot n u v) k =
            ring_sum mldsa_zq {j | j < n}
             (\j. ring_mul mldsa_zq (mldsa_ntt (u j) k) (mldsa_ntt (v j) k))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mldsa_dot] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) MLDSA_NTT_SUM o lhand o snd) THEN
  ASM_SIMP_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM; RING_MUL] THEN
  DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC RING_SUM_EQ THEN
  ASM_SIMP_TAC[IN_ELIM_THM; MLDSA_NTT_MUL]);;

let MLDSA_NTT_INV_MUL = prove
 (`!f g. f IN ring_carrier mldsa_rq /\ g IN ring_carrier mldsa_rq
         ==> mldsa_ntt_inv
              (\k. ring_mul mldsa_zq (mldsa_ntt f k) (mldsa_ntt g k)) =
             ring_mul mldsa_rq f g`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MLDSA_NTT_INV_UNIQUE THEN
  ASM_SIMP_TAC[RING_MUL; MLDSA_NTT_MUL]);;

let MLDSA_NTT_INV_SUB = prove
 (`!a b. (!k. k < 256 ==> a k IN ring_carrier mldsa_zq /\
                          b k IN ring_carrier mldsa_zq)
         ==> ring_sub mldsa_rq (mldsa_ntt_inv a) (mldsa_ntt_inv b) =
             mldsa_ntt_inv (\k. ring_sub mldsa_zq (a k) (b k))`,
  REWRITE_TAC[IN_MLDSA_ZQ] THEN REPEAT STRIP_TAC THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC MLDSA_NTT_INV_UNIQUE THEN
  ASM_SIMP_TAC[RING_SUB; MLDSA_NTT_INV; MLDSA_NTT_SUB]);;

let MLDSA_DOT_NTT_INV = prove
 (`!n a v.
        (!j k. j < n /\ k < 256 ==> &0 <= a j k /\ a j k < &8380417) /\
        (!j. j < n ==> v j IN ring_carrier mldsa_rq)
        ==> mldsa_dot n (\j. mldsa_ntt_inv (a j)) v =
            mldsa_ntt_inv
             (\k. ring_sum mldsa_zq {j | j < n}
                   (\j. ring_mul mldsa_zq (a j k) (mldsa_ntt (v j) k)))`,
  REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC MLDSA_NTT_INV_UNIQUE THEN REWRITE_TAC[MLDSA_DOT_IN_RQ] THEN
  X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) MLDSA_NTT_DOT o lhand o snd) THEN
  ASM_SIMP_TAC[MLDSA_NTT_INV] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC RING_SUM_EQ THEN ASM_SIMP_TAC[IN_ELIM_THM; MLDSA_NTT_INV]);;

(* ------------------------------------------------------------------------- *)
(* The NTT and its inverse as single sums of integers mod q; 731434 is 1 /   *)
(* 1753 and 8347681 is 1 / 256 mod q. The right-hand sides of                *)
(* MLDSA_NTT_MLDSA_POLY and MLDSA_NTT_INV_TOMONT are the definitions of      *)
(* arm_mldsa_forward_ntt a k and arm_mldsa_inverse_ntt a k in                *)
(* common/mlkem_mldsa.ml, the specifications of the AArch64 NTT code. The    *)
(* latter includes the Montgomery factor 2^32, which turns 1 / 256 into      *)
(* 2^24.                                                                     *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NTT_FORWARD = prove
 (`!f k. f IN ring_carrier mldsa_rq
         ==> mldsa_ntt f k =
             isum (0..255)
              (\j. coeff j f * &1753 pow ((2 * bitreverse8 k + 1) * j))
             rem &8380417`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[MLDSA_NTT_EXPLICIT] THEN
  REWRITE_TAC[MLDSA_ZQ] THEN
  SUBGOAL_THEN `{j:num | j < 256} = 0..255` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_NUMSEG] THEN ARITH_TAC;
    SIMP_TAC[MLDSA_ZQ_RING_SUM; FINITE_NUMSEG]] THEN
  REWRITE_TAC[INT_REM_EQ] THEN MATCH_MP_TAC INT_CONG_ISUM THEN
  REWRITE_TAC[FINITE_NUMSEG] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM INT_POW_POW] THEN
  MATCH_MP_TAC(INTEGER_RULE
   `(y:int == z) (mod n) ==> (x * y == x * z) (mod n)`) THEN
  REWRITE_TAC[INT_CONG_LREM] THEN MATCH_MP_TAC INT_CONG_POW THEN
  REWRITE_TAC[INT_CONG_LREM; INTEGER_RULE `(x:int == x) (mod n)`]);;

let MLDSA_NTT_MLDSA_POLY = prove
 (`!a k. mldsa_ntt (mldsa_poly a) k =
         isum (0..255) (\j. a j * &1753 pow ((2 * bitreverse8 k + 1) * j))
         rem &8380417`,
  REPEAT GEN_TAC THEN SIMP_TAC[MLDSA_NTT_FORWARD; MLDSA_POLY_IN_RQ] THEN
  REWRITE_TAC[COEFF_MLDSA_POLY; INT_REM_EQ] THEN
  MATCH_MP_TAC INT_CONG_ISUM THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[ARITH_RULE `j <= 255 ==> j < 256`] THEN
  MATCH_MP_TAC(INTEGER_RULE
   `(x:int == y) (mod n) ==> (x * z == y * z) (mod n)`) THEN
  REWRITE_TAC[INT_CONG_LREM; INTEGER_RULE `(x:int == x) (mod n)`]);;

(* The sums over j of (zeta^(2 * r + 1) / zeta^(2 * m + 1))^j.               *)

let MLDSA_ZETA_ORTHOGONAL = prove
 (`!r m. r < 256 /\ m < 256
         ==> (isum (0..255)
               (\j. (&731434 pow (2 * m + 1) * &1753 pow (2 * r + 1)) pow j) ==
              if m = r then &256 else &0) (mod &8380417)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `y:int = &731434 pow (2 * m + 1) * &1753 pow (2 * r + 1)` THEN
  SUBGOAL_THEN `!n. ((&1753 * &731434:int) pow n == &1) (mod &8380417)`
  ASSUME_TAC THENL
   [GEN_TAC THEN MP_TAC(ISPECL [`&1753 * &731434:int`; `&1:int`;
                                `&8380417:int`] INT_CONG_POW) THEN
    REWRITE_TAC[INT_POW_ONE] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[GSYM INT_REM_EQ] THEN CONV_TAC INT_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(&1753 pow (2 * m + 1) * y:int == &1753 pow (2 * r + 1)) (mod &8380417)`
  ASSUME_TAC THENL
   [EXPAND_TAC "y" THEN REWRITE_TAC[INT_MUL_ASSOC; GSYM INT_POW_MUL] THEN
    MATCH_MP_TAC(INTEGER_RULE
     `!a b n:int. (a == &1) (mod n) ==> (a * b == b) (mod n)`) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `((y:int) pow 256 == &1) (mod &8380417)` ASSUME_TAC THENL
   [EXPAND_TAC "y" THEN REWRITE_TAC[INT_POW_MUL] THEN
    ONCE_REWRITE_TAC[INT_POW_POW_SWAP] THEN
    MATCH_MP_TAC(INTEGER_RULE
     `!a b n:int. (a == -- &1) (mod n) /\ (b == -- &1) (mod n)
                  ==> (a * b == &1) (mod n)`) THEN
    CONJ_TAC THENL
     [MP_TAC(SPEC `2 * m + 1` (MATCH_MP INT_CONG_POW
       (prove(`(&731434 pow 256 == -- &1:int) (mod &8380417)`,
              REWRITE_TAC[GSYM INT_REM_EQ] THEN CONV_TAC INT_REDUCE_CONV))));
      MP_TAC(SPEC `2 * r + 1` (MATCH_MP INT_CONG_POW
       (prove(`(&1753 pow 256 == -- &1:int) (mod &8380417)`,
              REWRITE_TAC[GSYM INT_REM_EQ] THEN CONV_TAC INT_REDUCE_CONV))))]
    THEN REWRITE_TAC[INT_POW_NEG; EVEN_ADD; EVEN_MULT; ARITH; INT_POW_ONE];
    ALL_TAC] THEN
  COND_CASES_TAC THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    SUBGOAL_THEN `(y:int == &1) (mod &8380417)` ASSUME_TAC THENL
     [EXPAND_TAC "y" THEN REWRITE_TAC[GSYM INT_POW_MUL] THEN
      ONCE_REWRITE_TAC[INT_MUL_SYM] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC(INTEGER_RULE
     `!z. (x:int == z) (mod n) /\ (z == y) (mod n) ==> (x == y) (mod n)`) THEN
    EXISTS_TAC `isum (0..255) (\j. &1)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC INT_CONG_ISUM THEN REWRITE_TAC[FINITE_NUMSEG] THEN
      X_GEN_TAC `j:num` THEN DISCH_TAC THEN
      UNDISCH_TAC `(y:int == &1) (mod &8380417)` THEN
      DISCH_THEN(MP_TAC o SPEC `j:num` o MATCH_MP INT_CONG_POW) THEN
      REWRITE_TAC[INT_POW_ONE];
      REWRITE_TAC[ISUM_CONST_NUMSEG] THEN
      CONV_TAC(NUM_REDUCE_CONV THENC INT_REDUCE_CONV) THEN
      REWRITE_TAC[INTEGER_RULE `(x:int == x) (mod n)`]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((y:int == &1) (mod &8380417))` ASSUME_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `(1753 EXP (2 * m + 1) == 1753 EXP (2 * r + 1)) (mod 8380417)`
    MP_TAC THENL
     [REWRITE_TAC[num_congruent; GSYM INT_OF_NUM_POW] THEN
      MATCH_MP_TAC(INTEGER_RULE
       `!a b y n:int. (a * y == b) (mod n) /\ (y == &1) (mod n)
                      ==> (a == b) (mod n)`) THEN
      EXISTS_TAC `y:int` THEN ASM_REWRITE_TAC[];
      DISCH_TAC THEN
      MP_TAC(SPECL [`2 * m + 1`; `2 * r + 1`] MLDSA_ZETA_EXP_INJ) THEN
      ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(SPECL [`y:int`; `255`] INT_GEOM_SERIES) THEN
  REWRITE_TAC[ARITH_RULE `SUC 255 = 256`] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `&8380417 divides ((y - &1) * isum (0..255) (\j. (y:int) pow j))`
  MP_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(INTEGER_RULE
     `!x n:int. (x == &1) (mod n) ==> n divides (x - &1)`) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SIMP_TAC[PRIME_INT_DIVPROD_EQ; PRIME_8380417] THEN
  ASM_REWRITE_TAC[INTEGER_RULE
   `!x n:int. n divides (x - &1) <=> (x == &1) (mod n)`] THEN
  REWRITE_TAC[INTEGER_RULE `!s n:int. n divides s ==> (s == &0) (mod n)`]);;

let MLDSA_NTT_INV_EXPLICIT = prove
 (`!a. (!i. i < 256 ==> &0 <= a i /\ a i < &8380417)
       ==> mldsa_ntt_inv a =
           mldsa_poly
            (\k. &8347681 *
                 isum (0..255)
                  (\j. a(bitreverse8 j) * &731434 pow ((2 * j + 1) * k)))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MLDSA_NTT_INV_UNIQUE THEN
  REWRITE_TAC[MLDSA_POLY_IN_RQ] THEN
  X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  REWRITE_TAC[MLDSA_NTT_MLDSA_POLY] THEN
  SUBGOAL_THEN `(a:num->int) k = a k rem &8380417` SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC INT_REM_LT THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[INT_REM_EQ] THEN ABBREV_TAC `r = bitreverse8 k` THEN
  REWRITE_TAC[GSYM ISUM_LMUL; GSYM ISUM_RMUL] THEN
  GEN_REWRITE_TAC ONCE_DEPTH_CONV [ISUM_SWAP_NUMSEG] THEN BETA_TAC THEN
  MATCH_MP_TAC(INTEGER_RULE
   `!y. (x:int == y) (mod n) /\ (y == z) (mod n) ==> (x == z) (mod n)`) THEN
  EXISTS_TAC
   `isum (0..255) (\m. &8347681 * a(bitreverse8 m) *
                       (if m = r then &256 else &0))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC INT_CONG_ISUM THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `m:num` THEN STRIP_TAC THEN
    REWRITE_TAC[INT_ARITH
     `(c * x * y) * z:int = c * x * (y * z)`] THEN
    REWRITE_TAC[ISUM_LMUL] THEN
    REPEAT(MATCH_MP_TAC(INTEGER_RULE
     `(x:int == y) (mod n) ==> (c * x == c * y) (mod n)`)) THEN
    REWRITE_TAC[GSYM INT_POW_POW; GSYM INT_POW_MUL] THEN
    MATCH_MP_TAC MLDSA_ZETA_ORTHOGONAL THEN
    EXPAND_TAC "r" THEN REWRITE_TAC[BITREVERSE8_BOUND] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `isum (0..255)
     (\m. &8347681 * a(bitreverse8 m) * (if m = r then &256 else &0)) =
    isum (0..255)
     (\m. if m = r then &8347681 * a(bitreverse8 r) * &256 else &0)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC ISUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[INT_MUL_RZERO];
    ALL_TAC] THEN
  REWRITE_TAC[ISUM_DELTA; IN_NUMSEG; LE_0] THEN
  SUBGOAL_THEN `r <= 255 /\ bitreverse8 r = k` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "r" THEN
    ASM_SIMP_TAC[BITREVERSE8_BITREVERSE8; BITREVERSE8_BOUND;
                 ARITH_RULE `x < 256 ==> x <= 255`];
    ASM_REWRITE_TAC[]] THEN
  MATCH_MP_TAC(INTEGER_RULE
   `(c * d == &1) (mod n) ==> (c * x * d == x:int) (mod n)`) THEN
  REWRITE_TAC[GSYM INT_REM_EQ] THEN CONV_TAC INT_REDUCE_CONV);;

let MLDSA_NTT_INV_COEFF = prove
 (`!a k. (!i. i < 256 ==> &0 <= a i /\ a i < &8380417) /\ k < 256
         ==> coeff k (mldsa_ntt_inv a) =
             (&8347681 *
              isum (0..255)
               (\j. a(bitreverse8 j) * &731434 pow ((2 * j + 1) * k)))
             rem &8380417`,
  SIMP_TAC[MLDSA_NTT_INV_EXPLICIT; COEFF_MLDSA_POLY]);;

let MLDSA_NTT_INV_TOMONT = prove
 (`!a k. k < 256
         ==> (&2 pow 32 * coeff k (mldsa_ntt_inv (\i. a i rem &8380417)))
             rem &8380417 =
             (&2 pow 24 *
              isum (0..255)
               (\j. a(bitreverse8 j) * &731434 pow ((2 * j + 1) * k)))
             rem &8380417`,
  REPEAT STRIP_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) MLDSA_NTT_INV_COEFF o
    rand o lhand o lhand o snd) THEN
  ASM_REWRITE_TAC[INT_REM_POS_EQ; INT_LT_REM_EQ] THEN
  CONV_TAC INT_REDUCE_CONV THEN DISCH_THEN SUBST1_TAC THEN
  CONV_TAC INT_REM_DOWN_CONV THEN REWRITE_TAC[INT_REM_EQ] THEN
  MATCH_MP_TAC(INTEGER_RULE
   `!s s' n. (s':int == s) (mod n) /\ (a * b == c) (mod n)
             ==> (a * b * s' == c * s) (mod n)`) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC INT_CONG_ISUM THEN REWRITE_TAC[FINITE_NUMSEG] THEN
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC(INTEGER_RULE
     `(x:int == y) (mod n) ==> (x * z == y * z) (mod n)`) THEN
    REWRITE_TAC[INT_CONG_LREM; INTEGER_RULE `(x:int == x) (mod n)`];
    REWRITE_TAC[GSYM INT_REM_EQ] THEN CONV_TAC INT_REDUCE_CONV]);;

(* ------------------------------------------------------------------------- *)
(* Byte strings: the bit packings (mldsa_encode is mlkem_encode, and         *)
(* mldsa_field reads its fields back), sub-lists, and the bit lengths used   *)
(* by the three parameter sets.                                              *)
(* ------------------------------------------------------------------------- *)

let MLDSA_ENCODE_MLKEM_ENCODE = prove
 (`mldsa_encode = mlkem_encode`,
  REWRITE_TAC[FUN_EQ_THM; mldsa_encode; mlkem_encode]);;

let MLDSA_ENCODE_LENGTH = prove
 (`!c n f. LENGTH(mldsa_encode c n f) = (c * n) DIV 8`,
  REWRITE_TAC[MLDSA_ENCODE_MLKEM_ENCODE; MLKEM_ENCODE_LENGTH]);;

let NUM_OF_BYTELIST_MLDSA_ENCODE = prove
 (`!c n f. 8 divides (c * n)
           ==> num_of_bytelist(mldsa_encode c n f) =
               nsum {i | i < n}
                    (\i. num_of_int(f i rem &2 pow c) * 2 EXP (c * i))`,
  REWRITE_TAC[MLDSA_ENCODE_MLKEM_ENCODE; NUM_OF_BYTELIST_MLKEM_ENCODE]);;

let MLDSA_ENCODE_EQ = prove
 (`!c n f g. (!i. i < n ==> f i = g i)
             ==> mldsa_encode c n f = mldsa_encode c n g`,
  REWRITE_TAC[MLDSA_ENCODE_MLKEM_ENCODE; MLKEM_ENCODE_EQ]);;

let MLDSA_ENCODE_EQ_REM = prove
 (`!c n f g. (!i. i < n ==> f i rem &2 pow c = g i rem &2 pow c)
             ==> mldsa_encode c n f = mldsa_encode c n g`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mldsa_encode] THEN AP_TERM_TAC THEN
  MATCH_MP_TAC NSUM_EQ THEN ASM_SIMP_TAC[IN_ELIM_THM]);;

let MLDSA_FIELD_BOUND = prove
 (`!c b i. &0 <= mldsa_field c b i /\ mldsa_field c b i < &2 pow c`,
  REWRITE_TAC[mldsa_field; INT_POS; INT_OF_NUM_POW; INT_OF_NUM_LT] THEN
  REWRITE_TAC[MOD_LT_EQ; EXP_EQ_0; ARITH_EQ]);;

let MLDSA_FIELD_ENCODE = prove
 (`!c n f i.
        8 divides (c * n) /\ i < n
        ==> mldsa_field c (mldsa_encode c n f) i = f i rem &2 pow c`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[mldsa_field; NUM_OF_BYTELIST_MLDSA_ENCODE] THEN
  REWRITE_TAC[MESON[EXP_EXP; MULT_SYM]
   `b * 2 EXP (d * i) = (2 EXP d) EXP i * b`] THEN
  REWRITE_TAC[GSYM EXP_EXP] THEN
  MP_TAC(ISPECL [`2 EXP c`; `\i. num_of_int ((f:num->int) i rem &2 pow c)`;
                 `{i:num | i < n}`; `i:num`] DIGITSUM_DIV_MOD) THEN
  REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM; MLKEM_ENCODE_DIGIT] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[MLKEM_ENCODE_DIGIT]);;

let MLDSA_FIELD_ENCODE_SMALL = prove
 (`!c n f i.
        8 divides (c * n) /\ i < n /\ &0 <= f i /\ f i < &2 pow c
        ==> mldsa_field c (mldsa_encode c n f) i = f i`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[MLDSA_FIELD_ENCODE] THEN
  MATCH_MP_TAC INT_REM_LT THEN ASM_REWRITE_TAC[]);;

let MLDSA_ENCODE_FIELD = prove
 (`!c n b. 8 divides (c * n) /\ LENGTH b = (c * n) DIV 8
           ==> mldsa_encode c n (mldsa_field c b) = b`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM BYTELIST_OF_NUM_OF_BYTELIST] THEN
  ASM_REWRITE_TAC[mldsa_encode] THEN AP_TERM_TAC THEN
  REWRITE_TAC[mldsa_field; INT_OF_NUM_POW; INT_OF_NUM_REM;
              NUM_OF_INT_OF_NUM; MOD_MOD_REFL] THEN
  REWRITE_TAC[MESON[EXP_EXP; MULT_SYM]
   `b * 2 EXP (d * i) = (2 EXP d) EXP i * b`] THEN
  REWRITE_TAC[GSYM EXP_EXP; DIGITSUM_WORKS_GEN] THEN
  MATCH_MP_TAC MOD_LT THEN REWRITE_TAC[EXP_EXP] THEN
  MP_TAC(ISPEC `b:byte list` NUM_OF_BYTELIST_BOUND) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `m:num` SUBST_ALL_TAC o
    REWRITE_RULE[divides]) THEN
  ASM_REWRITE_TAC[ARITH_RULE `(8 * m) DIV 8 = m`] THEN
  REWRITE_TAC[EXP_EXP; ARITH_RULE `256 = 2 EXP 8`]);;

let LENGTH_MLDSA_SLICE = prove
 (`!a n l. LENGTH(mldsa_slice a n l) = n`,
  REWRITE_TAC[mldsa_slice; LENGTH_LIST_OF_SEQ]);;

let EL_MLDSA_SLICE = prove
 (`!a n l i. i < n ==> EL i (mldsa_slice a n l) = EL (a + i) l`,
  SIMP_TAC[mldsa_slice; EL_LIST_OF_SEQ]);;

let MLDSA_SLICE_LENGTH = prove
 (`!l. mldsa_slice 0 (LENGTH l) l = l`,
  GEN_TAC THEN REWRITE_TAC[LIST_EQ; LENGTH_MLDSA_SLICE] THEN
  SIMP_TAC[EL_MLDSA_SLICE; ADD_CLAUSES]);;

let MLDSA_SLICE_SLICE = prove
 (`!a n b m l. a + n <= m
               ==> mldsa_slice a n (mldsa_slice b m l) =
                   mldsa_slice (b + a) n l`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LIST_EQ; LENGTH_MLDSA_SLICE] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[EL_MLDSA_SLICE] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) EL_MLDSA_SLICE o lhand o snd) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[ADD_ASSOC]);;

let MLDSA_SLICE_APPEND = prove
 (`!a n l m.
        (a + n <= LENGTH l
         ==> mldsa_slice a n (APPEND l m) = mldsa_slice a n l) /\
        (LENGTH l <= a
         ==> mldsa_slice a n (APPEND l m) = mldsa_slice (a - LENGTH l) n m)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LIST_EQ; LENGTH_MLDSA_SLICE] THEN
  SIMP_TAC[EL_MLDSA_SLICE; EL_APPEND] THEN REPEAT STRIP_TAC THEN
  COND_CASES_TAC THEN TRY(AP_THM_TAC THEN AP_TERM_TAC) THEN
  ASM_ARITH_TAC);;

let MLDSA_BITLEN_UNIQUE = prove
 (`!n c. n < 2 EXP c /\ 2 EXP c <= 2 * n ==> mldsa_bitlen n = c`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mldsa_bitlen] THEN
  MATCH_MP_TAC MINIMAL_UNIQUE THEN ASM_REWRITE_TAC[NOT_LT] THEN
  X_GEN_TAC `m:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `2 EXP c = 2 * 2 EXP (c - 1) /\ 2 EXP m <= 2 EXP (c - 1)`
  MP_TAC THENL
   [REWRITE_TAC[GSYM(CONJUNCT2 EXP); LE_EXP] THEN
    CONJ_TAC THENL [AP_TERM_TAC; ALL_TAC] THEN ASM_ARITH_TAC;
    ASM_ARITH_TAC]);;

let MLDSA_BITLEN_0 = prove
 (`mldsa_bitlen 0 = 0`,
  REWRITE_TAC[mldsa_bitlen] THEN MATCH_MP_TAC MINIMAL_UNIQUE THEN
  REWRITE_TAC[EXP; LT] THEN ARITH_TAC);;

(* Evaluation of mldsa_bitlen n for a numeral n.                             *)

let MLDSA_BITLEN_CONV =
  let pth = MLDSA_BITLEN_UNIQUE in
  let rec bits n = if n =/ num 0 then 0 else 1 + bits (quo_num n (num 2)) in
  fun tm ->
    match tm with
      Comb(Const("mldsa_bitlen",_),ntm) when is_numeral ntm ->
        let n = dest_numeral ntm in
        if n =/ num 0 then MLDSA_BITLEN_0 else
        let th = SPECL [ntm; mk_small_numeral(bits n)] pth in
        MP th (EQT_ELIM(NUM_REDUCE_CONV(lhand(concl th))))
    | _ -> failwith "MLDSA_BITLEN_CONV";;

let MLDSA_BITLEN_CLAUSES = prove
 (`mldsa_bitlen 4 = 3 /\ mldsa_bitlen 8 = 4 /\ mldsa_bitlen 15 = 4 /\
   mldsa_bitlen 43 = 6 /\ mldsa_bitlen 131071 = 17 /\
   mldsa_bitlen 524287 = 19`,
  CONV_TAC(DEPTH_CONV MLDSA_BITLEN_CONV) THEN REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The ML-DSA algorithms in the NTT-domain form of the pseudocode of FIPS    *)
(* 204 Algorithms 6 (key generation), 7 (one attempt of the signing loop)    *)
(* and 8 (verification): A^ is the matrix of RejNTTPoly samples, and the     *)
(* products are pointwise products of NTTs followed by NTT^-1. They need the *)
(* assumption that the RejNTTPoly values used are < q, which holds whenever  *)
(* RejNTTPoly is well defined, i.e. whenever the loop of FIPS 204 Algorithm  *)
(* 30 terminates.                                                            *)
(* ------------------------------------------------------------------------- *)

let MLDSA_REJ_NTT_POLY_POS = prove
 (`!rho i. &0 <= mldsa_rej_ntt_poly rho i`,
  REWRITE_TAC[mldsa_rej_ntt_poly] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[INT_POS]);;

let MLDSA_REJ_BOUNDED_POLY_IN_RQ = prove
 (`!eta rho. mldsa_rej_bounded_poly eta rho IN ring_carrier mldsa_rq`,
  REWRITE_TAC[mldsa_rej_bounded_poly] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[MLDSA_POLY_IN_RQ]);;

let MLDSA_EXPAND_MASK_IN_RQ = prove
 (`!gamma1 rho kappa r.
        mldsa_expand_mask gamma1 rho kappa r IN ring_carrier mldsa_rq`,
  REWRITE_TAC[mldsa_expand_mask] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[MLDSA_POLY_IN_RQ]);;

let MLDSA_SAMPLE_IN_BALL_IN_RQ = prove
 (`!tau rho. mldsa_sample_in_ball tau rho IN ring_carrier mldsa_rq`,
  REWRITE_TAC[mldsa_sample_in_ball; MLDSA_POLY_IN_RQ]);;

let MLDSA_EXPAND_A = prove
 (`!rho i. mldsa_expand_a rho i =
           \j. mldsa_ntt_inv
                (mldsa_rej_ntt_poly (APPEND rho [word j; word i]))`,
  REWRITE_TAC[FUN_EQ_THM; mldsa_expand_a]);;

let MLDSA_DOT_EXPAND_A = prove
 (`!rho k l.
        (!i j n. i < k /\ j < l /\ n < 256
                 ==> mldsa_rej_ntt_poly (APPEND rho [word j; word i]) n
                     < &8380417)
        ==> !s i. (!j. j < l ==> s j IN ring_carrier mldsa_rq) /\ i < k
                  ==> mldsa_dot l (mldsa_expand_a rho i) s =
                      mldsa_ntt_inv
                       (\n. ring_sum mldsa_zq {j | j < l}
                             (\j. ring_mul mldsa_zq
                                   (mldsa_rej_ntt_poly
                                     (APPEND rho [word j; word i]) n)
                                   (mldsa_ntt (s j) n)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[MLDSA_EXPAND_A] THEN
  MP_TAC(ISPECL [`l:num`;
                 `\j. mldsa_rej_ntt_poly (APPEND rho [word j; word i])`;
                 `s:num->(1->num)->int`] MLDSA_DOT_NTT_INV) THEN
  ASM_SIMP_TAC[MLDSA_REJ_NTT_POLY_POS]);;

let DIV256_LT = ARITH_RULE `!n k. n DIV 256 < k <=> n < 256 * k`;;

(* ASM_SIMP_TAC with p in the context when simplifying q in p /\ q, as in    *)
(* the hints h = \p. p < 256 * k /\ ... of mldsa_sign_attempt.               *)

let MLDSA_CONJ_SIMP_TAC =
  let CONJ_CONG = TAUT
   `(p <=> p') ==> (p' ==> (q <=> q')) ==> (p /\ q <=> p' /\ q')` in
  fun thl ->
    let Simpset(net,prover,provers,rewmaker) = basic_ss [] in
    let ss = Simpset(net_of_cong CONJ_CONG net,prover,provers,rewmaker) in
    ASM(fun thl' -> CONV_TAC(SIMPLIFY_CONV ss thl')) thl;;

let MLDSA_KEYGEN_INTERNAL_FIPS = prove
 (`!k l eta tau lam gamma1 gamma2 omega xi.
        (!i j n. i < k /\ j < l /\ n < 256
                 ==> mldsa_rej_ntt_poly
                      (APPEND (mldsa_slice 0 32
                                (mldsa_h (APPEND xi [word k; word l]) 128))
                              [word j; word i]) n < &8380417)
        ==> mldsa_keygen_internal (k,l,eta,tau,lam,gamma1,gamma2,omega) xi =
            let seeds = mldsa_h (APPEND xi [word k; word l]) 128 in
            let rho = mldsa_slice 0 32 seeds
            and rho' = mldsa_slice 32 64 seeds
            and key = mldsa_slice 96 32 seeds in
            let Ahat = \i j. mldsa_rej_ntt_poly (APPEND rho [word j; word i]) in
            let s1 = \i. mldsa_rej_bounded_poly eta
                          (APPEND rho' (bytelist_of_num 2 i)) in
            let s2 = \i. mldsa_rej_bounded_poly eta
                          (APPEND rho' (bytelist_of_num 2 (l + i))) in
            let s1hat = \i. mldsa_ntt (s1 i) in
            let t = \i. ring_add mldsa_rq
                         (mldsa_ntt_inv
                           (\n. ring_sum mldsa_zq {j | j < l}
                                 (\j. ring_mul mldsa_zq (Ahat i j n)
                                                        (s1hat j n))))
                         (s2 i) in
            let t1 = \n. FST(mldsa_power2round
                              (coeff (n MOD 256) (t(n DIV 256)))) in
            let t0 = \n. SND(mldsa_power2round
                              (coeff (n MOD 256) (t(n DIV 256)))) in
            let pk = APPEND rho (mldsa_encode 10 (256 * k) t1) in
            let c = mldsa_bitlen(2 * eta) in
            let s1b = mldsa_encode c (256 * l)
                       (\n. &eta - mldsa_modpm (coeff (n MOD 256)
                                                (s1(n DIV 256))) 8380417)
            and s2b = mldsa_encode c (256 * k)
                       (\n. &eta - mldsa_modpm (coeff (n MOD 256)
                                                (s2(n DIV 256))) 8380417)
            and t0b = mldsa_encode 13 (256 * k) (\n. &4096 - t0 n) in
            pk,APPEND rho (APPEND key (APPEND (mldsa_h pk 64)
                                              (APPEND s1b (APPEND s2b t0b))))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mldsa_keygen_internal] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ABBREV_TAC
   `rho = mldsa_slice 0 32 (mldsa_h (APPEND xi [word k; word l]) 128)` THEN
  DISCH_THEN(ASSUME_TAC o MATCH_MP MLDSA_DOT_EXPAND_A) THEN
  REWRITE_TAC[mldsa_encode] THEN
  ASM_SIMP_TAC[DIV256_LT; MLDSA_REJ_BOUNDED_POLY_IN_RQ]);;

let MLDSA_SIGN_ATTEMPT_FIPS = prove
 (`!k l eta tau lam gamma1 gamma2 omega rho s1 s2 t0 mu rho'' kappa.
        (!i j n. i < k /\ j < l /\ n < 256
                 ==> mldsa_rej_ntt_poly (APPEND rho [word j; word i]) n
                     < &8380417) /\
        (!i. i < l ==> s1 i IN ring_carrier mldsa_rq) /\
        (!i. i < k ==> s2 i IN ring_carrier mldsa_rq /\
                       t0 i IN ring_carrier mldsa_rq)
        ==> mldsa_sign_attempt (k,l,eta,tau,lam,gamma1,gamma2,omega)
             (mldsa_expand_a rho) s1 s2 t0 mu rho'' kappa =
            let Ahat = \i j. mldsa_rej_ntt_poly (APPEND rho [word j; word i]) in
            let s1hat = \i. mldsa_ntt (s1 i)
            and s2hat = \i. mldsa_ntt (s2 i)
            and t0hat = \i. mldsa_ntt (t0 i) in
            let y = \i. mldsa_expand_mask gamma1 rho'' kappa i in
            let yhat = \i. mldsa_ntt (y i) in
            let w = \i. mldsa_ntt_inv
                         (\n. ring_sum mldsa_zq {j | j < l}
                               (\j. ring_mul mldsa_zq (Ahat i j n)
                                                      (yhat j n))) in
            let w1 = \n. mldsa_highbits gamma2
                          (coeff (n MOD 256) (w(n DIV 256))) in
            let ct = mldsa_h (APPEND mu (mldsa_encode
                                (mldsa_bitlen(8380416 DIV (2 * gamma2) - 1))
                                (256 * k) w1))
                             (lam DIV 4) in
            let c = mldsa_sample_in_ball tau ct in
            let chat = mldsa_ntt c in
            let cs1 = \i. mldsa_ntt_inv
                           (\n. ring_mul mldsa_zq (chat n) (s1hat i n))
            and cs2 = \i. mldsa_ntt_inv
                           (\n. ring_mul mldsa_zq (chat n) (s2hat i n)) in
            let z = \i. ring_add mldsa_rq (y i) (cs1 i) in
            let r = \i. ring_sub mldsa_rq (w i) (cs2 i) in
            let ct0 = \i. mldsa_ntt_inv
                           (\n. ring_mul mldsa_zq (chat n) (t0hat i n)) in
            let h = \p. p < 256 * k /\
                        mldsa_makehint gamma2
                         (--(coeff (p MOD 256) (ct0(p DIV 256))))
                         (coeff (p MOD 256)
                           (ring_add mldsa_rq (r(p DIV 256))
                                              (ct0(p DIV 256)))) in
            let beta = tau * eta in
            if mldsa_vec_norm_lt l (gamma1 - beta) z /\
               (!i j. i < k /\ j < 256
                      ==> abs(mldsa_lowbits gamma2 (coeff j (r i)))
                          < &(gamma2 - beta)) /\
               mldsa_vec_norm_lt k gamma2 ct0 /\
               mldsa_hint_count h (256 * k) <= omega
            then SOME(APPEND ct
                       (APPEND (mldsa_encode (1 + mldsa_bitlen(gamma1 - 1))
                                             (256 * l)
                                 (\n. &gamma1 -
                                      mldsa_modpm (coeff (n MOD 256)
                                                    (z(n DIV 256)))
                                                  8380417))
                               (mldsa_hintbitpack k omega h)))
            else NONE`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2
   (ASSUME_TAC o MATCH_MP MLDSA_DOT_EXPAND_A) STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[mldsa_sign_attempt] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[mldsa_encode; mldsa_vec_norm_lt] THEN
  MLDSA_CONJ_SIMP_TAC[DIV256_LT; MLDSA_EXPAND_MASK_IN_RQ;
                      MLDSA_SAMPLE_IN_BALL_IN_RQ; GSYM MLDSA_NTT_INV_MUL]);;

let MLDSA_VERIFY_MU_FIPS = prove
 (`!k l eta tau lam gamma1 gamma2 omega pk mu sg.
        (!i j n. i < k /\ j < l /\ n < 256
                 ==> mldsa_rej_ntt_poly
                      (APPEND (mldsa_slice 0 32 pk) [word j; word i]) n
                     < &8380417)
        ==> (mldsa_verify_mu (k,l,eta,tau,lam,gamma1,gamma2,omega) pk mu sg <=>
             let c = 1 + mldsa_bitlen(gamma1 - 1) in
             let rho = mldsa_slice 0 32 pk
             and t1b = mldsa_slice 32 (320 * k) pk in
             let t1 = \i. mldsa_poly
                           (\j. &8192 * mldsa_field 10 t1b (256 * i + j)) in
             let ct = mldsa_slice 0 (lam DIV 4) sg
             and zb = mldsa_slice (lam DIV 4) (32 * c * l) sg
             and hb = mldsa_slice (lam DIV 4 + 32 * c * l) (omega + k) sg in
             let z = \i. mldsa_poly
                          (\j. &gamma1 - mldsa_field c zb (256 * i + j)) in
             LENGTH pk = 32 + 320 * k /\
             LENGTH sg = lam DIV 4 + 32 * c * l + omega + k /\
             match mldsa_hintbitunpack k omega hb with
               NONE -> F
             | SOME h ->
                let Ahat = \i j. mldsa_rej_ntt_poly
                                  (APPEND rho [word j; word i]) in
                let cc = mldsa_sample_in_ball tau ct in
                let zhat = \j. mldsa_ntt (z j)
                and chat = mldsa_ntt cc
                and t1hat = \i. mldsa_ntt (t1 i) in
                let w = \i. mldsa_ntt_inv
                             (\n. ring_sub mldsa_zq
                                   (ring_sum mldsa_zq {j | j < l}
                                     (\j. ring_mul mldsa_zq (Ahat i j n)
                                                            (zhat j n)))
                                   (ring_mul mldsa_zq (chat n)
                                                      (t1hat i n))) in
                let w1 = \n. mldsa_usehint gamma2 (h n)
                              (coeff (n MOD 256) (w(n DIV 256))) in
                mldsa_vec_norm_lt l (gamma1 - tau * eta) z /\
                mldsa_h (APPEND mu (mldsa_encode
                                     (mldsa_bitlen
                                       (8380416 DIV (2 * gamma2) - 1))
                                     (256 * k) w1))
                        (lam DIV 4) = ct)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mldsa_verify_mu] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  DISCH_THEN(ASSUME_TAC o MATCH_MP MLDSA_DOT_EXPAND_A) THEN
  REWRITE_TAC[mldsa_encode] THEN
  ASM_SIMP_TAC[DIV256_LT; MLDSA_POLY_IN_RQ; MLDSA_SAMPLE_IN_BALL_IN_RQ;
               GSYM MLDSA_NTT_INV_MUL; MLDSA_NTT_INV_SUB; RING_SUM; RING_MUL;
               MLDSA_NTT_IN_ZQ]);;

(* ------------------------------------------------------------------------- *)
(* Rounding (FIPS 204 Section 2.3 and Algorithms 35-37). mod+- gives the     *)
(* centered representative. For alpha = 2 * gamma2 a divisor of q - 1,       *)
(* Decompose(r) is the unique pair (r1,r0) with 0 <= r1, alpha * r1 < q - 1, *)
(* r0 in (-gamma2,gamma2] or else r1 = 0 and r0 = -gamma2, and alpha * r1 +  *)
(* r0 == r (mod q) (MLDSA_DECOMPOSE_UNIQUE). These functions depend only on  *)
(* their arguments mod q, and adding s to r shifts the low part by s when    *)
(* that stays strictly inside (-gamma2,gamma2).                              *)
(* ------------------------------------------------------------------------- *)

let MLDSA_MODPM = prove
 (`!a m. ~(m = 0)
         ==> (mldsa_modpm a m == a) (mod &m) /\
             --(&m) < &2 * mldsa_modpm a m /\ &2 * mldsa_modpm a m <= &m`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[mldsa_modpm] THEN
  MP_TAC(ISPECL [`a:int`; `&m:int`] INT_DIVISION) THEN
  ASM_REWRITE_TAC[INT_OF_NUM_EQ; INT_ABS_NUM] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`a:int`; `&m:int`] INT_REM_MOD_SELF) THEN
  DISCH_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
   [ASM_INT_ARITH_TAC;
    CONJ_TAC THENL
     [UNDISCH_TAC `(a rem &m == a) (mod &m)` THEN
      CONV_TAC INTEGER_RULE;
      ASM_INT_ARITH_TAC]]);;

let MLDSA_REM_Q = prove
 (`!r. &0 <= r rem &8380417 /\ r rem &8380417 < &8380417 /\
       (r rem &8380417 == r) (mod &8380417)`,
  REWRITE_TAC[INT_REM_MOD_SELF; INT_REM_POS_EQ; INT_LT_REM_EQ] THEN
  INT_ARITH_TAC);;

let MLDSA_DECOMPOSE_CORE = prove
 (`!a M (N:int) (r0:int) (rp:int).
        &0 < a /\ a * &M = &8380416 /\ &0 <= rp /\ rp < &8380417 /\
        rp - r0 = a * N /\ --a < &2 * r0 /\ &2 * r0 <= a
        ==> &0 <= N /\ N <= &M /\ (N = &M ==> r0 <= &0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `a /\ b /\ (b ==> c) ==> a /\ b /\ c`) THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[GSYM INT_NOT_LT] THEN DISCH_TAC THEN
    SUBGOAL_THEN `(a:int) * N <= a * -- &1` MP_TAC THENL
     [MATCH_MP_TAC INT_LE_LMUL THEN ASM_INT_ARITH_TAC; ASM_INT_ARITH_TAC];
    REWRITE_TAC[GSYM INT_NOT_LT] THEN DISCH_TAC THEN
    SUBGOAL_THEN `(a:int) * (&M + &1) <= a * N` MP_TAC THENL
     [MATCH_MP_TAC INT_LE_LMUL THEN ASM_INT_ARITH_TAC; ASM_INT_ARITH_TAC];
    DISCH_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN ASM_INT_ARITH_TAC]);;

let MLDSA_ARITH2_TAC =
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM INT_OF_NUM_MUL]) THEN
  REWRITE_TAC[GSYM INT_OF_NUM_MUL] THEN ASM_INT_ARITH_TAC;;

let MLDSA_DECOMPOSE_VALID = prove
 (`!gamma2 r.
        ~(gamma2 = 0) /\ (2 * gamma2) divides 8380416
        ==> &0 <= mldsa_highbits gamma2 r /\
            &(2 * gamma2) * mldsa_highbits gamma2 r < &8380416 /\
            (--(&gamma2) < mldsa_lowbits gamma2 r /\
             mldsa_lowbits gamma2 r <= &gamma2 \/
             mldsa_highbits gamma2 r = &0 /\
             mldsa_lowbits gamma2 r = --(&gamma2)) /\
            (&(2 * gamma2) * mldsa_highbits gamma2 r + mldsa_lowbits gamma2 r
             == r) (mod &8380417)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[divides] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_TAC `M:num`)) THEN
  SUBGOAL_THEN `&0:int < &(2 * gamma2) /\ &0:int < &M /\
                &(2 * gamma2) * &M:int = &8380416`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[INT_OF_NUM_MUL; INT_OF_NUM_LT; INT_OF_NUM_EQ] THEN
    UNDISCH_TAC `8380416 = (2 * gamma2) * M` THEN
    ASM_CASES_TAC `M = 0` THEN ASM_REWRITE_TAC[MULT_CLAUSES] THEN
    ASM_ARITH_TAC;
    UNDISCH_THEN `8380416 = (2 * gamma2) * M` (K ALL_TAC)] THEN
  REWRITE_TAC[mldsa_highbits; mldsa_lowbits; mldsa_decompose] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  MP_TAC(SPEC `r:int` MLDSA_REM_Q) THEN
  SPEC_TAC(`r rem &8380417`,`rp:int`) THEN GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`rp:int`; `2 * gamma2`] MLDSA_MODPM) THEN
  REWRITE_TAC[MULT_EQ_0; ARITH_EQ] THEN ASM_REWRITE_TAC[] THEN
  SPEC_TAC(`mldsa_modpm rp (2 * gamma2)`,`r0:int`) THEN GEN_TAC THEN
  REWRITE_TAC[int_congruent] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `n:int`) STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `rp - r0:int = &(2 * gamma2) * --n` ASSUME_TAC THENL
   [ASM_INT_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`&(2 * gamma2):int`; `M:num`; `--n:int`; `r0:int`;
                 `rp:int`] MLDSA_DECOMPOSE_CORE) THEN
  ANTS_TAC THENL [ASM_INT_ARITH_TAC; STRIP_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(&(2 * gamma2) * --n) div &(2 * gamma2) = --n:int`
  SUBST1_TAC THENL
   [MATCH_MP_TAC(CONJUNCT2 INT_DIV_MUL) THEN ASM_INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&(2 * gamma2) * --n = &8380416 <=> --n = &M:int`
  SUBST1_TAC THENL
   [SUBST1_TAC(SYM(ASSUME `&(2 * gamma2) * &M:int = &8380416`)) THEN
    REWRITE_TAC[INT_EQ_MUL_LCANCEL] THEN ASM_INT_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `(rp == r:int) (mod &8380417)` THEN
  REWRITE_TAC[int_congruent] THEN
  DISCH_THEN(X_CHOOSE_TAC `e:int`) THEN
  ASM_CASES_TAC `--n:int = &M` THEN ASM_REWRITE_TAC[INT_MUL_RZERO] THENL
   [SUBGOAL_THEN `rp - r0:int = &8380416` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THEN
  FIRST [EXISTS_TAC `e:int` THEN MLDSA_ARITH2_TAC;
         EXISTS_TAC `e - &1:int` THEN MLDSA_ARITH2_TAC;
         SUBST1_TAC(SYM(ASSUME `&(2 * gamma2) * &M:int = &8380416`)) THEN
         ASM_SIMP_TAC[INT_LT_LMUL_EQ] THEN MLDSA_ARITH2_TAC;
         MLDSA_ARITH2_TAC]);;

let MLDSA_DECOMPOSE_UNIQUE_CORE = prove
 (`!a g M (x1:int) x0 y1 y0.
        &0 < g /\ a = &2 * g /\ a * &M = &8380416 /\
        &0 <= x1 /\ a * x1 < &8380416 /\
        (--g < x0 /\ x0 <= g \/ x1 = &0 /\ x0 = --g) /\
        &0 <= y1 /\ a * y1 < &8380416 /\
        (--g < y0 /\ y0 <= g \/ y1 = &0 /\ y0 = --g) /\
        (a * x1 + x0 == a * y1 + y0) (mod &8380417)
        ==> x1 = y1 /\ x0 = y0`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `&0:int < a` ASSUME_TAC THENL
   [ASM_INT_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(x1:int) < &M /\ (y1:int) < &M` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN REWRITE_TAC[GSYM INT_NOT_LE] THEN DISCH_TAC THENL
     [SUBGOAL_THEN `a * &M <= a * x1:int` MP_TAC;
      SUBGOAL_THEN `a * &M <= a * y1:int` MP_TAC] THEN
    (CONJ_TAC ORELSE ALL_TAC) THEN
    TRY(MATCH_MP_TAC INT_LE_LMUL THEN ASM_INT_ARITH_TAC) THEN
    ASM_INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(a:int) * x1 <= a * (&M - &1) /\ a * y1 <= a * (&M - &1)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC INT_LE_LMUL THEN ASM_INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (a:int) * x1 /\ &0 <= a * y1` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC INT_LE_MUL THEN ASM_INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `a * (&M - &1):int = &8380416 - a` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[INT_SUB_LDISTRIB; INT_MUL_RID]; ALL_TAC] THEN
  SUBGOAL_THEN `a * x1 + x0:int = a * y1 + y0` ASSUME_TAC THENL
   [UNDISCH_TAC `(a * x1 + x0 == a * y1 + y0:int) (mod &8380417)` THEN
    REWRITE_TAC[int_congruent] THEN DISCH_THEN(X_CHOOSE_TAC `d:int`) THEN
    ASM_CASES_TAC `d:int = &0` THENL
     [UNDISCH_TAC `(a * x1 + x0) - (a * y1 + y0):int = &8380417 * d` THEN
      ASM_REWRITE_TAC[INT_MUL_RZERO] THEN INT_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&8380417 * &1 <= abs(&8380417 * d:int)` MP_TAC THENL
     [REWRITE_TAC[INT_ABS_MUL; INT_ABS_NUM] THEN
      MATCH_MP_TAC INT_LE_LMUL THEN ASM_INT_ARITH_TAC;
      ALL_TAC] THEN
    UNDISCH_TAC `(a * x1 + x0) - (a * y1 + y0):int = &8380417 * d` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `x1:int = y1` ASSUME_TAC THENL
   [ALL_TAC; UNDISCH_TAC `a * x1 + x0:int = a * y1 + y0` THEN
    ASM_REWRITE_TAC[] THEN INT_ARITH_TAC] THEN
  REWRITE_TAC[GSYM INT_LE_ANTISYM; GSYM INT_NOT_LT] THEN
  CONJ_TAC THEN DISCH_TAC THENL
   [SUBGOAL_THEN `a * (y1 + &1):int <= a * x1` MP_TAC THENL
     [MATCH_MP_TAC INT_LE_LMUL THEN ASM_INT_ARITH_TAC;
      REWRITE_TAC[INT_ADD_LDISTRIB; INT_MUL_RID] THEN ASM_INT_ARITH_TAC];
    SUBGOAL_THEN `a * (x1 + &1):int <= a * y1` MP_TAC THENL
     [MATCH_MP_TAC INT_LE_LMUL THEN ASM_INT_ARITH_TAC;
      REWRITE_TAC[INT_ADD_LDISTRIB; INT_MUL_RID] THEN ASM_INT_ARITH_TAC]]);;

let MLDSA_DECOMPOSE_PAIR = prove
 (`!gamma2 r. mldsa_decompose gamma2 r =
              mldsa_highbits gamma2 r,mldsa_lowbits gamma2 r`,
  REWRITE_TAC[mldsa_highbits; mldsa_lowbits]);;

let MLDSA_DECOMPOSE_UNIQUE = prove
 (`!gamma2 r r1 r0.
        ~(gamma2 = 0) /\ (2 * gamma2) divides 8380416
        ==> (mldsa_decompose gamma2 r = (r1,r0) <=>
             &0 <= r1 /\ &(2 * gamma2) * r1 < &8380416 /\
             (--(&gamma2) < r0 /\ r0 <= &gamma2 \/
              r1 = &0 /\ r0 = --(&gamma2)) /\
             (&(2 * gamma2) * r1 + r0 == r) (mod &8380417))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `r:int` o MATCH_MP MLDSA_DECOMPOSE_VALID) THEN
  REWRITE_TAC[MLDSA_DECOMPOSE_PAIR; PAIR_EQ] THEN
  SPEC_TAC(`mldsa_highbits gamma2 r`,`h:int`) THEN
  SPEC_TAC(`mldsa_lowbits gamma2 r`,`l:int`) THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN EQ_TAC THENL
   [DISCH_THEN(CONJUNCTS_THEN SUBST_ALL_TAC) THEN ASM_REWRITE_TAC[];
    DISCH_TAC] THEN
  UNDISCH_THEN `~(gamma2 = 0) /\ (2 * gamma2) divides 8380416`
   (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `M:num` (ASSUME_TAC o SYM)) o
    REWRITE_RULE[divides]) THEN
  MATCH_MP_TAC MLDSA_DECOMPOSE_UNIQUE_CORE THEN
  MAP_EVERY EXISTS_TAC [`&(2 * gamma2):int`; `&gamma2:int`; `M:num`] THEN
  ASM_REWRITE_TAC[INT_OF_NUM_MUL; INT_OF_NUM_EQ; INT_OF_NUM_LT;
                  ARITH_RULE `0 < n <=> ~(n = 0)`] THEN
  MATCH_MP_TAC(INTEGER_RULE
   `!a b r n:int. (a == r) (mod n) /\ (b == r) (mod n)
                  ==> (a == b) (mod n)`) THEN
  EXISTS_TAC `r:int` THEN ASM_REWRITE_TAC[]);;

let MLDSA_MODPM_UNIQUE = prove
 (`!a b m. ~(m = 0)
           ==> (mldsa_modpm a m = b <=>
                (b == a) (mod &m) /\ --(&m) < &2 * b /\ &2 * b <= &m)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`a:int`; `m:num`] MLDSA_MODPM) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN EQ_TAC THENL
   [DISCH_THEN(SUBST_ALL_TAC o SYM) THEN ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MATCH_MP_TAC INT_CONG_IMP_EQ THEN EXISTS_TAC `&m:int` THEN
  CONJ_TAC THENL [ASM_INT_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(INTEGER_RULE
   `!x y z n:int. (x == z) (mod n) /\ (y == z) (mod n)
                  ==> (x == y) (mod n)`) THEN
  EXISTS_TAC `a:int` THEN ASM_REWRITE_TAC[]);;

let MLDSA_MODPM_SMALL = prove
 (`!b m. --(&m) < &2 * b /\ &2 * b <= &m ==> mldsa_modpm b m = b`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(m = 0)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN ASM_INT_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[MLDSA_MODPM_UNIQUE; INTEGER_RULE `!x n:int. (x == x) (mod n)`]);;

let MLDSA_MODPM_CONG = prove
 (`!a b m. (a == b) (mod &m) ==> mldsa_modpm a m = mldsa_modpm b m`,
  REWRITE_TAC[GSYM INT_REM_EQ] THEN SIMP_TAC[mldsa_modpm]);;

let MLDSA_DECOMPOSE_CONG = prove
 (`!gamma2 x y.
        (x == y) (mod &8380417)
        ==> mldsa_decompose gamma2 x = mldsa_decompose gamma2 y`,
  REWRITE_TAC[GSYM INT_REM_EQ] THEN SIMP_TAC[mldsa_decompose]);;

let MLDSA_HIGHBITS_CONG = prove
 (`!gamma2 x y.
        (x == y) (mod &8380417)
        ==> mldsa_highbits gamma2 x = mldsa_highbits gamma2 y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mldsa_highbits] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC MLDSA_DECOMPOSE_CONG THEN
  ASM_REWRITE_TAC[]);;

let MLDSA_LOWBITS_CONG = prove
 (`!gamma2 x y.
        (x == y) (mod &8380417)
        ==> mldsa_lowbits gamma2 x = mldsa_lowbits gamma2 y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mldsa_lowbits] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC MLDSA_DECOMPOSE_CONG THEN
  ASM_REWRITE_TAC[]);;

let MLDSA_LOWBITS_BOUND = prove
 (`!gamma2 r.
        ~(gamma2 = 0) /\ (2 * gamma2) divides 8380416
        ==> abs(mldsa_lowbits gamma2 r) <= &gamma2`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o
             SPEC `r:int` o MATCH_MP MLDSA_DECOMPOSE_VALID) THEN
  INT_ARITH_TAC);;

let MLDSA_DECOMPOSE_ADD = prove
 (`!gamma2 x s.
        ~(gamma2 = 0) /\ (2 * gamma2) divides 8380416 /\
        abs(mldsa_lowbits gamma2 x + s) < &gamma2
        ==> mldsa_highbits gamma2 (x + s) = mldsa_highbits gamma2 x /\
            mldsa_lowbits gamma2 (x + s) = mldsa_lowbits gamma2 x + s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM PAIR_EQ; GSYM MLDSA_DECOMPOSE_PAIR] THEN
  ASM_SIMP_TAC[MLDSA_DECOMPOSE_UNIQUE] THEN
  MP_TAC(SPECL [`gamma2:num`; `x:int`] MLDSA_DECOMPOSE_VALID) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [UNDISCH_TAC `abs(mldsa_lowbits gamma2 x + s) < &gamma2` THEN
    INT_ARITH_TAC;
    MATCH_MP_TAC(INTEGER_RULE
     `!a b x s n:int. (a + b == x) (mod n)
                      ==> (a + (b + s) == x + s) (mod n)`) THEN
    ASM_REWRITE_TAC[]]);;

let MLDSA_DECOMPOSE_SUB = prove
 (`!gamma2 w s.
        ~(gamma2 = 0) /\ (2 * gamma2) divides 8380416 /\
        abs(mldsa_modpm (mldsa_lowbits gamma2 w - s) 8380417) < &gamma2
        ==> mldsa_highbits gamma2 (w - s) = mldsa_highbits gamma2 w /\
            mldsa_lowbits gamma2 (w - s) =
            mldsa_modpm (mldsa_lowbits gamma2 w - s) 8380417`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`mldsa_lowbits gamma2 w - s`; `8380417`] MLDSA_MODPM) THEN
  REWRITE_TAC[ARITH_EQ] THEN
  ABBREV_TAC `u = mldsa_modpm (mldsa_lowbits gamma2 w - s) 8380417` THEN
  STRIP_TAC THEN
  REWRITE_TAC[GSYM PAIR_EQ; GSYM MLDSA_DECOMPOSE_PAIR] THEN
  ASM_SIMP_TAC[MLDSA_DECOMPOSE_UNIQUE] THEN
  MP_TAC(SPECL [`gamma2:num`; `w:int`] MLDSA_DECOMPOSE_VALID) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [UNDISCH_TAC `abs(u:int) < &gamma2` THEN INT_ARITH_TAC;
    MATCH_MP_TAC(INTEGER_RULE
     `!x w0 w u s n:int. (x + w0 == w) (mod n) /\ (u == w0 - s) (mod n)
                         ==> (x + u == w - s) (mod n)`) THEN
    EXISTS_TAC `mldsa_lowbits gamma2 w` THEN ASM_REWRITE_TAC[]]);;

let MLDSA_MODPM_ABS_LE = prove
 (`!x. abs(mldsa_modpm x 8380417) <= abs x`,
  GEN_TAC THEN MP_TAC(ISPECL [`x:int`; `8380417`] MLDSA_MODPM) THEN
  REWRITE_TAC[ARITH_EQ; int_congruent] THEN
  ABBREV_TAC `r = mldsa_modpm x 8380417` THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `d:int`) STRIP_ASSUME_TAC) THEN
  ASM_CASES_TAC `d:int = &0` THENL
   [UNDISCH_TAC `r - x:int = &8380417 * d` THEN
    ASM_REWRITE_TAC[INT_MUL_RZERO] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&8380417 * &1 <= abs(&8380417 * d:int)` MP_TAC THENL
   [REWRITE_TAC[INT_ABS_MUL; INT_ABS_NUM] THEN
    MATCH_MP_TAC INT_LE_LMUL THEN ASM_INT_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `r - x:int = &8380417 * d` THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_INT_ARITH_TAC);;

let MLDSA_MAKEHINT_CONG = prove
 (`!gamma2 z z' r r'.
        (z == z') (mod &8380417) /\ (r == r') (mod &8380417)
        ==> (mldsa_makehint gamma2 z r <=> mldsa_makehint gamma2 z' r')`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mldsa_makehint] THEN
  AP_TERM_TAC THEN BINOP_TAC THEN
  MATCH_MP_TAC MLDSA_HIGHBITS_CONG THEN
  REPEAT(POP_ASSUM MP_TAC) THEN SPEC_TAC(`&8380417:int`,`n:int`) THEN
  CONV_TAC INTEGER_RULE);;

let MLDSA_MODPM_REM = prove
 (`!x m. mldsa_modpm (x rem &m) m = mldsa_modpm x m`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC MLDSA_MODPM_CONG THEN
  REWRITE_TAC[INT_REM_MOD_SELF]);;

let MLDSA_DECOMPOSE_REM = prove
 (`!gamma2 x. mldsa_decompose gamma2 (x rem &8380417) =
              mldsa_decompose gamma2 x`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC MLDSA_DECOMPOSE_CONG THEN
  REWRITE_TAC[INT_REM_MOD_SELF]);;

let MLDSA_HIGHBITS_REM = prove
 (`!gamma2 x. mldsa_highbits gamma2 (x rem &8380417) =
              mldsa_highbits gamma2 x`,
  REWRITE_TAC[mldsa_highbits; MLDSA_DECOMPOSE_REM]);;

let MLDSA_LOWBITS_REM = prove
 (`!gamma2 x. mldsa_lowbits gamma2 (x rem &8380417) =
              mldsa_lowbits gamma2 x`,
  REWRITE_TAC[mldsa_lowbits; MLDSA_DECOMPOSE_REM]);;

let MLDSA_MAKEHINT_REM = prove
 (`(!gamma2 z r. mldsa_makehint gamma2 (z rem &8380417) r <=>
                 mldsa_makehint gamma2 z r) /\
   (!gamma2 z r. mldsa_makehint gamma2 z (r rem &8380417) <=>
                 mldsa_makehint gamma2 z r)`,
  CONJ_TAC THEN REPEAT GEN_TAC THEN MATCH_MP_TAC MLDSA_MAKEHINT_CONG THEN
  REWRITE_TAC[INT_REM_MOD_SELF; INTEGER_RULE `!x n:int. (x == x) (mod n)`]);;

(* Normalize the arguments of the functions on Z_q to a single "rem".        *)

let MLDSA_REM_NORM_TAC =
  let ths = [MLDSA_MODPM_REM; MLDSA_HIGHBITS_REM; MLDSA_LOWBITS_REM;
             CONJUNCT2 MLDSA_MAKEHINT_REM] in
  ONCE_REWRITE_TAC[GSYM MLDSA_HIGHBITS_REM; GSYM MLDSA_LOWBITS_REM;
                   GSYM(CONJUNCT2 MLDSA_MAKEHINT_REM)] THEN
  ONCE_REWRITE_TAC[GSYM(SPECL [`x:int`; `8380417`] MLDSA_MODPM_REM)] THEN
  CONV_TAC INT_REM_DOWN_CONV THEN REWRITE_TAC ths;;

let MLDSA_GAMMA2_CLAUSES = prove
 (`(~(95232 = 0) /\ (2 * 95232) divides 8380416 /\ 4 * 95232 <= 8380416) /\
   (~(261888 = 0) /\ (2 * 261888) divides 8380416 /\
    4 * 261888 <= 8380416)`,
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC(ONCE_DEPTH_CONV DIVIDES_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV);;

(* ------------------------------------------------------------------------- *)
(* The alternative way of checking the low bits and computing the hints of   *)
(* Section 5.1 of the Round 3 Dilithium specification, which FIPS 204        *)
(* explicitly permits. With w0 the low part of w and |s| <= beta, ||w0 - s|| *)
(* < gamma2 - beta iff ||LowBits(w - s)|| < gamma2 - beta (the paper's Lemma *)
(* 3, MLDSA_LOWBITS_SUB_ALT), and then the high part of w - s is that of w.  *)
(* For |t| < gamma2 and 4 * gamma2 <= q - 1, MakeHint(-t,r + t) holds unless *)
(* LowBits(r) + t is in (-gamma2,gamma2], or is -gamma2 with HighBits(r) = 0 *)
(* (MLDSA_MAKEHINT_ALT). The forms for the coefficients of elements of R_q   *)
(* follow.                                                                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_LOWBITS_SUB_ALT = prove
 (`!gamma2 beta w s.
        ~(gamma2 = 0) /\ (2 * gamma2) divides 8380416 /\ abs(s) <= &beta
        ==> (abs(mldsa_modpm (mldsa_lowbits gamma2 w - s) 8380417)
             < &gamma2 - &beta <=>
             abs(mldsa_lowbits gamma2 (w - s)) < &gamma2 - &beta)`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN DISCH_TAC THENL
   [MP_TAC(SPECL [`gamma2:num`; `w:int`; `s:int`] MLDSA_DECOMPOSE_SUB) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [POP_ASSUM MP_TAC THEN INT_ARITH_TAC;
      DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(SPECL [`gamma2:num`; `w - s:int`; `s:int`] MLDSA_DECOMPOSE_ADD) THEN
  ASM_REWRITE_TAC[INT_ARITH `(w - s) + s:int = w`] THEN ANTS_TAC THENL
   [UNDISCH_TAC `abs(s:int) <= &beta` THEN
    UNDISCH_TAC `abs(mldsa_lowbits gamma2 (w - s)) < &gamma2 - &beta` THEN
    INT_ARITH_TAC;
    DISCH_THEN(SUBST1_TAC o CONJUNCT2)] THEN
  REWRITE_TAC[INT_ARITH `(x + s) - s:int = x`] THEN
  SUBGOAL_THEN `2 * gamma2 <= 8380416` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o MATCH_MP DIVIDES_LE) THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mldsa_modpm (mldsa_lowbits gamma2 (w - s)) 8380417 =
    mldsa_lowbits gamma2 (w - s)`
   (fun th -> ASM_REWRITE_TAC[th]) THEN
  MATCH_MP_TAC MLDSA_MODPM_SMALL THEN
  UNDISCH_TAC `2 * gamma2 <= 8380416` THEN
  REWRITE_TAC[GSYM INT_OF_NUM_LE; GSYM INT_OF_NUM_MUL] THEN
  UNDISCH_TAC `abs(mldsa_lowbits gamma2 (w - s)) < &gamma2 - &beta` THEN
  INT_ARITH_TAC);;

let MLDSA_MAKEHINT_ALT = prove
 (`!gamma2 r t.
        ~(gamma2 = 0) /\ (2 * gamma2) divides 8380416 /\
        4 * gamma2 <= 8380416 /\ abs(t) < &gamma2
        ==> (mldsa_makehint gamma2 (--t) (r + t) <=>
             ~(--(&gamma2) < mldsa_lowbits gamma2 r + t /\
               mldsa_lowbits gamma2 r + t <= &gamma2 \/
               mldsa_highbits gamma2 r = &0 /\
               mldsa_lowbits gamma2 r + t = --(&gamma2)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[mldsa_makehint; INT_ARITH `(r + t) + --t:int = r`] THEN
  AP_TERM_TAC THEN
  MP_TAC(SPECL [`gamma2:num`; `r + t:int`; `mldsa_highbits gamma2 r`;
                `mldsa_lowbits gamma2 r + t`] MLDSA_DECOMPOSE_UNIQUE) THEN
  MP_TAC(SPECL [`gamma2:num`; `r:int`] MLDSA_DECOMPOSE_VALID) THEN
  MP_TAC(SPECL [`gamma2:num`; `r + t:int`] MLDSA_DECOMPOSE_VALID) THEN
  ASM_REWRITE_TAC[MLDSA_DECOMPOSE_PAIR; PAIR_EQ] THEN
  ABBREV_TAC `h = mldsa_highbits gamma2 r` THEN
  ABBREV_TAC `l = mldsa_lowbits gamma2 r` THEN
  ABBREV_TAC `h' = mldsa_highbits gamma2 (r + t)` THEN
  ABBREV_TAC `l' = mldsa_lowbits gamma2 (r + t)` THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `(&(2 * gamma2) * h + (l + t) == r + t:int) (mod &8380417)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `(&(2 * gamma2) * h + l == r:int) (mod &8380417)` THEN
    SPEC_TAC(`&(2 * gamma2) * h:int`,`a:int`) THEN
    SPEC_TAC(`&8380417:int`,`n:int`) THEN CONV_TAC INTEGER_RULE;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  EQ_TAC THEN SIMP_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN
  MATCH_MP_TAC INT_CONG_IMP_EQ THEN EXISTS_TAC `&8380417:int` THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN `&4 * &gamma2:int <= &8380416` MP_TAC THENL
     [ASM_REWRITE_TAC[INT_OF_NUM_MUL; INT_OF_NUM_LE]; ALL_TAC] THEN
    UNDISCH_TAC `abs(t:int) < &gamma2` THEN
    UNDISCH_TAC `--(&gamma2) < (l:int) /\ l <= &gamma2 \/
                 (h:int) = &0 /\ l = --(&gamma2)` THEN
    UNDISCH_TAC `--(&gamma2) < (l':int) /\ l' <= &gamma2 \/
                 (h:int) = &0 /\ l' = --(&gamma2)` THEN
    INT_ARITH_TAC;
    UNDISCH_TAC `(&(2 * gamma2) * h + l == r:int) (mod &8380417)` THEN
    UNDISCH_TAC `(&(2 * gamma2) * h + l' == r + t:int) (mod &8380417)` THEN
    SPEC_TAC(`&(2 * gamma2) * h:int`,`a:int`) THEN
    SPEC_TAC(`&8380417:int`,`n:int`) THEN CONV_TAC INTEGER_RULE]);;

let MLDSA_HINT_ALT_SCALAR = prove
 (`!gamma2 beta x s t.
        ~(gamma2 = 0) /\ (2 * gamma2) divides 8380416 /\
        4 * gamma2 <= 8380416 /\
        abs(mldsa_modpm (mldsa_lowbits gamma2 x - s) 8380417)
        < &(gamma2 - beta) /\
        abs(mldsa_modpm t 8380417) < &gamma2
        ==> abs(mldsa_lowbits gamma2 (x - s)) < &(gamma2 - beta) /\
            (mldsa_makehint gamma2 (--t) ((x - s) + t) <=>
             let v = mldsa_modpm (mldsa_lowbits gamma2 x - s + t) 8380417 in
             ~(--(&gamma2) < v /\ v <= &gamma2 \/
               mldsa_highbits gamma2 x = &0 /\ v = --(&gamma2)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  MP_TAC(SPECL [`gamma2:num`; `x:int`; `s:int`] MLDSA_DECOMPOSE_SUB) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `abs(mldsa_modpm (mldsa_lowbits gamma2 x - s) 8380417)
                 < &(gamma2 - beta)` THEN
    MATCH_MP_TAC(INT_ARITH `b <= g ==> x < b ==> x:int < g`) THEN
    REWRITE_TAC[INT_OF_NUM_LE] THEN ARITH_TAC;
    STRIP_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `u = mldsa_modpm (mldsa_lowbits gamma2 x - s) 8380417` THEN
  ABBREV_TAC `t' = mldsa_modpm t 8380417` THEN
  MP_TAC(ISPECL [`t:int`; `8380417`] MLDSA_MODPM) THEN
  MP_TAC(ISPECL [`mldsa_lowbits gamma2 x - s`; `8380417`] MLDSA_MODPM) THEN
  ASM_REWRITE_TAC[ARITH_EQ] THEN STRIP_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `mldsa_makehint gamma2 (--t) ((x - s) + t) <=>
    mldsa_makehint gamma2 (--t') ((x - s) + t')`
  SUBST1_TAC THENL
   [MATCH_MP_TAC MLDSA_MAKEHINT_CONG THEN
    UNDISCH_TAC `(t':int == t) (mod &8380417)` THEN
    SPEC_TAC(`&8380417:int`,`n:int`) THEN CONV_TAC INTEGER_RULE;
    ALL_TAC] THEN
  MP_TAC(SPECL [`gamma2:num`; `x - s:int`; `t':int`] MLDSA_MAKEHINT_ALT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `mldsa_modpm (mldsa_lowbits gamma2 x - s + t) 8380417 = u + t'`
  SUBST1_TAC THENL [ALL_TAC; REWRITE_TAC[]] THEN
  ASM_SIMP_TAC[MLDSA_MODPM_UNIQUE; ARITH_EQ] THEN CONJ_TAC THENL
   [UNDISCH_TAC `(t':int == t) (mod &8380417)` THEN
    UNDISCH_TAC `(u == mldsa_lowbits gamma2 x - s:int) (mod &8380417)` THEN
    SPEC_TAC(`mldsa_lowbits gamma2 x`,`a:int`) THEN
    SPEC_TAC(`&8380417:int`,`n:int`) THEN CONV_TAC INTEGER_RULE;
    SUBGOAL_THEN `&4 * &gamma2:int <= &8380416` MP_TAC THENL
     [ASM_REWRITE_TAC[INT_OF_NUM_MUL; INT_OF_NUM_LE]; ALL_TAC] THEN
    SUBGOAL_THEN `&(gamma2 - beta):int <= &gamma2` MP_TAC THENL
     [REWRITE_TAC[INT_OF_NUM_LE] THEN ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `abs(u:int) < &(gamma2 - beta)` THEN
    UNDISCH_TAC `abs(t':int) < &gamma2` THEN
    INT_ARITH_TAC]);;

let MLDSA_LOWBITS_ALT_SCALAR = prove
 (`!gamma2 beta x s.
        ~(gamma2 = 0) /\ (2 * gamma2) divides 8380416 /\
        abs(mldsa_modpm s 8380417) <= &beta /\
        abs(mldsa_lowbits gamma2 (x - s)) < &(gamma2 - beta)
        ==> abs(mldsa_modpm (mldsa_lowbits gamma2 x - s) 8380417)
            < &(gamma2 - beta)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `beta <= gamma2` THENL
   [ALL_TAC;
    UNDISCH_TAC `abs(mldsa_lowbits gamma2 (x - s)) < &(gamma2 - beta)` THEN
    ASM_SIMP_TAC[ARITH_RULE `~(b <= g) ==> g - b = 0`] THEN INT_ARITH_TAC] THEN
  UNDISCH_TAC `abs(mldsa_lowbits gamma2 (x - s)) < &(gamma2 - beta)` THEN
  ASM_SIMP_TAC[GSYM INT_OF_NUM_SUB] THEN
  MP_TAC(ISPECL [`s:int`; `8380417`] MLDSA_MODPM) THEN
  REWRITE_TAC[ARITH_EQ] THEN
  ABBREV_TAC `s' = mldsa_modpm s 8380417` THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `mldsa_modpm (mldsa_lowbits gamma2 x - s) 8380417 =
    mldsa_modpm (mldsa_lowbits gamma2 x - s') 8380417 /\
    mldsa_lowbits gamma2 (x - s) = mldsa_lowbits gamma2 (x - s')`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC MLDSA_MODPM_CONG; MATCH_MP_TAC MLDSA_LOWBITS_CONG] THEN
    UNDISCH_TAC `(s' == s:int) (mod &8380417)` THEN
    SPEC_TAC(`mldsa_lowbits gamma2 x`,`a:int`) THEN
    REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES] THEN
    SPEC_TAC(`&8380417:int`,`n:int`) THEN CONV_TAC INTEGER_RULE;
    ALL_TAC] THEN
  MP_TAC(SPECL [`gamma2:num`; `beta:num`; `x:int`; `s':int`]
               MLDSA_LOWBITS_SUB_ALT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[]);;

let MLDSA_HINT_ALT_COEFF = prove
 (`!gamma2 beta w s t j.
        ~(gamma2 = 0) /\ (2 * gamma2) divides 8380416 /\
        4 * gamma2 <= 8380416 /\
        w IN ring_carrier mldsa_rq /\ s IN ring_carrier mldsa_rq /\
        t IN ring_carrier mldsa_rq /\ j < 256 /\
        abs(mldsa_modpm
             (coeff j (ring_sub mldsa_rq
                        (mldsa_poly(\j. mldsa_lowbits gamma2 (coeff j w))) s))
             8380417) < &(gamma2 - beta) /\
        abs(mldsa_modpm (coeff j t) 8380417) < &gamma2
        ==> abs(mldsa_lowbits gamma2 (coeff j (ring_sub mldsa_rq w s)))
            < &(gamma2 - beta) /\
            (mldsa_makehint gamma2 (--(coeff j t))
               (coeff j (ring_add mldsa_rq (ring_sub mldsa_rq w s) t)) <=>
             let v = mldsa_modpm
                      (coeff j (ring_add mldsa_rq
                        (ring_sub mldsa_rq
                          (mldsa_poly(\j. mldsa_lowbits gamma2 (coeff j w)))
                          s)
                        t)) 8380417 in
             ~(--(&gamma2) < v /\ v <= &gamma2 \/
               mldsa_highbits gamma2 (coeff j w) = &0 /\ v = --(&gamma2)))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[TAUT `a /\ b /\ c /\ d /\ e /\ f /\ g /\ h /\ i ==> j <=>
                    d /\ e /\ f /\ g ==> a /\ b /\ c /\ h /\ i ==> j`] THEN
  STRIP_TAC THEN
  ASM_SIMP_TAC[MLDSA_RQ_COEFF_ADD; MLDSA_RQ_COEFF_SUB; RING_SUB;
               MLDSA_POLY_IN_RQ; COEFF_MLDSA_POLY] THEN
  MLDSA_REM_NORM_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  MP_TAC(SPECL [`gamma2:num`; `beta:num`; `coeff j w:int`; `coeff j s:int`;
                `coeff j t:int`] MLDSA_HINT_ALT_SCALAR) THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[]);;

let MLDSA_LOWBITS_ALT_COEFF = prove
 (`!gamma2 beta w s j.
        ~(gamma2 = 0) /\ (2 * gamma2) divides 8380416 /\
        w IN ring_carrier mldsa_rq /\ s IN ring_carrier mldsa_rq /\
        j < 256 /\
        abs(mldsa_modpm (coeff j s) 8380417) <= &beta /\
        abs(mldsa_lowbits gamma2 (coeff j (ring_sub mldsa_rq w s)))
        < &(gamma2 - beta)
        ==> abs(mldsa_modpm
                 (coeff j (ring_sub mldsa_rq
                    (mldsa_poly(\j. mldsa_lowbits gamma2 (coeff j w))) s))
                 8380417) < &(gamma2 - beta)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[TAUT `a /\ b /\ c /\ d /\ e /\ f /\ g ==> h <=>
                    c /\ d /\ e ==> a /\ b /\ f /\ g ==> h`] THEN
  STRIP_TAC THEN
  ASM_SIMP_TAC[MLDSA_RQ_COEFF_SUB; MLDSA_POLY_IN_RQ; COEFF_MLDSA_POLY] THEN
  MLDSA_REM_NORM_TAC THEN
  REWRITE_TAC[MLDSA_LOWBITS_ALT_SCALAR]);;

(* ------------------------------------------------------------------------- *)
(* SampleInBall gives at most tau nonzero coefficients, each 1 or -1, so     *)
(* each coefficient of c * s has absolute value at most tau * eta = beta     *)
(* when those of s are in [-eta,eta] (MLDSA_SAMPLE_IN_BALL_MUL_BOUND). The   *)
(* vectors that skDecode gives are in that range if the fields of the key    *)
(* are at most 2 * eta; FIPS 204 Algorithm 25 notes that a malformed key can *)
(* give values outside it.                                                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_BALL_COEFFS_BOUND = prove
 (`!tau s k t. abs(mldsa_ball_coeffs tau s k t) <= &1`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[mldsa_ball_coeffs] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REPEAT GEN_TAC THEN REPEAT COND_CASES_TAC THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC INT_REDUCE_CONV);;

let MLDSA_BALL_STEP_SUPPORT = prove
 (`!f:num->int sg j i n.
        FINITE {t | ~(f t = &0)} /\ CARD {t | ~(f t = &0)} <= n
        ==> FINITE {t | ~((if t = j then sg
                           else if t = i then f j else f t) = &0)} /\
            CARD {t | ~((if t = j then sg
                         else if t = i then f j else f t) = &0)}
            <= SUC n`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(MESON[FINITE_SUBSET; CARD_SUBSET; LE_TRANS]
   `!s t:num->bool. FINITE t /\ CARD t <= SUC n /\ s SUBSET t
                    ==> FINITE s /\ CARD s <= SUC n`) THEN
  EXISTS_TAC `j INSERT IMAGE (\x. if x = j then i else x)
                             {t | ~((f:num->int) t = &0)}` THEN
  ASM_SIMP_TAC[FINITE_INSERT; FINITE_IMAGE; CARD_CLAUSES] THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`\x. if x = j then i else (x:num)`;
                   `{t | ~((f:num->int) t = &0)}`] CARD_IMAGE_LE) THEN
    ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_ARITH_TAC;
    REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_INSERT; IN_IMAGE] THEN
    X_GEN_TAC `t:num` THEN ASM_CASES_TAC `t:num = j` THEN
    ASM_REWRITE_TAC[] THEN ASM_CASES_TAC `t:num = i` THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THENL
     [EXISTS_TAC `j:num` THEN ASM_REWRITE_TAC[];
      EXISTS_TAC `t:num` THEN ASM_REWRITE_TAC[]]]);;

let MLDSA_BALL_COEFFS_SUPPORT = prove
 (`!tau s k.
        FINITE {t | ~(mldsa_ball_coeffs tau s k t = &0)} /\
        CARD {t | ~(mldsa_ball_coeffs tau s k t = &0)} <= k`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[mldsa_ball_coeffs; EMPTY_GSPEC; FINITE_EMPTY;
              CARD_CLAUSES; LE_REFL] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  MATCH_MP_TAC MLDSA_BALL_STEP_SUPPORT THEN ASM_REWRITE_TAC[]);;

let MLDSA_SAMPLE_IN_BALL_COEFF = prove
 (`!tau rho i.
        i < 256
        ==> coeff i (mldsa_sample_in_ball tau rho) =
            mldsa_ball_coeffs tau (shake256 rho) tau i rem &8380417`,
  SIMP_TAC[mldsa_sample_in_ball; COEFF_MLDSA_POLY]);;

let MLDSA_BALL_COEFFS_SUM_ABS = prove
 (`!tau s. isum (0..255) (\i. abs(mldsa_ball_coeffs tau s tau i)) <= &tau`,
  REPEAT GEN_TAC THEN
  ABBREV_TAC `b = mldsa_ball_coeffs tau s tau` THEN
  SUBGOAL_THEN
   `isum (0..255) (\i. abs((b:num->int) i)) =
    isum ((0..255) INTER {t | ~(b t = &0)}) (\i. abs(b i))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC ISUM_SUPERSET THEN
    REWRITE_TAC[INTER_SUBSET; IN_INTER; IN_ELIM_THM; INT_ABS_ZERO] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC INT_LE_TRANS THEN
  EXISTS_TAC
   `&(CARD((0..255) INTER {t | ~((b:num->int) t = &0)})) * &1:int` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC ISUM_BOUND THEN
    SIMP_TAC[FINITE_INTER; FINITE_NUMSEG] THEN
    EXPAND_TAC "b" THEN REWRITE_TAC[MLDSA_BALL_COEFFS_BOUND];
    REWRITE_TAC[INT_MUL_RID; INT_OF_NUM_LE] THEN
    MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC `CARD {t | ~((b:num->int) t = &0)}` THEN
    EXPAND_TAC "b" THEN REWRITE_TAC[MLDSA_BALL_COEFFS_SUPPORT] THEN
    MATCH_MP_TAC CARD_SUBSET THEN
    REWRITE_TAC[INTER_SUBSET; MLDSA_BALL_COEFFS_SUPPORT]]);;

let MLDSA_SAMPLE_IN_BALL_MUL_BOUND = prove
 (`!tau rho eta s k.
        s IN ring_carrier mldsa_rq /\ mldsa_norm_lt (eta + 1) s /\ k < 256
        ==> abs(mldsa_modpm
                 (coeff k (ring_mul mldsa_rq (mldsa_sample_in_ball tau rho) s))
                 8380417) <= &(tau * eta)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mldsa_norm_lt] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[MLDSA_RQ_COEFF_MUL; MLDSA_SAMPLE_IN_BALL_IN_RQ] THEN
  REWRITE_TAC[MLDSA_MODPM_REM] THEN
  MP_TAC(SPECL [`tau:num`; `shake256 rho`] MLDSA_BALL_COEFFS_SUM_ABS) THEN
  ABBREV_TAC `b = mldsa_ball_coeffs tau (shake256 rho) tau` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN
   `!i. i < 256
        ==> (coeff i (mldsa_sample_in_ball tau rho) == b i) (mod &8380417)`
  ASSUME_TAC THENL
   [EXPAND_TAC "b" THEN
    SIMP_TAC[MLDSA_SAMPLE_IN_BALL_COEFF; INT_REM_MOD_SELF];
    ALL_TAC] THEN
  ABBREV_TAC `c = mldsa_sample_in_ball tau rho` THEN
  ABBREV_TAC `s' = \j. mldsa_modpm (coeff j s) 8380417` THEN
  SUBGOAL_THEN
   `(!j. j < 256 ==> (coeff j s == s' j) (mod &8380417)) /\
    (!j. j < 256 ==> abs(s' j:int) <= &eta)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "s'" THEN REWRITE_TAC[] THEN CONJ_TAC THEN
    X_GEN_TAC `j:num` THEN DISCH_TAC THENL
     [MP_TAC(ISPECL [`coeff j s:int`; `8380417`] MLDSA_MODPM) THEN
      REWRITE_TAC[ARITH_EQ] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN
      SPEC_TAC(`&8380417:int`,`n:int`) THEN CONV_TAC INTEGER_RULE;
      FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o
                    check (free_in `eta:num` o concl)) THEN
      ASM_REWRITE_TAC[GSYM INT_OF_NUM_ADD] THEN INT_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC INT_LE_TRANS THEN
  EXISTS_TAC
   `abs(isum (0..k) (\i. b i * s'(k - i)) -
        isum (k+1..255) (\i. b i * s'(k + 256 - i)):int)` THEN
  CONJ_TAC THENL
   [W(fun (asl,w) ->
      SUBGOAL_THEN (mk_eq(rand(lhand w),
                    mk_comb(mk_comb(`mldsa_modpm`,rand(rand w)),`8380417`)))
      SUBST1_TAC) THEN
    REWRITE_TAC[MLDSA_MODPM_ABS_LE] THEN
    MATCH_MP_TAC MLDSA_MODPM_CONG THEN
    MATCH_MP_TAC(INTEGER_RULE
     `!a b c d n:int. (a == c) (mod n) /\ (b == d) (mod n)
                      ==> (a - b == c - d) (mod n)`) THEN
    CONJ_TAC THEN MATCH_MP_TAC INT_CONG_ISUM THEN
    REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC(INTEGER_RULE
     `!a b c d n:int. (a == c) (mod n) /\ (b == d) (mod n)
                      ==> (a * b == c * d) (mod n)`) THEN
    CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC INT_LE_TRANS THEN
  EXISTS_TAC `isum (0..k) (\i. abs(b i) * &eta) +
              isum (k+1..255) (\i. abs(b i) * &eta):int` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(INT_ARITH
     `abs x <= a /\ abs y <= b ==> abs(x - y:int) <= a + b`) THEN
    CONJ_TAC THEN
    W(MP_TAC o PART_MATCH (lhand o rand) ISUM_ABS o lhand o snd) THEN
    REWRITE_TAC[FINITE_NUMSEG] THEN BETA_TAC THEN
    MATCH_MP_TAC(INT_ARITH `y <= z ==> x <= y ==> x:int <= z`) THEN
    MATCH_MP_TAC ISUM_LE_NUMSEG THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN BETA_TAC THEN
    REWRITE_TAC[INT_ABS_MUL] THEN
    MATCH_MP_TAC INT_LE_LMUL THEN REWRITE_TAC[INT_ABS_POS] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[ISUM_RMUL; GSYM INT_ADD_RDISTRIB] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) ISUM_COMBINE_R o
    lhand o lhand o snd) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_MUL] THEN
  MATCH_MP_TAC INT_LE_RMUL THEN ASM_REWRITE_TAC[INT_POS]);;

let MLDSA_SKDECODE_NORM = prove
 (`!eta c b i.
        (!j. j < 256 ==> mldsa_field c b (256 * i + j) <= &(2 * eta))
        ==> mldsa_norm_lt (eta + 1)
             (mldsa_poly(\j. &eta - mldsa_field c b (256 * i + j)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mldsa_norm_lt; COEFF_MLDSA_POLY] THEN
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[MLDSA_MODPM_REM] THEN
  MATCH_MP_TAC INT_LET_TRANS THEN
  EXISTS_TAC `abs(&eta - mldsa_field c b (256 * i + j))` THEN
  REWRITE_TAC[MLDSA_MODPM_ABS_LE] THEN
  MP_TAC(SPECL [`c:num`; `b:byte list`; `256 * i + j`] MLDSA_FIELD_BOUND) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `j:num`) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_ADD; GSYM INT_OF_NUM_MUL] THEN INT_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* One signing attempt, and signing from mu, in the form of Section 5.1:     *)
(* ||w0 - c s2|| < gamma2 - beta replaces the check on LowBits(w - c s2),    *)
(* and a hint bit is set unless the centered coefficient of w0 - c s2 + c t0 *)
(* is in (-gamma2,gamma2], or is -gamma2 with the matching coefficient of w1 *)
(* zero. Every signature of the alternative attempt is that of the FIPS 204  *)
(* attempt (MLDSA_SIGN_ATTEMPT_ALT_SOUND), and the two attempts are the same *)
(* if the coefficients of s2 are in [-eta,eta] (MLDSA_SIGN_ATTEMPT_ALT), so  *)
(* signing from mu is the same if the fields of s2 in the secret key are at  *)
(* most 2 * eta (MLDSA_SIGN_MU_ALT). Without that, for a malformed key, ||c  *)
(* s2|| can exceed beta and the FIPS 204 attempt can be accepted where the   *)
(* alternative one is rejected.                                              *)
(* ------------------------------------------------------------------------- *)

let mldsa_sign_attempt_alt = new_definition
 `mldsa_sign_attempt_alt
    ((k,l,eta,tau,lam,gamma1,gamma2,omega):mldsa_params)
    (A:num->num->(1->num)->int) s1 s2 (t0:num->(1->num)->int)
    (mu:byte list) (rho'':byte list) kappa =
    let y = \i. mldsa_expand_mask gamma1 rho'' kappa i in
    let w = \i. mldsa_dot l (A i) y in
    let w1 = \n. mldsa_highbits gamma2 (coeff (n MOD 256) (w(n DIV 256))) in
    let w0 = \i. mldsa_poly(\j. mldsa_lowbits gamma2 (coeff j (w i))) in
    let ct = mldsa_h (APPEND mu (mldsa_encode
                                  (mldsa_bitlen(8380416 DIV (2 * gamma2) - 1))
                                  (256 * k) w1))
                     (lam DIV 4) in
    let c = mldsa_sample_in_ball tau ct in
    let z = \i. ring_add mldsa_rq (y i) (ring_mul mldsa_rq c (s1 i)) in
    let r0 = \i. ring_sub mldsa_rq (w0 i) (ring_mul mldsa_rq c (s2 i)) in
    let ct0 = \i. ring_mul mldsa_rq c (t0 i) in
    let h = \p. p < 256 * k /\
                let v = mldsa_modpm
                         (coeff (p MOD 256)
                           (ring_add mldsa_rq (r0(p DIV 256)) (ct0(p DIV 256))))
                         8380417 in
                ~(--(&gamma2) < v /\ v <= &gamma2 \/
                  w1 p = &0 /\ v = --(&gamma2)) in
    let beta = tau * eta in
    if mldsa_vec_norm_lt l (gamma1 - beta) z /\
       mldsa_vec_norm_lt k (gamma2 - beta) r0 /\
       mldsa_vec_norm_lt k gamma2 ct0 /\
       mldsa_hint_count h (256 * k) <= omega
    then SOME(APPEND ct
               (APPEND (mldsa_encode (1 + mldsa_bitlen(gamma1 - 1)) (256 * l)
                         (\n. &gamma1 -
                              mldsa_modpm (coeff (n MOD 256) (z(n DIV 256)))
                                          8380417))
                       (mldsa_hintbitpack k omega h)))
    else NONE`;;

let MLDSA_SIGN_ATTEMPT_ALT_CORE = prove
 (`!gamma2 beta k (w:num->(1->num)->int) c s2 t0.
        ~(gamma2 = 0) /\ (2 * gamma2) divides 8380416 /\
        4 * gamma2 <= 8380416 /\ c IN ring_carrier mldsa_rq /\
        (!i. i < k ==> w i IN ring_carrier mldsa_rq /\
                       s2 i IN ring_carrier mldsa_rq /\
                       t0 i IN ring_carrier mldsa_rq)
        ==> mldsa_vec_norm_lt k gamma2 (\i. ring_mul mldsa_rq c (t0 i)) /\
        mldsa_vec_norm_lt k (gamma2 - beta)
         (\i. ring_sub mldsa_rq
               (mldsa_poly(\j. mldsa_lowbits gamma2 (coeff j (w i))))
               (ring_mul mldsa_rq c (s2 i)))
        ==> (!i j. i < k /\ j < 256
                   ==> abs(mldsa_lowbits gamma2
                            (coeff j (ring_sub mldsa_rq (w i)
                                       (ring_mul mldsa_rq c (s2 i)))))
                       < &(gamma2 - beta)) /\
            (\p. p < 256 * k /\
                 mldsa_makehint gamma2
                  (--(coeff (p MOD 256)
                       (ring_mul mldsa_rq c (t0(p DIV 256)))))
                  (coeff (p MOD 256)
                    (ring_add mldsa_rq
                      (ring_sub mldsa_rq (w(p DIV 256))
                                (ring_mul mldsa_rq c (s2(p DIV 256))))
                      (ring_mul mldsa_rq c (t0(p DIV 256)))))) =
            (\p. p < 256 * k /\
                 let v = mldsa_modpm
                          (coeff (p MOD 256)
                            (ring_add mldsa_rq
                              (ring_sub mldsa_rq
                                (mldsa_poly(\j. mldsa_lowbits gamma2
                                                 (coeff j (w(p DIV 256)))))
                                (ring_mul mldsa_rq c (s2(p DIV 256))))
                              (ring_mul mldsa_rq c (t0(p DIV 256)))))
                          8380417 in
                 ~(--(&gamma2) < v /\ v <= &gamma2 \/
                   mldsa_highbits gamma2 (coeff (p MOD 256) (w(p DIV 256)))
                   = &0 /\ v = --(&gamma2)))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[IMP_IMP; mldsa_vec_norm_lt; mldsa_norm_lt] THEN
  BETA_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
    MP_TAC(SPECL [`gamma2:num`; `beta:num`; `(w:num->(1->num)->int) i`;
                  `ring_mul mldsa_rq c ((s2:num->(1->num)->int) i)`;
                  `ring_mul mldsa_rq c ((t0:num->(1->num)->int) i)`; `j:num`]
                 MLDSA_HINT_ALT_COEFF) THEN
    ASM_SIMP_TAC[RING_MUL];
    REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `p:num` THEN
    ASM_CASES_TAC `p < 256 * k` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `p DIV 256 < k /\ p MOD 256 < 256` STRIP_ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPECL [`gamma2:num`; `beta:num`;
                  `(w:num->(1->num)->int) (p DIV 256)`;
                  `ring_mul mldsa_rq c ((s2:num->(1->num)->int) (p DIV 256))`;
                  `ring_mul mldsa_rq c ((t0:num->(1->num)->int) (p DIV 256))`;
                  `p MOD 256`] MLDSA_HINT_ALT_COEFF) THEN
    ASM_SIMP_TAC[RING_MUL]]);;

let MLDSA_SIGN_ATTEMPT_ALT_CORE_CONV = prove
 (`!gamma2 beta k (w:num->(1->num)->int) c s2.
        ~(gamma2 = 0) /\ (2 * gamma2) divides 8380416 /\
        c IN ring_carrier mldsa_rq /\
        (!i. i < k ==> w i IN ring_carrier mldsa_rq /\
                       s2 i IN ring_carrier mldsa_rq) /\
        (!i j. i < k /\ j < 256
               ==> abs(mldsa_modpm (coeff j (ring_mul mldsa_rq c (s2 i)))
                                   8380417) <= &beta)
        ==> (!i j. i < k /\ j < 256
               ==> abs(mldsa_lowbits gamma2
                        (coeff j (ring_sub mldsa_rq (w i)
                                   (ring_mul mldsa_rq c (s2 i)))))
                   < &(gamma2 - beta))
        ==> mldsa_vec_norm_lt k (gamma2 - beta)
             (\i. ring_sub mldsa_rq
                   (mldsa_poly(\j. mldsa_lowbits gamma2 (coeff j (w i))))
                   (ring_mul mldsa_rq c (s2 i)))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[IMP_IMP; mldsa_vec_norm_lt; mldsa_norm_lt] THEN
  STRIP_TAC THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC MLDSA_LOWBITS_ALT_COEFF THEN ASM_SIMP_TAC[RING_MUL]);;

(* Instantiate a core lemma for the terms of the unfolded attempts.          *)

let MLDSA_ALT_INSTANCE_TAC th =
  W(fun (asl,w) ->
    let ct = find_term (can (term_match [] `mldsa_h x (lam DIV 4)`)) w in
    let wl = `\i. mldsa_dot l ((A:num->num->(1->num)->int) i)
                    (\i. mldsa_expand_mask gamma1 rho'' kappa i)` in
    let c = mk_comb(`mldsa_sample_in_ball tau`,ct) in
    let ith = ISPECL [`gamma2:num`; `tau * eta`; `k:num`; wl; c;
                      `s2:num->(1->num)->int`] th in
    let ith' = try ISPEC `t0:num->(1->num)->int` ith with Failure _ -> ith in
    MP_TAC(CONV_RULE(TOP_DEPTH_CONV let_CONV) (BETA_RULE ith')));;

let MLDSA_SIGN_ATTEMPT_ALT_SOUND = prove
 (`!k l eta tau lam gamma1 gamma2 omega A s1 s2 t0 mu rho'' kappa sg.
        ~(gamma2 = 0) /\ (2 * gamma2) divides 8380416 /\
        4 * gamma2 <= 8380416 /\
        (!i. i < k ==> s2 i IN ring_carrier mldsa_rq /\
                       t0 i IN ring_carrier mldsa_rq) /\
        mldsa_sign_attempt_alt (k,l,eta,tau,lam,gamma1,gamma2,omega)
         A s1 s2 t0 mu rho'' kappa = SOME sg
        ==> mldsa_sign_attempt (k,l,eta,tau,lam,gamma1,gamma2,omega)
             A s1 s2 t0 mu rho'' kappa = SOME sg`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[mldsa_sign_attempt; mldsa_sign_attempt_alt] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN BETA_TAC THEN
  MLDSA_ALT_INSTANCE_TAC MLDSA_SIGN_ATTEMPT_ALT_CORE THEN
  REWRITE_TAC[MLDSA_SAMPLE_IN_BALL_IN_RQ; MLDSA_DOT_IN_RQ] THEN
  REPEAT STRIP_TAC THEN POP_ASSUM MP_TAC THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN SIMP_TAC[]);;

let MLDSA_SIGN_ATTEMPT_ALT = prove
 (`!k l eta tau lam gamma1 gamma2 omega A s1 s2 t0 mu rho'' kappa.
        ~(gamma2 = 0) /\ (2 * gamma2) divides 8380416 /\
        4 * gamma2 <= 8380416 /\
        (!i. i < k ==> s2 i IN ring_carrier mldsa_rq /\
                       mldsa_norm_lt (eta + 1) (s2 i) /\
                       t0 i IN ring_carrier mldsa_rq)
        ==> mldsa_sign_attempt_alt (k,l,eta,tau,lam,gamma1,gamma2,omega)
             A s1 s2 t0 mu rho'' kappa =
            mldsa_sign_attempt (k,l,eta,tau,lam,gamma1,gamma2,omega)
             A s1 s2 t0 mu rho'' kappa`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[mldsa_sign_attempt; mldsa_sign_attempt_alt] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN BETA_TAC THEN
  MLDSA_ALT_INSTANCE_TAC MLDSA_SIGN_ATTEMPT_ALT_CORE_CONV THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[MLDSA_SAMPLE_IN_BALL_IN_RQ; MLDSA_DOT_IN_RQ;
                 MLDSA_SAMPLE_IN_BALL_MUL_BOUND];
    DISCH_THEN(LABEL_TAC "conv")] THEN
  MLDSA_ALT_INSTANCE_TAC MLDSA_SIGN_ATTEMPT_ALT_CORE THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[MLDSA_SAMPLE_IN_BALL_IN_RQ; MLDSA_DOT_IN_RQ];
    DISCH_THEN(LABEL_TAC "core")] THEN
  W(fun (asl,w) ->
    let cond t = rand(rator(rator t)) in
    match conjuncts(cond(lhs w)) with
      [_;ra;ta;_] ->
        ASM_CASES_TAC ta THEN ASM_REWRITE_TAC[] THEN
        ASM_CASES_TAC ra THENL
         [REMOVE_THEN "core" MP_TAC THEN ASM_REWRITE_TAC[] THEN
          STRIP_TAC THEN ASM_REWRITE_TAC[];
          REMOVE_THEN "conv" MP_TAC THEN ASM_REWRITE_TAC[] THEN
          DISCH_TAC THEN ASM_REWRITE_TAC[]]
    | _ -> failwith "MLDSA_SIGN_ATTEMPT_ALT"));;

let mldsa_sign_mu_alt = new_definition
 `mldsa_sign_mu_alt ((k,l,eta,tau,lam,gamma1,gamma2,omega):mldsa_params)
                    (sk:byte list) (mu:byte list) (rnd:byte list) =
    let c = mldsa_bitlen(2 * eta) in
    let rho = mldsa_slice 0 32 sk and key = mldsa_slice 32 32 sk in
    let s1b = mldsa_slice 128 (32 * c * l) sk
    and s2b = mldsa_slice (128 + 32 * c * l) (32 * c * k) sk
    and t0b = mldsa_slice (128 + 32 * c * (l + k)) (416 * k) sk in
    let s1 = \i. mldsa_poly(\j. &eta - mldsa_field c s1b (256 * i + j)) in
    let s2 = \i. mldsa_poly(\j. &eta - mldsa_field c s2b (256 * i + j)) in
    let t0 = \i. mldsa_poly(\j. &4096 - mldsa_field 13 t0b (256 * i + j)) in
    let rho'' = mldsa_h (APPEND key (APPEND rnd mu)) 64 in
    let att = \n. mldsa_sign_attempt_alt
                   (k,l,eta,tau,lam,gamma1,gamma2,omega)
                   (mldsa_expand_a rho) s1 s2 t0 mu rho'' (l * n) in
    if ?n. ~(att n = NONE) then att(minimal n. ~(att n = NONE)) else NONE`;;

let MLDSA_SIGN_MU_ALT = prove
 (`!k l eta tau lam gamma1 gamma2 omega sk mu rnd.
        ~(gamma2 = 0) /\ (2 * gamma2) divides 8380416 /\
        4 * gamma2 <= 8380416 /\
        (!n. n < 256 * k
             ==> mldsa_field (mldsa_bitlen(2 * eta))
                  (mldsa_slice (128 + 32 * mldsa_bitlen(2 * eta) * l)
                               (32 * mldsa_bitlen(2 * eta) * k) sk) n
                 <= &(2 * eta))
        ==> mldsa_sign_mu_alt (k,l,eta,tau,lam,gamma1,gamma2,omega)
             sk mu rnd =
            mldsa_sign_mu (k,l,eta,tau,lam,gamma1,gamma2,omega) sk mu rnd`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[mldsa_sign_mu; mldsa_sign_mu_alt] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  SUBGOAL_THEN
   `!i. i < k
        ==> !j. j < 256
                ==> mldsa_field (mldsa_bitlen(2 * eta))
                     (mldsa_slice (128 + 32 * mldsa_bitlen(2 * eta) * l)
                                  (32 * mldsa_bitlen(2 * eta) * k) sk)
                     (256 * i + j) <= &(2 * eta)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[MLDSA_SIGN_ATTEMPT_ALT; MLDSA_POLY_IN_RQ;
               MLDSA_SKDECODE_NORM]);;

(* Restore the default setting for anything loaded later.                    *)

type_invention_error := false;;
