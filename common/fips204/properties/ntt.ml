(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Part 2: the roots zeta^(2 * BitRev8(i) + 1) of X^256 + 1, the NTT as an   *)
(* isomorphism from R_q onto Z_q^256 with pointwise operations, and the      *)
(* NTT and its inverse as explicit sums (including the forms of the          *)
(* AArch64 NTT specifications of common/mlkem_mldsa.ml).                     *)
(* ========================================================================= *)

needs "common/fips204/properties/rq_ring.ml";;

type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* zeta = 1753 has order 512 mod q and BitRev8 is a bijection of [0,256), so *)
(* the 256 values zeta^(2 * BitRev8(i) + 1) are distinct. They are roots of  *)
(* X^256 + 1, since zeta^256 = -1.                                           *)
(* ------------------------------------------------------------------------- *)

let BITREVERSE8_BOUND = prove
 (`!i. i < 256 ==> bitreverse8 i < 256`,
  SIMP_TAC[BITREVERSE8_ALT] THEN GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPEC `word_reversefields 1 (word i:8 word)` VAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_CONV `dimindex(:8)`] THEN ARITH_TAC);;

let BITREVERSE8_BITREVERSE8 = prove
 (`!i. i < 256 ==> bitreverse8(bitreverse8 i) = i`,
  CONV_TAC EXPAND_CASES_CONV THEN REWRITE_TAC[bitreverse8] THEN
  CONV_TAC(DEPTH_CONV BITMAP_CONV) THEN REWRITE_TAC[]);;

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
  MP_TAC(SPEC `j:num` BITREVERSE8_BOUND) THEN ASM_REWRITE_TAC[] THEN
  ARITH_TAC);;

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
    EXPAND_TAC "r" THEN ASM_SIMP_TAC[BITREVERSE8_BOUND] THEN ASM_ARITH_TAC;
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

type_invention_error := false;;
