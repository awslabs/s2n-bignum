(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Part 5: the rounding functions of FIPS 204 Section 2.3 and Algorithms     *)
(* 35-37 (Power2Round, Decompose, HighBits, LowBits, MakeHint, UseHint).     *)
(* ========================================================================= *)

needs "common/fips204/properties/ntt_domain.ml";;

type_invention_error := true;;

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

type_invention_error := false;;
