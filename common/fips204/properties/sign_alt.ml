(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Part 6: the alternative way of checking the low bits and computing the    *)
(* hints of Section 5.1 of the Round 3 Dilithium specification, which FIPS   *)
(* 204 permits and mldsa-native uses, and its equivalence with Algorithm 7   *)
(* (MLDSA_SIGN_MU_ALT) for secret keys whose s2 fields are at most 2 *       *)
(* eta.                                                                      *)
(* ========================================================================= *)

needs "common/fips204/properties/rounding.ml";;

type_invention_error := true;;

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
                    (bound:num option)
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
    mldsa_sign_of_option
     (if ?n. mldsa_attempt_allowed bound n /\ ~(att n = NONE)
      then att(minimal n. mldsa_attempt_allowed bound n /\ ~(att n = NONE))
      else NONE)`;;

let MLDSA_SIGN_MU_ALT = prove
 (`!k l eta tau lam gamma1 gamma2 omega bound sk mu rnd.
        ~(gamma2 = 0) /\ (2 * gamma2) divides 8380416 /\
        4 * gamma2 <= 8380416 /\
        (!n. n < 256 * k
             ==> mldsa_field (mldsa_bitlen(2 * eta))
                  (mldsa_slice (128 + 32 * mldsa_bitlen(2 * eta) * l)
                               (32 * mldsa_bitlen(2 * eta) * k) sk) n
                 <= &(2 * eta))
        ==> mldsa_sign_mu_alt (k,l,eta,tau,lam,gamma1,gamma2,omega) bound
             sk mu rnd =
            mldsa_sign_mu (k,l,eta,tau,lam,gamma1,gamma2,omega) bound
             sk mu rnd`,
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

type_invention_error := false;;
