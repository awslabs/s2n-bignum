(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Lemmas connecting the reduction, rounding, hint and norm-check functions  *)
(* of the specification of mldsa-native's C code (common/mldsa_native_*.ml)  *)
(* to the FIPS 204 specification in common/fips204.ml, for the inputs that   *)
(* the C contracts allow: mld_reduce32 keeps the value mod q and gives a     *)
(* result in [-6283009,6283009); on [0,q), mld_power2round, mld_decompose    *)
(* and mld_use_hint compute Power2Round, Decompose (HighBits and LowBits)    *)
(* and UseHint; mld_make_hint, on the values that signing gives it, is the   *)
(* hint criterion of mldsa_sign_attempt_alt of common/fips204_theory.ml; and *)
(* mld_poly_chknorm is the bound on the infinity norm.                       *)
(* ========================================================================= *)

needs "common/fips204_theory.ml";;
needs "common/mldsa_native_rounding.ml";;
needs "common/mldsa_native_hints.ml";;
needs "common/mldsa_native_sign.ml";;

(* ------------------------------------------------------------------------- *)
(* Exact 32-bit arithmetic. MLD_FIPS204_IVAL_TAC proves ival(e) = v for a    *)
(* word expression e that WORD_RULE shows to be iword(v), when v is in the   *)
(* range of int32 by ASM_INT_ARITH_TAC. An arithmetic shift right by n is    *)
(* the floor of the division by 2^n (MLD_FIPS204_IVAL_ISHR), and the         *)
(* constant-time selection of ct.h on a mask of ct.h is a conditional.       *)
(* ------------------------------------------------------------------------- *)

let MLD_FIPS204_IVAL_TAC =
  W(fun (asl,w) ->
     let e = rand(lhs w) and v = rhs w in
     let th = WORD_RULE(mk_eq(e,mk_comb(`iword:int->int32`,v))) in
     GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THEN
  MATCH_MP_TAC IVAL_IWORD THEN REWRITE_TAC[DIMINDEX_32] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC INT_REDUCE_CONV THEN
  ASM_INT_ARITH_TAC;;

let MLD_FIPS204_IVAL_ISHR = prove
 (`!(x:N word) n.
        &2 pow n * ival(word_ishr x n) <= ival x /\
        ival x < &2 pow n * ival(word_ishr x n) + &2 pow n`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IVAL_WORD_ISHR] THEN
  MP_TAC(SPECL [`ival(x:N word)`; `(&2:int) pow n`] INT_DIVISION) THEN
  REWRITE_TAC[INT_POW_EQ_0; INT_ABS_POW; INT_ABS_NUM] THEN
  CONV_TAC INT_REDUCE_CONV THEN
  SPEC_TAC(`ival(x:N word) div (&2:int) pow n`,`q:int`) THEN
  SPEC_TAC(`ival(x:N word) rem (&2:int) pow n`,`r:int`) THEN
  SPEC_TAC(`(&2:int) pow n`,`d:int`) THEN INT_ARITH_TAC);;

let MLD_FIPS204_CT_SEL_CMASK_NEG = prove
 (`!a b x:int32.
        mld_ct_sel a b (mld_ct_cmask_neg x) = if ival x < &0 then a else b`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mld_ct_sel; mld_ct_cmask_neg] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN BITBLAST_TAC);;

let MLD_FIPS204_IVAL_CT_ABS = prove
 (`!x:int32. --(&2147483647) <= ival x ==> ival(mld_ct_abs x) = abs(ival x)`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[mld_ct_abs] THEN
  COND_CASES_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `--(ival(x:int32))` THEN
    CONJ_TAC THENL [MLD_FIPS204_IVAL_TAC; ASM_INT_ARITH_TAC];
    ASM_INT_ARITH_TAC]);;

let MLD_FIPS204_IVAL_AND_15 = prove
 (`!x:int32. ival(word_and x (word 15)) = ival x rem &16`,
  GEN_TAC THEN MP_TAC(ISPECL [`x:int32`; `4`] VAL_WORD_AND_MASK_WORD) THEN
  CONV_TAC(LAND_CONV NUM_REDUCE_CONV) THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[ival; DIMINDEX_32] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[ARITH_RULE `n MOD 16 < 2147483648`] THEN
  COND_CASES_TAC THEN REWRITE_TAC[INT_OF_NUM_REM] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_REM] THEN
  REWRITE_TAC[INT_REM_EQ; int_congruent] THEN
  EXISTS_TAC `&268435456:int` THEN INT_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Reduction (reduce.h): for a <= INT32_MAX - 2^22, the precondition of      *)
(* mld_reduce32, its result is congruent to a mod q and in [-6283009,        *)
(* 6283009), the range MLD_REDUCE32_RANGE_MAX of reduce.h (the bound         *)
(* -6283009 is reached, for a = -2143289344). The polynomial version keeps   *)
(* the element of R_q. (mld_caddq is in mldsa_native_fips204_ntt.ml.)        *)
(* ------------------------------------------------------------------------- *)

let MLD_FIPS204_REDUCE32 = prove
 (`!a:int32.
        ival a <= &2143289343
        ==> (ival(mld_reduce32 a) == ival a) (mod &8380417) /\
            --(&6283009) <= ival(mld_reduce32 a) /\
            ival(mld_reduce32 a) < &6283009`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPEC `a:int32` IVAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_32] THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC INT_REDUCE_CONV THEN STRIP_TAC THEN
  ABBREV_TAC `t = (ival(a:int32) + &4194304) div &8388608` THEN
  SUBGOAL_THEN `--(&256) <= t /\ t:int <= &255` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "t" THEN
    REWRITE_TAC[INT_ARITH `x <= &255 <=> x < &256:int`] THEN
    SIMP_TAC[INT_LE_DIV_EQ; INT_DIV_LT_EQ; INT_ARITH `&0:int < &8388608`] THEN
    ASM_INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `ival(mld_reduce32 a) = ival(a:int32) - t * &8380417`
  SUBST1_TAC THENL
   [REWRITE_TAC[mld_reduce32; WORD_RULE
     `word_sub (a:int32) (word_mul b (word 8380417)) =
      iword(ival a - ival b * &8380417)`] THEN
    REWRITE_TAC[IVAL_WORD_ISHR; WORD_RULE
     `word_add (a:int32) (word 4194304) = iword(ival a + &4194304)`] THEN
    SUBGOAL_THEN `ival(iword(ival(a:int32) + &4194304):int32) =
                  ival a + &4194304` SUBST1_TAC THENL
     [MATCH_MP_TAC IVAL_IWORD THEN REWRITE_TAC[DIMINDEX_32] THEN
      CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC INT_REDUCE_CONV THEN
      ASM_INT_ARITH_TAC;
      CONV_TAC INT_REDUCE_CONV THEN ASM_REWRITE_TAC[]] THEN
    MATCH_MP_TAC IVAL_IWORD THEN REWRITE_TAC[DIMINDEX_32] THEN
    CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC INT_REDUCE_CONV THEN
    ASM_INT_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [SPEC_TAC(`&8380417:int`,`n:int`) THEN CONV_TAC INTEGER_RULE;
    ALL_TAC] THEN
  MP_TAC(SPECL [`ival(a:int32) + &4194304`; `&8388608:int`] INT_DIVISION) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC INT_REDUCE_CONV THEN STRIP_TAC THEN
  ASM_CASES_TAC `t = --(&256):int` THEN ASM_INT_ARITH_TAC);;

let MLD_FIPS204_POLY_REDUCE = prove
 (`!(a:num->int32) i.
        ival(a i) <= &2143289343
        ==> (ival(mld_poly_reduce a i) == ival(a i)) (mod &8380417) /\
            --(&6283009) <= ival(mld_poly_reduce a i) /\
            ival(mld_poly_reduce a i) < &6283009`,
  SIMP_TAC[mld_poly_reduce; MLD_FIPS204_REDUCE32]);;

let MLD_FIPS204_MLDSA_POLY_REDUCE = prove
 (`!a:num->int32.
        (!i. i < 256 ==> ival(a i) <= &2143289343)
        ==> mldsa_poly(\i. ival(mld_poly_reduce a i)) =
            mldsa_poly(\i. ival(a i))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mldsa_poly; FUN_EQ_THM] THEN
  X_GEN_TAC `m:1->num` THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
  REWRITE_TAC[INT_REM_EQ] THEN ASM_SIMP_TAC[MLD_FIPS204_POLY_REDUCE]);;

(* ------------------------------------------------------------------------- *)
(* Power2Round (FIPS 204 Algorithm 35): for a in [0,q), the contract of      *)
(* mld_power2round, the high part (a + 2^12 - 1) >> 13 and the low part      *)
(* a - 2^13 * a1 are the pair (r1,r0) of Power2Round(a).                     *)
(* ------------------------------------------------------------------------- *)

let MLD_FIPS204_POWER2ROUND = prove
 (`!a:int32.
        &0 <= ival a /\ ival a < &8380417
        ==> (ival(mld_power2round_hi a),ival(mld_power2round_lo a)) =
            mldsa_power2round (ival a)`,
  GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `t = (ival(a:int32) + &4095) div &8192` THEN
  MP_TAC(SPECL [`ival(a:int32) + &4095`; `&8192:int`] INT_DIVISION) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC INT_REDUCE_CONV THEN STRIP_TAC THEN
  SUBGOAL_THEN `ival(mld_power2round_hi a) = t` ASSUME_TAC THENL
   [EXPAND_TAC "t" THEN
    REWRITE_TAC[mld_power2round_hi; IVAL_WORD_ISHR; WORD_RULE
     `word_add (a:int32) (word 4095) = iword(ival a + &4095)`] THEN
    CONV_TAC INT_REDUCE_CONV THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC IVAL_IWORD THEN REWRITE_TAC[DIMINDEX_32] THEN
    CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC INT_REDUCE_CONV THEN
    ASM_INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `ival(mld_power2round_lo a) = ival(a:int32) - &8192 * t`
  SUBST1_TAC THENL
   [REWRITE_TAC[mld_power2round_lo; WORD_RULE
     `word_sub (a:int32) (word_shl b 13) = iword(ival a - &8192 * ival b)`] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IVAL_IWORD THEN
    REWRITE_TAC[DIMINDEX_32] THEN CONV_TAC NUM_REDUCE_CONV THEN
    CONV_TAC INT_REDUCE_CONV THEN ASM_INT_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[mldsa_power2round] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  SUBGOAL_THEN `ival(a:int32) rem &8380417 = ival a` SUBST1_TAC THENL
   [MATCH_MP_TAC INT_REM_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `mldsa_modpm (ival(a:int32)) 8192 = ival a - &8192 * t`
  SUBST1_TAC THENL
   [SIMP_TAC[MLDSA_MODPM_UNIQUE; ARITH_EQ] THEN CONJ_TAC THENL
     [REWRITE_TAC[INTEGER_RULE `(a - n * t:int == a) (mod n)`];
      ASM_INT_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[PAIR_EQ; INT_ARITH `a - (a - &8192 * t):int = t * &8192`] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC INT_DIV_UNIQ THEN
  EXISTS_TAC `&0:int` THEN INT_ARITH_TAC);;

let MLD_FIPS204_POLY_POWER2ROUND = prove
 (`!(a:num->int32) i.
        &0 <= ival(a i) /\ ival(a i) < &8380417
        ==> (ival(mld_poly_power2round_hi a i),
             ival(mld_poly_power2round_lo a i)) =
            mldsa_power2round (ival(a i))`,
  SIMP_TAC[mld_poly_power2round_hi; mld_poly_power2round_lo;
           MLD_FIPS204_POWER2ROUND]);;

(* ------------------------------------------------------------------------- *)
(* Decompose (FIPS 204 Algorithm 36): for r in [0,q) and g the rounding of   *)
(* r / (2 * gamma2) with halves rounded down, i.e. 2 * gamma2 * g - gamma2 < *)
(* r <= 2 * gamma2 * g + gamma2, Decompose(r) is (g,r - 2 * gamma2 * g),     *)
(* or (0,r - q) when 2 * gamma2 * g = q - 1 (MLD_FIPS204_DECOMPOSE_CORE).    *)
(* The C code computes g from f = (r + 127) >> 7 = ceil(r / 128) by a        *)
(* multiplication and a shift that give the rounding of f / (2 * gamma2 /    *)
(* 128) (MLD_FIPS204_DECOMPOSE_HI_88 and _32), maps g = (q - 1) / (2 *       *)
(* gamma2) to 0, and subtracts q from the low part when it is above          *)
(* (q - 1) / 2. So its high and low parts are HighBits and LowBits, with     *)
(* the ranges of the C contract.                                             *)
(* ------------------------------------------------------------------------- *)

let MLD_FIPS204_DECOMPOSE_CORE = prove
 (`!gamma2 x g.
        ~(gamma2 = 0) /\ (2 * gamma2) divides 8380416 /\
        &0 <= x /\ x < &8380417 /\
        &(2 * gamma2) * g - &gamma2 < x /\ x <= &(2 * gamma2) * g + &gamma2
        ==> mldsa_decompose gamma2 x =
            if &(2 * gamma2) * g = &8380416 then &0,x - &8380417
            else g,x - &(2 * gamma2) * g`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `M:num` (ASSUME_TAC o SYM) o
    REWRITE_RULE[divides]) THEN
  SUBGOAL_THEN `&2 * &gamma2 * &M:int = &8380416` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[INT_OF_NUM_MUL; MULT_ASSOC]; ALL_TAC] THEN
  UNDISCH_THEN `(2 * gamma2) * M = 8380416` (K ALL_TAC) THEN
  SUBGOAL_THEN `&0:int < &gamma2` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[INT_OF_NUM_LT; ARITH_RULE `0 < n <=> ~(n = 0)`];
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM INT_OF_NUM_MUL]) THEN
  SUBGOAL_THEN `&0:int <= g` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM INT_NOT_LT] THEN DISCH_TAC THEN
    SUBGOAL_THEN `&gamma2 * g <= &gamma2 * --(&1):int` MP_TAC THENL
     [MATCH_MP_TAC INT_LE_LMUL THEN ASM_INT_ARITH_TAC; ASM_INT_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&2 * &gamma2 * g <= &8380416:int` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM INT_NOT_LT] THEN DISCH_TAC THEN
    SUBGOAL_THEN `&M:int < g` ASSUME_TAC THENL
     [SUBGOAL_THEN `&gamma2 * &M:int < &gamma2 * g` MP_TAC THENL
       [ASM_INT_ARITH_TAC; ASM_SIMP_TAC[INT_LT_LMUL_EQ]];
      ALL_TAC] THEN
    SUBGOAL_THEN `&gamma2 * (&M + &1) <= &gamma2 * g:int` MP_TAC THENL
     [MATCH_MP_TAC INT_LE_LMUL THEN ASM_INT_ARITH_TAC; ASM_INT_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_MUL] THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[MLDSA_DECOMPOSE_UNIQUE] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_MUL; INT_MUL_RZERO; INT_ADD_LID;
              INT_ARITH `(a:int) + x - a = x`] THEN
  REWRITE_TAC[INTEGER_RULE `(x - n:int == x) (mod n)`;
              INTEGER_RULE `(x:int == x) (mod n)`] THEN
  ASM_INT_ARITH_TAC);;

let MLD_FIPS204_DECOMPOSE_LO_SEL = prove
 (`!a0:int32.
        abs(ival a0) <= &8380416
        ==> ival(mld_ct_sel (word_sub a0 (word 8380417)) a0
                  (mld_ct_cmask_neg (word_sub (word 4190208) a0))) =
            if &4190208 < ival a0 then ival a0 - &8380417 else ival a0`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[MLD_FIPS204_CT_SEL_CMASK_NEG] THEN
  SUBGOAL_THEN `ival(word_sub (word 4190208) a0:int32) = &4190208 - ival a0`
  SUBST1_TAC THENL [MLD_FIPS204_IVAL_TAC; ALL_TAC] THEN
  REWRITE_TAC[INT_ARITH `a - b < &0 <=> a < b:int`] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN MLD_FIPS204_IVAL_TAC);;

let MLD_FIPS204_DECOMPOSE_HI_88 = prove
 (`!a:int32.
        &0 <= ival a /\ ival a < &8380417
        ==> ?g. &190464 * g - &95232 < ival a /\
                ival a <= &190464 * g + &95232 /\
                ival(mld_decompose_hi_88 a) = if g = &44 then &0 else g`,
  GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[mld_decompose_hi_88] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[MLD_FIPS204_CT_SEL_CMASK_NEG] THEN
  SUBGOAL_THEN `ival(word_add a (word 127):int32) = ival a + &127`
  ASSUME_TAC THENL [MLD_FIPS204_IVAL_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`word_add a (word 127):int32`; `7`]
                MLD_FIPS204_IVAL_ISHR) THEN
  ABBREV_TAC `fw = word_ishr (word_add a (word 127)) 7:int32` THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC INT_REDUCE_CONV THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `ival(word_add (word_mul fw (word 11275)) (word 8388608):int32) =
    ival fw * &11275 + &8388608`
  ASSUME_TAC THENL [MLD_FIPS204_IVAL_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`word_add (word_mul fw (word 11275)) (word 8388608):int32`;
                 `24`] MLD_FIPS204_IVAL_ISHR) THEN
  ABBREV_TAC
   `gw = word_ishr (word_add (word_mul fw (word 11275)) (word 8388608))
                   24:int32` THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC INT_REDUCE_CONV THEN STRIP_TAC THEN
  SUBGOAL_THEN `ival(word_sub (word 43) gw:int32) = &43 - ival gw`
  SUBST1_TAC THENL [MLD_FIPS204_IVAL_TAC; ALL_TAC] THEN
  EXISTS_TAC `ival(gw:int32)` THEN
  SUBGOAL_THEN
   `&1488 * ival(gw:int32) - &744 < ival(fw:int32) /\
    ival fw <= &1488 * ival gw + &744`
  STRIP_ASSUME_TAC THENL
   [ASM_CASES_TAC `ival(gw:int32) <= &0` THEN ASM_INT_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THEN TRY ASM_INT_ARITH_TAC THEN
  ASM_CASES_TAC `ival(gw:int32) = &44` THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC INT_REDUCE_CONV THEN CONV_TAC WORD_REDUCE_CONV THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_INT_ARITH_TAC);;

let MLD_FIPS204_DECOMPOSE_88 = prove
 (`!a:int32.
        &0 <= ival a /\ ival a < &8380417
        ==> ival(mld_decompose_hi_88 a) = mldsa_highbits 95232 (ival a) /\
            ival(mld_decompose_lo_88 a) = mldsa_lowbits 95232 (ival a)`,
  GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `a:int32` MLD_FIPS204_DECOMPOSE_HI_88) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `g:int` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`95232`; `ival(a:int32)`; `g:int`]
               MLD_FIPS204_DECOMPOSE_CORE) THEN
  REWRITE_TAC[MLDSA_GAMMA2_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ANTS_TAC THENL [ASM_INT_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[mldsa_highbits; mldsa_lowbits] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[mld_decompose_lo_88] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  SUBGOAL_THEN
   `ival(word_sub a (word_mul (word_mul (mld_decompose_hi_88 a) (word 2))
                              (word 95232)):int32) =
    ival a - &190464 * ival(mld_decompose_hi_88 a)`
  ASSUME_TAC THENL
   [MLD_FIPS204_IVAL_TAC THEN COND_CASES_TAC THEN ASM_INT_ARITH_TAC;
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) MLD_FIPS204_DECOMPOSE_LO_SEL o
    lhand o rand o snd) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_INT_ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `g:int = &44` THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC INT_REDUCE_CONV THEN REWRITE_TAC[] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_INT_ARITH_TAC);;

let MLD_FIPS204_DECOMPOSE_HI_32 = prove
 (`!a:int32.
        &0 <= ival a /\ ival a < &8380417
        ==> ?g. &523776 * g - &261888 < ival a /\
                ival a <= &523776 * g + &261888 /\
                ival(mld_decompose_hi_32 a) = if g = &16 then &0 else g`,
  GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[mld_decompose_hi_32] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  SUBGOAL_THEN `ival(word_add a (word 127):int32) = ival a + &127`
  ASSUME_TAC THENL [MLD_FIPS204_IVAL_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`word_add a (word 127):int32`; `7`]
                MLD_FIPS204_IVAL_ISHR) THEN
  ABBREV_TAC `fw = word_ishr (word_add a (word 127)) 7:int32` THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC INT_REDUCE_CONV THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `ival(word_add (word_mul fw (word 1025)) (word 2097152):int32) =
    ival fw * &1025 + &2097152`
  ASSUME_TAC THENL [MLD_FIPS204_IVAL_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`word_add (word_mul fw (word 1025)) (word 2097152):int32`;
                 `22`] MLD_FIPS204_IVAL_ISHR) THEN
  ABBREV_TAC
   `gw = word_ishr (word_add (word_mul fw (word 1025)) (word 2097152))
                   22:int32` THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC INT_REDUCE_CONV THEN STRIP_TAC THEN
  EXISTS_TAC `ival(gw:int32)` THEN
  SUBGOAL_THEN
   `&4092 * ival(gw:int32) - &2046 < ival(fw:int32) /\
    ival fw <= &4092 * ival gw + &2046`
  STRIP_ASSUME_TAC THENL
   [ASM_CASES_TAC `ival(gw:int32) <= &0` THEN ASM_INT_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THEN TRY ASM_INT_ARITH_TAC THEN
  REWRITE_TAC[MLD_FIPS204_IVAL_AND_15] THEN
  ASM_CASES_TAC `ival(gw:int32) = &16` THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC INT_REDUCE_CONV THEN
  MATCH_MP_TAC INT_REM_LT THEN ASM_INT_ARITH_TAC);;

let MLD_FIPS204_DECOMPOSE_32 = prove
 (`!a:int32.
        &0 <= ival a /\ ival a < &8380417
        ==> ival(mld_decompose_hi_32 a) = mldsa_highbits 261888 (ival a) /\
            ival(mld_decompose_lo_32 a) = mldsa_lowbits 261888 (ival a)`,
  GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `a:int32` MLD_FIPS204_DECOMPOSE_HI_32) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `g:int` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`261888`; `ival(a:int32)`; `g:int`]
               MLD_FIPS204_DECOMPOSE_CORE) THEN
  REWRITE_TAC[MLDSA_GAMMA2_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ANTS_TAC THENL [ASM_INT_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[mldsa_highbits; mldsa_lowbits] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[mld_decompose_lo_32] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  SUBGOAL_THEN
   `ival(word_sub a (word_mul (word_mul (mld_decompose_hi_32 a) (word 2))
                              (word 261888)):int32) =
    ival a - &523776 * ival(mld_decompose_hi_32 a)`
  ASSUME_TAC THENL
   [MLD_FIPS204_IVAL_TAC THEN COND_CASES_TAC THEN ASM_INT_ARITH_TAC;
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) MLD_FIPS204_DECOMPOSE_LO_SEL o
    lhand o rand o snd) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_INT_ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `g:int = &16` THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC INT_REDUCE_CONV THEN REWRITE_TAC[] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_INT_ARITH_TAC);;

let MLD_FIPS204_DECOMPOSE_88_BOUNDS = prove
 (`!a:int32.
        &0 <= ival a /\ ival a < &8380417
        ==> &0 <= ival(mld_decompose_hi_88 a) /\
            ival(mld_decompose_hi_88 a) < &44 /\
            abs(ival(mld_decompose_lo_88 a)) <= &95232`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP MLD_FIPS204_DECOMPOSE_88 th]) THEN
  MP_TAC(SPECL [`95232`; `ival(a:int32)`] MLDSA_DECOMPOSE_VALID) THEN
  MP_TAC(SPECL [`95232`; `ival(a:int32)`] MLDSA_LOWBITS_BOUND) THEN
  REWRITE_TAC[MLDSA_GAMMA2_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV THEN
  INT_ARITH_TAC);;

let MLD_FIPS204_DECOMPOSE_32_BOUNDS = prove
 (`!a:int32.
        &0 <= ival a /\ ival a < &8380417
        ==> &0 <= ival(mld_decompose_hi_32 a) /\
            ival(mld_decompose_hi_32 a) < &16 /\
            abs(ival(mld_decompose_lo_32 a)) <= &261888`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP MLD_FIPS204_DECOMPOSE_32 th]) THEN
  MP_TAC(SPECL [`261888`; `ival(a:int32)`] MLDSA_DECOMPOSE_VALID) THEN
  MP_TAC(SPECL [`261888`; `ival(a:int32)`] MLDSA_LOWBITS_BOUND) THEN
  REWRITE_TAC[MLDSA_GAMMA2_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV THEN
  INT_ARITH_TAC);;

let MLD_FIPS204_POLY_DECOMPOSE_88 = prove
 (`!(a:num->int32) i.
        &0 <= ival(a i) /\ ival(a i) < &8380417
        ==> ival(mld_poly_decompose_hi_88 a i) =
            mldsa_highbits 95232 (ival(a i)) /\
            ival(mld_poly_decompose_lo_88 a i) =
            mldsa_lowbits 95232 (ival(a i))`,
  SIMP_TAC[mld_poly_decompose_hi_88; mld_poly_decompose_lo_88;
           MLD_FIPS204_DECOMPOSE_88]);;

let MLD_FIPS204_POLY_DECOMPOSE_32 = prove
 (`!(a:num->int32) i.
        &0 <= ival(a i) /\ ival(a i) < &8380417
        ==> ival(mld_poly_decompose_hi_32 a i) =
            mldsa_highbits 261888 (ival(a i)) /\
            ival(mld_poly_decompose_lo_32 a i) =
            mldsa_lowbits 261888 (ival(a i))`,
  SIMP_TAC[mld_poly_decompose_hi_32; mld_poly_decompose_lo_32;
           MLD_FIPS204_DECOMPOSE_32]);;

(* ------------------------------------------------------------------------- *)
(* UseHint (FIPS 204 Algorithm 40): for a in [0,q), mld_use_hint with any    *)
(* nonzero hint word is UseHint with h true, and with the zero word UseHint  *)
(* with h false; its result is in [0,(q - 1) / (2 * gamma2)).                *)
(* ------------------------------------------------------------------------- *)

let MLD_FIPS204_REM_TAC =
  W(fun (asl,w) ->
     let e = lhand(rhs w) in
     MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC e THEN CONJ_TAC THENL
      [MLD_FIPS204_IVAL_TAC;
       CONV_TAC SYM_CONV THEN MATCH_MP_TAC INT_REM_LT THEN
       ASM_INT_ARITH_TAC]);;

let MLD_FIPS204_USE_HINT_88 = prove
 (`!a h:int32.
        &0 <= ival a /\ ival a < &8380417
        ==> ival(mld_use_hint_88 a h) =
            mldsa_usehint 95232 (~(h = word 0)) (ival a)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL [`95232`; `ival(a:int32)`] MLDSA_DECOMPOSE_VALID) THEN
  REWRITE_TAC[mldsa_usehint; mld_use_hint_88; MLDSA_GAMMA2_CLAUSES] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  FIRST_ASSUM(fun th ->
    REWRITE_TAC[GSYM(MATCH_MP MLD_FIPS204_DECOMPOSE_88 th)]) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SPEC_TAC(`mld_decompose_lo_88 a`,`a0:int32`) THEN
  SPEC_TAC(`mld_decompose_hi_88 a`,`a1:int32`) THEN
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ASM_CASES_TAC `h:int32 = word 0` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `&0 < ival(a0:int32)` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM IVAL_EQ] THEN CONV_TAC WORD_REDUCE_CONV THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC INT_REDUCE_CONV THEN
  MLD_FIPS204_REM_TAC);;

let MLD_FIPS204_USE_HINT_32 = prove
 (`!a h:int32.
        &0 <= ival a /\ ival a < &8380417
        ==> ival(mld_use_hint_32 a h) =
            mldsa_usehint 261888 (~(h = word 0)) (ival a)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL [`261888`; `ival(a:int32)`] MLDSA_DECOMPOSE_VALID) THEN
  REWRITE_TAC[mldsa_usehint; mld_use_hint_32; MLDSA_GAMMA2_CLAUSES] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  FIRST_ASSUM(fun th ->
    REWRITE_TAC[GSYM(MATCH_MP MLD_FIPS204_DECOMPOSE_32 th)]) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SPEC_TAC(`mld_decompose_lo_32 a`,`a0:int32`) THEN
  SPEC_TAC(`mld_decompose_hi_32 a`,`a1:int32`) THEN
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ASM_CASES_TAC `h:int32 = word 0` THEN ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[MLD_FIPS204_IVAL_AND_15] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN MLD_FIPS204_IVAL_TAC);;

let MLD_FIPS204_USE_HINT_88_BOUNDS = prove
 (`!a h:int32.
        &0 <= ival a /\ ival a < &8380417
        ==> &0 <= ival(mld_use_hint_88 a h) /\
            ival(mld_use_hint_88 a h) < &44`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP MLD_FIPS204_USE_HINT_88 th]) THEN
  MP_TAC(SPECL [`95232`; `ival(a:int32)`] MLDSA_DECOMPOSE_VALID) THEN
  REWRITE_TAC[mldsa_usehint; MLDSA_GAMMA2_CLAUSES] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  REPEAT COND_CASES_TAC THEN
  REWRITE_TAC[INT_REM_POS_EQ; INT_LT_REM_EQ] THEN INT_ARITH_TAC);;

let MLD_FIPS204_USE_HINT_32_BOUNDS = prove
 (`!a h:int32.
        &0 <= ival a /\ ival a < &8380417
        ==> &0 <= ival(mld_use_hint_32 a h) /\
            ival(mld_use_hint_32 a h) < &16`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP MLD_FIPS204_USE_HINT_32 th]) THEN
  MP_TAC(SPECL [`261888`; `ival(a:int32)`] MLDSA_DECOMPOSE_VALID) THEN
  REWRITE_TAC[mldsa_usehint; MLDSA_GAMMA2_CLAUSES] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  REPEAT COND_CASES_TAC THEN
  REWRITE_TAC[INT_REM_POS_EQ; INT_LT_REM_EQ] THEN INT_ARITH_TAC);;

let MLD_FIPS204_POLY_USE_HINT_88 = prove
 (`!(a:num->int32) h i.
        &0 <= ival(a i) /\ ival(a i) < &8380417
        ==> ival(mld_poly_use_hint_88 a h i) =
            mldsa_usehint 95232 (~(h i = word 0)) (ival(a i))`,
  SIMP_TAC[mld_poly_use_hint_88; MLD_FIPS204_USE_HINT_88]);;

let MLD_FIPS204_POLY_USE_HINT_32 = prove
 (`!(a:num->int32) h i.
        &0 <= ival(a i) /\ ival(a i) < &8380417
        ==> ival(mld_poly_use_hint_32 a h i) =
            mldsa_usehint 261888 (~(h i = word 0)) (ival(a i))`,
  SIMP_TAC[mld_poly_use_hint_32; MLD_FIPS204_USE_HINT_32]);;

(* ------------------------------------------------------------------------- *)
(* MakeHint in the form of Section 5.1 of the Round 3 Dilithium paper, the   *)
(* criterion of mldsa_sign_attempt_alt: mld_make_hint a0 a1 holds unless a0  *)
(* is in (-gamma2,gamma2], or is -gamma2 with a1 = 0. When a0 is congruent   *)
(* to v mod q and in [-(q - 1) / 2,(q - 1) / 2], v mod+- q is a0, so the     *)
(* hints of a vector are those of the centered values v. In signing, a0 is   *)
(* the sum w0 - c s2 + c t0 (mld_sign_hint_x) of two polynomials that have   *)
(* passed the norm checks, so with coefficients below gamma2 in absolute     *)
(* value, and a1 is unpacked from the first k polynomials of the packed high *)
(* parts (mld_sign_hint_w1). So the hints are those of                       *)
(* mldsa_sign_attempt_alt for the elements r0 and ct0 of R_q that the two    *)
(* polynomials represent and the unpacked high parts w1.                     *)
(* ------------------------------------------------------------------------- *)

let MLD_FIPS204_MAKE_HINT_88 = prove
 (`!a0 a1:int32.
        mld_make_hint_88 a0 a1 <=>
        ~(--(&95232) < ival a0 /\ ival a0 <= &95232 \/
          ival a1 = &0 /\ ival a0 = --(&95232))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mld_make_hint_88; GSYM IVAL_EQ] THEN
  CONV_TAC WORD_REDUCE_CONV THEN INT_ARITH_TAC);;

let MLD_FIPS204_MAKE_HINT_32 = prove
 (`!a0 a1:int32.
        mld_make_hint_32 a0 a1 <=>
        ~(--(&261888) < ival a0 /\ ival a0 <= &261888 \/
          ival a1 = &0 /\ ival a0 = --(&261888))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mld_make_hint_32; GSYM IVAL_EQ] THEN
  CONV_TAC WORD_REDUCE_CONV THEN INT_ARITH_TAC);;

let MLD_FIPS204_MODPM_IVAL = prove
 (`!(x:int32) v.
        (ival x == v) (mod &8380417) /\ abs(ival x) <= &4190208
        ==> mldsa_modpm v 8380417 = ival x`,
  REPEAT STRIP_TAC THEN SIMP_TAC[MLDSA_MODPM_UNIQUE; ARITH_EQ] THEN
  ASM_REWRITE_TAC[] THEN ASM_INT_ARITH_TAC);;

let MLD_FIPS204_POLYVEC_MAKE_HINT_TAC defs =
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "in") (LABEL_TAC "out")) THEN
  REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `p:num` THEN REWRITE_TAC defs THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ASM_CASES_TAC `p < 256 * k` THEN ASM_REWRITE_TAC[] THENL
   [REMOVE_THEN "in" (MP_TAC o SPEC `p:num`) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`(x:num->int32) p`; `(v:num->int) p`]
                 MLD_FIPS204_MODPM_IVAL) THEN
    ASM_SIMP_TAC[];
    REMOVE_THEN "out" (MP_TAC o SPEC `p:num`) THEN
    ASM_REWRITE_TAC[GSYM NOT_LT] THEN DISCH_THEN SUBST1_TAC THEN
    CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC INT_REDUCE_CONV];;

let MLD_FIPS204_POLYVEC_MAKE_HINT_88 = prove
 (`!k (x:num->int32) (b:num->byte) (v:num->int) (w1:num->int).
        (!p. p < 256 * k
             ==> (ival(x p) == v p) (mod &8380417) /\
                 abs(ival(x p)) <= &4190208 /\
                 ival(mld_polyvec_unpack 192 mld_polyw1_unpack_88 b p) =
                 w1 p) /\
        (!p. 256 * k <= p ==> x p = word 0)
        ==> mld_polyvec_make_hint_88 x b =
            \p. p < 256 * k /\
                let v' = mldsa_modpm (v p) 8380417 in
                ~(--(&95232) < v' /\ v' <= &95232 \/
                  w1 p = &0 /\ v' = --(&95232))`,
  MLD_FIPS204_POLYVEC_MAKE_HINT_TAC
   [mld_polyvec_make_hint_88; MLD_FIPS204_MAKE_HINT_88]);;

let MLD_FIPS204_POLYVEC_MAKE_HINT_32 = prove
 (`!k (x:num->int32) (b:num->byte) (v:num->int) (w1:num->int).
        (!p. p < 256 * k
             ==> (ival(x p) == v p) (mod &8380417) /\
                 abs(ival(x p)) <= &4190208 /\
                 ival(mld_polyvec_unpack 128 mld_polyw1_unpack_32 b p) =
                 w1 p) /\
        (!p. 256 * k <= p ==> x p = word 0)
        ==> mld_polyvec_make_hint_32 x b =
            \p. p < 256 * k /\
                let v' = mldsa_modpm (v p) 8380417 in
                ~(--(&261888) < v' /\ v' <= &261888 \/
                  w1 p = &0 /\ v' = --(&261888))`,
  MLD_FIPS204_POLYVEC_MAKE_HINT_TAC
   [mld_polyvec_make_hint_32; MLD_FIPS204_MAKE_HINT_32]);;

let MLD_FIPS204_POLYW1_UNPACK_88_LOCAL = prove
 (`!(b:num->byte) b' i.
        i < 256 /\ (!t. t < 192 ==> b t = b' t)
        ==> mld_polyw1_unpack_88 b i = mld_polyw1_unpack_88 b' i`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mld_polyw1_unpack_88] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  SUBGOAL_THEN `!m. m < 3 ==> (b:num->byte)(3 * i DIV 4 + m) =
                              b'(3 * i DIV 4 + m)` MP_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    SUBGOAL_THEN `i DIV 4 < 64` MP_TAC THENL
     [ASM_SIMP_TAC[RDIV_LT_EQ; ARITH_EQ] THEN SIMPLE_ARITH_TAC;
      SIMPLE_ARITH_TAC];
    CONV_TAC(LAND_CONV EXPAND_CASES_CONV) THEN
    CONV_TAC(LAND_CONV NUM_REDUCE_CONV) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES]]);;

let MLD_FIPS204_POLYW1_UNPACK_32_LOCAL = prove
 (`!(b:num->byte) b' i.
        i < 256 /\ (!t. t < 128 ==> b t = b' t)
        ==> mld_polyw1_unpack_32 b i = mld_polyw1_unpack_32 b' i`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mld_polyw1_unpack_32] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  SUBGOAL_THEN `(b:num->byte)(i DIV 2) = b'(i DIV 2)`
   (fun th -> REWRITE_TAC[th]) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_SIMP_TAC[RDIV_LT_EQ; ARITH_EQ] THEN SIMPLE_ARITH_TAC);;

let MLD_FIPS204_SIGN_HINT_W1_TAC localth =
  REPEAT STRIP_TAC THEN REWRITE_TAC[mld_polyvec_unpack; mld_polyvec] THEN
  MATCH_MP_TAC localth THEN
  REWRITE_TAC[mld_sign_hint_w1; MOD_LT_EQ; ARITH_EQ] THEN
  X_GEN_TAC `t:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `p DIV 256 < k` ASSUME_TAC THENL
   [ASM_SIMP_TAC[RDIV_LT_EQ; ARITH_EQ] THEN SIMPLE_ARITH_TAC;
    COND_CASES_TAC THEN REWRITE_TAC[] THEN
    REPEAT(POP_ASSUM MP_TAC) THEN ARITH_TAC];;

let MLD_FIPS204_SIGN_HINT_W1_88 = prove
 (`!k (w1b:num->byte) p.
        p < 256 * k
        ==> mld_polyvec_unpack 192 mld_polyw1_unpack_88
             (mld_sign_hint_w1 k 192 w1b) p =
            mld_polyvec_unpack 192 mld_polyw1_unpack_88 w1b p`,
  MLD_FIPS204_SIGN_HINT_W1_TAC MLD_FIPS204_POLYW1_UNPACK_88_LOCAL);;

let MLD_FIPS204_SIGN_HINT_W1_32 = prove
 (`!k (w1b:num->byte) p.
        p < 256 * k
        ==> mld_polyvec_unpack 128 mld_polyw1_unpack_32
             (mld_sign_hint_w1 k 128 w1b) p =
            mld_polyvec_unpack 128 mld_polyw1_unpack_32 w1b p`,
  MLD_FIPS204_SIGN_HINT_W1_TAC MLD_FIPS204_POLYW1_UNPACK_32_LOCAL);;

let MLD_FIPS204_SIGN_HINT_TAC polyvecth w1th =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC polyvecth THEN
  ASM_SIMP_TAC[mld_sign_hint_x; mld_poly_add; GSYM NOT_LT; w1th] THEN
  X_GEN_TAC `p:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `p DIV 256 < k /\ p MOD 256 < 256` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[RDIV_LT_EQ; MOD_LT_EQ; ARITH_EQ] THEN SIMPLE_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[MLDSA_RQ_COEFF_ADD] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`p DIV 256`; `p MOD 256`]) THEN
  ASM_REWRITE_TAC[] THEN
  SPEC_TAC(`mld_sign_r0 dlo w s2hat cphat (p DIV 256) (p MOD 256)`,
           `x:int32`) THEN
  SPEC_TAC(`mld_sign_ct0 t0hat cphat (p DIV 256) (p MOD 256)`,`y:int32`) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `ival(word_add x y:int32) = ival x + ival y` SUBST1_TAC THENL
   [MLD_FIPS204_IVAL_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [ALL_TAC; ASM_INT_ARITH_TAC] THEN
  REWRITE_TAC[GSYM INT_REM_EQ; INT_REM_REM] THEN REWRITE_TAC[INT_REM_EQ] THEN
  MATCH_MP_TAC INT_CONG_ADD THEN ASM_REWRITE_TAC[];;

let MLD_FIPS204_SIGN_HINT_88 = prove
 (`!k dlo (w:num->int32) s2hat t0hat cphat (w1b:num->byte)
    (r0:num->(1->num)->int) (ct0:num->(1->num)->int) (w1:num->int).
        (!j. j < k ==> r0 j IN ring_carrier mldsa_rq /\
                       ct0 j IN ring_carrier mldsa_rq) /\
        (!j i. j < k /\ i < 256
               ==> (ival(mld_sign_r0 dlo w s2hat cphat j i) == coeff i (r0 j))
                   (mod &8380417) /\
                   (ival(mld_sign_ct0 t0hat cphat j i) == coeff i (ct0 j))
                   (mod &8380417) /\
                   abs(ival(mld_sign_r0 dlo w s2hat cphat j i)) < &95232 /\
                   abs(ival(mld_sign_ct0 t0hat cphat j i)) < &95232) /\
        (!p. p < 256 * k
             ==> ival(mld_polyvec_unpack 192 mld_polyw1_unpack_88 w1b p) =
                 w1 p)
        ==> mld_polyvec_make_hint_88
             (mld_sign_hint_x k dlo w s2hat t0hat cphat)
             (mld_sign_hint_w1 k 192 w1b) =
            \p. p < 256 * k /\
                let v = mldsa_modpm
                         (coeff (p MOD 256)
                           (ring_add mldsa_rq (r0(p DIV 256)) (ct0(p DIV 256))))
                         8380417 in
                ~(--(&95232) < v /\ v <= &95232 \/
                  w1 p = &0 /\ v = --(&95232))`,
  MLD_FIPS204_SIGN_HINT_TAC
   MLD_FIPS204_POLYVEC_MAKE_HINT_88 MLD_FIPS204_SIGN_HINT_W1_88);;

let MLD_FIPS204_SIGN_HINT_32 = prove
 (`!k dlo (w:num->int32) s2hat t0hat cphat (w1b:num->byte)
    (r0:num->(1->num)->int) (ct0:num->(1->num)->int) (w1:num->int).
        (!j. j < k ==> r0 j IN ring_carrier mldsa_rq /\
                       ct0 j IN ring_carrier mldsa_rq) /\
        (!j i. j < k /\ i < 256
               ==> (ival(mld_sign_r0 dlo w s2hat cphat j i) == coeff i (r0 j))
                   (mod &8380417) /\
                   (ival(mld_sign_ct0 t0hat cphat j i) == coeff i (ct0 j))
                   (mod &8380417) /\
                   abs(ival(mld_sign_r0 dlo w s2hat cphat j i)) < &261888 /\
                   abs(ival(mld_sign_ct0 t0hat cphat j i)) < &261888) /\
        (!p. p < 256 * k
             ==> ival(mld_polyvec_unpack 128 mld_polyw1_unpack_32 w1b p) =
                 w1 p)
        ==> mld_polyvec_make_hint_32
             (mld_sign_hint_x k dlo w s2hat t0hat cphat)
             (mld_sign_hint_w1 k 128 w1b) =
            \p. p < 256 * k /\
                let v = mldsa_modpm
                         (coeff (p MOD 256)
                           (ring_add mldsa_rq (r0(p DIV 256)) (ct0(p DIV 256))))
                         8380417 in
                ~(--(&261888) < v /\ v <= &261888 \/
                  w1 p = &0 /\ v = --(&261888))`,
  MLD_FIPS204_SIGN_HINT_TAC
   MLD_FIPS204_POLYVEC_MAKE_HINT_32 MLD_FIPS204_SIGN_HINT_W1_32);;

(* ------------------------------------------------------------------------- *)
(* The norm check (poly.c): for coefficients in [-6283009,6283009), as       *)
(* mld_reduce32 gives them and the contract of mld_poly_chknorm requires,    *)
(* and a bound B <= q - 6283009 = 2097408, also as in the contract (gamma1 - *)
(* beta, gamma2 - beta, gamma2 and eta + 1 are below it for all parameter    *)
(* sets), mld_poly_chknorm a B is zero iff all |a i| < B, and that is the    *)
(* bound ||a||_inf < B of FIPS 204 on the element of R_q, since the centered *)
(* remainder of a coefficient outside [-(q - 1) / 2,(q - 1) / 2] is then at  *)
(* least B in absolute value. Likewise for a vector of n polynomials.        *)
(* ------------------------------------------------------------------------- *)

let MLD_FIPS204_POLY_CHKNORM_ABS = prove
 (`!(a:num->int32) B.
        (!i. i < 256
             ==> --(&6283009) <= ival(a i) /\ ival(a i) < &6283009) /\
        B <= 2097408
        ==> (mld_poly_chknorm a (word B) = word 0 <=>
             !i. i < 256 ==> abs(ival(a i)) < &B)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&B:int <= &2097408` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[INT_OF_NUM_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `ival(word B:int32) = &B` ASSUME_TAC THENL
   [MP_TAC(ISPEC `word B:int32` IVAL_EQ_VAL) THEN
    REWRITE_TAC[VAL_WORD; DIMINDEX_32] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_SIMP_TAC[MOD_LT; ARITH_RULE
     `B <= 2097408 ==> B < 4294967296 /\ B < 2147483648`];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. i < 256
        ==> (ival(word_sub (word_sub (word B) (word 1))
                           (mld_ct_abs((a:num->int32) i))) < &0 <=>
             ~(abs(ival(a i)) < &B))`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `ival(mld_ct_abs((a:num->int32) i)) = abs(ival(a i))`
    ASSUME_TAC THENL
     [MATCH_MP_TAC MLD_FIPS204_IVAL_CT_ABS THEN ASM_INT_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `ival(word_sub (word_sub (word B) (word 1))
                    (mld_ct_abs((a:num->int32) i))) =
      ival(word B:int32) - &1 - ival(mld_ct_abs(a i))`
    SUBST1_TAC THENL [MLD_FIPS204_IVAL_TAC; ASM_INT_ARITH_TAC];
    ALL_TAC] THEN
  ASM_SIMP_TAC[mld_poly_chknorm] THEN
  COND_CASES_TAC THEN CONV_TAC WORD_REDUCE_CONV THEN ASM_MESON_TAC[]);;

let MLD_FIPS204_MODPM_ABS_LT = prove
 (`!x B. --(&6283009) <= x /\ x < &6283009 /\ B <= 2097408
         ==> (abs(mldsa_modpm x 8380417) < &B <=> abs x < &B)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&B:int <= &2097408` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[INT_OF_NUM_LE]; ALL_TAC] THEN
  SUBGOAL_THEN
   `mldsa_modpm x 8380417 =
    if x < --(&4190208) then x + &8380417
    else if &4190208 < x then x - &8380417 else x`
  SUBST1_TAC THENL
   [SIMP_TAC[MLDSA_MODPM_UNIQUE; ARITH_EQ] THEN
    REPEAT COND_CASES_TAC THEN
    REWRITE_TAC[INTEGER_RULE `(x + n:int == x) (mod n)`;
                INTEGER_RULE `(x - n:int == x) (mod n)`;
                INTEGER_RULE `(x:int == x) (mod n)`] THEN
    ASM_INT_ARITH_TAC;
    REPEAT COND_CASES_TAC THEN ASM_INT_ARITH_TAC]);;

let MLD_FIPS204_POLY_CHKNORM = prove
 (`!(a:num->int32) B.
        (!i. i < 256
             ==> --(&6283009) <= ival(a i) /\ ival(a i) < &6283009) /\
        B <= 2097408
        ==> (mld_poly_chknorm a (word B) = word 0 <=>
             mldsa_norm_lt B (mldsa_poly(\i. ival(a i))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_SIMP_TAC[MLD_FIPS204_POLY_CHKNORM_ABS] THEN
  REWRITE_TAC[mldsa_norm_lt; COEFF_MLDSA_POLY] THEN
  SIMP_TAC[MLDSA_MODPM_REM] THEN
  ASM_SIMP_TAC[MLD_FIPS204_MODPM_ABS_LT]);;

let MLD_FIPS204_POLYVEC_CHKNORM = prove
 (`!n (x:num->int32) B.
        (!i. i < 256 * n
             ==> --(&6283009) <= ival(x i) /\ ival(x i) < &6283009) /\
        B <= 2097408
        ==> (mld_polyvec_chknorm n x (word B) = word 0 <=>
             mldsa_vec_norm_lt n B
              (\j. mldsa_poly(\i. ival(x(256 * j + i)))))`,
  INDUCT_TAC THEN
  REWRITE_TAC[mld_polyvec_chknorm; mldsa_vec_norm_lt; LT] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[WORD_OR_EQ_0; TAUT `(p \/ q ==> r) <=> (p ==> r) /\ (q ==> r)`;
              FORALL_AND_THM; FORALL_UNWIND_THM2] THEN
  MATCH_MP_TAC(TAUT `(a <=> d) /\ (b <=> c) ==> (a /\ b <=> c /\ d)`) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM mldsa_vec_norm_lt] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    SIMPLE_ARITH_TAC;
    REWRITE_TAC[mld_poly_of] THEN BETA_TAC THEN
    MATCH_MP_TAC MLD_FIPS204_POLY_CHKNORM THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    SIMPLE_ARITH_TAC]);;
