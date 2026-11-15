(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Properties of the Keccak permutation in common/fips202/fips202.ml:         *)
(* lanes and states correspond, and each step mapping only depends on the     *)
(* lanes with 0 <= x,y < 5.                                                   *)
(* ========================================================================= *)

needs "common/fips202/fips202.ml";;

type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Basic properties: lanes and states correspond, and each step mapping (so  *)
(* the permutation) only depends on the lanes with 0 <= x,y < 5.             *)
(* ------------------------------------------------------------------------- *)

let NSUM_DIGITS_25 = prove
 (`!b:num->num.
        (!i. b i < 2 EXP 64)
        ==> nsum (0..24) (\i. b i * 2 EXP (64 * i)) < 2 EXP 1600 /\
            !j. j < 25
                ==> (nsum (0..24) (\i. b i * 2 EXP (64 * i)) DIV
                     2 EXP (64 * j)) MOD 2 EXP 64 = b j`,
  GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[MESON[EXP_EXP; MULT_SYM]
   `b * 2 EXP (64 * i) = (2 EXP 64) EXP i * b`] THEN
  REWRITE_TAC[GSYM EXP_EXP] THEN
  SUBGOAL_THEN `0..24 = {i | i < 25}` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_NUMSEG; IN_ELIM_THM] THEN ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`2 EXP 64`; `b:num->num`; `25`] DIGITSUM_BOUND) THEN
    ASM_REWRITE_TAC[EXP_EXP] THEN CONV_TAC NUM_REDUCE_CONV;
    REPEAT STRIP_TAC THEN
    W(MP_TAC o PART_MATCH (lhand o rand) DIGITSUM_DIV_MOD o lhand o snd) THEN
    ASM_SIMP_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM]]);;

let KECCAK_LANES_STATE = prove
 (`!a x y. x < 5 /\ y < 5 ==> keccak_lanes (keccak_state a) x y = a x y`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `\i. val((a:num->num->int64) (i MOD 5) (i DIV 5))`
               NSUM_DIGITS_25) THEN
  REWRITE_TAC[REWRITE_RULE[DIMINDEX_64]
               (INST_TYPE [`:64`,`:N`] VAL_BOUND)] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `x + 5 * y`)) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(x + 5 * y) MOD 5 = x /\ (x + 5 * y) DIV 5 = y`
   (fun th -> REWRITE_TAC[th])
  THENL
   [ONCE_REWRITE_TAC[ADD_SYM] THEN
    SIMP_TAC[MOD_MULT_ADD; DIV_MULT_ADD; ARITH_EQ] THEN
    ASM_SIMP_TAC[MOD_LT; DIV_LT; ADD_CLAUSES];
    ALL_TAC] THEN
  REWRITE_TAC[keccak_lanes; keccak_state; word_subword; VAL_WORD;
              DIMINDEX_CONV `dimindex(:1600)`] THEN
  ASM_SIMP_TAC[MOD_LT] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[WORD_VAL]);;

let KECCAK_STATE_LANES = prove
 (`!s. keccak_state (keccak_lanes s) = s`,
  GEN_TAC THEN REWRITE_TAC[keccak_state; keccak_lanes] THEN
  SUBGOAL_THEN `!i. i MOD 5 + 5 * i DIV 5 = i` (fun th -> REWRITE_TAC[th])
  THENL
   [GEN_TAC THEN MP_TAC(SPECL [`i:num`; `5`] DIVISION) THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[VAL_WORD_SUBWORD; DIMINDEX_64; ARITH_RULE `MIN 64 64 = 64`] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM WORD_VAL] THEN AP_TERM_TAC THEN
  REWRITE_TAC[MESON[EXP_EXP; MULT_SYM]
   `b * 2 EXP (64 * i) = (2 EXP 64) EXP i * b`] THEN
  REWRITE_TAC[GSYM EXP_EXP] THEN
  SUBGOAL_THEN `0..24 = {i | i < 25}` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_NUMSEG; IN_ELIM_THM] THEN ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC DIGITSUM_WORKS THEN
  MP_TAC(ISPEC `s:1600 word` VAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_CONV `dimindex(:1600)`; EXP_EXP] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let KECCAK_STATE_EQ = prove
 (`!a b. (!x y. x < 5 /\ y < 5 ==> a x y = b x y)
         ==> keccak_state a = keccak_state b`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[keccak_state] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC NSUM_EQ THEN
  X_GEN_TAC `i:num` THEN REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`i MOD 5`; `i DIV 5`]) THEN
  SIMP_TAC[MOD_LT_EQ; RDIV_LT_EQ; ARITH_EQ] THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; SIMP_TAC[]]);;

let KECCAK_STEP_LOCAL_TAC =
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[keccak_theta; keccak_rho; keccak_pi; keccak_chi;
              keccak_iota] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[] THEN
  ASM_SIMP_TAC[MOD_LT_EQ; ARITH_EQ; ARITH_RULE
   `0 < 5 /\ 1 < 5 /\ 2 < 5 /\ 3 < 5 /\ 4 < 5`];;

let KECCAK_THETA_LOCAL = prove
 (`!a b. (!x y. x < 5 /\ y < 5 ==> a x y = b x y)
         ==> !x y. x < 5 /\ y < 5 ==> keccak_theta a x y = keccak_theta b x y`,
  KECCAK_STEP_LOCAL_TAC);;

let KECCAK_RHO_LOCAL = prove
 (`!a b. (!x y. x < 5 /\ y < 5 ==> a x y = b x y)
         ==> !x y. x < 5 /\ y < 5 ==> keccak_rho a x y = keccak_rho b x y`,
  KECCAK_STEP_LOCAL_TAC);;

let KECCAK_PI_LOCAL = prove
 (`!a b. (!x y. x < 5 /\ y < 5 ==> a x y = b x y)
         ==> !x y. x < 5 /\ y < 5 ==> keccak_pi a x y = keccak_pi b x y`,
  KECCAK_STEP_LOCAL_TAC);;

let KECCAK_CHI_LOCAL = prove
 (`!a b. (!x y. x < 5 /\ y < 5 ==> a x y = b x y)
         ==> !x y. x < 5 /\ y < 5 ==> keccak_chi a x y = keccak_chi b x y`,
  KECCAK_STEP_LOCAL_TAC);;

let KECCAK_IOTA_LOCAL = prove
 (`!i a b. (!x y. x < 5 /\ y < 5 ==> a x y = b x y)
           ==> !x y. x < 5 /\ y < 5
                     ==> keccak_iota i a x y = keccak_iota i b x y`,
  KECCAK_STEP_LOCAL_TAC);;

let KECCAK_RND_LOCAL = prove
 (`!i a b. (!x y. x < 5 /\ y < 5 ==> a x y = b x y)
           ==> !x y. x < 5 /\ y < 5
                     ==> keccak_rnd i a x y = keccak_rnd i b x y`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[keccak_rnd] THEN
  MATCH_MP_TAC KECCAK_IOTA_LOCAL THEN MATCH_MP_TAC KECCAK_CHI_LOCAL THEN
  MATCH_MP_TAC KECCAK_PI_LOCAL THEN MATCH_MP_TAC KECCAK_RHO_LOCAL THEN
  MATCH_MP_TAC KECCAK_THETA_LOCAL THEN ASM_REWRITE_TAC[]);;

let KECCAK_F1600_ROUND_WORDS = prove
 (`!s n. keccak_state (keccak_rounds (SUC n) (keccak_lanes s)) =
         keccak_state (keccak_rnd n
           (keccak_lanes (keccak_state (keccak_rounds n (keccak_lanes s)))))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[keccak_rounds] THEN
  MATCH_MP_TAC KECCAK_STATE_EQ THEN MATCH_MP_TAC KECCAK_RND_LOCAL THEN
  SIMP_TAC[KECCAK_LANES_STATE]);;

(* Restore the default setting for anything loaded later.                    *)

type_invention_error := false;;
