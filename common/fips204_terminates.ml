(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The samplers of FIPS 204 terminate for seeds of one block, so for all     *)
(* their uses in ML-DSA: RejNTTPoly (Algorithm 30, seeds rho || j || i of 34 *)
(* bytes) has as many acceptable candidates as wanted, and so do             *)
(* RejBoundedPoly (Algorithm 31, seeds rho' || nonce of 66 bytes) and        *)
(* SampleInBall (Algorithm 29, seeds c~ of lambda / 4 <= 64 bytes). By       *)
(* SHAKE128_PERIODIC_LAST and SHAKE256_PERIODIC_LAST, the last byte of the   *)
(* output blocks (k + 1) * q - 1 is 0x80 (0x9F for a SHAKE128 seed of 167    *)
(* bytes): the candidate of RejNTTPoly ending there is < 2^21 < q, the low   *)
(* nibble 0 of that byte is accepted by RejBoundedPoly, and the byte 128 is  *)
(* <= 256 - tau, so accepted by SampleInBall, for tau <= 128.                *)
(* ========================================================================= *)

needs "common/fips202_theory.ml";;
needs "common/fips204.ml";;

type_invention_error := true;;

let MLDSA_REJ_NTT_POLY_TERMINATES = prove
 (`!rho n. LENGTH rho < 168
           ==> ?J. n <= CARD {j | j < J /\
                     val(shake128 rho (3 * j)) +
                     256 * val(shake128 rho (3 * j + 1)) +
                     65536 * (val(shake128 rho (3 * j + 2)) MOD 128)
                     < 8380417}`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `q:num` STRIP_ASSUME_TAC o
    MATCH_MP SHAKE128_PERIODIC_LAST) THEN
  EXISTS_TAC `56 * ((n + 1) * q - 1) + 55` THEN
  MP_TAC(ISPECL
   [`\j. val(shake128 rho (3 * j)) + 256 * val(shake128 rho (3 * j + 1)) +
         65536 * (val(shake128 rho (3 * j + 2)) MOD 128) < 8380417`;
    `\k. 56 * ((k + 1) * q - 1) + 55`; `n:num`]
   CARD_RESTRICT_INCREASING) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_SIMP_TAC[KECCAK_PERIOD_INCREASING; ARITH_RULE `0 < 56`] THEN
  X_GEN_TAC `k:num` THEN
  REWRITE_TAC[ARITH_RULE `3 * (56 * t + 55) + 2 = 168 * t + 167`] THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY (fun t -> MP_TAC(ISPEC t VAL_BOUND))
   [`shake128 rho (3 * (56 * ((k + 1) * q - 1) + 55))`;
    `shake128 rho (3 * (56 * ((k + 1) * q - 1) + 55) + 1)`] THEN
  REWRITE_TAC[DIMINDEX_8] THEN
  COND_CASES_TAC THEN REWRITE_TAC[VAL_WORD; DIMINDEX_8] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC);;

let MLDSA_REJ_BOUNDED_POLY_TERMINATES = prove
 (`!eta rho n.
        LENGTH rho < 135
        ==> ?T. n <= CARD {t | t < T /\
                  (if eta = 2
                   then (val(shake256 rho (t DIV 2)) DIV 16 EXP (t MOD 2)) MOD
                        16 < 15
                   else (val(shake256 rho (t DIV 2)) DIV 16 EXP (t MOD 2)) MOD
                        16 < 9)}`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP SHAKE256_PERIODIC_LAST o
    MATCH_MP (ARITH_RULE `n < 135 ==> n < 136`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `q:num` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `2 * (136 * ((n + 1) * q - 1) + 135)` THEN
  MP_TAC(ISPECL
   [`\t. if eta = 2
         then (val(shake256 rho (t DIV 2)) DIV 16 EXP (t MOD 2)) MOD 16 < 15
         else (val(shake256 rho (t DIV 2)) DIV 16 EXP (t MOD 2)) MOD 16 < 9`;
    `\k. 2 * (136 * ((k + 1) * q - 1) + 135)`; `n:num`]
   CARD_RESTRICT_INCREASING) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
   [X_GEN_TAC `k:num` THEN SIMP_TAC[DIV_MULT; MOD_MULT; ARITH_EQ] THEN
    ASM_SIMP_TAC[ARITH_RULE `n < 135 ==> ~(n = 135)`] THEN
    REWRITE_TAC[VAL_WORD; DIMINDEX_8] THEN CONV_TAC NUM_REDUCE_CONV THEN
    COND_CASES_TAC THEN CONV_TAC NUM_REDUCE_CONV;
    GEN_TAC THEN REWRITE_TAC[LT_MULT_LCANCEL; ARITH_EQ] THEN
    ASM_SIMP_TAC[KECCAK_PERIOD_INCREASING; ARITH_RULE `0 < 136`]]);;

let MLDSA_SAMPLE_IN_BALL_TERMINATES = prove
 (`!tau rho N.
        LENGTH rho < 135 /\ tau <= 128
        ==> ?p. N < p /\ val(shake256 rho p) <= 256 - tau`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP SHAKE256_PERIODIC_LAST o
    MATCH_MP (ARITH_RULE `n < 135 ==> n < 136`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `q:num` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `136 * ((N + 1) * q - 1) + 135` THEN
  ASM_SIMP_TAC[ARITH_RULE `n < 135 ==> ~(n = 135)`] THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_8] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[ARITH_RULE `128 <= 256 - tau <=> tau <= 128`] THEN
  SUBGOAL_THEN `N <= (N + 1) * q - 1` MP_TAC THENL
   [SUBGOAL_THEN `N + 1 <= (N + 1) * q` MP_TAC THENL
     [GEN_REWRITE_TAC LAND_CONV [ARITH_RULE `N + 1 = (N + 1) * 1`] THEN
      REWRITE_TAC[LE_MULT_LCANCEL] THEN ASM_ARITH_TAC;
      ARITH_TAC];
    ARITH_TAC]);;

(* Restore the default setting for anything loaded later.                    *)

type_invention_error := false;;
