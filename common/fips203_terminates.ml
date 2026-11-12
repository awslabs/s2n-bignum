(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* SampleNTT (FIPS 203 Algorithm 7) terminates: for every seed b of at most  *)
(* 167 bytes, so in particular rho || j || i, the XOF output has as many     *)
(* 12-bit fields < q as wanted. The padded seed is a single block of         *)
(* SHAKE128, so by KECCAK_SPONGE_PERIODIC it reappears as output block       *)
(* t = (k + 1) * q - 1 for each k, and the last 12-bit field of that block   *)
(* is the top nibble of its byte 166 plus 16 times its byte 167, the last    *)
(* byte of the padding, 0x80 (or 0x9F when b has 167 bytes): at most 2559,   *)
(* so it is accepted.                                                        *)
(* ========================================================================= *)

needs "common/fips202_theory.ml";;
needs "common/fips203.ml";;

type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The 12-bit field 2 * j + 1 is in bytes 3 * j + 1 and 3 * j + 2.           *)
(* ------------------------------------------------------------------------- *)

let MLKEM_XOF_FIELD_ODD = prove
 (`!s j. mlkem_xof_field s (2 * j + 1) =
         val(s(3 * j + 1):byte) DIV 16 + 16 * val(s(3 * j + 2):byte)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mlkem_xof_field] THEN
  REWRITE_TAC[ARITH_RULE `16 = 2 EXP 4`; VAL_DIV_ALT] THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV o RAND_CONV) [val_def] THEN
  REWRITE_TAC[DIMINDEX_8] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[NUMSEG_LT] THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC(ONCE_DEPTH_CONV EXPAND_NSUM_CONV) THEN
  REWRITE_TAC[ARITH_RULE
   `12 * (2 * j + 1) + k = 8 * (3 * j + 1) + (k + 4)`] THEN
  SIMP_TAC[DIV_MULT_ADD; MOD_MULT_ADD; ARITH_EQ] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[ADD_CLAUSES; ARITH_RULE `(3 * j + 1) + 1 = 3 * j + 2`] THEN
  ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The termination of SampleNTT.                                             *)
(* ------------------------------------------------------------------------- *)

let MLKEM_SAMPLE_NTT_TERMINATES = prove
 (`!b n. LENGTH b < 168
         ==> ?J. n <= CARD {j | j < J /\
                                mlkem_xof_field (mlkem_xof b) j < 3329}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mlkem_xof] THEN
  FIRST_ASSUM(X_CHOOSE_THEN `q:num` STRIP_ASSUME_TAC o
    MATCH_MP SHAKE128_PERIODIC_LAST) THEN
  EXISTS_TAC `112 * ((n + 1) * q - 1) + 111` THEN
  MP_TAC(ISPECL [`\j. mlkem_xof_field (shake128 b) j < 3329`;
                 `\k. 112 * ((k + 1) * q - 1) + 111`; `n:num`]
                CARD_RESTRICT_INCREASING) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_SIMP_TAC[KECCAK_PERIOD_INCREASING; ARITH_RULE `0 < 112`] THEN
  X_GEN_TAC `k:num` THEN
  REWRITE_TAC[ARITH_RULE `112 * t + 111 = 2 * (56 * t + 55) + 1`;
              MLKEM_XOF_FIELD_ODD] THEN
  REWRITE_TAC[ARITH_RULE `3 * (56 * t + 55) + 2 = 168 * t + 167`;
              ARITH_RULE `3 * (56 * t + 55) + 1 = 168 * t + 166`] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `shake128 b (168 * ((k + 1) * q - 1) + 166)` VAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_8] THEN
  COND_CASES_TAC THEN REWRITE_TAC[VAL_WORD; DIMINDEX_8] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC);;

(* Restore the default setting for anything loaded later.                    *)

type_invention_error := false;;
