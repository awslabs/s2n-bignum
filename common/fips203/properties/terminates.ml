(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* SampleNTT (FIPS 203 Algorithm 7) terminates for seeds of one block, so    *)
(* for all its uses in ML-KEM (seeds rho || j || i of 34 bytes): the XOF     *)
(* output has as many 12-bit fields below q = 3329 as wanted.                *)
(*                                                                           *)
(* A block of 168 output bytes holds exactly 112 fields, and field 111 of a  *)
(* block is the high 4 bits of byte 166 and the 8 bits of byte 167. By       *)
(* SHAKE128_PERIODIC_LAST, for the period p of the sponge, byte 167 of the   *)
(* output blocks (k + 1) * p - 1 is the last byte of the padding, 0x80, or   *)
(* 0x9F for a seed of 167 bytes. Field 111 of those blocks is therefore at   *)
(* most 15 + 16 * 159 = 2559 < q, and it is accepted.                        *)
(*                                                                           *)
(* This is the argument of common/fips204/properties/terminates.ml for       *)
(* RejNTTPoly of ML-DSA, with the lemmas of keccak_sponge_periodic.ml.       *)
(* SAMPLE_OK_ALL in sampling.ml proves the case of 34 bytes in another way:  *)
(* there the output block that is the padded seed again has a field 0.       *)
(* ========================================================================= *)

needs "common/fips202/properties/keccak_sponge_periodic.ml";;
needs "common/fips203/properties/sampling.ml";;

type_invention_error := true;;

let MLKEM_SAMPLE_NTT_TERMINATES = prove
 (`!b n. LENGTH b < 168
         ==> ?J. n <= CARD {j | j < J /\
                              mlkem_xof_field (mlkem_xof b) j < 3329}`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `p:num` STRIP_ASSUME_TAC o
    MATCH_MP SHAKE128_PERIODIC_LAST) THEN
  EXISTS_TAC `112 * ((n + 1) * p - 1) + 111` THEN
  MP_TAC(ISPECL
   [`\j. mlkem_xof_field (mlkem_xof b) j < 3329`;
    `\k. 112 * ((k + 1) * p - 1) + 111`; `n:num`]
   CARD_RESTRICT_INCREASING) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_SIMP_TAC[KECCAK_PERIOD_INCREASING; ARITH_RULE `0 < 112`] THEN
  X_GEN_TAC `k:num` THEN
  REWRITE_TAC[ARITH_RULE `112 * t + 111 = 2 * (56 * t + 55) + 1`;
              SAMPLE_XOF_FIELD_ODD; mlkem_xof] THEN
  REWRITE_TAC[ARITH_RULE `3 * (56 * t + 55) + 2 = 168 * t + 167`] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `shake128 b (3 * (56 * ((k + 1) * p - 1) + 55) + 1)`
    VAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_8] THEN
  COND_CASES_TAC THEN REWRITE_TAC[VAL_WORD; DIMINDEX_8] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC);;

(* Restore the default setting for anything loaded later.                    *)

type_invention_error := false;;
