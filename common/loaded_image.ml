(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Addresses in the image of a binary loaded at a multiple of 4096, as the   *)
(* dynamic loader loads a shared object: lemmas that do not depend on the    *)
(* instruction set, for the tools of arm/proofs/utils/loaded_image.ml.       *)
(* Generalized from common/fips203/properties/mlkem_native_image.ml of the   *)
(* mlkem-native proofs.                                                      *)
(* ========================================================================= *)

let ALIGNED_4096_WORD_AND = prove
 (`!x:int64. aligned 4096 x <=> word_and x (word 4095) = word 0`,
  GEN_TAC THEN REWRITE_TAC[aligned; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC(ONCE_DEPTH_CONV DIVIDES_CONV) THEN REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`x:int64`; `12`] (CONJUNCT1 WORD_AND_MASK_WORD)) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[DIVIDES_MOD; GSYM VAL_EQ_0; VAL_WORD; DIMINDEX_64] THEN
  SIMP_TAC[MOD_LT; ARITH_RULE `x MOD 4096 < 4096`; ARITH_RULE
    `x < 4096 ==> x < 2 EXP 64`]);;

(*** The page and the offset within it computed by ADRP and ADD or LDR ***)

let PAGE_ADD_ALIGNED = prove
 (`!x y:int64.
        word_and x (word 4095) = word 0
        ==> word_and (word_add x y) (word 0xFFFFFFFFFFFFF000) =
            word_add x (word_and y (word 0xFFFFFFFFFFFFF000)) /\
            word_subword (word_add x y) (0,12):(12)word =
            word_subword y (0,12) /\
            word_subword (word_add x y) (4,8):(12)word =
            word_subword y (4,8)`,
  BITBLAST_TAC);;
