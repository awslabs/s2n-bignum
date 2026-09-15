(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Linearized ML-DSA transform specifications.                               *)
(* ========================================================================= *)

needs "common/mlkem_mldsa.ml";;

let MLDSA_BITREVERSE8_BOUND = prove
 (`!n. bitreverse8 n < 256`,
  GEN_TAC THEN
  REWRITE_TAC[bitreverse8] THEN
  MP_TAC
   (ISPEC
     `word_reversefields 1 (word n:8 word)`
     VAL_BOUND) THEN
  CONV_TAC
   (DEPTH_CONV DIMINDEX_CONV THENC NUM_REDUCE_CONV));;

let MLDSA_BITREVERSE8_INVOLUTION = prove
 (`!n. n < 256
       ==> bitreverse8 (bitreverse8 n) = n`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC
   [bitreverse8; WORD_VAL;
    WORD_REVERSEFIELDS_REVERSEFIELDS;
    VAL_WORD; DIMINDEX_8] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[MOD_LT]);;

let MLDSA_BITREVERSE8_INJECTIVE = prove
 (`!x y.
     x < 256 /\ y < 256 /\
     bitreverse8 x = bitreverse8 y
     ==> x = y`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o AP_TERM `bitreverse8`) THEN
  ASM_SIMP_TAC[MLDSA_BITREVERSE8_INVOLUTION]);;

let MLDSA_ISUM_BITREVERSE8 = prove
 (`!f:num->int.
     isum (0..255) (f o bitreverse8) =
     isum (0..255) f`,
  GEN_TAC THEN
  MATCH_MP_TAC ISUM_INJECTION THEN
  REWRITE_TAC[FINITE_NUMSEG] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[IN_NUMSEG] THEN
    REPEAT STRIP_TAC THEN
    REWRITE_TAC[LE_0] THEN
    MP_TAC(SPEC `x:num` MLDSA_BITREVERSE8_BOUND) THEN
    ARITH_TAC;
    REWRITE_TAC[IN_NUMSEG] THEN
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC MLDSA_BITREVERSE8_INJECTIVE THEN
    ASM_REWRITE_TAC[] THEN
    ASM_ARITH_TAC]);;

let MLDSA_BITREVERSE_INVERSE_NTT_REORDERED = prove
 (`!f:num->int. !k.
     mldsa_bitreverse_inverse_ntt f k =
     (&2 pow 24 *
      isum (0..255)
       (\j. f j *
            &731434 pow ((2 * bitreverse8 j + 1) * k)))
     rem &8380417`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[mldsa_bitreverse_inverse_ntt] THEN
  MATCH_MP_TAC(MESON[] `(x:int) = y ==> x rem q = y rem q`) THEN
  MATCH_MP_TAC(MESON[] `(x:int) = y ==> c * x = c * y`) THEN
  let h =
   `\j. (f:num->int) j *
        &731434 pow ((2 * bitreverse8 j + 1) * k)` in
  TRANS_TAC EQ_TRANS
   (subst [h,`H:num->int`]
     `isum (0..255) (H o bitreverse8)`) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC ISUM_EQ THEN
    REWRITE_TAC[IN_NUMSEG; o_THM] THEN
    REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC
     [MLDSA_BITREVERSE8_INVOLUTION;
      ARITH_RULE `x <= 255 ==> x < 256`];
    MATCH_ACCEPT_TAC
     (SPEC h MLDSA_ISUM_BITREVERSE8)]);;

let MLDSA_BITREVERSE_FORWARD_NTT_REORDERED_ALT = prove
 (`mldsa_bitreverse_forward_ntt f k =
   isum (0..255)
        (\j. f (bitreverse8 j) *
             ((&1753 pow
               ((2 * bitreverse8 k + 1) * bitreverse8 j))
              rem &8380417))
    rem &8380417`,
  REWRITE_TAC[MLDSA_BITREVERSE_FORWARD_NTT_ALT] THEN
  ONCE_REWRITE_TAC
   [GSYM
     (SPEC
       `(\j. (f:num->int) j *
             ((&1753 pow
               ((2 * bitreverse8 k + 1) * j))
              rem &8380417))`
       MLDSA_ISUM_BITREVERSE8)] THEN
  REWRITE_TAC[o_DEF]);;

(* Every output uses the same finite sum. Construct its expansion once and
   instantiate it before evaluating the output-specific coefficients. *)

let MLDSA_ISUM_0_255_EXPANSION =
  EXPAND_ISUM_CONV
   `isum (0..255) (f:num->int)`;;

(* Expand one concrete-index forward-transform output after reindexing its
   input by bit reversal. For example,

     MLDSA_BITREVERSE_FORWARD_NTT_REORDERED_CONV
       `mldsa_bitreverse_forward_ntt f 7`

   returns a 256-term expression over `f (bitreverse8 j)` with all concrete
   bit reversals and root powers reduced. *)

let MLDSA_BITREVERSE_FORWARD_NTT_REORDERED_CONV =
  GEN_REWRITE_CONV I
    [MLDSA_BITREVERSE_FORWARD_NTT_REORDERED_ALT] THENC
  LAND_CONV
   (GEN_REWRITE_CONV I
      [MLDSA_ISUM_0_255_EXPANSION] THENC
    DEPTH_CONV BETA_CONV THENC
    DEPTH_CONV NUM_RED_CONV THENC
    GEN_REWRITE_CONV ONCE_DEPTH_CONV
      [BITREVERSE8_CLAUSES] THENC
    DEPTH_CONV NUM_RED_CONV THENC
    ONCE_DEPTH_CONV MLDSA_ROOT_POWER_CONV THENC
    INT_REDUCE_CONV);;
