(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The decomposition of common/mldsa_native_rounding.ml in the form that the *)
(* gcc 12 -O2 code computes it, for SCALAR_LANE_TAC: the products by         *)
(* constants as the code does them, a multiplication or shifts and adds, as  *)
(* in arm/proofs/utils/mldsa_native_rounding.ml (the x86 code computes them  *)
(* in the same way), and the test of the low part in mld_use_hint.           *)
(* ========================================================================= *)

needs "x86/proofs/utils/mldsa_native_scalar.ml";;
needs "common/mldsa_native_rounding.ml";;

let WORD_SHL_AS_MUL = prove
 (`!x:N word n. word_shl x n = word_mul (word(2 EXP n)) x`,
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_SHL; VAL_WORD_MUL; VAL_WORD] THEN
  CONV_TAC MOD_DOWN_CONV THEN REWRITE_TAC[]);;

(*** gamma2 = (q - 1) / 88: a0 = a + a1 * (-2 * gamma2) with MADD ***)

let DECOMPOSE_LO_88_ALT = prove
 (`!a:int32. mld_decompose_lo_88 a =
     let a0 = word_add a (word_mul (mld_decompose_hi_88 a)
                                   (word 4294776832)) in
     mld_ct_sel (word_sub a0 (word 8380417)) a0
                (mld_ct_cmask_neg (word_sub (word 4190208) a0))`,
  SUBGOAL_THEN
   `!a h:int32. word_sub a (word_mul (word_mul h (word 2)) (word 95232)) =
                word_add a (word_mul h (word 4294776832))`
   (fun th -> REWRITE_TAC[mld_decompose_lo_88; th]) THEN
  REWRITE_TAC[GSYM(WORD_REDUCE_CONV `word_neg(word 190464):int32`)] THEN
  CONV_TAC WORD_RULE);;

(*** gamma2 = (q - 1) / 32: f * 1025 = f + (f << 10) and                    ***)
(*** a0 = a + ((a1 - (a1 << 10)) << 9) = a - a1 * 2 * gamma2                ***)

let DECOMPOSE_HI_32_ALT = prove
 (`!a:int32. mld_decompose_hi_32 a =
     let f = word_ishr (word_add a (word 127)) 7 in
     word_and (word_ishr (word_add (word_add f (word_shl f 10))
                                   (word 2097152)) 22)
              (word 15)`,
  SUBGOAL_THEN
   `!f:int32. word_mul f (word 1025) = word_add f (word_shl f 10)`
   (fun th -> REWRITE_TAC[mld_decompose_hi_32; th]) THEN
  REWRITE_TAC[WORD_SHL_AS_MUL] THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC WORD_RULE);;

let DECOMPOSE_LO_32_ALT = prove
 (`!a:int32. mld_decompose_lo_32 a =
     let a0 = word_add a (word_shl (word_sub (mld_decompose_hi_32 a)
                                             (word_shl (mld_decompose_hi_32 a)
                                                       10)) 9) in
     mld_ct_sel (word_sub a0 (word 8380417)) a0
                (mld_ct_cmask_neg (word_sub (word 4190208) a0))`,
  SUBGOAL_THEN
   `!a h:int32. word_sub a (word_mul (word_mul h (word 2)) (word 261888)) =
                word_add a (word_shl (word_sub h (word_shl h 10)) 9)`
   (fun th -> REWRITE_TAC[mld_decompose_lo_32; th]) THEN
  REWRITE_TAC[WORD_SHL_AS_MUL] THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC WORD_RULE);;

(* ------------------------------------------------------------------------- *)
(* The test of the low part in mld_use_hint as the x86 code makes it: JG     *)
(* after the XOR that computes the low part w (which clears OF), taken when  *)
(* ~(ival w < &0) /\ ~(val w = 0), as a comparison.                          *)
(* ------------------------------------------------------------------------- *)

let USE_HINT_GT_COND = prove
 (`!w:int32. ~(ival w < &0) /\ ~(val w = 0) <=> &0 < ival w`,
  REWRITE_TAC[VAL_EQ_0; GSYM IVAL_EQ_0] THEN INT_ARITH_TAC);;
