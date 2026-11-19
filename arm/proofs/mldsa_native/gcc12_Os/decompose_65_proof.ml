(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Decomposition of one coefficient into high and low parts: the proof (see  *)
(* decompose_65_spec.ml).                                                    *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/gcc12_Os/decompose_65_spec.ml";;
needs "arm/proofs/utils/mldsa_native_full.ml";;
needs "arm/proofs/utils/mldsa_native_rounding.ml";;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety. The code has no branches    *)
(* and reads no memory; the two stored values are shown equal to the         *)
(* functions of common/mldsa_native_rounding.ml by bit-blasting, with the    *)
(* coefficient as a variable (and the high part as a variable for the low    *)
(* part, see SCALAR_LANE_TAC).                                               *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_DECOMPOSE_65_GCC12_OS_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_DECOMPOSE_65_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT,
  let EXEC = MLDSA_NATIVE_DECOMPOSE_65_GCC12_OS_EXEC in
  META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `a0p:int64`; `a1p:int64`; `a:int64`; `pc:num`;
    `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              PAIRWISE; NONOVERLAPPING_CLAUSES; ALL; fst EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FULL_INIT_TAC THEN
  ARM_STEPS_TAC EXEC (1--19) THEN
  SCALAR_LANE_TAC `a1p:int64` `word_zx(a:int64):int32`
    `mld_decompose_hi_32` [DECOMPOSE_HI_32_ALT] THEN
  SCALAR_LANE_TAC `a0p:int64` `word_zx(a:int64):int32`
    `mld_decompose_lo_32` [DECOMPOSE_LO_32_ALT; mld_ct_sel] THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_DECOMPOSE_65_GCC12_OS_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_DECOMPOSE_65_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT,
  CORRECT_OF_FULL_TAC
    MLDSA_NATIVE_DECOMPOSE_65_GCC12_OS_IMAGE_SUBROUTINE_FULL);;

let MLDSA_NATIVE_DECOMPOSE_65_GCC12_OS_IMAGE_SUBROUTINE_SAFE = prove
 (MLDSA_NATIVE_DECOMPOSE_65_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT,
  SAFE_OF_FULL_TAC
    MLDSA_NATIVE_DECOMPOSE_65_GCC12_OS_IMAGE_SUBROUTINE_FULL);;
