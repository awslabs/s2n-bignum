(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Copying rho, K and tr to the start of a secret key: the proof (see        *)
(* pack_sk_rho_key_tr_44_spec.ml).                                           *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/gcc12_O2/pack_sk_rho_key_tr_44_spec.ml";;
needs "arm/proofs/utils/mldsa_native_hints.ml";;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety: the 128 bytes as eight      *)
(* 128-bit words, loaded and stored.                                         *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_PACK_SK_RHO_KEY_TR_44_GCC12_O2_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_PACK_SK_RHO_KEY_TR_44_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT,
  let EXEC = MLDSA_NATIVE_PACK_SK_RHO_KEY_TR_44_GCC12_O2_EXEC in
  META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `sk:int64`; `rho:int64`; `tr:int64`;
    `key:int64`; `r:num->byte`; `t:num->byte`; `k:num->byte`;
    `pc:num`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; ALL; fst EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FULL_INIT_TAC THEN
  GLUE_LOAD128_TAC `rho:int64` [0; 16] THEN
  GLUE_LOAD128_TAC `key:int64` [0; 16] THEN
  GLUE_LOAD128_TAC `tr:int64` [0; 16; 32; 48] THEN
  ARM_STEPS_TAC EXEC (1--10) THEN GLUE_STORE_TAC `sk:int64` THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  W(fun (_,w) -> if is_exists w then DISCHARGE_SAFETY_PROPERTY_TAC
                 else GLUE_BYTES_FINAL_TAC));;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_PACK_SK_RHO_KEY_TR_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_PACK_SK_RHO_KEY_TR_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  CORRECT_OF_FULL_TAC
    MLDSA_NATIVE_PACK_SK_RHO_KEY_TR_44_GCC12_O2_IMAGE_SUBROUTINE_FULL);;

let MLDSA_NATIVE_PACK_SK_RHO_KEY_TR_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE = prove
 (MLDSA_NATIVE_PACK_SK_RHO_KEY_TR_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  SAFE_OF_FULL_TAC
    MLDSA_NATIVE_PACK_SK_RHO_KEY_TR_44_GCC12_O2_IMAGE_SUBROUTINE_FULL);;
