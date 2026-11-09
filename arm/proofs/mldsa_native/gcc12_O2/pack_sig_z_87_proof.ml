(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Packing polynomial i of z into a signature: the proof (see                *)
(* pack_sig_z_87_spec.ml).                                                   *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/gcc12_O2/pack_sig_z_87_spec.ml";;
needs "arm/proofs/utils/mldsa_native_hints.ml";;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety: the address of the output,  *)
(* then the tail call of mldsa87_polyz_pack.                                 *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_PACK_SIG_Z_87_GCC12_O2_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_PACK_SIG_Z_87_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT,
  let EXEC = MLDSA_NATIVE_PACK_SIG_Z_87_GCC12_O2_EXEC in
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_POLYZ_PACK_87_GCC12_O2_IMAGE_SUBROUTINE_FULL "H_PACK" THEN
  META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `sig:int64`; `zi:int64`; `x:num->int32`;
    `i:num`; `pc:num`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; ALL; fst EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FULL_INIT_TAC THEN ARM_STEPS_TAC EXEC (1--5) THEN
  GLUE_REG_TAC `X0` `word_add sig (word(64 + 640 * i)):int64` THEN
  FULL_CALL_TAC mldsa_native_libmldsa_gcc12_O2_mc EXEC "H_PACK"
   [`read X0 s`; `read X1 s`; `x:num->int32`; `pc:num`; `read X30 s`]
   [`pc:num`; `sig:int64`; `zi:int64`; `i:num`; `returnaddress:int64`] 6 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[ADD_ASSOC] THEN ASM_REWRITE_TAC[];
    DISCHARGE_SAFETY_PROPERTY_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_PACK_SIG_Z_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_PACK_SIG_Z_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  CORRECT_OF_FULL_TAC
    MLDSA_NATIVE_PACK_SIG_Z_87_GCC12_O2_IMAGE_SUBROUTINE_FULL);;

let MLDSA_NATIVE_PACK_SIG_Z_87_GCC12_O2_IMAGE_SUBROUTINE_SAFE = prove
 (MLDSA_NATIVE_PACK_SIG_Z_87_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  SAFE_OF_FULL_TAC
    MLDSA_NATIVE_PACK_SIG_Z_87_GCC12_O2_IMAGE_SUBROUTINE_FULL);;
