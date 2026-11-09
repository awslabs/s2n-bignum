(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Verifying a signature with external mu: the proof (see                    *)
(* verify_extmu_44_spec.ml).                                                 *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/gcc12_O2/verify_extmu_44_spec.ml";;
needs "arm/proofs/utils/mldsa_native_wrap.ml";;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety. The five moves of the       *)
(* arguments and the tail call, with the frame of mldsa44_verify_internal at *)
(* the same stack pointer and pre = NULL, prelen = 0, ext = 1 and mlen = 64, *)
(* so that mu is the 64 bytes at mu.                                         *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_VERIFY_EXTMU_44_GCC12_O2_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_VERIFY_EXTMU_44_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> MLD_WRAP_ASSUME_CALLEE_TAC
    (MATCH_MP MLDSA_NATIVE_VERIFY_INTERNAL_44_GCC12_O2_IMAGE_SUBROUTINE_FULL
              th) "H_INTERNAL") THEN
  META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `sig:int64`; `mu:int64`; `pk:int64`;
    `sigb:num->byte`; `pkb:num->byte`; `MU:num`; `guard:int64`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 29888 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; NONOVERLAPPING_CLAUSES;
              fst MLDSA_NATIVE_VERIFY_EXTMU_44_GCC12_O2_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC MLDSA_NATIVE_VERIFY_EXTMU_44_GCC12_O2_EXEC (1--6) THEN
  MLD_WRAP_NULL_TAC [`stackpointer:int64`,`29888`] THEN
  FULL_CALL_TAC mldsa_native_libmldsa_gcc12_O2_mc
   MLDSA_NATIVE_VERIFY_EXTMU_44_GCC12_O2_EXEC "H_INTERNAL"
   [`read X0 s`; `read X1 s`; `64`; `read X3 s`; `0`; `read X5 s`;
    `read X6 s`; `sigb:num->byte`; `pkb:num->byte`; `MU:num`; `0`;
    `guard:int64`; `pc:num`; `read SP s`; `read X30 s`]
   [`sig:int64`; `mu:int64`; `pk:int64`; `sigb:num->byte`; `pkb:num->byte`;
    `MU:num`; `guard:int64`; `mf:int64`; `pc:num`; `stackpointer:int64`;
    `returnaddress:int64`] 7 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [CONV_TAC WORD_REDUCE_CONV THEN
    MP_TAC(ISPECL [`mu:int64`; `64`; `read memory s7`] READ_BYTES_BOUND) THEN
    REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[MOD_LT];
    MLD_WRAP_DISCHARGE_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_VERIFY_EXTMU_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_VERIFY_EXTMU_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  MLD_WRAP_CORRECT_TAC
   MLDSA_NATIVE_VERIFY_EXTMU_44_GCC12_O2_IMAGE_SUBROUTINE_FULL);;

let MLDSA_NATIVE_VERIFY_EXTMU_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE = prove
 (MLDSA_NATIVE_VERIFY_EXTMU_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  MLD_WRAP_SAFE_TAC
   MLDSA_NATIVE_VERIFY_EXTMU_44_GCC12_O2_IMAGE_SUBROUTINE_FULL);;
