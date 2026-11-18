(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Verifying a signature with external mu: the proof (see                    *)
(* verify_extmu_44_spec.ml).                                                 *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/gcc12_O2/verify_extmu_44_spec.ml";;
needs "x86/proofs/utils/mldsa_native_verify.ml";;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety. The moves of the arguments, *)
(* ext = 1 pushed on the stack, and the call of mldsa44_verify_internal,     *)
(* whose frame is the 29997 bytes at stackpointer below the 32 of the        *)
(* function, with pre = NULL, prelen = 0 and mlen = 64, so that mu is the 64 *)
(* bytes at mu.                                                              *)
(* ------------------------------------------------------------------------- *)

let VEM44_EXEC = MLDSA_NATIVE_VERIFY_EXTMU_44_GCC12_O2_EXEC;;

let MLDSA_NATIVE_VERIFY_EXTMU_44_GCC12_O2_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_VERIFY_EXTMU_44_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> VERIF_ASSUME_CALLEE_TAC
    (MATCH_MP MLDSA_NATIVE_VERIFY_INTERNAL_44_GCC12_O2_IMAGE_SUBROUTINE_FULL
              th) "H_INTERNAL") THEN
  META_EXISTS_TAC THEN REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; NONOVERLAPPING_CLAUSES; fst VEM44_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC VEM44_EXEC (1--7) THEN
  VERIF_NULL_TAC [`stackpointer:int64`,`29997`] THEN
  FULL_CALL_TAC mldsa_native_libmldsa_gcc12_O2_mc VEM44_EXEC "H_INTERNAL"
   [`read RDI s`; `read RSI s`; `64`; `read RCX s`; `0`; `read R9 s`;
    `word 1:int64`; `sigb:num->byte`; `pkb:num->byte`; `MU:num`; `0`;
    `pc:num`; `read RSP s`; `read (memory :> bytes64 (read RSP s)) s`]
   [`sig:int64`; `mu:int64`; `pk:int64`; `sigb:num->byte`; `pkb:num->byte`;
    `MU:num`; `mf:int64`; `pc:num`; `stackpointer:int64`;
    `returnaddress:int64`] 8 THEN
  X86_STEPS_TAC VEM44_EXEC (9--10) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [CONV_TAC WORD_REDUCE_CONV THEN
    MP_TAC(ISPECL [`mu:int64`; `64`; `read memory s10`] READ_BYTES_BOUND) THEN
    REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[MOD_LT];
    VERIF_EMPTY_REGIONS_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_VERIFY_EXTMU_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_VERIFY_EXTMU_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> CORRECT_OF_FULL_TAC
    (MP (SPEC_ALL MLDSA_NATIVE_VERIFY_EXTMU_44_GCC12_O2_IMAGE_SUBROUTINE_FULL)
        th)));;

let MLDSA_NATIVE_VERIFY_EXTMU_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE = prove
 (MLDSA_NATIVE_VERIFY_EXTMU_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> SAFE_OF_FULL_TAC
    (MP (SPEC_ALL MLDSA_NATIVE_VERIFY_EXTMU_44_GCC12_O2_IMAGE_SUBROUTINE_FULL)
        th)));;
