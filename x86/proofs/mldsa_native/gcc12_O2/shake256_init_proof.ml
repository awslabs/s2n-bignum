(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Initialization of a SHAKE256 context: the proof (see                      *)
(* shake256_init_spec.ml).                                                   *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/gcc12_O2/shake256_init_spec.ml";;
needs "x86/proofs/utils/mldsa_native_full.ml";;
needs "x86/proofs/utils/mldsa_native_memset.ml";;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety. The state is zeroed by the  *)
(* stores of quadwords at both ends and the REP STOSQ in between, whose      *)
(* address depends on the alignment of ctx (see MEMSET_PREP_TAC in           *)
(* utils/mldsa_native_keccak.ml), and the position by a store of a 32-bit    *)
(* word.                                                                     *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SHAKE256_INIT_GCC12_O2_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_SHAKE256_INIT_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT,
  META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `ctx:int64`; `pc:num`; `stackpointer:int64`;
    `returnaddress:int64`] THEN
  REWRITE_TAC[C_ARGUMENTS; NONOVERLAPPING_CLAUSES; ALL;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              fst MLDSA_NATIVE_SHAKE256_INIT_GCC12_O2_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FULL_INIT_TAC THEN
  X86_STEPS_TAC MLDSA_NATIVE_SHAKE256_INIT_GCC12_O2_EXEC (1--10) THEN
  MEMSET_PREP_TAC THEN
  MEMSET_STEP_TAC MLDSA_NATIVE_SHAKE256_INIT_GCC12_O2_EXEC 11 THEN
  MEMSET_DONE_TAC `ctx:int64` 200 "s11" THEN
  X86_STEPS_TAC MLDSA_NATIVE_SHAKE256_INIT_GCC12_O2_EXEC (12--13) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[READ_MEMORY_WBYTES_1600; VAL_WORD_0] THEN ASM_REWRITE_TAC[];
    DISCHARGE_SAFETY_PROPERTY_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SHAKE256_INIT_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_SHAKE256_INIT_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  CORRECT_OF_FULL_TAC
    MLDSA_NATIVE_SHAKE256_INIT_GCC12_O2_IMAGE_SUBROUTINE_FULL);;

let MLDSA_NATIVE_SHAKE256_INIT_GCC12_O2_IMAGE_SUBROUTINE_SAFE = prove
 (MLDSA_NATIVE_SHAKE256_INIT_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  SAFE_OF_FULL_TAC
    MLDSA_NATIVE_SHAKE256_INIT_GCC12_O2_IMAGE_SUBROUTINE_FULL);;
