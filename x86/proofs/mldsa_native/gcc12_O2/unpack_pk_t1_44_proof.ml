(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Unpacking polynomial i of t1 from a public key: the proof (see            *)
(* unpack_pk_t1_44_spec.ml).                                                 *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/gcc12_O2/unpack_pk_t1_44_spec.ml";;
needs "x86/proofs/utils/mldsa_native_hints.ml";;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety: the address of the input,   *)
(* computed with 32-bit operations on i, then the tail call of               *)
(* mldsa_polyt1_unpack.                                                      *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_UNPACK_PK_T1_44_GCC12_O2_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_UNPACK_PK_T1_44_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT,
  let EXEC = MLDSA_NATIVE_UNPACK_PK_T1_44_GCC12_O2_EXEC in
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_POLYT1_UNPACK_GCC12_O2_IMAGE_SUBROUTINE_FULL "H_UNPACK" THEN
  META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `t1:int64`; `pk:int64`; `b:num->byte`;
    `i:num`; `pc:num`; `stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; ALL; fst EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FULL_INIT_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[ADD_ASSOC]) THEN
  X86_STEPS_TAC EXEC (1--4) THEN
  GLUE_REG_TAC `RSI` `word_add pk (word(32 + 320 * i)):int64` THEN
  FULL_CALL_TAC mldsa_native_libmldsa_gcc12_O2_mc EXEC "H_UNPACK"
   [`read RDI s`; `read RSI s`; `b:num->byte`; `pc:num`; `read RSP s`;
    `read (memory :> bytes64 (read RSP s)) s`]
   [`pc:num`; `t1:int64`; `pk:int64`; `i:num`; `stackpointer:int64`;
    `returnaddress:int64`] 5 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_UNPACK_PK_T1_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_UNPACK_PK_T1_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  CORRECT_OF_FULL_TAC
    MLDSA_NATIVE_UNPACK_PK_T1_44_GCC12_O2_IMAGE_SUBROUTINE_FULL);;

let MLDSA_NATIVE_UNPACK_PK_T1_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE = prove
 (MLDSA_NATIVE_UNPACK_PK_T1_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  SAFE_OF_FULL_TAC
    MLDSA_NATIVE_UNPACK_PK_T1_44_GCC12_O2_IMAGE_SUBROUTINE_FULL);;
