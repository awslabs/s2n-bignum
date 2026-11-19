(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The proof for mldsa_shake256x4_release (see shake256x4_release_spec.ml):  *)
(* a tail call of mldsa_shake128x4_release, whose theorems are used.         *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/gcc12_Os/shake256x4_release_spec.ml";;
needs "arm/proofs/utils/mldsa_native_full.ml";;

(* ------------------------------------------------------------------------- *)
(* Correctness proof, assuming the contract for memset at the address mf in  *)
(* the GOT entry, with its code and data in the region (ea,el), which must   *)
(* not overlap the context or the stack. The stack is the 16 bytes of        *)
(* mldsa_shake128x4_release.                                                 *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SHAKE256X4_RELEASE_GCC12_OS_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_SHAKE256X4_RELEASE_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT,
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; NONOVERLAPPING_CLAUSES] THEN
  REPEAT STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC MLDSA_NATIVE_SHAKE256X4_RELEASE_GCC12_OS_EXEC (1--1) THEN
  ARM_SUBROUTINE_SIM_TAC
   (mldsa_native_libmldsa_gcc12_Os_mc,
    MLDSA_NATIVE_SHAKE256X4_RELEASE_GCC12_OS_EXEC,
    0x0,mldsa_native_libmldsa_gcc12_Os_mc,
    MLDSA_NATIVE_SHAKE128X4_RELEASE_GCC12_OS_IMAGE_SUBROUTINE_CORRECT)
   [`read X0 s`; `mf:int64`; `ea:int64`; `el:num`; `ev:num`;
    `pc:num`; `read SP s`; `read X30 s`] 2 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together, and constant time  *)
(* and memory safety alone.                                                  *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SHAKE256X4_RELEASE_GCC12_OS_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_SHAKE256X4_RELEASE_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(fun th ->
    ASSUME_CALLEE_SAFETY_TAILED_TAC
     (MATCH_MP MLDSA_NATIVE_SHAKE128X4_RELEASE_GCC12_OS_IMAGE_SUBROUTINE_FULL th)
     "H_CALLEE") THEN
  META_EXISTS_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC MLDSA_NATIVE_SHAKE256X4_RELEASE_GCC12_OS_EXEC (1--1) THEN
  REMOVE_THEN "H_CALLEE" (fun safety_th ->
    ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mldsa_native_libmldsa_gcc12_Os_mc,
       MLDSA_NATIVE_SHAKE256X4_RELEASE_GCC12_OS_EXEC,
       0x0,mldsa_native_libmldsa_gcc12_Os_mc,safety_th)
      [`e:(uarch_event)list`; `read X0 s`; `pc:num`; `read SP s`;
       `read X30 s`] 2 THENL
     [EXISTS_E2_TAC (ref [`pc:num`; `st:int64`; `mf:int64`;
                          `stackpointer:int64`; `returnaddress:int64`]);
      LABEL_TAC "H_CALLEE" safety_th]) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

let MLDSA_NATIVE_SHAKE256X4_RELEASE_GCC12_OS_IMAGE_SUBROUTINE_SAFE = prove
 (MLDSA_NATIVE_SHAKE256X4_RELEASE_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> SAFE_OF_FULL_TAC
    (MP (SPEC_ALL
          MLDSA_NATIVE_SHAKE256X4_RELEASE_GCC12_OS_IMAGE_SUBROUTINE_FULL)
        th)));;
