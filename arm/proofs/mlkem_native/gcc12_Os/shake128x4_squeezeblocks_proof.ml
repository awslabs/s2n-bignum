(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

needs "arm/proofs/mlkem_native/gcc12_Os/shake128x4_squeezeblocks_spec.ml";;


let MLKEM_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_GCC12_OS_IMAGE_SUBROUTINE_CORRECT = prove
 (MLKEM_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT,
  REWRITE_TAC[C_ARGUMENTS; ALL; PAIRWISE; NONOVERLAPPING_CLAUSES] THEN
  REPEAT STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC MLKEM_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_GCC12_OS_EXEC (1--2) THEN
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_Os_mc,
    MLKEM_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_GCC12_OS_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_Os_mc,
    MLKEM_NATIVE_KECCAK_SQUEEZEBLOCKS_X4_GCC12_OS_IMAGE_SUBROUTINE_CORRECT)
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X3 s`; `nblocks:num`;
    `read X5 s`; `168`; `S0:1600 word`; `S1:1600 word`; `S2:1600 word`;
    `S3:1600 word`; `pc:num`; `read SP s`; `read X30 s`] 3 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]);;

let MLKEM_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_GCC12_OS_IMAGE_SUBROUTINE_SAFE = time prove
 (MLKEM_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT,
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_KECCAK_SQUEEZEBLOCKS_X4_GCC12_OS_IMAGE_SUBROUTINE_SAFE
    "H_SQUEEZE" THEN
  META_EXISTS_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; PAIRWISE; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC MLKEM_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_GCC12_OS_EXEC (1--2) THEN
  REMOVE_THEN "H_SQUEEZE" (fun safety_th ->
    ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_gcc12_Os_mc,
       MLKEM_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_GCC12_OS_EXEC,
       0x0,mlkem_native_libmlkem_gcc12_Os_mc,safety_th)
      [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`;
       `read X3 s`; `nblocks:num`; `read X5 s`; `168`; `pc:num`;
       `read SP s`; `read X30 s`] 3 THENL
     [EXISTS_E2_TAC (ref [`pc:num`; `out0:int64`; `out1:int64`;
                          `out2:int64`; `out3:int64`; `nblocks:num`;
                          `st:int64`; `stackpointer:int64`;
                          `returnaddress:int64`]);
      LABEL_TAC "H_SQUEEZE" safety_th]) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

let MLKEM_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_GCC12_OS_IMAGE_SUBROUTINE_FULL = prove
 (MLKEM_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT,
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_KECCAK_SQUEEZEBLOCKS_X4_GCC12_OS_IMAGE_SUBROUTINE_FULL
    "H_SQUEEZE" THEN
  META_EXISTS_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; PAIRWISE; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC MLKEM_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_GCC12_OS_EXEC (1--2) THEN
  REMOVE_THEN "H_SQUEEZE" (fun safety_th ->
    ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_gcc12_Os_mc,
       MLKEM_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_GCC12_OS_EXEC,
       0x0,mlkem_native_libmlkem_gcc12_Os_mc,safety_th)
      [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`;
       `read X3 s`; `nblocks:num`; `read X5 s`; `168`; `S0:1600 word`;
       `S1:1600 word`; `S2:1600 word`; `S3:1600 word`; `pc:num`;
       `read SP s`; `read X30 s`] 3 THENL
     [EXISTS_E2_TAC (ref [`pc:num`; `out0:int64`; `out1:int64`;
                          `out2:int64`; `out3:int64`; `nblocks:num`;
                          `st:int64`; `stackpointer:int64`;
                          `returnaddress:int64`]);
      LABEL_TAC "H_SQUEEZE" safety_th]) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;
