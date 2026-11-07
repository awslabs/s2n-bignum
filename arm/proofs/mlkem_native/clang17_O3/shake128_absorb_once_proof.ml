(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

needs "arm/proofs/mlkem_native/clang17_O3/shake128_absorb_once_spec.ml";;


let MLKEM_NATIVE_SHAKE128_ABSORB_ONCE_CLANG17_O3_IMAGE_SUBROUTINE_FULL = prove
 (MLKEM_NATIVE_SHAKE128_ABSORB_ONCE_CLANG17_O3_IMAGE_SUBROUTINE_FULL_STMT,
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_KECCAK_ABSORB_ONCE_CLANG17_O3_IMAGE_SUBROUTINE_FULL
    "H_ABSORB" THEN
  META_EXISTS_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_stack_chk_guard:num`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`;
                                     `got_stack_chk_guard:num`] WORD_ADD]) THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC MLKEM_NATIVE_SHAKE128_ABSORB_ONCE_CLANG17_O3_EXEC (1--6) THEN
  REMOVE_THEN "H_ABSORB" (fun safety_th ->
    ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_clang17_O3_mc,
       MLKEM_NATIVE_SHAKE128_ABSORB_ONCE_CLANG17_O3_EXEC,
       0x0,mlkem_native_libmlkem_clang17_O3_mc,safety_th)
      [`e:(uarch_event)list`; `read X0 s`; `168`; `read X2 s`; `mlen:num`;
       `0x1F`; `M:num`; `guard:int64`; `pc:num`; `read SP s`;
       `read X30 s`] 7 THENL
     [EXISTS_E2_TAC (ref [`pc:num`; `st:int64`; `m:int64`; `mlen:num`;
                          `guard:int64`; `stackpointer:int64`;
                          `returnaddress:int64`]);
      LABEL_TAC "H_ABSORB" safety_th]) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

let MLKEM_NATIVE_SHAKE128_ABSORB_ONCE_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT = prove
 (MLKEM_NATIVE_SHAKE128_ABSORB_ONCE_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT_STMT,
  REPEAT STRIP_TAC THEN
  X_CHOOSE_TAC
   `f:int64->int64->num->int64->num->int64->int64->(uarch_event)list`
   MLKEM_NATIVE_SHAKE128_ABSORB_ONCE_CLANG17_O3_IMAGE_SUBROUTINE_FULL THEN
  GHOST_INTRO_TAC `e:(uarch_event)list` `read events` THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`e:(uarch_event)list`; `st:int64`; `m:int64`; `mlen:num`; `M:num`;
    `guard:int64`; `pc:num`; `stackpointer:int64`;
    `returnaddress:int64`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MATCH_MP_TAC o MATCH_MP ENSURES_PREPOST_WEAKEN) THEN
  SIMP_TAC[]);;

let MLKEM_NATIVE_SHAKE128_ABSORB_ONCE_CLANG17_O3_IMAGE_SUBROUTINE_SAFE = prove
 (MLKEM_NATIVE_SHAKE128_ABSORB_ONCE_CLANG17_O3_IMAGE_SUBROUTINE_SAFE_STMT,
  MP_TAC MLKEM_NATIVE_SHAKE128_ABSORB_ONCE_CLANG17_O3_IMAGE_SUBROUTINE_FULL THEN
  MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN DISCH_TAC THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  GHOST_INTRO_TAC `M:num` `read (memory :> bytes(m,mlen))` THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`e:(uarch_event)list`; `st:int64`; `m:int64`; `mlen:num`; `M:num`;
    `guard:int64`; `pc:num`; `stackpointer:int64`;
    `returnaddress:int64`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MATCH_MP_TAC o MATCH_MP ENSURES_PREPOST_WEAKEN) THEN
  SIMP_TAC[]);;
