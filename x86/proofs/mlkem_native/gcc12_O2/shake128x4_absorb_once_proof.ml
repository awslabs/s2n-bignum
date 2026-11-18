(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

needs "x86/proofs/mlkem_native/gcc12_O2/shake128x4_absorb_once_spec.ml";;


let MLKEM_NATIVE_SHAKE128X4_ABSORB_ONCE_GCC12_O2_IMAGE_SUBROUTINE_FULL = time prove
 (MLKEM_NATIVE_SHAKE128X4_ABSORB_ONCE_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT,
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_IMAGE_SUBROUTINE_FULL
    "H_ABSORB" THEN
  META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `st:int64`; `m0:int64`; `m1:int64`; `m2:int64`;
    `m3:int64`; `mlen:num`; `M0:num`; `M1:num`; `M2:num`; `M3:num`;
    `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 416 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC MLKEM_NATIVE_SHAKE128X4_ABSORB_ONCE_GCC12_O2_EXEC (1--12) THEN
  MEMSET_PREP_TAC THEN
  MEMSET_STEP_TAC MLKEM_NATIVE_SHAKE128X4_ABSORB_ONCE_GCC12_O2_EXEC 13 THEN
  MEMSET_DONE_TAC `st:int64` 800 "s13" THEN
  X86_STEPS_TAC MLKEM_NATIVE_SHAKE128X4_ABSORB_ONCE_GCC12_O2_EXEC (14--21) THEN
  REMOVE_THEN "H_ABSORB" (fun safety_th ->
    X86_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_gcc12_O2_mc,
       MLKEM_NATIVE_SHAKE128X4_ABSORB_ONCE_GCC12_O2_EXEC,
       0x0,mlkem_native_libmlkem_gcc12_O2_mc,safety_th)
      [`e:(uarch_event)list`; `read RDI s`; `168`; `read RDX s`;
       `read RCX s`; `read R8 s`; `read R9 s`; `mlen:num`;
       `M0:num`; `M1:num`; `M2:num`; `M3:num`; `pc:num`; `read RSP s`;
       `read (memory :> bytes64(read RSP s)) s`] 22 THENL
     [EXISTS_E2_TAC (ref [`pc:num`; `st:int64`; `m0:int64`; `m1:int64`;
                          `m2:int64`; `m3:int64`; `mlen:num`;
                          `stackpointer:int64`; `returnaddress:int64`]);
      LABEL_TAC "H_ABSORB" safety_th]) THEN
  X86_STEPS_TAC MLKEM_NATIVE_SHAKE128X4_ABSORB_ONCE_GCC12_O2_EXEC (23--24) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

let MLKEM_NATIVE_SHAKE128X4_ABSORB_ONCE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (MLKEM_NATIVE_SHAKE128X4_ABSORB_ONCE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  GHOST_INTRO_TAC `e:(uarch_event)list` `read events` THEN
  MP_TAC
   MLKEM_NATIVE_SHAKE128X4_ABSORB_ONCE_GCC12_O2_IMAGE_SUBROUTINE_FULL THEN
  DISCH_THEN(CHOOSE_THEN (MP_TAC o SPECL
   [`e:(uarch_event)list`; `st:int64`; `m0:int64`; `m1:int64`; `m2:int64`;
    `m3:int64`; `mlen:num`; `M0:num`; `M1:num`; `M2:num`; `M3:num`;
    `pc:num`; `stackpointer:int64`; `returnaddress:int64`])) THEN
  ANTS_TAC THENL
   [POP_ASSUM MP_TAC THEN REWRITE_TAC[ALLPAIRS; ALL] THEN SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MATCH_MP_TAC o MATCH_MP ENSURES_WEAKEN_RULE) THEN
  SIMP_TAC[]);;

let MLKEM_NATIVE_SHAKE128X4_ABSORB_ONCE_GCC12_O2_IMAGE_SUBROUTINE_SAFE = prove
 (MLKEM_NATIVE_SHAKE128X4_ABSORB_ONCE_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  MP_TAC
   MLKEM_NATIVE_SHAKE128X4_ABSORB_ONCE_GCC12_O2_IMAGE_SUBROUTINE_FULL THEN
  MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `st:int64`; `m0:int64`; `m1:int64`; `m2:int64`;
    `m3:int64`; `mlen:num`; `pc:num`; `stackpointer:int64`;
    `returnaddress:int64`] THEN
  DISCH_TAC THEN
  MAP_EVERY (fun (m,mm) ->
    GHOST_INTRO_TAC mm (subst [m,`m:int64`]
     `read (memory :> bytes(m,mlen)):x86state->num`))
   [`m0:int64`,`M0:num`; `m1:int64`,`M1:num`; `m2:int64`,`M2:num`;
    `m3:int64`,`M3:num`] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`e:(uarch_event)list`; `st:int64`; `m0:int64`; `m1:int64`; `m2:int64`;
    `m3:int64`; `mlen:num`; `M0:num`; `M1:num`; `M2:num`; `M3:num`;
    `pc:num`; `stackpointer:int64`; `returnaddress:int64`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MATCH_MP_TAC o MATCH_MP ENSURES_WEAKEN_RULE) THEN
  SIMP_TAC[]);;
