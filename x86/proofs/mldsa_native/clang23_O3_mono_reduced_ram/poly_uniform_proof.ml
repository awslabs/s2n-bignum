(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Uniform sampling of a polynomial mod q from a seed: the proof (see        *)
(* poly_uniform_spec.ml). The prologue saves six registers, aligns RSP to 32 *)
(* bytes and reserves 1088 bytes; with the callee stacks they are the 1384   *)
(* bytes (bot,1384) of the aligned part of the frame (see                    *)
(* utils/mldsa_native_realign.ml), which is the region bq of PU_MAIN of      *)
(* inline_pu.ml, and the epilogue restores the registers. Everything in      *)
(* between is PU_MAIN.                                                       *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/poly_uniform_spec.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_pu.ml";;
needs "x86/proofs/utils/mldsa_native_realign.ml";;

let PU_EXEC = MLDSA_NATIVE_POLY_UNIFORM_CLANG23_O3_MONO_REDUCED_RAM_EXEC;;

let PUT_ALLOWED = [`a:int64`; `seed:int64`; `M:num`; `mf:int64`; `mc:int64`; `pc:num`; `stackpointer:int64`; `returnaddress:int64`; `bot:int64`];;
let PUT_MCALL name ilist n =
  REMOVE_THEN name (fun th ->
    X86_SUBROUTINE_SIM_TAC ~is_safety_thm:true (mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc,PU_EXEC,0x0,mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc,th)
      (`e:(uarch_event)list`::ilist) n THENL
     [PU_E2_ANY (ref PUT_ALLOWED); LABEL_TAC name th]);;

let MLDSA_NATIVE_POLY_UNIFORM_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_POLY_UNIFORM_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT,
  (REPEAT GEN_TAC THEN
  DISCH_THEN(fun th ->
    ASSUME_CALLEE_SAFETY_TAILED_TAC (MP (SPECL [`mf:int64`;`mc:int64`;`ea:int64`;`el:num`;`ev:num`] PU_MAIN) th) "H_MAIN") THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(a:int64) (seed:int64) (M:num) (mf:int64) (mc:int64) (pc:num) (stackpointer:int64) (returnaddress:int64).
     f_ev_all a seed M mf mc pc stackpointer returnaddress:(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES; fst PU_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
  (REALIGN_TAC 1415 THEN REALIGN_FRAME_TAC 1463 1415 THEN
  REALIGN_NONOV_TAC 1384
   [`a:int64,1024`; `seed:int64,34`; `word pc:int64,libmldsa_size`;
    `word(pc + got_memset):int64,8`; `word(pc + got_memcpy):int64,8`;
    `ea:int64,el:num`;
    `word_add stackpointer (word 1415):int64,48`;
    `word_add stackpointer (word 1463):int64,8`] THEN
  REALIGN_ALIGNED_TAC [296]) THEN
  (ENSURES_PRESERVED_TAC "rbx_init" `RBX` THEN
  ENSURES_PRESERVED_TAC "rbp_init" `RBP` THEN
  ENSURES_PRESERVED_TAC "r12_init" `R12` THEN
  ENSURES_PRESERVED_TAC "r13_init" `R13` THEN
  ENSURES_PRESERVED_TAC "r14_init" `R14` THEN
  ENSURES_PRESERVED_TAC "r15_init" `R15`) THEN
  (FULL_INIT_TAC THEN X86_STEPS_TAC PU_EXEC (1--8) THEN REALIGN_RSP_TAC THEN X86_STEPS_TAC PU_EXEC (9--9)) THEN
  (PUT_MCALL "H_MAIN" [`a:int64`; `seed:int64`; `M:num`; `bot:int64`; `pc:num`] 10) THEN
  (X86_STEPS_TAC PU_EXEC (11--23)) THEN
  (ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC) THEN
  REALIGN_UNBOT_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC);;

let MLDSA_NATIVE_POLY_UNIFORM_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_POLY_UNIFORM_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th ->
    CORRECT_OF_FULL_TAC
     (MP (SPEC_ALL
       MLDSA_NATIVE_POLY_UNIFORM_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL) th)));;

let MLDSA_NATIVE_POLY_UNIFORM_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE = prove
 (MLDSA_NATIVE_POLY_UNIFORM_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th ->
    SAFE_OF_FULL_TAC
     (MP (SPEC_ALL
       MLDSA_NATIVE_POLY_UNIFORM_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL) th)));;
