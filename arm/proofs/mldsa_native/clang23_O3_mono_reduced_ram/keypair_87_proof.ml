(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Key generation with random bytes: the proof (see keypair_87_spec.ml).     *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/keypair_87_spec.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_wrap.ml";;

(* ------------------------------------------------------------------------- *)
(* The calls. Clang aligns the stack pointer itself: after the 32 bytes of   *)
(* saved registers, sp = (sp0 - 96) AND NOT 31, the seed is the buffer at sp *)
(* and the canary at sp + 56. With the stack of 13632 bytes at the bottom,   *)
(* sp = stackpointer + kb, kb = 10144 or 10128, and the proof splits on      *)
(* whether the stackpointer is a multiple of 32 (as it is for kb) right      *)
(* after the prologue. The events before a call are functions of the         *)
(* variables MLD_KEYPAIR87_VARS.                                             *)
(* ------------------------------------------------------------------------- *)

let MLD_KEYPAIR87_EXEC = MLDSA_NATIVE_KEYPAIR_87_CLANG23_O3_MONO_REDUCED_RAM_EXEC;;

let MLD_KEYPAIR87_VARS =
  [`pk:int64`; `sk:int64`; `guard:int64`; `mf:int64`; `mc:int64`; `mr:int64`; `pc:num`;
   `stackpointer:int64`; `returnaddress:int64`];;

(*** To the test of the result of randombytes, the seed SEED its bytes ***)

let MLD_KEYPAIR87_HEAD_TAC =
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC MLD_KEYPAIR87_EXEC (1--5) THEN
  MLD_WRAP_SYMBUF_TAC `kb:num` THEN MLD_WRAP_SYMBUF_END_TAC `kb:num` THEN
  ARM_STEPS_TAC MLD_KEYPAIR87_EXEC (6--6) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLD_KEYPAIR87_EXEC (7--14) THEN
  LIBC_PLT_TAC MLD_KEYPAIR87_EXEC 14 THEN
  LIBC_SAFE_CALL_TAC "H_RANDOMBYTES" MLD_KEYPAIR87_EXEC
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X30 s`]
   (ref MLD_KEYPAIR87_VARS) 19 THEN
  ABBREV_TAC `rv = read X0 s19` THEN
  MLD_WRAP_RANDOM_TAC `SEED:num` `SP` `32` `s19:armstate`;;

(*** randombytes succeeds: the keys from SEED and the return of 0 ***)

let MLD_KEYPAIR87_OK_TAC =
  ARM_STEPS_TAC MLD_KEYPAIR87_EXEC (20--24) THEN
  MLD_WRAP_GOT_TAC THEN
  FIRST_ASSUM(fun th ->
    try STRIP_ASSUME_TAC
         (MP (SPEC `SEED:num` th) (ASSUME `SEED < 2 EXP 256`))
    with Failure _ -> NO_TAC) THEN
  MLD_CLANG_CALL_FACTS_TAC 13632 13504 THEN
  FULL_CALL_TAC mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
   MLD_KEYPAIR87_EXEC "H_INTERNAL"
   [`read X0 s`; `read X1 s`; `read X2 s`; `SEED:num`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] MLD_KEYPAIR87_VARS 25 THEN
  ARM_STEPS_TAC MLD_KEYPAIR87_EXEC (26--30) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLD_KEYPAIR87_EXEC (31--43) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `SEED:num` THEN ASM_REWRITE_TAC[MLD_WRAP_RET_DISTINCT] THEN
  ABBREV_TAC `rho = mld_keypair_rho 8 7 SEED` THEN
  ABBREV_TAC `dcl = mld_keypair_declass_87 SEED` THEN
  MLD_WRAP_DISCHARGE_TAC;;

(*** randombytes fails: the return of -3, the seed any number ***)

let MLD_KEYPAIR87_FAIL_TAC =
  ARM_STEPS_TAC MLD_KEYPAIR87_EXEC (20--26) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLD_KEYPAIR87_EXEC (27--39) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `0` THEN ASM_REWRITE_TAC[MLD_WRAP_RET_DISTINCT] THEN
  CONV_TAC NUM_REDUCE_CONV THEN MLD_WRAP_DISCHARGE_TAC;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety, by cases on whether         *)
(* randombytes succeeds, which the result shows, and, from the prologue on,  *)
(* on whether the stack pointer is a multiple of 32.                         *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_KEYPAIR_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_KEYPAIR_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th ->
    let ms,rest = CONJ_PAIR th in
    let mcp,mrb = CONJ_PAIR rest in
    MLD_WRAP_ASSUME_CALLEE_TAC
     (MATCH_MP MLDSA_NATIVE_KEYPAIR_INTERNAL_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL
               (CONJ ms mcp)) "H_INTERNAL" THEN
    MLD_WRAP_ASSUME_CALLEE_TAC
     (REWRITE_RULE[randombytes_safety_contract] mrb) "H_RANDOMBYTES") THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(pk:int64) (sk:int64) (r:int64) (rho:num) (dcl:num->(bool)list)
     (guard:int64) (mf:int64) (mc:int64) (mr:int64) (pc:num) (sp:int64) (ra:int64).
     if aligned 32 sp then
       if r = word 0 then f_ev_a1 pk sk rho dcl guard mf mc mr pc sp ra
       else f_ev_a0 pk sk guard mf mc mr pc sp ra
     else
       if r = word 0 then f_ev_u1 pk sk rho dcl guard mf mc mr pc sp ra
       else f_ev_u0 pk sk guard mf mc mr pc sp ra
     :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `pk:int64`; `sk:int64`; `guard:int64`;
    `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 13632 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst MLD_KEYPAIR87_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MLD_WRAP_FRAME_TAC 13632 [`got_stack_chk_guard:num`; `got_randombytes:num`]
   ((19--20) @ [29]) THEN
  MLD_KEYPAIR87_HEAD_TAC THEN
  ASM_CASES_TAC `val(word_zx(rv:int64):int32) = 0` THEN
  MLD_CLANG_IF `val(word_zx(rv:int64):int32) = 0` MLD_KEYPAIR87_OK_TAC
   MLD_KEYPAIR87_FAIL_TAC);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_KEYPAIR_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_KEYPAIR_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT,
  MLD_WRAP_CORRECT_TAC MLDSA_NATIVE_KEYPAIR_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL);;

let MLDSA_NATIVE_KEYPAIR_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE = prove
 (MLDSA_NATIVE_KEYPAIR_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT,
  MLD_WRAP_SAFE_TAC MLDSA_NATIVE_KEYPAIR_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL);;
