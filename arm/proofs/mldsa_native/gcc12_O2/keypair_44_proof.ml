(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Key generation with random bytes: the proof (see keypair_44_spec.ml).     *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/gcc12_O2/keypair_44_spec.ml";;
needs "arm/proofs/utils/mldsa_native_wrap.ml";;

(* ------------------------------------------------------------------------- *)
(* The calls. The frame of 96 bytes is at stackpointer + 28096, with the     *)
(* seed in the buffer at stackpointer + kb, kb = 28128 or 28144 (aligned to  *)
(* 32), and the canary at + 28184. The events before a call are functions of *)
(* the variables MLD_KEYPAIR44_VARS.                                         *)
(* ------------------------------------------------------------------------- *)

let MLD_KEYPAIR44_EXEC = MLDSA_NATIVE_KEYPAIR_44_GCC12_O2_EXEC;;

let MLD_KEYPAIR44_VARS =
  [`pk:int64`; `sk:int64`; `guard:int64`; `mf:int64`; `mr:int64`; `pc:num`;
   `stackpointer:int64`; `returnaddress:int64`; `kb:num`];;

(*** To the test of the result of randombytes, the seed SEED its bytes ***)

let MLD_KEYPAIR44_HEAD_TAC =
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC MLD_KEYPAIR44_EXEC (1--3) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLD_KEYPAIR44_EXEC (4--7) THEN
  MLD_WRAP_SYMBUF_TAC `kb:num` THEN
  ARM_STEPS_TAC MLD_KEYPAIR44_EXEC (8--14) THEN
  LIBC_PLT_TAC MLD_KEYPAIR44_EXEC 14 THEN
  LIBC_SAFE_CALL_TAC "H_RANDOMBYTES" MLD_KEYPAIR44_EXEC
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X30 s`]
   (ref MLD_KEYPAIR44_VARS) 19 THEN
  ABBREV_TAC `rv = read X0 s19` THEN
  MLD_WRAP_RANDOM_TAC `SEED:num` `X19` `32` `s19:armstate`;;

(*** randombytes succeeds: the keys from SEED and the return of 0 ***)

let MLD_KEYPAIR44_OK_TAC =
  ARM_STEPS_TAC MLD_KEYPAIR44_EXEC (20--24) THEN
  MLD_WRAP_GOT_TAC THEN
  FIRST_ASSUM(fun th ->
    try STRIP_ASSUME_TAC
         (MP (SPEC `SEED:num` th) (ASSUME `SEED < 2 EXP 256`))
    with Failure _ -> NO_TAC) THEN
  FULL_CALL_TAC mldsa_native_libmldsa_gcc12_O2_mc MLD_KEYPAIR44_EXEC
   "H_INTERNAL"
   [`read X0 s`; `read X1 s`; `read X2 s`; `SEED:num`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] MLD_KEYPAIR44_VARS 25 THEN
  ARM_STEPS_TAC MLD_KEYPAIR44_EXEC (26--28) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLD_KEYPAIR44_EXEC (29--37) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `SEED:num` THEN ASM_REWRITE_TAC[MLD_WRAP_RET_DISTINCT] THEN
  ABBREV_TAC `rho = mld_keypair_rho 4 4 SEED` THEN
  ABBREV_TAC `dcl = mld_keypair_declass_44 SEED` THEN
  MLD_WRAP_DISCHARGE_TAC;;

(*** randombytes fails: the return of -3, the seed any number ***)

let MLD_KEYPAIR44_FAIL_TAC =
  ARM_STEPS_TAC MLD_KEYPAIR44_EXEC (20--25) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLD_KEYPAIR44_EXEC (26--34) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `0` THEN ASM_REWRITE_TAC[MLD_WRAP_RET_DISTINCT] THEN
  CONV_TAC NUM_REDUCE_CONV THEN MLD_WRAP_DISCHARGE_TAC;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety, by cases on whether         *)
(* randombytes succeeds, which the result shows, and at the end of each on   *)
(* whether the stack pointer is a multiple of 32, which gives the address of *)
(* the buffer.                                                               *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_KEYPAIR_44_GCC12_O2_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_KEYPAIR_44_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th ->
    let ms,mrb = CONJ_PAIR th in
    MLD_WRAP_ASSUME_CALLEE_TAC
     (MATCH_MP MLDSA_NATIVE_KEYPAIR_INTERNAL_44_GCC12_O2_IMAGE_SUBROUTINE_FULL
               ms) "H_INTERNAL" THEN
    MLD_WRAP_ASSUME_CALLEE_TAC
     (REWRITE_RULE[randombytes_safety_contract] mrb) "H_RANDOMBYTES") THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(pk:int64) (sk:int64) (r:int64) (rho:num) (dcl:num->(bool)list)
     (guard:int64) (mf:int64) (mr:int64) (pc:num) (sp:int64) (ra:int64).
     if aligned 32 sp then
       if r = word 0 then f_ev_a1 pk sk rho dcl guard mf mr pc sp ra
       else f_ev_a0 pk sk guard mf mr pc sp ra
     else
       if r = word 0 then f_ev_u1 pk sk rho dcl guard mf mr pc sp ra
       else f_ev_u0 pk sk guard mf mr pc sp ra
     :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `pk:int64`; `sk:int64`; `guard:int64`;
    `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 28192 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst MLD_KEYPAIR44_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MLD_WRAP_FRAME_TAC 28192 [`got_stack_chk_guard:num`; `got_randombytes:num`]
   (19--21) THEN
  MLD_KEYPAIR44_HEAD_TAC THEN
  ASM_CASES_TAC `val(word_zx(rv:int64):int32) = 0` THENL
   [MLD_KEYPAIR44_OK_TAC; MLD_KEYPAIR44_FAIL_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_KEYPAIR_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_KEYPAIR_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  MLD_WRAP_CORRECT_TAC MLDSA_NATIVE_KEYPAIR_44_GCC12_O2_IMAGE_SUBROUTINE_FULL);;

let MLDSA_NATIVE_KEYPAIR_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE = prove
 (MLDSA_NATIVE_KEYPAIR_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  MLD_WRAP_SAFE_TAC MLDSA_NATIVE_KEYPAIR_44_GCC12_O2_IMAGE_SUBROUTINE_FULL);;
