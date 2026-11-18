(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Signing with external mu (randomized): the proof (see                     *)
(* signature_extmu_44_spec.ml).                                              *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/gcc12_O2/signature_extmu_44_spec.ml";;
needs "arm/proofs/utils/mldsa_native_wrap.ml";;

(* ------------------------------------------------------------------------- *)
(* The calls. The frame of 112 bytes is at stackpointer + 49536, with rnd in *)
(* the buffer at stackpointer + kb, kb = 49600 or 49584 (aligned to 32), and *)
(* the canary at + 49640. The events before a call are functions of the      *)
(* variables MLD_SIGNEXTMU44_VARS.                                           *)
(* ------------------------------------------------------------------------- *)

let MLD_SIGNEXTMU44_EXEC = MLDSA_NATIVE_SIGNATURE_EXTMU_44_GCC12_O2_EXEC;;

let MLD_SIGNEXTMU44_VARS =
  [`sig:int64`; `mu:int64`; `sk:int64`; `guard:int64`; `mf:int64`;
   `mc:int64`; `mr:int64`; `pc:num`; `stackpointer:int64`;
   `returnaddress:int64`; `kb:num`];;

(*** To the test of the result of randombytes, with RND its bytes ***)

let MLD_SIGNEXTMU44_HEAD_TAC =
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC MLD_SIGNEXTMU44_EXEC (1--3) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLD_SIGNEXTMU44_EXEC (4--8) THEN
  MLD_WRAP_SYMBUF_TAC `kb:num` THEN
  ARM_STEPS_TAC MLD_SIGNEXTMU44_EXEC (9--16) THEN
  LIBC_PLT_TAC MLD_SIGNEXTMU44_EXEC 16 THEN
  LIBC_SAFE_CALL_TAC "H_RANDOMBYTES" MLD_SIGNEXTMU44_EXEC
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X30 s`]
   (ref MLD_SIGNEXTMU44_VARS) 21 THEN
  ABBREV_TAC `rv = read X0 s21` THEN
  MLD_WRAP_RANDOM_TAC `RND:num` `X19` `32` `s21:armstate`;;

(*** randombytes succeeds: signing with RND, mlen = 64, ext = 1 ***)

let MLD_SIGNEXTMU44_OK_TAC =
  ARM_STEPS_TAC MLD_SIGNEXTMU44_EXEC (22--31) THEN
  MLD_WRAP_GOT_TAC THEN
  MLD_WRAP_NULL_TAC [`sig:int64`,`2420`; `stackpointer:int64`,`49648`] THEN
  FIRST_ASSUM(fun th ->
    try STRIP_ASSUME_TAC
         (MP (SPEC `RND:num` th) (ASSUME `RND < 2 EXP 256`))
    with Failure _ -> NO_TAC) THEN
  SUBGOAL_THEN `~(word_zx (word 1:int64):int32 = word 0)` ASSUME_TAC THENL
   [CONV_TAC WORD_REDUCE_CONV; ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MLD_WRAP_READ_BYTES_BOUND o
    check (fun th -> concl th = `read (memory :> bytes(mu,64)) s31 = MU`)) THEN
  SUBGOAL_THEN `MU MOD 2 EXP 512 = MU` ASSUME_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN
    RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FULL_CALL_TAC mldsa_native_libmldsa_gcc12_O2_mc MLD_SIGNEXTMU44_EXEC
   "H_INTERNAL"
   [`read X0 s`; `read X1 s`; `64`; `read X3 s`; `0`; `read X5 s`;
    `read X6 s`; `read X7 s`; `skb:num->byte`; `MU:num`; `0`; `RND:num`;
    `MU:num`; `guard:int64`; `pc:num`; `read SP s`; `read X30 s`]
   MLD_SIGNEXTMU44_VARS 32 THEN
  ARM_STEPS_TAC MLD_SIGNEXTMU44_EXEC (33--35) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLD_SIGNEXTMU44_EXEC (36--45) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `RND:num` THEN
  ASM_REWRITE_TAC[MLD_WRAP_RET_DISTINCT; MLD_WRAP_SIGN_RET] THEN
  ABBREV_TAC `rho = mld_sk_rho skb` THEN
  ABBREV_TAC `dcl = mld_sign_declass_44 skb MU RND` THEN
  MLD_WRAP_DISCHARGE_TAC;;

(*** randombytes fails: the return of -3, RND any number ***)

let MLD_SIGNEXTMU44_FAIL_TAC =
  ARM_STEPS_TAC MLD_SIGNEXTMU44_EXEC (22--27) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLD_SIGNEXTMU44_EXEC (28--37) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `0` THEN ASM_REWRITE_TAC[MLD_WRAP_RET_DISTINCT] THEN
  CONV_TAC NUM_REDUCE_CONV THEN MLD_WRAP_DISCHARGE_TAC;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety, by cases on whether         *)
(* randombytes succeeds, which the result shows (signing returns 0 or -4),   *)
(* and at the end of each on whether the stack pointer is a multiple of 32,  *)
(* which gives the address of the buffer.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SIGNATURE_EXTMU_44_GCC12_O2_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_SIGNATURE_EXTMU_44_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th ->
    let ms,th' = CONJ_PAIR th in
    let mcp,mrb = CONJ_PAIR th' in
    MLD_WRAP_ASSUME_CALLEE_TAC
     (MATCH_MP MLDSA_NATIVE_SIGNATURE_INTERNAL_44_GCC12_O2_IMAGE_SUBROUTINE_FULL
               (CONJ ms mcp)) "H_INTERNAL" THEN
    MLD_WRAP_ASSUME_CALLEE_TAC
     (REWRITE_RULE[randombytes_safety_contract] mrb) "H_RANDOMBYTES") THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(sig:int64) (mu:int64) (sk:int64) (rho:num) (r:int64)
     (dcl:num->num#num#(num->int32)#(num->byte)) (guard:int64) (mf:int64)
     (mc:int64) (mr:int64) (pc:num) (sp:int64) (ra:int64).
     if aligned 32 sp then
       if r = word 4294967293
       then f_ev_a0 sig mu sk guard mf mc mr pc sp ra
       else f_ev_a1 sig mu sk rho dcl guard mf mc mr pc sp ra
     else
       if r = word 4294967293
       then f_ev_u0 sig mu sk guard mf mc mr pc sp ra
       else f_ev_u1 sig mu sk rho dcl guard mf mc mr pc sp ra
     :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `sig:int64`; `mu:int64`; `sk:int64`;
    `skb:num->byte`; `MU:num`; `guard:int64`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 49648 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst MLD_SIGNEXTMU44_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MLD_WRAP_FRAME_TAC 49648 [`got_stack_chk_guard:num`; `got_randombytes:num`]
   (19--22) THEN
  MLD_SIGNEXTMU44_HEAD_TAC THEN
  ASM_CASES_TAC `val(word_zx(rv:int64):int32) = 0` THENL
   [MLD_SIGNEXTMU44_OK_TAC; MLD_SIGNEXTMU44_FAIL_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SIGNATURE_EXTMU_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_SIGNATURE_EXTMU_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  MLD_WRAP_CORRECT_TAC
   MLDSA_NATIVE_SIGNATURE_EXTMU_44_GCC12_O2_IMAGE_SUBROUTINE_FULL);;

let MLDSA_NATIVE_SIGNATURE_EXTMU_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE = prove
 (MLDSA_NATIVE_SIGNATURE_EXTMU_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  MLD_WRAP_SAFE_TAC
   MLDSA_NATIVE_SIGNATURE_EXTMU_44_GCC12_O2_IMAGE_SUBROUTINE_FULL);;
