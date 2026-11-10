(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Key generation with random bytes: the proof (see keypair_44_spec.ml).     *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/gcc12_O2/keypair_44_spec.ml";;
needs "x86/proofs/utils/mldsa_native_api.ml";;

let KPA44_EXEC = MLDSA_NATIVE_KEYPAIR_44_GCC12_O2_EXEC;;

(* ------------------------------------------------------------------------- *)
(* The frame. After REPEAT_GEN_AND_OFFSET_STACKPTR_TAC, stackpointer is the  *)
(* bottom of the 28331 bytes of stack below the return address, at           *)
(* stackpointer + 28331; the code pushes RBP (the frame pointer), R13, R12   *)
(* and RBX, from stackpointer + 28323 down to stackpointer + 28299, aligns   *)
(* RSP to 32 bytes, at bot + 28268 (see utils/mldsa_native_realign.ml), and  *)
(* reserves 32 bytes for the buffer of the random bytes, at bot + 28236,     *)
(* below which mldsa44_keypair_internal uses the stack down to bot. The      *)
(* events before a call are functions of the variables KPA44_ALLOWED.        *)
(* ------------------------------------------------------------------------- *)

let KPA44_ALLOWED =
  [`pk:int64`; `sk:int64`; `mf:int64`; `mr:int64`; `pc:num`;
   `stackpointer:int64`; `returnaddress:int64`; `bot:int64`];;

(*** To the call of randombytes, through its PLT stub ***)

let KPA44_HEAD_TAC =
  FULL_INIT_TAC THEN
  X86_STEPS_TAC KPA44_EXEC (1--9) THEN REALIGN_RSP_TAC THEN
  X86_STEPS_TAC KPA44_EXEC (10--13) THEN
  LIBC_PLT_TAC KPA44_EXEC (layout "plt_randombytes")
   (layout "got_randombytes") 13 THEN
  LIBC_FULL_CALL_TAC "H_RANDOMBYTES" KPA44_EXEC
   [`e:(uarch_event)list`; `read RDI s`; `read RSI s`; `read RSP s`;
    `read (memory :> bytes64 (read RSP s)) s`]
   (ref KPA44_ALLOWED) 15 THEN
  ABBREV_TAC `rv = read RAX s15` THEN
  API_RANDOM_TAC `SEED:num` `word_add bot (word 28236):int64` 32
   `s15:x86state`;;

(*** randombytes succeeds: the keys from SEED and the return of 0 ***)

let KPA44_OK_TAC =
  X86_STEPS_TAC KPA44_EXEC (16--21) THEN
  FIRST_ASSUM(fun th ->
    try STRIP_ASSUME_TAC
         (MP (SPEC `SEED:num` th) (ASSUME `SEED < 2 EXP 256`))
    with Failure _ -> NO_TAC) THEN
  FULL_CALL_TAC mldsa_native_libmldsa_gcc12_O2_mc KPA44_EXEC "H_INTERNAL"
   [`read RDI s`; `read RSI s`; `read RDX s`; `SEED:num`; `pc:num`;
    `read RSP s`; `read (memory :> bytes64 (read RSP s)) s`]
   KPA44_ALLOWED 22 THEN
  X86_STEPS_TAC KPA44_EXEC (23--31) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `SEED:num` THEN ASM_REWRITE_TAC[API_RET_DISTINCT] THEN
  ABBREV_TAC `rho = mld_keypair_rho 4 4 SEED` THEN
  ABBREV_TAC `dcl = mld_keypair_declass_44 SEED` THEN
  REALIGN_UNBOT_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC;;

(*** randombytes fails: the return of -3, the seed any number ***)

let KPA44_FAIL_TAC =
  X86_STEPS_TAC KPA44_EXEC (16--28) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `0` THEN ASM_REWRITE_TAC[API_RET_DISTINCT] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REALIGN_UNBOT_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety, by cases on whether         *)
(* randombytes succeeds, which its result shows.                             *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_KEYPAIR_44_GCC12_O2_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_KEYPAIR_44_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th ->
    let ms,mrb = CONJ_PAIR th in
    ASSUME_CALLEE_SAFETY_TAILED_TAC
     (MATCH_MP
       MLDSA_NATIVE_KEYPAIR_INTERNAL_44_GCC12_O2_IMAGE_SUBROUTINE_FULL
       ms) "H_INTERNAL" THEN
    ASSUME_CALLEE_SAFETY_TAILED_TAC
     (REWRITE_RULE[randombytes_safety_contract] mrb) "H_RANDOMBYTES") THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(pk:int64) (sk:int64) (r:int64) (rho:num) (dcl:num->(bool)list)
     (mf:int64) (mr:int64) (pc:num) (stackpointer:int64)
     (returnaddress:int64).
     if r = word 0
     then f_ev_1 pk sk rho dcl mf mr pc stackpointer returnaddress
     else f_ev_0 pk sk mf mr pc stackpointer returnaddress
     :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst KPA44_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REALIGN_TAC 28299 THEN REALIGN_FRAME_TAC 28331 28299 THEN
  REALIGN_NONOV_TAC 28268
   [`pk:int64,1312`; `sk:int64,2560`; `word pc:int64,libmldsa_size`;
    `word(pc + got_memset):int64,8`;
    `word(pc + got_randombytes):int64,8`; `ea:int64,el:num`;
    `word_add stackpointer (word 28299):int64,32`;
    `word_add stackpointer (word 28331):int64,8`] THEN
  REALIGN_ALIGNED_TAC [28236] THEN
  ENSURES_PRESERVED_TAC "rbx_init" `RBX` THEN
  ENSURES_PRESERVED_TAC "rbp_init" `RBP` THEN
  ENSURES_PRESERVED_TAC "r12_init" `R12` THEN
  ENSURES_PRESERVED_TAC "r13_init" `R13` THEN
  KPA44_HEAD_TAC THEN
  ASM_CASES_TAC `val(word_zx(rv:int64):int32) = 0` THENL
   [KPA44_OK_TAC; KPA44_FAIL_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_KEYPAIR_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_KEYPAIR_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  API_CORRECT_TAC
    MLDSA_NATIVE_KEYPAIR_44_GCC12_O2_IMAGE_SUBROUTINE_FULL);;

let MLDSA_NATIVE_KEYPAIR_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE = prove
 (MLDSA_NATIVE_KEYPAIR_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  API_SAFE_TAC
    MLDSA_NATIVE_KEYPAIR_44_GCC12_O2_IMAGE_SUBROUTINE_FULL);;
