(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Key generation with random bytes: the proof (see keypair_87_spec.ml).     *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/keypair_87_spec.ml";;
needs "x86/proofs/utils/mldsa_native_api.ml";;

let KPA87_EXEC = MLDSA_NATIVE_KEYPAIR_87_CLANG23_O3_MONO_REDUCED_RAM_EXEC;;

(* ------------------------------------------------------------------------- *)
(* The frame. After REPEAT_GEN_AND_OFFSET_STACKPTR_TAC, stackpointer is the  *)
(* bottom of the 12763 bytes of stack below the return address, at           *)
(* stackpointer + 12763; the code pushes RBP (the frame pointer), R14 and    *)
(* RBX, from stackpointer + 12755 down to stackpointer + 12739, aligns RSP   *)
(* to 32 bytes, at bot + 12708 (see utils/mldsa_native_realign.ml), and      *)
(* reserves 32 bytes for the buffer of the random bytes, at bot + 12676,     *)
(* below which mldsa87_keypair_internal uses the stack down to bot. The      *)
(* events before a call are functions of the variables KPA87_ALLOWED.        *)
(* ------------------------------------------------------------------------- *)

let KPA87_ALLOWED =
  [`pk:int64`; `sk:int64`; `mf:int64`; `mc:int64`; `mr:int64`; `pc:num`;
   `stackpointer:int64`; `returnaddress:int64`; `bot:int64`];;

(*** To the call of randombytes, through its PLT stub ***)

let KPA87_HEAD_TAC =
  FULL_INIT_TAC THEN
  X86_STEPS_TAC KPA87_EXEC (1--5) THEN REALIGN_RSP_TAC THEN
  X86_STEPS_TAC KPA87_EXEC (6--11) THEN
  LIBC_PLT_TAC KPA87_EXEC (layout "plt_randombytes")
   (layout "got_randombytes") 11 THEN
  LIBC_FULL_CALL_TAC "H_RANDOMBYTES" KPA87_EXEC
   [`e:(uarch_event)list`; `read RDI s`; `read RSI s`; `read RSP s`;
    `read (memory :> bytes64 (read RSP s)) s`]
   (ref KPA87_ALLOWED) 13 THEN
  ABBREV_TAC `rv = read RAX s13` THEN
  API_RANDOM_TAC `SEED:num` `word_add bot (word 12676):int64` 32
   `s13:x86state`;;

(*** randombytes succeeds: the keys from SEED and the return of 0 ***)

let KPA87_OK_TAC =
  X86_STEPS_TAC KPA87_EXEC (14--16) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_ZX_ZX_32_64_32]) THEN
  X86_STEPS_TAC KPA87_EXEC (17--21) THEN
  FIRST_ASSUM(fun th ->
    try STRIP_ASSUME_TAC
         (MP (SPEC `SEED:num` th) (ASSUME `SEED < 2 EXP 256`))
    with Failure _ -> NO_TAC) THEN
  FULL_CALL_TAC mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc KPA87_EXEC "H_INTERNAL"
   [`read RDI s`; `read RSI s`; `read RDX s`; `SEED:num`; `pc:num`;
    `read RSP s`; `read (memory :> bytes64 (read RSP s)) s`]
   KPA87_ALLOWED 22 THEN
  X86_STEPS_TAC KPA87_EXEC (23--36) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `SEED:num` THEN ASM_REWRITE_TAC[API_RET_DISTINCT] THEN
  ABBREV_TAC `rho = mld_keypair_rho 8 7 SEED` THEN
  ABBREV_TAC `dcl = mld_keypair_declass_87 SEED` THEN
  REALIGN_UNBOT_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC;;

(*** randombytes fails: the return of -3, the seed any number ***)

let KPA87_FAIL_TAC =
  X86_STEPS_TAC KPA87_EXEC (14--16) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_ZX_ZX_32_64_32]) THEN
  X86_STEPS_TAC KPA87_EXEC (17--30) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `0` THEN ASM_REWRITE_TAC[API_RET_DISTINCT] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REALIGN_UNBOT_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety, by cases on whether         *)
(* randombytes succeeds, which its result shows.                             *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_KEYPAIR_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_KEYPAIR_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th ->
    let ms,rest = CONJ_PAIR th in
    let mcb,mrb = CONJ_PAIR rest in
    ASSUME_CALLEE_SAFETY_TAILED_TAC
     (MATCH_MP
       MLDSA_NATIVE_KEYPAIR_INTERNAL_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL
       (CONJ ms mcb)) "H_INTERNAL" THEN
    ASSUME_CALLEE_SAFETY_TAILED_TAC
     (REWRITE_RULE[randombytes_safety_contract] mrb) "H_RANDOMBYTES") THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(pk:int64) (sk:int64) (r:int64) (rho:num) (dcl:num->(bool)list)
     (mf:int64) (mc:int64) (mr:int64) (pc:num) (stackpointer:int64)
     (returnaddress:int64).
     if r = word 0
     then f_ev_1 pk sk rho dcl mf mc mr pc stackpointer returnaddress
     else f_ev_0 pk sk mf mc mr pc stackpointer returnaddress
     :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst KPA87_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REALIGN_TAC 12739 THEN REALIGN_FRAME_TAC 12763 12739 THEN
  REALIGN_NONOV_TAC 12708
   [`pk:int64,2592`; `sk:int64,4896`; `word pc:int64,libmldsa_size`;
    `word(pc + got_memset):int64,8`; `word(pc + got_memcpy):int64,8`;
    `word(pc + got_randombytes):int64,8`; `ea:int64,el:num`;
    `word_add stackpointer (word 12739):int64,24`;
    `word_add stackpointer (word 12763):int64,8`] THEN
  REALIGN_ALIGNED_TAC [12676] THEN
  ENSURES_PRESERVED_TAC "rbx_init" `RBX` THEN
  ENSURES_PRESERVED_TAC "rbp_init" `RBP` THEN
  ENSURES_PRESERVED_TAC "r14_init" `R14` THEN
  KPA87_HEAD_TAC THEN
  ASM_CASES_TAC `val(word_zx(rv:int64):int32) = 0` THENL
   [KPA87_OK_TAC; KPA87_FAIL_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_KEYPAIR_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_KEYPAIR_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT,
  API_CORRECT_TAC
    MLDSA_NATIVE_KEYPAIR_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL);;

let MLDSA_NATIVE_KEYPAIR_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE = prove
 (MLDSA_NATIVE_KEYPAIR_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT,
  API_SAFE_TAC
    MLDSA_NATIVE_KEYPAIR_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL);;
