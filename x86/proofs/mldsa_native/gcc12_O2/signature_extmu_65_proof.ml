(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Signing with external mu (randomized): the proof (see                     *)
(* signature_extmu_65_spec.ml).                                              *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/gcc12_O2/signature_extmu_65_spec.ml";;
needs "x86/proofs/utils/mldsa_native_api.ml";;

let SGX65_EXEC = MLDSA_NATIVE_SIGNATURE_EXTMU_65_GCC12_O2_EXEC;;

(* ------------------------------------------------------------------------- *)
(* The frame. After REPEAT_GEN_AND_OFFSET_STACKPTR_TAC, stackpointer is the  *)
(* bottom of the 73212 bytes of stack below the return address, at           *)
(* stackpointer + 73212; the code first aligns RSP to 32 bytes, at bot +     *)
(* 73181 (see utils/mldsa_native_realign.ml), with R10 keeping the original  *)
(* RSP + 8, and then pushes a copy of the return address, RBP (at bot +      *)
(* 73165, the frame pointer), R14, R13, R12, R10 and RBX, and reserves the   *)
(* buffer rnd at bot + 73085, above the two arguments of                     *)
(* mldsa65_signature_internal on the stack (sk and ext = 1), whose frame is  *)
(* the 73061 bytes at bot. The SSE stores that zero rnd through RBP need its *)
(* alignment. The events before a call are functions of the variables        *)
(* SGX65_ALLOWED.                                                            *)
(* ------------------------------------------------------------------------- *)

let SGX65_ALLOWED =
  [`sig:int64`; `mu:int64`; `sk:int64`; `mf:int64`; `mr:int64`; `pc:num`;
   `stackpointer:int64`; `returnaddress:int64`; `bot:int64`];;

(*** To the test of the result of randombytes, with RND its bytes ***)

let SGX65_HEAD_TAC =
  FULL_INIT_TAC THEN
  X86_STEPS_TAC SGX65_EXEC (1--2) THEN REALIGN_RSP_TAC THEN
  X86_STEPS_TAC SGX65_EXEC (3--18) THEN
  LIBC_PLT_TAC SGX65_EXEC (layout "plt_randombytes")
   (layout "got_randombytes") 18 THEN
  LIBC_FULL_CALL_TAC "H_RANDOMBYTES" SGX65_EXEC
   [`e:(uarch_event)list`; `read RDI s`; `read RSI s`; `read RSP s`;
    `read (memory :> bytes64 (read RSP s)) s`]
   (ref SGX65_ALLOWED) 20 THEN
  ABBREV_TAC `rv = read RAX s20` THEN
  API_RANDOM_TAC `RND:num` `word_add bot (word 73085):int64` 32
   `s20:x86state`;;

(*** randombytes succeeds: signing with RND, mlen = 64 and ext = 1, with   ***)
(*** pre = NULL and prelen = 0, MU being the message mu                    ***)

let SGX65_OK_TAC =
  X86_STEPS_TAC SGX65_EXEC (21--31) THEN
  API_NULL_TAC [`sig:int64`,`3309`; `bot:int64`,`73061`] THEN
  FIRST_ASSUM(fun th ->
    try STRIP_ASSUME_TAC
         (MP (SPEC `RND:num` th) (ASSUME `RND < 2 EXP 256`))
    with Failure _ -> NO_TAC) THEN
  SUBGOAL_THEN `~(word_zx (word 1:int64):int32 = word 0)` ASSUME_TAC THENL
   [CONV_TAC WORD_REDUCE_CONV; ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP API_READ_BYTES_BOUND o
    check (fun th -> concl th = `read (memory :> bytes(mu,64)) s31 = MU`)) THEN
  SUBGOAL_THEN `MU MOD 2 EXP 512 = MU` ASSUME_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN
    RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FULL_CALL_TAC mldsa_native_libmldsa_gcc12_O2_mc SGX65_EXEC "H_INTERNAL"
   [`read RDI s`; `read RSI s`; `64`; `read RCX s`; `0`; `read R9 s`;
    `sk:int64`; `word 1:int64`; `skb:num->byte`; `MU:num`; `0`;
    `RND:num`; `MU:num`; `pc:num`; `read RSP s`;
    `read (memory :> bytes64 (read RSP s)) s`]
   SGX65_ALLOWED 32 THEN
  X86_STEPS_TAC SGX65_EXEC (33--46) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `RND:num` THEN
  ASM_REWRITE_TAC[API_SIGN_DISTINCT; API_SIGN_RET] THEN
  ABBREV_TAC `rho = mld_sk_rho skb` THEN
  ABBREV_TAC `dcl = mld_sign_declass_65 skb MU RND` THEN
  REALIGN_UNBOT_TAC THEN API_EMPTY_REGIONS_TAC THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

(*** randombytes fails: the return of -3, RND any number ***)

let SGX65_FAIL_TAC =
  X86_STEPS_TAC SGX65_EXEC (21--36) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `0` THEN ASM_REWRITE_TAC[API_SIGN_DISTINCT] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REALIGN_UNBOT_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety, by cases on whether         *)
(* randombytes succeeds, which the result shows (signing returns 0 or -4).   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SIGNATURE_EXTMU_65_GCC12_O2_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_SIGNATURE_EXTMU_65_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th ->
    let ms,mrb = CONJ_PAIR th in
    API_ASSUME_CALLEE_TAC
     (MATCH_MP
       MLDSA_NATIVE_SIGNATURE_INTERNAL_65_GCC12_O2_IMAGE_SUBROUTINE_FULL
       ms) "H_INTERNAL" THEN
    API_ASSUME_CALLEE_TAC
     (REWRITE_RULE[randombytes_safety_contract] mrb) "H_RANDOMBYTES") THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(sig:int64) (mu:int64) (sk:int64) (rho:num) (r:int64)
     (dcl:num->num#num#(num->int32)#(num->byte)) (mf:int64) (mr:int64)
     (pc:num) (stackpointer:int64) (returnaddress:int64).
     if r = word 4294967293
     then f_ev_0 sig mu sk mf mr pc stackpointer returnaddress
     else f_ev_1 sig mu sk rho dcl mf mr pc stackpointer returnaddress
     :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst SGX65_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REALIGN_TAC 73212 THEN REALIGN_FRAME_TAC 73212 73212 THEN
  REALIGN_NONOV_TAC 73181
   [`sig:int64,3309`; `mu:int64,64`; `sk:int64,4032`;
    `word pc:int64,libmldsa_size`; `word(pc + got_memset):int64,8`;
    `word(pc + got_randombytes):int64,8`; `ea:int64,el:num`;
    `word_add stackpointer (word 73212):int64,8`] THEN
  REALIGN_ALIGNED_TAC [73165] THEN
  ENSURES_PRESERVED_TAC "rbx_init" `RBX` THEN
  ENSURES_PRESERVED_TAC "rbp_init" `RBP` THEN
  ENSURES_PRESERVED_TAC "r12_init" `R12` THEN
  ENSURES_PRESERVED_TAC "r13_init" `R13` THEN
  ENSURES_PRESERVED_TAC "r14_init" `R14` THEN
  SGX65_HEAD_TAC THEN
  ASM_CASES_TAC `val(word_zx(rv:int64):int32) = 0` THENL
   [SGX65_OK_TAC; SGX65_FAIL_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SIGNATURE_EXTMU_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_SIGNATURE_EXTMU_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  API_SIGN_CORRECT_TAC
   MLDSA_NATIVE_SIGNATURE_EXTMU_65_GCC12_O2_IMAGE_SUBROUTINE_FULL);;

let MLDSA_NATIVE_SIGNATURE_EXTMU_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE = prove
 (MLDSA_NATIVE_SIGNATURE_EXTMU_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  API_SIGN_SAFE_TAC
   MLDSA_NATIVE_SIGNATURE_EXTMU_65_GCC12_O2_IMAGE_SUBROUTINE_FULL);;
