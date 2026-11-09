(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Verifying a signature of a message (pure ML-DSA): the proof (see          *)
(* verify_87_spec.ml).                                                       *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/gcc12_O2/verify_87_spec.ml";;
needs "arm/proofs/utils/mldsa_native_wrap.ml";;

(* ------------------------------------------------------------------------- *)
(* The calls. The frame of 416 bytes is at stackpointer + 74224, with the    *)
(* prefix in the buffer at stackpointer + kb, kb = 74272 or 74288 (aligned   *)
(* to 32), and the canary at + 74632. The events before a call are functions *)
(* of the variables MLD_VERIFY87_VARS.                                       *)
(* ------------------------------------------------------------------------- *)

let MLD_VERIFY87_EXEC = MLDSA_NATIVE_VERIFY_87_GCC12_O2_EXEC;;

let MLD_VERIFY87_VARS =
  [`sig:int64`; `m:int64`; `mlen:num`; `ctx:int64`; `ctxlen:num`;
   `pk:int64`; `sigb:num->byte`; `pkb:num->byte`; `M:num`; `C:num`;
   `guard:int64`; `mf:int64`; `mc:int64`; `pc:num`; `stackpointer:int64`;
   `returnaddress:int64`; `kb:num`];;

let MLD_VERIFY87_CALL_TAC name ilist n =
  FULL_CALL_TAC mldsa_native_libmldsa_gcc12_O2_mc MLD_VERIFY87_EXEC name
   ilist MLD_VERIFY87_VARS n;;

(*** The prologue and the prefix 0 || ctxlen || ctx, with ph = NULL ***)

let MLD_VERIFY87_HEAD_TAC =
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC MLD_VERIFY87_EXEC (1--3) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLD_VERIFY87_EXEC (4--7) THEN MLD_WRAP_SYMBUF_TAC `kb:num` THEN
  ARM_STEPS_TAC MLD_VERIFY87_EXEC (8--18) THEN
  MLD_WRAP_NULL_TAC [`stackpointer:int64`,`74640`] THEN
  MLD_VERIFY87_CALL_TAC "H_PREFIX"
   [`read X0 s`; `read X1 s`; `0`; `read X3 s`; `ctxlen:num`; `read X5 s`;
    `C:num`; `0`; `pc:num`; `read SP s`; `read X30 s`] 19 THEN
  MLD_WRAP_LET_TAC [] MLD_WRAP_PREFIX_THMS;;

(*** From join1 at step k: the zeroing of the prefix and the return ***)

let MLD_VERIFY87_TAIL_TAC k =
  ARM_STEPS_TAC MLD_VERIFY87_EXEC (k--(k + 3)) THEN
  LIBC_PLT_TAC MLD_VERIFY87_EXEC (k + 3) THEN
  LIBC_SAFE_CALL_TAC "H_MEMSET" MLD_VERIFY87_EXEC
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`;
    `read X30 s`] (ref MLD_VERIFY87_VARS) (k + 8) THEN
  ARM_STEPS_TAC MLD_VERIFY87_EXEC ((k + 9)--(k + 9)) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLD_VERIFY87_EXEC ((k + 10)--(k + 20)) THEN
  MLD_WRAP_FINAL_TAC;;

(*** ctxlen > 255: the prefix is rejected and the result is -9 ***)

let MLD_VERIFY87_REJECT_TAC =
  ARM_STEPS_TAC MLD_VERIFY87_EXEC (20--22) THEN
  MLD_VERIFY87_TAIL_TAC 23;;

(*** ctxlen <= 255: verification with the prefix of 2 + ctxlen bytes ***)

let MLD_VERIFY87_ACCEPT_TAC =
  SUBGOAL_THEN `ctxlen <= 255` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[GSYM NOT_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `2 + ctxlen < 2 EXP 64` ASSUME_TAC THENL
   [SIMPLE_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `val(word(2 + ctxlen):int64) = 2 + ctxlen` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    SIMPLE_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(2 + ctxlen = 0)` ASSUME_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  ARM_STEPS_TAC MLD_VERIFY87_EXEC (20--28) THEN
  MLD_WRAP_GOT_TAC THEN MLD_WRAP_MP_TAC `ctxlen <= 255` THEN
  MLD_VERIFY87_CALL_TAC "H_INTERNAL"
   [`read X0 s`; `read X1 s`; `mlen:num`; `read X3 s`; `2 + ctxlen`;
    `read X5 s`; `read X6 s`; `sigb:num->byte`; `pkb:num->byte`; `M:num`;
    `num_of_bytelist(mld_domain_separation_prefix 0
       (bytelist_of_num ctxlen C) [])`;
    `guard:int64`; `pc:num`; `read SP s`; `read X30 s`] 29 THEN
  ARM_STEPS_TAC MLD_VERIFY87_EXEC (30--30) THEN
  MLD_VERIFY87_TAIL_TAC 31;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety, by cases on whether the     *)
(* context is too long, and at the end of each on whether the stack pointer  *)
(* is a multiple of 32, which gives the address of the buffer.               *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_VERIFY_87_GCC12_O2_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_VERIFY_87_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th ->
    let ms,mcp = CONJ_PAIR th in
    MLD_WRAP_ASSUME_CALLEE_TAC
     (MATCH_MP MLDSA_NATIVE_VERIFY_INTERNAL_87_GCC12_O2_IMAGE_SUBROUTINE_FULL
               ms) "H_INTERNAL" THEN
    MLD_WRAP_ASSUME_CALLEE_TAC
     (MATCH_MP
       MLDSA_NATIVE_PREPARE_DOMAIN_SEPARATION_PREFIX_87_GCC12_O2_IMAGE_SUBROUTINE_FULL
       mcp) "H_PREFIX" THEN
    MLD_WRAP_ASSUME_CALLEE_TAC
     (REWRITE_RULE[memset_ret_full_contract] ms) "H_MEMSET") THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(sig:int64) (m:int64) (mlen:num) (ctx:int64) (ctxlen:num) (pk:int64)
     (sigb:num->byte) (pkb:num->byte) (M:num) (C:num) (guard:int64)
     (mf:int64) (mc:int64) (pc:num) (sp:int64) (ra:int64).
     if aligned 32 sp then
       if 255 < ctxlen
       then f_ev_a0 sig m mlen ctx ctxlen pk guard mf mc pc sp ra
       else f_ev_a1 sig m mlen ctx ctxlen pk sigb pkb M C guard mf mc pc sp ra
     else
       if 255 < ctxlen
       then f_ev_u0 sig m mlen ctx ctxlen pk guard mf mc pc sp ra
       else f_ev_u1 sig m mlen ctx ctxlen pk sigb pkb M C guard mf mc pc sp ra
     :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `sig:int64`; `m:int64`; `mlen:num`; `ctx:int64`;
    `ctxlen:num`; `pk:int64`; `sigb:num->byte`; `pkb:num->byte`; `M:num`;
    `C:num`; `guard:int64`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 74640 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; NONOVERLAPPING_CLAUSES;
              fst MLD_VERIFY87_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MLD_WRAP_FRAME_TAC 74640 [`got_stack_chk_guard:num`; `got_memset:num`]
   (19--23) THEN
  MLD_VERIFY87_HEAD_TAC THEN ASM_CASES_TAC `255 < ctxlen` THEN
  MLD_WRAP_USE_CASE_TAC `255 < ctxlen` [ADD_EQ_0; ARITH_EQ] THENL
   [MLD_VERIFY87_REJECT_TAC; MLD_VERIFY87_ACCEPT_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_VERIFY_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_VERIFY_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  MLD_WRAP_CORRECT_TAC MLDSA_NATIVE_VERIFY_87_GCC12_O2_IMAGE_SUBROUTINE_FULL);;

let MLDSA_NATIVE_VERIFY_87_GCC12_O2_IMAGE_SUBROUTINE_SAFE = prove
 (MLDSA_NATIVE_VERIFY_87_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  MLD_WRAP_SAFE_TAC MLDSA_NATIVE_VERIFY_87_GCC12_O2_IMAGE_SUBROUTINE_FULL);;
