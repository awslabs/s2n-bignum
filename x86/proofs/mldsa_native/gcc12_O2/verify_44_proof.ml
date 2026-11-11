(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Verifying a signature of a message (pure ML-DSA): the proof (see          *)
(* verify_44_spec.ml).                                                       *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/gcc12_O2/verify_44_spec.ml";;
needs "x86/proofs/utils/mldsa_native_verify.ml";;

(* ------------------------------------------------------------------------- *)
(* The calls. The frame is realigned to 32 bytes below the entry RSP (with   *)
(* REALIGN_TAC k = N, as the AND comes first): RBP at bot + 30421, the       *)
(* prefix and RSP at bot + 30021, and mldsa44_verify_internal called with    *)
(* RSP at bot + 29997, its frame the 29997 bytes at bot. The events before a *)
(* call are functions of the variables VER44_VARS, with bot, which           *)
(* REALIGN_UNBOT_TAC expands at the end.                                     *)
(* ------------------------------------------------------------------------- *)

let VER44_EXEC = MLDSA_NATIVE_VERIFY_44_GCC12_O2_EXEC;;

let VER44_VARS =
  [`sig:int64`; `m:int64`; `mlen:num`; `ctx:int64`; `ctxlen:num`;
   `pk:int64`; `sigb:num->byte`; `pkb:num->byte`; `M:num`; `C:num`;
   `mf:int64`; `mc:int64`; `pc:num`; `stackpointer:int64`;
   `returnaddress:int64`; `bot:int64`];;

let VER44_CALL_TAC name ilist n =
  FULL_CALL_TAC mldsa_native_libmldsa_gcc12_O2_mc VER44_EXEC name
   (ilist @ [`pc:num`; `read RSP s`;
             `read (memory :> bytes64 (read RSP s)) s`])
   VER44_VARS n;;

let VER44_TEMPLATE =
  `\(sig:int64) (m:int64) (mlen:num) (ctx:int64) (ctxlen:num) (pk:int64)
    (sigb:num->byte) (pkb:num->byte) (M:num) (C:num) (mf:int64) (mc:int64)
    (pc:num) (stackpointer:int64) (returnaddress:int64).
    if 255 < ctxlen
    then f_ev_rej sig m mlen ctx ctxlen pk mf mc pc stackpointer
          returnaddress
    else f_ev_acc sig m mlen ctx ctxlen pk sigb pkb M C mf mc pc stackpointer
          returnaddress
    :(uarch_event)list`;;

(*** The prologue and the prefix 0 || ctxlen || ctx, with ph = NULL ***)

let VER44_HEAD_TAC =
  ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC VER44_EXEC (1--2) THEN REALIGN_RSP_TAC THEN
  X86_STEPS_TAC VER44_EXEC (3--22) THEN
  VERIF_NULL_TAC [`word_add bot (word 30021):int64`,`332`;
                  `word_add bot (word 29949):int64`,`64`] THEN
  VER44_CALL_TAC "H_PREFIX"
   [`read RDI s`; `read RSI s`; `0`; `read RCX s`; `ctxlen:num`;
    `read R9 s`; `C:num`; `0`] 23 THEN
  VERIF_LET_TAC [] VERIF_PREFIX_THMS;;

(*** From join1 at step k: the zeroing of the prefix and the return ***)

let VER44_TAIL_TAC k =
  X86_STEPS_TAC VER44_EXEC (k--(k + 15)) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN TRY(VERIF_RET_TAC THEN NO_TAC) THEN
  REALIGN_UNBOT_TAC THEN VERIF_EMPTY_REGIONS_TAC THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

(*** ctxlen > 255: the prefix is rejected and the result is -9 ***)

let VER44_REJECT_TAC =
  X86_STEPS_TAC VER44_EXEC (24--27) THEN VER44_TAIL_TAC 28;;

(*** ctxlen <= 255: verification with the prefix of 2 + ctxlen bytes ***)

let VER44_ACCEPT_TAC =
  SUBGOAL_THEN `ctxlen <= 255` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[GSYM NOT_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `2 + ctxlen < 2 EXP 64` ASSUME_TAC THENL
   [SIMPLE_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `val(word(2 + ctxlen):int64) = 2 + ctxlen` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    SIMPLE_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(2 + ctxlen = 0)` ASSUME_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  X86_STEPS_TAC VER44_EXEC (24--34) THEN
  VERIF_MP_TAC `ctxlen <= 255` THEN
  VER44_CALL_TAC "H_INTERNAL"
   [`read RDI s`; `read RSI s`; `mlen:num`; `read RCX s`; `2 + ctxlen`;
    `read R9 s`; `word 0:int64`; `sigb:num->byte`; `pkb:num->byte`; `M:num`;
    `num_of_bytelist(mld_domain_separation_prefix 0
       (bytelist_of_num ctxlen C) [])`] 35 THEN
  X86_STEPS_TAC VER44_EXEC (36--38) THEN
  VER44_TAIL_TAC 39;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety, by cases on whether the     *)
(* context is too long.                                                      *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_VERIFY_44_GCC12_O2_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_VERIFY_44_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th ->
    let ms,mcp = CONJ_PAIR th in
    VERIF_ASSUME_CALLEE_TAC
     (MATCH_MP MLDSA_NATIVE_VERIFY_INTERNAL_44_GCC12_O2_IMAGE_SUBROUTINE_FULL
               ms) "H_INTERNAL" THEN
    VERIF_ASSUME_CALLEE_TAC
     (MATCH_MP
       MLDSA_NATIVE_PREPARE_DOMAIN_SEPARATION_PREFIX_44_GCC12_O2_IMAGE_SUBROUTINE_FULL
       mcp) "H_PREFIX") THEN
  CONCRETIZE_F_EVENTS_TAC VER44_TEMPLATE THEN
  REPEAT META_EXISTS_TAC THEN REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; NONOVERLAPPING_CLAUSES; fst VER44_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REALIGN_TAC 30468 THEN REALIGN_FRAME_TAC 30468 30468 THEN
  REALIGN_NONOV_TAC 30437
   [`sig:int64,2420`; `m:int64,mlen:num`; `ctx:int64,ctxlen:num`;
    `pk:int64,1312`; `word pc:int64,51232`;
    `word(pc + got_memset):int64,8`; `word(pc + got_memcpy):int64,8`;
    `ea:int64,el:num`; `word_add stackpointer (word 30468):int64,8`] THEN
  ENSURES_PRESERVED_TAC "rbx_init" `RBX` THEN
  ENSURES_PRESERVED_TAC "rbp_init" `RBP` THEN
  ENSURES_PRESERVED_TAC "r12_init" `R12` THEN
  ENSURES_PRESERVED_TAC "r13_init" `R13` THEN
  ENSURES_PRESERVED_TAC "r14_init" `R14` THEN
  ENSURES_PRESERVED_TAC "r15_init" `R15` THEN
  VER44_HEAD_TAC THEN ASM_CASES_TAC `255 < ctxlen` THEN
  VERIF_USE_CASE_TAC `255 < ctxlen` [ADD_EQ_0; ARITH_EQ] THENL
   [VER44_REJECT_TAC; VER44_ACCEPT_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_VERIFY_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_VERIFY_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> CORRECT_OF_FULL_TAC
    (MP (SPEC_ALL MLDSA_NATIVE_VERIFY_44_GCC12_O2_IMAGE_SUBROUTINE_FULL) th)));;

let MLDSA_NATIVE_VERIFY_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE = prove
 (MLDSA_NATIVE_VERIFY_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> SAFE_OF_FULL_TAC
    (MP (SPEC_ALL MLDSA_NATIVE_VERIFY_44_GCC12_O2_IMAGE_SUBROUTINE_FULL) th)));;
