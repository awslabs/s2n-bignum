(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Verifying a signature of a message (pure ML-DSA): the proof (see          *)
(* verify_65_spec.ml).                                                       *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/verify_65_spec.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_wrap.ml";;

(* ------------------------------------------------------------------------- *)
(* The calls. The frame of 432 bytes is below stackpointer + 12896: 64 bytes *)
(* of saved registers, then the stack pointer is aligned down to 32 bytes    *)
(* (sp = stackpointer + kb, kb = 11488 or 11472, by the proof splitting on   *)
(* whether stackpointer is a multiple of 32 right after the prologue) with   *)
(* the prefix at sp and the canary at sp + 344. The events before a call are *)
(* functions of the variables MLD_VERIFY65_VARS.                             *)
(* ------------------------------------------------------------------------- *)

let MLD_VERIFY65_EXEC = MLDSA_NATIVE_VERIFY_65_CLANG23_O3_MONO_REDUCED_RAM_EXEC;;

let MLD_VERIFY65_VARS =
  [`sig:int64`; `m:int64`; `mlen:num`; `ctx:int64`; `ctxlen:num`;
   `pk:int64`; `sigb:num->byte`; `pkb:num->byte`; `M:num`; `C:num`;
   `guard:int64`; `mf:int64`; `mc:int64`; `pc:num`; `stackpointer:int64`;
   `returnaddress:int64`];;

let MLD_VERIFY65_CALL_TAC name ilist n =
  FULL_CALL_TAC mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc MLD_VERIFY65_EXEC name
   ilist MLD_VERIFY65_VARS n;;

(*** The prologue and the check ctxlen <= 255 ***)

let MLD_VERIFY65_HEAD_TAC =
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC MLD_VERIFY65_EXEC (1--7) THEN
  MLD_WRAP_SYMBUF_TAC `kb:num` THEN MLD_WRAP_SYMBUF_END_TAC `kb:num` THEN
  ARM_STEPS_TAC MLD_VERIFY65_EXEC (8--8) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLD_VERIFY65_EXEC (9--13);;

(*** From the zeroing of the buffer at step k to the return ***)

let MLD_VERIFY65_TAIL_TAC k =
  ARM_STEPS_TAC MLD_VERIFY65_EXEC (k--(k + 14)) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLD_VERIFY65_EXEC ((k + 15)--(k + 33)) THEN
  MLD_CLANG_FINAL_TAC;;

(*** ctxlen > 255: the prefix is rejected and the result is -9 ***)

let MLD_VERIFY65_REJECT_TAC =
  ARM_STEPS_TAC MLD_VERIFY65_EXEC (14--15) THEN MLD_VERIFY65_TAIL_TAC 16;;

(*** The facts about 2 + ctxlen that the callee needs ***)

let MLD_VERIFY65_LEN_TAC =
  SUBGOAL_THEN `ctxlen <= 255` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[GSYM NOT_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `2 + ctxlen < 2 EXP 64` ASSUME_TAC THENL
   [SIMPLE_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `val(word(2 + ctxlen):int64) = 2 + ctxlen` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    SIMPLE_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `val(word ctxlen:int64) = ctxlen` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    SIMPLE_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `word_add (word ctxlen:int64) (word 2) = word(2 + ctxlen)`
  ASSUME_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC];;

(*** The call of verify_internal at step n, with the prefix of plen bytes,
     the number pre, from which the tail follows ***)

let MLD_VERIFY65_INTERNAL_TAC n plen pre =
  MLD_WRAP_GOT_TAC THEN MLD_WRAP_MP_TAC `ctxlen <= 255` THEN
  MLD_CLANG_PREFIX_TAC THEN MLD_CLANG_CALL_FACTS_TAC 12896 12448 THEN
  MLD_VERIFY65_CALL_TAC "H_INTERNAL"
   [`read X0 s`; `read X1 s`; `mlen:num`; `read X3 s`; plen;
    `read X5 s`; `read X6 s`; `sigb:num->byte`; `pkb:num->byte`; `M:num`;
    pre; `guard:int64`; `pc:num`; `read SP s`; `read X30 s`] n THEN
  MLD_VERIFY65_TAIL_TAC (n + 1);;

(*** ctxlen = 0: the prefix is the two zero bytes, nothing to copy; the
     simulation has used ctxlen = 0 for the length in x4 ***)

let MLD_VERIFY65_EMPTY_TAC =
  ARM_STEPS_TAC MLD_VERIFY65_EXEC (14--20) THEN
  MLD_WRAP_GOT_TAC THEN MLD_WRAP_MP_TAC `ctxlen <= 255` THEN
  MLD_CLANG_PREFIX_TAC THEN
  FIRST_X_ASSUM(fun th ->
    ASSUME_TAC(REWRITE_RULE[ADD_CLAUSES; ASSUME `ctxlen = 0`] th)) THEN
  MLD_CLANG_CALL_FACTS_TAC 12896 12448 THEN
  MLD_VERIFY65_CALL_TAC "H_INTERNAL"
   [`read X0 s`; `read X1 s`; `mlen:num`; `read X3 s`; `2`;
    `read X5 s`; `read X6 s`; `sigb:num->byte`; `pkb:num->byte`; `M:num`;
    `num_of_bytelist(mld_domain_separation_prefix 0
       (bytelist_of_num 0 C) [])`;
    `guard:int64`; `pc:num`; `read SP s`; `read X30 s`] 21 THEN
  MLD_VERIFY65_TAIL_TAC 22;;

(*** 0 < ctxlen <= 255: the prefix is copied with memcpy ***)

let MLD_VERIFY65_COPY_TAC =
  ARM_STEPS_TAC MLD_VERIFY65_EXEC (14--25) THEN MLD_CLANG_OR_TAC THEN
  ARM_STEPS_TAC MLD_VERIFY65_EXEC (26--26) THEN
  LIBC_PLT_TAC MLD_VERIFY65_EXEC 26 THEN
  LIBC_SAFE_CALL_TAC "H_MEMCPY" MLD_VERIFY65_EXEC
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`; `C:num`;
    `read X30 s`] (ref MLD_VERIFY65_VARS) 31 THEN
  ARM_STEPS_TAC MLD_VERIFY65_EXEC (32--40) THEN
  MLD_VERIFY65_INTERNAL_TAC 41 `2 + ctxlen`
   `num_of_bytelist(mld_domain_separation_prefix 0
      (bytelist_of_num ctxlen C) [])`;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety, by cases on whether the     *)
(* context is too long and whether it is empty, and, from the prologue on,   *)
(* on whether the stack pointer is a multiple of 32.                         *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_VERIFY_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_VERIFY_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th ->
    let ms,mcp = CONJ_PAIR th in
    MLD_WRAP_ASSUME_CALLEE_TAC
     (MATCH_MP MLDSA_NATIVE_VERIFY_INTERNAL_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL
               (CONJ ms mcp)) "H_INTERNAL" THEN
    MLD_WRAP_ASSUME_CALLEE_TAC
     (REWRITE_RULE[memcpy_full_contract] mcp) "H_MEMCPY") THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(sig:int64) (m:int64) (mlen:num) (ctx:int64) (ctxlen:num) (pk:int64)
     (sigb:num->byte) (pkb:num->byte) (M:num) (C:num) (guard:int64)
     (mf:int64) (mc:int64) (pc:num) (sp:int64) (ra:int64).
     if aligned 32 sp then
       if 255 < ctxlen
       then f_ev_a0 sig m mlen ctx ctxlen pk guard mf mc pc sp ra
       else if ctxlen = 0
       then f_ev_a2 sig m mlen ctx ctxlen pk sigb pkb M C guard mf mc pc sp ra
       else f_ev_a1 sig m mlen ctx ctxlen pk sigb pkb M C guard mf mc pc sp ra
     else
       if 255 < ctxlen
       then f_ev_u0 sig m mlen ctx ctxlen pk guard mf mc pc sp ra
       else if ctxlen = 0
       then f_ev_u2 sig m mlen ctx ctxlen pk sigb pkb M C guard mf mc pc sp ra
       else f_ev_u1 sig m mlen ctx ctxlen pk sigb pkb M C guard mf mc pc sp ra
     :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `sig:int64`; `m:int64`; `mlen:num`; `ctx:int64`;
    `ctxlen:num`; `pk:int64`; `sigb:num->byte`; `pkb:num->byte`; `M:num`;
    `C:num`; `guard:int64`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 12896 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; NONOVERLAPPING_CLAUSES;
              fst MLD_VERIFY65_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MLD_WRAP_FRAME_TAC 12896 [`got_stack_chk_guard:num`; `got_memcpy:num`]
   ((19--23) @ [28; 29]) THEN
  MLD_VERIFY65_HEAD_TAC THEN MLD_CLANG_CTX_TAC THEN
  ASM_CASES_TAC `255 < ctxlen` THEN
  MLD_WRAP_USE_CASE_TAC `255 < ctxlen` [ADD_EQ_0; ARITH_EQ] THEN
  MLD_CLANG_IF `255 < ctxlen` MLD_VERIFY65_REJECT_TAC
   (MLD_VERIFY65_LEN_TAC THEN ASM_CASES_TAC `ctxlen = 0` THEN
    MLD_CLANG_IF `ctxlen = 0` MLD_VERIFY65_EMPTY_TAC
     MLD_VERIFY65_COPY_TAC));;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_VERIFY_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_VERIFY_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT,
  MLD_WRAP_CORRECT_TAC MLDSA_NATIVE_VERIFY_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL);;

let MLDSA_NATIVE_VERIFY_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE = prove
 (MLDSA_NATIVE_VERIFY_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT,
  MLD_WRAP_SAFE_TAC MLDSA_NATIVE_VERIFY_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL);;
