(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Signing a message (pure ML-DSA, randomized): the proof (see               *)
(* signature_44_spec.ml).                                                    *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/gcc12_O2/signature_44_spec.ml";;
needs "x86/proofs/utils/mldsa_native_api.ml";;
needs "x86/proofs/utils/mldsa_native_signing.ml";;

let SG44_EXEC = MLDSA_NATIVE_SIGNATURE_44_GCC12_O2_EXEC;;

(* ------------------------------------------------------------------------- *)
(* The frame. After REPEAT_GEN_AND_OFFSET_STACKPTR_TAC, stackpointer is the  *)
(* bottom of the 50036 bytes of stack below the return address, at           *)
(* stackpointer + 50036; the code first aligns RSP to 32 bytes, at bot +     *)
(* 50005 (see utils/mldsa_native_realign.ml), with R10 keeping the original  *)
(* RSP + 8, and then pushes a copy of the return address, RBP (at bot +      *)
(* 49989, the frame pointer), R15, R14, R13, R12, R10 and RBX, and reserves  *)
(* the prefix at bot + 49589, rnd at bot + 49557, the saved m at bot + 49549 *)
(* and the saved length of the prefix at bot + 49541, with RSP at bot +      *)
(* 49525. The calls of the prefix and randombytes have their return          *)
(* addresses at bot + 49517 (the frame of the prefix is the 64 bytes below   *)
(* it), and that of mldsa44_signature_internal, above its two arguments on   *)
(* the stack (sk and ext = 0), at bot + 49501, its frame the 49501 bytes at  *)
(* bot. The SSE stores that zero rnd through RBP need its alignment. The     *)
(* events before a call are functions of the variables SG44_VARS, with bot,  *)
(* which REALIGN_UNBOT_TAC expands at the end.                               *)
(* ------------------------------------------------------------------------- *)

let SG44_VARS =
  [`sig:int64`; `m:int64`; `mlen:num`; `ctx:int64`; `ctxlen:num`;
   `sk:int64`; `skb:num->byte`; `M:num`; `C:num`; `MU:num`; `RND:num`;
   `mf:int64`; `mc:int64`; `mr:int64`; `pc:num`; `stackpointer:int64`;
   `returnaddress:int64`; `bot:int64`];;

let SG44_CALL_TAC name ilist n =
  FULL_CALL_TAC mldsa_native_libmldsa_gcc12_O2_mc SG44_EXEC name
   (ilist @ [`pc:num`; `read RSP s`;
             `read (memory :> bytes64 (read RSP s)) s`])
   SG44_VARS n;;

(*** From join2 at step j: the zeroing of rnd and of the prefix, and the   ***)
(*** return                                                                ***)

let SG44_R_TAC j = X86_STEPS_TAC SG44_EXEC (j--(j + 18));;

(*** From join1 at step k: the zeroing of the signature (see               ***)
(*** utils/mldsa_native_signing.ml), and then join2                        ***)

let SG44_Z_TAC k =
  X86_STEPS_TAC SG44_EXEC (k--(k + 8)) THEN
  SIGN_STOS_PREP_TAC `sig:int64` 2420 THEN
  SIGN_STOS_STEP_TAC SG44_EXEC (k + 9) THEN
  SIGN_STOS_DONE_TAC `sig:int64` 2420 (k + 9) THEN
  SG44_R_TAC (k + 10);;

(*** The end of a path, with the random bytes rnd (any number if           ***)
(*** randombytes was not called), and the events, with the count of the    ***)
(*** REP STOSQ that zeroes the signature generalized for the bounds of its ***)
(*** accesses                                                              ***)

let SG44_DISCHARGE_TAC =
  SAFE_META_EXISTS_TAC allowed_vars_e THEN
  CONJ_TAC THENL [EXISTS_E2_TAC allowed_vars_e; ALL_TAC] THEN
  W(fun (asl,w) ->
    (if is_conj w then CONJ_TAC THENL [FULL_UNIFY_F_EVENTS_TAC; ALL_TAC]
     else ALL_TAC) THEN
    SIGN_STOS_GEN_TAC `sig:int64` 2420 THEN
    DISCHARGE_MEMACCESS_INBOUNDS_TAC);;

let SG44_FINAL_TAC rnd =
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  EXISTS_TAC rnd THEN
  ASM_REWRITE_TAC[API_SIGN_DISTINCT; API_SIGN_RET; GSYM NOT_LT] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REPEAT CONJ_TAC THEN
  TRY(MATCH_MP_TAC SIGN_BYTES8_ZERO THEN FIRST_ASSUM ACCEPT_TAC THEN
      NO_TAC) THEN
  ABBREV_TAC `rho = mld_sk_rho skb` THEN
  ABBREV_TAC `dcl = mld_sign_declass_44 skb MU RND` THEN
  REALIGN_UNBOT_TAC THEN API_EMPTY_REGIONS_TAC THEN
  SG44_DISCHARGE_TAC;;

(*** The prologue and the prefix 0 || ctxlen || ctx, for hashalg 0, with   ***)
(*** ph NULL and phlen 0                                                   ***)

let SG44_HEAD_TAC =
  FULL_INIT_TAC THEN
  X86_STEPS_TAC SG44_EXEC (1--2) THEN REALIGN_RSP_TAC THEN
  X86_STEPS_TAC SG44_EXEC (3--22) THEN
  API_NULL_TAC [`word_add bot (word 49589):int64`,`332`;
                `word_add bot (word 49453):int64`,`64`] THEN
  SG44_CALL_TAC "H_PREFIX"
   [`read RDI s`; `read RSI s`; `0`; `read RCX s`; `ctxlen:num`;
    `read R9 s`; `C:num`; `0`] 23 THEN
  API_LET_TAC [] API_PREFIX_THMS;;

(*** ctxlen > 255: the prefix is rejected and the result is -9 ***)

let SG44_REJECT_TAC =
  X86_STEPS_TAC SG44_EXEC (24--28) THEN SG44_Z_TAC 29 THEN
  SG44_FINAL_TAC `0`;;

(*** randombytes succeeds: signing the message with the prefix (of 2 +     ***)
(*** ctxlen bytes) and RND, ext = 0, and the zeroing of the signature if   ***)
(*** that fails                                                            ***)

let SG44_SIGN_TAC =
  X86_STEPS_TAC SG44_EXEC (33--44) THEN
  API_MP_TAC `ctxlen <= 255` THEN
  FIRST_ASSUM(fun th ->
    try STRIP_ASSUME_TAC
         (MP (SPEC `RND:num` th) (ASSUME `RND < 2 EXP 256`))
    with Failure _ -> NO_TAC) THEN
  ASSUME_TAC(INST_TYPE [`:64`,`:M`; `:32`,`:N`] WORD_ZX_0) THEN
  API_NULL_TAC [`sig:int64`,`2420`; `bot:int64`,`49501`] THEN
  SG44_CALL_TAC "H_INTERNAL"
   [`read RDI s`; `read RSI s`; `mlen:num`; `read RCX s`; `2 + ctxlen`;
    `read R9 s`; `sk:int64`; `word 0:int64`; `skb:num->byte`; `M:num`;
    `num_of_bytelist(mld_domain_separation_prefix 0
       (bytelist_of_num ctxlen C) [])`;
    `RND:num`; `MU:num`] 45 THEN
  ASM_CASES_TAC `mld_sign_ok_44 skb MU RND` THEN
  API_USE_CASE_TAC `mld_sign_ok_44 skb MU RND` [] THENL
   [X86_STEPS_TAC SG44_EXEC (46--50) THEN SG44_R_TAC 51 THEN
    SG44_FINAL_TAC `RND:num`;
    X86_STEPS_TAC SG44_EXEC (46--51) THEN SG44_Z_TAC 52 THEN
    SG44_FINAL_TAC `RND:num`];;

(*** ctxlen <= 255: the prefix of 2 + ctxlen bytes, apart from what is     ***)
(*** written below it before the signing; randombytes into rnd, failing    ***)
(*** with -3, or signing                                                   ***)

let SG44_PFX = `word_add bot (word 49589):int64,2 + ctxlen`;;

let SG44_RANDOM_TAC =
  SUBGOAL_THEN `ctxlen <= 255` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[GSYM NOT_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `2 + ctxlen < 2 EXP 64` ASSUME_TAC THENL
   [SIMPLE_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `val(word(2 + ctxlen):int64) = 2 + ctxlen` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    SIMPLE_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(2 + ctxlen = 0)` ASSUME_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `2 + ctxlen <= 332` ASSUME_TAC THENL
   [SIMPLE_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY (fun r -> API_DRIVER_TAC
    (mk_comb(mk_comb(`nonoverlapping:int64#num->int64#num->bool`,r),
             SG44_PFX))
    (ASSUME `2 + ctxlen <= 332`))
   [`word_add bot (word 49541):int64,8`; `word_add bot (word 49557):int64,32`;
    `word_add bot (word 49517):int64,8`; `word_add bot (word 49509):int64,8`;
    `bot:int64,49501`; `sig:int64,2420`] THEN
  X86_STEPS_TAC SG44_EXEC (24--30) THEN
  LIBC_PLT_TAC SG44_EXEC (layout "plt_randombytes")
   (layout "got_randombytes") 30 THEN
  LIBC_FULL_CALL_TAC "H_RANDOMBYTES" SG44_EXEC
   [`e:(uarch_event)list`; `read RDI s`; `read RSI s`; `read RSP s`;
    `read (memory :> bytes64 (read RSP s)) s`]
   (ref SG44_VARS) 32 THEN
  ABBREV_TAC `rv = read RAX s32` THEN
  API_RANDOM_TAC `RND:num` `word_add bot (word 49557):int64` 32
   `s32:x86state` THEN
  ASM_CASES_TAC `val(word_zx(rv:int64):int32) = 0` THENL
   [SG44_SIGN_TAC;
    X86_STEPS_TAC SG44_EXEC (33--35) THEN SG44_Z_TAC 36 THEN
    SG44_FINAL_TAC `0`];;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety, by cases on whether the     *)
(* context is too long, whether randombytes succeeds and whether signing     *)
(* does, which the result shows.                                             *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SIGNATURE_44_GCC12_O2_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_SIGNATURE_44_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th ->
    let ms,th' = CONJ_PAIR th in
    let mcp,mrb = CONJ_PAIR th' in
    API_ASSUME_CALLEE_TAC
     (MATCH_MP
       MLDSA_NATIVE_SIGNATURE_INTERNAL_44_GCC12_O2_IMAGE_SUBROUTINE_FULL
       ms) "H_INTERNAL" THEN
    API_ASSUME_CALLEE_TAC
     (MATCH_MP
       MLDSA_NATIVE_PREPARE_DOMAIN_SEPARATION_PREFIX_44_GCC12_O2_IMAGE_SUBROUTINE_FULL
       mcp) "H_PREFIX" THEN
    API_ASSUME_CALLEE_TAC
     (REWRITE_RULE[randombytes_safety_contract] mrb) "H_RANDOMBYTES") THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(sig:int64) (m:int64) (mlen:num) (ctx:int64) (ctxlen:num) (sk:int64)
     (rho:num) (r:int64) (dcl:num->num#num#(num->int32)#(num->byte))
     (mf:int64) (mc:int64) (mr:int64) (pc:num) (stackpointer:int64)
     (returnaddress:int64).
     if 255 < ctxlen
     then f_ev_0 sig m mlen ctx ctxlen sk mf mc mr pc stackpointer
           returnaddress
     else if r = word 4294967293
     then f_ev_1 sig m mlen ctx ctxlen sk mf mc mr pc stackpointer
           returnaddress
     else if r = word 0
     then f_ev_2 sig m mlen ctx ctxlen sk rho dcl mf mc mr pc stackpointer
           returnaddress
     else f_ev_3 sig m mlen ctx ctxlen sk rho dcl mf mc mr pc stackpointer
           returnaddress
     :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst SG44_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th ->
    is_eq(concl th) && lhs(concl th) = `MU:num`)) THEN
  REALIGN_TAC 50036 THEN REALIGN_FRAME_TAC 50036 50036 THEN
  REALIGN_NONOV_TAC 50005
   [`sig:int64,2420`; `m:int64,mlen:num`; `ctx:int64,ctxlen:num`;
    `sk:int64,2560`; `word pc:int64,libmldsa_size`;
    `word(pc + got_memset):int64,8`; `word(pc + got_memcpy):int64,8`;
    `word(pc + got_randombytes):int64,8`; `ea:int64,el:num`;
    `word_add stackpointer (word 50036):int64,8`] THEN
  REALIGN_ALIGNED_TAC [49989] THEN
  ENSURES_PRESERVED_TAC "rbx_init" `RBX` THEN
  ENSURES_PRESERVED_TAC "rbp_init" `RBP` THEN
  ENSURES_PRESERVED_TAC "r12_init" `R12` THEN
  ENSURES_PRESERVED_TAC "r13_init" `R13` THEN
  ENSURES_PRESERVED_TAC "r14_init" `R14` THEN
  ENSURES_PRESERVED_TAC "r15_init" `R15` THEN
  SG44_HEAD_TAC THEN
  ASM_CASES_TAC `255 < ctxlen` THEN
  API_USE_CASE_TAC `255 < ctxlen` [ADD_EQ_0; ARITH_EQ] THENL
   [SG44_REJECT_TAC; SG44_RANDOM_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SIGNATURE_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_SIGNATURE_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  API_SIGN_CORRECT_TAC
   MLDSA_NATIVE_SIGNATURE_44_GCC12_O2_IMAGE_SUBROUTINE_FULL);;

let MLDSA_NATIVE_SIGNATURE_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE = prove
 (MLDSA_NATIVE_SIGNATURE_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  API_SIGN_SAFE_TAC
   MLDSA_NATIVE_SIGNATURE_44_GCC12_O2_IMAGE_SUBROUTINE_FULL);;
