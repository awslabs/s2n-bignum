(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Signing a message (pure ML-DSA, randomized): the proof (see               *)
(* signature_65_spec.ml).                                                    *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/gcc12_O2/signature_65_spec.ml";;
needs "arm/proofs/utils/mldsa_native_wrap.ml";;

(* ------------------------------------------------------------------------- *)
(* The calls. The frame of 496 bytes is at stackpointer + 73088, with the    *)
(* prefix in the buffer at stackpointer + kb, kb = 73184 or 73168 (aligned   *)
(* to 32), rnd 352 bytes after it and the canary at + 73576. The events      *)
(* before a call are functions of the variables MLD_SIGN65_VARS (those of    *)
(* the signing being the arguments of its events).                           *)
(* ------------------------------------------------------------------------- *)

let MLD_SIGN65_EXEC = MLDSA_NATIVE_SIGNATURE_65_GCC12_O2_EXEC;;

let MLD_SIGN65_VARS =
  [`sig:int64`; `m:int64`; `mlen:num`; `ctx:int64`; `ctxlen:num`;
   `sk:int64`; `skb:num->byte`; `MU:num`; `RND:num`; `guard:int64`;
   `mf:int64`; `mc:int64`; `mr:int64`; `pc:num`; `stackpointer:int64`;
   `returnaddress:int64`; `kb:num`];;

(*** The call of memset at step n, after its PLT stub ***)

let MLD_SIGN65_MEMSET_TAC n =
  LIBC_PLT_TAC MLD_SIGN65_EXEC (n - 5) THEN
  LIBC_SAFE_CALL_TAC "H_MEMSET" MLD_SIGN65_EXEC
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`;
    `read X30 s`] (ref MLD_SIGN65_VARS) n THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_ZX_0]);;

(*** From join2 (zeroing rnd and the prefix) at step j to the return ***)

let MLD_SIGN65_R_TAC j =
  ARM_STEPS_TAC MLD_SIGN65_EXEC (j--(j + 5)) THEN
  MLD_SIGN65_MEMSET_TAC (j + 10) THEN
  ARM_STEPS_TAC MLD_SIGN65_EXEC ((j + 11)--(j + 11)) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLD_SIGN65_EXEC ((j + 12)--(j + 24));;

(*** From join1 (zeroing the signature) at step k to the return ***)

let MLD_SIGN65_Z_TAC k =
  ARM_STEPS_TAC MLD_SIGN65_EXEC (k--(k + 3)) THEN
  MLD_SIGN65_MEMSET_TAC (k + 8) THEN
  MLD_SIGN65_R_TAC (k + 9);;

(*** The end, with the random bytes rnd (any if randombytes was not run) ***)

let MLD_SIGN65_FINAL_TAC rnd =
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  EXISTS_TAC rnd THEN
  ASM_REWRITE_TAC[MLD_WRAP_RET_DISTINCT; GSYM NOT_LT] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ABBREV_TAC `rho = mld_sk_rho skb` THEN
  ABBREV_TAC `dcl = mld_sign_declass_65 skb MU RND` THEN
  MLD_WRAP_DISCHARGE_TAC;;

(*** The prologue and the prefix 0 || ctxlen || ctx, with ph = NULL ***)

let MLD_SIGN65_HEAD_TAC =
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC MLD_SIGN65_EXEC (1--3) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLD_SIGN65_EXEC (4--7) THEN MLD_WRAP_SYMBUF_TAC `kb:num` THEN
  ARM_STEPS_TAC MLD_SIGN65_EXEC (8--20) THEN
  MLD_WRAP_NULL_TAC [`stackpointer:int64`,`73584`] THEN
  FULL_CALL_TAC mldsa_native_libmldsa_gcc12_O2_mc MLD_SIGN65_EXEC "H_PREFIX"
   [`read X0 s`; `read X1 s`; `0`; `read X3 s`; `ctxlen:num`; `read X5 s`;
    `C:num`; `0`; `pc:num`; `read SP s`; `read X30 s`] MLD_SIGN65_VARS 21 THEN
  MLD_WRAP_LET_TAC [] MLD_WRAP_PREFIX_THMS;;

(*** ctxlen > 255: the prefix is rejected and the result is -9 ***)

let MLD_SIGN65_REJECT_TAC =
  ARM_STEPS_TAC MLD_SIGN65_EXEC (22--24) THEN MLD_WRAP_NORM_TAC THEN
  MLD_SIGN65_Z_TAC 25 THEN MLD_SIGN65_FINAL_TAC `0`;;

(*** Signing succeeds, the result is 0, and the signature is kept ***)

let MLD_SIGN65_OK_TAC =
  ARM_STEPS_TAC MLD_SIGN65_EXEC (45--46) THEN
  MLD_SIGN65_R_TAC 47 THEN MLD_SIGN65_FINAL_TAC `RND:num`;;

(*** Signing fails with -4 and the signature is zeroed ***)

let MLD_SIGN65_FAIL_TAC =
  ARM_STEPS_TAC MLD_SIGN65_EXEC (45--47) THEN
  MLD_SIGN65_Z_TAC 48 THEN MLD_SIGN65_FINAL_TAC `RND:num`;;

(*** randombytes succeeds: signing with the prefix and RND ***)

let MLD_SIGN65_SIGN_TAC =
  ARM_STEPS_TAC MLD_SIGN65_EXEC (34--43) THEN
  MLD_WRAP_GOT_TAC THEN MLD_WRAP_MP_TAC `ctxlen <= 255` THEN
  FIRST_ASSUM(fun th ->
    try STRIP_ASSUME_TAC
         (MP (SPEC `RND:num` th) (ASSUME `RND < 2 EXP 256`))
    with Failure _ -> NO_TAC) THEN
  ASSUME_TAC(INST_TYPE [`:64`,`:M`; `:32`,`:N`] WORD_ZX_0) THEN
  FULL_CALL_TAC mldsa_native_libmldsa_gcc12_O2_mc MLD_SIGN65_EXEC
   "H_INTERNAL"
   [`read X0 s`; `read X1 s`; `mlen:num`; `read X3 s`; `2 + ctxlen`;
    `read X5 s`; `read X6 s`; `read X7 s`; `skb:num->byte`; `M:num`;
    `num_of_bytelist(mld_domain_separation_prefix 0
       (bytelist_of_num ctxlen C) [])`;
    `RND:num`; `MU:num`; `guard:int64`; `pc:num`; `read SP s`; `read X30 s`]
   MLD_SIGN65_VARS 44 THEN
  ASM_CASES_TAC `mld_sign_ok_65 skb MU RND` THEN
  MLD_WRAP_USE_CASE_TAC `mld_sign_ok_65 skb MU RND` [] THENL
   [MLD_SIGN65_OK_TAC; MLD_SIGN65_FAIL_TAC];;

(*** ctxlen <= 255: randombytes into rnd, failing with -3 or signing ***)

let MLD_SIGN65_RANDOM_TAC =
  SUBGOAL_THEN `ctxlen <= 255` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[GSYM NOT_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `2 + ctxlen < 2 EXP 64` ASSUME_TAC THENL
   [SIMPLE_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `val(word(2 + ctxlen):int64) = 2 + ctxlen` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    SIMPLE_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(2 + ctxlen = 0)` ASSUME_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  ARM_STEPS_TAC MLD_SIGN65_EXEC (22--28) THEN MLD_WRAP_NORM_TAC THEN
  LIBC_PLT_TAC MLD_SIGN65_EXEC 28 THEN
  LIBC_SAFE_CALL_TAC "H_RANDOMBYTES" MLD_SIGN65_EXEC
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X30 s`]
   (ref MLD_SIGN65_VARS) 33 THEN
  ABBREV_TAC `rv = read X0 s33` THEN
  MLD_WRAP_RANDOM_TAC `RND:num` `X22` `32` `s33:armstate` THEN
  ASM_CASES_TAC `val(word_zx(rv:int64):int32) = 0` THENL
   [MLD_SIGN65_SIGN_TAC;
    ARM_STEPS_TAC MLD_SIGN65_EXEC (34--34) THEN
    MLD_SIGN65_Z_TAC 35 THEN MLD_SIGN65_FINAL_TAC `0`];;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety, by cases on whether the     *)
(* context is too long, whether randombytes succeeds and whether signing     *)
(* does, which the result shows, and at the end of each on whether the stack *)
(* pointer is a multiple of 32, which gives the address of the buffer.       *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SIGNATURE_65_GCC12_O2_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_SIGNATURE_65_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th ->
    let ms,th' = CONJ_PAIR th in
    let mcp,mrb = CONJ_PAIR th' in
    MLD_WRAP_ASSUME_CALLEE_TAC
     (MATCH_MP MLDSA_NATIVE_SIGNATURE_INTERNAL_65_GCC12_O2_IMAGE_SUBROUTINE_FULL
               (CONJ ms mcp)) "H_INTERNAL" THEN
    MLD_WRAP_ASSUME_CALLEE_TAC
     (MATCH_MP
       MLDSA_NATIVE_PREPARE_DOMAIN_SEPARATION_PREFIX_65_GCC12_O2_IMAGE_SUBROUTINE_FULL
       mcp) "H_PREFIX" THEN
    MLD_WRAP_ASSUME_CALLEE_TAC
     (REWRITE_RULE[memset_full_contract] ms) "H_MEMSET" THEN
    MLD_WRAP_ASSUME_CALLEE_TAC
     (REWRITE_RULE[randombytes_safety_contract] mrb) "H_RANDOMBYTES") THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(sig:int64) (m:int64) (mlen:num) (ctx:int64) (ctxlen:num) (sk:int64)
     (rho:num) (r:int64) (dcl:num->num#num#(num->int32)#(num->byte))
     (guard:int64) (mf:int64) (mc:int64) (mr:int64) (pc:num) (sp:int64)
     (ra:int64).
     if aligned 32 sp then
       if 255 < ctxlen
       then f_ev_a0 sig m mlen ctx ctxlen sk guard mf mc mr pc sp ra
       else if r = word 4294967293
       then f_ev_a1 sig m mlen ctx ctxlen sk guard mf mc mr pc sp ra
       else if r = word 0
       then f_ev_a2 sig m mlen ctx ctxlen sk rho dcl guard mf mc mr pc sp ra
       else f_ev_a3 sig m mlen ctx ctxlen sk rho dcl guard mf mc mr pc sp ra
     else
       if 255 < ctxlen
       then f_ev_u0 sig m mlen ctx ctxlen sk guard mf mc mr pc sp ra
       else if r = word 4294967293
       then f_ev_u1 sig m mlen ctx ctxlen sk guard mf mc mr pc sp ra
       else if r = word 0
       then f_ev_u2 sig m mlen ctx ctxlen sk rho dcl guard mf mc mr pc sp ra
       else f_ev_u3 sig m mlen ctx ctxlen sk rho dcl guard mf mc mr pc sp ra
     :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `sig:int64`; `m:int64`; `mlen:num`; `ctx:int64`;
    `ctxlen:num`; `sk:int64`; `skb:num->byte`; `M:num`; `C:num`; `MU:num`;
    `guard:int64`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 73584 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst MLD_SIGN65_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th ->
    is_eq(concl th) && lhs(concl th) = `MU:num`)) THEN
  MLD_WRAP_FRAME_TAC 73584
   [`got_stack_chk_guard:num`; `got_memset:num`; `got_randombytes:num`]
   (19--26) THEN
  MLD_SIGN65_HEAD_TAC THEN ASM_CASES_TAC `255 < ctxlen` THEN
  MLD_WRAP_USE_CASE_TAC `255 < ctxlen` [ADD_EQ_0; ARITH_EQ] THENL
   [MLD_SIGN65_REJECT_TAC; MLD_SIGN65_RANDOM_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SIGNATURE_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_SIGNATURE_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  MLD_WRAP_CORRECT_TAC
   MLDSA_NATIVE_SIGNATURE_65_GCC12_O2_IMAGE_SUBROUTINE_FULL);;

let MLDSA_NATIVE_SIGNATURE_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE = prove
 (MLDSA_NATIVE_SIGNATURE_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  MLD_WRAP_SAFE_TAC
   MLDSA_NATIVE_SIGNATURE_65_GCC12_O2_IMAGE_SUBROUTINE_FULL);;
