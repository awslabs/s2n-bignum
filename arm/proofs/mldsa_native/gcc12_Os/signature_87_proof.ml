(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Signing a message (pure ML-DSA, randomized): the proof (see               *)
(* signature_87_spec.ml).                                                    *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/gcc12_Os/signature_87_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/zeroize_6_spec.ml";;
needs "arm/proofs/utils/mldsa_native_wrap.ml";;
needs "arm/proofs/utils/mldsa_native_matrix.ml";;
needs "arm/proofs/utils/mldsa_native_hash.ml";;
needs "arm/proofs/utils/mldsa_native_signing.ml";;

(* ------------------------------------------------------------------------- *)
(* The bytes of a region that is zero (mld_zeroize leaves a number 0).       *)
(* ------------------------------------------------------------------------- *)

let SIGN_BYTES_ZERO = prove
 (`!(a:int64) n (s:armstate).
        read (memory :> bytes(a,n)) s = 0
        ==> !j. j < n
                ==> read (memory :> bytes8 (word_add a (word j))) s = word 0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`a:int64`; `n:num`; `0`; `j:num`; `s:armstate`]
               READ_MEMORY_BYTES8_OF_NUM) THEN
  ASM_SIMP_TAC[DIV_0; MOD_0; ARITH_RULE `j + 1 <= n <=> j < n`] THEN
  CONV_TAC WORD_REDUCE_CONV);;

(* ------------------------------------------------------------------------- *)
(* The calls. The frame of 480 bytes is at stackpointer + 112096, with the   *)
(* prefix in the buffer at stackpointer + kb, kb = 112176 or 112160 (aligned *)
(* to 32), rnd 352 bytes after it and the canary at + 112568. The events     *)
(* before a call are functions of the variables MLD_SIGN87_VARS (those of    *)
(* the signing being the arguments of its events).                           *)
(* ------------------------------------------------------------------------- *)

let MLD_SIGN87_EXEC = MLDSA_NATIVE_SIGNATURE_87_GCC12_OS_EXEC;;

let MLD_SIGN87_VARS =
  [`sig:int64`; `m:int64`; `mlen:num`; `ctx:int64`; `ctxlen:num`;
   `sk:int64`; `skb:num->byte`; `MU:num`; `RND:num`; `guard:int64`;
   `mf:int64`; `mc:int64`; `mr:int64`; `pc:num`; `stackpointer:int64`;
   `returnaddress:int64`; `kb:num`];;

(*** The call of mld_zeroize on len bytes at X0, whose arguments are set by
     the steps k, k + 1 and k + 2 (the call is at step k + 3) ***)

let MLD_SIGN87_ZERO_TAC k len =
  ARM_STEPS_TAC MLD_SIGN87_EXEC (k--(k + 2)) THEN
  FULL_CALL_TAC mldsa_native_libmldsa_gcc12_Os_mc MLD_SIGN87_EXEC "H_ZERO"
   [`read X0 s`; mk_small_numeral len; `pc:num`; `read SP s`; `read X30 s`]
   MLD_SIGN87_VARS (k + 3);;

(*** From the zeroing of rnd (32 bytes) at step j to the return ***)

let MLD_SIGN87_R_TAC j =
  MLD_SIGN87_ZERO_TAC j 32 THEN MLD_SIGN87_ZERO_TAC (j + 4) 332 THEN
  ARM_STEPS_TAC MLD_SIGN87_EXEC ((j + 8)--(j + 8)) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLD_SIGN87_EXEC ((j + 9)--(j + 20));;

(*** From the zeroing of the signature at step k to the return ***)

let MLD_SIGN87_Z_TAC k =
  MLD_SIGN87_ZERO_TAC k 4627 THEN MLD_SIGN87_R_TAC (k + 4);;

(*** The signature, if it was zeroed by mld_zeroize, is zero byte by byte ***)

let MLD_SIGN87_ZSIG_TAC =
  TRY(CONJ_TAC THENL
   [X_GEN_TAC `t:num` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `t:num` o MATCH_MP SIGN_BYTES_ZERO o check
     (can (term_match [`sig:int64`] `read (memory :> bytes(sig,4627)) s = 0`) o
      concl)) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC]);;

(*** The end, with the random bytes rnd (any if randombytes was not run) ***)

let MLD_SIGN87_FINAL_TAC rnd =
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  EXISTS_TAC rnd THEN
  ASM_REWRITE_TAC[MLD_WRAP_RET_DISTINCT; SIGN_RET_ZX; GSYM NOT_LT] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ABBREV_TAC `rho = mld_sk_rho skb` THEN
  ABBREV_TAC `dcl = mld_sign_declass_87 skb MU RND` THEN
  MLD_SIGN87_ZSIG_TAC THEN MLD_WRAP_DISCHARGE_TAC;;

(*** The prologue and the prefix 0 || ctxlen || ctx, with ph = NULL ***)

let MLD_SIGN87_HEAD_TAC =
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC MLD_SIGN87_EXEC (1--5) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLD_SIGN87_EXEC (6--8) THEN MLD_WRAP_SYMBUF_TAC `kb:num` THEN
  ARM_STEPS_TAC MLD_SIGN87_EXEC (9--20) THEN
  MLD_WRAP_NULL_TAC [`stackpointer:int64`,`112576`] THEN
  FULL_CALL_TAC mldsa_native_libmldsa_gcc12_Os_mc MLD_SIGN87_EXEC "H_PREFIX"
   [`read X0 s`; `read X1 s`; `0`; `read X3 s`; `ctxlen:num`; `read X5 s`;
    `C:num`; `0`; `pc:num`; `read SP s`; `read X30 s`] MLD_SIGN87_VARS 21 THEN
  MLD_WRAP_LET_TAC [] MLD_WRAP_PREFIX_THMS;;

(*** ctxlen > 255: the prefix is rejected and the result is -9 ***)

let MLD_SIGN87_REJECT_TAC =
  ARM_STEPS_TAC MLD_SIGN87_EXEC (22--24) THEN MLD_WRAP_NORM_TAC THEN
  MLD_SIGN87_Z_TAC 25 THEN MLD_SIGN87_FINAL_TAC `0`;;

(*** Signing succeeds, the result is 0, and the signature is kept ***)

let MLD_SIGN87_OK_TAC =
  ARM_STEPS_TAC MLD_SIGN87_EXEC (43--44) THEN
  MLD_SIGN87_R_TAC 45 THEN MLD_SIGN87_FINAL_TAC `RND:num`;;

(*** Signing fails with -4 and the signature is zeroed ***)

let MLD_SIGN87_FAIL_TAC =
  ARM_STEPS_TAC MLD_SIGN87_EXEC (43--44) THEN
  MLD_SIGN87_Z_TAC 45 THEN MLD_SIGN87_FINAL_TAC `RND:num`;;

(*** randombytes succeeds: signing with the prefix and RND ***)

let MLD_SIGN87_SIGN_TAC =
  ARM_STEPS_TAC MLD_SIGN87_EXEC (32--41) THEN
  MLD_WRAP_GOT_TAC THEN MLD_WRAP_MP_TAC `ctxlen <= 255` THEN
  FIRST_ASSUM(fun th ->
    try STRIP_ASSUME_TAC
         (MP (SPEC `RND:num` th) (ASSUME `RND < 2 EXP 256`))
    with Failure _ -> NO_TAC) THEN
  ASSUME_TAC(INST_TYPE [`:64`,`:M`; `:32`,`:N`] WORD_ZX_0) THEN
  FULL_CALL_TAC mldsa_native_libmldsa_gcc12_Os_mc MLD_SIGN87_EXEC
   "H_INTERNAL"
   [`read X0 s`; `read X1 s`; `mlen:num`; `read X3 s`; `2 + ctxlen`;
    `read X5 s`; `read X6 s`; `read X7 s`; `skb:num->byte`; `M:num`;
    `num_of_bytelist(mld_domain_separation_prefix 0
       (bytelist_of_num ctxlen C) [])`;
    `RND:num`; `MU:num`; `guard:int64`; `pc:num`; `read SP s`; `read X30 s`]
   MLD_SIGN87_VARS 42 THEN
  ASM_CASES_TAC `mld_sign_ok_87 skb MU RND` THEN
  MLD_WRAP_USE_CASE_TAC `mld_sign_ok_87 skb MU RND` [] THENL
   [MLD_SIGN87_OK_TAC; MLD_SIGN87_FAIL_TAC];;

(*** ctxlen <= 255: randombytes into rnd, failing with -3 or signing ***)

let MLD_SIGN87_RANDOM_TAC =
  SUBGOAL_THEN `ctxlen <= 255` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[GSYM NOT_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `2 + ctxlen < 2 EXP 64` ASSUME_TAC THENL
   [SIMPLE_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `val(word(2 + ctxlen):int64) = 2 + ctxlen` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    SIMPLE_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(2 + ctxlen = 0)` ASSUME_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  ARM_STEPS_TAC MLD_SIGN87_EXEC (22--26) THEN MLD_WRAP_NORM_TAC THEN
  LIBC_PLT_TAC MLD_SIGN87_EXEC 26 THEN
  LIBC_SAFE_CALL_TAC "H_RANDOMBYTES" MLD_SIGN87_EXEC
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X30 s`]
   (ref MLD_SIGN87_VARS) 31 THEN
  ABBREV_TAC `rv = read X0 s31` THEN
  MLD_WRAP_RANDOM_TAC `RND:num` `X22` `32` `s31:armstate` THEN
  ASM_CASES_TAC `val(word_zx(rv:int64):int32) = 0` THENL
   [MLD_SIGN87_SIGN_TAC;
    ARM_STEPS_TAC MLD_SIGN87_EXEC (32--34) THEN
    MLD_SIGN87_Z_TAC 35 THEN MLD_SIGN87_FINAL_TAC `0`];;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety, by cases on whether the     *)
(* context is too long, whether randombytes succeeds and whether signing     *)
(* does, which the result shows, and at the end of each on whether the stack *)
(* pointer is a multiple of 32, which gives the address of the buffer.       *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SIGNATURE_87_GCC12_OS_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_SIGNATURE_87_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th ->
    let ms,th' = CONJ_PAIR th in
    let mcp,mrb = CONJ_PAIR th' in
    MLD_WRAP_ASSUME_CALLEE_TAC
     (MATCH_MP MLDSA_NATIVE_SIGNATURE_INTERNAL_87_GCC12_OS_IMAGE_SUBROUTINE_FULL
               (CONJ ms mcp)) "H_INTERNAL" THEN
    MLD_WRAP_ASSUME_CALLEE_TAC
     (MATCH_MP
       MLDSA_NATIVE_PREPARE_DOMAIN_SEPARATION_PREFIX_87_GCC12_OS_IMAGE_SUBROUTINE_FULL
       mcp) "H_PREFIX" THEN
    MLD_WRAP_ASSUME_CALLEE_TAC
     (MATCH_MP MLDSA_NATIVE_ZEROIZE_6_GCC12_OS_IMAGE_SUBROUTINE_FULL ms)
     "H_ZERO" THEN
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
  WORD_FORALL_OFFSET_TAC 112576 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst MLD_SIGN87_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th ->
    is_eq(concl th) && lhs(concl th) = `MU:num`)) THEN
  MLD_WRAP_FRAME_TAC 112576
   [`got_stack_chk_guard:num`; `got_randombytes:num`]
   (19--25) THEN
  MLD_SIGN87_HEAD_TAC THEN ASM_CASES_TAC `255 < ctxlen` THEN
  MLD_WRAP_USE_CASE_TAC `255 < ctxlen` [ADD_EQ_0; ARITH_EQ] THENL
   [MLD_SIGN87_REJECT_TAC; MLD_SIGN87_RANDOM_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SIGNATURE_87_GCC12_OS_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_SIGNATURE_87_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT,
  MLD_WRAP_CORRECT_TAC
   MLDSA_NATIVE_SIGNATURE_87_GCC12_OS_IMAGE_SUBROUTINE_FULL);;

let MLDSA_NATIVE_SIGNATURE_87_GCC12_OS_IMAGE_SUBROUTINE_SAFE = prove
 (MLDSA_NATIVE_SIGNATURE_87_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT,
  MLD_WRAP_SAFE_TAC
   MLDSA_NATIVE_SIGNATURE_87_GCC12_OS_IMAGE_SUBROUTINE_FULL);;
