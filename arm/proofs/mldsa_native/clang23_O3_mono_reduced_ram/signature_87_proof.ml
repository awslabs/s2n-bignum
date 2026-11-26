(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Signing a message (pure ML-DSA, randomized): the proof (see               *)
(* signature_87_spec.ml).                                                    *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/signature_87_spec.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_wrap.ml";;

(* ------------------------------------------------------------------------- *)
(* The calls. The frame is of 464 bytes below stackpointer + 17600: 64 bytes *)
(* of saved registers, then the stack pointer is aligned down to 32 bytes    *)
(* (sp = stackpointer + kb, kb = 12896 or 12880, by the proof splitting on   *)
(* whether stackpointer is a multiple of 32 right after the prologue), with  *)
(* rnd at sp, the prefix at sp + 32 and the canary at sp + 376. The events   *)
(* before a call are functions of the variables MLD_SIGN87_VARS (those of    *)
(* the signing being the arguments of its events).                           *)
(* ------------------------------------------------------------------------- *)

let MLD_SIGN87_EXEC = MLDSA_NATIVE_SIGNATURE_87_CLANG23_O3_MONO_REDUCED_RAM_EXEC;;

let MLD_SIGN87_VARS =
  [`sig:int64`; `m:int64`; `mlen:num`; `ctx:int64`; `ctxlen:num`;
   `sk:int64`; `skb:num->byte`; `MU:num`; `RND:num`; `guard:int64`;
   `mf:int64`; `mc:int64`; `mr:int64`; `pc:num`; `stackpointer:int64`;
   `returnaddress:int64`];;

(*** The call of memset at step n, after its PLT stub ***)

let MLD_SIGN87_MEMSET_TAC n =
  LIBC_PLT_TAC MLD_SIGN87_EXEC (n - 5) THEN
  LIBC_SAFE_CALL_TAC "H_MEMSET" MLD_SIGN87_EXEC
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`;
    `read X30 s`] (ref MLD_SIGN87_VARS) n THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_ZX_0]);;

(*** The end, with the random bytes rnd (any if randombytes was not run) ***)

let MLD_SIGN87_FINAL_TAC rnd =
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  EXISTS_TAC rnd THEN
  ASM_REWRITE_TAC[MLD_WRAP_RET_DISTINCT; GSYM NOT_LT] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ABBREV_TAC `rho = mld_sk_rho skb` THEN
  ABBREV_TAC `dcl = mld_sign_declass_87 skb MU RND` THEN
  MLD_WRAP_DISCHARGE_TAC;;

(*** From the zeroing of the buffers at step k to the return ***)

let MLD_SIGN87_TAIL_TAC k rnd =
  ARM_STEPS_TAC MLD_SIGN87_EXEC (k--(k + 16)) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLD_SIGN87_EXEC ((k + 17)--(k + 38)) THEN
  MLD_SIGN87_FINAL_TAC rnd;;

(*** From the zeroing of the signature at step k to the return ***)

let MLD_SIGN87_Z_TAC k rnd =
  ARM_STEPS_TAC MLD_SIGN87_EXEC (k--(k + 3)) THEN
  MLD_SIGN87_MEMSET_TAC (k + 8) THEN MLD_SIGN87_TAIL_TAC (k + 9) rnd;;

(*** The prologue and the check ctxlen <= 255 ***)

let MLD_SIGN87_HEAD_TAC =
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC MLD_SIGN87_EXEC (1--7) THEN
  MLD_WRAP_SYMBUF_TAC `kb:num` THEN MLD_WRAP_SYMBUF_END_TAC `kb:num` THEN
  ARM_STEPS_TAC MLD_SIGN87_EXEC (8--8) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLD_SIGN87_EXEC (9--14);;

(*** ctxlen > 255: the signature is zeroed and the result is -9 ***)

let MLD_SIGN87_REJECT_TAC =
  ARM_STEPS_TAC MLD_SIGN87_EXEC (15--16) THEN MLD_SIGN87_Z_TAC 17 `0`;;

(*** Signing succeeds, the result is 0, and the signature is kept ***)

let MLD_SIGN87_OK_TAC j0 =
  ARM_STEPS_TAC MLD_SIGN87_EXEC ((j0 + 11)--(j0 + 12)) THEN
  MLD_SIGN87_TAIL_TAC (j0 + 13) `RND:num`;;

(*** Signing fails with -4 and the signature is zeroed ***)

let MLD_SIGN87_FAIL_TAC j0 =
  ARM_STEPS_TAC MLD_SIGN87_EXEC ((j0 + 11)--(j0 + 12)) THEN
  MLD_SIGN87_Z_TAC (j0 + 13) `RND:num`;;

(*** randombytes succeeds at the test at step j0: signing with the prefix
     and RND, with the prefix of 2 + ctxlen bytes at sp + 32 ***)

let MLD_SIGN87_SIGN_TAC j0 plen pre post =
  ARM_STEPS_TAC MLD_SIGN87_EXEC (j0--(j0 + 9)) THEN
  MLD_WRAP_GOT_TAC THEN MLD_WRAP_MP_TAC `ctxlen <= 255` THEN
  FIRST_ASSUM(fun th ->
    try STRIP_ASSUME_TAC
         (MP (SPEC `RND:num` th) (ASSUME `RND < 2 EXP 256`))
    with Failure _ -> NO_TAC) THEN
  ASSUME_TAC(INST_TYPE [`:64`,`:M`; `:32`,`:N`] WORD_ZX_0) THEN
  MLD_CLANG_PREFIX_OFS_TAC 32 THEN post THEN
  MLD_CLANG_CALL_FACTS_TAC 17600 17120 THEN
  FULL_CALL_TAC mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc MLD_SIGN87_EXEC
   "H_INTERNAL"
   [`read X0 s`; `read X1 s`; `mlen:num`; `read X3 s`; plen;
    `read X5 s`; `read X6 s`; `read X7 s`; `skb:num->byte`; `M:num`; pre;
    `RND:num`; `MU:num`; `guard:int64`; `pc:num`; `read SP s`; `read X30 s`]
   MLD_SIGN87_VARS (j0 + 10) THEN
  ASM_CASES_TAC `mld_sign_ok_87 skb MU RND` THEN
  MLD_WRAP_USE_CASE_TAC `mld_sign_ok_87 skb MU RND` [] THEN
  MLD_CLANG_IF `mld_sign_ok_87 skb MU RND` (MLD_SIGN87_OK_TAC j0)
   (MLD_SIGN87_FAIL_TAC j0);;

(*** The call of randombytes into rnd at step n - 5, returning at step n,
     then failing with -3 or signing; the test is at step j0 = n + 1 ***)

let MLD_SIGN87_RANDOM_TAC n plen pre post =
  let st = "s" ^ string_of_int n in
  LIBC_PLT_TAC MLD_SIGN87_EXEC (n - 5) THEN
  LIBC_SAFE_CALL_TAC "H_RANDOMBYTES" MLD_SIGN87_EXEC
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X30 s`]
   (ref MLD_SIGN87_VARS) n THEN
  ABBREV_TAC (mk_eq(`rv:int64`,parse_term("read X0 " ^ st))) THEN
  MLD_WRAP_RANDOM_TAC `RND:num` `SP` `32` (mk_var(st,`:armstate`)) THEN
  ASM_CASES_TAC `val(word_zx(rv:int64):int32) = 0` THEN
  MLD_CLANG_IF `val(word_zx(rv:int64):int32) = 0`
   (MLD_SIGN87_SIGN_TAC (n + 1) plen pre post)
   (ARM_STEPS_TAC MLD_SIGN87_EXEC ((n + 1)--(n + 3)) THEN
    MLD_SIGN87_Z_TAC (n + 4) `0`);;

(*** ctxlen <= 255: the prefix 0 || ctxlen || ctx at sp + 32, the context
     copied by memcpy unless it is empty, then randombytes into rnd ***)

let MLD_SIGN87_LEN_TAC =
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

let MLD_SIGN87_EMPTY_TAC =
  ARM_STEPS_TAC MLD_SIGN87_EXEC (15--24) THEN
  MLD_SIGN87_RANDOM_TAC 29 `2`
   `num_of_bytelist(mld_domain_separation_prefix 0
      (bytelist_of_num 0 C) [])`
   (FIRST_X_ASSUM(fun th ->
      ASSUME_TAC(REWRITE_RULE[ADD_CLAUSES; ASSUME `ctxlen = 0`] th)) THEN
    RULE_ASSUM_TAC(fun th ->
      if not(is_forall(concl th)) &&
         can (find_term (fun t -> is_const t && name_of t = "mld_sign_mu"))
             (concl th)
      then REWRITE_RULE[ADD_CLAUSES; ASSUME `ctxlen = 0`] th else th));;

let MLD_SIGN87_COPY_TAC =
  ARM_STEPS_TAC MLD_SIGN87_EXEC (15--25) THEN
  MLD_CLANG_OR_OFS_TAC 32 THEN ARM_STEPS_TAC MLD_SIGN87_EXEC (26--26) THEN
  LIBC_PLT_TAC MLD_SIGN87_EXEC 26 THEN
  LIBC_SAFE_CALL_TAC "H_MEMCPY" MLD_SIGN87_EXEC
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`; `C:num`;
    `read X30 s`] (ref MLD_SIGN87_VARS) 31 THEN
  ARM_STEPS_TAC MLD_SIGN87_EXEC (32--34) THEN
  MLD_SIGN87_RANDOM_TAC 39 `2 + ctxlen`
   `num_of_bytelist(mld_domain_separation_prefix 0
      (bytelist_of_num ctxlen C) [])` ALL_TAC;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety, by cases on whether the     *)
(* context is too long or empty, whether randombytes succeeds and whether    *)
(* signing does, which the result shows, and, from the prologue on, on       *)
(* whether the stack pointer is a multiple of 32.                            *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SIGNATURE_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_SIGNATURE_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th ->
    let ms,th' = CONJ_PAIR th in
    let mcp,mrb = CONJ_PAIR th' in
    MLD_WRAP_ASSUME_CALLEE_TAC
     (MATCH_MP MLDSA_NATIVE_SIGNATURE_INTERNAL_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL
               (CONJ ms mcp)) "H_INTERNAL" THEN
    MLD_WRAP_ASSUME_CALLEE_TAC
     (REWRITE_RULE[memcpy_full_contract] mcp) "H_MEMCPY" THEN
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
       else if ctxlen = 0
       then (if r = word 4294967293
             then f_ev_a4 sig m mlen ctx ctxlen sk guard mf mc mr pc sp ra
             else if r = word 0
             then f_ev_a5 sig m mlen ctx ctxlen sk rho dcl guard mf mc mr
                   pc sp ra
             else f_ev_a6 sig m mlen ctx ctxlen sk rho dcl guard mf mc mr
                   pc sp ra)
       else if r = word 4294967293
       then f_ev_a1 sig m mlen ctx ctxlen sk guard mf mc mr pc sp ra
       else if r = word 0
       then f_ev_a2 sig m mlen ctx ctxlen sk rho dcl guard mf mc mr pc sp ra
       else f_ev_a3 sig m mlen ctx ctxlen sk rho dcl guard mf mc mr pc sp ra
     else
       if 255 < ctxlen
       then f_ev_u0 sig m mlen ctx ctxlen sk guard mf mc mr pc sp ra
       else if ctxlen = 0
       then (if r = word 4294967293
             then f_ev_u4 sig m mlen ctx ctxlen sk guard mf mc mr pc sp ra
             else if r = word 0
             then f_ev_u5 sig m mlen ctx ctxlen sk rho dcl guard mf mc mr
                   pc sp ra
             else f_ev_u6 sig m mlen ctx ctxlen sk rho dcl guard mf mc mr
                   pc sp ra)
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
  WORD_FORALL_OFFSET_TAC 17600 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst MLD_SIGN87_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th ->
    is_eq(concl th) && lhs(concl th) = `MU:num`)) THEN
  MLD_WRAP_FRAME_TAC 17600
   [`got_stack_chk_guard:num`; `got_memset:num`; `got_memcpy:num`;
    `got_randombytes:num`]
   ((19--23) @ [28; 29]) THEN
  MLD_SIGN87_HEAD_TAC THEN MLD_CLANG_CTX_TAC THEN
  ASM_CASES_TAC `255 < ctxlen` THEN
  MLD_WRAP_USE_CASE_TAC `255 < ctxlen` [ADD_EQ_0; ARITH_EQ] THEN
  MLD_CLANG_IF `255 < ctxlen` MLD_SIGN87_REJECT_TAC
   (MLD_SIGN87_LEN_TAC THEN ASM_CASES_TAC `ctxlen = 0` THEN
    MLD_CLANG_IF `ctxlen = 0` MLD_SIGN87_EMPTY_TAC MLD_SIGN87_COPY_TAC));;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SIGNATURE_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_SIGNATURE_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT,
  MLD_WRAP_CORRECT_TAC
   MLDSA_NATIVE_SIGNATURE_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL);;

let MLDSA_NATIVE_SIGNATURE_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE = prove
 (MLDSA_NATIVE_SIGNATURE_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT,
  MLD_WRAP_SAFE_TAC
   MLDSA_NATIVE_SIGNATURE_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL);;
