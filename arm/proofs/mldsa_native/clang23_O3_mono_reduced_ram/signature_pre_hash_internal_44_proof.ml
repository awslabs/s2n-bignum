(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Signing a pre-hash (HashML-DSA): the proof (see                           *)
(* signature_pre_hash_internal_44_spec.ml).                                  *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/signature_pre_hash_internal_44_spec.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_wrap.ml";;

(* ------------------------------------------------------------------------- *)
(* The calls. The frame is of 432 bytes below stackpointer + 13312: 48 bytes *)
(* of saved registers, then the stack pointer is aligned down to 32 bytes    *)
(* (sp = stackpointer + kb, kb = 12896 or 12880, by the proof splitting on   *)
(* whether stackpointer is a multiple of 32 right after the prologue), with  *)
(* the prefix in the buffer at sp and the canary at sp + 360. The events     *)
(* before a call are functions of the variables MLD_SPHI44_VARS (those of    *)
(* the signing being the arguments of its events). HA, PLEN and PRE are      *)
(* replaced by their definitions, the length MLD_SPHI44_PLEN and the prefix  *)
(* MLD_SPHI44_PRE.                                                           *)
(* ------------------------------------------------------------------------- *)

let MLD_SPHI44_EXEC =
  MLDSA_NATIVE_SIGNATURE_PRE_HASH_INTERNAL_44_CLANG23_O3_MONO_REDUCED_RAM_EXEC;;

let MLD_SPHI44_VARS =
  [`sig:int64`; `ph:int64`; `phlen:num`; `ctx:int64`; `ctxlen:num`;
   `rnd:int64`; `sk:int64`; `hashalg:int64`; `skb:num->byte`; `MU:num`;
   `RND:num`; `guard:int64`; `mf:int64`; `mc:int64`; `pc:num`;
   `stackpointer:int64`; `returnaddress:int64`];;

let MLD_SPHI44_PLEN =
  `mld_domain_separation_prefix_length (val(word_zx (hashalg:int64):int32))
     ctxlen phlen`
and MLD_SPHI44_PRE =
  `num_of_bytelist(mld_domain_separation_prefix
     (val(word_zx (hashalg:int64):int32))
     (bytelist_of_num ctxlen C) (bytelist_of_num phlen PH))`;;

let MLD_SPHI44_LE =
  SPECL [`val(word_zx (hashalg:int64):int32)`; `ctxlen:num`; `phlen:num`]
   MLD_WRAP_PREFIX_LENGTH_LE;;

(*** The call of memset at step n, after its PLT stub ***)

let MLD_SPHI44_MEMSET_TAC n =
  LIBC_PLT_TAC MLD_SPHI44_EXEC (n - 5) THEN
  LIBC_SAFE_CALL_TAC "H_MEMSET" MLD_SPHI44_EXEC
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`;
    `read X30 s`] (ref MLD_SPHI44_VARS) n THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_ZX_0]);;

(*** The end of a path ***)

let MLD_SPHI44_FINAL_TAC =
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[MLD_WRAP_RET_DISTINCT] THEN
  REPEAT CONJ_TAC THEN TRY(MLD_WRAP_RET_TAC THEN NO_TAC) THEN
  ABBREV_TAC `rho = mld_sk_rho skb` THEN
  ABBREV_TAC `dcl = mld_sign_declass_44 skb MU RND` THEN
  MLD_WRAP_DISCHARGE_TAC;;

(*** From the zeroing of the prefix at step k to the return ***)

let MLD_SPHI44_R_TAC k =
  ARM_STEPS_TAC MLD_SPHI44_EXEC (k--(k + 14)) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLD_SPHI44_EXEC ((k + 15)--(k + 34)) THEN
  MLD_SPHI44_FINAL_TAC;;

(*** From the zeroing of the signature at step k to the return ***)

let MLD_SPHI44_Z_TAC k =
  ARM_STEPS_TAC MLD_SPHI44_EXEC (k--(k + 3)) THEN
  MLD_SPHI44_MEMSET_TAC (k + 8) THEN
  MLD_SPHI44_R_TAC (k + 9);;

(*** A prefix of PLEN bytes: signing it as the message, pre = NULL ***)

let MLD_SPHI44_SIGN_TAC =
  SUBGOAL_THEN (mk_comb(mk_comb(`(<):num->num->bool`,MLD_SPHI44_PLEN),
                        `2 EXP 64`)) ASSUME_TAC THENL
   [MP_TAC MLD_SPHI44_LE THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN (mk_eq(mk_comb(`val:int64->num`,
                       mk_comb(`word:num->int64`,MLD_SPHI44_PLEN)),
                      MLD_SPHI44_PLEN)) ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    MP_TAC MLD_SPHI44_LE THEN ARITH_TAC;
    ALL_TAC] THEN
  ARM_STEPS_TAC MLD_SPHI44_EXEC (19--28) THEN
  MLD_WRAP_GOT_TAC THEN
  MLD_WRAP_NULL_TAC [`sig:int64`,`2420`; `stackpointer:int64`,`13312`] THEN
  TRY MLD_WRAP_TERMINATES_TAC THEN
  ASSUME_TAC(INST_TYPE [`:64`,`:M`; `:32`,`:N`] WORD_ZX_0) THEN
  MLD_CLANG_CALL_FACTS_TAC 13312 12864 THEN
  MLD_CLANG_DRIVER_TAC 12864 [`sig:int64,2420`] MLD_SPHI44_LE THEN
  FULL_CALL_TAC mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc MLD_SPHI44_EXEC
   "H_INTERNAL"
   [`read X0 s`; `read X1 s`; MLD_SPHI44_PLEN; `read X3 s`; `0`;
    `read X5 s`; `read X6 s`; `read X7 s`; `skb:num->byte`;
    MLD_SPHI44_PRE; `0`; `RND:num`; `MU:num`; `guard:int64`; `pc:num`;
    `read SP s`; `read X30 s`] MLD_SPHI44_VARS 29 THEN
  MLD_CLANG_WIDEN_TAC MLD_SPHI44_LE THEN
  ASM_CASES_TAC `mld_sign_ok_44 skb MU RND` THEN
  MLD_WRAP_USE_CASE_TAC `mld_sign_ok_44 skb MU RND` [] THEN
  FIRST_ASSUM(ASSUME_TAC o REWRITE_RULE[MLD_WRAP_SIGN_OK_DECLASS_44] o
    check (fun th -> concl th = `mld_sign_ok_44 skb MU RND` ||
                     concl th = `~mld_sign_ok_44 skb MU RND`)) THEN
  MLD_CLANG_IF `mld_sign_ok_44 skb MU RND`
   (ARM_STEPS_TAC MLD_SPHI44_EXEC (30--32) THEN MLD_SPHI44_R_TAC 33)
   (ASSUME_TAC(GEN `t:num` (MP (SPECL [`skb:num->byte`; `MU:num`;
      `RND:num`; `t:num`] (CONJUNCT1 MLD_WRAP_SIGN_SIG_FAIL))
      (ASSUME `~mld_sign_ok_44 skb MU RND`))) THEN
    ARM_STEPS_TAC MLD_SPHI44_EXEC (30--31) THEN MLD_SPHI44_Z_TAC 32);;

(*** hashalg is not 0: the prefix, -9 if it is rejected ***)

let MLD_SPHI44_PREFIX_TAC =
  ARM_STEPS_TAC MLD_SPHI44_EXEC (12--17) THEN
  FULL_CALL_TAC mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc MLD_SPHI44_EXEC "H_PREFIX"
   [`read X0 s`; `read X1 s`; `phlen:num`; `read X3 s`; `ctxlen:num`;
    `read X5 s`; `C:num`; `PH:num`; `pc:num`; `read SP s`; `read X30 s`]
   MLD_SPHI44_VARS 18 THEN
  MLD_WRAP_LET_TAC [] [MLD_PREFIX_ZX_ZX] THEN
  ASM_CASES_TAC (mk_eq(MLD_SPHI44_PLEN,`0`)) THEN
  MLD_WRAP_USE_CASE_TAC (mk_eq(MLD_SPHI44_PLEN,`0`)) [] THEN
  MLD_CLANG_IF (mk_eq(MLD_SPHI44_PLEN,`0`))
   (ARM_STEPS_TAC MLD_SPHI44_EXEC (19--20) THEN MLD_SPHI44_Z_TAC 21)
   MLD_SPHI44_SIGN_TAC;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety, by cases on whether hashalg *)
(* is 0, whether the prefix is rejected and whether signing succeeds (which  *)
(* the events give as what it declassifies), and at the end of each on       *)
(* whether the stack pointer is a multiple of 32, which gives the address of *)
(* the buffer.                                                               *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SIGNATURE_PRE_HASH_INTERNAL_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL =
  prove
 (MLDSA_NATIVE_SIGNATURE_PRE_HASH_INTERNAL_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th ->
    let ms,mcp = CONJ_PAIR th in
    MLD_WRAP_ASSUME_CALLEE_TAC
     (MATCH_MP MLDSA_NATIVE_SIGNATURE_INTERNAL_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL
               (CONJ ms mcp)) "H_INTERNAL" THEN
    MLD_WRAP_ASSUME_CALLEE_TAC
     (MATCH_MP
       MLDSA_NATIVE_PREPARE_DOMAIN_SEPARATION_PREFIX_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL
       mcp) "H_PREFIX" THEN
    MLD_WRAP_ASSUME_CALLEE_TAC
     (REWRITE_RULE[memset_full_contract] ms) "H_MEMSET") THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(sig:int64) (ph:int64) (phlen:num) (ctx:int64) (ctxlen:num) (rnd:int64)
     (sk:int64) (hashalg:int64) (rho:num)
     (dcl:num->num#num#(num->int32)#(num->byte)) (guard:int64) (mf:int64)
     (mc:int64) (pc:num) (sp:int64) (ra:int64).
     if aligned 32 sp then
       if val(word_zx hashalg:int32) = 0
       then f_ev_a0 sig ph phlen ctx ctxlen rnd sk hashalg guard mf mc pc sp ra
       else if mld_domain_separation_prefix_length
                (val(word_zx hashalg:int32)) ctxlen phlen = 0
       then f_ev_a1 sig ph phlen ctx ctxlen rnd sk hashalg guard mf mc pc sp ra
       else if (?n. FST(SND(dcl n)) = 13)
       then f_ev_a2 sig ph phlen ctx ctxlen rnd sk hashalg rho dcl guard mf mc
             pc sp ra
       else f_ev_a3 sig ph phlen ctx ctxlen rnd sk hashalg rho dcl guard mf mc
             pc sp ra
     else
       if val(word_zx hashalg:int32) = 0
       then f_ev_u0 sig ph phlen ctx ctxlen rnd sk hashalg guard mf mc pc sp ra
       else if mld_domain_separation_prefix_length
                (val(word_zx hashalg:int32)) ctxlen phlen = 0
       then f_ev_u1 sig ph phlen ctx ctxlen rnd sk hashalg guard mf mc pc sp ra
       else if (?n. FST(SND(dcl n)) = 13)
       then f_ev_u2 sig ph phlen ctx ctxlen rnd sk hashalg rho dcl guard mf mc
             pc sp ra
       else f_ev_u3 sig ph phlen ctx ctxlen rnd sk hashalg rho dcl guard mf mc
             pc sp ra
     :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `sig:int64`; `ph:int64`; `phlen:num`;
    `ctx:int64`; `ctxlen:num`; `rnd:int64`; `sk:int64`; `hashalg:int64`;
    `skb:num->byte`; `PH:num`; `C:num`; `RND:num`; `HA:num`; `PLEN:num`;
    mk_var("PRE",`:num`); `MU:num`; `guard:int64`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 13312 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst MLD_SPHI44_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MAP_EVERY (fun v -> FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
    is_eq(concl th) && lhs(concl th) = v)))
   [`HA:num`; `PLEN:num`; mk_var("PRE",`:num`)] THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th ->
    is_eq(concl th) && lhs(concl th) = `MU:num`)) THEN
  MLD_WRAP_FRAME_TAC 13312 [`got_stack_chk_guard:num`; `got_memset:num`]
   ((19--21) @ [28; 29]) THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC MLD_SPHI44_EXEC (1--6) THEN
  MLD_WRAP_SYMBUF_TAC `kb:num` THEN MLD_WRAP_SYMBUF_END_TAC `kb:num` THEN
  ARM_STEPS_TAC MLD_SPHI44_EXEC (7--7) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLD_SPHI44_EXEC (8--11) THEN
  ASM_CASES_TAC `val(word_zx (hashalg:int64):int32) = 0` THEN
  MLD_WRAP_USE_CASE_TAC `val(word_zx (hashalg:int64):int32) = 0` [] THEN
  MLD_CLANG_IF `val(word_zx (hashalg:int64):int32) = 0`
   (ARM_STEPS_TAC MLD_SPHI44_EXEC (12--13) THEN MLD_SPHI44_Z_TAC 14)
   MLD_SPHI44_PREFIX_TAC);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SIGNATURE_PRE_HASH_INTERNAL_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT =
  prove
 (MLDSA_NATIVE_SIGNATURE_PRE_HASH_INTERNAL_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT,
  MLD_WRAP_CORRECT_TAC
   MLDSA_NATIVE_SIGNATURE_PRE_HASH_INTERNAL_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL);;

let MLDSA_NATIVE_SIGNATURE_PRE_HASH_INTERNAL_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE =
  prove
 (MLDSA_NATIVE_SIGNATURE_PRE_HASH_INTERNAL_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT,
  MLD_WRAP_SAFE_TAC
   MLDSA_NATIVE_SIGNATURE_PRE_HASH_INTERNAL_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL);;
