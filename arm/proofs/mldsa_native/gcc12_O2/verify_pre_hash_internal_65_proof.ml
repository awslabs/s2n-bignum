(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Verifying a signature of a pre-hash: the proof (see                       *)
(* verify_pre_hash_internal_65_spec.ml).                                     *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/gcc12_O2/verify_pre_hash_internal_65_spec.ml";;
needs "arm/proofs/utils/mldsa_native_wrap.ml";;

(* ------------------------------------------------------------------------- *)
(* The calls. The frame of 400 bytes is at stackpointer + 45280, with the    *)
(* prefix in the buffer at stackpointer + kb, kb = 45312 or 45328 (aligned   *)
(* to 32), and the canary at + 45672. The events before a call are functions *)
(* of the variables MLD_VPHI65_VARS. HA, PLEN and PRE are replaced by their  *)
(* definitions, the length MLD_VPHI65_PLEN and the prefix MLD_VPHI65_PRE.    *)
(* ------------------------------------------------------------------------- *)

let MLD_VPHI65_EXEC = MLDSA_NATIVE_VERIFY_PRE_HASH_INTERNAL_65_GCC12_O2_EXEC;;

let MLD_VPHI65_VARS =
  [`sig:int64`; `ph:int64`; `phlen:num`; `ctx:int64`; `ctxlen:num`;
   `pk:int64`; `hashalg:int64`; `sigb:num->byte`; `pkb:num->byte`;
   `PH:num`; `C:num`; `guard:int64`; `mf:int64`; `mc:int64`; `pc:num`;
   `stackpointer:int64`; `returnaddress:int64`; `kb:num`];;

let MLD_VPHI65_PLEN =
  `mld_domain_separation_prefix_length (val(word_zx (hashalg:int64):int32))
     ctxlen phlen`
and MLD_VPHI65_PRE =
  `num_of_bytelist(mld_domain_separation_prefix
     (val(word_zx (hashalg:int64):int32))
     (bytelist_of_num ctxlen C) (bytelist_of_num phlen PH))`;;

let MLD_VPHI65_LE =
  SPECL [`val(word_zx (hashalg:int64):int32)`; `ctxlen:num`; `phlen:num`]
   MLD_WRAP_PREFIX_LENGTH_LE;;

(*** From join1 at step k: the zeroing of the prefix and the return ***)

let MLD_VPHI65_TAIL_TAC k =
  ARM_STEPS_TAC MLD_VPHI65_EXEC (k--(k + 3)) THEN
  LIBC_PLT_TAC MLD_VPHI65_EXEC (k + 3) THEN
  LIBC_SAFE_CALL_TAC "H_MEMSET" MLD_VPHI65_EXEC
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`;
    `read X30 s`] (ref MLD_VPHI65_VARS) (k + 8) THEN
  ARM_STEPS_TAC MLD_VPHI65_EXEC ((k + 9)--(k + 9)) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLD_VPHI65_EXEC ((k + 10)--(k + 19)) THEN
  MLD_WRAP_FINAL_TAC;;

(*** A prefix of PLEN bytes: verification, pre = NULL and mlen = PLEN ***)

let MLD_VPHI65_VERIFY_TAC =
  SUBGOAL_THEN (mk_comb(mk_comb(`(<):num->num->bool`,MLD_VPHI65_PLEN),
                        `2 EXP 64`)) ASSUME_TAC THENL
   [MP_TAC MLD_VPHI65_LE THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN (mk_eq(mk_comb(`val:int64->num`,
                       mk_comb(`word:num->int64`,MLD_VPHI65_PLEN)),
                      MLD_VPHI65_PLEN)) ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    MP_TAC MLD_VPHI65_LE THEN ARITH_TAC;
    ALL_TAC] THEN
  ARM_STEPS_TAC MLD_VPHI65_EXEC (18--26) THEN
  MLD_WRAP_GOT_TAC THEN
  MLD_WRAP_NULL_TAC [`stackpointer:int64`,`45680`] THEN
  MLD_WRAP_TERMINATES_TAC THEN
  MLD_WRAP_DRIVER_TAC
   (mk_comb(mk_comb(`nonoverlapping:int64#num->int64#num->bool`,
                    `stackpointer:int64,45280`),
            mk_pair(`word_add stackpointer (word kb):int64`,
                    MLD_VPHI65_PLEN)))
   MLD_VPHI65_LE THEN
  FULL_CALL_TAC mldsa_native_libmldsa_gcc12_O2_mc MLD_VPHI65_EXEC
   "H_INTERNAL"
   [`read X0 s`; `read X1 s`; MLD_VPHI65_PLEN; `read X3 s`; `0`;
    `read X5 s`; `read X6 s`; `sigb:num->byte`; `pkb:num->byte`;
    MLD_VPHI65_PRE; `0`; `guard:int64`; `pc:num`; `read SP s`;
    `read X30 s`] MLD_VPHI65_VARS 27 THEN
  MLD_WRAP_WIDEN_TAC
   [prove(mk_comb(mk_comb(`contained:int64#num->int64#num->bool`,
                          mk_pair(`word_add stackpointer (word kb):int64`,
                                  MLD_VPHI65_PLEN)),
                  `word_add stackpointer (word kb):int64,332`),
          REWRITE_TAC[contained; CONTAINED_MODULO_REFL;
                      MLD_WRAP_PREFIX_LENGTH_LE])] THEN
  ARM_STEPS_TAC MLD_VPHI65_EXEC (28--29) THEN
  MLD_VPHI65_TAIL_TAC 30;;

(*** hashalg is not 0: the prefix, -9 if it is rejected ***)

let MLD_VPHI65_PREFIX_TAC =
  ARM_STEPS_TAC MLD_VPHI65_EXEC (10--16) THEN
  FULL_CALL_TAC mldsa_native_libmldsa_gcc12_O2_mc MLD_VPHI65_EXEC "H_PREFIX"
   [`read X0 s`; `read X1 s`; `phlen:num`; `read X3 s`; `ctxlen:num`;
    `read X5 s`; `C:num`; `PH:num`; `pc:num`; `read SP s`; `read X30 s`]
   MLD_VPHI65_VARS 17 THEN
  MLD_WRAP_LET_TAC [] [MLD_PREFIX_ZX_ZX] THEN
  ASM_CASES_TAC (mk_eq(MLD_VPHI65_PLEN,`0`)) THEN
  MLD_WRAP_USE_CASE_TAC (mk_eq(MLD_VPHI65_PLEN,`0`)) [] THENL
   [ARM_STEPS_TAC MLD_VPHI65_EXEC (18--22) THEN MLD_VPHI65_TAIL_TAC 23;
    MLD_VPHI65_VERIFY_TAC];;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety, by cases on whether hashalg *)
(* is 0 and whether the prefix is rejected, and at the end of each on        *)
(* whether the stack pointer is a multiple of 32, which gives the address of *)
(* the buffer.                                                               *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_VERIFY_PRE_HASH_INTERNAL_65_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  prove
 (MLDSA_NATIVE_VERIFY_PRE_HASH_INTERNAL_65_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th ->
    let ms,mcp = CONJ_PAIR th in
    MLD_WRAP_ASSUME_CALLEE_TAC
     (MATCH_MP MLDSA_NATIVE_VERIFY_INTERNAL_65_GCC12_O2_IMAGE_SUBROUTINE_FULL
               ms) "H_INTERNAL" THEN
    MLD_WRAP_ASSUME_CALLEE_TAC
     (MATCH_MP
       MLDSA_NATIVE_PREPARE_DOMAIN_SEPARATION_PREFIX_65_GCC12_O2_IMAGE_SUBROUTINE_FULL
       mcp) "H_PREFIX" THEN
    MLD_WRAP_ASSUME_CALLEE_TAC
     (REWRITE_RULE[memset_ret_full_contract] ms) "H_MEMSET") THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(sig:int64) (ph:int64) (phlen:num) (ctx:int64) (ctxlen:num) (pk:int64)
     (hashalg:int64) (sigb:num->byte) (pkb:num->byte) (PH:num) (C:num)
     (guard:int64) (mf:int64) (mc:int64) (pc:num) (sp:int64) (ra:int64).
     if aligned 32 sp then
       if val(word_zx hashalg:int32) = 0
       then f_ev_a0 sig ph phlen ctx ctxlen pk hashalg guard mf mc pc sp ra
       else if mld_domain_separation_prefix_length
                (val(word_zx hashalg:int32)) ctxlen phlen = 0
       then f_ev_a1 sig ph phlen ctx ctxlen pk hashalg guard mf mc pc sp ra
       else f_ev_a2 sig ph phlen ctx ctxlen pk hashalg sigb pkb PH C guard
             mf mc pc sp ra
     else
       if val(word_zx hashalg:int32) = 0
       then f_ev_u0 sig ph phlen ctx ctxlen pk hashalg guard mf mc pc sp ra
       else if mld_domain_separation_prefix_length
                (val(word_zx hashalg:int32)) ctxlen phlen = 0
       then f_ev_u1 sig ph phlen ctx ctxlen pk hashalg guard mf mc pc sp ra
       else f_ev_u2 sig ph phlen ctx ctxlen pk hashalg sigb pkb PH C guard
             mf mc pc sp ra
     :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `sig:int64`; `ph:int64`; `phlen:num`;
    `ctx:int64`; `ctxlen:num`; `pk:int64`; `hashalg:int64`;
    `sigb:num->byte`; `pkb:num->byte`; `PH:num`; `C:num`; `HA:num`;
    `PLEN:num`; mk_var("PRE",`:num`); `guard:int64`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 45680 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; NONOVERLAPPING_CLAUSES; fst MLD_VPHI65_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MAP_EVERY (fun v -> FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
    is_eq(concl th) && lhs(concl th) = v)))
   [`HA:num`; `PLEN:num`; mk_var("PRE",`:num`)] THEN
  MLD_WRAP_FRAME_TAC 45680 [`got_stack_chk_guard:num`; `got_memset:num`]
   (19--21) THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC MLD_VPHI65_EXEC (1--2) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLD_VPHI65_EXEC (3--9) THEN MLD_WRAP_SYMBUF_TAC `kb:num` THEN
  ASM_CASES_TAC `val(word_zx (hashalg:int64):int32) = 0` THENL
   [ARM_STEPS_TAC MLD_VPHI65_EXEC (10--12) THEN MLD_VPHI65_TAIL_TAC 13;
    MLD_VPHI65_PREFIX_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_VERIFY_PRE_HASH_INTERNAL_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  prove
 (MLDSA_NATIVE_VERIFY_PRE_HASH_INTERNAL_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  MLD_WRAP_CORRECT_TAC
   MLDSA_NATIVE_VERIFY_PRE_HASH_INTERNAL_65_GCC12_O2_IMAGE_SUBROUTINE_FULL);;

let MLDSA_NATIVE_VERIFY_PRE_HASH_INTERNAL_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  prove
 (MLDSA_NATIVE_VERIFY_PRE_HASH_INTERNAL_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  MLD_WRAP_SAFE_TAC
   MLDSA_NATIVE_VERIFY_PRE_HASH_INTERNAL_65_GCC12_O2_IMAGE_SUBROUTINE_FULL);;
