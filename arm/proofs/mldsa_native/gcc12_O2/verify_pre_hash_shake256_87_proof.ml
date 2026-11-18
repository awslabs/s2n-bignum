(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Verifying a signature with a SHAKE256 pre-hash: the proof (see            *)
(* verify_pre_hash_shake256_87_spec.ml).                                     *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/gcc12_O2/verify_pre_hash_shake256_87_spec.ml";;
needs "arm/proofs/utils/mldsa_native_wrap.ml";;

(* ------------------------------------------------------------------------- *)
(* The calls. The frame of 144 bytes is at stackpointer + 74624, with the    *)
(* pre-hash in the buffer at stackpointer + kb, kb = 74688 or 74672 (aligned *)
(* to 32), and the canary at + 74760. The events before a call are functions *)
(* of the variables MLD_VPHS87_VARS. PH and PRE are replaced by their        *)
(* definitions, MLD_VPHS87_PH and MLD_VPHS87_PRE.                            *)
(* ------------------------------------------------------------------------- *)

let MLD_VPHS87_EXEC = MLDSA_NATIVE_VERIFY_PRE_HASH_SHAKE256_87_GCC12_O2_EXEC;;

let MLD_VPHS87_VARS =
  [`sig:int64`; `m:int64`; `mlen:num`; `ctx:int64`; `ctxlen:num`;
   `pk:int64`; `sigb:num->byte`; `pkb:num->byte`; `M:num`; `C:num`;
   `guard:int64`; `mf:int64`; `mc:int64`; `pc:num`; `stackpointer:int64`;
   `returnaddress:int64`; `kb:num`];;

let MLD_VPHS87_PH =
  `num_of_bytelist(list_of_seq (mld_shake256_byte mlen M) 64)`;;

let MLD_VPHS87_PRE =
  `num_of_bytelist(mld_domain_separation_prefix 12 (bytelist_of_num ctxlen C)
    (bytelist_of_num 64 (num_of_bytelist(list_of_seq
                          (mld_shake256_byte mlen M) 64))))`;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety: SHAKE256 of the message     *)
(* into the buffer, the verification of the pre-hash with hashalg = 12, the  *)
(* zeroing of the buffer and, at the end, the cases on whether the stack     *)
(* pointer is a multiple of 32, which gives its address.                     *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_VERIFY_PRE_HASH_SHAKE256_87_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  prove
 (MLDSA_NATIVE_VERIFY_PRE_HASH_SHAKE256_87_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th ->
    MLD_WRAP_ASSUME_CALLEE_TAC
     (MATCH_MP
       MLDSA_NATIVE_VERIFY_PRE_HASH_INTERNAL_87_GCC12_O2_IMAGE_SUBROUTINE_FULL
       th) "H_INTERNAL" THEN
    MLD_WRAP_ASSUME_CALLEE_TAC
     MLDSA_NATIVE_SHAKE256_GCC12_O2_IMAGE_SUBROUTINE_FULL "H_SHAKE") THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(sig:int64) (m:int64) (mlen:num) (ctx:int64) (ctxlen:num) (pk:int64)
     (sigb:num->byte) (pkb:num->byte) (M:num) (C:num) (guard:int64)
     (mf:int64) (mc:int64) (pc:num) (sp:int64) (ra:int64).
     if aligned 32 sp
     then f_ev_a sig m mlen ctx ctxlen pk sigb pkb M C guard mf mc pc sp ra
     else f_ev_u sig m mlen ctx ctxlen pk sigb pkb M C guard mf mc pc sp ra
     :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `sig:int64`; `m:int64`; `mlen:num`; `ctx:int64`;
    `ctxlen:num`; `pk:int64`; `sigb:num->byte`; `pkb:num->byte`; `M:num`;
    `C:num`; `PH:num`; mk_var("PRE",`:num`); `guard:int64`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 74768 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; NONOVERLAPPING_CLAUSES; fst MLD_VPHS87_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MAP_EVERY (fun v -> FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
    is_eq(concl th) && lhs(concl th) = v)))
   [`PH:num`; mk_var("PRE",`:num`)] THEN
  MLD_WRAP_FRAME_TAC 74768 [`got_stack_chk_guard:num`] (19--23) THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC MLD_VPHS87_EXEC (1--4) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLD_VPHS87_EXEC (5--9) THEN MLD_WRAP_SYMBUF_TAC `kb:num` THEN
  ARM_STEPS_TAC MLD_VPHS87_EXEC (10--20) THEN MLD_WRAP_GOT_TAC THEN
  FULL_CALL_TAC mldsa_native_libmldsa_gcc12_O2_mc MLD_VPHS87_EXEC "H_SHAKE"
   [`read X0 s`; `64`; `read X2 s`; `mlen:num`; `M:num`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] MLD_VPHS87_VARS 21 THEN
  ARM_STEPS_TAC MLD_VPHS87_EXEC (22--29) THEN
  MLD_WRAP_SHAKE256_TERMINATES_TAC THEN
  FULL_CALL_TAC mldsa_native_libmldsa_gcc12_O2_mc MLD_VPHS87_EXEC
   "H_INTERNAL"
   [`read X0 s`; `read X1 s`; `64`; `read X3 s`; `ctxlen:num`;
    `read X5 s`; `read X6 s`; `sigb:num->byte`; `pkb:num->byte`;
    MLD_VPHS87_PH; `C:num`; `12`;
    `mld_domain_separation_prefix_length 12 ctxlen 64`; MLD_VPHS87_PRE;
    `guard:int64`; `pc:num`; `read SP s`; `read X30 s`]
   MLD_VPHS87_VARS 30 THEN
  ARM_STEPS_TAC MLD_VPHS87_EXEC (31--34) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLD_VPHS87_EXEC (35--44) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN TRY(MLD_WRAP_SHAKE256_RESULT_TAC THEN NO_TAC) THEN
  MLD_WRAP_DISCHARGE_TAC);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_VERIFY_PRE_HASH_SHAKE256_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  prove
 (MLDSA_NATIVE_VERIFY_PRE_HASH_SHAKE256_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  MLD_WRAP_CORRECT_TAC
   MLDSA_NATIVE_VERIFY_PRE_HASH_SHAKE256_87_GCC12_O2_IMAGE_SUBROUTINE_FULL);;

let MLDSA_NATIVE_VERIFY_PRE_HASH_SHAKE256_87_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  prove
 (MLDSA_NATIVE_VERIFY_PRE_HASH_SHAKE256_87_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  MLD_WRAP_SAFE_TAC
   MLDSA_NATIVE_VERIFY_PRE_HASH_SHAKE256_87_GCC12_O2_IMAGE_SUBROUTINE_FULL);;
