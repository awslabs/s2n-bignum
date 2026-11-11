(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Verifying a signature with a SHAKE256 pre-hash: the proof (see            *)
(* verify_pre_hash_shake256_87_spec.ml).                                     *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/gcc12_O2/verify_pre_hash_shake256_87_spec.ml";;
needs "x86/proofs/utils/mldsa_native_verify.ml";;

(* ------------------------------------------------------------------------- *)
(* The calls. The frame is realigned to 32 bytes below the entry RSP (with   *)
(* REALIGN_TAC k = N, as the AND comes first): RBP at bot + 74956, the       *)
(* pre-hash and RSP at bot + 74844, and mldsa87_verify_pre_hash_internal     *)
(* called with RSP at bot + 74820, its frame the 74820 bytes at bot. The     *)
(* events before a call are functions of the variables VPHS87_VARS, with     *)
(* bot, which REALIGN_UNBOT_TAC expands at the end. PH and PRE are replaced  *)
(* by their definitions, VPHS87_PH and VPHS87_PRE.                           *)
(* ------------------------------------------------------------------------- *)

let VPHS87_EXEC = MLDSA_NATIVE_VERIFY_PRE_HASH_SHAKE256_87_GCC12_O2_EXEC;;

let VPHS87_VARS =
  [`sig:int64`; `m:int64`; `mlen:num`; `ctx:int64`; `ctxlen:num`;
   `pk:int64`; `sigb:num->byte`; `pkb:num->byte`; `M:num`; `C:num`;
   `mf:int64`; `mc:int64`; `pc:num`; `stackpointer:int64`;
   `returnaddress:int64`; `bot:int64`];;

let VPHS87_CALL_TAC name ilist n =
  FULL_CALL_TAC mldsa_native_libmldsa_gcc12_O2_mc VPHS87_EXEC name
   (ilist @ [`pc:num`; `read RSP s`;
             `read (memory :> bytes64 (read RSP s)) s`])
   VPHS87_VARS n;;

let VPHS87_PH =
  `num_of_bytelist(list_of_seq (mld_shake256_byte mlen M) 64)`;;

let VPHS87_PRE =
  `num_of_bytelist(mld_domain_separation_prefix 12 (bytelist_of_num ctxlen C)
    (bytelist_of_num 64 (num_of_bytelist(list_of_seq
                          (mld_shake256_byte mlen M) 64))))`;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety: SHAKE256 of the message     *)
(* into the buffer, the verification of the pre-hash with hashalg = 12, and  *)
(* the zeroing of the buffer, whose 128-bit stores need it aligned.          *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_VERIFY_PRE_HASH_SHAKE256_87_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  prove
 (MLDSA_NATIVE_VERIFY_PRE_HASH_SHAKE256_87_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th ->
    VERIF_ASSUME_CALLEE_TAC
     (MATCH_MP
       MLDSA_NATIVE_VERIFY_PRE_HASH_INTERNAL_87_GCC12_O2_IMAGE_SUBROUTINE_FULL
       th) "H_INTERNAL" THEN
    VERIF_ASSUME_CALLEE_TAC
     MLDSA_NATIVE_SHAKE256_GCC12_O2_IMAGE_SUBROUTINE_FULL "H_SHAKE") THEN
  META_EXISTS_TAC THEN REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; NONOVERLAPPING_CLAUSES; fst VPHS87_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MAP_EVERY (fun v -> FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
    is_eq(concl th) && lhs(concl th) = v)))
   [`PH:num`; mk_var("PRE'",`:num`)] THEN
  REALIGN_TAC 75003 THEN REALIGN_FRAME_TAC 75003 75003 THEN
  REALIGN_NONOV_TAC 74972
   [`sig:int64,4627`; `m:int64,mlen:num`; `ctx:int64,ctxlen:num`;
    `pk:int64,2592`; `word pc:int64,51232`;
    `word(pc + got_memset):int64,8`; `word(pc + got_memcpy):int64,8`;
    `ea:int64,el:num`; `word_add stackpointer (word 75003):int64,8`] THEN
  REALIGN_ALIGNED_TAC [74956; 74844] THEN
  ENSURES_PRESERVED_TAC "rbx_init" `RBX` THEN
  ENSURES_PRESERVED_TAC "rbp_init" `RBP` THEN
  ENSURES_PRESERVED_TAC "r12_init" `R12` THEN
  ENSURES_PRESERVED_TAC "r13_init" `R13` THEN
  ENSURES_PRESERVED_TAC "r14_init" `R14` THEN
  ENSURES_PRESERVED_TAC "r15_init" `R15` THEN
  ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC VPHS87_EXEC (1--2) THEN REALIGN_RSP_TAC THEN
  X86_STEPS_TAC VPHS87_EXEC (3--22) THEN
  VPHS87_CALL_TAC "H_SHAKE"
   [`read RDI s`; `64`; `read RDX s`; `mlen:num`; `M:num`] 23 THEN
  X86_STEPS_TAC VPHS87_EXEC (24--32) THEN
  VERIF_SHAKE256_TERMINATES_TAC THEN
  VPHS87_CALL_TAC "H_INTERNAL"
   [`read RDI s`; `read RSI s`; `64`; `read RCX s`; `ctxlen:num`;
    `read R9 s`; `word 12:int64`; `sigb:num->byte`; `pkb:num->byte`;
    VPHS87_PH; `C:num`; `12`;
    `mld_domain_separation_prefix_length 12 ctxlen 64`; VPHS87_PRE] 33 THEN
  YMM_GHOST_TAC `s33:x86state` ["YMM0","ymm0_33"] THEN
  X86_STEPS_TAC VPHS87_EXEC (34--50) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[VERIF_SUBWORD_JOIN_LO]) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN TRY(VERIF_SHAKE256_RESULT_TAC THEN NO_TAC) THEN
  REALIGN_UNBOT_TAC THEN VERIF_EMPTY_REGIONS_TAC THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_VERIFY_PRE_HASH_SHAKE256_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  prove
 (MLDSA_NATIVE_VERIFY_PRE_HASH_SHAKE256_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> CORRECT_OF_FULL_TAC
    (MP (SPEC_ALL
      MLDSA_NATIVE_VERIFY_PRE_HASH_SHAKE256_87_GCC12_O2_IMAGE_SUBROUTINE_FULL)
        th)));;

let MLDSA_NATIVE_VERIFY_PRE_HASH_SHAKE256_87_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  prove
 (MLDSA_NATIVE_VERIFY_PRE_HASH_SHAKE256_87_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> SAFE_OF_FULL_TAC
    (MP (SPEC_ALL
      MLDSA_NATIVE_VERIFY_PRE_HASH_SHAKE256_87_GCC12_O2_IMAGE_SUBROUTINE_FULL)
        th)));;
