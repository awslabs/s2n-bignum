(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Signing a message with a SHAKE256 pre-hash (HashML-DSA): the proof (see   *)
(* signature_pre_hash_shake256_44_spec.ml).                                  *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/gcc12_O2/signature_pre_hash_shake256_44_spec.ml";;
needs "x86/proofs/utils/mldsa_native_api.ml";;

let SPHS44_EXEC =
  MLDSA_NATIVE_SIGNATURE_PRE_HASH_SHAKE256_44_GCC12_O2_EXEC;;

(* ------------------------------------------------------------------------- *)
(* The frame. After REPEAT_GEN_AND_OFFSET_STACKPTR_TAC, stackpointer is the  *)
(* bottom of the 50187 bytes of stack below the return address, at           *)
(* stackpointer + 50187, with sk above it; the code first aligns RSP to 32   *)
(* bytes, at bot + 50156 (see utils/mldsa_native_realign.ml), with R10       *)
(* keeping the original RSP + 8, and then pushes a copy of the return        *)
(* address, RBP (at bot + 50140, the frame pointer), R15, R14, R13, R12, R10 *)
(* and RBX, and reserves the pre-hash at bot + 50028 and the saved sig at    *)
(* bot + 50020, with RSP at bot + 49996. The call of mldsa_shake256 has its  *)
(* return address at bot + 49988 (its frame the 576 bytes below it), and     *)
(* that of mldsa44_signature_pre_hash_internal, above its two arguments on   *)
(* the stack (sk and hashalg = 12), at bot + 49972, its frame the 49972      *)
(* bytes at bot. The SSE stores that zero the pre-hash through RBP need its  *)
(* alignment. The events before a call are functions of the variables        *)
(* SPHS44_VARS, with bot, which REALIGN_UNBOT_TAC expands at the end. PH and *)
(* PRE are replaced by their definitions, SPHS44_PH and SPHS44_PRE.          *)
(* ------------------------------------------------------------------------- *)

let SPHS44_VARS =
  [`sig:int64`; `m:int64`; `mlen:num`; `ctx:int64`; `ctxlen:num`;
   `rnd:int64`; `sk:int64`; `skb:num->byte`; `M:num`; `C:num`; `RND:num`;
   `MU:num`; `mf:int64`; `mc:int64`; `pc:num`; `stackpointer:int64`;
   `returnaddress:int64`; `bot:int64`];;

let SPHS44_CALL_TAC name ilist n =
  FULL_CALL_TAC mldsa_native_libmldsa_gcc12_O2_mc SPHS44_EXEC name
   (ilist @ [`pc:num`; `read RSP s`;
             `read (memory :> bytes64 (read RSP s)) s`])
   SPHS44_VARS n;;

let SPHS44_PH =
  `num_of_bytelist(list_of_seq (mld_shake256_byte mlen M) 64)`;;

let SPHS44_PRE =
  `num_of_bytelist(mld_domain_separation_prefix 12 (bytelist_of_num ctxlen C)
    (bytelist_of_num 64 (num_of_bytelist(list_of_seq
                          (mld_shake256_byte mlen M) 64))))`;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety: SHAKE256 of the message     *)
(* into the buffer, the signing of the pre-hash with hashalg = 12, and the   *)
(* zeroing of the buffer.                                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SIGNATURE_PRE_HASH_SHAKE256_44_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  prove
 (MLDSA_NATIVE_SIGNATURE_PRE_HASH_SHAKE256_44_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th ->
    API_ASSUME_CALLEE_TAC
     (MATCH_MP
       MLDSA_NATIVE_SIGNATURE_PRE_HASH_INTERNAL_44_GCC12_O2_IMAGE_SUBROUTINE_FULL
       th) "H_INTERNAL" THEN
    API_ASSUME_CALLEE_TAC
     MLDSA_NATIVE_SHAKE256_GCC12_O2_IMAGE_SUBROUTINE_FULL "H_SHAKE") THEN
  META_EXISTS_TAC THEN REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst SPHS44_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MAP_EVERY (fun v -> FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
    is_eq(concl th) && lhs(concl th) = v)))
   [`PH:num`; mk_var("PRE'",`:num`)] THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th ->
    is_eq(concl th) && lhs(concl th) = `MU:num`)) THEN
  REALIGN_TAC 50187 THEN REALIGN_FRAME_TAC 50187 50187 THEN
  REALIGN_NONOV_TAC 50156
   [`sig:int64,2420`; `m:int64,mlen:num`; `ctx:int64,ctxlen:num`;
    `rnd:int64,32`; `sk:int64,2560`; `word pc:int64,libmldsa_size`;
    `word(pc + got_memset):int64,8`; `word(pc + got_memcpy):int64,8`;
    `ea:int64,el:num`; `word_add stackpointer (word 50187):int64,16`] THEN
  REALIGN_ALIGNED_TAC [50140] THEN
  ENSURES_PRESERVED_TAC "rbx_init" `RBX` THEN
  ENSURES_PRESERVED_TAC "rbp_init" `RBP` THEN
  ENSURES_PRESERVED_TAC "r12_init" `R12` THEN
  ENSURES_PRESERVED_TAC "r13_init" `R13` THEN
  ENSURES_PRESERVED_TAC "r14_init" `R14` THEN
  ENSURES_PRESERVED_TAC "r15_init" `R15` THEN
  FULL_INIT_TAC THEN
  X86_STEPS_TAC SPHS44_EXEC (1--2) THEN REALIGN_RSP_TAC THEN
  X86_STEPS_TAC SPHS44_EXEC (3--23) THEN
  SPHS44_CALL_TAC "H_SHAKE"
   [`read RDI s`; `64`; `read RDX s`; `mlen:num`; `M:num`] 24 THEN
  X86_STEPS_TAC SPHS44_EXEC (25--33) THEN
  API_SHAKE256_TERMINATES_TAC THEN
  SPHS44_CALL_TAC "H_INTERNAL"
   [`read RDI s`; `read RSI s`; `64`; `read RCX s`; `ctxlen:num`;
    `read R9 s`; `sk:int64`; `word 12:int64`; `skb:num->byte`;
    SPHS44_PH; `C:num`; `RND:num`; `12`;
    `mld_domain_separation_prefix_length 12 ctxlen 64`; SPHS44_PRE;
    `MU:num`] 34 THEN
  X86_STEPS_TAC SPHS44_EXEC (35--51) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN TRY(API_SHAKE256_RESULT_TAC THEN NO_TAC) THEN
  ABBREV_TAC `rho = mld_sk_rho skb` THEN
  ABBREV_TAC `dcl = mld_sign_declass_44 skb MU RND` THEN
  REALIGN_UNBOT_TAC THEN API_EMPTY_REGIONS_TAC THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SIGNATURE_PRE_HASH_SHAKE256_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  prove
 (MLDSA_NATIVE_SIGNATURE_PRE_HASH_SHAKE256_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  API_SIGN_CORRECT_TAC
   MLDSA_NATIVE_SIGNATURE_PRE_HASH_SHAKE256_44_GCC12_O2_IMAGE_SUBROUTINE_FULL);;

let MLDSA_NATIVE_SIGNATURE_PRE_HASH_SHAKE256_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  prove
 (MLDSA_NATIVE_SIGNATURE_PRE_HASH_SHAKE256_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  API_SIGN_SAFE_TAC
   MLDSA_NATIVE_SIGNATURE_PRE_HASH_SHAKE256_44_GCC12_O2_IMAGE_SUBROUTINE_FULL);;
