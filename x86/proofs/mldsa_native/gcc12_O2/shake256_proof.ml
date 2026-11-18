(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* One-shot SHAKE256: the proof (see shake256_spec.ml).                      *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/gcc12_O2/shake256_spec.ml";;
needs "x86/proofs/utils/mldsa_native_absorb.ml";;
needs "x86/proofs/utils/mldsa_native_full.ml";;

(* ------------------------------------------------------------------------- *)
(* The calls, with the FULL theorems of the callees assumed as "H_INIT",     *)
(* "H_ABSORB", "H_FINALIZE", "H_SQUEEZE" and "H_RELEASE".                    *)
(* ------------------------------------------------------------------------- *)

let SHAKE256_CALL_TAC name ilist n =
  FULL_CALL_TAC mldsa_native_libmldsa_gcc12_O2_mc
   MLDSA_NATIVE_SHAKE256_GCC12_O2_EXEC name
   (ilist @ [`pc:num`; `read RSP s`;
             `read (memory :> bytes64 (read RSP s)) s`])
   [`out:int64`; `outlen:num`; `src:int64`; `inlen:num`; `pc:num`;
    `stackpointer:int64`; `returnaddress:int64`] n;;

(*** The position after absorbing inlen bytes at position 0 ***)

let SHAKE256_ABSORB_POS = prove
 (`!inlen M. SND(mld_keccak_absorb 136 (word 0) 0 inlen M) = inlen MOD 136`,
  REWRITE_TAC[mld_keccak_absorb] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[ADD_CLAUSES]);;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety. The frame of 248 bytes is   *)
(* at stackpointer + 328, with the context at its bottom; absorbing and      *)
(* squeezing use the 320 bytes below the return address of the calls at      *)
(* stackpointer + 320, finalizing the top 32 of them. S1 is the state after  *)
(* absorbing, and the position after it is inlen MOD 136, so that the events *)
(* of the calls are functions of the lengths and the addresses only.         *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SHAKE256_GCC12_O2_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_SHAKE256_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT,
  let EXEC = MLDSA_NATIVE_SHAKE256_GCC12_O2_EXEC in
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_SHAKE256_INIT_GCC12_O2_IMAGE_SUBROUTINE_FULL "H_INIT" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_SHAKE256_ABSORB_GCC12_O2_IMAGE_SUBROUTINE_FULL "H_ABSORB" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_SHAKE256_FINALIZE_GCC12_O2_IMAGE_SUBROUTINE_FULL
    "H_FINALIZE" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_SHAKE256_SQUEEZE_GCC12_O2_IMAGE_SUBROUTINE_FULL
    "H_SQUEEZE" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_SHAKE256_RELEASE_GCC12_O2_IMAGE_SUBROUTINE_FULL
    "H_RELEASE" THEN
  META_EXISTS_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES; fst EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ABBREV_TAC `S1 = FST(mld_keccak_absorb 136 (word 0) 0 inlen M)` THEN
  SUBGOAL_THEN `inlen MOD 136 <= 136` ASSUME_TAC THENL
   [MP_TAC(SPECL [`inlen:num`; `136`] MOD_LT_EQ) THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[mld_shake256_byte; mld_shake256_state; SHAKE256_ABSORB_POS] THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY (fun (n,c) -> ENSURES_PRESERVED_TAC n c)
   [("rbx_init",`RBX`); ("rbp_init",`RBP`); ("r12_init",`R12`);
    ("r13_init",`R13`); ("r14_init",`R14`)] THEN
  FULL_INIT_TAC THEN

  (*** The prologue, with the context at stackpointer + 328 ***)

  X86_STEPS_TAC EXEC (1--13) THEN

  (*** init ***)

  SHAKE256_CALL_TAC "H_INIT" [`read RDI s`] 14 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN

  (*** absorb ***)

  X86_STEPS_TAC EXEC (15--18) THEN
  KECCAK_STATE_AT_TAC `word_add stackpointer (word 328):int64` THEN
  SHAKE256_CALL_TAC "H_ABSORB"
   [`read RDI s`; `read RSI s`; `inlen:num`; `word 0:1600 word`; `0`;
    `M:num`] 19 THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [ASSUME `FST(mld_keccak_absorb 136 (word 0) 0 inlen M) = S1`;
    SHAKE256_ABSORB_POS; READ_MEMORY_WBYTES_1600]) THEN

  (*** finalize ***)

  X86_STEPS_TAC EXEC (20--21) THEN
  KECCAK_STATE_AT_TAC `word_add stackpointer (word 328):int64` THEN
  SHAKE256_CALL_TAC "H_FINALIZE"
   [`read RDI s`; `S1:1600 word`; `inlen MOD 136`] 22 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN

  (*** squeeze ***)

  X86_STEPS_TAC EXEC (23--26) THEN
  KECCAK_STATE_AT_TAC `word_add stackpointer (word 328):int64` THEN
  SHAKE256_CALL_TAC "H_SQUEEZE"
   [`read RDI s`; `outlen:num`; `read RDX s`;
    `mld_keccak_finalize 136 31 S1 (inlen MOD 136)`; `136`] 27 THEN

  (*** release, and the epilogue ***)

  X86_STEPS_TAC EXEC (28--29) THEN
  SHAKE256_CALL_TAC "H_RELEASE" [`read RDI s`] 30 THEN
  X86_STEPS_TAC EXEC (31--37) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SHAKE256_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_SHAKE256_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  CORRECT_OF_FULL_TAC MLDSA_NATIVE_SHAKE256_GCC12_O2_IMAGE_SUBROUTINE_FULL);;

let MLDSA_NATIVE_SHAKE256_GCC12_O2_IMAGE_SUBROUTINE_SAFE = prove
 (MLDSA_NATIVE_SHAKE256_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  SAFE_OF_FULL_TAC MLDSA_NATIVE_SHAKE256_GCC12_O2_IMAGE_SUBROUTINE_FULL);;
