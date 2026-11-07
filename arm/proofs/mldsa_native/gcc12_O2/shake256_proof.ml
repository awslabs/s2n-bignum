(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* One-shot SHAKE256: the proof (see shake256_spec.ml).                      *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/gcc12_O2/shake256_spec.ml";;

(* ------------------------------------------------------------------------- *)
(* The calls.                                                                *)
(* ------------------------------------------------------------------------- *)

let LOCAL_INIT_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mldsa_native_libmldsa_gcc12_O2_mc,MLDSA_NATIVE_SHAKE256_GCC12_O2_EXEC,
    0x0,mldsa_native_libmldsa_gcc12_O2_mc,
    MLDSA_NATIVE_SHAKE256_INIT_GCC12_O2_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_ABSORB_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mldsa_native_libmldsa_gcc12_O2_mc,MLDSA_NATIVE_SHAKE256_GCC12_O2_EXEC,
    0x0,mldsa_native_libmldsa_gcc12_O2_mc,
    MLDSA_NATIVE_SHAKE256_ABSORB_GCC12_O2_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_FINALIZE_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mldsa_native_libmldsa_gcc12_O2_mc,MLDSA_NATIVE_SHAKE256_GCC12_O2_EXEC,
    0x0,mldsa_native_libmldsa_gcc12_O2_mc,
    MLDSA_NATIVE_SHAKE256_FINALIZE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_SQUEEZE_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mldsa_native_libmldsa_gcc12_O2_mc,MLDSA_NATIVE_SHAKE256_GCC12_O2_EXEC,
    0x0,mldsa_native_libmldsa_gcc12_O2_mc,
    MLDSA_NATIVE_SHAKE256_SQUEEZE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_RELEASE_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mldsa_native_libmldsa_gcc12_O2_mc,MLDSA_NATIVE_SHAKE256_GCC12_O2_EXEC,
    0x0,mldsa_native_libmldsa_gcc12_O2_mc,
    MLDSA_NATIVE_SHAKE256_RELEASE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT);;

(*** The GOT entry of the stack guard at word(pc + got_stack_chk_guard), ***)
(*** the form of the address in the spec of finalize                     ***)

let GUARD_ADDR_TAC =
  FIRST_ASSUM(ASSUME_TAC o REWRITE_RULE[GSYM WORD_ADD] o check (fun th ->
    can (term_match []
          `read (memory :> bytes64 (word_add (word pc) (word n))) s =
           guard:int64`) (concl th)));;

(* ------------------------------------------------------------------------- *)
(* Correctness proof. The frame of 272 bytes is at stackpointer + 256, with  *)
(* the context at stackpointer + 312 and the canary at stackpointer + 520;   *)
(* absorbing and squeezing use the 256 bytes below it, finalizing the top    *)
(* 32 of them. S1 and p1 are the state and the position after absorbing.     *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SHAKE256_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_SHAKE256_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  let EXEC = MLDSA_NATIVE_SHAKE256_GCC12_O2_EXEC in
  MAP_EVERY X_GEN_TAC
   [`out:int64`; `outlen:num`; `src:int64`; `inlen:num`; `M:num`;
    `guard:int64`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 528 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_stack_chk_guard:num`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`;
                                     `got_stack_chk_guard:num`] WORD_ADD]) THEN
  GHOST_INTRO_TAC `canary:int64` `read (memory :> bytes64 guard)` THEN
  ABBREV_TAC `S1 = FST(mld_keccak_absorb 136 (word 0) 0 inlen M)` THEN
  ABBREV_TAC `p1 = SND(mld_keccak_absorb 136 (word 0) 0 inlen M)` THEN
  SUBGOAL_THEN `p1 <= 136` ASSUME_TAC THENL
   [EXPAND_TAC "p1" THEN REWRITE_TAC[mld_keccak_absorb] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    MP_TAC(SPECL [`0 + inlen`; `136`] MOD_LT_EQ) THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[mld_shake256_byte; mld_shake256_state] THEN
  ASM_REWRITE_TAC[] THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  ENSURES_PRESERVED_TAC "x19_init" `X19` THEN
  ENSURES_PRESERVED_TAC "x20_init" `X20` THEN
  ENSURES_PRESERVED_TAC "x21_init" `X21` THEN
  ENSURES_PRESERVED_TAC "x22_init" `X22` THEN
  ENSURES_PRESERVED_TAC "x23_init" `X23` THEN
  ENSURES_INIT_TAC "s0" THEN

  (*** The prologue, with the canary stored at stackpointer + 520 ***)

  ARM_STEPS_TAC EXEC (1--3) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC EXEC (4--15) THEN

  (*** init ***)

  LOCAL_INIT_TAC [`read X0 s`; `pc:num`; `read X30 s`] 16 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN

  (*** absorb ***)

  ARM_STEPS_TAC EXEC (17--20) THEN
  KECCAK_STATE_AT_TAC `word_add stackpointer (word 312):int64` THEN
  LOCAL_ABSORB_TAC [`read X0 s`; `read X1 s`; `inlen:num`;
                    `word 0:1600 word`; `0`; `M:num`; `pc:num`; `read SP s`;
                    `read X30 s`] 21 THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [ASSUME `FST(mld_keccak_absorb 136 (word 0) 0 inlen M) = S1`;
    ASSUME `SND(mld_keccak_absorb 136 (word 0) 0 inlen M) = p1`;
    READ_MEMORY_WBYTES_1600]) THEN

  (*** finalize ***)

  ARM_STEPS_TAC EXEC (22--23) THEN
  KECCAK_STATE_AT_TAC `word_add stackpointer (word 312):int64` THEN
  GUARD_ADDR_TAC THEN
  LOCAL_FINALIZE_TAC [`read X0 s`; `S1:1600 word`; `p1:num`; `guard:int64`;
                      `pc:num`; `read SP s`; `read X30 s`] 24 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN

  (*** squeeze ***)

  ARM_STEPS_TAC EXEC (25--28) THEN
  KECCAK_STATE_AT_TAC `word_add stackpointer (word 312):int64` THEN
  LOCAL_SQUEEZE_TAC [`read X0 s`; `outlen:num`; `read X2 s`;
                     `mld_keccak_finalize 136 31 S1 p1`; `136`; `pc:num`;
                     `read SP s`; `read X30 s`] 29 THEN

  (*** release, and the check of the canary ***)

  ARM_STEPS_TAC EXEC (30--31) THEN
  LOCAL_RELEASE_TAC [`read X0 s`; `pc:num`; `read X30 s`] 32 THEN
  ARM_STEPS_TAC EXEC (33--33) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC EXEC (34--43) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]);;
