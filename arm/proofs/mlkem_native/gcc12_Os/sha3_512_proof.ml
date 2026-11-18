(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

needs "arm/proofs/mlkem_native/gcc12_Os/sha3_512_spec.ml";;

(*** The hash of the state after absorbing, from the output of the squeezing ***)

let SHA3_512_HASH_TAC =
  REWRITE_TAC[sha3_512] THEN AP_TERM_TAC THEN
  MATCH_MP_TAC LIST_OF_SEQ_EQ THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN
  MP_TAC(SPECL [`1024`; `6`; `inp:byte list`; `72`;
                `num_of_bytelist(inp:byte list) +
                 2 EXP (8 * LENGTH inp) *
                 num_of_bytelist(keccak_pad 72 6 (LENGTH inp))`; `i:num`]
               KECCAK_SPONGE_SQUEEZE) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN REFL_TAC;;

let SHA3_512_SETUP_TAC =
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_stack_chk_guard:num`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`;
                                     `got_stack_chk_guard:num`] WORD_ADD]) THEN
  GHOST_INTRO_TAC `canary:int64` `read (memory :> bytes64 guard)` THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  ENSURES_PRESERVED_TAC "x19_init" `X19` THEN
  ENSURES_PRESERVED_TAC "x20_init" `X20`;;

let MLKEM_NATIVE_SHA3_512_GCC12_OS_IMAGE_SUBROUTINE_CORRECT = prove
 (MLKEM_NATIVE_SHA3_512_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT,
  MAP_EVERY X_GEN_TAC
   [`out:int64`; `m:int64`; `inp:byte list`; `guard:int64`; `mf:int64`;
    `ea:int64`; `el:num`; `ev:num`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 544 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (fun th -> ASSUME_TAC th THEN
              LABEL_TAC "H_MEMSET" (REWRITE_RULE[memset_contract] th))
   (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_stack_chk_guard:num`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`;
                                     `got_stack_chk_guard:num`] WORD_ADD]) THEN
  GHOST_INTRO_TAC `canary:int64` `read (memory :> bytes64 guard)` THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  ENSURES_PRESERVED_TAC "x19_init" `X19` THEN
  ENSURES_PRESERVED_TAC "x20_init" `X20` THEN
  ENSURES_INIT_TAC "s0" THEN

  (*** Saving the registers and the stack guard, and the absorption ***)

  ARM_STEPS_TAC MLKEM_NATIVE_SHA3_512_GCC12_OS_EXEC (1--4) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_SHA3_512_GCC12_OS_EXEC (5--15) THEN
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_Os_mc,MLKEM_NATIVE_SHA3_512_GCC12_OS_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_Os_mc,
    MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_OS_IMAGE_SUBROUTINE_CORRECT)
   [`read X0 s`; `72`; `read X2 s`; `LENGTH(inp:byte list)`; `6`;
    `num_of_bytelist(inp:byte list)`; `mf:int64`; `ea:int64`; `el:num`;
    `ev:num`; `pc:num`; `read SP s`; `read X30 s`] 16 THEN

  (*** The squeezing of the hash ***)

  ARM_STEPS_TAC MLKEM_NATIVE_SHA3_512_GCC12_OS_EXEC (17--21) THEN
  KECCAK_STATE_THEN `word_add (stackpointer:int64) (word 336)` (fun v ->
    ARM_SUBROUTINE_SIM_TAC
     (mlkem_native_libmlkem_gcc12_Os_mc,MLKEM_NATIVE_SHA3_512_GCC12_OS_EXEC,
      0x0,mlkem_native_libmlkem_gcc12_Os_mc,
      MLKEM_NATIVE_KECCAK_SQUEEZE_ONCE_GCC12_OS_IMAGE_SUBROUTINE_CORRECT)
     [`read X0 s`; `64`; `read X2 s`; `72`; v; `pc:num`; `read SP s`;
      `read X30 s`] 22) THEN

  (*** Zeroing the state with memset ***)

  ARM_STEPS_TAC MLKEM_NATIVE_SHA3_512_GCC12_OS_EXEC (23--26) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`;
                                     `got_memset:num`] WORD_ADD]) THEN
  LIBC_PLT_TAC MLKEM_NATIVE_SHA3_512_GCC12_OS_EXEC 26 THEN
  LIBC_CALL_TAC "H_MEMSET" MLKEM_NATIVE_SHA3_512_GCC12_OS_EXEC
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X30 s`] 31 THEN

  (*** The check of the stack guard and the return ***)

  ARM_STEPS_TAC MLKEM_NATIVE_SHA3_512_GCC12_OS_EXEC (32--32) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_SHA3_512_GCC12_OS_EXEC (33--41) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SHA3_512_HASH_TAC);;

let SHA3_512_SAFE_CALL_TAC name ilist n =
  REMOVE_THEN name (fun safety_th ->
    ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_gcc12_Os_mc,MLKEM_NATIVE_SHA3_512_GCC12_OS_EXEC,
       0x0,mlkem_native_libmlkem_gcc12_Os_mc,safety_th)
      ilist n THENL
     [EXISTS_E2_TAC (ref [`pc:num`; `m:int64`; `out:int64`; `inlen:num`;
                          `guard:int64`; `mf:int64`; `stackpointer:int64`;
                          `returnaddress:int64`]);
      LABEL_TAC name safety_th]);;

let MLKEM_NATIVE_SHA3_512_GCC12_OS_IMAGE_SUBROUTINE_SAFE = time prove
 (MLKEM_NATIVE_SHA3_512_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(fun th ->
    ASSUME_CALLEE_SAFETY_TAILED_TAC
     (MATCH_MP MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_OS_IMAGE_SUBROUTINE_SAFE
               th)
     "H_ABSORB") THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_KECCAK_SQUEEZE_ONCE_GCC12_OS_IMAGE_SUBROUTINE_SAFE
    "H_SQUEEZE" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    (REWRITE_RULE[memset_safety_contract]
      (ASSUME `memset_safety_contract (mf:int64) (ea:int64) (el:num) (ev:num)`))
    "H_MEMSET" THEN
  META_EXISTS_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  SHA3_512_SETUP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC MLKEM_NATIVE_SHA3_512_GCC12_OS_EXEC (1--4) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_SHA3_512_GCC12_OS_EXEC (5--15) THEN
  SHA3_512_SAFE_CALL_TAC "H_ABSORB"
   [`e:(uarch_event)list`; `read X0 s`; `72`; `read X2 s`; `inlen:num`;
    `6`; `pc:num`; `read SP s`; `read X30 s`] 16 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_SHA3_512_GCC12_OS_EXEC (17--21) THEN
  SHA3_512_SAFE_CALL_TAC "H_SQUEEZE"
   [`e:(uarch_event)list`; `read X0 s`; `64`; `read X2 s`; `72`;
    `pc:num`; `read SP s`; `read X30 s`] 22 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_SHA3_512_GCC12_OS_EXEC (23--26) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`;
                                     `got_memset:num`] WORD_ADD]) THEN
  LIBC_PLT_TAC MLKEM_NATIVE_SHA3_512_GCC12_OS_EXEC 26 THEN
  LIBC_SAFE_CALL_TAC "H_MEMSET" MLKEM_NATIVE_SHA3_512_GCC12_OS_EXEC
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`;
    `read X30 s`]
   (ref [`pc:num`; `m:int64`; `out:int64`; `inlen:num`; `guard:int64`;
         `mf:int64`; `stackpointer:int64`; `returnaddress:int64`])
   31 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_SHA3_512_GCC12_OS_EXEC (32--32) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_SHA3_512_GCC12_OS_EXEC (33--41) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

let MLKEM_NATIVE_SHA3_512_GCC12_OS_IMAGE_SUBROUTINE_FULL = prove
 (MLKEM_NATIVE_SHA3_512_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(fun th ->
    ASSUME_CALLEE_SAFETY_TAILED_TAC
     (MATCH_MP MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_OS_IMAGE_SUBROUTINE_FULL
               th)
     "H_ABSORB") THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_KECCAK_SQUEEZE_ONCE_GCC12_OS_IMAGE_SUBROUTINE_FULL
    "H_SQUEEZE" THEN
  FIRST_X_ASSUM(fun th ->
    ASSUME_CALLEE_SAFETY_TAILED_TAC
     (REWRITE_RULE[memset_full_contract] th) "H_MEMSET") THEN
  META_EXISTS_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  SHA3_512_SETUP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC MLKEM_NATIVE_SHA3_512_GCC12_OS_EXEC (1--4) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_SHA3_512_GCC12_OS_EXEC (5--15) THEN
  SHA3_512_SAFE_CALL_TAC "H_ABSORB"
   [`e:(uarch_event)list`; `read X0 s`; `72`; `read X2 s`; `inlen:num`;
    `6`; `num_of_bytelist(inp:byte list)`; `pc:num`; `read SP s`;
    `read X30 s`] 16 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_SHA3_512_GCC12_OS_EXEC (17--21) THEN
  KECCAK_STATE_THEN `word_add (stackpointer:int64) (word 336)` (fun v ->
    SHA3_512_SAFE_CALL_TAC "H_SQUEEZE"
     [`e:(uarch_event)list`; `read X0 s`; `64`; `read X2 s`; `72`; v;
      `pc:num`; `read SP s`; `read X30 s`] 22) THEN
  ARM_STEPS_TAC MLKEM_NATIVE_SHA3_512_GCC12_OS_EXEC (23--26) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`;
                                     `got_memset:num`] WORD_ADD]) THEN
  LIBC_PLT_TAC MLKEM_NATIVE_SHA3_512_GCC12_OS_EXEC 26 THEN
  LIBC_SAFE_CALL_TAC "H_MEMSET" MLKEM_NATIVE_SHA3_512_GCC12_OS_EXEC
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`;
    `read X30 s`]
   (ref [`pc:num`; `m:int64`; `out:int64`; `inlen:num`; `guard:int64`;
         `mf:int64`; `stackpointer:int64`; `returnaddress:int64`])
   31 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_SHA3_512_GCC12_OS_EXEC (32--32) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_SHA3_512_GCC12_OS_EXEC (33--41) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [UNDISCH_THEN `LENGTH(inp:byte list) = inlen` (SUBST_ALL_TAC o SYM) THEN
    SHA3_512_HASH_TAC;
    DISCHARGE_SAFETY_PROPERTY_TAC]);;
