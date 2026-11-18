(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Finalizing the absorbing into a SHAKE256 context: the proof (see          *)
(* shake256_finalize_spec.ml).                                               *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/gcc12_O2/shake256_finalize_spec.ml";;
needs "arm/proofs/utils/mldsa_native_full.ml";;

(* ------------------------------------------------------------------------- *)
(* The calls of mldsa_keccakf1600_xor_bytes, with the FULL theorem assumed   *)
(* as "H_XOR", whose events depend on the addresses and the position only,   *)
(* and a byte b at stackpointer + off in state sname as a 1-byte array.      *)
(* ------------------------------------------------------------------------- *)

let SHAKE256_FINALIZE_XOR_TAC ilist n =
  REMOVE_THEN "H_XOR" (fun th ->
    ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true
     (mldsa_native_libmldsa_gcc12_O2_mc,
      MLDSA_NATIVE_SHAKE256_FINALIZE_GCC12_O2_EXEC,
      0x0,mldsa_native_libmldsa_gcc12_O2_mc,th)
     ilist n THENL
     [EXISTS_E2_TAC (ref [`ctx:int64`; `pos:num`; `guard:int64`; `pc:num`;
                          `stackpointer:int64`; `returnaddress:int64`]);
      LABEL_TAC "H_XOR" th]);;

let SHAKE256_FINALIZE_BYTE_FACT_TAC sname off n =
  let s = mk_var(sname,`:armstate`) in
  SUBGOAL_THEN
   (subst [s,`s:armstate`; n,`n:num`; off,`off:num`]
     `read (memory :> bytes (word_add stackpointer (word off),1)) s = n`)
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_BYTES8] THEN
    REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN
    ASM_REWRITE_TAC[VAL_WORD] THEN
    REWRITE_TAC[DIMINDEX_8] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC];;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety. The bytes 0x1F and 0x80 are *)
(* stored at stackpointer + 23 and + 22 of the 32-byte frame, and XORed into *)
(* the state at the position and at 135 by the two calls; the code is        *)
(* straight-line, and the events depend on the position only through the     *)
(* arguments of the first call.                                              *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SHAKE256_FINALIZE_GCC12_O2_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_SHAKE256_FINALIZE_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT,
  let EXEC = MLDSA_NATIVE_SHAKE256_FINALIZE_GCC12_O2_EXEC in
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_KECCAKF1600_XOR_BYTES_GCC12_O2_IMAGE_SUBROUTINE_FULL
    "H_XOR" THEN
  META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `ctx:int64`; `S:1600 word`; `pos:num`;
    `guard:int64`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 32 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              READ_MEMORY_WBYTES_1600; fst EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_stack_chk_guard:num`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`;
                                     `got_stack_chk_guard:num`] WORD_ADD]) THEN
  GHOST_INTRO_TAC `canary:int64` `read (memory :> bytes64 guard)` THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  ENSURES_PRESERVED_TAC "x19_init" `X19` THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC EXEC (1--4) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC EXEC (5--14) THEN
  ARGS_64_TAC [`pos:num`] THEN
  SHAKE256_FINALIZE_BYTE_FACT_TAC "s14" `23` `31` THEN
  SUBGOAL_THEN `pos + 1 <= 200` ASSUME_TAC THENL
   [UNDISCH_TAC `pos <= 136` THEN ARITH_TAC; ALL_TAC] THEN
  ARM_STEPS_TAC EXEC (15--15) THEN
  KECCAK_STATE_AT_TAC `ctx:int64` THEN
  SHAKE256_FINALIZE_XOR_TAC
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `pos:num`; `1`;
    `S:1600 word`; `31`; `pc:num`; `read X30 s`] 16 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
  ARM_STEPS_TAC EXEC (17--21) THEN
  SHAKE256_FINALIZE_BYTE_FACT_TAC "s21" `22` `128` THEN
  KECCAK_STATE_AT_TAC `ctx:int64` THEN
  KECCAK_STATE_THEN `ctx:int64` (fun v ->
    SHAKE256_FINALIZE_XOR_TAC
     [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `135`; `1`; v;
      `128`; `pc:num`; `read X30 s`] 22) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
  ARM_STEPS_TAC EXEC (23--23) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC EXEC (24--33) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[mld_keccak_finalize] THEN CONV_TAC NUM_REDUCE_CONV;
    DISCHARGE_SAFETY_PROPERTY_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SHAKE256_FINALIZE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_SHAKE256_FINALIZE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  CORRECT_OF_FULL_TAC
    MLDSA_NATIVE_SHAKE256_FINALIZE_GCC12_O2_IMAGE_SUBROUTINE_FULL);;

let MLDSA_NATIVE_SHAKE256_FINALIZE_GCC12_O2_IMAGE_SUBROUTINE_SAFE = prove
 (MLDSA_NATIVE_SHAKE256_FINALIZE_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  SAFE_OF_FULL_TAC
    MLDSA_NATIVE_SHAKE256_FINALIZE_GCC12_O2_IMAGE_SUBROUTINE_FULL);;
