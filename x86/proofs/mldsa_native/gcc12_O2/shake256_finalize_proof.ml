(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Finalizing the absorbing into a SHAKE256 context: the proof (see          *)
(* shake256_finalize_spec.ml).                                               *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/gcc12_O2/shake256_finalize_spec.ml";;
needs "x86/proofs/utils/mldsa_native_absorb.ml";;
needs "x86/proofs/utils/mldsa_native_full.ml";;

(* ------------------------------------------------------------------------- *)
(* The calls of mldsa_keccakf1600_xor_bytes, with the FULL theorem assumed   *)
(* as "H_XOR", whose events depend on the addresses and the position only,   *)
(* and a byte b at stackpointer + off in state sname as a 1-byte array.      *)
(* ------------------------------------------------------------------------- *)

let SHAKE256_FINALIZE_XOR_TAC ilist n =
  FULL_CALL_TAC mldsa_native_libmldsa_gcc12_O2_mc
   MLDSA_NATIVE_SHAKE256_FINALIZE_GCC12_O2_EXEC "H_XOR" ilist
   [`ctx:int64`; `pos:num`; `pc:num`; `stackpointer:int64`;
    `returnaddress:int64`] n;;

let SHAKE256_FINALIZE_BYTE_FACT_TAC sname off n =
  let s = mk_var(sname,`:x86state`) in
  SUBGOAL_THEN
   (subst [s,`s:x86state`; n,`n:num`; off,`off:num`]
     `read (memory :> bytes (word_add stackpointer (word off),1)) s = n`)
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_BYTES8] THEN
    REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN
    ASM_REWRITE_TAC[VAL_WORD] THEN
    REWRITE_TAC[DIMINDEX_8] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC];;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety. With the stack pointer at   *)
(* the bottom of the 32-byte frame, the bytes 0x1F and 0x80 are stored at    *)
(* stackpointer + 23 and + 22, and XORed into the state at the position and  *)
(* at 135 by the two calls; the code is straight-line, and the events depend *)
(* on the position only through the arguments of the first call.             *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SHAKE256_FINALIZE_GCC12_O2_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_SHAKE256_FINALIZE_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT,
  let EXEC = MLDSA_NATIVE_SHAKE256_FINALIZE_GCC12_O2_EXEC in
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_KECCAKF1600_XOR_BYTES_GCC12_O2_IMAGE_SUBROUTINE_FULL
    "H_XOR" THEN
  META_EXISTS_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              READ_MEMORY_WBYTES_1600; fst EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_PRESERVED_TAC "rbx_init" `RBX` THEN
  FULL_INIT_TAC THEN
  X86_STEPS_TAC EXEC (1--8) THEN
  ARGS_64_TAC [`pos:num`] THEN
  SHAKE256_FINALIZE_BYTE_FACT_TAC "s8" `23` `31` THEN
  SUBGOAL_THEN `pos + 1 <= 200` ASSUME_TAC THENL
   [UNDISCH_TAC `pos <= 136` THEN ARITH_TAC; ALL_TAC] THEN
  X86_STEPS_TAC EXEC (9--9) THEN
  KECCAK_STATE_AT_TAC `ctx:int64` THEN
  SHAKE256_FINALIZE_XOR_TAC
   [`read RDI s`; `read RSI s`; `pos:num`; `1`; `S:1600 word`; `31`;
    `pc:num`; `read RSP s`; `read (memory :> bytes64 (read RSP s)) s`] 10 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
  X86_STEPS_TAC EXEC (11--15) THEN
  SHAKE256_FINALIZE_BYTE_FACT_TAC "s15" `22` `128` THEN
  KECCAK_STATE_AT_TAC `ctx:int64` THEN
  KECCAK_STATE_THEN `ctx:int64` (fun v ->
    SHAKE256_FINALIZE_XOR_TAC
     [`read RDI s`; `read RSI s`; `135`; `1`; v; `128`; `pc:num`;
      `read RSP s`; `read (memory :> bytes64 (read RSP s)) s`] 16) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
  X86_STEPS_TAC EXEC (17--20) THEN
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
