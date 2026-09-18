(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(******************************************************************************
  Prove simple properties of straight-line RV32I arithmetic.
******************************************************************************)

needs "riscv/proofs/base.ml";;

(* add a2,a0,a1; sub a2,a2,a1 *)
let simple_mc = define_word_list "simple_mc"
 `[word 0x33; word 0x06; word 0xb5; word 0x00;
   word 0x33; word 0x06; word 0xb6; word 0x40]:byte list`;;

let SIMPLE_EXEC = RISCV_MK_EXEC_RULE simple_mc;;

(* addi zero,zero,0 at the final aligned RV32 address. *)
let pc_wrap_mc = define_word_list "pc_wrap_mc"
 `[word 0x13; word 0x00; word 0x00; word 0x00]:byte list`;;

let PC_WRAP_EXEC = RISCV_MK_EXEC_RULE pc_wrap_mc;;

let PC_WRAP_STEP_CORRECT = prove
 (`!pc.
    ensures riscv
      (\s. aligned_bytes_loaded s (word pc) pc_wrap_mc /\
           read PC s = word pc)
      (\s. read PC s = word (pc + 4))
      (MAYCHANGE [PC])`,
  REWRITE_TAC[fst PC_WRAP_EXEC] THEN
  GEN_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  RISCV_STEPS_TAC PC_WRAP_EXEC [1] THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[]);;

let PC_WRAP_CORRECT =
  let pc_wrap = prove
   (`(word ((2 EXP 32 - 4) + 4):int32) = word 0`,
    CONV_TAC (LAND_CONV (RAND_CONV NUM_REDUCE_CONV)) THEN
    CONV_TAC WORD_REDUCE_CONV) in
  CONV_RULE (ONCE_DEPTH_CONV (REWR_CONV pc_wrap))
    (SPEC `2 EXP 32 - 4` PC_WRAP_STEP_CORRECT);;

let SIMPLE_CORRECT = prove
 (`!pc a b.
    ensures riscv
      (\s. aligned_bytes_loaded s (word pc) simple_mc /\
           read PC s = word pc /\
           read A0 s = word a /\
           read A1 s = word b)
      (\s. read PC s = word (pc + 8) /\
           read A2 s = word a)
      (MAYCHANGE [PC] ,, MAYCHANGE [A2])`,
  REWRITE_TAC[fst SIMPLE_EXEC] THEN
  REPEAT GEN_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  RISCV_STEPS_TAC SIMPLE_EXEC (1--2) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[] THEN
  CONV_TAC WORD_RULE);;
