(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(******************************************************************************
  Verify conditional and indirect RV32I control flow.
******************************************************************************)

needs "riscv/proofs/base.ml";;

(* bne a0,a1,+8; addi a2,zero,1; addi a3,zero,0 *)
let branch_mc = define_word_list "branch_mc"
 `[word 0x63; word 0x14; word 0xb5; word 0x00;
   word 0x13; word 0x06; word 0x10; word 0x00;
   word 0x93; word 0x06; word 0x00; word 0x00]:byte list`;;

let BRANCH_EXEC = RISCV_MK_EXEC_RULE branch_mc;;

let BRANCH_CORRECT = prove
 (`!pc a b e.
    ensures riscv
      (\s. aligned_bytes_loaded s (word pc) branch_mc /\
           read PC s = word pc /\
           read A0 s = a /\
           read A1 s = b /\
           read A2 s = word 2 /\
           read events s = e)
      (\s. read PC s = word (pc + 12) /\
           read A2 s = (if a = b then word 1 else word 2) /\
           read events s =
           CONS (EventJump
             (word pc,if a = b then word (pc + 4) else word (pc + 8))) e)
      (MAYCHANGE [PC] ,, MAYCHANGE [A2; A3] ,, MAYCHANGE [events])`,
  REWRITE_TAC[fst BRANCH_EXEC] THEN
  REPEAT GEN_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  RISCV_STEPS_TAC BRANCH_EXEC [1] THEN
  FIRST_X_ASSUM MP_TAC THEN
  COND_CASES_TAC THEN DISCH_TAC THENL
   [RISCV_STEPS_TAC BRANCH_EXEC (2--3);
    RISCV_STEPS_TAC BRANCH_EXEC [2]] THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[]);;

(* jalr zero,ra,0 *)
let jalr_mc = define_word_list "jalr_mc"
 `[word 0x67; word 0x80; word 0x00; word 0x00]:byte list`;;

let JALR_EXEC = RISCV_MK_EXEC_RULE jalr_mc;;

let JALR_EVENT_CORRECT = prove
 (`!pc (returnaddress:int32) e.
    aligned 4 returnaddress
    ==> ensures riscv
      (\s. aligned_bytes_loaded s (word pc) jalr_mc /\
           read PC s = word pc /\
           read RA s = returnaddress /\
           read events s = e)
      (\s. read PC s = returnaddress /\
           read events s =
           CONS (EventJump (word pc,returnaddress)) e)
      (MAYCHANGE [PC] ,, MAYCHANGE [events])`,
  REWRITE_TAC[fst JALR_EXEC] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  RISCV_STEPS_TAC JALR_EXEC [1] THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_SIMP_TAC[RISCV_JALR_ALIGNED_MASK_WORD]);;
