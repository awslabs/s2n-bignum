(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(******************************************************************************
  Promote RV32I core theorems to psABI subroutine theorems.
******************************************************************************)

needs "riscv/proofs/base.ml";;

(* First promote a core theorem when JALR immediately follows the core. *)
let nostack_mc = define_word_list "nostack_mc"
 `[word 0x13; word 0x05; word 0x15; word 0x00;
   word 0x67; word 0x80; word 0x00; word 0x00]:byte list`;;

let NOSTACK_EXEC = RISCV_MK_EXEC_RULE nostack_mc;;

let NOSTACK_CORE_CORRECT = prove
 (`!pc a.
    ensures riscv
      (\s. aligned_bytes_loaded s (word pc) nostack_mc /\
           read PC s = word pc /\
           C_ARGUMENTS [a] s)
      (\s. read PC s = word (pc + 4) /\
           C_RETURN s = word_add a (word 1))
      (MAYCHANGE [PC] ,, MAYCHANGE [A0])`,
  REWRITE_TAC[fst NOSTACK_EXEC; C_ARGUMENTS; C_RETURN] THEN
  REPEAT STRIP_TAC THEN
  RISCV_SIM_TAC NOSTACK_EXEC [1]);;

let NOSTACK_SUBROUTINE_CORRECT = prove
 (`!pc a (returnaddress:int32).
    aligned 4 returnaddress
    ==> ensures riscv
      (\s. aligned_bytes_loaded s (word pc) nostack_mc /\
           read PC s = word pc /\
           read RA s = returnaddress /\
           C_ARGUMENTS [a] s)
      (\s. read PC s = returnaddress /\
           C_RETURN s = word_add a (word 1))
      MAYCHANGE_REGS_PERMITTED_BY_ABI`,
  REWRITE_TAC[fst NOSTACK_EXEC] THEN
  RISCV_ADD_RETURN_NOSTACK_TAC NOSTACK_EXEC
    (REWRITE_RULE[fst NOSTACK_EXEC] NOSTACK_CORE_CORRECT));;

(* Save s0/s1; increment a0; restore s0/s1; return through ra. *)
let subroutine_mc = define_word_list "subroutine_mc"
 `[word 0x13; word 0x01; word 0x01; word 0xff;
   word 0x23; word 0x20; word 0x81; word 0x00;
   word 0x23; word 0x22; word 0x91; word 0x00;
   word 0x13; word 0x05; word 0x15; word 0x00;
   word 0x03; word 0x24; word 0x01; word 0x00;
   word 0x83; word 0x24; word 0x41; word 0x00;
   word 0x13; word 0x01; word 0x01; word 0x01;
   word 0x67; word 0x80; word 0x00; word 0x00]:byte list`;;

let SUBROUTINE_EXEC = RISCV_MK_EXEC_RULE subroutine_mc;;

let SUBROUTINE_STACK_ALIGNED = prove
 (`!stackpointer:int32.
    aligned 16 stackpointer
    ==> aligned 16 (word_sub stackpointer (word 16))`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC ALIGNED_WORD_SUB THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ALIGNED_WORD; DIMINDEX_32; VAL_WORD] THEN
  CONV_TAC NUMBER_RULE);;

let SUBROUTINE_CORE_CORRECT = prove
 (`!pc a.
    ensures riscv
      (\s. aligned_bytes_loaded s (word pc) subroutine_mc /\
           read PC s = word (pc + 12) /\
           C_ARGUMENTS [a] s)
      (\s. read PC s = word (pc + 16) /\
           C_RETURN s = word_add a (word 1))
      (MAYCHANGE [PC] ,, MAYCHANGE [A0])`,
  REWRITE_TAC[fst SUBROUTINE_EXEC; C_ARGUMENTS; C_RETURN] THEN
  REPEAT STRIP_TAC THEN
  RISCV_SIM_TAC SUBROUTINE_EXEC [1]);;

let SUBROUTINE_CORRECT = prove
 (`!pc a (stackpointer:int32) (returnaddress:int32).
    aligned 16 stackpointer /\
    aligned 4 returnaddress /\
    nonoverlapping
      ((word pc):int32,LENGTH subroutine_mc)
      (word_sub stackpointer (word 16),16)
    ==> ensures riscv
      (\s. aligned_bytes_loaded s (word pc) subroutine_mc /\
           read PC s = word pc /\
           read SP s = stackpointer /\
           read RA s = returnaddress /\
           C_ARGUMENTS [a] s)
      (\s. read PC s = returnaddress /\
           read SP s = stackpointer /\
           C_RETURN s = word_add a (word 1))
      (MAYCHANGE_REGS_PERMITTED_BY_ABI ,,
       MAYCHANGE
        [memory :> bytes (word_sub stackpointer (word 16),16)])`,
  REWRITE_TAC[fst SUBROUTINE_EXEC] THEN
  RISCV_ADD_RETURN_STACK_TAC SUBROUTINE_EXEC
    (REWRITE_RULE[fst SUBROUTINE_EXEC] SUBROUTINE_CORE_CORRECT)
    `[S0; S1]` 16);;
