(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(******************************************************************************
  Verify an RV32I routine that swaps two 32-bit memory words.
******************************************************************************)

needs "riscv/proofs/base.ml";;

(* lw t0,0(a0); lw t1,0(a1); sw t0,0(a1); sw t1,0(a0) *)
let memory_mc = define_word_list "memory_mc"
 `[word 0x83; word 0x22; word 0x05; word 0x00;
   word 0x03; word 0xa3; word 0x05; word 0x00;
   word 0x23; word 0xa0; word 0x55; word 0x00;
   word 0x23; word 0x20; word 0x65; word 0x00]:byte list`;;

let MEMORY_EXEC = RISCV_MK_EXEC_RULE memory_mc;;

let MEMORY_CORRECT = prove
 (`!pc (p0:int32) p1 x y e.
    aligned 4 p0 /\
    aligned 4 p1 /\
    nonoverlapping ((word pc):int32,LENGTH memory_mc) (p0,4) /\
    nonoverlapping ((word pc):int32,LENGTH memory_mc) (p1,4) /\
    nonoverlapping (p0,4) (p1,4)
    ==> ensures riscv
      (\s. aligned_bytes_loaded s (word pc) memory_mc /\
           read PC s = word pc /\
           read A0 s = p0 /\
           read A1 s = p1 /\
           read (memory :> bytes32 p0) s = x /\
           read (memory :> bytes32 p1) s = y /\
           read events s = e)
      (\s. read PC s = word (pc + 16) /\
           read (memory :> bytes32 p0) s = y /\
           read (memory :> bytes32 p1) s = x /\
           read events s =
           CONS (EventStore (p0,4))
             (CONS (EventStore (p1,4))
               (CONS (EventLoad (p1,4))
                 (CONS (EventLoad (p0,4)) e))))
      (MAYCHANGE [PC] ,, MAYCHANGE [T0; T1] ,,
       MAYCHANGE [memory :> bytes32 p0; memory :> bytes32 p1] ,,
       MAYCHANGE [events])`,
  REWRITE_TAC[fst MEMORY_EXEC] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  RISCV_STEPS_TAC MEMORY_EXEC (1--4) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[]);;
