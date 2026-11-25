(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Regression tests of bstep (common/bstep.ml, arm/proofs/bstep.ml) on the   *)
(* programs of arm/bstep_tests/bstep_tests.S, with make                      *)
(* bstep_tests/bstep_tests.correct:                                          *)
(*                                                                           *)
(*  - contracts with the named frame MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_  *)
(*    ABI, alone and as a clause: a function proved by one block, a tail     *)
(*    call (b) and a call (bl) of it after a block by ARM_BSTEP_CALL_TAC,    *)
(*    with the frame of the block and the callee's composed;                 *)
(*  - ADRP within a block, in code at a 4096-aligned pc: the pages are       *)
(*    word_add (word pc) (word k), an LDR from a page finds the fact about   *)
(*    the address, and a br to an address computed by ADRP and ADD goes on   *)
(*    in the code.                                                           *)
(* ========================================================================= *)

needs "arm/proofs/bstep.ml";;

let bstep_tests_mc =
  define_from_elf "bstep_tests_mc" "arm/bstep_tests/bstep_tests.o";;

let BSTEP_TESTS_EXEC = ARM_MK_EXEC_RULE bstep_tests_mc;;

(* ------------------------------------------------------------------------- *)
(* Calls.                                                                    *)
(* ------------------------------------------------------------------------- *)

let BSTEP_F_CORRECT = prove
 (`!pc a returnaddress.
        ensures arm
         (\s. aligned_bytes_loaded s (word pc) bstep_tests_mc /\
              read PC s = word(pc + 0x20) /\
              read X1 s = a /\ read X30 s = returnaddress)
         (\s. read PC s = returnaddress /\ read X0 s = word_add a (word 1))
         MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI`,
  REPEAT STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
  ARM_BSTEP_TAC BSTEP_TESTS_EXEC (1--2) THEN
  BSTEP_FINAL_TAC THEN ASM_REWRITE_TAC[]);;

(* A tail call: the step before it and the callee have the same frame.      *)

let BSTEP_TAIL_CORRECT = prove
 (`!pc a returnaddress.
        ensures arm
         (\s. aligned_bytes_loaded s (word pc) bstep_tests_mc /\
              read PC s = word pc /\
              read X0 s = a /\ read X30 s = returnaddress)
         (\s. read PC s = returnaddress /\ read X0 s = word_add a (word 1))
         MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI`,
  REPEAT STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
  ARM_BSTEP_TAC BSTEP_TESTS_EXEC (1--2) THEN
  ARM_BSTEP_CALL_TAC BSTEP_TESTS_EXEC
   (SPECL [`pc:num`; `a:int64`; `returnaddress:int64`] BSTEP_F_CORRECT)
   "s3" THEN
  BSTEP_FINAL_TAC THEN ASM_REWRITE_TAC[]);;

(* A call, with the named frame as a clause of the caller's frame, and a     *)
(* block after it.                                                           *)

let BSTEP_CALL_CORRECT = prove
 (`!pc a returnaddress.
        ensures arm
         (\s. aligned_bytes_loaded s (word pc) bstep_tests_mc /\
              read PC s = word(pc + 0x8) /\
              read X0 s = a /\ read X30 s = returnaddress)
         (\s. read PC s = returnaddress /\ read X0 s = word_add a (word 3))
         (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X19; X30])`,
  REPEAT STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
  ARM_BSTEP_TAC BSTEP_TESTS_EXEC (1--3) THEN
  ARM_BSTEP_CALL_TAC BSTEP_TESTS_EXEC
   (SPECL [`pc:num`; `a:int64`; `word(pc + 0x14):int64`] BSTEP_F_CORRECT)
   "s4" THEN
  ARM_BSTEP_TAC BSTEP_TESTS_EXEC (5--6) THEN
  BSTEP_FINAL_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE);;

(* ------------------------------------------------------------------------- *)
(* ADRP, in one block.                                                       *)
(* ------------------------------------------------------------------------- *)

let BSTEP_ADRP_CORRECT = prove
 (`!pc v returnaddress.
        aligned 4096 (word pc:int64)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bstep_tests_mc /\
                  read PC s = word(pc + 0x28) /\
                  read X30 s = returnaddress /\
                  read (memory :> bytes64 (word_add (word pc) (word 0x2008)))
                       s = v)
             (\s. read PC s = returnaddress /\ read X0 s = v /\
                  read X16 s = word_add (word pc) (word 0x2008) /\
                  read X2 s = word_add (word pc) (word 0x44))
             (MAYCHANGE [PC; X0; X2; X16; X17] ,, MAYCHANGE [events])`,
  REPEAT STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
  ARM_BSTEP_TAC BSTEP_TESTS_EXEC (1--8) THEN
  BSTEP_FINAL_TAC THEN ASM_REWRITE_TAC[]);;
