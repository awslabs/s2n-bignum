(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Tests for LDST.                                                           *)
(* ========================================================================= *)

loadt "arm/proofs/base.ml";;

(* ld1, one register, SIMD, 64-bit, immediate offset, post-index *)
(* ld1 v0[0], [x0], #8 *)
let LD1_1_SIMD_64_IMM_POST = define_word_list "LD1_1_SIMD_64_IMM_POST"
  `(CONS ((word 0x00):8 word) 
     (CONS ((word 0x70):8 word) 
       (CONS ((word 0xDF):8 word) 
         (CONS ((word 0x0C):8 word) []))))`;;

let LD1_1_SIMD_64_IMM_POST_EXEC = ARM_MK_EXEC_RULE LD1_1_SIMD_64_IMM_POST;;

let LD1_1_SIMD_64_IMM_POST_TEST = time prove
 (`!x a pc.
      True
      ==>
        ensures arm
             (\s. aligned_bytes_loaded s (word pc) LD1_1_SIMD_64_IMM_POST /\
                  read PC s = word pc /\
                  C_ARGUMENTS [x] s /\
                  read (memory :> bytes(x, 8)) s = val a)
             (\s. read PC s = word (pc + 0x04) /\
                  read (DREG' (word 0:5 word)) s = a)
             (MAYCHANGE [PC; X0],,
              MAYCHANGE [Q0])`,
  MAP_EVERY X_GEN_TAC [`x:int64`; `a:int64`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_ACCSTEPS_TAC LD1_1_SIMD_64_IMM_POST_EXEC [] [1] THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[]
  );;