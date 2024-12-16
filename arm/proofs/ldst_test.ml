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
 (`!arbitrary x a pc.
      True
      ==>
        ensures arm
             (\s. aligned_bytes_loaded s (word pc) LD1_1_SIMD_64_IMM_POST /\
                  read PC s = word pc /\
                  C_ARGUMENTS [arbitrary; x] s /\
                  read (memory :> bytes(x, 8)) s = val a)
             (\s. read PC s = word (pc + 0x04) /\
                  read (DREG' (word 0:5 word)) s = a)
             (MAYCHANGE [PC; D0])`,
  MAP_EVERY X_GEN_TAC
   [`arbitrary:int64`; `x:int64`; `a:int64`; `pc:num`] THEN
   (* - : goalstack = 1 subgoal (1 total)

   `True
    ==> ensures arm
        (\s.
             aligned_bytes_loaded s (word pc) LD1_1_SIMD_64_IMM_POST /\
             read PC s = word pc /\
             C_ARGUMENTS [arbitrary; x] s /\
             read (memory :> bytes (x,8)) s = val a)
        (\s. read PC s = word (pc + 4) /\ read (DREG' (word 0)) s = a)
        (MAYCHANGE [PC; D0])` *)
  REWRITE_TAC[C_ARGUMENTS] THEN
  (* - : goalstack = 1 subgoal (1 total)

`True
 ==> ensures arm
     (\s.
          aligned_bytes_loaded s (word pc) LD1_1_SIMD_64_IMM_POST /\
          read PC s = word pc /\
          (read X0 s = arbitrary /\ read X1 s = x) /\
          read (memory :> bytes (x,8)) s = val a)
     (\s. read PC s = word (pc + 4) /\ read (DREG' (word 0)) s = a)
     (MAYCHANGE [PC; D0])` *)
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  (* - : goalstack = 1 subgoal (1 total)

  0 [`True`]

`ensures arm
 (\s.
      aligned_bytes_loaded s (word pc) LD1_1_SIMD_64_IMM_POST /\
      read PC s = word pc /\
      (read X0 s = arbitrary /\ read X1 s = x) /\
      read (memory :> bytes (x,8)) s = val a)
 (\s. read PC s = word (pc + 4) /\ read (DREG' (word 0)) s = a)
 (MAYCHANGE [PC; D0])` *)
  ENSURES_INIT_TAC "s0" THEN
(* - : goalstack = 1 subgoal (1 total)

  0 [`True`]
  1 [`aligned_bytes_loaded s0 (word pc) LD1_1_SIMD_64_IMM_POST`]
  2 [`read PC s0 = word pc`]
  3 [`read X0 s0 = arbitrary`]
  4 [`read X1 s0 = x`]
  5 [`read (memory :> bytes (x,8)) s0 = val a`]
  6 [`(MAYCHANGE:((armstate,?269923)component)list->armstate->armstate->bool)
      []
      s0
      s0`]

`eventually arm
 (\s'.
      (read PC s' = word (pc + 4) /\ read (DREG' (word 0)) s' = a) /\
      MAYCHANGE [PC; D0] s0 s')
 s0` *)
  ARM_SIM_TAC LD1_1_SIMD_64_IMM_POST_EXEC (1--1) THEN 
  (* Exception: Failure "REWRITES_CONV". *)
  );;