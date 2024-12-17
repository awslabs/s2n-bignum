(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Unit proofs for LDST.                                                     *)
(* ========================================================================= *)

loadt "arm/proofs/base.ml";;

(* ------------------------------------------------------------------------- *)
(* ld1, one register, SIMD, 64-bit, immediate offset, post-index *)
(* ld1 v0[0], [x0], #8 *)
let LD1_1_SIMD_64_IMM_POST = define_word_list "LD1_1_SIMD_64_IMM_POST"
  `[word 0x00; word 0x70; word 0xDF; word 0x0C]:byte list`;;

let LD1_1_SIMD_64_IMM_POST_EXEC = ARM_MK_EXEC_RULE LD1_1_SIMD_64_IMM_POST;;

let LD1_1_SIMD_64_IMM_POST_CORRECT = time prove
 (`!x a pc.
     ensures arm
          (\s. aligned_bytes_loaded s (word pc) LD1_1_SIMD_64_IMM_POST /\
               read PC s = word pc /\
               C_ARGUMENTS [x] s /\
               read (memory :> bytes64 x) s = a)
          (\s. read PC s = word (pc + 0x04) /\
               read Q0 s = (word_zx:int64->int128) a /\
               read X0 s = word_add x (word 8))
          (MAYCHANGE [PC; X0],, MAYCHANGE [Q0])`,
  MAP_EVERY X_GEN_TAC [`x:int64`; `a:int64`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS] THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_ACCSTEPS_TAC LD1_1_SIMD_64_IMM_POST_EXEC [] [1] THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[]
  );;

(* ------------------------------------------------------------------------- *)
(* st1, one register, SIMD, 128-bit, immediate offset, post-index *)
(* st1 v0, [x0], #16 *)
let ST1_1_SIMD_128_IMM_POST = define_word_list "ST1_1_SIMD_128_IMM_POST"
  `[word 0x00; word 0x78; word 0x9F; word 0x4C]:byte list`;;

let ST1_1_SIMD_128_IMM_POST_EXEC = ARM_MK_EXEC_RULE ST1_1_SIMD_128_IMM_POST;;

let ST1_1_SIMD_128_IMM_POST_CORRECT = time prove
 (`!x a pc.
      nonoverlapping (word pc,0x04) (x,16)
      ==>
        ensures arm
             (\s. aligned_bytes_loaded s (word pc) ST1_1_SIMD_128_IMM_POST /\
                  read PC s = word pc /\
                  C_ARGUMENTS [x] s /\
                  read Q0 s = a)
             (\s. read PC s = word (pc + 0x04) /\
                  read (memory :> bytes128 x) s = a /\
                  read X0 s = word_add x (word 16))
             (MAYCHANGE [PC; X0],,
              MAYCHANGE [memory :> bytes128 x])`,
  MAP_EVERY X_GEN_TAC [`x:int64`; `a:int128`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_ACCSTEPS_TAC ST1_1_SIMD_128_IMM_POST_EXEC [] [1] THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[]
  );;

(* ------------------------------------------------------------------------- *)
(* ld2, two register, SIMD, 128-bit, immediate offset, post-index *)
(* ld2 v0, [x0], #32 *)
let LD2_SIMD_128_IMM_POST = define_word_list "LD2_SIMD_128_IMM_POST"
  `[word 0x00; word 0x88; word 0xDF; word 0x4C]:byte list`;;

let LD2_SIMD_128_IMM_POST_EXEC = ARM_MK_EXEC_RULE LD2_SIMD_128_IMM_POST;;


let mc_length_th, decode_ths = LD2_SIMD_128_IMM_POST_EXEC;;

let LD2_SIMD_128_IMM_POST_CORRECT = time prove
 (`!x a b pc.
     ensures arm
          (\s. aligned_bytes_loaded s (word pc) LD2_SIMD_128_IMM_POST /\
               read PC s = word pc /\
               C_ARGUMENTS [x] s /\
               read (memory :> bytes128 x) s = a /\
               read (memory :> bytes128 (word_add x (word 0x80))) s = b)
          (\s. read PC s = word (pc + 0x04) /\
               read Q0 s = ((word_join:(96 word->32 word->128 word))
                             ((word_join:(64 word->32 word->96 word))
                               ((word_join:(32 word->32 word->64 word))
                                 (word_subword a (0,32)) (word_subword a (64,32)))
                                   (word_subword b (0,32))) (word_subword b (64,32))) /\
               read Q1 s = ((word_join:(96 word->32 word->128 word))
                             ((word_join:(64 word->32 word->96 word))
                               ((word_join:(32 word->32 word->64 word))
                                 (word_subword a (32,32)) (word_subword a (96,32)))
                                   (word_subword b (32,32))) (word_subword b (96,32))) /\
               read X0 s = word_add x (word 32))
          (MAYCHANGE [PC; X0],, MAYCHANGE [Q0; Q1])`,
  MAP_EVERY X_GEN_TAC [`x:int64`; `a:int128`; `b:int128`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS] THEN
  ENSURES_INIT_TAC "s0" THEN
  BIGNUM_DIGITIZE_TAC "a_" `read (memory :> bytes128 x) s0` THEN
  BIGNUM_DIGITIZE_TAC "b_" `read (memory :> bytes128 (word_add x (word 128))) s0` THEN

  ARM_ACCSTEPS_TAC LD2_SIMD_128_IMM_POST_EXEC [] [1] THEN
  ARM_VERBOSE_STEP_TAC LD2_SIMD_128_IMM_POST_EXEC "S0" THEN
  ARM_STEP_TAC LD2_SIMD_128_IMM_POST_EXEC [] "S0" THEN
  ARM_BASIC_STEP_TAC decode_ths "s0"

  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[]
  );;