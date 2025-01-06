(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Unit proofs for LDST.                                                     *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* ld1, one register, SIMD, 64-bit, immediate offset, post-index *)
(* ld1 v0[0].2D, [x0], #8 *)
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
(* ld2 v0.4s, v1.4s, [x0], #32 *)
let LD2_SIMD_128_IMM_POST = define_word_list "LD2_SIMD_128_IMM_POST"
  `[word 0x00; word 0x88; word 0xDF; word 0x4C]:byte list`;;

let LD2_SIMD_128_IMM_POST_EXEC = ARM_MK_EXEC_RULE LD2_SIMD_128_IMM_POST;;

(* Use wbytes because the definition of LD2 uses wbytes. 
   This helps symbolic execution. *)
let LD2_SIMD_128_IMM_POST_CORRECT = time prove
 (`!x a pc.
     ensures arm
          (\s. aligned_bytes_loaded s (word pc) LD2_SIMD_128_IMM_POST /\
               read PC s = word pc /\
               C_ARGUMENTS [x] s /\
               read (memory :> wbytes x) s = a)
          (\s. read PC s = word (pc + 0x04) /\
               read Q0 s = ((word_join:(96 word->32 word->128 word))
                             ((word_join:(64 word->32 word->96 word))
                               ((word_join:(32 word->32 word->64 word))
                                 ((word_subword:(256 word->(num#num)->32 word)) a (192,32)) 
                                 ((word_subword:(256 word->(num#num)->32 word)) a (128,32)))
                                   ((word_subword:(256 word->(num#num)->32 word)) a (64,32))) 
                                     ((word_subword:(256 word->(num#num)->32 word)) a (0,32))) /\
               read Q1 s = ((word_join:(96 word->32 word->128 word))
                             ((word_join:(64 word->32 word->96 word))
                               ((word_join:(32 word->32 word->64 word))
                                 ((word_subword:(256 word->(num#num)->32 word)) a (224,32)) 
                                 ((word_subword:(256 word->(num#num)->32 word)) a (160,32)))
                                   ((word_subword:(256 word->(num#num)->32 word)) a (96,32)))
                                     ((word_subword:(256 word->(num#num)->32 word)) a (32,32))) /\
               read X0 s = word_add x (word 32))
          (MAYCHANGE [PC; X0],, MAYCHANGE [Q0; Q1])`,
  MAP_EVERY X_GEN_TAC [`x:int64`; `a:(256 word)`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS] THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_ACCSTEPS_TAC LD2_SIMD_128_IMM_POST_EXEC [] [1] THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[] THEN
  BITBLAST_TAC
  );;

(* ------------------------------------------------------------------------- *)
(* st2, two register, SIMD, 64-bit, immediate offset, post-index *)
(* st2 v0.4HB, v1.4H, [x0], #16 *)
let ST2_SIMD_64_IMM_POST = define_word_list "ST2_SIMD_64_IMM_POST"
  `[word 0x00; word 0x84; word 0x9F; word 0x0C]:byte list`;;

let ST2_SIMD_64_IMM_POST_EXEC = ARM_MK_EXEC_RULE ST2_SIMD_64_IMM_POST;;

(* Use wbytes because the definition of ST2 uses wbytes. 
   This helps symbolic execution. *)
let ST2_SIMD_64_IMM_POST_CORRECT = time prove
(`!x a b pc.
  nonoverlapping (word pc,0x04) (x,16)
  ==>
    ensures arm
      (\s. aligned_bytes_loaded s (word pc) ST2_SIMD_64_IMM_POST /\
           read PC s = word pc /\
           C_ARGUMENTS [x] s /\
           word_subword (read Q0 s) (0, 64) = a /\
           word_subword (read Q1 s) (0, 64) = b )
      (\s. read PC s = word (pc + 0x04) /\
           read (memory :> bytes128 x) s = 
             ((word_join:(16 word->112 word->128 word)) 
               ((word_subword:(64 word->(num#num)->16 word)) b (48, 16))
               ((word_join:(16 word->96 word->112 word))
                ((word_subword:(64 word->(num#num)->16 word)) a (48, 16))
                ((word_join:(16 word->80 word->96 word))
                 ((word_subword:(64 word->(num#num)->16 word)) b (32, 16))
                   ((word_join:(16 word->64 word->80 word))
                    ((word_subword:(64 word->(num#num)->16 word)) a (32, 16))
                     ((word_join:(16 word->48 word->64 word))
                      ((word_subword:(64 word->(num#num)->16 word)) b (16, 16))
                       ((word_join:(16 word->32 word->48 word))
                        ((word_subword:(64 word->(num#num)->16 word)) a (16, 16))
                         ((word_join:(16 word->16 word->32 word))
                          ((word_subword:(64 word->(num#num)->16 word)) b (0, 16)) 
                          ((word_subword:(64 word->(num#num)->16 word)) a (0, 16))))))))) /\
           read X0 s = word_add x (word 16))
      (MAYCHANGE [PC; X0],, 
       MAYCHANGE [memory :> bytes128 x])`,
  MAP_EVERY X_GEN_TAC [`x:int64`; `a:int64`; `b:int64`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_ACCSTEPS_TAC ST2_SIMD_64_IMM_POST_EXEC [] [1] THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[] THEN
  BITBLAST_TAC
  );;
