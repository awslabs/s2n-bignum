(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

needs "arm/proofs/snappy/gcc12_O2/c_max_compressed_length_spec.ml";;
needs "arm/proofs/bstep.ml";;

(*** The tail call: one step to MaxCompressedLength, whose contract then  ***)
(*** returns to the caller's X30 with the result. ARM_BSTEP_CALL_TAC      ***)
(*** absorbs the frame of the contract into that of the step, both the    ***)
(*** frame of the ABI by name.                                            ***)

let SNAPPY_C_MAX_COMPRESSED_LENGTH_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (SNAPPY_C_MAX_COMPRESSED_LENGTH_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  REWRITE_TAC[C_ARGUMENTS; C_RETURN] THEN
  MAP_EVERY X_GEN_TAC [`n:int64`; `pc:num`; `returnaddress:int64`] THEN
  STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
  ARM_BSTEP_TAC SNAPPY_C_MAX_COMPRESSED_LENGTH_GCC12_O2_EXEC (1--1) THEN
  MP_TAC(SPECL [`n:int64`; `pc:num`; `returnaddress:int64`]
    SNAPPY_MAX_COMPRESSED_LENGTH_GCC12_O2_IMAGE_SUBROUTINE_CORRECT) THEN
  ASM_REWRITE_TAC[C_ARGUMENTS; C_RETURN] THEN
  DISCH_THEN(fun th ->
    ARM_BSTEP_CALL_TAC SNAPPY_C_MAX_COMPRESSED_LENGTH_GCC12_O2_EXEC th "s2") THEN
  BSTEP_FINAL_TAC THEN ASM_REWRITE_TAC[]);;

needs "arm/proofs/snappy/events_inset.ml";;

let SNAPPY_C_MAX_COMPRESSED_LENGTH_GCC12_O2_IMAGE_SUBROUTINE_SAFE = prove
 (SNAPPY_C_MAX_COMPRESSED_LENGTH_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  REWRITE_TAC[C_ARGUMENTS; C_RETURN] THEN
  MAP_EVERY X_GEN_TAC [`e:uarch_event list`; `n:int64`; `pc:num`;
                       `returnaddress:int64`] THEN
  STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
  ARM_BSTEP_TAC SNAPPY_C_MAX_COMPRESSED_LENGTH_GCC12_O2_EXEC (1--1) THEN
  W(fun (asl,w) ->
    MP_TAC(SPECL [snappy_current_events (asl,w); `n:int64`; `pc:num`;
                  `returnaddress:int64`]
      SNAPPY_MAX_COMPRESSED_LENGTH_GCC12_O2_IMAGE_SUBROUTINE_SAFE)) THEN
  ASM_REWRITE_TAC[C_ARGUMENTS; C_RETURN] THEN
  DISCH_THEN(fun th ->
    ARM_BSTEP_CALL_TAC SNAPPY_C_MAX_COMPRESSED_LENGTH_GCC12_O2_EXEC th "s2") THEN
  BSTEP_FINAL_TAC THEN SNAPPY_INSET_FIRST_TAC THEN ASM_REWRITE_TAC[]);;
