(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

needs "arm/proofs/snappy/gcc12_O2/c_validate_compressed_buffer_spec.ml";;
needs "arm/proofs/heap_plt.ml";;
needs "arm/proofs/snappy/validator_tactics.ml";;

(*** The frame, the call of IsValidCompressedBuffer, the status. The cases ***)
(*** of the result are split first, so that the contract of the callee     ***)
(*** gives the result word as a plain fact that crosses the epilogue. The   ***)
(*** stack is split into the frame (16 bytes) and the callee's 544 bytes,   ***)
(*** so that the saved X29, X30 cross the call.                             ***)

let SNAPPY_C_VALIDATE_COMPRESSED_BUFFER_GCC12_O2_IMAGE_SUBROUTINE_SAFE = prove
 (SNAPPY_C_VALIDATE_COMPRESSED_BUFFER_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  let exec = SNAPPY_C_VALIDATE_COMPRESSED_BUFFER_GCC12_O2_EXEC in
  let callee =
    SNAPPY_IS_VALID_COMPRESSED_BUFFER_GCC12_O2_IMAGE_SUBROUTINE_SAFE in
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              ALL] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[snappy_validate_status] THEN
  ENSURES_FRAME_SPLIT_TAC
   `MAYCHANGE [memory :> bytes(word_sub sp (word 560),560)]`
   `MAYCHANGE [memory :> bytes(word_sub sp (word 16),16)] ,,
    MAYCHANGE [memory :> bytes(word_sub sp (word 560),544)]` THEN
  SUBGOAL_THEN `544 <= val(word_sub sp (word 16):int64)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[VAL_WORD_SUB_NOWRAP; ARITH_RULE `560 <= x ==> 16 <= x`;
                 VAL_WORD_NOWRAP; ARITH_RULE `16 < 2 EXP 64`] THEN
    ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `snappy_decode (l:byte list) = NONE` THEN
  ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_BSTEP_TAC exec (1--3) THEN
  W(fun (asl,_) ->
    let hth = snd(find (fun (_,th) ->
      (is_eq(concl th) || is_neg(concl th)) &&
      can (find_term ((=) `snappy_decode (l:byte list)`)) (concl th)) asl) in
    let cth = REWRITE_RULE[hth; BITVAL_CLAUSES] callee in
    ARM_BSTEP_CONTRACT_TAC exec cth
     [`read events s`; `read X0 s`; `read X1 s`; `l:byte list`; `pc:num`;
      `rw:num`; `read SP s`; `read X30 s`; `read X19 s`; `read X20 s`;
      `read X21 s`; `read X22 s`; `read X23 s`; `read X24 s`; `read X25 s`;
      `read X26 s`; `read X29 s`; `ea:int64`; `el:num`; `ev:num`] "s4") THEN
  ARM_BSTEP_TAC exec (5--8) THEN
  BSTEP_FINAL_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
  CONV_TAC WORD_REDUCE_CONV THEN REPEAT CONJ_TAC THEN
  TRY(CONV_TAC WORD_RULE THEN NO_TAC) THEN
  TRY(ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  MEMACCESS_INSET_TAC);;

let SNAPPY_C_VALIDATE_COMPRESSED_BUFFER_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (SNAPPY_C_VALIDATE_COMPRESSED_BUFFER_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  ENSURES_DROP_EVENTS_TAC
    SNAPPY_C_VALIDATE_COMPRESSED_BUFFER_GCC12_O2_IMAGE_SUBROUTINE_SAFE);;
