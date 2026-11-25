(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

needs "arm/proofs/snappy/gcc12_O2/c_uncompressed_length_spec.ml";;
needs "arm/proofs/heap_plt.ml";;

(*** The frame, the call of GetUncompressedLength, the status. The cases   ***)
(*** of the header are split first, so that the contract of the callee     ***)
(*** gives the result word as a plain fact that crosses the epilogue.      ***)

let SNAPPY_C_UNCOMPRESSED_LENGTH_GCC12_O2_IMAGE_SUBROUTINE_SAFE = prove
 (SNAPPY_C_UNCOMPRESSED_LENGTH_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  let exec = SNAPPY_C_UNCOMPRESSED_LENGTH_GCC12_O2_EXEC in
  let callee = SNAPPY_GET_UNCOMPRESSED_LENGTH_CHARP_ULONG_ULONGP_GCC12_O2_IMAGE_SUBROUTINE_SAFE in
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              ALL] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[snappy_uncompressed_length_status] THEN
  MP_TAC(ISPEC `snappy_header (l:byte list)` (cases "option")) THEN
  DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC (X_CHOOSE_TAC `m:num`)) THEN
  ASM_REWRITE_TAC[option_DISTINCT; option_INJ; FORALL_UNWIND_THM1;
                  FORALL_UNWIND_THM2; BITVAL_CLAUSES] THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_BSTEP_TAC exec (1--3) THEN
  FIRST_ASSUM(fun hth ->
    if not(is_eq(concl hth)) ||
       lhand(concl hth) <> `snappy_header (l:byte list)` then NO_TAC else
    let cth = GENL [`e:(uarch_event)list`; `inp:int64`; `n:int64`; `res:int64`]
      (REWRITE_RULE[hth; option_DISTINCT; option_INJ; FORALL_UNWIND_THM1;
                    FORALL_UNWIND_THM2; BITVAL_CLAUSES]
        (SPECL [`e:(uarch_event)list`; `inp:int64`; `n:int64`; `res:int64`;
                `l:byte list`] callee)) in
    ARM_BSTEP_CONTRACT_TAC exec cth
     [`read events s`; `read X0 s`; `read X1 s`; `read X2 s`;
      `r0:int64`; `pc:num`; `read X30 s`] "s4") THEN
  ARM_BSTEP_TAC exec (5--8) THEN
  BSTEP_FINAL_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC WORD_REDUCE_CONV THEN REPEAT CONJ_TAC THEN
  TRY(CONV_TAC WORD_RULE THEN NO_TAC) THEN
  TRY(ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  MEMACCESS_INSET_TAC);;

let SNAPPY_C_UNCOMPRESSED_LENGTH_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (SNAPPY_C_UNCOMPRESSED_LENGTH_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  ENSURES_DROP_EVENTS_TAC SNAPPY_C_UNCOMPRESSED_LENGTH_GCC12_O2_IMAGE_SUBROUTINE_SAFE);;
