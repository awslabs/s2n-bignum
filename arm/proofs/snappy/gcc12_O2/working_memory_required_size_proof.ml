(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

needs "arm/proofs/snappy/gcc12_O2/working_memory_required_size_spec.ml";;
needs "arm/proofs/heap_plt.ml";;

(*** The three ranges of n that the code distinguishes by its branches,     ***)
(*** n > 65536, 32768 < n <= 65536 and n <= 32768, and in the last one the  ***)
(*** condition n > 255 of the csel, are split by cases on the comparisons   ***)
(*** that CMP_HI_TAC relates to the conditions of the flags; each case is   ***)
(*** one run of bstep with the call of MaxCompressedLength in it, and the   ***)
(*** result is snappy_working_memory_size n in the form of                  ***)
(*** SNAPPY_WORKING_MEMORY_SIZE_CASES.                                      ***)

let SNAPPY_WORKING_MEMORY_REQUIRED_SIZE_GCC12_O2_TAC (mcl:thm) : tactic =
  let exec = SNAPPY_WORKING_MEMORY_REQUIRED_SIZE_GCC12_O2_EXEC in
  let call_mcl n =
    ARM_BSTEP_CONTRACT_TAC exec mcl
      ((if is_forall(concl mcl) &&
           name_of(fst(dest_forall(concl mcl))) = "e"
        then [`read events s`] else []) @
       [`read X0 s`; `pc:num`; `read X30 s`])
      ("s" ^ string_of_int n) in
  let result =
    TRY(ASM_SIMP_TAC[SNAPPY_TABLE_BYTES_CLZ;
                     ARITH_RULE `~(32768 < n) ==> n <= 32768`]) THEN
    REWRITE_TAC[GSYM WORD_ADD] THEN AP_TERM_TAC THEN
    ONCE_REWRITE_TAC[SNAPPY_WORKING_MEMORY_SIZE_CASES] THEN
    ASM_SIMP_TAC[SNAPPY_MAX_COMPRESSED_LENGTH_GCC12_O2_RESULT_SMALL; ARITH;
                 ARITH_RULE `~(65536 < n) ==> n < 2 EXP 32`;
                 SNAPPY_TABLE_SIZE_MIN;
                 ARITH_RULE `~(255 < n) ==> n <= 256`] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC in
  let finish =
    BSTEP_FINAL_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
    FIRST [MEMACCESS_INSET_TAC; CONV_TAC WORD_RULE; result] in
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REPEAT(W(fun (_,w) ->
    let v,_ = dest_forall w in
    if name_of v = "n" then failwith "" else GEN_TAC)) THEN
  W64_GEN_TAC `n:num` THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
  CMP_HI_TAC `word n:int64` `65536` THEN CMP_HI_TAC `word n:int64` `32768` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[VAL_WORD_EQ; DIMINDEX_64]) THEN
  ASM_CASES_TAC `65536 < n` THENL
   [ARM_BSTEP_TAC exec (1--10) THEN call_mcl 11 THEN
    ARM_BSTEP_TAC exec (12--15) THEN finish;
    ALL_TAC] THEN
  ASM_CASES_TAC `32768 < n` THENL
   [ARM_BSTEP_TAC exec (1--13) THEN call_mcl 14 THEN
    ARM_BSTEP_TAC exec (15--18) THEN finish;
    ALL_TAC] THEN
  SUBGOAL_THEN `word_zx (word n:int64):int32 = word n` ASSUME_TAC THENL
   [ASM_SIMP_TAC[word_zx; VAL_WORD_EQ; DIMINDEX_64]; ALL_TAC] THEN
  SUBGOAL_THEN `val(word n:int32) = n` ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD_EQ_EQ; DIMINDEX_32] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  CMP_HI_TAC ~rws:[ASSUME `val(word n:int32) = n`] `word n:int32` `255` THEN
  ASM_CASES_TAC `255 < n` THEN
  ARM_BSTEP_TAC exec (1--20) THEN call_mcl 21 THEN
  ARM_BSTEP_TAC exec (22--25) THEN finish;;

let SNAPPY_WORKING_MEMORY_REQUIRED_SIZE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (SNAPPY_WORKING_MEMORY_REQUIRED_SIZE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  SNAPPY_WORKING_MEMORY_REQUIRED_SIZE_GCC12_O2_TAC
    SNAPPY_MAX_COMPRESSED_LENGTH_GCC12_O2_IMAGE_SUBROUTINE_CORRECT);;

let SNAPPY_WORKING_MEMORY_REQUIRED_SIZE_GCC12_O2_IMAGE_SUBROUTINE_SAFE = prove
 (SNAPPY_WORKING_MEMORY_REQUIRED_SIZE_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  SNAPPY_WORKING_MEMORY_REQUIRED_SIZE_GCC12_O2_TAC
    SNAPPY_MAX_COMPRESSED_LENGTH_GCC12_O2_IMAGE_SUBROUTINE_SAFE);;
