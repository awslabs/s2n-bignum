(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

needs "arm/proofs/snappy/gcc12_O2/working_memory_ctor_ulong_charp_spec.ml";;
needs "arm/proofs/heap_plt.ml";;

(*** The same ranges as RequiredSize: n > 65536, 32768 < n <= 65536, and   ***)
(*** for n <= 32768 the branch on n <= 255 (b.ls on the 32-bit compare),   ***)
(*** each one run of bstep with the call of RequiredSize, whose frame is   ***)
(*** below the 48 bytes of this one. The fields are then                    ***)
(*** snappy_working_memory_input/output by the table size of each range.   ***)

let SNAPPY_WORKING_MEMORY_CTOR_ULONG_CHARP_GCC12_O2_TAC (rs:thm) : tactic =
  let exec = SNAPPY_WORKING_MEMORY_CTOR_ULONG_CHARP_GCC12_O2_EXEC in
  let call_rs n =
    ARM_BSTEP_CONTRACT_TAC exec rs
      ((if name_of(fst(dest_forall(concl rs))) = "e"
        then [`read events s`] else []) @
       [`read X0 s`; `pc:num`; `read SP s`; `read X30 s`;
        `read X19 s`; `read X20 s`; `read X29 s`])
      ("s" ^ string_of_int n) in
  let field =
    TRY(ASM_SIMP_TAC[SNAPPY_TABLE_BYTES_CLZ;
                     ARITH_RULE `~(32768 < n) ==> n <= 32768`]) THEN
    REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN
    ASM_SIMP_TAC[ARITH_RULE `~(65536 < n) ==> MIN n 65536 = n`;
                 ARITH_RULE `65536 < n ==> MIN n 65536 = 65536`] THEN
    ASM_SIMP_TAC[SNAPPY_TABLE_SIZE_MAX; SNAPPY_TABLE_SIZE_MIN; ARITH;
                 ARITH_RULE `32768 < n ==> 16384 < n`;
                 ARITH_RULE `~(255 < n) ==> n <= 256`] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC in
  let finish =
    BSTEP_FINAL_TAC THEN
    ASM_REWRITE_TAC[snappy_working_memory_input; snappy_working_memory_output;
                    snappy_fragment_size; BITVAL_CLAUSES] THEN
    REPEAT CONJ_TAC THEN FIRST [MEMACCESS_INSET_TAC; CONV_TAC WORD_RULE; field] in
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              ALLPAIRS; ALL; snappy_working_memory] THEN
  REPEAT(W(fun (_,w) ->
    let v,_ = dest_forall w in
    if name_of v = "n" then failwith "" else GEN_TAC)) THEN
  W64_GEN_TAC `n:num` THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
  CMP_HI_TAC `word n:int64` `65536` THEN CMP_HI_TAC `word n:int64` `32768` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[VAL_WORD_EQ; DIMINDEX_64]) THEN
  ASM_CASES_TAC `65536 < n` THENL
   [ARM_BSTEP_TAC exec (1--13) THEN call_rs 14 THEN
    ARM_BSTEP_TAC exec (15--25) THEN finish;
    ALL_TAC] THEN
  ASM_CASES_TAC `32768 < n` THENL
   [ARM_BSTEP_TAC exec (1--15) THEN call_rs 16 THEN
    ARM_BSTEP_TAC exec (17--27) THEN finish;
    ALL_TAC] THEN
  SUBGOAL_THEN `word_zx (word n:int64):int32 = word n` ASSUME_TAC THENL
   [ASM_SIMP_TAC[word_zx; VAL_WORD_EQ; DIMINDEX_64]; ALL_TAC] THEN
  SUBGOAL_THEN `val(word n:int32) = n` ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD_EQ_EQ; DIMINDEX_32] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  CMP_HI_TAC ~rws:[ASSUME `val(word n:int32) = n`] `word n:int32` `255` THEN
  ASM_CASES_TAC `255 < n` THENL
   [ARM_BSTEP_TAC exec (1--21) THEN call_rs 22 THEN
    ARM_BSTEP_TAC exec (23--33) THEN finish;
    ARM_BSTEP_TAC exec (1--17) THEN call_rs 18 THEN
    ARM_BSTEP_TAC exec (19--29) THEN finish];;

let SNAPPY_WORKING_MEMORY_CTOR_ULONG_CHARP_GCC12_O2_IMAGE_SUBROUTINE_SAFE = prove
 (SNAPPY_WORKING_MEMORY_CTOR_ULONG_CHARP_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  SNAPPY_WORKING_MEMORY_CTOR_ULONG_CHARP_GCC12_O2_TAC
    SNAPPY_WORKING_MEMORY_REQUIRED_SIZE_GCC12_O2_IMAGE_SUBROUTINE_SAFE);;

let SNAPPY_WORKING_MEMORY_CTOR_ULONG_CHARP_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (SNAPPY_WORKING_MEMORY_CTOR_ULONG_CHARP_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  SNAPPY_WORKING_MEMORY_CTOR_ULONG_CHARP_GCC12_O2_TAC
    SNAPPY_WORKING_MEMORY_REQUIRED_SIZE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT);;
