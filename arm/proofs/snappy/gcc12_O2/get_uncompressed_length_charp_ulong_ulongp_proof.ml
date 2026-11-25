(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

needs "arm/proofs/snappy/gcc12_O2/get_uncompressed_length_charp_ulong_ulongp_spec.ml";;
needs "arm/proofs/heap_plt.ml";;
needs "arm/proofs/snappy/decompressor_objects.ml";;

(*** One case per input length L = 0, 1, 2, 3, 4 and L >= 5. In each, the  ***)
(*** comparisons of the address of the next byte with start + n are facts  ***)
(*** that decide those branches, and the bytes 0 .. min(L,5)-1 are facts   ***)
(*** EL k l; the branches on the bytes are split (ARM_BSTEP_RUN_TAC). At    ***)
(*** each return the header is SNAPPY_HEADER_BYTES, the tests of the bytes  ***)
(*** are rewritten into val (EL k l) < 128 (or < 16 for the 5th), and the   ***)
(*** value stored is the header by SNAPPY_HEADER_WORD_TAC.                  ***)

let SNAPPY_GET_UNCOMPRESSED_LENGTH_CHARP_ULONG_ULONGP_GCC12_O2_IMAGE_SUBROUTINE_SAFE = prove
 (SNAPPY_GET_UNCOMPRESSED_LENGTH_CHARP_ULONG_ULONGP_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  let exec = SNAPPY_GET_UNCOMPRESSED_LENGTH_CHARP_ULONG_ULONGP_GCC12_O2_EXEC in
  let cmp_byte k =
    GEN `b:byte` (CONV_RULE NUM_REDUCE_CONV
      (MP (SPECL [`b:byte`; mk_small_numeral k] CMP_HI_WORD_ZX_BYTE)
          (EQT_ELIM(NUM_REDUCE_CONV
            (mk_comb(mk_comb(`(<):num->num->bool`,mk_small_numeral k),
                     `256`)))))) in
  let byte_rules = [BIT7_WORD_ZX_BYTE; cmp_byte 127; cmp_byte 15] in
  let fact_tac tm =
    SUBGOAL_THEN tm ASSUME_TAC THENL
     [ASM_REWRITE_TAC[VAL_WORD_SUB_CASES] THEN TRY COND_CASES_TAC THEN
      ASM_ARITH_TAC;
      ALL_TAC] in
  let add_tac tm =
    SUBGOAL_THEN tm ASSUME_TAC THENL
     [REWRITE_TAC[VAL_WORD_ADD; DIMINDEX_64; VAL_WORD] THEN
      CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC;
      ALL_TAC] in
  let leaf big =
    BSTEP_FINAL_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE byte_rules) THEN
    REWRITE_TAC[SNAPPY_HEADER_BYTES] THEN
    ASM_REWRITE_TAC[option_DISTINCT; option_INJ; FORALL_UNWIND_THM1;
                    FORALL_UNWIND_THM2; BITVAL_CLAUSES] THEN
    REPEAT CONJ_TAC THEN
    TRY(CONV_TAC WORD_REDUCE_CONV THEN NO_TAC) THEN
    TRY(SNAPPY_HEADER_WORD_TAC THEN NO_TAC) THEN
    (if big then
       MATCH_MP_TAC MEMACCESS_INSET_EXISTS_MONO THEN
       EXISTS_TAC `memrange(inp:int64,5)` THEN CONJ_TAC THENL
        [MATCH_MP_TAC MEMRANGE_PREFIX_SUBSET THEN ASM_REWRITE_TAC[];
         MEMACCESS_INSET_TAC]
     else MEMACCESS_INSET_TAC) in
  let case_tac lk =
    let big = (lk = None) in
    let len = match lk with Some k -> k | None -> 5 in
    let kmax = min len 4 in
    let ks = if kmax = 0 then [] else 1--kmax in
    let num k = mk_small_numeral k in
    MAP_EVERY (fun k -> add_tac
      (subst [num k,`k:num`] `val(word_add inp (word k):int64) = val inp + k`))
     ks THEN
    add_tac `val(word_add inp n:int64) = val inp + LENGTH(l:byte list)` THEN
    fact_tac (if len = 0 then `val(word_add inp n:int64) <= val inp`
              else `~(val(word_add inp n:int64) <= val inp)`) THEN
    MAP_EVERY (fun k ->
      fact_tac (subst [num k,`k:num`]
        `val(word_add inp (word k):int64) <= val(word_add inp n:int64)`) THEN
      fact_tac (subst [num k,`k:num`]
        (if k = len
         then `val(word_sub (word_add inp n) (word_add inp (word k)):int64) = 0`
         else `~(val(word_sub (word_add inp n) (word_add inp (word k)):int64) = 0)`)))
     ks THEN
    ENSURES_INIT_TAC "s0" THEN
    MAP_EVERY (fun k -> FIRST_ASSUM(fun th ->
      if can (term_match [] `read (memory :> bytelist(a,LENGTH l)) s = l`)
             (concl th)
      then MP_TAC(MATCH_MP READ_MEMORY_BYTELIST_EL
             (CONJ th (let hyp = if big then `5 <= LENGTH(l:byte list)`
                         else subst [num len,`k:num`] `LENGTH(l:byte list) = k` in
                       MP (ARITH_RULE(mk_imp(hyp,subst [num k,`k:num`]
                             `k < LENGTH(l:byte list)`))) (ASSUME hyp))))
      else NO_TAC) THEN
      REWRITE_TAC[WORD_ADD_0] THEN DISCH_TAC)
     (if len = 0 then [] else 0--(len-1)) THEN
    ARM_BSTEP_RUN_TAC exec 1 (leaf big) in
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN
  ASM_CASES_TAC `LENGTH(l:byte list) = 0` THENL [case_tac (Some 0); ALL_TAC] THEN
  ASM_CASES_TAC `LENGTH(l:byte list) = 1` THENL [case_tac (Some 1); ALL_TAC] THEN
  ASM_CASES_TAC `LENGTH(l:byte list) = 2` THENL [case_tac (Some 2); ALL_TAC] THEN
  ASM_CASES_TAC `LENGTH(l:byte list) = 3` THENL [case_tac (Some 3); ALL_TAC] THEN
  ASM_CASES_TAC `LENGTH(l:byte list) = 4` THENL [case_tac (Some 4); ALL_TAC] THEN
  SUBGOAL_THEN `5 <= LENGTH(l:byte list)` ASSUME_TAC THENL
   [ASM_ARITH_TAC; case_tac None]);;

let SNAPPY_GET_UNCOMPRESSED_LENGTH_CHARP_ULONG_ULONGP_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (SNAPPY_GET_UNCOMPRESSED_LENGTH_CHARP_ULONG_ULONGP_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  ENSURES_DROP_EVENTS_TAC
    SNAPPY_GET_UNCOMPRESSED_LENGTH_CHARP_ULONG_ULONGP_GCC12_O2_IMAGE_SUBROUTINE_SAFE);;
