(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

needs "arm/proofs/snappy/gcc12_O2/working_memory_get_hash_table_spec.ml";;

(*** m = the fragment size modulo 2^32 (the 32-bit compares). The three    ***)
(*** ranges m > 32768, m <= 255 and the rest are runs of bstep with the    ***)
(*** call of memset through the PLT; in the first two the table size is a ***)
(*** numeral, in the third the values of the clz computation are replaced ***)
(*** by word(snappy_table_size m) and word(2 * snappy_table_size m)       ***)
(*** (SNAPPY_TABLE_SIZE_CLZ, SNAPPY_TABLE_BYTES_CLZ) before the call.      ***)
(*** memset's postcondition, byte by byte, is turned into                  ***)
(*** read (memory :> bytes(t,2 * h)) s = 0 (READ_MEMORY_BYTES_EQ_0) and   ***)
(*** its events into the set form.                                         ***)

let SNAPPY_WORKING_MEMORY_GET_HASH_TABLE_GCC12_O2_IMAGE_SUBROUTINE_SAFE = prove
 (SNAPPY_WORKING_MEMORY_GET_HASH_TABLE_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  let exec = SNAPPY_WORKING_MEMORY_GET_HASH_TABLE_GCC12_O2_EXEC in
  let memset_zero =
    FIRST_X_ASSUM(fun th ->
      if is_forall(concl th) &&
         can (find_term (fun t -> match t with
                Const("bytes8",_) -> true | _ -> false)) (concl th)
      then ASSUME_TAC(MATCH_MP READ_MEMORY_BYTES_EQ_0
                        (CONV_RULE(DEPTH_CONV WORD_RED_CONV) th))
      else NO_TAC) in
  let call_memset n =
    USE_THEN "H_MEMSET" (fun th ->
      ARM_BSTEP_PLT_STUB_TAC exec THEN
      ARM_BSTEP_CONTRACT_TAC exec th
       [`read events s`; `read X0 s`; `read X1 s`; `read X2 s`; `read X30 s`]
       ("s" ^ string_of_int n)) THEN
    memset_zero THEN MEMACCESS_INBOUNDS_TO_INSET_TAC in
  let finish =
    BSTEP_FINAL_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [CONV_TAC WORD_RULE; MEMACCESS_INSET_TAC] in
  let numeral_size th =
    SUBST_ALL_TAC th THEN
    RULE_ASSUM_TAC(CONV_RULE(DEPTH_CONV NUM_MULT_CONV)) THEN
    CONV_TAC(DEPTH_CONV NUM_MULT_CONV) in
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              ALLPAIRS; ALL] THEN
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (LABEL_TAC "H_MEMSET" o REWRITE_RULE[memset_correct_safe_contract])
    STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `m = val(n:int64) MOD 2 EXP 32` THEN
  SUBGOAL_THEN `m < 2 EXP 32` ASSUME_TAC THENL
   [EXPAND_TAC "m" THEN REWRITE_TAC[MOD_LT_EQ] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN `val(word_zx (n:int64):int32) = m` ASSUME_TAC THENL
   [EXPAND_TAC "m" THEN REWRITE_TAC[VAL_WORD_ZX_GEN; DIMINDEX_32]; ALL_TAC] THEN
  CMP_HI_TAC ~rws:[ASSUME `val(word_zx (n:int64):int32) = m`]
    `word_zx (n:int64):int32` `32768` THEN
  CMP_HI_TAC ~rws:[ASSUME `val(word_zx (n:int64):int32) = m`]
    `word_zx (n:int64):int32` `255` THEN
  ENSURES_INIT_TAC "s0" THEN
  ELF_RELOCATED_DATA_TAC ~defs:[snappy_libsnappy_gcc12_O2_relocated]
    ~select:(elf_slots_importing ["memset"]) THEN
  ASM_CASES_TAC `32768 < m` THENL
   [(* 32768 entries *)
    SUBGOAL_THEN `snappy_table_size m = 32768` numeral_size THENL
     [ASM_SIMP_TAC[SNAPPY_TABLE_SIZE_MAX; ARITH_RULE `32768 < m ==> 16384 < m`];
      ALL_TAC] THEN
    ARM_BSTEP_TAC exec (1--14) THEN call_memset 19 THEN
    ARM_BSTEP_TAC exec (20--25) THEN finish;
    ALL_TAC] THEN
  ASM_CASES_TAC `255 < m` THENL
   [ALL_TAC;
    (* 256 entries *)
    SUBGOAL_THEN `snappy_table_size m = 256` numeral_size THENL
     [ASM_SIMP_TAC[SNAPPY_TABLE_SIZE_MIN; ARITH_RULE `~(255 < m) ==> m <= 256`];
      ALL_TAC] THEN
    ARM_BSTEP_TAC exec (1--16) THEN call_memset 21 THEN
    ARM_BSTEP_TAC exec (22--27) THEN finish] THEN
  (* 256 < entries <= 32768, by clz *)
  SUBGOAL_THEN `255 < m /\ m <= 32768` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`255 < m`; `~(32768 < m)`] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `val(word(2 * snappy_table_size m):int64) = 2 * snappy_table_size m`
  ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD_EQ_EQ; DIMINDEX_64] THEN
    MP_TAC(SPEC `m:num` SNAPPY_TABLE_SIZE_BOUNDS) THEN ARITH_TAC;
    ALL_TAC] THEN
  ARM_BSTEP_TAC exec (1--20) THEN
  SUBGOAL_THEN `word_zx (n:int64):int32 = word m` MP_TAC THENL
   [ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN ASM_REWRITE_TAC[VAL_WORD; DIMINDEX_32] THEN
    ASM_SIMP_TAC[MOD_LT];
    ALL_TAC] THEN
  DISCH_THEN(fun zx -> FIRST_ASSUM(fun c ->
    if concl c <> `255 < m /\ m <= 32768` then NO_TAC else
    let l1 = MP (SPEC `m:num` SNAPPY_TABLE_BYTES_CLZ) c
    and l2 = MP (SPEC `m:num` SNAPPY_TABLE_SIZE_CLZ) c in
    RULE_ASSUM_TAC(fun th -> match concl th with
        Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),r),_)),_)
          when r = `X2` -> REWRITE_RULE[zx; l1] th
      | Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),r),_)),_)
          when r = `X21` -> REWRITE_RULE[zx; l2] th
      | _ -> th))) THEN
  call_memset 25 THEN
  ARM_BSTEP_TAC exec (26--31) THEN finish);;

let SNAPPY_WORKING_MEMORY_GET_HASH_TABLE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (SNAPPY_WORKING_MEMORY_GET_HASH_TABLE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  ENSURES_DROP_EVENTS_TAC
    SNAPPY_WORKING_MEMORY_GET_HASH_TABLE_GCC12_O2_IMAGE_SUBROUTINE_SAFE);;
