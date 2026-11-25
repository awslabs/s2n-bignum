(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

needs "arm/proofs/snappy/gcc12_O2/working_memory_ctor_ulong_spec.ml";;

(*** The branch to the call of std::__throw_bad_alloc tests bit 63 of      ***)
(*** RequiredSize(n), which is at most 207562: the fact ~bit 63 ... decides ***)
(*** it, so the path is not taken. The size as the argument of new is      ***)
(*** word(snappy_working_memory_size (val n)), whose val is the size.      ***)

let NOT_BIT63_SMALL = prove
 (`!x:int64. val x < 2 EXP 63 ==> ~bit 63 x`,
  SIMP_TAC[BIT_VAL; DIV_LT; ODD]);;

let SNAPPY_WORKING_MEMORY_CTOR_ULONG_GCC12_O2_IMAGE_SUBROUTINE_SAFE = prove
 (SNAPPY_WORKING_MEMORY_CTOR_ULONG_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  let exec = SNAPPY_WORKING_MEMORY_CTOR_ULONG_GCC12_O2_EXEC in
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              ALLPAIRS; ALL] THEN
  MAP_EVERY X_GEN_TAC
   [`heap_ok:(int64#num)list->(int64->byte)->bool`;
    `heap_fp:(int64#num)list->int64->bool`;
    `heap_room:(int64#num)list->num->bool`; `stk:num`] THEN
  DISCH_THEN(fun model ->
    ASSUME_TAC model THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC(SPEC `val(n:int64)` SNAPPY_WORKING_MEMORY_SIZE_BOUND) THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `val(word(snappy_working_memory_size (val(n:int64))):int64) =
                  snappy_working_memory_size (val n)` ASSUME_TAC THENL
     [REWRITE_TAC[VAL_WORD_EQ_EQ; DIMINDEX_64] THEN
      UNDISCH_TAC `snappy_working_memory_size (val(n:int64)) <= 207562` THEN
      ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `~bit 63 (word(snappy_working_memory_size (val(n:int64))):int64)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC NOT_BIT63_SMALL THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `snappy_working_memory_size (val(n:int64)) <= 207562` THEN
      ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `(heap_room:(int64#num)list->num->bool) H
        (val(word(snappy_working_memory_size (val(n:int64))):int64))`
    ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ENSURES_INIT_TAC "s0" THEN
    ELF_RELOCATED_DATA_TAC ~defs:[snappy_libsnappy_gcc12_O2_relocated]
      ~select:(elf_slots_importing ["_Znwm"]) THEN
    (* RequiredSize(n) *)
    ARM_BSTEP_TAC exec (1--7) THEN
    ARM_BSTEP_CONTRACT_TAC exec
      SNAPPY_WORKING_MEMORY_REQUIRED_SIZE_GCC12_O2_IMAGE_SUBROUTINE_SAFE
      [`read events s`; `read X0 s`; `pc:num`; `read SP s`; `read X30 s`;
       `read X19 s`; `read X20 s`; `read X29 s`] "s8" THEN
    (* the size check, and operator new through the PLT *)
    ARM_BSTEP_TAC exec (9--10) THEN
    ARM_BSTEP_PLT_HEAP_NEW_TAC exec model "p" "s15" THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ASSUME
     `val(word(snappy_working_memory_size (val(n:int64))):int64) =
      snappy_working_memory_size (val n)`]) THEN
    (* WorkingMemory(n, p) *)
    ARM_BSTEP_TAC exec (16--19) THEN
    ARM_BSTEP_CONTRACT_TAC exec
      SNAPPY_WORKING_MEMORY_CTOR_ULONG_CHARP_GCC12_O2_IMAGE_SUBROUTINE_SAFE
      [`read events s`; `read X0 s`; `read X1 s`; `read X2 s`; `pc:num`;
       `read SP s`; `read X30 s`; `read X19 s`; `read X20 s`; `read X21 s`;
       `read X29 s`] "s20" THEN
    SNAPPY_OBJECTS_EXPAND_TAC THEN
    (* owns_mem_ = true, and the return *)
    ARM_BSTEP_TAC exec (21--25) THEN
    BSTEP_FINAL_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    EXISTS_TAC `p:int64` THEN
    ASM_REWRITE_TAC[snappy_working_memory; BITVAL_CLAUSES] THEN
    REPEAT CONJ_TAC THEN
    TRY(CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
    MEMACCESS_INSET_TAC));;

let SNAPPY_WORKING_MEMORY_CTOR_ULONG_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (SNAPPY_WORKING_MEMORY_CTOR_ULONG_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  ENSURES_DROP_EVENTS_TAC SNAPPY_WORKING_MEMORY_CTOR_ULONG_GCC12_O2_IMAGE_SUBROUTINE_SAFE);;
