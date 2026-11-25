(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

needs "arm/proofs/snappy/gcc12_O2/raw_compress_spec.ml";;
needs "arm/proofs/bstep.ml";;
needs "arm/proofs/snappy/events_inset.ml";;

(*** The level 1 in w4, then the tail call (X30 is the caller's).           ***)

let SNAPPY_RC_EXEC =
  ARM_MK_EXEC_RANGES_RULE snappy_libsnappy_gcc12_O2_mc
   [layout_range "RawCompress__charp_ulong_charp_ulongp"];;

let SNAPPY_RAW_COMPRESS_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (SNAPPY_RAW_COMPRESS_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  MAP_EVERY X_GEN_TAC
   [`heap_ok:(int64#num)list->(int64->byte)->bool`;
    `heap_fp:(int64#num)list->int64->bool`;
    `heap_room:(int64#num)list->num->bool`; `stk:num`] THEN
  DISCH_THEN(fun model ->
    ASSUME_TAC model THEN
    REWRITE_TAC[C_ARGUMENTS; ALLPAIRS; ALL; PAIRWISE;
                MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
    ENSURES_INIT_TAC "s0" THEN
    ARM_BSTEP_TAC SNAPPY_RC_EXEC (1--2) THEN
    ARM_BSTEP_CONTRACT_TAC SNAPPY_RC_EXEC
      (REWRITE_RULE[ARITH_EQ]
        (SPEC `1`
          (MATCH_MP SNAPPY_RAW_COMPRESS_OPTIONS_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
                    model)))
      [`inp:byte list`; `src:int64`; `out:int64`; `lenp:int64`;
       `H:(int64#num)list`; `pc:num`; `ea:int64`; `el:num`; `ev:num`;
       `rw:num`; `read SP s`; `read X30 s`] "s3" THEN
    BSTEP_FINAL_TAC THEN ASM_REWRITE_TAC[]));;

let SNAPPY_RAW_COMPRESS_GCC12_O2_IMAGE_SUBROUTINE_SAFE = prove
 (SNAPPY_RAW_COMPRESS_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  MAP_EVERY X_GEN_TAC
   [`heap_ok:(int64#num)list->(int64->byte)->bool`;
    `heap_fp:(int64#num)list->int64->bool`;
    `heap_room:(int64#num)list->num->bool`; `stk:num`] THEN
  DISCH_THEN(fun model ->
    ASSUME_TAC model THEN
    REWRITE_TAC[C_ARGUMENTS; ALLPAIRS; ALL; PAIRWISE;
                MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
    ENSURES_INIT_TAC "s0" THEN
    ARM_BSTEP_TAC SNAPPY_RC_EXEC (1--2) THEN
    W(fun (asl,w) ->
      ARM_BSTEP_CONTRACT_TAC SNAPPY_RC_EXEC
        (REWRITE_RULE[ARITH_EQ]
          (SPECL [snappy_current_events (asl,w); `1`]
            (MATCH_MP SNAPPY_RAW_COMPRESS_OPTIONS_GCC12_O2_IMAGE_SUBROUTINE_SAFE
                      model)))
        [`inp:byte list`; `src:int64`; `out:int64`; `lenp:int64`;
         `H:(int64#num)list`; `pc:num`; `ea:int64`; `el:num`; `ev:num`;
         `rw:num`; `read SP s`; `read X30 s`] "s3") THEN
    BSTEP_FINAL_TAC THEN SNAPPY_INSET_FIRST_TAC THEN ASM_REWRITE_TAC[]));;
