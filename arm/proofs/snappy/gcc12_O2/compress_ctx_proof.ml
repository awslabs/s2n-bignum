(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

needs "arm/proofs/snappy/gcc12_O2/compress_ctx_spec.ml";;
needs "arm/proofs/bstep.ml";;
needs "arm/proofs/snappy/events_inset.ml";;

(*** ldr x3, [x3]; b InternalCompress: two steps, then the contract of    ***)
(*** InternalCompress returns to the caller's X30.                        ***)

let SNAPPY_COMPRESS_CTX_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE snappy_libsnappy_gcc12_O2_mc
   [layout_range "Compress__Sourcep_Sinkp_CompressionOptions_CompressionContextp"];;

let SNAPPY_COMPRESS_CTX_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (SNAPPY_COMPRESS_CTX_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  REWRITE_TAC[C_ARGUMENTS; ALLPAIRS; ALL; PAIRWISE] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[snappy_compression_context; snappy_working_memory] THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_BSTEP_TAC SNAPPY_COMPRESS_CTX_GCC12_O2_EXEC (1--2) THEN
  MP_TAC(SPECL [`level:num`; `inp:byte list`; `src:int64`; `out:int64`;
                `so:int64`; `sk:int64`; `wm:int64`; `mem:int64`; `nw:num`;
                `owns:bool`; `pc:num`; `imp:string->int64`; `ea:int64`;
                `el:num`; `ev:num`; `rw:num`; `stackpointer:int64`;
                `returnaddress:int64`]
    SNAPPY_INTERNAL_COMPRESS_GCC12_O2_IMAGE_SUBROUTINE_CORRECT) THEN
  REWRITE_TAC[snappy_working_memory] THEN
  ASM_REWRITE_TAC[C_ARGUMENTS; ALLPAIRS; ALL; PAIRWISE] THEN
  DISCH_THEN(fun th ->
    ARM_BSTEP_CALL_TAC SNAPPY_COMPRESS_CTX_GCC12_O2_EXEC th "s3") THEN
  BSTEP_FINAL_TAC THEN ASM_REWRITE_TAC[]);;

let SNAPPY_COMPRESS_CTX_GCC12_O2_IMAGE_SUBROUTINE_SAFE = prove
 (SNAPPY_COMPRESS_CTX_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  REWRITE_TAC[C_ARGUMENTS; ALLPAIRS; ALL; PAIRWISE] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[snappy_compression_context; snappy_working_memory] THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_BSTEP_TAC SNAPPY_COMPRESS_CTX_GCC12_O2_EXEC (1--2) THEN
  W(fun (asl,w) ->
    MP_TAC(SPECL [snappy_current_events (asl,w);
                  `level:num`; `inp:byte list`; `src:int64`; `out:int64`;
                  `so:int64`; `sk:int64`; `wm:int64`; `mem:int64`; `nw:num`;
                  `owns:bool`; `pc:num`; `imp:string->int64`; `ea:int64`;
                  `el:num`; `ev:num`; `rw:num`; `stackpointer:int64`;
                  `returnaddress:int64`]
      SNAPPY_INTERNAL_COMPRESS_GCC12_O2_IMAGE_SUBROUTINE_SAFE)) THEN
  REWRITE_TAC[snappy_working_memory] THEN
  ASM_REWRITE_TAC[C_ARGUMENTS; ALLPAIRS; ALL; PAIRWISE] THEN
  DISCH_THEN(fun th ->
    ARM_BSTEP_CALL_TAC SNAPPY_COMPRESS_CTX_GCC12_O2_EXEC th "s3") THEN
  BSTEP_FINAL_TAC THEN SNAPPY_INSET_FIRST_TAC THEN ASM_REWRITE_TAC[]);;
