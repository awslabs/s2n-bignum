(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

needs "arm/proofs/mlkem_native/gcc12_O3/sha3_512_spec.ml";;


let MLKEM_NATIVE_SHA3_512_GCC12_O3_IMAGE_SUBROUTINE_FULL = prove
 (MLKEM_NATIVE_SHA3_512_GCC12_O3_IMAGE_SUBROUTINE_FULL_STMT,
  S512_INTRO_TAC THEN
  ENSURES_EVENTS_SEQUENCE_TAC `pc + mlkem_sha3_512_join3` S512_MID3 THEN
  CONJ_TAC THENL
   [ENSURES_EVENTS_SEQUENCE_TAC `pc + mlkem_sha3_512_loop1_exit` S512_MID1 THEN
    CONJ_TAC THENL
     [ASM_CASES_TAC `inlen < 72` THEN ASM_REWRITE_TAC[] THENL
       [S512_SHORT_TAC; S512_LOOP_TAC];
      ASM_CASES_TAC `inlen < 72` THEN ASM_REWRITE_TAC[] THEN
      S512_TAIL_TAC];
    S512_FINAL_TAC]);;

let MLKEM_NATIVE_SHA3_512_GCC12_O3_IMAGE_SUBROUTINE_CORRECT = prove
 (MLKEM_NATIVE_SHA3_512_GCC12_O3_IMAGE_SUBROUTINE_CORRECT_STMT,
  REPEAT STRIP_TAC THEN
  X_CHOOSE_TAC
   `f:int64->int64->num->int64->num->int64->int64->(uarch_event)list`
   MLKEM_NATIVE_SHA3_512_GCC12_O3_IMAGE_SUBROUTINE_FULL THEN
  GHOST_INTRO_TAC `e:(uarch_event)list` `read events` THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`e:(uarch_event)list`; `out:int64`; `m:int64`; `inp:byte list`;
    `LENGTH(inp:byte list)`; `guard:int64`; `pc:num`; `stackpointer:int64`;
    `returnaddress:int64`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MATCH_MP_TAC o MATCH_MP ENSURES_PREPOST_WEAKEN) THEN
  SIMP_TAC[]);;

let MLKEM_NATIVE_SHA3_512_GCC12_O3_IMAGE_SUBROUTINE_SAFE = prove
 (MLKEM_NATIVE_SHA3_512_GCC12_O3_IMAGE_SUBROUTINE_SAFE_STMT,
  MP_TAC MLKEM_NATIVE_SHA3_512_GCC12_O3_IMAGE_SUBROUTINE_FULL THEN
  MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN DISCH_TAC THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  GHOST_INTRO_TAC `inp:byte list`
   `read (memory :> bytelist(m,inlen)):armstate->byte list` THEN
  REWRITE_TAC[READ_BYTELIST_EQ_BYTES] THEN
  ASM_CASES_TAC `LENGTH(inp:byte list) = inlen` THEN ASM_REWRITE_TAC[] THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL
     [`e:(uarch_event)list`; `out:int64`; `m:int64`; `inp:byte list`;
      `inlen:num`; `guard:int64`; `pc:num`; `stackpointer:int64`;
      `returnaddress:int64`]) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MATCH_MP_TAC o MATCH_MP ENSURES_PREPOST_WEAKEN) THEN
    SIMP_TAC[];
    REWRITE_TAC[ensures]]);;
