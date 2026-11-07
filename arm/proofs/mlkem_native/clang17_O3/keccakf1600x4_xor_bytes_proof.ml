(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

needs "arm/proofs/mlkem_native/clang17_O3/keccakf1600x4_xor_bytes_spec.ml";;


let MLKEM_NATIVE_KECCAKF1600X4_XOR_BYTES_CLANG17_O3_IMAGE_SUBROUTINE_FULL = prove
 (MLKEM_NATIVE_KECCAKF1600X4_XOR_BYTES_CLANG17_O3_IMAGE_SUBROUTINE_FULL_STMT,
  XOR4_MAIN_TAC);;

let MLKEM_NATIVE_KECCAKF1600X4_XOR_BYTES_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT = prove
 (MLKEM_NATIVE_KECCAKF1600X4_XOR_BYTES_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT_STMT,
  REPEAT STRIP_TAC THEN
  X_CHOOSE_TAC
   `f:int64->int64->int64->int64->int64->num->num->num->int64->
      (uarch_event)list`
   MLKEM_NATIVE_KECCAKF1600X4_XOR_BYTES_CLANG17_O3_IMAGE_SUBROUTINE_FULL THEN
  GHOST_INTRO_TAC `e:(uarch_event)list` `read events` THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`e:(uarch_event)list`; `a:int64`; `d0:int64`; `d1:int64`; `d2:int64`;
    `d3:int64`; `off:num`; `len:num`; `S0:1600 word`; `S1:1600 word`;
    `S2:1600 word`; `S3:1600 word`; `m0:num`; `m1:num`; `m2:num`; `m3:num`;
    `pc:num`; `returnaddress:int64`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MATCH_MP_TAC o MATCH_MP ENSURES_PREPOST_WEAKEN) THEN
  SIMP_TAC[]);;

let MLKEM_NATIVE_KECCAKF1600X4_XOR_BYTES_CLANG17_O3_IMAGE_SUBROUTINE_SAFE = prove
 (MLKEM_NATIVE_KECCAKF1600X4_XOR_BYTES_CLANG17_O3_IMAGE_SUBROUTINE_SAFE_STMT,
  MP_TAC
   MLKEM_NATIVE_KECCAKF1600X4_XOR_BYTES_CLANG17_O3_IMAGE_SUBROUTINE_FULL THEN
  MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN DISCH_TAC THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MAP_EVERY (fun (v,t) -> GHOST_INTRO_TAC v t)
   [`S0:1600 word`,`read (memory :> wbytes a):armstate->1600 word`;
    `S1:1600 word`,
    `read (memory :> wbytes (word_add a (word 200))):armstate->1600 word`;
    `S2:1600 word`,
    `read (memory :> wbytes (word_add a (word 400))):armstate->1600 word`;
    `S3:1600 word`,
    `read (memory :> wbytes (word_add a (word 600))):armstate->1600 word`;
    `m0:num`,`read (memory :> bytes(d0,len))`;
    `m1:num`,`read (memory :> bytes(d1,len))`;
    `m2:num`,`read (memory :> bytes(d2,len))`;
    `m3:num`,`read (memory :> bytes(d3,len))`] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`e:(uarch_event)list`; `a:int64`; `d0:int64`; `d1:int64`; `d2:int64`;
    `d3:int64`; `off:num`; `len:num`; `S0:1600 word`; `S1:1600 word`;
    `S2:1600 word`; `S3:1600 word`; `m0:num`; `m1:num`; `m2:num`; `m3:num`;
    `pc:num`; `returnaddress:int64`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MATCH_MP_TAC o MATCH_MP ENSURES_PREPOST_WEAKEN) THEN
  SIMP_TAC[]);;
