(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Unpacking of a secret key, lazily: the proof (see unpack_sk_44_spec.ml).  *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/unpack_sk_44_spec.ml";;
needs "x86/proofs/utils/mldsa_native_hints.ml";;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: a straight line.   *)
(* The address of the secret key is loaded from its slot on the stack. The   *)
(* 128 bytes of rho, key and tr are loaded and stored as eight 128-bit       *)
(* words, and the three addresses in the secret key are stored as 64-bit     *)
(* words. The legacy SSE loads keep the upper halves of the YMM registers,   *)
(* whose initial values are ghost variables.                                 *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_UNPACK_SK_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL =
  prove
 (MLDSA_NATIVE_UNPACK_SK_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT,
  let EXEC = MLDSA_NATIVE_UNPACK_SK_44_GCC12_O2_REDUCED_RAM_EXEC in
  META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `rho:int64`; `tr:int64`; `key:int64`;
    `t0:int64`; `s1:int64`; `s2:int64`; `sk:int64`; `skb:num->byte`;
    `pc:num`; `stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES; fst EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  GHOST_INTRO_TAC `ymm0_init:int256` `read YMM0` THEN
  GHOST_INTRO_TAC `ymm1_init:int256` `read YMM1` THEN
  GHOST_INTRO_TAC `ymm2_init:int256` `read YMM2` THEN
  GHOST_INTRO_TAC `ymm3_init:int256` `read YMM3` THEN
  GHOST_INTRO_TAC `ymm4_init:int256` `read YMM4` THEN
  GHOST_INTRO_TAC `ymm5_init:int256` `read YMM5` THEN
  GHOST_INTRO_TAC `ymm6_init:int256` `read YMM6` THEN
  GHOST_INTRO_TAC `ymm7_init:int256` `read YMM7` THEN
  FULL_INIT_TAC THEN
  GLUE_SLICE_TAC
   `!j. j < 128
        ==> read(memory :> bytes8(word_add sk (word j))) s0 =
            (skb:num->byte) j` THEN
  GLUE_LOAD128_TAC `sk:int64` [0; 16; 32; 48; 64; 80; 96; 112] THEN
  X86_STEPS_TAC EXEC (1--24) THEN
  GLUE_STORE_TAC `rho:int64` THEN GLUE_STORE_TAC `key:int64` THEN
  GLUE_STORE_TAC `tr:int64` THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  W(fun (_,w) -> if is_exists w then DISCHARGE_SAFETY_PROPERTY_TAC
                 else GLUE_BYTES_FINAL_TAC));;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_UNPACK_SK_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT =
  prove
 (MLDSA_NATIVE_UNPACK_SK_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT,
  CORRECT_OF_FULL_TAC
    MLDSA_NATIVE_UNPACK_SK_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL);;

let MLDSA_NATIVE_UNPACK_SK_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE =
  prove
 (MLDSA_NATIVE_UNPACK_SK_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT,
  SAFE_OF_FULL_TAC
    MLDSA_NATIVE_UNPACK_SK_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL);;
