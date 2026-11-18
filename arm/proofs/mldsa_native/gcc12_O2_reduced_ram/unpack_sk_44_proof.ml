(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Unpacking of a secret key: the proof (see unpack_sk_44_spec.ml).          *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/gcc12_O2_reduced_ram/unpack_sk_44_spec.ml";;
needs "arm/proofs/utils/mldsa_native_hints.ml";;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the 128 bytes of   *)
(* rho, key and tr as eight 128-bit words, loaded and stored, and the three  *)
(* addresses, computed and stored.                                           *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_UNPACK_SK_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_UNPACK_SK_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT,
  let EXEC = MLDSA_NATIVE_UNPACK_SK_44_GCC12_O2_REDUCED_RAM_EXEC in
  META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `rho:int64`; `tr:int64`; `key:int64`;
    `t0:int64`; `s1:int64`; `s2:int64`; `sk:int64`; `skb:num->byte`;
    `pc:num`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES; fst EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FULL_INIT_TAC THEN
  GLUE_SLICE_TAC
   `!j. j < 128
        ==> read(memory :> bytes8(word_add sk (word j))) s0 =
            (skb:num->byte) j` THEN
  GLUE_LOAD128_TAC `sk:int64` [0; 16; 32; 48; 64; 80; 96; 112] THEN
  ARM_STEPS_TAC EXEC (1--16) THEN
  GLUE_STORE_TAC `rho:int64` THEN GLUE_STORE_TAC `key:int64` THEN
  GLUE_STORE_TAC `tr:int64` THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  TRY GLUE_BYTES_FINAL_TAC THEN
  TRY(CONV_TAC WORD_RULE) THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_UNPACK_SK_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_UNPACK_SK_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT,
  CORRECT_OF_FULL_TAC
    MLDSA_NATIVE_UNPACK_SK_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL);;

let MLDSA_NATIVE_UNPACK_SK_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE = prove
 (MLDSA_NATIVE_UNPACK_SK_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT,
  SAFE_OF_FULL_TAC
    MLDSA_NATIVE_UNPACK_SK_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL);;
