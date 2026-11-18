(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The proof for mldsa_keccakf1600x4_xor_bytes (see keccakf1600x4_xor_bytes_spec.ml). *)
(* The proof is that of the same code in the gcc12_O2 image of               *)
(* mlkem-native (proofs/mlkem_native/gcc12_O2), with the names changed.      *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/gcc12_O2/keccakf1600x4_xor_bytes_spec.ml";;
needs "arm/proofs/utils/mldsa_native_full.ml";;



(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety. The four states, each a     *)
(* 1600-bit word as for mldsa_keccakf1600_xor_bytes, are consecutive in      *)
(* memory. The data for the states, which are only read, may overlap, e.g.   *)
(* all be the same.                                                          *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_KECCAKF1600X4_XOR_BYTES_GCC12_O2_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_KECCAKF1600X4_XOR_BYTES_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT,
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_KECCAKF1600_XOR_BYTES_GCC12_O2_IMAGE_SUBROUTINE_FULL
    "H_XOR_BYTES" THEN
  META_EXISTS_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              READ_MEMORY_WBYTES_1600] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  ENSURES_PRESERVED_TAC "x19_init" `X19` THEN
  ENSURES_PRESERVED_TAC "x20_init" `X20` THEN
  ENSURES_PRESERVED_TAC "x21_init" `X21` THEN
  ENSURES_PRESERVED_TAC "x22_init" `X22` THEN
  ENSURES_PRESERVED_TAC "x23_init" `X23` THEN
  ENSURES_PRESERVED_TAC "x24_init" `X24` THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC MLDSA_NATIVE_KECCAKF1600X4_XOR_BYTES_GCC12_O2_EXEC (1--13) THEN
  ARGS_32_TAC [`off:num`; `len:num`] THEN
  XOR_BYTES_X4_CS_CALL_TAC `S0:1600 word` `m0:num` 14 THEN
  ARM_STEPS_TAC MLDSA_NATIVE_KECCAKF1600X4_XOR_BYTES_GCC12_O2_EXEC
   (15--19) THEN
  ARGS_32_TAC [`off:num`; `len:num`] THEN
  XOR_BYTES_X4_CS_CALL_TAC `S1:1600 word` `m1:num` 20 THEN
  ARM_STEPS_TAC MLDSA_NATIVE_KECCAKF1600X4_XOR_BYTES_GCC12_O2_EXEC
   (21--25) THEN
  ARGS_32_TAC [`off:num`; `len:num`] THEN
  XOR_BYTES_X4_CS_CALL_TAC `S2:1600 word` `m2:num` 26 THEN
  ARM_STEPS_TAC MLDSA_NATIVE_KECCAKF1600X4_XOR_BYTES_GCC12_O2_EXEC
   (27--35) THEN
  ARGS_32_TAC [`off:num`; `len:num`] THEN
  XOR_BYTES_X4_CS_CALL_TAC `S3:1600 word` `m3:num` 36 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_KECCAKF1600X4_XOR_BYTES_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  prove
 (MLDSA_NATIVE_KECCAKF1600X4_XOR_BYTES_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  CORRECT_OF_FULL_TAC
    MLDSA_NATIVE_KECCAKF1600X4_XOR_BYTES_GCC12_O2_IMAGE_SUBROUTINE_FULL);;

let MLDSA_NATIVE_KECCAKF1600X4_XOR_BYTES_GCC12_O2_IMAGE_SUBROUTINE_SAFE = prove
 (MLDSA_NATIVE_KECCAKF1600X4_XOR_BYTES_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  SAFE_OF_FULL_TAC
    MLDSA_NATIVE_KECCAKF1600X4_XOR_BYTES_GCC12_O2_IMAGE_SUBROUTINE_FULL);;
