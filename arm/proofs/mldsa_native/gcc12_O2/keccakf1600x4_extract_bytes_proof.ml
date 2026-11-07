(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The proof for mldsa_keccakf1600x4_extract_bytes (see keccakf1600x4_extract_bytes_spec.ml). *)
(* The proof is that of the same code in the gcc12_O2 image of               *)
(* mlkem-native (proofs/mlkem_native/gcc12_O2), with the names changed.      *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/gcc12_O2/keccakf1600x4_extract_bytes_spec.ml";;



(* ------------------------------------------------------------------------- *)
(* Correctness proof. The four states, each a 1600-bit word as for           *)
(* mldsa_keccakf1600_extract_bytes, are consecutive in memory.               *)
(* ------------------------------------------------------------------------- *)

let LOCAL_EXTRACT_BYTES_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mldsa_native_libmldsa_gcc12_O2_mc,
    MLDSA_NATIVE_KECCAKF1600X4_EXTRACT_BYTES_GCC12_O2_EXEC,
    0x0,mldsa_native_libmldsa_gcc12_O2_mc,
    MLDSA_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_O2_IMAGE_SUBROUTINE_CORRECT);;

let EXTRACT_BYTES_X4_CALL_TAC sv n =
  KECCAK_STATE_WBYTES_TAC sv THEN
  LOCAL_EXTRACT_BYTES_TAC [`read X0 s`; `read X1 s`; `off:num`; `len:num`;
                           sv; `pc:num`; `read X30 s`] n;;

let MLDSA_NATIVE_KECCAKF1600X4_EXTRACT_BYTES_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_KECCAKF1600X4_EXTRACT_BYTES_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  MAP_EVERY X_GEN_TAC
   [`a:int64`; `d0:int64`; `d1:int64`; `d2:int64`; `d3:int64`;
    `off:num`; `len:num`; `S0:1600 word`; `S1:1600 word`; `S2:1600 word`;
    `S3:1600 word`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 64 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
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
  ARM_STEPS_TAC MLDSA_NATIVE_KECCAKF1600X4_EXTRACT_BYTES_GCC12_O2_EXEC
   (1--13) THEN
  ARGS_32_TAC [`off:num`; `len:num`] THEN
  EXTRACT_BYTES_X4_CALL_TAC `S0:1600 word` 14 THEN
  ARM_STEPS_TAC MLDSA_NATIVE_KECCAKF1600X4_EXTRACT_BYTES_GCC12_O2_EXEC
   (15--19) THEN
  ARGS_32_TAC [`off:num`; `len:num`] THEN
  EXTRACT_BYTES_X4_CALL_TAC `S1:1600 word` 20 THEN
  ARM_STEPS_TAC MLDSA_NATIVE_KECCAKF1600X4_EXTRACT_BYTES_GCC12_O2_EXEC
   (21--25) THEN
  ARGS_32_TAC [`off:num`; `len:num`] THEN
  EXTRACT_BYTES_X4_CALL_TAC `S2:1600 word` 26 THEN
  ARM_STEPS_TAC MLDSA_NATIVE_KECCAKF1600X4_EXTRACT_BYTES_GCC12_O2_EXEC
   (27--35) THEN
  ARGS_32_TAC [`off:num`; `len:num`] THEN
  EXTRACT_BYTES_X4_CALL_TAC `S3:1600 word` 36 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]);;
