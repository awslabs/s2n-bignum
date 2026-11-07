(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The proof for mldsa_shake256x4_release (see shake256x4_release_spec.ml):  *)
(* that of mldsa_shake128x4_release (see shake128x4_release_proof.ml),       *)
(* itself that of the same code in mlkem-native, with the rate 136 of        *)
(* SHAKE256 for the rate 168 of SHAKE128: the code differs only in that      *)
(* constant.                                                                 *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/gcc12_O2/shake256x4_release_spec.ml";;



(* ------------------------------------------------------------------------- *)
(* Correctness proof, assuming the contract for memset at the address mf in  *)
(* the GOT entry, with its code and data in the region (ea,el), which must   *)
(* not overlap the context or the stack.                                     *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SHAKE256X4_RELEASE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_SHAKE256X4_RELEASE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  MAP_EVERY X_GEN_TAC
   [`st:int64`; `mf:int64`; `ea:int64`; `el:num`; `ev:num`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 16 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (LABEL_TAC "H_MEMSET" o REWRITE_RULE[memset_contract])
   (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_memset:num`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`;
                                     `got_memset:num`] WORD_ADD]) THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  ENSURES_PRESERVED_TAC "x19_init" `X19` THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC MLDSA_NATIVE_SHAKE256X4_RELEASE_GCC12_O2_EXEC (1--5) THEN
  LIBC_PLT_TAC MLDSA_NATIVE_SHAKE256X4_RELEASE_GCC12_O2_EXEC 5 THEN
  LIBC_CALL_TAC "H_MEMSET" MLDSA_NATIVE_SHAKE256X4_RELEASE_GCC12_O2_EXEC
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X30 s`] 10 THEN
  ARM_STEPS_TAC MLDSA_NATIVE_SHAKE256X4_RELEASE_GCC12_O2_EXEC (11--12) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MEMSET_ZERO_BYTES THEN ASM_REWRITE_TAC[]);;
