(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The proof for mldsa_keccakf1600x4_permute (see keccakf1600x4_permute_spec.ml). *)
(* The proof is that of the same code in the gcc12_O2 image of               *)
(* mlkem-native (proofs/mlkem_native/gcc12_O2), with the names changed.      *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/gcc12_O2/keccakf1600x4_permute_spec.ml";;
needs "arm/proofs/utils/mldsa_native_full.ml";;



(* ------------------------------------------------------------------------- *)
(* The four calls of mldsa_keccakf1600_permute, keeping the states in memory *)
(* as numbers so that they are carried through the steps.                    *)
(* ------------------------------------------------------------------------- *)

let WORDLIST_FROM_MEMORY_25 = prove
 (`!a s (l:int64 list).
        wordlist_from_memory(a,25) s = l <=>
        LENGTH l = 25 /\ read (memory :> bytes(a,200)) s = num_of_wordlist l`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC WORDLIST_FROM_MEMORY_EQ_ALT THEN
  REWRITE_TAC[DIMINDEX_64] THEN ARITH_TAC);;

let LOCAL_KECCAK_TAC =
  let tac = ARM_SUBROUTINE_SIM_TAC
   (mldsa_native_libmldsa_gcc12_O2_mc,
    MLDSA_NATIVE_KECCAKF1600X4_PERMUTE_GCC12_O2_EXEC,
    0x0,mldsa_native_libmldsa_gcc12_O2_mc,
    MLDSA_NATIVE_KECCAKF1600_PERMUTE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT) in
  fun atm n ->
    tac [`read X0 s`; atm; `pc:num`; `read SP s`; `read X30 s`] n THENL
     [REWRITE_TAC[WORDLIST_FROM_MEMORY_25] THEN ASM_REWRITE_TAC[];
      FIRST_X_ASSUM(MP_TAC o check
       (can (term_match [] `wordlist_from_memory(a,25) s:int64 list = l`) o
        concl)) THEN
      REWRITE_TAC[WORDLIST_FROM_MEMORY_25] THEN STRIP_TAC];;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_KECCAKF1600X4_PERMUTE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_KECCAKF1600X4_PERMUTE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  MAP_EVERY X_GEN_TAC
   [`a:int64`; `A1:int64 list`; `A2:int64 list`; `A3:int64 list`;
    `A4:int64 list`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 208 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  ENSURES_PRESERVED_TAC "x19_init" `X19` THEN
  REWRITE_TAC[WORDLIST_FROM_MEMORY_25] THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC MLDSA_NATIVE_KECCAKF1600X4_PERMUTE_GCC12_O2_EXEC (1--3) THEN
  LOCAL_KECCAK_TAC `A1:int64 list` 4 THEN
  ARM_STEPS_TAC MLDSA_NATIVE_KECCAKF1600X4_PERMUTE_GCC12_O2_EXEC (5--6) THEN
  LOCAL_KECCAK_TAC `A2:int64 list` 7 THEN
  ARM_STEPS_TAC MLDSA_NATIVE_KECCAKF1600X4_PERMUTE_GCC12_O2_EXEC (8--9) THEN
  LOCAL_KECCAK_TAC `A3:int64 list` 10 THEN
  ARM_STEPS_TAC MLDSA_NATIVE_KECCAKF1600X4_PERMUTE_GCC12_O2_EXEC (11--13) THEN
  LOCAL_KECCAK_TAC `A4:int64 list` 14 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety for the states as 1600-bit   *)
(* words, with the FULL theorem of mldsa_keccakf1600_permute, from which the *)
(* correctness for 1600-bit words and constant time and memory safety alone  *)
(* follow.                                                                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_KECCAKF1600X4_PERMUTE_GCC12_O2_IMAGE_SUBROUTINE_FULL_F1600 =
  prove
 (MLDSA_NATIVE_KECCAKF1600X4_PERMUTE_GCC12_O2_IMAGE_SUBROUTINE_FULL_F1600_STMT,
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_KECCAKF1600_PERMUTE_GCC12_O2_IMAGE_SUBROUTINE_FULL_F1600
    "H_KECCAK" THEN
  META_EXISTS_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; NONOVERLAPPING_CLAUSES;
              READ_MEMORY_WBYTES_1600] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  ENSURES_PRESERVED_TAC "x19_init" `X19` THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC MLDSA_NATIVE_KECCAKF1600X4_PERMUTE_GCC12_O2_EXEC (1--3) THEN
  LOCAL_KECCAK_CS_TAC `S0:1600 word` 4 THEN
  ARM_STEPS_TAC MLDSA_NATIVE_KECCAKF1600X4_PERMUTE_GCC12_O2_EXEC (5--6) THEN
  LOCAL_KECCAK_CS_TAC `S1:1600 word` 7 THEN
  ARM_STEPS_TAC MLDSA_NATIVE_KECCAKF1600X4_PERMUTE_GCC12_O2_EXEC (8--9) THEN
  LOCAL_KECCAK_CS_TAC `S2:1600 word` 10 THEN
  ARM_STEPS_TAC MLDSA_NATIVE_KECCAKF1600X4_PERMUTE_GCC12_O2_EXEC (11--13) THEN
  LOCAL_KECCAK_CS_TAC `S3:1600 word` 14 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

let MLDSA_NATIVE_KECCAKF1600X4_PERMUTE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_F1600 =
  prove
 (MLDSA_NATIVE_KECCAKF1600X4_PERMUTE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_F1600_STMT,
  CORRECT_OF_FULL_TAC
    MLDSA_NATIVE_KECCAKF1600X4_PERMUTE_GCC12_O2_IMAGE_SUBROUTINE_FULL_F1600);;

let MLDSA_NATIVE_KECCAKF1600X4_PERMUTE_GCC12_O2_IMAGE_SUBROUTINE_SAFE = prove
 (MLDSA_NATIVE_KECCAKF1600X4_PERMUTE_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  SAFE_OF_FULL_TAC
    MLDSA_NATIVE_KECCAKF1600X4_PERMUTE_GCC12_O2_IMAGE_SUBROUTINE_FULL_F1600);;
