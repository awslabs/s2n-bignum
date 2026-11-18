(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Keccak-f1600 permutation of four consecutive states: the proof (see       *)
(* keccakf1600x4_permute_spec.ml).                                           *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/gcc12_O2/keccakf1600x4_permute_spec.ml";;
needs "x86/proofs/utils/mldsa_native_full.ml";;

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
  let tac = X86_SUBROUTINE_SIM_TAC
   (mldsa_native_libmldsa_gcc12_O2_mc,
    MLDSA_NATIVE_KECCAKF1600X4_PERMUTE_GCC12_O2_EXEC,
    0x0,mldsa_native_libmldsa_gcc12_O2_mc,
    MLDSA_NATIVE_KECCAKF1600_PERMUTE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT) in
  fun atm n ->
    tac [`read RDI s`; atm; `pc:num`; `read RSP s`;
         `read (memory :> bytes64 (read RSP s)) s`] n THENL
     [REWRITE_TAC[WORDLIST_FROM_MEMORY_25] THEN ASM_REWRITE_TAC[];
      FIRST_X_ASSUM(MP_TAC o check
       (can (term_match [] `wordlist_from_memory(a,25) s:int64 list = l`) o
        concl)) THEN
      REWRITE_TAC[WORDLIST_FROM_MEMORY_25] THEN STRIP_TAC];;

(* ------------------------------------------------------------------------- *)
(* Correctness, with the correctness theorem of mldsa_keccakf1600_permute.   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_KECCAKF1600X4_PERMUTE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_KECCAKF1600X4_PERMUTE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_PRESERVED_TAC "rbx_init" `RBX` THEN
  REWRITE_TAC[WORDLIST_FROM_MEMORY_25] THEN
  ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC MLDSA_NATIVE_KECCAKF1600X4_PERMUTE_GCC12_O2_EXEC (1--3) THEN
  LOCAL_KECCAK_TAC `A1:int64 list` 4 THEN
  X86_STEPS_TAC MLDSA_NATIVE_KECCAKF1600X4_PERMUTE_GCC12_O2_EXEC (5--6) THEN
  LOCAL_KECCAK_TAC `A2:int64 list` 7 THEN
  X86_STEPS_TAC MLDSA_NATIVE_KECCAKF1600X4_PERMUTE_GCC12_O2_EXEC (8--9) THEN
  LOCAL_KECCAK_TAC `A3:int64 list` 10 THEN
  X86_STEPS_TAC MLDSA_NATIVE_KECCAKF1600X4_PERMUTE_GCC12_O2_EXEC (11--13) THEN
  LOCAL_KECCAK_TAC `A4:int64 list` 14 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety for the states as 1600-bit   *)
(* words, with the FULL theorem of mldsa_keccakf1600_permute, from which the *)
(* correctness for 1600-bit words and constant time and memory safety alone  *)
(* follow. Each state is restated in the wbytes form for its call, and the   *)
(* result back as 200 bytes.                                                 *)
(* ------------------------------------------------------------------------- *)

let LOCAL_KECCAK_CS_TAC sv n =
  KECCAK_STATE_WBYTES_TAC sv THEN
  FULL_CALL_TAC mldsa_native_libmldsa_gcc12_O2_mc
   MLDSA_NATIVE_KECCAKF1600X4_PERMUTE_GCC12_O2_EXEC "H_KECCAK"
   [`read RDI s`; sv; `pc:num`; `read RSP s`;
    `read (memory :> bytes64 (read RSP s)) s`]
   [`pc:num`; `a:int64`; `stackpointer:int64`; `returnaddress:int64`] n THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]);;

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
  ENSURES_PRESERVED_TAC "rbx_init" `RBX` THEN
  FULL_INIT_TAC THEN
  X86_STEPS_TAC MLDSA_NATIVE_KECCAKF1600X4_PERMUTE_GCC12_O2_EXEC (1--3) THEN
  LOCAL_KECCAK_CS_TAC `S0:1600 word` 4 THEN
  X86_STEPS_TAC MLDSA_NATIVE_KECCAKF1600X4_PERMUTE_GCC12_O2_EXEC (5--6) THEN
  LOCAL_KECCAK_CS_TAC `S1:1600 word` 7 THEN
  X86_STEPS_TAC MLDSA_NATIVE_KECCAKF1600X4_PERMUTE_GCC12_O2_EXEC (8--9) THEN
  LOCAL_KECCAK_CS_TAC `S2:1600 word` 10 THEN
  X86_STEPS_TAC MLDSA_NATIVE_KECCAKF1600X4_PERMUTE_GCC12_O2_EXEC (11--13) THEN
  LOCAL_KECCAK_CS_TAC `S3:1600 word` 14 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

let MLDSA_NATIVE_KECCAKF1600X4_PERMUTE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_F1600 =
  prove(
MLDSA_NATIVE_KECCAKF1600X4_PERMUTE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_F1600_STMT,
  CORRECT_OF_FULL_TAC
    MLDSA_NATIVE_KECCAKF1600X4_PERMUTE_GCC12_O2_IMAGE_SUBROUTINE_FULL_F1600);;

let MLDSA_NATIVE_KECCAKF1600X4_PERMUTE_GCC12_O2_IMAGE_SUBROUTINE_SAFE = prove
 (MLDSA_NATIVE_KECCAKF1600X4_PERMUTE_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  SAFE_OF_FULL_TAC
    MLDSA_NATIVE_KECCAKF1600X4_PERMUTE_GCC12_O2_IMAGE_SUBROUTINE_FULL_F1600);;
