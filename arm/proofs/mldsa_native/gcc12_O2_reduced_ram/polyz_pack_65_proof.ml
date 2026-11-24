(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Packing of a polynomial with 20 bits per coefficient, of 2^19 - a: the    *)
(* proof.                                                                    *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/gcc12_O2_reduced_ram/polyz_pack_65_spec.ml";;
needs "arm/proofs/utils/mldsa_native_full.ml";;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety. Each of the 128 iterations  *)
(* of the loop handles 2 coefficients and 5 bytes. The code before the loop  *)
(* saves the return address, loads the stack guard and stores it as the      *)
(* canary; the code after the loop zeroes the temporary array, checks the    *)
(* canary against the stack guard and restores the return address. The loop  *)
(* test is the end of the body, as ENSURES_EVENTS_WHILE_UP2_TAC requires,    *)
(* and the events of an iteration depend on its index only.                  *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYZ_PACK_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_POLYZ_PACK_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT,
  let EXEC = MLDSA_NATIVE_POLYZ_PACK_65_GCC12_O2_REDUCED_RAM_EXEC in
  CONCRETIZE_F_EVENTS_TAC
    `\(r:int64) (a:int64) (guard:int64) (pc:num) (stackpointer:int64)
      (returnaddress:int64).
      APPEND
        (f_ev_epil r a guard pc stackpointer returnaddress)
        (APPEND
          (ENUMERATEL 128
            (\i. f_ev_loop r a guard pc stackpointer returnaddress i))
          (f_ev_prol r a guard pc stackpointer returnaddress))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; ALL; ALLPAIRS; PAIRWISE; fst EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_stack_chk_guard:num`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [SPECL [`pc:num`; `got_stack_chk_guard:num`] WORD_ADD]) THEN
  GHOST_INTRO_TAC `canary:int64` `read (memory :> bytes64 guard)` THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `128` `pc + mldsa65_polyz_pack_loop1`
   `pc + mldsa65_polyz_pack_loop1_exit`
   `\i s. read X0 s = word_add r (word(5 * i)) /\
          read X1 s = word_add a (word(8 * i)) /\
          read X7 s = word_add r (word 640) /\
          read X5 s = word 524288 /\
          read SP s = stackpointer /\
          read (memory :> bytes64 stackpointer) s = returnaddress /\
          read (memory :> bytes64 (word_add stackpointer (word 40))) s =
          canary /\
          read (memory :> bytes64 (word_add (word pc) (word 131064))) s =
          guard /\
          read (memory :> bytes64 guard) s = canary /\
          (!j. j < 256
               ==> read(memory :> bytes32(word_add a (word(4 * j)))) s =
                   x j) /\
          (!j. j < 5 * i
               ==> read(memory :> bytes8(word_add r (word j))) s =
                   mld_polyz_pack_19 x j)` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** Initialization, saving the return address and the stack guard ***)

    FULL_INIT_TAC THEN
    ARM_STEPS_TAC EXEC (1--1) THEN
    MLKEM_NATIVE_ADRP_TAC THEN
    ARM_STEPS_TAC EXEC (2--8) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; ADD_CLAUSES; WORD_ADD_0] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    (*** The loop body ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    FULL_INIT_TAC THEN
    CHUNK_INPUT_TAC `x:num->int32` 2 THEN
    ARM_STEPS_TAC EXEC (1--17) THEN
    CHUNK_FULL_FINAL_TAC mld_polyz_pack_19 `x:num->int32`;

    (*** The zeroing, the check of the stack guard and the return ***)

    REWRITE_TAC[] THEN FULL_INIT_TAC THEN
    ARM_STEPS_TAC EXEC (1--3) THEN
    MLKEM_NATIVE_ADRP_TAC THEN
    ARM_STEPS_TAC EXEC (4--11) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN
    TRY(FIRST_ASSUM(MATCH_ACCEPT_TAC o
          CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN NO_TAC) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYZ_PACK_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_POLYZ_PACK_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT,
  CORRECT_OF_FULL_TAC
    MLDSA_NATIVE_POLYZ_PACK_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL);;

let MLDSA_NATIVE_POLYZ_PACK_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE = prove
 (MLDSA_NATIVE_POLYZ_PACK_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT,
  SAFE_OF_FULL_TAC
    MLDSA_NATIVE_POLYZ_PACK_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL);;
