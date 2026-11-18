(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Unpacking of a polynomial with 4 bits per coefficient, of 4 - a: the      *)
(* proof.                                                                    *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/gcc12_O2/polyeta_unpack_65_spec.ml";;
needs "x86/proofs/utils/mldsa_native_pack.ml";;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety. Each of the 128 iterations  *)
(* of the loop handles 1 byte and 2 coefficients, storing the first          *)
(* coefficient twice, the second time with its final value; the pointer to   *)
(* the outputs in RDX is 4 bytes beyond the start of the pair. The loop test *)
(* is the end of the body, as ENSURES_EVENTS_WHILE_UP2_TAC requires, and the *)
(* events of an iteration depend on its index only.                          *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYETA_UNPACK_65_GCC12_O2_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_POLYETA_UNPACK_65_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT,
  let EXEC = MLDSA_NATIVE_POLYETA_UNPACK_65_GCC12_O2_EXEC in
  CONCRETIZE_F_EVENTS_TAC
    `\(r:int64) (a:int64) (pc:num) (stackpointer:int64)
      (returnaddress:int64).
      APPEND
        (f_ev_epil r a pc stackpointer returnaddress)
        (APPEND
          (ENUMERATEL 128
            (\i. f_ev_loop r a pc stackpointer returnaddress i))
          (f_ev_prol r a pc stackpointer returnaddress))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `r:int64`; `a:int64`; `b:num->byte`; `pc:num`;
    `stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; ALL; fst EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `128` `pc + mldsa65_polyeta_unpack_loop1`
   `pc + mldsa65_polyeta_unpack_loop1_exit`
   `\i s. read RDX s = word_add (word_add r (word(8 * i))) (word 4) /\
          read RSI s = word_add a (word i) /\
          read R9 s = word_add a (word 128) /\
          read RDI s = word 4 /\
          read RSP s = stackpointer /\
          read (memory :> bytes64 stackpointer) s = returnaddress /\
          (!j. j < 128
               ==> read(memory :> bytes8(word_add a (word j))) s = b j) /\
          (!j. j < 2 * i
               ==> read(memory :> bytes32(word_add r (word(4 * j)))) s =
                   mld_polyeta_unpack_4 b j)` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** Initialization ***)

    FULL_INIT_TAC THEN
    X86_STEPS_TAC EXEC (1--3) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; WORD_ADD_0] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    (*** The loop body, with the loop test ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    FULL_INIT_TAC THEN
    CHUNK_INPUT_TAC `b:num->byte` 1 THEN
    X86_STEPS_TAC EXEC (1--16) THEN
    CHUNK_FULL_FINAL_TAC mld_polyeta_unpack_4 `b:num->byte`;

    (*** The return ***)

    FULL_EXIT_TAC EXEC 1]);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYETA_UNPACK_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_POLYETA_UNPACK_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  CORRECT_OF_FULL_TAC
    MLDSA_NATIVE_POLYETA_UNPACK_65_GCC12_O2_IMAGE_SUBROUTINE_FULL);;

let MLDSA_NATIVE_POLYETA_UNPACK_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE = prove
 (MLDSA_NATIVE_POLYETA_UNPACK_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  SAFE_OF_FULL_TAC
    MLDSA_NATIVE_POLYETA_UNPACK_65_GCC12_O2_IMAGE_SUBROUTINE_FULL);;
