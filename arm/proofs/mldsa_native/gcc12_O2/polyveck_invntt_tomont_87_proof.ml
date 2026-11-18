(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Inverse number-theoretic transform of a vector of 8 polynomials, with the *)
(* factor mont / 256: the proof (see polyveck_invntt_tomont_87_spec.ml).     *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/gcc12_O2/polyveck_invntt_tomont_87_spec.ml";;
needs "arm/proofs/utils/mldsa_native_polyvec.ml";;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together. The loop calls     *)
(* mldsa_poly_invntt_tomont for polynomial i at v + 1024 * i, with X19       *)
(* pointing to the next polynomial and X20 to the end of the vector.         *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVECK_INVNTT_TOMONT_87_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  prove
 (MLDSA_NATIVE_POLYVECK_INVNTT_TOMONT_87_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT,
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_IMAGE_SUBROUTINE_FULL "H_POLY" THEN
  CONCRETIZE_F_EVENTS_TAC
    `\(v:int64) (pc:num) (stackpointer:int64) (returnaddress:int64).
      APPEND
        (f_ev_epil v pc stackpointer returnaddress)
        (APPEND
          (ENUMERATEL 8 (\i. f_ev_loop v pc stackpointer returnaddress i))
          (f_ev_prol v pc stackpointer returnaddress))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; NONOVERLAPPING_CLAUSES;
              fst MLDSA_NATIVE_POLYVECK_INVNTT_TOMONT_87_GCC12_O2_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  ENSURES_PRESERVED_TAC "x19_init" `X19` THEN
  ENSURES_PRESERVED_TAC "x20_init" `X20` THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `8` `pc + mldsa87_polyveck_invntt_tomont_loop1`
   `pc + mldsa87_polyveck_invntt_tomont_loop1_exit`
   `\i s. read X19 s = word_add v (word(1024 * i)) /\
          read X20 s = word_add v (word 8192) /\
          read SP s = stackpointer /\
          read (memory :> bytes64 stackpointer) s = x19_init /\
          read (memory :> bytes64 (word_add stackpointer (word 8))) s =
            x20_init /\
          read (memory :> bytes64 (word_add stackpointer (word 16))) s =
            returnaddress /\
          (!j. j < 256 * i
               ==> read(memory :> bytes32(word_add v (word(4 * j)))) s =
                   mld_polyvec_map mld_poly_invntt_tomont x j) /\
          (!j. 256 * i <= j /\ j < 2048
               ==> read(memory :> bytes32(word_add v (word(4 * j)))) s =
                   x j)` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** Initialization ***)

    VEC_FULL_INIT_TAC MLDSA_NATIVE_POLYVECK_INVNTT_TOMONT_87_GCC12_O2_EXEC 4 [];

    (*** The loop body, with the loop test ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    FULL_INIT_TAC THEN
    ARM_STEPS_TAC
     MLDSA_NATIVE_POLYVECK_INVNTT_TOMONT_87_GCC12_O2_EXEC (1--2) THEN
    VEC_SLICE_TAC
     `!j. j < 256
          ==> read(memory :> bytes32(word_add v (word(1024 * i + 4 * j))))
                s2 = x(256 * i + j)` THEN
    VEC_REST_TAC
     `!j. 256 * (i + 1) <= j /\ j < 2048
          ==> read(memory :> bytes32(word_add v (word(4 * j)))) s2 = x j` THEN
    ARM_STEPS_TAC
     MLDSA_NATIVE_POLYVECK_INVNTT_TOMONT_87_GCC12_O2_EXEC (3--3) THEN
    FULL_CALL_TAC mldsa_native_libmldsa_gcc12_O2_mc
     MLDSA_NATIVE_POLYVECK_INVNTT_TOMONT_87_GCC12_O2_EXEC "H_POLY"
     [`read X0 s`; `\j. (x:num->int32)(256 * i + j)`; `pc:num`;
      `read X30 s`]
     [`pc:num`; `v:int64`; `stackpointer:int64`; `returnaddress:int64`;
      `i:num`] 4 THEN
    ARM_STEPS_TAC
     MLDSA_NATIVE_POLYVECK_INVNTT_TOMONT_87_GCC12_O2_EXEC (5--6) THEN
    VEC_FULL_FINAL_TAC [];

    (*** The return ***)

    FULL_EXIT_TAC MLDSA_NATIVE_POLYVECK_INVNTT_TOMONT_87_GCC12_O2_EXEC 3]);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVECK_INVNTT_TOMONT_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  prove
 (MLDSA_NATIVE_POLYVECK_INVNTT_TOMONT_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  CORRECT_OF_FULL_TAC
    MLDSA_NATIVE_POLYVECK_INVNTT_TOMONT_87_GCC12_O2_IMAGE_SUBROUTINE_FULL);;

let MLDSA_NATIVE_POLYVECK_INVNTT_TOMONT_87_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  prove
 (MLDSA_NATIVE_POLYVECK_INVNTT_TOMONT_87_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  SAFE_OF_FULL_TAC
    MLDSA_NATIVE_POLYVECK_INVNTT_TOMONT_87_GCC12_O2_IMAGE_SUBROUTINE_FULL);;
