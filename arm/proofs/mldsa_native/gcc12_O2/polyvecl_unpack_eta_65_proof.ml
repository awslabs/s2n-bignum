(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Unpacking of a vector of 5 polynomials with coefficients in [-4,4]: the   *)
(* proof (see polyvecl_unpack_eta_65_spec.ml).                               *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/gcc12_O2/polyvecl_unpack_eta_65_spec.ml";;
needs "arm/proofs/utils/mldsa_native_polyvec.ml";;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together, with a loop over   *)
(* the polynomials, polynomial i being at p + 1024 * i and its packed form   *)
(* at r + 128 * i.                                                           *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVECL_UNPACK_ETA_65_GCC12_O2_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_POLYVECL_UNPACK_ETA_65_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT,
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_POLYETA_UNPACK_65_GCC12_O2_IMAGE_SUBROUTINE_FULL "H_C0" THEN
  CONCRETIZE_F_EVENTS_TAC
    `\(p:int64) (r:int64) (pc:num) (stackpointer:int64)
      (returnaddress:int64).
      APPEND
        (f_ev_epil p r pc stackpointer returnaddress)
        (APPEND
          (ENUMERATEL 5 (\i. f_ev_loop p r pc stackpointer returnaddress i))
          (f_ev_prol p r pc stackpointer returnaddress))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst MLDSA_NATIVE_POLYVECL_UNPACK_ETA_65_GCC12_O2_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  ENSURES_PRESERVED_TAC "x19_init" `X19` THEN
  ENSURES_PRESERVED_TAC "x20_init" `X20` THEN
  ENSURES_PRESERVED_TAC "x21_init" `X21` THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `5` `pc + mldsa65_polyvecl_unpack_eta_loop1`
   `pc + mldsa65_polyvecl_unpack_eta_loop1_exit`
   `\i s. read X19 s = word_add p (word(1024 * i)) /\
          read X20 s = word_add r (word(128 * i)) /\
          read X21 s = word_add p (word 5120) /\
          read SP s = stackpointer /\
          read (memory :> bytes64 stackpointer) s = x19_init /\
          read (memory :> bytes64 (word_add stackpointer (word 8))) s =
            x20_init /\
          read (memory :> bytes64 (word_add stackpointer (word 16))) s =
            x21_init /\
          read (memory :> bytes64 (word_add stackpointer (word 24))) s =
            returnaddress /\
          (!j. j < 256 * i
               ==> read(memory :> bytes32(word_add p (word(4 * j)))) s =
                   mld_polyvec_unpack 128 mld_polyeta_unpack_4 b j) /\
          (!j. j < 640
               ==> read(memory :> bytes8(word_add r (word j))) s = b j)` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** Initialization ***)

    VEC_FULL_INIT_TAC MLDSA_NATIVE_POLYVECL_UNPACK_ETA_65_GCC12_O2_EXEC 6
     [];

    (*** The loop body, with the loop test ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    FULL_INIT_TAC THEN
    ARM_STEPS_TAC MLDSA_NATIVE_POLYVECL_UNPACK_ETA_65_GCC12_O2_EXEC (1--3) THEN
    VEC_SLICE_TAC
     `!j. j < 128
          ==> read(memory :> bytes8(word_add r (word(128 * i + j)))) s3 =
              b(128 * i + j)` THEN
    ARM_STEPS_TAC MLDSA_NATIVE_POLYVECL_UNPACK_ETA_65_GCC12_O2_EXEC (4--4) THEN
    FULL_CALL_TAC mldsa_native_libmldsa_gcc12_O2_mc
     MLDSA_NATIVE_POLYVECL_UNPACK_ETA_65_GCC12_O2_EXEC "H_C0"
     [`read X0 s`; `read X1 s`; `\j. (b:num->byte)(128 * i + j)`;
      `pc:num`; `read X30 s`]
     [`pc:num`; `p:int64`; `r:int64`; `stackpointer:int64`;
      `returnaddress:int64`; `i:num`] 5 THEN
    ARM_STEPS_TAC MLDSA_NATIVE_POLYVECL_UNPACK_ETA_65_GCC12_O2_EXEC (6--8) THEN
    VEC_FULL_FINAL_TAC
     [];

    (*** The return ***)

    VEC_FULL_EXIT_TAC MLDSA_NATIVE_POLYVECL_UNPACK_ETA_65_GCC12_O2_EXEC 3
     []]);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVECL_UNPACK_ETA_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  prove
 (MLDSA_NATIVE_POLYVECL_UNPACK_ETA_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  CORRECT_OF_FULL_TAC
    MLDSA_NATIVE_POLYVECL_UNPACK_ETA_65_GCC12_O2_IMAGE_SUBROUTINE_FULL);;

let MLDSA_NATIVE_POLYVECL_UNPACK_ETA_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE = prove
 (MLDSA_NATIVE_POLYVECL_UNPACK_ETA_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  SAFE_OF_FULL_TAC
    MLDSA_NATIVE_POLYVECL_UNPACK_ETA_65_GCC12_O2_IMAGE_SUBROUTINE_FULL);;
