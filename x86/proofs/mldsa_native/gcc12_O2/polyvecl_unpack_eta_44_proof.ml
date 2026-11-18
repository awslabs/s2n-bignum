(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Unpacking of a vector of 4 polynomials with coefficients in [-2,2]: the   *)
(* proof (see polyvecl_unpack_eta_44_spec.ml).                               *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/gcc12_O2/polyvecl_unpack_eta_44_spec.ml";;
needs "x86/proofs/utils/mldsa_native_polyvec.ml";;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together, with a loop over   *)
(* the polynomials, polynomial i being at p + 1024 * i and its packed form   *)
(* at r + 96 * i, with RBX pointing to the packed form of the next           *)
(* polynomial, RBP to the next polynomial and R12 to the end of the packed   *)
(* forms.                                                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVECL_UNPACK_ETA_44_GCC12_O2_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_POLYVECL_UNPACK_ETA_44_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT,
  let EXEC = MLDSA_NATIVE_POLYVECL_UNPACK_ETA_44_GCC12_O2_EXEC in
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_POLYETA_UNPACK_44_GCC12_O2_IMAGE_SUBROUTINE_FULL "H_C0" THEN
  CONCRETIZE_F_EVENTS_TAC
    `\(p:int64) (r:int64) (pc:num) (stackpointer:int64)
      (returnaddress:int64).
      APPEND
        (f_ev_epil p r pc stackpointer returnaddress)
        (APPEND
          (ENUMERATEL 4 (\i. f_ev_loop p r pc stackpointer returnaddress i))
          (f_ev_prol p r pc stackpointer returnaddress))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; NONOVERLAPPING_CLAUSES; fst EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_PRESERVED_TAC "rbx_init" `RBX` THEN
  ENSURES_PRESERVED_TAC "rbp_init" `RBP` THEN
  ENSURES_PRESERVED_TAC "r12_init" `R12` THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `4`
   `pc + mldsa44_polyvecl_unpack_eta_loop1`
   `pc + mldsa44_polyvecl_unpack_eta_loop1_exit`
   `\i s. read RBX s = word_add r (word(96 * i)) /\
          read RBP s = word_add p (word(1024 * i)) /\
          read R12 s = word_add r (word 384) /\
          read RSP s = word_add stackpointer (word 40) /\
          read (memory :> bytes64 (word_add stackpointer (word 40))) s =
            rbx_init /\
          read (memory :> bytes64 (word_add stackpointer (word 48))) s =
            rbp_init /\
          read (memory :> bytes64 (word_add stackpointer (word 56))) s =
            r12_init /\
          read (memory :> bytes64 (word_add stackpointer (word 64))) s =
            returnaddress /\
          (!j. j < 256 * i
               ==> read(memory :> bytes32(word_add p (word(4 * j)))) s =
                   mld_polyvec_unpack 96 mld_polyeta_unpack_2 b j) /\
          (!j. j < 384
               ==> read(memory :> bytes8(word_add r (word j))) s = b j)` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** Initialization ***)

    VEC_FULL_INIT_TAC EXEC 6 [];

    (*** The loop body, with the loop test ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    FULL_INIT_TAC THEN
    X86_STEPS_TAC EXEC (1--4) THEN
    VEC_SLICE_TAC
     `!j. j < 96
          ==> read(memory :> bytes8(word_add r (word(96 * i + j)))) s4 =
              b(96 * i + j)` THEN
    X86_STEPS_TAC EXEC (5--5) THEN
    FULL_CALL_TAC mldsa_native_libmldsa_gcc12_O2_mc EXEC "H_C0"
     [`read RDI s`; `read RSI s`; `\j. (b:num->byte)(96 * i + j)`;
      `pc:num`; `read RSP s`; `read (memory :> bytes64 (read RSP s)) s`]
     [`pc:num`; `p:int64`; `r:int64`; `stackpointer:int64`;
      `returnaddress:int64`; `i:num`] 6 THEN
    X86_STEPS_TAC EXEC (7--8) THEN
    VEC_FULL_FINAL_TAC [];

    (*** The return ***)

    VEC_FULL_EXIT_TAC EXEC 4 []]);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVECL_UNPACK_ETA_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  prove
 (MLDSA_NATIVE_POLYVECL_UNPACK_ETA_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  CORRECT_OF_FULL_TAC
    MLDSA_NATIVE_POLYVECL_UNPACK_ETA_44_GCC12_O2_IMAGE_SUBROUTINE_FULL);;

let MLDSA_NATIVE_POLYVECL_UNPACK_ETA_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE = prove
 (MLDSA_NATIVE_POLYVECL_UNPACK_ETA_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  SAFE_OF_FULL_TAC
    MLDSA_NATIVE_POLYVECL_UNPACK_ETA_44_GCC12_O2_IMAGE_SUBROUTINE_FULL);;
