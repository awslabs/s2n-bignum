(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Forward number-theoretic transform of a vector of 6 polynomials: the      *)
(* proof (see polyveck_ntt_65_spec.ml).                                      *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/gcc12_O2/polyveck_ntt_65_spec.ml";;
needs "x86/proofs/utils/mldsa_native_polyvec.ml";;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together. The loop calls     *)
(* mldsa_poly_ntt for polynomial i at v + 1024 * i, with RBX pointing to the *)
(* next polynomial and RBP to the end of the vector.                         *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVECK_NTT_65_GCC12_O2_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_POLYVECK_NTT_65_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT,
  let EXEC = MLDSA_NATIVE_POLYVECK_NTT_65_GCC12_O2_EXEC in
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_POLY_NTT_GCC12_O2_IMAGE_SUBROUTINE_FULL "H_POLY" THEN
  CONCRETIZE_F_EVENTS_TAC
    `\(v:int64) (pc:num) (stackpointer:int64) (returnaddress:int64).
      APPEND
        (f_ev_epil v pc stackpointer returnaddress)
        (APPEND
          (ENUMERATEL 6 (\i. f_ev_loop v pc stackpointer returnaddress i))
          (f_ev_prol v pc stackpointer returnaddress))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; NONOVERLAPPING_CLAUSES; fst EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_PRESERVED_TAC "rbx_init" `RBX` THEN
  ENSURES_PRESERVED_TAC "rbp_init" `RBP` THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `6` `pc + mldsa65_polyveck_ntt_loop1`
   `pc + mldsa65_polyveck_ntt_loop1_exit`
   `\i s. read RBX s = word_add v (word(1024 * i)) /\
          read RBP s = word_add v (word 6144) /\
          read RSP s = word_add stackpointer (word 64) /\
          read (memory :> bytes64 (word_add stackpointer (word 72))) s =
            rbx_init /\
          read (memory :> bytes64 (word_add stackpointer (word 80))) s =
            rbp_init /\
          read (memory :> bytes64 (word_add stackpointer (word 88))) s =
            returnaddress /\
          (!j. j < 256 * i
               ==> read(memory :> bytes32(word_add v (word(4 * j)))) s =
                   mld_polyvec_map mld_poly_ntt x j) /\
          (!j. 256 * i <= j /\ j < 1536
               ==> read(memory :> bytes32(word_add v (word(4 * j)))) s =
                   x j)` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** Initialization ***)

    VEC_FULL_INIT_TAC EXEC 5 [];

    (*** The loop body, with the loop test ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    FULL_INIT_TAC THEN
    X86_STEPS_TAC EXEC (1--2) THEN
    VEC_SLICE_TAC
     `!j. j < 256
          ==> read(memory :> bytes32(word_add v (word(1024 * i + 4 * j))))
                s2 = x(256 * i + j)` THEN
    VEC_REST_TAC
     `!j. 256 * (i + 1) <= j /\ j < 1536
          ==> read(memory :> bytes32(word_add v (word(4 * j)))) s2 = x j` THEN
    X86_STEPS_TAC EXEC (3--3) THEN
    FULL_CALL_TAC mldsa_native_libmldsa_gcc12_O2_mc EXEC "H_POLY"
     [`read RDI s`; `\j. (x:num->int32)(256 * i + j)`; `pc:num`; `read RSP s`;
      `read (memory :> bytes64 (read RSP s)) s`]
     [`pc:num`; `v:int64`; `stackpointer:int64`;
      `returnaddress:int64`; `i:num`] 4 THEN
    X86_STEPS_TAC EXEC (5--6) THEN
    VEC_FULL_FINAL_TAC [];

    (*** The return ***)

    FULL_EXIT_TAC EXEC 4]);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVECK_NTT_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_POLYVECK_NTT_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  CORRECT_OF_FULL_TAC
    MLDSA_NATIVE_POLYVECK_NTT_65_GCC12_O2_IMAGE_SUBROUTINE_FULL);;

let MLDSA_NATIVE_POLYVECK_NTT_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE = prove
 (MLDSA_NATIVE_POLYVECK_NTT_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  SAFE_OF_FULL_TAC
    MLDSA_NATIVE_POLYVECK_NTT_65_GCC12_O2_IMAGE_SUBROUTINE_FULL);;
