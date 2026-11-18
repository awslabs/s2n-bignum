(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Norm check of a vector of 7 polynomials: the proof (see                   *)
(* polyvecl_chknorm_87_spec.ml).                                             *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/gcc12_O2/polyvecl_chknorm_87_spec.ml";;
needs "x86/proofs/utils/mldsa_native_polyvec.ml";;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together. The loop calls     *)
(* mldsa_poly_chknorm for polynomial i at v + 1024 * i, with RBX pointing to *)
(* the next polynomial and R13 to the end of the vector, the bound in R12    *)
(* and the OR of the results so far in RBP.                                  *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVECL_CHKNORM_87_GCC12_O2_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_POLYVECL_CHKNORM_87_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT,
  let EXEC = MLDSA_NATIVE_POLYVECL_CHKNORM_87_GCC12_O2_EXEC in
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_POLY_CHKNORM_GCC12_O2_IMAGE_SUBROUTINE_FULL "H_POLY" THEN
  CONCRETIZE_F_EVENTS_TAC
    `\(v:int64) (bnd:int64) (pc:num) (stackpointer:int64)
      (returnaddress:int64).
      APPEND
        (f_ev_epil v bnd pc stackpointer returnaddress)
        (APPEND
          (ENUMERATEL 7 (\i. f_ev_loop v bnd pc stackpointer returnaddress i))
          (f_ev_prol v bnd pc stackpointer returnaddress))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; NONOVERLAPPING_CLAUSES; fst EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_PRESERVED_TAC "rbx_init" `RBX` THEN
  ENSURES_PRESERVED_TAC "rbp_init" `RBP` THEN
  ENSURES_PRESERVED_TAC "r12_init" `R12` THEN
  ENSURES_PRESERVED_TAC "r13_init" `R13` THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `7` `pc + mldsa87_polyvecl_chknorm_loop1`
   `pc + mldsa87_polyvecl_chknorm_loop1_exit`
   `\i s. read RBX s = word_add v (word(1024 * i)) /\
          read R13 s = word_add v (word 7168) /\
          read R12 s = word_zx(word_zx (bnd:int64):int32) /\
          read RBP s =
            word_zx(mld_polyvec_chknorm i x (word_zx (bnd:int64))) /\
          read RSP s = word_add stackpointer (word 8) /\
          read (memory :> bytes64 (word_add stackpointer (word 16))) s =
            rbx_init /\
          read (memory :> bytes64 (word_add stackpointer (word 24))) s =
            rbp_init /\
          read (memory :> bytes64 (word_add stackpointer (word 32))) s =
            r12_init /\
          read (memory :> bytes64 (word_add stackpointer (word 40))) s =
            r13_init /\
          read (memory :> bytes64 (word_add stackpointer (word 48))) s =
            returnaddress /\
          (!j. j < 1792
               ==> read(memory :> bytes32(word_add v (word(4 * j)))) s =
                   x j)` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** Initialization ***)

    VEC_FULL_INIT_TAC EXEC 10 [mld_polyvec_chknorm; WORD_ZX_0];

    (*** The loop body, with the loop test ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    FULL_INIT_TAC THEN
    X86_STEPS_TAC EXEC (1--3) THEN
    VEC_SLICE_TAC
     `!j. j < 256
          ==> read(memory :> bytes32(word_add v (word(1024 * i + 4 * j))))
                s3 = x(256 * i + j)` THEN
    X86_STEPS_TAC EXEC (4--4) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[WORD_ZX_ZX_32_64_32]) THEN
    FULL_CALL_TAC mldsa_native_libmldsa_gcc12_O2_mc EXEC "H_POLY"
     [`read RDI s`; `\j. (x:num->int32)(256 * i + j)`; `read RSI s`;
      `pc:num`; `read RSP s`;
      `read (memory :> bytes64 (read RSP s)) s`]
     [`pc:num`; `v:int64`; `bnd:int64`; `stackpointer:int64`;
      `returnaddress:int64`; `i:num`] 5 THEN
    X86_STEPS_TAC EXEC (6--8) THEN
    VEC_FULL_FINAL_TAC
     [WORD_ZX_ZX_32_64_32; MLD_POLYVEC_CHKNORM_ADD1; mld_poly_of];

    (*** The return ***)

    VEC_FULL_EXIT_TAC EXEC 7 [WORD_ZX_ZX_32_64_32]]);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVECL_CHKNORM_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_POLYVECL_CHKNORM_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  CORRECT_OF_FULL_TAC
    MLDSA_NATIVE_POLYVECL_CHKNORM_87_GCC12_O2_IMAGE_SUBROUTINE_FULL);;

let MLDSA_NATIVE_POLYVECL_CHKNORM_87_GCC12_O2_IMAGE_SUBROUTINE_SAFE = prove
 (MLDSA_NATIVE_POLYVECL_CHKNORM_87_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  SAFE_OF_FULL_TAC
    MLDSA_NATIVE_POLYVECL_CHKNORM_87_GCC12_O2_IMAGE_SUBROUTINE_FULL);;
