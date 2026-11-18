(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Norm check of a vector of 4 polynomials: the proof (see                   *)
(* polyvecl_chknorm_44_spec.ml).                                             *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/gcc12_O2/polyvecl_chknorm_44_spec.ml";;
needs "arm/proofs/utils/mldsa_native_polyvec.ml";;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together, with a loop over   *)
(* the polynomials, polynomial i being at v + 1024 * i.                      *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVECL_CHKNORM_44_GCC12_O2_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_POLYVECL_CHKNORM_44_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT,
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_POLY_CHKNORM_GCC12_O2_IMAGE_SUBROUTINE_FULL "H_C0" THEN
  CONCRETIZE_F_EVENTS_TAC
    `\(v:int64) (bnd:int64) (pc:num) (stackpointer:int64)
      (returnaddress:int64).
      APPEND
        (f_ev_epil v bnd pc stackpointer returnaddress)
        (APPEND
          (ENUMERATEL 4 (\i. f_ev_loop v bnd pc stackpointer returnaddress i))
          (f_ev_prol v bnd pc stackpointer returnaddress))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst MLDSA_NATIVE_POLYVECL_CHKNORM_44_GCC12_O2_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  ENSURES_PRESERVED_TAC "x19_init" `X19` THEN
  ENSURES_PRESERVED_TAC "x20_init" `X20` THEN
  ENSURES_PRESERVED_TAC "x21_init" `X21` THEN
  ENSURES_PRESERVED_TAC "x22_init" `X22` THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `4` `pc + mldsa44_polyvecl_chknorm_loop1`
   `pc + mldsa44_polyvecl_chknorm_loop1_exit`
   `\i s. read X19 s = word_add v (word(1024 * i)) /\
          read X22 s = word_add v (word 4096) /\
          read X21 s = word_zx(word_zx (bnd:int64):int32) /\
          read X20 s =
            word_zx(mld_polyvec_chknorm i x (word_zx (bnd:int64))) /\
          read SP s = stackpointer /\
          read (memory :> bytes64 stackpointer) s = x19_init /\
          read (memory :> bytes64 (word_add stackpointer (word 8))) s =
            x20_init /\
          read (memory :> bytes64 (word_add stackpointer (word 16))) s =
            x21_init /\
          read (memory :> bytes64 (word_add stackpointer (word 24))) s =
            x22_init /\
          read (memory :> bytes64 (word_add stackpointer (word 32))) s =
            returnaddress /\
          (!j. j < 1024
               ==> read(memory :> bytes32(word_add v (word(4 * j)))) s =
                   x j)` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** Initialization ***)

    VEC_FULL_INIT_TAC MLDSA_NATIVE_POLYVECL_CHKNORM_44_GCC12_O2_EXEC 7
     [mld_polyvec_chknorm; WORD_ZX_0];

    (*** The loop body, with the loop test ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    FULL_INIT_TAC THEN
    ARM_STEPS_TAC MLDSA_NATIVE_POLYVECL_CHKNORM_44_GCC12_O2_EXEC (1--3) THEN
    VEC_SLICE_TAC
     `!j. j < 256
          ==> read(memory :> bytes32(word_add v (word(1024 * i + 4 * j))))
                s3 = x(256 * i + j)` THEN
    ARM_STEPS_TAC MLDSA_NATIVE_POLYVECL_CHKNORM_44_GCC12_O2_EXEC (4--4) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[WORD_ZX_ZX_32_64_32]) THEN
    FULL_CALL_TAC mldsa_native_libmldsa_gcc12_O2_mc
     MLDSA_NATIVE_POLYVECL_CHKNORM_44_GCC12_O2_EXEC "H_C0"
     [`read X0 s`; `\j. (x:num->int32)(256 * i + j)`; `read X1 s`;
      `pc:num`; `read X30 s`]
     [`pc:num`; `v:int64`; `bnd:int64`; `stackpointer:int64`;
      `returnaddress:int64`; `i:num`] 5 THEN
    ARM_STEPS_TAC MLDSA_NATIVE_POLYVECL_CHKNORM_44_GCC12_O2_EXEC (6--8) THEN
    VEC_FULL_FINAL_TAC
     [WORD_ZX_ZX_32_64_32; MLD_POLYVEC_CHKNORM_ADD1; mld_poly_of];

    (*** The return ***)

    VEC_FULL_EXIT_TAC MLDSA_NATIVE_POLYVECL_CHKNORM_44_GCC12_O2_EXEC 5
     [WORD_ZX_ZX_32_64_32]]);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVECL_CHKNORM_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_POLYVECL_CHKNORM_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  CORRECT_OF_FULL_TAC
    MLDSA_NATIVE_POLYVECL_CHKNORM_44_GCC12_O2_IMAGE_SUBROUTINE_FULL);;

let MLDSA_NATIVE_POLYVECL_CHKNORM_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE = prove
 (MLDSA_NATIVE_POLYVECL_CHKNORM_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  SAFE_OF_FULL_TAC
    MLDSA_NATIVE_POLYVECL_CHKNORM_44_GCC12_O2_IMAGE_SUBROUTINE_FULL);;
