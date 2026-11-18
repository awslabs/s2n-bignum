(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Unpacking and norm check of a vector of 8 polynomials with coefficients   *)
(* in [-2,2]: the proof (see polyveck_unpack_eta_chknorm_87_spec.ml).        *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/gcc12_O2/polyveck_unpack_eta_chknorm_87_spec.ml";;
needs "arm/proofs/utils/mldsa_native_polyvec.ml";;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together, with a loop over   *)
(* the polynomials, the packed form of polynomial i being at r + 96 * i.     *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVECK_UNPACK_ETA_CHKNORM_87_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  prove
 (MLDSA_NATIVE_POLYVECK_UNPACK_ETA_CHKNORM_87_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT,
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_POLYETA_UNPACK_87_GCC12_O2_IMAGE_SUBROUTINE_FULL "H_C0" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_POLY_CHKNORM_GCC12_O2_IMAGE_SUBROUTINE_FULL "H_C1" THEN
  CONCRETIZE_F_EVENTS_TAC
    `\(r:int64) (bnd:int64) (scratch:int64) (pc:num) (stackpointer:int64)
      (returnaddress:int64).
      APPEND
        (f_ev_epil r bnd scratch pc stackpointer returnaddress)
        (APPEND
          (ENUMERATEL 8
            (\i. f_ev_loop r bnd scratch pc stackpointer returnaddress i))
          (f_ev_prol r bnd scratch pc stackpointer returnaddress))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst
               MLDSA_NATIVE_POLYVECK_UNPACK_ETA_CHKNORM_87_GCC12_O2_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  ENSURES_PRESERVED_TAC "x19_init" `X19` THEN
  ENSURES_PRESERVED_TAC "x20_init" `X20` THEN
  ENSURES_PRESERVED_TAC "x21_init" `X21` THEN
  ENSURES_PRESERVED_TAC "x22_init" `X22` THEN
  ENSURES_PRESERVED_TAC "x23_init" `X23` THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `8`
   `pc + mldsa87_polyveck_unpack_eta_chknorm_loop1`
   `pc + mldsa87_polyveck_unpack_eta_chknorm_loop1_exit`
   `\i s. read X19 s = word_add r (word(96 * i)) /\
          read X23 s = word_add r (word 768) /\
          read X20 s = scratch /\
          read X22 s = word_zx(word_zx (bnd:int64):int32) /\
          read X21 s =
            word_zx(mld_polyvec_chknorm i
                     (mld_polyvec_unpack 96 mld_polyeta_unpack_2 b)
                     (word_zx (bnd:int64))) /\
          read SP s = stackpointer /\
          read (memory :> bytes64 stackpointer) s = x19_init /\
          read (memory :> bytes64 (word_add stackpointer (word 8))) s =
            x20_init /\
          read (memory :> bytes64 (word_add stackpointer (word 16))) s =
            x21_init /\
          read (memory :> bytes64 (word_add stackpointer (word 24))) s =
            x22_init /\
          read (memory :> bytes64 (word_add stackpointer (word 32))) s =
            x23_init /\
          read (memory :> bytes64 (word_add stackpointer (word 40))) s =
            returnaddress /\
          (!j. j < 768
               ==> read(memory :> bytes8(word_add r (word j))) s = b j)` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** Initialization ***)

    VEC_FULL_INIT_TAC
     MLDSA_NATIVE_POLYVECK_UNPACK_ETA_CHKNORM_87_GCC12_O2_EXEC 8
     [mld_polyvec_chknorm; WORD_ZX_0];

    (*** The loop body, with the loop test ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    FULL_INIT_TAC THEN
    ARM_STEPS_TAC
     MLDSA_NATIVE_POLYVECK_UNPACK_ETA_CHKNORM_87_GCC12_O2_EXEC (1--2) THEN
    VEC_SLICE_TAC
     `!j. j < 96
          ==> read(memory :> bytes8(word_add r (word(96 * i + j)))) s2 =
              b(96 * i + j)` THEN
    ARM_STEPS_TAC
     MLDSA_NATIVE_POLYVECK_UNPACK_ETA_CHKNORM_87_GCC12_O2_EXEC (3--3) THEN
    FULL_CALL_TAC mldsa_native_libmldsa_gcc12_O2_mc
     MLDSA_NATIVE_POLYVECK_UNPACK_ETA_CHKNORM_87_GCC12_O2_EXEC "H_C0"
     [`read X0 s`; `read X1 s`; `\j. (b:num->byte)(96 * i + j)`;
      `pc:num`; `read X30 s`]
     [`pc:num`; `r:int64`; `bnd:int64`; `scratch:int64`; `stackpointer:int64`;
      `returnaddress:int64`; `i:num`] 4 THEN
    ARM_STEPS_TAC
     MLDSA_NATIVE_POLYVECK_UNPACK_ETA_CHKNORM_87_GCC12_O2_EXEC (5--7) THEN
    ARM_STEPS_TAC
     MLDSA_NATIVE_POLYVECK_UNPACK_ETA_CHKNORM_87_GCC12_O2_EXEC (8--8) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[WORD_ZX_ZX_32_64_32]) THEN
    FULL_CALL_TAC mldsa_native_libmldsa_gcc12_O2_mc
     MLDSA_NATIVE_POLYVECK_UNPACK_ETA_CHKNORM_87_GCC12_O2_EXEC "H_C1"
     [`read X0 s`; `mld_polyeta_unpack_2 (\j. (b:num->byte)(96 * i + j))`;
      `read X1 s`; `pc:num`; `read X30 s`]
     [`pc:num`; `r:int64`; `bnd:int64`; `scratch:int64`; `stackpointer:int64`;
      `returnaddress:int64`; `i:num`] 9 THEN
    ARM_STEPS_TAC
     MLDSA_NATIVE_POLYVECK_UNPACK_ETA_CHKNORM_87_GCC12_O2_EXEC (10--12) THEN
    VEC_FULL_FINAL_TAC
     [WORD_ZX_ZX_32_64_32; MLD_POLYVEC_CHKNORM_ADD1;
      MLD_POLY_CHKNORM_POLYVEC_UNPACK];

    (*** The return ***)

    VEC_FULL_EXIT_TAC
     MLDSA_NATIVE_POLYVECK_UNPACK_ETA_CHKNORM_87_GCC12_O2_EXEC 5
     [WORD_ZX_ZX_32_64_32]]);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVECK_UNPACK_ETA_CHKNORM_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  prove
 (MLDSA_NATIVE_POLYVECK_UNPACK_ETA_CHKNORM_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  CORRECT_OF_FULL_TAC
    MLDSA_NATIVE_POLYVECK_UNPACK_ETA_CHKNORM_87_GCC12_O2_IMAGE_SUBROUTINE_FULL);;

let MLDSA_NATIVE_POLYVECK_UNPACK_ETA_CHKNORM_87_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  prove
 (MLDSA_NATIVE_POLYVECK_UNPACK_ETA_CHKNORM_87_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  SAFE_OF_FULL_TAC
    MLDSA_NATIVE_POLYVECK_UNPACK_ETA_CHKNORM_87_GCC12_O2_IMAGE_SUBROUTINE_FULL);;
