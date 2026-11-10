(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Unpacking and norm check of a vector of 6 polynomials with coefficients   *)
(* in [-4,4]: the proof (see polyveck_unpack_eta_chknorm_65_spec.ml).        *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/gcc12_O2/polyveck_unpack_eta_chknorm_65_spec.ml";;
needs "x86/proofs/utils/mldsa_native_polyvec.ml";;
needs "x86/proofs/utils/mldsa_native_wrap.ml";;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together, with a loop over   *)
(* the polynomials, the packed form of polynomial i being at r + 128 * i,    *)
(* with RBX pointing to the next packed form, R14 to the end of them, RBP to *)
(* the scratch polynomial, the bound in R13 and the OR of the results so far *)
(* in R12.                                                                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVECK_UNPACK_ETA_CHKNORM_65_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  prove
 (MLDSA_NATIVE_POLYVECK_UNPACK_ETA_CHKNORM_65_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT,
  let EXEC = MLDSA_NATIVE_POLYVECK_UNPACK_ETA_CHKNORM_65_GCC12_O2_EXEC in
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_POLYETA_UNPACK_65_GCC12_O2_IMAGE_SUBROUTINE_FULL "H_C0" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_POLY_CHKNORM_GCC12_O2_IMAGE_SUBROUTINE_FULL "H_C1" THEN
  CONCRETIZE_F_EVENTS_TAC
    `\(r:int64) (bnd:int64) (scratch:int64) (pc:num) (stackpointer:int64)
      (returnaddress:int64).
      APPEND
        (f_ev_epil r bnd scratch pc stackpointer returnaddress)
        (APPEND
          (ENUMERATEL 6
            (\i. f_ev_loop r bnd scratch pc stackpointer returnaddress i))
          (f_ev_prol r bnd scratch pc stackpointer returnaddress))
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
  ENSURES_PRESERVED_TAC "r14_init" `R14` THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `6`
   `pc + mldsa65_polyveck_unpack_eta_chknorm_loop1`
   `pc + mldsa65_polyveck_unpack_eta_chknorm_loop1_exit`
   `\i s. read RBX s = word_add r (word(128 * i)) /\
          read R14 s = word_add r (word 768) /\
          read RBP s = scratch /\
          read R13 s = word_zx(word_zx (bnd:int64):int32) /\
          read R12 s =
            word_zx(mld_polyvec_chknorm i
                     (mld_polyvec_unpack 128 mld_polyeta_unpack_4 b)
                     (word_zx (bnd:int64))) /\
          read RSP s = word_add stackpointer (word 8) /\
          read (memory :> bytes64 (word_add stackpointer (word 8))) s =
            rbx_init /\
          read (memory :> bytes64 (word_add stackpointer (word 16))) s =
            rbp_init /\
          read (memory :> bytes64 (word_add stackpointer (word 24))) s =
            r12_init /\
          read (memory :> bytes64 (word_add stackpointer (word 32))) s =
            r13_init /\
          read (memory :> bytes64 (word_add stackpointer (word 40))) s =
            r14_init /\
          read (memory :> bytes64 (word_add stackpointer (word 48))) s =
            returnaddress /\
          (!j. j < 768
               ==> read(memory :> bytes8(word_add r (word j))) s = b j)` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** Initialization ***)

    VEC_FULL_INIT_TAC EXEC 11 [mld_polyvec_chknorm; WORD_ZX_0];

    (*** The loop body, with the loop test ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    FULL_INIT_TAC THEN
    X86_STEPS_TAC EXEC (1--3) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[WORD_SUB_M128]) THEN
    VEC_SLICE_TAC
     `!j. j < 128
          ==> read(memory :> bytes8(word_add r (word(128 * i + j)))) s3 =
              b(128 * i + j)` THEN
    X86_STEPS_TAC EXEC (4--4) THEN
    FULL_CALL_TAC mldsa_native_libmldsa_gcc12_O2_mc EXEC "H_C0"
     [`read RDI s`; `read RSI s`; `\j. (b:num->byte)(128 * i + j)`;
      `pc:num`; `read RSP s`; `read (memory :> bytes64 (read RSP s)) s`]
     [`pc:num`; `r:int64`; `bnd:int64`; `scratch:int64`;
      `stackpointer:int64`; `returnaddress:int64`; `i:num`] 5 THEN
    X86_STEPS_TAC EXEC (6--8) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[WORD_ZX_ZX_32_64_32]) THEN
    FULL_CALL_TAC mldsa_native_libmldsa_gcc12_O2_mc EXEC "H_C1"
     [`read RDI s`; `mld_polyeta_unpack_4 (\j. (b:num->byte)(128 * i + j))`;
      `read RSI s`; `pc:num`; `read RSP s`;
      `read (memory :> bytes64 (read RSP s)) s`]
     [`pc:num`; `r:int64`; `bnd:int64`; `scratch:int64`;
      `stackpointer:int64`; `returnaddress:int64`; `i:num`] 9 THEN
    X86_STEPS_TAC EXEC (10--12) THEN
    VEC_FULL_FINAL_TAC
     [WORD_ZX_ZX_32_64_32; MLD_POLYVEC_CHKNORM_ADD1;
      MLD_POLY_CHKNORM_POLYVEC_UNPACK];

    (*** The return ***)

    VEC_FULL_EXIT_TAC EXEC 7 [WORD_ZX_ZX_32_64_32]]);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let
 MLDSA_NATIVE_POLYVECK_UNPACK_ETA_CHKNORM_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  prove
 (MLDSA_NATIVE_POLYVECK_UNPACK_ETA_CHKNORM_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  CORRECT_OF_FULL_TAC
    MLDSA_NATIVE_POLYVECK_UNPACK_ETA_CHKNORM_65_GCC12_O2_IMAGE_SUBROUTINE_FULL);;

let MLDSA_NATIVE_POLYVECK_UNPACK_ETA_CHKNORM_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  prove
 (MLDSA_NATIVE_POLYVECK_UNPACK_ETA_CHKNORM_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  SAFE_OF_FULL_TAC
    MLDSA_NATIVE_POLYVECK_UNPACK_ETA_CHKNORM_65_GCC12_O2_IMAGE_SUBROUTINE_FULL);;
