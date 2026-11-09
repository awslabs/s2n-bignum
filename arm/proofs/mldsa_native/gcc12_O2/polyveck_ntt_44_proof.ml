(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Forward number-theoretic transform of a vector of 4 polynomials: the      *)
(* proof (see polyveck_ntt_44_spec.ml).                                      *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/gcc12_O2/polyveck_ntt_44_spec.ml";;
needs "arm/proofs/utils/mldsa_native_polyvec.ml";;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together. The calls of       *)
(* mldsa_poly_ntt for the polynomials at v + 1024 * i, the last a tail call. *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVECK_NTT_44_GCC12_O2_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_POLYVECK_NTT_44_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT,
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_POLY_NTT_GCC12_O2_IMAGE_SUBROUTINE_FULL "H_POLY" THEN
  META_EXISTS_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; NONOVERLAPPING_CLAUSES;
              fst MLDSA_NATIVE_POLYVECK_NTT_44_GCC12_O2_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  ENSURES_PRESERVED_TAC "x19_init" `X19` THEN
  FULL_INIT_TAC THEN POLYVEC_SPLIT_TAC 4 THEN
  ARM_STEPS_TAC MLDSA_NATIVE_POLYVECK_NTT_44_GCC12_O2_EXEC (1--3) THEN
  FULL_CALL_TAC mldsa_native_libmldsa_gcc12_O2_mc
   MLDSA_NATIVE_POLYVECK_NTT_44_GCC12_O2_EXEC "H_POLY"
   [`read X0 s`; `x:num->int32`; `pc:num`; `read X30 s`]
   [`pc:num`; `v:int64`; `stackpointer:int64`;
    `returnaddress:int64`] 4 THEN
  ARM_STEPS_TAC MLDSA_NATIVE_POLYVECK_NTT_44_GCC12_O2_EXEC (5--6) THEN
  FULL_CALL_TAC mldsa_native_libmldsa_gcc12_O2_mc
   MLDSA_NATIVE_POLYVECK_NTT_44_GCC12_O2_EXEC "H_POLY"
   [`read X0 s`; `\j. (x:num->int32)(256 + j)`; `pc:num`; `read X30 s`]
   [`pc:num`; `v:int64`; `stackpointer:int64`;
    `returnaddress:int64`] 7 THEN
  ARM_STEPS_TAC MLDSA_NATIVE_POLYVECK_NTT_44_GCC12_O2_EXEC (8--9) THEN
  FULL_CALL_TAC mldsa_native_libmldsa_gcc12_O2_mc
   MLDSA_NATIVE_POLYVECK_NTT_44_GCC12_O2_EXEC "H_POLY"
   [`read X0 s`; `\j. (x:num->int32)(512 + j)`; `pc:num`; `read X30 s`]
   [`pc:num`; `v:int64`; `stackpointer:int64`;
    `returnaddress:int64`] 10 THEN
  ARM_STEPS_TAC MLDSA_NATIVE_POLYVECK_NTT_44_GCC12_O2_EXEC (11--13) THEN
  FULL_CALL_TAC mldsa_native_libmldsa_gcc12_O2_mc
   MLDSA_NATIVE_POLYVECK_NTT_44_GCC12_O2_EXEC "H_POLY"
   [`read X0 s`; `\j. (x:num->int32)(768 + j)`; `pc:num`; `read X30 s`]
   [`pc:num`; `v:int64`; `stackpointer:int64`;
    `returnaddress:int64`] 14 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [VEC_UNROLL_JOIN_TAC 256 4 []; DISCHARGE_SAFETY_PROPERTY_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVECK_NTT_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_POLYVECK_NTT_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  CORRECT_OF_FULL_TAC
    MLDSA_NATIVE_POLYVECK_NTT_44_GCC12_O2_IMAGE_SUBROUTINE_FULL);;

let MLDSA_NATIVE_POLYVECK_NTT_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE = prove
 (MLDSA_NATIVE_POLYVECK_NTT_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  SAFE_OF_FULL_TAC
    MLDSA_NATIVE_POLYVECK_NTT_44_GCC12_O2_IMAGE_SUBROUTINE_FULL);;
