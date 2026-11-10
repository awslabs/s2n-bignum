(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Uniform sampling of the vector y for ML-DSA-65: the proof (see            *)
(* polyvecl_uniform_gamma1_65_spec.ml), a straight-line simulation with the  *)
(* FULL theorems of mldsa65_poly_uniform_gamma1_4x for the first four        *)
(* polynomials and of mldsa65_poly_uniform_gamma1 for the fifth, in the tail *)
(* call (a JMP after the POPs).                                              *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/gcc12_O2/polyvecl_uniform_gamma1_65_spec.ml";;
needs "x86/proofs/utils/mldsa_native_sampling.ml";;
needs "x86/proofs/utils/mldsa_native_polyvec.ml";;

let POLYVECL_UNIFORM_GAMMA1_65_EXEC =
  MLDSA_NATIVE_POLYVECL_UNIFORM_GAMMA1_65_GCC12_O2_EXEC;;

let POLYVECL_UNIFORM_GAMMA1_65_ALLOWED =
  [`pc:num`; `v:int64`; `seed:int64`; `stackpointer:int64`;
   `returnaddress:int64`];;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together. The nonces are     *)
(* rewritten as word_add (word_zx kappa) (word k) with SAMPLING_NONCE16_TAC, *)
(* as in the statement, before the vector is put together from the           *)
(* polynomials (VEC_UNROLL_JOIN_TAC).                                        *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVECL_UNIFORM_GAMMA1_65_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  prove
 (MLDSA_NATIVE_POLYVECL_UNIFORM_GAMMA1_65_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT,
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_POLY_UNIFORM_GAMMA1_4X_65_GCC12_O2_IMAGE_SUBROUTINE_FULL
    "H_4X" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_POLY_UNIFORM_GAMMA1_65_GCC12_O2_IMAGE_SUBROUTINE_FULL
    "H_G1" THEN
  META_EXISTS_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst POLYVECL_UNIFORM_GAMMA1_65_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_PRESERVED_TAC "rbx_init" `RBX` THEN
  ENSURES_PRESERVED_TAC "rbp_init" `RBP` THEN
  ENSURES_PRESERVED_TAC "r12_init" `R12` THEN
  FULL_INIT_TAC THEN

  (*** The first four polynomials, the last three nonces on the stack ***)

  X86_STEPS_TAC POLYVECL_UNIFORM_GAMMA1_65_EXEC (1--22) THEN
  FULL_CALL_TAC mldsa_native_libmldsa_gcc12_O2_mc
   POLYVECL_UNIFORM_GAMMA1_65_EXEC "H_4X"
   [`read RDI s`; `read RSI s`; `read RDX s`; `read RCX s`; `read R8 s`;
    `sd:num`; `read R9 s`;
    `read (memory :> bytes64 (word_add (read RSP s) (word 8))) s`;
    `read (memory :> bytes64 (word_add (read RSP s) (word 16))) s`;
    `read (memory :> bytes64 (word_add (read RSP s) (word 24))) s`;
    `pc:num`; `read RSP s`; `read (memory :> bytes64 (read RSP s)) s`]
   POLYVECL_UNIFORM_GAMMA1_65_ALLOWED 23 THEN
  SAMPLING_NONCE16_TAC `kappa:int64` THEN

  (*** The fifth in the tail call ***)

  X86_STEPS_TAC POLYVECL_UNIFORM_GAMMA1_65_EXEC (24--32) THEN
  FULL_CALL_TAC mldsa_native_libmldsa_gcc12_O2_mc
   POLYVECL_UNIFORM_GAMMA1_65_EXEC "H_G1"
   [`read RDI s`; `read RSI s`; `sd:num`; `read RDX s`;
    `pc:num`; `read RSP s`; `read (memory :> bytes64 (read RSP s)) s`]
   POLYVECL_UNIFORM_GAMMA1_65_ALLOWED 33 THEN
  SAMPLING_NONCE16_TAC `kappa:int64` THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [VEC_UNROLL_JOIN_TAC 256 5 [MLD_POLYVEC_COEFF];
    DISCHARGE_SAFETY_PROPERTY_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVECL_UNIFORM_GAMMA1_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  prove
(MLDSA_NATIVE_POLYVECL_UNIFORM_GAMMA1_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  CORRECT_OF_FULL_TAC
    MLDSA_NATIVE_POLYVECL_UNIFORM_GAMMA1_65_GCC12_O2_IMAGE_SUBROUTINE_FULL);;

let MLDSA_NATIVE_POLYVECL_UNIFORM_GAMMA1_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  prove
 (MLDSA_NATIVE_POLYVECL_UNIFORM_GAMMA1_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  SAFE_OF_FULL_TAC
    MLDSA_NATIVE_POLYVECL_UNIFORM_GAMMA1_65_GCC12_O2_IMAGE_SUBROUTINE_FULL);;
