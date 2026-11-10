(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Uniform sampling of the vector y for ML-DSA-87: the proof (see            *)
(* polyvecl_uniform_gamma1_87_spec.ml), a straight-line simulation with the  *)
(* FULL theorem of mldsa87_poly_uniform_gamma1_4x for its two calls; the     *)
(* second overwrites polynomial 3, which the first also writes.              *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/gcc12_O2/polyvecl_uniform_gamma1_87_spec.ml";;
needs "x86/proofs/utils/mldsa_native_sampling.ml";;
needs "x86/proofs/utils/mldsa_native_polyvec.ml";;

let POLYVECL_UNIFORM_GAMMA1_87_EXEC =
  MLDSA_NATIVE_POLYVECL_UNIFORM_GAMMA1_87_GCC12_O2_EXEC;;

let POLYVECL_UNIFORM_GAMMA1_87_ALLOWED =
  [`pc:num`; `v:int64`; `seed:int64`; `stackpointer:int64`;
   `returnaddress:int64`];;

let POLYVECL_UNIFORM_GAMMA1_87_CALL_TAC n =
  FULL_CALL_TAC mldsa_native_libmldsa_gcc12_O2_mc
   POLYVECL_UNIFORM_GAMMA1_87_EXEC "H_4X"
   [`read RDI s`; `read RSI s`; `read RDX s`; `read RCX s`; `read R8 s`;
    `sd:num`; `read R9 s`;
    `read (memory :> bytes64 (word_add (read RSP s) (word 8))) s`;
    `read (memory :> bytes64 (word_add (read RSP s) (word 16))) s`;
    `read (memory :> bytes64 (word_add (read RSP s) (word 24))) s`;
    `pc:num`; `read RSP s`; `read (memory :> bytes64 (read RSP s)) s`]
   POLYVECL_UNIFORM_GAMMA1_87_ALLOWED n;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together. The nonces are     *)
(* rewritten as word_add (word_zx kappa) (word k) with SAMPLING_NONCE16_TAC, *)
(* as in the statement, before the vector is put together from the           *)
(* polynomials (VEC_UNROLL_JOIN_TAC).                                        *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVECL_UNIFORM_GAMMA1_87_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  prove
 (MLDSA_NATIVE_POLYVECL_UNIFORM_GAMMA1_87_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT,
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_POLY_UNIFORM_GAMMA1_4X_87_GCC12_O2_IMAGE_SUBROUTINE_FULL
    "H_4X" THEN
  META_EXISTS_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst POLYVECL_UNIFORM_GAMMA1_87_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_PRESERVED_TAC "rbx_init" `RBX` THEN
  ENSURES_PRESERVED_TAC "rbp_init" `RBP` THEN
  ENSURES_PRESERVED_TAC "r12_init" `R12` THEN
  ENSURES_PRESERVED_TAC "r13_init" `R13` THEN
  FULL_INIT_TAC THEN

  (*** Polynomials 0 to 2, and 3 with the nonce 255 ***)

  X86_STEPS_TAC POLYVECL_UNIFORM_GAMMA1_87_EXEC (1--22) THEN
  POLYVECL_UNIFORM_GAMMA1_87_CALL_TAC 23 THEN
  SAMPLING_NONCE16_TAC `kappa:int64` THEN

  (*** Polynomials 3 to 6 ***)

  X86_STEPS_TAC POLYVECL_UNIFORM_GAMMA1_87_EXEC (24--41) THEN
  POLYVECL_UNIFORM_GAMMA1_87_CALL_TAC 42 THEN
  SAMPLING_NONCE16_TAC `kappa:int64` THEN
  X86_STEPS_TAC POLYVECL_UNIFORM_GAMMA1_87_EXEC (43--48) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [VEC_UNROLL_JOIN_TAC 256 7 [MLD_POLYVEC_COEFF];
    DISCHARGE_SAFETY_PROPERTY_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVECL_UNIFORM_GAMMA1_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  prove
(MLDSA_NATIVE_POLYVECL_UNIFORM_GAMMA1_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  CORRECT_OF_FULL_TAC
    MLDSA_NATIVE_POLYVECL_UNIFORM_GAMMA1_87_GCC12_O2_IMAGE_SUBROUTINE_FULL);;

let MLDSA_NATIVE_POLYVECL_UNIFORM_GAMMA1_87_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  prove
 (MLDSA_NATIVE_POLYVECL_UNIFORM_GAMMA1_87_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  SAFE_OF_FULL_TAC
    MLDSA_NATIVE_POLYVECL_UNIFORM_GAMMA1_87_GCC12_O2_IMAGE_SUBROUTINE_FULL);;
