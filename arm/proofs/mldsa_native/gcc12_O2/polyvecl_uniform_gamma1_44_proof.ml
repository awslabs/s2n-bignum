(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Uniform sampling of the vector y for ML-DSA-44: the proof (see            *)
(* polyvecl_uniform_gamma1_44_spec.ml), a straight-line simulation with the  *)
(* FULL theorem of mldsa44_poly_uniform_gamma1_4x, whose four polynomials    *)
(* make the vector.                                                          *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/gcc12_O2/polyvecl_uniform_gamma1_44_spec.ml";;
needs "arm/proofs/utils/mldsa_native_sampling.ml";;
needs "arm/proofs/utils/mldsa_native_polyvec.ml";;

let POLYVECL_UNIFORM_GAMMA1_44_EXEC =
  MLDSA_NATIVE_POLYVECL_UNIFORM_GAMMA1_44_GCC12_O2_EXEC;;

let POLYVECL_UNIFORM_GAMMA1_44_ALLOWED =
  [`pc:num`; `v:int64`; `seed:int64`; `guard:int64`; `mf:int64`;
   `stackpointer:int64`; `returnaddress:int64`];;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together. The nonces are     *)
(* rewritten as word_add (word_zx kappa) (word k) with                       *)
(* SAMPLING_NONCE16_RULE, as in the statement, before the vector is put      *)
(* together from the polynomials (VEC_UNROLL_JOIN_TAC).                      *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVECL_UNIFORM_GAMMA1_44_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  prove
 (MLDSA_NATIVE_POLYVECL_UNIFORM_GAMMA1_44_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(fun th ->
    ASSUME_CALLEE_SAFETY_TAILED_TAC
     (MATCH_MP
       MLDSA_NATIVE_POLY_UNIFORM_GAMMA1_4X_44_GCC12_O2_IMAGE_SUBROUTINE_FULL th)
     "H_4X") THEN
  META_EXISTS_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst POLYVECL_UNIFORM_GAMMA1_44_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `aligned 16 (stackpointer:int64)` ASSUME_TAC THENL
   [UNDISCH_TAC `aligned 16 (word_add stackpointer (word 4496):int64)` THEN
    CONV_TAC(LAND_CONV NORMALIZE_ALIGNED_WORD_CONV) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  ENSURES_INIT_TAC "s0" THEN

  (*** The four polynomials, the fourth nonce on the stack ***)

  ARM_STEPS_TAC POLYVECL_UNIFORM_GAMMA1_44_EXEC (1--13) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SAMPLING_NONCE16_RULE 3]) THEN
  FULL_CALL_TAC mldsa_native_libmldsa_gcc12_O2_mc
   POLYVECL_UNIFORM_GAMMA1_44_EXEC "H_4X"
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X3 s`; `read X4 s`;
    `sd:num`; `read X5 s`; `read X6 s`; `read X7 s`;
    `word_add (word_zx (kappa:int64)) (word 3):int16`;
    `guard:int64`; `pc:num`; `read SP s`; `read X30 s`]
   POLYVECL_UNIFORM_GAMMA1_44_ALLOWED 14 THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [SAMPLING_NONCE16_0; SAMPLING_NONCE16_RULE 1; SAMPLING_NONCE16_RULE 2]) THEN
  ARM_STEPS_TAC POLYVECL_UNIFORM_GAMMA1_44_EXEC (15--17) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [VEC_UNROLL_JOIN_TAC 256 4 [MLD_POLYVEC_COEFF];
    DISCHARGE_SAFETY_PROPERTY_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVECL_UNIFORM_GAMMA1_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  prove
 (MLDSA_NATIVE_POLYVECL_UNIFORM_GAMMA1_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> CORRECT_OF_FULL_TAC
    (MP (SPEC_ALL
     MLDSA_NATIVE_POLYVECL_UNIFORM_GAMMA1_44_GCC12_O2_IMAGE_SUBROUTINE_FULL)
        th)));;

let MLDSA_NATIVE_POLYVECL_UNIFORM_GAMMA1_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  prove
 (MLDSA_NATIVE_POLYVECL_UNIFORM_GAMMA1_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> SAFE_OF_FULL_TAC
    (MP (SPEC_ALL
     MLDSA_NATIVE_POLYVECL_UNIFORM_GAMMA1_44_GCC12_O2_IMAGE_SUBROUTINE_FULL)
        th)));;
