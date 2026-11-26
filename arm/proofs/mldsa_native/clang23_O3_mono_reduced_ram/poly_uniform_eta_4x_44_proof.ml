(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Sampling of four polynomials with coefficients in [-2,2] for ML-DSA-44:   *)
(* the proof (see poly_uniform_eta_4x_44_spec.ml). The region lemmas of      *)
(* inline_eta4x.ml (the absorbing, the eight scan loops, the guarded scans   *)
(* and the tests) are proved for the code of mldsa44_poly_uniform_eta_4x,    *)
(* then composed by the main lemma and the top level of                      *)
(* inline_eta4x_main.ml.                                                     *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/poly_uniform_eta_4x_44_spec.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_eta4x.ml";;

let EM_EXEC = MLDSA_NATIVE_POLY_UNIFORM_ETA_4X_44_CLANG23_O3_MONO_REDUCED_RAM_EXEC;;
let EM_B = 0x38d28;;
let EM_L = ETA2_PROVE_ALL EM_EXEC EM_B;;
let EM_P = ETA2_MAIN_PAR;;

loadt "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_eta4x_main.ml";;

let ETA44_MAIN = prove(ETA_MAIN_TM EM_B 2, EM_MAIN_TAC);;

let MLDSA_NATIVE_POLY_UNIFORM_ETA_4X_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_POLY_UNIFORM_ETA_4X_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT,
  ETA_TOP_TAC EM_EXEC ETA44_MAIN);;

let MLDSA_NATIVE_POLY_UNIFORM_ETA_4X_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_POLY_UNIFORM_ETA_4X_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> CORRECT_OF_FULL_TAC
    (MP (SPEC_ALL MLDSA_NATIVE_POLY_UNIFORM_ETA_4X_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL)
        th)));;

let MLDSA_NATIVE_POLY_UNIFORM_ETA_4X_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE = prove
 (MLDSA_NATIVE_POLY_UNIFORM_ETA_4X_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> SAFE_OF_FULL_TAC
    (MP (SPEC_ALL MLDSA_NATIVE_POLY_UNIFORM_ETA_4X_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL)
        th)));;
