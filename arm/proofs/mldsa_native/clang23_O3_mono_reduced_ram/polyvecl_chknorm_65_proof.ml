(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Norm check of a vector of 5 polynomials: the proof (see                   *)
(* polyvecl_chknorm_65_spec.ml). The code is 5 loops, one per polynomial,    *)
(* that clang has inlined; each is a call of the lemma of inline_chknorm.ml  *)
(* for its registers.                                                        *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/polyvecl_chknorm_65_spec.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_chknorm.ml";;

let MLDSA_NATIVE_POLYVECL_CHKNORM_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_POLYVECL_CHKNORM_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT,
  CHKNORM_FULL_TAC mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
    MLDSA_NATIVE_POLYVECL_CHKNORM_65_CLANG23_O3_MONO_REDUCED_RAM_EXEC
    "mldsa65_polyvecl_chknorm" 5 16);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVECL_CHKNORM_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_POLYVECL_CHKNORM_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT,
  CORRECT_OF_FULL_TAC
    MLDSA_NATIVE_POLYVECL_CHKNORM_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL);;

let MLDSA_NATIVE_POLYVECL_CHKNORM_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE = prove
 (MLDSA_NATIVE_POLYVECL_CHKNORM_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT,
  SAFE_OF_FULL_TAC
    MLDSA_NATIVE_POLYVECL_CHKNORM_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL);;
