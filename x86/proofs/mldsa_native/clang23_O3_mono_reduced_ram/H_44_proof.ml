(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* SHAKE256 of up to three inputs: the proof (see H_44_spec.ml). Clang       *)
(* inlines the absorbs, the padding and the squeeze; the region lemmas of    *)
(* H_44_inline.ml (on inline_hxor.ml, inline_hphase.ml and                   *)
(* inline_hsqueeze.ml) are proved for mld_H44 and composed as in the gcc     *)
(* proof, which composes the calls of the shake256 functions.                *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/H_44_spec.ml";;
needs "x86/proofs/utils/mldsa_native_full.ml";;
needs "x86/proofs/utils/mldsa_native_hash.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/H_44_inline.ml";;

let H44_LEMMAS = H44_PROVE_ALL "mld_H44";;

let MLDSA_NATIVE_H_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_H_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT,
  H44_TOP_TAC MLDSA_NATIVE_H_44_CLANG23_O3_MONO_REDUCED_RAM_EXEC H44_LEMMAS);;

let MLDSA_NATIVE_H_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_H_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th ->
    CORRECT_OF_FULL_TAC
     (MP (SPEC_ALL MLDSA_NATIVE_H_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL) th)));;

let MLDSA_NATIVE_H_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE = prove
 (MLDSA_NATIVE_H_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th ->
    SAFE_OF_FULL_TAC
     (MP (SPEC_ALL MLDSA_NATIVE_H_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL) th)));;
