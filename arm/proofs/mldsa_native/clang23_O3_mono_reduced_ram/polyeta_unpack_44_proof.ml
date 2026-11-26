(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Unpacking of a polynomial with 3 bits per coefficient, of 2 - a: the      *)
(* proof for ML-DSA-44 (see inline_polyeta.ml for the structure of the proof *)
(* and polyeta_unpack_44_spec.ml for the code). The scalar loop is proved as *)
(* a lemma for 16 iterations (after the vector block) and for 32 (when the   *)
(* buffers overlap), and called from the proof of the function.              *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/polyeta_unpack_44_spec.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_polyeta.ml";;

let ETA44_LOOP2_16 = prove(ETA_L2_TM "mldsa44" 16,
  ETA_L2_TAC "mldsa44" MLDSA_NATIVE_POLYETA_UNPACK_44_CLANG23_O3_MONO_REDUCED_RAM_EXEC 16);;

let ETA44_LOOP2_32 = prove(ETA_L2_TM "mldsa44" 32,
  ETA_L2_TAC "mldsa44" MLDSA_NATIVE_POLYETA_UNPACK_44_CLANG23_O3_MONO_REDUCED_RAM_EXEC 32);;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety.                             *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYETA_UNPACK_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_POLYETA_UNPACK_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT,
  ETA_FULL_TAC "mldsa44" MLDSA_NATIVE_POLYETA_UNPACK_44_CLANG23_O3_MONO_REDUCED_RAM_EXEC
    ETA44_LOOP2_16 ETA44_LOOP2_32);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYETA_UNPACK_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_POLYETA_UNPACK_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT,
  CORRECT_OF_FULL_TAC
    MLDSA_NATIVE_POLYETA_UNPACK_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL);;

let MLDSA_NATIVE_POLYETA_UNPACK_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE = prove
 (MLDSA_NATIVE_POLYETA_UNPACK_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT,
  SAFE_OF_FULL_TAC
    MLDSA_NATIVE_POLYETA_UNPACK_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL);;
