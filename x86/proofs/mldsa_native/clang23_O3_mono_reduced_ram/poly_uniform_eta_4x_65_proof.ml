(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Sampling of four polynomials by rejection for ML-DSA-65: the proof (see   *)
(* poly_uniform_eta_4x_65_spec.ml), by PEM_FULL_TAC of inline_eta4x_top.ml   *)
(* with the region lemmas of poly_uniform_eta_4x_65_lemmas.ml.               *)
(* The code of mldsa65_poly_uniform_eta_4x differs from that of the eta = 2  *)
(* functions in the first pass, which squeezes two blocks of each stream     *)
(* (two rounds of four permutations and four memcpys, the second to the      *)
(* buffer + 136) and scans 272 bytes, and in its frame (2432 bytes).         *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/poly_uniform_eta_4x_65_spec.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/poly_uniform_eta_4x_65_lemmas.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_eta4x_top.ml";;

let ETA65_P =
  { pnn = "65"; pfn = "mldsa65_poly_uniform_eta_4x"; peta = 4; pt0 = 272;
    pbufs = [0x4e0; 0x600; 0x720; 0x840]; pstack = 2807;
    pexec = MLDSA_NATIVE_POLY_UNIFORM_ETA_4X_65_CLANG23_O3_MONO_REDUCED_RAM_EXEC;
    pfull = MLDSA_NATIVE_POLY_UNIFORM_ETA_4X_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT;
    pabs = ETA65_ABS; pscans = fst(chop_list 4 ETA65_SCANS);
    pguards = ETA65_GUARDS;
    pa1 = "loop3_exit"; phead = "join15"; pexit = "join29";
    pstreg = ["R12"; "R13"; "R14"; "R15"]; pmset = [800; 1152; 384] };;

pem_exec () := ETA65_P.pexec;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together.                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_UNIFORM_ETA_4X_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_POLY_UNIFORM_ETA_4X_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT,
  PEM_FULL_TAC ETA65_P);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_UNIFORM_ETA_4X_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_POLY_UNIFORM_ETA_4X_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> CORRECT_OF_FULL_TAC
    (MP (SPEC_ALL MLDSA_NATIVE_POLY_UNIFORM_ETA_4X_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL) th)));;

let MLDSA_NATIVE_POLY_UNIFORM_ETA_4X_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE = prove
 (MLDSA_NATIVE_POLY_UNIFORM_ETA_4X_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> SAFE_OF_FULL_TAC
    (MP (SPEC_ALL MLDSA_NATIVE_POLY_UNIFORM_ETA_4X_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL) th)));;
