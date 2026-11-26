(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Sampling of four polynomials by rejection for ML-DSA-87: the proof (see   *)
(* poly_uniform_eta_4x_87_spec.ml), by PEM_FULL_TAC of inline_eta4x_top.ml   *)
(* with the region lemmas of poly_uniform_eta_4x_87_lemmas.ml.               *)
(* The code is the same as that of mldsa44_poly_uniform_eta_4x, so the       *)
(* tactic is the same as for it.                                             *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/poly_uniform_eta_4x_87_spec.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/poly_uniform_eta_4x_87_lemmas.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_eta4x_top.ml";;

let ETA87_P =
  { pnn = "87"; pfn = "mldsa87_poly_uniform_eta_4x"; peta = 2; pt0 = 136;
    pbufs = [0x4e0; 0x580; 0x620; 0x6c0]; pstack = 2295;
    pexec = MLDSA_NATIVE_POLY_UNIFORM_ETA_4X_87_CLANG23_O3_MONO_REDUCED_RAM_EXEC;
    pfull = MLDSA_NATIVE_POLY_UNIFORM_ETA_4X_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT;
    pabs = ETA87_ABS; pscans = fst(chop_list 4 ETA87_SCANS);
    pguards = ETA87_GUARDS;
    pa1 = "loop3_exit"; phead = "loop4"; pexit = "loop4_exit";
    pstreg = ["R13"; "R14"; "R15"; "R12"]; pmset = [800; 640; 384] };;

pem_exec () := ETA87_P.pexec;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together.                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_UNIFORM_ETA_4X_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_POLY_UNIFORM_ETA_4X_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT,
  PEM_FULL_TAC ETA87_P);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_UNIFORM_ETA_4X_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_POLY_UNIFORM_ETA_4X_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> CORRECT_OF_FULL_TAC
    (MP (SPEC_ALL MLDSA_NATIVE_POLY_UNIFORM_ETA_4X_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL) th)));;

let MLDSA_NATIVE_POLY_UNIFORM_ETA_4X_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE = prove
 (MLDSA_NATIVE_POLY_UNIFORM_ETA_4X_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> SAFE_OF_FULL_TAC
    (MP (SPEC_ALL MLDSA_NATIVE_POLY_UNIFORM_ETA_4X_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL) th)));;
