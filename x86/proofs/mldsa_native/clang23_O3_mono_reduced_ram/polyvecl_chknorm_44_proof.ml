(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Norm check of a vector of 4 polynomials: the proof (see                   *)
(* polyvecl_chknorm_44_spec.ml). The tools are in chknorm_tools.ml.          *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/polyvecl_chknorm_44_spec.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/chknorm_tools.ml";;

let CHK44_CFG =
 { chk_l = 4; chk_acc = ["RCX"; "RDX"; "R8"; "RAX"];
   chk_idx = ["RAX"; "RAX"; "RAX"; "R9"];
   chk_mids = [3; 3; 3; 4]; chk_push = 3; chk_pushed = ["RBX"];
   chk_ret = 13; chk_name = "mldsa44_polyvecl_chknorm";
   chk_exec = MLDSA_NATIVE_POLYVECL_CHKNORM_44_CLANG23_O3_MONO_REDUCED_RAM_EXEC;
   chk_lowreg = (fun r -> String.lowercase_ascii r) };;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together. The events are     *)
(* those of the 4 loops, with those of the code before each loop and after   *)
(* the last.                                                                 *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVECL_CHKNORM_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_POLYVECL_CHKNORM_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT,
  chk_full_tac CHK44_CFG);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVECL_CHKNORM_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_POLYVECL_CHKNORM_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT,
  CORRECT_OF_FULL_TAC
    MLDSA_NATIVE_POLYVECL_CHKNORM_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL);;

let MLDSA_NATIVE_POLYVECL_CHKNORM_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE = prove
 (MLDSA_NATIVE_POLYVECL_CHKNORM_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT,
  SAFE_OF_FULL_TAC
    MLDSA_NATIVE_POLYVECL_CHKNORM_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL);;
