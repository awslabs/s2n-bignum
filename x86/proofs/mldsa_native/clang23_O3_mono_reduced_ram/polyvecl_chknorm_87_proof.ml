(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Norm check of a vector of 7 polynomials: the proof (see                   *)
(* polyvecl_chknorm_87_spec.ml). The tools are in chknorm_tools.ml.          *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/polyvecl_chknorm_87_spec.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/chknorm_tools.ml";;

let CHK87_CFG =
 { chk_l = 7; chk_acc = ["RCX"; "RDX"; "R8"; "R9"; "R10"; "R11"; "RAX"];
   chk_idx = ["RAX"; "RAX"; "RAX"; "RAX"; "RAX"; "RAX"; "RBX"];
   chk_mids = [3; 3; 3; 7; 3; 3; 3]; chk_push = 3; chk_pushed = ["RBP"; "R15"; "R14"; "RBX"];
   chk_ret = 19; chk_name = "mldsa87_polyvecl_chknorm";
   chk_exec = MLDSA_NATIVE_POLYVECL_CHKNORM_87_CLANG23_O3_MONO_REDUCED_RAM_EXEC;
   chk_lowreg = (fun r -> String.lowercase_ascii r) };;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together. The events are     *)
(* those of the 7 loops, with those of the code before each loop and after   *)
(* the last.                                                                 *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVECL_CHKNORM_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_POLYVECL_CHKNORM_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT,
  chk_full_tac CHK87_CFG);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVECL_CHKNORM_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_POLYVECL_CHKNORM_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT,
  CORRECT_OF_FULL_TAC
    MLDSA_NATIVE_POLYVECL_CHKNORM_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL);;

let MLDSA_NATIVE_POLYVECL_CHKNORM_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE = prove
 (MLDSA_NATIVE_POLYVECL_CHKNORM_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT,
  SAFE_OF_FULL_TAC
    MLDSA_NATIVE_POLYVECL_CHKNORM_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL);;
