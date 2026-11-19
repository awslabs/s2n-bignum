(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Unpacking the hints of a polynomial of a signature: the proof (see        *)
(* sig_unpack_hints_87_spec.ml).                                             *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/gcc12_Os/sig_unpack_hints_87_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/sig_unpack_hints_os.ml";;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together, with one loop over *)
(* the iterations of both loops of the code, as GLUE_SUH_FULL_TAC_OS of      *)
(* sig_unpack_hints_os.ml does it. At the head of the first loop, x1 is the  *)
(* address of the byte of the hints at the position and w2 the position.     *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SIG_UNPACK_HINTS_87_GCC12_OS_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_SIG_UNPACK_HINTS_87_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT,
  GLUE_SUH_FULL_TAC_OS
   {suhos_exec = MLDSA_NATIVE_SIG_UNPACK_HINTS_87_GCC12_OS_EXEC;
    suhos_fn = "mldsa87_sig_unpack_hints";
    suhos_omega = 75; suhos_k = 8; suhos_sigh = 4544;
    suhos_l1 = 0xc8; suhos_l2 = 0x9c; suhos_ret = 0x44;
    suhos_regs1 =
     `read X1 s = word_add sig (word(SH + j)) /\ read X2 s = word j`});;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SIG_UNPACK_HINTS_87_GCC12_OS_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_SIG_UNPACK_HINTS_87_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> CORRECT_OF_FULL_TAC
    (MP (SPEC_ALL
       MLDSA_NATIVE_SIG_UNPACK_HINTS_87_GCC12_OS_IMAGE_SUBROUTINE_FULL) th)));;

let MLDSA_NATIVE_SIG_UNPACK_HINTS_87_GCC12_OS_IMAGE_SUBROUTINE_SAFE = prove
 (MLDSA_NATIVE_SIG_UNPACK_HINTS_87_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> SAFE_OF_FULL_TAC
    (MP (SPEC_ALL
       MLDSA_NATIVE_SIG_UNPACK_HINTS_87_GCC12_OS_IMAGE_SUBROUTINE_FULL) th)));;
