(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Unpacking the hints of a polynomial of a signature: the proof (see        *)
(* sig_unpack_hints_87_spec.ml).                                             *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/gcc12_O2/sig_unpack_hints_87_spec.ml";;
needs "x86/proofs/utils/mldsa_native_hints.ml";;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together, with one loop over *)
(* the iterations of both loops of the code, as GLUE_SUH_FULL_TAC of         *)
(* utils/mldsa_native_hints.ml does it, with the REP STOSQ of the memset of  *)
(* the coefficients that gcc inlines at offset 0x68. At the head of the      *)
(* first loop, rax is the position and rdx the address of its byte in the    *)
(* signature.                                                                *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SIG_UNPACK_HINTS_87_GCC12_O2_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_SIG_UNPACK_HINTS_87_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT,
  GLUE_SUH_FULL_TAC
   {suh_exec = MLDSA_NATIVE_SIG_UNPACK_HINTS_87_GCC12_O2_EXEC;
    suh_fn = "mldsa87_sig_unpack_hints";
    suh_omega = 75; suh_k = 8; suh_sigh = 4544; suh_stos = 0x68});;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SIG_UNPACK_HINTS_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_SIG_UNPACK_HINTS_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  CORRECT_OF_FULL_TAC
    MLDSA_NATIVE_SIG_UNPACK_HINTS_87_GCC12_O2_IMAGE_SUBROUTINE_FULL);;

let MLDSA_NATIVE_SIG_UNPACK_HINTS_87_GCC12_O2_IMAGE_SUBROUTINE_SAFE = prove
 (MLDSA_NATIVE_SIG_UNPACK_HINTS_87_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  SAFE_OF_FULL_TAC
    MLDSA_NATIVE_SIG_UNPACK_HINTS_87_GCC12_O2_IMAGE_SUBROUTINE_FULL);;
