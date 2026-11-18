(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Unpacking the hints of a polynomial of a signature: the proof (see        *)
(* sig_unpack_hints_44_spec.ml).                                             *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/gcc12_O2/sig_unpack_hints_44_spec.ml";;
needs "arm/proofs/utils/mldsa_native_hints.ml";;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together, with one loop over *)
(* the iterations of both loops of the code, as GLUE_SUH_FULL_TAC of         *)
(* utils/mldsa_native_hints.ml does it. At the head of the first loop, x3 is *)
(* the address of the signature plus the position and w1 the position.       *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SIG_UNPACK_HINTS_44_GCC12_O2_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_SIG_UNPACK_HINTS_44_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT,
  GLUE_SUH_FULL_TAC
   {suh_exec = MLDSA_NATIVE_SIG_UNPACK_HINTS_44_GCC12_O2_EXEC;
    suh_fn = "mldsa44_sig_unpack_hints";
    suh_omega = 80; suh_k = 4; suh_sigh = 2336;
    suh_regs1 = `read X3 s = word_add sig (word j) /\ read X1 s = word j`});;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SIG_UNPACK_HINTS_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_SIG_UNPACK_HINTS_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> CORRECT_OF_FULL_TAC
    (MP (SPEC_ALL
       MLDSA_NATIVE_SIG_UNPACK_HINTS_44_GCC12_O2_IMAGE_SUBROUTINE_FULL) th)));;

let MLDSA_NATIVE_SIG_UNPACK_HINTS_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE = prove
 (MLDSA_NATIVE_SIG_UNPACK_HINTS_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> SAFE_OF_FULL_TAC
    (MP (SPEC_ALL
       MLDSA_NATIVE_SIG_UNPACK_HINTS_44_GCC12_O2_IMAGE_SUBROUTINE_FULL) th)));;
