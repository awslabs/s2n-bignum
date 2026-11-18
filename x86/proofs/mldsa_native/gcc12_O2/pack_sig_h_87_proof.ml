(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Packing the hints of a signature: the proof (see pack_sig_h_87_spec.ml).  *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/gcc12_O2/pack_sig_h_87_spec.ml";;
needs "x86/proofs/utils/mldsa_native_hints.ml";;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together, with one loop over *)
(* the 2048 positions of the vector, as GLUE_PSH_FULL_TAC of                 *)
(* utils/mldsa_native_hints.ml does it, with the REP STOSQ of the memset of  *)
(* the hints that gcc inlines at offset 0x53.                                *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_PACK_SIG_H_87_GCC12_O2_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_PACK_SIG_H_87_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT,
  GLUE_PSH_FULL_TAC
   {psh_exec = MLDSA_NATIVE_PACK_SIG_H_87_GCC12_O2_EXEC;
    psh_fn = "mldsa87_pack_sig_h";
    psh_callee = "mldsa_polyw1_unpack_32";
    psh_hintf = `mld_polyvec_make_hint_32`;
    psh_inrf = `glue_hint_inr_32`;
    psh_unpackf = `mld_polyw1_unpack_32`;
    psh_inr_val = GLUE_INR_32;
    psh_inr = GLUE_HINT_INR_32;
    psh_out = GLUE_HINT_OUT_32;
    psh_unfold = GLUE_POLYVEC_HINT_32;
    psh_omega = 75; psh_k = 8; psh_wbytes = 128; psh_sigh = 4544;
    psh_gamma = 261888; psh_stos = 0x53}
   MLDSA_NATIVE_POLYW1_UNPACK_32_GCC12_O2_IMAGE_SUBROUTINE_FULL);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_PACK_SIG_H_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_PACK_SIG_H_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  CORRECT_OF_FULL_TAC
    MLDSA_NATIVE_PACK_SIG_H_87_GCC12_O2_IMAGE_SUBROUTINE_FULL);;

let MLDSA_NATIVE_PACK_SIG_H_87_GCC12_O2_IMAGE_SUBROUTINE_SAFE = prove
 (MLDSA_NATIVE_PACK_SIG_H_87_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  SAFE_OF_FULL_TAC
    MLDSA_NATIVE_PACK_SIG_H_87_GCC12_O2_IMAGE_SUBROUTINE_FULL);;
