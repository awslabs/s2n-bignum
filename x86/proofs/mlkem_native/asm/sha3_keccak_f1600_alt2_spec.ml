(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The kernel sha3_keccak_f1600_alt2 as the build asm uses it: the           *)
(* definitions, tactics and theorems of its standalone proof                 *)
(* x86/proofs/sha3_keccak_f1600_alt2.ml, loaded with every proof assumed     *)
(* (see common/relative.ml), so that the callers use them as contracts.      *)
(* sha3_keccak_f1600_alt2_proof.ml loads that file again and proves them.    *)
(* ========================================================================= *)

needs "x86/proofs/mlkem_native/relative.ml";;
needs "x86/proofs/base.ml";;
needs "x86/proofs/utils/keccak_spec.ml";;
needs "x86/proofs/utils/keccak_avx2.ml";;
needs "x86/proofs/consttime.ml";;
needs "x86/proofs/subroutine_signatures.ml";;

(relative_assuming ()) := true;;
loadt "x86/proofs/sha3_keccak_f1600_alt2.ml";;
(relative_assuming ()) := false;;
