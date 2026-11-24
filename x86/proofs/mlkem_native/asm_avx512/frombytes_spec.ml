(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The kernel frombytes as the build asm_avx512 uses it: the definitions,    *)
(* tactics and theorems of its standalone proof                              *)
(* x86/proofs/mlkem_frombytes.ml, loaded with every proof assumed (see       *)
(* common/relative.ml), so that the callers use them as contracts.           *)
(* frombytes_proof.ml loads that file again and proves them.                 *)
(* ========================================================================= *)

needs "x86/proofs/mlkem_native/relative.ml";;
needs "x86/proofs/base.ml";;
needs "common/mlkem_mldsa.ml";;

(relative_assuming ()) := true;;
loadt "x86/proofs/mlkem_frombytes.ml";;
(relative_assuming ()) := false;;
