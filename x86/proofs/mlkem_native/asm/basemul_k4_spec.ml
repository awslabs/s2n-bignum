(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The kernel basemul_k4 as the build asm uses it: the definitions,          *)
(* tactics and theorems of its standalone proof                              *)
(* x86/proofs/mlkem_basemul_k4.ml, loaded with every proof assumed (see      *)
(* common/relative.ml), so that the callers use them as contracts.           *)
(* basemul_k4_proof.ml loads that file again and proves them.                *)
(* ========================================================================= *)

needs "x86/proofs/mlkem_native/relative.ml";;
needs "x86/proofs/base.ml";;
needs "common/mlkem_mldsa.ml";;

(relative_assuming ()) := true;;
loadt "x86/proofs/mlkem_basemul_k4.ml";;
(relative_assuming ()) := false;;
