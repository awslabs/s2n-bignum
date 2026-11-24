(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The kernel check_encoding as the build asm_avx512 uses it: the            *)
(* definitions, tactics and theorems of its standalone proof                 *)
(* x86/proofs/mlkem_check_encoding.ml, loaded with every proof assumed       *)
(* (see common/relative.ml), so that the callers use them as contracts.      *)
(* check_encoding_proof.ml loads that file again and proves them.            *)
(* ========================================================================= *)

needs "x86/proofs/mlkem_native/relative.ml";;
needs "x86/proofs/base.ml";;
needs "common/mlkem_mldsa.ml";;
needs "x86/proofs/utils/mlkem_bytes.ml";;
needs "x86/proofs/utils/mlkem_lanes.ml";;
needs "x86/proofs/consttime.ml";;
needs "x86/proofs/subroutine_signatures.ml";;

(relative_assuming ()) := true;;
loadt "x86/proofs/mlkem_check_encoding.ml";;
(relative_assuming ()) := false;;
