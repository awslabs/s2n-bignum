(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The kernel compress_d11_x86 as the build asm_avx512 uses it: the          *)
(* definitions, tactics and theorems of its standalone proof                 *)
(* x86/proofs/mlkem_compress_d11_x86.ml, loaded with every proof assumed     *)
(* (see common/relative.ml), so that the callers use them as contracts.      *)
(* compress_d11_x86_proof.ml loads that file again and proves them.          *)
(* ========================================================================= *)

needs "x86/proofs/mlkem_native/relative.ml";;
needs "x86/proofs/base.ml";;
needs "x86/proofs/utils/mlkem_codec_utils.ml";;
needs "x86/proofs/utils/mlkem_compress_common.ml";;
needs "x86/proofs/utils/mlkem_compress_consts.ml";;
needs "x86/proofs/subroutine_signatures.ml";;

(relative_assuming ()) := true;;
loadt "x86/proofs/mlkem_compress_d11_x86.ml";;
(relative_assuming ()) := false;;
