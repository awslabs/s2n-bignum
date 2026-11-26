(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* polyw1_pack_88 as clang 23 -O3 has inlined it into the row loop of        *)
(* mldsa44_verify_internal: the theorem INLINE_W1PACK44 of the statement and *)
(* the proof in inline_sign_w1pack_tac.ml (about 12 minutes).                *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_sign_w1pack_tac.ml";;

let INLINE_W1PACK44 = INLINE_W1PACK44_PROVE INLINE_W1PACK44_TERM;;
