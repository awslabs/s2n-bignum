(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Loader for FIPS 197 AES definitions and KATs.                             *)
(*                                                                           *)
(* This file exists so that build-proof.sh can validate common/fips197.ml    *)
(* via the standard `make proofs/fips197.correct` flow. It will also serve   *)
(* as the bridge for proving equivalence between the FIPS 197 definitions    *)
(* and the hardware-oriented AES model used in the x86 proofs.              *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;
needs "common/fips197.ml";;
