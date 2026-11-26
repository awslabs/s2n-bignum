(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The inlined code of mldsa44_keypair_internal in the clang 23 -O3          *)
(* monolithic reduced-RAM build, as lemmas for the proof of its statement:  *)
(* the SHAKE256 of the seed (KI_SEED_PROVE), the eight packings of the       *)
(* polynomials of s2 and s1 into the secret key (KP44_PACK) and the SHAKE256 *)
(* of the public key (KG_SHAKE_PROVE), all of inline_keypair.ml.             *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_keypair.ml";;

let KI44_SEED = KI_SEED_PROVE KS44;;

let KI44_PACK_THS = map KP44_PACK (0--7);;

let KI44_SHAKE = KG_SHAKE_PROVE KI_SHAKE44_INST "X20";;
