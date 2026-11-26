(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The inlined code of mldsa87_keypair_internal in the clang 23 -O3          *)
(* monolithic reduced-RAM build, as lemmas for the proof of its statement:  *)
(* the SHAKE256 of the seed (KI_SEED_PROVE), the fifteen packings of the     *)
(* polynomials of s2 and s1 into the secret key (KP87_PACK) and the SHAKE256 *)
(* of the public key (KG_SHAKE_PROVE), all of inline_keypair.ml.             *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_keypair.ml";;

let KI87_SEED = KI_SEED_PROVE KS87;;

let KI87_PACK_THS = map KP87_PACK (0--14);;

let KI87_SHAKE = KG_SHAKE_PROVE KI_SHAKE87_INST "X20";;
