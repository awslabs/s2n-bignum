(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The lemmas for the regions that clang 23 inlines into                     *)
(* mldsa44_keypair_internal, instantiated from the generators of             *)
(* inline_keypair.ml: the SHAKE256 of the seed (SEED), the eight packings of *)
(* s2 and s1 into the secret key (PACK1 to PACK8) and the SHAKE256 of the    *)
(* public key (HASH).                                                        *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/keypair_internal_44_spec.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_keypair.ml";;

let KP44 = "mldsa44_keypair_internal";;
let KP44_FB = layout KP44;;

let KP44_SEED = PROVE_KPSEED (KP44_FB + 0x2a) (KP44_FB + 0x22b) 4 4 "R12";;

(*** s2 (nonces 4 to 7) at sk + 512 and s1 (nonces 0 to 3) at sk + 128, from
     the four polynomials at rsp0 + 0x1e0 + 1024 n; the instances use R13 or
     R15 and R15, R13 or R12 besides the fixed registers ***)

let KP44_PACKS = map (fun (n,ob,d,t) ->
   PROVE_KPPACK2 KP44 ("loop"^string_of_int n) ("loop"^string_of_int n^"_exit") ob (ob + 2) d t)
  [1,512,"R13","R15"; 2,608,"R15","R13"; 3,704,"R15","R13"; 4,800,"R15","R13";
   5,128,"R15","R12"; 6,224,"R15","R12"; 7,320,"R15","R12"; 8,416,"R15","R12"];;

let KP44_HASH = PROVE_PKHASHB_R KP44 (KP44_FB + 0x985) "after_mldsa_keccakf1600_permute_11"
  16 "R14" "R13" 1312 516 516 0;;
