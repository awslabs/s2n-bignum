(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The lemmas for the regions that clang 23 inlines into                     *)
(* mldsa87_keypair_internal, instantiated from the generators of             *)
(* inline_keypair.ml: the SHAKE256 of the seed (SEED), the fifteen packings  *)
(* of s2 and s1 into the secret key (PACK1, in the form PACK2B, and PACK2 to *)
(* PACK15) and the SHAKE256 of the public key (HASH).                        *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/keypair_internal_87_spec.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_keypair.ml";;

let KP87 = "mldsa87_keypair_internal";;
let KP87_FB = layout KP87;;

let KP87_SEED = PROVE_KPSEED (KP87_FB + 0x2a) (KP87_FB + 0x22b) 8 7 "R15";;

(*** The four samplings fill the polynomials at rsp0 + 0x1e0 + 1024 n: s2 4
     to 7 (nonces 11 to 14) and 0 to 3 (nonces 7 to 10) into sk + 800 +
     96 n, s1 4 to 6 (nonces 4 to 6, in the polynomials 4 to 6) and 0 to 3
     into sk + 128 + 96 n. The instances use R12, R13 or R15 besides the
     fixed registers. ***)

let KP87_PACKS =
  PROVE_KPPACK2B KP87 "loop1" "loop1_exit" 1184 480 ::
  map (fun (n,ob,d,t) ->
     PROVE_KPPACK2 KP87 ("loop"^string_of_int n) ("loop"^string_of_int n^"_exit") ob (ob + 2) d t)
   [2,1280,"R12","R13"; 3,1376,"R12","R13"; 4,1472,"R12","R13";
    5,800,"R12","R13"; 6,896,"R12","R13"; 7,992,"R12","R13"; 8,1088,"R12","R13";
    9,512,"R13","R12"; 10,608,"R12","R13"; 11,704,"R12","R13";
    12,128,"R15","R12"; 13,224,"R15","R12"; 14,320,"R15","R12"; 15,416,"R15","R12"];;

let KP87_HASH = PROVE_PKHASHB_R KP87 (KP87_FB + 0xff1) "after_mldsa_keccakf1600_permute_21"
  16 "R14" "R13" 2592 516 516 0;;
