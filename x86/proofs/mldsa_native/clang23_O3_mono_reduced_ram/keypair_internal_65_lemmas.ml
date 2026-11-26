(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The lemmas for the regions that clang 23 inlines into                     *)
(* mldsa65_keypair_internal, instantiated from the generators of             *)
(* inline_keypair.ml: the SHAKE256 of the seed (SEED) and the SHAKE256 of    *)
(* the public key (HASH, whose last block of 48 bytes the code XORs in as    *)
(* three 16-byte chunks), and from inline_keypair_pack4.ml the eleven        *)
(* vectorised packings of s2 and s1 with eta = 4 into the secret key         *)
(* (PACK1 to PACK11).                                                        *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/keypair_internal_65_spec.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_keypair.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_keypair_pack4.ml";;

let KP65 = "mldsa65_keypair_internal";;
let KP65_FB = layout KP65;;

let KP65_SEED = PROVE_KPSEED (KP65_FB + 0x2a) (KP65_FB + 0x241) 6 5 "R15";;

let KP65_HASH = PROVE_PKHASHB_R KP65 (KP65_FB + 0x1188) "after_mldsa_keccakf1600_permute_16"
  16 "R14" "R13" 1952 516 516 3;;

(*** The three samplings fill the polynomials at rsp0 + 0x1e0 + 1024 n: s2 2
     to 5 (nonces 7 to 10) in the polynomials 0 to 3, packed into sk + 1024
     + 128 m; s1 4 and s2 0 and 1 (nonces 4 to 6, and 255 in vain) in the
     polynomials 4, 0 and 1, packed into sk + 640, sk + 768 and sk + 896;
     s1 0 to 3 (nonces 0 to 3) in the polynomials 0 to 3, packed into sk +
     128 + 128 n. Each instance is given by its loop, the start a0 of RAX,
     the displacement dl of the loads and ds of the stores. ***)

let KP65_PACKS =
  map (fun (n,a0,dl,ds) ->
     PROVE_KPPACK4 KP65 ("loop"^string_of_int n) ("loop"^string_of_int n^"_exit") a0 dl ds)
   [1,0,0x1e0,0x400; 2,0x480,-0x1e20,0; 3,0x500,-0x1e20,0; 4,0x580,-0x1e20,0;
    5,0x200,0x1e0,0x80; 6,0,0x1e0,0x300; 7,0x380,-0x1620,0;
    8,4,0x1c0,0x7c; 9,0x80,0x1e0,0x80; 10,0x100,0x1e0,0x80; 11,0x180,0x1e0,0x80];;
