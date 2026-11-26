(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The lemmas for the loops and regions that clang 23 inlines into           *)
(* mldsa65_pk_from_sk, instantiated from the generators of inline_keygen.ml  *)
(* and inline_keygen_eta4.ml: the unpacking (eta = 4) of the five            *)
(* polynomials of s1 into the frame and of the six of s2 into one scratch    *)
(* buffer, the norm checks of s2 (the first two leave their result in RDI    *)
(* and R8, which the code then stores in slots of the frame), the comparison *)
(* of t0 with that of the secret key, the rest of the checks with the        *)
(* SHAKE256 of the public key (RED, HASHB and TRCB, composed into TAILB),    *)
(* and the end from join1 to the return (CL).                                *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/pk_from_sk_65_spec.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_keygen_eta4.ml";;

let PK65 = "mldsa65_pk_from_sk";;
let PK65_FB = layout PK65;;

(*** s1: polynomial n from sk + 128 + 128 n to rsp0 + 1472 + 1024 n ***)

let PK65_ETA1 = PROVE_PKETA4 PK65 "loop1" "loop1_exit" 0x80 0x0 0x5c0;;
let PK65_ETA2 = PROVE_PKETA4 PK65 "loop2" "loop2_exit" 0x80 0x80 0x5c0;;
let PK65_ETA3 = PROVE_PKETA4 PK65 "loop3" "loop3_exit" 0x80 0x100 0x5c0;;
let PK65_ETA4 = PROVE_PKETA4 PK65 "loop4" "loop4_exit" 0x80 0x180 0x5c0;;
let PK65_ETA5 = PROVE_PKETA4 PK65 "loop5" "loop5_exit" 0x80 0x200 0x5c0;;

(*** s2: polynomial n from sk + 768 + 128 n to rsp0 + 448, each followed by
     its norm check ***)

let PK65_ETA6 = PROVE_PKETA4 PK65 "loop6" "loop6_exit" 0x300 0x0 0x1c0;;
let PK65_ETA7 = PROVE_PKETA4 PK65 "loop8" "loop8_exit" 0x380 0x0 0x1c0;;
let PK65_ETA8 = PROVE_PKETA4 PK65 "loop10" "loop10_exit" 0x400 0x0 0x1c0;;
let PK65_ETA9 = PROVE_PKETA4 PK65 "loop12" "loop12_exit" 0x480 0x0 0x1c0;;
let PK65_ETA10 = PROVE_PKETA4 PK65 "loop14" "loop14_exit" 0x500 0x0 0x1c0;;
let PK65_ETA11 = PROVE_PKETA4 PK65 "loop16" "loop16_exit" 0x580 0x0 0x1c0;;

let PK65_SCAN1 = PROVE_PKSCAN_BB PK65 "loop6_exit" "loop7" "loop7_exit" "RDI" 3 448 5;;
let PK65_SCAN2 = PROVE_PKSCAN_BB PK65 "loop8_exit" "loop9" "loop9_exit" "R8" 3 448 5;;
let PK65_SCAN3 = PROVE_PKSCAN_BB PK65 "loop10_exit" "loop11" "loop11_exit" "R12" 3 448 5;;
let PK65_SCAN4 = PROVE_PKSCAN_BB PK65 "loop12_exit" "loop13" "loop13_exit" "RBX" 3 448 5;;
let PK65_SCAN5 = PROVE_PKSCAN_BB PK65 "loop14_exit" "loop15" "loop15_exit" "R13" 3 448 5;;
let PK65_SCAN6 = PROVE_PKSCAN_OFF PK65 "loop16_exit" 16 "loop17" "loop17_exit" "R14" 3 448 5;;

let PK65_CMP = PROVE_PKCMP PK65 "after_mld_compute_pack_t0_t165" "loop18" "loop18_exit" 1536 6592 39;;

(*** The checks of s2 as the code keeps them: polynomials 0 and 1 in the
     slots at rsp0 + 280 and 272, 2 to 5 in R12, RBX, R13 and R14 ***)

let PK65_SLOTS = [280,"c1"; 272,"c2"];;
let PK65_REGS = ["R12","c3"; "RBX","c4"; "R13","c5"; "R14","c6"];;
let PK65_ORDER = ["c1"; "c2"; "c3"; "c4"; "c5"; "c6"];;

let PK65_RED = PROVE_PKRED_G PK65 (PK65_FB + 0x970) (PK65_FB + 0x9f3) 208 264 [208,4; 264,8];;
let PK65_HASH = PROVE_PKHASHB_C PK65 (PK65_FB + 0x9f3) "after_mldsa_keccakf1600_permute_15"
  0 216 1952 520 500 3;;
let PK65_TRC = PROVE_PKTRCB PK65 (PK65_FB + 0x1389) (PK65_FB + 0x151e) 288 352 212 264 208
  PK65_SLOTS PK65_REGS PK65_ORDER "R12" 416 352 33 77;;
let PK65_TAIL = PROVE_PKTAILB PK65 (PK65_FB + 0x970) (PK65_FB + 0x151e) 216 1952 352 212
  PK65_SLOTS PK65_REGS PK65_ORDER "R12" 712 648 PK65_RED PK65_HASH PK65_TRC;;

let PK65_CL = PROVE_PKCL PK65 9120
  [0x1b0;0x1a0;0x150;0x140;0x130;0x120;0x190;0x180;0x170;0x160;0xf0;0xe0];;
