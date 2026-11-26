(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The lemmas for the loops and regions that clang 23 inlines into           *)
(* mldsa87_pk_from_sk, instantiated from the generators of                   *)
(* inline_keygen.ml: the eight norm checks of s2 (the first four leave their *)
(* result in RDI, which the code then stores in a slot of the frame), the    *)
(* comparison of t0 with that of the secret key, the rest of the checks with *)
(* the SHAKE256 of the public key (RED, HASHB and TRCB, composed into        *)
(* TAILB), and the end from join1 to the return (CL).                        *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/pk_from_sk_87_spec.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_keygen.ml";;

let PK87 = "mldsa87_pk_from_sk";;
let PK87_FB = layout PK87;;

let PK87_SCAN1 = PROVE_PKSCAN_B PK87 "after_mldsa87_polyeta_unpack_8" "loop1" "loop1_exit" "RDI" 3 480;;
let PK87_SCAN2 = PROVE_PKSCAN_B PK87 "after_mldsa87_polyeta_unpack_9" "loop2" "loop2_exit" "RDI" 3 480;;
let PK87_SCAN3 = PROVE_PKSCAN_B PK87 "after_mldsa87_polyeta_unpack_10" "loop3" "loop3_exit" "RDI" 3 480;;
let PK87_SCAN4 = PROVE_PKSCAN_B PK87 "after_mldsa87_polyeta_unpack_11" "loop4" "loop4_exit" "RDI" 3 480;;
let PK87_SCAN5 = PROVE_PKSCAN_B PK87 "after_mldsa87_polyeta_unpack_12" "loop5" "loop5_exit" "R14" 3 480;;
let PK87_SCAN6 = PROVE_PKSCAN_B PK87 "after_mldsa87_polyeta_unpack_13" "loop6" "loop6_exit" "R12" 3 480;;
let PK87_SCAN7 = PROVE_PKSCAN_B PK87 "after_mldsa87_polyeta_unpack_14" "loop7" "loop7_exit" "R13" 3 480;;
let PK87_SCAN8 = PROVE_PKSCAN_B PK87 "after_mldsa87_polyeta_unpack_15" "loop8" "loop8_exit" "RBX" 3 480;;
let PK87_CMP = PROVE_PKCMP PK87 "after_mld_compute_pack_t0_t187" "loop9" "loop9_exit" 1568 8672 52;;

(*** The checks of s2 as the code keeps them: polynomials 0 to 3 in the slots
     at rsp0 + 312, 304, 296 and 288, 4 to 7 in R14, R12, R13 and RBX ***)

let PK87_SLOTS = [312,"c1"; 304,"c2"; 296,"c3"; 288,"c4"];;
let PK87_REGS = ["R14","c5"; "R12","c6"; "R13","c7"; "RBX","c8"];;
let PK87_ORDER = ["c1"; "c2"; "c3"; "c4"; "c5"; "c6"; "c7"; "c8"];;

let PK87_RED = PROVE_PKRED_G PK87 (PK87_FB + 0x550) (PK87_FB + 0x5d3) 208 280 [208,4; 280,8];;
let PK87_HASH = PROVE_PKHASHB PK87 (PK87_FB + 0x5d3) "after_mldsa_keccakf1600_permute_20"
  0 216 2592 520 500;;
let PK87_TRC = PROVE_PKTRCB PK87 (PK87_FB + 0x1279) (PK87_FB + 0x1420) 320 384 212 280 208
  PK87_SLOTS PK87_REGS PK87_ORDER "R12" 448 384 33 80;;
let PK87_TAIL = PROVE_PKTAILB PK87 (PK87_FB + 0x550) (PK87_FB + 0x1420) 216 2592 384 212
  PK87_SLOTS PK87_REGS PK87_ORDER "R12" 744 680 PK87_RED PK87_HASH PK87_TRC;;

let PK87_CL = PROVE_PKCL PK87 12032
  [0x1d0;0x1c0;0x170;0x160;0x150;0x140;0x1b0;0x1a0;0x190;0x180;0xf0;0xe0];;
