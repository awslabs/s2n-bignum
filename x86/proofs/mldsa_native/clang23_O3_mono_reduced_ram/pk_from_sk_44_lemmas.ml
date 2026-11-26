(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The lemmas for the loops and regions that clang 23 inlines into           *)
(* mldsa44_pk_from_sk, instantiated from the generators of                   *)
(* inline_keygen.ml: the four norm checks of s2, the comparison of t0 with   *)
(* that of the secret key, the rest of the checks with the SHAKE256 of the   *)
(* public key (RED, HASH and TRC, composed into TAIL), and the end from      *)
(* join1 to the return (CL).                                                 *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/pk_from_sk_44_spec.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_keygen.ml";;

let PK44 = "mldsa44_pk_from_sk";;
let PK44_FB = layout PK44;;

let PK44_SCAN1 = PROVE_PKSCAN PK44 "after_mldsa44_polyeta_unpack_5" "loop1" "loop1_exit" "R14" 2;;
let PK44_SCAN2 = PROVE_PKSCAN PK44 "after_mldsa44_polyeta_unpack_6" "loop2" "loop2_exit" "R12" 3;;
let PK44_SCAN3 = PROVE_PKSCAN PK44 "after_mldsa44_polyeta_unpack_7" "loop3" "loop3_exit" "R13" 3;;
let PK44_SCAN4 = PROVE_PKSCAN PK44 "after_mldsa44_polyeta_unpack_8" "loop4" "loop4_exit" "RBX" 3;;
let PK44_CMP = PROVE_PKCMP PK44 "after_mld_compute_pack_t0_t144" "loop5" "loop5_exit" 896 1472 26;;

let PK44_RED = PROVE_PKRED PK44 (PK44_FB + 0x360) (PK44_FB + 0x3e3);;
let PK44_HASH = PROVE_PKHASH PK44 (PK44_FB + 0x3e3);;
let PK44_TRC = PROVE_PKTRC PK44 (PK44_FB + 0xb06) (PK44_FB + 0xc87);;
let PK44_TAIL = PROVE_PKTAIL PK44 (PK44_FB + 0x360) (PK44_FB + 0xc87) PK44_RED PK44_HASH PK44_TRC;;

let PK44_CL = PROVE_PKCL PK44 7264
  [0x100;0x110;0x120;0x130;0x140;0x150;0x160;0x170;0x180;0x190;0x1a0;0x1b0];;
