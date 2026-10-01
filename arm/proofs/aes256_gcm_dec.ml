(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================== *)
(* Functional correctness, constant-time and memory-safety proofs of the       *)
(* AES-256-GCM bulk decryption kernel aes256_gcm_dec.                          *)
(*                                                                            *)
(* The software-pipelined four-block main loop is verified from a single       *)
(* mid-pipeline invariant swp_inv, decomposed into leg theorems (each a Hoare  *)
(* triple over the kernel's machine code):                                    *)
(*                                                                            *)
(*   FILL_TO_CBZ_DEC  precond @0x2c -> swp_inv 0 @0x268                       *)
(*   FILLLEG          one hop from it (cbz@0x268 not taken) @0x26c             *)
(*   BODYLEG          swp_inv i @0x26c -> swp_inv (i+1) @0x570                *)
(*   DRAIN_FROM_574   swp_inv (loop_count-1) @0x574 -> drain_bridge @0x6c0     *)
(*   DRAINLEG         one hop from it (cbnz@0x570 not taken)                   *)
(*   TAILLEG          drain_bridge @0x6c0 -> tail_post @0x7c4                  *)
(*                                                                            *)
(* GHASH is computed over the INPUT (ciphertext) blocks (nist_input_block);    *)
(* the accumulator Q30 is carried in the half-swapped SPLIT form.             *)
(*                                                                            *)
(* The whole-function composition assembles the legs: the steady-state loop   *)
(* by ENSURES_WHILE over loop_count-1 iterations (MAINLEG), the loop_count    *)
(* in {0,1} cases by LEG_LC0 and LEG_LC1, unified by CORE_FROM88 and lifted   *)
(* to AES256_GCM_DEC_CORRECT (core, pc+0x2c to pc+0x7c4) and the subroutine   *)
(* wrapper AES256_GCM_DEC_SUBROUTINE_CORRECT.  The shared lemma substrate is  *)
(* in aes_gcm_utils.ml.                                                       *)
(* ========================================================================== *)

needs "arm/proofs/base.ml";;
needs "common/fips197.ml";;
needs "common/polyval_ghash.ml";;
needs "common/ghash_nist_bridge.ml";;
needs "common/karatsuba_pmul.ml";;
needs "arm/proofs/aes_gcm_utils.ml";;

let aes256_gcm_dec_mc = define_assert_from_elf "aes256_gcm_dec_mc" "arm/aes_gcm/aes256_gcm_dec.o"
[
  0xd10383ff;       (* arm_SUB SP SP (rvalue (word 224)) *)
  0xa90053f3;       (* arm_STP X19 X20 SP (Immediate_Offset (iword (&0))) *)
  0xa9015bf5;       (* arm_STP X21 X22 SP (Immediate_Offset (iword (&16))) *)
  0xa90263f7;       (* arm_STP X23 X24 SP (Immediate_Offset (iword (&32))) *)
  0xa9036bf9;       (* arm_STP X25 X26 SP (Immediate_Offset (iword (&48))) *)
  0xa90473fb;       (* arm_STP X27 X28 SP (Immediate_Offset (iword (&64))) *)
  0xa9057bfd;       (* arm_STP X29 X30 SP (Immediate_Offset (iword (&80))) *)
  0x6d0627e8;       (* arm_STP D8 D9 SP (Immediate_Offset (iword (&96))) *)
  0x6d072fea;       (* arm_STP D10 D11 SP (Immediate_Offset (iword (&112))) *)
  0x6d0837ec;       (* arm_STP D12 D13 SP (Immediate_Offset (iword (&128))) *)
  0x6d093fee;       (* arm_STP D14 D15 SP (Immediate_Offset (iword (&144))) *)
  0xd343fc2f;       (* arm_LSR X15 X1 3 *)
  0x3dc000b2;       (* arm_LDR Q18 X5 (Immediate_Offset (word 0)) *)
  0x3dc004b3;       (* arm_LDR Q19 X5 (Immediate_Offset (word 16)) *)
  0x3dc008b4;       (* arm_LDR Q20 X5 (Immediate_Offset (word 32)) *)
  0x3dc00cb5;       (* arm_LDR Q21 X5 (Immediate_Offset (word 48)) *)
  0x3dc010b6;       (* arm_LDR Q22 X5 (Immediate_Offset (word 64)) *)
  0x3dc014b7;       (* arm_LDR Q23 X5 (Immediate_Offset (word 80)) *)
  0x3dc018b8;       (* arm_LDR Q24 X5 (Immediate_Offset (word 96)) *)
  0x3dc01cb9;       (* arm_LDR Q25 X5 (Immediate_Offset (word 112)) *)
  0x3dc020ba;       (* arm_LDR Q26 X5 (Immediate_Offset (word 128)) *)
  0x3dc024bb;       (* arm_LDR Q27 X5 (Immediate_Offset (word 144)) *)
  0x3dc028bc;       (* arm_LDR Q28 X5 (Immediate_Offset (word 160)) *)
  0x3dc02caf;       (* arm_LDR Q15 X5 (Immediate_Offset (word 176)) *)
  0x3dc030b0;       (* arm_LDR Q16 X5 (Immediate_Offset (word 192)) *)
  0x3dc034b1;       (* arm_LDR Q17 X5 (Immediate_Offset (word 208)) *)
  0x3dc038a2;       (* arm_LDR Q2 X5 (Immediate_Offset (word 224)) *)
  0x3dc0007e;       (* arm_LDR Q30 X3 (Immediate_Offset (word 0)) *)
  0x4e200bde;       (* arm_REV64_VEC Q30 Q30 8 *)
  0xa940308b;       (* arm_LDP X11 X12 X4 (Immediate_Offset (iword (&0))) *)
  0xa90a33eb;       (* arm_STP X11 X12 SP (Immediate_Offset (iword (&160))) *)
  0xa90b33eb;       (* arm_STP X11 X12 SP (Immediate_Offset (iword (&176))) *)
  0xa90c33eb;       (* arm_STP X11 X12 SP (Immediate_Offset (iword (&192))) *)
  0xa90d33eb;       (* arm_STP X11 X12 SP (Immediate_Offset (iword (&208))) *)
  0xd360fd8d;       (* arm_LSR X13 X12 32 *)
  0x5ac009ad;       (* arm_REV W13 W13 *)
  0x2a0c018c;       (* arm_ORR W12 W12 W12 *)
  0xd344fde7;       (* arm_LSR X7 X15 4 *)
  0xd342fce1;       (* arm_LSR X1 X7 2 *)
  0x924004e9;       (* arm_AND X9 X7 (rvalue (word 3)) *)
  0x0f06e447;       (* arm_MOVI D7 (word 14033993530586874562) *)
  0x5f7854e7;       (* arm_SHL_VEC Q7 Q7 56 64 64 *)
  0xb40030c1;       (* arm_CBZ X1 (word 1560) *)
  0x3dc000c5;       (* arm_LDR Q5 X6 (Immediate_Offset (word 0)) *)
  0x3dc00c00;       (* arm_LDR Q0 X0 (Immediate_Offset (word 48)) *)
  0x110005ab;       (* arm_ADD W11 W13 (rvalue (word 1)) *)
  0x110009bb;       (* arm_ADD W27 W13 (rvalue (word 2)) *)
  0x3dc00cdf;       (* arm_LDR Q31 X6 (Immediate_Offset (word 48)) *)
  0x3dc0081d;       (* arm_LDR Q29 X0 (Immediate_Offset (word 32)) *)
  0x5ac00b6c;       (* arm_REV W12 W27 *)
  0x5ac0097e;       (* arm_REV W30 W11 *)
  0x3dc010cd;       (* arm_LDR Q13 X6 (Immediate_Offset (word 64)) *)
  0x11000dbb;       (* arm_ADD W27 W13 (rvalue (word 3)) *)
  0xb900bffe;       (* arm_STR W30 SP (Immediate_Offset (word 188)) *)
  0x110001b9;       (* arm_ADD W25 W13 (rvalue (word 0)) *)
  0x3dc00401;       (* arm_LDR Q1 X0 (Immediate_Offset (word 16)) *)
  0x5ac00b31;       (* arm_REV W17 W25 *)
  0x5ac00b67;       (* arm_REV W7 W27 *)
  0xb900cfec;       (* arm_STR W12 SP (Immediate_Offset (word 204)) *)
  0x4e200808;       (* arm_REV64_VEC Q8 Q0 8 *)
  0x3dc02fe3;       (* arm_LDR Q3 SP (Immediate_Offset (word 176)) *)
  0x4e200bae;       (* arm_REV64_VEC Q14 Q29 8 *)
  0x3dc033ec;       (* arm_LDR Q12 SP (Immediate_Offset (word 192)) *)
  0xb900dfe7;       (* arm_STR W7 SP (Immediate_Offset (word 220)) *)
  0x0ee5e10a;       (* arm_PMULL_VEC Q10 Q8 Q5 64 *)
  0x5e180506;       (* arm_DUP_ELEM_SCALAR Q6 Q8 1 64 *)
  0xb900aff1;       (* arm_STR W17 SP (Immediate_Offset (word 172)) *)
  0x4ee5e10b;       (* arm_PMULL2_VEC Q11 Q8 Q5 64 *)
  0x3dc004c5;       (* arm_LDR Q5 X6 (Immediate_Offset (word 16)) *)
  0x6e0e41c4;       (* arm_EXT Q4 Q14 Q14 64 *)
  0x4e284a43;       (* arm_AESE Q3 Q18 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284a4c;       (* arm_AESE Q12 Q18 *)
  0x4e28698c;       (* arm_AESMC Q12 Q12 *)
  0x2e281cc6;       (* arm_EOR_VEC Q6 Q6 Q8 64 *)
  0x6e2e1c88;       (* arm_EOR_VEC Q8 Q4 Q14 128 *)
  0x4e284a63;       (* arm_AESE Q3 Q19 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e200829;       (* arm_REV64_VEC Q9 Q1 8 *)
  0x0ee5e0c4;       (* arm_PMULL_VEC Q4 Q6 Q5 64 *)
  0x4ee5e108;       (* arm_PMULL2_VEC Q8 Q8 Q5 64 *)
  0x3dc008c5;       (* arm_LDR Q5 X6 (Immediate_Offset (word 32)) *)
  0x4e284a83;       (* arm_AESE Q3 Q20 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284a6c;       (* arm_AESE Q12 Q19 *)
  0x4e28698c;       (* arm_AESMC Q12 Q12 *)
  0x4e284aa3;       (* arm_AESE Q3 Q21 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284a8c;       (* arm_AESE Q12 Q20 *)
  0x4e28698c;       (* arm_AESMC Q12 Q12 *)
  0x4ee5e1c6;       (* arm_PMULL2_VEC Q6 Q14 Q5 64 *)
  0x4e284aac;       (* arm_AESE Q12 Q21 *)
  0x4e28698c;       (* arm_AESMC Q12 Q12 *)
  0x6e261d6b;       (* arm_EOR_VEC Q11 Q11 Q6 128 *)
  0x4e284ac3;       (* arm_AESE Q3 Q22 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284acc;       (* arm_AESE Q12 Q22 *)
  0x4e28698c;       (* arm_AESMC Q12 Q12 *)
  0x6e281c86;       (* arm_EOR_VEC Q6 Q4 Q8 128 *)
  0x5e180528;       (* arm_DUP_ELEM_SCALAR Q8 Q9 1 64 *)
  0x4e284ae3;       (* arm_AESE Q3 Q23 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284aec;       (* arm_AESE Q12 Q23 *)
  0x4e28698c;       (* arm_AESMC Q12 Q12 *)
  0x4e284b03;       (* arm_AESE Q3 Q24 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x2e291d04;       (* arm_EOR_VEC Q4 Q8 Q9 64 *)
  0x4e284b0c;       (* arm_AESE Q12 Q24 *)
  0x4e28698c;       (* arm_AESMC Q12 Q12 *)
  0x3dc037e8;       (* arm_LDR Q8 SP (Immediate_Offset (word 208)) *)
  0x4e284b23;       (* arm_AESE Q3 Q25 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b2c;       (* arm_AESE Q12 Q25 *)
  0x4e28698c;       (* arm_AESMC Q12 Q12 *)
  0x4e284b43;       (* arm_AESE Q3 Q26 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b4c;       (* arm_AESE Q12 Q26 *)
  0x4e28698c;       (* arm_AESMC Q12 Q12 *)
  0x4e284b63;       (* arm_AESE Q3 Q27 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b6c;       (* arm_AESE Q12 Q27 *)
  0x4e28698c;       (* arm_AESMC Q12 Q12 *)
  0x4e284b83;       (* arm_AESE Q3 Q28 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b8c;       (* arm_AESE Q12 Q28 *)
  0x4e28698c;       (* arm_AESMC Q12 Q12 *)
  0x4e284a48;       (* arm_AESE Q8 Q18 *)
  0x4e286908;       (* arm_AESMC Q8 Q8 *)
  0x4e2849ec;       (* arm_AESE Q12 Q15 *)
  0x4e28698c;       (* arm_AESMC Q12 Q12 *)
  0x0ee5e1ce;       (* arm_PMULL_VEC Q14 Q14 Q5 64 *)
  0x4e284a0c;       (* arm_AESE Q12 Q16 *)
  0x4e28698c;       (* arm_AESMC Q12 Q12 *)
  0x6e2e1d4a;       (* arm_EOR_VEC Q10 Q10 Q14 128 *)
  0x4e284a68;       (* arm_AESE Q8 Q19 *)
  0x4e286908;       (* arm_AESMC Q8 Q8 *)
  0x4e284a2c;       (* arm_AESE Q12 Q17 *)
  0x3cc4040e;       (* arm_LDR Q14 X0 (Postimmediate_Offset (word 64)) *)
  0x4effe125;       (* arm_PMULL2_VEC Q5 Q9 Q31 64 *)
  0x6e221d8c;       (* arm_EOR_VEC Q12 Q12 Q2 128 *)
  0x4e284a88;       (* arm_AESE Q8 Q20 *)
  0x4e286908;       (* arm_AESMC Q8 Q8 *)
  0x0effe129;       (* arm_PMULL_VEC Q9 Q9 Q31 64 *)
  0x3dc02bff;       (* arm_LDR Q31 SP (Immediate_Offset (word 160)) *)
  0x6e3d1d8c;       (* arm_EOR_VEC Q12 Q12 Q29 128 *)
  0x4e284aa8;       (* arm_AESE Q8 Q21 *)
  0x4e286908;       (* arm_AESMC Q8 Q8 *)
  0x3dc014dd;       (* arm_LDR Q29 X6 (Immediate_Offset (word 80)) *)
  0x4e2849e3;       (* arm_AESE Q3 Q15 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284ac8;       (* arm_AESE Q8 Q22 *)
  0x4e286908;       (* arm_AESMC Q8 Q8 *)
  0x3d80084c;       (* arm_STR Q12 X2 (Immediate_Offset (word 32)) *)
  0xd1000421;       (* arm_SUB X1 X1 (rvalue (word 1)) *)
  0xb4001861;       (* arm_CBZ X1 (word 780) *)
  0x6e251d6c;       (* arm_EOR_VEC Q12 Q11 Q5 128 *)
  0x0eede085;       (* arm_PMULL_VEC Q5 Q4 Q13 64 *)
  0x110011ad;       (* arm_ADD W13 W13 (rvalue (word 4)) *)
  0x6e291d44;       (* arm_EOR_VEC Q4 Q10 Q9 128 *)
  0x4e284a5f;       (* arm_AESE Q31 Q18 *)
  0x4e286bff;       (* arm_AESMC Q31 Q31 *)
  0x11000dbb;       (* arm_ADD W27 W13 (rvalue (word 3)) *)
  0x110009ac;       (* arm_ADD W12 W13 (rvalue (word 2)) *)
  0x4e284a03;       (* arm_AESE Q3 Q16 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e2009c9;       (* arm_REV64_VEC Q9 Q14 8 *)
  0x110005b1;       (* arm_ADD W17 W13 (rvalue (word 1)) *)
  0x5ac0098b;       (* arm_REV W11 W12 *)
  0x4e284a7f;       (* arm_AESE Q31 Q19 *)
  0x4e286bff;       (* arm_AESMC Q31 Q31 *)
  0xb900cfeb;       (* arm_STR W11 SP (Immediate_Offset (word 204)) *)
  0x5ac00a39;       (* arm_REV W25 W17 *)
  0x4e284a23;       (* arm_AESE Q3 Q17 *)
  0x6e3e1d2a;       (* arm_EOR_VEC Q10 Q9 Q30 128 *)
  0xb900bff9;       (* arm_STR W25 SP (Immediate_Offset (word 188)) *)
  0x110001a7;       (* arm_ADD W7 W13 (rvalue (word 0)) *)
  0x4e284a9f;       (* arm_AESE Q31 Q20 *)
  0x4e286bff;       (* arm_AESMC Q31 Q31 *)
  0x3dc033fe;       (* arm_LDR Q30 SP (Immediate_Offset (word 192)) *)
  0x5ac008fe;       (* arm_REV W30 W7 *)
  0x6e251cc5;       (* arm_EOR_VEC Q5 Q6 Q5 128 *)
  0x0efde14b;       (* arm_PMULL_VEC Q11 Q10 Q29 64 *)
  0x5ac00b68;       (* arm_REV W8 W27 *)
  0x6e221c63;       (* arm_EOR_VEC Q3 Q3 Q2 128 *)
  0x4e284abf;       (* arm_AESE Q31 Q21 *)
  0x4e286bff;       (* arm_AESMC Q31 Q31 *)
  0xb900dfe8;       (* arm_STR W8 SP (Immediate_Offset (word 220)) *)
  0x6e2b1c84;       (* arm_EOR_VEC Q4 Q4 Q11 128 *)
  0x4efde14b;       (* arm_PMULL2_VEC Q11 Q10 Q29 64 *)
  0xb900affe;       (* arm_STR W30 SP (Immediate_Offset (word 172)) *)
  0x4e284a5e;       (* arm_AESE Q30 Q18 *)
  0x4e286bde;       (* arm_AESMC Q30 Q30 *)
  0x4e284adf;       (* arm_AESE Q31 Q22 *)
  0x4e286bff;       (* arm_AESMC Q31 Q31 *)
  0x6e2b1d89;       (* arm_EOR_VEC Q9 Q12 Q11 128 *)
  0x6e0a414c;       (* arm_EXT Q12 Q10 Q10 64 *)
  0x4e284a7e;       (* arm_AESE Q30 Q19 *)
  0x4e286bde;       (* arm_AESMC Q30 Q30 *)
  0x6e211c61;       (* arm_EOR_VEC Q1 Q3 Q1 128 *)
  0x4e284ae8;       (* arm_AESE Q8 Q23 *)
  0x4e286908;       (* arm_AESMC Q8 Q8 *)
  0x6e2a1d83;       (* arm_EOR_VEC Q3 Q12 Q10 128 *)
  0x4e284a9e;       (* arm_AESE Q30 Q20 *)
  0x4e286bde;       (* arm_AESMC Q30 Q30 *)
  0x4e284b08;       (* arm_AESE Q8 Q24 *)
  0x4e286908;       (* arm_AESMC Q8 Q8 *)
  0x3d800441;       (* arm_STR Q1 X2 (Immediate_Offset (word 16)) *)
  0x4e284abe;       (* arm_AESE Q30 Q21 *)
  0x4e286bde;       (* arm_AESMC Q30 Q30 *)
  0x3dc00801;       (* arm_LDR Q1 X0 (Immediate_Offset (word 32)) *)
  0x4e284b28;       (* arm_AESE Q8 Q25 *)
  0x4e286908;       (* arm_AESMC Q8 Q8 *)
  0x6e094126;       (* arm_EXT Q6 Q9 Q9 64 *)
  0x0ee7e12c;       (* arm_PMULL_VEC Q12 Q9 Q7 64 *)
  0x4e284b48;       (* arm_AESE Q8 Q26 *)
  0x4e286908;       (* arm_AESMC Q8 Q8 *)
  0x4eede06b;       (* arm_PMULL2_VEC Q11 Q3 Q13 64 *)
  0x6e291c89;       (* arm_EOR_VEC Q9 Q4 Q9 128 *)
  0x6e2c1cc3;       (* arm_EOR_VEC Q3 Q6 Q12 128 *)
  0x4e284b68;       (* arm_AESE Q8 Q27 *)
  0x4e286908;       (* arm_AESMC Q8 Q8 *)
  0x4e284ade;       (* arm_AESE Q30 Q22 *)
  0x4e286bde;       (* arm_AESMC Q30 Q30 *)
  0x6e2b1cac;       (* arm_EOR_VEC Q12 Q5 Q11 128 *)
  0x4e20083d;       (* arm_REV64_VEC Q29 Q1 8 *)
  0x4e284b88;       (* arm_AESE Q8 Q28 *)
  0x4e286908;       (* arm_AESMC Q8 Q8 *)
  0x3dc004ca;       (* arm_LDR Q10 X6 (Immediate_Offset (word 16)) *)
  0x4e284afe;       (* arm_AESE Q30 Q23 *)
  0x4e286bde;       (* arm_AESMC Q30 Q30 *)
  0x6e1d43ad;       (* arm_EXT Q13 Q29 Q29 64 *)
  0x4e2849e8;       (* arm_AESE Q8 Q15 *)
  0x4e286908;       (* arm_AESMC Q8 Q8 *)
  0x4e284b1e;       (* arm_AESE Q30 Q24 *)
  0x4e286bde;       (* arm_AESMC Q30 Q30 *)
  0x6e3d1da6;       (* arm_EOR_VEC Q6 Q13 Q29 128 *)
  0x4e284a08;       (* arm_AESE Q8 Q16 *)
  0x4e286908;       (* arm_AESMC Q8 Q8 *)
  0x6e291d8d;       (* arm_EOR_VEC Q13 Q12 Q9 128 *)
  0x4e284b3e;       (* arm_AESE Q30 Q25 *)
  0x4e286bde;       (* arm_AESMC Q30 Q30 *)
  0x4e284a28;       (* arm_AESE Q8 Q17 *)
  0x6e231da9;       (* arm_EOR_VEC Q9 Q13 Q3 128 *)
  0x4e284b5e;       (* arm_AESE Q30 Q26 *)
  0x4e286bde;       (* arm_AESMC Q30 Q30 *)
  0x6e221d0b;       (* arm_EOR_VEC Q11 Q8 Q2 128 *)
  0x4e284aff;       (* arm_AESE Q31 Q23 *)
  0x4e286bff;       (* arm_AESMC Q31 Q31 *)
  0x3dc037e8;       (* arm_LDR Q8 SP (Immediate_Offset (word 208)) *)
  0x4e284b7e;       (* arm_AESE Q30 Q27 *)
  0x4e286bde;       (* arm_AESMC Q30 Q30 *)
  0x6e201d6d;       (* arm_EOR_VEC Q13 Q11 Q0 128 *)
  0x0ee7e125;       (* arm_PMULL_VEC Q5 Q9 Q7 64 *)
  0x3dc00c00;       (* arm_LDR Q0 X0 (Immediate_Offset (word 48)) *)
  0x4e284b9e;       (* arm_AESE Q30 Q28 *)
  0x4e286bde;       (* arm_AESMC Q30 Q30 *)
  0x4e284b1f;       (* arm_AESE Q31 Q24 *)
  0x4e286bff;       (* arm_AESMC Q31 Q31 *)
  0x3d800c4d;       (* arm_STR Q13 X2 (Immediate_Offset (word 48)) *)
  0x6e251c8c;       (* arm_EOR_VEC Q12 Q4 Q5 128 *)
  0x4e2849fe;       (* arm_AESE Q30 Q15 *)
  0x4e286bde;       (* arm_AESMC Q30 Q30 *)
  0x4e284b3f;       (* arm_AESE Q31 Q25 *)
  0x4e286bff;       (* arm_AESMC Q31 Q31 *)
  0x6e094125;       (* arm_EXT Q5 Q9 Q9 64 *)
  0x4e20080b;       (* arm_REV64_VEC Q11 Q0 8 *)
  0x4e284a1e;       (* arm_AESE Q30 Q16 *)
  0x4e286bde;       (* arm_AESMC Q30 Q30 *)
  0x4e284b5f;       (* arm_AESE Q31 Q26 *)
  0x4e286bff;       (* arm_AESMC Q31 Q31 *)
  0x6e251d85;       (* arm_EOR_VEC Q5 Q12 Q5 128 *)
  0x3dc02fe3;       (* arm_LDR Q3 SP (Immediate_Offset (word 176)) *)
  0x4e284a3e;       (* arm_AESE Q30 Q17 *)
  0x5e18056c;       (* arm_DUP_ELEM_SCALAR Q12 Q11 1 64 *)
  0x4e284b7f;       (* arm_AESE Q31 Q27 *)
  0x4e286bff;       (* arm_AESMC Q31 Q31 *)
  0x4e284a48;       (* arm_AESE Q8 Q18 *)
  0x4e286908;       (* arm_AESMC Q8 Q8 *)
  0x6e221fc4;       (* arm_EOR_VEC Q4 Q30 Q2 128 *)
  0x2e2b1d8c;       (* arm_EOR_VEC Q12 Q12 Q11 64 *)
  0x4e284b9f;       (* arm_AESE Q31 Q28 *)
  0x4e286bff;       (* arm_AESMC Q31 Q31 *)
  0x4e284a43;       (* arm_AESE Q3 Q18 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284a68;       (* arm_AESE Q8 Q19 *)
  0x4e286908;       (* arm_AESMC Q8 Q8 *)
  0x4e2849ff;       (* arm_AESE Q31 Q15 *)
  0x4e286bff;       (* arm_AESMC Q31 Q31 *)
  0x3dc000de;       (* arm_LDR Q30 X6 (Immediate_Offset (word 0)) *)
  0x4eeae0c9;       (* arm_PMULL2_VEC Q9 Q6 Q10 64 *)
  0x3dc008cd;       (* arm_LDR Q13 X6 (Immediate_Offset (word 32)) *)
  0x4e284a63;       (* arm_AESE Q3 Q19 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x0eeae186;       (* arm_PMULL_VEC Q6 Q12 Q10 64 *)
  0x6e211c8c;       (* arm_EOR_VEC Q12 Q4 Q1 128 *)
  0x4e284a83;       (* arm_AESE Q3 Q20 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x6e291cc6;       (* arm_EOR_VEC Q6 Q6 Q9 128 *)
  0x4e284a1f;       (* arm_AESE Q31 Q16 *)
  0x4e286bff;       (* arm_AESMC Q31 Q31 *)
  0x4e284aa3;       (* arm_AESE Q3 Q21 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284a3f;       (* arm_AESE Q31 Q17 *)
  0x4e284ac3;       (* arm_AESE Q3 Q22 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x3dc00401;       (* arm_LDR Q1 X0 (Immediate_Offset (word 16)) *)
  0x6e221fff;       (* arm_EOR_VEC Q31 Q31 Q2 128 *)
  0x0efee164;       (* arm_PMULL_VEC Q4 Q11 Q30 64 *)
  0x4e284ae3;       (* arm_AESE Q3 Q23 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x6e2e1fea;       (* arm_EOR_VEC Q10 Q31 Q14 128 *)
  0x4efee16b;       (* arm_PMULL2_VEC Q11 Q11 Q30 64 *)
  0x3dc00cce;       (* arm_LDR Q14 X6 (Immediate_Offset (word 48)) *)
  0x4e284b03;       (* arm_AESE Q3 Q24 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x6e0540be;       (* arm_EXT Q30 Q5 Q5 64 *)
  0x4e284a88;       (* arm_AESE Q8 Q20 *)
  0x4e286908;       (* arm_AESMC Q8 Q8 *)
  0x4e284b23;       (* arm_AESE Q3 Q25 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e20083f;       (* arm_REV64_VEC Q31 Q1 8 *)
  0x3c84044a;       (* arm_STR Q10 X2 (Postimmediate_Offset (word 64)) *)
  0x0eede3aa;       (* arm_PMULL_VEC Q10 Q29 Q13 64 *)
  0x4e284b43;       (* arm_AESE Q3 Q26 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x5e1807e5;       (* arm_DUP_ELEM_SCALAR Q5 Q31 1 64 *)
  0x4eede3bd;       (* arm_PMULL2_VEC Q29 Q29 Q13 64 *)
  0x6e2a1c8a;       (* arm_EOR_VEC Q10 Q4 Q10 128 *)
  0x4e284b63;       (* arm_AESE Q3 Q27 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x2e3f1ca4;       (* arm_EOR_VEC Q4 Q5 Q31 64 *)
  0x0eeee3e9;       (* arm_PMULL_VEC Q9 Q31 Q14 64 *)
  0x3dc010cd;       (* arm_LDR Q13 X6 (Immediate_Offset (word 64)) *)
  0x4eeee3e5;       (* arm_PMULL2_VEC Q5 Q31 Q14 64 *)
  0x3cc4040e;       (* arm_LDR Q14 X0 (Postimmediate_Offset (word 64)) *)
  0x6e3d1d6b;       (* arm_EOR_VEC Q11 Q11 Q29 128 *)
  0x4e284b83;       (* arm_AESE Q3 Q28 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x3dc02bff;       (* arm_LDR Q31 SP (Immediate_Offset (word 160)) *)
  0x4e284aa8;       (* arm_AESE Q8 Q21 *)
  0x4e286908;       (* arm_AESMC Q8 Q8 *)
  0x3dc014dd;       (* arm_LDR Q29 X6 (Immediate_Offset (word 80)) *)
  0x4e2849e3;       (* arm_AESE Q3 Q15 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284ac8;       (* arm_AESE Q8 Q22 *)
  0x4e286908;       (* arm_AESMC Q8 Q8 *)
  0x3d80084c;       (* arm_STR Q12 X2 (Immediate_Offset (word 32)) *)
  0xd1000421;       (* arm_SUB X1 X1 (rvalue (word 1)) *)
  0xb5ffe7e1;       (* arm_CBNZ X1 (word 2096380) *)
  0x0eede084;       (* arm_PMULL_VEC Q4 Q4 Q13 64 *)
  0x4e2009cc;       (* arm_REV64_VEC Q12 Q14 8 *)
  0x110011ad;       (* arm_ADD W13 W13 (rvalue (word 4)) *)
  0x4e284a5f;       (* arm_AESE Q31 Q18 *)
  0x4e286bff;       (* arm_AESMC Q31 Q31 *)
  0x6e291d4a;       (* arm_EOR_VEC Q10 Q10 Q9 128 *)
  0x6e241cc9;       (* arm_EOR_VEC Q9 Q6 Q4 128 *)
  0x4e284ae8;       (* arm_AESE Q8 Q23 *)
  0x4e286908;       (* arm_AESMC Q8 Q8 *)
  0x4e284a7f;       (* arm_AESE Q31 Q19 *)
  0x4e286bff;       (* arm_AESMC Q31 Q31 *)
  0x6e3e1d9e;       (* arm_EOR_VEC Q30 Q12 Q30 128 *)
  0x6e251d6c;       (* arm_EOR_VEC Q12 Q11 Q5 128 *)
  0x4e284b08;       (* arm_AESE Q8 Q24 *)
  0x4e286908;       (* arm_AESMC Q8 Q8 *)
  0x4efde3c4;       (* arm_PMULL2_VEC Q4 Q30 Q29 64 *)
  0x6e1e43c6;       (* arm_EXT Q6 Q30 Q30 64 *)
  0x0efde3c5;       (* arm_PMULL_VEC Q5 Q30 Q29 64 *)
  0x4e284b28;       (* arm_AESE Q8 Q25 *)
  0x4e286908;       (* arm_AESMC Q8 Q8 *)
  0x6e3e1cde;       (* arm_EOR_VEC Q30 Q6 Q30 128 *)
  0x6e251d4a;       (* arm_EOR_VEC Q10 Q10 Q5 128 *)
  0x4e284a9f;       (* arm_AESE Q31 Q20 *)
  0x4e286bff;       (* arm_AESMC Q31 Q31 *)
  0x4eede3cb;       (* arm_PMULL2_VEC Q11 Q30 Q13 64 *)
  0x6e241d84;       (* arm_EOR_VEC Q4 Q12 Q4 128 *)
  0x4e284abf;       (* arm_AESE Q31 Q21 *)
  0x4e286bff;       (* arm_AESMC Q31 Q31 *)
  0x0ee7e08d;       (* arm_PMULL_VEC Q13 Q4 Q7 64 *)
  0x6e04409e;       (* arm_EXT Q30 Q4 Q4 64 *)
  0x4e284adf;       (* arm_AESE Q31 Q22 *)
  0x4e286bff;       (* arm_AESMC Q31 Q31 *)
  0x6e2b1d25;       (* arm_EOR_VEC Q5 Q9 Q11 128 *)
  0x4e284b48;       (* arm_AESE Q8 Q26 *)
  0x4e286908;       (* arm_AESMC Q8 Q8 *)
  0x6e241d49;       (* arm_EOR_VEC Q9 Q10 Q4 128 *)
  0x6e2d1fc6;       (* arm_EOR_VEC Q6 Q30 Q13 128 *)
  0x4e284aff;       (* arm_AESE Q31 Q23 *)
  0x4e286bff;       (* arm_AESMC Q31 Q31 *)
  0x6e291ca5;       (* arm_EOR_VEC Q5 Q5 Q9 128 *)
  0x4e284b68;       (* arm_AESE Q8 Q27 *)
  0x4e286908;       (* arm_AESMC Q8 Q8 *)
  0x4e284b1f;       (* arm_AESE Q31 Q24 *)
  0x4e286bff;       (* arm_AESMC Q31 Q31 *)
  0x4e284b88;       (* arm_AESE Q8 Q28 *)
  0x4e286908;       (* arm_AESMC Q8 Q8 *)
  0x6e261ca5;       (* arm_EOR_VEC Q5 Q5 Q6 128 *)
  0x4e284b3f;       (* arm_AESE Q31 Q25 *)
  0x4e286bff;       (* arm_AESMC Q31 Q31 *)
  0x4e2849e8;       (* arm_AESE Q8 Q15 *)
  0x4e286908;       (* arm_AESMC Q8 Q8 *)
  0x4e284b5f;       (* arm_AESE Q31 Q26 *)
  0x4e286bff;       (* arm_AESMC Q31 Q31 *)
  0x0ee7e0a6;       (* arm_PMULL_VEC Q6 Q5 Q7 64 *)
  0x6e0540a5;       (* arm_EXT Q5 Q5 Q5 64 *)
  0x4e284b7f;       (* arm_AESE Q31 Q27 *)
  0x4e286bff;       (* arm_AESMC Q31 Q31 *)
  0x4e284a08;       (* arm_AESE Q8 Q16 *)
  0x4e286908;       (* arm_AESMC Q8 Q8 *)
  0x6e261d4a;       (* arm_EOR_VEC Q10 Q10 Q6 128 *)
  0x4e284b9f;       (* arm_AESE Q31 Q28 *)
  0x4e286bff;       (* arm_AESMC Q31 Q31 *)
  0x4e284a28;       (* arm_AESE Q8 Q17 *)
  0x6e251d45;       (* arm_EOR_VEC Q5 Q10 Q5 128 *)
  0x4e2849ff;       (* arm_AESE Q31 Q15 *)
  0x4e286bff;       (* arm_AESMC Q31 Q31 *)
  0x4e284a03;       (* arm_AESE Q3 Q16 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x6e0540be;       (* arm_EXT Q30 Q5 Q5 64 *)
  0x6e221d05;       (* arm_EOR_VEC Q5 Q8 Q2 128 *)
  0x4e284a1f;       (* arm_AESE Q31 Q16 *)
  0x4e286bff;       (* arm_AESMC Q31 Q31 *)
  0x4e284a23;       (* arm_AESE Q3 Q17 *)
  0x6e201ca5;       (* arm_EOR_VEC Q5 Q5 Q0 128 *)
  0x4e284a3f;       (* arm_AESE Q31 Q17 *)
  0x6e221c68;       (* arm_EOR_VEC Q8 Q3 Q2 128 *)
  0x3d800c45;       (* arm_STR Q5 X2 (Immediate_Offset (word 48)) *)
  0x6e221fe5;       (* arm_EOR_VEC Q5 Q31 Q2 128 *)
  0x6e211d0c;       (* arm_EOR_VEC Q12 Q8 Q1 128 *)
  0x6e2e1ca5;       (* arm_EOR_VEC Q5 Q5 Q14 128 *)
  0x3d80044c;       (* arm_STR Q12 X2 (Immediate_Offset (word 16)) *)
  0x3c840445;       (* arm_STR Q5 X2 (Postimmediate_Offset (word 64)) *)
  0x14000001;       (* arm_B (word 4) *)
  0x3dc000cc;       (* arm_LDR Q12 X6 (Immediate_Offset (word 0)) *)
  0x3dc008cd;       (* arm_LDR Q13 X6 (Immediate_Offset (word 32)) *)
  0x3dc004ce;       (* arm_LDR Q14 X6 (Immediate_Offset (word 16)) *)
  0xb4000729;       (* arm_CBZ X9 (word 228) *)
  0x3cc10408;       (* arm_LDR Q8 X0 (Postimmediate_Offset (word 16)) *)
  0x110001ba;       (* arm_ADD W26 W13 (rvalue (word 0)) *)
  0x110005ad;       (* arm_ADD W13 W13 (rvalue (word 1)) *)
  0x5ac00b58;       (* arm_REV W24 W26 *)
  0xb900aff8;       (* arm_STR W24 SP (Immediate_Offset (word 172)) *)
  0x3dc02be5;       (* arm_LDR Q5 SP (Immediate_Offset (word 160)) *)
  0x4e200903;       (* arm_REV64_VEC Q3 Q8 8 *)
  0x6e3e1c7e;       (* arm_EOR_VEC Q30 Q3 Q30 128 *)
  0x5e1807c9;       (* arm_DUP_ELEM_SCALAR Q9 Q30 1 64 *)
  0x4e284a45;       (* arm_AESE Q5 Q18 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4eece3cd;       (* arm_PMULL2_VEC Q13 Q30 Q12 64 *)
  0x2e3e1d21;       (* arm_EOR_VEC Q1 Q9 Q30 64 *)
  0x4e284a65;       (* arm_AESE Q5 Q19 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x6e0d41bd;       (* arm_EXT Q29 Q13 Q13 64 *)
  0x0eece3cb;       (* arm_PMULL_VEC Q11 Q30 Q12 64 *)
  0x4e284a85;       (* arm_AESE Q5 Q20 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x6e2d1d7f;       (* arm_EOR_VEC Q31 Q11 Q13 128 *)
  0x0ee7e1ad;       (* arm_PMULL_VEC Q13 Q13 Q7 64 *)
  0x4e284aa5;       (* arm_AESE Q5 Q21 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x6e2d1fad;       (* arm_EOR_VEC Q13 Q29 Q13 128 *)
  0x0eeee026;       (* arm_PMULL_VEC Q6 Q1 Q14 64 *)
  0x4e284ac5;       (* arm_AESE Q5 Q22 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x6e3f1cdd;       (* arm_EOR_VEC Q29 Q6 Q31 128 *)
  0x4e284ae5;       (* arm_AESE Q5 Q23 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x6e2d1fad;       (* arm_EOR_VEC Q13 Q29 Q13 128 *)
  0x4e284b05;       (* arm_AESE Q5 Q24 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x6e0d41a0;       (* arm_EXT Q0 Q13 Q13 64 *)
  0x0ee7e1ad;       (* arm_PMULL_VEC Q13 Q13 Q7 64 *)
  0x4e284b25;       (* arm_AESE Q5 Q25 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x6e2d1d7d;       (* arm_EOR_VEC Q29 Q11 Q13 128 *)
  0x4e284b45;       (* arm_AESE Q5 Q26 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x6e201fad;       (* arm_EOR_VEC Q13 Q29 Q0 128 *)
  0x4e284b65;       (* arm_AESE Q5 Q27 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b85;       (* arm_AESE Q5 Q28 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e2849e5;       (* arm_AESE Q5 Q15 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284a05;       (* arm_AESE Q5 Q16 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284a25;       (* arm_AESE Q5 Q17 *)
  0x6e221cbe;       (* arm_EOR_VEC Q30 Q5 Q2 128 *)
  0x6e281fde;       (* arm_EOR_VEC Q30 Q30 Q8 128 *)
  0x3c81045e;       (* arm_STR Q30 X2 (Postimmediate_Offset (word 16)) *)
  0x6e0d41be;       (* arm_EXT Q30 Q13 Q13 64 *)
  0xd1000529;       (* arm_SUB X9 X9 (rvalue (word 1)) *)
  0xb5fff929;       (* arm_CBNZ X9 (word 2096932) *)
  0xaa0f03e0;       (* arm_MOV X0 X15 *)
  0x4e200bde;       (* arm_REV64_VEC Q30 Q30 8 *)
  0x3d80007e;       (* arm_STR Q30 X3 (Immediate_Offset (word 0)) *)
  0x5ac009ae;       (* arm_REV W14 W13 *)
  0xb9000c8e;       (* arm_STR W14 X4 (Immediate_Offset (word 12)) *)
  0x6d4627e8;       (* arm_LDP D8 D9 SP (Immediate_Offset (iword (&96))) *)
  0x6d472fea;       (* arm_LDP D10 D11 SP (Immediate_Offset (iword (&112))) *)
  0x6d4837ec;       (* arm_LDP D12 D13 SP (Immediate_Offset (iword (&128))) *)
  0x6d493fee;       (* arm_LDP D14 D15 SP (Immediate_Offset (iword (&144))) *)
  0xa94053f3;       (* arm_LDP X19 X20 SP (Immediate_Offset (iword (&0))) *)
  0xa9415bf5;       (* arm_LDP X21 X22 SP (Immediate_Offset (iword (&16))) *)
  0xa94263f7;       (* arm_LDP X23 X24 SP (Immediate_Offset (iword (&32))) *)
  0xa9436bf9;       (* arm_LDP X25 X26 SP (Immediate_Offset (iword (&48))) *)
  0xa94473fb;       (* arm_LDP X27 X28 SP (Immediate_Offset (iword (&64))) *)
  0xa9457bfd;       (* arm_LDP X29 X30 SP (Immediate_Offset (iword (&80))) *)
  0x910383ff;       (* arm_ADD SP SP (rvalue (word 224)) *)
  0xd65f03c0        (* arm_RET X30 *)
];;
let AES256_GCM_DEC_EXEC = ARM_MK_EXEC_RULE aes256_gcm_dec_mc;;

(* enc-256 substrate 84-707 *)

(* ------------------------------------------------------------------------- *)
(* Reconstruction of high-level concepts from the computed expressions.      *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Scalar counter representation.  Unlike the vector-IV kernels, this variant *)
(* keeps the counter block in scalar registers: after "ldp x11,x12,[x4]" the *)
(* two 64-bit halves of the (little-endian) IV live in X11 (low) and X12      *)
(* (high); the running counter is byte-reversed out of X12's top word into    *)
(* X13.  The loop rebuilds the reversed counter block via                     *)
(*   w14 = rev(w13);  x14 = orr x12 (w14 lsl 32);  Q0 = word_join x14 x11.     *)
(* These lemmas connect that scalar reconstruction back to ctr_block.         *)

(* Given the initial IV halves (join = reversed ctr_block for counter 2), the *)
(* loop-built block for any counter value equals the reversed ctr_block.      *)

(* Setup-block obligations for the scalar counter registers, phrased directly    *)
(* from the IV-halves join relation so that all widths stay concrete (avoids the  *)
(* type-variable ambiguity that arises if ivhi is substituted before WORD_BLAST). *)

(* Closed form: with X11/X12 written as (counter-free) subwords of the reversed
   ctr_block for the canonical counter 2, the loop-built block for counter cval
   equals the reversed ctr_block for cval.  This is what the loop body invokes. *)

(* Normalisation rules for the scalar counter.  The counter lives in the 32-bit W13 *)
(* view of X13; each "add w13,w13,#1" is a 32-bit add and each read of W13 is a      *)
(* truncation, so counter expressions accumulate word_zx chains.  These two rules    *)
(* (applied alongside WORD_SIMPLE_SUBWORD_CONV while stepping) keep the counter in a *)
(* single-word_zx normal form: ZX_COUNTER_UD kills up-then-down conversions,         *)
(* ZX_COUNTER_INC pushes the 32-bit increment through the extension.                 *)

(* Epilogue byte-splice: the final "str w14,[x4,#12]" overwrites only the top 4 bytes *)
(* of the ivec (the byte-reversed counter word); the low 12 bytes keep their initial  *)
(* value (the reversed nonce from ctr_block nonce c).  Recombining gives the reversed *)
(* ctr_block for the final counter value.                                             *)

(* Same splice phrased for the 64/64 then 32/32 decomposition of the 128-bit ivec    *)
(* read (which is how READ_MEMORY_BYTESIZED_SPLIT breaks it): the stored counter word *)
(* is the top 32 bits of the high 64-bit half, the rest is the unchanged nonce.       *)

(* After the 32-bit-cell split (and collapsing the word_zx conversion chain with     *)
(* ZX_COUNTER_UD), the counter cell (offset 12) is word_bytereverse(word c), which    *)
(* equals the top 32 bits of the reversed ctr_block.                                  *)

(* The low three 32-bit cells of the reversed ivec (the nonce) are independent of the *)
(* counter value, so they still hold their initial (counter-2) contents.              *)

(* This variant assembles the counter block on the STACK: "stp x11,x14,[sp,#OFF]"    *)
(* then "ldr q0,[sp,#OFF]".  The load reads back the two stored halves as            *)
(* word_join x14 x11, which reconstructs the reversed ctr_block.                     *)

(* Each block's counter word is "add w14,w13,#N" from                          *)
(* a fixed base w13, then byte-reversed; the W-register up/down-conversions leave *)
(* a word_zx nest around either the bare base (word (4*i+2), four zx layers) or   *)
(* the offset form word_add (word_zx (word_zx (word (4*i+2)))) (word N).  These   *)
(* two rules (int32) collapse both to word n / word_add (word n) (word m).        *)
(* The s2n-bignum simulator does not auto-merge two 64-bit stores into a       *)
(* 128-bit load, so after "stp x11,x14,[sp,#OFF]" the subsequent               *)
(* "ldr q0,[sp,#OFF]" would leave Q0 symbolic.  This tactic, spliced in AFTER  *)
(* the stp step and BEFORE the ldr step for state s<N>, derives the merged     *)
(* 128-bit read read(bytes128 (sp+OFF)) s<N> = word_join x14 x11 from the two  *)
(* bytes64 store facts, so the simulator can resolve the load against it.      *)

(* Split a 128-bit input-block memory read into two 64-bit halves whose addresses  *)
(* are folded back to the canonical "in_p + word(off)" form.  The scalar_rk final  *)
(* round loads each input block as scalars via "ldp x22,x23,[x0,#K]", i.e. it reads *)
(* the block's two 64-bit halves at x0+K and x0+K+8.  READ_MEMORY_SPLIT_CONV emits  *)
(* the high half at address (in_p + word off) + word 8; the simulator's memory      *)
(* lookup will not match that against x0+K+8 unless we renormalise it to            *)
(* in_p + word(off+8).  NORMALIZE_RELATIVE_ADDRESS_CONV reassociates and GSYM       *)
(* ADD_ASSOC + NUM_ADD_CONV fold the numeric offset.                                *)

(* Tail-loop variant of the input split.  The tail block is loaded by the         *)
(* POST-INDEXED "ldp x22,x23,[x0],#16": the ARM model reads the second register    *)
(* x23 from address in_p + word((64*loop_count + 16*i) + 8) — the "+ 8" stays a    *)
(* separate num-level summand because the block offset (64*loop_count + 16*i) has   *)
(* a symbolic i, so NUM_ADD_CONV cannot fold it.  The plain SPLIT + NORMALISE (no   *)
(* ADD_ASSOC/NUM fold) reproduces exactly that address form, letting the           *)
(* post-indexed load resolve x23 (offset-mode loads in the main loop DO fold, hence *)
(* the two different conversions).                                                 *)

(*** Direct implementation of AES256 using the hardware primitives ***)
(*** 14 rounds: aese for rk0..rk13 (13 aesmc/aese pairs after the initial   ***)
(*** aese plaintext rk0), then the final round key rk14 XORed in.           ***)

(*** This is the sequence in the code, folding an XOR in sooner ***)

(* In the scalar_rk variant the final AES round key (EL 10) is XORed in scalar    *)
(* registers X20/X21 into the input block halves, and the block ciphertext is     *)
(* word_xor (word_join <input_hi ^ key10_hi> <input_lo ^ key10_lo>) (9-round Q0). *)
(* This lemma rewrites that scalar-built form into the word_xor <9round>           *)
(* (word_xor rk10 inblock) shape that XOR_AES256_CIPHER_RECONSTRUCT consumes,      *)
(* with rk10 = word_reversefields 8 (EL 10 rk) and inblock = word_join of the      *)
(* input halves.  Both operand orders of the outer word_xor are covered: the       *)
(* ciphertext-output copy keeps the (word_join ... ) nineround order from the       *)
(* "eor v0,v29,v0", while the GHASH-accumulated copy has the operands commuted by   *)
(* the intervening normalisation, so we need both orientations.                     *)

(* ---- GHASH reduce-reconstruction lemmas (mc-agnostic, shared with the AES-128 proof) ---- *)

(* ------------------------------------------------------------------------- *)
(* Variants of the existing Karatsuba lemmas better fitting the code.        *)
(* ------------------------------------------------------------------------- *)

(* ========================================================================= *)
(* Keystream-fold + counter/lane helper lemmas (256 analogs of the 128       *)
(* KEYSTREAM_FOLD / CT_TO_NCB / JOIN_* / mk_cbv, re-indexed to rk14/EL14).    *)
(* ========================================================================= *)

(* --- dec-256 carry-depth AES abstractions (Q3=aes12c depth-12, Q8=aes5c depth-5) + aes14p bridges --- *)
let aes5c = new_definition
 `aes5c nonce (rk:int128 list) c : int128 =
    aesmc(aese (aesmc(aese (aesmc(aese (aesmc(aese (aesmc(aese
     (word_reversefields 8 (ctr_block nonce c))
     (word_reversefields 8 (EL 0 rk))))
     (word_reversefields 8 (EL 1 rk))))
     (word_reversefields 8 (EL 2 rk))))
     (word_reversefields 8 (EL 3 rk))))
     (word_reversefields 8 (EL 4 rk)))`;;
let aes12c = new_definition
 `aes12c nonce (rk:int128 list) c : int128 =
    aesmc(aese(aesmc(aese(aesmc(aese(aesmc(aese(aesmc(aese(aesmc(aese
     (aesmc(aese(aesmc(aese(aesmc(aese(aesmc(aese(aesmc(aese(aesmc(aese
      (word_reversefields 8 (ctr_block nonce c))
      (word_reversefields 8 (EL 0 rk))))(word_reversefields 8 (EL 1 rk))))
      (word_reversefields 8 (EL 2 rk))))(word_reversefields 8 (EL 3 rk))))
      (word_reversefields 8 (EL 4 rk))))(word_reversefields 8 (EL 5 rk))))
      (word_reversefields 8 (EL 6 rk))))(word_reversefields 8 (EL 7 rk))))
      (word_reversefields 8 (EL 8 rk))))(word_reversefields 8 (EL 9 rk))))
      (word_reversefields 8 (EL 10 rk))))(word_reversefields 8 (EL 11 rk)))`;;
let AES14P_VIA_AES12C = prove
 (`aes14p nonce rk c =
   aese(aesmc(aese (aes12c nonce rk c) (word_reversefields 8 (EL 12 rk))))
     (word_reversefields 8 (EL 13 rk))`,
  REWRITE_TAC[aes14p; aes12c]);;
let AES14P_VIA_AES5C = prove
 (`aes14p nonce rk c =
   aese(aesmc(aese(aesmc(aese(aesmc(aese(aesmc(aese(aesmc(aese(aesmc(aese(aesmc(aese(aesmc(aese
     (aes5c nonce rk c) (word_reversefields 8 (EL 5 rk))))
     (word_reversefields 8 (EL 6 rk))))(word_reversefields 8 (EL 7 rk))))
     (word_reversefields 8 (EL 8 rk))))(word_reversefields 8 (EL 9 rk))))
     (word_reversefields 8 (EL 10 rk))))(word_reversefields 8 (EL 11 rk))))
     (word_reversefields 8 (EL 12 rk))))(word_reversefields 8 (EL 13 rk))`,
  REWRITE_TAC[aes14p; aes5c]);;

(* dec-ordered keystream fold: the DECRYPT machine value is word_xor inblock (word_xor rk14 <tower>)
   (see XOR_AES256_CIPHER_RECONSTRUCT_DEC), so after folding <tower> -> aes14p the LHS XOR order is
   inb outer / aes14p inner -- the transpose of KEYSTREAM_FOLD256.  Same RHS.  Proved identically
   (AES14P_COMPLETE + WORD_BITWISE_RULE, ONCE at load, symbolic c).  Lets the output-block closer fold
   forward by pure rewriting instead of a use-time CONV_TAC WORD_BITWISE_RULE (which bit-blasts word c). *)
let KEYSTREAM_FOLD256_DEC = prove
 (`[EL 0 rk; EL 1 rk; EL 2 rk; EL 3 rk; EL 4 rk; EL 5 rk; EL 6 rk; EL 7 rk;
    EL 8 rk; EL 9 rk; EL 10 rk; EL 11 rk; EL 12 rk; EL 13 rk; EL 14 rk]:(int128)list = rk
   ==> word_xor inb (word_xor (word_reversefields 8 (EL 14 rk)) (aes14p nonce rk c))
       = word_xor (word_reversefields 8 (aes256_cipher (ctr_block nonce c) rk)) inb`,
  DISCH_THEN(fun th -> MP_TAC(MATCH_MP AES14P_COMPLETE th)) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN CONV_TAC WORD_BITWISE_RULE);;

(* ciphertext -> nist_cipher_block: word_xor(rev8(cipher(ctr(j+2))))(inblock j) = rev8(nist_cipher_block j). *)

(* lane recombine (mc-agnostic, verbatim from 128). *)

(* dec-256 stepping infrastructure ported from enc-256 *)
(* The 2-level split -- the str-w
   pattern (dec-256's) needs BOTH the bytes128->bytes64 split AND the bytes64@+8 ->
   bytes32 split, so the counter-word lane (bytes32 @ +12) and the nonce lanes (bytes64 @ +0, bytes32 @ +8)
   are all exposed and resolve against the surviving reads.  The old 1-level version only split bytes128->bytes64
   and left the +8/+12 lanes unresolved -- THE bug. *)
(* Assumption-list GC (DISCARD_STALE_TAC, shared in aes_gcm_utils.ml): drop a fact about
   an OLD state when the same fact modulo the state var already holds of the current state and no OTHER
   assumption pins that old state.  A fact "refers to" a state that occurs in it OTHER than as the state its
   own left-hand read is about (so `read Q5 s148 = ..read(mem..)s99..` protects s99, not s148).  Appended to
   gkeepN so the stale-state forall region-invariants + multi-state derived facts do not accumulate across a
   leg (the per-register pruner keeps them); without this every ARM_STEP + ASM_REWRITE is linear in the asl,
   giving quadratic leg cost.  ~9x speedup on the 256 enc SWP proof. *)
(* Q14 holds the GHASH block-0 input (inblock(4i)); its value is referenced by the Q30 accumulator tower at an
   EARLY state (read Q14 s10) but Q14 is later overwritten (AES scratch + next-group reload).  gc2's latest-only
   pruning would drop the early `read Q14 s0 = inblock(4i)` fact, leaving the tower's `read Q14 s10` unfoldable
   -> the 800-var block-0 byte-tower blowup in the seed closer.  Exempt `read Q14 sK` from BOTH prunings (like
   in_p) so the block-0 fact survives for the seed closer to fold. Cheap: Q14 has few states. *)
let is_q14_read c = try (match lhs c with
    Comb(Comb(Const("read",_),Const("Q14",_)),_) -> true | _ -> false) with _ -> false;;
(* Per-step assumption pruner for the staged-counter stepper.  The staged-counter
   staged counter blocks live at stack offsets 160/176/192/208; their block-base reads must be ANCHORED
   (kept across states) so read-over-write resolves the staged blocks at the body-end (the plain gkeepN's
   latest-only pruning dropped them -> SP_SLOT/AES/out closers failed).  is_spctr_read anchors ONLY the 4
   block-base reads (NOT +8/+12 lanes or bytes8 components -> no bloat).  Also anchor tag_p/ivec_p/htable_p
   reads + handle the in_p/out_p frame foralls (keep) like dec-128.  The stale-fact GC (DISCARD_STALE_TAC)
   runs after this pruning: the anchored reads and frame foralls are re-derived by every ARM_STEP_TAC, and
   without the GC their old-state copies accumulate (about 20 facts per step, so several thousand over a
   leg), making each step and each closer linear in the leg length and the leg itself quadratic. *)
let is_spctr_read c = try
    let l = lhs c in
    fst(dest_const(fst(strip_comb l)))="read" && free_in `stackpointer:int64` l &&
    (can (find_term (fun t -> match t with
       | Comb(Comb(Const("word_add",_),sp),Comb(Const("word",_),n))
           when (try fst(dest_var sp)="stackpointer" with _->false) ->
             (try let v=dest_small_numeral n in v=160||v=176||v=192||v=208 with _ -> false) | _ -> false)) l)
  with _ -> false;;
(* state index of a `read _ sK = _` fact (K), or -1 *)
let read_state_idx c = try (match lhs c with
   Comb(Comb(Const("read",_),_),Var(nm,_)) when String.length nm>=2 && nm.[0]='s' ->
     int_of_string(String.sub nm 1 (String.length nm-1)) | _ -> -1) with _ -> -1;;
(* spctr block-base offset (160/176/192/208) of a read fact, or -1 *)
let spctr_off c = try (match find_terms (fun t -> match t with
     Comb(Comb(Const("word_add",_),sp),Comb(Const("word",_),n)) when (try fst(dest_var sp)="stackpointer" with _->false)
       -> (let v=dest_small_numeral n in v=160||v=176||v=192||v=208) | _ -> false) (lhs c) with
   | (Comb(Comb(_,_),Comb(_,n)))::_ -> dest_small_numeral n | _ -> -1) with _ -> -1;;
(* The staged-block closer primes constant nonce lanes at s0:
     read(bytes64 sp+{160,176,192,208})s0 = subword(rev8(ctr_block nonce c))(0,64)   [lo]
     read(bytes32 sp+{168,184,200,216})s0 = subword(rev8(ctr_block nonce c))(64,32)  [mid]
   These are s0-anchored CONSTANTS (never written by the body -- only the +12 counter lane is), needed at the
   per-slot MERGE (steps 16/20/32/35).  is_spctr_read/spmx anchors ONLY the bytes128 block reads at
   160/176/192/208 and its latest-per-OFFSET pruning would drop these (mid-lanes at 168.. aren't matched at all;
   lo-lanes conflate with the bytes128 baseline at the same offset).  is_ctrlane_read matches them by the exact
   lane offset set {160,176,192,208,168,184,200,216} AND requires the RHS to be a subword-of-ctr_block-2 (the
   primed constant form) so it only ever protects the priming facts, never a transient read. *)
(* APPROACH E: the primed lanes have VARIABLE RHS (ivlo | word_subword ivhi (0,32)) -- NOT the compound
   word_subword(rev8(ctr_block 2))(..) form (which crashes native ARM_STEP).  Match those. *)
let is_ctrlane_read c =
  try
    let l = lhs c in
    let headok = fst(dest_const(fst(strip_comb l))) = "read" in
    let spok = free_in `stackpointer:int64` l in
    let offpred t = match t with
       | Comb(Comb(Const("word_add",_),sp),Comb(Const("word",_),n)) ->
           (try (fst(dest_var sp) = "stackpointer") &&
                (let v = dest_small_numeral n in
                 v=160||v=176||v=192||v=208||v=168||v=184||v=200||v=216)
            with _ -> false)
       | _ -> false in
    (* RHS is ivlo (a variable) or word_subword ivhi (0,32) -- the Approach-E variable-form nonce lane.
       Tested last and lazily: the RHS of a carried fact can be a large tower. *)
    let rhsok () = let r = rhs c in
                (try fst(dest_var r) = "ivlo" with _ -> false) ||
                (free_in `ivhi:int64` r &&
                 can (find_term (fun t -> match t with Const("word_subword",_) -> true | _ -> false)) r) in
    headok && spok && (can (find_term offpred) l) && rhsok ()
  with _ -> false;;
(* address-modulo-state KEY of a ctrlane read (the lhs component, i.e. the (:>) comb, ignoring the state var):
   distinguishes bytes64@192 from bytes32@200 etc. so per-lane latest-state pruning doesn't conflate them. *)
let ctrlane_key c = try let l = lhs c in fst(dest_comb l) with _ -> `T`;;
(* Pruning policy of the dec-256 stepper: the tag_p/ivec_p/htable_p/in_p reads and the Q14 reads always
   kept, the staged counter slots (per offset) and the primed nonce lanes (per lane) kept latest-only,
   current-state foralls only, with the stale sweep (see aes_gcm_utils.ml SWP_STEP_TAC_P). *)
let dec_prune =
  { anchors = [`tag_p:int64`; `ivec_p:int64`; `htable_p:int64`; `in_p:int64`]; slots = [];
    families =
     [(fun c -> if is_ctrlane_read c then Some(string_of_term(ctrlane_key c), read_state_idx c) else None);
      (fun c -> if is_spctr_read c then Some(string_of_int(spctr_off c), read_state_idx c) else None)];
    exempt = is_q14_read; all_foralls = false; stale_gc = true };;
let gkeepN keeplist th sname = SWP_STEP_TAC_P dec_prune keeplist th sname;;
(* One pruned symbolic step followed by the per-step assumption normalisation (subword *)
(* nests, relative addresses, in_p offsets).  DEC_STEPS_TAC runs a range of steps with  *)
(* a per-step hook (staged counter-slot merges, lane priming) after each one.           *)

let DEC_NORM_ASM_TAC : tactic =
  RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV THENC
                           ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV THENC IN_P_ADDR_FOLD_CONV));;

let DEC_STEP_TAC keep k : tactic =
  gkeepN keep AES256_GCM_DEC_EXEC ("s"^string_of_int k) THEN DEC_NORM_ASM_TAC;;

let DEC_STEPS_TAC keep (hook:int->tactic) ks : tactic =
  fun g -> MAP_EVERY (fun k -> DEC_STEP_TAC keep k THEN hook k) ks g;;

(* The hook that applies a staged counter-slot merge at its store step. *)

let merge_hook merges mk k : tactic =
  match filter (fun (kk,_,_) -> kk = k) merges with
  | (_,off,cval)::_ -> mk off cval ("s"^string_of_int k)
  | [] -> ALL_TAC;;

(* 256 carried/reduce reg-set: AES partials Q3/Q4/Q8 + reduce Q1/Q2/Q11/Q13/Q14/Q29/Q30 + h-powers
   (REDSETX_DEC, ghost_lanes_dec and the merge tables are defined with the body leg below). *)
let contains sub s =
  let ls = String.length s and lsub = String.length sub in
  let rec go i = if i+lsub > ls then false
    else if String.sub s i lsub = sub then true else go (i+1) in go 0;;
(* swp_inv: dec-256 SWP mid-pipeline invariant (53 conjuncts).
   Q10/Q11's 2nd term is byteswap128(h_power 0) (not a nested pmul)
   -- this made the whole GHASH pipeline (incl Q30 accumulator) numerically consistent; body-leg valid. *)

let swp_inv : term =
  `\i s.
    read X3 s = tag_p /\
    read X4 s = ivec_p /\
    read X6 s = htable_p /\
    read SP s = stackpointer /\
    read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
    read (memory :> bytes128 ivec_p) s =
    word_reversefields 8 (ctr_block nonce c) /\
    read Q18 s = word_reversefields 8 (EL 0 rk) /\
    read Q19 s = word_reversefields 8 (EL 1 rk) /\
    read Q20 s = word_reversefields 8 (EL 2 rk) /\
    read Q21 s = word_reversefields 8 (EL 3 rk) /\
    read Q22 s = word_reversefields 8 (EL 4 rk) /\
    read Q23 s = word_reversefields 8 (EL 5 rk) /\
    read Q24 s = word_reversefields 8 (EL 6 rk) /\
    read Q25 s = word_reversefields 8 (EL 7 rk) /\
    read Q26 s = word_reversefields 8 (EL 8 rk) /\
    read Q27 s = word_reversefields 8 (EL 9 rk) /\
    read Q28 s = word_reversefields 8 (EL 10 rk) /\
    read Q15 s = word_reversefields 8 (EL 11 rk) /\
    read Q16 s = word_reversefields 8 (EL 12 rk) /\
    read Q17 s = word_reversefields 8 (EL 13 rk) /\
    read Q2 s = word_reversefields 8 (EL 14 rk) /\
    read Q7 s = word 13979173243358019584 /\
    htable_mem_4 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s /\
    (forall j.
         j < nblocks
         ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
             inblock j) /\
    read X0 s = word_add in_p (word (64 * (i + 1))) /\
    read X2 s = word_add out_p (word (64 * i)) /\
    read X1 s = word (loop_count - (i + 1)) /\
    read X15 s = word (len_bits DIV 8) /\
    read X9 s = word loop_remain /\
    read X13 s = word_zx (word (4 * i + c):int32) /\
    read (memory :> bytes128 (word_add stackpointer (word 160))) s =
    word_reversefields 8 (ctr_block nonce (4 * i + c)) /\
    read (memory :> bytes128 (word_add stackpointer (word 176))) s =
    word_reversefields 8 (ctr_block nonce (4 * i + c + 1)) /\
    read (memory :> bytes128 (word_add stackpointer (word 192))) s =
    word_reversefields 8 (ctr_block nonce (4 * i + c + 2)) /\
    read (memory :> bytes128 (word_add stackpointer (word 208))) s =
    word_reversefields 8 (ctr_block nonce (4 * i + c + 3)) /\
    (forall j.
         j < 4 * i
         ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
             word_xor (aes256_ctr_block c nonce rk j) (inblock j)) /\
    read (memory :> bytes128 (word_add out_p (word (64 * i + 32)))) s =
    word_xor (aes256_ctr_block c nonce rk (4 * i + 2)) (inblock (4 * i + 2)) /\
    read Q30 s =
    word_join
    (word_subword
     (nist_ghash (aes256_cipher (word 0) rk) tag0
     (list_of_seq (nist_input_block inblock) (4 * i)))
     (0,64):int64)
    (word_subword
     (nist_ghash (aes256_cipher (word 0) rk) tag0
     (list_of_seq (nist_input_block inblock) (4 * i)))
     (64,64):int64) /\
    read Q3 s = aes12c nonce rk (4 * i + c + 1) /\
    read Q8 s = aes5c nonce rk (4 * i + c + 3) /\
    read Q0 s = inblock (4 * i + 3) /\
    read Q1 s = inblock (4 * i + 1) /\
    read Q13 s =
    word_join
    (karatsuba_mid (h_power (ghash_twist (aes256_cipher (word 0) rk)) 3))
    (karatsuba_mid (h_power (ghash_twist (aes256_cipher (word 0) rk)) 2)) /\
    read Q29 s =
    byteswap128 (h_power (ghash_twist (aes256_cipher (word 0) rk)) 3) /\
    read Q31 s = word_reversefields 8 (ctr_block nonce (4 * i + c)) /\
    read Q4 s =
    word_zx
    (word_subword
     (word_xor
      (word_join
       (word_subword (word_reversefields 8 (inblock (4 * i + 1))) (0,64):int64)
      (word_subword (word_reversefields 8 (inblock (4 * i + 1))) (64,64):int64))
     (word_zx
      (word_subword (word_reversefields 8 (inblock (4 * i + 1))) (0,64):int64):int128))
     (0,64):int64) /\
    read Q5 s =
    word_pmul
    (word_subword (word_reversefields 8 (inblock (4 * i + 1))) (0,64):int64)
    (word_subword
     (byteswap128 (h_power (ghash_twist (aes256_cipher (word 0) rk)) 2))
     (64,64):int64) /\
    read Q6 s =
    word_xor
    (word_pmul
     (word_subword
      (word_xor
       (word_join
        (word_subword (word_reversefields 8 (inblock (4 * i + 2))) (0,64):int64)
       (word_subword (word_reversefields 8 (inblock (4 * i + 2))) (64,64):int64))
      (word_subword
       (word_join
        (word_join
         (word_subword (word_reversefields 8 (inblock (4 * i + 2))) (0,64):int64)
         (word_subword (word_reversefields 8 (inblock (4 * i + 2))) (64,64):int64):int128)
        (word_join
         (word_subword (word_reversefields 8 (inblock (4 * i + 2))) (0,64):int64)
         (word_subword (word_reversefields 8 (inblock (4 * i + 2))) (64,64):int64):int128):int256)
       (64,128):int128))
      (64,64):int64)
    (word_subword
     (word_join
      (karatsuba_mid (h_power (ghash_twist (aes256_cipher (word 0) rk)) 1))
      (karatsuba_mid (h_power (ghash_twist (aes256_cipher (word 0) rk)) 0)):int128)
     (64,64):int64))
    (word_pmul
     (word_subword
      (word_xor
       (word_join
        (word_subword (word_reversefields 8 (inblock (4 * i + 3))) (0,64):int64)
       (word_subword (word_reversefields 8 (inblock (4 * i + 3))) (64,64):int64))
      (word_zx
       (word_subword (word_reversefields 8 (inblock (4 * i + 3))) (0,64):int64):int128))
      (0,64):int64)
    (word_subword
     (word_join
      (karatsuba_mid (h_power (ghash_twist (aes256_cipher (word 0) rk)) 1))
      (karatsuba_mid (h_power (ghash_twist (aes256_cipher (word 0) rk)) 0)):int128)
     (0,64):int64)) /\
    read Q9 s =
    word_pmul
    (word_subword (word_reversefields 8 (inblock (4 * i + 1))) (64,64):int64)
    (word_subword
     (byteswap128 (h_power (ghash_twist (aes256_cipher (word 0) rk)) 2))
     (0,64):int64) /\
    read Q10 s =
    word_xor
    (word_pmul
     (word_subword (word_reversefields 8 (inblock (4 * i + 2))) (64,64):int64)
    (word_subword
     (byteswap128 (h_power (ghash_twist (aes256_cipher (word 0) rk)) 1))
     (0,64):int64))
    (word_pmul
     (word_subword (word_reversefields 8 (inblock (4 * i + 3))) (64,64):int64)
    (word_subword
     (byteswap128 (h_power (ghash_twist (aes256_cipher (word 0) rk)) 0))
     (0,64):int64)) /\
    read Q11 s =
    word_xor
    (word_pmul
     (word_subword (word_reversefields 8 (inblock (4 * i + 2))) (0,64):int64)
    (word_subword
     (byteswap128 (h_power (ghash_twist (aes256_cipher (word 0) rk)) 1))
     (64,64):int64))
    (word_pmul
     (word_subword (word_reversefields 8 (inblock (4 * i + 3))) (0,64):int64)
    (word_subword
     (byteswap128 (h_power (ghash_twist (aes256_cipher (word 0) rk)) 0))
     (64,64):int64)) /\
    read Q14 s = inblock (4 * i)`;;
(* ============================================================================
   dec-256 SWP BODYLEG closers: the extra lemmas (ported from dec-128, adapted
   aes128->aes256) + the dispatcher CLOSE_DEC.
   Requires: front-matter (aes256_cipher/nist_ghash/h_power/karatsuba_mid/
   polyval_reduce_g2/RECONSTRUCT_POLYVAL_REDUCE_G2/POLYVAL_REDUCE_G2/
   PMUL_KARATSUBA_JOIN_ALT/INBLOCK_REASSEMBLE/DEC_GHASH_NORM_TAC/aesNc/
   AES14P_VIA_*/KEYSTREAM_FOLD256/CT_TO_NCB256/CTR_BLOCK_BUILD_INSERT/
   XOR_AES256_CIPHER_RECONSTRUCT/mk_cbv/ZX_COUNTER_UD/ZX_COUNTER_INC/CTR_ZX_NORM)
   + swp_inv + body_goal_dec + steppers (gkeepN etc.) all loaded.
   ============================================================================ *)

(* --- ported GHASH/AES/arith building blocks --- *)

(* the crux batched GHASH-reduce identity (aes256): the 4-block Horner accumulator step. *)
let SWP_GHASH_BRANCH2_256 = prove
 (`polyval_reduce_prop3
     (word_xor (word_pmul (nist_input_block inblock (4*i+3):int128)
                          (h_power (ghash_twist (aes256_cipher (word 0) rk)) 0))
     (word_xor (word_pmul (nist_input_block inblock (4*i+2))
                          (h_power (ghash_twist (aes256_cipher (word 0) rk)) 1))
     (word_xor (word_pmul (nist_input_block inblock (4*i+1))
                          (h_power (ghash_twist (aes256_cipher (word 0) rk)) 2))
     (word_pmul (word_xor (nist_ghash (aes256_cipher (word 0) rk) tag0
                              (list_of_seq (nist_input_block inblock) (4*i)))
                          (nist_input_block inblock (4*i)))
                (h_power (ghash_twist (aes256_cipher (word 0) rk)) 3)))))
   = nist_ghash (aes256_cipher (word 0) rk) tag0
       (list_of_seq (nist_input_block inblock) (4*i+4))`,
  MP_TAC(ISPECL [`ghash_twist (aes256_cipher (word 0) rk)`;
                 `[nist_input_block inblock (4*i+1); nist_input_block inblock (4*i+2); nist_input_block inblock (4*i+3)]:(int128)list`;
                 `nist_ghash (aes256_cipher (word 0) rk) tag0 (list_of_seq (nist_input_block inblock) (4*i)):int128`;
                 `nist_input_block inblock (4*i):int128`] GHASH_POLYVAL_ACC_BATCHED) THEN
  REWRITE_TAC[LENGTH; ghash_wide] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[NIST_GHASH_IS_POLYVAL] THEN
  REWRITE_TAC[ARITH_RULE `4 * i + 4 = SUC(SUC(SUC(SUC(4 * i))))`] THEN
  REWRITE_TAC[list_of_seq] THEN REWRITE_TAC[GSYM APPEND_ASSOC; APPEND] THEN
  REWRITE_TAC[GHASH_ACC_APPEND] THEN
  REWRITE_TAC[ADD1; GSYM ADD_ASSOC] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[GSYM NIST_GHASH_IS_POLYVAL] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN AP_TERM_TAC THEN CONV_TAC WORD_BITWISE_RULE);;

(* dec out-store readback (14-round, aes256): word_xor inblock (word_xor rk14 (aese-tower))
   = word_xor (rev8(aes256_cipher(rev8 plaintext) rk-list)) inblock. *)
let XOR_AES256_CIPHER_RECONSTRUCT_DEC = prove
 (`word_xor inblock (word_xor rk14
     (aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc
      (aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc
      (aese (aesmc (aese plaintext rk0)) rk1)) rk2)) rk3)) rk4)) rk5)) rk6)) rk7))
      rk8)) rk9)) rk10)) rk11)) rk12)) rk13)) =
   word_xor
   (word_reversefields 8
   (aes256_cipher (word_reversefields 8 plaintext)
   (MAP (word_reversefields 8)
   [rk0; rk1; rk2; rk3; rk4; rk5; rk6; rk7; rk8; rk9; rk10; rk11; rk12; rk13; rk14])))
   inblock`,
  ONCE_REWRITE_TAC[GSYM XOR_AES256_CIPHER_RECONSTRUCT] THEN
  CONV_TAC WORD_BITWISE_RULE);;

(* X1 decrement matched to the invariant form word(loop_count-(i+1)). *)
let SWP_SUB_LEMMA_DEC = prove
 (`i < loop_count - 2 ==> word_sub (word (loop_count - (i+1)):int64) (word 1) = word (loop_count - ((i+1)+1))`,
  DISCH_TAC THEN SUBGOAL_THEN `loop_count - ((i+1)+1) = (loop_count - (i+1)) - 1` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[WORD_SUB; ARITH_RULE `i < loop_count - 2 ==> 1 <= loop_count - (i+1)`]);;

let SWP_SUB_LEMMA_DEC_L1 = prove
 (`i < loop_count - 1
   ==> word_sub (word (loop_count - (i + 1))) (word 1):int64 = word (loop_count - ((i + 1) + 1))`,
  DISCH_TAC THEN SUBGOAL_THEN `loop_count - ((i+1)+1) = (loop_count - (i+1)) - 1 /\ 1 <= loop_count - (i+1)`
    STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `i < loop_count - 1` THEN ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[WORD_SUB; VAL_WORD_1] THEN
  REWRITE_TAC[GSYM VAL_WORD_1] THEN AP_TERM_TAC THEN UNDISCH_TAC `i < loop_count - 1` THEN ARITH_TAC);;

(* ============================================================================
   SWP pipelined-accumulator machinery (ported from the enc-256-swp proof).
   The dec-256 loop-head Q30 is NOT the settled nist_ghash..4(i+1) (that conjunct is
   FALSE -- HOL-certified: the machine reduce at loop head is a pipelined partial, not
   the settled group-accumulator).  swpgrp = the abstract recursive Horner accumulator;
   SWPGRP_IS_NIST_GHASH bridges it to nist_ghash at DRAIN. *)

(* The exploratory algebraic-toolkit lemmas (PSB/PMUL_LANE_LO/PROP3_LANES/PROP3_GEN) were
   REMOVED -- the final seed proof (SEED_AC_CLOSE_TAC + G2_IS_PROP3, below) does NOT use them, and
   PROP3_LANES' hand-written RHS was a fragile normal-form that failed REFL_TAC under the native
   let_CONV/WORD_SIMPLE_SUBWORD_CONV output ordering.  The seed is closed WITHOUT them. *)

(* ============================================================================
   SEED CLOSER (John's algebraic route: poly-const NEVER bit-blasted).
   The Q30 body-end seed reduces to:  machwj = byteswap128(polyval_reduce_prop3 simple)
   where machwj = the machine's word_join reduce over the 9 lanes vacc/vcb0..3/vh0..3, and
   simple = word_xor(pmul cb3 h0)(xor(pmul cb2 h1)(xor(pmul cb1 h2)(pmul(xor acc cb0) h3))).
   TWO axiom-free lemmas over the 9 free lanes:
     (a) MACHWJ = byteswap128(polyval_reduce_g2 <karatsuba towers>)   -- SEED_AC_CLOSE_TAC
     (b) polyval_reduce_g2 <towers> = polyval_reduce_prop3 simple      -- CORE_REDUCE branch1 (G2_IS_PROP3)
   Chain (a) o AP_TERM byteswap128 (b) = the seed.  KEY: the poly-const word_pmul _ (word 0xC2..)
   is only ever an OPAQUE shared atom -- it is unified across machine/prop3 sides by AC-xor of its
   argument (POLYARG_UNIFY), never expanded, so WORD_BLAST/BITBLAST never sees the carryless mult. *)

(* fast AC-xor prover (linear GF(2), NOT bit-blasting). Closes word_xor-tree = word_xor-tree over atoms. *)
let WORD_XOR_AC_THM = prove
 (`word_xor x y = word_xor y x /\
   word_xor (word_xor x y) z = word_xor x (word_xor y z) /\
   word_xor x (word_xor y z) = word_xor y (word_xor x z)`,
  REWRITE_TAC[WORD_XOR_ASSOC] THEN REPEAT CONJ_TAC THEN CONV_TAC WORD_BITWISE_RULE);;

(* karatsuba-mid fold for a 2-term xor base (the acc-lane mid factor): folds the machine's
   word_xor(word_xor(sw a 0)(sw b 0))(word_xor(sw a 64)(sw b 64)) to karatsuba_mid(word_xor a b). *)
let CMID_XOR2 = prove
 (`word_xor (word_xor (word_subword (a:int128) (0,64)) (word_subword (b:int128) (0,64)))
            (word_xor (word_subword a (64,64)) (word_subword b (64,64))):int64
   = karatsuba_mid (word_xor a b)`,
  REWRITE_TAC[karatsuba_mid; WORD_SUBWORD_XOR] THEN CONV_TAC WORD_BITWISE_RULE);;

(* word_subword of a 64|64 word_join (collapse g2's LO/HI-of-join on the RHS). *)
let SJ_LO = WORD_BLAST `word_subword(word_join (h:int64) (l:int64):int128)(0,64):int64 = l`;;
let SJ_HI = WORD_BLAST `word_subword(word_join (h:int64) (l:int64):int128)(64,64):int64 = h`;;

(* POLYARG_UNIFY_TAC: deterministic one-pass unifier for the poly-const mults.  Finds poly-const
   word_pmul's whose argument word_xor-trees have the SAME leaf-multiset (nested poly-const subwords
   treated as atoms), proves arg-equality by the AC prover, lifts to a word_pmul equality (AP_THM/AP_TERM),
   and PURE_REWRITEs.  Apply TWICE: pass 1 unifies the inner (w1) mult so the outer (w2) args' nested
   subwords coincide; pass 2 unifies w2.  After both passes the 2 machine poly-const mults are
   syntactically identical to prop3's -> abstract as opaque + BINOP + AC closes with zero blasting. *)
let POLYARG_UNIFY_TAC : tactic = fun (asl,w) ->
  let poly = `word 13979173243358019584:int64` in
  let is_pc t = match strip_comb t with Const("word_pmul",_),[_;b]->b=poly|_->false in
  let rec flatten_xor t = match t with
    | Comb(Comb(Const("word_xor",_),a),b) -> flatten_xor a @ flatten_xor b | _ -> [t] in
  let key t = sort (<=) (map string_of_term (flatten_xor (el 0 (snd(strip_comb t))))) in
  let pcs = sort (fun a b -> String.length(string_of_term a) <= String.length(string_of_term b))
                 (setify (find_terms is_pc w)) in
  let eqs = ref [] and seen = ref [] in
  List.iter (fun t ->
     let k = key t in
     match (try Some(assoc k !seen) with _ -> None) with
     | Some rep -> if not(aconv t rep) then
         (let arga = el 0 (snd(strip_comb rep)) and argb = el 0 (snd(strip_comb t)) in
          let argeq = prove(mk_eq(argb,arga),
            (fun g -> let is_pcsub s = match s with Comb(Comb(Const("word_subword",_),bd),_)->is_pc bd|_->false in
               let subs = setify(find_terms is_pcsub (mk_eq(argb,arga))) in
               (EVERY(List.mapi (fun i s->ABBREV_TAC(mk_eq(mk_var(Printf.sprintf "Z_%d" i,type_of s),s))) subs)) g)
            THEN POP_ASSUM_LIST(K ALL_TAC) THEN CONV_TAC(AC WORD_XOR_AC_THM)) in
          eqs := (AP_THM (AP_TERM `word_pmul:int64->int64->int128` argeq) poly) :: !eqs)
     | None -> seen := (k,t) :: !seen) pcs;
  (if !eqs = [] then ALL_TAC else PURE_REWRITE_TAC !eqs) (asl,w);;

(* SEED_AC_CLOSE_TAC: closes  machwj = byteswap128(polyval_reduce_g2 <towers>)  in ~1.2s, no blasting.
   Unfold g2/byteswap, fold both sides to atomic word_xor-of-64x64-lane form (leaves L_i, karatsuba_mid
   kept folded so mid-lanes are single atoms), unify the 2 poly-const mults by AC (POLYARG x2), abstract
   the shared pmuls+subwords as opaque, split the top word_join (BINOP), close each half by AC-xor. *)
let SEED_AC_CLOSE_TAC : tactic =
  REWRITE_TAC[polyval_reduce_g2; byteswap128] THEN
  CONV_TAC(RAND_CONV(TOP_DEPTH_CONV let_CONV)) THEN
  REWRITE_TAC[CMID_HILO; CMID_LOHI; CMID_XOR2] THEN
  (fun (asl,w) ->
     let is_leaf t = match t with
       | Comb(Comb(Const("word_subword",_),b),_) ->
           (match strip_comb b with Const("word_pmul",_),[_;bb] -> bb <> `word 13979173243358019584:int64` | _ -> false)
       | _ -> false in
     let leaves = setify (find_terms is_leaf w) in
     (EVERY (List.mapi (fun i t -> ABBREV_TAC(mk_eq(mk_var(Printf.sprintf "L_%d" i,type_of t),t))) leaves)) (asl,w)) THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[CMID_HILO; CMID_LOHI; CMID_XOR2] THEN
  REWRITE_TAC[WORD_SUBWORD_XOR] THEN
  REWRITE_TAC[SJ_LO; SJ_HI] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[CMID_HILO; CMID_LOHI; CMID_XOR2] THEN
  REWRITE_TAC[WORD_SUBWORD_XOR] THEN
  ASM_REWRITE_TAC[] THEN
  POLYARG_UNIFY_TAC THEN POLYARG_UNIFY_TAC THEN
  (fun (asl,w) ->
     let is_pmul t = match strip_comb t with Const("word_pmul",_),[_;_]->true|_->false in
     let pms = sort (fun a b -> String.length(string_of_term a) <= String.length(string_of_term b))
                    (setify(find_terms is_pmul w)) in
     (EVERY (List.mapi (fun i t -> ABBREV_TAC(mk_eq(mk_var(Printf.sprintf "QC_%d" i,type_of t),t))) pms)) (asl,w)) THEN
  (fun (asl,w) ->
     let is_sub t = match t with Comb(Comb(Const("word_subword",_),_),_)->true|_->false in
     let subs = setify(find_terms is_sub w) in
     (EVERY (List.mapi (fun i t -> ABBREV_TAC(mk_eq(mk_var(Printf.sprintf "T_%d" i,type_of t),t))) subs)) (asl,w)) THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN
  BINOP_TAC THEN CONV_TAC(AC WORD_XOR_AC_THM);;

(* ---------------------------------------------------------------------------
   SEED_ABS + SWP_Q30_SEED_FINISH_TAC (the wired-in Q30 seed closer).
   machwj_abs/simple_abs/g2app_free are the abstract seed terms over 9 lanes
   vacc/vcb0..3/vh0..3; machwj_abs is assembled from its repeated lane subterms.
   SEED_ABS : machwj_abs = byteswap128(polyval_reduce_prop3 simple_abs)  -- axiom-free.
   --------------------------------------------------------------------------- *)
let machwj_abs =
  let lanes =
   [`t1:int64`, `(word_subword (vh3:int128) (0,64):int64)`;
    `t2:int64`, `(word_subword (vh2:int128) (0,64):int64)`;
    `t3:int64`, `(word_subword (vh1:int128) (0,64):int64)`;
    `t4:int64`, `(word_subword (vh0:int128) (0,64):int64)`;
    `t5:int64`, `(word_subword (vcb3:int128) (0,64):int64)`;
    `t6:int64`, `(word_subword (vcb2:int128) (0,64):int64)`;
    `t7:int64`, `(word_subword (vcb1:int128) (0,64):int64)`;
    `t8:int64`, `(word_subword (vcb0:int128) (0,64):int64)`;
    `t9:int64`, `(word_subword (vacc:int128) (0,64):int64)`;
    `t10:int128`, `(word_pmul (word_xor t9 (t8:int64)) (t1:int64):int128)`;
    `t11:int64`, `(word_subword (t10:int128) (0,64):int64)`;
    `t12:int64`, `(word_subword (word_pmul (t7:int64) (t2:int64):int128) (0,64):int64)`;
    `t13:int64`, `(word_subword (word_pmul (t6:int64) (t3:int64):int128) (0,64):int64)`;
    `t14:int64`, `(word_subword (word_pmul (t5:int64) (t4:int64):int128) (0,64):int64)`;
    `t15:int64`, `word_xor t12 (word_xor t13 (t14:int64))`;
    `t16:int64`, `(word_subword (vh3:int128) (64,64):int64)`;
    `t17:int64`, `(word_subword (vh2:int128) (64,64):int64)`;
    `t18:int64`, `(word_subword (vh1:int128) (64,64):int64)`;
    `t19:int64`, `(word_subword (vh0:int128) (64,64):int64)`;
    `t20:int64`, `(word_subword (vcb3:int128) (64,64):int64)`;
    `t21:int128`, `(word_pmul (word_xor t20 (t5:int64)) (karatsuba_mid vh0):int128)`;
    `t22:int64`, `(word_subword (t21:int128) (0,64):int64)`;
    `t23:int64`, `(word_subword (word_pmul (t20:int64) (t19:int64):int128) (0,64):int64)`;
    `t24:int64`, `(word_subword (vcb2:int128) (64,64):int64)`;
    `t25:int128`, `(word_pmul (word_xor t6 (t24:int64)) (karatsuba_mid vh1):int128)`;
    `t26:int64`, `(word_subword (t25:int128) (0,64):int64)`;
    `t27:int64`, `(word_subword (word_pmul (t24:int64) (t18:int64):int128) (0,64):int64)`;
    `t28:int64`, `(word_subword (vcb1:int128) (64,64):int64)`;
    `t29:int128`, `(word_pmul (word_xor t28 (t7:int64)) (karatsuba_mid vh2):int128)`;
    `t30:int64`, `(word_subword (t29:int128) (0,64):int64)`;
    `t31:int64`, `word_xor t30 (word_xor t26 (t22:int64))`;
    `t32:int64`, `(word_subword (word_pmul (t28:int64) (t17:int64):int128) (0,64):int64)`;
    `t33:int64`, `word_xor t32 (word_xor t27 (t23:int64))`;
    `t34:int64`, `(word_subword (vcb0:int128) (64,64):int64)`;
    `t35:int64`, `(word_subword (vacc:int128) (64,64):int64)`;
    `t36:int128`, `(word_pmul (word_xor t35 (t34:int64)) (t16:int64):int128)`;
    `t37:int64`, `word_xor (word_xor t9 t8) (word_xor t35 (t34:int64))`;
    `t38:int64`, `(word_subword (t36:int128) (0,64):int64)`;
    `t39:int64`, `word_xor (word_xor t11 t15) (word_xor t38 (t33:int64))`;
    `t40:int64`, `(word_subword (word_pmul (t37:int64) (karatsuba_mid vh3):int128) (0,64):int64)`;
    `t41:int64`, `word_xor t39 (word_xor t40 (t31:int64))`;
    `t42:int64`, `(word_subword (t36:int128) (64,64):int64)`;
    `t43:int64`, `(word_subword (t10:int128) (64,64):int64)`;
    `t44:int64`, `(word_subword (word_pmul (t7:int64) (t2:int64):int128) (64,64):int64)`;
    `t45:int64`, `(word_subword (word_pmul (t6:int64) (t3:int64):int128) (64,64):int64)`;
    `t46:int64`, `(word_subword (word_pmul (t5:int64) (t4:int64):int128) (64,64):int64)`;
    `t47:int64`, `word_xor t44 (word_xor t45 (t46:int64))`;
    `t48:int64`, `(word_subword (word_pmul (t28:int64) (t17:int64):int128) (64,64):int64)`;
    `t49:int64`, `(word_subword (word_pmul (t24:int64) (t18:int64):int128) (64,64):int64)`;
    `t50:int64`, `(word_subword (word_pmul (t20:int64) (t19:int64):int128) (64,64):int64)`;
    `t51:int64`, `word_xor t48 (word_xor t49 (t50:int64))`;
    `t52:int64`, `(word 13979173243358019584:int64)`;
    `t53:int128`, `(word_pmul (word_xor t11 (t15:int64)) (t52:int64):int128)`;
    `t54:int64`, `(word_subword (t53:int128) (0,64):int64)`;
    `t55:int64`, `word_xor t54 (word_xor t43 (t47:int64))`;
    `t56:int128`, `(word_pmul (word_xor t55 (t41:int64)) (t52:int64):int128)`] in
  itlist (fun (v,d) acc -> vsubst [d,v] acc) lanes
   `(word_join
 (word_xor
  (word_xor
   (word_xor (word_subword (t53:int128) (64,64)) (word_xor t11 t15))
  (word_xor (word_xor (word_xor t43 t47) (word_xor t42 t51))
  (word_xor
   (word_subword (word_pmul (t37:int64) (karatsuba_mid vh3):int128)
   (64,64))
  (word_xor (word_subword (t29:int128) (64,64))
  (word_xor (word_subword (t25:int128) (64,64))
  (word_subword (t21:int128) (64,64)))))))
 (word_xor (word_subword t56 (0,64)) (word_xor t38 t33)))
 (word_xor (word_xor t55 t41)
 (word_xor (word_subword (t56:int128) (64,64))
 (word_xor t42 (t51:int64)))):int128)`;;
let simple_abs =
  `word_xor (word_pmul (vcb3:int128) (vh0:int128))
(word_xor (word_pmul (vcb2:int128) (vh1:int128))
(word_xor (word_pmul (vcb1:int128) (vh2:int128))
(word_pmul (word_xor vacc (vcb0:int128)) (vh3:int128):int256)))`;;
let g2app_free =
  `polyval_reduce_g2
(word_xor
 (word_pmul (word_subword vcb3 (0,64):int64)
 (word_subword vh0 (0,64):int64))
(word_xor
 (word_pmul (word_subword vcb2 (0,64):int64)
 (word_subword vh1 (0,64):int64))
(word_xor
 (word_pmul (word_subword vcb1 (0,64):int64)
 (word_subword vh2 (0,64):int64))
(word_pmul (word_subword (word_xor vacc vcb0) (0,64):int64)
(word_subword vh3 (0,64):int64)))))
(word_xor
 (word_pmul (word_subword vcb3 (64,64):int64)
 (word_subword vh0 (64,64):int64))
(word_xor
 (word_pmul (word_subword vcb2 (64,64):int64)
 (word_subword vh1 (64,64):int64))
(word_xor
 (word_pmul (word_subword vcb1 (64,64):int64)
 (word_subword vh2 (64,64):int64))
(word_pmul (word_subword (word_xor vacc vcb0) (64,64):int64)
(word_subword vh3 (64,64):int64)))))
(word_xor (word_pmul (karatsuba_mid vcb3) (karatsuba_mid vh0))
(word_xor (word_pmul (karatsuba_mid vcb2) (karatsuba_mid vh1))
(word_xor (word_pmul (karatsuba_mid vcb1) (karatsuba_mid vh2))
(word_pmul (karatsuba_mid (word_xor vacc vcb0)) (karatsuba_mid vh3)))))`;;

(* (a) machwj_abs = byteswap128(polyval_reduce_g2 <towers>) -- SEED_AC_CLOSE_TAC, ~1.2s, no blasting. *)
let MACHWJ_IS_BSW_G2 = prove
 (mk_eq(machwj_abs, mk_comb(`byteswap128`, g2app_free)), SEED_AC_CLOSE_TAC);;
(* (b) polyval_reduce_g2 <towers> = polyval_reduce_prop3 simple_abs -- CORE_REDUCE branch1, ~14s. *)
let G2_IS_PROP3 = prove
 (mk_eq(g2app_free, mk_comb(`polyval_reduce_prop3`, simple_abs)),
  REWRITE_TAC[POLYVAL_REDUCE_G2] THEN
  GEN_REWRITE_TAC (RAND_CONV o TOP_DEPTH_CONV) [PMUL_KARATSUBA_JOIN_ALT] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[karatsuba_mid] THEN
  REWRITE_TAC[CMID_LOHI; CMID_HILO] THEN AP_TERM_TAC THEN
  REWRITE_TAC[JOIN_XOR_256; JOIN_XOR_128] THEN
  ABBREV_PMULS THEN POP_ASSUM_LIST(K ALL_TAC) THEN CONV_TAC BITBLAST_RULE);;
let SEED_ABS = TRANS MACHWJ_IS_BSW_G2 (AP_TERM `byteswap128` G2_IS_PROP3);;

(* SWP_Q30_SEED_FINISH_TAC: closes the body-end Q30 goal once it is in the form
     machwj[real lanes] = word_join (word_subword ACC (0,64)) (word_subword ACC (64,64))
   with ACC = nist_ghash..(4*(i+1)).  term_match recovers the 9 lane instantiations from the LHS,
   INST SEED_ABS -> machwj = byteswap128(prop3 simple[lanes]); BRANCH2 folds prop3 simple -> nist_ghash..4(i+1);
   byteswap128 def matches the RHS half-swap.  Instant (no blasting -- SEED_ABS did the work). *)
let SWP_Q30_SEED_FINISH_TAC : tactic = fun (asl,w) ->
  let (_,ilist,_) = term_match [] machwj_abs (lhs w) in
  let seed_i = INST ilist SEED_ABS in
  let br2 = REWRITE_RULE[ARITH_RULE `4*i+4 = 4*(i+1)`] SWP_GHASH_BRANCH2_256 in
  let seed_bsw = REWRITE_RULE[br2] seed_i in
  (ONCE_REWRITE_TAC[seed_bsw] THEN REWRITE_TAC[byteswap128]) (asl,w);;

(* X13 counter-lane closer: the running counter X13 = word_zx(word(4i+2)) advances by +4 each body
   (0x274 add w13,w13,#4), so the body-end goal is
     word_zx (word_add (word_zx (word_zx (word (4*i+2)))) (word 4)) = word_zx (word (4*(i+1)+2)).
   ZXRT32 folds the inner int32->int64->int32 round-trip, then AP_TERM + WORD_RULE on the +4 arith. *)
let ZXRT32 = WORD_BLAST `word_zx(word_zx (m:int32):int64):int32 = m`;;
let CTR_LANE_dec : tactic =
  REWRITE_TAC[ZXRT32] THEN TRY(AP_TERM_TAC THEN CONV_TAC WORD_RULE) THEN
  TRY(CONV_TAC WORD_RULE);;

(* Staged-block fact: rev8(ctr_block nonce a) and rev8(ctr_block nonce b) share the SAME low-96 bits
   (the nonce part); only the high-32 (+12 counter word) differs.  Validates the 3-way merge: the body's
   counter-word store to sp+OFF+12 changes only the +12 lane; the nonce lanes come unchanged from the s0
   baseline read(bytes128 sp+OFF)s0 = rev8(ctr_block 4i+M).  Building block for SP_SLOT_dec. *)

(* THE staged-slot 3-way-merge reassembly (the SP_SLOT algebraic core).  After rev8, the counter word lives in the
   TOP 32 bits [96,128); the low 96 bits are the (counter-independent) nonce.  When the body overwrites the
   +12 counter-word lane (bytes32 at sp+OFF+12) with the new counter word word_zx(word_bytereverse(word b)),
   the resulting block = word_join <that counter word> <baseline's low-96 nonce> = rev8(ctr_block nonce b).
   So the staged-block closer, after resolving read(bytes128 sp+OFF)s193 via read-over-write to
   (counter-word ++ baseline-low-96), folds to rev8(ctr_block b) by STAGED_REASSEMBLE (a = old block index in the
   surviving s0 baseline, b = new index).  Read-over-write recipe: split bytes128 -> bytes64 ->
   bytes32 (READ_MEMORY_BYTESIZED_SPLIT el 1 then el 2, NORMALIZE between) then ONCE_DEPTH COMPONENT_READ_OVER_WRITE_CONV
   resolves the +12 lane to the store value and the other lanes (disjoint) to the baseline reads. *)
let STAGED_REASSEMBLE = prove
 (`word_join (word_zx (word_bytereverse (word b:int32)):int32)
             (word_subword (word_reversefields 8 (ctr_block (nonce:(96)word) a):int128) (0,96):(96)word)
    :int128
   = word_reversefields 8 (ctr_block nonce b)`,
  REWRITE_TAC[ctr_block] THEN CONV_TAC WORD_BLAST);;

(* ============================================================================
   staged-block setup lemmas.  SLOT_LO/SLOT_MID rewrite the staged-slot nonce subwords (of the reversed ctr_block 2)
   back to the resident IV halves ivlo / subword ivhi, so ASM_REWRITE closes them against the split store facts.
   CTR_BLOCK_BUILD_INSERT_PLAIN folds the AES-embedded (plain) counter-slot form to rev8(ctr_block cval).
   Cipher-independent (pure ctr_block/counter algebra). *)
let SLOT_LO = prove
 (`word_join (ivhi:int64) (ivlo:int64):int128 = word_reversefields 8 (ctr_block nonce c)
   ==> word_subword (word_reversefields 8 (ctr_block nonce c):int128) (0,64):int64 = ivlo`,
  DISCH_THEN(SUBST1_TAC o SYM) THEN CONV_TAC WORD_BLAST);;
let SLOT_MID = prove
 (`word_join (ivhi:int64) (ivlo:int64):int128 = word_reversefields 8 (ctr_block nonce c)
   ==> word_subword (word_reversefields 8 (ctr_block nonce c):int128) (64,32):int32 =
       word_subword (ivhi:int64) (0,32):int32`,
  DISCH_THEN(SUBST1_TAC o SYM) THEN CONV_TAC WORD_BLAST);;

(* ============================================================================
   Staged-block closer -- reconstruct each staged counter block DURING STEPPING at its counter-store state,
   from nonce lanes primed at s0 (constant, counter-independent) + the body's +12 counter-word str.
   These four lemmas are cipher-independent (pure component/ctr_block algebra). ============================== *)

(* Lane-extraction: a bytes64/bytes32 read equals the corresponding subword of the enclosing bytes128 read.
   (Pure component algebra: the byte-sized split + WORD_BLAST on the word_join reassembly.) *)
let B64_OF_B128_LO = prove
 (`read (memory :> bytes64 x) s :int64 = word_subword (read (memory :> bytes128 x) s :int128) (0,64)`,
  REWRITE_TAC[el 1 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT)] THEN CONV_TAC WORD_BLAST);;
let B32_OF_B128_MID = prove
 (`read (memory :> bytes32 (word_add x (word 8))) s :int32 =
     word_subword (read (memory :> bytes128 x) s :int128) (64,32)`,
  REWRITE_TAC[el 1 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT);
              el 2 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT)] THEN
  CONV_TAC WORD_BLAST);;

(* Counter-independence of the nonce lanes: the low-64 and mid-32 subwords of rev8(ctr_block nonce c) do NOT
   depend on the counter c (only the top-32 counter lane does).  Lets us canonicalize any staged block's nonce
   lanes to the resident ctr_block-2 form (== the ivec) so they are CONSTANT across iterations. *)
let SUBW_LO_CI = prove
 (`word_subword (word_reversefields 8 (ctr_block nonce a):int128) (0,64):int64 =
   word_subword (word_reversefields 8 (ctr_block nonce b):int128) (0,64):int64`,
  REWRITE_TAC[ctr_block] THEN CONV_TAC WORD_BLAST);;
let SUBW_MID_CI = prove
 (`word_subword (word_reversefields 8 (ctr_block nonce a):int128) (64,32):int32 =
   word_subword (word_reversefields 8 (ctr_block nonce b):int128) (64,32):int32`,
  REWRITE_TAC[ctr_block] THEN CONV_TAC WORD_BLAST);;

(* THE dec-256 3-way-join reload fold.  DIFFERS from CTR_BLOCK_BUILD_INSERT_PLAIN by an EXTRA int64
   word_zx in the counter chain (dec-256's `str w` reversal is 64-bit-wide, so after CTR_ZX_NORM the counter
   cell is word_zx(word_zx(word_bytereverse(word_zx(word_zx(word cval:int32):int64):int64):int64):int32):int32),
   NOT the int32-bytereverse).  General in cval.  Proven by ctr_block + BITBLAST (~0.4s). *)

(* ============================================================================
   NATIVE-SAFE staged-block reconstruction (ivlo/ivhi VARIABLE lanes).
   The Design-A persistent lanes (RHS = word_subword(rev8(ctr_block 2))(..), a compound ctr_block memory read at
   an OLD state) crash native ARM_STEP_TAC (mk_comb).  We avoid this by ABBREVing the ivec halves as
   VARIABLES ivlo/ivhi and stating lanes as `= ivlo` / `= word_subword ivhi (0,32)` (variable RHS -> ARM_STEP-safe).
   CTR_BLOCK_BUILD_V_DEC: the ivlo/ivhi-variable 3-way-join fold (given the join relation).  Its counter-cell
   width profile (word_zx over int64 intermediates) is subtle and PRINTS identical to a wrong int32 form but
   term_match-FAILS -- so we rebuild it from a fully-typed .tm dump (dec256_ctr_v_dec.tm), NOT hand-typed. *)
let CTR_BLOCK_BUILD_V_DEC =
  let tm = parse_term ("(word_join:(64)word->(64)word->(128)word) (ivhi:(64)word) (ivlo:(64)word) =
(word_reversefields:num->(128)word->(128)word) 8
((ctr_block:(96)word->num->(128)word) (nonce:(96)word) (c:num))
==> (word_join:(64)word->(64)word->(128)word)
    ((word_join:(32)word->(32)word->(64)word)
     ((word_zx:(64)word->(32)word)
     ((word_zx:(32)word->(64)word)
     ((word_bytereverse:(32)word->(32)word)
     ((word_zx:(64)word->(32)word)
     ((word_zx:(32)word->(64)word) ((word:num->(32)word) (cval:num)))))))
    ((word_subword:(64)word->num#num->(32)word) (ivhi:(64)word) (0,32)))
    (ivlo:(64)word) =
    (word_reversefields:num->(128)word->(128)word) 8
    ((ctr_block:(96)word->num->(128)word) (nonce:(96)word) (cval:num))") in
  prove(tm,
    DISCH_THEN(fun th -> MP_TAC(MATCH_MP SCALAR_IV_SPLIT th)) THEN
    REWRITE_TAC[ctr_block] THEN DISCH_THEN(CONJUNCTS_THEN SUBST1_TAC) THEN
    CONV_TAC WORD_BLAST);;
(* ============================================================================
   dec-256 SWP body/fill SHARED closers, used by both the BODYLEG (symbolic i)
   and the FILL leg (i=0): rk15, INFOLD_dec, GHASH_PARTIAL_CLOSE_dec,
   SWP_Q30_SEED_TAC, OUT_BLOCK_CLOSE_dec, OUT_STORE_dec, SP_SLOT_dec,
   close_pc_cond, close_frame_dec, OUT_FRAME_dec, IVEC_RECOMB_dec, CTRREG_dec
   and the CLOSE_DEC dispatcher.
   ============================================================================ *)

(* in_p addr normalizations (64*(i+1)+K -> 16*(4*(i+1)+M)); (i+1) form. *)
let inp_addr_norms_dec =
  (* bare K=0 case: goal address is `word (64*(i+1))` with no `+0` *)
  (WORD_RULE `word_add (in_p:int64) (word (64*(i+1))):int64 = word_add in_p (word (16*(4*(i+1))))`) ::
  List.map (fun (kk,m) ->
    WORD_RULE (subst [mk_small_numeral kk, `K:num`; mk_small_numeral m, `M:num`]
                 `word_add (in_p:int64) (word (64*(i+1)+K)):int64 = word_add in_p (word (16*(4*(i+1)+M)))`))
  [(0,0);(16,1);(32,2);(48,3);(64,4);(80,5);(96,6);(112,7)];;

(* read(in_p+...)=inblock: normalize addr then in-forall. *)
let IN_READ_CLOSE_dec : tactic =
  REWRITE_TAC inp_addr_norms_dec THEN
  (fun (asl,w) ->
     FIRST_ASSUM(fun fa -> if (try is_forall(concl fa) && free_in `in_p:int64`(concl fa)
                                  && free_in (rand(lhs w)) (concl fa) with _->false)
                          then MATCH_MP_TAC fa else NO_TAC) (asl,w)) THEN
  (* block-index bound blk < nblocks: ASM_ARITH alone cannot cross nblocks DIV 4 = loop_count,
     so first establish 4i+7 < nblocks (covers all body-leg blocks) from the 3 root facts. *)
  (SUBGOAL_THEN `4*i+7 < nblocks` ASSUME_TAC THENL
    [UNDISCH_TAC `nblocks DIV 4 = loop_count` THEN UNDISCH_TAC `i < loop_count - 2` THEN
     UNDISCH_TAC `2 <= loop_count` THEN ARITH_TAC; ALL_TAC]
   ORELSE ALL_TAC) THEN
  ASM_ARITH_TAC;;

(* in-read folder that dewraps+normalizes inside a partial tower. *)
let is_inp_bytes128_read t =
  try let rd,st = dest_comb t in
      let rc,comp = dest_comb rd in
      fst(dest_const rc) = "read" && is_var st &&
      free_in `in_p:int64` comp &&
      can (find_term (fun u -> is_const u && fst(dest_const u) = "bytes128")) comp
  with _ -> false;;
let sixteen_blk rd =
  let mul16 = find_term (fun t ->
      try let op,args = strip_comb t in
          fst(dest_const op) = "*" && length args = 2 &&
          is_numeral (hd args) && dest_numeral (hd args) = num 16
      with _ -> false) rd in
  rand mul16;;
(* state of an in_p bytes128 read term (the s-var name), or "" *)
let inpread_state rd = try (match dest_comb rd with (_,Var(nm,_)) -> nm | _ -> "") with _ -> "";;
(* state that an input-frame forall's read is about (its bound-body read state var), or "" *)
let inpforall_state c = try
   (match snd(strip_forall c) with
    | Comb(Comb(Const("==>",_),_),bod) ->
       (match find_terms (fun t -> match t with
          Comb(Comb(Const("read",_),cmp),Var(nm,_)) when free_in `in_p:int64` cmp -> true | _ -> false) bod with
        | (Comb(Comb(_,_),Var(nm,_)))::_ -> nm | _ -> "")
    | _ -> "") with _ -> "";;
(* fold an in_p read to inblock, picking the input-frame forall AT THE READ'S OWN STATE (the out-store's embedded
   in_p read is at an OLD state sK; gkeepN keeps in_p foralls at all states, so the sK forall is present). *)
let INFOLD_dec : tactic =
  REWRITE_TAC inp_addr_norms_dec THEN
  (fun (asl,w) ->
    let inreads = setify(find_terms is_inp_bytes128_read w) in
    if inreads = [] then ALL_TAC (asl,w)
    else (EVERY (map (fun rd ->
       let blk = sixteen_blk rd in
       let st = inpread_state rd in
       (* TRY to fold rd -> inblock blk; NEVER throw (if no usable forall, leave rd unfolded so the caller can
          decide -- avoids regressing the whole closer to a raw-goal throw). *)
       TRY(SUBGOAL_THEN (mk_eq(rd, mk_comb(`inblock:num->int128`, blk))) ASSUME_TAC THENL
        [(* prefer the input-frame forall at the SAME state as the read; else any in_p forall *)
         (FIRST_ASSUM(fun fa -> if (try is_forall(concl fa) && free_in `in_p:int64`(concl fa)
                                       && inpforall_state (concl fa) = st with _->false)
                                  then MATCH_MP_TAC fa else NO_TAC)
          ORELSE FIRST_ASSUM(fun fa -> if (try is_forall(concl fa) && free_in `in_p:int64`(concl fa) with _->false)
                                         then MATCH_MP_TAC fa else NO_TAC))
         THEN
         (* the block-index bound (blk < nblocks): ASM_ARITH alone can't cross the nblocks DIV 4 = loop_count
            relation, so first establish 4*i+7 < nblocks (covers all body-leg blocks incl one-ahead 4(i+1)+2),
            from the 3 root invariant facts, then ASM_ARITH. *)
         (SUBGOAL_THEN `4*i+7 < nblocks` ASSUME_TAC THENL
           [UNDISCH_TAC `nblocks DIV 4 = loop_count` THEN UNDISCH_TAC `i < loop_count - 2` THEN
            UNDISCH_TAC `2 <= loop_count` THEN ARITH_TAC; ALL_TAC]
          ORELSE ALL_TAC) THEN
         ASM_ARITH_TAC; ALL_TAC]))
      inreads)) (asl,w));;

(* GHASH partial (pmul/xor over inblock x h-power lanes, RHS is my partial form, NO nist_ghash).
   With the Q10/Q11 invariant fix, all 5 partials (Q5/Q6/Q9/Q10/Q11) are TRUE.  Q5/Q9/Q10/Q11 close
   by REFL after the in-fold + reassemble.  Q6 (compound: karatsuba_mid mid-lane + block-2 word_subword(word_join
   ..)(64,128) structure) needs the extra SWP_SUBWORD_JOIN_MID + WORD_SIMPLE_SUBWORD + WORD_BLAST tail to fold the
   word_subword(word_join(km h1)(km h0))(k,64) -> km h_ and close the word_xor congruence. *)
let GHASH_PARTIAL_CLOSE_dec : tactic =
  INFOLD_dec THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[INBLOCK_REASSEMBLE; GSYM nist_input_block] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[nist_input_block] THEN ASM_REWRITE_TAC[] THEN
  (TRY REFL_TAC THEN
   TRY (REWRITE_TAC[SWP_SUBWORD_JOIN_MID] THEN CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
        TRY(CONV_TAC WORD_BLAST)));;

(* GHASH seed-core (Q30 half-swap accumulator = half-swap(nist_ghash..4(i+1))). aes256. *)

(* Q30 seed conjunct.  With the Q10/Q11 invariant fix, the Q30 goal is TRUE (machine reduce =
   half-swap of nist_ghash..(4(i+1))).  DISASM: Q30 = ext(v5,#8) = half-swap of the settled reduce v5.  After
   SWP_JOIN_IS_BSW/xor_rcancel/byteswap128/SWP_SUBWORD_JOIN_MID the goal is
     word_join (word_subword MACHINE_lo (0,64)) (word_subword MACHINE_hi (64,64))
       = word_join (word_subword ACC (0,64)) (word_subword ACC (64,64))     [ACC = nist_ghash..(4(i+1))]
   where MACHINE_lo != MACHINE_hi (the two 64-bit lanes come from DIFFERENT machine reduce sub-trees) -- so the
   dec-128 single-x `MATCH_MP_TAC(BITBLAST_RULE join(sub x)(sub x)=join(sub y)(sub y))` is UNSOUND here.  Use
   BINOP_TAC to split into the two ALIGNED per-half identities (sub MACHINE_lo 0 = sub ACC 0) & (sub MACHINE_hi 64
   = sub ACC 64); each is a bounded GHASH-reduce word-identity closed by the recon (fold ACC via
   GSYM SWP_GHASH_BRANCH2_256 -> prop3 packing, RECONSTRUCT, then a native BITBLAST ~117s -- native-only).  branch2 (packing=nist_ghash) is subsumed by the GSYM-BRANCH2 fold. *)
(* The seed closer (algebraic route, no poly-const blast).  The seed goal after the prefix is
     machwj[real lanes] = word_join (word_subword ACC (0,64)) (word_subword ACC (64,64))   [ACC=nist_ghash..4(i+1)]
   PREFIX: SWP_SUBWORD_JOIN_MID collapses LHS word_subword(word_join BIG)(64,128) -> word_join(sw.. 0)(sw.. 64)
     = machwj; DEC_GHASH_NORM_TAC folds the inblock byte-lanes -> nist_input_block; ASM_REWRITE folds the block-0
     Q14 read (read Q14 sK = inblock(4i), in asl) then GSYM nist_input_block makes it nist_input_block(4i); now
     LHS is exactly machwj over the real lanes.  FINISH: SWP_Q30_SEED_FINISH_TAC term_matches
     machwj_abs -> the 9 lane insts, INSTs the proven SEED_ABS (= byteswap128(prop3 simple), axiom-free, NO
     poly-const blast), folds prop3 simple -> nist_ghash..4(i+1) via SWP_GHASH_BRANCH2_256, byteswap128 def closes.
   The whole seed is now ~instant (SEED_ABS built once at load; ~1.5s+14s).  Invariant Q30 unchanged (confirmed
   correct: half-swap of nist_ghash..4i). *)
let SWP_Q30_SEED_TAC : tactic =
  REWRITE_TAC[SWP_SUBWORD_JOIN_MID] THEN DEC_GHASH_NORM_TAC THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM nist_input_block] THEN ASM_REWRITE_TAC[] THEN
  SWP_Q30_SEED_FINISH_TAC;;

(* AES14P_VIA_* bridges: fold a carried AES partial (aesNc) + remaining rounds -> aes14p. *)
let out_via_lemmas =
  [AES14P_VIA_AES5C; AES14P_VIA_AES12C; AES14P_VIA_AES1C; AES14P_VIA_AES6C; AES14P_VIA_AES7C; AES14P_VIA_AES11C];;
(* per-block out-store keystream fold.  After the read resolves to the machine value
     word_xor inblock_j (word_xor rk14 <tower>) = word_xor (aes256_ctr_block j) inblock_j
   <tower> is either a FULL 14-round tower on a resolved rev8(ctr_block(j+2)) [block whose counter block is
   resident] OR built on a carried AES partial aesNc(j+2) [pipelined blocks].  Try both. *)
(* aes256_ctr_block j unfolds to rev8(aes256_cipher(ctr_block(j+2))); normalize the ctr index j+2.
   Cover BOTH the out-frame form (j = 4i+M) AND the one-ahead form (j = 4(i+1)+M). *)
let ctr_idx_norms = [ARITH_RULE `(4*i)+c = 4*i+c`; ARITH_RULE `(4*i+1)+c = 4*i+c+1`;
                     ARITH_RULE `(4*i+2)+c = 4*i+c+2`; ARITH_RULE `(4*i+3)+c = 4*i+c+3`;
                     ARITH_RULE `(4*(i+1)+0)+c = 4*(i+1)+c`; ARITH_RULE `(4*(i+1)+1)+c = 4*(i+1)+c+1`;
                     ARITH_RULE `(4*(i+1)+2)+c = 4*(i+1)+c+2`; ARITH_RULE `(4*(i+1)+3)+c = 4*(i+1)+c+3`];;
(* resident-block ctr index bridges: the FULL-tower one-ahead keystream runs on a RESIDENT rev8(ctr_block(4i+K))
   (K=6,7,8,9), while after aes256_ctr_block unfold the target ctr index is 4(i+1)+M+2.  Bridge 4i+K = 4(i+1)+M'. *)
let resident_ctr_norms = [ARITH_RULE `4*i+c+4 = 4*(i+1)+c`; ARITH_RULE `4*i+c+5 = 4*(i+1)+c+1`;
                          ARITH_RULE `4*i+c+6 = 4*(i+1)+c+2`; ARITH_RULE `4*i+c+7 = 4*(i+1)+c+3`];;
(* symbolic-c output-block closer: fold the keystream forward by KEYSTREAM_FOLD256_DEC (pure rewriting,
   no use-time CONV_TAC WORD_BITWISE_RULE, which would bit-blast the symbolic counter word c).  Try the
   aligned form (4i+c+M) first, then the (4i+M)+c / (4(i+1)+M)+c re-associations as fallbacks. *)
let KS_FIX_dec : tactic =
  fun (asl,w) ->
    let rkth = try snd(find (fun (_,th) -> concl th = rk15) asl) with _ -> ASSUME rk15 in
    (FIRST
      [ (REWRITE_TAC[MATCH_MP KEYSTREAM_FOLD256_DEC rkth] THEN ASM_REWRITE_TAC[] THEN REFL_TAC);
        (REWRITE_TAC[ARITH_RULE `4 * i + c + 3 = (4 * i + 3) + c`;
                     ARITH_RULE `4 * i + c + 2 = (4 * i + 2) + c`;
                     ARITH_RULE `4 * i + c + 1 = (4 * i + 1) + c`;
                     ARITH_RULE `4 * i + 0 = 4 * i`] THEN
         REWRITE_TAC[MATCH_MP KEYSTREAM_FOLD256_DEC rkth] THEN ASM_REWRITE_TAC[] THEN REFL_TAC);
        (REWRITE_TAC[ARITH_RULE `4 * (i+1) + c + 3 = (4 * (i+1) + 3) + c`;
                     ARITH_RULE `4 * (i+1) + c + 2 = (4 * (i+1) + 2) + c`;
                     ARITH_RULE `4 * (i+1) + c + 1 = (4 * (i+1) + 1) + c`] THEN
         REWRITE_TAC[MATCH_MP KEYSTREAM_FOLD256_DEC rkth] THEN ASM_REWRITE_TAC[] THEN REFL_TAC) ]) (asl,w);;

let OUT_BLOCK_CLOSE_dec : tactic =
  (* ADD_CLAUSES normalizes 4*i+0 -> 4*i (block-0's target has an explicit +0 that the INFOLD-folded operand lacks). *)
  REWRITE_TAC[ADD_CLAUSES] THEN
  ((REWRITE_TAC[XOR_AES256_CIPHER_RECONSTRUCT_DEC] THEN
   REWRITE_TAC[WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
   REWRITE_TAC[MAP; WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
   ASM_REWRITE_TAC[] THEN
   REWRITE_TAC[aes256_ctr_block] THEN REWRITE_TAC ctr_idx_norms THEN
   REWRITE_TAC resident_ctr_norms THEN REFL_TAC)
  ORELSE
  (REWRITE_TAC(map GSYM out_via_lemmas) THEN
   REWRITE_TAC[aes256_ctr_block] THEN REWRITE_TAC ctr_idx_norms THEN
   REWRITE_TAC resident_ctr_norms THEN
   KS_FIX_dec));;

(* out-store address normalization: the goal's one-ahead address out_p+word(64*(i+1)+32) must match the store
   fact's out_p+word((64*i+64)+32) form (the body's x2 post-increment produced 64*i+64, not 64*(i+1)). *)
let out_addr_norms = [
  WORD_RULE `word_add (out_p:int64) (word (64*(i+1)+32)) = word_add out_p (word ((64*i+64)+32))`];;
(* out-store readback (one-ahead q12 store of block 4(i+1)+2 = 4i+6 at out_p+(64*i+64)+32).
   Normalize the address so ASM resolves the read to the machine value, then the unified per-block keystream fold. *)
let OUT_STORE_dec : tactic =
  REWRITE_TAC out_addr_norms THEN
  (* FIRST resolve the out_p read to the machine value (which embeds an old-state in_p read); ONLY THEN can
     INFOLD see + fold that embedded in_p read.  (Running INFOLD before ASM_REWRITE was the bug: the in_p read
     is invisible until the out read resolves.) *)
  ASM_REWRITE_TAC[] THEN
  INFOLD_dec THEN ASM_REWRITE_TAC[] THEN
  OUT_BLOCK_CLOSE_dec;;

(* staged counter block: goal is either
     word_join (read sp+X+8 sK) (read sp+X sK) = rev8(ctr_block(4(i+1)+M))   [split-form], or
     read (bytes128 sp+X) sK = rev8(ctr_block(4(i+1)+M))                     [whole-form].
   Resolve the sp reads (their values are in asl from stepping), collapse the counter-word tower to
   word_shl(word_zx(word_bytereverse(word cval)))32, then CTR_BLOCK_BUILD_INSERT + mk_cbv folds to
   rev8(ctr_block). ASM_REWRITE brings in the read facts; the ZX/CTR lemmas normalize; mk_cbv-style
   const bridges close. Robustly try REFL/WORD_BLAST after each normalization. *)
(* dec-256 RHS index norms: rev8(ctr_block (4(i+1)+M)) -> rev8(ctr_block (4i+(4+M))) so the counter-word
   base 4i+4 folds cleanly against the stored add-value; the staged blocks are +2..+6. *)
let SP_RHS_NORMS_dec = [
  ARITH_RULE `4*(i+1)+c = 4*i+c+4`; ARITH_RULE `4*(i+1)+c+1 = 4*i+c+5`;
  ARITH_RULE `4*(i+1)+c+2 = 4*i+c+6`; ARITH_RULE `4*(i+1)+c+3 = 4*i+c+7`;
  ARITH_RULE `4*(i+1)+c+4 = 4*i+c+8`];;
(* counter-word add folds (int32): the body computes add w,w13,#N with w13=word(4i+6) at store time. *)
let SP_LANE_FOLDS_dec = [
  WORD_RULE `word_add (word (4*i+c+4):int32) (word 1) = word(4*i+c+5)`;
  WORD_RULE `word_add (word (4*i+c+4):int32) (word 2) = word(4*i+c+6)`;
  WORD_RULE `word_add (word (4*i+c+4):int32) (word 3) = word(4*i+c+7)`;
  WORD_RULE `word_add (word (4*i+c+4):int32) (word 4) = word(4*i+c+8)`];;
(* staged counter block closer.  Two goal shapes:
     split: word_join(read sp+X+8 sK)(read sp+X sK) = rev8(ctr_block(4(i+1)+M))
     whole: read(bytes128 sp+X) sK          = rev8(ctr_block(4(i+1)+M))
   For the split form, MERGE_CTR128_TAC folds the two bytes64 reads back to a bytes128 read (matching the
   stepping's stored value); then ASM_REWRITE brings the stored insert-form in, CTR_ZX_NORM/lane-folds
   normalize the counter word, CTR_BLOCK_BUILD_INSERT folds to rev8(ctr_block).  We try MERGE at each staged
   offset (only the matching one fires; the rest ASM_REWRITE to no-ops).  Robust closers after. *)
(* SP_SLOT_dec (read-over-write split resolution + STAGED_REASSEMBLE).
   goal (split-form): word_join(read b64 sp+OFF+8 s193)(read b64 sp+OFF s193) = rev8(ctr_block(4(i+1)+M))
   or (whole-form): read(bytes128 sp+OFF)sK = rev8(ctr_block(4(i+1)+M)).
   Recipe: (1) if split-form, GSYM-fold to read(bytes128 sp+OFF)s193 (via READ_MEMORY_BYTESIZED_SPLIT el 1);
   (2) fully split bytes128->4 bytes32 (el 1 then el 2) + resolve the +12 lane to the counter-word store and the
   other 3 lanes to the surviving baseline, via ONCE_DEPTH COMPONENT_READ_OVER_WRITE_CONV (repeated to chain
   through the state write-tower); (3) ASM_REWRITE brings the resolved counter-word + baseline lanes; normalize
   the counter word (CTR_ZX_NORM/lane-folds) and fold via CTR_BLOCK_BUILD_INSERT/STAGED_REASSEMBLE to rev8(ctr_block).
   Robust fallbacks after each step. *)
(* Fast path: with MERGE_CTR128_FOLD wired into the stepper, each staged block is already resident at
   body-end as read(bytes128 sp+off)s193 = rev8(ctr_block (4(i+1)+M)) (the fold produced 4i+M' = 4(i+1)+M and
   read-over-write auto-advanced it to s193).  So the whole-form goal closes by ASM_REWRITE after bridging the
   index arithmetic 4(i+1)+M = 4i+M'.  Try this first; fall back to the old read-over-write recipe otherwise. *)
let SP_SLOT_dec_fast : tactic =
  REWRITE_TAC[ARITH_RULE `4*(i+1)+c = 4*i+c+4`; ARITH_RULE `4*(i+1)+c+1 = 4*i+c+5`;
              ARITH_RULE `4*(i+1)+c+2 = 4*i+c+6`; ARITH_RULE `4*(i+1)+c+3 = 4*i+c+7`] THEN
  ASM_REWRITE_TAC[];;
let SP_SLOT_dec : tactic = fun (asl,w) ->
  let splitL = el 1 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT)
  and splitL2 = el 2 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT) in
  (* if the goal LHS is word_join(read b64)(read b64), fold it back to read(bytes128 X) *)
  (TRY(fun (a,g) ->
     (match lhs g with
      | Comb(Comb(Const("word_join",_),
          Comb(Comb(Const("read",_),_),st)),_) ->
          let base = (match find_terms (fun t->match t with
             Comb(Comb(Const("word_add",_),v),_)->(try fst(dest_var v)="stackpointer" with _->false)|_->false)
             (rand(rator(lhs g))) with
             | (Comb(Comb(_,_),Comb(_,n)))::_ -> (try dest_small_numeral n with _->160) | _ -> 160) in
          let inst = CONV_RULE(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)
            (ISPECL [`memory`; mk_comb(mk_comb(`word_add:int64->int64->int64`,`stackpointer:int64`),
                     mk_comb(`word:num->int64`,mk_small_numeral base)); st] splitL) in
          GEN_REWRITE_TAC LAND_CONV [GSYM inst] (a,g)
      | _ -> ALL_TAC (a,g))) THEN
   (* resolve the bytes128 read through the write chain: split ONCE to 4 bytes32 lanes, then a BOUNDED number
      of read-over-write passes (each peels one write; the chain is deep but the +12 lane resolves to the last
      relevant store and the nonce lanes are disjoint from all body stores -> ASM_REWRITE finishes).
      NB the TOP_DEPTH split is applied ONCE (not in the REPEAT loop) to avoid re-splitting the whole goal. *)
   GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [splitL; splitL2] THEN
   CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
   CONV_TAC(ONCE_DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV) THEN
   ASM_REWRITE_TAC[] THEN
   REWRITE_TAC[ZX_COUNTER_UD; ZX_COUNTER_INC; CTR_ZX_NORM] THEN
   CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
   REWRITE_TAC SP_LANE_FOLDS_dec THEN REWRITE_TAC SP_RHS_NORMS_dec THEN
   ASM_REWRITE_TAC[] THEN
   REWRITE_TAC[STAGED_REASSEMBLE; CTR_BLOCK_BUILD_INSERT] THEN
   REWRITE_TAC[WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
   TRY(CONV_TAC WORD_RULE) THEN TRY REFL_TAC THEN TRY(CONV_TAC WORD_BLAST) THEN
   TRY(REWRITE_TAC[ctr_block] THEN CONV_TAC WORD_BLAST)) (asl,w);;

(* counter scalar-lane folds (word_zx/word_add towers).  The X13 running-counter lane
   (word_zx(word_add(word_zx(word_zx(word(4i+2))))(word 4)) = word_zx(word(4(i+1)+2))) closes via
   CTR_LANE_dec (ZXRT32 round-trip + AP_TERM + WORD_RULE); other lanes via the ZX/CTR normal forms. *)
let CTRREG_dec : tactic =
  CTR_LANE_dec ORELSE
  (REWRITE_TAC[ZX_COUNTER_UD; ZX_COUNTER_INC; CTR_ZX_NORM] THEN
   CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
   TRY REFL_TAC THEN TRY(CONV_TAC WORD_RULE) THEN TRY(AP_TERM_TAC THEN ARITH_TAC));;

(* pointers. *)
let close_ptr_dec : tactic =
  REWRITE_TAC[ARITH_RULE `64*((i+1)+1)=64*(i+1)+64`; ARITH_RULE `64*(i+1) = 64*i+64`; LEFT_ADD_DISTRIB] THEN
  CONV_TAC WORD_RULE;;

(* X1 decrement. *)
let close_x1_dec : tactic =
  ASM_SIMP_TAC[SWP_SUB_LEMMA_DEC];;

(* back-edge PC COND: the cbnz test resolves nonzero for i+1 < loop_count (steady). *)
let close_pc_cond : tactic =
  COND_CASES_TAC THENL [REFL_TAC; ALL_TAC] THEN
  (* the else-branch is contradictory: val(word_sub..)=0 impossible for i+1<loop_count-1... but at
     i=loop_count-2 boundary this is the LAST steady iter. The WHILE composition handles the boundary;
     here (i<loop_count-2) so word_sub(loop_count-(i+1))(1) != 0. *)
  POP_ASSUM MP_TAC THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(val (word_sub (word (loop_count-(i+1))) (word 1):int64) = 0)` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_SIMP_TAC[SWP_SUB_LEMMA_DEC] THEN REWRITE_TAC[VAL_EQ_0] THEN
    MATCH_MP_TAC(MESON[] `~(x = word 0) ==> ~(x = word 0)`) THEN
    REWRITE_TAC[WORD_EQ_0] THEN MAP_EVERY UNDISCH_TAC [`i < loop_count - 2`; `2 <= loop_count`] THEN ARITH_TAC;
    REFL_TAC];;

(* MAYCHANGE frame. *)
let pth_frame_dec = prove(`R s s' ==> R subsumed R' ==> R' s s'`, REWRITE_TAC[subsumed] THEN MESON_TAC[]);;
let close_frame_dec : tactic =
  fun (asl,w) ->
    let frame_th = try snd(List.find (fun (_,th) -> let c=concl th in
        (try not(is_eq c) && can(find_term(fun x->match x with Const("MAYCHANGE",_)->true|_->false)) c
            && (match c with Comb(Comb(_,a),b) -> is_var a && is_var b | _->false) with _->false)) asl)
      with _ -> failwith "close_frame_dec: no frame asm" in
    (MATCH_MP_TAC(MATCH_MP pth_frame_dec frame_th) THEN
     REWRITE_TAC[ETA_AX; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN SUBSUMED_MAYCHANGE_TAC) (asl,w);;

(* out-frame forall (j<4(i+1)): orthogonality preservation. Ported from dec-128 OUT0_TAC. *)
let OUT_FRAME_dec : tactic =
  REWRITE_TAC[ARITH_RULE `j < 4 * (i+1) <=>
                          j < 4 * i \/ j = 4*i+0 \/ j = 4*i+1 \/ j = 4*i+2 \/ j = 4*i+3`] THEN
  ASM_REWRITE_TAC[TAUT `p \/ q ==> r <=> (p ==> r) /\ (q ==> r)`] THEN
  REWRITE_TAC[FORALL_AND_THM; FORALL_UNWIND_THM2] THEN
  REWRITE_TAC[ARITH_RULE `16 * (4*i+0) = 64*i`; ARITH_RULE `16 * (4*i+1) = 64*i+16`;
     ARITH_RULE `16 * (4*i+2) = 64*i+32`; ARITH_RULE `16 * (4*i+3) = 64*i+48`] THEN
  ASM_REWRITE_TAC[] THEN
  (* split into: forall j<4i (incoming out-frame invariant, ASM) + 4 blocks j=4i+{0,1,2,3}.
     block 4i+2 = frame-carry (incoming one-ahead, ASM); blocks 4i+{0,1,3} = fresh stores (INFOLD-resolve the
     in_p read + the resident counter, then the unified per-block keystream fold).  Each branch: try ASM
     (closes the forall + carry), else the block fold. *)
  REPEAT CONJ_TAC THEN
  (* forall j<4i goal: accept the incoming out-frame invariant forall (ASM_REWRITE can't instantiate a forall).
     concrete-block goals: ASM (frame-carry blk 4i+2) else INFOLD+fold (fresh blks).  ORDER (per OUT_STORE fix):
     ASM_REWRITE to resolve the out read FIRST, THEN INFOLD the now-visible embedded in_p read, THEN OUT_BLOCK. *)
  TRY (FIRST_X_ASSUM (fun th -> if (try is_forall(concl th) && free_in `out_p:int64` (concl th) with _->false)
                                then MATCH_ACCEPT_TAC th else NO_TAC)) THEN
  TRY (ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  ASM_REWRITE_TAC[] THEN INFOLD_dec THEN ASM_REWRITE_TAC[] THEN
  OUT_BLOCK_CLOSE_dec;;

(* ivec recombine: after IVEC_SPLIT the ivec baseline is in ivlo/ivhi halves; the body never writes ivec_p, so
   read(bytes128 ivec_p)s193 recombines to word_join ivhi ivlo = rev8(ctr_block 2). *)
let IVEC_RECOMB_dec : tactic =
  GEN_REWRITE_TAC LAND_CONV [el 1 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT)] THEN
  ASM_REWRITE_TAC[];;

(* master dispatcher (shape+content routed). *)
let CLOSE_DEC : tactic =
  fun (asl,w) ->
    let has c t = can (find_term (fun u -> try fst(dest_const(fst(strip_comb u)))=c with _->false)) t in
    let has_mc t = try can(find_term(fun x->match x with Const("MAYCHANGE",_)->true|_->false)) t with _->false in
    let hd t = try fst(dest_const(fst(strip_comb t))) with _->"" in
    let deep_ghash = try has "nist_ghash" w with _ -> false in
    if has_mc w then close_frame_dec (asl,w)
    else if has "aligned_bytes_loaded" w then ASM_REWRITE_TAC[] (asl,w)
    else if is_forall w then OUT_FRAME_dec (asl,w)
    else if not(is_eq w) then (ASM_REWRITE_TAC[] THEN TRY close_pc_cond) (asl,w)
    else if hd w = "COND" || (has "pc" w && has "COND" w) then close_pc_cond (asl,w)
    else if hd (lhs w) = "word_sub" then close_x1_dec (asl,w)
    else if hd (lhs w) = "word_add" then close_ptr_dec (asl,w)
    else if hd (lhs w) = "read" && has "aes256_ctr_block" (rhs w) then OUT_STORE_dec (asl,w)
    else if hd (lhs w) = "read" && has "inblock" (rhs w) then IN_READ_CLOSE_dec (asl,w)
    else if hd (lhs w) = "read" && free_in `ivec_p:int64` (lhs w) then IVEC_RECOMB_dec (asl,w)
    else if hd (lhs w) = "read" && has "ctr_block" (rhs w) then (SP_SLOT_dec_fast ORELSE SP_SLOT_dec) (asl,w)
    else if hd (lhs w) = "word_reversefields" && has "ctr_block" (lhs w) && has "ctr_block" (rhs w) then
      (* staged slot / Q31 body-end: rev8(ctr_block(4i+M')) = rev8(ctr_block(4(i+1)+M)) with 4i+M' = 4(i+1)+M.
         The E-merge/ASM already rewrote the read to the resident block; only the index arithmetic remains. *)
      (AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC) (asl,w)
    else if deep_ghash then SWP_Q30_SEED_TAC (asl,w)
    else if hd (lhs w) = "aesmc" then
      (* Q3=aes12c(4(i+1)+3), Q8=aes5c(4(i+1)+5): unfold def, counter fold *)
      ((REWRITE_TAC[aes12c;aes5c] THEN REPEAT(AP_TERM_TAC ORELSE AP_THM_TAC) THEN
        REWRITE_TAC[ZX_COUNTER_UD;ZX_COUNTER_INC;CTR_ZX_NORM] THEN
        CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
        REWRITE_TAC[CTR_BLOCK_BUILD_INSERT; WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
        TRY(CONV_TAC WORD_RULE) THEN TRY REFL_TAC) ORELSE CTRREG_dec) (asl,w)
    else if hd (lhs w) = "word_join" && has "ctr_block" (rhs w) then (SP_SLOT_dec_fast ORELSE SP_SLOT_dec) (asl,w)
    else if free_in `in_p:int64` w then
      (* any lane embedding an in_p read = a GHASH partial (Q4/5/6/9/10/11 or word_zx Karatsuba-mid) *)
      (GHASH_PARTIAL_CLOSE_dec ORELSE SWP_Q30_SEED_TAC ORELSE CTRREG_dec) (asl,w)
    else if hd (lhs w) = "word_zx" || hd (lhs w) = "word_subword" then CTRREG_dec (asl,w)
    else (* word_xor / word_pmul GHASH partials *)
      (GHASH_PARTIAL_CLOSE_dec ORELSE SWP_Q30_SEED_TAC) (asl,w);;

(* ===== leg proofs (FILL/BODY/DRAIN/TAIL) ===== *)

(* ==================== LEG: BODY ==================== *)
(* ============================================================================
   dec-256 SWP BODYLEG (real): swp_inv i @0x26c -> inv(i+1) @0x570.
   Steps the body 1..193 (0x26c..0x56c; 0x570 cbnz is the back-edge, handled by
   the WHILE composition -- do NOT step it here), ENSURES_FINAL_STATE, then the
   CLOSE_DEC dispatcher (transplant of dec-128 CLOSE_V8, adapted to aes256 +
   aes5c/aes12c + the dec-256 conjunct order/counter offsets).
   ============================================================================ *)

(* ---- keep-sets, goal, stepper ---- *)
(* X11/X12 are not invariant lanes (DISASM 0x288 add w12,w13,#2; 0x29c rev w11,w12 -- the body
   CLOBBERS them as counter-scratch and never restores them; they are NOT resident nonce lanes).  The
   staged counter blocks live in MEMORY (bytes128 sp+OFF conjuncts, reconstructed from X13), so the X11/X12
   REGISTER values are dead at the loop head and appear neither in the invariant nor here.  (X11 stays in
   REDSETX so the stepper still tracks it harmlessly, but it is not a ghost input.) *)
let REDSETX_DEC = ["Q0";"Q1";"Q2";"Q3";"Q4";"Q5";"Q6";"Q7";"Q8";"Q9";"Q10";"Q11";"Q12";"Q13";"Q14";
                   "Q29";"Q30";"Q31"; "X7";"X8";"X13";"X17";"X25";"X27";"X30"];;
let ghost_lanes_dec = ["X7";"X8";"X17";"X25";"X27";"X30";"X13"];;
(* Merge RIGHT AFTER each counter-word store (before the ldr q), per dec-128's timing.
   Counter-word +12 stores: sp+204@step15 (block sp+192), sp+188@19 (block sp+176), sp+220@31 (block sp+208),
   sp+172@34 (block sp+160).  So merge at store+1 = (16,192),(20,176),(32,208),(35,160) -- NOT the load steps. *)

let leg_state_dec inv off idx =
  let body = rhs(concl((TOP_DEPTH_CONV BETA_CONV THENC REWRITE_CONV[ADD_CLAUSES])
                        (list_mk_comb(inv,[idx;`s:armstate`])))) in
  mk_abs(`s:armstate`,
    list_mk_conj(`aligned_bytes_loaded s (word pc) aes256_gcm_dec_mc` ::
                 mk_eq(`read PC s`,mk_comb(`word:num->int64`,mk_binop `+` `pc:num` off)) ::
                 conjuncts body));;

(* Leg hypotheses shared by the four legs: the argument facts and the nonoverlapping assumptions
   of the whole-function precondition (the leg-specific loop_count and len_bits facts are inserted
   at their customary positions by mk_leg_hyps). *)
let leg_hyps_common = `([EL 0 rk; EL 1 rk; EL 2 rk; EL 3 rk; EL 4 rk; EL 5 rk; EL 6 rk; EL 7 rk;
      EL 8 rk; EL 9 rk; EL 10 rk; EL 11 rk; EL 12 rk; EL 13 rk; EL 14 rk]:(int128)list = rk) /\
     len_bits DIV 128 = nblocks /\ nblocks DIV 4 = loop_count /\ nblocks MOD 4 = loop_remain /\
     16 * nblocks < 2 EXP 64 /\ aligned 16 (stackpointer:int64) /\
     nonoverlapping (out_p:int64,16 * nblocks) (word pc:int64,2036) /\
     nonoverlapping (out_p:int64,16 * nblocks) (in_p:int64,16 * nblocks) /\
     nonoverlapping (out_p:int64,16 * nblocks) (htable_p:int64,96) /\
     nonoverlapping (out_p:int64,16 * nblocks) (tag_p:int64,16) /\
     nonoverlapping (out_p:int64,16 * nblocks) (ivec_p:int64,16) /\
     nonoverlapping (out_p:int64,16*nblocks) (word_add stackpointer (word 160):int64,64) /\
     nonoverlapping (tag_p:int64,16) (word pc:int64,2036) /\
     nonoverlapping (tag_p:int64,16) (in_p:int64,16*nblocks) /\
     nonoverlapping (tag_p:int64,16) (htable_p:int64,96) /\
     nonoverlapping (tag_p:int64,16) (word_add stackpointer (word 160):int64,64) /\
     nonoverlapping (ivec_p:int64,16) (word pc:int64,2036) /\
     nonoverlapping (ivec_p:int64,16) (in_p:int64,16*nblocks) /\
     nonoverlapping (ivec_p:int64,16) (htable_p:int64,96) /\
     nonoverlapping (ivec_p:int64,16) (word_add stackpointer (word 160):int64,64) /\
     nonoverlapping (tag_p:int64,16) (ivec_p:int64,16) /\
     nonoverlapping (word_add stackpointer (word 160):int64,64) (word pc:int64,2036) /\
     nonoverlapping (word_add stackpointer (word 160):int64,64) (in_p:int64,16*nblocks) /\
     nonoverlapping (word_add stackpointer (word 160):int64,64) (htable_p:int64,96)`;;
let mk_leg_hyps lc_facts len_facts extra =
  let pre,rest = chop_list 4 (conjuncts leg_hyps_common) in
  list_mk_conj (pre @ lc_facts @ [hd rest] @ len_facts @ tl rest @ extra);;
let mk_leg_goal hyps pre post frame = mk_imp(hyps, list_mk_icomb "ensures" [`arm`; pre; post; frame]);;

let body_frame = `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
      MAYCHANGE [X19; X20; X21; X22; X23; X24; X25; X26; X27; X28; X29; X30] ,,
      MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
      MAYCHANGE [memory :> bytes(out_p:int64, 16 * nblocks)] ,,
      MAYCHANGE [memory :> bytes(word_add stackpointer (word 160):int64, 64)] ,, MAYCHANGE [events]`;;
let mk_body_goal_dec inv =
  mk_leg_goal (mk_leg_hyps [`2 <= loop_count`; `i < loop_count - 1`] [] [])
    (leg_state_dec inv `0x26c` `i:num`) (leg_state_dec inv `0x570` `i+1`) body_frame;;

let body_goal_dec = mk_body_goal_dec swp_inv;;

(* The in_p frame forall gives the n input blocks a leg reads as facts at s0 (block index idx k for
   k = 0..n-1); the bound idx (n-1) < nblocks is discharged from the given root facts. *)
let INPUT_SPLIT_DEC (idx:int->term) (n:int) (roots:term list) : tactic =
  let tmpl = `read (memory :> bytes128 (word_add in_p (word (16 * K)))) s0 = inblock K` in
  SUBGOAL_THEN (list_mk_conj (map (fun k -> vsubst [idx k,`K:num`] tmpl) (0--(n-1)))) STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN (vsubst [idx (n-1),`K:num`] `K < nblocks`) ASSUME_TAC THENL
     [MAP_EVERY UNDISCH_TAC roots THEN ARITH_TAC; ALL_TAC] THEN
    REPEAT CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC];;
let blk_from (base:term) k = mk_binop `(+):num->num->num` base (mk_small_numeral k);;

let INPUT_SPLIT_TAC_dec =
  INPUT_SPLIT_DEC (blk_from `4*i`) 8 [`nblocks DIV 4 = loop_count`; `i < loop_count - 1`; `2 <= loop_count`] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE `16 * (4*i+0) = 64*i`; ARITH_RULE `16 * (4*i+1) = 64*i+16`;
     ARITH_RULE `16 * (4*i+2) = 64*i+32`; ARITH_RULE `16 * (4*i+3) = 64*i+48`;
     ARITH_RULE `16 * (4*i+4) = 64*i+64`; ARITH_RULE `16 * (4*i+5) = 64*i+80`;
     ARITH_RULE `16 * (4*i+6) = 64*i+96`; ARITH_RULE `16 * (4*i+7) = 64*i+112`]);;

(* Common leg entry: strip the hypotheses, ghost the scratch lanes, ENSURES_INIT at s0 and unfold
   the htable block; HTABLE_STRIP_DEC then splits the unfolded htable facts into the assumptions. *)
let LEG_INIT_DEC (ghosts:string list) : tactic =
  STRIP_TAC THEN REWRITE_TAC[fst AES256_GCM_DEC_EXEC] THEN
  MAP_EVERY (fun rn -> GHOST_INTRO_TAC (mk_var("ghost_"^rn,`:int64`)) (parse_term("read "^rn))) ghosts THEN
  ENSURES_INIT_TAC "s0" THEN
  (if ghosts = [] then ALL_TAC
   else RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV BETA_CONV)) THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_4]) THEN REWRITE_TAC[htable_mem_4];;
let HTABLE_STRIP_DEC : tactic =
  FIRST_X_ASSUM(fun th -> if is_conj(concl th) && (let s = string_of_term(concl th) in
      contains "h_power" s && contains "htable_p" s) then STRIP_ASSUME_TAC th else NO_TAC);;

let setup_tac_dec =
  LEG_INIT_DEC ghost_lanes_dec THEN
  SUBGOAL_THEN `4*i+7 < nblocks` ASSUME_TAC THENL
   [UNDISCH_TAC `nblocks DIV 4 = loop_count` THEN UNDISCH_TAC `i < loop_count - 1` THEN
    UNDISCH_TAC `2 <= loop_count` THEN ARITH_TAC; ALL_TAC] THEN
  INPUT_SPLIT_TAC_dec THEN HTABLE_STRIP_DEC;;

(* ---- Staged-block reconstruction (native-safe; ivlo/ivhi VARIABLE lanes) ----
   A persistent-lane form (RHS = compound word_subword(rev8(ctr_block 2))(..) memory read at an OLD state)
   crashes native ARM_STEP_TAC.  We use ivec-half VARIABLES ivlo/ivhi and state
   lanes as `= ivlo`/`= word_subword ivhi (0,32)` (variable RHS -> ARM_STEP-safe).  We do the same:
   IVEC_SPLIT_dec (ABBREV ivlo/ivhi + join relation), SLOT_PRIME_E (variable-form lanes), MERGE_CTR128_FOLD_E
   (reconstruct via CTR_BLOCK_BUILD_V_DEC given the join relation). *)
let splitL  = el 1 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT);;
let splitL2 = el 2 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT);;
let woff_sp n = mk_comb(mk_comb(`word_add:int64->int64->int64`,`stackpointer:int64`),
                        mk_comb(`word:num->int64`,mk_small_numeral n));;
let baseline_of_dec asl off =
  let addr = woff_sp off in
  tryfind (fun (_,th) -> match concl th with
    | Comb(Comb(Const("=",_),
        Comb(Comb(Const("read",_),Comb(Comb(_,Const("memory",_)),Comb(Const("bytes128",_),a))),
             Var("s0",_))),_) when a = addr -> th
    | _ -> fail()) asl;;
(* split the resident ivec bytes128 baseline into ABBREV'd 64-bit halves ivlo/ivhi (+ join relation). *)
let IVEC_SPLIT_dec : tactic =
  UNDISCH_TAC `read (memory :> bytes128 ivec_p) s0 = word_reversefields 8 (ctr_block nonce c)` THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [el 1 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT)] THEN
  DISCH_TAC THEN
  ABBREV_TAC `ivlo:int64 = read (memory :> bytes64 ivec_p) s0` THEN
  ABBREV_TAC `ivhi:int64 = read (memory :> bytes64 (word_add ivec_p (word 8))) s0`;;
let find_join asl =
  tryfind (fun (_,th) -> if can (term_match [] `word_join (ivhi:int64) (ivlo:int64):int128 = xx`) (concl th)
                         then th else fail()) asl;;
(* lo-lane: read(bytes64 sp+off)s0 = ivlo  [B64 + baseline + TRANS via subword(ctr2)(0,64) + SLOT_LO(join)] *)
let prime_lo_E off : tactic = fun (asl,w) ->
  let tm = mk_eq(mk_comb(mk_comb(`read:(armstate,int64)component->armstate->int64`,
              mk_comb(mk_comb(`(:>):(armstate,int64->byte)component->(int64->byte,int64)component->(armstate,int64)component`,`memory`),
                      mk_comb(`bytes64`,woff_sp off))),`s0:armstate`),`ivlo:int64`) in
  let bl = baseline_of_dec asl off in
  let sl = MATCH_MP SLOT_LO (find_join asl) in
  (SUBGOAL_THEN tm ASSUME_TAC THENL
   [REWRITE_TAC[B64_OF_B128_LO; bl] THEN
    TRANS_TAC EQ_TRANS `word_subword (word_reversefields 8 (ctr_block nonce c):int128) (0,64):int64` THEN
    CONJ_TAC THENL [REWRITE_TAC[ctr_block] THEN CONV_TAC WORD_BLAST; ACCEPT_TAC sl]; ALL_TAC]) (asl,w);;
(* mid-lane: read(bytes32 sp+off+8)s0 = word_subword ivhi (0,32) [B32 + addr_rw + baseline + TRANS + SLOT_MID] *)
let prime_mid_E off : tactic = fun (asl,w) ->
  let tm = mk_eq(mk_comb(mk_comb(`read:(armstate,int32)component->armstate->int32`,
              mk_comb(mk_comb(`(:>):(armstate,int64->byte)component->(int64->byte,int32)component->(armstate,int32)component`,`memory`),
                      mk_comb(`bytes32`,woff_sp (off+8)))),`s0:armstate`),`word_subword (ivhi:int64) (0,32):int32`) in
  let bl = baseline_of_dec asl off in
  let sm = MATCH_MP SLOT_MID (find_join asl) in
  let addr_rw = WORD_RULE (mk_eq(woff_sp (off+8), mk_comb(mk_comb(`word_add:int64->int64->int64`, woff_sp off),`word 8:int64`))) in
  (SUBGOAL_THEN tm ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[addr_rw] THEN REWRITE_TAC[B32_OF_B128_MID; bl] THEN
    TRANS_TAC EQ_TRANS `word_subword (word_reversefields 8 (ctr_block nonce c):int128) (64,32):int32` THEN
    CONJ_TAC THENL [REWRITE_TAC[ctr_block] THEN CONV_TAC WORD_BLAST; ACCEPT_TAC sm]; ALL_TAC]) (asl,w);;
let SLOT_PRIME_E : tactic =
  EVERY (map (fun off -> prime_lo_E off THEN prime_mid_E off) [160;176;192;208]);;
(* reconstruct read(bytes128 sp+off)sname = rev8(ctr_block cval) from the ivlo/ivhi lanes + the +12 counter store,
   folding via CTR_BLOCK_BUILD_V_DEC (needs the join relation). *)
let MERGE_CTR128_FOLD_E off cval sname : tactic = fun (asl,w) ->
  let b128 = mk_comb(mk_comb(`read:(armstate,int128)component->armstate->int128`,
              mk_comb(mk_comb(`(:>):(armstate,int64->byte)component->(int64->byte,int128)component->(armstate,int128)component`,`memory`),
                      mk_comb(`bytes128`,woff_sp off))),mk_var(sname,`:armstate`)) in
  let target = mk_eq(b128, mk_comb(mk_comb(`word_reversefields:num->int128->int128`,`8`),
                                   mk_comb(mk_comb(`ctr_block:(96)word->num->int128`,`nonce:(96)word`),cval))) in
  let sp128 = CONV_RULE(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)(ISPECL [`memory`; woff_sp off; mk_var(sname,`:armstate`)] splitL) in
  let sp64  = CONV_RULE(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)(ISPECL [`memory`; woff_sp (off+8); mk_var(sname,`:armstate`)] splitL2) in
  let bv = INST [cval,`cval:num`] (MATCH_MP CTR_BLOCK_BUILD_V_DEC (find_join asl)) in
  (SUBGOAL_THEN target ASSUME_TAC THENL
   [GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [sp128; sp64] THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[CTR_ZX_NORM] THEN
    REWRITE_TAC[GSYM WORD_ADD] THEN
    (fun (a,g) ->
       let brs = find_terms (fun t -> match t with Comb(Const("word_bytereverse",_),_) -> true | _ -> false) (lhs g) in
       let idx_exprs = setify (List.concat_map (fun br ->
          find_terms (fun t -> match t with Comb(Const("word",_),e) when not(is_numeral e) -> true | _ -> false) br) brs) in
       (EVERY (map (fun we -> let e = rand we in
          if e = cval then ALL_TAC else
          GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [ARITH_RULE (mk_eq(e,cval))]) idx_exprs)) (a,g)) THEN
    ACCEPT_TAC bv;
    ALL_TAC]) (asl,w);;
(* (store_step, slot_off, body-end block index cval).  store steps from disasm: 192@16,176@20,208@32,160@35. *)
let merges_dec_fold = [ (16, 192, `4*i+c+6`); (20, 176, `4*i+c+5`); (32, 208, `4*i+c+7`); (35, 160, `4*i+c+4`) ];;

let step_body_all =
  setup_tac_dec THEN
  IVEC_SPLIT_dec THEN
  SLOT_PRIME_E THEN
  DEC_STEPS_TAC REDSETX_DEC (merge_hook merges_dec_fold MERGE_CTR128_FOLD_E) (1--193) THEN
  DEC_NORM_ASM_TAC;;

let BODYLEG = prove(body_goal_dec,
  step_body_all THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[SWP_SUB_LEMMA_DEC_L1] THEN
  REPEAT CONJ_TAC THEN CLOSE_DEC);;

(* ==================== LEG: FILL ==================== *)
(* ============================================================================
   dec-256 SWP FILL leg: whole-fn precond @ pc+0x2c  ->  swp_inv 0 @ pc+0x26c.
   Establishes the mid-pipeline invariant at the first steady head (i=0), from the
   C-argument preconditions (round keys / ivec / tag / htable / input in memory).
   Reuses the bodyleg steppers, invariant and closers; the ivec halves are
   ABBREV'd ivlo/ivhi (IVEC_SPLIT_dec) as in the body leg.
   ============================================================================ *)

(* loop_count is bounded by the input length. *)
let lc_bound = prove(`nblocks DIV 4 = loop_count /\ 16 * nblocks < 2 EXP 64 ==> loop_count < 2 EXP 64`,
  STRIP_TAC THEN
  SUBGOAL_THEN `loop_count <= nblocks` MP_TAC THENL
   [EXPAND_TAC "loop_count" THEN ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `16 * nblocks < 2 EXP 64` THEN ARITH_TAC);;

(* FILL precondition @ pc+0x2c: the whole-fn entry state (C args + ivec/tag/htable/input in memory).
   Mirrors the enc-256 AES256_GCM_DEC_CORRECT precond, dec-256 adapted (aes256_cipher, wordlist(key_p,15), input-frame). *)
let fill_pre_body = `read X3 s = tag_p /\ read X4 s = ivec_p /\ read X6 s = htable_p /\ read SP s = stackpointer /\
   read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
   read (memory :> bytes128 ivec_p) s = word_reversefields 8 (ctr_block nonce c) /\
   wordlist_from_memory(key_p,15) s = MAP (word_reversefields 8) rk /\
   read X0 s = in_p /\ read X2 s = out_p /\ read X5 s = key_p /\
   read X1 s = word len_bits /\
   (!j. j < nblocks ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s = inblock j) /\
   htable_mem_4 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s`;;
let fill_pre = mk_abs(`s:armstate`, list_mk_conj(
   `aligned_bytes_loaded s (word pc) aes256_gcm_dec_mc` ::
   `read PC s = word (pc + 0x2c)` :: conjuncts fill_pre_body));;
let fill_post = leg_state_dec swp_inv `0x26c` `0`;;
(* fill hypotheses: like the bodyleg's but WITHOUT `i`, plus the key_p nonoverlaps. *)
let fill_hyps = mk_leg_hyps [`2 <= loop_count`] [`len_bits < 2 EXP 64`]
  [`nonoverlapping (key_p:int64,240) (word_add stackpointer (word 160):int64,64)`;
   `nonoverlapping (key_p:int64,240) (out_p:int64,16*nblocks)`;
   `nonoverlapping (key_p:int64,240) (tag_p:int64,16)`];;
let fill_frame = `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
      MAYCHANGE [X19; X20; X21; X22; X23; X24; X25; X26; X27; X28; X29; X30] ,,
      MAYCHANGE [Q0; Q1; Q2; Q3; Q4; Q5; Q6; Q7; Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15; Q16; Q17; Q29; Q30; Q31] ,,
      MAYCHANGE [memory :> bytes(out_p:int64, 16 * nblocks)] ,,
      MAYCHANGE [memory :> bytes(word_add stackpointer (word 160):int64, 64)] ,, MAYCHANGE [events]`;;
let fill_goal = mk_leg_goal fill_hyps fill_pre fill_post fill_frame;;
(* The fill is simulated ONCE, up to the cbz@0x268, under the weaker 1 <= loop_count (its prefetch of
   blocks 4..7 is invisible to the invariant).  FILLLEG (cbz not taken, 2 <= loop_count) and the
   loop_count = 1 composition LEG_LC1 (cbz taken, into the drain at 0x574) are one-instruction hops from it. *)
let fill_hyps1 = mk_leg_hyps [`1 <= loop_count`] [`len_bits < 2 EXP 64`]
  [`nonoverlapping (key_p:int64,240) (word_add stackpointer (word 160):int64,64)`;
   `nonoverlapping (key_p:int64,240) (out_p:int64,16*nblocks)`;
   `nonoverlapping (key_p:int64,240) (tag_p:int64,16)`];;
let fill_cbz_goal = mk_leg_goal fill_hyps1 fill_pre (leg_state_dec swp_inv `0x268` `0`) fill_frame;;

(* ---- FILL setup: STRIP hyps, ENSURES_INIT @s0 (=pc+0x2c), IVEC-split (Approach-E), input-frame pin, guard facts. ---- *)
(* input-frame pin: the fill loads blocks 0..3 (in_p+{0,16,32,48}); pin them (nblocks>=4 from 1<=loop_count).
   The prefetched blocks 4..7 stay symbolic reads: the invariant never mentions them. *)
let FILL_INPUT_SPLIT_TAC = INPUT_SPLIT_DEC mk_small_numeral 4 [`nblocks DIV 4 = loop_count`; `1 <= loop_count`];;

(* KEY_EXPAND_TAC: expand wordlist_from_memory(key_p,15) s0 = MAP rev8 rk into the 15 individual round-key
   reads read(bytes128 key_p+16k) s0 = word_reversefields 8 (EL k rk) (the FILL ldr q18..q2 loads at steps 1-15
   read these at s0; needed to close the round-key Q-reg invariant conjuncts). *)
let KEY_EXPAND_TAC : tactic = fun (asl,w) ->
  let cs = map (fun (_,th) -> concl th) asl in
  let wl = find (fun t -> is_eq t &&
                 (try fst(dest_const(fst(strip_comb(lhs t)))) = "wordlist_from_memory"
                  with _ -> false)) cs in
  let rkeq = find (fun t -> try is_eq t && rhs t = `rk:(int128)list` with _->false) cs in
  let wl_expanded = CONV_RULE(LAND_CONV WORDLIST_FROM_MEMORY_CONV) (ASSUME wl) in
  let expanded = REWRITE_RULE[MAP; CONS_11] (GEN_REWRITE_RULE (RAND_CONV o RAND_CONV) [SYM(ASSUME rkeq)] wl_expanded) in
  STRIP_ASSUME_TAC expanded (asl,w);;

let fill_setup_tac =
  LEG_INIT_DEC [] THEN IVEC_SPLIT_dec THEN FILL_INPUT_SPLIT_TAC THEN HTABLE_STRIP_DEC THEN KEY_EXPAND_TAC;;

(* ---- Approach-E machinery (bodyleg reuse + FILL specifics) ---- *)
let find_ctr_join asl =
  snd(find (fun (_,th) -> try let c = concl th in is_eq c &&
    (match lhs c with Comb(Comb(Const("word_join",_),_),_) -> true | _ -> false) &&
    contains "ctr_block" (string_of_term(rhs c)) with _ -> false) asl);;

(* FILL mid-lane prime: from the stp-store `read(bytes64 sp+(off+8)) sK = ivhi`, split bytes64->bytes32 and
   derive the mid lane `read(bytes32 sp+(off+8)) sK = word_subword ivhi (0,32)` (Approach-E variable form). *)
let fill_prime_mid off sK : tactic = fun (asl,w) ->
  let sv = mk_var(sK,`:armstate`) in
  let split_hi = CONV_RULE(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)
    (ISPECL [`memory`; woff_sp (off+8); sv] splitL2) in
  let rd64_hi = lhs(concl split_hi) in
  let hi_th = find (fun (_,th) -> try lhs(concl th) = rd64_hi && rhs(concl th) = `ivhi:int64` with _ -> false) asl in
  let iv_eq = TRANS (SYM (snd hi_th)) split_hi in
  let mid = mk_eq(rand(rhs(concl split_hi)), `word_subword (ivhi:int64) (0,32):int32`) in
  (SUBGOAL_THEN mid ASSUME_TAC THENL
   [MP_TAC iv_eq THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN CONV_TAC WORD_BLAST; ALL_TAC]) (asl,w);;
let fill_prime_mids sK : tactic = MAP_EVERY (fun off -> fill_prime_mid off sK) [160;176;192;208];;
let fill_prime_hook k : tactic = if k = 23 then fill_prime_mids "s23" else ALL_TAC;;

(* base-counter lemma: the ivec's counter field (rev8(ctr_block nonce c)) reverses back to `word c`.
   Derived from the shared X13_SETUP (which recovers the counter word robustly for symbolic c via
   BITBLAST_RULE): apply word_zx:int64->int32 to both sides and collapse the double zx (ZX_COUNTER_UD). *)
let BASE_CTR_DEC = prove(
  `word_join (ivhi:int64) (ivlo:int64):int128 = word_reversefields 8 (ctr_block nonce c)
   ==> word_bytereverse (word_zx (word_ushr ivhi 32):int32) = word c:int32`,
  DISCH_THEN(fun th ->
    ACCEPT_TAC(REWRITE_RULE[ZX_COUNTER_UD]
      (AP_TERM `word_zx:int64->int32` (MATCH_MP X13_SETUP th)))));;

(* FILL guard + cbz resolution (0x88 counter setup -> cbz@0xa8 fall-through -> 0xac).  Establishes
   val(word len_bits)=len_bits (needs len_bits<2^64), X1=word loop_count, val(word loop_count)=loop_count,
   ~(X1=word 0); steps the cbz (produces `if`) then collapses it via loop_count>=2. *)
let fill_guard_facts sK : tactic =
  let x1lc = subst [mk_var(sK,`:armstate`),`s:armstate`] `read X1 s = word loop_count` in
  let x1ne = subst [mk_var(sK,`:armstate`),`s:armstate`] `~(read X1 s = word 0)` in
  SUBGOAL_THEN `val(word len_bits:int64) = len_bits` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    UNDISCH_TAC `len_bits < 2 EXP 64` THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN x1lc ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN REWRITE_TAC[WORD_USHR_COMPOSE] THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
    REWRITE_TAC[word_ushr] THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY EXPAND_TAC ["loop_count"; "nblocks"] THEN
    REWRITE_TAC[DIV_DIV] THEN AP_TERM_TAC THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  SUBGOAL_THEN `val(word loop_count:int64) = loop_count` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    MAP_EVERY (fun t -> TRY(UNDISCH_TAC t)) [`nblocks DIV 4 = loop_count`; `16 * nblocks < 2 EXP 64`] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN x1ne ASSUME_TAC THENL
   [GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [ASSUME x1lc] THEN
    REWRITE_TAC[GSYM VAL_EQ_0] THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `1 <= loop_count` THEN ARITH_TAC; ALL_TAC];;
let FILL_GUARD_CBZ_TAC : tactic =
  fill_guard_facts "s31" THEN
  gkeepN REDSETX_DEC AES256_GCM_DEC_EXEC "s32" THEN
  SUBGOAL_THEN `(val (word_ushr (word_ushr (word_ushr (word len_bits) 3) 4) 2:int64) = 0) <=> F`
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th]) THENL
   [REWRITE_TAC[] THEN
    SUBGOAL_THEN `word_ushr (word_ushr (word_ushr (word len_bits) 3) 4) 2:int64 = word loop_count`
      SUBST1_TAC THENL
     [ONCE_REWRITE_TAC[GSYM(ASSUME `read X1 s32 = word_ushr (word_ushr (word_ushr (word len_bits) 3) 4) 2`)] THEN
      ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `1 <= loop_count` THEN ARITH_TAC; ALL_TAC] THEN
  DEC_NORM_ASM_TAC;;

(* FILL counter merge (at the STORE step, mirroring bodyleg merges_dec_fold): reconstruct
   read(bytes128 sp+off) sK = rev8(ctr_block nonce cval) from the lo/mid lanes + the just-stored +12 counter
   lane.  The fill counter lane is runtime `word_add base (word K)` (base = rev(ivhi>>32)); BASE_CTR_DEC folds
   base->word 2, then a live-typed WORD_BLAST eq normalizes word_add(word 2)(word K)->word cval, then
   CTR_BLOCK_BUILD_V_DEC closes.  (Bodyleg's MERGE_CTR128_FOLD_E had a clean symbolic word cval already.) *)
(* For all 4 counters (folds + persists): after splitting bytes128->lo/mid/counter
   lanes + ASM_REWRITE + REWRITE[bc] (base->word 2), the goal is `<lane-expr> = rev8(ctr_block cval)` and bv is
   `<bv-lhs> = rev8(ctr_block cval)`.  The lane-expr's counter core (arg of the non-ivhi word_bytereverse) is a
   word_zx-tower over word_add(word 2)(word K) [K=1/2/3] or a longer word_zx-tower over word 2 [K=0, the +0
   collapsed by the assembler]; bv's core is word_zx(word_zx(word cval)).  Bridge the two cores via a live WORD_BLAST
   eq (WORD_BLAST can't see through word_bytereverse, so we normalize its ARGUMENT to bv's exact core form, NOT to
   word cval), then ACCEPT bv.  Bare hand-typed widths mismatch -> always build the eq from live terms. *)
let MERGE_CTR128_FILL off cval sK : tactic = fun (asl,w) ->
  let b128 = mk_comb(mk_comb(`read:(armstate,int128)component->armstate->int128`,
              mk_comb(mk_comb(`(:>):(armstate,int64->byte)component->(int64->byte,int128)component->(armstate,int128)component`,`memory`),
                      mk_comb(`bytes128`,woff_sp off))),mk_var(sK,`:armstate`)) in
  let target = mk_eq(b128, mk_comb(mk_comb(`word_reversefields:num->int128->int128`,`8`),
                                   mk_comb(mk_comb(`ctr_block:(96)word->num->int128`,`nonce:(96)word`),cval))) in
  let sp128 = CONV_RULE(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)(ISPECL [`memory`; woff_sp off; mk_var(sK,`:armstate`)] splitL) in
  let sp64  = CONV_RULE(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)(ISPECL [`memory`; woff_sp (off+8); mk_var(sK,`:armstate`)] splitL2) in
  let bc = MATCH_MP BASE_CTR_DEC (find_ctr_join asl) in
  let bv = INST [cval,`cval:num`] (MATCH_MP CTR_BLOCK_BUILD_V_DEC (find_ctr_join asl)) in
  let brev_noiv t = match t with Comb(Const("word_bytereverse",_),_) -> not(free_in `ivhi:int64` t) | _ -> false in
  let bv_core = rand(find_term brev_noiv (lhs(concl bv))) in
  (SUBGOAL_THEN target ASSUME_TAC THENL
   [GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [sp128; sp64] THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[bc] THEN
    (fun (a,g) ->
       let core = rand(find_term brev_noiv (lhs g)) in
       if core = bv_core then ACCEPT_TAC bv (a,g)
       else let ceq = prove(mk_eq(core, bv_core), REWRITE_TAC[ZXRT32] THEN CONV_TAC WORD_RULE) in
            (GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [ceq] THEN ACCEPT_TAC bv) (a,g));
    ALL_TAC]) (asl,w);;
(* merges at the STORE steps (str w,[sp,#off+12]; like the bodyleg's merges_dec_fold): 176@43(ctr3), 192@48(ctr4),
   208@53(ctr5), 160@56(ctr2).  Merging at the STORE (not reload) folds read(bytes128 sp+off)s(store)=rev8(ctr_block)
   EARLY, so it propagates via read-over-write to ALL later consumers: the AES input reload (Q3/Q8/Q12 = aes on the
   staged block), the reload-into-Q, and the staged-slot invariant conjunct at the final state.  (The reload-step
   merge folded too late -- at s(reload) -- so consumers reading s(reload-1) or the AES input saw the unfolded slot.) *)
let dec_fill_merges = [ (43, 176, `c+1`); (48, 192, `c+2`); (53, 208, `c+3`); (56, 160, `c:num`) ];;

(* ---- shared body/fill closers (rk15, INFOLD_dec, OUT_STORE_dec, CLOSE_DEC, ...) ---- *)

(* ---- FILL i=0 in-read folding: INFOLD_dec expects addresses in 16*(4*(i+1)+M) form + a body `i`; at i=0 the FILL
   reads are direct word N and there is no `i`.  INFOLD_FILL = INFOLD_dec's fold but with (a) FILL address norms
   (word N = word(16*M) for N=16..112) so sixteen_blk finds the block index, (b) the block bound 7<nblocks from
   2<=loop_count (not i<loop_count-2). ---- *)
let inp_addr_norms_fill =
  List.map (fun (n,m) -> WORD_RULE (subst [mk_small_numeral n,`N:num`; mk_small_numeral m,`M:num`]
              `word_add (in_p:int64) (word N):int64 = word_add in_p (word (16 * M))`))
    [(16,1);(32,2);(48,3);(64,4);(80,5);(96,6);(112,7)];;
let INFOLD_FILL : tactic =
  REWRITE_TAC inp_addr_norms_fill THEN
  (fun (asl,w) ->
    let inreads = setify(find_terms is_inp_bytes128_read w) in
    if inreads = [] then ALL_TAC (asl,w)
    else (EVERY (map (fun rd ->
       let blk = sixteen_blk rd in
       let st = inpread_state rd in
       TRY(SUBGOAL_THEN (mk_eq(rd, mk_comb(`inblock:num->int128`, blk))) ASSUME_TAC THENL
        [(FIRST_ASSUM(fun fa -> if (try is_forall(concl fa) && free_in `in_p:int64`(concl fa)
                                       && inpforall_state (concl fa) = st with _->false)
                                  then MATCH_MP_TAC fa else NO_TAC)
          ORELSE FIRST_ASSUM(fun fa -> if (try is_forall(concl fa) && free_in `in_p:int64`(concl fa) with _->false)
                                         then MATCH_MP_TAC fa else NO_TAC))
         THEN
         (SUBGOAL_THEN `3 < nblocks` ASSUME_TAC THENL
           [UNDISCH_TAC `nblocks DIV 4 = loop_count` THEN UNDISCH_TAC `1 <= loop_count` THEN ARITH_TAC; ALL_TAC]
          ORELSE ALL_TAC) THEN
         ASM_ARITH_TAC; ALL_TAC]))
      inreads)) (asl,w));;
(* i=0 index normalizations: 4*0+K = K (the FILL folds reads to bare inblock K, but the invariant RHS uses the
   symbolic 4*0+K form).  Applied in the GHASH-partial/in-read/out-store closers so both sides match for REFL. *)
let fill_idx_norms = map (fun k -> ARITH_RULE (subst [mk_small_numeral k,`K:num`] `4*0+K = K`)) [0;1;2;3;4;5;6;7;8;9];;
(* GHASH partial closer at i=0: INFOLD_FILL then the bodyleg reassemble tail + i=0 index norms. *)
let GHASH_PARTIAL_FILL : tactic =
  INFOLD_FILL THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[INBLOCK_REASSEMBLE; GSYM nist_input_block] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[nist_input_block] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC fill_idx_norms THEN                       (* 4*0+K -> K so LHS(inblock K)=RHS(inblock(4*0+K)) *)
  (TRY REFL_TAC THEN
   TRY (REWRITE_TAC[SWP_SUBWORD_JOIN_MID] THEN CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
        TRY(CONV_TAC WORD_BLAST)));;
(* FILL Q30 seed at i=0: the accumulator is nist_ghash .. tag0 (list_of_seq .. (4*0)) = nist_ghash .. tag0 [] =
   tag0 (GHASH over the empty list), so Q30 = half-swap(tag0) -- NO Horner reduce (unlike the bodyleg's 4i seed).
   Reduce the RHS accumulator to tag0, then the machine lanes (byte-tower of rev8 tag0) = half-swap(tag0) by WORD_BLAST. *)
let SEED_TAG0_REDUCE = prove(
  `nist_ghash (aes256_cipher (word 0) rk) tag0 (list_of_seq (nist_input_block inblock) (4 * 0)) = tag0`,
  REWRITE_TAC[MULT_CLAUSES; LIST_OF_SEQ; nist_ghash]);;
let SEED_FILL : tactic =
  REWRITE_TAC[SEED_TAG0_REDUCE] THEN CONV_TAC WORD_BLAST;;

(* FILL out-store closer (block-2 one-ahead): read(out_p+64*0+32) s144 = word_xor(aes256_ctr_block(4*0+2))(inblock
   (4*0+2)).  At i=0 the address is out_p+64*0+32 directly (no 64*(i+1) form), so skip out_addr_norms; resolve the
   store via ASM, in-fold the embedded in_p read (INFOLD_FILL), then the bodyleg block-close + i=0 idx norms. *)
(* i=0 out address: the goal reads out_p+word(64*0+32); the store fact is at out_p+word 32.  Normalize. *)
let out_addr_norms_fill = [ WORD_RULE `word_add (out_p:int64) (word (64*0+32)) = word_add out_p (word 32)` ];;
(* i=0 counter index norms for aes256_ctr_block unfolding: aes256_ctr_block c .. K = rev8(aes256_cipher(ctr_block(K+c))..);
   the resident (machine) counter is c+K, so bridge the target K+c -> c+K at the num level (K=0 collapses to c). *)
let fill_ctr_idx_norms = map (fun k ->
  ARITH_RULE (mk_eq(mk_binop `+` (mk_small_numeral k) `c:num`,
                    if k = 0 then `c:num` else mk_binop `+` `c:num` (mk_small_numeral k)))) [0;1;2;3;4;5;6;7];;
let OUT_STORE_FILL : tactic =
  REWRITE_TAC out_addr_norms_fill THEN
  ASM_REWRITE_TAC[] THEN INFOLD_FILL THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ADD_CLAUSES] THEN REWRITE_TAC fill_idx_norms THEN
  (* Reconstruct: XOR_AES256_CIPHER_RECONSTRUCT_DEC folds the machine AES tower to
     rev8(aes256_cipher(ctr_block(c+K))rk); WORD_REVERSEFIELDS_REVERSEFIELDS undoes the rev8-of-rev8 on the ctr-block
     + round keys; MAP+rk15 rebuilds rk; aes256_ctr_block def + K+c -> c+K bridge makes RHS match. *)
  ((REWRITE_TAC[XOR_AES256_CIPHER_RECONSTRUCT_DEC] THEN
    REWRITE_TAC[WORD_REVERSEFIELDS_REVERSEFIELDS] THEN REWRITE_TAC[MAP; WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[aes256_ctr_block] THEN REWRITE_TAC fill_ctr_idx_norms THEN REFL_TAC)
   ORELSE
   (REWRITE_TAC(map GSYM out_via_lemmas) THEN REWRITE_TAC[aes256_ctr_block] THEN REWRITE_TAC fill_ctr_idx_norms THEN
    (fun (asl,w) ->
       let c = try rand(find_term (fun t -> match t with Comb(Comb(Const("ctr_block",_),_),_) -> true | _ -> false) (rhs w))
               with _ -> `4` in
       let inb = lhand (lhs w) in
       MP_TAC(SPECL[c; inb] (GENL [`c:num`;`inb:int128`] (MATCH_MP KEYSTREAM_FOLD256 (ASSUME rk15)))) (asl,w)) THEN
    DISCH_TAC THEN POP_ASSUM(fun th -> REWRITE_TAC[GSYM th]) THEN CONV_TAC WORD_BITWISE_RULE)
   ORELSE ALL_TAC);;   (* never throw -- any unclosed residual surfaces at the final state. *)

(* FILL in-read closer (Q0/Q1/Q14 = inblock K): the read may already be folded to `inblock K` by INFOLD/ASM
   (leaving `inblock K = inblock(4*0+K)` = pure index-arith), OR be a raw read at in_p+word N (N=16..112) or bare
   in_p (block 0, offset 0).  Normalize 4*0+K->K and 4*0->0 on the RHS; normalize the addr (incl bare in_p ->
   in_p+word(16*0)); MATCH the in_p forall. *)
let IN_READ_FILL : tactic =
  REWRITE_TAC (ARITH_RULE `4*0=0` :: fill_idx_norms) THEN
  (* bare in_p (block 0, offset 0): the read address is exactly in_p (no word_add).  Rewrite in_p ->
     word_add in_p (word(16*0)) via SUBST1 ONLY in that case (guarded: goal LHS read address = bare in_p). *)
  (fun (asl,w) ->
     let is_bare = (try let rd = lhs w in
        let addr = rand(rand(rand(rator rd))) in fst(dest_var addr) = "in_p" with _ -> false) in
     (if is_bare then
        (SUBGOAL_THEN `in_p:int64 = word_add in_p (word (16 * 0))` SUBST1_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC])
      else TRY (REWRITE_TAC inp_addr_norms_fill)) (asl,w)) THEN
  (((fun (asl,w) ->
       FIRST_ASSUM(fun fa -> if (try is_forall(concl fa) && free_in `in_p:int64`(concl fa) with _->false)
                            then MATCH_MP_TAC fa else NO_TAC) (asl,w)) THEN
    (SUBGOAL_THEN `3 < nblocks` ASSUME_TAC THENL
      [UNDISCH_TAC `nblocks DIV 4 = loop_count` THEN UNDISCH_TAC `1 <= loop_count` THEN ARITH_TAC; ALL_TAC]
     ORELSE ALL_TAC) THEN ASM_ARITH_TAC)
   ORELSE ALL_TAC);;

(* ---- full fill stepper: setup -> steps 1-31 (+ mid-lane prime @ s23) -> guard/cbz -> body 33-143 (-> 0x268). ---- *)
let NSTEP_FILL = 143;;  (* 0x2c..0x264 straight-line, ending at the cbz@0x268 (taken by the hops). *)
(* body keeplist: REDSETX + X1 (so read X1 = word loop_count persists from the guard to the terminal cbz). *)
let REDSETX_FILL = "X1"::REDSETX_DEC;;
let fill_step_all =
  fill_setup_tac THEN
  (* steps 1-31: round keys, tag0, ivec pair -> 4 slots; prime the mid lanes at s23 (post the 4 stp). *)
  DEC_STEPS_TAC REDSETX_FILL fill_prime_hook (1--31) THEN
  (* guard + cbz @ 0xa8 -> 0xac *)
  FILL_GUARD_CBZ_TAC THEN
  (* body 33-143 (0xac..0x264) with counter merges at the RELOAD steps; keep X1 for the terminal cbz *)
  DEC_STEPS_TAC REDSETX_FILL (merge_hook dec_fill_merges MERGE_CTR128_FILL) (33--NSTEP_FILL) THEN
  DEC_NORM_ASM_TAC;;

(* ---- establish swp_inv 0 @ 0x26c: reuse the bodyleg CLOSE_DEC dispatcher at i=0.
   The post-state conjuncts have the same shapes as the bodyleg's (with 4*0+K concrete), so CLOSE_DEC
   handles them; the Q30 seed at i=0 = half-swap(nist_ghash..(4*0)) = half-swap(tag0) (GHASH over empty list),
   the out-frame forall j<0 is VACUOUS.  The cbz@0x268 (step 144) falls through since 2<=loop_count. ---- *)
(* FILL out-frame at i=0: the incoming FILL has NO out-frame forall (fresh start), so the split's vacuous
   `forall j. j < 4*0 ==> ...` branch can't MATCH_ACCEPT an incoming forall -> discharge it via MULT_CLAUSES+LT
   +ARITH FIRST.  The 4 concrete blocks (j=4*0+{0,1,2,3}) are all fresh keystream folds (blk 4*0+2 = one-ahead
   carry from the invariant conjunct). Otherwise identical to the bodyleg OUT_FRAME_dec. *)
let OUT_FRAME_fill : tactic =
  REWRITE_TAC[ARITH_RULE `j < 4 * (i+1) <=>
                          j < 4 * i \/ j = 4*i+0 \/ j = 4*i+1 \/ j = 4*i+2 \/ j = 4*i+3`] THEN
  ASM_REWRITE_TAC[TAUT `p \/ q ==> r <=> (p ==> r) /\ (q ==> r)`] THEN
  REWRITE_TAC[FORALL_AND_THM; FORALL_UNWIND_THM2] THEN
  REWRITE_TAC[ARITH_RULE `16 * (4*i+0) = 64*i`; ARITH_RULE `16 * (4*i+1) = 64*i+16`;
     ARITH_RULE `16 * (4*i+2) = 64*i+32`; ARITH_RULE `16 * (4*i+3) = 64*i+48`] THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  TRY (REWRITE_TAC[MULT_CLAUSES; LT] THEN ARITH_TAC) THEN          (* vacuous j<4*0 forall *)
  TRY (FIRST_X_ASSUM (fun th -> if (try is_forall(concl th) && free_in `out_p:int64` (concl th) with _->false)
                                then MATCH_ACCEPT_TAC th else NO_TAC)) THEN
  TRY (ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  ASM_REWRITE_TAC[] THEN INFOLD_dec THEN ASM_REWRITE_TAC[] THEN
  OUT_BLOCK_CLOSE_dec;;
(* FILL register-setup closers (X1/X15/X9/X13): the FILL computes these registers at runtime from len_bits/ivhi,
   while the bodyleg's invariant has them pre-set symbolically. *)
let REG_X15_FILL : tactic =   (* word_ushr(word len_bits) 3 = word(len_bits DIV 8) *)
  REWRITE_TAC[word_ushr] THEN AP_TERM_TAC THEN
  SUBGOAL_THEN `val(word len_bits:int64) = len_bits` SUBST1_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    UNDISCH_TAC `len_bits < 2 EXP 64` THEN ARITH_TAC; ARITH_TAC];;
let REG_X9_FILL : tactic =   (* word_and(word_ushr(word_ushr(word len_bits)3)4)(word 3) = word loop_remain *)
  REWRITE_TAC[WORD_USHR_COMPOSE] THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
  REWRITE_TAC[word_ushr] THEN
  SUBGOAL_THEN `val(word len_bits:int64) = len_bits` SUBST1_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    UNDISCH_TAC `len_bits < 2 EXP 64` THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `3 = 2 EXP 2 - 1`] THEN
  REWRITE_TAC[WORD_AND_MASK_WORD; VAL_WORD; DIMINDEX_64] THEN REWRITE_TAC[MOD_MOD_EXP_MIN] THEN
  MAP_EVERY EXPAND_TAC ["loop_remain"; "nblocks"] THEN AP_TERM_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC;;
let REG_X1_FILL : tactic =   (* word_sub(word loop_count)(word 1) = word(loop_count-1) *)
  SUBGOAL_THEN `val(word loop_count:int64) = loop_count` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    MAP_EVERY (fun t -> TRY(UNDISCH_TAC t)) [`nblocks DIV 4 = loop_count`; `16 * nblocks < 2 EXP 64`] THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[WORD_SUB] THEN COND_CASES_TAC THENL
   [AP_TERM_TAC THEN REWRITE_TAC[VAL_WORD_1];
    FIRST_X_ASSUM MP_TAC THEN REWRITE_TAC[VAL_WORD_1] THEN
    UNDISCH_TAC `1 <= loop_count` THEN ASM_REWRITE_TAC[] THEN ARITH_TAC];;
let REG_X13_FILL : tactic =   (* X13 counter at i=0: word_zx(word_bytereverse(word_zx(word_ushr ivhi 32))) = word_zx(word(4i+c)) at i=0 *)
  fun (asl,w) ->
    (REWRITE_TAC[MATCH_MP BASE_CTR_DEC (find_ctr_join asl)] THEN
     REWRITE_TAC[ARITH_RULE `4 * 0 + c = c`]) (asl,w);;
(* FILL closer: route foralls -> OUT_FRAME_fill; the FILL register-setup forms -> their closers; else the bodyleg
   dispatcher.  X15/X9/X13 are new (not in CLOSE_DEC); X1 (word_sub) overrides close_x1_dec's body form. *)
let CLOSE_FILL : tactic = fun (asl,w) ->
  let has c t = can (find_term (fun u -> try fst(dest_const(fst(strip_comb u)))=c with _->false)) t in
  let hd t = try fst(dest_const(fst(strip_comb t))) with _->"" in
  (* head NAME whether const OR var (inblock is a VARIABLE in the spec, so `has`/`hd`(const) miss it). *)
  let hdname t = (try fst(dest_const(fst(strip_comb t))) with _ -> (try fst(dest_var(fst(strip_comb t))) with _ -> "")) in
  let inb = `inblock:num->int128` in
  let deep_ghash = try has "nist_ghash" w with _ -> false in
  if is_forall w then OUT_FRAME_fill (asl,w)
  else if is_eq w && hd(lhs w)="word_ushr" && free_in `len_bits:num` w && not(has "word_and" w) then REG_X15_FILL (asl,w)
  else if is_eq w && hd(lhs w)="word_and" && free_in `len_bits:num` w then REG_X9_FILL (asl,w)
  else if is_eq w && hd(lhs w)="word_sub" && free_in `loop_count:num` w && not(has "pc" w) then REG_X1_FILL (asl,w)
  else if is_eq w && hd(lhs w)="word_zx" && has "word_ushr" (lhs w) && free_in `ivhi:int64` (lhs w) then REG_X13_FILL (asl,w)
  (* Q30 seed (deep nist_ghash over the empty list at i=0 = half-swap(tag0)): reduce to tag0 + WORD_BLAST. *)
  else if deep_ghash then SEED_FILL (asl,w)
  (* pure index-arith residual inblock K = inblock(4*0+K) (in-read already folded by INFOLD/ASM). *)
  else if is_eq w && hdname(lhs w)="inblock" && hdname(rhs w)="inblock" then
    (REWRITE_TAC (ARITH_RULE `4*0=0` :: fill_idx_norms) THEN REFL_TAC) (asl,w)
  (* Q0/Q1/Q14 inblock reads (read(bytes128 in_p+..) = inblock(4*0+K) or bare in_p = inblock(4*0)): in-read closer. *)
  else if is_eq w && hd(lhs w)="read" && free_in `in_p:int64` (lhs w) && free_in inb (rhs w) then IN_READ_FILL (asl,w)
  (* out-store block (read(bytes128 out_p+..) = word_xor(aes256_ctr_block..)(inblock..)): FILL i=0 out-store closer. *)
  else if is_eq w && hd(lhs w)="read" && free_in `out_p:int64` (lhs w) && has "aes256_ctr_block" (rhs w) then OUT_STORE_FILL (asl,w)
  (* GHASH partials (pmul/xor/zx towers embedding in_p reads): FILL in-fold variant. *)
  else if free_in `in_p:int64` w then (GHASH_PARTIAL_FILL ORELSE CLOSE_DEC) (asl,w)
  else CLOSE_DEC (asl,w);;

let FILL_TO_CBZ_DEC = GEN_ALL(prove(fill_cbz_goal,
  fill_step_all THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[SWP_SUB_LEMMA_DEC] THEN
  REPEAT CONJ_TAC THEN CLOSE_FILL));;

(* One-instruction hops out of a full swp_inv state: swp_inv_dec_at gives the invariant body for
   ENSURES_SEQUENCE_TAC, hop_init_dec opens the state, and after the step every conjunct is an unchanged
   read or the branch PC, resolved from the val fact assumed beforehand. *)
let REFOLD_ABI = REWRITE_TAC[GSYM MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI];;
let swp_inv_dec_at idx =
  rhs(concl((BETA_CONV THENC REWRITE_CONV[ADD_CLAUSES]) (mk_comb(swp_inv,idx))));;
let hop_init_dec : tactic =
  ENSURES_INIT_TAC "s0" THEN RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_4]) THEN REWRITE_TAC[htable_mem_4];;

(* FILLLEG: FILL_TO_CBZ_DEC, then the cbz@0x268 not taken (X1 = word (loop_count - 1), nonzero). *)
let FILLLEG = prove(fill_goal,
  STRIP_TAC THEN REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  ENSURES_SEQUENCE_TAC `pc + 0x268` (swp_inv_dec_at `0`) THEN CONJ_TAC THENL
   [REFOLD_ABI THEN MATCH_MP_TAC FILL_TO_CBZ_DEC THEN ASM_REWRITE_TAC[] THEN
    TRY(UNDISCH_TAC `2 <= loop_count` THEN ARITH_TAC);
    hop_init_dec THEN
    SUBGOAL_THEN `val (word (loop_count - 1):int64) = loop_count - 1` ASSUME_TAC THENL
     [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
      MAP_EVERY (fun t -> TRY(UNDISCH_TAC t)) [`nblocks DIV 4 = loop_count`; `16 * nblocks < 2 EXP 64`] THEN
      ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `~(val (word (loop_count - 1):int64) = 0)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `2 <= loop_count` THEN ARITH_TAC; ALL_TAC] THEN
    (* the stepper states the cbz condition as loop_count <= 1 *)
    SUBGOAL_THEN `~(loop_count <= 1)` ASSUME_TAC THENL
     [UNDISCH_TAC `2 <= loop_count` THEN ARITH_TAC; ALL_TAC] THEN
    ARM_STEPS_TAC AES256_GCM_DEC_EXEC [1] THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]]);;

(* ==================== LEG: DRAIN ==================== *)
(* ============================================================================
   dec-256 SWP DRAIN leg: swp_inv (loop_count-1) @ pc+0x570 (cbnz, x1=0 falls through)
   -> drain_bridge @ pc+0x6c0.  Finishes the LAST group (blocks 4(loop_count-1)..4*loop_count-1):
   settles Q30 = half-swap(nist_ghash .. tag0 (list_of_seq (nist_input_block inblock) (4*loop_count)))
   and stores the last group's outputs.  Mirrors the enc-256 SWP drain leg (drain_bridge @0xdd0),
   dec-256 adapted: GHASH over INPUT (ciphertext), aes256, bare `b 0x6c0` end (no body skip).
   Control flow (disasm): 0x570 cbnz x1 (x1=0 -> fall through, the DRAINLEG hop) ; 0x574..0x6b8
   straight-line drain (83 instrs; 3 output stores str q5/q12/q5 @ 0x6a4/0x6b4/0x6b8) ; 0x6bc b 0x6c0.
   Reuses the bodyleg front-matter + steppers + invariant + shared closers.
   ============================================================================ *)

(* ---- drain_bridge @ pc+0x6c0 (settled state feeding the 1-block tail).
   Q30 is SETTLED to half-swap(nist_ghash over 4*loop_count input blocks); the tail reloads Q12/Q13/Q14 from
   htable (0x6c0-0x6c8) so the bridge omits them.  Mirrors enc drain_bridge @0xdd0, dec-adapted (nist_input_block,
   half-swap not byteswap128, Q2=rev8(EL 14 rk) as the 15th round key). ---- *)
(* Q7 = the polyval-reduce constant, loop-carried (never written); the TAIL's Q30 reduce needs it pinned.
   Carried unchanged from swp_inv (which has it); closes by ASM in the drain (drain never writes Q7).
   Staged counter slot 160: carried UNCHANGED from the invariant @i=loop_count-1 (the drain never writes sp+160);
   the TAIL needs its nonce lanes to rebuild its per-block counter (it only re-stores the +12 counter word). *)
let drain_bridge = mk_abs(`s:armstate`, list_mk_conj
 [`aligned_bytes_loaded s (word pc) aes256_gcm_dec_mc`;
  `read PC s = word (pc + 0x6c0)`;
  `read X0 s = word_add in_p (word (64 * loop_count))`;
  `read X2 s = word_add out_p (word (64 * loop_count))`;
  `read X3 s = tag_p`; `read X4 s = ivec_p`; `read X6 s = htable_p`; `read SP s = stackpointer`;
  `read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0`;
  `read (memory :> bytes128 ivec_p) s = word_reversefields 8 (ctr_block nonce c)`;
  `read X13 s = word_zx (word (4 * loop_count + c):int32):int64`;
  `read X15 s = word(len_bits DIV 8)`; `read X9 s = word loop_remain`;
  `read Q18 s = word_reversefields 8 (EL 0 rk)`; `read Q19 s = word_reversefields 8 (EL 1 rk)`;
  `read Q20 s = word_reversefields 8 (EL 2 rk)`; `read Q21 s = word_reversefields 8 (EL 3 rk)`;
  `read Q22 s = word_reversefields 8 (EL 4 rk)`; `read Q23 s = word_reversefields 8 (EL 5 rk)`;
  `read Q24 s = word_reversefields 8 (EL 6 rk)`; `read Q25 s = word_reversefields 8 (EL 7 rk)`;
  `read Q26 s = word_reversefields 8 (EL 8 rk)`; `read Q27 s = word_reversefields 8 (EL 9 rk)`;
  `read Q28 s = word_reversefields 8 (EL 10 rk)`; `read Q15 s = word_reversefields 8 (EL 11 rk)`;
  `read Q16 s = word_reversefields 8 (EL 12 rk)`; `read Q17 s = word_reversefields 8 (EL 13 rk)`;
  `read Q2 s = word_reversefields 8 (EL 14 rk)`;
  `read Q7 s = word 13979173243358019584`;
  `read Q30 s = word_join
     ((word_subword (nist_ghash (aes256_cipher (word 0) rk) tag0
        (list_of_seq (nist_input_block inblock) (4 * loop_count))) (0,64)):int64)
     ((word_subword (nist_ghash (aes256_cipher (word 0) rk) tag0
        (list_of_seq (nist_input_block inblock) (4 * loop_count))) (64,64)):int64)`;
  `htable_mem_4 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s`;
  `read (memory :> bytes128 (word_add stackpointer (word 160))) s =
     word_reversefields 8 (ctr_block nonce (4 * (loop_count - 1) + c))`;
  `!j. j < nblocks ==> read (memory :> bytes128 (word_add in_p (word(16*j)))) s = inblock j`;
  `!j. j < 4 * loop_count ==> read (memory :> bytes128 (word_add out_p (word(16*j)))) s =
           word_xor (aes256_ctr_block c nonce rk j) (inblock j)`]);;

(* ---- drain_goal: swp_inv (loop_count-1) @0x570 -> drain_bridge @0x6c0. ---- *)
let drain_hyps = mk_leg_hyps [`2 <= loop_count`] [`len_bits < 2 EXP 64`] [];;
let drain_frame = fill_frame;;
let drain_goal = mk_leg_goal drain_hyps (leg_state_dec swp_inv `0x570` `loop_count - 1`) drain_bridge drain_frame;;
(* The drain proper is simulated ONCE from 0x574 under 1 <= loop_count; DRAINLEG (cbnz@0x570 not
   taken) and LEG_LC1 (cbz@0x268 taken) are hops into it. *)
let drain_hyps1 = mk_leg_hyps [`1 <= loop_count`] [`len_bits < 2 EXP 64`] [];;
let drain574_goal = mk_leg_goal drain_hyps1 (leg_state_dec swp_inv `0x574` `loop_count - 1`) drain_bridge drain_frame;;

(* ---- drain setup: enters the invariant @0x570 (i=loop_count-1); round keys already in Q18-Q28 (NO KEY_EXPAND,
   unlike FILL).  m=loop_count-1, X1->word 0, last-group input split (blocks 4m..4m+3).  Lands
   s0@0x570, 97 asls, X1=word 0.  (Reuses the bodyleg setup_tac_dec structure: GHOST_INTRO + ENSURES_INIT + BETA
   + htable unfold + input-split.  No IVEC-split needed here yet -- add if the drain reads ivec lanes.) ---- *)
let INPUT_SPLIT_TAC_drain =
  INPUT_SPLIT_DEC (blk_from `4*(loop_count-1)`) 4 [`nblocks DIV 4 = loop_count`; `1 <= loop_count`];;
let drain_setup_tac =
  LEG_INIT_DEC ghost_lanes_dec THEN
  SUBGOAL_THEN `read X1 s0 = word 0` ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> if can (term_match [] `read X1 s0 = word (loop_count - ((loop_count-1)+1))`) (concl th)
      then MP_TAC th else NO_TAC) THEN
    SUBGOAL_THEN `loop_count - ((loop_count-1)+1) = 0` SUBST1_TAC THENL
     [UNDISCH_TAC `1 <= loop_count` THEN ARITH_TAC; DISCH_THEN(fun th -> REWRITE_TAC[th])]; ALL_TAC] THEN
  INPUT_SPLIT_TAC_drain THEN HTABLE_STRIP_DEC;;

(* ---- drain stepper: steps 1..83 (0x574..0x6bc; the b 0x6c0@0x6bc is step 83).  NO counter merges.
   Reuses REDSETX_DEC + the bodyleg per-step conv. ---- *)
let NSTEP_DRAIN = 83;;   (* 0x574..0x6bc (83 instrs incl b 0x6c0@0x6bc -> 0x6c0); the cbnz@0x570 is DRAINLEG's hop. *)
let drain_step_all =
  drain_setup_tac THEN
  DEC_STEPS_TAC REDSETX_DEC (K ALL_TAC) (1--NSTEP_DRAIN) THEN
  DEC_NORM_ASM_TAC;;

(* ---- DRAIN closer: the drain_bridge conjuncts
   are: aligned/PC (ASM), the carried regs (round keys/X-regs = ASM from invariant + stepping), the SETTLED Q30
   (THE CRUX -- last-group Horner reduce), the 3 output stores + output-frame.  Route most to CLOSE_DEC/ASM;
   route the Q30 + output-frame gaps to bespoke closers. ---- *)

(* --- drain-specific closers: pointer arithmetic, the X13 counter, the Q30 settle and the output frame. --- *)
(* Pointer arithmetic X0/X2 (loop_count-1+1 = loop_count, 64(lc-1)+64 = 64lc). *)
let DRAIN_PTR_TAC : tactic =
  AP_TERM_TAC THEN AP_TERM_TAC THEN UNDISCH_TAC `1 <= loop_count` THEN ARITH_TAC;;
(* X13 counter word_zx(word_add(word_zx(word_zx(word(4(lc-1)+2))))(word 4)) = word_zx(word(4lc+2)).
   The drain does add w13,#4 @0x57c; the base counter is nested word_zx(word_zx ..) (int32->int64->int32 round-trip).
   ZX_WT collapses the nesting, GSYM WORD_ADD merges the +4, then AP_TERM + ARITH. *)
let ZX_WT = prove(`word_zx(word_zx(w:int32):int64):int32 = w`, CONV_TAC WORD_BLAST);;
let DRAIN_X13_TAC : tactic =
  REWRITE_TAC[ZX_WT] THEN REWRITE_TAC[GSYM WORD_ADD] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN UNDISCH_TAC `1 <= loop_count` THEN ARITH_TAC;;
(* The Q30 settle.  Bridge the RHS 4(loop_count) -> 4((loop_count-1)+1) so SWP_Q30_SEED_TAC (bodyleg, which
   proves machine-reduce = half-swap(nist_ghash..4*(i+1)) with i:=loop_count-1) can close.  The dec Q30 is the
   split half-swap form; SWP_Q30_SEED_TAC handles it (SWP_SUBWORD_JOIN_MID + DEC_GHASH_NORM + SWP_Q30_SEED_FINISH).
   Adapt at i=loop_count-1: rewrite 4*loop_count -> 4*((loop_count-1)+1) on BOTH sides first. *)
(* NB: 4*loop_count = 4*((loop_count-1)+1) is only true for 1<=loop_count -- a bare ARITH_RULE is FALSE at
   loop_count=0 (truncated subtraction: 0-1+1=1); establish it from the 2<=loop_count hypothesis via SUBGOAL_THEN.
   THE Q30 SETTLE: the goal is machine-reduce (embedding half-swap(nist_ghash..4*(loop_count-1))) = half-swap
   (nist_ghash..4*loop_count).  SWP_Q30_SEED_TAC (bodyleg) proves this at a bare loop-index `i` (its internal
   ARITH_RULEs like 4*i+4=SUC^4(4*i) need `i` to be a VARIABLE), but here the index is the compound `loop_count-1`.
   FIX: ABBREV m = loop_count - 1 so the goal uses the bare `m` (LHS 4*(loop_count-1)->4*m, RHS via loop_count=m+1
   -> 4*(m+1)); then SWP_Q30_SEED_TAC fires with i:=m.  Mirrors enc drain_close_q30's m-indexing. *)
(* After the bridge + ABBREV m, SWP_Q30_SEED_TAC (SWP_SUBWORD_JOIN_MID +
   DEC_GHASH_NORM_TAC + ASM + GSYM nist_input_block + ASM + SWP_Q30_SEED_FINISH_TAC) reduces the machine reduce to
   byteswap128(nist_ghash..4*(m+1)) = word_join(subword..)(subword..), leaving both sides the split half-swap of
   nist_ghash..4*(m+1) -> REFL_TAC closes.  (term_match machwj_abs succeeds after DEC_GHASH_NORM.)  REQUIRES the
   drain_bridge Q30 conjunct's word_subword outputs be int64-pinned (else free type-vars block the final REFL). *)
let DRAIN_Q30_TAC : tactic =
  SUBGOAL_THEN `4 * loop_count = 4 * ((loop_count - 1) + 1)`
    (fun th -> GEN_REWRITE_TAC (RAND_CONV o TOP_DEPTH_CONV) [th]) THENL
   [UNDISCH_TAC `1 <= loop_count` THEN ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `m = loop_count - 1` THEN
  SWP_Q30_SEED_TAC THEN REFL_TAC;;
(* Output-frame forall j<4(loop_count).  Split into j<4(loop_count-1) (incoming) + the last-group blocks
   (4*(loop_count-1)+{0,1,2,3}); incoming via ASM forall, last-group blocks via OUT_STORE-reconstruct.  Delegate to
   the bodyleg OUT_FRAME_dec machinery with 4*loop_count = 4*((loop_count-1)+1). *)
let DRAIN_OUTFRAME_TAC : tactic =
  SUBGOAL_THEN `4 * loop_count = 4 * ((loop_count-1)+1)` (fun th -> GEN_REWRITE_TAC (ONCE_DEPTH_CONV) [th]) THENL
   [UNDISCH_TAC `1 <= loop_count` THEN ARITH_TAC; ALL_TAC] THEN
  (OUT_FRAME_dec ORELSE (ASM_REWRITE_TAC[] THEN CLOSE_DEC));;

let CLOSE_DRAIN : tactic = fun (asl,w) ->
  let has c t = can (find_term (fun u -> try fst(dest_const(fst(strip_comb u)))=c with _->false)) t in
  let hd t = try fst(dest_const(fst(strip_comb t))) with _->"" in
  let has_mc t = try can(find_term(fun x->match x with Const("MAYCHANGE",_)->true|_->false)) t with _->false in
  let deep_ghash = try has "nist_ghash" w with _ -> false in
  if has_mc w then close_frame_dec (asl,w)                              (* MAYCHANGE frame subsumption *)
  else if not(is_eq w) && not(is_forall w) then ASM_REWRITE_TAC[] (asl,w)   (* aligned_bytes_loaded / PC *)
  else if is_forall w then DRAIN_OUTFRAME_TAC (asl,w)
  else if hd(lhs w)="word_add" && (free_in `in_p:int64` w || free_in `out_p:int64` w) then DRAIN_PTR_TAC (asl,w)
  else if hd(lhs w)="word_zx" && free_in `loop_count:num` (lhs w) then DRAIN_X13_TAC (asl,w)
  else if deep_ghash then DRAIN_Q30_TAC (asl,w)
  (* staged counter slot 160 = rev8(ctr_block(4*(loop_count-1)+2)): carried unchanged from the invariant (drain
     never writes sp+160). ASM resolves read-over-84-nonwriting-steps to the s0 value; SP_SLOT_dec folds it. *)
  else if is_eq w && hd(lhs w)="read" && free_in `stackpointer:int64` (lhs w) && has "ctr_block" (rhs w) then
    (ASM_REWRITE_TAC[] THEN TRY (SP_SLOT_dec_fast ORELSE SP_SLOT_dec)) (asl,w)
  else (ASM_REWRITE_TAC[] THEN TRY CLOSE_DEC) (asl,w);;
let DRAIN_FROM_574 = GEN_ALL(prove(drain574_goal,
  drain_step_all THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN CLOSE_DRAIN));;

(* DRAINLEG: the cbnz@0x570 not taken (X1 = word 0 at index loop_count-1), then DRAIN_FROM_574. *)
let DRAINLEG = prove(drain_goal,
  STRIP_TAC THEN REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  ENSURES_SEQUENCE_TAC `pc + 0x574` (swp_inv_dec_at `loop_count - 1`) THEN CONJ_TAC THENL
   [hop_init_dec THEN
    SUBGOAL_THEN `loop_count - ((loop_count - 1) + 1) = 0`
      (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th]) THENL
     [UNDISCH_TAC `2 <= loop_count` THEN ARITH_TAC; ALL_TAC] THEN
    ARM_STEPS_TAC AES256_GCM_DEC_EXEC [1] THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
    REFOLD_ABI THEN MATCH_MP_TAC DRAIN_FROM_574 THEN ASM_REWRITE_TAC[] THEN
    TRY(UNDISCH_TAC `2 <= loop_count` THEN ARITH_TAC)]);;

(* ---- tail_inv i : the drain_bridge shape + loop index i (X0/X2 += 16*i, X13/X9/Q30 track i) + Q12/Q14 h-power
   pins (reloaded @0x6c0-0x6c8; the 1-block GHASH needs them).  Mirrors enc
   tail_inv @0xde0. ---- *)
let tail_inv = `\(i:num) s.
    read X0 s = word_add in_p (word (64 * loop_count + 16 * i)) /\
    read X2 s = word_add out_p (word (64 * loop_count + 16 * i)) /\
    read X3 s = tag_p /\ read X4 s = ivec_p /\ read X6 s = htable_p /\ read SP s = stackpointer /\
    read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
    read (memory :> bytes128 ivec_p) s = word_reversefields 8 (ctr_block nonce c) /\
    read Q18 s = word_reversefields 8 (EL 0 rk) /\ read Q19 s = word_reversefields 8 (EL 1 rk) /\
    read Q20 s = word_reversefields 8 (EL 2 rk) /\ read Q21 s = word_reversefields 8 (EL 3 rk) /\
    read Q22 s = word_reversefields 8 (EL 4 rk) /\ read Q23 s = word_reversefields 8 (EL 5 rk) /\
    read Q24 s = word_reversefields 8 (EL 6 rk) /\ read Q25 s = word_reversefields 8 (EL 7 rk) /\
    read Q26 s = word_reversefields 8 (EL 8 rk) /\ read Q27 s = word_reversefields 8 (EL 9 rk) /\
    read Q28 s = word_reversefields 8 (EL 10 rk) /\ read Q15 s = word_reversefields 8 (EL 11 rk) /\
    read Q16 s = word_reversefields 8 (EL 12 rk) /\ read Q17 s = word_reversefields 8 (EL 13 rk) /\
    read Q2 s = word_reversefields 8 (EL 14 rk) /\
    read Q7 s = word 13979173243358019584 /\
    read X13 s = word_zx (word (4 * loop_count + i + c):int32):int64 /\
    read X15 s = word(len_bits DIV 8) /\ read X9 s = word(loop_remain - i) /\
    read Q30 s = word_join
       ((word_subword (nist_ghash (aes256_cipher (word 0) rk) tag0
          (list_of_seq (nist_input_block inblock) (4 * loop_count + i))) (0,64)):int64)
       ((word_subword (nist_ghash (aes256_cipher (word 0) rk) tag0
          (list_of_seq (nist_input_block inblock) (4 * loop_count + i))) (64,64)):int64) /\
    htable_mem_4 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s /\
    read Q12 s = byteswap128 (h_power (ghash_twist (aes256_cipher (word 0) rk)) 0) /\
    read Q14 s = word_join
       (karatsuba_mid (h_power (ghash_twist (aes256_cipher (word 0) rk)) 1))
       (karatsuba_mid (h_power (ghash_twist (aes256_cipher (word 0) rk)) 0)) /\
    read (memory :> bytes64 (word_add stackpointer (word 160))) s =
       word_subword (word_reversefields 8 (ctr_block nonce c):int128) (0,64):int64 /\
    read (memory :> bytes32 (word_add stackpointer (word 168))) s =
       word_subword (word_reversefields 8 (ctr_block nonce c):int128) (64,32):int32 /\
    (!j. j < nblocks ==> read (memory :> bytes128 (word_add in_p (word(16*j)))) s = inblock j) /\
    (!j. j < 4 * loop_count + i ==> read (memory :> bytes128 (word_add out_p (word(16*j)))) s =
             word_xor (aes256_ctr_block c nonce rk j) (inblock j))`;;

(* ---- tail_post @ pc+0x7c4 (writeback done): tag = rev8(nist_ghash over all nblocks), counter word out at
   ivec_p+12, X0 = len_bits DIV 8, out-forall over ALL nblocks.  (At loop exit i=loop_remain,
   4*loop_count+loop_remain = nblocks.) ---- *)
let tail_post = mk_abs(`s:armstate`, list_mk_conj
 [`aligned_bytes_loaded s (word pc) aes256_gcm_dec_mc`;
  `read PC s = word (pc + 0x7c4)`;
  `read (memory :> bytes128 tag_p) s = word_reversefields 8
     (nist_ghash (aes256_cipher (word 0) rk) tag0
        (list_of_seq (nist_input_block inblock) nblocks))`;
  `read (memory :> bytes128 ivec_p) s =
     word_reversefields 8 (ctr_block nonce (nblocks + c))`;
  `read X0 s = word (len_bits DIV 8)`;
  `!j. j < nblocks ==> read (memory :> bytes128 (word_add out_p (word(16*j)))) s =
           word_xor (aes256_ctr_block c nonce rk j) (inblock j)`]);;

(* ---- tail_goal: drain_bridge @0x6c0 -> tail_post @0x7c4.  Takes drain_bridge AS the precond (= proven
   DRAINLEG post). ---- *)
let tail_hyps = mk_leg_hyps [] [`len_bits < 2 EXP 64`] [];;
let tail_frame = `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
      MAYCHANGE [X19; X20; X21; X22; X23; X24; X25; X26; X27; X28; X29; X30] ,,
      MAYCHANGE [Q0; Q1; Q2; Q3; Q4; Q5; Q6; Q7; Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15; Q16; Q17; Q29; Q30; Q31] ,,
      MAYCHANGE [memory :> bytes(out_p:int64, 16 * nblocks)] ,,
      MAYCHANGE [memory :> bytes(tag_p:int64,16)] ,, MAYCHANGE [memory :> bytes(ivec_p:int64,16)] ,,
      MAYCHANGE [memory :> bytes(word_add stackpointer (word 160):int64, 64)] ,, MAYCHANGE [events]`;;
let tail_goal = mk_leg_goal tail_hyps drain_bridge tail_post tail_frame;;

(* ---- tail_tac: ASM_CASES loop_remain=0 -> [degenerate | WHILE]. ----
   DEGENERATE (loop_remain=0): SUBST loop_remain=0; nblocks=4*loop_count; ENSURES_INIT; htable unfold; step 1..3
     (htable reloads 0x6c0-0x6c8); step 4 (cbz x9@0x6cc, x9=word 0 TAKEN -> 0x7b0); step 5..9 (writeback
     mov/rev64/str q30/rev/str w14 -> 0x7c4); ENSURES_FINAL; per-conjunct: tag (ABBREV gv + nblocks->4*loop_count
     + WORD_BLAST), counter (nblocks->4*loop_count + WORD_BLAST), out-frame (nblocks->4*loop_count + ASM),
     frame (close_frame_dec).
   WHILE (loop_remain>0): REWRITE[ABI] THEN ENSURES_WHILE_UP_TAC `loop_remain` `pc+0x6d0` `pc+0x7ac` tail_inv THEN
     REPEAT CONJ_TAC -> 5 obligations:
     g0 ~(loop_remain=0): ASM_REWRITE.
     g1 BASE (drain_bridge->tail_inv 0): ENSURES_INIT; htable unfold; step 1..3 (reloads); val(word loop_remain)=
        loop_remain (from lr<4); step 4 (cbz NOT taken -> 0x6d0); ENSURES_FINAL; ASM_REWRITE[ADD_CLAUSES;
        MULT_CLAUSES; SUB_0; htable_mem_4] (i=0 norms: 16*0=0, +0, -0, 4lc+0=4lc).
     g2 STEP (tail_inv i -> tail_inv(i+1)): X_GEN_TAC i; STRIP; VAL_INT64_TAC i; ENSURES_INIT; htable unfold;
        pin the input block read(in_p+64*loop_count+16*i) = inblock(4*loop_count+i) (64a+16b=16(4a+b)); step the
        56-instr 1-block body (0x6d0..0x7a8): counter merge MERGE_CTR128 160 @ step ~6; str q30@step53 out-store;
        the 1-block GHASH Q30 update half-swap(nist_ghash..(4lc+i)) + block -> half-swap(nist_ghash..(4lc+i+1))
        via NIST_GHASH single-CONS append + the machine pmull reduce (Q12/Q14 pins).
     g3 back-edge: cbnz x9@0x7ac, x9=word(loop_remain-(i+1)) != 0 for i+1<loop_remain -> back to 0x6d0.
     g4 EXIT (tail_inv loop_remain -> tail_post): the writeback postamble 0x7b0..0x7c4 (mov/rev64/str q30/rev/str
        w14) at i=loop_remain (4*loop_count+loop_remain=nblocks); SAME closers as the DEGENERATE case.
   Model: the enc-256 SWP tail_tac.  dec: aes256, half-swap Q30, INPUT GHASH (nist_input_block),
   counter str to [x4,#12].
   THE STEP Q30 update (g2 core): the 1-block GHASH.  half-swap(nist_ghash..(4lc+i)) XOR inblock(4lc+i) folded by
   one pmull-reduce (h_power 0 via Q12, karatsuba-mid via Q14) = half-swap(nist_ghash..(4lc+i+1)).  Algebraically
   NIST_GHASH_APPEND / a single ghash_polyval_acc step; adapt bodyleg GHASH-partial closers to the single-block case.
   ============================================================================ *)

(* ============================================================================
   tail_goal + tail_tac.  Degenerate (loop_remain=0) + WHILE dispatch; the Q30 1-block reduce is ported
   from the enc tail_ghash_close (dec-adapted).
   ============================================================================ *)

let woff_t n = mk_comb(mk_comb(`word_add:int64->int64->int64`,`stackpointer:int64`),mk_comb(`word:num->int64`,mk_small_numeral n));;

(* BASE nonce-lane derivation: drain_bridge carries the FULL bytes128 sp+160 block (= rev8(ctr_block(4*(lc-1)+2)));
   tail_inv 0 wants the two counter-INDEPENDENT nonce sub-lanes (bytes64@+0 -> subword(rev8(ctr_block 2))(0,64),
   bytes32@+8 -> subword(..)(64,32)).  Derive them at s0 via B64_OF_B128_LO / B32_OF_B128_MID (lane = subword of
   enclosing block) + SUBW_LO_CI / SUBW_MID_CI (nonce lanes are counter-independent -> canonicalize ctr to 2), then
   STRIP_ASSUME so they survive the 4 non-storing setup steps (ldr q12/q13/q14, cbz) into s4. *)
let TAIL_BASE_LANES : tactic =
  SUBGOAL_THEN
   `read (memory :> bytes64 (word_add stackpointer (word 160))) s0 =
      word_subword (word_reversefields 8 (ctr_block nonce c):int128) (0,64):int64 /\
    read (memory :> bytes32 (word_add stackpointer (word 168))) s0 =
      word_subword (word_reversefields 8 (ctr_block nonce c):int128) (64,32):int32`
   STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[B64_OF_B128_LO] THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBW_LO_CI] THEN CONV_TAC WORD_BLAST;
      REWRITE_TAC[WORD_RULE `word_add stackpointer (word 168):int64 =
                             word_add (word_add stackpointer (word 160)) (word 8)`] THEN
      REWRITE_TAC[B32_OF_B128_MID] THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBW_MID_CI] THEN CONV_TAC WORD_BLAST];
    ALL_TAC];;

(* tail counter merge @ sK: fold read(bytes128 sp+160)sK = rev8(ctr_block(4*loop_count+i+2)) from the nonce lanes
   (bytes64@+0, bytes32@+8) carried in tail_inv + the fresh +12 counter word. *)
let TAIL_CTR_MERGE sK : tactic =
  let sp128 = CONV_RULE(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)(ISPECL [`memory`; woff_t 160; mk_var(sK,`:armstate`)] splitL) in
  let sp64  = CONV_RULE(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)(ISPECL [`memory`; woff_t 168; mk_var(sK,`:armstate`)] splitL2) in
  SUBGOAL_THEN (subst [mk_var(sK,`:armstate`),`s:armstate`]
     `read (memory :> bytes128 (word_add stackpointer (word 160))) s =
      word_reversefields 8 (ctr_block nonce (4 * loop_count + i + c))`) ASSUME_TAC THENL
   [GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [sp128; sp64] THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[ctr_block] THEN
    (CONV_TAC WORD_BLAST ORELSE CONV_TAC WORD_RULE ORELSE (REPEAT AP_TERM_TAC THEN ARITH_TAC)); ALL_TAC];;

(* PLAIN stepper (no gkeepN pruning) for the tail.  The 1-block loop does NOT re-read htable, and gkeepN prunes the
   GHASH karatsuba-mid intermediates Q4/Q7/Q10 -> Q30's value dangles `read Q7 s34` unclosable.  Plain ARM_STEPS
   substitutes them fully into Q30.  Also FASTER here (17s vs 155s) -- gkeepN's per-step pruning over 55 steps is
   costly and the 1-block asl is small enough to not need it. *)

(* STRIP the 6-way htable_mem_4 conjunction (after RULE_ASSUM REWRITE[htable_mem_4]) into 6 individual reads so
   ARM_STEP advances each to the final state (else they stay folded at s0 and the htable_mem_4 conjunct can't close).
   Mirrors DRAIN's setup.  Requires the tail_hyps `nonoverlapping (htable_p,96)(sp+160,64)` so the reads cross the
   counter store.  *)

(* --- STEP closers --- *)
let TAIL_X9_CLOSE : tactic =    (* word_sub(word(loop_remain-i))(word 1) = word(loop_remain-(i+1)) *)
  SUBGOAL_THEN `word_sub (word (loop_remain - i)) (word 1):int64 = word ((loop_remain - i) - 1)`
    (fun th -> REWRITE_TAC[th]) THENL
   [GEN_REWRITE_TAC RAND_CONV [WORD_SUB] THEN COND_CASES_TAC THENL
     [REFL_TAC;
      FIRST_X_ASSUM MP_TAC THEN REWRITE_TAC[VAL_WORD_1] THEN UNDISCH_TAC `i < loop_remain` THEN ARITH_TAC];
    AP_TERM_TAC THEN UNDISCH_TAC `i < loop_remain` THEN ARITH_TAC];;

(* Single-block GHASH-accumulate lemma (proven via GHASH_POLYVAL_ACC_BATCHED with the empty extra-list): the
   1-block analogue of SWP_GHASH_BRANCH2_256.  Use it to fold the settled 1-block reduce prop3(pmul(acc XOR blk)(h0))
   to nist_ghash..(m+1) once the machine tower is reconstructed. *)
let SWP_GHASH_BRANCH2_1BLK = prove
 (`polyval_reduce_prop3
     (word_pmul (word_xor (nist_ghash (aes256_cipher (word 0) rk) tag0
                              (list_of_seq (nist_input_block inblock) m))
                          (nist_input_block inblock m))
                (h_power (ghash_twist (aes256_cipher (word 0) rk)) 0))
   = nist_ghash (aes256_cipher (word 0) rk) tag0
       (list_of_seq (nist_input_block inblock) (m+1))`,
  MP_TAC(ISPECL [`ghash_twist (aes256_cipher (word 0) rk)`; `[]:(int128)list`;
                 `nist_ghash (aes256_cipher (word 0) rk) tag0 (list_of_seq (nist_input_block inblock) m):int128`;
                 `nist_input_block inblock m:int128`] GHASH_POLYVAL_ACC_BATCHED) THEN
  REWRITE_TAC[LENGTH; ghash_wide] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[NIST_GHASH_IS_POLYVAL] THEN
  REWRITE_TAC[ARITH_RULE `m + 1 = SUC m`] THEN
  REWRITE_TAC[list_of_seq] THEN REWRITE_TAC[GSYM APPEND_ASSOC; APPEND] THEN
  REWRITE_TAC[GHASH_ACC_APPEND] THEN
  REWRITE_TAC[ADD1; GSYM ADD_ASSOC] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[GSYM NIST_GHASH_IS_POLYVAL] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN AP_TERM_TAC THEN CONV_TAC WORD_BITWISE_RULE);;

(* Q30 1-block GHASH update.  half-swap(nist_ghash..(4lc+i)) XOR block(4lc+i) --one pmull reduce-->
   half-swap(nist_ghash..(4lc+i+1)).  Ported from the PROVEN enc-256 tail_ghash_close (identical machine tower;
   enc/dec differ only in the block: dec GHASHes the INPUT via nist_input_block).
   Structure (all algebraic, ~2.4s):
     byteswap128 + (64,128)-subword-join collapse -> MATCH_MP_TAC(join(sub x)=join(sub y) from x=y)
     -> ABBREV sofar/cipherblock/h/k -> TRANS through polyval_reduce_prop3(word_pmul(xor sofar cb) h):
       branch 1 (machine karatsuba tower = prop3(pmul..)):  PMUL_KARATSUBA_JOIN_ALT + byteswap + subword-conv
         + karatsuba_mid + INBLOCK_REASSEMBLE + GSYM nist_input_block (folds the byte tower to cipherblock)
         + POLYVAL_REDUCE_G2 + prop3-unfold + ABBREV w1 (=pmul(sub p1 0)(polyconst)) + EXPAND ks + WORD_SUBWORD_XOR
         + AC-unify the two reduce-pmul args (WORD_BITWISE_RULE on their args) + ABBREV w2 + drop asms + BITBLAST
         (only 5 free vars w1,w2,p1,p2,p3 -> 641 bool vars, tractable; blasting the raw pmul tower is NOT);
       branch 2 (prop3(pmul(xor sofar cb) h) = nist_ghash(i+1)):  EXPAND + SWP_GHASH_BRANCH2_1BLK. *)
let TAIL_Q30_CLOSE : tactic =
  REWRITE_TAC [byteswap128; WORD_BLAST
   `word_subword((word_join:int128->int128->int256) h l) (64,128):int128 =
    word_join (word_subword h (0,64):int64) (word_subword l (64,64):int64)`] THEN
  MATCH_MP_TAC(BITBLAST_RULE
   `x:int128 = y ==> word_join (word_subword x (0,64):int64) (word_subword x (64,64):int64):int128 =
        word_join (word_subword y (0,64):int64) (word_subword y (64,64):int64):int128`) THEN
  MAP_EVERY ABBREV_TAC
   [`sofar = (nist_ghash (aes256_cipher (word 0) rk) tag0
               (list_of_seq (nist_input_block inblock) (4 * loop_count + i)))`;
    `cipherblock = nist_input_block inblock (4 * loop_count + i)`;
    `h = h_power (ghash_twist (aes256_cipher (word 0) rk)) 0`;
    `k = karatsuba_mid h`] THEN
  TRANS_TAC EQ_TRANS `polyval_reduce_prop3 (word_pmul (word_xor sofar cipherblock:int128) (h:int128))` THEN
  CONJ_TAC THENL
   [(* branch 1: machine karatsuba tower = prop3(pmul(xor sofar cb) h) *)
    REWRITE_TAC[PMUL_KARATSUBA_JOIN_ALT] THEN
    REWRITE_TAC[byteswap128; WORD_SUBWORD_XOR] THEN
    CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
    ASM_REWRITE_TAC[] THEN LET_TAC THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "k" THEN REWRITE_TAC[karatsuba_mid] THEN
    ASM_REWRITE_TAC[] THEN REPEAT LET_TAC THEN
    REWRITE_TAC[INBLOCK_REASSEMBLE] THEN REWRITE_TAC[GSYM nist_input_block] THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[POLYVAL_REDUCE_G2] THEN
    ABBREV_TAC
     `w1 = (word_pmul:int64->int64->int128)
        (word_subword (p1:int128) (0,64)) (word 13979173243358019584)` THEN
    REWRITE_TAC[polyval_reduce_prop3] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
    ASM_REWRITE_TAC[] THEN
    (* ks was reintroduced by ASM_REWRITE (asm word_xor(xor p1 p2)p3 = ks); expand back + distribute *)
    (TRY(EXPAND_TAC "ks")) THEN REWRITE_TAC[WORD_SUBWORD_XOR] THEN
    (* AC-unify the two reduce-pmul args (they are XOR-rearrangements of the same 5 leaves) *)
    (fun (asl,w) ->
      let redp = filter (fun u->match u with
                   Comb(Comb(Const("word_pmul",_),_),Comb(Const("word",_),n)) when n=`13979173243358019584`->true|_->false)
                   (setify(find_terms (fun u->match u with Comb(Comb(Const("word_pmul",_),_),_)->true|_->false) w)) in
      match redp with
       [pm0; pm1] ->
         let getarg t = hd(snd(strip_comb t)) in
         (REWRITE_TAC[WORD_BITWISE_RULE(mk_eq(getarg pm1, getarg pm0))] ORELSE ALL_TAC) (asl,w)
      | _ -> ALL_TAC (asl,w)) THEN
    (* abstract the single remaining reduce-pmul to w2, drop the definitional asms, and bit-blast *)
    (fun (asl,w) ->
      let redp = setify(filter (fun u->match u with
                   Comb(Comb(Const("word_pmul",_),_),Comb(Const("word",_),n)) when n=`13979173243358019584`->true|_->false)
                   (find_terms (fun u->match u with Comb(Comb(Const("word_pmul",_),_),_)->true|_->false) w)) in
      match redp with
       [pm] -> ABBREV_TAC (mk_eq(mk_var("w2",type_of pm), pm)) (asl,w)
      | _ -> ALL_TAC (asl,w)) THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN CONV_TAC BITBLAST_RULE;
    (* branch 2: prop3(pmul(xor sofar cb) h) = nist_ghash(i+1) *)
    MAP_EVERY EXPAND_TAC ["sofar"; "cipherblock"; "h"] THEN
    REWRITE_TAC[ARITH_RULE `4 * loop_count + i + 1 = (4 * loop_count + i) + 1`] THEN
    MATCH_ACCEPT_TAC SWP_GHASH_BRANCH2_1BLK];;

(* Tail 1-block out-store keystream fold: FULL AES-256 tower on the resident rev8(ctr_block(4lc+i+2)) (merged @s5).
   XOR_AES256_CIPHER_RECONSTRUCT_DEC folds the machine tower -> rev8(aes256_cipher(ctr_block..)) = aes256_ctr_block. *)
let TAIL_OUT_BLOCK : tactic =
  REWRITE_TAC[ADD_CLAUSES] THEN
  REWRITE_TAC[XOR_AES256_CIPHER_RECONSTRUCT_DEC] THEN
  REWRITE_TAC[WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
  REWRITE_TAC[MAP; WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[aes256_ctr_block] THEN
  REWRITE_TAC[ARITH_RULE `(4 * loop_count + i) + c = 4 * loop_count + i + c`] THEN
  REFL_TAC;;

(* Tail out-frame extension (1 new block): j<4lc+i+1 <=> j<4lc+i \/ j=4lc+i.  Old sub-frame = incoming invariant
   (ASM-accept the forall); new block j=4lc+i -> the stored decrypted block (TAIL_OUT_BLOCK). *)
let TAIL_OUT_FRAME : tactic =
  REWRITE_TAC[ARITH_RULE `j < 4 * loop_count + i + 1 <=>
                          j < 4 * loop_count + i \/ j = 4 * loop_count + i`] THEN
  ASM_REWRITE_TAC[TAUT `p \/ q ==> r <=> (p ==> r) /\ (q ==> r)`] THEN
  REWRITE_TAC[FORALL_AND_THM; FORALL_UNWIND_THM2] THEN
  REWRITE_TAC[ARITH_RULE `16 * (4 * loop_count + i) = 64 * loop_count + 16 * i`] THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  TRY (FIRST_X_ASSUM (fun th -> if (try is_forall(concl th) && free_in `out_p:int64` (concl th) with _->false)
                                then MATCH_ACCEPT_TAC th else NO_TAC)) THEN
  TRY (ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  ASM_REWRITE_TAC[] THEN TAIL_OUT_BLOCK;;

(* Per-conjunct STEP router (post ENSURES_FINAL + ASM_REWRITE).  gkeepN resolves Q30 to the machine value, so the
   Q30 conjunct's RHS holds nist_ghash..(4lc+i+1) (target) and its LHS is the settled machine reduce -> route by
   `nist_ghash` to TAIL_Q30_CLOSE.  NB TAIL_Q30_CLOSE is NOT in the FIRST[] fallback (it partially applies + leaves
   the reduce subgoal on non-Q30 conjuncts). *)
let TAIL_STEP_CLOSE : tactic = fun (asl,w) ->
  let has c t = can (find_term (fun u -> try fst(dest_const(fst(strip_comb u)))=c with _->false)) t in
  if is_forall w && free_in `out_p:int64` w then TAIL_OUT_FRAME (asl,w)
  else if is_forall w && free_in `in_p:int64` w then ASM_REWRITE_TAC[] (asl,w)
  else if has "htable_mem_4" w then ASM_REWRITE_TAC[htable_mem_4] (asl,w)
  else if is_eq w && has "nist_ghash" w then TAIL_Q30_CLOSE (asl,w)  (* Q30 settled machine reduce *)
  else FIRST
    [ (AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC);                        (* X0/X2 ptr *)
      (REWRITE_TAC[ZX_WT] THEN REWRITE_TAC[GSYM WORD_ADD] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC);  (* X13 *)
      TAIL_X9_CLOSE;                                                        (* X9 *)
      close_frame_dec;                                                      (* MAYCHANGE *)
      (ASM_REWRITE_TAC[htable_mem_4]) ] (asl,w);;

(* ---- ivec-canonical support: produce the FULL bytes128 ivec post (not bytes32(ivec+12)).
   IVEC_SPLIT_TAIL: after ENSURES_INIT, split the drain_bridge ivec read `bytes128 ivec = wrf(ctr_block nonce c)`
   into 4-byte cells (READ_MEMORY_SPLIT_CONV 2, recursive) so the 3 low nonce cells (ivec+0/+4/+8) survive the
   counter writeback (str w14,[x4,#12] touches ONLY ivec+12).  Mirrors the AES-128 decrypt proof.
   IVEC_RECOMB_TAIL: at the final state, split the GOAL ivec the same way + rewrite the 3 nonce cells from the
   surviving split-precond cells + the +12 counter cell (already in asm) + ctr_block + WORD_BLAST.  ctr_block
   nonce k shares the low 96 bits for all k, so nonce cells of ..(nblocks+2) match those of ..2. ---- *)
let IVEC_SPLIT_TAIL : tactic =
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o CONV_RULE(READ_MEMORY_SPLIT_CONV 2) o
    check (fun th -> let c = concl th in
      is_eq c && free_in `ivec_p:int64` (lhs c) &&
      not(free_in `out_p:int64` (lhs c)) && not(free_in `in_p:int64` (lhs c)) &&
      not(free_in `htable_p:int64` (lhs c)) && not(free_in `tag_p:int64` (lhs c)) &&
      not(free_in `key_p:int64` (lhs c)) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "bytes128")) (lhs c)));;
(* per-cell rewrites: the 3 nonce cells of ctr_block nonce (nblocks+c) equal those of ctr_block nonce c
   (k-independence -- low 96 bits are the nonce), and the counter cell (bits 96-127) = word_bytereverse(word(nblocks+2)).
   Each proven by REWRITE[ctr_block] + WORD_BLAST (symbolic nblocks OK -- ctr_block nonce K = word_join nonce (word K),
   nonce cells drop K, counter cell keeps word K under bytereverse). *)
(* word_zx on the SAME width is the identity -- collapses the machine counter zx-tower (all int32 layers). *)
let WORD_ZX_ID32 = prove(`!x:int32. word_zx x:int32 = x`, GEN_TAC THEN CONV_TAC WORD_BLAST);;
(* the machine counter cell zx-tower (4 int32 zx's around word_bytereverse) = word_bytereverse of the inner word. *)
let ZXTOWER_COLLAPSE_32 = prove
 (`word_zx (word_zx (word_bytereverse (word_zx (word_zx (c:int32):int32):int32):int32):int32):int32 =
   word_bytereverse c`, CONV_TAC WORD_BLAST);;
(* IVEC_RECON: the bytes128 ivec reconstruction (counter word ++ preserved low-96 nonce).  ONE-shot use only
   (its RHS has ctr_block nonce c, self-matching -> a plain REWRITE loops -> stack overflow). *)
let IVEC_RECON = prove
 (`word_reversefields 8 (ctr_block nonce k):int128 =
   word_join (word_bytereverse (word (k):int32))
             (word_subword (word_reversefields 8 (ctr_block nonce c):int128) (0,96):(96)word)`,
  REWRITE_TAC[ctr_block] THEN CONV_TAC WORD_BLAST);;
(* IVEC_RECOMB_TAIL: rewrite goal RHS wrf(ctr_block(K)) via IVEC_RECON (one-shot), split
   goal + asm cells, collapse the counter zx-tower SURGICALLY (only the bytes32-ivec asms -- NOT a blanket
   RULE_ASSUM which recurses into the Q30 tower -> overflow), ASM_REWRITE, then fold the symbolic counter index
   K -> nblocks+2 (AP_TERM_TAC + ASM_ARITH, assoc-robust: 4lc+lr+2 parses right-assoc so plain SUBST misses it),
   per-cell WORD_BLAST. *)
(* kidx = the ivec counter index in the GOAL (from tail_post ivec = wrf(ctr_block nonce kidx)): nblocks+2 for g4,
   4*loop_count+2 for degen.  All symbolic counter words in the split cells get folded to `word kidx` via ASM_ARITH. *)
let IVEC_RECOMB_TAIL (kidx:term) : tactic =
  TRY(GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [IVEC_RECON]) THEN
  CONV_TAC(ONCE_DEPTH_CONV(fun t ->
      if is_eq t && free_in `ivec_p:int64` (lhs t) &&
         not(free_in `out_p:int64` (lhs t)) && not(free_in `tag_p:int64` (lhs t))
      then READ_MEMORY_SPLIT_CONV 2 t else failwith "")) THEN
  CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
  W(fun (asl,w) ->
     let ivec_cells = filter (fun (_,th) -> let c = concl th in
        try is_eq c && free_in `ivec_p:int64` (lhs c) &&
            can (find_term (fun t -> is_const t && fst(dest_const t)="bytes32")) (lhs c)
        with _ -> false) asl in
     let normed = map (fun (_,th) -> REWRITE_RULE
        [ZXTOWER_COLLAPSE_32; WORD_ZX_ID32; ZX_WT; ADD_CLAUSES; MULT_CLAUSES] th) ivec_cells in
     REWRITE_TAC normed) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ctr_block] THEN
  W(fun (asl,w) ->
     let ktm = mk_comb(`word:num->int32`,kidx) in
     let idxs = setify(find_terms (fun t -> match t with
        Comb(Const("word",_),e) when (try type_of t = `:int32` with _->false) && not(is_numeral e) && not(t = ktm) && not(e = `c:num`) -> true | _ -> false) w) in
     EVERY (map (fun t ->
        SUBGOAL_THEN (mk_eq(t, ktm)) (fun th -> REWRITE_TAC[th]) THENL
         [AP_TERM_TAC THEN ASM_ARITH_TAC; ALL_TAC]) idxs)) THEN
  REPEAT CONJ_TAC THEN CONV_TAC WORD_BLAST;;

(* ---- writeback per-conjunct dispatcher (shape-routed): ivec bytes128 -> IVEC_RECOMB_TAIL; tag (nist_ghash RHS)
   -> ABBREV gv + WORD_BLAST; MAYCHANGE -> close_frame_dec; else ASM_REWRITE.  SHAPE-ROUTED so WORD_BLAST never
   hits the wrong (huge) conjunct.  `mgv` = the settled-GHASH index (4*loop_count for degen, nblocks for g4). ---- *)
let TAIL_WB_CLOSE (mgv:term) : tactic = fun (asl,w) ->
  let has c t = can (find_term (fun u -> try fst(dest_const(fst(strip_comb u)))=c with _->false)) t in
  if not(is_eq w) then
    (if has "MAYCHANGE" w then close_frame_dec (asl,w)
     else if is_forall w then ASM_REWRITE_TAC[] (asl,w)
     else ASM_REWRITE_TAC[] (asl,w))
  else if free_in `ivec_p:int64` (lhs w) && has "bytes128" (lhs w) then
    IVEC_RECOMB_TAIL (mk_binary "+" (mgv, `c:num`)) (asl,w)
  else if has "nist_ghash" (rhs w) then
    (* resolve the tag read to its machine byteswap tower (ASM_REWRITE) FIRST, then ABBREV the settled GHASH gv
       and WORD_BLAST the byteswap reassembly.  (WORD_BLAST can't prove an unresolved `read(...) = ...`.) *)
    (ASM_REWRITE_TAC[] THEN
     ABBREV_TAC(mk_eq(`gv:int128`,
        list_mk_comb(`nist_ghash:int128->int128->(int128)list->int128`,
          [`aes256_cipher (word 0) rk:int128`; `tag0:int128`;
           mk_comb(`list_of_seq (nist_input_block inblock):num->(int128)list`, mgv)]))) THEN
     CONV_TAC WORD_BLAST) (asl,w)
  else (ASM_REWRITE_TAC[] ORELSE CONV_TAC WORD_BLAST) (asl,w);;

(* ---- tail_tac: degenerate(loop_remain=0) | WHILE(loop_remain>0). ---- *)
let TAIL_DEGEN : tactic =
  POP_ASSUM SUBST_ALL_TAC THEN ENSURES_INIT_TAC "s0" THEN IVEC_SPLIT_TAIL THEN
  RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_4]) THEN
  SUBGOAL_THEN `nblocks = 4 * loop_count` SUBST_ALL_TAC THENL
   [MAP_EVERY(fun t->TRY(UNDISCH_TAC t)) [`nblocks DIV 4 = loop_count`; `nblocks MOD 4 = 0`] THEN ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY (DEC_STEP_TAC REDSETX_DEC) (1--9) THEN ENSURES_FINAL_STATE_TAC THEN
  REPEAT CONJ_TAC THEN TAIL_WB_CLOSE `4 * loop_count`;;

let tail_tac : tactic =
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[fst AES256_GCM_DEC_EXEC] THEN
  ASM_CASES_TAC `loop_remain = 0` THENL
   [TAIL_DEGEN;
    REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    ENSURES_WHILE_UP_TAC `loop_remain:num` `pc + 0x6d0` `pc + 0x7ac` tail_inv THEN
    REPEAT CONJ_TAC THENL
     [(* g0 *) ASM_REWRITE_TAC[];
      (* g1 BASE: drain_bridge -> tail_inv 0 *)
      ENSURES_INIT_TAC "s0" THEN RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_4]) THEN
      TAIL_BASE_LANES THEN
      MAP_EVERY (DEC_STEP_TAC REDSETX_DEC) (1--3) THEN
      SUBGOAL_THEN `val(word loop_remain:int64) = loop_remain` ASSUME_TAC THENL
       [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
        MAP_EVERY(fun t->TRY(UNDISCH_TAC t)) [`nblocks MOD 4 = loop_remain`; `16 * nblocks < 2 EXP 64`] THEN ARITH_TAC; ALL_TAC] THEN
      DEC_STEP_TAC REDSETX_DEC 4 THEN ENSURES_FINAL_STATE_TAC THEN
      ASM_REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES; SUB_0; htable_mem_4];
      (* g2 STEP: tail_inv i -> tail_inv(i+1).  gkeepN stepping (DEC_STEP_TAC) -- keeps Q30 (the loop-carried GHASH acc)
         resolved to its machine value at s55; PLAIN ARM_STEPS drops the dead ext-v30 write.  htable individual reads
         are kept by gkeepN's anchored clause + advanced across the counter store by the sp-nonoverlaps in tail_hyps.
         Counter merge @s5 (post counter-store, matching the keystream's ldr q5,[sp,#160] read). *)
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
      ENSURES_INIT_TAC "s0" THEN RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_4]) THEN
      SUBGOAL_THEN `read (memory :> bytes128 (word_add in_p (word (64 * loop_count + 16 * i)))) s0 = inblock (4 * loop_count + i)`
      ASSUME_TAC THENL
       [REWRITE_TAC[ARITH_RULE `64 * a + 16 * b = 16 * (4 * a + b)`] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        MAP_EVERY(fun t->TRY(UNDISCH_TAC t)) [`nblocks DIV 4 = loop_count`; `nblocks MOD 4 = loop_remain`; `i < loop_remain`] THEN ARITH_TAC; ALL_TAC] THEN
      MAP_EVERY (DEC_STEP_TAC REDSETX_DEC) (1--5) THEN TAIL_CTR_MERGE "s5" THEN MAP_EVERY (DEC_STEP_TAC REDSETX_DEC) (6--55) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      REPEAT CONJ_TAC THEN TAIL_STEP_CLOSE;
      (* g3 back-edge: cbnz x9@0x7ac (1 instr), x9=word(loop_remain-(i+1)) != 0 for i+1<loop_remain -> 0x6d0. *)
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
      ENSURES_INIT_TAC "s0" THEN RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_4]) THEN REWRITE_TAC[htable_mem_4] THEN
      ARM_STEPS_TAC AES256_GCM_DEC_EXEC [1] THEN ENSURES_FINAL_STATE_TAC THEN
      ASM_SIMP_TAC[WORD_SUB; LT_IMP_LE; VAL_EQ_0; WORD_SUB_EQ_0] THEN ASM_REWRITE_TAC[GSYM VAL_EQ] THEN
      SUBGOAL_THEN `val(word loop_remain:int64) = loop_remain` ASSUME_TAC THENL
       [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
        MAP_EVERY (fun t -> TRY(UNDISCH_TAC t)) [`nblocks MOD 4 = loop_remain`; `16 * nblocks < 2 EXP 64`] THEN ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[ARITH_RULE `i < loop_remain ==> ~(loop_remain = i)`];
      (* g4 EXIT: tail_inv loop_remain @0x7ac (cbnz not taken) -> tail_post @0x7c4 (writeback: mov/rev64/str-tag/
         rev/str-ctr = 5 instrs after cbnz, step 1--6).  tag via WORD_BLAST; ivec recompose (IVEC_RECOMB_TAIL);
         out-frame = the invariant's s6 out-forall (4lc+lr=nblocks).  Split ivec at init so nonce cells survive. *)
      ENSURES_INIT_TAC "s0" THEN IVEC_SPLIT_TAIL THEN RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_4]) THEN
      SUBGOAL_THEN `4 * loop_count + loop_remain = nblocks` ASSUME_TAC THENL
       [MAP_EVERY(fun t->TRY(UNDISCH_TAC t)) [`nblocks DIV 4 = loop_count`; `nblocks MOD 4 = loop_remain`] THEN ARITH_TAC; ALL_TAC] THEN
      (* gkeepN stepping (prunes the Q30 tower); split ivec cells carried as memory reads. *)
      MAP_EVERY (DEC_STEP_TAC REDSETX_DEC) (1--6) THEN ENSURES_FINAL_STATE_TAC THEN
      REPEAT CONJ_TAC THEN
      (* out-forall (j<nblocks): accept the invariant's s6 out-forall (4lc+lr=nblocks). *)
      TRY (FIRST_X_ASSUM(fun th -> if (try is_forall(concl th) && free_in `out_p:int64` (concl th) &&
             contains "s6" (string_of_term(concl th)) with _->false) then MP_TAC th else NO_TAC) THEN
           ASM_REWRITE_TAC[] THEN NO_TAC) THEN
      TAIL_WB_CLOSE `nblocks:num`]];;

let TAILLEG = prove(tail_goal, tail_tac);;

(* ============================================================================ *)
(* P4: whole-function composition (MAINLEG + CORE_FROM88) + AES256_GCM_DEC_CORRECT +  *)
(* P5 SUBROUTINE wrapper.  Follows the enc-256 SWP sibling proof's               *)
(* composition and wrapper, with the LEG_LC0 degenerate leg.                    *)
(* Legs in scope: FILLLEG, BODYLEG, DRAINLEG,          *)
(* TAILLEG (= TAIL_NO2, canonical bytes128 ivec, no 2<=loop_count).       *)
(* ============================================================================ *)

(* ---- (b) frame-widening infra ---- *)
let broad_frame =
  let _,ens = dest_imp drain_goal in last(snd(strip_comb ens));;
let widen_frame_to_broad th =
  let narrow = rand(concl th) in
  let subth = prove(list_mk_icomb "subsumed" [narrow; broad_frame],
     REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN SUBSUMED_MAYCHANGE_TAC) in
  MATCH_MP ENSURES_FRAME_SUBSUMED (CONJ subth th);;
let widen_leg leg =
  let vars,_ = strip_forall (concl leg) in
  let leg0 = SPEC_ALL leg in
  let pre = lhand(concl leg0) in
  let broad = DISCH pre (widen_frame_to_broad (UNDISCH leg0)) in
  GENL (if vars = [] then frees(concl broad) else vars) broad;;

let FILLLEG_BROAD = widen_leg FILLLEG;;
let DRAINLEG_BROAD = widen_leg DRAINLEG;;
let BODYLEG_BROAD = widen_leg BODYLEG;;
let fill_pre_state = el 1 (snd(strip_comb(snd(dest_imp fill_goal))));;
let while_inv = mk_gabs(`k:num`, mk_comb(swp_inv, `k:num`));;

let gen_precond = list_mk_conj (filter (fun c -> c <> `2 <= loop_count`) (conjuncts(lhand fill_goal)));;
let mk_lcN_goal n = mk_imp(mk_conj(gen_precond, mk_eq(`loop_count:num`, mk_small_numeral n)),
    list_mk_icomb "ensures" [`arm`; fill_pre_state; drain_bridge; broad_frame]);;

(* ---- (c) MAINLEG: fill_pre@0x2c -> drain_bridge@0x6c0, loop_count>=2 (folds LC2). ---- *)
let mainleg_goal = mk_imp(mk_conj(gen_precond, `2 <= loop_count`),
    list_mk_icomb "ensures" [`arm`; fill_pre_state; drain_bridge; broad_frame]);;
let mainleg_body =
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  ENSURES_SEQUENCE_TAC `pc + 0x26c`
    (rhs(concl((BETA_CONV THENC REWRITE_CONV[ADD_CLAUSES]) (mk_comb(swp_inv,`0`))))) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    MATCH_MP_TAC FILLLEG_BROAD THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ENSURES_SEQUENCE_TAC `pc + 0x570`
    (rhs(concl((BETA_CONV THENC REWRITE_CONV[ADD_CLAUSES]) (mk_comb(swp_inv,`loop_count - 1`))))) THEN
  CONJ_TAC THENL
   [ENSURES_WHILE_UP_TAC `loop_count - 1` `pc + 0x26c` `pc + 0x570` while_inv THEN
    REPEAT CONJ_TAC THENL
     [MAP_EVERY(fun t->TRY(UNDISCH_TAC t)) [`2 <= loop_count`] THEN ARITH_TAC;
      ENSURES_INIT_TAC "s0" THEN ENSURES_FINAL_STATE_TAC THEN
      RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE `4 * 0 + 2 = 2`; ARITH_RULE `64 * 0 + 32 = 32`;
                                  ARITH_RULE `4 * 0 = 0`; ARITH_RULE `64 * 0 = 0`; MULT_CLAUSES; ADD_CLAUSES]) THEN
      REWRITE_TAC[ARITH_RULE `4 * 0 + 2 = 2`; ARITH_RULE `4 * 0 + 3 = 3`; ARITH_RULE `4 * 0 + 4 = 4`;
                  ARITH_RULE `4 * 0 + 5 = 5`; ARITH_RULE `4 * 0 + 1 = 1`; ARITH_RULE `4 * 0 = 0`;
                  ARITH_RULE `64 * 1 = 64`; ARITH_RULE `64 * 0 = 0`; ARITH_RULE `64 * 0 + 32 = 32`;
                  MULT_CLAUSES; ADD_CLAUSES; LT] THEN
      ASM_REWRITE_TAC[];
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[ADD_CLAUSES] THEN
      REWRITE_TAC[GSYM MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
      MATCH_MP_TAC BODYLEG_BROAD THEN ASM_REWRITE_TAC[] THEN
      MAP_EVERY (fun t -> TRY(UNDISCH_TAC t)) [`i < loop_count - 1`; `2 <= loop_count`] THEN ARITH_TAC;
      X_GEN_TAC `k:num` THEN STRIP_TAC THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[ADD_CLAUSES] THEN
      ENSURES_INIT_TAC "s0" THEN RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_4]) THEN REWRITE_TAC[htable_mem_4] THEN
      SUBGOAL_THEN `val (word (loop_count - (k+1)):int64) = loop_count - (k+1)` ASSUME_TAC THENL
       [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
        MAP_EVERY(fun t->TRY(UNDISCH_TAC t)) [`nblocks DIV 4 = loop_count`; `16 * nblocks < 2 EXP 64`] THEN ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `~(loop_count - (k+1) = 0)` ASSUME_TAC THENL
       [MAP_EVERY(fun t->TRY(UNDISCH_TAC t)) [`k < loop_count - 1`; `2 <= loop_count`] THEN ARITH_TAC; ALL_TAC] THEN
      ARM_STEPS_TAC AES256_GCM_DEC_EXEC [1] THEN ENSURES_FINAL_STATE_TAC THEN
      ASM_REWRITE_TAC[VAL_EQ_0; WORD_SUB_EQ_0] THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES] THEN ASM_REWRITE_TAC[];
      ENSURES_INIT_TAC "s0" THEN ENSURES_FINAL_STATE_TAC THEN
      REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES] THEN ASM_REWRITE_TAC[]];
    REWRITE_TAC[GSYM MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    MATCH_MP_TAC DRAINLEG_BROAD THEN ASM_REWRITE_TAC[]];;
let MAINLEG = prove(mainleg_goal, REPEAT GEN_TAC THEN STRIP_TAC THEN mainleg_body);;

(* ---- (d) LEG_LC0 (loop_count=0) : full tactic from P4_draft 326-386. ---- *)
let USHR_CHAIN_VAL = prove
 (`!lb. val(word lb:int64) = lb
        ==> val(word_ushr (word_ushr (word_ushr (word lb:int64) 3) 4) 2) = lb DIV 512`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[VAL_WORD_USHR] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[DIV_DIV] THEN AP_TERM_TAC THEN ARITH_TAC);;
let LC0_DIV = prove
 (`len_bits DIV 128 = nblocks /\ nblocks DIV 4 = loop_count /\ loop_count = 0 ==> len_bits DIV 512 = 0`,
  STRIP_TAC THEN SUBGOAL_THEN `len_bits DIV 512 = loop_count` (fun th->ASM_REWRITE_TAC[th]) THEN
  MAP_EVERY EXPAND_TAC ["loop_count"; "nblocks"] THEN ASM_REWRITE_TAC[DIV_DIV] THEN AP_TERM_TAC THEN ARITH_TAC);;
let X15_FOLD = prove
 (`!lb. lb < 2 EXP 64 ==> word_ushr (word lb:int64) 3 = word (lb DIV 8)`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `val(word lb:int64) = lb` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN ASM_REWRITE_TAC[DIMINDEX_64]; ALL_TAC] THEN
  REWRITE_TAC[GSYM VAL_EQ] THEN ASM_REWRITE_TAC[VAL_WORD_USHR] THEN
  SUBGOAL_THEN `2 EXP 3 = 8` SUBST1_TAC THENL [CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC VAL_WORD_EQ THEN
  REWRITE_TAC[DIMINDEX_64] THEN UNDISCH_TAC `lb < 2 EXP 64` THEN ARITH_TAC);;
let USHR2_128 = prove
 (`!lb. lb < 2 EXP 64 ==> word_ushr (word_ushr (word lb:int64) 3) 4 = word (lb DIV 128)`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `val(word lb:int64) = lb` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN ASM_REWRITE_TAC[DIMINDEX_64]; ALL_TAC] THEN
  REWRITE_TAC[GSYM VAL_EQ] THEN ASM_REWRITE_TAC[VAL_WORD_USHR] THEN
  SUBGOAL_THEN `2 EXP 3 = 8 /\ 2 EXP 4 = 16` (fun th -> REWRITE_TAC[CONJUNCT1 th; CONJUNCT2 th]) THENL
   [CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  ASM_REWRITE_TAC[DIV_DIV] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
  UNDISCH_TAC `lb < 2 EXP 64` THEN ARITH_TAC);;
let X9_FOLD = prove
 (`!lb. lb < 2 EXP 64
    ==> word_and (word_ushr (word_ushr (word lb:int64) 3) 4) (word 3) = word ((lb DIV 128) MOD 4)`,
  GEN_TAC THEN DISCH_TAC THEN ASM_SIMP_TAC[USHR2_128] THEN
  SUBGOAL_THEN `word 3:int64 = word (2 EXP 2 - 1)` SUBST1_TAC THENL
   [REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_AND_MASK_WORD] THEN
  SUBGOAL_THEN `val(word (lb DIV 128):int64) = lb DIV 128` SUBST1_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    UNDISCH_TAC `lb < 2 EXP 64` THEN ARITH_TAC; ALL_TAC] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
  MATCH_MP_TAC(ARITH_RULE `x < 4 ==> x < 2 EXP 64`) THEN
  REWRITE_TAC[MOD_LT_EQ] THEN CONV_TAC NUM_REDUCE_CONV);;
let NIST_GHASH_NIL = prove
 (`!h tag0 f. nist_ghash h tag0 (list_of_seq f 0) = tag0`, REWRITE_TAC[LIST_OF_SEQ; nist_ghash]);;
let leg_lc0_tac =
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  STRIP_TAC THEN REWRITE_TAC[fst AES256_GCM_DEC_EXEC] THEN ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_4]) THEN REWRITE_TAC[htable_mem_4] THEN
  UNDISCH_TAC `read (memory :> bytes128 ivec_p) s0 = word_reversefields 8 (ctr_block nonce c)` THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [el 1 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT)] THEN DISCH_TAC THEN
  ABBREV_TAC `ivlo:int64 = read (memory :> bytes64 ivec_p) s0` THEN
  ABBREV_TAC `ivhi:int64 = read (memory :> bytes64 (word_add ivec_p (word 8))) s0` THEN
  FIRST_X_ASSUM(fun th -> if is_conj(concl th) && (let s = string_of_term(concl th) in
      contains "h_power" s && contains "htable_p" s) then STRIP_ASSUME_TAC th else NO_TAC) THEN
  KEY_EXPAND_TAC THEN
  MAP_EVERY (fun n -> gkeepN REDSETX_DEC AES256_GCM_DEC_EXEC ("s"^string_of_int n)) (1--31) THEN
  SUBGOAL_THEN `val(word len_bits:int64) = len_bits` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    UNDISCH_TAC `len_bits < 2 EXP 64` THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `read X1 s31 = word loop_count` ASSUME_TAC THENL
   [FIRST_ASSUM(fun th -> if concl th = `read X1 s31 = word_ushr (word_ushr (word_ushr (word len_bits) 3) 4) 2`
      then REWRITE_TAC[th] else NO_TAC) THEN
    REWRITE_TAC[WORD_USHR_COMPOSE] THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN REWRITE_TAC[word_ushr] THEN
    REWRITE_TAC[ASSUME `val(word len_bits:int64) = len_bits`] THEN
    MAP_EVERY EXPAND_TAC ["loop_count"; "nblocks"] THEN REWRITE_TAC[DIV_DIV] THEN AP_TERM_TAC THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN `val(word_ushr (word_ushr (word_ushr (word len_bits) 3) 4) 2:int64) = 0` ASSUME_TAC THENL
   [MP_TAC(SPEC `len_bits:num` USHR_CHAIN_VAL) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC LC0_DIV THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  gkeepN REDSETX_DEC AES256_GCM_DEC_EXEC "s32" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `val(word_ushr (word_ushr (word_ushr (word len_bits) 3) 4) 2:int64) = 0`]) THEN
  DISCARD_OLDSTATE_TAC "s32" THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ARITH_RULE `64 * 0 = 0`; WORD_ADD_0; ARITH_RULE `4 * 0 = 0`;
              ARITH_RULE `4 * (0 - 1) = 0`; ADD_CLAUSES] THEN
  REPEAT CONJ_TAC THEN
  (fun (asl,w) ->
    let ivjoin () = snd(List.find (fun (_,th)-> can (find_term (fun t->t=`word_reversefields 8 (ctr_block nonce c)`)) (concl th)
                       && (try fst(dest_const(fst(strip_comb(lhs(concl th)))))="word_join" with _->false)) asl) in
    let is_mem_iv w = is_eq w && (try fst(dest_const(fst(strip_comb(rhs w))))="word_reversefields" with _->false)
                       && can(find_term(fun t->match t with Comb(Comb(Const("ctr_block",_),_),_)->true|_->false)) (rhs w) in
    if is_forall w then (REWRITE_TAC[LT] THEN GEN_TAC THEN REWRITE_TAC[]) (asl,w)
    else if is_mem_iv w then
      (GEN_REWRITE_TAC (LAND_CONV) [el 1 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT)] THEN
       CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN ASM_REWRITE_TAC[]) (asl,w)
    else if is_eq w && can(find_term(fun t->match t with Const("nist_ghash",_)->true|_->false)) w then
      (REWRITE_TAC[NIST_GHASH_NIL] THEN POP_ASSUM_LIST(K ALL_TAC) THEN CONV_TAC WORD_BLAST) (asl,w)
    else if is_eq w && can(find_term(fun t->t=`ivhi:int64`)) (lhs w) then
      (REWRITE_TAC[MATCH_MP BASE_CTR_DEC (ivjoin())]) (asl,w)
    else if is_eq w && (try fst(dest_const(fst(strip_comb(lhs w))))="word_ushr" with _->false)
            && not(can(find_term(fun t->match t with Const("word_and",_)->true|_->false)) w) then
      ASM_SIMP_TAC[X15_FOLD] (asl,w)
    else if is_eq w && (try fst(dest_const(fst(strip_comb(lhs w))))="word_and" with _->false) then
      (ASM_SIMP_TAC[X9_FOLD] THEN AP_TERM_TAC THEN
       MAP_EVERY (fun t->TRY(UNDISCH_TAC t)) [`nblocks MOD 4 = loop_remain`; `len_bits DIV 128 = nblocks`] THEN MESON_TAC[]) (asl,w)
    else ASM_REWRITE_TAC[] (asl,w));;
let LEG_LC0 = prove(mk_lcN_goal 0, leg_lc0_tac);;

(* ---- (e) LEG_LC1: the loop_count=1 degenerate leg: FILL_TO_CBZ_DEC, the cbz@0x268 TAKEN (X1 = word
   (loop_count - 1) = word 0) into the drain at 0x574, then DRAIN_FROM_574 at index loop_count - 1 = 0. ---- *)

let lc1_frame = `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
      MAYCHANGE [X19; X20; X21; X22; X23; X24; X25; X26; X27; X28; X29; X30] ,,
      MAYCHANGE [Q0; Q1; Q2; Q3; Q4; Q5; Q6; Q7; Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15; Q16; Q17; Q29; Q30; Q31] ,,
      MAYCHANGE [memory :> bytes(out_p:int64, 16 * nblocks)] ,,
      MAYCHANGE [memory :> bytes(tag_p:int64,16)] ,, MAYCHANGE [memory :> bytes(ivec_p:int64,16)] ,,
      MAYCHANGE [memory :> bytes(word_add stackpointer (word 160):int64, 64)] ,, MAYCHANGE [events]`;;

let leg_lc1_goal = mk_imp(mk_conj(gen_precond, `loop_count = 1`),
    list_mk_icomb "ensures" [`arm`; fill_pre; drain_bridge; lc1_frame]);;

let widen_leg_to bigframe th =
  let vars,_ = strip_forall (concl th) in
  let leg0 = SPEC_ALL th in
  let pre = lhand(concl leg0) in
  let ud = UNDISCH leg0 in
  let narrow = rand(concl ud) in
  let subth = prove(list_mk_icomb "subsumed" [narrow; bigframe],
     REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN SUBSUMED_MAYCHANGE_TAC) in
  let broad = DISCH pre (MATCH_MP ENSURES_FRAME_SUBSUMED (CONJ subth ud)) in
  GENL (if vars = [] then frees(concl broad) else vars) broad;;
let FILL_TO_CBZ_DEC_LC1 = widen_leg_to lc1_frame FILL_TO_CBZ_DEC;;
let DRAIN_FROM_574_LC1 = widen_leg_to lc1_frame DRAIN_FROM_574;;

let leg_lc1_tac =
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  ENSURES_SEQUENCE_TAC `pc + 0x268` (swp_inv_dec_at `0`) THEN CONJ_TAC THENL
   [REFOLD_ABI THEN MATCH_MP_TAC FILL_TO_CBZ_DEC_LC1 THEN ASM_REWRITE_TAC[] THEN
    TRY(UNDISCH_TAC `loop_count = 1` THEN ARITH_TAC);
    ENSURES_SEQUENCE_TAC `pc + 0x574` (swp_inv_dec_at `0`) THEN CONJ_TAC THENL
     [hop_init_dec THEN
      SUBGOAL_THEN `val (word (loop_count - 1):int64) = 0` ASSUME_TAC THENL
       [UNDISCH_TAC `loop_count = 1` THEN DISCH_THEN SUBST1_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN
        REWRITE_TAC[VAL_WORD_0]; ALL_TAC] THEN
      SUBGOAL_THEN `loop_count <= 1` ASSUME_TAC THENL
       [UNDISCH_TAC `loop_count = 1` THEN ARITH_TAC; ALL_TAC] THEN
      ARM_STEPS_TAC AES256_GCM_DEC_EXEC [1] THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      TRY(CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]);
      (* index bridge: the hop lands in the invariant at the CONCRETE index 0 = loop_count - 1. *)
      ENSURES_PRECONDITION_TAC (leg_state_dec swp_inv `0x574` `loop_count - 1`) THEN CONJ_TAC THENL
       [GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
        FIRST_ASSUM(fun th -> if lhs(concl th) = `loop_count:num` then REWRITE_TAC[th] else NO_TAC) THEN
        CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];
        REFOLD_ABI THEN MATCH_MP_TAC DRAIN_FROM_574_LC1 THEN ASM_REWRITE_TAC[] THEN
        TRY(UNDISCH_TAC `loop_count = 1` THEN ARITH_TAC)]]];;
let LEG_LC1 = prove(leg_lc1_goal, leg_lc1_tac);;

(* ---- (f) CORE_FROM88: gen_precond -> tail_post@0x7c4, ALL loop_count. ---- *)
let from88_frame = last(snd(strip_comb(snd(dest_imp(concl(SPEC_ALL TAILLEG))))));;
let widen_to_from88 th =
  let vars,_ = strip_forall (concl th) in
  let leg0 = SPEC_ALL th in
  let pre = lhand(concl leg0) in
  let ud = UNDISCH leg0 in
  let narrow = rand(concl ud) in
  let subth = prove(list_mk_icomb "subsumed" [narrow; from88_frame],
     REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN SUBSUMED_MAYCHANGE_TAC) in
  let broad = DISCH pre (MATCH_MP ENSURES_FRAME_SUBSUMED (CONJ subth ud)) in
  GENL (if vars = [] then frees(concl broad) else vars) broad;;
let strip_aligned_pc abs =
  let s,body = dest_abs abs in
  let keep = filter (fun c ->
    not(can (find_term (fun t -> is_const t && fst(dest_const t)="aligned_bytes_loaded")) c)
    && not(can (find_term (fun t -> t = `read PC`)) c)) (conjuncts body) in
  mk_abs(s, list_mk_conj keep);;
let drain_bridge_body = strip_aligned_pc drain_bridge;;
let TAILLEG_FROM88 = widen_to_from88 TAILLEG;;
let core_from88_goal = mk_imp(gen_precond, list_mk_icomb "ensures" [`arm`; fill_pre_state; tail_post; from88_frame]);;
let core_from88_tac =
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  ENSURES_SEQUENCE_TAC `pc + 0x6c0` drain_bridge_body THEN
  CONJ_TAC THENL
   [ASM_CASES_TAC `loop_count = 0` THENL
     [REWRITE_TAC[GSYM MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN MATCH_MP_TAC (widen_to_from88 LEG_LC0) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_CASES_TAC `loop_count = 1` THENL
     [REWRITE_TAC[GSYM MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN MATCH_MP_TAC (widen_to_from88 LEG_LC1) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `2 <= loop_count` ASSUME_TAC THENL
     [MAP_EVERY(fun t->TRY(UNDISCH_TAC t)) [`~(loop_count=0)`;`~(loop_count=1)`] THEN ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[GSYM MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN MATCH_MP_TAC (widen_to_from88 MAINLEG) THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[GSYM MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN MATCH_MP_TAC TAILLEG_FROM88 THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN NONOVERLAPPING_TAC];;
let CORE_FROM88 = prove(core_from88_goal, core_from88_tac);;

(* ============================================================================ *)
(* AES256_GCM_DEC_CORRECT: whole core function pc+0x2c -> pc+0x7c4.                      *)
(* Since fill_pre is at 0x2c and tail_post at 0x7c4, CORE_FROM88 spans the       *)
(* entire core; the CORRECT preamble is just the round-key list split + a bridge *)
(* to fill_pre_state, then MATCH_MP_TAC CORE_FROM88.  (Simpler than enc-256,     *)
(* which needed a 0x2c->0xb0 preamble step; dec-256's round-key loads live       *)
(* inside FILL.)                                                                 *)
(* ============================================================================ *)
(* The (stronger) from88 postcondition, extracted from CORE_FROM88 directly (folded htable). *)
let core_from88_post =
  el 2 (snd(strip_comb(snd(dest_imp(snd(strip_forall(concl CORE_FROM88)))))));;
let AES256_GCM_DEC_CORRECT = prove
 (`!in_p out_p len_bits tag_p ivec_p key_p htable_p tag0 nonce rk inblock pc
     stackpointer.
       aligned 16 stackpointer /\
       ALLPAIRS nonoverlapping
        [(out_p, 16 * val len_bits DIV 128); (tag_p, 16); (ivec_p, 16);
         (word_add stackpointer (word 160), 64)]
        [(word pc, LENGTH aes256_gcm_dec_mc);
         (in_p,  16 * val len_bits DIV 128); (key_p, 240); (htable_p, 96)] /\
       PAIRWISE nonoverlapping
        [(out_p, 16 * val len_bits DIV 128); (tag_p, 16); (ivec_p, 16);
         (word_add stackpointer (word 160), 64)]
    ==>
    ensures arm
      (\s. aligned_bytes_loaded s (word pc) aes256_gcm_dec_mc /\
           read PC s = word (pc + 0x2c) /\
           read SP s = stackpointer /\
           C_ARGUMENTS
            [in_p; len_bits; out_p; tag_p; ivec_p; key_p; htable_p] s /\
           read (memory :> bytes128 tag_p)  s = word_reversefields 8 tag0 /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce c) /\
           wordlist_from_memory(key_p,15) s =
             MAP (word_reversefields 8) rk /\
           (!i. i < val len_bits DIV 128
                ==> read (memory :> bytes128 (word_add in_p (word(16*i)))) s =
                    inblock i) /\
           htable_mem_4 (ghash_twist (aes256_cipher (word 0) rk))
                      htable_p s)
      (\s. read PC s = word (pc + 0x7c4) /\
           (!i. i < val len_bits DIV 128
                ==> read (memory :> bytes128 (word_add out_p (word(16*i)))) s =
                    word_xor (aes256_ctr_block c nonce rk i) (inblock i)) /\
           read (memory :> bytes128 tag_p) s =
             word_reversefields 8
              (nist_ghash (aes256_cipher (word 0) rk) tag0
                 (list_of_seq (nist_input_block inblock)
                              (val len_bits DIV 128))) /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8
               (ctr_block nonce (val len_bits DIV 128 + c)) /\
           read X0 s = word (val len_bits DIV 8))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [X19; X20; X21; X22; X23; X24; X25; X26; X27; X28; X29; X30] ,,
       MAYCHANGE [Q0; Q1; Q2; Q3; Q4; Q5; Q6; Q7; Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15; Q16; Q17; Q29; Q30; Q31] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * val len_bits DIV 128)] ,,
       MAYCHANGE [memory :> bytes(tag_p, 16)] ,,
       MAYCHANGE [memory :> bytes(ivec_p, 16)] ,,
       MAYCHANGE [memory :> bytes(word_add stackpointer (word 160), 64)] ,,
       MAYCHANGE [events])`,
  GEN_TAC THEN GEN_TAC THEN W64_GEN_TAC `len_bits:num` THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REWRITE_TAC[ALLPAIRS; PAIRWISE; ALL; fst AES256_GCM_DEC_EXEC] THEN
  ABBREV_TAC `nblocks     = len_bits DIV 128` THEN
  ABBREV_TAC `loop_count  = nblocks DIV 4` THEN
  ABBREV_TAC `loop_remain = nblocks MOD 4` THEN
  STRIP_TAC THEN
  (*** Weaken the goal postcondition to the (stronger) from88 postcondition FIRST, before the
       round-key case split, so both LENGTH branches share it. ***)
  MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN
  EXISTS_TAC core_from88_post THEN CONJ_TAC THENL
   [GEN_TAC THEN BETA_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (*** CORE_FROM88 keeps rk abstract (wordlist_from_memory).  Case-split LENGTH rk = 15:
       - =15: derive the round-key list identity [EL 0 rk;...;EL 14 rk] = rk (from LENGTH via
         LENGTH_EQ_LIST_OF_SEQ, NO rk expansion), reconcile the C_ARGUMENTS-form precondition with
         fill_pre_state (ENSURES_PRECONDITION), then MATCH_MP_TAC CORE_FROM88.
       - <>15: the wordlist_from_memory precondition forces LENGTH rk = 15, a contradiction, so the
         precondition is unsatisfiable -> ENSURES_PRECONDITION to (\s.F) + ENSURES_TRIVIAL. ***)
  ASM_CASES_TAC `LENGTH(rk:int128 list) = 15` THENL
   [SUBGOAL_THEN
     `[EL 0 rk; EL 1 rk; EL 2 rk; EL 3 rk; EL 4 rk; EL 5 rk; EL 6 rk; EL 7 rk;
       EL 8 rk; EL 9 rk; EL 10 rk; EL 11 rk; EL 12 rk; EL 13 rk; EL 14 rk]:(int128)list = rk`
     ASSUME_TAC THENL
     [FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [LENGTH_EQ_LIST_OF_SEQ]) THEN
      CONV_TAC(LAND_CONV(RAND_CONV LIST_OF_SEQ_CONV)) THEN
      CONV_TAC(LAND_CONV(RAND_CONV(TOP_DEPTH_CONV BETA_CONV))) THEN
      DISCH_THEN(ACCEPT_TAC o SYM); ALL_TAC] THEN
    ENSURES_PRECONDITION_TAC fill_pre_state THEN CONJ_TAC THENL
     [GEN_TAC THEN BETA_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[GSYM MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    MATCH_MP_TAC CORE_FROM88 THEN
    REPEAT CONJ_TAC THEN
    FIRST[ ASM_REWRITE_TAC[] THEN NO_TAC;
           (MAP_EVERY UNDISCH_TAC [`len_bits < 2 EXP 64`; `len_bits DIV 128 = nblocks`] THEN ARITH_TAC);
           NONOVERLAPPING_TAC ];
    ENSURES_PRECONDITION_TAC `\s:armstate. F` THEN CONJ_TAC THENL
     [GEN_TAC THEN BETA_TAC THEN STRIP_TAC THEN
      FIRST_X_ASSUM(fun th -> let c = concl th in
         if is_eq c && can (find_term (fun t -> is_const t && fst(dest_const t)="wordlist_from_memory")) c
         then MP_TAC(AP_TERM `LENGTH:int128 list->num` th) else NO_TAC) THEN
      REWRITE_TAC[LENGTH_WORDLIST_FROM_MEMORY; LENGTH_MAP] THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[ENSURES_TRIVIAL]]]);;

(* ============================================================================ *)
(* P5 SUBROUTINE wrapper: lift AES256_GCM_DEC_CORRECT through the 11-step save prologue  *)
(* and 11-step restore epilogue (D8-D15 + X19-X30, 224-byte frame).             *)

let AES256_GCM_DEC_SUBROUTINE_CORRECT = prove
 (`!in_p out_p len_bits tag_p ivec_p key_p htable_p tag0 nonce rk inblock
    pc stackpointer returnaddress.
    aligned 16 stackpointer /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * val len_bits DIV 128); (tag_p, 16); (ivec_p, 16);
       (word_sub stackpointer (word 224), 224)]
      [(word pc, LENGTH aes256_gcm_dec_mc);
       (in_p,  16 * val len_bits DIV 128); (key_p, 240); (htable_p, 96)] /\
    PAIRWISE nonoverlapping
      [(out_p, 16 * val len_bits DIV 128); (tag_p, 16); (ivec_p, 16);
       (word_sub stackpointer (word 224), 224)]
    ==>
    ensures arm
      (\s. aligned_bytes_loaded s (word pc) aes256_gcm_dec_mc /\
           read PC s = word pc /\
           read SP s = stackpointer /\
           read X30 s = returnaddress /\
           C_ARGUMENTS
            [in_p; len_bits; out_p; tag_p; ivec_p; key_p; htable_p] s /\
           read (memory :> bytes128 tag_p)  s = word_reversefields 8 tag0 /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce c) /\
           wordlist_from_memory(key_p,15) s =
             MAP (word_reversefields 8) rk /\
           (!i. i < val len_bits DIV 128
                ==> read (memory :> bytes128 (word_add in_p (word(16*i)))) s =
                    inblock i) /\
           htable_mem_4 (ghash_twist (aes256_cipher (word 0) rk))
                      htable_p s)
      (\s. read PC s = returnaddress /\
           (!i. i < val len_bits DIV 128
                ==> read (memory :> bytes128 (word_add out_p (word(16*i)))) s =
                    word_xor (aes256_ctr_block c nonce rk i) (inblock i)) /\
           read (memory :> bytes128 tag_p) s =
             word_reversefields 8
              (nist_ghash (aes256_cipher (word 0) rk) tag0
                 (list_of_seq (nist_input_block inblock)
                              (val len_bits DIV 128))) /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8
               (ctr_block nonce (val len_bits DIV 128 + c)) /\
           read X0 s = word (val len_bits DIV 8))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * val len_bits DIV 128);
                  memory :> bytes(tag_p, 16);
                  memory :> bytes(ivec_p, 16);
                  memory :> bytes(word_sub stackpointer (word 224), 224)])`,
  REWRITE_TAC[fst AES256_GCM_DEC_EXEC; htable_mem_4; KEY15_SPLIT] THEN
  ARM_ADD_RETURN_STACK_TAC
    ~pre_post_nsteps:(11, 11)
    AES256_GCM_DEC_EXEC
    (REWRITE_RULE[KEY15_SPLIT]
       (REWRITE_RULE[fst AES256_GCM_DEC_EXEC; htable_mem_4] AES256_GCM_DEC_CORRECT))
    `[X19; X20; X21; X22; X23; X24; X25; X26; X27; X28; X29; X30;
      D8; D9; D10; D11; D12; D13; D14; D15]` 224);;

(* ========================================================================= *)
(* Constant-time (data-independent event trace) and memory-safety proofs.    *)
(* Mirrors the AES-GCM-128 SWP dec/enc safety proofs: an abstract per-leg     *)
(* event scaffold (CONCRETIZE_F_EVENTS_TAC) walked with the event-tracking    *)
(* simulator SAFE_SIM, closed by the shared consttime/utils closers.          *)
(* Case split loop_count = 0 / 1 / >=2 (fill + steady + drain) and the tail   *)
(* WHILE over loop_remain; SUBROUTINE variant wraps the 224-byte frame        *)
(* prologue/epilogue (x30 at sp+88).                                          *)
(* ========================================================================= *)

(* ===== dec-256 SWP constant-time + memory-safety ===== *)
(* Uses AES256_GCM_DEC_EXEC from the prefix.  CFG (post-prologue core, entry pc+0x2c):   *)
(*   0xa8  cbz  x1,0x6c0   (loop_count=0 -> tail region)                          *)
(*   0x268 cbz  x1,0x574   (loop_count=1 -> drain; x1=loop_count-1 here)          *)
(*   0x570 cbnz x1,0x26c   (main-loop back-edge, body 0x26c..0x56c = 193 instr)   *)
(*   0x6bc b    0x6c0      (drain -> tail-region join; drain 0x570..0x6bc = 84)   *)
(*   0x6cc cbz  x9,0x7b0   (loop_remain=0 -> writeback)                           *)
(*   0x7ac cbnz x9,0x6d0   (tail-loop back-edge, body 0x6d0..0x7a8 = 55 instr)    *)
(*   0x7c4 core end (tail_post); 0x7f0 ret.  loop_remain reg = X9.                *)

let SAFE_SIM = SAFE_SIM_TAC AES256_GCM_DEC_EXEC;;

(* DRAIN pointer reconciliation: the loop-exit inv carries 64*(loop_count-1)+64, the drain_bridge
   states 64*loop_count.  Linearise loop_count = (loop_count-1)+1 (valid since loop_count>=2) so
   WORD_RULE sees only linear combinations. *)
let DRAIN_ADDR = DRAIN_ADDR_K `1`;;

let OPEN_DEC = OPEN_SWP_SAFE AES256_GCM_DEC_EXEC;;

(* scaffold: cases loop_count = 0 (m0) / 1 (m1) / >=2 (drain + steady(loop_count-1) + fill). *)
let scaffold_dec =
 `\(in_p:int64) (out_p:int64) (tag_p:int64) (ivec_p:int64) (key_p:int64) (htable_p:int64)
   (len_bits:int64) (pc:num) (stackpointer:int64).
   APPEND
     (if val len_bits DIV 128 MOD 4 = 0 then
        f_ev_tail0 in_p out_p tag_p ivec_p key_p htable_p len_bits pc stackpointer
      else
        APPEND
          (f_ev_tail_post in_p out_p tag_p ivec_p key_p htable_p len_bits pc stackpointer)
          (APPEND
            (ENUMERATEL (val len_bits DIV 128 MOD 4)
              (\i. f_ev_tail_body in_p out_p tag_p ivec_p key_p htable_p len_bits pc stackpointer i))
            (f_ev_tail_pre in_p out_p tag_p ivec_p key_p htable_p len_bits pc stackpointer)))
     (APPEND
       (if val len_bits DIV 128 DIV 4 = 0 then
          f_ev_m0 in_p out_p tag_p ivec_p key_p htable_p len_bits pc stackpointer
        else if val len_bits DIV 128 DIV 4 = 1 then
          f_ev_m1 in_p out_p tag_p ivec_p key_p htable_p len_bits pc stackpointer
        else
          APPEND
            (f_ev_drain in_p out_p tag_p ivec_p key_p htable_p len_bits pc stackpointer)
            (APPEND
              (ENUMERATEL (val len_bits DIV 128 DIV 4 - 1)
                (\i. f_ev_steady in_p out_p tag_p ivec_p key_p htable_p len_bits pc stackpointer i))
              (f_ev_fill in_p out_p tag_p ivec_p key_p htable_p len_bits pc stackpointer)))
       (f_ev_pro in_p out_p tag_p ivec_p key_p htable_p len_bits pc stackpointer))
   :(uarch_event) list`;;

let AES256_GCM_DEC_SAFE = prove
 (`exists f_events.
    forall e in_p len_bits out_p tag_p ivec_p key_p htable_p pc stackpointer.
      aligned 16 stackpointer /\
      ALLPAIRS nonoverlapping
        [(out_p, 16 * val len_bits DIV 128); (tag_p, 16); (ivec_p, 16);
         (word_add stackpointer (word 160), 64)]
        [(word pc, LENGTH aes256_gcm_dec_mc);
         (in_p,  16 * val len_bits DIV 128); (key_p, 240); (htable_p, 96)] /\
      PAIRWISE nonoverlapping
        [(out_p, 16 * val len_bits DIV 128); (tag_p, 16); (ivec_p, 16);
         (word_add stackpointer (word 160), 64)]
      ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) aes256_gcm_dec_mc /\
               read PC s = word (pc + 0x2c) /\
               read SP s = stackpointer /\
               C_ARGUMENTS [in_p; len_bits; out_p; tag_p; ivec_p; key_p; htable_p] s /\
               read events s = e)
          (\s. read PC s = word (pc + 0x7c4) /\
               (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events in_p out_p tag_p ivec_p key_p htable_p len_bits pc stackpointer /\
                    memaccess_inbounds e2
                      [in_p, 16 * val len_bits DIV 128; tag_p, 16; ivec_p, 16; key_p, 240; htable_p, 96;
                       out_p, 16 * val len_bits DIV 128; word_add stackpointer (word 160), 64]
                      [out_p, 16 * val len_bits DIV 128; tag_p, 16; ivec_p, 16;
                       word_add stackpointer (word 160), 64]))
          (\s s'. T)`,
  CONCRETIZE_F_EVENTS_TAC scaffold_dec THEN
  OPEN_DEC THEN

  (*** Top split at 0x6c0 (main region -> tail region). ***)
  ENSURES_EVENTS_SEQUENCE_TAC `pc + 0x6c0`
   `\s. read X0 s = word_add in_p (word (64 * loop_count)) /\
        read X2 s = word_add out_p (word (64 * loop_count)) /\
        read X3 s = tag_p /\ read X4 s = ivec_p /\ read X6 s = htable_p /\
        read SP s = stackpointer /\ read X9 s = word loop_remain` THEN
  CONJ_TAC THENL
   [(*** MAIN REGION pc+0x2c -> pc+0x6c0. ***)
    ENSURES_EVENTS_SEQUENCE_TAC `pc + 0xa8`
     `\s. read X0 s = in_p /\ read X2 s = out_p /\ read X3 s = tag_p /\
          read X4 s = ivec_p /\ read X6 s = htable_p /\ read SP s = stackpointer /\
          read X1 s = word loop_count /\ read X9 s = word loop_remain` THEN
    CONJ_TAC THENL [SAFE_SIM (1--31) THEN CLOSE; ALL_TAC] THEN

    (*** loop_count = 0 : cbz @0xa8 taken -> 0x6c0. ***)
    ASM_CASES_TAC `loop_count = 0` THENL
     [REDUCE_IF0 `loop_count:num` THEN SAFE_SIM (1--1) THEN CLOSE; ALL_TAC] THEN
    REDUCE_IFN0 `loop_count:num` THEN

    (*** loop_count = 1 : FILL to cbz@0x268 (x1=0) taken -> 0x574 -> drain -> 0x6c0. ***)
    ASM_CASES_TAC `loop_count = 1` THENL
     [REDUCE_IFEQ `loop_count:num` `1` THEN SAFE_SIM (1--196) THEN CLOSE; ALL_TAC] THEN
    REDUCE_IFNE `loop_count:num` `1` THEN

    (*** loop_count >= 2 : FILL + STEADY(loop_count-1) + DRAIN. ***)
    SUBGOAL_THEN `2 <= loop_count` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ENSURES_EVENTS_WHILE_UP2_TAC `loop_count - 1` `pc + 0x26c` `pc + 0x574`
     `\i s. read X0 s = word_add in_p (word (64 * i + 64)) /\
            read X2 s = word_add out_p (word (64 * i)) /\
            read X3 s = tag_p /\ read X4 s = ivec_p /\ read X6 s = htable_p /\
            read SP s = stackpointer /\ read X9 s = word loop_remain /\
            read X1 s = word (loop_count - 1 - i)` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [(*** ~(loop_count - 1 = 0) ***)
      ASM_ARITH_TAC;
      (*** FILL: 0xa8 -> 0x26c, establish inv 0.  cbz@0x268 not taken (loop_count>=2). ***)
      BEQ_NZ `1` THEN SAFE_SIM (1--113) THEN
      REPEAT CONJ_TAC THENL
       [ADDR_RECON;
        ADDR_RECON;
        REWRITE_TAC[SUB_0] THEN GEN_REWRITE_TAC RAND_CONV [WORD_SUB] THEN
        ASM_SIMP_TAC[ARITH_RULE `2 <= loop_count ==> 1 <= loop_count`];
        DEABBR THEN DISCHARGE_SAFETY_PROPERTY_TAC];
      (*** STEADY body: 0x26c -> 0x570, inv i -> inv (i+1).  193 instr. ***)
      REWRITE_TAC[] THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
      SUBGOAL_THEN `loop_count - 1 < 2 EXP 64` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      SAFE_SIM (1--194) THEN CLOSE_R2;
      (*** DRAIN: 0x570 -> 0x6c0.  84 instr. ***)
      SAFE_SIM (1--83) THEN REPEAT CONJ_TAC THENL
       [DRAIN_ADDR; DRAIN_ADDR; DEABBR THEN DISCHARGE_SAFE_ROBUST]];

    ALL_TAC] THEN

  (*** TAIL REGION pc+0x6c0 -> pc+0x7c4. ***)
  ASM_CASES_TAC `loop_remain = 0` THENL
   [REDUCE_IF0 `loop_remain:num` THEN SAFE_SIM (1--9) THEN CLOSE_R2; ALL_TAC] THEN
  REDUCE_IFN0 `loop_remain:num` THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `loop_remain:num` `pc + 0x6d0` `pc + 0x7b0`
   `\i s. read X0 s = word_add in_p (word (64 * loop_count + 16 * i)) /\
          read X2 s = word_add out_p (word (64 * loop_count + 16 * i)) /\
          read X3 s = tag_p /\ read X4 s = ivec_p /\ read X6 s = htable_p /\
          read SP s = stackpointer /\ read X9 s = word (loop_remain - i)` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [SAFE_SIM (1--4) THEN CLOSE_R2;
    ALL_TAC;
    REWRITE_TAC[] THEN SAFE_SIM (1--5) THEN CLOSE_R2] THEN
  REWRITE_TAC[] THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
  SAFE_SIM (1--56) THEN CLOSE_R2);;


(* ===== dec-256 SWP subroutine-level constant-time + memory-safety ===== *)
(* Prologue 11 instrs (frame 224, x30 at sp+88); post-prologue core entry pc+0x2c.  *)
(* prologue+setup pc..0xa8 = 42 steps; epilogue pc+0x7c4..0x7f0 = 12 steps (ldp/add/ret, no stores). *)

let AES256_GCM_DEC_SUBROUTINE_SAFE = prove
 (`exists f_events.
    forall e in_p len_bits out_p tag_p ivec_p key_p htable_p pc stackpointer returnaddress.
      aligned 16 stackpointer /\
      ALLPAIRS nonoverlapping
        [(out_p, 16 * val len_bits DIV 128); (tag_p, 16); (ivec_p, 16);
         (word_sub stackpointer (word 224), 224)]
        [(word pc, LENGTH aes256_gcm_dec_mc);
         (in_p,  16 * val len_bits DIV 128); (key_p, 240); (htable_p, 96)] /\
      PAIRWISE nonoverlapping
        [(out_p, 16 * val len_bits DIV 128); (tag_p, 16); (ivec_p, 16);
         (word_sub stackpointer (word 224), 224)]
      ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) aes256_gcm_dec_mc /\
               read PC s = word pc /\
               read SP s = stackpointer /\
               read X30 s = returnaddress /\
               C_ARGUMENTS [in_p; len_bits; out_p; tag_p; ivec_p; key_p; htable_p] s /\
               read events s = e)
          (\s. read PC s = returnaddress /\
               (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events in_p out_p tag_p ivec_p key_p htable_p len_bits pc
                           (word_sub stackpointer (word 224)) returnaddress /\
                    memaccess_inbounds e2
                      [in_p, 16 * val len_bits DIV 128; tag_p, 16; ivec_p, 16; key_p, 240; htable_p, 96;
                       out_p, 16 * val len_bits DIV 128; word_sub stackpointer (word 224), 224]
                      [out_p, 16 * val len_bits DIV 128; tag_p, 16; ivec_p, 16;
                       word_sub stackpointer (word 224), 224]))
          (\s s'. T)`,
  CONCRETIZE_F_EVENTS_TAC
    `\(in_p:int64) (out_p:int64) (tag_p:int64) (ivec_p:int64) (key_p:int64) (htable_p:int64)
      (len_bits:int64) (pc:num) (stackpointer:int64) (returnaddress:int64).
      APPEND
        (f_ev_epi in_p out_p tag_p ivec_p key_p htable_p len_bits pc stackpointer returnaddress)
        (APPEND
        (if val len_bits DIV 128 MOD 4 = 0 then
           f_ev_tail0 in_p out_p tag_p ivec_p key_p htable_p len_bits pc stackpointer returnaddress
         else
           APPEND
             (f_ev_tail_post in_p out_p tag_p ivec_p key_p htable_p len_bits pc stackpointer returnaddress)
             (APPEND
               (ENUMERATEL (val len_bits DIV 128 MOD 4)
                 (\i. f_ev_tail_body in_p out_p tag_p ivec_p key_p htable_p len_bits pc stackpointer returnaddress i))
               (f_ev_tail_pre in_p out_p tag_p ivec_p key_p htable_p len_bits pc stackpointer returnaddress)))
        (APPEND
          (if val len_bits DIV 128 DIV 4 = 0 then
             f_ev_m0 in_p out_p tag_p ivec_p key_p htable_p len_bits pc stackpointer returnaddress
           else if val len_bits DIV 128 DIV 4 = 1 then
             f_ev_m1 in_p out_p tag_p ivec_p key_p htable_p len_bits pc stackpointer returnaddress
           else
             APPEND
               (f_ev_drain in_p out_p tag_p ivec_p key_p htable_p len_bits pc stackpointer returnaddress)
               (APPEND
                 (ENUMERATEL (val len_bits DIV 128 DIV 4 - 1)
                   (\i. f_ev_steady in_p out_p tag_p ivec_p key_p htable_p len_bits pc stackpointer returnaddress i))
                 (f_ev_fill in_p out_p tag_p ivec_p key_p htable_p len_bits pc stackpointer returnaddress)))
          (f_ev_pro in_p out_p tag_p ivec_p key_p htable_p len_bits pc stackpointer returnaddress)))
      :(uarch_event) list` THEN

  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  GEN_TAC THEN W64_GEN_TAC `len_bits:num` THEN
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
  WORD_FORALL_OFFSET_TAC 224 THEN GEN_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS] THEN
  REWRITE_TAC[ALLPAIRS; PAIRWISE; ALL; fst AES256_GCM_DEC_EXEC] THEN
  ABBREV_TAC `nblocks     = len_bits DIV 128` THEN
  ABBREV_TAC `loop_count  = nblocks DIV 4` THEN
  ABBREV_TAC `loop_remain = nblocks MOD 4` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `loop_count < 2 EXP 64 /\ loop_remain < 2 EXP 64` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [EXPAND_TAC "loop_count" THEN EXPAND_TAC "nblocks" THEN REWRITE_TAC[DIV_DIV] THEN
      TRANS_TAC LET_TRANS `len_bits:num` THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
      EXPAND_TAC "loop_remain" THEN TRANS_TAC LTE_TRANS `4` THEN
      SIMP_TAC[MOD_LT_EQ; ARITH_RULE `~(4 = 0)`] THEN ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `val(word loop_count:int64) = loop_count /\ val(word loop_remain:int64) = loop_remain`
    STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC VAL_WORD_EQ THEN ASM_REWRITE_TAC[DIMINDEX_64]; ALL_TAC] THEN
  STRIP_TAC THEN

  (*** Epilogue split at pc+0x7b0 (first writeback instr); region B = writeback + epilogue. ***)
  ENSURES_EVENTS_SEQUENCE_TAC `pc + 0x7b0`
   `\s. read X3 s = tag_p /\ read X4 s = ivec_p /\ read SP s = stackpointer /\
        read (memory :> bytes64 (word_add stackpointer (word 88))) s = returnaddress` THEN
  CONJ_TAC THENL
   [(*** REGION A: pc -> pc+0x7b0 (prologue + pipelined body, up to the writeback). ***)
    ENSURES_EVENTS_SEQUENCE_TAC `pc + 0x6c0`
     `\s. read X0 s = word_add in_p (word (64 * loop_count)) /\
          read X2 s = word_add out_p (word (64 * loop_count)) /\
          read X3 s = tag_p /\ read X4 s = ivec_p /\ read X6 s = htable_p /\
          read SP s = stackpointer /\ read X9 s = word loop_remain /\
          read (memory :> bytes64 (word_add stackpointer (word 88))) s = returnaddress` THEN
    CONJ_TAC THENL
     [(*** setup incl prologue: pc -> 0xa8 = 42 steps. ***)
      ENSURES_EVENTS_SEQUENCE_TAC `pc + 0xa8`
       `\s. read X0 s = in_p /\ read X2 s = out_p /\ read X3 s = tag_p /\
            read X4 s = ivec_p /\ read X6 s = htable_p /\ read SP s = stackpointer /\
            read X1 s = word loop_count /\ read X9 s = word loop_remain /\
            read (memory :> bytes64 (word_add stackpointer (word 88))) s = returnaddress` THEN
      CONJ_TAC THENL [SAFE_SIM (1--42) THEN CLOSE_SUB; ALL_TAC] THEN

      ASM_CASES_TAC `loop_count = 0` THENL
       [REDUCE_IF0 `loop_count:num` THEN SAFE_SIM (1--1) THEN CLOSE_SUB; ALL_TAC] THEN
      REDUCE_IFN0 `loop_count:num` THEN
      ASM_CASES_TAC `loop_count = 1` THENL
       [REDUCE_IFEQ `loop_count:num` `1` THEN SAFE_SIM (1--196) THEN CLOSE_SUB; ALL_TAC] THEN
      REDUCE_IFNE `loop_count:num` `1` THEN
      SUBGOAL_THEN `2 <= loop_count` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      ENSURES_EVENTS_WHILE_UP2_TAC `loop_count - 1` `pc + 0x26c` `pc + 0x574`
       `\i s. read X0 s = word_add in_p (word (64 * i + 64)) /\
              read X2 s = word_add out_p (word (64 * i)) /\
              read X3 s = tag_p /\ read X4 s = ivec_p /\ read X6 s = htable_p /\
              read SP s = stackpointer /\ read X9 s = word loop_remain /\
              read X1 s = word (loop_count - 1 - i) /\
              read (memory :> bytes64 (word_add stackpointer (word 88))) s = returnaddress` THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [ASM_ARITH_TAC;
        BEQ_NZ `1` THEN SAFE_SIM (1--113) THEN
        REPEAT CONJ_TAC THEN
        W(fun (asl,w) ->
          if is_exists w then (DEABBR THEN DISCHARGE_SAFETY_PROPERTY_TAC)
          else if can dest_eq w &&
                  (let l,_ = dest_eq w in
                   can (find_term (fun t -> t = `word_sub (word loop_count:int64) (word 1)`)) l)
          then (REWRITE_TAC[SUB_0] THEN GEN_REWRITE_TAC RAND_CONV [WORD_SUB] THEN
                ASM_SIMP_TAC[ARITH_RULE `2 <= loop_count ==> 1 <= loop_count`])
          else (ADDR_RECON ORELSE MEM_PRESERVE));
        REWRITE_TAC[] THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
        SUBGOAL_THEN `loop_count - 1 < 2 EXP 64` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
        SAFE_SIM (1--194) THEN CLOSE_R2_SUB;
        SAFE_SIM (1--83) THEN REPEAT CONJ_TAC THEN
        W(fun (asl,w) ->
          if is_exists w then (DEABBR THEN DISCHARGE_SAFE_ROBUST)
          else (DRAIN_ADDR ORELSE MEM_PRESERVE))];

      ALL_TAC] THEN
    (*** TAIL region of the body: pc+0x6c0 -> pc+0x7b0. ***)
    ASM_CASES_TAC `loop_remain = 0` THENL
     [REDUCE_IF0 `loop_remain:num` THEN SAFE_SIM (1--4) THEN CLOSE_R2_SUB; ALL_TAC] THEN
    REDUCE_IFN0 `loop_remain:num` THEN
    ENSURES_EVENTS_WHILE_UP2_TAC `loop_remain:num` `pc + 0x6d0` `pc + 0x7b0`
     `\i s. read X0 s = word_add in_p (word (64 * loop_count + 16 * i)) /\
            read X2 s = word_add out_p (word (64 * loop_count + 16 * i)) /\
            read X3 s = tag_p /\ read X4 s = ivec_p /\ read X6 s = htable_p /\
            read SP s = stackpointer /\ read X9 s = word (loop_remain - i) /\
            read (memory :> bytes64 (word_add stackpointer (word 88))) s = returnaddress` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [SAFE_SIM (1--4) THEN CLOSE_R2_SUB;
      ALL_TAC;
      REWRITE_TAC[] THEN SAFE_SIM [] THEN CLOSE_R2_SUB] THEN
    REWRITE_TAC[] THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
    SAFE_SIM (1--56) THEN CLOSE_R2_SUB;

    (*** REGION B: pc+0x7b0 -> returnaddress (mov x0,x15; str tag; str ctr; 10 ldp; add sp; ret = 17 steps). ***)
    SAFE_SIM (1--17) THEN REPEAT CONJ_TAC THEN
    (MEM_PRESERVE ORELSE DISCHARGE_SAFETY_PROPERTY_TAC)] );;
