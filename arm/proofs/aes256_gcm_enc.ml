(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Functional correctness, constant-time and memory-safety proofs of the      *)
(* AES-256-GCM bulk encryption kernel aes256_gcm_enc.                         *)
(*                                                                           *)
(* Structured like the AES-128 proof in aes128_gcm_enc.ml: a single           *)
(* mid-pipeline loop invariant (swp_inv, asserted at the steady loop head     *)
(* pc+0x560) drives one ENSURES_WHILE, with fill and drain legs, a single-    *)
(* block tail loop, and separate legs for the loop_count = 0, 1 and 2 paths.  *)
(* The core theorem AES256_GCM_ENC_CORRECT (pc+0x2c to pc+0xee4) is wrapped   *)
(* into AES256_GCM_ENC_SUBROUTINE_CORRECT.                                    *)
(*                                                                           *)
(* Control-flow map (965 instructions):                                      *)
(*   preamble 0x2c..0xb0 ; cbz x1 @0xb0 -> 0xdd0 (loop_count = 0)            *)
(*   cmp x1,#1 ; b.eq @0xb8 -> 0xa90 (loop_count = 1: single iteration)      *)
(*   FILL 0xbc..0x558 ; sub x1,#2 ; cbz @0x55c -> 0x8a8 (loop_count = 2)     *)
(*   steady head 0x560 ; body .. cbnz x1 @0x8a4 -> 0x560                     *)
(*   DRAIN / postamble 0x8a8.. ; tail loop 0xde0 ; ret 0xf10                 *)
(*                                                                           *)
(* Structure:                                                                *)
(*   - the shared lemma substrate (counter, AES-256 and GHASH-reduce          *)
(*     reconstruction, the pipelined stepper, the safety closers) is in       *)
(*     aes_gcm_utils.ml; this file adds aes256_nist_cipher_block and the      *)
(*     kernel-specific closers;                                              *)
(*   - the machine code (AES256_GCM_ENC_EXEC) and the invariant swp_inv;      *)
(*   - the stepped legs FILL_TO_CBZ, BODYLEG, DRAINLEG_8A8, TAILLEG and       *)
(*     ITER1_LEG, each with its stepper and per-conjunct closers, plus the    *)
(*     one-instruction hops FILLLEG, LC2_PARTA and DRAINLEG that share the    *)
(*     fill and drain simulations between the loop_count paths;              *)
(*   - their composition BODY_DRAIN, MAINLEG, LEG_LC0, LEG_LC2 and            *)
(*     CORE_FROM88, the core theorem and the subroutine wrapper.             *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "common/fips197.ml";;
needs "common/polyval_ghash.ml";;
needs "common/ghash_nist_bridge.ml";;
needs "common/karatsuba_pmul.ml";;
needs "arm/proofs/aes_gcm_utils.ml";;

(* ------------------------------------------------------------------------- *)
(* The machine code.                                                         *)
(* ------------------------------------------------------------------------- *)

let aes256_gcm_enc_mc = define_assert_from_elf "aes256_gcm_enc_mc" "arm/aes_gcm/aes256_gcm_enc.o"
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
  0xa94e54b4;       (* arm_LDP X20 X21 X5 (Immediate_Offset (iword (&224))) *)
  0x3dc0007e;       (* arm_LDR Q30 X3 (Immediate_Offset (word 0)) *)
  0x4e200bde;       (* arm_REV64_VEC Q30 Q30 8 *)
  0xa940308b;       (* arm_LDP X11 X12 X4 (Immediate_Offset (iword (&0))) *)
  0xd360fd8d;       (* arm_LSR X13 X12 32 *)
  0x5ac009ad;       (* arm_REV W13 W13 *)
  0x2a0c018c;       (* arm_ORR W12 W12 W12 *)
  0xd344fde7;       (* arm_LSR X7 X15 4 *)
  0xd342fce1;       (* arm_LSR X1 X7 2 *)
  0x924004f0;       (* arm_AND X16 X7 (rvalue (word 3)) *)
  0x0f06e447;       (* arm_MOVI D7 (word 14033993530586874562) *)
  0x5f7854e7;       (* arm_SHL_VEC Q7 Q7 56 64 64 *)
  0x3dc000cc;       (* arm_LDR Q12 X6 (Immediate_Offset (word 0)) *)
  0x3dc008cd;       (* arm_LDR Q13 X6 (Immediate_Offset (word 32)) *)
  0x3dc004ce;       (* arm_LDR Q14 X6 (Immediate_Offset (word 16)) *)
  0x3dc00ccc;       (* arm_LDR Q12 X6 (Immediate_Offset (word 48)) *)
  0x3dc014cd;       (* arm_LDR Q13 X6 (Immediate_Offset (word 80)) *)
  0x3dc010ce;       (* arm_LDR Q14 X6 (Immediate_Offset (word 64)) *)
  0xb4006901;       (* arm_CBZ X1 (word 3360) *)
  0xf100043f;       (* arm_CMP X1 (rvalue (word 1)) *)
  0x54004ec0;       (* arm_BEQ (word 2520) *)
  0xa9414417;       (* arm_LDP X23 X17 X0 (Immediate_Offset (iword (&16))) *)
  0xa9424c08;       (* arm_LDP X8 X19 X0 (Immediate_Offset (iword (&32))) *)
  0x110005bc;       (* arm_ADD W28 W13 (rvalue (word 1)) *)
  0xca1402e7;       (* arm_EOR X7 X23 X20 *)
  0xa943781b;       (* arm_LDP X27 X30 X0 (Immediate_Offset (iword (&48))) *)
  0x110001bd;       (* arm_ADD W29 W13 (rvalue (word 0)) *)
  0xca14010a;       (* arm_EOR X10 X8 X20 *)
  0x5ac00bb8;       (* arm_REV W24 W29 *)
  0xca15026e;       (* arm_EOR X14 X19 X21 *)
  0x110009a8;       (* arm_ADD W8 W13 (rvalue (word 2)) *)
  0xaa188196;       (* arm_ORR X22 X12 (Shiftedreg X24 LSL 32) *)
  0xa90a5beb;       (* arm_STP X11 X22 SP (Immediate_Offset (iword (&160))) *)
  0xca1503da;       (* arm_EOR X26 X30 X21 *)
  0x5ac0091d;       (* arm_REV W29 W8 *)
  0x11000da8;       (* arm_ADD W8 W13 (rvalue (word 3)) *)
  0x110011ad;       (* arm_ADD W13 W13 (rvalue (word 4)) *)
  0xca140378;       (* arm_EOR X24 X27 X20 *)
  0x5ac00919;       (* arm_REV W25 W8 *)
  0xaa1d819e;       (* arm_ORR X30 X12 (Shiftedreg X29 LSL 32) *)
  0x5ac00b9d;       (* arm_REV W29 W28 *)
  0xaa198188;       (* arm_ORR X8 X12 (Shiftedreg X25 LSL 32) *)
  0xaa1d819d;       (* arm_ORR X29 X12 (Shiftedreg X29 LSL 32) *)
  0x3dc02be3;       (* arm_LDR Q3 SP (Immediate_Offset (word 160)) *)
  0xa90c7beb;       (* arm_STP X11 X30 SP (Immediate_Offset (iword (&192))) *)
  0xa90d23eb;       (* arm_STP X11 X8 SP (Immediate_Offset (iword (&208))) *)
  0xa90b77eb;       (* arm_STP X11 X29 SP (Immediate_Offset (iword (&176))) *)
  0x4e284a43;       (* arm_AESE Q3 Q18 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x3dc033e4;       (* arm_LDR Q4 SP (Immediate_Offset (word 192)) *)
  0xa90c3bea;       (* arm_STP X10 X14 SP (Immediate_Offset (iword (&192))) *)
  0x4e284a63;       (* arm_AESE Q3 Q19 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284a44;       (* arm_AESE Q4 Q18 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284a83;       (* arm_AESE Q3 Q20 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284a64;       (* arm_AESE Q4 Q19 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0xa8c42819;       (* arm_LDP X25 X10 X0 (Postimmediate_Offset (iword (&64))) *)
  0x4e284a84;       (* arm_AESE Q4 Q20 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x3dc037ff;       (* arm_LDR Q31 SP (Immediate_Offset (word 208)) *)
  0x4e284aa3;       (* arm_AESE Q3 Q21 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284aa4;       (* arm_AESE Q4 Q21 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284ac3;       (* arm_AESE Q3 Q22 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284a5f;       (* arm_AESE Q31 Q18 *)
  0x4e286bff;       (* arm_AESMC Q31 Q31 *)
  0xca15015d;       (* arm_EOR X29 X10 X21 *)
  0x3dc02fe8;       (* arm_LDR Q8 SP (Immediate_Offset (word 176)) *)
  0xca14032a;       (* arm_EOR X10 X25 X20 *)
  0x4e284ae3;       (* arm_AESE Q3 Q23 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284a7f;       (* arm_AESE Q31 Q19 *)
  0x4e286bff;       (* arm_AESMC Q31 Q31 *)
  0x4e284ac4;       (* arm_AESE Q4 Q22 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0xa90a77ea;       (* arm_STP X10 X29 SP (Immediate_Offset (iword (&160))) *)
  0xca15023d;       (* arm_EOR X29 X17 X21 *)
  0x4e284a48;       (* arm_AESE Q8 Q18 *)
  0x4e286908;       (* arm_AESMC Q8 Q8 *)
  0x4e284ae4;       (* arm_AESE Q4 Q23 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0xa90b77e7;       (* arm_STP X7 X29 SP (Immediate_Offset (iword (&176))) *)
  0x4e284b03;       (* arm_AESE Q3 Q24 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b04;       (* arm_AESE Q4 Q24 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x3dc014c2;       (* arm_LDR Q2 X6 (Immediate_Offset (word 80)) *)
  0x4e284b23;       (* arm_AESE Q3 Q25 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284a9f;       (* arm_AESE Q31 Q20 *)
  0x4e286bff;       (* arm_AESMC Q31 Q31 *)
  0x3dc000cd;       (* arm_LDR Q13 X6 (Immediate_Offset (word 0)) *)
  0x4e284b43;       (* arm_AESE Q3 Q26 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284abf;       (* arm_AESE Q31 Q21 *)
  0x4e286bff;       (* arm_AESMC Q31 Q31 *)
  0x4e284b63;       (* arm_AESE Q3 Q27 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284adf;       (* arm_AESE Q31 Q22 *)
  0x4e286bff;       (* arm_AESMC Q31 Q31 *)
  0x4e284b83;       (* arm_AESE Q3 Q28 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284aff;       (* arm_AESE Q31 Q23 *)
  0x4e286bff;       (* arm_AESMC Q31 Q31 *)
  0x3dc02be9;       (* arm_LDR Q9 SP (Immediate_Offset (word 160)) *)
  0x4e284b24;       (* arm_AESE Q4 Q25 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x3dc004cc;       (* arm_LDR Q12 X6 (Immediate_Offset (word 16)) *)
  0x4e2849e3;       (* arm_AESE Q3 Q15 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x3dc033ea;       (* arm_LDR Q10 SP (Immediate_Offset (word 192)) *)
  0x4e284b44;       (* arm_AESE Q4 Q26 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x3dc010c6;       (* arm_LDR Q6 X6 (Immediate_Offset (word 64)) *)
  0x4e284a03;       (* arm_AESE Q3 Q16 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b64;       (* arm_AESE Q4 Q27 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0xa9414417;       (* arm_LDP X23 X17 X0 (Immediate_Offset (iword (&16))) *)
  0x4e284a23;       (* arm_AESE Q3 Q17 *)
  0x4e284b1f;       (* arm_AESE Q31 Q24 *)
  0x4e286bff;       (* arm_AESMC Q31 Q31 *)
  0xa9424c08;       (* arm_LDP X8 X19 X0 (Immediate_Offset (iword (&32))) *)
  0x6e231d21;       (* arm_EOR_VEC Q1 Q9 Q3 128 *)
  0x4e284a68;       (* arm_AESE Q8 Q19 *)
  0x4e286908;       (* arm_AESMC Q8 Q8 *)
  0x110005bc;       (* arm_ADD W28 W13 (rvalue (word 1)) *)
  0x4e284b3f;       (* arm_AESE Q31 Q25 *)
  0x4e286bff;       (* arm_AESMC Q31 Q31 *)
  0xa90d6bf8;       (* arm_STP X24 X26 SP (Immediate_Offset (iword (&208))) *)
  0xca1402e7;       (* arm_EOR X7 X23 X20 *)
  0x4e284b84;       (* arm_AESE Q4 Q28 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e20082b;       (* arm_REV64_VEC Q11 Q1 8 *)
  0xa943781b;       (* arm_LDP X27 X30 X0 (Immediate_Offset (iword (&48))) *)
  0x110001bd;       (* arm_ADD W29 W13 (rvalue (word 0)) *)
  0x4e284a88;       (* arm_AESE Q8 Q20 *)
  0x4e286908;       (* arm_AESMC Q8 Q8 *)
  0xca14010a;       (* arm_EOR X10 X8 X20 *)
  0x4e284b5f;       (* arm_AESE Q31 Q26 *)
  0x4e286bff;       (* arm_AESMC Q31 Q31 *)
  0x6e3e1d69;       (* arm_EOR_VEC Q9 Q11 Q30 128 *)
  0x5ac00bb8;       (* arm_REV W24 W29 *)
  0xca15026e;       (* arm_EOR X14 X19 X21 *)
  0x3dc008de;       (* arm_LDR Q30 X6 (Immediate_Offset (word 32)) *)
  0x4e284aa8;       (* arm_AESE Q8 Q21 *)
  0x4e286908;       (* arm_AESMC Q8 Q8 *)
  0x110009a8;       (* arm_ADD W8 W13 (rvalue (word 2)) *)
  0xaa188196;       (* arm_ORR X22 X12 (Shiftedreg X24 LSL 32) *)
  0x4ee2e12b;       (* arm_PMULL2_VEC Q11 Q9 Q2 64 *)
  0x6e094125;       (* arm_EXT Q5 Q9 Q9 64 *)
  0xa90a5beb;       (* arm_STP X11 X22 SP (Immediate_Offset (iword (&160))) *)
  0x4e284ac8;       (* arm_AESE Q8 Q22 *)
  0x4e286908;       (* arm_AESMC Q8 Q8 *)
  0x4e284b7f;       (* arm_AESE Q31 Q27 *)
  0x4e286bff;       (* arm_AESMC Q31 Q31 *)
  0x3dc02fe0;       (* arm_LDR Q0 SP (Immediate_Offset (word 176)) *)
  0x4e2849e4;       (* arm_AESE Q4 Q15 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0xca1503da;       (* arm_EOR X26 X30 X21 *)
  0x4e284b9f;       (* arm_AESE Q31 Q28 *)
  0x4e286bff;       (* arm_AESMC Q31 Q31 *)
  0x4e284a04;       (* arm_AESE Q4 Q16 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x5ac0091d;       (* arm_REV W29 W8 *)
  0x4e284ae8;       (* arm_AESE Q8 Q23 *)
  0x4e286908;       (* arm_AESMC Q8 Q8 *)
  0x11000da8;       (* arm_ADD W8 W13 (rvalue (word 3)) *)
  0x110011ad;       (* arm_ADD W13 W13 (rvalue (word 4)) *)
  0x4e284a24;       (* arm_AESE Q4 Q17 *)
  0xca140378;       (* arm_EOR X24 X27 X20 *)
  0x4e284b08;       (* arm_AESE Q8 Q24 *)
  0x4e286908;       (* arm_AESMC Q8 Q8 *)
  0x5ac00919;       (* arm_REV W25 W8 *)
  0x4e2849ff;       (* arm_AESE Q31 Q15 *)
  0x4e286bff;       (* arm_AESMC Q31 Q31 *)
  0x6e241d4a;       (* arm_EOR_VEC Q10 Q10 Q4 128 *)
  0xaa1d819e;       (* arm_ORR X30 X12 (Shiftedreg X29 LSL 32) *)
  0x5ac00b9d;       (* arm_REV W29 W28 *)
  0x3dc037e4;       (* arm_LDR Q4 SP (Immediate_Offset (word 208)) *)
  0x4e284b28;       (* arm_AESE Q8 Q25 *)
  0x4e286908;       (* arm_AESMC Q8 Q8 *)
  0xaa198188;       (* arm_ORR X8 X12 (Shiftedreg X25 LSL 32) *)
  0x4e284a1f;       (* arm_AESE Q31 Q16 *)
  0x4e286bff;       (* arm_AESMC Q31 Q31 *)
  0x6e291ca5;       (* arm_EOR_VEC Q5 Q5 Q9 128 *)
  0xaa1d819d;       (* arm_ORR X29 X12 (Shiftedreg X29 LSL 32) *)
  0x3d80084a;       (* arm_STR Q10 X2 (Immediate_Offset (word 32)) *)
  0x4e284b48;       (* arm_AESE Q8 Q26 *)
  0x4e286908;       (* arm_AESMC Q8 Q8 *)
  0x4e284a3f;       (* arm_AESE Q31 Q17 *)
  0x3dc02be3;       (* arm_LDR Q3 SP (Immediate_Offset (word 160)) *)
  0x0ee2e13d;       (* arm_PMULL_VEC Q29 Q9 Q2 64 *)
  0x4e200942;       (* arm_REV64_VEC Q2 Q10 8 *)
  0xa90c7beb;       (* arm_STP X11 X30 SP (Immediate_Offset (iword (&192))) *)
  0x6e3f1c84;       (* arm_EOR_VEC Q4 Q4 Q31 128 *)
  0x4e284b68;       (* arm_AESE Q8 Q27 *)
  0x4e286908;       (* arm_AESMC Q8 Q8 *)
  0x0efee04a;       (* arm_PMULL_VEC Q10 Q2 Q30 64 *)
  0x6e02404e;       (* arm_EXT Q14 Q2 Q2 64 *)
  0xa90d23eb;       (* arm_STP X11 X8 SP (Immediate_Offset (iword (&208))) *)
  0x4e200889;       (* arm_REV64_VEC Q9 Q4 8 *)
  0x4e284b88;       (* arm_AESE Q8 Q28 *)
  0x4e286908;       (* arm_AESMC Q8 Q8 *)
  0x4efee05f;       (* arm_PMULL2_VEC Q31 Q2 Q30 64 *)
  0x6e221dce;       (* arm_EOR_VEC Q14 Q14 Q2 128 *)
  0x3d800c44;       (* arm_STR Q4 X2 (Immediate_Offset (word 48)) *)
  0x4e2849e8;       (* arm_AESE Q8 Q15 *)
  0x4e286908;       (* arm_AESMC Q8 Q8 *)
  0x5e180524;       (* arm_DUP_ELEM_SCALAR Q4 Q9 1 64 *)
  0x4eece1ce;       (* arm_PMULL2_VEC Q14 Q14 Q12 64 *)
  0xa90b77eb;       (* arm_STP X11 X29 SP (Immediate_Offset (iword (&176))) *)
  0x4e284a08;       (* arm_AESE Q8 Q16 *)
  0x4e286908;       (* arm_AESMC Q8 Q8 *)
  0x2e291c9e;       (* arm_EOR_VEC Q30 Q4 Q9 64 *)
  0x4e284a43;       (* arm_AESE Q3 Q18 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284a28;       (* arm_AESE Q8 Q17 *)
  0x3dc033e4;       (* arm_LDR Q4 SP (Immediate_Offset (word 192)) *)
  0x0eece3de;       (* arm_PMULL_VEC Q30 Q30 Q12 64 *)
  0xa90c3bea;       (* arm_STP X10 X14 SP (Immediate_Offset (iword (&192))) *)
  0x4eede122;       (* arm_PMULL2_VEC Q2 Q9 Q13 64 *)
  0x6e281c0c;       (* arm_EOR_VEC Q12 Q0 Q8 128 *)
  0x3dc00cc8;       (* arm_LDR Q8 X6 (Immediate_Offset (word 48)) *)
  0x4e284a63;       (* arm_AESE Q3 Q19 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x3d80044c;       (* arm_STR Q12 X2 (Immediate_Offset (word 16)) *)
  0x4e284a44;       (* arm_AESE Q4 Q18 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x3c840441;       (* arm_STR Q1 X2 (Postimmediate_Offset (word 64)) *)
  0x4e284a83;       (* arm_AESE Q3 Q20 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x6e2e1fde;       (* arm_EOR_VEC Q30 Q30 Q14 128 *)
  0x4e284a64;       (* arm_AESE Q4 Q19 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0xa8c42819;       (* arm_LDP X25 X10 X0 (Postimmediate_Offset (iword (&64))) *)
  0x4e20098e;       (* arm_REV64_VEC Q14 Q12 8 *)
  0x0eede12c;       (* arm_PMULL_VEC Q12 Q9 Q13 64 *)
  0x6e3f1c49;       (* arm_EOR_VEC Q9 Q2 Q31 128 *)
  0x4e284a84;       (* arm_AESE Q4 Q20 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x0ee8e1c2;       (* arm_PMULL_VEC Q2 Q14 Q8 64 *)
  0x3dc037ff;       (* arm_LDR Q31 SP (Immediate_Offset (word 208)) *)
  0x6e2a1d8d;       (* arm_EOR_VEC Q13 Q12 Q10 128 *)
  0x4e284aa3;       (* arm_AESE Q3 Q21 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4ee8e1ca;       (* arm_PMULL2_VEC Q10 Q14 Q8 64 *)
  0x5e1805c0;       (* arm_DUP_ELEM_SCALAR Q0 Q14 1 64 *)
  0x6e221da8;       (* arm_EOR_VEC Q8 Q13 Q2 128 *)
  0x4e284aa4;       (* arm_AESE Q4 Q21 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x2e2e1c0c;       (* arm_EOR_VEC Q12 Q0 Q14 64 *)
  0x4e284ac3;       (* arm_AESE Q3 Q22 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x6e2a1d20;       (* arm_EOR_VEC Q0 Q9 Q10 128 *)
  0x4e284a5f;       (* arm_AESE Q31 Q18 *)
  0x4e286bff;       (* arm_AESMC Q31 Q31 *)
  0x6e3d1d0a;       (* arm_EOR_VEC Q10 Q8 Q29 128 *)
  0x4ee6e0a1;       (* arm_PMULL2_VEC Q1 Q5 Q6 64 *)
  0xca15015d;       (* arm_EOR X29 X10 X21 *)
  0x0ee6e18d;       (* arm_PMULL_VEC Q13 Q12 Q6 64 *)
  0x3dc02fe8;       (* arm_LDR Q8 SP (Immediate_Offset (word 176)) *)
  0xca14032a;       (* arm_EOR X10 X25 X20 *)
  0x6e2b1c0c;       (* arm_EOR_VEC Q12 Q0 Q11 128 *)
  0x4e284ae3;       (* arm_AESE Q3 Q23 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284a7f;       (* arm_AESE Q31 Q19 *)
  0x4e286bff;       (* arm_AESMC Q31 Q31 *)
  0x6e2c1d45;       (* arm_EOR_VEC Q5 Q10 Q12 128 *)
  0x0ee7e180;       (* arm_PMULL_VEC Q0 Q12 Q7 64 *)
  0x6e2d1fc2;       (* arm_EOR_VEC Q2 Q30 Q13 128 *)
  0x4e284ac4;       (* arm_AESE Q4 Q22 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0xa90a77ea;       (* arm_STP X10 X29 SP (Immediate_Offset (iword (&160))) *)
  0xca15023d;       (* arm_EOR X29 X17 X21 *)
  0x6e0c418b;       (* arm_EXT Q11 Q12 Q12 64 *)
  0x4e284a48;       (* arm_AESE Q8 Q18 *)
  0x4e286908;       (* arm_AESMC Q8 Q8 *)
  0x6e211c4e;       (* arm_EOR_VEC Q14 Q2 Q1 128 *)
  0x4e284ae4;       (* arm_AESE Q4 Q23 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0xa90b77e7;       (* arm_STP X7 X29 SP (Immediate_Offset (iword (&176))) *)
  0x6e201d60;       (* arm_EOR_VEC Q0 Q11 Q0 128 *)
  0x4e284b03;       (* arm_AESE Q3 Q24 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x6e251dc5;       (* arm_EOR_VEC Q5 Q14 Q5 128 *)
  0x4e284b04;       (* arm_AESE Q4 Q24 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x3dc014c2;       (* arm_LDR Q2 X6 (Immediate_Offset (word 80)) *)
  0x4e284b23;       (* arm_AESE Q3 Q25 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x6e201cab;       (* arm_EOR_VEC Q11 Q5 Q0 128 *)
  0x4e284a9f;       (* arm_AESE Q31 Q20 *)
  0x4e286bff;       (* arm_AESMC Q31 Q31 *)
  0x3dc000cd;       (* arm_LDR Q13 X6 (Immediate_Offset (word 0)) *)
  0x4e284b43;       (* arm_AESE Q3 Q26 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x0ee7e161;       (* arm_PMULL_VEC Q1 Q11 Q7 64 *)
  0x6e0b416c;       (* arm_EXT Q12 Q11 Q11 64 *)
  0x4e284abf;       (* arm_AESE Q31 Q21 *)
  0x4e286bff;       (* arm_AESMC Q31 Q31 *)
  0x6e211d4b;       (* arm_EOR_VEC Q11 Q10 Q1 128 *)
  0x4e284b63;       (* arm_AESE Q3 Q27 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284adf;       (* arm_AESE Q31 Q22 *)
  0x4e286bff;       (* arm_AESMC Q31 Q31 *)
  0x6e2c1d7d;       (* arm_EOR_VEC Q29 Q11 Q12 128 *)
  0x4e284b83;       (* arm_AESE Q3 Q28 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284aff;       (* arm_AESE Q31 Q23 *)
  0x4e286bff;       (* arm_AESMC Q31 Q31 *)
  0xd1000821;       (* arm_SUB X1 X1 (rvalue (word 2)) *)
  0xb4001a61;       (* arm_CBZ X1 (word 844) *)
  0x3dc02be9;       (* arm_LDR Q9 SP (Immediate_Offset (word 160)) *)
  0x4e284b24;       (* arm_AESE Q4 Q25 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x3dc004cc;       (* arm_LDR Q12 X6 (Immediate_Offset (word 16)) *)
  0x4e2849e3;       (* arm_AESE Q3 Q15 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x3dc033ea;       (* arm_LDR Q10 SP (Immediate_Offset (word 192)) *)
  0x4e284b44;       (* arm_AESE Q4 Q26 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x3dc010c6;       (* arm_LDR Q6 X6 (Immediate_Offset (word 64)) *)
  0x4e284a03;       (* arm_AESE Q3 Q16 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b64;       (* arm_AESE Q4 Q27 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0xa9414417;       (* arm_LDP X23 X17 X0 (Immediate_Offset (iword (&16))) *)
  0x4e284a23;       (* arm_AESE Q3 Q17 *)
  0x6e1d43be;       (* arm_EXT Q30 Q29 Q29 64 *)
  0x4e284b1f;       (* arm_AESE Q31 Q24 *)
  0x4e286bff;       (* arm_AESMC Q31 Q31 *)
  0xa9424c08;       (* arm_LDP X8 X19 X0 (Immediate_Offset (iword (&32))) *)
  0x6e231d21;       (* arm_EOR_VEC Q1 Q9 Q3 128 *)
  0x4e284a68;       (* arm_AESE Q8 Q19 *)
  0x4e286908;       (* arm_AESMC Q8 Q8 *)
  0x110005bc;       (* arm_ADD W28 W13 (rvalue (word 1)) *)
  0x4e284b3f;       (* arm_AESE Q31 Q25 *)
  0x4e286bff;       (* arm_AESMC Q31 Q31 *)
  0xa90d6bf8;       (* arm_STP X24 X26 SP (Immediate_Offset (iword (&208))) *)
  0xca1402e7;       (* arm_EOR X7 X23 X20 *)
  0x4e284b84;       (* arm_AESE Q4 Q28 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e20082b;       (* arm_REV64_VEC Q11 Q1 8 *)
  0xa943781b;       (* arm_LDP X27 X30 X0 (Immediate_Offset (iword (&48))) *)
  0x110001bd;       (* arm_ADD W29 W13 (rvalue (word 0)) *)
  0x4e284a88;       (* arm_AESE Q8 Q20 *)
  0x4e286908;       (* arm_AESMC Q8 Q8 *)
  0xca14010a;       (* arm_EOR X10 X8 X20 *)
  0x4e284b5f;       (* arm_AESE Q31 Q26 *)
  0x4e286bff;       (* arm_AESMC Q31 Q31 *)
  0x6e3e1d69;       (* arm_EOR_VEC Q9 Q11 Q30 128 *)
  0x5ac00bb8;       (* arm_REV W24 W29 *)
  0xca15026e;       (* arm_EOR X14 X19 X21 *)
  0x3dc008de;       (* arm_LDR Q30 X6 (Immediate_Offset (word 32)) *)
  0x4e284aa8;       (* arm_AESE Q8 Q21 *)
  0x4e286908;       (* arm_AESMC Q8 Q8 *)
  0x110009a8;       (* arm_ADD W8 W13 (rvalue (word 2)) *)
  0xaa188196;       (* arm_ORR X22 X12 (Shiftedreg X24 LSL 32) *)
  0x4ee2e12b;       (* arm_PMULL2_VEC Q11 Q9 Q2 64 *)
  0x6e094125;       (* arm_EXT Q5 Q9 Q9 64 *)
  0xa90a5beb;       (* arm_STP X11 X22 SP (Immediate_Offset (iword (&160))) *)
  0x4e284ac8;       (* arm_AESE Q8 Q22 *)
  0x4e286908;       (* arm_AESMC Q8 Q8 *)
  0x4e284b7f;       (* arm_AESE Q31 Q27 *)
  0x4e286bff;       (* arm_AESMC Q31 Q31 *)
  0x3dc02fe0;       (* arm_LDR Q0 SP (Immediate_Offset (word 176)) *)
  0x4e2849e4;       (* arm_AESE Q4 Q15 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0xca1503da;       (* arm_EOR X26 X30 X21 *)
  0x4e284b9f;       (* arm_AESE Q31 Q28 *)
  0x4e286bff;       (* arm_AESMC Q31 Q31 *)
  0x4e284a04;       (* arm_AESE Q4 Q16 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x5ac0091d;       (* arm_REV W29 W8 *)
  0x4e284ae8;       (* arm_AESE Q8 Q23 *)
  0x4e286908;       (* arm_AESMC Q8 Q8 *)
  0x11000da8;       (* arm_ADD W8 W13 (rvalue (word 3)) *)
  0x110011ad;       (* arm_ADD W13 W13 (rvalue (word 4)) *)
  0x4e284a24;       (* arm_AESE Q4 Q17 *)
  0xca140378;       (* arm_EOR X24 X27 X20 *)
  0x4e284b08;       (* arm_AESE Q8 Q24 *)
  0x4e286908;       (* arm_AESMC Q8 Q8 *)
  0x5ac00919;       (* arm_REV W25 W8 *)
  0x4e2849ff;       (* arm_AESE Q31 Q15 *)
  0x4e286bff;       (* arm_AESMC Q31 Q31 *)
  0x6e241d4a;       (* arm_EOR_VEC Q10 Q10 Q4 128 *)
  0xaa1d819e;       (* arm_ORR X30 X12 (Shiftedreg X29 LSL 32) *)
  0x5ac00b9d;       (* arm_REV W29 W28 *)
  0x3dc037e4;       (* arm_LDR Q4 SP (Immediate_Offset (word 208)) *)
  0x4e284b28;       (* arm_AESE Q8 Q25 *)
  0x4e286908;       (* arm_AESMC Q8 Q8 *)
  0xaa198188;       (* arm_ORR X8 X12 (Shiftedreg X25 LSL 32) *)
  0x4e284a1f;       (* arm_AESE Q31 Q16 *)
  0x4e286bff;       (* arm_AESMC Q31 Q31 *)
  0x6e291ca5;       (* arm_EOR_VEC Q5 Q5 Q9 128 *)
  0xaa1d819d;       (* arm_ORR X29 X12 (Shiftedreg X29 LSL 32) *)
  0x3d80084a;       (* arm_STR Q10 X2 (Immediate_Offset (word 32)) *)
  0x4e284b48;       (* arm_AESE Q8 Q26 *)
  0x4e286908;       (* arm_AESMC Q8 Q8 *)
  0x4e284a3f;       (* arm_AESE Q31 Q17 *)
  0x3dc02be3;       (* arm_LDR Q3 SP (Immediate_Offset (word 160)) *)
  0x0ee2e13d;       (* arm_PMULL_VEC Q29 Q9 Q2 64 *)
  0x4e200942;       (* arm_REV64_VEC Q2 Q10 8 *)
  0xa90c7beb;       (* arm_STP X11 X30 SP (Immediate_Offset (iword (&192))) *)
  0x6e3f1c84;       (* arm_EOR_VEC Q4 Q4 Q31 128 *)
  0x4e284b68;       (* arm_AESE Q8 Q27 *)
  0x4e286908;       (* arm_AESMC Q8 Q8 *)
  0x0efee04a;       (* arm_PMULL_VEC Q10 Q2 Q30 64 *)
  0x6e02404e;       (* arm_EXT Q14 Q2 Q2 64 *)
  0xa90d23eb;       (* arm_STP X11 X8 SP (Immediate_Offset (iword (&208))) *)
  0x4e200889;       (* arm_REV64_VEC Q9 Q4 8 *)
  0x4e284b88;       (* arm_AESE Q8 Q28 *)
  0x4e286908;       (* arm_AESMC Q8 Q8 *)
  0x4efee05f;       (* arm_PMULL2_VEC Q31 Q2 Q30 64 *)
  0x6e221dce;       (* arm_EOR_VEC Q14 Q14 Q2 128 *)
  0x3d800c44;       (* arm_STR Q4 X2 (Immediate_Offset (word 48)) *)
  0x4e2849e8;       (* arm_AESE Q8 Q15 *)
  0x4e286908;       (* arm_AESMC Q8 Q8 *)
  0x5e180524;       (* arm_DUP_ELEM_SCALAR Q4 Q9 1 64 *)
  0x4eece1ce;       (* arm_PMULL2_VEC Q14 Q14 Q12 64 *)
  0xa90b77eb;       (* arm_STP X11 X29 SP (Immediate_Offset (iword (&176))) *)
  0x4e284a08;       (* arm_AESE Q8 Q16 *)
  0x4e286908;       (* arm_AESMC Q8 Q8 *)
  0x2e291c9e;       (* arm_EOR_VEC Q30 Q4 Q9 64 *)
  0x4e284a43;       (* arm_AESE Q3 Q18 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284a28;       (* arm_AESE Q8 Q17 *)
  0x3dc033e4;       (* arm_LDR Q4 SP (Immediate_Offset (word 192)) *)
  0x0eece3de;       (* arm_PMULL_VEC Q30 Q30 Q12 64 *)
  0xa90c3bea;       (* arm_STP X10 X14 SP (Immediate_Offset (iword (&192))) *)
  0x4eede122;       (* arm_PMULL2_VEC Q2 Q9 Q13 64 *)
  0x6e281c0c;       (* arm_EOR_VEC Q12 Q0 Q8 128 *)
  0x3dc00cc8;       (* arm_LDR Q8 X6 (Immediate_Offset (word 48)) *)
  0x4e284a63;       (* arm_AESE Q3 Q19 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x3d80044c;       (* arm_STR Q12 X2 (Immediate_Offset (word 16)) *)
  0x4e284a44;       (* arm_AESE Q4 Q18 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x3c840441;       (* arm_STR Q1 X2 (Postimmediate_Offset (word 64)) *)
  0x4e284a83;       (* arm_AESE Q3 Q20 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x6e2e1fde;       (* arm_EOR_VEC Q30 Q30 Q14 128 *)
  0x4e284a64;       (* arm_AESE Q4 Q19 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0xa8c42819;       (* arm_LDP X25 X10 X0 (Postimmediate_Offset (iword (&64))) *)
  0x4e20098e;       (* arm_REV64_VEC Q14 Q12 8 *)
  0x0eede12c;       (* arm_PMULL_VEC Q12 Q9 Q13 64 *)
  0x6e3f1c49;       (* arm_EOR_VEC Q9 Q2 Q31 128 *)
  0x4e284a84;       (* arm_AESE Q4 Q20 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x0ee8e1c2;       (* arm_PMULL_VEC Q2 Q14 Q8 64 *)
  0x3dc037ff;       (* arm_LDR Q31 SP (Immediate_Offset (word 208)) *)
  0x6e2a1d8d;       (* arm_EOR_VEC Q13 Q12 Q10 128 *)
  0x4e284aa3;       (* arm_AESE Q3 Q21 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4ee8e1ca;       (* arm_PMULL2_VEC Q10 Q14 Q8 64 *)
  0x5e1805c0;       (* arm_DUP_ELEM_SCALAR Q0 Q14 1 64 *)
  0x6e221da8;       (* arm_EOR_VEC Q8 Q13 Q2 128 *)
  0x4e284aa4;       (* arm_AESE Q4 Q21 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x2e2e1c0c;       (* arm_EOR_VEC Q12 Q0 Q14 64 *)
  0x4e284ac3;       (* arm_AESE Q3 Q22 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x6e2a1d20;       (* arm_EOR_VEC Q0 Q9 Q10 128 *)
  0x4e284a5f;       (* arm_AESE Q31 Q18 *)
  0x4e286bff;       (* arm_AESMC Q31 Q31 *)
  0x6e3d1d0a;       (* arm_EOR_VEC Q10 Q8 Q29 128 *)
  0x4ee6e0a1;       (* arm_PMULL2_VEC Q1 Q5 Q6 64 *)
  0xca15015d;       (* arm_EOR X29 X10 X21 *)
  0x0ee6e18d;       (* arm_PMULL_VEC Q13 Q12 Q6 64 *)
  0x3dc02fe8;       (* arm_LDR Q8 SP (Immediate_Offset (word 176)) *)
  0xca14032a;       (* arm_EOR X10 X25 X20 *)
  0x6e2b1c0c;       (* arm_EOR_VEC Q12 Q0 Q11 128 *)
  0x4e284ae3;       (* arm_AESE Q3 Q23 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284a7f;       (* arm_AESE Q31 Q19 *)
  0x4e286bff;       (* arm_AESMC Q31 Q31 *)
  0x6e2c1d45;       (* arm_EOR_VEC Q5 Q10 Q12 128 *)
  0x0ee7e180;       (* arm_PMULL_VEC Q0 Q12 Q7 64 *)
  0x6e2d1fc2;       (* arm_EOR_VEC Q2 Q30 Q13 128 *)
  0x4e284ac4;       (* arm_AESE Q4 Q22 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0xa90a77ea;       (* arm_STP X10 X29 SP (Immediate_Offset (iword (&160))) *)
  0xca15023d;       (* arm_EOR X29 X17 X21 *)
  0x6e0c418b;       (* arm_EXT Q11 Q12 Q12 64 *)
  0x4e284a48;       (* arm_AESE Q8 Q18 *)
  0x4e286908;       (* arm_AESMC Q8 Q8 *)
  0x6e211c4e;       (* arm_EOR_VEC Q14 Q2 Q1 128 *)
  0x4e284ae4;       (* arm_AESE Q4 Q23 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0xa90b77e7;       (* arm_STP X7 X29 SP (Immediate_Offset (iword (&176))) *)
  0x6e201d60;       (* arm_EOR_VEC Q0 Q11 Q0 128 *)
  0x4e284b03;       (* arm_AESE Q3 Q24 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x6e251dc5;       (* arm_EOR_VEC Q5 Q14 Q5 128 *)
  0x4e284b04;       (* arm_AESE Q4 Q24 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x3dc014c2;       (* arm_LDR Q2 X6 (Immediate_Offset (word 80)) *)
  0x4e284b23;       (* arm_AESE Q3 Q25 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x6e201cab;       (* arm_EOR_VEC Q11 Q5 Q0 128 *)
  0x4e284a9f;       (* arm_AESE Q31 Q20 *)
  0x4e286bff;       (* arm_AESMC Q31 Q31 *)
  0x3dc000cd;       (* arm_LDR Q13 X6 (Immediate_Offset (word 0)) *)
  0x4e284b43;       (* arm_AESE Q3 Q26 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x0ee7e161;       (* arm_PMULL_VEC Q1 Q11 Q7 64 *)
  0x6e0b416c;       (* arm_EXT Q12 Q11 Q11 64 *)
  0x4e284abf;       (* arm_AESE Q31 Q21 *)
  0x4e286bff;       (* arm_AESMC Q31 Q31 *)
  0x6e211d4b;       (* arm_EOR_VEC Q11 Q10 Q1 128 *)
  0x4e284b63;       (* arm_AESE Q3 Q27 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284adf;       (* arm_AESE Q31 Q22 *)
  0x4e286bff;       (* arm_AESMC Q31 Q31 *)
  0x6e2c1d7d;       (* arm_EOR_VEC Q29 Q11 Q12 128 *)
  0x4e284b83;       (* arm_AESE Q3 Q28 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284aff;       (* arm_AESE Q31 Q23 *)
  0x4e286bff;       (* arm_AESMC Q31 Q31 *)
  0xd1000421;       (* arm_SUB X1 X1 (rvalue (word 1)) *)
  0xb5ffe5e1;       (* arm_CBNZ X1 (word 2096316) *)
  0x3dc02be9;       (* arm_LDR Q9 SP (Immediate_Offset (word 160)) *)
  0x4e284b24;       (* arm_AESE Q4 Q25 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x3dc004cc;       (* arm_LDR Q12 X6 (Immediate_Offset (word 16)) *)
  0x4e2849e3;       (* arm_AESE Q3 Q15 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x3dc033ea;       (* arm_LDR Q10 SP (Immediate_Offset (word 192)) *)
  0x4e284b44;       (* arm_AESE Q4 Q26 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x3dc010c6;       (* arm_LDR Q6 X6 (Immediate_Offset (word 64)) *)
  0x4e284a03;       (* arm_AESE Q3 Q16 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b64;       (* arm_AESE Q4 Q27 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284a23;       (* arm_AESE Q3 Q17 *)
  0x6e1d43be;       (* arm_EXT Q30 Q29 Q29 64 *)
  0x4e284b1f;       (* arm_AESE Q31 Q24 *)
  0x4e286bff;       (* arm_AESMC Q31 Q31 *)
  0x6e231d21;       (* arm_EOR_VEC Q1 Q9 Q3 128 *)
  0x4e284a68;       (* arm_AESE Q8 Q19 *)
  0x4e286908;       (* arm_AESMC Q8 Q8 *)
  0x4e284b3f;       (* arm_AESE Q31 Q25 *)
  0x4e286bff;       (* arm_AESMC Q31 Q31 *)
  0xa90d6bf8;       (* arm_STP X24 X26 SP (Immediate_Offset (iword (&208))) *)
  0x4e284b84;       (* arm_AESE Q4 Q28 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e20082b;       (* arm_REV64_VEC Q11 Q1 8 *)
  0x4e284a88;       (* arm_AESE Q8 Q20 *)
  0x4e286908;       (* arm_AESMC Q8 Q8 *)
  0x4e284b5f;       (* arm_AESE Q31 Q26 *)
  0x4e286bff;       (* arm_AESMC Q31 Q31 *)
  0x6e3e1d69;       (* arm_EOR_VEC Q9 Q11 Q30 128 *)
  0x3dc008de;       (* arm_LDR Q30 X6 (Immediate_Offset (word 32)) *)
  0x4e284aa8;       (* arm_AESE Q8 Q21 *)
  0x4e286908;       (* arm_AESMC Q8 Q8 *)
  0x4ee2e12b;       (* arm_PMULL2_VEC Q11 Q9 Q2 64 *)
  0x6e094125;       (* arm_EXT Q5 Q9 Q9 64 *)
  0x4e284ac8;       (* arm_AESE Q8 Q22 *)
  0x4e286908;       (* arm_AESMC Q8 Q8 *)
  0x4e284b7f;       (* arm_AESE Q31 Q27 *)
  0x4e286bff;       (* arm_AESMC Q31 Q31 *)
  0x3dc02fe0;       (* arm_LDR Q0 SP (Immediate_Offset (word 176)) *)
  0x4e2849e4;       (* arm_AESE Q4 Q15 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b9f;       (* arm_AESE Q31 Q28 *)
  0x4e286bff;       (* arm_AESMC Q31 Q31 *)
  0x4e284a04;       (* arm_AESE Q4 Q16 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284ae8;       (* arm_AESE Q8 Q23 *)
  0x4e286908;       (* arm_AESMC Q8 Q8 *)
  0x4e284a24;       (* arm_AESE Q4 Q17 *)
  0x4e284b08;       (* arm_AESE Q8 Q24 *)
  0x4e286908;       (* arm_AESMC Q8 Q8 *)
  0x4e2849ff;       (* arm_AESE Q31 Q15 *)
  0x4e286bff;       (* arm_AESMC Q31 Q31 *)
  0x6e241d4a;       (* arm_EOR_VEC Q10 Q10 Q4 128 *)
  0x3dc037e4;       (* arm_LDR Q4 SP (Immediate_Offset (word 208)) *)
  0x4e284b28;       (* arm_AESE Q8 Q25 *)
  0x4e286908;       (* arm_AESMC Q8 Q8 *)
  0x4e284a1f;       (* arm_AESE Q31 Q16 *)
  0x4e286bff;       (* arm_AESMC Q31 Q31 *)
  0x6e291ca5;       (* arm_EOR_VEC Q5 Q5 Q9 128 *)
  0x3d80084a;       (* arm_STR Q10 X2 (Immediate_Offset (word 32)) *)
  0x4e284b48;       (* arm_AESE Q8 Q26 *)
  0x4e286908;       (* arm_AESMC Q8 Q8 *)
  0x4e284a3f;       (* arm_AESE Q31 Q17 *)
  0x0ee2e13d;       (* arm_PMULL_VEC Q29 Q9 Q2 64 *)
  0x4e200942;       (* arm_REV64_VEC Q2 Q10 8 *)
  0x6e3f1c84;       (* arm_EOR_VEC Q4 Q4 Q31 128 *)
  0x4e284b68;       (* arm_AESE Q8 Q27 *)
  0x4e286908;       (* arm_AESMC Q8 Q8 *)
  0x0efee04a;       (* arm_PMULL_VEC Q10 Q2 Q30 64 *)
  0x6e02404e;       (* arm_EXT Q14 Q2 Q2 64 *)
  0x4e200889;       (* arm_REV64_VEC Q9 Q4 8 *)
  0x4e284b88;       (* arm_AESE Q8 Q28 *)
  0x4e286908;       (* arm_AESMC Q8 Q8 *)
  0x4efee05f;       (* arm_PMULL2_VEC Q31 Q2 Q30 64 *)
  0x6e221dce;       (* arm_EOR_VEC Q14 Q14 Q2 128 *)
  0x3d800c44;       (* arm_STR Q4 X2 (Immediate_Offset (word 48)) *)
  0x4e2849e8;       (* arm_AESE Q8 Q15 *)
  0x4e286908;       (* arm_AESMC Q8 Q8 *)
  0x5e180524;       (* arm_DUP_ELEM_SCALAR Q4 Q9 1 64 *)
  0x4eece1ce;       (* arm_PMULL2_VEC Q14 Q14 Q12 64 *)
  0x4e284a08;       (* arm_AESE Q8 Q16 *)
  0x4e286908;       (* arm_AESMC Q8 Q8 *)
  0x2e291c9e;       (* arm_EOR_VEC Q30 Q4 Q9 64 *)
  0x4e284a28;       (* arm_AESE Q8 Q17 *)
  0x0eece3de;       (* arm_PMULL_VEC Q30 Q30 Q12 64 *)
  0x4eede122;       (* arm_PMULL2_VEC Q2 Q9 Q13 64 *)
  0x6e281c0c;       (* arm_EOR_VEC Q12 Q0 Q8 128 *)
  0x3dc00cc8;       (* arm_LDR Q8 X6 (Immediate_Offset (word 48)) *)
  0x3d80044c;       (* arm_STR Q12 X2 (Immediate_Offset (word 16)) *)
  0x3c840441;       (* arm_STR Q1 X2 (Postimmediate_Offset (word 64)) *)
  0x6e2e1fde;       (* arm_EOR_VEC Q30 Q30 Q14 128 *)
  0x4e20098e;       (* arm_REV64_VEC Q14 Q12 8 *)
  0x0eede12c;       (* arm_PMULL_VEC Q12 Q9 Q13 64 *)
  0x6e3f1c49;       (* arm_EOR_VEC Q9 Q2 Q31 128 *)
  0x0ee8e1c2;       (* arm_PMULL_VEC Q2 Q14 Q8 64 *)
  0x6e2a1d8d;       (* arm_EOR_VEC Q13 Q12 Q10 128 *)
  0x4ee8e1ca;       (* arm_PMULL2_VEC Q10 Q14 Q8 64 *)
  0x5e1805c0;       (* arm_DUP_ELEM_SCALAR Q0 Q14 1 64 *)
  0x6e221da8;       (* arm_EOR_VEC Q8 Q13 Q2 128 *)
  0x2e2e1c0c;       (* arm_EOR_VEC Q12 Q0 Q14 64 *)
  0x6e2a1d20;       (* arm_EOR_VEC Q0 Q9 Q10 128 *)
  0x6e3d1d0a;       (* arm_EOR_VEC Q10 Q8 Q29 128 *)
  0x4ee6e0a1;       (* arm_PMULL2_VEC Q1 Q5 Q6 64 *)
  0x0ee6e18d;       (* arm_PMULL_VEC Q13 Q12 Q6 64 *)
  0x6e2b1c0c;       (* arm_EOR_VEC Q12 Q0 Q11 128 *)
  0x6e2c1d45;       (* arm_EOR_VEC Q5 Q10 Q12 128 *)
  0x0ee7e180;       (* arm_PMULL_VEC Q0 Q12 Q7 64 *)
  0x6e2d1fc2;       (* arm_EOR_VEC Q2 Q30 Q13 128 *)
  0x6e0c418b;       (* arm_EXT Q11 Q12 Q12 64 *)
  0x6e211c4e;       (* arm_EOR_VEC Q14 Q2 Q1 128 *)
  0x6e201d60;       (* arm_EOR_VEC Q0 Q11 Q0 128 *)
  0x6e251dc5;       (* arm_EOR_VEC Q5 Q14 Q5 128 *)
  0x6e201cab;       (* arm_EOR_VEC Q11 Q5 Q0 128 *)
  0x0ee7e161;       (* arm_PMULL_VEC Q1 Q11 Q7 64 *)
  0x6e0b416c;       (* arm_EXT Q12 Q11 Q11 64 *)
  0x6e211d4b;       (* arm_EOR_VEC Q11 Q10 Q1 128 *)
  0x6e2c1d7d;       (* arm_EOR_VEC Q29 Q11 Q12 128 *)
  0x6e1d43be;       (* arm_EXT Q30 Q29 Q29 64 *)
  0x140000d1;       (* arm_B (word 836) *)
  0x3dc010cd;       (* arm_LDR Q13 X6 (Immediate_Offset (word 64)) *)
  0xa943441b;       (* arm_LDP X27 X17 X0 (Immediate_Offset (iword (&48))) *)
  0x110009ae;       (* arm_ADD W14 W13 (rvalue (word 2)) *)
  0x11000db3;       (* arm_ADD W19 W13 (rvalue (word 3)) *)
  0xa9425807;       (* arm_LDP X7 X22 X0 (Immediate_Offset (iword (&32))) *)
  0x5ac009ce;       (* arm_REV W14 W14 *)
  0x5ac00a78;       (* arm_REV W24 W19 *)
  0xaa18818a;       (* arm_ORR X10 X12 (Shiftedreg X24 LSL 32) *)
  0xaa0e8193;       (* arm_ORR X19 X12 (Shiftedreg X14 LSL 32) *)
  0x110001bc;       (* arm_ADD W28 W13 (rvalue (word 0)) *)
  0xa90c4feb;       (* arm_STP X11 X19 SP (Immediate_Offset (iword (&192))) *)
  0xa90d2beb;       (* arm_STP X11 X10 SP (Immediate_Offset (iword (&208))) *)
  0x5ac00b99;       (* arm_REV W25 W28 *)
  0x110005be;       (* arm_ADD W30 W13 (rvalue (word 1)) *)
  0x110011ad;       (* arm_ADD W13 W13 (rvalue (word 4)) *)
  0xaa198193;       (* arm_ORR X19 X12 (Shiftedreg X25 LSL 32) *)
  0x3dc037ff;       (* arm_LDR Q31 SP (Immediate_Offset (word 208)) *)
  0x5ac00bca;       (* arm_REV W10 W30 *)
  0xca140377;       (* arm_EOR X23 X27 X20 *)
  0xa90a4feb;       (* arm_STP X11 X19 SP (Immediate_Offset (iword (&160))) *)
  0x3dc033e3;       (* arm_LDR Q3 SP (Immediate_Offset (word 192)) *)
  0xca15023a;       (* arm_EOR X26 X17 X21 *)
  0xca1400fd;       (* arm_EOR X29 X7 X20 *)
  0x3dc02be8;       (* arm_LDR Q8 SP (Immediate_Offset (word 160)) *)
  0xa9412011;       (* arm_LDP X17 X8 X0 (Immediate_Offset (iword (&16))) *)
  0xaa0a8193;       (* arm_ORR X19 X12 (Shiftedreg X10 LSL 32) *)
  0xca1502d8;       (* arm_EOR X24 X22 X21 *)
  0xa90c63fd;       (* arm_STP X29 X24 SP (Immediate_Offset (iword (&192))) *)
  0x4e284a5f;       (* arm_AESE Q31 Q18 *)
  0x4e286bff;       (* arm_AESMC Q31 Q31 *)
  0xa8c4640a;       (* arm_LDP X10 X25 X0 (Postimmediate_Offset (iword (&64))) *)
  0x3dc033e6;       (* arm_LDR Q6 SP (Immediate_Offset (word 192)) *)
  0x4e284a43;       (* arm_AESE Q3 Q18 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x3dc008ce;       (* arm_LDR Q14 X6 (Immediate_Offset (word 32)) *)
  0x4e284a48;       (* arm_AESE Q8 Q18 *)
  0x4e286908;       (* arm_AESMC Q8 Q8 *)
  0xca140231;       (* arm_EOR X17 X17 X20 *)
  0xca15011d;       (* arm_EOR X29 X8 X21 *)
  0x4e284a7f;       (* arm_AESE Q31 Q19 *)
  0x4e286bff;       (* arm_AESMC Q31 Q31 *)
  0xa90b77f1;       (* arm_STP X17 X29 SP (Immediate_Offset (iword (&176))) *)
  0x4e284a68;       (* arm_AESE Q8 Q19 *)
  0x4e286908;       (* arm_AESMC Q8 Q8 *)
  0xca150336;       (* arm_EOR X22 X25 X21 *)
  0xca14014a;       (* arm_EOR X10 X10 X20 *)
  0x4e284a63;       (* arm_AESE Q3 Q19 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0xa90a5bea;       (* arm_STP X10 X22 SP (Immediate_Offset (iword (&160))) *)
  0x4e284a88;       (* arm_AESE Q8 Q20 *)
  0x4e286908;       (* arm_AESMC Q8 Q8 *)
  0x3dc02be1;       (* arm_LDR Q1 SP (Immediate_Offset (word 160)) *)
  0x4e284a83;       (* arm_AESE Q3 Q20 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0xa90d6bf7;       (* arm_STP X23 X26 SP (Immediate_Offset (iword (&208))) *)
  0x4e284aa8;       (* arm_AESE Q8 Q21 *)
  0x4e286908;       (* arm_AESMC Q8 Q8 *)
  0x3dc02fea;       (* arm_LDR Q10 SP (Immediate_Offset (word 176)) *)
  0x4e284aa3;       (* arm_AESE Q3 Q21 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284ac8;       (* arm_AESE Q8 Q22 *)
  0x4e286908;       (* arm_AESMC Q8 Q8 *)
  0xa90b4feb;       (* arm_STP X11 X19 SP (Immediate_Offset (iword (&176))) *)
  0x3dc037e0;       (* arm_LDR Q0 SP (Immediate_Offset (word 208)) *)
  0x4e284ac3;       (* arm_AESE Q3 Q22 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x3dc02fe4;       (* arm_LDR Q4 SP (Immediate_Offset (word 176)) *)
  0x4e284ae8;       (* arm_AESE Q8 Q23 *)
  0x4e286908;       (* arm_AESMC Q8 Q8 *)
  0x3dc00cdd;       (* arm_LDR Q29 X6 (Immediate_Offset (word 48)) *)
  0x4e284ae3;       (* arm_AESE Q3 Q23 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b08;       (* arm_AESE Q8 Q24 *)
  0x4e286908;       (* arm_AESMC Q8 Q8 *)
  0x4e284b03;       (* arm_AESE Q3 Q24 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b28;       (* arm_AESE Q8 Q25 *)
  0x4e286908;       (* arm_AESMC Q8 Q8 *)
  0x4e284b23;       (* arm_AESE Q3 Q25 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b48;       (* arm_AESE Q8 Q26 *)
  0x4e286908;       (* arm_AESMC Q8 Q8 *)
  0x4e284b43;       (* arm_AESE Q3 Q26 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b68;       (* arm_AESE Q8 Q27 *)
  0x4e286908;       (* arm_AESMC Q8 Q8 *)
  0x4e284b63;       (* arm_AESE Q3 Q27 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b88;       (* arm_AESE Q8 Q28 *)
  0x4e286908;       (* arm_AESMC Q8 Q8 *)
  0x4e284b83;       (* arm_AESE Q3 Q28 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e2849e8;       (* arm_AESE Q8 Q15 *)
  0x4e286908;       (* arm_AESMC Q8 Q8 *)
  0x4e2849e3;       (* arm_AESE Q3 Q15 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284a08;       (* arm_AESE Q8 Q16 *)
  0x4e286908;       (* arm_AESMC Q8 Q8 *)
  0x4e284a03;       (* arm_AESE Q3 Q16 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284a28;       (* arm_AESE Q8 Q17 *)
  0x4e284a23;       (* arm_AESE Q3 Q17 *)
  0x4e284a9f;       (* arm_AESE Q31 Q20 *)
  0x4e286bff;       (* arm_AESMC Q31 Q31 *)
  0x6e281c29;       (* arm_EOR_VEC Q9 Q1 Q8 128 *)
  0x6e231cc6;       (* arm_EOR_VEC Q6 Q6 Q3 128 *)
  0x4e284a44;       (* arm_AESE Q4 Q18 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e200925;       (* arm_REV64_VEC Q5 Q9 8 *)
  0x4e284abf;       (* arm_AESE Q31 Q21 *)
  0x4e286bff;       (* arm_AESMC Q31 Q31 *)
  0x3d800846;       (* arm_STR Q6 X2 (Immediate_Offset (word 32)) *)
  0x4e284a64;       (* arm_AESE Q4 Q19 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x3dc000c3;       (* arm_LDR Q3 X6 (Immediate_Offset (word 0)) *)
  0x4e284adf;       (* arm_AESE Q31 Q22 *)
  0x4e286bff;       (* arm_AESMC Q31 Q31 *)
  0x4e284a84;       (* arm_AESE Q4 Q20 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x6e3e1cbe;       (* arm_EOR_VEC Q30 Q5 Q30 128 *)
  0x3dc014c8;       (* arm_LDR Q8 X6 (Immediate_Offset (word 80)) *)
  0x4e284aff;       (* arm_AESE Q31 Q23 *)
  0x4e286bff;       (* arm_AESMC Q31 Q31 *)
  0x4e284aa4;       (* arm_AESE Q4 Q21 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x6e1e43c1;       (* arm_EXT Q1 Q30 Q30 64 *)
  0x4e284b1f;       (* arm_AESE Q31 Q24 *)
  0x4e286bff;       (* arm_AESMC Q31 Q31 *)
  0x4e2008c2;       (* arm_REV64_VEC Q2 Q6 8 *)
  0x6e3e1c25;       (* arm_EOR_VEC Q5 Q1 Q30 128 *)
  0x4e284ac4;       (* arm_AESE Q4 Q22 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x6e02404c;       (* arm_EXT Q12 Q2 Q2 64 *)
  0x4e284b3f;       (* arm_AESE Q31 Q25 *)
  0x4e286bff;       (* arm_AESMC Q31 Q31 *)
  0x4e284ae4;       (* arm_AESE Q4 Q23 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b5f;       (* arm_AESE Q31 Q26 *)
  0x4e286bff;       (* arm_AESMC Q31 Q31 *)
  0x6e221d81;       (* arm_EOR_VEC Q1 Q12 Q2 128 *)
  0x4e284b04;       (* arm_AESE Q4 Q24 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b7f;       (* arm_AESE Q31 Q27 *)
  0x4e286bff;       (* arm_AESMC Q31 Q31 *)
  0x4e284b24;       (* arm_AESE Q4 Q25 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b9f;       (* arm_AESE Q31 Q28 *)
  0x4e286bff;       (* arm_AESMC Q31 Q31 *)
  0x4e284b44;       (* arm_AESE Q4 Q26 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e2849ff;       (* arm_AESE Q31 Q15 *)
  0x4e286bff;       (* arm_AESMC Q31 Q31 *)
  0x4e284b64;       (* arm_AESE Q4 Q27 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284a1f;       (* arm_AESE Q31 Q16 *)
  0x4e286bff;       (* arm_AESMC Q31 Q31 *)
  0x4e284b84;       (* arm_AESE Q4 Q28 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284a3f;       (* arm_AESE Q31 Q17 *)
  0x4e2849e4;       (* arm_AESE Q4 Q15 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x0eeee04c;       (* arm_PMULL_VEC Q12 Q2 Q14 64 *)
  0x6e3f1c0b;       (* arm_EOR_VEC Q11 Q0 Q31 128 *)
  0x3dc004df;       (* arm_LDR Q31 X6 (Immediate_Offset (word 16)) *)
  0x4e284a04;       (* arm_AESE Q4 Q16 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4eeee046;       (* arm_PMULL2_VEC Q6 Q2 Q14 64 *)
  0x4e200962;       (* arm_REV64_VEC Q2 Q11 8 *)
  0x3d800c4b;       (* arm_STR Q11 X2 (Immediate_Offset (word 48)) *)
  0x4e284a24;       (* arm_AESE Q4 Q17 *)
  0x4ee3e040;       (* arm_PMULL2_VEC Q0 Q2 Q3 64 *)
  0x5e18044e;       (* arm_DUP_ELEM_SCALAR Q14 Q2 1 64 *)
  0x6e241d4b;       (* arm_EOR_VEC Q11 Q10 Q4 128 *)
  0x0ee3e04a;       (* arm_PMULL_VEC Q10 Q2 Q3 64 *)
  0x2e221dc4;       (* arm_EOR_VEC Q4 Q14 Q2 64 *)
  0x4effe022;       (* arm_PMULL2_VEC Q2 Q1 Q31 64 *)
  0x4e200963;       (* arm_REV64_VEC Q3 Q11 8 *)
  0x6e2c1d4e;       (* arm_EOR_VEC Q14 Q10 Q12 128 *)
  0x0effe081;       (* arm_PMULL_VEC Q1 Q4 Q31 64 *)
  0x6e261c0a;       (* arm_EOR_VEC Q10 Q0 Q6 128 *)
  0x4efde060;       (* arm_PMULL2_VEC Q0 Q3 Q29 64 *)
  0x5e180466;       (* arm_DUP_ELEM_SCALAR Q6 Q3 1 64 *)
  0x0efde064;       (* arm_PMULL_VEC Q4 Q3 Q29 64 *)
  0x6e221c2c;       (* arm_EOR_VEC Q12 Q1 Q2 128 *)
  0x2e231cdd;       (* arm_EOR_VEC Q29 Q6 Q3 64 *)
  0x0ee8e3df;       (* arm_PMULL_VEC Q31 Q30 Q8 64 *)
  0x6e201d42;       (* arm_EOR_VEC Q2 Q10 Q0 128 *)
  0x4ee8e3c1;       (* arm_PMULL2_VEC Q1 Q30 Q8 64 *)
  0x6e241dce;       (* arm_EOR_VEC Q14 Q14 Q4 128 *)
  0x0eede3aa;       (* arm_PMULL_VEC Q10 Q29 Q13 64 *)
  0x4eede0be;       (* arm_PMULL2_VEC Q30 Q5 Q13 64 *)
  0x6e211c45;       (* arm_EOR_VEC Q5 Q2 Q1 128 *)
  0x6e3f1dc1;       (* arm_EOR_VEC Q1 Q14 Q31 128 *)
  0x6e2a1d80;       (* arm_EOR_VEC Q0 Q12 Q10 128 *)
  0x6e0540a3;       (* arm_EXT Q3 Q5 Q5 64 *)
  0x0ee7e0a4;       (* arm_PMULL_VEC Q4 Q5 Q7 64 *)
  0x6e3e1c00;       (* arm_EOR_VEC Q0 Q0 Q30 128 *)
  0x6e251c3e;       (* arm_EOR_VEC Q30 Q1 Q5 128 *)
  0x3d80044b;       (* arm_STR Q11 X2 (Immediate_Offset (word 16)) *)
  0x3c840449;       (* arm_STR Q9 X2 (Postimmediate_Offset (word 64)) *)
  0x6e3e1c00;       (* arm_EOR_VEC Q0 Q0 Q30 128 *)
  0x6e241c6b;       (* arm_EOR_VEC Q11 Q3 Q4 128 *)
  0x6e2b1c0b;       (* arm_EOR_VEC Q11 Q0 Q11 128 *)
  0x0ee7e16d;       (* arm_PMULL_VEC Q13 Q11 Q7 64 *)
  0x6e0b416b;       (* arm_EXT Q11 Q11 Q11 64 *)
  0x6e2d1c3e;       (* arm_EOR_VEC Q30 Q1 Q13 128 *)
  0x6e2b1fcb;       (* arm_EOR_VEC Q11 Q30 Q11 128 *)
  0x6e0b417e;       (* arm_EXT Q30 Q11 Q11 64 *)
  0x3dc000cc;       (* arm_LDR Q12 X6 (Immediate_Offset (word 0)) *)
  0x3dc008cd;       (* arm_LDR Q13 X6 (Immediate_Offset (word 32)) *)
  0x3dc004ce;       (* arm_LDR Q14 X6 (Immediate_Offset (word 16)) *)
  0xb40007b0;       (* arm_CBZ X16 (word 244) *)
  0x110001be;       (* arm_ADD W30 W13 (rvalue (word 0)) *)
  0x5ac00bdc;       (* arm_REV W28 W30 *)
  0xaa1c819a;       (* arm_ORR X26 X12 (Shiftedreg X28 LSL 32) *)
  0x110005ad;       (* arm_ADD W13 W13 (rvalue (word 1)) *)
  0xa90a6beb;       (* arm_STP X11 X26 SP (Immediate_Offset (iword (&160))) *)
  0x3dc02be9;       (* arm_LDR Q9 SP (Immediate_Offset (word 160)) *)
  0xa8c1281c;       (* arm_LDP X28 X10 X0 (Postimmediate_Offset (iword (&16))) *)
  0x4e284a49;       (* arm_AESE Q9 Q18 *)
  0x4e286929;       (* arm_AESMC Q9 Q9 *)
  0xca140387;       (* arm_EOR X7 X28 X20 *)
  0x4e284a69;       (* arm_AESE Q9 Q19 *)
  0x4e286929;       (* arm_AESMC Q9 Q9 *)
  0xca150157;       (* arm_EOR X23 X10 X21 *)
  0xa90a5fe7;       (* arm_STP X7 X23 SP (Immediate_Offset (iword (&160))) *)
  0x4e284a89;       (* arm_AESE Q9 Q20 *)
  0x4e286929;       (* arm_AESMC Q9 Q9 *)
  0x3dc02be1;       (* arm_LDR Q1 SP (Immediate_Offset (word 160)) *)
  0x4e284aa9;       (* arm_AESE Q9 Q21 *)
  0x4e286929;       (* arm_AESMC Q9 Q9 *)
  0x4e284ac9;       (* arm_AESE Q9 Q22 *)
  0x4e286929;       (* arm_AESMC Q9 Q9 *)
  0x4e284ae9;       (* arm_AESE Q9 Q23 *)
  0x4e286929;       (* arm_AESMC Q9 Q9 *)
  0x4e284b09;       (* arm_AESE Q9 Q24 *)
  0x4e286929;       (* arm_AESMC Q9 Q9 *)
  0x4e284b29;       (* arm_AESE Q9 Q25 *)
  0x4e286929;       (* arm_AESMC Q9 Q9 *)
  0x4e284b49;       (* arm_AESE Q9 Q26 *)
  0x4e286929;       (* arm_AESMC Q9 Q9 *)
  0x4e284b69;       (* arm_AESE Q9 Q27 *)
  0x4e286929;       (* arm_AESMC Q9 Q9 *)
  0x4e284b89;       (* arm_AESE Q9 Q28 *)
  0x4e286929;       (* arm_AESMC Q9 Q9 *)
  0x4e2849e9;       (* arm_AESE Q9 Q15 *)
  0x4e286929;       (* arm_AESMC Q9 Q9 *)
  0x4e284a09;       (* arm_AESE Q9 Q16 *)
  0x4e286929;       (* arm_AESMC Q9 Q9 *)
  0x4e284a29;       (* arm_AESE Q9 Q17 *)
  0x6e291c29;       (* arm_EOR_VEC Q9 Q1 Q9 128 *)
  0x4e200923;       (* arm_REV64_VEC Q3 Q9 8 *)
  0x3c810449;       (* arm_STR Q9 X2 (Postimmediate_Offset (word 16)) *)
  0x6e3e1c61;       (* arm_EOR_VEC Q1 Q3 Q30 128 *)
  0x5e180420;       (* arm_DUP_ELEM_SCALAR Q0 Q1 1 64 *)
  0x4eece03f;       (* arm_PMULL2_VEC Q31 Q1 Q12 64 *)
  0x0eece028;       (* arm_PMULL_VEC Q8 Q1 Q12 64 *)
  0x2e211c1d;       (* arm_EOR_VEC Q29 Q0 Q1 64 *)
  0x0ee7e3eb;       (* arm_PMULL_VEC Q11 Q31 Q7 64 *)
  0x6e3f1d04;       (* arm_EOR_VEC Q4 Q8 Q31 128 *)
  0x6e1f43ff;       (* arm_EXT Q31 Q31 Q31 64 *)
  0x0eeee3a6;       (* arm_PMULL_VEC Q6 Q29 Q14 64 *)
  0x6e2b1fff;       (* arm_EOR_VEC Q31 Q31 Q11 128 *)
  0x6e241cc2;       (* arm_EOR_VEC Q2 Q6 Q4 128 *)
  0x6e3f1c45;       (* arm_EOR_VEC Q5 Q2 Q31 128 *)
  0x0ee7e0aa;       (* arm_PMULL_VEC Q10 Q5 Q7 64 *)
  0x6e0540bf;       (* arm_EXT Q31 Q5 Q5 64 *)
  0x6e2a1d04;       (* arm_EOR_VEC Q4 Q8 Q10 128 *)
  0x6e3f1c8b;       (* arm_EOR_VEC Q11 Q4 Q31 128 *)
  0x6e0b417e;       (* arm_EXT Q30 Q11 Q11 64 *)
  0xd1000610;       (* arm_SUB X16 X16 (rvalue (word 1)) *)
  0xb5fff8b0;       (* arm_CBNZ X16 (word 2096916) *)
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

let AES256_GCM_ENC_EXEC =
  ARM_MK_EXEC_RULE aes256_gcm_enc_mc;;

(* ---- AES-256 crypto substrate (the generic lemmas are in aes_gcm_utils.ml) ---- *)

(**** This is the form that we actually XOR little-endian bytes with
 **** in the algorithm, so we switch back out of NIST big-endian
 ****)

(* The i-th ciphertext block: keystream XOR plaintext - little-endian *)

let aes256_cipher_block = new_definition
 `aes256_cipher_block c nonce rk inblock i =
    word_xor (aes256_ctr_block c nonce rk i) (inblock i)`;;

(* The NIST convention is big-endian, however *)

let aes256_nist_cipher_block = new_definition
 `aes256_nist_cipher_block c nonce rk inblock i =
        word_reversefields 8 (aes256_cipher_block c nonce rk inblock i)`;;

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

(* Split a 128-bit input-block memory read into two 64-bit halves whose addresses  *)
(* are folded back to the canonical "in_p + word(off)" form.  The scalar_rk final  *)
(* round loads each input block as scalars via "ldp x22,x23,[x0,#K]", i.e. it reads *)
(* the block's two 64-bit halves at x0+K and x0+K+8.  READ_MEMORY_SPLIT_CONV emits  *)
(* the high half at address (in_p + word off) + word 8; the simulator's memory      *)
(* lookup will not match that against x0+K+8 unless we renormalise it to            *)
(* in_p + word(off+8).  NORMALIZE_RELATIVE_ADDRESS_CONV reassociates and GSYM       *)

(* Tail-loop variant of the input split.  The tail block is loaded by the         *)
(* POST-INDEXED "ldp x22,x23,[x0],#16": the ARM model reads the second register    *)
(* x23 from address in_p + word((64*loop_count + 16*i) + 8) — the "+ 8" stays a    *)
(* separate num-level summand because the block offset (64*loop_count + 16*i) has   *)
(* a symbolic i, so NUM_ADD_CONV cannot fold it.  The plain SPLIT + NORMALISE (no   *)
(* ADD_ASSOC/NUM fold) reproduces exactly that address form, letting the           *)
(* post-indexed load resolve x23 (offset-mode loads in the main loop DO fold, hence *)

let AES256_CTR_BLOCK_RECONSTRUCT = prove
 (`word_reversefields 8 (aes256_cipher (ctr_block nonce (i + c)) rk) =
   aes256_ctr_block c nonce rk i /\
   word_reversefields 8 (aes256_cipher (ctr_block nonce (i + c + 1)) rk) =
   aes256_ctr_block c nonce rk (i + 1) /\
   word_reversefields 8 (aes256_cipher (ctr_block nonce (i + c + 2)) rk) =
   aes256_ctr_block c nonce rk (i + 2) /\
   word_reversefields 8 (aes256_cipher (ctr_block nonce (i + c + 3)) rk) =
   aes256_ctr_block c nonce rk (i + 3)`,
  REWRITE_TAC[aes256_ctr_block;
              ARITH_RULE `i + c + 1 = (i + 1) + c`;
              ARITH_RULE `i + c + 2 = (i + 2) + c`;
              ARITH_RULE `i + c + 3 = (i + 3) + c`]);;

let AES256_CIPHER_BLOCK_NIST = prove
 (`aes256_cipher_block c nonce rk inblock i =
        word_reversefields 8 (aes256_nist_cipher_block c nonce rk inblock i)`,
  REWRITE_TAC[aes256_nist_cipher_block; WORD_REVERSEFIELDS_REVERSEFIELDS]);;

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

(* ========================================================================= *)
(* AES-256 partial-encryption abstractions (256 analog of the 128 aes7c/8c/  *)
(* 10p).  Carried head depths from static aese-key-EL trace of the steady    *)
(* body: Q3=11 rounds (aes11c), Q4=7 rounds (aes7c), Q8=1 round (aes1c).      *)
(* aesNc = N COMPLETE rounds (N aese, N aesmc), keys EL 0..N-1, over the      *)
(* byte-reversed counter block; ends on aesmc.  aes14p = pre-final-rk14 tower *)
(* (14 aese, 13 aesmc, keys EL 0..13, NO final EL14 XOR).                     *)
(* ========================================================================= *)

(* ========================================================================= *)
(* Keystream-fold + counter/lane helper lemmas (256 analogs of the 128       *)
(* KEYSTREAM_FOLD / CT_TO_NCB / JOIN_* / mk_cbv, re-indexed to rk14/EL14).    *)
(* ========================================================================= *)

(* ciphertext -> aes256_nist_cipher_block: word_xor(rev8(cipher(ctr(j+2))))(inblock j) = rev8(aes256_nist_cipher_block j). *)
let CT_TO_NCB256 = prove
 (`word_xor (word_reversefields 8 (aes256_cipher (ctr_block nonce (j + c)) rk)) (inblock j)
   = word_reversefields 8 (aes256_nist_cipher_block c nonce rk inblock j)`,
  REWRITE_TAC[aes256_nist_cipher_block; aes256_cipher_block; aes256_ctr_block; WORD_REVERSEFIELDS_REVERSEFIELDS]);;

(* ========================================================================= *)
(* The elaborated mid-pipeline invariant swp_inv at the steady head       *)
(* pc+0x560 (Lloop_unrolled_start).  256 analog of the AES-128 invariant.      *)
(* Deltas: round keys Q18-Q28=EL0-10, Q15/Q16/Q17=EL11-13, scalar X20/X21=    *)
(* EL14; aes256_cipher; carried AES partials Q3=aes11c/Q4=aes7c/Q8=aes1c;     *)
(* PCs 0x560/0x8a4.  Counter indices per partial are a HYPOTHESIS validated by *)
(* the BODYLEG fold-forward (must land inv(i+1) with counters +4).            *)
(* ========================================================================= *)

(* swpgrp: the loop-carried GHASH accumulator for the 256 SWP schedule.  KEY FINDING (from the CONJ1
   WORD_BITWISE ground truth): the head-ext `ext v30,v29,v29` byteswaps Q29 into register form, but the reduce's
   Karatsuba packing reads the two 64-bit halves in the SWAPPED order, so the two half-swaps CANCEL.  Net: the
   recurrence is BYTESWAP-FREE -- Q29(i+1) = ghash gt (Q29(i)) [cbs] -- and Q29 IS the clean Horner accumulator
   (consistent with FILL having earlier disproved Q29 = byteswap128(nist_ghash)).  swpgrp gt acc i = the plain
   accumulator after i 4-block groups; the body-leg close_goal7 is REFLEXIVE against it.  The DRAIN/tail leg links
   swpgrp gt tag0 loop_count to the stored tag via the postamble's ext/rev64. *)
let swpgrp = define
 `swpgrp (gt:int128) (acc:int128) 0 (blk:num->int128) = acc /\
  swpgrp gt acc (SUC i) blk =
    ghash_polyval_acc gt (swpgrp gt acc i blk)
      [blk (4*i); blk (4*i+1); blk (4*i+2); blk (4*i+3)]`;;

let swp_inv = `\(i:num) s.
    read X0 s = word_add in_p (word (64 * (i+1))) /\
    read X2 s = word_add out_p (word (64 * i)) /\
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
    read X20 s = word_subword (word_reversefields 8 (EL 14 rk):int128) (0,64):int64 /\
    read X21 s = word_subword (word_reversefields 8 (EL 14 rk):int128) (64,64):int64 /\
    read X11 s = word_subword (word_reversefields 8 (ctr_block nonce c):int128) (0,64):int64 /\
    read X12 s = word_zx (word_zx (word_subword
        (word_reversefields 8 (ctr_block nonce c):int128) (64,64):int64):int32):int64 /\
    read X13 s = word_zx (word (4 * i + c + 4):int32):int64 /\
    read Q7 s = word 13979173243358019584 /\
    read Q3  s = aes11c nonce rk (4*i+c) /\
    read Q4  s = aes7c nonce rk (4*i+c+2) /\
    read Q8  s = aes1c nonce rk (4*i+c+1) /\
    read Q29 s = swpgrp (ghash_twist (aes256_cipher (word 0) rk)) tag0 i
                   (aes256_nist_cipher_block c nonce rk inblock) /\
    read Q2 s = byteswap128 (h_power (ghash_twist (aes256_cipher (word 0) rk)) 3) /\
    read Q13 s = byteswap128 (h_power (ghash_twist (aes256_cipher (word 0) rk)) 0) /\
    read X1 s = word (loop_count - (i+1)) /\ read X15 s = word(len_bits DIV 8) /\ read X16 s = word loop_remain /\
    htable_mem_4 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s /\
    (!j. j < nblocks ==> read (memory :> bytes128 (word_add in_p (word(16*j)))) s = inblock j) /\
    (!j. j < 4 * i ==> read (memory :> bytes128 (word_add out_p (word(16*j)))) s =
             word_xor (aes256_ctr_block c nonce rk j) (inblock j)) /\
    read (memory :> bytes128 (word_add stackpointer (word 160))) s = word_xor (inblock (4*i+0)) (word_reversefields 8 (EL 14 rk)) /\
    read (memory :> bytes128 (word_add stackpointer (word 176))) s = word_xor (inblock (4*i+1)) (word_reversefields 8 (EL 14 rk)) /\
    read (memory :> bytes128 (word_add stackpointer (word 192))) s = word_xor (inblock (4*i+2)) (word_reversefields 8 (EL 14 rk)) /\
    read Q31 s = aes6c nonce rk (4*i+c+3) /\
    read X26 s = word_subword (word_xor (inblock (4*i+3)) (word_reversefields 8 (EL 14 rk)):int128) (64,64):int64 /\
    read X24 s = word_subword (word_xor (inblock (4*i+3)) (word_reversefields 8 (EL 14 rk)):int128) (0,64):int64`;;

(* ========================================================================= *)
(* BODYLEG: one-body preservation swp_inv i @0x560 -> swp_inv(i+1)    *)
(* @0x8a4.  The AES-128 proof's machinery (leg_state / mk_body_goal /         *)
(* INPUT_SPLIT_TAC / setup_tac / step_body_tac / closers) re-indexed for 256: *)
(* PCs 0x560/0x8a4, step 1..210, 256 merge sites, +4 AES rounds, EL14/rk14,   *)
(* 15-elt rk-list, aes256_cipher, XOR_AES256_CIPHER_RECONSTRUCT.              *)
(* ========================================================================= *)

(* ============================================================================ *)
(* Shared machinery ends here; the per-leg sections (stepper, closers, leg theorem) follow. *)

(* ========== LEG: fill ========== *)

(* Pruning policy of the enc-256 steppers: in_p reads always kept, every quantified fact kept, with the
   stale sweep (see aes_gcm_utils.ml SWP_STEP_TAC_P). *)
let enc_prune =
  { anchors = []; slots = []; families = [];
    exempt = (fun c -> try free_in `in_p:int64` (lhs c) with _ -> false);
    all_foralls = true; stale_gc = true };;
let gkeepN keeplist th sname = SWP_STEP_TAC_P enc_prune keeplist th sname;;
(* Extract (ptr-name, state-index) from a `read (memory :> bytes128 tag_p/ivec_p) sK = V` assumption. *)
let get_membyteread c =
  try let l = lhs c in
      let rd, st = dest_comb l in
      let _, comp = dest_comb rd in
      let stname = (match st with Var(nm,_) when String.length nm>=2 && nm.[0]='s' ->
                       int_of_string(String.sub nm 1 (String.length nm-1)) | _ -> raise Exit) in
      if free_in `tag_p:int64` comp then Some("tag_p", stname)
      else if free_in `ivec_p:int64` comp then Some("ivec_p", stname)
      else None
  with _ -> None;;
(* FILL variant: keep the tag_p/ivec_p bytes128 reads (gkeepN drops them -> conj3,4 FAIL, the s297 read is absent),
   BUT keep ONLY THE LATEST-state read per ptr (else ~600 stale reads accumulate -> 10.6GB RSS + hours-long close).
   The latest read + the tag_p/ivec_p<->stack nonoverlaps (now in fill_goal precond) let ENSURES_FINAL_STATE_TAC
   carry it forward across the [sp,#*] stores to s297.  (in_p reads still never-discarded, as gkeepN.) *)
let gkeepF keeplist th sname =
  SWP_STEP_TAC_P { enc_prune with families = [get_membyteread] } keeplist th sname;;

(* 256 carried/reduce reg-set: AES partials Q3/Q4/Q8 + reduce Q1/Q2/Q11/Q13/Q14/Q29/Q30 + h-powers
   Q5/Q6/Q17/Q31 + const Q7 + counter/input X-lanes (from harvest). *)
let REDSETX256 = ["Q1";"Q2";"Q3";"Q4";"Q5";"Q6";"Q7";"Q8";"Q11";"Q13";"Q14";"Q16";"Q17";"Q28";"Q29";"Q30";"Q31";
                  "X7";"X8";"X10";"X11";"X13";"X14";"X17";"X22";"X23";"X24";"X25";"X26";"X28";"X29";"X30"];;
(* 256 loop-head scalar lanes to GHOST_INTRO (harvest showed X7/X8/X17/X22/X23/X24/X25/X26/X28/X29/X30
   carry values; add X10/X14/X19/X27 like 128). *)
let ghost_lanes256 = ["X7";"X8";"X17";"X22";"X23";"X24";"X25";"X26";"X28";"X29";"X30";"X10";"X14";"X19";"X27"];;

(* 256 counter-store MERGE sites (body-instr, [sp,#offset]) from disasm stp-to-sp in steady body. *)
let merges256 = [(27,208);(49,160);(92,192);(98,208);(109,176);(118,192);(171,160);(179,176)];;

(* input-split: blocks 4i+0..4i+7 (current group + prefetch), like 128. *)
let INPUT_SPLIT_TAC256_b bound =
  SUBGOAL_THEN
   `read (memory :> bytes128 (word_add in_p (word (16 * (4*i+0))))) s0 = inblock (4*i+0) /\
    read (memory :> bytes128 (word_add in_p (word (16 * (4*i+1))))) s0 = inblock (4*i+1) /\
    read (memory :> bytes128 (word_add in_p (word (16 * (4*i+2))))) s0 = inblock (4*i+2) /\
    read (memory :> bytes128 (word_add in_p (word (16 * (4*i+3))))) s0 = inblock (4*i+3) /\
    read (memory :> bytes128 (word_add in_p (word (16 * (4*i+4))))) s0 = inblock (4*i+4) /\
    read (memory :> bytes128 (word_add in_p (word (16 * (4*i+5))))) s0 = inblock (4*i+5) /\
    read (memory :> bytes128 (word_add in_p (word (16 * (4*i+6))))) s0 = inblock (4*i+6) /\
    read (memory :> bytes128 (word_add in_p (word (16 * (4*i+7))))) s0 = inblock (4*i+7)`
   STRIP_ASSUME_TAC THENL
    [SUBGOAL_THEN `4*i+7 < nblocks` ASSUME_TAC THENL
      [UNDISCH_TAC `nblocks DIV 4 = loop_count` THEN UNDISCH_TAC bound THEN
       UNDISCH_TAC `2 <= loop_count` THEN ARITH_TAC; ALL_TAC] THEN
     REPEAT CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE `16 * (4*i+0) = 64*i`; ARITH_RULE `16 * (4*i+1) = 64*i+16`;
     ARITH_RULE `16 * (4*i+2) = 64*i+32`; ARITH_RULE `16 * (4*i+3) = 64*i+48`;
     ARITH_RULE `16 * (4*i+4) = 64*i+64`; ARITH_RULE `16 * (4*i+5) = 64*i+80`;
     ARITH_RULE `16 * (4*i+6) = 64*i+96`; ARITH_RULE `16 * (4*i+7) = 64*i+112`]) THEN
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o CONV_RULE SPLIT_INPUT_CONV o
     check (fun th -> let c = concl th in is_eq c && free_in `in_p:int64` (lhs c) &&
       can (find_term (fun t -> is_const t && fst(dest_const t) = "bytes128")) (lhs c))));;
let INPUT_SPLIT_TAC256 = INPUT_SPLIT_TAC256_b `i < loop_count - 1`;;

(* leg pre/post state builder (flat beta-reduced conjunction), verbatim from 128. *)
let leg_state inv off idx =
  let body = rhs(concl((TOP_DEPTH_CONV BETA_CONV THENC REWRITE_CONV[ADD_CLAUSES])
                        (list_mk_comb(inv,[idx;`s:armstate`])))) in
  mk_abs(`s:armstate`,
    list_mk_conj(`aligned_bytes_loaded s (word pc) aes256_gcm_enc_mc` ::
                 mk_eq(`read PC s`,mk_comb(`word:num->int64`,mk_binop `+` `pc:num` off)) ::
                 conjuncts body));;

(* --- mk_body_goal: inv i @0x560 -> inv(i+1) @0x8a4, steady range i<loop_count-1. --- *)
let mk_body_goal_b bound inv =
  mk_imp(subst [bound,`i < loop_count - 2`] `([EL 0 rk; EL 1 rk; EL 2 rk; EL 3 rk; EL 4 rk; EL 5 rk; EL 6 rk; EL 7 rk;
      EL 8 rk; EL 9 rk; EL 10 rk; EL 11 rk; EL 12 rk; EL 13 rk; EL 14 rk]:(int128)list = rk) /\
     len_bits DIV 128 = nblocks /\ nblocks DIV 4 = loop_count /\ nblocks MOD 4 = loop_remain /\
     2 <= loop_count /\ i < loop_count - 2 /\ 16 * nblocks < 2 EXP 64 /\ aligned 16 (stackpointer:int64) /\
     nonoverlapping (out_p:int64,16 * nblocks) (word pc:int64,3860) /\
     nonoverlapping (out_p:int64,16 * nblocks) (in_p:int64,16 * nblocks) /\
     nonoverlapping (out_p:int64,16 * nblocks) (htable_p:int64,192) /\
     nonoverlapping (out_p:int64,16 * nblocks) (tag_p:int64,16) /\
     nonoverlapping (out_p:int64,16 * nblocks) (ivec_p:int64,16) /\
     nonoverlapping (out_p:int64,16*nblocks) (word_add stackpointer (word 160):int64,64) /\
     nonoverlapping (tag_p:int64,16) (word pc:int64,3860) /\
     nonoverlapping (tag_p:int64,16) (in_p:int64,16*nblocks) /\
     nonoverlapping (tag_p:int64,16) (htable_p:int64,192) /\
     nonoverlapping (tag_p:int64,16) (word_add stackpointer (word 160):int64,64) /\
     nonoverlapping (ivec_p:int64,16) (word pc:int64,3860) /\
     nonoverlapping (ivec_p:int64,16) (in_p:int64,16*nblocks) /\
     nonoverlapping (ivec_p:int64,16) (htable_p:int64,192) /\
     nonoverlapping (ivec_p:int64,16) (word_add stackpointer (word 160):int64,64) /\
     nonoverlapping (tag_p:int64,16) (ivec_p:int64,16) /\
     nonoverlapping (word_add stackpointer (word 160):int64,64) (word pc:int64,3860) /\
     nonoverlapping (word_add stackpointer (word 160):int64,64) (in_p:int64,16*nblocks) /\
     nonoverlapping (word_add stackpointer (word 160):int64,64) (htable_p:int64,192)`,
   list_mk_icomb "ensures" [`arm`;
     leg_state inv `0x560` `i:num` ;
     leg_state inv `0x8a4` `i+1` ;
     `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
      MAYCHANGE [X19; X20; X21; X22; X23; X24; X25; X26; X27; X28; X29; X30] ,,
      MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
      MAYCHANGE [memory :> bytes(out_p:int64, 16 * nblocks)] ,,
      MAYCHANGE [memory :> bytes(word_add stackpointer (word 160):int64, 64)] ,, MAYCHANGE [events]`]);;
let mk_body_goal = mk_body_goal_b `i < loop_count - 1`;;

let body_goal = mk_body_goal swp_inv;;

(* --- setup: GHOST_INTRO scalar lanes + ENSURES_INIT + input-split + ABBREV read-C-s0 (except in_p). --- *)
let setup_tac_s split =
  STRIP_TAC THEN REWRITE_TAC[fst AES256_GCM_ENC_EXEC] THEN
  MAP_EVERY (fun rn -> GHOST_INTRO_TAC (mk_var("ghost_"^rn,`:int64`)) (parse_term("read "^rn))) ghost_lanes256 THEN
  ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV BETA_CONV)) THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_4]) THEN REWRITE_TAC[htable_mem_4] THEN
  split THEN
  (fun (asl,w) ->
    let jv = `j:num` in
    let reads0 = setify(flat(map (fun (_,th) -> find_terms (fun t -> try let h,a=strip_comb t in
         fst(dest_const h)="read" && length a=2 && string_of_term(hd(tl a))="s0" with _->false) (concl th)) asl)) in
    let toab = filter (fun t -> not(free_in jv t) && not(free_in `in_p:int64` t)
                              && string_of_term t <> "read PC s0") reads0 in
    (EVERY (List.mapi (fun k t -> ABBREV_TAC (mk_eq(mk_var(Printf.sprintf "init_%d" k, type_of t), t))) toab)) (asl,w));;
let setup_tac = setup_tac_s INPUT_SPLIT_TAC256;;

(* --- stepper: gkeepN over REDSETX256, 1..210, MERGE at merges256 sites. --- *)
(* stepping-only prefix (up to but NOT including ENSURES_FINAL_STATE): after this, the s209 read-facts are
   ASSUMPTIONS. *)
(* h-power reload steps: at these instrs the kernel does `ldr q2,[x6,#80]` / `ldr q13,[x6]` (+ Q12/Q6/Q8
   at other htable offsets), loading htable h-power constants.  gkeepN keeps only the LATEST reg value, so the
   INTERMEDIATE reg-reads (read Q2 s46 etc.) referenced by the GHASH reduce tower get orphaned.  Fix: right
   after each such step, fold the just-loaded reg to its htable h-power value using the htable-read assumptions
   (setup_tac already REWRITE_RULE[htable_mem_4] into asl: read(mem,htable_p+M) s0 = byteswap128(h_power..)/
   word_join(kmid..)).  We rewrite the whole assumption set with those + a read-over-nonoverlap frame so the
   ldr result resolves to the s0 htable value.  Applied every step (cheap: the htable facts are few). *)
let step_body_prefix_s setup =
  setup THEN
  (fun (asl,w) ->
     (MAP_EVERY (fun k ->
        gkeepN REDSETX256 AES256_GCM_ENC_EXEC ("s"^string_of_int k) THEN
        RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV THENC
                                 ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV THENC
                                 IN_P_ADDR_FOLD_CONV)) THEN
        (if List.mem_assoc k merges256 then MERGE_CTR128_TAC (List.assoc k merges256) ("s"^string_of_int k)
         else ALL_TAC))
       (1--209)) (asl,w)) THEN   (* body is 209 instrs 0x560..0x8a4; instr 210 = cbnz backedge, handled by WHILE glue *)
  RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV THENC
                           ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV THENC
                           IN_P_ADDR_FOLD_CONV));;
let step_body_prefix = step_body_prefix_s setup_tac;;
let step_body_tac_s prefix =
  prefix THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];;
let step_body_tac = step_body_tac_s step_body_prefix;;

(* ========================================================================= *)
(* Closers (the AES-128 closers re-indexed for the four extra rounds).         *)
(* ========================================================================= *)

(* closers for the AES-partial conjuncts Q3=aes11c/Q4=aes7c/Q8=aes1c + ptrs/X13.
   Order in the invariant: [X0 ptr][X2 ptr]...[X13]...[Q3=aes11c][Q4=aes7c][Q8=aes1c].
   Each aesNc pin at i+1 = aesNc nonce rk (4*(i+1)+K); fold via the def + counter build. *)
let close_ptr : tactic =
  REWRITE_TAC[ARITH_RULE `64*(i+1)=64*i+64`; LEFT_ADD_DISTRIB] THEN CONV_TAC WORD_RULE;;
let close_x13 : tactic =
  REWRITE_TAC[ZX_COUNTER_UD] THEN AP_TERM_TAC THEN REWRITE_TAC[GSYM WORD_ADD] THEN AP_TERM_TAC THEN ARITH_TAC;;
(* aesNc closers: Q3=aes11c(4(i+1)+6), Q4=aes7c(4(i+1)+8), Q8=aes1c(4(i+1)+7).  The stepped value is the
   aesNc def applied to the reassembled reversed-lane counter (word(4i+10)+K, X13 post +4); fold via mk_cbv.
   +4-shifted from the original -4-consistent version (block base 4i+4, confirmed by objdump FILL trace). *)
let close_aes11c : tactic =
  REWRITE_TAC[aes11c] THEN REPEAT(AP_TERM_TAC ORELSE AP_THM_TAC) THEN REWRITE_TAC[ZXNEST4;ZX_COUNTER_UD] THEN
  SUBGOAL_THEN `word (4*i+c+4):int32 = word(4*(i+1)+c)` SUBST1_TAC THENL
   [AP_TERM_TAC THEN ARITH_TAC; ALL_TAC] THEN ACCEPT_TAC (mk_cbv `4*(i+1)+c`);;
let close_aes7c : tactic =
  REWRITE_TAC[aes7c] THEN REPEAT(AP_TERM_TAC ORELSE AP_THM_TAC) THEN REWRITE_TAC[ZXNEST4;ZX_COUNTER_UD] THEN
  SUBGOAL_THEN `word_add (word (4*i+c+4):int32) (word 2) = word(4*(i+1)+c+2):int32` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM WORD_ADD] THEN AP_TERM_TAC THEN ARITH_TAC; ALL_TAC] THEN ACCEPT_TAC (mk_cbv `4*(i+1)+c+2`);;
let close_aes1c : tactic =
  REWRITE_TAC[aes1c] THEN REPEAT(AP_TERM_TAC ORELSE AP_THM_TAC) THEN REWRITE_TAC[ZXNEST4;ZX_COUNTER_UD] THEN
  SUBGOAL_THEN `word_add (word (4*i+c+4):int32) (word 1) = word(4*(i+1)+c+1):int32` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM WORD_ADD] THEN AP_TERM_TAC THEN ARITH_TAC; ALL_TAC] THEN ACCEPT_TAC (mk_cbv `4*(i+1)+c+1`);;

(* Normalize the fresh-read addresses word(64*(i+1)+K) to the split-input canonical word(64*i+(64+K)).
   Body reads input at X0=in_p+64*(i+1); the ldp offsets 0/8/16/24/32/40/48/56 hit blocks 4i+4..7 halves. *)
let SLOT_ADDR_NORM = [
  ARITH_RULE `64*(i+1) = 64*i+64`; ARITH_RULE `64*(i+1)+8 = 64*i+72`;
  ARITH_RULE `64*(i+1)+16 = 64*i+80`; ARITH_RULE `64*(i+1)+24 = 64*i+88`;
  ARITH_RULE `64*(i+1)+32 = 64*i+96`; ARITH_RULE `64*(i+1)+40 = 64*i+104`;
  ARITH_RULE `64*(i+1)+48 = 64*i+112`; ARITH_RULE `64*(i+1)+56 = 64*i+120`];;

(* [sp160/176/192] input^rk14 lane pins.  Body LHS = word_join(word_xor(read bytes64 (in_p+64(i+2)+8k'))(rk14hi))
   (word_xor(read bytes64 (in_p+64(i+2)+0))(rk14lo)); RHS = word_xor(inblock(4(i+1)+4+k))(rk14).  Fold the two
   bytes64 half-reads to inblock via the split-input assumptions (block 4i+8+k = fresh read at X0=in_p+64(i+2)),
   then combine lanes with WORD_BITWISE.  +4-shifted (block base 4i+4). *)
let close_lanejoin : tactic =
  fun (asl,w) ->
    (* the split-input bytes64 assumptions the sim already derived (read bytes64 in_p+... = word_subword(inblock..)) *)
    let inpfacts = List.filter_map (fun (_,th) ->
      let c = concl th in
      if is_eq c && (try can (find_term (fun t -> match t with
             Comb(Const("read",_),Comb(Comb(Const((":>"),_),Const("memory",_)),
                   Comb(Const("bytes64",_),_))) -> true | _ -> false)) (lhs c) with _->false)
         && free_in `in_p:int64` (lhs c)
      then Some th else None) asl in
    (REWRITE_TAC[ARITH_RULE `4*(i+1) = 4*i+4`; ARITH_RULE `4*(i+1)+1 = 4*i+5`;
                 ARITH_RULE `4*(i+1)+2 = 4*i+6`] THEN
     REWRITE_TAC SLOT_ADDR_NORM THEN
     REWRITE_TAC inpfacts THEN
     REWRITE_TAC[WORD_SUBWORD_XOR] THEN
     (REFL_TAC ORELSE CONV_TAC WORD_BLAST ORELSE
      (REWRITE_TAC[JOIN_XOR_LANES] THEN (REFL_TAC ORELSE CONV_TAC WORD_BLAST)))) (asl,w);;

(* X24/X26 = word_subword(word_xor(inblock(4(i+1)+3))(rk14rev))(0/64,64).  4(i+1)+3 = 4i+7.
   Body LHS = word_xor(read bytes64 (in_p+64(i+1)+{48,56}))(subword(rk14rev)(0/64,64)); the bytes64 read is a
   half of block 4i+7.  Fold via split-input assumptions, push subword through xor (WORD_SUBWORD_XOR). *)
let close_x2426 : tactic =
  fun (asl,w) ->
    let inpfacts = List.filter_map (fun (_,th) ->
      let c = concl th in
      if is_eq c && (try can (find_term (fun t -> match t with
             Comb(Const("read",_),Comb(Comb(Const((":>"),_),Const("memory",_)),
                   Comb(Const("bytes64",_),_))) -> true | _ -> false)) (lhs c) with _->false)
         && free_in `in_p:int64` (lhs c)
      then Some th else None) asl in
    (REWRITE_TAC[ARITH_RULE `4*(i+1)+3 = 4*i+7`] THEN
     REWRITE_TAC SLOT_ADDR_NORM THEN
     REWRITE_TAC inpfacts THEN
     REWRITE_TAC[WORD_SUBWORD_XOR] THEN
     (REFL_TAC ORELSE CONV_TAC WORD_BLAST)) (asl,w);;

(* Q31 = aes6c nonce rk (4(i+1)+5).  Mirror of close_aes1c/aes7c but at depth 6.  Dump showed the raw body
   counter is word_add(word(4i+6))(word 3) = 4i+9 = 4(i+1)+5 (the least-advanced/last block of the group). *)
let close_aes6c : tactic =
  REWRITE_TAC[aes6c] THEN REPEAT(AP_TERM_TAC ORELSE AP_THM_TAC) THEN REWRITE_TAC[ZXNEST4;ZX_COUNTER_UD] THEN
  SUBGOAL_THEN `word_add (word (4*i+c+4):int32) (word 3) = word(4*(i+1)+c+3):int32` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM WORD_ADD] THEN AP_TERM_TAC THEN ARITH_TAC; ALL_TAC] THEN ACCEPT_TAC (mk_cbv `4*(i+1)+c+3`);;

(* X1 decrement: word_sub(word(loop_count-(i+1)))(word 1) = word(loop_count-((i+1)+1)). *)
let close_goal8_b bound : tactic =
  fun (asl,w) ->
    let bnds = List.filter_map (fun (_,th) -> let c = concl th in
      if c = `2 <= loop_count` || c = bound then Some th else None) asl in
    (MAP_EVERY (fun th -> ASSUME_TAC th) bnds THEN
     SUBGOAL_THEN `loop_count - ((i+1)+1) = (loop_count - (i+1)) - 1 /\ 1 <= loop_count - (i+1)` STRIP_ASSUME_TAC THENL
      [MAP_EVERY (fun th -> MP_TAC th) bnds THEN ARITH_TAC; ALL_TAC] THEN
     ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[WORD_SUB; VAL_WORD_1] THEN
     REWRITE_TAC[GSYM VAL_WORD_1] THEN AP_TERM_TAC THEN
     MAP_EVERY (fun th -> MP_TAC th) bnds THEN ARITH_TAC) (asl,w);;
let close_goal8_b1 = close_goal8_b `i < loop_count - 1`;;
let close_goal8_b2 = close_goal8_b `i < loop_count - 2`;;

(* output-block keystream identities (the conj close_goal9 leaves). *)
let close_ksfold : tactic =
  fun (asl,w) ->
    let rkth = try snd(find (fun (_,th) -> concl th = rk15) asl) with _ -> failwith "close_ksfold: no rk-hyp" in
    (REPEAT CONJ_TAC THEN
     REWRITE_TAC[JOIN_SUBWORD_RECOMBINE] THEN
     REWRITE_TAC[GSYM AES14P_VIA_AES7C; GSYM AES14P_VIA_AES11C; GSYM AES14P_VIA_AES1C; GSYM AES14P_VIA_AES6C] THEN
     REWRITE_TAC[MATCH_MP KEYSTREAM_FOLD256 rkth]) (asl,w);;

(* output-forall j<4(i+2): split old(j<4(i+1))+4 new blocks 4(i+1)+0..3 = 4i+4..4i+7 (+4-shifted base),
   reconstruct via XOR_AES256_CIPHER_RECONSTRUCT.  The new stored group is 4i+4..4i+7 (X2=out_p+64(i+1)). *)
let close_goal9 : tactic =
  fun (asl,w) ->
    let rkth = try snd(find (fun (_,th) -> concl th = rk15) asl) with _ -> failwith "close_goal9: no rk-hyp" in
    (REWRITE_TAC[ARITH_RULE `j < 4 * (i+1) <=>
                          j < 4 * i \/ j = 4*i+0 \/ j = 4*i+1 \/ j = 4*i+2 \/ j = 4*i+3`] THEN
     ASM_REWRITE_TAC[TAUT `p \/ q ==> r <=> (p ==> r) /\ (q ==> r)`] THEN
     REWRITE_TAC[FORALL_AND_THM; FORALL_UNWIND_THM2] THEN
     (* out_p store addresses: goal blocks 4i+0..3 -> 64*i+0/16/32/48 (X2=out_p+64*i, store fact form) *)
     REWRITE_TAC[ARITH_RULE `16 * (4*i+0) = 64*i`; ARITH_RULE `16 * (4*i+1) = 64*i+16`;
        ARITH_RULE `16 * (4*i+2) = 64*i+32`; ARITH_RULE `16 * (4*i+3) = 64*i+48`] THEN
     ASM_REWRITE_TAC[] THEN
     REWRITE_TAC[ARITH_RULE `4*i+0 = 4*i`] THEN ASM_REWRITE_TAC[] THEN
     REWRITE_TAC[CTR_BLOCK_BUILD_INSERT] THEN
     REWRITE_TAC[SCALAR_RK_RECONSTRUCT] THEN
     REWRITE_TAC[XOR_AES256_CIPHER_RECONSTRUCT] THEN
     ASM_REWRITE_TAC[MAP; WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
     REWRITE_TAC[aes256_ctr_block] THEN
     REWRITE_TAC[ARITH_RULE `4 * i + c + 3 = (4 * i + 3) + c`;
                 ARITH_RULE `4 * i + c + 2 = (4 * i + 2) + c`;
                 ARITH_RULE `4 * i + c + 1 = (4 * i + 1) + c`;
                 ARITH_RULE `4 * i + 0 = 4 * i`] THEN ASM_REWRITE_TAC[] THEN
     REPEAT CONJ_TAC THEN
     REWRITE_TAC[JOIN_SUBWORD_RECOMBINE] THEN
     REWRITE_TAC[GSYM AES14P_VIA_AES7C; GSYM AES14P_VIA_AES11C; GSYM AES14P_VIA_AES1C; GSYM AES14P_VIA_AES6C] THEN
     REWRITE_TAC[MATCH_MP KEYSTREAM_FOLD256 rkth]) (asl,w);;

(* FILL output-forall at i=0.  close_goal9's symbolic 64*i/4*i+k arith leaves 64*0/4*0+k
   UNREDUCED at i=0 (its NUM_ADD_CONV doesn't collapse the 64*0 multiplication) -> addresses/indices don't match the
   concrete out-store facts (out_p+0/16/32/48, inblock 0..3) -> PARTIAL residual.  This i=0 variant splits j<4
   concretely, NUM_REDUCE_CONV collapses ALL arith to concrete, then the SAME store-fact ASM_REWRITE + reconstruct
   chain (aes256_ctr_block unfold + XOR_AES256_CIPHER_RECONSTRUCT + KEYSTREAM_FOLD256). *)
let close_goal9_i0 : tactic =
  fun (asl,w) ->
    let rkth = try snd(find (fun (_,th) -> concl th = rk15) asl) with _ -> failwith "close_goal9_i0: no rk-hyp" in
    (REWRITE_TAC[ARITH_RULE `j < 4 <=> j = 0 \/ j = 1 \/ j = 2 \/ j = 3`] THEN
     REWRITE_TAC[TAUT `p \/ q ==> r <=> (p ==> r) /\ (q ==> r)`] THEN
     REWRITE_TAC[FORALL_AND_THM; FORALL_UNWIND_THM2] THEN
     CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
     (* block 0's out-store is `str q1,[x2],#64` (post-indexed at x2=out_p) -> store fact reads bare `out_p`, but the
        goal address is `word_add out_p (word 0)` (from 16*0=0).  WORD_ADD_0 normalizes word_add out_p (word 0) -> out_p
        so the block-0 store fact matches (blocks 1,2,3 have nonzero offsets that match directly). *)
     REWRITE_TAC[WORD_ADD_0] THEN
     ASM_REWRITE_TAC[] THEN
     REWRITE_TAC[CTR_BLOCK_BUILD_INSERT] THEN
     REWRITE_TAC[SCALAR_RK_RECONSTRUCT] THEN
     REWRITE_TAC[XOR_AES256_CIPHER_RECONSTRUCT] THEN
     ASM_REWRITE_TAC[MAP; WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
     REWRITE_TAC[aes256_ctr_block; GSYM ADD_ASSOC] THEN
     REWRITE_TAC[ARITH_RULE `(1:num) + c = c + 1`; ARITH_RULE `(2:num) + c = c + 2`;
                 ARITH_RULE `(3:num) + c = c + 3`; ARITH_RULE `(4:num) + c = c + 4`;
                 ARITH_RULE `(0:num) + c = c`] THEN
     CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[] THEN
     REPEAT CONJ_TAC THEN
     REWRITE_TAC[JOIN_SUBWORD_RECOMBINE] THEN
     REWRITE_TAC[GSYM AES14P_VIA_AES7C; GSYM AES14P_VIA_AES11C; GSYM AES14P_VIA_AES1C; GSYM AES14P_VIA_AES6C] THEN
     REWRITE_TAC[MATCH_MP KEYSTREAM_FOLD256 rkth] THEN
     (* block 0 (post-indexed store) goes through XOR_AES256_CIPHER_RECONSTRUCT which leaves its counter as the RAW
        packed form rev8(word_join(word_or(...)(zx-nest of word c))(...)) inside aes256_cipher(rev8(..)); the
        earlier CTR_BLOCK_BUILD_INSERT already ran so this packed counter wasn't folded.  Final pass:
        zx-normalise (ZXNEST4/ZX_COUNTER_UD/GSYM WORD_ADD) + CTR_BLOCK_BUILD_INSERT (packed->rev8(ctr_block)) + WORD_REVERSEFIELDS_REVERSEFIELDS
        (collapse the double rev8) folds block 0's counter -> ctr_block nonce c.  Harmless no-op on blocks 1,2,3 (closed). *)
     REWRITE_TAC[ZXNEST4; ZX_COUNTER_UD; GSYM WORD_ADD] THEN
     REWRITE_TAC[CTR_BLOCK_BUILD_INSERT] THEN
     REWRITE_TAC[WORD_REVERSEFIELDS_REVERSEFIELDS]) (asl,w);;

(* frame. *)
let close_goal10_b bound : tactic =
  fun (asl,w) ->
    let is_mc c = try can(find_term(fun x->match x with Const("MAYCHANGE",_)->true|_->false)) c with _->false in
    let pth = prove(`R s s' ==> R subsumed R' ==> R' s s'`, REWRITE_TAC[subsumed] THEN MESON_TAC[]) in
    (TRY(SUBGOAL_THEN `4*i+3 < nblocks` ASSUME_TAC THENL
      [MAP_EVERY (fun t -> TRY(UNDISCH_TAC t))
         [`nblocks DIV 4 = loop_count`; bound; `2 <= loop_count`] THEN ARITH_TAC; ALL_TAC]) THEN
     (fun (asl2,w2) ->
        let mcths = List.filter_map (fun (_,th) -> if is_mc(concl th) then Some th else None) asl2 in
        (FIRST (map (fun th -> fun g ->
            (MATCH_MP_TAC(MATCH_MP pth th) THEN
             REWRITE_TAC[ETA_AX; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
             SUBSUMED_MAYCHANGE_TAC) g) mcths)) (asl2,w2))) (asl,w);;
let close_goal10_b1 = close_goal10_b `i < loop_count - 1`;;
let close_goal10_b2 = close_goal10_b `i < loop_count - 2`;;

(* HO-match artifact fix: the collapse's CT_TO_NCB on the accumulator-block 4*i leaves a constant-function
   inblock arg `aes256_nist_cipher_block c nonce rk (\x. inblock(4*i)) (4*i)`.  Since aes256_nist_cipher_block only reads the
   j-th block (inblock i, here i=4*i), (\x. inblock(4*i)) 4*i = inblock(4*i) = the plain inblock at 4*i.  So
   the const-fn form EQUALS the plain form.  Prove it (BETA after unfolding the two block defs). *)
let NCB_CONST_FN = prove
 (`aes256_nist_cipher_block c nonce rk (\x:num. inblock (4*i)) (4*i) =
   aes256_nist_cipher_block c nonce rk inblock (4*i)`,
  REWRITE_TAC[aes256_nist_cipher_block; aes256_cipher_block] THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN REFL_TAC);;

(* ABBREV every maximal `word_pmul a b` subterm of the goal as a fresh int128 var.  After this, BITBLAST sees
   only word_join/word_subword/word_xor SHUFFLE over abstract int128s (fast, ~0.5s, 385 BDD vars) instead of
   modelling the 64x64 carryless-multiply circuit (30GB blowup).  This is the key to the 256 reduce closer. *)

(* The head-ext `ext v30,v29,v29` where Q29=swpgrp i (a fresh var, NOT a byteswap128 term) yields the acc
   word_subword(word_join x x)(64,128) = byteswap128 x.  NB byteswap128 is a DEFINED const -- must expand it before
   WORD_BLAST (bare WORD_BLAST on this FAILS: byteswap128 opaque).  Proven once here; REWRITE with it in close_goal7. *)
let ACC_JOIN_BYTESWAP = prove
 (`!x:int128. word_subword (word_join x x :int256) (64,128) :int128 = byteswap128 x`,
  GEN_TAC THEN REWRITE_TAC[byteswap128] THEN CONV_TAC WORD_BLAST);;

(* CORE: the WHOLE 4-lane GHASH-reduce identity in one lemma (CONJ1 karatsuba shuffle + CONJ2 batched fused).
   reduce_g2 of the karatsuba lo/hi/mid sums of lanes (cbb3,hp0)(cbb2,hp1)(cbb1,hp2)(word_xor A cbb0, hp3)
   [hp k = h_power gt k] = ghash_polyval_acc gt A [cbb0;cbb1;cbb2;cbb3].  Proven axiom-free (~14s).  close_goal7,
   after cleaning the acc (ACC double-byteswap -> A) and stripping the outer byteswap, MATCHes this with A:=nist_ghash 4i. *)
let CORE_REDUCE_GHASH = prove
 (`polyval_reduce_g2
     (word_xor (word_pmul (word_subword (cbb3:int128) (0,64):int64) (word_subword (h_power (gt:int128) 0) (0,64):int64))
     (word_xor (word_pmul (word_subword (cbb2:int128) (0,64):int64) (word_subword (h_power gt 1) (0,64):int64))
     (word_xor (word_pmul (word_subword (cbb1:int128) (0,64):int64) (word_subword (h_power gt 2) (0,64):int64))
     (word_pmul (word_subword (word_xor (A:int128) cbb0) (0,64):int64) (word_subword (h_power gt 3) (0,64):int64)))))
     (word_xor (word_pmul (word_subword cbb3 (64,64):int64) (word_subword (h_power gt 0) (64,64):int64))
     (word_xor (word_pmul (word_subword cbb2 (64,64):int64) (word_subword (h_power gt 1) (64,64):int64))
     (word_xor (word_pmul (word_subword cbb1 (64,64):int64) (word_subword (h_power gt 2) (64,64):int64))
     (word_pmul (word_subword (word_xor A cbb0) (64,64):int64) (word_subword (h_power gt 3) (64,64):int64)))))
     (word_xor (word_pmul (karatsuba_mid cbb3) (karatsuba_mid (h_power gt 0)))
     (word_xor (word_pmul (karatsuba_mid cbb2) (karatsuba_mid (h_power gt 1)))
     (word_xor (word_pmul (karatsuba_mid cbb1) (karatsuba_mid (h_power gt 2)))
     (word_pmul (karatsuba_mid (word_xor A cbb0)) (karatsuba_mid (h_power gt 3))))))
   = ghash_polyval_acc gt A [cbb0; cbb1; cbb2; cbb3]`,
  TRANS_TAC EQ_TRANS
   `polyval_reduce_prop3
      (word_xor (word_pmul (cbb3:int128) (h_power gt 0))
      (word_xor (word_pmul (cbb2:int128) (h_power gt 1))
      (word_xor (word_pmul (cbb1:int128) (h_power gt 2))
      (word_pmul (word_xor (A:int128) cbb0) (h_power gt 3)))) :int256)` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[POLYVAL_REDUCE_G2] THEN
    GEN_REWRITE_TAC (RAND_CONV o TOP_DEPTH_CONV) [PMUL_KARATSUBA_JOIN_ALT] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[karatsuba_mid] THEN
    REWRITE_TAC[CMID_LOHI; CMID_HILO] THEN AP_TERM_TAC THEN
    REWRITE_TAC[JOIN_XOR_256; JOIN_XOR_128] THEN
    ABBREV_PMULS THEN POP_ASSUM_LIST(K ALL_TAC) THEN CONV_TAC BITBLAST_RULE;
    MP_TAC(ISPECL [`gt:int128`; `[cbb1;cbb2;cbb3]:(int128)list`; `A:int128`; `cbb0:int128`]
                  GHASH_POLYVAL_ACC_BATCHED) THEN
    REWRITE_TAC[LENGTH; ghash_wide] THEN CONV_TAC NUM_REDUCE_CONV THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    AP_TERM_TAC THEN CONV_TAC WORD_BITWISE_RULE]);;

(* collapse_q30 + close_goal7 (Q30 GHASH tag reduce reconstruction), 256 re-index. *)

(* CT_TO_NCB256 folds word_xor(rev8(aes256_cipher(ctr_block nonce (j + c))rk))(inblock j) ->
   rev8(aes256_nist_cipher_block .. j), pattern (j + c).  FILL's close_goal7 runs at i=0 (reduces group 0), so the
   folded group-0 blocks have counters c,c+1,c+2,c+3 and plain CT_TO_NCB256 higher-order MIS-fires on them.  These 4
   CONCRETE instances (j pre-instantiated to 0,1,2,3, counter base c+K) close that gap so the
   rewrite matches the group-0 blocks. *)
let ct_ncb_concrete =
  [ REWRITE_RULE[ARITH_RULE `(0:num) + c = c`]     (INST [`0`,`j:num`] (SPEC_ALL CT_TO_NCB256));
    REWRITE_RULE[ARITH_RULE `(1:num) + c = c + 1`] (INST [`1`,`j:num`] (SPEC_ALL CT_TO_NCB256));
    REWRITE_RULE[ARITH_RULE `(2:num) + c = c + 2`] (INST [`2`,`j:num`] (SPEC_ALL CT_TO_NCB256));
    REWRITE_RULE[ARITH_RULE `(3:num) + c = c + 3`] (INST [`3`,`j:num`] (SPEC_ALL CT_TO_NCB256)) ];;

let collapse_q30_g g0 : tactic =
  fun (asl,w) ->
    let rkth = try snd(find (fun (_,th) -> concl th = rk15) asl) with _ -> failwith "collapse_q30: no rk-hyp" in
    let ksf = MATCH_MP KEYSTREAM_FOLD256 rkth in
    let ghostpins = List.filter_map (fun (_,th) ->
      let c = concl th in
      if is_eq c then (match lhs c with
        | Var(nm,_) when String.length nm>=6 && String.sub nm 0 6="ghost_"
            && can (find_term (fun t -> try fst(dest_const(fst(strip_comb t)))="inblock" with _->false)) (rhs c)
          -> Some th | _ -> None) else None) asl in
    (* h-power reg-read reloads: the sim left `read Q2 sN`/`read Q13 sN` (htable-loaded h-powers) as opaque
       reg reads whose RHS is a memory read `read(memory:>bytes128 (htable_p+M)) s*`.  Collect those reg-read
       equations; rewriting with them THEN htable_mem_4 resolves the reduce tower's h-power reads to their
       byteswap128(h_power..)/word_join(karatsuba_mid..) values.  Collect any `read Qk sN = <RHS>` (Q-reg,
       state-tagged) assumption. *)
    let hpreads = List.filter_map (fun (_,th) ->
      let c = concl th in
      if is_eq c
         && (try let l=lhs c in let rd,st=dest_comb l in
                 (match rd with Comb(Const("read",_),cc) ->
                     (match cc with Const(rn,_) -> rn="Q2" || rn="Q13" | _ -> false)
                  | _ -> false)
                 && (match st with Var(nm,_)->String.length nm>=1 && nm.[0]='s' |_->false)
             with _->false)
      then Some th else None) asl in
    let htab_exp = try [REWRITE_RULE[htable_mem_4]
                          (snd(find (fun (_,th) -> can (find_term (fun t ->
                             try fst(dest_const(fst(strip_comb t)))="htable_mem_4" with _->false)) (concl th)) asl))]
                   with _ -> [] in
    (REWRITE_TAC[ARITH_RULE `4*(i+1) = 4*i+4`] THEN
     REWRITE_TAC(ghostpins @ hpreads) THEN         (* resolve h-power reg-reads -> their (memory) RHS *)
     REWRITE_TAC htab_exp THEN                      (* memory htable reads -> byteswap128(h_power..)/word_join(kmid..) *)
     REWRITE_TAC[JOIN_SUBWORD_RECOMBINE] THEN
     REWRITE_TAC(ghostpins @ hpreads) THEN
     (* GROUP-0 counter fold (g0 = true: fill / iter1 / lc2 legs): the 4 group-0 GHASH-block AES towers read their counter from the MERGED
        stack slot, now in packed form word_join(word_or(...subword(rev8(ctr_block nonce c))(64,64)...)(word CONST))
        (subword(rev8(ctr_block nonce c))(0,64)).  Normalize the zx-nest (ZXNEST4/ZX_COUNTER_UD/GSYM WORD_ADD), then CTR_BLOCK_BUILD_INSERT
        folds -> word_reversefields 8 (ctr_block nonce cval), giving the aes14p tower input GSYM aes14p needs. *)
     (if g0 then REWRITE_TAC[ZXNEST4; ZX_COUNTER_UD; GSYM WORD_ADD] THEN REWRITE_TAC[CTR_BLOCK_BUILD_INSERT] else ALL_TAC) THEN
     REWRITE_TAC[GSYM AES14P_VIA_AES7C; GSYM AES14P_VIA_AES11C; GSYM AES14P_VIA_AES1C; GSYM AES14P_VIA_AES6C; GSYM aes14p] THEN
     REWRITE_TAC[JOIN_XOR_LANES] THEN
     REWRITE_TAC[ksf] THEN
     REWRITE_TAC[ARITH_RULE `4*i+c+3 = (4*i+3)+c`; ARITH_RULE `4*i+c+2 = (4*i+2)+c`;
                 ARITH_RULE `4*i+c+1 = (4*i+1)+c`; ARITH_RULE `4*i+0 = 4*i`] THEN
     (if g0 then REWRITE_TAC ct_ncb_concrete else ALL_TAC) THEN   (* g0: fold group-0 blocks via the 4 concrete instances BEFORE plain CT_TO_NCB256.
        Under symbolic c the group-0 counters are sums c+K (not the fixed-c literals 2,3,4,5), so plain CT_TO_NCB256's j+c pattern
        higher-order MIS-fires on them (matches j->c, c->K, inblock->const-fn).  ct_ncb_concrete has j pre-instantiated to a literal,
        so its RHS index/counter-base are fixed and it folds cleanly; running it first leaves CT_TO_NCB256 a no-op for g0. *)
     REWRITE_TAC[CT_TO_NCB256] THEN
     REWRITE_TAC[ARITH_RULE `(4*i+0)+2 = 4*i+2`; ARITH_RULE `(4*i+1)+2 = 4*i+3`;
                 ARITH_RULE `(4*i+2)+2 = 4*i+4`; ARITH_RULE `(4*i+3)+2 = 4*i+5`;
                 ARITH_RULE `4*i+0 = 4*i`] THEN
     REWRITE_TAC[NCB_CONST_FN]) (asl,w);;
let collapse_q30_g0 = collapse_q30_g true;;
let collapse_q30_gi = collapse_q30_g false;;

(* swpgrp-invariant close_goal7: the invariant Q29 = swpgrp gt tag0 i lives in the byteswapped GHASH
   domain (head-ext byteswaps it each iteration).  The body-end goal is <machine reduce> = swpgrp gt tag0 (i+1) blk.
   collapse_q30 folds the LHS keystreams; no acc-cleanup (the acc = word_subword(word_join(swpgrp i)(swpgrp i))(64,128) =
   byteswap128(swpgrp i) is EXACTLY the seed swpgrp(SUC i) wants -- do NOT collapse it to clean).  Then RECONSTRUCT folds
   the reduce -> polyval_reduce_g2(byteswap128(swpgrp i)-seed lanes), and CORE_REDUCE_GHASH's recipe closes it =
   ghash gt (byteswap128(swpgrp i))[cbs] = swpgrp(SUC i) by the swpgrp SUC-def.  REFLEXIVE -- no byteswap-commute. *)
(* FILL runs close_goal7 at i=0 (reduces swpgrp 0=tag0 -> swpgrp 1 over group-0 blocks).
   The symbolic-i machinery below normalizes the RHS via `i+1=SUC i`, but FILL's RHS is `swpgrp gt tag0 1` (CONCRETE 1),
   so that rewrite + CONJUNCT2 don't fire and the sofar/cipherblock_k ABBREVs (swpgrp gt tag0 i / ncb..(4*i+k)) miss ->
   the LHS keeps tag0 + aes256_nist_cipher_block..k while the EXISTS_TAC target has the abbrev vars -> WORD_BITWISE mismatch.
   Remedy: at i=0, first REWRITE the RHS swpgrp..1 -> ghash_polyval_acc gt tag0 [ncb0..3] (num_CONV 1 + swpgrp CONJUNCTs +
   NUM_REDUCE), then ABBREV `sofar = tag0` and `cipherblock_k = aes256_nist_cipher_block..k` (CONCRETE forms) so the SAME
   downstream byteswap-strip + EQ_TRANS + CORE machinery applies verbatim.  Detect i=0 by `swpgrp .. 1` (literal 1) in
   the goal's RHS. *)
let close_goal7_i0_c collapse : tactic =
  fun (asl,w) ->
    (collapse THEN
     (* unfold RHS swpgrp..1 -> ghash_polyval_acc gt tag0 [ncb0;ncb1;ncb2;ncb3] *)
     GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [num_CONV `1`] THEN
     GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [CONJUNCT2 swpgrp] THEN
     GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [CONJUNCT1 swpgrp] THEN
     CONV_TAC(RAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
     (* concrete abbrevs: acc = tag0 (i=0 base); blocks = ncb..0/1/2/3.  The head-ext acc collapse uses ACC_JOIN_BYTESWAP
        on word_subword(word_join tag0 tag0)(64,128); ABBREV sofar=tag0 FIRST so it matches the symbolic-path shape. *)
     ABBREV_TAC `sofar:int128 = tag0` THEN
     REWRITE_TAC[ACC_JOIN_BYTESWAP] THEN
     ABBREV_TAC `bsofar:int128 = byteswap128 (sofar:int128)` THEN
     REWRITE_TAC[WORD_SUBWORD_REVERSEFIELDS] THEN
     SIMP_TAC[WORD_JOIN_COMBINE_LEMMA; ARITH] THEN
     REWRITE_TAC[WORD_SUBWORD_XOR] THEN
     REWRITE_TAC[WORD_SUBWORD_BYTESWAP128] THEN
     CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
     REWRITE_TAC[WORD_SUBWORD_XOR] THEN
     CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
     MAP_EVERY ABBREV_TAC
      [`cipherblock_0 = aes256_nist_cipher_block c nonce rk inblock 0`;
       `cipherblock_1 = aes256_nist_cipher_block c nonce rk inblock 1`;
       `cipherblock_2 = aes256_nist_cipher_block c nonce rk inblock 2`;
       `cipherblock_3 = aes256_nist_cipher_block c nonce rk inblock 3`;
       `h0 = h_power (ghash_twist (aes256_cipher (word 0) rk)) 0`;
       `h1 = h_power (ghash_twist (aes256_cipher (word 0) rk)) 1`;
       `h2 = h_power (ghash_twist (aes256_cipher (word 0) rk)) 2`;
       `h3 = h_power (ghash_twist (aes256_cipher (word 0) rk)) 3`] THEN
     REWRITE_TAC[GSYM WORD_SUBWORD_XOR] THEN
     REWRITE_TAC[byteswap128] THEN
     REWRITE_TAC[RECONSTRUCT_POLYVAL_REDUCE_G2] THEN
     EXPAND_TAC "bsofar" THEN
     REWRITE_TAC[WORD_SUBWORD_BYTESWAP128] THEN
     REWRITE_TAC[GSYM WORD_SUBWORD_XOR] THEN
     REWRITE_TAC[CMID_LOHI; CMID_HILO] THEN
     MAP_EVERY EXPAND_TAC ["h0"; "h1"; "h2"; "h3"] THEN
     MATCH_MP_TAC EQ_TRANS THEN
     EXISTS_TAC
      `polyval_reduce_g2
         (word_xor (word_pmul (word_subword (cipherblock_3:int128) (0,64):int64) (word_subword (h_power (ghash_twist (aes256_cipher (word 0) rk)) 0) (0,64):int64))
         (word_xor (word_pmul (word_subword (cipherblock_2:int128) (0,64):int64) (word_subword (h_power (ghash_twist (aes256_cipher (word 0) rk)) 1) (0,64):int64))
         (word_xor (word_pmul (word_subword (cipherblock_1:int128) (0,64):int64) (word_subword (h_power (ghash_twist (aes256_cipher (word 0) rk)) 2) (0,64):int64))
         (word_pmul (word_subword (word_xor (sofar:int128) cipherblock_0) (0,64):int64) (word_subword (h_power (ghash_twist (aes256_cipher (word 0) rk)) 3) (0,64):int64)))))
         (word_xor (word_pmul (word_subword cipherblock_3 (64,64):int64) (word_subword (h_power (ghash_twist (aes256_cipher (word 0) rk)) 0) (64,64):int64))
         (word_xor (word_pmul (word_subword cipherblock_2 (64,64):int64) (word_subword (h_power (ghash_twist (aes256_cipher (word 0) rk)) 1) (64,64):int64))
         (word_xor (word_pmul (word_subword cipherblock_1 (64,64):int64) (word_subword (h_power (ghash_twist (aes256_cipher (word 0) rk)) 2) (64,64):int64))
         (word_pmul (word_subword (word_xor sofar cipherblock_0) (64,64):int64) (word_subword (h_power (ghash_twist (aes256_cipher (word 0) rk)) 3) (64,64):int64)))))
         (word_xor (word_pmul (karatsuba_mid cipherblock_3) (karatsuba_mid (h_power (ghash_twist (aes256_cipher (word 0) rk)) 0)))
         (word_xor (word_pmul (karatsuba_mid cipherblock_2) (karatsuba_mid (h_power (ghash_twist (aes256_cipher (word 0) rk)) 1)))
         (word_xor (word_pmul (karatsuba_mid cipherblock_1) (karatsuba_mid (h_power (ghash_twist (aes256_cipher (word 0) rk)) 2)))
         (word_pmul (karatsuba_mid (word_xor sofar cipherblock_0)) (karatsuba_mid (h_power (ghash_twist (aes256_cipher (word 0) rk)) 3))))))` THEN
     CONJ_TAC THENL
      [MK_COMB_TAC THENL
        [MK_COMB_TAC THENL
          [AP_TERM_TAC THEN CONV_TAC WORD_BITWISE_RULE;
           CONV_TAC WORD_BITWISE_RULE];
         CONV_TAC WORD_BITWISE_RULE];
       MATCH_ACCEPT_TAC CORE_REDUCE_GHASH]) (asl,w);;
let close_goal7_i0 = close_goal7_i0_c collapse_q30_g0;;

let close_goal7_c collapse i0 : tactic =
  fun (asl,w) ->
    (* i=0 dispatch (i0 = true: fill / lc2 legs): if the RHS accumulator is swpgrp..1 (literal 1), use the concrete-abbrev closer. *)
    if i0 && (try can (find_term (fun t -> match t with
          Comb(Comb(Comb(Comb(Const("swpgrp",_),_),_),n),_) -> n = `1`
          | _ -> false)) (rhs w) with _ -> false)
    then close_goal7_i0_c collapse (asl,w)
    else
    (collapse THEN
     (* unfold RHS swpgrp(i+1) -> ghash gt (byteswap128(swpgrp gt tag0 i blk)) [4 blocks] FIRST, so the inner
        `swpgrp gt tag0 i blk` appears on BOTH sides (LHS acc + RHS seed) and one ABBREV catches both. *)
     GEN_REWRITE_TAC (RAND_CONV o TOP_DEPTH_CONV) [ARITH_RULE `i + 1 = SUC i`] THEN
     GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [CONJUNCT2 swpgrp] THEN
     (* ABBREV the acc swpgrp gt tag0 i blk -> 'sofar' (catches LHS acc AND RHS seed), collapse the head-ext
        word_subword(word_join(sofar)(sofar))(64,128) -> byteswap128 sofar via ACC_JOIN_BYTESWAP, BEFORE the block/h
        byteswap-split (else the split tangles the acc).  Then ABBREV byteswap128 sofar -> bsofar (clean var, both sides). *)
     ABBREV_TAC `sofar = swpgrp (ghash_twist (aes256_cipher (word 0) rk)) tag0 i (aes256_nist_cipher_block c nonce rk inblock)` THEN
     REWRITE_TAC[ACC_JOIN_BYTESWAP] THEN
     ABBREV_TAC `bsofar:int128 = byteswap128 (sofar:int128)` THEN
     (* PREFIX NORMALIZATION: fold block byte-towers -> aes256_nist_cipher_block,
        byteswapped h-powers -> clean, so the reduce becomes RECONSTRUCT-foldable.  bsofar is now an opaque var, untouched. *)
     REWRITE_TAC[WORD_SUBWORD_REVERSEFIELDS] THEN
     SIMP_TAC[WORD_JOIN_COMBINE_LEMMA; ARITH] THEN
     REWRITE_TAC[WORD_SUBWORD_XOR] THEN
     REWRITE_TAC[WORD_SUBWORD_BYTESWAP128] THEN
     CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
     REWRITE_TAC[WORD_SUBWORD_XOR] THEN
     CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
     MAP_EVERY ABBREV_TAC
      [`cipherblock_0 = aes256_nist_cipher_block c nonce rk inblock (4 * i)`;
       `cipherblock_1 = aes256_nist_cipher_block c nonce rk inblock (4 * i + 1)`;
       `cipherblock_2 = aes256_nist_cipher_block c nonce rk inblock (4 * i + 2)`;
       `cipherblock_3 = aes256_nist_cipher_block c nonce rk inblock (4 * i + 3)`;
       `h0 = h_power (ghash_twist (aes256_cipher (word 0) rk)) 0`;
       `h1 = h_power (ghash_twist (aes256_cipher (word 0) rk)) 1`;
       `h2 = h_power (ghash_twist (aes256_cipher (word 0) rk)) 2`;
       `h3 = h_power (ghash_twist (aes256_cipher (word 0) rk)) 3`] THEN
     REWRITE_TAC[GSYM WORD_SUBWORD_XOR] THEN
     (* CRITICAL: the prefix folded the reduce_g2 packing's word_join(word_subword ks (0,64))(word_subword ks (64,64))
        into byteswap128 ks, which RECONSTRUCT (expecting word_join(word_subword ks (0,64))(word_subword ks (64,64)))
        cannot match.  EXPAND byteswap128 back to word_join(sub 0)(sub 64) so RECONSTRUCT folds the reduce -> polyval_reduce_g2.
        (bsofar is a var so byteswap128 only appears on the ks-packing here, not on bsofar itself.) *)
     REWRITE_TAC[byteswap128] THEN
     REWRITE_TAC[RECONSTRUCT_POLYVAL_REDUCE_G2] THEN
     (* now goal: polyval_reduce_g2(P1 P2 P3) = ghash gt sofar [cb0..cb3] where the machine's acc-lanes read the
        BYTESWAPPED acc, i.e. word_subword bsofar (64,64) in the lo lane etc.  KEY:
        the head-ext byteswap and the reduce's Karatsuba half-swap CANCEL, so the true seed is sofar (NOT bsofar).
        (1) EXPAND_TAC "bsofar" restores byteswap128 sofar; (2) WORD_SUBWORD_BYTESWAP128 rewrites its halves back to
        sofar's halves (with the 0<->64 position swap that IS the cancellation); (3) GSYM WORD_SUBWORD_XOR folds the
        now-aligned acc-lane word_xor(sub sofar)(sub cb0) -> sub(word_xor sofar cb0), and CMID_LOHI folds the mid acc
        -> karatsuba_mid(word_xor sofar cb0), matching CORE's A-lane form (A:=sofar).  Then EXPAND h0..h3, EQ_TRANS
        through CORE's cbb3.h0-first ordering, MK_COMB-peel the reduce_g2 congruence (each arg a word_xor AC-reorder of
        identical pmul/karatsuba_mid atoms, closed by WORD_BITWISE_RULE), MATCH_ACCEPT CORE_REDUCE_GHASH (A:=sofar). *)
     EXPAND_TAC "bsofar" THEN
     REWRITE_TAC[WORD_SUBWORD_BYTESWAP128] THEN
     REWRITE_TAC[GSYM WORD_SUBWORD_XOR] THEN
     (* fold BOTH mid-lane sub-xor orders -> karatsuba_mid: the acc lane is LO-first (CMID_LOHI) but the machine's
        block mid-lanes (cb1,cb3) are HI-first (CMID_HILO).  Both needed or arg-3 (mid) congruence won't align. *)
     REWRITE_TAC[CMID_LOHI; CMID_HILO] THEN
     MAP_EVERY EXPAND_TAC ["h0"; "h1"; "h2"; "h3"] THEN
     MATCH_MP_TAC EQ_TRANS THEN
     EXISTS_TAC
      `polyval_reduce_g2
         (word_xor (word_pmul (word_subword (cipherblock_3:int128) (0,64):int64) (word_subword (h_power (ghash_twist (aes256_cipher (word 0) rk)) 0) (0,64):int64))
         (word_xor (word_pmul (word_subword (cipherblock_2:int128) (0,64):int64) (word_subword (h_power (ghash_twist (aes256_cipher (word 0) rk)) 1) (0,64):int64))
         (word_xor (word_pmul (word_subword (cipherblock_1:int128) (0,64):int64) (word_subword (h_power (ghash_twist (aes256_cipher (word 0) rk)) 2) (0,64):int64))
         (word_pmul (word_subword (word_xor (sofar:int128) cipherblock_0) (0,64):int64) (word_subword (h_power (ghash_twist (aes256_cipher (word 0) rk)) 3) (0,64):int64)))))
         (word_xor (word_pmul (word_subword cipherblock_3 (64,64):int64) (word_subword (h_power (ghash_twist (aes256_cipher (word 0) rk)) 0) (64,64):int64))
         (word_xor (word_pmul (word_subword cipherblock_2 (64,64):int64) (word_subword (h_power (ghash_twist (aes256_cipher (word 0) rk)) 1) (64,64):int64))
         (word_xor (word_pmul (word_subword cipherblock_1 (64,64):int64) (word_subword (h_power (ghash_twist (aes256_cipher (word 0) rk)) 2) (64,64):int64))
         (word_pmul (word_subword (word_xor sofar cipherblock_0) (64,64):int64) (word_subword (h_power (ghash_twist (aes256_cipher (word 0) rk)) 3) (64,64):int64)))))
         (word_xor (word_pmul (karatsuba_mid cipherblock_3) (karatsuba_mid (h_power (ghash_twist (aes256_cipher (word 0) rk)) 0)))
         (word_xor (word_pmul (karatsuba_mid cipherblock_2) (karatsuba_mid (h_power (ghash_twist (aes256_cipher (word 0) rk)) 1)))
         (word_xor (word_pmul (karatsuba_mid cipherblock_1) (karatsuba_mid (h_power (ghash_twist (aes256_cipher (word 0) rk)) 2)))
         (word_pmul (karatsuba_mid (word_xor sofar cipherblock_0)) (karatsuba_mid (h_power (ghash_twist (aes256_cipher (word 0) rk)) 3))))))` THEN
     CONJ_TAC THENL
      [(* goal-LHS = CORE-LHS: same reduce_g2 (curried f P1 P2 P3 = ((f P1) P2) P3) with P1,P2,P3 word_xor-reordered
         (AC).  Peel the application spine with EXACTLY two MK_COMB (to the outer P3, then P2), and AP_TERM to P1 --
         each arg is a word_xor reordering of the SAME opaque pmul/karatsuba_mid atoms, closed by WORD_BITWISE_RULE.
         (The naive REPEAT/BINOP over-recursed into the xor trees and split misaligned subterms.) *)
       MK_COMB_TAC THENL
        [MK_COMB_TAC THENL
          [AP_TERM_TAC THEN CONV_TAC WORD_BITWISE_RULE;
           CONV_TAC WORD_BITWISE_RULE];
         CONV_TAC WORD_BITWISE_RULE];
       (* CORE-LHS = ghash gt sofar [cbs]: exactly CORE_REDUCE_GHASH (A:=sofar). *)
       MATCH_ACCEPT_TAC CORE_REDUCE_GHASH]) (asl,w);;
let close_goal7_fill = close_goal7_c collapse_q30_g0 true;;
let close_goal7_steady = close_goal7_c collapse_q30_gi false;;
let close_goal7_iter1 = close_goal7_c collapse_q30_g0 false;;

let close_all_c cg7 cg8 cg10 : tactic =
  fun (asl,w) ->
    let has c t = can (find_term (fun u -> try fst(dest_const(fst(strip_comb u)))=c with _->false)) t in
    let has_mc t = try can(find_term(fun x->match x with Const("MAYCHANGE",_)->true|_->false)) t with _->false in
    if has_mc w then cg10 (asl,w)
    else if has "aligned_bytes_loaded" w then ASM_REWRITE_TAC[] (asl,w)
    else if is_forall w then MUST close_goal9 (asl,w)
    else if is_eq w && (has "nist_ghash" (rhs w) || has "swpgrp" (rhs w)) then cg7 (asl,w)
    else
      (FIRST (map MUST
        [ close_ksfold;
          close_ptr; close_x13;
          close_aes11c; close_aes7c; close_aes1c; close_aes6c;
          close_x2426;
          close_lanejoin; cg8;
          (* Q2/Q13 carried h-power pins: read Qk s209 = byteswap128(h_power ..); the sim's s209 value is the
             htable reload, resolvable via ASM (htable_mem_4 expanded in asl) + REFL. *)
          (ASM_REWRITE_TAC[] THEN REFL_TAC);
          ASM_REWRITE_TAC[] ])) (asl,w);;
let close_all_body = close_all_c close_goal7_steady close_goal8_b1 close_goal10_b1;;
let close_all_drain = close_all_c close_goal7_steady close_goal8_b2 close_goal10_b2;;
let close_all_iter1 = close_all_c close_goal7_iter1 close_goal8_b1 close_goal10_b1;;

(* ========================================================================= *)
(* FILL LEG: pc+0xbc -> pc+0x55c (FILL_TO_CBZ), establishing swp_inv 1    *)
(* just before the cbz that separates loop_count = 2 from loop_count >= 3.    *)
(* SEAM (pinned from disasm): the 256 schedule primes ONE                     *)
(* full GHASH group into the FILL, so the head 0x560 is at index i=1 (X13=10, *)
(* out_p+64, Q29=swpgrp gt tag0 1, in_p+128).  The 296 fill instructions are  *)
(* simulated ONCE; FILLLEG (cbz not taken, loop_count >= 3, -> 0x560) and  *)
(* LC2_PARTA (cbz taken, loop_count = 2, -> 0x8a8) are one-instruction hops.  *)
(* Q29 FILL closer: no head-ext, reduce reads Q30=byteswap128                 *)
(* tag0 directly -> close_goal7 tail with A:=tag0.                            *)
(* ========================================================================= *)

(* FILL entry precondition at 0x88 (from the q29harvest precondition; correct). *)
(* The precondition MUST include the tag_p/ivec_p nonoverlaps (vs pc/in_p/htable/stack+160 and
   tag_p vs ivec_p), matching the proven body_goal.  Without nonoverlapping(tag_p/ivec_p)(stackpointer+160), the
   read-over-store at FILL step 12 (0xe8 `stp x11,x22,[sp,#160]`) cannot discharge, so the tag_p/ivec_p reads get
   dropped after s11 and conj3,4 (the s297 invariant reads) fail. *)
let fill_goal = mk_imp
 (`([EL 0 rk; EL 1 rk; EL 2 rk; EL 3 rk; EL 4 rk; EL 5 rk; EL 6 rk; EL 7 rk; EL 8 rk; EL 9 rk;
     EL 10 rk; EL 11 rk; EL 12 rk; EL 13 rk; EL 14 rk]:(int128)list = rk) /\
   len_bits DIV 128 = nblocks /\ nblocks DIV 4 = loop_count /\ nblocks MOD 4 = loop_remain /\
   3 <= loop_count /\ 16 * nblocks < 2 EXP 64 /\ aligned 16 (stackpointer:int64) /\
   nonoverlapping (out_p:int64,16 * nblocks) (word pc:int64,3860) /\
   nonoverlapping (out_p:int64,16 * nblocks) (in_p:int64,16 * nblocks) /\
   nonoverlapping (out_p:int64,16 * nblocks) (htable_p:int64,192) /\
   nonoverlapping (out_p:int64,16 * nblocks) (tag_p:int64,16) /\
   nonoverlapping (out_p:int64,16 * nblocks) (ivec_p:int64,16) /\
   nonoverlapping (out_p:int64,16*nblocks) (word_add stackpointer (word 160):int64,64) /\
   nonoverlapping (tag_p:int64,16) (word pc:int64,3860) /\
   nonoverlapping (tag_p:int64,16) (in_p:int64,16*nblocks) /\
   nonoverlapping (tag_p:int64,16) (htable_p:int64,192) /\
   nonoverlapping (tag_p:int64,16) (word_add stackpointer (word 160):int64,64) /\
   nonoverlapping (ivec_p:int64,16) (word pc:int64,3860) /\
   nonoverlapping (ivec_p:int64,16) (in_p:int64,16*nblocks) /\
   nonoverlapping (ivec_p:int64,16) (htable_p:int64,192) /\
   nonoverlapping (ivec_p:int64,16) (word_add stackpointer (word 160):int64,64) /\
   nonoverlapping (tag_p:int64,16) (ivec_p:int64,16) /\
   nonoverlapping (word_add stackpointer (word 160):int64,64) (word pc:int64,3860) /\
   nonoverlapping (word_add stackpointer (word 160):int64,64) (in_p:int64,16*nblocks) /\
   nonoverlapping (word_add stackpointer (word 160):int64,64) (htable_p:int64,192) /\
   nonoverlapping (word_add stackpointer (word 160):int64,64) (out_p:int64,16*nblocks)`,
  list_mk_icomb "ensures" [`arm`;
    mk_abs(`s:armstate`, list_mk_conj
      [`aligned_bytes_loaded s (word pc) aes256_gcm_enc_mc`;
       `read PC s = word (pc + 0xbc)`;
       `read X0 s = in_p`; `read X2 s = out_p`; `read X3 s = tag_p`; `read X4 s = ivec_p`;
       `read X5 s = key_p`; `read X6 s = htable_p`; `read SP s = stackpointer`;
       `read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0`;
       `read (memory :> bytes128 ivec_p) s = word_reversefields 8 (ctr_block nonce c)`;
       `read Q18 s = word_reversefields 8 (EL 0 rk)`; `read Q19 s = word_reversefields 8 (EL 1 rk)`;
       `read Q20 s = word_reversefields 8 (EL 2 rk)`; `read Q21 s = word_reversefields 8 (EL 3 rk)`;
       `read Q22 s = word_reversefields 8 (EL 4 rk)`; `read Q23 s = word_reversefields 8 (EL 5 rk)`;
       `read Q24 s = word_reversefields 8 (EL 6 rk)`; `read Q25 s = word_reversefields 8 (EL 7 rk)`;
       `read Q26 s = word_reversefields 8 (EL 8 rk)`; `read Q27 s = word_reversefields 8 (EL 9 rk)`;
       `read Q28 s = word_reversefields 8 (EL 10 rk)`; `read Q15 s = word_reversefields 8 (EL 11 rk)`;
       `read Q16 s = word_reversefields 8 (EL 12 rk)`; `read Q17 s = word_reversefields 8 (EL 13 rk)`;
       `read X20 s = word_subword (word_reversefields 8 (EL 14 rk):int128) (0,64):int64`;
       `read X21 s = word_subword (word_reversefields 8 (EL 14 rk):int128) (64,64):int64`;
       `read Q7 s = word 13979173243358019584`;
       `read X11 s = word_subword (word_reversefields 8 (ctr_block nonce c):int128) (0,64):int64`;
       `read X12 s = word_zx (word_zx (word_subword
           (word_reversefields 8 (ctr_block nonce c):int128) (64,64):int64):int32):int64`;
       `read X13 s = word_zx (word c:int32):int64`; `read X15 s = word(len_bits DIV 8)`;
       `read X1 s = word loop_count`; `read X7 s = word nblocks`; `read X16 s = word loop_remain`;
       `read Q30 s = byteswap128 tag0`;
       `htable_mem_4 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s`;
       `!j. j < nblocks ==> read (memory :> bytes128 (word_add in_p (word(16*j)))) s = inblock j`]) ;
    leg_state swp_inv `0x560` `1` ;
    `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
     MAYCHANGE [X19; X20; X21; X22; X23; X24; X25; X26; X27; X28; X29; X30] ,,
     MAYCHANGE [Q0;Q1;Q2;Q3;Q4;Q5;Q6;Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15; Q29; Q30; Q31] ,,
     MAYCHANGE [memory :> bytes(out_p:int64, 16 * nblocks)] ,,
     MAYCHANGE [memory :> bytes(word_add stackpointer (word 160):int64, 64)] ,, MAYCHANGE [events]`]);;

(* FILL input-split at i=0 form (blocks 0..7 = current group 0-3 + prefetch 4-7). *)
let FILL_INPUT_SPLIT_TAC =
  SUBGOAL_THEN
   `read (memory :> bytes128 (word_add in_p (word (16 * 0)))) s0 = inblock 0 /\
    read (memory :> bytes128 (word_add in_p (word (16 * 1)))) s0 = inblock 1 /\
    read (memory :> bytes128 (word_add in_p (word (16 * 2)))) s0 = inblock 2 /\
    read (memory :> bytes128 (word_add in_p (word (16 * 3)))) s0 = inblock 3 /\
    read (memory :> bytes128 (word_add in_p (word (16 * 4)))) s0 = inblock 4 /\
    read (memory :> bytes128 (word_add in_p (word (16 * 5)))) s0 = inblock 5 /\
    read (memory :> bytes128 (word_add in_p (word (16 * 6)))) s0 = inblock 6 /\
    read (memory :> bytes128 (word_add in_p (word (16 * 7)))) s0 = inblock 7`
   STRIP_ASSUME_TAC THENL
    [SUBGOAL_THEN `7 < nblocks` ASSUME_TAC THENL
      [MAP_EVERY (fun t -> TRY(UNDISCH_TAC t))
         [`nblocks DIV 4 = loop_count`; `3 <= loop_count`; `2 <= loop_count`] THEN ARITH_TAC; ALL_TAC] THEN
     REPEAT CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE `16 * 0 = 0`; ARITH_RULE `16 * 1 = 16`; ARITH_RULE `16 * 2 = 32`;
     ARITH_RULE `16 * 3 = 48`; ARITH_RULE `16 * 4 = 64`; ARITH_RULE `16 * 5 = 80`;
     ARITH_RULE `16 * 6 = 96`; ARITH_RULE `16 * 7 = 112`; WORD_ADD_0]) THEN
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o CONV_RULE SPLIT_INPUT_CONV o
     check (fun th -> let c = concl th in is_eq c && free_in `in_p:int64` (lhs c) &&
       can (find_term (fun t -> is_const t && fst(dest_const t) = "bytes128")) (lhs c))));;

(* FILL setup: enter at 0xbc, ghost the lanes, THEN init-abbrev the constant s0-read RHSs (as the body's setup_tac
   does).  This is ESSENTIAL for stepping perf: it abstracts the big constant lanes (word_reversefields 8 (EL k rk),
   ctr_block, etc.) to opaque init_k vars so the per-step WORD_SIMPLE_SUBWORD_CONV stays cheap.  WITHOUT it the FILL
   stepper crawls to a halt in the GHASH region.  This differs from the body's version (which hit DISCH_TAC
   at FILL): only abbreviate RHS terms that are NOT already bare variables (FILL's precond has read X5 s0 = key_p and
   ghost reads whose RHS is a var; ABBREV_TAC on a bare var fails). *)
let fill_setup_tac =
  STRIP_TAC THEN REWRITE_TAC[fst AES256_GCM_ENC_EXEC] THEN
  MAP_EVERY (fun rn -> GHOST_INTRO_TAC (mk_var("ghost_"^rn,`:int64`)) (parse_term("read "^rn))) ghost_lanes256 THEN
  ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV BETA_CONV)) THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_4]) THEN REWRITE_TAC[htable_mem_4] THEN
  FILL_INPUT_SPLIT_TAC;;
  (* No init-abstraction of the rk lanes: abstracting them to init_k would leave opaque init_k in the
     tag_p/ivec_p/rk14 conjuncts (needing un-abbreviation) and turn the aese tower keys into init_k, so the
     body's close_aesNc (which expects word_reversefields 8 (EL k rk)) could not match.  Keeping everything
     concrete lets the aese towers carry real EL-keys (body close_aesNc applies verbatim) and keeps the
     memory reads in closable form; speed comes from the every-15 WORD_SIMPLE_SUBWORD_CONV harvest in the
     stepper, which already bounds the tower. *)

(* FILL merges (body merges256 plus the group-0 counter/input stores below).  The FILL
   region 0xbc..0x558 is straight-line = (0x558-0xbc)/4 = 295 instrs, then sub@0x558 = 296; the cbz@0x55c
   is left to the FILLLEG / LC2_PARTA hops. *)
(* FILL counter-store steps (computed from disasm: step = (addr-0xbc)/4+1 for the stp x,y,[sp,#off] in 0xbc..0x558):
   0x280->s114 #208, 0x2d8->s136 #160, 0x384->s179 #192, 0x39c->s185 #208, 0x3c8->s196 #176, 0x3ec->s205 #192,
   0x4c0->s258 #160, 0x4e0->s266 #176.  (The earlier addresses 0xe8..0x1c0 are before the FILL body proper / in the
   priming that gkeep discards.)  MERGE fires at the store step (sN is post-store). *)
(* The GROUP-0 counter STORES (stp x,y,[sp,#OFF]) happen at steps 12/24/25/26 (0xe8/0x118/0x11c/0x120)
   -- these were MISSING from fill_merges_guess (which only had the group-1 prefetch merges at 114-266).  Without a
   MERGE at the store step, the group-0 counter loads (ldr q3/q4/q31/q8 at steps 23/29/42/52) leave Q3/Q4/Q31/Q8 as
   UNRESOLVED stack reads, so their AES towers stay raw (aese(...(read[sp+OFF] sK)...)) and collapse_q30's GSYM aes14p
   can't fold them -> close_goal7 WORD_BITWISE crash.  Body leg's merges256 fire at the STORE steps; FILL must do the same for group 0. *)
(* The group-0 INPUT^rk14 stores (scalar_rk final-round: eor input-half,rk14-half then
   stp x,y,[sp,#OFF]) also need merging, else the block-completion read (word_xor(aes14p)(read[sp+OFF] s_late))
   leaves read[sp+OFF] s_late unresolved -> AES14P_COMPLETE/SCALAR_RK_RECONSTRUCT can't fire.  Store steps (2nd stp
   per slot): [sp160]@60 (ldr@89->s88), [sp176]@66 (ldr@141->s140), [sp192]@30 (ldr@95->s94).  Block 3's [sp208]@114
   was ALREADY in the list (114,208) -- which is exactly why block 3 folded fully while 0,1,2 stuck.  Add the 3
   missing group-0 input^rk14 merges to mirror block 3's working path. *)
let fill_merges_guess = [(12,160);(24,192);(25,208);(26,176);       (* group-0 COUNTER stores (part 1 fix) *)
                         (30,192);(60,160);(66,176);                (* group-0 INPUT^rk14 stores (part 3 fix; 208@114 below) *)
                         (114,208);(136,160);(179,192);(185,208);(196,176);(205,192);(258,160);(266,176)];;
let NSTEP_FILL = 296;;
(* HARVEST-FAST stepper (q29harvest did 296 steps fast this way; all my per-step-conv variants crawled): the killer
   is per-step WORD_SIMPLE_SUBWORD_CONV over the growing explicit GHASH tower.  Do it ONLY every 15 steps.  Per step:
   just gkeepN-discard (keeps asl bounded) + the CHEAP address-normalization (needed so merges/input-reads match).
   Merges need the normalized counter reads -> run the merge (TRY) right after the cheap address fold. *)
let fill_step_prefix =
  fill_setup_tac THEN
  (fun (asl,w) ->
     (MAP_EVERY (fun k ->
        gkeepF REDSETX256 AES256_GCM_ENC_EXEC ("s"^string_of_int k) THEN
        (* BODY-IDENTICAL per-step conv (WORD_SIMPLE_SUBWORD + NORMALIZE_RELATIVE_ADDRESS + IN_P_ADDR_FOLD): a
           sparser every-15 subword conv would drop the tag_p/ivec_p bytes128 memory reads that conjuncts 3
           and 4 need (the s297 read), so the FILL uses the body's per-step conv, which keeps them at no
           measurable cost. *)
        RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV THENC
                                 ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV THENC IN_P_ADDR_FOLD_CONV)) THEN
        (if List.mem_assoc k fill_merges_guess then TRY(MERGE_CTR128_TAC (List.assoc k fill_merges_guess) ("s"^string_of_int k))
         else ALL_TAC))
       (1--NSTEP_FILL)) (asl,w)) THEN
  RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV THENC
                           ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV THENC
                           IN_P_ADDR_FOLD_CONV));;

(* Step the FILL via the SINGLE-APPLICATION fill_step_prefix (body-identical fast path).  Performance:
   the earlier per-step `do_list (fun k -> e(...))` accumulated 297 goalstack-history entries, each
   a ~700MB goal -> O(n^2) RSS + slowdown (crawled to s190 over ~1hr).  Applying the whole MAP_EVERY inside ONE e()
   keeps NO intermediate history (exactly what step_body_prefix does over 209 steps in ~minutes). *)

(* ---- fill_close_all_256: per-conjunct closer at CONCRETE i=1 (from the v10 probe: 19 conjuncts).  The FILL
   endpoint is swp_inv 1.  First UN-ABBREV the init_k vars (setup abstracted word_reversefields lanes ->
   init_k, which block the tag/ivec/rk14 closers), then dispatch per conjunct.  Concrete i=1 => 4*1+K reduces to
   a numeral; counters via mk_cbv, aesNc via the def + mk_cbv, Q29 via close_goal7-tail (A:=tag0). ---- *)
let unabbrev_init : tactic =
  fun (asl,w) ->
    let ivars = setify(filter (fun v -> try String.length(fst(dest_var v))>=5 && String.sub (fst(dest_var v)) 0 5 = "init_" with _->false)
                              (frees w)) in
    (MAP_EVERY (fun v -> TRY(EXPAND_TAC (fst(dest_var v)))) ivars) (asl,w);;
let fill_close_all_256_c cg10 cg7 : tactic =
  fun (asl,w) ->
    let has c t = can (find_term (fun u -> try fst(dest_const(fst(strip_comb u)))=c with _->false)) t in
    let has_mc t = try can(find_term(fun x->match x with Const("MAYCHANGE",_)->true|_->false)) t with _->false in
    if has_mc w then cg10 (asl,w)
    else if has "aligned_bytes_loaded" w then ASM_REWRITE_TAC[] (asl,w)
    else if is_forall w then
      (REWRITE_TAC[ARITH_RULE `4 * 1 = 4`] THEN close_goal9_i0) (asl,w)
    (* Q29 GHASH conjunct: route DIRECTLY to close_goal7 (like the body leg's close_all_tac).  Performance:
       without this the swpgrp conjunct falls into the else-branch FIRST-list and tries CONV_TAC
       WORD_RULE / WORD_BLAST on the giant concrete-i=1 GHASH tower FIRST -- each ~45min before failing -> the close
       phase took >9h.  close_goal7 ABBREVs the big terms away, so routing straight to it is fast. *)
    else if is_eq w && (has "nist_ghash" (rhs w) || has "swpgrp" (rhs w)) then cg7 (asl,w)
    else
      (unabbrev_init THEN REWRITE_TAC[ZXNEST4; ZX_COUNTER_UD; GSYM WORD_ADD] THEN
       FIRST (map MUST
        [ (* pointers in_p/out_p (already CLOSED in probe, keep for robustness) *)
          close_ptr;
          (* tag_p/ivec_p reads: after unabbrev, = word_reversefields 8 tag0 / ctr_block; the s297 read-fact is in
             asl (gkeep keeps memory reads -- body leg relies on it).  ASM_REWRITE alone closes (NO THEN REFL_TAC --
             ASM_REWRITE already fully closes it, and REFL_TAC on the empty goal would error). *)
          (FIRST_ASSUM ACCEPT_TAC); ASM_REWRITE_TAC[];
          (* X13: word 10 = word_zx(word(4*1+6)) *)
          (REWRITE_TAC[ZXNEST4; ZX_COUNTER_UD] THEN AP_TERM_TAC THEN REWRITE_TAC[GSYM WORD_ADD] THEN AP_TERM_TAC THEN ARITH_TAC);
          (* aesNc Q3=aes11c(6)/Q4=aes7c(8)/Q8=aes1c(7)/Q31=aes6c(9): reduce index, unfold def, AP_TERM to the counter,
             ACCEPT mk_cbv N.  mk_cbv N's LHS IS exactly the sim counter form (correct int64 types). *)
          (REWRITE_TAC[ARITH_RULE `4 * 1 + c = c + 4`; aes11c] THEN
           REPEAT(AP_TERM_TAC ORELSE AP_THM_TAC) THEN ACCEPT_TAC(mk_cbv `(c:num) + 4`));
          (REWRITE_TAC[ARITH_RULE `(c + 4) + 2 = c + 6`; ARITH_RULE `4 * 1 + c + 2 = c + 6`; aes7c] THEN
           REPEAT(AP_TERM_TAC ORELSE AP_THM_TAC) THEN ACCEPT_TAC(mk_cbv `(c:num) + 6`));
          (REWRITE_TAC[ARITH_RULE `(c + 4) + 1 = c + 5`; ARITH_RULE `4 * 1 + c + 1 = c + 5`; aes1c] THEN
           REPEAT(AP_TERM_TAC ORELSE AP_THM_TAC) THEN ACCEPT_TAC(mk_cbv `(c:num) + 5`));
          (REWRITE_TAC[ARITH_RULE `(c + 4) + 3 = c + 7`; ARITH_RULE `4 * 1 + c + 3 = c + 7`; aes6c] THEN
           REPEAT(AP_TERM_TAC ORELSE AP_THM_TAC) THEN ACCEPT_TAC(mk_cbv `(c:num) + 7`));
          (* X1: word_sub(word loop_count)(word 2) = word(loop_count-(1+1)) *)
          (REWRITE_TAC[ARITH_RULE `(1:num)+1=2`] THEN
           SUBGOAL_THEN `2 <= loop_count` ASSUME_TAC THENL
            [MAP_EVERY (fun t -> TRY(UNDISCH_TAC t)) [`3 <= loop_count`; `2 <= loop_count`] THEN ARITH_TAC;
             ALL_TAC] THEN
           ASM_SIMP_TAC[WORD_SUB; GSYM VAL_WORD_1] THEN AP_TERM_TAC THEN
           MAP_EVERY (fun t -> TRY(UNDISCH_TAC t)) [`3 <= loop_count`; `2 <= loop_count`] THEN ARITH_TAC);
          (* [sp160/176/192] input^rk14 lane joins (blocks 4/5/6): after unabbrev, word_join(word_xor..)=word_xor a b *)
          (REWRITE_TAC[JOIN_XOR_LANES] THEN (REFL_TAC ORELSE CONV_TAC WORD_BLAST));
          (* X24/X26 subword pins (block 7 halves): after unabbrev, push subword through xor *)
          (REWRITE_TAC[WORD_SUBWORD_XOR] THEN (REFL_TAC ORELSE CONV_TAC WORD_BLAST));
          (* Q29 GHASH: swpgrp 1 = ghash gt tag0 [cbs]; close_goal7-tail handles (routes via close_all_tac's swpgrp branch) *)
          cg7;
          (* Q2/Q13 h-power reloads *)
          (ASM_REWRITE_TAC[] THEN REFL_TAC);
          ASM_REWRITE_TAC[]; CONV_TAC WORD_BLAST; CONV_TAC WORD_RULE ])) (asl,w);;
let fill_close_all_256 = fill_close_all_256_c close_goal10_b2 close_goal7_fill;;
(* FILL_TO_CBZ: the shared 296-instruction fill, pc+0xbc -> pc+0x55c, under 2 <= loop_count.  All 17
   conjuncts close; conj 9 (output-forall) via close_goal9_i0 (concrete j<4 split + NUM_REDUCE + WORD_ADD_0 for
   block-0's post-indexed store + ZXNEST4/ZX_COUNTER_UD/CTR_BLOCK_BUILD_INSERT/WORD_REVERSEFIELDS_REVERSEFIELDS
   final pass for block-0's counter). *)
let fill_frame = last(snd(strip_comb(snd(dest_imp fill_goal))));;
let fill_pre_state = el 1 (snd(strip_comb(snd(dest_imp fill_goal))));;
let fill_cbz_goal = mk_imp
 (list_mk_conj (map (fun c -> if c = `3 <= loop_count` then `2 <= loop_count` else c) (conjuncts (lhand fill_goal))),
  list_mk_icomb "ensures" [`arm`; fill_pre_state; leg_state swp_inv `0x55c` `1`; fill_frame]);;
let FILL_TO_CBZ = GEN_ALL(prove(fill_cbz_goal,
  fill_step_prefix THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN fill_close_all_256));;

(* One-instruction hops out of a full swp_inv state.  swp_inv_at gives the invariant body for
   ENSURES_SEQUENCE_TAC; hop_init opens the state; after the step every conjunct is either an unchanged read
   (ASM_REWRITE) or the branch PC, resolved from the val fact assumed beforehand. *)
let REFOLD_ABI = REWRITE_TAC[GSYM MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI];;
let swp_inv_at idx = rhs(concl((BETA_CONV THENC REWRITE_CONV[ADD_CLAUSES]) (mk_comb(swp_inv,idx))));;
let hop_init : tactic =
  ENSURES_INIT_TAC "s0" THEN RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_4]) THEN REWRITE_TAC[htable_mem_4];;
let HOP_CLOSE : tactic =
  REPEAT CONJ_TAC THEN
  (FIRST_ASSUM ACCEPT_TAC ORELSE (ASM_REWRITE_TAC[] THEN NO_TAC) ORELSE
   (ASM_REWRITE_TAC[COND_CLAUSES; VAL_WORD_0] THEN CONV_TAC WORD_RULE));;

(* FILLLEG: pc+0xbc -> pc+0x560 for loop_count >= 3 = FILL_TO_CBZ then the cbz@0x55c not taken
   (X1 = word (loop_count - 2), nonzero). *)
let FILLLEG = GEN_ALL(prove(fill_goal,
  STRIP_TAC THEN REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  ENSURES_SEQUENCE_TAC `pc + 0x55c` (swp_inv_at `1`) THEN CONJ_TAC THENL
   [REFOLD_ABI THEN MATCH_MP_TAC FILL_TO_CBZ THEN ASM_REWRITE_TAC[] THEN
    TRY(UNDISCH_TAC `3 <= loop_count` THEN ARITH_TAC);
    hop_init THEN
    SUBGOAL_THEN `val (word (loop_count - 2):int64) = loop_count - 2` ASSUME_TAC THENL
     [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
      MAP_EVERY (fun t -> TRY(UNDISCH_TAC t)) [`nblocks DIV 4 = loop_count`; `16 * nblocks < 2 EXP 64`] THEN
      ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `~(val (word (loop_count - 2):int64) = 0)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `3 <= loop_count` THEN ARITH_TAC; ALL_TAC] THEN
    ARM_STEPS_TAC AES256_GCM_ENC_EXEC [1] THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN HOP_CLOSE]));;

(* LC2_PARTA: pc+0xbc -> pc+0x8a8 for loop_count = 2 = FILL_TO_CBZ then the cbz@0x55c taken (X1 = word 0).
   The waypoint is swp_inv at the CONCRETE index 1 (= loop_count - 1 for loop_count = 2); LEG_LC2 bridges
   the index before applying DRAINLEG_8A8. *)
let lc2a_precond =
  list_mk_conj ((filter (fun c -> c <> `3 <= loop_count`) (conjuncts (lhand fill_goal))) @ [`loop_count = 2`]);;
let lc2_waypoint = leg_state swp_inv `0x8a8` `1`;;
let lc2a_goal = mk_imp(lc2a_precond, list_mk_icomb "ensures" [`arm`; fill_pre_state; lc2_waypoint; fill_frame]);;
let LC2_PARTA = prove(lc2a_goal,
  STRIP_TAC THEN REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  ENSURES_SEQUENCE_TAC `pc + 0x55c` (swp_inv_at `1`) THEN CONJ_TAC THENL
   [REFOLD_ABI THEN MATCH_MP_TAC FILL_TO_CBZ THEN ASM_REWRITE_TAC[] THEN
    TRY(UNDISCH_TAC `loop_count = 2` THEN ARITH_TAC);
    hop_init THEN
    SUBGOAL_THEN `val (word (loop_count - (1 + 1)):int64) = 0` ASSUME_TAC THENL
     [UNDISCH_TAC `loop_count = 2` THEN DISCH_THEN SUBST1_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC[VAL_WORD_0];
      ALL_TAC] THEN
    ARM_STEPS_TAC AES256_GCM_ENC_EXEC [1] THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN HOP_CLOSE]);;

(* ========== LEG: bodyleg ========== *)

(* ========================================================================= *)
(* Closers (the AES-128 closers re-indexed for the four extra rounds).         *)
(* ========================================================================= *)

(* ABBREV every maximal `word_pmul a b` subterm of the goal as a fresh int128 var.  After this, BITBLAST sees
   only word_join/word_subword/word_xor SHUFFLE over abstract int128s (fast, ~0.5s, 385 BDD vars) instead of
   modelling the 64x64 carryless-multiply circuit (30GB blowup).  This is the key to the 256 reduce closer. *)

(* collapse_q30 + close_goal7 (Q30 GHASH tag reduce reconstruction), 256 re-index. *)

(* swpgrp-invariant close_goal7: the invariant Q29 = swpgrp gt tag0 i lives in the byteswapped GHASH
   domain (head-ext byteswaps it each iteration).  The body-end goal is <machine reduce> = swpgrp gt tag0 (i+1) blk.
   collapse_q30 folds the LHS keystreams; no acc-cleanup (the acc = word_subword(word_join(swpgrp i)(swpgrp i))(64,128) =
   byteswap128(swpgrp i) is EXACTLY the seed swpgrp(SUC i) wants -- do NOT collapse it to clean).  Then RECONSTRUCT folds
   the reduce -> polyval_reduce_g2(byteswap128(swpgrp i)-seed lanes), and CORE_REDUCE_GHASH's recipe closes it =
   ghash gt (byteswap128(swpgrp i))[cbs] = swpgrp(SUC i) by the swpgrp SUC-def.  REFLEXIVE -- no byteswap-commute. *)

let BODYLEG = prove(body_goal, step_body_tac THEN REPEAT CONJ_TAC THEN close_all_body);;
(* self-report: confirm the loosened bound i < loop_count - 1 is in the goal, and no axioms crept in. *)

(* ========== LEG: drain ========== *)

(* ========================================================================= *)
(* Closers (the AES-128 closers re-indexed for the four extra rounds).         *)
(* ========================================================================= *)

(* ABBREV every maximal `word_pmul a b` subterm of the goal as a fresh int128 var.  After this, BITBLAST sees
   only word_join/word_subword/word_xor SHUFFLE over abstract int128s (fast, ~0.5s, 385 BDD vars) instead of
   modelling the 64x64 carryless-multiply circuit (30GB blowup).  This is the key to the 256 reduce closer. *)

(* collapse_q30 + close_goal7 (Q30 GHASH tag reduce reconstruction), 256 re-index. *)

(* swpgrp-invariant close_goal7: the invariant Q29 = swpgrp gt tag0 i lives in the byteswapped GHASH
   domain (head-ext byteswaps it each iteration).  The body-end goal is <machine reduce> = swpgrp gt tag0 (i+1) blk.
   collapse_q30 folds the LHS keystreams; no acc-cleanup (the acc = word_subword(word_join(swpgrp i)(swpgrp i))(64,128) =
   byteswap128(swpgrp i) is EXACTLY the seed swpgrp(SUC i) wants -- do NOT collapse it to clean).  Then RECONSTRUCT folds
   the reduce -> polyval_reduce_g2(byteswap128(swpgrp i)-seed lanes), and CORE_REDUCE_GHASH's recipe closes it =
   ghash gt (byteswap128(swpgrp i))[cbs] = swpgrp(SUC i) by the swpgrp SUC-def.  REFLEXIVE -- no byteswap-commute. *)

(* ========================================================================= *)
(* DRAIN leg: swp_inv (loop_count-1) @ 0x8a8  ->  bridge @ 0xdd0.          *)
(* The WHILE exits with the last body landing inv(loop_count-1)@0x8a4; cbnz    *)
(* x1@0x8a4 NOT taken (X1=word(loop_count-((loop_count-1)+1))=word 0) -> 0x8a8.*)
(* DRAIN 0x8a8..0xdcc: reduces the last group (blocks 4(lc-1)..4lc-1) into Q29 *)
(* -> Q30 = byteswap128(nist_ghash..(4*loop_count)); stores last-group ct.     *)
(* Bridge @0xdd0 (Lloop_unrolled_end) = body-only enc256 0x3fc "break" state.  *)
(* ========================================================================= *)

(* drain bridge lemmas (list-split + swpgrp->nist_ghash). *)
let LIST_OF_SEQ_APPEND = prove
 (`!n f m. list_of_seq f (m + n) =
           APPEND (list_of_seq f m) (list_of_seq (\i. f(m+i)) n)`,
  GEN_TAC THEN ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[ADD_CLAUSES; LIST_OF_SEQ; APPEND; o_THM; ETA_AX]);;
let SWPGRP_IS_NIST_GHASH = prove
 (`!h acc i blk.
       swpgrp (ghash_twist h) acc i blk =
       nist_ghash h acc (list_of_seq blk (4 * i))`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN GEN_TAC THENL
   [REWRITE_TAC[swpgrp; MULT_CLAUSES; LIST_OF_SEQ; nist_ghash];
    REWRITE_TAC[ARITH_RULE `4 * SUC i = 4 * i + 4`] THEN
    REWRITE_TAC[LIST_OF_SEQ_APPEND] THEN REWRITE_TAC[NIST_GHASH_APPEND] THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[swpgrp] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[LIST_OF_SEQ_CLAUSES] THEN REWRITE_TAC[ARITH_RULE `4*i+0 = 4*i`] THEN
    REWRITE_TAC[NIST_GHASH_IS_POLYVAL]]);;

(* bridge state @ 0xdd0 (= body-only enc256 0x3fc break state, indexed at 4*loop_count). *)
let drain_bridge = mk_abs(`s:armstate`, list_mk_conj
 [`aligned_bytes_loaded s (word pc) aes256_gcm_enc_mc`;
  `read PC s = word (pc + 0xdd0)`;
  `read X0 s = word_add in_p (word (64 * loop_count))`;
  `read X2 s = word_add out_p (word (64 * loop_count))`;
  `read X3 s = tag_p`; `read X4 s = ivec_p`; `read X6 s = htable_p`; `read SP s = stackpointer`;
  `read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0`;
  `read (memory :> bytes128 ivec_p) s = word_reversefields 8 (ctr_block nonce c)`;
  `read X13 s = word_zx (word (4 * loop_count + c):int32):int64`;
  `read X15 s = word(len_bits DIV 8)`;
  (* NB: X1 is NOT constrained here.  The steady/drain path leaves X1=word 0 (loop decremented it) but the
     iter_1 (loop_count=1) path leaves X1=word 1, and the tail (0xdd0+) never reads X1 (tail_inv uses X16).
     So X1 is dead at this seam; dropping it lets BOTH the drain and iter_1 legs reach this same bridge. *)
  `read X16 s = word loop_remain`;
  (* round-key + h-power + counter-lane registers held live at the drain->tail seam (tail loop's AES+GHASH need
     them; swp_inv carries them + the drain body preserves them).  tail_inv @ i=0 requires this exact set. *)
  `read Q18 s = word_reversefields 8 (EL 0 rk)`; `read Q19 s = word_reversefields 8 (EL 1 rk)`;
  `read Q20 s = word_reversefields 8 (EL 2 rk)`; `read Q21 s = word_reversefields 8 (EL 3 rk)`;
  `read Q22 s = word_reversefields 8 (EL 4 rk)`; `read Q23 s = word_reversefields 8 (EL 5 rk)`;
  `read Q24 s = word_reversefields 8 (EL 6 rk)`; `read Q25 s = word_reversefields 8 (EL 7 rk)`;
  `read Q26 s = word_reversefields 8 (EL 8 rk)`; `read Q27 s = word_reversefields 8 (EL 9 rk)`;
  `read Q28 s = word_reversefields 8 (EL 10 rk)`; `read Q15 s = word_reversefields 8 (EL 11 rk)`;
  `read Q16 s = word_reversefields 8 (EL 12 rk)`; `read Q17 s = word_reversefields 8 (EL 13 rk)`;
  `read X20 s = word_subword (word_reversefields 8 (EL 14 rk):int128) (0,64):int64`;
  `read X21 s = word_subword (word_reversefields 8 (EL 14 rk):int128) (64,64):int64`;
  `read Q7 s = word 13979173243358019584`;
  `read X11 s = word_subword (word_reversefields 8 (ctr_block nonce c):int128) (0,64):int64`;
  `read X12 s = word_zx (word_zx (word_subword
       (word_reversefields 8 (ctr_block nonce c):int128) (64,64):int64):int32):int64`;
  (* NB Q12/Q14 are NOT carried here: the drain leaves them as computed reduce-lane values, and the TAIL RELOADS
     them from htable at its first two instrs (ldr q12,[x6] @0xdd0 ; ldr q14,[x6,#16] @0xdd8) -- htable_mem_4 (below)
     supplies the values, so tail_inv's Q12/Q14 are established by the tail's own stepping, not by the bridge. *)
  `read Q30 s = byteswap128 (nist_ghash (aes256_cipher (word 0) rk) tag0
                  (list_of_seq (aes256_nist_cipher_block c nonce rk inblock) (4 * loop_count)))`;
  `htable_mem_4 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s`;
  `!j. j < nblocks ==> read (memory :> bytes128 (word_add in_p (word(16*j)))) s = inblock j`;
  `!j. j < 4 * loop_count ==> read (memory :> bytes128 (word_add out_p (word(16*j)))) s =
           word_xor (aes256_ctr_block c nonce rk j) (inblock j)`]);;

(* ---- DRAIN goal: swp_inv (loop_count-1) @0x8a4 -> drain_bridge @0xdd0.  Broad frame (MAYCHANGEs the
   speculative next-group AES partials Q3/Q4/Q8/Q31, all working regs, out_p bytes, stack). ---- *)
let drain_goal = mk_imp
 (`([EL 0 rk; EL 1 rk; EL 2 rk; EL 3 rk; EL 4 rk; EL 5 rk; EL 6 rk; EL 7 rk;
     EL 8 rk; EL 9 rk; EL 10 rk; EL 11 rk; EL 12 rk; EL 13 rk; EL 14 rk]:(int128)list = rk) /\
   len_bits DIV 128 = nblocks /\ nblocks DIV 4 = loop_count /\ nblocks MOD 4 = loop_remain /\
   2 <= loop_count /\ 16 * nblocks < 2 EXP 64 /\ aligned 16 (stackpointer:int64) /\
   nonoverlapping (out_p:int64,16 * nblocks) (word pc:int64,3860) /\
   nonoverlapping (out_p:int64,16 * nblocks) (in_p:int64,16 * nblocks) /\
   nonoverlapping (out_p:int64,16 * nblocks) (htable_p:int64,192) /\
   nonoverlapping (out_p:int64,16 * nblocks) (tag_p:int64,16) /\
   nonoverlapping (out_p:int64,16 * nblocks) (ivec_p:int64,16) /\
   nonoverlapping (out_p:int64,16*nblocks) (word_add stackpointer (word 160):int64,64) /\
   nonoverlapping (tag_p:int64,16) (word pc:int64,3860) /\
   nonoverlapping (tag_p:int64,16) (in_p:int64,16*nblocks) /\
   nonoverlapping (tag_p:int64,16) (htable_p:int64,192) /\
   nonoverlapping (tag_p:int64,16) (word_add stackpointer (word 160):int64,64) /\
   nonoverlapping (ivec_p:int64,16) (word pc:int64,3860) /\
   nonoverlapping (ivec_p:int64,16) (in_p:int64,16*nblocks) /\
   nonoverlapping (ivec_p:int64,16) (htable_p:int64,192) /\
   nonoverlapping (ivec_p:int64,16) (word_add stackpointer (word 160):int64,64) /\
   nonoverlapping (tag_p:int64,16) (ivec_p:int64,16) /\
   nonoverlapping (word_add stackpointer (word 160):int64,64) (word pc:int64,3860) /\
   nonoverlapping (word_add stackpointer (word 160):int64,64) (in_p:int64,16*nblocks) /\
   nonoverlapping (word_add stackpointer (word 160):int64,64) (htable_p:int64,192)`,
  list_mk_icomb "ensures" [`arm`;
    leg_state swp_inv `0x8a4` `loop_count - 1` ;
    drain_bridge ;
    `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
     MAYCHANGE [X19; X20; X21; X22; X23; X24; X25; X26; X27; X28; X29; X30] ,,
     MAYCHANGE [Q0;Q1;Q2;Q3;Q4;Q5;Q6;Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15; Q29; Q30; Q31] ,,
     MAYCHANGE [memory :> bytes(out_p:int64, 16 * nblocks)] ,,
     MAYCHANGE [memory :> bytes(word_add stackpointer (word 160):int64, 64)] ,, MAYCHANGE [events]`]);;

(* DRAIN Q30 closer (conj 2): word_subword(word_join <hi> <lo>)(64,128) [outer Q30 byteswap of the reduce] =
   byteswap128(nist_ghash..(4*(m+1))).  The INNER reduce (acc seed byteswap128(swpgrp m), last group blocks) is exactly
   close_goal7's LHS (proves = swpgrp(m+1)).  STRATEGY: (1) GSYM SWPGRP_IS_NIST_GHASH bridges RHS nist_ghash..(4*(m+1))
   -> byteswap128(swpgrp gt tag0 (m+1) ncb) [after 4*(m+1) matches the lemma's 4*i with i:=m+1]; (2) both sides are now
   the packed/byteswapped reduce vs byteswap128(swpgrp(m+1)); reduce to <inner reduce> = swpgrp(m+1) via the
   word_subword(word_join)(64,128) outer-strip (128 reducelast model) + AP_TERM; (3) close_goal7 (i:=m) finishes. *)
(* drain_close_q30: the drain Q30 conj = word_subword(word_join <reduce-lanes>)(64,128) = byteswap128(nist_ghash..(4(m+1))).
   collapse_q30 normalizes 4*(m+1)->4*m+4 on the RHS, so bridge with 4*m+4->4*(m+1) first, then GSYM SWPGRP_IS_NIST_GHASH
   -> byteswap128(swpgrp gt tag0 (m+1)).  close_goal7 was written for RHS = swpgrp(i+1) (bare); the drain has the outer
   byteswap on BOTH sides.  HYPOTHESIS (test on real run, since g2 is loosely-typed): close_goal7's own machinery
   (collapse_q30 + ACC_JOIN_BYTESWAP + WORD_SUBWORD_BYTESWAP128 + the byteswap-domain reduce) already handles the
   byteswapped form, so bridging the RHS then calling close_goal7 closes it.  If MK_COMB fails on the real (typed) goal,
   fall back to the full reducelast_close_ghash port (byteswap-strip + MATCH_MP BITBLAST after the reduce). *)
(* drain_close_q30 v3: self-contained (does NOT reuse close_goal7, whose EQ_TRANS tail assumes a BARE reduce=swpgrp(i+1);
   the drain has byteswap128(reduce)=byteswap128(swpgrp(m+1)) -- one byteswap layer more).  Structure = close_goal7's
   proven reduce-prefix (m-indexed) + the AES-128 reducelast byteswap-strip tail + swpgrp SUC-fold.
   Step (1) bridge RHS 4m+4->4(m+1) then GSYM SWPGRP -> byteswap128(swpgrp(m+1)); step (2) collapse_q30 + unfold
   swpgrp(SUC m) + ABBREV sofar=swpgrp m, bsofar=byteswap128 sofar + reduce-normalize (SAME as close_goal7 but m-indexed);
   step (3) the goal is now byteswap128(polyval_reduce_g2 P1 P2 P3) = byteswap128(ghash_polyval_acc gt sofar [cbs]);
   strip outer byteswap128 (both sides word_subword(word_join)(64,128) via byteswap128 def + strip_lem + MATCH_MP BITBLAST)
   reducing to polyval_reduce_g2(P1 P2 P3) = ghash_polyval_acc gt sofar [cbs]; step (4) EQ_TRANS to CORE order + MK_COMB
   + WORD_BITWISE + MATCH_ACCEPT CORE_REDUCE_GHASH (A:=sofar).  Same tail as close_goal7 from the EQ_TRANS on. *)
let drain_close_q30_c collapse : tactic =
  fun (asl,w) ->
    (GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [ARITH_RULE `4 * m + 4 = 4 * (m + 1)`] THEN
     GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [GSYM SWPGRP_IS_NIST_GHASH] THEN
     (* --- close_goal7 reduce-prefix, m-indexed --- *)
     collapse THEN
     GEN_REWRITE_TAC (RAND_CONV o TOP_DEPTH_CONV) [ARITH_RULE `m + 1 = SUC m`] THEN
     GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [CONJUNCT2 swpgrp] THEN
     ABBREV_TAC `sofar = swpgrp (ghash_twist (aes256_cipher (word 0) rk)) tag0 m (aes256_nist_cipher_block c nonce rk inblock)` THEN
     REWRITE_TAC[ACC_JOIN_BYTESWAP] THEN
     ABBREV_TAC `bsofar:int128 = byteswap128 (sofar:int128)` THEN
     REWRITE_TAC[WORD_SUBWORD_REVERSEFIELDS] THEN
     SIMP_TAC[WORD_JOIN_COMBINE_LEMMA; ARITH] THEN
     REWRITE_TAC[WORD_SUBWORD_XOR] THEN
     REWRITE_TAC[WORD_SUBWORD_BYTESWAP128] THEN
     CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
     REWRITE_TAC[WORD_SUBWORD_XOR] THEN
     CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
     MAP_EVERY ABBREV_TAC
      [`cipherblock_0 = aes256_nist_cipher_block c nonce rk inblock (4 * m)`;
       `cipherblock_1 = aes256_nist_cipher_block c nonce rk inblock (4 * m + 1)`;
       `cipherblock_2 = aes256_nist_cipher_block c nonce rk inblock (4 * m + 2)`;
       `cipherblock_3 = aes256_nist_cipher_block c nonce rk inblock (4 * m + 3)`;
       `h0 = h_power (ghash_twist (aes256_cipher (word 0) rk)) 0`;
       `h1 = h_power (ghash_twist (aes256_cipher (word 0) rk)) 1`;
       `h2 = h_power (ghash_twist (aes256_cipher (word 0) rk)) 2`;
       `h3 = h_power (ghash_twist (aes256_cipher (word 0) rk)) 3`] THEN
     REWRITE_TAC[GSYM WORD_SUBWORD_XOR] THEN
     REWRITE_TAC[byteswap128] THEN
     REWRITE_TAC[RECONSTRUCT_POLYVAL_REDUCE_G2] THEN
     EXPAND_TAC "bsofar" THEN
     REWRITE_TAC[WORD_SUBWORD_BYTESWAP128] THEN
     REWRITE_TAC[GSYM WORD_SUBWORD_XOR] THEN
     REWRITE_TAC[CMID_LOHI; CMID_HILO] THEN
     MAP_EVERY EXPAND_TAC ["h0"; "h1"; "h2"; "h3"] THEN
     (* --- 128 reducelast byteswap-strip: goal now byteswap128(polyval_reduce_g2..) = byteswap128(ghash_polyval_acc..) --- *)
     REWRITE_TAC [byteswap128; WORD_BLAST
       `word_subword((word_join:int128->int128->int256) h l) (64,128):int128 =
        word_join (word_subword h (0,64):int64) (word_subword l (64,64):int64)`] THEN
     MATCH_MP_TAC(BITBLAST_RULE
      `x:int128 = y
       ==> word_join (word_subword x (0,64):int64) (word_subword x (64,64):int64):int128 =
           word_join (word_subword y (0,64):int64) (word_subword y (64,64):int64):int128`) THEN
     (* --- close_goal7's EQ_TRANS tail (CORE order reconcile), m-indexed --- *)
     MATCH_MP_TAC EQ_TRANS THEN
     EXISTS_TAC
      `polyval_reduce_g2
         (word_xor (word_pmul (word_subword (cipherblock_3:int128) (0,64):int64) (word_subword (h_power (ghash_twist (aes256_cipher (word 0) rk)) 0) (0,64):int64))
         (word_xor (word_pmul (word_subword (cipherblock_2:int128) (0,64):int64) (word_subword (h_power (ghash_twist (aes256_cipher (word 0) rk)) 1) (0,64):int64))
         (word_xor (word_pmul (word_subword (cipherblock_1:int128) (0,64):int64) (word_subword (h_power (ghash_twist (aes256_cipher (word 0) rk)) 2) (0,64):int64))
         (word_pmul (word_subword (word_xor (sofar:int128) cipherblock_0) (0,64):int64) (word_subword (h_power (ghash_twist (aes256_cipher (word 0) rk)) 3) (0,64):int64)))))
         (word_xor (word_pmul (word_subword cipherblock_3 (64,64):int64) (word_subword (h_power (ghash_twist (aes256_cipher (word 0) rk)) 0) (64,64):int64))
         (word_xor (word_pmul (word_subword cipherblock_2 (64,64):int64) (word_subword (h_power (ghash_twist (aes256_cipher (word 0) rk)) 1) (64,64):int64))
         (word_xor (word_pmul (word_subword cipherblock_1 (64,64):int64) (word_subword (h_power (ghash_twist (aes256_cipher (word 0) rk)) 2) (64,64):int64))
         (word_pmul (word_subword (word_xor sofar cipherblock_0) (64,64):int64) (word_subword (h_power (ghash_twist (aes256_cipher (word 0) rk)) 3) (64,64):int64)))))
         (word_xor (word_pmul (karatsuba_mid cipherblock_3) (karatsuba_mid (h_power (ghash_twist (aes256_cipher (word 0) rk)) 0)))
         (word_xor (word_pmul (karatsuba_mid cipherblock_2) (karatsuba_mid (h_power (ghash_twist (aes256_cipher (word 0) rk)) 1)))
         (word_xor (word_pmul (karatsuba_mid cipherblock_1) (karatsuba_mid (h_power (ghash_twist (aes256_cipher (word 0) rk)) 2)))
         (word_pmul (karatsuba_mid (word_xor sofar cipherblock_0)) (karatsuba_mid (h_power (ghash_twist (aes256_cipher (word 0) rk)) 3))))))` THEN
     CONJ_TAC THENL
      [MK_COMB_TAC THENL
        [MK_COMB_TAC THENL
          [AP_TERM_TAC THEN CONV_TAC WORD_BITWISE_RULE;
           CONV_TAC WORD_BITWISE_RULE];
         CONV_TAC WORD_BITWISE_RULE];
       MATCH_ACCEPT_TAC CORE_REDUCE_GHASH]) (asl,w);;
let drain_close_q30 = drain_close_q30_c collapse_q30_gi;;

(* drain per-conjunct closer: route the Q30 conjunct (rhs has byteswap128 + nist_ghash) to drain_close_q30; else close_all_tac.
   PERF: the round-key/scalar/h-power register conjuncts added to drain_bridge (read Qk = word_reversefields 8 (EL k rk),
   X20/X21/X11/X12, Q7, Q12/Q14) are carried UNCHANGED in the drain assumptions -- close them by a CHEAP ASM/ACCEPT
   route FIRST, so they never enter close_all_tac's expensive FIRST(map MUST [word_blast/aes-reconstruct...]) gauntlet
   (21 such conjuncts x that gauntlet blew past the 1h timeout). *)
let drain_close_all_c dq30 closeall : tactic =
  fun (asl,w) ->
    let has c t = can (find_term (fun u -> try fst(dest_const(fst(strip_comb u)))=c with _->false)) t in
    if is_eq w && has "nist_ghash" (rhs w) && has "byteswap128" (rhs w) then dq30 (asl,w)
    else if is_eq w &&
            (has "word_reversefields" (rhs w) || has "karatsuba_mid" (rhs w) ||
             (is_comb(rhs w) && fst(dest_const(fst(strip_comb(rhs w)))) = "word") ||
             has "h_power" (rhs w))
    then (FIRST_ASSUM ACCEPT_TAC ORELSE ASM_REWRITE_TAC[] ORELSE closeall) (asl,w)
    else closeall (asl,w);;
let drain_close_all = drain_close_all_c drain_close_q30 close_all_drain;;

(* ---- DRAINLEG_8A8: the drain proper, pc+0x8a8 -> drain_bridge, from swp_inv (loop_count-1) with X1 =
   word 0.  drain_goal_8a8 = drain_goal with entry PC 0x8a4 -> 0x8a8.  Simulated ONCE and shared: the WHILE
   exit (DRAINLEG, cbnz@0x8a4 not taken) and the loop_count = 2 path (LEG_LC2, cbz@0x55c taken) both
   land here. ---- *)
let drain_goal_8a8 =
  let pre8a8 = leg_state swp_inv `0x8a8` `loop_count - 1` in
  mk_imp(lhand drain_goal,
    list_mk_icomb "ensures" [`arm`; pre8a8; drain_bridge;
      last(snd(strip_comb(snd(dest_imp drain_goal))))]);;

(* setup for the 0x8a8 entry: m = loop_count - 1, X1 -> word 0, input-split the LAST group (blocks 4m..4m+3). *)
let drain_setup_tac_8a8 =
  STRIP_TAC THEN REWRITE_TAC[fst AES256_GCM_ENC_EXEC] THEN
  MAP_EVERY (fun rn -> GHOST_INTRO_TAC (mk_var("ghost_"^rn,`:int64`)) (parse_term("read "^rn))) ghost_lanes256 THEN
  ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV BETA_CONV)) THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_4]) THEN REWRITE_TAC[htable_mem_4] THEN
  ABBREV_TAC `m = loop_count - 1` THEN
  SUBGOAL_THEN `loop_count = m + 1` ASSUME_TAC THENL
   [EXPAND_TAC "m" THEN UNDISCH_TAC `2 <= loop_count` THEN ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(fun th ->
    if can (term_match [] `read X1 s0 = word (loop_count - (m + 1))`) (concl th)
    then ASSUME_TAC(REWRITE_RULE[ASSUME `loop_count = m + 1`; ARITH_RULE `(m + 1) - (m + 1) = 0`] th)
    else NO_TAC) THEN
  SUBGOAL_THEN
   `read (memory :> bytes128 (word_add in_p (word (16 * (4*m+0))))) s0 = inblock (4*m+0) /\
    read (memory :> bytes128 (word_add in_p (word (16 * (4*m+1))))) s0 = inblock (4*m+1) /\
    read (memory :> bytes128 (word_add in_p (word (16 * (4*m+2))))) s0 = inblock (4*m+2) /\
    read (memory :> bytes128 (word_add in_p (word (16 * (4*m+3))))) s0 = inblock (4*m+3)`
   STRIP_ASSUME_TAC THENL
    [SUBGOAL_THEN `4*m+3 < nblocks` ASSUME_TAC THENL
      [MAP_EVERY (fun t -> TRY(UNDISCH_TAC t))
         [`nblocks DIV 4 = loop_count`; `loop_count = m + 1`; `2 <= loop_count`] THEN ARITH_TAC; ALL_TAC] THEN
     REPEAT CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE `16 * (4*m+0) = 64*m`; ARITH_RULE `16 * (4*m+1) = 64*m+16`;
     ARITH_RULE `16 * (4*m+2) = 64*m+32`; ARITH_RULE `16 * (4*m+3) = 64*m+48`]) THEN
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o CONV_RULE SPLIT_INPUT_CONV o
     check (fun th -> let c = concl th in is_eq c && free_in `in_p:int64` (lhs c) &&
       can (find_term (fun t -> is_const t && fst(dest_const t) = "bytes128")) (lhs c))));;
(* the only stp[sp] counter-store site in 0x8a8..0xa8c is step 24; 0xa8c is the b dd0 that skips the loop body. *)
let drain_merges_8a8 = [(24,208)];;
let NSTEP_DRAIN_8a8 = 122;;
let drain_step_prefix_8a8 =
  drain_setup_tac_8a8 THEN
  (fun (asl,w) ->
     (MAP_EVERY (fun k ->
        gkeepN REDSETX256 AES256_GCM_ENC_EXEC ("s"^string_of_int k) THEN
        RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV THENC
                                 ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV THENC IN_P_ADDR_FOLD_CONV)) THEN
        (if List.mem_assoc k drain_merges_8a8 then TRY(MERGE_CTR128_TAC (List.assoc k drain_merges_8a8) ("s"^string_of_int k))
         else ALL_TAC))
       (1--NSTEP_DRAIN_8a8)) (asl,w)) THEN
  RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV THENC
                           ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV THENC IN_P_ADDR_FOLD_CONV));;
let DRAINLEG_8A8 = GEN_ALL(prove(drain_goal_8a8,
  drain_step_prefix_8a8 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN drain_close_all));;

(* DRAINLEG: entry at the cbnz@0x8a4 with swp_inv (loop_count-1), X1 = word 0 so it is not taken,
   then DRAINLEG_8A8.  GEN_ALL so composition MATCH_MP_TAC leaves the ?key_p etc. *)
let DRAINLEG = GEN_ALL(prove(drain_goal,
  STRIP_TAC THEN REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  ENSURES_SEQUENCE_TAC `pc + 0x8a8` (swp_inv_at `loop_count - 1`) THEN CONJ_TAC THENL
   [hop_init THEN
    SUBGOAL_THEN `loop_count - ((loop_count - 1) + 1) = 0`
      (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th]) THENL
     [UNDISCH_TAC `2 <= loop_count` THEN ARITH_TAC; ALL_TAC] THEN
    ARM_STEPS_TAC AES256_GCM_ENC_EXEC [1] THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN HOP_CLOSE;
    REFOLD_ABI THEN MATCH_MP_TAC DRAINLEG_8A8 THEN ASM_REWRITE_TAC[]]));;

(* ========== LEG: tail ========== *)

(* ========================================================================= *)
(* Closers (the AES-128 closers re-indexed for the four extra rounds).         *)
(* ========================================================================= *)

(* tail final-state per-conjunct router (mirrors DRAIN's drain_close_all shape): AFTER the goal has been
   ENSURES_FINAL_STATE'd, gval-abstracted, ivec-split, normalized and ASM_REWRITTEN, split the postcondition
   conjunction and route each conjunct by shape.  The naive "REPEAT CONJ_TAC THEN ... WORD_BLAST" crashes
   because the MAYCHANGE frame conjunct reaches WORD_BLAST -- close_goal10 handles the frame; the out-forall
   closes by assumption (postamble does not write out_p, so the bridge/inv forall survives to the final state);
   tag/ivec close by the byteswap/ctr word identity. *)
let tail_final_close : tactic =
  REPEAT CONJ_TAC THEN
  FIRST
   [close_goal10_b2;
    FIRST_ASSUM MATCH_ACCEPT_TAC;
    (REWRITE_TAC[byteswap128; ctr_block] THEN
     REWRITE_TAC[ADD_ASSOC; ZX_COUNTER_UD; CTR_ZX_NORM] THEN
     CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN CONV_TAC WORD_BLAST)];;

(* ABBREV every maximal `word_pmul a b` subterm of the goal as a fresh int128 var.  After this, BITBLAST sees
   only word_join/word_subword/word_xor SHUFFLE over abstract int128s (fast, ~0.5s, 385 BDD vars) instead of
   modelling the 64x64 carryless-multiply circuit (30GB blowup).  This is the key to the 256 reduce closer. *)

(* collapse_q30 + close_goal7 (Q30 GHASH tag reduce reconstruction), 256 re-index. *)

(* swpgrp-invariant close_goal7: the invariant Q29 = swpgrp gt tag0 i lives in the byteswapped GHASH
   domain (head-ext byteswaps it each iteration).  The body-end goal is <machine reduce> = swpgrp gt tag0 (i+1) blk.
   collapse_q30 folds the LHS keystreams; no acc-cleanup (the acc = word_subword(word_join(swpgrp i)(swpgrp i))(64,128) =
   byteswap128(swpgrp i) is EXACTLY the seed swpgrp(SUC i) wants -- do NOT collapse it to clean).  Then RECONSTRUCT folds
   the reduce -> polyval_reduce_g2(byteswap128(swpgrp i)-seed lanes), and CORE_REDUCE_GHASH's recipe closes it =
   ghash gt (byteswap128(swpgrp i))[cbs] = swpgrp(SUC i) by the swpgrp SUC-def.  REFLEXIVE -- no byteswap-commute. *)

(* ========================================================================= *)
(* DRAIN leg: swp_inv (loop_count-1) @ 0x8a8  ->  bridge @ 0xdd0.          *)
(* The WHILE exits with the last body landing inv(loop_count-1)@0x8a4; cbnz    *)
(* x1@0x8a4 NOT taken (X1=word(loop_count-((loop_count-1)+1))=word 0) -> 0x8a8.*)
(* DRAIN 0x8a8..0xdcc: reduces the last group (blocks 4(lc-1)..4lc-1) into Q29 *)
(* -> Q30 = byteswap128(nist_ghash..(4*loop_count)); stores last-group ct.     *)
(* Bridge @0xdd0 (Lloop_unrolled_end) = body-only enc256 0x3fc "break" state.  *)
(* ========================================================================= *)

(* ========================================================================= *)
(* TAIL leg: drain_bridge @0xdd0 -> crypto-complete @0xee4 (tag+ivec+out stored, pre-epilogue). *)
(* Structure ports body-only enc256 tail (scalar_rk.ml 1258-1508): loop_remain WHILE @0xde0/0xecc + tag-store postamble. *)
(* ========================================================================= *)

(* tail loop invariant @0xde0 (= drain_bridge + loop index i + Q12/Q14 h-power pins for the single-block GHASH). *)
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
    read X20 s = word_subword (word_reversefields 8 (EL 14 rk):int128) (0,64):int64 /\
    read X21 s = word_subword (word_reversefields 8 (EL 14 rk):int128) (64,64):int64 /\
    read Q7 s = word 13979173243358019584 /\
    read X11 s = word_subword (word_reversefields 8 (ctr_block nonce c):int128) (0,64):int64 /\
    read X12 s = word_zx (word_zx (word_subword
        (word_reversefields 8 (ctr_block nonce c):int128) (64,64):int64):int32):int64 /\
    read X13 s = word_zx (word (4 * loop_count + i + c):int32):int64 /\
    read X15 s = word(len_bits DIV 8) /\ read X16 s = word(loop_remain - i) /\
    read Q30 s = byteswap128 (nist_ghash (aes256_cipher (word 0) rk) tag0
                   (list_of_seq (aes256_nist_cipher_block c nonce rk inblock) (4 * loop_count + i))) /\
    htable_mem_4 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s /\
    read Q12 s = byteswap128 (h_power (ghash_twist (aes256_cipher (word 0) rk)) 0) /\
    read Q14 s = word_join
       (karatsuba_mid (h_power (ghash_twist (aes256_cipher (word 0) rk)) 1))
       (karatsuba_mid (h_power (ghash_twist (aes256_cipher (word 0) rk)) 0)) /\
    (!j. j < nblocks ==> read (memory :> bytes128 (word_add in_p (word(16*j)))) s = inblock j) /\
    (!j. j < 4 * loop_count + i ==> read (memory :> bytes128 (word_add out_p (word(16*j)))) s =
             word_xor (aes256_ctr_block c nonce rk j) (inblock j))`;;

(* tail post @0xee4: tag + ivec stored, out-forall over ALL nblocks. *)
let tail_post = mk_abs(`s:armstate`, list_mk_conj
 [`aligned_bytes_loaded s (word pc) aes256_gcm_enc_mc`;
  `read PC s = word (pc + 0xee4)`;
  `read (memory :> bytes128 tag_p) s = word_reversefields 8
     (nist_ghash (aes256_cipher (word 0) rk) tag0
        (list_of_seq (aes256_nist_cipher_block c nonce rk inblock) nblocks))`;
  `read (memory :> bytes128 ivec_p) s = word_reversefields 8 (ctr_block nonce (nblocks + c))`;
  `read X0 s = word (len_bits DIV 8)`;
  `!j. j < nblocks ==> read (memory :> bytes128 (word_add out_p (word(16*j)))) s =
           word_xor (aes256_ctr_block c nonce rk j) (inblock j)`]);;

(* tail goal: precond (loop_count>=2 comes from being reached post-drain; tail is general in loop_remain<4) -> the
   ensures from drain_bridge @0xdd0 to tail_post @0xee4.  We take drain_bridge AS the precondition state (it's the
   proven DRAINLEG post), broad frame. *)
let tail_goal = mk_imp
 (`([EL 0 rk; EL 1 rk; EL 2 rk; EL 3 rk; EL 4 rk; EL 5 rk; EL 6 rk; EL 7 rk;
     EL 8 rk; EL 9 rk; EL 10 rk; EL 11 rk; EL 12 rk; EL 13 rk; EL 14 rk]:(int128)list = rk) /\
   len_bits DIV 128 = nblocks /\ nblocks DIV 4 = loop_count /\ nblocks MOD 4 = loop_remain /\
   16 * nblocks < 2 EXP 64 /\ aligned 16 (stackpointer:int64) /\
   nonoverlapping (out_p:int64,16 * nblocks) (word pc:int64,3860) /\
   nonoverlapping (out_p:int64,16 * nblocks) (in_p:int64,16 * nblocks) /\
   nonoverlapping (out_p:int64,16 * nblocks) (htable_p:int64,192) /\
   nonoverlapping (out_p:int64,16 * nblocks) (tag_p:int64,16) /\
   nonoverlapping (out_p:int64,16 * nblocks) (ivec_p:int64,16) /\
   nonoverlapping (tag_p:int64,16) (word pc:int64,3860) /\
   nonoverlapping (tag_p:int64,16) (in_p:int64,16*nblocks) /\
   nonoverlapping (tag_p:int64,16) (htable_p:int64,192) /\
   nonoverlapping (ivec_p:int64,16) (word pc:int64,3860) /\
   nonoverlapping (ivec_p:int64,16) (in_p:int64,16*nblocks) /\
   nonoverlapping (ivec_p:int64,16) (htable_p:int64,192) /\
   nonoverlapping (tag_p:int64,16) (ivec_p:int64,16) /\
   nonoverlapping (out_p:int64,16*nblocks) (word_add stackpointer (word 160):int64,64) /\
   nonoverlapping (tag_p:int64,16) (word_add stackpointer (word 160):int64,64) /\
   nonoverlapping (ivec_p:int64,16) (word_add stackpointer (word 160):int64,64) /\
   nonoverlapping (word_add stackpointer (word 160):int64,64) (word pc:int64,3860) /\
   nonoverlapping (word_add stackpointer (word 160):int64,64) (in_p:int64,16*nblocks) /\
   nonoverlapping (word_add stackpointer (word 160):int64,64) (htable_p:int64,192) /\
   nonoverlapping (word_add stackpointer (word 160):int64,64) (out_p:int64,16*nblocks)`,
  list_mk_icomb "ensures" [`arm`;
    drain_bridge ;
    tail_post ;
    `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
     MAYCHANGE [X19; X20; X21; X22; X23; X24; X25; X26; X27; X28; X29; X30] ,,
     MAYCHANGE [Q0;Q1;Q2;Q3;Q4;Q5;Q6;Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15; Q29; Q30; Q31] ,,
     MAYCHANGE [memory :> bytes(out_p:int64, 16 * nblocks)] ,,
     MAYCHANGE [memory :> bytes(word_add stackpointer (word 160):int64, 64)] ,,
     MAYCHANGE [memory :> bytes(ivec_p:int64, 16)] ,,
     MAYCHANGE [memory :> bytes(tag_p:int64, 16)] ,, MAYCHANGE [events]`]);;

(* ---- tail single-block GHASH-append closer (Q30 i->i+1) + block reconstruct, ported from body-only 1418-1467.
   MONOLITHIC (runs on the whole post-forall-split goal); the extra frame-discharge after the WORD_RULE peel
   closes the surviving MAYCHANGE frame subgoal (standalone leg -- body-only had none) so only the Q30 word_join
   eq reaches the byteswap MATCH_MP_TAC. ---- *)
(* peel closer for the register/counter word-equalities: X16 is word_sub(word(loop_remain-i))(word 1) which
   WORD_SUB turns into an `if i<=loop_remain then..` conditional -- resolve both ifs to T via i<loop_remain,
   then WORD_RULE.  (Plain WORD_RULE fails on the COND.) *)
let tail_wordeq_close : tactic =
  ASM_SIMP_TAC[ARITH_RULE `i < loop_remain ==> (i <= loop_remain <=> T)`;
               ARITH_RULE `i < loop_remain ==> (i + 1 <= loop_remain <=> T)`] THEN
  (CONV_TAC WORD_RULE ORELSE (AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC));;

let tail_ghash_close : tactic =
  REWRITE_TAC[ZX_COUNTER_UD; ZX_COUNTER_INC; CTR_ZX_NORM] THEN
  REWRITE_TAC[GSYM WORD_ADD; WORD_ADD_0; ADD_0] THEN
  REWRITE_TAC[CTR_BLOCK_BUILD_INSERT] THEN
  REWRITE_TAC[SCALAR_RK_RECONSTRUCT] THEN
  REWRITE_TAC[XOR_AES256_CIPHER_RECONSTRUCT] THEN
  ASM_REWRITE_TAC[MAP; WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
  REWRITE_TAC[aes256_ctr_block; GSYM ADD_ASSOC] THEN
  CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
  ASM_SIMP_TAC[WORD_SUB; LT_IMP_LE; ARITH_RULE `i < l ==> i + 1 <= l`] THEN
  (* close the htable_mem_4 s59 conjunct NOW (before DISCARD_STATE_TAC kills the s59 reads): unfold the goal's
     htable and match the 6 individual reads carried through stepping (g3 unfolded htable_mem_4 in the s0 asm). *)
  TRY(ASM_REWRITE_TAC[htable_mem_4]) THEN
  DISCARD_STATE_TAC "s59" THEN
  REWRITE_TAC[ADD_ASSOC; ARITH] THEN
  REWRITE_TAC[AES256_CTR_BLOCK_RECONSTRUCT] THEN
  REWRITE_TAC[GSYM aes256_cipher_block] THEN
  REWRITE_TAC[AES256_CIPHER_BLOCK_NIST] THEN
  REWRITE_TAC[WORD_SUBWORD_REVERSEFIELDS] THEN
  SIMP_TAC[WORD_JOIN_COMBINE_LEMMA; ARITH] THEN
  REWRITE_TAC[WORD_SUBWORD_XOR] THEN
  REWRITE_TAC[WORD_SUBWORD_BYTESWAP128] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[WORD_SUBWORD_XOR] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REPEAT(CONJ_TAC THENL [tail_wordeq_close; ALL_TAC]) THEN
  REWRITE_TAC [byteswap128; WORD_BLAST
   `word_subword((word_join:int128->int128->int256) h l) (64,128):int128 =
    word_join (word_subword h (0,64):int64) (word_subword l (64,64):int64)`] THEN
  MATCH_MP_TAC(BITBLAST_RULE
   `x:int128 = y
    ==> word_join (word_subword x (0,64):int64) (word_subword x (64,64):int64):int128 =
        word_join (word_subword y (0,64):int64) (word_subword y (64,64):int64):int128`) THEN
  MAP_EVERY ABBREV_TAC
   [`sofar = (nist_ghash (aes256_cipher (word 0) rk) tag0
               (list_of_seq (aes256_nist_cipher_block c nonce rk inblock) (4 * loop_count + i)))`;
    `cipherblock = aes256_nist_cipher_block c nonce rk inblock (4 * loop_count + i)`;
    `h = h_power (ghash_twist (aes256_cipher (word 0) rk)) 0`;
    `k = karatsuba_mid h`] THEN
  REWRITE_TAC[GSYM WORD_SUBWORD_XOR] THEN
  REWRITE_TAC[RECONSTRUCT_POLYVAL_REDUCE_G2] THEN
  TRANS_TAC EQ_TRANS
    `polyval_reduce_prop3 (word_pmul (word_xor sofar cipherblock:int128) (h:int128))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[PMUL_KARATSUBA_JOIN_ALT] THEN
    REWRITE_TAC[byteswap128; WORD_SUBWORD_XOR] THEN
    CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
    ASM_REWRITE_TAC[] THEN LET_TAC THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "k" THEN REWRITE_TAC[karatsuba_mid] THEN
    ASM_REWRITE_TAC[] THEN REPEAT LET_TAC THEN
    REWRITE_TAC[POLYVAL_REDUCE_G2] THEN ASM_REWRITE_TAC[] THEN NO_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM polyval_dot] THEN
  EXPAND_TAC "h" THEN REWRITE_TAC[h_power] THEN
  REWRITE_TAC[GSYM NIST_DOT_IS_POLYVAL_DOT] THEN
  REWRITE_TAC[ARITH_RULE `(k + 1) = SUC k`] THEN
  REWRITE_TAC[list_of_seq; NIST_GHASH_APPEND; NIST_GHASH_CONS; nist_ghash] THEN
  ASM_REWRITE_TAC[];;

(* g3 closer = the monolithic body-only closer tail_ghash_close, which now internally discharges the surviving
   MAYCHANGE frame (discharged after its WORD_RULE peel) before the Q30 byteswap MATCH. *)
let tail_g3_close : tactic = tail_ghash_close;;

let tail_stepconv n =
  ARM_STEPS_TAC AES256_GCM_ENC_EXEC [n] THEN RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV));;

(* ---- tail_tac: drain_bridge@0xdd0 -> tail_post@0xee4.  Port body-only enc256 tail (scalar_rk.ml 1258-1508). ---- *)
(* The bridge state feeds directly; 3 htable-reload steps (ldr q12/q13/q14) then cbz x16@0xddc guards the loop. *)
let tail_tac =
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[fst AES256_GCM_ENC_EXEC] THEN
  (* NB: do NOT ENSURES_INIT globally -- the loop_remain>0 branch needs the raw `ensures`
     goal for ENSURES_WHILE_UP_TAC to MATCH_MP its pth.  Each branch does its own
     ENSURES_INIT + htable_mem_4 unfold (the latter resolves the q12/q13/q14 reloads). *)
  ASM_CASES_TAC `loop_remain = 0` THENL
   [(* loop_remain = 0: nblocks = 4*loop_count; cbz x16 taken -> 0xed0 -> postamble. *)
    POP_ASSUM SUBST_ALL_TAC THEN
    ENSURES_INIT_TAC "s0" THEN
    RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_4]) THEN
    SUBGOAL_THEN `nblocks = 4 * loop_count` SUBST_ALL_TAC THENL
     [MAP_EVERY(fun t -> TRY(UNDISCH_TAC t)) [`nblocks DIV 4 = loop_count`; `nblocks MOD 4 = 0`] THEN ARITH_TAC; ALL_TAC] THEN
    (* split the ivec read (low 12 nonce bytes survive the 4-byte counter writeback). *)
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o CONV_RULE(READ_MEMORY_SPLIT_CONV 2) o
      check (fun th -> let c = concl th in is_eq c && free_in `ivec_p:int64` (lhs c) &&
        not(free_in `out_p:int64` (lhs c)) && not(free_in `htable_p:int64` (lhs c)) && not(free_in `tag_p:int64` (lhs c)))) THEN
    (* steps: 3 htable reloads + cbz(taken) + postamble (mov/rev64/str q30/rev/str w14). bridge 0xdd0->0xee4. *)
    MAP_EVERY tail_stepconv (1--9) THEN  (* trivial: 0xdd0 s1..ddc(cbz taken)s4->ed0 s5..ee0 s9 ->ee4 *)
    ENSURES_FINAL_STATE_TAC THEN
    (* abstract the settled GHASH so WORD_BLAST sees an opaque G:int128 (not the huge nist_ghash byte-tower). *)
    ABBREV_TAC `gval:int128 = nist_ghash (aes256_cipher (word 0) rk) tag0
                  (list_of_seq (aes256_nist_cipher_block c nonce rk inblock) (4 * loop_count))` THEN
    CONV_TAC(ONCE_DEPTH_CONV(fun t ->
      if is_eq t && free_in `ivec_p:int64` (lhs t) && not(free_in `out_p:int64` (lhs t)) && not(free_in `tag_p:int64` (lhs t))
      then READ_MEMORY_SPLIT_CONV 2 t else failwith "")) THEN
    CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    REWRITE_TAC[ZX_COUNTER_UD; CTR_ZX_NORM] THEN ASM_REWRITE_TAC[] THEN
    (* out-forall (j<4*loop_count) is unchanged from the bridge -> ASM; frame -> close_goal10; tag+ivec via WORD_BLAST. *)
    tail_final_close;

    (* loop_remain > 0: WHILE over loop_remain @0xde0/0xecc.  Expand the ABI macro first so
       ENSURES_WHILE_UP_TAC's C,,C=C idempotence (MAYCHANGE_IDEMPOT -> ASSIGNS_SEQ_ABSORB_CONV) can
       decompose the frame; folded ABI makes ASSIGNS_SEQ_ABSORB_CONV fail (128 mainleg_tac does this). *)
    REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    ENSURES_WHILE_UP_TAC `loop_remain:num` `pc + 0xde0` `pc + 0xecc` tail_inv THEN
    REPEAT CONJ_TAC THENL
     [(* g1: ~(loop_remain=0) *) ASM_REWRITE_TAC[];
      (* g2 base: drain_bridge (post 3 htable reloads + cbz-not-taken) -> tail_inv 0.  The cbz@0xddc leaves a
         COND on val(word loop_remain)=0; resolve it via val(word loop_remain)=loop_remain (VAL_WORD_EQ,
         loop_remain<4 from nblocks MOD 4) + the g2 hyp ~(loop_remain=0) so the COND takes the else -> 0xde0. *)
      ENSURES_INIT_TAC "s0" THEN RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_4]) THEN
      MAP_EVERY tail_stepconv (1--4) THEN
      ENSURES_FINAL_STATE_TAC THEN
      SUBGOAL_THEN `val(word loop_remain:int64) = loop_remain` ASSUME_TAC THENL
       [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
        MAP_EVERY (fun t -> TRY(UNDISCH_TAC t)) [`nblocks MOD 4 = loop_remain`; `16 * nblocks < 2 EXP 64`] THEN ARITH_TAC;
        ALL_TAC] THEN
      (* htable_mem_4 needs unfolding in the goal (the 6 s4 reads are carried in asm from the g2 htable unfold). *)
      ASM_REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES; SUB_0; htable_mem_4];
      (* g3 body: tail_inv i -> tail_inv(i+1).  Unfold htable_mem_4 in the s0 asm (like bodyleg setup) so the 6
         htable reads become individual assumptions that the stepping carries to s59 -> the tail_inv(i+1)
         htable_mem_4 conjunct closes by ASM at the end. *)
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN ENSURES_INIT_TAC "s0" THEN
      RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_4]) THEN
      SUBGOAL_THEN `read (memory :> bytes128 (word_add in_p (word (64 * loop_count + 16 * i)))) s0 = inblock (4 * loop_count + i)`
      ASSUME_TAC THENL
       [REWRITE_TAC[ARITH_RULE `64 * a + 16 * b = 16 * (4 * a + b)`] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
      FIRST_X_ASSUM(STRIP_ASSUME_TAC o CONV_RULE SPLIT_INPUT_TAIL_CONV o
        check (fun th -> let c = concl th in is_eq c && free_in `in_p:int64` (lhs c) &&
          can (find_term (fun t -> is_const t && fst(dest_const t) = "bytes128")) (lhs c))) THEN
      MAP_EVERY tail_stepconv (1--5) THEN MERGE_CTR128_TAC 160 "s5" THEN
      MAP_EVERY tail_stepconv (6--13) THEN
      DISCARD_MATCHING_ASSUMPTIONS
       [`read (memory :> bytes128 (word_add stackpointer (word 160))) s = x`;
        `read (memory :> bytes64 (word_add stackpointer (word 160))) s = x`;
        `read (memory :> bytes64 (word_add stackpointer (word 168))) s = x`] THEN
      MAP_EVERY tail_stepconv (14--14) THEN MERGE_CTR128_TAC 160 "s14" THEN
      MAP_EVERY tail_stepconv (15--59) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[ARITH_RULE `j < a + i + 1 <=> j < a + i \/ j = a + i`] THEN
      ASM_REWRITE_TAC[TAUT `p \/ q ==> r <=> (p ==> r) /\ (q ==> r)`] THEN
      REWRITE_TAC[FORALL_UNWIND_THM2] THEN
      ASM_REWRITE_TAC[ARITH_RULE `16 * (4 * a + b) = 64 * a + 16 * b`] THEN
      tail_g3_close;
      (* g4 back-edge cbnz@0xecc.  Unfold htable_mem_4 (asm+goal) BEFORE stepping so the 6 htable reads carry
         through the 1-instr step; resolve the cbnz PC-COND (X16=word(loop_remain-i), taken since i<loop_remain)
         via val(word loop_remain)=loop_remain + ~(loop_remain=i). *)
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
      ENSURES_INIT_TAC "s0" THEN RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_4]) THEN REWRITE_TAC[htable_mem_4] THEN
      ARM_STEPS_TAC AES256_GCM_ENC_EXEC [1] THEN ENSURES_FINAL_STATE_TAC THEN
      ASM_SIMP_TAC[WORD_SUB; LT_IMP_LE; VAL_EQ_0; WORD_SUB_EQ_0] THEN ASM_REWRITE_TAC[GSYM VAL_EQ] THEN
      SUBGOAL_THEN `val(word loop_remain:int64) = loop_remain` ASSUME_TAC THENL
       [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
        MAP_EVERY (fun t -> TRY(UNDISCH_TAC t)) [`nblocks MOD 4 = loop_remain`; `16 * nblocks < 2 EXP 64`] THEN ARITH_TAC;
        ALL_TAC] THEN
      ASM_SIMP_TAC[ARITH_RULE `i < loop_remain ==> ~(loop_remain = i)`];
      (* g5 postamble: tail_inv loop_remain @0xecc-exit -> tail_post @0xee4. nblocks = 4*lc+loop_remain. *)
      ENSURES_INIT_TAC "s0" THEN
      FIRST_X_ASSUM(STRIP_ASSUME_TAC o CONV_RULE(READ_MEMORY_SPLIT_CONV 2) o
        check (fun th -> let c = concl th in is_eq c && free_in `ivec_p:int64` (lhs c) &&
          not(free_in `out_p:int64` (lhs c)) && not(free_in `htable_p:int64` (lhs c)) && not(free_in `tag_p:int64` (lhs c)))) THEN
      MAP_EVERY tail_stepconv (1--6) THEN  (* g5: loop-exit 0xecc s1 (cbnz not taken) ..ee0 s6 ->ee4 *)
      ENSURES_FINAL_STATE_TAC THEN
      SUBGOAL_THEN `nblocks = 4 * loop_count + loop_remain` SUBST_ALL_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
      (* abstract the settled GHASH (over 4*lc+loop_remain=nblocks blocks) so WORD_BLAST sees opaque gval. *)
      ABBREV_TAC `gval:int128 = nist_ghash (aes256_cipher (word 0) rk) tag0
                    (list_of_seq (aes256_nist_cipher_block c nonce rk inblock) (4 * loop_count + loop_remain))` THEN
      CONV_TAC(ONCE_DEPTH_CONV(fun t ->
        if is_eq t && free_in `ivec_p:int64` (lhs t) && not(free_in `out_p:int64` (lhs t)) && not(free_in `tag_p:int64` (lhs t))
        then READ_MEMORY_SPLIT_CONV 2 t else failwith "")) THEN
      CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
      REWRITE_TAC[ZX_COUNTER_UD] THEN ASM_REWRITE_TAC[] THEN
      tail_final_close]];;

let TAILLEG = GEN_ALL(prove(tail_goal, tail_tac));;

(* ========== LEG: iter1 ========== *)

(* ========================================================================= *)
(* Closers (the AES-128 closers re-indexed for the four extra rounds).         *)
(* ========================================================================= *)

(* ABBREV every maximal `word_pmul a b` subterm of the goal as a fresh int128 var.  After this, BITBLAST sees
   only word_join/word_subword/word_xor SHUFFLE over abstract int128s (fast, ~0.5s, 385 BDD vars) instead of
   modelling the 64x64 carryless-multiply circuit (30GB blowup).  This is the key to the 256 reduce closer. *)

(* collapse_q30 (Q30 GHASH tag reduce reconstruction), FILL's GROUP-0 version: adds the packed-counter fold
   (ZXNEST4/ZX_COUNTER_UD/GSYM WORD_ADD + CTR_BLOCK_BUILD_INSERT) + literal-index CT->NCB (ct_ncb_concrete) so the concrete-block-0..3
   aes-towers fold to aes256_nist_cipher_block (the symbolic-i bodyleg version does NOT fold iter_1's literal blocks). *)

(* swpgrp-invariant close_goal7: the invariant Q29 = swpgrp gt tag0 i lives in the byteswapped GHASH
   domain (head-ext byteswaps it each iteration).  The body-end goal is <machine reduce> = swpgrp gt tag0 (i+1) blk.
   collapse_q30 folds the LHS keystreams; no acc-cleanup (the acc = word_subword(word_join(swpgrp i)(swpgrp i))(64,128) =
   byteswap128(swpgrp i) is EXACTLY the seed swpgrp(SUC i) wants -- do NOT collapse it to clean).  Then RECONSTRUCT folds
   the reduce -> polyval_reduce_g2(byteswap128(swpgrp i)-seed lanes), and CORE_REDUCE_GHASH's recipe closes it =
   ghash gt (byteswap128(swpgrp i))[cbs] = swpgrp(SUC i) by the swpgrp SUC-def.  REFLEXIVE -- no byteswap-commute. *)

(* ================================================================= *)
(* iter_1 (loop_count=1) leg: from88 entry @0xb0 -> drain_bridge@0xdd0 *)
(*   3 control steps (cbz-fall/cmp/b.eq-taken) -> 0xa90 iter_1 block   *)
(*   then 208 straight-line instrs (0xa90..0xdcc) FALL THROUGH -> 0xdd0 *)
(* ================================================================= *)

(* pre-state @0xb0 = fill_pre_state (the fill legs' ensures-pre) with PC 0xbc -> 0xb0 *)
let iter1_entry = mk_abs(`s:armstate`,
  subst [`word (pc + 0xb0):int64`, `word (pc + 188):int64`] (snd(dest_abs fill_pre_state)));;

(* precond = fill_goal's precond with (3<=loop_count) dropped, (loop_count=1) added *)
let iter1_precond =
  list_mk_conj ((filter (fun c -> c <> `3 <= loop_count`) (conjuncts (lhand fill_goal)))
                @ [`loop_count = 1`]);;
(* frame: use the fill_goal frame (out_p bytes + stack) -- iter_1 writes out_p blocks 0..3 + stack counters. *)
let iter1_frame = last(snd(strip_comb(snd(dest_imp fill_goal))));;
let iter1_goal = mk_imp(iter1_precond,
  list_mk_icomb "ensures" [`arm`; iter1_entry; drain_bridge; iter1_frame]);;

(* priming for blocks 0..3 (loop_count=1) *)
let iter1_prime =
  SUBGOAL_THEN `3 < nblocks` ASSUME_TAC THENL
   [MP_TAC(SPECL [`nblocks:num`;`4`] DIVISION) THEN
    UNDISCH_TAC `nblocks DIV 4 = loop_count` THEN UNDISCH_TAC `loop_count = 1` THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `read (memory :> bytes128 in_p) s0 = inblock 0 /\
    read (memory :> bytes128 (word_add in_p (word 16))) s0 = inblock 1 /\
    read (memory :> bytes128 (word_add in_p (word 32))) s0 = inblock 2 /\
    read (memory :> bytes128 (word_add in_p (word 48))) s0 = inblock 3`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [SUBST1_TAC(WORD_RULE `in_p:int64 = word_add in_p (word (16*0))`);
      SUBST1_TAC(WORD_RULE `word_add in_p (word 16):int64 = word_add in_p (word (16*1))`);
      SUBST1_TAC(WORD_RULE `word_add in_p (word 32):int64 = word_add in_p (word (16*2))`);
      SUBST1_TAC(WORD_RULE `word_add in_p (word 48):int64 = word_add in_p (word (16*3))`)] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  (* ALSO split each primed bytes128 input block into its two bytes64 halves, so the machine's mid-block
     bytes64 loads (read(memory:>bytes64 (in_p+8))sK etc.) resolve to inblock-halves and the GHASH cipherblocks
     fold to aes256_nist_cipher_block (mirror INPUT_SPLIT_TAC256's tail).  Without this the Q30 reduce lanes carry raw
     bytes64 towers that CORE_REDUCE_GHASH can't match. *)
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o CONV_RULE SPLIT_INPUT_CONV o
     check (fun th -> let c = concl th in is_eq c && free_in `in_p:int64` (lhs c) &&
       can (find_term (fun t -> is_const t && fst(dest_const t) = "bytes128")) (lhs c))));;

let iter1_head =
  REWRITE_TAC[SND] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[fst AES256_GCM_ENC_EXEC] THEN
  MAP_EVERY (fun rn -> GHOST_INTRO_TAC (mk_var("ghost_"^rn,`:int64`)) (parse_term("read "^rn))) ghost_lanes256 THEN
  REWRITE_TAC[htable_mem_4] THEN
  ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV BETA_CONV)) THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_4]) THEN
  iter1_prime;;

let iter1_merges_abs = [(19,208);(23,192);(26,160);(34,192);(54,160);(60,176);(66,208);(69,176)];;
let iter1_block_step lo hi =
  MAP_EVERY (fun k -> gkeepN REDSETX256 AES256_GCM_ENC_EXEC ("s"^string_of_int k) THEN
     RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV THENC
        ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV THENC IN_P_ADDR_FOLD_CONV)) THEN
     (if List.mem_assoc k iter1_merges_abs then MERGE_CTR128_TAC (List.assoc k iter1_merges_abs) ("s"^string_of_int k)
      else ALL_TAC)) (lo--hi);;

(* pre-closer normalization for the loop_count=1 literal final state:
   - reduce 4*1 -> 4, 64*1 -> 64 (ptr/counter conjuncts)
   - fold Q30's RHS nist_ghash..(4*1)=nist_ghash..(4*(0+1)) -> swpgrp gt tag0 (0+1) via GSYM bridge, so
     close_goal7 (which unfolds swpgrp(i+1)) fires with i:=0
   - refold htable_mem_4 (the 6 flat reads -> folded) so close_all_tac's htable path matches *)
(* Pre-closer normalization for loop_count=1: only the globally-safe reductions.  The two `4*1` uses
   (Q30 nist_ghash..(4*1) and out-forall j<4*1) need DIFFERENT forms, so each is handled in its conjunct
   closer, NOT here.  64*1->64 (ptrs), 4+2->6 (X13), refold htable. *)
let ITER1_PRE_CLOSE : tactic =
  REWRITE_TAC[ARITH_RULE `64 * 1 = 64`; ARITH_RULE `4 * 1 + c = c + 4`] THEN
  REWRITE_TAC[GSYM htable_mem_4];;

(* Q30 closer for loop_count=1: PORTED from DRAIN's drain_close_q30 (v3), which is built for exactly the
   byteswap128(nist_ghash..(4*loop_count)) drain_bridge form (one byteswap layer more than FILL's bare-swpgrp
   Q29).  For iter_1, loop_count=1 so m:=0: first present RHS 4*1 as 4*0+4, then run drain_close_q30's body
   with m literally 0 (ABBREV sofar = swpgrp gt tag0 0 = tag0, opaque; CORE_REDUCE_GHASH A:=sofar). *)
let close_q30_i0 : tactic =
  fun (asl,w) ->
    (GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [ARITH_RULE `4 * 1 = 4 * 0 + 4`] THEN
     GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [ARITH_RULE `4 * 0 + 4 = 4 * (0 + 1)`] THEN
     GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [GSYM SWPGRP_IS_NIST_GHASH] THEN
     collapse_q30_g0 THEN
     GEN_REWRITE_TAC (RAND_CONV o TOP_DEPTH_CONV) [ARITH_RULE `0 + 1 = SUC 0`] THEN
     GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [CONJUNCT2 swpgrp] THEN
     (* reduce the seed swpgrp gt tag0 0 -> tag0 (CONJUNCT1) so it matches the machine's literal-tag0 acc lane,
        then ABBREV sofar = tag0 (like FILL's close_goal7_i0; NOT the drain's symbolic swpgrp m). *)
     GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [CONJUNCT1 swpgrp] THEN
     (* reduce the RHS block indices 4*0+k -> k so they match the machine's literal-k aes256_nist_cipher_block lanes *)
     CONV_TAC(RAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
     ABBREV_TAC `sofar:int128 = tag0` THEN
     REWRITE_TAC[ACC_JOIN_BYTESWAP] THEN
     ABBREV_TAC `bsofar:int128 = byteswap128 (sofar:int128)` THEN
     REWRITE_TAC[WORD_SUBWORD_REVERSEFIELDS] THEN
     SIMP_TAC[WORD_JOIN_COMBINE_LEMMA; ARITH] THEN
     REWRITE_TAC[WORD_SUBWORD_XOR] THEN
     REWRITE_TAC[WORD_SUBWORD_BYTESWAP128] THEN
     CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
     REWRITE_TAC[WORD_SUBWORD_XOR] THEN
     CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
     MAP_EVERY ABBREV_TAC
      [`cipherblock_0 = aes256_nist_cipher_block c nonce rk inblock 0`;
       `cipherblock_1 = aes256_nist_cipher_block c nonce rk inblock 1`;
       `cipherblock_2 = aes256_nist_cipher_block c nonce rk inblock 2`;
       `cipherblock_3 = aes256_nist_cipher_block c nonce rk inblock 3`;
       `h0 = h_power (ghash_twist (aes256_cipher (word 0) rk)) 0`;
       `h1 = h_power (ghash_twist (aes256_cipher (word 0) rk)) 1`;
       `h2 = h_power (ghash_twist (aes256_cipher (word 0) rk)) 2`;
       `h3 = h_power (ghash_twist (aes256_cipher (word 0) rk)) 3`] THEN
     REWRITE_TAC[GSYM WORD_SUBWORD_XOR] THEN
     REWRITE_TAC[byteswap128] THEN
     REWRITE_TAC[RECONSTRUCT_POLYVAL_REDUCE_G2] THEN
     EXPAND_TAC "bsofar" THEN
     REWRITE_TAC[WORD_SUBWORD_BYTESWAP128] THEN
     REWRITE_TAC[GSYM WORD_SUBWORD_XOR] THEN
     REWRITE_TAC[CMID_LOHI; CMID_HILO] THEN
     MAP_EVERY EXPAND_TAC ["h0"; "h1"; "h2"; "h3"] THEN
     REWRITE_TAC [byteswap128; WORD_BLAST
       `word_subword((word_join:int128->int128->int256) h l) (64,128):int128 =
        word_join (word_subword h (0,64):int64) (word_subword l (64,64):int64)`] THEN
     MATCH_MP_TAC(BITBLAST_RULE
      `x:int128 = y
       ==> word_join (word_subword x (0,64):int64) (word_subword x (64,64):int64):int128 =
           word_join (word_subword y (0,64):int64) (word_subword y (64,64):int64):int128`) THEN
     MATCH_MP_TAC EQ_TRANS THEN
     EXISTS_TAC
      `polyval_reduce_g2
         (word_xor (word_pmul (word_subword (cipherblock_3:int128) (0,64):int64) (word_subword (h_power (ghash_twist (aes256_cipher (word 0) rk)) 0) (0,64):int64))
         (word_xor (word_pmul (word_subword (cipherblock_2:int128) (0,64):int64) (word_subword (h_power (ghash_twist (aes256_cipher (word 0) rk)) 1) (0,64):int64))
         (word_xor (word_pmul (word_subword (cipherblock_1:int128) (0,64):int64) (word_subword (h_power (ghash_twist (aes256_cipher (word 0) rk)) 2) (0,64):int64))
         (word_pmul (word_subword (word_xor (sofar:int128) cipherblock_0) (0,64):int64) (word_subword (h_power (ghash_twist (aes256_cipher (word 0) rk)) 3) (0,64):int64)))))
         (word_xor (word_pmul (word_subword cipherblock_3 (64,64):int64) (word_subword (h_power (ghash_twist (aes256_cipher (word 0) rk)) 0) (64,64):int64))
         (word_xor (word_pmul (word_subword cipherblock_2 (64,64):int64) (word_subword (h_power (ghash_twist (aes256_cipher (word 0) rk)) 1) (64,64):int64))
         (word_xor (word_pmul (word_subword cipherblock_1 (64,64):int64) (word_subword (h_power (ghash_twist (aes256_cipher (word 0) rk)) 2) (64,64):int64))
         (word_pmul (word_subword (word_xor sofar cipherblock_0) (64,64):int64) (word_subword (h_power (ghash_twist (aes256_cipher (word 0) rk)) 3) (64,64):int64)))))
         (word_xor (word_pmul (karatsuba_mid cipherblock_3) (karatsuba_mid (h_power (ghash_twist (aes256_cipher (word 0) rk)) 0)))
         (word_xor (word_pmul (karatsuba_mid cipherblock_2) (karatsuba_mid (h_power (ghash_twist (aes256_cipher (word 0) rk)) 1)))
         (word_xor (word_pmul (karatsuba_mid cipherblock_1) (karatsuba_mid (h_power (ghash_twist (aes256_cipher (word 0) rk)) 2)))
         (word_pmul (karatsuba_mid (word_xor sofar cipherblock_0)) (karatsuba_mid (h_power (ghash_twist (aes256_cipher (word 0) rk)) 3))))))` THEN
     CONJ_TAC THENL
      [MK_COMB_TAC THENL
        [MK_COMB_TAC THENL
          [AP_TERM_TAC THEN CONV_TAC WORD_BITWISE_RULE;
           CONV_TAC WORD_BITWISE_RULE];
         CONV_TAC WORD_BITWISE_RULE];
       MATCH_ACCEPT_TAC CORE_REDUCE_GHASH]) (asl,w);;

(* out-store forall for loop_count=1: j<4*1 -> j<4 -> split LITERALLY j=0/1/2/3 (dec ITER1 style, avoids the
   j<4*0 residual that close_goal9's 4*(i+1) split leaves), then close_goal9's reconstruct tail per block
   (CTR_BLOCK_BUILD_INSERT + SCALAR_RK_RECONSTRUCT + XOR_AES256_CIPHER_RECONSTRUCT + aes256_ctr_block + AES14P/ksf). *)
let close_out_forall_i0 : tactic =
  fun (asl,w) ->
    let rkth = try snd(find (fun (_,th) -> concl th = rk15) asl) with _ -> failwith "close_out_forall_i0: no rk-hyp" in
    (REWRITE_TAC[ARITH_RULE `4 * 1 = 4`] THEN
     REWRITE_TAC[ARITH_RULE `j < 4 <=> j = 0 \/ j = 1 \/ j = 2 \/ j = 3`] THEN
     REWRITE_TAC[TAUT `p \/ q ==> r <=> (p ==> r) /\ (q ==> r)`] THEN
     REWRITE_TAC[FORALL_AND_THM; FORALL_UNWIND_THM2] THEN
     (* reduce 16*j to concrete offsets AND normalize block-0's word_add out_p (word 0) -> out_p BEFORE
        ASM_REWRITE, else the block-0 store fact (at bare out_p) fails to substitute. *)
     CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN REWRITE_TAC[WORD_ADD_0] THEN ASM_REWRITE_TAC[] THEN
     (* mirror close_goal9's PROVEN reconstruct tail (it handles the enc256 store word_xor(tower)(SCALAR_RK
        word_join) form), PLUS ZXNEST4/ZX_COUNTER_UD/GSYM WORD_ADD for the packed counter. *)
     REWRITE_TAC[ZXNEST4; ZX_COUNTER_UD; GSYM WORD_ADD] THEN
     REWRITE_TAC[CTR_BLOCK_BUILD_INSERT] THEN
     REWRITE_TAC[SCALAR_RK_RECONSTRUCT] THEN
     REWRITE_TAC[XOR_AES256_CIPHER_RECONSTRUCT] THEN
     ASM_REWRITE_TAC[MAP; WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
     REWRITE_TAC[aes256_ctr_block; GSYM ADD_ASSOC] THEN
     REWRITE_TAC[ARITH_RULE `(1:num) + c = c + 1`; ARITH_RULE `(2:num) + c = c + 2`;
                 ARITH_RULE `(3:num) + c = c + 3`; ARITH_RULE `(4:num) + c = c + 4`;
                 ARITH_RULE `(0:num) + c = c`] THEN
     CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[] THEN
     REPEAT CONJ_TAC THEN
     REWRITE_TAC[JOIN_SUBWORD_RECOMBINE] THEN
     REWRITE_TAC[GSYM AES14P_VIA_AES7C; GSYM AES14P_VIA_AES11C; GSYM AES14P_VIA_AES1C; GSYM AES14P_VIA_AES6C] THEN
     REWRITE_TAC[MATCH_MP KEYSTREAM_FOLD256 rkth]) (asl,w);;

(* per-conjunct dispatcher for the residual iter_1 conjuncts. *)
let iter1_close_conj : tactic =
  fun (asl,w) ->
    let has c t = can (find_term (fun u -> try fst(dest_const(fst(strip_comb u)))=c with _->false)) t in
    let attempt =
      if is_forall w then close_out_forall_i0
      else if is_eq w && has "nist_ghash" (rhs w) && has "byteswap128" (rhs w) then close_q30_i0
      else if is_eq w && has "word_zx" (rhs w) then ((REWRITE_TAC[ZXNEST4; ZX_COUNTER_UD] THEN AP_TERM_TAC THEN REWRITE_TAC[GSYM WORD_ADD] THEN AP_TERM_TAC THEN ARITH_TAC) ORELSE CONV_TAC WORD_BLAST)
      else close_all_iter1 in
    (* attempt must close the conjunct fully; the trailing tactic fails hard on any residual subgoal. *)
    (attempt THEN (fun (a,ww) -> failwith "iter1_close_conj: unclosed subgoal")) (asl,w);;

let ITER1_LEG =
  prove(iter1_goal,
    iter1_head THEN iter1_block_step 1 211 THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    ITER1_PRE_CLOSE THEN
    REPEAT CONJ_TAC THEN iter1_close_conj);;

(* ===== COMPOSITION APPARATUS ===== *)

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
let BODYLEG_BROAD = widen_leg BODYLEG;;

(* BODY_DRAIN: inv(loop_count-2)@0x560 -> drain_bridge@0xdd0 (last body iter + drain). *)
let body_drain_goal =
  mk_imp(lhand drain_goal,
    list_mk_icomb "ensures" [`arm`;
      leg_state swp_inv `0x560` `loop_count - 2` ; drain_bridge ; broad_frame]);;
let BODY_DRAIN = prove(body_drain_goal,
   REPEAT GEN_TAC THEN STRIP_TAC THEN
   REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
   SUBGOAL_THEN `(loop_count - 2) + 1 = loop_count - 1` ASSUME_TAC THENL
    [UNDISCH_TAC `2 <= loop_count` THEN ARITH_TAC; ALL_TAC] THEN
   ENSURES_SEQUENCE_TAC `pc + 0x8a4`
     (rhs(concl((BETA_CONV THENC REWRITE_CONV[ADD_CLAUSES]) (mk_comb(swp_inv,`loop_count - 1`))))) THEN
   CONJ_TAC THENL
    [FIRST_X_ASSUM(fun th -> if concl th = `(loop_count - 2) + 1 = loop_count - 1`
       then REWRITE_TAC[SYM th] else NO_TAC) THEN
     REWRITE_TAC[GSYM MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
     MATCH_MP_TAC BODYLEG_BROAD THEN ASM_REWRITE_TAC[] THEN
     UNDISCH_TAC `2 <= loop_count` THEN ARITH_TAC;
     REWRITE_TAC[GSYM MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
     MATCH_MP_TAC DRAINLEG THEN ASM_REWRITE_TAC[]]);;

(* ===== MAINLEG: FILL + seam-to-seam WHILE + BODY_DRAIN ===== *)
(* WHILE reindex: base k=0 -> inv1 (FILL post); body maps inv(k+1)@0x560 -> inv(k+2)@0x8a4 -> backedge.
   Loop = ENSURES_WHILE_UP (loop_count-2) @0x560 @0x8a4 while_inv, exit at inv(loop_count-2)@0x560 -> BODY_DRAIN. *)
let while_inv = mk_gabs(`k:num`, mk_comb(swp_inv, `k + 1`));;

let mainleg_goal =
  mk_imp(lhand fill_goal,
    list_mk_icomb "ensures" [`arm`; fill_pre_state; drain_bridge; broad_frame]);;

let MAINLEG = prove(mainleg_goal,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  ENSURES_SEQUENCE_TAC `pc + 0x560` (rhs(concl((BETA_CONV THENC REWRITE_CONV[ADD_CLAUSES]) (mk_comb(swp_inv,`1`))))) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN MATCH_MP_TAC FILLLEG THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `loop_count = 3` THENL
   [(fun (asl,w) ->
      let sv = `s:armstate` in
      let invbody = rhs(concl((BETA_CONV THENC REWRITE_CONV[ADD_CLAUSES]) (mk_comb(swp_inv,`loop_count - 2`)))) in
      let invbody_s = rhs(concl(BETA_CONV(mk_comb(invbody,sv)))) in
      let dpre = mk_abs(sv, list_mk_conj(
        [`aligned_bytes_loaded s (word pc) aes256_gcm_enc_mc`;
         `read PC s = word (pc + 0x560)`] @ conjuncts invbody_s)) in
      (ENSURES_PRECONDITION_TAC dpre THEN CONJ_TAC THENL
        [GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
         ASM_REWRITE_TAC[ARITH_RULE `3 - 2 = 1`; ADD_CLAUSES] THEN CONV_TAC(DEPTH_CONV NUM_REDUCE_CONV) THEN DISCH_THEN ACCEPT_TAC;
         REWRITE_TAC[GSYM MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN MATCH_MP_TAC BODY_DRAIN THEN ASM_REWRITE_TAC[] THEN
         MAP_EVERY (fun t -> TRY(UNDISCH_TAC t)) [`3 <= loop_count`] THEN ARITH_TAC]) (asl,w));
    ALL_TAC] THEN
  ENSURES_SEQUENCE_TAC `pc + 0x560` (rhs(concl((BETA_CONV THENC REWRITE_CONV[ADD_CLAUSES]) (mk_comb(swp_inv,`loop_count - 2`))))) THEN
  CONJ_TAC THENL
   [ENSURES_WHILE_UP_TAC `loop_count - 3` `pc + 0x560` `pc + 0x560` while_inv THEN
    REPEAT CONJ_TAC THENL
     [MAP_EVERY (fun t -> TRY(UNDISCH_TAC t)) [`~(loop_count = 3)`; `3 <= loop_count`] THEN ARITH_TAC;
      ENSURES_INIT_TAC "s0" THEN ENSURES_FINAL_STATE_TAC THEN REWRITE_TAC[ADD_CLAUSES] THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `k:num` THEN STRIP_TAC THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[ADD_CLAUSES] THEN
      ENSURES_SEQUENCE_TAC `pc + 0x8a4` (rhs(concl((BETA_CONV THENC REWRITE_CONV[ADD_CLAUSES]) (mk_comb(swp_inv,`(k+1)+1`))))) THEN
      CONJ_TAC THENL
       [REWRITE_TAC[GSYM MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN MATCH_MP_TAC BODYLEG_BROAD THEN ASM_REWRITE_TAC[] THEN
        MAP_EVERY (fun t -> TRY(UNDISCH_TAC t)) [`k < loop_count - 3`; `~(loop_count=3)`; `3 <= loop_count`] THEN ARITH_TAC;
        ENSURES_INIT_TAC "s0" THEN RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_4]) THEN
        SUBGOAL_THEN `val(word (loop_count - (((k+1)+1)+1)):int64) = loop_count - (((k+1)+1)+1) /\ ~(loop_count - (((k+1)+1)+1) = 0)`
        STRIP_ASSUME_TAC THENL
         [CONJ_TAC THENL
           [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
            MAP_EVERY (fun t -> TRY(UNDISCH_TAC t)) [`nblocks DIV 4 = loop_count`; `16 * nblocks < 2 EXP 64`] THEN ARITH_TAC;
            MAP_EVERY (fun t -> TRY(UNDISCH_TAC t)) [`k < loop_count - 3`; `3 <= loop_count`] THEN ARITH_TAC]; ALL_TAC] THEN
        ARM_STEPS_TAC AES256_GCM_ENC_EXEC [1] THEN
        RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `val(word (loop_count - (((k+1)+1)+1)):int64) = loop_count - (((k+1)+1)+1)`;
                                    ASSUME `~(loop_count - (((k+1)+1)+1) = 0)`; COND_CLAUSES]) THEN
        ENSURES_FINAL_STATE_TAC THEN CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[ADD_CLAUSES; htable_mem_4] THEN ASM_REWRITE_TAC[]];
      X_GEN_TAC `k:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
      SUBGOAL_THEN `(loop_count - 3) + 1 = loop_count - 2` (fun th -> ASSUME_TAC th THEN RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th]) THENL
       [MAP_EVERY (fun t -> TRY(UNDISCH_TAC t)) [`3 <= loop_count`] THEN ARITH_TAC; ALL_TAC] THEN
      CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[ADD_CLAUSES] THEN
      ENSURES_INIT_TAC "s0" THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES]];
    REWRITE_TAC[GSYM MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN MATCH_MP_TAC BODY_DRAIN THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY (fun t -> TRY(UNDISCH_TAC t)) [`3 <= loop_count`] THEN ARITH_TAC]);;

(* ===== CORE_FROM88 apparatus ===== *)
(* from88 frame = TAIL's frame (widest: out_p+stack+ivec+tag); widen drain-reaching legs to it. *)
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
(* from88 entry @0xb0 = fill_pre_state with PC 0xbc->0xb0 *)
let from88_entry = mk_abs(`s:armstate`,
  subst [`word (pc + 0xb0):int64`, `word (pc + 188):int64`] (snd(dest_abs fill_pre_state)));;
(* general precond (drop 2<=loop_count; from88 handles lc=0/1/2/>=3) *)
let gen_precond = list_mk_conj (filter (fun c -> c <> `2 <= loop_count`) (conjuncts (lhand drain_goal)));;
let core_from88_goal =
  mk_imp(gen_precond, list_mk_icomb "ensures" [`arm`; from88_entry; tail_post; from88_frame]);;
(* degenerate leg goals (lc=0/1/2 -> drain_bridge). *)
let mk_lcN_goal n =
  mk_imp(mk_conj(gen_precond, mk_eq(`loop_count:num`, mk_small_numeral n)),
    list_mk_icomb "ensures" [`arm`; from88_entry; drain_bridge; broad_frame]);;
(* loop_count = 0: cbz x1@0xb0 taken -> 0xdd0 (drain_bridge), skipping the whole loop.
   One instruction; drain_bridge reduces via list_of_seq _ 0 = [], nist_ghash h tag0 [] = tag0,
   64*0 = 0 etc.  Unfold htable_mem_4 in the goal FIRST so its memory reads carry through the step. *)
let LEG_LC0 = GEN_ALL(prove(mk_lcN_goal 0,
  REWRITE_TAC[SND] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[htable_mem_4] THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC AES256_GCM_ENC_EXEC [1] THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[LIST_OF_SEQ; nist_ghash; MULT_CLAUSES; ADD_CLAUSES; WORD_ADD_0; LT] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN TRY MONOTONE_MAYCHANGE_TAC));;

(* ===== from88 body-form state helpers (compose 1945-1965) ===== *)
(* ===== CORE_FROM88 full assembly: whole main-body 0xb0 -> tail_post ===== *)
(* Body-form state helpers: strip the leading aligned_bytes_loaded/program-decode/PC conjuncts
   (ENSURES_SEQUENCE re-prepends them for a waypoint), and unfold the htable_mem_4 abbreviation. *)
let strip_aligned_pc abs =
  let s,body = dest_abs abs in
  let keep = filter (fun c ->
    not(can (find_term (fun t -> is_const t &&
        (fst(dest_const t)="aligned_bytes_loaded"))) c)
    && not(can (find_term (fun t -> t = `read PC`)) c)
    && not(free_in
        `aes256_gcm_enc_mc` c))
    (conjuncts body) in
  mk_abs(s, list_mk_conj keep);;
let unfold_htable_in abs =
  let s,body = dest_abs abs in
  mk_abs(s, rhs(concl(REWRITE_CONV[htable_mem_4] body)));;

let drain_bridge_body = strip_aligned_pc drain_bridge;;
let fill_pre_body = strip_aligned_pc fill_pre_state;;
let fill_pre_body_flat = unfold_htable_in fill_pre_body;;

(* ===== LEG_LC1 / LEG_LC2 degenerate legs ===== *)
let LEG_LC1 = ITER1_LEG;;
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
let leg_htab th = REWRITE_RULE[htable_mem_4; GSYM CONJ_ASSOC] th;;
let discharge_leg_hyps : tactic =
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
  TRY(FIRST_ASSUM ACCEPT_TAC) THEN TRY(ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  TRY(ASM_ARITH_TAC) THEN TRY NONOVERLAPPING_TAC;;
let apply_leg_core (legn:thm) : tactic =
  REFOLD_ABI THEN
  ((MATCH_MP_TAC legn THEN TRY(EXISTS_TAC `key_p:int64`) THEN discharge_leg_hyps)
   ORELSE
   (MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN
    EXISTS_TAC (el 3 (snd(strip_comb(snd(dest_imp(snd(strip_forall(concl legn)))))))) THEN
    CONJ_TAC THENL
     [REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN SUBSUMED_MAYCHANGE_TAC;
      MATCH_MP_TAC legn THEN TRY(EXISTS_TAC `key_p:int64`) THEN discharge_leg_hyps]));;
let apply_leg_1 (legn:thm) : tactic =
  fun (asl,w) ->
    ((apply_leg_core legn)
     ORELSE
     (fun (a2,w2) ->
        if (try fst(dest_const(fst(strip_comb w2))) = "ensures" with _ -> false) then
          (let lpost = el 2 (snd(strip_comb(snd(dest_imp(snd(strip_forall(concl legn))))))) in
           (ENSURES_POSTCONDITION_TAC lpost THEN
            CONJ_TAC THENL
             [REPEAT GEN_TAC THEN REWRITE_TAC[GSYM MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
              DISCH_THEN(fun th -> REPEAT CONJ_TAC THEN
                 FIRST[ACCEPT_TAC th; (STRIP_ASSUME_TAC th THEN ASM_REWRITE_TAC[])]);
              apply_leg_core legn]) (a2,w2))
        else failwith "apply_leg_1: not ensures")) (asl,w);;
let APPLY_LEG (leg:thm) : tactic =
  (apply_leg_1 (leg_htab leg))
  ORELSE
  (apply_leg_1 (REWRITE_RULE[GSYM CONJ_ASSOC] leg));;
let LC2_PARTA_W = widen_leg_to broad_frame LC2_PARTA;;
(* LEG_LC2 composition (loop_count=2): hop 0xb0->0xbc (folded htable waypoint) + PARTA (FILL, 0xbc->0x8a8)
   + DRAINLEG_8A8 (drain, 0x8a8->drain_bridge).  KEY (from the focused subagent solve): the drain half needs the
   FULL leg_state predicate in ENSURES_PRECONDITION_TAC (aligned+PC included, NOT strip_aligned_pc), the
   implication-branch normalizes literal-1 vs loop_count-1 under loop_count=2 (TOP_DEPTH BETA + loop_count
   rewrite + NUM_REDUCE), and CRUCIALLY REFOLD_ABI before MATCH_MP_TAC DRAINLEG_8A8 (the top-level REWRITE[ABI]
   expanded the goal frame while DRAINLEG_8A8 carries the folded ABI frame -> "No match" without the
   refold), then ARITH_TAC discharges DRAINLEG_8A8's `2 <= loop_count` residual (=`2 <= 2`). *)
let LEG_LC2 = GEN_ALL(prove(mk_lcN_goal 2,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  ENSURES_SEQUENCE_TAC `pc + 0xbc` (strip_aligned_pc fill_pre_state) THEN CONJ_TAC THENL
   [(* hop 0xb0 -> 0xbc, folded htable waypoint (refold htable_mem_4 at the end) *)
    ENSURES_INIT_TAC "s0" THEN RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_4]) THEN
    SUBGOAL_THEN `val(word loop_count:int64) = loop_count` ASSUME_TAC THENL
     [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
      MAP_EVERY (fun t -> TRY(UNDISCH_TAC t))
        [`nblocks DIV 4 = loop_count`; `16 * nblocks < 2 EXP 64`] THEN ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `~(val (word_sub (word loop_count) (word 1):int64) = 0)` ASSUME_TAC THENL
     [REWRITE_TAC[VAL_EQ_0; WORD_SUB_EQ_0] THEN DISCH_THEN(MP_TAC o AP_TERM `val:int64->num`) THEN
      ASM_REWRITE_TAC[VAL_WORD_1] THEN UNDISCH_TAC `loop_count = 2` THEN ARITH_TAC; ALL_TAC] THEN
    MAP_EVERY (fun n -> ARM_STEPS_TAC AES256_GCM_ENC_EXEC [n]) (1--3) THEN
    ENSURES_FINAL_STATE_TAC THEN REWRITE_TAC[htable_mem_4] THEN ASM_REWRITE_TAC[];
    ENSURES_SEQUENCE_TAC `pc + 0x8a8` (strip_aligned_pc lc2_waypoint) THEN CONJ_TAC THENL
     [(* PARTA: FILL leg (folded 0xbc entry matches LC2_PARTA_W); blanket-discharge its precond leftovers *)
      APPLY_LEG LC2_PARTA_W THEN
      (ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
       TRY(ASM_ARITH_TAC) THEN TRY NONOVERLAPPING_TAC);
      (* PARTB: drain leg, loop_count=2 index-normalization + REFOLD_ABI before MATCH_MP_TAC *)
      ENSURES_PRECONDITION_TAC (leg_state swp_inv `0x8a8` `loop_count - 1`) THEN
      CONJ_TAC THENL
       [GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
        FIRST_ASSUM(fun th -> if lhs(concl th)=`loop_count:num` then REWRITE_TAC[th] else NO_TAC) THEN
        CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];
        REFOLD_ABI THEN MATCH_MP_TAC DRAINLEG_8A8 THEN ASM_REWRITE_TAC[] THEN ARITH_TAC]]]));;

(* ===== widen degenerate legs + leg_precond_close (compose 1967-1977) ===== *)
(* Widen every drain-reaching degenerate leg + MAINLEG to the from88 (widest) frame. *)
let LEG_LC0_W = widen_to_from88 LEG_LC0;;
let LEG_LC1_W = widen_to_from88 LEG_LC1;;
let LEG_LC2_W = widen_to_from88 LEG_LC2;;
let MAINLEG_W = widen_to_from88 MAINLEG;;

(* Preconditions of every leg differ from from88's context only by nonoverlap orientation. *)
let leg_precond_close =
  ASM_REWRITE_TAC[] THEN RULE_ASSUM_TAC(ONCE_REWRITE_RULE[nonoverlapping]) THEN
  REWRITE_TAC[nonoverlapping] THEN ONCE_REWRITE_TAC[NONOVERLAPPING_MODULO_SYM] THEN
  ASM_REWRITE_TAC[];;

(* ===== CORE_FROM88 (compose 1979-2017) ===== *)
let CORE_FROM88 = prove(core_from88_goal,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  ENSURES_SEQUENCE_TAC `pc + 0xdd0` drain_bridge_body THEN
  CONJ_TAC THENL
   [(* entry (0xb0) -> drain_bridge@0xdd0, by loop_count case *)
    ASM_CASES_TAC `loop_count = 0` THENL
     [REWRITE_TAC[GSYM MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
      MATCH_MP_TAC LEG_LC0_W THEN leg_precond_close; ALL_TAC] THEN
    ASM_CASES_TAC `loop_count = 1` THENL
     [REWRITE_TAC[GSYM MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
      MATCH_MP_TAC LEG_LC1_W THEN leg_precond_close; ALL_TAC] THEN
    ASM_CASES_TAC `loop_count = 2` THENL
     [REWRITE_TAC[GSYM MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
      MATCH_MP_TAC LEG_LC2_W THEN leg_precond_close; ALL_TAC] THEN
    SUBGOAL_THEN `3 <= loop_count` ASSUME_TAC THENL
     [MAP_EVERY (fun t -> TRY(UNDISCH_TAC t))
        [`~(loop_count=0)`;`~(loop_count=1)`;`~(loop_count=2)`] THEN ARITH_TAC; ALL_TAC] THEN
    (* lc>=3: hop 0xb0->0xbc (cmp x1,#1;b.eq 0xa90 falls through), then MAINLEG *)
    ENSURES_SEQUENCE_TAC `pc + 0xbc` fill_pre_body_flat THEN
    CONJ_TAC THENL
     [ENSURES_INIT_TAC "s0" THEN RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_4]) THEN
      SUBGOAL_THEN `val(word loop_count:int64) = loop_count` ASSUME_TAC THENL
       [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
        MAP_EVERY (fun t -> TRY(UNDISCH_TAC t))
          [`nblocks DIV 4 = loop_count`; `16 * nblocks < 2 EXP 64`] THEN ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `~(val (word_sub (word loop_count) (word 1):int64) = 0)` ASSUME_TAC THENL
       [REWRITE_TAC[VAL_EQ_0; WORD_SUB_EQ_0] THEN
        DISCH_THEN(MP_TAC o AP_TERM `val:int64->num`) THEN
        ASM_REWRITE_TAC[VAL_WORD_1] THEN ASM_ARITH_TAC; ALL_TAC] THEN
      MAP_EVERY (fun n -> ARM_STEPS_TAC AES256_GCM_ENC_EXEC [n]) (1--3) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[GSYM MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
      REWRITE_TAC[GSYM htable_mem_4] THEN
      MATCH_MP_TAC MAINLEG_W THEN leg_precond_close];
    (* drain_bridge@0xdd0 -> tail_post@0xee4 *)
    REWRITE_TAC[GSYM MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    MATCH_MP_TAC TAILLEG THEN leg_precond_close]);;

(* ===== AES256_GCM_ENC_CORRECT (full function 0x2c -> 0xee4) ===== *)
(* Witness for ENSURES_POSTCONDITION_THM: the (stronger) from88 postcondition, extracted
   from CORE_FROM88 with htable_mem_4 unfolded+flattened to match the goal pre form. *)
let core_from88_post =
  el 2 (snd(strip_comb(snd(dest_imp(snd(strip_forall(
    concl (REWRITE_RULE[htable_mem_4; GSYM CONJ_ASSOC] CORE_FROM88))))))));;
let AES256_GCM_ENC_CORRECT = prove
 (`!in_p out_p len_bits tag_p ivec_p key_p htable_p tag0 nonce rk inblock pc
     stackpointer.
       aligned 16 stackpointer /\
       ALLPAIRS nonoverlapping
        [(out_p, 16 * val len_bits DIV 128); (tag_p, 16); (ivec_p, 16);
         (word_add stackpointer (word 160), 64)]
        [(word pc, LENGTH aes256_gcm_enc_mc);
         (in_p,  16 * val len_bits DIV 128); (key_p, 240); (htable_p, 192)] /\
       PAIRWISE nonoverlapping
        [(out_p, 16 * val len_bits DIV 128); (tag_p, 16); (ivec_p, 16);
         (word_add stackpointer (word 160), 64)]
    ==>
    ensures arm
      (\s. aligned_bytes_loaded s (word pc) aes256_gcm_enc_mc /\
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
      (\s. read PC s = word (pc + 0xee4) /\
           (!i. i < val len_bits DIV 128
                ==> read (memory :> bytes128 (word_add out_p (word(16*i)))) s =
                    word_xor (aes256_ctr_block c nonce rk i) (inblock i)) /\
           read (memory :> bytes128 tag_p) s =
             word_reversefields 8
              (nist_ghash (aes256_cipher (word 0) rk) tag0
                 (list_of_seq (aes256_nist_cipher_block c nonce rk inblock)
                              (val len_bits DIV 128))) /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8
               (ctr_block nonce (val len_bits DIV 128 + c)) /\
           read X0 s = word (val len_bits DIV 8))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [X19; X20; X21; X22; X23; X24; X25; X26; X27; X28; X29; X30] ,,
       MAYCHANGE [Q0; Q1; Q2; Q3; Q4; Q5; Q6; Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15; Q29; Q30; Q31] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * val len_bits DIV 128)] ,,
       MAYCHANGE [memory :> bytes(word_add stackpointer (word 160), 64)] ,,
       MAYCHANGE [memory :> bytes(ivec_p, 16)] ,,
       MAYCHANGE [memory :> bytes(tag_p, 16)] ,,
       MAYCHANGE [events])`,
  GEN_TAC THEN GEN_TAC THEN W64_GEN_TAC `len_bits:num` THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REWRITE_TAC[ALLPAIRS; PAIRWISE; ALL; fst AES256_GCM_ENC_EXEC] THEN

  (*** Abbreviate the loop counts to keep goal terms manageable ***)

  ABBREV_TAC `nblocks     = len_bits DIV 128` THEN
  ABBREV_TAC `loop_count  = nblocks DIV 4` THEN
  ABBREV_TAC `loop_remain = nblocks MOD 4` THEN
  STRIP_TAC THEN
  CONV_TAC(ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN REWRITE_TAC[WORD_ADD_0] THEN

  (*** Break up the round key list - a bit clumsy ****)

  ASM_CASES_TAC `LENGTH(rk:int128 list) = 15` THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [LENGTH_EQ_LIST_OF_SEQ]) THEN
    CONV_TAC(LAND_CONV(RAND_CONV LIST_OF_SEQ_CONV)) THEN
    DISCH_THEN(ASSUME_TAC o SYM) THEN
    CONV_TAC(ONCE_DEPTH_CONV WORDLIST_FROM_MEMORY_CONV) THEN
    EXPAND_TAC "rk" THEN REWRITE_TAC[MAP; CONS_11; GSYM CONJ_ASSOC] THEN
    ASM_REWRITE_TAC[];
    ENSURES_INIT_TAC "s0" THEN
    FIRST_ASSUM(MP_TAC o AP_TERM `LENGTH:int128 list->num`) THEN
    ASM_REWRITE_TAC[LENGTH_WORDLIST_FROM_MEMORY; LENGTH_MAP]] THEN

  (***** Initial state setup ****)

  ENSURES_SEQUENCE_TAC `pc + 0xb0`
   `\s. read X0 s = in_p /\
        read X2 s = out_p /\
        read X3 s = tag_p /\
        read X4 s = ivec_p /\
        read X5 s = key_p /\
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
        read X20 s = word_subword (word_reversefields 8 (EL 14 rk):int128) (0,64):int64 /\
        read X21 s = word_subword (word_reversefields 8 (EL 14 rk):int128) (64,64):int64 /\
        read Q7 s = word 13979173243358019584 /\
        read X11 s =
          word_subword (word_reversefields 8 (ctr_block nonce c):int128) (0,64):int64 /\
        read X12 s =
          word_zx (word_zx (word_subword
            (word_reversefields 8 (ctr_block nonce c):int128) (64,64):int64):int32):int64 /\
        read X13 s = word_zx (word c:int32):int64 /\
        read X15 s = word(len_bits DIV 8) /\
        read X1 s = word loop_count /\
        read X7 s = word nblocks /\
        read X16 s = word loop_remain /\
        read Q30 s =
          byteswap128 tag0 /\
        htable_mem_4 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s /\
        (!i. i < nblocks
             ==> read (memory :> bytes128 (word_add in_p (word(16*i)))) s =
                 inblock i)` THEN
  REWRITE_TAC[htable_mem_4; GSYM CONJ_ASSOC] THEN CONJ_TAC THENL
   [ENSURES_INIT_TAC "s0" THEN
    (*** Split + abbreviate the two 64-bit IV halves so the scalar counter    ***)
    (*** registers X11/X12/X13 loaded by "ldp x11,x12,[x4]" survive as clean  ***)
    (*** variables rather than being dropped as compound initial-memory reads ***)
    UNDISCH_TAC
     `read (memory :> bytes128 ivec_p) s0 =
      word_reversefields 8 (ctr_block nonce c)` THEN
    GEN_REWRITE_TAC (LAND_CONV o LAND_CONV)
     [el 1 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT)] THEN
    DISCH_TAC THEN
    ABBREV_TAC `ivlo:int64 = read (memory :> bytes64 ivec_p) s0` THEN
    ABBREV_TAC `ivhi:int64 = read (memory :> bytes64 (word_add ivec_p (word 8))) s0` THEN
    (*** The scalar_rk variant loads the final round key (EL 14 rk) into the   ***)
    (*** scalar pair X20/X21 via "ldp x20,x21,[x5,#224]", so that key cell     ***)
    (*** must be present at 64-bit granularity.  Split it (leaving the k=0..13 ***)
    (*** cells as bytes128 for the "ldr q18..q28,q15,q16,q17" vector loads).    ***)
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o CONV_RULE(READ_MEMORY_SPLIT_CONV 1) o
      check (fun th -> let c = concl th in
        is_eq c && free_in `key_p:int64` (lhs c) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "bytes128"))
            (lhs c) &&
        can (find_term (fun t -> t = `224`)) (lhs c))) THEN
    ARM_STEPS_TAC AES256_GCM_ENC_EXEC (1--33) THEN
    ENSURES_FINAL_STATE_TAC THEN
    (*** Name the IV-halves join relation for reuse in the counter conjuncts.    ***)
    (*** Keep ivlo/ivhi UNsubstituted so the ivec recombination still closes.    ***)
    FIRST_ASSUM(fun th ->
      if can (term_match [] `word_join (ivhi:int64) (ivlo:int64):int128 = xx`)
             (concl th)
      then ASSUME_TAC th else NO_TAC) THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [(*** ivec memory read: recombine the two abbreviated halves ***)
      GEN_REWRITE_TAC LAND_CONV
       [el 1 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT)] THEN ASM_REWRITE_TAC[];
      (*** X11 = low half of the reversed counter block ***)
      FIRST_ASSUM(fun th ->
        if can (term_match [] `word_join (ivhi:int64) (ivlo:int64):int128 = xx`)
               (concl th)
        then ACCEPT_TAC(MATCH_MP X11_SETUP th) else NO_TAC);
      (*** X12 = nonce-remainder half (counter lane zeroed) ***)
      FIRST_ASSUM(fun th ->
        if can (term_match [] `word_join (ivhi:int64) (ivlo:int64):int128 = xx`)
               (concl th)
        then ACCEPT_TAC(MATCH_MP X12_SETUP th) else NO_TAC);
      (*** X13 = counter value 2 ***)
      FIRST_ASSUM(fun th ->
        if can (term_match [] `word_join (ivhi:int64) (ivlo:int64):int128 = xx`)
               (concl th)
        then ACCEPT_TAC(MATCH_MP X13_SETUP th) else NO_TAC);
      (*** X15 = len_bits DIV 8 ***)
      ASM_REWRITE_TAC[word_ushr] THEN AP_TERM_TAC THEN ARITH_TAC;
      (*** X1 = loop_count (three composed lsr's) ***)
      REWRITE_TAC[WORD_USHR_COMPOSE] THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
      ASM_REWRITE_TAC[word_ushr] THEN
      MAP_EVERY EXPAND_TAC ["loop_count"; "nblocks"] THEN
      REWRITE_TAC[DIV_DIV] THEN AP_TERM_TAC THEN CONV_TAC NUM_REDUCE_CONV;
      (*** X7 = nblocks (two composed lsr's) ***)
      REWRITE_TAC[WORD_USHR_COMPOSE] THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
      ASM_REWRITE_TAC[word_ushr] THEN EXPAND_TAC "nblocks" THEN
      AP_TERM_TAC THEN CONV_TAC NUM_REDUCE_CONV;
      (*** X9 = loop_remain ***)
      REWRITE_TAC[WORD_USHR_COMPOSE] THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
      ASM_REWRITE_TAC[word_ushr] THEN
      REWRITE_TAC[ARITH_RULE `3 = 2 EXP 2 - 1`] THEN
      REWRITE_TAC[WORD_AND_MASK_WORD; VAL_WORD; DIMINDEX_64] THEN
      REWRITE_TAC[MOD_MOD_EXP_MIN] THEN
      MAP_EVERY EXPAND_TAC ["loop_remain"; "nblocks"] THEN
      AP_TERM_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC;
      (*** Q11 = byteswap tag ***)
      REWRITE_TAC[byteswap128] THEN CONV_TAC WORD_BLAST];
    MAP_EVERY VAL_INT64_TAC
     [`nblocks:num`; `loop_count:num`; `loop_remain:num`]] THEN
  (* SECOND ENSURES_SEQUENCE branch: preamble-post @0xb0 -> tail_post @0xee4 = CORE_FROM88.
     Two mismatches vs a bare MATCH_MP_TAC CORE_FROM88:
       (1) htable_mem_4 is UNFOLDED+flattened in the goal pre (the preamble did
           REWRITE[htable_mem_4; GSYM CONJ_ASSOC]) but FOLDED in from88_entry -> use
           CORE_FROM88_flat = REWRITE_RULE[htable_mem_4; GSYM CONJ_ASSOC] CORE_FROM88.
       (2) CORE_FROM88's post is STRONGER than the canonical CORRECT post (it retains an extra
           aligned_bytes_loaded conjunct and orders the out-forall last), so a direct match on the
           postcondition fails.  Weaken via ENSURES_POSTCONDITION_THM: EXISTS the from88 post as the
           witness, discharge (from88_post ==> goal_post) by BETA + ASM_REWRITE (drops the extra
           conjunct, reorders), then MATCH_MP_TAC the flat CORE_FROM88 for the ensures itself.
     Refold the ABI frame first. *)
  REWRITE_TAC[GSYM MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN
  EXISTS_TAC core_from88_post THEN CONJ_TAC THENL
   [GEN_TAC THEN STRIP_TAC THEN RULE_ASSUM_TAC BETA_RULE THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC (REWRITE_RULE[htable_mem_4; GSYM CONJ_ASSOC] CORE_FROM88) THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC [`len_bits < 2 EXP 64`; `len_bits DIV 128 = nblocks`] THEN
    ARITH_TAC]);;

(* ============================================================================ *)
(* SUBROUTINE wrapper: lifts AES256_GCM_ENC_CORRECT through the 11-step save prologue    *)
(* and 11-step restore epilogue + ret.  Prologue/epilogue byte-identical to the  *)
(* body-only enc256 kernel (D8-D15 + X19-X30 saves, 224-byte frame).             *)
(* ============================================================================ *)

let AES256_GCM_ENC_SUBROUTINE_CORRECT = prove
 (`!in_p out_p len_bits tag_p ivec_p key_p htable_p tag0 nonce rk inblock
    pc stackpointer returnaddress.
    aligned 16 stackpointer /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * val len_bits DIV 128); (tag_p, 16); (ivec_p, 16);
       (word_sub stackpointer (word 224), 224)]
      [(word pc, LENGTH aes256_gcm_enc_mc);
       (in_p,  16 * val len_bits DIV 128); (key_p, 240); (htable_p, 192)] /\
    PAIRWISE nonoverlapping
      [(out_p, 16 * val len_bits DIV 128); (tag_p, 16); (ivec_p, 16);
       (word_sub stackpointer (word 224), 224)]
    ==>
    ensures arm
      (\s. aligned_bytes_loaded s (word pc) aes256_gcm_enc_mc /\
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
                 (list_of_seq (aes256_nist_cipher_block c nonce rk inblock)
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
  REWRITE_TAC[fst AES256_GCM_ENC_EXEC; htable_mem_4; KEY15_SPLIT] THEN
  ARM_ADD_RETURN_STACK_TAC
    ~pre_post_nsteps:(11, 11)
    AES256_GCM_ENC_EXEC
    (REWRITE_RULE[KEY15_SPLIT]
       (REWRITE_RULE[fst AES256_GCM_ENC_EXEC; htable_mem_4] AES256_GCM_ENC_CORRECT))
    `[X19; X20; X21; X22; X23; X24; X25; X26; X27; X28; X29; X30;
      D8; D9; D10; D11; D12; D13; D14; D15]` 224);;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory-safety for the AES-256-GCM SWP encrypt kernel.    *)
(* Event scaffold (CONCRETIZE_F_EVENTS_TAC) walked with the event-tracking    *)
(* simulator SAFE_SIM; per-leg obligations closed by the shared           *)
(* consttime/utils closers plus a few depth-3 pointer/counter reconcilers.    *)
(* ------------------------------------------------------------------------- *)

let SAFE_SIM = SAFE_SIM_TAC AES256_GCM_ENC_EXEC;;

(* fill X1: word_sub(word C)(word 2) = word(C - 2 - 0), where C = len_bits DIV 512 = loop_count.
   Guarded so it only fires on a word_sub-by-2 equation. *)
let FILL_X1 : tactic =
  W(fun (asl,w) ->
    if (try let l,_ = dest_eq w in
            name_of(fst(strip_comb l)) = "word_sub" && rand l = `word 2:int64`
        with _ -> false)
    then
      REWRITE_TAC[SUB_0] THEN
      TRY(SUBGOAL_THEN `len_bits DIV 512 = loop_count` SUBST1_TAC THENL
       [UNDISCH_TAC `len_bits DIV 128 = 4 * loop_count + loop_remain` THEN
        UNDISCH_TAC `loop_remain < 4` THEN REWRITE_TAC[DIV_DIV] THEN ARITH_TAC; ALL_TAC]) THEN
      SUBGOAL_THEN `loop_count = (loop_count - 2) + 2`
        (fun th -> GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [th]) THENL
       [ASM_ARITH_TAC; CONV_TAC WORD_RULE]
    else NO_TAC);;

(* Leaf closers: the shared chain plus the depth-3 reconcilers (fill counter, drain pointers). *)
let CLOSE_ENC = CLOSE_R2_WITH [FILL_X1; DRAIN_ADDR_K `1`; DRAIN_ADDR_K `2`];;
let CLOSE_ENC_SUB = CLOSE_R2_WITH [MEM_PRESERVE; FILL_X1; DRAIN_ADDR_K `1`; DRAIN_ADDR_K `2`];;

let scaffold_enc =
 `\(in_p:int64) (out_p:int64) (tag_p:int64) (ivec_p:int64) (key_p:int64) (htable_p:int64)
   (len_bits:int64) (pc:num) (stackpointer:int64).
   APPEND
     (if val len_bits DIV 128 MOD 4 = 0 then f_ev_tail0 in_p out_p tag_p ivec_p key_p htable_p len_bits pc stackpointer
      else APPEND (f_ev_tail_post in_p out_p tag_p ivec_p key_p htable_p len_bits pc stackpointer)
        (APPEND (ENUMERATEL (val len_bits DIV 128 MOD 4) (\i. f_ev_tail_body in_p out_p tag_p ivec_p key_p htable_p len_bits pc stackpointer i))
            (f_ev_tail_pre in_p out_p tag_p ivec_p key_p htable_p len_bits pc stackpointer)))
     (APPEND
       (if val len_bits DIV 128 DIV 4 = 0 then f_ev_m0 in_p out_p tag_p ivec_p key_p htable_p len_bits pc stackpointer
        else if val len_bits DIV 128 DIV 4 = 1 then f_ev_m1 in_p out_p tag_p ivec_p key_p htable_p len_bits pc stackpointer
        else if val len_bits DIV 128 DIV 4 = 2 then f_ev_m2 in_p out_p tag_p ivec_p key_p htable_p len_bits pc stackpointer
        else APPEND (f_ev_drain in_p out_p tag_p ivec_p key_p htable_p len_bits pc stackpointer)
            (APPEND (ENUMERATEL (val len_bits DIV 128 DIV 4 - 2) (\i. f_ev_steady in_p out_p tag_p ivec_p key_p htable_p len_bits pc stackpointer i))
              (f_ev_fill in_p out_p tag_p ivec_p key_p htable_p len_bits pc stackpointer)))
       (f_ev_pro in_p out_p tag_p ivec_p key_p htable_p len_bits pc stackpointer))
   :(uarch_event) list`;;

let OPEN_ENC : tactic =
  OPEN_SWP_SAFE AES256_GCM_ENC_EXEC THEN
  SUBGOAL_THEN `nblocks = 4 * loop_count + loop_remain` SUBST_ALL_TAC THENL
   [UNDISCH_TAC `nblocks DIV 4 = loop_count` THEN UNDISCH_TAC `nblocks MOD 4 = loop_remain` THEN ARITH_TAC; ALL_TAC];;

let AES256_GCM_ENC_SAFE = prove
 (`exists f_events.
    forall e in_p len_bits out_p tag_p ivec_p key_p htable_p pc stackpointer.
      aligned 16 stackpointer /\
      ALLPAIRS nonoverlapping
        [(out_p, 16 * val len_bits DIV 128); (tag_p, 16); (ivec_p, 16);
         (word_add stackpointer (word 160), 64)]
        [(word pc, LENGTH aes256_gcm_enc_mc);
         (in_p,  16 * val len_bits DIV 128); (key_p, 240); (htable_p, 192)] /\
      PAIRWISE nonoverlapping
        [(out_p, 16 * val len_bits DIV 128); (tag_p, 16); (ivec_p, 16);
         (word_add stackpointer (word 160), 64)]
      ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) aes256_gcm_enc_mc /\
               read PC s = word (pc + 0x2c) /\ read SP s = stackpointer /\
               C_ARGUMENTS [in_p; len_bits; out_p; tag_p; ivec_p; key_p; htable_p] s /\
               read events s = e)
          (\s. read PC s = word (pc + 0xee4) /\
               (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events in_p out_p tag_p ivec_p key_p htable_p len_bits pc stackpointer /\
                    memaccess_inbounds e2
                      [in_p, 16 * val len_bits DIV 128; tag_p, 16; ivec_p, 16; key_p, 240; htable_p, 192;
                       out_p, 16 * val len_bits DIV 128; word_add stackpointer (word 160), 64]
                      [out_p, 16 * val len_bits DIV 128; tag_p, 16; ivec_p, 16;
                       word_add stackpointer (word 160), 64]))
          (\s s'. T)`,
  CONCRETIZE_F_EVENTS_TAC scaffold_enc THEN OPEN_ENC THEN
  (* Top split at 0xdd0 (main region -> tail region). *)
  ENSURES_EVENTS_SEQUENCE_TAC `pc + 0xdd0`
   `\s. read X0 s = word_add in_p (word (64 * loop_count)) /\
        read X2 s = word_add out_p (word (64 * loop_count)) /\
        read X3 s = tag_p /\ read X4 s = ivec_p /\ read X6 s = htable_p /\
        read SP s = stackpointer /\ read X16 s = word loop_remain` THEN
  CONJ_TAC THENL
   [(* MAIN REGION pc+0x2c -> pc+0xdd0. *)
    ENSURES_EVENTS_SEQUENCE_TAC `pc + 0xb0`
     `\s. read X0 s = in_p /\ read X2 s = out_p /\ read X3 s = tag_p /\
          read X4 s = ivec_p /\ read X6 s = htable_p /\ read SP s = stackpointer /\
          read X1 s = word loop_count /\ read X16 s = word loop_remain` THEN
    CONJ_TAC THENL [SAFE_SIM (1--33) THEN CLOSE_ENC; ALL_TAC] THEN
    ASM_CASES_TAC `loop_count = 0` THENL
     [REDUCE_IF0 `loop_count:num` THEN SAFE_SIM (1--1) THEN CLOSE_ENC; ALL_TAC] THEN
    REDUCE_IFN0 `loop_count:num` THEN
    ASM_CASES_TAC `loop_count = 1` THENL
     [REDUCE_IFEQ `loop_count:num` `1` THEN POP_ASSUM SUBST_ALL_TAC THEN
      SAFE_SIM (1--211) THEN CLOSE_ENC; ALL_TAC] THEN
    REDUCE_IFNE `loop_count:num` `1` THEN
    ASM_CASES_TAC `loop_count = 2` THENL
     [REDUCE_IFEQ `loop_count:num` `2` THEN POP_ASSUM SUBST_ALL_TAC THEN
      SAFE_SIM (1--422) THEN CLOSE_ENC; ALL_TAC] THEN
    REDUCE_IFNE `loop_count:num` `2` THEN
    SUBGOAL_THEN `3 <= loop_count` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ENSURES_EVENTS_WHILE_UP2_TAC `loop_count - 2` `pc + 0x560` `pc + 0x8a8`
     `\i s. read X0 s = word_add in_p (word (64 * i + 128)) /\
            read X2 s = word_add out_p (word (64 * i + 64)) /\
            read X3 s = tag_p /\ read X4 s = ivec_p /\ read X6 s = htable_p /\
            read SP s = stackpointer /\ read X16 s = word loop_remain /\
            read X1 s = word (loop_count - 2 - i)` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_ARITH_TAC;
      BEQ_NZ `1` THEN BEQ_NZ `2` THEN SAFE_SIM (1--300) THEN CLOSE_ENC;
      REWRITE_TAC[] THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
      SUBGOAL_THEN `loop_count - 2 < 2 EXP 64` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      SAFE_SIM (1--210) THEN CLOSE_ENC;
      SAFE_SIM (1--122) THEN CLOSE_ENC];
    ALL_TAC] THEN
  (* TAIL REGION pc+0xdd0 -> pc+0xee4. *)
  ASM_CASES_TAC `loop_remain = 0` THENL
   [REDUCE_IF0 `loop_remain:num` THEN SAFE_SIM (1--9) THEN CLOSE_ENC; ALL_TAC] THEN
  REDUCE_IFN0 `loop_remain:num` THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `loop_remain:num` `pc + 0xde0` `pc + 0xed0`
   `\i s. read X0 s = word_add in_p (word (64 * loop_count + 16 * i)) /\
          read X2 s = word_add out_p (word (64 * loop_count + 16 * i)) /\
          read X3 s = tag_p /\ read X4 s = ivec_p /\ read X6 s = htable_p /\
          read SP s = stackpointer /\ read X16 s = word (loop_remain - i)` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [SAFE_SIM (1--4) THEN CLOSE_ENC;
    ALL_TAC;
    REWRITE_TAC[] THEN SAFE_SIM (1--5) THEN CLOSE_ENC] THEN
  REWRITE_TAC[] THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
  SAFE_SIM (1--60) THEN CLOSE_ENC);;

let AES256_GCM_ENC_SUBROUTINE_SAFE = prove
 (`exists f_events.
    forall e in_p len_bits out_p tag_p ivec_p key_p htable_p pc stackpointer returnaddress.
      aligned 16 stackpointer /\
      ALLPAIRS nonoverlapping
        [(out_p, 16 * val len_bits DIV 128); (tag_p, 16); (ivec_p, 16);
         (word_sub stackpointer (word 224), 224)]
        [(word pc, LENGTH aes256_gcm_enc_mc);
         (in_p,  16 * val len_bits DIV 128); (key_p, 240); (htable_p, 192)] /\
      PAIRWISE nonoverlapping
        [(out_p, 16 * val len_bits DIV 128); (tag_p, 16); (ivec_p, 16);
         (word_sub stackpointer (word 224), 224)]
      ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) aes256_gcm_enc_mc /\
               read PC s = word pc /\ read SP s = stackpointer /\ read X30 s = returnaddress /\
               C_ARGUMENTS [in_p; len_bits; out_p; tag_p; ivec_p; key_p; htable_p] s /\
               read events s = e)
          (\s. read PC s = returnaddress /\
               (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events in_p out_p tag_p ivec_p key_p htable_p len_bits pc
                           (word_sub stackpointer (word 224)) returnaddress /\
                    memaccess_inbounds e2
                      [in_p, 16 * val len_bits DIV 128; tag_p, 16; ivec_p, 16; key_p, 240; htable_p, 192;
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
         else APPEND
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
           else if val len_bits DIV 128 DIV 4 = 2 then
             f_ev_m2 in_p out_p tag_p ivec_p key_p htable_p len_bits pc stackpointer returnaddress
           else APPEND
               (f_ev_drain in_p out_p tag_p ivec_p key_p htable_p len_bits pc stackpointer returnaddress)
               (APPEND
                 (ENUMERATEL (val len_bits DIV 128 DIV 4 - 2)
                   (\i. f_ev_steady in_p out_p tag_p ivec_p key_p htable_p len_bits pc stackpointer returnaddress i))
                 (f_ev_fill in_p out_p tag_p ivec_p key_p htable_p len_bits pc stackpointer returnaddress)))
          (f_ev_pro in_p out_p tag_p ivec_p key_p htable_p len_bits pc stackpointer returnaddress)))
      :(uarch_event) list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  GEN_TAC THEN W64_GEN_TAC `len_bits:num` THEN
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
  WORD_FORALL_OFFSET_TAC 224 THEN GEN_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS] THEN
  REWRITE_TAC[ALLPAIRS; PAIRWISE; ALL; fst AES256_GCM_ENC_EXEC] THEN
  ABBREV_TAC `nblocks     = len_bits DIV 128` THEN
  ABBREV_TAC `loop_count  = nblocks DIV 4` THEN
  ABBREV_TAC `loop_remain = nblocks MOD 4` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `loop_count < 2 EXP 64 /\ loop_remain < 2 EXP 64 /\ loop_remain < 4` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [EXPAND_TAC "loop_count" THEN EXPAND_TAC "nblocks" THEN REWRITE_TAC[DIV_DIV] THEN
      TRANS_TAC LET_TRANS `len_bits:num` THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
      EXPAND_TAC "loop_remain" THEN TRANS_TAC LTE_TRANS `4` THEN SIMP_TAC[MOD_LT_EQ; ARITH_RULE `~(4 = 0)`] THEN ARITH_TAC;
      EXPAND_TAC "loop_remain" THEN SIMP_TAC[MOD_LT_EQ; ARITH_RULE `~(4 = 0)`]]; ALL_TAC] THEN
  SUBGOAL_THEN `val(word loop_count:int64) = loop_count /\ val(word loop_remain:int64) = loop_remain` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC VAL_WORD_EQ THEN ASM_REWRITE_TAC[DIMINDEX_64]; ALL_TAC] THEN
  SUBGOAL_THEN `nblocks = 4 * loop_count + loop_remain` SUBST_ALL_TAC THENL
   [UNDISCH_TAC `nblocks DIV 4 = loop_count` THEN UNDISCH_TAC `nblocks MOD 4 = loop_remain` THEN ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN

  (* Split at pc+0xee4 (core end): region A = prologue+core; region B = epilogue. *)
  ENSURES_EVENTS_SEQUENCE_TAC `pc + 0xee4`
   `\s. read SP s = stackpointer /\
        read (memory :> bytes64 (word_add stackpointer (word 88))) s = returnaddress` THEN
  CONJ_TAC THENL
   [(* REGION A: pc -> pc+0xee4 (prologue + full core). *)
    ENSURES_EVENTS_SEQUENCE_TAC `pc + 0xdd0`
     `\s. read X0 s = word_add in_p (word (64 * loop_count)) /\
          read X2 s = word_add out_p (word (64 * loop_count)) /\
          read X3 s = tag_p /\ read X4 s = ivec_p /\ read X6 s = htable_p /\
          read SP s = stackpointer /\ read X16 s = word loop_remain /\
          read (memory :> bytes64 (word_add stackpointer (word 88))) s = returnaddress` THEN
    CONJ_TAC THENL
     [(* MAIN REGION pc -> pc+0xdd0. *)
      ENSURES_EVENTS_SEQUENCE_TAC `pc + 0xb0`
       `\s. read X0 s = in_p /\ read X2 s = out_p /\ read X3 s = tag_p /\
            read X4 s = ivec_p /\ read X6 s = htable_p /\ read SP s = stackpointer /\
            read X1 s = word loop_count /\ read X16 s = word loop_remain /\
            read (memory :> bytes64 (word_add stackpointer (word 88))) s = returnaddress` THEN
      CONJ_TAC THENL [SAFE_SIM (1--44) THEN CLOSE_ENC_SUB; ALL_TAC] THEN
      ASM_CASES_TAC `loop_count = 0` THENL
       [REDUCE_IF0 `loop_count:num` THEN SAFE_SIM (1--1) THEN CLOSE_ENC_SUB; ALL_TAC] THEN
      REDUCE_IFN0 `loop_count:num` THEN
      ASM_CASES_TAC `loop_count = 1` THENL
       [REDUCE_IFEQ `loop_count:num` `1` THEN POP_ASSUM SUBST_ALL_TAC THEN
        SAFE_SIM (1--211) THEN CLOSE_ENC_SUB; ALL_TAC] THEN
      REDUCE_IFNE `loop_count:num` `1` THEN
      ASM_CASES_TAC `loop_count = 2` THENL
       [REDUCE_IFEQ `loop_count:num` `2` THEN POP_ASSUM SUBST_ALL_TAC THEN
        SAFE_SIM (1--422) THEN CLOSE_ENC_SUB; ALL_TAC] THEN
      REDUCE_IFNE `loop_count:num` `2` THEN
      SUBGOAL_THEN `3 <= loop_count` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      ENSURES_EVENTS_WHILE_UP2_TAC `loop_count - 2` `pc + 0x560` `pc + 0x8a8`
       `\i s. read X0 s = word_add in_p (word (64 * i + 128)) /\
              read X2 s = word_add out_p (word (64 * i + 64)) /\
              read X3 s = tag_p /\ read X4 s = ivec_p /\ read X6 s = htable_p /\
              read SP s = stackpointer /\ read X16 s = word loop_remain /\
              read X1 s = word (loop_count - 2 - i) /\
              read (memory :> bytes64 (word_add stackpointer (word 88))) s = returnaddress` THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [ASM_ARITH_TAC;
        BEQ_NZ `1` THEN BEQ_NZ `2` THEN SAFE_SIM (1--300) THEN CLOSE_ENC_SUB;
        REWRITE_TAC[] THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
        SUBGOAL_THEN `loop_count - 2 < 2 EXP 64` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
        SAFE_SIM (1--210) THEN CLOSE_ENC_SUB;
        SAFE_SIM (1--122) THEN CLOSE_ENC_SUB];
      ALL_TAC] THEN
    (* TAIL REGION pc+0xdd0 -> pc+0xee4. *)
    ASM_CASES_TAC `loop_remain = 0` THENL
     [REDUCE_IF0 `loop_remain:num` THEN SAFE_SIM (1--9) THEN CLOSE_ENC_SUB; ALL_TAC] THEN
    REDUCE_IFN0 `loop_remain:num` THEN
    ENSURES_EVENTS_WHILE_UP2_TAC `loop_remain:num` `pc + 0xde0` `pc + 0xed0`
     `\i s. read X0 s = word_add in_p (word (64 * loop_count + 16 * i)) /\
            read X2 s = word_add out_p (word (64 * loop_count + 16 * i)) /\
            read X3 s = tag_p /\ read X4 s = ivec_p /\ read X6 s = htable_p /\
            read SP s = stackpointer /\ read X16 s = word (loop_remain - i) /\
            read (memory :> bytes64 (word_add stackpointer (word 88))) s = returnaddress` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [SAFE_SIM (1--4) THEN CLOSE_ENC_SUB;
      ALL_TAC;
      REWRITE_TAC[] THEN SAFE_SIM (1--5) THEN CLOSE_ENC_SUB] THEN
    REWRITE_TAC[] THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
    SAFE_SIM (1--60) THEN CLOSE_ENC_SUB;

    (* REGION B: pc+0xee4 -> returnaddress (epilogue: 10 ldp + add sp + ret = 12 steps). *)
    SAFE_SIM (1--12) THEN CLOSE_ENC_SUB]);;
