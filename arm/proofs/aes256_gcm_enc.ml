(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Functional correctness, constant-time and memory-safety proofs of the     *)
(* AES-256-GCM bulk encryption kernel aes256_gcm_enc, the 4-way              *)
(* software-pipelined kernel.                                                *)
(*                                                                           *)
(* The kernel processes the len_bits DIV 128 whole 16-byte blocks of its     *)
(* input: block i is encrypted in counter mode with the counter block        *)
(* ctr_block nonce (i + c), the ciphertext is folded into the GHASH tag, and *)
(* the tag and the next counter block ctr_block nonce (nblocks + c) are      *)
(* written back; X0 returns the byte length len_bits DIV 8.  The output may  *)
(* be the input buffer itself (in-place operation).                          *)
(*                                                                           *)
(* Control flow (offsets in the trimmed code, see below; 965 instructions):  *)
(*   preamble 0x2c..0xac; cbz x1 at 0xb0 -> 0xdd0 (loop_count = 0)           *)
(*   cmp x1,#1; b.eq at 0xb8 -> 0xa90 (loop_count = 1)                       *)
(*   fill 0xbc..0x558; cbz x1 at 0x55c -> 0x8a8 (loop_count = 2)             *)
(*   loop head 0x560; body 0x560..0x8a0; cbnz x1 at 0x8a4 -> 0x560           *)
(*   drain 0x8a8..0xa88; b at 0xa8c -> 0xdd0                                 *)
(*   iter_1 block 0xa90..0xdcc (loop_count = 1), falling through to 0xdd0    *)
(*   key-table reloads 0xdd0..0xdd8; cbz x16 at 0xddc -> 0xed0               *)
(*   tail loop 0xde0..0xecc; tag and counter stores 0xed0..0xee0; ret 0xf10  *)
(*                                                                           *)
(* The core theorem AES256_GCM_ENC_CORRECT runs from pc + 0x2c, after the    *)
(* register saves, to pc + 0xee4, before the restores.  The preamble (round  *)
(* keys, tag, counter registers, block counts and key table) ends at         *)
(* pc + 0xb0 and CORE_FROM88 covers the rest.  The loop over groups of four  *)
(* blocks is software-pipelined: the fill completes group 0 and starts group *)
(* 1, each iteration completes one group and starts the next, and the drain  *)
(* completes the last one.  So the loop invariant swp_inv i, asserted at the *)
(* loop head pc + 0x560, records the partial encryptions and the inputs of   *)
(* group i besides the GHASH accumulator and the output of groups 0..i-1,    *)
(* and the fill establishes it at i = 1.  The stepped legs are FILL_TO_CBZ   *)
(* (pc + 0xbc -> pc + 0x55c), BODYLEG (one iteration, pc + 0x560 ->          *)
(* pc + 0x8a4), DRAINLEG_8A8 (pc + 0x8a8 -> pc + 0xdd0), ITER1_LEG           *)
(* (loop_count = 1, pc + 0xb0 -> pc + 0xdd0) and TAILLEG (the single-block   *)
(* tail loop and the tag and counter stores, pc + 0xdd0 -> pc + 0xee4).  The *)
(* one-instruction hops FILLLEG, LC2_PARTA and DRAINLEG share the fill and   *)
(* drain simulations between the loop_count cases.  MAINLEG composes         *)
(* FILLLEG, an ENSURES_WHILE_UP over loop_count - 3 iterations at pc + 0x560 *)
(* and BODY_DRAIN (one more iteration and DRAINLEG); LEG_LC0, LEG_LC1 and    *)
(* LEG_LC2 cover loop_count = 0, 1 and 2, and CORE_FROM88 dispatches on      *)
(* loop_count before TAILLEG.  The safety theorems follow the same regions   *)
(* with the event-tracking simulator.                                        *)
(*                                                                           *)
(* The specification vocabulary (ctr_block, aes_ctr_block,                   *)
(* nist_cipher_block, htable_mem_4) is in arm/proofs/utils/aes_gcm_spec.ml;  *)
(* the lemmas and tactics shared with the other AES-GCM proofs are in        *)
(* arm/proofs/utils/aes_gcm_common.ml.                                       *)
(*                                                                           *)
(* The code begins with a BTI landing pad (bti c).  The proofs are about the *)
(* trimmed code aes256_gcm_enc_tmc without it, which is also the code of a   *)
(* -DNO_IBT build, so all offsets above are offsets in that code; the        *)
(* subroutine theorems for the full code are derived by ARM_ADD_IBT_RULE.    *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "arm/proofs/utils/aes_gcm_common.ml";;

(* ------------------------------------------------------------------------- *)
(* The machine code.                                                         *)
(* ------------------------------------------------------------------------- *)

let aes256_gcm_enc_mc = define_assert_from_elf "aes256_gcm_enc_mc" "arm/aes_gcm/aes256_gcm_enc.o"
[
  0xd503245f;       (* arm_BTI *)
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

(* The code without its BTI landing pad, which the proofs are about (see the *)
(* header).                                                                  *)

let aes256_gcm_enc_tmc = define_trimmed "aes256_gcm_enc_tmc" aes256_gcm_enc_mc;;

let AES256_GCM_ENC_EXEC =
  ARM_MK_EXEC_RULE aes256_gcm_enc_tmc;;


(* ------------------------------------------------------------------------- *)
(* The loop invariant.                                                       *)
(* ------------------------------------------------------------------------- *)

(* swpgrp gt acc i blk is the GHASH accumulator after i groups of four blocks
   of blk, the value the loop keeps in Q29.  The ext v30,v29,v29,#8 in the loop
   body puts Q29 half-swapped (byteswap128) into Q30, but the Karatsuba packing
   of the reduction reads the two 64-bit halves in swapped order as well, so
   the two swaps cancel and the recurrence has no byteswap128.
   SWPGRP_IS_NIST_GHASH relates swpgrp to nist_ghash; the ext at the end of the
   drain leaves byteswap128 of the accumulator in Q30. *)
let swpgrp = define
 `swpgrp (gt:int128) (acc:int128) 0 (blk:num->int128) = acc /\
  swpgrp gt acc (SUC i) blk =
    ghash_polyval_acc gt (swpgrp gt acc i blk)
      [blk (4*i); blk (4*i+1); blk (4*i+2); blk (4*i+3)]`;;

(* The invariant swp_inv i at the loop head pc + 0x560: groups 0..i-1 are
   stored and hashed (Q29), group i is in flight, and X0 already points at
   group i+1.  For group i, the input blocks XOR the last round key are in
   the stack slots sp+160, sp+176, sp+192 (blocks 4i..4i+2) and in X26/X24
   (block 4i+3), and the counter blocks are partly encrypted: Q3 = aes11c
   (block 4i), Q8 = aes1c (4i+1), Q4 = aes7c (4i+2) and Q31 = aes6c (4i+3).
   The round keys are in Q18..Q28 (rk0..rk10), Q15..Q17 (rk11..rk13) and
   X20/X21 (the two halves of rk14). *)
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
                   (nist_cipher_block aes256_cipher c nonce rk inblock) /\
    read Q2 s = byteswap128 (h_power (ghash_twist (aes256_cipher (word 0) rk)) 3) /\
    read Q13 s = byteswap128 (h_power (ghash_twist (aes256_cipher (word 0) rk)) 0) /\
    read X1 s = word (loop_count - (i+1)) /\ read X15 s = word(len_bits DIV 8) /\ read X16 s = word loop_remain /\
    htable_mem_4 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s /\
    (!j. 4 * i <= j /\ j < nblocks ==> read (memory :> bytes128 (word_add in_p (word(16*j)))) s = inblock j) /\
    (!j. j < 4 * i ==> read (memory :> bytes128 (word_add out_p (word(16*j)))) s =
             word_xor (aes_ctr_block aes256_cipher c nonce rk j) (inblock j)) /\
    read (memory :> bytes128 (word_add stackpointer (word 160))) s = word_xor (inblock (4*i+0)) (word_reversefields 8 (EL 14 rk)) /\
    read (memory :> bytes128 (word_add stackpointer (word 176))) s = word_xor (inblock (4*i+1)) (word_reversefields 8 (EL 14 rk)) /\
    read (memory :> bytes128 (word_add stackpointer (word 192))) s = word_xor (inblock (4*i+2)) (word_reversefields 8 (EL 14 rk)) /\
    read Q31 s = aes6c nonce rk (4*i+c+3) /\
    read X26 s = word_subword (word_xor (inblock (4*i+3)) (word_reversefields 8 (EL 14 rk)):int128) (64,64):int64 /\
    read X24 s = word_subword (word_xor (inblock (4*i+3)) (word_reversefields 8 (EL 14 rk)):int128) (0,64):int64`;;

(* ------------------------------------------------------------------------- *)
(* Stepping a leg: the pruning policy, the registers whose latest values the *)
(* stepper keeps, the stack-store merge sites, and the goal, setup and       *)
(* stepper of BODYLEG (swp_inv i at pc + 0x560 -> swp_inv (i+1) at           *)
(* pc + 0x8a4, 209 steps).                                                   *)
(* ------------------------------------------------------------------------- *)

(* The pruning policy of the steppers of this proof: the in_p reads and all
   quantified facts are always kept, with the stale sweep (see SWP_STEP_TAC_P
   in utils/aes_gcm_common.ml). *)
let enc_prune =
  { anchors = []; slots = []; families = [];
    exempt = (fun c -> try free_in `in_p:int64` (lhs c) with _ -> false);
    all_foralls = true; stale_gc = true };;
let gkeepN keeplist th sname = SWP_STEP_TAC_P enc_prune keeplist th sname;;
(* The (pointer, state index) of a fact read C sK = V whose component C
   mentions tag_p or ivec_p: a family for SWP_STEP_TAC_P. *)
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
(* The stepper of the fill: as gkeepN, but it also keeps the reads of the tag_p
   and ivec_p memory, which gkeepN would drop and the fill's postcondition
   needs; only the latest read per pointer is kept, so that stale copies do not
   pile up.  With the nonoverlapping facts of tag_p and ivec_p against the
   stack slots in fill_goal, ENSURES_FINAL_STATE_TAC carries the latest read
   across the stack stores to the final state s296. *)
let gkeepF keeplist th sname =
  SWP_STEP_TAC_P { enc_prune with families = [get_membyteread] } keeplist th sname;;

(* The registers whose latest values the steppers keep: the carried AES
   partials Q3, Q4, Q8 and Q31, the GHASH and key-power registers, the
   reduction constant Q7, the round keys Q16, Q17 and Q28, and the scalar
   counter and input lanes. *)
let REDSETX256 = ["Q1";"Q2";"Q3";"Q4";"Q5";"Q6";"Q7";"Q8";"Q11";"Q13";"Q14";"Q16";"Q17";"Q28";"Q29";"Q30";"Q31";
                  "X7";"X8";"X10";"X11";"X13";"X14";"X17";"X22";"X23";"X24";"X25";"X26";"X28";"X29";"X30"];;
(* The scalar registers introduced as ghosts (GHOST_INTRO_TAC) at the start
   of a leg, so that their initial values stay available as variables. *)
let ghost_lanes256 = ["X7";"X8";"X17";"X22";"X23";"X24";"X25";"X26";"X28";"X29";"X30";"X10";"X14";"X19";"X27"];;

(* The stack stores of the loop body, as (step, sp offset) pairs for
   MERGE_CTR128_TAC: counter blocks at steps 49, 92, 98 and 109, input blocks
   XOR the last round key at steps 27, 118, 171 and 179. *)
let merges256 = [(27,208);(49,160);(92,192);(98,208);(109,176);(118,192);(171,160);(179,176)];;

(* Split the 128-bit input reads of blocks 4i..4i+7 (group i and group i+1; the
   body loads the latter) into 64-bit halves (SPLIT_INPUT_CONV). *)
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

(* Leg pre/postconditions over this kernel's code (see mk_leg_state). *)
let leg_state = mk_leg_state `aes256_gcm_enc_tmc`;;

(* The body-leg goal, swp_inv i at pc + 0x560 -> swp_inv (i+1) at
   pc + 0x8a4, for i < loop_count - 1 (mk_body_goal_b takes the bound). *)
let mk_body_goal_b bound inv =
  mk_imp(subst [bound,`i < loop_count - 2`] `([EL 0 rk; EL 1 rk; EL 2 rk; EL 3 rk; EL 4 rk; EL 5 rk; EL 6 rk; EL 7 rk;
      EL 8 rk; EL 9 rk; EL 10 rk; EL 11 rk; EL 12 rk; EL 13 rk; EL 14 rk]:(int128)list = rk) /\
     len_bits DIV 128 = nblocks /\ nblocks DIV 4 = loop_count /\ nblocks MOD 4 = loop_remain /\
     2 <= loop_count /\ i < loop_count - 2 /\ 16 * nblocks < 2 EXP 64 /\ aligned 16 (stackpointer:int64) /\
     nonoverlapping (out_p:int64,16 * nblocks) (word pc:int64,3860) /\
     (in_p:int64 = out_p \/
      nonoverlapping (in_p:int64,16 * nblocks) (out_p:int64,16 * nblocks)) /\
     nonoverlapping (out_p:int64,16 * nblocks) (htable_p:int64,96) /\
     nonoverlapping (out_p:int64,16 * nblocks) (tag_p:int64,16) /\
     nonoverlapping (out_p:int64,16 * nblocks) (ivec_p:int64,16) /\
     nonoverlapping (out_p:int64,16*nblocks) (word_add stackpointer (word 160):int64,64) /\
     nonoverlapping (tag_p:int64,16) (word pc:int64,3860) /\
     nonoverlapping (in_p:int64,16*nblocks) (tag_p:int64,16) /\
     nonoverlapping (tag_p:int64,16) (htable_p:int64,96) /\
     nonoverlapping (tag_p:int64,16) (word_add stackpointer (word 160):int64,64) /\
     nonoverlapping (ivec_p:int64,16) (word pc:int64,3860) /\
     nonoverlapping (in_p:int64,16*nblocks) (ivec_p:int64,16) /\
     nonoverlapping (ivec_p:int64,16) (htable_p:int64,96) /\
     nonoverlapping (ivec_p:int64,16) (word_add stackpointer (word 160):int64,64) /\
     nonoverlapping (tag_p:int64,16) (ivec_p:int64,16) /\
     nonoverlapping (word_add stackpointer (word 160):int64,64) (word pc:int64,3860) /\
     nonoverlapping (in_p:int64,16*nblocks) (word_add stackpointer (word 160):int64,64) /\
     nonoverlapping (word_add stackpointer (word 160):int64,64) (htable_p:int64,96)`,
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

(* The leg setup: introduce the ghost lanes, ENSURES_INIT_TAC, unfold
   htable_mem_4, split the input reads, then abbreviate as init_k variables
   the remaining reads read C s0, except the in_p reads and those mentioning
   j. *)
let setup_tac_s split =
  INTRO_HYPS_TAC THEN REWRITE_TAC[fst AES256_GCM_ENC_EXEC] THEN
  MAP_EVERY (fun rn -> GHOST_INTRO_TAC (mk_var("ghost_"^rn,`:int64`)) (parse_term("read "^rn))) ghost_lanes256 THEN
  ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV BETA_CONV)) THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_4]) THEN REWRITE_TAC[htable_mem_4] THEN
  split THEN INPUT_LEG_TAC [] THEN
  (fun (asl,w) ->
    let jv = `j:num` in
    let reads0 = setify(flat(map (fun (_,th) -> find_terms (fun t -> try let h,a=strip_comb t in
         fst(dest_const h)="read" && length a=2 && string_of_term(hd(tl a))="s0" with _->false) (concl th)) asl)) in
    let toab = filter (fun t -> not(free_in jv t) && not(free_in `in_p:int64` t)
                              && string_of_term t <> "read PC s0") reads0 in
    (EVERY (List.mapi (fun k t -> ABBREV_TAC (mk_eq(mk_var(Printf.sprintf "init_%d" k, type_of t), t))) toab)) (asl,w));;
let setup_tac = setup_tac_s INPUT_SPLIT_TAC256;;

(* The body stepper: steps 1..209 (pc + 0x560 .. pc + 0x8a0) with gkeepN over
   REDSETX256, the subword and address normalization after each step, and
   MERGE_CTR128_TAC at the merges256 sites; the cbnz at pc + 0x8a4 is left to
   the loop composition.  step_body_prefix stops before
   ENSURES_FINAL_STATE_TAC, so the facts about s209 are still assumptions. *)
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
       (1--209)) (asl,w)) THEN
  RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV THENC
                           ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV THENC
                           IN_P_ADDR_FOLD_CONV));;
let step_body_prefix = step_body_prefix_s setup_tac;;
let step_body_tac_s prefix =
  prefix THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];;
let step_body_tac = step_body_tac_s step_body_prefix;;

(* ------------------------------------------------------------------------- *)
(* The closers for the conjuncts of swp_inv (i+1) at the end of a leg.       *)
(* ------------------------------------------------------------------------- *)

(* The pointers and X13. *)
let close_ptr : tactic =
  REWRITE_TAC[ARITH_RULE `64*(i+1)=64*i+64`; LEFT_ADD_DISTRIB] THEN CONV_TAC WORD_RULE;;
let close_x13 : tactic =
  REWRITE_TAC[ZX_COUNTER_UD] THEN AP_TERM_TAC THEN REWRITE_TAC[GSYM WORD_ADD] THEN AP_TERM_TAC THEN ARITH_TAC;;
(* The carried AES partials Q3 = aes11c (4*(i+1)+c), Q4 = aes7c
   (4*(i+1)+c+2) and Q8 = aes1c (4*(i+1)+c+1): the stepped value applies the
   rounds to the counter block built from word (4*i+c+4) + K, the X13 value
   plus K; unfold the definition and fold that block with mk_cbv. *)
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

(* Normalize the addresses word (64*(i+1)+K) of the input reads to the
   split-input form word (64*i+(64+K)).  The body reads its input at
   X0 = in_p + 64*(i+1); the ldp offsets 0, 8, .., 56 are the halves of
   blocks 4i+4..4i+7. *)
let SLOT_ADDR_NORM = [
  ARITH_RULE `64*(i+1) = 64*i+64`; ARITH_RULE `64*(i+1)+8 = 64*i+72`;
  ARITH_RULE `64*(i+1)+16 = 64*i+80`; ARITH_RULE `64*(i+1)+24 = 64*i+88`;
  ARITH_RULE `64*(i+1)+32 = 64*i+96`; ARITH_RULE `64*(i+1)+40 = 64*i+104`;
  ARITH_RULE `64*(i+1)+48 = 64*i+112`; ARITH_RULE `64*(i+1)+56 = 64*i+120`];;

(* The stack slots sp+160, sp+176, sp+192 at i+1 hold block 4*(i+1)+k XOR
   the last round key for k = 0, 1, 2, i.e. blocks 4i+4..4i+6, which the
   body reads at X0 = in_p + 64*(i+1).  The stepped
   value is a word_join of the XORs of the two 64-bit halves: fold the half
   reads with the split-input facts, then recombine the lanes. *)
let close_lanejoin : tactic =
  fun (asl,w) ->
    (* the split-input facts among the assumptions,
       read (memory :> bytes64 ..) s = word_subword (inblock ..) .. *)
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

(* X26/X24 = the high and low halves of
   word_xor (inblock (4*(i+1)+3)) (word_reversefields 8 (EL 14 rk)), block
   4i+7.  The stepped value is the XOR of the bytes64 read at
   in_p+64*(i+1)+48 or +56 with the matching half of the key: fold the read
   with the split-input facts and push the subword through the XOR
   (WORD_SUBWORD_XOR). *)
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

(* Q31 = aes6c nonce rk (4*(i+1)+c+3), as close_aes1c and close_aes7c: the
   stepped counter is word_add (word (4*i+c+4)) (word 3), block 4*(i+1)+3,
   the last block of the group. *)
let close_aes6c : tactic =
  REWRITE_TAC[aes6c] THEN REPEAT(AP_TERM_TAC ORELSE AP_THM_TAC) THEN REWRITE_TAC[ZXNEST4;ZX_COUNTER_UD] THEN
  SUBGOAL_THEN `word_add (word (4*i+c+4):int32) (word 3) = word(4*(i+1)+c+3):int32` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM WORD_ADD] THEN AP_TERM_TAC THEN ARITH_TAC; ALL_TAC] THEN ACCEPT_TAC (mk_cbv `4*(i+1)+c+3`);;

(* The X1 decrement: word_sub (word (loop_count-(i+1))) (word 1) =
   word (loop_count-((i+1)+1)). *)
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

(* The output-block keystream identities that close_goal9 leaves. *)
let close_ksfold : tactic =
  fun (asl,w) ->
    let rkth = try snd(find (fun (_,th) -> concl th = rk15) asl) with _ -> failwith "close_ksfold: no rk-hyp" in
    (REPEAT CONJ_TAC THEN
     REWRITE_TAC[JOIN_SUBWORD_RECOMBINE] THEN
     REWRITE_TAC[GSYM AES14P_VIA_AES7C; GSYM AES14P_VIA_AES11C; GSYM AES14P_VIA_AES1C; GSYM AES14P_VIA_AES6C] THEN
     REWRITE_TAC[MATCH_MP KEYSTREAM_FOLD256 rkth]) (asl,w);;

(* The output forall j < 4*(i+1): split into j < 4*i (from the invariant)
   and the four new blocks 4i..4i+3, stored at X2 = out_p + 64*i; reconstruct
   each with XOR_AES256_CIPHER_RECONSTRUCT and KEYSTREAM_FOLD256. *)
let close_goal9 : tactic =
  fun (asl,w) ->
    let rkth = try snd(find (fun (_,th) -> concl th = rk15) asl) with _ -> failwith "close_goal9: no rk-hyp" in
    (REWRITE_TAC[ARITH_RULE `j < 4 * (i+1) <=>
                          j < 4 * i \/ j = 4*i+0 \/ j = 4*i+1 \/ j = 4*i+2 \/ j = 4*i+3`] THEN
     ASM_REWRITE_TAC[TAUT `p \/ q ==> r <=> (p ==> r) /\ (q ==> r)`] THEN
     REWRITE_TAC[FORALL_AND_THM; FORALL_UNWIND_THM2] THEN
     (* the store addresses of blocks 4i..4i+3: out_p + 64*i + 0/16/32/48,
        the form of the store facts *)
     REWRITE_TAC[ARITH_RULE `16 * (4*i+0) = 64*i`; ARITH_RULE `16 * (4*i+1) = 64*i+16`;
        ARITH_RULE `16 * (4*i+2) = 64*i+32`; ARITH_RULE `16 * (4*i+3) = 64*i+48`] THEN
     ASM_REWRITE_TAC[] THEN
     REWRITE_TAC[ARITH_RULE `4*i+0 = 4*i`] THEN ASM_REWRITE_TAC[] THEN
     REWRITE_TAC[CTR_BLOCK_BUILD_INSERT] THEN
     REWRITE_TAC[SCALAR_RK_RECONSTRUCT] THEN
     REWRITE_TAC[XOR_AES256_CIPHER_RECONSTRUCT] THEN
     ASM_REWRITE_TAC[MAP; WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
     REWRITE_TAC[aes_ctr_block] THEN
     REWRITE_TAC[ARITH_RULE `4 * i + c + 3 = (4 * i + 3) + c`;
                 ARITH_RULE `4 * i + c + 2 = (4 * i + 2) + c`;
                 ARITH_RULE `4 * i + c + 1 = (4 * i + 1) + c`;
                 ARITH_RULE `4 * i + 0 = 4 * i`] THEN ASM_REWRITE_TAC[] THEN
     REPEAT CONJ_TAC THEN
     REWRITE_TAC[JOIN_SUBWORD_RECOMBINE] THEN
     REWRITE_TAC[GSYM AES14P_VIA_AES7C; GSYM AES14P_VIA_AES11C; GSYM AES14P_VIA_AES1C; GSYM AES14P_VIA_AES6C] THEN
     REWRITE_TAC[MATCH_MP KEYSTREAM_FOLD256 rkth]) (asl,w);;

(* The output forall for group 0 (j < 4) at the end of the fill.  The
   symbolic 64*i and 4*i+k terms of close_goal9 would stay unreduced at
   i = 0 and not match the concrete store facts (out_p+0/16/32/48, inblock
   0..3), so this variant splits j < 4 concretely and reduces all the
   arithmetic, then runs the same store-fact rewriting and reconstruction. *)
let close_goal9_i0 : tactic =
  fun (asl,w) ->
    let rkth = try snd(find (fun (_,th) -> concl th = rk15) asl) with _ -> failwith "close_goal9_i0: no rk-hyp" in
    (REWRITE_TAC[ARITH_RULE `j < 4 <=> j = 0 \/ j = 1 \/ j = 2 \/ j = 3`] THEN
     REWRITE_TAC[TAUT `p \/ q ==> r <=> (p ==> r) /\ (q ==> r)`] THEN
     REWRITE_TAC[FORALL_AND_THM; FORALL_UNWIND_THM2] THEN
     CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
     (* Block 0 is stored by the post-indexed str q1,[x2],#64 at x2 = out_p,
        so its store fact reads out_p while the goal has
        word_add out_p (word 0); WORD_ADD_0 makes them match (blocks 1..3
        have nonzero offsets that match directly). *)
     REWRITE_TAC[WORD_ADD_0] THEN
     ASM_REWRITE_TAC[] THEN
     REWRITE_TAC[CTR_BLOCK_BUILD_INSERT] THEN
     REWRITE_TAC[SCALAR_RK_RECONSTRUCT] THEN
     REWRITE_TAC[XOR_AES256_CIPHER_RECONSTRUCT] THEN
     ASM_REWRITE_TAC[MAP; WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
     REWRITE_TAC[aes_ctr_block; GSYM ADD_ASSOC] THEN
     REWRITE_TAC[ARITH_RULE `(1:num) + c = c + 1`; ARITH_RULE `(2:num) + c = c + 2`;
                 ARITH_RULE `(3:num) + c = c + 3`; ARITH_RULE `(4:num) + c = c + 4`;
                 ARITH_RULE `(0:num) + c = c`] THEN
     CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[] THEN
     REPEAT CONJ_TAC THEN
     REWRITE_TAC[JOIN_SUBWORD_RECOMBINE] THEN
     REWRITE_TAC[GSYM AES14P_VIA_AES7C; GSYM AES14P_VIA_AES11C; GSYM AES14P_VIA_AES1C; GSYM AES14P_VIA_AES6C] THEN
     REWRITE_TAC[MATCH_MP KEYSTREAM_FOLD256 rkth] THEN
     (* Block 0 (the post-indexed store) comes out of
        XOR_AES256_CIPHER_RECONSTRUCT with its counter block still in the
        packed form built by the code, inside aes256_cipher
        (word_reversefields 8 ..), because the CTR_BLOCK_BUILD_INSERT above
        ran before that form appeared.  A final pass normalizes the word_zx
        nest (ZXNEST4, ZX_COUNTER_UD, GSYM WORD_ADD), folds the packed form
        with CTR_BLOCK_BUILD_INSERT and cancels the double
        word_reversefields 8, giving ctr_block nonce c; blocks 1..3 are
        already closed. *)
     REWRITE_TAC[ZXNEST4; ZX_COUNTER_UD; GSYM WORD_ADD] THEN
     REWRITE_TAC[CTR_BLOCK_BUILD_INSERT] THEN
     REWRITE_TAC[WORD_REVERSEFIELDS_REVERSEFIELDS]) (asl,w);;

(* The MAYCHANGE frame: establish 4*i+3 < nblocks (for the out_p stores),
   then weaken a MAYCHANGE assumption of the leg to the declared frame with
   SUBSUMED_MAYCHANGE_TAC. *)
let close_goal10_b bound : tactic =
  fun (asl,w) ->
    let is_mc c = try can(find_term(fun x->match x with Const("MAYCHANGE",_)->true|_->false)) c with _->false in
    (TRY(SUBGOAL_THEN `4*i+3 < nblocks` ASSUME_TAC THENL
      [MAP_EVERY (fun t -> TRY(UNDISCH_TAC t))
         [`nblocks DIV 4 = loop_count`; bound; `2 <= loop_count`] THEN ARITH_TAC; ALL_TAC]) THEN
     (fun (asl2,w2) ->
        let mcths = List.filter_map (fun (_,th) -> if is_mc(concl th) then Some th else None) asl2 in
        (FIRST (map (fun th -> fun g ->
            (MATCH_MP_TAC(MATCH_MP SUBSUMED_APPLY th) THEN
             REWRITE_TAC[ETA_AX; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
             SUBSUMED_MAYCHANGE_TAC) g) mcths)) (asl2,w2))) (asl,w);;
let close_goal10_b1 = close_goal10_b `i < loop_count - 1`;;
let close_goal10_b2 = close_goal10_b `i < loop_count - 2`;;

(* A higher-order match artifact: CT_TO_NCB on block 4*i in the collapse can
   produce nist_cipher_block with the constant function (\x. inblock (4*i))
   as its input argument.  nist_cipher_block reads only the block at its
   index, so this equals the plain form. *)
let NCB_CONST_FN = prove
 (`nist_cipher_block aes256_cipher c nonce rk (\x:num. inblock (4*i)) (4*i) =
   nist_cipher_block aes256_cipher c nonce rk inblock (4*i)`,
  REWRITE_TAC[nist_cipher_block; cipher_block] THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN REFL_TAC);;

(* The ext v30,v29,v29,#8 on the accumulator x = swpgrp .. i gives
   word_subword (word_join x x) (64,128), which is byteswap128 x.
   byteswap128 is a defined constant, so the proof expands it before
   WORD_BLAST.  close_goal7 rewrites with this. *)
let ACC_JOIN_BYTESWAP = prove
 (`!x:int128. word_subword (word_join x x :int256) (64,128) :int128 = byteswap128 x`,
  GEN_TAC THEN REWRITE_TAC[byteswap128] THEN CONV_TAC WORD_BLAST);;

(* The GHASH step of one group in one lemma: polyval_reduce_g2 of the
   Karatsuba low, high and middle sums of the products of (cbb3,
   h_power gt 0), (cbb2, h_power gt 1), (cbb1, h_power gt 2) and
   (word_xor A cbb0, h_power gt 3) is ghash_polyval_acc gt A
   [cbb0; cbb1; cbb2; cbb3].  The first step is the Karatsuba shuffle (with
   ABBREV_PMULS), the second the batched accumulation
   GHASH_POLYVAL_ACC_BATCHED.  close_goal7 matches it with A := sofar, the
   swpgrp accumulator. *)
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

(* The GHASH conjunct: collapse_q30 folds the keystreams in the reduction
   tower to nist_cipher_block, close_goal7 folds the reduction. *)

(* CT_TO_NCB folds word_xor (word_reversefields 8 (aes256_cipher
   (ctr_block nonce (j + c)) rk)) (inblock j) to word_reversefields 8
   (nist_cipher_block .. j).  For group 0 (the fill and ITER1_LEG) the
   counters are c, c+1, c+2 and c+3, on which the higher-order match of
   CT_TO_NCB goes wrong; these four instances at j = 0..3 match them
   directly. *)
let ct_ncb_concrete =
  [ REWRITE_RULE[ARITH_RULE `(0:num) + c = c`]     (INST [`0`,`j:num`] (SPEC_ALL CT_TO_NCB));
    REWRITE_RULE[ARITH_RULE `(1:num) + c = c + 1`] (INST [`1`,`j:num`] (SPEC_ALL CT_TO_NCB));
    REWRITE_RULE[ARITH_RULE `(2:num) + c = c + 2`] (INST [`2`,`j:num`] (SPEC_ALL CT_TO_NCB));
    REWRITE_RULE[ARITH_RULE `(3:num) + c = c + 3`] (INST [`3`,`j:num`] (SPEC_ALL CT_TO_NCB)) ];;

(* collapse_q30_g g0: fold the ghost pins, the key-power reloads and the
   keystreams of the four blocks of the group in the reduction tower.  With
   g0 (group 0, with literal block indices: the fill and ITER1_LEG) it also
   folds the packed counter blocks and uses ct_ncb_concrete. *)
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
    (* Key-power reloads: the simulation leaves read Q2 sN and read Q13 sN
       (key powers reloaded from the table) as register reads equal to a
       memory read of htable_p + M.  Rewriting with these equations and then
       with htable_mem_4 resolves the key powers in the reduction tower to
       their byteswap128 (h_power ..) and word_join (karatsuba_mid ..)
       values.  Collect the read Q2 and read Q13 facts about states sN. *)
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
     REWRITE_TAC(ghostpins @ hpreads) THEN
     REWRITE_TAC htab_exp THEN
     REWRITE_TAC[JOIN_SUBWORD_RECOMBINE] THEN
     REWRITE_TAC(ghostpins @ hpreads) THEN
     (* Group-0 counter fold (g0): the AES towers of the four group-0 blocks
        read their counter blocks from the merged stack slots, in the packed
        form built by the code.  Normalize the word_zx nest (ZXNEST4,
        ZX_COUNTER_UD, GSYM WORD_ADD), then CTR_BLOCK_BUILD_INSERT folds
        them to word_reversefields 8 (ctr_block nonce cval), the form GSYM
        aes14p needs. *)
     (if g0 then REWRITE_TAC[ZXNEST4; ZX_COUNTER_UD; GSYM WORD_ADD] THEN REWRITE_TAC[CTR_BLOCK_BUILD_INSERT] else ALL_TAC) THEN
     REWRITE_TAC[GSYM AES14P_VIA_AES7C; GSYM AES14P_VIA_AES11C; GSYM AES14P_VIA_AES1C; GSYM AES14P_VIA_AES6C; GSYM aes14p] THEN
     REWRITE_TAC[JOIN_XOR_LANES] THEN
     REWRITE_TAC[ksf] THEN
     REWRITE_TAC[ARITH_RULE `4*i+c+3 = (4*i+3)+c`; ARITH_RULE `4*i+c+2 = (4*i+2)+c`;
                 ARITH_RULE `4*i+c+1 = (4*i+1)+c`; ARITH_RULE `4*i+0 = 4*i`] THEN
     (* For group 0, fold with ct_ncb_concrete before CT_TO_NCB: the group-0
        counters are sums c+K, on which the higher-order match of CT_TO_NCB
        goes wrong (j := c, c := K, a constant-function inblock); with j
        fixed the instances fold cleanly, leaving nothing for CT_TO_NCB in
        those blocks. *)
     (if g0 then REWRITE_TAC ct_ncb_concrete else ALL_TAC) THEN
     REWRITE_TAC[CT_TO_NCB] THEN
     REWRITE_TAC[ARITH_RULE `(4*i+0)+2 = 4*i+2`; ARITH_RULE `(4*i+1)+2 = 4*i+3`;
                 ARITH_RULE `(4*i+2)+2 = 4*i+4`; ARITH_RULE `(4*i+3)+2 = 4*i+5`;
                 ARITH_RULE `4*i+0 = 4*i`] THEN
     REWRITE_TAC[NCB_CONST_FN]) (asl,w);;
let collapse_q30_g0 = collapse_q30_g true;;
let collapse_q30_gi = collapse_q30_g false;;

(* close_goal7, the GHASH conjunct at the end of a body leg: the goal is
   <reduction computed by the code> = swpgrp gt tag0 (i+1) blk.  After
   collapse_q30 the accumulator lanes read byteswap128 (swpgrp .. i), and
   that half-swap cancels the half-swap of the Karatsuba packing
   (WORD_SUBWORD_BYTESWAP128), so CORE_REDUCE_GHASH applies with
   A := swpgrp .. i. *)
(* close_goal7_i0_c: the same at the end of the fill, whose goal has the
   literal swpgrp gt tag0 1 on the right.  The rewrite i + 1 = SUC i of the
   general case does not apply there, so this unfolds swpgrp .. 1 to
   ghash_polyval_acc gt tag0 [blocks 0..3] directly (num_CONV and the
   swpgrp clauses) and abbreviates sofar = tag0 and the concrete
   cipherblock_k, after which the general reconstruction applies unchanged.
   close_goal7_c selects it by the literal 1. *)
let close_goal7_i0_c collapse : tactic =
  fun (asl,w) ->
    (collapse THEN
     (* unfold swpgrp .. 1 on the right to ghash_polyval_acc gt tag0
        [cb0; cb1; cb2; cb3] *)
     GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [num_CONV `1`] THEN
     GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [CONJUNCT2 swpgrp] THEN
     GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [CONJUNCT1 swpgrp] THEN
     CONV_TAC(RAND_CONV(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
     (* concrete abbreviations: the accumulator is tag0 (i = 0) and the
        blocks are 0..3; abbreviate sofar = tag0 first, so that the goal has
        the shape of the general case *)
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
      [`cipherblock_0 = nist_cipher_block aes256_cipher c nonce rk inblock 0`;
       `cipherblock_1 = nist_cipher_block aes256_cipher c nonce rk inblock 1`;
       `cipherblock_2 = nist_cipher_block aes256_cipher c nonce rk inblock 2`;
       `cipherblock_3 = nist_cipher_block aes256_cipher c nonce rk inblock 3`;
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
let close_goal7_c collapse i0 : tactic =
  fun (asl,w) ->
    (* i0 (the fill): if the right-hand side is the literal swpgrp .. 1,
       use close_goal7_i0_c. *)
    if i0 && (try can (find_term (fun t -> match t with
          Comb(Comb(Comb(Comb(Const("swpgrp",_),_),_),n),_) -> n = `1`
          | _ -> false)) (rhs w) with _ -> false)
    then close_goal7_i0_c collapse (asl,w)
    else
    (collapse THEN
     (* Unfold swpgrp (i+1) on the right to
        ghash_polyval_acc gt (swpgrp gt tag0 i blk) [four blocks] first, so
        that swpgrp gt tag0 i blk appears on both sides (the accumulator on
        the left, the seed on the right) and one ABBREV catches both. *)
     GEN_REWRITE_TAC (RAND_CONV o TOP_DEPTH_CONV) [ARITH_RULE `i + 1 = SUC i`] THEN
     GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [CONJUNCT2 swpgrp] THEN
     (* Abbreviate the accumulator swpgrp gt tag0 i blk as sofar (on both
        sides) and fold word_subword (word_join sofar sofar) (64,128) to
        byteswap128 sofar with ACC_JOIN_BYTESWAP, before the half splitting
        of the blocks and key powers below, which would take the accumulator
        apart as well; then abbreviate byteswap128 sofar as bsofar. *)
     ABBREV_TAC `sofar = swpgrp (ghash_twist (aes256_cipher (word 0) rk)) tag0 i (nist_cipher_block aes256_cipher c nonce rk inblock)` THEN
     REWRITE_TAC[ACC_JOIN_BYTESWAP] THEN
     ABBREV_TAC `bsofar:int128 = byteswap128 (sofar:int128)` THEN
     (* Normalize: fold the byte towers of the blocks to nist_cipher_block
        and the half-swapped key powers back, so that
        RECONSTRUCT_POLYVAL_REDUCE_G2 can fold the reduction; bsofar is a
        variable and stays untouched. *)
     REWRITE_TAC[WORD_SUBWORD_REVERSEFIELDS] THEN
     SIMP_TAC[WORD_JOIN_COMBINE_LEMMA; ARITH] THEN
     REWRITE_TAC[WORD_SUBWORD_XOR] THEN
     REWRITE_TAC[WORD_SUBWORD_BYTESWAP128] THEN
     CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
     REWRITE_TAC[WORD_SUBWORD_XOR] THEN
     CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
     MAP_EVERY ABBREV_TAC
      [`cipherblock_0 = nist_cipher_block aes256_cipher c nonce rk inblock (4 * i)`;
       `cipherblock_1 = nist_cipher_block aes256_cipher c nonce rk inblock (4 * i + 1)`;
       `cipherblock_2 = nist_cipher_block aes256_cipher c nonce rk inblock (4 * i + 2)`;
       `cipherblock_3 = nist_cipher_block aes256_cipher c nonce rk inblock (4 * i + 3)`;
       `h0 = h_power (ghash_twist (aes256_cipher (word 0) rk)) 0`;
       `h1 = h_power (ghash_twist (aes256_cipher (word 0) rk)) 1`;
       `h2 = h_power (ghash_twist (aes256_cipher (word 0) rk)) 2`;
       `h3 = h_power (ghash_twist (aes256_cipher (word 0) rk)) 3`] THEN
     REWRITE_TAC[GSYM WORD_SUBWORD_XOR] THEN
     (* The normalization folded the packing
        word_join (word_subword ks (0,64)) (word_subword ks (64,64)) of the
        reduction into byteswap128 ks, which RECONSTRUCT_POLYVAL_REDUCE_G2
        does not match: expand byteswap128 again (it occurs only there,
        bsofar being a variable). *)
     REWRITE_TAC[byteswap128] THEN
     REWRITE_TAC[RECONSTRUCT_POLYVAL_REDUCE_G2] THEN
     (* The goal is now polyval_reduce_g2 P1 P2 P3 = ghash_polyval_acc gt
        sofar [cb0; ..; cb3], where the accumulator lanes of the code read
        halves of bsofar = byteswap128 sofar in swapped positions.  The
        half-swaps of the ext and of the Karatsuba packing cancel, so the
        seed is sofar: expanding bsofar and rewriting with
        WORD_SUBWORD_BYTESWAP128 gives the halves of sofar in their own
        positions, GSYM WORD_SUBWORD_XOR folds the XOR of the halves of sofar
        and cb0 into the halves of word_xor sofar cb0, and CMID_LOHI folds
        the middle term to karatsuba_mid (word_xor sofar cb0), the A-lane
        form of CORE_REDUCE_GHASH with A := sofar.  Then expand h0..h3 and
        go through CORE_REDUCE_GHASH's operand order with EQ_TRANS: each
        argument of polyval_reduce_g2 is an XOR reordering of the same pmul
        and karatsuba_mid atoms (WORD_BITWISE_RULE). *)
     EXPAND_TAC "bsofar" THEN
     REWRITE_TAC[WORD_SUBWORD_BYTESWAP128] THEN
     REWRITE_TAC[GSYM WORD_SUBWORD_XOR] THEN
     (* Fold both XOR orders of the middle lanes to karatsuba_mid: the
        accumulator lane is low-first (CMID_LOHI), block middle lanes are
        high-first (CMID_HILO). *)
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
      [(* Both sides are polyval_reduce_g2 P1 P2 P3 with the arguments
          XOR-reordered: peel the curried application with exactly two
          MK_COMB_TAC (P3, then P2) and AP_TERM_TAC (P1); each argument is a
          reordering of the same pmul and karatsuba_mid atoms
          (WORD_BITWISE_RULE). *)
       MK_COMB_TAC THENL
        [MK_COMB_TAC THENL
          [AP_TERM_TAC THEN CONV_TAC WORD_BITWISE_RULE;
           CONV_TAC WORD_BITWISE_RULE];
         CONV_TAC WORD_BITWISE_RULE];
       (* the right-hand side is that of CORE_REDUCE_GHASH (A := sofar) *)
       MATCH_ACCEPT_TAC CORE_REDUCE_GHASH]) (asl,w);;
let close_goal7_fill = close_goal7_c collapse_q30_g0 true;;
let close_goal7_steady = close_goal7_c collapse_q30_gi false;;
let close_goal7_iter1 = close_goal7_c collapse_q30_g0 false;;

let close_all_c cg7 cg8 cg10 : tactic =
  fun (asl,w) ->
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
          (* the carried key powers Q2 and Q13: the final value is a reload
             from the table, resolved with the unfolded htable_mem_4 facts *)
          (ASM_REWRITE_TAC[] THEN REFL_TAC);
          ASM_REWRITE_TAC[] ])) (asl,w);;
let close_all_body = close_all_c close_goal7_steady close_goal8_b1 close_goal10_b1;;
let close_all_drain = close_all_c close_goal7_steady close_goal8_b2 close_goal10_b2;;
let close_all_iter1 = close_all_c close_goal7_iter1 close_goal8_b1 close_goal10_b1;;

(* ------------------------------------------------------------------------- *)
(* The fill: FILL_TO_CBZ, pc + 0xbc -> pc + 0x55c, establishing swp_inv 1    *)
(* just before the cbz that separates loop_count = 2 from loop_count >= 3.   *)
(* The fill completes group 0 (stored and hashed) and starts group 1, so it  *)
(* ends at index i = 1: X13 = word_zx (word (c + 8)), X2 = out_p + 64,       *)
(* X0 = in_p + 128, Q29 = swpgrp gt tag0 1.  Its 296 instructions are        *)
(* simulated once; FILLLEG (cbz not taken, loop_count >= 3, -> pc + 0x560)   *)
(* and LC2_PARTA (cbz taken, loop_count = 2, -> pc + 0x8a8) add one          *)
(* instruction each.  No ext precedes the GHASH of group 0: the reduction    *)
(* reads Q30 = byteswap128 tag0 directly (close_goal7_i0_c, A := tag0).      *)
(* ------------------------------------------------------------------------- *)

(* The fill goal, from pc + 0xbc to swp_inv 1 at pc + 0x560 (FILLLEG;
   FILL_TO_CBZ and the other legs reuse its precondition and frame).  The
   precondition includes the nonoverlapping facts of tag_p and ivec_p with
   the code, the input, the key table and the stack slots, and with each
   other, as body_goal does: without the stack ones the tag_p and ivec_p
   reads could not be carried across the stack stores (the first is step
   12, stp x11,x22,[sp,#160] at 0xe8) to the final state s296. *)
let fill_goal = mk_imp
 (`([EL 0 rk; EL 1 rk; EL 2 rk; EL 3 rk; EL 4 rk; EL 5 rk; EL 6 rk; EL 7 rk; EL 8 rk; EL 9 rk;
     EL 10 rk; EL 11 rk; EL 12 rk; EL 13 rk; EL 14 rk]:(int128)list = rk) /\
   len_bits DIV 128 = nblocks /\ nblocks DIV 4 = loop_count /\ nblocks MOD 4 = loop_remain /\
   3 <= loop_count /\ 16 * nblocks < 2 EXP 64 /\ aligned 16 (stackpointer:int64) /\
   nonoverlapping (out_p:int64,16 * nblocks) (word pc:int64,3860) /\
   (in_p:int64 = out_p \/
    nonoverlapping (in_p:int64,16 * nblocks) (out_p:int64,16 * nblocks)) /\
   nonoverlapping (out_p:int64,16 * nblocks) (htable_p:int64,96) /\
   nonoverlapping (out_p:int64,16 * nblocks) (tag_p:int64,16) /\
   nonoverlapping (out_p:int64,16 * nblocks) (ivec_p:int64,16) /\
   nonoverlapping (out_p:int64,16*nblocks) (word_add stackpointer (word 160):int64,64) /\
   nonoverlapping (tag_p:int64,16) (word pc:int64,3860) /\
   nonoverlapping (in_p:int64,16*nblocks) (tag_p:int64,16) /\
   nonoverlapping (tag_p:int64,16) (htable_p:int64,96) /\
   nonoverlapping (tag_p:int64,16) (word_add stackpointer (word 160):int64,64) /\
   nonoverlapping (ivec_p:int64,16) (word pc:int64,3860) /\
   nonoverlapping (in_p:int64,16*nblocks) (ivec_p:int64,16) /\
   nonoverlapping (ivec_p:int64,16) (htable_p:int64,96) /\
   nonoverlapping (ivec_p:int64,16) (word_add stackpointer (word 160):int64,64) /\
   nonoverlapping (tag_p:int64,16) (ivec_p:int64,16) /\
   nonoverlapping (word_add stackpointer (word 160):int64,64) (word pc:int64,3860) /\
   nonoverlapping (in_p:int64,16*nblocks) (word_add stackpointer (word 160):int64,64) /\
   nonoverlapping (word_add stackpointer (word 160):int64,64) (htable_p:int64,96) /\
   nonoverlapping (word_add stackpointer (word 160):int64,64) (out_p:int64,16*nblocks)`,
  list_mk_icomb "ensures" [`arm`;
    mk_abs(`s:armstate`, list_mk_conj
      [`aligned_bytes_loaded s (word pc) aes256_gcm_enc_tmc`;
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

(* The input split for the fill: blocks 0..7, groups 0 and 1, both of which
   the fill loads. *)
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

(* The fill setup: enter at pc + 0xbc, introduce the ghost lanes,
   ENSURES_INIT_TAC, unfold htable_mem_4 and split blocks 0..7.  Unlike
   setup_tac it abbreviates no initial reads as init_k: that would leave
   opaque init_k variables in the tag_p, ivec_p and rk14 conjuncts and in
   the round keys of the aese towers, where the closers of the AES partials,
   which expect word_reversefields 8 (EL k rk), would not match. *)
let fill_setup_tac =
  INTRO_HYPS_TAC THEN REWRITE_TAC[fst AES256_GCM_ENC_EXEC] THEN
  MAP_EVERY (fun rn -> GHOST_INTRO_TAC (mk_var("ghost_"^rn,`:int64`)) (parse_term("read "^rn))) ghost_lanes256 THEN
  ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV BETA_CONV)) THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_4]) THEN REWRITE_TAC[htable_mem_4] THEN
  FILL_INPUT_SPLIT_TAC THEN INPUT_LEG_TAC [];;

(* The stack-store merge sites of the fill, as (step, sp offset) with step =
   (address - 0xbc)/4 + 1: the group-0 counter blocks at steps 12, 24, 25
   and 26, the group-0 inputs XOR the last round key at 30, 60, 66 and 114,
   and the group-1 stores at 136, 179, 185, 196 (counter blocks) and 205,
   258, 266 (inputs).  Without a merge at a store step, the 128-bit reload
   of the slot would stay an unresolved stack read and the AES tower or
   the block completion built on it would not fold.  The fill is
   straight-line code of 296 instructions, 0xbc..0x558 (the last is the
   sub x1,x1,#2); the cbz at 0x55c is left to FILLLEG and LC2_PARTA. *)
let fill_merges_guess = [(12,160);(24,192);(25,208);(26,176);
                         (30,192);(60,160);(66,176);
                         (114,208);(136,160);(179,192);(185,208);(196,176);(205,192);(258,160);(266,176)];;
let NSTEP_FILL = 296;;
(* The fill stepper: steps 1..296 with gkeepF over REDSETX256, the
   normalization after each step, and MERGE_CTR128_TAC (tried) at the
   fill_merges_guess sites. *)
let fill_step_prefix =
  fill_setup_tac THEN
  (fun (asl,w) ->
     (MAP_EVERY (fun k ->
        gkeepF REDSETX256 AES256_GCM_ENC_EXEC ("s"^string_of_int k) THEN
        (* the body's normalization after every step: a sparser schedule
           would lose the tag_p and ivec_p reads that the postcondition
           needs at s296 *)
        RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV THENC
                                 ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV THENC IN_P_ADDR_FOLD_CONV)) THEN
        (if List.mem_assoc k fill_merges_guess then TRY(MERGE_CTR128_TAC (List.assoc k fill_merges_guess) ("s"^string_of_int k))
         else ALL_TAC))
       (1--NSTEP_FILL)) (asl,w)) THEN
  RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV THENC
                           ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV THENC
                           IN_P_ADDR_FOLD_CONV));;

(* fill_close_all_256: the per-conjunct closer for the fill's endpoint
   swp_inv 1.  The index is the literal 1, so the counter arguments
   4*1+c+K reduce to c+4+K: counters and AES partials close by their
   definitions and mk_cbv, the GHASH conjunct by close_goal7_i0_c
   (A := tag0).  unabbrev_init expands any init_k variables (fill_setup_tac
   introduces none). *)
let unabbrev_init : tactic =
  fun (asl,w) ->
    let ivars = setify(filter (fun v -> try String.length(fst(dest_var v))>=5 && String.sub (fst(dest_var v)) 0 5 = "init_" with _->false)
                              (frees w)) in
    (MAP_EVERY (fun v -> TRY(EXPAND_TAC (fst(dest_var v)))) ivars) (asl,w);;
let fill_close_all_256_c cg10 cg7 : tactic =
  fun (asl,w) ->
    let has_mc t = try can(find_term(fun x->match x with Const("MAYCHANGE",_)->true|_->false)) t with _->false in
    if has_mc w then cg10 (asl,w)
    else if has "aligned_bytes_loaded" w then ASM_REWRITE_TAC[] (asl,w)
    else if is_forall w then
      (REWRITE_TAC[ARITH_RULE `4 * 1 = 4`] THEN close_goal9_i0) (asl,w)
    (* The GHASH conjunct goes straight to close_goal7, which abbreviates the
       large terms first, so that the general closers below never try
       WORD_RULE or WORD_BLAST on the GHASH tower. *)
    else if is_eq w && (has "nist_ghash" (rhs w) || has "swpgrp" (rhs w)) then cg7 (asl,w)
    else
      (unabbrev_init THEN REWRITE_TAC[ZXNEST4; ZX_COUNTER_UD; GSYM WORD_ADD] THEN
       FIRST (map MUST
        [ (* pointers in_p/out_p (normally already closed) *)
          close_ptr;
          (* the tag_p and ivec_p reads: the s296 read facts are assumptions
             (gkeepF keeps them), so ASM_REWRITE_TAC closes them; no REFL_TAC
             after it, since the goal is then already closed *)
          (FIRST_ASSUM ACCEPT_TAC); ASM_REWRITE_TAC[];
          (* X13: word_zx (word (4*1+c+4)) *)
          (REWRITE_TAC[ZXNEST4; ZX_COUNTER_UD] THEN AP_TERM_TAC THEN REWRITE_TAC[GSYM WORD_ADD] THEN AP_TERM_TAC THEN ARITH_TAC);
          (* the AES partials Q3 = aes11c (c+4), Q4 = aes7c (c+6),
             Q8 = aes1c (c+5) and Q31 = aes6c (c+7): reduce the index,
             unfold the definition, peel down to the counter block and
             accept mk_cbv, whose left-hand side is the simulated form *)
          (REWRITE_TAC[ARITH_RULE `4 * 1 + c = c + 4`; aes11c] THEN
           REPEAT(AP_TERM_TAC ORELSE AP_THM_TAC) THEN ACCEPT_TAC(mk_cbv `(c:num) + 4`));
          (REWRITE_TAC[ARITH_RULE `(c + 4) + 2 = c + 6`; ARITH_RULE `4 * 1 + c + 2 = c + 6`; aes7c] THEN
           REPEAT(AP_TERM_TAC ORELSE AP_THM_TAC) THEN ACCEPT_TAC(mk_cbv `(c:num) + 6`));
          (REWRITE_TAC[ARITH_RULE `(c + 4) + 1 = c + 5`; ARITH_RULE `4 * 1 + c + 1 = c + 5`; aes1c] THEN
           REPEAT(AP_TERM_TAC ORELSE AP_THM_TAC) THEN ACCEPT_TAC(mk_cbv `(c:num) + 5`));
          (REWRITE_TAC[ARITH_RULE `(c + 4) + 3 = c + 7`; ARITH_RULE `4 * 1 + c + 3 = c + 7`; aes6c] THEN
           REPEAT(AP_TERM_TAC ORELSE AP_THM_TAC) THEN ACCEPT_TAC(mk_cbv `(c:num) + 7`));
          (* X1: word_sub (word loop_count) (word 2) =
             word (loop_count-(1+1)) *)
          (REWRITE_TAC[ARITH_RULE `(1:num)+1=2`] THEN
           SUBGOAL_THEN `2 <= loop_count` ASSUME_TAC THENL
            [MAP_EVERY (fun t -> TRY(UNDISCH_TAC t)) [`3 <= loop_count`; `2 <= loop_count`] THEN ARITH_TAC;
             ALL_TAC] THEN
           ASM_SIMP_TAC[WORD_SUB; GSYM VAL_WORD_1] THEN AP_TERM_TAC THEN
           MAP_EVERY (fun t -> TRY(UNDISCH_TAC t)) [`3 <= loop_count`; `2 <= loop_count`] THEN ARITH_TAC);
          (* the stack slots sp+160, sp+176, sp+192: blocks 4, 5, 6 XOR the
             last round key, a join of the XORed lanes (JOIN_XOR_LANES) *)
          (REWRITE_TAC[JOIN_XOR_LANES] THEN (REFL_TAC ORELSE CONV_TAC WORD_BLAST));
          (* X26/X24, the halves of block 7 XOR the last round key: push the
             subword through the XOR *)
          (REWRITE_TAC[WORD_SUBWORD_XOR] THEN (REFL_TAC ORELSE CONV_TAC WORD_BLAST));
          (* the GHASH conjunct, swpgrp gt tag0 1 (normally routed to
             close_goal7 by the dispatch above) *)
          cg7;
          (* the key powers Q2 and Q13 (table reloads) *)
          (ASM_REWRITE_TAC[] THEN REFL_TAC);
          ASM_REWRITE_TAC[]; CONV_TAC WORD_BLAST; CONV_TAC WORD_RULE ])) (asl,w);;
let fill_close_all_256 = fill_close_all_256_c close_goal10_b2 close_goal7_fill;;
(* FILL_TO_CBZ: the shared 296-instruction fill, pc + 0xbc -> pc + 0x55c,
   under 2 <= loop_count (the precondition of fill_goal with 3 <= loop_count
   weakened), ending at swp_inv 1 before the cbz.  The output forall closes
   by close_goal9_i0. *)
let fill_frame = last(snd(strip_comb(snd(dest_imp fill_goal))));;
let fill_pre_state = el 1 (snd(strip_comb(snd(dest_imp fill_goal))));;
let fill_cbz_goal = mk_imp
 (list_mk_conj (map (fun c -> if c = `3 <= loop_count` then `2 <= loop_count` else c) (conjuncts (lhand fill_goal))),
  list_mk_icomb "ensures" [`arm`; fill_pre_state; leg_state swp_inv `0x55c` `1`; fill_frame]);;
let FILL_TO_CBZ = GEN_ALL(prove(fill_cbz_goal,
  fill_step_prefix THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN fill_close_all_256));;

(* One-instruction hops out of a full swp_inv state.  swp_inv_at gives the
   invariant body for ENSURES_SEQUENCE_TAC and hop_init opens the state;
   after the step every conjunct is an unchanged read (ASM_REWRITE_TAC) or
   the branch PC, resolved from the val fact assumed before the step. *)
let REFOLD_ABI = REWRITE_TAC[GSYM MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI];;
let swp_inv_at idx = rhs(concl((BETA_CONV THENC REWRITE_CONV[ADD_CLAUSES]) (mk_comb(swp_inv,idx))));;
let hop_init : tactic =
  ENSURES_INIT_TAC "s0" THEN RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_4]) THEN REWRITE_TAC[htable_mem_4];;
let HOP_CLOSE : tactic =
  REPEAT CONJ_TAC THEN
  (FIRST_ASSUM ACCEPT_TAC ORELSE (ASM_REWRITE_TAC[] THEN NO_TAC) ORELSE
   (ASM_REWRITE_TAC[COND_CLAUSES; VAL_WORD_0] THEN CONV_TAC WORD_RULE));;

(* FILLLEG: pc + 0xbc -> pc + 0x560 for loop_count >= 3, FILL_TO_CBZ then
   the cbz at 0x55c not taken (X1 = word (loop_count - 2), nonzero). *)
let FILLLEG = GEN_ALL(prove(fill_goal,
  INTRO_HYPS_TAC THEN REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
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

(* LC2_PARTA: pc + 0xbc -> pc + 0x8a8 for loop_count = 2, FILL_TO_CBZ then
   the cbz at 0x55c taken (X1 = word 0).  The waypoint is swp_inv at the
   literal index 1 (loop_count - 1 for loop_count = 2); LEG_LC2 converts the
   index before applying DRAINLEG_8A8. *)
let lc2a_precond =
  list_mk_conj ((filter (fun c -> c <> `3 <= loop_count`) (conjuncts (lhand fill_goal))) @ [`loop_count = 2`]);;
let lc2_waypoint = leg_state swp_inv `0x8a8` `1`;;
let lc2a_goal = mk_imp(lc2a_precond, list_mk_icomb "ensures" [`arm`; fill_pre_state; lc2_waypoint; fill_frame]);;
let LC2_PARTA = prove(lc2a_goal,
  INTRO_HYPS_TAC THEN REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  ENSURES_SEQUENCE_TAC `pc + 0x55c` (swp_inv_at `1`) THEN CONJ_TAC THENL
   [REFOLD_ABI THEN MATCH_MP_TAC FILL_TO_CBZ THEN ASM_REWRITE_TAC[] THEN
    TRY(UNDISCH_TAC `loop_count = 2` THEN ARITH_TAC);
    hop_init THEN
    SUBGOAL_THEN `val (word (loop_count - (1 + 1)):int64) = 0` ASSUME_TAC THENL
     [UNDISCH_TAC `loop_count = 2` THEN DISCH_THEN SUBST1_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC[VAL_WORD_0];
      ALL_TAC] THEN
    ARM_STEPS_TAC AES256_GCM_ENC_EXEC [1] THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN HOP_CLOSE]);;

(* BODYLEG: swp_inv i at pc + 0x560 -> swp_inv (i+1) at pc + 0x8a4, one
   iteration of the loop body. *)
let BODYLEG = prove(body_goal, step_body_tac THEN REPEAT CONJ_TAC THEN close_all_body);;

(* ------------------------------------------------------------------------- *)
(* The drain: swp_inv (loop_count - 1) at pc + 0x8a4 -> the bridge state at  *)
(* pc + 0xdd0.  After the last iteration X1 = word 0, so the cbnz at 0x8a4   *)
(* is not taken; the drain 0x8a8..0xa8c (122 instructions, ending with the b *)
(* to 0xdd0 over the iter_1 block) completes the last group, blocks 4m..4m+3 *)
(* with m = loop_count - 1: it stores them and hashes them into Q29, and its *)
(* final ext leaves Q30 = byteswap128 (nist_ghash .. (4 * loop_count)).      *)
(* ------------------------------------------------------------------------- *)

(* Lemmas for the bridge: splitting list_of_seq, and swpgrp as nist_ghash. *)
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

(* The bridge state at pc + 0xdd0, after 4 * loop_count blocks: the
   postcondition of the drain and of LEG_LC0, LEG_LC1 and LEG_LC2, and the
   precondition of TAILLEG. *)
let drain_bridge = mk_abs(`s:armstate`, list_mk_conj
 [`aligned_bytes_loaded s (word pc) aes256_gcm_enc_tmc`;
  `read PC s = word (pc + 0xdd0)`;
  `read X0 s = word_add in_p (word (64 * loop_count))`;
  `read X2 s = word_add out_p (word (64 * loop_count))`;
  `read X3 s = tag_p`; `read X4 s = ivec_p`; `read X6 s = htable_p`; `read SP s = stackpointer`;
  `read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0`;
  `read (memory :> bytes128 ivec_p) s = word_reversefields 8 (ctr_block nonce c)`;
  `read X13 s = word_zx (word (4 * loop_count + c):int32):int64`;
  `read X15 s = word(len_bits DIV 8)`;
  (* X1 is not constrained: the drain path leaves X1 = word 0 but the
     iter_1 path (loop_count = 1) leaves X1 = word 1, and the tail never
     reads X1 (tail_inv uses X16), so both paths can reach this bridge. *)
  `read X16 s = word loop_remain`;
  (* the round keys, the reduction constant Q7 and the counter lanes
     X11/X12, which the tail loop uses: swp_inv carries them and the drain
     preserves them; tail_inv 0 needs them *)
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
  (* Q12 and Q14 are not carried: the drain leaves other values in them, and
     the tail reloads Q12, Q13 and Q14 from the table at 0xdd0..0xdd8;
     htable_mem_4 below supplies the values, so tail_inv's Q12 and Q14
     conjuncts come from the tail's own stepping. *)
  `read Q30 s = byteswap128 (nist_ghash (aes256_cipher (word 0) rk) tag0
                  (list_of_seq (nist_cipher_block aes256_cipher c nonce rk inblock) (4 * loop_count)))`;
  `htable_mem_4 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s`;
  `!j. 4 * loop_count <= j /\ j < nblocks ==> read (memory :> bytes128 (word_add in_p (word(16*j)))) s = inblock j`;
  `!j. j < 4 * loop_count ==> read (memory :> bytes128 (word_add out_p (word(16*j)))) s =
           word_xor (aes_ctr_block aes256_cipher c nonce rk j) (inblock j)`]);;

(* The drain goal (DRAINLEG): swp_inv (loop_count - 1) at pc + 0x8a4 ->
   drain_bridge at pc + 0xdd0, with the broad frame (the working registers
   including the AES partials, the out_p bytes and the stack slots). *)
let drain_goal = mk_imp
 (`([EL 0 rk; EL 1 rk; EL 2 rk; EL 3 rk; EL 4 rk; EL 5 rk; EL 6 rk; EL 7 rk;
     EL 8 rk; EL 9 rk; EL 10 rk; EL 11 rk; EL 12 rk; EL 13 rk; EL 14 rk]:(int128)list = rk) /\
   len_bits DIV 128 = nblocks /\ nblocks DIV 4 = loop_count /\ nblocks MOD 4 = loop_remain /\
   2 <= loop_count /\ 16 * nblocks < 2 EXP 64 /\ aligned 16 (stackpointer:int64) /\
   nonoverlapping (out_p:int64,16 * nblocks) (word pc:int64,3860) /\
   (in_p:int64 = out_p \/
    nonoverlapping (in_p:int64,16 * nblocks) (out_p:int64,16 * nblocks)) /\
   nonoverlapping (out_p:int64,16 * nblocks) (htable_p:int64,96) /\
   nonoverlapping (out_p:int64,16 * nblocks) (tag_p:int64,16) /\
   nonoverlapping (out_p:int64,16 * nblocks) (ivec_p:int64,16) /\
   nonoverlapping (out_p:int64,16*nblocks) (word_add stackpointer (word 160):int64,64) /\
   nonoverlapping (tag_p:int64,16) (word pc:int64,3860) /\
   nonoverlapping (in_p:int64,16*nblocks) (tag_p:int64,16) /\
   nonoverlapping (tag_p:int64,16) (htable_p:int64,96) /\
   nonoverlapping (tag_p:int64,16) (word_add stackpointer (word 160):int64,64) /\
   nonoverlapping (ivec_p:int64,16) (word pc:int64,3860) /\
   nonoverlapping (in_p:int64,16*nblocks) (ivec_p:int64,16) /\
   nonoverlapping (ivec_p:int64,16) (htable_p:int64,96) /\
   nonoverlapping (ivec_p:int64,16) (word_add stackpointer (word 160):int64,64) /\
   nonoverlapping (tag_p:int64,16) (ivec_p:int64,16) /\
   nonoverlapping (word_add stackpointer (word 160):int64,64) (word pc:int64,3860) /\
   nonoverlapping (in_p:int64,16*nblocks) (word_add stackpointer (word 160):int64,64) /\
   nonoverlapping (word_add stackpointer (word 160):int64,64) (htable_p:int64,96)`,
  list_mk_icomb "ensures" [`arm`;
    leg_state swp_inv `0x8a4` `loop_count - 1` ;
    drain_bridge ;
    `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
     MAYCHANGE [X19; X20; X21; X22; X23; X24; X25; X26; X27; X28; X29; X30] ,,
     MAYCHANGE [Q0;Q1;Q2;Q3;Q4;Q5;Q6;Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15; Q29; Q30; Q31] ,,
     MAYCHANGE [memory :> bytes(out_p:int64, 16 * nblocks)] ,,
     MAYCHANGE [memory :> bytes(word_add stackpointer (word 160):int64, 64)] ,, MAYCHANGE [events]`]);;

(* drain_close_q30: the GHASH conjunct of the bridge,
   <reduction computed by the code, half-swapped> =
   byteswap128 (nist_ghash .. (4*(m+1))) with m = loop_count - 1.  It has
   one byteswap128 more than the goal of close_goal7, which is therefore not
   reused: (1) present the index as 4*(m+1) and use GSYM
   SWPGRP_IS_NIST_GHASH to get byteswap128 (swpgrp gt tag0 (m+1) ..);
   (2) normalize the reduction as close_goal7 does, at index m; (3) strip
   byteswap128 from both sides (expand it and use the BITBLAST_RULE
   x = y ==> word_join (halves of x) = word_join (halves of y)); (4) finish
   with the EQ_TRANS tail of close_goal7 and CORE_REDUCE_GHASH
   (A := sofar). *)
let drain_close_q30_c collapse : tactic =
  fun (asl,w) ->
    (GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [ARITH_RULE `4 * m + 4 = 4 * (m + 1)`] THEN
     GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [GSYM SWPGRP_IS_NIST_GHASH] THEN
     (* close_goal7's normalization, at index m *)
     collapse THEN
     GEN_REWRITE_TAC (RAND_CONV o TOP_DEPTH_CONV) [ARITH_RULE `m + 1 = SUC m`] THEN
     GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [CONJUNCT2 swpgrp] THEN
     ABBREV_TAC `sofar = swpgrp (ghash_twist (aes256_cipher (word 0) rk)) tag0 m (nist_cipher_block aes256_cipher c nonce rk inblock)` THEN
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
      [`cipherblock_0 = nist_cipher_block aes256_cipher c nonce rk inblock (4 * m)`;
       `cipherblock_1 = nist_cipher_block aes256_cipher c nonce rk inblock (4 * m + 1)`;
       `cipherblock_2 = nist_cipher_block aes256_cipher c nonce rk inblock (4 * m + 2)`;
       `cipherblock_3 = nist_cipher_block aes256_cipher c nonce rk inblock (4 * m + 3)`;
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
     (* the goal is byteswap128 (polyval_reduce_g2 ..) =
        byteswap128 (ghash_polyval_acc ..): strip byteswap128 *)
     REWRITE_TAC [byteswap128; WORD_BLAST
       `word_subword((word_join:int128->int128->int256) h l) (64,128):int128 =
        word_join (word_subword h (0,64):int64) (word_subword l (64,64):int64)`] THEN
     MATCH_MP_TAC(BITBLAST_RULE
      `x:int128 = y
       ==> word_join (word_subword x (0,64):int64) (word_subword x (64,64):int64):int128 =
           word_join (word_subword y (0,64):int64) (word_subword y (64,64):int64):int128`) THEN
     (* close_goal7's EQ_TRANS tail, at index m *)
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

(* The per-conjunct closer of the drain: the GHASH conjunct (byteswap128 and
   nist_ghash on the right) goes to drain_close_q30; the register conjuncts
   carried unchanged (round keys, X20/X21, X11/X12, Q7) close by assumption
   before close_all_drain, so they never reach its expensive alternatives. *)
let drain_close_all_c dq30 closeall : tactic =
  fun (asl,w) ->
    if is_eq w && has "nist_ghash" (rhs w) && has "byteswap128" (rhs w) then dq30 (asl,w)
    else if is_eq w &&
            (has "word_reversefields" (rhs w) || has "karatsuba_mid" (rhs w) ||
             (is_comb(rhs w) && fst(dest_const(fst(strip_comb(rhs w)))) = "word") ||
             has "h_power" (rhs w))
    then (FIRST_ASSUM ACCEPT_TAC ORELSE ASM_REWRITE_TAC[] ORELSE closeall) (asl,w)
    else closeall (asl,w);;
let drain_close_all = drain_close_all_c drain_close_q30 close_all_drain;;

(* DRAINLEG_8A8: the drain proper, pc + 0x8a8 -> drain_bridge, from
   swp_inv (loop_count - 1) with X1 = word 0; drain_goal_8a8 is drain_goal
   with the entry PC 0x8a8.  It is simulated once and shared: the loop exit
   (DRAINLEG, the cbnz at 0x8a4 not taken) and the loop_count = 2 path
   (LEG_LC2, the cbz at 0x55c taken) both land here. *)
let drain_goal_8a8 =
  let pre8a8 = leg_state swp_inv `0x8a8` `loop_count - 1` in
  mk_imp(lhand drain_goal,
    list_mk_icomb "ensures" [`arm`; pre8a8; drain_bridge;
      last(snd(strip_comb(snd(dest_imp drain_goal))))]);;

(* The setup at 0x8a8: m = loop_count - 1, X1 = word 0, and the input split
   of the last group (blocks 4m..4m+3). *)
let drain_setup_tac_8a8 =
  INTRO_HYPS_TAC THEN REWRITE_TAC[fst AES256_GCM_ENC_EXEC] THEN
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
       can (find_term (fun t -> is_const t && fst(dest_const t) = "bytes128")) (lhs c)))) THEN
  INPUT_LEG_TAC [];;
(* The only stack store of the drain is step 24 (stp x24,x26,[sp,#208],
   block 4m+3 XOR the last round key); step 122, at 0xa8c, is the b to 0xdd0
   over the iter_1 block. *)
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
  ENSURES_FINAL_STATE_TAC THEN INPUT_POSTS_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN drain_close_all));;

(* DRAINLEG: entry at the cbnz at 0x8a4 with swp_inv (loop_count - 1) and
   X1 = word 0, so that it is not taken, then DRAINLEG_8A8.  GEN_ALL so that
   MATCH_MP_TAC in the composition leaves key_p existential. *)
let DRAINLEG = GEN_ALL(prove(drain_goal,
  INTRO_HYPS_TAC THEN REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  ENSURES_SEQUENCE_TAC `pc + 0x8a8` (swp_inv_at `loop_count - 1`) THEN CONJ_TAC THENL
   [hop_init THEN
    SUBGOAL_THEN `loop_count - ((loop_count - 1) + 1) = 0`
      (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th]) THENL
     [UNDISCH_TAC `2 <= loop_count` THEN ARITH_TAC; ALL_TAC] THEN
    ARM_STEPS_TAC AES256_GCM_ENC_EXEC [1] THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN HOP_CLOSE;
    REFOLD_ABI THEN MATCH_MP_TAC DRAINLEG_8A8 THEN ASM_REWRITE_TAC[]]));;

(* ------------------------------------------------------------------------- *)
(* The tail: TAILLEG, drain_bridge at pc + 0xdd0 -> tail_post at pc + 0xee4  *)
(* (the tag, the counter and all output blocks stored, before the            *)
(* restores).  After the three key-table reloads, the cbz x16 at 0xddc       *)
(* skips or enters the loop over the loop_remain remaining blocks            *)
(* (pc + 0xde0 .. pc + 0xecc); X0 and the tag and counter stores follow at   *)
(* 0xed0..0xee0.                                                             *)
(* ------------------------------------------------------------------------- *)

(* The closer of the tail's final state, after ENSURES_FINAL_STATE_TAC, the
   gval abbreviation, the ivec split, the normalization and ASM_REWRITE_TAC:
   the MAYCHANGE frame conjunct goes to close_goal10_b2 (it must not reach
   WORD_BLAST); the output forall holds by assumption, since the tag and
   counter stores do not write out_p; the tag and ivec conjuncts close by
   the byteswap128 and ctr_block word identities. *)
let tail_final_close : tactic =
  REPEAT CONJ_TAC THEN
  FIRST
   [close_goal10_b2;
    FIRST_ASSUM MATCH_ACCEPT_TAC;
    (REWRITE_TAC[byteswap128; ctr_block] THEN
     REWRITE_TAC[ADD_ASSOC; ZX_COUNTER_UD; CTR_ZX_NORM] THEN
     CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN CONV_TAC WORD_BLAST)];;

(* The tail loop invariant at pc + 0xde0: the bridge state advanced by i
   blocks, with the reloaded table entries Q12 (byteswap128 of h_power 0) and
   Q14 (the middle terms of h_power 0 and 1) for the single-block GHASH. *)
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
                   (list_of_seq (nist_cipher_block aes256_cipher c nonce rk inblock) (4 * loop_count + i))) /\
    htable_mem_4 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s /\
    read Q12 s = byteswap128 (h_power (ghash_twist (aes256_cipher (word 0) rk)) 0) /\
    read Q14 s = word_join
       (karatsuba_mid (h_power (ghash_twist (aes256_cipher (word 0) rk)) 1))
       (karatsuba_mid (h_power (ghash_twist (aes256_cipher (word 0) rk)) 0)) /\
    (!j. 4 * loop_count + i <= j /\ j < nblocks ==> read (memory :> bytes128 (word_add in_p (word(16*j)))) s = inblock j) /\
    (!j. j < 4 * loop_count + i ==> read (memory :> bytes128 (word_add out_p (word(16*j)))) s =
             word_xor (aes_ctr_block aes256_cipher c nonce rk j) (inblock j))`;;

(* The tail postcondition at pc + 0xee4: the tag and the counter stored and
   all nblocks output blocks written. *)
let tail_post = mk_abs(`s:armstate`, list_mk_conj
 [`aligned_bytes_loaded s (word pc) aes256_gcm_enc_tmc`;
  `read PC s = word (pc + 0xee4)`;
  `read (memory :> bytes128 tag_p) s = word_reversefields 8
     (nist_ghash (aes256_cipher (word 0) rk) tag0
        (list_of_seq (nist_cipher_block aes256_cipher c nonce rk inblock) nblocks))`;
  `read (memory :> bytes128 ivec_p) s = word_reversefields 8 (ctr_block nonce (nblocks + c))`;
  `read X0 s = word (len_bits DIV 8)`;
  `!j. j < nblocks ==> read (memory :> bytes128 (word_add out_p (word(16*j)))) s =
           word_xor (aes_ctr_block aes256_cipher c nonce rk j) (inblock j)`]);;

(* The tail goal: drain_bridge at pc + 0xdd0 -> tail_post at pc + 0xee4,
   for any loop_remain < 4, with the broad frame plus tag_p and ivec_p. *)
let tail_goal = mk_imp
 (`([EL 0 rk; EL 1 rk; EL 2 rk; EL 3 rk; EL 4 rk; EL 5 rk; EL 6 rk; EL 7 rk;
     EL 8 rk; EL 9 rk; EL 10 rk; EL 11 rk; EL 12 rk; EL 13 rk; EL 14 rk]:(int128)list = rk) /\
   len_bits DIV 128 = nblocks /\ nblocks DIV 4 = loop_count /\ nblocks MOD 4 = loop_remain /\
   16 * nblocks < 2 EXP 64 /\ aligned 16 (stackpointer:int64) /\
   nonoverlapping (out_p:int64,16 * nblocks) (word pc:int64,3860) /\
   (in_p:int64 = out_p \/
    nonoverlapping (in_p:int64,16 * nblocks) (out_p:int64,16 * nblocks)) /\
   nonoverlapping (out_p:int64,16 * nblocks) (htable_p:int64,96) /\
   nonoverlapping (out_p:int64,16 * nblocks) (tag_p:int64,16) /\
   nonoverlapping (out_p:int64,16 * nblocks) (ivec_p:int64,16) /\
   nonoverlapping (tag_p:int64,16) (word pc:int64,3860) /\
   nonoverlapping (in_p:int64,16*nblocks) (tag_p:int64,16) /\
   nonoverlapping (tag_p:int64,16) (htable_p:int64,96) /\
   nonoverlapping (ivec_p:int64,16) (word pc:int64,3860) /\
   nonoverlapping (in_p:int64,16*nblocks) (ivec_p:int64,16) /\
   nonoverlapping (ivec_p:int64,16) (htable_p:int64,96) /\
   nonoverlapping (tag_p:int64,16) (ivec_p:int64,16) /\
   nonoverlapping (out_p:int64,16*nblocks) (word_add stackpointer (word 160):int64,64) /\
   nonoverlapping (tag_p:int64,16) (word_add stackpointer (word 160):int64,64) /\
   nonoverlapping (ivec_p:int64,16) (word_add stackpointer (word 160):int64,64) /\
   nonoverlapping (word_add stackpointer (word 160):int64,64) (word pc:int64,3860) /\
   nonoverlapping (in_p:int64,16*nblocks) (word_add stackpointer (word 160):int64,64) /\
   nonoverlapping (word_add stackpointer (word 160):int64,64) (htable_p:int64,96) /\
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

(* tail_ghash_close: the closer of the tail loop body (tail_inv i ->
   tail_inv (i+1)): the reconstruction of the output block, the remaining
   word equalities (tail_wordeq_close), and the one-block GHASH step of Q30:
   strip byteswap128, show that the reduction computed by the code is
   polyval_reduce_prop3 of the product of word_xor sofar block and
   h_power 0 (PMUL_KARATSUBA_JOIN_ALT, POLYVAL_REDUCE_G2), a polyval_dot,
   and fold that into nist_ghash over one more block. *)
(* tail_wordeq_close: the register and counter word equalities.  X16 is
   word_sub (word (loop_remain - i)) (word 1), which WORD_SUB turns into a
   conditional on i <= loop_remain: resolve both conditionals to T with
   i < loop_remain first, since WORD_RULE alone does not handle them. *)
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
  REWRITE_TAC[aes_ctr_block; GSYM ADD_ASSOC] THEN
  CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
  ASM_SIMP_TAC[WORD_SUB; LT_IMP_LE; ARITH_RULE `i < l ==> i + 1 <= l`] THEN
  (* Close the htable_mem_4 conjunct about s59 before DISCARD_STATE_TAC
     removes the s59 reads: unfold it in the goal and match the six reads
     carried through the stepping (the body subgoal unfolded htable_mem_4
     in the s0 assumption). *)
  TRY(ASM_REWRITE_TAC[htable_mem_4]) THEN
  DISCARD_STATE_TAC "s59" THEN
  REWRITE_TAC[ADD_ASSOC; ARITH] THEN
  REWRITE_TAC[AES_CTR_BLOCK_RECONSTRUCT] THEN
  REWRITE_TAC[GSYM cipher_block] THEN
  REWRITE_TAC[CIPHER_BLOCK_NIST] THEN
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
               (list_of_seq (nist_cipher_block aes256_cipher c nonce rk inblock) (4 * loop_count + i)))`;
    `cipherblock = nist_cipher_block aes256_cipher c nonce rk inblock (4 * loop_count + i)`;
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

(* The closer of the body subgoal of the tail loop. *)
let tail_g3_close : tactic = tail_ghash_close;;

let tail_stepconv n =
  ARM_STEPS_TAC AES256_GCM_ENC_EXEC [n] THEN RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV));;

(* tail_tac: drain_bridge at pc + 0xdd0 -> tail_post at pc + 0xee4.  Three
   table reloads (ldr q12/q13/q14), then the cbz x16 at 0xddc guards the
   loop. *)
let tail_tac =
  REPEAT GEN_TAC THEN INTRO_HYPS_TAC THEN REWRITE_TAC[fst AES256_GCM_ENC_EXEC] THEN
  (* No ENSURES_INIT_TAC here: the loop_remain > 0 branch needs the ensures
     goal for ENSURES_WHILE_UP_TAC.  Each branch does its own
     ENSURES_INIT_TAC and htable_mem_4 unfold (which resolves the
     q12/q13/q14 reloads). *)
  ASM_CASES_TAC `loop_remain = 0` THENL
   [(* loop_remain = 0: nblocks = 4 * loop_count; the cbz x16 is taken to
       0xed0, the tag and counter stores. *)
    POP_ASSUM SUBST_ALL_TAC THEN
    ENSURES_INIT_TAC "s0" THEN
    RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_4]) THEN
    SUBGOAL_THEN `nblocks = 4 * loop_count` SUBST_ALL_TAC THENL
     [MAP_EVERY(fun t -> TRY(UNDISCH_TAC t)) [`nblocks DIV 4 = loop_count`; `nblocks MOD 4 = 0`] THEN ARITH_TAC; ALL_TAC] THEN
    (* split the ivec read (the low 12 nonce bytes survive the 4-byte
       counter store) *)
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o CONV_RULE(READ_MEMORY_SPLIT_CONV 2) o
      check (fun th -> let c = concl th in is_eq c && free_in `ivec_p:int64` (lhs c) &&
        not(free_in `out_p:int64` (lhs c)) && not(free_in `htable_p:int64` (lhs c)) && not(free_in `tag_p:int64` (lhs c)))) THEN
    (* nine steps: the three reloads (s1..s3), the cbz at 0xddc taken (s4),
       and mov, rev64, str q30, rev, str w14 at 0xed0..0xee0 (s5..s9), ending
       at 0xee4 *)
    MAP_EVERY tail_stepconv (1--9) THEN
    ENSURES_FINAL_STATE_TAC THEN
    (* abbreviate the settled GHASH value as gval, so that WORD_BLAST sees
       a variable *)
    ABBREV_TAC `gval:int128 = nist_ghash (aes256_cipher (word 0) rk) tag0
                  (list_of_seq (nist_cipher_block aes256_cipher c nonce rk inblock) (4 * loop_count))` THEN
    CONV_TAC(ONCE_DEPTH_CONV(fun t ->
      if is_eq t && free_in `ivec_p:int64` (lhs t) && not(free_in `out_p:int64` (lhs t)) && not(free_in `tag_p:int64` (lhs t))
      then READ_MEMORY_SPLIT_CONV 2 t else failwith "")) THEN
    CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    REWRITE_TAC[ZX_COUNTER_UD; CTR_ZX_NORM] THEN ASM_REWRITE_TAC[] THEN
    (* the output forall (j < 4 * loop_count) is unchanged from the bridge (by
       assumption); the frame by close_goal10; tag and ivec by WORD_BLAST *)
    tail_final_close;

    (* loop_remain > 0: ENSURES_WHILE_UP over loop_remain from 0xde0 to
       0xecc.  Expand the ABI macro first, so that the C ,, C = C
       idempotence of ENSURES_WHILE_UP_TAC (MAYCHANGE_IDEMPOT_TAC,
       ASSIGNS_SEQ_ABSORB_CONV) can decompose the frame; with the macro
       folded ASSIGNS_SEQ_ABSORB_CONV fails. *)
    REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    ENSURES_WHILE_UP_TAC `loop_remain:num` `pc + 0xde0` `pc + 0xecc` tail_inv THEN
    REPEAT CONJ_TAC THENL
     [(* ~(loop_remain = 0) *) ASM_REWRITE_TAC[];
      (* The initialization: from drain_bridge, the three reloads and the cbz
         at 0xddc, not taken: resolve its condition on
         val (word loop_remain) = 0 with val (word loop_remain) = loop_remain
         (VAL_WORD_EQ, loop_remain < 4) and ~(loop_remain = 0), so that
         execution continues at 0xde0. *)
      ENSURES_INIT_TAC "s0" THEN RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_4]) THEN
      MAP_EVERY tail_stepconv (1--4) THEN
      ENSURES_FINAL_STATE_TAC THEN
      SUBGOAL_THEN `val(word loop_remain:int64) = loop_remain` ASSUME_TAC THENL
       [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
        MAP_EVERY (fun t -> TRY(UNDISCH_TAC t)) [`nblocks MOD 4 = loop_remain`; `16 * nblocks < 2 EXP 64`] THEN ARITH_TAC;
        ALL_TAC] THEN
      (* unfold htable_mem_4 in the goal too (the six reads are carried to
         s4 from the unfolded assumption) *)
      ASM_REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES; SUB_0; htable_mem_4];
      (* The body: tail_inv i -> tail_inv (i+1), 59 steps.  htable_mem_4 is
         unfolded in the s0 assumption, as in setup_tac, so that the six
         table reads are carried to s59 and the htable_mem_4 conjunct of
         tail_inv (i+1) closes by assumption. *)
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN ENSURES_INIT_TAC "s0" THEN
      RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_4]) THEN
      SUBGOAL_THEN `read (memory :> bytes128 (word_add in_p (word (64 * loop_count + 16 * i)))) s0 = inblock (4 * loop_count + i)`
      ASSUME_TAC THENL
       [REWRITE_TAC[ARITH_RULE `64 * a + 16 * b = 16 * (4 * a + b)`] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
      FIRST_X_ASSUM(STRIP_ASSUME_TAC o CONV_RULE SPLIT_INPUT_TAIL_CONV o
        check (fun th -> let c = concl th in is_eq c && free_in `in_p:int64` (lhs c) &&
          can (find_term (fun t -> is_const t && fst(dest_const t) = "bytes128")) (lhs c))) THEN
      INPUT_LEG_TAC [] THEN
      (* The slot sp+160 is stored twice: the counter block at step 5 and
         the input block XOR the last round key at step 14.  Merge after
         each store, and discard the facts about its first contents before
         the second. *)
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
      (* The back edge, the cbnz at 0xecc taken (X16 = word (loop_remain - i)
         with i < loop_remain): unfold htable_mem_4 in the assumption and in
         the goal before the step, so that the six reads carry through it,
         and resolve the condition with val (word loop_remain) = loop_remain
         and ~(loop_remain = i). *)
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
      ENSURES_INIT_TAC "s0" THEN RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_4]) THEN REWRITE_TAC[htable_mem_4] THEN
      ARM_STEPS_TAC AES256_GCM_ENC_EXEC [1] THEN ENSURES_FINAL_STATE_TAC THEN
      ASM_SIMP_TAC[WORD_SUB; LT_IMP_LE; VAL_EQ_0; WORD_SUB_EQ_0] THEN ASM_REWRITE_TAC[GSYM VAL_EQ] THEN
      SUBGOAL_THEN `val(word loop_remain:int64) = loop_remain` ASSUME_TAC THENL
       [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
        MAP_EVERY (fun t -> TRY(UNDISCH_TAC t)) [`nblocks MOD 4 = loop_remain`; `16 * nblocks < 2 EXP 64`] THEN ARITH_TAC;
        ALL_TAC] THEN
      ASM_SIMP_TAC[ARITH_RULE `i < loop_remain ==> ~(loop_remain = i)`];
      (* The exit: tail_inv loop_remain at 0xecc -> tail_post at 0xee4, six
         steps (the cbnz not taken, then the stores up to 0xee0);
         nblocks = 4 * loop_count + loop_remain. *)
      ENSURES_INIT_TAC "s0" THEN
      FIRST_X_ASSUM(STRIP_ASSUME_TAC o CONV_RULE(READ_MEMORY_SPLIT_CONV 2) o
        check (fun th -> let c = concl th in is_eq c && free_in `ivec_p:int64` (lhs c) &&
          not(free_in `out_p:int64` (lhs c)) && not(free_in `htable_p:int64` (lhs c)) && not(free_in `tag_p:int64` (lhs c)))) THEN
      MAP_EVERY tail_stepconv (1--6) THEN
      ENSURES_FINAL_STATE_TAC THEN
      SUBGOAL_THEN `nblocks = 4 * loop_count + loop_remain` SUBST_ALL_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
      (* abbreviate the settled GHASH value, over
         4 * loop_count + loop_remain = nblocks blocks, as gval *)
      ABBREV_TAC `gval:int128 = nist_ghash (aes256_cipher (word 0) rk) tag0
                    (list_of_seq (nist_cipher_block aes256_cipher c nonce rk inblock) (4 * loop_count + loop_remain))` THEN
      CONV_TAC(ONCE_DEPTH_CONV(fun t ->
        if is_eq t && free_in `ivec_p:int64` (lhs t) && not(free_in `out_p:int64` (lhs t)) && not(free_in `tag_p:int64` (lhs t))
        then READ_MEMORY_SPLIT_CONV 2 t else failwith "")) THEN
      CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
      REWRITE_TAC[ZX_COUNTER_UD] THEN ASM_REWRITE_TAC[] THEN
      tail_final_close]];;

let TAILLEG = GEN_ALL(prove(tail_goal, tail_tac));;

(* ------------------------------------------------------------------------- *)
(* loop_count = 1: ITER1_LEG, pc + 0xb0 -> drain_bridge at pc + 0xdd0.  The  *)
(* cbz at 0xb0 is not taken and the b.eq at 0xb8 is taken to the iter_1      *)
(* block 0xa90..0xdcc, 208 straight-line instructions that fall through to   *)
(* 0xdd0 (211 steps in all).                                                 *)
(* ------------------------------------------------------------------------- *)

(* The entry state at pc + 0xb0: fill_pre_state with the PC changed. *)
let iter1_entry = mk_abs(`s:armstate`,
  subst [`word (pc + 0xb0):int64`, `word (pc + 188):int64`] (snd(dest_abs fill_pre_state)));;

(* The precondition: fill_goal's with 3 <= loop_count dropped and
   loop_count = 1 added. *)
let iter1_precond =
  list_mk_conj ((filter (fun c -> c <> `3 <= loop_count`) (conjuncts (lhand fill_goal)))
                @ [`loop_count = 1`]);;
(* The frame: fill_goal's (the out_p bytes and the stack slots); iter_1
   writes the output blocks 0..3 and the stack slots. *)
let iter1_frame = last(snd(strip_comb(snd(dest_imp fill_goal))));;
let iter1_goal = mk_imp(iter1_precond,
  list_mk_icomb "ensures" [`arm`; iter1_entry; drain_bridge; iter1_frame]);;

(* The input reads of blocks 0..3. *)
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
  (* Split each block read into its two 64-bit halves, as INPUT_SPLIT_TAC256
     does, so that the scalar loads resolve to halves of inblock and the
     GHASH blocks fold to nist_cipher_block. *)
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o CONV_RULE SPLIT_INPUT_CONV o
     check (fun th -> let c = concl th in is_eq c && free_in `in_p:int64` (lhs c) &&
       can (find_term (fun t -> is_const t && fst(dest_const t) = "bytes128")) (lhs c))));;

let iter1_head =
  REWRITE_TAC[SND] THEN REPEAT GEN_TAC THEN INTRO_HYPS_TAC THEN
  REWRITE_TAC[fst AES256_GCM_ENC_EXEC] THEN
  MAP_EVERY (fun rn -> GHOST_INTRO_TAC (mk_var("ghost_"^rn,`:int64`)) (parse_term("read "^rn))) ghost_lanes256 THEN
  REWRITE_TAC[htable_mem_4] THEN
  ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV BETA_CONV)) THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_4]) THEN
  iter1_prime THEN INPUT_LEG_TAC [];;

(* The stack-store merge sites of ITER1_LEG, as (step, sp offset) with steps
   counted from 0xb0 (step k >= 4 is at 0xa90 + 4*(k-4)): each site is the
   step just before the 128-bit reload of the slot. *)
let iter1_merges_abs = [(19,208);(23,192);(26,160);(34,192);(54,160);(60,176);(66,208);(69,176)];;
let iter1_block_step lo hi =
  MAP_EVERY (fun k -> gkeepN REDSETX256 AES256_GCM_ENC_EXEC ("s"^string_of_int k) THEN
     RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV THENC
        ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV THENC IN_P_ADDR_FOLD_CONV)) THEN
     (if List.mem_assoc k iter1_merges_abs then MERGE_CTR128_TAC (List.assoc k iter1_merges_abs) ("s"^string_of_int k)
      else ALL_TAC)) (lo--hi);;

(* The normalization before the closers for loop_count = 1, only the
   reductions that are safe for every conjunct: 64*1 -> 64 (the pointers),
   4*1+c -> c+4 (X13), and refolding htable_mem_4.  The two uses of 4*1 (the
   GHASH index and the bound of the output forall) need different forms and
   are handled by their closers. *)
let ITER1_PRE_CLOSE : tactic =
  REWRITE_TAC[ARITH_RULE `64 * 1 = 64`; ARITH_RULE `4 * 1 + c = c + 4`] THEN
  REWRITE_TAC[GSYM htable_mem_4];;

(* The GHASH conjunct for loop_count = 1, proved as in drain_close_q30
   with m = 0: the bridge has the form byteswap128 (nist_ghash ..
   (4 * loop_count)), one byteswap128 more than the swpgrp goal of the
   fill.  Present 4*1 as 4*(0+1), then follow drain_close_q30 with m
   literally 0 and the seed sofar = swpgrp gt tag0 0 = tag0. *)
let close_q30_i0 : tactic =
  fun (asl,w) ->
    (GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [ARITH_RULE `4 * 1 = 4 * 0 + 4`] THEN
     GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [ARITH_RULE `4 * 0 + 4 = 4 * (0 + 1)`] THEN
     GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [GSYM SWPGRP_IS_NIST_GHASH] THEN
     collapse_q30_g0 THEN
     GEN_REWRITE_TAC (RAND_CONV o TOP_DEPTH_CONV) [ARITH_RULE `0 + 1 = SUC 0`] THEN
     GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [CONJUNCT2 swpgrp] THEN
     (* reduce the seed swpgrp gt tag0 0 to tag0 (CONJUNCT1 swpgrp), the
        accumulator lane of the code, then abbreviate sofar = tag0, as
        close_goal7_i0_c does *)
     GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [CONJUNCT1 swpgrp] THEN
     (* reduce the block indices 4*0+k on the right to k, as in the code's
        nist_cipher_block lanes *)
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
      [`cipherblock_0 = nist_cipher_block aes256_cipher c nonce rk inblock 0`;
       `cipherblock_1 = nist_cipher_block aes256_cipher c nonce rk inblock 1`;
       `cipherblock_2 = nist_cipher_block aes256_cipher c nonce rk inblock 2`;
       `cipherblock_3 = nist_cipher_block aes256_cipher c nonce rk inblock 3`;
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

(* The output forall for loop_count = 1: split j < 4*1 into j = 0, 1, 2, 3
   (close_goal9's split of j < 4*(i+1) would leave a j < 4*0 case), then
   close_goal9's reconstruction for each block. *)
let close_out_forall_i0 : tactic =
  fun (asl,w) ->
    let rkth = try snd(find (fun (_,th) -> concl th = rk15) asl) with _ -> failwith "close_out_forall_i0: no rk-hyp" in
    (REWRITE_TAC[ARITH_RULE `4 * 1 = 4`] THEN
     REWRITE_TAC[ARITH_RULE `j < 4 <=> j = 0 \/ j = 1 \/ j = 2 \/ j = 3`] THEN
     REWRITE_TAC[TAUT `p \/ q ==> r <=> (p ==> r) /\ (q ==> r)`] THEN
     REWRITE_TAC[FORALL_AND_THM; FORALL_UNWIND_THM2] THEN
     (* reduce 16*j to concrete offsets and normalize block 0's
        word_add out_p (word 0) to out_p before ASM_REWRITE_TAC, so that the
        block-0 store fact (at out_p) applies *)
     CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN REWRITE_TAC[WORD_ADD_0] THEN ASM_REWRITE_TAC[] THEN
     (* close_goal9's reconstruction, plus the word_zx normalization of the
        packed counter blocks *)
     REWRITE_TAC[ZXNEST4; ZX_COUNTER_UD; GSYM WORD_ADD] THEN
     REWRITE_TAC[CTR_BLOCK_BUILD_INSERT] THEN
     REWRITE_TAC[SCALAR_RK_RECONSTRUCT] THEN
     REWRITE_TAC[XOR_AES256_CIPHER_RECONSTRUCT] THEN
     ASM_REWRITE_TAC[MAP; WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
     REWRITE_TAC[aes_ctr_block; GSYM ADD_ASSOC] THEN
     REWRITE_TAC[ARITH_RULE `(1:num) + c = c + 1`; ARITH_RULE `(2:num) + c = c + 2`;
                 ARITH_RULE `(3:num) + c = c + 3`; ARITH_RULE `(4:num) + c = c + 4`;
                 ARITH_RULE `(0:num) + c = c`] THEN
     CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[] THEN
     REPEAT CONJ_TAC THEN
     REWRITE_TAC[JOIN_SUBWORD_RECOMBINE] THEN
     REWRITE_TAC[GSYM AES14P_VIA_AES7C; GSYM AES14P_VIA_AES11C; GSYM AES14P_VIA_AES1C; GSYM AES14P_VIA_AES6C] THEN
     REWRITE_TAC[MATCH_MP KEYSTREAM_FOLD256 rkth]) (asl,w);;

(* The per-conjunct closer of ITER1_LEG. *)
let iter1_close_conj : tactic =
  fun (asl,w) ->
    let attempt =
      if is_forall w then close_out_forall_i0
      else if is_eq w && has "nist_ghash" (rhs w) && has "byteswap128" (rhs w) then close_q30_i0
      else if is_eq w && has "word_zx" (rhs w) then ((REWRITE_TAC[ZXNEST4; ZX_COUNTER_UD] THEN AP_TERM_TAC THEN REWRITE_TAC[GSYM WORD_ADD] THEN AP_TERM_TAC THEN ARITH_TAC) ORELSE CONV_TAC WORD_BLAST)
      else close_all_iter1 in
    (* each attempt must close its conjunct; the trailing tactic fails on
       any remaining subgoal *)
    (attempt THEN (fun (a,ww) -> failwith "iter1_close_conj: unclosed subgoal")) (asl,w);;

let ITER1_LEG =
  prove(iter1_goal,
    iter1_head THEN iter1_block_step 1 211 THEN
    ENSURES_FINAL_STATE_TAC THEN INPUT_POSTS_TAC THEN ASM_REWRITE_TAC[] THEN
    ITER1_PRE_CLOSE THEN
    REPEAT CONJ_TAC THEN iter1_close_conj);;

(* ------------------------------------------------------------------------- *)
(* Composing the legs.                                                       *)
(* ------------------------------------------------------------------------- *)

let broad_frame =
  let _,ens = dest_imp drain_goal in last(snd(strip_comb ens));;
let widen_leg = WIDEN_LEG_FRAME_RULE broad_frame;;
let BODYLEG_BROAD = widen_leg BODYLEG;;

(* BODY_DRAIN: swp_inv (loop_count - 2) at pc + 0x560 -> drain_bridge at
   pc + 0xdd0, the last iteration of the loop body and the drain. *)
let body_drain_goal =
  mk_imp(lhand drain_goal,
    list_mk_icomb "ensures" [`arm`;
      leg_state swp_inv `0x560` `loop_count - 2` ; drain_bridge ; broad_frame]);;
let BODY_DRAIN = prove(body_drain_goal,
   REPEAT GEN_TAC THEN INTRO_HYPS_TAC THEN
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

(* MAINLEG: pc + 0xbc -> drain_bridge for loop_count >= 3.  After FILLLEG
   (swp_inv 1 at pc + 0x560), loop_count = 3 goes straight to BODY_DRAIN;
   otherwise an ENSURES_WHILE_UP over loop_count - 3 iterations from
   pc + 0x560 to pc + 0x560, with while_inv k = swp_inv (k+1) (each
   iteration is BODYLEG_BROAD and the cbnz back edge at 0x8a4), reaches
   swp_inv (loop_count - 2), and BODY_DRAIN finishes. *)
let while_inv = mk_gabs(`k:num`, mk_comb(swp_inv, `k + 1`));;

let mainleg_goal =
  mk_imp(lhand fill_goal,
    list_mk_icomb "ensures" [`arm`; fill_pre_state; drain_bridge; broad_frame]);;

let MAINLEG = prove(mainleg_goal,
  REPEAT GEN_TAC THEN INTRO_HYPS_TAC THEN REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  ENSURES_SEQUENCE_TAC `pc + 0x560` (rhs(concl((BETA_CONV THENC REWRITE_CONV[ADD_CLAUSES]) (mk_comb(swp_inv,`1`))))) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN MATCH_MP_TAC FILLLEG THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `loop_count = 3` THENL
   [(fun (asl,w) ->
      let sv = `s:armstate` in
      let invbody = rhs(concl((BETA_CONV THENC REWRITE_CONV[ADD_CLAUSES]) (mk_comb(swp_inv,`loop_count - 2`)))) in
      let invbody_s = rhs(concl(BETA_CONV(mk_comb(invbody,sv)))) in
      let dpre = mk_abs(sv, list_mk_conj(
        [`aligned_bytes_loaded s (word pc) aes256_gcm_enc_tmc`;
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

(* CORE_FROM88: pc + 0xb0 -> tail_post.  Its frame is TAILLEG's, the widest
   (the out_p bytes, the stack slots, ivec_p and tag_p); the legs ending at
   drain_bridge are widened to it. *)
let from88_frame = last(snd(strip_comb(snd(dest_imp(concl(SPEC_ALL TAILLEG))))));;
let widen_to_from88 = WIDEN_LEG_FRAME_RULE from88_frame;;
(* The same entry state at pc + 0xb0, for CORE_FROM88. *)
let from88_entry = mk_abs(`s:armstate`,
  subst [`word (pc + 0xb0):int64`, `word (pc + 188):int64`] (snd(dest_abs fill_pre_state)));;
(* The general precondition: drain_goal's without 2 <= loop_count. *)
let gen_precond = list_mk_conj (filter (fun c -> c <> `2 <= loop_count`) (conjuncts (lhand drain_goal)));;
let core_from88_goal =
  mk_imp(gen_precond, list_mk_icomb "ensures" [`arm`; from88_entry; tail_post; from88_frame]);;
(* The goals of the legs for loop_count = 0, 1 and 2, ending at
   drain_bridge. *)
let mk_lcN_goal n =
  mk_imp(mk_conj(gen_precond, mk_eq(`loop_count:num`, mk_small_numeral n)),
    list_mk_icomb "ensures" [`arm`; from88_entry; drain_bridge; broad_frame]);;
(* loop_count = 0: the cbz x1 at 0xb0 is taken to 0xdd0, skipping the loop.
   One instruction; drain_bridge reduces by list_of_seq _ 0 = [],
   nist_ghash h tag0 [] = tag0, 64*0 = 0 etc.  htable_mem_4 is unfolded in
   the goal first, so that its memory reads carry through the step. *)
let LEG_LC0 = GEN_ALL(prove(mk_lcN_goal 0,
  REWRITE_TAC[SND] THEN REPEAT GEN_TAC THEN INTRO_HYPS_TAC THEN
  REWRITE_TAC[htable_mem_4] THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC AES256_GCM_ENC_EXEC [1] THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[LIST_OF_SEQ; nist_ghash; MULT_CLAUSES; ADD_CLAUSES; WORD_ADD_0; LT; LE_0] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN TRY MONOTONE_MAYCHANGE_TAC));;

(* State predicates without the leading aligned_bytes_loaded and PC
   conjuncts (ENSURES_SEQUENCE_TAC adds them for a waypoint), and with
   htable_mem_4 unfolded. *)
let strip_aligned_pc abs =
  let s,body = dest_abs abs in
  let keep = filter (fun c ->
    not(can (find_term (fun t -> is_const t &&
        (fst(dest_const t)="aligned_bytes_loaded"))) c)
    && not(can (find_term (fun t -> t = `read PC`)) c)
    && not(free_in
        `aes256_gcm_enc_tmc` c))
    (conjuncts body) in
  mk_abs(s, list_mk_conj keep);;
let unfold_htable_in abs =
  let s,body = dest_abs abs in
  mk_abs(s, rhs(concl(REWRITE_CONV[htable_mem_4] body)));;

let drain_bridge_body = strip_aligned_pc drain_bridge;;
let fill_pre_body = strip_aligned_pc fill_pre_state;;
let fill_pre_body_flat = unfold_htable_in fill_pre_body;;

(* The legs for loop_count = 1 (ITER1_LEG) and loop_count = 2, and the
   tactics that apply a leg whose htable_mem_4, frame or postcondition
   differ in form from the goal's. *)
let LEG_LC1 = ITER1_LEG;;
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
let LC2_PARTA_W = WIDEN_LEG_FRAME_RULE broad_frame LC2_PARTA;;
(* LEG_LC2 (loop_count = 2): the hop pc + 0xb0 -> pc + 0xbc (with
   htable_mem_4 folded again at the waypoint), LC2_PARTA (the fill,
   pc + 0xbc -> pc + 0x8a8) and DRAINLEG_8A8 (pc + 0x8a8 -> drain_bridge).
   For the drain, ENSURES_PRECONDITION_TAC takes the full leg_state
   predicate (with the aligned and PC conjuncts) and normalizes the literal
   index 1 against loop_count - 1 under loop_count = 2.  REFOLD_ABI is
   needed before MATCH_MP_TAC DRAINLEG_8A8, whose frame has the ABI part
   folded while the goal's was expanded, and ARITH_TAC discharges its
   2 <= loop_count. *)
let LEG_LC2 = GEN_ALL(prove(mk_lcN_goal 2,
  REPEAT GEN_TAC THEN INTRO_HYPS_TAC THEN REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  ENSURES_SEQUENCE_TAC `pc + 0xbc` (strip_aligned_pc fill_pre_state) THEN CONJ_TAC THENL
   [(* the hop 0xb0 -> 0xbc, with htable_mem_4 folded at the end *)
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
     [(* LC2_PARTA (widened), then the leftover hypotheses of its
         precondition *)
      APPLY_LEG LC2_PARTA_W THEN
      (ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
       TRY(ASM_ARITH_TAC) THEN TRY NONOVERLAPPING_TAC);
      (* the drain, after normalizing the index under loop_count = 2 *)
      ENSURES_PRECONDITION_TAC (leg_state swp_inv `0x8a8` `loop_count - 1`) THEN
      CONJ_TAC THENL
       [GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
        FIRST_ASSUM(fun th -> if lhs(concl th)=`loop_count:num` then REWRITE_TAC[th] else NO_TAC) THEN
        CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];
        REFOLD_ABI THEN MATCH_MP_TAC DRAINLEG_8A8 THEN ASM_REWRITE_TAC[] THEN ARITH_TAC]]]));;

(* Widen the legs that end at drain_bridge to CORE_FROM88's frame. *)
let LEG_LC0_W = widen_to_from88 LEG_LC0;;
let LEG_LC1_W = widen_to_from88 LEG_LC1;;
let LEG_LC2_W = widen_to_from88 LEG_LC2;;
let MAINLEG_W = widen_to_from88 MAINLEG;;

(* The precondition of every leg differs from the context of CORE_FROM88
   only in the orientation of nonoverlapping facts. *)
let leg_precond_close =
  ASM_REWRITE_TAC[] THEN RULE_ASSUM_TAC(ONCE_REWRITE_RULE[nonoverlapping]) THEN
  REWRITE_TAC[nonoverlapping] THEN ONCE_REWRITE_TAC[NONOVERLAPPING_MODULO_SYM] THEN
  ASM_REWRITE_TAC[];;

(* CORE_FROM88: by cases on loop_count, LEG_LC0, LEG_LC1, LEG_LC2 or (for
   loop_count >= 3, after the hop to pc + 0xbc) MAINLEG, all ending at
   drain_bridge; then TAILLEG. *)
let CORE_FROM88 = prove(core_from88_goal,
  REPEAT GEN_TAC THEN INTRO_HYPS_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  ENSURES_SEQUENCE_TAC `pc + 0xdd0` drain_bridge_body THEN
  CONJ_TAC THENL
   [(* the entry at 0xb0 -> drain_bridge at 0xdd0, by cases on
       loop_count *)
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
    (* loop_count >= 3: the hop 0xb0 -> 0xbc (the cmp x1,#1 and b.eq at
       0xb8 fall through), then MAINLEG *)
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
    (* drain_bridge at 0xdd0 -> tail_post at 0xee4 *)
    REWRITE_TAC[GSYM MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    MATCH_MP_TAC TAILLEG THEN leg_precond_close]);;

(* ========================================================================= *)
(* The core correctness theorem, pc + 0x2c -> pc + 0xee4.                    *)
(* ========================================================================= *)

(* The witness for ENSURES_POSTCONDITION_THM below: the stronger
   postcondition of CORE_FROM88, with htable_mem_4 unfolded and flattened
   to match the form of the goal's precondition. *)
let core_from88_post =
  el 2 (snd(strip_comb(snd(dest_imp(snd(strip_forall(
    concl (REWRITE_RULE[htable_mem_4; GSYM CONJ_ASSOC] CORE_FROM88))))))));;
let AES256_GCM_ENC_CORRECT = prove
 (`!in_p len_bits out_p tag_p ivec_p key_p htable_p inblock tag0 nonce c rk pc
     stackpointer.
       aligned 16 stackpointer /\
       ALLPAIRS nonoverlapping
        [(out_p, 16 * val len_bits DIV 128); (tag_p, 16); (ivec_p, 16);
         (word_add stackpointer (word 160), 64)]
        [(word pc, LENGTH aes256_gcm_enc_tmc); (key_p, 240); (htable_p, 96)] /\
       ALL (nonoverlapping (in_p, 16 * val len_bits DIV 128))
        [(tag_p, 16); (ivec_p, 16);
         (word_add stackpointer (word 160), 64)] /\
       (in_p = out_p \/
        nonoverlapping (in_p, 16 * val len_bits DIV 128)
                       (out_p, 16 * val len_bits DIV 128)) /\
       PAIRWISE nonoverlapping
        [(out_p, 16 * val len_bits DIV 128); (tag_p, 16); (ivec_p, 16);
         (word_add stackpointer (word 160), 64)]
    ==>
    ensures arm
      (\s. aligned_bytes_loaded s (word pc) aes256_gcm_enc_tmc /\
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
                    word_xor (aes_ctr_block aes256_cipher c nonce rk i) (inblock i)) /\
           read (memory :> bytes128 tag_p) s =
             word_reversefields 8
              (nist_ghash (aes256_cipher (word 0) rk) tag0
                 (list_of_seq (nist_cipher_block aes256_cipher c nonce rk inblock)
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
  GEN_TAC THEN W64_GEN_TAC `len_bits:num` THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REWRITE_TAC[ALLPAIRS; PAIRWISE; ALL; fst AES256_GCM_ENC_EXEC] THEN

  (*** Abbreviate the loop counts to keep goal terms manageable ***)

  ABBREV_TAC `nblocks     = len_bits DIV 128` THEN
  ABBREV_TAC `loop_count  = nblocks DIV 4` THEN
  ABBREV_TAC `loop_remain = nblocks MOD 4` THEN
  INTRO_HYPS_TAC THEN
  CONV_TAC(ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN REWRITE_TAC[WORD_ADD_0] THEN

  (*** Break up the round key list ***)

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
    (*** Split and abbreviate the two 64-bit IV halves, so that the scalar ***)
    (*** counter registers X11/X12/X13 loaded by "ldp x11,x12,[x4]"        ***)
    (*** survive as variables rather than being dropped as compound        ***)
    (*** initial-memory reads.                                             ***)
    UNDISCH_TAC
     `read (memory :> bytes128 ivec_p) s0 =
      word_reversefields 8 (ctr_block nonce c)` THEN
    GEN_REWRITE_TAC (LAND_CONV o LAND_CONV)
     [el 1 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT)] THEN
    DISCH_TAC THEN
    ABBREV_TAC `ivlo:int64 = read (memory :> bytes64 ivec_p) s0` THEN
    ABBREV_TAC `ivhi:int64 = read (memory :> bytes64 (word_add ivec_p (word 8))) s0` THEN
    (*** The kernel loads the last round key (EL 14 rk) into the scalar    ***)
    (*** pair X20/X21 by "ldp x20,x21,[x5,#224]", so that key cell must be ***)
    (*** split into 64-bit halves (the cells k = 0..13 stay bytes128 for   ***)
    (*** the "ldr q18..q28,q15,q16,q17" vector loads).                     ***)
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o CONV_RULE(READ_MEMORY_SPLIT_CONV 1) o
      check (fun th -> let c = concl th in
        is_eq c && free_in `key_p:int64` (lhs c) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "bytes128"))
            (lhs c) &&
        can (find_term (fun t -> t = `224`)) (lhs c))) THEN
    ARM_STEPS_TAC AES256_GCM_ENC_EXEC (1--33) THEN
    ENSURES_FINAL_STATE_TAC THEN
    (*** Name the IV-halves join relation for reuse in the counter         ***)
    (*** conjuncts; keep ivlo/ivhi unsubstituted so that the ivec          ***)
    (*** recombination still closes.                                       ***)
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
      (*** X13 = counter value c ***)
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
      (*** X16 = loop_remain ***)
      REWRITE_TAC[WORD_USHR_COMPOSE] THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
      ASM_REWRITE_TAC[word_ushr] THEN
      REWRITE_TAC[ARITH_RULE `3 = 2 EXP 2 - 1`] THEN
      REWRITE_TAC[WORD_AND_MASK_WORD; VAL_WORD; DIMINDEX_64] THEN
      REWRITE_TAC[MOD_MOD_EXP_MIN] THEN
      MAP_EVERY EXPAND_TAC ["loop_remain"; "nblocks"] THEN
      AP_TERM_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC;
      (*** Q30 = byteswap128 tag0 ***)
      REWRITE_TAC[byteswap128] THEN CONV_TAC WORD_BLAST];
    MAP_EVERY VAL_INT64_TAC
     [`nblocks:num`; `loop_count:num`; `loop_remain:num`]] THEN
  (* The second branch, pc + 0xb0 -> pc + 0xee4, is CORE_FROM88 up to two
     differences.  (1) htable_mem_4 is unfolded and flattened in the goal's
     precondition (the preamble branch rewrote with htable_mem_4 and
     GSYM CONJ_ASSOC) but folded in from88_entry, so the flattened
     REWRITE_RULE[htable_mem_4; GSYM CONJ_ASSOC] CORE_FROM88 is used.
     (2) The postcondition of CORE_FROM88 is stronger (an extra
     aligned_bytes_loaded conjunct, the output forall last), so it is
     weakened with ENSURES_POSTCONDITION_THM, using it as the witness: the
     implication closes by BETA_RULE and ASM_REWRITE_TAC.  The ABI frame is
     refolded first. *)
  REWRITE_TAC[GSYM MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN
  EXISTS_TAC core_from88_post THEN CONJ_TAC THENL
   [GEN_TAC THEN STRIP_TAC THEN RULE_ASSUM_TAC BETA_RULE THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC (REWRITE_RULE[htable_mem_4; GSYM CONJ_ASSOC] CORE_FROM88) THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC [`len_bits < 2 EXP 64`; `len_bits DIV 128 = nblocks`] THEN
    ARITH_TAC]);;

(* ========================================================================= *)
(* The subroutine theorems: AES256_GCM_ENC_CORRECT lifted through the        *)
(* 11-instruction prologue and epilogue, which save and restore D8-D15 and   *)
(* X19-X30 in a 224-byte frame (ARM_ADD_RETURN_STACK_TAC), then to the full  *)
(* code with its BTI landing pad.                                            *)
(* ========================================================================= *)

let AES256_GCM_ENC_NOIBT_SUBROUTINE_CORRECT = prove
 (`!in_p len_bits out_p tag_p ivec_p key_p htable_p inblock tag0 nonce c rk
    pc stackpointer returnaddress.
    aligned 16 stackpointer /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * val len_bits DIV 128); (tag_p, 16); (ivec_p, 16);
       (word_sub stackpointer (word 224), 224)]
      [(word pc, LENGTH aes256_gcm_enc_tmc); (key_p, 240); (htable_p, 96)] /\
    ALL (nonoverlapping (in_p, 16 * val len_bits DIV 128))
      [(tag_p, 16); (ivec_p, 16);
       (word_sub stackpointer (word 224), 224)] /\
    (in_p = out_p \/
     nonoverlapping (in_p, 16 * val len_bits DIV 128)
                    (out_p, 16 * val len_bits DIV 128)) /\
    PAIRWISE nonoverlapping
      [(out_p, 16 * val len_bits DIV 128); (tag_p, 16); (ivec_p, 16);
       (word_sub stackpointer (word 224), 224)]
    ==>
    ensures arm
      (\s. aligned_bytes_loaded s (word pc) aes256_gcm_enc_tmc /\
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
                    word_xor (aes_ctr_block aes256_cipher c nonce rk i) (inblock i)) /\
           read (memory :> bytes128 tag_p) s =
             word_reversefields 8
              (nist_ghash (aes256_cipher (word 0) rk) tag0
                 (list_of_seq (nist_cipher_block aes256_cipher c nonce rk inblock)
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

(* The same for the full code, with its BTI landing pad. *)

let AES256_GCM_ENC_SUBROUTINE_CORRECT = prove
 (`!in_p len_bits out_p tag_p ivec_p key_p htable_p inblock tag0 nonce c rk
    pc stackpointer returnaddress.
    aligned 16 stackpointer /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * val len_bits DIV 128); (tag_p, 16); (ivec_p, 16);
       (word_sub stackpointer (word 224), 224)]
      [(word pc, LENGTH aes256_gcm_enc_mc); (key_p, 240); (htable_p, 96)] /\
    ALL (nonoverlapping (in_p, 16 * val len_bits DIV 128))
      [(tag_p, 16); (ivec_p, 16);
       (word_sub stackpointer (word 224), 224)] /\
    (in_p = out_p \/
     nonoverlapping (in_p, 16 * val len_bits DIV 128)
                    (out_p, 16 * val len_bits DIV 128)) /\
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
                    word_xor (aes_ctr_block aes256_cipher c nonce rk i) (inblock i)) /\
           read (memory :> bytes128 tag_p) s =
             word_reversefields 8
              (nist_ghash (aes256_cipher (word 0) rk) tag0
                 (list_of_seq (nist_cipher_block aes256_cipher c nonce rk inblock)
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
  MATCH_ACCEPT_TAC(ARM_ADD_IBT_RULE ~extra:[htable_mem_4; wordlist_from_memory]
    aes256_gcm_enc_mc aes256_gcm_enc_tmc AES256_GCM_ENC_NOIBT_SUBROUTINE_CORRECT));;

(* ========================================================================= *)
(* Constant time and memory safety.  AES256_GCM_ENC_SAFE covers the same     *)
(* core as AES256_GCM_ENC_CORRECT (pc + 0x2c -> pc + 0xee4): the event trace *)
(* is a function of the public arguments only, given by the scaffold         *)
(* scaffold_enc (CONCRETIZE_F_EVENTS_TAC), and every memory access stays     *)
(* within the declared buffers.  The proof walks the same regions with the   *)
(* event-tracking simulator SAFE_SIM: the preamble, the cases loop_count =   *)
(* 0, 1 and 2, and for loop_count >= 3 a loop of loop_count - 2 iterations   *)
(* from pc + 0x560 to pc + 0x8a8 between the fill and the drain, then the    *)
(* tail loop.  The leaf obligations are closed by the shared closers of      *)
(* utils/aes_gcm_common.ml and the reconcilers FILL_X1 and DRAIN_ADDR_K.     *)
(* ========================================================================= *)

let SAFE_SIM = SAFE_SIM_TAC AES256_GCM_ENC_EXEC;;

(* The fill's X1: word_sub (word C) (word 2) = word (C - 2 - 0), where
   C = len_bits DIV 512 = loop_count.  Guarded so that it only fires on a
   word_sub by 2. *)
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

(* The leaf closer: the shared chain plus the reconcilers for the fill's
   counter (FILL_X1) and the drain pointers (DRAIN_ADDR_K). *)
let CLOSE_ENC = CLOSE_R2_WITH [FILL_X1; DRAIN_ADDR_K `1`; DRAIN_ADDR_K `2`];;
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
        [(word pc, LENGTH aes256_gcm_enc_tmc); (key_p, 240); (htable_p, 96)] /\
      ALL (nonoverlapping (in_p, 16 * val len_bits DIV 128))
        [(tag_p, 16); (ivec_p, 16);
         (word_add stackpointer (word 160), 64)] /\
      (in_p = out_p \/
       nonoverlapping (in_p, 16 * val len_bits DIV 128)
                      (out_p, 16 * val len_bits DIV 128)) /\
      PAIRWISE nonoverlapping
        [(out_p, 16 * val len_bits DIV 128); (tag_p, 16); (ivec_p, 16);
         (word_add stackpointer (word 160), 64)]
      ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) aes256_gcm_enc_tmc /\
               read PC s = word (pc + 0x2c) /\ read SP s = stackpointer /\
               C_ARGUMENTS [in_p; len_bits; out_p; tag_p; ivec_p; key_p; htable_p] s /\
               read events s = e)
          (\s. read PC s = word (pc + 0xee4) /\
               (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events in_p out_p tag_p ivec_p key_p htable_p len_bits pc stackpointer /\
                    memaccess_inbounds e2
                      [in_p, 16 * val len_bits DIV 128; tag_p, 16; ivec_p, 16; key_p, 240; htable_p, 96;
                       out_p, 16 * val len_bits DIV 128; word_add stackpointer (word 160), 64]
                      [out_p, 16 * val len_bits DIV 128; tag_p, 16; ivec_p, 16;
                       word_add stackpointer (word 160), 64]))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [X19; X20; X21; X22; X23; X24;
                      X25; X26; X27; X28; X29; X30] ,,
           MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
           MAYCHANGE [memory :> bytes(out_p, 16 * val len_bits DIV 128);
                      memory :> bytes(tag_p, 16);
                      memory :> bytes(ivec_p, 16);
                      memory :> bytes(word_add stackpointer (word 160), 64)])`,
  CONCRETIZE_F_EVENTS_TAC scaffold_enc THEN OPEN_ENC THEN
  (* the top split at 0xdd0, between the main region and the tail *)
  ENSURES_EVENTS_SEQUENCE_TAC `pc + 0xdd0`
   `\s. read X0 s = word_add in_p (word (64 * loop_count)) /\
        read X2 s = word_add out_p (word (64 * loop_count)) /\
        read X3 s = tag_p /\ read X4 s = ivec_p /\ read X6 s = htable_p /\
        read SP s = stackpointer /\ read X16 s = word loop_remain` THEN
  CONJ_TAC THENL
   [(* the main region, pc + 0x2c -> pc + 0xdd0 *)
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
  (* the tail region, pc + 0xdd0 -> pc + 0xee4 *)
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

(* ------------------------------------------------------------------------- *)
(* The whole-function version, obtained from the core theorem exactly as the *)
(* correctness theorem is: the 11-instruction prologue and epilogue save and *)
(* restore the callee-saved registers in a 224-byte frame.                   *)
(* ------------------------------------------------------------------------- *)
let AES256_GCM_ENC_NOIBT_SUBROUTINE_SAFE = prove
 (`exists f_events.
    forall e in_p len_bits out_p tag_p ivec_p key_p htable_p pc stackpointer returnaddress.
      aligned 16 stackpointer /\
      ALLPAIRS nonoverlapping
        [(out_p, 16 * val len_bits DIV 128); (tag_p, 16); (ivec_p, 16);
         (word_sub stackpointer (word 224), 224)]
        [(word pc, LENGTH aes256_gcm_enc_tmc); (key_p, 240); (htable_p, 96)] /\
      ALL (nonoverlapping (in_p, 16 * val len_bits DIV 128))
        [(tag_p, 16); (ivec_p, 16);
         (word_sub stackpointer (word 224), 224)] /\
      (in_p = out_p \/
       nonoverlapping (in_p, 16 * val len_bits DIV 128)
                      (out_p, 16 * val len_bits DIV 128)) /\
      PAIRWISE nonoverlapping
        [(out_p, 16 * val len_bits DIV 128); (tag_p, 16); (ivec_p, 16);
         (word_sub stackpointer (word 224), 224)]
      ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) aes256_gcm_enc_tmc /\
               read PC s = word pc /\ read SP s = stackpointer /\ read X30 s = returnaddress /\
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
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(out_p, 16 * val len_bits DIV 128);
                      memory :> bytes(tag_p, 16);
                      memory :> bytes(ivec_p, 16);
                      memory :> bytes(word_sub stackpointer (word 224), 224)])`,
  ARM_ADD_RETURN_STACK_TAC
    ~pre_post_nsteps:(11, 11)
    AES256_GCM_ENC_EXEC AES256_GCM_ENC_SAFE
    `[X19; X20; X21; X22; X23; X24; X25; X26; X27; X28; X29; X30;
      D8; D9; D10; D11; D12; D13; D14; D15]` 224 THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

(* The same for the full code, with its BTI landing pad. *)

let AES256_GCM_ENC_SUBROUTINE_SAFE = prove
 (`exists f_events.
    forall e in_p len_bits out_p tag_p ivec_p key_p htable_p pc stackpointer returnaddress.
      aligned 16 stackpointer /\
      ALLPAIRS nonoverlapping
        [(out_p, 16 * val len_bits DIV 128); (tag_p, 16); (ivec_p, 16);
         (word_sub stackpointer (word 224), 224)]
        [(word pc, LENGTH aes256_gcm_enc_mc); (key_p, 240); (htable_p, 96)] /\
      ALL (nonoverlapping (in_p, 16 * val len_bits DIV 128))
        [(tag_p, 16); (ivec_p, 16);
         (word_sub stackpointer (word 224), 224)] /\
      (in_p = out_p \/
       nonoverlapping (in_p, 16 * val len_bits DIV 128)
                      (out_p, 16 * val len_bits DIV 128)) /\
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
                      [in_p, 16 * val len_bits DIV 128; tag_p, 16; ivec_p, 16; key_p, 240; htable_p, 96;
                       out_p, 16 * val len_bits DIV 128; word_sub stackpointer (word 224), 224]
                      [out_p, 16 * val len_bits DIV 128; tag_p, 16; ivec_p, 16;
                       word_sub stackpointer (word 224), 224]))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(out_p, 16 * val len_bits DIV 128);
                      memory :> bytes(tag_p, 16);
                      memory :> bytes(ivec_p, 16);
                      memory :> bytes(word_sub stackpointer (word 224), 224)])`,
  MATCH_ACCEPT_TAC(ARM_ADD_IBT_RULE
    aes256_gcm_enc_mc aes256_gcm_enc_tmc AES256_GCM_ENC_NOIBT_SUBROUTINE_SAFE));;
