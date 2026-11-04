(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Functional correctness, constant-time and memory-safety proofs of the     *)
(* AES-128-GCM bulk encryption kernel aes128_gcm_enc, the 4-way              *)
(* software-pipelined kernel.                                                *)
(*                                                                           *)
(* The kernel processes the len_bits DIV 128 whole 16-byte blocks of its     *)
(* input: block i is encrypted in counter mode with the counter block        *)
(* ctr_block nonce (i + c), the ciphertext is folded into the GHASH tag, and *)
(* the tag and the next counter block ctr_block nonce (nblocks + c) are      *)
(* written back; X0 returns the byte length len_bits DIV 8.                  *)
(*                                                                           *)
(* The core theorem AES128_GCM_ENC_CORRECT runs from pc + 0x2c, after the    *)
(* register saves, to pc + 0x710, before the restores.  The preamble (round  *)
(* keys, tag, counter registers and block counts) ends at pc + 0x88 and      *)
(* CORE_FROM88 covers the rest.  The loop over groups of four blocks is      *)
(* software-pipelined: each iteration also starts the AES rounds of blocks   *)
(* 1..3 of the next group, so the loop invariant swp_inv, asserted at the    *)
(* loop head pc + 0x1ec, records partial encryptions of the current group    *)
(* besides the tag and the output of the blocks already done.  The legs are  *)
(* FILLLEG (pc + 0x88 -> pc + 0x1ec, establishing swp_inv 0), BODYLEG (one   *)
(* iteration, pc + 0x1ec -> pc + 0x4b0), REDUCELAST (the last group,         *)
(* pc + 0x4b0 -> pc + 0x61c), TAILLEG (the single-block tail loop and the    *)
(* tag and counter stores, pc + 0x61c -> pc + 0x710) and MAINLEG_LC1 (the    *)
(* case loop_count = 1).  MAINLEG composes FILLLEG, an ENSURES_WHILE_UP over *)
(* loop_count - 2 iterations at pc + 0x1ec and DRAINLEG (one more iteration  *)
(* and REDUCELAST).  The safety theorems follow the same regions with the    *)
(* event-tracking simulator.                                                 *)
(*                                                                           *)
(* The specification vocabulary (ctr_block, aes_ctr_block,                   *)
(* nist_cipher_block, htable_mem_4) is in arm/proofs/utils/aes_gcm_spec.ml;  *)
(* the lemmas and tactics shared with the other AES-GCM proofs are in        *)
(* arm/proofs/utils/aes_gcm_common.ml.                                       *)
(*                                                                           *)
(* The code begins with a BTI landing pad (bti c).  The proofs are about the *)
(* trimmed code aes128_gcm_enc_tmc without it, which is also the code of a   *)
(* -DNO_IBT build, so all offsets above are offsets in that code; the        *)
(* subroutine theorems for the full code are derived by ARM_ADD_IBT_RULE.    *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "arm/proofs/utils/aes_gcm_common.ml";;

(* ------------------------------------------------------------------------- *)
(* The machine code.                                                         *)
(* ------------------------------------------------------------------------- *)

let aes128_gcm_enc_mc = define_assert_from_elf "aes128_gcm_enc_mc" "arm/aes_gcm/aes128_gcm_enc.o"
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
  0xa94a54b4;       (* arm_LDP X20 X21 X5 (Immediate_Offset (iword (&160))) *)
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
  0xb4002ca1;       (* arm_CBZ X1 (word 1428) *)
  0x11000dae;       (* arm_ADD W14 W13 (rvalue (word 3)) *)
  0x110001b3;       (* arm_ADD W19 W13 (rvalue (word 0)) *)
  0x110009b8;       (* arm_ADD W24 W13 (rvalue (word 2)) *)
  0x110005be;       (* arm_ADD W30 W13 (rvalue (word 1)) *)
  0x110011ad;       (* arm_ADD W13 W13 (rvalue (word 4)) *)
  0x5ac00b16;       (* arm_REV W22 W24 *)
  0x5ac00bde;       (* arm_REV W30 W30 *)
  0xaa16819a;       (* arm_ORR X26 X12 (Shiftedreg X22 LSL 32) *)
  0xaa1e8199;       (* arm_ORR X25 X12 (Shiftedreg X30 LSL 32) *)
  0xa90c6beb;       (* arm_STP X11 X26 SP (Immediate_Offset (iword (&192))) *)
  0xa90b67eb;       (* arm_STP X11 X25 SP (Immediate_Offset (iword (&176))) *)
  0x5ac00a7d;       (* arm_REV W29 W19 *)
  0x3dc033e9;       (* arm_LDR Q9 SP (Immediate_Offset (word 192)) *)
  0xa941580a;       (* arm_LDP X10 X22 X0 (Immediate_Offset (iword (&16))) *)
  0xaa1d8191;       (* arm_ORR X17 X12 (Shiftedreg X29 LSL 32) *)
  0x5ac009db;       (* arm_REV W27 W14 *)
  0xaa1b8188;       (* arm_ORR X8 X12 (Shiftedreg X27 LSL 32) *)
  0xa90a47eb;       (* arm_STP X11 X17 SP (Immediate_Offset (iword (&160))) *)
  0xca1502d7;       (* arm_EOR X23 X22 X21 *)
  0xa942581c;       (* arm_LDP X28 X22 X0 (Immediate_Offset (iword (&32))) *)
  0x4e284a49;       (* arm_AESE Q9 Q18 *)
  0x4e286929;       (* arm_AESMC Q9 Q9 *)
  0xa90d23eb;       (* arm_STP X11 X8 SP (Immediate_Offset (iword (&208))) *)
  0xa943601d;       (* arm_LDP X29 X24 X0 (Immediate_Offset (iword (&48))) *)
  0x4e284a69;       (* arm_AESE Q9 Q19 *)
  0x4e286929;       (* arm_AESMC Q9 Q9 *)
  0xca1502da;       (* arm_EOR X26 X22 X21 *)
  0xca14038e;       (* arm_EOR X14 X28 X20 *)
  0xca14015c;       (* arm_EOR X28 X10 X20 *)
  0xa90c6bee;       (* arm_STP X14 X26 SP (Immediate_Offset (iword (&192))) *)
  0xca150308;       (* arm_EOR X8 X24 X21 *)
  0xca1403a7;       (* arm_EOR X7 X29 X20 *)
  0x4e284a89;       (* arm_AESE Q9 Q20 *)
  0x4e286929;       (* arm_AESMC Q9 Q9 *)
  0x3dc037fc;       (* arm_LDR Q28 SP (Immediate_Offset (word 208)) *)
  0xa90d23e7;       (* arm_STP X7 X8 SP (Immediate_Offset (iword (&208))) *)
  0x3dc02fec;       (* arm_LDR Q12 SP (Immediate_Offset (word 176)) *)
  0x4e284aa9;       (* arm_AESE Q9 Q21 *)
  0x4e286929;       (* arm_AESMC Q9 Q9 *)
  0x4e284a5c;       (* arm_AESE Q28 Q18 *)
  0x4e286b9c;       (* arm_AESMC Q28 Q28 *)
  0x4e284a4c;       (* arm_AESE Q12 Q18 *)
  0x4e28698c;       (* arm_AESMC Q12 Q12 *)
  0x3dc037ef;       (* arm_LDR Q15 SP (Immediate_Offset (word 208)) *)
  0x4e284a7c;       (* arm_AESE Q28 Q19 *)
  0x4e286b9c;       (* arm_AESMC Q28 Q28 *)
  0x4e284ac9;       (* arm_AESE Q9 Q22 *)
  0x4e286929;       (* arm_AESMC Q9 Q9 *)
  0x4e284a9c;       (* arm_AESE Q28 Q20 *)
  0x4e286b9c;       (* arm_AESMC Q28 Q28 *)
  0x4e284abc;       (* arm_AESE Q28 Q21 *)
  0x4e286b9c;       (* arm_AESMC Q28 Q28 *)
  0x4e284adc;       (* arm_AESE Q28 Q22 *)
  0x4e286b9c;       (* arm_AESMC Q28 Q28 *)
  0x4e284afc;       (* arm_AESE Q28 Q23 *)
  0x4e286b9c;       (* arm_AESMC Q28 Q28 *)
  0x4e284ae9;       (* arm_AESE Q9 Q23 *)
  0x4e286929;       (* arm_AESMC Q9 Q9 *)
  0x4e284a6c;       (* arm_AESE Q12 Q19 *)
  0x4e28698c;       (* arm_AESMC Q12 Q12 *)
  0x4e284a8c;       (* arm_AESE Q12 Q20 *)
  0x4e28698c;       (* arm_AESMC Q12 Q12 *)
  0x4e284b1c;       (* arm_AESE Q28 Q24 *)
  0x4e286b9c;       (* arm_AESMC Q28 Q28 *)
  0x3dc000c5;       (* arm_LDR Q5 X6 (Immediate_Offset (word 0)) *)
  0x4e284aac;       (* arm_AESE Q12 Q21 *)
  0x4e28698c;       (* arm_AESMC Q12 Q12 *)
  0x4e284b3c;       (* arm_AESE Q28 Q25 *)
  0x4e286b9c;       (* arm_AESMC Q28 Q28 *)
  0x3dc008d1;       (* arm_LDR Q17 X6 (Immediate_Offset (word 32)) *)
  0x4e284acc;       (* arm_AESE Q12 Q22 *)
  0x4e28698c;       (* arm_AESMC Q12 Q12 *)
  0x3dc004df;       (* arm_LDR Q31 X6 (Immediate_Offset (word 16)) *)
  0x4e284b5c;       (* arm_AESE Q28 Q26 *)
  0x4e286b9c;       (* arm_AESMC Q28 Q28 *)
  0x4e284aec;       (* arm_AESE Q12 Q23 *)
  0x4e28698c;       (* arm_AESMC Q12 Q12 *)
  0x4e284b7c;       (* arm_AESE Q28 Q27 *)
  0x3dc033ea;       (* arm_LDR Q10 SP (Immediate_Offset (word 192)) *)
  0x4e284b0c;       (* arm_AESE Q12 Q24 *)
  0x4e28698c;       (* arm_AESMC Q12 Q12 *)
  0x4e284b09;       (* arm_AESE Q9 Q24 *)
  0x4e286929;       (* arm_AESMC Q9 Q9 *)
  0x3dc010c6;       (* arm_LDR Q6 X6 (Immediate_Offset (word 64)) *)
  0x4e284b2c;       (* arm_AESE Q12 Q25 *)
  0x4e28698c;       (* arm_AESMC Q12 Q12 *)
  0xd1000421;       (* arm_SUB X1 X1 (rvalue (word 1)) *)
  0xb4001661;       (* arm_CBZ X1 (word 716) *)
  0x3dc02be0;       (* arm_LDR Q0 SP (Immediate_Offset (word 160)) *)
  0x4e284b29;       (* arm_AESE Q9 Q25 *)
  0x4e286929;       (* arm_AESMC Q9 Q9 *)
  0x11000dae;       (* arm_ADD W14 W13 (rvalue (word 3)) *)
  0x110001b3;       (* arm_ADD W19 W13 (rvalue (word 0)) *)
  0x4e284b4c;       (* arm_AESE Q12 Q26 *)
  0x4e28698c;       (* arm_AESMC Q12 Q12 *)
  0x6e3c1def;       (* arm_EOR_VEC Q15 Q15 Q28 128 *)
  0x110009b8;       (* arm_ADD W24 W13 (rvalue (word 2)) *)
  0xa90b5ffc;       (* arm_STP X28 X23 SP (Immediate_Offset (iword (&176))) *)
  0x4e284b49;       (* arm_AESE Q9 Q26 *)
  0x4e286929;       (* arm_AESMC Q9 Q9 *)
  0x3dc014cb;       (* arm_LDR Q11 X6 (Immediate_Offset (word 80)) *)
  0x110005be;       (* arm_ADD W30 W13 (rvalue (word 1)) *)
  0x110011ad;       (* arm_ADD W13 W13 (rvalue (word 4)) *)
  0x4e2009f0;       (* arm_REV64_VEC Q16 Q15 8 *)
  0x4e284b6c;       (* arm_AESE Q12 Q27 *)
  0x5ac00b16;       (* arm_REV W22 W24 *)
  0xa8c41c11;       (* arm_LDP X17 X7 X0 (Postimmediate_Offset (iword (&64))) *)
  0x3dc02fed;       (* arm_LDR Q13 SP (Immediate_Offset (word 176)) *)
  0x4e284b69;       (* arm_AESE Q9 Q27 *)
  0x5ac00bde;       (* arm_REV W30 W30 *)
  0xaa16819a;       (* arm_ORR X26 X12 (Shiftedreg X22 LSL 32) *)
  0x5e180601;       (* arm_DUP_ELEM_SCALAR Q1 Q16 1 64 *)
  0x4e284a40;       (* arm_AESE Q0 Q18 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0xaa1e8199;       (* arm_ORR X25 X12 (Shiftedreg X30 LSL 32) *)
  0xa90c6beb;       (* arm_STP X11 X26 SP (Immediate_Offset (iword (&192))) *)
  0x0ee5e20e;       (* arm_PMULL_VEC Q14 Q16 Q5 64 *)
  0x6e291d5c;       (* arm_EOR_VEC Q28 Q10 Q9 128 *)
  0xa90b67eb;       (* arm_STP X11 X25 SP (Immediate_Offset (iword (&176))) *)
  0x5ac00a7d;       (* arm_REV W29 W19 *)
  0x3dc033e9;       (* arm_LDR Q9 SP (Immediate_Offset (word 192)) *)
  0x4e284a60;       (* arm_AESE Q0 Q19 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0xca1500e7;       (* arm_EOR X7 X7 X21 *)
  0xca140228;       (* arm_EOR X8 X17 X20 *)
  0x4e200b88;       (* arm_REV64_VEC Q8 Q28 8 *)
  0x4ee5e202;       (* arm_PMULL2_VEC Q2 Q16 Q5 64 *)
  0xa941580a;       (* arm_LDP X10 X22 X0 (Immediate_Offset (iword (&16))) *)
  0xa90a1fe8;       (* arm_STP X8 X7 SP (Immediate_Offset (iword (&160))) *)
  0x4e284a80;       (* arm_AESE Q0 Q20 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x2e301c24;       (* arm_EOR_VEC Q4 Q1 Q16 64 *)
  0xaa1d8191;       (* arm_ORR X17 X12 (Shiftedreg X29 LSL 32) *)
  0x5ac009db;       (* arm_REV W27 W14 *)
  0x0ef1e101;       (* arm_PMULL_VEC Q1 Q8 Q17 64 *)
  0x3dc02bf0;       (* arm_LDR Q16 SP (Immediate_Offset (word 160)) *)
  0xaa1b8188;       (* arm_ORR X8 X12 (Shiftedreg X27 LSL 32) *)
  0xa90a47eb;       (* arm_STP X11 X17 SP (Immediate_Offset (iword (&160))) *)
  0x4ef1e103;       (* arm_PMULL2_VEC Q3 Q8 Q17 64 *)
  0x6e2c1dad;       (* arm_EOR_VEC Q13 Q13 Q12 128 *)
  0x0effe085;       (* arm_PMULL_VEC Q5 Q4 Q31 64 *)
  0x6e211dd1;       (* arm_EOR_VEC Q17 Q14 Q1 128 *)
  0xca1502d7;       (* arm_EOR X23 X22 X21 *)
  0xa942581c;       (* arm_LDP X28 X22 X0 (Immediate_Offset (iword (&32))) *)
  0x6e231c44;       (* arm_EOR_VEC Q4 Q2 Q3 128 *)
  0x4e284aa0;       (* arm_AESE Q0 Q21 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x3dc00cc1;       (* arm_LDR Q1 X6 (Immediate_Offset (word 48)) *)
  0x4e284a49;       (* arm_AESE Q9 Q18 *)
  0x4e286929;       (* arm_AESMC Q9 Q9 *)
  0xa90d23eb;       (* arm_STP X11 X8 SP (Immediate_Offset (iword (&208))) *)
  0x4e284ac0;       (* arm_AESE Q0 Q22 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e2009a2;       (* arm_REV64_VEC Q2 Q13 8 *)
  0xa943601d;       (* arm_LDP X29 X24 X0 (Immediate_Offset (iword (&48))) *)
  0x4e284a69;       (* arm_AESE Q9 Q19 *)
  0x4e286929;       (* arm_AESMC Q9 Q9 *)
  0xca1502da;       (* arm_EOR X26 X22 X21 *)
  0xca14038e;       (* arm_EOR X14 X28 X20 *)
  0x3d80044d;       (* arm_STR Q13 X2 (Immediate_Offset (word 16)) *)
  0x4e284ae0;       (* arm_AESE Q0 Q23 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0xca14015c;       (* arm_EOR X28 X10 X20 *)
  0x3d80085c;       (* arm_STR Q28 X2 (Immediate_Offset (word 32)) *)
  0x0ee1e05d;       (* arm_PMULL_VEC Q29 Q2 Q1 64 *)
  0x5e18045c;       (* arm_DUP_ELEM_SCALAR Q28 Q2 1 64 *)
  0x4e284b00;       (* arm_AESE Q0 Q24 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0xa90c6bee;       (* arm_STP X14 X26 SP (Immediate_Offset (iword (&192))) *)
  0xca150308;       (* arm_EOR X8 X24 X21 *)
  0x4ee1e04d;       (* arm_PMULL2_VEC Q13 Q2 Q1 64 *)
  0x6e3d1e31;       (* arm_EOR_VEC Q17 Q17 Q29 128 *)
  0xca1403a7;       (* arm_EOR X7 X29 X20 *)
  0x2e221f82;       (* arm_EOR_VEC Q2 Q28 Q2 64 *)
  0x4e284b20;       (* arm_AESE Q0 Q25 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x6e08410a;       (* arm_EXT Q10 Q8 Q8 64 *)
  0x4e284a89;       (* arm_AESE Q9 Q20 *)
  0x4e286929;       (* arm_AESMC Q9 Q9 *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x3dc037fc;       (* arm_LDR Q28 SP (Immediate_Offset (word 208)) *)
  0xa90d23e7;       (* arm_STP X7 X8 SP (Immediate_Offset (iword (&208))) *)
  0x0ee6e05d;       (* arm_PMULL_VEC Q29 Q2 Q6 64 *)
  0x3dc02fec;       (* arm_LDR Q12 SP (Immediate_Offset (word 176)) *)
  0x6e281d42;       (* arm_EOR_VEC Q2 Q10 Q8 128 *)
  0x4e284b60;       (* arm_AESE Q0 Q27 *)
  0x3d800c4f;       (* arm_STR Q15 X2 (Immediate_Offset (word 48)) *)
  0x4e284aa9;       (* arm_AESE Q9 Q21 *)
  0x4e286929;       (* arm_AESMC Q9 Q9 *)
  0x6e201e01;       (* arm_EOR_VEC Q1 Q16 Q0 128 *)
  0x4e284a5c;       (* arm_AESE Q28 Q18 *)
  0x4e286b9c;       (* arm_AESMC Q28 Q28 *)
  0x4e284a4c;       (* arm_AESE Q12 Q18 *)
  0x4e28698c;       (* arm_AESMC Q12 Q12 *)
  0x3dc037ef;       (* arm_LDR Q15 SP (Immediate_Offset (word 208)) *)
  0x4e284a7c;       (* arm_AESE Q28 Q19 *)
  0x4e286b9c;       (* arm_AESMC Q28 Q28 *)
  0x4e200830;       (* arm_REV64_VEC Q16 Q1 8 *)
  0x3c840441;       (* arm_STR Q1 X2 (Postimmediate_Offset (word 64)) *)
  0x4e284ac9;       (* arm_AESE Q9 Q22 *)
  0x4e286929;       (* arm_AESMC Q9 Q9 *)
  0x4e284a9c;       (* arm_AESE Q28 Q20 *)
  0x4e286b9c;       (* arm_AESMC Q28 Q28 *)
  0x6e3e1e0e;       (* arm_EOR_VEC Q14 Q16 Q30 128 *)
  0x6e2d1c8d;       (* arm_EOR_VEC Q13 Q4 Q13 128 *)
  0x4effe044;       (* arm_PMULL2_VEC Q4 Q2 Q31 64 *)
  0x6e0e41c3;       (* arm_EXT Q3 Q14 Q14 64 *)
  0x4eebe1c1;       (* arm_PMULL2_VEC Q1 Q14 Q11 64 *)
  0x6e241cbf;       (* arm_EOR_VEC Q31 Q5 Q4 128 *)
  0x4e284abc;       (* arm_AESE Q28 Q21 *)
  0x4e286b9c;       (* arm_AESMC Q28 Q28 *)
  0x6e2e1c60;       (* arm_EOR_VEC Q0 Q3 Q14 128 *)
  0x0eebe1ce;       (* arm_PMULL_VEC Q14 Q14 Q11 64 *)
  0x6e3d1fe4;       (* arm_EOR_VEC Q4 Q31 Q29 128 *)
  0x4e284adc;       (* arm_AESE Q28 Q22 *)
  0x4e286b9c;       (* arm_AESMC Q28 Q28 *)
  0x4ee6e006;       (* arm_PMULL2_VEC Q6 Q0 Q6 64 *)
  0x6e2e1e2e;       (* arm_EOR_VEC Q14 Q17 Q14 128 *)
  0x4e284afc;       (* arm_AESE Q28 Q23 *)
  0x4e286b9c;       (* arm_AESMC Q28 Q28 *)
  0x6e211da1;       (* arm_EOR_VEC Q1 Q13 Q1 128 *)
  0x6e261c9d;       (* arm_EOR_VEC Q29 Q4 Q6 128 *)
  0x4e284ae9;       (* arm_AESE Q9 Q23 *)
  0x4e286929;       (* arm_AESMC Q9 Q9 *)
  0x6e211dcd;       (* arm_EOR_VEC Q13 Q14 Q1 128 *)
  0x4e284a6c;       (* arm_AESE Q12 Q19 *)
  0x4e28698c;       (* arm_AESMC Q12 Q12 *)
  0x0ee7e023;       (* arm_PMULL_VEC Q3 Q1 Q7 64 *)
  0x6e014024;       (* arm_EXT Q4 Q1 Q1 64 *)
  0x6e2d1fa1;       (* arm_EOR_VEC Q1 Q29 Q13 128 *)
  0x4e284a8c;       (* arm_AESE Q12 Q20 *)
  0x4e28698c;       (* arm_AESMC Q12 Q12 *)
  0x6e231c91;       (* arm_EOR_VEC Q17 Q4 Q3 128 *)
  0x4e284b1c;       (* arm_AESE Q28 Q24 *)
  0x4e286b9c;       (* arm_AESMC Q28 Q28 *)
  0x3dc000c5;       (* arm_LDR Q5 X6 (Immediate_Offset (word 0)) *)
  0x4e284aac;       (* arm_AESE Q12 Q21 *)
  0x4e28698c;       (* arm_AESMC Q12 Q12 *)
  0x6e311c23;       (* arm_EOR_VEC Q3 Q1 Q17 128 *)
  0x4e284b3c;       (* arm_AESE Q28 Q25 *)
  0x4e286b9c;       (* arm_AESMC Q28 Q28 *)
  0x3dc008d1;       (* arm_LDR Q17 X6 (Immediate_Offset (word 32)) *)
  0x4e284acc;       (* arm_AESE Q12 Q22 *)
  0x4e28698c;       (* arm_AESMC Q12 Q12 *)
  0x0ee7e070;       (* arm_PMULL_VEC Q16 Q3 Q7 64 *)
  0x3dc004df;       (* arm_LDR Q31 X6 (Immediate_Offset (word 16)) *)
  0x4e284b5c;       (* arm_AESE Q28 Q26 *)
  0x4e286b9c;       (* arm_AESMC Q28 Q28 *)
  0x6e034062;       (* arm_EXT Q2 Q3 Q3 64 *)
  0x4e284aec;       (* arm_AESE Q12 Q23 *)
  0x4e28698c;       (* arm_AESMC Q12 Q12 *)
  0x6e301dce;       (* arm_EOR_VEC Q14 Q14 Q16 128 *)
  0x4e284b7c;       (* arm_AESE Q28 Q27 *)
  0x3dc033ea;       (* arm_LDR Q10 SP (Immediate_Offset (word 192)) *)
  0x6e221dd0;       (* arm_EOR_VEC Q16 Q14 Q2 128 *)
  0x4e284b0c;       (* arm_AESE Q12 Q24 *)
  0x4e28698c;       (* arm_AESMC Q12 Q12 *)
  0x4e284b09;       (* arm_AESE Q9 Q24 *)
  0x4e286929;       (* arm_AESMC Q9 Q9 *)
  0x3dc010c6;       (* arm_LDR Q6 X6 (Immediate_Offset (word 64)) *)
  0x4e284b2c;       (* arm_AESE Q12 Q25 *)
  0x4e28698c;       (* arm_AESMC Q12 Q12 *)
  0x6e10421e;       (* arm_EXT Q30 Q16 Q16 64 *)
  0xd1000421;       (* arm_SUB X1 X1 (rvalue (word 1)) *)
  0xb5ffe9e1;       (* arm_CBNZ X1 (word 2096444) *)
  0x3dc02be0;       (* arm_LDR Q0 SP (Immediate_Offset (word 160)) *)
  0x4e284b29;       (* arm_AESE Q9 Q25 *)
  0x4e286929;       (* arm_AESMC Q9 Q9 *)
  0x4e284b4c;       (* arm_AESE Q12 Q26 *)
  0x4e28698c;       (* arm_AESMC Q12 Q12 *)
  0x6e3c1def;       (* arm_EOR_VEC Q15 Q15 Q28 128 *)
  0xa90b5ffc;       (* arm_STP X28 X23 SP (Immediate_Offset (iword (&176))) *)
  0x4e284b49;       (* arm_AESE Q9 Q26 *)
  0x4e286929;       (* arm_AESMC Q9 Q9 *)
  0x3dc014cb;       (* arm_LDR Q11 X6 (Immediate_Offset (word 80)) *)
  0x4e2009f0;       (* arm_REV64_VEC Q16 Q15 8 *)
  0x4e284b6c;       (* arm_AESE Q12 Q27 *)
  0xa8c41c11;       (* arm_LDP X17 X7 X0 (Postimmediate_Offset (iword (&64))) *)
  0x3dc02fed;       (* arm_LDR Q13 SP (Immediate_Offset (word 176)) *)
  0x4e284b69;       (* arm_AESE Q9 Q27 *)
  0x5e180601;       (* arm_DUP_ELEM_SCALAR Q1 Q16 1 64 *)
  0x4e284a40;       (* arm_AESE Q0 Q18 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x0ee5e20e;       (* arm_PMULL_VEC Q14 Q16 Q5 64 *)
  0x6e291d5c;       (* arm_EOR_VEC Q28 Q10 Q9 128 *)
  0x4e284a60;       (* arm_AESE Q0 Q19 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0xca1500e7;       (* arm_EOR X7 X7 X21 *)
  0xca140228;       (* arm_EOR X8 X17 X20 *)
  0x4e200b88;       (* arm_REV64_VEC Q8 Q28 8 *)
  0x4ee5e202;       (* arm_PMULL2_VEC Q2 Q16 Q5 64 *)
  0xa90a1fe8;       (* arm_STP X8 X7 SP (Immediate_Offset (iword (&160))) *)
  0x4e284a80;       (* arm_AESE Q0 Q20 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x2e301c24;       (* arm_EOR_VEC Q4 Q1 Q16 64 *)
  0x0ef1e101;       (* arm_PMULL_VEC Q1 Q8 Q17 64 *)
  0x3dc02bf0;       (* arm_LDR Q16 SP (Immediate_Offset (word 160)) *)
  0x4ef1e103;       (* arm_PMULL2_VEC Q3 Q8 Q17 64 *)
  0x6e2c1dad;       (* arm_EOR_VEC Q13 Q13 Q12 128 *)
  0x0effe085;       (* arm_PMULL_VEC Q5 Q4 Q31 64 *)
  0x6e211dd1;       (* arm_EOR_VEC Q17 Q14 Q1 128 *)
  0x6e231c44;       (* arm_EOR_VEC Q4 Q2 Q3 128 *)
  0x4e284aa0;       (* arm_AESE Q0 Q21 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x3dc00cc1;       (* arm_LDR Q1 X6 (Immediate_Offset (word 48)) *)
  0x4e284ac0;       (* arm_AESE Q0 Q22 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e2009a2;       (* arm_REV64_VEC Q2 Q13 8 *)
  0x3d80044d;       (* arm_STR Q13 X2 (Immediate_Offset (word 16)) *)
  0x4e284ae0;       (* arm_AESE Q0 Q23 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x3d80085c;       (* arm_STR Q28 X2 (Immediate_Offset (word 32)) *)
  0x0ee1e05d;       (* arm_PMULL_VEC Q29 Q2 Q1 64 *)
  0x5e18045c;       (* arm_DUP_ELEM_SCALAR Q28 Q2 1 64 *)
  0x4e284b00;       (* arm_AESE Q0 Q24 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4ee1e04d;       (* arm_PMULL2_VEC Q13 Q2 Q1 64 *)
  0x6e3d1e31;       (* arm_EOR_VEC Q17 Q17 Q29 128 *)
  0x2e221f82;       (* arm_EOR_VEC Q2 Q28 Q2 64 *)
  0x4e284b20;       (* arm_AESE Q0 Q25 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x6e08410a;       (* arm_EXT Q10 Q8 Q8 64 *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x0ee6e05d;       (* arm_PMULL_VEC Q29 Q2 Q6 64 *)
  0x6e281d42;       (* arm_EOR_VEC Q2 Q10 Q8 128 *)
  0x4e284b60;       (* arm_AESE Q0 Q27 *)
  0x3d800c4f;       (* arm_STR Q15 X2 (Immediate_Offset (word 48)) *)
  0x6e201e01;       (* arm_EOR_VEC Q1 Q16 Q0 128 *)
  0x4e200830;       (* arm_REV64_VEC Q16 Q1 8 *)
  0x3c840441;       (* arm_STR Q1 X2 (Postimmediate_Offset (word 64)) *)
  0x6e3e1e0e;       (* arm_EOR_VEC Q14 Q16 Q30 128 *)
  0x6e2d1c8d;       (* arm_EOR_VEC Q13 Q4 Q13 128 *)
  0x4effe044;       (* arm_PMULL2_VEC Q4 Q2 Q31 64 *)
  0x6e0e41c3;       (* arm_EXT Q3 Q14 Q14 64 *)
  0x4eebe1c1;       (* arm_PMULL2_VEC Q1 Q14 Q11 64 *)
  0x6e241cbf;       (* arm_EOR_VEC Q31 Q5 Q4 128 *)
  0x6e2e1c60;       (* arm_EOR_VEC Q0 Q3 Q14 128 *)
  0x0eebe1ce;       (* arm_PMULL_VEC Q14 Q14 Q11 64 *)
  0x6e3d1fe4;       (* arm_EOR_VEC Q4 Q31 Q29 128 *)
  0x4ee6e006;       (* arm_PMULL2_VEC Q6 Q0 Q6 64 *)
  0x6e2e1e2e;       (* arm_EOR_VEC Q14 Q17 Q14 128 *)
  0x6e211da1;       (* arm_EOR_VEC Q1 Q13 Q1 128 *)
  0x6e261c9d;       (* arm_EOR_VEC Q29 Q4 Q6 128 *)
  0x6e211dcd;       (* arm_EOR_VEC Q13 Q14 Q1 128 *)
  0x0ee7e023;       (* arm_PMULL_VEC Q3 Q1 Q7 64 *)
  0x6e014024;       (* arm_EXT Q4 Q1 Q1 64 *)
  0x6e2d1fa1;       (* arm_EOR_VEC Q1 Q29 Q13 128 *)
  0x6e231c91;       (* arm_EOR_VEC Q17 Q4 Q3 128 *)
  0x6e311c23;       (* arm_EOR_VEC Q3 Q1 Q17 128 *)
  0x0ee7e070;       (* arm_PMULL_VEC Q16 Q3 Q7 64 *)
  0x6e034062;       (* arm_EXT Q2 Q3 Q3 64 *)
  0x6e301dce;       (* arm_EOR_VEC Q14 Q14 Q16 128 *)
  0x6e221dd0;       (* arm_EOR_VEC Q16 Q14 Q2 128 *)
  0x6e10421e;       (* arm_EXT Q30 Q16 Q16 64 *)
  0x3dc000cc;       (* arm_LDR Q12 X6 (Immediate_Offset (word 0)) *)
  0x3dc008cd;       (* arm_LDR Q13 X6 (Immediate_Offset (word 32)) *)
  0x3dc004ce;       (* arm_LDR Q14 X6 (Immediate_Offset (word 16)) *)
  0xb40006b0;       (* arm_CBZ X16 (word 212) *)
  0xa8c15c16;       (* arm_LDP X22 X23 X0 (Postimmediate_Offset (iword (&16))) *)
  0x110001ae;       (* arm_ADD W14 W13 (rvalue (word 0)) *)
  0x5ac009ce;       (* arm_REV W14 W14 *)
  0xaa0e818e;       (* arm_ORR X14 X12 (Shiftedreg X14 LSL 32) *)
  0xa90a3beb;       (* arm_STP X11 X14 SP (Immediate_Offset (iword (&160))) *)
  0x3dc02be0;       (* arm_LDR Q0 SP (Immediate_Offset (word 160)) *)
  0x4e284a40;       (* arm_AESE Q0 Q18 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284a60;       (* arm_AESE Q0 Q19 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284a80;       (* arm_AESE Q0 Q20 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284aa0;       (* arm_AESE Q0 Q21 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284ac0;       (* arm_AESE Q0 Q22 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284ae0;       (* arm_AESE Q0 Q23 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b00;       (* arm_AESE Q0 Q24 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b20;       (* arm_AESE Q0 Q25 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b60;       (* arm_AESE Q0 Q27 *)
  0xca1402d6;       (* arm_EOR X22 X22 X20 *)
  0xca1502f7;       (* arm_EOR X23 X23 X21 *)
  0xa90a5ff6;       (* arm_STP X22 X23 SP (Immediate_Offset (iword (&160))) *)
  0x3dc02bfd;       (* arm_LDR Q29 SP (Immediate_Offset (word 160)) *)
  0x6e201fa0;       (* arm_EOR_VEC Q0 Q29 Q0 128 *)
  0x3c810440;       (* arm_STR Q0 X2 (Postimmediate_Offset (word 16)) *)
  0x4e200800;       (* arm_REV64_VEC Q0 Q0 8 *)
  0x6e3e1c00;       (* arm_EOR_VEC Q0 Q0 Q30 128 *)
  0x0eece008;       (* arm_PMULL_VEC Q8 Q0 Q12 64 *)
  0x4eece009;       (* arm_PMULL2_VEC Q9 Q0 Q12 64 *)
  0x5e18040b;       (* arm_DUP_ELEM_SCALAR Q11 Q0 1 64 *)
  0x2e201d6b;       (* arm_EOR_VEC Q11 Q11 Q0 64 *)
  0x0eeee16a;       (* arm_PMULL_VEC Q10 Q11 Q14 64 *)
  0x6e291d00;       (* arm_EOR_VEC Q0 Q8 Q9 128 *)
  0x0ee7e121;       (* arm_PMULL_VEC Q1 Q9 Q7 64 *)
  0x6e094129;       (* arm_EXT Q9 Q9 Q9 64 *)
  0x6e201d4a;       (* arm_EOR_VEC Q10 Q10 Q0 128 *)
  0x6e211d21;       (* arm_EOR_VEC Q1 Q9 Q1 128 *)
  0x6e211d4a;       (* arm_EOR_VEC Q10 Q10 Q1 128 *)
  0x0ee7e149;       (* arm_PMULL_VEC Q9 Q10 Q7 64 *)
  0x6e291d08;       (* arm_EOR_VEC Q8 Q8 Q9 128 *)
  0x6e0a414a;       (* arm_EXT Q10 Q10 Q10 64 *)
  0x6e2a1d1e;       (* arm_EOR_VEC Q30 Q8 Q10 128 *)
  0x6e1e43de;       (* arm_EXT Q30 Q30 Q30 64 *)
  0x110005ad;       (* arm_ADD W13 W13 (rvalue (word 1)) *)
  0xd1000610;       (* arm_SUB X16 X16 (rvalue (word 1)) *)
  0xb5fff9b0;       (* arm_CBNZ X16 (word 2096948) *)
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

let aes128_gcm_enc_tmc = define_trimmed "aes128_gcm_enc_tmc" aes128_gcm_enc_mc;;
let AES128_GCM_ENC_EXEC = ARM_MK_EXEC_RULE aes128_gcm_enc_tmc;;

(* The partial encryptions this kernel carries besides aes7c, and the
   completion of aes10p: aes10p XOR the last round key is the whole AES-128
   keystream block, in lane order. *)
let aes8c = define_aes_partial "aes8c" 8;;
let aes10p = define_aes_prefinal "aes10p" 10;;

let AES10P_COMPLETE = prove
 (`[EL 0 rk; EL 1 rk; EL 2 rk; EL 3 rk; EL 4 rk; EL 5 rk; EL 6 rk;
    EL 7 rk; EL 8 rk; EL 9 rk; EL 10 rk]:(int128)list = rk
   ==> word_xor (aes10p nonce rk c) (word_reversefields 8 (EL 10 rk))
       = word_reversefields 8 (aes128_cipher (ctr_block nonce c) rk)`,
  DISCH_TAC THEN REWRITE_TAC[aes10p] THEN
  GEN_REWRITE_TAC LAND_CONV
   [INST ((`word_reversefields 8 (ctr_block nonce c):int128`,`plaintext:int128`) ::
          map (fun j -> (parse_term(Printf.sprintf "word_reversefields 8 (EL %d rk):int128" j),
                         mk_var("rk"^string_of_int j,`:int128`))) (0--10))
         AES128_CIPHER_RECONSTRUCT] THEN
  REWRITE_TAC[WORD_REVERSEFIELDS_REVERSEFIELDS; MAP] THEN ASM_REWRITE_TAC[]);;

(* The keystream folds of the GHASH (Q30) closers.  In the GHASH terms the
   keystreams of a group occur as aes10p, as further rounds on aes7c or aes8c,
   as the fully expanded rounds on the counter block, and joined from scalar
   lanes.  AES10P_VIA_AES7C and AES10P_VIA_AES8C bring the partial forms to
   aes10p, and KEYSTREAM_FOLD turns aes10p XOR (input block XOR the last round
   key) into the cipher of the counter block XOR the input block, which
   CT_TO_NCB folds to nist_cipher_block: counter j + c goes with
   aes_ctr_block j and inblock j. *)
let AES10P_VIA_AES7C = AES_PREFINAL_VIA_PARTIAL aes10p 10 aes7c 7;;
let AES10P_VIA_AES8C = AES_PREFINAL_VIA_PARTIAL aes10p 10 aes8c 8;;
let KEYSTREAM_FOLD = prove
 (`[EL 0 rk; EL 1 rk; EL 2 rk; EL 3 rk; EL 4 rk; EL 5 rk; EL 6 rk;
    EL 7 rk; EL 8 rk; EL 9 rk; EL 10 rk]:(int128)list = rk
   ==> word_xor (aes10p nonce rk c) (word_xor inb (word_reversefields 8 (EL 10 rk)))
       = word_xor (word_reversefields 8 (aes128_cipher (ctr_block nonce c) rk)) inb`,
  DISCH_THEN(fun th -> MP_TAC(MATCH_MP AES10P_COMPLETE th)) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN CONV_TAC WORD_BITWISE_RULE);;

(* ------------------------------------------------------------------------- *)
(* The loop invariant and the body leg BODYLEG: pc + 0x1ec -> pc + 0x4b0.    *)
(* ------------------------------------------------------------------------- *)

(* swp_inv i holds at the loop head pc + 0x1ec at the start of iteration i,
   which completes the group of blocks 4i..4i+3.  Besides the values that
   stay fixed (round keys rk0..rk9 in Q18..Q27 and the last round key rk10 in
   X20/X21, the reduction constant Q7, the IV halves X11/X12, the key powers
   in Q5, Q31, Q17 and Q6, the byte and block counts) it records: X0/X2
   advanced by 64*i and X1 = word (loop_count - (i+1)); the lane-order
   counter blocks of blocks 4i and 4i+1 at sp+160 and sp+176, and X13, the
   counter of block 4i+4; the partial encryptions aes8c of block 4i+1 (Q12),
   aes7c of block 4i+2 (Q9) and aes10p of block 4i+3 (Q28); the input blocks
   4i+1, 4i+2 and 4i+3 XOR rk10, in X23/X28, in Q10 and at sp+192, and in Q15
   and at sp+208; Q30, the byteswapped GHASH tag of the first 4i ciphertext
   blocks; and the first 4i output blocks.  Here rk10 is the lane-order last
   round key word_reversefields 8 (EL 10 rk). *)
let swp_inv = `\(i:num) s.
    read X0 s = word_add in_p (word (64 * i)) /\
    read X2 s = word_add out_p (word (64 * i)) /\
    read X3 s = tag_p /\ read X4 s = ivec_p /\ read X6 s = htable_p /\ read SP s = stackpointer /\
    read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
    read (memory :> bytes128 ivec_p) s = word_reversefields 8 (ctr_block nonce c) /\
    read (memory :> bytes128 (word_add stackpointer (word 160))) s =
        word_reversefields 8 (ctr_block nonce (4*i+c)) /\
    read Q18 s = word_reversefields 8 (EL 0 rk) /\ read Q19 s = word_reversefields 8 (EL 1 rk) /\
    read Q20 s = word_reversefields 8 (EL 2 rk) /\ read Q21 s = word_reversefields 8 (EL 3 rk) /\
    read Q22 s = word_reversefields 8 (EL 4 rk) /\ read Q23 s = word_reversefields 8 (EL 5 rk) /\
    read Q24 s = word_reversefields 8 (EL 6 rk) /\ read Q25 s = word_reversefields 8 (EL 7 rk) /\
    read Q26 s = word_reversefields 8 (EL 8 rk) /\ read Q27 s = word_reversefields 8 (EL 9 rk) /\
    read X20 s = word_subword (word_reversefields 8 (EL 10 rk):int128) (0,64):int64 /\
    read X21 s = word_subword (word_reversefields 8 (EL 10 rk):int128) (64,64):int64 /\
    read X11 s = word_subword (word_reversefields 8 (ctr_block nonce c):int128) (0,64):int64 /\
    read X12 s = word_zx (word_zx (word_subword
        (word_reversefields 8 (ctr_block nonce c):int128) (64,64):int64):int32):int64 /\
    read X13 s = word_zx (word (4 * i + c + 4):int32):int64 /\
    read Q7 s = word 13979173243358019584 /\
    read Q9  s = aes7c nonce rk (4*i+c+2) /\
    read Q12 s = aes8c nonce rk (4*i+c+1) /\
    read Q28 s = aes10p nonce rk (4*i+c+3) /\
    read Q30 s = byteswap128
        (nist_ghash (aes128_cipher (word 0) rk) tag0
           (list_of_seq (nist_cipher_block aes128_cipher c nonce rk inblock) (4 * i))) /\
    read X1 s = word (loop_count - (i+1)) /\ read X15 s = word(len_bits DIV 8) /\ read X16 s = word loop_remain /\
    htable_mem_4 (ghash_twist (aes128_cipher (word 0) rk)) htable_p s /\
    (!j. j < nblocks ==> read (memory :> bytes128 (word_add in_p (word(16*j)))) s = inblock j) /\
    (!j. j < 4 * i ==> read (memory :> bytes128 (word_add out_p (word(16*j)))) s =
             word_xor (aes_ctr_block aes128_cipher c nonce rk j) (inblock j)) /\
    read Q5 s = byteswap128(h_power (ghash_twist (aes128_cipher (word 0) rk)) 0) /\
    read Q31 s = word_join (karatsuba_mid(h_power (ghash_twist (aes128_cipher (word 0) rk)) 1):int64)
                           (karatsuba_mid(h_power (ghash_twist (aes128_cipher (word 0) rk)) 0):int64) /\
    read Q17 s = byteswap128(h_power (ghash_twist (aes128_cipher (word 0) rk)) 1) /\
    read Q6 s = word_join (karatsuba_mid(h_power (ghash_twist (aes128_cipher (word 0) rk)) 3):int64)
                          (karatsuba_mid(h_power (ghash_twist (aes128_cipher (word 0) rk)) 2):int64) /\
    read (memory :> bytes128 (word_add stackpointer (word 176))) s = word_reversefields 8 (ctr_block nonce (4*i+c+1)) /\
    read (memory :> bytes128 (word_add stackpointer (word 192))) s = word_xor (inblock (4*i+2)) (word_reversefields 8 (EL 10 rk)) /\
    read (memory :> bytes128 (word_add stackpointer (word 208))) s = word_xor (inblock (4*i+3)) (word_reversefields 8 (EL 10 rk)) /\
    read Q10 s = word_xor (inblock (4*i+2)) (word_reversefields 8 (EL 10 rk)) /\
    read Q15 s = word_xor (inblock (4*i+3)) (word_reversefields 8 (EL 10 rk)) /\
    read X23 s = word_subword (word_xor (inblock (4*i+1)) (word_reversefields 8 (EL 10 rk)):int128) (64,64):int64 /\
    read X28 s = word_subword (word_xor (inblock (4*i+1)) (word_reversefields 8 (EL 10 rk)):int128) (0,64):int64`;;

(* Leg pre/postconditions over this kernel's code (see mk_leg_state). *)
let leg_state = mk_leg_state `aes128_gcm_enc_tmc`;;

(* The goal of the body leg for an invariant inv: under the hypotheses
   (round-key list, block counts, 2 <= loop_count, i < loop_count - 1, size
   bound, stack alignment, nonoverlapping), inv i at pc + 0x1ec leads to
   inv (i+1) at pc + 0x4b0. *)
let mk_body_goal inv =
  mk_imp(`([EL 0 rk; EL 1 rk; EL 2 rk; EL 3 rk; EL 4 rk; EL 5 rk; EL 6 rk;
      EL 7 rk; EL 8 rk; EL 9 rk; EL 10 rk]:(int128)list = rk) /\
     len_bits DIV 128 = nblocks /\ nblocks DIV 4 = loop_count /\ nblocks MOD 4 = loop_remain /\
     2 <= loop_count /\ i < loop_count - 1 /\ 16 * nblocks < 2 EXP 64 /\ aligned 16 (stackpointer:int64) /\
     nonoverlapping (out_p:int64,16 * nblocks) (word pc:int64,1856) /\
     nonoverlapping (out_p:int64,16 * nblocks) (in_p:int64,16 * nblocks) /\
     nonoverlapping (out_p:int64,16 * nblocks) (htable_p:int64,96) /\
     nonoverlapping (out_p:int64,16 * nblocks) (tag_p:int64,16) /\
     nonoverlapping (out_p:int64,16 * nblocks) (ivec_p:int64,16) /\
     nonoverlapping (out_p:int64,16*nblocks) (word_add stackpointer (word 160):int64,64) /\
     nonoverlapping (tag_p:int64,16) (word pc:int64,1856) /\
     nonoverlapping (tag_p:int64,16) (in_p:int64,16*nblocks) /\
     nonoverlapping (tag_p:int64,16) (htable_p:int64,96) /\
     nonoverlapping (tag_p:int64,16) (word_add stackpointer (word 160):int64,64) /\
     nonoverlapping (ivec_p:int64,16) (word pc:int64,1856) /\
     nonoverlapping (ivec_p:int64,16) (in_p:int64,16*nblocks) /\
     nonoverlapping (ivec_p:int64,16) (htable_p:int64,96) /\
     nonoverlapping (ivec_p:int64,16) (word_add stackpointer (word 160):int64,64) /\
     nonoverlapping (tag_p:int64,16) (ivec_p:int64,16) /\
     nonoverlapping (word_add stackpointer (word 160):int64,64) (word pc:int64,1856) /\
     nonoverlapping (word_add stackpointer (word 160):int64,64) (in_p:int64,16*nblocks) /\
     nonoverlapping (word_add stackpointer (word 160):int64,64) (htable_p:int64,96)`,
   list_mk_icomb "ensures" [`arm`;
     (* Pre- and postcondition as flat, beta-reduced conjunctions (leg_state),
        so that the leg closes the obligations of ENSURES_SEQUENCE_TAC and
        ENSURES_WHILE_UP_TAC by MATCH_MP_TAC. *)
     leg_state inv `0x1ec` `i:num` ;
     leg_state inv `0x4b0` `i+1` ;
     (* The frame also has the callee-saved registers the body uses, which
        the prologue saves and the epilogue restores: X19..X30 and all of
        Q8..Q15 (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI has only their
        top halves). *)
     `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
      MAYCHANGE [X19; X20; X21; X22; X23; X24; X25; X26; X27; X28; X29; X30] ,,
      MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
      MAYCHANGE [memory :> bytes(out_p:int64, 16 * nblocks)] ,,
      MAYCHANGE [memory :> bytes(word_add stackpointer (word 160):int64, 64)] ,, MAYCHANGE [events]`]);;

let body_goal = mk_body_goal swp_inv;;

(* The (step, offset) pairs of the stp stores into the stack slots, after
   which MERGE_CTR128_TAC derives the 128-bit read of the slot. *)
let merges = [(10,176);(28,192);(31,176);(41,160);(50,160);(63,208);(81,192);(95,208)];;

(* The registers whose latest value the stepper keeps: the vector registers
   of the GHASH computation and the scalar counter and input lanes. *)
let REDSETX = ["Q0";"Q1";"Q2";"Q3";"Q4";"Q5";"Q6";"Q8";"Q13";"Q14";"Q16";"Q17";"Q28";"Q29";"Q30";"Q31";
               "X7";"X8";"X11";"X13";"X14";"X17";"X23";"X24";"X25";"X26";"X28";"X30"];;
(* The stepper keeps the reads at in_p, the input-split facts about s0. *)
let enc_anchors = [`in_p:int64`];;

(* Scalar registers whose loop-head values GHOST_INTRO_TAC names ghost_<reg>,
   so that terms in them stay meaningful when the stepper discards the facts
   about old states.  X23 and X28 hold the lanes of block 4i+1 XOR rk10,
   stored to sp+176 at 0x210 and reloaded into Q13 at 0x238; with their
   invariant conjuncts GHOST_INTRO_TAC gives the equations
   ghost_X23 = word_subword ... that the keystream fold of block 4i+1 uses. *)
let ghost_lanes = ["X7";"X8";"X17";"X22";"X23";"X24";"X25";"X26";"X28";"X29";"X30";"X10";"X14";"X19";"X27"];;

(* Split the input facts of blocks 4i..4i+7 into 64-bit halves.  The body
   loads block 4i (ldp x17,x7,[x0],#64) and, after that post-increment,
   blocks 4i+5..4i+7 of the next group (ldp [x0,#16], [x0,#32], [x0,#48]),
   which become the X23/X28, Q10/sp+192 and Q15/sp+208 values of
   swp_inv (i+1); blocks 4i+1..4i+3 come in those values of swp_inv i.  The
   bound 4i+7 < nblocks follows from i < loop_count - 1. *)
let INPUT_SPLIT_TAC =
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
      [UNDISCH_TAC `nblocks DIV 4 = loop_count` THEN UNDISCH_TAC `i < loop_count - 1` THEN
       UNDISCH_TAC `2 <= loop_count` THEN ARITH_TAC; ALL_TAC] THEN
     REPEAT CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE `16 * (4*i+0) = 64*i`; ARITH_RULE `16 * (4*i+1) = 64*i+16`;
     ARITH_RULE `16 * (4*i+2) = 64*i+32`; ARITH_RULE `16 * (4*i+3) = 64*i+48`;
     ARITH_RULE `16 * (4*i+4) = 64*i+64`; ARITH_RULE `16 * (4*i+5) = 64*i+80`;
     ARITH_RULE `16 * (4*i+6) = 64*i+96`; ARITH_RULE `16 * (4*i+7) = 64*i+112`]) THEN
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o CONV_RULE SPLIT_INPUT_CONV o
     check (fun th -> let c = concl th in is_eq c && free_in `in_p:int64` (lhs c) &&
       can (find_term (fun t -> is_const t && fst(dest_const t) = "bytes128")) (lhs c))));;

(* The body setup: name the loop-head scalar registers (ghost_lanes), start
   the simulation, split the input blocks and abbreviate the remaining reads
   of s0 as variables init_k.  Every value computed in the body is then an
   expression in those variables, which the stepper does not discard and
   which keeps the GHASH terms small. *)
let setup_tac =
  STRIP_TAC THEN REWRITE_TAC[fst AES128_GCM_ENC_EXEC] THEN
  MAP_EVERY (fun rn -> GHOST_INTRO_TAC (mk_var("ghost_"^rn,`:int64`)) (parse_term("read "^rn))) ghost_lanes THEN
  ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV BETA_CONV)) THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_4]) THEN REWRITE_TAC[htable_mem_4] THEN
  INPUT_SPLIT_TAC THEN
  (* Abbreviate the reads of s0 that do not mention j, except those of input
     memory: the input-split facts read (bytes64 ...) s0 = word_subword
     (inblock ..) .. are what the prefetch loads (reading s39, s55 and s66)
     resolve through, and abbreviating them would leave those loads without
     a matching fact. *)
  (fun (asl,w) ->
    let jv = `j:num` in
    let reads0 = setify(flat(map (fun (_,th) -> find_terms (fun t -> try let h,a=strip_comb t in
         fst(dest_const h)="read" && length a=2 && string_of_term(hd(tl a))="s0" with _->false) (concl th)) asl)) in
    let toab = filter (fun t -> not(free_in jv t) && not(free_in `in_p:int64` t)
                              && string_of_term t <> "read PC s0") reads0 in
    (EVERY (List.mapi (fun k t -> ABBREV_TAC (mk_eq(mk_var(Printf.sprintf "init_%d" k, type_of t), t))) toab)) (asl,w));;

(* Stepping the body: SWP_STEPS_TAC keeps the latest fact for each register
   in REDSETX, so the GHASH registers survive the discarding of old states
   (Q30 is last written at step 176).  The prefetch loads of blocks
   4i+5..4i+7 address memory relative to x0 = in_p + 64i + 64; the address
   normalization after each step (NORMALIZE_RELATIVE_ADDRESS_CONV, then
   IN_P_ADDR_FOLD_CONV) brings those addresses to the form of the input-split
   facts, and is applied once more before the final state. *)
let step_body_tac =
  setup_tac THEN
  SWP_STEPS_TAC enc_anchors [] REDSETX AES128_GCM_ENC_EXEC (K ALL_TAC) merges (1--177) THEN
  RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV THENC
                           ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV THENC
                           IN_P_ADDR_FOLD_CONV)) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];;

(* Closers for the conjuncts of swp_inv (i+1) about X0, X2, the counter block
   at sp+160, X13 and the partial encryptions aes7c (Q9), aes8c (Q12) and
   aes10p (Q28): pointer arithmetic, and mk_cbv for the counter blocks. *)
let closers_0_6 =
  [ REWRITE_TAC[ARITH_RULE `64*(i+1)=64*i+64`; LEFT_ADD_DISTRIB] THEN CONV_TAC WORD_RULE;
    REWRITE_TAC[ARITH_RULE `64*(i+1)=64*i+64`; LEFT_ADD_DISTRIB] THEN CONV_TAC WORD_RULE;
    REWRITE_TAC[ZXNEST4] THEN
      SUBGOAL_THEN `word (4*i+c+4):int32 = word(4*(i+1)+c)` SUBST1_TAC THENL
       [AP_TERM_TAC THEN ARITH_TAC; ALL_TAC] THEN ACCEPT_TAC (mk_cbv `4*(i+1)+c`);
    REWRITE_TAC[ZX_COUNTER_UD] THEN AP_TERM_TAC THEN REWRITE_TAC[GSYM WORD_ADD] THEN AP_TERM_TAC THEN ARITH_TAC;
    REWRITE_TAC[aes7c] THEN REPEAT(AP_TERM_TAC ORELSE AP_THM_TAC) THEN REWRITE_TAC[ZXNEST4;ZX_COUNTER_UD] THEN
      SUBGOAL_THEN `word_add (word (4*i+c+4):int32) (word 2) = word(4*(i+1)+c+2):int32` SUBST1_TAC THENL
       [REWRITE_TAC[GSYM WORD_ADD] THEN AP_TERM_TAC THEN ARITH_TAC; ALL_TAC] THEN ACCEPT_TAC (mk_cbv `4*(i+1)+c+2`);
    REWRITE_TAC[aes8c] THEN REPEAT(AP_TERM_TAC ORELSE AP_THM_TAC) THEN REWRITE_TAC[ZXNEST4;ZX_COUNTER_UD] THEN
      SUBGOAL_THEN `word_add (word (4*i+c+4):int32) (word 1) = word(4*(i+1)+c+1):int32` SUBST1_TAC THENL
       [REWRITE_TAC[GSYM WORD_ADD] THEN AP_TERM_TAC THEN ARITH_TAC; ALL_TAC] THEN ACCEPT_TAC (mk_cbv `4*(i+1)+c+1`);
    REWRITE_TAC[aes10p] THEN REPEAT(AP_TERM_TAC ORELSE AP_THM_TAC) THEN REWRITE_TAC[ZXNEST4;ZX_COUNTER_UD] THEN
      SUBGOAL_THEN `word_add (word (4*i+c+4):int32) (word 3) = word(4*(i+1)+c+3):int32` SUBST1_TAC THENL
       [REWRITE_TAC[GSYM WORD_ADD] THEN AP_TERM_TAC THEN ARITH_TAC; ALL_TAC] THEN ACCEPT_TAC (mk_cbv `4*(i+1)+c+3`)];;

(* The first part of the Q30 (GHASH tag) closer: fold the ghost pins of X23
   and X28 and the keystreams of the four blocks of the group to
   nist_cipher_block, leaving the Karatsuba product terms over the four
   ciphertext blocks.  ksf is KEYSTREAM_FOLD for the round-key list
   hypothesis among the assumptions. *)
let collapse_q30 : tactic =
  fun (asl,w) ->
    let rkth = try snd(find (fun (_,th) -> concl th =
        `[EL 0 rk; EL 1 rk; EL 2 rk; EL 3 rk; EL 4 rk; EL 5 rk; EL 6 rk;
          EL 7 rk; EL 8 rk; EL 9 rk; EL 10 rk]:(int128)list = rk`) asl)
      with _ -> failwith "collapse_q30: rk-list hyp not found" in
    let ksf = MATCH_MP KEYSTREAM_FOLD rkth in
    let ghostpins = List.filter_map (fun (_,th) ->
      let c = concl th in
      if is_eq c then (match lhs c with
        | Var(nm,_) when String.length nm>=6 && String.sub nm 0 6="ghost_"
            && can (find_term (fun t -> try fst(dest_const(fst(strip_comb t)))="inblock" with _->false)) (rhs c)
          -> Some th | _ -> None) else None) asl in
    (
    (* (0) Write the tag index 4*(i+1) as 4*i+4, as the final unfolding of
       close_goal7 by SUC and GHASH_ACC_APPEND expects. *)
    REWRITE_TAC[ARITH_RULE `4*(i+1) = 4*i+4`] THEN
    (* (1) Fold the X23/X28 ghost pins and recombine their join into
       word_xor (inblock (4i+1)) rk10. *)
    REWRITE_TAC(JOIN_SUBWORD_RECOMBINE :: ghostpins) THEN
    (* (2) The goal stays wrapped in byteswap128: the reconstruction in
       close_goal7 splits it once itself, and the keystream folds below
       reach inside the wrapper.
       (3) Bring the four keystreams to aes10p, join the lanes, apply ksf,
       write the counters as (4*i+k)+c and fold with CT_TO_NCB. *)
    REWRITE_TAC[GSYM AES10P_VIA_AES7C; GSYM AES10P_VIA_AES8C; GSYM aes10p] THEN
    REWRITE_TAC[JOIN_XOR_LANES] THEN
    REWRITE_TAC[ksf] THEN
    REWRITE_TAC[ARITH_RULE `4*i+c+3 = (4*i+3)+c`; ARITH_RULE `4*i+c+2 = (4*i+2)+c`;
                ARITH_RULE `4*i+c+1 = (4*i+1)+c`; ARITH_RULE `4*i+0 = 4*i`] THEN
    REWRITE_TAC[CT_TO_NCB] THEN
    (* (4) Normalize the block indices to 4*i+k. *)
    REWRITE_TAC[ARITH_RULE `(4*i+0)+2 = 4*i+2`; ARITH_RULE `(4*i+1)+2 = 4*i+3`;
                ARITH_RULE `(4*i+2)+2 = 4*i+4`; ARITH_RULE `(4*i+3)+2 = 4*i+5`;
                ARITH_RULE `4*i+0 = 4*i`]
    ) (asl,w);;

(* The Q30 (GHASH tag) closer of the body: after collapse_q30, reconstruct
   the GHASH update of the four blocks, from the tag of 4*i blocks to the
   tag of 4*(i+1) blocks. *)
let close_goal7 : tactic =
  fun (asl,w) ->
    (
    collapse_q30 THEN
    (* (5) The goal is word_subword (word_join ...) (64,128) =
       byteswap128 (nist_ghash ... (4*i+4)).  Split the byteswap once,
       abbreviate the tag so far (sofar), the four ciphertext blocks and the
       key powers, fold the reduction with RECONSTRUCT_POLYVAL_REDUCE_G2 and
       the products with PMUL_KARATSUBA_JOIN_ALT and KARATSUBA_JOIN_XOR4,
       then match GHASH_POLYVAL_ACC_BATCHED. *)
    REWRITE_TAC[WORD_SUBWORD_REVERSEFIELDS] THEN
    SIMP_TAC[WORD_JOIN_COMBINE_LEMMA; ARITH] THEN
    REWRITE_TAC[WORD_SUBWORD_XOR] THEN
    REWRITE_TAC[WORD_SUBWORD_BYTESWAP128] THEN
    CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
    REWRITE_TAC[WORD_SUBWORD_XOR] THEN
    CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
    REWRITE_TAC [byteswap128; WORD_BLAST
      `word_subword((word_join:int128->int128->int256) h l) (64,128):int128 =
       word_join (word_subword h (0,64):int64) (word_subword l (64,64):int64)`] THEN
    MATCH_MP_TAC(BITBLAST_RULE
     `x:int128 = y
      ==> word_join (word_subword x (0,64):int64) (word_subword x (64,64):int64):int128 =
          word_join (word_subword y (0,64):int64) (word_subword y (64,64):int64):int128`) THEN
    MAP_EVERY ABBREV_TAC
     [`sofar = (nist_ghash (aes128_cipher (word 0) rk) tag0
                 (list_of_seq (nist_cipher_block aes128_cipher c nonce rk inblock) (4 * i)))`;
      `cipherblock_0 = nist_cipher_block aes128_cipher c nonce rk inblock (4 * i)`;
      `cipherblock_1 = nist_cipher_block aes128_cipher c nonce rk inblock (4 * i + 1)`;
      `cipherblock_2 = nist_cipher_block aes128_cipher c nonce rk inblock (4 * i + 2)`;
      `cipherblock_3 = nist_cipher_block aes128_cipher c nonce rk inblock (4 * i + 3)`;
      `h0 = h_power (ghash_twist (aes128_cipher (word 0) rk)) 0`;
      `h1 = h_power (ghash_twist (aes128_cipher (word 0) rk)) 1`;
      `h2 = h_power (ghash_twist (aes128_cipher (word 0) rk)) 2`;
      `h3 = h_power (ghash_twist (aes128_cipher (word 0) rk)) 3`] THEN
    REWRITE_TAC[GSYM WORD_SUBWORD_XOR] THEN
    REWRITE_TAC[RECONSTRUCT_POLYVAL_REDUCE_G2] THEN
    TRANS_TAC EQ_TRANS
     `polyval_reduce_prop3
          (word_xor (word_pmul (cipherblock_3:int128) (h0:int128))
          (word_xor (word_pmul (cipherblock_2:int128) (h1:int128))
          (word_xor (word_pmul (cipherblock_1:int128) (h2:int128))
          (word_pmul (word_xor (sofar:int128) cipherblock_0) (h3:int128)))))` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[PMUL_KARATSUBA_JOIN_ALT] THEN
      REWRITE_TAC[byteswap128; WORD_SUBWORD_XOR] THEN
      CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
      REWRITE_TAC[karatsuba_mid] THEN ASM_REWRITE_TAC[] THEN
      REPEAT(LET_TAC THEN ASM_REWRITE_TAC[]) THEN
      ONCE_REWRITE_TAC[MESON[WORD_XOR_SYM]
       `word_pmul (word_xor a b) (word_xor c d) = word_pmul (word_xor b a) (word_xor c d)`] THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[POLYVAL_REDUCE_G2] THEN ASM_REWRITE_TAC[] THEN
      MAP_EVERY EXPAND_TAC ["ks"; "ks'"; "ks''"; "ks'''"] THEN
      CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
      AP_TERM_TAC THEN REWRITE_TAC[GSYM karatsuba_join] THEN MATCH_ACCEPT_TAC KARATSUBA_JOIN_XOR4;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`ghash_twist (aes128_cipher (word 0) rk)`;
                   `[cipherblock_1;cipherblock_2;cipherblock_3]:(int128)list`;
                   `sofar:int128`; `cipherblock_0:int128`]
                  GHASH_POLYVAL_ACC_BATCHED) THEN
    REWRITE_TAC[LENGTH; ghash_wide] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(MESON[]
     `y' = y /\ x' = x ==> x = y ==> y' = x'`) THEN
    CONJ_TAC THENL [AP_TERM_TAC THEN CONV_TAC WORD_BITWISE_RULE; ALL_TAC] THEN
    EXPAND_TAC "sofar" THEN
    REWRITE_TAC[NIST_GHASH_IS_POLYVAL] THEN
    REWRITE_TAC[ARITH_RULE `4*i+4 = SUC(SUC(SUC(SUC(4*i))))`] THEN
    REWRITE_TAC[list_of_seq] THEN REWRITE_TAC[GSYM APPEND_ASSOC] THEN
    REWRITE_TAC[APPEND] THEN
    REWRITE_TAC[GHASH_ACC_APPEND] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ADD1; GSYM ADD_ASSOC] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[GSYM NIST_GHASH_IS_POLYVAL]
    ) (asl,w);;


(* The X1 conjunct of swp_inv (i+1): word_sub (word (loop_count - (i+1)))
   (word 1) = word (loop_count - ((i+1)+1)), from
   loop_count - (i+2) = (loop_count - (i+1)) - 1 and 1 <= loop_count - (i+1),
   which follow from i < loop_count - 1. *)
let close_goal8 : tactic =
  fun (asl,w) ->
    let bnds = List.filter_map (fun (_,th) -> let c = concl th in
      if c = `2 <= loop_count` || c = `i < loop_count - 2` || c = `i < loop_count - 1` then Some th else None) asl in
    (MAP_EVERY (fun th -> ASSUME_TAC th) bnds THEN
     SUBGOAL_THEN `loop_count - ((i+1)+1) = (loop_count - (i+1)) - 1 /\ 1 <= loop_count - (i+1)` STRIP_ASSUME_TAC THENL
      [MAP_EVERY (fun th -> MP_TAC th) bnds THEN ARITH_TAC; ALL_TAC] THEN
     ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[WORD_SUB; VAL_WORD_1] THEN
     REWRITE_TAC[GSYM VAL_WORD_1] THEN AP_TERM_TAC THEN
     MAP_EVERY (fun th -> MP_TAC th) bnds THEN ARITH_TAC) (asl,w);;

(* Closers for the carried values of swp_inv (i+1): word identities after
   the index shift 4*(i+1)+k = 4*i+(k+4). *)

(* The counter block at sp+176, ctr_block nonce (4*(i+1)+c+1), from the
   counter register by mk_cbv. *)
let close_ctr176 : tactic =
  REWRITE_TAC[ZXNEST4;ZX_COUNTER_UD] THEN
  SUBGOAL_THEN `word_add (word (4*i+c+4):int32) (word 1) = word(4*(i+1)+c+1):int32` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM WORD_ADD] THEN AP_TERM_TAC THEN ARITH_TAC; ALL_TAC] THEN
  ACCEPT_TAC (mk_cbv `4*(i+1)+c+1`);;
(* Q10, Q15 and the slots at sp+192 and sp+208: the join of the XORed scalar
   lanes is word_xor (inblock (4*(i+1)+k)) rk10. *)
let close_lanejoin : tactic =
  REWRITE_TAC[ARITH_RULE `4*(i+1)+0 = 4*i+4`; ARITH_RULE `4*(i+1)+1 = 4*i+5`;
              ARITH_RULE `4*(i+1)+2 = 4*i+6`; ARITH_RULE `4*(i+1)+3 = 4*i+7`] THEN
  REWRITE_TAC[ARITH_RULE `4*(i+1)+c = 4*i+c+4`; ARITH_RULE `4*(i+1)+c+1 = 4*i+c+5`] THEN
  REWRITE_TAC[JOIN_XOR_LANES];;
(* X23 and X28: the XOR of the lanes is the corresponding lane of
   word_xor (inblock (4*(i+1)+1)) rk10. *)
let close_subwordpin : tactic =
  REWRITE_TAC[ARITH_RULE `4*(i+1)+0 = 4*i+4`; ARITH_RULE `4*(i+1)+1 = 4*i+5`;
              ARITH_RULE `4*(i+1)+2 = 4*i+6`; ARITH_RULE `4*(i+1)+3 = 4*i+7`] THEN CONV_TAC WORD_BLAST;;

(* The keystream identities of the output blocks: each
     word_xor <keystream> (input XOR rk10) =
     word_xor (word_reversefields 8 (aes128_cipher (ctr_block ..) rk))
              (inblock ..).
   Recombine the lanes of block 4i+1, bring the partial encryptions to aes10p
   and apply KEYSTREAM_FOLD; the right-hand sides are already in
   aes128_cipher form, not nist_cipher_block. *)
let close_ksfold : tactic =
  fun (asl,w) ->
    let rkth = try snd(find (fun (_,th) -> concl th =
        `[EL 0 rk; EL 1 rk; EL 2 rk; EL 3 rk; EL 4 rk; EL 5 rk; EL 6 rk;
          EL 7 rk; EL 8 rk; EL 9 rk; EL 10 rk]:(int128)list = rk`) asl)
      with _ -> failwith "close_ksfold: no rk-hyp" in
    (REPEAT CONJ_TAC THEN
     REWRITE_TAC[JOIN_SUBWORD_RECOMBINE] THEN
     REWRITE_TAC[GSYM AES10P_VIA_AES7C; GSYM AES10P_VIA_AES8C] THEN
     REWRITE_TAC[MATCH_MP KEYSTREAM_FOLD rkth]) (asl,w);;

(* The output conjunct of swp_inv (i+1), for j < 4*(i+1): the blocks
   j < 4*i come from the invariant, and the four blocks 4*i..4*i+3 stored in
   this iteration reconstruct to word_xor (aes_ctr_block ... j) (inblock j). *)
let close_goal9 : tactic =
  fun (asl,w) ->
    let rkth = try snd(find (fun (_,th) -> concl th =
        `[EL 0 rk; EL 1 rk; EL 2 rk; EL 3 rk; EL 4 rk; EL 5 rk; EL 6 rk;
          EL 7 rk; EL 8 rk; EL 9 rk; EL 10 rk]:(int128)list = rk`) asl)
      with _ -> failwith "close_goal9: no rk-hyp" in
    (REWRITE_TAC[ARITH_RULE `j < 4 * (i+1) <=>
                          j < 4 * i \/ j = 4*i+0 \/ j = 4*i+1 \/ j = 4*i+2 \/ j = 4*i+3`] THEN
     ASM_REWRITE_TAC[TAUT `p \/ q ==> r <=> (p ==> r) /\ (q ==> r)`] THEN
     REWRITE_TAC[FORALL_AND_THM; FORALL_UNWIND_THM2] THEN
     REWRITE_TAC[ARITH_RULE `16 * (4*i+0) = 64*i`; ARITH_RULE `16 * (4*i+1) = 64*i+16`;
        ARITH_RULE `16 * (4*i+2) = 64*i+32`; ARITH_RULE `16 * (4*i+3) = 64*i+48`] THEN
     ASM_REWRITE_TAC[] THEN
     REWRITE_TAC[CTR_BLOCK_BUILD_INSERT] THEN
     REWRITE_TAC[SCALAR_RK_RECONSTRUCT] THEN
     REWRITE_TAC[XOR_AES128_CIPHER_RECONSTRUCT] THEN
     ASM_REWRITE_TAC[MAP; WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
     REWRITE_TAC[aes_ctr_block] THEN
     REWRITE_TAC[ARITH_RULE `4 * i + c + 3 = (4 * i + 3) + c`;
                 ARITH_RULE `4 * i + c + 2 = (4 * i + 2) + c`;
                 ARITH_RULE `4 * i + c + 1 = (4 * i + 1) + c`;
                 ARITH_RULE `4 * i + 0 = 4 * i`] THEN ASM_REWRITE_TAC[] THEN
     (* The reconstruction leaves keystream identities; fold them as
        close_ksfold does. *)
     REPEAT CONJ_TAC THEN
     REWRITE_TAC[JOIN_SUBWORD_RECOMBINE] THEN
     REWRITE_TAC[GSYM AES10P_VIA_AES7C; GSYM AES10P_VIA_AES8C] THEN
     REWRITE_TAC[MATCH_MP KEYSTREAM_FOLD rkth] THEN
     REWRITE_TAC[ARITH_RULE `64 * (i + 1) = 64 * i + 64`]) (asl,w);;

(* The frame conjunct, <declared frame> s0 s177 in the body.  The stepper
   leaves several MAYCHANGE assumptions over various pairs of states, so each
   is tried in turn: weaken it along subsumption (pth) and check with
   SUBSUMED_MAYCHANGE_TAC, after expanding
   MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI so that the register lists can
   be compared; the cumulative one, from s0 to the final state, succeeds.
   The tactic is shared with the fill and REDUCELAST.  It first records the
   bounds 4*i+3 < nblocks (body) and 8 <= nblocks (fill), when they follow,
   for the containment of the output stores in the frame. *)
let close_goal10 : tactic =
  fun (asl,w) ->
    let is_mc c = try can(find_term(fun x->match x with Const("MAYCHANGE",_)->true|_->false)) c with _->false in
    let pth = prove(`R s s' ==> R subsumed R' ==> R' s s'`, REWRITE_TAC[subsumed] THEN MESON_TAC[]) in
    (TRY(SUBGOAL_THEN `4*i+3 < nblocks` ASSUME_TAC THENL
      [MAP_EVERY (fun t -> TRY(UNDISCH_TAC t))
         [`nblocks DIV 4 = loop_count`; `i < loop_count - 1`; `i < loop_count - 2`; `2 <= loop_count`] THEN ARITH_TAC;
       ALL_TAC]) THEN
     TRY(SUBGOAL_THEN `8 <= nblocks` ASSUME_TAC THENL
      [MAP_EVERY (fun t -> TRY(UNDISCH_TAC t))
         [`nblocks DIV 4 = loop_count`; `2 <= loop_count`] THEN ARITH_TAC;
       ALL_TAC]) THEN
     (fun (asl2,w2) ->
        let mcths = List.filter_map (fun (_,th) -> if is_mc(concl th) then Some th else None) asl2 in
        (FIRST (map (fun th -> fun g ->
            (MATCH_MP_TAC(MATCH_MP pth th) THEN
             REWRITE_TAC[ETA_AX; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
             SUBSUMED_MAYCHANGE_TAC) g) mcths)) (asl2,w2))) (asl,w);;

(* The dispatcher of the body leg, applied to each conjunct after
   REPEAT CONJ_TAC: the frame goes to close_goal10, aligned_bytes_loaded to
   ASM_REWRITE_TAC, the output forall to close_goal9, the Q30 conjunct (an
   equation whose right-hand side mentions nist_ghash) to close_goal7, and
   any other conjunct to the first of the remaining closers that closes
   it. *)
let close_all_tac : tactic =
  fun (asl,w) ->
    let has_mc t = try can(find_term(fun x->match x with Const("MAYCHANGE",_)->true|_->false)) t with _->false in
    let dispatch (asl,w) =
      if has_mc w then close_goal10 (asl,w)
      else if has "aligned_bytes_loaded" w then ASM_REWRITE_TAC[] (asl,w)
      else if is_forall w then MUST close_goal9 (asl,w)
      else if is_eq w && has "nist_ghash" (rhs w) then close_goal7 (asl,w)
      else
        (FIRST (map MUST
          [ close_ksfold; close_goal9;
            el 0 closers_0_6; el 1 closers_0_6; el 2 closers_0_6; close_ctr176; el 3 closers_0_6;
            el 4 closers_0_6; el 5 closers_0_6; el 6 closers_0_6;
            close_lanejoin; close_subwordpin; close_goal8; CONV_TAC WORD_RULE ])) (asl,w) in
    dispatch (asl,w)
    ;;

(* The body leg: step the body, split the conjuncts and dispatch them. *)
let body_leg_tac : tactic =
  step_body_tac THEN REPEAT CONJ_TAC THEN close_all_tac;;

(* BODYLEG: swp_inv i at pc + 0x1ec -> swp_inv (i+1) at pc + 0x4b0. *)
let BODYLEG = prove(body_goal, body_leg_tac);;

(* ------------------------------------------------------------------------- *)
(* The fill leg FILLLEG: pc + 0x88 -> pc + 0x1ec, establishing swp_inv 0 for *)
(* loop_count >= 2.  The fill runs 89 instructions; neither the cbz x1 at    *)
(* 0x88 nor the cbz at 0x1e8, after the sub x1,x1,#1 at 0x1e4, is taken.  It *)
(* starts the rounds of blocks 1..3 of group 0 and loads those blocks, so    *)
(* the closers reconstruct the partial encryptions and carried values of     *)
(* swp_inv 0.                                                                *)
(* ------------------------------------------------------------------------- *)
let mk_fill_goal inv =
  mk_imp(`([EL 0 rk; EL 1 rk; EL 2 rk; EL 3 rk; EL 4 rk; EL 5 rk; EL 6 rk;
      EL 7 rk; EL 8 rk; EL 9 rk; EL 10 rk]:(int128)list = rk) /\
     len_bits DIV 128 = nblocks /\ nblocks DIV 4 = loop_count /\ nblocks MOD 4 = loop_remain /\
     2 <= loop_count /\ 16 * nblocks < 2 EXP 64 /\ aligned 16 (stackpointer:int64) /\
     nonoverlapping (out_p:int64,16 * nblocks) (word pc:int64,1856) /\
     nonoverlapping (out_p:int64,16 * nblocks) (in_p:int64,16 * nblocks) /\
     nonoverlapping (out_p:int64,16 * nblocks) (htable_p:int64,96) /\
     nonoverlapping (out_p:int64,16 * nblocks) (tag_p:int64,16) /\
     nonoverlapping (out_p:int64,16 * nblocks) (ivec_p:int64,16) /\
     nonoverlapping (out_p:int64,16*nblocks) (word_add stackpointer (word 160):int64,64) /\
     nonoverlapping (tag_p:int64,16) (word pc:int64,1856) /\
     nonoverlapping (tag_p:int64,16) (in_p:int64,16*nblocks) /\
     nonoverlapping (tag_p:int64,16) (htable_p:int64,96) /\
     nonoverlapping (tag_p:int64,16) (word_add stackpointer (word 160):int64,64) /\
     nonoverlapping (ivec_p:int64,16) (word pc:int64,1856) /\
     nonoverlapping (ivec_p:int64,16) (in_p:int64,16*nblocks) /\
     nonoverlapping (ivec_p:int64,16) (htable_p:int64,96) /\
     nonoverlapping (ivec_p:int64,16) (word_add stackpointer (word 160):int64,64) /\
     nonoverlapping (tag_p:int64,16) (ivec_p:int64,16) /\
     nonoverlapping (word_add stackpointer (word 160):int64,64) (word pc:int64,1856) /\
     nonoverlapping (word_add stackpointer (word 160):int64,64) (in_p:int64,16*nblocks) /\
     nonoverlapping (word_add stackpointer (word 160):int64,64) (htable_p:int64,96)`,
   list_mk_icomb "ensures" [`arm`;
     mk_abs(`s:armstate`, list_mk_conj
       [`aligned_bytes_loaded s (word pc) aes128_gcm_enc_tmc`; `read PC s = word (pc + 0x88)`;
        `read X0 s = in_p`; `read X2 s = out_p`; `read X3 s = tag_p`; `read X4 s = ivec_p`;
        `read X6 s = htable_p`; `read SP s = stackpointer`;
        `read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0`;
        `read (memory :> bytes128 ivec_p) s = word_reversefields 8 (ctr_block nonce c)`;
        `read Q18 s = word_reversefields 8 (EL 0 rk)`; `read Q19 s = word_reversefields 8 (EL 1 rk)`;
        `read Q20 s = word_reversefields 8 (EL 2 rk)`; `read Q21 s = word_reversefields 8 (EL 3 rk)`;
        `read Q22 s = word_reversefields 8 (EL 4 rk)`; `read Q23 s = word_reversefields 8 (EL 5 rk)`;
        `read Q24 s = word_reversefields 8 (EL 6 rk)`; `read Q25 s = word_reversefields 8 (EL 7 rk)`;
        `read Q26 s = word_reversefields 8 (EL 8 rk)`; `read Q27 s = word_reversefields 8 (EL 9 rk)`;
        `read X20 s = word_subword (word_reversefields 8 (EL 10 rk):int128) (0,64):int64`;
        `read X21 s = word_subword (word_reversefields 8 (EL 10 rk):int128) (64,64):int64`;
        `read Q7 s = word 13979173243358019584`;
        `read X11 s = word_subword (word_reversefields 8 (ctr_block nonce c):int128) (0,64):int64`;
        `read X12 s = word_zx (word_zx (word_subword
            (word_reversefields 8 (ctr_block nonce c):int128) (64,64):int64):int32):int64`;
        `read X13 s = word_zx (word c:int32):int64`; `read X15 s = word(len_bits DIV 8)`;
        `read X1 s = word loop_count`; `read X7 s = word nblocks`; `read X16 s = word loop_remain`;
        `read Q30 s = byteswap128 tag0`;
        `htable_mem_4 (ghash_twist (aes128_cipher (word 0) rk)) htable_p s`;
        `!j. j < nblocks ==> read (memory :> bytes128 (word_add in_p (word(16*j)))) s = inblock j`]) ;
     leg_state inv `0x1ec` `0` ;
     `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
      MAYCHANGE [X19; X20; X21; X22; X23; X24; X25; X26; X27; X28; X29; X30] ,,
      MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
      MAYCHANGE [memory :> bytes(out_p:int64, 16 * nblocks)] ,,
      MAYCHANGE [memory :> bytes(word_add stackpointer (word 160):int64, 64)] ,, MAYCHANGE [events]`]);;
let fill_goal = mk_fill_goal swp_inv;;

(* Split the input facts of blocks 0..7 into 64-bit halves, as INPUT_SPLIT_TAC
   does for the body (the fill itself loads blocks 1..3); 7 < nblocks follows
   from 2 <= loop_count. *)
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
      [UNDISCH_TAC `nblocks DIV 4 = loop_count` THEN UNDISCH_TAC `2 <= loop_count` THEN ARITH_TAC; ALL_TAC] THEN
     REPEAT CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE `16 * 0 = 0`; ARITH_RULE `16 * 1 = 16`; ARITH_RULE `16 * 2 = 32`;
     ARITH_RULE `16 * 3 = 48`; ARITH_RULE `16 * 4 = 64`; ARITH_RULE `16 * 5 = 80`;
     ARITH_RULE `16 * 6 = 96`; ARITH_RULE `16 * 7 = 112`; WORD_ADD_0]) THEN
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o CONV_RULE SPLIT_INPUT_CONV o
     check (fun th -> let c = concl th in is_eq c && free_in `in_p:int64` (lhs c) &&
       can (find_term (fun t -> is_const t && fst(dest_const t) = "bytes128")) (lhs c))));;

(* Facts for the two branches of the fill: val (word loop_count) = loop_count
   and ~(loop_count = 0) for the cbz at 0x88, and
   val (word_sub (word loop_count) (word 1)) = loop_count - 1 and
   ~(loop_count - 1 = 0) for the cbz at 0x1e8, after the sub at 0x1e4. *)
let fill_valfacts_tac =
  SUBGOAL_THEN `val(word loop_count:int64) = loop_count` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    UNDISCH_TAC `nblocks DIV 4 = loop_count` THEN UNDISCH_TAC `16 * nblocks < 2 EXP 64` THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~(loop_count = 0)` ASSUME_TAC THENL
   [UNDISCH_TAC `2 <= loop_count` THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `val(word_sub (word loop_count) (word 1):int64) = loop_count - 1` ASSUME_TAC THENL
   [SUBGOAL_THEN `val(word 1:int64) <= val(word loop_count:int64)` MP_TAC THENL
     [REWRITE_TAC[VAL_WORD_1] THEN ASM_REWRITE_TAC[] THEN UNDISCH_TAC `2 <= loop_count` THEN ARITH_TAC;
      DISCH_THEN(fun th -> REWRITE_TAC[VAL_WORD_SUB_CASES; th; VAL_WORD_1]) THEN ASM_REWRITE_TAC[]]; ALL_TAC] THEN
  SUBGOAL_THEN `~(loop_count - 1 = 0)` ASSUME_TAC THENL
   [UNDISCH_TAC `2 <= loop_count` THEN ARITH_TAC; ALL_TAC];;

(* The stp sites of the fill: steps 11, 12, 19, 24, 31 and 37, at 0xb0, 0xb4,
   0xd0, 0xe4, 0x100 and 0x118. *)
let fill_merges = [(11,192);(12,176);(19,160);(24,208);(31,192);(37,208)];;

let fill_step_tac =
  STRIP_TAC THEN REWRITE_TAC[fst AES128_GCM_ENC_EXEC] THEN
  MAP_EVERY (fun rn -> GHOST_INTRO_TAC (mk_var("ghost_"^rn,`:int64`)) (parse_term("read "^rn))) ghost_lanes THEN
  ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV BETA_CONV)) THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_4]) THEN REWRITE_TAC[htable_mem_4] THEN
  FILL_INPUT_SPLIT_TAC THEN
  fill_valfacts_tac THEN
  (* Step 1, the cbz at 0x88: not taken since ~(loop_count = 0). *)
  ARM_STEPS_TAC AES128_GCM_ENC_EXEC [1] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `val(word loop_count:int64) = loop_count`;
                             ASSUME `~(loop_count = 0)`; COND_CLAUSES]) THEN
  (* Steps 2..88, merging the stack stores; step 89 is the cbz at 0x1e8, not
     taken since ~(loop_count - 1 = 0), which ends at the loop head 0x1ec. *)
  SWP_STEPS_TAC enc_anchors [] REDSETX AES128_GCM_ENC_EXEC (K ALL_TAC) fill_merges (2--88) THEN
  ARM_STEPS_TAC AES128_GCM_ENC_EXEC [89] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `val(word_sub (word loop_count) (word 1):int64) = loop_count - 1`;
                             ASSUME `~(loop_count - 1 = 0)`; COND_CLAUSES]) THEN
  RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV THENC
                           ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV THENC IN_P_ADDR_FOLD_CONV)) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[];;

(* The dispatcher of the fill (i = 0; the tag is still tag0).  The counter
   blocks and partial encryptions of group 0 fold with mk_cbv at the
   counters c..c+3, as in the body leg. *)
let fill_close_all : tactic =
  fun (asl,w) ->
    let has_mc t = try can(find_term(fun x->match x with Const("MAYCHANGE",_)->true|_->false)) t with _->false in
    (if has_mc w then close_goal10 (asl,w)
    else if has "aligned_bytes_loaded" w then ASM_REWRITE_TAC[] (asl,w)
    else if is_forall w then
      (* The output forall for j < 4*0: vacuous *)
      (REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT] THEN
        REWRITE_TAC[ARITH_RULE `j < 0 <=> F`]) (asl,w)
    else
      (REWRITE_TAC[ZXNEST4; ZX_COUNTER_UD; GSYM WORD_ADD] THEN FIRST (map MUST
        [ (* ptrs: in_p = word_add in_p (word(64*0)) *)
          (REWRITE_TAC[ARITH_RULE `64*0=0`; WORD_ADD_0] THEN REFL_TAC);
          (* Q30: byteswap128 tag0 = byteswap128(nist_ghash..(4*0)) *)
          (REWRITE_TAC[ARITH_RULE `4*0=0`; list_of_seq; nist_ghash]);
          (* X13 = word_zx (word (4*0+c+4)) *)
          (REWRITE_TAC[ZXNEST4; ZX_COUNTER_UD] THEN AP_TERM_TAC THEN REWRITE_TAC[GSYM WORD_ADD] THEN AP_TERM_TAC THEN ARITH_TAC);
          (* The counter block at sp+160, for counter 4*0+c: normalize
             4*0+c to c, then mk_cbv c *)
          (REWRITE_TAC[ARITH_RULE `4 * 0 + c = c`; ZXNEST4; ZX_COUNTER_UD] THEN ACCEPT_TAC(mk_cbv `c:num`));
          (* The counter block at sp+176, for counter 4*0+c+1 *)
          (REWRITE_TAC[ARITH_RULE `4 * 0 + c + 1 = c + 1`; ZXNEST4; ZX_COUNTER_UD] THEN ACCEPT_TAC(mk_cbv `(c:num) + 1`));
          (* aes7c(4*0+c+2) *)
          (REWRITE_TAC[ARITH_RULE `4 * 0 + c + 2 = c + 2`; aes7c] THEN REPEAT(AP_TERM_TAC ORELSE AP_THM_TAC) THEN
           ACCEPT_TAC(mk_cbv `(c:num) + 2`));
          (* aes8c(4*0+c+1) *)
          (REWRITE_TAC[ARITH_RULE `4 * 0 + c + 1 = c + 1`; aes8c] THEN REPEAT(AP_TERM_TAC ORELSE AP_THM_TAC) THEN
           ACCEPT_TAC(mk_cbv `(c:num) + 1`));
          (* aes10p(4*0+c+3) *)
          (REWRITE_TAC[ARITH_RULE `4 * 0 + c + 3 = c + 3`; aes10p] THEN REPEAT(AP_TERM_TAC ORELSE AP_THM_TAC) THEN
           ACCEPT_TAC(mk_cbv `(c:num) + 3`));
          (* X1: word_sub (word loop_count) (word 1) = word (loop_count-(0+1))
             = word (loop_count-1), using 1 <= loop_count. *)
          (fun (a,w) ->
            let bnd = try snd(find (fun (_,th)->concl th = `2 <= loop_count`) a) with _ -> TRUTH in
            (REWRITE_TAC[ARITH_RULE `(0:num)+1=1`] THEN
             SUBGOAL_THEN `1 <= loop_count` ASSUME_TAC THENL [MP_TAC bnd THEN ARITH_TAC; ALL_TAC] THEN
             ASM_SIMP_TAC[WORD_SUB; VAL_WORD_1] THEN REWRITE_TAC[GSYM VAL_WORD_1] THEN
             AP_TERM_TAC THEN MP_TAC bnd THEN ARITH_TAC) (a,w));
          (* Q10, Q15 and the slots at sp+192 and sp+208: the join of the
             XORed lanes is word_xor (inblock (4*0+2)) rk10, resp. 4*0+3 *)
          (REWRITE_TAC[ARITH_RULE `4*0+2=2`; ARITH_RULE `4*0+3=3`] THEN REWRITE_TAC[JOIN_XOR_LANES]);
          (* X23 and X28: the lanes of word_xor (inblock (4*0+1)) rk10 *)
          (REWRITE_TAC[ARITH_RULE `4*0+1=1`] THEN CONV_TAC WORD_BLAST);
          CONV_TAC WORD_RULE ])) (asl,w))
    ;;

(* FILLLEG.  The goal is an implication with free variables, so the theorem
   is generalized with GEN_ALL: otherwise MATCH_MP_TAC with it would treat
   key_p, which occurs only in its hypotheses, as fixed and leave no
   existential for the EXISTS_TAC `key_p:int64` of the callers.  The same
   holds for the other legs below. *)
let FILLLEG = GEN_ALL(prove(fill_goal, fill_step_tac THEN REPEAT CONJ_TAC THEN fill_close_all));;

(* ------------------------------------------------------------------------- *)
(* The end of the 4-block loop.  REDUCELAST takes swp_inv (loop_count - 1)   *)
(* at pc + 0x4b0, where the cbnz is not taken (X1 = word 0), through         *)
(* reduce_last (pc + 0x4b4 .. pc + 0x618), which finishes the last group:    *)
(* its AES rounds, its four output blocks and its GHASH.  It ends at the     *)
(* bridge state swps_bridge_post at pc + 0x61c, where X0/X2 are advanced by  *)
(* 64*loop_count, X1 = word 0, X13 = word_zx (word (4*loop_count+c)), Q30 is *)
(* the tag of the first 4*loop_count blocks and those blocks are stored.     *)
(* TAILLEG takes the bridge state to the postcondition at pc + 0x710.        *)
(*                                                                           *)
(* These legs use the broad frame swps_broad_frame, which adds the tag and   *)
(* ivec buffers the tail writes, since the composition needs one frame;      *)
(* BODYLEG and FILLLEG, proved with a narrower frame, are widened to it      *)
(* below.                                                                    *)
(* ------------------------------------------------------------------------- *)

(* The broad frame of the composed legs. *)
let swps_broad_frame =
  `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
   MAYCHANGE [X19; X20; X21; X22; X23; X24; X25; X26; X27; X28; X29; X30] ,,
   MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
   MAYCHANGE [memory :> bytes(out_p:int64, 16 * nblocks);
              memory :> bytes(tag_p:int64, 16); memory :> bytes(ivec_p:int64, 16);
              memory :> bytes(word_add stackpointer (word 160):int64, 64)]`;;

(* The hypotheses of REDUCELAST, DRAINLEG, MAINLEG and, without
   2 <= loop_count, TAILLEG: the round-key list, the block counts, the size
   bound, the stack alignment and the nonoverlapping conditions. *)
let swps_leg_precond =
  `([EL 0 rk; EL 1 rk; EL 2 rk; EL 3 rk; EL 4 rk; EL 5 rk; EL 6 rk;
      EL 7 rk; EL 8 rk; EL 9 rk; EL 10 rk]:(int128)list = rk) /\
     len_bits DIV 128 = nblocks /\ nblocks DIV 4 = loop_count /\ nblocks MOD 4 = loop_remain /\
     2 <= loop_count /\ 16 * nblocks < 2 EXP 64 /\ aligned 16 (stackpointer:int64) /\
     nonoverlapping (out_p:int64,16 * nblocks) (word pc:int64,1856) /\
     nonoverlapping (out_p:int64,16 * nblocks) (in_p:int64,16 * nblocks) /\
     nonoverlapping (out_p:int64,16 * nblocks) (key_p:int64,176) /\
     nonoverlapping (out_p:int64,16 * nblocks) (htable_p:int64,96) /\
     nonoverlapping (tag_p:int64,16) (word pc:int64,1856) /\
     nonoverlapping (tag_p:int64,16) (in_p:int64,16*nblocks) /\
     nonoverlapping (tag_p:int64,16) (key_p:int64,176) /\
     nonoverlapping (tag_p:int64,16) (htable_p:int64,96) /\
     nonoverlapping (ivec_p:int64,16) (word pc:int64,1856) /\
     nonoverlapping (ivec_p:int64,16) (in_p:int64,16*nblocks) /\
     nonoverlapping (ivec_p:int64,16) (key_p:int64,176) /\
     nonoverlapping (ivec_p:int64,16) (htable_p:int64,96) /\
     nonoverlapping (word_add stackpointer (word 160):int64,64) (word pc:int64,1856) /\
     nonoverlapping (word_add stackpointer (word 160):int64,64) (in_p:int64,16*nblocks) /\
     nonoverlapping (word_add stackpointer (word 160):int64,64) (key_p:int64,176) /\
     nonoverlapping (word_add stackpointer (word 160):int64,64) (htable_p:int64,96) /\
     nonoverlapping (out_p:int64,16 * nblocks) (tag_p:int64,16) /\
     nonoverlapping (out_p:int64,16 * nblocks) (ivec_p:int64,16) /\
     nonoverlapping (out_p:int64,16*nblocks) (word_add stackpointer (word 160):int64,64) /\
     nonoverlapping (tag_p:int64,16) (ivec_p:int64,16) /\
     nonoverlapping (tag_p:int64,16) (word_add stackpointer (word 160):int64,64) /\
     nonoverlapping (ivec_p:int64,16) (word_add stackpointer (word 160):int64,64)`;;

(* The bridge state at pc + 0x61c, after the 4-block loop; everything is
   indexed by 4*loop_count. *)
let swps_bridge_post =
  mk_abs(`s:armstate`, list_mk_conj
    [`aligned_bytes_loaded s (word pc) aes128_gcm_enc_tmc`; `read PC s = word (pc + 0x61c)`;
     `read X0 s = word_add in_p (word (64 * loop_count))`;
     `read X2 s = word_add out_p (word (64 * loop_count))`;
     `read X3 s = tag_p`; `read X4 s = ivec_p`; `read X6 s = htable_p`; `read SP s = stackpointer`;
     `read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0`;
     `read (memory :> bytes128 ivec_p) s = word_reversefields 8 (ctr_block nonce c)`;
     `read Q18 s = word_reversefields 8 (EL 0 rk)`; `read Q19 s = word_reversefields 8 (EL 1 rk)`;
     `read Q20 s = word_reversefields 8 (EL 2 rk)`; `read Q21 s = word_reversefields 8 (EL 3 rk)`;
     `read Q22 s = word_reversefields 8 (EL 4 rk)`; `read Q23 s = word_reversefields 8 (EL 5 rk)`;
     `read Q24 s = word_reversefields 8 (EL 6 rk)`; `read Q25 s = word_reversefields 8 (EL 7 rk)`;
     `read Q26 s = word_reversefields 8 (EL 8 rk)`; `read Q27 s = word_reversefields 8 (EL 9 rk)`;
     `read X20 s = word_subword (word_reversefields 8 (EL 10 rk):int128) (0,64):int64`;
     `read X21 s = word_subword (word_reversefields 8 (EL 10 rk):int128) (64,64):int64`;
     `read Q7 s = word 13979173243358019584`;
     `read X11 s = word_subword (word_reversefields 8 (ctr_block nonce c):int128) (0,64):int64`;
     `read X12 s = word_zx (word_zx (word_subword
         (word_reversefields 8 (ctr_block nonce c):int128) (64,64):int64):int32):int64`;
     `read X13 s = word_zx (word (4 * loop_count + c):int32):int64`;
     `read X15 s = word(len_bits DIV 8)`; `read X1 s = word 0`; `read X16 s = word loop_remain`;
     `read Q30 s = byteswap128
          (nist_ghash (aes128_cipher (word 0) rk) tag0
             (list_of_seq (nist_cipher_block aes128_cipher c nonce rk inblock) (4 * loop_count)))`;
     `htable_mem_4 (ghash_twist (aes128_cipher (word 0) rk)) htable_p s`;
     `!j. j < nblocks ==> read (memory :> bytes128 (word_add in_p (word(16*j)))) s = inblock j`;
     `!j. j < 4 * loop_count ==> read (memory :> bytes128 (word_add out_p (word(16*j)))) s =
              word_xor (aes_ctr_block aes128_cipher c nonce rk j) (inblock j)`]);;

(* REDUCELAST: swp_inv (loop_count - 1) at pc + 0x4b0 -> swps_bridge_post at
   pc + 0x61c, with the broad frame. *)
let reducelast_goal =
  mk_imp(swps_leg_precond,
   list_mk_icomb "ensures" [`arm`;
     leg_state swp_inv `0x4b0` `loop_count - 1` ;
     swps_bridge_post ;
     swps_broad_frame]);;

(* REDUCELAST starts with the cbnz at 0x4b0, not taken since X1 = word 0, and
   then runs reduce_last (0x4b4..0x618), which finishes the last group
   4m..4m+3 (m = loop_count - 1) and loads no further blocks.  Its stp sites
   are steps 8 (0x4cc, sp+176) and 28 (0x51c, sp+160), counting the cbnz as
   step 1; both store input lanes XOR rk10. *)
let reducelast_merges = [(8,176);(28,160)];;

let REDUCELAST_INPUT_SPLIT_TAC =
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

(* Stepping REDUCELAST: with m = loop_count - 1 the precondition is swp_inv m,
   whose X1 conjunct reduces to word 0; then the cbnz and reduce_last. *)
let reducelast_step_tac =
  STRIP_TAC THEN REWRITE_TAC[fst AES128_GCM_ENC_EXEC] THEN
  MAP_EVERY (fun rn -> GHOST_INTRO_TAC (mk_var("ghost_"^rn,`:int64`)) (parse_term("read "^rn))) ghost_lanes THEN
  ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV BETA_CONV)) THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_4]) THEN REWRITE_TAC[htable_mem_4] THEN
  ABBREV_TAC `m = loop_count - 1` THEN
  SUBGOAL_THEN `loop_count = m + 1` ASSUME_TAC THENL
   [EXPAND_TAC "m" THEN UNDISCH_TAC `2 <= loop_count` THEN ARITH_TAC; ALL_TAC] THEN
  (* After the abbreviation the X1 conjunct reads word (loop_count - (m+1)),
     which is word 0 since loop_count = m + 1. *)
  FIRST_X_ASSUM(fun th ->
    if can (term_match [] `read X1 s0 = word (loop_count - (m + 1))`) (concl th)
    then ASSUME_TAC(REWRITE_RULE[ASSUME `loop_count = m + 1`;
                     ARITH_RULE `(m + 1) - (m + 1) = 0`] th)
    else NO_TAC) THEN
  REDUCELAST_INPUT_SPLIT_TAC THEN
  (* Step 1, the cbnz at 0x4b0: not taken since X1 = word 0. *)
  ARM_STEPS_TAC AES128_GCM_ENC_EXEC [1] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[VAL_WORD_0; COND_CLAUSES]) THEN
  (* Steps 2..91: reduce_last, 0x4b4..0x618. *)
  SWP_STEPS_TAC enc_anchors [] REDSETX AES128_GCM_ENC_EXEC (K ALL_TAC) reducelast_merges (2--91) THEN
  RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV THENC
                           ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV THENC IN_P_ADDR_FOLD_CONV)) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];;

(* The closers of REDUCELAST.  The precondition is swp_inv m with
   m = loop_count - 1, so the bridge conjuncts appear in terms of m+1.  Q30
   goes from the tag of 4*m blocks to that of 4*m+4 by the reconstruction of
   close_goal7; the output forall splits into the blocks j < 4*m and the last
   group. *)
let reducelast_close_ghash : tactic =
  (* Q30: word_subword (word_join ...) (64,128) =
     byteswap128 (nist_ghash ... (4*(m+1))).  The four last ciphertext blocks
     fold from the carried partial encryptions (aes7c, aes8c, aes10p) and the
     block computed from scratch in reduce_last; then the GHASH update is
     reconstructed as in close_goal7, with the tag of 4*m blocks as sofar. *)
  fun (asl,w) ->
    let rkth = try snd(find (fun (_,th) -> concl th =
        `[EL 0 rk; EL 1 rk; EL 2 rk; EL 3 rk; EL 4 rk; EL 5 rk; EL 6 rk;
          EL 7 rk; EL 8 rk; EL 9 rk; EL 10 rk]:(int128)list = rk`) asl)
      with _ -> failwith "reducelast_close_ghash: no rk-hyp" in
    let ksf = MATCH_MP KEYSTREAM_FOLD rkth in
    let ghostpins = List.filter_map (fun (_,th) ->
      let c = concl th in
      if is_eq c then (match lhs c with
        | Var(nm,_) when String.length nm>=6 && String.sub nm 0 6="ghost_"
            && can (find_term (fun t -> try fst(dest_const(fst(strip_comb t)))="inblock" with _->false)) (rhs c)
          -> Some th | _ -> None) else None) asl in
    (
    (* Write the tag index 4*(m+1) as 4*m+4 and fold the keystreams of the
       last group. *)
    REWRITE_TAC[ARITH_RULE `4*(m+1) = 4*m+4`] THEN
    REWRITE_TAC(JOIN_SUBWORD_RECOMBINE :: ghostpins) THEN
    REWRITE_TAC[GSYM AES10P_VIA_AES7C; GSYM AES10P_VIA_AES8C; GSYM aes10p] THEN
    REWRITE_TAC[JOIN_XOR_LANES] THEN
    REWRITE_TAC[ksf] THEN
    REWRITE_TAC[ARITH_RULE `4*m+c+3 = (4*m+3)+c`; ARITH_RULE `4*m+c+2 = (4*m+2)+c`;
                ARITH_RULE `4*m+c+1 = (4*m+1)+c`; ARITH_RULE `4*m+0 = 4*m`] THEN
    REWRITE_TAC[CT_TO_NCB] THEN
    REWRITE_TAC[ARITH_RULE `(4*m+0)+2 = 4*m+2`; ARITH_RULE `(4*m+1)+2 = 4*m+3`;
                ARITH_RULE `(4*m+2)+2 = 4*m+4`; ARITH_RULE `(4*m+3)+2 = 4*m+5`;
                ARITH_RULE `4*m+0 = 4*m`] THEN
    (* The GHASH reconstruction, as in close_goal7. *)
    REWRITE_TAC[WORD_SUBWORD_REVERSEFIELDS] THEN
    SIMP_TAC[WORD_JOIN_COMBINE_LEMMA; ARITH] THEN
    REWRITE_TAC[WORD_SUBWORD_XOR] THEN
    REWRITE_TAC[WORD_SUBWORD_BYTESWAP128] THEN
    CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
    REWRITE_TAC[WORD_SUBWORD_XOR] THEN
    CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
    REWRITE_TAC [byteswap128; WORD_BLAST
      `word_subword((word_join:int128->int128->int256) h l) (64,128):int128 =
       word_join (word_subword h (0,64):int64) (word_subword l (64,64):int64)`] THEN
    MATCH_MP_TAC(BITBLAST_RULE
     `x:int128 = y
      ==> word_join (word_subword x (0,64):int64) (word_subword x (64,64):int64):int128 =
          word_join (word_subword y (0,64):int64) (word_subword y (64,64):int64):int128`) THEN
    MAP_EVERY ABBREV_TAC
     [`sofar = (nist_ghash (aes128_cipher (word 0) rk) tag0
                 (list_of_seq (nist_cipher_block aes128_cipher c nonce rk inblock) (4 * m)))`;
      `cipherblock_0 = nist_cipher_block aes128_cipher c nonce rk inblock (4 * m)`;
      `cipherblock_1 = nist_cipher_block aes128_cipher c nonce rk inblock (4 * m + 1)`;
      `cipherblock_2 = nist_cipher_block aes128_cipher c nonce rk inblock (4 * m + 2)`;
      `cipherblock_3 = nist_cipher_block aes128_cipher c nonce rk inblock (4 * m + 3)`;
      `h0 = h_power (ghash_twist (aes128_cipher (word 0) rk)) 0`;
      `h1 = h_power (ghash_twist (aes128_cipher (word 0) rk)) 1`;
      `h2 = h_power (ghash_twist (aes128_cipher (word 0) rk)) 2`;
      `h3 = h_power (ghash_twist (aes128_cipher (word 0) rk)) 3`] THEN
    REWRITE_TAC[GSYM WORD_SUBWORD_XOR] THEN
    REWRITE_TAC[RECONSTRUCT_POLYVAL_REDUCE_G2] THEN
    TRANS_TAC EQ_TRANS
     `polyval_reduce_prop3
          (word_xor (word_pmul (cipherblock_3:int128) (h0:int128))
          (word_xor (word_pmul (cipherblock_2:int128) (h1:int128))
          (word_xor (word_pmul (cipherblock_1:int128) (h2:int128))
          (word_pmul (word_xor (sofar:int128) cipherblock_0) (h3:int128)))))` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[PMUL_KARATSUBA_JOIN_ALT] THEN
      REWRITE_TAC[byteswap128; WORD_SUBWORD_XOR] THEN
      CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
      REWRITE_TAC[karatsuba_mid] THEN ASM_REWRITE_TAC[] THEN
      REPEAT(LET_TAC THEN ASM_REWRITE_TAC[]) THEN
      ONCE_REWRITE_TAC[MESON[WORD_XOR_SYM]
       `word_pmul (word_xor a b) (word_xor c d) = word_pmul (word_xor b a) (word_xor c d)`] THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[POLYVAL_REDUCE_G2] THEN ASM_REWRITE_TAC[] THEN
      MAP_EVERY EXPAND_TAC ["ks"; "ks'"; "ks''"; "ks'''"] THEN
      CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
      AP_TERM_TAC THEN REWRITE_TAC[GSYM karatsuba_join] THEN MATCH_ACCEPT_TAC KARATSUBA_JOIN_XOR4;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`ghash_twist (aes128_cipher (word 0) rk)`;
                   `[cipherblock_1;cipherblock_2;cipherblock_3]:(int128)list`;
                   `sofar:int128`; `cipherblock_0:int128`]
                  GHASH_POLYVAL_ACC_BATCHED) THEN
    REWRITE_TAC[LENGTH; ghash_wide] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(MESON[]
     `y' = y /\ x' = x ==> x = y ==> y' = x'`) THEN
    CONJ_TAC THENL [AP_TERM_TAC THEN CONV_TAC WORD_BITWISE_RULE; ALL_TAC] THEN
    EXPAND_TAC "sofar" THEN
    REWRITE_TAC[NIST_GHASH_IS_POLYVAL] THEN
    REWRITE_TAC[ARITH_RULE `4*m+4 = SUC(SUC(SUC(SUC(4*m))))`] THEN
    REWRITE_TAC[list_of_seq] THEN REWRITE_TAC[GSYM APPEND_ASSOC] THEN
    REWRITE_TAC[APPEND] THEN
    REWRITE_TAC[GHASH_ACC_APPEND] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ADD1; GSYM ADD_ASSOC] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[GSYM NIST_GHASH_IS_POLYVAL]
    ) (asl,w);;

(* The output forall of the bridge: j < 4*(m+1) splits into j < 4*m, from the
   invariant, and the last group 4m..4m+3; as close_goal9, with m for i. *)
let reducelast_close_outputs : tactic =
  fun (asl,w) ->
    let rkth = try snd(find (fun (_,th) -> concl th =
        `[EL 0 rk; EL 1 rk; EL 2 rk; EL 3 rk; EL 4 rk; EL 5 rk; EL 6 rk;
          EL 7 rk; EL 8 rk; EL 9 rk; EL 10 rk]:(int128)list = rk`) asl)
      with _ -> failwith "reducelast_close_outputs: no rk-hyp" in
    (REWRITE_TAC[ARITH_RULE `4 * (m+1) = 4*m+4`] THEN
     REWRITE_TAC[ARITH_RULE `j < 4*m+4 <=>
                          j < 4 * m \/ j = 4*m+0 \/ j = 4*m+1 \/ j = 4*m+2 \/ j = 4*m+3`] THEN
     ASM_REWRITE_TAC[TAUT `p \/ q ==> r <=> (p ==> r) /\ (q ==> r)`] THEN
     REWRITE_TAC[FORALL_AND_THM; FORALL_UNWIND_THM2] THEN
     REWRITE_TAC[ARITH_RULE `16 * (4*m+0) = 64*m`; ARITH_RULE `16 * (4*m+1) = 64*m+16`;
        ARITH_RULE `16 * (4*m+2) = 64*m+32`; ARITH_RULE `16 * (4*m+3) = 64*m+48`] THEN
     ASM_REWRITE_TAC[] THEN
     REWRITE_TAC[CTR_BLOCK_BUILD_INSERT] THEN
     REWRITE_TAC[SCALAR_RK_RECONSTRUCT] THEN
     REWRITE_TAC[XOR_AES128_CIPHER_RECONSTRUCT] THEN
     ASM_REWRITE_TAC[MAP; WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
     REWRITE_TAC[aes_ctr_block] THEN
     REWRITE_TAC[ARITH_RULE `4 * i + c + 3 = (4 * i + 3) + c`;
                 ARITH_RULE `4 * i + c + 2 = (4 * i + 2) + c`;
                 ARITH_RULE `4 * i + c + 1 = (4 * i + 1) + c`;
                 ARITH_RULE `4 * i + 0 = 4 * i`] THEN ASM_REWRITE_TAC[] THEN
     REPEAT CONJ_TAC THEN
     REWRITE_TAC[JOIN_SUBWORD_RECOMBINE] THEN
     REWRITE_TAC[GSYM AES10P_VIA_AES7C; GSYM AES10P_VIA_AES8C] THEN
     REWRITE_TAC[MATCH_MP KEYSTREAM_FOLD rkth]) (asl,w);;

(* The dispatcher of REDUCELAST (m = loop_count - 1; the bridge is indexed
   by m+1). *)
let reducelast_close_all : tactic =
  fun (asl,w) ->
    let has_mc t = try can(find_term(fun x->match x with Const("MAYCHANGE",_)->true|_->false)) t with _->false in
    (if has_mc w then close_goal10 (asl,w)
    else if has "aligned_bytes_loaded" w then ASM_REWRITE_TAC[] (asl,w)
    else if is_forall w then MUST reducelast_close_outputs (asl,w)
    else if is_eq w && has "nist_ghash" (rhs w) then reducelast_close_ghash (asl,w)
    else
      (FIRST (map MUST
        [ (* X0/X2: word_add p (word(64*m+64)) = word_add p (word(64*(m+1))) *)
          (REWRITE_TAC[ARITH_RULE `64*(m+1)=64*m+64`; LEFT_ADD_DISTRIB] THEN CONV_TAC WORD_RULE);
          (REWRITE_TAC[ARITH_RULE `4*(m+1)+2 = 4*m+6`] THEN CONV_TAC WORD_RULE);
          (* X13: word_zx (word (4*m+c+4)) = word_zx (word (4*(m+1)+c)), by
             arithmetic on the counter *)
          (AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC);
          (* X1: word 0 (already settled) *)
          REFL_TAC;
          CONV_TAC WORD_RULE;
          CONV_TAC WORD_BLAST ])) (asl,w))
    ;;

let REDUCELAST = GEN_ALL(prove(reducelast_goal,
         (reducelast_step_tac THEN REPEAT CONJ_TAC THEN reducelast_close_all)));;

(* ------------------------------------------------------------------------- *)
(* The tail leg TAILLEG: swps_bridge_post at pc + 0x61c -> the               *)
(* postcondition at pc + 0x710.  The single-block tail loop processes the    *)
(* loop_remain remaining blocks (head pc + 0x62c, back edge pc + 0x6f8),     *)
(* then the tag and the counter word are stored; the postcondition gives all *)
(* the output blocks, the tag, the ivec and X0.                              *)
(* ------------------------------------------------------------------------- *)
(* WORD_SIMPLE_SUBWORD_CONV on every assumption except the quantified
   memory facts. *)
let SUBWORD_NONFORALL =
  RULE_ASSUM_TAC(fun th ->
    if is_forall (concl th) then th
    else CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) th);;

(* TAILLEG is used for every loop_count (CORE_FROM88 reaches it after all
   three cases), so its hypotheses omit 2 <= loop_count. *)
let swps_tail_precond =
  list_mk_conj(filter (fun c -> c <> `2 <= loop_count`) (conjuncts swps_leg_precond));;
let swps_tail_goal =
  mk_imp(swps_tail_precond,
   list_mk_icomb "ensures" [`arm`;
     swps_bridge_post ;
     mk_abs(`s:armstate`, list_mk_conj
       [`read PC s = word (pc + 0x710)`;
        `!i. i < nblocks ==> read (memory :> bytes128 (word_add out_p (word(16*i)))) s =
                 word_xor (aes_ctr_block aes128_cipher c nonce rk i) (inblock i)`;
        `read (memory :> bytes128 tag_p) s =
           word_reversefields 8
            (nist_ghash (aes128_cipher (word 0) rk) tag0
               (list_of_seq (nist_cipher_block aes128_cipher c nonce rk inblock) nblocks))`;
        `read (memory :> bytes128 ivec_p) s =
           word_reversefields 8 (ctr_block nonce (nblocks + c))`;
        `read X0 s = word (len_bits DIV 8)`]) ;
     swps_broad_frame]);;

let swps_tail_tac =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  (*** loop_remain = 0: no tail iterations, only the tag and ivec stores ***)
  ASM_CASES_TAC `loop_remain = 0` THENL
   [POP_ASSUM SUBST_ALL_TAC THEN
    ENSURES_INIT_TAC "s0" THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o CONV_RULE(READ_MEMORY_SPLIT_CONV 2) o
      check (fun th -> let c = concl th in
        is_eq c && free_in `ivec_p:int64` (lhs c) &&
        not(free_in `out_p:int64` (lhs c)) && not(free_in `key_p:int64` (lhs c)) &&
        not(free_in `htable_p:int64` (lhs c)) && not(free_in `tag_p:int64` (lhs c)))) THEN
    MAP_EVERY(fun n -> ARM_STEPS_TAC AES128_GCM_ENC_EXEC [n] THEN
          RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV))) (1--9) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP (ARITH_RULE `n MOD 4 = 0 ==> 4 * n DIV 4 = n`)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN
    CONV_TAC(ONCE_DEPTH_CONV(fun t ->
      if is_eq t && free_in `ivec_p:int64` (lhs t) &&
         not(free_in `out_p:int64` (lhs t)) && not(free_in `tag_p:int64` (lhs t))
      then READ_MEMORY_SPLIT_CONV 2 t else failwith "")) THEN
    CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    REWRITE_TAC[ZX_COUNTER_UD; CTR_ZX_NORM] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[byteswap128; ctr_block] THEN
    CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN CONV_TAC WORD_BLAST;
    ALL_TAC] THEN
  (*** loop_remain >= 1: the tail loop, head 0x62c, back edge 0x6f8 ***)
  ENSURES_WHILE_UP_TAC `loop_remain:num` `pc + 0x62c` `pc + 0x6f8`
    `\i s.
      read X0  s = word_add in_p  (word (64 * loop_count + 16 * i)) /\
      read X2  s = word_add out_p (word (64 * loop_count + 16 * i)) /\
      read X3 s = tag_p /\ read X4 s = ivec_p /\ read X6 s = htable_p /\
      read SP s = stackpointer /\
      read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
      read (memory :> bytes128 ivec_p) s = word_reversefields 8 (ctr_block nonce c) /\
      read Q18 s = word_reversefields 8 (EL 0 rk) /\ read Q19 s = word_reversefields 8 (EL 1 rk) /\
      read Q20 s = word_reversefields 8 (EL 2 rk) /\ read Q21 s = word_reversefields 8 (EL 3 rk) /\
      read Q22 s = word_reversefields 8 (EL 4 rk) /\ read Q23 s = word_reversefields 8 (EL 5 rk) /\
      read Q24 s = word_reversefields 8 (EL 6 rk) /\ read Q25 s = word_reversefields 8 (EL 7 rk) /\
      read Q26 s = word_reversefields 8 (EL 8 rk) /\ read Q27 s = word_reversefields 8 (EL 9 rk) /\
      read X20 s = word_subword (word_reversefields 8 (EL 10 rk):int128) (0,64):int64 /\
      read X21 s = word_subword (word_reversefields 8 (EL 10 rk):int128) (64,64):int64 /\
      read Q7 s = word 13979173243358019584 /\
      read X11 s = word_subword (word_reversefields 8 (ctr_block nonce c):int128) (0,64):int64 /\
      read X12 s = word_zx (word_zx (word_subword
          (word_reversefields 8 (ctr_block nonce c):int128) (64,64):int64):int32):int64 /\
      read X13 s = word_zx (word (4 * loop_count + i + c):int32):int64 /\
      read X15 s = word(len_bits DIV 8) /\ read X16 s = word(loop_remain - i) /\
      read Q30 s = byteswap128
          (nist_ghash (aes128_cipher (word 0) rk) tag0
             (list_of_seq (nist_cipher_block aes128_cipher c nonce rk inblock) (4 * loop_count + i))) /\
      htable_mem_4 (ghash_twist (aes128_cipher (word 0) rk)) htable_p s /\
      read Q12 s = byteswap128 (h_power (ghash_twist (aes128_cipher (word 0) rk)) 0) /\
      read Q14 s = word_join
       (karatsuba_mid (h_power (ghash_twist (aes128_cipher (word 0) rk)) 1))
       (karatsuba_mid (h_power (ghash_twist (aes128_cipher (word 0) rk)) 0)) /\
        (!j. j < nblocks ==> read (memory :> bytes128 (word_add in_p (word(16*j)))) s = inblock j) /\
      (!j. j < 4 * loop_count + i
           ==> read (memory :> bytes128 (word_add out_p (word(16*j)))) s =
               word_xor (aes_ctr_block aes128_cipher c nonce rk j) (inblock j))` THEN
  ASM_REWRITE_TAC[htable_mem_4; GSYM CONJ_ASSOC] THEN REPEAT CONJ_TAC THENL
   [(*** The initialization: the bridge at 0x61c -> 0x62c, i = 0 ***)
    ENSURES_INIT_TAC "s0" THEN
    MAP_EVERY(fun n -> ARM_STEPS_TAC AES128_GCM_ENC_EXEC [n] THEN
          RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV))) (1--3) THEN
    ARM_STEPS_TAC AES128_GCM_ENC_EXEC [4] THEN
    SUBGOAL_THEN `val(word loop_remain:int64) = loop_remain` ASSUME_TAC THENL
     [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
      EXPAND_TAC "loop_remain" THEN
      W(fun _ -> MP_TAC(SPECL [`nblocks:num`;`4`] MOD_LT_EQ)) THEN ARITH_TAC;
      ALL_TAC] THEN
    FIRST_X_ASSUM(fun th -> match concl th with
      | Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),Const("PC",_)),Var("s4",_))),
             Comb(Comb(Comb(Const("COND",_),_),_),_)) ->
          ASSUME_TAC(REWRITE_RULE[ASSUME `val(word loop_remain:int64) = loop_remain`;
                                  ASSUME `~(loop_remain = 0)`; COND_CLAUSES] th)
      | _ -> NO_TAC) THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES; SUB_0];

    (*** The body: 0x62c -> 0x6f8, one block ***)
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
    ENSURES_INIT_TAC "s0" THEN
    SUBGOAL_THEN
     `read (memory :> bytes128 (word_add in_p (word (64 * loop_count + 16 * i)))) s0 =
      inblock (4 * loop_count + i)`
    ASSUME_TAC THENL
     [REWRITE_TAC[ARITH_RULE `64 * a + 16 * b = 16 * (4 * a + b)`] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o CONV_RULE SPLIT_INPUT_TAIL_CONV o
      check (fun th -> let c = concl th in
        is_eq c && free_in `in_p:int64` (lhs c) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "bytes128")) (lhs c))) THEN
    SUBGOAL_THEN `4 * loop_count + i < nblocks` ASSUME_TAC THENL
     [MAP_EVERY (fun t -> UNDISCH_TAC t)
        [`i < loop_remain`; `nblocks MOD 4 = loop_remain`; `nblocks DIV 4 = loop_count`] THEN
      ARITH_TAC; ALL_TAC] THEN
    MAP_EVERY(fun n -> ARM_STEPS_TAC AES128_GCM_ENC_EXEC [n] THEN SUBWORD_NONFORALL) (1--5) THEN
    MERGE_CTR128_TAC 160 "s5" THEN
    MAP_EVERY(fun n -> ARM_STEPS_TAC AES128_GCM_ENC_EXEC [n] THEN SUBWORD_NONFORALL) (6--28) THEN
    MERGE_CTR128_TAC 160 "s28" THEN
    MAP_EVERY(fun n -> ARM_STEPS_TAC AES128_GCM_ENC_EXEC [n] THEN SUBWORD_NONFORALL) (29--51) THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ARITH_RULE `j < a + i + 1 <=> j < a + i \/ j = a + i`] THEN
    ASM_REWRITE_TAC[TAUT `p \/ q ==> r <=> (p ==> r) /\ (q ==> r)`] THEN
    REWRITE_TAC[FORALL_AND_THM; FORALL_UNWIND_THM2] THEN
    ASM_REWRITE_TAC[ARITH_RULE `16 * (4 * a + b) = 64 * a + 16 * b`] THEN
    REWRITE_TAC[ZX_COUNTER_UD; ZX_COUNTER_INC; CTR_ZX_NORM] THEN
    REWRITE_TAC[GSYM WORD_ADD; WORD_ADD_0; ADD_0] THEN
    REWRITE_TAC[CTR_BLOCK_BUILD_INSERT] THEN
    REWRITE_TAC[SCALAR_RK_RECONSTRUCT] THEN
    REWRITE_TAC[XOR_AES128_CIPHER_RECONSTRUCT] THEN
    ASM_REWRITE_TAC[MAP; WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
    REWRITE_TAC[aes_ctr_block; GSYM ADD_ASSOC] THEN
    CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
    ASM_SIMP_TAC[WORD_SUB; LT_IMP_LE; ARITH_RULE `i < l ==> i + 1 <= l`] THEN
    DISCARD_STATE_TAC "s51" THEN
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
    FIRST_ASSUM(fun th -> if can (term_match []
        `[EL 0 rk; EL 1 rk; EL 2 rk; EL 3 rk; EL 4 rk; EL 5 rk; EL 6 rk;
          EL 7 rk; EL 8 rk; EL 9 rk; EL 10 rk]:(int128)list = rk`) (concl th)
      then REWRITE_TAC[th] else NO_TAC) THEN
    REPEAT(CONJ_TAC THENL
      [CONV_TAC WORD_RULE ORELSE (AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC);
       ALL_TAC]) THEN
    REWRITE_TAC [byteswap128; WORD_BLAST
    `word_subword((word_join:int128->int128->int256) h l) (64,128):int128 =
     word_join (word_subword h (0,64):int64) (word_subword l (64,64):int64)`] THEN
    MATCH_MP_TAC(BITBLAST_RULE
     `x:int128 = y
      ==> word_join (word_subword x (0,64):int64) (word_subword x (64,64):int64):int128 =
          word_join (word_subword y (0,64):int64) (word_subword y (64,64):int64):int128`) THEN
    MAP_EVERY ABBREV_TAC
     [`sofar = (nist_ghash (aes128_cipher (word 0) rk) tag0
                 (list_of_seq (nist_cipher_block aes128_cipher c nonce rk inblock) (4 * loop_count + i)))`;
      `cipherblock = nist_cipher_block aes128_cipher c nonce rk inblock (4 * loop_count + i)`;
      `h = h_power (ghash_twist (aes128_cipher (word 0) rk)) 0`;
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
    ASM_REWRITE_TAC[];

    (*** The back edge: the cbnz at 0x6f8, taken ***)
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
    ARM_SIM_TAC AES128_GCM_ENC_EXEC [1] THEN
    SUBGOAL_THEN `val(word loop_remain:int64) = loop_remain` ASSUME_TAC THENL
     [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
      EXPAND_TAC "loop_remain" THEN
      W(fun _ -> MP_TAC(SPECL [`nblocks:num`;`4`] MOD_LT_EQ)) THEN ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[WORD_SUB; LT_IMP_LE; VAL_EQ_0; WORD_SUB_EQ_0] THEN
    ASM_REWRITE_TAC[GSYM VAL_EQ] THEN ASM_ARITH_TAC;

    (*** The exit: the cbnz at 0x6f8 not taken, then the tag and ivec stores,
     *** to 0x710 ***)
    ENSURES_INIT_TAC "s0" THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o CONV_RULE(READ_MEMORY_SPLIT_CONV 2) o
      check (fun th -> let c = concl th in
        is_eq c && free_in `ivec_p:int64` (lhs c) &&
        not(free_in `out_p:int64` (lhs c)) && not(free_in `key_p:int64` (lhs c)) &&
        not(free_in `htable_p:int64` (lhs c)) && not(free_in `tag_p:int64` (lhs c)))) THEN
    MAP_EVERY(fun n -> ARM_STEPS_TAC AES128_GCM_ENC_EXEC [n] THEN
          RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV))) (1--6) THEN
    ENSURES_FINAL_STATE_TAC THEN
    SUBGOAL_THEN `nblocks = 4 * loop_count + loop_remain` SUBST_ALL_TAC THENL
     [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    CONV_TAC(ONCE_DEPTH_CONV(fun t ->
      if is_eq t && free_in `ivec_p:int64` (lhs t) &&
         not(free_in `out_p:int64` (lhs t)) && not(free_in `tag_p:int64` (lhs t))
      then READ_MEMORY_SPLIT_CONV 2 t else failwith "")) THEN
    CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    REWRITE_TAC[ZX_COUNTER_UD] THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[byteswap128; ctr_block] THEN
    REWRITE_TAC[ADD_ASSOC; ZX_COUNTER_UD; CTR_ZX_NORM] THEN
    CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
    CONV_TAC WORD_BLAST];;

let TAILLEG = GEN_ALL(prove(swps_tail_goal, swps_tail_tac));;

(* BODYLEG and FILLLEG are proved with a narrower frame, without the tag
   and ivec buffers; WIDEN_LEG_FRAME_RULE restates them with the broad
   frame (ENSURES_FRAME_SUBSUMED). *)
let widen_leg = WIDEN_LEG_FRAME_RULE swps_broad_frame;;
let BODYLEG_BROAD = widen_leg BODYLEG;;
let FILLLEG_BROAD = widen_leg FILLLEG;;

(* ------------------------------------------------------------------------- *)
(* DRAINLEG: swp_inv (loop_count - 2) at pc + 0x1ec -> the bridge state at   *)
(* pc + 0x61c, with the broad frame: BODYLEG_BROAD at i = loop_count - 2, to *)
(* swp_inv (loop_count - 1) at pc + 0x4b0, then REDUCELAST.  It serves both  *)
(* the exit of the loop and the case loop_count = 2.                         *)
(* ------------------------------------------------------------------------- *)
let swps_drain_goal =
  mk_imp(swps_leg_precond,
    list_mk_icomb "ensures" [`arm`;
      leg_state swp_inv `0x1ec` `loop_count - 2` ;
      swps_bridge_post ;
      swps_broad_frame]);;

let DRAINLEG =
    let th = GEN_ALL(prove(swps_drain_goal,
     REPEAT GEN_TAC THEN STRIP_TAC THEN
     REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
     SUBGOAL_THEN `(loop_count - 2) + 1 = loop_count - 1` ASSUME_TAC THENL
      [UNDISCH_TAC `2 <= loop_count` THEN ARITH_TAC; ALL_TAC] THEN
     ENSURES_SEQUENCE_TAC `pc + 0x4b0`
       (rhs(concl((BETA_CONV THENC REWRITE_CONV[ADD_CLAUSES]) (mk_comb(swp_inv,`loop_count - 1`))))) THEN
     CONJ_TAC THENL
      [(* BODYLEG_BROAD at i = loop_count - 2: rewrite the waypoint
          swp_inv (loop_count - 1) of the goal to
          swp_inv ((loop_count - 2) + 1) so that it matches, then discharge
          loop_count - 2 < loop_count - 1. *)
       FIRST_X_ASSUM(fun th -> if concl th = `(loop_count - 2) + 1 = loop_count - 1`
         then REWRITE_TAC[SYM th] else NO_TAC) THEN
       REWRITE_TAC[GSYM MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
       MATCH_MP_TAC BODYLEG_BROAD THEN ASM_REWRITE_TAC[] THEN
       UNDISCH_TAC `2 <= loop_count` THEN ARITH_TAC;
       (* REDUCELAST: key_p occurs only in its hypotheses, so MATCH_MP_TAC
          leaves it existential; supply key_p. *)
       REWRITE_TAC[GSYM MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
       MATCH_MP_TAC REDUCELAST THEN EXISTS_TAC `key_p:int64` THEN ASM_REWRITE_TAC[]])) in
    th;;

(* ------------------------------------------------------------------------- *)
(* MAINLEG: pc + 0x88 -> the bridge state at pc + 0x61c, for                 *)
(* loop_count >= 2: FILLLEG, then for loop_count >= 3 an ENSURES_WHILE_UP    *)
(* over loop_count - 2 iterations with both PCs at the loop head pc + 0x1ec, *)
(* whose body is BODYLEG_BROAD followed by the taken cbnz at pc + 0x4b0, and *)
(* finally DRAINLEG.                                                         *)
(* ------------------------------------------------------------------------- *)

(* The precondition at the end of the preamble, pc + 0x88 (that of FILLLEG). *)
let swps_pre88 = mk_abs(`s:armstate`, list_mk_conj
   [`aligned_bytes_loaded s (word pc) aes128_gcm_enc_tmc`; `read PC s = word (pc + 0x88)`;
    `read X0 s = in_p`; `read X2 s = out_p`; `read X3 s = tag_p`; `read X4 s = ivec_p`;
    `read X6 s = htable_p`; `read SP s = stackpointer`;
    `read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0`;
    `read (memory :> bytes128 ivec_p) s = word_reversefields 8 (ctr_block nonce c)`;
    `read Q18 s = word_reversefields 8 (EL 0 rk)`; `read Q19 s = word_reversefields 8 (EL 1 rk)`;
    `read Q20 s = word_reversefields 8 (EL 2 rk)`; `read Q21 s = word_reversefields 8 (EL 3 rk)`;
    `read Q22 s = word_reversefields 8 (EL 4 rk)`; `read Q23 s = word_reversefields 8 (EL 5 rk)`;
    `read Q24 s = word_reversefields 8 (EL 6 rk)`; `read Q25 s = word_reversefields 8 (EL 7 rk)`;
    `read Q26 s = word_reversefields 8 (EL 8 rk)`; `read Q27 s = word_reversefields 8 (EL 9 rk)`;
    `read X20 s = word_subword (word_reversefields 8 (EL 10 rk):int128) (0,64):int64`;
    `read X21 s = word_subword (word_reversefields 8 (EL 10 rk):int128) (64,64):int64`;
    `read Q7 s = word 13979173243358019584`;
    `read X11 s = word_subword (word_reversefields 8 (ctr_block nonce c):int128) (0,64):int64`;
    `read X12 s = word_zx (word_zx (word_subword
        (word_reversefields 8 (ctr_block nonce c):int128) (64,64):int64):int32):int64`;
    `read X13 s = word_zx (word c:int32):int64`; `read X15 s = word(len_bits DIV 8)`;
    `read X1 s = word loop_count`; `read X7 s = word nblocks`; `read X16 s = word loop_remain`;
    `read Q30 s = byteswap128 tag0`;
    `htable_mem_4 (ghash_twist (aes128_cipher (word 0) rk)) htable_p s`;
    `!j. j < nblocks ==> read (memory :> bytes128 (word_add in_p (word(16*j)))) s = inblock j`]);;

let swps_leg1_goal =
  mk_imp(swps_leg_precond,
    list_mk_icomb "ensures" [`arm`; swps_pre88; swps_bridge_post; swps_broad_frame]);;

(* The invariant of the ENSURES_WHILE_UP is swp_inv itself;
   ENSURES_WHILE_UP_TAC adds the code and PC conjuncts. *)
let swps_while_inv = swp_inv;;

let swps_leg1_tac =
     REPEAT GEN_TAC THEN STRIP_TAC THEN
     (* Expand MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI so that the frame
        idempotence C ,, C = C needed by ENSURES_SEQUENCE_TAC and
        ENSURES_WHILE_UP_TAC can be proved; it is folded back before each
        MATCH_MP_TAC of a leg, whose frame has it folded. *)
     REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
     (* FILLLEG: 0x88 -> 0x1ec, swp_inv 0 *)
     ENSURES_SEQUENCE_TAC `pc + 0x1ec`
       (rhs(concl((BETA_CONV THENC REWRITE_CONV[ADD_CLAUSES]) (mk_comb(swp_inv,`0`))))) THEN
     CONJ_TAC THENL
      [(* Fold the frame back so that it matches that of FILLLEG_BROAD. *)
       REWRITE_TAC[GSYM MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
       MATCH_MP_TAC FILLLEG_BROAD THEN ASM_REWRITE_TAC[];
       ALL_TAC] THEN
     (* Now swp_inv 0 at 0x1ec -> the bridge at 0x61c; split on
        loop_count = 2. *)
     ASM_CASES_TAC `loop_count = 2` THENL
      [(* loop_count = 2: no iterations of the loop, so DRAINLEG directly.  Its
          precondition swp_inv (loop_count - 2) is swp_inv 0 here;
          ENSURES_PRECONDITION_TAC switches to it. *)
       (fun (asl,w) ->
         (* dpre: the code and PC conjuncts and swp_inv (loop_count - 2),
            normalized as the postcondition of FILLLEG is, so that the
            implication between them closes after loop_count = 2 and
            2 - 2 = 0. *)
         let sv = `s:armstate` in
         let invbody = rhs(concl((BETA_CONV THENC REWRITE_CONV[ADD_CLAUSES])
                         (mk_comb(swp_inv,`loop_count - 2`)))) in
         let invbody_s = rhs(concl(BETA_CONV(mk_comb(invbody,sv)))) in
         let dpre = mk_abs(sv, list_mk_conj(
           [`aligned_bytes_loaded s (word pc) aes128_gcm_enc_tmc`;
            `read PC s = word (pc + 0x1ec)`] @ conjuncts invbody_s)) in
         (ENSURES_PRECONDITION_TAC dpre THEN
          CONJ_TAC THENL
           [(* The implication: both sides become the same after
               loop_count = 2 and 2 - 2 = 0. *)
            GEN_TAC THEN
            CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
            ASM_REWRITE_TAC[ARITH_RULE `2 - 2 = 0`; ADD_CLAUSES] THEN
            CONV_TAC(DEPTH_CONV NUM_REDUCE_CONV) THEN
            DISCH_THEN ACCEPT_TAC;
            REWRITE_TAC[GSYM MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
            MATCH_MP_TAC DRAINLEG THEN EXISTS_TAC `key_p:int64` THEN ASM_REWRITE_TAC[]]) (asl,w));
       ALL_TAC] THEN
     (* loop_count >= 3: the ENSURES_WHILE_UP over loop_count - 2 iterations
        at 0x1ec, then DRAINLEG. *)
     ENSURES_WHILE_UP_TAC `loop_count - 2` `pc + 0x1ec` `pc + 0x1ec` swps_while_inv THEN
     REPEAT CONJ_TAC THENL
      [(* ~(loop_count - 2 = 0) *)
       UNDISCH_TAC `~(loop_count = 2)` THEN UNDISCH_TAC `2 <= loop_count` THEN ARITH_TAC;
       (* The initialization: swp_inv 0 at 0x1ec, which FILLLEG established;
          the X1 conjunct needs 0 + 1 = 1. *)
       ENSURES_INIT_TAC "s0" THEN ENSURES_FINAL_STATE_TAC THEN
       REWRITE_TAC[ADD_CLAUSES] THEN ASM_REWRITE_TAC[];
       (* The body: swp_inv i at 0x1ec -> swp_inv (i+1) at 0x1ec, through
          0x4b0: BODYLEG_BROAD, then the taken cbnz. *)
       X_GEN_TAC `i:num` THEN STRIP_TAC THEN
       ENSURES_SEQUENCE_TAC `pc + 0x4b0`
         (rhs(concl((BETA_CONV THENC REWRITE_CONV[ADD_CLAUSES]) (mk_comb(swp_inv,`i+1`))))) THEN
       CONJ_TAC THENL
        [(* BODYLEG_BROAD; its hypotheses follow from those of the body. *)
         REWRITE_TAC[GSYM MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
         MATCH_MP_TAC BODYLEG_BROAD THEN ASM_REWRITE_TAC[] THEN
         MAP_EVERY (fun t -> TRY(UNDISCH_TAC t)) [`i < loop_count - 2`; `2 <= loop_count`] THEN ARITH_TAC;
         (* The cbnz at 0x4b0, taken since X1 = word (loop_count - (i+2)) is
            nonzero for i < loop_count - 2.  htable_mem_4 is expanded in the
            assumptions and in the goal so that its six reads carry over
            the step. *)
         ENSURES_INIT_TAC "s0" THEN
         RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_4]) THEN REWRITE_TAC[htable_mem_4] THEN
         SUBGOAL_THEN `val(word (loop_count - (i + 2)):int64) = loop_count - (i + 2) /\ ~(loop_count - (i+2) = 0)`
         STRIP_ASSUME_TAC THENL
          [CONJ_TAC THENL
            [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
             MAP_EVERY (fun t -> TRY(UNDISCH_TAC t)) [`nblocks DIV 4 = loop_count`; `16 * nblocks < 2 EXP 64`] THEN ARITH_TAC;
             MAP_EVERY (fun t -> TRY(UNDISCH_TAC t)) [`i < loop_count - 2`] THEN ARITH_TAC]; ALL_TAC] THEN
         (* The X1 conjunct of swp_inv (i+1) is word (loop_count-((i+1)+1)),
            i.e. word (loop_count-(i+2)). *)
         RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE `(i+1)+1 = i+2`]) THEN
         ARM_STEPS_TAC AES128_GCM_ENC_EXEC [1] THEN
         RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `val(word (loop_count - (i + 2)):int64) = loop_count - (i + 2)`;
                                     ASSUME `~(loop_count - (i+2) = 0)`; COND_CLAUSES]) THEN
         ENSURES_FINAL_STATE_TAC THEN
         (* What remains is the X1 conjunct, after (i+1)+1 = i+2, and the six
            table reads. *)
         REWRITE_TAC[ARITH_RULE `(i+1)+1 = i+2`] THEN ASM_REWRITE_TAC[]];
       (* The back edge: trivial, both PCs are 0x1ec. *)
       REPEAT STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN ENSURES_FINAL_STATE_TAC THEN
       REWRITE_TAC[ADD_CLAUSES] THEN ASM_REWRITE_TAC[];
       (* The exit: DRAINLEG, supplying key_p. *)
       REWRITE_TAC[GSYM MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
       MATCH_MP_TAC DRAINLEG THEN EXISTS_TAC `key_p:int64` THEN ASM_REWRITE_TAC[]];;

let MAINLEG = GEN_ALL(prove(swps_leg1_goal, swps_leg1_tac));;

(* ------------------------------------------------------------------------- *)
(* MAINLEG_LC1, the case loop_count = 1: pc + 0x88 -> pc + 0x61c in 179      *)
(* steps, the fill 0x88..0x1e8 (89 steps, its cbz at 0x1e8 taken) and then   *)
(* reduce_last 0x4b4..0x618 (90 steps), which finishes group 0.              *)
(* ------------------------------------------------------------------------- *)
let MAINLEG_LC1 = prove
 (`!in_p out_p len_bits tag_p ivec_p key_p htable_p tag0 nonce rk inblock pc
     stackpointer nblocks loop_count loop_remain.
       [EL 0 rk; EL 1 rk; EL 2 rk; EL 3 rk; EL 4 rk; EL 5 rk; EL 6 rk;
        EL 7 rk; EL 8 rk; EL 9 rk; EL 10 rk]:(int128)list = rk /\
       len_bits DIV 128 = nblocks /\ nblocks DIV 4 = loop_count /\
       nblocks MOD 4 = loop_remain /\
       loop_count = 1 /\
       16 * nblocks < 2 EXP 64 /\
       aligned 16 stackpointer /\
       nonoverlapping (out_p,16 * nblocks) (word pc,1856) /\
       nonoverlapping (out_p,16 * nblocks) (in_p,16 * nblocks) /\
       nonoverlapping (out_p,16 * nblocks) (key_p,176) /\
       nonoverlapping (out_p,16 * nblocks) (htable_p,96) /\
       nonoverlapping (tag_p:int64,16) (word pc,1856) /\
       nonoverlapping (tag_p:int64,16) (in_p,16 * nblocks) /\
       nonoverlapping (tag_p:int64,16) (key_p,176) /\
       nonoverlapping (tag_p:int64,16) (htable_p,96) /\
       nonoverlapping (ivec_p:int64,16) (word pc,1856) /\
       nonoverlapping (ivec_p:int64,16) (in_p,16 * nblocks) /\
       nonoverlapping (ivec_p:int64,16) (key_p,176) /\
       nonoverlapping (ivec_p:int64,16) (htable_p,96) /\
       nonoverlapping (word_add stackpointer (word 160),64) (word pc,1856) /\
       nonoverlapping (word_add stackpointer (word 160),64) (in_p,16 * nblocks) /\
       nonoverlapping (word_add stackpointer (word 160),64) (key_p,176) /\
       nonoverlapping (word_add stackpointer (word 160),64) (htable_p,96) /\
       nonoverlapping (out_p,16 * nblocks) (tag_p:int64,16) /\
       nonoverlapping (out_p,16 * nblocks) (ivec_p:int64,16) /\
       nonoverlapping (out_p,16 * nblocks) (word_add stackpointer (word 160),64) /\
       nonoverlapping (tag_p:int64,16) (ivec_p:int64,16) /\
       nonoverlapping (tag_p:int64,16) (word_add stackpointer (word 160),64) /\
       nonoverlapping (ivec_p:int64,16) (word_add stackpointer (word 160),64)
    ==>
    ensures arm
      (\s. aligned_bytes_loaded s (word pc) aes128_gcm_enc_tmc /\
           read PC s = word (pc + 0x88) /\
           read X0 s = in_p /\ read X2 s = out_p /\ read X3 s = tag_p /\
           read X4 s = ivec_p /\ read X6 s = htable_p /\ read SP s = stackpointer /\
           read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
           read (memory :> bytes128 ivec_p) s = word_reversefields 8 (ctr_block nonce c) /\
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
           read X20 s = word_subword (word_reversefields 8 (EL 10 rk):int128) (0,64):int64 /\
           read X21 s = word_subword (word_reversefields 8 (EL 10 rk):int128) (64,64):int64 /\
           read Q7 s = word 13979173243358019584 /\
           read X11 s = word_subword (word_reversefields 8 (ctr_block nonce c):int128) (0,64):int64 /\
           read X12 s = word_zx (word_zx (word_subword
               (word_reversefields 8 (ctr_block nonce c):int128) (64,64):int64):int32):int64 /\
           read X13 s = word_zx (word c:int32):int64 /\ read X15 s = word(len_bits DIV 8) /\
           read X1 s = word loop_count /\ read X7 s = word nblocks /\ read X16 s = word loop_remain /\
           read Q30 s = byteswap128 tag0 /\
           htable_mem_4 (ghash_twist (aes128_cipher (word 0) rk)) htable_p s /\
           (!i. i < nblocks ==> read (memory :> bytes128 (word_add in_p (word(16*i)))) s = inblock i))
      (\s. aligned_bytes_loaded s (word pc) aes128_gcm_enc_tmc /\
           read PC s = word (pc + 0x61c) /\
           read X0 s = word_add in_p (word (64 * loop_count)) /\
        read X2 s = word_add out_p (word (64 * loop_count)) /\
        read X3 s = tag_p /\ read X4 s = ivec_p /\ read X6 s = htable_p /\
        read SP s = stackpointer /\
        read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
        read (memory :> bytes128 ivec_p) s = word_reversefields 8 (ctr_block nonce c) /\
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
        read X20 s = word_subword (word_reversefields 8 (EL 10 rk):int128) (0,64):int64 /\
        read X21 s = word_subword (word_reversefields 8 (EL 10 rk):int128) (64,64):int64 /\
        read Q7 s = word 13979173243358019584 /\
        read X11 s = word_subword (word_reversefields 8 (ctr_block nonce c):int128) (0,64):int64 /\
        read X12 s = word_zx (word_zx (word_subword
            (word_reversefields 8 (ctr_block nonce c):int128) (64,64):int64):int32):int64 /\
        read X13 s = word_zx (word (4 * loop_count + c):int32):int64 /\
        read X15 s = word(len_bits DIV 8) /\ read X1 s = word 0 /\
        read X16 s = word loop_remain /\
        read Q30 s = byteswap128
            (nist_ghash (aes128_cipher (word 0) rk) tag0
               (list_of_seq (nist_cipher_block aes128_cipher c nonce rk inblock) (4 * loop_count))) /\
        htable_mem_4 (ghash_twist (aes128_cipher (word 0) rk)) htable_p s /\
        (!j. j < nblocks ==> read (memory :> bytes128 (word_add in_p (word(16*j)))) s = inblock j) /\
        (!j. j < 4 * loop_count
             ==> read (memory :> bytes128 (word_add out_p (word(16*j)))) s =
                 word_xor (aes_ctr_block aes128_cipher c nonce rk j) (inblock j)))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [X19; X20; X21; X22; X23; X24; X25; X26; X27; X28; X29; X30] ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * nblocks);
                  memory :> bytes(tag_p, 16); memory :> bytes(ivec_p, 16);
                  memory :> bytes(word_add stackpointer (word 160), 64)])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REWRITE_TAC[htable_mem_4] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_4]) THEN
  ENSURES_INIT_TAC "s0" THEN
  (*** The input facts of the four blocks of group 0 (nblocks >= 4) ***)
  SUBGOAL_THEN
   `read (memory :> bytes128 (word_add in_p (word (16 * 0)))) s0 = inblock 0 /\
    read (memory :> bytes128 (word_add in_p (word (16 * 1)))) s0 = inblock 1 /\
    read (memory :> bytes128 (word_add in_p (word (16 * 2)))) s0 = inblock 2 /\
    read (memory :> bytes128 (word_add in_p (word (16 * 3)))) s0 = inblock 3`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `4 <= nblocks` ASSUME_TAC THENL
     [UNDISCH_TAC `nblocks DIV 4 = loop_count` THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
      ALL_TAC] THEN
    REPEAT CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [ARITH_RULE `16 * 0 = 0`; ARITH_RULE `16 * 1 = 16`;
    ARITH_RULE `16 * 2 = 32`; ARITH_RULE `16 * 3 = 48`; WORD_ADD_0]) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o CONV_RULE SPLIT_INPUT_TAIL_CONV o
    check (fun th -> let c = concl th in
      is_eq c && can (find_term (fun t -> t = `(memory :> bytes128 in_p)`)) (lhs c))) THEN
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o CONV_RULE SPLIT_INPUT_CONV o
    check (fun th -> let c = concl th in
      is_eq c && free_in `in_p:int64` (lhs c) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "bytes128")) (lhs c)))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_ADD_0]) THEN
  MAP_EVERY (fun n -> ARM_STEPS_TAC AES128_GCM_ENC_EXEC [n] THEN
    RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV))) (1--11) THEN
  MERGE_CTR128_TAC 192 "s11" THEN
  MAP_EVERY (fun n -> ARM_STEPS_TAC AES128_GCM_ENC_EXEC [n] THEN
    RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV))) (12--12) THEN
  MERGE_CTR128_TAC 176 "s12" THEN
  MAP_EVERY (fun n -> ARM_STEPS_TAC AES128_GCM_ENC_EXEC [n] THEN
    RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV))) (13--19) THEN
  MERGE_CTR128_TAC 160 "s19" THEN
  MAP_EVERY (fun n -> ARM_STEPS_TAC AES128_GCM_ENC_EXEC [n] THEN
    RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV))) (20--24) THEN
  MERGE_CTR128_TAC 208 "s24" THEN
  MAP_EVERY (fun n -> ARM_STEPS_TAC AES128_GCM_ENC_EXEC [n] THEN
    RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV))) (25--31) THEN
  MERGE_CTR128_TAC 192 "s31" THEN
  MAP_EVERY (fun n -> ARM_STEPS_TAC AES128_GCM_ENC_EXEC [n] THEN
    RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV))) (32--37) THEN
  MERGE_CTR128_TAC 208 "s37" THEN
  MAP_EVERY (fun n -> ARM_STEPS_TAC AES128_GCM_ENC_EXEC [n] THEN
    RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV))) (38--96) THEN
  MERGE_CTR128_TAC 176 "s96" THEN
  MAP_EVERY (fun n -> ARM_STEPS_TAC AES128_GCM_ENC_EXEC [n] THEN
    RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV))) (97--116) THEN
  MERGE_CTR128_TAC 160 "s116" THEN
  MAP_EVERY (fun n -> ARM_STEPS_TAC AES128_GCM_ENC_EXEC [n] THEN
    RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV))) (117--179) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_THEN `loop_count = 1` SUBST_ALL_TAC THEN
  CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ARITH_RULE `j < 4 <=> j = 0 \/ j = 1 \/ j = 2 \/ j = 3`] THEN
  ASM_REWRITE_TAC[TAUT `p \/ q ==> r <=> (p ==> r) /\ (q ==> r)`] THEN
  REWRITE_TAC[FORALL_AND_THM; FORALL_UNWIND_THM2] THEN
  REWRITE_TAC[ARITH_RULE `16 * (4 * a + b) = 64 * a + 16 * b`] THEN
  REWRITE_TAC[ARITH_RULE `16 * 4 * i = 64 * i`] THEN
  CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN
  REWRITE_TAC[WORD_ADD_0] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ZX_COUNTER_UD; ZX_COUNTER_INC; CTR_ZX_NORM] THEN
  REWRITE_TAC[GSYM WORD_ADD] THEN
  REWRITE_TAC[ARITH_RULE `(4 * i + 2) + n = 4 * i + (2 + n)`] THEN
  CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
  REWRITE_TAC[(prove(`word 144115188075855872:int64 = word_shl (word_zx (word_bytereverse (word 2:int32)):int64) 32`, CONV_TAC WORD_BLAST));
              (prove(`word 216172782113783808:int64 = word_shl (word_zx (word_bytereverse (word 3:int32)):int64) 32`, CONV_TAC WORD_BLAST));
              (prove(`word 288230376151711744:int64 = word_shl (word_zx (word_bytereverse (word 4:int32)):int64) 32`, CONV_TAC WORD_BLAST));
              (prove(`word 360287970189639680:int64 = word_shl (word_zx (word_bytereverse (word 5:int32)):int64) 32`, CONV_TAC WORD_BLAST))] THEN
  REWRITE_TAC[CTR_BLOCK_BUILD_INSERT] THEN
  REWRITE_TAC[SCALAR_RK_RECONSTRUCT] THEN
  REWRITE_TAC[XOR_AES128_CIPHER_RECONSTRUCT] THEN
  ASM_REWRITE_TAC[MAP; WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
  REWRITE_TAC[aes_ctr_block; GSYM ADD_ASSOC] THEN
  REWRITE_TAC[ARITH_RULE `(1:num) + c = c + 1`; ARITH_RULE `(2:num) + c = c + 2`;
              ARITH_RULE `(3:num) + c = c + 3`; ARITH_RULE `(4:num) + c = c + 4`;
              ARITH_RULE `(0:num) + c = c`] THEN
  CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; GSYM ADD_ASSOC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[WORD_ADD; GSYM WORD_ADD_ASSOC] THEN
  DISCARD_STATE_TAC "s179" THEN
  REWRITE_TAC[ADD_ASSOC; ARITH] THEN
  (*** loop_count = 1, so the blocks are 0..3 with counters c..c+3, which  ***)
  (*** AES_CTR_BLOCK_RECONSTRUCT matches only in its instance i = 0.      ***)
  REWRITE_TAC[REWRITE_RULE[ADD_CLAUSES]
               (INST [`0`,`i:num`] AES_CTR_BLOCK_RECONSTRUCT)] THEN
  REWRITE_TAC[GSYM cipher_block] THEN
  REWRITE_TAC[CIPHER_BLOCK_NIST] THEN
  REWRITE_TAC[WORD_SUBWORD_REVERSEFIELDS] THEN
  SIMP_TAC[WORD_JOIN_COMBINE_LEMMA; ARITH] THEN
  REWRITE_TAC[WORD_SUBWORD_XOR] THEN
  REWRITE_TAC[WORD_SUBWORD_BYTESWAP128] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[WORD_SUBWORD_XOR] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  FIRST_ASSUM(fun th -> if can (term_match []
      `[EL 0 rk; EL 1 rk; EL 2 rk; EL 3 rk; EL 4 rk; EL 5 rk; EL 6 rk;
        EL 7 rk; EL 8 rk; EL 9 rk; EL 10 rk]:(int128)list = rk`) (concl th)
    then REWRITE_TAC[th] else NO_TAC) THEN
  REPEAT(CONJ_TAC THENL
    [CONV_TAC WORD_RULE ORELSE (AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC);
     ALL_TAC]) THEN
  REWRITE_TAC [byteswap128; WORD_BLAST
  `word_subword((word_join:int128->int128->int256) h l) (64,128):int128 =
   word_join (word_subword h (0,64):int64)
             (word_subword l (64,64):int64)`] THEN
  MATCH_MP_TAC(BITBLAST_RULE
   `x:int128 = y
    ==> word_join (word_subword x (0,64):int64)
                  (word_subword x (64,64):int64):int128 =
        word_join (word_subword y (0,64):int64)
                  (word_subword y (64,64):int64):int128`) THEN
  (*** loop_count = 1, so the tag so far is still tag0               ***)
  (*** (nist_ghash h tag0 [] = tag0) and there is no sofar to         ***)
  (*** abbreviate: block 0 enters as word_xor tag0 cipherblock_0.     ***)
  MAP_EVERY ABBREV_TAC
   [`cipherblock_0 = nist_cipher_block aes128_cipher c nonce rk inblock 0`;
    `cipherblock_1 = nist_cipher_block aes128_cipher c nonce rk inblock 1`;
    `cipherblock_2 = nist_cipher_block aes128_cipher c nonce rk inblock 2`;
    `cipherblock_3 = nist_cipher_block aes128_cipher c nonce rk inblock 3`;
    `h0 = h_power (ghash_twist (aes128_cipher (word 0) rk)) 0`;
    `h1 = h_power (ghash_twist (aes128_cipher (word 0) rk)) 1`;
    `h2 = h_power (ghash_twist (aes128_cipher (word 0) rk)) 2`;
    `h3 = h_power (ghash_twist (aes128_cipher (word 0) rk)) 3`] THEN
  REWRITE_TAC[GSYM WORD_SUBWORD_XOR] THEN
  REWRITE_TAC[RECONSTRUCT_POLYVAL_REDUCE_G2] THEN
  TRANS_TAC EQ_TRANS
   `polyval_reduce_prop3
        (word_xor
        (word_pmul (cipherblock_3:int128) (h0:int128))
        (word_xor
        (word_pmul (cipherblock_2:int128) (h1:int128))
        (word_xor
        (word_pmul (cipherblock_1:int128) (h2:int128))
        (word_pmul (word_xor (tag0:int128) cipherblock_0)
                   (h3:int128)))))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[PMUL_KARATSUBA_JOIN_ALT] THEN
    REWRITE_TAC[byteswap128; WORD_SUBWORD_XOR] THEN
    CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
    REWRITE_TAC[karatsuba_mid] THEN
    ASM_REWRITE_TAC[] THEN
    REPEAT(LET_TAC THEN ASM_REWRITE_TAC[]) THEN
    ONCE_REWRITE_TAC[MESON[WORD_XOR_SYM]
     `word_pmul (word_xor a b) (word_xor c d) =
      word_pmul (word_xor b a) (word_xor c d)`] THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[POLYVAL_REDUCE_G2] THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY EXPAND_TAC ["ks"; "ks'"; "ks''"; "ks'''"] THEN
    CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
    AP_TERM_TAC THEN REWRITE_TAC[GSYM karatsuba_join] THEN MATCH_ACCEPT_TAC KARATSUBA_JOIN_XOR4;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`ghash_twist (aes128_cipher (word 0) rk)`;
                 `[cipherblock_1;cipherblock_2;cipherblock_3]:(int128)list`;
                 `tag0:int128`; `cipherblock_0:int128`]
                GHASH_POLYVAL_ACC_BATCHED) THEN
  REWRITE_TAC[LENGTH; ghash_wide] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(MESON[]
   `y' = y /\ x' = x ==> x = y ==> y' = x'`) THEN
  CONJ_TAC THENL [AP_TERM_TAC THEN CONV_TAC WORD_BITWISE_RULE; ALL_TAC] THEN
  REWRITE_TAC[NIST_GHASH_IS_POLYVAL] THEN
  REWRITE_TAC[ARITH_RULE `4 = SUC(SUC(SUC(SUC 0)))`] THEN
  REWRITE_TAC[list_of_seq] THEN REWRITE_TAC[GSYM APPEND_ASSOC] THEN
  REWRITE_TAC[APPEND] THEN
  REWRITE_TAC[GHASH_ACC_APPEND] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ADD1; GSYM ADD_ASSOC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[GSYM NIST_GHASH_IS_POLYVAL]);;


(* ------------------------------------------------------------------------- *)
(* CORE_FROM88: pc + 0x88 -> pc + 0x710, sequenced at the bridge pc + 0x61c. *)
(* The first part splits on loop_count: 0 (the cbz at 0x88 is taken), 1      *)
(* (MAINLEG_LC1) and >= 2 (MAINLEG); the second part is TAILLEG.             *)
(* ------------------------------------------------------------------------- *)
let core_from88_stmt =
  `!in_p out_p len_bits tag_p ivec_p key_p htable_p tag0 nonce rk inblock pc
     stackpointer nblocks loop_count loop_remain.
       [EL 0 rk; EL 1 rk; EL 2 rk; EL 3 rk; EL 4 rk; EL 5 rk; EL 6 rk;
        EL 7 rk; EL 8 rk; EL 9 rk; EL 10 rk]:(int128)list = rk /\
       len_bits DIV 128 = nblocks /\ nblocks DIV 4 = loop_count /\
       nblocks MOD 4 = loop_remain /\
       16 * nblocks < 2 EXP 64 /\
       aligned 16 stackpointer /\
       nonoverlapping (out_p,16 * nblocks) (word pc,1856) /\
       nonoverlapping (out_p,16 * nblocks) (in_p,16 * nblocks) /\
       nonoverlapping (out_p,16 * nblocks) (key_p,176) /\
       nonoverlapping (out_p,16 * nblocks) (htable_p,96) /\
       nonoverlapping (tag_p:int64,16) (word pc,1856) /\
       nonoverlapping (tag_p:int64,16) (in_p,16 * nblocks) /\
       nonoverlapping (tag_p:int64,16) (key_p,176) /\
       nonoverlapping (tag_p:int64,16) (htable_p,96) /\
       nonoverlapping (ivec_p:int64,16) (word pc,1856) /\
       nonoverlapping (ivec_p:int64,16) (in_p,16 * nblocks) /\
       nonoverlapping (ivec_p:int64,16) (key_p,176) /\
       nonoverlapping (ivec_p:int64,16) (htable_p,96) /\
       nonoverlapping (word_add stackpointer (word 160),64) (word pc,1856) /\
       nonoverlapping (word_add stackpointer (word 160),64) (in_p,16 * nblocks) /\
       nonoverlapping (word_add stackpointer (word 160),64) (key_p,176) /\
       nonoverlapping (word_add stackpointer (word 160),64) (htable_p,96) /\
       nonoverlapping (out_p,16 * nblocks) (tag_p:int64,16) /\
       nonoverlapping (out_p,16 * nblocks) (ivec_p:int64,16) /\
       nonoverlapping (out_p,16 * nblocks) (word_add stackpointer (word 160),64) /\
       nonoverlapping (tag_p:int64,16) (ivec_p:int64,16) /\
       nonoverlapping (tag_p:int64,16) (word_add stackpointer (word 160),64) /\
       nonoverlapping (ivec_p:int64,16) (word_add stackpointer (word 160),64)
    ==>
    ensures arm
      (\s. aligned_bytes_loaded s (word pc) aes128_gcm_enc_tmc /\
           read PC s = word (pc + 0x88) /\
           read X0 s = in_p /\ read X2 s = out_p /\ read X3 s = tag_p /\
           read X4 s = ivec_p /\ read X6 s = htable_p /\ read SP s = stackpointer /\
           read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
           read (memory :> bytes128 ivec_p) s = word_reversefields 8 (ctr_block nonce c) /\
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
           read X20 s = word_subword (word_reversefields 8 (EL 10 rk):int128) (0,64):int64 /\
           read X21 s = word_subword (word_reversefields 8 (EL 10 rk):int128) (64,64):int64 /\
           read Q7 s = word 13979173243358019584 /\
           read X11 s = word_subword (word_reversefields 8 (ctr_block nonce c):int128) (0,64):int64 /\
           read X12 s = word_zx (word_zx (word_subword
               (word_reversefields 8 (ctr_block nonce c):int128) (64,64):int64):int32):int64 /\
           read X13 s = word_zx (word c:int32):int64 /\ read X15 s = word(len_bits DIV 8) /\
           read X1 s = word loop_count /\ read X7 s = word nblocks /\ read X16 s = word loop_remain /\
           read Q30 s = byteswap128 tag0 /\
           htable_mem_4 (ghash_twist (aes128_cipher (word 0) rk)) htable_p s /\
           (!i. i < nblocks ==> read (memory :> bytes128 (word_add in_p (word(16*i)))) s = inblock i))
      (\s. read PC s = word (pc + 0x710) /\
           (!i. i < nblocks
                ==> read (memory :> bytes128 (word_add out_p (word(16*i)))) s =
                    word_xor (aes_ctr_block aes128_cipher c nonce rk i) (inblock i)) /\
           read (memory :> bytes128 tag_p) s =
             word_reversefields 8
              (nist_ghash (aes128_cipher (word 0) rk) tag0
                 (list_of_seq (nist_cipher_block aes128_cipher c nonce rk inblock) nblocks)) /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce (nblocks + c)) /\
           read X0 s = word (len_bits DIV 8))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [X19; X20; X21; X22; X23; X24; X25; X26; X27; X28; X29; X30] ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * nblocks);
                  memory :> bytes(tag_p, 16); memory :> bytes(ivec_p, 16);
                  memory :> bytes(word_add stackpointer (word 160), 64)])`;;
let core_from88_tac =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  (*** Sequence at the tail entry pc+0x61c: the first part is the fill, the
   *** loop and the drain, which produce the first 4*loop_count blocks and
   *** their tag; the second part is the single-block tail, TAILLEG.  The
   *** intermediate predicate is the precondition of TAILLEG, the bridge
   *** state. ***)
  ENSURES_SEQUENCE_TAC `pc + 0x61c`
   `\s. read X0 s = word_add in_p (word (64 * loop_count)) /\
        read X2 s = word_add out_p (word (64 * loop_count)) /\
        read X3 s = tag_p /\ read X4 s = ivec_p /\ read X6 s = htable_p /\
        read SP s = stackpointer /\
        read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
        read (memory :> bytes128 ivec_p) s = word_reversefields 8 (ctr_block nonce c) /\
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
        read X20 s = word_subword (word_reversefields 8 (EL 10 rk):int128) (0,64):int64 /\
        read X21 s = word_subword (word_reversefields 8 (EL 10 rk):int128) (64,64):int64 /\
        read Q7 s = word 13979173243358019584 /\
        read X11 s = word_subword (word_reversefields 8 (ctr_block nonce c):int128) (0,64):int64 /\
        read X12 s = word_zx (word_zx (word_subword
            (word_reversefields 8 (ctr_block nonce c):int128) (64,64):int64):int32):int64 /\
        read X13 s = word_zx (word (4 * loop_count + c):int32):int64 /\
        read X15 s = word(len_bits DIV 8) /\ read X1 s = word 0 /\
        read X16 s = word loop_remain /\
        read Q30 s = byteswap128
            (nist_ghash (aes128_cipher (word 0) rk) tag0
               (list_of_seq (nist_cipher_block aes128_cipher c nonce rk inblock) (4 * loop_count))) /\
        htable_mem_4 (ghash_twist (aes128_cipher (word 0) rk)) htable_p s /\
        (!j. j < nblocks ==> read (memory :> bytes128 (word_add in_p (word(16*j)))) s = inblock j) /\
        (!j. j < 4 * loop_count
             ==> read (memory :> bytes128 (word_add out_p (word(16*j)))) s =
                 word_xor (aes_ctr_block aes128_cipher c nonce rk j) (inblock j))` THEN
  CONJ_TAC THENL
   [(*** The first part: fill, loop and drain (pc+0x88 -> pc+0x61c).  Split
     *** on the group count before stepping, so that each case is a plain
     *** ensures goal that a leg theorem closes. ***)
    ASM_CASES_TAC `loop_count = 0` THENL
     [(*** loop_count = 0: the cbz at 0x88 is taken to 0x61c and nothing is
       *** produced (the tag is still nist_ghash ... [] = tag0).  Substitute
       *** loop_count = 0 before ENSURES_INIT_TAC, after which FIRST_X_ASSUM
       *** would pick a read equation. ***)
      UNDISCH_THEN `loop_count = 0` SUBST_ALL_TAC THEN
      ENSURES_INIT_TAC "s0" THEN
      RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_4]) THEN
      ARM_STEPS_TAC AES128_GCM_ENC_EXEC [1] THEN
      ENSURES_FINAL_STATE_TAC THEN
      ASM_REWRITE_TAC[htable_mem_4; MULT_CLAUSES; ADD_CLAUSES; WORD_ADD_0;
                      list_of_seq; nist_ghash] THEN
      REWRITE_TAC[CONJUNCT1 LT];
      (*** loop_count >= 1: the fill 0x8c..0x1e4, then the cbz at 0x1e8.  For
       *** loop_count = 1 it is taken into reduce_last (MAINLEG_LC1); for
       *** loop_count >= 2 it falls through to the loop head 0x1ec
       *** (MAINLEG). ***)
      ASM_CASES_TAC `loop_count = 1` THENL
       [(*** loop_count = 1: MAINLEG_LC1.  key_p occurs only in its
         *** hypotheses, so MATCH_MP_TAC leaves it existential; supply it,
         *** and ASM_REWRITE_TAC discharges the hypotheses. ***)
        REWRITE_TAC[GSYM MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
        MATCH_MP_TAC MAINLEG_LC1 THEN
        EXISTS_TAC `key_p:int64` THEN ASM_REWRITE_TAC[];
        (*** loop_count >= 2: MAINLEG (fill, loop at 0x1ec, DRAINLEG), after
         *** folding the ABI frame back; supply key_p.  ASM_REWRITE_TAC
         *** discharges every hypothesis except 2 <= loop_count. ***)
        REWRITE_TAC[GSYM MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
        MATCH_MP_TAC MAINLEG THEN
        EXISTS_TAC `key_p:int64` THEN ASM_REWRITE_TAC[] THEN
        (* 2 <= loop_count, from ~(loop_count = 0) and ~(loop_count = 1) *)
        ASM_ARITH_TAC]];
    (*** The second part: the single-block tail (pc+0x61c -> pc+0x710),
     *** TAILLEG.  key_p occurs only in its hypotheses, so MATCH_MP_TAC
     *** leaves it existential; supply it, and ASM_REWRITE_TAC discharges
     *** the hypotheses (the round-key list and 16 * nblocks < 2 EXP 64 are
     *** assumptions of CORE_FROM88). ***)
    REWRITE_TAC[GSYM MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    MATCH_MP_TAC TAILLEG THEN
    EXISTS_TAC `key_p:int64` THEN ASM_REWRITE_TAC[]];;
let CORE_FROM88 = prove(core_from88_stmt, core_from88_tac);;

(* ------------------------------------------------------------------------- *)
(* The core correctness theorem.                                             *)
(*                                                                           *)
(* This covers the body of the function without the register saves and       *)
(* restores: the PC starts at pc + 0x2c, the first instruction after the 11  *)
(* save instructions, and ends at pc + 0x710, the first restore              *)
(* (ldp d8,d9).  The stackpointer is the value after the sub sp,sp,#0xe0,    *)
(* i.e. the value the SP register holds inside the function body.            *)
(*                                                                           *)
(* Arguments (standard ARM ABI, values in registers at core entry):          *)
(*   X0 = in        input buffer (len_bits/8 bytes)                          *)
(*   X1 = len_bits  length in bits (len_bits DIV 128 whole blocks are done)  *)
(*   X2 = out       output buffer (len_bits/8 bytes)                         *)
(*   X3 = tag       16-byte GHASH accumulator (in/out)                       *)
(*   X4 = ivec      16-byte counter block (in/out)                           *)
(*   X5 = key       AES-128 round keys (176 bytes = 11 x 16)                 *)
(*   X6 = Htable    precomputed H-powers table (first 96 bytes read)         *)
(*   returns X0 = len_bits DIV 8                                             *)
(* ------------------------------------------------------------------------- *)

(*** The NIST-level specifications read byte strings as big-endian words, so
 *** the round keys rk, the counter block ctr_block nonce c and the tag tag0
 *** are NIST-order words.  The kernel loads them in the usual little-endian
 *** ARM fashion, so the precondition gives the memory contents as their byte
 *** reversals; the data blocks inblock i are the lane-order values of the
 *** loads themselves.
 ***)
let AES128_GCM_ENC_CORRECT = prove
 (`!in_p out_p len_bits tag_p ivec_p key_p htable_p tag0 nonce c rk inblock pc
     stackpointer.
       aligned 16 stackpointer /\
       ALLPAIRS nonoverlapping
        [(out_p, 16 * val len_bits DIV 128); (tag_p, 16); (ivec_p, 16);
         (word_add stackpointer (word 160), 64)]
        [(word pc, LENGTH aes128_gcm_enc_tmc);
         (in_p,  16 * val len_bits DIV 128); (key_p, 176); (htable_p, 96)] /\
       PAIRWISE nonoverlapping
        [(out_p, 16 * val len_bits DIV 128); (tag_p, 16); (ivec_p, 16);
         (word_add stackpointer (word 160), 64)]
    ==>
    ensures arm
      (\s. aligned_bytes_loaded s (word pc) aes128_gcm_enc_tmc /\
           read PC s = word (pc + 0x2c) /\
           read SP s = stackpointer /\
           C_ARGUMENTS
            [in_p; len_bits; out_p; tag_p; ivec_p; key_p; htable_p] s /\
           read (memory :> bytes128 tag_p)  s = word_reversefields 8 tag0 /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce c) /\
           wordlist_from_memory(key_p,11) s =
             MAP (word_reversefields 8) rk /\
           (!i. i < val len_bits DIV 128
                ==> read (memory :> bytes128 (word_add in_p (word(16*i)))) s =
                    inblock i) /\
           htable_mem_4 (ghash_twist (aes128_cipher (word 0) rk))
                      htable_p s)
      (\s. read PC s = word (pc + 0x710) /\
           (!i. i < val len_bits DIV 128
                ==> read (memory :> bytes128 (word_add out_p (word(16*i)))) s =
                    word_xor (aes_ctr_block aes128_cipher c nonce rk i) (inblock i)) /\
           read (memory :> bytes128 tag_p) s =
             word_reversefields 8
              (nist_ghash (aes128_cipher (word 0) rk) tag0
                 (list_of_seq (nist_cipher_block aes128_cipher c nonce rk inblock)
                              (val len_bits DIV 128))) /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8
               (ctr_block nonce (val len_bits DIV 128 + c)) /\
           read X0 s = word (val len_bits DIV 8))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [X19; X20; X21; X22; X23; X24;
                  X25; X26; X27; X28; X29; X30] ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * val len_bits DIV 128);
                  memory :> bytes(tag_p, 16);
                  memory :> bytes(ivec_p, 16);
                  memory :> bytes(word_add stackpointer (word 160), 64)])`,
  (*** setup boilerplate ***)
  GEN_TAC THEN GEN_TAC THEN W64_GEN_TAC `len_bits:num` THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REWRITE_TAC[ALLPAIRS; PAIRWISE; ALL; fst AES128_GCM_ENC_EXEC] THEN
  ABBREV_TAC `nblocks = len_bits DIV 128` THEN
  ABBREV_TAC `loop_count = nblocks DIV 4` THEN
  ABBREV_TAC `loop_remain = nblocks MOD 4` THEN STRIP_TAC THEN
  CONV_TAC(ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN REWRITE_TAC[WORD_ADD_0] THEN
  (*** round-key list length split ***)
  ASM_CASES_TAC `LENGTH(rk:int128 list) = 11` THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [LENGTH_EQ_LIST_OF_SEQ]) THEN
    CONV_TAC(LAND_CONV(RAND_CONV LIST_OF_SEQ_CONV)) THEN
    DISCH_THEN(ASSUME_TAC o SYM) THEN
    CONV_TAC(ONCE_DEPTH_CONV WORDLIST_FROM_MEMORY_CONV) THEN
    EXPAND_TAC "rk" THEN REWRITE_TAC[MAP; CONS_11; GSYM CONJ_ASSOC] THEN ASM_REWRITE_TAC[];
    ENSURES_INIT_TAC "s0" THEN
    FIRST_ASSUM(MP_TAC o AP_TERM `LENGTH:int128 list->num`) THEN
    ASM_REWRITE_TAC[LENGTH_WORDLIST_FROM_MEMORY; LENGTH_MAP]] THEN
  (*** Sequence at the end of the preamble, pc+0x88: the first part is the
   *** preamble, the second CORE_FROM88 ***)
  ENSURES_SEQUENCE_TAC `pc + 0x88`
   `\s. read X0 s = in_p /\ read X2 s = out_p /\ read X3 s = tag_p /\
        read X4 s = ivec_p /\ read X6 s = htable_p /\ read SP s = stackpointer /\
        read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
        read (memory :> bytes128 ivec_p) s = word_reversefields 8 (ctr_block nonce c) /\
        read Q18 s = word_reversefields 8 (EL 0 rk) /\ read Q19 s = word_reversefields 8 (EL 1 rk) /\
        read Q20 s = word_reversefields 8 (EL 2 rk) /\ read Q21 s = word_reversefields 8 (EL 3 rk) /\
        read Q22 s = word_reversefields 8 (EL 4 rk) /\ read Q23 s = word_reversefields 8 (EL 5 rk) /\
        read Q24 s = word_reversefields 8 (EL 6 rk) /\ read Q25 s = word_reversefields 8 (EL 7 rk) /\
        read Q26 s = word_reversefields 8 (EL 8 rk) /\ read Q27 s = word_reversefields 8 (EL 9 rk) /\
        read X20 s = word_subword (word_reversefields 8 (EL 10 rk):int128) (0,64):int64 /\
        read X21 s = word_subword (word_reversefields 8 (EL 10 rk):int128) (64,64):int64 /\
        read Q7 s = word 13979173243358019584 /\
        read X11 s = word_subword (word_reversefields 8 (ctr_block nonce c):int128) (0,64):int64 /\
        read X12 s = word_zx (word_zx (word_subword
            (word_reversefields 8 (ctr_block nonce c):int128) (64,64):int64):int32):int64 /\
        read X13 s = word_zx (word c:int32):int64 /\ read X15 s = word(len_bits DIV 8) /\
        read X1 s = word loop_count /\ read X7 s = word nblocks /\ read X16 s = word loop_remain /\
        read Q30 s = byteswap128 tag0 /\
        htable_mem_4 (ghash_twist (aes128_cipher (word 0) rk)) htable_p s /\
        (!i. i < nblocks ==> read (memory :> bytes128 (word_add in_p (word(16*i)))) s = inblock i)` THEN
  CONJ_TAC THENL
   [(*** The preamble: pc+0x2c -> pc+0x88 ***)
    REWRITE_TAC[htable_mem_4; GSYM CONJ_ASSOC] THEN
    ENSURES_INIT_TAC "s0" THEN
    UNDISCH_TAC `read (memory :> bytes128 ivec_p) s0 = word_reversefields 8 (ctr_block nonce c)` THEN
    GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [el 1 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT)] THEN
    DISCH_TAC THEN
    ABBREV_TAC `ivlo:int64 = read (memory :> bytes64 ivec_p) s0` THEN
    ABBREV_TAC `ivhi:int64 = read (memory :> bytes64 (word_add ivec_p (word 8))) s0` THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o CONV_RULE(READ_MEMORY_SPLIT_CONV 1) o
      check (fun th -> let c = concl th in
        is_eq c && free_in `key_p:int64` (lhs c) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "bytes128")) (lhs c) &&
        can (find_term (fun t -> t = `160`)) (lhs c))) THEN
    ARM_STEPS_TAC AES128_GCM_ENC_EXEC (1--23) THEN ENSURES_FINAL_STATE_TAC THEN
    FIRST_ASSUM(fun th ->
      if can (term_match [] `word_join (ivhi:int64) (ivlo:int64):int128 = xx`) (concl th)
      then ASSUME_TAC th else NO_TAC) THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [GEN_REWRITE_TAC LAND_CONV [el 1 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT)] THEN ASM_REWRITE_TAC[];
      FIRST_ASSUM(fun th -> if can (term_match [] `word_join (ivhi:int64) (ivlo:int64):int128 = xx`) (concl th)
        then ACCEPT_TAC(MATCH_MP X11_SETUP th) else NO_TAC);
      FIRST_ASSUM(fun th -> if can (term_match [] `word_join (ivhi:int64) (ivlo:int64):int128 = xx`) (concl th)
        then ACCEPT_TAC(MATCH_MP X12_SETUP th) else NO_TAC);
      FIRST_ASSUM(fun th -> if can (term_match [] `word_join (ivhi:int64) (ivlo:int64):int128 = xx`) (concl th)
        then ACCEPT_TAC(MATCH_MP X13_SETUP th) else NO_TAC);
      ASM_REWRITE_TAC[word_ushr] THEN AP_TERM_TAC THEN ARITH_TAC;
      REWRITE_TAC[WORD_USHR_COMPOSE] THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
      ASM_REWRITE_TAC[word_ushr] THEN MAP_EVERY EXPAND_TAC ["loop_count"; "nblocks"] THEN
      REWRITE_TAC[DIV_DIV] THEN AP_TERM_TAC THEN CONV_TAC NUM_REDUCE_CONV;
      REWRITE_TAC[WORD_USHR_COMPOSE] THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
      ASM_REWRITE_TAC[word_ushr] THEN EXPAND_TAC "nblocks" THEN
      AP_TERM_TAC THEN CONV_TAC NUM_REDUCE_CONV;
      REWRITE_TAC[WORD_USHR_COMPOSE] THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
      ASM_REWRITE_TAC[word_ushr] THEN REWRITE_TAC[ARITH_RULE `3 = 2 EXP 2 - 1`] THEN
      REWRITE_TAC[WORD_AND_MASK_WORD; VAL_WORD; DIMINDEX_64] THEN REWRITE_TAC[MOD_MOD_EXP_MIN] THEN
      MAP_EVERY EXPAND_TAC ["loop_remain"; "nblocks"] THEN
      AP_TERM_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC;
      REWRITE_TAC[byteswap128] THEN CONV_TAC WORD_BLAST];
    (*** The rest, pc+0x88 -> pc+0x710: CORE_FROM88.  htable_mem_4 stays
         folded here (only the preamble part expanded it); fold the ABI
         frame back so that the goal is an instance of CORE_FROM88.  key_p
         occurs only in its hypotheses, so MATCH_MP_TAC leaves an
         existential, satisfied by key_p. ***)
    REWRITE_TAC[GSYM MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    MATCH_MP_TAC CORE_FROM88 THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `key_p:int64` THEN ASM_REWRITE_TAC[] THEN
    (*** The hypothesis 16 * nblocks < 2 EXP 64 of CORE_FROM88:          ***)
    (*** nblocks is len_bits DIV 128 and len_bits < 2 EXP 64 (W64_GEN_TAC) ***)
    EXPAND_TAC "nblocks" THEN
    UNDISCH_TAC `len_bits < 2 EXP 64` THEN ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The subroutine form for the trimmed code: ARM_ADD_RETURN_STACK_TAC adds   *)
(* the prologue and the epilogue (11 instructions each), which save and      *)
(* restore the callee-saved registers in a 224-byte frame.                   *)
(* ------------------------------------------------------------------------- *)

let AES128_GCM_ENC_NOIBT_SUBROUTINE_CORRECT = prove
 (`!in_p out_p len_bits tag_p ivec_p key_p htable_p tag0 nonce c rk inblock
    pc stackpointer returnaddress.
    aligned 16 stackpointer /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * val len_bits DIV 128); (tag_p, 16); (ivec_p, 16);
       (word_sub stackpointer (word 224), 224)]
      [(word pc, LENGTH aes128_gcm_enc_tmc);
       (in_p,  16 * val len_bits DIV 128); (key_p, 176); (htable_p, 96)] /\
    PAIRWISE nonoverlapping
      [(out_p, 16 * val len_bits DIV 128); (tag_p, 16); (ivec_p, 16);
       (word_sub stackpointer (word 224), 224)]
    ==>
    ensures arm
      (\s. aligned_bytes_loaded s (word pc) aes128_gcm_enc_tmc /\
           read PC s = word pc /\
           read SP s = stackpointer /\
           read X30 s = returnaddress /\
           C_ARGUMENTS
            [in_p; len_bits; out_p; tag_p; ivec_p; key_p; htable_p] s /\
           read (memory :> bytes128 tag_p)  s = word_reversefields 8 tag0 /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce c) /\
           wordlist_from_memory(key_p,11) s =
             MAP (word_reversefields 8) rk /\
           (!i. i < val len_bits DIV 128
                ==> read (memory :> bytes128 (word_add in_p (word(16*i)))) s =
                    inblock i) /\
           htable_mem_4 (ghash_twist (aes128_cipher (word 0) rk))
                      htable_p s)
      (\s. read PC s = returnaddress /\
           (!i. i < val len_bits DIV 128
                ==> read (memory :> bytes128 (word_add out_p (word(16*i)))) s =
                    word_xor (aes_ctr_block aes128_cipher c nonce rk i) (inblock i)) /\
           read (memory :> bytes128 tag_p) s =
             word_reversefields 8
              (nist_ghash (aes128_cipher (word 0) rk) tag0
                 (list_of_seq (nist_cipher_block aes128_cipher c nonce rk inblock)
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
  REWRITE_TAC[fst AES128_GCM_ENC_EXEC; htable_mem_4] THEN
  CONV_TAC(ONCE_DEPTH_CONV WORDLIST_FROM_MEMORY_CONV) THEN
  ARM_ADD_RETURN_STACK_TAC
    ~pre_post_nsteps:(11, 11)
    AES128_GCM_ENC_EXEC
    (CONV_RULE(ONCE_DEPTH_CONV WORDLIST_FROM_MEMORY_CONV)
       (REWRITE_RULE[fst AES128_GCM_ENC_EXEC; htable_mem_4]
          AES128_GCM_ENC_CORRECT))
    `[X19; X20; X21; X22; X23; X24; X25; X26; X27; X28; X29; X30;
      D8; D9; D10; D11; D12; D13; D14; D15]` 224);;

(* The same for the full code, with its BTI landing pad. *)

let AES128_GCM_ENC_SUBROUTINE_CORRECT = prove
 (`!in_p out_p len_bits tag_p ivec_p key_p htable_p tag0 nonce c rk inblock
    pc stackpointer returnaddress.
    aligned 16 stackpointer /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * val len_bits DIV 128); (tag_p, 16); (ivec_p, 16);
       (word_sub stackpointer (word 224), 224)]
      [(word pc, LENGTH aes128_gcm_enc_mc);
       (in_p,  16 * val len_bits DIV 128); (key_p, 176); (htable_p, 96)] /\
    PAIRWISE nonoverlapping
      [(out_p, 16 * val len_bits DIV 128); (tag_p, 16); (ivec_p, 16);
       (word_sub stackpointer (word 224), 224)]
    ==>
    ensures arm
      (\s. aligned_bytes_loaded s (word pc) aes128_gcm_enc_mc /\
           read PC s = word pc /\
           read SP s = stackpointer /\
           read X30 s = returnaddress /\
           C_ARGUMENTS
            [in_p; len_bits; out_p; tag_p; ivec_p; key_p; htable_p] s /\
           read (memory :> bytes128 tag_p)  s = word_reversefields 8 tag0 /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce c) /\
           wordlist_from_memory(key_p,11) s =
             MAP (word_reversefields 8) rk /\
           (!i. i < val len_bits DIV 128
                ==> read (memory :> bytes128 (word_add in_p (word(16*i)))) s =
                    inblock i) /\
           htable_mem_4 (ghash_twist (aes128_cipher (word 0) rk))
                      htable_p s)
      (\s. read PC s = returnaddress /\
           (!i. i < val len_bits DIV 128
                ==> read (memory :> bytes128 (word_add out_p (word(16*i)))) s =
                    word_xor (aes_ctr_block aes128_cipher c nonce rk i) (inblock i)) /\
           read (memory :> bytes128 tag_p) s =
             word_reversefields 8
              (nist_ghash (aes128_cipher (word 0) rk) tag0
                 (list_of_seq (nist_cipher_block aes128_cipher c nonce rk inblock)
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
    aes128_gcm_enc_mc aes128_gcm_enc_tmc AES128_GCM_ENC_NOIBT_SUBROUTINE_CORRECT));;

(* ========================================================================= *)
(* Constant-time and memory safety.                                          *)
(*                                                                           *)
(* AES128_GCM_ENC_SAFE covers the same core as AES128_GCM_ENC_CORRECT        *)
(* (pc + 0x2c .. pc + 0x710); AES128_GCM_ENC_SUBROUTINE_SAFE is the whole    *)
(* function, obtained from it as the correctness theorem is.                 *)
(*                                                                           *)
(* The outer `exists f_events. forall <public args> ...` says that the event *)
(* trace is a function of the public arguments only (independent of the      *)
(* secret plaintext and key bytes), i.e. constant time; the                  *)
(* memaccess_inbounds conjunct says that every load and store stays within   *)
(* the declared buffers, i.e. memory safety.  The proof splits at the end of *)
(* the 4-block loop, pc + 0x61c.  The main region splits on loop_count: 0,   *)
(* 1, 2, and loop_count >= 3 with an ENSURES_EVENTS_WHILE_UP2 of             *)
(* loop_count - 1 iterations from the loop head pc + 0x1ec between the fill  *)
(* and reduce_last (pc + 0x4b4).  The tail is a loop over the loop_remain    *)
(* remaining blocks (pc + 0x62c, exit pc + 0x6fc).                           *)
(* ========================================================================= *)

let EXEC = AES128_GCM_ENC_EXEC;;

let SAFE_SIM = SAFE_SIM_TAC EXEC;;

(* Closers specific to the pipelined loop. *)

(* The steady-state loop runs loop_count - 1 times, so at the drain the      *)
(* pointers are base + 64*(loop_count-1), while the split point after it has *)
(* base + 64*loop_count.  DRAIN_ADDR writes loop_count as                    *)
(* (loop_count - 1) + 1 so that WORD_RULE sees only linear combinations.     *)
let DRAIN_ADDR = DRAIN_ADDR_K `1`;;

let OPEN_ENC = OPEN_SWP_SAFE EXEC;;

(* The event scaffold: e2 = APPEND (tail events) (APPEND (main events)       *)
(* (prologue events)).  The main region has four paths: loop_count = 0       *)
(* (f_ev_m0), 1 (f_ev_m1, the fill and reduce_last), 2 (f_ev_m2), and >= 3   *)
(* (the fill, ENUMERATEL (loop_count - 1) steady iterations and the drain).  *)
let scaffold_enc =
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
        else if val len_bits DIV 128 DIV 4 = 2 then
          f_ev_m2 in_p out_p tag_p ivec_p key_p htable_p len_bits pc stackpointer
        else
          APPEND
            (f_ev_drain in_p out_p tag_p ivec_p key_p htable_p len_bits pc stackpointer)
            (APPEND
              (ENUMERATEL (val len_bits DIV 128 DIV 4 - 1)
                (\i. f_ev_steady in_p out_p tag_p ivec_p key_p htable_p len_bits pc stackpointer i))
              (f_ev_fill in_p out_p tag_p ivec_p key_p htable_p len_bits pc stackpointer)))
       (f_ev_pro in_p out_p tag_p ivec_p key_p htable_p len_bits pc stackpointer))
   :(uarch_event) list`;;

let AES128_GCM_ENC_SAFE = prove
 (`exists f_events.
    forall e in_p len_bits out_p tag_p ivec_p key_p htable_p pc stackpointer.
      aligned 16 stackpointer /\
      ALLPAIRS nonoverlapping
        [(out_p, 16 * val len_bits DIV 128); (tag_p, 16); (ivec_p, 16);
         (word_add stackpointer (word 160), 64)]
        [(word pc, LENGTH aes128_gcm_enc_tmc);
         (in_p,  16 * val len_bits DIV 128); (key_p, 176); (htable_p, 96)] /\
      PAIRWISE nonoverlapping
        [(out_p, 16 * val len_bits DIV 128); (tag_p, 16); (ivec_p, 16);
         (word_add stackpointer (word 160), 64)]
      ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) aes128_gcm_enc_tmc /\
               read PC s = word (pc + 0x2c) /\
               read SP s = stackpointer /\
               C_ARGUMENTS [in_p; len_bits; out_p; tag_p; ivec_p; key_p; htable_p] s /\
               read events s = e)
          (\s. read PC s = word (pc + 0x710) /\
               (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events in_p out_p tag_p ivec_p key_p htable_p len_bits pc stackpointer /\
                    memaccess_inbounds e2
                      [in_p, 16 * val len_bits DIV 128; tag_p, 16; ivec_p, 16; key_p, 176; htable_p, 96;
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
  CONCRETIZE_F_EVENTS_TAC scaffold_enc THEN
  OPEN_ENC THEN

  (*** Split at 0x61c, the main region and the tail region. ***)
  ENSURES_EVENTS_SEQUENCE_TAC `pc + 0x61c`
   `\s. read X0 s = word_add in_p (word (64 * loop_count)) /\
        read X2 s = word_add out_p (word (64 * loop_count)) /\
        read X3 s = tag_p /\ read X4 s = ivec_p /\ read X6 s = htable_p /\
        read SP s = stackpointer /\ read X16 s = word loop_remain` THEN
  CONJ_TAC THENL
   [(*** The main region pc+0x2c -> pc+0x61c: the preamble and the loop. ***)
    ENSURES_EVENTS_SEQUENCE_TAC `pc + 0x88`
     `\s. read X0 s = in_p /\ read X2 s = out_p /\ read X3 s = tag_p /\
          read X4 s = ivec_p /\ read X6 s = htable_p /\ read SP s = stackpointer /\
          read X1 s = word loop_count /\ read X16 s = word loop_remain` THEN
    CONJ_TAC THENL [SAFE_SIM (1--23) THEN CLOSE; ALL_TAC] THEN

    (*** loop_count = 0: the cbz at 0x88 is taken to 0x61c. ***)
    ASM_CASES_TAC `loop_count = 0` THENL
     [REDUCE_IF0 `loop_count:num` THEN SAFE_SIM (1--1) THEN CLOSE; ALL_TAC] THEN
    REDUCE_IFN0 `loop_count:num` THEN

    (*** loop_count = 1: the fill (the cbz at 0x1e8 taken), reduce_last. ***)
    ASM_CASES_TAC `loop_count = 1` THENL
     [REDUCE_IFEQ `loop_count:num` `1` THEN SAFE_SIM (1--179) THEN CLOSE; ALL_TAC] THEN
    REDUCE_IFNE `loop_count:num` `1` THEN

    (*** loop_count = 2: the fill, one iteration (the cbnz at 0x4b0 falls ***)
    (*** through) and reduce_last.                                         ***)
    ASM_CASES_TAC `loop_count = 2` THENL
     [REDUCE_IFEQ `loop_count:num` `2` THEN SAFE_SIM (1--357) THEN CLOSE; ALL_TAC] THEN
    REDUCE_IFNE `loop_count:num` `2` THEN

    (*** loop_count >= 3: the fill, loop_count - 1 iterations and          ***)
    (*** reduce_last.  The fill does not load block 0, so at iteration i   ***)
    (*** X0/X2 are advanced by 64*i, and X1 = word (loop_count - 1 - i).   ***)
    SUBGOAL_THEN `3 <= loop_count` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ENSURES_EVENTS_WHILE_UP2_TAC `loop_count - 1` `pc + 0x1ec` `pc + 0x4b4`
     `\i s. read X0 s = word_add in_p (word (64 * i)) /\
            read X2 s = word_add out_p (word (64 * i)) /\
            read X3 s = tag_p /\ read X4 s = ivec_p /\ read X6 s = htable_p /\
            read SP s = stackpointer /\ read X16 s = word loop_remain /\
            read X1 s = word (loop_count - 1 - i)` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [(*** ~(loop_count - 1 = 0) ***)
      ASM_ARITH_TAC;
      (*** The fill: 0x88 -> 0x1ec, the invariant at 0.  BEQ_NZ `1`      ***)
      (*** gives the condition of the cbz at 0x1e8; the conjuncts left    ***)
      (*** are X0, X2, X1 and the events.                                ***)
      BEQ_NZ `1` THEN SAFE_SIM (1--89) THEN
      BEQ_NZ `2` THEN
      REPEAT CONJ_TAC THENL
       [ADDR_RECON;
        ADDR_RECON;
        (* X1 = word(loop_count - 1 - 0) *)
        REWRITE_TAC[SUB_0] THEN GEN_REWRITE_TAC RAND_CONV [WORD_SUB] THEN
        ASM_SIMP_TAC[ARITH_RULE `3 <= loop_count ==> 1 <= loop_count`];
        DEABBR THEN DISCHARGE_SAFETY_PROPERTY_TAC];
      (*** The body: one iteration, from 0x1ec back to 0x1ec, or to 0x4b4 ***)
      (*** after the last one.                                             ***)
      REWRITE_TAC[] THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
      SUBGOAL_THEN `loop_count - 1 < 2 EXP 64` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      SAFE_SIM (1--178) THEN CLOSE_R2;
      (*** The exit: reduce_last, 0x4b4 -> 0x61c. ***)
      SAFE_SIM (1--90) THEN REPEAT CONJ_TAC THENL
       [DRAIN_ADDR; DRAIN_ADDR; DEABBR THEN DISCHARGE_SAFE_ROBUST]];

    ALL_TAC] THEN

  (*** The tail region pc+0x61c -> pc+0x710: a loop over loop_remain     ***)
  (*** blocks, head 0x62c and exit 0x6fc, then the tag and counter stores. ***)
  ASM_CASES_TAC `loop_remain = 0` THENL
   [REDUCE_IF0 `loop_remain:num` THEN SAFE_SIM (1--9) THEN CLOSE_R2; ALL_TAC] THEN
  REDUCE_IFN0 `loop_remain:num` THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `loop_remain:num` `pc + 0x62c` `pc + 0x6fc`
   `\i s. read X0 s = word_add in_p (word (64 * loop_count + 16 * i)) /\
          read X2 s = word_add out_p (word (64 * loop_count + 16 * i)) /\
          read X3 s = tag_p /\ read X4 s = ivec_p /\ read X6 s = htable_p /\
          read SP s = stackpointer /\ read X16 s = word (loop_remain - i)` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [SAFE_SIM (1--4) THEN CLOSE_R2;
    ALL_TAC;
    REWRITE_TAC[] THEN SAFE_SIM (1--5) THEN CLOSE_R2] THEN
  REWRITE_TAC[] THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
  SAFE_SIM (1--52) THEN CLOSE_R2);;

(* ------------------------------------------------------------------------- *)
(* The whole-function version, obtained from the core theorem exactly as the *)
(* correctness theorem is: the 11-instruction prologue and epilogue save and *)
(* restore the callee-saved registers in a 224-byte frame.                   *)
(* ------------------------------------------------------------------------- *)
let AES128_GCM_ENC_NOIBT_SUBROUTINE_SAFE = prove
 (`exists f_events.
    forall e in_p len_bits out_p tag_p ivec_p key_p htable_p pc stackpointer returnaddress.
      aligned 16 stackpointer /\
      ALLPAIRS nonoverlapping
        [(out_p, 16 * val len_bits DIV 128); (tag_p, 16); (ivec_p, 16);
         (word_sub stackpointer (word 224), 224)]
        [(word pc, LENGTH aes128_gcm_enc_tmc);
         (in_p,  16 * val len_bits DIV 128); (key_p, 176); (htable_p, 96)] /\
      PAIRWISE nonoverlapping
        [(out_p, 16 * val len_bits DIV 128); (tag_p, 16); (ivec_p, 16);
         (word_sub stackpointer (word 224), 224)]
      ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) aes128_gcm_enc_tmc /\
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
                      [in_p, 16 * val len_bits DIV 128; tag_p, 16; ivec_p, 16; key_p, 176; htable_p, 96;
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
    AES128_GCM_ENC_EXEC AES128_GCM_ENC_SAFE
    `[X19; X20; X21; X22; X23; X24; X25; X26; X27; X28; X29; X30;
      D8; D9; D10; D11; D12; D13; D14; D15]` 224 THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

(* The same for the full code, with its BTI landing pad. *)

let AES128_GCM_ENC_SUBROUTINE_SAFE = prove
 (`exists f_events.
    forall e in_p len_bits out_p tag_p ivec_p key_p htable_p pc stackpointer returnaddress.
      aligned 16 stackpointer /\
      ALLPAIRS nonoverlapping
        [(out_p, 16 * val len_bits DIV 128); (tag_p, 16); (ivec_p, 16);
         (word_sub stackpointer (word 224), 224)]
        [(word pc, LENGTH aes128_gcm_enc_mc);
         (in_p,  16 * val len_bits DIV 128); (key_p, 176); (htable_p, 96)] /\
      PAIRWISE nonoverlapping
        [(out_p, 16 * val len_bits DIV 128); (tag_p, 16); (ivec_p, 16);
         (word_sub stackpointer (word 224), 224)]
      ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) aes128_gcm_enc_mc /\
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
                      [in_p, 16 * val len_bits DIV 128; tag_p, 16; ivec_p, 16; key_p, 176; htable_p, 96;
                       out_p, 16 * val len_bits DIV 128; word_sub stackpointer (word 224), 224]
                      [out_p, 16 * val len_bits DIV 128; tag_p, 16; ivec_p, 16;
                       word_sub stackpointer (word 224), 224]))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(out_p, 16 * val len_bits DIV 128);
                      memory :> bytes(tag_p, 16);
                      memory :> bytes(ivec_p, 16);
                      memory :> bytes(word_sub stackpointer (word 224), 224)])`,
  MATCH_ACCEPT_TAC(ARM_ADD_IBT_RULE
    aes128_gcm_enc_mc aes128_gcm_enc_tmc AES128_GCM_ENC_NOIBT_SUBROUTINE_SAFE));;
