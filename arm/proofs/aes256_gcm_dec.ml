(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Functional correctness, constant-time and memory-safety proofs of the     *)
(* AES-256-GCM bulk decryption kernel aes256_gcm_dec, the 4-way              *)
(* software-pipelined kernel.                                                *)
(*                                                                           *)
(* The kernel processes the len_bits DIV 128 whole 16-byte blocks of its     *)
(* input: block i is decrypted in counter mode with the counter block        *)
(* ctr_block nonce (i + c), the input (ciphertext) is folded into the GHASH  *)
(* tag, and the tag and the next counter block ctr_block nonce (nblocks + c) *)
(* are written back; X0 returns the byte length len_bits DIV 8.              *)
(*                                                                           *)
(* Control flow (offsets in the trimmed code, see below):                    *)
(*   0x2c..0xa4    preamble: byte length, round keys, tag, the IV halves     *)
(*                 into the counter slots at sp + 160..208, counter, block   *)
(*                 counts and the reduction constant                         *)
(*   0xa8          cbz x1,0x6c0: loop_count = 0 skips to the tail            *)
(*   0xac..0x264   fill: loads group 0, starts its AES and GHASH, stores its *)
(*                 block 2                                                   *)
(*   0x268         cbz x1,0x574: loop_count = 1 goes to the drain            *)
(*   0x26c..0x56c  main loop body (193 instructions)                         *)
(*   0x570         cbnz x1,0x26c: the loop back edge                         *)
(*   0x574..0x6bc  drain: finishes the last group (83 instructions)          *)
(*   0x6c0..0x6c8  reloads of H^1, H^2 and their middle terms                *)
(*   0x6cc         cbz x9,0x7b0: loop_remain = 0 skips the tail loop         *)
(*   0x6d0..0x7ac  single-block tail loop (cbnz x9,0x6d0 at 0x7ac)           *)
(*   0x7b0..0x7c0  X0, tag and counter word stores                           *)
(*                                                                           *)
(* The main loop is verified from one mid-pipeline invariant swp_inv i,      *)
(* asserted at the loop head pc + 0x26c: at the start of iteration i the tag *)
(* of blocks 0..4i-1 is in Q30 (with its two 64-bit halves swapped), the     *)
(* outputs of blocks 0..4i-1 and of block 4i+2 are stored, the counter       *)
(* blocks of group i are staged at sp + 160..208, and further registers hold *)
(* input blocks and partial AES and GHASH results of the group.  The legs    *)
(* are                                                                       *)
(*   FILL_TO_CBZ_DEC  pc + 0x2c -> swp_inv 0 at pc + 0x268                   *)
(*   FILLLEG          the same, then the cbz at 0x268 not taken              *)
(*   BODYLEG          swp_inv i at pc + 0x26c -> swp_inv (i+1) at pc + 0x570 *)
(*   DRAIN_FROM_574   swp_inv (loop_count-1) at pc + 0x574 -> drain_bridge   *)
(*                    at pc + 0x6c0                                          *)
(*   DRAINLEG         the cbnz at 0x570 not taken, then DRAIN_FROM_574       *)
(*   TAILLEG          drain_bridge at pc + 0x6c0 -> tail_post at pc + 0x7c4  *)
(* MAINLEG composes FILLLEG, an ENSURES_WHILE_UP over loop_count - 1         *)
(* iterations of BODYLEG and the back edge, and DRAINLEG; LEG_LC0 and        *)
(* LEG_LC1 cover loop_count = 0 and 1; CORE_FROM88 joins them with TAILLEG   *)
(* (despite its name it starts at pc + 0x2c: here the fill leg includes the  *)
(* preamble).  The core theorem AES256_GCM_DEC_CORRECT, from pc + 0x2c after *)
(* the register saves to pc + 0x7c4 before the restores, follows from        *)
(* CORE_FROM88.  The safety theorems follow the same regions with the        *)
(* event-tracking simulator.                                                 *)
(*                                                                           *)
(* The specification vocabulary (ctr_block, aes_ctr_block, nist_input_block, *)
(* htable_mem_4) is in arm/proofs/utils/aes_gcm_spec.ml; the lemmas and      *)
(* tactics shared with the other AES-GCM proofs are in                       *)
(* arm/proofs/utils/aes_gcm_common.ml.                                       *)
(*                                                                           *)
(* The code begins with a BTI landing pad (bti c).  The proofs are about the *)
(* trimmed code aes256_gcm_dec_tmc without it, which is also the code of a   *)
(* -DNO_IBT build, so all offsets above are offsets in that code; the        *)
(* subroutine theorems for the full code are derived by ARM_ADD_IBT_RULE.    *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "arm/proofs/utils/aes_gcm_common.ml";;

(* ------------------------------------------------------------------------- *)
(* The machine code.                                                         *)
(* ------------------------------------------------------------------------- *)

let aes256_gcm_dec_mc = define_assert_from_elf "aes256_gcm_dec_mc" "arm/aes_gcm/aes256_gcm_dec.o"
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

(* The code without its BTI landing pad, which the proofs are about (see the *)
(* header).                                                                  *)

let aes256_gcm_dec_tmc = define_trimmed "aes256_gcm_dec_tmc" aes256_gcm_dec_mc;;
let AES256_GCM_DEC_EXEC = ARM_MK_EXEC_RULE aes256_gcm_dec_tmc;;

(* ------------------------------------------------------------------------- *)
(* The partial encryptions this kernel carries besides those of              *)
(* aes_gcm_common.ml (at the loop head Q3 holds aes12c, 12 rounds, and Q8    *)
(* holds aes5c, 5 rounds, of counter blocks of the group), their bridges to  *)
(* aes14p, and the keystream fold in the operand order of the decrypt code.  *)
(* ------------------------------------------------------------------------- *)

let aes5c = define_aes_partial "aes5c" 5;;
let aes12c = define_aes_partial "aes12c" 12;;
let AES14P_VIA_AES12C = AES_PREFINAL_VIA_PARTIAL aes14p 14 aes12c 12;;
let AES14P_VIA_AES5C = AES_PREFINAL_VIA_PARTIAL aes14p 14 aes5c 5;;

(* The keystream fold in the operand order of the decrypt code: there the
   output block is word_xor inblock (word_xor rk14 <tower>) (see
   XOR_AES256_CIPHER_RECONSTRUCT_DEC), so once <tower> is folded to aes14p the
   XORs are nested the other way round from KEYSTREAM_FOLD256; the right-hand
   side is the same.  Proving it once here, for a symbolic c, lets the
   output-block closer fold by rewriting instead of a WORD_BITWISE_RULE call at
   each use, which would bit-blast the counter word. *)
let KEYSTREAM_FOLD256_DEC = prove
 (`[EL 0 rk; EL 1 rk; EL 2 rk; EL 3 rk; EL 4 rk; EL 5 rk; EL 6 rk; EL 7 rk;
    EL 8 rk; EL 9 rk; EL 10 rk; EL 11 rk; EL 12 rk; EL 13 rk; EL 14 rk]:(int128)list = rk
   ==> word_xor inb (word_xor (word_reversefields 8 (EL 14 rk)) (aes14p nonce rk c))
       = word_xor (word_reversefields 8 (aes256_cipher (ctr_block nonce c) rk)) inb`,
  DISCH_THEN(fun th -> MP_TAC(MATCH_MP AES14P_COMPLETE th)) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN CONV_TAC WORD_BITWISE_RULE);;

(* ------------------------------------------------------------------------- *)
(* The stepper: one ARM step (SWP_STEP_TAC_P) with the pruning policy        *)
(* dec_prune, followed by the normalization of the new facts.                *)
(* ------------------------------------------------------------------------- *)

(* Q14 holds the input block 4i (inblock(4i)) at the loop head.  The tag
   computation reads it at an early state, but Q14 is overwritten later in the
   body, so the latest-only pruning would drop the fact about that early state
   that the seed closer needs to fold block 4i.  is_q14_read exempts the reads
   of Q14 from the pruning, as the in_p reads are. *)
let is_q14_read c = try (match lhs c with
    Comb(Comb(Const("read",_),Const("Q14",_)),_) -> true | _ -> false) with _ -> false;;
(* The staged counter blocks live in the stack slots at sp + 160, 176, 192 and
   208.  Their 128-bit reads are kept (the latest one of each slot) so that
   read-over-write can resolve the staged blocks at the end of the body;
   is_spctr_read matches only these four block reads, not the +8/+12 lanes or
   the byte components.  The tag_p, ivec_p, htable_p and in_p reads are
   anchors, and the in_p/out_p foralls are kept.  The stale-fact sweep
   (DISCARD_STALE_TAC) runs after this pruning: the anchored reads and the
   frame foralls are re-derived by every ARM_STEP_TAC, and without the sweep
   their old-state copies would accumulate, making each step and each closer
   linear in the length of the leg. *)
let is_spctr_read c = try
    let l = lhs c in
    fst(dest_const(fst(strip_comb l)))="read" && free_in `stackpointer:int64` l &&
    (can (find_term (fun t -> match t with
       | Comb(Comb(Const("word_add",_),sp),Comb(Const("word",_),n))
           when (try fst(dest_var sp)="stackpointer" with _->false) ->
             (try let v=dest_small_numeral n in v=160||v=176||v=192||v=208 with _ -> false) | _ -> false)) l)
  with _ -> false;;
(* The state index K of a fact `read _ sK = _`, or -1. *)
let read_state_idx c = try (match lhs c with
   Comb(Comb(Const("read",_),_),Var(nm,_)) when String.length nm>=2 && nm.[0]='s' ->
     int_of_string(String.sub nm 1 (String.length nm-1)) | _ -> -1) with _ -> -1;;
(* The slot offset (160/176/192/208) of a staged-block read, or -1. *)
let spctr_off c = try (match find_terms (fun t -> match t with
     Comb(Comb(Const("word_add",_),sp),Comb(Const("word",_),n)) when (try fst(dest_var sp)="stackpointer" with _->false)
       -> (let v=dest_small_numeral n in v=160||v=176||v=192||v=208) | _ -> false) (lhs c) with
   | (Comb(Comb(_,_),Comb(_,n)))::_ -> dest_small_numeral n | _ -> -1) with _ -> -1;;
(* The nonce lanes of the four slots are primed at s0 as
     read (bytes64 (sp+OFF)) s0 = ivlo
     read (bytes32 (sp+OFF+8)) s0 = word_subword ivhi (0,32)
   for OFF = 160, 176, 192, 208 (the body writes only the counter word at +12
   of each slot), and the counter-slot merges at the store steps (16, 20, 32
   and 35 of the body) need them.  is_spctr_read does not match the bytes32
   lanes at all and would conflate the bytes64 lanes with the slot reads at the
   same offset, so is_ctrlane_read matches these lanes by their exact offsets
   and by their right-hand side (ivlo, or a word_subword of ivhi), which only
   the priming facts have. *)
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
    (* The right-hand side is ivlo or a word_subword of ivhi.  It is tested
       last and lazily, since the right-hand side of a carried fact can be
       large. *)
    let rhsok () = let r = rhs c in
                (try fst(dest_var r) = "ivlo" with _ -> false) ||
                (free_in `ivhi:int64` r &&
                 can (find_term (fun t -> match t with Const("word_subword",_) -> true | _ -> false)) r) in
    headok && spok && (can (find_term offpred) l) && rhsok ()
  with _ -> false;;
(* The key of a nonce-lane read, its component without the state, which keeps
   apart the lanes of one slot (bytes64 at 192, bytes32 at 200, ...) in the
   latest-only pruning. *)
let ctrlane_key c = try let l = lhs c in fst(dest_comb l) with _ -> `T`;;
(* The pruning policy of the stepper: the tag_p, ivec_p, htable_p and in_p
   reads and the Q14 reads are always kept, the staged counter slots (per
   offset) and the primed nonce lanes (per lane) latest-only, the foralls of
   the current state only, with the stale sweep (see SWP_STEP_TAC_P in
   arm/proofs/utils/aes_gcm_common.ml). *)
let dec_prune =
  { anchors = [`tag_p:int64`; `ivec_p:int64`; `htable_p:int64`; `in_p:int64`]; slots = [];
    families =
     [(fun c -> if is_ctrlane_read c then Some(string_of_term(ctrlane_key c), read_state_idx c) else None);
      (fun c -> if is_spctr_read c then Some(string_of_int(spctr_off c), read_state_idx c) else None)];
    exempt = is_q14_read; all_foralls = false; stale_gc = true };;
let gkeepN keeplist th sname = SWP_STEP_TAC_P dec_prune keeplist th sname;;
(* DEC_STEP_TAC is one pruned symbolic step followed by the normalization of
   the assumptions (subword nests, relative addresses, in_p offsets);
   DEC_STEPS_TAC runs a range of steps with a per-step hook (counter-slot
   merges, lane priming) after each one. *)

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

(* contains sub s: whether the string sub occurs in s. *)
let contains sub s =
  let ls = String.length s and lsub = String.length sub in
  let rec go i = if i+lsub > ls then false
    else if String.sub s i lsub = sub then true else go (i+1) in go 0;;
(* The loop invariant swp_inv i, asserted at the loop head pc + 0x26c at the
   start of iteration i (BODYLEG ends in it at pc + 0x570 for i + 1, and the
   hops at pc + 0x268 and pc + 0x574 use it too).  Besides the pointers (X0
   already points at group i + 1), the counts, the round keys (Q18-Q28,
   Q15-Q17, Q2), the reduction constant Q7, the key table and the input:
   - the outputs of blocks 0..4i-1, and of block 4i+2, which the previous
     iteration (or the fill) has stored;
   - the counter blocks 4i+c..4i+c+3 staged at sp + 160..208, the first also in
     Q31, and the counter base 4i+c in X13;
   - the tag of blocks 0..4i-1 in Q30, with its two 64-bit halves swapped;
   - the input blocks 4i, 4i+1 and 4i+3 in Q14, Q1 and Q0, the partial
     encryptions aes12c of counter 4i+c+1 in Q3 and aes5c of counter 4i+c+3 in
     Q8, the Karatsuba partial results of the GHASH of blocks 4i+1..4i+3 in
     Q4-Q6 and Q9-Q11, and the key-table entries at offsets 64 and 80 (the
     middle terms of H^3 and H^4, and H^4) in Q13 and Q29. *)

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
             word_xor (aes_ctr_block aes256_cipher c nonce rk j) (inblock j)) /\
    read (memory :> bytes128 (word_add out_p (word (64 * i + 32)))) s =
    word_xor (aes_ctr_block aes256_cipher c nonce rk (4 * i + 2)) (inblock (4 * i + 2)) /\
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
(* ------------------------------------------------------------------------- *)
(* Closers for the body leg: GHASH, AES and arithmetic lemmas, the tag seed  *)
(* closer, the staged counter blocks, and the dispatcher CLOSE_DEC.          *)
(* ------------------------------------------------------------------------- *)

(* One group of the GHASH (Horner) recurrence: the reduced sum of the products
   of blocks 4i+3, 4i+2 and 4i+1 with H, H^2 and H^3 and of (tag XOR block 4i)
   with H^4 is the tag after block 4i+3. *)
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

(* The output block in the form the decrypt code computes it, word_xor inblock
   (word_xor rk14 <aese tower>), folded to the cipher. *)
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

(* ------------------------------------------------------------------------- *)
(* The seed closer, for the tag at the end of the body.  The goal reduces to *)
(*   machwj = byteswap128 (polyval_reduce_prop3 simple)                      *)
(* where machwj is the code's reduction, a word_join over products of nine   *)
(* lanes vacc, vcb0..vcb3 and vh0..vh3 (the tag, the blocks and the key      *)
(* powers), and                                                              *)
(*   simple = word_xor (pmul cb3 h0) (word_xor (pmul cb2 h1)                 *)
(*              (word_xor (pmul cb1 h2) (pmul (word_xor acc cb0) h3))).      *)
(* Two lemmas over the nine free lanes give it:                              *)
(*   MACHWJ_IS_BSW_G2: machwj = byteswap128 (polyval_reduce_g2 <towers>),    *)
(*     by SEED_AC_CLOSE_TAC;                                                 *)
(*   G2_IS_PROP3: polyval_reduce_g2 <towers> = polyval_reduce_prop3 simple.  *)
(* The products with the reduction constant word 13979173243358019584 stay   *)
(* opaque atoms: POLYARG_UNIFY_TAC identifies the code's and the             *)
(* specification's copies through XOR associativity and commutativity of     *)
(* their arguments, so the carry-less multiplier is never bit-blasted.       *)
(* ------------------------------------------------------------------------- *)

(* XOR associativity and commutativity, for AC: it proves equations between
   word_xor trees over atoms without bit-blasting. *)
let WORD_XOR_AC_THM = prove
 (`word_xor x y = word_xor y x /\
   word_xor (word_xor x y) z = word_xor x (word_xor y z) /\
   word_xor x (word_xor y z) = word_xor y (word_xor x z)`,
  REWRITE_TAC[WORD_XOR_ASSOC] THEN REPEAT CONJ_TAC THEN CONV_TAC WORD_BITWISE_RULE);;

(* Karatsuba middle-term fold for the XOR of two words (the middle factor of
   the accumulator lane): the code's word_xor (word_xor (sw a 0) (sw b 0))
   (word_xor (sw a 64) (sw b 64)) is karatsuba_mid (word_xor a b). *)
let CMID_XOR2 = prove
 (`word_xor (word_xor (word_subword (a:int128) (0,64)) (word_subword (b:int128) (0,64)))
            (word_xor (word_subword a (64,64)) (word_subword b (64,64))):int64
   = karatsuba_mid (word_xor a b)`,
  REWRITE_TAC[karatsuba_mid; WORD_SUBWORD_XOR] THEN CONV_TAC WORD_BITWISE_RULE);;

(* The 64-bit halves of a word_join (the LO/HI of polyval_reduce_g2). *)
let SJ_LO = WORD_BLAST `word_subword(word_join (h:int64) (l:int64):int128)(0,64):int64 = l`;;
let SJ_HI = WORD_BLAST `word_subword(word_join (h:int64) (l:int64):int128)(64,64):int64 = h`;;

(* POLYARG_UNIFY_TAC: one pass that identifies the products with the reduction
   constant whose arguments are XOR trees with the same multiset of leaves
   (nested products with the constant count as atoms): it proves the arguments
   equal by XOR AC, lifts that to the products (AP_THM/AP_TERM) and rewrites
   with PURE_REWRITE_TAC.  It is applied twice: the first pass unifies the
   inner products (w1), which makes the arguments of the outer ones (w2)
   coincide, and the second pass unifies those.  Then the code's two products
   with the constant are syntactically the specification's, so they can be
   abstracted as opaque atoms and closed by AC. *)
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

(* SEED_AC_CLOSE_TAC proves machwj = byteswap128 (polyval_reduce_g2 <towers>)
   without bit-blasting: unfold polyval_reduce_g2 and byteswap128, bring both
   sides to XOR trees over 64-bit lanes of the products (abbreviated L_i, with
   karatsuba_mid kept folded so that each middle lane is one atom), unify the
   two products with the reduction constant (POLYARG_UNIFY_TAC twice),
   abbreviate the remaining products and subwords, split the outer word_join
   (BINOP_TAC) and close each half by XOR AC. *)
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

(* ------------------------------------------------------------------------- *)
(* SEED_ABS and SWP_Q30_SEED_FINISH_TAC.  machwj_abs, simple_abs and         *)
(* g2app_free are the abstract seed terms over the nine lanes vacc,          *)
(* vcb0..vcb3 and vh0..vh3 (machwj_abs is assembled from its repeated        *)
(* subterms), and SEED_ABS is                                                *)
(*   machwj_abs = byteswap128 (polyval_reduce_prop3 simple_abs).             *)
(* ------------------------------------------------------------------------- *)
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

(* machwj_abs = byteswap128 (polyval_reduce_g2 <towers>): SEED_AC_CLOSE_TAC *)
let MACHWJ_IS_BSW_G2 = prove
 (mk_eq(machwj_abs, mk_comb(`byteswap128`, g2app_free)), SEED_AC_CLOSE_TAC);;
(* polyval_reduce_g2 <towers> = polyval_reduce_prop3 simple_abs: the Karatsuba
   join, then BITBLAST_RULE over the abbreviated products. *)
let G2_IS_PROP3 = prove
 (mk_eq(g2app_free, mk_comb(`polyval_reduce_prop3`, simple_abs)),
  REWRITE_TAC[POLYVAL_REDUCE_G2] THEN
  GEN_REWRITE_TAC (RAND_CONV o TOP_DEPTH_CONV) [PMUL_KARATSUBA_JOIN_ALT] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[karatsuba_mid] THEN
  REWRITE_TAC[CMID_LOHI; CMID_HILO] THEN AP_TERM_TAC THEN
  REWRITE_TAC[JOIN_XOR_256; JOIN_XOR_128] THEN
  ABBREV_PMULS THEN POP_ASSUM_LIST(K ALL_TAC) THEN CONV_TAC BITBLAST_RULE);;
let SEED_ABS = TRANS MACHWJ_IS_BSW_G2 (AP_TERM `byteswap128` G2_IS_PROP3);;

(* SWP_Q30_SEED_FINISH_TAC closes the tag goal at the end of the body once it
   has the form
     machwj[lanes] =
     word_join (word_subword ACC (0,64)) (word_subword ACC (64,64))
   with ACC = nist_ghash .. (4*(i+1)): term_match finds the nine lane instances
   in the left-hand side, the instance of SEED_ABS turns it into byteswap128
   (polyval_reduce_prop3 simple[lanes]), SWP_GHASH_BRANCH2_256 folds that to
   byteswap128 ACC, and the definition of byteswap128 gives the right-hand
   side. *)
let SWP_Q30_SEED_FINISH_TAC : tactic = fun (asl,w) ->
  let (_,ilist,_) = term_match [] machwj_abs (lhs w) in
  let seed_i = INST ilist SEED_ABS in
  let br2 = REWRITE_RULE[ARITH_RULE `4*i+4 = 4*(i+1)`] SWP_GHASH_BRANCH2_256 in
  let seed_bsw = REWRITE_RULE[br2] seed_i in
  (ONCE_REWRITE_TAC[seed_bsw] THEN REWRITE_TAC[byteswap128]) (asl,w);;

(* The X13 counter closer: the counter base X13 = word_zx (word (4i+c))
   advances by 4 in each body (add w13,w13,#4 at 0x274), so the goal at the end
   of the body is
     word_zx (word_add (word_zx (word_zx (word (4*i+c)))) (word 4)) =
     word_zx (word (4*(i+1)+c)).
   ZX_COUNTER_UD folds the inner int32 -> int64 -> int32 round trip, then
   AP_TERM_TAC and WORD_RULE do the arithmetic. *)
let CTR_LANE_dec : tactic =
  REWRITE_TAC[ZX_COUNTER_UD] THEN TRY(AP_TERM_TAC THEN CONV_TAC WORD_RULE) THEN
  TRY(CONV_TAC WORD_RULE);;

(* STAGED_REASSEMBLE: in word_reversefields 8 (ctr_block nonce a) the counter
   word is the top 32 bits and the low 96 bits are the nonce, the same for
   every counter a.  When the body overwrites the +12 lane of a slot (bytes32
   at sp+OFF+12) with a new counter word word_zx (word_bytereverse (word b)),
   the slot holds that word joined with the low 96 bits of the old block, which
   is word_reversefields 8 (ctr_block nonce b).  SP_SLOT_dec uses it after
   resolving the slot read by read-over-write. *)
let STAGED_REASSEMBLE = prove
 (`word_join (word_zx (word_bytereverse (word b:int32)):int32)
             (word_subword (word_reversefields 8 (ctr_block (nonce:(96)word) a):int128) (0,96):(96)word)
    :int128
   = word_reversefields 8 (ctr_block nonce b)`,
  REWRITE_TAC[ctr_block] THEN CONV_TAC WORD_BLAST);;

(* SLOT_LO and SLOT_MID rewrite the nonce subwords of word_reversefields 8
   (ctr_block nonce c) in a staged slot to the ivec halves ivlo and
   word_subword ivhi (0,32), given the join relation, so that ASM_REWRITE_TAC
   closes them against the split store facts. *)
let SLOT_LO = prove
 (`word_join (ivhi:int64) (ivlo:int64):int128 = word_reversefields 8 (ctr_block nonce c)
   ==> word_subword (word_reversefields 8 (ctr_block nonce c):int128) (0,64):int64 = ivlo`,
  DISCH_THEN(SUBST1_TAC o SYM) THEN CONV_TAC WORD_BLAST);;
let SLOT_MID = prove
 (`word_join (ivhi:int64) (ivlo:int64):int128 = word_reversefields 8 (ctr_block nonce c)
   ==> word_subword (word_reversefields 8 (ctr_block nonce c):int128) (64,32):int32 =
       word_subword (ivhi:int64) (0,32):int32`,
  DISCH_THEN(SUBST1_TAC o SYM) THEN CONV_TAC WORD_BLAST);;

(* ------------------------------------------------------------------------- *)
(* Rebuilding a staged counter block during stepping, at its counter-store   *)
(* state, from the nonce lanes primed at s0 (which do not depend on the      *)
(* counter) and the counter word stored at +12.  The next lemmas are pure    *)
(* component and ctr_block algebra.                                          *)
(* ------------------------------------------------------------------------- *)

(* Lane extraction: a bytes64 or bytes32 read is the corresponding subword of
   the enclosing bytes128 read (READ_MEMORY_BYTESIZED_SPLIT and WORD_BLAST). *)
let B64_OF_B128_LO = prove
 (`read (memory :> bytes64 x) s :int64 = word_subword (read (memory :> bytes128 x) s :int128) (0,64)`,
  REWRITE_TAC[el 1 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT)] THEN CONV_TAC WORD_BLAST);;
let B32_OF_B128_MID = prove
 (`read (memory :> bytes32 (word_add x (word 8))) s :int32 =
     word_subword (read (memory :> bytes128 x) s :int128) (64,32)`,
  REWRITE_TAC[el 1 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT);
              el 2 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT)] THEN
  CONV_TAC WORD_BLAST);;

(* The nonce lanes do not depend on the counter: the low 64 and the middle 32
   bits of word_reversefields 8 (ctr_block nonce a) are the same for every a.
   This puts the nonce lanes of any staged block in the ctr_block nonce c form
   of the ivec, the same in every iteration. *)
let SUBW_LO_CI = prove
 (`word_subword (word_reversefields 8 (ctr_block nonce a):int128) (0,64):int64 =
   word_subword (word_reversefields 8 (ctr_block nonce b):int128) (0,64):int64`,
  REWRITE_TAC[ctr_block] THEN CONV_TAC WORD_BLAST);;
let SUBW_MID_CI = prove
 (`word_subword (word_reversefields 8 (ctr_block nonce a):int128) (64,32):int32 =
   word_subword (word_reversefields 8 (ctr_block nonce b):int128) (64,32):int32`,
  REWRITE_TAC[ctr_block] THEN CONV_TAC WORD_BLAST);;

(* Staged-block reconstruction over the ivec halves ivlo and ivhi: the nonce
   lanes are stated as = ivlo and = word_subword ivhi (0,32), right-hand sides
   that are variables or subwords of a variable, which ARM_STEP_TAC carries
   without trouble.  CTR_BLOCK_BUILD_V_DEC is the reconstruction, given the
   join relation.  The widths of its counter word (word_zx over int64
   intermediates) print the same as a wrong int32 form, which term_match
   rejects, so the statement is parsed with full type annotations. *)
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
(* ------------------------------------------------------------------------- *)
(* Closers shared by the body leg (symbolic i) and the fill leg (i = 0):     *)
(* INFOLD_dec, GHASH_PARTIAL_CLOSE_dec, SWP_Q30_SEED_TAC,                    *)
(* OUT_BLOCK_CLOSE_dec, OUT_STORE_dec, SP_SLOT_dec, close_pc_cond,           *)
(* close_frame_dec, OUT_FRAME_dec, IVEC_RECOMB_dec, CTRREG_dec and the       *)
(* dispatcher CLOSE_DEC.                                                     *)
(* ------------------------------------------------------------------------- *)

(* Input addresses of the next group: in_p + word (64*(i+1)+K) as in_p + word
   (16*(4*(i+1)+M)). *)
let inp_addr_norms_dec =
  (* the case K = 0: the goal address is word (64*(i+1)), without + 0 *)
  (WORD_RULE `word_add (in_p:int64) (word (64*(i+1))):int64 = word_add in_p (word (16*(4*(i+1))))`) ::
  List.map (fun (kk,m) ->
    WORD_RULE (subst [mk_small_numeral kk, `K:num`; mk_small_numeral m, `M:num`]
                 `word_add (in_p:int64) (word (64*(i+1)+K)):int64 = word_add in_p (word (16*(4*(i+1)+M)))`))
  [(0,0);(16,1);(32,2);(48,3);(64,4);(80,5);(96,6);(112,7)];;

(* An input read = inblock: normalize the address, use the input forall. *)
let IN_READ_CLOSE_dec : tactic =
  REWRITE_TAC inp_addr_norms_dec THEN
  (fun (asl,w) ->
     FIRST_ASSUM(fun fa -> if (try is_forall(concl fa) && free_in `in_p:int64`(concl fa)
                                  && free_in (rand(lhs w)) (concl fa) with _->false)
                          then MATCH_MP_TAC fa else NO_TAC) (asl,w)) THEN
  (* The block bound blk < nblocks: ASM_ARITH_TAC alone cannot use
     nblocks DIV 4 = loop_count, so first try to establish 4i+7 < nblocks,
     which covers every block of the body leg. *)
  (SUBGOAL_THEN `4*i+7 < nblocks` ASSUME_TAC THENL
    [UNDISCH_TAC `nblocks DIV 4 = loop_count` THEN UNDISCH_TAC `i < loop_count - 2` THEN
     UNDISCH_TAC `2 <= loop_count` THEN ARITH_TAC; ALL_TAC]
   ORELSE ALL_TAC) THEN
  ASM_ARITH_TAC;;

(* Helpers of INFOLD_dec: the in_p bytes128 reads in a term, the block index of
   such a read (the K of 16 * K) and its state. *)
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
(* The state (variable name) of an in_p bytes128 read, or "". *)
let inpread_state rd = try (match dest_comb rd with (_,Var(nm,_)) -> nm | _ -> "") with _ -> "";;
(* The state that the read of an input forall is about, or "". *)
let inpforall_state c = try
   (match snd(strip_forall c) with
    | Comb(Comb(Const("==>",_),_),bod) ->
       (match find_terms (fun t -> match t with
          Comb(Comb(Const("read",_),cmp),Var(nm,_)) when free_in `in_p:int64` cmp -> true | _ -> false) bod with
        | (Comb(Comb(_,_),Var(nm,_)))::_ -> nm | _ -> "")
    | _ -> "") with _ -> "";;
(* Fold the in_p reads in the goal to inblock, using the input forall at the
   state of each read: the input read embedded in an output store is at an
   earlier state sK, and gkeepN keeps the in_p foralls of all states, so the
   forall about sK is there. *)
let INFOLD_dec : tactic =
  REWRITE_TAC inp_addr_norms_dec THEN
  (fun (asl,w) ->
    let inreads = setify(find_terms is_inp_bytes128_read w) in
    if inreads = [] then ALL_TAC (asl,w)
    else (EVERY (map (fun rd ->
       let blk = sixteen_blk rd in
       let st = inpread_state rd in
       (* Try to fold rd to inblock blk, never failing: without a usable forall
          rd stays unfolded and the caller decides. *)
       TRY(SUBGOAL_THEN (mk_eq(rd, mk_comb(`inblock:num->int128`, blk))) ASSUME_TAC THENL
        [(* the input forall at the state of the read, else any in_p forall *)
         (FIRST_ASSUM(fun fa -> if (try is_forall(concl fa) && free_in `in_p:int64`(concl fa)
                                       && inpforall_state (concl fa) = st with _->false)
                                  then MATCH_MP_TAC fa else NO_TAC)
          ORELSE FIRST_ASSUM(fun fa -> if (try is_forall(concl fa) && free_in `in_p:int64`(concl fa) with _->false)
                                         then MATCH_MP_TAC fa else NO_TAC))
         THEN
         (* The block bound, as in IN_READ_CLOSE_dec (4*i+7 < nblocks also
            covers block 4(i+1)+2 of the next group). *)
         (SUBGOAL_THEN `4*i+7 < nblocks` ASSUME_TAC THENL
           [UNDISCH_TAC `nblocks DIV 4 = loop_count` THEN UNDISCH_TAC `i < loop_count - 2` THEN
            UNDISCH_TAC `2 <= loop_count` THEN ARITH_TAC; ALL_TAC]
          ORELSE ALL_TAC) THEN
         ASM_ARITH_TAC; ALL_TAC]))
      inreads)) (asl,w));;

(* GHASH partial closer (products and XORs of input-block and key-power lanes;
   no nist_ghash on the right).  Q5, Q9, Q10 and Q11 close by REFL_TAC after
   the input fold and the reassembly; Q6, whose block 4i+2 operand is a
   word_subword (word_join ..) (64,128) and whose factor is a middle-term lane
   of the key table, also needs SWP_SUBWORD_JOIN_MID, WORD_SIMPLE_SUBWORD_CONV
   and WORD_BLAST to close the word_xor. *)
let GHASH_PARTIAL_CLOSE_dec : tactic =
  INFOLD_dec THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[INBLOCK_REASSEMBLE; GSYM nist_input_block] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[nist_input_block] THEN ASM_REWRITE_TAC[] THEN
  (TRY REFL_TAC THEN
   TRY (REWRITE_TAC[SWP_SUBWORD_JOIN_MID] THEN CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
        TRY(CONV_TAC WORD_BLAST)));;

(* The seed closer for the tag at the end of the body.  After
   SWP_SUBWORD_JOIN_MID (a word_subword (word_join BIG) (64,128) becomes the
   word_join of two subwords), DEC_GHASH_NORM_TAC (the input byte lanes become
   nist_input_block) and the folding of the Q14 read of block 4i (read Q14 sK =
   inblock(4i) is an assumption, then GSYM nist_input_block), the goal is
     machwj[lanes] =
     word_join (word_subword ACC (0,64)) (word_subword ACC (64,64))
   with ACC = nist_ghash .. (4*(i+1)), which SWP_Q30_SEED_FINISH_TAC closes. *)
let SWP_Q30_SEED_TAC : tactic =
  REWRITE_TAC[SWP_SUBWORD_JOIN_MID] THEN DEC_GHASH_NORM_TAC THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM nist_input_block] THEN ASM_REWRITE_TAC[] THEN
  SWP_Q30_SEED_FINISH_TAC;;

(* The AES14P_VIA_* bridges: a carried partial aesNc followed by the remaining
   rounds is aes14p. *)
let out_via_lemmas =
  [AES14P_VIA_AES5C; AES14P_VIA_AES12C; AES14P_VIA_AES1C; AES14P_VIA_AES6C; AES14P_VIA_AES7C; AES14P_VIA_AES11C];;
(* The keystream fold for an output block.  Once the read resolves to the
   code's value, the goal is
     word_xor inblock_j (word_xor rk14 <tower>) =
     word_xor (aes_ctr_block j) inblock_j
   where <tower> is either all 14 rounds on a resolved word_reversefields 8
   (ctr_block nonce (j+c)) (a block whose counter block is in a register or
   slot) or the remaining rounds on a carried partial aesNc (j+c) (the
   pipelined blocks); OUT_BLOCK_CLOSE_dec tries both.  aes_ctr_block j unfolds
   to the cipher of ctr_block nonce (j+c), and ctr_idx_norms normalize that
   index for blocks of the current group (j = 4i+M) and of the next one
   (j = 4(i+1)+M). *)
let ctr_idx_norms = [ARITH_RULE `(4*i)+c = 4*i+c`; ARITH_RULE `(4*i+1)+c = 4*i+c+1`;
                     ARITH_RULE `(4*i+2)+c = 4*i+c+2`; ARITH_RULE `(4*i+3)+c = 4*i+c+3`;
                     ARITH_RULE `(4*(i+1)+0)+c = 4*(i+1)+c`; ARITH_RULE `(4*(i+1)+1)+c = 4*(i+1)+c+1`;
                     ARITH_RULE `(4*(i+1)+2)+c = 4*(i+1)+c+2`; ARITH_RULE `(4*(i+1)+3)+c = 4*(i+1)+c+3`];;
(* The full-tower keystreams of the next group run on a counter block resident
   as ctr_block nonce (4i+c+4) .. (4i+c+7), while the unfolded target index is
   4(i+1)+c+M; resident_ctr_norms bridge the two. *)
let resident_ctr_norms = [ARITH_RULE `4*i+c+4 = 4*(i+1)+c`; ARITH_RULE `4*i+c+5 = 4*(i+1)+c+1`;
                          ARITH_RULE `4*i+c+6 = 4*(i+1)+c+2`; ARITH_RULE `4*i+c+7 = 4*(i+1)+c+3`];;
(* Output-block keystream fold by KEYSTREAM_FOLD256_DEC, by rewriting only (a
   WORD_BITWISE_RULE here would bit-blast the counter word c): try the index
   form 4i+c+M first, then the forms (4i+M)+c and (4(i+1)+M)+c. *)
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
  (* ADD_CLAUSES turns 4*i+0 into 4*i (the target of block 4i has an explicit
     + 0 that the folded operand lacks). *)
  REWRITE_TAC[ADD_CLAUSES] THEN
  ((REWRITE_TAC[XOR_AES256_CIPHER_RECONSTRUCT_DEC] THEN
   REWRITE_TAC[WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
   REWRITE_TAC[MAP; WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
   ASM_REWRITE_TAC[] THEN
   REWRITE_TAC[aes_ctr_block] THEN REWRITE_TAC ctr_idx_norms THEN
   REWRITE_TAC resident_ctr_norms THEN REFL_TAC)
  ORELSE
  (REWRITE_TAC(map GSYM out_via_lemmas) THEN
   REWRITE_TAC[aes_ctr_block] THEN REWRITE_TAC ctr_idx_norms THEN
   REWRITE_TAC resident_ctr_norms THEN
   KS_FIX_dec));;

(* Output address of the next group: the goal's out_p + word (64*(i+1)+32) is
   the store fact's out_p + word ((64*i+64)+32), since the post-increment of x2
   gives 64*i+64. *)
let out_addr_norms = [
  WORD_RULE `word_add (out_p:int64) (word (64*(i+1)+32)) = word_add out_p (word ((64*i+64)+32))`];;
(* The early output store: block 4(i+1)+2 = 4i+6, stored from Q12 at out_p +
   (64*i+64)+32.  Normalize the address so that ASM_REWRITE_TAC resolves the
   read to the code's value, then the keystream fold of the output block. *)
let OUT_STORE_dec : tactic =
  REWRITE_TAC out_addr_norms THEN
  (* First resolve the out_p read to the code's value, which embeds an in_p
     read at an earlier state; only then can INFOLD_dec see and fold that
     read. *)
  ASM_REWRITE_TAC[] THEN
  INFOLD_dec THEN ASM_REWRITE_TAC[] THEN
  OUT_BLOCK_CLOSE_dec;;

(* SP_RHS_NORMS_dec: the right-hand side index 4(i+1)+c+M as 4i+c+4+M, so that
   the counter base 4i+c+4 matches the value the code adds to. *)
let SP_RHS_NORMS_dec = [
  ARITH_RULE `4*(i+1)+c = 4*i+c+4`; ARITH_RULE `4*(i+1)+c+1 = 4*i+c+5`;
  ARITH_RULE `4*(i+1)+c+2 = 4*i+c+6`; ARITH_RULE `4*(i+1)+c+3 = 4*i+c+7`;
  ARITH_RULE `4*(i+1)+c+4 = 4*i+c+8`];;
(* Counter-word folds (int32): the code computes add wK,w13,#N with
   w13 = word (4i+c+4) at the stores. *)
let SP_LANE_FOLDS_dec = [
  WORD_RULE `word_add (word (4*i+c+4):int32) (word 1) = word(4*i+c+5)`;
  WORD_RULE `word_add (word (4*i+c+4):int32) (word 2) = word(4*i+c+6)`;
  WORD_RULE `word_add (word (4*i+c+4):int32) (word 3) = word(4*i+c+7)`;
  WORD_RULE `word_add (word (4*i+c+4):int32) (word 4) = word(4*i+c+8)`];;
(* SP_SLOT_dec: a staged counter block from read-over-write and
   STAGED_REASSEMBLE.  The goal is
     word_join (read (bytes64 (sp+OFF+8)) sK) (read (bytes64 (sp+OFF)) sK) =
     word_reversefields 8 (ctr_block nonce (4(i+1)+c+M))
   or the same with read (bytes128 (sp+OFF)) sK on the left.  The split form is
   first folded back to the bytes128 read (READ_MEMORY_BYTESIZED_SPLIT); that
   read is split into bytes32 lanes, one read-over-write pass resolves the +12
   lane to the last counter store and the nonce lanes to the baseline, the
   counter word is normalized (CTR_ZX_NORM and the lane folds), and
   STAGED_REASSEMBLE or CTR_BLOCK_BUILD_INSERT folds the block, with fallbacks.

   SP_SLOT_dec_fast: with MERGE_CTR128_FOLD_E applied at the store steps, each
   staged block is already an assumption at the end of the body,
     read (bytes128 (sp+OFF)) sK =
     word_reversefields 8 (ctr_block nonce (4i+c+K)),
   so the goal closes by ASM_REWRITE_TAC once 4(i+1)+c+M is rewritten as
   4i+c+K.  CLOSE_DEC tries it before SP_SLOT_dec. *)
let SP_SLOT_dec_fast : tactic =
  REWRITE_TAC[ARITH_RULE `4*(i+1)+c = 4*i+c+4`; ARITH_RULE `4*(i+1)+c+1 = 4*i+c+5`;
              ARITH_RULE `4*(i+1)+c+2 = 4*i+c+6`; ARITH_RULE `4*(i+1)+c+3 = 4*i+c+7`] THEN
  ASM_REWRITE_TAC[];;
let SP_SLOT_dec : tactic = fun (asl,w) ->
  let splitL = el 1 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT)
  and splitL2 = el 2 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT) in
  (* if the left-hand side is word_join (read bytes64) (read bytes64), fold it
     back to the bytes128 read *)
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
   (* Split the bytes128 read once into bytes32 lanes; one read-over-write pass
      then resolves the +12 lane to the last counter store and the nonce lanes,
      which no store of the body touches, to the baseline. *)
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

(* Counter registers: the X13 counter base (CTR_LANE_dec), else the ZX/CTR
   normal forms. *)
let CTRREG_dec : tactic =
  CTR_LANE_dec ORELSE
  (REWRITE_TAC[ZX_COUNTER_UD; ZX_COUNTER_INC; CTR_ZX_NORM] THEN
   CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
   TRY REFL_TAC THEN TRY(CONV_TAC WORD_RULE) THEN TRY(AP_TERM_TAC THEN ARITH_TAC));;

(* Pointer arithmetic. *)
let close_ptr_dec : tactic =
  REWRITE_TAC[ARITH_RULE `64*((i+1)+1)=64*(i+1)+64`; ARITH_RULE `64*(i+1) = 64*i+64`; LEFT_ADD_DISTRIB] THEN
  CONV_TAC WORD_RULE;;

(* The X1 decrement. *)
let close_x1_dec : tactic =
  ASM_SIMP_TAC[SWP_SUB_LEMMA_DEC];;

(* A conditional PC (the cbnz back edge): the taken case closes by REFL_TAC;
   the other case is refuted from i < loop_count - 2 by SWP_SUB_LEMMA_DEC. *)
let close_pc_cond : tactic =
  COND_CASES_TAC THENL [REFL_TAC; ALL_TAC] THEN
  (* the fall-through case: X1 - 1 is nonzero when i < loop_count - 2 *)
  POP_ASSUM MP_TAC THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(val (word_sub (word (loop_count-(i+1))) (word 1):int64) = 0)` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_SIMP_TAC[SWP_SUB_LEMMA_DEC] THEN REWRITE_TAC[VAL_EQ_0] THEN
    MATCH_MP_TAC(MESON[] `~(x = word 0) ==> ~(x = word 0)`) THEN
    REWRITE_TAC[WORD_EQ_0] THEN MAP_EVERY UNDISCH_TAC [`i < loop_count - 2`; `2 <= loop_count`] THEN ARITH_TAC;
    REFL_TAC];;

(* The MAYCHANGE frame, from the frame assumption between the initial and the
   final state by SUBSUMED_APPLY. *)
let close_frame_dec : tactic =
  fun (asl,w) ->
    let frame_th = try snd(List.find (fun (_,th) -> let c=concl th in
        (try not(is_eq c) && can(find_term(fun x->match x with Const("MAYCHANGE",_)->true|_->false)) c
            && (match c with Comb(Comb(_,a),b) -> is_var a && is_var b | _->false) with _->false)) asl)
      with _ -> failwith "close_frame_dec: no frame asm" in
    (MATCH_MP_TAC(MATCH_MP SUBSUMED_APPLY frame_th) THEN
     REWRITE_TAC[ETA_AX; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN SUBSUMED_MAYCHANGE_TAC) (asl,w);;

(* The output forall j < 4(i+1): the blocks j < 4i from the invariant, then the
   four blocks of group i. *)
let OUT_FRAME_dec : tactic =
  REWRITE_TAC[ARITH_RULE `j < 4 * (i+1) <=>
                          j < 4 * i \/ j = 4*i+0 \/ j = 4*i+1 \/ j = 4*i+2 \/ j = 4*i+3`] THEN
  ASM_REWRITE_TAC[TAUT `p \/ q ==> r <=> (p ==> r) /\ (q ==> r)`] THEN
  REWRITE_TAC[FORALL_AND_THM; FORALL_UNWIND_THM2] THEN
  REWRITE_TAC[ARITH_RULE `16 * (4*i+0) = 64*i`; ARITH_RULE `16 * (4*i+1) = 64*i+16`;
     ARITH_RULE `16 * (4*i+2) = 64*i+32`; ARITH_RULE `16 * (4*i+3) = 64*i+48`] THEN
  ASM_REWRITE_TAC[] THEN
  (* split into the forall j < 4i of the invariant and the blocks 4i+0..4i+3:
     the forall and block 4i+2, stored by the previous iteration, are
     assumptions, the other three blocks are stored now *)
  REPEAT CONJ_TAC THEN
  (* the forall is accepted from the invariant (ASM_REWRITE_TAC cannot
     instantiate a forall) and block 4i+2 closes by ASM_REWRITE_TAC; for the
     others ASM_REWRITE_TAC first resolves the out_p read, then INFOLD_dec
     folds the in_p read now visible in it, then OUT_BLOCK_CLOSE_dec *)
  TRY (FIRST_X_ASSUM (fun th -> if (try is_forall(concl th) && free_in `out_p:int64` (concl th) with _->false)
                                then MATCH_ACCEPT_TAC th else NO_TAC)) THEN
  TRY (ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  ASM_REWRITE_TAC[] THEN INFOLD_dec THEN ASM_REWRITE_TAC[] THEN
  OUT_BLOCK_CLOSE_dec;;

(* The ivec: after IVEC_SPLIT_dec it is in the halves ivlo/ivhi and the body
   never writes ivec_p, so its bytes128 read at the end recombines to word_join
   ivhi ivlo = word_reversefields 8 (ctr_block nonce c). *)
let IVEC_RECOMB_dec : tactic =
  GEN_REWRITE_TAC LAND_CONV [el 1 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT)] THEN
  ASM_REWRITE_TAC[];;

(* The dispatcher: each conjunct of the final state goes to its closer by shape
   and content. *)
let CLOSE_DEC : tactic =
  fun (asl,w) ->
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
    else if hd (lhs w) = "read" && has "aes_ctr_block" (rhs w) then OUT_STORE_dec (asl,w)
    else if hd (lhs w) = "read" && has "inblock" (rhs w) then IN_READ_CLOSE_dec (asl,w)
    else if hd (lhs w) = "read" && free_in `ivec_p:int64` (lhs w) then IVEC_RECOMB_dec (asl,w)
    else if hd (lhs w) = "read" && has "ctr_block" (rhs w) then (SP_SLOT_dec_fast ORELSE SP_SLOT_dec) (asl,w)
    else if hd (lhs w) = "word_reversefields" && has "ctr_block" (lhs w) && has "ctr_block" (rhs w) then
      (* staged slot or Q31 at the end of the body: word_reversefields 8
         (ctr_block nonce (4i+M')) = word_reversefields 8 (ctr_block nonce
         (4(i+1)+M)) with 4i+M' = 4(i+1)+M.  MERGE_CTR128_FOLD_E or
         ASM_REWRITE_TAC already rewrote the read to the resident block; only
         the index arithmetic remains. *)
      (AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC) (asl,w)
    else if deep_ghash then SWP_Q30_SEED_TAC (asl,w)
    else if hd (lhs w) = "aesmc" then
      (* Q3 = aes12c (4(i+1)+c+1) and Q8 = aes5c (4(i+1)+c+3): unfold the
         definitions and fold the counter *)
      ((REWRITE_TAC[aes12c;aes5c] THEN REPEAT(AP_TERM_TAC ORELSE AP_THM_TAC) THEN
        REWRITE_TAC[ZX_COUNTER_UD;ZX_COUNTER_INC;CTR_ZX_NORM] THEN
        CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
        REWRITE_TAC[CTR_BLOCK_BUILD_INSERT; WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
        TRY(CONV_TAC WORD_RULE) THEN TRY REFL_TAC) ORELSE CTRREG_dec) (asl,w)
    else if hd (lhs w) = "word_join" && has "ctr_block" (rhs w) then (SP_SLOT_dec_fast ORELSE SP_SLOT_dec) (asl,w)
    else if free_in `in_p:int64` w then
      (* a lane embedding an in_p read is a GHASH partial (Q4/5/6/9/10/11, or
         the word_zx middle operand) *)
      (GHASH_PARTIAL_CLOSE_dec ORELSE SWP_Q30_SEED_TAC ORELSE CTRREG_dec) (asl,w)
    else if hd (lhs w) = "word_zx" || hd (lhs w) = "word_subword" then CTRREG_dec (asl,w)
    else (* word_xor / word_pmul GHASH partials *)
      (GHASH_PARTIAL_CLOSE_dec ORELSE SWP_Q30_SEED_TAC) (asl,w);;

(* ========================================================================= *)
(* The legs.                                                                 *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* The body leg BODYLEG: swp_inv i at pc + 0x26c -> swp_inv (i+1) at         *)
(* pc + 0x570, under 2 <= loop_count and i < loop_count - 1.  It steps the   *)
(* 193 instructions 0x26c..0x56c; the cbnz at 0x570 is the back edge,        *)
(* stepped in MAINLEG.  The closers are those above, through the dispatcher  *)
(* CLOSE_DEC.                                                                *)
(* ------------------------------------------------------------------------- *)

(* X11 and X12 are not in the invariant: the body uses them as scratch for
   the counter words (add w12,w13,#2 at 0x288, rev w11,w12 at 0x29c), and the
   staged counter blocks live in the stack slots (the sp + 160..208
   conjuncts, rebuilt from X13), so their values are dead at the loop head.
   REDSETX_DEC is the keep list of the stepper (see SWP_STEP_TAC_P), and the
   registers of ghost_lanes_dec get ghost variables for their values at the
   start of a leg. *)
let REDSETX_DEC = ["Q0";"Q1";"Q2";"Q3";"Q4";"Q5";"Q6";"Q7";"Q8";"Q9";"Q10";"Q11";"Q12";"Q13";"Q14";
                   "Q29";"Q30";"Q31"; "X7";"X8";"X13";"X17";"X25";"X27";"X30"];;
let ghost_lanes_dec = ["X7";"X8";"X17";"X25";"X27";"X30";"X13"];;
(* Leg pre/postconditions over this kernel's code (see mk_leg_state). *)
let leg_state_dec = mk_leg_state `aes256_gcm_dec_tmc`;;

(* The leg hypotheses shared by the four legs: the argument facts and the
   nonoverlapping assumptions of the whole-function precondition
   (mk_leg_hyps inserts the leg-specific loop_count and len_bits facts at
   their usual positions). *)
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

(* The in_p frame forall gives the n input blocks a leg reads as facts at s0
   (block index idx k for k = 0..n-1); the bound idx (n-1) < nblocks is
   discharged from the given root facts. *)
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

(* The common leg entry: strip the hypotheses, ghost the scratch lanes,
   ENSURES_INIT_TAC at s0 and unfold htable_mem_4; HTABLE_STRIP_DEC then splits
   the unfolded key-table facts into the assumptions. *)
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

(* Staged-block reconstruction with the nonce lanes kept as variables:
   IVEC_SPLIT_dec abbreviates the ivec halves ivlo/ivhi (keeping the join
   relation), SLOT_PRIME_E states the lanes of the four slots as = ivlo and =
   word_subword ivhi (0,32), and MERGE_CTR128_FOLD_E rebuilds each block at its
   counter store by CTR_BLOCK_BUILD_V_DEC. *)
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
(* Split the ivec read at s0 into the abbreviated 64-bit halves ivlo and ivhi,
   keeping the join relation. *)
let IVEC_SPLIT_dec : tactic =
  UNDISCH_TAC `read (memory :> bytes128 ivec_p) s0 = word_reversefields 8 (ctr_block nonce c)` THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [el 1 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT)] THEN
  DISCH_TAC THEN
  ABBREV_TAC `ivlo:int64 = read (memory :> bytes64 ivec_p) s0` THEN
  ABBREV_TAC `ivhi:int64 = read (memory :> bytes64 (word_add ivec_p (word 8))) s0`;;
let find_join asl =
  tryfind (fun (_,th) -> if can (term_match [] `word_join (ivhi:int64) (ivlo:int64):int128 = xx`) (concl th)
                         then th else fail()) asl;;
(* The low lane read (bytes64 (sp+off)) s0 = ivlo: the slot read at s0
   (B64_OF_B128_LO), the subword of word_reversefields 8 (ctr_block nonce c),
   and SLOT_LO. *)
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
(* The middle lane read (bytes32 (sp+off+8)) s0 = word_subword ivhi (0,32), in
   the same way with B32_OF_B128_MID and SLOT_MID. *)
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
(* MERGE_CTR128_FOLD_E off cval sname derives
     read (bytes128 (sp+off)) sname =
     word_reversefields 8 (ctr_block nonce cval)
   at a counter store step.  The slot read is split twice (into bytes64 halves,
   then the high half into bytes32 lanes), so that the nonce lanes at +0 and +8
   and the counter word at +12 each resolve against their own facts, and
   CTR_BLOCK_BUILD_V_DEC (with the join relation) folds the block. *)
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
(* The counter-slot merges of the body: (store step, slot offset, block index
   at the end of the body).  The counter words are stored at steps 16 (sp+204,
   slot 192), 20 (sp+188, slot 176), 32 (sp+220, slot 208) and 35 (sp+172, slot
   160), and each merge runs at its store step. *)
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

(* ------------------------------------------------------------------------- *)
(* The fill legs: from the entry state at pc + 0x2c (the C arguments and the *)
(* round keys, ivec, tag, key table and input in memory) to swp_inv 0.       *)
(* FILL_TO_CBZ_DEC simulates the preamble and the fill once, to the cbz at   *)
(* pc + 0x268, under 1 <= loop_count; FILLLEG adds the cbz not taken         *)
(* (2 <= loop_count), reaching the loop head pc + 0x26c.  They use the body  *)
(* leg's stepper, invariant and closers, and the ivec halves are abbreviated *)
(* ivlo/ivhi by IVEC_SPLIT_dec as in the body leg.                           *)
(* ------------------------------------------------------------------------- *)

(* The fill precondition at pc + 0x2c: the precondition of
   AES256_GCM_DEC_CORRECT with the C arguments as register values. *)
let fill_pre_body = `read X3 s = tag_p /\ read X4 s = ivec_p /\ read X6 s = htable_p /\ read SP s = stackpointer /\
   read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
   read (memory :> bytes128 ivec_p) s = word_reversefields 8 (ctr_block nonce c) /\
   wordlist_from_memory(key_p,15) s = MAP (word_reversefields 8) rk /\
   read X0 s = in_p /\ read X2 s = out_p /\ read X5 s = key_p /\
   read X1 s = word len_bits /\
   (!j. j < nblocks ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s = inblock j) /\
   htable_mem_4 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s`;;
let fill_pre = mk_abs(`s:armstate`, list_mk_conj(
   `aligned_bytes_loaded s (word pc) aes256_gcm_dec_tmc` ::
   `read PC s = word (pc + 0x2c)` :: conjuncts fill_pre_body));;
let fill_post = leg_state_dec swp_inv `0x26c` `0`;;
(* The fill hypotheses: those of the body leg without i, plus the
   nonoverlapping facts for key_p. *)
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
(* The fill is simulated once, up to the cbz at pc + 0x268, under the weaker
   1 <= loop_count: it reads only the input blocks 0..3.  FILLLEG (cbz not
   taken, 2 <= loop_count) and the loop_count = 1 composition LEG_LC1 (cbz
   taken, into the drain at 0x574) are one-instruction hops from it. *)
let fill_hyps1 = mk_leg_hyps [`1 <= loop_count`] [`len_bits < 2 EXP 64`]
  [`nonoverlapping (key_p:int64,240) (word_add stackpointer (word 160):int64,64)`;
   `nonoverlapping (key_p:int64,240) (out_p:int64,16*nblocks)`;
   `nonoverlapping (key_p:int64,240) (tag_p:int64,16)`];;
let fill_cbz_goal = mk_leg_goal fill_hyps1 fill_pre (leg_state_dec swp_inv `0x268` `0`) fill_frame;;

(* The fill setup: strip the hypotheses, ENSURES_INIT_TAC at s0 (pc + 0x2c),
   the ivec split, the input blocks 0..3 that the fill loads (from the input
   forall; nblocks >= 4 from 1 <= loop_count) and the round keys. *)
let FILL_INPUT_SPLIT_TAC = INPUT_SPLIT_DEC mk_small_numeral 4 [`nblocks DIV 4 = loop_count`; `1 <= loop_count`];;

(* KEY_EXPAND_TAC expands wordlist_from_memory (key_p,15) s0 =
   MAP (word_reversefields 8) rk into the 15 round-key reads
   read (bytes128 (key_p+16k)) s0 = word_reversefields 8 (EL k rk), which the
   loads into Q18..Q2 at steps 2-16 of the fill read; the round-key conjuncts
   of the invariant need them. *)
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

(* Fill lane priming and counter merges. *)
let find_ctr_join asl =
  snd(find (fun (_,th) -> try let c = concl th in is_eq c &&
    (match lhs c with Comb(Comb(Const("word_join",_),_),_) -> true | _ -> false) &&
    contains "ctr_block" (string_of_term(rhs c)) with _ -> false) asl);;

(* The middle lanes of the fill: from the stp store read (bytes64 (sp+(off+8)))
   sK = ivhi, split bytes64 into bytes32 and derive read (bytes32 (sp+(off+8)))
   sK = word_subword ivhi (0,32). *)
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

(* The base counter: the counter field of the ivec, word_reversefields 8
   (ctr_block nonce c), reverses back to word c.  It follows from X13_SETUP of
   aes_gcm_common.ml (which recovers the counter word for a symbolic c by
   BITBLAST_RULE): apply word_zx:int64->int32 to both sides and collapse the
   double word_zx (ZX_COUNTER_UD). *)
let BASE_CTR_DEC = prove(
  `word_join (ivhi:int64) (ivlo:int64):int128 = word_reversefields 8 (ctr_block nonce c)
   ==> word_bytereverse (word_zx (word_ushr ivhi 32):int32) = word c:int32`,
  DISCH_THEN(fun th ->
    ACCEPT_TAC(REWRITE_RULE[ZX_COUNTER_UD]
      (AP_TERM `word_zx:int64->int32` (MATCH_MP X13_SETUP th)))));;

(* The guard at the end of the preamble: establish val (word len_bits) =
   len_bits (from len_bits < 2 EXP 64), X1 = word loop_count,
   val (word loop_count) = loop_count and ~(X1 = word 0), so that the cbz at
   0xa8 (step 32) falls through to 0xac under 1 <= loop_count. *)
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

(* MERGE_CTR128_FILL off cval sK: the counter-slot merge of the fill, at the
   store step as in the body: rebuild
     read (bytes128 (sp+off)) sK =
     word_reversefields 8 (ctr_block nonce cval)
   from the nonce lanes and the counter word just stored at +12.  After the
   split, ASM_REWRITE_TAC and BASE_CTR_DEC (which folds the reversed top word
   of ivhi to word c), the counter word is a word_zx tower over
   word_add (word c) (word K), or over word c; the equation between this core
   (the argument of word_bytereverse) and the core of CTR_BLOCK_BUILD_V_DEC is
   proved from the live terms, since hand-typed widths would not match, by
   ZX_COUNTER_UD and WORD_RULE, and the instance of CTR_BLOCK_BUILD_V_DEC
   closes the goal. *)
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
       else let ceq = prove(mk_eq(core, bv_core), REWRITE_TAC[ZX_COUNTER_UD] THEN CONV_TAC WORD_RULE) in
            (GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [ceq] THEN ACCEPT_TAC bv) (a,g));
    ALL_TAC]) (asl,w);;
(* The counter-slot merges of the fill, at the store steps
   (str wN,[sp,#off+12]): slot 176 at step 43 (counter c+1), 192 at 48 (c+2),
   208 at 53 (c+3) and 160 at 56 (c).  Merging at the store makes the slot fact
   available, by read-over-write, to every later reader: the AES input loads
   and the staged-slot conjuncts at the final state. *)
let dec_fill_merges = [ (43, 176, `c+1`); (48, 192, `c+2`); (53, 208, `c+3`); (56, 160, `c:num`) ];;

(* Fill variants of the body-leg closers, at i = 0.

   INFOLD_FILL is INFOLD_dec for the fill, where the addresses are plain in_p +
   word N and there is no i: (a) the fill address norms (word N = word (16*M)
   for N = 16..112) let sixteen_blk find the block index, (b) the block bound
   is 3 < nblocks, from 1 <= loop_count. *)
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
(* The index normalizations at i = 0: 4*0+K = K (the fill folds reads to
   inblock K, but the invariant has the form 4*0+K).  The GHASH-partial,
   input-read and output-store closers apply them so that both sides match
   for REFL_TAC. *)
let fill_idx_norms = map (fun k -> ARITH_RULE (subst [mk_small_numeral k,`K:num`] `4*0+K = K`)) [0;1;2;3;4;5;6;7;8;9];;
(* The GHASH partial closer at i = 0: INFOLD_FILL, then the reassembly of the
   body leg and the index norms. *)
let GHASH_PARTIAL_FILL : tactic =
  INFOLD_FILL THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[INBLOCK_REASSEMBLE; GSYM nist_input_block] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[nist_input_block] THEN ASM_REWRITE_TAC[] THEN
  (* 4*0+K -> K, so that inblock K on the left matches inblock (4*0+K) *)
  REWRITE_TAC fill_idx_norms THEN
  (TRY REFL_TAC THEN
   TRY (REWRITE_TAC[SWP_SUBWORD_JOIN_MID] THEN CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
        TRY(CONV_TAC WORD_BLAST)));;
(* The tag at i = 0: nist_ghash .. tag0 (list_of_seq .. (4*0)) is the GHASH of
   the empty list, tag0, so Q30 holds tag0 with its halves swapped, and there
   is no Horner step (unlike the seed closer of the body).  Reduce the
   right-hand side to tag0, then WORD_BLAST shows that the code's Q30 (rev64 of
   the loaded word_reversefields 8 tag0) is tag0 with its halves swapped. *)
let SEED_TAG0_REDUCE = prove(
  `nist_ghash (aes256_cipher (word 0) rk) tag0 (list_of_seq (nist_input_block inblock) (4 * 0)) = tag0`,
  REWRITE_TAC[MULT_CLAUSES; LIST_OF_SEQ; nist_ghash]);;
let SEED_FILL : tactic =
  REWRITE_TAC[SEED_TAG0_REDUCE] THEN CONV_TAC WORD_BLAST;;

(* The early output store of the fill (block 2): read (out_p+64*0+32) s143 =
   word_xor (aes_ctr_block (4*0+2)) (inblock (4*0+2)).  At i = 0 the address is
   out_p+64*0+32 itself (not of the 64*(i+1) form), so out_addr_norms do not
   apply: resolve the store by ASM_REWRITE_TAC, fold the embedded in_p read
   (INFOLD_FILL), then close the block as in the body with the index norms. *)
(* The output address at i = 0: the goal reads out_p + word (64*0+32), the
   store fact is at out_p + word 32. *)
let out_addr_norms_fill = [ WORD_RULE `word_add (out_p:int64) (word (64*0+32)) = word_add out_p (word 32)` ];;
(* The counter index norms for unfolding aes_ctr_block at i = 0: aes_ctr_block
   aes256_cipher c .. K is the cipher of ctr_block nonce (K+c), while the
   code's counter is c+K, so bridge K+c to c+K (and 0+c to c). *)
let fill_ctr_idx_norms = map (fun k ->
  ARITH_RULE (mk_eq(mk_binop `+` (mk_small_numeral k) `c:num`,
                    if k = 0 then `c:num` else mk_binop `+` `c:num` (mk_small_numeral k)))) [0;1;2;3;4;5;6;7];;
let OUT_STORE_FILL : tactic =
  REWRITE_TAC out_addr_norms_fill THEN
  ASM_REWRITE_TAC[] THEN INFOLD_FILL THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ADD_CLAUSES] THEN REWRITE_TAC fill_idx_norms THEN
  (* XOR_AES256_CIPHER_RECONSTRUCT_DEC folds the code's AES tower to
     word_reversefields 8 (aes256_cipher (ctr_block nonce (c+K)) rk);
     WORD_REVERSEFIELDS_REVERSEFIELDS cancels the double reversal of the
     counter block and the round keys, MAP and rk15 rebuild rk, and the
     definition of aes_ctr_block with the K+c -> c+K bridge gives the
     right-hand side. *)
  ((REWRITE_TAC[XOR_AES256_CIPHER_RECONSTRUCT_DEC] THEN
    REWRITE_TAC[WORD_REVERSEFIELDS_REVERSEFIELDS] THEN REWRITE_TAC[MAP; WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[aes_ctr_block] THEN REWRITE_TAC fill_ctr_idx_norms THEN REFL_TAC)
   ORELSE
   (REWRITE_TAC(map GSYM out_via_lemmas) THEN REWRITE_TAC[aes_ctr_block] THEN REWRITE_TAC fill_ctr_idx_norms THEN
    (fun (asl,w) ->
       let c = try rand(find_term (fun t -> match t with Comb(Comb(Const("ctr_block",_),_),_) -> true | _ -> false) (rhs w))
               with _ -> `4` in
       let inb = lhand (lhs w) in
       MP_TAC(SPECL[c; inb] (GENL [`c:num`;`inb:int128`] (MATCH_MP KEYSTREAM_FOLD256 (ASSUME rk15)))) (asl,w)) THEN
    DISCH_TAC THEN POP_ASSUM(fun th -> REWRITE_TAC[GSYM th]) THEN CONV_TAC WORD_BITWISE_RULE)
   ORELSE ALL_TAC);;   (* never fail: a residual shows in the final state *)

(* The input reads of the fill (Q0/Q1/Q14 = inblock K): the read may already be
   folded to inblock K by INFOLD_FILL or ASM_REWRITE_TAC, leaving the index
   equation inblock K = inblock (4*0+K), or be a raw read at in_p + word N
   (N = 16..112), or at in_p itself (block 0).  Normalize 4*0+K to K and 4*0 to
   0, normalize the address (in_p itself as in_p + word (16*0)) and use the
   input forall. *)
let IN_READ_FILL : tactic =
  REWRITE_TAC (ARITH_RULE `4*0=0` :: fill_idx_norms) THEN
  (* block 0: the read address is in_p itself (no word_add); only in that case
     rewrite in_p to word_add in_p (word (16*0)) by SUBST1_TAC *)
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

(* The fill stepper: the setup, steps 1-31 (priming the middle lanes at s23),
   the guard and the cbz at step 32, then steps 33-143 (0xac..0x264), ending at
   the cbz at pc + 0x268.  The keep list adds X1, so that X1 = word loop_count
   persists from the guard to that cbz. *)
let NSTEP_FILL = 143;;
let REDSETX_FILL = "X1"::REDSETX_DEC;;
let fill_step_all =
  fill_setup_tac THEN
  (* steps 1-31: byte length, round keys, tag, IV halves to the four slots *)
  DEC_STEPS_TAC REDSETX_FILL fill_prime_hook (1--31) THEN
  (* the guard and the cbz at 0xa8, falling through to 0xac *)
  FILL_GUARD_CBZ_TAC THEN
  (* steps 33-143 (0xac..0x264), with the counter merges at the store steps 43,
     48, 53 and 56 *)
  DEC_STEPS_TAC REDSETX_FILL (merge_hook dec_fill_merges MERGE_CTR128_FILL) (33--NSTEP_FILL) THEN
  DEC_NORM_ASM_TAC;;

(* Closing swp_inv 0 at pc + 0x268 with the dispatcher CLOSE_DEC of the body
   leg at i = 0: the conjuncts have the shapes of the body leg's, the tag is
   that of the empty list (tag0) with its halves swapped, and the output forall
   j < 4*0 is vacuous.

   OUT_FRAME_fill: as OUT_FRAME_dec, except that there is no incoming output
   forall to accept, so the vacuous part j < 4*0 is discharged first by
   MULT_CLAUSES, LT and ARITH_TAC. *)
let OUT_FRAME_fill : tactic =
  REWRITE_TAC[ARITH_RULE `j < 4 * (i+1) <=>
                          j < 4 * i \/ j = 4*i+0 \/ j = 4*i+1 \/ j = 4*i+2 \/ j = 4*i+3`] THEN
  ASM_REWRITE_TAC[TAUT `p \/ q ==> r <=> (p ==> r) /\ (q ==> r)`] THEN
  REWRITE_TAC[FORALL_AND_THM; FORALL_UNWIND_THM2] THEN
  REWRITE_TAC[ARITH_RULE `16 * (4*i+0) = 64*i`; ARITH_RULE `16 * (4*i+1) = 64*i+16`;
     ARITH_RULE `16 * (4*i+2) = 64*i+32`; ARITH_RULE `16 * (4*i+3) = 64*i+48`] THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  (* the vacuous forall j < 4*0 *)
  TRY (REWRITE_TAC[MULT_CLAUSES; LT] THEN ARITH_TAC) THEN
  TRY (FIRST_X_ASSUM (fun th -> if (try is_forall(concl th) && free_in `out_p:int64` (concl th) with _->false)
                                then MATCH_ACCEPT_TAC th else NO_TAC)) THEN
  TRY (ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  ASM_REWRITE_TAC[] THEN INFOLD_dec THEN ASM_REWRITE_TAC[] THEN
  OUT_BLOCK_CLOSE_dec;;
(* Closers for the registers the fill computes from len_bits and ivhi (X1, X15,
   X9, X13), which the body leg's invariant has in symbolic form already. *)
(* X15: word_ushr (word len_bits) 3 = word (len_bits DIV 8) *)
let REG_X15_FILL : tactic =
  REWRITE_TAC[word_ushr] THEN AP_TERM_TAC THEN
  SUBGOAL_THEN `val(word len_bits:int64) = len_bits` SUBST1_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    UNDISCH_TAC `len_bits < 2 EXP 64` THEN ARITH_TAC; ARITH_TAC];;
(* X9: word_and (word_ushr (word_ushr (word len_bits) 3) 4) (word 3) =
       word loop_remain *)
let REG_X9_FILL : tactic =
  REWRITE_TAC[WORD_USHR_COMPOSE] THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
  REWRITE_TAC[word_ushr] THEN
  SUBGOAL_THEN `val(word len_bits:int64) = len_bits` SUBST1_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    UNDISCH_TAC `len_bits < 2 EXP 64` THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `3 = 2 EXP 2 - 1`] THEN
  REWRITE_TAC[WORD_AND_MASK_WORD; VAL_WORD; DIMINDEX_64] THEN REWRITE_TAC[MOD_MOD_EXP_MIN] THEN
  MAP_EVERY EXPAND_TAC ["loop_remain"; "nblocks"] THEN AP_TERM_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC;;
(* X1: word_sub (word loop_count) (word 1) = word (loop_count - 1) *)
let REG_X1_FILL : tactic =
  SUBGOAL_THEN `val(word loop_count:int64) = loop_count` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    MAP_EVERY (fun t -> TRY(UNDISCH_TAC t)) [`nblocks DIV 4 = loop_count`; `16 * nblocks < 2 EXP 64`] THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[WORD_SUB] THEN COND_CASES_TAC THENL
   [AP_TERM_TAC THEN REWRITE_TAC[VAL_WORD_1];
    FIRST_X_ASSUM MP_TAC THEN REWRITE_TAC[VAL_WORD_1] THEN
    UNDISCH_TAC `1 <= loop_count` THEN ASM_REWRITE_TAC[] THEN ARITH_TAC];;
(* X13 at i = 0: word_zx (word_bytereverse (word_zx (word_ushr ivhi 32))) =
        word_zx (word (4*0+c)) *)
let REG_X13_FILL : tactic =
  fun (asl,w) ->
    (REWRITE_TAC[MATCH_MP BASE_CTR_DEC (find_ctr_join asl)] THEN
     REWRITE_TAC[ARITH_RULE `4 * 0 + c = c`]) (asl,w);;
(* The fill closer: the foralls go to OUT_FRAME_fill, the computed registers to
   their closers (X15, X9 and X13 do not occur in CLOSE_DEC, and the fill's X1
   differs from the body's), the rest to the dispatcher of the body leg. *)
let CLOSE_FILL : tactic = fun (asl,w) ->
  let hd t = try fst(dest_const(fst(strip_comb t))) with _->"" in
  (* the head name, constant or variable (inblock is a variable of the
     specification, which has and hd, for constants, miss) *)
  let hdname t = (try fst(dest_const(fst(strip_comb t))) with _ -> (try fst(dest_var(fst(strip_comb t))) with _ -> "")) in
  let inb = `inblock:num->int128` in
  let deep_ghash = try has "nist_ghash" w with _ -> false in
  if is_forall w then OUT_FRAME_fill (asl,w)
  else if is_eq w && hd(lhs w)="word_ushr" && free_in `len_bits:num` w && not(has "word_and" w) then REG_X15_FILL (asl,w)
  else if is_eq w && hd(lhs w)="word_and" && free_in `len_bits:num` w then REG_X9_FILL (asl,w)
  else if is_eq w && hd(lhs w)="word_sub" && free_in `loop_count:num` w && not(has "pc" w) then REG_X1_FILL (asl,w)
  else if is_eq w && hd(lhs w)="word_zx" && has "word_ushr" (lhs w) && free_in `ivhi:int64` (lhs w) then REG_X13_FILL (asl,w)
  (* the tag at i = 0, over the empty list: reduce to tag0, then WORD_BLAST *)
  else if deep_ghash then SEED_FILL (asl,w)
  (* the index equation inblock K = inblock (4*0+K) left by an input read
     already folded *)
  else if is_eq w && hdname(lhs w)="inblock" && hdname(rhs w)="inblock" then
    (REWRITE_TAC (ARITH_RULE `4*0=0` :: fill_idx_norms) THEN REFL_TAC) (asl,w)
  (* the input reads read (bytes128 (in_p+..)) = inblock (4*0+K) for Q0/Q1/Q14,
     or of in_p itself for block 0 *)
  else if is_eq w && hd(lhs w)="read" && free_in `in_p:int64` (lhs w) && free_in inb (rhs w) then IN_READ_FILL (asl,w)
  (* the output store read (bytes128 (out_p+..)) = word_xor (aes_ctr_block ..)
     (inblock ..) *)
  else if is_eq w && hd(lhs w)="read" && free_in `out_p:int64` (lhs w) && has "aes_ctr_block" (rhs w) then OUT_STORE_FILL (asl,w)
  (* the GHASH partials (pmul/xor/zx towers over in_p reads) *)
  else if free_in `in_p:int64` w then (GHASH_PARTIAL_FILL ORELSE CLOSE_DEC) (asl,w)
  else CLOSE_DEC (asl,w);;

let FILL_TO_CBZ_DEC = GEN_ALL(prove(fill_cbz_goal,
  fill_step_all THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[SWP_SUB_LEMMA_DEC] THEN
  REPEAT CONJ_TAC THEN CLOSE_FILL));;

(* One-instruction hops out of a whole swp_inv state: swp_inv_dec_at gives the
   invariant body for ENSURES_SEQUENCE_TAC, hop_init_dec opens the state, and
   after the step every conjunct is an unchanged read or the branch PC,
   resolved from the val fact assumed beforehand. *)
let REFOLD_ABI = REWRITE_TAC[GSYM MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI];;
let swp_inv_dec_at idx =
  rhs(concl((BETA_CONV THENC REWRITE_CONV[ADD_CLAUSES]) (mk_comb(swp_inv,idx))));;
let hop_init_dec : tactic =
  ENSURES_INIT_TAC "s0" THEN RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_4]) THEN REWRITE_TAC[htable_mem_4];;

(* FILLLEG: FILL_TO_CBZ_DEC, then the cbz at 0x268 not taken (X1 = word
   (loop_count - 1) is nonzero). *)
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

(* ------------------------------------------------------------------------- *)
(* The drain legs: swp_inv (loop_count-1) -> drain_bridge at pc + 0x6c0.     *)
(* They finish the last group (blocks 4*(loop_count-1)..4*loop_count-1): the *)
(* tag becomes nist_ghash over the 4*loop_count input blocks (halves         *)
(* swapped), and the outputs of blocks 4*(loop_count-1), +1 and +3 are       *)
(* stored (str q5/q12/q5 at 0x6a4/0x6b4/0x6b8; block +2 was stored by the    *)
(* last iteration or the fill).  DRAIN_FROM_574 simulates the drain          *)
(* 0x574..0x6bc (83 instructions, ending with b 0x6c0) once, from swp_inv    *)
(* (loop_count-1) at pc + 0x574, under 1 <= loop_count; DRAINLEG adds the    *)
(* cbnz at 0x570 not taken (X1 = word 0), and LEG_LC1 enters it from the cbz *)
(* at 0x268.                                                                 *)
(* ------------------------------------------------------------------------- *)

(* drain_bridge at pc + 0x6c0, the state the single-block tail starts from: the
   tag in Q30 is settled (nist_ghash over the 4*loop_count input blocks, halves
   swapped) and the outputs of blocks 0..4*loop_count-1 are stored.  The tail
   reloads Q12, Q13 and Q14 from the key table at 0x6c0..0x6c8, so the bridge
   omits them.  The reduction constant Q7, which the tail's reductions need, is
   carried unchanged from swp_inv (the drain does not write it), and so is the
   staged slot at sp + 160 (the drain does not write it either): the tail
   rebuilds its counter blocks from that slot's nonce lanes, re-storing only
   the counter word at +12. *)
let drain_bridge = mk_abs(`s:armstate`, list_mk_conj
 [`aligned_bytes_loaded s (word pc) aes256_gcm_dec_tmc`;
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
           word_xor (aes_ctr_block aes256_cipher c nonce rk j) (inblock j)`]);;

(* The goal of DRAINLEG: swp_inv (loop_count-1) at pc + 0x570 -> drain_bridge
   at pc + 0x6c0. *)
let drain_hyps = mk_leg_hyps [`2 <= loop_count`] [`len_bits < 2 EXP 64`] [];;
let drain_frame = fill_frame;;
let drain_goal = mk_leg_goal drain_hyps (leg_state_dec swp_inv `0x570` `loop_count - 1`) drain_bridge drain_frame;;
(* The drain itself is simulated once, from 0x574, under 1 <= loop_count;
   DRAINLEG (cbnz at 0x570 not taken) and LEG_LC1 (cbz at 0x268 taken) are hops
   into it. *)
let drain_hyps1 = mk_leg_hyps [`1 <= loop_count`] [`len_bits < 2 EXP 64`] [];;
let drain574_goal = mk_leg_goal drain_hyps1 (leg_state_dec swp_inv `0x574` `loop_count - 1`) drain_bridge drain_frame;;

(* The drain setup: enter swp_inv at pc + 0x574 with i = loop_count - 1, using
   the leg entry of the body (LEG_INIT_DEC); the round keys are already in
   registers (no KEY_EXPAND_TAC, unlike the fill).  Then X1 = word 0, and the
   input split covers the blocks 4m..4m+3 of the last group
   (m = loop_count - 1). *)
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

(* The drain stepper: steps 1..83 (0x574..0x6bc, the b 0x6c0 at 0x6bc being
   step 83) with the keep list of the body and no counter merges; the cbnz at
   0x570 is the hop of DRAINLEG. *)
let NSTEP_DRAIN = 83;;
let drain_step_all =
  drain_setup_tac THEN
  DEC_STEPS_TAC REDSETX_DEC (K ALL_TAC) (1--NSTEP_DRAIN) THEN
  DEC_NORM_ASM_TAC;;

(* The drain closer.  The conjuncts of drain_bridge are the alignment and PC,
   the carried registers (from the invariant and the stepping), the settled tag
   (the last Horner step), the staged slot at sp + 160 and the output forall,
   which includes the blocks the drain stores; CLOSE_DRAIN routes the pointers,
   X13, the tag and the output forall to the closers below, the frame to
   close_frame_dec and the rest to ASM_REWRITE_TAC and CLOSE_DEC. *)
(* The pointers X0/X2: (loop_count-1)+1 = loop_count and
   64*(loop_count-1)+64 = 64*loop_count. *)
let DRAIN_PTR_TAC : tactic =
  AP_TERM_TAC THEN AP_TERM_TAC THEN UNDISCH_TAC `1 <= loop_count` THEN ARITH_TAC;;
(* X13: word_zx (word_add (word_zx (word_zx (word (4(lc-1)+c)))) (word 4)) =
   word_zx (word (4*lc+c)).  The drain does add w13,w13,#4 at 0x57c; ZX_WT
   collapses the int32 -> int64 -> int32 round trip, GSYM WORD_ADD merges the
   +4, then AP_TERM_TAC and ARITH_TAC. *)
let ZX_WT = prove(`word_zx(word_zx(w:int32):int64):int32 = w`, CONV_TAC WORD_BLAST);;
let DRAIN_X13_TAC : tactic =
  REWRITE_TAC[ZX_WT] THEN REWRITE_TAC[GSYM WORD_ADD] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN UNDISCH_TAC `1 <= loop_count` THEN ARITH_TAC;;
(* The settled tag.  SWP_Q30_SEED_TAC proves the tag step of the body (the
   code's reduction is nist_ghash .. (4*(i+1)) with its halves swapped) for a
   variable index i.  Here the index is loop_count - 1, so first rewrite
   4*loop_count as 4*((loop_count-1)+1) on the right (true only for
   1 <= loop_count, hence the SUBGOAL_THEN) and abbreviate m = loop_count - 1;
   then SWP_Q30_SEED_TAC applies with i := m and leaves the same swapped-halves
   form on both sides, which REFL_TAC closes.  That final REFL_TAC needs the
   int64 annotations of the word_subwords in the Q30 conjunct of
   drain_bridge. *)
let DRAIN_Q30_TAC : tactic =
  SUBGOAL_THEN `4 * loop_count = 4 * ((loop_count - 1) + 1)`
    (fun th -> GEN_REWRITE_TAC (RAND_CONV o TOP_DEPTH_CONV) [th]) THENL
   [UNDISCH_TAC `1 <= loop_count` THEN ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `m = loop_count - 1` THEN
  SWP_Q30_SEED_TAC THEN REFL_TAC;;
(* The output forall j < 4*loop_count: the blocks j < 4*(loop_count-1) from the
   invariant and the four blocks of the last group, by OUT_FRAME_dec after
   rewriting 4*loop_count as 4*((loop_count-1)+1). *)
let DRAIN_OUTFRAME_TAC : tactic =
  SUBGOAL_THEN `4 * loop_count = 4 * ((loop_count-1)+1)` (fun th -> GEN_REWRITE_TAC (ONCE_DEPTH_CONV) [th]) THENL
   [UNDISCH_TAC `1 <= loop_count` THEN ARITH_TAC; ALL_TAC] THEN
  (OUT_FRAME_dec ORELSE (ASM_REWRITE_TAC[] THEN CLOSE_DEC));;

let CLOSE_DRAIN : tactic = fun (asl,w) ->
  let hd t = try fst(dest_const(fst(strip_comb t))) with _->"" in
  let has_mc t = try can(find_term(fun x->match x with Const("MAYCHANGE",_)->true|_->false)) t with _->false in
  let deep_ghash = try has "nist_ghash" w with _ -> false in
  if has_mc w then close_frame_dec (asl,w)
  else if not(is_eq w) && not(is_forall w) then ASM_REWRITE_TAC[] (asl,w)
  else if is_forall w then DRAIN_OUTFRAME_TAC (asl,w)
  else if hd(lhs w)="word_add" && (free_in `in_p:int64` w || free_in `out_p:int64` w) then DRAIN_PTR_TAC (asl,w)
  else if hd(lhs w)="word_zx" && free_in `loop_count:num` (lhs w) then DRAIN_X13_TAC (asl,w)
  else if deep_ghash then DRAIN_Q30_TAC (asl,w)
  (* the staged slot at sp + 160, word_reversefields 8 (ctr_block nonce
     (4*(loop_count-1)+c)), carried unchanged from the invariant (the drain
     does not write sp + 160): ASM_REWRITE_TAC resolves the read over the 83
     steps to its value at s0, else SP_SLOT_dec folds it *)
  else if is_eq w && hd(lhs w)="read" && free_in `stackpointer:int64` (lhs w) && has "ctr_block" (rhs w) then
    (ASM_REWRITE_TAC[] THEN TRY (SP_SLOT_dec_fast ORELSE SP_SLOT_dec)) (asl,w)
  else (ASM_REWRITE_TAC[] THEN TRY CLOSE_DEC) (asl,w);;
let DRAIN_FROM_574 = GEN_ALL(prove(drain574_goal,
  drain_step_all THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN CLOSE_DRAIN));;

(* DRAINLEG: the cbnz at 0x570 not taken (X1 = word 0 at index loop_count - 1),
   then DRAIN_FROM_574. *)
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

(* ------------------------------------------------------------------------- *)
(* The tail leg TAILLEG: drain_bridge at pc + 0x6c0 -> tail_post at          *)
(* pc + 0x7c4, over the loop_remain remaining blocks.                        *)
(* ------------------------------------------------------------------------- *)

(* The tail invariant tail_inv i, at pc + 0x6d0 and pc + 0x7ac: the
   drain_bridge state advanced by i blocks (X0 and X2 by 16*i; the counter
   X13, the remaining count X9 and the tag Q30 follow i), with H^1 in Q12
   and the middle terms in Q14 (reloaded at 0x6c0..0x6c8), and the nonce
   lanes of the slot at sp + 160 (bytes64 at +0, bytes32 at +8) instead of
   the whole slot. *)
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
             word_xor (aes_ctr_block aes256_cipher c nonce rk j) (inblock j))`;;

(* tail_post at pc + 0x7c4, after the stores: the tag is word_reversefields 8
   of nist_ghash over all nblocks blocks, the ivec holds ctr_block nonce
   (nblocks + c) (the code stores the counter word at ivec_p + 12),
   X0 = len_bits DIV 8, and the output forall covers all nblocks blocks (at the
   exit of the loop, i = loop_remain and 4*loop_count + loop_remain =
   nblocks). *)
let tail_post = mk_abs(`s:armstate`, list_mk_conj
 [`aligned_bytes_loaded s (word pc) aes256_gcm_dec_tmc`;
  `read PC s = word (pc + 0x7c4)`;
  `read (memory :> bytes128 tag_p) s = word_reversefields 8
     (nist_ghash (aes256_cipher (word 0) rk) tag0
        (list_of_seq (nist_input_block inblock) nblocks))`;
  `read (memory :> bytes128 ivec_p) s =
     word_reversefields 8 (ctr_block nonce (nblocks + c))`;
  `read X0 s = word (len_bits DIV 8)`;
  `!j. j < nblocks ==> read (memory :> bytes128 (word_add out_p (word(16*j)))) s =
           word_xor (aes_ctr_block aes256_cipher c nonce rk j) (inblock j)`]);;

(* The goal of TAILLEG: drain_bridge (the postcondition of DRAINLEG) at
   pc + 0x6c0 -> tail_post at pc + 0x7c4. *)
let tail_hyps = mk_leg_hyps [] [`len_bits < 2 EXP 64`] [];;
let tail_frame = `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
      MAYCHANGE [X19; X20; X21; X22; X23; X24; X25; X26; X27; X28; X29; X30] ,,
      MAYCHANGE [Q0; Q1; Q2; Q3; Q4; Q5; Q6; Q7; Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15; Q16; Q17; Q29; Q30; Q31] ,,
      MAYCHANGE [memory :> bytes(out_p:int64, 16 * nblocks)] ,,
      MAYCHANGE [memory :> bytes(tag_p:int64,16)] ,, MAYCHANGE [memory :> bytes(ivec_p:int64,16)] ,,
      MAYCHANGE [memory :> bytes(word_add stackpointer (word 160):int64, 64)] ,, MAYCHANGE [events]`;;
let tail_goal = mk_leg_goal tail_hyps drain_bridge tail_post tail_frame;;

(* The tail.  For loop_remain = 0, TAIL_DEGEN steps the three key-table
   reloads, the cbz x9 at 0x6cc (taken) and the five instructions 0x7b0..0x7c0
   (9 steps).  Otherwise tail_tac uses ENSURES_WHILE_UP_TAC over loop_remain
   iterations at pc + 0x6d0 / pc + 0x7ac with tail_inv:
   - the initialization: the three reloads and the cbz not taken (4 steps);
   - the body: the 55 instructions 0x6d0..0x7a8, with the counter merge
     TAIL_CTR_MERGE at s5 (after the counter word store at 0x6e0), the output
     store at step 53 and the one-block tag update TAIL_Q30_CLOSE;
   - the back edge: the cbnz x9 at 0x7ac taken;
   - the exit: the cbnz not taken and the five stores (6 steps), closed as in
     TAIL_DEGEN. *)

let woff_t n = mk_comb(mk_comb(`word_add:int64->int64->int64`,`stackpointer:int64`),mk_comb(`word:num->int64`,mk_small_numeral n));;

(* The nonce lanes for tail_inv 0: drain_bridge has the whole slot at sp + 160
   (word_reversefields 8 (ctr_block nonce (4*(lc-1)+c))), and tail_inv 0 wants
   its two nonce lanes, the bytes64 at +0 and the bytes32 at +8, as subwords of
   word_reversefields 8 (ctr_block nonce c).  They are derived at s0 by
   B64_OF_B128_LO / B32_OF_B128_MID (a lane is a subword of the enclosing
   block) and SUBW_LO_CI / SUBW_MID_CI (the nonce lanes do not depend on the
   counter), and kept by STRIP_ASSUME_TAC across the four setup steps
   (ldr q12/q13/q14 and the cbz), which do not store. *)
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

(* The tail counter merge at sK: read (bytes128 (sp+160)) sK =
   word_reversefields 8 (ctr_block nonce (4*loop_count+i+c)), from the nonce
   lanes carried in tail_inv and the counter word just stored at +12. *)
let TAIL_CTR_MERGE sK : tactic =
  let sp128 = CONV_RULE(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)(ISPECL [`memory`; woff_t 160; mk_var(sK,`:armstate`)] splitL) in
  let sp64  = CONV_RULE(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)(ISPECL [`memory`; woff_t 168; mk_var(sK,`:armstate`)] splitL2) in
  SUBGOAL_THEN (subst [mk_var(sK,`:armstate`),`s:armstate`]
     `read (memory :> bytes128 (word_add stackpointer (word 160))) s =
      word_reversefields 8 (ctr_block nonce (4 * loop_count + i + c))`) ASSUME_TAC THENL
   [GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [sp128; sp64] THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[ctr_block] THEN
    (CONV_TAC WORD_BLAST ORELSE CONV_TAC WORD_RULE ORELSE (REPEAT AP_TERM_TAC THEN ARITH_TAC)); ALL_TAC];;

(* Closers for the tail body. *)

(* X9: word_sub (word (loop_remain - i)) (word 1) = word (loop_remain-(i+1)) *)
let TAIL_X9_CLOSE : tactic =
  SUBGOAL_THEN `word_sub (word (loop_remain - i)) (word 1):int64 = word ((loop_remain - i) - 1)`
    (fun th -> REWRITE_TAC[th]) THENL
   [GEN_REWRITE_TAC RAND_CONV [WORD_SUB] THEN COND_CASES_TAC THENL
     [REFL_TAC;
      FIRST_X_ASSUM MP_TAC THEN REWRITE_TAC[VAL_WORD_1] THEN UNDISCH_TAC `i < loop_remain` THEN ARITH_TAC];
    AP_TERM_TAC THEN UNDISCH_TAC `i < loop_remain` THEN ARITH_TAC];;

(* The one-block GHASH step (GHASH_POLYVAL_ACC_BATCHED with an empty list of
   further blocks), the analogue of SWP_GHASH_BRANCH2_256: it folds the
   reduction polyval_reduce_prop3 (pmul (acc XOR block) h0) of the settled
   one-block tower to nist_ghash .. (m+1). *)
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

(* The one-block tag update: the halves-swapped nist_ghash .. (4lc+i) XOR block
   4lc+i, through one pmull reduction, gives the halves-swapped nist_ghash ..
   (4lc+i+1).  The decrypt kernel hashes its input block (nist_input_block).
   After the byteswap128 and (64,128)-subword collapse, MATCH_MP_TAC reduces
   the goal to x = y, and with sofar, cipherblock, h and k abbreviated the
   proof passes through polyval_reduce_prop3 (word_pmul (word_xor sofar
   cipherblock) h):
   - the code's Karatsuba tower equals it: PMUL_KARATSUBA_JOIN_ALT,
     INBLOCK_REASSEMBLE and GSYM nist_input_block (the byte lanes become the
     block), POLYVAL_REDUCE_G2, the abbreviation w1 of the first reduction
     product, the two reduction products unified by WORD_BITWISE_RULE on their
     arguments and abbreviated to w2, then BITBLAST_RULE over the five free
     words w1, w2, p1, p2, p3 (bit-blasting the products themselves would not
     be practical);
   - it equals nist_ghash .. (4lc+i+1) by SWP_GHASH_BRANCH2_1BLK. *)
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
    (* ASM_REWRITE_TAC reintroduced ks (by the assumption defining ks): expand
       it again and distribute *)
    (TRY(EXPAND_TAC "ks")) THEN REWRITE_TAC[WORD_SUBWORD_XOR] THEN
    (* unify the arguments of the two reduction products (XOR rearrangements of
       the same five leaves) *)
    (fun (asl,w) ->
      let redp = filter (fun u->match u with
                   Comb(Comb(Const("word_pmul",_),_),Comb(Const("word",_),n)) when n=`13979173243358019584`->true|_->false)
                   (setify(find_terms (fun u->match u with Comb(Comb(Const("word_pmul",_),_),_)->true|_->false) w)) in
      match redp with
       [pm0; pm1] ->
         let getarg t = hd(snd(strip_comb t)) in
         (REWRITE_TAC[WORD_BITWISE_RULE(mk_eq(getarg pm1, getarg pm0))] ORELSE ALL_TAC) (asl,w)
      | _ -> ALL_TAC (asl,w)) THEN
    (* abbreviate the remaining reduction product as w2, drop the definitions
       and bit-blast *)
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

(* The output block of the tail body: all 14 rounds on the counter block
   word_reversefields 8 (ctr_block nonce (4lc+i+c)) merged at s5;
   XOR_AES256_CIPHER_RECONSTRUCT_DEC folds the code's tower to the cipher, i.e.
   to aes_ctr_block. *)
let TAIL_OUT_BLOCK : tactic =
  REWRITE_TAC[ADD_CLAUSES] THEN
  REWRITE_TAC[XOR_AES256_CIPHER_RECONSTRUCT_DEC] THEN
  REWRITE_TAC[WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
  REWRITE_TAC[MAP; WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[aes_ctr_block] THEN
  REWRITE_TAC[ARITH_RULE `(4 * loop_count + i) + c = 4 * loop_count + i + c`] THEN
  REFL_TAC;;

(* The output forall gains one block: j < 4lc+i+1 <=> j < 4lc+i \/ j = 4lc+i.
   The old part is the invariant's forall (accepted from the assumptions); the
   new block j = 4lc+i is the block just stored (TAIL_OUT_BLOCK). *)
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

(* The per-conjunct router of the tail body (after ENSURES_FINAL_STATE_TAC and
   ASM_REWRITE_TAC).  The stepper resolves Q30 to the code's value, so the tag
   conjunct has nist_ghash .. (4lc+i+1) on the right and the settled reduction
   on the left, and is routed by nist_ghash to TAIL_Q30_CLOSE.  TAIL_Q30_CLOSE
   is not among the alternatives of the FIRST below, since on other conjuncts
   it applies partially and leaves the reduction subgoal.  The alternatives are
   the pointers X0/X2, the counter X13, the count X9, the MAYCHANGE frame and
   the key-table reads. *)
let TAIL_STEP_CLOSE : tactic = fun (asl,w) ->
  if is_forall w && free_in `out_p:int64` w then TAIL_OUT_FRAME (asl,w)
  else if is_forall w && free_in `in_p:int64` w then ASM_REWRITE_TAC[] (asl,w)
  else if has "htable_mem_4" w then ASM_REWRITE_TAC[htable_mem_4] (asl,w)
  else if is_eq w && has "nist_ghash" w then TAIL_Q30_CLOSE (asl,w)
  else FIRST
    [ (AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC);
      (REWRITE_TAC[ZX_WT] THEN REWRITE_TAC[GSYM WORD_ADD] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC);
      TAIL_X9_CLOSE;
      close_frame_dec;
      (ASM_REWRITE_TAC[htable_mem_4]) ] (asl,w);;

(* The whole bytes128 ivec in the postcondition (not only the bytes32 at
   ivec_p + 12).  IVEC_SPLIT_TAIL, after ENSURES_INIT_TAC, splits the ivec read
   of drain_bridge (bytes128 ivec = word_reversefields 8 (ctr_block nonce c))
   into 4-byte cells (READ_MEMORY_SPLIT_CONV 2) so that the three nonce cells
   at ivec+0/+4/+8 survive the counter store (str w14,[x4,#12] touches only
   ivec+12).  IVEC_RECOMB_TAIL, at the final state, splits the ivec of the goal
   in the same way and closes it from these cells and the counter word. *)
let IVEC_SPLIT_TAIL : tactic =
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o CONV_RULE(READ_MEMORY_SPLIT_CONV 2) o
    check (fun th -> let c = concl th in
      is_eq c && free_in `ivec_p:int64` (lhs c) &&
      not(free_in `out_p:int64` (lhs c)) && not(free_in `in_p:int64` (lhs c)) &&
      not(free_in `htable_p:int64` (lhs c)) && not(free_in `tag_p:int64` (lhs c)) &&
      not(free_in `key_p:int64` (lhs c)) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "bytes128")) (lhs c)));;
(* word_zx to the same width is the identity: it collapses the int32 layers of
   the code's counter word tower. *)
let WORD_ZX_ID32 = prove(`!x:int32. word_zx x:int32 = x`, GEN_TAC THEN CONV_TAC WORD_BLAST);;
(* The counter cell tower (four int32 word_zx around word_bytereverse) is
   word_bytereverse of the inner word. *)
let ZXTOWER_COLLAPSE_32 = prove
 (`word_zx (word_zx (word_bytereverse (word_zx (word_zx (c:int32):int32):int32):int32):int32):int32 =
   word_bytereverse c`, CONV_TAC WORD_BLAST);;
(* IVEC_RECON: the bytes128 ivec as the counter word joined with the low 96
   bits (the nonce).  Use it once only (GEN_REWRITE_TAC with ONCE_DEPTH_CONV):
   its right-hand side contains ctr_block nonce c, which it matches again, so
   REWRITE_TAC would loop. *)
let IVEC_RECON = prove
 (`word_reversefields 8 (ctr_block nonce k):int128 =
   word_join (word_bytereverse (word (k):int32))
             (word_subword (word_reversefields 8 (ctr_block nonce c):int128) (0,96):(96)word)`,
  REWRITE_TAC[ctr_block] THEN CONV_TAC WORD_BLAST);;
(* IVEC_RECOMB_TAIL kidx: the ivec at the end, where kidx is the counter index
   of the goal (nblocks + c at the exit of the tail loop, 4*loop_count + c in
   TAIL_DEGEN).  Rewrite the right-hand side once by IVEC_RECON, split the goal
   and the ivec assumptions into bytes32 cells, collapse the counter word_zx
   tower in the ivec cell assumptions only (a blanket RULE_ASSUM_TAC would also
   rewrite inside the tag tower), ASM_REWRITE_TAC, fold every symbolic counter
   word to word kidx by AP_TERM_TAC and ASM_ARITH_TAC (4lc+lr+c associates to
   the right, so a plain substitution would miss it), and close each cell by
   WORD_BLAST: in ctr_block nonce K = word_join nonce (word K) the nonce cells
   do not depend on K and the counter cell is word K under word_bytereverse. *)
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

(* The per-conjunct router of the final stores, by shape, so that WORD_BLAST
   never meets a large conjunct: the bytes128 ivec goes to IVEC_RECOMB_TAIL,
   the tag (nist_ghash on the right) to an abbreviation of the GHASH value gv
   and WORD_BLAST, the MAYCHANGE frame to close_frame_dec, the rest to
   ASM_REWRITE_TAC.  mgv is the number of blocks hashed (4*loop_count in
   TAIL_DEGEN, nblocks at the exit of the loop). *)
let TAIL_WB_CLOSE (mgv:term) : tactic = fun (asl,w) ->
  if not(is_eq w) then
    (if has "MAYCHANGE" w then close_frame_dec (asl,w)
     else if is_forall w then ASM_REWRITE_TAC[] (asl,w)
     else ASM_REWRITE_TAC[] (asl,w))
  else if free_in `ivec_p:int64` (lhs w) && has "bytes128" (lhs w) then
    IVEC_RECOMB_TAIL (mk_binary "+" (mgv, `c:num`)) (asl,w)
  else if has "nist_ghash" (rhs w) then
    (* first resolve the tag read to the code's byteswapped value
       (ASM_REWRITE_TAC), then abbreviate the settled GHASH value gv and
       WORD_BLAST the byteswap (WORD_BLAST cannot prove an unresolved read) *)
    (ASM_REWRITE_TAC[] THEN
     ABBREV_TAC(mk_eq(`gv:int128`,
        list_mk_comb(`nist_ghash:int128->int128->(int128)list->int128`,
          [`aes256_cipher (word 0) rk:int128`; `tag0:int128`;
           mk_comb(`list_of_seq (nist_input_block inblock):num->(int128)list`, mgv)]))) THEN
     CONV_TAC WORD_BLAST) (asl,w)
  else (ASM_REWRITE_TAC[] ORELSE CONV_TAC WORD_BLAST) (asl,w);;

(* TAIL_DEGEN (loop_remain = 0) and tail_tac. *)
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
     [ASM_REWRITE_TAC[];
      (* the initialization: drain_bridge -> tail_inv 0 *)
      ENSURES_INIT_TAC "s0" THEN RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_4]) THEN
      TAIL_BASE_LANES THEN
      MAP_EVERY (DEC_STEP_TAC REDSETX_DEC) (1--3) THEN
      SUBGOAL_THEN `val(word loop_remain:int64) = loop_remain` ASSUME_TAC THENL
       [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
        MAP_EVERY(fun t->TRY(UNDISCH_TAC t)) [`nblocks MOD 4 = loop_remain`; `16 * nblocks < 2 EXP 64`] THEN ARITH_TAC; ALL_TAC] THEN
      DEC_STEP_TAC REDSETX_DEC 4 THEN ENSURES_FINAL_STATE_TAC THEN
      ASM_REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES; SUB_0; htable_mem_4];
      (* the body: tail_inv i -> tail_inv (i+1).  DEC_STEP_TAC keeps Q30, the
         tag carried by the loop, resolved to its value at s55; the key-table
         reads are anchors of the pruning and cross the counter store by the
         stack nonoverlaps of tail_hyps.  The counter merge is at s5, after the
         counter word store and before ldr q5,[sp,#160]. *)
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
      ENSURES_INIT_TAC "s0" THEN RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_4]) THEN
      SUBGOAL_THEN `read (memory :> bytes128 (word_add in_p (word (64 * loop_count + 16 * i)))) s0 = inblock (4 * loop_count + i)`
      ASSUME_TAC THENL
       [REWRITE_TAC[ARITH_RULE `64 * a + 16 * b = 16 * (4 * a + b)`] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        MAP_EVERY(fun t->TRY(UNDISCH_TAC t)) [`nblocks DIV 4 = loop_count`; `nblocks MOD 4 = loop_remain`; `i < loop_remain`] THEN ARITH_TAC; ALL_TAC] THEN
      MAP_EVERY (DEC_STEP_TAC REDSETX_DEC) (1--5) THEN TAIL_CTR_MERGE "s5" THEN MAP_EVERY (DEC_STEP_TAC REDSETX_DEC) (6--55) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      REPEAT CONJ_TAC THEN TAIL_STEP_CLOSE;
      (* the back edge: the cbnz x9 at 0x7ac (one instruction), with
         x9 = word (loop_remain - (i+1)) nonzero for i+1 < loop_remain, goes
         back to 0x6d0 *)
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
      ENSURES_INIT_TAC "s0" THEN RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_4]) THEN REWRITE_TAC[htable_mem_4] THEN
      ARM_STEPS_TAC AES256_GCM_DEC_EXEC [1] THEN ENSURES_FINAL_STATE_TAC THEN
      ASM_SIMP_TAC[WORD_SUB; LT_IMP_LE; VAL_EQ_0; WORD_SUB_EQ_0] THEN ASM_REWRITE_TAC[GSYM VAL_EQ] THEN
      SUBGOAL_THEN `val(word loop_remain:int64) = loop_remain` ASSUME_TAC THENL
       [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
        MAP_EVERY (fun t -> TRY(UNDISCH_TAC t)) [`nblocks MOD 4 = loop_remain`; `16 * nblocks < 2 EXP 64`] THEN ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[ARITH_RULE `i < loop_remain ==> ~(loop_remain = i)`];
      (* the exit: tail_inv loop_remain at 0x7ac (the cbnz not taken) ->
         tail_post at 0x7c4, through the five instructions after the cbnz (mov,
         rev64, the tag store, rev and the counter store): steps 1--6.  The tag
         by WORD_BLAST, the ivec by IVEC_RECOMB_TAIL (the ivec is split at the
         start so that its nonce cells survive), and the output forall is the
         invariant's at s6 (4lc+lr = nblocks). *)
      ENSURES_INIT_TAC "s0" THEN IVEC_SPLIT_TAIL THEN RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_4]) THEN
      SUBGOAL_THEN `4 * loop_count + loop_remain = nblocks` ASSUME_TAC THENL
       [MAP_EVERY(fun t->TRY(UNDISCH_TAC t)) [`nblocks DIV 4 = loop_count`; `nblocks MOD 4 = loop_remain`] THEN ARITH_TAC; ALL_TAC] THEN
      (* DEC_STEP_TAC prunes the tag tower; the split ivec cells are carried as
         memory reads *)
      MAP_EVERY (DEC_STEP_TAC REDSETX_DEC) (1--6) THEN ENSURES_FINAL_STATE_TAC THEN
      REPEAT CONJ_TAC THEN
      (* the output forall j < nblocks: the invariant's forall at s6
         (4lc+lr = nblocks) *)
      TRY (FIRST_X_ASSUM(fun th -> if (try is_forall(concl th) && free_in `out_p:int64` (concl th) &&
             contains "s6" (string_of_term(concl th)) with _->false) then MP_TAC th else NO_TAC) THEN
           ASM_REWRITE_TAC[] THEN NO_TAC) THEN
      TAIL_WB_CLOSE `nblocks:num`]];;

let TAILLEG = prove(tail_goal, tail_tac);;

(* ========================================================================= *)
(* Composition: MAINLEG, LEG_LC0 and LEG_LC1 reach drain_bridge at           *)
(* pc + 0x6c0 for loop_count >= 2, = 0 and = 1, and CORE_FROM88 joins them   *)
(* with TAILLEG.  The legs are first widened to a common frame.              *)
(* ========================================================================= *)

(* Frame widening. *)
let broad_frame =
  let _,ens = dest_imp drain_goal in last(snd(strip_comb ens));;
let widen_leg = WIDEN_LEG_FRAME_RULE broad_frame;;

let FILLLEG_BROAD = widen_leg FILLLEG;;
let DRAINLEG_BROAD = widen_leg DRAINLEG;;
let BODYLEG_BROAD = widen_leg BODYLEG;;
let fill_pre_state = el 1 (snd(strip_comb(snd(dest_imp fill_goal))));;
let while_inv = mk_gabs(`k:num`, mk_comb(swp_inv, `k:num`));;

let gen_precond = list_mk_conj (filter (fun c -> c <> `2 <= loop_count`) (conjuncts(lhand fill_goal)));;
let mk_lcN_goal n = mk_imp(mk_conj(gen_precond, mk_eq(`loop_count:num`, mk_small_numeral n)),
    list_mk_icomb "ensures" [`arm`; fill_pre_state; drain_bridge; broad_frame]);;

(* MAINLEG, for 2 <= loop_count: fill_pre at pc + 0x2c -> drain_bridge at
   pc + 0x6c0 by FILLLEG, an ENSURES_WHILE_UP_TAC over loop_count - 1
   iterations of BODYLEG (pc + 0x26c -> pc + 0x570) and the back edge (the cbnz
   at 0x570 taken), then DRAINLEG. *)
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

(* LEG_LC0, loop_count = 0: the preamble (31 steps) and the cbz at 0xa8 taken,
   straight to drain_bridge at pc + 0x6c0.  The lemmas below fold the shifts of
   len_bits in X15, X1 and X9 and the GHASH of the empty list. *)
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

(* LEG_LC1, loop_count = 1: FILL_TO_CBZ_DEC, the cbz at 0x268 taken
   (X1 = word (loop_count - 1) = word 0) into the drain at 0x574, then
   DRAIN_FROM_574 at index loop_count - 1 = 0. *)

let lc1_frame = `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
      MAYCHANGE [X19; X20; X21; X22; X23; X24; X25; X26; X27; X28; X29; X30] ,,
      MAYCHANGE [Q0; Q1; Q2; Q3; Q4; Q5; Q6; Q7; Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15; Q16; Q17; Q29; Q30; Q31] ,,
      MAYCHANGE [memory :> bytes(out_p:int64, 16 * nblocks)] ,,
      MAYCHANGE [memory :> bytes(tag_p:int64,16)] ,, MAYCHANGE [memory :> bytes(ivec_p:int64,16)] ,,
      MAYCHANGE [memory :> bytes(word_add stackpointer (word 160):int64, 64)] ,, MAYCHANGE [events]`;;

let leg_lc1_goal = mk_imp(mk_conj(gen_precond, `loop_count = 1`),
    list_mk_icomb "ensures" [`arm`; fill_pre; drain_bridge; lc1_frame]);;

let FILL_TO_CBZ_DEC_LC1 = WIDEN_LEG_FRAME_RULE lc1_frame FILL_TO_CBZ_DEC;;
let DRAIN_FROM_574_LC1 = WIDEN_LEG_FRAME_RULE lc1_frame DRAIN_FROM_574;;

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
      (* the index bridge: the hop lands in the invariant at the index
         0 = loop_count - 1 *)
      ENSURES_PRECONDITION_TAC (leg_state_dec swp_inv `0x574` `loop_count - 1`) THEN CONJ_TAC THENL
       [GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
        FIRST_ASSUM(fun th -> if lhs(concl th) = `loop_count:num` then REWRITE_TAC[th] else NO_TAC) THEN
        CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];
        REFOLD_ABI THEN MATCH_MP_TAC DRAIN_FROM_574_LC1 THEN ASM_REWRITE_TAC[] THEN
        TRY(UNDISCH_TAC `loop_count = 1` THEN ARITH_TAC)]]];;
let LEG_LC1 = prove(leg_lc1_goal, leg_lc1_tac);;

(* CORE_FROM88, for every loop_count: fill_pre_state at pc + 0x2c -> tail_post
   at pc + 0x7c4, by the sequence at drain_bridge (pc + 0x6c0), split on
   loop_count = 0, 1 and >= 2, then TAILLEG. *)
let from88_frame = last(snd(strip_comb(snd(dest_imp(concl(SPEC_ALL TAILLEG))))));;
let widen_to_from88 = WIDEN_LEG_FRAME_RULE from88_frame;;
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

(* ========================================================================= *)
(* The core correctness theorem, pc + 0x2c -> pc + 0x7c4.  CORE_FROM88       *)
(* already spans the whole core (the fill leg includes the preamble), so the *)
(* proof only derives the round-key list identity from LENGTH rk = 15,       *)
(* restates the precondition as fill_pre_state and applies CORE_FROM88.      *)
(* ========================================================================= *)
(* The postcondition of CORE_FROM88 (with htable_mem_4 folded), stronger than
   that of the theorem. *)
let core_from88_post =
  el 2 (snd(strip_comb(snd(dest_imp(snd(strip_forall(concl CORE_FROM88)))))));;
let AES256_GCM_DEC_CORRECT = prove
 (`!in_p out_p len_bits tag_p ivec_p key_p htable_p tag0 nonce c rk inblock pc
     stackpointer.
       aligned 16 stackpointer /\
       ALLPAIRS nonoverlapping
        [(out_p, 16 * val len_bits DIV 128); (tag_p, 16); (ivec_p, 16);
         (word_add stackpointer (word 160), 64)]
        [(word pc, LENGTH aes256_gcm_dec_tmc);
         (in_p,  16 * val len_bits DIV 128); (key_p, 240); (htable_p, 96)] /\
       PAIRWISE nonoverlapping
        [(out_p, 16 * val len_bits DIV 128); (tag_p, 16); (ivec_p, 16);
         (word_add stackpointer (word 160), 64)]
    ==>
    ensures arm
      (\s. aligned_bytes_loaded s (word pc) aes256_gcm_dec_tmc /\
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
                    word_xor (aes_ctr_block aes256_cipher c nonce rk i) (inblock i)) /\
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
  (*** Weaken the postcondition to that of CORE_FROM88 first, before the case
     split on the round keys, so that both cases share it. ***)
  MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN
  EXISTS_TAC core_from88_post THEN CONJ_TAC THENL
   [GEN_TAC THEN BETA_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (*** CORE_FROM88 keeps rk abstract (wordlist_from_memory).  Case split on
     LENGTH rk = 15:
     - = 15: derive the round-key list identity [EL 0 rk; ...; EL 14 rk] = rk
       from LENGTH_EQ_LIST_OF_SEQ (without expanding rk), restate the
       C_ARGUMENTS precondition as fill_pre_state (ENSURES_PRECONDITION_TAC)
       and apply CORE_FROM88;
     - otherwise: the wordlist_from_memory precondition forces LENGTH rk = 15,
       so the precondition is unsatisfiable: ENSURES_PRECONDITION_TAC to
       (\s. F) and ENSURES_TRIVIAL. ***)
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

(* ------------------------------------------------------------------------- *)
(* The subroutine theorem: AES256_GCM_DEC_CORRECT lifted through the         *)
(* 11-instruction prologue and epilogue, which save and restore D8-D15 and   *)
(* X19-X30 in a 224-byte frame (ARM_ADD_RETURN_STACK_TAC).                   *)
(* ------------------------------------------------------------------------- *)

let AES256_GCM_DEC_NOIBT_SUBROUTINE_CORRECT = prove
 (`!in_p out_p len_bits tag_p ivec_p key_p htable_p tag0 nonce c rk inblock
    pc stackpointer returnaddress.
    aligned 16 stackpointer /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * val len_bits DIV 128); (tag_p, 16); (ivec_p, 16);
       (word_sub stackpointer (word 224), 224)]
      [(word pc, LENGTH aes256_gcm_dec_tmc);
       (in_p,  16 * val len_bits DIV 128); (key_p, 240); (htable_p, 96)] /\
    PAIRWISE nonoverlapping
      [(out_p, 16 * val len_bits DIV 128); (tag_p, 16); (ivec_p, 16);
       (word_sub stackpointer (word 224), 224)]
    ==>
    ensures arm
      (\s. aligned_bytes_loaded s (word pc) aes256_gcm_dec_tmc /\
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

(* The same for the full code, with its BTI landing pad. *)

let AES256_GCM_DEC_SUBROUTINE_CORRECT = prove
 (`!in_p out_p len_bits tag_p ivec_p key_p htable_p tag0 nonce c rk inblock
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
                    word_xor (aes_ctr_block aes256_cipher c nonce rk i) (inblock i)) /\
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
  MATCH_ACCEPT_TAC(ARM_ADD_IBT_RULE ~extra:[htable_mem_4; wordlist_from_memory]
    aes256_gcm_dec_mc aes256_gcm_dec_tmc AES256_GCM_DEC_NOIBT_SUBROUTINE_CORRECT));;

(* ========================================================================= *)
(* Constant-time (data-independent event trace) and memory-safety proofs, in *)
(* the scheme of the other 4-way proofs: an abstract event scaffold          *)
(* (CONCRETIZE_F_EVENTS_TAC) walked with the event-tracking simulator        *)
(* SAFE_SIM and closed by the closers of aes_gcm_common.ml.  The main region *)
(* pc + 0x2c -> pc + 0x6c0 is split on loop_count = 0, 1 and >= 2 (the fill, *)
(* loop_count - 1 iterations of the body with its back edge, and the drain); *)
(* the tail region pc + 0x6c0 -> pc + 0x7c4 is a loop over loop_remain.  The *)
(* subroutine version wraps the 224-byte frame.                              *)
(* ========================================================================= *)

let SAFE_SIM = SAFE_SIM_TAC AES256_GCM_DEC_EXEC;;

(* The drain pointers: the invariant at the loop exit has 64*(loop_count-1)+64,
   the sequence postcondition 64*loop_count.  DRAIN_ADDR writes loop_count as
   (loop_count-1)+1 (valid since loop_count >= 2) so that WORD_RULE sees only
   linear combinations. *)
let DRAIN_ADDR = DRAIN_ADDR_K `1`;;

let OPEN_DEC = OPEN_SWP_SAFE AES256_GCM_DEC_EXEC;;

(* The scaffold: loop_count = 0 (f_ev_m0), 1 (f_ev_m1), or >= 2 (the drain,
   loop_count - 1 iterations of the body and the fill), then the tail. *)
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
        [(word pc, LENGTH aes256_gcm_dec_tmc);
         (in_p,  16 * val len_bits DIV 128); (key_p, 240); (htable_p, 96)] /\
      PAIRWISE nonoverlapping
        [(out_p, 16 * val len_bits DIV 128); (tag_p, 16); (ivec_p, 16);
         (word_add stackpointer (word 160), 64)]
      ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) aes256_gcm_dec_tmc /\
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
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [X19; X20; X21; X22; X23; X24;
                      X25; X26; X27; X28; X29; X30] ,,
           MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
           MAYCHANGE [memory :> bytes(out_p, 16 * val len_bits DIV 128);
                      memory :> bytes(tag_p, 16);
                      memory :> bytes(ivec_p, 16);
                      memory :> bytes(word_add stackpointer (word 160), 64)])`,
  CONCRETIZE_F_EVENTS_TAC scaffold_dec THEN
  OPEN_DEC THEN

  (*** Top split at 0x6c0 (main region -> tail region). ***)
  ENSURES_EVENTS_SEQUENCE_TAC `pc + 0x6c0`
   `\s. read X0 s = word_add in_p (word (64 * loop_count)) /\
        read X2 s = word_add out_p (word (64 * loop_count)) /\
        read X3 s = tag_p /\ read X4 s = ivec_p /\ read X6 s = htable_p /\
        read SP s = stackpointer /\ read X9 s = word loop_remain` THEN
  CONJ_TAC THENL
   [(*** The main region pc+0x2c -> pc+0x6c0. ***)
    ENSURES_EVENTS_SEQUENCE_TAC `pc + 0xa8`
     `\s. read X0 s = in_p /\ read X2 s = out_p /\ read X3 s = tag_p /\
          read X4 s = ivec_p /\ read X6 s = htable_p /\ read SP s = stackpointer /\
          read X1 s = word loop_count /\ read X9 s = word loop_remain` THEN
    CONJ_TAC THENL [SAFE_SIM (1--31) THEN CLOSE; ALL_TAC] THEN

    (*** loop_count = 0: the cbz at 0xa8 taken, to 0x6c0. ***)
    ASM_CASES_TAC `loop_count = 0` THENL
     [REDUCE_IF0 `loop_count:num` THEN SAFE_SIM (1--1) THEN CLOSE; ALL_TAC] THEN
    REDUCE_IFN0 `loop_count:num` THEN

    (*** loop_count = 1: the fill, the cbz at 0x268 taken, the drain. ***)
    ASM_CASES_TAC `loop_count = 1` THENL
     [REDUCE_IFEQ `loop_count:num` `1` THEN SAFE_SIM (1--196) THEN CLOSE; ALL_TAC] THEN
    REDUCE_IFNE `loop_count:num` `1` THEN

    (*** loop_count >= 2: the fill, loop_count - 1 bodies, the drain. ***)
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
      (*** the fill: 0xa8 -> 0x26c (the cbz at 0x268 not taken), inv 0 ***)
      BEQ_NZ `1` THEN SAFE_SIM (1--113) THEN
      REPEAT CONJ_TAC THENL
       [ADDR_RECON;
        ADDR_RECON;
        REWRITE_TAC[SUB_0] THEN GEN_REWRITE_TAC RAND_CONV [WORD_SUB] THEN
        ASM_SIMP_TAC[ARITH_RULE `2 <= loop_count ==> 1 <= loop_count`];
        DEABBR THEN DISCHARGE_SAFETY_PROPERTY_TAC];
      (*** the body: 0x26c -> 0x26c, or 0x574 after the last iteration; 193
         instructions and the cbnz at 0x570, so 194 steps ***)
      REWRITE_TAC[] THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
      SUBGOAL_THEN `loop_count - 1 < 2 EXP 64` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      SAFE_SIM (1--194) THEN CLOSE_R2;
      (*** the drain: 0x574 -> 0x6c0, 83 instructions ***)
      SAFE_SIM (1--83) THEN REPEAT CONJ_TAC THENL
       [DRAIN_ADDR; DRAIN_ADDR; DEABBR THEN DISCHARGE_SAFE_ROBUST]];

    ALL_TAC] THEN

  (*** The tail region pc+0x6c0 -> pc+0x7c4. ***)
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

(* ------------------------------------------------------------------------- *)
(* The whole-function version, obtained from the core theorem exactly as the *)
(* correctness theorem is: the 11-instruction prologue and epilogue save and *)
(* restore the callee-saved registers in a 224-byte frame.                   *)
(* ------------------------------------------------------------------------- *)
let AES256_GCM_DEC_NOIBT_SUBROUTINE_SAFE = prove
 (`exists f_events.
    forall e in_p len_bits out_p tag_p ivec_p key_p htable_p pc stackpointer returnaddress.
      aligned 16 stackpointer /\
      ALLPAIRS nonoverlapping
        [(out_p, 16 * val len_bits DIV 128); (tag_p, 16); (ivec_p, 16);
         (word_sub stackpointer (word 224), 224)]
        [(word pc, LENGTH aes256_gcm_dec_tmc);
         (in_p,  16 * val len_bits DIV 128); (key_p, 240); (htable_p, 96)] /\
      PAIRWISE nonoverlapping
        [(out_p, 16 * val len_bits DIV 128); (tag_p, 16); (ivec_p, 16);
         (word_sub stackpointer (word 224), 224)]
      ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) aes256_gcm_dec_tmc /\
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
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(out_p, 16 * val len_bits DIV 128);
                      memory :> bytes(tag_p, 16);
                      memory :> bytes(ivec_p, 16);
                      memory :> bytes(word_sub stackpointer (word 224), 224)])`,
  ARM_ADD_RETURN_STACK_TAC
    ~pre_post_nsteps:(11, 11)
    AES256_GCM_DEC_EXEC AES256_GCM_DEC_SAFE
    `[X19; X20; X21; X22; X23; X24; X25; X26; X27; X28; X29; X30;
      D8; D9; D10; D11; D12; D13; D14; D15]` 224 THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

(* The same for the full code, with its BTI landing pad. *)

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
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(out_p, 16 * val len_bits DIV 128);
                      memory :> bytes(tag_p, 16);
                      memory :> bytes(ivec_p, 16);
                      memory :> bytes(word_sub stackpointer (word 224), 224)])`,
  MATCH_ACCEPT_TAC(ARM_ADD_IBT_RULE
    aes256_gcm_dec_mc aes256_gcm_dec_tmc AES256_GCM_DEC_NOIBT_SUBROUTINE_SAFE));;
