(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Functional correctness, constant-time and memory-safety proofs of the     *)
(* AES-128-GCM bulk decryption kernel aes128_gcm_dec, the 4-way              *)
(* software-pipelined kernel.                                                *)
(*                                                                           *)
(* The kernel processes the len_bits DIV 128 whole 16-byte blocks of its     *)
(* input: block i is decrypted in counter mode with the counter block        *)
(* ctr_block nonce (i + c), the input (ciphertext) block is folded into the  *)
(* GHASH tag, and the tag and the next counter block                         *)
(* ctr_block nonce (nblocks + c) are written back; X0 returns the byte       *)
(* length len_bits DIV 8.  The output may be the input buffer itself         *)
(* (in-place operation).                                                     *)
(*                                                                           *)
(* Control flow (offsets in the trimmed code, see below):                    *)
(*   0x2c          core entry, after the register saves                      *)
(*   0xa0          cbz x1 -> 0xaa0 (loop_count = 0); b.eq at 0xa8 -> 0x828   *)
(*                 (loop_count = 1)                                          *)
(*   0xac..0x290   fill; cbz x1 at 0x290 -> 0x514 (loop_count = 2)           *)
(*   0x294..0x510  loop body; cbnz x1 at 0x510 -> 0x294                      *)
(*   0x514..0x824  drain, ending with b 0xaa0                                *)
(*   0x828..0xa9c  iter_1, the single-group path; falls into 0xaa0           *)
(*   0xaa0         cbz x16 -> 0xb68 (loop_remain = 0)                        *)
(*   0xaa4..0xb64  single-block tail loop                                    *)
(*   0xb68..0xb78  tag and counter writeback; 0xb7c core exit                *)
(*                                                                           *)
(* The core theorem AES128_GCM_DEC_CORRECT runs from pc + 0x2c to            *)
(* pc + 0xb7c, before the restores.  It sequences at pc + 0xa0, the end of   *)
(* the preamble (round keys, key table, tag, counter registers and block     *)
(* counts), and at pc + 0xaa0, the end of the four-block loop; the tail      *)
(* loop is an ENSURES_WHILE_UP over loop_remain between pc + 0xaa4 and       *)
(* pc + 0xb64.  The four-block loop is software-pipelined two groups deep:   *)
(* at the loop head of iteration i the last two blocks of group i are        *)
(* already decrypted and stored, the AES of the first two is under way (in   *)
(* Q30 and Q5) and the GHASH of the group is partly computed; the loop       *)
(* invariant swp_inv records all of this.  Each case of                      *)
(* loop_count = nblocks DIV 4 has its own legs: loop_count = 0 is closed     *)
(* inline, loop_count = 1 by SWP_DEC_ITER1 (pc + 0xa0 -> pc + 0xaa0),        *)
(* loop_count = 2 by SWP_DEC_LC2 (the fill SWP_DEC_LC2_PARTA,                *)
(* pc + 0xa0 -> pc + 0x514, then the drain SWP_DEC_DRAIN514,                 *)
(* pc + 0x514 -> pc + 0xaa0), and loop_count >= 3 by an ENSURES_WHILE_UP     *)
(* over loop_count - 2 iterations between pc + 0x294 and pc + 0x510, with    *)
(* SWP_DEC_FILLLEG (pc + 0xa0 -> pc + 0x294), SWP_DEC_BODYLEG                *)
(* (pc + 0x294 -> pc + 0x510) and SWP_DEC_DRAINLEG                           *)
(* (pc + 0x510 -> pc + 0xaa0).  The safety theorems follow the same regions  *)
(* with the event-tracking simulator.                                        *)
(*                                                                           *)
(* The specification vocabulary (ctr_block, aes_ctr_block, nist_input_block, *)
(* htable_mem_4) is in arm/proofs/utils/aes_gcm_spec.ml; the lemmas and      *)
(* tactics shared with the other AES-GCM proofs are in                       *)
(* arm/proofs/utils/aes_gcm_common.ml.                                       *)
(*                                                                           *)
(* The code begins with a BTI landing pad (bti c).  The proofs are about the *)
(* trimmed code aes128_gcm_dec_tmc without it, which is also the code of a   *)
(* -DNO_IBT build, so all offsets above are offsets in that code; the        *)
(* subroutine theorems for the full code are derived by ARM_ADD_IBT_RULE.    *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "arm/proofs/utils/aes_gcm_common.ml";;

(* ------------------------------------------------------------------------- *)
(* The machine code.                                                         *)
(* ------------------------------------------------------------------------- *)

(* print_literal_from_elf "arm/aes_gcm/aes128_gcm_dec.o";; *)

let aes128_gcm_dec_mc =
  define_assert_from_elf "aes128_gcm_dec_mc" "arm/aes_gcm/aes128_gcm_dec.o"
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
  0x3dc00ccf;       (* arm_LDR Q15 X6 (Immediate_Offset (word 48)) *)
  0x3dc014d0;       (* arm_LDR Q16 X6 (Immediate_Offset (word 80)) *)
  0x3dc010d1;       (* arm_LDR Q17 X6 (Immediate_Offset (word 64)) *)
  0xb4005001;       (* arm_CBZ X1 (word 2560) *)
  0xf100043f;       (* arm_CMP X1 (rvalue (word 1)) *)
  0x54003c00;       (* arm_BEQ (word 1920) *)
  0x110001aa;       (* arm_ADD W10 W13 (rvalue (word 0)) *)
  0x11000dba;       (* arm_ADD W26 W13 (rvalue (word 3)) *)
  0x5ac00951;       (* arm_REV W17 W10 *)
  0xaa118195;       (* arm_ORR X21 X12 (Shiftedreg X17 LSL 32) *)
  0x110005be;       (* arm_ADD W30 W13 (rvalue (word 1)) *)
  0x5ac00bce;       (* arm_REV W14 W30 *)
  0xaa0e8198;       (* arm_ORR X24 X12 (Shiftedreg X14 LSL 32) *)
  0xa90a57eb;       (* arm_STP X11 X21 SP (Immediate_Offset (iword (&160))) *)
  0x5ac00b57;       (* arm_REV W23 W26 *)
  0xa90b63eb;       (* arm_STP X11 X24 SP (Immediate_Offset (iword (&176))) *)
  0xaa17819d;       (* arm_ORR X29 X12 (Shiftedreg X23 LSL 32) *)
  0x110009a7;       (* arm_ADD W7 W13 (rvalue (word 2)) *)
  0xa90d77eb;       (* arm_STP X11 X29 SP (Immediate_Offset (iword (&208))) *)
  0x110011ad;       (* arm_ADD W13 W13 (rvalue (word 4)) *)
  0x5ac008f9;       (* arm_REV W25 W7 *)
  0x3dc037ff;       (* arm_LDR Q31 SP (Immediate_Offset (word 208)) *)
  0xaa19819b;       (* arm_ORR X27 X12 (Shiftedreg X25 LSL 32) *)
  0x110001aa;       (* arm_ADD W10 W13 (rvalue (word 0)) *)
  0xa90c6feb;       (* arm_STP X11 X27 SP (Immediate_Offset (iword (&192))) *)
  0x11000dba;       (* arm_ADD W26 W13 (rvalue (word 3)) *)
  0x5ac00951;       (* arm_REV W17 W10 *)
  0xaa118195;       (* arm_ORR X21 X12 (Shiftedreg X17 LSL 32) *)
  0x4e284a5f;       (* arm_AESE Q31 Q18 *)
  0x4e286bff;       (* arm_AESMC Q31 Q31 *)
  0x4e284a7f;       (* arm_AESE Q31 Q19 *)
  0x4e286bff;       (* arm_AESMC Q31 Q31 *)
  0x3dc02fe5;       (* arm_LDR Q5 SP (Immediate_Offset (word 176)) *)
  0x4e284a9f;       (* arm_AESE Q31 Q20 *)
  0x4e286bff;       (* arm_AESMC Q31 Q31 *)
  0x3dc033e4;       (* arm_LDR Q4 SP (Immediate_Offset (word 192)) *)
  0x4e284abf;       (* arm_AESE Q31 Q21 *)
  0x4e286bff;       (* arm_AESMC Q31 Q31 *)
  0x110005be;       (* arm_ADD W30 W13 (rvalue (word 1)) *)
  0x4e284a45;       (* arm_AESE Q5 Q18 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x5ac00bce;       (* arm_REV W14 W30 *)
  0x4e284adf;       (* arm_AESE Q31 Q22 *)
  0x4e286bff;       (* arm_AESMC Q31 Q31 *)
  0xaa0e8198;       (* arm_ORR X24 X12 (Shiftedreg X14 LSL 32) *)
  0x3dc00c02;       (* arm_LDR Q2 X0 (Immediate_Offset (word 48)) *)
  0x4e284a44;       (* arm_AESE Q4 Q18 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284aff;       (* arm_AESE Q31 Q23 *)
  0x4e286bff;       (* arm_AESMC Q31 Q31 *)
  0x4e200840;       (* arm_REV64_VEC Q0 Q2 8 *)
  0x4e284a64;       (* arm_AESE Q4 Q19 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b1f;       (* arm_AESE Q31 Q24 *)
  0x4e286bff;       (* arm_AESMC Q31 Q31 *)
  0x4e284a84;       (* arm_AESE Q4 Q20 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b3f;       (* arm_AESE Q31 Q25 *)
  0x4e286bff;       (* arm_AESMC Q31 Q31 *)
  0x4e284aa4;       (* arm_AESE Q4 Q21 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x3cc4041d;       (* arm_LDR Q29 X0 (Postimmediate_Offset (word 64)) *)
  0x0eece00a;       (* arm_PMULL_VEC Q10 Q0 Q12 64 *)
  0x4e284ac4;       (* arm_AESE Q4 Q22 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284a65;       (* arm_AESE Q5 Q19 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284ae4;       (* arm_AESE Q4 Q23 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e200ba6;       (* arm_REV64_VEC Q6 Q29 8 *)
  0x4e284a85;       (* arm_AESE Q5 Q20 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b04;       (* arm_AESE Q4 Q24 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x3cde0008;       (* arm_LDR Q8 X0 (Immediate_Offset (word 18446744073709551584)) *)
  0x4e284aa5;       (* arm_AESE Q5 Q21 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x6e3e1ccb;       (* arm_EOR_VEC Q11 Q6 Q30 128 *)
  0x4e284b5f;       (* arm_AESE Q31 Q26 *)
  0x4e286bff;       (* arm_AESMC Q31 Q31 *)
  0x3dc02bfe;       (* arm_LDR Q30 SP (Immediate_Offset (word 160)) *)
  0x4e284ac5;       (* arm_AESE Q5 Q22 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x6e0b4166;       (* arm_EXT Q6 Q11 Q11 64 *)
  0xa90a57eb;       (* arm_STP X11 X21 SP (Immediate_Offset (iword (&160))) *)
  0x4e284b7f;       (* arm_AESE Q31 Q27 *)
  0x4e284ae5;       (* arm_AESE Q5 Q23 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x6e2b1cc6;       (* arm_EOR_VEC Q6 Q6 Q11 128 *)
  0x4e284b24;       (* arm_AESE Q4 Q25 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x6e3c1fe9;       (* arm_EOR_VEC Q9 Q31 Q28 128 *)
  0x4e200901;       (* arm_REV64_VEC Q1 Q8 8 *)
  0x4e284b05;       (* arm_AESE Q5 Q24 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x6e221d23;       (* arm_EOR_VEC Q3 Q9 Q2 128 *)
  0x4e284b44;       (* arm_AESE Q4 Q26 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x6e014029;       (* arm_EXT Q9 Q1 Q1 64 *)
  0x4e284b25;       (* arm_AESE Q5 Q25 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x3d800c43;       (* arm_STR Q3 X2 (Immediate_Offset (word 48)) *)
  0x4eede023;       (* arm_PMULL2_VEC Q3 Q1 Q13 64 *)
  0x6e211d29;       (* arm_EOR_VEC Q9 Q9 Q1 128 *)
  0x0eede03f;       (* arm_PMULL_VEC Q31 Q1 Q13 64 *)
  0x5e180402;       (* arm_DUP_ELEM_SCALAR Q2 Q0 1 64 *)
  0x4e284b45;       (* arm_AESE Q5 Q26 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x6e3f1d5f;       (* arm_EOR_VEC Q31 Q10 Q31 128 *)
  0x4e284b64;       (* arm_AESE Q4 Q27 *)
  0x3cdd000a;       (* arm_LDR Q10 X0 (Immediate_Offset (word 18446744073709551568)) *)
  0x4e284b65;       (* arm_AESE Q5 Q27 *)
  0x6e3c1c84;       (* arm_EOR_VEC Q4 Q4 Q28 128 *)
  0x4e284a5e;       (* arm_AESE Q30 Q18 *)
  0x4e286bde;       (* arm_AESMC Q30 Q30 *)
  0x4eece001;       (* arm_PMULL2_VEC Q1 Q0 Q12 64 *)
  0x2e201c42;       (* arm_EOR_VEC Q2 Q2 Q0 64 *)
  0x6e281c88;       (* arm_EOR_VEC Q8 Q4 Q8 128 *)
  0x4e284a7e;       (* arm_AESE Q30 Q19 *)
  0x4e286bde;       (* arm_AESMC Q30 Q30 *)
  0x4eeee124;       (* arm_PMULL2_VEC Q4 Q9 Q14 64 *)
  0x4e200940;       (* arm_REV64_VEC Q0 Q10 8 *)
  0x3d800848;       (* arm_STR Q8 X2 (Immediate_Offset (word 32)) *)
  0x4ef0e168;       (* arm_PMULL2_VEC Q8 Q11 Q16 64 *)
  0x6e231c29;       (* arm_EOR_VEC Q9 Q1 Q3 128 *)
  0x4eefe003;       (* arm_PMULL2_VEC Q3 Q0 Q15 64 *)
  0xd1000821;       (* arm_SUB X1 X1 (rvalue (word 2)) *)
  0xb4001421;       (* arm_CBZ X1 (word 644) *)
  0x6e3c1ca5;       (* arm_EOR_VEC Q5 Q5 Q28 128 *)
  0x4e284a9e;       (* arm_AESE Q30 Q20 *)
  0x4e286bde;       (* arm_AESMC Q30 Q30 *)
  0x5ac00b57;       (* arm_REV W23 W26 *)
  0xa90b63eb;       (* arm_STP X11 X24 SP (Immediate_Offset (iword (&176))) *)
  0x6e231d23;       (* arm_EOR_VEC Q3 Q9 Q3 128 *)
  0x0eefe009;       (* arm_PMULL_VEC Q9 Q0 Q15 64 *)
  0xaa17819d;       (* arm_ORR X29 X12 (Shiftedreg X23 LSL 32) *)
  0x110009a7;       (* arm_ADD W7 W13 (rvalue (word 2)) *)
  0x6e2a1ca5;       (* arm_EOR_VEC Q5 Q5 Q10 128 *)
  0x4e284abe;       (* arm_AESE Q30 Q21 *)
  0x4e286bde;       (* arm_AESMC Q30 Q30 *)
  0xa90d77eb;       (* arm_STP X11 X29 SP (Immediate_Offset (iword (&208))) *)
  0x110011ad;       (* arm_ADD W13 W13 (rvalue (word 4)) *)
  0x0ef0e16a;       (* arm_PMULL_VEC Q10 Q11 Q16 64 *)
  0x6e291feb;       (* arm_EOR_VEC Q11 Q31 Q9 128 *)
  0x5ac008f9;       (* arm_REV W25 W7 *)
  0x3dc037ff;       (* arm_LDR Q31 SP (Immediate_Offset (word 208)) *)
  0x4e284ade;       (* arm_AESE Q30 Q22 *)
  0x4e286bde;       (* arm_AESMC Q30 Q30 *)
  0xaa19819b;       (* arm_ORR X27 X12 (Shiftedreg X25 LSL 32) *)
  0x4ef1e0c9;       (* arm_PMULL2_VEC Q9 Q6 Q17 64 *)
  0x5e180406;       (* arm_DUP_ELEM_SCALAR Q6 Q0 1 64 *)
  0x110001aa;       (* arm_ADD W10 W13 (rvalue (word 0)) *)
  0xa90c6feb;       (* arm_STP X11 X27 SP (Immediate_Offset (iword (&192))) *)
  0x6e2a1d6a;       (* arm_EOR_VEC Q10 Q11 Q10 128 *)
  0x4e284afe;       (* arm_AESE Q30 Q23 *)
  0x4e286bde;       (* arm_AESMC Q30 Q30 *)
  0x11000dba;       (* arm_ADD W26 W13 (rvalue (word 3)) *)
  0x0eeee041;       (* arm_PMULL_VEC Q1 Q2 Q14 64 *)
  0x2e201cc6;       (* arm_EOR_VEC Q6 Q6 Q0 64 *)
  0x5ac00951;       (* arm_REV W17 W10 *)
  0x6e281c63;       (* arm_EOR_VEC Q3 Q3 Q8 128 *)
  0x4e284b1e;       (* arm_AESE Q30 Q24 *)
  0x4e286bde;       (* arm_AESMC Q30 Q30 *)
  0xaa118195;       (* arm_ORR X21 X12 (Shiftedreg X17 LSL 32) *)
  0x0ef1e0c0;       (* arm_PMULL_VEC Q0 Q6 Q17 64 *)
  0x6e241c2b;       (* arm_EOR_VEC Q11 Q1 Q4 128 *)
  0x4e284a5f;       (* arm_AESE Q31 Q18 *)
  0x4e286bff;       (* arm_AESMC Q31 Q31 *)
  0x6e034066;       (* arm_EXT Q6 Q3 Q3 64 *)
  0x0ee7e068;       (* arm_PMULL_VEC Q8 Q3 Q7 64 *)
  0x6e231d43;       (* arm_EOR_VEC Q3 Q10 Q3 128 *)
  0x3d800445;       (* arm_STR Q5 X2 (Immediate_Offset (word 16)) *)
  0x4e284a7f;       (* arm_AESE Q31 Q19 *)
  0x4e286bff;       (* arm_AESMC Q31 Q31 *)
  0x3dc02fe5;       (* arm_LDR Q5 SP (Immediate_Offset (word 176)) *)
  0x4e284b3e;       (* arm_AESE Q30 Q25 *)
  0x4e286bde;       (* arm_AESMC Q30 Q30 *)
  0x4e284a9f;       (* arm_AESE Q31 Q20 *)
  0x4e286bff;       (* arm_AESMC Q31 Q31 *)
  0x6e201d60;       (* arm_EOR_VEC Q0 Q11 Q0 128 *)
  0x3dc033e4;       (* arm_LDR Q4 SP (Immediate_Offset (word 192)) *)
  0x4e284b5e;       (* arm_AESE Q30 Q26 *)
  0x4e286bde;       (* arm_AESMC Q30 Q30 *)
  0x4e284abf;       (* arm_AESE Q31 Q21 *)
  0x4e286bff;       (* arm_AESMC Q31 Q31 *)
  0x6e291c09;       (* arm_EOR_VEC Q9 Q0 Q9 128 *)
  0x110005be;       (* arm_ADD W30 W13 (rvalue (word 1)) *)
  0x4e284a45;       (* arm_AESE Q5 Q18 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x6e281cc6;       (* arm_EOR_VEC Q6 Q6 Q8 128 *)
  0x5ac00bce;       (* arm_REV W14 W30 *)
  0x4e284adf;       (* arm_AESE Q31 Q22 *)
  0x4e286bff;       (* arm_AESMC Q31 Q31 *)
  0x6e231d28;       (* arm_EOR_VEC Q8 Q9 Q3 128 *)
  0xaa0e8198;       (* arm_ORR X24 X12 (Shiftedreg X14 LSL 32) *)
  0x3dc00c02;       (* arm_LDR Q2 X0 (Immediate_Offset (word 48)) *)
  0x4e284a44;       (* arm_AESE Q4 Q18 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284aff;       (* arm_AESE Q31 Q23 *)
  0x4e286bff;       (* arm_AESMC Q31 Q31 *)
  0x6e261d06;       (* arm_EOR_VEC Q6 Q8 Q6 128 *)
  0x4e284b7e;       (* arm_AESE Q30 Q27 *)
  0x0ee7e0c1;       (* arm_PMULL_VEC Q1 Q6 Q7 64 *)
  0x6e0640c9;       (* arm_EXT Q9 Q6 Q6 64 *)
  0x4e200840;       (* arm_REV64_VEC Q0 Q2 8 *)
  0x4e284a64;       (* arm_AESE Q4 Q19 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b1f;       (* arm_AESE Q31 Q24 *)
  0x4e286bff;       (* arm_AESMC Q31 Q31 *)
  0x6e3c1fc8;       (* arm_EOR_VEC Q8 Q30 Q28 128 *)
  0x4e284a84;       (* arm_AESE Q4 Q20 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x6e211d46;       (* arm_EOR_VEC Q6 Q10 Q1 128 *)
  0x4e284b3f;       (* arm_AESE Q31 Q25 *)
  0x4e286bff;       (* arm_AESMC Q31 Q31 *)
  0x6e3d1d08;       (* arm_EOR_VEC Q8 Q8 Q29 128 *)
  0x4e284aa4;       (* arm_AESE Q4 Q21 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x3cc4041d;       (* arm_LDR Q29 X0 (Postimmediate_Offset (word 64)) *)
  0x0eece00a;       (* arm_PMULL_VEC Q10 Q0 Q12 64 *)
  0x3c840448;       (* arm_STR Q8 X2 (Postimmediate_Offset (word 64)) *)
  0x4e284ac4;       (* arm_AESE Q4 Q22 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x6e291cde;       (* arm_EOR_VEC Q30 Q6 Q9 128 *)
  0x4e284a65;       (* arm_AESE Q5 Q19 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284ae4;       (* arm_AESE Q4 Q23 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e200ba6;       (* arm_REV64_VEC Q6 Q29 8 *)
  0x4e284a85;       (* arm_AESE Q5 Q20 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x6e1e43de;       (* arm_EXT Q30 Q30 Q30 64 *)
  0x4e284b04;       (* arm_AESE Q4 Q24 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x3cde0008;       (* arm_LDR Q8 X0 (Immediate_Offset (word 18446744073709551584)) *)
  0x4e284aa5;       (* arm_AESE Q5 Q21 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x6e3e1ccb;       (* arm_EOR_VEC Q11 Q6 Q30 128 *)
  0x4e284b5f;       (* arm_AESE Q31 Q26 *)
  0x4e286bff;       (* arm_AESMC Q31 Q31 *)
  0x3dc02bfe;       (* arm_LDR Q30 SP (Immediate_Offset (word 160)) *)
  0x4e284ac5;       (* arm_AESE Q5 Q22 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x6e0b4166;       (* arm_EXT Q6 Q11 Q11 64 *)
  0xa90a57eb;       (* arm_STP X11 X21 SP (Immediate_Offset (iword (&160))) *)
  0x4e284b7f;       (* arm_AESE Q31 Q27 *)
  0x4e284ae5;       (* arm_AESE Q5 Q23 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x6e2b1cc6;       (* arm_EOR_VEC Q6 Q6 Q11 128 *)
  0x4e284b24;       (* arm_AESE Q4 Q25 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x6e3c1fe9;       (* arm_EOR_VEC Q9 Q31 Q28 128 *)
  0x4e200901;       (* arm_REV64_VEC Q1 Q8 8 *)
  0x4e284b05;       (* arm_AESE Q5 Q24 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x6e221d23;       (* arm_EOR_VEC Q3 Q9 Q2 128 *)
  0x4e284b44;       (* arm_AESE Q4 Q26 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x6e014029;       (* arm_EXT Q9 Q1 Q1 64 *)
  0x4e284b25;       (* arm_AESE Q5 Q25 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x3d800c43;       (* arm_STR Q3 X2 (Immediate_Offset (word 48)) *)
  0x4eede023;       (* arm_PMULL2_VEC Q3 Q1 Q13 64 *)
  0x6e211d29;       (* arm_EOR_VEC Q9 Q9 Q1 128 *)
  0x0eede03f;       (* arm_PMULL_VEC Q31 Q1 Q13 64 *)
  0x5e180402;       (* arm_DUP_ELEM_SCALAR Q2 Q0 1 64 *)
  0x4e284b45;       (* arm_AESE Q5 Q26 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x6e3f1d5f;       (* arm_EOR_VEC Q31 Q10 Q31 128 *)
  0x4e284b64;       (* arm_AESE Q4 Q27 *)
  0x3cdd000a;       (* arm_LDR Q10 X0 (Immediate_Offset (word 18446744073709551568)) *)
  0x4e284b65;       (* arm_AESE Q5 Q27 *)
  0x6e3c1c84;       (* arm_EOR_VEC Q4 Q4 Q28 128 *)
  0x4e284a5e;       (* arm_AESE Q30 Q18 *)
  0x4e286bde;       (* arm_AESMC Q30 Q30 *)
  0x4eece001;       (* arm_PMULL2_VEC Q1 Q0 Q12 64 *)
  0x2e201c42;       (* arm_EOR_VEC Q2 Q2 Q0 64 *)
  0x6e281c88;       (* arm_EOR_VEC Q8 Q4 Q8 128 *)
  0x4e284a7e;       (* arm_AESE Q30 Q19 *)
  0x4e286bde;       (* arm_AESMC Q30 Q30 *)
  0x4eeee124;       (* arm_PMULL2_VEC Q4 Q9 Q14 64 *)
  0x4e200940;       (* arm_REV64_VEC Q0 Q10 8 *)
  0x3d800848;       (* arm_STR Q8 X2 (Immediate_Offset (word 32)) *)
  0x4ef0e168;       (* arm_PMULL2_VEC Q8 Q11 Q16 64 *)
  0x6e231c29;       (* arm_EOR_VEC Q9 Q1 Q3 128 *)
  0x4eefe003;       (* arm_PMULL2_VEC Q3 Q0 Q15 64 *)
  0xd1000421;       (* arm_SUB X1 X1 (rvalue (word 1)) *)
  0xb5ffec21;       (* arm_CBNZ X1 (word 2096516) *)
  0x6e3c1ca5;       (* arm_EOR_VEC Q5 Q5 Q28 128 *)
  0x4e284a9e;       (* arm_AESE Q30 Q20 *)
  0x4e286bde;       (* arm_AESMC Q30 Q30 *)
  0x5ac00b57;       (* arm_REV W23 W26 *)
  0xa90b63eb;       (* arm_STP X11 X24 SP (Immediate_Offset (iword (&176))) *)
  0x6e231d23;       (* arm_EOR_VEC Q3 Q9 Q3 128 *)
  0x0eefe009;       (* arm_PMULL_VEC Q9 Q0 Q15 64 *)
  0xaa17819d;       (* arm_ORR X29 X12 (Shiftedreg X23 LSL 32) *)
  0x110009a7;       (* arm_ADD W7 W13 (rvalue (word 2)) *)
  0x6e2a1ca5;       (* arm_EOR_VEC Q5 Q5 Q10 128 *)
  0x4e284abe;       (* arm_AESE Q30 Q21 *)
  0x4e286bde;       (* arm_AESMC Q30 Q30 *)
  0xa90d77eb;       (* arm_STP X11 X29 SP (Immediate_Offset (iword (&208))) *)
  0x110011ad;       (* arm_ADD W13 W13 (rvalue (word 4)) *)
  0x0ef0e16a;       (* arm_PMULL_VEC Q10 Q11 Q16 64 *)
  0x6e291feb;       (* arm_EOR_VEC Q11 Q31 Q9 128 *)
  0x5ac008f9;       (* arm_REV W25 W7 *)
  0x3dc037ff;       (* arm_LDR Q31 SP (Immediate_Offset (word 208)) *)
  0x4e284ade;       (* arm_AESE Q30 Q22 *)
  0x4e286bde;       (* arm_AESMC Q30 Q30 *)
  0xaa19819b;       (* arm_ORR X27 X12 (Shiftedreg X25 LSL 32) *)
  0x4ef1e0c9;       (* arm_PMULL2_VEC Q9 Q6 Q17 64 *)
  0x5e180406;       (* arm_DUP_ELEM_SCALAR Q6 Q0 1 64 *)
  0xa90c6feb;       (* arm_STP X11 X27 SP (Immediate_Offset (iword (&192))) *)
  0x6e2a1d6a;       (* arm_EOR_VEC Q10 Q11 Q10 128 *)
  0x4e284afe;       (* arm_AESE Q30 Q23 *)
  0x4e286bde;       (* arm_AESMC Q30 Q30 *)
  0x0eeee041;       (* arm_PMULL_VEC Q1 Q2 Q14 64 *)
  0x2e201cc6;       (* arm_EOR_VEC Q6 Q6 Q0 64 *)
  0x6e281c63;       (* arm_EOR_VEC Q3 Q3 Q8 128 *)
  0x4e284b1e;       (* arm_AESE Q30 Q24 *)
  0x4e286bde;       (* arm_AESMC Q30 Q30 *)
  0x0ef1e0c0;       (* arm_PMULL_VEC Q0 Q6 Q17 64 *)
  0x6e241c2b;       (* arm_EOR_VEC Q11 Q1 Q4 128 *)
  0x4e284a5f;       (* arm_AESE Q31 Q18 *)
  0x4e286bff;       (* arm_AESMC Q31 Q31 *)
  0x6e034066;       (* arm_EXT Q6 Q3 Q3 64 *)
  0x0ee7e068;       (* arm_PMULL_VEC Q8 Q3 Q7 64 *)
  0x6e231d43;       (* arm_EOR_VEC Q3 Q10 Q3 128 *)
  0x3d800445;       (* arm_STR Q5 X2 (Immediate_Offset (word 16)) *)
  0x4e284a7f;       (* arm_AESE Q31 Q19 *)
  0x4e286bff;       (* arm_AESMC Q31 Q31 *)
  0x3dc02fe5;       (* arm_LDR Q5 SP (Immediate_Offset (word 176)) *)
  0x4e284b3e;       (* arm_AESE Q30 Q25 *)
  0x4e286bde;       (* arm_AESMC Q30 Q30 *)
  0x4e284a9f;       (* arm_AESE Q31 Q20 *)
  0x4e286bff;       (* arm_AESMC Q31 Q31 *)
  0x6e201d60;       (* arm_EOR_VEC Q0 Q11 Q0 128 *)
  0x3dc033e4;       (* arm_LDR Q4 SP (Immediate_Offset (word 192)) *)
  0x4e284b5e;       (* arm_AESE Q30 Q26 *)
  0x4e286bde;       (* arm_AESMC Q30 Q30 *)
  0x4e284abf;       (* arm_AESE Q31 Q21 *)
  0x4e286bff;       (* arm_AESMC Q31 Q31 *)
  0x6e291c09;       (* arm_EOR_VEC Q9 Q0 Q9 128 *)
  0x4e284a45;       (* arm_AESE Q5 Q18 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x6e281cc6;       (* arm_EOR_VEC Q6 Q6 Q8 128 *)
  0x4e284adf;       (* arm_AESE Q31 Q22 *)
  0x4e286bff;       (* arm_AESMC Q31 Q31 *)
  0x6e231d28;       (* arm_EOR_VEC Q8 Q9 Q3 128 *)
  0x3dc00c02;       (* arm_LDR Q2 X0 (Immediate_Offset (word 48)) *)
  0x4e284a44;       (* arm_AESE Q4 Q18 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284aff;       (* arm_AESE Q31 Q23 *)
  0x4e286bff;       (* arm_AESMC Q31 Q31 *)
  0x6e261d06;       (* arm_EOR_VEC Q6 Q8 Q6 128 *)
  0x4e284b7e;       (* arm_AESE Q30 Q27 *)
  0x0ee7e0c1;       (* arm_PMULL_VEC Q1 Q6 Q7 64 *)
  0x6e0640c9;       (* arm_EXT Q9 Q6 Q6 64 *)
  0x4e200840;       (* arm_REV64_VEC Q0 Q2 8 *)
  0x4e284a64;       (* arm_AESE Q4 Q19 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b1f;       (* arm_AESE Q31 Q24 *)
  0x4e286bff;       (* arm_AESMC Q31 Q31 *)
  0x6e3c1fc8;       (* arm_EOR_VEC Q8 Q30 Q28 128 *)
  0x4e284a84;       (* arm_AESE Q4 Q20 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x6e211d46;       (* arm_EOR_VEC Q6 Q10 Q1 128 *)
  0x4e284b3f;       (* arm_AESE Q31 Q25 *)
  0x4e286bff;       (* arm_AESMC Q31 Q31 *)
  0x6e3d1d08;       (* arm_EOR_VEC Q8 Q8 Q29 128 *)
  0x4e284aa4;       (* arm_AESE Q4 Q21 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x3cc4041d;       (* arm_LDR Q29 X0 (Postimmediate_Offset (word 64)) *)
  0x0eece00a;       (* arm_PMULL_VEC Q10 Q0 Q12 64 *)
  0x3c840448;       (* arm_STR Q8 X2 (Postimmediate_Offset (word 64)) *)
  0x4e284ac4;       (* arm_AESE Q4 Q22 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x6e291cde;       (* arm_EOR_VEC Q30 Q6 Q9 128 *)
  0x4e284a65;       (* arm_AESE Q5 Q19 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284ae4;       (* arm_AESE Q4 Q23 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e200ba6;       (* arm_REV64_VEC Q6 Q29 8 *)
  0x4e284a85;       (* arm_AESE Q5 Q20 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x6e1e43de;       (* arm_EXT Q30 Q30 Q30 64 *)
  0x4e284b04;       (* arm_AESE Q4 Q24 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x3cde0008;       (* arm_LDR Q8 X0 (Immediate_Offset (word 18446744073709551584)) *)
  0x4e284aa5;       (* arm_AESE Q5 Q21 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x6e3e1ccb;       (* arm_EOR_VEC Q11 Q6 Q30 128 *)
  0x4e284b5f;       (* arm_AESE Q31 Q26 *)
  0x4e286bff;       (* arm_AESMC Q31 Q31 *)
  0x3dc02bfe;       (* arm_LDR Q30 SP (Immediate_Offset (word 160)) *)
  0x4e284ac5;       (* arm_AESE Q5 Q22 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x6e0b4166;       (* arm_EXT Q6 Q11 Q11 64 *)
  0x4e284b7f;       (* arm_AESE Q31 Q27 *)
  0x4e284ae5;       (* arm_AESE Q5 Q23 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x6e2b1cc6;       (* arm_EOR_VEC Q6 Q6 Q11 128 *)
  0x4e284b24;       (* arm_AESE Q4 Q25 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x6e3c1fe9;       (* arm_EOR_VEC Q9 Q31 Q28 128 *)
  0x4e200901;       (* arm_REV64_VEC Q1 Q8 8 *)
  0x4e284b05;       (* arm_AESE Q5 Q24 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x6e221d23;       (* arm_EOR_VEC Q3 Q9 Q2 128 *)
  0x4e284b44;       (* arm_AESE Q4 Q26 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x6e014029;       (* arm_EXT Q9 Q1 Q1 64 *)
  0x4e284b25;       (* arm_AESE Q5 Q25 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x3d800c43;       (* arm_STR Q3 X2 (Immediate_Offset (word 48)) *)
  0x4eede023;       (* arm_PMULL2_VEC Q3 Q1 Q13 64 *)
  0x6e211d29;       (* arm_EOR_VEC Q9 Q9 Q1 128 *)
  0x0eede03f;       (* arm_PMULL_VEC Q31 Q1 Q13 64 *)
  0x5e180402;       (* arm_DUP_ELEM_SCALAR Q2 Q0 1 64 *)
  0x4e284b45;       (* arm_AESE Q5 Q26 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x6e3f1d5f;       (* arm_EOR_VEC Q31 Q10 Q31 128 *)
  0x4e284b64;       (* arm_AESE Q4 Q27 *)
  0x3cdd000a;       (* arm_LDR Q10 X0 (Immediate_Offset (word 18446744073709551568)) *)
  0x4e284b65;       (* arm_AESE Q5 Q27 *)
  0x6e3c1c84;       (* arm_EOR_VEC Q4 Q4 Q28 128 *)
  0x4e284a5e;       (* arm_AESE Q30 Q18 *)
  0x4e286bde;       (* arm_AESMC Q30 Q30 *)
  0x4eece001;       (* arm_PMULL2_VEC Q1 Q0 Q12 64 *)
  0x2e201c42;       (* arm_EOR_VEC Q2 Q2 Q0 64 *)
  0x6e281c88;       (* arm_EOR_VEC Q8 Q4 Q8 128 *)
  0x4e284a7e;       (* arm_AESE Q30 Q19 *)
  0x4e286bde;       (* arm_AESMC Q30 Q30 *)
  0x4eeee124;       (* arm_PMULL2_VEC Q4 Q9 Q14 64 *)
  0x4e200940;       (* arm_REV64_VEC Q0 Q10 8 *)
  0x3d800848;       (* arm_STR Q8 X2 (Immediate_Offset (word 32)) *)
  0x4ef0e168;       (* arm_PMULL2_VEC Q8 Q11 Q16 64 *)
  0x6e231c29;       (* arm_EOR_VEC Q9 Q1 Q3 128 *)
  0x4eefe003;       (* arm_PMULL2_VEC Q3 Q0 Q15 64 *)
  0x6e3c1ca5;       (* arm_EOR_VEC Q5 Q5 Q28 128 *)
  0x4e284a9e;       (* arm_AESE Q30 Q20 *)
  0x4e286bde;       (* arm_AESMC Q30 Q30 *)
  0x6e231d23;       (* arm_EOR_VEC Q3 Q9 Q3 128 *)
  0x0eefe009;       (* arm_PMULL_VEC Q9 Q0 Q15 64 *)
  0x6e2a1ca5;       (* arm_EOR_VEC Q5 Q5 Q10 128 *)
  0x4e284abe;       (* arm_AESE Q30 Q21 *)
  0x4e286bde;       (* arm_AESMC Q30 Q30 *)
  0x0ef0e16a;       (* arm_PMULL_VEC Q10 Q11 Q16 64 *)
  0x6e291feb;       (* arm_EOR_VEC Q11 Q31 Q9 128 *)
  0x4e284ade;       (* arm_AESE Q30 Q22 *)
  0x4e286bde;       (* arm_AESMC Q30 Q30 *)
  0x4ef1e0c9;       (* arm_PMULL2_VEC Q9 Q6 Q17 64 *)
  0x5e180406;       (* arm_DUP_ELEM_SCALAR Q6 Q0 1 64 *)
  0x6e2a1d6a;       (* arm_EOR_VEC Q10 Q11 Q10 128 *)
  0x4e284afe;       (* arm_AESE Q30 Q23 *)
  0x4e286bde;       (* arm_AESMC Q30 Q30 *)
  0x0eeee041;       (* arm_PMULL_VEC Q1 Q2 Q14 64 *)
  0x2e201cc6;       (* arm_EOR_VEC Q6 Q6 Q0 64 *)
  0x6e281c63;       (* arm_EOR_VEC Q3 Q3 Q8 128 *)
  0x4e284b1e;       (* arm_AESE Q30 Q24 *)
  0x4e286bde;       (* arm_AESMC Q30 Q30 *)
  0x0ef1e0c0;       (* arm_PMULL_VEC Q0 Q6 Q17 64 *)
  0x6e241c2b;       (* arm_EOR_VEC Q11 Q1 Q4 128 *)
  0x6e034066;       (* arm_EXT Q6 Q3 Q3 64 *)
  0x0ee7e068;       (* arm_PMULL_VEC Q8 Q3 Q7 64 *)
  0x6e231d43;       (* arm_EOR_VEC Q3 Q10 Q3 128 *)
  0x3d800445;       (* arm_STR Q5 X2 (Immediate_Offset (word 16)) *)
  0x4e284b3e;       (* arm_AESE Q30 Q25 *)
  0x4e286bde;       (* arm_AESMC Q30 Q30 *)
  0x6e201d60;       (* arm_EOR_VEC Q0 Q11 Q0 128 *)
  0x4e284b5e;       (* arm_AESE Q30 Q26 *)
  0x4e286bde;       (* arm_AESMC Q30 Q30 *)
  0x6e291c09;       (* arm_EOR_VEC Q9 Q0 Q9 128 *)
  0x6e281cc6;       (* arm_EOR_VEC Q6 Q6 Q8 128 *)
  0x6e231d28;       (* arm_EOR_VEC Q8 Q9 Q3 128 *)
  0x6e261d06;       (* arm_EOR_VEC Q6 Q8 Q6 128 *)
  0x4e284b7e;       (* arm_AESE Q30 Q27 *)
  0x0ee7e0c1;       (* arm_PMULL_VEC Q1 Q6 Q7 64 *)
  0x6e0640c9;       (* arm_EXT Q9 Q6 Q6 64 *)
  0x6e3c1fc8;       (* arm_EOR_VEC Q8 Q30 Q28 128 *)
  0x6e211d46;       (* arm_EOR_VEC Q6 Q10 Q1 128 *)
  0x6e3d1d08;       (* arm_EOR_VEC Q8 Q8 Q29 128 *)
  0x3c840448;       (* arm_STR Q8 X2 (Postimmediate_Offset (word 64)) *)
  0x6e291cde;       (* arm_EOR_VEC Q30 Q6 Q9 128 *)
  0x6e1e43de;       (* arm_EXT Q30 Q30 Q30 64 *)
  0x1400009f;       (* arm_B (word 636) *)
  0x3dc0040a;       (* arm_LDR Q10 X0 (Immediate_Offset (word 16)) *)
  0x110005be;       (* arm_ADD W30 W13 (rvalue (word 1)) *)
  0x110001b7;       (* arm_ADD W23 W13 (rvalue (word 0)) *)
  0x11000dba;       (* arm_ADD W26 W13 (rvalue (word 3)) *)
  0x3dc00c04;       (* arm_LDR Q4 X0 (Immediate_Offset (word 48)) *)
  0x110009b5;       (* arm_ADD W21 W13 (rvalue (word 2)) *)
  0x110011ad;       (* arm_ADD W13 W13 (rvalue (word 4)) *)
  0x5ac00b58;       (* arm_REV W24 W26 *)
  0x3dc00802;       (* arm_LDR Q2 X0 (Immediate_Offset (word 32)) *)
  0xaa188187;       (* arm_ORR X7 X12 (Shiftedreg X24 LSL 32) *)
  0x5ac00aaa;       (* arm_REV W10 W21 *)
  0x5ac00bce;       (* arm_REV W14 W30 *)
  0xa90d1feb;       (* arm_STP X11 X7 SP (Immediate_Offset (iword (&208))) *)
  0xaa0a8191;       (* arm_ORR X17 X12 (Shiftedreg X10 LSL 32) *)
  0xaa0e819d;       (* arm_ORR X29 X12 (Shiftedreg X14 LSL 32) *)
  0x4e200948;       (* arm_REV64_VEC Q8 Q10 8 *)
  0x5ac00af9;       (* arm_REV W25 W23 *)
  0x4e20088b;       (* arm_REV64_VEC Q11 Q4 8 *)
  0x3dc037e5;       (* arm_LDR Q5 SP (Immediate_Offset (word 208)) *)
  0xa90b77eb;       (* arm_STP X11 X29 SP (Immediate_Offset (iword (&176))) *)
  0xaa19819b;       (* arm_ORR X27 X12 (Shiftedreg X25 LSL 32) *)
  0x4eefe103;       (* arm_PMULL2_VEC Q3 Q8 Q15 64 *)
  0x4e200840;       (* arm_REV64_VEC Q0 Q2 8 *)
  0xa90a6feb;       (* arm_STP X11 X27 SP (Immediate_Offset (iword (&160))) *)
  0x5e18057d;       (* arm_DUP_ELEM_SCALAR Q29 Q11 1 64 *)
  0x4eece169;       (* arm_PMULL2_VEC Q9 Q11 Q12 64 *)
  0x6e004001;       (* arm_EXT Q1 Q0 Q0 64 *)
  0x4eede01f;       (* arm_PMULL2_VEC Q31 Q0 Q13 64 *)
  0xa90c47eb;       (* arm_STP X11 X17 SP (Immediate_Offset (iword (&192))) *)
  0x4e284a45;       (* arm_AESE Q5 Q18 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x2e2b1fbd;       (* arm_EOR_VEC Q29 Q29 Q11 64 *)
  0x6e3f1d29;       (* arm_EOR_VEC Q9 Q9 Q31 128 *)
  0x0eece16b;       (* arm_PMULL_VEC Q11 Q11 Q12 64 *)
  0x4e284a65;       (* arm_AESE Q5 Q19 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x3dc02bff;       (* arm_LDR Q31 SP (Immediate_Offset (word 160)) *)
  0x0eeee3a6;       (* arm_PMULL_VEC Q6 Q29 Q14 64 *)
  0x6e201c3d;       (* arm_EOR_VEC Q29 Q1 Q0 128 *)
  0x6e231d23;       (* arm_EOR_VEC Q3 Q9 Q3 128 *)
  0x4e284a85;       (* arm_AESE Q5 Q20 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4eeee3a9;       (* arm_PMULL2_VEC Q9 Q29 Q14 64 *)
  0x4e284aa5;       (* arm_AESE Q5 Q21 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x6e291cc1;       (* arm_EOR_VEC Q1 Q6 Q9 128 *)
  0x4e284a5f;       (* arm_AESE Q31 Q18 *)
  0x4e286bff;       (* arm_AESMC Q31 Q31 *)
  0x4e284ac5;       (* arm_AESE Q5 Q22 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x5e180509;       (* arm_DUP_ELEM_SCALAR Q9 Q8 1 64 *)
  0x4e284a7f;       (* arm_AESE Q31 Q19 *)
  0x4e286bff;       (* arm_AESMC Q31 Q31 *)
  0x4e284ae5;       (* arm_AESE Q5 Q23 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x2e281d26;       (* arm_EOR_VEC Q6 Q9 Q8 64 *)
  0x4e284a9f;       (* arm_AESE Q31 Q20 *)
  0x4e286bff;       (* arm_AESMC Q31 Q31 *)
  0x4e284b05;       (* arm_AESE Q5 Q24 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284abf;       (* arm_AESE Q31 Q21 *)
  0x4e286bff;       (* arm_AESMC Q31 Q31 *)
  0x4e284b25;       (* arm_AESE Q5 Q25 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284adf;       (* arm_AESE Q31 Q22 *)
  0x4e286bff;       (* arm_AESMC Q31 Q31 *)
  0x4e284b45;       (* arm_AESE Q5 Q26 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284aff;       (* arm_AESE Q31 Q23 *)
  0x4e286bff;       (* arm_AESMC Q31 Q31 *)
  0x4e284b65;       (* arm_AESE Q5 Q27 *)
  0x4e284b1f;       (* arm_AESE Q31 Q24 *)
  0x4e286bff;       (* arm_AESMC Q31 Q31 *)
  0x0eefe11d;       (* arm_PMULL_VEC Q29 Q8 Q15 64 *)
  0x6e3c1ca8;       (* arm_EOR_VEC Q8 Q5 Q28 128 *)
  0x4e284b3f;       (* arm_AESE Q31 Q25 *)
  0x4e286bff;       (* arm_AESMC Q31 Q31 *)
  0x3dc033e5;       (* arm_LDR Q5 SP (Immediate_Offset (word 192)) *)
  0x0ef1e0c9;       (* arm_PMULL_VEC Q9 Q6 Q17 64 *)
  0x6e241d06;       (* arm_EOR_VEC Q6 Q8 Q4 128 *)
  0x4e284b5f;       (* arm_AESE Q31 Q26 *)
  0x4e286bff;       (* arm_AESMC Q31 Q31 *)
  0x3dc02fe4;       (* arm_LDR Q4 SP (Immediate_Offset (word 176)) *)
  0x3d800c46;       (* arm_STR Q6 X2 (Immediate_Offset (word 48)) *)
  0x0eede008;       (* arm_PMULL_VEC Q8 Q0 Q13 64 *)
  0x3cc40406;       (* arm_LDR Q6 X0 (Postimmediate_Offset (word 64)) *)
  0x4e284b7f;       (* arm_AESE Q31 Q27 *)
  0x4e284a45;       (* arm_AESE Q5 Q18 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x6e281d60;       (* arm_EOR_VEC Q0 Q11 Q8 128 *)
  0x4e284a44;       (* arm_AESE Q4 Q18 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x6e3c1fff;       (* arm_EOR_VEC Q31 Q31 Q28 128 *)
  0x4e284a65;       (* arm_AESE Q5 Q19 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x6e261fff;       (* arm_EOR_VEC Q31 Q31 Q6 128 *)
  0x4e284a64;       (* arm_AESE Q4 Q19 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284a85;       (* arm_AESE Q5 Q20 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e2008c6;       (* arm_REV64_VEC Q6 Q6 8 *)
  0x3c84045f;       (* arm_STR Q31 X2 (Postimmediate_Offset (word 64)) *)
  0x4e284a84;       (* arm_AESE Q4 Q20 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284aa5;       (* arm_AESE Q5 Q21 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x6e3e1ccb;       (* arm_EOR_VEC Q11 Q6 Q30 128 *)
  0x4e284aa4;       (* arm_AESE Q4 Q21 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x6e3d1c1f;       (* arm_EOR_VEC Q31 Q0 Q29 128 *)
  0x0ef0e160;       (* arm_PMULL_VEC Q0 Q11 Q16 64 *)
  0x6e0b417e;       (* arm_EXT Q30 Q11 Q11 64 *)
  0x4e284ac4;       (* arm_AESE Q4 Q22 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x6e291c26;       (* arm_EOR_VEC Q6 Q1 Q9 128 *)
  0x6e201fe0;       (* arm_EOR_VEC Q0 Q31 Q0 128 *)
  0x4ef0e17d;       (* arm_PMULL2_VEC Q29 Q11 Q16 64 *)
  0x4e284ae4;       (* arm_AESE Q4 Q23 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x6e2b1fc9;       (* arm_EOR_VEC Q9 Q30 Q11 128 *)
  0x4e284ac5;       (* arm_AESE Q5 Q22 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x6e3d1c61;       (* arm_EOR_VEC Q1 Q3 Q29 128 *)
  0x4ef1e123;       (* arm_PMULL2_VEC Q3 Q9 Q17 64 *)
  0x4e284ae5;       (* arm_AESE Q5 Q23 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x6e014029;       (* arm_EXT Q9 Q1 Q1 64 *)
  0x6e231cc6;       (* arm_EOR_VEC Q6 Q6 Q3 128 *)
  0x0ee7e023;       (* arm_PMULL_VEC Q3 Q1 Q7 64 *)
  0x4e284b05;       (* arm_AESE Q5 Q24 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x6e211c0b;       (* arm_EOR_VEC Q11 Q0 Q1 128 *)
  0x6e231d3d;       (* arm_EOR_VEC Q29 Q9 Q3 128 *)
  0x4e284b04;       (* arm_AESE Q4 Q24 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b25;       (* arm_AESE Q5 Q25 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x6e2b1cc6;       (* arm_EOR_VEC Q6 Q6 Q11 128 *)
  0x4e284b24;       (* arm_AESE Q4 Q25 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x6e3d1cc3;       (* arm_EOR_VEC Q3 Q6 Q29 128 *)
  0x4e284b45;       (* arm_AESE Q5 Q26 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b44;       (* arm_AESE Q4 Q26 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x6e03407d;       (* arm_EXT Q29 Q3 Q3 64 *)
  0x4e284b65;       (* arm_AESE Q5 Q27 *)
  0x4e284b64;       (* arm_AESE Q4 Q27 *)
  0x6e3c1ca6;       (* arm_EOR_VEC Q6 Q5 Q28 128 *)
  0x0ee7e07e;       (* arm_PMULL_VEC Q30 Q3 Q7 64 *)
  0x6e3c1c84;       (* arm_EOR_VEC Q4 Q4 Q28 128 *)
  0x6e3e1c00;       (* arm_EOR_VEC Q0 Q0 Q30 128 *)
  0x6e2a1c9e;       (* arm_EOR_VEC Q30 Q4 Q10 128 *)
  0x6e3d1c1f;       (* arm_EOR_VEC Q31 Q0 Q29 128 *)
  0x6e221cc6;       (* arm_EOR_VEC Q6 Q6 Q2 128 *)
  0x3c9d005e;       (* arm_STR Q30 X2 (Immediate_Offset (word 18446744073709551568)) *)
  0x3c9e0046;       (* arm_STR Q6 X2 (Immediate_Offset (word 18446744073709551584)) *)
  0x6e1f43fe;       (* arm_EXT Q30 Q31 Q31 64 *)
  0xb4000650;       (* arm_CBZ X16 (word 200) *)
  0x3cc1041d;       (* arm_LDR Q29 X0 (Postimmediate_Offset (word 16)) *)
  0x110001b1;       (* arm_ADD W17 W13 (rvalue (word 0)) *)
  0x110005ad;       (* arm_ADD W13 W13 (rvalue (word 1)) *)
  0x5ac00a31;       (* arm_REV W17 W17 *)
  0xaa118197;       (* arm_ORR X23 X12 (Shiftedreg X17 LSL 32) *)
  0xa90a5feb;       (* arm_STP X11 X23 SP (Immediate_Offset (iword (&160))) *)
  0x4e200bb1;       (* arm_REV64_VEC Q17 Q29 8 *)
  0x3dc02bea;       (* arm_LDR Q10 SP (Immediate_Offset (word 160)) *)
  0x6e3e1e28;       (* arm_EOR_VEC Q8 Q17 Q30 128 *)
  0x4eece10d;       (* arm_PMULL2_VEC Q13 Q8 Q12 64 *)
  0x5e18051e;       (* arm_DUP_ELEM_SCALAR Q30 Q8 1 64 *)
  0x4e284a4a;       (* arm_AESE Q10 Q18 *)
  0x4e28694a;       (* arm_AESMC Q10 Q10 *)
  0x0ee7e1af;       (* arm_PMULL_VEC Q15 Q13 Q7 64 *)
  0x2e281fde;       (* arm_EOR_VEC Q30 Q30 Q8 64 *)
  0x4e284a6a;       (* arm_AESE Q10 Q19 *)
  0x4e28694a;       (* arm_AESMC Q10 Q10 *)
  0x0eece10b;       (* arm_PMULL_VEC Q11 Q8 Q12 64 *)
  0x4e284a8a;       (* arm_AESE Q10 Q20 *)
  0x4e28694a;       (* arm_AESMC Q10 Q10 *)
  0x0eeee3c5;       (* arm_PMULL_VEC Q5 Q30 Q14 64 *)
  0x6e2d1d7e;       (* arm_EOR_VEC Q30 Q11 Q13 128 *)
  0x4e284aaa;       (* arm_AESE Q10 Q21 *)
  0x4e28694a;       (* arm_AESMC Q10 Q10 *)
  0x6e0d41ad;       (* arm_EXT Q13 Q13 Q13 64 *)
  0x6e3e1cbe;       (* arm_EOR_VEC Q30 Q5 Q30 128 *)
  0x4e284aca;       (* arm_AESE Q10 Q22 *)
  0x4e28694a;       (* arm_AESMC Q10 Q10 *)
  0x6e2f1da6;       (* arm_EOR_VEC Q6 Q13 Q15 128 *)
  0x4e284aea;       (* arm_AESE Q10 Q23 *)
  0x4e28694a;       (* arm_AESMC Q10 Q10 *)
  0x6e261fc1;       (* arm_EOR_VEC Q1 Q30 Q6 128 *)
  0x4e284b0a;       (* arm_AESE Q10 Q24 *)
  0x4e28694a;       (* arm_AESMC Q10 Q10 *)
  0x6e01402d;       (* arm_EXT Q13 Q1 Q1 64 *)
  0x0ee7e03f;       (* arm_PMULL_VEC Q31 Q1 Q7 64 *)
  0x4e284b2a;       (* arm_AESE Q10 Q25 *)
  0x4e28694a;       (* arm_AESMC Q10 Q10 *)
  0x6e3f1d6f;       (* arm_EOR_VEC Q15 Q11 Q31 128 *)
  0x4e284b4a;       (* arm_AESE Q10 Q26 *)
  0x4e28694a;       (* arm_AESMC Q10 Q10 *)
  0x6e2d1ded;       (* arm_EOR_VEC Q13 Q15 Q13 128 *)
  0x4e284b6a;       (* arm_AESE Q10 Q27 *)
  0x6e3c1d5e;       (* arm_EOR_VEC Q30 Q10 Q28 128 *)
  0x6e3d1fde;       (* arm_EOR_VEC Q30 Q30 Q29 128 *)
  0x3c81045e;       (* arm_STR Q30 X2 (Postimmediate_Offset (word 16)) *)
  0x6e0d41be;       (* arm_EXT Q30 Q13 Q13 64 *)
  0xd1000610;       (* arm_SUB X16 X16 (rvalue (word 1)) *)
  0xb5fffa10;       (* arm_CBNZ X16 (word 2096960) *)
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

let aes128_gcm_dec_tmc = define_trimmed "aes128_gcm_dec_tmc" aes128_gcm_dec_mc;;

let AES128_GCM_DEC_EXEC = ARM_MK_EXEC_RULE aes128_gcm_dec_tmc;;
let EXEC = AES128_GCM_DEC_EXEC;;

(* ------------------------------------------------------------------------- *)
(* Decryption-specific reconstruction.  The last round of each block (the    *)
(* aesr_final macro of the kernel source) is an aese with rk9 followed by    *)
(* two eor instructions, out = (aes_st XOR rk10) XOR plain.  This variant of *)
(* XOR_AES128_CIPHER_RECONSTRUCT folds the 10-round aese/aesmc tower with    *)
(* the input block and the last round key in that operand order,             *)
(* word_xor inblock (word_xor rk10 tower).                                   *)
(* ------------------------------------------------------------------------- *)

let XOR_AES128_CIPHER_RECONSTRUCT_DEC = prove
 (`word_xor inblock (word_xor rk10
     (aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc
      (aese (aesmc
             (aese (aesmc (aese (aesmc (aese (aesmc (aese plaintext rk0)) rk1))
        rk2)) rk3)) rk4)) rk5)) rk6)) rk7)) rk8)) rk9)) =
   word_xor
   (word_reversefields 8
   (aes128_cipher (word_reversefields 8 plaintext)
   (MAP (word_reversefields 8)
   [rk0; rk1; rk2; rk3; rk4; rk5; rk6; rk7; rk8; rk9; rk10])))
   inblock`,
  ONCE_REWRITE_TAC[GSYM XOR_AES128_CIPHER_RECONSTRUCT] THEN
  CONV_TAC WORD_BITWISE_RULE);;

(* Two AES rounds of a counter block; swp_inv carries block 4i's in Q30. *)
let aes2c = define_aes_partial "aes2c" 2;;

(* ------------------------------------------------------------------------- *)
(* The loop invariant swp_inv i.  It holds at the loop head pc + 0x294 at    *)
(* the start of iteration i and, for i + 1, at the back edge pc + 0x510 at   *)
(* its end.  Besides the loop-constant registers (round keys, key powers, IV *)
(* lanes, lengths and the reduction constant Q7) it records the pointers     *)
(* X0 = in_p + 64 * i + 64 and X2 = out_p + 64 * i, the count                *)
(* X1 = loop_count - 2 - i, the output blocks stored so far (j < 4 * i, and  *)
(* blocks 4i+2 and 4i+3), the GHASH of group i under way (terms built from   *)
(* the tag of the first 4 * i blocks XORed with block 4i and from blocks     *)
(* 4i+1..4i+3, some already multiplied by key powers), the AES of blocks 4i  *)
(* (aes2c in Q30) and 4i+1 (Q5, all but the last round key) under way, and   *)
(* the counter blocks for 4*i+c+1 .. 4*i+c+4 staged at sp + 176, 192, 208    *)
(* and 160.                                                                  *)
(* ------------------------------------------------------------------------- *)

let swp_inv : term =
`\(i:num) s.
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
    read Q7 s = word 13979173243358019584 /\
    read Q12 s =
      byteswap128 (h_power (ghash_twist (aes128_cipher (word 0) rk)) 0) /\
    read Q13 s =
      byteswap128 (h_power (ghash_twist (aes128_cipher (word 0) rk)) 1) /\
    read Q14 s =
      word_join (karatsuba_mid
                 (h_power (ghash_twist (aes128_cipher (word 0) rk)) 1))
        (karatsuba_mid
         (h_power (ghash_twist (aes128_cipher (word 0) rk)) 0)):int128 /\
    read Q15 s =
      byteswap128 (h_power (ghash_twist (aes128_cipher (word 0) rk)) 2) /\
    read Q16 s =
      byteswap128 (h_power (ghash_twist (aes128_cipher (word 0) rk)) 3) /\
    read Q17 s =
      word_join (karatsuba_mid
                 (h_power (ghash_twist (aes128_cipher (word 0) rk)) 3))
        (karatsuba_mid
         (h_power (ghash_twist (aes128_cipher (word 0) rk)) 2)):int128 /\
    read X11 s =
      word_subword (word_reversefields 8 (ctr_block nonce c)) (0,64):int64 /\
    read X12 s = (word_zx:int32->int64) ((word_zx:int64->int32) (word_subword
        (word_reversefields 8 (ctr_block nonce c)) (64,64):int64)) /\
    read X15 s = word (len_bits DIV 8) /\
    read X16 s = word loop_remain /\
    htable_mem_4 (ghash_twist (aes128_cipher (word 0) rk)) htable_p s /\
    (forall j. 4 * i + 4 <= j /\ j < nblocks ==>
        read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
          inblock j) /\
    read X0 s = word_add in_p (word (64 * i + 64)) /\
    read X2 s = word_add out_p (word (64 * i)) /\
    read X1 s = word (loop_count - 2 - i) /\
    read X13 s = (word_zx:int32->int64) (word (4 * i + c + 4)) /\
    (forall j. j < 4 * i
     ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
        word_xor (aes_ctr_block aes128_cipher c nonce rk j) (inblock j)) /\
    read (memory :> bytes128 (word_add out_p (word (64 * i + 32)))) s =
      word_xor (aes_ctr_block
        aes128_cipher c nonce rk (4 * i + 2)) (inblock (4 * i + 2)) /\
    read (memory :> bytes128 (word_add out_p (word (64 * i + 48)))) s =
      word_xor (aes_ctr_block
        aes128_cipher c nonce rk (4 * i + 3)) (inblock (4 * i + 3)) /\
    read Q11 s =
      word_xor (byteswap128
                (nist_ghash (aes128_cipher (word 0) rk) tag0 (list_of_seq
        (nist_input_block inblock) (4 * i))))
          (byteswap128 (word_reversefields 8 (inblock (4 *
        i)))) /\
    read Q0 s =
      word_join (word_subword (word_reversefields 8 (inblock (4 * i + 1)))
        (0,64):int64) (word_subword (word_reversefields 8 (inblock (4 * i + 1)))
        (64,64):int64):int128 /\
    read Q1 s =
      word_pmul (word_subword (word_reversefields 8 (inblock (4 * i + 3)))
        (0,64):int64)
          (word_subword
           (byteswap128 (h_power (ghash_twist (aes128_cipher (word 0)
        rk)) 0)) (64,64):int64):int128 /\
    read Q9 s =
      word_xor (word_pmul
                (word_subword (word_reversefields 8 (inblock (4 * i + 2)))
        (0,64):int64)
          (word_subword
           (byteswap128 (h_power (ghash_twist (aes128_cipher (word 0)
        rk)) 1)) (64,64):int64):int128)
          (word_pmul (word_subword (word_reversefields 8 (inblock
        (4 * i + 3))) (0,64):int64)
          (word_subword (byteswap128 (h_power (ghash_twist
        (aes128_cipher (word 0) rk)) 0)) (64,64):int64):int128) /\
    read Q31 s =
      word_xor (word_pmul
                (word_subword (word_reversefields 8 (inblock (4 * i + 2)))
        (64,64):int64)
          (word_subword
           (byteswap128 (h_power (ghash_twist (aes128_cipher (word 0)
        rk)) 1)) (0,64):int64):int128)
          (word_pmul (word_subword (word_reversefields 8 (inblock
        (4 * i + 3))) (64,64):int64)
          (word_subword (byteswap128 (h_power (ghash_twist
        (aes128_cipher (word 0) rk)) 0)) (0,64):int64):int128) /\
    read Q29 s = inblock (4 * i) /\
    read Q10 s = inblock (4 * i + 1) /\
    read Q30 s = aes2c nonce rk (4 * i + c) /\
    read (memory :> bytes128 (word_add stackpointer (word 176))) s =
      word_reversefields 8
        (ctr_block nonce (4 * i + c + 1)) /\
    read (memory :> bytes128 (word_add stackpointer (word 192))) s =
      word_reversefields 8
        (ctr_block nonce (4 * i + c + 2)) /\
    read (memory :> bytes128 (word_add stackpointer (word 208))) s =
      word_reversefields 8
        (ctr_block nonce (4 * i + c + 3)) /\
    read (memory :> bytes128 (word_add stackpointer (word 160))) s =
      word_reversefields 8
        (ctr_block nonce (4 * i + c + 4)) /\
    read X26 s = (word_zx:int32->int64) (word (4 * i + c + 7)) /\
    read Q5 s =
      aese (aesmc
            (aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc
        (aese (aesmc
               (aese (aesmc
                      (aese (aesmc
                             (aese (word_join (word_or ((word_zx:int32->int64)
        ((word_zx:int64->int32)
         (word_subword (word_reversefields 8 (ctr_block nonce c))
        (64,64):int64)))
          (word_shl ((word_zx:int32->int64)
                     (word_bytereverse (word (4 * i + c + 1)))) 32))
                       (word_subword (word_reversefields 8 (ctr_block nonce c))
        (0,64):int64):int128) (word_reversefields 8 (EL 0 rk))))
          (word_reversefields 8 (EL 1
        rk)))) (word_reversefields 8 (EL 2 rk))))
          (word_reversefields 8 (EL 3 rk))))
        (word_reversefields 8 (EL 4 rk)))) (word_reversefields 8 (EL 5 rk))))
        (word_reversefields 8 (EL 6 rk)))) (word_reversefields 8 (EL 7 rk))))
        (word_reversefields 8 (EL 8 rk)))) (word_reversefields 8 (EL 9 rk)) /\
    read X24 s =
      word_or ((word_zx:int32->int64) ((word_zx:int64->int32) (word_subword
        (word_reversefields 8 (ctr_block nonce c)) (64,64):int64))) (word_shl
        ((word_zx:int32->int64) (word_bytereverse (word (4 * i + c + 5))))
          32) /\
    read Q2 s =
      (word_zx:int64->int128) (word_subword (word_xor (word_join (word_subword
        (word_reversefields 8 (inblock (4 * i + 3))) (0,64):int64) (word_subword
        (word_reversefields 8 (inblock (4 * i + 3))) (64,64):int64):int128)
        ((word_zx:int64->int128)
         (word_subword (word_reversefields 8 (inblock (4 * i + 3)))
        (0,64):int64))) (0,64):int64) /\
    read Q3 s =
      word_pmul (word_subword (word_reversefields 8 (inblock (4 * i + 1)))
        (0,64):int64)
          (word_subword
           (byteswap128 (h_power (ghash_twist (aes128_cipher (word 0)
        rk)) 2)) (64,64):int64):int128 /\
    read Q4 s =
      word_pmul (word_subword
                 (word_xor (word_join (word_subword (word_reversefields 8
        (inblock (4 * i + 2))) (0,64):int64)
          (word_subword (word_reversefields 8 (inblock (4 * i
        + 2))) (64,64):int64):int128)
          (word_subword (word_join (word_join (word_subword
        (word_reversefields 8 (inblock (4 * i + 2))) (0,64):int64) (word_subword
        (word_reversefields 8 (inblock (4 * i + 2))) (64,64):int64):int128)
          (word_join
        (word_subword (word_reversefields 8 (inblock (4 * i + 2))) (0,64):int64)
          (word_subword
        (word_reversefields 8 (inblock (4 * i + 2)))
          (64,64):int64):int128):int256)
        (64,128):int128)) (64,64):int64)
          (karatsuba_mid (h_power (ghash_twist (aes128_cipher
        (word 0) rk)) 1)):int128 /\
    read Q6 s =
      word_xor (word_xor
                (byteswap128 (nist_ghash (aes128_cipher (word 0) rk) tag0
        (list_of_seq (nist_input_block inblock) (4 * i))))
          (word_join (word_subword
        (word_reversefields 8 (inblock (4 * i))) (0,64):int64)
          (word_subword (word_reversefields
        8 (inblock (4 * i))) (64,64):int64):int128))
          (word_subword (word_join (word_xor
        (byteswap128
         (nist_ghash (aes128_cipher (word 0) rk) tag0
          (list_of_seq (nist_input_block
        inblock) (4 * i))))
          (word_join (word_subword (word_reversefields 8 (inblock (4 * i)))
        (0,64):int64) (word_subword (word_reversefields 8 (inblock (4 * i)))
        (64,64):int64):int128))
          (word_xor (byteswap128 (nist_ghash (aes128_cipher (word 0) rk)
        tag0 (list_of_seq (nist_input_block inblock) (4 * i))))
          (word_join (word_subword
        (word_reversefields 8 (inblock (4 * i))) (0,64):int64)
          (word_subword (word_reversefields
        8 (inblock (4 * i))) (64,64):int64):int128)):int256) (64,128):int128) /\
    read Q8 s =
      word_pmul (word_subword
                 (word_xor (byteswap128 (nist_ghash (aes128_cipher (word
        0) rk) tag0 (list_of_seq (nist_input_block inblock) (4 * i))))
          (word_join (word_subword
        (word_reversefields 8 (inblock (4 * i))) (0,64):int64)
          (word_subword (word_reversefields
        8 (inblock (4 * i))) (64,64):int64):int128)) (64,64):int64)
          (word_subword (byteswap128
        (h_power (ghash_twist (aes128_cipher (word 0) rk)) 3))
          (64,64):int64):int128`;;

(* ------------------------------------------------------------------------- *)
(* Closers for the body leg SWP_DEC_BODYLEG, dispatched per conjunct by      *)
(* CLOSE_V8_TAC below; the closers of the other legs reuse many of them.     *)
(* First some helper lemmas and the GHASH closers.                           *)
(* ------------------------------------------------------------------------- *)

let SWP_JOIN_IS_BSW = prove
 (`!x:int128. word_join (word_subword x (0,64):int64)
   (word_subword x (64,64):int64):int128 = byteswap128 x`,
  GEN_TAC THEN REWRITE_TAC[byteswap128]);;
let xor_rcancel =
  prove(`!a b p:int128. (word_xor a p = word_xor b p) <=> (a = b)`,
  REPEAT GEN_TAC THEN CONV_TAC WORD_BITWISE_RULE);;
let SWP_SUB_LEMMA = prove
 (`i < loop_count - 2
   ==> word_sub (word (loop_count - 2 - i):int64) (word 1) =
     word (loop_count - 2 - (i + 1))`,
  DISCH_TAC THEN
  SUBGOAL_THEN `loop_count - 2 - (i + 1) = (loop_count - 2 - i) - 1`
    SUBST1_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[WORD_SUB;
               ARITH_RULE `i < loop_count - 2 ==> 1 <= loop_count - 2 - i`]);;
let dewrap80 =
  prove(`word (64 * i + 18446744073709551696):int64 = word (16 * (4 * i + 5))`,
  REWRITE_TAC[WORD_EQ; CONG; DIMINDEX_64] THEN
  REWRITE_TAC[ARITH_RULE
              `64 * i + 18446744073709551696 =
               (16 * (4 * i + 5)) + 1 * 2 EXP 64`] THEN
               REWRITE_TAC[MOD_MULT_ADD]);;
let dewrap96 =
  prove(`word (64 * i + 18446744073709551712):int64 = word (16 * (4 * i + 6))`,
  REWRITE_TAC[WORD_EQ; CONG; DIMINDEX_64] THEN
  REWRITE_TAC[ARITH_RULE
              `64 * i + 18446744073709551712 =
               (16 * (4 * i + 6)) + 1 * 2 EXP 64`] THEN
               REWRITE_TAC[MOD_MULT_ADD]);;
let dewrap112 =
  prove(`word (64 * i + 18446744073709551728):int64 = word (16 * (4 * i + 7))`,
  REWRITE_TAC[WORD_EQ; CONG; DIMINDEX_64] THEN
  REWRITE_TAC[ARITH_RULE
              `64 * i + 18446744073709551728 =
               (16 * (4 * i + 7)) + 1 * 2 EXP 64`] THEN
               REWRITE_TAC[MOD_MULT_ADD]);;

let SWP_GHASH_BRANCH2 = prove
 (`polyval_reduce_prop3
     (word_xor (word_pmul (nist_input_block inblock (4*i+3):int128)
                          (h_power (ghash_twist (aes128_cipher (word 0) rk)) 0))
     (word_xor (word_pmul (nist_input_block inblock (4*i+2))
                          (h_power (ghash_twist (aes128_cipher (word 0) rk)) 1))
     (word_xor (word_pmul (nist_input_block inblock (4*i+1))
                          (h_power (ghash_twist (aes128_cipher (word 0) rk)) 2))
     (word_pmul (word_xor (nist_ghash (aes128_cipher (word 0) rk) tag0
                              (list_of_seq (nist_input_block inblock) (4*i)))
                          (nist_input_block inblock (4*i)))
                (h_power (ghash_twist (aes128_cipher (word 0) rk)) 3)))))
   = nist_ghash (aes128_cipher (word 0) rk) tag0
       (list_of_seq (nist_input_block inblock) (4*i+4))`,
  MP_TAC(ISPECL [`ghash_twist (aes128_cipher (word 0) rk)`;
                 `[nist_input_block inblock (4*i+1);
                   nist_input_block inblock (4*i+2);
                   nist_input_block inblock (4*i+3)]:(int128)list`;
                 `nist_ghash (aes128_cipher (word 0) rk) tag0
                  (list_of_seq (nist_input_block inblock) (4*i)):int128`;
                 `nist_input_block inblock (4*i):int128`]
                   GHASH_POLYVAL_ACC_BATCHED) THEN
  REWRITE_TAC[LENGTH; ghash_wide] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[NIST_GHASH_IS_POLYVAL] THEN
  REWRITE_TAC[ARITH_RULE `4 * i + 4 = SUC(SUC(SUC(SUC(4 * i))))`] THEN
  REWRITE_TAC[list_of_seq] THEN REWRITE_TAC[GSYM APPEND_ASSOC; APPEND] THEN
  REWRITE_TAC[GHASH_ACC_APPEND] THEN
  REWRITE_TAC[ADD1; GSYM ADD_ASSOC] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[GSYM NIST_GHASH_IS_POLYVAL] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN AP_TERM_TAC THEN
  CONV_TAC WORD_BITWISE_RULE);;

(* The GHASH goals.  After DEC_GHASH_NORM_TAC a goal has the form
     word_xor <accumulator half> pending =
     word_xor (byteswap128 (nist_ghash h acc [four blocks])) pending.
   GHASH_SPLIT_TAC cancels the pending term and unwraps byteswap128 on both
   sides (WORD_JOIN_HALVES_CONG); GHASH_GROUP_TAC then closes the goal for
   one group of four blocks: the accumulator acc and the blocks blk 0..3 are
   abbreviated and the goal is bridged through polyval_reduce_prop3, branch
   1 being the Karatsuba recombination of the four partial products
   (KARATSUBA_JOIN_XOR4 after normalization) and branch 2 the GHASH step
   lemma supplied by the caller.  fold folds the input-block reads of the
   goal (nothing for the body, whose blocks are already inblock terms). *)
let WORD_JOIN_HALVES_CONG = prove
 (`x:int128 = y
   ==> word_join (word_subword x (0,64):int64)
     (word_subword x (64,64):int64):int128 =
                    word_join (word_subword y (0,64):int64)
                      (word_subword y (64,64):int64):int128`,
  DISCH_THEN SUBST1_TAC THEN REFL_TAC);;

let GHASH_SPLIT_TAC : tactic =
  REWRITE_TAC[SWP_JOIN_IS_BSW] THEN REWRITE_TAC[xor_rcancel] THEN
  REWRITE_TAC [byteswap128; SWP_SUBWORD_JOIN_MID] THEN
  MATCH_MP_TAC WORD_JOIN_HALVES_CONG;;

let GHASH_GROUP_TAC (fold:tactic) (acc:term) (blk:int->term) (branch2:tactic) :
  tactic =
  fold THEN
  MAP_EVERY ABBREV_TAC
     [mk_eq(`sofar:int128`, acc);
      mk_eq(`cipherblock_0:int128`, blk 0);
      mk_eq(`cipherblock_1:int128`, blk 1);
      mk_eq(`cipherblock_2:int128`, blk 2);
      mk_eq(`cipherblock_3:int128`, blk 3);
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
          (word_pmul (word_xor (sofar:int128) cipherblock_0)
           (h3:int128)))))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[PMUL_KARATSUBA_JOIN_ALT] THEN
    REWRITE_TAC[byteswap128; WORD_SUBWORD_XOR] THEN
    CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
    REWRITE_TAC[karatsuba_mid] THEN ASM_REWRITE_TAC[] THEN
    REPEAT(LET_TAC THEN ASM_REWRITE_TAC[]) THEN
    fold THEN REWRITE_TAC[INBLOCK_REASSEMBLE] THEN
    REWRITE_TAC[GSYM nist_input_block] THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[MESON[WORD_XOR_SYM]
                     `word_pmul (word_xor a b) (word_xor c d) =
                      word_pmul (word_xor b a) (word_xor c d)`] THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[POLYVAL_REDUCE_G2] THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY EXPAND_TAC ["ks"; "ks'"; "ks''"; "ks'''"] THEN
    CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN AP_TERM_TAC THEN
    REWRITE_TAC[GSYM karatsuba_join] THEN MATCH_ACCEPT_TAC KARATSUBA_JOIN_XOR4;
    MAP_EVERY EXPAND_TAC
      ["sofar";"cipherblock_0";"cipherblock_1";"cipherblock_2";"cipherblock_3";
       "h0";"h1";"h2";"h3"] THEN
    branch2];;

(* The body's GHASH closer: group i, accumulator nist_ghash .. (4 * i),
   blocks 4 * i .. 4 * i + 3. *)
let SWP_GHASH_CORE_TAC : tactic =
  DEC_GHASH_NORM_TAC THEN GHASH_SPLIT_TAC THEN
  GHASH_GROUP_TAC ALL_TAC
    `nist_ghash (aes128_cipher (word 0) rk) tag0
     (list_of_seq (nist_input_block inblock) (4 * i))`
    (fun j -> mk_comb(`nist_input_block inblock`,
                      if j = 0 then `4 * i`
                        else mk_binop `(+):num->num->num` `4 * i`
                          (mk_small_numeral j)))
    (ACCEPT_TAC SWP_GHASH_BRANCH2);;

(* Counter closers: Q30 (aes2c of the next group's first counter block), the
   counter blocks staged in the stack slots and the counter registers. *)
let SLOT_LANE_FOLDS = [
  WORD_RULE `word_add (word c) (word 4):int32 = word (c + 4)`;
  WORD_RULE `word_add (word (4*i+c+4)) (word 1):int32 = word(4*i+c+5)`;
  WORD_RULE `word_add (word (4*i+c+4)) (word 2):int32 = word(4*i+c+6)`;
  WORD_RULE `word_add (word (4*i+c+4)) (word 3):int32 = word(4*i+c+7)`;
  WORD_RULE `word_add (word_add (word (4*i)) (word (c+4))) (word 1):int32 =
             word(4*i+c+5)`;
  WORD_RULE `word_add (word_add (word (4*i)) (word (c+4))) (word 2):int32 =
             word(4*i+c+6)`;
  WORD_RULE `word_add (word_add (word (4*i)) (word (c+4))) (word 3):int32 =
             word(4*i+c+7)`;
  WORD_RULE `word_add (word_add (word (4*i)) (word (c+4))) (word 4):int32 =
             word(4*i+c+8)`];;
let RHS_IDX_NORMS = [
  ARITH_RULE `(4 * i + 4) + 4 = 4*i+8`; ARITH_RULE `(4 * i + 4) + 5 = 4*i+9`;
  ARITH_RULE `(4 * i + 4) + 6 = 4*i+10`;
  ARITH_RULE `(4 * i + 4) + 7 = 4*i+11`];;
let Q30_TAC : tactic =
  REWRITE_TAC[aes2c] THEN MERGE_CTR128_TAC 160 "s112" THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[CTR_ZX_NORM; ZX_COUNTER_UD] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[WORD_ADD] THEN REWRITE_TAC[CTR_BLOCK_BUILD_INSERT] THEN
  REWRITE_TAC[WORD_REVERSEFIELDS_REVERSEFIELDS] THEN TRY REFL_TAC THEN
  TRY(AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC);;
let SP160_TAC : tactic =
  MERGE_CTR128_TAC 160 "s159" THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[CTR_ZX_NORM; ZX_COUNTER_UD] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[WORD_ADD] THEN
  REWRITE_TAC[WORD_RULE
              `word_add (word_add (word (4 * i)) (word_add (word c) (word 4)))
               (word 4):int32 = word (4 * i + c + 8)`;
              WORD_RULE `word_add (word_add (word (4 * i)) (word (c + 4)))
                         (word 4):int32 = word (4 * i + c + 8)`] THEN
  REWRITE_TAC[CTR_BLOCK_BUILD_INSERT] THEN
  REWRITE_TAC[WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
  TRY REFL_TAC THEN TRY(AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC);;
let SP_SLOT3_TAC : tactic =
  REWRITE_TAC RHS_IDX_NORMS THEN REWRITE_TAC SLOT_LANE_FOLDS THEN
  REWRITE_TAC[CTR_BLOCK_BUILD_INSERT] THEN
  REWRITE_TAC[WORD_REVERSEFIELDS_REVERSEFIELDS] THEN TRY REFL_TAC;;
let CTR_ADD_FOLDS = [
  WORD_RULE `word_add (word (4*i+c+4)) (word 4):int32 = word(4*i+c+8)`;
  WORD_RULE `word_add (word (4*i+c+8)) (word 1):int32 = word(4*i+c+9)`;
  WORD_RULE `word_add (word (4*i+c+8)) (word 2):int32 = word(4*i+c+10)`;
  WORD_RULE `word_add (word (4*i+c+8)) (word 3):int32 = word(4*i+c+11)`];;
let CTR_RHS_NORMS = [
  ARITH_RULE `(4*i+4)+7 = 4*i+11`; ARITH_RULE `(4*i+4)+9 = 4*i+13`;
  ARITH_RULE `(4*i+4)+6 = 4*i+10`; ARITH_RULE `(4*i+4)+8 = 4*i+12`];;
let CTRREG_TAC : tactic =
  REWRITE_TAC CTR_RHS_NORMS THEN REWRITE_TAC CTR_ADD_FOLDS THEN
  TRY REFL_TAC THEN
  TRY(AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC);;

(* Output-store closers: the output blocks j < 4 * i stored before the leg
   are preserved by its stores, whose 16-byte cells are disjoint from them.
   They need 16 * nblocks <= 2 EXP 64 among the assumptions (leg_hyps has
   it; it follows from nblocks = len_bits DIV 128 and len_bits < 2^64). *)
let pth128 = prove
   (`!(a:int64) m n. 16 <= val(word_sub (word m) (word n):int64) /\
     16 <= val(word_sub (word n) (word m):int64)
          ==> orthogonal_components (bytes128 (word_add a (word m)))
            (bytes128 (word_add a (word n)))`,
    REPEAT STRIP_TAC THEN REWRITE_TAC[bytes128] THEN
    MATCH_MP_TAC ORTHOGONAL_COMPONENTS_COMPOSE_LEFT THEN
    REWRITE_TAC[ORTHOGONAL_COMPONENTS_BYTES; DIMINDEX_64] THEN
    REWRITE_TAC[VAL_WORD_ADD; DIMINDEX_64; NONOVERLAPPING_MODULO_MOD2] THEN
    MATCH_MP_TAC NONOVERLAPPING_MODULO_OFFSET_SIMPLE_BOTH THEN
    RULE_ASSUM_TAC(REWRITE_RULE[VAL_WORD_SUB_CASES; DIMINDEX_64]) THEN
    MP_TAC(ISPEC `word m:int64` VAL_BOUND) THEN
    MP_TAC(ISPEC `word n:int64` VAL_BOUND) THEN
    REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC);;
let orth_lemma = prove
   (`orthogonal_components c d /\ read c s' = read c s
     ==> read c (write d y s') = read c s`,
    MESON_TAC[orthogonal_components]);;
(* orthogonal_components (memory :> bytes128 (out_p + 16 * j))
   (memory :> bytes128 (out_p + OFF)) for j < 4 * i, from the bounds in the
   assumptions. *)
let OUT_ORTH_TAC : tactic =
  MATCH_MP_TAC ORTHOGONAL_COMPONENTS_COMPOSE_RIGHT THEN CONJ_TAC THENL
   [CONV_TAC VALID_COMPONENT_CONV;
    MATCH_MP_TAC pth128 THEN
    W(fun (asl,w) ->
      let sub1 = rand(rand(fst(dest_conj w))) in
      let mtm = rand(rator sub1) and ntm = rand sub1 in
      let m = rand mtm and n = rand ntm in
      SUBGOAL_THEN (list_mk_conj [mk_binop `(<):num->num->bool` m `2 EXP 64`;
                                  mk_binop `(<):num->num->bool` n `2 EXP 64`])
        STRIP_ASSUME_TAC THENL
       [REWRITE_TAC[ARITH_RULE `2 EXP 64 = 18446744073709551616`] THEN
        ASM_ARITH_TAC; ALL_TAC]) THEN
    REWRITE_TAC[VAL_WORD_SUB_CASES; VAL_WORD; DIMINDEX_64] THEN
    ASM_SIMP_TAC[MOD_LT] THEN ASM_ARITH_TAC];;
let ORTH_STEP_TAC : tactic =
  FIRST [ OUT_ORTH_TAC; ORTHOGONAL_COMPONENTS_TAC;
          (MATCH_MP_TAC ORTHOGONAL_COMPONENTS_COMPOSE_RIGHT THEN CONJ_TAC THENL
            [CONV_TAC VALID_COMPONENT_CONV; ORTHOGONAL_COMPONENTS_TAC]) ];;
let rec OUT_ROW_TAC g =
  (REFL_TAC ORELSE
   (MATCH_MP_TAC orth_lemma THEN CONJ_TAC
    THENL [ORTH_STEP_TAC; OUT_ROW_TAC])) g;;
(* OUT0_TAC: the conjunct !j. j < 4 * i ==> read (out_p + 16 * j) =
   word_xor (aes_ctr_block .. j) (inblock j), from the same fact about s0 and
   the orthogonality of the leg's stores (through its MAYCHANGE fact). *)
let OUT0_TAC : tactic =
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  FIRST_ASSUM(fun th ->
              if (try is_forall(concl th) && free_in `out_p:int64` (concl th) &&
                  free_in `s0:armstate`(concl th) with _->false)
                        then ASSUME_TAC(SPEC `j:num` th) else NO_TAC) THEN
  FIRST_X_ASSUM(fun th ->
                if (try is_imp(concl th) &&
                    free_in `s0:armstate`(concl th) with _->false)
                          then ASSUME_TAC(MP th (ASSUME `j < 4 * i`))
                            else NO_TAC) THEN
  FIRST_X_ASSUM(fun th ->
                if (try is_eq(concl th) && free_in `out_p:int64`(concl th) &&
                    free_in `s0:armstate`(concl th)
                                && fst(dest_const(fst(strip_comb(lhs(concl
                                    th)))))="read" with _->false)
                          then GEN_REWRITE_TAC RAND_CONV [SYM th]
                            else NO_TAC) THEN
  FIRST_ASSUM(fun th ->
              if (try not(is_eq(concl th)) &&
                  can(find_term(fun x->match x with
                                Const("MAYCHANGE",_)->true|_->false)) (concl th)
                                  with _->false)
                        then MP_TAC th else NO_TAC) THEN
  REWRITE_TAC[MAYCHANGE; SEQ_ID; GSYM SEQ_ASSOC] THEN
  PURE_REWRITE_TAC[ASSIGNS_SEQ] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[ASSIGNS_THM; LEFT_IMP_EXISTS_THM] THEN REPEAT GEN_TAC THEN
  DISCH_THEN (SUBST1_TAC o SYM) THEN
  OUT_ROW_TAC;;

let dec_setup_extra : tactic =
  RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_4]) THEN REWRITE_TAC[htable_mem_4] THEN
  (fun (asl,w) ->
    let jv = `j:num` in
    let reads0 =
      setify(flat(map
                  (fun (_,th) ->
                   find_terms (fun t -> try let h,a=strip_comb t in
         fst(dest_const h)="read" && length a=2 &&
           string_of_term(hd(tl a))="s0" with _->false) (concl th)) asl)) in
    let toab = filter (fun t -> not(free_in jv t) && not(free_in `in_p:int64` t)
                              && string_of_term t <> "read PC s0") reads0 in
    (EVERY (List.mapi
            (fun k t ->
             ABBREV_TAC
               (mk_eq(mk_var(Printf.sprintf "init_%d" k, type_of t), t))) toab))
                 (asl,w));;

(* Stepper parameters for this kernel: the memory reads at the tag, IV and
   Htable pointers are anchored (and, in the legs that also finish the
   output, those at the input and output pointers), as are the counter stack
   slots; REDSETX_DEC lists the registers whose latest value is carried. *)
let dec_anchors = [`tag_p:int64`; `ivec_p:int64`; `htable_p:int64`];;
let dec_anchors_io = dec_anchors @ [`in_p:int64`; `out_p:int64`];;
let ctr_slots = ["160"; "176"; "192"; "208"];;
let ctr_slots_all = ctr_slots @ ["168"; "184"; "200"; "216"];;
let REDSETX_DEC =
  ["Q0";"Q1";"Q2";"Q3";"Q4";"Q5";"Q6";"Q8";"Q9";"Q10";"Q11";"Q29";"Q30";"Q31";
                   "X0";"X2";"X7";"X13";"X14";"X17";"X21";"X23";"X24";"X25";
                   "X26";"X27";"X29"];;
(* The body stepper: steps 1..159 (pc + 0x294 .. pc + 0x50c), with the
   counter-slot merges just before the loads from the slots (steps 18, 47, 53
   and 113). *)
let steady_merges = [(17,208);(46,176);(52,192);(112,160)];;
let body_step_tac =
  SWP_STEPS_TAC dec_anchors ctr_slots REDSETX_DEC EXEC (K ALL_TAC) steady_merges
    (1--159);;

(* More closers: the input reads (INFOLD3_TAC, IN_READ_CLOSE_TAC), the GHASH
   partial products, the byteswap reassembly, the output stores (AES2C_OUT_TAC,
   OUTBLK_TAC) and the frame (close_goal10). *)
let inp_addr_norms = List.map (fun (kk,m) ->
    WORD_RULE (subst [mk_small_numeral kk, `K:num`; mk_small_numeral m, `M:num`]
                 `word_add (in_p:int64) (word (64*i+K)):int64 =
                  word_add in_p (word (16*(4*i+M)))`))
  [(0,0);(16,1);(32,2);(48,3);(64,4);(80,5);(96,6);(112,7)];;
(* INFOLD3_TAC: fold the wrapped address offsets (dewrap80/96/112), normalize
   the input addresses to in_p + word (16 * (4 * i + m)), then rewrite each
   input read with the input forall, which FIRST_ASSUM keeps so that several
   reads can use it. *)
let INFOLD3_TAC : tactic =
  REWRITE_TAC[dewrap80;dewrap96;dewrap112] THEN REWRITE_TAC inp_addr_norms THEN
  (fun (asl,w) ->
    let inreads = setify(find_terms (fun t -> match t with
      | Comb(Comb(Const("read",_),
                  Comb(Comb(Const(":>",_),Const("memory",_)),
                       Comb(Const("bytes128",_),a))),st)
          when (free_in `in_p:int64` a && (match st with Var _->true|_->false))
            -> true | _->false) w) in
    if inreads=[] then ALL_TAC (asl,w)
    else (EVERY (map (fun rd ->
       let st = rand rd in
       (* blk = the BLK in the `word (16 * BLK)` address subterm of rd *)
       let sixteenblk = rand(find_term (fun t -> match t with
           Comb(Const("word",_), n) when
             (try fst(dest_const(fst(strip_comb n)))="*" with _->false) ->
               true | _->false) rd) in
       let blk = rand sixteenblk in
       (SUBGOAL_THEN (mk_eq(rd, mk_comb(`inblock:num->int128`, blk)))
        ASSUME_TAC THENL
        [FIRST_ASSUM(fun fa ->
                     if (try is_forall(concl fa) &&
                         free_in `in_p:int64`(concl fa) &&
                           free_in st (concl fa) with _->false)
                                 then MATCH_MP_TAC fa THEN
                                 ARITH_HYPS_TAC else NO_TAC); ALL_TAC]))
      inreads)) (asl,w));;
let GHASH_PARTIAL_CLOSE_TAC : tactic =
  INFOLD3_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[INBLOCK_REASSEMBLE; GSYM nist_input_block] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[nist_input_block] THEN ASM_REWRITE_TAC[] THEN TRY REFL_TAC;;
(* A goal read (in_p + ADDR) sK = inblock m: the same address
   normalization, then the input forall. *)
let IN_READ_CLOSE_TAC : tactic =
  REWRITE_TAC[dewrap80;dewrap96;dewrap112] THEN REWRITE_TAC inp_addr_norms THEN
  (fun (asl,w) ->
     FIRST_ASSUM(fun fa ->
                 if (try is_forall(concl fa) && free_in `in_p:int64`(concl fa)
                                  && free_in (rand(lhs w)) (concl fa) with
                                    _->false)
                          then MATCH_MP_TAC fa THEN
                          ARITH_HYPS_TAC else NO_TAC) (asl,w));;
let SWP_BYTESWAP_REASSEMBLE_TAC : tactic =
  REWRITE_TAC[dewrap80;dewrap96;dewrap112] THEN INFOLD3_TAC THEN
  REWRITE_TAC[INBLOCK_REASSEMBLE] THEN REWRITE_TAC[GSYM nist_input_block] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[nist_input_block] THEN ASM_REWRITE_TAC[] THEN TRY REFL_TAC;;
(* The output store of a block whose AES tower starts from aes2c (block 4i)
   or is explicit (block 4i+1): unfold aes2c and fold the tower to
   aes_ctr_block. *)
let AES2C_OUT_TAC : tactic =
  REWRITE_TAC[aes2c] THEN REWRITE_TAC[XOR_AES128_CIPHER_RECONSTRUCT_DEC] THEN
  REWRITE_TAC[WORD_REVERSEFIELDS_REVERSEFIELDS] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM aes_ctr_block] THEN REWRITE_TAC[MAP] THEN
  REWRITE_TAC[WORD_REVERSEFIELDS_REVERSEFIELDS] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[aes_ctr_block] THEN
  REWRITE_TAC[ARITH_RULE `4*i+2 = (4*i)+2`; ARITH_RULE `(4*i+1)+2 = 4*i+3`] THEN
  REWRITE_TAC[CTR_BLOCK_BUILD_INSERT] THEN
  REWRITE_TAC[WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
  REWRITE_TAC[ARITH_RULE `4*i+3 = (4*i+1)+2`] THEN
  REWRITE_TAC[GSYM aes_ctr_block] THEN TRY REFL_TAC;;
(* The frame conjunct, from the MAYCHANGE fact for s0 .. sN among the
   assumptions and subsumption. *)
let close_goal10 : tactic =
  fun (asl,w) ->
    let frame_th = try snd(List.find (fun (_,th) -> let c=concl th in
        (try not(is_eq c) &&
         can(find_term(fun x->match x with
                       Const("MAYCHANGE",_)->true|_->false)) c
            && (match c with Comb(Comb(_,a),b) -> is_var a &&
                is_var b | _->false) with _->false)) asl)
      with _ -> failwith "close_goal10: no frame asm" in
    (MATCH_MP_TAC(MATCH_MP SUBSUMED_APPLY frame_th) THEN
     REWRITE_TAC[ETA_AX; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
     SUBSUMED_MAYCHANGE_TAC) (asl,w);;
(* OUTBLK_TAC addr_rule: the output store of block 4i+6 or 4i+7 (offset
   64 * i + 96 or 64 * i + 112, blocks 2 and 3 of group i + 1): rewrite the
   address with addr_rule, fold the input reads, reconstruct the AES tower
   and collapse the counter.  It fails at once unless the offset of
   addr_rule occurs in the goal: otherwise, in
   FIRST [close_outahead96; close_outahead112], close_outahead96 would run
   on the +112 goal with a no-op address rewrite and fail in the middle of
   the reconstruction before close_outahead112 is tried. *)
let OUTBLK_TAC (addr_rule:thm) : tactic =
  fun (asl,w) ->
    if not (free_in (lhs(concl addr_rule)) w)
    then failwith "OUTBLK_TAC: offset absent" else
   (REWRITE_TAC[addr_rule] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[dewrap80;dewrap96;dewrap112] THEN INFOLD3_TAC THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[XOR_AES128_CIPHER_RECONSTRUCT_DEC] THEN
  REWRITE_TAC[WORD_REVERSEFIELDS_REVERSEFIELDS] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM aes_ctr_block] THEN REWRITE_TAC[MAP] THEN
  REWRITE_TAC[WORD_REVERSEFIELDS_REVERSEFIELDS] THEN ASM_REWRITE_TAC[] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[aes_ctr_block] THEN
  AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[ZX_COUNTER_UD; CTR_ZX_NORM] THEN
  REWRITE_TAC[WORD_RULE
              `word_add (word (4*i+c+4)) (word 2):int32 = word(4*i+c+6)`;
              WORD_RULE `word_add (word (4*i+7)) (word 2):int32 =
                         word(4*i+9)`] THEN
  REWRITE_TAC[CTR_BLOCK_BUILD_INSERT] THEN
  REWRITE_TAC[WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
  REWRITE_TAC[ARITH_RULE `4*i+8 = (4*i+6)+2`;
              ARITH_RULE `4*i+9 = (4*i+7)+2`] THEN
  REWRITE_TAC[GSYM aes_ctr_block] THEN TRY REFL_TAC) (asl,w);;
let close_outahead96 : tactic =
  OUTBLK_TAC (ARITH_RULE `64 * i + 96 = (64 * i + 64) + 32`);;
let close_outahead112 : tactic =
  OUTBLK_TAC (ARITH_RULE `64 * i + 112 = (64 * i + 64) + 48`);;

(* SWP_Q8_TAC: the Q8 conjunct, a word_pmul of a subword of the tag XOR block
   term: peel the word_pmul and the word_subword, then SWP_GHASH_CORE_TAC. *)
let SWP_Q8_TAC : tactic = AP_THM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN
AP_TERM_TAC THEN SWP_GHASH_CORE_TAC;;
(* SWP_Q6_FULL_TAC: the Q6 conjunct, a word_xor in which the tag XOR block
   term occurs twice: split it by BINOP_TAC, close the first operand by
   SWP_GHASH_CORE_TAC, and peel the subword of the second (splitting again if
   needed) before SWP_GHASH_CORE_TAC. *)
let SWP_Q6_FULL_TAC : tactic =
  BINOP_TAC THENL
   [SWP_GHASH_CORE_TAC;
    AP_THM_TAC THEN AP_TERM_TAC THEN
    (SWP_GHASH_CORE_TAC ORELSE (BINOP_TAC THEN SWP_GHASH_CORE_TAC))];;

(* CLOSE_V8_TAC: the per-conjunct dispatcher of the body leg, by the shape of
   the conjunct, most specific first. *)
let CLOSE_V8_TAC : tactic =
  fun (asl,w) ->
    let has_mc t =
      try can(find_term(fun x->match x with
                        Const("MAYCHANGE",_)->true|_->false)) t with _->false in
    let hd t = try fst(dest_const(fst(strip_comb t))) with _->"" in
    let rh c = try has c (rhs w) with _->false in
    if has_mc w then close_goal10 (asl,w)
    else if has "aligned_bytes_loaded" w then ASM_REWRITE_TAC[] (asl,w)
    else if is_eq w && rh "aes2c" then MUST_PROGRESS Q30_TAC (asl,w)
    else if is_eq w && hd(lhs w)="read" && rh "inblock" && not(rh "word_xor") &&
      not(rh "aes_ctr_block") then MUST_PROGRESS IN_READ_CLOSE_TAC (asl,w)
    else if is_eq w && hd(lhs w)="read" && rh "ctr_block" &&
      rh "word_reversefields" then MUST_PROGRESS SP160_TAC (asl,w)
    else if is_eq w && hd(lhs w)="word_join" && rh "ctr_block" &&
      rh "word_reversefields" then MUST_PROGRESS SP_SLOT3_TAC (asl,w)
    else if is_eq w &&
      (hd(lhs w)="word_or" ||
       (hd(lhs w)="word_zx" && String.length(string_of_term w)<200))
         then MUST_PROGRESS CTRREG_TAC (asl,w)
    else if is_forall w then MUST_PROGRESS OUT0_TAC (asl,w)
    else if is_eq w && hd(lhs w)="read" && rh "aes_ctr_block"
      then MUST_PROGRESS (FIRST[close_outahead96; close_outahead112]) (asl,w)
    (* GHASH goals, whose right-hand side mentions nist_ghash: peel, then
       SWP_GHASH_CORE_TAC. *)
    else if is_eq w && rh "nist_ghash" && hd(lhs w)="word_pmul"
      then MUST_PROGRESS (FIRST[SWP_Q8_TAC; SWP_GHASH_CORE_TAC]) (asl,w)
    else if is_eq w && rh "nist_ghash" && hd(lhs w)="word_xor"
      then MUST_PROGRESS (FIRST[SWP_GHASH_CORE_TAC; SWP_Q6_FULL_TAC]) (asl,w)
    else if is_eq w && rh "nist_ghash"
      then MUST_PROGRESS SWP_GHASH_CORE_TAC (asl,w)
    (* output-store readback with an aes2c or explicit aese tower:
       word_xor (inblock ..) (word_xor rk10 tower) =
       word_xor (aes_ctr_block ..) (inblock ..) *)
    else if is_eq w && rh "aes_ctr_block" &&
      (has "aes2c" w || has "aese" (lhs w))
        then MUST_PROGRESS AES2C_OUT_TAC (asl,w)
    (* byteswap reassembly, Karatsuba partials over reassembled input blocks *)
    else if is_eq w && hd(lhs w)="word_join"
      then MUST_PROGRESS
        (FIRST[SWP_BYTESWAP_REASSEMBLE_TAC; GHASH_PARTIAL_CLOSE_TAC]) (asl,w)
    else MUST_PROGRESS
      (FIRST[GHASH_PARTIAL_CLOSE_TAC; AES2C_OUT_TAC; SWP_GHASH_CORE_TAC;
             CTRREG_TAC; ASM_REWRITE_TAC[] THEN TRY REFL_TAC]) (asl,w)
     ;;

(* ------------------------------------------------------------------------- *)
(* The leg goals.                                                            *)
(* ------------------------------------------------------------------------- *)

(* Every leg is stated with the main theorem's frame (swp_frame) and with
   state predicates of the form
     \s. aligned_bytes_loaded s (word pc) mc /\ read PC s = word (pc + off) /\
         <body>,
   which is how ENSURES_SEQUENCE_TAC and ENSURES_WHILE_UP_TAC present the
   leaf goals of the main theorem; the entry (0xa0) and exit (0xaa0)
   mid-conditions are shared with the main theorem below.  A leg then
   discharges its leaf goal by MATCH_MP_TAC (see APPLY_LEG_TAC). *)
let ap inv i s = rhs(concl(REDEPTH_CONV BETA_CONV (list_mk_comb(inv,[i;s]))));;
let leg_state off body =
  mk_abs(`s:armstate`,
    list_mk_conj(`aligned_bytes_loaded s (word pc) aes128_gcm_dec_tmc` ::
                 mk_eq(`read PC s`,
                       mk_comb(`word:num->int64`, mk_binop `+` `pc:num` off)) ::
                 conjuncts body));;
let inv_state off idx = leg_state off (ap swp_inv idx `s:armstate`);;
let swp_frame = `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
    MAYCHANGE [X19; X20; X21; X22; X23; X24; X25; X26; X27; X28; X29; X30] ,,
    MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
    MAYCHANGE [memory :> bytes(out_p, 16 * nblocks); memory :> bytes(tag_p, 16);
               memory :> bytes(ivec_p, 16);
               memory :> bytes(word_add stackpointer (word 160), 64)]`;;
let leg_goal vars hyps pre post =
  list_mk_forall(vars,
                 mk_imp(hyps,
                        list_mk_comb(`ensures arm`, [pre; post; swp_frame])));;

(* The hypotheses of the body leg; the other legs replace the loop-index
   bound by their own constraint on loop_count.  key_p occurs only here, so
   a leg applied by MATCH_MP_TAC leaves ?key_p. *)
let leg_hyps = `aligned 16 (stackpointer:int64) /\
    nblocks DIV 4 = loop_count /\ nblocks MOD 4 = loop_remain /\
    16 * nblocks <= 2 EXP 64 /\
    ([EL 0 rk; EL 1 rk; EL 2 rk; EL 3 rk; EL 4 rk; EL 5 rk; EL 6 rk; EL 7 rk;
      EL 8 rk; EL 9 rk; EL 10 rk]:(int128)list = rk) /\
    i < loop_count - 2 /\
    nonoverlapping ((out_p:int64), 16 * nblocks) (word pc, 2988) /\
    nonoverlapping (word_add (stackpointer:int64) (word 160), 64)
      (word pc, 2988) /\
    nonoverlapping (word_add (stackpointer:int64) (word 160), 64)
      ((key_p:int64), 176) /\
    nonoverlapping (word_add (stackpointer:int64) (word 160), 64)
      ((htable_p:int64), 96) /\
    (in_p:int64 = out_p \/
     nonoverlapping ((in_p:int64), 16 * nblocks)
       ((out_p:int64), 16 * nblocks)) /\
    nonoverlapping ((in_p:int64), 16 * nblocks)
      (word_add (stackpointer:int64) (word 160), 64) /\
    nonoverlapping ((out_p:int64), 16 * nblocks)
      (word_add (stackpointer:int64) (word 160), 64) /\
    nonoverlapping ((tag_p:int64), 16) ((out_p:int64), 16 * nblocks) /\
    nonoverlapping ((tag_p:int64), 16)
      (word_add (stackpointer:int64) (word 160), 64) /\
    nonoverlapping ((ivec_p:int64), 16) ((out_p:int64), 16 * nblocks) /\
    nonoverlapping ((ivec_p:int64), 16)
      (word_add (stackpointer:int64) (word 160), 64) /\
    nonoverlapping ((htable_p:int64), 96) ((out_p:int64), 16 * nblocks) /\
    nonoverlapping ((htable_p:int64), 96)
      (word_add (stackpointer:int64) (word 160), 64)`;;
let vs =
  [`in_p:int64`;`out_p:int64`;`len_bits:int64`;`tag_p:int64`;`ivec_p:int64`;
   `key_p:int64`;`htable_p:int64`;
          `tag0:int128`;`nonce:int128`;`rk:(int128)list`;`inblock:num->int128`;
          `pc:num`;
          `stackpointer:int64`;`nblocks:num`;`loop_count:num`;
          `loop_remain:num`];;
let base_hyps =
  filter (fun t -> not (t = `i < loop_count - 2`) &&
          not (t = `3 <= loop_count`)) (conjuncts leg_hyps);;

(* The entry state at pc + 0xa0 (after the register setup) and the exit
   state at pc + 0xaa0 (after the four-block loop, before the single-block
   tail loop), as used by the legs and by the main theorem. *)
let entry_body =
  `read X0 s = in_p /\ read X2 s = out_p /\ read X3 s = tag_p /\
   read X4 s = ivec_p /\
    read X6 s = htable_p /\ read SP s = stackpointer /\
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
    read Q12 s =
      byteswap128 (h_power (ghash_twist (aes128_cipher (word 0) rk)) 0) /\
    read Q13 s =
      byteswap128 (h_power (ghash_twist (aes128_cipher (word 0) rk)) 1) /\
    read Q14 s =
      word_join (karatsuba_mid
                 (h_power (ghash_twist (aes128_cipher (word 0) rk)) 1))
                   (karatsuba_mid
                    (h_power (ghash_twist (aes128_cipher (word 0) rk)) 0)) /\
    read Q15 s =
      byteswap128 (h_power (ghash_twist (aes128_cipher (word 0) rk)) 2) /\
    read Q16 s =
      byteswap128 (h_power (ghash_twist (aes128_cipher (word 0) rk)) 3) /\
    read Q17 s =
      word_join (karatsuba_mid
                 (h_power (ghash_twist (aes128_cipher (word 0) rk)) 3))
                   (karatsuba_mid
                    (h_power (ghash_twist (aes128_cipher (word 0) rk)) 2)) /\
    read Q7 s = word 13979173243358019584 /\
    read X11 s =
      word_subword (word_reversefields 8 (ctr_block nonce c):int128)
        (0,64):int64 /\
    read X12 s =
      word_zx (word_zx
               (word_subword (word_reversefields 8 (ctr_block nonce c):int128)
                (64,64):int64):int32):int64 /\
    read X13 s = word_zx (word c:int32):int64 /\
    read X15 s = word(len_bits DIV 8) /\ read X1 s = word loop_count /\
    read X7 s = word nblocks /\ read X16 s = word loop_remain /\
    read Q30 s = byteswap128 tag0 /\
    htable_mem_4 (ghash_twist (aes128_cipher (word 0) rk)) htable_p s /\
    (!j. j < nblocks
     ==> read (memory :> bytes128 (word_add in_p (word(16*j)))) s =
       inblock j)`;;
let entry_state = leg_state `0xa0` entry_body;;

let exit_body = `read X0 s = word_add in_p (word (64 * loop_count)) /\
   read X2 s = word_add out_p (word (64 * loop_count)) /\
   read X3 s = tag_p /\ read X4 s = ivec_p /\ read X6 s = htable_p /\
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
   read Q12 s =
     byteswap128 (h_power (ghash_twist (aes128_cipher (word 0) rk)) 0) /\
   read Q13 s =
     byteswap128 (h_power (ghash_twist (aes128_cipher (word 0) rk)) 1) /\
   read Q14 s =
     word_join (karatsuba_mid
                (h_power (ghash_twist (aes128_cipher (word 0) rk)) 1))
                  (karatsuba_mid
                   (h_power (ghash_twist (aes128_cipher (word 0) rk)) 0)) /\
   read Q15 s =
     byteswap128 (h_power (ghash_twist (aes128_cipher (word 0) rk)) 2) /\
   read Q16 s =
     byteswap128 (h_power (ghash_twist (aes128_cipher (word 0) rk)) 3) /\
   read Q17 s =
     word_join (karatsuba_mid
                (h_power (ghash_twist (aes128_cipher (word 0) rk)) 3))
                  (karatsuba_mid
                   (h_power (ghash_twist (aes128_cipher (word 0) rk)) 2)) /\
   read Q7 s = word 13979173243358019584 /\
   read X11 s =
     word_subword (word_reversefields 8 (ctr_block nonce c):int128)
       (0,64):int64 /\
   read X12 s =
     word_zx (word_zx
              (word_subword (word_reversefields 8 (ctr_block nonce c):int128)
               (64,64):int64):int32):int64 /\
   read X13 s = word_zx (word (4 * loop_count + c):int32):int64 /\
   read X15 s = word(len_bits DIV 8) /\ read X16 s = word loop_remain /\
   read Q30 s =
     byteswap128
       (nist_ghash (aes128_cipher (word 0) rk) tag0
        (list_of_seq (nist_input_block inblock) (4 * loop_count))) /\
   htable_mem_4 (ghash_twist (aes128_cipher (word 0) rk)) htable_p s /\
   (!j. 4 * loop_count <= j /\ j < nblocks
    ==> read (memory :> bytes128 (word_add in_p (word(16*j)))) s = inblock j) /\
   (!j. j < 4 * loop_count
    ==> read (memory :> bytes128 (word_add out_p (word(16*j)))) s =
      word_xor (aes_ctr_block aes128_cipher c nonce rk j) (inblock j))`;;
let exit_state = leg_state `0xaa0` exit_body;;

let bodyleg_goal =
  leg_goal (vs @ [`i:num`]) leg_hyps (inv_state `0x294` `i:num`)
    (inv_state `0x510` `i + 1`);;

(* ------------------------------------------------------------------------- *)
(* The GHASH step for an arbitrary group k, SWP_GHASH_BRANCH2_SETTLED: the   *)
(* body's SWP_GHASH_BRANCH2 with 4 * k in place of 4 * i.  The accumulator   *)
(* is the tag nist_ghash .. (list_of_seq .. (4 * k)) and the right-hand side *)
(* the next tag nist_ghash .. (list_of_seq .. (4 * k + 4)), the form of the  *)
(* goals.  The drain uses it for each of its two groups (DRAIN_Q30_TAC) and  *)
(* iter_1 for its single group.                                              *)
(* ------------------------------------------------------------------------- *)
let SWP_GHASH_BRANCH2_SETTLED = prove
 (`!k. polyval_reduce_prop3
     (word_xor (word_pmul (nist_input_block inblock (4*k+3):int128)
                          (h_power (ghash_twist (aes128_cipher (word 0) rk)) 0))
     (word_xor (word_pmul (nist_input_block inblock (4*k+2))
                          (h_power (ghash_twist (aes128_cipher (word 0) rk)) 1))
     (word_xor (word_pmul (nist_input_block inblock (4*k+1))
                          (h_power (ghash_twist (aes128_cipher (word 0) rk)) 2))
     (word_pmul (word_xor (nist_ghash (aes128_cipher (word 0) rk) tag0
                              (list_of_seq (nist_input_block inblock) (4*k)))
                          (nist_input_block inblock (4*k)))
                (h_power (ghash_twist (aes128_cipher (word 0) rk)) 3)))))
   = nist_ghash (aes128_cipher (word 0) rk) tag0
       (list_of_seq (nist_input_block inblock) (4*k+4))`,
  GEN_TAC THEN
  MP_TAC(ISPECL [`ghash_twist (aes128_cipher (word 0) rk)`;
                 `[nist_input_block inblock (4*k+1);
                   nist_input_block inblock (4*k+2);
                   nist_input_block inblock (4*k+3)]:(int128)list`;
                 `nist_ghash (aes128_cipher (word 0) rk) tag0
                  (list_of_seq (nist_input_block inblock) (4*k)):int128`;
                 `nist_input_block inblock (4*k):int128`]
                   GHASH_POLYVAL_ACC_BATCHED) THEN
  REWRITE_TAC[LENGTH; ghash_wide] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[NIST_GHASH_IS_POLYVAL] THEN
  REWRITE_TAC[ARITH_RULE `4 * k + 4 = SUC(SUC(SUC(SUC(4 * k))))`] THEN
  REWRITE_TAC[list_of_seq] THEN REWRITE_TAC[GSYM APPEND_ASSOC; APPEND] THEN
  REWRITE_TAC[GHASH_ACC_APPEND] THEN
  REWRITE_TAC[ADD1; GSYM ADD_ASSOC] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[GSYM NIST_GHASH_IS_POLYVAL] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN AP_TERM_TAC THEN
  CONV_TAC WORD_BITWISE_RULE);;

(* ------------------------------------------------------------------------- *)
(* The body leg SWP_DEC_BODYLEG: pc + 0x294 -> pc + 0x510, from swp_inv i to *)
(* swp_inv (i + 1), for i < loop_count - 2.                                  *)
(* ------------------------------------------------------------------------- *)

(* CTR_CANON_TAC: canonicalize the counter arithmetic a closer may leave,
   e.g. aes_ctr_block .. (c+1) .. (4*i) against .. c .. (4*i+1), or
   ctr_block nonce (4*i+c+K) against ((4*i+K)+c): fold the built counter
   blocks, unfold aes_ctr_block, normalize the sums to 4 * i + c + K and
   try REFL_TAC. *)
let CTR_CANON_TAC : tactic =
  REWRITE_TAC[CTR_BLOCK_BUILD_INSERT; WORD_REVERSEFIELDS_REVERSEFIELDS;
              aes_ctr_block] THEN
  REWRITE_TAC[ARITH_RULE `(4 * i + 1) + c = 4 * i + c + 1`;
              ARITH_RULE `(4 * i + 2) + c = 4 * i + c + 2`;
              ARITH_RULE `(4 * i + 3) + c = 4 * i + c + 3`;
              ARITH_RULE `(4 * i + 4) + c = 4 * i + c + 4`;
              ARITH_RULE `(4 * i + 5) + c = 4 * i + c + 5`;
              ARITH_RULE `(4 * i + 6) + c = 4 * i + c + 6`;
              ARITH_RULE `(4 * i + 7) + c = 4 * i + c + 7`;
              ARITH_RULE `4 * i + (c + 4) + 4 = 4 * i + c + 8`;
              ARITH_RULE `4 * i + (c + 5) + 4 = 4 * i + c + 9`] THEN
  TRY REFL_TAC;;
let SWP_DEC_BODYLEG = prove(bodyleg_goal,
  REPEAT GEN_TAC THEN INTRO_HYPS_TAC THEN ENSURES_INIT_TAC "s0" THEN
  SUBGOAL_THEN `4*i+7 < nblocks` ASSUME_TAC THENL
   [SUBST1_TAC(SYM(ASSUME `nblocks DIV 4 = loop_count`)) THEN
    MP_TAC(SPECL [`nblocks:num`;`4`] DIVISION) THEN
    UNDISCH_TAC `i < loop_count - 2` THEN
    SUBST1_TAC(SYM(ASSUME `nblocks DIV 4 = loop_count`)) THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `read (memory :> bytes128 (word_add in_p (word (64*i+64)))) s0 =
    inblock (4*i+4) /\
    read (memory :> bytes128 (word_add in_p (word (64*i+80)))) s0 =
      inblock (4*i+5) /\
    read (memory :> bytes128 (word_add in_p (word (64*i+96)))) s0 =
      inblock (4*i+6) /\
    read (memory :> bytes128 (word_add in_p (word (64*i+112)))) s0 =
      inblock (4*i+7)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [SUBST1_TAC(WORD_RULE
                 `word_add in_p (word (64*i+64)):int64 =
                  word_add in_p (word (16*(4*i+4)))`);
      SUBST1_TAC(WORD_RULE
                 `word_add in_p (word (64*i+80)):int64 =
                  word_add in_p (word (16*(4*i+5)))`);
      SUBST1_TAC(WORD_RULE
                 `word_add in_p (word (64*i+96)):int64 =
                  word_add in_p (word (16*(4*i+6)))`);
      SUBST1_TAC(WORD_RULE
                 `word_add in_p (word (64*i+112)):int64 =
                  word_add in_p (word (16*(4*i+7)))`)] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  INPUT_LEG_TAC [`4*i+4`; `4*i+5`; `4*i+6`; `4*i+7`] THEN
  dec_setup_extra THEN
  body_step_tac THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ARITH_RULE `j < 4 * (i + 1) <=>
                          j < 4 * i \/ j = 4 * i \/ j = 4 * i + 1 \/
                          j = 4 * i + 2 \/ j = 4 * i + 3`] THEN
  ASM_REWRITE_TAC[TAUT `p \/ q ==> r <=> (p ==> r) /\ (q ==> r)`] THEN
  REWRITE_TAC[FORALL_AND_THM; FORALL_UNWIND_THM2] THEN
  REWRITE_TAC[ARITH_RULE `16 * (4 * a + b) = 64 * a + 16 * b`] THEN
  REWRITE_TAC[ARITH_RULE `16 * 4 * i = 64 * i`] THEN
  CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ZX_COUNTER_UD; ZX_COUNTER_INC; CTR_ZX_NORM] THEN
  REWRITE_TAC[ARITH_RULE `4 * (i + 1) = 4 * i + 4`;
              ARITH_RULE `64 * (i + 1) = 64 * i + 64`;
              ARITH_RULE `(4 * i + 4) + 1 = 4 * i + 5`;
              ARITH_RULE `(4 * i + 4) + 2 = 4 * i + 6`;
              ARITH_RULE `(4 * i + 4) + 3 = 4 * i + 7`;
              ARITH_RULE `(4 * i + 4) + c = 4 * i + c + 4`;
              ARITH_RULE `(4 * i + 4) + c + 1 = 4 * i + c + 5`;
              ARITH_RULE `(4 * i + 4) + c + 2 = 4 * i + c + 6`;
              ARITH_RULE `(4 * i + 4) + c + 3 = 4 * i + c + 7`;
              ARITH_RULE `(64 * i + 64) + 64 = 64 * i + 128`;
              ARITH_RULE `(64 * i + 64) + 32 = 64 * i + 96`;
              ARITH_RULE `(64 * i + 64) + 48 = 64 * i + 112`;
              ARITH_RULE `(4 * i + 4) + 6 = 4 * i + 10`;
              ARITH_RULE `(4 * i + 4) + 9 = 4 * i + 13`] THEN
  REWRITE_TAC[WORD_RULE
              `word_add (word (4 * i)) (word_add (word c) (word 4)):int32 =
               word (4 * i + c + 4)`;
              WORD_RULE `word_add (word (4 * i + c + 4)) (word 4):int32 =
                         word(4 * i + c + 8)`] THEN
  ASM_SIMP_TAC[SWP_SUB_LEMMA] THEN
  REPEAT CONJ_TAC THEN CLOSE_V8_TAC THEN TRY CTR_CANON_TAC)
  ;;

(* ------------------------------------------------------------------------- *)
(* The fill: pc + 0xa0 -> pc + 0x294, establishing swp_inv 0.                *)
(* ------------------------------------------------------------------------- *)

let fill_hyps = subst [`3 <= loop_count`, `i < loop_count - 2`] leg_hyps;;
let fill_goal = leg_goal vs fill_hyps entry_state (inv_state `0x294` `0`);;

(* The rev64 instruction on a whole block as byteswap128 of its byte
   reversal.  The fill computes the block term of the GHASH seed Q11 at
   i = 0 as rev64 of inblock 0, which the invariant writes as
   byteswap128 (word_reversefields 8 (inblock 0)). *)
let REV64_16B_IS_BSW_REVFIELDS = prove(
  `word_join (word_bytereverse (word_subword (x:int128) (64,64):int64):int64)
             (word_bytereverse
              (word_subword (x:int128) (0,64):int64):int64):int128
   = byteswap128 (word_reversefields 8 x)`,
  GEN_REWRITE_TAC I [WORD_EQ_BITS_ALT] THEN X_GEN_TAC `k:num` THEN
  DISCH_TAC THEN
  POP_ASSUM MP_TAC THEN SPEC_TAC(`k:num`,`k:num`) THEN
  REWRITE_TAC[GSYM WORD_EQ_BITS_ALT] THEN REWRITE_TAC[byteswap128] THEN
  CONV_TAC(BINOP_CONV(RAND_CONV(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV))) THEN
  CONV_TAC BITBLAST_RULE);;

(* KS9_CTRBASE_0: the reassembled counter block for counter c + 1 (block 1
   at i = 0, staged at sp + 176) as word_reversefields 8
   (ctr_block nonce (c + 1)), so that the Q5 towers of the fill (built on
   the slot reloaded at step 30) and of the invariant (built on the inline
   counter block) agree. *)
let KS9_CTRBASE_0 = mk_cbv `c + 1`;;

(* CTRBASEN: the folds of the reassembled counter blocks for the counters
   c, ..., c + 4 to word_reversefields 8 (ctr_block nonce K) (mk_cbv). *)
let CTRBASEN =
  end_itlist CONJ (map mk_cbv [`c:num`; `c + 1`; `c + 2`; `c + 3`; `c + 4`]);;

(* CBLAST_TAC and CRULE_TAC: WORD_BLAST and WORD_RULE, guarded to goals free of
   the symbolic counter c, on which they blow up (in the fill these are the
   GHASH conjuncts); the counter conjuncts are closed at the level of the
   numeral arithmetic instead. *)
let CBLAST_TAC : tactic = fun (asl,w) ->
  if free_in `c:num` w
    then failwith "CBLAST_TAC: symbolic c present (would explode)"
      else CONV_TAC WORD_BLAST (asl,w);;
let CRULE_TAC : tactic = fun (asl,w) ->
  if free_in `c:num` w then failwith "CRULE_TAC: symbolic c present"
    else CONV_TAC WORD_RULE (asl,w);;
(* Close a counter goal with mismatched numeral indices (word_reversefields,
   ctr_block, aes2c or aes_ctr_block over expressions in c): canonicalize
   0 + c, then REFL_TAC, or peel the function layers down to the numeral
   argument and use ARITH_TAC.  It never blasts, so it is safe on the
   symbolic counter. *)
let CTR_NUM_CLOSE_TAC : tactic =
  REWRITE_TAC[ADD_CLAUSES] THEN
  (REFL_TAC ORELSE
   (REPEAT (AP_TERM_TAC ORELSE AP_THM_TAC) THEN (REFL_TAC ORELSE ARITH_TAC)));;
(* FILL_CLOSE_TAC: the per-conjunct closer of the fill, with one branch per
   shape of conjunct, each closing its goal or failing.  In SWP_DEC_FILL290 it
   runs after the arithmetic normalization of fill290_close, so that the
   conjuncts are in inblock k / literal-offset form, as CLOSE_V8_TAC expects in
   the body; SWP_DEC_FILLLEG and SWP_DEC_LC2_PARTA use it again after their
   branch step.  The GHASH seed Q11 at i = 0 also needs
   nist_ghash .. 0 = tag0 (list_of_seq, nist_ghash). *)
let FILL_CLOSE_TAC : tactic =
  FIRST
   [ (* the counter registers at i = 0 (word_zx / word_or of word c): collapse
        the zx nest, fold word_add, canonicalize 0 + c and close on the
        numerals *)
     (REWRITE_TAC[ZX_COUNTER_UD; ZX_COUNTER_INC; CTR_ZX_NORM] THEN
      REWRITE_TAC[GSYM WORD_ADD] THEN
      REWRITE_TAC[ADD_CLAUSES] THEN CTR_NUM_CLOSE_TAC THEN NO_TAC);
     (* GHASH (the seed Q11 and the partial products): reassembly, the empty
        GHASH, byteswap and the rev64 bridge, then CBLAST_TAC (c is absent) *)
     (REWRITE_TAC[INBLOCK_REASSEMBLE; list_of_seq; nist_ghash] THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[byteswap128] THEN CBLAST_TAC THEN NO_TAC);
     (REWRITE_TAC[INBLOCK_REASSEMBLE; list_of_seq; nist_ghash] THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[REV64_16B_IS_BSW_REVFIELDS; byteswap128] THEN CBLAST_TAC THEN
      NO_TAC);
     (* the counter stack slots (word_join to ctr_block): zx normalization,
        the CTRBASEN folds, then close on the numerals (no blasting) *)
     (ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[ZX_COUNTER_UD; ZX_COUNTER_INC; CTR_ZX_NORM] THEN
      REWRITE_TAC[GSYM WORD_ADD] THEN REWRITE_TAC[ADD_CLAUSES] THEN
      REWRITE_TAC[CTRBASEN; KS9_CTRBASE_0] THEN
      REWRITE_TAC[WORD_REVERSEFIELDS_REVERSEFIELDS] THEN CTR_NUM_CLOSE_TAC THEN
      NO_TAC);
     (* the Q30 and Q5 AES towers to aes2c: merge the reloaded slots, fold
        the counter, aes2c, close on the numerals (no blasting) *)
     ((MERGE_CTR128_TAC 160 "s77" ORELSE ALL_TAC) THEN
      (MERGE_CTR128_TAC 176 "s29" ORELSE ALL_TAC) THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[ZX_COUNTER_UD; ZX_COUNTER_INC; CTR_ZX_NORM] THEN
      REWRITE_TAC[GSYM WORD_ADD] THEN REWRITE_TAC[ADD_CLAUSES] THEN
      REWRITE_TAC[CTRBASEN; KS9_CTRBASE_0] THEN
      REWRITE_TAC[aes2c] THEN CTR_NUM_CLOSE_TAC THEN NO_TAC);
     (* the output stores of blocks 2 and 3: merge the reloaded slots, fold
        the counter, reconstruct the AES tower, aes_ctr_block, close on the
        numerals (no blasting) *)
     ((MERGE_CTR128_TAC 192 "s32" ORELSE ALL_TAC) THEN
      (MERGE_CTR128_TAC 208 "s18" ORELSE ALL_TAC) THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[ZX_COUNTER_UD; ZX_COUNTER_INC; CTR_ZX_NORM] THEN
      REWRITE_TAC[GSYM WORD_ADD] THEN REWRITE_TAC[ADD_CLAUSES] THEN
      REWRITE_TAC[CTRBASEN] THEN
      REWRITE_TAC[XOR_AES128_CIPHER_RECONSTRUCT_DEC] THEN
      REWRITE_TAC[MAP; WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[aes_ctr_block] THEN
      CTR_NUM_CLOSE_TAC THEN NO_TAC);
     (* the loop count (word_sub) *)
     (SUBGOAL_THEN `2 <= loop_count` ASSUME_TAC
      THENL [ASM_ARITH_TAC; ASM_SIMP_TAC[WORD_SUB]] THEN NO_TAC);
     (* the MAYCHANGE frame *)
     (close_goal10 THEN NO_TAC);
     (* the other registers and the htable reads (htable_mem_4 unfolded),
        by ASM_REWRITE_TAC *)
     (ASM_REWRITE_TAC[] THEN TRY REFL_TAC THEN NO_TAC);
     (ASM_REWRITE_TAC[] THEN CRULE_TAC THEN NO_TAC) ];;

(* The merge sites of the fill stepper, one per counter slot: the steps just
   before the fill's counter stores (stp at steps 11, 13, 16 and 22).
   FILL_CLOSE_TAC merges the slots again at the states before their reloads
   (s18, s29, s32 and s77), and fill290_close at the final state s124. *)
let fill_merges = [(10,160);(12,176);(15,208);(21,192)];;

(* SWP_DEC_FILL290, the fill up to its exit test: pc + 0xa0 -> pc + 0x290,
   establishing swp_inv 0 (at pc + 0x290) under 2 <= loop_count.
   SWP_DEC_FILLLEG and SWP_DEC_LC2_PARTA each add the cbz at pc + 0x290
   (not taken and taken respectively). *)

(* Branch resolution for the b.eq at 0xa8, which tests loop_count = 1 and so
   is not taken when loop_count >= 2. *)
let branch_lem_ge2 = prove(
  `2 <= loop_count /\ loop_count < 2 EXP 64
   ==> (val(word_sub (word loop_count:int64) (word 1)) = 0 <=> F)`,
  STRIP_TAC THEN REWRITE_TAC[VAL_EQ_0; WORD_SUB_EQ_0] THEN
  DISCH_THEN(MP_TAC o AP_TERM `val:int64->num`) THEN
  SUBGOAL_THEN `val(word loop_count:int64) = loop_count` SUBST1_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN ASM_REWRITE_TAC[DIMINDEX_64]; ALL_TAC] THEN
  REWRITE_TAC[VAL_WORD_1] THEN UNDISCH_TAC `2 <= loop_count` THEN ARITH_TAC);;

let fill290_hyps = subst [`2 <= loop_count`,`3 <= loop_count`] fill_hyps;;
let fill290_goal =
  leg_goal vs fill290_hyps entry_state (inv_state `0x290` `0`);;

let fill290_step n =
  SWP_STEPS_TAC dec_anchors ctr_slots_all REDSETX_DEC EXEC
    (K (RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `loop_count = 0 <=> F`;
                                    ASSUME `loop_count = 1 <=> F`;
          ASSUME `val(word_sub (word loop_count:int64) (word 1)) = 0 <=> F`;
          COND_CLAUSES])))
    fill_merges (1--n);;

let fill290_prefix =
  REPEAT GEN_TAC THEN INTRO_HYPS_TAC THEN ENSURES_INIT_TAC "s0" THEN
  SUBGOAL_THEN `loop_count < 2 EXP 64` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
    [`nblocks DIV 4 = loop_count`; `16 * nblocks <= 2 EXP 64`] THEN
    ARITH_TAC; ALL_TAC] THEN
  VAL_INT64_TAC `loop_count:num` THEN
  SUBGOAL_THEN `(loop_count = 0 <=> F) /\ (loop_count = 1 <=> F)`
    STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `2 <= loop_count` THEN ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC_ALL branch_lem_ge2) THEN ANTS_TAC THENL
  [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_4]) THEN REWRITE_TAC[htable_mem_4] THEN
  SUBGOAL_THEN
   `read (memory :> bytes128 in_p) s0 = inblock 0 /\
    read (memory :> bytes128 (word_add in_p (word 16))) s0 = inblock 1 /\
    read (memory :> bytes128 (word_add in_p (word 32))) s0 = inblock 2 /\
    read (memory :> bytes128 (word_add in_p (word 48))) s0 = inblock 3`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [SUBST1_TAC(WORD_RULE `in_p:int64 = word_add in_p (word (16*0))`);
      SUBST1_TAC(WORD_RULE
                 `word_add in_p (word 16):int64 = word_add in_p (word (16*1))`);
      SUBST1_TAC(WORD_RULE
                 `word_add in_p (word 32):int64 = word_add in_p (word (16*2))`);
      SUBST1_TAC(WORD_RULE
                 `word_add in_p (word 48):int64 =
                  word_add in_p (word (16*3))`)] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  INPUT_LEG_TAC [`0`; `1`; `2`; `3`];;

let fill290_close =
  ENSURES_FINAL_STATE_TAC THEN
  MERGE_CTR128_TAC 160 "s124" THEN MERGE_CTR128_TAC 176 "s124" THEN
  MERGE_CTR128_TAC 192 "s124" THEN MERGE_CTR128_TAC 208 "s124" THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ARITH_RULE `4 * 0 = 0`; ARITH_RULE `64 * 0 = 0`;
    ARITH_RULE `4 * 0 + 1 = 1`; ARITH_RULE `4 * 0 + 2 = 2`;
    ARITH_RULE `4 * 0 + 3 = 3`;
    ARITH_RULE `4 * 0 + 4 = 4`; ARITH_RULE `4 * 0 + 5 = 5`;
    ARITH_RULE `4 * 0 + 6 = 6`;
    ARITH_RULE `4 * 0 + 7 = 7`; ARITH_RULE `4 * 0 + 9 = 9`;
    ARITH_RULE `0 + 7 = 7`; ARITH_RULE `0 + 3 = 3`;
    ARITH_RULE `64 * 0 + 32 = 32`; ARITH_RULE `64 * 0 + 48 = 48`;
    ARITH_RULE `64 * 0 + 64 = 64`;
    ARITH_RULE `loop_count - 2 - 0 = loop_count - 2`] THEN
  REWRITE_TAC[ARITH_RULE `j < 0 <=> F`] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ADD_CLAUSES] THEN
  REPEAT CONJ_TAC THEN FILL_CLOSE_TAC;;

let SWP_DEC_FILL290 = prove(fill290_goal,
  fill290_prefix THEN fill290_step 124 THEN fill290_close);;

(* The cbz at pc + 0x290 tests X1 in the literal form of swp_inv 0,
   word (loop_count - 2 - 0): not taken for loop_count >= 3, taken for
   loop_count = 2. *)
let fill290_cbz_nt = prove(
  `3 <= loop_count /\ loop_count < 2 EXP 64
   ==> (val(word(loop_count - 2 - 0):int64) = 0 <=> F)`,
  STRIP_TAC THEN
  SUBGOAL_THEN `val(word(loop_count - 2 - 0):int64) = loop_count - 2 - 0`
    SUBST1_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    UNDISCH_TAC `loop_count < 2 EXP 64` THEN ARITH_TAC;
    UNDISCH_TAC `3 <= loop_count` THEN ARITH_TAC]);;
let fill290_cbz_t = prove(
  `loop_count = 2 ==> (val(word(loop_count - 2 - 0):int64) = 0 <=> T)`,
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[ARITH_RULE `2 - 2 - 0 = 0`; VAL_WORD_0]);;

(* SWP_DEC_FILLLEG (pc + 0xa0 -> pc + 0x294, establishing swp_inv 0) is
   SWP_DEC_FILL290 followed by the cbz at pc + 0x290, not taken under
   3 <= loop_count (it falls through and X1 keeps its swp_inv 0 value). *)
let SWP_DEC_FILLLEG = prove(fill_goal,
  REPEAT GEN_TAC THEN INTRO_HYPS_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  ENSURES_SEQUENCE_TAC `pc + 0x290`
    (mk_abs(`s:armstate`, ap swp_inv `0` `s:armstate`)) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    SUBGOAL_THEN `2 <= loop_count` ASSUME_TAC THENL
     [UNDISCH_TAC `3 <= loop_count` THEN ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC SWP_DEC_FILL290 THEN EXISTS_TAC `key_p:int64` THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[GSYM MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    ENSURES_INIT_TAC "s0" THEN
    RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_4]) THEN
    REWRITE_TAC[htable_mem_4] THEN
    SUBGOAL_THEN `loop_count < 2 EXP 64` ASSUME_TAC THENL
     [MAP_EVERY UNDISCH_TAC
      [`nblocks DIV 4 = loop_count`; `16 * nblocks <= 2 EXP 64`] THEN
      ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPEC_ALL fill290_cbz_nt) THEN ANTS_TAC THENL
    [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    SWP_STEP_TAC dec_anchors ctr_slots_all REDSETX_DEC EXEC "s1" THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ASSUME
                                `val(word(loop_count - 2 - 0):int64) = 0 <=> F`;
                               COND_CLAUSES]) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN FILL_CLOSE_TAC]);;

(* SWP_DEC_LC2_PARTA (pc + 0xa0 -> pc + 0x514, loop_count = 2) is
   SWP_DEC_FILL290 followed by the cbz at pc + 0x290, taken into the drain
   (X1 = word 0). *)
let fill_hyps_lc2 = list_mk_conj (base_hyps @ [`loop_count = 2`]);;
let fill_goal_lc2 =
  leg_goal vs fill_hyps_lc2 entry_state (inv_state `0x514` `0`);;

let SWP_DEC_LC2_PARTA = prove(fill_goal_lc2,
  REPEAT GEN_TAC THEN INTRO_HYPS_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  ENSURES_SEQUENCE_TAC `pc + 0x290`
    (mk_abs(`s:armstate`, ap swp_inv `0` `s:armstate`)) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    SUBGOAL_THEN `2 <= loop_count` ASSUME_TAC THENL
     [UNDISCH_TAC `loop_count = 2` THEN ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC SWP_DEC_FILL290 THEN EXISTS_TAC `key_p:int64` THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[GSYM MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    ENSURES_INIT_TAC "s0" THEN
    RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_4]) THEN
    REWRITE_TAC[htable_mem_4] THEN
    MP_TAC(SPEC_ALL fill290_cbz_t) THEN ANTS_TAC THENL
    [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    SWP_STEP_TAC dec_anchors ctr_slots_all REDSETX_DEC EXEC "s1" THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ASSUME
                                `val(word(loop_count - 2 - 0):int64) = 0 <=> T`;
                               COND_CLAUSES]) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN FILL_CLOSE_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The drain: pc + 0x510 -> pc + 0xaa0, from swp_inv (loop_count - 2) to the *)
(* exit state.  It finishes the last two groups, so its stepper also anchors *)
(* the memory facts at the input and output pointers.                        *)
(* ------------------------------------------------------------------------- *)

let drain_hyps = subst [`3 <= loop_count`, `i < loop_count - 2`] leg_hyps;;
let drain_goal =
  leg_goal vs drain_hyps (inv_state `0x510` `loop_count - 2`) exit_state;;

(* SWP_DEC_DRAIN514, the drain after the loop's exit test: pc + 0x514 ->
   pc + 0xaa0 under 2 <= loop_count, used by SWP_DEC_DRAINLEG and by the
   case loop_count = 2.  drain_hyps keeps 3 <= loop_count for the
   SWP_DEC_DRAINLEG leaf goal; drain514_hyps weakens it to 2 <= loop_count. *)
let drain514_pre = inv_state `0x514` `loop_count - 2`;;
let drain514_hyps = subst [`2 <= loop_count`, `3 <= loop_count`] drain_hyps;;
let drain514_goal = leg_goal vs drain514_hyps drain514_pre exit_state;;

(* The drain stepper: steps 1..197 (pc + 0x514 .. pc + 0x824), with the
   counter-slot merges just before the loads from the slots (steps 18, 43
   and 49).  Step 97 (pc + 0x694) is the final ext v30 of the first
   reduction: the tag after group loop_count - 2 is abbreviated there to
   inter, so that the second reduction and the later references use the
   abbreviation instead of the whole tower. *)
let drain_merges = [(17,208);(42,176);(48,192)];;
let drain_step_tac =
  SWP_STEPS_TAC dec_anchors_io ctr_slots_all REDSETX_DEC EXEC
    (fun k -> RULE_ASSUM_TAC(REWRITE_RULE[COND_CLAUSES]) THEN
              (if k = 97
               then REABBREV_TAC (mk_eq(`inter:int128`, `read Q30 s97`))
                 else ALL_TAC))
    drain_merges (1--197);;

let rhs_has c w = try (is_eq w) &&
  can (find_term
       (fun u -> try fst(dest_const(fst(strip_comb u)))=c with _->false))
         (rhs w) with _->false;;

(* GHASH_SETTLE_TAC ktm off: the drain's GHASH closer for one group.  ktm is
   the group index (accumulator nist_ghash .. (4 * ktm); branch 2 uses
   SWP_GHASH_BRANCH2_SETTLED ktm); off is 0 for subgoal B (blocks
   4 * (loop_count - 2) + 0..3) and 4 for subgoal A (blocks
   4 * (loop_count - 2) + 4..7).  The block abbreviations use the goal's
   index 4 * (loop_count - 2) + (off + j), which an arithmetic step before
   branch 2 rewrites to the base 4 * ktm of the lemma. *)
let GHASH_SETTLE_TAC (ktm:term) (off:int) : tactic =
  let mtm = mk_binop `( * ):num->num->num` `4` ktm in
  let basetm = `4 * (loop_count - 2)` in
  let blkidx j = if off+j = 0 then basetm
                 else mk_binop `(+):num->num->num` basetm
                   (mk_small_numeral (off+j)) in
  DEC_GHASH_NORM_TAC THEN GHASH_SPLIT_TAC THEN
  GHASH_GROUP_TAC
    (INFOLD3_TAC THEN REWRITE_TAC[INBLOCK_REASSEMBLE] THEN
     REWRITE_TAC[GSYM nist_input_block] THEN ASM_REWRITE_TAC[])
    (subst [ktm, `k:num`]
     `nist_ghash (aes128_cipher (word 0) rk) tag0
      (list_of_seq (nist_input_block inblock) (4*k))`)
    (fun j -> mk_comb(`nist_input_block inblock`, blkidx j))
    ((if off = 0 then ALL_TAC else
        SUBGOAL_THEN
          (list_mk_conj (map (fun j ->
             mk_eq(mk_binop `(+):num->num->num` `4*(loop_count-2)`
                   (mk_small_numeral (off+j)),
                   if j = 0 then mtm
                     else mk_binop `(+):num->num->num` mtm
                       (mk_small_numeral j)))
           [0;1;2;3]))
          (fun th -> REWRITE_TAC[th]) THENL
         [UNDISCH_TAC `2 <= loop_count` THEN ARITH_TAC; ALL_TAC]) THEN
     MP_TAC(ISPEC ktm SWP_GHASH_BRANCH2_SETTLED) THEN
     REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]));;

(* DRAIN_Q30_TAC: the Q30 conjunct, split into two single-group goals.  inter
   was abbreviated at step 97 (the tag after the first reduction); subgoal B
   proves inter = byteswap128 (nist_ghash .. (4 * (loop_count - 1))), and
   subgoal A the final reduction over it. *)
let DRAIN_Q30_TAC : tactic =
  SUBGOAL_THEN `inter = byteswap128 (nist_ghash (aes128_cipher (word 0) rk) tag0
                        (list_of_seq (nist_input_block inblock)
                         (4 * (loop_count - 1))))`
    ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th ->
                  if (try is_eq(concl th) && rhs(concl th) = `inter:int128`
                                 with _ -> false) then MP_TAC th
                                   else NO_TAC) THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    SUBGOAL_THEN `4 * (loop_count - 1) = 4 * (loop_count - 2) + 4`
      SUBST1_TAC THENL
     [UNDISCH_TAC `2 <= loop_count` THEN ARITH_TAC; ALL_TAC] THEN
    GHASH_SETTLE_TAC `loop_count - 2` 0;
    ALL_TAC] THEN
  FIRST_X_ASSUM(fun th ->
                if (try is_eq(concl th) && lhs(concl th) = `inter:int128` &&
                                 can(find_term(fun u->try
                                               fst(dest_const(fst(strip_comb
                                                   u)))="nist_ghash" with
                                                     _->false))(rhs(concl th))
                               with _ -> false) then SUBST1_TAC th
                                 else NO_TAC) THEN
  SUBGOAL_THEN `4 * loop_count = 4 * (loop_count - 1) + 4` SUBST1_TAC THENL
   [UNDISCH_TAC `2 <= loop_count` THEN ARITH_TAC; ALL_TAC] THEN
  GHASH_SETTLE_TAC `loop_count - 1` 4;;

(* DRAIN_CLOSE_TAC: the per-conjunct closer of the drain, by the shape of the
   conjunct. *)
let DRAIN_CLOSE_TAC : tactic =
  fun (asl,w) ->
    (if not(is_eq w) then
       (FIRST[close_goal10; MUST_PROGRESS OUT0_TAC;
              ASM_REWRITE_TAC[] THEN NO_TAC]) (asl,w)
     else if rhs_has "nist_ghash" w then
       (FIRST[ (ASM_REWRITE_TAC[] THEN REFL_TAC THEN NO_TAC);
               (DRAIN_Q30_TAC THEN NO_TAC) ]) (asl,w)
     else if rhs_has "aes_ctr_block" w then
       (* output-store readback.  RECON handles both the aes2c base (first
          group) and the counter blocks staged on the stack, with the
          counter-block reconstruction (CTR_BLOCK_BUILD_INSERT) and the
          round-key list fold (ASM_REWRITE_TAC).  Blocks
          4 * (loop_count - 2) + 5, 6 and 7 first normalize the address of
          their store fact (ADDRNORM).  Every alternative ends with
          NO_TAC. *)
       (let RECON =
          REWRITE_TAC[aes2c] THEN
          REWRITE_TAC[XOR_AES128_CIPHER_RECONSTRUCT_DEC] THEN
          REWRITE_TAC[WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
          REWRITE_TAC[MAP] THEN
          REWRITE_TAC[WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
          REWRITE_TAC[ZX_COUNTER_UD; ZX_COUNTER_INC; CTR_ZX_NORM] THEN
          CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
          REWRITE_TAC[GSYM WORD_ADD] THEN
          REWRITE_TAC[ARITH_RULE `(4*(loop_count-2)+4)+2 = 4*(loop_count-2)+6`;
                      ARITH_RULE `(4*(loop_count-2)+5)+2 = 4*(loop_count-2)+7`;
                      ARITH_RULE `(4*(loop_count-2)+6)+2 = 4*(loop_count-2)+8`;
                      ARITH_RULE
                        `(4*(loop_count-2)+7)+2 = 4*(loop_count-2)+9`] THEN
          REWRITE_TAC[CTR_BLOCK_BUILD_INSERT] THEN
          REWRITE_TAC[aes_ctr_block] THEN
          REWRITE_TAC[GSYM ADD_ASSOC] THEN
          CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN
          REWRITE_TAC[WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
          ASM_REWRITE_TAC[] in
        let ADDRNORM =
          REWRITE_TAC[ARITH_RULE
                      `64*(loop_count-2)+80 = (64*(loop_count-2)+64)+16`;
                             ARITH_RULE
                               `64*(loop_count-2)+96 =
                                (64*(loop_count-2)+64)+32`;
                             ARITH_RULE
                               `64*(loop_count-2)+112 =
                                (64*(loop_count-2)+64)+48`] in
        FIRST[ (ASM_REWRITE_TAC[] THEN NO_TAC);
               (RECON THEN NO_TAC);
               (RECON THEN CTR_NUM_CLOSE_TAC THEN NO_TAC);
               (CLOSE_V8_TAC THEN NO_TAC);
               ((ADDRNORM THEN ASM_REWRITE_TAC[] THEN RECON) THEN NO_TAC);
               ((ADDRNORM THEN ASM_REWRITE_TAC[] THEN RECON THEN
                 CTR_NUM_CLOSE_TAC) THEN NO_TAC);
               ((ADDRNORM THEN ASM_REWRITE_TAC[] THEN CLOSE_V8_TAC) THEN
                NO_TAC);
               ((ADDRNORM THEN ASM_REWRITE_TAC[] THEN
                 REWRITE_TAC[dewrap80; dewrap96; dewrap112] THEN
                 REWRITE_TAC[ARITH_RULE `16 * (4 * a + b) = 64 * a + 16 * b`]
                   THEN CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN
                 ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[WORD_XOR_SYM] THEN
                 RECON THEN TRY CTR_NUM_CLOSE_TAC) THEN NO_TAC);
               ((ADDRNORM THEN ASM_REWRITE_TAC[] THEN INFOLD3_TAC THEN RECON)
                THEN NO_TAC);
               ((ADDRNORM THEN ASM_REWRITE_TAC[] THEN
                 ONCE_REWRITE_TAC[WORD_XOR_SYM] THEN
                 INFOLD3_TAC THEN ASM_REWRITE_TAC[] THEN RECON THEN
                 TRY CTR_NUM_CLOSE_TAC) THEN NO_TAC);
               ((ADDRNORM THEN ASM_REWRITE_TAC[] THEN INFOLD3_TAC THEN
                 ASM_REWRITE_TAC[] THEN
                 ONCE_REWRITE_TAC[WORD_XOR_SYM] THEN RECON THEN
                 TRY CTR_NUM_CLOSE_TAC) THEN NO_TAC);
               ((ADDRNORM THEN ASM_REWRITE_TAC[] THEN AES2C_OUT_TAC) THEN
                NO_TAC);
               ((ADDRNORM THEN ASM_REWRITE_TAC[] THEN
                 REWRITE_TAC[dewrap80; dewrap96; dewrap112] THEN
                 REWRITE_TAC[ARITH_RULE `16 * (4 * a + b) = 64 * a + 16 * b`]
                   THEN CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN
                 ASM_REWRITE_TAC[] THEN
                 REWRITE_TAC[XOR_AES128_CIPHER_RECONSTRUCT_DEC] THEN
                 REWRITE_TAC[MAP; WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
                 ASM_REWRITE_TAC[] THEN
                 REWRITE_TAC[ZX_COUNTER_UD; ZX_COUNTER_INC; CTR_ZX_NORM] THEN
                 CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
                 REWRITE_TAC[GSYM WORD_ADD] THEN
                 REWRITE_TAC[CTR_BLOCK_BUILD_INSERT] THEN
                 REWRITE_TAC[WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
                 REWRITE_TAC[ARITH_RULE
                             `4 * (loop_count - 2) + c + 4 =
                              (4 * (loop_count - 2) + 4) + c`;
                             ARITH_RULE
                               `4 * (loop_count - 2) + c + 5 =
                                (4 * (loop_count - 2) + 5) + c`;
                             ARITH_RULE
                               `4 * (loop_count - 2) + c + 6 =
                                (4 * (loop_count - 2) + 6) + c`;
                             ARITH_RULE
                               `4 * (loop_count - 2) + c + 7 =
                                (4 * (loop_count - 2) + 7) + c`;
                             ARITH_RULE
                               `((4 * (loop_count - 2) + 4) + c) + 2 =
                                (4 * (loop_count - 2) + 6) + c`;
                             ARITH_RULE
                               `((4 * (loop_count - 2) + 5) + c) + 2 =
                                (4 * (loop_count - 2) + 7) + c`] THEN
                 REWRITE_TAC[GSYM aes_ctr_block] THEN ASM_REWRITE_TAC[] THEN
                 ONCE_REWRITE_TAC[WORD_XOR_SYM] THEN ASM_REWRITE_TAC[] THEN
                 TRY REFL_TAC) THEN NO_TAC) ]) (asl,w)
     else if (try fst(dest_const(fst(strip_comb(lhs w))))="word_zx" with
              _->false) then
       (* the X13 counter conjunct,
          word_zx (word_add (word_zx (word_zx (word K))) (word 4)) =
          word_zx (word (4 * loop_count + c)) *)
       (REWRITE_TAC[ZX_COUNTER_UD; ZX_COUNTER_INC; CTR_ZX_NORM] THEN
        REWRITE_TAC[GSYM WORD_ADD] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
        ASM_ARITH_TAC) (asl,w)
     else
       (FIRST[ (ASM_REWRITE_TAC[] THEN TRY REFL_TAC THEN NO_TAC);
               (AP_TERM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC THEN NO_TAC);
               (ASM_REWRITE_TAC[] THEN REWRITE_TAC[ctr_block] THEN
                CONV_TAC NUM_REDUCE_CONV THEN CBLAST_TAC THEN NO_TAC);
               (CRULE_TAC THEN NO_TAC);
               (CLOSE_V8_TAC THEN NO_TAC) ]) (asl,w));;

let SWP_DEC_DRAIN514 = prove(drain514_goal,
  REPEAT GEN_TAC THEN INTRO_HYPS_TAC THEN ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE
                              `loop_count - 2 - (loop_count - 2) = 0`]) THEN
  (* Prime the four input-block reads of the last group to inblock form:
     otherwise the loads reach the GHASH closer as raw byte-reassembly
     towers, on which the BITBLAST of branch 1 blows up. *)
  SUBGOAL_THEN `4*(loop_count-2)+7 < nblocks` ASSUME_TAC THENL
   [MP_TAC(SPECL [`nblocks:num`;`4`] DIVISION) THEN
    UNDISCH_TAC `2 <= loop_count` THEN
    SUBST1_TAC(SYM(ASSUME `nblocks DIV 4 = loop_count`)) THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `read (memory :> bytes128 (word_add in_p (word (64*(loop_count-2)+64)))) s0 =
    inblock (4*(loop_count-2)+4) /\
    read (memory :> bytes128 (word_add in_p (word (64*(loop_count-2)+80)))) s0 =
      inblock (4*(loop_count-2)+5) /\
    read (memory :> bytes128 (word_add in_p (word (64*(loop_count-2)+96)))) s0 =
      inblock (4*(loop_count-2)+6) /\
    read (memory :> bytes128 (word_add in_p (word (64*(loop_count-2)+112)))) s0
      = inblock (4*(loop_count-2)+7)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [SUBST1_TAC(WORD_RULE
                 `word_add in_p (word (64*(loop_count-2)+64)):int64 =
                  word_add in_p (word (16*(4*(loop_count-2)+4)))`);
      SUBST1_TAC(WORD_RULE
                 `word_add in_p (word (64*(loop_count-2)+80)):int64 =
                  word_add in_p (word (16*(4*(loop_count-2)+5)))`);
      SUBST1_TAC(WORD_RULE
                 `word_add in_p (word (64*(loop_count-2)+96)):int64 =
                  word_add in_p (word (16*(4*(loop_count-2)+6)))`);
      SUBST1_TAC(WORD_RULE
                 `word_add in_p (word (64*(loop_count-2)+112)):int64 =
                  word_add in_p (word (16*(4*(loop_count-2)+7)))`)] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  INPUT_LEG_TAC
    [`4*(loop_count-2)+4`; `4*(loop_count-2)+5`; `4*(loop_count-2)+6`;
     `4*(loop_count-2)+7`] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_4]) THEN REWRITE_TAC[htable_mem_4] THEN
  drain_step_tac THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `64 * (loop_count - 2) + 128 = 64 * loop_count /\
                (64 * (loop_count - 2) + 64) + 64 = 64 * loop_count`
    (fun th -> REWRITE_TAC[th]) THENL
   [MAP_EVERY UNDISCH_TAC [`2 <= loop_count`] THEN ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  (* Split the output forall of the postcondition (j < 4 * loop_count) into
     the prefix j < 4 * (loop_count - 2), preserved from the invariant, and
     the eight blocks of the last two groups, as explicit equations. *)
  SUBGOAL_THEN `!j:num. j < 4 * loop_count <=>
      j < 4*(loop_count-2) \/ j = 4*(loop_count-2) \/ j = 4*(loop_count-2)+1 \/
      j = 4*(loop_count-2)+2 \/
      j = 4*(loop_count-2)+3 \/ j = 4*(loop_count-2)+4 \/
      j = 4*(loop_count-2)+5 \/ j = 4*(loop_count-2)+6 \/
      j = 4*(loop_count-2)+7`
    (fun th -> REWRITE_TAC[th]) THENL
   [UNDISCH_TAC `2 <= loop_count` THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[TAUT `p \/ q ==> r <=> (p ==> r) /\ (q ==> r)`] THEN
  REWRITE_TAC[FORALL_AND_THM; FORALL_UNWIND_THM2] THEN
  REWRITE_TAC[ARITH_RULE `16 * (4 * a + b) = 64 * a + 16 * b`;
              ARITH_RULE `16 * 4 * a = 64 * a`] THEN
  CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN DRAIN_CLOSE_TAC);;

(* The cbnz at pc + 0x510 after the last iteration:
   X1 = word (loop_count - 2 - (loop_count - 2)) = word 0, so the branch is
   not taken. *)
let drain_cbnz_guard = prove(
  `val(word(loop_count - 2 - (loop_count - 2)):int64) = 0 <=> T`,
  REWRITE_TAC[ARITH_RULE `loop_count - 2 - (loop_count - 2) = 0`; VAL_WORD_0]);;

(* SWP_DEC_DRAINLEG (pc + 0x510 -> pc + 0xaa0, under 3 <= loop_count) is the
   cbnz at pc + 0x510, not taken (X1 = word 0; it falls through, keeping
   swp_inv (loop_count - 2)), followed by SWP_DEC_DRAIN514. *)
let SWP_DEC_DRAINLEG = prove(drain_goal,
  REPEAT GEN_TAC THEN INTRO_HYPS_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  ENSURES_SEQUENCE_TAC `pc + 0x514`
    (mk_abs(`s:armstate`, ap swp_inv `loop_count - 2` `s:armstate`)) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    ENSURES_INIT_TAC "s0" THEN
    RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_4]) THEN
    REWRITE_TAC[htable_mem_4] THEN
    MP_TAC drain_cbnz_guard THEN DISCH_TAC THEN
    SWP_STEP_TAC dec_anchors_io ctr_slots_all REDSETX_DEC EXEC "s1" THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ASSUME
                                `val(word(loop_count - 2 -
                                          (loop_count - 2)):int64) = 0 <=> T`;
                               NOT_CLAUSES; COND_CLAUSES]) THEN
    ENSURES_FINAL_STATE_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE
                                `loop_count - 2 - (loop_count - 2) = 0`]) THEN
    REWRITE_TAC[ARITH_RULE `loop_count - 2 - (loop_count - 2) = 0`] THEN
    ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN
    FIRST [close_goal10; (ASM_REWRITE_TAC[] THEN TRY REFL_TAC THEN NO_TAC);
           (AP_TERM_TAC THEN ARITH_TAC)];
    REWRITE_TAC[GSYM MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    SUBGOAL_THEN `2 <= loop_count` ASSUME_TAC THENL
     [UNDISCH_TAC `3 <= loop_count` THEN ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC SWP_DEC_DRAIN514 THEN EXISTS_TAC `key_p:int64` THEN
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The single-group path iter_1 (loop_count = 1): SWP_DEC_ITER1,             *)
(* pc + 0xa0 -> pc + 0xaa0.  The b.eq at pc + 0xa8 branches to pc + 0x828,   *)
(* and iter_1 (pc + 0x828 .. pc + 0xa9c) decrypts and hashes the four blocks *)
(* and falls into pc + 0xaa0.                                                *)
(* ------------------------------------------------------------------------- *)

let iter1_hyps = list_mk_conj (base_hyps @ [`loop_count = 1`]);;
let iter1_goal = leg_goal vs iter1_hyps entry_state exit_state;;

(* The iter_1 stepper: the three control-flow steps (cbz, cmp, b.eq), then
   the 158 instructions of iter_1 as steps 4..161.  Each counter slot is
   merged after its store stp x11,xN,[sp,#OFF]: steps 16 (sp + 208), 23
   (sp + 176), 27 (sp + 160) and 32 (sp + 192), i.e. iter_1 instructions 13,
   20, 24 and 29. *)
let iter1_merges = [(16,208);(23,176);(27,160);(32,192)];;
let iter1_step_tac =
  SWP_STEPS_TAC dec_anchors_io ctr_slots_all REDSETX_DEC EXEC
    (K (RULE_ASSUM_TAC(REWRITE_RULE[COND_CLAUSES]))) iter1_merges (1--161);;

(* ITER1_Q30_TAC: the GHASH closer for the single group: accumulator
   tag0 = nist_ghash .. 0, blocks 0..3, result nist_ghash .. 4.  The input
   reads were primed to inblock j at s0, so the fold may find nothing (hence
   TRY).  SWP_GHASH_BRANCH2_SETTLED at k = 0 has nist_ghash .. (4 * 0) where
   the goal has tag0, so nist_ghash .. 0 = tag0 is proved and folded into the
   lemma (after NUM_REDUCE_CONV). *)
let ITER1_Q30_TAC : tactic =
  DEC_GHASH_NORM_TAC THEN GHASH_SPLIT_TAC THEN
  GHASH_GROUP_TAC
    (TRY INFOLD3_TAC THEN REWRITE_TAC[INBLOCK_REASSEMBLE] THEN
     REWRITE_TAC[GSYM nist_input_block] THEN ASM_REWRITE_TAC[])
    `tag0:int128`
    (fun j -> mk_comb(`nist_input_block inblock`, mk_small_numeral j))
    (MP_TAC(REWRITE_RULE
             [prove(`nist_ghash (aes128_cipher (word 0) rk) tag0
                     (list_of_seq (nist_input_block inblock) 0) = tag0`,
                    REWRITE_TAC[list_of_seq; nist_ghash])]
             (CONV_RULE NUM_REDUCE_CONV
              (ISPEC `0` SWP_GHASH_BRANCH2_SETTLED))) THEN
     DISCH_THEN(fun th -> REWRITE_TAC[th]));;

(* ITER1_CLOSE_TAC: the per-conjunct closer of iter_1 (blocks 0..3; the counter
   base is X13 = word c, so the counters are c..c+3), with the shape
   dispatch of DRAIN_CLOSE_TAC but literal block indices. *)
let ITER1_CLOSE_TAC : tactic =
  fun (asl,w) ->
    (if not(is_eq w) then
       (FIRST[close_goal10; MUST_PROGRESS OUT0_TAC;
              ASM_REWRITE_TAC[] THEN NO_TAC]) (asl,w)
     else if rhs_has "nist_ghash" w then
       (* the Q30 conjunct read Q30 s = byteswap128 (nist_ghash .. 4):
          substitute only the s161 fact about Q30 (not a full
          ASM_REWRITE_TAC over the large assumption list), discard all the
          read facts (ITER1_Q30_TAC needs only the round-key list equation
          and arithmetic), then run the GHASH closer *)
       (FIRST_X_ASSUM(fun th -> try
           (match lhs(concl th) with
            | Comb(Comb(Const("read",_),Const("Q30",_)),_) -> SUBST1_TAC th
            | _ -> failwith "") with _ -> NO_TAC) THEN
        DISCARD_ASSUMPTIONS_TAC
          (fun th ->
           try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "read" with _
             -> false) THEN
        ITER1_Q30_TAC THEN NO_TAC) (asl,w)
     else if rhs_has "aes_ctr_block" w then
       (* the output-store readback for block j.  Once the store value is
          substituted (ADDRNORM, ASM_REWRITE_TAC) the goal is
            word_xor (inblock j) (word_xor rk10 tower) =
            word_xor (aes_ctr_block aes128_cipher c nonce rk j) (inblock j);
          FOLD turns the tower into the cipher of its counter block
          (XOR_AES128_CIPHER_RECONSTRUCT_DEC and the round-key list) and
          unfolds aes_ctr_block on the right. *)
       (let ADDRNORM =
        GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [WORD_ADD_0] in
        let FOLD =
          REWRITE_TAC[XOR_AES128_CIPHER_RECONSTRUCT_DEC] THEN
          REWRITE_TAC[MAP] THEN
          REWRITE_TAC[WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
          ASM_REWRITE_TAC[] THEN
          REWRITE_TAC[aes_ctr_block] in
        (* After FOLD both sides have the form
           word_xor (word_reversefields 8 (aes128_cipher CTR rk)) (inblock j).
           PEEL_CTR peels them, in a fixed number of steps, down to an
           equation between the counter blocks:
             word_xor A (inblock j) = word_xor A' (inblock j)  to  A = A',
             word_reversefields 8 X = word_reversefields 8 X'  to  X = X',
             aes128_cipher CTR rk = aes128_cipher CTR' rk  to  CTR = CTR'.
           (A REPEAT would peel into the counter blocks themselves, and the
           blast that follows would blow up.)  The counter blocks then
           agree by REFL_TAC after WORD_REVERSEFIELDS_REVERSEFIELDS, by the
           folds CTRBASEN and KS9_CTRBASE_0 and CTR_NUM_CLOSE_TAC, or, failing
           those, by unfolding ctr_block and CBLAST_TAC. *)
        let PEEL_CTR =
          AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN
          AP_TERM_TAC THEN
          REWRITE_TAC[WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
          (REFL_TAC ORELSE
           (REWRITE_TAC[CTRBASEN; KS9_CTRBASE_0] THEN
            REWRITE_TAC[WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
            (REFL_TAC ORELSE CTR_NUM_CLOSE_TAC)) ORELSE
           (REWRITE_TAC[ctr_block] THEN CONV_TAC NUM_REDUCE_CONV THEN
            CBLAST_TAC)) in
        FIRST[ (ADDRNORM THEN ASM_REWRITE_TAC[] THEN FOLD THEN PEEL_CTR THEN
                NO_TAC);
               (ASM_REWRITE_TAC[] THEN FOLD THEN PEEL_CTR THEN NO_TAC);
               (ADDRNORM THEN ASM_REWRITE_TAC[] THEN REWRITE_TAC[aes2c] THEN
                FOLD THEN PEEL_CTR THEN NO_TAC);
               (ADDRNORM THEN ASM_REWRITE_TAC[] THEN AES2C_OUT_TAC THEN NO_TAC);
               (TRY ADDRNORM THEN ASM_REWRITE_TAC[] THEN
                REWRITE_TAC[XOR_AES128_CIPHER_RECONSTRUCT_DEC] THEN
                REWRITE_TAC[MAP; WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
                ASM_REWRITE_TAC[] THEN
                REWRITE_TAC[ZX_COUNTER_UD; ZX_COUNTER_INC; CTR_ZX_NORM] THEN
                CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
                REWRITE_TAC[GSYM WORD_ADD] THEN
                REWRITE_TAC[CTR_BLOCK_BUILD_INSERT] THEN
                REWRITE_TAC[WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
                REWRITE_TAC[ARITH_RULE `c + 1 = 1 + c`;
                            ARITH_RULE `c + 2 = 2 + c`;
                            ARITH_RULE `c + 3 = 3 + c`;
                            ARITH_RULE `0 + c = c`] THEN
                REWRITE_TAC[GSYM aes_ctr_block] THEN ASM_REWRITE_TAC[] THEN
                ONCE_REWRITE_TAC[WORD_XOR_SYM] THEN ASM_REWRITE_TAC[] THEN
                TRY REFL_TAC THEN NO_TAC);
               (* block 0 (base counter c): unfold aes_ctr_block on the
                  right, canonicalize 0 + c, collapse the double
                  word_reversefields 8 and commute *)
               (TRY ADDRNORM THEN ASM_REWRITE_TAC[] THEN
                REWRITE_TAC[XOR_AES128_CIPHER_RECONSTRUCT_DEC] THEN
                REWRITE_TAC[MAP; WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
                ASM_REWRITE_TAC[] THEN
                REWRITE_TAC[ZX_COUNTER_UD; ZX_COUNTER_INC; CTR_ZX_NORM] THEN
                REWRITE_TAC[CTR_BLOCK_BUILD_INSERT] THEN
                REWRITE_TAC[WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
                REWRITE_TAC[aes_ctr_block] THEN REWRITE_TAC[ADD_CLAUSES] THEN
                REWRITE_TAC[WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
                ASM_REWRITE_TAC[] THEN
                (REFL_TAC ORELSE MATCH_ACCEPT_TAC WORD_XOR_SYM) THEN NO_TAC);
               (ASM_REWRITE_TAC[] THEN NO_TAC) ]) (asl,w)
     else if (try can
              (find_term
               (fun u ->
                try fst(dest_const(fst(strip_comb u)))="word_zx" with _->false))
                  w with _->false) then
       (* the X13 counter conjunct (word_zx (word (4 * 1 + c)) at
          loop_count = 1): normalize the zx nest and the numeral
          arithmetic; CBLAST_TAC is the fallback for goals without c *)
       (FIRST[ (REWRITE_TAC[ZX_COUNTER_UD; ZX_COUNTER_INC; CTR_ZX_NORM] THEN
                REWRITE_TAC[GSYM WORD_ADD] THEN TRY AP_TERM_TAC THEN
                TRY AP_TERM_TAC THEN
                CONV_TAC NUM_REDUCE_CONV THEN (REFL_TAC ORELSE ARITH_TAC) THEN
                NO_TAC);
               (CONV_TAC NUM_REDUCE_CONV THEN CBLAST_TAC THEN NO_TAC) ]) (asl,w)
     else
       (* register conjuncts (mostly read Qn s = word_reversefields 8
          (EL k rk)): ASM_REWRITE_TAC and REFL_TAC from the s161 facts left
          by the pruning; the X0 and X2 pointer conjuncts need a WORD_RULE
          step (CRULE_TAC) for 64 * 1 = 64 *)
       (FIRST[ (ASM_REWRITE_TAC[] THEN REFL_TAC THEN NO_TAC);
               (ASM_REWRITE_TAC[] THEN
                REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES] THEN CRULE_TAC THEN
                NO_TAC) ]) (asl,w));;

let MAYCHANGE_ABI_CLOSE_TAC =
  FIRST_X_ASSUM(fun th -> if maychange_term(concl th) then
     MATCH_MP_TAC(MATCH_MP SUBSUMED_APPLY th) else NO_TAC) THEN
   REWRITE_TAC[ETA_AX] THEN
   REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
   SUBSUMED_MAYCHANGE_TAC;;

(* The per-conjunct closer of iter_1: the frame goals by
   MAYCHANGE_ABI_CLOSE_TAC, everything else by ITER1_CLOSE_TAC. *)
let ITER1_CLOSE_ALL_TAC : tactic =
  fun (asl,w) ->
    (if maychange_term w then MAYCHANGE_ABI_CLOSE_TAC else ITER1_CLOSE_TAC)
      (asl,w);;

let SWP_DEC_ITER1 = prove(iter1_goal,
  REPEAT GEN_TAC THEN INTRO_HYPS_TAC THEN
  REPEAT(FIRST_X_ASSUM
         (SUBST_ALL_TAC o check
          (fun th -> try lhs(concl th) = `loop_count:num` with _->false))) THEN
  ENSURES_INIT_TAC "s0" THEN
  (* Prime the four input-block reads to inblock form, as in the drain:
     otherwise the loads reach the GHASH closer and the output-store
     readbacks as raw byte-reassembly towers, on which BITBLAST blows up. *)
  SUBGOAL_THEN `3 < nblocks` ASSUME_TAC THENL
   [MP_TAC(SPECL [`nblocks:num`;`4`] DIVISION) THEN
    UNDISCH_TAC `nblocks DIV 4 = 1` THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `read (memory :> bytes128 in_p) s0 = inblock 0 /\
    read (memory :> bytes128 (word_add in_p (word 16))) s0 = inblock 1 /\
    read (memory :> bytes128 (word_add in_p (word 32))) s0 = inblock 2 /\
    read (memory :> bytes128 (word_add in_p (word 48))) s0 = inblock 3`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [SUBST1_TAC(WORD_RULE `in_p:int64 = word_add in_p (word (16*0))`);
      SUBST1_TAC(WORD_RULE
                 `word_add in_p (word 16):int64 = word_add in_p (word (16*1))`);
      SUBST1_TAC(WORD_RULE
                 `word_add in_p (word 32):int64 = word_add in_p (word (16*2))`);
      SUBST1_TAC(WORD_RULE
                 `word_add in_p (word 48):int64 =
                  word_add in_p (word (16*3))`)] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  INPUT_LEG_TAC [`0`; `1`; `2`; `3`] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_4]) THEN REWRITE_TAC[htable_mem_4] THEN
  iter1_step_tac THEN
  ENSURES_FINAL_STATE_TAC THEN
  (* Prune the assumptions before the closers: the stepping leaves register
     reads of intermediate states with large right-hand sides (GHASH
     partial products), which slow down every ASM_REWRITE_TAC and WORD_RULE
     of the closers.  Discard the register reads of states other than s161
     whose right-hand side has more than 60 term nodes (counted by tsize);
     the final s161 register values and all the memory facts (the output,
     input, tag and IV cells the reconstruction needs) are kept. *)
  (let rec tsize n t = if n > 60 then n else
     match t with Comb(a,b) -> tsize (tsize (n+1) a) b | Abs(_,b) ->
       tsize (n+1) b | _ -> n+1 in
   DISCARD_ASSUMPTIONS_TAC
    (fun th -> try let c = concl th in is_eq c &&
       (match lhs c with Comb(Comb(Const("read",_),comp),st) ->
          (* memory reads (out_p/in_p/tag/ivec/mem): keep *)
          (match comp with Comb(Const(":>",_),_) -> false
                         | _ ->
             (* register read: drop it if it is about a state other than
                s161 and has a large right-hand side; tsize stops counting
                at 60 nodes, which keeps the test cheap on large towers *)
             tsize 0 (rhs c) > 60 &&
             (match st with Var(nm,_) -> nm <> "s161" | _ -> true))
        | _ -> false)
     with _ -> false)) THEN
  ASM_REWRITE_TAC[] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES] THEN
  REWRITE_TAC[ARITH_RULE `j < 4 <=> j = 0 \/ j = 1 \/ j = 2 \/ j = 3`] THEN
  REWRITE_TAC[TAUT `p \/ q ==> r <=> (p ==> r) /\ (q ==> r)`] THEN
  REWRITE_TAC[FORALL_AND_THM; FORALL_UNWIND_THM2] THEN
  CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN ITER1_CLOSE_ALL_TAC);;

(* ------------------------------------------------------------------------- *)
(* loop_count = 2: SWP_DEC_LC2 is SWP_DEC_LC2_PARTA                          *)
(* (pc + 0xa0 -> pc + 0x514) followed by SWP_DEC_DRAIN514                    *)
(* (pc + 0x514 -> pc + 0xaa0).                                               *)
(* ------------------------------------------------------------------------- *)
let lc2_goal = leg_goal vs fill_hyps_lc2 entry_state exit_state;;
let SWP_DEC_LC2 = prove(lc2_goal,
  REPEAT GEN_TAC THEN INTRO_HYPS_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  ENSURES_SEQUENCE_TAC `pc + 0x514`
    (mk_abs(`s:armstate`, ap swp_inv `0` `s:armstate`)) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    MATCH_MP_TAC SWP_DEC_LC2_PARTA THEN EXISTS_TAC `key_p:int64` THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[GSYM MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    ENSURES_PRECONDITION_TAC drain514_pre THEN CONJ_TAC THENL
     [GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
      FIRST_ASSUM(fun th -> if lhs(concl th)=`loop_count:num`
                  then REWRITE_TAC[th] else NO_TAC) THEN
      CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];
      MATCH_MP_TAC SWP_DEC_DRAIN514 THEN EXISTS_TAC `key_p:int64` THEN
      REPEAT CONJ_TAC THEN TRY(FIRST_X_ASSUM ACCEPT_TAC) THEN
      TRY(ASM_REWRITE_TAC[] THEN NO_TAC) THEN
      (UNDISCH_TAC `loop_count = 2` THEN ARITH_TAC)]]);;

(* ------------------------------------------------------------------------- *)
(* Leaf tactics for the seven leaf goals of the main theorem: the five leg   *)
(* lemmas (applied by APPLY_LEG_TAC) and the inline cases loop_count = 0 and *)
(* the back edge.                                                            *)
(* ------------------------------------------------------------------------- *)

(* loop_count = 0 (pc + 0xa0 -> pc + 0xaa0, the cbz at pc + 0xa0 taken),
   closed inline. *)
let SWP_DEC_LC0_TAC : tactic =
  ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_4]) THEN
  ARM_STEPS_TAC AES128_GCM_DEC_EXEC [1] THEN
  ENSURES_FINAL_STATE_TAC THEN REWRITE_TAC[htable_mem_4] THEN
  ASM_REWRITE_TAC[] THEN
  (* Reduce 4 * 0 to 0 before unfolding list_of_seq and nist_ghash, whose
     recursive equations loop on the unreduced count; LT (or CONJUNCT1 LT)
     stays out of the rewrite set for the same reason.  Then close the
     numeric residuals. *)
  REWRITE_TAC[ARITH_RULE `4 * 0 = 0`; ARITH_RULE `64 * 0 = 0`;
              ARITH_RULE `4 * 0 + 2 = 2`;
              MULT_CLAUSES; ADD_CLAUSES; WORD_ADD_0; LE_0] THEN
  REWRITE_TAC[list_of_seq] THEN REWRITE_TAC[nist_ghash] THEN
  REWRITE_TAC[ARITH_RULE `j < 0 <=> F`] THEN
  (* Fold the ABI macro back in the frame goal (the main theorem expanded
     it), so that the frame fact MAYCHANGE_ABI_CLOSE_TAC uses matches the goal
     (ABI ,, ..) s0 s1. *)
  REWRITE_TAC[GSYM MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REPEAT CONJ_TAC THEN
  TRY(ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  TRY(CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_BLAST THEN NO_TAC) THEN
  MAYCHANGE_ABI_CLOSE_TAC;;

(* The main theorem presents its leaf goals with the ABI macro expanded,
   htable_mem_4 unfolded and the conjunctions right-associated (by
   REWRITE_TAC[htable_mem_4; GSYM CONJ_ASSOC] after each
   ENSURES_SEQUENCE_TAC and ENSURES_WHILE_UP_TAC); leaf_form puts a leg
   lemma in the same form. *)
let leaf_form th =
  REWRITE_RULE[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; htable_mem_4;
               GSYM CONJ_ASSOC] th;;

(* Discharge a leg's hypotheses from the main theorem's context.  The
   nonoverlapping facts may appear with their arguments swapped relative to
   the ALLPAIRS expansion, hence the NONOVERLAPPING_TAC fallback. *)
let LEG_HYPS_TAC : tactic =
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
  TRY(FIRST_ASSUM ACCEPT_TAC) THEN TRY(ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  TRY(ASM_ARITH_TAC) THEN TRY NONOVERLAPPING_TAC;;

(* Close a leaf goal with a leg lemma (key_p occurs only in its hypotheses). *)
let APPLY_LEG_TAC (leg:thm) : tactic =
  MATCH_MP_TAC (leaf_form leg) THEN EXISTS_TAC `key_p:int64` THEN LEG_HYPS_TAC;;

(* The back edge (the cbnz at pc + 0x510 taken back to pc + 0x294 while
   X1 = word (loop_count - 2 - i) is nonzero), closed inline. *)
let SWP_DEC_BACKEDGE_LEAF_TAC : tactic =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_4]) THEN
  (* The cbnz is taken: ~(val (word (loop_count - 2 - i)) = 0) follows from
     the small loop-count facts alone (val (word loop_count) = loop_count
     bounds loop_count by 2^64; i < loop_count - 2).  ASM_ARITH_TAC would
     drag the whole invariant into the arithmetic and blow up. *)
  SUBGOAL_THEN `~(val(word(loop_count-2-i):int64) = 0)` ASSUME_TAC THENL
   [SUBGOAL_THEN `val(word(loop_count-2-i):int64) = loop_count-2-i`
    SUBST1_TAC THENL
     [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
      MP_TAC(ISPEC `word loop_count:int64` VAL_BOUND_64) THEN
      TRY(FIRST_ASSUM(fun th -> if lhs(concl th) = `val(word loop_count:int64)`
                      then REWRITE_TAC[th] else NO_TAC)) THEN
      UNDISCH_TAC `i < loop_count - 2` THEN ARITH_TAC;
      UNDISCH_TAC `i < loop_count - 2` THEN ARITH_TAC];
    ALL_TAC] THEN
  ARM_STEPS_TAC AES128_GCM_DEC_EXEC [1] THEN
  ENSURES_FINAL_STATE_TAC THEN REWRITE_TAC[htable_mem_4] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  MAYCHANGE_ABI_CLOSE_TAC;;

(* ========================================================================= *)
(* The core correctness theorem.                                             *)
(*                                                                           *)
(* This covers the body of the function without the register saves and       *)
(* restores: the PC starts at pc + 0x2c, the first instruction after the 11  *)
(* save instructions, and ends at pc + 0xb7c, the first restore              *)
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
(* ========================================================================= *)

(*** The NIST-level specifications read byte strings as big-endian words, so
 *** the round keys rk, the counter block ctr_block nonce c and the tag tag0
 *** are NIST-order words.  The kernel loads them in the usual little-endian
 *** ARM fashion, so the precondition gives the memory contents as their byte
 *** reversals; the data blocks inblock i are the lane-order values of the
 *** loads themselves.
 ***)

let AES128_GCM_DEC_CORRECT = prove
 (`!in_p len_bits out_p tag_p ivec_p key_p htable_p inblock tag0 nonce c rk pc
     stackpointer.
       aligned 16 stackpointer /\
       ALLPAIRS nonoverlapping
        [(out_p, 16 * val len_bits DIV 128); (tag_p, 16); (ivec_p, 16);
         (word_add stackpointer (word 160), 64)]
        [(word pc, LENGTH aes128_gcm_dec_tmc); (key_p, 176); (htable_p, 96)] /\
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
      (\s. aligned_bytes_loaded s (word pc) aes128_gcm_dec_tmc /\
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
      (\s. read PC s = word (pc + 0xb7c) /\
           (!i. i < val len_bits DIV 128
                ==> read (memory :> bytes128 (word_add out_p (word(16*i)))) s =
                    word_xor (aes_ctr_block aes128_cipher c nonce rk i)
                      (inblock i)) /\
           read (memory :> bytes128 tag_p) s =
             word_reversefields 8
              (nist_ghash (aes128_cipher (word 0) rk) tag0
                 (list_of_seq (nist_input_block inblock)
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
  GEN_TAC THEN W64_GEN_TAC `len_bits:num` THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REWRITE_TAC[ALLPAIRS; PAIRWISE; ALL; fst AES128_GCM_DEC_EXEC] THEN

  (*** Abbreviate the loop counts to keep goal terms manageable ***)

  ABBREV_TAC `nblocks     = len_bits DIV 128` THEN
  ABBREV_TAC `loop_count  = nblocks DIV 4` THEN
  ABBREV_TAC `loop_remain = nblocks MOD 4` THEN
  INTRO_HYPS_TAC THEN
  CONV_TAC(ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN REWRITE_TAC[WORD_ADD_0] THEN

  (*** Break up the round key list ***)

  ASM_CASES_TAC `LENGTH(rk:int128 list) = 11` THENL
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

  ENSURES_SEQUENCE_TAC `pc + 0xa0` (mk_abs(`s:armstate`, entry_body)) THEN
  REWRITE_TAC[htable_mem_4; GSYM CONJ_ASSOC] THEN CONJ_TAC THENL
   [ENSURES_INIT_TAC "s0" THEN
    (*** Split + abbreviate the two 64-bit IV halves so the scalar counter ***)
    (*** registers X11/X12/X13 loaded by "ldp x11,x12,[x4]" survive as     ***)
    (*** clean variables rather than being dropped as compound             ***)
    (*** initial-memory reads                                              ***)
    UNDISCH_TAC
     `read (memory :> bytes128 ivec_p) s0 =
      word_reversefields 8 (ctr_block nonce c)` THEN
    GEN_REWRITE_TAC (LAND_CONV o LAND_CONV)
     [el 1 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT)] THEN
    DISCH_TAC THEN
    ABBREV_TAC `ivlo:int64 = read (memory :> bytes64 ivec_p) s0` THEN
    ABBREV_TAC
      `ivhi:int64 = read (memory :> bytes64 (word_add ivec_p (word 8))) s0` THEN
    ARM_STEPS_TAC AES128_GCM_DEC_EXEC (1--29) THEN
    ENSURES_FINAL_STATE_TAC THEN
    (*** Name the IV-halves join relation for reuse in the counter         ***)
    (*** conjuncts.  Keep ivlo/ivhi unsubstituted so the ivec              ***)
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
      (*** Q30 = byteswap tag ***)
      REWRITE_TAC[byteswap128] THEN CONV_TAC WORD_BLAST];
    MAP_EVERY VAL_INT64_TAC
     [`nblocks:num`; `loop_count:num`; `loop_remain:num`]] THEN

  (*** Break code between main unrolled loop and tail loop ***)

  ENSURES_SEQUENCE_TAC `pc + 0xaa0` (mk_abs(`s:armstate`, exit_body)) THEN
  REWRITE_TAC[htable_mem_4; GSYM CONJ_ASSOC] THEN CONJ_TAC THENL
   [(*** The four-block loop, pc + 0xa0 -> pc + 0xaa0, with four control-flow
     *** paths on loop_count.  The fill does sub x1,x1,#2 (0x28c) then
     *** cbz x1,0x514; the loop body does sub x1,x1,#1 (0x50c) then
     *** cbnz x1,0x294, so the loop runs loop_count - 2 times (the pipeline
     *** is two groups deep: the AES and the GHASH of each group start in the
     *** iteration before):
     ***   loop_count = 0: the cbz x1 at 0xa0 goes straight to 0xaa0.
     ***   loop_count = 1: the b.eq at 0xa8 goes to iter_1 (0x828), which
     ***                   falls into 0xaa0.
     ***   loop_count = 2: the fill, then the cbz at 0x290 is taken to the
     ***                   drain at 0x514; the loop runs 0 times, so
     ***                   ENSURES_WHILE_UP_TAC (which needs ~(k = 0)) does
     ***                   not apply and the case is separate.
     ***   loop_count >= 3: ENSURES_WHILE_UP_TAC (loop_count - 2) with the
     ***                   loop head 0x294 and the back edge 0x510; the fill
     ***                   (0xa0 -> 0x294, establishing swp_inv 0) and the
     ***                   drain (0x510 -> 0xaa0) are its initialization and
     ***                   exit subgoals, and the body is SWP_DEC_BODYLEG.
     *** Each leaf goal is discharged by its leg lemma (SWP_DEC_ITER1,
     *** SWP_DEC_LC2, SWP_DEC_FILLLEG, SWP_DEC_BODYLEG, SWP_DEC_DRAINLEG) via
     *** APPLY_LEG_TAC, or inline (loop_count = 0, the back edge). ***)

    ASM_CASES_TAC `loop_count = 0` THENL
     [POP_ASSUM SUBST_ALL_TAC THEN SWP_DEC_LC0_TAC;
      ALL_TAC] THEN

    ASM_CASES_TAC `loop_count = 1` THENL
     [APPLY_LEG_TAC SWP_DEC_ITER1;
      ALL_TAC] THEN

    ASM_CASES_TAC `loop_count = 2` THENL
     [APPLY_LEG_TAC SWP_DEC_LC2;
      ALL_TAC] THEN

    SUBGOAL_THEN `3 <= loop_count` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN

    ENSURES_WHILE_UP_TAC `loop_count - 2` `pc + 0x294` `pc + 0x510`
      (mk_abs(`i:num`,
              mk_abs(`s:armstate`, ap swp_inv `i:num` `s:armstate`))) THEN
    REWRITE_TAC[htable_mem_4; GSYM CONJ_ASSOC] THEN REPEAT CONJ_TAC THENL
     [(*** ~(loop_count - 2 = 0), from 3 <= loop_count. ***)
      ASM_ARITH_TAC;
      (*** FILL: 0xa0 -> 0x294, establish the inlined invariant at i = 0. ***)
      APPLY_LEG_TAC SWP_DEC_FILLLEG;
      (*** The body (SWP_DEC_BODYLEG): 0x294 -> 0x510, inv i -> inv (i+1). ***)
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN APPLY_LEG_TAC SWP_DEC_BODYLEG;
      (*** The back edge: the cbnz x1 at 0x510 is taken back to 0x294. ***)
      SWP_DEC_BACKEDGE_LEAF_TAC;
      (*** The drain: 0x510 -> 0xaa0, inv (loop_count-2) -> exit state. ***)
      APPLY_LEG_TAC SWP_DEC_DRAINLEG];
    ALL_TAC] THEN
  (*** Trivial case of the tail loop ***)

  ASM_CASES_TAC `loop_remain = 0` THENL
   [POP_ASSUM SUBST_ALL_TAC THEN
    ENSURES_INIT_TAC "s0" THEN
    (*** Split the initial ivec read so the low 12 bytes (untouched by the ***)
    (*** counter writeback) survive as separate 32-bit cells across the    ***)
    (*** stepping.                                                         ***)
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o CONV_RULE(READ_MEMORY_SPLIT_CONV 2) o
      check (fun th -> let c = concl th in
        is_eq c && free_in `ivec_p:int64` (lhs c) &&
        not(free_in `out_p:int64` (lhs c)) &&
          not(free_in `key_p:int64` (lhs c)) &&
        not(free_in `htable_p:int64` (lhs c)) &&
          not(free_in `tag_p:int64` (lhs c)))) THEN
    MAP_EVERY(fun n -> ARM_STEPS_TAC AES128_GCM_DEC_EXEC [n] THEN
          RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)))
        (1--6) THEN
    ENSURES_FINAL_STATE_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP (ARITH_RULE
     `n MOD 4 = 0 ==> 4 * n DIV 4 = n`)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN
    (*** Recompose the ivec postcondition from the 32-bit cells: three     ***)
    (*** unchanged nonce cells plus the freshly-written byte-reversed      ***)
    (*** counter word.  Split only the ivec read (guarded), not the        ***)
    (*** out-block reads.                                                  ***)
    CONV_TAC(ONCE_DEPTH_CONV(fun t ->
      if is_eq t && free_in `ivec_p:int64` (lhs t) &&
         not(free_in `out_p:int64` (lhs t)) &&
           not(free_in `tag_p:int64` (lhs t))
      then READ_MEMORY_SPLIT_CONV 2 t else failwith "")) THEN
    CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    REWRITE_TAC[ZX_COUNTER_UD; CTR_ZX_NORM] THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[byteswap128; ctr_block] THEN
    CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
    CONV_TAC WORD_BLAST;

    ALL_TAC] THEN

  (*** Loop setup for the tail loop ***)

  ENSURES_WHILE_UP_TAC `loop_remain:num` `pc + 0xaa4` `pc + 0xb64`
    `\i s.
      read X0  s = word_add in_p  (word (64 * loop_count + 16 * i)) /\
      read X2  s = word_add out_p (word (64 * loop_count + 16 * i)) /\
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
      read Q7 s = word 13979173243358019584 /\
      read X11 s =
        word_subword (word_reversefields 8 (ctr_block nonce c):int128)
          (0,64):int64 /\
      read X12 s =
        word_zx (word_zx (word_subword
          (word_reversefields 8 (ctr_block nonce c):int128)
            (64,64):int64):int32):int64 /\
      read X13 s = word_zx (word (4 * loop_count + i + c):int32):int64 /\
      read X15 s = word(len_bits DIV 8) /\
      read X16 s = word(loop_remain - i) /\
      read Q30 s =
        byteswap128
            (nist_ghash (aes128_cipher (word 0) rk) tag0
               (list_of_seq (nist_input_block inblock)
                          (4 * loop_count + i))) /\
      htable_mem_4 (ghash_twist (aes128_cipher (word 0) rk)) htable_p s /\
      read Q12 s = byteswap128
        (h_power (ghash_twist (aes128_cipher (word 0) rk)) 0) /\
      read Q14 s = word_join
       (karatsuba_mid (h_power (ghash_twist (aes128_cipher (word 0) rk)) 1))
       (karatsuba_mid (h_power (ghash_twist (aes128_cipher (word 0) rk)) 0)) /\
      (!j. 4 * loop_count + i <= j /\ j < nblocks
           ==> read (memory :> bytes128 (word_add in_p (word(16*j)))) s =
               inblock j) /\
      (!j. j < 4 * loop_count + i
           ==> read (memory :> bytes128 (word_add out_p (word(16*j)))) s =
               word_xor (aes_ctr_block aes128_cipher c nonce rk j)
                 (inblock j))` THEN
  ASM_REWRITE_TAC[htable_mem_4; GSYM CONJ_ASSOC] THEN REPEAT CONJ_TAC THENL
   [ENSURES_INIT_TAC "s0" THEN
    MAP_EVERY(fun n -> ARM_STEPS_TAC AES128_GCM_DEC_EXEC [n] THEN
          RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)))
        (1--1) THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES; SUB_0];

    (*** Main loop invariant (tail loop) ****)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
    ENSURES_INIT_TAC "s0" THEN
    SUBGOAL_THEN
     `read (memory :> bytes128
        (word_add in_p (word (64 * loop_count + 16 * i)))) s0 =
      inblock (4 * loop_count + i)`
    ASSUME_TAC THENL
     [REWRITE_TAC[ARITH_RULE `64 * a + 16 * b = 16 * (4 * a + b)`] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN SIMPLE_ARITH_TAC;
      ALL_TAC] THEN
    INPUT_LEG_TAC [] THEN
    (*** The tail block's counter block is assembled on the stack at       ***)
    (*** sp + 160: stored by stp x11,x23 at step 6, reloaded into Q10 by   ***)
    (*** ldr at step 8.  MERGE_CTR128_TAC at s6, after the stp and before  ***)
    (*** the ldr, gives the reload a concrete counter block; without it    ***)
    (*** Q10 would stay a symbolic read of an old state and the output     ***)
    (*** store could not be resolved.                                      ***)
    MAP_EVERY(fun n -> ARM_STEPS_TAC AES128_GCM_DEC_EXEC [n] THEN
      RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)))
     (1--6) THEN
    MERGE_CTR128_TAC 160 "s6" THEN
    MAP_EVERY(fun n -> ARM_STEPS_TAC AES128_GCM_DEC_EXEC [n] THEN
      RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)))
     (7--48) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ARITH_RULE `j < a + i + 1 <=> j < a + i \/ j = a + i`] THEN
    ASM_REWRITE_TAC[TAUT `p \/ q ==> r <=> (p ==> r) /\ (q ==> r)`] THEN
    REWRITE_TAC[FORALL_UNWIND_THM2] THEN
    ASM_REWRITE_TAC[ARITH_RULE `16 * (4 * a + b) = 64 * a + 16 * b`] THEN
    (*** Scalar counter reconstruction (tail loop, single block: the       ***)
    (*** counter word is "add w17,w13,#0", the base 4*loop_count+i+c).     ***)
    REWRITE_TAC[ZX_COUNTER_UD; ZX_COUNTER_INC; CTR_ZX_NORM] THEN
    REWRITE_TAC[GSYM WORD_ADD; WORD_ADD_0; ADD_0] THEN
    REWRITE_TAC[CTR_BLOCK_BUILD_INSERT] THEN
    REWRITE_TAC[XOR_AES128_CIPHER_RECONSTRUCT_DEC] THEN
    ASM_REWRITE_TAC[MAP; WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
    REWRITE_TAC[aes_ctr_block; GSYM ADD_ASSOC] THEN
    CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
    ASM_SIMP_TAC[WORD_SUB; LT_IMP_LE; ARITH_RULE `i < l ==> i + 1 <= l`] THEN
    DISCARD_STATE_TAC "s48" THEN
    REWRITE_TAC[ADD_ASSOC; ARITH] THEN
    (*** Fold the GHASH operand to nist_input_block subwords (as in the    ***)
    (*** main loop).                                                       ***)
    DEC_GHASH_NORM_TAC THEN
    (*** Peel the counter conjunct (word arithmetic); the single           ***)
    (*** output-store conjunct was already folded and resolved above, by   ***)
    (*** the forall split (j = 4*loop_count+i) and                         ***)
    (*** XOR_AES128_CIPHER_RECONSTRUCT_DEC, as for the stores of the main  ***)
    (*** loop.  This leaves the single GHASH accumulator goal.             ***)
    REPEAT(CONJ_TAC
           THENL
           [(REPEAT AP_TERM_TAC THEN ARITH_TAC) ORELSE CONV_TAC WORD_RULE ORELSE
      ASM_SIMP_TAC[WORD_SUB; LT_IMP_LE;
                   ARITH_RULE `i < loop_remain ==> i + 1 <= loop_remain`];
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
    MAP_EVERY ABBREV_TAC
     [`sofar = (nist_ghash (aes128_cipher (word 0) rk) tag0
                 (list_of_seq (nist_input_block inblock)
                              (4 * loop_count + i)))`;
      `cipherblock =
        nist_input_block inblock (4 * loop_count + i)`;
      `h = h_power (ghash_twist (aes128_cipher (word 0) rk)) 0`;
      `k = karatsuba_mid h`] THEN
    REWRITE_TAC[GSYM WORD_SUBWORD_XOR] THEN
    REWRITE_TAC[RECONSTRUCT_POLYVAL_REDUCE_G2] THEN
    TRANS_TAC EQ_TRANS
      `polyval_reduce_prop3
          (word_pmul (word_xor sofar cipherblock:int128) (h:int128))` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[PMUL_KARATSUBA_JOIN_ALT] THEN
      REWRITE_TAC[byteswap128; WORD_SUBWORD_XOR] THEN
      CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
      ASM_REWRITE_TAC[] THEN
      LET_TAC THEN ASM_REWRITE_TAC[] THEN
      EXPAND_TAC "k" THEN REWRITE_TAC[karatsuba_mid] THEN
      ASM_REWRITE_TAC[] THEN REPEAT LET_TAC THEN
      REWRITE_TAC[INBLOCK_REASSEMBLE] THEN
      REWRITE_TAC[GSYM nist_input_block] THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[POLYVAL_REDUCE_G2] THEN ASM_REWRITE_TAC[] THEN NO_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[GSYM polyval_dot] THEN
    EXPAND_TAC "h" THEN REWRITE_TAC[h_power] THEN
    REWRITE_TAC[GSYM NIST_DOT_IS_POLYVAL_DOT] THEN
    REWRITE_TAC[ARITH_RULE `(k + 1) = SUC k`] THEN
    REWRITE_TAC[list_of_seq; NIST_GHASH_APPEND;
                NIST_GHASH_CONS; nist_ghash] THEN
    ASM_REWRITE_TAC[];

    (*** Trivial loop-back goal (tail loop) ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
    ARM_SIM_TAC AES128_GCM_DEC_EXEC [1] THEN
    ASM_SIMP_TAC[WORD_SUB; LT_IMP_LE; VAL_EQ_0; WORD_SUB_EQ_0] THEN
    ASM_REWRITE_TAC[GSYM VAL_EQ];

    (**** Final writeback, reversal etc. ***)

    ENSURES_INIT_TAC "s0" THEN
    (*** Split the initial ivec read so the low 12 (nonce) bytes survive   ***)
    (*** the 4-byte counter writeback as separate cells.                   ***)
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o CONV_RULE(READ_MEMORY_SPLIT_CONV 2) o
      check (fun th -> let c = concl th in
        is_eq c && free_in `ivec_p:int64` (lhs c) &&
        not(free_in `out_p:int64` (lhs c)) &&
          not(free_in `key_p:int64` (lhs c)) &&
        not(free_in `htable_p:int64` (lhs c)) &&
          not(free_in `tag_p:int64` (lhs c)))) THEN
    MAP_EVERY(fun n -> ARM_STEPS_TAC AES128_GCM_DEC_EXEC [n] THEN
          RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)))
        (1--6) THEN
    ENSURES_FINAL_STATE_TAC THEN
    (*** Unify the counter values: the postcondition uses nblocks, the     ***)
    (*** running counter is 4*loop_count+loop_remain; rewrite nblocks to   ***)
    (*** the latter so both sides share one expression before blasting.    ***)
    SUBGOAL_THEN `nblocks = 4 * loop_count + loop_remain` SUBST_ALL_TAC THENL
     [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    CONV_TAC(ONCE_DEPTH_CONV(fun t ->
      if is_eq t && free_in `ivec_p:int64` (lhs t) &&
         not(free_in `out_p:int64` (lhs t)) &&
           not(free_in `tag_p:int64` (lhs t))
      then READ_MEMORY_SPLIT_CONV 2 t else failwith "")) THEN
    CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    REWRITE_TAC[ZX_COUNTER_UD] THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[byteswap128; ctr_block] THEN
    (*** Normalise counter-value associativity (X13's                     ***)
    (*** 4*loop_count+loop_remain+c against the postcondition's            ***)
    (*** (4*loop_count+loop_remain)+c) and collapse the W-conversion chain ***)
    (*** before blasting.                                                  ***)
    REWRITE_TAC[ADD_ASSOC; ZX_COUNTER_UD; CTR_ZX_NORM] THEN
    CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
    CONV_TAC WORD_BLAST]);;

(* ========================================================================= *)
(* Subroutine correctness: the core theorem lifted through the register save *)
(* and restore code and the final ret, first for the trimmed code and then   *)
(* for the full code with its BTI landing pad                                *)
(* (AES128_GCM_DEC_SUBROUTINE_CORRECT, the theorem used externally).         *)
(* ========================================================================= *)

(*** The pre- and postconditions are those of the core theorem (the CTR
 *** output, here the plaintext, the GHASH tag and the updated counter),
 *** lifted through the save/restore prologue and epilogue and the final
 *** ret.  The stack frame (224 bytes below the incoming SP) is added to the
 *** nonoverlapping lists and to the MAYCHANGE.  ARM_ADD_RETURN_STACK_TAC
 *** does the lifting; htable_mem_4 and wordlist_from_memory are expanded,
 *** in the goal and in the core theorem fed to it, so that the
 *** precondition of the inner step is discharged with no residual subgoal.
 ***)

let AES128_GCM_DEC_NOIBT_SUBROUTINE_CORRECT = prove
 (`!in_p len_bits out_p tag_p ivec_p key_p htable_p inblock tag0 nonce c rk
    pc stackpointer returnaddress.
    aligned 16 stackpointer /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * val len_bits DIV 128); (tag_p, 16); (ivec_p, 16);
       (word_sub stackpointer (word 224), 224)]
      [(word pc, LENGTH aes128_gcm_dec_tmc); (key_p, 176); (htable_p, 96)] /\
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
      (\s. aligned_bytes_loaded s (word pc) aes128_gcm_dec_tmc /\
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
                    word_xor (aes_ctr_block aes128_cipher c nonce rk i)
                      (inblock i)) /\
           read (memory :> bytes128 tag_p) s =
             word_reversefields 8
              (nist_ghash (aes128_cipher (word 0) rk) tag0
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
  REWRITE_TAC[fst AES128_GCM_DEC_EXEC; htable_mem_4] THEN
  CONV_TAC(ONCE_DEPTH_CONV WORDLIST_FROM_MEMORY_CONV) THEN
  ARM_ADD_RETURN_STACK_TAC
    ~pre_post_nsteps:(11, 11)
    AES128_GCM_DEC_EXEC
    (CONV_RULE(ONCE_DEPTH_CONV WORDLIST_FROM_MEMORY_CONV)
       (REWRITE_RULE[fst AES128_GCM_DEC_EXEC; htable_mem_4]
          AES128_GCM_DEC_CORRECT))
    `[X19; X20; X21; X22; X23; X24; X25; X26; X27; X28; X29; X30;
      D8; D9; D10; D11; D12; D13; D14; D15]` 224);;

(* The same for the full code, with its BTI landing pad. *)

let AES128_GCM_DEC_SUBROUTINE_CORRECT = prove
 (`!in_p len_bits out_p tag_p ivec_p key_p htable_p inblock tag0 nonce c rk
    pc stackpointer returnaddress.
    aligned 16 stackpointer /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * val len_bits DIV 128); (tag_p, 16); (ivec_p, 16);
       (word_sub stackpointer (word 224), 224)]
      [(word pc, LENGTH aes128_gcm_dec_mc); (key_p, 176); (htable_p, 96)] /\
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
      (\s. aligned_bytes_loaded s (word pc) aes128_gcm_dec_mc /\
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
                    word_xor (aes_ctr_block aes128_cipher c nonce rk i)
                      (inblock i)) /\
           read (memory :> bytes128 tag_p) s =
             word_reversefields 8
              (nist_ghash (aes128_cipher (word 0) rk) tag0
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
    aes128_gcm_dec_mc aes128_gcm_dec_tmc
      AES128_GCM_DEC_NOIBT_SUBROUTINE_CORRECT));;

(* ========================================================================= *)
(* Constant-time and memory-safety proofs, for the core and for the whole    *)
(* subroutine.                                                               *)
(*                                                                           *)
(* The outer exists f_events, quantified before the public arguments (the    *)
(* in/out/tag/ivec/key/htable pointers, len_bits, pc, stackpointer and, for  *)
(* the subroutine, returnaddress), makes the event trace e2 of the kernel a  *)
(* function of those arguments only, and memaccess_inbounds puts every       *)
(* memory access in the declared readable and writable ranges: this gives    *)
(* constant-time execution and memory safety.                                *)
(*                                                                           *)
(* The main loop (loop_count = nblocks DIV 4 groups of 64 bytes) is a        *)
(* pipeline two groups deep with four control-flow paths                     *)
(* (loop_count = 0, 1, 2 and >= 3), and the tail loop                        *)
(* (loop_remain = nblocks MOD 4 blocks of 16 bytes) is a plain WHILE.  The   *)
(* subroutine versions also wrap the register-save prologue and              *)
(* register-restore epilogue over the 224-byte stack frame                   *)
(* (ARM_ADD_RETURN_STACK_TAC).                                               *)
(* ========================================================================= *)

let SAFE_SIM_TAC = ARM_SAFE_SIM_TAC EXEC;;

(* The loop runs loop_count - 2 times (the exit test of the fill, the cbz at *)
(* 0x290, tests loop_count - 2), so the pointers at the drain are in terms   *)
(* of loop_count - 2 and have to be reconciled with the 64 * loop_count of   *)
(* the sequence post.  DRAIN_ADDR_TAC writes loop_count as (loop_count - 2)  *)
(* + 2 so that WORD_RULE sees only linear combinations.                      *)
let DRAIN_ADDR_TAC = DRAIN_ADDR_K_TAC `2`;;

let OPEN_DEC_TAC = OPEN_SWP_SAFE_TAC EXEC;;

let scaffold_dec =
 `\(in_p:int64) (out_p:int64) (tag_p:int64) (ivec_p:int64) (key_p:int64)
  (htable_p:int64)
   (len_bits:int64) (pc:num) (stackpointer:int64).
   APPEND
     (if val len_bits DIV 128 MOD 4 = 0 then
        f_ev_tail0 in_p out_p tag_p ivec_p key_p htable_p len_bits pc
          stackpointer
      else
        APPEND
          (f_ev_tail_post in_p out_p tag_p ivec_p key_p htable_p len_bits pc
           stackpointer)
          (APPEND
            (ENUMERATEL (val len_bits DIV 128 MOD 4)
              (\i. f_ev_tail_body in_p out_p tag_p ivec_p key_p htable_p
               len_bits pc stackpointer i))
            (f_ev_tail_pre in_p out_p tag_p ivec_p key_p htable_p len_bits pc
             stackpointer)))
     (APPEND
       (if val len_bits DIV 128 DIV 4 = 0 then
          f_ev_m0 in_p out_p tag_p ivec_p key_p htable_p len_bits pc
            stackpointer
        else if val len_bits DIV 128 DIV 4 = 1 then
          f_ev_m1 in_p out_p tag_p ivec_p key_p htable_p len_bits pc
            stackpointer
        else if val len_bits DIV 128 DIV 4 = 2 then
          f_ev_m2 in_p out_p tag_p ivec_p key_p htable_p len_bits pc
            stackpointer
        else
          APPEND
            (f_ev_drain in_p out_p tag_p ivec_p key_p htable_p len_bits pc
             stackpointer)
            (APPEND
              (ENUMERATEL (val len_bits DIV 128 DIV 4 - 2)
                (\i. f_ev_steady in_p out_p tag_p ivec_p key_p htable_p len_bits
                 pc stackpointer i))
              (f_ev_fill in_p out_p tag_p ivec_p key_p htable_p len_bits pc
               stackpointer)))
       (f_ev_pro in_p out_p tag_p ivec_p key_p htable_p len_bits pc
        stackpointer))
   :(uarch_event) list`;;

let AES128_GCM_DEC_SAFE = prove
 (`exists f_events.
    forall e in_p len_bits out_p tag_p ivec_p key_p htable_p pc stackpointer.
      aligned 16 stackpointer /\
      ALLPAIRS nonoverlapping
        [(out_p, 16 * val len_bits DIV 128); (tag_p, 16); (ivec_p, 16);
         (word_add stackpointer (word 160), 64)]
        [(word pc, LENGTH aes128_gcm_dec_tmc); (key_p, 176); (htable_p, 96)] /\
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
          (\s. aligned_bytes_loaded s (word pc) aes128_gcm_dec_tmc /\
               read PC s = word (pc + 0x2c) /\
               read SP s = stackpointer /\
               C_ARGUMENTS
                 [in_p; len_bits; out_p; tag_p; ivec_p; key_p; htable_p] s /\
               read events s = e)
          (\s. read PC s = word (pc + 0xb7c) /\
               (exists e2.
                    read events s = APPEND e2 e /\
                    e2 =
                      f_events in_p out_p tag_p ivec_p key_p htable_p len_bits
                        pc stackpointer /\
                    memaccess_inbounds e2
                      [in_p, 16 * val len_bits DIV 128; tag_p, 16; ivec_p, 16;
                       key_p, 176; htable_p, 96;
                       out_p, 16 * val len_bits DIV 128;
                       word_add stackpointer (word 160), 64]
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
  OPEN_DEC_TAC THEN

  (*** Top split at 0xaa0 (main region -> tail region). ***)
  ENSURES_EVENTS_SEQUENCE_TAC `pc + 0xaa0`
   `\s. read X0 s = word_add in_p (word (64 * loop_count)) /\
        read X2 s = word_add out_p (word (64 * loop_count)) /\
        read X3 s = tag_p /\ read X4 s = ivec_p /\ read X6 s = htable_p /\
        read SP s = stackpointer /\ read X16 s = word loop_remain` THEN
  CONJ_TAC THENL
   [(*** Main region pc + 0x2c -> pc + 0xaa0: setup and four-block loop. ***)
    ENSURES_EVENTS_SEQUENCE_TAC `pc + 0xa0`
     `\s. read X0 s = in_p /\ read X2 s = out_p /\ read X3 s = tag_p /\
          read X4 s = ivec_p /\ read X6 s = htable_p /\
          read SP s = stackpointer /\
          read X1 s = word loop_count /\ read X16 s = word loop_remain` THEN
    CONJ_TAC THENL [SAFE_SIM_TAC (1--29) THEN CLOSE_TAC; ALL_TAC] THEN

    (*** loop_count = 0 : cbz @0xa0 taken -> 0xaa0. ***)
    ASM_CASES_TAC `loop_count = 0` THENL
     [REDUCE_IF0_TAC `loop_count:num` THEN SAFE_SIM_TAC (1--1) THEN CLOSE_TAC;
      ALL_TAC] THEN
    REDUCE_IFN0_TAC `loop_count:num` THEN

    (*** loop_count = 1 : b.eq @0xa8 -> iter_1 path (3 + 158 steps). ***)
    ASM_CASES_TAC `loop_count = 1` THENL
     [REDUCE_IFEQ_TAC `loop_count:num` `1` THEN SAFE_SIM_TAC (1--161) THEN
      CLOSE_TAC; ALL_TAC] THEN
    REDUCE_IFNE_TAC `loop_count:num` `1` THEN

    (*** loop_count = 2: fill (cbz @0x290 taken) + drain, 125 + 197 steps. ***)
    ASM_CASES_TAC `loop_count = 2` THENL
     [REDUCE_IFEQ_TAC `loop_count:num` `2` THEN SAFE_SIM_TAC (1--322) THEN
      CLOSE_TAC; ALL_TAC] THEN
    REDUCE_IFNE_TAC `loop_count:num` `2` THEN

    (*** loop_count >= 3: fill, loop_count - 2 iterations, drain. ***)
    SUBGOAL_THEN `3 <= loop_count` ASSUME_TAC THENL
    [ASM_ARITH_TAC; ALL_TAC] THEN
    ENSURES_EVENTS_WHILE_UP2_TAC `loop_count - 2` `pc + 0x294` `pc + 0x514`
     `\i s. read X0 s = word_add in_p (word (64 * i + 64)) /\
            read X2 s = word_add out_p (word (64 * i)) /\
            read X3 s = tag_p /\ read X4 s = ivec_p /\ read X6 s = htable_p /\
            read SP s = stackpointer /\ read X16 s = word loop_remain /\
            read X1 s = word (loop_count - 2 - i)` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [(*** ~(loop_count - 2 = 0) ***)
      ASM_ARITH_TAC;
      (*** FILL: 0xa0 -> 0x294, establish inv 0. ***)
      BEQ_NZ_TAC `1` THEN SAFE_SIM_TAC (1--125) THEN
      BEQ_NZ_TAC `2` THEN
      REPEAT CONJ_TAC THENL
       [(* cbz @0x290 branch not taken *)
        ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE;
        ADDR_RECON_TAC;
        ADDR_RECON_TAC;
        (* X1 = word(loop_count - 2 - 0) *)
        REWRITE_TAC[SUB_0] THEN GEN_REWRITE_TAC RAND_CONV [WORD_SUB] THEN
        ASM_SIMP_TAC[ARITH_RULE `3 <= loop_count ==> 2 <= loop_count`];
        DEABBR_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC];
      (*** The body and back edge: 0x294 -> 0x514, inv i -> inv (i+1). ***)
      REWRITE_TAC[] THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      VAL_INT64_TAC `i:num` THEN
      SUBGOAL_THEN `loop_count - 2 < 2 EXP 64` ASSUME_TAC THENL
      [ASM_ARITH_TAC; ALL_TAC] THEN
      SAFE_SIM_TAC (1--160) THEN CLOSE_R2_TAC;
      (*** The drain: 0x514 -> 0xaa0. ***)
      SAFE_SIM_TAC (1--197) THEN REPEAT CONJ_TAC THENL
       [DRAIN_ADDR_TAC; DRAIN_ADDR_TAC;
        DEABBR_TAC THEN DISCHARGE_SAFE_ROBUST_TAC]];

    ALL_TAC] THEN

  (*** Tail region pc + 0xaa0 -> pc + 0xb7c: a plain WHILE on loop_remain ***)
  (*** from 0xaa4 to 0xb68, then the tag and counter stores.              ***)
  ASM_CASES_TAC `loop_remain = 0` THENL
   [REDUCE_IF0_TAC `loop_remain:num` THEN SAFE_SIM_TAC (1--6) THEN CLOSE_R2_TAC;
    ALL_TAC] THEN
  REDUCE_IFN0_TAC `loop_remain:num` THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `loop_remain:num` `pc + 0xaa4` `pc + 0xb68`
   `\i s. read X0 s = word_add in_p (word (64 * loop_count + 16 * i)) /\
          read X2 s = word_add out_p (word (64 * loop_count + 16 * i)) /\
          read X3 s = tag_p /\ read X4 s = ivec_p /\ read X6 s = htable_p /\
          read SP s = stackpointer /\ read X16 s = word (loop_remain - i)` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [SAFE_SIM_TAC (1--1) THEN CLOSE_R2_TAC;
    ALL_TAC;
    REWRITE_TAC[] THEN SAFE_SIM_TAC (1--5) THEN CLOSE_R2_TAC] THEN
  REWRITE_TAC[] THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  VAL_INT64_TAC `i:num` THEN
  SAFE_SIM_TAC (1--49) THEN CLOSE_R2_TAC);;

(* ------------------------------------------------------------------------- *)
(* The whole-function version, obtained from the core theorem exactly as the *)
(* correctness theorem is: the 11-instruction prologue and epilogue save and *)
(* restore the callee-saved registers in a 224-byte frame.                   *)
(* ------------------------------------------------------------------------- *)
let AES128_GCM_DEC_NOIBT_SUBROUTINE_SAFE = prove
 (`exists f_events.
    forall e in_p len_bits out_p tag_p ivec_p key_p htable_p pc stackpointer
      returnaddress.
      aligned 16 stackpointer /\
      ALLPAIRS nonoverlapping
        [(out_p, 16 * val len_bits DIV 128); (tag_p, 16); (ivec_p, 16);
         (word_sub stackpointer (word 224), 224)]
        [(word pc, LENGTH aes128_gcm_dec_tmc); (key_p, 176); (htable_p, 96)] /\
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
          (\s. aligned_bytes_loaded s (word pc) aes128_gcm_dec_tmc /\
               read PC s = word pc /\
               read SP s = stackpointer /\
               read X30 s = returnaddress /\
               C_ARGUMENTS
                 [in_p; len_bits; out_p; tag_p; ivec_p; key_p; htable_p] s /\
               read events s = e)
          (\s. read PC s = returnaddress /\
               (exists e2.
                    read events s = APPEND e2 e /\
                    e2 =
                      f_events in_p out_p tag_p ivec_p key_p htable_p
                        len_bits pc
                           (word_sub stackpointer (word 224)) returnaddress /\
                    memaccess_inbounds e2
                      [in_p, 16 * val len_bits DIV 128; tag_p, 16; ivec_p, 16;
                       key_p, 176; htable_p, 96;
                       out_p, 16 * val len_bits DIV 128;
                       word_sub stackpointer (word 224), 224]
                      [out_p, 16 * val len_bits DIV 128; tag_p, 16; ivec_p, 16;
                       word_sub stackpointer (word 224), 224]))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(out_p, 16 * val len_bits DIV 128);
                      memory :> bytes(tag_p, 16);
                      memory :> bytes(ivec_p, 16);
                      memory :> bytes(word_sub stackpointer (word 224), 224)])`,
  ARM_ADD_RETURN_STACK_TAC
    ~pre_post_nsteps:(11, 11)
    AES128_GCM_DEC_EXEC AES128_GCM_DEC_SAFE
    `[X19; X20; X21; X22; X23; X24; X25; X26; X27; X28; X29; X30;
      D8; D9; D10; D11; D12; D13; D14; D15]` 224 THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

(* The same for the full code, with its BTI landing pad. *)

let AES128_GCM_DEC_SUBROUTINE_SAFE = prove
 (`exists f_events.
    forall e in_p len_bits out_p tag_p ivec_p key_p htable_p pc stackpointer
      returnaddress.
      aligned 16 stackpointer /\
      ALLPAIRS nonoverlapping
        [(out_p, 16 * val len_bits DIV 128); (tag_p, 16); (ivec_p, 16);
         (word_sub stackpointer (word 224), 224)]
        [(word pc, LENGTH aes128_gcm_dec_mc); (key_p, 176); (htable_p, 96)] /\
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
          (\s. aligned_bytes_loaded s (word pc) aes128_gcm_dec_mc /\
               read PC s = word pc /\
               read SP s = stackpointer /\
               read X30 s = returnaddress /\
               C_ARGUMENTS
                 [in_p; len_bits; out_p; tag_p; ivec_p; key_p; htable_p] s /\
               read events s = e)
          (\s. read PC s = returnaddress /\
               (exists e2.
                    read events s = APPEND e2 e /\
                    e2 =
                      f_events in_p out_p tag_p ivec_p key_p htable_p
                        len_bits pc
                           (word_sub stackpointer (word 224)) returnaddress /\
                    memaccess_inbounds e2
                      [in_p, 16 * val len_bits DIV 128; tag_p, 16; ivec_p, 16;
                       key_p, 176; htable_p, 96;
                       out_p, 16 * val len_bits DIV 128;
                       word_sub stackpointer (word 224), 224]
                      [out_p, 16 * val len_bits DIV 128; tag_p, 16; ivec_p, 16;
                       word_sub stackpointer (word 224), 224]))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(out_p, 16 * val len_bits DIV 128);
                      memory :> bytes(tag_p, 16);
                      memory :> bytes(ivec_p, 16);
                      memory :> bytes(word_sub stackpointer (word 224), 224)])`,
  MATCH_ACCEPT_TAC(ARM_ADD_IBT_RULE
    aes128_gcm_dec_mc aes128_gcm_dec_tmc
      AES128_GCM_DEC_NOIBT_SUBROUTINE_SAFE));;
