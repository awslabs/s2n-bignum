(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Functional correctness, constant-time and memory-safety proofs of the      *)
(* AES-128-GCM bulk decryption kernel aes128_gcm_dec.                         *)
(*                                                                           *)
(* The kernel processes a whole number of 16-byte blocks: each block is       *)
(* decrypted in counter mode and the INPUT (ciphertext) block is folded into  *)
(* the GHASH authenticator (nist_input_block); the counter and authenticator  *)
(* are written back.  The main four-block loop is software-pipelined, so the  *)
(* proof works from a single mid-pipeline loop invariant driving one          *)
(* ENSURES_WHILE, with fill and drain legs, a dedicated single-iteration      *)
(* block for loop count 1, and the single-block tail loop.  Control flow:     *)
(*   0x2c  core entry (after the register-save preamble)                      *)
(*   0xa0  loop-count fork: cbz count -> tail; cmp count,#1 / b.eq -> iter_1   *)
(*   0xc8..0x290  fill;  0x294..0x510 steady;  0x514..0x824 drain -> 0xaa0     *)
(*   0x828..0xa34 iter_1 (count==1) -> 0xaa0                                   *)
(*   0xaa0  Lloop_unrolled_end: cbz remainder -> writeback                    *)
(*   0xaa4..0xb64 Lloop_1x tail                                               *)
(*   0xb68  Lloop_1x_end: final ivec/tag writeback; 0xb7c = core exit (ldp)      *)
(* The shared lemma substrate is in aes_gcm_utils.ml.                         *)
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

(* print_literal_from_elf "arm/aes_gcm/aes128_gcm_dec.o";; *)

let aes128_gcm_dec_mc = define_assert_from_elf "aes128_gcm_dec_mc" "arm/aes_gcm/aes128_gcm_dec.o"
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

let AES128_GCM_DEC_EXEC = ARM_MK_EXEC_RULE aes128_gcm_dec_mc;;
let EXEC = AES128_GCM_DEC_EXEC;;

(* ------------------------------------------------------------------------- *)
(* Some specification concepts.                                              *)
(* ------------------------------------------------------------------------- *)

(* For DECRYPTION the GHASH authenticator is computed over the INPUT
   (ciphertext) blocks, not the output.  The i-th folded operand in the NIST
   big-endian convention is therefore just the byte-reversal of the loaded
   little-endian input block.  (Contrast nist_cipher_block above, used by the
   encrypt kernel, which reverses the keystream-XORed OUTPUT.)  The output
   store itself is unchanged - it is still cipher_block = keystream XOR input,
   since XOR is symmetric in plaintext/ciphertext. *)

(* ------------------------------------------------------------------------- *)
(* Decryption-specific reconstruction lemmas.                                *)
(*                                                                           *)
(* The decrypt kernel's per-block store instruction is                       *)
(*    eor3 out, aes_st, rk10, plain                                          *)
(* i.e. out = aes_st XOR rk10 XOR plain, whereas the encrypt kernel emits     *)
(*    eor3 out, plain, rk10, aes_st.                                          *)
(* So the store value has the AES keystream and the input in the opposite     *)
(* XOR order from XOR_AES128_CIPHER_RECONSTRUCT; this commuted variant folds   *)
(* the 10-round AESE/AESMC tower for that operand order.                      *)
(* ------------------------------------------------------------------------- *)

let XOR_AES128_CIPHER_RECONSTRUCT_DEC = prove
 (`word_xor inblock (word_xor rk10
     (aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc
      (aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc (aese plaintext rk0)) rk1))
        rk2)) rk3)) rk4)) rk5)) rk6)) rk7)) rk8)) rk9)) =
   word_xor
   (word_reversefields 8
   (aes128_cipher (word_reversefields 8 plaintext)
   (MAP (word_reversefields 8)
   [rk0; rk1; rk2; rk3; rk4; rk5; rk6; rk7; rk8; rk9; rk10])))
   inblock`,
  ONCE_REWRITE_TAC[GSYM XOR_AES128_CIPHER_RECONSTRUCT] THEN
  CONV_TAC WORD_BITWISE_RULE);;

(* Byte-reassembly: the GHASH pmull operands are built from the loaded input   *)
(* block by 16 byte-lane word_subword/word_join operations.  These fold each   *)
(* 64-bit lane back to a subword of the byte-reversal of the whole block,      *)
(* i.e. of nist_input_block, so the accumulator reconstruction can proceed in  *)
(* terms of the settled input blocks rather than 128 raw bit variables.        *)

(* The one genuinely decrypt-specific normalization step, shared by the main-loop *)
(* and tail GHASH reconstructions.  The GHASH pmull operands are the loaded input  *)
(* run through the hardware rev64 (a per-lane byte reversal, exploded into a       *)
(* byte-lane word_join tower by WORD_SIMPLE_SUBWORD_CONV during stepping).         *)
(* INBLOCK_REASSEMBLE folds each 64-bit lane back to a subword of the byte-reversed *)
(* block, GSYM nist_input_block names it, and WORD_SUBWORD_XOR/BYTESWAP128 +        *)
(* WORD_SIMPLE_SUBWORD_CONV collapse the byteswap128/lane-swap wrappers -- putting  *)
(* the pmull operands into exactly the encrypt closer's word_subword(...)(lane)     *)
(* form so the shared reduction lemmas apply.  (Encrypt needs none of this: its     *)
(* operand is already the settled nist_cipher_block from the output store.)         *)

(* ------------------------------------------------------------------------- *)
(* Core correctness theorem.                                                 *)
(*                                                                           *)
(* This covers the body of the function with the save/restore boilerplate    *)
(* excised: PC starts at pc + 0x2c (first real instruction after the 11      *)
(* save instructions) and ends at pc + 0x3cc (first ldp of the postamble).   *)
(* The stackpointer is the value AFTER the sub sp, #0xa0 adjustment, i.e.    *)
(* the value the SP register actually holds inside the function body.        *)
(*                                                                           *)
(* Arguments (Standard ARM ABI, values in registers at core entry):          *)
(*   X0 = in        input buffer (len_bits/8 bytes)                          *)
(*   X1 = len_bits  length in bits (whole 16-byte blocks)                    *)
(*   X2 = out       output buffer (len_bits/8 bytes)                         *)
(*   X3 = tag       16-byte GHASH accumulator (in/out)                       *)
(*   X4 = ivec      16-byte counter block (in/out)                           *)
(*   X5 = key       AES-128 round keys (176 bytes = 11 x 16)                 *)
(*   X6 = Htable    192-byte precomputed H-powers table                      *)
(*   returns X0 = byte_len (= len_bits / 8)                                  *)
(* ------------------------------------------------------------------------- *)

(*** Note that the NIST-level specs consider all byte-level encodings as
 *** big-endian, and the AES-related ARM instructions take that view too.
 *** Hence in the precondition "ctr_block" and "rk" correspond as 128-bit
 *** words to the NIST specifications. Since they are loaded from memory
 *** in the usual little-endian ARM fashion, we byte-reverse when
 *** specifying them as the values in any memory cells.
 ***)


(* ===== aes2c: the 2-AES-round counter precompute (SWP-staged in Q30) ===== *)
let aes2c = new_definition
 `aes2c nonce (rk:int128 list) c : int128 =
    aesmc(aese(aesmc(aese
      (word_reversefields 8 (ctr_block nonce c))
      (word_reversefields 8 (EL 0 rk))))(word_reversefields 8 (EL 1 rk)))`;;

(* ===== invariant swp_inv (Q = P o [Y]) ===== *)
let swp_inv : term =
`\(i:num) s.
    read X3 s = tag_p /\
    read X4 s = ivec_p /\
    read X6 s = htable_p /\
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
    read Q28 s = word_reversefields 8 (EL 10 rk) /\
    read Q7 s = word 13979173243358019584 /\
    read Q12 s = byteswap128 (h_power (ghash_twist (aes128_cipher (word 0) rk)) 0) /\
    read Q13 s = byteswap128 (h_power (ghash_twist (aes128_cipher (word 0) rk)) 1) /\
    read Q14 s = word_join (karatsuba_mid (h_power (ghash_twist (aes128_cipher (word 0) rk)) 1))
        (karatsuba_mid (h_power (ghash_twist (aes128_cipher (word 0) rk)) 0)):int128 /\
    read Q15 s = byteswap128 (h_power (ghash_twist (aes128_cipher (word 0) rk)) 2) /\
    read Q16 s = byteswap128 (h_power (ghash_twist (aes128_cipher (word 0) rk)) 3) /\
    read Q17 s = word_join (karatsuba_mid (h_power (ghash_twist (aes128_cipher (word 0) rk)) 3))
        (karatsuba_mid (h_power (ghash_twist (aes128_cipher (word 0) rk)) 2)):int128 /\
    read X11 s = word_subword (word_reversefields 8 (ctr_block nonce c)) (0,64):int64 /\
    read X12 s = (word_zx:int32->int64) ((word_zx:int64->int32) (word_subword
        (word_reversefields 8 (ctr_block nonce c)) (64,64):int64)) /\
    read X15 s = word (len_bits DIV 8) /\
    read X16 s = word loop_remain /\
    htable_mem_4 (ghash_twist (aes128_cipher (word 0) rk)) htable_p s /\
    (forall j. j < nblocks ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
        inblock j) /\
    read X0 s = word_add in_p (word (64 * i + 64)) /\
    read X2 s = word_add out_p (word (64 * i)) /\
    read X1 s = word (loop_count - 2 - i) /\
    read X13 s = (word_zx:int32->int64) (word (4 * i + c + 4)) /\
    (forall j. j < 4 * i ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
        word_xor (aes_ctr_block c nonce rk j) (inblock j)) /\
    read (memory :> bytes128 (word_add out_p (word (64 * i + 32)))) s = word_xor (aes_ctr_block
        c nonce rk (4 * i + 2)) (inblock (4 * i + 2)) /\
    read (memory :> bytes128 (word_add out_p (word (64 * i + 48)))) s = word_xor (aes_ctr_block
        c nonce rk (4 * i + 3)) (inblock (4 * i + 3)) /\
    read Q11 s = word_xor (byteswap128 (nist_ghash (aes128_cipher (word 0) rk) tag0 (list_of_seq
        (nist_input_block inblock) (4 * i)))) (byteswap128 (word_reversefields 8 (inblock (4 *
        i)))) /\
    read Q0 s = word_join (word_subword (word_reversefields 8 (inblock (4 * i + 1)))
        (0,64):int64) (word_subword (word_reversefields 8 (inblock (4 * i + 1)))
        (64,64):int64):int128 /\
    read Q1 s = word_pmul (word_subword (word_reversefields 8 (inblock (4 * i + 3)))
        (0,64):int64) (word_subword (byteswap128 (h_power (ghash_twist (aes128_cipher (word 0)
        rk)) 0)) (64,64):int64):int128 /\
    read Q9 s = word_xor (word_pmul (word_subword (word_reversefields 8 (inblock (4 * i + 2)))
        (0,64):int64) (word_subword (byteswap128 (h_power (ghash_twist (aes128_cipher (word 0)
        rk)) 1)) (64,64):int64):int128) (word_pmul (word_subword (word_reversefields 8 (inblock
        (4 * i + 3))) (0,64):int64) (word_subword (byteswap128 (h_power (ghash_twist
        (aes128_cipher (word 0) rk)) 0)) (64,64):int64):int128) /\
    read Q31 s = word_xor (word_pmul (word_subword (word_reversefields 8 (inblock (4 * i + 2)))
        (64,64):int64) (word_subword (byteswap128 (h_power (ghash_twist (aes128_cipher (word 0)
        rk)) 1)) (0,64):int64):int128) (word_pmul (word_subword (word_reversefields 8 (inblock
        (4 * i + 3))) (64,64):int64) (word_subword (byteswap128 (h_power (ghash_twist
        (aes128_cipher (word 0) rk)) 0)) (0,64):int64):int128) /\
    read Q29 s = inblock (4 * i) /\
    read Q10 s = inblock (4 * i + 1) /\
    read Q30 s = aes2c nonce rk (4 * i + c) /\
    read (memory :> bytes128 (word_add stackpointer (word 176))) s = word_reversefields 8
        (ctr_block nonce (4 * i + c + 1)) /\
    read (memory :> bytes128 (word_add stackpointer (word 192))) s = word_reversefields 8
        (ctr_block nonce (4 * i + c + 2)) /\
    read (memory :> bytes128 (word_add stackpointer (word 208))) s = word_reversefields 8
        (ctr_block nonce (4 * i + c + 3)) /\
    read (memory :> bytes128 (word_add stackpointer (word 160))) s = word_reversefields 8
        (ctr_block nonce (4 * i + c + 4)) /\
    read X26 s = (word_zx:int32->int64) (word (4 * i + c + 7)) /\
    read Q5 s = aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc
        (aese (aesmc (aese (aesmc (aese (aesmc (aese (word_join (word_or ((word_zx:int32->int64)
        ((word_zx:int64->int32) (word_subword (word_reversefields 8 (ctr_block nonce c))
        (64,64):int64))) (word_shl ((word_zx:int32->int64) (word_bytereverse (word (4 * i + c + 1)))) 32)) (word_subword (word_reversefields 8 (ctr_block nonce c))
        (0,64):int64):int128) (word_reversefields 8 (EL 0 rk)))) (word_reversefields 8 (EL 1
        rk)))) (word_reversefields 8 (EL 2 rk)))) (word_reversefields 8 (EL 3 rk))))
        (word_reversefields 8 (EL 4 rk)))) (word_reversefields 8 (EL 5 rk))))
        (word_reversefields 8 (EL 6 rk)))) (word_reversefields 8 (EL 7 rk))))
        (word_reversefields 8 (EL 8 rk)))) (word_reversefields 8 (EL 9 rk)) /\
    read X24 s = word_or ((word_zx:int32->int64) ((word_zx:int64->int32) (word_subword
        (word_reversefields 8 (ctr_block nonce c)) (64,64):int64))) (word_shl
        ((word_zx:int32->int64) (word_bytereverse (word (4 * i + c + 5)))) 32) /\
    read Q2 s = (word_zx:int64->int128) (word_subword (word_xor (word_join (word_subword
        (word_reversefields 8 (inblock (4 * i + 3))) (0,64):int64) (word_subword
        (word_reversefields 8 (inblock (4 * i + 3))) (64,64):int64):int128)
        ((word_zx:int64->int128) (word_subword (word_reversefields 8 (inblock (4 * i + 3)))
        (0,64):int64))) (0,64):int64) /\
    read Q3 s = word_pmul (word_subword (word_reversefields 8 (inblock (4 * i + 1)))
        (0,64):int64) (word_subword (byteswap128 (h_power (ghash_twist (aes128_cipher (word 0)
        rk)) 2)) (64,64):int64):int128 /\
    read Q4 s = word_pmul (word_subword (word_xor (word_join (word_subword (word_reversefields 8
        (inblock (4 * i + 2))) (0,64):int64) (word_subword (word_reversefields 8 (inblock (4 * i
        + 2))) (64,64):int64):int128) (word_subword (word_join (word_join (word_subword
        (word_reversefields 8 (inblock (4 * i + 2))) (0,64):int64) (word_subword
        (word_reversefields 8 (inblock (4 * i + 2))) (64,64):int64):int128) (word_join
        (word_subword (word_reversefields 8 (inblock (4 * i + 2))) (0,64):int64) (word_subword
        (word_reversefields 8 (inblock (4 * i + 2))) (64,64):int64):int128):int256)
        (64,128):int128)) (64,64):int64) (karatsuba_mid (h_power (ghash_twist (aes128_cipher
        (word 0) rk)) 1)):int128 /\
    read Q6 s = word_xor (word_xor (byteswap128 (nist_ghash (aes128_cipher (word 0) rk) tag0
        (list_of_seq (nist_input_block inblock) (4 * i)))) (word_join (word_subword
        (word_reversefields 8 (inblock (4 * i))) (0,64):int64) (word_subword (word_reversefields
        8 (inblock (4 * i))) (64,64):int64):int128)) (word_subword (word_join (word_xor
        (byteswap128 (nist_ghash (aes128_cipher (word 0) rk) tag0 (list_of_seq (nist_input_block
        inblock) (4 * i)))) (word_join (word_subword (word_reversefields 8 (inblock (4 * i)))
        (0,64):int64) (word_subword (word_reversefields 8 (inblock (4 * i)))
        (64,64):int64):int128)) (word_xor (byteswap128 (nist_ghash (aes128_cipher (word 0) rk)
        tag0 (list_of_seq (nist_input_block inblock) (4 * i)))) (word_join (word_subword
        (word_reversefields 8 (inblock (4 * i))) (0,64):int64) (word_subword (word_reversefields
        8 (inblock (4 * i))) (64,64):int64):int128)):int256) (64,128):int128) /\
    read Q8 s = word_pmul (word_subword (word_xor (byteswap128 (nist_ghash (aes128_cipher (word
        0) rk) tag0 (list_of_seq (nist_input_block inblock) (4 * i)))) (word_join (word_subword
        (word_reversefields 8 (inblock (4 * i))) (0,64):int64) (word_subword (word_reversefields
        8 (inblock (4 * i))) (64,64):int64):int128)) (64,64):int64) (word_subword (byteswap128
        (h_power (ghash_twist (aes128_cipher (word 0) rk)) 3)) (64,64):int64):int128`;;

(* ===== GHASH-seed / reduce closers ===== *)
(* dec-swp BODYLEG unified closer, applied after the body stepping, the back-edge
   resolution and ENSURES_FINAL_STATE_TAC.
   Strategy: normalize arith/counters globally, then REPEAT CONJ_TAC and route each
   residual subgoal through FIRST[...] of the verified per-conjunct closers.
   Requires v5 invariant + all swp-prelude lemmas + SWP_GHASH_CORE helpers + Q5 lemmas.
   ============================================================================ *)

(* helper lemmas (proven) *)
let SWP_JOIN_IS_BSW = prove
 (`!x:int128. word_join (word_subword x (0,64):int64) (word_subword x (64,64):int64):int128 = byteswap128 x`,
  GEN_TAC THEN REWRITE_TAC[byteswap128]);;
let xor_rcancel = prove(`!a b p:int128. (word_xor a p = word_xor b p) <=> (a = b)`,
  REPEAT GEN_TAC THEN CONV_TAC WORD_BITWISE_RULE);;
let SWP_SUB_LEMMA = prove
 (`i < loop_count - 2 ==> word_sub (word (loop_count - 2 - i):int64) (word 1) = word (loop_count - 2 - (i + 1))`,
  DISCH_TAC THEN SUBGOAL_THEN `loop_count - 2 - (i + 1) = (loop_count - 2 - i) - 1` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[WORD_SUB; ARITH_RULE `i < loop_count - 2 ==> 1 <= loop_count - 2 - i`]);;
let dewrap80 = prove(`word (64 * i + 18446744073709551696):int64 = word (16 * (4 * i + 5))`,
  REWRITE_TAC[WORD_EQ; CONG; DIMINDEX_64] THEN
  REWRITE_TAC[ARITH_RULE `64 * i + 18446744073709551696 = (16 * (4 * i + 5)) + 1 * 2 EXP 64`] THEN REWRITE_TAC[MOD_MULT_ADD]);;
let dewrap96 = prove(`word (64 * i + 18446744073709551712):int64 = word (16 * (4 * i + 6))`,
  REWRITE_TAC[WORD_EQ; CONG; DIMINDEX_64] THEN
  REWRITE_TAC[ARITH_RULE `64 * i + 18446744073709551712 = (16 * (4 * i + 6)) + 1 * 2 EXP 64`] THEN REWRITE_TAC[MOD_MULT_ADD]);;
let dewrap112 = prove(`word (64 * i + 18446744073709551728):int64 = word (16 * (4 * i + 7))`,
  REWRITE_TAC[WORD_EQ; CONG; DIMINDEX_64] THEN
  REWRITE_TAC[ARITH_RULE `64 * i + 18446744073709551728 = (16 * (4 * i + 7)) + 1 * 2 EXP 64`] THEN REWRITE_TAC[MOD_MULT_ADD]);;

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
                 `[nist_input_block inblock (4*i+1); nist_input_block inblock (4*i+2); nist_input_block inblock (4*i+3)]:(int128)list`;
                 `nist_ghash (aes128_cipher (word 0) rk) tag0 (list_of_seq (nist_input_block inblock) (4*i)):int128`;
                 `nist_input_block inblock (4*i):int128`] GHASH_POLYVAL_ACC_BATCHED) THEN
  REWRITE_TAC[LENGTH; ghash_wide] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[NIST_GHASH_IS_POLYVAL] THEN
  REWRITE_TAC[ARITH_RULE `4 * i + 4 = SUC(SUC(SUC(SUC(4 * i))))`] THEN
  REWRITE_TAC[list_of_seq] THEN REWRITE_TAC[GSYM APPEND_ASSOC; APPEND] THEN
  REWRITE_TAC[GHASH_ACC_APPEND] THEN
  REWRITE_TAC[ADD1; GSYM ADD_ASSOC] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[GSYM NIST_GHASH_IS_POLYVAL] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN AP_TERM_TAC THEN CONV_TAC WORD_BITWISE_RULE);;

(* The settled-accumulator GHASH goals.  After DEC_GHASH_NORM_TAC the goal is
   `word_xor <accumulator half> pending = word_xor (byteswap128 (nist_ghash h acc [four blocks])) pending`;
   GHASH_SPLIT_TAC cancels the pending term and splits the 128-bit equation into its two 64-bit halves,
   then GHASH_GROUP_TAC closes it for one group of four blocks: the accumulator acc and the blocks blk 0..3
   are abbreviated, the goal is bridged through polyval_reduce_prop3, branch 1 is the Karatsuba
   recombination of the four partial products (KARATSUBA_JOIN_XOR4 after normalizing), and branch 2 is the
   GHASH step lemma supplied by the caller.  fold folds the input-block reads of the goal (nothing for the
   steady body, whose blocks are already inblock terms). *)
let WORD_JOIN_HALVES_CONG = prove
 (`x:int128 = y ==> word_join (word_subword x (0,64):int64) (word_subword x (64,64):int64):int128 =
                    word_join (word_subword y (0,64):int64) (word_subword y (64,64):int64):int128`,
  DISCH_THEN SUBST1_TAC THEN REFL_TAC);;

let GHASH_SPLIT_TAC : tactic =
  REWRITE_TAC[SWP_JOIN_IS_BSW] THEN REWRITE_TAC[xor_rcancel] THEN
  REWRITE_TAC [byteswap128; SWP_SUBWORD_JOIN_MID] THEN
  MATCH_MP_TAC WORD_JOIN_HALVES_CONG;;

let GHASH_GROUP_TAC (fold:tactic) (acc:term) (blk:int->term) (branch2:tactic) : tactic =
  fold THEN
  MAP_EVERY ABBREV_TAC
     [mk_eq(`sofar:int128`, acc);
      mk_eq(`cipherblock_0:int128`, blk 0); mk_eq(`cipherblock_1:int128`, blk 1);
      mk_eq(`cipherblock_2:int128`, blk 2); mk_eq(`cipherblock_3:int128`, blk 3);
      `h0 = h_power (ghash_twist (aes128_cipher (word 0) rk)) 0`; `h1 = h_power (ghash_twist (aes128_cipher (word 0) rk)) 1`;
      `h2 = h_power (ghash_twist (aes128_cipher (word 0) rk)) 2`; `h3 = h_power (ghash_twist (aes128_cipher (word 0) rk)) 3`] THEN
  REWRITE_TAC[GSYM WORD_SUBWORD_XOR] THEN REWRITE_TAC[RECONSTRUCT_POLYVAL_REDUCE_G2] THEN
  TRANS_TAC EQ_TRANS
     `polyval_reduce_prop3
          (word_xor (word_pmul (cipherblock_3:int128) (h0:int128))
          (word_xor (word_pmul (cipherblock_2:int128) (h1:int128))
          (word_xor (word_pmul (cipherblock_1:int128) (h2:int128))
          (word_pmul (word_xor (sofar:int128) cipherblock_0) (h3:int128)))))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[PMUL_KARATSUBA_JOIN_ALT] THEN REWRITE_TAC[byteswap128; WORD_SUBWORD_XOR] THEN
    CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN REWRITE_TAC[karatsuba_mid] THEN ASM_REWRITE_TAC[] THEN
    REPEAT(LET_TAC THEN ASM_REWRITE_TAC[]) THEN
    fold THEN REWRITE_TAC[INBLOCK_REASSEMBLE] THEN REWRITE_TAC[GSYM nist_input_block] THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[MESON[WORD_XOR_SYM] `word_pmul (word_xor a b) (word_xor c d) = word_pmul (word_xor b a) (word_xor c d)`] THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[POLYVAL_REDUCE_G2] THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY EXPAND_TAC ["ks"; "ks'"; "ks''"; "ks'''"] THEN
    CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN AP_TERM_TAC THEN
    REWRITE_TAC[GSYM karatsuba_join] THEN MATCH_ACCEPT_TAC KARATSUBA_JOIN_XOR4;
    MAP_EVERY EXPAND_TAC ["sofar";"cipherblock_0";"cipherblock_1";"cipherblock_2";"cipherblock_3";"h0";"h1";"h2";"h3"] THEN
    branch2];;

(* The steady body's GHASH closer: group i, accumulator nist_ghash..(4*i), blocks 4*i..4*i+3. *)
let SWP_GHASH_CORE_TAC : tactic =
  DEC_GHASH_NORM_TAC THEN GHASH_SPLIT_TAC THEN
  GHASH_GROUP_TAC ALL_TAC
    `nist_ghash (aes128_cipher (word 0) rk) tag0 (list_of_seq (nist_input_block inblock) (4 * i))`
    (fun j -> mk_comb(`nist_input_block inblock`,
                      if j = 0 then `4 * i` else mk_binop `(+):num->num->num` `4 * i` (mk_small_numeral j)))
    (ACCEPT_TAC SWP_GHASH_BRANCH2);;

(* ===== counter-cluster closers ===== *)
(* dec-swp counter-cluster closers.
   Requires: prelude (CTR_BLOCK_BUILD_INSERT, MERGE_CTR128_TAC, CTR_ZX_NORM, ZX_COUNTER_UD,
   WORD_REVERSEFIELDS_REVERSEFIELDS, WORD_SIMPLE_SUBWORD_CONV) + aes2c defined. *)
let SLOT_LANE_FOLDS = [
  WORD_RULE `word_add (word c) (word 4):int32 = word (c + 4)`;
  WORD_RULE `word_add (word (4*i+c+4)) (word 1):int32 = word(4*i+c+5)`;
  WORD_RULE `word_add (word (4*i+c+4)) (word 2):int32 = word(4*i+c+6)`;
  WORD_RULE `word_add (word (4*i+c+4)) (word 3):int32 = word(4*i+c+7)`;
  WORD_RULE `word_add (word_add (word (4*i)) (word (c+4))) (word 1):int32 = word(4*i+c+5)`;
  WORD_RULE `word_add (word_add (word (4*i)) (word (c+4))) (word 2):int32 = word(4*i+c+6)`;
  WORD_RULE `word_add (word_add (word (4*i)) (word (c+4))) (word 3):int32 = word(4*i+c+7)`;
  WORD_RULE `word_add (word_add (word (4*i)) (word (c+4))) (word 4):int32 = word(4*i+c+8)`];;
let RHS_IDX_NORMS = [
  ARITH_RULE `(4 * i + 4) + 4 = 4*i+8`; ARITH_RULE `(4 * i + 4) + 5 = 4*i+9`;
  ARITH_RULE `(4 * i + 4) + 6 = 4*i+10`; ARITH_RULE `(4 * i + 4) + 7 = 4*i+11`];;
let Q30_TAC : tactic =
  REWRITE_TAC[aes2c] THEN MERGE_CTR128_TAC 160 "s112" THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[CTR_ZX_NORM; ZX_COUNTER_UD] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[WORD_ADD] THEN REWRITE_TAC[CTR_BLOCK_BUILD_INSERT] THEN
  REWRITE_TAC[WORD_REVERSEFIELDS_REVERSEFIELDS] THEN TRY REFL_TAC THEN TRY(AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC);;
let SP160_TAC : tactic =
  MERGE_CTR128_TAC 160 "s159" THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[CTR_ZX_NORM; ZX_COUNTER_UD] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[WORD_ADD] THEN
  REWRITE_TAC[WORD_RULE `word_add (word_add (word (4 * i)) (word_add (word c) (word 4))) (word 4):int32 = word (4 * i + c + 8)`;
              WORD_RULE `word_add (word_add (word (4 * i)) (word (c + 4))) (word 4):int32 = word (4 * i + c + 8)`] THEN
  REWRITE_TAC[CTR_BLOCK_BUILD_INSERT] THEN
  REWRITE_TAC[WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
  TRY REFL_TAC THEN TRY(AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC);;
let SP_SLOT_TAC3 : tactic =
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
  REWRITE_TAC CTR_RHS_NORMS THEN REWRITE_TAC CTR_ADD_FOLDS THEN TRY REFL_TAC THEN
  TRY(AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC);;

(* ===== out-store orthogonality closers ===== *)
(* dec-swp OUT-STORE tactics: close the [0] `forall j.j<4i` preservation.
   KEY: needs `16 * nblocks <= 2 EXP 64` in scope (derivable from nblocks = len_bits DIV 128, since
   val len_bits < 2^64 => nblocks < 2^57).  Requires prelude. *)
let pth128 = prove
   (`!(a:int64) m n. 16 <= val(word_sub (word m) (word n):int64) /\ 16 <= val(word_sub (word n) (word m):int64)
          ==> orthogonal_components (bytes128 (word_add a (word m))) (bytes128 (word_add a (word n)))`,
    REPEAT STRIP_TAC THEN REWRITE_TAC[bytes128] THEN MATCH_MP_TAC ORTHOGONAL_COMPONENTS_COMPOSE_LEFT THEN
    REWRITE_TAC[ORTHOGONAL_COMPONENTS_BYTES; DIMINDEX_64] THEN
    REWRITE_TAC[VAL_WORD_ADD; DIMINDEX_64; NONOVERLAPPING_MODULO_MOD2] THEN
    MATCH_MP_TAC NONOVERLAPPING_MODULO_OFFSET_SIMPLE_BOTH THEN
    RULE_ASSUM_TAC(REWRITE_RULE[VAL_WORD_SUB_CASES; DIMINDEX_64]) THEN
    MP_TAC(ISPEC `word m:int64` VAL_BOUND) THEN MP_TAC(ISPEC `word n:int64` VAL_BOUND) THEN
    REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC);;
let orth_lemma = prove
   (`orthogonal_components c d /\ read c s' = read c s ==> read c (write d y s') = read c s`,
    MESON_TAC[orthogonal_components]);;
(* orthogonal_components (memory:>bytes128 out+16j) (memory:>bytes128 out+OFF), j<4i, bounds in scope *)
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
       [REWRITE_TAC[ARITH_RULE `2 EXP 64 = 18446744073709551616`] THEN ASM_ARITH_TAC; ALL_TAC]) THEN
    REWRITE_TAC[VAL_WORD_SUB_CASES; VAL_WORD; DIMINDEX_64] THEN
    ASM_SIMP_TAC[MOD_LT] THEN ASM_ARITH_TAC];;
let ORTH_STEP : tactic =
  FIRST [ OUT_ORTH_TAC; ORTHOGONAL_COMPONENTS_TAC;
          (MATCH_MP_TAC ORTHOGONAL_COMPONENTS_COMPOSE_RIGHT THEN CONJ_TAC THENL
            [CONV_TAC VALID_COMPONENT_CONV; ORTHOGONAL_COMPONENTS_TAC]) ];;
let rec OUT_ROW_TAC g =
  (REFL_TAC ORELSE (MATCH_MP_TAC orth_lemma THEN CONJ_TAC THENL [ORTH_STEP; OUT_ROW_TAC])) g;;
(* full [0] closer: forall j.j<4i ==> read(out+16j)sHI = word_xor(aes_ctr j)(inblock j) *)
let OUT0_TAC : tactic =
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  FIRST_ASSUM(fun th -> if (try is_forall(concl th) && free_in `out_p:int64` (concl th) && free_in `s0:armstate`(concl th) with _->false)
                        then ASSUME_TAC(SPEC `j:num` th) else NO_TAC) THEN
  FIRST_X_ASSUM(fun th -> if (try is_imp(concl th) && free_in `s0:armstate`(concl th) with _->false)
                          then ASSUME_TAC(MP th (ASSUME `j < 4 * i`)) else NO_TAC) THEN
  FIRST_X_ASSUM(fun th -> if (try is_eq(concl th) && free_in `out_p:int64`(concl th) && free_in `s0:armstate`(concl th)
                                && fst(dest_const(fst(strip_comb(lhs(concl th)))))="read" with _->false)
                          then GEN_REWRITE_TAC RAND_CONV [SYM th] else NO_TAC) THEN
  FIRST_ASSUM(fun th -> if (try not(is_eq(concl th)) && can(find_term(fun x->match x with Const("MAYCHANGE",_)->true|_->false)) (concl th) with _->false)
                        then MP_TAC th else NO_TAC) THEN
  REWRITE_TAC[MAYCHANGE; SEQ_ID; GSYM SEQ_ASSOC] THEN
  PURE_REWRITE_TAC[ASSIGNS_SEQ] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[ASSIGNS_THM; LEFT_IMP_EXISTS_THM] THEN REPEAT GEN_TAC THEN DISCH_THEN (SUBST1_TAC o SYM) THEN
  OUT_ROW_TAC;;

let dec_setup_extra : tactic =
  RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_4]) THEN REWRITE_TAC[htable_mem_4] THEN
  (fun (asl,w) ->
    let jv = `j:num` in
    let reads0 = setify(flat(map (fun (_,th) -> find_terms (fun t -> try let h,a=strip_comb t in
         fst(dest_const h)="read" && length a=2 && string_of_term(hd(tl a))="s0" with _->false) (concl th)) asl)) in
    let toab = filter (fun t -> not(free_in jv t) && not(free_in `in_p:int64` t)
                              && string_of_term t <> "read PC s0") reads0 in
    (EVERY (List.mapi (fun k t -> ABBREV_TAC (mk_eq(mk_var(Printf.sprintf "init_%d" k, type_of t), t))) toab)) (asl,w));;

(* Stepper parameters for this kernel: the memory reads at the tag, IV and Htable pointers are anchored
   (and, in the legs that also finish the output, those at the input and output pointers), as are the
   counter stack slots; REDSETX_DEC lists the registers whose latest value is carried. *)
let dec_anchors = [`tag_p:int64`; `ivec_p:int64`; `htable_p:int64`];;
let dec_anchors_io = dec_anchors @ [`in_p:int64`; `out_p:int64`];;
let ctr_slots = ["160"; "176"; "192"; "208"];;
let ctr_slots_all = ctr_slots @ ["168"; "184"; "200"; "216"];;
let REDSETX_DEC = ["Q0";"Q1";"Q2";"Q3";"Q4";"Q5";"Q6";"Q8";"Q9";"Q10";"Q11";"Q29";"Q30";"Q31";
                   "X0";"X2";"X7";"X13";"X14";"X17";"X21";"X23";"X24";"X25";"X26";"X27";"X29"];;
let steady_merges = [(17,208);(46,176);(52,192);(112,160)];;
let body_step_tac = SWP_STEPS_TAC dec_anchors ctr_slots REDSETX_DEC EXEC (K ALL_TAC) steady_merges (1--159);;

(* ---- extra closers: out-block recon (OUTBLK), in-read folder (INFOLD3), byteswap, GHASH partial ---- *)
let inp_addr_norms = List.map (fun (kk,m) ->
    WORD_RULE (subst [mk_small_numeral kk, `K:num`; mk_small_numeral m, `M:num`]
                 `word_add (in_p:int64) (word (64*i+K)):int64 = word_add in_p (word (16*(4*i+M)))`))
  [(0,0);(16,1);(32,2);(48,3);(64,4);(80,5);(96,6);(112,7)];;
(* INFOLD3: dewrap + normalize addrs to 16*(4i+m), then fold EACH in-read via the in-forall (FIRST_ASSUM keeps
   the forall so multiple reads can reuse it). blk = rand(16*blk) where off=word(16*blk). *)
let INFOLD3 : tactic =
  REWRITE_TAC[dewrap80;dewrap96;dewrap112] THEN REWRITE_TAC inp_addr_norms THEN
  (fun (asl,w) ->
    let inreads = setify(find_terms (fun t -> match t with
      | Comb(Comb(Const("read",_),Comb(Comb(Const(":>",_),Const("memory",_)),Comb(Const("bytes128",_),a))),st)
          when (free_in `in_p:int64` a && (match st with Var _->true|_->false)) -> true | _->false) w) in
    if inreads=[] then ALL_TAC (asl,w)
    else (EVERY (map (fun rd ->
       let st = rand rd in
       (* blk = the BLK in the `word (16 * BLK)` address subterm of rd *)
       let sixteenblk = rand(find_term (fun t -> match t with
           Comb(Const("word",_), n) when (try fst(dest_const(fst(strip_comb n)))="*" with _->false) -> true | _->false) rd) in
       let blk = rand sixteenblk in
       (SUBGOAL_THEN (mk_eq(rd, mk_comb(`inblock:num->int128`, blk))) ASSUME_TAC THENL
        [FIRST_ASSUM(fun fa -> if (try is_forall(concl fa) && free_in `in_p:int64`(concl fa) && free_in st (concl fa) with _->false)
                                 then MATCH_MP_TAC fa else NO_TAC) THEN ASM_ARITH_TAC; ALL_TAC]))
      inreads)) (asl,w));;
let GHASH_PARTIAL_CLOSE : tactic =
  INFOLD3 THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[INBLOCK_REASSEMBLE; GSYM nist_input_block] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[nist_input_block] THEN ASM_REWRITE_TAC[] THEN TRY REFL_TAC;;
(* read(in_p+ADDR)sK = inblock(blk): dewrap+norm then in-forall. *)
let IN_READ_CLOSE : tactic =
  REWRITE_TAC[dewrap80;dewrap96;dewrap112] THEN REWRITE_TAC inp_addr_norms THEN
  (fun (asl,w) ->
     FIRST_ASSUM(fun fa -> if (try is_forall(concl fa) && free_in `in_p:int64`(concl fa)
                                  && free_in (rand(lhs w)) (concl fa) with _->false)
                          then MATCH_MP_TAC fa else NO_TAC) (asl,w)) THEN ASM_ARITH_TAC;;
let SWP_BYTESWAP_REASSEMBLE_TAC : tactic =
  REWRITE_TAC[dewrap80;dewrap96;dewrap112] THEN INFOLD3 THEN
  REWRITE_TAC[INBLOCK_REASSEMBLE] THEN REWRITE_TAC[GSYM nist_input_block] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[nist_input_block] THEN ASM_REWRITE_TAC[] THEN TRY REFL_TAC;;
(* block-4i/4i+1 out-store via aes2c(4i+2): unfold aes2c, reconstruct AES tower to aes_ctr_block. *)
let AES2C_OUT_TAC : tactic =
  REWRITE_TAC[aes2c] THEN REWRITE_TAC[XOR_AES128_CIPHER_RECONSTRUCT_DEC] THEN
  REWRITE_TAC[WORD_REVERSEFIELDS_REVERSEFIELDS] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM aes_ctr_block] THEN REWRITE_TAC[MAP] THEN
  REWRITE_TAC[WORD_REVERSEFIELDS_REVERSEFIELDS] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[aes_ctr_block] THEN
  REWRITE_TAC[ARITH_RULE `4*i+2 = (4*i)+2`; ARITH_RULE `(4*i+1)+2 = 4*i+3`] THEN
  REWRITE_TAC[CTR_BLOCK_BUILD_INSERT] THEN REWRITE_TAC[WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
  REWRITE_TAC[ARITH_RULE `4*i+3 = (4*i+1)+2`] THEN REWRITE_TAC[GSYM aes_ctr_block] THEN TRY REFL_TAC;;
(* frame (,, s0 sN): use the asl MAYCHANGE-seq fact + subsumption. *)
let pth_frame = prove(`R s s' ==> R subsumed R' ==> R' s s'`, REWRITE_TAC[subsumed] THEN MESON_TAC[]);;
let close_goal10 : tactic =
  fun (asl,w) ->
    let frame_th = try snd(List.find (fun (_,th) -> let c=concl th in
        (try not(is_eq c) && can(find_term(fun x->match x with Const("MAYCHANGE",_)->true|_->false)) c
            && (match c with Comb(Comb(_,a),b) -> is_var a && is_var b | _->false) with _->false)) asl)
      with _ -> failwith "close_goal10: no frame asm" in
    (MATCH_MP_TAC(MATCH_MP pth_frame frame_th) THEN
     REWRITE_TAC[ETA_AX; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN SUBSUMED_MAYCHANGE_TAC) (asl,w);;
(* out-block recon: addr rewrite param + reconstruct + counter-collapse (handles +96/+112).
   GUARD: fail-fast unless this closer's own offset (addr_rule LHS, e.g. 64*i+96 or
   64*i+112) actually occurs in the goal.  Without this, FIRST[close_outahead96;
   close_outahead112] on the +112 goal runs close_outahead96's addr_rule as a no-op but
   still executes the rest of OUTBLK_TAC, which mangles/errors ("MATCH_MP_TAC: No match"
   via the GHASH fallback) before close_outahead112 is ever tried. *)
let OUTBLK_TAC (addr_rule:thm) : tactic =
  fun (asl,w) ->
    if not (free_in (lhs(concl addr_rule)) w)
    then failwith "OUTBLK_TAC: offset absent" else
   (REWRITE_TAC[addr_rule] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[dewrap80;dewrap96;dewrap112] THEN INFOLD3 THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[XOR_AES128_CIPHER_RECONSTRUCT_DEC] THEN
  REWRITE_TAC[WORD_REVERSEFIELDS_REVERSEFIELDS] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM aes_ctr_block] THEN REWRITE_TAC[MAP] THEN
  REWRITE_TAC[WORD_REVERSEFIELDS_REVERSEFIELDS] THEN ASM_REWRITE_TAC[] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[aes_ctr_block] THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[ZX_COUNTER_UD; CTR_ZX_NORM] THEN
  REWRITE_TAC[WORD_RULE `word_add (word (4*i+c+4)) (word 2):int32 = word(4*i+c+6)`;
              WORD_RULE `word_add (word (4*i+7)) (word 2):int32 = word(4*i+9)`] THEN
  REWRITE_TAC[CTR_BLOCK_BUILD_INSERT] THEN REWRITE_TAC[WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
  REWRITE_TAC[ARITH_RULE `4*i+8 = (4*i+6)+2`; ARITH_RULE `4*i+9 = (4*i+7)+2`] THEN
  REWRITE_TAC[GSYM aes_ctr_block] THEN TRY REFL_TAC) (asl,w);;
let close_outahead96 : tactic = OUTBLK_TAC (ARITH_RULE `64 * i + 96 = (64 * i + 64) + 32`);;
let close_outahead112 : tactic = OUTBLK_TAC (ARITH_RULE `64 * i + 112 = (64 * i + 64) + 48`);;

(* Q8 settled partial (word_pmul head): peel the pmul(subword) on the RAW conjunct then core. *)
let SWP_Q8_TAC : tactic = AP_THM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN SWP_GHASH_CORE_TAC;;
(* Q6 compound (word_xor head, seed appears twice): BINOP split -> g0 core, g1 subword-join -> AP_THM/AP_TERM
   then re-split to subword-level + core (or BINOP again). *)
let SWP_Q6_FULL_TAC : tactic =
  BINOP_TAC THENL
   [SWP_GHASH_CORE_TAC;
    AP_THM_TAC THEN AP_TERM_TAC THEN
    (SWP_GHASH_CORE_TAC ORELSE (BINOP_TAC THEN SWP_GHASH_CORE_TAC))];;

(* master closer: shape-gated, most-specific first. SWP_GHASH_CORE_TAC for the big GHASH reduces. *)
let CLOSE_V8 : tactic =
  fun (asl,w) ->
    let has c t = can (find_term (fun u -> try fst(dest_const(fst(strip_comb u)))=c with _->false)) t in
    let has_mc t = try can(find_term(fun x->match x with Const("MAYCHANGE",_)->true|_->false)) t with _->false in
    let hd t = try fst(dest_const(fst(strip_comb t))) with _->"" in
    let rh c = try has c (rhs w) with _->false in
    if has_mc w then close_goal10 (asl,w)
    else if has "aligned_bytes_loaded" w then ASM_REWRITE_TAC[] (asl,w)
    else if is_eq w && rh "aes2c" then MUST_PROGRESS Q30_TAC (asl,w)
    else if is_eq w && hd(lhs w)="read" && rh "inblock" && not(rh "word_xor") && not(rh "aes_ctr_block") then MUST_PROGRESS IN_READ_CLOSE (asl,w)
    else if is_eq w && hd(lhs w)="read" && rh "ctr_block" && rh "word_reversefields" then MUST_PROGRESS SP160_TAC (asl,w)
    else if is_eq w && hd(lhs w)="word_join" && rh "ctr_block" && rh "word_reversefields" then MUST_PROGRESS SP_SLOT_TAC3 (asl,w)
    else if is_eq w && (hd(lhs w)="word_or" || (hd(lhs w)="word_zx" && String.length(string_of_term w)<200)) then MUST_PROGRESS CTRREG_TAC (asl,w)
    else if is_forall w then MUST_PROGRESS OUT0_TAC (asl,w)
    else if is_eq w && hd(lhs w)="read" && rh "aes_ctr_block" then MUST_PROGRESS (FIRST[close_outahead96; close_outahead112]) (asl,w)
    (* GHASH-reduce goals: RHS mentions nist_ghash (settled accumulator). Peel on RAW then SWP_GHASH_CORE_TAC. *)
    else if is_eq w && rh "nist_ghash" && hd(lhs w)="word_pmul" then MUST_PROGRESS (FIRST[SWP_Q8_TAC; SWP_GHASH_CORE_TAC]) (asl,w)
    else if is_eq w && rh "nist_ghash" && hd(lhs w)="word_xor" then MUST_PROGRESS (FIRST[SWP_GHASH_CORE_TAC; SWP_Q6_FULL_TAC]) (asl,w)
    else if is_eq w && rh "nist_ghash" then MUST_PROGRESS SWP_GHASH_CORE_TAC (asl,w)
    (* aes2c-based out-store readback: LHS = word_xor(inblock)(word_xor(rk10)(aese-tower)), RHS = word_xor(aes_ctr_block)(inblock) *)
    else if is_eq w && rh "aes_ctr_block" && (has "aes2c" w || has "aese" (lhs w)) then MUST_PROGRESS AES2C_OUT_TAC (asl,w)
    (* byteswap reassembly / Karatsuba partials over reassembled input blocks *)
    else if is_eq w && hd(lhs w)="word_join" then MUST_PROGRESS (FIRST[SWP_BYTESWAP_REASSEMBLE_TAC; GHASH_PARTIAL_CLOSE]) (asl,w)
    else MUST_PROGRESS (FIRST[GHASH_PARTIAL_CLOSE; AES2C_OUT_TAC; SWP_GHASH_CORE_TAC; CTRREG_TAC; ASM_REWRITE_TAC[] THEN TRY REFL_TAC]) (asl,w)
     ;;

(* ---- Leg goals ---- *)
(* Every leg is stated with the main theorem's frame (swp_frame) and with state predicates of the form
   \s. aligned_bytes_loaded s (word pc) mc /\ read PC s = word (pc + off) /\ <body>, which is how
   ENSURES_SEQUENCE_TAC and ENSURES_WHILE_UP_TAC present the leaf goals of the main theorem; the entry
   (0xa0) and exit (0xaa0) mid-conditions are shared with the main theorem below.  A leg then discharges
   its leaf goal by MATCH_MP_TAC (see APPLY_LEG). *)
let ap inv i s = rhs(concl(REDEPTH_CONV BETA_CONV (list_mk_comb(inv,[i;s]))));;
let leg_state off body =
  mk_abs(`s:armstate`,
    list_mk_conj(`aligned_bytes_loaded s (word pc) aes128_gcm_dec_mc` ::
                 mk_eq(`read PC s`, mk_comb(`word:num->int64`, mk_binop `+` `pc:num` off)) ::
                 conjuncts body));;
let inv_state off idx = leg_state off (ap swp_inv idx `s:armstate`);;
let swp_frame = `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
    MAYCHANGE [X19; X20; X21; X22; X23; X24; X25; X26; X27; X28; X29; X30] ,,
    MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
    MAYCHANGE [memory :> bytes(out_p, 16 * nblocks); memory :> bytes(tag_p, 16);
               memory :> bytes(ivec_p, 16); memory :> bytes(word_add stackpointer (word 160), 64)]`;;
let leg_goal vars hyps pre post =
  list_mk_forall(vars, mk_imp(hyps, list_mk_comb(`ensures arm`, [pre; post; swp_frame])));;

(* The hypotheses of the steady body leg; the other legs replace the loop-index bound by their own
   constraint on loop_count.  key_p occurs only here, so a leg applied by MATCH_MP_TAC leaves ?key_p. *)
let leg_hyps = `aligned 16 (stackpointer:int64) /\
    nblocks DIV 4 = loop_count /\ nblocks MOD 4 = loop_remain /\
    16 * nblocks <= 2 EXP 64 /\
    ([EL 0 rk; EL 1 rk; EL 2 rk; EL 3 rk; EL 4 rk; EL 5 rk; EL 6 rk; EL 7 rk; EL 8 rk; EL 9 rk; EL 10 rk]:(int128)list = rk) /\
    i < loop_count - 2 /\
    nonoverlapping ((out_p:int64), 16 * nblocks) (word pc, 2988) /\
    nonoverlapping (word_add (stackpointer:int64) (word 160), 64) (word pc, 2988) /\
    nonoverlapping (word_add (stackpointer:int64) (word 160), 64) ((key_p:int64), 176) /\
    nonoverlapping (word_add (stackpointer:int64) (word 160), 64) ((htable_p:int64), 192) /\
    nonoverlapping ((out_p:int64), 16 * nblocks) ((in_p:int64), 16 * nblocks) /\
    nonoverlapping ((in_p:int64), 16 * nblocks) (word_add (stackpointer:int64) (word 160), 64) /\
    nonoverlapping ((out_p:int64), 16 * nblocks) (word_add (stackpointer:int64) (word 160), 64) /\
    nonoverlapping ((tag_p:int64), 16) ((out_p:int64), 16 * nblocks) /\
    nonoverlapping ((tag_p:int64), 16) (word_add (stackpointer:int64) (word 160), 64) /\
    nonoverlapping ((ivec_p:int64), 16) ((out_p:int64), 16 * nblocks) /\
    nonoverlapping ((ivec_p:int64), 16) (word_add (stackpointer:int64) (word 160), 64) /\
    nonoverlapping ((htable_p:int64), 192) ((out_p:int64), 16 * nblocks) /\
    nonoverlapping ((htable_p:int64), 192) (word_add (stackpointer:int64) (word 160), 64)`;;
let vs = [`in_p:int64`;`out_p:int64`;`len_bits:int64`;`tag_p:int64`;`ivec_p:int64`;`key_p:int64`;`htable_p:int64`;
          `tag0:int128`;`nonce:int128`;`rk:(int128)list`;`inblock:num->int128`;`pc:num`;
          `stackpointer:int64`;`nblocks:num`;`loop_count:num`;`loop_remain:num`];;
let base_hyps = filter (fun t -> not (t = `i < loop_count - 2`) && not (t = `3 <= loop_count`)) (conjuncts leg_hyps);;

(* The 0xa0 entry state (after the register setup) and the 0xaa0 exit state (after the pipelined
   loop, before the single-block tail loop), as used by the legs and by the main theorem. *)
let entry_body = `read X0 s = in_p /\ read X2 s = out_p /\ read X3 s = tag_p /\ read X4 s = ivec_p /\
    read X6 s = htable_p /\ read SP s = stackpointer /\
    read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
    read (memory :> bytes128 ivec_p) s = word_reversefields 8 (ctr_block nonce c) /\
    read Q18 s = word_reversefields 8 (EL 0 rk) /\ read Q19 s = word_reversefields 8 (EL 1 rk) /\
    read Q20 s = word_reversefields 8 (EL 2 rk) /\ read Q21 s = word_reversefields 8 (EL 3 rk) /\
    read Q22 s = word_reversefields 8 (EL 4 rk) /\ read Q23 s = word_reversefields 8 (EL 5 rk) /\
    read Q24 s = word_reversefields 8 (EL 6 rk) /\ read Q25 s = word_reversefields 8 (EL 7 rk) /\
    read Q26 s = word_reversefields 8 (EL 8 rk) /\ read Q27 s = word_reversefields 8 (EL 9 rk) /\
    read Q28 s = word_reversefields 8 (EL 10 rk) /\
    read Q12 s = byteswap128 (h_power (ghash_twist (aes128_cipher (word 0) rk)) 0) /\
    read Q13 s = byteswap128 (h_power (ghash_twist (aes128_cipher (word 0) rk)) 1) /\
    read Q14 s = word_join (karatsuba_mid (h_power (ghash_twist (aes128_cipher (word 0) rk)) 1)) (karatsuba_mid (h_power (ghash_twist (aes128_cipher (word 0) rk)) 0)) /\
    read Q15 s = byteswap128 (h_power (ghash_twist (aes128_cipher (word 0) rk)) 2) /\
    read Q16 s = byteswap128 (h_power (ghash_twist (aes128_cipher (word 0) rk)) 3) /\
    read Q17 s = word_join (karatsuba_mid (h_power (ghash_twist (aes128_cipher (word 0) rk)) 3)) (karatsuba_mid (h_power (ghash_twist (aes128_cipher (word 0) rk)) 2)) /\
    read Q7 s = word 13979173243358019584 /\
    read X11 s = word_subword (word_reversefields 8 (ctr_block nonce c):int128) (0,64):int64 /\
    read X12 s = word_zx (word_zx (word_subword (word_reversefields 8 (ctr_block nonce c):int128) (64,64):int64):int32):int64 /\
    read X13 s = word_zx (word c:int32):int64 /\
    read X15 s = word(len_bits DIV 8) /\ read X1 s = word loop_count /\
    read X7 s = word nblocks /\ read X16 s = word loop_remain /\
    read Q30 s = byteswap128 tag0 /\
    htable_mem_4 (ghash_twist (aes128_cipher (word 0) rk)) htable_p s /\
    (!j. j < nblocks ==> read (memory :> bytes128 (word_add in_p (word(16*j)))) s = inblock j)`;;
let entry_state = leg_state `0xa0` entry_body;;

let exit_body = `read X0 s = word_add in_p (word (64 * loop_count)) /\
   read X2 s = word_add out_p (word (64 * loop_count)) /\
   read X3 s = tag_p /\ read X4 s = ivec_p /\ read X6 s = htable_p /\ read SP s = stackpointer /\
   read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
   read (memory :> bytes128 ivec_p) s = word_reversefields 8 (ctr_block nonce c) /\
   read Q18 s = word_reversefields 8 (EL 0 rk) /\ read Q19 s = word_reversefields 8 (EL 1 rk) /\
   read Q20 s = word_reversefields 8 (EL 2 rk) /\ read Q21 s = word_reversefields 8 (EL 3 rk) /\
   read Q22 s = word_reversefields 8 (EL 4 rk) /\ read Q23 s = word_reversefields 8 (EL 5 rk) /\
   read Q24 s = word_reversefields 8 (EL 6 rk) /\ read Q25 s = word_reversefields 8 (EL 7 rk) /\
   read Q26 s = word_reversefields 8 (EL 8 rk) /\ read Q27 s = word_reversefields 8 (EL 9 rk) /\
   read Q28 s = word_reversefields 8 (EL 10 rk) /\
   read Q12 s = byteswap128 (h_power (ghash_twist (aes128_cipher (word 0) rk)) 0) /\
   read Q13 s = byteswap128 (h_power (ghash_twist (aes128_cipher (word 0) rk)) 1) /\
   read Q14 s = word_join (karatsuba_mid (h_power (ghash_twist (aes128_cipher (word 0) rk)) 1)) (karatsuba_mid (h_power (ghash_twist (aes128_cipher (word 0) rk)) 0)) /\
   read Q15 s = byteswap128 (h_power (ghash_twist (aes128_cipher (word 0) rk)) 2) /\
   read Q16 s = byteswap128 (h_power (ghash_twist (aes128_cipher (word 0) rk)) 3) /\
   read Q17 s = word_join (karatsuba_mid (h_power (ghash_twist (aes128_cipher (word 0) rk)) 3)) (karatsuba_mid (h_power (ghash_twist (aes128_cipher (word 0) rk)) 2)) /\
   read Q7 s = word 13979173243358019584 /\
   read X11 s = word_subword (word_reversefields 8 (ctr_block nonce c):int128) (0,64):int64 /\
   read X12 s = word_zx (word_zx (word_subword (word_reversefields 8 (ctr_block nonce c):int128) (64,64):int64):int32):int64 /\
   read X13 s = word_zx (word (4 * loop_count + c):int32):int64 /\
   read X15 s = word(len_bits DIV 8) /\ read X16 s = word loop_remain /\
   read Q30 s = byteswap128 (nist_ghash (aes128_cipher (word 0) rk) tag0 (list_of_seq (nist_input_block inblock) (4 * loop_count))) /\
   htable_mem_4 (ghash_twist (aes128_cipher (word 0) rk)) htable_p s /\
   (!j. j < nblocks ==> read (memory :> bytes128 (word_add in_p (word(16*j)))) s = inblock j) /\
   (!j. j < 4 * loop_count ==> read (memory :> bytes128 (word_add out_p (word(16*j)))) s = word_xor (aes_ctr_block c nonce rk j) (inblock j))`;;
let exit_state = leg_state `0xaa0` exit_body;;

let bodyleg_goal = leg_goal (vs @ [`i:num`]) leg_hyps (inv_state `0x294` `i:num`) (inv_state `0x510` `i + 1`);;

(* ===== drain GHASH composition lemmas ===== *)
(* ============================================================================
   DRAIN Q30 composition lemmas: settle the depth-2 (2-group) GHASH reduce by
   splitting it into two single-group reduces (John's decomposition).  All proven
   axiom-free from GHASH_POLYVAL_ACC_BATCHED / NIST_GHASH_APPEND / list_of_seq.
   Load AFTER RESTORE_dec_session.ml (needs those + swp_closer_cleanhalf).
   ============================================================================ *)

(* SETTLED branch2: acc presented as the settled accumulator nist_ghash..(list_of_seq..(4*k)); RHS is the
   NEXT settled accumulator nist_ghash..(list_of_seq..(4*k+4)) -- exactly the byteswap-split goal's RHS form
   (unlike _GEN which yields nist_ghash h acc [4 explicit blocks], not syntactically the list_of_seq form).
   This is BODYLEG's SWP_GHASH_BRANCH2 generalized from the literal 4*i to an arbitrary 4*k. *)
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
                 `[nist_input_block inblock (4*k+1); nist_input_block inblock (4*k+2); nist_input_block inblock (4*k+3)]:(int128)list`;
                 `nist_ghash (aes128_cipher (word 0) rk) tag0 (list_of_seq (nist_input_block inblock) (4*k)):int128`;
                 `nist_input_block inblock (4*k):int128`] GHASH_POLYVAL_ACC_BATCHED) THEN
  REWRITE_TAC[LENGTH; ghash_wide] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[NIST_GHASH_IS_POLYVAL] THEN
  REWRITE_TAC[ARITH_RULE `4 * k + 4 = SUC(SUC(SUC(SUC(4 * k))))`] THEN
  REWRITE_TAC[list_of_seq] THEN REWRITE_TAC[GSYM APPEND_ASSOC; APPEND] THEN
  REWRITE_TAC[GHASH_ACC_APPEND] THEN
  REWRITE_TAC[ADD1; GSYM ADD_ASSOC] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[GSYM NIST_GHASH_IS_POLYVAL] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN AP_TERM_TAC THEN CONV_TAC WORD_BITWISE_RULE);;

(* Canonicalize num-equal counter mismatches a closer may leave (base/assoc differ, e.g.
   aes_ctr_block (c+1) rk (4*i) vs c rk (4*i+1);  ctr_block nonce (4*i+c+K) vs ((4*i+K)+c)).
   Fold built blocks, unfold aes_ctr_block, peel word-structure to the counter nums, close by ARITH. *)
let CTR_CANON_TAC : tactic =
  REWRITE_TAC[CTR_BLOCK_BUILD_INSERT; WORD_REVERSEFIELDS_REVERSEFIELDS; aes_ctr_block] THEN
  REWRITE_TAC[ARITH_RULE `(4 * i + 1) + c = 4 * i + c + 1`; ARITH_RULE `(4 * i + 2) + c = 4 * i + c + 2`;
              ARITH_RULE `(4 * i + 3) + c = 4 * i + c + 3`; ARITH_RULE `(4 * i + 4) + c = 4 * i + c + 4`;
              ARITH_RULE `(4 * i + 5) + c = 4 * i + c + 5`; ARITH_RULE `(4 * i + 6) + c = 4 * i + c + 6`;
              ARITH_RULE `(4 * i + 7) + c = 4 * i + c + 7`;
              ARITH_RULE `4 * i + (c + 4) + 4 = 4 * i + c + 8`;
              ARITH_RULE `4 * i + (c + 5) + 4 = 4 * i + c + 9`] THEN
  TRY REFL_TAC;;
let SWP_DEC_BODYLEG = prove(bodyleg_goal,
  REPEAT STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
  SUBGOAL_THEN `4*i+7 < nblocks` ASSUME_TAC THENL
   [SUBST1_TAC(SYM(ASSUME `nblocks DIV 4 = loop_count`)) THEN
    MP_TAC(SPECL [`nblocks:num`;`4`] DIVISION) THEN
    UNDISCH_TAC `i < loop_count - 2` THEN SUBST1_TAC(SYM(ASSUME `nblocks DIV 4 = loop_count`)) THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `read (memory :> bytes128 (word_add in_p (word (64*i+64)))) s0 = inblock (4*i+4) /\
    read (memory :> bytes128 (word_add in_p (word (64*i+80)))) s0 = inblock (4*i+5) /\
    read (memory :> bytes128 (word_add in_p (word (64*i+96)))) s0 = inblock (4*i+6) /\
    read (memory :> bytes128 (word_add in_p (word (64*i+112)))) s0 = inblock (4*i+7)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [SUBST1_TAC(WORD_RULE `word_add in_p (word (64*i+64)):int64 = word_add in_p (word (16*(4*i+4)))`);
      SUBST1_TAC(WORD_RULE `word_add in_p (word (64*i+80)):int64 = word_add in_p (word (16*(4*i+5)))`);
      SUBST1_TAC(WORD_RULE `word_add in_p (word (64*i+96)):int64 = word_add in_p (word (16*(4*i+6)))`);
      SUBST1_TAC(WORD_RULE `word_add in_p (word (64*i+112)):int64 = word_add in_p (word (16*(4*i+7)))`)] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  dec_setup_extra THEN
  body_step_tac THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ARITH_RULE `j < 4 * (i + 1) <=>
                          j < 4 * i \/ j = 4 * i \/ j = 4 * i + 1 \/ j = 4 * i + 2 \/ j = 4 * i + 3`] THEN
  ASM_REWRITE_TAC[TAUT `p \/ q ==> r <=> (p ==> r) /\ (q ==> r)`] THEN
  REWRITE_TAC[FORALL_AND_THM; FORALL_UNWIND_THM2] THEN
  REWRITE_TAC[ARITH_RULE `16 * (4 * a + b) = 64 * a + 16 * b`] THEN
  REWRITE_TAC[ARITH_RULE `16 * 4 * i = 64 * i`] THEN
  CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ZX_COUNTER_UD; ZX_COUNTER_INC; CTR_ZX_NORM] THEN
  REWRITE_TAC[ARITH_RULE `4 * (i + 1) = 4 * i + 4`; ARITH_RULE `64 * (i + 1) = 64 * i + 64`;
              ARITH_RULE `(4 * i + 4) + 1 = 4 * i + 5`; ARITH_RULE `(4 * i + 4) + 2 = 4 * i + 6`;
              ARITH_RULE `(4 * i + 4) + 3 = 4 * i + 7`;
              ARITH_RULE `(4 * i + 4) + c = 4 * i + c + 4`; ARITH_RULE `(4 * i + 4) + c + 1 = 4 * i + c + 5`;
              ARITH_RULE `(4 * i + 4) + c + 2 = 4 * i + c + 6`; ARITH_RULE `(4 * i + 4) + c + 3 = 4 * i + c + 7`;
              ARITH_RULE `(64 * i + 64) + 64 = 64 * i + 128`;
              ARITH_RULE `(64 * i + 64) + 32 = 64 * i + 96`;
              ARITH_RULE `(64 * i + 64) + 48 = 64 * i + 112`;
              ARITH_RULE `(4 * i + 4) + 6 = 4 * i + 10`;  ARITH_RULE `(4 * i + 4) + 9 = 4 * i + 13`] THEN
  REWRITE_TAC[WORD_RULE `word_add (word (4 * i)) (word_add (word c) (word 4)):int32 = word (4 * i + c + 4)`;
              WORD_RULE `word_add (word (4 * i + c + 4)) (word 4):int32 = word(4 * i + c + 8)`] THEN
  ASM_SIMP_TAC[SWP_SUB_LEMMA] THEN
  REPEAT CONJ_TAC THEN CLOSE_V8 THEN TRY CTR_CANON_TAC)
  ;;

(* ================= FILL: entry -> inv 0  (0xa0 -> 0x294) ================= *)
(* shared with DRAIN: REV64_16B_IS_BSW_REVFIELDS. *)
let fill_hyps = subst [`3 <= loop_count`, `i < loop_count - 2`] leg_hyps;;
let fill_goal = leg_goal vs fill_hyps entry_state (inv_state `0x294` `0`);;

(* ---- branch-resolution lemmas for the two guards at 0xa4/0xa8 (b.eq iter_1) and 0x290 (cbz drain) ---- *)
let branch_lem = prove(
  `3 <= loop_count /\ loop_count < 2 EXP 64
   ==> (val(word_sub (word loop_count:int64) (word 1)) = 0 <=> F)`,
  STRIP_TAC THEN REWRITE_TAC[VAL_EQ_0; WORD_SUB_EQ_0] THEN
  DISCH_THEN(MP_TAC o AP_TERM `val:int64->num`) THEN
  SUBGOAL_THEN `val(word loop_count:int64) = loop_count` SUBST1_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN ASM_REWRITE_TAC[DIMINDEX_64]; ALL_TAC] THEN
  REWRITE_TAC[VAL_WORD_1] THEN UNDISCH_TAC `3 <= loop_count` THEN ARITH_TAC);;

(* bridge: the machine rev64.16b(block) = byteswap128(word_reversefields 8 block); needed to close the
   i=0 GHASH seed (Q11) whose FILL machine value is rev64.16b(inblock 0) but the invariant writes it as
   byteswap128(word_reversefields 8 (inblock 0)). *)
let REV64_16B_IS_BSW_REVFIELDS = prove(
  `word_join (word_bytereverse (word_subword (x:int128) (64,64):int64):int64)
             (word_bytereverse (word_subword (x:int128) (0,64):int64):int64):int128
   = byteswap128 (word_reversefields 8 x)`,
  GEN_REWRITE_TAC I [WORD_EQ_BITS_ALT] THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  POP_ASSUM MP_TAC THEN SPEC_TAC(`k:num`,`k:num`) THEN
  REWRITE_TAC[GSYM WORD_EQ_BITS_ALT] THEN REWRITE_TAC[byteswap128] THEN
  CONV_TAC(BINOP_CONV(RAND_CONV(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV))) THEN
  CONV_TAC BITBLAST_RULE);;

(* FILL per-conjunct closer.  Applied AFTER the goal-level arith-normalization pass, so conjuncts
   are in `inblock k` / literal-offset form (same shape CLOSE_V8 expects from BODYLEG).  The Q11 seed
   at i=0 additionally needs nist_ghash..0 -> tag0 (empty Horner); handle it explicitly first. *)


(* ks9 counter-base lemma: the inline staged-counter for block 3 (i=0) = revfields8(ctr_block nonce 3).
   Lets the machine Q5 keystream (base = read(sp+176) = revfields8(ctr_block nonce 3) via the invariant's
   own sp+176 conjunct) match the invariant ks9's inline-counter base inside the 9-round AES tower. *)
let KS9_CTRBASE_0 = mk_cbv `c + 1`;;

(* counter-base folds with the REDUCED shl-numeral (the stepping reduces word_shl(word_bytereverse(word k))32
   to a numeral): the FILL staged counter-lane join = word_reversefields 8 (ctr_block nonce K) for K=2..6. *)
let CTRBASEN = end_itlist CONJ (map mk_cbv [`c:num`; `c + 1`; `c + 2`; `c + 3`; `c + 4`]);;

(* FILL per-conjunct closer.  8 shape-specific branches. *)
(* Blast guards: WORD_BLAST / WORD_RULE explode on the symbolic counter c, so only apply them when c
   is absent from the goal (i.e. the GHASH conjuncts).  Counter conjuncts are closed at the NUM level. *)
let CBLAST : tactic = fun (asl,w) ->
  if free_in `c:num` w then failwith "CBLAST: symbolic c present (would explode)" else CONV_TAC WORD_BLAST (asl,w);;
let CRULE : tactic = fun (asl,w) ->
  if free_in `c:num` w then failwith "CRULE: symbolic c present" else CONV_TAC WORD_RULE (asl,w);;
(* Close a counter-goal num-index mismatch (word_reversefields/ctr_block/aes2c/aes_ctr_block over
   c-expressions): canonicalize 0+c, then REFL or peel the function layers to the num arg and ARITH.
   Never blasts, so it is safe on the symbolic counter. *)
let CTR_NUM_CLOSE : tactic =
  REWRITE_TAC[ADD_CLAUSES] THEN
  (REFL_TAC ORELSE (REPEAT (AP_TERM_TAC ORELSE AP_THM_TAC) THEN (REFL_TAC ORELSE ARITH_TAC)));;
let FILL_CLOSE : tactic =
  FIRST
   [ (* i=0 counter registers (word_zx/word_or of word c): collapse zx-nest, fold word_add, canon 0+c, NUM close *)
     (REWRITE_TAC[ZX_COUNTER_UD; ZX_COUNTER_INC; CTR_ZX_NORM] THEN REWRITE_TAC[GSYM WORD_ADD] THEN
      REWRITE_TAC[ADD_CLAUSES] THEN CTR_NUM_CLOSE THEN NO_TAC);
     (* GHASH (seed Q11 + partials): reassembly + ghash-nil + byteswap + bridge + WORD_BLAST (c absent) *)
     (REWRITE_TAC[INBLOCK_REASSEMBLE; list_of_seq; nist_ghash] THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[byteswap128] THEN CBLAST THEN NO_TAC);
     (REWRITE_TAC[INBLOCK_REASSEMBLE; list_of_seq; nist_ghash] THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[REV64_16B_IS_BSW_REVFIELDS; byteswap128] THEN CBLAST THEN NO_TAC);
     (* counter stack slots (word_join -> ctr_block): zx-norm + CTRBASEN fold + NUM close (no blast) *)
     (ASM_REWRITE_TAC[] THEN REWRITE_TAC[ZX_COUNTER_UD; ZX_COUNTER_INC; CTR_ZX_NORM] THEN
      REWRITE_TAC[GSYM WORD_ADD] THEN REWRITE_TAC[ADD_CLAUSES] THEN REWRITE_TAC[CTRBASEN; KS9_CTRBASE_0] THEN
      REWRITE_TAC[WORD_REVERSEFIELDS_REVERSEFIELDS] THEN CTR_NUM_CLOSE THEN NO_TAC);
     (* Q30/ks9 aes towers -> aes2c: MERGE base, fold counter, aes2c, NUM close (no blast) *)
     ((MERGE_CTR128_TAC 160 "s77" ORELSE ALL_TAC) THEN (MERGE_CTR128_TAC 176 "s29" ORELSE ALL_TAC) THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[ZX_COUNTER_UD; ZX_COUNTER_INC; CTR_ZX_NORM] THEN
      REWRITE_TAC[GSYM WORD_ADD] THEN REWRITE_TAC[ADD_CLAUSES] THEN REWRITE_TAC[CTRBASEN; KS9_CTRBASE_0] THEN
      REWRITE_TAC[aes2c] THEN CTR_NUM_CLOSE THEN NO_TAC);
     (* out-stores blk2,3: MERGE base, fold counter, DEC readback recon, aes_ctr_block, NUM close (no blast) *)
     ((MERGE_CTR128_TAC 192 "s32" ORELSE ALL_TAC) THEN (MERGE_CTR128_TAC 208 "s18" ORELSE ALL_TAC) THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[ZX_COUNTER_UD; ZX_COUNTER_INC; CTR_ZX_NORM] THEN
      REWRITE_TAC[GSYM WORD_ADD] THEN REWRITE_TAC[ADD_CLAUSES] THEN REWRITE_TAC[CTRBASEN] THEN
      REWRITE_TAC[XOR_AES128_CIPHER_RECONSTRUCT_DEC] THEN REWRITE_TAC[MAP; WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[aes_ctr_block] THEN CTR_NUM_CLOSE THEN NO_TAC);
     (* word_sub loop-count *)
     (SUBGOAL_THEN `2 <= loop_count` ASSUME_TAC THENL [ASM_ARITH_TAC; ASM_SIMP_TAC[WORD_SUB]] THEN NO_TAC);
     (* MAYCHANGE frame *)
     (close_goal10 THEN NO_TAC);
     (* trivial registers / htable (post htable-unfold, the 4 reads close by ASM) *)
     (ASM_REWRITE_TAC[] THEN TRY REFL_TAC THEN NO_TAC);
     (ASM_REWRITE_TAC[] THEN CRULE THEN NO_TAC) ];;

(* Counter-slot store sites in the fill (MERGE_CTR128_TAC after these steps). *)
let fill_merges = [(10,160);(12,176);(15,208);(21,192)];;

(* ------------------------------------------------------------------ *)
(* Shared pre-branch fill leg (0xa0 -> 0x290, establishes inv 0, hyp 2 <= loop_count). *)
(* FILLLEG and LC2-PARTA both bridge one branch step off this shared leg. *)
(* ------------------------------------------------------------------ *)

(* branch_lem restated for the shared leg's weaker hypothesis 2 <= loop_count: the b.eq at 0xa8
   guard tests loop_count = 1, already false for loop_count >= 2.  branch_lem itself needs 3 <= loop_count. *)
let branch_lem_ge2 = prove(
  `2 <= loop_count /\ loop_count < 2 EXP 64
   ==> (val(word_sub (word loop_count:int64) (word 1)) = 0 <=> F)`,
  STRIP_TAC THEN REWRITE_TAC[VAL_EQ_0; WORD_SUB_EQ_0] THEN
  DISCH_THEN(MP_TAC o AP_TERM `val:int64->num`) THEN
  SUBGOAL_THEN `val(word loop_count:int64) = loop_count` SUBST1_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN ASM_REWRITE_TAC[DIMINDEX_64]; ALL_TAC] THEN
  REWRITE_TAC[VAL_WORD_1] THEN UNDISCH_TAC `2 <= loop_count` THEN ARITH_TAC);;

let fill290_hyps = subst [`2 <= loop_count`,`3 <= loop_count`] fill_hyps;;
let fill290_goal = leg_goal vs fill290_hyps entry_state (inv_state `0x290` `0`);;

let fill290_step n =
  SWP_STEPS_TAC dec_anchors ctr_slots_all REDSETX_DEC EXEC
    (K (RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `loop_count = 0 <=> F`; ASSUME `loop_count = 1 <=> F`;
          ASSUME `val(word_sub (word loop_count:int64) (word 1)) = 0 <=> F`; COND_CLAUSES])))
    fill_merges (1--n);;

let fill290_prefix =
  REPEAT STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
  SUBGOAL_THEN `loop_count < 2 EXP 64` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`nblocks DIV 4 = loop_count`; `16 * nblocks <= 2 EXP 64`] THEN ARITH_TAC; ALL_TAC] THEN
  VAL_INT64_TAC `loop_count:num` THEN
  SUBGOAL_THEN `(loop_count = 0 <=> F) /\ (loop_count = 1 <=> F)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `2 <= loop_count` THEN ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC_ALL branch_lem_ge2) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_4]) THEN REWRITE_TAC[htable_mem_4] THEN
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
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC];;

let fill290_close =
  ENSURES_FINAL_STATE_TAC THEN
  MERGE_CTR128_TAC 160 "s124" THEN MERGE_CTR128_TAC 176 "s124" THEN
  MERGE_CTR128_TAC 192 "s124" THEN MERGE_CTR128_TAC 208 "s124" THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ARITH_RULE `4 * 0 = 0`; ARITH_RULE `64 * 0 = 0`;
    ARITH_RULE `4 * 0 + 1 = 1`; ARITH_RULE `4 * 0 + 2 = 2`; ARITH_RULE `4 * 0 + 3 = 3`;
    ARITH_RULE `4 * 0 + 4 = 4`; ARITH_RULE `4 * 0 + 5 = 5`; ARITH_RULE `4 * 0 + 6 = 6`;
    ARITH_RULE `4 * 0 + 7 = 7`; ARITH_RULE `4 * 0 + 9 = 9`;
    ARITH_RULE `0 + 7 = 7`; ARITH_RULE `0 + 3 = 3`;
    ARITH_RULE `64 * 0 + 32 = 32`; ARITH_RULE `64 * 0 + 48 = 48`;
    ARITH_RULE `64 * 0 + 64 = 64`; ARITH_RULE `loop_count - 2 - 0 = loop_count - 2`] THEN
  REWRITE_TAC[ARITH_RULE `j < 0 <=> F`] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ADD_CLAUSES] THEN
  REPEAT CONJ_TAC THEN FILL_CLOSE;;

let SWP_DEC_FILL290 = prove(fill290_goal,
  fill290_prefix THEN fill290_step 124 THEN fill290_close);;

(* cbz at 0x290 guards on the invariant's literal X1 form word(loop_count-2-0) (= inv 0). *)
let fill290_cbz_nt = prove(
  `3 <= loop_count /\ loop_count < 2 EXP 64
   ==> (val(word(loop_count - 2 - 0):int64) = 0 <=> F)`,
  STRIP_TAC THEN
  SUBGOAL_THEN `val(word(loop_count - 2 - 0):int64) = loop_count - 2 - 0` SUBST1_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    UNDISCH_TAC `loop_count < 2 EXP 64` THEN ARITH_TAC;
    UNDISCH_TAC `3 <= loop_count` THEN ARITH_TAC]);;
let fill290_cbz_t = prove(
  `loop_count = 2 ==> (val(word(loop_count - 2 - 0):int64) = 0 <=> T)`,
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[ARITH_RULE `2 - 2 - 0 = 0`; VAL_WORD_0]);;

(* FILLLEG (0xa0 -> 0x294, establish inv 0) = FILL290 followed by the cbz-not-taken bridge
   0x290 -> 0x294 under 3 <= loop_count (branch falls through, X1 preserved at inv 0). *)
let SWP_DEC_FILLLEG = prove(fill_goal,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  ENSURES_SEQUENCE_TAC `pc + 0x290`
    (mk_abs(`s:armstate`, ap swp_inv `0` `s:armstate`)) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    SUBGOAL_THEN `2 <= loop_count` ASSUME_TAC THENL
     [UNDISCH_TAC `3 <= loop_count` THEN ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC SWP_DEC_FILL290 THEN EXISTS_TAC `key_p:int64` THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[GSYM MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    ENSURES_INIT_TAC "s0" THEN
    RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_4]) THEN REWRITE_TAC[htable_mem_4] THEN
    SUBGOAL_THEN `loop_count < 2 EXP 64` ASSUME_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`nblocks DIV 4 = loop_count`; `16 * nblocks <= 2 EXP 64`] THEN
      ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPEC_ALL fill290_cbz_nt) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    SWP_STEP_TAC dec_anchors ctr_slots_all REDSETX_DEC EXEC "s1" THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `val(word(loop_count - 2 - 0):int64) = 0 <=> F`;
                               COND_CLAUSES]) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN FILL_CLOSE]);;

(* LC2-PARTA (0xa0 -> 0x514, loop_count = 2) = FILL290 followed by the cbz-taken bridge
   0x290 -> 0x514 (branch taken into the drain, X1 = word 0). *)
let fill_hyps_lc2 = list_mk_conj (base_hyps @ [`loop_count = 2`]);;
let fill_goal_lc2 = leg_goal vs fill_hyps_lc2 entry_state (inv_state `0x514` `0`);;

let SWP_DEC_LC2_PARTA = prove(fill_goal_lc2,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  ENSURES_SEQUENCE_TAC `pc + 0x290`
    (mk_abs(`s:armstate`, ap swp_inv `0` `s:armstate`)) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    SUBGOAL_THEN `2 <= loop_count` ASSUME_TAC THENL
     [UNDISCH_TAC `loop_count = 2` THEN ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC SWP_DEC_FILL290 THEN EXISTS_TAC `key_p:int64` THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[GSYM MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    ENSURES_INIT_TAC "s0" THEN
    RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_4]) THEN REWRITE_TAC[htable_mem_4] THEN
    MP_TAC(SPEC_ALL fill290_cbz_t) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    SWP_STEP_TAC dec_anchors ctr_slots_all REDSETX_DEC EXEC "s1" THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `val(word(loop_count - 2 - 0):int64) = 0 <=> T`;
                               COND_CLAUSES]) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN FILL_CLOSE]);;

(* ================= DRAIN: inv (loop_count-2) -> postcondition  (0x510 -> 0xaa0) ================= *)
(* Uses FILL's shared REV64_16B_IS_BSW_REVFIELDS.  The drain also finishes the output, so its
   stepper anchors the input and output memory facts as well. *)

let drain_hyps = subst [`3 <= loop_count`, `i < loop_count - 2`] leg_hyps;;
let drain_goal = leg_goal vs drain_hyps (inv_state `0x510` `loop_count - 2`) exit_state;;

(* Shared drain leg (0x514 -> 0xaa0, hyp 2 <= loop_count): entered by the DRAINLEG leaf bridge and
   by the loop_count = 2 composition.  drain_hyps keeps 3 <= for the DRAINLEG leaf goal; drain514_hyps
   weakens it to 2 <= for this shared leg. *)
let drain514_pre = inv_state `0x514` `loop_count - 2`;;
let drain514_hyps = subst [`2 <= loop_count`, `3 <= loop_count`] drain_hyps;;
let drain514_goal = leg_goal vs drain514_hyps drain514_pre exit_state;;

(* stepper: counter merges at the tower-referenced ldr states.  Step 97 (0x694) is the first
   reduce's final `ext v30`: abbreviate the settled group-(loop_count-2) accumulator to `inter` so the second
   reduce + downstream references fold it (a 10x collapse of the Q30 tower). *)
let drain_merges = [(17,208);(42,176);(48,192)];;
let drain_step_tac =
  SWP_STEPS_TAC dec_anchors_io ctr_slots_all REDSETX_DEC EXEC
    (fun k -> RULE_ASSUM_TAC(REWRITE_RULE[COND_CLAUSES]) THEN
              (if k = 97 then REABBREV_TAC (mk_eq(`inter:int128`, `read Q30 s97`)) else ALL_TAC))
    drain_merges (1--197);;

let rhs_has c w = try (is_eq w) && can (find_term (fun u -> try fst(dest_const(fst(strip_comb u)))=c with _->false)) (rhs w) with _->false;;

(* The drain's settled-Q30 closer for one group.  ktm = the SETTLED group index (acc = nist_ghash..(4*ktm),
   branch 2 uses SWP_GHASH_BRANCH2_SETTLED ktm); off = 0 for subgoal B (blocks 4*(loop_count-2)+0..3), 4 for
   subgoal A (blocks +4..+7).  The block abbreviations use the goal's literal index 4*(loop_count-2)+(off+j);
   an arithmetic bridge before branch 2 reconciles that base to 4*ktm for the SETTLED lemma. *)
let GHASH_SETTLE_TAC (ktm:term) (off:int) : tactic =
  let mtm = mk_binop `( * ):num->num->num` `4` ktm in
  let basetm = `4 * (loop_count - 2)` in
  let blkidx j = if off+j = 0 then basetm
                 else mk_binop `(+):num->num->num` basetm (mk_small_numeral (off+j)) in
  DEC_GHASH_NORM_TAC THEN GHASH_SPLIT_TAC THEN
  GHASH_GROUP_TAC
    (INFOLD3 THEN REWRITE_TAC[INBLOCK_REASSEMBLE] THEN REWRITE_TAC[GSYM nist_input_block] THEN ASM_REWRITE_TAC[])
    (subst [ktm, `k:num`] `nist_ghash (aes128_cipher (word 0) rk) tag0 (list_of_seq (nist_input_block inblock) (4*k))`)
    (fun j -> mk_comb(`nist_input_block inblock`, blkidx j))
    ((if off = 0 then ALL_TAC else
        SUBGOAL_THEN
          (list_mk_conj (map (fun j ->
             mk_eq(mk_binop `(+):num->num->num` `4*(loop_count-2)` (mk_small_numeral (off+j)),
                   if j = 0 then mtm else mk_binop `(+):num->num->num` mtm (mk_small_numeral j)))
           [0;1;2;3]))
          (fun th -> REWRITE_TAC[th]) THENL
         [UNDISCH_TAC `2 <= loop_count` THEN ARITH_TAC; ALL_TAC]) THEN
     MP_TAC(ISPEC ktm SWP_GHASH_BRANCH2_SETTLED) THEN
     REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]));;

(* The settled-Q30 conjunct closer (subgoal A + B via a two-single-group split).  `inter` was abbreviated at
   step 98 (the first reduce's settled accumulator); subgoal B proves inter = byteswap128(nist_ghash..(4*(loop_count-1))),
   subgoal A the final reduce over it. *)
let DRAIN_Q30_TAC : tactic =
  SUBGOAL_THEN `inter = byteswap128 (nist_ghash (aes128_cipher (word 0) rk) tag0
                        (list_of_seq (nist_input_block inblock) (4 * (loop_count - 1))))`
    ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> if (try is_eq(concl th) && rhs(concl th) = `inter:int128`
                                 with _ -> false) then MP_TAC th else NO_TAC) THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    SUBGOAL_THEN `4 * (loop_count - 1) = 4 * (loop_count - 2) + 4` SUBST1_TAC THENL
     [UNDISCH_TAC `2 <= loop_count` THEN ARITH_TAC; ALL_TAC] THEN
    GHASH_SETTLE_TAC `loop_count - 2` 0;
    ALL_TAC] THEN
  FIRST_X_ASSUM(fun th -> if (try is_eq(concl th) && lhs(concl th) = `inter:int128` &&
                                 can(find_term(fun u->try fst(dest_const(fst(strip_comb u)))="nist_ghash" with _->false))(rhs(concl th))
                               with _ -> false) then SUBST1_TAC th else NO_TAC) THEN
  SUBGOAL_THEN `4 * loop_count = 4 * (loop_count - 1) + 4` SUBST1_TAC THENL
   [UNDISCH_TAC `2 <= loop_count` THEN ARITH_TAC; ALL_TAC] THEN
  GHASH_SETTLE_TAC `loop_count - 1` 4;;

(* Per-conjunct closer for the drain postcondition, shape-gated. *)
let DRAIN_CLOSE : tactic =
  fun (asl,w) ->
    (if not(is_eq w) then
       (FIRST[close_goal10; MUST_PROGRESS OUT0_TAC; ASM_REWRITE_TAC[] THEN NO_TAC]) (asl,w)
     else if rhs_has "nist_ghash" w then
       (FIRST[ (ASM_REWRITE_TAC[] THEN REFL_TAC THEN NO_TAC);
               (DRAIN_Q30_TAC THEN NO_TAC) ]) (asl,w)
     else if rhs_has "aes_ctr_block" w then
       (* out-store readback.  RECON handles both the aes2c (first-group) and stack-staged ctr_block bases,
          plus the counter-block reconstruction (CTR_BLOCK_BUILD_INSERT) and the rk-list fold (ASM_REWRITE).
          blocks +5/+6/+7 first addr-normalize their store-fact address. Every option ends THEN NO_TAC. *)
       (let RECON =
          REWRITE_TAC[aes2c] THEN
          REWRITE_TAC[XOR_AES128_CIPHER_RECONSTRUCT_DEC] THEN
          REWRITE_TAC[WORD_REVERSEFIELDS_REVERSEFIELDS] THEN REWRITE_TAC[MAP] THEN
          REWRITE_TAC[WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
          REWRITE_TAC[ZX_COUNTER_UD; ZX_COUNTER_INC; CTR_ZX_NORM] THEN
          CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
          REWRITE_TAC[GSYM WORD_ADD] THEN
          REWRITE_TAC[ARITH_RULE `(4*(loop_count-2)+4)+2 = 4*(loop_count-2)+6`;
                      ARITH_RULE `(4*(loop_count-2)+5)+2 = 4*(loop_count-2)+7`;
                      ARITH_RULE `(4*(loop_count-2)+6)+2 = 4*(loop_count-2)+8`;
                      ARITH_RULE `(4*(loop_count-2)+7)+2 = 4*(loop_count-2)+9`] THEN
          REWRITE_TAC[CTR_BLOCK_BUILD_INSERT] THEN
          REWRITE_TAC[aes_ctr_block] THEN
          REWRITE_TAC[GSYM ADD_ASSOC] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN
          REWRITE_TAC[WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
          ASM_REWRITE_TAC[] in
        let ADDRNORM = REWRITE_TAC[ARITH_RULE `64*(loop_count-2)+80 = (64*(loop_count-2)+64)+16`;
                             ARITH_RULE `64*(loop_count-2)+96 = (64*(loop_count-2)+64)+32`;
                             ARITH_RULE `64*(loop_count-2)+112 = (64*(loop_count-2)+64)+48`] in
        FIRST[ (ASM_REWRITE_TAC[] THEN NO_TAC);
               (RECON THEN NO_TAC);
               (RECON THEN CTR_NUM_CLOSE THEN NO_TAC);
               (CLOSE_V8 THEN NO_TAC);
               ((ADDRNORM THEN ASM_REWRITE_TAC[] THEN RECON) THEN NO_TAC);
               ((ADDRNORM THEN ASM_REWRITE_TAC[] THEN RECON THEN CTR_NUM_CLOSE) THEN NO_TAC);
               ((ADDRNORM THEN ASM_REWRITE_TAC[] THEN CLOSE_V8) THEN NO_TAC);
               ((ADDRNORM THEN ASM_REWRITE_TAC[] THEN
                 REWRITE_TAC[dewrap80; dewrap96; dewrap112] THEN
                 REWRITE_TAC[ARITH_RULE `16 * (4 * a + b) = 64 * a + 16 * b`] THEN CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN
                 ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[WORD_XOR_SYM] THEN RECON THEN TRY CTR_NUM_CLOSE) THEN NO_TAC);
               ((ADDRNORM THEN ASM_REWRITE_TAC[] THEN INFOLD3 THEN RECON) THEN NO_TAC);
               ((ADDRNORM THEN ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[WORD_XOR_SYM] THEN
                 INFOLD3 THEN ASM_REWRITE_TAC[] THEN RECON THEN TRY CTR_NUM_CLOSE) THEN NO_TAC);
               ((ADDRNORM THEN ASM_REWRITE_TAC[] THEN INFOLD3 THEN ASM_REWRITE_TAC[] THEN
                 ONCE_REWRITE_TAC[WORD_XOR_SYM] THEN RECON THEN TRY CTR_NUM_CLOSE) THEN NO_TAC);
               ((ADDRNORM THEN ASM_REWRITE_TAC[] THEN AES2C_OUT_TAC) THEN NO_TAC);
               ((ADDRNORM THEN ASM_REWRITE_TAC[] THEN REWRITE_TAC[dewrap80; dewrap96; dewrap112] THEN
                 REWRITE_TAC[ARITH_RULE `16 * (4 * a + b) = 64 * a + 16 * b`] THEN CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN
                 ASM_REWRITE_TAC[] THEN
                 REWRITE_TAC[XOR_AES128_CIPHER_RECONSTRUCT_DEC] THEN
                 REWRITE_TAC[MAP; WORD_REVERSEFIELDS_REVERSEFIELDS] THEN ASM_REWRITE_TAC[] THEN
                 REWRITE_TAC[ZX_COUNTER_UD; ZX_COUNTER_INC; CTR_ZX_NORM] THEN
                 CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN REWRITE_TAC[GSYM WORD_ADD] THEN
                 REWRITE_TAC[CTR_BLOCK_BUILD_INSERT] THEN REWRITE_TAC[WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
                 REWRITE_TAC[ARITH_RULE `4 * (loop_count - 2) + c + 4 = (4 * (loop_count - 2) + 4) + c`;
                             ARITH_RULE `4 * (loop_count - 2) + c + 5 = (4 * (loop_count - 2) + 5) + c`;
                             ARITH_RULE `4 * (loop_count - 2) + c + 6 = (4 * (loop_count - 2) + 6) + c`;
                             ARITH_RULE `4 * (loop_count - 2) + c + 7 = (4 * (loop_count - 2) + 7) + c`;
                             ARITH_RULE `((4 * (loop_count - 2) + 4) + c) + 2 = (4 * (loop_count - 2) + 6) + c`;
                             ARITH_RULE `((4 * (loop_count - 2) + 5) + c) + 2 = (4 * (loop_count - 2) + 7) + c`] THEN
                 REWRITE_TAC[GSYM aes_ctr_block] THEN ASM_REWRITE_TAC[] THEN
                 ONCE_REWRITE_TAC[WORD_XOR_SYM] THEN ASM_REWRITE_TAC[] THEN
                 TRY REFL_TAC) THEN NO_TAC) ]) (asl,w)
     else if (try fst(dest_const(fst(strip_comb(lhs w))))="word_zx" with _->false) then
       (* X13 scalar counter word_zx(word_add(word_zx(word_zx(word K)))(word 4)) = word_zx(word(4*lc+2)). *)
       (REWRITE_TAC[ZX_COUNTER_UD; ZX_COUNTER_INC; CTR_ZX_NORM] THEN
        REWRITE_TAC[GSYM WORD_ADD] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC) (asl,w)
     else
       (FIRST[ (ASM_REWRITE_TAC[] THEN TRY REFL_TAC THEN NO_TAC);
               (AP_TERM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC THEN NO_TAC);
               (ASM_REWRITE_TAC[] THEN REWRITE_TAC[ctr_block] THEN CONV_TAC NUM_REDUCE_CONV THEN CBLAST THEN NO_TAC);
               (CRULE THEN NO_TAC);
               (CLOSE_V8 THEN NO_TAC) ]) (asl,w));;

let SWP_DEC_DRAIN514 = prove(drain514_goal,
  REPEAT STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE `loop_count - 2 - (loop_count - 2) = 0`]) THEN
  (* prime the drained group's 4 input-block reads to `inblock` form (the SWP ldrs otherwise reach the
     settled-Q30 closer as raw byte-reassembly towers and the branch1 BITBLAST blows up). *)
  SUBGOAL_THEN `4*(loop_count-2)+7 < nblocks` ASSUME_TAC THENL
   [MP_TAC(SPECL [`nblocks:num`;`4`] DIVISION) THEN
    UNDISCH_TAC `2 <= loop_count` THEN
    SUBST1_TAC(SYM(ASSUME `nblocks DIV 4 = loop_count`)) THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `read (memory :> bytes128 (word_add in_p (word (64*(loop_count-2)+64)))) s0 = inblock (4*(loop_count-2)+4) /\
    read (memory :> bytes128 (word_add in_p (word (64*(loop_count-2)+80)))) s0 = inblock (4*(loop_count-2)+5) /\
    read (memory :> bytes128 (word_add in_p (word (64*(loop_count-2)+96)))) s0 = inblock (4*(loop_count-2)+6) /\
    read (memory :> bytes128 (word_add in_p (word (64*(loop_count-2)+112)))) s0 = inblock (4*(loop_count-2)+7)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [SUBST1_TAC(WORD_RULE `word_add in_p (word (64*(loop_count-2)+64)):int64 = word_add in_p (word (16*(4*(loop_count-2)+4)))`);
      SUBST1_TAC(WORD_RULE `word_add in_p (word (64*(loop_count-2)+80)):int64 = word_add in_p (word (16*(4*(loop_count-2)+5)))`);
      SUBST1_TAC(WORD_RULE `word_add in_p (word (64*(loop_count-2)+96)):int64 = word_add in_p (word (16*(4*(loop_count-2)+6)))`);
      SUBST1_TAC(WORD_RULE `word_add in_p (word (64*(loop_count-2)+112)):int64 = word_add in_p (word (16*(4*(loop_count-2)+7)))`)] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_4]) THEN REWRITE_TAC[htable_mem_4] THEN
  drain_step_tac THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `64 * (loop_count - 2) + 128 = 64 * loop_count /\
                (64 * (loop_count - 2) + 64) + 64 = 64 * loop_count`
    (fun th -> REWRITE_TAC[th]) THENL
   [MAP_EVERY UNDISCH_TAC [`2 <= loop_count`] THEN ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  (* split the out-store forall (post j < 4*loop_count) into the invariant's preserved prefix
     j < 4*(loop_count-2) + the 8 drained blocks as explicit unwound equations. *)
  SUBGOAL_THEN `!j:num. j < 4 * loop_count <=>
      j < 4*(loop_count-2) \/ j = 4*(loop_count-2) \/ j = 4*(loop_count-2)+1 \/ j = 4*(loop_count-2)+2 \/
      j = 4*(loop_count-2)+3 \/ j = 4*(loop_count-2)+4 \/ j = 4*(loop_count-2)+5 \/ j = 4*(loop_count-2)+6 \/
      j = 4*(loop_count-2)+7`
    (fun th -> REWRITE_TAC[th]) THENL
   [UNDISCH_TAC `2 <= loop_count` THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[TAUT `p \/ q ==> r <=> (p ==> r) /\ (q ==> r)`] THEN
  REWRITE_TAC[FORALL_AND_THM; FORALL_UNWIND_THM2] THEN
  REWRITE_TAC[ARITH_RULE `16 * (4 * a + b) = 64 * a + 16 * b`; ARITH_RULE `16 * 4 * a = 64 * a`] THEN
  CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN DRAIN_CLOSE);;

(* cbnz @ 0x510 guard: X1 = word(loop_count - 2 - (loop_count - 2)) = word 0, so the branch is NOT taken. *)
let drain_cbnz_guard = prove(
  `val(word(loop_count - 2 - (loop_count - 2)):int64) = 0 <=> T`,
  REWRITE_TAC[ARITH_RULE `loop_count - 2 - (loop_count - 2) = 0`; VAL_WORD_0]);;

(* DRAINLEG (0x510 -> 0xaa0, hyp 3 <= loop_count) = the cbnz-not-taken bridge 0x510 -> 0x514
   (X1 = word 0, falls through, invariant inv(loop_count - 2) preserved) then SWP_DEC_DRAIN514. *)
let SWP_DEC_DRAINLEG = prove(drain_goal,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  ENSURES_SEQUENCE_TAC `pc + 0x514`
    (mk_abs(`s:armstate`, ap swp_inv `loop_count - 2` `s:armstate`)) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    ENSURES_INIT_TAC "s0" THEN
    RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_4]) THEN REWRITE_TAC[htable_mem_4] THEN
    MP_TAC drain_cbnz_guard THEN DISCH_TAC THEN
    SWP_STEP_TAC dec_anchors_io ctr_slots_all REDSETX_DEC EXEC "s1" THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `val(word(loop_count - 2 - (loop_count - 2)):int64) = 0 <=> T`;
                               NOT_CLAUSES; COND_CLAUSES]) THEN
    ENSURES_FINAL_STATE_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE `loop_count - 2 - (loop_count - 2) = 0`]) THEN
    REWRITE_TAC[ARITH_RULE `loop_count - 2 - (loop_count - 2) = 0`] THEN
    ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN
    FIRST [close_goal10; (ASM_REWRITE_TAC[] THEN TRY REFL_TAC THEN NO_TAC);
           (AP_TERM_TAC THEN ARITH_TAC)];
    REWRITE_TAC[GSYM MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    SUBGOAL_THEN `2 <= loop_count` ASSUME_TAC THENL
     [UNDISCH_TAC `3 <= loop_count` THEN ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC SWP_DEC_DRAIN514 THEN EXISTS_TAC `key_p:int64` THEN ASM_REWRITE_TAC[]]);;

(* ============================ iter_1 (loop_count=1) leg ============================ *)

(* ---- iter_1 goal: entry state (0xa0) -> exit state (0xaa0), loop_count = 1 ---- *)
let iter1_hyps = list_mk_conj (base_hyps @ [`loop_count = 1`]);;
let iter1_goal = leg_goal vs iter1_hyps entry_state exit_state;;

(* ---- iter_1 stepper: 3 control-flow steps then 158 body steps.  Merges (stp x11,_/ldr q,[sp,#OFF]) at
   ABS step indices 16(208), 23(176), 27(160), 32(192) (body-relative 13/20/24/29 + 3 control prefix). ---- *)
let iter1_merges = [(16,208);(23,176);(27,160);(32,192)];;
let iter1_step_tac =
  SWP_STEPS_TAC dec_anchors_io ctr_slots_all REDSETX_DEC EXEC
    (K (RULE_ASSUM_TAC(REWRITE_RULE[COND_CLAUSES]))) iter1_merges (1--161);;

(* ---- single-group settled-Q30 closer: acc = tag0 = nist_ghash..(0), blocks 0..3, reduces to
   nist_ghash..(4).  With the s0 input priming the blocks are already `inblock j`, so the fold may find
   nothing (TRY).  SWP_GHASH_BRANCH2_SETTLED @ k=0 has `nist_ghash..(4*0)` in the acc slot where the goal
   has `tag0`; pre-prove nist_ghash..0 = tag0 and fold it into the (NUM_REDUCE'd) lemma. ---- *)
let ITER1_Q30_TAC : tactic =
  DEC_GHASH_NORM_TAC THEN GHASH_SPLIT_TAC THEN
  GHASH_GROUP_TAC
    (TRY INFOLD3 THEN REWRITE_TAC[INBLOCK_REASSEMBLE] THEN REWRITE_TAC[GSYM nist_input_block] THEN ASM_REWRITE_TAC[])
    `tag0:int128`
    (fun j -> mk_comb(`nist_input_block inblock`, mk_small_numeral j))
    (MP_TAC(REWRITE_RULE
             [prove(`nist_ghash (aes128_cipher (word 0) rk) tag0 (list_of_seq (nist_input_block inblock) 0) = tag0`,
                    REWRITE_TAC[list_of_seq; nist_ghash])]
             (CONV_RULE NUM_REDUCE_CONV (ISPEC `0` SWP_GHASH_BRANCH2_SETTLED))) THEN
     DISCH_THEN(fun th -> REWRITE_TAC[th]));;

(* ---- out-store readback closer (RECON): blocks 0,1,2,3; counter base X13=word 2, so ctr = 2,3,4,5.
   Reuse DRAIN's RECON structure but with literal block/counter indices. ---- *)
let ITER1_CLOSE : tactic =
  fun (asl,w) ->
    (if not(is_eq w) then
       (FIRST[close_goal10; MUST_PROGRESS OUT0_TAC; ASM_REWRITE_TAC[] THEN NO_TAC]) (asl,w)
     else if rhs_has "nist_ghash" w then
       (* Q30 conjunct `read Q30 s = byteswap128(nist_ghash..4)`.  Substitute ONLY the Q30 s161 read fact
          (targeted, not full ASM_REWRITE over the polluted asl), THEN discard ALL read facts (ITER1_Q30_TAC
          uses only the rk-list eq + arithmetic), THEN run the GHASH closer on the lean context. *)
       (FIRST_X_ASSUM(fun th -> try
           (match lhs(concl th) with
            | Comb(Comb(Const("read",_),Const("Q30",_)),_) -> SUBST1_TAC th
            | _ -> failwith "") with _ -> NO_TAC) THEN
        DISCARD_ASSUMPTIONS_TAC
          (fun th -> try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "read" with _ -> false) THEN
        ITER1_Q30_TAC THEN NO_TAC) (asl,w)
     else if rhs_has "aes_ctr_block" w then
       (* out-store readback for block j: after substituting the store value (ADDRNORM+ASM_REWRITE), the LHS is
          `word_xor (inblock j) (word_xor rk10 (aese-tower(CTRBLK, wrf(EL k rk))))` and RHS
          `word_xor (aes_ctr_block c nonce rk j) (inblock j)`.  Fold via XOR_AES128_CIPHER_RECONSTRUCT_DEC
          (tower -> wrf(aes128_cipher (wrf CTRBLK)(MAP wrf rk))) + rk-list, unfold aes_ctr_block on RHS, then
          peel wrf/aes128_cipher/rk to `wrf CTRBLK = ctr_block nonce (j+c)` and WORD_BLAST it (iter_1 counters
          are LITERAL lanes -- CTR_BLOCK_BUILD_INSERT does NOT match, ctr_block+WORD_BLAST does). *)
       (let ADDRNORM = GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [WORD_ADD_0] in
        let FOLD =
          REWRITE_TAC[XOR_AES128_CIPHER_RECONSTRUCT_DEC] THEN
          REWRITE_TAC[MAP] THEN REWRITE_TAC[WORD_REVERSEFIELDS_REVERSEFIELDS] THEN ASM_REWRITE_TAC[] THEN
          REWRITE_TAC[aes_ctr_block] in
        (* after FOLD both sides are `wrf(aes128_cipher CTR rk)`; peel wrf/aes128_cipher/rk to `CTR_lhs = CTR_rhs`,
           reduce the RHS counter index (j+2), then close.  Block 0 (base ctr 2): CTR_lhs = wrf(wrf(ctr_block nonce c))
           -> WORD_REVERSEFIELDS_REVERSEFIELDS + REFL.  Blocks 1-3 (literal lanes): ctr_block + NUM_REDUCE + WORD_BLAST. *)
        (* BOUNDED peel (do NOT use REPEAT -- it over-peels into CTR's structure and WORD_BLAST blows up):
           word_xor A (inblock j) = word_xor A' (inblock j)  --AP_THM;AP_TERM-->  A = A'
           A = wrf(aes128_cipher CTR rk)                       --AP_TERM-->        aes128_cipher CTR rk = ..
           aes128_cipher CTR rk = aes128_cipher CTR' rk        --AP_THM;AP_TERM--> CTR = CTR'
           Then block0's CTR = wrf(wrf ctr_block) -> WORD_REVERSEFIELDS_REVERSEFIELDS + REFL;
                blocks1-3 CTR = word_join(literal lane) -> ctr_block + NUM_REDUCE + WORD_BLAST. *)
        (* PEEL to CTR_lhs = CTR_rhs (bounded), then close: block-0 (base ctr 2, wrf(wrf ctr_block)) via
           WORD_REVERSEFIELDS_REVERSEFIELDS+REFL; blocks 1-3 (literal lanes) via ctr_block+NUM_REDUCE+WORD_BLAST. *)
        let PEEL_CTR =
          AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
          REWRITE_TAC[WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
          (REFL_TAC ORELSE
           (REWRITE_TAC[CTRBASEN; KS9_CTRBASE_0] THEN REWRITE_TAC[WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
            (REFL_TAC ORELSE CTR_NUM_CLOSE)) ORELSE
           (REWRITE_TAC[ctr_block] THEN CONV_TAC NUM_REDUCE_CONV THEN CBLAST)) in
        FIRST[ (ADDRNORM THEN ASM_REWRITE_TAC[] THEN FOLD THEN PEEL_CTR THEN NO_TAC);
               (ASM_REWRITE_TAC[] THEN FOLD THEN PEEL_CTR THEN NO_TAC);
               (ADDRNORM THEN ASM_REWRITE_TAC[] THEN REWRITE_TAC[aes2c] THEN FOLD THEN PEEL_CTR THEN NO_TAC);
               (ADDRNORM THEN ASM_REWRITE_TAC[] THEN AES2C_OUT_TAC THEN NO_TAC);
               (TRY ADDRNORM THEN ASM_REWRITE_TAC[] THEN
                REWRITE_TAC[XOR_AES128_CIPHER_RECONSTRUCT_DEC] THEN
                REWRITE_TAC[MAP; WORD_REVERSEFIELDS_REVERSEFIELDS] THEN ASM_REWRITE_TAC[] THEN
                REWRITE_TAC[ZX_COUNTER_UD; ZX_COUNTER_INC; CTR_ZX_NORM] THEN
                CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN REWRITE_TAC[GSYM WORD_ADD] THEN
                REWRITE_TAC[CTR_BLOCK_BUILD_INSERT] THEN REWRITE_TAC[WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
                REWRITE_TAC[ARITH_RULE `c + 1 = 1 + c`; ARITH_RULE `c + 2 = 2 + c`; ARITH_RULE `c + 3 = 3 + c`;
                            ARITH_RULE `0 + c = c`] THEN
                REWRITE_TAC[GSYM aes_ctr_block] THEN ASM_REWRITE_TAC[] THEN
                ONCE_REWRITE_TAC[WORD_XOR_SYM] THEN ASM_REWRITE_TAC[] THEN TRY REFL_TAC THEN NO_TAC);
               (* block 0 (base counter c): unfold target aes_ctr_block, canon 0+c, collapse double-wrf, commute *)
               (TRY ADDRNORM THEN ASM_REWRITE_TAC[] THEN
                REWRITE_TAC[XOR_AES128_CIPHER_RECONSTRUCT_DEC] THEN
                REWRITE_TAC[MAP; WORD_REVERSEFIELDS_REVERSEFIELDS] THEN ASM_REWRITE_TAC[] THEN
                REWRITE_TAC[ZX_COUNTER_UD; ZX_COUNTER_INC; CTR_ZX_NORM] THEN
                REWRITE_TAC[CTR_BLOCK_BUILD_INSERT] THEN REWRITE_TAC[WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
                REWRITE_TAC[aes_ctr_block] THEN REWRITE_TAC[ADD_CLAUSES] THEN
                REWRITE_TAC[WORD_REVERSEFIELDS_REVERSEFIELDS] THEN ASM_REWRITE_TAC[] THEN
                (REFL_TAC ORELSE MATCH_ACCEPT_TAC WORD_XOR_SYM) THEN NO_TAC);
               (ASM_REWRITE_TAC[] THEN NO_TAC) ]) (asl,w)
     else if (try can (find_term (fun u -> try fst(dest_const(fst(strip_comb u)))="word_zx" with _->false)) w with _->false) then
       (* X13 scalar counter word_zx goals, incl `word 6 = word_zx(word(4+2))`: reduce the numeral
          arithmetic then collapse word_zx(word n) via BITBLAST. *)
       (FIRST[ (REWRITE_TAC[ZX_COUNTER_UD; ZX_COUNTER_INC; CTR_ZX_NORM] THEN
                REWRITE_TAC[GSYM WORD_ADD] THEN TRY AP_TERM_TAC THEN TRY AP_TERM_TAC THEN
                CONV_TAC NUM_REDUCE_CONV THEN (REFL_TAC ORELSE ARITH_TAC) THEN NO_TAC);
               (CONV_TAC NUM_REDUCE_CONV THEN CBLAST THEN NO_TAC) ]) (asl,w)
     else
       (* register-value conjuncts (mostly `read Qn s = wrf(EL k rk)` etc.): ASM_REWRITE+REFL closes them from
          the (pruned) s161 read facts; the two X0/X2 pointer conjuncts need a bounded WORD_RULE (64*1=64). *)
       (FIRST[ (ASM_REWRITE_TAC[] THEN REFL_TAC THEN NO_TAC);
               (ASM_REWRITE_TAC[] THEN REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES] THEN CRULE THEN NO_TAC) ]) (asl,w));;

let MAYCHANGE_ABI_CLOSE =
  FIRST_X_ASSUM(fun th -> if maychange_term(concl th) then
     MATCH_MP_TAC(MATCH_MP (MESON[subsumed] `R s s' ==> R subsumed R' ==> R' s s'`) th) else NO_TAC) THEN
   REWRITE_TAC[ETA_AX] THEN REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN SUBSUMED_MAYCHANGE_TAC;;

(* Per-conjunct closer: frame goals via MAYCHANGE_ABI_CLOSE, everything else via ITER1_CLOSE
   (Q30 GHASH / out-store RECON / word_zx / register-value dispatch).  Axiom-free (no CHEAT). *)
let ITER1_CLOSE_ALL : tactic =
  fun (asl,w) -> (if maychange_term w then MAYCHANGE_ABI_CLOSE else ITER1_CLOSE) (asl,w);;

let SWP_DEC_ITER1 = prove(iter1_goal,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM (SUBST_ALL_TAC o check (fun th -> try lhs(concl th) = `loop_count:num` with _->false))) THEN
  ENSURES_INIT_TAC "s0" THEN
  (* PRIME the group's 4 input-block reads to `inblock` form (mirror DRAIN): without this the SWP ldrs
     reach the Q30 GHASH closer + out-store readbacks as RAW byte-reassembly towers and BITBLAST blows up. *)
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
      SUBST1_TAC(WORD_RULE `word_add in_p (word 16):int64 = word_add in_p (word (16*1))`);
      SUBST1_TAC(WORD_RULE `word_add in_p (word 32):int64 = word_add in_p (word (16*2))`);
      SUBST1_TAC(WORD_RULE `word_add in_p (word 48):int64 = word_add in_p (word (16*3))`)] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_4]) THEN REWRITE_TAC[htable_mem_4] THEN
  iter1_step_tac THEN
  ENSURES_FINAL_STATE_TAC THEN
  (* PRUNE asl before the closers: the 161 keep-steps leave transient huge-RHS register reads
     (`read Qn sK = <GHASH-partial tower>`) that make every closer ASM_REWRITE/WORD_RULE storm
     (O(asl*termsize)).  Discard reads whose RHS term is large (>800 chars); the postcondition's
     final Q-reads have small RHS (wrf(EL k rk) etc.) and survive, as do the out_p/in_p/mem store
     facts the RECON needs (those are `read(memory:>..)` -- kept: only REGISTER reads pruned). *)
  (let rec tsize n t = if n > 60 then n else
     match t with Comb(a,b) -> tsize (tsize (n+1) a) b | Abs(_,b) -> tsize (n+1) b | _ -> n+1 in
   DISCARD_ASSUMPTIONS_TAC
    (fun th -> try let c = concl th in is_eq c &&
       (match lhs c with Comb(Comb(Const("read",_),comp),st) ->
          (match comp with Comb(Const(":>",_),_) -> false   (* memory reads (out_p/in_p/tag/ivec/mem): keep *)
                         | _ ->
             (* register read: drop only TRANSIENT ones (state != s161) with a big RHS; keep final s161
                reads (postcondition register values).  Use a cheap bounded node-count (string_of_term on
                the 4000-node GHASH towers x60 facts would itself storm). *)
             tsize 0 (rhs c) > 60 &&
             (match st with Var(nm,_) -> nm <> "s161" | _ -> true))
        | _ -> false)
     with _ -> false)) THEN
  ASM_REWRITE_TAC[] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES] THEN
  REWRITE_TAC[ARITH_RULE `j < 4 <=> j = 0 \/ j = 1 \/ j = 2 \/ j = 3`] THEN
  REWRITE_TAC[TAUT `p \/ q ==> r <=> (p ==> r) /\ (q ==> r)`] THEN
  REWRITE_TAC[FORALL_AND_THM; FORALL_UNWIND_THM2] THEN
  CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN ITER1_CLOSE_ALL);;

(* ==================== COMPOSITION: loop_count=2 = LC2-PARTA (0xa0 -> 0x514) + DRAIN514 (0x514 -> 0xaa0) ==================== *)
let lc2_goal = leg_goal vs fill_hyps_lc2 entry_state exit_state;;
let SWP_DEC_LC2 = prove(lc2_goal,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  ENSURES_SEQUENCE_TAC `pc + 0x514`
    (mk_abs(`s:armstate`, ap swp_inv `0` `s:armstate`)) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    MATCH_MP_TAC SWP_DEC_LC2_PARTA THEN EXISTS_TAC `key_p:int64` THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[GSYM MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    ENSURES_PRECONDITION_TAC drain514_pre THEN CONJ_TAC THENL
     [GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
      FIRST_ASSUM(fun th -> if lhs(concl th)=`loop_count:num` then REWRITE_TAC[th] else NO_TAC) THEN
      CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];
      MATCH_MP_TAC SWP_DEC_DRAIN514 THEN EXISTS_TAC `key_p:int64` THEN
      REPEAT CONJ_TAC THEN TRY(FIRST_X_ASSUM ACCEPT_TAC) THEN
      TRY(ASM_REWRITE_TAC[] THEN NO_TAC) THEN (UNDISCH_TAC `loop_count = 2` THEN ARITH_TAC)]]);;

(* ==================== leaf tactics wiring the 7 proven legs into the main theorem ==================== *)
(* lc0 (0xa0->0xaa0, loop_count=0): closed inline (no separate lemma). *)
let SWP_DEC_LC0_TAC : tactic =
  ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_4]) THEN
  ARM_STEPS_TAC AES128_GCM_DEC_EXEC [1] THEN
  ENSURES_FINAL_STATE_TAC THEN REWRITE_TAC[htable_mem_4] THEN ASM_REWRITE_TAC[] THEN
  (* CRUCIAL: reduce 4*0 -> 0 BEFORE unfolding list_of_seq/nist_ghash, else nist_ghash's recursive
     equation loops (stack overflow) on the un-reduced count.  Do NOT use `LT`/`CONJUNCT1 LT` in a
     REWRITE set -- LT's recursive def loops too.  Then close the trivial numeric residuals. *)
  REWRITE_TAC[ARITH_RULE `4 * 0 = 0`; ARITH_RULE `64 * 0 = 0`; ARITH_RULE `4 * 0 + 2 = 2`;
              MULT_CLAUSES; ADD_CLAUSES; WORD_ADD_0] THEN
  REWRITE_TAC[list_of_seq] THEN REWRITE_TAC[nist_ghash] THEN
  REWRITE_TAC[ARITH_RULE `j < 0 <=> F`] THEN
  (* re-FOLD the ABI macro in the goal frame (main thm expanded it up top) so MAYCHANGE_ABI_CLOSE's
     MATCH_MP against the folded-ABI subsumption lemma matches the frame goal `(ABI ,, ..) s0 s1`. *)
  REWRITE_TAC[GSYM MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REPEAT CONJ_TAC THEN
  TRY(ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  TRY(CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_BLAST THEN NO_TAC) THEN
  MAYCHANGE_ABI_CLOSE;;

(* The main theorem presents its leaf goals with the ABI macro expanded, htable_mem_4 unfolded and the
   conjunctions right-associated (the family's REWRITE_TAC[htable_mem_4; GSYM CONJ_ASSOC] after each
   ENSURES_SEQUENCE_TAC / ENSURES_WHILE_UP_TAC); leaf_form puts a leg lemma in the same form. *)
let leaf_form th = REWRITE_RULE[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; htable_mem_4; GSYM CONJ_ASSOC] th;;

(* Discharge a leg's hypotheses from the main theorem's context.  The nonoverlapping facts may appear
   with their arguments swapped relative to the ALLPAIRS expansion, hence the NONOVERLAPPING_TAC fallback. *)
let LEG_HYPS_TAC : tactic =
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
  TRY(FIRST_ASSUM ACCEPT_TAC) THEN TRY(ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  TRY(ASM_ARITH_TAC) THEN TRY NONOVERLAPPING_TAC;;

(* Close a leaf goal with a proven leg (key_p occurs only in the hypotheses). *)
let APPLY_LEG (leg:thm) : tactic =
  MATCH_MP_TAC (leaf_form leg) THEN EXISTS_TAC `key_p:int64` THEN LEG_HYPS_TAC;;

(* back-edge leaf (cbnz@0x510 -> 0x294 while i+1 < loop_count-2): closed inline. *)
let SWP_DEC_BACKEDGE_LEAF_TAC : tactic =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_4]) THEN
  (* the cbnz@0x510 guard is not-taken since (loop_count-2)-i != 0 for i < loop_count-2.  Discharge the
     `~(val(word(loop_count-2-i))=0)` obligation from whatever loop-count facts the WHILE-leaf provides
     (ASM_ARITH_TAC uses all assumptions -- robust to the exact assumption forms). *)
  (* discharge the cbnz-not-taken guard using ONLY the small loop-count facts (val(word loop_count)=loop_count
     gives loop_count<2^64; i<loop_count-2 gives loop_count-2-i>0).  Do NOT use ASM_ARITH_TAC -- it drags the
     whole huge invariant into the linear-arith engine and blows up. *)
  SUBGOAL_THEN `~(val(word(loop_count-2-i):int64) = 0)` ASSUME_TAC THENL
   [SUBGOAL_THEN `val(word(loop_count-2-i):int64) = loop_count-2-i` SUBST1_TAC THENL
     [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
      MP_TAC(ISPEC `word loop_count:int64` VAL_BOUND_64) THEN
      TRY(FIRST_ASSUM(fun th -> if lhs(concl th) = `val(word loop_count:int64)` then REWRITE_TAC[th] else NO_TAC)) THEN
      UNDISCH_TAC `i < loop_count - 2` THEN ARITH_TAC;
      UNDISCH_TAC `i < loop_count - 2` THEN ARITH_TAC];
    ALL_TAC] THEN
  ARM_STEPS_TAC AES128_GCM_DEC_EXEC [1] THEN
  ENSURES_FINAL_STATE_TAC THEN REWRITE_TAC[htable_mem_4] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN MAYCHANGE_ABI_CLOSE;;

(* ==================== MAIN THEOREM (7 legs wired) ==================== *)
let AES128_GCM_DEC_CORRECT = prove
 (`!in_p out_p len_bits tag_p ivec_p key_p htable_p tag0 nonce rk inblock pc
     stackpointer.
       aligned 16 stackpointer /\
       ALLPAIRS nonoverlapping
        [(out_p, 16 * val len_bits DIV 128); (tag_p, 16); (ivec_p, 16);
         (word_add stackpointer (word 160), 64)]
        [(word pc, LENGTH aes128_gcm_dec_mc);
         (in_p,  16 * val len_bits DIV 128); (key_p, 176); (htable_p, 192)] /\
       PAIRWISE nonoverlapping
        [(out_p, 16 * val len_bits DIV 128); (tag_p, 16); (ivec_p, 16);
         (word_add stackpointer (word 160), 64)]
    ==>
    ensures arm
      (\s. aligned_bytes_loaded s (word pc) aes128_gcm_dec_mc /\
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
                    word_xor (aes_ctr_block c nonce rk i) (inblock i)) /\
           read (memory :> bytes128 tag_p) s =
             word_reversefields 8
              (nist_ghash (aes128_cipher (word 0) rk) tag0
                 (list_of_seq (nist_input_block inblock)
                              (val len_bits DIV 128))) /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8
               (ctr_block nonce (val len_bits DIV 128 + c)))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [X19; X20; X21; X22; X23; X24;
                  X25; X26; X27; X28; X29; X30] ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * val len_bits DIV 128);
                  memory :> bytes(tag_p, 16);
                  memory :> bytes(ivec_p, 16);
                  memory :> bytes(word_add stackpointer (word 160), 64)])`,
  GEN_TAC THEN GEN_TAC THEN W64_GEN_TAC `len_bits:num` THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REWRITE_TAC[ALLPAIRS; PAIRWISE; ALL; fst AES128_GCM_DEC_EXEC] THEN

  (*** Abbreviate the loop counts to keep goal terms manageable ***)

  ABBREV_TAC `nblocks     = len_bits DIV 128` THEN
  ABBREV_TAC `loop_count  = nblocks DIV 4` THEN
  ABBREV_TAC `loop_remain = nblocks MOD 4` THEN
  STRIP_TAC THEN
  CONV_TAC(ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN REWRITE_TAC[WORD_ADD_0] THEN

  (*** Break up the round key list - a bit clumsy ****)

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
    ARM_STEPS_TAC AES128_GCM_DEC_EXEC (1--29) THEN
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

  (*** Break code between main unrolled loop and tail loop ***)

  ENSURES_SEQUENCE_TAC `pc + 0xaa0` (mk_abs(`s:armstate`, exit_body)) THEN
  REWRITE_TAC[htable_mem_4; GSYM CONJ_ASSOC] THEN CONJ_TAC THENL
   [(*** MAIN LOOP (software-pipelined), 0xa0 -> 0xaa0, via the elaborated Q = P o [Y]
     *** invariant inlined at the ENSURES_WHILE_UP_TAC below.  Four control-flow paths
     *** on loop_count.  The fill does "sub x1,x1,#2" (0x28c) then "cbz x1,0x514"; the
     *** steady body does "sub x1,x1,#1" (0x50c) then "cbnz x1,0x294", so the steady
     *** loop runs loop_count-2 times (a DEPTH-2 pipeline: AES runs ahead in Q30/Q5,
     *** GHASH lags behind with this group's fold half-done):
     ***   count = 0 : cbz x1 at 0xa0 -> straight to 0xaa0 (no blocks).
     ***   count = 1 : b.eq 0x828 -> iter_1 single-group path -> 0xaa0.
     ***   count = 2 : fill then cbz at 0x290 -> drain 0x514; steady loop runs 0 times
     ***              (k=0), so ENSURES_WHILE_UP_TAC (which needs ~(k=0)) does not apply
     ***              -> its own peeled case.
     ***   count >=3 : ENSURES_WHILE_UP_TAC (loop_count-2), head 0x294 / back-edge 0x510.
     ***              FILL (0xa0->0x294, establish inv 0) and DRAIN (0x510->0xaa0,
     ***              inv (loop_count-2) -> after-loop postcondition) are this tactic's
     ***              first and last subgoals, NOT separate ENSURES_SEQUENCE_TACs.  The
     ***              steady body is the BODYLEG.
     *** Each leaf subgoal is discharged by its proven leg lemma (SWP_DEC_ITER1,     ***
     *** SWP_DEC_LC2, SWP_DEC_FILLLEG, SWP_DEC_BODYLEG, SWP_DEC_DRAINLEG) or an       ***
     *** inline recipe (loop_count=0, back-edge), via APPLY_LEG.                      ***)

    ASM_CASES_TAC `loop_count = 0` THENL
     [POP_ASSUM SUBST_ALL_TAC THEN SWP_DEC_LC0_TAC;
      ALL_TAC] THEN

    ASM_CASES_TAC `loop_count = 1` THENL
     [APPLY_LEG SWP_DEC_ITER1;
      ALL_TAC] THEN

    ASM_CASES_TAC `loop_count = 2` THENL
     [APPLY_LEG SWP_DEC_LC2;
      ALL_TAC] THEN

    SUBGOAL_THEN `3 <= loop_count` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN

    ENSURES_WHILE_UP_TAC `loop_count - 2` `pc + 0x294` `pc + 0x510`
      (mk_abs(`i:num`, mk_abs(`s:armstate`, ap swp_inv `i:num` `s:armstate`))) THEN
    REWRITE_TAC[htable_mem_4; GSYM CONJ_ASSOC] THEN REPEAT CONJ_TAC THENL
     [(*** ~(loop_count - 2 = 0), from 3 <= loop_count. ***)
      ASM_ARITH_TAC;
      (*** FILL: 0xa0 -> 0x294, establish the inlined invariant at i = 0. ***)
      APPLY_LEG SWP_DEC_FILLLEG;
      (*** BODY (BODYLEG): 0x294 -> 0x510, inv i -> inv (i+1). ***)
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN APPLY_LEG SWP_DEC_BODYLEG;
      (*** back-edge: cbnz x1 at 0x510 -> 0x294 while i+1 < loop_count-2. ***)
      SWP_DEC_BACKEDGE_LEAF_TAC;
      (*** DRAIN: 0x510 -> 0xaa0, inv (loop_count-2) -> after-loop postcondition. ***)
      APPLY_LEG SWP_DEC_DRAINLEG];
    ALL_TAC] THEN
  (*** Trivial case of the tail loop ***)

  ASM_CASES_TAC `loop_remain = 0` THENL
   [POP_ASSUM SUBST_ALL_TAC THEN
    ENSURES_INIT_TAC "s0" THEN
    (*** Split the initial ivec read so the low 12 bytes (untouched by the counter ***)
    (*** writeback) survive as separate 32-bit cells across the stepping.          ***)
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o CONV_RULE(READ_MEMORY_SPLIT_CONV 2) o
      check (fun th -> let c = concl th in
        is_eq c && free_in `ivec_p:int64` (lhs c) &&
        not(free_in `out_p:int64` (lhs c)) && not(free_in `key_p:int64` (lhs c)) &&
        not(free_in `htable_p:int64` (lhs c)) && not(free_in `tag_p:int64` (lhs c)))) THEN
    MAP_EVERY(fun n -> ARM_STEPS_TAC AES128_GCM_DEC_EXEC [n] THEN
          RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)))
        (1--6) THEN
    ENSURES_FINAL_STATE_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP (ARITH_RULE
     `n MOD 4 = 0 ==> 4 * n DIV 4 = n`)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN
    (*** Recompose the ivec postcondition from the 32-bit cells: three unchanged   ***)
    (*** nonce cells plus the freshly-written byte-reversed counter word.  Split    ***)
    (*** ONLY the ivec read (guarded), not the out-block reads.                     ***)
    CONV_TAC(ONCE_DEPTH_CONV(fun t ->
      if is_eq t && free_in `ivec_p:int64` (lhs t) &&
         not(free_in `out_p:int64` (lhs t)) && not(free_in `tag_p:int64` (lhs t))
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
        word_subword (word_reversefields 8 (ctr_block nonce c):int128) (0,64):int64 /\
      read X12 s =
        word_zx (word_zx (word_subword
          (word_reversefields 8 (ctr_block nonce c):int128) (64,64):int64):int32):int64 /\
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
        (!j. j < nblocks
             ==> read (memory :> bytes128 (word_add in_p (word(16*j)))) s =
                 inblock j) /\
      (!j. j < 4 * loop_count + i
           ==> read (memory :> bytes128 (word_add out_p (word(16*j)))) s =
               word_xor (aes_ctr_block c nonce rk j) (inblock j))` THEN
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
    (*** The single tail block also assembles its counter on the stack          ***)
    (*** SWP tail: "stp x11,x23,[sp,#160]" at step 6, "ldr q10,[sp,#160]" at step 8; ***)
    (*** merge the two 64-bit stores AT STATE s6 (after the stp, BEFORE the ldr)  ***)
    (*** so the 128-bit reload at step 6 yields a CONCRETE counter block.  This    ***)
    (*** is essential: if merged at s6 the ldr q0 keeps a symbolic read, the AES   ***)
    (*** chain `read Q0 sN = aese (read Q0 s_{N-1})..` then references old states   ***)
    (*** and every step is DISCARDED by DISCARD_OLDSTATE, so the output-store       ***)
    (*** read-back `read(mem) s28 = read Q0 s27` is erased and the postcondition    ***)
    (*** store read never resolves.  (Encrypt's tail merges at s6 because its stp   ***)
    (*** lands one step later; the decrypt tail schedule puts the stp at step 5.)   ***)
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
    (*** Scalar counter reconstruction (tail loop, single block; "add w14,w13,#0" ***)
    (*** so the counter word is the base 4*loop_count+i+2).                          ***)
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
    (*** Fold the GHASH operand to nist_input_block subwords (as in the main loop).       ***)
    DEC_GHASH_NORM_TAC THEN
    (*** Peel the counter conjunct (word arithmetic); the single output-store conjunct was  ***)
    (*** already folded + resolved in the store/counter prefix above via the forall-split    ***)
    (*** (j = 4*loop_count+i) + XOR_AES128_CIPHER_RECONSTRUCT_DEC, exactly as the main loop's ***)
    (*** four stores.  This leaves the single GHASH accumulator goal.                        ***)
    REPEAT(CONJ_TAC THENL [(REPEAT AP_TERM_TAC THEN ARITH_TAC) ORELSE CONV_TAC WORD_RULE ORELSE
      ASM_SIMP_TAC[WORD_SUB; LT_IMP_LE; ARITH_RULE `i < loop_remain ==> i + 1 <= loop_remain`];
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
    (*** Split the initial ivec read so the low 12 (nonce) bytes survive the        ***)
    (*** 4-byte counter writeback as separate cells.                                ***)
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o CONV_RULE(READ_MEMORY_SPLIT_CONV 2) o
      check (fun th -> let c = concl th in
        is_eq c && free_in `ivec_p:int64` (lhs c) &&
        not(free_in `out_p:int64` (lhs c)) && not(free_in `key_p:int64` (lhs c)) &&
        not(free_in `htable_p:int64` (lhs c)) && not(free_in `tag_p:int64` (lhs c)))) THEN
    MAP_EVERY(fun n -> ARM_STEPS_TAC AES128_GCM_DEC_EXEC [n] THEN
          RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)))
        (1--6) THEN
    ENSURES_FINAL_STATE_TAC THEN
    (*** Unify the counter values: the postcondition uses nblocks, the running     ***)
    (*** counter is 4*loop_count+loop_remain; rewrite nblocks to the latter so both ***)
    (*** sides share one expression before blasting.                                ***)
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
    (*** Normalise counter-value associativity (X13's 4*lc+lr+2 vs the         ***)
    (*** postcondition's (4*lc+lr)+2) and collapse the W-conversion chain      ***)
    (*** before blasting.                                                      ***)
    REWRITE_TAC[ADD_ASSOC; ZX_COUNTER_UD; CTR_ZX_NORM] THEN
    CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
    CONV_TAC WORD_BLAST]);;

(* Subroutine correctness: lifts the core proof through the save/restore     *)
(* boilerplate and the final ret. This is the theorem used externally.       *)
(* ------------------------------------------------------------------------- *)

(*** The externally-used spec. Its pre/postconditions match the core theorem
 *** (CTR ciphertext output, GHASH tag, updated counter), lifted through the
 *** save/restore prologue/epilogue and the final ret. The stack frame region
 *** (224 bytes below the incoming SP) is added to the nonoverlapping lists and
 *** to the MAYCHANGE. ARM_ADD_RETURN_STACK_TAC does the lifting; we expand the
 *** compound memory predicates htable_mem_4 and wordlist_from_memory (in both
 *** the goal and the fed core theorem) so the interior big-step's precondition
 *** obligation is discharged with no residual subgoal.
 ***)

let AES128_GCM_DEC_SUBROUTINE_CORRECT = prove
 (`!in_p out_p len_bits tag_p ivec_p key_p htable_p tag0 nonce rk inblock
    pc stackpointer returnaddress.
    aligned 16 stackpointer /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * val len_bits DIV 128); (tag_p, 16); (ivec_p, 16);
       (word_sub stackpointer (word 224), 224)]
      [(word pc, LENGTH aes128_gcm_dec_mc);
       (in_p,  16 * val len_bits DIV 128); (key_p, 176); (htable_p, 192)] /\
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
                    word_xor (aes_ctr_block c nonce rk i) (inblock i)) /\
           read (memory :> bytes128 tag_p) s =
             word_reversefields 8
              (nist_ghash (aes128_cipher (word 0) rk) tag0
                 (list_of_seq (nist_input_block inblock)
                              (val len_bits DIV 128))) /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8
               (ctr_block nonce (val len_bits DIV 128 + c)))
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

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory-safety proofs (core kernel body + full subroutine).*)
(*                                                                            *)
(* The event trace e2 produced by the kernel is a function of the PUBLIC       *)
(* arguments only (in/out/tag/ivec/key/htable pointers, len_bits, pc,          *)
(* stackpointer[, returnaddress]) -- established by the outer `exists          *)
(* f_events` over public data -- and every memory access lies in the declared  *)
(* readable / writable ranges (memaccess_inbounds).  This gives constant-time  *)
(* execution and memory safety.                                                *)
(*                                                                            *)
(* This kernel is software-pipelined: the main loop (loop_count = nblocks      *)
(* DIV 4, over 64-byte groups) is a depth-2 pipeline with four control-flow    *)
(* paths (loop_count = 0 / 1 / 2 / >=3), and the tail loop (loop_remain =      *)
(* nblocks MOD 4, over 16-byte blocks) is a plain WHILE.  The `_SUBROUTINE_`   *)
(* variant additionally wraps the register-save prologue and register-restore *)
(* epilogue over the 224-byte stack frame (WORD_FORALL_OFFSET_TAC 224).        *)
(* ------------------------------------------------------------------------- *)

let SAFE_SIM = SAFE_SIM_TAC EXEC;;

(* --- SWP-specific closers. --- *)

(* The FILL back-edge cbz @0x290 tests loop_count-2; DRAIN pointer reconciliation *)
(* uses loop_count = (loop_count-2)+2.  DRAIN_ADDR normalises that so WORD_RULE     *)
(* sees only linear combinations.                                                 *)
let DRAIN_ADDR = DRAIN_ADDR_K `2`;;

(* The b.eq @0xa8 (loop_count=1) and cbz @0x290 (loop_count=2) branch facts: with *)

let OPEN_DEC = OPEN_SWP_SAFE EXEC;;

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
        else if val len_bits DIV 128 DIV 4 = 2 then
          f_ev_m2 in_p out_p tag_p ivec_p key_p htable_p len_bits pc stackpointer
        else
          APPEND
            (f_ev_drain in_p out_p tag_p ivec_p key_p htable_p len_bits pc stackpointer)
            (APPEND
              (ENUMERATEL (val len_bits DIV 128 DIV 4 - 2)
                (\i. f_ev_steady in_p out_p tag_p ivec_p key_p htable_p len_bits pc stackpointer i))
              (f_ev_fill in_p out_p tag_p ivec_p key_p htable_p len_bits pc stackpointer)))
       (f_ev_pro in_p out_p tag_p ivec_p key_p htable_p len_bits pc stackpointer))
   :(uarch_event) list`;;

let AES128_GCM_DEC_SAFE = prove
 (`exists f_events.
    forall e in_p len_bits out_p tag_p ivec_p key_p htable_p pc stackpointer.
      aligned 16 stackpointer /\
      ALLPAIRS nonoverlapping
        [(out_p, 16 * val len_bits DIV 128); (tag_p, 16); (ivec_p, 16);
         (word_add stackpointer (word 160), 64)]
        [(word pc, LENGTH aes128_gcm_dec_mc);
         (in_p,  16 * val len_bits DIV 128); (key_p, 176); (htable_p, 192)] /\
      PAIRWISE nonoverlapping
        [(out_p, 16 * val len_bits DIV 128); (tag_p, 16); (ivec_p, 16);
         (word_add stackpointer (word 160), 64)]
      ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) aes128_gcm_dec_mc /\
               read PC s = word (pc + 0x2c) /\
               read SP s = stackpointer /\
               C_ARGUMENTS [in_p; len_bits; out_p; tag_p; ivec_p; key_p; htable_p] s /\
               read events s = e)
          (\s. read PC s = word (pc + 0xb68) /\
               (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events in_p out_p tag_p ivec_p key_p htable_p len_bits pc stackpointer /\
                    memaccess_inbounds e2
                      [in_p, 16 * val len_bits DIV 128; tag_p, 16; ivec_p, 16; key_p, 176; htable_p, 192;
                       out_p, 16 * val len_bits DIV 128; word_add stackpointer (word 160), 64]
                      [out_p, 16 * val len_bits DIV 128; tag_p, 16; ivec_p, 16;
                       word_add stackpointer (word 160), 64]))
          (\s s'. T)`,
  CONCRETIZE_F_EVENTS_TAC scaffold_dec THEN
  OPEN_DEC THEN

  (*** Top split at 0xaa0 (main region -> tail region). ***)
  ENSURES_EVENTS_SEQUENCE_TAC `pc + 0xaa0`
   `\s. read X0 s = word_add in_p (word (64 * loop_count)) /\
        read X2 s = word_add out_p (word (64 * loop_count)) /\
        read X3 s = tag_p /\ read X4 s = ivec_p /\ read X6 s = htable_p /\
        read SP s = stackpointer /\ read X16 s = word loop_remain` THEN
  CONJ_TAC THENL
   [(*** MAIN REGION pc+0x2c -> pc+0xaa0 (setup + 4-way pipelined loop). ***)
    ENSURES_EVENTS_SEQUENCE_TAC `pc + 0xa0`
     `\s. read X0 s = in_p /\ read X2 s = out_p /\ read X3 s = tag_p /\
          read X4 s = ivec_p /\ read X6 s = htable_p /\ read SP s = stackpointer /\
          read X1 s = word loop_count /\ read X16 s = word loop_remain` THEN
    CONJ_TAC THENL [SAFE_SIM (1--29) THEN CLOSE; ALL_TAC] THEN

    (*** loop_count = 0 : cbz @0xa0 taken -> 0xaa0. ***)
    ASM_CASES_TAC `loop_count = 0` THENL
     [REDUCE_IF0 `loop_count:num` THEN SAFE_SIM (1--1) THEN CLOSE; ALL_TAC] THEN
    REDUCE_IFN0 `loop_count:num` THEN

    (*** loop_count = 1 : b.eq @0xa8 -> iter_1 path (3 + 158 steps). ***)
    ASM_CASES_TAC `loop_count = 1` THENL
     [REDUCE_IFEQ `loop_count:num` `1` THEN SAFE_SIM (1--161) THEN CLOSE; ALL_TAC] THEN
    REDUCE_IFNE `loop_count:num` `1` THEN

    (*** loop_count = 2 : FILL (cbz @0x290 taken) + DRAIN (322 steps). ***)
    ASM_CASES_TAC `loop_count = 2` THENL
     [REDUCE_IFEQ `loop_count:num` `2` THEN SAFE_SIM (1--322) THEN CLOSE; ALL_TAC] THEN
    REDUCE_IFNE `loop_count:num` `2` THEN

    (*** loop_count >= 3 : FILL + STEADY(loop_count-2) + DRAIN. ***)
    SUBGOAL_THEN `3 <= loop_count` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
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
      BEQ_NZ `1` THEN SAFE_SIM (1--125) THEN
      BEQ_NZ `2` THEN
      REPEAT CONJ_TAC THENL
       [(* cbz @0x290 branch not taken *) ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE;
        ADDR_RECON;
        ADDR_RECON;
        (* X1 = word(loop_count - 2 - 0) *)
        REWRITE_TAC[SUB_0] THEN GEN_REWRITE_TAC RAND_CONV [WORD_SUB] THEN
        ASM_SIMP_TAC[ARITH_RULE `3 <= loop_count ==> 2 <= loop_count`];
        DEABBR THEN DISCHARGE_SAFETY_PROPERTY_TAC];
      (*** back-edge / STEADY body: 0x294 -> 0x514, inv i -> inv (i+1). ***)
      REWRITE_TAC[] THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
      SUBGOAL_THEN `loop_count - 2 < 2 EXP 64` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      SAFE_SIM (1--160) THEN CLOSE_R2;
      (*** DRAIN post-leg: 0x514 -> 0xaa0. ***)
      SAFE_SIM (1--197) THEN REPEAT CONJ_TAC THENL
       [DRAIN_ADDR; DRAIN_ADDR; DEABBR THEN DISCHARGE_SAFE_ROBUST]];

    ALL_TAC] THEN

  (*** TAIL REGION pc+0xaa0 -> pc+0xb68. ***)
  ASM_CASES_TAC `loop_remain = 0` THENL
   [REDUCE_IF0 `loop_remain:num` THEN SAFE_SIM (1--1) THEN CLOSE_R2; ALL_TAC] THEN
  REDUCE_IFN0 `loop_remain:num` THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `loop_remain:num` `pc + 0xaa4` `pc + 0xb68`
   `\i s. read X0 s = word_add in_p (word (64 * loop_count + 16 * i)) /\
          read X2 s = word_add out_p (word (64 * loop_count + 16 * i)) /\
          read X3 s = tag_p /\ read X4 s = ivec_p /\ read X6 s = htable_p /\
          read SP s = stackpointer /\ read X16 s = word (loop_remain - i)` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [SAFE_SIM (1--1) THEN CLOSE_R2;
    ALL_TAC;
    REWRITE_TAC[] THEN SAFE_SIM [] THEN CLOSE_R2] THEN
  REWRITE_TAC[] THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
  SAFE_SIM (1--49) THEN CLOSE_R2);;


(* ------------------------------------------------------------------------- *)
(* Full-function (subroutine-level) constant-time + memory-safety.            *)
(*                                                                            *)
(* Same wrapping as the other subroutine proofs: WORD_FORALL_                 *)
(* OFFSET_TAC 224 aligns the post-prologue running SP with the abstract       *)
(* stackpointer (so the pipelined body reasoning applies verbatim), and every *)
(* invariant carries the saved-x30 slot (sp+88) so the epilogue restore + ret *)
(* provably returns to returnaddress.  Prologue/epilogue are byte-identical to *)
(* the clean kernels (frame 224, x30 at sp+88); the setup leg is pc..0xa0 =    *)
(* 11 (prologue) + 29 (setup) = 40 steps; the epilogue pc+0xb68 -> ret is 17.  *)
(* ------------------------------------------------------------------------- *)

let AES128_GCM_DEC_SUBROUTINE_SAFE = prove
 (`exists f_events.
    forall e in_p len_bits out_p tag_p ivec_p key_p htable_p pc stackpointer returnaddress.
      aligned 16 stackpointer /\
      ALLPAIRS nonoverlapping
        [(out_p, 16 * val len_bits DIV 128); (tag_p, 16); (ivec_p, 16);
         (word_sub stackpointer (word 224), 224)]
        [(word pc, LENGTH aes128_gcm_dec_mc);
         (in_p,  16 * val len_bits DIV 128); (key_p, 176); (htable_p, 192)] /\
      PAIRWISE nonoverlapping
        [(out_p, 16 * val len_bits DIV 128); (tag_p, 16); (ivec_p, 16);
         (word_sub stackpointer (word 224), 224)]
      ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) aes128_gcm_dec_mc /\
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
                      [in_p, 16 * val len_bits DIV 128; tag_p, 16; ivec_p, 16; key_p, 176; htable_p, 192;
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
              else if val len_bits DIV 128 DIV 4 = 2 then
                f_ev_m2 in_p out_p tag_p ivec_p key_p htable_p len_bits pc stackpointer returnaddress
              else
                APPEND
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
  REWRITE_TAC[ALLPAIRS; PAIRWISE; ALL; fst EXEC] THEN
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

  (*** Epilogue split at pc+0xb68.  The epilogue stores the tag (str q30,[x3]) and the counter    ***)
  (*** (str w14,[x4,#12]), so X3=tag_p and X4=ivec_p must be carried to prove those stores do not  ***)
  (*** hit code; X15 holds the value moved into x0 (mov x0,x15) but is not a store address.        ***)
  ENSURES_EVENTS_SEQUENCE_TAC `pc + 0xb68`
   `\s. read X3 s = tag_p /\ read X4 s = ivec_p /\ read SP s = stackpointer /\
        read (memory :> bytes64 (word_add stackpointer (word 88))) s = returnaddress` THEN
  CONJ_TAC THENL
   [(*** REGION A: pc -> pc+0xb68 (prologue + pipelined body). ***)
    ENSURES_EVENTS_SEQUENCE_TAC `pc + 0xaa0`
     `\s. read X0 s = word_add in_p (word (64 * loop_count)) /\
          read X2 s = word_add out_p (word (64 * loop_count)) /\
          read X3 s = tag_p /\ read X4 s = ivec_p /\ read X6 s = htable_p /\
          read SP s = stackpointer /\ read X16 s = word loop_remain /\
          read (memory :> bytes64 (word_add stackpointer (word 88))) s = returnaddress` THEN
    CONJ_TAC THENL
     [(*** setup incl prologue: pc -> 0xa0 = 40 steps. ***)
      ENSURES_EVENTS_SEQUENCE_TAC `pc + 0xa0`
       `\s. read X0 s = in_p /\ read X2 s = out_p /\ read X3 s = tag_p /\
            read X4 s = ivec_p /\ read X6 s = htable_p /\ read SP s = stackpointer /\
            read X1 s = word loop_count /\ read X16 s = word loop_remain /\
            read (memory :> bytes64 (word_add stackpointer (word 88))) s = returnaddress` THEN
      CONJ_TAC THENL [SAFE_SIM (1--40) THEN CLOSE_SUB; ALL_TAC] THEN

      ASM_CASES_TAC `loop_count = 0` THENL
       [REDUCE_IF0 `loop_count:num` THEN SAFE_SIM (1--1) THEN CLOSE_SUB; ALL_TAC] THEN
      REDUCE_IFN0 `loop_count:num` THEN
      ASM_CASES_TAC `loop_count = 1` THENL
       [REDUCE_IFEQ `loop_count:num` `1` THEN SAFE_SIM (1--161) THEN CLOSE_SUB; ALL_TAC] THEN
      REDUCE_IFNE `loop_count:num` `1` THEN
      ASM_CASES_TAC `loop_count = 2` THENL
       [REDUCE_IFEQ `loop_count:num` `2` THEN SAFE_SIM (1--322) THEN CLOSE_SUB; ALL_TAC] THEN
      REDUCE_IFNE `loop_count:num` `2` THEN
      SUBGOAL_THEN `3 <= loop_count` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      ENSURES_EVENTS_WHILE_UP2_TAC `loop_count - 2` `pc + 0x294` `pc + 0x514`
       `\i s. read X0 s = word_add in_p (word (64 * i + 64)) /\
              read X2 s = word_add out_p (word (64 * i)) /\
              read X3 s = tag_p /\ read X4 s = ivec_p /\ read X6 s = htable_p /\
              read SP s = stackpointer /\ read X16 s = word loop_remain /\
              read X1 s = word (loop_count - 2 - i) /\
              read (memory :> bytes64 (word_add stackpointer (word 88))) s = returnaddress` THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [ASM_ARITH_TAC;
        BEQ_NZ `1` THEN SAFE_SIM (1--125) THEN
        BEQ_NZ `2` THEN
        REPEAT CONJ_TAC THEN
        W(fun (asl,w) ->
          if is_exists w then (DEABBR THEN DISCHARGE_SAFETY_PROPERTY_TAC)
          else if is_branch_goal w then (ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE)
          else if can dest_eq w &&
                  (let l,_ = dest_eq w in
                   can (find_term (fun t -> t = `word_sub (word loop_count:int64) (word 2)`)) l)
          then (REWRITE_TAC[SUB_0] THEN GEN_REWRITE_TAC RAND_CONV [WORD_SUB] THEN
                ASM_SIMP_TAC[ARITH_RULE `3 <= loop_count ==> 2 <= loop_count`])
          else (ADDR_RECON ORELSE MEM_PRESERVE));
        REWRITE_TAC[] THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
        SUBGOAL_THEN `loop_count - 2 < 2 EXP 64` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
        SAFE_SIM (1--160) THEN CLOSE_R2_SUB;
        SAFE_SIM (1--197) THEN REPEAT CONJ_TAC THEN
        W(fun (asl,w) ->
          if is_exists w then (DEABBR THEN DISCHARGE_SAFE_ROBUST)
          else (DRAIN_ADDR ORELSE MEM_PRESERVE))];

      ALL_TAC] THEN
    (*** TAIL region of the body: pc+0xaa0 -> pc+0xb68. ***)
    ASM_CASES_TAC `loop_remain = 0` THENL
     [REDUCE_IF0 `loop_remain:num` THEN SAFE_SIM (1--1) THEN CLOSE_R2_SUB; ALL_TAC] THEN
    REDUCE_IFN0 `loop_remain:num` THEN
    ENSURES_EVENTS_WHILE_UP2_TAC `loop_remain:num` `pc + 0xaa4` `pc + 0xb68`
     `\i s. read X0 s = word_add in_p (word (64 * loop_count + 16 * i)) /\
            read X2 s = word_add out_p (word (64 * loop_count + 16 * i)) /\
            read X3 s = tag_p /\ read X4 s = ivec_p /\ read X6 s = htable_p /\
            read SP s = stackpointer /\ read X16 s = word (loop_remain - i) /\
            read (memory :> bytes64 (word_add stackpointer (word 88))) s = returnaddress` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [SAFE_SIM (1--1) THEN CLOSE_R2_SUB;
      ALL_TAC;
      REWRITE_TAC[] THEN SAFE_SIM [] THEN CLOSE_R2_SUB] THEN
    REWRITE_TAC[] THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
    SAFE_SIM (1--49) THEN CLOSE_R2_SUB;

    (*** REGION B: pc+0xb68 -> returnaddress (epilogue: mov x0,x15; rev64/str tag; rev/str ctr;   ***)
    (*** then 11 ldp; add sp; ret = 17 steps).                                                     ***)
    SAFE_SIM (1--17) THEN REPEAT CONJ_TAC THEN
    (MEM_PRESERVE ORELSE DISCHARGE_SAFETY_PROPERTY_TAC)] );;


(* ------------------------------------------------------------------------- *)
(* Certify that the whole development above is axiom-free (only the three     *)
(* basic HOL Light axioms INFINITY_AX / SELECT_AX / ETA_AX are permitted).   *)
(* ------------------------------------------------------------------------- *)

check_axioms();;
