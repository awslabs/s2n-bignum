(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

use_file_raise_failure := true;;
arm_print_log := true;;

needs "arm/proofs/base.ml";;
loadt "arm/proofs/aes_xts_decrypt_spec.ml";;

(* print_literal_from_elf "arm/aes-xts/aes_xts_decrypt_armv8.o";; *)
let aes_xts_decrypt_mc = define_assert_from_elf "aes_xts_decrypt_mc" "arm/aes-xts/aes_xts_decrypt_armv8.o"
[
  0xd10183ff;       (* arm_SUB SP SP (rvalue (word 0x60)) *)
  0x6d0227e8;       (* arm_STP D8 D9 SP (Immediate_Offset (iword (&0x20))) *)
  0x6d032fea;       (* arm_STP D10 D11 SP (Immediate_Offset (iword (&0x30))) *)
  0x6d0437ec;       (* arm_STP D12 D13 SP (Immediate_Offset (iword (&0x40))) *)
  0x6d053fee;       (* arm_STP D14 D15 SP (Immediate_Offset (iword (&0x50))) *)
  0xa90053f3;       (* arm_STP X19 X20 SP (Immediate_Offset (iword (&0x0))) *)
  0xa9015bf5;       (* arm_STP X21 X22 SP (Immediate_Offset (iword (&0x10))) *)
  0xf100405f;       (* arm_CMP X2 (rvalue (word 0x10)) *)
  0x5400570b;       (* arm_BLT (word 0xae0) *)
  0xd503201f;       (* arm_NOP *)
  0xd503201f;       (* arm_NOP *)
  0xd503201f;       (* arm_NOP *)
  0xd503201f;       (* arm_NOP *)
  0xd503201f;       (* arm_NOP *)
  0xd503201f;       (* arm_NOP *)
  0xd503201f;       (* arm_NOP *)
  0x92400c55;       (* arm_AND X21 X2 (rvalue (word 0xf)) *)
  0x927cec42;       (* arm_AND X2 X2 (rvalue (word 0xfffffffffffffff0)) *)
  0xb940f086;       (* arm_LDR W6 X4 (Immediate_Offset (word 0xf0)) *)
  0x4cdf7880;       (* arm_LDR Q0 X4 (Postimmediate_Offset (word 0x10)) *)
  0x4c4070a6;       (* arm_LDR Q6 X5 No_Offset *)
  0x510008c6;       (* arm_SUB W6 W6 (rvalue (word 0x2)) *)
  0x4cdf7881;       (* arm_LDR Q1 X4 (Postimmediate_Offset (word 0x10)) *)
  0x4e284806;       (* arm_AESE Q6 Q0 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4cdf7880;       (* arm_LDR Q0 X4 (Postimmediate_Offset (word 0x10)) *)
  0x710008c6;       (* arm_SUBS W6 W6 (rvalue (word 0x2)) *)
  0x4e284826;       (* arm_AESE Q6 Q1 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4cdf7881;       (* arm_LDR Q1 X4 (Postimmediate_Offset (word 0x10)) *)
  0x54ffff2c;       (* arm_BGT (word 0x1fffe4) *)
  0x4e284806;       (* arm_AESE Q6 Q0 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4c407880;       (* arm_LDR Q0 X4 No_Offset *)
  0x4e284826;       (* arm_AESE Q6 Q1 *)
  0x6e201cc6;       (* arm_EOR_VEC Q6 Q6 Q0 0x80 *)
  0x9e6600c9;       (* arm_FMOV_FtoI X9 Q6 0x0 0x40 *)
  0x9eae00ca;       (* arm_FMOV_FtoI X10 Q6 0x1 0x40 *)
  0x528010f3;       (* arm_MOV W19 (rvalue (word 0x87)) *)
  0x93ca8156;       (* arm_ROR X22 X10 0x20 *)
  0x93c9fd4a;       (* arm_EXTR X10 X10 X9 0x3f *)
  0x0a967e6b;       (* arm_AND W11 W19 (Shiftedreg W22 ASR 0x1f) *)
  0xca090569;       (* arm_EOR X9 X11 (Shiftedreg X9 LSL 0x1) *)
  0x9e670128;       (* arm_FMOV_ItoF Q8 X9 0x0 *)
  0x9eaf0148;       (* arm_FMOV_ItoF Q8 X10 0x1 *)
  0xaa0303e7;       (* arm_MOV X7 X3 *)
  0x4cdfa8f0;       (* arm_LDP Q16 Q17 X7 (Postimmediate_Offset (word 0x20)) *)
  0x4cdfa8ec;       (* arm_LDP Q12 Q13 X7 (Postimmediate_Offset (word 0x20)) *)
  0x4cdfa8ee;       (* arm_LDP Q14 Q15 X7 (Postimmediate_Offset (word 0x20)) *)
  0x4cdfa8e4;       (* arm_LDP Q4 Q5 X7 (Postimmediate_Offset (word 0x20)) *)
  0x4cdfa8f2;       (* arm_LDP Q18 Q19 X7 (Postimmediate_Offset (word 0x20)) *)
  0x4cdfa8f4;       (* arm_LDP Q20 Q21 X7 (Postimmediate_Offset (word 0x20)) *)
  0x4cdfa8f6;       (* arm_LDP Q22 Q23 X7 (Postimmediate_Offset (word 0x20)) *)
  0x4c4078e7;       (* arm_LDR Q7 X7 No_Offset *)
  0xf2400ebf;       (* arm_TST X21 (rvalue (word 0xf)) *)
  0x54000080;       (* arm_BEQ (word 0x10) *)
  0xf1004042;       (* arm_SUBS X2 X2 (rvalue (word 0x10)) *)
  0xf100405f;       (* arm_CMP X2 (rvalue (word 0x10)) *)
  0x5400492b;       (* arm_BLT (word 0x924) *)
  0xb202e7e8;       (* arm_MOV X8 (rvalue (word 0xcccccccccccccccc)) *)
  0xf29999a8;       (* arm_MOVK X8 (word 0xcccd) 0x0 *)
  0x9bc87c48;       (* arm_UMULH X8 X2 X8 *)
  0xd346fd08;       (* arm_LSR X8 X8 0x6 *)
  0xf100805f;       (* arm_CMP X2 (rvalue (word 0x20)) *)
  0x54004343;       (* arm_BCC (word 0x868) *)
  0xf100c05f;       (* arm_CMP X2 (rvalue (word 0x30)) *)
  0x54003a23;       (* arm_BCC (word 0x744) *)
  0x93ca8156;       (* arm_ROR X22 X10 0x20 *)
  0x93c9fd4a;       (* arm_EXTR X10 X10 X9 0x3f *)
  0x0a967e6b;       (* arm_AND W11 W19 (Shiftedreg W22 ASR 0x1f) *)
  0xca090569;       (* arm_EOR X9 X11 (Shiftedreg X9 LSL 0x1) *)
  0x9e670129;       (* arm_FMOV_ItoF Q9 X9 0x0 *)
  0x9eaf0149;       (* arm_FMOV_ItoF Q9 X10 0x1 *)
  0xf101005f;       (* arm_CMP X2 (rvalue (word 0x40)) *)
  0x54002c43;       (* arm_BCC (word 0x588) *)
  0x93ca8156;       (* arm_ROR X22 X10 0x20 *)
  0x93c9fd4a;       (* arm_EXTR X10 X10 X9 0x3f *)
  0x0a967e6b;       (* arm_AND W11 W19 (Shiftedreg W22 ASR 0x1f) *)
  0xca090569;       (* arm_EOR X9 X11 (Shiftedreg X9 LSL 0x1) *)
  0x9e67012a;       (* arm_FMOV_ItoF Q10 X9 0x0 *)
  0x9eaf014a;       (* arm_FMOV_ItoF Q10 X10 0x1 *)
  0xf101405f;       (* arm_CMP X2 (rvalue (word 0x50)) *)
  0x54001a43;       (* arm_BCC (word 0x348) *)
  0x93ca8156;       (* arm_ROR X22 X10 0x20 *)
  0x93c9fd4a;       (* arm_EXTR X10 X10 X9 0x3f *)
  0x0a967e6b;       (* arm_AND W11 W19 (Shiftedreg W22 ASR 0x1f) *)
  0xca090569;       (* arm_EOR X9 X11 (Shiftedreg X9 LSL 0x1) *)
  0x9e67012b;       (* arm_FMOV_ItoF Q11 X9 0x0 *)
  0x9eaf014b;       (* arm_FMOV_ItoF Q11 X10 0x1 *)
  0xd503201f;       (* arm_NOP *)
  0xd503201f;       (* arm_NOP *)
  0xd503201f;       (* arm_NOP *)
  0xacc28400;       (* arm_LDP Q0 Q1 X0 (Postimmediate_Offset (iword (&0x50))) *)
  0xad7ee418;       (* arm_LDP Q24 Q25 X0 (Immediate_Offset (iword (-- &0x30))) *)
  0x3cdf001a;       (* arm_LDR Q26 X0 (Immediate_Offset (word 0xfffffffffffffff0)) *)
  0x6e261c00;       (* arm_EOR_VEC Q0 Q0 Q6 0x80 *)
  0x6e281c21;       (* arm_EOR_VEC Q1 Q1 Q8 0x80 *)
  0x6e291f18;       (* arm_EOR_VEC Q24 Q24 Q9 0x80 *)
  0x6e2a1f39;       (* arm_EOR_VEC Q25 Q25 Q10 0x80 *)
  0x6e2b1f5a;       (* arm_EOR_VEC Q26 Q26 Q11 0x80 *)
  0x4e285a00;       (* arm_AESD Q0 Q16 *)
  0x4e287800;       (* arm_AESIMC Q0 Q0 *)
  0x4e285a01;       (* arm_AESD Q1 Q16 *)
  0x4e287821;       (* arm_AESIMC Q1 Q1 *)
  0x4e285a18;       (* arm_AESD Q24 Q16 *)
  0x4e287b18;       (* arm_AESIMC Q24 Q24 *)
  0x4e285a19;       (* arm_AESD Q25 Q16 *)
  0x4e287b39;       (* arm_AESIMC Q25 Q25 *)
  0x4e285a1a;       (* arm_AESD Q26 Q16 *)
  0x4e287b5a;       (* arm_AESIMC Q26 Q26 *)
  0x4e285a20;       (* arm_AESD Q0 Q17 *)
  0x4e287800;       (* arm_AESIMC Q0 Q0 *)
  0x4e285a21;       (* arm_AESD Q1 Q17 *)
  0x4e287821;       (* arm_AESIMC Q1 Q1 *)
  0x4e285a38;       (* arm_AESD Q24 Q17 *)
  0x4e287b18;       (* arm_AESIMC Q24 Q24 *)
  0x4e285a39;       (* arm_AESD Q25 Q17 *)
  0x4e287b39;       (* arm_AESIMC Q25 Q25 *)
  0x4e285a3a;       (* arm_AESD Q26 Q17 *)
  0x4e287b5a;       (* arm_AESIMC Q26 Q26 *)
  0x4e285980;       (* arm_AESD Q0 Q12 *)
  0x4e287800;       (* arm_AESIMC Q0 Q0 *)
  0x4e285981;       (* arm_AESD Q1 Q12 *)
  0x4e287821;       (* arm_AESIMC Q1 Q1 *)
  0x4e285998;       (* arm_AESD Q24 Q12 *)
  0x4e287b18;       (* arm_AESIMC Q24 Q24 *)
  0x4e285999;       (* arm_AESD Q25 Q12 *)
  0x4e287b39;       (* arm_AESIMC Q25 Q25 *)
  0x4e28599a;       (* arm_AESD Q26 Q12 *)
  0x4e287b5a;       (* arm_AESIMC Q26 Q26 *)
  0x4e2859a0;       (* arm_AESD Q0 Q13 *)
  0x4e287800;       (* arm_AESIMC Q0 Q0 *)
  0x4e2859a1;       (* arm_AESD Q1 Q13 *)
  0x4e287821;       (* arm_AESIMC Q1 Q1 *)
  0x4e2859b8;       (* arm_AESD Q24 Q13 *)
  0x4e287b18;       (* arm_AESIMC Q24 Q24 *)
  0x4e2859b9;       (* arm_AESD Q25 Q13 *)
  0x4e287b39;       (* arm_AESIMC Q25 Q25 *)
  0x4e2859ba;       (* arm_AESD Q26 Q13 *)
  0x4e287b5a;       (* arm_AESIMC Q26 Q26 *)
  0x4e2859c0;       (* arm_AESD Q0 Q14 *)
  0x4e287800;       (* arm_AESIMC Q0 Q0 *)
  0x4e2859c1;       (* arm_AESD Q1 Q14 *)
  0x4e287821;       (* arm_AESIMC Q1 Q1 *)
  0x4e2859d8;       (* arm_AESD Q24 Q14 *)
  0x4e287b18;       (* arm_AESIMC Q24 Q24 *)
  0x4e2859d9;       (* arm_AESD Q25 Q14 *)
  0x4e287b39;       (* arm_AESIMC Q25 Q25 *)
  0x4e2859da;       (* arm_AESD Q26 Q14 *)
  0x4e287b5a;       (* arm_AESIMC Q26 Q26 *)
  0x4e2859e0;       (* arm_AESD Q0 Q15 *)
  0x4e287800;       (* arm_AESIMC Q0 Q0 *)
  0x4e2859e1;       (* arm_AESD Q1 Q15 *)
  0x4e287821;       (* arm_AESIMC Q1 Q1 *)
  0x4e2859f8;       (* arm_AESD Q24 Q15 *)
  0x4e287b18;       (* arm_AESIMC Q24 Q24 *)
  0x4e2859f9;       (* arm_AESD Q25 Q15 *)
  0x4e287b39;       (* arm_AESIMC Q25 Q25 *)
  0x4e2859fa;       (* arm_AESD Q26 Q15 *)
  0x4e287b5a;       (* arm_AESIMC Q26 Q26 *)
  0x4e285880;       (* arm_AESD Q0 Q4 *)
  0x4e287800;       (* arm_AESIMC Q0 Q0 *)
  0x4e285881;       (* arm_AESD Q1 Q4 *)
  0x4e287821;       (* arm_AESIMC Q1 Q1 *)
  0x4e285898;       (* arm_AESD Q24 Q4 *)
  0x4e287b18;       (* arm_AESIMC Q24 Q24 *)
  0x4e285899;       (* arm_AESD Q25 Q4 *)
  0x4e287b39;       (* arm_AESIMC Q25 Q25 *)
  0x4e28589a;       (* arm_AESD Q26 Q4 *)
  0x4e287b5a;       (* arm_AESIMC Q26 Q26 *)
  0x4e2858a0;       (* arm_AESD Q0 Q5 *)
  0x4e287800;       (* arm_AESIMC Q0 Q0 *)
  0x4e2858a1;       (* arm_AESD Q1 Q5 *)
  0x4e287821;       (* arm_AESIMC Q1 Q1 *)
  0x4e2858b8;       (* arm_AESD Q24 Q5 *)
  0x4e287b18;       (* arm_AESIMC Q24 Q24 *)
  0x4e2858b9;       (* arm_AESD Q25 Q5 *)
  0x4e287b39;       (* arm_AESIMC Q25 Q25 *)
  0x4e2858ba;       (* arm_AESD Q26 Q5 *)
  0x4e287b5a;       (* arm_AESIMC Q26 Q26 *)
  0x4e285a40;       (* arm_AESD Q0 Q18 *)
  0x4e287800;       (* arm_AESIMC Q0 Q0 *)
  0x4e285a41;       (* arm_AESD Q1 Q18 *)
  0x4e287821;       (* arm_AESIMC Q1 Q1 *)
  0x4e285a58;       (* arm_AESD Q24 Q18 *)
  0x4e287b18;       (* arm_AESIMC Q24 Q24 *)
  0x4e285a59;       (* arm_AESD Q25 Q18 *)
  0x4e287b39;       (* arm_AESIMC Q25 Q25 *)
  0x4e285a5a;       (* arm_AESD Q26 Q18 *)
  0x4e287b5a;       (* arm_AESIMC Q26 Q26 *)
  0x4e285a60;       (* arm_AESD Q0 Q19 *)
  0x4e287800;       (* arm_AESIMC Q0 Q0 *)
  0x4e285a61;       (* arm_AESD Q1 Q19 *)
  0x4e287821;       (* arm_AESIMC Q1 Q1 *)
  0x4e285a78;       (* arm_AESD Q24 Q19 *)
  0x4e287b18;       (* arm_AESIMC Q24 Q24 *)
  0x4e285a79;       (* arm_AESD Q25 Q19 *)
  0x4e287b39;       (* arm_AESIMC Q25 Q25 *)
  0x4e285a7a;       (* arm_AESD Q26 Q19 *)
  0x4e287b5a;       (* arm_AESIMC Q26 Q26 *)
  0x4e285a80;       (* arm_AESD Q0 Q20 *)
  0x4e287800;       (* arm_AESIMC Q0 Q0 *)
  0x4e285a81;       (* arm_AESD Q1 Q20 *)
  0x4e287821;       (* arm_AESIMC Q1 Q1 *)
  0x4e285a98;       (* arm_AESD Q24 Q20 *)
  0x4e287b18;       (* arm_AESIMC Q24 Q24 *)
  0x4e285a99;       (* arm_AESD Q25 Q20 *)
  0x4e287b39;       (* arm_AESIMC Q25 Q25 *)
  0x4e285a9a;       (* arm_AESD Q26 Q20 *)
  0x4e287b5a;       (* arm_AESIMC Q26 Q26 *)
  0x4e285aa0;       (* arm_AESD Q0 Q21 *)
  0x4e287800;       (* arm_AESIMC Q0 Q0 *)
  0x4e285aa1;       (* arm_AESD Q1 Q21 *)
  0x4e287821;       (* arm_AESIMC Q1 Q1 *)
  0x4e285ab8;       (* arm_AESD Q24 Q21 *)
  0x4e287b18;       (* arm_AESIMC Q24 Q24 *)
  0x4e285ab9;       (* arm_AESD Q25 Q21 *)
  0x4e287b39;       (* arm_AESIMC Q25 Q25 *)
  0x4e285aba;       (* arm_AESD Q26 Q21 *)
  0x4e287b5a;       (* arm_AESIMC Q26 Q26 *)
  0x4e285ac0;       (* arm_AESD Q0 Q22 *)
  0x4e287800;       (* arm_AESIMC Q0 Q0 *)
  0x4e285ac1;       (* arm_AESD Q1 Q22 *)
  0x4e287821;       (* arm_AESIMC Q1 Q1 *)
  0x4e285ad8;       (* arm_AESD Q24 Q22 *)
  0x4e287b18;       (* arm_AESIMC Q24 Q24 *)
  0x4e285ad9;       (* arm_AESD Q25 Q22 *)
  0x4e287b39;       (* arm_AESIMC Q25 Q25 *)
  0x4e285ada;       (* arm_AESD Q26 Q22 *)
  0x4e287b5a;       (* arm_AESIMC Q26 Q26 *)
  0x4e285ae0;       (* arm_AESD Q0 Q23 *)
  0x4e285ae1;       (* arm_AESD Q1 Q23 *)
  0x4e285af8;       (* arm_AESD Q24 Q23 *)
  0x4e285af9;       (* arm_AESD Q25 Q23 *)
  0x4e285afa;       (* arm_AESD Q26 Q23 *)
  0x6e271c00;       (* arm_EOR_VEC Q0 Q0 Q7 0x80 *)
  0x6e261c00;       (* arm_EOR_VEC Q0 Q0 Q6 0x80 *)
  0x93ca8156;       (* arm_ROR X22 X10 0x20 *)
  0x93c9fd4a;       (* arm_EXTR X10 X10 X9 0x3f *)
  0x0a967e6b;       (* arm_AND W11 W19 (Shiftedreg W22 ASR 0x1f) *)
  0xca090569;       (* arm_EOR X9 X11 (Shiftedreg X9 LSL 0x1) *)
  0x9e670126;       (* arm_FMOV_ItoF Q6 X9 0x0 *)
  0x9eaf0146;       (* arm_FMOV_ItoF Q6 X10 0x1 *)
  0x6e271c21;       (* arm_EOR_VEC Q1 Q1 Q7 0x80 *)
  0x6e281c21;       (* arm_EOR_VEC Q1 Q1 Q8 0x80 *)
  0x93ca8156;       (* arm_ROR X22 X10 0x20 *)
  0x93c9fd4a;       (* arm_EXTR X10 X10 X9 0x3f *)
  0x0a967e6b;       (* arm_AND W11 W19 (Shiftedreg W22 ASR 0x1f) *)
  0xca090569;       (* arm_EOR X9 X11 (Shiftedreg X9 LSL 0x1) *)
  0x9e670128;       (* arm_FMOV_ItoF Q8 X9 0x0 *)
  0x9eaf0148;       (* arm_FMOV_ItoF Q8 X10 0x1 *)
  0x6e271f18;       (* arm_EOR_VEC Q24 Q24 Q7 0x80 *)
  0x6e291f18;       (* arm_EOR_VEC Q24 Q24 Q9 0x80 *)
  0x93ca8156;       (* arm_ROR X22 X10 0x20 *)
  0x93c9fd4a;       (* arm_EXTR X10 X10 X9 0x3f *)
  0x0a967e6b;       (* arm_AND W11 W19 (Shiftedreg W22 ASR 0x1f) *)
  0xca090569;       (* arm_EOR X9 X11 (Shiftedreg X9 LSL 0x1) *)
  0x9e670129;       (* arm_FMOV_ItoF Q9 X9 0x0 *)
  0x9eaf0149;       (* arm_FMOV_ItoF Q9 X10 0x1 *)
  0x6e271f39;       (* arm_EOR_VEC Q25 Q25 Q7 0x80 *)
  0x6e2a1f39;       (* arm_EOR_VEC Q25 Q25 Q10 0x80 *)
  0x93ca8156;       (* arm_ROR X22 X10 0x20 *)
  0x93c9fd4a;       (* arm_EXTR X10 X10 X9 0x3f *)
  0x0a967e6b;       (* arm_AND W11 W19 (Shiftedreg W22 ASR 0x1f) *)
  0xca090569;       (* arm_EOR X9 X11 (Shiftedreg X9 LSL 0x1) *)
  0x9e67012a;       (* arm_FMOV_ItoF Q10 X9 0x0 *)
  0x9eaf014a;       (* arm_FMOV_ItoF Q10 X10 0x1 *)
  0x6e271f5a;       (* arm_EOR_VEC Q26 Q26 Q7 0x80 *)
  0x6e2b1f5a;       (* arm_EOR_VEC Q26 Q26 Q11 0x80 *)
  0x93ca8156;       (* arm_ROR X22 X10 0x20 *)
  0x93c9fd4a;       (* arm_EXTR X10 X10 X9 0x3f *)
  0x0a967e6b;       (* arm_AND W11 W19 (Shiftedreg W22 ASR 0x1f) *)
  0xca090569;       (* arm_EOR X9 X11 (Shiftedreg X9 LSL 0x1) *)
  0x9e67012b;       (* arm_FMOV_ItoF Q11 X9 0x0 *)
  0x9eaf014b;       (* arm_FMOV_ItoF Q11 X10 0x1 *)
  0xac828420;       (* arm_STP Q0 Q1 X1 (Postimmediate_Offset (iword (&0x50))) *)
  0xad3ee438;       (* arm_STP Q24 Q25 X1 (Immediate_Offset (iword (-- &0x30))) *)
  0x3c9f003a;       (* arm_STR Q26 X1 (Immediate_Offset (word 0xfffffffffffffff0)) *)
  0xf1014042;       (* arm_SUBS X2 X2 (rvalue (word 0x50)) *)
  0xf1000508;       (* arm_SUBS X8 X8 (rvalue (word 0x1)) *)
  0xb5ffe888;       (* arm_CBNZ X8 (word 0x1ffd10) *)
  0xf101005f;       (* arm_CMP X2 (rvalue (word 0x40)) *)
  0x54000140;       (* arm_BEQ (word 0x28) *)
  0xf100c05f;       (* arm_CMP X2 (rvalue (word 0x30)) *)
  0x54001200;       (* arm_BEQ (word 0x240) *)
  0xf100805f;       (* arm_CMP X2 (rvalue (word 0x20)) *)
  0x54001ea0;       (* arm_BEQ (word 0x3d4) *)
  0xf100405f;       (* arm_CMP X2 (rvalue (word 0x10)) *)
  0x54002740;       (* arm_BEQ (word 0x4e8) *)
  0x14000162;       (* arm_B (word 0x588) *)
  0xd503201f;       (* arm_NOP *)
  0xd503201f;       (* arm_NOP *)
  0x4cdfa000;       (* arm_LDP Q0 Q1 X0 (Postimmediate_Offset (word 0x20)) *)
  0x4cdfa018;       (* arm_LDP Q24 Q25 X0 (Postimmediate_Offset (word 0x20)) *)
  0x6e261c00;       (* arm_EOR_VEC Q0 Q0 Q6 0x80 *)
  0x6e281c21;       (* arm_EOR_VEC Q1 Q1 Q8 0x80 *)
  0x6e291f18;       (* arm_EOR_VEC Q24 Q24 Q9 0x80 *)
  0x6e2a1f39;       (* arm_EOR_VEC Q25 Q25 Q10 0x80 *)
  0x4e285a00;       (* arm_AESD Q0 Q16 *)
  0x4e287800;       (* arm_AESIMC Q0 Q0 *)
  0x4e285a01;       (* arm_AESD Q1 Q16 *)
  0x4e287821;       (* arm_AESIMC Q1 Q1 *)
  0x4e285a18;       (* arm_AESD Q24 Q16 *)
  0x4e287b18;       (* arm_AESIMC Q24 Q24 *)
  0x4e285a19;       (* arm_AESD Q25 Q16 *)
  0x4e287b39;       (* arm_AESIMC Q25 Q25 *)
  0x4e285a20;       (* arm_AESD Q0 Q17 *)
  0x4e287800;       (* arm_AESIMC Q0 Q0 *)
  0x4e285a21;       (* arm_AESD Q1 Q17 *)
  0x4e287821;       (* arm_AESIMC Q1 Q1 *)
  0x4e285a38;       (* arm_AESD Q24 Q17 *)
  0x4e287b18;       (* arm_AESIMC Q24 Q24 *)
  0x4e285a39;       (* arm_AESD Q25 Q17 *)
  0x4e287b39;       (* arm_AESIMC Q25 Q25 *)
  0x4e285980;       (* arm_AESD Q0 Q12 *)
  0x4e287800;       (* arm_AESIMC Q0 Q0 *)
  0x4e285981;       (* arm_AESD Q1 Q12 *)
  0x4e287821;       (* arm_AESIMC Q1 Q1 *)
  0x4e285998;       (* arm_AESD Q24 Q12 *)
  0x4e287b18;       (* arm_AESIMC Q24 Q24 *)
  0x4e285999;       (* arm_AESD Q25 Q12 *)
  0x4e287b39;       (* arm_AESIMC Q25 Q25 *)
  0x4e2859a0;       (* arm_AESD Q0 Q13 *)
  0x4e287800;       (* arm_AESIMC Q0 Q0 *)
  0x4e2859a1;       (* arm_AESD Q1 Q13 *)
  0x4e287821;       (* arm_AESIMC Q1 Q1 *)
  0x4e2859b8;       (* arm_AESD Q24 Q13 *)
  0x4e287b18;       (* arm_AESIMC Q24 Q24 *)
  0x4e2859b9;       (* arm_AESD Q25 Q13 *)
  0x4e287b39;       (* arm_AESIMC Q25 Q25 *)
  0x4e2859c0;       (* arm_AESD Q0 Q14 *)
  0x4e287800;       (* arm_AESIMC Q0 Q0 *)
  0x4e2859c1;       (* arm_AESD Q1 Q14 *)
  0x4e287821;       (* arm_AESIMC Q1 Q1 *)
  0x4e2859d8;       (* arm_AESD Q24 Q14 *)
  0x4e287b18;       (* arm_AESIMC Q24 Q24 *)
  0x4e2859d9;       (* arm_AESD Q25 Q14 *)
  0x4e287b39;       (* arm_AESIMC Q25 Q25 *)
  0x4e2859e0;       (* arm_AESD Q0 Q15 *)
  0x4e287800;       (* arm_AESIMC Q0 Q0 *)
  0x4e2859e1;       (* arm_AESD Q1 Q15 *)
  0x4e287821;       (* arm_AESIMC Q1 Q1 *)
  0x4e2859f8;       (* arm_AESD Q24 Q15 *)
  0x4e287b18;       (* arm_AESIMC Q24 Q24 *)
  0x4e2859f9;       (* arm_AESD Q25 Q15 *)
  0x4e287b39;       (* arm_AESIMC Q25 Q25 *)
  0x4e285880;       (* arm_AESD Q0 Q4 *)
  0x4e287800;       (* arm_AESIMC Q0 Q0 *)
  0x4e285881;       (* arm_AESD Q1 Q4 *)
  0x4e287821;       (* arm_AESIMC Q1 Q1 *)
  0x4e285898;       (* arm_AESD Q24 Q4 *)
  0x4e287b18;       (* arm_AESIMC Q24 Q24 *)
  0x4e285899;       (* arm_AESD Q25 Q4 *)
  0x4e287b39;       (* arm_AESIMC Q25 Q25 *)
  0x4e2858a0;       (* arm_AESD Q0 Q5 *)
  0x4e287800;       (* arm_AESIMC Q0 Q0 *)
  0x4e2858a1;       (* arm_AESD Q1 Q5 *)
  0x4e287821;       (* arm_AESIMC Q1 Q1 *)
  0x4e2858b8;       (* arm_AESD Q24 Q5 *)
  0x4e287b18;       (* arm_AESIMC Q24 Q24 *)
  0x4e2858b9;       (* arm_AESD Q25 Q5 *)
  0x4e287b39;       (* arm_AESIMC Q25 Q25 *)
  0x4e285a40;       (* arm_AESD Q0 Q18 *)
  0x4e287800;       (* arm_AESIMC Q0 Q0 *)
  0x4e285a41;       (* arm_AESD Q1 Q18 *)
  0x4e287821;       (* arm_AESIMC Q1 Q1 *)
  0x4e285a58;       (* arm_AESD Q24 Q18 *)
  0x4e287b18;       (* arm_AESIMC Q24 Q24 *)
  0x4e285a59;       (* arm_AESD Q25 Q18 *)
  0x4e287b39;       (* arm_AESIMC Q25 Q25 *)
  0x4e285a60;       (* arm_AESD Q0 Q19 *)
  0x4e287800;       (* arm_AESIMC Q0 Q0 *)
  0x4e285a61;       (* arm_AESD Q1 Q19 *)
  0x4e287821;       (* arm_AESIMC Q1 Q1 *)
  0x4e285a78;       (* arm_AESD Q24 Q19 *)
  0x4e287b18;       (* arm_AESIMC Q24 Q24 *)
  0x4e285a79;       (* arm_AESD Q25 Q19 *)
  0x4e287b39;       (* arm_AESIMC Q25 Q25 *)
  0x4e285a80;       (* arm_AESD Q0 Q20 *)
  0x4e287800;       (* arm_AESIMC Q0 Q0 *)
  0x4e285a81;       (* arm_AESD Q1 Q20 *)
  0x4e287821;       (* arm_AESIMC Q1 Q1 *)
  0x4e285a98;       (* arm_AESD Q24 Q20 *)
  0x4e287b18;       (* arm_AESIMC Q24 Q24 *)
  0x4e285a99;       (* arm_AESD Q25 Q20 *)
  0x4e287b39;       (* arm_AESIMC Q25 Q25 *)
  0x4e285aa0;       (* arm_AESD Q0 Q21 *)
  0x4e287800;       (* arm_AESIMC Q0 Q0 *)
  0x4e285aa1;       (* arm_AESD Q1 Q21 *)
  0x4e287821;       (* arm_AESIMC Q1 Q1 *)
  0x4e285ab8;       (* arm_AESD Q24 Q21 *)
  0x4e287b18;       (* arm_AESIMC Q24 Q24 *)
  0x4e285ab9;       (* arm_AESD Q25 Q21 *)
  0x4e287b39;       (* arm_AESIMC Q25 Q25 *)
  0x4e285ac0;       (* arm_AESD Q0 Q22 *)
  0x4e287800;       (* arm_AESIMC Q0 Q0 *)
  0x4e285ac1;       (* arm_AESD Q1 Q22 *)
  0x4e287821;       (* arm_AESIMC Q1 Q1 *)
  0x4e285ad8;       (* arm_AESD Q24 Q22 *)
  0x4e287b18;       (* arm_AESIMC Q24 Q24 *)
  0x4e285ad9;       (* arm_AESD Q25 Q22 *)
  0x4e287b39;       (* arm_AESIMC Q25 Q25 *)
  0x4e285ae0;       (* arm_AESD Q0 Q23 *)
  0x4e285ae1;       (* arm_AESD Q1 Q23 *)
  0x4e285af8;       (* arm_AESD Q24 Q23 *)
  0x4e285af9;       (* arm_AESD Q25 Q23 *)
  0x6e271c00;       (* arm_EOR_VEC Q0 Q0 Q7 0x80 *)
  0x6e261c00;       (* arm_EOR_VEC Q0 Q0 Q6 0x80 *)
  0x6e271c21;       (* arm_EOR_VEC Q1 Q1 Q7 0x80 *)
  0x6e281c21;       (* arm_EOR_VEC Q1 Q1 Q8 0x80 *)
  0x6e271f18;       (* arm_EOR_VEC Q24 Q24 Q7 0x80 *)
  0x6e291f18;       (* arm_EOR_VEC Q24 Q24 Q9 0x80 *)
  0x6e271f39;       (* arm_EOR_VEC Q25 Q25 Q7 0x80 *)
  0x6e2a1f39;       (* arm_EOR_VEC Q25 Q25 Q10 0x80 *)
  0x9e660149;       (* arm_FMOV_FtoI X9 Q10 0x0 0x40 *)
  0x9eae014a;       (* arm_FMOV_FtoI X10 Q10 0x1 0x40 *)
  0x93ca8156;       (* arm_ROR X22 X10 0x20 *)
  0x93c9fd4a;       (* arm_EXTR X10 X10 X9 0x3f *)
  0x0a967e6b;       (* arm_AND W11 W19 (Shiftedreg W22 ASR 0x1f) *)
  0xca090569;       (* arm_EOR X9 X11 (Shiftedreg X9 LSL 0x1) *)
  0x9e670126;       (* arm_FMOV_ItoF Q6 X9 0x0 *)
  0x9eaf0146;       (* arm_FMOV_ItoF Q6 X10 0x1 *)
  0x4c9fa020;       (* arm_STP Q0 Q1 X1 (Postimmediate_Offset (word 0x20)) *)
  0x4c9fa038;       (* arm_STP Q24 Q25 X1 (Postimmediate_Offset (word 0x20)) *)
  0x140000db;       (* arm_B (word 0x36c) *)
  0xd503201f;       (* arm_NOP *)
  0xd503201f;       (* arm_NOP *)
  0xd503201f;       (* arm_NOP *)
  0x4cdfa000;       (* arm_LDP Q0 Q1 X0 (Postimmediate_Offset (word 0x20)) *)
  0x4cdf7018;       (* arm_LDR Q24 X0 (Postimmediate_Offset (word 0x10)) *)
  0x6e261c00;       (* arm_EOR_VEC Q0 Q0 Q6 0x80 *)
  0x6e281c21;       (* arm_EOR_VEC Q1 Q1 Q8 0x80 *)
  0x6e291f18;       (* arm_EOR_VEC Q24 Q24 Q9 0x80 *)
  0x4e285a00;       (* arm_AESD Q0 Q16 *)
  0x4e287800;       (* arm_AESIMC Q0 Q0 *)
  0x4e285a01;       (* arm_AESD Q1 Q16 *)
  0x4e287821;       (* arm_AESIMC Q1 Q1 *)
  0x4e285a18;       (* arm_AESD Q24 Q16 *)
  0x4e287b18;       (* arm_AESIMC Q24 Q24 *)
  0x4e285a20;       (* arm_AESD Q0 Q17 *)
  0x4e287800;       (* arm_AESIMC Q0 Q0 *)
  0x4e285a21;       (* arm_AESD Q1 Q17 *)
  0x4e287821;       (* arm_AESIMC Q1 Q1 *)
  0x4e285a38;       (* arm_AESD Q24 Q17 *)
  0x4e287b18;       (* arm_AESIMC Q24 Q24 *)
  0x4e285980;       (* arm_AESD Q0 Q12 *)
  0x4e287800;       (* arm_AESIMC Q0 Q0 *)
  0x4e285981;       (* arm_AESD Q1 Q12 *)
  0x4e287821;       (* arm_AESIMC Q1 Q1 *)
  0x4e285998;       (* arm_AESD Q24 Q12 *)
  0x4e287b18;       (* arm_AESIMC Q24 Q24 *)
  0x4e2859a0;       (* arm_AESD Q0 Q13 *)
  0x4e287800;       (* arm_AESIMC Q0 Q0 *)
  0x4e2859a1;       (* arm_AESD Q1 Q13 *)
  0x4e287821;       (* arm_AESIMC Q1 Q1 *)
  0x4e2859b8;       (* arm_AESD Q24 Q13 *)
  0x4e287b18;       (* arm_AESIMC Q24 Q24 *)
  0x4e2859c0;       (* arm_AESD Q0 Q14 *)
  0x4e287800;       (* arm_AESIMC Q0 Q0 *)
  0x4e2859c1;       (* arm_AESD Q1 Q14 *)
  0x4e287821;       (* arm_AESIMC Q1 Q1 *)
  0x4e2859d8;       (* arm_AESD Q24 Q14 *)
  0x4e287b18;       (* arm_AESIMC Q24 Q24 *)
  0x4e2859e0;       (* arm_AESD Q0 Q15 *)
  0x4e287800;       (* arm_AESIMC Q0 Q0 *)
  0x4e2859e1;       (* arm_AESD Q1 Q15 *)
  0x4e287821;       (* arm_AESIMC Q1 Q1 *)
  0x4e2859f8;       (* arm_AESD Q24 Q15 *)
  0x4e287b18;       (* arm_AESIMC Q24 Q24 *)
  0x4e285880;       (* arm_AESD Q0 Q4 *)
  0x4e287800;       (* arm_AESIMC Q0 Q0 *)
  0x4e285881;       (* arm_AESD Q1 Q4 *)
  0x4e287821;       (* arm_AESIMC Q1 Q1 *)
  0x4e285898;       (* arm_AESD Q24 Q4 *)
  0x4e287b18;       (* arm_AESIMC Q24 Q24 *)
  0x4e2858a0;       (* arm_AESD Q0 Q5 *)
  0x4e287800;       (* arm_AESIMC Q0 Q0 *)
  0x4e2858a1;       (* arm_AESD Q1 Q5 *)
  0x4e287821;       (* arm_AESIMC Q1 Q1 *)
  0x4e2858b8;       (* arm_AESD Q24 Q5 *)
  0x4e287b18;       (* arm_AESIMC Q24 Q24 *)
  0x4e285a40;       (* arm_AESD Q0 Q18 *)
  0x4e287800;       (* arm_AESIMC Q0 Q0 *)
  0x4e285a41;       (* arm_AESD Q1 Q18 *)
  0x4e287821;       (* arm_AESIMC Q1 Q1 *)
  0x4e285a58;       (* arm_AESD Q24 Q18 *)
  0x4e287b18;       (* arm_AESIMC Q24 Q24 *)
  0x4e285a60;       (* arm_AESD Q0 Q19 *)
  0x4e287800;       (* arm_AESIMC Q0 Q0 *)
  0x4e285a61;       (* arm_AESD Q1 Q19 *)
  0x4e287821;       (* arm_AESIMC Q1 Q1 *)
  0x4e285a78;       (* arm_AESD Q24 Q19 *)
  0x4e287b18;       (* arm_AESIMC Q24 Q24 *)
  0x4e285a80;       (* arm_AESD Q0 Q20 *)
  0x4e287800;       (* arm_AESIMC Q0 Q0 *)
  0x4e285a81;       (* arm_AESD Q1 Q20 *)
  0x4e287821;       (* arm_AESIMC Q1 Q1 *)
  0x4e285a98;       (* arm_AESD Q24 Q20 *)
  0x4e287b18;       (* arm_AESIMC Q24 Q24 *)
  0x4e285aa0;       (* arm_AESD Q0 Q21 *)
  0x4e287800;       (* arm_AESIMC Q0 Q0 *)
  0x4e285aa1;       (* arm_AESD Q1 Q21 *)
  0x4e287821;       (* arm_AESIMC Q1 Q1 *)
  0x4e285ab8;       (* arm_AESD Q24 Q21 *)
  0x4e287b18;       (* arm_AESIMC Q24 Q24 *)
  0x4e285ac0;       (* arm_AESD Q0 Q22 *)
  0x4e287800;       (* arm_AESIMC Q0 Q0 *)
  0x4e285ac1;       (* arm_AESD Q1 Q22 *)
  0x4e287821;       (* arm_AESIMC Q1 Q1 *)
  0x4e285ad8;       (* arm_AESD Q24 Q22 *)
  0x4e287b18;       (* arm_AESIMC Q24 Q24 *)
  0x4e285ae0;       (* arm_AESD Q0 Q23 *)
  0x4e285ae1;       (* arm_AESD Q1 Q23 *)
  0x4e285af8;       (* arm_AESD Q24 Q23 *)
  0x6e271c00;       (* arm_EOR_VEC Q0 Q0 Q7 0x80 *)
  0x6e261c00;       (* arm_EOR_VEC Q0 Q0 Q6 0x80 *)
  0x6e271c21;       (* arm_EOR_VEC Q1 Q1 Q7 0x80 *)
  0x6e281c21;       (* arm_EOR_VEC Q1 Q1 Q8 0x80 *)
  0x6e271f18;       (* arm_EOR_VEC Q24 Q24 Q7 0x80 *)
  0x6e291f18;       (* arm_EOR_VEC Q24 Q24 Q9 0x80 *)
  0x9e660129;       (* arm_FMOV_FtoI X9 Q9 0x0 0x40 *)
  0x9eae012a;       (* arm_FMOV_FtoI X10 Q9 0x1 0x40 *)
  0x93ca8156;       (* arm_ROR X22 X10 0x20 *)
  0x93c9fd4a;       (* arm_EXTR X10 X10 X9 0x3f *)
  0x0a967e6b;       (* arm_AND W11 W19 (Shiftedreg W22 ASR 0x1f) *)
  0xca090569;       (* arm_EOR X9 X11 (Shiftedreg X9 LSL 0x1) *)
  0x9e670126;       (* arm_FMOV_ItoF Q6 X9 0x0 *)
  0x9eaf0146;       (* arm_FMOV_ItoF Q6 X10 0x1 *)
  0x4c9fa020;       (* arm_STP Q0 Q1 X1 (Postimmediate_Offset (word 0x20)) *)
  0x4c9f7038;       (* arm_STR Q24 X1 (Postimmediate_Offset (word 0x10)) *)
  0x14000071;       (* arm_B (word 0x1c4) *)
  0x4cdfa000;       (* arm_LDP Q0 Q1 X0 (Postimmediate_Offset (word 0x20)) *)
  0x6e261c00;       (* arm_EOR_VEC Q0 Q0 Q6 0x80 *)
  0x6e281c21;       (* arm_EOR_VEC Q1 Q1 Q8 0x80 *)
  0x4e285a00;       (* arm_AESD Q0 Q16 *)
  0x4e287800;       (* arm_AESIMC Q0 Q0 *)
  0x4e285a01;       (* arm_AESD Q1 Q16 *)
  0x4e287821;       (* arm_AESIMC Q1 Q1 *)
  0x4e285a20;       (* arm_AESD Q0 Q17 *)
  0x4e287800;       (* arm_AESIMC Q0 Q0 *)
  0x4e285a21;       (* arm_AESD Q1 Q17 *)
  0x4e287821;       (* arm_AESIMC Q1 Q1 *)
  0x4e285980;       (* arm_AESD Q0 Q12 *)
  0x4e287800;       (* arm_AESIMC Q0 Q0 *)
  0x4e285981;       (* arm_AESD Q1 Q12 *)
  0x4e287821;       (* arm_AESIMC Q1 Q1 *)
  0x4e2859a0;       (* arm_AESD Q0 Q13 *)
  0x4e287800;       (* arm_AESIMC Q0 Q0 *)
  0x4e2859a1;       (* arm_AESD Q1 Q13 *)
  0x4e287821;       (* arm_AESIMC Q1 Q1 *)
  0x4e2859c0;       (* arm_AESD Q0 Q14 *)
  0x4e287800;       (* arm_AESIMC Q0 Q0 *)
  0x4e2859c1;       (* arm_AESD Q1 Q14 *)
  0x4e287821;       (* arm_AESIMC Q1 Q1 *)
  0x4e2859e0;       (* arm_AESD Q0 Q15 *)
  0x4e287800;       (* arm_AESIMC Q0 Q0 *)
  0x4e2859e1;       (* arm_AESD Q1 Q15 *)
  0x4e287821;       (* arm_AESIMC Q1 Q1 *)
  0x4e285880;       (* arm_AESD Q0 Q4 *)
  0x4e287800;       (* arm_AESIMC Q0 Q0 *)
  0x4e285881;       (* arm_AESD Q1 Q4 *)
  0x4e287821;       (* arm_AESIMC Q1 Q1 *)
  0x4e2858a0;       (* arm_AESD Q0 Q5 *)
  0x4e287800;       (* arm_AESIMC Q0 Q0 *)
  0x4e2858a1;       (* arm_AESD Q1 Q5 *)
  0x4e287821;       (* arm_AESIMC Q1 Q1 *)
  0x4e285a40;       (* arm_AESD Q0 Q18 *)
  0x4e287800;       (* arm_AESIMC Q0 Q0 *)
  0x4e285a41;       (* arm_AESD Q1 Q18 *)
  0x4e287821;       (* arm_AESIMC Q1 Q1 *)
  0x4e285a60;       (* arm_AESD Q0 Q19 *)
  0x4e287800;       (* arm_AESIMC Q0 Q0 *)
  0x4e285a61;       (* arm_AESD Q1 Q19 *)
  0x4e287821;       (* arm_AESIMC Q1 Q1 *)
  0x4e285a80;       (* arm_AESD Q0 Q20 *)
  0x4e287800;       (* arm_AESIMC Q0 Q0 *)
  0x4e285a81;       (* arm_AESD Q1 Q20 *)
  0x4e287821;       (* arm_AESIMC Q1 Q1 *)
  0x4e285aa0;       (* arm_AESD Q0 Q21 *)
  0x4e287800;       (* arm_AESIMC Q0 Q0 *)
  0x4e285aa1;       (* arm_AESD Q1 Q21 *)
  0x4e287821;       (* arm_AESIMC Q1 Q1 *)
  0x4e285ac0;       (* arm_AESD Q0 Q22 *)
  0x4e287800;       (* arm_AESIMC Q0 Q0 *)
  0x4e285ac1;       (* arm_AESD Q1 Q22 *)
  0x4e287821;       (* arm_AESIMC Q1 Q1 *)
  0x4e285ae0;       (* arm_AESD Q0 Q23 *)
  0x4e285ae1;       (* arm_AESD Q1 Q23 *)
  0x6e271c00;       (* arm_EOR_VEC Q0 Q0 Q7 0x80 *)
  0x6e261c00;       (* arm_EOR_VEC Q0 Q0 Q6 0x80 *)
  0x6e271c21;       (* arm_EOR_VEC Q1 Q1 Q7 0x80 *)
  0x6e281c21;       (* arm_EOR_VEC Q1 Q1 Q8 0x80 *)
  0x4c9fa020;       (* arm_STP Q0 Q1 X1 (Postimmediate_Offset (word 0x20)) *)
  0x9e660109;       (* arm_FMOV_FtoI X9 Q8 0x0 0x40 *)
  0x9eae010a;       (* arm_FMOV_FtoI X10 Q8 0x1 0x40 *)
  0x93ca8156;       (* arm_ROR X22 X10 0x20 *)
  0x93c9fd4a;       (* arm_EXTR X10 X10 X9 0x3f *)
  0x0a967e6b;       (* arm_AND W11 W19 (Shiftedreg W22 ASR 0x1f) *)
  0xca090569;       (* arm_EOR X9 X11 (Shiftedreg X9 LSL 0x1) *)
  0x9e670126;       (* arm_FMOV_ItoF Q6 X9 0x0 *)
  0x9eaf0146;       (* arm_FMOV_ItoF Q6 X10 0x1 *)
  0x1400002a;       (* arm_B (word 0xa8) *)
  0x4cdf7000;       (* arm_LDR Q0 X0 (Postimmediate_Offset (word 0x10)) *)
  0x6e261c00;       (* arm_EOR_VEC Q0 Q0 Q6 0x80 *)
  0x4e285a00;       (* arm_AESD Q0 Q16 *)
  0x4e287800;       (* arm_AESIMC Q0 Q0 *)
  0x4e285a20;       (* arm_AESD Q0 Q17 *)
  0x4e287800;       (* arm_AESIMC Q0 Q0 *)
  0x4e285980;       (* arm_AESD Q0 Q12 *)
  0x4e287800;       (* arm_AESIMC Q0 Q0 *)
  0x4e2859a0;       (* arm_AESD Q0 Q13 *)
  0x4e287800;       (* arm_AESIMC Q0 Q0 *)
  0x4e2859c0;       (* arm_AESD Q0 Q14 *)
  0x4e287800;       (* arm_AESIMC Q0 Q0 *)
  0x4e2859e0;       (* arm_AESD Q0 Q15 *)
  0x4e287800;       (* arm_AESIMC Q0 Q0 *)
  0x4e285880;       (* arm_AESD Q0 Q4 *)
  0x4e287800;       (* arm_AESIMC Q0 Q0 *)
  0x4e2858a0;       (* arm_AESD Q0 Q5 *)
  0x4e287800;       (* arm_AESIMC Q0 Q0 *)
  0x4e285a40;       (* arm_AESD Q0 Q18 *)
  0x4e287800;       (* arm_AESIMC Q0 Q0 *)
  0x4e285a60;       (* arm_AESD Q0 Q19 *)
  0x4e287800;       (* arm_AESIMC Q0 Q0 *)
  0x4e285a80;       (* arm_AESD Q0 Q20 *)
  0x4e287800;       (* arm_AESIMC Q0 Q0 *)
  0x4e285aa0;       (* arm_AESD Q0 Q21 *)
  0x4e287800;       (* arm_AESIMC Q0 Q0 *)
  0x4e285ac0;       (* arm_AESD Q0 Q22 *)
  0x4e287800;       (* arm_AESIMC Q0 Q0 *)
  0x4e285ae0;       (* arm_AESD Q0 Q23 *)
  0x6e271c00;       (* arm_EOR_VEC Q0 Q0 Q7 0x80 *)
  0x6e261c00;       (* arm_EOR_VEC Q0 Q0 Q6 0x80 *)
  0x4c9f7020;       (* arm_STR Q0 X1 (Postimmediate_Offset (word 0x10)) *)
  0x9e6600c9;       (* arm_FMOV_FtoI X9 Q6 0x0 0x40 *)
  0x9eae00ca;       (* arm_FMOV_FtoI X10 Q6 0x1 0x40 *)
  0x93ca8156;       (* arm_ROR X22 X10 0x20 *)
  0x93c9fd4a;       (* arm_EXTR X10 X10 X9 0x3f *)
  0x0a967e6b;       (* arm_AND W11 W19 (Shiftedreg W22 ASR 0x1f) *)
  0xca090569;       (* arm_EOR X9 X11 (Shiftedreg X9 LSL 0x1) *)
  0x9e670126;       (* arm_FMOV_ItoF Q6 X9 0x0 *)
  0x9eaf0146;       (* arm_FMOV_ItoF Q6 X10 0x1 *)
  0x14000001;       (* arm_B (word 0x4) *)
  0xf2400ebf;       (* arm_TST X21 (rvalue (word 0xf)) *)
  0x54000780;       (* arm_BEQ (word 0xf0) *)
  0xaa0303e7;       (* arm_MOV X7 X3 *)
  0x9e6600c9;       (* arm_FMOV_FtoI X9 Q6 0x0 0x40 *)
  0x9eae00ca;       (* arm_FMOV_FtoI X10 Q6 0x1 0x40 *)
  0x93ca8156;       (* arm_ROR X22 X10 0x20 *)
  0x93c9fd4a;       (* arm_EXTR X10 X10 X9 0x3f *)
  0x0a967e6b;       (* arm_AND W11 W19 (Shiftedreg W22 ASR 0x1f) *)
  0xca090569;       (* arm_EOR X9 X11 (Shiftedreg X9 LSL 0x1) *)
  0x9e670128;       (* arm_FMOV_ItoF Q8 X9 0x0 *)
  0x9eaf0148;       (* arm_FMOV_ItoF Q8 X10 0x1 *)
  0x4cdf7800;       (* arm_LDR Q0 X0 (Postimmediate_Offset (word 0x10)) *)
  0x6e281c1a;       (* arm_EOR_VEC Q26 Q0 Q8 0x80 *)
  0xb940f066;       (* arm_LDR W6 X3 (Immediate_Offset (word 0xf0)) *)
  0x4cdf7860;       (* arm_LDR Q0 X3 (Postimmediate_Offset (word 0x10)) *)
  0x510008c6;       (* arm_SUB W6 W6 (rvalue (word 0x2)) *)
  0x4cdf7861;       (* arm_LDR Q1 X3 (Postimmediate_Offset (word 0x10)) *)
  0x4e28581a;       (* arm_AESD Q26 Q0 *)
  0x4e287b5a;       (* arm_AESIMC Q26 Q26 *)
  0x4cdf7860;       (* arm_LDR Q0 X3 (Postimmediate_Offset (word 0x10)) *)
  0x710008c6;       (* arm_SUBS W6 W6 (rvalue (word 0x2)) *)
  0x4e28583a;       (* arm_AESD Q26 Q1 *)
  0x4e287b5a;       (* arm_AESIMC Q26 Q26 *)
  0x4cdf7861;       (* arm_LDR Q1 X3 (Postimmediate_Offset (word 0x10)) *)
  0x54ffff2c;       (* arm_BGT (word 0x1fffe4) *)
  0x4e28581a;       (* arm_AESD Q26 Q0 *)
  0x4e287b5a;       (* arm_AESIMC Q26 Q26 *)
  0x4c407860;       (* arm_LDR Q0 X3 No_Offset *)
  0x4e28583a;       (* arm_AESD Q26 Q1 *)
  0x6e201f5a;       (* arm_EOR_VEC Q26 Q26 Q0 0x80 *)
  0x6e281f5a;       (* arm_EOR_VEC Q26 Q26 Q8 0x80 *)
  0x4c00703a;       (* arm_STR Q26 X1 No_Offset *)
  0xaa0003f4;       (* arm_MOV X20 X0 *)
  0x9100402d;       (* arm_ADD X13 X1 (rvalue (word 0x10)) *)
  0xf10006b5;       (* arm_SUBS X21 X21 (rvalue (word 0x1)) *)
  0x3875682f;       (* arm_LDRB W15 X1 (Register_Offset X21) *)
  0x38756a8e;       (* arm_LDRB W14 X20 (Register_Offset X21) *)
  0x383569af;       (* arm_STRB W15 X13 (Register_Offset X21) *)
  0x3835682e;       (* arm_STRB W14 X1 (Register_Offset X21) *)
  0x54ffff6c;       (* arm_BGT (word 0x1fffec) *)
  0x4c40703a;       (* arm_LDR Q26 X1 No_Offset *)
  0x6e261f5a;       (* arm_EOR_VEC Q26 Q26 Q6 0x80 *)
  0xb940f0e6;       (* arm_LDR W6 X7 (Immediate_Offset (word 0xf0)) *)
  0x4cdf70e0;       (* arm_LDR Q0 X7 (Postimmediate_Offset (word 0x10)) *)
  0x510008c6;       (* arm_SUB W6 W6 (rvalue (word 0x2)) *)
  0x4cdf70e1;       (* arm_LDR Q1 X7 (Postimmediate_Offset (word 0x10)) *)
  0x4e28581a;       (* arm_AESD Q26 Q0 *)
  0x4e287b5a;       (* arm_AESIMC Q26 Q26 *)
  0x4cdf78e0;       (* arm_LDR Q0 X7 (Postimmediate_Offset (word 0x10)) *)
  0x710008c6;       (* arm_SUBS W6 W6 (rvalue (word 0x2)) *)
  0x4e28583a;       (* arm_AESD Q26 Q1 *)
  0x4e287b5a;       (* arm_AESIMC Q26 Q26 *)
  0x4cdf78e1;       (* arm_LDR Q1 X7 (Postimmediate_Offset (word 0x10)) *)
  0x54ffff2c;       (* arm_BGT (word 0x1fffe4) *)
  0x4e28581a;       (* arm_AESD Q26 Q0 *)
  0x4e287b5a;       (* arm_AESIMC Q26 Q26 *)
  0x4c4078e0;       (* arm_LDR Q0 X7 No_Offset *)
  0x4e28583a;       (* arm_AESD Q26 Q1 *)
  0x6e201f5a;       (* arm_EOR_VEC Q26 Q26 Q0 0x80 *)
  0x6e261f5a;       (* arm_EOR_VEC Q26 Q26 Q6 0x80 *)
  0x4c00703a;       (* arm_STR Q26 X1 No_Offset *)
  0x6d4227e8;       (* arm_LDP D8 D9 SP (Immediate_Offset (iword (&0x20))) *)
  0x6d432fea;       (* arm_LDP D10 D11 SP (Immediate_Offset (iword (&0x30))) *)
  0x6d4437ec;       (* arm_LDP D12 D13 SP (Immediate_Offset (iword (&0x40))) *)
  0x6d453fee;       (* arm_LDP D14 D15 SP (Immediate_Offset (iword (&0x50))) *)
  0xa94053f3;       (* arm_LDP X19 X20 SP (Immediate_Offset (iword (&0x0))) *)
  0xa9415bf5;       (* arm_LDP X21 X22 SP (Immediate_Offset (iword (&0x10))) *)
  0x910183ff;       (* arm_ADD SP SP (rvalue (word 0x60)) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let AES_XTS_DECRYPT_EXEC = ARM_MK_EXEC_RULE aes_xts_decrypt_mc;;

(** Definitions **)

let set_key_schedule = new_definition
  `set_key_schedule (s:armstate) (key_ptr:int64) (k0:int128)
     (k1:int128) (k2:int128) (k3:int128) (k4:int128) (k5:int128)
     (k6:int128) (k7:int128) (k8:int128) (k9:int128) (ka:int128)
     (kb:int128) (kc:int128) (kd:int128) (ke:int128) : bool =
     (read(memory :> bytes128 key_ptr) s = k0 /\
      read(memory :> bytes128 (word_add key_ptr (word 16))) s = k1 /\
      read(memory :> bytes128 (word_add key_ptr (word 32))) s = k2 /\
      read(memory :> bytes128 (word_add key_ptr (word 48))) s = k3 /\
      read(memory :> bytes128 (word_add key_ptr (word 64))) s = k4 /\
      read(memory :> bytes128 (word_add key_ptr (word 80))) s = k5 /\
      read(memory :> bytes128 (word_add key_ptr (word 96))) s = k6 /\
      read(memory :> bytes128 (word_add key_ptr (word 112))) s = k7 /\
      read(memory :> bytes128 (word_add key_ptr (word 128))) s = k8 /\
      read(memory :> bytes128 (word_add key_ptr (word 144))) s = k9 /\
      read(memory :> bytes128 (word_add key_ptr (word 160))) s = ka /\
      read(memory :> bytes128 (word_add key_ptr (word 176))) s = kb /\
      read(memory :> bytes128 (word_add key_ptr (word 192))) s = kc /\
      read(memory :> bytes128 (word_add key_ptr (word 208))) s = kd /\
      read(memory :> bytes128 (word_add key_ptr (word 224))) s = ke /\
      read(memory :> bytes32 (word_add key_ptr (word 240))) s = word 14)`;;

(** Tactics **)

let AESENC_TAC =
  REWRITE_TAC [aes256_encrypt] THEN
  REWRITE_TAC EL_15_128_CLAUSES THEN
  REWRITE_TAC [aes256_encrypt_round] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC [aese;aesmc] THEN
  GEN_REWRITE_TAC LAND_CONV [WORD_XOR_SYM] THEN
  REFL_TAC;;

let AESDEC_TAC =
  REWRITE_TAC [aes256_decrypt] THEN
  REWRITE_TAC EL_15_128_CLAUSES THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC [aes256_decrypt_round] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC [aesd;aesimc] THEN
  (* NOTE: BITBLAST_TAC couldn't handle this goal *)
  GEN_REWRITE_TAC LAND_CONV [WORD_XOR_SYM] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [WORD_XOR_SYM] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REPLICATE_TAC 13 (AP_THM_TAC THEN (REPLICATE_TAC 4 AP_TERM_TAC)) THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [WORD_XOR_SYM] THEN REFL_TAC;;

let TWEAK_UPDATE_CONV =
  let ADD_SUC_1 = ARITH_RULE `!n. n + 1 = SUC(n)` in
  let ADD_SUC_2 = ARITH_RULE `!n. n + 2 = SUC(n + 1)` in
  let ADD_SUC_3 = ARITH_RULE `!n. n + 3 = SUC(n + 2)` in
  let ADD_SUC_4 = ARITH_RULE `!n. n + 4 = SUC(n + 3)` in
  let ADD_SUC_5 = ARITH_RULE `!n. n + 5 = SUC(n + 4)` in
  let ADD_SUC_6 = ARITH_RULE `!n. n + 6 = SUC(n + 5)` in
  let ADD_SUC_7 = ARITH_RULE `!n. n + 7 = SUC(n + 6)` in
  let ADD_SUC_8 = ARITH_RULE `!n. n + 8 = SUC(n + 7)` in
  let ADD_SUC_9 = ARITH_RULE `!n. n + 9 = SUC(n + 8)` in
  NUM_REDUCE_CONV THENC
  RATOR_CONV (LAND_CONV (num_CONV ORELSEC
    FIRST_CONV
    [ CHANGED_CONV (ONCE_REWRITE_CONV [ADD_SUC_1]);
      CHANGED_CONV (ONCE_REWRITE_CONV [ADD_SUC_2]);
      CHANGED_CONV (ONCE_REWRITE_CONV [ADD_SUC_3]);
      CHANGED_CONV (ONCE_REWRITE_CONV [ADD_SUC_4]);
      CHANGED_CONV (ONCE_REWRITE_CONV [ADD_SUC_5]);
      CHANGED_CONV (ONCE_REWRITE_CONV [ADD_SUC_6]);
      CHANGED_CONV (ONCE_REWRITE_CONV [ADD_SUC_7]);
      CHANGED_CONV (ONCE_REWRITE_CONV [ADD_SUC_8]);
      CHANGED_CONV (ONCE_REWRITE_CONV [ADD_SUC_9]);])) THENC
  REWRITE_CONV [CONJUNCT2 calculate_tweak] THENC
  GF_128_MULT_BY_PRIMITIVE_CONV;;

let TWEAK_TAC reg ind indm1 =
  let lower_term = subst [ind,`ind:num`] `(word_zx:int128->int64) (calculate_tweak ind iv key2)` in
  let upper_term = subst [ind,`ind:num`] `(word_subword:int128->num#num->int64) (calculate_tweak ind iv key2) (64,64)` in
  let full_term = subst [ind,`ind:num`] `calculate_tweak ind iv key2` in
  let full_lemma = subst [reg,`reg:(armstate,int128)component`] `read (reg:(armstate,int128)component) (s:armstate) = a ==> !a'. a = a' ==> read reg s = a'` in
  let abbrev_term = subst [indm1,`indm1:num`] `tweak_pre:int128 = (calculate_tweak indm1 iv key2)` in
  FIRST_X_ASSUM(MP_TAC o SPEC lower_term
    o  MATCH_MP (MESON[] `read X9 s = a ==> !a'. a = a' ==> read X9 s = a'`)) THEN
    ANTS_TAC THENL [CONV_TAC (RAND_CONV (RAND_CONV TWEAK_UPDATE_CONV)) THEN
      ABBREV_TAC abbrev_term THEN
      BITBLAST_TAC; DISCH_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC upper_term
    o  MATCH_MP (MESON[] `read X10 s = a ==> !a'. a = a' ==> read X10 s = a'`)) THEN
    ANTS_TAC THENL [CONV_TAC (RAND_CONV (RATOR_CONV (RAND_CONV TWEAK_UPDATE_CONV))) THEN
      ABBREV_TAC abbrev_term THEN
      BITBLAST_TAC; DISCH_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC full_term
    o  MATCH_MP (MESON[] full_lemma)) THEN
    ANTS_TAC THENL [CONV_TAC (RAND_CONV TWEAK_UPDATE_CONV) THEN
      ABBREV_TAC abbrev_term THEN
      BITBLAST_TAC; DISCH_TAC];;

let XTSDEC_TAC reg ind ind_tweak =
  let tm = subst [ind, `ind:num`; ind_tweak, `ind_tweak:num`]
            `aes256_xts_decrypt_round (bytes_to_int128 (SUB_LIST (ind,0x10) (ct:byte list)))
              (calculate_tweak ind_tweak iv key2) key1` in
  let lemma = subst [reg, `reg:(armstate,int128)component`]
            `read (reg:(armstate,int128)component) (s:armstate) = a ==> !a'. a = a' ==> read reg s = a'` in
  let _ = print_term tm in
  let _ = print_term lemma in
  FIRST_X_ASSUM(MP_TAC o SPEC tm o  MATCH_MP (MESON[] lemma)) THEN
      ANTS_TAC THENL
      [ EXPAND_TAC "key1" THEN
        CONV_TAC (RAND_CONV (
          REWRITE_CONV [aes256_xts_decrypt_round] THENC
          DEPTH_CONV let_CONV)) THEN
        AESDEC_TAC; DISCH_TAC ];;

(** Proof **)

let AES_XTS_DECRYPT_1BLOCK_CORRECT = prove(
  `!ct_ptr pt_ptr key0_ptr key1_ptr iv_ptr ib iv
    (k00:int128) k01 k02 k03 k04 k05 k06 k07 k08 k09 k0a k0b k0c k0d k0e
    k10 k11 k12 k13 k14 k15 k16 k17 k18 k19 k1a k1b k1c k1d k1e
    pc.
    nonoverlapping (word pc, LENGTH aes_xts_decrypt_mc) (pt_ptr, 16)
    ==> ensures arm
    (\s. aligned_bytes_loaded s (word pc) aes_xts_decrypt_mc /\
         read PC s = word (pc + 0x1c) /\
         C_ARGUMENTS [ct_ptr; pt_ptr; word 16; key0_ptr; key1_ptr; iv_ptr] s /\
         read(memory :> bytes128 ct_ptr) s = ib /\
         read(memory :> bytes128 iv_ptr) s = iv /\
         set_key_schedule s key0_ptr k00 k01 k02 k03 k04 k05 k06 k07 k08 k09 k0a k0b k0c k0d k0e /\
         set_key_schedule s key1_ptr k10 k11 k12 k13 k14 k15 k16 k17 k18 k19 k1a k1b k1c k1d k1e)
    (\s. read PC s = word (pc + 0xa10) /\
         read(memory :> bytes128 pt_ptr) s =
           aes256_xts_decrypt_1block ib iv
           [k00; k01; k02; k03; k04; k05; k06; k07; k08; k09; k0a; k0b; k0c; k0d; k0e]
           [k10; k11; k12; k13; k14; k15; k16; k17; k18; k19; k1a; k1b; k1c; k1d; k1e]
         )
    (MAYCHANGE [PC] ,, MAYCHANGE [events] ,,
     MAYCHANGE [X21;X2;X6;X4;X9;X10;X19;X22;X11;X7;X0;X1;X8] ,,
     MAYCHANGE [Q6;Q1;Q0;Q8;Q16;Q17;Q12;Q13;Q14;Q15;Q4;Q5;Q18;Q19;Q20;Q21;Q22;Q23;Q7;Q29;Q24] ,,
     MAYCHANGE SOME_FLAGS,, MAYCHANGE [memory :> bytes128 pt_ptr])
    `,
  REWRITE_TAC [(REWRITE_CONV [aes_xts_decrypt_mc] THENC LENGTH_CONV) `LENGTH aes_xts_decrypt_mc`] THEN
  REWRITE_TAC[set_key_schedule; C_ARGUMENTS; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  REPEAT STRIP_TAC THEN

  (* Start symbolic simulation*)
  ENSURES_INIT_TAC "s0" THEN
  (* Simulate until the first tweak and verify the first tweak equiv the spec *)
  ARM_ACCSTEPS_TAC AES_XTS_DECRYPT_EXEC [] (1--69) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC
    `(aes256_encrypt iv [k10; k11; k12; k13; k14; k15; k16; k17; k18; k19; k1a; k1b; k1c; k1d; k1e]):int128`
    o  MATCH_MP (MESON[] `read Q6 s = a ==> !a'. a = a' ==> read Q6 s = a'`)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN AESENC_TAC; DISCH_TAC] THEN

  (* Simulating until finish decrypting one block *)
  ARM_ACCSTEPS_TAC AES_XTS_DECRYPT_EXEC [] (70--126) THEN
  FIRST_X_ASSUM(MP_TAC o
    SPEC `(aes256_xts_decrypt_1block ib iv
       [k00; k01; k02; k03; k04; k05; k06; k07; k08; k09; k0a; k0b; k0c; k0d; k0e]
       [k10; k11; k12; k13; k14; k15; k16; k17; k18; k19; k1a; k1b; k1c; k1d; k1e]):int128`
    o  MATCH_MP (MESON[] `read Q0 s = a ==> !a'. a = a' ==> read Q0 s = a'`)) THEN
  ANTS_TAC THENL [
    REWRITE_TAC [aes256_xts_decrypt_1block] THEN
    REWRITE_TAC [xts_init_tweak] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    REWRITE_TAC [aes256_xts_decrypt_round] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    AESDEC_TAC; DISCH_TAC] THEN

    (* Simulate to the end *)
    ARM_ACCSTEPS_TAC AES_XTS_DECRYPT_EXEC [] (127--137) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC []
);;


(*******************************************)
(* Full proof *)

(* Taken from Amanda's code at https://github.com/amanda-zx/s2n-bignum/blob/ed25519/arm/sha512/utils.ml *)

let byte_list_at = define
  `byte_list_at (m : byte list) (m_p : int64) s =
    ! i. i < LENGTH m ==> read (memory :> bytes8(word_add m_p (word i))) s = EL i m`;;

let tail_len_lt_16_lemma = prove(
  `!tail_len:int64.
    word_and len (word 0xf) = tail_len ==> val tail_len < 16`,
  BITBLAST_TAC
);;

let num_blocks_ge_80_lemma = prove(
  `!num_blocks:int64.
    word_and len (word 0xfffffffffffffff0) = num_blocks /\ val len >= 0x50
    ==> val num_blocks >= 0x50`,
  BITBLAST_TAC
);;

let crock_lemma = prove(
  `!a:num b:num. a >= b /\ b > 0 ==> ~(a DIV b = 0)`,
  REPEAT GEN_TAC THEN
  MP_TAC (SPECL [`a:num`; `b:num`] DIV_EQ_0) THEN
  ARITH_TAC
);;

let word_split_lemma = prove(
  `!len:int64. len = word_add (word_and len (word 0xf))
                              (word_and len (word 0xfffffffffffffff0))`,
  BITBLAST_TAC);;

let blt_lemma = prove(
  `!len:int64 x:num.
    val len >= x /\ val len < 2 EXP 63
    ==> (ival (word_sub len (word x)) < &0 <=> ~(ival len - &x = ival (word_sub len (word x))))`,
  REPEAT STRIP_TAC THEN
  CHEAT_TAC);;

let UDIV_OPT_LEMMA = prove(
  `!n:int64. val n < 2 EXP 64 ==>
    word_ushr
      ((word ((val (word_and n (word 0xfffffffffffffff0)) * 0xcccccccccccccccd) DIV 0x2 EXP 0x40)):int64)
      0x6 = word ((val n) DIV 0x50)`,
  REPEAT STRIP_TAC THEN
  CHEAT_TAC);;

let READ_CT_LEMMA = prove(
  `!ct_ptr s ct i.
    (forall j.
          j < LENGTH ct
          ==> read (memory :> bytes8 (word_add ct_ptr (word j))) s = EL j ct)
          /\ ~(LENGTH ct < 0x50)
          /\ i < LENGTH ct DIV 0x50  ==>
    read (memory :> bytes128 (word_add ct_ptr (word_mul (word 0x50) (word i)))) s0 =
      bytes_to_int128 (SUB_LIST (i * 80, 16) ct) /\
    read (memory :> bytes128 (word_add (word_add ct_ptr (word_mul (word 0x50) (word i))) (word 0x10))) s =
      bytes_to_int128 (SUB_LIST (i * 80 + 16, 16) ct) /\
    read (memory :> bytes128 (word_add (word_add ct_ptr (word_mul (word 0x50) (word i))) (word 0x20))) s =
      bytes_to_int128 (SUB_LIST (i * 80 + 32, 16) ct) /\
    read (memory :> bytes128 (word_add (word_add ct_ptr (word_mul (word 0x50) (word i))) (word 0x30))) s =
      bytes_to_int128 (SUB_LIST (i * 80 + 48, 16) ct) /\
    read (memory :> bytes128 (word_add (word_add ct_ptr (word_mul (word 0x50) (word i))) (word 0x40))) s =
      bytes_to_int128 (SUB_LIST (i * 80 + 64, 16) ct)
    `,
  CHEAT_TAC
);;

let READ_CT_TAIL4_LEMMA = prove(
  `!ct_ptr s ct len (num_blocks:int64) (num_5blocks_adjusted:int64).
    (forall j.
          j < LENGTH ct
          ==> read (memory :> bytes8 (word_add ct_ptr (word j))) s = EL j ct)
          /\ ~(LENGTH ct < 0x50)
          /\ val len = LENGTH ct
          /\ word_and len (word 0xfffffffffffffff0) = num_blocks
          /\ val
      (word_sub
       (word_sub (num_blocks_adjusted:int64)
       (word_mul (word 0x50) num_5blocks_adjusted))
      (word 0x40)) =
      0x0
    ==>
    read (memory :> bytes128 (word_add
      (word_add ct_ptr (word_mul (word 0x50) num_5blocks_adjusted))
      (word 0x30))) s =
      bytes_to_int128 (SUB_LIST (val num_5blocks_adjusted * 16 + 0x30, 16) ct) /\
    read (memory :> bytes128 (word_add
      (word_add ct_ptr (word_mul (word 0x50) num_5blocks_adjusted))
      (word 0x20))) s =
      bytes_to_int128 (SUB_LIST (val num_5blocks_adjusted * 16 + 0x20, 16) ct) /\
    read (memory :> bytes128 (word_add
      (word_add ct_ptr (word_mul (word 0x50) num_5blocks_adjusted))
      (word 0x10))) s =
      bytes_to_int128 (SUB_LIST (val num_5blocks_adjusted * 16 + 0x10, 16) ct) /\
    read (memory :> bytes128
      (word_add ct_ptr (word_mul (word 0x50) num_5blocks_adjusted))) s =
      bytes_to_int128 (SUB_LIST (val num_5blocks_adjusted * 16, 16) ct)
    `,
  CHEAT_TAC
);;

let READ_CT_TAIL3_LEMMA = prove(
  `!ct_ptr s ct len (num_blocks:int64) (num_5blocks_adjusted:int64).
    (forall j.
          j < LENGTH ct
          ==> read (memory :> bytes8 (word_add ct_ptr (word j))) s = EL j ct)
          /\ ~(LENGTH ct < 0x50)
          /\ val len = LENGTH ct
          /\ word_and len (word 0xfffffffffffffff0) = num_blocks
          /\ val
      (word_sub
       (word_sub (num_blocks_adjusted:int64)
       (word_mul (word 0x50) num_5blocks_adjusted))
      (word 0x30)) =
      0x0
    ==>
    read (memory :> bytes128 (word_add
      (word_add ct_ptr (word_mul (word 0x50) num_5blocks_adjusted))
      (word 0x20))) s =
      bytes_to_int128 (SUB_LIST (val num_5blocks_adjusted * 16 + 0x20, 16) ct) /\
    read (memory :> bytes128 (word_add
      (word_add ct_ptr (word_mul (word 0x50) num_5blocks_adjusted))
      (word 0x10))) s =
      bytes_to_int128 (SUB_LIST (val num_5blocks_adjusted * 16 + 0x10, 16) ct) /\
    read (memory :> bytes128
      (word_add ct_ptr (word_mul (word 0x50) num_5blocks_adjusted))) s =
      bytes_to_int128 (SUB_LIST (val num_5blocks_adjusted * 16, 16) ct)
    `,
  CHEAT_TAC
);;

let READ_CT_TAIL2_LEMMA = prove(
  `!ct_ptr s ct len (num_blocks:int64) (num_5blocks_adjusted:int64).
    (forall j.
          j < LENGTH ct
          ==> read (memory :> bytes8 (word_add ct_ptr (word j))) s = EL j ct)
          /\ ~(LENGTH ct < 0x50)
          /\ val len = LENGTH ct
          /\ word_and len (word 0xfffffffffffffff0) = num_blocks
          /\ val
      (word_sub
       (word_sub num_blocks_adjusted
       (word_mul (word 0x50) num_5blocks_adjusted))
      (word 0x20)) =
      0x0
    ==>
    read (memory :> bytes128 (word_add
      (word_add ct_ptr (word_mul (word 0x50) num_5blocks_adjusted))
      (word 0x10))) s =
      bytes_to_int128 (SUB_LIST (val num_5blocks_adjusted * 16 + 0x10, 16) ct) /\
    read (memory :> bytes128
      (word_add ct_ptr (word_mul (word 0x50) num_5blocks_adjusted))) s =
      bytes_to_int128 (SUB_LIST (val num_5blocks_adjusted * 16, 16) ct)
    `,
  CHEAT_TAC
);;

let READ_CT_TAIL1_LEMMA = prove(
  `!ct_ptr s ct len (num_blocks:int64) (num_5blocks_adjusted:int64).
    (forall j.
          j < LENGTH ct
          ==> read (memory :> bytes8 (word_add ct_ptr (word j))) s = EL j ct)
          /\ ~(LENGTH ct < 0x50)
          /\ val len = LENGTH ct
          /\ word_and len (word 0xfffffffffffffff0) = num_blocks
          /\ val
      (word_sub
       (word_sub num_blocks_adjusted
       (word_mul (word 0x50) num_5blocks_adjusted))
      (word 0x10)) =
      0x0
    ==>
    read (memory :> bytes128
      (word_add ct_ptr (word_mul (word 0x50) num_5blocks_adjusted))) s =
      bytes_to_int128 (SUB_LIST (val num_5blocks_adjusted * 16, 16) ct)
    `,
  CHEAT_TAC
);;

let AES_XTS_DECRYPT_CORRECT = prove(
  `!ct_ptr pt_ptr ct pt_init key1_ptr key2_ptr iv_ptr iv len
    k00 k01 k02 k03 k04 k05 k06 k07 k08 k09 k0a k0b k0c k0d k0e
    k10 k11 k12 k13 k14 k15 k16 k17 k18 k19 k1a k1b k1c k1d k1e
    pc.
    nonoverlapping (word pc, LENGTH aes_xts_decrypt_mc) (pt_ptr, val len)
    /\ val len >= 16 /\ val len <= 2 EXP 24 /\ val len = LENGTH ct
    ==> ensures arm
    (\s. aligned_bytes_loaded s (word pc) aes_xts_decrypt_mc /\
         read PC s = word (pc + 0x1c) /\
         C_ARGUMENTS [ct_ptr; pt_ptr; len; key1_ptr; key2_ptr; iv_ptr] s /\
         byte_list_at ct ct_ptr s /\
         byte_list_at pt_init pt_ptr s /\
         read(memory :> bytes128 iv_ptr) s = iv /\
         set_key_schedule s key1_ptr k00 k01 k02 k03 k04 k05 k06 k07 k08 k09 k0a k0b k0c k0d k0e /\
         set_key_schedule s key2_ptr k10 k11 k12 k13 k14 k15 k16 k17 k18 k19 k1a k1b k1c k1d k1e)
    (\s. read PC s = word (pc + 0xb00) /\
         byte_list_at (aes256_xts_decrypt ct (val len) iv
              [k00; k01; k02; k03; k04; k05; k06; k07; k08; k09; k0a; k0b; k0c; k0d; k0e]
              [k10; k11; k12; k13; k14; k15; k16; k17; k18; k19; k1a; k1b; k1c; k1d; k1e]
              pt_init) pt_ptr s
         )
    (MAYCHANGE [PC] ,, MAYCHANGE [events] ,,
     MAYCHANGE [X21;X2;X6;X4;X9;X10;X19;X22;X11;X7;X0;X1;X8] ,,
     MAYCHANGE [Q6;Q1;Q0;Q8;Q9;Q10;Q11;Q16;Q17;Q12;Q13;Q14;Q15;
                Q4;Q5;Q18;Q19;Q20;Q21;Q22;Q23;Q7;Q29;Q24;Q25;Q26] ,,
     MAYCHANGE SOME_FLAGS,, MAYCHANGE [memory :> bytes(pt_ptr, val len)])
    `,
    REWRITE_TAC [(REWRITE_CONV [aes_xts_decrypt_mc] THENC LENGTH_CONV) `LENGTH aes_xts_decrypt_mc`] THEN
    REWRITE_TAC[set_key_schedule; C_ARGUMENTS; SOME_FLAGS; NONOVERLAPPING_CLAUSES; byte_list_at] THEN
    REPEAT STRIP_TAC THEN

    (* Break len into full blocks and tail *)
    SUBGOAL_THEN `len:int64 = word_add (word_and len (word 0xf))
      (word_and len (word 0xfffffffffffffff0))` ASSUME_TAC THENL
    [REWRITE_TAC[word_split_lemma]; ALL_TAC] THEN
    ABBREV_TAC `num_blocks:int64 = word_and len (word 0xfffffffffffffff0)` THEN
    ABBREV_TAC `tail_len:int64 = word_and len (word 0xf)` THEN
    ABBREV_TAC `key1:int128 list = [k00; k01; k02; k03; k04; k05; k06; k07; k08; k09; k0a; k0b; k0c; k0d; k0e]` THEN
    ABBREV_TAC `key2:int128 list = [k10; k11; k12; k13; k14; k15; k16; k17; k18; k19; k1a; k1b; k1c; k1d; k1e]` THEN

    (* Case splits on length:
      len < 16 -- error case
      len < 32 -- one block, or one block and a tail
      len < 48 -- two blocks, or two blocks and a tail
      len < 64 -- three blocks, or three blocks and a tail
      len < 80 -- four blocks, or four blocks and a tail
      len < 96 -- five blocks, or five blocks and a tail
      len >= 96 -- six blocks and up

      Note: for decrypt, because of cipherstealing, there needs to be one extra
      block at the end together with the tail to be processed for cipherstealing
     *)
    ASM_CASES_TAC `val (len:int64) < 96` THENL [CHEAT_TAC; ALL_TAC] THEN

    ABBREV_TAC `num_blocks_adjusted = if val (tail_len:int64) = 0
          then num_blocks else word_sub (num_blocks:int64) (word 0x10)` THEN
    ABBREV_TAC `num_5blocks_adjusted = (word (val (num_blocks_adjusted:int64) DIV 0x50)):int64` THEN

    (* Verify properties of the program until the beginning of the loop.
       The properties include the invariant, and a bunch of other initial setup.
     *)
    ENSURES_SEQUENCE_TAC `pc + 0x170`
    `\s.
        read X0 s = ct_ptr /\
        read X1 s = pt_ptr /\
        read X2 s = num_blocks_adjusted /\
        read X3 s = key1_ptr /\
        read X21 s = tail_len /\
        read X8 s = num_5blocks_adjusted /\
        read Q6 s = calculate_tweak 0 iv key2 /\
        read Q8 s = calculate_tweak 1 iv key2 /\
        read Q9 s = calculate_tweak 2 iv key2 /\
        read Q10 s = calculate_tweak 3 iv key2 /\
        read Q11 s = calculate_tweak 4 iv key2 /\
        read X19 s = word 0x87 /\
        read X10 s = word_subword (calculate_tweak 4 iv key2) (64,64) /\
        read X9 s = word_zx (calculate_tweak 4 iv key2) /\
        read Q16 s = k00 /\ read Q17 s = k01 /\ read Q12 s = k02 /\ read Q13 s = k03 /\
        read Q14 s = k04 /\ read Q15 s = k05 /\ read Q4 s = k06 /\ read Q5 s = k07 /\
        read Q18 s = k08 /\ read Q19 s = k09 /\ read Q20 s = k0a /\ read Q21 s = k0b /\
        read Q22 s = k0c /\ read Q23 s = k0d /\ read Q7 s = k0e /\
        byte_list_at ct ct_ptr s /\
        byte_list_at (aes256_xts_decrypt ct 0 iv key1 key2 pt_init) pt_ptr s /\
        set_key_schedule s key1_ptr k00 k01 k02 k03 k04 k05 k06 k07 k08 k09 k0a k0b k0c k0d k0e` THEN
        CONJ_TAC THENL
        [
          (* ===> Symbolic Simulation: Start symbolic simulation*)
          ENSURES_INIT_TAC "s0" THEN
          ARM_ACCSTEPS_TAC AES_XTS_DECRYPT_EXEC [] (1--2) THEN
          (* Discharge if condition *)
          SUBGOAL_THEN
            `ival (word_sub (word_add (tail_len:int64) (num_blocks:int64)) (word 0x10)) < &0x0 <=>
          ~(ival (word_add tail_len num_blocks) - &0x10 =
            ival (word_sub (word_add tail_len num_blocks) (word 0x10)))` ASSUME_TAC THENL
          [ MATCH_MP_TAC blt_lemma THEN CONJ_TAC THENL
            [ UNDISCH_TAC `len:int64 = word_add tail_len num_blocks` THEN
              UNDISCH_TAC `val (len:int64) >= 16` THEN
              WORD_ARITH_TAC;
              UNDISCH_TAC `len:int64 = word_add tail_len num_blocks` THEN
              UNDISCH_TAC `val (len:int64) <= 2 EXP 24` THEN
              WORD_ARITH_TAC];
            ALL_TAC] THEN
          POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN

          (* ===> Symbolic Simulation: Symbolic execution for initialization of tweak *)
          ARM_ACCSTEPS_TAC AES_XTS_DECRYPT_EXEC [] (3--69) THEN
          (* Prove Q6 stores initial tweak *)
          FIRST_X_ASSUM(MP_TAC o SPEC `(calculate_tweak 0 iv key2)`
            o  MATCH_MP (MESON[] `read Q6 s = a ==> !a'. a = a' ==> read Q6 s = a'`)) THEN
          ANTS_TAC THENL
          [REWRITE_TAC[CONJUNCT1 calculate_tweak; xts_init_tweak] THEN
           EXPAND_TAC "key2" THEN AESENC_TAC; DISCH_TAC] THEN

          (* ===> Symbolic Simulation: Symbolic simulating untill next branch *)
          ARM_ACCSTEPS_TAC AES_XTS_DECRYPT_EXEC [] (70--89) THEN
          (* Case split on whether there is a tail *)
          FIRST_X_ASSUM MP_TAC THEN
          COND_CASES_TAC THENL
          [
            (* If there is no tail *)
            DISCH_TAC THEN
            (* Prove x9, x10 stores lower and upper halves and Q8 stores the full tweak *)
            TWEAK_TAC `Q8:(armstate,int128)component` `1:num` `0:num` THEN
            ARM_ACCSTEPS_TAC AES_XTS_DECRYPT_EXEC [] (90--93) THEN
            (* Prove the optimized udiv is basically udiv *)
            SUBGOAL_THEN `word_ushr ((word ((val (word_and (word_add (tail_len:int64) num_blocks)
              (word 0xfffffffffffffff0)) * 0xcccccccccccccccd) DIV 0x2 EXP 0x40)):int64)
              0x6 = word ((val num_blocks) DIV 0x50)` ASSUME_TAC THENL
            [ CHEAT_TAC
             ; ALL_TAC] THEN
            POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN

            (* Eliminate 1 block case *)
            ARM_ACCSTEPS_TAC AES_XTS_DECRYPT_EXEC [] (94--95) THEN
            SUBGOAL_THEN `~(val (word_and (word_add (tail_len:int64) num_blocks) (word 0xfffffffffffffff0)) < 0x20)` ASSUME_TAC THENL
            [CHEAT_TAC; POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))] THEN
            (* Eliminate 2 blocks case *)
            ARM_ACCSTEPS_TAC AES_XTS_DECRYPT_EXEC [] (96--97) THEN
            SUBGOAL_THEN `~(val (word_and (word_add (tail_len:int64) num_blocks) (word 0xfffffffffffffff0)) < 0x30)` ASSUME_TAC THENL
            [CHEAT_TAC; POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))] THEN
            (* Eliminate 3 blocks case and prove Q9 stores tweak 2 *)
            ARM_ACCSTEPS_TAC AES_XTS_DECRYPT_EXEC [] (98--105) THEN
            SUBGOAL_THEN `~(val (word_and (word_add (tail_len:int64) num_blocks) (word 0xfffffffffffffff0)) < 0x40)` ASSUME_TAC THENL
            [CHEAT_TAC; POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))] THEN
            TWEAK_TAC `Q9:(armstate,int128)component` `2:num` `1:num` THEN

            (* Eliminate 4 blocks case and Q10 stores tweak 3 *)
            ARM_ACCSTEPS_TAC AES_XTS_DECRYPT_EXEC [] (106--113) THEN
            SUBGOAL_THEN `~(val (word_and (word_add (tail_len:int64) num_blocks) (word 0xfffffffffffffff0)) < 0x50)` ASSUME_TAC THENL
            [CHEAT_TAC; POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))] THEN
            TWEAK_TAC `Q10:(armstate,int128)component` `3:num` `2:num` THEN

            (* Must have 5 blocks, execute until start of loop. Q11 stores tweak 4 *)
            ARM_ACCSTEPS_TAC AES_XTS_DECRYPT_EXEC [] (114--122) THEN
            TWEAK_TAC `Q11:(armstate,int128)component` `4:num` `3:num` THEN

            ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
            REPEAT CONJ_TAC THENL
            [
              CHEAT_TAC;
              REWRITE_TAC[SYM (ASSUME `len:int64 = word_add tail_len num_blocks`)] THEN
              ASM_REWRITE_TAC[];
              CHEAT_TAC;
              ASM_REWRITE_TAC[byte_list_at];
              CHEAT_TAC;
              ASM_REWRITE_TAC[set_key_schedule]]
            ; ALL_TAC
          ] THEN

          (* If there is a tail *)
          DISCH_TAC THEN
          ARM_ACCSTEPS_TAC AES_XTS_DECRYPT_EXEC [] (90--92) THEN
          (* Discharge if condition *)
          SUBGOAL_THEN
            `ival
            (word_sub
             (word_sub
              (word_and (word_add (tail_len:int64) num_blocks)
              (word 0xfffffffffffffff0))
             (word 0x10))
            (word 0x10)) <
            &0x0 <=>
            ~(ival
              (word_sub
               (word_and (word_add tail_len num_blocks)
               (word 0xfffffffffffffff0))
              (word 0x10)) -
              &0x10 =
              ival
              (word_sub
               (word_sub
                (word_and (word_add tail_len num_blocks)
                (word 0xfffffffffffffff0))
               (word 0x10))
              (word 0x10)))` ASSUME_TAC THENL
          [ CHEAT_TAC;
            ALL_TAC] THEN
          POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN

          (* Prove x9, x10 stores lower and upper halves and Q8 stores the full tweak *)
          TWEAK_TAC `Q8:(armstate,int128)component` `1:num` `0:num` THEN
          ARM_ACCSTEPS_TAC AES_XTS_DECRYPT_EXEC [] (93--96) THEN
          (* Prove the optimized udiv is basically udiv *)
          SUBGOAL_THEN `word_ushr
      (word
      ((val
        (word_sub
         (word_and (word_add (tail_len:int64) num_blocks) (word 0xfffffffffffffff0))
        (word 0x10)) *
        0xcccccccccccccccd) DIV
       0x2 EXP 0x40):int64)
      0x6 = word ((val (word_sub num_blocks (word 1))) DIV 0x50)` ASSUME_TAC THENL
          [ CHEAT_TAC
            ; ALL_TAC] THEN
          POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN

          (* Eliminate 1 block case *)
          ARM_ACCSTEPS_TAC AES_XTS_DECRYPT_EXEC [] (97--98) THEN
          SUBGOAL_THEN `~(val
          (word_sub
           (word_and (word_add (tail_len:int64) num_blocks)
           (word 0xfffffffffffffff0))
          (word 0x10)) <
          0x20)` ASSUME_TAC THENL
          [CHEAT_TAC; POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))] THEN
          (* Eliminate 2 blocks case *)
          ARM_ACCSTEPS_TAC AES_XTS_DECRYPT_EXEC [] (99--100) THEN
          SUBGOAL_THEN `~(val
          (word_sub
           (word_and (word_add (tail_len:int64) num_blocks)
           (word 0xfffffffffffffff0))
          (word 0x10)) <
          0x30)` ASSUME_TAC THENL
          [CHEAT_TAC; POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))] THEN
          (* Eliminate 3 blocks case and prove Q9 stores tweak 2 *)
          ARM_ACCSTEPS_TAC AES_XTS_DECRYPT_EXEC [] (101--108) THEN
          SUBGOAL_THEN `~(val
          (word_sub
           (word_and (word_add (tail_len:int64) num_blocks)
           (word 0xfffffffffffffff0))
          (word 0x10)) <
          0x40)` ASSUME_TAC THENL
          [CHEAT_TAC; POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))] THEN
          TWEAK_TAC `Q9:(armstate,int128)component` `2:num` `1:num` THEN

          (* Eliminate 4 blocks case and Q10 stores tweak 3 *)
          ARM_ACCSTEPS_TAC AES_XTS_DECRYPT_EXEC [] (109--116) THEN
          SUBGOAL_THEN `~(val
          (word_sub
           (word_and (word_add (tail_len:int64) num_blocks)
           (word 0xfffffffffffffff0))
          (word 0x10)) <
          0x50)` ASSUME_TAC THENL
          [CHEAT_TAC; POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))] THEN
          TWEAK_TAC `Q10:(armstate,int128)component` `3:num` `2:num` THEN

          (* Must have 5 blocks, execute until start of loop. Q11 stores tweak 4 *)
          ARM_ACCSTEPS_TAC AES_XTS_DECRYPT_EXEC [] (117--125) THEN
          TWEAK_TAC `Q11:(armstate,int128)component` `4:num` `3:num` THEN

          ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
          REPEAT CONJ_TAC THENL
          [
            CHEAT_TAC;
            REWRITE_TAC[SYM (ASSUME `len:int64 = word_add tail_len num_blocks`)] THEN
            ASM_REWRITE_TAC[];
            CHEAT_TAC;
            ASM_REWRITE_TAC[byte_list_at];
            CHEAT_TAC;
            ASM_REWRITE_TAC[set_key_schedule]]
          ; ALL_TAC
        ] THEN

    (* Prove the rest of the program *)
    (* Setting up the loop invariant *)

    (* Invariant:
      X0 holds ct_ptr + i*0x50
      X1 hols pt_ptr + i*0x50
      X3 holds key1_ptr
      X21 holds tail_len

      X2 holds number of blocks left
      X8 holds number of 5xblocks left
      Q6, Q8, Q9, Q10, Q11 holds the next 5 tweaks
      X10 stores upper half of last tweak
      X9 stores lower half of last tweak
      X19 holds 0x87
      Q16, Q17, Q12, Q13, Q14, Q15, Q4, Q5, Q18, Q19, Q20, Q21, Q22, Q23, Q7 stores the key1
      Memory: ct_ptr points to the input data blocks
      Memory: Up to the new five blocks in output pt_ptr matche the specification
    *)

    ENSURES_WHILE_PAUP_TAC
      `0`
      `val (num_5blocks_adjusted:int64)`
      `pc + 0x170`
      `pc + 0x460`
      `\i s.
        (read X0 s = word_add ct_ptr (word_mul (word 0x50) (word i)) /\
         read X1 s = word_add pt_ptr (word_mul (word 0x50) (word i)) /\
         read X3 s = key1_ptr /\
         read X21 s = tail_len /\
         read X2 s = word_sub num_blocks_adjusted (word_mul (word 0x50) (word i)) /\
         read X8 s = word_sub num_5blocks_adjusted (word i) /\
         read Q6 s = calculate_tweak (i * 5) iv key2 /\
         read Q8 s = calculate_tweak (i * 5 + 1) iv key2 /\
         read Q9 s = calculate_tweak (i * 5 + 2) iv key2 /\
         read Q10 s = calculate_tweak (i * 5 + 3) iv key2 /\
         read Q11 s = calculate_tweak (i * 5 + 4) iv key2 /\
         read X19 s = word 0x87 /\
         read X10 s = word_subword (calculate_tweak (i * 5 + 4) iv key2) (64,64) /\
         read X9 s = word_zx (calculate_tweak (i * 5 + 4) iv key2) /\
         read Q16 s = k00 /\ read Q17 s = k01 /\ read Q12 s = k02 /\ read Q13 s = k03 /\
         read Q14 s = k04 /\ read Q15 s = k05 /\ read Q4 s = k06 /\ read Q5 s = k07 /\
         read Q18 s = k08 /\ read Q19 s = k09 /\ read Q20 s = k0a /\ read Q21 s = k0b /\
         read Q22 s = k0c /\ read Q23 s = k0d /\ read Q7 s = k0e /\
         byte_list_at ct ct_ptr s /\
         byte_list_at (aes256_xts_decrypt ct (i * 5 * 16) iv key1 key2 pt_init) pt_ptr s) /\
        // loop backedge condition
        (read ZF s <=> i = val (num_5blocks_adjusted:int64))` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
    [
      (* Subgoal 1. Bound of loop is not zero *)
      CHEAT_TAC;

      (* Subgoal 2. Invariant holds before entering the loop *)
      REWRITE_TAC[byte_list_at] THEN
      ENSURES_INIT_TAC "s0" THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      REPEAT CONJ_TAC THENL
      [
        WORD_ARITH_TAC; WORD_ARITH_TAC;
        CHEAT_TAC;
        CHEAT_TAC;
        CONV_TAC NUM_REDUCE_CONV;
        CONV_TAC NUM_REDUCE_CONV;
        CONV_TAC NUM_REDUCE_CONV;
        CONV_TAC NUM_REDUCE_CONV;
        CONV_TAC NUM_REDUCE_CONV;
        CONV_TAC NUM_REDUCE_CONV;
        CONV_TAC NUM_REDUCE_CONV;
        CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[byte_list_at]
      ];

      (* Subgoal 3: loop body *)
      REPEAT STRIP_TAC THEN
      (* ===> Symbolic Simulation: Start symbolic simulation*)
      REWRITE_TAC[byte_list_at] THEN
      SUBGOAL_THEN `i < LENGTH (ct:byte list) DIV 0x50` ASSUME_TAC THENL
      [CHEAT_TAC;ALL_TAC] THEN
      SUBGOAL_THEN `~(LENGTH (ct:byte list) < 0x50)` ASSUME_TAC THENL
      [CHEAT_TAC;ALL_TAC] THEN

      GHOST_INTRO_TAC `b0:int128` `read (memory :> bytes128 (word_add pt_ptr (word_mul (word 0x50) (word i))))` THEN
      GHOST_INTRO_TAC `b1:int128` `read (memory :> bytes128 (word_add (word_add pt_ptr (word_mul (word 0x50) (word i))) (word 0x10)))` THEN
      GHOST_INTRO_TAC `b2:int128` `read (memory :> bytes128 (word_add (word_add pt_ptr (word_mul (word 0x50) (word i))) (word 0x20)))` THEN
      GHOST_INTRO_TAC `b3:int128` `read (memory :> bytes128 (word_add (word_add pt_ptr (word_mul (word 0x50) (word i))) (word 0x30)))` THEN
      GHOST_INTRO_TAC `b4:int128` `read (memory :> bytes128 (word_add (word_add pt_ptr (word_mul (word 0x50) (word i))) (word 0x40)))` THEN

      ENSURES_INIT_TAC "s0" THEN
      (* List values for ct_ptr + [0 .. 0x40] *)
      MP_TAC (SPECL [`ct_ptr:int64`; `s0:armstate`; `ct:byte list`; `i:num`] READ_CT_LEMMA) THEN
      ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
      ARM_ACCSTEPS_TAC AES_XTS_DECRYPT_EXEC [] (1--151) THEN
      (* Prove Q0, Q1, Q24, Q25, Q26 stores correct plaintext *)
      (* and prove Q6, Q8, Q9, Q10, Q11 stores correct tweak *)
      XTSDEC_TAC `Q0:(armstate,int128)component` `i * 0x50` `i * 0x5` THEN
      TWEAK_TAC `Q6:(armstate,int128)component` `i * 5 + 5` `i * 5 + 4` THEN

      ARM_ACCSTEPS_TAC AES_XTS_DECRYPT_EXEC [] (152--159) THEN
      XTSDEC_TAC `Q1:(armstate,int128)component` `i * 0x50 + 0x10` `i * 0x5 + 0x1` THEN
      TWEAK_TAC `Q8:(armstate,int128)component` `i * 5 + 6` `i * 5 + 5` THEN

      ARM_ACCSTEPS_TAC AES_XTS_DECRYPT_EXEC [] (160--167) THEN
      XTSDEC_TAC `Q24:(armstate,int128)component` `i * 0x50 + 0x20` `i * 0x5 + 0x2` THEN
      TWEAK_TAC `Q9:(armstate,int128)component` `i * 5 + 7` `i * 5 + 6` THEN

      ARM_ACCSTEPS_TAC AES_XTS_DECRYPT_EXEC [] (168--175) THEN
      XTSDEC_TAC `Q25:(armstate,int128)component` `i * 0x50 + 0x30` `i * 0x5 + 0x3` THEN
      TWEAK_TAC `Q10:(armstate,int128)component` `i * 5 + 8` `i * 5 + 7` THEN

      ARM_ACCSTEPS_TAC AES_XTS_DECRYPT_EXEC [] (176--183) THEN
      XTSDEC_TAC `Q26:(armstate,int128)component` `i * 0x50 + 0x40` `i * 0x5 + 0x4` THEN
      TWEAK_TAC `Q11:(armstate,int128)component` `i * 5 + 9` `i * 5 + 8` THEN

      (* Simulate until end of loop *)
      ARM_ACCSTEPS_TAC AES_XTS_DECRYPT_EXEC [] (184--188) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      REPEAT CONJ_TAC THENL
      [ CHEAT_TAC;
        CHEAT_TAC;
        CHEAT_TAC;
        CHEAT_TAC;
        CHEAT_TAC;
        CHEAT_TAC;
        CHEAT_TAC;
        CHEAT_TAC;
        CHEAT_TAC;
        CHEAT_TAC;
        CHEAT_TAC;
        CHEAT_TAC;
        CHEAT_TAC;
        CHEAT_TAC;
        CHEAT_TAC
      ];


      (* Subgoal 4: prove backedge is taken if i != val num_5blocks_adjusted *)
      REPEAT STRIP_TAC THEN
      REWRITE_TAC[byte_list_at] THEN
      ENSURES_INIT_TAC "s0" THEN
      ARM_ACCSTEPS_TAC AES_XTS_DECRYPT_EXEC [] (1--1) THEN
      SUBGOAL_THEN `~(val (word_sub (num_5blocks_adjusted:int64) (word i)) = 0x0)` ASSUME_TAC THENL
      [CHEAT_TAC; ALL_TAC] THEN
      POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];


      (* Subgoal 5: Prove the invariant implies post-condition
                    Backedge instruction is executed here *)
      REPEAT STRIP_TAC THEN
      REWRITE_TAC[byte_list_at] THEN
      SUBGOAL_THEN `~(LENGTH (ct:byte list) < 0x50)` ASSUME_TAC THENL
      [CHEAT_TAC;ALL_TAC] THEN
      SUBGOAL_THEN `(word (val (num_5blocks_adjusted:int64))):int64 = num_5blocks_adjusted` SUBST_ALL_TAC THENL
      [CHEAT_TAC;ALL_TAC] THEN

      GHOST_INTRO_TAC `bt_0:int128`
        `read (memory :> bytes128 (word_add pt_ptr (word_mul (word 0x50) (num_5blocks_adjusted:int64))))` THEN
      GHOST_INTRO_TAC `bt_1:int128`
        `read (memory :> bytes128 (word_add (word_add pt_ptr (word_mul (word 0x50) (num_5blocks_adjusted:int64))) (word 0x10)))` THEN
      GHOST_INTRO_TAC `bt_2:int128`
        `read (memory :> bytes128 (word_add (word_add (pt_ptr:int64) (word_mul (word 0x50) (num_5blocks_adjusted:int64))) (word 0x20)))` THEN
      GHOST_INTRO_TAC `bt_3:int128`
        `read (memory :> bytes128 (word_add (word_add (pt_ptr:int64) (word_mul (word 0x50) (num_5blocks_adjusted:int64))) (word 0x30)))` THEN

      ENSURES_INIT_TAC "s0" THEN
      ARM_ACCSTEPS_TAC AES_XTS_DECRYPT_EXEC [] (1--3) THEN
      FIRST_X_ASSUM MP_TAC THEN

      COND_CASES_TAC THENL
      [ (* Case: len % 0x50 = 0x40 *)
        DISCH_TAC THEN

        MP_TAC (SPECL [`ct_ptr:int64`; `s3:armstate`; `ct:byte list`;
          `len:int64`; `num_blocks:int64`; `num_5blocks_adjusted:int64`] READ_CT_TAIL4_LEMMA) THEN
        ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN

        ARM_ACCSTEPS_TAC AES_XTS_DECRYPT_EXEC [] (4--125) THEN
        XTSDEC_TAC `Q0:(armstate,int128)component`
          `val (num_5blocks_adjusted:int64) * 0x10` `val (num_5blocks_adjusted:int64) * 0x5` THEN
        XTSDEC_TAC `Q1:(armstate,int128)component`
          `val (num_5blocks_adjusted:int64) * 0x10 + 0x10` `val (num_5blocks_adjusted:int64) * 0x5 + 0x1` THEN
        XTSDEC_TAC `Q24:(armstate,int128)component`
          `val (num_5blocks_adjusted:int64) * 0x10 + 0x20` `val (num_5blocks_adjusted:int64) * 0x5 + 0x2` THEN
        XTSDEC_TAC `Q25:(armstate,int128)component`
          `val (num_5blocks_adjusted:int64) * 0x10 + 0x30` `val (num_5blocks_adjusted:int64) * 0x5 + 0x3` THEN

        ARM_ACCSTEPS_TAC AES_XTS_DECRYPT_EXEC [] (126--133) THEN
        TWEAK_TAC `Q6:(armstate,int128)component` `val (num_5blocks_adjusted:int64) * 0x5 + 0x4` `val (num_5blocks_adjusted:int64) * 0x5 + 0x3` THEN

        (* The following lemmas are for NONSELFMODIFYING_STATE_UPDATE_TAC when store back to pt_ptr *)
        RULE_ASSUM_TAC(REWRITE_RULE
          [WORD_RULE `word_mul (word 0x50) num_5blocks_adjusted:int64 = word(0x50 * val num_5blocks_adjusted)`]) THEN
        SUBGOAL_THEN `80 * val(num_5blocks_adjusted:int64) + 64 <= val(len:int64)`
          ASSUME_TAC THENL [CHEAT_TAC; ALL_TAC] THEN

        ARM_ACCSTEPS_TAC AES_XTS_DECRYPT_EXEC [] (134--138) THEN
        FIRST_X_ASSUM MP_TAC THEN
        COND_CASES_TAC THENL
        [
          DISCH_TAC THEN
          ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
          CHEAT_TAC;
          ALL_TAC
        ] THEN
        (* Cipher stealing branch *)
        CHEAT_TAC;
        ALL_TAC
      ] THEN

      DISCH_TAC THEN
      ARM_ACCSTEPS_TAC AES_XTS_DECRYPT_EXEC [] (4--5) THEN
      FIRST_X_ASSUM MP_TAC THEN
      COND_CASES_TAC THENL
      [ (* Case: len % 0x50 = 0x30 *)
        DISCH_TAC THEN
        MP_TAC (SPECL [`ct_ptr:int64`; `s5:armstate`; `ct:byte list`; `len:int64`; `num_blocks:int64`; `num_5blocks_adjusted:int64`] READ_CT_TAIL3_LEMMA) THEN
        ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN

        ARM_ACCSTEPS_TAC AES_XTS_DECRYPT_EXEC [] (6--97) THEN
        XTSDEC_TAC `Q0:(armstate,int128)component`
          `val (num_5blocks_adjusted:int64) * 0x10` `val (num_5blocks_adjusted:int64) * 0x5` THEN
        XTSDEC_TAC `Q1:(armstate,int128)component`
          `val (num_5blocks_adjusted:int64) * 0x10 + 0x10` `val (num_5blocks_adjusted:int64) * 0x5 + 0x1` THEN
        XTSDEC_TAC `Q24:(armstate,int128)component`
          `val (num_5blocks_adjusted:int64) * 0x10 + 0x20` `val (num_5blocks_adjusted:int64) * 0x5 + 0x2` THEN

        ARM_ACCSTEPS_TAC AES_XTS_DECRYPT_EXEC [] (98--105) THEN
        TWEAK_TAC `Q6:(armstate,int128)component` `val (num_5blocks_adjusted:int64) * 0x5 + 0x3` `val (num_5blocks_adjusted:int64) * 0x5 + 0x2` THEN

        (* The following lemmas are for NONSELFMODIFYING_STATE_UPDATE_TAC when store back to pt_ptr *)
        RULE_ASSUM_TAC(REWRITE_RULE
          [WORD_RULE `word_mul (word 0x50) num_5blocks_adjusted:int64 = word(0x50 * val num_5blocks_adjusted)`]) THEN
        SUBGOAL_THEN `80 * val(num_5blocks_adjusted:int64) + 48 <= val(len:int64)`
          ASSUME_TAC THENL [CHEAT_TAC; ALL_TAC] THEN

        ARM_ACCSTEPS_TAC AES_XTS_DECRYPT_EXEC [] (106--110) THEN
        FIRST_X_ASSUM MP_TAC THEN
        COND_CASES_TAC THENL
        [
          DISCH_TAC THEN
          ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
          CHEAT_TAC;
          ALL_TAC
        ] THEN
        (* Cipher stealing branch *)
        CHEAT_TAC;
        ALL_TAC
      ] THEN

      DISCH_TAC THEN
      ARM_ACCSTEPS_TAC AES_XTS_DECRYPT_EXEC [] (6--7) THEN
      FIRST_X_ASSUM MP_TAC THEN
      COND_CASES_TAC THENL
      [ (* Case: len % 0x50 = 0x20 *)
        DISCH_TAC THEN
        MP_TAC (SPECL [`ct_ptr:int64`; `s7:armstate`; `ct:byte list`; `len:int64`; `num_blocks:int64`; `num_5blocks_adjusted:int64`] READ_CT_TAIL2_LEMMA) THEN
        ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN

        ARM_ACCSTEPS_TAC AES_XTS_DECRYPT_EXEC [] (8--68) THEN
        XTSDEC_TAC `Q0:(armstate,int128)component`
          `val (num_5blocks_adjusted:int64) * 0x10` `val (num_5blocks_adjusted:int64) * 0x5` THEN
        XTSDEC_TAC `Q1:(armstate,int128)component`
          `val (num_5blocks_adjusted:int64) * 0x10 + 0x10` `val (num_5blocks_adjusted:int64) * 0x5 + 0x1` THEN

        (* The following lemmas are for NONSELFMODIFYING_STATE_UPDATE_TAC when store back to pt_ptr *)
        RULE_ASSUM_TAC(REWRITE_RULE
          [WORD_RULE `word_mul (word 0x50) num_5blocks_adjusted:int64 = word(0x50 * val num_5blocks_adjusted)`]) THEN
        SUBGOAL_THEN `80 * val(num_5blocks_adjusted:int64) + 32 <= val(len:int64)`
          ASSUME_TAC THENL [CHEAT_TAC; ALL_TAC] THEN

        ARM_ACCSTEPS_TAC AES_XTS_DECRYPT_EXEC [] (69--77) THEN
        TWEAK_TAC `Q6:(armstate,int128)component` `val (num_5blocks_adjusted:int64) * 0x5 + 0x2` `val (num_5blocks_adjusted:int64) * 0x5 + 0x1` THEN

        ARM_ACCSTEPS_TAC AES_XTS_DECRYPT_EXEC [] (78--80) THEN
        FIRST_X_ASSUM MP_TAC THEN
        COND_CASES_TAC THENL
        [
          DISCH_TAC THEN
          ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
          CHEAT_TAC;
          ALL_TAC
        ] THEN
        (* Cipher stealing branch *)
        CHEAT_TAC;
        ALL_TAC] THEN

      DISCH_TAC THEN
      ARM_ACCSTEPS_TAC AES_XTS_DECRYPT_EXEC [] (8--9) THEN
      FIRST_X_ASSUM MP_TAC THEN
      COND_CASES_TAC THENL
      [ (* Case: len % 0x50 = 0x10 *)
        DISCH_TAC THEN
        MP_TAC (SPECL [`ct_ptr:int64`; `s9:armstate`; `ct:byte list`; `len:int64`; `num_blocks:int64`; `num_5blocks_adjusted:int64`] READ_CT_TAIL1_LEMMA) THEN
        ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN

        ARM_ACCSTEPS_TAC AES_XTS_DECRYPT_EXEC [] (10--40) THEN
        XTSDEC_TAC `Q0:(armstate,int128)component`
          `val (num_5blocks_adjusted:int64) * 0x10` `val (num_5blocks_adjusted:int64) * 0x5` THEN

        (* The following lemmas are for NONSELFMODIFYING_STATE_UPDATE_TAC when store back to pt_ptr *)
        RULE_ASSUM_TAC(REWRITE_RULE
          [WORD_RULE `word_mul (word 0x50) num_5blocks_adjusted:int64 = word(0x50 * val num_5blocks_adjusted)`]) THEN
        SUBGOAL_THEN `80 * val(num_5blocks_adjusted:int64) + 16 <= val(len:int64)`
          ASSUME_TAC THENL [CHEAT_TAC; ALL_TAC] THEN

        ARM_ACCSTEPS_TAC AES_XTS_DECRYPT_EXEC [] (41--49) THEN
        TWEAK_TAC `Q6:(armstate,int128)component` `val (num_5blocks_adjusted:int64) * 0x5 + 0x1` `val (num_5blocks_adjusted:int64) * 0x5` THEN

        ARM_ACCSTEPS_TAC AES_XTS_DECRYPT_EXEC [] (50--52) THEN
        FIRST_X_ASSUM MP_TAC THEN
        COND_CASES_TAC THENL
        [
          DISCH_TAC THEN
          ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
          CHEAT_TAC;
          ALL_TAC
        ] THEN
        (* Cipher stealing branch *)
        CHEAT_TAC;
        ALL_TAC] THEN

      (* Case: len % 0x50 = 0 *)
      DISCH_TAC THEN
      ARM_ACCSTEPS_TAC AES_XTS_DECRYPT_EXEC [] (10--12) THEN
      FIRST_X_ASSUM MP_TAC THEN
      COND_CASES_TAC THENL
      [
        DISCH_TAC THEN
        ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
        CHEAT_TAC;
        ALL_TAC
      ] THEN
      (* Cipher stealing branch *)
      CHEAT_TAC
    ]
);;
