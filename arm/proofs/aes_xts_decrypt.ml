(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)
use_file_raise_failure := true;;

needs "arm/proofs/utils/aes_xts_common.ml";;

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
  0x540059cb;       (* arm_BLT (word 0xb38) *)
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
  0x54000a40;       (* arm_BEQ (word 0x148) *)
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
  0x4e285a1a;       (* arm_AESD Q26 Q16 *)
  0x4e287b5a;       (* arm_AESIMC Q26 Q26 *)
  0x4e285a3a;       (* arm_AESD Q26 Q17 *)
  0x4e287b5a;       (* arm_AESIMC Q26 Q26 *)
  0x4e28599a;       (* arm_AESD Q26 Q12 *)
  0x4e287b5a;       (* arm_AESIMC Q26 Q26 *)
  0x4e2859ba;       (* arm_AESD Q26 Q13 *)
  0x4e287b5a;       (* arm_AESIMC Q26 Q26 *)
  0x4e2859da;       (* arm_AESD Q26 Q14 *)
  0x4e287b5a;       (* arm_AESIMC Q26 Q26 *)
  0x4e2859fa;       (* arm_AESD Q26 Q15 *)
  0x4e287b5a;       (* arm_AESIMC Q26 Q26 *)
  0x4e28589a;       (* arm_AESD Q26 Q4 *)
  0x4e287b5a;       (* arm_AESIMC Q26 Q26 *)
  0x4e2858ba;       (* arm_AESD Q26 Q5 *)
  0x4e287b5a;       (* arm_AESIMC Q26 Q26 *)
  0x4e285a5a;       (* arm_AESD Q26 Q18 *)
  0x4e287b5a;       (* arm_AESIMC Q26 Q26 *)
  0x4e285a7a;       (* arm_AESD Q26 Q19 *)
  0x4e287b5a;       (* arm_AESIMC Q26 Q26 *)
  0x4e285a9a;       (* arm_AESD Q26 Q20 *)
  0x4e287b5a;       (* arm_AESIMC Q26 Q26 *)
  0x4e285aba;       (* arm_AESD Q26 Q21 *)
  0x4e287b5a;       (* arm_AESIMC Q26 Q26 *)
  0x4e285ada;       (* arm_AESD Q26 Q22 *)
  0x4e287b5a;       (* arm_AESIMC Q26 Q26 *)
  0x4e285afa;       (* arm_AESD Q26 Q23 *)
  0x6e271f5a;       (* arm_EOR_VEC Q26 Q26 Q7 0x80 *)
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
  0x4e285a1a;       (* arm_AESD Q26 Q16 *)
  0x4e287b5a;       (* arm_AESIMC Q26 Q26 *)
  0x4e285a3a;       (* arm_AESD Q26 Q17 *)
  0x4e287b5a;       (* arm_AESIMC Q26 Q26 *)
  0x4e28599a;       (* arm_AESD Q26 Q12 *)
  0x4e287b5a;       (* arm_AESIMC Q26 Q26 *)
  0x4e2859ba;       (* arm_AESD Q26 Q13 *)
  0x4e287b5a;       (* arm_AESIMC Q26 Q26 *)
  0x4e2859da;       (* arm_AESD Q26 Q14 *)
  0x4e287b5a;       (* arm_AESIMC Q26 Q26 *)
  0x4e2859fa;       (* arm_AESD Q26 Q15 *)
  0x4e287b5a;       (* arm_AESIMC Q26 Q26 *)
  0x4e28589a;       (* arm_AESD Q26 Q4 *)
  0x4e287b5a;       (* arm_AESIMC Q26 Q26 *)
  0x4e2858ba;       (* arm_AESD Q26 Q5 *)
  0x4e287b5a;       (* arm_AESIMC Q26 Q26 *)
  0x4e285a5a;       (* arm_AESD Q26 Q18 *)
  0x4e287b5a;       (* arm_AESIMC Q26 Q26 *)
  0x4e285a7a;       (* arm_AESD Q26 Q19 *)
  0x4e287b5a;       (* arm_AESIMC Q26 Q26 *)
  0x4e285a9a;       (* arm_AESD Q26 Q20 *)
  0x4e287b5a;       (* arm_AESIMC Q26 Q26 *)
  0x4e285aba;       (* arm_AESD Q26 Q21 *)
  0x4e287b5a;       (* arm_AESIMC Q26 Q26 *)
  0x4e285ada;       (* arm_AESD Q26 Q22 *)
  0x4e287b5a;       (* arm_AESIMC Q26 Q26 *)
  0x4e285afa;       (* arm_AESD Q26 Q23 *)
  0x6e271f5a;       (* arm_EOR_VEC Q26 Q26 Q7 0x80 *)
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

(**********************************************************************)
(**                    Decrypt-specific lemmas                       **)

let LENGTH_OF_AES256_XTS_DECRYPT_REC = prove(
  `!(i:num) (m:num) (C:byte list) (iv:int128) (key1:int128 list) (key2:int128 list).
    LENGTH(aes256_xts_decrypt_rec i m C iv key1 key2) = (if m < i then 0 else (m - i + 1) * 0x10)`,
    REPEAT GEN_TAC THEN
    (* Wellfounded induction with measure (m + 1) - i
       Note that the parentheses are essential because of the precedence of + and - *)
    WF_INDUCT_TAC `(m + 1) - i` THEN
    ONCE_REWRITE_TAC[aes256_xts_decrypt_rec] THEN
    COND_CASES_TAC THENL
    [ SIMP_TAC[LENGTH_EQ_NIL];
      SIMP_TAC[] THEN
      REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
      REWRITE_TAC[LENGTH_APPEND] THEN
      SUBGOAL_THEN `~(m < i) ==> (m + 1) - (i + 1) < (m + 1) - i` ASSUME_TAC THENL
      [ ASM_ARITH_TAC ; ALL_TAC ] THEN
      ASM_SIMP_TAC[] THEN
      REWRITE_TAC[LENGTH_OF_INT128_TO_BYTES] THEN
      COND_CASES_TAC THENL
      [ASM_ARITH_TAC; ASM_ARITH_TAC]]
);;

let LENGTH_OF_FST_OF_CIPHER_STEALING = prove(
  `!(block:byte list) (tail:byte list) (tail_len:num)
    (iv:int128) (i:num) (key1:int128 list) (key2:int128 list).
  LENGTH (FST (cipher_stealing block tail tail_len iv i key1 key2)) = 16`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[cipher_stealing] THEN
  ASM_REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  REWRITE_TAC[LENGTH_OF_INT128_TO_BYTES]
);;

let LENGTH_OF_SND_OF_CIPHER_STEALING = prove(
  `!(block:byte list) (tail:byte list) (tail_len:num)
    (iv:int128) (i:num) (key1:int128 list) (key2:int128 list).
  LENGTH (SND (cipher_stealing block tail tail_len iv i key1 key2)) = MIN tail_len 16`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[cipher_stealing] THEN
  ASM_REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  REWRITE_TAC[LENGTH_SUB_LIST] THEN
  REWRITE_TAC[LENGTH_OF_INT128_TO_BYTES] THEN
  REWRITE_TAC[MIN] THEN
  CONV_TAC NUM_REDUCE_CONV
);;

let LENGTH_OF_AES256_XTS_DECRYPT_TAIL = prove(
  `! (i:num) (tail_len:num) (C:byte list) (iv:int128) (key1:int128 list) (key2:int128 list).
  LENGTH(aes256_xts_decrypt_tail i tail_len C iv key1 key2) = 0x10 + MIN tail_len 16`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[aes256_xts_decrypt_tail] THEN
  COND_CASES_TAC THENL [
    ASM_REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
    REWRITE_TAC[LENGTH_OF_INT128_TO_BYTES] THEN
    REWRITE_TAC[ADD_CLAUSES; MIN] THEN
    CONV_TAC NUM_REDUCE_CONV;

    REWRITE_TAC[LET_DEF; LET_END_DEF; LENGTH_APPEND] THEN
    REWRITE_TAC[LENGTH_OF_FST_OF_CIPHER_STEALING] THEN
    REWRITE_TAC[LENGTH_OF_SND_OF_CIPHER_STEALING]]
);;

let LENGTH_OF_AES256_XTS_DECRYPT_REC_TRIVIAL = prove(
  `!(ct:byte list) (iv:int128) (key1:int128 list) (key2:int128 list).
   LENGTH (aes256_xts_decrypt_rec 0x0 0x0 ct iv key1 key2) = 16`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[LENGTH_OF_AES256_XTS_DECRYPT_REC] THEN
  CONV_TAC NUM_REDUCE_CONV
);;

let LENGTH_OF_AES256_XTS_DECRYPT_TAIL_TRIVIAL = prove(
  `!(ct:byte list) (iv:int128) (key1:int128 list) (key2:int128 list).
  LENGTH(aes256_xts_decrypt_tail 0 0 ct iv key1 key2) = 16`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[LENGTH_OF_AES256_XTS_DECRYPT_TAIL] THEN
  CONV_TAC NUM_REDUCE_CONV
);;

let AES256_XTS_DECRYPT_REC_EQ_TAIL_TRIVIAL = prove(
  `!(ct:byte list) (iv:int128) (key1:int128 list) (key2:int128 list).
   aes256_xts_decrypt_rec 0x0 0x0 ct iv key1 key2 =
   aes256_xts_decrypt_tail 0x0 0x0 ct iv key1 key2`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[aes256_xts_decrypt_rec] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  ONCE_REWRITE_TAC[aes256_xts_decrypt_rec] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[APPEND_NIL] THEN

  REWRITE_TAC[aes256_xts_decrypt_tail] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  CONV_TAC NUM_REDUCE_CONV
);;

let LENGTH_OF_AES256_XTS_DECRYPT_FULL_BLOCKS = prove(
  `! (i:num) (ct:byte list) (iv:int128) (key1:int128 list) (key2:int128 list).
  LENGTH(aes256_xts_decrypt ct (0x10 * i) iv key1 key2) = 0x10 * i`,
  REPEAT STRIP_TAC THEN
  SPEC_TAC (`i:num`, `i:num`) THEN
  INDUCT_TAC THENL
  [
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[aes256_xts_decrypt] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[LENGTH_EQ_NIL];
    ALL_TAC] THEN

  REWRITE_TAC[ADD1; LEFT_ADD_DISTRIB] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[aes256_xts_decrypt] THEN

  ASM_CASES_TAC `i = 0` THENL
  [ ASM_SIMP_TAC[] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    IMP_REWRITE_TAC[LET_DEF;LET_END_DEF;SUB_0] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[LENGTH_OF_AES256_XTS_DECRYPT_TAIL_TRIVIAL]
    ; ALL_TAC
  ] THEN

  SUBGOAL_THEN `~(0x10 * i + 0x10 < 0x10)` ASSUME_TAC THENL
  [ ASM_ARITH_TAC; ALL_TAC ] THEN ASM_SIMP_TAC[] THEN
  REWRITE_TAC[ARITH_RULE `0x10 * i + 0x10 = 0x10 * (i + 1)`; MOD_MULT] THEN
  IMP_REWRITE_TAC[LET_DEF; LET_END_DEF;SUB_0;DIV_MULT] THEN
  CONJ_TAC THENL [ALL_TAC; ARITH_TAC] THEN
  SUBGOAL_THEN `~(i + 0x1 < 0x2)` ASSUME_TAC THENL
  [ ASM_ARITH_TAC; ALL_TAC] THEN ASM_SIMP_TAC[] THEN
  REWRITE_TAC[LENGTH_APPEND] THEN
  REWRITE_TAC[LENGTH_OF_AES256_XTS_DECRYPT_REC] THEN
  REWRITE_TAC[LENGTH_OF_AES256_XTS_DECRYPT_TAIL] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ASM_ARITH_TAC
);;

let LENGTH_OF_AES256_XTS_DECRYPT = prove(
  `! (i:num) (tail_len:num) (ct:byte list) (iv:int128) (key1:int128 list) (key2:int128 list).
  ~(tail_len = 0) /\ tail_len < 16 ==>
  LENGTH(aes256_xts_decrypt ct (16 * i + 16 + tail_len) iv key1 key2) = 16 * i + 16 + tail_len`,
  REPEAT STRIP_TAC THEN
  (* Case 1: i = 0 *)
  ASM_CASES_TAC `i = 0` THENL
  [
    ASM_SIMP_TAC[ADD_ASSOC] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[aes256_xts_decrypt] THEN
    SUBGOAL_THEN `~(0x10 + tail_len < 0x10)` ASSUME_TAC THENL
    [ ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(0x10 + tail_len) MOD 0x10 = tail_len` ASSUME_TAC THENL
    [ REWRITE_TAC[ARITH_RULE `0x10 + tail_len = 1 * 16 + tail_len`] THEN
      IMP_REWRITE_TAC[MOD_MULT_ADD; MOD_LT]; ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN
    REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
    SUBGOAL_THEN `((0x10 + tail_len) - tail_len) DIV 0x10 = 1` SUBST1_TAC THENL
    [ ASM_ARITH_TAC; ALL_TAC ] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[LENGTH_OF_AES256_XTS_DECRYPT_TAIL] THEN
    ASM_ARITH_TAC;
    ALL_TAC
  ] THEN

  (* Case 2: i >= 1 *)
  ASM_CASES_TAC `i >= 1` THENL
  [
    REWRITE_TAC[aes256_xts_decrypt] THEN
    SUBGOAL_THEN `(0x10 * i + 0x10 + tail_len) MOD 0x10 = tail_len` SUBST1_TAC THENL
    [ REWRITE_TAC[ADD_ASSOC; ARITH_RULE `0x10 * i + 0x10 = 16 * (i + 1)`] THEN
      IMP_REWRITE_TAC[MOD_MULT_ADD; MOD_LT]; ALL_TAC] THEN
    SUBGOAL_THEN `~(0x10 * i + 0x10 + tail_len < 0x10)` ASSUME_TAC THENL
    [ ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN
    REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
    SUBGOAL_THEN `((0x10 * i + 0x10 + tail_len) - tail_len) DIV 0x10 = i + 1` SUBST1_TAC THENL
    [ REWRITE_TAC[ARITH_RULE `(0x10 * i + 0x10 + tail_len) - tail_len = 16 * (i + 1)`] THEN
      IMP_REWRITE_TAC[DIV_MULT] THEN
      ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `~(i + 1 < 2)` ASSUME_TAC THENL
    [ ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN
    IMP_REWRITE_TAC[ARITH_RULE `(i + 1) - 2 = i - 1`; ADD_SUB] THEN
    REWRITE_TAC[LENGTH_APPEND] THEN
    IMP_REWRITE_TAC[LENGTH_OF_AES256_XTS_DECRYPT_REC] THEN
    IMP_REWRITE_TAC[LENGTH_OF_AES256_XTS_DECRYPT_TAIL] THEN
    ASM_ARITH_TAC;
    ALL_TAC
  ] THEN

  ASM_ARITH_TAC
);;

let AES256_XTS_DECRYPT_TAIL_WHEN_1BLOCK = prove(
  `!(n:num) (ct:byte list) (iv:int128) (key1:int128 list) (key2:int128 list).
   bytes_to_int128
     (aes256_xts_decrypt_tail n 0x0 ct iv key1 key2) =
   aes256_xts_decrypt_round
     (bytes_to_int128 (SUB_LIST (n * 0x10,0x10) ct))
     (calculate_tweak n iv key2) key1`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[aes256_xts_decrypt_tail] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  REWRITE_TAC[BYTES_TO_INT128_OF_INT128_TO_BYTES]
);;

let AES256_XTS_DECRYPT_REC_EQ_TAIL = prove(
  `!(i:num) (k:num) (ct:byte list) (iv:int128) (key1:int128 list) (key2:int128 list).
  k >= i ==>
  aes256_xts_decrypt_rec i (k + 1) ct iv key1 key2 =
  APPEND (aes256_xts_decrypt_rec i k ct iv key1 key2)
         (aes256_xts_decrypt_tail (k + 1) 0x0 ct iv key1 key2)`,
  REPEAT GEN_TAC THEN
  WF_INDUCT_TAC `(k + 1) - i` THEN
  STRIP_TAC THEN
  GEN_REWRITE_TAC (RATOR_CONV o ONCE_DEPTH_CONV) [aes256_xts_decrypt_rec] THEN
  SUBGOAL_THEN `~(k + 0x1 < i)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  SUBGOAL_THEN `(k + 1) - (i + 1) < (k + 1) - i` ASSUME_TAC THENL [ ASM_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM (MP_TAC o SPECL [`k:num`; `i + 1:num`]) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `k >= i + 1` THENL
  [
    ASM_SIMP_TAC[] THEN DISCH_TAC THEN
    REWRITE_TAC[APPEND_ASSOC] THEN
    AP_THM_TAC THEN
    GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [aes256_xts_decrypt_rec] THEN
    SUBGOAL_THEN `~(k < i)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN
    REWRITE_TAC[LET_DEF; LET_END_DEF]; ALL_TAC
  ] THEN
  SUBGOAL_THEN `k:num = i` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[aes256_xts_decrypt_rec] THEN
  REWRITE_TAC[LT_REFL; LET_DEF; LET_END_DEF] THEN
  ONCE_REWRITE_TAC[aes256_xts_decrypt_rec] THEN
  REWRITE_TAC[ARITH_RULE `i < i + 1`; APPEND_NIL] THEN
  AP_TERM_TAC THEN
  REWRITE_TAC[aes256_xts_decrypt_tail; LET_DEF; LET_END_DEF]
);;


let SUB_LIST_OF_AES256_XTS_DECRYPT_FULL_BLOCKS = prove(
  `!(i:num) (ct:byte list) (iv:int128) (key1:int128 list) (key2:int128 list).
    (SUB_LIST (0,16 * i)
      (aes256_xts_decrypt ct (16 * i + 16) iv key1 key2))
    = aes256_xts_decrypt ct (16 * i) iv key1 key2`,
  REPEAT STRIP_TAC THEN

  (* when i = 0, trivial *)
  ASM_CASES_TAC `i = 0` THENL
  [
    ASM_REWRITE_TAC[] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[CONJUNCT1 SUB_LIST; aes256_xts_decrypt] THEN
    CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC
  ] THEN

  (* when i = 1, using aes256_xts_decrypt_tail *)
  ASM_CASES_TAC `i = 1` THENL
  [
    ASM_REWRITE_TAC[] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[aes256_xts_decrypt] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    MP_TAC (SPECL [`ct:byte list`; `iv:int128`; `key1: int128 list`; `key2: int128 list`]
      LENGTH_OF_AES256_XTS_DECRYPT_REC_TRIVIAL) THEN
    DISCH_TAC THEN
    IMP_REWRITE_TAC[SUB_LIST_APPEND_LEFT] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    IMP_REWRITE_TAC[SUB_LIST_LENGTH_IMPLIES] THEN
    REWRITE_TAC[AES256_XTS_DECRYPT_REC_EQ_TAIL_TRIVIAL];
    ALL_TAC
  ] THEN

  (* when i >= 2, using aes256_xts_decrypt_rec *)
  REWRITE_TAC[aes256_xts_decrypt] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN `~(0x10 * i < 0x10)` ASSUME_TAC THENL
  [ ASM_ARITH_TAC ; ALL_TAC] THEN
  SUBGOAL_THEN `~(0x10 * i + 0x10 < 0x10)` ASSUME_TAC THENL
  [ ASM_ARITH_TAC ; ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN
  REWRITE_TAC[ARITH_RULE `16 * i + 16 = 16 * (i + 1)`; MOD_MULT] THEN
  IMP_REWRITE_TAC[LET_DEF;LET_END_DEF;SUB_0;DIV_MULT] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN `~(i < 0x2)` ASSUME_TAC THENL
  [ ASM_ARITH_TAC ; ALL_TAC] THEN
  SUBGOAL_THEN `~(i + 1 < 0x2)` ASSUME_TAC THENL
  [ ASM_ARITH_TAC ; ALL_TAC] THEN
  ASM_SIMP_TAC[ARITH_RULE `(i + 0x1) - 0x2 = i - 1`; ADD_SUB] THEN
  SUBGOAL_THEN `LENGTH (aes256_xts_decrypt_rec 0x0 (i - 0x1) ct iv key1 key2) = 16 * i` ASSUME_TAC THENL
  [ REWRITE_TAC[LENGTH_OF_AES256_XTS_DECRYPT_REC] THEN
    ASM_ARITH_TAC; ALL_TAC] THEN
  IMP_REWRITE_TAC[SUB_LIST_APPEND_LEFT; SUB_LIST_LENGTH_IMPLIES] THEN
  CONJ_TAC THENL [ALL_TAC; ARITH_TAC] THEN
  SUBGOAL_THEN `i - 1 = i - 2 + 1` ASSUME_TAC THENL
  [ ASM_ARITH_TAC; ALL_TAC ] THEN
  ASM_REWRITE_TAC[] THEN
  IMP_REWRITE_TAC[AES256_XTS_DECRYPT_REC_EQ_TAIL] THEN
  ASM_ARITH_TAC
);;

let SUB_LIST_OF_AES256_XTS_DECRYPT = prove(
  `!(i:num) (tail_len:num) (ct:byte list) (iv:int128) (key1:int128 list) (key2:int128 list).
    ~(tail_len = 0) /\ tail_len < 16 ==>
    (SUB_LIST (0,16 * i)
      (aes256_xts_decrypt ct (16 * i + 16 + tail_len) iv key1 key2))
    = aes256_xts_decrypt ct (16 * i) iv key1 key2`,
  REPEAT STRIP_TAC THEN
  (* Case 1: i = 0 *)
  ASM_CASES_TAC `i = 0` THENL
  [
    ASM_REWRITE_TAC[] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[ADD; SUB_LIST_CLAUSES; aes256_xts_decrypt] THEN
    CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC
  ] THEN
  (* Case 2: i = 1 *)
  ASM_CASES_TAC `i = 1` THENL
  [
    ASM_REWRITE_TAC[] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[aes256_xts_decrypt; ADD_ASSOC] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    SUBGOAL_THEN `~(0x20 + tail_len < 0x10)` ASSUME_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    SUBGOAL_THEN `(0x20 + tail_len) MOD 0x10 = tail_len` ASSUME_TAC THENL
    [ ASM_SIMP_TAC[ARITH_RULE `32 = 2 * 16`; MOD_MULT_ADD] THEN
      IMP_REWRITE_TAC[MOD_LT]
      ; ALL_TAC] THEN
    SUBGOAL_THEN `((0x20 + tail_len) - (0x20 + tail_len) MOD 0x10) DIV 0x10 = 0x2` ASSUME_TAC THENL
    [ ASM_REWRITE_TAC[ADD_ASSOC; ADD_SUB] THEN
      ARITH_TAC ; ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC (SPECL [`ct:byte list`; `iv:int128`; `key1:int128 list`; `key2:int128 list`] LENGTH_OF_AES256_XTS_DECRYPT_REC_TRIVIAL) THEN
    DISCH_TAC THEN IMP_REWRITE_TAC[SUB_LIST_APPEND_LEFT] THEN
    REWRITE_TAC[AES256_XTS_DECRYPT_REC_EQ_TAIL_TRIVIAL] THEN
    MP_TAC (SPECL [`ct:byte list`; `iv:int128`; `key1:int128 list`; `key2:int128 list`] LENGTH_OF_AES256_XTS_DECRYPT_TAIL_TRIVIAL) THEN
    DISCH_TAC THEN IMP_REWRITE_TAC[SUB_LIST_LENGTH_IMPLIES] THEN
    ARITH_TAC;
    ALL_TAC
  ] THEN

  (* Case 3: i >= 2 *)
  ASM_CASES_TAC `i >= 2` THENL
  [
    ASM_REWRITE_TAC[ADD_ASSOC] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[aes256_xts_decrypt] THEN
    SUBGOAL_THEN `~(0x10 * i < 0x10)` ASSUME_TAC THENL
    [ ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `~((0x10 * i + 0x10) + tail_len < 0x10)` ASSUME_TAC THENL
    [ ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[LET_DEF; LET_END_DEF] THEN
    SUBGOAL_THEN `((0x10 * i + 0x10) + tail_len) MOD 0x10 = tail_len` SUBST1_TAC THENL
    [ REWRITE_TAC[ARITH_RULE `0x10 * i + 0x10 = 16 * (i + 1)`] THEN
      IMP_REWRITE_TAC[MOD_MULT_ADD; MOD_LT]
      ; ALL_TAC] THEN
    REWRITE_TAC[ADD_SUB; MOD_MULT; SUB_0;
      ARITH_RULE `0x10 * i + 0x10 = 16 * (i + 1)`] THEN
    IMP_REWRITE_TAC[DIV_MULT] THEN
    SUBGOAL_THEN `~(i + 1 < 2)` ASSUME_TAC THENL [ ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `~(i < 2)` ASSUME_TAC THENL [ ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[ADD_SUB; ARITH_RULE `(i + 1) - 2 = i - 1`] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    MP_TAC (SPECL [`0:num`; `(i - 1):num`; `ct:byte list`; `iv:int128`;
      `key1:int128 list`; `key2:int128 list`] LENGTH_OF_AES256_XTS_DECRYPT_REC) THEN
    SUBGOAL_THEN `~((i - 1) < 0)` ASSUME_TAC THENL [ ASM_ARITH_TAC; ALL_TAC] THEN
    IMP_REWRITE_TAC[ARITH_RULE `i >= 2 ==> i - 0x1 - 0x0 + 0x1 = i`] THEN
    IMP_REWRITE_TAC[SUB_LIST_APPEND_LEFT] THEN
    SIMP_TAC[ARITH_RULE `16 * i <= i * 16`] THEN
    IMP_REWRITE_TAC[SUB_LIST_LENGTH_IMPLIES] THEN
    SIMP_TAC[ARITH_RULE `i * 16 = 16 * i`] THEN
    DISCH_TAC THEN
    MP_TAC (SPECL [`0`; `(i-2):num`; `ct:byte list`; `iv:int128`;
      `key1:int128 list`; `key2:int128 list`] AES256_XTS_DECRYPT_REC_EQ_TAIL) THEN
    ANTS_TAC THENL [ ASM_ARITH_TAC; ALL_TAC ] THEN
    IMP_REWRITE_TAC[ARITH_RULE `i >= 2 ==> i - 0x2 + 0x1 = i - 1`];
    ALL_TAC
  ] THEN

  ASM_ARITH_TAC
);;

let READ_BYTES_EQ_READ_BYTE128_1BLOCK = prove(
  `!(ptr:int64) (ct:byte list) (iv:int128) (key1:int128 list) (key2:int128 list) s.
    (read (memory :> bytes128 pt_ptr) s =
      aes256_xts_decrypt_round (bytes_to_int128 (SUB_LIST (0x0,0x10) ct))
      (calculate_tweak 0x0 iv key2)
      key1) ==>
    read (memory :> bytes (pt_ptr,0x10)) s =
      num_of_bytelist (SUB_LIST (0x0,0x10) (aes256_xts_decrypt ct 0x10 iv key1 key2))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[READ_MEMORY_BYTES_BYTES128] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[aes256_xts_decrypt] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[aes256_xts_decrypt_tail] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[SUB_LIST_OF_INT128_TO_BYTES] THEN
  REWRITE_TAC[NUM_OF_BYTELIST_OF_INT128_TO_BYTES]
);;

let READ_BYTES_EQ_READ_BYTE128_2BLOCKS = prove(
  `!(ptr:int64) (ct:byte list) (iv:int128) (key1:int128 list) (key2:int128 list) s.
    (read (memory :> bytes128 pt_ptr) s =
      aes256_xts_decrypt_round (bytes_to_int128 (SUB_LIST (0x0,0x10) ct))
      (calculate_tweak 0x0 iv key2)
      key1) ==>
    (read (memory :> bytes128 (word_add pt_ptr (word 0x10))) s =
      aes256_xts_decrypt_round (bytes_to_int128 (SUB_LIST (0x10,0x10) ct))
      (calculate_tweak 0x1 iv key2)
      key1) ==>
    read (memory :> bytes (pt_ptr,0x20)) s =
      num_of_bytelist (SUB_LIST (0x0,0x20) (aes256_xts_decrypt ct 0x20 iv key1 key2))`,
  REPEAT STRIP_TAC THEN
  IMP_REWRITE_TAC[ARITH_RULE `0x20 = 0x10 + 0x10`; READ_BYTES_AND_BYTE128_SPLIT] THEN
  EXISTS_TAC `aes256_xts_decrypt ct 0x20 iv key1 key2` THEN
  REPEAT CONJ_TAC THENL
  [
    CONV_TAC NUM_REDUCE_CONV;

    MP_TAC (SPECL [`2:num`; `ct:byte list`; `iv:int128`; `key1:int128 list`; `key2:int128 list`]
      LENGTH_OF_AES256_XTS_DECRYPT_FULL_BLOCKS) THEN
    ARITH_TAC;

    REWRITE_TAC[aes256_xts_decrypt] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    MP_TAC (SPECL [`ct:byte list`; `iv:int128`; `key1:int128 list`; `key2:int128 list`]
      LENGTH_OF_AES256_XTS_DECRYPT_REC_TRIVIAL) THEN
    IMP_REWRITE_TAC[SUB_LIST_APPEND_RIGHT_LEMMA] THEN DISCH_TAC THEN
    REWRITE_TAC[aes256_xts_decrypt_tail] THEN
    REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
    REWRITE_TAC[SUB_LIST_OF_INT128_TO_BYTES] THEN
    REWRITE_TAC[NUM_OF_BYTELIST_OF_INT128_TO_BYTES] THEN
    REWRITE_TAC[BYTES_TO_INT128_OF_INT128_TO_BYTES] THEN
    CONV_TAC NUM_REDUCE_CONV;

    MP_TAC (SPECL [`1:num`; `ct:byte list`; `iv:int128`; `key1:int128 list`; `key2:int128 list`]
      SUB_LIST_OF_AES256_XTS_DECRYPT_FULL_BLOCKS) THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    SIMP_TAC[] THEN DISCH_TAC THEN
    IMP_REWRITE_TAC[READ_BYTES_EQ_READ_BYTE128_1BLOCK] THEN
    MP_TAC (SPECL [`1:num`; `ct:byte list`; `iv:int128`; `key1:int128 list`; `key2:int128 list`]
      LENGTH_OF_AES256_XTS_DECRYPT_FULL_BLOCKS) THEN
    CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
    IMP_REWRITE_TAC[SUB_LIST_LENGTH_IMPLIES]
  ]
);;

let READ_BYTES_EQ_READ_BYTE128_3BLOCKS = prove(
  `!(ptr:int64) (ct:byte list) (iv:int128) (key1:int128 list) (key2:int128 list) s.
    (read (memory :> bytes128 pt_ptr) s =
      aes256_xts_decrypt_round (bytes_to_int128 (SUB_LIST (0x0,0x10) ct))
      (calculate_tweak 0x0 iv key2)
      key1) ==>
    (read (memory :> bytes128 (word_add pt_ptr (word 0x10))) s =
      aes256_xts_decrypt_round (bytes_to_int128 (SUB_LIST (0x10,0x10) ct))
      (calculate_tweak 0x1 iv key2)
      key1) ==>
    (read (memory :> bytes128 (word_add pt_ptr (word 0x20))) s =
      aes256_xts_decrypt_round (bytes_to_int128 (SUB_LIST (0x20,0x10) ct))
      (calculate_tweak 0x2 iv key2)
      key1) ==>
    read (memory :> bytes (pt_ptr,0x30)) s =
      num_of_bytelist (SUB_LIST (0x0,0x30) (aes256_xts_decrypt ct 0x30 iv key1 key2))`,
  REPEAT STRIP_TAC THEN
  IMP_REWRITE_TAC[ARITH_RULE `0x30 = 0x20 + 0x10`; READ_BYTES_AND_BYTE128_SPLIT] THEN
  EXISTS_TAC `aes256_xts_decrypt ct 0x30 iv key1 key2` THEN
  REPEAT CONJ_TAC THENL
  [
    CONV_TAC NUM_REDUCE_CONV;

    MP_TAC (SPECL [`3:num`; `ct:byte list`; `iv:int128`; `key1:int128 list`; `key2:int128 list`]
      LENGTH_OF_AES256_XTS_DECRYPT_FULL_BLOCKS) THEN
    ARITH_TAC;

    REWRITE_TAC[aes256_xts_decrypt] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    MP_TAC (SPECL [`0:num`; `1:num`; `ct:byte list`; `iv:int128`; `key1:int128 list`; `key2:int128 list`]
      LENGTH_OF_AES256_XTS_DECRYPT_REC) THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    IMP_REWRITE_TAC[SUB_LIST_APPEND_RIGHT_LEMMA] THEN DISCH_TAC THEN
    REWRITE_TAC[aes256_xts_decrypt_tail] THEN
    REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
    REWRITE_TAC[SUB_LIST_OF_INT128_TO_BYTES] THEN
    REWRITE_TAC[NUM_OF_BYTELIST_OF_INT128_TO_BYTES] THEN
    REWRITE_TAC[BYTES_TO_INT128_OF_INT128_TO_BYTES] THEN
    CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN

  MP_TAC (SPECL [`2:num`; `ct:byte list`; `iv:int128`; `key1:int128 list`; `key2:int128 list`]
    SUB_LIST_OF_AES256_XTS_DECRYPT_FULL_BLOCKS) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SIMP_TAC[] THEN DISCH_TAC THEN
  IMP_REWRITE_TAC[READ_BYTES_EQ_READ_BYTE128_2BLOCKS] THEN
  MP_TAC (SPECL [`2:num`; `ct:byte list`; `iv:int128`; `key1:int128 list`; `key2:int128 list`]
    LENGTH_OF_AES256_XTS_DECRYPT_FULL_BLOCKS) THEN
  CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
  IMP_REWRITE_TAC[SUB_LIST_LENGTH_IMPLIES]
);;

let READ_BYTES_EQ_READ_BYTE128_4BLOCKS = prove(
  `!(ptr:int64) (ct:byte list) (iv:int128) (key1:int128 list) (key2:int128 list) s.
    (read (memory :> bytes128 pt_ptr) s =
      aes256_xts_decrypt_round (bytes_to_int128 (SUB_LIST (0x0,0x10) ct))
      (calculate_tweak 0x0 iv key2)
      key1) ==>
    (read (memory :> bytes128 (word_add pt_ptr (word 0x10))) s =
      aes256_xts_decrypt_round (bytes_to_int128 (SUB_LIST (0x10,0x10) ct))
      (calculate_tweak 0x1 iv key2)
      key1) ==>
    (read (memory :> bytes128 (word_add pt_ptr (word 0x20))) s =
      aes256_xts_decrypt_round (bytes_to_int128 (SUB_LIST (0x20,0x10) ct))
      (calculate_tweak 0x2 iv key2)
      key1) ==>
    (read (memory :> bytes128 (word_add pt_ptr (word 0x30))) s =
      aes256_xts_decrypt_round (bytes_to_int128 (SUB_LIST (0x30,0x10) ct))
      (calculate_tweak 0x3 iv key2)
      key1) ==>
    read (memory :> bytes (pt_ptr,0x40)) s =
      num_of_bytelist (SUB_LIST (0x0,0x40) (aes256_xts_decrypt ct 0x40 iv key1 key2))`,
  REPEAT STRIP_TAC THEN
  IMP_REWRITE_TAC[ARITH_RULE `0x40 = 0x30 + 0x10`; READ_BYTES_AND_BYTE128_SPLIT] THEN
  EXISTS_TAC `aes256_xts_decrypt ct 0x40 iv key1 key2` THEN
  REPEAT CONJ_TAC THENL
  [
    CONV_TAC NUM_REDUCE_CONV;

    MP_TAC (SPECL [`4:num`; `ct:byte list`; `iv:int128`; `key1:int128 list`; `key2:int128 list`]
      LENGTH_OF_AES256_XTS_DECRYPT_FULL_BLOCKS) THEN
    ARITH_TAC;

    REWRITE_TAC[aes256_xts_decrypt] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    MP_TAC (SPECL [`0:num`; `2:num`; `ct:byte list`; `iv:int128`; `key1:int128 list`; `key2:int128 list`]
      LENGTH_OF_AES256_XTS_DECRYPT_REC) THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    IMP_REWRITE_TAC[SUB_LIST_APPEND_RIGHT_LEMMA] THEN DISCH_TAC THEN
    REWRITE_TAC[aes256_xts_decrypt_tail] THEN
    REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
    REWRITE_TAC[SUB_LIST_OF_INT128_TO_BYTES] THEN
    REWRITE_TAC[BYTES_TO_INT128_OF_INT128_TO_BYTES] THEN
    CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN

  MP_TAC (SPECL [`3:num`; `ct:byte list`; `iv:int128`; `key1:int128 list`; `key2:int128 list`]
    SUB_LIST_OF_AES256_XTS_DECRYPT_FULL_BLOCKS) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SIMP_TAC[] THEN DISCH_TAC THEN
  IMP_REWRITE_TAC[READ_BYTES_EQ_READ_BYTE128_3BLOCKS] THEN
  MP_TAC (SPECL [`3:num`; `ct:byte list`; `iv:int128`; `key1:int128 list`; `key2:int128 list`]
    LENGTH_OF_AES256_XTS_DECRYPT_FULL_BLOCKS) THEN
  CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
  IMP_REWRITE_TAC[SUB_LIST_LENGTH_IMPLIES]
);;


let READ_BYTES_EQ_READ_BYTE128_5BLOCKS = prove(
  `!(ptr:int64) (ct:byte list) (iv:int128) (key1:int128 list) (key2:int128 list) s.
    (read (memory :> bytes128 pt_ptr) s =
      aes256_xts_decrypt_round (bytes_to_int128 (SUB_LIST (0x0,0x10) ct))
      (calculate_tweak 0x0 iv key2)
      key1) ==>
    (read (memory :> bytes128 (word_add pt_ptr (word 0x10))) s =
      aes256_xts_decrypt_round (bytes_to_int128 (SUB_LIST (0x10,0x10) ct))
      (calculate_tweak 0x1 iv key2)
      key1) ==>
    (read (memory :> bytes128 (word_add pt_ptr (word 0x20))) s =
      aes256_xts_decrypt_round (bytes_to_int128 (SUB_LIST (0x20,0x10) ct))
      (calculate_tweak 0x2 iv key2)
      key1) ==>
    (read (memory :> bytes128 (word_add pt_ptr (word 0x30))) s =
      aes256_xts_decrypt_round (bytes_to_int128 (SUB_LIST (0x30,0x10) ct))
      (calculate_tweak 0x3 iv key2)
      key1) ==>
    (read (memory :> bytes128 (word_add pt_ptr (word 0x40))) s =
      aes256_xts_decrypt_round (bytes_to_int128 (SUB_LIST (0x40,0x10) ct))
      (calculate_tweak 0x4 iv key2)
      key1) ==>
    read (memory :> bytes (pt_ptr,0x50)) s =
      num_of_bytelist (SUB_LIST (0x0,0x50) (aes256_xts_decrypt ct 0x50 iv key1 key2))`,
  REPEAT STRIP_TAC THEN
  IMP_REWRITE_TAC[ARITH_RULE `0x50 = 0x40 + 0x10`; READ_BYTES_AND_BYTE128_SPLIT] THEN
  EXISTS_TAC `aes256_xts_decrypt ct 0x50 iv key1 key2` THEN
  REPEAT CONJ_TAC THENL
  [
    CONV_TAC NUM_REDUCE_CONV;

    MP_TAC (SPECL [`5:num`; `ct:byte list`; `iv:int128`; `key1:int128 list`; `key2:int128 list`]
      LENGTH_OF_AES256_XTS_DECRYPT_FULL_BLOCKS) THEN
    ARITH_TAC;

    REWRITE_TAC[aes256_xts_decrypt] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    MP_TAC (SPECL [`0:num`; `3:num`; `ct:byte list`; `iv:int128`; `key1:int128 list`; `key2:int128 list`]
      LENGTH_OF_AES256_XTS_DECRYPT_REC) THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    IMP_REWRITE_TAC[SUB_LIST_APPEND_RIGHT_LEMMA] THEN DISCH_TAC THEN
    REWRITE_TAC[aes256_xts_decrypt_tail] THEN
    REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
    REWRITE_TAC[SUB_LIST_OF_INT128_TO_BYTES] THEN
    REWRITE_TAC[BYTES_TO_INT128_OF_INT128_TO_BYTES] THEN
    CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN

  MP_TAC (SPECL [`4:num`; `ct:byte list`; `iv:int128`; `key1:int128 list`; `key2:int128 list`]
    SUB_LIST_OF_AES256_XTS_DECRYPT_FULL_BLOCKS) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SIMP_TAC[] THEN DISCH_TAC THEN
  IMP_REWRITE_TAC[READ_BYTES_EQ_READ_BYTE128_4BLOCKS] THEN
  MP_TAC (SPECL [`4:num`; `ct:byte list`; `iv:int128`; `key1:int128 list`; `key2:int128 list`]
    LENGTH_OF_AES256_XTS_DECRYPT_FULL_BLOCKS) THEN
  CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
  IMP_REWRITE_TAC[SUB_LIST_LENGTH_IMPLIES]
);;

(**********************************************************************)
(**                           Tactics                                **)

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
  FIRST_X_ASSUM(MP_TAC o SPEC tm o  MATCH_MP (MESON[] lemma)) THEN
      ANTS_TAC THENL
      [ EXPAND_TAC "key1" THEN
        CONV_TAC (RAND_CONV (
          REWRITE_CONV [aes256_xts_decrypt_round] THENC
          DEPTH_CONV let_CONV)) THEN
        AESDEC_TAC; DISCH_TAC ];;

let TAIL_SWAP_CASE_TAC case =
  let c_tm = `case:num` in
  let v_tm = `v:num` in
  let v = rand (concl (NUM_RED_CONV (subst [case,c_tm] `0x10 + case`))) in
  let r1 = subst [case,c_tm; v,v_tm] `curr_len + 0x10 + case = curr_len + v` in
  let t1 = subst [case,c_tm] `(cipher_stealing_inv case curr_len (val (tail_len:int64)) PP ct):int128` in
  POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th]) THEN
  (* Simplify so that symbolic execution could match up, but couldn't use
     CONV_TAC NUM_REDUCE_CONV because of non-overlapping *)
  RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE r1]) THEN
  ARM_ACCSTEPS_TAC AES_XTS_DECRYPT_EXEC [] (1--5) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM ADD_ASSOC]) THEN
  RULE_ASSUM_TAC (CONV_RULE NUM_REDUCE_CONV) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
  [
    REWRITE_TAC[
      WORD_RULE `!(a:int64) b c. word_add (word_add a b) c = word_add a (word_add b c)`;
      WORD_RULE `!a b. word_add ((word a):int64) (word b) = word (a + b)`];

    MATCH_MP_TAC (snd (EQ_IMP_RULE (SPECL [`(word_add pt_ptr (word curr_len)):int64`;
      `s5:armstate`; t1] BREAK_ONE_BLOCK_INTO_BYTES))) THEN
    REWRITE_TAC[
      WORD_RULE `!(a:int64) b c. word_add (word_add a b) c = word_add a (word_add b c)`;
      WORD_RULE `!a b. word_add ((word a):int64) (word b) = word (a + b)`] THEN
    ASM_REWRITE_TAC[] THEN
    CONV_TAC NUM_REDUCE_CONV THEN

    MP_TAC (SPECL [case; `curr_len:num`; `tail_len:int64`; `PP:int128`; `ct:byte list`]
      CIPHER_STEALING_BYTE_EQUAL) THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    STRIP_TAC THEN

    MAP_EVERY (fun i -> CONJ_TAC THENL
      [CIPHER_STEALING_INV_SIMP_TAC (mk_numeral (num i)); ALL_TAC])
      (0--0xe) THEN
    CIPHER_STEALING_INV_SIMP_TAC `0xf:num`;

    MP_TAC (SPECL [`pt_ptr:int64`; case; `val (tail_len:int64)`;
      `curr_len:num`; `(int128_to_bytes PP):byte list`; `s5:armstate`]
      BYTE_LIST_AT_SPLIT_BACKWARDS) THEN
    REWRITE_TAC[LENGTH_OF_INT128_TO_BYTES] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    ASM_SIMP_TAC[] THEN
    ANTS_TAC THENL
    [ IMP_REWRITE_TAC[WORD_ZX_ZX] THEN
      REWRITE_TAC[DIMINDEX_8; DIMINDEX_32; DIMINDEX_64] THEN
      MP_TAC (SPECL [case; `curr_len:num`; `tail_len:int64`; `PP:int128`; `ct:byte list`]
        CIPHER_STEALING_INV_SELECT) THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      ASM_SIMP_TAC[]
      ; ALL_TAC ] THEN
    MESON_TAC[];

    WORD_ARITH_TAC;
    WORD_ARITH_TAC
    ];;

let TAIL_SWAP_ASM_CASES_TAC case =
  let c_tm = `case:num` in
  let asm_case = subst [case, c_tm] `(i:num) = case` in
  ASM_CASES_TAC asm_case THENL [ TAIL_SWAP_CASE_TAC case; ALL_TAC] THEN
  MP_TAC (SPECL [case; `i:num`] LE_LT) THEN
  ASM_SIMP_TAC[] THEN
  DISCH_TAC THEN
  MP_TAC (SPECL [case; `i:num`] LE_SUC_LT) THEN
  ASM_SIMP_TAC[] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[] THEN
  DISCH_TAC;;


(**********************************************************************)
(**                           Proofs                                 **)


(* Proof: Cipher stealing *)
let CIPHER_STEALING_CORRECT = time prove(
  `!ct_ptr pt_ptr ct key1_ptr iv len pc
    k00 k01 k02 k03 k04 k05 k06 k07 k08 k09 k0a k0b k0c k0d k0e
    tail_len num_blocks key1 num_blocks_adjusted num_5blocks_adjusted.
    nonoverlapping (word pc, LENGTH aes_xts_decrypt_mc) (pt_ptr, val len)
    /\ nonoverlapping (ct_ptr, val len) (pt_ptr, val len)
    /\ nonoverlapping (key1_ptr, 260) (pt_ptr, val len)
    /\ val len >= 16 /\ val len <= 2 EXP 24 /\ LENGTH ct = val len
    /\ word_add tail_len num_blocks = len
    /\ word_and len (word 0xfffffffffffffff0) = num_blocks
    /\ word_and len (word 0xf) = tail_len
    /\ [k00; k01; k02; k03; k04; k05; k06; k07; k08; k09; k0a; k0b; k0c; k0d; k0e] = key1
    /\ (if val tail_len = 0x0 then num_blocks else word_sub num_blocks (word 0x10)) = num_blocks_adjusted
    /\ word (val num_blocks_adjusted DIV 0x50) = num_5blocks_adjusted
    ==> ensures arm
    (\s. aligned_bytes_loaded s (word pc) aes_xts_decrypt_mc /\
         read PC s = word (pc + 0xa0c) /\
         read X0 s = word_add ct_ptr (word (acc_len num_5blocks_adjusted num_blocks_adjusted)) /\
         read X1 s = word_add pt_ptr (word (acc_len num_5blocks_adjusted num_blocks_adjusted)) /\
         read X3 s = key1_ptr /\
         read X21 s = tail_len /\
         read Q6 s = calculate_tweak (acc_blocks num_5blocks_adjusted num_blocks_adjusted T) iv key2 /\
         read X19 s = word 0x87 /\
         read Q16 s = k00 /\ read Q17 s = k01 /\ read Q12 s = k02 /\ read Q13 s = k03 /\
         read Q14 s = k04 /\ read Q15 s = k05 /\ read Q4 s = k06 /\ read Q5 s = k07 /\
         read Q18 s = k08 /\ read Q19 s = k09 /\ read Q20 s = k0a /\ read Q21 s = k0b /\
         read Q22 s = k0c /\ read Q23 s = k0d /\ read Q7 s = k0e /\
         byte_list_at ct ct_ptr len s /\
         byte_list_at (aes256_xts_decrypt ct (acc_len num_5blocks_adjusted num_blocks_adjusted) iv key1 key2)
            pt_ptr (word (acc_len num_5blocks_adjusted num_blocks_adjusted)) s)
    (\s. read PC s = word (pc + 0xb58) /\
         byte_list_at (aes256_xts_decrypt ct (val len) iv key1 key2) pt_ptr len s
         )
    (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI,,
     MAYCHANGE [X19; X20; X21; X22],,
     MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15],,
     MAYCHANGE [memory :> bytes(pt_ptr, val len)])
    `,
  REWRITE_TAC [(REWRITE_CONV [aes_xts_decrypt_mc] THENC LENGTH_CONV) `LENGTH aes_xts_decrypt_mc`] THEN
  REWRITE_TAC[set_key_schedule; C_ARGUMENTS; SOME_FLAGS;
    NONOVERLAPPING_CLAUSES; byte_list_at;
    MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REPEAT STRIP_TAC THEN

  (* Prove once and for all the bounds for num_blocks, num_blocks_adjusted
     and num_5blocks_adjusted *)
  SUBGOAL_THEN `~(val (num_blocks:int64) < 16)` ASSUME_TAC THENL
  [ SUBGOAL_THEN `~(val (len:int64) < 16)` MP_TAC THENL
    [ASM_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `word_and len (word 0xfffffffffffffff0) = (num_blocks:int64)` THEN
    MP_TAC (SPECL [`len:int64`; `num_blocks:int64`] NUM_BLOCKS_LO_BOUND_1BLOCK_THM) THEN
    SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `val (num_blocks:int64) <= 2 EXP 24` ASSUME_TAC THENL
  [ UNDISCH_TAC `val (len:int64) <= 2 EXP 24` THEN
    UNDISCH_TAC `word_and len (word 0xfffffffffffffff0) = (num_blocks:int64)` THEN
    MP_TAC (SPECL [`len:int64`; `num_blocks:int64`] NUM_BLOCKS_HI_BOUND_THM) THEN
    SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~(val (num_blocks_adjusted:int64) < 0)` ASSUME_TAC THENL
  [ UNDISCH_TAC `~(val (num_blocks:int64) < 16)` THEN
    UNDISCH_TAC `(if val (tail_len:int64) = 0x0
     then (num_blocks:int64)
     else word_sub num_blocks (word 0x10)) =
     num_blocks_adjusted` THEN
    MP_TAC (SPECL [`num_blocks:int64`;`tail_len:int64`;`num_blocks_adjusted:int64`]
      NUM_BLOCKS_ADJUSTED_LO_BOUND_1BLOCK_THM) THEN SIMP_TAC[]
    ; ALL_TAC] THEN
  SUBGOAL_THEN `val (num_blocks_adjusted:int64) <= 2 EXP 24` ASSUME_TAC THENL
  [ UNDISCH_TAC `val (num_blocks:int64) <= 2 EXP 24` THEN
    UNDISCH_TAC `~(val (num_blocks:int64) < 16)` THEN
    UNDISCH_TAC `(if val (tail_len:int64) = 0x0
     then (num_blocks:int64)
     else word_sub num_blocks (word 0x10)) =
     num_blocks_adjusted` THEN
    MP_TAC (SPECL [`num_blocks:int64`;`tail_len:int64`;`num_blocks_adjusted:int64`]
      NUM_BLOCKS_ADJUSTED_HI_BOUND_THM) THEN SIMP_TAC[]
    ; ALL_TAC] THEN
  SUBGOAL_THEN `val (tail_len:int64) < 16` ASSUME_TAC THENL
  [ EXPAND_TAC "tail_len" THEN
    REWRITE_TAC[ARITH_RULE `0xf = 2 EXP 4 - 1`] THEN
    REWRITE_TAC[VAL_WORD_AND_MASK_WORD] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    SIMP_TAC[MOD_LT_EQ] THEN
    CONV_TAC NUM_REDUCE_CONV
  ; ALL_TAC] THEN
  (* relationship between variables *)
  SUBGOAL_THEN `val (num_blocks:int64) <= val (len:int64)` ASSUME_TAC THENL
  [ EXPAND_TAC "num_blocks" THEN SIMP_TAC[NUM_BLOCKS_LT_LEN_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `val (num_blocks_adjusted:int64) <= val (len:int64)` ASSUME_TAC THENL
  [ EXPAND_TAC "num_blocks_adjusted" THEN
    COND_CASES_TAC THENL
    [ ASM_SIMP_TAC[];
      UNDISCH_TAC `~(val (num_blocks:int64) < 16)` THEN
      UNDISCH_TAC `word_and (len:int64) (word 0xfffffffffffffff0) = (num_blocks:int64)` THEN
      MP_TAC (SPECL [`len:int64`; `num_blocks:int64`] NUM_BLOCKS_ADJUSTED_LT_LEN_THM) THEN
      SIMP_TAC[]]; ALL_TAC] THEN
  SUBGOAL_THEN `val (num_5blocks_adjusted:int64) * 0x50 <= val (num_blocks_adjusted:int64)` ASSUME_TAC THENL
  [ EXPAND_TAC "num_5blocks_adjusted" THEN
    REWRITE_TAC [VAL_WORD; DIMINDEX_64] THEN
    UNDISCH_TAC `val (num_blocks_adjusted:int64) <= 0x2 EXP 0x18` THEN
    ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `val (num_5blocks_adjusted:int64) * 0x50 <= val (len:int64)` ASSUME_TAC THENL
  [ EXPAND_TAC "num_5blocks_adjusted" THEN
    REWRITE_TAC [VAL_WORD; DIMINDEX_64] THEN
    UNDISCH_TAC `val (num_blocks_adjusted:int64) <= 0x2 EXP 0x18` THEN
    UNDISCH_TAC `val (num_blocks_adjusted:int64) <= val (len:int64)` THEN
    ARITH_TAC; ALL_TAC] THEN

  (* Prove more properties about num_blocks_adjusted and num_5blocks_adjusted *)
  SUBGOAL_THEN `val (num_blocks_adjusted:int64) DIV 0x50 = val (num_5blocks_adjusted:int64)` ASSUME_TAC THENL
  [ EXPAND_TAC "num_5blocks_adjusted" THEN
    IMP_REWRITE_TAC[VAL_WORD; DIMINDEX_64; MOD_LT] THEN
    UNDISCH_TAC `val (num_blocks_adjusted:int64) <= 0x2 EXP 0x18` THEN
    ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `0x10 divides val (num_blocks_adjusted:int64)` ASSUME_TAC THENL
  [ EXPAND_TAC "num_blocks_adjusted" THEN
    EXPAND_TAC "num_blocks" THEN
    COND_CASES_TAC THENL
    [ REWRITE_TAC[NUM_BLOCKS_TO_VAL] THEN
      IMP_REWRITE_TAC[VAL_WORD; DIMINDEX_64; MOD_LT; DIVIDES_RMUL; DIVIDES_REFL] THEN
      MP_TAC (SPEC `len:int64` VAL_BOUND_64) THEN
      ARITH_TAC;

      IMP_REWRITE_TAC[NUM_BLOCKS_MINUS1_TO_VAL] THEN
      IMP_REWRITE_TAC[VAL_WORD; DIMINDEX_64; MOD_LT; DIVIDES_RMUL; DIVIDES_REFL] THEN
      MP_TAC (SPEC `len:int64` VAL_BOUND_64) THEN
      ARITH_TAC]; ALL_TAC] THEN

  (* If no tail, execute to the end *)
  ASM_CASES_TAC `val (tail_len:int64) = 0` THENL
  [
    ENSURES_INIT_TAC "s0" THEN
    ARM_ACCSTEPS_TAC AES_XTS_DECRYPT_EXEC [] (1--2) THEN
    (* Discharge if condition *)
    SUBGOAL_THEN `val (word_and (tail_len:int64) (word 0xf)) = 0x0` MP_TAC THENL
    [ UNDISCH_TAC `val (tail_len:int64) = 0x0` THEN BITBLAST_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN

    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN

    SUBGOAL_THEN `val (word (acc_len (num_5blocks_adjusted:int64) (num_blocks_adjusted:int64)):int64) =
      acc_len num_5blocks_adjusted num_blocks_adjusted` ASSUME_TAC THENL
    [ IMP_REWRITE_TAC[VAL_WORD; DIMINDEX_64; MOD_LT] THEN
      MP_TAC (SPECL [`num_5blocks_adjusted:int64`; `num_blocks_adjusted:int64`; `2 EXP 64`]
        BOUND_OF_ACC_LEN) THEN
      ANTS_TAC THENL [ ASM_ARITH_TAC; ALL_TAC] THEN
      ANTS_TAC THENL [ ASM_SIMP_TAC[]; ALL_TAC] THEN
      ANTS_TAC THENL [ ASM_SIMP_TAC[]; ALL_TAC] THEN
      ANTS_TAC THENL [ ASM_ARITH_TAC; ALL_TAC] THEN
      SIMP_TAC[]; ALL_TAC] THEN
    POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
    (* Prove that acc_len is equal to total len because there is no tail *)
    SUBGOAL_THEN `val (len:int64) =
      acc_len (num_5blocks_adjusted:int64) (num_blocks_adjusted:int64)` SUBST1_TAC THENL
    [ SUBGOAL_THEN `len = (num_blocks:int64)` SUBST1_TAC THENL
      [ EXPAND_TAC "len" THEN
        SUBGOAL_THEN `tail_len:int64 = word 0` ASSUME_TAC THENL
        [ REWRITE_TAC[GSYM VAL_EQ_0] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
        REWRITE_TAC[ASSUME `tail_len:int64 = word 0`; WORD_ADD_0]
        ; ALL_TAC] THEN
      SUBGOAL_THEN `num_blocks = (num_blocks_adjusted:int64)` SUBST1_TAC THENL
      [ EXPAND_TAC "num_blocks_adjusted" THEN
        REWRITE_TAC[ASSUME `val (tail_len:int64) = 0`]
        ; ALL_TAC] THEN
      REWRITE_TAC[acc_len] THEN
      REPEAT_N 4 (COND_CASES_TAC THENL[ASM_ARITH_TAC; ALL_TAC]) THEN

      CONV_TAC SYM_CONV THEN
      REWRITE_TAC[ARITH_RULE `!a. 0x50 * a = a * 0x50`] THEN
      MATCH_MP_TAC (SPECL [`val (num_blocks_adjusted:int64)`; `val (num_5blocks_adjusted:int64)`] DIVISION_BY_80_LEMMA) THEN
      REPEAT CONJ_TAC THENL
      [
        ASM_SIMP_TAC[];
        ASM_SIMP_TAC[];

        UNDISCH_TAC `val (num_5blocks_adjusted:int64) * 0x50 <= val (num_blocks_adjusted:int64)` THEN
        UNDISCH_TAC `~(val (num_5blocks_adjusted:int64) * 0x50 + 0x10 = val (num_blocks_adjusted:int64))` THEN
        ARITH_TAC;

        UNDISCH_TAC `val (num_5blocks_adjusted:int64) * 0x50 <= val (num_blocks_adjusted:int64)` THEN
        UNDISCH_TAC `~(val (num_5blocks_adjusted:int64) * 0x50 + 0x20 = val (num_blocks_adjusted:int64))` THEN
        ARITH_TAC;

        UNDISCH_TAC `val (num_5blocks_adjusted:int64) * 0x50 <= val (num_blocks_adjusted:int64)` THEN
        UNDISCH_TAC `~(val (num_5blocks_adjusted:int64) * 0x50 + 0x30 = val (num_blocks_adjusted:int64))` THEN
        ARITH_TAC;

        UNDISCH_TAC `val (num_5blocks_adjusted:int64) * 0x50 <= val (num_blocks_adjusted:int64)` THEN
        UNDISCH_TAC `~(val (num_5blocks_adjusted:int64) * 0x50 + 0x40 = val (num_blocks_adjusted:int64))` THEN
        ARITH_TAC]
      ; ALL_TAC] THEN
    ASM_SIMP_TAC[]
  ; ALL_TAC] THEN

  (* The cipher stealing branch *)
  (* Break the rest of the program into two parts: before byte-swap and after.
     This is because byte-swap needs another invariant proof. *)
  ABBREV_TAC `curr_len = (acc_len (num_5blocks_adjusted:int64) (num_blocks_adjusted:int64)):num` THEN
  ABBREV_TAC `curr_blocks = (acc_blocks (num_5blocks_adjusted:int64) (num_blocks_adjusted:int64) T):num` THEN

  SUBGOAL_THEN `curr_len + 0x10 <= val (len:int64)` ASSUME_TAC THENL
  [ EXPAND_TAC "curr_len" THEN
    MP_TAC (SPECL [`num_5blocks_adjusted:int64`; `num_blocks_adjusted:int64`] VALUE_OF_ACC_LEN) THEN
    REPEAT_N 3 (ANTS_TAC THENL [ASM_ARITH_TAC ORELSE ASM_SIMP_TAC[]; ALL_TAC]) THEN
    SIMP_TAC[] THEN DISCH_TAC THEN
    EXPAND_TAC "num_blocks_adjusted" THEN
    SIMP_TAC[ASSUME `~(val (tail_len:int64) = 0)`] THEN
    UNDISCH_TAC `val (num_blocks:int64) <= val (len:int64)` THEN
    SUBGOAL_THEN `val (num_blocks:int64) >= 16` MP_TAC THENL
    [ASM_ARITH_TAC; ALL_TAC] THEN
    WORD_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `val ((word curr_len):int64) = curr_len` ASSUME_TAC THENL
  [ IMP_REWRITE_TAC[VAL_WORD; DIMINDEX_64; MOD_LT] THEN
    EXPAND_TAC "curr_len" THEN
    MP_TAC (SPECL [`num_5blocks_adjusted:int64`; `num_blocks_adjusted:int64`; `2 EXP 64`]
      BOUND_OF_ACC_LEN) THEN
    ANTS_TAC THENL [ ASM_ARITH_TAC; ALL_TAC] THEN
    ANTS_TAC THENL [ ASM_SIMP_TAC[]; ALL_TAC] THEN
    ANTS_TAC THENL [ ASM_SIMP_TAC[]; ALL_TAC] THEN
    ANTS_TAC THENL [ ASM_ARITH_TAC; ALL_TAC] THEN
    SIMP_TAC[]; ALL_TAC] THEN

  ENSURES_SEQUENCE_TAC `pc + 0xab8`
  `\s.
      read X0 s = word_add (word_add ct_ptr (word curr_len)) (word 0x10) /\
      read X1 s = word_add pt_ptr (word curr_len) /\
      read X21 s = tail_len /\
      read Q6 s = calculate_tweak curr_blocks iv key2 /\
      read Q16 s = k00 /\ read Q17 s = k01 /\ read Q12 s = k02 /\ read Q13 s = k03 /\
      read Q14 s = k04 /\ read Q15 s = k05 /\ read Q4 s = k06 /\ read Q5 s = k07 /\
      read Q18 s = k08 /\ read Q19 s = k09 /\ read Q20 s = k0a /\ read Q21 s = k0b /\
      read Q22 s = k0c /\ read Q23 s = k0d /\ read Q7 s = k0e /\

      byte_list_at ct ct_ptr len s /\
      byte_list_at (aes256_xts_decrypt ct curr_len iv key1 key2) pt_ptr (word curr_len) s /\
      read (memory :> bytes128 (word_add pt_ptr (word curr_len))) s =
        aes256_xts_decrypt_round
          (bytes_to_int128 (SUB_LIST (curr_len,0x10) ct))
          (calculate_tweak (curr_blocks + 0x1) iv key2)
          key1` THEN
  CONJ_TAC THENL
  [
    MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN
    EXISTS_TAC `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
        MAYCHANGE [X19; X20; X21; X22],,
        MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15],,
        MAYCHANGE [memory :> bytes128 (word_add pt_ptr (word curr_len))]` THEN
    REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    CONJ_TAC THENL [
      REPEAT (GEN_REWRITE_TAC ONCE_DEPTH_CONV [GSYM SEQ_ASSOC] THEN
              MATCH_MP_TAC SUBSUMED_SEQ THEN REWRITE_TAC[SUBSUMED_REFL]) THEN
      ABBREV_TAC `vallen = val (len:int64)` THEN
      SUBSUMED_MAYCHANGE_TAC; ALL_TAC] THEN

    REWRITE_TAC[byte_list_at] THEN
    UNDISCH_THEN `val ((word curr_len):int64) = curr_len`
        (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th]) THEN

    ENSURES_INIT_TAC "s0" THEN
    ARM_ACCSTEPS_TAC AES_XTS_DECRYPT_EXEC [] (1--2) THEN

    (* Discharge if condition *)
    SUBGOAL_THEN `~(val (word_and (tail_len:int64) (word 0xf)) = 0x0)` MP_TAC THENL
    [ UNDISCH_TAC `~(val (tail_len:int64) = 0x0)` THEN
      UNDISCH_TAC `val (tail_len:int64) < 16` THEN
      MP_TAC (SPEC `tail_len:int64` WORD_AND_MASK16_EQ_0) THEN
      SIMP_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN

    (* Decrypt last block *)
    ARM_ACCSTEPS_TAC AES_XTS_DECRYPT_EXEC [] (3--11) THEN
    TWEAK_TAC `Q8:(armstate,int128)component` `(curr_blocks + 1):num` `curr_blocks:num` THEN
    MP_TAC (SPECL [`ct_ptr:int64`; `curr_len:num`; `len:int64`; `ct:byte list`; `s11:armstate`] READ_LAST_LEMMA) THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    ARM_ACCSTEPS_TAC AES_XTS_DECRYPT_EXEC [] (12--42) THEN
    XTSDEC_TAC `Q26:(armstate,int128)component` `curr_len:num` `(curr_blocks + 1):num` THEN
    ARM_ACCSTEPS_TAC AES_XTS_DECRYPT_EXEC [] (43--43) THEN

    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]
    ; ALL_TAC
  ] THEN

  ABBREV_TAC `PP = aes256_xts_decrypt_round
    (bytes_to_int128 (SUB_LIST (curr_len,0x10) (ct:byte list)))
    (calculate_tweak (curr_blocks + 0x1) (iv:int128) (key2:int128 list))
    (key1:int128 list)` THEN
  SUBGOAL_THEN `curr_len + 16 + val (tail_len:int64) = val (len:int64)` ASSUME_TAC THENL
  [ REWRITE_TAC[GSYM (ASSUME `acc_len num_5blocks_adjusted num_blocks_adjusted = curr_len`)] THEN
    MP_TAC (SPECL [`num_5blocks_adjusted:int64`; `num_blocks_adjusted:int64`] VALUE_OF_ACC_LEN) THEN
    ANTS_TAC THENL[ASM_ARITH_TAC; ALL_TAC] THEN
    ANTS_TAC THENL[ASM_ARITH_TAC; ALL_TAC] THEN
    ANTS_TAC THENL[ASM_SIMP_TAC[]; ALL_TAC] THEN
    SIMP_TAC[] THEN DISCH_TAC THEN
    EXPAND_TAC "num_blocks_adjusted" THEN
    UNDISCH_TAC `~(val (tail_len:int64) = 0)` THEN
    SIMP_TAC[] THEN DISCH_TAC THEN
    ASM_SIMP_TAC[VAL_WORD_SUB; DIMINDEX_64; VAL_WORD;
      ARITH_RULE `16 MOD 2 EXP 64 = 16`] THEN
    MP_TAC (SPECL [`val (num_blocks:int64)`; `0x2 EXP 0x40`; `16`]
      (ARITH_RULE `!a b c. c <= a ==> c <= b ==> a + b - c = (a - c) + b`)) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN DISCH_TAC THEN
    MP_TAC (SPECL [`1`; `0x2 EXP 0x40`; `val (num_blocks:int64) - 16`]
      (CONJUNCT1 (CONJUNCT2 (CONJUNCT2 MOD_MULT_ADD)))) THEN
    SIMP_TAC[ARITH_RULE `!x. 1 * x = x`] THEN DISCH_TAC THEN
    IMP_REWRITE_TAC[MOD_LT] THEN
    CONJ_TAC THENL [
      SUBGOAL_THEN `val (num_blocks:int64) - 0x10 + 0x10 + val (tail_len:int64)
        = val num_blocks + val tail_len` SUBST1_TAC THENL
      [ IMP_REWRITE_TAC[ADD_ASSOC; SUB_ADD] THEN ASM_ARITH_TAC; ALL_TAC] THEN
      EXPAND_TAC "len" THEN
      REWRITE_TAC[VAL_WORD_ADD] THEN
      IMP_REWRITE_TAC[MOD_LT; DIMINDEX_64] THEN
      CONJ_TAC THENL [ARITH_TAC; ASM_ARITH_TAC];
      ALL_TAC
    ] THEN
    ASM_ARITH_TAC; ALL_TAC] THEN
  (* Invariant proof for .composite_dec_loop *)
  (* Invariant:
    X0 points to tail of ct
    X1 points to starting of last full block of pt
    X13 points to tail of pt
    X20 points to tail of ct
    X21 holds decreasing tail_len
    Q6 holds second to last tweak
    Q16 ... Q7 holds the key schedule for encryption

    Memory: ct_ptr points to the input
    Memory: Up to the second to last block, the output matches the specification
    Memory: For the last block, for each byte
      [0,i) -- previous decryption result
      [i,tail_len) -- equal corresponding ct tail bytes, Cm
      [tail_len,16] -- previous decryption result
    Memory: For the tail, for each byte
      [i,tail_len) -- copied over from Pm block
  *)
  ENSURES_WHILE_PADOWN_TAC
    `val (tail_len:int64)`
    `0`
    `pc + 0xac0`
    `pc + 0xad4`
    `\i s.
    ( read X0 s = word_add (word_add ct_ptr (word curr_len)) (word 0x10) /\
      read X1 s = word_add pt_ptr (word curr_len) /\
      read X13 s = word_add (word_add pt_ptr (word curr_len)) (word 0x10) /\
      read X20 s = word_add (word_add ct_ptr (word curr_len)) (word 0x10) /\
      read X21 s = (word i):int64 /\
      read Q6 s = calculate_tweak curr_blocks iv key2 /\
      read Q16 s = k00 /\ read Q17 s = k01 /\ read Q12 s = k02 /\ read Q13 s = k03 /\
      read Q14 s = k04 /\ read Q15 s = k05 /\ read Q4 s = k06 /\ read Q5 s = k07 /\
      read Q18 s = k08 /\ read Q19 s = k09 /\ read Q20 s = k0a /\ read Q21 s = k0b /\
      read Q22 s = k0c /\ read Q23 s = k0d /\ read Q7 s = k0e /\
      byte_list_at ct ct_ptr len s /\
      byte_list_at (aes256_xts_decrypt ct curr_len iv key1 key2) pt_ptr (word curr_len) s /\

      read (memory :> bytes128 (word_add pt_ptr (word curr_len))) s =
        cipher_stealing_inv i curr_len (val (tail_len:int64)) PP ct /\

      byte_list_at (SUB_LIST (i, val tail_len - i) (int128_to_bytes PP))
        (word_add pt_ptr (word (curr_len + 0x10 + i)))
        (word ((val tail_len) - i)) s) /\
      // loop backedge condition
      (read ZF s <=> i = 0) /\
      (read NF s <=> ival ((word i):int64) < &0) /\
      (read VF s <=> ~(ival ((word (i + 1)):int64) - &1 = ival ((word i):int64)))` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
  [
    (* Subgoal1: 0 < val tail_len *)
    ASM_ARITH_TAC;

    (* Subgoal2: invariant holds before entering loop *)
    REWRITE_TAC[byte_list_at] THEN
    UNDISCH_THEN `val ((word curr_len):int64) = curr_len`
        (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th]) THEN

    ENSURES_INIT_TAC "s0" THEN
    ARM_ACCSTEPS_TAC AES_XTS_DECRYPT_EXEC [] (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
    [
      REWRITE_TAC[WORD_VAL];

      REWRITE_TAC[cipher_stealing_inv; SUB_REFL] THEN
      SUBGOAL_THEN `SUB_LIST (val (tail_len:int64),0x0) (SUB_LIST (curr_len + 16,val tail_len) (ct:byte list)) = []` SUBST1_TAC THENL
      [ REWRITE_TAC[SUB_LIST_CLAUSES]; ALL_TAC] THEN
      REWRITE_TAC[CONJUNCT1 APPEND] THEN
      SUBGOAL_THEN `APPEND (SUB_LIST (0x0,val (tail_len:int64)) (int128_to_bytes PP))
        (SUB_LIST (val tail_len,0x10 - val tail_len) (int128_to_bytes PP)) =
        (int128_to_bytes PP)` SUBST1_TAC THENL
      [ MP_TAC (ISPECL [`int128_to_bytes PP`; `val (tail_len:int64)`; `16 - val (tail_len:int64)`; `0`] (GSYM SUB_LIST_SPLIT)) THEN
        IMP_REWRITE_TAC[ADD_CLAUSES; ARITH_RULE `!x. x < 16 ==> x + 16 - x = 16`] THEN
        DISCH_TAC THEN
        IMP_REWRITE_TAC[SUB_LIST_LENGTH_IMPLIES; LENGTH_OF_INT128_TO_BYTES]
        ; ALL_TAC] THEN
      REWRITE_TAC[BYTES_TO_INT128_OF_INT128_TO_BYTES];

      REWRITE_TAC[VAL_WORD_0] THEN ARITH_TAC
    ];

    (* Subgoal 3: inductive step *)
    REPEAT STRIP_TAC THEN

    (* For non-overlapping and MAYCHANGE address reasoning *)
    SUBGOAL_THEN `curr_len + 16 + i < val (len:int64)` ASSUME_TAC THENL
    [ REWRITE_TAC[GSYM (ASSUME `acc_len num_5blocks_adjusted num_blocks_adjusted = curr_len`)] THEN
      MP_TAC (SPECL [`num_5blocks_adjusted:int64`; `num_blocks_adjusted:int64`] VALUE_OF_ACC_LEN) THEN
      REPEAT_N 3 (ANTS_TAC THENL [ASM_ARITH_TAC ORELSE ASM_SIMP_TAC[]; ALL_TAC]) THEN
      SIMP_TAC[] THEN DISCH_TAC THEN
      EXPAND_TAC "num_blocks_adjusted" THEN
      SIMP_TAC[ASSUME `~(val (tail_len:int64) = 0)`] THEN
      REWRITE_TAC[VAL_WORD_SUB; DIMINDEX_64] THEN
      MP_TAC (SPECL [`val (num_blocks:int64)`; `0x2 EXP 0x40`; `val ((word 0x10):int64)`]
        (ARITH_RULE `!a b c. c <= a ==> c <= b ==> a + b - c = (a - c) + b`)) THEN
      ANTS_TAC THENL [
        IMP_REWRITE_TAC[VAL_WORD; DIMINDEX_64; MOD_LT] THEN ASM_ARITH_TAC
        ; ALL_TAC] THEN
      ANTS_TAC THENL [ WORD_ARITH_TAC; ALL_TAC] THEN
      SIMP_TAC[] THEN DISCH_TAC THEN
      MP_TAC (SPECL [`1`; `0x2 EXP 0x40`; `val (num_blocks:int64) - val ((word 0x10):int64)`]
        (CONJUNCT1 (CONJUNCT2 (CONJUNCT2 MOD_MULT_ADD)))) THEN
      SIMP_TAC[ARITH_RULE `!x. 1 * x = x`] THEN DISCH_TAC THEN
      IMP_REWRITE_TAC[MOD_LT] THEN
      IMP_REWRITE_TAC[VAL_WORD; DIMINDEX_64; MOD_LT] THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      EXPAND_TAC "len" THEN
      IMP_REWRITE_TAC[VAL_WORD_ADD; DIMINDEX_64; MOD_LT] THEN
      UNDISCH_TAC `val (num_blocks:int64) <= val (len:int64)` THEN
      UNDISCH_TAC `~(val (num_blocks:int64) < 16)` THEN
      UNDISCH_TAC `val (num_blocks:int64) <= 0x2 EXP 0x18` THEN
      UNDISCH_TAC `i < val (tail_len:int64)` THEN
      UNDISCH_TAC `val (tail_len:int64) < 0x10` THEN
      ARITH_TAC
      ; ALL_TAC] THEN

    MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN
    EXISTS_TAC `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
        MAYCHANGE [X19; X20; X21; X22],,
        MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15],,
        MAYCHANGE [memory :> bytes8 (word_add pt_ptr (word (curr_len + 0x10 + i)))],,
        MAYCHANGE [memory :> bytes8 (word_add pt_ptr (word (curr_len + i)))]` THEN
    REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    CONJ_TAC THENL [
      REPEAT (GEN_REWRITE_TAC ONCE_DEPTH_CONV [GSYM SEQ_ASSOC] THEN
              MATCH_MP_TAC SUBSUMED_SEQ THEN REWRITE_TAC[SUBSUMED_REFL]) THEN
      ABBREV_TAC `vallen = val (len:int64)` THEN
      SUBSUMED_MAYCHANGE_TAC; ALL_TAC] THEN

    REWRITE_TAC[byte_list_at] THEN
    UNDISCH_THEN `val ((word curr_len):int64) = curr_len`
        (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th]) THEN
    ENSURES_INIT_TAC "s0" THEN

    SUBGOAL_THEN `val ((word (val (tail_len:int64) - i)):int64) = val tail_len - i` SUBST_ALL_TAC THENL
    [ IMP_REWRITE_TAC[VAL_WORD; DIMINDEX_64; MOD_LT] THEN
      UNDISCH_TAC `i < val (tail_len:int64)` THEN
      UNDISCH_TAC `val (tail_len:int64) < 0x10` THEN
      ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `val ((word (val (tail_len:int64) - (i + 0x1))):int64) = val tail_len - (i + 1)` SUBST_ALL_TAC THENL
    [ IMP_REWRITE_TAC[VAL_WORD; DIMINDEX_64; MOD_LT] THEN
      UNDISCH_TAC `i < val (tail_len:int64)` THEN
      UNDISCH_TAC `val (tail_len:int64) < 0x10` THEN
      ARITH_TAC; ALL_TAC] THEN

    SUBGOAL_THEN `word_sub ((word (i + 0x1)):int64) (word 0x1) = word i` ASSUME_TAC THENL
    [ REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_SUB; DIMINDEX_64] THEN
      MP_TAC (SPECL [`val ((word (i + 0x1)):int64)`; `0x2 EXP 0x40`; `val ((word 0x1):int64)`]
        (ARITH_RULE `!a b c. c <= a ==> c <= b ==> a + b - c = (a - c) + b`)) THEN
      ANTS_TAC THENL [
        IMP_REWRITE_TAC[VAL_WORD; DIMINDEX_64; MOD_LT] THEN ASM_ARITH_TAC
        ; ALL_TAC] THEN
      ANTS_TAC THENL [ WORD_ARITH_TAC; ALL_TAC] THEN
      SIMP_TAC[] THEN DISCH_TAC THEN
      MP_TAC (SPECL [`1`; `0x2 EXP 0x40`; `val ((word (i + 0x1)):int64) - val ((word 0x1):int64)`]
        (CONJUNCT1 (CONJUNCT2 (CONJUNCT2 MOD_MULT_ADD)))) THEN
      SIMP_TAC[ARITH_RULE `!x. 1 * x = x`] THEN DISCH_TAC THEN
      IMP_REWRITE_TAC[MOD_LT] THEN
      CONJ_TAC THENL
      [ SUBGOAL_THEN `i + 1 < 2 EXP 64` MP_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
        IMP_REWRITE_TAC[VAL_WORD; DIMINDEX_64; MOD_LT] THEN
        ARITH_TAC;
        UNDISCH_TAC `i < val (tail_len:int64)` THEN
        UNDISCH_TAC `val (tail_len:int64) < 0x10` THEN
        WORD_ARITH_TAC]
      ; ALL_TAC] THEN

    MP_TAC (SPECL [`(word_add pt_ptr (word curr_len)):int64`; `word i:int64`; `s0:armstate`;
      `(cipher_stealing_inv (i + 0x1) curr_len (val (tail_len:int64)) PP ct):int128`]
      SELECT_ONE_BYTE_FROM_BLOCK) THEN

    SUBGOAL_THEN `val ((word i):int64) < 0x10` ASSUME_TAC THENL
    [ UNDISCH_TAC `i < val (tail_len:int64)` THEN
      UNDISCH_TAC `val (tail_len:int64) < 0x10` THEN
      WORD_ARITH_TAC; ALL_TAC ] THEN
    ASM_SIMP_TAC[] THEN
    REPEAT STRIP_TAC THEN

    MP_TAC (SPECL [`ct_ptr:int64`; `len:int64`;
      `(word_add (word (curr_len + 0x10)) (word i)):int64`;
      `ct:byte list`; `s0:armstate`] SELECT_ONE_BYTE_FROM_FORALL) THEN
    SUBGOAL_THEN `val (word_add ((word (curr_len + 0x10)):int64) (word i)) < val (len:int64)` ASSUME_TAC THENL
    [ REWRITE_TAC[WORD_RULE `!a b. word_add ((word a):int64) (word b) = word (a + b)`] THEN
      IMP_REWRITE_TAC[VAL_WORD; DIMINDEX_64; MOD_LT] THEN
      ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN
    STRIP_TAC THEN

    (* Break the `read (memory :> bytes128 (word_add pt_ptr (word curr_len))) s0
      into bytes using BREAK_ONE_BLOCK_INTO_BYTES *)
    MP_TAC (SPECL [`(word_add pt_ptr (word curr_len)):int64`; `s0:armstate`;
      `(cipher_stealing_inv (i + 0x1) curr_len (val (tail_len:int64)) PP ct):int128`]
      BREAK_ONE_BLOCK_INTO_BYTES) THEN
    ASM_SIMP_TAC[] THEN REPEAT STRIP_TAC THEN

    (* For address matching when symbolic simulation *)
    SUBGOAL_THEN `word_add (ct_ptr:int64) (word_add (word (curr_len + 0x10)) (word i)) =
      word_add ct_ptr (word (curr_len + 16 + i))` SUBST_ALL_TAC THENL
    [ REWRITE_TAC[WORD_RULE `!a b. word_add ((word a):int64) (word b) = word (a + b)`; ADD_ASSOC]
    ; ALL_TAC] THEN
    SUBGOAL_THEN `!x. word_add (word_add (pt_ptr:int64) (word curr_len)) (word x) =
      word_add pt_ptr (word (curr_len + x))` ASSUME_TAC THENL
    [ GEN_TAC THEN REWRITE_TAC[
        WORD_RULE `!(a:int64) b c. word_add (word_add a b) c = word_add a (word_add b c)`;
        WORD_RULE `!a b. word_add ((word a):int64) (word b) = word (a + b)`]
      ; ALL_TAC] THEN
    POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN

    (* case analysis based on i = 0 ... 14, because symbolic execution
       needs to know which byte is being overwritten in pt_ptr to properly update the state. *)
    MAP_EVERY (fun i -> TAIL_SWAP_ASM_CASES_TAC (mk_numeral (num i))) (0--14) THEN
    UNDISCH_TAC `15 <= i` THEN
    UNDISCH_TAC `i < val (tail_len:int64)` THEN
    UNDISCH_TAC `val (tail_len:int64) < 16` THEN
    ARITH_TAC;

    (* Subgoal 4: *)
    REPEAT STRIP_TAC THEN
    REWRITE_TAC[byte_list_at] THEN
    ENSURES_INIT_TAC "s0" THEN
    ARM_ACCSTEPS_TAC AES_XTS_DECRYPT_EXEC [] (1--1) THEN
    SUBGOAL_THEN `ival ((word i):int64) < &0x0 <=>
        ~(ival ((word (i + 0x1)):int64) - &0x1 = ival ((word i):int64))` ASSUME_TAC THENL
    [ SUBGOAL_THEN `ival ((word i):int64) = &i` ASSUME_TAC THENL
      [ MATCH_MP_TAC IVAL_WORD_LT THEN
        UNDISCH_TAC `i < val (tail_len:int64)` THEN
        UNDISCH_TAC `val (tail_len:int64) < 0x10` THEN
        ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `ival ((word (i + 0x1)):int64) = &(i + 1)` ASSUME_TAC THENL
      [ MATCH_MP_TAC IVAL_WORD_LT THEN
        UNDISCH_TAC `i < val (tail_len:int64)` THEN
        UNDISCH_TAC `val (tail_len:int64) < 0x10` THEN
        ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      ARITH_TAC; ALL_TAC] THEN
    POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_SIMP_TAC[];

    (* Subgoal 5: *)
    REPEAT STRIP_TAC THEN
    REWRITE_TAC[byte_list_at] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[cipher_stealing_inv; CONJUNCT1 SUB_LIST; CONJUNCT1 APPEND] THEN
    REWRITE_TAC[SUB_0] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `val ((word (val (tail_len:int64))):int64) = val tail_len` SUBST1_TAC THENL
    [ IMP_REWRITE_TAC[VAL_WORD; DIMINDEX_64; MOD_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(SUB_LIST (0x0,val (tail_len:int64)) (SUB_LIST (curr_len + 16,val tail_len) (ct:byte list))) =
      (SUB_LIST (curr_len + 16,val tail_len) ct)` SUBST1_TAC THENL
    [ IMP_REWRITE_TAC[SUB_LIST_REFL] THEN
      ASM_REWRITE_TAC[LENGTH_SUB_LIST; MIN] THEN
      ASM_ARITH_TAC; ALL_TAC] THEN

    MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN
    EXISTS_TAC `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
        MAYCHANGE [X19; X20; X21; X22],,
        MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15],,
        MAYCHANGE [memory :> bytes128 (word_add pt_ptr (word curr_len))]` THEN
    REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    CONJ_TAC THENL [
      REPEAT (GEN_REWRITE_TAC ONCE_DEPTH_CONV [GSYM SEQ_ASSOC] THEN
              MATCH_MP_TAC SUBSUMED_SEQ THEN REWRITE_TAC[SUBSUMED_REFL]) THEN
      ABBREV_TAC `vallen = val (len:int64)` THEN
      SUBSUMED_MAYCHANGE_TAC; ALL_TAC] THEN

    ENSURES_INIT_TAC "s0" THEN

    ARM_ACCSTEPS_TAC AES_XTS_DECRYPT_EXEC [] (1--32) THEN
    ABBREV_TAC `combinedPP = bytes_to_int128
                  (APPEND (SUB_LIST (curr_len + 16,val (tail_len:int64)) (ct:byte list))
                  (SUB_LIST (val tail_len,0x10 - val tail_len)
                  (int128_to_bytes (PP:int128))))` THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `aes256_xts_decrypt_round combinedPP
      (calculate_tweak curr_blocks iv key2) key1` o  MATCH_MP (MESON[]
      `read (Q26:(armstate,int128)component) (s:armstate) = a ==> !a'. a = a' ==> read Q26 s = a'`)) THEN
    ANTS_TAC THENL
    [ EXPAND_TAC "key1" THEN
      CONV_TAC (RAND_CONV (
        REWRITE_CONV [aes256_xts_decrypt_round] THENC
        DEPTH_CONV let_CONV)) THEN
      AESDEC_TAC; DISCH_TAC ] THEN
    ARM_ACCSTEPS_TAC AES_XTS_DECRYPT_EXEC [] (33--33) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_SIMP_TAC[] THEN

    UNDISCH_THEN `curr_len + 16 + val (tail_len:int64) = val (len:int64)`
      (fun th -> SUBST1_TAC (GSYM th)) THEN
    SUBGOAL_THEN `curr_len = 16 * curr_blocks` SUBST_ALL_TAC THENL
    [ REWRITE_TAC[GSYM (ASSUME `acc_len num_5blocks_adjusted num_blocks_adjusted = curr_len`)] THEN
      EXPAND_TAC "curr_blocks" THEN
      REWRITE_TAC[acc_len; acc_blocks] THEN
      COND_CASES_TAC THENL [SIMP_TAC[] THEN ARITH_TAC; ALL_TAC] THEN SIMP_TAC[] THEN
      COND_CASES_TAC THENL [SIMP_TAC[] THEN ARITH_TAC; ALL_TAC] THEN SIMP_TAC[] THEN
      COND_CASES_TAC THENL [SIMP_TAC[] THEN ARITH_TAC; ALL_TAC] THEN SIMP_TAC[] THEN
      COND_CASES_TAC THENL [SIMP_TAC[] THEN ARITH_TAC; ALL_TAC] THEN SIMP_TAC[] THEN
      ARITH_TAC; ALL_TAC] THEN

    MATCH_MP_TAC BREAK_DATA_INTO_PARTS_DECRYPT THEN
    REPEAT CONJ_TAC THENL
    [
      (* 0. Trivial *)
      IMP_REWRITE_TAC[LENGTH_OF_AES256_XTS_DECRYPT] THEN ARITH_TAC;

      (* 1. Result correct up to curr_len *)
      UNDISCH_TAC `forall i.
        i < 16 * curr_blocks
        ==> read (memory :> bytes8 (word_add (pt_ptr:int64) (word i))) s33 =
            EL i (aes256_xts_decrypt (ct:byte list) (16 * curr_blocks) (iv:int128)
              (key1:int128 list) (key2:int128 list))` THEN
      MP_TAC (SPECL [`16 * curr_blocks:num`; `pt_ptr:int64`;
        `(aes256_xts_decrypt ct (16 * curr_blocks + 0x10 + val (tail_len:int64)) iv key1 key2):byte list`;
        `s33:armstate`] BYTE_LIST_TO_NUM_THM) THEN
      ANTS_TAC THENL[
        IMP_REWRITE_TAC[LENGTH_OF_AES256_XTS_DECRYPT] THEN
        ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN (fun th -> REWRITE_TAC[th]) THEN
      MP_TAC (SPECL [`16 * curr_blocks:num`; `pt_ptr:int64`;
        `(aes256_xts_decrypt ct (16 * curr_blocks) iv key1 key2):byte list`;
        `s33:armstate`] BYTE_LIST_TO_NUM_THM) THEN
      ANTS_TAC THENL[
        REWRITE_TAC[LENGTH_OF_AES256_XTS_DECRYPT_FULL_BLOCKS] THEN
        ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN (fun th -> REWRITE_TAC[th]) THEN

      DISCH_THEN (fun th -> REWRITE_TAC[th]) THEN
      AP_TERM_TAC THEN
      MP_TAC (SPECL [`curr_blocks:num`; `ct:byte list`; `iv:int128`;
        `key1:int128 list`; `key2:int128 list`] LENGTH_OF_AES256_XTS_DECRYPT_FULL_BLOCKS) THEN
      REWRITE_TAC[ADD_0] THEN DISCH_TAC THEN
      IMP_REWRITE_TAC[SUB_LIST_OF_AES256_XTS_DECRYPT] THEN
      IMP_REWRITE_TAC[SUB_LIST_LENGTH_IMPLIES];

      (* 2. Last full block is correct *)
      MP_TAC (SPECL [`16:num`; `(word_add pt_ptr (word (0x10 * curr_blocks))):int64`;
        `(SUB_LIST (0x10 * curr_blocks,0x10 + val (tail_len:int64))
            (aes256_xts_decrypt ct (0x10 * curr_blocks + 0x10 + val tail_len)
            iv key1 key2)):byte list`;
        `s33:armstate`] BYTE_LIST_TO_NUM_THM) THEN
      ANTS_TAC THENL[
        REWRITE_TAC[LENGTH_SUB_LIST] THEN
        IMP_REWRITE_TAC[LENGTH_OF_AES256_XTS_DECRYPT] THEN
        ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN (fun th -> REWRITE_TAC[th]) THEN

      (* Proving last full block correct *)
      REWRITE_TAC[READ_MEMORY_BYTES_BYTES128] THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUB_LIST_MIN_RIGHT; MIN] THEN
      SIMP_TAC[ARITH_RULE `!x. 0x10 <= 0x10 + x`] THEN
      REWRITE_TAC[aes256_xts_decrypt] THEN
      SIMP_TAC[ARITH_RULE `!x y. ~(x + 16 + y < 16)`] THEN
      REWRITE_TAC[ARITH_RULE `0x10 * curr_blocks + 0x10 + val tail_len =
                      0x10 * (curr_blocks + 1) + val tail_len`] THEN
      REWRITE_TAC[MOD_MULT_ADD] THEN
      ASM_SIMP_TAC[MOD_LT] THEN
      REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
      REWRITE_TAC[ARITH_RULE
        `((0x10 * (curr_blocks + 0x1) + val tail_len) - val tail_len) DIV 0x10 =
         (0x10 * (curr_blocks + 0x1)) DIV 0x10`] THEN
      IMP_REWRITE_TAC[DIV_MULT; ARITH_RULE `~(16 = 0)`] THEN
      COND_CASES_TAC THENL
      [
        SUBGOAL_THEN `curr_blocks = 0` SUBST_ALL_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
        EXPAND_TAC "combinedPP" THEN
        REWRITE_TAC[aes256_xts_decrypt_tail] THEN
        ASM_SIMP_TAC[LET_DEF; LET_END_DEF] THEN
        CONV_TAC NUM_REDUCE_CONV THEN

        MP_TAC (SPECL [`(SUB_LIST (0,0x10) ct):byte list`;
          `(SUB_LIST (0x10,val (tail_len:int64)) ct):byte list`;
          `val (tail_len:int64)`; `iv:int128`; `0:num`; `key1:int128 list`;
          `key2:int128 list`] LENGTH_OF_FST_OF_CIPHER_STEALING) THEN
        DISCH_TAC THEN
        IMP_REWRITE_TAC[SUB_LIST_APPEND_LEFT; ARITH_RULE `16 <= 16`] THEN

        REWRITE_TAC[cipher_stealing; LET_DEF; LET_END_DEF] THEN
        REWRITE_TAC[SUB_LIST_OF_INT128_TO_BYTES;
          NUM_OF_BYTELIST_OF_INT128_TO_BYTES; CALCULATE_TWEAK_EXPAND] THEN
        EXPAND_TAC "combinedPP" THEN
        EXPAND_TAC "PP" THEN
        CONV_TAC NUM_REDUCE_CONV;
        ALL_TAC
      ] THEN

      SUBGOAL_THEN `curr_blocks >= 1` ASSUME_TAC THENL
      [ UNDISCH_TAC `~(curr_blocks + 0x1 < 0x2)` THEN ARITH_TAC; ALL_TAC] THEN

      IMP_REWRITE_TAC[ADD_SUB; ARITH_RULE `((curr_blocks + 0x1) - 0x2) = curr_blocks - 1`] THEN

      MP_TAC (SPECL [`0:num`; `(curr_blocks - 1):num`; `ct:byte list`; `iv:int128`;
        `key1:int128 list`; `key2:int128 list`] LENGTH_OF_AES256_XTS_DECRYPT_REC) THEN
      ASM_SIMP_TAC[ARITH_RULE `curr_blocks >= 1 ==> ~(curr_blocks - 1 < 0)`] THEN
      IMP_REWRITE_TAC[SUB_0; ARITH_RULE `curr_blocks >= 1 ==> curr_blocks - 1 + 1 = curr_blocks`] THEN
      ONCE_REWRITE_TAC[ARITH_RULE `curr_blocks * 16 = 16 * curr_blocks`] THEN
      DISCH_TAC THEN
      IMP_REWRITE_TAC[SUB_LIST_APPEND_RIGHT_LEMMA] THEN

      REWRITE_TAC[aes256_xts_decrypt_tail] THEN
      ASM_SIMP_TAC[LET_DEF; LET_END_DEF] THEN

      MP_TAC (SPECL [`(SUB_LIST (curr_blocks * 0x10,0x10) ct):byte list`;
        `(SUB_LIST ((curr_blocks + 0x1) * 0x10,val (tail_len:int64)) ct):byte list`;
        `val (tail_len:int64)`; `iv:int128`; `curr_blocks:num`; `key1:int128 list`;
        `key2:int128 list`] LENGTH_OF_FST_OF_CIPHER_STEALING) THEN
      DISCH_TAC THEN
      IMP_REWRITE_TAC[SUB_LIST_APPEND_LEFT; ARITH_RULE `16 <= 16`] THEN

      REWRITE_TAC[cipher_stealing; LET_DEF; LET_END_DEF] THEN
      REWRITE_TAC[SUB_LIST_OF_INT128_TO_BYTES;
        NUM_OF_BYTELIST_OF_INT128_TO_BYTES; CALCULATE_TWEAK_EXPAND;
        ARITH_RULE `curr_blocks * 16 = 16 * curr_blocks`;
        ARITH_RULE `0x10 * (curr_blocks + 0x1) = 16 * curr_blocks + 16`] THEN
      EXPAND_TAC "combinedPP" THEN
      EXPAND_TAC "PP" THEN
      REFL_TAC;

      (* 3. Proving tail is correct *)
      UNDISCH_TAC
        `forall i. i < val (tail_len:int64)
        ==> read (memory :> bytes8
            (word_add (word_add pt_ptr (word (0x10 * curr_blocks + 0x10)))
            (word i))) s33 =
            EL i (SUB_LIST (0x0,val tail_len) (int128_to_bytes PP))` THEN
      MP_TAC (SPECL [`val (tail_len:int64):num`; `(word_add pt_ptr (word (0x10 * curr_blocks + 0x10))):int64`;
        `(SUB_LIST (0x0,val (tail_len:int64)) (int128_to_bytes PP)):byte list`;
        `s33:armstate`] BYTE_LIST_TO_NUM_THM) THEN
      ANTS_TAC THENL[
        REWRITE_TAC[LENGTH_SUB_LIST; LENGTH_OF_INT128_TO_BYTES] THEN
        CONV_TAC NUM_REDUCE_CONV THEN
        UNDISCH_TAC `val (tail_len:int64) < 0x10` THEN
        ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN (fun th -> REWRITE_TAC[th]) THEN
      MP_TAC (SPECL [`val (tail_len:int64):num`; `(word_add pt_ptr (word (0x10 * curr_blocks + 0x10))):int64`;
        `(SUB_LIST (0x10 * curr_blocks + 0x10,val (tail_len:int64))
            (aes256_xts_decrypt ct (0x10 * curr_blocks + 0x10 + val tail_len) iv key1 key2)):byte list`;
        `s33:armstate`] BYTE_LIST_TO_NUM_THM) THEN
      ANTS_TAC THENL[
        REWRITE_TAC[LENGTH_SUB_LIST] THEN
        IMP_REWRITE_TAC[LENGTH_OF_AES256_XTS_DECRYPT] THEN
        ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN (fun th -> REWRITE_TAC[th]) THEN

      DISCH_THEN (fun th -> REWRITE_TAC[th]) THEN
      AP_TERM_TAC THEN
      REWRITE_TAC[SUB_LIST_IDEMPOTENT] THEN
      REWRITE_TAC[SUB_LIST_MIN_RIGHT; MIN; LE_REFL] THEN

      REWRITE_TAC[aes256_xts_decrypt;
        ARITH_RULE `~(0x10 * curr_blocks + 0x10 + val (tail_len:int64) < 0x10)`] THEN
      REWRITE_TAC[ARITH_RULE `0x10 * curr_blocks + 0x10 + val tail_len =
                      0x10 * (curr_blocks + 1) + val tail_len`] THEN
      REWRITE_TAC[MOD_MULT_ADD] THEN
      ASM_SIMP_TAC[MOD_LT] THEN
      REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
      REWRITE_TAC[ARITH_RULE
        `((0x10 * (curr_blocks + 0x1) + val tail_len) - val tail_len) DIV 0x10 =
        (0x10 * (curr_blocks + 0x1)) DIV 0x10`] THEN
      IMP_REWRITE_TAC[DIV_MULT; ARITH_RULE `~(16 = 0)`] THEN
      COND_CASES_TAC THENL
      [
        SUBGOAL_THEN `curr_blocks = 0` SUBST_ALL_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
        REWRITE_TAC[aes256_xts_decrypt_tail] THEN
        ASM_SIMP_TAC[LET_DEF; LET_END_DEF] THEN
        CONV_TAC NUM_REDUCE_CONV THEN

        MP_TAC (SPECL [`(SUB_LIST (0,0x10) ct):byte list`;
          `(SUB_LIST (0x10,val (tail_len:int64)) ct):byte list`;
          `val (tail_len:int64)`; `iv:int128`; `0:num`; `key1:int128 list`;
          `key2:int128 list`] LENGTH_OF_FST_OF_CIPHER_STEALING) THEN
        DISCH_TAC THEN
        IMP_REWRITE_TAC[SUB_LIST_APPEND_RIGHT_LEMMA; ARITH_RULE `16 <= 16`] THEN

        REWRITE_TAC[cipher_stealing; LET_DEF; LET_END_DEF; SUB_LIST_IDEMPOTENT] THEN
        EXPAND_TAC "PP" THEN
        REWRITE_TAC[CALCULATE_TWEAK_EXPAND] THEN
        CONV_TAC NUM_REDUCE_CONV;
        ALL_TAC
      ] THEN

      SUBGOAL_THEN `curr_blocks >= 1` ASSUME_TAC THENL
      [ UNDISCH_TAC `~(curr_blocks + 0x1 < 0x2)` THEN ARITH_TAC; ALL_TAC] THEN

      IMP_REWRITE_TAC[ADD_SUB; ARITH_RULE `((curr_blocks + 0x1) - 0x2) = curr_blocks - 1`] THEN

      MP_TAC (ISPECL [`(aes256_xts_decrypt_rec 0x0 (curr_blocks - 0x1) ct iv key1 key2):byte list`;
        `(aes256_xts_decrypt_tail curr_blocks (val (tail_len:int64)) ct iv key1 key2):byte list`;
        `0x10 * curr_blocks + 0x10:num`; `val (tail_len:int64)`; `0x10 * curr_blocks:num`
        ] SUB_LIST_APPEND_RIGHT_GENERAL) THEN
      ANTS_TAC THENL
      [ REWRITE_TAC[LENGTH_OF_AES256_XTS_DECRYPT_REC] THEN
        UNDISCH_TAC `curr_blocks >= 1` THEN
        ARITH_TAC; ALL_TAC] THEN
      ANTS_TAC THENL [ ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN (fun th -> REWRITE_TAC[th]) THEN

      REWRITE_TAC[ARITH_RULE `(0x10 * curr_blocks + 0x10) - 0x10 * curr_blocks = 0x10`] THEN
      REWRITE_TAC[aes256_xts_decrypt_tail] THEN
      ASM_SIMP_TAC[LET_DEF; LET_END_DEF] THEN

      MP_TAC (SPECL [`(SUB_LIST (curr_blocks * 0x10,0x10) ct):byte list`;
        `(SUB_LIST ((curr_blocks + 0x1) * 0x10,val (tail_len:int64)) ct):byte list`;
        `val (tail_len:int64)`; `iv:int128`; `curr_blocks:num`; `key1:int128 list`;
        `key2:int128 list`] LENGTH_OF_FST_OF_CIPHER_STEALING) THEN
      DISCH_TAC THEN
      IMP_REWRITE_TAC[SUB_LIST_APPEND_RIGHT_LEMMA; ARITH_RULE `16 <= 16`] THEN

      REWRITE_TAC[cipher_stealing; LET_DEF; LET_END_DEF; SUB_LIST_IDEMPOTENT] THEN
      EXPAND_TAC "PP" THEN
      REWRITE_TAC[ARITH_RULE `curr_blocks * 0x10 = 0x10 * curr_blocks`;
        CALCULATE_TWEAK_EXPAND]
      ]
  ]
);;

(* Proof: Less than 2 blocks *)
let AES_XTS_DECRYPT_LT_2BLOCK_CORRECT = time prove(
  `!ct_ptr pt_ptr ct key1_ptr key2_ptr iv_ptr iv len
    k00 k01 k02 k03 k04 k05 k06 k07 k08 k09 k0a k0b k0c k0d k0e
    k10 k11 k12 k13 k14 k15 k16 k17 k18 k19 k1a k1b k1c k1d k1e
    pc.
    nonoverlapping (word pc, LENGTH aes_xts_decrypt_mc) (pt_ptr, val len)
    /\ nonoverlapping (ct_ptr, val len) (pt_ptr, val len)
    /\ nonoverlapping (key1_ptr, 260) (pt_ptr, val len)
    /\ val len >= 16 /\ val len < 0x20 /\ LENGTH ct = val len
    /\ [k00; k01; k02; k03; k04; k05; k06; k07; k08; k09; k0a; k0b; k0c; k0d; k0e] = key1
    /\ [k10; k11; k12; k13; k14; k15; k16; k17; k18; k19; k1a; k1b; k1c; k1d; k1e] = key2
    ==> ensures arm
    (\s. aligned_bytes_loaded s (word pc) aes_xts_decrypt_mc /\
         read PC s = word (pc + 0x1c) /\
         C_ARGUMENTS [ct_ptr; pt_ptr; len; key1_ptr; key2_ptr; iv_ptr] s /\
         byte_list_at ct ct_ptr len s /\
         read(memory :> bytes128 iv_ptr) s = iv /\
         set_key_schedule s key1_ptr k00 k01 k02 k03 k04 k05 k06 k07 k08 k09 k0a k0b k0c k0d k0e /\
         set_key_schedule s key2_ptr k10 k11 k12 k13 k14 k15 k16 k17 k18 k19 k1a k1b k1c k1d k1e)
    (\s. read PC s = word (pc + 0xb58) /\
         byte_list_at (aes256_xts_decrypt ct (val len) iv key1 key2) pt_ptr len s
         )
    (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI,,
     MAYCHANGE [X19; X20; X21; X22],,
     MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15],,
     MAYCHANGE [memory :> bytes(pt_ptr, val len)])
    `,
  REWRITE_TAC [(REWRITE_CONV [aes_xts_decrypt_mc] THENC LENGTH_CONV) `LENGTH aes_xts_decrypt_mc`] THEN
  REWRITE_TAC[set_key_schedule; C_ARGUMENTS; SOME_FLAGS;
    NONOVERLAPPING_CLAUSES; byte_list_at;
    MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REPEAT STRIP_TAC THEN

  SUBGOAL_THEN `word_add (word_and len (word 0xf))
    (word_and len (word 0xfffffffffffffff0)) = len:int64` ASSUME_TAC THENL
  [REWRITE_TAC[word_split_lemma]; ALL_TAC] THEN
  ABBREV_TAC `num_blocks:int64 = word_and len (word 0xfffffffffffffff0)` THEN
  ABBREV_TAC `tail_len:int64 = word_and len (word 0xf)` THEN
  ABBREV_TAC `num_blocks_adjusted = if val (tail_len:int64) = 0
        then num_blocks else word_sub (num_blocks:int64) (word 0x10)` THEN
  ABBREV_TAC `num_5blocks_adjusted = (word (val (num_blocks_adjusted:int64) DIV 0x50)):int64` THEN

  SUBGOAL_THEN `val (num_blocks:int64) = 16` ASSUME_TAC THENL
  [ EXPAND_TAC "num_blocks" THEN
    REWRITE_TAC[NUM_BLOCKS_TO_VAL] THEN
    IMP_REWRITE_TAC[VAL_WORD; DIMINDEX_64; MOD_LT] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    SUBGOAL_THEN `val (len:int64) DIV 16 = 1` SUBST1_TAC THENL
    [ MATCH_MP_TAC(MESON[LE_ANTISYM] `m <= n /\ n <= m ==> m = n`) THEN
      CONJ_TAC THENL [ ASM_ARITH_TAC; ASM_ARITH_TAC];
      ALL_TAC] THEN
    ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `val (num_blocks_adjusted:int64) < 0x20` ASSUME_TAC THENL
  [ EXPAND_TAC "num_blocks_adjusted" THEN
    COND_CASES_TAC THENL[
      ASM_ARITH_TAC;
      UNDISCH_TAC `val (num_blocks:int64) = 0x10` THEN
      WORD_ARITH_TAC]
     ; ALL_TAC] THEN

  (* Prove property until start of cipher stealing. *)
  ENSURES_SEQUENCE_TAC `pc + 0xa0c`
  `\s.
    read X0 s = word_add ct_ptr (word (acc_len num_5blocks_adjusted num_blocks_adjusted)) /\
    read X1 s = word_add pt_ptr (word (acc_len num_5blocks_adjusted num_blocks_adjusted)) /\
    read X3 s = key1_ptr /\
    read X21 s = tail_len /\
    read Q6 s = calculate_tweak (acc_blocks num_5blocks_adjusted num_blocks_adjusted T) iv key2 /\
    read X19 s = word 0x87 /\
    read Q16 s = k00 /\ read Q17 s = k01 /\ read Q12 s = k02 /\ read Q13 s = k03 /\
    read Q14 s = k04 /\ read Q15 s = k05 /\ read Q4 s = k06 /\ read Q5 s = k07 /\
    read Q18 s = k08 /\ read Q19 s = k09 /\ read Q20 s = k0a /\ read Q21 s = k0b /\
    read Q22 s = k0c /\ read Q23 s = k0d /\ read Q7 s = k0e /\
    byte_list_at ct ct_ptr len s /\
    byte_list_at (aes256_xts_decrypt ct (acc_len num_5blocks_adjusted num_blocks_adjusted) iv key1 key2)
      pt_ptr (word (acc_len num_5blocks_adjusted num_blocks_adjusted)) s` THEN
  CONJ_TAC THENL
  [
    MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN
    EXISTS_TAC `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
      MAYCHANGE [X19; X20; X21; X22],,
      MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15],,
      MAYCHANGE [memory :> bytes128 pt_ptr]` THEN
    REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    CONJ_TAC THENL [
    REPEAT (GEN_REWRITE_TAC ONCE_DEPTH_CONV [GSYM SEQ_ASSOC] THEN
            MATCH_MP_TAC SUBSUMED_SEQ THEN REWRITE_TAC[SUBSUMED_REFL]) THEN
    ABBREV_TAC `vallen = val (len:int64)` THEN
    SUBSUMED_MAYCHANGE_TAC; ALL_TAC] THEN

    REWRITE_TAC[byte_list_at] THEN
    ENSURES_INIT_TAC "s0" THEN
    ARM_ACCSTEPS_TAC AES_XTS_DECRYPT_EXEC [] (1--2) THEN

    (* Discharge if condition *)
    SUBGOAL_THEN
      `ival (word_sub (len:int64) (word 0x10)) < &0x0
      <=> ~(ival (len:int64) - &0x10 = ival (word_sub (len:int64) (word 0x10)))` MP_TAC THENL
    [ MP_TAC (BITBLAST_RULE
        `val (len:int64)  >= 0x10 ==> val len < 0x20 ==>
        ival (word_sub len (word 0x10)) >= &0x0`) THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC (BITBLAST_RULE
        `val (len:int64)  >= 0x10 ==> val len < 0x20 ==>
         ival (len:int64) - &0x10 = ival (word_sub len (word 0x10))`) THEN
      ASM_REWRITE_TAC[] THEN
      ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN

    MP_TAC (SPECL [`ct_ptr:int64`; `len:int64`; `ct:byte list`; `s2:armstate`] READ_LT_2BLOCK) THEN
    ASM_SIMP_TAC[] THEN DISCH_TAC THEN

    ARM_ACCSTEPS_TAC AES_XTS_DECRYPT_EXEC [] (3--69) THEN
    (* Prove Q6 stores initial tweak *)
    FIRST_X_ASSUM(MP_TAC o SPEC `(calculate_tweak 0 iv key2)`
      o  MATCH_MP (MESON[] `read Q6 s = a ==> !a'. a = a' ==> read Q6 s = a'`)) THEN
    ANTS_TAC THENL
    [ REWRITE_TAC[CONJUNCT1 calculate_tweak; xts_init_tweak] THEN
      EXPAND_TAC "key2" THEN AESENC_TAC; DISCH_TAC] THEN

    (* Simulating until branch for num_blocks adjustment *)
    ARM_ACCSTEPS_TAC AES_XTS_DECRYPT_EXEC [] (70--89) THEN

    (* Case split on whether there is a tail *)
    FIRST_X_ASSUM MP_TAC THEN
    COND_CASES_TAC THENL
    [
      DISCH_TAC THEN

      SUBGOAL_THEN `val (tail_len:int64) = 0` SUBST_ALL_TAC THENL
      [ UNDISCH_TAC `val (word_and (tail_len:int64) (word 0xf)) = 0x0` THEN
        MP_TAC (SPECL [`len:int64`; `tail_len:int64`] TAIL_LEN_BOUND_THM) THEN
        ASM_SIMP_TAC[] THEN DISCH_TAC THEN
        SUBGOAL_THEN `val (word_and (tail_len:int64) (word 15)) = val tail_len` SUBST1_TAC THENL
        [ REWRITE_TAC[VAL_WORD_AND_MASK_WORD; ARITH_RULE `15 = 2 EXP 4 - 1`] THEN
          CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
          IMP_REWRITE_TAC[MOD_LT];
          ALL_TAC] THEN
        SIMP_TAC[]; ALL_TAC] THEN
      CONV_TAC NUM_REDUCE_CONV THEN

      SUBGOAL_THEN `val (num_blocks_adjusted:int64) = 16` ASSUME_TAC THENL
      [ EXPAND_TAC "num_blocks_adjusted" THEN
        CONV_TAC NUM_REDUCE_CONV THEN
        ASM_REWRITE_TAC[]
        ; ALL_TAC ] THEN
      SUBGOAL_THEN `val (num_5blocks_adjusted:int64) = 0` ASSUME_TAC THENL
      [ EXPAND_TAC "num_5blocks_adjusted" THEN
        UNDISCH_TAC `val (num_blocks_adjusted:int64) = 16` THEN
        SIMP_TAC[] THEN DISCH_TAC THEN
        CONV_TAC NUM_REDUCE_CONV THEN
        REWRITE_TAC[VAL_WORD_0]
        ; ALL_TAC ] THEN

      TWEAK_TAC `Q8:(armstate,int128)component` `1:num` `0:num` THEN
      ARM_ACCSTEPS_TAC AES_XTS_DECRYPT_EXEC [] (90--126) THEN
      XTSDEC_TAC `Q0:(armstate,int128)component` `0` `0` THEN
      ARM_ACCSTEPS_TAC AES_XTS_DECRYPT_EXEC [] (127--136) THEN
      TWEAK_TAC `Q6:(armstate,int128)component` `1:num` `0:num` THEN

      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      REPEAT CONJ_TAC THENL
      [
        ASM_REWRITE_TAC[acc_len] THEN CONV_TAC NUM_REDUCE_CONV;
        ASM_REWRITE_TAC[acc_len] THEN CONV_TAC NUM_REDUCE_CONV;
        ASM_REWRITE_TAC[acc_blocks] THEN CONV_TAC NUM_REDUCE_CONV;

        ASM_REWRITE_TAC[acc_len] THEN
        CONV_TAC NUM_REDUCE_CONV THEN
        IMP_REWRITE_TAC[VAL_WORD; DIMINDEX_64; MOD_LT] THEN
        CONV_TAC NUM_REDUCE_CONV THEN
        MP_TAC (SPECL [`16:num`; `pt_ptr:int64`; `(aes256_xts_decrypt ct 16 iv key1 key2):byte list`; `s136:armstate`] BYTE_LIST_TO_NUM_THM) THEN
        ANTS_TAC THENL[
          MP_TAC (SPECL [`1`; `ct:byte list`; `iv:int128`;
            `key1:int128 list`; `key2:int128 list`] LENGTH_OF_AES256_XTS_DECRYPT_FULL_BLOCKS) THEN
          ARITH_TAC; ALL_TAC] THEN
        DISCH_THEN (fun th -> REWRITE_TAC[th]) THEN
        ASM_REWRITE_TAC[] THEN
        IMP_REWRITE_TAC[READ_BYTES_EQ_READ_BYTE128_1BLOCK]
      ]
    ; ALL_TAC] THEN

    (* There is a tail *)
    DISCH_TAC THEN
    (* Prove ~ tail_len = 0 *)
    SUBGOAL_THEN `~(val (tail_len:int64) = 0)` ASSUME_TAC THENL
    [ UNDISCH_TAC `~(val (word_and (tail_len:int64) (word 0xf)) = 0x0)` THEN
      MP_TAC (SPECL [`len:int64`; `tail_len:int64`] TAIL_LEN_BOUND_THM) THEN
      ASM_REWRITE_TAC[] THEN
      SUBST1_TAC(ARITH_RULE `0xf = 2 EXP 4 - 1`) THEN
      REWRITE_TAC[VAL_WORD_AND_MASK_WORD] THEN
      NUM_REDUCE_TAC THEN IMP_REWRITE_TAC[MOD_LT]
    ; ALL_TAC] THEN
    (* Prove num_blocks_adjusted = word_sub num_blocks (word 0x10) *)
    SUBGOAL_THEN `word_sub num_blocks (word 0x10) = num_blocks_adjusted:int64` ASSUME_TAC THENL
    [ UNDISCH_TAC `(if val (tail_len:int64) = 0x0
        then (num_blocks:int64)
        else word_sub num_blocks (word 0x10)) = num_blocks_adjusted` THEN
      ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `val (num_blocks_adjusted:int64) = 0` ASSUME_TAC THENL
    [ EXPAND_TAC "num_blocks_adjusted" THEN
      UNDISCH_TAC `val (num_blocks:int64) = 16` THEN
      WORD_ARITH_TAC
    ; ALL_TAC ] THEN
    SUBGOAL_THEN `val (num_5blocks_adjusted:int64) = 0` ASSUME_TAC THENL
    [ EXPAND_TAC "num_5blocks_adjusted" THEN
      REWRITE_TAC[ASSUME `val (num_blocks_adjusted:int64) = 0`] THEN
      WORD_ARITH_TAC
      ; ALL_TAC ] THEN

    TWEAK_TAC `Q8:(armstate,int128)component` `1:num` `0:num` THEN
    ARM_ACCSTEPS_TAC AES_XTS_DECRYPT_EXEC [] (90--92) THEN
    (* Discharge if condition *)
    SUBGOAL_THEN
      `~(ival (word_sub (num_blocks_adjusted:int64) (word 0x10)) < &0x0 <=>
      ~(ival (num_blocks_adjusted:int64) - &0x10 =
        ival (word_sub (num_blocks_adjusted:int64) (word 0x10))))` MP_TAC THENL
    [ SUBGOAL_THEN `num_blocks_adjusted:int64 = (word 0)` SUBST1_TAC THENL
      [ UNDISCH_TAC `val (num_blocks_adjusted:int64) = 0` THEN
        WORD_ARITH_TAC; ALL_TAC] THEN
      WORD_ARITH_TAC
      ; ALL_TAC] THEN
    DISCH_TAC THEN
    POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN

    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
    [
      ASM_REWRITE_TAC[acc_len] THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC[WORD_ADD_0];
      ASM_REWRITE_TAC[acc_len] THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC[WORD_ADD_0];
      ASM_REWRITE_TAC[acc_blocks] THEN CONV_TAC NUM_REDUCE_CONV;

      ASM_REWRITE_TAC[acc_len] THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      IMP_REWRITE_TAC[VAL_WORD; DIMINDEX_64; MOD_LT] THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      MESON_TAC[ARITH_RULE `~(i < 0)`]
    ]
  ; ALL_TAC] THEN

  (* Reuse the cipher stealing proof *)
  MP_TAC CIPHER_STEALING_CORRECT THEN
  REWRITE_TAC [(REWRITE_CONV [aes_xts_decrypt_mc] THENC LENGTH_CONV) `LENGTH aes_xts_decrypt_mc`] THEN
  REWRITE_TAC[set_key_schedule; C_ARGUMENTS; SOME_FLAGS;
    NONOVERLAPPING_CLAUSES; byte_list_at;
    MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  EXISTS_TAC `(word 16):int64` THEN
  ASM_SIMP_TAC[] THEN
  SUBGOAL_THEN `num_blocks:int64 = word 0x10` ASSUME_TAC THENL
  [ UNDISCH_TAC `val (num_blocks:int64) = 16` THEN
    WORD_ARITH_TAC; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL [
    ASM_ARITH_TAC;
    EXPAND_TAC "len" THEN AP_TERM_TAC THEN
    UNDISCH_TAC `val (num_blocks:int64) = 16` THEN
    WORD_ARITH_TAC;
    ASM_SIMP_TAC[];
    EXPAND_TAC "num_blocks_adjusted" THEN
    REWRITE_TAC[ASSUME `num_blocks:int64 = word 16`]
  ]
);;


(* Proof: less than 3 blocks *)
let AES_XTS_DECRYPT_LT_3BLOCK_CORRECT = time prove(
  `!ct_ptr pt_ptr ct key1_ptr key2_ptr iv_ptr iv len
    k00 k01 k02 k03 k04 k05 k06 k07 k08 k09 k0a k0b k0c k0d k0e
    k10 k11 k12 k13 k14 k15 k16 k17 k18 k19 k1a k1b k1c k1d k1e
    pc.
    nonoverlapping (word pc, LENGTH aes_xts_decrypt_mc) (pt_ptr, val len)
    /\ nonoverlapping (ct_ptr, val len) (pt_ptr, val len)
    /\ nonoverlapping (key1_ptr, 260) (pt_ptr, val len)
    /\ ~(val len < 0x20) /\ val len < 0x30 /\ LENGTH ct = val len
    /\ [k00; k01; k02; k03; k04; k05; k06; k07; k08; k09; k0a; k0b; k0c; k0d; k0e] = key1
    /\ [k10; k11; k12; k13; k14; k15; k16; k17; k18; k19; k1a; k1b; k1c; k1d; k1e] = key2
    ==> ensures arm
    (\s. aligned_bytes_loaded s (word pc) aes_xts_decrypt_mc /\
         read PC s = word (pc + 0x1c) /\
         C_ARGUMENTS [ct_ptr; pt_ptr; len; key1_ptr; key2_ptr; iv_ptr] s /\
         byte_list_at ct ct_ptr len s /\
         read(memory :> bytes128 iv_ptr) s = iv /\
         set_key_schedule s key1_ptr k00 k01 k02 k03 k04 k05 k06 k07 k08 k09 k0a k0b k0c k0d k0e /\
         set_key_schedule s key2_ptr k10 k11 k12 k13 k14 k15 k16 k17 k18 k19 k1a k1b k1c k1d k1e)
    (\s. read PC s = word (pc + 0xb58) /\
         byte_list_at (aes256_xts_decrypt ct (val len) iv key1 key2) pt_ptr len s
         )
    (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI,,
     MAYCHANGE [X19; X20; X21; X22],,
     MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15],,
     MAYCHANGE [memory :> bytes(pt_ptr, val len)])
    `,
  REWRITE_TAC [(REWRITE_CONV [aes_xts_decrypt_mc] THENC LENGTH_CONV) `LENGTH aes_xts_decrypt_mc`] THEN
  REWRITE_TAC[set_key_schedule; C_ARGUMENTS; SOME_FLAGS;
    NONOVERLAPPING_CLAUSES; byte_list_at;
    MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REPEAT STRIP_TAC THEN

  SUBGOAL_THEN `word_add (word_and len (word 0xf))
    (word_and len (word 0xfffffffffffffff0)) = len:int64` ASSUME_TAC THENL
  [REWRITE_TAC[word_split_lemma]; ALL_TAC] THEN
  ABBREV_TAC `num_blocks:int64 = word_and len (word 0xfffffffffffffff0)` THEN
  ABBREV_TAC `tail_len:int64 = word_and len (word 0xf)` THEN
  ABBREV_TAC `num_blocks_adjusted = if val (tail_len:int64) = 0
        then num_blocks else word_sub (num_blocks:int64) (word 0x10)` THEN
  ABBREV_TAC `num_5blocks_adjusted = (word (val (num_blocks_adjusted:int64) DIV 0x50)):int64` THEN

  SUBGOAL_THEN `val (num_blocks:int64) = 32` ASSUME_TAC THENL
  [ EXPAND_TAC "num_blocks" THEN
    REWRITE_TAC[NUM_BLOCKS_TO_VAL] THEN
    IMP_REWRITE_TAC[VAL_WORD; DIMINDEX_64; MOD_LT] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    SUBGOAL_THEN `val (len:int64) DIV 16 = 2` SUBST1_TAC THENL
    [ MATCH_MP_TAC(MESON[LE_ANTISYM] `m <= n /\ n <= m ==> m = n`) THEN
      CONJ_TAC THENL [ ASM_ARITH_TAC; ASM_ARITH_TAC];
      ALL_TAC] THEN
    ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `val (num_blocks_adjusted:int64) < 0x30` ASSUME_TAC THENL
  [ EXPAND_TAC "num_blocks_adjusted" THEN
    COND_CASES_TAC THENL[
      ASM_ARITH_TAC;
      UNDISCH_TAC `val (num_blocks:int64) = 0x20` THEN
      WORD_ARITH_TAC]
     ; ALL_TAC] THEN

  ENSURES_SEQUENCE_TAC `pc + 0xa0c`
  `\s.
    read X0 s = word_add ct_ptr (word (acc_len num_5blocks_adjusted num_blocks_adjusted)) /\
    read X1 s = word_add pt_ptr (word (acc_len num_5blocks_adjusted num_blocks_adjusted)) /\
    read X3 s = key1_ptr /\
    read X21 s = tail_len /\
    read Q6 s = calculate_tweak (acc_blocks num_5blocks_adjusted num_blocks_adjusted T) iv key2 /\
    read X19 s = word 0x87 /\
    read Q16 s = k00 /\ read Q17 s = k01 /\ read Q12 s = k02 /\ read Q13 s = k03 /\
    read Q14 s = k04 /\ read Q15 s = k05 /\ read Q4 s = k06 /\ read Q5 s = k07 /\
    read Q18 s = k08 /\ read Q19 s = k09 /\ read Q20 s = k0a /\ read Q21 s = k0b /\
    read Q22 s = k0c /\ read Q23 s = k0d /\ read Q7 s = k0e /\
    byte_list_at ct ct_ptr len s /\
    byte_list_at (aes256_xts_decrypt ct (acc_len num_5blocks_adjusted num_blocks_adjusted) iv key1 key2)
      pt_ptr (word (acc_len num_5blocks_adjusted num_blocks_adjusted)) s` THEN
  CONJ_TAC THENL
  [
    MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN
    EXISTS_TAC `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
      MAYCHANGE [X19; X20; X21; X22],,
      MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15],,
      MAYCHANGE [memory :> bytes128 pt_ptr; memory :> bytes128 (word_add pt_ptr (word 16))]` THEN
    REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    CONJ_TAC THENL [
    REPEAT (GEN_REWRITE_TAC ONCE_DEPTH_CONV [GSYM SEQ_ASSOC] THEN
            MATCH_MP_TAC SUBSUMED_SEQ THEN REWRITE_TAC[SUBSUMED_REFL]) THEN
    ABBREV_TAC `vallen = val (len:int64)` THEN
    SUBSUMED_MAYCHANGE_TAC; ALL_TAC] THEN

    REWRITE_TAC[byte_list_at] THEN
    ENSURES_INIT_TAC "s0" THEN
    ARM_ACCSTEPS_TAC AES_XTS_DECRYPT_EXEC [] (1--2) THEN

    (* Discharge if condition *)
    SUBGOAL_THEN
      `ival (word_sub (len:int64) (word 0x10)) < &0x0
      <=> ~(ival (len:int64) - &0x10 = ival (word_sub (len:int64) (word 0x10)))` MP_TAC THENL
    [ MP_TAC (BITBLAST_RULE
        `~(val (len:int64) < 0x20) ==> val len < 0x30 ==>
        ival (word_sub len (word 0x10)) >= &0x0`) THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC (BITBLAST_RULE
        `~(val (len:int64) < 0x20) ==> val len < 0x30 ==>
         ival (len:int64) - &0x10 = ival (word_sub len (word 0x10))`) THEN
      ASM_REWRITE_TAC[] THEN
      ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN

    MP_TAC (SPECL [`ct_ptr:int64`; `len:int64`; `ct:byte list`; `s2:armstate`] READ_LT_3BLOCK) THEN
    ASM_SIMP_TAC[] THEN REPEAT STRIP_TAC THEN

    ARM_ACCSTEPS_TAC AES_XTS_DECRYPT_EXEC [] (3--69) THEN
    (* Prove Q6 stores initial tweak *)
    FIRST_X_ASSUM(MP_TAC o SPEC `(calculate_tweak 0 iv key2)`
      o  MATCH_MP (MESON[] `read Q6 s = a ==> !a'. a = a' ==> read Q6 s = a'`)) THEN
    ANTS_TAC THENL
    [ REWRITE_TAC[CONJUNCT1 calculate_tweak; xts_init_tweak] THEN
      EXPAND_TAC "key2" THEN AESENC_TAC; DISCH_TAC] THEN

    (* Simulating until branch for num_blocks adjustment *)
    ARM_ACCSTEPS_TAC AES_XTS_DECRYPT_EXEC [] (70--89) THEN

    (* Case split on whether there is a tail *)
    FIRST_X_ASSUM MP_TAC THEN
    COND_CASES_TAC THENL
    [
      DISCH_TAC THEN

      SUBGOAL_THEN `val (tail_len:int64) = 0` SUBST_ALL_TAC THENL
      [ UNDISCH_TAC `val (word_and (tail_len:int64) (word 0xf)) = 0x0` THEN
        MP_TAC (SPECL [`len:int64`; `tail_len:int64`] TAIL_LEN_BOUND_THM) THEN
        ASM_SIMP_TAC[] THEN DISCH_TAC THEN
        SUBGOAL_THEN `val (word_and (tail_len:int64) (word 15)) = val tail_len` SUBST1_TAC THENL
        [ REWRITE_TAC[VAL_WORD_AND_MASK_WORD; ARITH_RULE `15 = 2 EXP 4 - 1`] THEN
          CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
          IMP_REWRITE_TAC[MOD_LT];
          ALL_TAC] THEN
        SIMP_TAC[]; ALL_TAC] THEN
      CONV_TAC NUM_REDUCE_CONV THEN

      SUBGOAL_THEN `val (num_blocks_adjusted:int64) = 0x20` ASSUME_TAC THENL
      [ EXPAND_TAC "num_blocks_adjusted" THEN
        CONV_TAC NUM_REDUCE_CONV THEN
        ASM_REWRITE_TAC[]
        ; ALL_TAC ] THEN
      SUBGOAL_THEN `val (num_5blocks_adjusted:int64) = 0` ASSUME_TAC THENL
      [ EXPAND_TAC "num_5blocks_adjusted" THEN
        UNDISCH_TAC `val (num_blocks_adjusted:int64) = 0x20` THEN
        SIMP_TAC[] THEN DISCH_TAC THEN
        CONV_TAC NUM_REDUCE_CONV THEN
        REWRITE_TAC[VAL_WORD_0]
        ; ALL_TAC ] THEN

      TWEAK_TAC `Q8:(armstate,int128)component` `1:num` `0:num` THEN
      ARM_ACCSTEPS_TAC AES_XTS_DECRYPT_EXEC [] (90--158) THEN
      XTSDEC_TAC `Q0:(armstate,int128)component` `0` `0` THEN
      XTSDEC_TAC `Q1:(armstate,int128)component` `0x10` `0x1` THEN
      ARM_ACCSTEPS_TAC AES_XTS_DECRYPT_EXEC [] (159--168) THEN
      TWEAK_TAC `Q6:(armstate,int128)component` `2:num` `1:num` THEN

      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      REPEAT CONJ_TAC THENL
      [
        ASM_REWRITE_TAC[acc_len] THEN CONV_TAC NUM_REDUCE_CONV;
        ASM_REWRITE_TAC[acc_len] THEN CONV_TAC NUM_REDUCE_CONV;
        ASM_REWRITE_TAC[acc_blocks] THEN CONV_TAC NUM_REDUCE_CONV;

        ASM_REWRITE_TAC[acc_len] THEN
        CONV_TAC NUM_REDUCE_CONV THEN
        IMP_REWRITE_TAC[VAL_WORD; DIMINDEX_64; MOD_LT] THEN
        CONV_TAC NUM_REDUCE_CONV THEN
        MP_TAC (SPECL [`0x20:num`; `pt_ptr:int64`; `(aes256_xts_decrypt ct 0x20 iv key1 key2):byte list`;
          `s168:armstate`] BYTE_LIST_TO_NUM_THM) THEN
        ANTS_TAC THENL[
          MP_TAC (SPECL [`2`; `ct:byte list`; `iv:int128`;
            `key1:int128 list`; `key2:int128 list`] LENGTH_OF_AES256_XTS_DECRYPT_FULL_BLOCKS) THEN
          ARITH_TAC; ALL_TAC] THEN
        DISCH_THEN (fun th -> REWRITE_TAC[th]) THEN
        IMP_REWRITE_TAC[READ_BYTES_EQ_READ_BYTE128_2BLOCKS]
      ]; ALL_TAC] THEN

    (* There is a tail *)
    DISCH_TAC THEN
    (* Prove ~ tail_len = 0 *)
    SUBGOAL_THEN `~(val (tail_len:int64) = 0)` ASSUME_TAC THENL
    [ UNDISCH_TAC `~(val (word_and (tail_len:int64) (word 0xf)) = 0x0)` THEN
      MP_TAC (SPECL [`len:int64`; `tail_len:int64`] TAIL_LEN_BOUND_THM) THEN
      ASM_REWRITE_TAC[] THEN
      SUBST1_TAC(ARITH_RULE `0xf = 2 EXP 4 - 1`) THEN
      REWRITE_TAC[VAL_WORD_AND_MASK_WORD] THEN
      NUM_REDUCE_TAC THEN IMP_REWRITE_TAC[MOD_LT]
    ; ALL_TAC] THEN
    (* Prove num_blocks_adjusted = word_sub num_blocks (word 0x10) *)
    SUBGOAL_THEN `word_sub num_blocks (word 0x10) = num_blocks_adjusted:int64` ASSUME_TAC THENL
    [ UNDISCH_TAC `(if val (tail_len:int64) = 0x0
        then (num_blocks:int64)
        else word_sub num_blocks (word 0x10)) = num_blocks_adjusted` THEN
      ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `val (num_blocks_adjusted:int64) = 0x10` ASSUME_TAC THENL
    [ EXPAND_TAC "num_blocks_adjusted" THEN
      UNDISCH_TAC `val (num_blocks:int64) = 0x20` THEN
      WORD_ARITH_TAC
    ; ALL_TAC ] THEN
    SUBGOAL_THEN `val (num_5blocks_adjusted:int64) = 0` ASSUME_TAC THENL
    [ EXPAND_TAC "num_5blocks_adjusted" THEN
      REWRITE_TAC[ASSUME `val (num_blocks_adjusted:int64) = 0x10`] THEN
      WORD_ARITH_TAC
      ; ALL_TAC ] THEN

    TWEAK_TAC `Q8:(armstate,int128)component` `1:num` `0:num` THEN
    ARM_ACCSTEPS_TAC AES_XTS_DECRYPT_EXEC [] (90--92) THEN
    (* Discharge if condition *)
    SUBGOAL_THEN
      `ival (word_sub (num_blocks_adjusted:int64) (word 0x10)) < &0x0 <=>
      ~(ival (num_blocks_adjusted:int64) - &0x10 =
        ival (word_sub (num_blocks_adjusted:int64) (word 0x10)))` MP_TAC THENL
    [ SUBGOAL_THEN `num_blocks_adjusted:int64 = (word 0x10)` SUBST1_TAC THENL
      [ UNDISCH_TAC `val (num_blocks_adjusted:int64) = 0x10` THEN
        WORD_ARITH_TAC; ALL_TAC] THEN
      WORD_ARITH_TAC
      ; ALL_TAC] THEN
    DISCH_TAC THEN
    POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN

    ARM_ACCSTEPS_TAC AES_XTS_DECRYPT_EXEC [] (93--129) THEN
    XTSDEC_TAC `Q0:(armstate,int128)component` `0` `0` THEN
    ARM_ACCSTEPS_TAC AES_XTS_DECRYPT_EXEC [] (130--139) THEN
    TWEAK_TAC `Q6:(armstate,int128)component` `1:num` `0:num` THEN

    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
    [
      ASM_REWRITE_TAC[acc_len] THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC[WORD_ADD_0];
      ASM_REWRITE_TAC[acc_len] THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC[WORD_ADD_0];
      ASM_REWRITE_TAC[acc_blocks] THEN CONV_TAC NUM_REDUCE_CONV;

      ASM_REWRITE_TAC[acc_len] THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      IMP_REWRITE_TAC[VAL_WORD; DIMINDEX_64; MOD_LT] THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      MP_TAC (SPECL [`16:num`; `pt_ptr:int64`; `(aes256_xts_decrypt ct 16 iv key1 key2):byte list`;
        `s139:armstate`] BYTE_LIST_TO_NUM_THM) THEN
      ANTS_TAC THENL[
        MP_TAC (SPECL [`1`; `ct:byte list`; `iv:int128`;
          `key1:int128 list`; `key2:int128 list`] LENGTH_OF_AES256_XTS_DECRYPT_FULL_BLOCKS) THEN
        ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN (fun th -> REWRITE_TAC[th]) THEN
      IMP_REWRITE_TAC[READ_BYTES_EQ_READ_BYTE128_1BLOCK]
    ]
  ; ALL_TAC] THEN

  (* Reuse the cipher stealing proof *)
  MP_TAC CIPHER_STEALING_CORRECT THEN
  REWRITE_TAC [(REWRITE_CONV [aes_xts_decrypt_mc] THENC LENGTH_CONV) `LENGTH aes_xts_decrypt_mc`] THEN
  REWRITE_TAC[set_key_schedule; C_ARGUMENTS; SOME_FLAGS;
    NONOVERLAPPING_CLAUSES; byte_list_at;
    MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  EXISTS_TAC `(word 0x20):int64` THEN
  ASM_SIMP_TAC[] THEN
  SUBGOAL_THEN `num_blocks:int64 = word 0x20` ASSUME_TAC THENL
  [ UNDISCH_TAC `val (num_blocks:int64) = 0x20` THEN
    WORD_ARITH_TAC; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL [
    ASM_ARITH_TAC;
    ASM_ARITH_TAC;
    EXPAND_TAC "len" THEN AP_TERM_TAC THEN
    UNDISCH_TAC `val (num_blocks:int64) = 0x20` THEN
    WORD_ARITH_TAC;
    ASM_SIMP_TAC[];
    EXPAND_TAC "num_blocks_adjusted" THEN
    REWRITE_TAC[ASSUME `num_blocks:int64 = word 0x20`]
  ]
);;


(* Proof: less than 4 blocks *)
let AES_XTS_DECRYPT_LT_4BLOCK_CORRECT = time prove(
  `!ct_ptr pt_ptr ct key1_ptr key2_ptr iv_ptr iv len
    k00 k01 k02 k03 k04 k05 k06 k07 k08 k09 k0a k0b k0c k0d k0e
    k10 k11 k12 k13 k14 k15 k16 k17 k18 k19 k1a k1b k1c k1d k1e
    pc.
    nonoverlapping (word pc, LENGTH aes_xts_decrypt_mc) (pt_ptr, val len)
    /\ nonoverlapping (ct_ptr, val len) (pt_ptr, val len)
    /\ nonoverlapping (key1_ptr, 260) (pt_ptr, val len)
    /\ ~(val len < 0x30) /\ val len < 0x40 /\ LENGTH ct = val len
    /\ [k00; k01; k02; k03; k04; k05; k06; k07; k08; k09; k0a; k0b; k0c; k0d; k0e] = key1
    /\ [k10; k11; k12; k13; k14; k15; k16; k17; k18; k19; k1a; k1b; k1c; k1d; k1e] = key2
    ==> ensures arm
    (\s. aligned_bytes_loaded s (word pc) aes_xts_decrypt_mc /\
         read PC s = word (pc + 0x1c) /\
         C_ARGUMENTS [ct_ptr; pt_ptr; len; key1_ptr; key2_ptr; iv_ptr] s /\
         byte_list_at ct ct_ptr len s /\
         read(memory :> bytes128 iv_ptr) s = iv /\
         set_key_schedule s key1_ptr k00 k01 k02 k03 k04 k05 k06 k07 k08 k09 k0a k0b k0c k0d k0e /\
         set_key_schedule s key2_ptr k10 k11 k12 k13 k14 k15 k16 k17 k18 k19 k1a k1b k1c k1d k1e)
    (\s. read PC s = word (pc + 0xb58) /\
         byte_list_at (aes256_xts_decrypt ct (val len) iv key1 key2) pt_ptr len s
         )
    (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI,,
     MAYCHANGE [X19; X20; X21; X22],,
     MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15],,
     MAYCHANGE [memory :> bytes(pt_ptr, val len)])
    `,
  REWRITE_TAC [(REWRITE_CONV [aes_xts_decrypt_mc] THENC LENGTH_CONV) `LENGTH aes_xts_decrypt_mc`] THEN
  REWRITE_TAC[set_key_schedule; C_ARGUMENTS; SOME_FLAGS;
    NONOVERLAPPING_CLAUSES; byte_list_at;
    MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REPEAT STRIP_TAC THEN

  SUBGOAL_THEN `word_add (word_and len (word 0xf))
    (word_and len (word 0xfffffffffffffff0)) = len:int64` ASSUME_TAC THENL
  [REWRITE_TAC[word_split_lemma]; ALL_TAC] THEN
  ABBREV_TAC `num_blocks:int64 = word_and len (word 0xfffffffffffffff0)` THEN
  ABBREV_TAC `tail_len:int64 = word_and len (word 0xf)` THEN
  ABBREV_TAC `num_blocks_adjusted = if val (tail_len:int64) = 0
        then num_blocks else word_sub (num_blocks:int64) (word 0x10)` THEN
  ABBREV_TAC `num_5blocks_adjusted = (word (val (num_blocks_adjusted:int64) DIV 0x50)):int64` THEN

  SUBGOAL_THEN `val (num_blocks:int64) = 0x30` ASSUME_TAC THENL
  [ EXPAND_TAC "num_blocks" THEN
    REWRITE_TAC[NUM_BLOCKS_TO_VAL] THEN
    IMP_REWRITE_TAC[VAL_WORD; DIMINDEX_64; MOD_LT] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    SUBGOAL_THEN `val (len:int64) DIV 16 = 3` SUBST1_TAC THENL
    [ MATCH_MP_TAC(MESON[LE_ANTISYM] `m <= n /\ n <= m ==> m = n`) THEN
      CONJ_TAC THENL [ ASM_ARITH_TAC; ASM_ARITH_TAC];
      ALL_TAC] THEN
    ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `val (num_blocks_adjusted:int64) < 0x40` ASSUME_TAC THENL
  [ EXPAND_TAC "num_blocks_adjusted" THEN
    COND_CASES_TAC THENL[
      ASM_ARITH_TAC;
      UNDISCH_TAC `val (num_blocks:int64) = 0x30` THEN
      WORD_ARITH_TAC]
     ; ALL_TAC] THEN

  ENSURES_SEQUENCE_TAC `pc + 0xa0c`
  `\s.
    read X0 s = word_add ct_ptr (word (acc_len num_5blocks_adjusted num_blocks_adjusted)) /\
    read X1 s = word_add pt_ptr (word (acc_len num_5blocks_adjusted num_blocks_adjusted)) /\
    read X3 s = key1_ptr /\
    read X21 s = tail_len /\
    read Q6 s = calculate_tweak (acc_blocks num_5blocks_adjusted num_blocks_adjusted T) iv key2 /\
    read X19 s = word 0x87 /\
    read Q16 s = k00 /\ read Q17 s = k01 /\ read Q12 s = k02 /\ read Q13 s = k03 /\
    read Q14 s = k04 /\ read Q15 s = k05 /\ read Q4 s = k06 /\ read Q5 s = k07 /\
    read Q18 s = k08 /\ read Q19 s = k09 /\ read Q20 s = k0a /\ read Q21 s = k0b /\
    read Q22 s = k0c /\ read Q23 s = k0d /\ read Q7 s = k0e /\
    byte_list_at ct ct_ptr len s /\
    byte_list_at (aes256_xts_decrypt ct (acc_len num_5blocks_adjusted num_blocks_adjusted) iv key1 key2)
      pt_ptr (word (acc_len num_5blocks_adjusted num_blocks_adjusted)) s` THEN
  CONJ_TAC THENL
  [
    MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN
    EXISTS_TAC `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
      MAYCHANGE [X19; X20; X21; X22],,
      MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15],,
      MAYCHANGE [ memory :> bytes128 pt_ptr;
                  memory :> bytes128 (word_add pt_ptr (word 16));
                  memory :> bytes128 (word_add pt_ptr (word 32))]` THEN
    REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    CONJ_TAC THENL [
    REPEAT (GEN_REWRITE_TAC ONCE_DEPTH_CONV [GSYM SEQ_ASSOC] THEN
            MATCH_MP_TAC SUBSUMED_SEQ THEN REWRITE_TAC[SUBSUMED_REFL]) THEN
    ABBREV_TAC `vallen = val (len:int64)` THEN
    SUBSUMED_MAYCHANGE_TAC; ALL_TAC] THEN

    REWRITE_TAC[byte_list_at] THEN
    ENSURES_INIT_TAC "s0" THEN
    ARM_ACCSTEPS_TAC AES_XTS_DECRYPT_EXEC [] (1--2) THEN

    (* Discharge if condition *)
    SUBGOAL_THEN
      `ival (word_sub (len:int64) (word 0x10)) < &0x0
      <=> ~(ival (len:int64) - &0x10 = ival (word_sub (len:int64) (word 0x10)))` MP_TAC THENL
    [ MP_TAC (BITBLAST_RULE
        `~(val (len:int64) < 0x30) ==> val len < 0x40 ==>
        ival (word_sub len (word 0x10)) >= &0x0`) THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC (BITBLAST_RULE
        `~(val (len:int64) < 0x30) ==> val len < 0x40 ==>
         ival (len:int64) - &0x10 = ival (word_sub len (word 0x10))`) THEN
      ASM_REWRITE_TAC[] THEN
      ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN

    MP_TAC (SPECL [`ct_ptr:int64`; `len:int64`; `ct:byte list`; `s2:armstate`] READ_LT_4BLOCK) THEN
    ASM_SIMP_TAC[] THEN REPEAT STRIP_TAC THEN

    ARM_ACCSTEPS_TAC AES_XTS_DECRYPT_EXEC [] (3--69) THEN
    (* Prove Q6 stores initial tweak *)
    FIRST_X_ASSUM(MP_TAC o SPEC `(calculate_tweak 0 iv key2)`
      o  MATCH_MP (MESON[] `read Q6 s = a ==> !a'. a = a' ==> read Q6 s = a'`)) THEN
    ANTS_TAC THENL
    [ REWRITE_TAC[CONJUNCT1 calculate_tweak; xts_init_tweak] THEN
      EXPAND_TAC "key2" THEN AESENC_TAC; DISCH_TAC] THEN

    (* Simulating until branch for num_blocks adjustment *)
    ARM_ACCSTEPS_TAC AES_XTS_DECRYPT_EXEC [] (70--89) THEN

    (* Case split on whether there is a tail *)
    FIRST_X_ASSUM MP_TAC THEN
    COND_CASES_TAC THENL
    [
      DISCH_TAC THEN

      SUBGOAL_THEN `val (tail_len:int64) = 0` SUBST_ALL_TAC THENL
      [ UNDISCH_TAC `val (word_and (tail_len:int64) (word 0xf)) = 0x0` THEN
        MP_TAC (SPECL [`len:int64`; `tail_len:int64`] TAIL_LEN_BOUND_THM) THEN
        ASM_SIMP_TAC[] THEN DISCH_TAC THEN
        SUBGOAL_THEN `val (word_and (tail_len:int64) (word 15)) = val tail_len` SUBST1_TAC THENL
        [ REWRITE_TAC[VAL_WORD_AND_MASK_WORD; ARITH_RULE `15 = 2 EXP 4 - 1`] THEN
          CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
          IMP_REWRITE_TAC[MOD_LT];
          ALL_TAC] THEN
        SIMP_TAC[]; ALL_TAC] THEN
      CONV_TAC NUM_REDUCE_CONV THEN

      SUBGOAL_THEN `val (num_blocks_adjusted:int64) = 0x30` ASSUME_TAC THENL
      [ EXPAND_TAC "num_blocks_adjusted" THEN
        CONV_TAC NUM_REDUCE_CONV THEN
        ASM_REWRITE_TAC[]
        ; ALL_TAC ] THEN
      SUBGOAL_THEN `val (num_5blocks_adjusted:int64) = 0` ASSUME_TAC THENL
      [ EXPAND_TAC "num_5blocks_adjusted" THEN
        UNDISCH_TAC `val (num_blocks_adjusted:int64) = 0x30` THEN
        SIMP_TAC[] THEN DISCH_TAC THEN
        CONV_TAC NUM_REDUCE_CONV THEN
        REWRITE_TAC[VAL_WORD_0]
        ; ALL_TAC ] THEN

      TWEAK_TAC `Q8:(armstate,int128)component` `1:num` `0:num` THEN
      ARM_ACCSTEPS_TAC AES_XTS_DECRYPT_EXEC [] (90--105) THEN
      TWEAK_TAC `Q9:(armstate,int128)component` `2:num` `1:num` THEN
      ARM_ACCSTEPS_TAC AES_XTS_DECRYPT_EXEC [] (106--197) THEN
      XTSDEC_TAC `Q0:(armstate,int128)component` `0` `0` THEN
      XTSDEC_TAC `Q1:(armstate,int128)component` `0x10` `1` THEN
      XTSDEC_TAC `Q24:(armstate,int128)component` `0x20` `2` THEN
      ARM_ACCSTEPS_TAC AES_XTS_DECRYPT_EXEC [] (198--208) THEN
      TWEAK_TAC `Q6:(armstate,int128)component` `3:num` `2:num` THEN

      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      REPEAT CONJ_TAC THENL
      [
        ASM_REWRITE_TAC[acc_len] THEN CONV_TAC NUM_REDUCE_CONV;
        ASM_REWRITE_TAC[acc_len] THEN CONV_TAC NUM_REDUCE_CONV;
        ASM_REWRITE_TAC[acc_blocks] THEN CONV_TAC NUM_REDUCE_CONV;

        ASM_REWRITE_TAC[acc_len] THEN
        CONV_TAC NUM_REDUCE_CONV THEN
        IMP_REWRITE_TAC[VAL_WORD; DIMINDEX_64; MOD_LT] THEN
        CONV_TAC NUM_REDUCE_CONV THEN
        MP_TAC (SPECL [`0x30:num`; `pt_ptr:int64`; `(aes256_xts_decrypt ct 0x30 iv key1 key2):byte list`;
          `s208:armstate`] BYTE_LIST_TO_NUM_THM) THEN
        ANTS_TAC THENL[
          MP_TAC (SPECL [`3`; `ct:byte list`; `iv:int128`; `key1:int128 list`;
            `key2:int128 list`] LENGTH_OF_AES256_XTS_DECRYPT_FULL_BLOCKS) THEN
          ARITH_TAC; ALL_TAC] THEN
        DISCH_THEN (fun th -> REWRITE_TAC[th]) THEN
        IMP_REWRITE_TAC[READ_BYTES_EQ_READ_BYTE128_3BLOCKS]
      ]; ALL_TAC
    ] THEN

    (* There is a tail *)
    DISCH_TAC THEN
    (* Prove ~ tail_len = 0 *)
    SUBGOAL_THEN `~(val (tail_len:int64) = 0)` ASSUME_TAC THENL
    [ UNDISCH_TAC `~(val (word_and (tail_len:int64) (word 0xf)) = 0x0)` THEN
      MP_TAC (SPECL [`len:int64`; `tail_len:int64`] TAIL_LEN_BOUND_THM) THEN
      ASM_REWRITE_TAC[] THEN
      SUBST1_TAC(ARITH_RULE `0xf = 2 EXP 4 - 1`) THEN
      REWRITE_TAC[VAL_WORD_AND_MASK_WORD] THEN
      NUM_REDUCE_TAC THEN IMP_REWRITE_TAC[MOD_LT]
    ; ALL_TAC] THEN
    (* Prove num_blocks_adjusted = word_sub num_blocks (word 0x10) *)
    SUBGOAL_THEN `word_sub num_blocks (word 0x10) = num_blocks_adjusted:int64` ASSUME_TAC THENL
    [ UNDISCH_TAC `(if val (tail_len:int64) = 0x0
        then (num_blocks:int64)
        else word_sub num_blocks (word 0x10)) = num_blocks_adjusted` THEN
      ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `val (num_blocks_adjusted:int64) = 0x20` ASSUME_TAC THENL
    [ EXPAND_TAC "num_blocks_adjusted" THEN
      UNDISCH_TAC `val (num_blocks:int64) = 0x30` THEN
      WORD_ARITH_TAC
    ; ALL_TAC ] THEN
    SUBGOAL_THEN `val (num_5blocks_adjusted:int64) = 0` ASSUME_TAC THENL
    [ EXPAND_TAC "num_5blocks_adjusted" THEN
      REWRITE_TAC[ASSUME `val (num_blocks_adjusted:int64) = 0x20`] THEN
      WORD_ARITH_TAC
      ; ALL_TAC ] THEN

    TWEAK_TAC `Q8:(armstate,int128)component` `1:num` `0:num` THEN
    ARM_ACCSTEPS_TAC AES_XTS_DECRYPT_EXEC [] (90--92) THEN
    (* Discharge if condition *)
    SUBGOAL_THEN
      `ival (word_sub (num_blocks_adjusted:int64) (word 0x10)) < &0x0 <=>
      ~(ival (num_blocks_adjusted:int64) - &0x10 =
        ival (word_sub (num_blocks_adjusted:int64) (word 0x10)))` MP_TAC THENL
    [ SUBGOAL_THEN `num_blocks_adjusted:int64 = (word 0x20)` SUBST1_TAC THENL
      [ UNDISCH_TAC `val (num_blocks_adjusted:int64) = 0x20` THEN
        WORD_ARITH_TAC; ALL_TAC] THEN
      WORD_ARITH_TAC
      ; ALL_TAC] THEN
    DISCH_TAC THEN
    POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN

    ARM_ACCSTEPS_TAC AES_XTS_DECRYPT_EXEC [] (93--161) THEN
    XTSDEC_TAC `Q0:(armstate,int128)component` `0` `0` THEN
    XTSDEC_TAC `Q1:(armstate,int128)component` `0x10` `1` THEN
    ARM_ACCSTEPS_TAC AES_XTS_DECRYPT_EXEC [] (162--171) THEN
    TWEAK_TAC `Q6:(armstate,int128)component` `2:num` `1:num` THEN

    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
    [
      ASM_REWRITE_TAC[acc_len] THEN CONV_TAC NUM_REDUCE_CONV;
      ASM_REWRITE_TAC[acc_len] THEN CONV_TAC NUM_REDUCE_CONV;
      ASM_REWRITE_TAC[acc_blocks] THEN CONV_TAC NUM_REDUCE_CONV;

      ASM_REWRITE_TAC[acc_len] THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      IMP_REWRITE_TAC[VAL_WORD; DIMINDEX_64; MOD_LT] THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      MP_TAC (SPECL [`0x20:num`; `pt_ptr:int64`; `(aes256_xts_decrypt ct 0x20 iv key1 key2):byte list`;
        `s171:armstate`] BYTE_LIST_TO_NUM_THM) THEN
      ANTS_TAC THENL[
        MP_TAC (SPECL [`2`; `ct:byte list`; `iv:int128`;
          `key1:int128 list`; `key2:int128 list`] LENGTH_OF_AES256_XTS_DECRYPT_FULL_BLOCKS) THEN
        ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN (fun th -> REWRITE_TAC[th]) THEN
      IMP_REWRITE_TAC[READ_BYTES_EQ_READ_BYTE128_2BLOCKS]
    ]; ALL_TAC] THEN

  (* Reuse the cipher stealing proof *)
  MP_TAC CIPHER_STEALING_CORRECT THEN
  REWRITE_TAC [(REWRITE_CONV [aes_xts_decrypt_mc] THENC LENGTH_CONV) `LENGTH aes_xts_decrypt_mc`] THEN
  REWRITE_TAC[set_key_schedule; C_ARGUMENTS; SOME_FLAGS;
    NONOVERLAPPING_CLAUSES; byte_list_at;
    MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  EXISTS_TAC `(word 0x30):int64` THEN
  ASM_SIMP_TAC[] THEN
  SUBGOAL_THEN `num_blocks:int64 = word 0x30` ASSUME_TAC THENL
  [ UNDISCH_TAC `val (num_blocks:int64) = 0x30` THEN
    WORD_ARITH_TAC; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL [
    ASM_ARITH_TAC;
    ASM_ARITH_TAC;
    EXPAND_TAC "len" THEN AP_TERM_TAC THEN
    UNDISCH_TAC `val (num_blocks:int64) = 0x30` THEN
    WORD_ARITH_TAC;
    ASM_SIMP_TAC[];
    EXPAND_TAC "num_blocks_adjusted" THEN
    REWRITE_TAC[ASSUME `num_blocks:int64 = word 0x30`]
  ]
);;


(* Proof: less than 5 blocks *)
let AES_XTS_DECRYPT_LT_5BLOCK_CORRECT = time prove(
  `!ct_ptr pt_ptr ct key1_ptr key2_ptr iv_ptr iv len
    k00 k01 k02 k03 k04 k05 k06 k07 k08 k09 k0a k0b k0c k0d k0e
    k10 k11 k12 k13 k14 k15 k16 k17 k18 k19 k1a k1b k1c k1d k1e
    pc.
    nonoverlapping (word pc, LENGTH aes_xts_decrypt_mc) (pt_ptr, val len)
    /\ nonoverlapping (ct_ptr, val len) (pt_ptr, val len)
    /\ nonoverlapping (key1_ptr, 260) (pt_ptr, val len)
    /\ ~(val len < 0x40) /\ val len < 0x50 /\ LENGTH ct = val len
    /\ [k00; k01; k02; k03; k04; k05; k06; k07; k08; k09; k0a; k0b; k0c; k0d; k0e] = key1
    /\ [k10; k11; k12; k13; k14; k15; k16; k17; k18; k19; k1a; k1b; k1c; k1d; k1e] = key2
    ==> ensures arm
    (\s. aligned_bytes_loaded s (word pc) aes_xts_decrypt_mc /\
         read PC s = word (pc + 0x1c) /\
         C_ARGUMENTS [ct_ptr; pt_ptr; len; key1_ptr; key2_ptr; iv_ptr] s /\
         byte_list_at ct ct_ptr len s /\
         read(memory :> bytes128 iv_ptr) s = iv /\
         set_key_schedule s key1_ptr k00 k01 k02 k03 k04 k05 k06 k07 k08 k09 k0a k0b k0c k0d k0e /\
         set_key_schedule s key2_ptr k10 k11 k12 k13 k14 k15 k16 k17 k18 k19 k1a k1b k1c k1d k1e)
    (\s. read PC s = word (pc + 0xb58) /\
         byte_list_at (aes256_xts_decrypt ct (val len) iv key1 key2) pt_ptr len s
         )
    (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI,,
     MAYCHANGE [X19; X20; X21; X22],,
     MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15],,
     MAYCHANGE [memory :> bytes(pt_ptr, val len)])
    `,
  REWRITE_TAC [(REWRITE_CONV [aes_xts_decrypt_mc] THENC LENGTH_CONV) `LENGTH aes_xts_decrypt_mc`] THEN
  REWRITE_TAC[set_key_schedule; C_ARGUMENTS; SOME_FLAGS;
    NONOVERLAPPING_CLAUSES; byte_list_at;
    MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REPEAT STRIP_TAC THEN

  SUBGOAL_THEN `word_add (word_and len (word 0xf))
    (word_and len (word 0xfffffffffffffff0)) = len:int64` ASSUME_TAC THENL
  [REWRITE_TAC[word_split_lemma]; ALL_TAC] THEN
  ABBREV_TAC `num_blocks:int64 = word_and len (word 0xfffffffffffffff0)` THEN
  ABBREV_TAC `tail_len:int64 = word_and len (word 0xf)` THEN
  ABBREV_TAC `num_blocks_adjusted = if val (tail_len:int64) = 0
        then num_blocks else word_sub (num_blocks:int64) (word 0x10)` THEN
  ABBREV_TAC `num_5blocks_adjusted = (word (val (num_blocks_adjusted:int64) DIV 0x50)):int64` THEN

  SUBGOAL_THEN `val (num_blocks:int64) = 0x40` ASSUME_TAC THENL
  [ EXPAND_TAC "num_blocks" THEN
    REWRITE_TAC[NUM_BLOCKS_TO_VAL] THEN
    IMP_REWRITE_TAC[VAL_WORD; DIMINDEX_64; MOD_LT] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    SUBGOAL_THEN `val (len:int64) DIV 16 = 4` SUBST1_TAC THENL
    [ MATCH_MP_TAC(MESON[LE_ANTISYM] `m <= n /\ n <= m ==> m = n`) THEN
      CONJ_TAC THENL [ ASM_ARITH_TAC; ASM_ARITH_TAC];
      ALL_TAC] THEN
    ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `val (num_blocks_adjusted:int64) < 0x50` ASSUME_TAC THENL
  [ EXPAND_TAC "num_blocks_adjusted" THEN
    COND_CASES_TAC THENL[
      ASM_ARITH_TAC;
      UNDISCH_TAC `val (num_blocks:int64) = 0x40` THEN
      WORD_ARITH_TAC]
     ; ALL_TAC] THEN

  ENSURES_SEQUENCE_TAC `pc + 0xa0c`
  `\s.
    read X0 s = word_add ct_ptr (word (acc_len num_5blocks_adjusted num_blocks_adjusted)) /\
    read X1 s = word_add pt_ptr (word (acc_len num_5blocks_adjusted num_blocks_adjusted)) /\
    read X3 s = key1_ptr /\
    read X21 s = tail_len /\
    read Q6 s = calculate_tweak (acc_blocks num_5blocks_adjusted num_blocks_adjusted T) iv key2 /\
    read X19 s = word 0x87 /\
    read Q16 s = k00 /\ read Q17 s = k01 /\ read Q12 s = k02 /\ read Q13 s = k03 /\
    read Q14 s = k04 /\ read Q15 s = k05 /\ read Q4 s = k06 /\ read Q5 s = k07 /\
    read Q18 s = k08 /\ read Q19 s = k09 /\ read Q20 s = k0a /\ read Q21 s = k0b /\
    read Q22 s = k0c /\ read Q23 s = k0d /\ read Q7 s = k0e /\
    byte_list_at ct ct_ptr len s /\
    byte_list_at (aes256_xts_decrypt ct (acc_len num_5blocks_adjusted num_blocks_adjusted) iv key1 key2)
      pt_ptr (word (acc_len num_5blocks_adjusted num_blocks_adjusted)) s` THEN
  CONJ_TAC THENL
  [
    MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN
    EXISTS_TAC `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
      MAYCHANGE [X19; X20; X21; X22],,
      MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15],,
      MAYCHANGE [ memory :> bytes128 pt_ptr;
                  memory :> bytes128 (word_add pt_ptr (word 16));
                  memory :> bytes128 (word_add pt_ptr (word 32));
                  memory :> bytes128 (word_add pt_ptr (word 48))]` THEN
    REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    CONJ_TAC THENL [
    REPEAT (GEN_REWRITE_TAC ONCE_DEPTH_CONV [GSYM SEQ_ASSOC] THEN
            MATCH_MP_TAC SUBSUMED_SEQ THEN REWRITE_TAC[SUBSUMED_REFL]) THEN
    ABBREV_TAC `vallen = val (len:int64)` THEN
    SUBSUMED_MAYCHANGE_TAC; ALL_TAC] THEN

    REWRITE_TAC[byte_list_at] THEN
    ENSURES_INIT_TAC "s0" THEN
    ARM_ACCSTEPS_TAC AES_XTS_DECRYPT_EXEC [] (1--2) THEN

    (* Discharge if condition *)
    SUBGOAL_THEN
      `ival (word_sub (len:int64) (word 0x10)) < &0x0
      <=> ~(ival (len:int64) - &0x10 = ival (word_sub (len:int64) (word 0x10)))` MP_TAC THENL
    [ MP_TAC (BITBLAST_RULE
        `~(val (len:int64) < 0x40) ==> val len < 0x50 ==>
        ival (word_sub len (word 0x10)) >= &0x0`) THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC (BITBLAST_RULE
        `~(val (len:int64) < 0x40) ==> val len < 0x50 ==>
         ival (len:int64) - &0x10 = ival (word_sub len (word 0x10))`) THEN
      ASM_REWRITE_TAC[] THEN
      ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN

    MP_TAC (SPECL [`ct_ptr:int64`; `len:int64`; `ct:byte list`; `s2:armstate`] READ_LT_5BLOCK) THEN
    ASM_SIMP_TAC[] THEN REPEAT STRIP_TAC THEN

    ARM_ACCSTEPS_TAC AES_XTS_DECRYPT_EXEC [] (3--69) THEN
    (* Prove Q6 stores initial tweak *)
    FIRST_X_ASSUM(MP_TAC o SPEC `(calculate_tweak 0 iv key2)`
      o  MATCH_MP (MESON[] `read Q6 s = a ==> !a'. a = a' ==> read Q6 s = a'`)) THEN
    ANTS_TAC THENL
    [ REWRITE_TAC[CONJUNCT1 calculate_tweak; xts_init_tweak] THEN
      EXPAND_TAC "key2" THEN AESENC_TAC; DISCH_TAC] THEN

    (* Simulating until branch for num_blocks adjustment *)
    ARM_ACCSTEPS_TAC AES_XTS_DECRYPT_EXEC [] (70--89) THEN

    (* Case split on whether there is a tail *)
    FIRST_X_ASSUM MP_TAC THEN
    COND_CASES_TAC THENL
    [
      DISCH_TAC THEN

      SUBGOAL_THEN `val (tail_len:int64) = 0` SUBST_ALL_TAC THENL
      [ UNDISCH_TAC `val (word_and (tail_len:int64) (word 0xf)) = 0x0` THEN
        MP_TAC (SPECL [`len:int64`; `tail_len:int64`] TAIL_LEN_BOUND_THM) THEN
        ASM_SIMP_TAC[] THEN DISCH_TAC THEN
        SUBGOAL_THEN `val (word_and (tail_len:int64) (word 15)) = val tail_len` SUBST1_TAC THENL
        [ REWRITE_TAC[VAL_WORD_AND_MASK_WORD; ARITH_RULE `15 = 2 EXP 4 - 1`] THEN
          CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
          IMP_REWRITE_TAC[MOD_LT];
          ALL_TAC] THEN
        SIMP_TAC[]; ALL_TAC] THEN
      CONV_TAC NUM_REDUCE_CONV THEN

      SUBGOAL_THEN `val (num_blocks_adjusted:int64) = 0x40` ASSUME_TAC THENL
      [ EXPAND_TAC "num_blocks_adjusted" THEN
        CONV_TAC NUM_REDUCE_CONV THEN
        ASM_REWRITE_TAC[]
        ; ALL_TAC ] THEN
      SUBGOAL_THEN `val (num_5blocks_adjusted:int64) = 0` ASSUME_TAC THENL
      [ EXPAND_TAC "num_5blocks_adjusted" THEN
        UNDISCH_TAC `val (num_blocks_adjusted:int64) = 0x40` THEN
        SIMP_TAC[] THEN DISCH_TAC THEN
        CONV_TAC NUM_REDUCE_CONV THEN
        REWRITE_TAC[VAL_WORD_0]
        ; ALL_TAC ] THEN

      TWEAK_TAC `Q8:(armstate,int128)component` `1:num` `0:num` THEN
      ARM_ACCSTEPS_TAC AES_XTS_DECRYPT_EXEC [] (90--105) THEN
      TWEAK_TAC `Q9:(armstate,int128)component` `2:num` `1:num` THEN
      ARM_ACCSTEPS_TAC AES_XTS_DECRYPT_EXEC [] (106--113) THEN
      TWEAK_TAC `Q10:(armstate,int128)component` `3:num` `2:num` THEN

      ARM_ACCSTEPS_TAC AES_XTS_DECRYPT_EXEC [] (114--235) THEN
      XTSDEC_TAC `Q0:(armstate,int128)component` `0` `0` THEN
      XTSDEC_TAC `Q1:(armstate,int128)component` `0x10` `1` THEN
      XTSDEC_TAC `Q24:(armstate,int128)component` `0x20` `2` THEN
      XTSDEC_TAC `Q25:(armstate,int128)component` `0x30` `3` THEN
      ARM_ACCSTEPS_TAC AES_XTS_DECRYPT_EXEC [] (236--246) THEN
      TWEAK_TAC `Q6:(armstate,int128)component` `4:num` `3:num` THEN

      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      REPEAT CONJ_TAC THENL
      [
        ASM_REWRITE_TAC[acc_len] THEN CONV_TAC NUM_REDUCE_CONV;
        ASM_REWRITE_TAC[acc_len] THEN CONV_TAC NUM_REDUCE_CONV;
        ASM_REWRITE_TAC[acc_blocks] THEN CONV_TAC NUM_REDUCE_CONV;

        ASM_REWRITE_TAC[acc_len] THEN
        CONV_TAC NUM_REDUCE_CONV THEN
        IMP_REWRITE_TAC[VAL_WORD; DIMINDEX_64; MOD_LT] THEN
        CONV_TAC NUM_REDUCE_CONV THEN
        MP_TAC (SPECL [`0x40:num`; `pt_ptr:int64`; `(aes256_xts_decrypt ct 0x40 iv key1 key2):byte list`;
          `s246:armstate`] BYTE_LIST_TO_NUM_THM) THEN
        ANTS_TAC THENL[
          MP_TAC (SPECL [`4`; `ct:byte list`; `iv:int128`; `key1:int128 list`;
            `key2:int128 list`] LENGTH_OF_AES256_XTS_DECRYPT_FULL_BLOCKS) THEN
          ARITH_TAC; ALL_TAC] THEN
        DISCH_THEN (fun th -> REWRITE_TAC[th]) THEN
        IMP_REWRITE_TAC[READ_BYTES_EQ_READ_BYTE128_4BLOCKS] ]
      ; ALL_TAC
    ] THEN

    (* There is a tail *)
    DISCH_TAC THEN
    (* Prove ~ tail_len = 0 *)
    SUBGOAL_THEN `~(val (tail_len:int64) = 0)` ASSUME_TAC THENL
    [ UNDISCH_TAC `~(val (word_and (tail_len:int64) (word 0xf)) = 0x0)` THEN
      MP_TAC (SPECL [`len:int64`; `tail_len:int64`] TAIL_LEN_BOUND_THM) THEN
      ASM_REWRITE_TAC[] THEN
      SUBST1_TAC(ARITH_RULE `0xf = 2 EXP 4 - 1`) THEN
      REWRITE_TAC[VAL_WORD_AND_MASK_WORD] THEN
      NUM_REDUCE_TAC THEN IMP_REWRITE_TAC[MOD_LT]
    ; ALL_TAC] THEN
    (* Prove num_blocks_adjusted = word_sub num_blocks (word 0x10) *)
    SUBGOAL_THEN `word_sub num_blocks (word 0x10) = num_blocks_adjusted:int64` ASSUME_TAC THENL
    [ UNDISCH_TAC `(if val (tail_len:int64) = 0x0
        then (num_blocks:int64)
        else word_sub num_blocks (word 0x10)) = num_blocks_adjusted` THEN
      ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `val (num_blocks_adjusted:int64) = 0x30` ASSUME_TAC THENL
    [ EXPAND_TAC "num_blocks_adjusted" THEN
      UNDISCH_TAC `val (num_blocks:int64) = 0x40` THEN
      WORD_ARITH_TAC
    ; ALL_TAC ] THEN
    SUBGOAL_THEN `val (num_5blocks_adjusted:int64) = 0` ASSUME_TAC THENL
    [ EXPAND_TAC "num_5blocks_adjusted" THEN
      REWRITE_TAC[ASSUME `val (num_blocks_adjusted:int64) = 0x30`] THEN
      WORD_ARITH_TAC
      ; ALL_TAC ] THEN

    TWEAK_TAC `Q8:(armstate,int128)component` `1:num` `0:num` THEN
    ARM_ACCSTEPS_TAC AES_XTS_DECRYPT_EXEC [] (90--92) THEN
    (* Discharge if condition *)
    SUBGOAL_THEN
      `ival (word_sub (num_blocks_adjusted:int64) (word 0x10)) < &0x0 <=>
      ~(ival (num_blocks_adjusted:int64) - &0x10 =
        ival (word_sub (num_blocks_adjusted:int64) (word 0x10)))` MP_TAC THENL
    [ SUBGOAL_THEN `num_blocks_adjusted:int64 = (word 0x30)` SUBST1_TAC THENL
      [ UNDISCH_TAC `val (num_blocks_adjusted:int64) = 0x30` THEN
        WORD_ARITH_TAC; ALL_TAC] THEN
      WORD_ARITH_TAC
      ; ALL_TAC] THEN
    DISCH_TAC THEN
    POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN

    ARM_ACCSTEPS_TAC AES_XTS_DECRYPT_EXEC [] (93--108) THEN
    TWEAK_TAC `Q9:(armstate,int128)component` `2:num` `1:num` THEN
    ARM_ACCSTEPS_TAC AES_XTS_DECRYPT_EXEC [] (109--200) THEN
    XTSDEC_TAC `Q0:(armstate,int128)component` `0` `0` THEN
    XTSDEC_TAC `Q1:(armstate,int128)component` `0x10` `1` THEN
    XTSDEC_TAC `Q24:(armstate,int128)component` `0x20` `2` THEN
    ARM_ACCSTEPS_TAC AES_XTS_DECRYPT_EXEC [] (201--211) THEN
    TWEAK_TAC `Q6:(armstate,int128)component` `3:num` `2:num` THEN

    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
    [
      ASM_REWRITE_TAC[acc_len] THEN
      CONV_TAC NUM_REDUCE_CONV;
      ASM_REWRITE_TAC[acc_len] THEN
      CONV_TAC NUM_REDUCE_CONV;
      ASM_REWRITE_TAC[acc_blocks] THEN CONV_TAC NUM_REDUCE_CONV;

      ASM_REWRITE_TAC[acc_len] THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      IMP_REWRITE_TAC[VAL_WORD; DIMINDEX_64; MOD_LT] THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      MP_TAC (SPECL [`0x30:num`; `pt_ptr:int64`; `(aes256_xts_decrypt ct 0x30 iv key1 key2):byte list`;
        `s211:armstate`] BYTE_LIST_TO_NUM_THM) THEN
      ANTS_TAC THENL[
        MP_TAC (SPECL [`3`; `ct:byte list`; `iv:int128`;
          `key1:int128 list`; `key2:int128 list`] LENGTH_OF_AES256_XTS_DECRYPT_FULL_BLOCKS) THEN
        ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN (fun th -> REWRITE_TAC[th]) THEN
      IMP_REWRITE_TAC[READ_BYTES_EQ_READ_BYTE128_3BLOCKS]
  ]; ALL_TAC] THEN

  (* Reuse the cipher stealing proof *)
  MP_TAC CIPHER_STEALING_CORRECT THEN
  REWRITE_TAC [(REWRITE_CONV [aes_xts_decrypt_mc] THENC LENGTH_CONV) `LENGTH aes_xts_decrypt_mc`] THEN
  REWRITE_TAC[set_key_schedule; C_ARGUMENTS; SOME_FLAGS;
    NONOVERLAPPING_CLAUSES; byte_list_at;
    MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  EXISTS_TAC `(word 0x40):int64` THEN
  ASM_SIMP_TAC[] THEN
  SUBGOAL_THEN `num_blocks:int64 = word 0x40` ASSUME_TAC THENL
  [ UNDISCH_TAC `val (num_blocks:int64) = 0x40` THEN
    WORD_ARITH_TAC; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL [
    ASM_ARITH_TAC;
    ASM_ARITH_TAC;
    EXPAND_TAC "len" THEN AP_TERM_TAC THEN
    UNDISCH_TAC `val (num_blocks:int64) = 0x40` THEN
    WORD_ARITH_TAC;
    ASM_SIMP_TAC[];
    EXPAND_TAC "num_blocks_adjusted" THEN
    REWRITE_TAC[ASSUME `num_blocks:int64 = word 0x40`]
  ]
);;


(* Proof: less than 6 blocks *)
let AES_XTS_DECRYPT_LT_6BLOCK_CORRECT = time prove(
  `!ct_ptr pt_ptr ct key1_ptr key2_ptr iv_ptr iv len
    k00 k01 k02 k03 k04 k05 k06 k07 k08 k09 k0a k0b k0c k0d k0e
    k10 k11 k12 k13 k14 k15 k16 k17 k18 k19 k1a k1b k1c k1d k1e
    pc.
    nonoverlapping (word pc, LENGTH aes_xts_decrypt_mc) (pt_ptr, val len)
    /\ nonoverlapping (ct_ptr, val len) (pt_ptr, val len)
    /\ nonoverlapping (key1_ptr, 260) (pt_ptr, val len)
    /\ ~(val len < 0x50) /\ val len < 0x60 /\ LENGTH ct = val len
    /\ [k00; k01; k02; k03; k04; k05; k06; k07; k08; k09; k0a; k0b; k0c; k0d; k0e] = key1
    /\ [k10; k11; k12; k13; k14; k15; k16; k17; k18; k19; k1a; k1b; k1c; k1d; k1e] = key2
    ==> ensures arm
    (\s. aligned_bytes_loaded s (word pc) aes_xts_decrypt_mc /\
         read PC s = word (pc + 0x1c) /\
         C_ARGUMENTS [ct_ptr; pt_ptr; len; key1_ptr; key2_ptr; iv_ptr] s /\
         byte_list_at ct ct_ptr len s /\
         read(memory :> bytes128 iv_ptr) s = iv /\
         set_key_schedule s key1_ptr k00 k01 k02 k03 k04 k05 k06 k07 k08 k09 k0a k0b k0c k0d k0e /\
         set_key_schedule s key2_ptr k10 k11 k12 k13 k14 k15 k16 k17 k18 k19 k1a k1b k1c k1d k1e)
    (\s. read PC s = word (pc + 0xb58) /\
         byte_list_at (aes256_xts_decrypt ct (val len) iv key1 key2) pt_ptr len s
         )
    (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI,,
     MAYCHANGE [X19; X20; X21; X22],,
     MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15],,
     MAYCHANGE [memory :> bytes(pt_ptr, val len)])
    `,
  REWRITE_TAC [(REWRITE_CONV [aes_xts_decrypt_mc] THENC LENGTH_CONV) `LENGTH aes_xts_decrypt_mc`] THEN
  REWRITE_TAC[set_key_schedule; C_ARGUMENTS; SOME_FLAGS;
    NONOVERLAPPING_CLAUSES; byte_list_at;
    MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REPEAT STRIP_TAC THEN

  SUBGOAL_THEN `word_add (word_and len (word 0xf))
    (word_and len (word 0xfffffffffffffff0)) = len:int64` ASSUME_TAC THENL
  [REWRITE_TAC[word_split_lemma]; ALL_TAC] THEN
  ABBREV_TAC `num_blocks:int64 = word_and len (word 0xfffffffffffffff0)` THEN
  ABBREV_TAC `tail_len:int64 = word_and len (word 0xf)` THEN
  ABBREV_TAC `num_blocks_adjusted = if val (tail_len:int64) = 0
        then num_blocks else word_sub (num_blocks:int64) (word 0x10)` THEN
  ABBREV_TAC `num_5blocks_adjusted = (word (val (num_blocks_adjusted:int64) DIV 0x50)):int64` THEN

  SUBGOAL_THEN `val (num_blocks:int64) = 0x50` ASSUME_TAC THENL
  [ EXPAND_TAC "num_blocks" THEN
    REWRITE_TAC[NUM_BLOCKS_TO_VAL] THEN
    IMP_REWRITE_TAC[VAL_WORD; DIMINDEX_64; MOD_LT] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    SUBGOAL_THEN `val (len:int64) DIV 16 = 5` SUBST1_TAC THENL
    [ MATCH_MP_TAC(MESON[LE_ANTISYM] `m <= n /\ n <= m ==> m = n`) THEN
      CONJ_TAC THENL [ ASM_ARITH_TAC; ASM_ARITH_TAC];
      ALL_TAC] THEN
    ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `val (num_blocks_adjusted:int64) < 0x60` ASSUME_TAC THENL
  [ EXPAND_TAC "num_blocks_adjusted" THEN
    COND_CASES_TAC THENL[
      ASM_ARITH_TAC;
      UNDISCH_TAC `val (num_blocks:int64) = 0x50` THEN
      WORD_ARITH_TAC]
     ; ALL_TAC] THEN

  ENSURES_SEQUENCE_TAC `pc + 0xa0c`
  `\s.
    read X0 s = word_add ct_ptr (word (acc_len num_5blocks_adjusted num_blocks_adjusted)) /\
    read X1 s = word_add pt_ptr (word (acc_len num_5blocks_adjusted num_blocks_adjusted)) /\
    read X3 s = key1_ptr /\
    read X21 s = tail_len /\
    read Q6 s = calculate_tweak (acc_blocks num_5blocks_adjusted num_blocks_adjusted T) iv key2 /\
    read X19 s = word 0x87 /\
    read Q16 s = k00 /\ read Q17 s = k01 /\ read Q12 s = k02 /\ read Q13 s = k03 /\
    read Q14 s = k04 /\ read Q15 s = k05 /\ read Q4 s = k06 /\ read Q5 s = k07 /\
    read Q18 s = k08 /\ read Q19 s = k09 /\ read Q20 s = k0a /\ read Q21 s = k0b /\
    read Q22 s = k0c /\ read Q23 s = k0d /\ read Q7 s = k0e /\
    byte_list_at ct ct_ptr len s /\
    byte_list_at (aes256_xts_decrypt ct (acc_len num_5blocks_adjusted num_blocks_adjusted) iv key1 key2)
      pt_ptr (word (acc_len num_5blocks_adjusted num_blocks_adjusted)) s` THEN
  CONJ_TAC THENL
  [
    MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN
    EXISTS_TAC `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
      MAYCHANGE [X19; X20; X21; X22],,
      MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15],,
      MAYCHANGE [ memory :> bytes128 pt_ptr;
                  memory :> bytes128 (word_add pt_ptr (word 16));
                  memory :> bytes128 (word_add pt_ptr (word 32));
                  memory :> bytes128 (word_add pt_ptr (word 48));
                  memory :> bytes128 (word_add pt_ptr (word 64))]` THEN
    REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    CONJ_TAC THENL [
    REPEAT (GEN_REWRITE_TAC ONCE_DEPTH_CONV [GSYM SEQ_ASSOC] THEN
            MATCH_MP_TAC SUBSUMED_SEQ THEN REWRITE_TAC[SUBSUMED_REFL]) THEN
    ABBREV_TAC `vallen = val (len:int64)` THEN
    SUBSUMED_MAYCHANGE_TAC; ALL_TAC] THEN

    REWRITE_TAC[byte_list_at] THEN
    ENSURES_INIT_TAC "s0" THEN
    ARM_ACCSTEPS_TAC AES_XTS_DECRYPT_EXEC [] (1--2) THEN

    (* Discharge if condition *)
    SUBGOAL_THEN
      `ival (word_sub (len:int64) (word 0x10)) < &0x0
      <=> ~(ival (len:int64) - &0x10 = ival (word_sub (len:int64) (word 0x10)))` MP_TAC THENL
    [ MP_TAC (BITBLAST_RULE
        `~(val (len:int64) < 0x50) ==> val len < 0x60 ==>
        ival (word_sub len (word 0x10)) >= &0x0`) THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC (BITBLAST_RULE
        `~(val (len:int64) < 0x50) ==> val len < 0x60 ==>
         ival (len:int64) - &0x10 = ival (word_sub len (word 0x10))`) THEN
      ASM_REWRITE_TAC[] THEN
      ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN

    MP_TAC (SPECL [`ct_ptr:int64`; `len:int64`; `ct:byte list`; `s2:armstate`] READ_LT_6BLOCK) THEN
    ASM_SIMP_TAC[] THEN REPEAT STRIP_TAC THEN

    ARM_ACCSTEPS_TAC AES_XTS_DECRYPT_EXEC [] (3--69) THEN
    (* Prove Q6 stores initial tweak *)
    FIRST_X_ASSUM(MP_TAC o SPEC `(calculate_tweak 0 iv key2)`
      o  MATCH_MP (MESON[] `read Q6 s = a ==> !a'. a = a' ==> read Q6 s = a'`)) THEN
    ANTS_TAC THENL
    [ REWRITE_TAC[CONJUNCT1 calculate_tweak; xts_init_tweak] THEN
      EXPAND_TAC "key2" THEN AESENC_TAC; DISCH_TAC] THEN

    (* Simulating until branch for num_blocks adjustment *)
    ARM_ACCSTEPS_TAC AES_XTS_DECRYPT_EXEC [] (70--89) THEN

    (* Case split on whether there is a tail *)
    FIRST_X_ASSUM MP_TAC THEN
    COND_CASES_TAC THENL
    [
      DISCH_TAC THEN

      SUBGOAL_THEN `val (tail_len:int64) = 0` SUBST_ALL_TAC THENL
      [ UNDISCH_TAC `val (word_and (tail_len:int64) (word 0xf)) = 0x0` THEN
        MP_TAC (SPECL [`len:int64`; `tail_len:int64`] TAIL_LEN_BOUND_THM) THEN
        ASM_SIMP_TAC[] THEN DISCH_TAC THEN
        SUBGOAL_THEN `val (word_and (tail_len:int64) (word 15)) = val tail_len` SUBST1_TAC THENL
        [ REWRITE_TAC[VAL_WORD_AND_MASK_WORD; ARITH_RULE `15 = 2 EXP 4 - 1`] THEN
          CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
          IMP_REWRITE_TAC[MOD_LT];
          ALL_TAC] THEN
        SIMP_TAC[]; ALL_TAC] THEN
      CONV_TAC NUM_REDUCE_CONV THEN

      SUBGOAL_THEN `val (num_blocks_adjusted:int64) = 0x50` ASSUME_TAC THENL
      [ EXPAND_TAC "num_blocks_adjusted" THEN
        CONV_TAC NUM_REDUCE_CONV THEN
        ASM_REWRITE_TAC[]
        ; ALL_TAC ] THEN
      SUBGOAL_THEN `val (num_5blocks_adjusted:int64) = 1` ASSUME_TAC THENL
      [ EXPAND_TAC "num_5blocks_adjusted" THEN
        UNDISCH_TAC `val (num_blocks_adjusted:int64) = 0x50` THEN
        SIMP_TAC[] THEN DISCH_TAC THEN
        CONV_TAC NUM_REDUCE_CONV THEN
        REWRITE_TAC[VAL_WORD_1]
        ; ALL_TAC ] THEN
      SUBGOAL_THEN `~(val (word_sub (word_sub (num_blocks:int64) (word 0x50)) (word 0x40)) = 0x0)` ASSUME_TAC THENL
      [ SUBGOAL_THEN `num_blocks:int64 = word 0x50` ASSUME_TAC THENL
        [ UNDISCH_TAC `val (num_blocks:int64) = 0x50` THEN
          WORD_ARITH_TAC; ALL_TAC] THEN
        ASM_REWRITE_TAC[] THEN
        WORD_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `~(val (word_sub (word_sub (num_blocks:int64) (word 0x50)) (word 0x30)) = 0x0)` ASSUME_TAC THENL
      [ SUBGOAL_THEN `num_blocks:int64 = word 0x50` ASSUME_TAC THENL
        [ UNDISCH_TAC `val (num_blocks:int64) = 0x50` THEN
          WORD_ARITH_TAC; ALL_TAC] THEN
        ASM_REWRITE_TAC[] THEN
        WORD_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `~(val (word_sub (word_sub (num_blocks:int64) (word 0x50)) (word 0x20)) = 0x0)` ASSUME_TAC THENL
      [ SUBGOAL_THEN `num_blocks:int64 = word 0x50` ASSUME_TAC THENL
        [ UNDISCH_TAC `val (num_blocks:int64) = 0x50` THEN
          WORD_ARITH_TAC; ALL_TAC] THEN
        ASM_REWRITE_TAC[] THEN
        WORD_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `~(val (word_sub (word_sub (num_blocks:int64) (word 0x50)) (word 0x10)) = 0x0)` ASSUME_TAC THENL
      [ SUBGOAL_THEN `num_blocks:int64 = word 0x50` ASSUME_TAC THENL
        [ UNDISCH_TAC `val (num_blocks:int64) = 0x50` THEN
          WORD_ARITH_TAC; ALL_TAC] THEN
        ASM_REWRITE_TAC[] THEN
        WORD_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `val (word_sub (num_blocks:int64) (word 0x50)) = 0x0` ASSUME_TAC THENL
      [ SUBGOAL_THEN `num_blocks:int64 = word 0x50` ASSUME_TAC THENL
        [ UNDISCH_TAC `val (num_blocks:int64) = 0x50` THEN
          WORD_ARITH_TAC; ALL_TAC] THEN
        ASM_REWRITE_TAC[] THEN
        WORD_ARITH_TAC; ALL_TAC] THEN

      TWEAK_TAC `Q8:(armstate,int128)component` `1:num` `0:num` THEN
      ARM_ACCSTEPS_TAC AES_XTS_DECRYPT_EXEC [] (90--105) THEN
      TWEAK_TAC `Q9:(armstate,int128)component` `2:num` `1:num` THEN
      ARM_ACCSTEPS_TAC AES_XTS_DECRYPT_EXEC [] (106--113) THEN
      TWEAK_TAC `Q10:(armstate,int128)component` `3:num` `2:num` THEN
      ARM_ACCSTEPS_TAC AES_XTS_DECRYPT_EXEC [] (114--119) THEN
      TWEAK_TAC `Q11:(armstate,int128)component` `4:num` `3:num` THEN

      ARM_ACCSTEPS_TAC AES_XTS_DECRYPT_EXEC [] (120--273) THEN
      XTSDEC_TAC `Q0:(armstate,int128)component` `0` `0` THEN
      TWEAK_TAC `Q6:(armstate,int128)component` `5:num` `4:num` THEN

      ARM_ACCSTEPS_TAC AES_XTS_DECRYPT_EXEC [] (274--281) THEN
      XTSDEC_TAC `Q1:(armstate,int128)component` `0x10` `1` THEN
      TWEAK_TAC `Q8:(armstate,int128)component` `6:num` `5:num` THEN

      ARM_ACCSTEPS_TAC AES_XTS_DECRYPT_EXEC [] (282--289) THEN
      XTSDEC_TAC `Q24:(armstate,int128)component` `0x20` `2` THEN
      TWEAK_TAC `Q9:(armstate,int128)component` `7:num` `6:num` THEN

      ARM_ACCSTEPS_TAC AES_XTS_DECRYPT_EXEC [] (290--297) THEN
      XTSDEC_TAC `Q25:(armstate,int128)component` `0x30` `3` THEN
      TWEAK_TAC `Q10:(armstate,int128)component` `8:num` `7:num` THEN

      ARM_ACCSTEPS_TAC AES_XTS_DECRYPT_EXEC [] (298--305) THEN
      XTSDEC_TAC `Q26:(armstate,int128)component` `0x40` `4` THEN
      TWEAK_TAC `Q11:(armstate,int128)component` `9:num` `8:num` THEN

      ARM_ACCSTEPS_TAC AES_XTS_DECRYPT_EXEC [] (306--320) THEN

      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      REPEAT CONJ_TAC THENL
      [
        ASM_REWRITE_TAC[acc_len] THEN CONV_TAC NUM_REDUCE_CONV;
        ASM_REWRITE_TAC[acc_len] THEN CONV_TAC NUM_REDUCE_CONV;
        ASM_REWRITE_TAC[acc_blocks] THEN CONV_TAC NUM_REDUCE_CONV;

        ASM_REWRITE_TAC[acc_len] THEN
        CONV_TAC NUM_REDUCE_CONV THEN
        IMP_REWRITE_TAC[VAL_WORD; DIMINDEX_64; MOD_LT] THEN
        CONV_TAC NUM_REDUCE_CONV THEN
        MP_TAC (SPECL [`0x50:num`; `pt_ptr:int64`; `(aes256_xts_decrypt ct 0x50 iv key1 key2):byte list`;
          `s320:armstate`] BYTE_LIST_TO_NUM_THM) THEN
        ANTS_TAC THENL[
          MP_TAC (SPECL [`5`; `ct:byte list`; `iv:int128`; `key1:int128 list`;
            `key2:int128 list`] LENGTH_OF_AES256_XTS_DECRYPT_FULL_BLOCKS) THEN
          ARITH_TAC; ALL_TAC] THEN
        DISCH_THEN (fun th -> REWRITE_TAC[th]) THEN
        IMP_REWRITE_TAC[READ_BYTES_EQ_READ_BYTE128_5BLOCKS] ]
      ; ALL_TAC
    ] THEN

    (* There is a tail *)
    DISCH_TAC THEN
    (* Prove ~ tail_len = 0 *)
    SUBGOAL_THEN `~(val (tail_len:int64) = 0)` ASSUME_TAC THENL
    [ UNDISCH_TAC `~(val (word_and (tail_len:int64) (word 0xf)) = 0x0)` THEN
      MP_TAC (SPECL [`len:int64`; `tail_len:int64`] TAIL_LEN_BOUND_THM) THEN
      ASM_REWRITE_TAC[] THEN
      SUBST1_TAC(ARITH_RULE `0xf = 2 EXP 4 - 1`) THEN
      REWRITE_TAC[VAL_WORD_AND_MASK_WORD] THEN
      NUM_REDUCE_TAC THEN IMP_REWRITE_TAC[MOD_LT]
    ; ALL_TAC] THEN
    (* Prove num_blocks_adjusted = word_sub num_blocks (word 0x10) *)
    SUBGOAL_THEN `word_sub num_blocks (word 0x10) = num_blocks_adjusted:int64` ASSUME_TAC THENL
    [ UNDISCH_TAC `(if val (tail_len:int64) = 0x0
        then (num_blocks:int64)
        else word_sub num_blocks (word 0x10)) = num_blocks_adjusted` THEN
      ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `val (num_blocks_adjusted:int64) = 0x40` ASSUME_TAC THENL
    [ EXPAND_TAC "num_blocks_adjusted" THEN
      UNDISCH_TAC `val (num_blocks:int64) = 0x50` THEN
      WORD_ARITH_TAC
    ; ALL_TAC ] THEN
    SUBGOAL_THEN `val (num_5blocks_adjusted:int64) = 0` ASSUME_TAC THENL
    [ EXPAND_TAC "num_5blocks_adjusted" THEN
      REWRITE_TAC[ASSUME `val (num_blocks_adjusted:int64) = 0x40`] THEN
      WORD_ARITH_TAC
      ; ALL_TAC ] THEN

    TWEAK_TAC `Q8:(armstate,int128)component` `1:num` `0:num` THEN
    ARM_ACCSTEPS_TAC AES_XTS_DECRYPT_EXEC [] (90--92) THEN
    (* Discharge if condition *)
    SUBGOAL_THEN
      `ival (word_sub (num_blocks_adjusted:int64) (word 0x10)) < &0x0 <=>
      ~(ival (num_blocks_adjusted:int64) - &0x10 =
        ival (word_sub (num_blocks_adjusted:int64) (word 0x10)))` MP_TAC THENL
    [ SUBGOAL_THEN `num_blocks_adjusted:int64 = (word 0x40)` SUBST1_TAC THENL
      [ UNDISCH_TAC `val (num_blocks_adjusted:int64) = 0x40` THEN
        WORD_ARITH_TAC; ALL_TAC] THEN
      WORD_ARITH_TAC
      ; ALL_TAC] THEN
    DISCH_TAC THEN
    POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN

    ARM_ACCSTEPS_TAC AES_XTS_DECRYPT_EXEC [] (93--108) THEN
    TWEAK_TAC `Q9:(armstate,int128)component` `2:num` `1:num` THEN
    ARM_ACCSTEPS_TAC AES_XTS_DECRYPT_EXEC [] (109--116) THEN
    TWEAK_TAC `Q10:(armstate,int128)component` `3:num` `2:num` THEN
    ARM_ACCSTEPS_TAC AES_XTS_DECRYPT_EXEC [] (117--238) THEN
    XTSDEC_TAC `Q0:(armstate,int128)component` `0` `0` THEN
    XTSDEC_TAC `Q1:(armstate,int128)component` `0x10` `1` THEN
    XTSDEC_TAC `Q24:(armstate,int128)component` `0x20` `2` THEN
    XTSDEC_TAC `Q25:(armstate,int128)component` `0x30` `3` THEN
    ARM_ACCSTEPS_TAC AES_XTS_DECRYPT_EXEC [] (239--249) THEN
    TWEAK_TAC `Q6:(armstate,int128)component` `4:num` `3:num` THEN

    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
    [
      ASM_REWRITE_TAC[acc_len] THEN
      CONV_TAC NUM_REDUCE_CONV;
      ASM_REWRITE_TAC[acc_len] THEN
      CONV_TAC NUM_REDUCE_CONV;
      ASM_REWRITE_TAC[acc_blocks] THEN CONV_TAC NUM_REDUCE_CONV;

      ASM_REWRITE_TAC[acc_len] THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      IMP_REWRITE_TAC[VAL_WORD; DIMINDEX_64; MOD_LT] THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      MP_TAC (SPECL [`0x40:num`; `pt_ptr:int64`; `(aes256_xts_decrypt ct 0x40 iv key1 key2):byte list`;
        `s249:armstate`] BYTE_LIST_TO_NUM_THM) THEN
      ANTS_TAC THENL[
        MP_TAC (SPECL [`4`; `ct:byte list`; `iv:int128`;
          `key1:int128 list`; `key2:int128 list`] LENGTH_OF_AES256_XTS_DECRYPT_FULL_BLOCKS) THEN
        ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN (fun th -> REWRITE_TAC[th]) THEN
      IMP_REWRITE_TAC[READ_BYTES_EQ_READ_BYTE128_4BLOCKS]
    ]; ALL_TAC
  ] THEN

  (* Reuse the cipher stealing proof *)
  MP_TAC CIPHER_STEALING_CORRECT THEN
  REWRITE_TAC [(REWRITE_CONV [aes_xts_decrypt_mc] THENC LENGTH_CONV) `LENGTH aes_xts_decrypt_mc`] THEN
  REWRITE_TAC[set_key_schedule; C_ARGUMENTS; SOME_FLAGS;
    NONOVERLAPPING_CLAUSES; byte_list_at;
    MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  EXISTS_TAC `(word 0x50):int64` THEN
  ASM_SIMP_TAC[] THEN
  SUBGOAL_THEN `num_blocks:int64 = word 0x50` ASSUME_TAC THENL
  [ UNDISCH_TAC `val (num_blocks:int64) = 0x50` THEN
    WORD_ARITH_TAC; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL [
    ASM_ARITH_TAC;
    ASM_ARITH_TAC;
    EXPAND_TAC "len" THEN AP_TERM_TAC THEN
    UNDISCH_TAC `val (num_blocks:int64) = 0x50` THEN
    WORD_ARITH_TAC;
    ASM_SIMP_TAC[];
    EXPAND_TAC "num_blocks_adjusted" THEN
    REWRITE_TAC[ASSUME `num_blocks:int64 = word 0x50`]
  ]
);;



let AES_XTS_DECRYPT_CORRECT = time prove(
  `!ct_ptr pt_ptr ct key1_ptr key2_ptr iv_ptr iv len
    k00 k01 k02 k03 k04 k05 k06 k07 k08 k09 k0a k0b k0c k0d k0e
    k10 k11 k12 k13 k14 k15 k16 k17 k18 k19 k1a k1b k1c k1d k1e
    pc.
    nonoverlapping (word pc, LENGTH aes_xts_decrypt_mc) (pt_ptr, val len)
    /\ nonoverlapping (ct_ptr, val len) (pt_ptr, val len)
    /\ nonoverlapping (key1_ptr, 260) (pt_ptr, val len)
    /\ val len >= 16 /\ val len <= 2 EXP 24 /\ LENGTH ct = val len
    ==> ensures arm
    (\s. aligned_bytes_loaded s (word pc) aes_xts_decrypt_mc /\
         read PC s = word (pc + 0x1c) /\
         C_ARGUMENTS [ct_ptr; pt_ptr; len; key1_ptr; key2_ptr; iv_ptr] s /\
         byte_list_at ct ct_ptr len s /\
         read(memory :> bytes128 iv_ptr) s = iv /\
         set_key_schedule s key1_ptr k00 k01 k02 k03 k04 k05 k06 k07 k08 k09 k0a k0b k0c k0d k0e /\
         set_key_schedule s key2_ptr k10 k11 k12 k13 k14 k15 k16 k17 k18 k19 k1a k1b k1c k1d k1e)
    (\s. read PC s = word (pc + 0xb58) /\
         byte_list_at (aes256_xts_decrypt ct (val len) iv
              [k00; k01; k02; k03; k04; k05; k06; k07; k08; k09; k0a; k0b; k0c; k0d; k0e]
              [k10; k11; k12; k13; k14; k15; k16; k17; k18; k19; k1a; k1b; k1c; k1d; k1e])
              pt_ptr len s
         )
    (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI,,
     MAYCHANGE [X19; X20; X21; X22],,
     MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15],,
     MAYCHANGE [memory :> bytes(pt_ptr, val len)])
    `,
    REWRITE_TAC [(REWRITE_CONV [aes_xts_decrypt_mc] THENC LENGTH_CONV) `LENGTH aes_xts_decrypt_mc`] THEN
    REWRITE_TAC[set_key_schedule; C_ARGUMENTS; SOME_FLAGS;
      NONOVERLAPPING_CLAUSES; byte_list_at;
      MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    REPEAT STRIP_TAC THEN

    (* Break len into full blocks and tail *)
    SUBGOAL_THEN `word_add (word_and len (word 0xf))
      (word_and len (word 0xfffffffffffffff0)) = len:int64` ASSUME_TAC THENL
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
    ASM_CASES_TAC `val (len:int64) < 0x60` THENL [
      ASM_CASES_TAC `val (len:int64) < 0x20` THENL
      [
        MP_TAC AES_XTS_DECRYPT_LT_2BLOCK_CORRECT THEN
        REWRITE_TAC [(REWRITE_CONV [aes_xts_decrypt_mc] THENC LENGTH_CONV) `LENGTH aes_xts_decrypt_mc`] THEN
        REWRITE_TAC[set_key_schedule; C_ARGUMENTS; SOME_FLAGS;
          NONOVERLAPPING_CLAUSES; byte_list_at;
          MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
        DISCH_THEN MATCH_MP_TAC THEN
        ASM_SIMP_TAC[];
        ALL_TAC
      ] THEN

      ASM_CASES_TAC `val (len:int64) < 0x30` THENL
      [
        MP_TAC AES_XTS_DECRYPT_LT_3BLOCK_CORRECT THEN
        REWRITE_TAC [(REWRITE_CONV [aes_xts_decrypt_mc] THENC LENGTH_CONV) `LENGTH aes_xts_decrypt_mc`] THEN
        REWRITE_TAC[set_key_schedule; C_ARGUMENTS; SOME_FLAGS;
          NONOVERLAPPING_CLAUSES; byte_list_at;
          MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
        DISCH_THEN MATCH_MP_TAC THEN
        ASM_SIMP_TAC[];
        ALL_TAC
      ] THEN

      ASM_CASES_TAC `val (len:int64) < 0x40` THENL
      [
        MP_TAC AES_XTS_DECRYPT_LT_4BLOCK_CORRECT THEN
        REWRITE_TAC [(REWRITE_CONV [aes_xts_decrypt_mc] THENC LENGTH_CONV) `LENGTH aes_xts_decrypt_mc`] THEN
        REWRITE_TAC[set_key_schedule; C_ARGUMENTS; SOME_FLAGS;
          NONOVERLAPPING_CLAUSES; byte_list_at;
          MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
        DISCH_THEN MATCH_MP_TAC THEN
        ASM_SIMP_TAC[];
        ALL_TAC
      ] THEN

      ASM_CASES_TAC `val (len:int64) < 0x50` THENL
      [
        MP_TAC AES_XTS_DECRYPT_LT_5BLOCK_CORRECT THEN
        REWRITE_TAC [(REWRITE_CONV [aes_xts_decrypt_mc] THENC LENGTH_CONV) `LENGTH aes_xts_decrypt_mc`] THEN
        REWRITE_TAC[set_key_schedule; C_ARGUMENTS; SOME_FLAGS;
          NONOVERLAPPING_CLAUSES; byte_list_at;
          MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
        DISCH_THEN MATCH_MP_TAC THEN
        ASM_SIMP_TAC[];
        ALL_TAC
      ] THEN

      ASM_CASES_TAC `val (len:int64) < 0x60` THENL
      [
        MP_TAC AES_XTS_DECRYPT_LT_6BLOCK_CORRECT THEN
        REWRITE_TAC [(REWRITE_CONV [aes_xts_decrypt_mc] THENC LENGTH_CONV) `LENGTH aes_xts_decrypt_mc`] THEN
        REWRITE_TAC[set_key_schedule; C_ARGUMENTS; SOME_FLAGS;
          NONOVERLAPPING_CLAUSES; byte_list_at;
          MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
        DISCH_THEN MATCH_MP_TAC THEN
        ASM_SIMP_TAC[];
        ALL_TAC
      ] THEN

      ASM_ARITH_TAC
      ; ALL_TAC] THEN

    ABBREV_TAC `num_blocks_adjusted = if val (tail_len:int64) = 0
          then num_blocks else word_sub (num_blocks:int64) (word 0x10)` THEN
    ABBREV_TAC `num_5blocks_adjusted = (word (val (num_blocks_adjusted:int64) DIV 0x50)):int64` THEN

    (* Prove once and for all the bounds for num_blocks, num_blocks_adjusted
       and num_5blocks_adjusted *)
    SUBGOAL_THEN `~(val (num_blocks:int64) < 96)` ASSUME_TAC THENL
    [ UNDISCH_TAC `~(val (len:int64) < 0x60)` THEN
      UNDISCH_TAC `word_and len (word 0xfffffffffffffff0) = (num_blocks:int64)` THEN
      MP_TAC (SPECL [`len:int64`; `num_blocks:int64`] NUM_BLOCKS_LO_BOUND_THM) THEN
      SIMP_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `val (num_blocks:int64) <= 2 EXP 24` ASSUME_TAC THENL
    [ UNDISCH_TAC `val (len:int64) <= 2 EXP 24` THEN
      UNDISCH_TAC `word_and len (word 0xfffffffffffffff0) = (num_blocks:int64)` THEN
      MP_TAC (SPECL [`len:int64`; `num_blocks:int64`] NUM_BLOCKS_HI_BOUND_THM) THEN
      SIMP_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `~(val (num_blocks_adjusted:int64) < 80)` ASSUME_TAC THENL
    [ UNDISCH_TAC `~(val (num_blocks:int64) < 96)` THEN
      UNDISCH_TAC `(if val (tail_len:int64) = 0x0
       then (num_blocks:int64)
       else word_sub num_blocks (word 0x10)) =
       num_blocks_adjusted` THEN
      MP_TAC (SPECL [`num_blocks:int64`;`tail_len:int64`;`num_blocks_adjusted:int64`]
        NUM_BLOCKS_ADJUSTED_LO_BOUND_THM) THEN SIMP_TAC[]
      ; ALL_TAC] THEN
    SUBGOAL_THEN `val (num_blocks_adjusted:int64) <= 2 EXP 24` ASSUME_TAC THENL
    [ UNDISCH_TAC `val (num_blocks:int64) <= 2 EXP 24` THEN
      SUBGOAL_THEN `~(val (num_blocks:int64) < 16)` MP_TAC THENL
      [UNDISCH_TAC `~(val (num_blocks:int64) < 96)` THEN ARITH_TAC; ALL_TAC] THEN
      UNDISCH_TAC `(if val (tail_len:int64) = 0x0
       then (num_blocks:int64)
       else word_sub num_blocks (word 0x10)) =
       num_blocks_adjusted` THEN
      MP_TAC (SPECL [`num_blocks:int64`;`tail_len:int64`;`num_blocks_adjusted:int64`]
        NUM_BLOCKS_ADJUSTED_HI_BOUND_THM) THEN SIMP_TAC[]
      ; ALL_TAC] THEN
    SUBGOAL_THEN `0 < val (num_5blocks_adjusted:int64)` ASSUME_TAC THENL
    [ UNDISCH_TAC `word (val (num_blocks_adjusted:int64) DIV 0x50) = (num_5blocks_adjusted:int64)` THEN
      UNDISCH_TAC `~(val (num_blocks_adjusted:int64) < 0x50)` THEN
      UNDISCH_TAC `val (num_blocks_adjusted:int64) <= 0x2 EXP 0x18` THEN
      MP_TAC (SPECL [`num_blocks_adjusted:int64`; `num_5blocks_adjusted:int64`]
        NUM_5BLOCKS_ADJUSTED_LO_BOUND_THM) THEN SIMP_TAC[]
    ; ALL_TAC] THEN
    SUBGOAL_THEN `val (tail_len:int64) < 16` ASSUME_TAC THENL
    [ EXPAND_TAC "tail_len" THEN
      REWRITE_TAC[ARITH_RULE `0xf = 2 EXP 4 - 1`] THEN
      REWRITE_TAC[VAL_WORD_AND_MASK_WORD] THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      SIMP_TAC[MOD_LT_EQ] THEN
      CONV_TAC NUM_REDUCE_CONV
    ; ALL_TAC] THEN
    (* relationship between variables *)
    SUBGOAL_THEN `val (num_blocks:int64) <= val (len:int64)` ASSUME_TAC THENL
    [ EXPAND_TAC "num_blocks" THEN SIMP_TAC[NUM_BLOCKS_LT_LEN_THM]; ALL_TAC] THEN
    SUBGOAL_THEN `val (num_blocks_adjusted:int64) <= val (len:int64)` ASSUME_TAC THENL
    [ EXPAND_TAC "num_blocks_adjusted" THEN
      COND_CASES_TAC THENL
      [ ASM_SIMP_TAC[];
        SUBGOAL_THEN `~(val (num_blocks:int64) < 16)` MP_TAC THENL
        [UNDISCH_TAC `~(val (num_blocks:int64) < 96)` THEN ARITH_TAC; ALL_TAC] THEN
        UNDISCH_TAC `word_and (len:int64) (word 0xfffffffffffffff0) = (num_blocks:int64)` THEN
        MP_TAC (SPECL [`len:int64`; `num_blocks:int64`] NUM_BLOCKS_ADJUSTED_LT_LEN_THM) THEN
        SIMP_TAC[]]; ALL_TAC] THEN
    SUBGOAL_THEN `val (num_5blocks_adjusted:int64) * 0x50 <= val (num_blocks_adjusted:int64)` ASSUME_TAC THENL
    [ EXPAND_TAC "num_5blocks_adjusted" THEN
      REWRITE_TAC [VAL_WORD; DIMINDEX_64] THEN
      UNDISCH_TAC `val (num_blocks_adjusted:int64) <= 0x2 EXP 0x18` THEN
      ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `val (num_5blocks_adjusted:int64) * 0x50 <= val (len:int64)` ASSUME_TAC THENL
    [ EXPAND_TAC "num_5blocks_adjusted" THEN
      REWRITE_TAC [VAL_WORD; DIMINDEX_64] THEN
      UNDISCH_TAC `val (num_blocks_adjusted:int64) <= 0x2 EXP 0x18` THEN
      UNDISCH_TAC `val (num_blocks_adjusted:int64) <= val (len:int64)` THEN
      ARITH_TAC; ALL_TAC] THEN

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
        byte_list_at ct ct_ptr len s /\
        byte_list_at (aes256_xts_decrypt ct 0 iv key1 key2) pt_ptr (word 0) s /\
        set_key_schedule s key1_ptr k00 k01 k02 k03 k04 k05 k06 k07 k08 k09 k0a k0b k0c k0d k0e` THEN
    CONJ_TAC THENL
    [
      (* ===> Symbolic Simulation: Start symbolic simulation*)
      ENSURES_INIT_TAC "s0" THEN
      ARM_ACCSTEPS_TAC AES_XTS_DECRYPT_EXEC [] (1--2) THEN
      (* Discharge if condition *)
      SUBGOAL_THEN
        `ival (word_sub (len:int64) (word 0x10)) < &0x0
        <=> ~(ival (len:int64) - &0x10 = ival (word_sub (len:int64) (word 0x10)))` MP_TAC THENL
      [
        MP_TAC (BITBLAST_RULE
          `val (len:int64)  >= 0x10 ==> val len <= 2 EXP 0x18 ==>
           ival (word_sub len (word 0x10)) >= &0x0`) THEN
        ASM_REWRITE_TAC[] THEN
        MP_TAC (BITBLAST_RULE
          `val (len:int64)  >= 0x10 ==> val len <= 2 EXP 0x18 ==>
           ival (len:int64) - &0x10 = ival (word_sub len (word 0x10))`) THEN
        ASM_REWRITE_TAC[] THEN
        ARITH_TAC;
        ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
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
        (* Prove val tail_len = 0 and num_blocks = num_blocks_adjusted *)
        SUBGOAL_THEN `val (tail_len:int64) = 0` ASSUME_TAC THENL
        [ UNDISCH_TAC `val (word_and (tail_len:int64) (word 0xf)) = 0x0` THEN
          MP_TAC (SPECL [`len:int64`; `tail_len:int64`] TAIL_LEN_BOUND_THM) THEN
          ASM_REWRITE_TAC[] THEN
          SUBST1_TAC(ARITH_RULE `0xf = 2 EXP 4 - 1`) THEN
          REWRITE_TAC[VAL_WORD_AND_MASK_WORD] THEN
          NUM_REDUCE_TAC THEN IMP_REWRITE_TAC[MOD_LT]; ALL_TAC] THEN
        SUBGOAL_THEN `num_blocks_adjusted:int64 = num_blocks:int64` ASSUME_TAC THENL
        [ UNDISCH_TAC `(if val (tail_len:int64) = 0x0
            then (num_blocks:int64)
            else word_sub num_blocks (word 0x10)) =
            num_blocks_adjusted` THEN
          UNDISCH_TAC `val (tail_len:int64) = 0` THEN
          SIMP_TAC[]; ALL_TAC] THEN
        (* Prove x9, x10 stores lower and upper halves and Q8 stores the full tweak *)
        TWEAK_TAC `Q8:(armstate,int128)component` `1:num` `0:num` THEN
        ARM_ACCSTEPS_TAC AES_XTS_DECRYPT_EXEC [] (90--93) THEN
        (* Prove the optimized udiv is basically udiv *)
        SUBGOAL_THEN `word_ushr
            ((word ((val (num_blocks:int64) * 0xcccccccccccccccd) DIV 0x2 EXP 0x40)):int64)
            0x6 =
          word ((val num_blocks) DIV 0x50)` ASSUME_TAC THENL
        [ MP_TAC (BITBLAST_RULE `val (num_blocks:int64) < 2 EXP 64`) THEN
          REWRITE_TAC[word_ushr] THEN
          MP_TAC (SPECL [`val (num_blocks:int64)`] UDIV_OPT_THM) THEN SIMP_TAC[]
         ; ALL_TAC] THEN
        POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
        (* Eliminate 1 block case *)
        ARM_ACCSTEPS_TAC AES_XTS_DECRYPT_EXEC [] (94--95) THEN
        SUBGOAL_THEN `~(val (num_blocks:int64) < 0x20)` ASSUME_TAC THENL
        [ UNDISCH_TAC `~(val (num_blocks:int64) < 0x60)` THEN ARITH_TAC
          ; POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))] THEN
        (* Eliminate 2 blocks case *)
        ARM_ACCSTEPS_TAC AES_XTS_DECRYPT_EXEC [] (96--97) THEN
        SUBGOAL_THEN `~(val (num_blocks:int64) < 0x30)` ASSUME_TAC THENL
        [ UNDISCH_TAC `~(val (num_blocks:int64) < 0x60)` THEN ARITH_TAC
          ; POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))] THEN
        (* Eliminate 3 blocks case and prove Q9 stores tweak 2 *)
        ARM_ACCSTEPS_TAC AES_XTS_DECRYPT_EXEC [] (98--105) THEN
        SUBGOAL_THEN `~(val (num_blocks:int64) < 0x40)` ASSUME_TAC THENL
        [ UNDISCH_TAC `~(val (num_blocks:int64) < 0x60)` THEN ARITH_TAC
          ; POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))] THEN
        TWEAK_TAC `Q9:(armstate,int128)component` `2:num` `1:num` THEN
        (* Eliminate 4 blocks case and Q10 stores tweak 3 *)
        ARM_ACCSTEPS_TAC AES_XTS_DECRYPT_EXEC [] (106--113) THEN
        SUBGOAL_THEN `~(val (num_blocks:int64) < 0x50)` ASSUME_TAC THENL
        [ UNDISCH_TAC `~(val (num_blocks:int64) < 0x60)` THEN ARITH_TAC
          ; POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))] THEN
        TWEAK_TAC `Q10:(armstate,int128)component` `3:num` `2:num` THEN
        (* Must have 5 blocks, execute until start of loop. Q11 stores tweak 4 *)
        ARM_ACCSTEPS_TAC AES_XTS_DECRYPT_EXEC [] (114--122) THEN
        TWEAK_TAC `Q11:(armstate,int128)component` `4:num` `3:num` THEN
        ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
        REPEAT CONJ_TAC THENL
        [
          EXPAND_TAC "num_5blocks_adjusted" THEN
          EXPAND_TAC "num_blocks_adjusted" THEN
          ASM_REWRITE_TAC[];
          ASM_REWRITE_TAC[byte_list_at];
          REWRITE_TAC[aes256_xts_decrypt] THEN
          CONV_TAC (DEPTH_CONV NUM_RED_CONV) THEN
          ASM_REWRITE_TAC[byte_list_at] THEN
          REWRITE_TAC[VAL_WORD_0] THEN ARITH_TAC;
          ASM_REWRITE_TAC[set_key_schedule]]
        ; ALL_TAC
      ] THEN
      (* If there is a tail *)
      DISCH_TAC THEN
      (* Prove ~ tail_len = 0 *)
      SUBGOAL_THEN `~(val (tail_len:int64) = 0)` ASSUME_TAC THENL
      [ UNDISCH_TAC `~(val (word_and (tail_len:int64) (word 0xf)) = 0x0)` THEN
        MP_TAC (SPECL [`len:int64`; `tail_len:int64`] TAIL_LEN_BOUND_THM) THEN
        ASM_REWRITE_TAC[] THEN
        SUBST1_TAC(ARITH_RULE `0xf = 2 EXP 4 - 1`) THEN
        REWRITE_TAC[VAL_WORD_AND_MASK_WORD] THEN
        NUM_REDUCE_TAC THEN IMP_REWRITE_TAC[MOD_LT]
      ; ALL_TAC] THEN
      (* Prove num_blocks_adjusted = word_sub num_blocks (word 0x10) *)
      SUBGOAL_THEN `word_sub num_blocks (word 0x10) = num_blocks_adjusted:int64` ASSUME_TAC THENL
      [ UNDISCH_TAC `(if val (tail_len:int64) = 0x0
          then (num_blocks:int64)
          else word_sub num_blocks (word 0x10)) = num_blocks_adjusted` THEN
        ASM_REWRITE_TAC[]; ALL_TAC] THEN
      ARM_ACCSTEPS_TAC AES_XTS_DECRYPT_EXEC [] (90--92) THEN
      (* Discharge if condition *)
      SUBGOAL_THEN
        `ival (word_sub (num_blocks_adjusted:int64) (word 0x10)) < &0x0 <=>
        ~(ival (num_blocks_adjusted:int64) - &0x10 =
          ival (word_sub (num_blocks_adjusted:int64) (word 0x10)))` MP_TAC THENL
      [
        MP_TAC (BITBLAST_RULE
          `~(val (num_blocks_adjusted:int64) < 0x50) ==>
           val num_blocks_adjusted <= 2 EXP 0x18 ==>
           ival (word_sub num_blocks_adjusted (word 0x10)) >= &0x0`) THEN
        ASM_REWRITE_TAC[] THEN
        MP_TAC (BITBLAST_RULE
          `~(val (num_blocks_adjusted:int64) < 0x50) ==>
           val num_blocks_adjusted <= 2 EXP 0x18 ==>
           ival (num_blocks_adjusted:int64) - &0x10 = ival (word_sub num_blocks_adjusted (word 0x10))`) THEN
        ASM_REWRITE_TAC[] THEN
        ARITH_TAC;
        ALL_TAC] THEN
      DISCH_TAC THEN
      POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
      (* Prove x9, x10 stores lower and upper halves and Q8 stores the full tweak *)
      TWEAK_TAC `Q8:(armstate,int128)component` `1:num` `0:num` THEN
      ARM_ACCSTEPS_TAC AES_XTS_DECRYPT_EXEC [] (93--96) THEN
      (* Prove the optimized udiv is basically udiv *)
      SUBGOAL_THEN `word_ushr
        ((word ((val (num_blocks_adjusted:int64) * 0xcccccccccccccccd) DIV 0x2 EXP 0x40)):int64)
        0x6 = word ((val num_blocks_adjusted) DIV 0x50)` ASSUME_TAC THENL
      [ MP_TAC (BITBLAST_RULE `val (num_blocks_adjusted:int64) < 2 EXP 64`) THEN
        REWRITE_TAC[word_ushr] THEN
        MP_TAC (SPECL [`val (num_blocks_adjusted:int64)`] UDIV_OPT_THM) THEN SIMP_TAC[]
        ; ALL_TAC] THEN
      POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
      (* Eliminate 1 block case *)
      ARM_ACCSTEPS_TAC AES_XTS_DECRYPT_EXEC [] (97--98) THEN
      SUBGOAL_THEN `~(val (num_blocks_adjusted:int64) < 0x20)` ASSUME_TAC THENL
      [ UNDISCH_TAC `~(val (num_blocks_adjusted:int64) < 0x50)` THEN ARITH_TAC
      ; POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))] THEN
      (* Eliminate 2 blocks case *)
      ARM_ACCSTEPS_TAC AES_XTS_DECRYPT_EXEC [] (99--100) THEN
      SUBGOAL_THEN `~(val (num_blocks_adjusted:int64) < 0x30)` ASSUME_TAC THENL
      [ UNDISCH_TAC `~(val (num_blocks_adjusted:int64) < 0x50)` THEN ARITH_TAC
      ; POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))] THEN
      (* Eliminate 3 blocks case and prove Q9 stores tweak 2 *)
      ARM_ACCSTEPS_TAC AES_XTS_DECRYPT_EXEC [] (101--108) THEN
      SUBGOAL_THEN `~(val (num_blocks_adjusted:int64) < 0x40)` ASSUME_TAC THENL
      [ UNDISCH_TAC `~(val (num_blocks_adjusted:int64) < 0x50)` THEN ARITH_TAC
      ; POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))] THEN
      TWEAK_TAC `Q9:(armstate,int128)component` `2:num` `1:num` THEN
      (* Eliminate 4 blocks case and Q10 stores tweak 3 *)
      ARM_ACCSTEPS_TAC AES_XTS_DECRYPT_EXEC [] (109--116) THEN
      TWEAK_TAC `Q10:(armstate,int128)component` `3:num` `2:num` THEN
      (* Must have 5 blocks, execute until start of loop. Q11 stores tweak 4 *)
      ARM_ACCSTEPS_TAC AES_XTS_DECRYPT_EXEC [] (117--125) THEN
      TWEAK_TAC `Q11:(armstate,int128)component` `4:num` `3:num` THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      REPEAT CONJ_TAC THENL
      [ ASM_REWRITE_TAC[byte_list_at];
        REWRITE_TAC[aes256_xts_decrypt] THEN
        CONV_TAC (DEPTH_CONV NUM_RED_CONV) THEN
        ASM_REWRITE_TAC[byte_list_at] THEN
        REWRITE_TAC [VAL_WORD_0] THEN ARITH_TAC;
        ASM_REWRITE_TAC[set_key_schedule]]
      ; ALL_TAC
    ] THEN

    (* Prove property until right before cipher stealing *)
    ENSURES_SEQUENCE_TAC `pc + 0xa0c`
    `\s.
        read X0 s = word_add ct_ptr (word (acc_len num_5blocks_adjusted num_blocks_adjusted)) /\
        read X1 s = word_add pt_ptr (word (acc_len num_5blocks_adjusted num_blocks_adjusted)) /\
        read X3 s = key1_ptr /\
        read X21 s = tail_len /\
        read Q6 s = calculate_tweak (acc_blocks num_5blocks_adjusted num_blocks_adjusted T) iv key2 /\
        read X19 s = word 0x87 /\
        read Q16 s = k00 /\ read Q17 s = k01 /\ read Q12 s = k02 /\ read Q13 s = k03 /\
        read Q14 s = k04 /\ read Q15 s = k05 /\ read Q4 s = k06 /\ read Q5 s = k07 /\
        read Q18 s = k08 /\ read Q19 s = k09 /\ read Q20 s = k0a /\ read Q21 s = k0b /\
        read Q22 s = k0c /\ read Q23 s = k0d /\ read Q7 s = k0e /\
        byte_list_at ct ct_ptr len s /\
        byte_list_at (aes256_xts_decrypt ct (acc_len num_5blocks_adjusted num_blocks_adjusted) iv key1 key2)
           pt_ptr (word (acc_len num_5blocks_adjusted num_blocks_adjusted)) s` THEN
    CONJ_TAC THENL
    [
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
         byte_list_at ct ct_ptr len s /\
         byte_list_at (aes256_xts_decrypt ct (80 * i) iv key1 key2) pt_ptr (word (80 * i)) s) /\
        // loop backedge condition
        (read ZF s <=> i = val (num_5blocks_adjusted:int64))` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
    [
      (* Subgoal 1. Bound of loop is not zero -- automatically discharged by asm *)
      (* Subgoal 2. Invariant holds before entering the loop *)
      REWRITE_TAC[byte_list_at] THEN
      ENSURES_INIT_TAC "s0" THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      REPEAT CONJ_TAC THENL
      [
        WORD_ARITH_TAC; WORD_ARITH_TAC;
        WORD_ARITH_TAC; WORD_ARITH_TAC;
        CONV_TAC NUM_REDUCE_CONV;
        CONV_TAC NUM_REDUCE_CONV;
        CONV_TAC NUM_REDUCE_CONV;
        CONV_TAC NUM_REDUCE_CONV;
        CONV_TAC NUM_REDUCE_CONV;
        CONV_TAC NUM_REDUCE_CONV;
        CONV_TAC NUM_REDUCE_CONV;
        CONV_TAC (ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN REWRITE_TAC[VAL_WORD_0] THEN ARITH_TAC
      ];

      (* Subgoal 3: loop body *)
      REPEAT STRIP_TAC THEN

      (* An arithmetic rule for discharging subgoal in the following ENSURES_FRAME_SUBSUMED tactic *)
      SUBGOAL_THEN `i * 0x50 + 0x50 <= val (len:int64)` ASSUME_TAC THENL
      [ SUBGOAL_THEN `i + 1 <= val (num_5blocks_adjusted:int64)` MP_TAC THENL
          [ASM_ARITH_TAC; ALL_TAC] THEN
        SUBGOAL_THEN `(i + 1) * 0x50 <= val (len:int64)` MP_TAC THENL
          [ASM_ARITH_TAC; ALL_TAC] THEN
        ARITH_TAC; ALL_TAC] THEN

      MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN
      EXISTS_TAC `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
          MAYCHANGE [X19; X20; X21; X22],,
          MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15],,
          MAYCHANGE [memory :> bytes128 (word_add pt_ptr (word (0x50 * i)));
                     memory :> bytes128 (word_add pt_ptr (word (0x50 * i + 0x10)));
                     memory :> bytes128 (word_add pt_ptr (word (0x50 * i + 0x20)));
                     memory :> bytes128 (word_add pt_ptr (word (0x50 * i + 0x30)));
                     memory :> bytes128 (word_add pt_ptr (word (0x50 * i + 0x40)))]` THEN
      REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
      CONJ_TAC THENL [
        REPEAT (GEN_REWRITE_TAC ONCE_DEPTH_CONV [GSYM SEQ_ASSOC] THEN
                MATCH_MP_TAC SUBSUMED_SEQ THEN REWRITE_TAC[SUBSUMED_REFL]) THEN
        ABBREV_TAC `vallen = val (len:int64)` THEN
        SUBSUMED_MAYCHANGE_TAC; ALL_TAC] THEN

      (* ===> Symbolic Simulation: Start symbolic simulation*)
      ASM_REWRITE_TAC[byte_list_at] THEN

      ENSURES_INIT_TAC "s0" THEN
      (* List values for ct_ptr + [0 .. 0x40] *)
      MP_TAC (SPECL [`ct_ptr:int64`; `i:num`; `len:int64`; `ct:byte list`; `s0:armstate`] READ_BL_LEMMA) THEN
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

      (* The following lemmas are for NONSELFMODIFYING_STATE_UPDATE_TAC when store back to pt_ptr,
         and for the MAYCHANGE clauses *)
      RULE_ASSUM_TAC(REWRITE_RULE
        [WORD_RULE `word_mul (word 0x50) (word i):int64 = word(0x50 * i)`]) THEN

      (* Rewrite to help reasoning about nonoverlapping
         so that the universally quantified assumption stays.
         See: https://hol-light.zulipchat.com/#narrow/channel/474190-s2n-bignum/topic/.E2.9C.94.20Symbolic.20simulation.20removed.20assumption/with/541554894 *)
      SUBGOAL_THEN `val ((word (0x50 * i)):int64) = 0x50 * i` ASSUME_TAC THENL [
        IMP_REWRITE_TAC[VAL_WORD; DIMINDEX_64; MOD_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
      POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN

      (* Simulate until end of loop *)
      ARM_ACCSTEPS_TAC AES_XTS_DECRYPT_EXEC [] (184--188) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      REPEAT CONJ_TAC THENL
      [ REWRITE_TAC[WORD_RULE `word_mul (word 0x50) (word (i + 1)):int64 = word_add (word(0x50 * i)) (word 0x50)`] THEN
        REWRITE_TAC[WORD_ADD_ASSOC];
        REWRITE_TAC[WORD_RULE `word_mul (word 0x50) (word (i + 1)):int64 = word_add (word(0x50 * i)) (word 0x50)`] THEN
        REWRITE_TAC[WORD_ADD_ASSOC];
        REWRITE_TAC[WORD_RULE `word_mul (word 0x50) (word (i + 1)):int64 = word_add (word(0x50 * i)) (word 0x50)`] THEN
        CONV_TAC WORD_RULE;
        CONV_TAC WORD_RULE;
        REWRITE_TAC[WORD_RULE `(i + 0x1) * 0x5 = i * 0x5 + 0x5`];
        REWRITE_TAC[WORD_RULE `(i + 0x1) * 0x5 + 0x1 = i * 0x5 + 0x6`];
        REWRITE_TAC[WORD_RULE `(i + 0x1) * 0x5 + 0x2 = i * 0x5 + 0x7`];
        REWRITE_TAC[WORD_RULE `(i + 0x1) * 0x5 + 0x3 = i * 0x5 + 0x8`];
        REWRITE_TAC[WORD_RULE `(i + 0x1) * 0x5 + 0x4 = i * 0x5 + 0x9`];
        REWRITE_TAC[WORD_RULE `(i + 0x1) * 0x5 + 0x4 = i * 0x5 + 0x9`];
        REWRITE_TAC[WORD_RULE `(i + 0x1) * 0x5 + 0x4 = i * 0x5 + 0x9`];
        (* The following is the main proof for inductive step *)
        REWRITE_TAC[ARITH_RULE `0x50 * (i + 0x1) = 0x50 * i + 0x50`] THEN
        SUBGOAL_THEN `val ((word (0x50 * i + 0x50)):int64) = 0x50 * i + 0x50` ASSUME_TAC THENL [
          IMP_REWRITE_TAC[VAL_WORD; DIMINDEX_64; MOD_LT] THEN
          UNDISCH_TAC `i * 0x50 + 0x50 <= val (len:int64)` THEN
          UNDISCH_TAC `val (len:int64) <= 2 EXP 24` THEN
          ARITH_TAC; ALL_TAC] THEN
        ASM_REWRITE_TAC[] THEN

        (* Remove quantifier *)
        UNDISCH_TAC
        `forall i'.
          i' < 0x50 * i
          ==> read (memory :> bytes8 (word_add pt_ptr (word i'))) s188 =
              EL i' (aes256_xts_decrypt ct (0x50 * i) iv key1 key2)` THEN
        MP_TAC (SPECL [`0x50 * i + 0x50:num`; `pt_ptr:int64`; `(aes256_xts_decrypt ct (0x50 * i + 0x50) iv key1 key2):byte list`; `s188:armstate`] BYTE_LIST_TO_NUM_THM) THEN
        ANTS_TAC THENL[
          REWRITE_TAC[ARITH_RULE `0x50 * i + 0x50 = 0x10 * (5 * i + 5)`;
                      LENGTH_OF_AES256_XTS_DECRYPT_FULL_BLOCKS] THEN
          ARITH_TAC
          ; ALL_TAC] THEN
        DISCH_THEN (fun th -> REWRITE_TAC[th]) THEN
        MP_TAC (SPECL [`0x50 * i:num`; `pt_ptr:int64`; `(aes256_xts_decrypt ct (0x50 * i) iv key1 key2):byte list`; `s188:armstate`] BYTE_LIST_TO_NUM_THM) THEN
        ANTS_TAC THENL[
          REWRITE_TAC[ARITH_RULE `0x50 * i = 0x10 * 5 * i`;
                      LENGTH_OF_AES256_XTS_DECRYPT_FULL_BLOCKS] THEN
          ARITH_TAC
          ; ALL_TAC] THEN
        DISCH_THEN (fun th -> REWRITE_TAC[th]) THEN
        DISCH_TAC THEN

        (* Prove one block equivalence and reduce proving the following:
           `read (memory :> bytes (pt_ptr,0x50 * i + 0x50)) s188 =
            num_of_bytelist
             (aes256_xts_decrypt ct (0x50 * i + 0x50) iv key1 key2)`
           to:
          `read (memory :> bytes (pt_ptr,0x10 * 0x5 * i + 0x40)) s188 =
           num_of_bytelist
            (aes256_xts_decrypt ct (0x10 * 0x5 * i + 0x40) iv key1 key2)` *)
        IMP_REWRITE_TAC[ARITH_RULE `0x50 * i + 0x50 = (0x50 * i + 0x40) + 0x10`; READ_BYTES_AND_BYTE128_SPLIT] THEN
        EXISTS_TAC `(aes256_xts_decrypt ct (0x50 * i + 0x50) iv key1 key2)` THEN
        REPEAT CONJ_TAC THENL [
          REWRITE_TAC [ARITH_RULE `(0x50 * i + 0x40) + 0x10 = 0x50 * i + 0x50`];

          MP_TAC (SPECL [`0x5 * i + 0x5:num`; `ct:byte list`; `iv:int128`; `key1:int128 list`;
            `key2:int128 list`] LENGTH_OF_AES256_XTS_DECRYPT_FULL_BLOCKS) THEN
          REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_ASSOC; GSYM ADD_ASSOC] THEN
          CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
          IMP_REWRITE_TAC[SUB_LIST_LENGTH_IMPLIES] THEN ARITH_TAC;

          (* Establish that one xts decrypt round is the same as
             selecting one block of bytes from calling the top-level function. *)
          REWRITE_TAC[aes256_xts_decrypt] THEN
          SIMP_TAC[ARITH_RULE `~(0x50 * i + 0x50 < 0x10)`] THEN
          SUBGOAL_THEN `(0x50 * i + 0x50) MOD 0x10 = 0` SUBST1_TAC THENL
          [ REWRITE_TAC[ARITH_RULE `80 * i + 80 = 16 * (5 * i + 5)`] THEN
            REWRITE_TAC[MOD_MULT]
           ; ALL_TAC] THEN
          CONV_TAC (DEPTH_CONV let_CONV) THEN
          REWRITE_TAC[SUB_0; ARITH_RULE `(0x50 * i + 0x50) DIV 0x10 = 0x5 * i + 0x5`] THEN
          SIMP_TAC[ARITH_RULE `~(0x5 * i + 0x5 < 0x2)`;
                   ARITH_RULE `(0x5 * i + 0x5) - 0x2 = 0x5 * i + 0x3`;
                   ARITH_RULE `(0x5 * i + 0x5) - 0x1 = 0x5 * i + 0x4`] THEN

          MP_TAC (SPECL [`0`;`5 * i + 3:num`; `ct:byte list`; `iv:int128`; `key1:int128 list`; `key2:int128 list`]
            LENGTH_OF_AES256_XTS_DECRYPT_REC) THEN
          SIMP_TAC[ARITH_RULE `~(5 * i + 3 < 0)`;
                   ARITH_RULE `((0x5 * i + 0x3) - 0x0 + 0x1) * 0x10 = 0x50 * i + 0x40`] THEN
          IMP_REWRITE_TAC[SUB_LIST_APPEND_RIGHT_LEMMA] THEN DISCH_TAC THEN

          MP_TAC (SPECL [`5 * i + 4:num`; `0x0:num`; `ct:byte list`; `iv:int128`; `key1:int128 list`; `key2:int128 list`]
            LENGTH_OF_AES256_XTS_DECRYPT_TAIL) THEN
          CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[ADD_0] THEN DISCH_TAC THEN
          IMP_REWRITE_TAC[SUB_LIST_LENGTH_IMPLIES] THEN

          REWRITE_TAC[AES256_XTS_DECRYPT_TAIL_WHEN_1BLOCK] THEN
          SIMP_TAC[ARITH_RULE `i * 0x50 + 0x40 = (i * 0x5 + 0x4) * 0x10`;
                   ARITH_RULE `i * 0x5 = 0x5 * i`];

          (* Proving that reading previous bytes is the same as the spec *)
          REWRITE_TAC[ARITH_RULE `0x50 * i + 0x40 = 0x10 * (5 * i + 4)`;
                      ARITH_RULE `0x50 * i + 0x50 = 0x10 * (5 * i + 4) + 0x10`] THEN
          REWRITE_TAC[SUB_LIST_OF_AES256_XTS_DECRYPT_FULL_BLOCKS] THEN
          ASM_REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_ASSOC] THEN CONV_TAC NUM_REDUCE_CONV
        ] THEN

        IMP_REWRITE_TAC[ARITH_RULE `0x50 * i + 0x40 = (0x50 * i + 0x30) + 0x10`; READ_BYTES_AND_BYTE128_SPLIT] THEN
        EXISTS_TAC `(aes256_xts_decrypt ct (0x50 * i + 0x40) iv key1 key2)` THEN
        REPEAT CONJ_TAC THENL [
          REWRITE_TAC [ARITH_RULE `(0x50 * i + 0x30) + 0x10 = 0x50 * i + 0x40`] THEN

          MP_TAC (SPECL [`0x5 * i + 0x4:num`; `ct:byte list`; `iv:int128`; `key1:int128 list`;
            `key2:int128 list`] LENGTH_OF_AES256_XTS_DECRYPT_FULL_BLOCKS) THEN
          REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_ASSOC; GSYM ADD_ASSOC] THEN
          CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
          IMP_REWRITE_TAC[SUB_LIST_LENGTH_IMPLIES];

          MP_TAC (SPECL [`0x5 * i + 0x4:num`; `ct:byte list`; `iv:int128`; `key1:int128 list`;
            `key2:int128 list`] LENGTH_OF_AES256_XTS_DECRYPT_FULL_BLOCKS) THEN
          REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_ASSOC; GSYM ADD_ASSOC] THEN
          CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
          IMP_REWRITE_TAC[SUB_LIST_LENGTH_IMPLIES] THEN ARITH_TAC;

          (* Establish that one xts decrypt round is the same as
             selecting one block of bytes from calling the top-level function. *)
          REWRITE_TAC[aes256_xts_decrypt] THEN
          SIMP_TAC[ARITH_RULE `~(0x50 * i + 0x40 < 0x10)`] THEN
          SUBGOAL_THEN `(0x50 * i + 0x40) MOD 0x10 = 0` SUBST1_TAC THENL
          [ REWRITE_TAC[ARITH_RULE `80 * i + 64 = 16 * (5 * i + 4)`] THEN
            REWRITE_TAC[MOD_MULT]
           ; ALL_TAC] THEN
          CONV_TAC (DEPTH_CONV let_CONV) THEN
          REWRITE_TAC[SUB_0; ARITH_RULE `(0x50 * i + 0x40) DIV 0x10 = 0x5 * i + 0x4`] THEN
          SIMP_TAC[ARITH_RULE `~(0x5 * i + 0x4 < 0x2)`;
                   ARITH_RULE `(0x5 * i + 0x4) - 0x2 = 0x5 * i + 0x2`;
                   ARITH_RULE `(0x5 * i + 0x4) - 0x1 = 0x5 * i + 0x3`] THEN

          MP_TAC (SPECL [`0`;`5 * i + 2:num`; `ct:byte list`; `iv:int128`; `key1:int128 list`; `key2:int128 list`]
            LENGTH_OF_AES256_XTS_DECRYPT_REC) THEN
          SIMP_TAC[ARITH_RULE `~(5 * i + 2 < 0)`;
                   ARITH_RULE `((0x5 * i + 0x2) - 0x0 + 0x1) * 0x10 = 0x50 * i + 0x30`] THEN
          IMP_REWRITE_TAC[SUB_LIST_APPEND_RIGHT_LEMMA] THEN DISCH_TAC THEN

          MP_TAC (SPECL [`5 * i + 3:num`; `0x0:num`; `ct:byte list`; `iv:int128`; `key1:int128 list`; `key2:int128 list`]
            LENGTH_OF_AES256_XTS_DECRYPT_TAIL) THEN
          CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[ADD_0] THEN DISCH_TAC THEN
          IMP_REWRITE_TAC[SUB_LIST_LENGTH_IMPLIES] THEN

          REWRITE_TAC[AES256_XTS_DECRYPT_TAIL_WHEN_1BLOCK] THEN
          SIMP_TAC[ARITH_RULE `i * 0x50 + 0x30= (i * 0x5 + 0x3) * 0x10`;
                   ARITH_RULE `i * 0x5 = 0x5 * i`];

          (* Proving that reading previous bytes is the same as the spec *)
          REWRITE_TAC[ARITH_RULE `0x50 * i + 0x30 = 0x10 * (5 * i + 3)`;
                      ARITH_RULE `0x50 * i + 0x40 = 0x10 * (5 * i + 3) + 0x10`] THEN
          REWRITE_TAC[SUB_LIST_OF_AES256_XTS_DECRYPT_FULL_BLOCKS] THEN
          ASM_REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_ASSOC] THEN CONV_TAC NUM_REDUCE_CONV
        ] THEN

        IMP_REWRITE_TAC[ARITH_RULE `0x50 * i + 0x30 = (0x50 * i + 0x20) + 0x10`; READ_BYTES_AND_BYTE128_SPLIT] THEN
        EXISTS_TAC `(aes256_xts_decrypt ct (0x50 * i + 0x30) iv key1 key2)` THEN
        REPEAT CONJ_TAC THENL [
          REWRITE_TAC [ARITH_RULE `(0x50 * i + 0x20) + 0x10 = 0x50 * i + 0x30`] THEN

          MP_TAC (SPECL [`0x5 * i + 0x3:num`; `ct:byte list`; `iv:int128`; `key1:int128 list`;
            `key2:int128 list`] LENGTH_OF_AES256_XTS_DECRYPT_FULL_BLOCKS) THEN
          REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_ASSOC; GSYM ADD_ASSOC] THEN
          CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
          IMP_REWRITE_TAC[SUB_LIST_LENGTH_IMPLIES];

          MP_TAC (SPECL [`0x5 * i + 0x3:num`; `ct:byte list`; `iv:int128`; `key1:int128 list`;
            `key2:int128 list`] LENGTH_OF_AES256_XTS_DECRYPT_FULL_BLOCKS) THEN
          REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_ASSOC; GSYM ADD_ASSOC] THEN
          CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
          IMP_REWRITE_TAC[SUB_LIST_LENGTH_IMPLIES] THEN ARITH_TAC;

          (* Establish that one xts decrypt round is the same as
             selecting one block of bytes from calling the top-level function. *)
          REWRITE_TAC[aes256_xts_decrypt] THEN
          SIMP_TAC[ARITH_RULE `~(0x50 * i + 0x30 < 0x10)`] THEN
          SUBGOAL_THEN `(0x50 * i + 0x30) MOD 0x10 = 0` SUBST1_TAC THENL
          [ REWRITE_TAC[ARITH_RULE `80 * i + 48 = 16 * (5 * i + 3)`] THEN
            REWRITE_TAC[MOD_MULT]
           ; ALL_TAC] THEN
          CONV_TAC (DEPTH_CONV let_CONV) THEN
          REWRITE_TAC[SUB_0; ARITH_RULE `(0x50 * i + 0x30) DIV 0x10 = 0x5 * i + 0x3`] THEN
          SIMP_TAC[ARITH_RULE `~(0x5 * i + 0x3 < 0x2)`;
                   ARITH_RULE `(0x5 * i + 0x3) - 0x2 = 0x5 * i + 0x1`;
                   ARITH_RULE `(0x5 * i + 0x3) - 0x1 = 0x5 * i + 0x2`] THEN

          MP_TAC (SPECL [`0`;`5 * i + 1:num`; `ct:byte list`; `iv:int128`; `key1:int128 list`; `key2:int128 list`]
            LENGTH_OF_AES256_XTS_DECRYPT_REC) THEN
          SIMP_TAC[ARITH_RULE `~(5 * i + 1 < 0)`] THEN
          REWRITE_TAC[ARITH_RULE `((0x5 * i + 0x1) - 0x0 + 0x1) * 0x10 = 0x50 * i + 0x20`] THEN
          IMP_REWRITE_TAC[SUB_LIST_APPEND_RIGHT_LEMMA] THEN DISCH_TAC THEN

          MP_TAC (SPECL [`5 * i + 2:num`; `0x0:num`; `ct:byte list`; `iv:int128`; `key1:int128 list`; `key2:int128 list`]
            LENGTH_OF_AES256_XTS_DECRYPT_TAIL) THEN
          CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[ADD_0] THEN DISCH_TAC THEN
          IMP_REWRITE_TAC[SUB_LIST_LENGTH_IMPLIES] THEN

          REWRITE_TAC[AES256_XTS_DECRYPT_TAIL_WHEN_1BLOCK] THEN
          SIMP_TAC[ARITH_RULE `i * 0x50 + 0x20 = (i * 0x5 + 0x2) * 0x10`;
                   ARITH_RULE `i * 0x5 = 0x5 * i`];

          (* Proving that reading previous bytes is the same as the spec *)
          REWRITE_TAC[ARITH_RULE `0x50 * i + 0x20 = 0x10 * (5 * i + 2)`;
                      ARITH_RULE `0x50 * i + 0x30 = 0x10 * (5 * i + 2) + 0x10`] THEN
          REWRITE_TAC[SUB_LIST_OF_AES256_XTS_DECRYPT_FULL_BLOCKS] THEN
          ASM_REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_ASSOC] THEN CONV_TAC NUM_REDUCE_CONV
        ] THEN

        REWRITE_TAC[ARITH_RULE `0x50 * i + 0x20 = (0x50 * i + 0x10) + 0x10`] THEN
        (* Use SPECL to force IMP_REWRITE_TAC to apply once once *)
        IMP_REWRITE_TAC[(SPECL [`pt_ptr:int64`; `(0x50 * i + 0x10):num`;
          `x:byte list`; `s188:armstate`] READ_BYTES_AND_BYTE128_SPLIT)] THEN
        EXISTS_TAC `(aes256_xts_decrypt ct (0x50 * i + 0x20) iv key1 key2)` THEN
        REPEAT CONJ_TAC THENL [
          REWRITE_TAC [ARITH_RULE `(0x50 * i + 0x10) + 0x10 = 0x50 * i + 0x20`] THEN

          MP_TAC (SPECL [`0x5 * i + 0x2:num`; `ct:byte list`; `iv:int128`; `key1:int128 list`;
            `key2:int128 list`] LENGTH_OF_AES256_XTS_DECRYPT_FULL_BLOCKS) THEN
          REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_ASSOC; GSYM ADD_ASSOC] THEN
          CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
          IMP_REWRITE_TAC[SUB_LIST_LENGTH_IMPLIES] THEN ARITH_TAC;

          MP_TAC (SPECL [`0x5 * i + 0x2:num`; `ct:byte list`; `iv:int128`; `key1:int128 list`;
            `key2:int128 list`] LENGTH_OF_AES256_XTS_DECRYPT_FULL_BLOCKS) THEN
          REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_ASSOC; GSYM ADD_ASSOC] THEN
          CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
          IMP_REWRITE_TAC[SUB_LIST_LENGTH_IMPLIES] THEN ARITH_TAC;

          (* Establish that one xts decrypt round is the same as
             selecting one block of bytes from calling the top-level function. *)
          REWRITE_TAC[aes256_xts_decrypt] THEN
          SIMP_TAC[ARITH_RULE `~(0x50 * i + 0x20 < 0x10)`] THEN
          SUBGOAL_THEN `(0x50 * i + 0x20) MOD 0x10 = 0` SUBST1_TAC THENL
          [ REWRITE_TAC[ARITH_RULE `80 * i + 32 = 16 * (5 * i + 2)`] THEN
            REWRITE_TAC[MOD_MULT]
           ; ALL_TAC] THEN
          CONV_TAC (DEPTH_CONV let_CONV) THEN
          REWRITE_TAC[SUB_0; ARITH_RULE `(0x50 * i + 0x20) DIV 0x10 = 0x5 * i + 0x2`] THEN
          SIMP_TAC[ARITH_RULE `~(0x5 * i + 0x2 < 0x2)`;
                   ARITH_RULE `(0x5 * i + 0x2) - 0x2 = 0x5 * i`;
                   ARITH_RULE `(0x5 * i + 0x2) - 0x1 = 0x5 * i + 0x1`] THEN

          MP_TAC (SPECL [`0`;`5 * i:num`; `ct:byte list`; `iv:int128`; `key1:int128 list`; `key2:int128 list`]
            LENGTH_OF_AES256_XTS_DECRYPT_REC) THEN
          SIMP_TAC[ARITH_RULE `~(5 * i < 0)`;
                   ARITH_RULE `(0x5 * i - 0x0 + 0x1) * 0x10 = 0x50 * i + 0x10`] THEN
          IMP_REWRITE_TAC[SUB_LIST_APPEND_RIGHT_LEMMA] THEN DISCH_TAC THEN

          MP_TAC (SPECL [`5 * i + 1:num`; `0x0:num`; `ct:byte list`; `iv:int128`; `key1:int128 list`; `key2:int128 list`]
            LENGTH_OF_AES256_XTS_DECRYPT_TAIL) THEN
          CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[ADD_0] THEN DISCH_TAC THEN
          IMP_REWRITE_TAC[SUB_LIST_LENGTH_IMPLIES] THEN

          REWRITE_TAC[AES256_XTS_DECRYPT_TAIL_WHEN_1BLOCK] THEN
          SIMP_TAC[ARITH_RULE `i * 0x50 + 0x10 = (i * 0x5 + 0x1) * 0x10`;
                   ARITH_RULE `i * 0x5 = 0x5 * i`];

          (* Proving that reading previous bytes is the same as the spec *)
          REWRITE_TAC[ARITH_RULE `0x50 * i + 0x10 = 0x10 * (5 * i + 1)`;
                      ARITH_RULE `0x50 * i + 0x20 = 0x10 * (5 * i + 1) + 0x10`] THEN
          REWRITE_TAC[SUB_LIST_OF_AES256_XTS_DECRYPT_FULL_BLOCKS] THEN
          ASM_REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_ASSOC] THEN CONV_TAC NUM_REDUCE_CONV
        ] THEN

        IMP_REWRITE_TAC[(SPECL [`pt_ptr:int64`; `(0x50 * i):num`;
          `(aes256_xts_decrypt ct (0x50 * i + 0x10) iv key1 key2):byte list`; `s188:armstate`]
          READ_BYTES_AND_BYTE128_SPLIT)] THEN
        EXISTS_TAC `ct:byte list` THEN EXISTS_TAC `iv:int128` THEN
        EXISTS_TAC `key1:int128 list` THEN EXISTS_TAC `key2:int128 list` THEN
        REPEAT CONJ_TAC THENL [
          MP_TAC (SPECL [`0x5 * i + 0x1:num`; `ct:byte list`; `iv:int128`; `key1:int128 list`;
            `key2:int128 list`] LENGTH_OF_AES256_XTS_DECRYPT_FULL_BLOCKS) THEN
          REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_ASSOC; GSYM ADD_ASSOC] THEN
          CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
          IMP_REWRITE_TAC[SUB_LIST_LENGTH_IMPLIES] THEN ARITH_TAC;

          MP_TAC (SPECL [`0x5 * i + 0x1:num`; `ct:byte list`; `iv:int128`; `key1:int128 list`;
            `key2:int128 list`] LENGTH_OF_AES256_XTS_DECRYPT_FULL_BLOCKS) THEN
          REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_ASSOC; GSYM ADD_ASSOC] THEN
          CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
          IMP_REWRITE_TAC[SUB_LIST_LENGTH_IMPLIES] THEN ARITH_TAC;

          (* Establish that one xts decrypt round is the same as
             selecting one block of bytes from calling the top-level function. *)
          REWRITE_TAC[aes256_xts_decrypt] THEN
          SIMP_TAC[ARITH_RULE `~(0x50 * i + 0x10 < 0x10)`] THEN
          SUBGOAL_THEN `(0x50 * i + 0x10) MOD 0x10 = 0` SUBST1_TAC THENL
          [ REWRITE_TAC[ARITH_RULE `80 * i + 16 = 16 * (5 * i + 1)`] THEN
            REWRITE_TAC[MOD_MULT]
           ; ALL_TAC] THEN
          CONV_TAC (DEPTH_CONV let_CONV) THEN
          REWRITE_TAC[SUB_0; ARITH_RULE `(0x50 * i + 0x10) DIV 0x10 = 0x5 * i + 0x1`] THEN
          (* Two cases: i = 0 then execute tail branch, else execute recursion branch *)
          COND_CASES_TAC THENL
          [ SUBGOAL_THEN `i = 0` SUBST1_TAC THENL
            [ UNDISCH_TAC `5 * i + 1 < 2` THEN
              UNDISCH_TAC `0 <= i` THEN
              ARITH_TAC
            ; ALL_TAC] THEN CONV_TAC NUM_REDUCE_CONV THEN

            MP_TAC (SPECL [`0x0:num`; `0x0:num`; `ct:byte list`; `iv:int128`; `key1:int128 list`; `key2:int128 list`]
              LENGTH_OF_AES256_XTS_DECRYPT_TAIL) THEN
            CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[ADD_0] THEN DISCH_TAC THEN
            IMP_REWRITE_TAC[(ISPECL [`(aes256_xts_decrypt_tail 0x0 0x0 ct iv key1 key2):byte list`;
              `0x10:num`] SUB_LIST_LENGTH_IMPLIES)] THEN

            REWRITE_TAC[AES256_XTS_DECRYPT_TAIL_WHEN_1BLOCK] THEN
            CONV_TAC NUM_REDUCE_CONV;

            SIMP_TAC[ARITH_RULE `(0x5 * i + 0x1) - 0x2 = 0x5 * i - 0x1`;
                     ARITH_RULE `(0x5 * i + 0x1) - 0x1 = 0x5 * i`] THEN

            MP_TAC (SPECL [`0`;`5 * i - 1:num`; `ct:byte list`; `iv:int128`; `key1:int128 list`; `key2:int128 list`]
              LENGTH_OF_AES256_XTS_DECRYPT_REC) THEN
            SUBGOAL_THEN `~(0x5 * i - 0x1 < 0x0)` ASSUME_TAC THENL
            [ UNDISCH_TAC `~(0x5 * i + 0x1 < 0x2)` THEN ARITH_TAC; ALL_TAC ] THEN
            ASM_SIMP_TAC[] THEN
            IMP_REWRITE_TAC[ARITH_RULE `~(0x5 * i + 0x1 < 0x2) ==> (0x5 * i - 1 - 0x0 + 0x1) * 0x10 = 0x50 * i`] THEN
            IMP_REWRITE_TAC[SUB_LIST_APPEND_RIGHT_LEMMA] THEN DISCH_TAC THEN

            MP_TAC (SPECL [`5 * i:num`; `0x0:num`; `ct:byte list`; `iv:int128`; `key1:int128 list`; `key2:int128 list`]
              LENGTH_OF_AES256_XTS_DECRYPT_TAIL) THEN
            CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[ADD_0] THEN DISCH_TAC THEN
            IMP_REWRITE_TAC[SUB_LIST_LENGTH_IMPLIES] THEN

            REWRITE_TAC[AES256_XTS_DECRYPT_TAIL_WHEN_1BLOCK] THEN
            SIMP_TAC[ARITH_RULE `i * 0x50 = (i * 0x5) * 0x10`;
                     ARITH_RULE `i * 0x5 = 0x5 * i`]];

          (* Proving that reading previous bytes is the same as the spec *)
          REWRITE_TAC[ARITH_RULE `0x50 * i = 0x10 * 5 * i`;
                      ARITH_RULE `0x50 * i + 0x10 = 0x10 * 5 * i + 0x10`] THEN
          REWRITE_TAC[SUB_LIST_OF_AES256_XTS_DECRYPT_FULL_BLOCKS] THEN
          IMP_REWRITE_TAC[SUB_LIST_LENGTH_IMPLIES] THEN
          REWRITE_TAC[LENGTH_OF_AES256_XTS_DECRYPT_FULL_BLOCKS]
          ];

        SUBGOAL_THEN  `i + 1 < 2 EXP 64` ASSUME_TAC THENL
        [ UNDISCH_TAC `i < val (num_5blocks_adjusted:int64)` THEN
          EXPAND_TAC "num_5blocks_adjusted" THEN
          UNDISCH_TAC `val (num_blocks_adjusted:int64) <= 0x2 EXP 0x18` THEN
          REWRITE_TAC [VAL_WORD; DIMINDEX_64] THEN ARITH_TAC; ALL_TAC] THEN
        EQ_TAC THENL
        [ REWRITE_TAC[WORD_RULE `!x:int64 a b. (word_sub (word_sub x a) b) = word_sub x (word_add a b)`] THEN
          ASM_SIMP_TAC[WORD_RULE `!a b. a + b < 2 EXP 64 ==> (word_add (word a) (word b)) = word (a + b)`] THEN
          REWRITE_TAC[VAL_EQ_0; WORD_SUB_EQ_0] THEN
          DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
          IMP_REWRITE_TAC[VAL_WORD; DIMINDEX_64; MOD_LT];
          REWRITE_TAC[WORD_RULE `!x:int64 a b. (word_sub (word_sub x a) b) = word_sub x (word_add a b)`] THEN
          ASM_SIMP_TAC[WORD_RULE `!a b. a + b < 2 EXP 64 ==> (word_add (word a) (word b)) = word (a + b)`] THEN
          REWRITE_TAC[VAL_EQ_0; WORD_SUB_EQ_0; WORD_VAL]]
      ];


      (* Subgoal 4: prove backedge is taken if i != val num_5blocks_adjusted *)
      REPEAT STRIP_TAC THEN
      REWRITE_TAC[byte_list_at] THEN
      ENSURES_INIT_TAC "s0" THEN
      ARM_ACCSTEPS_TAC AES_XTS_DECRYPT_EXEC [] (1--1) THEN
      SUBGOAL_THEN `~(val (word_sub (num_5blocks_adjusted:int64) (word i)) = 0x0)` ASSUME_TAC THENL
      [ UNDISCH_TAC `i < val (num_5blocks_adjusted:int64)` THEN WORD_ARITH_TAC; ALL_TAC] THEN
      POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_SIMP_TAC[];


      (* Subgoal 5: Prove the invariant implies post-condition
                    Backedge instruction is executed here *)
      REPEAT STRIP_TAC THEN
      REWRITE_TAC[byte_list_at] THEN
      SUBST_ALL_TAC (WORD_RULE `(word (val (num_5blocks_adjusted:int64))):int64 = num_5blocks_adjusted`) THEN

      MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN
      EXISTS_TAC `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
          MAYCHANGE [X19; X20; X21; X22],,
          MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15],,
          if val (num_5blocks_adjusted:int64) * 0x50 + 0x40 = val (num_blocks_adjusted:int64)
          then
          MAYCHANGE [memory :> bytes128 (word_add pt_ptr (word (0x50 * val (num_5blocks_adjusted:int64))));
                     memory :> bytes128 (word_add pt_ptr (word (0x50 * val num_5blocks_adjusted + 0x10)));
                     memory :> bytes128 (word_add pt_ptr (word (0x50 * val num_5blocks_adjusted + 0x20)));
                     memory :> bytes128 (word_add pt_ptr (word (0x50 * val num_5blocks_adjusted + 0x30)))]
          else
          (if val (num_5blocks_adjusted:int64) * 0x50 + 0x30 = val (num_blocks_adjusted:int64)
           then
           MAYCHANGE [memory :> bytes128 (word_add pt_ptr (word (0x50 * val (num_5blocks_adjusted:int64))));
                     memory :> bytes128 (word_add pt_ptr (word (0x50 * val num_5blocks_adjusted + 0x10)));
                     memory :> bytes128 (word_add pt_ptr (word (0x50 * val num_5blocks_adjusted + 0x20)))]
           else
           (if val (num_5blocks_adjusted:int64) * 0x50 + 0x20 = val (num_blocks_adjusted:int64)
            then
            MAYCHANGE [memory :> bytes128 (word_add pt_ptr (word (0x50 * val (num_5blocks_adjusted:int64))));
                       memory :> bytes128 (word_add pt_ptr (word (0x50 * val num_5blocks_adjusted + 0x10)))]
            else
            (if val (num_5blocks_adjusted:int64) * 0x50 + 0x10 = val (num_blocks_adjusted:int64)
             then
             MAYCHANGE [memory :> bytes128 (word_add pt_ptr (word (0x50 * val (num_5blocks_adjusted:int64))))]
             else
             MAYCHANGE [])))` THEN
      REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
      CONJ_TAC THENL [
        REPEAT (GEN_REWRITE_TAC ONCE_DEPTH_CONV [GSYM SEQ_ASSOC] THEN
                MATCH_MP_TAC SUBSUMED_SEQ THEN REWRITE_TAC[SUBSUMED_REFL]) THEN
        REPEAT COND_CASES_TAC THENL
        [ SUBGOAL_THEN `0x50 * val (num_5blocks_adjusted:int64) + 0x40 <= val (len:int64)` ASSUME_TAC THENL
          [ ASM_ARITH_TAC; ALL_TAC] THEN
          ABBREV_TAC `val5blocks = val (num_5blocks_adjusted:int64)` THEN
          ABBREV_TAC `vallen = val (len:int64)` THEN
          SUBSUMED_MAYCHANGE_TAC;
          SUBGOAL_THEN `0x50 * val (num_5blocks_adjusted:int64) + 0x30 <= val (len:int64)` ASSUME_TAC THENL
          [ ASM_ARITH_TAC; ALL_TAC] THEN
          ABBREV_TAC `val5blocks = val (num_5blocks_adjusted:int64)` THEN
          ABBREV_TAC `vallen = val (len:int64)` THEN
          SUBSUMED_MAYCHANGE_TAC;
          SUBGOAL_THEN `0x50 * val (num_5blocks_adjusted:int64) + 0x20 <= val (len:int64)` ASSUME_TAC THENL
          [ ASM_ARITH_TAC; ALL_TAC] THEN
          ABBREV_TAC `val5blocks = val (num_5blocks_adjusted:int64)` THEN
          ABBREV_TAC `vallen = val (len:int64)` THEN
          SUBSUMED_MAYCHANGE_TAC;
          SUBGOAL_THEN `0x50 * val (num_5blocks_adjusted:int64) + 0x10 <= val (len:int64)` ASSUME_TAC THENL
          [ ASM_ARITH_TAC; ALL_TAC] THEN
          ABBREV_TAC `val5blocks = val (num_5blocks_adjusted:int64)` THEN
          ABBREV_TAC `vallen = val (len:int64)` THEN
          SUBSUMED_MAYCHANGE_TAC;
          SUBSUMED_MAYCHANGE_TAC]
       ; ALL_TAC] THEN

      ENSURES_INIT_TAC "s0" THEN
      ARM_ACCSTEPS_TAC AES_XTS_DECRYPT_EXEC [] (1--3) THEN
      FIRST_X_ASSUM MP_TAC THEN
      COND_CASES_TAC THENL
      [ (* Case: len % 0x50 = 0x40 *)
        DISCH_TAC THEN

        SUBGOAL_THEN `val (num_5blocks_adjusted:int64) * 0x50 + 0x40 = val (num_blocks_adjusted:int64)` ASSUME_TAC THENL
        [ UNDISCH_TAC `val (word_sub
            (word_sub (num_blocks_adjusted:int64)
                      (word_mul (word 0x50) (num_5blocks_adjusted:int64)))
            (word 0x40)) =
            0x0` THEN
          REWRITE_TAC [VAL_EQ_0; WORD_SUB_EQ_0] THEN
          REWRITE_TAC [WORD_RULE `!x:int64. word_mul (word 0x50) x = word(val x * 0x50)`] THEN
          REWRITE_TAC[GSYM VAL_EQ] THEN
          SUBGOAL_THEN `val (num_5blocks_adjusted:int64) * 0x50 < 2 EXP 64` MP_TAC THENL
          [ UNDISCH_TAC `val (num_5blocks_adjusted:int64) * 0x50 <= val (num_blocks_adjusted:int64)` THEN
            UNDISCH_TAC `val (num_blocks_adjusted:int64) <= 2 EXP 24` THEN
            ARITH_TAC; ALL_TAC] THEN
          REWRITE_TAC[VAL_WORD_SUB_CASES] THEN
          SIMP_TAC[VAL_WORD; DIMINDEX_64; MOD_LT] THEN
          UNDISCH_TAC `val (num_5blocks_adjusted:int64) * 0x50 <= val (num_blocks_adjusted:int64)` THEN
          NUM_REDUCE_TAC THEN ARITH_TAC; ALL_TAC] THEN

        SUBGOAL_THEN `val (num_5blocks_adjusted:int64) * 0x50 + 0x40 <= val (len:int64)` ASSUME_TAC THENL
        [ UNDISCH_TAC `val (num_5blocks_adjusted:int64) * 0x50 + 0x40 = val (num_blocks_adjusted:int64)` THEN
          UNDISCH_TAC `val (num_blocks_adjusted:int64) <= val (len:int64)` THEN
          ARITH_TAC; ALL_TAC] THEN
        MP_TAC (SPECL [`ct_ptr:int64`; `num_5blocks_adjusted:int64`; `len:int64`; `ct:byte list`; `s3:armstate`] READ_TAIL4_LEMMA) THEN
        ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN

        (* Assumptions that help with reasoning about nonoverlapping
         so that the universally quantified assumption stays.
         See: https://hol-light.zulipchat.com/#narrow/channel/474190-s2n-bignum/topic/.E2.9C.94.20Symbolic.20simulation.20removed.20assumption/with/541554894 *)
        SUBGOAL_THEN `0x50 * (val (num_5blocks_adjusted:int64)) < 0x2 EXP 0x40` ASSUME_TAC THENL
        [ UNDISCH_TAC `val (num_5blocks_adjusted:int64) * 0x50 <= val (num_blocks_adjusted:int64)` THEN
          UNDISCH_TAC `val (num_blocks_adjusted:int64) <= 0x2 EXP 0x18` THEN
          ARITH_TAC; ALL_TAC] THEN
        SUBGOAL_THEN `val ((word (0x50 * val (num_5blocks_adjusted:int64))):int64) = 0x50 * val num_5blocks_adjusted` ASSUME_TAC THENL [
          IMP_REWRITE_TAC[VAL_WORD; DIMINDEX_64; MOD_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
        POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN


        ARM_ACCSTEPS_TAC AES_XTS_DECRYPT_EXEC [] (4--125) THEN
        XTSDEC_TAC `Q0:(armstate,int128)component`
          `val (num_5blocks_adjusted:int64) * 0x50` `val (num_5blocks_adjusted:int64) * 0x5` THEN
        XTSDEC_TAC `Q1:(armstate,int128)component`
          `val (num_5blocks_adjusted:int64) * 0x50 + 0x10` `val (num_5blocks_adjusted:int64) * 0x5 + 0x1` THEN
        XTSDEC_TAC `Q24:(armstate,int128)component`
          `val (num_5blocks_adjusted:int64) * 0x50 + 0x20` `val (num_5blocks_adjusted:int64) * 0x5 + 0x2` THEN
        XTSDEC_TAC `Q25:(armstate,int128)component`
          `val (num_5blocks_adjusted:int64) * 0x50 + 0x30` `val (num_5blocks_adjusted:int64) * 0x5 + 0x3` THEN

        ARM_ACCSTEPS_TAC AES_XTS_DECRYPT_EXEC [] (126--133) THEN
        TWEAK_TAC `Q6:(armstate,int128)component` `val (num_5blocks_adjusted:int64) * 0x5 + 0x4` `val (num_5blocks_adjusted:int64) * 0x5 + 0x3` THEN

        (* The following lemmas are for NONSELFMODIFYING_STATE_UPDATE_TAC when store back to pt_ptr *)
        CHANGED_TAC (RULE_ASSUM_TAC(REWRITE_RULE
          [WORD_RULE `word_mul (word 0x50) num_5blocks_adjusted:int64 = word(0x50 * val num_5blocks_adjusted)`])) THEN
        CHANGED_TAC (RULE_ASSUM_TAC(REWRITE_RULE
          [WORD_RULE `!base m n. word_add (word_add base (word m)) (word n) = word_add base (word(m + n))`])) THEN

        ARM_ACCSTEPS_TAC AES_XTS_DECRYPT_EXEC [] (134--134) THEN
        (* Need to simplify the expression for X1 after the first store instruction *)
        CHANGED_TAC (RULE_ASSUM_TAC(REWRITE_RULE
          [WORD_RULE `!base m n. word_add (word_add base (word m)) (word n) = word_add base (word(m + n))`])) THEN
        ARM_ACCSTEPS_TAC AES_XTS_DECRYPT_EXEC [] (135--136) THEN
        ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
        REPEAT CONJ_TAC THENL
        [
          REWRITE_TAC[acc_len] THEN ASM_SIMP_TAC[] THEN CONV_TAC WORD_RULE;
          REWRITE_TAC[acc_len] THEN ASM_SIMP_TAC[] THEN CONV_TAC WORD_RULE;
          REWRITE_TAC[acc_blocks] THEN ASM_SIMP_TAC[] THEN CONV_TAC WORD_RULE;

          REWRITE_TAC[acc_len] THEN ASM_SIMP_TAC[LE_REFL] THEN
          SUBGOAL_THEN `val ((word (0x50 * val (num_5blocks_adjusted:int64) + 0x40)):int64) =
            0x50 * val num_5blocks_adjusted + 0x40` ASSUME_TAC THENL
          [ IMP_REWRITE_TAC[VAL_WORD; MOD_LT; DIMINDEX_64] THEN
            UNDISCH_TAC `val (num_5blocks_adjusted:int64) * 0x50 + 0x40 <= val (len:int64)` THEN
            UNDISCH_TAC `val (len:int64) <= 0x2 EXP 0x18` THEN
            ARITH_TAC; ALL_TAC] THEN
          POP_ASSUM(fun th -> REWRITE_TAC[th]) THEN

          (* Remove quantifier *)
          UNDISCH_TAC
          `forall i.
            i < 0x50 * val (num_5blocks_adjusted:int64)
            ==> read (memory :> bytes8 (word_add pt_ptr (word i))) s136 =
                EL i (aes256_xts_decrypt ct (0x50 * val num_5blocks_adjusted) iv key1 key2)` THEN
          MP_TAC (SPECL [`0x50 * val (num_5blocks_adjusted:int64) + 0x40:num`; `pt_ptr:int64`;
                         `(aes256_xts_decrypt ct (0x50 * val (num_5blocks_adjusted:int64) + 0x40) iv key1 key2):byte list`;
                         `s136:armstate`] BYTE_LIST_TO_NUM_THM) THEN
          ANTS_TAC THENL[
            REWRITE_TAC[ARITH_RULE `0x50 * i + 0x40 = 0x10 * (5 * i + 4)`;
                        LENGTH_OF_AES256_XTS_DECRYPT_FULL_BLOCKS] THEN
            ARITH_TAC
            ; ALL_TAC] THEN
          DISCH_THEN (fun th -> REWRITE_TAC[th]) THEN
          MP_TAC (SPECL [`0x50 * val (num_5blocks_adjusted:int64):num`; `pt_ptr:int64`;
                         `(aes256_xts_decrypt ct (0x50 * val (num_5blocks_adjusted:int64)) iv key1 key2):byte list`;
                         `s136:armstate`] BYTE_LIST_TO_NUM_THM) THEN
          ANTS_TAC THENL[
            REWRITE_TAC[ARITH_RULE `0x50 * i = 0x10 * 5 * i`;
                        LENGTH_OF_AES256_XTS_DECRYPT_FULL_BLOCKS] THEN
            ARITH_TAC
            ; ALL_TAC] THEN
          DISCH_THEN (fun th -> REWRITE_TAC[th]) THEN
          DISCH_TAC THEN

          IMP_REWRITE_TAC[ARITH_RULE `0x50 * i + 0x40 = (0x50 * i + 0x30) + 0x10`; READ_BYTES_AND_BYTE128_SPLIT] THEN
          EXISTS_TAC `(aes256_xts_decrypt ct (0x50 * val (num_5blocks_adjusted:int64) + 0x40) iv key1 key2)` THEN
          REPEAT CONJ_TAC THENL [
            REWRITE_TAC [ARITH_RULE `(0x50 * i + 0x30) + 0x10 = 0x50 * i + 0x40`];

            MP_TAC (SPECL [`0x5 * val (num_5blocks_adjusted:int64) + 0x4:num`;
              `ct:byte list`; `iv:int128`; `key1:int128 list`;
              `key2:int128 list`] LENGTH_OF_AES256_XTS_DECRYPT_FULL_BLOCKS) THEN
            REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_ASSOC; GSYM ADD_ASSOC] THEN
            CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
            ASM_REWRITE_TAC[] THEN ARITH_TAC;

           (* Establish that one xts decrypt round is the same as
               selecting one block of bytes from calling the top-level function. *)
            REWRITE_TAC[aes256_xts_decrypt] THEN
            SIMP_TAC[ARITH_RULE `~(0x50 * val (num_5blocks_adjusted:int64) + 0x40 < 0x10)`] THEN
            SUBGOAL_THEN `(0x50 * val (num_5blocks_adjusted:int64) + 0x40) MOD 0x10 = 0` SUBST1_TAC THENL
            [ REWRITE_TAC[ARITH_RULE `80 * i + 64 = 16 * (5 * i + 4)`] THEN
              REWRITE_TAC[MOD_MULT]
            ; ALL_TAC] THEN
            CONV_TAC (DEPTH_CONV let_CONV) THEN
            REWRITE_TAC[SUB_0; ARITH_RULE `(0x50 * i + 0x40) DIV 0x10 = 0x5 * i + 0x4`] THEN
            SIMP_TAC[ARITH_RULE `~(0x5 * i + 0x4 < 0x2)`;
                     ARITH_RULE `(0x5 * i + 0x4) - 0x2 = 0x5 * i + 0x2`;
                     ARITH_RULE `(0x5 * i + 0x4) - 0x1 = 0x5 * i + 0x3`] THEN

            MP_TAC (SPECL [`0`;`5 * val (num_5blocks_adjusted:int64) + 2:num`;
              `ct:byte list`; `iv:int128`; `key1:int128 list`; `key2:int128 list`]
              LENGTH_OF_AES256_XTS_DECRYPT_REC) THEN
            SIMP_TAC[ARITH_RULE `~(5 * i + 2 < 0)`;
                     ARITH_RULE `((0x5 * i + 0x2) - 0x0 + 0x1) * 0x10 = 0x50 * i + 0x30`] THEN
            IMP_REWRITE_TAC[SUB_LIST_APPEND_RIGHT_LEMMA] THEN DISCH_TAC THEN

            MP_TAC (SPECL [`5 * val (num_5blocks_adjusted:int64) + 3:num`;
              `0x0:num`; `ct:byte list`; `iv:int128`; `key1:int128 list`; `key2:int128 list`]
              LENGTH_OF_AES256_XTS_DECRYPT_TAIL) THEN
            CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[ADD_0] THEN DISCH_TAC THEN
            IMP_REWRITE_TAC[SUB_LIST_LENGTH_IMPLIES] THEN

            REWRITE_TAC[AES256_XTS_DECRYPT_TAIL_WHEN_1BLOCK] THEN
            ASM_SIMP_TAC[ARITH_RULE `(i * 0x5 + 0x3) * 0x10 = i * 0x50 + 0x30`;
                         ARITH_RULE `5 * i + 3 = i * 5 + 3`];

            (* Proving that reading previous bytes is the same as the spec *)
            REWRITE_TAC[ARITH_RULE `0x50 * i + 0x30 = 0x10 * (5 * i + 3)`;
                        ARITH_RULE `0x50 * i + 0x40 = 0x10 * (5 * i + 3) + 0x10`] THEN
            REWRITE_TAC[SUB_LIST_OF_AES256_XTS_DECRYPT_FULL_BLOCKS] THEN
            ASM_REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_ASSOC] THEN CONV_TAC NUM_REDUCE_CONV
          ] THEN

          IMP_REWRITE_TAC[ARITH_RULE `0x50 * i + 0x30 = (0x50 * i + 0x20) + 0x10`; READ_BYTES_AND_BYTE128_SPLIT] THEN
          EXISTS_TAC `(aes256_xts_decrypt ct (0x50 * val (num_5blocks_adjusted:int64) + 0x30) iv key1 key2)` THEN
          REPEAT CONJ_TAC THENL [
            MP_TAC (SPECL [`0x5 * val (num_5blocks_adjusted:int64) + 0x3:num`;
              `ct:byte list`; `iv:int128`; `key1:int128 list`;
              `key2:int128 list`] LENGTH_OF_AES256_XTS_DECRYPT_FULL_BLOCKS) THEN
            REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_ASSOC; GSYM ADD_ASSOC] THEN
            CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
            IMP_REWRITE_TAC[SUB_LIST_LENGTH_IMPLIES];

            REWRITE_TAC [ARITH_RULE `(0x50 * i + 0x20) + 0x10 = 0x50 * i + 0x30`] THEN
            MP_TAC (SPECL [`0x5 * val (num_5blocks_adjusted:int64) + 0x3:num`;
              `ct:byte list`; `iv:int128`; `key1:int128 list`;
              `key2:int128 list`] LENGTH_OF_AES256_XTS_DECRYPT_FULL_BLOCKS) THEN
            REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_ASSOC; GSYM ADD_ASSOC] THEN
            CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
            IMP_REWRITE_TAC[SUB_LIST_LENGTH_IMPLIES] THEN ARITH_TAC;

            (* Establish that one xts decrypt round is the same as
               selecting one block of bytes from calling the top-level function. *)
            REWRITE_TAC[aes256_xts_decrypt] THEN
            SIMP_TAC[ARITH_RULE `~(0x50 * i + 0x30 < 0x10)`] THEN
            SUBGOAL_THEN `(0x50 * val (num_5blocks_adjusted:int64) + 0x30) MOD 0x10 = 0` SUBST1_TAC THENL
            [ REWRITE_TAC[ARITH_RULE `80 * i + 48 = 16 * (5 * i + 3)`] THEN
              REWRITE_TAC[MOD_MULT]
            ; ALL_TAC] THEN
            CONV_TAC (DEPTH_CONV let_CONV) THEN
            REWRITE_TAC[SUB_0; ARITH_RULE `(0x50 * i + 0x30) DIV 0x10 = 0x5 * i + 0x3`] THEN
            SIMP_TAC[ARITH_RULE `~(0x5 * i + 0x3 < 0x2)`;
                     ARITH_RULE `(0x5 * i + 0x3) - 0x2 = 0x5 * i + 0x1`;
                     ARITH_RULE `(0x5 * i + 0x3) - 0x1 = 0x5 * i + 0x2`] THEN

            MP_TAC (SPECL [`0`;`5 * val (num_5blocks_adjusted:int64) + 1:num`;
              `ct:byte list`; `iv:int128`; `key1:int128 list`; `key2:int128 list`]
              LENGTH_OF_AES256_XTS_DECRYPT_REC) THEN
            SIMP_TAC[ARITH_RULE `~(5 * i + 1 < 0)`] THEN
            REWRITE_TAC[ARITH_RULE `((0x5 * i + 0x1) - 0x0 + 0x1) * 0x10 = 0x50 * i + 0x20`] THEN
            IMP_REWRITE_TAC[SUB_LIST_APPEND_RIGHT_LEMMA] THEN DISCH_TAC THEN

            MP_TAC (SPECL [`5 * val (num_5blocks_adjusted:int64) + 2:num`; `0x0:num`;
              `ct:byte list`; `iv:int128`; `key1:int128 list`; `key2:int128 list`]
              LENGTH_OF_AES256_XTS_DECRYPT_TAIL) THEN
            CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[ADD_0] THEN DISCH_TAC THEN
            IMP_REWRITE_TAC[SUB_LIST_LENGTH_IMPLIES] THEN

            REWRITE_TAC[AES256_XTS_DECRYPT_TAIL_WHEN_1BLOCK] THEN
            ASM_SIMP_TAC[ARITH_RULE `(i * 0x5 + 0x2) * 0x10 = i * 0x50 + 0x20`;
                         ARITH_RULE `5 * i + 2 = i * 5 + 2`];

          (* Proving that reading previous bytes is the same as the spec *)
          REWRITE_TAC[ARITH_RULE `0x50 * i + 0x20 = 0x10 * (5 * i + 2)`;
                      ARITH_RULE `0x50 * i + 0x30 = 0x10 * (5 * i + 2) + 0x10`] THEN
          REWRITE_TAC[SUB_LIST_OF_AES256_XTS_DECRYPT_FULL_BLOCKS] THEN
          ASM_REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_ASSOC] THEN CONV_TAC NUM_REDUCE_CONV
          ] THEN

          REWRITE_TAC[ARITH_RULE `0x50 * i + 0x20 = (0x50 * i + 0x10) + 0x10`] THEN
          (* Use SPECL to force IMP_REWRITE_TAC to apply once once *)
          IMP_REWRITE_TAC[(SPECL [`pt_ptr:int64`; `(0x50 * val (num_5blocks_adjusted:int64) + 0x10):num`;
            `x:byte list`; `s188:armstate`] READ_BYTES_AND_BYTE128_SPLIT)] THEN
          EXISTS_TAC `(aes256_xts_decrypt ct (0x50 * val (num_5blocks_adjusted:int64) + 0x20) iv key1 key2)` THEN
          REPEAT CONJ_TAC THENL [
            MP_TAC (SPECL [`0x5 * val (num_5blocks_adjusted:int64) + 0x2:num`;
              `ct:byte list`; `iv:int128`; `key1:int128 list`;
              `key2:int128 list`] LENGTH_OF_AES256_XTS_DECRYPT_FULL_BLOCKS) THEN
            REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_ASSOC; GSYM ADD_ASSOC] THEN
            CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
            IMP_REWRITE_TAC[SUB_LIST_LENGTH_IMPLIES] THEN ARITH_TAC;

            MP_TAC (SPECL [`0x5 * val (num_5blocks_adjusted:int64) + 0x2:num`;
              `ct:byte list`; `iv:int128`; `key1:int128 list`;
              `key2:int128 list`] LENGTH_OF_AES256_XTS_DECRYPT_FULL_BLOCKS) THEN
            REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_ASSOC; GSYM ADD_ASSOC] THEN
            CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
            IMP_REWRITE_TAC[SUB_LIST_LENGTH_IMPLIES] THEN ARITH_TAC;

            (* Establish that one xts decrypt round is the same as
               selecting one block of bytes from calling the top-level function. *)
            REWRITE_TAC[aes256_xts_decrypt] THEN
            SIMP_TAC[ARITH_RULE `~(0x50 * i + 0x20 < 0x10)`] THEN
            SUBGOAL_THEN `(0x50 * val (num_5blocks_adjusted:int64) + 0x20) MOD 0x10 = 0` SUBST1_TAC THENL
            [ REWRITE_TAC[ARITH_RULE `80 * i + 32 = 16 * (5 * i + 2)`] THEN
              REWRITE_TAC[MOD_MULT]
            ; ALL_TAC] THEN
            CONV_TAC (DEPTH_CONV let_CONV) THEN
            REWRITE_TAC[SUB_0; ARITH_RULE `(0x50 * i + 0x20) DIV 0x10 = 0x5 * i + 0x2`] THEN
            SIMP_TAC[ARITH_RULE `~(0x5 * i + 0x2 < 0x2)`;
                     ARITH_RULE `(0x5 * i + 0x2) - 0x2 = 0x5 * i`;
                     ARITH_RULE `(0x5 * i + 0x2) - 0x1 = 0x5 * i + 0x1`] THEN

            MP_TAC (SPECL [`0`;`5 * val (num_5blocks_adjusted:int64):num`;
              `ct:byte list`; `iv:int128`; `key1:int128 list`; `key2:int128 list`]
              LENGTH_OF_AES256_XTS_DECRYPT_REC) THEN
            SIMP_TAC[ARITH_RULE `~(5 * i < 0)`;
                     ARITH_RULE `(0x5 * i - 0x0 + 0x1) * 0x10 = 0x50 * i + 0x10`] THEN
            IMP_REWRITE_TAC[SUB_LIST_APPEND_RIGHT_LEMMA] THEN DISCH_TAC THEN

            MP_TAC (SPECL [`5 * val (num_5blocks_adjusted:int64) + 1:num`; `0x0:num`;
              `ct:byte list`; `iv:int128`; `key1:int128 list`; `key2:int128 list`]
              LENGTH_OF_AES256_XTS_DECRYPT_TAIL) THEN
            CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[ADD_0] THEN DISCH_TAC THEN
            IMP_REWRITE_TAC[SUB_LIST_LENGTH_IMPLIES] THEN

            REWRITE_TAC[AES256_XTS_DECRYPT_TAIL_WHEN_1BLOCK] THEN
            SIMP_TAC[ARITH_RULE `i * 0x50 + 0x10 = (i * 0x5 + 0x1) * 0x10`;
                     ARITH_RULE `i * 0x5 = 0x5 * i`];

            (* Proving that reading previous bytes is the same as the spec *)
            REWRITE_TAC[ARITH_RULE `0x50 * i + 0x10 = 0x10 * (5 * i + 1)`;
                        ARITH_RULE `0x50 * i + 0x20 = 0x10 * (5 * i + 1) + 0x10`] THEN
            REWRITE_TAC[SUB_LIST_OF_AES256_XTS_DECRYPT_FULL_BLOCKS] THEN
            ASM_REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_ASSOC] THEN CONV_TAC NUM_REDUCE_CONV
          ] THEN

          IMP_REWRITE_TAC[(SPECL [`pt_ptr:int64`; `(0x50 * val (num_5blocks_adjusted:int64)):num`;
            `(aes256_xts_decrypt ct (0x50 * val (num_5blocks_adjusted:int64) + 0x10) iv key1 key2):byte list`;
            `s188:armstate`]
            READ_BYTES_AND_BYTE128_SPLIT)] THEN
          EXISTS_TAC `ct:byte list` THEN EXISTS_TAC `iv:int128` THEN
          EXISTS_TAC `key1:int128 list` THEN EXISTS_TAC `key2:int128 list` THEN
          REPEAT CONJ_TAC THENL [
            MP_TAC (SPECL [`0x5 * val (num_5blocks_adjusted:int64) + 0x1:num`;
              `ct:byte list`; `iv:int128`; `key1:int128 list`;
              `key2:int128 list`] LENGTH_OF_AES256_XTS_DECRYPT_FULL_BLOCKS) THEN
            REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_ASSOC; GSYM ADD_ASSOC] THEN
            CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
            IMP_REWRITE_TAC[SUB_LIST_LENGTH_IMPLIES] THEN ARITH_TAC;

            MP_TAC (SPECL [`0x5 * val (num_5blocks_adjusted:int64) + 0x1:num`;
              `ct:byte list`; `iv:int128`; `key1:int128 list`;
              `key2:int128 list`] LENGTH_OF_AES256_XTS_DECRYPT_FULL_BLOCKS) THEN
            REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_ASSOC; GSYM ADD_ASSOC] THEN
            CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
            IMP_REWRITE_TAC[SUB_LIST_LENGTH_IMPLIES] THEN ARITH_TAC;

            (* Establish that one xts decrypt round is the same as
               selecting one block of bytes from calling the top-level function. *)
            REWRITE_TAC[aes256_xts_decrypt] THEN
            SIMP_TAC[ARITH_RULE `~(0x50 * i + 0x10 < 0x10)`] THEN
            SUBGOAL_THEN `(0x50 * val (num_5blocks_adjusted:int64) + 0x10) MOD 0x10 = 0` SUBST1_TAC THENL
            [ REWRITE_TAC[ARITH_RULE `80 * i + 16 = 16 * (5 * i + 1)`] THEN
              REWRITE_TAC[MOD_MULT]
            ; ALL_TAC] THEN
            CONV_TAC (DEPTH_CONV let_CONV) THEN
            REWRITE_TAC[SUB_0; ARITH_RULE `(0x50 * i + 0x10) DIV 0x10 = 0x5 * i + 0x1`] THEN
            (* Two cases: i = 0 then execute tail branch, else execute recursion branch *)
            COND_CASES_TAC THENL
            [ SUBGOAL_THEN `val (num_5blocks_adjusted:int64) = 0` SUBST1_TAC THENL
              [ UNDISCH_TAC `5 * val (num_5blocks_adjusted:int64) + 1 < 2` THEN
                UNDISCH_TAC `0 < val (num_5blocks_adjusted:int64)` THEN
                ARITH_TAC
              ; ALL_TAC] THEN CONV_TAC NUM_REDUCE_CONV THEN

              MP_TAC (SPECL [`0x0:num`; `0x0:num`; `ct:byte list`; `iv:int128`; `key1:int128 list`; `key2:int128 list`]
                LENGTH_OF_AES256_XTS_DECRYPT_TAIL) THEN
              CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[ADD_0] THEN DISCH_TAC THEN
              IMP_REWRITE_TAC[(ISPECL [`(aes256_xts_decrypt_tail 0x0 0x0 ct iv key1 key2):byte list`;
                `0x10:num`] SUB_LIST_LENGTH_IMPLIES)] THEN

              REWRITE_TAC[AES256_XTS_DECRYPT_TAIL_WHEN_1BLOCK] THEN
              CONV_TAC NUM_REDUCE_CONV;

              SIMP_TAC[ARITH_RULE `(0x5 * i + 0x1) - 0x2 = 0x5 * i - 0x1`;
                       ARITH_RULE `(0x5 * i + 0x1) - 0x1 = 0x5 * i`] THEN

              MP_TAC (SPECL [`0`;`5 * val (num_5blocks_adjusted:int64) - 1:num`;
                `ct:byte list`; `iv:int128`; `key1:int128 list`; `key2:int128 list`]
                LENGTH_OF_AES256_XTS_DECRYPT_REC) THEN
              SUBGOAL_THEN `~(0x5 * val (num_5blocks_adjusted:int64) - 0x1 < 0x0)` ASSUME_TAC THENL
              [ UNDISCH_TAC `~(0x5 * val (num_5blocks_adjusted:int64) + 0x1 < 0x2)` THEN ARITH_TAC; ALL_TAC ] THEN
              ASM_SIMP_TAC[] THEN
              IMP_REWRITE_TAC[ARITH_RULE `~(0x5 * i + 0x1 < 0x2) ==> (0x5 * i - 1 - 0x0 + 0x1) * 0x10 = 0x50 * i`] THEN
              IMP_REWRITE_TAC[SUB_LIST_APPEND_RIGHT_LEMMA] THEN DISCH_TAC THEN

              MP_TAC (SPECL [`5 * val (num_5blocks_adjusted:int64):num`;
                `0x0:num`; `ct:byte list`; `iv:int128`; `key1:int128 list`; `key2:int128 list`]
                LENGTH_OF_AES256_XTS_DECRYPT_TAIL) THEN
              CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[ADD_0] THEN DISCH_TAC THEN
              IMP_REWRITE_TAC[SUB_LIST_LENGTH_IMPLIES] THEN

              REWRITE_TAC[AES256_XTS_DECRYPT_TAIL_WHEN_1BLOCK] THEN
              SIMP_TAC[ARITH_RULE `i * 0x50 = (i * 0x5) * 0x10`;
                       ARITH_RULE `i * 0x5 = 0x5 * i`]];

            (* Proving that reading previous bytes is the same as the spec *)
            REWRITE_TAC[ARITH_RULE `0x50 * i = 0x10 * 5 * i`;
                        ARITH_RULE `0x50 * i + 0x10 = 0x10 * 5 * i + 0x10`] THEN
            REWRITE_TAC[SUB_LIST_OF_AES256_XTS_DECRYPT_FULL_BLOCKS] THEN
            IMP_REWRITE_TAC[SUB_LIST_LENGTH_IMPLIES] THEN
            REWRITE_TAC[LENGTH_OF_AES256_XTS_DECRYPT_FULL_BLOCKS]]
          ]
        ; ALL_TAC] THEN

      DISCH_TAC THEN
      ARM_ACCSTEPS_TAC AES_XTS_DECRYPT_EXEC [] (4--5) THEN
      FIRST_X_ASSUM MP_TAC THEN
      COND_CASES_TAC THENL
      [ (* Case: len % 0x50 = 0x30 *)
        DISCH_TAC THEN
        SUBGOAL_THEN `val (num_5blocks_adjusted:int64) * 0x50 + 0x30 = val (num_blocks_adjusted:int64)` ASSUME_TAC THENL
        [ UNDISCH_TAC `val (word_sub
            (word_sub (num_blocks_adjusted:int64)
                     (word_mul (word 0x50) (num_5blocks_adjusted:int64)))
            (word 0x30)) =
            0x0` THEN
          REWRITE_TAC [VAL_EQ_0; WORD_SUB_EQ_0] THEN
          REWRITE_TAC [WORD_RULE `!x:int64. word_mul (word 0x50) x = word(val x * 0x50)`] THEN
          REWRITE_TAC[GSYM VAL_EQ] THEN
          SUBGOAL_THEN `val (num_5blocks_adjusted:int64) * 0x50 < 2 EXP 64` MP_TAC THENL
          [ UNDISCH_TAC `val (num_5blocks_adjusted:int64) * 0x50 <= val (num_blocks_adjusted:int64)` THEN
            UNDISCH_TAC `val (num_blocks_adjusted:int64) <= 2 EXP 24` THEN
            ARITH_TAC; ALL_TAC] THEN
          REWRITE_TAC[VAL_WORD_SUB_CASES] THEN
          SIMP_TAC[VAL_WORD; DIMINDEX_64; MOD_LT] THEN
          UNDISCH_TAC `val (num_5blocks_adjusted:int64) * 0x50 <= val (num_blocks_adjusted:int64)` THEN
          NUM_REDUCE_TAC THEN ARITH_TAC; ALL_TAC] THEN
        SUBGOAL_THEN `~(val (num_5blocks_adjusted:int64) * 0x50 + 0x40 = val (num_blocks_adjusted:int64))` ASSUME_TAC THENL
        [ UNDISCH_TAC `val (num_5blocks_adjusted:int64) * 0x50 + 0x30 = val (num_blocks_adjusted:int64)` THEN
          ARITH_TAC; ALL_TAC] THEN
        SUBGOAL_THEN `val (num_5blocks_adjusted:int64) * 0x50 + 0x30 <= val (len:int64)` ASSUME_TAC THENL
        [ UNDISCH_TAC `val (num_5blocks_adjusted:int64) * 0x50 + 0x30 = val (num_blocks_adjusted:int64)` THEN
          UNDISCH_TAC `val (num_blocks_adjusted:int64) <= val (len:int64)` THEN
          ARITH_TAC; ALL_TAC] THEN
        MP_TAC (SPECL [`ct_ptr:int64`; `num_5blocks_adjusted:int64`; `len:int64`; `ct:byte list`; `s5:armstate`] READ_TAIL3_LEMMA) THEN
        ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN

        (* Assumptions that help with reasoning about nonoverlapping
         so that the universally quantified assumption stays.
         See: https://hol-light.zulipchat.com/#narrow/channel/474190-s2n-bignum/topic/.E2.9C.94.20Symbolic.20simulation.20removed.20assumption/with/541554894 *)
        SUBGOAL_THEN `0x50 * (val (num_5blocks_adjusted:int64)) < 0x2 EXP 0x40` ASSUME_TAC THENL
        [ UNDISCH_TAC `val (num_5blocks_adjusted:int64) * 0x50 <= val (num_blocks_adjusted:int64)` THEN
          UNDISCH_TAC `val (num_blocks_adjusted:int64) <= 0x2 EXP 0x18` THEN
          ARITH_TAC; ALL_TAC] THEN
        SUBGOAL_THEN `val ((word (0x50 * val (num_5blocks_adjusted:int64))):int64) = 0x50 * val num_5blocks_adjusted` ASSUME_TAC THENL [
          IMP_REWRITE_TAC[VAL_WORD; DIMINDEX_64; MOD_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
        POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN

        ARM_ACCSTEPS_TAC AES_XTS_DECRYPT_EXEC [] (6--97) THEN
        XTSDEC_TAC `Q0:(armstate,int128)component`
          `val (num_5blocks_adjusted:int64) * 0x50` `val (num_5blocks_adjusted:int64) * 0x5` THEN
        XTSDEC_TAC `Q1:(armstate,int128)component`
          `val (num_5blocks_adjusted:int64) * 0x50 + 0x10` `val (num_5blocks_adjusted:int64) * 0x5 + 0x1` THEN
        XTSDEC_TAC `Q24:(armstate,int128)component`
          `val (num_5blocks_adjusted:int64) * 0x50 + 0x20` `val (num_5blocks_adjusted:int64) * 0x5 + 0x2` THEN

        ARM_ACCSTEPS_TAC AES_XTS_DECRYPT_EXEC [] (98--105) THEN
        TWEAK_TAC `Q6:(armstate,int128)component` `val (num_5blocks_adjusted:int64) * 0x5 + 0x3` `val (num_5blocks_adjusted:int64) * 0x5 + 0x2` THEN

        (* The following lemmas are for NONSELFMODIFYING_STATE_UPDATE_TAC when store back to pt_ptr *)
        RULE_ASSUM_TAC(REWRITE_RULE
          [WORD_RULE `word_mul (word 0x50) num_5blocks_adjusted:int64 = word(0x50 * val num_5blocks_adjusted)`]) THEN

        ARM_ACCSTEPS_TAC AES_XTS_DECRYPT_EXEC [] (106--108) THEN
        ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
        REPEAT CONJ_TAC THENL
        [
          REWRITE_TAC[acc_len] THEN ASM_SIMP_TAC[] THEN CONV_TAC WORD_RULE;
          REWRITE_TAC[acc_len] THEN ASM_SIMP_TAC[] THEN CONV_TAC WORD_RULE;
          REWRITE_TAC[acc_blocks] THEN ASM_SIMP_TAC[] THEN CONV_TAC WORD_RULE;

          REWRITE_TAC[acc_len] THEN ASM_SIMP_TAC[LE_REFL] THEN
          SUBGOAL_THEN `val ((word (0x50 * val (num_5blocks_adjusted:int64) + 0x30)):int64) =
            0x50 * val num_5blocks_adjusted + 0x30` ASSUME_TAC THENL
          [ IMP_REWRITE_TAC[VAL_WORD; MOD_LT; DIMINDEX_64] THEN
            UNDISCH_TAC `val (num_5blocks_adjusted:int64) * 0x50 + 0x30 <= val (len:int64)` THEN
            UNDISCH_TAC `val (len:int64) <= 0x2 EXP 0x18` THEN
            ARITH_TAC; ALL_TAC] THEN
          POP_ASSUM(fun th -> REWRITE_TAC[th]) THEN

          (* Remove quantifier *)
          UNDISCH_TAC
          `forall i.
            i < 0x50 * val (num_5blocks_adjusted:int64)
            ==> read (memory :> bytes8 (word_add pt_ptr (word i))) s108 =
                EL i (aes256_xts_decrypt ct (0x50 * val num_5blocks_adjusted) iv key1 key2)` THEN
          MP_TAC (SPECL [`0x50 * val (num_5blocks_adjusted:int64) + 0x30:num`; `pt_ptr:int64`;
                         `(aes256_xts_decrypt ct (0x50 * val (num_5blocks_adjusted:int64) + 0x30) iv key1 key2):byte list`;
                         `s108:armstate`] BYTE_LIST_TO_NUM_THM) THEN
          ANTS_TAC THENL[
            REWRITE_TAC[ARITH_RULE `0x50 * i + 0x30 = 0x10 * (5 * i + 3)`;
                        LENGTH_OF_AES256_XTS_DECRYPT_FULL_BLOCKS] THEN
            ARITH_TAC
            ; ALL_TAC] THEN
          DISCH_THEN (fun th -> REWRITE_TAC[th]) THEN
          MP_TAC (SPECL [`0x50 * val (num_5blocks_adjusted:int64):num`; `pt_ptr:int64`;
                         `(aes256_xts_decrypt ct (0x50 * val (num_5blocks_adjusted:int64)) iv key1 key2):byte list`;
                         `s108:armstate`] BYTE_LIST_TO_NUM_THM) THEN
          ANTS_TAC THENL[
            REWRITE_TAC[ARITH_RULE `0x50 * i = 0x10 * 5 * i`;
                        LENGTH_OF_AES256_XTS_DECRYPT_FULL_BLOCKS] THEN
            ARITH_TAC
            ; ALL_TAC] THEN
          DISCH_THEN (fun th -> REWRITE_TAC[th]) THEN
          DISCH_TAC THEN

          IMP_REWRITE_TAC[ARITH_RULE `0x50 * i + 0x30 = (0x50 * i + 0x20) + 0x10`; READ_BYTES_AND_BYTE128_SPLIT] THEN
          EXISTS_TAC `(aes256_xts_decrypt ct (0x50 * val (num_5blocks_adjusted:int64) + 0x30) iv key1 key2)` THEN
          REPEAT CONJ_TAC THENL [
            MP_TAC (SPECL [`0x5 * val (num_5blocks_adjusted:int64) + 0x3:num`;
              `ct:byte list`; `iv:int128`; `key1:int128 list`;
              `key2:int128 list`] LENGTH_OF_AES256_XTS_DECRYPT_FULL_BLOCKS) THEN
            REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_ASSOC; GSYM ADD_ASSOC] THEN
            CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
            IMP_REWRITE_TAC[SUB_LIST_LENGTH_IMPLIES];

            REWRITE_TAC [ARITH_RULE `(0x50 * i + 0x20) + 0x10 = 0x50 * i + 0x30`] THEN
            MP_TAC (SPECL [`0x5 * val (num_5blocks_adjusted:int64) + 0x3:num`;
              `ct:byte list`; `iv:int128`; `key1:int128 list`;
              `key2:int128 list`] LENGTH_OF_AES256_XTS_DECRYPT_FULL_BLOCKS) THEN
            REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_ASSOC; GSYM ADD_ASSOC] THEN
            CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
            IMP_REWRITE_TAC[SUB_LIST_LENGTH_IMPLIES] THEN ARITH_TAC;

            (* Establish that one xts decrypt round is the same as
               selecting one block of bytes from calling the top-level function. *)
            REWRITE_TAC[aes256_xts_decrypt] THEN
            SIMP_TAC[ARITH_RULE `~(0x50 * i + 0x30 < 0x10)`] THEN
            SUBGOAL_THEN `(0x50 * val (num_5blocks_adjusted:int64) + 0x30) MOD 0x10 = 0` SUBST1_TAC THENL
            [ REWRITE_TAC[ARITH_RULE `80 * i + 48 = 16 * (5 * i + 3)`] THEN
              REWRITE_TAC[MOD_MULT]
            ; ALL_TAC] THEN
            CONV_TAC (DEPTH_CONV let_CONV) THEN
            REWRITE_TAC[SUB_0; ARITH_RULE `(0x50 * i + 0x30) DIV 0x10 = 0x5 * i + 0x3`] THEN
            SIMP_TAC[ARITH_RULE `~(0x5 * i + 0x3 < 0x2)`;
                     ARITH_RULE `(0x5 * i + 0x3) - 0x2 = 0x5 * i + 0x1`;
                     ARITH_RULE `(0x5 * i + 0x3) - 0x1 = 0x5 * i + 0x2`] THEN

            MP_TAC (SPECL [`0`;`5 * val (num_5blocks_adjusted:int64) + 1:num`;
              `ct:byte list`; `iv:int128`; `key1:int128 list`; `key2:int128 list`]
              LENGTH_OF_AES256_XTS_DECRYPT_REC) THEN
            SIMP_TAC[ARITH_RULE `~(5 * i + 1 < 0)`] THEN
            REWRITE_TAC[ARITH_RULE `((0x5 * i + 0x1) - 0x0 + 0x1) * 0x10 = 0x50 * i + 0x20`] THEN
            IMP_REWRITE_TAC[SUB_LIST_APPEND_RIGHT_LEMMA] THEN DISCH_TAC THEN

            MP_TAC (SPECL [`5 * val (num_5blocks_adjusted:int64) + 2:num`; `0x0:num`;
              `ct:byte list`; `iv:int128`; `key1:int128 list`; `key2:int128 list`]
              LENGTH_OF_AES256_XTS_DECRYPT_TAIL) THEN
            CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[ADD_0] THEN DISCH_TAC THEN
            IMP_REWRITE_TAC[SUB_LIST_LENGTH_IMPLIES] THEN

            REWRITE_TAC[AES256_XTS_DECRYPT_TAIL_WHEN_1BLOCK] THEN
            ASM_SIMP_TAC[ARITH_RULE `(i * 0x5 + 0x2) * 0x10 = i * 0x50 + 0x20`;
                         ARITH_RULE `5 * i + 2 = i * 5 + 2`];

          (* Proving that reading previous bytes is the same as the spec *)
          REWRITE_TAC[ARITH_RULE `0x50 * i + 0x20 = 0x10 * (5 * i + 2)`;
                      ARITH_RULE `0x50 * i + 0x30 = 0x10 * (5 * i + 2) + 0x10`] THEN
          REWRITE_TAC[SUB_LIST_OF_AES256_XTS_DECRYPT_FULL_BLOCKS] THEN
          ASM_REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_ASSOC] THEN CONV_TAC NUM_REDUCE_CONV
          ] THEN

          REWRITE_TAC[ARITH_RULE `0x50 * i + 0x20 = (0x50 * i + 0x10) + 0x10`] THEN
          (* Use SPECL to force IMP_REWRITE_TAC to apply once once *)
          IMP_REWRITE_TAC[(SPECL [`pt_ptr:int64`; `(0x50 * val (num_5blocks_adjusted:int64) + 0x10):num`;
            `x:byte list`; `s108:armstate`] READ_BYTES_AND_BYTE128_SPLIT)] THEN
          EXISTS_TAC `(aes256_xts_decrypt ct (0x50 * val (num_5blocks_adjusted:int64) + 0x20) iv key1 key2)` THEN
          REPEAT CONJ_TAC THENL [
            MP_TAC (SPECL [`0x5 * val (num_5blocks_adjusted:int64) + 0x2:num`;
              `ct:byte list`; `iv:int128`; `key1:int128 list`;
              `key2:int128 list`] LENGTH_OF_AES256_XTS_DECRYPT_FULL_BLOCKS) THEN
            REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_ASSOC; GSYM ADD_ASSOC] THEN
            CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
            IMP_REWRITE_TAC[SUB_LIST_LENGTH_IMPLIES] THEN ARITH_TAC;

            MP_TAC (SPECL [`0x5 * val (num_5blocks_adjusted:int64) + 0x2:num`;
              `ct:byte list`; `iv:int128`; `key1:int128 list`;
              `key2:int128 list`] LENGTH_OF_AES256_XTS_DECRYPT_FULL_BLOCKS) THEN
            REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_ASSOC; GSYM ADD_ASSOC] THEN
            CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
            IMP_REWRITE_TAC[SUB_LIST_LENGTH_IMPLIES] THEN ARITH_TAC;

            (* Establish that one xts decrypt round is the same as
               selecting one block of bytes from calling the top-level function. *)
            REWRITE_TAC[aes256_xts_decrypt] THEN
            SIMP_TAC[ARITH_RULE `~(0x50 * i + 0x20 < 0x10)`] THEN
            SUBGOAL_THEN `(0x50 * val (num_5blocks_adjusted:int64) + 0x20) MOD 0x10 = 0` SUBST1_TAC THENL
            [ REWRITE_TAC[ARITH_RULE `80 * i + 32 = 16 * (5 * i + 2)`] THEN
              REWRITE_TAC[MOD_MULT]
            ; ALL_TAC] THEN
            CONV_TAC (DEPTH_CONV let_CONV) THEN
            REWRITE_TAC[SUB_0; ARITH_RULE `(0x50 * i + 0x20) DIV 0x10 = 0x5 * i + 0x2`] THEN
            SIMP_TAC[ARITH_RULE `~(0x5 * i + 0x2 < 0x2)`;
                     ARITH_RULE `(0x5 * i + 0x2) - 0x2 = 0x5 * i`;
                     ARITH_RULE `(0x5 * i + 0x2) - 0x1 = 0x5 * i + 0x1`] THEN

            MP_TAC (SPECL [`0`;`5 * val (num_5blocks_adjusted:int64):num`;
              `ct:byte list`; `iv:int128`; `key1:int128 list`; `key2:int128 list`]
              LENGTH_OF_AES256_XTS_DECRYPT_REC) THEN
            SIMP_TAC[ARITH_RULE `~(5 * i < 0)`;
                     ARITH_RULE `(0x5 * i - 0x0 + 0x1) * 0x10 = 0x50 * i + 0x10`] THEN
            IMP_REWRITE_TAC[SUB_LIST_APPEND_RIGHT_LEMMA] THEN DISCH_TAC THEN

            MP_TAC (SPECL [`5 * val (num_5blocks_adjusted:int64) + 1:num`; `0x0:num`;
              `ct:byte list`; `iv:int128`; `key1:int128 list`; `key2:int128 list`]
              LENGTH_OF_AES256_XTS_DECRYPT_TAIL) THEN
            CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[ADD_0] THEN DISCH_TAC THEN
            IMP_REWRITE_TAC[SUB_LIST_LENGTH_IMPLIES] THEN

            REWRITE_TAC[AES256_XTS_DECRYPT_TAIL_WHEN_1BLOCK] THEN
            SIMP_TAC[ARITH_RULE `i * 0x50 + 0x10 = (i * 0x5 + 0x1) * 0x10`;
                     ARITH_RULE `i * 0x5 = 0x5 * i`];

            (* Proving that reading previous bytes is the same as the spec *)
            REWRITE_TAC[ARITH_RULE `0x50 * i + 0x10 = 0x10 * (5 * i + 1)`;
                        ARITH_RULE `0x50 * i + 0x20 = 0x10 * (5 * i + 1) + 0x10`] THEN
            REWRITE_TAC[SUB_LIST_OF_AES256_XTS_DECRYPT_FULL_BLOCKS] THEN
            ASM_REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_ASSOC] THEN CONV_TAC NUM_REDUCE_CONV
          ] THEN

          IMP_REWRITE_TAC[(SPECL [`pt_ptr:int64`; `(0x50 * val (num_5blocks_adjusted:int64)):num`;
            `(aes256_xts_decrypt ct (0x50 * val (num_5blocks_adjusted:int64) + 0x10) iv key1 key2):byte list`;
            `s108:armstate`]
            READ_BYTES_AND_BYTE128_SPLIT)] THEN
          EXISTS_TAC `ct:byte list` THEN EXISTS_TAC `iv:int128` THEN
          EXISTS_TAC `key1:int128 list` THEN EXISTS_TAC `key2:int128 list` THEN
          REPEAT CONJ_TAC THENL [
            MP_TAC (SPECL [`0x5 * val (num_5blocks_adjusted:int64) + 0x1:num`;
              `ct:byte list`; `iv:int128`; `key1:int128 list`;
              `key2:int128 list`] LENGTH_OF_AES256_XTS_DECRYPT_FULL_BLOCKS) THEN
            REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_ASSOC; GSYM ADD_ASSOC] THEN
            CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
            IMP_REWRITE_TAC[SUB_LIST_LENGTH_IMPLIES] THEN ARITH_TAC;

            MP_TAC (SPECL [`0x5 * val (num_5blocks_adjusted:int64) + 0x1:num`;
              `ct:byte list`; `iv:int128`; `key1:int128 list`;
              `key2:int128 list`] LENGTH_OF_AES256_XTS_DECRYPT_FULL_BLOCKS) THEN
            REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_ASSOC; GSYM ADD_ASSOC] THEN
            CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
            IMP_REWRITE_TAC[SUB_LIST_LENGTH_IMPLIES] THEN ARITH_TAC;

            (* Establish that one xts decrypt round is the same as
               selecting one block of bytes from calling the top-level function. *)
            REWRITE_TAC[aes256_xts_decrypt] THEN
            SIMP_TAC[ARITH_RULE `~(0x50 * i + 0x10 < 0x10)`] THEN
            SUBGOAL_THEN `(0x50 * val (num_5blocks_adjusted:int64) + 0x10) MOD 0x10 = 0` SUBST1_TAC THENL
            [ REWRITE_TAC[ARITH_RULE `80 * i + 16 = 16 * (5 * i + 1)`] THEN
              REWRITE_TAC[MOD_MULT]
            ; ALL_TAC] THEN
            CONV_TAC (DEPTH_CONV let_CONV) THEN
            REWRITE_TAC[SUB_0; ARITH_RULE `(0x50 * i + 0x10) DIV 0x10 = 0x5 * i + 0x1`] THEN
            (* Two cases: i = 0 then execute tail branch, else execute recursion branch *)
            COND_CASES_TAC THENL
            [ SUBGOAL_THEN `val (num_5blocks_adjusted:int64) = 0` SUBST1_TAC THENL
              [ UNDISCH_TAC `5 * val (num_5blocks_adjusted:int64) + 1 < 2` THEN
                UNDISCH_TAC `0 < val (num_5blocks_adjusted:int64)` THEN
                ARITH_TAC
              ; ALL_TAC] THEN CONV_TAC NUM_REDUCE_CONV THEN

              MP_TAC (SPECL [`0x0:num`; `0x0:num`; `ct:byte list`; `iv:int128`; `key1:int128 list`; `key2:int128 list`]
                LENGTH_OF_AES256_XTS_DECRYPT_TAIL) THEN
              CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[ADD_0] THEN DISCH_TAC THEN
              IMP_REWRITE_TAC[(ISPECL [`(aes256_xts_decrypt_tail 0x0 0x0 ct iv key1 key2):byte list`;
                `0x10:num`] SUB_LIST_LENGTH_IMPLIES)] THEN

              REWRITE_TAC[AES256_XTS_DECRYPT_TAIL_WHEN_1BLOCK] THEN
              CONV_TAC NUM_REDUCE_CONV;

              SIMP_TAC[ARITH_RULE `(0x5 * i + 0x1) - 0x2 = 0x5 * i - 0x1`;
                       ARITH_RULE `(0x5 * i + 0x1) - 0x1 = 0x5 * i`] THEN

              MP_TAC (SPECL [`0`;`5 * val (num_5blocks_adjusted:int64) - 1:num`;
                `ct:byte list`; `iv:int128`; `key1:int128 list`; `key2:int128 list`]
                LENGTH_OF_AES256_XTS_DECRYPT_REC) THEN
              SUBGOAL_THEN `~(0x5 * val (num_5blocks_adjusted:int64) - 0x1 < 0x0)` ASSUME_TAC THENL
              [ UNDISCH_TAC `~(0x5 * val (num_5blocks_adjusted:int64) + 0x1 < 0x2)` THEN ARITH_TAC; ALL_TAC ] THEN
              ASM_SIMP_TAC[] THEN
              IMP_REWRITE_TAC[ARITH_RULE `~(0x5 * i + 0x1 < 0x2) ==> (0x5 * i - 1 - 0x0 + 0x1) * 0x10 = 0x50 * i`] THEN
              IMP_REWRITE_TAC[SUB_LIST_APPEND_RIGHT_LEMMA] THEN DISCH_TAC THEN

              MP_TAC (SPECL [`5 * val (num_5blocks_adjusted:int64):num`;
                `0x0:num`; `ct:byte list`; `iv:int128`; `key1:int128 list`; `key2:int128 list`]
                LENGTH_OF_AES256_XTS_DECRYPT_TAIL) THEN
              CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[ADD_0] THEN DISCH_TAC THEN
              IMP_REWRITE_TAC[SUB_LIST_LENGTH_IMPLIES] THEN

              REWRITE_TAC[AES256_XTS_DECRYPT_TAIL_WHEN_1BLOCK] THEN
              SIMP_TAC[ARITH_RULE `i * 0x50 = (i * 0x5) * 0x10`;
                       ARITH_RULE `i * 0x5 = 0x5 * i`]];

            (* Proving that reading previous bytes is the same as the spec *)
            REWRITE_TAC[ARITH_RULE `0x50 * i = 0x10 * 5 * i`;
                        ARITH_RULE `0x50 * i + 0x10 = 0x10 * 5 * i + 0x10`] THEN
            REWRITE_TAC[SUB_LIST_OF_AES256_XTS_DECRYPT_FULL_BLOCKS] THEN
            IMP_REWRITE_TAC[SUB_LIST_LENGTH_IMPLIES] THEN
            REWRITE_TAC[LENGTH_OF_AES256_XTS_DECRYPT_FULL_BLOCKS]]
        ]
      ; ALL_TAC ] THEN

      DISCH_TAC THEN
      ARM_ACCSTEPS_TAC AES_XTS_DECRYPT_EXEC [] (6--7) THEN
      FIRST_X_ASSUM MP_TAC THEN
      COND_CASES_TAC THENL
      [ (* Case: len % 0x50 = 0x20 *)
        DISCH_TAC THEN

        SUBGOAL_THEN `val (num_5blocks_adjusted:int64) * 0x50 + 0x20 = val (num_blocks_adjusted:int64)` ASSUME_TAC THENL
        [ UNDISCH_TAC `val (word_sub
            (word_sub (num_blocks_adjusted:int64)
                      (word_mul (word 0x50) (num_5blocks_adjusted:int64)))
            (word 0x20)) =
            0x0` THEN
          REWRITE_TAC [VAL_EQ_0; WORD_SUB_EQ_0] THEN
          REWRITE_TAC [WORD_RULE `!x:int64. word_mul (word 0x50) x = word(val x * 0x50)`] THEN
          REWRITE_TAC[GSYM VAL_EQ] THEN
          SUBGOAL_THEN `val (num_5blocks_adjusted:int64) * 0x50 < 2 EXP 64` MP_TAC THENL
          [ UNDISCH_TAC `val (num_5blocks_adjusted:int64) * 0x50 <= val (num_blocks_adjusted:int64)` THEN
            UNDISCH_TAC `val (num_blocks_adjusted:int64) <= 2 EXP 24` THEN
            ARITH_TAC; ALL_TAC] THEN
          REWRITE_TAC[VAL_WORD_SUB_CASES] THEN
          SIMP_TAC[VAL_WORD; DIMINDEX_64; MOD_LT] THEN
          UNDISCH_TAC `val (num_5blocks_adjusted:int64) * 0x50 <= val (num_blocks_adjusted:int64)` THEN
          NUM_REDUCE_TAC THEN ARITH_TAC; ALL_TAC] THEN

        SUBGOAL_THEN `~(val (num_5blocks_adjusted:int64) * 0x50 + 0x40 = val (num_blocks_adjusted:int64))` ASSUME_TAC THENL
        [ UNDISCH_TAC `val (num_5blocks_adjusted:int64) * 0x50 + 0x20 = val (num_blocks_adjusted:int64)` THEN
          ARITH_TAC; ALL_TAC] THEN
        SUBGOAL_THEN `~(val (num_5blocks_adjusted:int64) * 0x50 + 0x30 = val (num_blocks_adjusted:int64))` ASSUME_TAC THENL
        [ UNDISCH_TAC `val (num_5blocks_adjusted:int64) * 0x50 + 0x20 = val (num_blocks_adjusted:int64)` THEN
          ARITH_TAC; ALL_TAC] THEN

        SUBGOAL_THEN `val (num_5blocks_adjusted:int64) * 0x50 + 0x20 <= val (len:int64)` ASSUME_TAC THENL
        [ UNDISCH_TAC `val (num_5blocks_adjusted:int64) * 0x50 + 0x20 = val (num_blocks_adjusted:int64)` THEN
          UNDISCH_TAC `val (num_blocks_adjusted:int64) <= val (len:int64)` THEN
          ARITH_TAC; ALL_TAC] THEN
        MP_TAC (SPECL [`ct_ptr:int64`; `num_5blocks_adjusted:int64`; `len:int64`; `ct:byte list`; `s7:armstate`] READ_TAIL2_LEMMA) THEN
        ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN

        (* Assumptions that help with reasoning about nonoverlapping
         so that the universally quantified assumption stays.
         See: https://hol-light.zulipchat.com/#narrow/channel/474190-s2n-bignum/topic/.E2.9C.94.20Symbolic.20simulation.20removed.20assumption/with/541554894 *)
        SUBGOAL_THEN `0x50 * (val (num_5blocks_adjusted:int64)) < 0x2 EXP 0x40` ASSUME_TAC THENL
        [ UNDISCH_TAC `val (num_5blocks_adjusted:int64) * 0x50 <= val (num_blocks_adjusted:int64)` THEN
          UNDISCH_TAC `val (num_blocks_adjusted:int64) <= 0x2 EXP 0x18` THEN
          ARITH_TAC; ALL_TAC] THEN
        SUBGOAL_THEN `val ((word (0x50 * val (num_5blocks_adjusted:int64))):int64) = 0x50 * val num_5blocks_adjusted` ASSUME_TAC THENL [
          IMP_REWRITE_TAC[VAL_WORD; DIMINDEX_64; MOD_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
        POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN

        ARM_ACCSTEPS_TAC AES_XTS_DECRYPT_EXEC [] (8--68) THEN
        XTSDEC_TAC `Q0:(armstate,int128)component`
          `val (num_5blocks_adjusted:int64) * 0x50` `val (num_5blocks_adjusted:int64) * 0x5` THEN
        XTSDEC_TAC `Q1:(armstate,int128)component`
          `val (num_5blocks_adjusted:int64) * 0x50 + 0x10` `val (num_5blocks_adjusted:int64) * 0x5 + 0x1` THEN

        (* The following lemmas are for NONSELFMODIFYING_STATE_UPDATE_TAC when store back to pt_ptr *)
        RULE_ASSUM_TAC(REWRITE_RULE
          [WORD_RULE `word_mul (word 0x50) num_5blocks_adjusted:int64 = word(0x50 * val num_5blocks_adjusted)`]) THEN

        ARM_ACCSTEPS_TAC AES_XTS_DECRYPT_EXEC [] (69--77) THEN
        TWEAK_TAC `Q6:(armstate,int128)component` `val (num_5blocks_adjusted:int64) * 0x5 + 0x2` `val (num_5blocks_adjusted:int64) * 0x5 + 0x1` THEN

        ARM_ACCSTEPS_TAC AES_XTS_DECRYPT_EXEC [] (78--78) THEN
        ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
        REPEAT CONJ_TAC THENL
        [
          REWRITE_TAC[acc_len] THEN ASM_SIMP_TAC[] THEN CONV_TAC WORD_RULE;
          REWRITE_TAC[acc_len] THEN ASM_SIMP_TAC[] THEN CONV_TAC WORD_RULE;
          REWRITE_TAC[acc_blocks] THEN ASM_SIMP_TAC[] THEN CONV_TAC WORD_RULE;

          REWRITE_TAC[acc_len] THEN ASM_SIMP_TAC[LE_REFL] THEN
          SUBGOAL_THEN `val ((word (0x50 * val (num_5blocks_adjusted:int64) + 0x20)):int64) = 0x50 * val num_5blocks_adjusted + 0x20` ASSUME_TAC THENL
          [ IMP_REWRITE_TAC[VAL_WORD; MOD_LT; DIMINDEX_64] THEN
            UNDISCH_TAC `val (num_5blocks_adjusted:int64) * 0x50 + 0x20 <= val (len:int64)` THEN
            UNDISCH_TAC `val (len:int64) <= 0x2 EXP 0x18` THEN
            ARITH_TAC; ALL_TAC] THEN
          POP_ASSUM(fun th -> REWRITE_TAC[th]) THEN

          (* Remove quantifier *)
          UNDISCH_TAC
          `forall i.
            i < 0x50 * val (num_5blocks_adjusted:int64)
            ==> read (memory :> bytes8 (word_add pt_ptr (word i))) s78 =
                EL i (aes256_xts_decrypt ct (0x50 * val num_5blocks_adjusted) iv key1 key2)` THEN
          MP_TAC (SPECL [`0x50 * val (num_5blocks_adjusted:int64) + 0x20:num`; `pt_ptr:int64`;
                         `(aes256_xts_decrypt ct (0x50 * val (num_5blocks_adjusted:int64) + 0x20) iv key1 key2):byte list`;
                         `s78:armstate`] BYTE_LIST_TO_NUM_THM) THEN
          ANTS_TAC THENL[
            REWRITE_TAC[ARITH_RULE `0x50 * i + 0x20 = 0x10 * (5 * i + 2)`;
                        LENGTH_OF_AES256_XTS_DECRYPT_FULL_BLOCKS] THEN
            ARITH_TAC
            ; ALL_TAC] THEN
          DISCH_THEN (fun th -> REWRITE_TAC[th]) THEN
          MP_TAC (SPECL [`0x50 * val (num_5blocks_adjusted:int64):num`; `pt_ptr:int64`;
                         `(aes256_xts_decrypt ct (0x50 * val (num_5blocks_adjusted:int64)) iv key1 key2):byte list`;
                         `s78:armstate`] BYTE_LIST_TO_NUM_THM) THEN
          ANTS_TAC THENL[
            REWRITE_TAC[ARITH_RULE `0x50 * i = 0x10 * 5 * i`;
                        LENGTH_OF_AES256_XTS_DECRYPT_FULL_BLOCKS] THEN
            ARITH_TAC
            ; ALL_TAC] THEN
          DISCH_THEN (fun th -> REWRITE_TAC[th]) THEN
          DISCH_TAC THEN

          REWRITE_TAC[ARITH_RULE `0x50 * i + 0x20 = (0x50 * i + 0x10) + 0x10`] THEN
          (* Use SPECL to force IMP_REWRITE_TAC to apply once once *)
          IMP_REWRITE_TAC[(SPECL [`pt_ptr:int64`; `(0x50 * val (num_5blocks_adjusted:int64) + 0x10):num`;
            `x:byte list`; `s78:armstate`] READ_BYTES_AND_BYTE128_SPLIT)] THEN
          EXISTS_TAC `(aes256_xts_decrypt ct (0x50 * val (num_5blocks_adjusted:int64) + 0x20) iv key1 key2)` THEN
          REPEAT CONJ_TAC THENL [
            MP_TAC (SPECL [`0x5 * val (num_5blocks_adjusted:int64) + 0x2:num`;
              `ct:byte list`; `iv:int128`; `key1:int128 list`;
              `key2:int128 list`] LENGTH_OF_AES256_XTS_DECRYPT_FULL_BLOCKS) THEN
            REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_ASSOC; GSYM ADD_ASSOC] THEN
            CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
            IMP_REWRITE_TAC[SUB_LIST_LENGTH_IMPLIES] THEN ARITH_TAC;

            MP_TAC (SPECL [`0x5 * val (num_5blocks_adjusted:int64) + 0x2:num`;
              `ct:byte list`; `iv:int128`; `key1:int128 list`;
              `key2:int128 list`] LENGTH_OF_AES256_XTS_DECRYPT_FULL_BLOCKS) THEN
            REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_ASSOC; GSYM ADD_ASSOC] THEN
            CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
            IMP_REWRITE_TAC[SUB_LIST_LENGTH_IMPLIES] THEN ARITH_TAC;

            (* Establish that one xts decrypt round is the same as
               selecting one block of bytes from calling the top-level function. *)
            REWRITE_TAC[aes256_xts_decrypt] THEN
            SIMP_TAC[ARITH_RULE `~(0x50 * i + 0x20 < 0x10)`] THEN
            SUBGOAL_THEN `(0x50 * val (num_5blocks_adjusted:int64) + 0x20) MOD 0x10 = 0` SUBST1_TAC THENL
            [ REWRITE_TAC[ARITH_RULE `80 * i + 32 = 16 * (5 * i + 2)`] THEN
              REWRITE_TAC[MOD_MULT]
            ; ALL_TAC] THEN
            CONV_TAC (DEPTH_CONV let_CONV) THEN
            REWRITE_TAC[SUB_0; ARITH_RULE `(0x50 * i + 0x20) DIV 0x10 = 0x5 * i + 0x2`] THEN
            SIMP_TAC[ARITH_RULE `~(0x5 * i + 0x2 < 0x2)`;
                     ARITH_RULE `(0x5 * i + 0x2) - 0x2 = 0x5 * i`;
                     ARITH_RULE `(0x5 * i + 0x2) - 0x1 = 0x5 * i + 0x1`] THEN

            MP_TAC (SPECL [`0`;`5 * val (num_5blocks_adjusted:int64):num`;
              `ct:byte list`; `iv:int128`; `key1:int128 list`; `key2:int128 list`]
              LENGTH_OF_AES256_XTS_DECRYPT_REC) THEN
            SIMP_TAC[ARITH_RULE `~(5 * i < 0)`;
                     ARITH_RULE `(0x5 * i - 0x0 + 0x1) * 0x10 = 0x50 * i + 0x10`] THEN
            IMP_REWRITE_TAC[SUB_LIST_APPEND_RIGHT_LEMMA] THEN DISCH_TAC THEN

            MP_TAC (SPECL [`5 * val (num_5blocks_adjusted:int64) + 1:num`; `0x0:num`;
              `ct:byte list`; `iv:int128`; `key1:int128 list`; `key2:int128 list`]
              LENGTH_OF_AES256_XTS_DECRYPT_TAIL) THEN
            CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[ADD_0] THEN DISCH_TAC THEN
            IMP_REWRITE_TAC[SUB_LIST_LENGTH_IMPLIES] THEN

            REWRITE_TAC[AES256_XTS_DECRYPT_TAIL_WHEN_1BLOCK] THEN
            SIMP_TAC[ARITH_RULE `i * 0x50 + 0x10 = (i * 0x5 + 0x1) * 0x10`;
                     ARITH_RULE `i * 0x5 = 0x5 * i`];

            (* Proving that reading previous bytes is the same as the spec *)
            REWRITE_TAC[ARITH_RULE `0x50 * i + 0x10 = 0x10 * (5 * i + 1)`;
                        ARITH_RULE `0x50 * i + 0x20 = 0x10 * (5 * i + 1) + 0x10`] THEN
            REWRITE_TAC[SUB_LIST_OF_AES256_XTS_DECRYPT_FULL_BLOCKS] THEN
            ASM_REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_ASSOC] THEN CONV_TAC NUM_REDUCE_CONV
          ] THEN

          IMP_REWRITE_TAC[(SPECL [`pt_ptr:int64`; `(0x50 * val (num_5blocks_adjusted:int64)):num`;
            `(aes256_xts_decrypt ct (0x50 * val (num_5blocks_adjusted:int64) + 0x10) iv key1 key2):byte list`;
            `s78:armstate`]
            READ_BYTES_AND_BYTE128_SPLIT)] THEN
          EXISTS_TAC `ct:byte list` THEN EXISTS_TAC `iv:int128` THEN
          EXISTS_TAC `key1:int128 list` THEN EXISTS_TAC `key2:int128 list` THEN
          REPEAT CONJ_TAC THENL [
            MP_TAC (SPECL [`0x5 * val (num_5blocks_adjusted:int64) + 0x1:num`;
              `ct:byte list`; `iv:int128`; `key1:int128 list`;
              `key2:int128 list`] LENGTH_OF_AES256_XTS_DECRYPT_FULL_BLOCKS) THEN
            REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_ASSOC; GSYM ADD_ASSOC] THEN
            CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
            IMP_REWRITE_TAC[SUB_LIST_LENGTH_IMPLIES] THEN ARITH_TAC;

            MP_TAC (SPECL [`0x5 * val (num_5blocks_adjusted:int64) + 0x1:num`;
              `ct:byte list`; `iv:int128`; `key1:int128 list`;
              `key2:int128 list`] LENGTH_OF_AES256_XTS_DECRYPT_FULL_BLOCKS) THEN
            REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_ASSOC; GSYM ADD_ASSOC] THEN
            CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
            IMP_REWRITE_TAC[SUB_LIST_LENGTH_IMPLIES] THEN ARITH_TAC;

            (* Establish that one xts decrypt round is the same as
               selecting one block of bytes from calling the top-level function. *)
            REWRITE_TAC[aes256_xts_decrypt] THEN
            SIMP_TAC[ARITH_RULE `~(0x50 * i + 0x10 < 0x10)`] THEN
            SUBGOAL_THEN `(0x50 * val (num_5blocks_adjusted:int64) + 0x10) MOD 0x10 = 0` SUBST1_TAC THENL
            [ REWRITE_TAC[ARITH_RULE `80 * i + 16 = 16 * (5 * i + 1)`] THEN
              REWRITE_TAC[MOD_MULT]
            ; ALL_TAC] THEN
            CONV_TAC (DEPTH_CONV let_CONV) THEN
            REWRITE_TAC[SUB_0; ARITH_RULE `(0x50 * i + 0x10) DIV 0x10 = 0x5 * i + 0x1`] THEN
            (* Two cases: i = 0 then execute tail branch, else execute recursion branch *)
            COND_CASES_TAC THENL
            [ SUBGOAL_THEN `val (num_5blocks_adjusted:int64) = 0` SUBST1_TAC THENL
              [ UNDISCH_TAC `5 * val (num_5blocks_adjusted:int64) + 1 < 2` THEN
                UNDISCH_TAC `0 < val (num_5blocks_adjusted:int64)` THEN
                ARITH_TAC
              ; ALL_TAC] THEN CONV_TAC NUM_REDUCE_CONV THEN

              MP_TAC (SPECL [`0x0:num`; `0x0:num`; `ct:byte list`; `iv:int128`; `key1:int128 list`; `key2:int128 list`]
                LENGTH_OF_AES256_XTS_DECRYPT_TAIL) THEN
              CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[ADD_0] THEN DISCH_TAC THEN
              IMP_REWRITE_TAC[(ISPECL [`(aes256_xts_decrypt_tail 0x0 0x0 ct iv key1 key2):byte list`;
                `0x10:num`] SUB_LIST_LENGTH_IMPLIES)] THEN

              REWRITE_TAC[AES256_XTS_DECRYPT_TAIL_WHEN_1BLOCK] THEN
              CONV_TAC NUM_REDUCE_CONV;

              SIMP_TAC[ARITH_RULE `(0x5 * i + 0x1) - 0x2 = 0x5 * i - 0x1`;
                       ARITH_RULE `(0x5 * i + 0x1) - 0x1 = 0x5 * i`] THEN

              MP_TAC (SPECL [`0`;`5 * val (num_5blocks_adjusted:int64) - 1:num`;
                `ct:byte list`; `iv:int128`; `key1:int128 list`; `key2:int128 list`]
                LENGTH_OF_AES256_XTS_DECRYPT_REC) THEN
              SUBGOAL_THEN `~(0x5 * val (num_5blocks_adjusted:int64) - 0x1 < 0x0)` ASSUME_TAC THENL
              [ UNDISCH_TAC `~(0x5 * val (num_5blocks_adjusted:int64) + 0x1 < 0x2)` THEN ARITH_TAC; ALL_TAC ] THEN
              ASM_SIMP_TAC[] THEN
              IMP_REWRITE_TAC[ARITH_RULE `~(0x5 * i + 0x1 < 0x2) ==> (0x5 * i - 1 - 0x0 + 0x1) * 0x10 = 0x50 * i`] THEN
              IMP_REWRITE_TAC[SUB_LIST_APPEND_RIGHT_LEMMA] THEN DISCH_TAC THEN

              MP_TAC (SPECL [`5 * val (num_5blocks_adjusted:int64):num`;
                `0x0:num`; `ct:byte list`; `iv:int128`; `key1:int128 list`; `key2:int128 list`]
                LENGTH_OF_AES256_XTS_DECRYPT_TAIL) THEN
              CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[ADD_0] THEN DISCH_TAC THEN
              IMP_REWRITE_TAC[SUB_LIST_LENGTH_IMPLIES] THEN

              REWRITE_TAC[AES256_XTS_DECRYPT_TAIL_WHEN_1BLOCK] THEN
              SIMP_TAC[ARITH_RULE `i * 0x50 = (i * 0x5) * 0x10`;
                       ARITH_RULE `i * 0x5 = 0x5 * i`]];

            (* Proving that reading previous bytes is the same as the spec *)
            REWRITE_TAC[ARITH_RULE `0x50 * i = 0x10 * 5 * i`;
                        ARITH_RULE `0x50 * i + 0x10 = 0x10 * 5 * i + 0x10`] THEN
            REWRITE_TAC[SUB_LIST_OF_AES256_XTS_DECRYPT_FULL_BLOCKS] THEN
            IMP_REWRITE_TAC[SUB_LIST_LENGTH_IMPLIES] THEN
            REWRITE_TAC[LENGTH_OF_AES256_XTS_DECRYPT_FULL_BLOCKS]]
        ]; ALL_TAC] THEN

      DISCH_TAC THEN
      ARM_ACCSTEPS_TAC AES_XTS_DECRYPT_EXEC [] (8--9) THEN
      FIRST_X_ASSUM MP_TAC THEN
      COND_CASES_TAC THENL
      [ (* Case: len % 0x50 = 0x10 *)
        DISCH_TAC THEN

        SUBGOAL_THEN `val (num_5blocks_adjusted:int64) * 0x50 + 0x10 = val (num_blocks_adjusted:int64)` ASSUME_TAC THENL
        [ UNDISCH_TAC `val (word_sub
            (word_sub (num_blocks_adjusted:int64)
                      (word_mul (word 0x50) (num_5blocks_adjusted:int64)))
            (word 0x10)) =
            0x0` THEN
          REWRITE_TAC [VAL_EQ_0; WORD_SUB_EQ_0] THEN
          REWRITE_TAC [WORD_RULE `!x:int64. word_mul (word 0x50) x = word(val x * 0x50)`] THEN
          REWRITE_TAC[GSYM VAL_EQ] THEN
          SUBGOAL_THEN `val (num_5blocks_adjusted:int64) * 0x50 < 2 EXP 64` MP_TAC THENL
          [ UNDISCH_TAC `val (num_5blocks_adjusted:int64) * 0x50 <= val (num_blocks_adjusted:int64)` THEN
            UNDISCH_TAC `val (num_blocks_adjusted:int64) <= 2 EXP 24` THEN
            ARITH_TAC; ALL_TAC] THEN
          REWRITE_TAC[VAL_WORD_SUB_CASES] THEN
          SIMP_TAC[VAL_WORD; DIMINDEX_64; MOD_LT] THEN
          UNDISCH_TAC `val (num_5blocks_adjusted:int64) * 0x50 <= val (num_blocks_adjusted:int64)` THEN
          NUM_REDUCE_TAC THEN ARITH_TAC; ALL_TAC] THEN

        SUBGOAL_THEN `~(val (num_5blocks_adjusted:int64) * 0x50 + 0x40 = val (num_blocks_adjusted:int64))` ASSUME_TAC THENL
        [ UNDISCH_TAC `val (num_5blocks_adjusted:int64) * 0x50 + 0x10 = val (num_blocks_adjusted:int64)` THEN
          ARITH_TAC; ALL_TAC] THEN
        SUBGOAL_THEN `~(val (num_5blocks_adjusted:int64) * 0x50 + 0x30 = val (num_blocks_adjusted:int64))` ASSUME_TAC THENL
        [ UNDISCH_TAC `val (num_5blocks_adjusted:int64) * 0x50 + 0x10 = val (num_blocks_adjusted:int64)` THEN
          ARITH_TAC; ALL_TAC] THEN
        SUBGOAL_THEN `~(val (num_5blocks_adjusted:int64) * 0x50 + 0x20 = val (num_blocks_adjusted:int64))` ASSUME_TAC THENL
        [ UNDISCH_TAC `val (num_5blocks_adjusted:int64) * 0x50 + 0x10 = val (num_blocks_adjusted:int64)` THEN
          ARITH_TAC; ALL_TAC] THEN

        SUBGOAL_THEN `val (num_5blocks_adjusted:int64) * 0x50 + 0x10 <= val (len:int64)` ASSUME_TAC THENL
        [ UNDISCH_TAC `val (num_5blocks_adjusted:int64) * 0x50 + 0x10 = val (num_blocks_adjusted:int64)` THEN
          UNDISCH_TAC `val (num_blocks_adjusted:int64) <= val (len:int64)` THEN
          ARITH_TAC; ALL_TAC] THEN
        MP_TAC (SPECL [`ct_ptr:int64`; `num_5blocks_adjusted:int64`; `len:int64`; `ct:byte list`; `s9:armstate`] READ_TAIL1_LEMMA) THEN
        ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN

        (* Assumptions that help with reasoning about nonoverlapping
         so that the universally quantified assumption stays.
         See: https://hol-light.zulipchat.com/#narrow/channel/474190-s2n-bignum/topic/.E2.9C.94.20Symbolic.20simulation.20removed.20assumption/with/541554894 *)
        SUBGOAL_THEN `0x50 * (val (num_5blocks_adjusted:int64)) < 0x2 EXP 0x40` ASSUME_TAC THENL
        [ UNDISCH_TAC `val (num_5blocks_adjusted:int64) * 0x50 <= val (num_blocks_adjusted:int64)` THEN
          UNDISCH_TAC `val (num_blocks_adjusted:int64) <= 0x2 EXP 0x18` THEN
          ARITH_TAC; ALL_TAC] THEN
        SUBGOAL_THEN `val ((word (0x50 * val (num_5blocks_adjusted:int64))):int64) = 0x50 * val num_5blocks_adjusted` ASSUME_TAC THENL [
          IMP_REWRITE_TAC[VAL_WORD; DIMINDEX_64; MOD_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
        POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN

        ARM_ACCSTEPS_TAC AES_XTS_DECRYPT_EXEC [] (10--40) THEN
        XTSDEC_TAC `Q0:(armstate,int128)component`
          `val (num_5blocks_adjusted:int64) * 0x50` `val (num_5blocks_adjusted:int64) * 0x5` THEN

        (* The following lemmas are for NONSELFMODIFYING_STATE_UPDATE_TAC when store back to pt_ptr *)
        RULE_ASSUM_TAC(REWRITE_RULE
          [WORD_RULE `word_mul (word 0x50) num_5blocks_adjusted:int64 = word(0x50 * val num_5blocks_adjusted)`]) THEN

        ARM_ACCSTEPS_TAC AES_XTS_DECRYPT_EXEC [] (41--49) THEN
        TWEAK_TAC `Q6:(armstate,int128)component` `val (num_5blocks_adjusted:int64) * 0x5 + 0x1` `val (num_5blocks_adjusted:int64) * 0x5` THEN

        ARM_ACCSTEPS_TAC AES_XTS_DECRYPT_EXEC [] (50--50) THEN
        ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
        REPEAT CONJ_TAC THENL
        [
          REWRITE_TAC[acc_len] THEN ASM_SIMP_TAC[] THEN CONV_TAC WORD_RULE;
          REWRITE_TAC[acc_len] THEN ASM_SIMP_TAC[] THEN CONV_TAC WORD_RULE;
          REWRITE_TAC[acc_blocks] THEN ASM_SIMP_TAC[] THEN CONV_TAC WORD_RULE;

          REWRITE_TAC[acc_len] THEN ASM_SIMP_TAC[LE_REFL] THEN
          SUBGOAL_THEN `val ((word (0x50 * val (num_5blocks_adjusted:int64) + 0x10)):int64) =
            0x50 * val num_5blocks_adjusted + 0x10` ASSUME_TAC THENL
          [ IMP_REWRITE_TAC[VAL_WORD; MOD_LT; DIMINDEX_64] THEN
            UNDISCH_TAC `val (num_5blocks_adjusted:int64) * 0x50 + 0x10 <= val (len:int64)` THEN
            UNDISCH_TAC `val (len:int64) <= 0x2 EXP 0x18` THEN
            ARITH_TAC; ALL_TAC] THEN
          POP_ASSUM(fun th -> REWRITE_TAC[th]) THEN

          (* Remove quantifier *)
          UNDISCH_TAC
          `forall i.
            i < 0x50 * val (num_5blocks_adjusted:int64)
            ==> read (memory :> bytes8 (word_add pt_ptr (word i))) s50 =
                EL i (aes256_xts_decrypt ct (0x50 * val num_5blocks_adjusted) iv key1 key2)` THEN
          MP_TAC (SPECL [`0x50 * val (num_5blocks_adjusted:int64) + 0x10:num`; `pt_ptr:int64`;
                         `(aes256_xts_decrypt ct (0x50 * val (num_5blocks_adjusted:int64) + 0x10) iv key1 key2):byte list`;
                         `s50:armstate`] BYTE_LIST_TO_NUM_THM) THEN
          ANTS_TAC THENL[
            REWRITE_TAC[ARITH_RULE `0x50 * i + 0x10 = 0x10 * (5 * i + 1)`;
                        LENGTH_OF_AES256_XTS_DECRYPT_FULL_BLOCKS] THEN
            ARITH_TAC
            ; ALL_TAC] THEN
          DISCH_THEN (fun th -> REWRITE_TAC[th]) THEN
          MP_TAC (SPECL [`0x50 * val (num_5blocks_adjusted:int64):num`; `pt_ptr:int64`;
                         `(aes256_xts_decrypt ct (0x50 * val (num_5blocks_adjusted:int64)) iv key1 key2):byte list`;
                         `s50:armstate`] BYTE_LIST_TO_NUM_THM) THEN
          ANTS_TAC THENL[
            REWRITE_TAC[ARITH_RULE `0x50 * i = 0x10 * 5 * i`;
                        LENGTH_OF_AES256_XTS_DECRYPT_FULL_BLOCKS] THEN
            ARITH_TAC
            ; ALL_TAC] THEN
          DISCH_THEN (fun th -> REWRITE_TAC[th]) THEN
          DISCH_TAC THEN

          IMP_REWRITE_TAC[(SPECL [`pt_ptr:int64`; `(0x50 * val (num_5blocks_adjusted:int64)):num`;
            `(aes256_xts_decrypt ct (0x50 * val (num_5blocks_adjusted:int64) + 0x10) iv key1 key2):byte list`;
            `s50:armstate`]
            READ_BYTES_AND_BYTE128_SPLIT)] THEN
          EXISTS_TAC `ct:byte list` THEN EXISTS_TAC `iv:int128` THEN
          EXISTS_TAC `key1:int128 list` THEN EXISTS_TAC `key2:int128 list` THEN
          REPEAT CONJ_TAC THENL [
            MP_TAC (SPECL [`0x5 * val (num_5blocks_adjusted:int64) + 0x1:num`;
              `ct:byte list`; `iv:int128`; `key1:int128 list`;
              `key2:int128 list`] LENGTH_OF_AES256_XTS_DECRYPT_FULL_BLOCKS) THEN
            REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_ASSOC; GSYM ADD_ASSOC] THEN
            CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
            IMP_REWRITE_TAC[SUB_LIST_LENGTH_IMPLIES] THEN ARITH_TAC;

            MP_TAC (SPECL [`0x5 * val (num_5blocks_adjusted:int64) + 0x1:num`;
              `ct:byte list`; `iv:int128`; `key1:int128 list`;
              `key2:int128 list`] LENGTH_OF_AES256_XTS_DECRYPT_FULL_BLOCKS) THEN
            REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_ASSOC; GSYM ADD_ASSOC] THEN
            CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
            IMP_REWRITE_TAC[SUB_LIST_LENGTH_IMPLIES] THEN ARITH_TAC;

            (* Establish that one xts decrypt round is the same as
               selecting one block of bytes from calling the top-level function. *)
            REWRITE_TAC[aes256_xts_decrypt] THEN
            SIMP_TAC[ARITH_RULE `~(0x50 * i + 0x10 < 0x10)`] THEN
            SUBGOAL_THEN `(0x50 * val (num_5blocks_adjusted:int64) + 0x10) MOD 0x10 = 0` SUBST1_TAC THENL
            [ REWRITE_TAC[ARITH_RULE `80 * i + 16 = 16 * (5 * i + 1)`] THEN
              REWRITE_TAC[MOD_MULT]
            ; ALL_TAC] THEN
            CONV_TAC (DEPTH_CONV let_CONV) THEN
            REWRITE_TAC[SUB_0; ARITH_RULE `(0x50 * i + 0x10) DIV 0x10 = 0x5 * i + 0x1`] THEN
            (* Two cases: i = 0 then execute tail branch, else execute recursion branch *)
            COND_CASES_TAC THENL
            [ SUBGOAL_THEN `val (num_5blocks_adjusted:int64) = 0` SUBST1_TAC THENL
              [ UNDISCH_TAC `5 * val (num_5blocks_adjusted:int64) + 1 < 2` THEN
                UNDISCH_TAC `0 < val (num_5blocks_adjusted:int64)` THEN
                ARITH_TAC
              ; ALL_TAC] THEN CONV_TAC NUM_REDUCE_CONV THEN

              MP_TAC (SPECL [`0x0:num`; `0x0:num`; `ct:byte list`; `iv:int128`; `key1:int128 list`; `key2:int128 list`]
                LENGTH_OF_AES256_XTS_DECRYPT_TAIL) THEN
              CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[ADD_0] THEN DISCH_TAC THEN
              IMP_REWRITE_TAC[(ISPECL [`(aes256_xts_decrypt_tail 0x0 0x0 ct iv key1 key2):byte list`;
                `0x10:num`] SUB_LIST_LENGTH_IMPLIES)] THEN

              REWRITE_TAC[AES256_XTS_DECRYPT_TAIL_WHEN_1BLOCK] THEN
              CONV_TAC NUM_REDUCE_CONV;

              SIMP_TAC[ARITH_RULE `(0x5 * i + 0x1) - 0x2 = 0x5 * i - 0x1`;
                       ARITH_RULE `(0x5 * i + 0x1) - 0x1 = 0x5 * i`] THEN

              MP_TAC (SPECL [`0`;`5 * val (num_5blocks_adjusted:int64) - 1:num`;
                `ct:byte list`; `iv:int128`; `key1:int128 list`; `key2:int128 list`]
                LENGTH_OF_AES256_XTS_DECRYPT_REC) THEN
              SUBGOAL_THEN `~(0x5 * val (num_5blocks_adjusted:int64) - 0x1 < 0x0)` ASSUME_TAC THENL
              [ UNDISCH_TAC `~(0x5 * val (num_5blocks_adjusted:int64) + 0x1 < 0x2)` THEN ARITH_TAC; ALL_TAC ] THEN
              ASM_SIMP_TAC[] THEN
              IMP_REWRITE_TAC[ARITH_RULE `~(0x5 * i + 0x1 < 0x2) ==> (0x5 * i - 1 - 0x0 + 0x1) * 0x10 = 0x50 * i`] THEN
              IMP_REWRITE_TAC[SUB_LIST_APPEND_RIGHT_LEMMA] THEN DISCH_TAC THEN

              MP_TAC (SPECL [`5 * val (num_5blocks_adjusted:int64):num`;
                `0x0:num`; `ct:byte list`; `iv:int128`; `key1:int128 list`; `key2:int128 list`]
                LENGTH_OF_AES256_XTS_DECRYPT_TAIL) THEN
              CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[ADD_0] THEN DISCH_TAC THEN
              IMP_REWRITE_TAC[SUB_LIST_LENGTH_IMPLIES] THEN

              REWRITE_TAC[AES256_XTS_DECRYPT_TAIL_WHEN_1BLOCK] THEN
              SIMP_TAC[ARITH_RULE `i * 0x50 = (i * 0x5) * 0x10`;
                       ARITH_RULE `i * 0x5 = 0x5 * i`]];

            (* Proving that reading previous bytes is the same as the spec *)
            REWRITE_TAC[ARITH_RULE `0x50 * i = 0x10 * 5 * i`;
                        ARITH_RULE `0x50 * i + 0x10 = 0x10 * 5 * i + 0x10`] THEN
            REWRITE_TAC[SUB_LIST_OF_AES256_XTS_DECRYPT_FULL_BLOCKS] THEN
            IMP_REWRITE_TAC[SUB_LIST_LENGTH_IMPLIES] THEN
            REWRITE_TAC[LENGTH_OF_AES256_XTS_DECRYPT_FULL_BLOCKS]]
        ]
      ; ALL_TAC] THEN

      (* Case: len % 0x50 = 0 *)
      DISCH_TAC THEN
      SUBGOAL_THEN `val (num_5blocks_adjusted:int64) * 0x50 = val (num_blocks_adjusted:int64)` ASSUME_TAC THENL
      [ MATCH_MP_TAC (SPECL [`val (num_blocks_adjusted:int64)`; `val (num_5blocks_adjusted:int64)`] DIVISION_BY_80_LEMMA) THEN
        REPEAT CONJ_TAC THENL
        [
          EXPAND_TAC "num_5blocks_adjusted" THEN
          IMP_REWRITE_TAC[VAL_WORD; DIMINDEX_64; MOD_LT] THEN
          UNDISCH_TAC `val (num_blocks_adjusted:int64) <= 0x2 EXP 0x18` THEN
          ARITH_TAC;

          EXPAND_TAC "num_blocks_adjusted" THEN
          EXPAND_TAC "num_blocks" THEN
          COND_CASES_TAC THENL
          [
            REWRITE_TAC[NUM_BLOCKS_TO_VAL] THEN
            IMP_REWRITE_TAC[VAL_WORD; DIMINDEX_64; MOD_LT; DIVIDES_RMUL; DIVIDES_REFL] THEN
            UNDISCH_TAC `val (len:int64) <= 0x2 EXP 0x18` THEN
            ARITH_TAC;

            IMP_REWRITE_TAC[NUM_BLOCKS_MINUS1_TO_VAL] THEN
            IMP_REWRITE_TAC[VAL_WORD; DIMINDEX_64; MOD_LT; DIVIDES_RMUL; DIVIDES_REFL] THEN
            UNDISCH_TAC `val (len:int64) <= 0x2 EXP 0x18` THEN
            ARITH_TAC];

          UNDISCH_TAC `~(val (word_sub
            (word_sub (num_blocks_adjusted:int64)
              (word_mul (word 0x50) (num_5blocks_adjusted:int64)))
            (word 0x10)) = 0x0)` THEN
          REWRITE_TAC[CONTRAPOS_THM] THEN
          REWRITE_TAC[VAL_WORD_SUB_EQ_0; VAL_WORD_MUL; VAL_WORD; DIMINDEX_64;
            ARITH_RULE `0x10 MOD 0x2 EXP 0x40 = 0x10`] THEN
          REWRITE_TAC[VAL_WORD_SUB; VAL_WORD_MUL; VAL_WORD; DIMINDEX_64;
            ARITH_RULE `0x50 MOD 0x2 EXP 0x40 = 0x50`] THEN

          SUBGOAL_THEN `0x50 * val (num_5blocks_adjusted:int64) < 2 EXP 64` ASSUME_TAC THENL
          [ UNDISCH_TAC `val (num_5blocks_adjusted:int64) * 0x50 <= val (len:int64)` THEN
            UNDISCH_TAC `val (len:int64) <= 0x2 EXP 0x18` THEN
            ARITH_TAC; ALL_TAC] THEN
          MP_TAC (SPECL [`0x50 * val (num_5blocks_adjusted:int64)`; `2 EXP 64`] MOD_LT) THEN
          ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
          SIMP_TAC[] THEN DISCH_TAC THEN

          MP_TAC (SPECL [`val (num_blocks_adjusted:int64)`; `0x2 EXP 0x40`;
            `0x50 * val (num_5blocks_adjusted:int64)`]
            (ARITH_RULE `!a b c. c <= a ==> c <= b ==> a + b - c = (a - c) + b`)) THEN
          ANTS_TAC THENL [
            UNDISCH_TAC `val (num_5blocks_adjusted:int64) * 0x50 <= val (num_blocks_adjusted:int64)` THEN
            SIMP_TAC[MULT_SYM]; ALL_TAC] THEN
          ANTS_TAC THENL [
            UNDISCH_TAC `0x50 * val (num_5blocks_adjusted:int64) < 2 EXP 64` THEN
            ARITH_TAC; ALL_TAC] THEN
          ASM_SIMP_TAC[] THEN DISCH_TAC THEN

          MP_TAC (SPECL [`1`; `0x2 EXP 0x40`;
            `val (num_blocks_adjusted:int64) - 0x50 * val (num_5blocks_adjusted:int64)`]
            (CONJUNCT1 (CONJUNCT2 (CONJUNCT2 MOD_MULT_ADD)))) THEN
          REWRITE_TAC[ARITH_RULE `1 * 2 EXP 64 = 2 EXP 64`] THEN
          SIMP_TAC[] THEN DISCH_TAC THEN
          SIMP_TAC[MULT_SYM] THEN DISCH_TAC THEN
          CONV_TAC NUM_REDUCE_CONV;

          UNDISCH_TAC `~(val (word_sub
            (word_sub (num_blocks_adjusted:int64)
              (word_mul (word 0x50) (num_5blocks_adjusted:int64)))
            (word 0x20)) = 0x0)` THEN
          REWRITE_TAC[CONTRAPOS_THM] THEN
          REWRITE_TAC[VAL_WORD_SUB_EQ_0; VAL_WORD_MUL; VAL_WORD; DIMINDEX_64;
            ARITH_RULE `0x20 MOD 0x2 EXP 0x40 = 0x20`] THEN
          REWRITE_TAC[VAL_WORD_SUB; VAL_WORD_MUL; VAL_WORD; DIMINDEX_64;
            ARITH_RULE `0x50 MOD 0x2 EXP 0x40 = 0x50`] THEN

          SUBGOAL_THEN `0x50 * val (num_5blocks_adjusted:int64) < 2 EXP 64` ASSUME_TAC THENL
          [ UNDISCH_TAC `val (num_5blocks_adjusted:int64) * 0x50 <= val (len:int64)` THEN
            UNDISCH_TAC `val (len:int64) <= 0x2 EXP 0x18` THEN
            ARITH_TAC; ALL_TAC] THEN
          MP_TAC (SPECL [`0x50 * val (num_5blocks_adjusted:int64)`; `2 EXP 64`] MOD_LT) THEN
          ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
          SIMP_TAC[] THEN DISCH_TAC THEN

          MP_TAC (SPECL [`val (num_blocks_adjusted:int64)`; `0x2 EXP 0x40`;
            `0x50 * val (num_5blocks_adjusted:int64)`]
            (ARITH_RULE `!a b c. c <= a ==> c <= b ==> a + b - c = (a - c) + b`)) THEN
          ANTS_TAC THENL [
            UNDISCH_TAC `val (num_5blocks_adjusted:int64) * 0x50 <= val (num_blocks_adjusted:int64)` THEN
            SIMP_TAC[MULT_SYM]; ALL_TAC] THEN
          ANTS_TAC THENL [
            UNDISCH_TAC `0x50 * val (num_5blocks_adjusted:int64) < 2 EXP 64` THEN
            ARITH_TAC; ALL_TAC] THEN
          ASM_SIMP_TAC[] THEN DISCH_TAC THEN

          MP_TAC (SPECL [`1`; `0x2 EXP 0x40`;
            `val (num_blocks_adjusted:int64) - 0x50 * val (num_5blocks_adjusted:int64)`]
            (CONJUNCT1 (CONJUNCT2 (CONJUNCT2 MOD_MULT_ADD)))) THEN
          REWRITE_TAC[ARITH_RULE `1 * 2 EXP 64 = 2 EXP 64`] THEN
          SIMP_TAC[] THEN DISCH_TAC THEN
          SIMP_TAC[MULT_SYM] THEN DISCH_TAC THEN
          CONV_TAC NUM_REDUCE_CONV;

          UNDISCH_TAC `~(val (word_sub
            (word_sub (num_blocks_adjusted:int64)
              (word_mul (word 0x50) (num_5blocks_adjusted:int64)))
            (word 0x30)) = 0x0)` THEN
          REWRITE_TAC[CONTRAPOS_THM] THEN
          REWRITE_TAC[VAL_WORD_SUB_EQ_0; VAL_WORD_MUL; VAL_WORD; DIMINDEX_64;
            ARITH_RULE `0x30 MOD 0x2 EXP 0x40 = 0x30`] THEN
          REWRITE_TAC[VAL_WORD_SUB; VAL_WORD_MUL; VAL_WORD; DIMINDEX_64;
            ARITH_RULE `0x50 MOD 0x2 EXP 0x40 = 0x50`] THEN

          SUBGOAL_THEN `0x50 * val (num_5blocks_adjusted:int64) < 2 EXP 64` ASSUME_TAC THENL
          [ UNDISCH_TAC `val (num_5blocks_adjusted:int64) * 0x50 <= val (len:int64)` THEN
            UNDISCH_TAC `val (len:int64) <= 0x2 EXP 0x18` THEN
            ARITH_TAC; ALL_TAC] THEN
          MP_TAC (SPECL [`0x50 * val (num_5blocks_adjusted:int64)`; `2 EXP 64`] MOD_LT) THEN
          ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
          SIMP_TAC[] THEN DISCH_TAC THEN

          MP_TAC (SPECL [`val (num_blocks_adjusted:int64)`; `0x2 EXP 0x40`;
            `0x50 * val (num_5blocks_adjusted:int64)`]
            (ARITH_RULE `!a b c. c <= a ==> c <= b ==> a + b - c = (a - c) + b`)) THEN
          ANTS_TAC THENL [
            UNDISCH_TAC `val (num_5blocks_adjusted:int64) * 0x50 <= val (num_blocks_adjusted:int64)` THEN
            SIMP_TAC[MULT_SYM]; ALL_TAC] THEN
          ANTS_TAC THENL [
            UNDISCH_TAC `0x50 * val (num_5blocks_adjusted:int64) < 2 EXP 64` THEN
            ARITH_TAC; ALL_TAC] THEN
          ASM_SIMP_TAC[] THEN DISCH_TAC THEN

          MP_TAC (SPECL [`1`; `0x2 EXP 0x40`;
            `val (num_blocks_adjusted:int64) - 0x50 * val (num_5blocks_adjusted:int64)`]
            (CONJUNCT1 (CONJUNCT2 (CONJUNCT2 MOD_MULT_ADD)))) THEN
          REWRITE_TAC[ARITH_RULE `1 * 2 EXP 64 = 2 EXP 64`] THEN
          SIMP_TAC[] THEN DISCH_TAC THEN
          SIMP_TAC[MULT_SYM] THEN DISCH_TAC THEN
          CONV_TAC NUM_REDUCE_CONV;

          UNDISCH_TAC `~(val (word_sub
            (word_sub (num_blocks_adjusted:int64)
              (word_mul (word 0x50) (num_5blocks_adjusted:int64)))
            (word 0x40)) = 0x0)` THEN
          REWRITE_TAC[CONTRAPOS_THM] THEN
          REWRITE_TAC[VAL_WORD_SUB_EQ_0; VAL_WORD_MUL; VAL_WORD; DIMINDEX_64;
            ARITH_RULE `0x40 MOD 0x2 EXP 0x40 = 0x40`] THEN
          REWRITE_TAC[VAL_WORD_SUB; VAL_WORD_MUL; VAL_WORD; DIMINDEX_64;
            ARITH_RULE `0x50 MOD 0x2 EXP 0x40 = 0x50`] THEN

          SUBGOAL_THEN `0x50 * val (num_5blocks_adjusted:int64) < 2 EXP 64` ASSUME_TAC THENL
          [ UNDISCH_TAC `val (num_5blocks_adjusted:int64) * 0x50 <= val (len:int64)` THEN
            UNDISCH_TAC `val (len:int64) <= 0x2 EXP 0x18` THEN
            ARITH_TAC; ALL_TAC] THEN
          MP_TAC (SPECL [`0x50 * val (num_5blocks_adjusted:int64)`; `2 EXP 64`] MOD_LT) THEN
          ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
          SIMP_TAC[] THEN DISCH_TAC THEN

          MP_TAC (SPECL [`val (num_blocks_adjusted:int64)`; `0x2 EXP 0x40`;
            `0x50 * val (num_5blocks_adjusted:int64)`]
            (ARITH_RULE `!a b c. c <= a ==> c <= b ==> a + b - c = (a - c) + b`)) THEN
          ANTS_TAC THENL [
            UNDISCH_TAC `val (num_5blocks_adjusted:int64) * 0x50 <= val (num_blocks_adjusted:int64)` THEN
            SIMP_TAC[MULT_SYM]; ALL_TAC] THEN
          ANTS_TAC THENL [
            UNDISCH_TAC `0x50 * val (num_5blocks_adjusted:int64) < 2 EXP 64` THEN
            ARITH_TAC; ALL_TAC] THEN
          ASM_SIMP_TAC[] THEN DISCH_TAC THEN

          MP_TAC (SPECL [`1`; `0x2 EXP 0x40`;
            `val (num_blocks_adjusted:int64) - 0x50 * val (num_5blocks_adjusted:int64)`]
            (CONJUNCT1 (CONJUNCT2 (CONJUNCT2 MOD_MULT_ADD)))) THEN
          REWRITE_TAC[ARITH_RULE `1 * 2 EXP 64 = 2 EXP 64`] THEN
          SIMP_TAC[] THEN DISCH_TAC THEN
          SIMP_TAC[MULT_SYM] THEN DISCH_TAC THEN
          CONV_TAC NUM_REDUCE_CONV
          ]
        ; ALL_TAC] THEN

      SUBGOAL_THEN `~(val (num_5blocks_adjusted:int64) * 0x50 + 0x40 = val (num_blocks_adjusted:int64))` ASSUME_TAC THENL
      [ UNDISCH_TAC `val (num_5blocks_adjusted:int64) * 0x50 = val (num_blocks_adjusted:int64)` THEN
        ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `~(val (num_5blocks_adjusted:int64) * 0x50 + 0x30 = val (num_blocks_adjusted:int64))` ASSUME_TAC THENL
      [ UNDISCH_TAC `val (num_5blocks_adjusted:int64) * 0x50 = val (num_blocks_adjusted:int64)` THEN
        ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `~(val (num_5blocks_adjusted:int64) * 0x50 + 0x20 = val (num_blocks_adjusted:int64))` ASSUME_TAC THENL
      [ UNDISCH_TAC `val (num_5blocks_adjusted:int64) * 0x50 = val (num_blocks_adjusted:int64)` THEN
        ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `~(val (num_5blocks_adjusted:int64) * 0x50 + 0x10 = val (num_blocks_adjusted:int64))` ASSUME_TAC THENL
      [ UNDISCH_TAC `val (num_5blocks_adjusted:int64) * 0x50 = val (num_blocks_adjusted:int64)` THEN
        ARITH_TAC; ALL_TAC] THEN

      ARM_ACCSTEPS_TAC AES_XTS_DECRYPT_EXEC [] (10--10) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      REPEAT CONJ_TAC THENL
      [
        REWRITE_TAC[acc_len] THEN ASM_SIMP_TAC[] THEN CONV_TAC WORD_RULE;
        REWRITE_TAC[acc_len] THEN ASM_SIMP_TAC[] THEN CONV_TAC WORD_RULE;
        REWRITE_TAC[acc_blocks] THEN ASM_SIMP_TAC[] THEN CONV_TAC WORD_RULE;
        REWRITE_TAC[acc_len] THEN ASM_SIMP_TAC[LE_REFL]
      ]
    ] (* End of loop invariant proof *)
    ; ALL_TAC] THEN

  MP_TAC CIPHER_STEALING_CORRECT THEN
  REWRITE_TAC [(REWRITE_CONV [aes_xts_decrypt_mc] THENC LENGTH_CONV) `LENGTH aes_xts_decrypt_mc`] THEN
  REWRITE_TAC[set_key_schedule; C_ARGUMENTS; SOME_FLAGS;
    NONOVERLAPPING_CLAUSES; byte_list_at;
    MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  EXISTS_TAC `num_blocks:int64` THEN
  ASM_SIMP_TAC[]
);;


let AES_XTS_DECRYPT_SUBROUTINE_CORRECT = time prove
 (`!ct_ptr pt_ptr ct key1_ptr key2_ptr iv_ptr iv len
    k00 k01 k02 k03 k04 k05 k06 k07 k08 k09 k0a k0b k0c k0d k0e
    k10 k11 k12 k13 k14 k15 k16 k17 k18 k19 k1a k1b k1c k1d k1e
    pc stackpointer returnaddress.
    aligned 16 stackpointer
    /\ ALL (nonoverlapping (word_sub stackpointer (word 96), 96))
        [ (word pc, LENGTH aes_xts_decrypt_mc);
          (ct_ptr, val len); (key1_ptr, 260);
          (key2_ptr, 260); (iv_ptr, 16);
          (pt_ptr, val len)]
    /\ nonoverlapping (word pc, LENGTH aes_xts_decrypt_mc) (pt_ptr, val len)
    /\ nonoverlapping (ct_ptr, val len) (pt_ptr, val len)
    /\ nonoverlapping (key1_ptr, 260) (pt_ptr, val len)
    /\ val len >= 16 /\ val len <= 2 EXP 24 /\ LENGTH ct = val len
    ==> ensures arm
    (\s. aligned_bytes_loaded s (word pc) aes_xts_decrypt_mc /\
         read PC s = word pc /\
         read SP s = stackpointer /\
         read X30 s = returnaddress /\
         C_ARGUMENTS [ct_ptr; pt_ptr; len; key1_ptr; key2_ptr; iv_ptr] s /\
         byte_list_at ct ct_ptr len s /\
         read(memory :> bytes128 iv_ptr) s = iv /\
         set_key_schedule s key1_ptr k00 k01 k02 k03 k04 k05 k06 k07 k08 k09 k0a k0b k0c k0d k0e /\
         set_key_schedule s key2_ptr k10 k11 k12 k13 k14 k15 k16 k17 k18 k19 k1a k1b k1c k1d k1e)
    (\s. read PC s = returnaddress /\
         byte_list_at (aes256_xts_decrypt ct (val len) iv
              [k00; k01; k02; k03; k04; k05; k06; k07; k08; k09; k0a; k0b; k0c; k0d; k0e]
              [k10; k11; k12; k13; k14; k15; k16; k17; k18; k19; k1a; k1b; k1c; k1d; k1e])
              pt_ptr len s
         )
    (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI,,
     MAYCHANGE [memory :> bytes(pt_ptr, val len);
                memory :> bytes(word_sub stackpointer (word 96), 96)])`,
  REWRITE_TAC[byte_list_at; set_key_schedule;
    fst AES_XTS_DECRYPT_EXEC] THEN
  (* ~pre_post_nsteps:(7,7): 7 instructions before and after program body
      for handling stack.
    96: the byte size occupied on stack for storing preserved registers *)
  ARM_ADD_RETURN_STACK_TAC
    ~pre_post_nsteps:(7,7) AES_XTS_DECRYPT_EXEC
    (REWRITE_RULE[byte_list_at; set_key_schedule;
      fst AES_XTS_DECRYPT_EXEC] AES_XTS_DECRYPT_CORRECT)
   `[X19; X20; X21; X22; D8; D9; D10; D11; D12; D13; D14; D15]` 96
  );;
