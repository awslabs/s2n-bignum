(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

use_file_raise_failure := true;;
arm_print_log := true;;
components_print_log := true;;

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

(* byte_list_at is adapted from Amanda's code at
   https://github.com/amanda-zx/s2n-bignum/blob/ed25519/arm/sha512/utils.ml *)
let byte_list_at = define
  `byte_list_at (m : byte list) (m_p : int64) (len: int64) s =
    ! i. i < val len ==> read (memory :> bytes8(word_add m_p (word i))) s = EL i m`;;

let word_split_lemma = prove(
  `!len:int64. word_add (word_and len (word 0xf))
      (word_and len (word 0xfffffffffffffff0)) = len`,
  BITBLAST_TAC);;

let BYTE_LIST_AT_ADD_ASSUM_TAC new_pos bound =
  let rule = subst [new_pos, `new_pos:num`; bound, `bound:num`]
    `(pos:num) + bound <= LENGTH (bl:byte list) ==> new_pos < LENGTH bl` in
  let p = subst [new_pos, `new_pos:num`] `new_pos:num` in
  MP_TAC (ARITH_RULE rule) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN (LABEL_TAC "tmp") THEN
  FIRST_ASSUM(fun th -> MP_TAC(SPEC p th)) THEN
  USE_THEN "tmp" (fun th -> REWRITE_TAC[th]) THEN
  POP_ASSUM (K ALL_TAC);;

let WORD_JOIN_ASSOC_16_8 = WORD_BLAST
  `!(x0:byte) (x1:byte) (x2:byte) (x3:byte).
      word_join (word_join x3 x2:int16)
                (word_join x1 x0:int16):int32 =
      word_join (word_join (word_join x3 x2:int32) x1:int32) x0`;;

let BYTES128_TO_BYTES8_THM = prove(
  `!pos bl_ptr s.
    read (memory :> bytes128 (word_add bl_ptr (word pos))) s =
    bytes_to_int128
      [read (memory :> bytes8 (word_add bl_ptr (word (pos + 0x0)))) s;
       read (memory :> bytes8 (word_add bl_ptr (word (pos + 0x1)))) s;
       read (memory :> bytes8 (word_add bl_ptr (word (pos + 0x2)))) s;
       read (memory :> bytes8 (word_add bl_ptr (word (pos + 0x3)))) s;
       read (memory :> bytes8 (word_add bl_ptr (word (pos + 0x4)))) s;
       read (memory :> bytes8 (word_add bl_ptr (word (pos + 0x5)))) s;
       read (memory :> bytes8 (word_add bl_ptr (word (pos + 0x6)))) s;
       read (memory :> bytes8 (word_add bl_ptr (word (pos + 0x7)))) s;
       read (memory :> bytes8 (word_add bl_ptr (word (pos + 0x8)))) s;
       read (memory :> bytes8 (word_add bl_ptr (word (pos + 0x9)))) s;
       read (memory :> bytes8 (word_add bl_ptr (word (pos + 0xa)))) s;
       read (memory :> bytes8 (word_add bl_ptr (word (pos + 0xb)))) s;
       read (memory :> bytes8 (word_add bl_ptr (word (pos + 0xc)))) s;
       read (memory :> bytes8 (word_add bl_ptr (word (pos + 0xd)))) s;
       read (memory :> bytes8 (word_add bl_ptr (word (pos + 0xe)))) s;
       read (memory :> bytes8 (word_add bl_ptr (word (pos + 0xf)))) s]`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[bytes_to_int128] THEN
  REWRITE_TAC EL_16_8_CLAUSES THEN
  GEN_REWRITE_TAC TOP_DEPTH_CONV [READ_MEMORY_BYTESIZED_SPLIT; WORD_ADD_ASSOC_CONSTS] THEN
  CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
  ONCE_REWRITE_TAC [ARITH_RULE `pos + 0 = (pos:num)`] THEN
  REFL_TAC
);;

let SUB_LIST_SUCSPLIT = prove(
  `!(l:A list) n p. SUB_LIST(p,SUC n) l = APPEND (SUB_LIST(p,1) l) (SUB_LIST(p+1,n) l)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC [ARITH_RULE `SUC n = 1 + n`] THEN
  REWRITE_TAC [SUB_LIST_SPLIT]
);;

let SUB_LIST_16_TAC n exp =
  let subgoal = subst [exp, `exp:num`] `exp < LENGTH (l:A list)` in
  CONV_TAC(RAND_CONV (REWRITE_CONV[num_CONV n; SUB_LIST_SUCSPLIT])) THEN
  SUBGOAL_THEN subgoal ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[SUB_LIST_1] THEN ASM_SIMP_TAC[GSYM ADD_ASSOC] THEN NUM_REDUCE_TAC;;

let SUB_LIST_16 = prove(
  `!(l:A list) n. n + 16 <= LENGTH l ==>
    [ EL (n + 0) l; EL (n + 1) l; EL (n + 2) l; EL (n + 3) l;
      EL (n + 4) l; EL (n + 5) l; EL (n + 6) l; EL (n + 7) l;
      EL (n + 8) l; EL (n + 9) l; EL (n + 10) l; EL (n + 11) l;
      EL (n + 12) l; EL (n + 13) l; EL (n + 14) l; EL (n + 15) l
    ] = SUB_LIST (n,16) l`,
  REPEAT STRIP_TAC THEN
  MAP_EVERY (fun i ->
    if i == 0
    then SUB_LIST_16_TAC `0x10` `n:num`
    else SUB_LIST_16_TAC (mk_numeral (num (16 - i)))
    (mk_binop (mk_const("+", [`:num`, `:A`])) (mk_var("n", `:num`))
      (mk_numeral (num i)))) (0--14) THEN
  SUBGOAL_THEN `n + 15 < LENGTH (l:A list)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[APPEND; ARITH_RULE `n + 0 = n`]
);;

let BYTE_LIST_AT_5BLOCKS = prove(
  `! pos bl bl_ptr len s.
    byte_list_at bl bl_ptr len s
    ==> LENGTH bl = val len
    ==> pos + 0x50 <= LENGTH bl
    ==> (read (memory :> bytes128 (word_add bl_ptr (word pos))) s =
         bytes_to_int128 (SUB_LIST (pos, 0x10) bl) /\
         read (memory :> bytes128 (word_add (word_add bl_ptr (word pos)) (word 0x10))) s =
         bytes_to_int128 (SUB_LIST (pos + 0x10, 0x10) bl) /\
         read (memory :> bytes128 (word_add (word_add bl_ptr (word pos)) (word 0x20))) s =
         bytes_to_int128 (SUB_LIST (pos + 0x20, 0x10) bl) /\
         read (memory :> bytes128 (word_add (word_add bl_ptr (word pos)) (word 0x30))) s =
         bytes_to_int128 (SUB_LIST (pos + 0x30, 0x10) bl) /\
         read (memory :> bytes128 (word_add (word_add bl_ptr (word pos)) (word 0x40))) s =
         bytes_to_int128 (SUB_LIST (pos + 0x40, 0x10) bl))`,
  REWRITE_TAC[byte_list_at] THEN
  REPEAT STRIP_TAC THENL
  [ (* Subgoal1 *)
     MAP_EVERY (fun i -> BYTE_LIST_AT_ADD_ASSUM_TAC
      (mk_binop (mk_const("+", [`:num`, `:A`])) (mk_var("pos", `:num`))
        (mk_numeral (num i))) `0x50`) (0--15) THEN
    REWRITE_TAC[WORD_ADD_ASSOC_CONSTS] THEN
    REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[BYTES128_TO_BYTES8_THM; GSYM ADD_ASSOC] THEN
    NUM_REDUCE_TAC THEN ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN
    MP_TAC (ISPECL [`bl:byte list`; `pos:num`] SUB_LIST_16) THEN
    REWRITE_TAC[GSYM ADD_ASSOC] THEN NUM_REDUCE_TAC THEN
    DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    (* Subgoal2 *)
    MAP_EVERY (fun i -> BYTE_LIST_AT_ADD_ASSUM_TAC
      (mk_binop (mk_const("+", [`:num`, `:A`])) (mk_var("pos", `:num`))
        (mk_numeral (num i))) `0x50`) (16--31) THEN
    REWRITE_TAC[WORD_ADD_ASSOC_CONSTS] THEN
    REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[BYTES128_TO_BYTES8_THM; GSYM ADD_ASSOC] THEN
    NUM_REDUCE_TAC THEN ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN
    MP_TAC (ISPECL [`bl:byte list`; `(pos+0x10):num`] SUB_LIST_16) THEN
    REWRITE_TAC[GSYM ADD_ASSOC] THEN NUM_REDUCE_TAC THEN
    DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    (* Subgoal3 *)
    MAP_EVERY (fun i -> BYTE_LIST_AT_ADD_ASSUM_TAC
      (mk_binop (mk_const("+", [`:num`, `:A`])) (mk_var("pos", `:num`))
        (mk_numeral (num i))) `0x50`) (32--47) THEN
    REWRITE_TAC[WORD_ADD_ASSOC_CONSTS] THEN
    REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[BYTES128_TO_BYTES8_THM; GSYM ADD_ASSOC] THEN
    NUM_REDUCE_TAC THEN ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN
    MP_TAC (ISPECL [`bl:byte list`; `(pos+0x20):num`] SUB_LIST_16) THEN
    REWRITE_TAC[GSYM ADD_ASSOC] THEN NUM_REDUCE_TAC THEN
    DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    (* Subgoal4 *)
    MAP_EVERY (fun i -> BYTE_LIST_AT_ADD_ASSUM_TAC
      (mk_binop (mk_const("+", [`:num`, `:A`])) (mk_var("pos", `:num`))
        (mk_numeral (num i))) `0x50`) (48--63) THEN
    REWRITE_TAC[WORD_ADD_ASSOC_CONSTS] THEN
    REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[BYTES128_TO_BYTES8_THM; GSYM ADD_ASSOC] THEN
    NUM_REDUCE_TAC THEN ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN
    MP_TAC (ISPECL [`bl:byte list`; `(pos+0x30):num`] SUB_LIST_16) THEN
    REWRITE_TAC[GSYM ADD_ASSOC] THEN NUM_REDUCE_TAC THEN
    DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    (* Subgoal 5 *)
    MAP_EVERY (fun i -> BYTE_LIST_AT_ADD_ASSUM_TAC
      (mk_binop (mk_const("+", [`:num`, `:A`])) (mk_var("pos", `:num`))
        (mk_numeral (num i))) `0x50`) (64--79) THEN
    REWRITE_TAC[WORD_ADD_ASSOC_CONSTS] THEN
    REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[BYTES128_TO_BYTES8_THM; GSYM ADD_ASSOC] THEN
    NUM_REDUCE_TAC THEN ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN
    MP_TAC (ISPECL [`bl:byte list`; `(pos+0x40):num`] SUB_LIST_16) THEN
    REWRITE_TAC[GSYM ADD_ASSOC] THEN NUM_REDUCE_TAC THEN
    DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC
  ]
);;

let BYTE_LIST_AT_4BLOCKS = prove(
  `! pos bl bl_ptr len s.
    byte_list_at bl bl_ptr len s
    ==> LENGTH bl = val len
    ==> pos + 0x40 <= LENGTH bl
    ==> (read (memory :> bytes128 (word_add bl_ptr (word pos))) s =
         bytes_to_int128 (SUB_LIST (pos, 0x10) bl) /\
         read (memory :> bytes128 (word_add (word_add bl_ptr (word pos)) (word 0x10))) s =
         bytes_to_int128 (SUB_LIST (pos + 0x10, 0x10) bl) /\
         read (memory :> bytes128 (word_add (word_add bl_ptr (word pos)) (word 0x20))) s =
         bytes_to_int128 (SUB_LIST (pos + 0x20, 0x10) bl) /\
         read (memory :> bytes128 (word_add (word_add bl_ptr (word pos)) (word 0x30))) s =
         bytes_to_int128 (SUB_LIST (pos + 0x30, 0x10) bl))`,
  REWRITE_TAC[byte_list_at] THEN
  REPEAT STRIP_TAC THENL
  [ (* Subgoal1 *)
    MAP_EVERY (fun i -> BYTE_LIST_AT_ADD_ASSUM_TAC
      (mk_binop (mk_const("+", [`:num`, `:A`])) (mk_var("pos", `:num`))
        (mk_numeral (num i))) `0x40`) (0--15) THEN
    REWRITE_TAC[WORD_ADD_ASSOC_CONSTS] THEN
    REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[BYTES128_TO_BYTES8_THM; GSYM ADD_ASSOC] THEN
    NUM_REDUCE_TAC THEN ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN
    MP_TAC (ISPECL [`bl:byte list`; `pos:num`] SUB_LIST_16) THEN
    REWRITE_TAC[GSYM ADD_ASSOC] THEN NUM_REDUCE_TAC THEN
    DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    (* Subgoal2 *)
    MAP_EVERY (fun i -> BYTE_LIST_AT_ADD_ASSUM_TAC
      (mk_binop (mk_const("+", [`:num`, `:A`])) (mk_var("pos", `:num`))
        (mk_numeral (num i))) `0x40`) (16--31) THEN
    REWRITE_TAC[WORD_ADD_ASSOC_CONSTS] THEN
    REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[BYTES128_TO_BYTES8_THM; GSYM ADD_ASSOC] THEN
    NUM_REDUCE_TAC THEN ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN
    MP_TAC (ISPECL [`bl:byte list`; `(pos+0x10):num`] SUB_LIST_16) THEN
    REWRITE_TAC[GSYM ADD_ASSOC] THEN NUM_REDUCE_TAC THEN
    DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    (* Subgoal3 *)
    MAP_EVERY (fun i -> BYTE_LIST_AT_ADD_ASSUM_TAC
      (mk_binop (mk_const("+", [`:num`, `:A`])) (mk_var("pos", `:num`))
        (mk_numeral (num i))) `0x40`) (32--47) THEN
    REWRITE_TAC[WORD_ADD_ASSOC_CONSTS] THEN
    REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[BYTES128_TO_BYTES8_THM; GSYM ADD_ASSOC] THEN
    NUM_REDUCE_TAC THEN ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN
    MP_TAC (ISPECL [`bl:byte list`; `(pos+0x20):num`] SUB_LIST_16) THEN
    REWRITE_TAC[GSYM ADD_ASSOC] THEN NUM_REDUCE_TAC THEN
    DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    (* Subgoal4 *)
    MAP_EVERY (fun i -> BYTE_LIST_AT_ADD_ASSUM_TAC
      (mk_binop (mk_const("+", [`:num`, `:A`])) (mk_var("pos", `:num`))
        (mk_numeral (num i))) `0x40`) (48--63) THEN
    REWRITE_TAC[WORD_ADD_ASSOC_CONSTS] THEN
    REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[BYTES128_TO_BYTES8_THM; GSYM ADD_ASSOC] THEN
    NUM_REDUCE_TAC THEN ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN
    MP_TAC (ISPECL [`bl:byte list`; `(pos+0x30):num`] SUB_LIST_16) THEN
    REWRITE_TAC[GSYM ADD_ASSOC] THEN NUM_REDUCE_TAC THEN
    DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC
  ]
);;

let BYTE_LIST_AT_3BLOCKS = prove(
  `! pos bl bl_ptr len s.
    byte_list_at bl bl_ptr len s
    ==> LENGTH bl = val len
    ==> pos + 0x30 <= LENGTH bl
    ==> (read (memory :> bytes128 (word_add bl_ptr (word pos))) s =
         bytes_to_int128 (SUB_LIST (pos, 0x10) bl) /\
         read (memory :> bytes128 (word_add (word_add bl_ptr (word pos)) (word 0x10))) s =
         bytes_to_int128 (SUB_LIST (pos + 0x10, 0x10) bl) /\
         read (memory :> bytes128 (word_add (word_add bl_ptr (word pos)) (word 0x20))) s =
         bytes_to_int128 (SUB_LIST (pos + 0x20, 0x10) bl))`,
  REWRITE_TAC[byte_list_at] THEN
  REPEAT STRIP_TAC THENL
  [ (* Subgoal1 *)
    MAP_EVERY (fun i -> BYTE_LIST_AT_ADD_ASSUM_TAC
      (mk_binop (mk_const("+", [`:num`, `:A`])) (mk_var("pos", `:num`))
        (mk_numeral (num i))) `0x30`) (0--15) THEN
    REWRITE_TAC[WORD_ADD_ASSOC_CONSTS] THEN
    REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[BYTES128_TO_BYTES8_THM; GSYM ADD_ASSOC] THEN
    NUM_REDUCE_TAC THEN ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN
    MP_TAC (ISPECL [`bl:byte list`; `pos:num`] SUB_LIST_16) THEN
    REWRITE_TAC[GSYM ADD_ASSOC] THEN NUM_REDUCE_TAC THEN
    DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    (* Subgoal2 *)
    MAP_EVERY (fun i -> BYTE_LIST_AT_ADD_ASSUM_TAC
      (mk_binop (mk_const("+", [`:num`, `:A`])) (mk_var("pos", `:num`))
        (mk_numeral (num i))) `0x30`) (16--31) THEN
    REWRITE_TAC[WORD_ADD_ASSOC_CONSTS] THEN
    REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[BYTES128_TO_BYTES8_THM; GSYM ADD_ASSOC] THEN
    NUM_REDUCE_TAC THEN ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN
    MP_TAC (ISPECL [`bl:byte list`; `(pos+0x10):num`] SUB_LIST_16) THEN
    REWRITE_TAC[GSYM ADD_ASSOC] THEN NUM_REDUCE_TAC THEN
    DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    (* Subgoal3 *)
    MAP_EVERY (fun i -> BYTE_LIST_AT_ADD_ASSUM_TAC
      (mk_binop (mk_const("+", [`:num`, `:A`])) (mk_var("pos", `:num`))
        (mk_numeral (num i))) `0x30`) (32--47) THEN
    REWRITE_TAC[WORD_ADD_ASSOC_CONSTS] THEN
    REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[BYTES128_TO_BYTES8_THM; GSYM ADD_ASSOC] THEN
    NUM_REDUCE_TAC THEN ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN
    MP_TAC (ISPECL [`bl:byte list`; `(pos+0x20):num`] SUB_LIST_16) THEN
    REWRITE_TAC[GSYM ADD_ASSOC] THEN NUM_REDUCE_TAC THEN
    DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC
  ]
);;

let BYTE_LIST_AT_2BLOCKS = prove(
  `! pos bl bl_ptr len s.
    byte_list_at bl bl_ptr len s
    ==> LENGTH bl = val len
    ==> pos + 0x20 <= LENGTH bl
    ==> (read (memory :> bytes128 (word_add bl_ptr (word pos))) s =
         bytes_to_int128 (SUB_LIST (pos, 0x10) bl) /\
         read (memory :> bytes128 (word_add (word_add bl_ptr (word pos)) (word 0x10))) s =
         bytes_to_int128 (SUB_LIST (pos + 0x10, 0x10) bl))`,
  REWRITE_TAC[byte_list_at] THEN
  REPEAT STRIP_TAC THENL
  [ (* Subgoal1 *)
    MAP_EVERY (fun i -> BYTE_LIST_AT_ADD_ASSUM_TAC
      (mk_binop (mk_const("+", [`:num`, `:A`])) (mk_var("pos", `:num`))
        (mk_numeral (num i))) `0x20`) (0--15) THEN
    REWRITE_TAC[WORD_ADD_ASSOC_CONSTS] THEN
    REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[BYTES128_TO_BYTES8_THM; GSYM ADD_ASSOC] THEN
    NUM_REDUCE_TAC THEN ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN
    MP_TAC (ISPECL [`bl:byte list`; `pos:num`] SUB_LIST_16) THEN
    REWRITE_TAC[GSYM ADD_ASSOC] THEN NUM_REDUCE_TAC THEN
    DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    (* Subgoal2 *)
    MAP_EVERY (fun i -> BYTE_LIST_AT_ADD_ASSUM_TAC
      (mk_binop (mk_const("+", [`:num`, `:A`])) (mk_var("pos", `:num`))
        (mk_numeral (num i))) `0x20`) (16--31) THEN
    REWRITE_TAC[WORD_ADD_ASSOC_CONSTS] THEN
    REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[BYTES128_TO_BYTES8_THM; GSYM ADD_ASSOC] THEN
    NUM_REDUCE_TAC THEN ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN
    MP_TAC (ISPECL [`bl:byte list`; `(pos+0x10):num`] SUB_LIST_16) THEN
    REWRITE_TAC[GSYM ADD_ASSOC] THEN NUM_REDUCE_TAC THEN
    DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC
  ]
);;

let BYTE_LIST_AT_1BLOCKS = prove(
  `! pos bl bl_ptr len s.
    byte_list_at bl bl_ptr len s
    ==> LENGTH bl = val len
    ==> pos + 0x10 <= LENGTH bl
    ==> read (memory :> bytes128 (word_add bl_ptr (word pos))) s =
        bytes_to_int128 (SUB_LIST (pos, 0x10) bl)`,
  REWRITE_TAC[byte_list_at] THEN
  REPEAT STRIP_TAC THENL
  [ (* Subgoal1 *)
    MAP_EVERY (fun i -> BYTE_LIST_AT_ADD_ASSUM_TAC
      (mk_binop (mk_const("+", [`:num`, `:A`])) (mk_var("pos", `:num`))
        (mk_numeral (num i))) `0x10`) (0--15) THEN
    REWRITE_TAC[WORD_ADD_ASSOC_CONSTS] THEN
    REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[BYTES128_TO_BYTES8_THM; GSYM ADD_ASSOC] THEN
    NUM_REDUCE_TAC THEN ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN
    MP_TAC (ISPECL [`bl:byte list`; `pos:num`] SUB_LIST_16) THEN
    REWRITE_TAC[GSYM ADD_ASSOC] THEN NUM_REDUCE_TAC THEN
    DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC
  ]
);;

let READ_CT_LEMMA = prove(
  `!ct_ptr i (len:int64) (ct:byte list) s.
    (forall j. j < val len ==> read (memory :> bytes8 (word_add ct_ptr (word j))) s = EL j ct)
    /\ i * 0x50 + 0x50 <= val len
    /\ LENGTH ct = val len
    ==>
    read (memory :> bytes128 (word_add ct_ptr (word_mul (word 0x50) (word i)))) s =
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
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC [WORD_RULE `word_mul (word 0x50) (word i) = word (i * 80)`] THEN
  MP_TAC
    (SPECL [`(i * 80):num`; `ct:byte list`; `ct_ptr:int64`; `len:int64`; `s:armstate`]
     BYTE_LIST_AT_5BLOCKS) THEN
  REWRITE_TAC[byte_list_at] THEN ASM_SIMP_TAC[]
);;

let READ_CT_TAIL4_LEMMA = prove(
  `!ct_ptr (num_5blocks_adjusted:int64) (len:int64) (ct:byte list) s.
    (forall j. j < val len ==> read (memory :> bytes8 (word_add ct_ptr (word j))) s = EL j ct)
    /\ val num_5blocks_adjusted * 0x50 + 0x40 <= val len
    /\ LENGTH ct = val len
    ==>
    read (memory :> bytes128 (word_add
      (word_add ct_ptr (word_mul (word 0x50) num_5blocks_adjusted))
      (word 0x30))) s =
      bytes_to_int128 (SUB_LIST (val num_5blocks_adjusted * 80 + 0x30, 16) ct) /\
    read (memory :> bytes128 (word_add
      (word_add ct_ptr (word_mul (word 0x50) num_5blocks_adjusted))
      (word 0x20))) s =
      bytes_to_int128 (SUB_LIST (val num_5blocks_adjusted * 80 + 0x20, 16) ct) /\
    read (memory :> bytes128 (word_add
      (word_add ct_ptr (word_mul (word 0x50) num_5blocks_adjusted))
      (word 0x10))) s =
      bytes_to_int128 (SUB_LIST (val num_5blocks_adjusted * 80 + 0x10, 16) ct) /\
    read (memory :> bytes128
      (word_add ct_ptr (word_mul (word 0x50) num_5blocks_adjusted))) s =
      bytes_to_int128 (SUB_LIST (val num_5blocks_adjusted * 80, 16) ct)
    `,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC [WORD_RULE `(word_mul (word 0x50) (num_5blocks_adjusted:int64)) = word (val num_5blocks_adjusted * 80)`] THEN
  MP_TAC
    (SPECL [`(val (num_5blocks_adjusted:int64) * 80):num`; `ct:byte list`; `ct_ptr:int64`; `len:int64`; `s:armstate`]
     BYTE_LIST_AT_4BLOCKS) THEN
  REWRITE_TAC[byte_list_at] THEN ASM_SIMP_TAC[]
);;

let READ_CT_TAIL3_LEMMA = prove(
  `!ct_ptr (num_5blocks_adjusted:int64) (len:int64) (ct:byte list) s.
    (forall j. j < val len ==> read (memory :> bytes8 (word_add ct_ptr (word j))) s = EL j ct)
    /\ val num_5blocks_adjusted * 0x50 + 0x30 <= val len
    /\ LENGTH ct = val len
    ==>
    read (memory :> bytes128 (word_add
      (word_add ct_ptr (word_mul (word 0x50) num_5blocks_adjusted))
      (word 0x20))) s =
      bytes_to_int128 (SUB_LIST (val num_5blocks_adjusted * 80 + 0x20, 16) ct) /\
    read (memory :> bytes128 (word_add
      (word_add ct_ptr (word_mul (word 0x50) num_5blocks_adjusted))
      (word 0x10))) s =
      bytes_to_int128 (SUB_LIST (val num_5blocks_adjusted * 80 + 0x10, 16) ct) /\
    read (memory :> bytes128
      (word_add ct_ptr (word_mul (word 0x50) num_5blocks_adjusted))) s =
      bytes_to_int128 (SUB_LIST (val num_5blocks_adjusted * 80, 16) ct)
    `,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC [WORD_RULE `(word_mul (word 0x50) (num_5blocks_adjusted:int64)) = word (val num_5blocks_adjusted * 80)`] THEN
  MP_TAC
    (SPECL [`(val (num_5blocks_adjusted:int64) * 80):num`; `ct:byte list`; `ct_ptr:int64`; `len:int64`; `s:armstate`]
     BYTE_LIST_AT_3BLOCKS) THEN
  REWRITE_TAC[byte_list_at] THEN ASM_SIMP_TAC[]
);;

let READ_CT_TAIL2_LEMMA = prove(
  `!ct_ptr (num_5blocks_adjusted:int64) (len:int64) (ct:byte list) s.
    (forall j. j < val len ==> read (memory :> bytes8 (word_add ct_ptr (word j))) s = EL j ct)
    /\ val num_5blocks_adjusted * 0x50 + 0x20 <= val len
    /\ LENGTH ct = val len
    ==>
    read (memory :> bytes128 (word_add
      (word_add ct_ptr (word_mul (word 0x50) num_5blocks_adjusted))
      (word 0x10))) s =
      bytes_to_int128 (SUB_LIST (val num_5blocks_adjusted * 80 + 0x10, 16) ct) /\
    read (memory :> bytes128
      (word_add ct_ptr (word_mul (word 0x50) num_5blocks_adjusted))) s =
      bytes_to_int128 (SUB_LIST (val num_5blocks_adjusted * 80, 16) ct)
    `,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC [WORD_RULE `(word_mul (word 0x50) (num_5blocks_adjusted:int64)) = word (val num_5blocks_adjusted * 80)`] THEN
  MP_TAC
    (SPECL [`(val (num_5blocks_adjusted:int64) * 80):num`; `ct:byte list`; `ct_ptr:int64`; `len:int64`; `s:armstate`]
     BYTE_LIST_AT_2BLOCKS) THEN
  REWRITE_TAC[byte_list_at] THEN ASM_SIMP_TAC[]
);;

let READ_CT_TAIL1_LEMMA = prove(
  `!ct_ptr (num_5blocks_adjusted:int64) (len:int64) (ct:byte list) s.
    (forall j. j < val len ==> read (memory :> bytes8 (word_add ct_ptr (word j))) s = EL j ct)
    /\ val num_5blocks_adjusted * 0x50 + 0x10 <= val len
    /\ LENGTH ct = val len
    ==>
    read (memory :> bytes128
      (word_add ct_ptr (word_mul (word 0x50) num_5blocks_adjusted))) s =
      bytes_to_int128 (SUB_LIST (val num_5blocks_adjusted * 80, 16) ct)
    `,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC [WORD_RULE `(word_mul (word 0x50) (num_5blocks_adjusted:int64)) = word (val num_5blocks_adjusted * 80)`] THEN
  MP_TAC
    (SPECL [`(val (num_5blocks_adjusted:int64) * 80):num`; `ct:byte list`; `ct_ptr:int64`; `len:int64`; `s:armstate`]
     BYTE_LIST_AT_1BLOCKS) THEN
  REWRITE_TAC[byte_list_at] THEN ASM_SIMP_TAC[]
);;

let UDIV_OPT_THM = prove(`!n:num. n < 0x2 EXP 0x40
  ==> (word (val ((word ((n * 0xcccccccccccccccd) DIV 0x2 EXP 0x40)):int64) DIV 0x2 EXP 0x6)):int64 = word (n DIV 0x50)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN
  SUBGOAL_THEN `!p n:num. ~(p = 0) /\ n < p * p ==> n DIV p MOD p = n DIV p`
    (MP_TAC o SPECL [`0x2 EXP 0x40`; `n * 0xcccccccccccccccd`]) THENL
  [ REPEAT STRIP_TAC THEN
    REWRITE_TAC[DIV_MOD] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC MOD_LT THEN
    ASM_ARITH_TAC; ALL_TAC] THEN
  ANTS_TAC THENL [ASM_ARITH_TAC;ALL_TAC] THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  AP_TERM_TAC THEN ASM_ARITH_TAC);;

let NUM_BLOCKS_LO_BOUND_THM = prove(
  `!(len:int64) num_blocks. word_and len (word 0xfffffffffffffff0) = num_blocks
   ==> ~(val len < 0x60)
   ==> ~(val num_blocks < 0x60)`,
   BITBLAST_TAC);;

let NUM_BLOCKS_HI_BOUND_THM = prove(
  `!(len:int64) num_blocks. word_and len (word 0xfffffffffffffff0) = num_blocks
   ==> val len <= 2 EXP 24
   ==> val num_blocks <= 2 EXP 24`,
   BITBLAST_TAC);;

let TAIL_LEN_BOUND_THM = prove(
  `!(len:int64) tail_len. word_and len (word 0xf) = tail_len
   ==> val tail_len < 0x10`,
   BITBLAST_TAC);;

let NUM_BLOCKS_ADJUSTED_LO_BOUND_THM = prove(
  `!(num_blocks:int64) (tail_len:int64) num_blocks_adjusted.
    (if val tail_len = 0x0 then num_blocks else word_sub num_blocks (word 0x10)) = num_blocks_adjusted
    ==> ~(val num_blocks < 0x60)
    ==> ~(val num_blocks_adjusted < 0x50)`,
  BITBLAST_TAC
);;

let NUM_BLOCKS_ADJUSTED_HI_BOUND_THM = prove(
  `!(num_blocks:int64) (tail_len:int64) num_blocks_adjusted.
    (if val tail_len = 0x0 then num_blocks else word_sub num_blocks (word 0x10)) = num_blocks_adjusted
    ==> val num_blocks <= 2 EXP 24
    ==> ~(val num_blocks < 0x60)
    ==> val num_blocks_adjusted <= 2 EXP 24`,
  BITBLAST_TAC
);;

let NUM_5BLOCKS_ADJUSTED_LO_BOUND_THM = prove(
  `!(num_blocks_adjusted:int64) (num_5blocks_adjusted:int64).
    val num_blocks_adjusted <= 0x2 EXP 0x18
    ==> ~(val num_blocks_adjusted < 0x50)
    ==> word (val num_blocks_adjusted DIV 0x50) = num_5blocks_adjusted
    ==> 0x0 < val num_5blocks_adjusted`,
  REPEAT STRIP_TAC THEN
  EXPAND_TAC "num_5blocks_adjusted" THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN
  UNDISCH_TAC `~(val (num_blocks_adjusted:int64) < 0x50)` THEN
  ABBREV_TAC `n = val (num_blocks_adjusted:int64)` THEN
  SUBGOAL_THEN `n DIV 80 < 2 EXP 64` ASSUME_TAC THENL
  [ ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[MOD_LT] THEN
  ARITH_TAC
);;

let NUM_BLOCKS_LT_LEN_THM = prove(
  `!(len:int64). val (word_and len (word 0xfffffffffffffff0)) <= val len`,
  BITBLAST_TAC
);;

let NUM_BLOCKS_ADJUSTED_LT_LEN_THM = prove(
  `!(len:int64) num_blocks.
    word_and len (word 0xfffffffffffffff0) = num_blocks
    ==> ~(val num_blocks < 0x60)
    ==> val (word_sub num_blocks (word 0x10)) <= val len`,
    BITBLAST_TAC
);;

let NUM_OF_BYTELIST_APPEND = prove
 (`!l1 l2. num_of_bytelist (APPEND l1 l2) =
           num_of_bytelist l1 + 2 EXP (8 * LENGTH l1) * num_of_bytelist l2`,
   LIST_INDUCT_TAC THENL
   [ REWRITE_TAC[APPEND; LENGTH; num_of_bytelist; MULT_CLAUSES; EXP; ADD_CLAUSES];
     REWRITE_TAC[APPEND; LENGTH; num_of_bytelist] THEN
     ASM_REWRITE_TAC[] THEN
     REWRITE_TAC[MULT_SUC; EXP_ADD] THEN
     REWRITE_TAC[MULT_ASSOC; LEFT_ADD_DISTRIB] THEN
     ARITH_TAC]);;

let NUM_OF_BYTELIST_OF_SUB_LIST = prove(
  `!sz len (x:byte list).
   sz <= LENGTH x ==>
   num_of_bytelist (SUB_LIST (0, sz + len) x) =
   num_of_bytelist (SUB_LIST (0, sz) x) +
   2 EXP (8 * sz) * num_of_bytelist (SUB_LIST (sz, len) x)`,
  REPEAT STRIP_TAC THEN
  SUBST1_TAC(ISPECL [`x:byte list`; `sz:num`; `len:num`; `0:num`] SUB_LIST_SPLIT) THEN
  REWRITE_TAC[NUM_OF_BYTELIST_APPEND] THEN
  ASM_SIMP_TAC[LENGTH_SUB_LIST; SUB_0; MIN; ARITH_RULE `0 + sz = sz`]
);;

let MEMORY_READ_SUBSET_LEMMA = prove
 (`!len (bl:byte list) s.
   (forall i.
          i < SUC len
          ==> read (memory :> bytes8 (word_add pt_ptr (word i))) s = EL i bl) ==>
   (forall i.
           i < len
           ==> read (memory :> bytes8 (word_add pt_ptr (word i))) s = EL i bl) /\
   read (memory :> bytes (word_add pt_ptr (word len),1)) s =
    val(read (memory :> bytes8 (word_add pt_ptr (word len))) s)
   `,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  CONJ_TAC THENL
  [ GEN_TAC THEN DISCH_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[LT_SUC_LE] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[bytes8; READ_COMPONENT_COMPOSE; asword; through; read] THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_8] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  IMP_REWRITE_TAC[MOD_LT] THEN
  MP_TAC (ISPECL [`(word_add (pt_ptr:int64) (word len)):int64`; `1:num`; `(read memory s):int64->byte`] READ_BYTES_BOUND) THEN
  CONV_TAC NUM_REDUCE_CONV
);;

let BYTE_LIST_AT_SPLIT = prove(
  `!len (bl:byte list) s.
  SUC len <= LENGTH bl ==>
   ((forall i.
     i < SUC len
     ==> read (memory :> bytes8 (word_add pt_ptr (word i))) s = EL i bl) <=>
   ((forall i.
     i < len
     ==> read (memory :> bytes8 (word_add pt_ptr (word i))) s = EL i bl) /\
    read (memory :> bytes8 (word_add pt_ptr (word len))) s = EL len bl))`,
    REPEAT STRIP_TAC THEN
    EQ_TAC THENL
    [ STRIP_TAC THEN
      CONJ_TAC THENL
      [ ASM_SIMP_TAC[ARITH_RULE `i < len ==> i < SUC len`];
        ASM_SIMP_TAC[ARITH_RULE `len < SUC len`]];
      ALL_TAC ] THEN
    REPEAT STRIP_TAC THEN
    ASM_CASES_TAC `i < len` THENL
    [ FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_SIMP_TAC[];
      SUBGOAL_THEN `i = len:num` SUBST1_TAC THENL
      [ASM_ARITH_TAC; ASM_REWRITE_TAC[]]
    ]
);;


let MEMORY_READ_BYTES_SUBSET_LEMMA = prove(
  `!len (bl:byte list) s.
   SUC len <= LENGTH bl ==>
   read (memory :> bytes (pt_ptr,SUC len)) s =
      num_of_bytelist (SUB_LIST (0x0,SUC len) bl) ==>
   read (memory :> bytes (pt_ptr,len)) s =
      num_of_bytelist (SUB_LIST (0x0,len) bl) /\
   read (memory :> bytes8 (word_add pt_ptr (word len))) s = EL len bl`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `SUC len = len + 1` SUBST_ALL_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN
  SUBGOAL_THEN `len <= LENGTH (bl:byte list)` ASSUME_TAC THENL [ ASM_ARITH_TAC; ALL_TAC] THEN
  (* Use READ_BYTES_COMBINE to decompose the memory read *)
  MP_TAC(ISPECL [`pt_ptr:int64`; `len:num`; `1:num`; `(read memory s):int64->byte`] READ_BYTES_COMBINE) THEN
  DISCH_TAC THEN
  (* Use SUB_LIST_SPLIT to decompose the byte list *)
  MP_TAC(ISPECL [`bl:byte list`; `len:num`; `1:num`; `0:num`] SUB_LIST_SPLIT) THEN
  REWRITE_TAC[ADD_CLAUSES] THEN DISCH_TAC THEN
  (* Decompose num_of_bytelist *)
  SUBGOAL_THEN
   `num_of_bytelist (SUB_LIST (0,len + 1) (bl:byte list)) =
    num_of_bytelist (SUB_LIST (0,len) bl) +
    2 EXP (8 * len) * num_of_bytelist (SUB_LIST (len,1) bl)`
  ASSUME_TAC THENL
   [ ASM_REWRITE_TAC[] THEN
     REWRITE_TAC[NUM_OF_BYTELIST_APPEND] THEN
     AP_TERM_TAC THEN AP_THM_TAC THEN REPEAT_N 3 AP_TERM_TAC THEN
     IMP_REWRITE_TAC[LENGTH_SUB_LIST; MIN; SUB_0] THEN
     ASM_SIMP_TAC[]
     ; ALL_TAC] THEN
  (* Rewrite in goal *)
  ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  CONJ_TAC THENL
  [ (* First part: read (memory :> bytes (pt_ptr,len)) s = num_of_bytelist (SUB_LIST (0,len) bl) *)
    FIRST_X_ASSUM(MP_TAC o AP_TERM `\x. x MOD 2 EXP (8 * len)`) THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MOD_MULT_ADD; MOD_LT] THEN
    REWRITE_TAC[READ_BYTES_MOD; MIN] THEN
    SIMP_TAC[ARITH_RULE `len <= len`] THEN
    DISCH_TAC THEN
    IMP_REWRITE_TAC[MOD_LT] THEN
    MP_TAC (SPEC `(SUB_LIST (0,len) bl:byte list)` NUM_OF_BYTELIST_BOUND) THEN
    IMP_REWRITE_TAC[LENGTH_SUB_LIST; SUB_0; MIN] THEN
    SUBGOAL_THEN `256 EXP len = 2 EXP (8 * len)` SUBST1_TAC THENL
    [ REWRITE_TAC[ARITH_RULE `256 = 2 EXP 8`; EXP_EXP]; ALL_TAC] THEN
    SIMP_TAC[];
    ALL_TAC
  ] THEN
  (* Second part: read (memory :> bytes8 (word_add pt_ptr (word len))) s = EL len bl *)
  FIRST_X_ASSUM(MP_TAC o AP_TERM `\x. x DIV 2 EXP (8 * len)`) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(0x2 EXP (0x8 * len) = 0x0)` ASSUME_TAC THENL
  [ REWRITE_TAC[EXP_EQ_0; ARITH_EQ]; ALL_TAC] THEN
  IMP_REWRITE_TAC[DIV_MULT_ADD] THEN
  SUBGOAL_THEN `read (bytes (pt_ptr,len)) (read memory s) < 0x2 EXP (0x8 * len)` ASSUME_TAC THENL
  [ REWRITE_TAC[READ_BYTES_BOUND]; ALL_TAC] THEN
  SUBGOAL_THEN `num_of_bytelist (SUB_LIST (0x0,len) bl) < 0x2 EXP (0x8 * len)` ASSUME_TAC THENL
  [ MP_TAC (SPEC `(SUB_LIST (0,len) bl:byte list)` NUM_OF_BYTELIST_BOUND) THEN
    IMP_REWRITE_TAC[LENGTH_SUB_LIST; SUB_0; MIN] THEN
    SUBGOAL_THEN `256 EXP len = 2 EXP (8 * len)` SUBST1_TAC THENL
    [ REWRITE_TAC[ARITH_RULE `256 = 2 EXP 8`; EXP_EXP]; ALL_TAC] THEN SIMP_TAC[]; ALL_TAC] THEN
  IMP_REWRITE_TAC[DIV_LT; ADD] THEN
  (* Some rewrites to close the goal *)
  REWRITE_TAC[bytes8; READ_COMPONENT_COMPOSE; asword; through; read] THEN
  SUBGOAL_THEN `len < LENGTH (bl:byte list)` ASSUME_TAC THENL [ ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[SUB_LIST_1] THEN
  REWRITE_TAC[num_of_bytelist; MULT_CLAUSES; ADD_CLAUSES; WORD_VAL]
);;

let BYTE_LIST_TO_NUM_THM = prove(
  `!len (bl:byte list) s.
    len <= LENGTH bl ==>
    ((forall i. i < len
      ==> read (memory :> bytes8 (word_add pt_ptr (word i))) s = EL i bl) <=>
    (read (memory :> bytes (pt_ptr, len)) s = num_of_bytelist (SUB_LIST (0, len) bl)))`,
  REPEAT GEN_TAC THEN
  SPEC_TAC (`len:num`, `len:num`) THEN
  (* Base case: len = 0 *)
  INDUCT_TAC THENL
  [ STRIP_TAC THEN
    REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_TRIVIAL;
      CONJUNCT1 SUB_LIST; CONJUNCT1 num_of_bytelist] THEN
    GEN_TAC THEN MESON_TAC[ARITH_RULE `~(i < 0)`];
    ALL_TAC] THEN

  (* Inductive step: left to right *)
  STRIP_TAC THEN
  EQ_TAC THENL
  [ MP_TAC (ARITH_RULE `SUC len <= LENGTH (bl:byte list) ==> len <= LENGTH bl`) THEN
    ASM_SIMP_TAC[] THEN REPEAT DISCH_TAC THEN
    MP_TAC (SPECL [`len:num`; `bl:byte list`; `s:armstate`] MEMORY_READ_SUBSET_LEMMA) THEN
    ASM_SIMP_TAC[] THEN
    DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
    REWRITE_TAC[READ_COMPONENT_COMPOSE; ADD1] THEN
    ONCE_REWRITE_TAC[READ_BYTES_COMBINE] THEN
    REWRITE_TAC[SUB_LIST_SPLIT; NUM_OF_BYTELIST_APPEND; CONJUNCT1 ADD] THEN
    IMP_REWRITE_TAC[ARITH_RULE `a = c ==> (a + b = c + d) = (b = d)`] THEN
    CONJ_TAC THENL [
      REWRITE_TAC[LENGTH_SUB_LIST; MIN; SUB_0] THEN
      ASM_SIMP_TAC[] THEN
      AP_TERM_TAC THEN
      REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN
      FIRST_X_ASSUM (fun th -> MP_TAC (SPEC `len:num` th)) THEN
      REWRITE_TAC[ARITH_RULE `len < SUC len`] THEN
      SUBGOAL_THEN `len < LENGTH (bl:byte list)` ASSUME_TAC THENL
      [ ASM_ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[SUB_LIST_1; num_of_bytelist] THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC[ADD_0] THEN
      STRIP_TAC THEN AP_TERM_TAC THEN ASM_SIMP_TAC[]
      ; ALL_TAC] THEN
    REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN
    ASM_SIMP_TAC[]
    ; ALL_TAC] THEN

  (* Inductive step: right to left *)
  MP_TAC (ARITH_RULE `SUC len <= LENGTH (bl:byte list) ==> len <= LENGTH bl`) THEN
  ASM_SIMP_TAC[] THEN REPEAT DISCH_TAC THEN
  MP_TAC (SPECL [`len:num`; `bl:byte list`; `s:armstate`] MEMORY_READ_BYTES_SUBSET_LEMMA) THEN
  ASM_SIMP_TAC[] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  IMP_REWRITE_TAC[BYTE_LIST_AT_SPLIT] THEN
  CONJ_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[]
);;

let MEMORY_BYTES_BOUND = prove
  (`read (memory :> bytes (x,16)) s < 2 EXP dimindex (:128)`,
  REWRITE_TAC[READ_COMPONENT_COMPOSE; DIMINDEX_128] THEN
  SUBST1_TAC(ARITH_RULE `128 = 8 * 16`) THEN REWRITE_TAC[READ_BYTES_BOUND]
  );;

(* Copied from bignum_copy_row_from_table_8n.ml *)
let READ_MEMORY_BYTES_BYTES128 = prove(`!z s.
    read (memory :> bytes (z,16)) s = val (read (memory :> bytes128 z) s)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[el 1 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT)] THEN
  REWRITE_TAC[VAL_WORD_JOIN;DIMINDEX_64;DIMINDEX_128] THEN
  IMP_REWRITE_TAC[MOD_LT] THEN
  REWRITE_TAC[ARITH_RULE`2 EXP 128 = 2 EXP 64 * 2 EXP 64`] THEN
  IMP_REWRITE_TAC[LT_MULT_ADD_MULT] THEN
  REWRITE_TAC[VAL_BOUND_64;ARITH_RULE`0<2 EXP 64`;LE_REFL] THEN
  REWRITE_TAC[ARITH_RULE`16 = 8*(1+1)`;GSYM BIGNUM_FROM_MEMORY_BYTES;BIGNUM_FROM_MEMORY_STEP;BIGNUM_FROM_MEMORY_SING] THEN
  REWRITE_TAC[ARITH_RULE`8*1=8`;ARITH_RULE`64*1=64`] THEN ARITH_TAC);;

let READ_MEMORY_BYTES128_BYTES = prove(`!z s.
    read (memory :> bytes128 z) s = word (read (memory :> bytes (z,16)) s)`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
  IMP_REWRITE_TAC [VAL_WORD_EQ] THEN
  CONJ_TAC THENL [REWRITE_TAC [READ_MEMORY_BYTES_BYTES128]; ALL_TAC] THEN
  REWRITE_TAC [MEMORY_BYTES_BOUND]
  );;

let WORD_JOIN_BOUND_TAC x y =
  REWRITE_TAC[VAL_WORD_JOIN; DIMINDEX_CLAUSES] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  IMP_REWRITE_TAC[MOD_LT] THEN
  CONJ_TAC THENL[ REWRITE_TAC[ADD_SYM]; ALL_TAC ] THEN
  MP_TAC (ISPECL [x] VAL_BOUND) THEN
  MP_TAC (ISPECL [y] VAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_CLAUSES] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ARITH_TAC;;

let WORD_JOIN_16_8_ASSOC = WORD_BLAST
  `!(x0:byte) (x1:byte) (x2:byte) (x3:byte)
    (x4:byte) (x5:byte) (x6:byte) (x7:byte)
    (x8:byte) (x9:byte) (x10:byte) (x11:byte)
    (x12:byte) (x13:byte) (x14:byte) (x15:byte).
    (word_join
      (word_join
        (word_join (word_join x15 x14 : int16) (word_join x13 x12 : int16) : int32)
        (word_join (word_join x11 x10 : int16) (word_join x9 x8 : int16) : int32) : int64)
      (word_join
        (word_join (word_join x7 x6 : int16) (word_join x5 x4 : int16) : int32)
        (word_join (word_join x3 x2 : int16) (word_join x1 x0 : int16) : int32) : int64)) =
    (word_join
      (word_join
        (word_join
          (word_join
            (word_join
              (word_join
                (word_join
                  (word_join
                    (word_join
                      (word_join
                        (word_join
                          (word_join
                            (word_join
                              (word_join
                                (word_join x15 x14:16 word)
                              x13:24 word)
                            x12:32 word)
                          x11:40 word)
                        x10:48 word)
                      x9:56 word)
                    x8:64 word)
                  x7:72 word)
                x6:80 word)
              x5:88 word)
            x4:96 word)
          x3:104 word)
        x2:112 word)
      x1:120 word)
    x0:128 word)`;;

let VAL_OF_BYTES_TO_INT128_EQ_NUM_OF_BYTELIST = prove(
  `!x:byte list. LENGTH x = 16 ==> val (bytes_to_int128 x) = num_of_bytelist x`,
  REPEAT STRIP_TAC THEN
  (* conversion for breaking down a list *)
  MP_TAC ((GEN_REWRITE_CONV I [LENGTH_EQ_LIST_OF_SEQ] THENC
   RAND_CONV LIST_OF_SEQ_CONV) `LENGTH (x:byte list) = 16`) THEN
  ASM_SIMP_TAC[] THEN
  DISCH_THEN (fun th -> ONCE_REWRITE_TAC[th]) THEN
  REWRITE_TAC[bytes_to_int128] THEN
  REWRITE_TAC EL_16_8_CLAUSES THEN
  REPEAT_N 16 (ONCE_REWRITE_TAC[num_of_bytelist]) THEN
  REWRITE_TAC[CONJUNCT1 num_of_bytelist] THEN
  MAP_EVERY ABBREV_TAC
    [`x0 = EL 0 x:byte`; `x1 = EL 1 x:byte`; `x2 = EL 2 x:byte`; `x3 = EL 3 x:byte`;
     `x4 = EL 4 x:byte`; `x5 = EL 5 x:byte`; `x6 = EL 6 x:byte`; `x7 = EL 7 x:byte`;
     `x8 = EL 8 x:byte`; `x9 = EL 9 x:byte`; `x10 = EL 10 x:byte`; `x11 = EL 11 x:byte`;
     `x12 = EL 12 x:byte`; `x13 = EL 13 x:byte`; `x14 = EL 14 x:byte`; `x15 = EL 15 x:byte`] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[ADD_0; WORD_JOIN_16_8_ASSOC] THEN
  (* reduce RHS to LHS *)
  SUBGOAL_THEN `val (x14:byte) + 0x100 * val (x15:byte) = val ((word_join x15 x14):int16)` SUBST1_TAC THENL
  [ WORD_JOIN_BOUND_TAC `x15:byte` `x14:byte`; ALL_TAC] THEN ABBREV_TAC `y14:int16 = word_join (x15:byte) (x14:byte)` THEN
  SUBGOAL_THEN `val (x13:byte) + 0x100 * val (y14:16 word) = val ((word_join y14 x13):24 word)` SUBST1_TAC THENL
  [ WORD_JOIN_BOUND_TAC `y14:16 word` `x13:byte`; ALL_TAC] THEN ABBREV_TAC `y13:24 word = word_join (y14:16 word) (x13:byte)` THEN
  SUBGOAL_THEN `val (x12:byte) + 0x100 * val (y13:24 word) = val ((word_join y13 x12):32 word)` SUBST1_TAC THENL
  [ WORD_JOIN_BOUND_TAC `y13:24 word` `x12:byte`; ALL_TAC] THEN ABBREV_TAC `y12:32 word = word_join (y13:24 word) (x12:byte)` THEN
  SUBGOAL_THEN `val (x11:byte) + 0x100 * val (y12:32 word) = val ((word_join y12 x11):40 word)` SUBST1_TAC THENL
  [ WORD_JOIN_BOUND_TAC `y12:32 word` `x11:byte`; ALL_TAC] THEN ABBREV_TAC `y11:40 word = word_join (y12:32 word) (x11:byte)` THEN
  SUBGOAL_THEN `val (x10:byte) + 0x100 * val (y11:40 word) = val ((word_join y11 x10):48 word)` SUBST1_TAC THENL
  [ WORD_JOIN_BOUND_TAC `y11:40 word` `x10:byte`; ALL_TAC] THEN ABBREV_TAC `y10:48 word = word_join (y11:40 word) (x10:byte)` THEN
  SUBGOAL_THEN `val (x9:byte) + 0x100 * val (y10:48 word) = val ((word_join y10 x9):56 word)` SUBST1_TAC THENL
  [ WORD_JOIN_BOUND_TAC `y10:48 word` `x9:byte`; ALL_TAC] THEN ABBREV_TAC `y9:56 word = word_join (y10:48 word) (x9:byte)` THEN
  SUBGOAL_THEN `val (x8:byte) + 0x100 * val (y9:56 word) = val ((word_join y9 x8):64 word)` SUBST1_TAC THENL
  [ WORD_JOIN_BOUND_TAC `y9:56 word` `x8:byte`; ALL_TAC] THEN ABBREV_TAC `y8:64 word = word_join (y9:56 word) (x8:byte)` THEN
  SUBGOAL_THEN `val (x7:byte) + 0x100 * val (y8:64 word) = val ((word_join y8 x7):72 word)` SUBST1_TAC THENL
  [ WORD_JOIN_BOUND_TAC `y8:64 word` `x7:byte`; ALL_TAC] THEN ABBREV_TAC `y7:72 word = word_join (y8:64 word) (x7:byte)` THEN
  SUBGOAL_THEN `val (x6:byte) + 0x100 * val (y7:72 word) = val ((word_join y7 x6):80 word)` SUBST1_TAC THENL
  [ WORD_JOIN_BOUND_TAC `y7:72 word` `x6:byte`; ALL_TAC] THEN ABBREV_TAC `y6:80 word = word_join (y7:72 word) (x6:byte)` THEN
  SUBGOAL_THEN `val (x5:byte) + 0x100 * val (y6:80 word) = val ((word_join y6 x5):88 word)` SUBST1_TAC THENL
  [ WORD_JOIN_BOUND_TAC `y6:80 word` `x5:byte`; ALL_TAC] THEN ABBREV_TAC `y5:88 word = word_join (y6:80 word) (x5:byte)` THEN
  SUBGOAL_THEN `val (x4:byte) + 0x100 * val (y5:88 word) = val ((word_join y5 x4):96 word)` SUBST1_TAC THENL
  [ WORD_JOIN_BOUND_TAC `y5:88 word` `x4:byte`; ALL_TAC] THEN ABBREV_TAC `y4:96 word = word_join (y5:88 word) (x4:byte)` THEN
  SUBGOAL_THEN `val (x3:byte) + 0x100 * val (y4:96 word) = val ((word_join y4 x3):104 word)` SUBST1_TAC THENL
  [ WORD_JOIN_BOUND_TAC `y4:96 word` `x3:byte`; ALL_TAC] THEN ABBREV_TAC `y3:104 word = word_join (y4:96 word) (x3:byte)` THEN
  SUBGOAL_THEN `val (x2:byte) + 0x100 * val (y3:104 word) = val ((word_join y3 x2):112 word)` SUBST1_TAC THENL
  [ WORD_JOIN_BOUND_TAC `y3:104 word` `x2:byte`; ALL_TAC] THEN ABBREV_TAC `y2:112 word = word_join (y3:104 word) (x2:byte)` THEN
  SUBGOAL_THEN `val (x1:byte) + 0x100 * val (y2:112 word) = val ((word_join y2 x1):120 word)` SUBST1_TAC THENL
  [ WORD_JOIN_BOUND_TAC `y2:112 word` `x1:byte`; ALL_TAC] THEN ABBREV_TAC `y1:120 word = word_join (y2:112 word) (x1:byte)` THEN
  SUBGOAL_THEN `val (x0:byte) + 0x100 * val (y1:120 word) = val ((word_join y1 x0):128 word)` SUBST1_TAC THENL
  [ WORD_JOIN_BOUND_TAC `y1:120 word` `x0:byte`; ALL_TAC] THEN ABBREV_TAC `y0:128 word = word_join (y1:120 word) (x0:byte)` THEN
  REFL_TAC
);;

let READ_BYTES_AND_BYTE128_SPLIT = prove(
  `!(pt_ptr:int64) (sz:num) (x:byte list) (s:armstate).
    sz + 16 <= LENGTH x ==>
    read (memory :> bytes128 (word_add pt_ptr (word sz))) s = bytes_to_int128 (SUB_LIST (sz, 0x10) x)
    /\ read (memory :> bytes (pt_ptr, sz)) s = num_of_bytelist (SUB_LIST (0, sz) x)
    ==> read (memory :> bytes (pt_ptr,sz + 0x10)) s = num_of_bytelist (SUB_LIST (0, sz + 0x10) x)`,
  REWRITE_TAC[READ_MEMORY_BYTES128_BYTES] THEN
  REPEAT STRIP_TAC THEN

  SUBGOAL_THEN `sz <= LENGTH (x:byte list)` ASSUME_TAC THENL
  [ UNDISCH_TAC `sz + 16 <= LENGTH (x:byte list)` THEN ARITH_TAC; ALL_TAC ] THEN

  SUBGOAL_THEN `16 <= LENGTH (x:byte list) - sz` ASSUME_TAC THENL
  [ UNDISCH_TAC `sz + 16 <= LENGTH (x:byte list)` THEN ARITH_TAC; ALL_TAC ] THEN

  SUBGOAL_THEN `read (memory :> bytes (pt_ptr, sz + 16)) s =
                read (memory :> bytes (pt_ptr, sz)) s +
                2 EXP (8 * sz) * (read (memory :> bytes (word_add pt_ptr (word sz), 16)) s)` SUBST1_TAC THENL
  [ REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN
    REWRITE_TAC[READ_BYTES_COMBINE]; ALL_TAC] THEN

  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `read (memory :> bytes (word_add pt_ptr (word sz),0x10)) s =
      val (bytes_to_int128 (SUB_LIST (sz,0x10) x))` SUBST1_TAC THENL
  [ UNDISCH_THEN
     `word (read (memory :> bytes (word_add (pt_ptr:int64) (word sz),0x10)) s) =
      bytes_to_int128 (SUB_LIST (sz,0x10) x)`
      (fun th -> MP_TAC (AP_TERM `val:int128->num` th)) THEN
    IMP_REWRITE_TAC[VAL_WORD] THEN
    SUBGOAL_THEN `read (memory :> bytes (word_add pt_ptr (word sz),0x10)) s < 2 EXP dimindex (:128)` ASSUME_TAC THENL
    [ SIMP_TAC[MEMORY_BYTES_BOUND] ; ALL_TAC] THEN
    SUBST_ALL_TAC DIMINDEX_128 THEN
    ASM_SIMP_TAC[MOD_LT]; ALL_TAC] THEN

  IMP_REWRITE_TAC[NUM_OF_BYTELIST_OF_SUB_LIST] THEN
  IMP_REWRITE_TAC[VAL_OF_BYTES_TO_INT128_EQ_NUM_OF_BYTELIST] THEN
  REWRITE_TAC[LENGTH_SUB_LIST; MIN] THEN ASM_SIMP_TAC[]
  );;


let SUB_LIST_APPEND_RIGHT_LEMMA = prove(
  `!(x:A list) y n m. LENGTH x = n ==> SUB_LIST (n,m) (APPEND x y) = SUB_LIST (0,m) y`,
  LIST_INDUCT_TAC THENL
  [ REPEAT GEN_TAC THEN
    SIMP_TAC[CONJUNCT1 LENGTH; APPEND; SUB_LIST_CLAUSES];

    ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
    INDUCT_TAC THENL[
      SIMP_TAC[LENGTH_EQ_NIL] THEN REWRITE_TAC[APPEND];
      ASM_SIMP_TAC[APPEND; LENGTH; SUB_LIST_CLAUSES; SUC_INJ]]]);;

let SUB_LIST_LENGTH_IMPLIES = prove(
  `!(l:A list) n. LENGTH l = n ==> SUB_LIST(0,n) l = l`,
   REPEAT STRIP_TAC THEN
   UNDISCH_THEN `LENGTH (l:A list) = n` (fun th -> REWRITE_TAC[GSYM th]) THEN
   REWRITE_TAC[SUB_LIST_LENGTH]
);;

let LENGTH_OF_INT128_TO_BYTES = prove(
  `!x. LENGTH(int128_to_bytes x) = 16`,
  STRIP_TAC THEN
  REWRITE_TAC[int128_to_bytes] THEN
  REWRITE_TAC[LENGTH] THEN
  CONV_TAC NUM_REDUCE_CONV
);;

let DIVISION_BY_80_LEMMA = prove(
  `!(a:num) b. a DIV 0x50 = b ==>
    ~(a - b * 0x50 - 0x10 = 0x0) ==>
    ~(a - b * 0x50 - 0x20 = 0x0) ==>
    ~(a - b * 0x50 - 0x30 = 0x0) ==>
    ~(a - b * 0x50 - 0x40 = 0x0) ==>
    b * 0x50 = a`,
  CHEAT_TAC
);;


(* ********************************************************** *)
(* Properties that we prove about the specification functions *)

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

let BYTES_TO_INT128_OF_INT128_TO_BYTES = prove(
  `!x. bytes_to_int128 (int128_to_bytes x) = x`,
  GEN_TAC THEN
  REWRITE_TAC[int128_to_bytes; bytes_to_int128] THEN
  REWRITE_TAC EL_16_8_CLAUSES THEN
  BITBLAST_TAC
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

let tail_cases_in_byte = new_definition
`tail_cases_in_byte (i:int64) (len:int64) : num =
  if val i * 0x50 + 0x40 = val len then 0x50 * val i + 0x40
  else
    if val i * 0x50 + 0x30 = val len then 0x50 * val i + 0x30
    else
      if val i * 0x50 + 0x20 = val len then 0x50 * val i + 0x20
      else
        if val i * 0x50 + 0x10 = val len then 0x50 * val i + 0x10
        else 0x50 * val i`;;

(* For X9 and X10, they stand for i * 0x5 + 4 when number of blocks is divisible by 5 *)
let tail_cases_in_index = new_definition
`tail_cases_in_index (i:int64) (len:int64) (last:bool) : num =
  if val i * 0x50 + 0x40 = val len then val i * 0x5 + 4
  else
    if val i * 0x50 + 0x30 = val len then val i * 0x5 + 3
    else
      if val i * 0x50 + 0x20 = val len then val i * 0x5 + 2
      else
        if val i * 0x50 + 0x10 = val len then val i * 0x5 + 1
        else
          if last then val i * 0x5 else val i * 0x5 + 4`;;

let AES_XTS_DECRYPT_CORRECT = prove(
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
    (\s. read PC s = word (pc + 0xb00) /\
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

    (* These are for top-level wrapper function
    (* Add values for preserved registers *)
    ENSURES_PRESERVED_TAC "x19_init" `X19` THEN
    ENSURES_PRESERVED_TAC "x20_init" `X20` THEN
    ENSURES_PRESERVED_TAC "x21_init" `X21` THEN
    ENSURES_PRESERVED_TAC "x22_init" `X22` THEN
    ENSURES_PRESERVED_DREG_TAC "d8_init" `D8` THEN
    ENSURES_PRESERVED_DREG_TAC "d9_init" `D9` THEN
    ENSURES_PRESERVED_DREG_TAC "d10_init" `D10` THEN
    ENSURES_PRESERVED_DREG_TAC "d11_init" `D11` THEN
    ENSURES_PRESERVED_DREG_TAC "d12_init" `D12` THEN
    ENSURES_PRESERVED_DREG_TAC "d13_init" `D13` THEN
    ENSURES_PRESERVED_DREG_TAC "d14_init" `D14` THEN
    ENSURES_PRESERVED_DREG_TAC "d15_init" `D15` THEN
*)

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
    ASM_CASES_TAC `val (len:int64) < 96` THENL [CHEAT_TAC; ALL_TAC] THEN

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
      UNDISCH_TAC `~(val (num_blocks:int64) < 96)` THEN
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
    (* relationship between variables *)
    SUBGOAL_THEN `val (num_blocks:int64) <= val (len:int64)` ASSUME_TAC THENL
    [ EXPAND_TAC "num_blocks" THEN SIMP_TAC[NUM_BLOCKS_LT_LEN_THM]; ALL_TAC] THEN
    SUBGOAL_THEN `val (num_blocks_adjusted:int64) <= val (len:int64)` ASSUME_TAC THENL
    [ EXPAND_TAC "num_blocks_adjusted" THEN
      COND_CASES_TAC THENL
      [ ASM_SIMP_TAC[];
        UNDISCH_TAC `~(val (num_blocks:int64) < 0x60)` THEN
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
          NUM_REDUCE_TAC THEN SIMP_TAC[MOD_LT]; ALL_TAC] THEN
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
        NUM_REDUCE_TAC THEN SIMP_TAC[MOD_LT]
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
        read X0 s = word_add ct_ptr (word (tail_cases_in_byte num_5blocks_adjusted num_blocks_adjusted)) /\
        read X1 s = word_add pt_ptr (word (tail_cases_in_byte num_5blocks_adjusted num_blocks_adjusted)) /\
        read X3 s = key1_ptr /\
        read X21 s = tail_len /\
        read Q6 s = calculate_tweak (tail_cases_in_index num_5blocks_adjusted num_blocks_adjusted T) iv key2 /\
        read X19 s = word 0x87 /\
        read X10 s = word_subword (calculate_tweak (tail_cases_in_index num_5blocks_adjusted num_blocks_adjusted F) iv key2) (64,64) /\
        read X9 s = word_zx (calculate_tweak (tail_cases_in_index num_5blocks_adjusted num_blocks_adjusted F) iv key2) /\
        byte_list_at ct ct_ptr len s /\
        byte_list_at (aes256_xts_decrypt ct (tail_cases_in_byte num_5blocks_adjusted num_blocks_adjusted) iv key1 key2)
           pt_ptr (word (tail_cases_in_byte num_5blocks_adjusted num_blocks_adjusted)) s /\
        set_key_schedule s key1_ptr k00 k01 k02 k03 k04 k05 k06 k07 k08 k09 k0a k0b k0c k0d k0e` THEN
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
         byte_list_at (aes256_xts_decrypt ct (80 * i) iv key1 key2) pt_ptr (word (80 * i)) s /\
         set_key_schedule s key1_ptr k00 k01 k02 k03 k04 k05 k06 k07 k08 k09 k0a k0b k0c k0d k0e) /\
        // loop backedge condition
        (read ZF s <=> i = val (num_5blocks_adjusted:int64))` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
    [
      (* Subgoal 1. Bound of loop is not zero -- automatically discharged by asm *)
      (* Subgoal 2. Invariant holds before entering the loop *)
      REWRITE_TAC[byte_list_at; set_key_schedule] THEN
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

      (* TODO: add a comment explaining what this bound is for *)
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
      ASM_REWRITE_TAC[byte_list_at; set_key_schedule] THEN

      ENSURES_INIT_TAC "s0" THEN
      (* List values for ct_ptr + [0 .. 0x40] *)
      MP_TAC (SPECL [`ct_ptr:int64`; `i:num`; `len:int64`; `ct:byte list`; `s0:armstate`] READ_CT_LEMMA) THEN
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
        MP_TAC (SPECL [`0x50 * i + 0x50:num`; `(aes256_xts_decrypt ct (0x50 * i + 0x50) iv key1 key2):byte list`; `s188:armstate`] BYTE_LIST_TO_NUM_THM) THEN
        ANTS_TAC THENL[
          REWRITE_TAC[ARITH_RULE `0x50 * i + 0x50 = 0x10 * (5 * i + 5)`;
                      LENGTH_OF_AES256_XTS_DECRYPT_FULL_BLOCKS] THEN
          ARITH_TAC
          ; ALL_TAC] THEN
        DISCH_THEN (fun th -> REWRITE_TAC[th]) THEN
        MP_TAC (SPECL [`0x50 * i:num`; `(aes256_xts_decrypt ct (0x50 * i) iv key1 key2):byte list`; `s188:armstate`] BYTE_LIST_TO_NUM_THM) THEN
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
      REWRITE_TAC[byte_list_at; set_key_schedule] THEN
      ENSURES_INIT_TAC "s0" THEN
      ARM_ACCSTEPS_TAC AES_XTS_DECRYPT_EXEC [] (1--1) THEN
      SUBGOAL_THEN `~(val (word_sub (num_5blocks_adjusted:int64) (word i)) = 0x0)` ASSUME_TAC THENL
      [ UNDISCH_TAC `i < val (num_5blocks_adjusted:int64)` THEN WORD_ARITH_TAC; ALL_TAC] THEN
      POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_SIMP_TAC[];


      (* Subgoal 5: Prove the invariant implies post-condition
                    Backedge instruction is executed here *)
      REPEAT STRIP_TAC THEN
      REWRITE_TAC[byte_list_at; set_key_schedule] THEN
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
        MP_TAC (SPECL [`ct_ptr:int64`; `num_5blocks_adjusted:int64`; `len:int64`; `ct:byte list`; `s3:armstate`] READ_CT_TAIL4_LEMMA) THEN
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
        RULE_ASSUM_TAC(REWRITE_RULE
          [WORD_RULE `word_mul (word 0x50) num_5blocks_adjusted:int64 = word(0x50 * val num_5blocks_adjusted)`]) THEN

        (* TODO: there is a non-overlapping issue in the symbolic simulation that the third block is missing *)
        ARM_ACCSTEPS_TAC AES_XTS_DECRYPT_EXEC [] (134--136) THEN
        ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
        REPEAT CONJ_TAC THENL
        [
          REWRITE_TAC[tail_cases_in_byte] THEN ASM_SIMP_TAC[] THEN CONV_TAC WORD_RULE;
          REWRITE_TAC[tail_cases_in_byte] THEN ASM_SIMP_TAC[] THEN CONV_TAC WORD_RULE;
          REWRITE_TAC[tail_cases_in_index] THEN ASM_SIMP_TAC[] THEN CONV_TAC WORD_RULE;
          REWRITE_TAC[tail_cases_in_index] THEN ASM_SIMP_TAC[] THEN CONV_TAC WORD_RULE;
          REWRITE_TAC[tail_cases_in_index] THEN ASM_SIMP_TAC[] THEN CONV_TAC WORD_RULE;

          REWRITE_TAC[tail_cases_in_byte] THEN ASM_SIMP_TAC[LE_REFL] THEN
          SUBGOAL_THEN `val ((word (0x50 * val (num_5blocks_adjusted:int64) + 0x40)):int64) =
            0x50 * val num_5blocks_adjusted + 0x40` ASSUME_TAC THENL
          [ IMP_REWRITE_TAC[VAL_WORD; MOD_LT; DIMINDEX_64] THEN
            UNDISCH_TAC `val (num_5blocks_adjusted:int64) * 0x50 + 0x40 <= val (len:int64)` THEN
            UNDISCH_TAC `val (len:int64) <= 0x2 EXP 0x18` THEN
            ARITH_TAC; ALL_TAC] THEN
          POP_ASSUM(fun th -> REWRITE_TAC[th]) THEN

          (* TODO: Manually add the assumption as a temporary fix *)
          SUBGOAL_THEN `read
          (memory :>
            bytes128
            (word_add (pt_ptr:int64) (word (0x50 * val (num_5blocks_adjusted:int64) + 0x20))))
            s136 =
          aes256_xts_decrypt_round
            (bytes_to_int128
              (SUB_LIST (val num_5blocks_adjusted * 0x50 + 0x20,0x10) ct))
            (calculate_tweak (val num_5blocks_adjusted * 0x5 + 0x2) iv key2)
            key1` ASSUME_TAC THENL [CHEAT_TAC; ALL_TAC] THEN
          (* TODO: ??? *)
          RULE_ASSUM_TAC(REWRITE_RULE
          [WORD_RULE `(word_add (word_add pt_ptr (word (0x50 * val num_5blocks_adjusted)))
              (word 0x30)) = (word_add (pt_ptr:int64) (word (0x50 * val (num_5blocks_adjusted:int64) + 0x30)))`]) THEN

          (* Remove quantifier *)
          UNDISCH_TAC
          `forall i.
            i < 0x50 * val (num_5blocks_adjusted:int64)
            ==> read (memory :> bytes8 (word_add pt_ptr (word i))) s136 =
                EL i (aes256_xts_decrypt ct (0x50 * val num_5blocks_adjusted) iv key1 key2)` THEN
          MP_TAC (SPECL [`0x50 * val (num_5blocks_adjusted:int64) + 0x40:num`;
                         `(aes256_xts_decrypt ct (0x50 * val (num_5blocks_adjusted:int64) + 0x40) iv key1 key2):byte list`;
                         `s136:armstate`] BYTE_LIST_TO_NUM_THM) THEN
          ANTS_TAC THENL[
            REWRITE_TAC[ARITH_RULE `0x50 * i + 0x40 = 0x10 * (5 * i + 4)`;
                        LENGTH_OF_AES256_XTS_DECRYPT_FULL_BLOCKS] THEN
            ARITH_TAC
            ; ALL_TAC] THEN
          DISCH_THEN (fun th -> REWRITE_TAC[th]) THEN
          MP_TAC (SPECL [`0x50 * val (num_5blocks_adjusted:int64):num`;
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
        MP_TAC (SPECL [`ct_ptr:int64`; `num_5blocks_adjusted:int64`; `len:int64`; `ct:byte list`; `s5:armstate`] READ_CT_TAIL3_LEMMA) THEN
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
          REWRITE_TAC[tail_cases_in_byte] THEN ASM_SIMP_TAC[] THEN CONV_TAC WORD_RULE;
          REWRITE_TAC[tail_cases_in_byte] THEN ASM_SIMP_TAC[] THEN CONV_TAC WORD_RULE;
          REWRITE_TAC[tail_cases_in_index] THEN ASM_SIMP_TAC[] THEN CONV_TAC WORD_RULE;
          REWRITE_TAC[tail_cases_in_index] THEN ASM_SIMP_TAC[] THEN CONV_TAC WORD_RULE;
          REWRITE_TAC[tail_cases_in_index] THEN ASM_SIMP_TAC[] THEN CONV_TAC WORD_RULE;

          REWRITE_TAC[tail_cases_in_byte] THEN ASM_SIMP_TAC[LE_REFL] THEN
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
          MP_TAC (SPECL [`0x50 * val (num_5blocks_adjusted:int64) + 0x30:num`;
                         `(aes256_xts_decrypt ct (0x50 * val (num_5blocks_adjusted:int64) + 0x30) iv key1 key2):byte list`;
                         `s108:armstate`] BYTE_LIST_TO_NUM_THM) THEN
          ANTS_TAC THENL[
            REWRITE_TAC[ARITH_RULE `0x50 * i + 0x30 = 0x10 * (5 * i + 3)`;
                        LENGTH_OF_AES256_XTS_DECRYPT_FULL_BLOCKS] THEN
            ARITH_TAC
            ; ALL_TAC] THEN
          DISCH_THEN (fun th -> REWRITE_TAC[th]) THEN
          MP_TAC (SPECL [`0x50 * val (num_5blocks_adjusted:int64):num`;
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
        MP_TAC (SPECL [`ct_ptr:int64`; `num_5blocks_adjusted:int64`; `len:int64`; `ct:byte list`; `s7:armstate`] READ_CT_TAIL2_LEMMA) THEN
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
          REWRITE_TAC[tail_cases_in_byte] THEN ASM_SIMP_TAC[] THEN CONV_TAC WORD_RULE;
          REWRITE_TAC[tail_cases_in_byte] THEN ASM_SIMP_TAC[] THEN CONV_TAC WORD_RULE;
          REWRITE_TAC[tail_cases_in_index] THEN ASM_SIMP_TAC[] THEN CONV_TAC WORD_RULE;
          REWRITE_TAC[tail_cases_in_index] THEN ASM_SIMP_TAC[] THEN CONV_TAC WORD_RULE;
          REWRITE_TAC[tail_cases_in_index] THEN ASM_SIMP_TAC[] THEN CONV_TAC WORD_RULE;

          REWRITE_TAC[tail_cases_in_byte] THEN ASM_SIMP_TAC[LE_REFL] THEN
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
          MP_TAC (SPECL [`0x50 * val (num_5blocks_adjusted:int64) + 0x20:num`;
                         `(aes256_xts_decrypt ct (0x50 * val (num_5blocks_adjusted:int64) + 0x20) iv key1 key2):byte list`;
                         `s78:armstate`] BYTE_LIST_TO_NUM_THM) THEN
          ANTS_TAC THENL[
            REWRITE_TAC[ARITH_RULE `0x50 * i + 0x20 = 0x10 * (5 * i + 2)`;
                        LENGTH_OF_AES256_XTS_DECRYPT_FULL_BLOCKS] THEN
            ARITH_TAC
            ; ALL_TAC] THEN
          DISCH_THEN (fun th -> REWRITE_TAC[th]) THEN
          MP_TAC (SPECL [`0x50 * val (num_5blocks_adjusted:int64):num`;
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
        MP_TAC (SPECL [`ct_ptr:int64`; `num_5blocks_adjusted:int64`; `len:int64`; `ct:byte list`; `s9:armstate`] READ_CT_TAIL1_LEMMA) THEN
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
          REWRITE_TAC[tail_cases_in_byte] THEN ASM_SIMP_TAC[] THEN CONV_TAC WORD_RULE;
          REWRITE_TAC[tail_cases_in_byte] THEN ASM_SIMP_TAC[] THEN CONV_TAC WORD_RULE;
          REWRITE_TAC[tail_cases_in_index] THEN ASM_SIMP_TAC[] THEN CONV_TAC WORD_RULE;
          REWRITE_TAC[tail_cases_in_index] THEN ASM_SIMP_TAC[] THEN CONV_TAC WORD_RULE;
          REWRITE_TAC[tail_cases_in_index] THEN ASM_SIMP_TAC[] THEN CONV_TAC WORD_RULE;

          REWRITE_TAC[tail_cases_in_byte] THEN ASM_SIMP_TAC[LE_REFL] THEN
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
          MP_TAC (SPECL [`0x50 * val (num_5blocks_adjusted:int64) + 0x10:num`;
                         `(aes256_xts_decrypt ct (0x50 * val (num_5blocks_adjusted:int64) + 0x10) iv key1 key2):byte list`;
                         `s50:armstate`] BYTE_LIST_TO_NUM_THM) THEN
          ANTS_TAC THENL[
            REWRITE_TAC[ARITH_RULE `0x50 * i + 0x10 = 0x10 * (5 * i + 1)`;
                        LENGTH_OF_AES256_XTS_DECRYPT_FULL_BLOCKS] THEN
            ARITH_TAC
            ; ALL_TAC] THEN
          DISCH_THEN (fun th -> REWRITE_TAC[th]) THEN
          MP_TAC (SPECL [`0x50 * val (num_5blocks_adjusted:int64):num`;
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
      [ SUBGOAL_THEN `~(val (num_blocks_adjusted:int64) - val (num_5blocks_adjusted:int64) * 0x50 - 0x40 = 0)` MP_TAC THENL
        [ CHEAT_TAC; ALL_TAC] THEN
        SUBGOAL_THEN `~(val (num_blocks_adjusted:int64) - val (num_5blocks_adjusted:int64) * 0x50 - 0x30 = 0)` MP_TAC THENL
        [ CHEAT_TAC; ALL_TAC] THEN
        SUBGOAL_THEN `~(val (num_blocks_adjusted:int64) - val (num_5blocks_adjusted:int64) * 0x50 - 0x20 = 0)` MP_TAC THENL
        [ CHEAT_TAC; ALL_TAC] THEN
        SUBGOAL_THEN `~(val (num_blocks_adjusted:int64) - val (num_5blocks_adjusted:int64) * 0x50 - 0x10 = 0)` MP_TAC THENL
        [ CHEAT_TAC; ALL_TAC] THEN
        SUBGOAL_THEN `val (num_blocks_adjusted:int64) DIV 0x50 = val (num_5blocks_adjusted:int64)` MP_TAC THENL
        [ CHEAT_TAC; ALL_TAC] THEN
        SIMP_TAC[SPECL [`val (num_blocks_adjusted:int64)`; `val (num_5blocks_adjusted:int64)`] DIVISION_BY_80_LEMMA]
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
        REWRITE_TAC[tail_cases_in_byte] THEN ASM_SIMP_TAC[] THEN CONV_TAC WORD_RULE;
        REWRITE_TAC[tail_cases_in_byte] THEN ASM_SIMP_TAC[] THEN CONV_TAC WORD_RULE;
        REWRITE_TAC[tail_cases_in_index] THEN ASM_SIMP_TAC[] THEN CONV_TAC WORD_RULE;
        REWRITE_TAC[tail_cases_in_index] THEN ASM_SIMP_TAC[] THEN CONV_TAC WORD_RULE;
        REWRITE_TAC[tail_cases_in_index] THEN ASM_SIMP_TAC[] THEN CONV_TAC WORD_RULE;
        REWRITE_TAC[tail_cases_in_byte] THEN ASM_SIMP_TAC[LE_REFL]
      ]
    ] (* End of loop invariant proof *)
    ; ALL_TAC] THEN

    (* prove the rest of the program, basically cipher stealing *)
    CHEAT_TAC
);;
