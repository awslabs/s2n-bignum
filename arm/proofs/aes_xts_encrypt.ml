(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)
use_file_raise_failure := true;;

needs "arm/proofs/utils/aes_xts_common.ml";;

(* print_literal_from_elf "arm/aes-xts/aes_xts_encrypt.o";; *)
let aes256_xts_encrypt_mc = define_assert_from_elf "aes256_xts_encrypt_mc" "arm/aes-xts/aes_xts_encrypt.o"
[
  0xd10183ff;       (* arm_SUB SP SP (rvalue (word 0x60)) *)
  0x6d0227e8;       (* arm_STP D8 D9 SP (Immediate_Offset (iword (&0x20))) *)
  0x6d032fea;       (* arm_STP D10 D11 SP (Immediate_Offset (iword (&0x30))) *)
  0x6d0437ec;       (* arm_STP D12 D13 SP (Immediate_Offset (iword (&0x40))) *)
  0x6d053fee;       (* arm_STP D14 D15 SP (Immediate_Offset (iword (&0x50))) *)
  0xa90053f3;       (* arm_STP X19 X20 SP (Immediate_Offset (iword (&0x0))) *)
  0xa9015bf5;       (* arm_STP X21 X22 SP (Immediate_Offset (iword (&0x10))) *)
  0xf100405f;       (* arm_CMP X2 (rvalue (word 0x10)) *)
  0x5400536b;       (* arm_BLT (word 0xa6c) *)
  0xd503201f;       (* arm_NOP *)
  0xd503201f;       (* arm_NOP *)
  0xd503201f;       (* arm_NOP *)

  (* // Lxts_enc_big_size: *)
  0x92400c55;       (* arm_AND X21 X2 (rvalue (word 0xf)) *)
  0x927cec42;       (* arm_AND X2 X2 (rvalue (word 0xfffffffffffffff0)) *)

  (* // Firstly, encrypt the iv with key2 *)
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

  (* Load key schedule *)
  (* pc + 0x80 *)
  0xaa0303e7;       (* arm_MOV X7 X3 *)
  0x4cdfa8f0;       (* arm_LDP Q16 Q17 X7 (Postimmediate_Offset (word 0x20)) *)
  0x4cdfa8ec;       (* arm_LDP Q12 Q13 X7 (Postimmediate_Offset (word 0x20)) *)
  0x4cdfa8ee;       (* arm_LDP Q14 Q15 X7 (Postimmediate_Offset (word 0x20)) *)
  0x4cdfa8e4;       (* arm_LDP Q4 Q5 X7 (Postimmediate_Offset (word 0x20)) *)
  0x4cdfa8f2;       (* arm_LDP Q18 Q19 X7 (Postimmediate_Offset (word 0x20)) *)
  0x4cdfa8f4;       (* arm_LDP Q20 Q21 X7 (Postimmediate_Offset (word 0x20)) *)
  0x4cdfa8f6;       (* arm_LDP Q22 Q23 X7 (Postimmediate_Offset (word 0x20)) *)
  0x4c4078e7;       (* arm_LDR Q7 X7 No_Offset *)

  (* Lxts_enc: *)
  (* pc + 0xa4 *)
  0x528010f3;       (* arm_MOV W19 (rvalue (word 0x87)) *)
  0xf100805f;       (* arm_CMP X2 (rvalue (word 0x20)) *)
  0x54004463;       (* arm_BCC (word 0x88c) *)
  0x9e6600c9;       (* arm_FMOV_FtoI X9 Q6 0x0 0x40 *)
  0x9eae00ca;       (* arm_FMOV_FtoI X10 Q6 0x1 0x40 *)
  0x93ca8156;       (* arm_ROR X22 X10 0x20 *)
  0x93c9fd4a;       (* arm_EXTR X10 X10 X9 0x3f *)
  0x0a967e6b;       (* arm_AND W11 W19 (Shiftedreg W22 ASR 0x1f) *)
  0xca090569;       (* arm_EOR X9 X11 (Shiftedreg X9 LSL 0x1) *)
  0x9e670128;       (* arm_FMOV_ItoF Q8 X9 0x0 *)
  0x9eaf0148;       (* arm_FMOV_ItoF Q8 X10 0x1 *)
  0xf100c05f;       (* arm_CMP X2 (rvalue (word 0x30)) *)
  0x54003a43;       (* arm_BCC (word 0x748) *)
  0x93ca8156;       (* arm_ROR X22 X10 0x20 *)
  0x93c9fd4a;       (* arm_EXTR X10 X10 X9 0x3f *)
  0x0a967e6b;       (* arm_AND W11 W19 (Shiftedreg W22 ASR 0x1f) *)
  0xca090569;       (* arm_EOR X9 X11 (Shiftedreg X9 LSL 0x1) *)
  0x9e670129;       (* arm_FMOV_ItoF Q9 X9 0x0 *)
  0x9eaf0149;       (* arm_FMOV_ItoF Q9 X10 0x1 *)
  0xf101005f;       (* arm_CMP X2 (rvalue (word 0x40)) *)
  0x54002c63;       (* arm_BCC (word 0x58c) *)
  0x93ca8156;       (* arm_ROR X22 X10 0x20 *)
  0x93c9fd4a;       (* arm_EXTR X10 X10 X9 0x3f *)
  0x0a967e6b;       (* arm_AND W11 W19 (Shiftedreg W22 ASR 0x1f) *)
  0xca090569;       (* arm_EOR X9 X11 (Shiftedreg X9 LSL 0x1) *)
  0x9e67012a;       (* arm_FMOV_ItoF Q10 X9 0x0 *)
  0x9eaf014a;       (* arm_FMOV_ItoF Q10 X10 0x1 *)
  0xf101405f;       (* arm_CMP X2 (rvalue (word 0x50)) *)
  0x54001a63;       (* arm_BCC (word 0x34c) *)
  0x93ca8156;       (* arm_ROR X22 X10 0x20 *)
  0x93c9fd4a;       (* arm_EXTR X10 X10 X9 0x3f *)
  0x0a967e6b;       (* arm_AND W11 W19 (Shiftedreg W22 ASR 0x1f) *)
  0xca090569;       (* arm_EOR X9 X11 (Shiftedreg X9 LSL 0x1) *)
  0x9e67012b;       (* arm_FMOV_ItoF Q11 X9 0x0 *)
  0x9eaf014b;       (* arm_FMOV_ItoF Q11 X10 0x1 *)
  0xb202e7e8;       (* arm_MOV X8 (rvalue (word 0xcccccccccccccccc)) *)
  0xf29999a8;       (* arm_MOVK X8 (word 0xcccd) 0x0 *)
  0x9bc87c48;       (* arm_UMULH X8 X2 X8 *)
  0xd346fd08;       (* arm_LSR X8 X8 0x6 *)

  (* .Loop5x_xts_enc: *)
  (* pc + 0x140 *)
  0xacc28400;       (* arm_LDP Q0 Q1 X0 (Postimmediate_Offset (iword (&0x50))) *)
  0xad7ee418;       (* arm_LDP Q24 Q25 X0 (Immediate_Offset (iword (-- &0x30))) *)
  0x3cdf001a;       (* arm_LDR Q26 X0 (Immediate_Offset (word 0xfffffffffffffff0)) *)
  0x6e261c00;       (* arm_EOR_VEC Q0 Q0 Q6 0x80 *)
  0x6e281c21;       (* arm_EOR_VEC Q1 Q1 Q8 0x80 *)
  0x6e291f18;       (* arm_EOR_VEC Q24 Q24 Q9 0x80 *)
  0x6e2a1f39;       (* arm_EOR_VEC Q25 Q25 Q10 0x80 *)
  0x6e2b1f5a;       (* arm_EOR_VEC Q26 Q26 Q11 0x80 *)
  0x4e284a00;       (* arm_AESE Q0 Q16 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284a01;       (* arm_AESE Q1 Q16 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284a18;       (* arm_AESE Q24 Q16 *)
  0x4e286b18;       (* arm_AESMC Q24 Q24 *)
  0x4e284a19;       (* arm_AESE Q25 Q16 *)
  0x4e286b39;       (* arm_AESMC Q25 Q25 *)
  0x4e284a1a;       (* arm_AESE Q26 Q16 *)
  0x4e286b5a;       (* arm_AESMC Q26 Q26 *)
  0x4e284a20;       (* arm_AESE Q0 Q17 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284a21;       (* arm_AESE Q1 Q17 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284a38;       (* arm_AESE Q24 Q17 *)
  0x4e286b18;       (* arm_AESMC Q24 Q24 *)
  0x4e284a39;       (* arm_AESE Q25 Q17 *)
  0x4e286b39;       (* arm_AESMC Q25 Q25 *)
  0x4e284a3a;       (* arm_AESE Q26 Q17 *)
  0x4e286b5a;       (* arm_AESMC Q26 Q26 *)
  0x4e284980;       (* arm_AESE Q0 Q12 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284981;       (* arm_AESE Q1 Q12 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284998;       (* arm_AESE Q24 Q12 *)
  0x4e286b18;       (* arm_AESMC Q24 Q24 *)
  0x4e284999;       (* arm_AESE Q25 Q12 *)
  0x4e286b39;       (* arm_AESMC Q25 Q25 *)
  0x4e28499a;       (* arm_AESE Q26 Q12 *)
  0x4e286b5a;       (* arm_AESMC Q26 Q26 *)
  0x4e2849a0;       (* arm_AESE Q0 Q13 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e2849a1;       (* arm_AESE Q1 Q13 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e2849b8;       (* arm_AESE Q24 Q13 *)
  0x4e286b18;       (* arm_AESMC Q24 Q24 *)
  0x4e2849b9;       (* arm_AESE Q25 Q13 *)
  0x4e286b39;       (* arm_AESMC Q25 Q25 *)
  0x4e2849ba;       (* arm_AESE Q26 Q13 *)
  0x4e286b5a;       (* arm_AESMC Q26 Q26 *)
  0x4e2849c0;       (* arm_AESE Q0 Q14 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e2849c1;       (* arm_AESE Q1 Q14 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e2849d8;       (* arm_AESE Q24 Q14 *)
  0x4e286b18;       (* arm_AESMC Q24 Q24 *)
  0x4e2849d9;       (* arm_AESE Q25 Q14 *)
  0x4e286b39;       (* arm_AESMC Q25 Q25 *)
  0x4e2849da;       (* arm_AESE Q26 Q14 *)
  0x4e286b5a;       (* arm_AESMC Q26 Q26 *)
  0x4e2849e0;       (* arm_AESE Q0 Q15 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e2849e1;       (* arm_AESE Q1 Q15 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e2849f8;       (* arm_AESE Q24 Q15 *)
  0x4e286b18;       (* arm_AESMC Q24 Q24 *)
  0x4e2849f9;       (* arm_AESE Q25 Q15 *)
  0x4e286b39;       (* arm_AESMC Q25 Q25 *)
  0x4e2849fa;       (* arm_AESE Q26 Q15 *)
  0x4e286b5a;       (* arm_AESMC Q26 Q26 *)
  0x4e284880;       (* arm_AESE Q0 Q4 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284881;       (* arm_AESE Q1 Q4 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284898;       (* arm_AESE Q24 Q4 *)
  0x4e286b18;       (* arm_AESMC Q24 Q24 *)
  0x4e284899;       (* arm_AESE Q25 Q4 *)
  0x4e286b39;       (* arm_AESMC Q25 Q25 *)
  0x4e28489a;       (* arm_AESE Q26 Q4 *)
  0x4e286b5a;       (* arm_AESMC Q26 Q26 *)
  0x4e2848a0;       (* arm_AESE Q0 Q5 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e2848a1;       (* arm_AESE Q1 Q5 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e2848b8;       (* arm_AESE Q24 Q5 *)
  0x4e286b18;       (* arm_AESMC Q24 Q24 *)
  0x4e2848b9;       (* arm_AESE Q25 Q5 *)
  0x4e286b39;       (* arm_AESMC Q25 Q25 *)
  0x4e2848ba;       (* arm_AESE Q26 Q5 *)
  0x4e286b5a;       (* arm_AESMC Q26 Q26 *)
  0x4e284a40;       (* arm_AESE Q0 Q18 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284a41;       (* arm_AESE Q1 Q18 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284a58;       (* arm_AESE Q24 Q18 *)
  0x4e286b18;       (* arm_AESMC Q24 Q24 *)
  0x4e284a59;       (* arm_AESE Q25 Q18 *)
  0x4e286b39;       (* arm_AESMC Q25 Q25 *)
  0x4e284a5a;       (* arm_AESE Q26 Q18 *)
  0x4e286b5a;       (* arm_AESMC Q26 Q26 *)
  0x4e284a60;       (* arm_AESE Q0 Q19 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284a61;       (* arm_AESE Q1 Q19 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284a78;       (* arm_AESE Q24 Q19 *)
  0x4e286b18;       (* arm_AESMC Q24 Q24 *)
  0x4e284a79;       (* arm_AESE Q25 Q19 *)
  0x4e286b39;       (* arm_AESMC Q25 Q25 *)
  0x4e284a7a;       (* arm_AESE Q26 Q19 *)
  0x4e286b5a;       (* arm_AESMC Q26 Q26 *)
  0x4e284a80;       (* arm_AESE Q0 Q20 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284a81;       (* arm_AESE Q1 Q20 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284a98;       (* arm_AESE Q24 Q20 *)
  0x4e286b18;       (* arm_AESMC Q24 Q24 *)
  0x4e284a99;       (* arm_AESE Q25 Q20 *)
  0x4e286b39;       (* arm_AESMC Q25 Q25 *)
  0x4e284a9a;       (* arm_AESE Q26 Q20 *)
  0x4e286b5a;       (* arm_AESMC Q26 Q26 *)
  0x4e284aa0;       (* arm_AESE Q0 Q21 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284aa1;       (* arm_AESE Q1 Q21 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284ab8;       (* arm_AESE Q24 Q21 *)
  0x4e286b18;       (* arm_AESMC Q24 Q24 *)
  0x4e284ab9;       (* arm_AESE Q25 Q21 *)
  0x4e286b39;       (* arm_AESMC Q25 Q25 *)
  0x4e284aba;       (* arm_AESE Q26 Q21 *)
  0x4e286b5a;       (* arm_AESMC Q26 Q26 *)
  0x4e284ac0;       (* arm_AESE Q0 Q22 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284ac1;       (* arm_AESE Q1 Q22 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284ad8;       (* arm_AESE Q24 Q22 *)
  0x4e286b18;       (* arm_AESMC Q24 Q24 *)
  0x4e284ad9;       (* arm_AESE Q25 Q22 *)
  0x4e286b39;       (* arm_AESMC Q25 Q25 *)
  0x4e284ada;       (* arm_AESE Q26 Q22 *)
  0x4e286b5a;       (* arm_AESMC Q26 Q26 *)
  0x4e284ae0;       (* arm_AESE Q0 Q23 *)
  0x4e284ae1;       (* arm_AESE Q1 Q23 *)
  0x4e284af8;       (* arm_AESE Q24 Q23 *)
  0x4e284af9;       (* arm_AESE Q25 Q23 *)
  0x4e284afa;       (* arm_AESE Q26 Q23 *)
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
  0xd1014042;       (* arm_SUB X2 X2 (rvalue (word 0x50)) *)
  0xf1000508;       (* arm_SUBS X8 X8 (rvalue (word 0x1)) *)
  0xb5ffe888;       (* arm_CBNZ X8 (word 0x1ffd10) *)

  (* .Loop5x_enc_after: *)
  (* pc +  0x434 *)
  0xf101005f;       (* arm_CMP X2 (rvalue (word 0x40)) *)
  0x54000140;       (* arm_BEQ (word 0x28) *)
  0xf100c05f;       (* arm_CMP X2 (rvalue (word 0x30)) *)
  0x54001200;       (* arm_BEQ (word 0x240) *)
  0xf100805f;       (* arm_CMP X2 (rvalue (word 0x20)) *)
  0x54001ea0;       (* arm_BEQ (word 0x3d4) *)
  0xf100405f;       (* arm_CMP X2 (rvalue (word 0x10)) *)
  0x54002740;       (* arm_BEQ (word 0x4e8) *)
  0x14000163;       (* arm_B (word 0x58c) *)
  0xd503201f;       (* arm_NOP *)
  0xd503201f;       (* arm_NOP *)
  0x4cdf7000;       (* arm_LDR Q0 X0 (Postimmediate_Offset (word 0x10)) *)
  0x4cdf7001;       (* arm_LDR Q1 X0 (Postimmediate_Offset (word 0x10)) *)
  0x4cdf7018;       (* arm_LDR Q24 X0 (Postimmediate_Offset (word 0x10)) *)
  0x4cdf7019;       (* arm_LDR Q25 X0 (Postimmediate_Offset (word 0x10)) *)
  0x6e261c00;       (* arm_EOR_VEC Q0 Q0 Q6 0x80 *)
  0x6e281c21;       (* arm_EOR_VEC Q1 Q1 Q8 0x80 *)
  0x6e291f18;       (* arm_EOR_VEC Q24 Q24 Q9 0x80 *)
  0x6e2a1f39;       (* arm_EOR_VEC Q25 Q25 Q10 0x80 *)
  0x4e284a00;       (* arm_AESE Q0 Q16 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284a01;       (* arm_AESE Q1 Q16 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284a18;       (* arm_AESE Q24 Q16 *)
  0x4e286b18;       (* arm_AESMC Q24 Q24 *)
  0x4e284a19;       (* arm_AESE Q25 Q16 *)
  0x4e286b39;       (* arm_AESMC Q25 Q25 *)
  0x4e284a20;       (* arm_AESE Q0 Q17 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284a21;       (* arm_AESE Q1 Q17 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284a38;       (* arm_AESE Q24 Q17 *)
  0x4e286b18;       (* arm_AESMC Q24 Q24 *)
  0x4e284a39;       (* arm_AESE Q25 Q17 *)
  0x4e286b39;       (* arm_AESMC Q25 Q25 *)
  0x4e284980;       (* arm_AESE Q0 Q12 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284981;       (* arm_AESE Q1 Q12 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284998;       (* arm_AESE Q24 Q12 *)
  0x4e286b18;       (* arm_AESMC Q24 Q24 *)
  0x4e284999;       (* arm_AESE Q25 Q12 *)
  0x4e286b39;       (* arm_AESMC Q25 Q25 *)
  0x4e2849a0;       (* arm_AESE Q0 Q13 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e2849a1;       (* arm_AESE Q1 Q13 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e2849b8;       (* arm_AESE Q24 Q13 *)
  0x4e286b18;       (* arm_AESMC Q24 Q24 *)
  0x4e2849b9;       (* arm_AESE Q25 Q13 *)
  0x4e286b39;       (* arm_AESMC Q25 Q25 *)
  0x4e2849c0;       (* arm_AESE Q0 Q14 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e2849c1;       (* arm_AESE Q1 Q14 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e2849d8;       (* arm_AESE Q24 Q14 *)
  0x4e286b18;       (* arm_AESMC Q24 Q24 *)
  0x4e2849d9;       (* arm_AESE Q25 Q14 *)
  0x4e286b39;       (* arm_AESMC Q25 Q25 *)
  0x4e2849e0;       (* arm_AESE Q0 Q15 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e2849e1;       (* arm_AESE Q1 Q15 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e2849f8;       (* arm_AESE Q24 Q15 *)
  0x4e286b18;       (* arm_AESMC Q24 Q24 *)
  0x4e2849f9;       (* arm_AESE Q25 Q15 *)
  0x4e286b39;       (* arm_AESMC Q25 Q25 *)
  0x4e284880;       (* arm_AESE Q0 Q4 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284881;       (* arm_AESE Q1 Q4 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284898;       (* arm_AESE Q24 Q4 *)
  0x4e286b18;       (* arm_AESMC Q24 Q24 *)
  0x4e284899;       (* arm_AESE Q25 Q4 *)
  0x4e286b39;       (* arm_AESMC Q25 Q25 *)
  0x4e2848a0;       (* arm_AESE Q0 Q5 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e2848a1;       (* arm_AESE Q1 Q5 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e2848b8;       (* arm_AESE Q24 Q5 *)
  0x4e286b18;       (* arm_AESMC Q24 Q24 *)
  0x4e2848b9;       (* arm_AESE Q25 Q5 *)
  0x4e286b39;       (* arm_AESMC Q25 Q25 *)
  0x4e284a40;       (* arm_AESE Q0 Q18 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284a41;       (* arm_AESE Q1 Q18 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284a58;       (* arm_AESE Q24 Q18 *)
  0x4e286b18;       (* arm_AESMC Q24 Q24 *)
  0x4e284a59;       (* arm_AESE Q25 Q18 *)
  0x4e286b39;       (* arm_AESMC Q25 Q25 *)
  0x4e284a60;       (* arm_AESE Q0 Q19 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284a61;       (* arm_AESE Q1 Q19 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284a78;       (* arm_AESE Q24 Q19 *)
  0x4e286b18;       (* arm_AESMC Q24 Q24 *)
  0x4e284a79;       (* arm_AESE Q25 Q19 *)
  0x4e286b39;       (* arm_AESMC Q25 Q25 *)
  0x4e284a80;       (* arm_AESE Q0 Q20 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284a81;       (* arm_AESE Q1 Q20 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284a98;       (* arm_AESE Q24 Q20 *)
  0x4e286b18;       (* arm_AESMC Q24 Q24 *)
  0x4e284a99;       (* arm_AESE Q25 Q20 *)
  0x4e286b39;       (* arm_AESMC Q25 Q25 *)
  0x4e284aa0;       (* arm_AESE Q0 Q21 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284aa1;       (* arm_AESE Q1 Q21 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284ab8;       (* arm_AESE Q24 Q21 *)
  0x4e286b18;       (* arm_AESMC Q24 Q24 *)
  0x4e284ab9;       (* arm_AESE Q25 Q21 *)
  0x4e286b39;       (* arm_AESMC Q25 Q25 *)
  0x4e284ac0;       (* arm_AESE Q0 Q22 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284ac1;       (* arm_AESE Q1 Q22 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284ad8;       (* arm_AESE Q24 Q22 *)
  0x4e286b18;       (* arm_AESMC Q24 Q24 *)
  0x4e284ad9;       (* arm_AESE Q25 Q22 *)
  0x4e286b39;       (* arm_AESMC Q25 Q25 *)
  0x4e284ae0;       (* arm_AESE Q0 Q23 *)
  0x4e284ae1;       (* arm_AESE Q1 Q23 *)
  0x4e284af8;       (* arm_AESE Q24 Q23 *)
  0x4e284af9;       (* arm_AESE Q25 Q23 *)
  0x6e271c00;       (* arm_EOR_VEC Q0 Q0 Q7 0x80 *)
  0x6e261c00;       (* arm_EOR_VEC Q0 Q0 Q6 0x80 *)
  0x6e271c21;       (* arm_EOR_VEC Q1 Q1 Q7 0x80 *)
  0x6e281c21;       (* arm_EOR_VEC Q1 Q1 Q8 0x80 *)
  0x6e271f18;       (* arm_EOR_VEC Q24 Q24 Q7 0x80 *)
  0x6e291f18;       (* arm_EOR_VEC Q24 Q24 Q9 0x80 *)
  0x6e271f39;       (* arm_EOR_VEC Q25 Q25 Q7 0x80 *)
  0x6e2a1f39;       (* arm_EOR_VEC Q25 Q25 Q10 0x80 *)
  0x4c9fa020;       (* arm_STP Q0 Q1 X1 (Postimmediate_Offset (word 0x20)) *)
  0x4c9fa038;       (* arm_STP Q24 Q25 X1 (Postimmediate_Offset (word 0x20)) *)
  0x9e660149;       (* arm_FMOV_FtoI X9 Q10 0x0 0x40 *)
  0x9eae014a;       (* arm_FMOV_FtoI X10 Q10 0x1 0x40 *)
  0x93ca8156;       (* arm_ROR X22 X10 0x20 *)
  0x93c9fd4a;       (* arm_EXTR X10 X10 X9 0x3f *)
  0x0a967e6b;       (* arm_AND W11 W19 (Shiftedreg W22 ASR 0x1f) *)
  0xca090569;       (* arm_EOR X9 X11 (Shiftedreg X9 LSL 0x1) *)
  0x9e670126;       (* arm_FMOV_ItoF Q6 X9 0x0 *)
  0x9eaf0146;       (* arm_FMOV_ItoF Q6 X10 0x1 *)
  0x140000da;       (* arm_B (word 0x368) *)
  0xd503201f;       (* arm_NOP *)
  0x4cdfa000;       (* arm_LDP Q0 Q1 X0 (Postimmediate_Offset (word 0x20)) *)
  0x4cdf7018;       (* arm_LDR Q24 X0 (Postimmediate_Offset (word 0x10)) *)
  0x6e261c00;       (* arm_EOR_VEC Q0 Q0 Q6 0x80 *)
  0x6e281c21;       (* arm_EOR_VEC Q1 Q1 Q8 0x80 *)
  0x6e291f18;       (* arm_EOR_VEC Q24 Q24 Q9 0x80 *)
  0x4e284a00;       (* arm_AESE Q0 Q16 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284a01;       (* arm_AESE Q1 Q16 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284a18;       (* arm_AESE Q24 Q16 *)
  0x4e286b18;       (* arm_AESMC Q24 Q24 *)
  0x4e284a20;       (* arm_AESE Q0 Q17 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284a21;       (* arm_AESE Q1 Q17 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284a38;       (* arm_AESE Q24 Q17 *)
  0x4e286b18;       (* arm_AESMC Q24 Q24 *)
  0x4e284980;       (* arm_AESE Q0 Q12 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284981;       (* arm_AESE Q1 Q12 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284998;       (* arm_AESE Q24 Q12 *)
  0x4e286b18;       (* arm_AESMC Q24 Q24 *)
  0x4e2849a0;       (* arm_AESE Q0 Q13 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e2849a1;       (* arm_AESE Q1 Q13 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e2849b8;       (* arm_AESE Q24 Q13 *)
  0x4e286b18;       (* arm_AESMC Q24 Q24 *)
  0x4e2849c0;       (* arm_AESE Q0 Q14 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e2849c1;       (* arm_AESE Q1 Q14 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e2849d8;       (* arm_AESE Q24 Q14 *)
  0x4e286b18;       (* arm_AESMC Q24 Q24 *)
  0x4e2849e0;       (* arm_AESE Q0 Q15 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e2849e1;       (* arm_AESE Q1 Q15 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e2849f8;       (* arm_AESE Q24 Q15 *)
  0x4e286b18;       (* arm_AESMC Q24 Q24 *)
  0x4e284880;       (* arm_AESE Q0 Q4 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284881;       (* arm_AESE Q1 Q4 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284898;       (* arm_AESE Q24 Q4 *)
  0x4e286b18;       (* arm_AESMC Q24 Q24 *)
  0x4e2848a0;       (* arm_AESE Q0 Q5 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e2848a1;       (* arm_AESE Q1 Q5 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e2848b8;       (* arm_AESE Q24 Q5 *)
  0x4e286b18;       (* arm_AESMC Q24 Q24 *)
  0x4e284a40;       (* arm_AESE Q0 Q18 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284a41;       (* arm_AESE Q1 Q18 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284a58;       (* arm_AESE Q24 Q18 *)
  0x4e286b18;       (* arm_AESMC Q24 Q24 *)
  0x4e284a60;       (* arm_AESE Q0 Q19 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284a61;       (* arm_AESE Q1 Q19 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284a78;       (* arm_AESE Q24 Q19 *)
  0x4e286b18;       (* arm_AESMC Q24 Q24 *)
  0x4e284a80;       (* arm_AESE Q0 Q20 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284a81;       (* arm_AESE Q1 Q20 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284a98;       (* arm_AESE Q24 Q20 *)
  0x4e286b18;       (* arm_AESMC Q24 Q24 *)
  0x4e284aa0;       (* arm_AESE Q0 Q21 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284aa1;       (* arm_AESE Q1 Q21 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284ab8;       (* arm_AESE Q24 Q21 *)
  0x4e286b18;       (* arm_AESMC Q24 Q24 *)
  0x4e284ac0;       (* arm_AESE Q0 Q22 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284ac1;       (* arm_AESE Q1 Q22 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284ad8;       (* arm_AESE Q24 Q22 *)
  0x4e286b18;       (* arm_AESMC Q24 Q24 *)
  0x4e284ae0;       (* arm_AESE Q0 Q23 *)
  0x4e284ae1;       (* arm_AESE Q1 Q23 *)
  0x4e284af8;       (* arm_AESE Q24 Q23 *)
  0x6e271c00;       (* arm_EOR_VEC Q0 Q0 Q7 0x80 *)
  0x6e261c00;       (* arm_EOR_VEC Q0 Q0 Q6 0x80 *)
  0x6e271c21;       (* arm_EOR_VEC Q1 Q1 Q7 0x80 *)
  0x6e281c21;       (* arm_EOR_VEC Q1 Q1 Q8 0x80 *)
  0x6e271f18;       (* arm_EOR_VEC Q24 Q24 Q7 0x80 *)
  0x6e291f18;       (* arm_EOR_VEC Q24 Q24 Q9 0x80 *)
  0x4c9fa020;       (* arm_STP Q0 Q1 X1 (Postimmediate_Offset (word 0x20)) *)
  0x4c9f7038;       (* arm_STR Q24 X1 (Postimmediate_Offset (word 0x10)) *)
  0x9e660129;       (* arm_FMOV_FtoI X9 Q9 0x0 0x40 *)
  0x9eae012a;       (* arm_FMOV_FtoI X10 Q9 0x1 0x40 *)
  0x93ca8156;       (* arm_ROR X22 X10 0x20 *)
  0x93c9fd4a;       (* arm_EXTR X10 X10 X9 0x3f *)
  0x0a967e6b;       (* arm_AND W11 W19 (Shiftedreg W22 ASR 0x1f) *)
  0xca090569;       (* arm_EOR X9 X11 (Shiftedreg X9 LSL 0x1) *)
  0x9e670126;       (* arm_FMOV_ItoF Q6 X9 0x0 *)
  0x9eaf0146;       (* arm_FMOV_ItoF Q6 X10 0x1 *)
  0x14000072;       (* arm_B (word 0x1c8) *)
  0x4cdfa000;       (* arm_LDP Q0 Q1 X0 (Postimmediate_Offset (word 0x20)) *)
  0x6e261c00;       (* arm_EOR_VEC Q0 Q0 Q6 0x80 *)
  0x6e281c21;       (* arm_EOR_VEC Q1 Q1 Q8 0x80 *)
  0x4e284a00;       (* arm_AESE Q0 Q16 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284a01;       (* arm_AESE Q1 Q16 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284a20;       (* arm_AESE Q0 Q17 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284a21;       (* arm_AESE Q1 Q17 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284980;       (* arm_AESE Q0 Q12 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284981;       (* arm_AESE Q1 Q12 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e2849a0;       (* arm_AESE Q0 Q13 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e2849a1;       (* arm_AESE Q1 Q13 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e2849c0;       (* arm_AESE Q0 Q14 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e2849c1;       (* arm_AESE Q1 Q14 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e2849e0;       (* arm_AESE Q0 Q15 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e2849e1;       (* arm_AESE Q1 Q15 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284880;       (* arm_AESE Q0 Q4 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284881;       (* arm_AESE Q1 Q4 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e2848a0;       (* arm_AESE Q0 Q5 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e2848a1;       (* arm_AESE Q1 Q5 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284a40;       (* arm_AESE Q0 Q18 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284a41;       (* arm_AESE Q1 Q18 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284a60;       (* arm_AESE Q0 Q19 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284a61;       (* arm_AESE Q1 Q19 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284a80;       (* arm_AESE Q0 Q20 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284a81;       (* arm_AESE Q1 Q20 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284aa0;       (* arm_AESE Q0 Q21 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284aa1;       (* arm_AESE Q1 Q21 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284ac0;       (* arm_AESE Q0 Q22 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284ac1;       (* arm_AESE Q1 Q22 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284ae0;       (* arm_AESE Q0 Q23 *)
  0x4e284ae1;       (* arm_AESE Q1 Q23 *)
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
  0x1400002b;       (* arm_B (word 0xac) *)

  (* Lxts_enc_tail1x: *)
  (* pc + 0x938 *)
  0x4cdf7000;       (* arm_LDR Q0 X0 (Postimmediate_Offset (word 0x10)) *)
  0x6e261c00;       (* arm_EOR_VEC Q0 Q0 Q6 0x80 *)
  0x4e284a00;       (* arm_AESE Q0 Q16 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284a20;       (* arm_AESE Q0 Q17 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284980;       (* arm_AESE Q0 Q12 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e2849a0;       (* arm_AESE Q0 Q13 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e2849c0;       (* arm_AESE Q0 Q14 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e2849e0;       (* arm_AESE Q0 Q15 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284880;       (* arm_AESE Q0 Q4 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e2848a0;       (* arm_AESE Q0 Q5 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
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
  0x14000002;       (* arm_B (word 0x8) *)
  0xd503201f;       (* arm_NOP *)

  (* Lxts_enc_done: *)
  (* pc + 0x9e0 *)
  0xf2400ebf;       (* arm_TST X21 (rvalue (word 0xf)) *)
  0x54000540;       (* arm_BEQ (word 0xa8) *)
  0xaa0003f4;       (* arm_MOV X20 X0 *)
  0xaa0103ed;       (* arm_MOV X13 X1 *)
  0xd1004021;       (* arm_SUB X1 X1 (rvalue (word 0x10)) *)
  0xf10006b5;       (* arm_SUBS X21 X21 (rvalue (word 0x1)) *)
  0x3875682f;       (* arm_LDRB W15 X1 (Register_Offset X21) *)
  0x38756a8e;       (* arm_LDRB W14 X20 (Register_Offset X21) *)
  0x383569af;       (* arm_STRB W15 X13 (Register_Offset X21) *)
  0x3835682e;       (* arm_STRB W14 X1 (Register_Offset X21) *)
  0x54ffff6c;       (* arm_BGT (word 0x1fffec) *)
  0x4c40703a;       (* arm_LDR Q26 X1 No_Offset *)
  0x6e261f5a;       (* arm_EOR_VEC Q26 Q26 Q6 0x80 *)

  0x4e284a1a;       (* arm_AESE Q26 Q16 *)
  0x4e286b5a;       (* arm_AESMC Q26 Q26 *)
  0x4e284a3a;       (* arm_AESE Q26 Q17 *)
  0x4e286b5a;       (* arm_AESMC Q26 Q26 *)
  0x4e28499a;       (* arm_AESE Q26 Q12 *)
  0x4e286b5a;       (* arm_AESMC Q26 Q26 *)
  0x4e2849ba;       (* arm_AESE Q26 Q13 *)
  0x4e286b5a;       (* arm_AESMC Q26 Q26 *)
  0x4e2849da;       (* arm_AESE Q26 Q14 *)
  0x4e286b5a;       (* arm_AESMC Q26 Q26 *)
  0x4e2849fa;       (* arm_AESE Q26 Q15 *)
  0x4e286b5a;       (* arm_AESMC Q26 Q26 *)
  0x4e28489a;       (* arm_AESE Q26 Q4 *)
  0x4e286b5a;       (* arm_AESMC Q26 Q26 *)
  0x4e2848ba;       (* arm_AESE Q26 Q5 *)
  0x4e286b5a;       (* arm_AESMC Q26 Q26 *)
  0x4e284a5a;       (* arm_AESE Q26 Q18 *)
  0x4e286b5a;       (* arm_AESMC Q26 Q26 *)
  0x4e284a7a;       (* arm_AESE Q26 Q19 *)
  0x4e286b5a;       (* arm_AESMC Q26 Q26 *)
  0x4e284a9a;       (* arm_AESE Q26 Q20 *)
  0x4e286b5a;       (* arm_AESMC Q26 Q26 *)
  0x4e284aba;       (* arm_AESE Q26 Q21 *)
  0x4e286b5a;       (* arm_AESMC Q26 Q26 *)
  0x4e284ada;       (* arm_AESE Q26 Q22 *)
  0x4e286b5a;       (* arm_AESMC Q26 Q26 *)
  0x4e284afa;       (* arm_AESE Q26 Q23 *)
  0x6e271f5a;       (* arm_EOR_VEC Q26 Q26 Q7 0x80 *)

  0x6e261f5a;       (* arm_EOR_VEC Q26 Q26 Q6 0x80 *)
  0x4c00703a;       (* arm_STR Q26 X1 No_Offset *)
  0xa94053f3;       (* arm_LDP X19 X20 SP (Immediate_Offset (iword (&0x0))) *)
  0xa9415bf5;       (* arm_LDP X21 X22 SP (Immediate_Offset (iword (&0x10))) *)
  0x6d4227e8;       (* arm_LDP D8 D9 SP (Immediate_Offset (iword (&0x20))) *)
  0x6d432fea;       (* arm_LDP D10 D11 SP (Immediate_Offset (iword (&0x30))) *)
  0x6d4437ec;       (* arm_LDP D12 D13 SP (Immediate_Offset (iword (&0x40))) *)
  0x6d453fee;       (* arm_LDP D14 D15 SP (Immediate_Offset (iword (&0x50))) *)
  0x910183ff;       (* arm_ADD SP SP (rvalue (word 0x60)) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let AES256_XTS_ENCRYPT_EXEC = ARM_MK_EXEC_RULE aes256_xts_encrypt_mc;;

(**********************************************************************)
(**                    Encrypt-specific lemmas                       **)

let LENGTH_OF_AES256_XTS_ENCRYPT_REC = prove(
  `!(i:num) (m:num) (P:byte list) (iv:int128) (key1:int128 list) (key2:int128 list).
    LENGTH(aes256_xts_encrypt_rec i m P iv key1 key2) = (if m < i then 0 else (m - i + 1) * 0x10)`,
    REPEAT GEN_TAC THEN
    (* Wellfounded induction with measure (m + 1) - i
       Note that the parentheses are essential because of the precedence of + and - *)
    WF_INDUCT_TAC `(m + 1) - i` THEN
    ONCE_REWRITE_TAC[aes256_xts_encrypt_rec] THEN
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

let LENGTH_OF_FST_OF_ENC_CIPHER_STEALING = prove(
  `!(block:byte list) (tail:byte list) (tail_len:num)
    (iv:int128) (i:num) (key1:int128 list) (key2:int128 list).
  LENGTH (FST (cipher_stealing_encrypt block tail tail_len iv i key1 key2)) = 16`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[cipher_stealing_encrypt] THEN
  ASM_REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  REWRITE_TAC[LENGTH_OF_INT128_TO_BYTES]
);;

let LENGTH_OF_SND_OF_ENC_CIPHER_STEALING = prove(
  `!(block:byte list) (tail:byte list) (tail_len:num)
    (iv:int128) (i:num) (key1:int128 list) (key2:int128 list).
  LENGTH (SND (cipher_stealing_encrypt block tail tail_len iv i key1 key2)) = MIN tail_len 16`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[cipher_stealing_encrypt] THEN
  ASM_REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  REWRITE_TAC[LENGTH_SUB_LIST] THEN
  REWRITE_TAC[LENGTH_OF_INT128_TO_BYTES] THEN
  REWRITE_TAC[MIN] THEN
  CONV_TAC NUM_REDUCE_CONV
);;

let LENGTH_OF_AES256_XTS_ENCRYPT_TAIL = prove(
  `! (i:num) (tail_len:num) (P:byte list) (iv:int128) (key1:int128 list) (key2:int128 list).
  LENGTH(aes256_xts_encrypt_tail i tail_len P iv key1 key2) = 0x10 + MIN tail_len 16`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[aes256_xts_encrypt_tail] THEN
  COND_CASES_TAC THENL [
    ASM_REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
    REWRITE_TAC[LENGTH_OF_INT128_TO_BYTES] THEN
    REWRITE_TAC[ADD_CLAUSES; MIN] THEN
    CONV_TAC NUM_REDUCE_CONV;

    REWRITE_TAC[LET_DEF; LET_END_DEF; LENGTH_APPEND] THEN
    REWRITE_TAC[LENGTH_OF_FST_OF_ENC_CIPHER_STEALING] THEN
    REWRITE_TAC[LENGTH_OF_SND_OF_ENC_CIPHER_STEALING]]
);;

let LENGTH_OF_AES256_XTS_ENCRYPT_REC_TRIVIAL = prove(
  `!(pt:byte list) (iv:int128) (key1:int128 list) (key2:int128 list).
   LENGTH (aes256_xts_encrypt_rec 0x0 0x0 pt iv key1 key2) = 16`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[LENGTH_OF_AES256_XTS_ENCRYPT_REC] THEN
  CONV_TAC NUM_REDUCE_CONV
);;

let LENGTH_OF_AES256_XTS_ENCRYPT_TAIL_TRIVIAL = prove(
  `!(pt:byte list) (iv:int128) (key1:int128 list) (key2:int128 list).
  LENGTH(aes256_xts_encrypt_tail 0 0 pt iv key1 key2) = 16`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[LENGTH_OF_AES256_XTS_ENCRYPT_TAIL] THEN
  CONV_TAC NUM_REDUCE_CONV
);;

let AES256_XTS_ENCRYPT_REC_EQ_TAIL_TRIVIAL = prove(
  `!(pt:byte list) (iv:int128) (key1:int128 list) (key2:int128 list).
   aes256_xts_encrypt_rec 0x0 0x0 ct iv key1 key2 =
   aes256_xts_encrypt_tail 0x0 0x0 ct iv key1 key2`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[aes256_xts_encrypt_rec] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  ONCE_REWRITE_TAC[aes256_xts_encrypt_rec] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[APPEND_NIL] THEN

  REWRITE_TAC[aes256_xts_encrypt_tail] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  CONV_TAC NUM_REDUCE_CONV
);;

let LENGTH_OF_AES256_XTS_ENCRYPT_FULL_BLOCKS = prove(
  `! (i:num) (pt:byte list) (iv:int128) (key1:int128 list) (key2:int128 list).
  LENGTH(aes256_xts_encrypt pt (0x10 * i) iv key1 key2) = 0x10 * i`,
  REPEAT STRIP_TAC THEN
  SPEC_TAC (`i:num`, `i:num`) THEN
  INDUCT_TAC THENL
  [
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[aes256_xts_encrypt] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[LENGTH_EQ_NIL];
    ALL_TAC] THEN

  REWRITE_TAC[ADD1; LEFT_ADD_DISTRIB] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[aes256_xts_encrypt] THEN

  ASM_CASES_TAC `i = 0` THENL
  [ ASM_SIMP_TAC[] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    IMP_REWRITE_TAC[LET_DEF;LET_END_DEF;SUB_0] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[LENGTH_OF_AES256_XTS_ENCRYPT_TAIL_TRIVIAL]
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
  REWRITE_TAC[LENGTH_OF_AES256_XTS_ENCRYPT_REC] THEN
  REWRITE_TAC[LENGTH_OF_AES256_XTS_ENCRYPT_TAIL] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ASM_ARITH_TAC
);;

let LENGTH_OF_AES256_XTS_ENCRYPT = prove(
  `! (i:num) (tail_len:num) (pt:byte list) (iv:int128) (key1:int128 list) (key2:int128 list).
  ~(tail_len = 0) /\ tail_len < 16 ==>
  LENGTH(aes256_xts_encrypt pt (16 * i + 16 + tail_len) iv key1 key2) = 16 * i + 16 + tail_len`,
  REPEAT STRIP_TAC THEN
  (* Case 1: i = 0 *)
  ASM_CASES_TAC `i = 0` THENL
  [
    ASM_SIMP_TAC[ADD_ASSOC] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[aes256_xts_encrypt] THEN
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
    REWRITE_TAC[LENGTH_OF_AES256_XTS_ENCRYPT_TAIL] THEN
    ASM_ARITH_TAC;
    ALL_TAC
  ] THEN

  (* Case 2: i >= 1 *)
  ASM_CASES_TAC `i >= 1` THENL
  [
    REWRITE_TAC[aes256_xts_encrypt] THEN
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
    IMP_REWRITE_TAC[LENGTH_OF_AES256_XTS_ENCRYPT_REC] THEN
    IMP_REWRITE_TAC[LENGTH_OF_AES256_XTS_ENCRYPT_TAIL] THEN
    ASM_ARITH_TAC;
    ALL_TAC
  ] THEN

  ASM_ARITH_TAC
);;

let AES256_XTS_ENCRYPT_TAIL_WHEN_1BLOCK = prove(
  `!(n:num) (pt:byte list) (iv:int128) (key1:int128 list) (key2:int128 list).
   bytes_to_int128
     (aes256_xts_encrypt_tail n 0x0 pt iv key1 key2) =
   aes256_xts_encrypt_round
     (bytes_to_int128 (SUB_LIST (n * 0x10,0x10) pt))
     (calculate_tweak n iv key2) key1`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[aes256_xts_encrypt_tail] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  REWRITE_TAC[BYTES_TO_INT128_OF_INT128_TO_BYTES]
);;

let AES256_XTS_ENCRYPT_REC_EQ_TAIL = prove(
  `!(i:num) (k:num) (pt:byte list) (iv:int128) (key1:int128 list) (key2:int128 list).
  k >= i ==>
  aes256_xts_encrypt_rec i (k + 1) pt iv key1 key2 =
  APPEND (aes256_xts_encrypt_rec i k pt iv key1 key2)
         (aes256_xts_encrypt_tail (k + 1) 0x0 pt iv key1 key2)`,
  REPEAT GEN_TAC THEN
  WF_INDUCT_TAC `(k + 1) - i` THEN
  STRIP_TAC THEN
  GEN_REWRITE_TAC (RATOR_CONV o ONCE_DEPTH_CONV) [aes256_xts_encrypt_rec] THEN
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
    GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [aes256_xts_encrypt_rec] THEN
    SUBGOAL_THEN `~(k < i)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN
    REWRITE_TAC[LET_DEF; LET_END_DEF]; ALL_TAC
  ] THEN
  SUBGOAL_THEN `k:num = i` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[aes256_xts_encrypt_rec] THEN
  REWRITE_TAC[LT_REFL; LET_DEF; LET_END_DEF] THEN
  ONCE_REWRITE_TAC[aes256_xts_encrypt_rec] THEN
  REWRITE_TAC[ARITH_RULE `i < i + 1`; APPEND_NIL] THEN
  AP_TERM_TAC THEN
  REWRITE_TAC[aes256_xts_encrypt_tail; LET_DEF; LET_END_DEF]
);;

let SUB_LIST_OF_AES256_XTS_ENCRYPT_FULL_BLOCKS = prove(
  `!(i:num) (pt:byte list) (iv:int128) (key1:int128 list) (key2:int128 list).
    (SUB_LIST (0,16 * i)
      (aes256_xts_encrypt pt (16 * i + 16) iv key1 key2))
    = aes256_xts_encrypt pt (16 * i) iv key1 key2`,
  REPEAT STRIP_TAC THEN

  (* when i = 0, trivial *)
  ASM_CASES_TAC `i = 0` THENL
  [
    ASM_REWRITE_TAC[] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[CONJUNCT1 SUB_LIST; aes256_xts_encrypt] THEN
    CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC
  ] THEN

  (* when i = 1, using aes256_xts_encrypt_tail *)
  ASM_CASES_TAC `i = 1` THENL
  [
    ASM_REWRITE_TAC[] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[aes256_xts_encrypt] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    MP_TAC (SPECL [`pt:byte list`; `iv:int128`; `key1: int128 list`; `key2: int128 list`]
      LENGTH_OF_AES256_XTS_ENCRYPT_REC_TRIVIAL) THEN
    DISCH_TAC THEN
    IMP_REWRITE_TAC[SUB_LIST_APPEND_LEFT] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    IMP_REWRITE_TAC[SUB_LIST_LENGTH_IMPLIES] THEN
    REWRITE_TAC[AES256_XTS_ENCRYPT_REC_EQ_TAIL_TRIVIAL];
    ALL_TAC
  ] THEN

  (* when i >= 2, using aes256_xts_encrypt_rec *)
  REWRITE_TAC[aes256_xts_encrypt] THEN
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
  SUBGOAL_THEN `LENGTH (aes256_xts_encrypt_rec 0x0 (i - 0x1) pt iv key1 key2) = 16 * i` ASSUME_TAC THENL
  [ REWRITE_TAC[LENGTH_OF_AES256_XTS_ENCRYPT_REC] THEN
    ASM_ARITH_TAC; ALL_TAC] THEN
  IMP_REWRITE_TAC[SUB_LIST_APPEND_LEFT; SUB_LIST_LENGTH_IMPLIES] THEN
  CONJ_TAC THENL [ALL_TAC; ARITH_TAC] THEN
  SUBGOAL_THEN `i - 1 = i - 2 + 1` ASSUME_TAC THENL
  [ ASM_ARITH_TAC; ALL_TAC ] THEN
  ASM_REWRITE_TAC[] THEN
  IMP_REWRITE_TAC[AES256_XTS_ENCRYPT_REC_EQ_TAIL] THEN
  ASM_ARITH_TAC
);;

let SUB_LIST_OF_AES256_XTS_ENCRYPT = prove(
  `!(i:num) (tail_len:num) (pt:byte list) (iv:int128) (key1:int128 list) (key2:int128 list).
    ~(tail_len = 0) /\ tail_len < 16 ==>
    (SUB_LIST (0,16 * i)
      (aes256_xts_encrypt pt (16 * i + 16 + tail_len) iv key1 key2))
    = aes256_xts_encrypt pt (16 * i) iv key1 key2`,
  REPEAT STRIP_TAC THEN
  (* Case 1: i = 0 *)
  ASM_CASES_TAC `i = 0` THENL
  [
    ASM_REWRITE_TAC[] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[ADD; SUB_LIST_CLAUSES; aes256_xts_encrypt] THEN
    CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC
  ] THEN
  (* Case 2: i = 1 *)
  ASM_CASES_TAC `i = 1` THENL
  [
    ASM_REWRITE_TAC[] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[aes256_xts_encrypt; ADD_ASSOC] THEN
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
    MP_TAC (SPECL [`pt:byte list`; `iv:int128`; `key1:int128 list`; `key2:int128 list`] LENGTH_OF_AES256_XTS_ENCRYPT_REC_TRIVIAL) THEN
    DISCH_TAC THEN IMP_REWRITE_TAC[SUB_LIST_APPEND_LEFT] THEN
    REWRITE_TAC[AES256_XTS_ENCRYPT_REC_EQ_TAIL_TRIVIAL] THEN
    MP_TAC (SPECL [`pt:byte list`; `iv:int128`; `key1:int128 list`; `key2:int128 list`] LENGTH_OF_AES256_XTS_ENCRYPT_TAIL_TRIVIAL) THEN
    DISCH_TAC THEN IMP_REWRITE_TAC[SUB_LIST_LENGTH_IMPLIES] THEN
    ARITH_TAC;
    ALL_TAC
  ] THEN

  (* Case 3: i >= 2 *)
  ASM_CASES_TAC `i >= 2` THENL
  [
    ASM_REWRITE_TAC[ADD_ASSOC] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[aes256_xts_encrypt] THEN
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
    MP_TAC (SPECL [`0:num`; `(i - 1):num`; `pt:byte list`; `iv:int128`;
      `key1:int128 list`; `key2:int128 list`] LENGTH_OF_AES256_XTS_ENCRYPT_REC) THEN
    SUBGOAL_THEN `~((i - 1) < 0)` ASSUME_TAC THENL [ ASM_ARITH_TAC; ALL_TAC] THEN
    IMP_REWRITE_TAC[ARITH_RULE `i >= 2 ==> i - 0x1 - 0x0 + 0x1 = i`] THEN
    IMP_REWRITE_TAC[SUB_LIST_APPEND_LEFT] THEN
    SIMP_TAC[ARITH_RULE `16 * i <= i * 16`] THEN
    IMP_REWRITE_TAC[SUB_LIST_LENGTH_IMPLIES] THEN
    SIMP_TAC[ARITH_RULE `i * 16 = 16 * i`] THEN
    DISCH_TAC THEN
    MP_TAC (SPECL [`0`; `(i-2):num`; `pt:byte list`; `iv:int128`;
      `key1:int128 list`; `key2:int128 list`] AES256_XTS_ENCRYPT_REC_EQ_TAIL) THEN
    ANTS_TAC THENL [ ASM_ARITH_TAC; ALL_TAC ] THEN
    IMP_REWRITE_TAC[ARITH_RULE `i >= 2 ==> i - 0x2 + 0x1 = i - 1`];
    ALL_TAC
  ] THEN

  ASM_ARITH_TAC
);;

let READ_BYTES_EQ_READ_BYTE128_1BLOCK_ENC = prove(
  `!(ptr:int64) (ct:byte list) (iv:int128) (key1:int128 list) (key2:int128 list) s.
    (read (memory :> bytes128 pt_ptr) s =
      aes256_xts_encrypt_round (bytes_to_int128 (SUB_LIST (0x0,0x10) ct))
      (calculate_tweak 0x0 iv key2)
      key1) ==>
    read (memory :> bytes (pt_ptr,0x10)) s =
      num_of_bytelist (SUB_LIST (0x0,0x10) (aes256_xts_encrypt ct 0x10 iv key1 key2))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[READ_MEMORY_BYTES_BYTES128] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[aes256_xts_encrypt] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[aes256_xts_encrypt_tail] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[SUB_LIST_OF_INT128_TO_BYTES] THEN
  REWRITE_TAC[NUM_OF_BYTELIST_OF_INT128_TO_BYTES]
);;

let READ_BYTES_EQ_READ_BYTE128_2BLOCKS_ENC = prove(
  `!(ptr:int64) (ct:byte list) (iv:int128) (key1:int128 list) (key2:int128 list) s.
    (read (memory :> bytes128 pt_ptr) s =
      aes256_xts_encrypt_round (bytes_to_int128 (SUB_LIST (0x0,0x10) ct))
      (calculate_tweak 0x0 iv key2)
      key1) ==>
    (read (memory :> bytes128 (word_add pt_ptr (word 0x10))) s =
      aes256_xts_encrypt_round (bytes_to_int128 (SUB_LIST (0x10,0x10) ct))
      (calculate_tweak 0x1 iv key2)
      key1) ==>
    read (memory :> bytes (pt_ptr,0x20)) s =
      num_of_bytelist (SUB_LIST (0x0,0x20) (aes256_xts_encrypt ct 0x20 iv key1 key2))`,
  REPEAT STRIP_TAC THEN
  IMP_REWRITE_TAC[ARITH_RULE `0x20 = 0x10 + 0x10`; READ_BYTES_AND_BYTE128_SPLIT] THEN
  EXISTS_TAC `aes256_xts_encrypt ct 0x20 iv key1 key2` THEN
  REPEAT CONJ_TAC THENL
  [
    CONV_TAC NUM_REDUCE_CONV;

    MP_TAC (SPECL [`2:num`; `ct:byte list`; `iv:int128`; `key1:int128 list`; `key2:int128 list`]
      LENGTH_OF_AES256_XTS_ENCRYPT_FULL_BLOCKS) THEN
    ARITH_TAC;

    REWRITE_TAC[aes256_xts_encrypt] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    MP_TAC (SPECL [`ct:byte list`; `iv:int128`; `key1:int128 list`; `key2:int128 list`]
      LENGTH_OF_AES256_XTS_ENCRYPT_REC_TRIVIAL) THEN
    IMP_REWRITE_TAC[SUB_LIST_APPEND_RIGHT_LEMMA] THEN DISCH_TAC THEN
    REWRITE_TAC[aes256_xts_encrypt_tail] THEN
    REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
    REWRITE_TAC[SUB_LIST_OF_INT128_TO_BYTES] THEN
    REWRITE_TAC[NUM_OF_BYTELIST_OF_INT128_TO_BYTES] THEN
    REWRITE_TAC[BYTES_TO_INT128_OF_INT128_TO_BYTES] THEN
    CONV_TAC NUM_REDUCE_CONV;

    MP_TAC (SPECL [`1:num`; `ct:byte list`; `iv:int128`; `key1:int128 list`; `key2:int128 list`]
      SUB_LIST_OF_AES256_XTS_ENCRYPT_FULL_BLOCKS) THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    SIMP_TAC[] THEN DISCH_TAC THEN
    IMP_REWRITE_TAC[READ_BYTES_EQ_READ_BYTE128_1BLOCK_ENC] THEN
    MP_TAC (SPECL [`1:num`; `ct:byte list`; `iv:int128`; `key1:int128 list`; `key2:int128 list`]
      LENGTH_OF_AES256_XTS_ENCRYPT_FULL_BLOCKS) THEN
    CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
    IMP_REWRITE_TAC[SUB_LIST_LENGTH_IMPLIES]
  ]
);;

let READ_BYTES_EQ_READ_BYTE128_3BLOCKS_ENC = prove(
  `!(ptr:int64) (ct:byte list) (iv:int128) (key1:int128 list) (key2:int128 list) s.
    (read (memory :> bytes128 pt_ptr) s =
      aes256_xts_encrypt_round (bytes_to_int128 (SUB_LIST (0x0,0x10) ct))
      (calculate_tweak 0x0 iv key2)
      key1) ==>
    (read (memory :> bytes128 (word_add pt_ptr (word 0x10))) s =
      aes256_xts_encrypt_round (bytes_to_int128 (SUB_LIST (0x10,0x10) ct))
      (calculate_tweak 0x1 iv key2)
      key1) ==>
    (read (memory :> bytes128 (word_add pt_ptr (word 0x20))) s =
      aes256_xts_encrypt_round (bytes_to_int128 (SUB_LIST (0x20,0x10) ct))
      (calculate_tweak 0x2 iv key2)
      key1) ==>
    read (memory :> bytes (pt_ptr,0x30)) s =
      num_of_bytelist (SUB_LIST (0x0,0x30) (aes256_xts_encrypt ct 0x30 iv key1 key2))`,
  REPEAT STRIP_TAC THEN
  IMP_REWRITE_TAC[ARITH_RULE `0x30 = 0x20 + 0x10`; READ_BYTES_AND_BYTE128_SPLIT] THEN
  EXISTS_TAC `aes256_xts_encrypt ct 0x30 iv key1 key2` THEN
  REPEAT CONJ_TAC THENL
  [
    CONV_TAC NUM_REDUCE_CONV;

    MP_TAC (SPECL [`3:num`; `ct:byte list`; `iv:int128`; `key1:int128 list`; `key2:int128 list`]
      LENGTH_OF_AES256_XTS_ENCRYPT_FULL_BLOCKS) THEN
    ARITH_TAC;

    REWRITE_TAC[aes256_xts_encrypt] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    MP_TAC (SPECL [`0:num`; `1:num`; `ct:byte list`; `iv:int128`; `key1:int128 list`; `key2:int128 list`]
      LENGTH_OF_AES256_XTS_ENCRYPT_REC) THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    IMP_REWRITE_TAC[SUB_LIST_APPEND_RIGHT_LEMMA] THEN DISCH_TAC THEN
    REWRITE_TAC[aes256_xts_encrypt_tail] THEN
    REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
    REWRITE_TAC[SUB_LIST_OF_INT128_TO_BYTES] THEN
    REWRITE_TAC[NUM_OF_BYTELIST_OF_INT128_TO_BYTES] THEN
    REWRITE_TAC[BYTES_TO_INT128_OF_INT128_TO_BYTES] THEN
    CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN

  MP_TAC (SPECL [`2:num`; `ct:byte list`; `iv:int128`; `key1:int128 list`; `key2:int128 list`]
    SUB_LIST_OF_AES256_XTS_ENCRYPT_FULL_BLOCKS) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SIMP_TAC[] THEN DISCH_TAC THEN
  IMP_REWRITE_TAC[READ_BYTES_EQ_READ_BYTE128_2BLOCKS_ENC] THEN
  MP_TAC (SPECL [`2:num`; `ct:byte list`; `iv:int128`; `key1:int128 list`; `key2:int128 list`]
    LENGTH_OF_AES256_XTS_ENCRYPT_FULL_BLOCKS) THEN
  CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
  IMP_REWRITE_TAC[SUB_LIST_LENGTH_IMPLIES]
);;

let READ_BYTES_EQ_READ_BYTE128_4BLOCKS_ENC = prove(
  `!(ptr:int64) (ct:byte list) (iv:int128) (key1:int128 list) (key2:int128 list) s.
    (read (memory :> bytes128 pt_ptr) s =
      aes256_xts_encrypt_round (bytes_to_int128 (SUB_LIST (0x0,0x10) ct))
      (calculate_tweak 0x0 iv key2)
      key1) ==>
    (read (memory :> bytes128 (word_add pt_ptr (word 0x10))) s =
      aes256_xts_encrypt_round (bytes_to_int128 (SUB_LIST (0x10,0x10) ct))
      (calculate_tweak 0x1 iv key2)
      key1) ==>
    (read (memory :> bytes128 (word_add pt_ptr (word 0x20))) s =
      aes256_xts_encrypt_round (bytes_to_int128 (SUB_LIST (0x20,0x10) ct))
      (calculate_tweak 0x2 iv key2)
      key1) ==>
    (read (memory :> bytes128 (word_add pt_ptr (word 0x30))) s =
      aes256_xts_encrypt_round (bytes_to_int128 (SUB_LIST (0x30,0x10) ct))
      (calculate_tweak 0x3 iv key2)
      key1) ==>
    read (memory :> bytes (pt_ptr,0x40)) s =
      num_of_bytelist (SUB_LIST (0x0,0x40) (aes256_xts_encrypt ct 0x40 iv key1 key2))`,
  REPEAT STRIP_TAC THEN
  IMP_REWRITE_TAC[ARITH_RULE `0x40 = 0x30 + 0x10`; READ_BYTES_AND_BYTE128_SPLIT] THEN
  EXISTS_TAC `aes256_xts_encrypt ct 0x40 iv key1 key2` THEN
  REPEAT CONJ_TAC THENL
  [
    CONV_TAC NUM_REDUCE_CONV;

    MP_TAC (SPECL [`4:num`; `ct:byte list`; `iv:int128`; `key1:int128 list`; `key2:int128 list`]
      LENGTH_OF_AES256_XTS_ENCRYPT_FULL_BLOCKS) THEN
    ARITH_TAC;

    REWRITE_TAC[aes256_xts_encrypt] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    MP_TAC (SPECL [`0:num`; `2:num`; `ct:byte list`; `iv:int128`; `key1:int128 list`; `key2:int128 list`]
      LENGTH_OF_AES256_XTS_ENCRYPT_REC) THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    IMP_REWRITE_TAC[SUB_LIST_APPEND_RIGHT_LEMMA] THEN DISCH_TAC THEN
    REWRITE_TAC[aes256_xts_encrypt_tail] THEN
    REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
    REWRITE_TAC[SUB_LIST_OF_INT128_TO_BYTES] THEN
    REWRITE_TAC[BYTES_TO_INT128_OF_INT128_TO_BYTES] THEN
    CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN

  MP_TAC (SPECL [`3:num`; `ct:byte list`; `iv:int128`; `key1:int128 list`; `key2:int128 list`]
    SUB_LIST_OF_AES256_XTS_ENCRYPT_FULL_BLOCKS) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SIMP_TAC[] THEN DISCH_TAC THEN
  IMP_REWRITE_TAC[READ_BYTES_EQ_READ_BYTE128_3BLOCKS_ENC] THEN
  MP_TAC (SPECL [`3:num`; `ct:byte list`; `iv:int128`; `key1:int128 list`; `key2:int128 list`]
    LENGTH_OF_AES256_XTS_ENCRYPT_FULL_BLOCKS) THEN
  CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
  IMP_REWRITE_TAC[SUB_LIST_LENGTH_IMPLIES]
);;


(**********************************************************************)
(**                           Tactics                                **)

let AESENC_TAC =
  REWRITE_TAC [aes256_encrypt] THEN
  REWRITE_TAC EL_15_128_CLAUSES THEN
  REWRITE_TAC [aes256_encrypt_round; aese; aesmc] THEN
  CONV_TAC (TOP_DEPTH_CONV let_CONV) THEN
  BITBLAST_TAC;;

let AESXTS_ENC_ONE_BLOCK_TAC =
  REWRITE_TAC [aes256_xts_encrypt_1block] THEN
  REWRITE_TAC [xts_init_tweak; aes256_xts_encrypt_round] THEN
  CONV_TAC (TOP_DEPTH_CONV let_CONV) THEN
  GEN_REWRITE_TAC LAND_CONV [WORD_XOR_SYM] THEN
  REPEAT (AP_THM_TAC THEN AP_TERM_TAC) THEN
  BITBLAST_TAC;;

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

(* differs from the Decrypt definition in using key2_lst instead of key2
   TODO: it seems that value of indm1 doesn't matter to the tactic, can it be removed? *)
let TWEAK_TAC reg ind indm1 =
  let lower_term = subst [ind,`ind:num`] `(word_zx:int128->int64) (calculate_tweak ind iv key2_lst)` in
  let upper_term = subst [ind,`ind:num`] `(word_subword:int128->num#num->int64) (calculate_tweak ind iv key2_lst) (64,64)` in
  let full_term = subst [ind,`ind:num`] `calculate_tweak ind iv key2_lst` in
  let full_lemma = subst [reg,`reg:(armstate,int128)component`] `read (reg:(armstate,int128)component) (s:armstate) = a ==> !a'. a = a' ==> read reg s = a'` in
  let abbrev_term = subst [indm1,`indm1:num`] `tweak_pre:int128 = (calculate_tweak indm1 iv key2_lst)` in
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

let XTSENC_TAC reg ind ind_tweak =
  let tm = subst [ind, `ind:num`; ind_tweak, `ind_tweak:num`]
            `aes256_xts_encrypt_round (bytes_to_int128 (SUB_LIST (ind,0x10) (pt_in:byte list)))
              (calculate_tweak (ind_tweak) iv key2_lst) key1_lst` in
  let lemma = subst [reg, `reg:(armstate,int128)component`]
            `read (reg:(armstate,int128)component) (s:armstate) = a ==> !a'. a = a' ==> read reg s = a'` in
  FIRST_X_ASSUM(MP_TAC o SPEC tm o  MATCH_MP (MESON[] lemma)) THEN
      ANTS_TAC THENL
      [ EXPAND_TAC "key1_lst" THEN
        CONV_TAC (RAND_CONV (
          REWRITE_CONV [aes256_xts_encrypt_round] THENC
          DEPTH_CONV let_CONV)) THEN
        GEN_REWRITE_TAC LAND_CONV [WORD_XOR_SYM] THEN
        REPEAT (AP_THM_TAC THEN AP_TERM_TAC) THEN
        GEN_REWRITE_TAC ONCE_DEPTH_CONV [WORD_XOR_SYM] THEN
        AESENC_TAC; DISCH_TAC ];;

let ENC_TAIL_SWAP_CASE_0_TAC =
      POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th]) THEN
      (* Simplify so that symbolic execution could match up, but couldn't use
      CONV_TAC NUM_REDUCE_CONV because of non-overlapping *)

      RULE_ASSUM_TAC(REWRITE_RULE[ADD_0]) THEN

      ARM_ACCSTEPS_TAC AES256_XTS_ENCRYPT_EXEC [] (1--5) THEN

      RULE_ASSUM_TAC(REWRITE_RULE[GSYM ADD_ASSOC]) THEN
      RULE_ASSUM_TAC (CONV_RULE NUM_REDUCE_CONV) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN

      REPEAT CONJ_TAC THENL
      [ MATCH_MP_TAC (snd (EQ_IMP_RULE (SPECL [`(word_add ctxt_p (word l1_curr_len)):int64`; `s5:armstate`;
                                               `(cipher_stealing_inv 0x0 l1_curr_len (val (tail_len:int64)) CC pt_in):int128`]
                           BREAK_ONE_BLOCK_INTO_BYTES))) THEN
        CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
        ASM_REWRITE_TAC[] THEN

        MP_TAC (SPECL [`0x0`; `l1_curr_len:num`; `tail_len:int64`; `CC:int128`; `pt_in:byte list`]
                  CIPHER_STEALING_BYTE_EQUAL) THEN
        CHANGED_TAC(CONV_TAC NUM_REDUCE_CONV) THEN
        REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
        ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN

        ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
        STRIP_TAC THEN

        (* The case for 0 needed to be separated out and simplified from CIPHER_STEALING_INV_SIMP_TAC *)
        CONJ_TAC THENL
        [ ASM_REWRITE_TAC[] THEN
          IMP_REWRITE_TAC[WORD_ZX_ZX; WORD_ZX_TRIVIAL] THEN
          REWRITE_TAC[DIMINDEX_8; DIMINDEX_32; DIMINDEX_64] THEN
          ASM_ARITH_TAC ; ALL_TAC] THEN

        MAP_EVERY (fun i -> CONJ_TAC THENL
          [CIPHER_STEALING_INV_SIMP_TAC (mk_numeral (num i)); ALL_TAC]) (1--0xe) THEN
        CIPHER_STEALING_INV_SIMP_TAC `0xf:num`;

        MP_TAC (SPECL [`ctxt_p:int64`; `0x0`; `val (tail_len:int64)`;
          `l1_curr_len:num`; `(int128_to_bytes CC):byte list`; `s5:armstate`]
          BYTE_LIST_AT_SPLIT_BACKWARDS_CARNONICAL) THEN
        REWRITE_TAC[LENGTH_OF_INT128_TO_BYTES] THEN
        CONV_TAC NUM_REDUCE_CONV THEN
        CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
        ASM_SIMP_TAC[] THEN
        ANTS_TAC THENL
        [ IMP_REWRITE_TAC[WORD_ZX_ZX] THEN
          REWRITE_TAC[DIMINDEX_8; DIMINDEX_32; DIMINDEX_64] THEN
          MP_TAC (SPECL [`0x0`; `l1_curr_len:num`; `tail_len:int64`; `CC:int128`; `pt_in:byte list`]
            CIPHER_STEALING_INV_SELECT) THEN
          CONV_TAC NUM_REDUCE_CONV THEN
          ASM_SIMP_TAC[] ; ALL_TAC ] THEN
        REWRITE_TAC[ADD_ASSOC; ARITH_RULE `((l1_curr_len + 0x10) + 0x0) = (l1_curr_len + 0x10)`]; (* will need replacement with v *)

        WORD_ARITH_TAC;
        WORD_ARITH_TAC;
];;

let ENC_TAIL_SWAP_CASE_TAC case =
  let c_tm = `case:num` in
  let v_tm = `v:num` in
  let v = rand (concl (NUM_RED_CONV (subst [case,c_tm] `0x10 + case`))) in
  let r1 = subst [case,c_tm; v,v_tm] `((l1_curr_len + 0x10) + case) = (l1_curr_len + v)` in
  let t1 = subst [case,c_tm] `(cipher_stealing_inv case l1_curr_len (val (tail_len:int64)) CC pt_in):int128` in

  POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th]) THEN (* pop assum: i = case *)

  ARM_ACCSTEPS_TAC AES256_XTS_ENCRYPT_EXEC [] (1--5) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM ADD_ASSOC]) THEN
  RULE_ASSUM_TAC (CONV_RULE NUM_REDUCE_CONV) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    (* For case = 0x1
     `read (memory :> bytes128 (word_add ctxt_p (word l1_curr_len))) s5 =
      cipher_stealing_inv 0x1 l1_curr_len (val tail_len) CC pt_in /\
      (forall i'.
            i' < val tail_len - 0x1
            ==> read (memory :> bytes8 (word_add (word_add ctxt_p (word (l1_curr_len + 0x10 + 0x1))) (word i'))) s5 =
                EL i' (SUB_LIST (0x1,val tail_len - 0x1) (int128_to_bytes CC))) /\
      ~(ival (word 0x1) < &0x0) /\ ival (word (0x1 + 0x1)) - &0x1 = ival (word 0x1)`   *)
  REPEAT CONJ_TAC THENL (* 4 subgoals *)
  [ MATCH_MP_TAC (snd (EQ_IMP_RULE (SPECL [`(word_add ctxt_p (word l1_curr_len)):int64`;
      `s5:armstate`; t1] BREAK_ONE_BLOCK_INTO_BYTES))) THEN
    CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    ASM_REWRITE_TAC[] THEN

    MP_TAC (SPECL [case; `l1_curr_len:num`; `tail_len:int64`; `CC:int128`; `pt_in:byte list`]
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

    MP_TAC (SPECL [`ctxt_p:int64`; case; `val (tail_len:int64)`;
                   `l1_curr_len:num`; `(int128_to_bytes CC):byte list`; `s5:armstate`]
             BYTE_LIST_AT_SPLIT_BACKWARDS_CARNONICAL) THEN
    REWRITE_TAC[LENGTH_OF_INT128_TO_BYTES] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    ASM_SIMP_TAC[] THEN
    ANTS_TAC THENL
    [ IMP_REWRITE_TAC[WORD_ZX_ZX] THEN
      REWRITE_TAC[DIMINDEX_8; DIMINDEX_32; DIMINDEX_64] THEN
      MP_TAC (SPECL [case; `l1_curr_len:num`; `tail_len:int64`; `CC:int128`; `pt_in:byte list`]
              CIPHER_STEALING_INV_SELECT) THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      ASM_SIMP_TAC[] ; ALL_TAC ] THEN
    REWRITE_TAC[ADD_ASSOC; ARITH_RULE r1];

    WORD_ARITH_TAC;
    WORD_ARITH_TAC
];;

let ENC_TAIL_SWAP_ASM_CASES_TAC case =
  let c_tm = `case:num` in
  let asm_case = subst [case, c_tm] `(i:num) = case` in
  ASM_CASES_TAC asm_case THENL [ ENC_TAIL_SWAP_CASE_TAC case; ALL_TAC] THEN
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
let CIPHER_STEALING_ENC_CORRECT = time prove(
  `!ptxt_p ctxt_p len key1_p
    pt_in iv tail_len len_full_blocks num_5blocks
    k1_0 k1_1 k1_2 k1_3 k1_4 k1_5 k1_6 k1_7 k1_8 k1_9 k1_10 k1_11 k1_12 k1_13 k1_14
    pc.
    PAIRWISE nonoverlapping
    [(word pc, LENGTH aes256_xts_encrypt_mc);
    (ptxt_p, val len);
    (ctxt_p, val len);
    (key1_p, 244)] /\
    val len >= 16 /\ val len <= 2 EXP 24 /\
    LENGTH pt_in = val len /\
    word_and len (word 0xfffffffffffffff0) = len_full_blocks /\
    word_and len (word 0xf) = tail_len /\
    word (val len_full_blocks DIV 0x50) = num_5blocks /\
    word_add tail_len len_full_blocks = len /\
    [k1_0; k1_1; k1_2; k1_3; k1_4; k1_5; k1_6; k1_7; k1_8; k1_9; k1_10;
       k1_11; k1_12; k1_13; k1_14] = key1_lst
    ==> ensures arm
    (\s. aligned_bytes_loaded s (word pc) aes256_xts_encrypt_mc /\
         read PC s = word (pc + 0x9e0) /\
         read X0 s = word_add ptxt_p (word (acc_len num_5blocks len_full_blocks)) /\
         read X1 s = word_add ctxt_p (word (acc_len num_5blocks len_full_blocks)) /\
         read X3 s = key1_p /\
         read X21 s = tail_len /\
         read Q6 s = calculate_tweak (acc_blocks num_5blocks len_full_blocks true) iv key2_lst /\
         read X19 s = word 0x87 /\
         read Q16 s = k1_0 /\ read Q17 s = k1_1 /\ read Q12 s = k1_2 /\ read Q13 s = k1_3 /\
         read Q14 s = k1_4 /\ read Q15 s = k1_5 /\ read Q4 s = k1_6 /\ read Q5 s = k1_7 /\
         read Q18 s = k1_8 /\ read Q19 s = k1_9 /\ read Q20 s = k1_10 /\ read Q21 s = k1_11 /\
         read Q22 s = k1_12 /\ read Q23 s = k1_13 /\ read Q7 s = k1_14 /\
         byte_list_at pt_in ptxt_p len s /\
         byte_list_at (aes256_xts_encrypt pt_in (acc_len num_5blocks len_full_blocks) iv key1_lst key2_lst)
         ctxt_p (word (acc_len num_5blocks len_full_blocks)) s)
    (\s.
        read PC s = word (pc + 0xa8c) /\ //LENGTH aes256_xts_encrypt_mc - 8*4 = 0xaac - 0x8 * 0x4
        byte_list_at (aes256_xts_encrypt pt_in (val len) iv key1_lst key2_lst) ctxt_p len s )
    ( MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI,,
      MAYCHANGE [X19; X20; X21; X22] ,,
      MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
      MAYCHANGE [memory :> bytes (ctxt_p,val len)])
    `,
  REWRITE_TAC [(REWRITE_CONV [aes256_xts_encrypt_mc] THENC LENGTH_CONV) `LENGTH aes256_xts_encrypt_mc`] THEN
  REWRITE_TAC[byte_list_at; PAIRWISE; ALL;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REPEAT STRIP_TAC THEN

  (* Prove the bounds on len_full_blocks, num_5blocks and len and their relationships *)
  SUBGOAL_THEN `~(val (len_full_blocks:int64) < 0x10)` ASSUME_TAC THENL
  [ SUBGOAL_THEN `~(val (len:int64) < 0x10)` MP_TAC THENL
    [ASM_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `word_and len (word 0xfffffffffffffff0) = (len_full_blocks:int64)` THEN
    MP_TAC (SPECL [`len:int64`; `len_full_blocks:int64`] NUM_BLOCKS_LO_BOUND_1BLOCK_THM) THEN
    SIMP_TAC[]; ALL_TAC] THEN

  SUBGOAL_THEN `val (len_full_blocks:int64) <= 0x2 EXP 24` ASSUME_TAC THENL
  [ UNDISCH_TAC `val (len:int64) <= 0x2 EXP 24` THEN
    UNDISCH_TAC `word_and len (word 0xfffffffffffffff0) = (len_full_blocks:int64)` THEN
    MP_TAC (SPECL [`len:int64`; `len_full_blocks:int64`] NUM_BLOCKS_HI_BOUND_THM) THEN
    SIMP_TAC[]; ALL_TAC] THEN

  SUBGOAL_THEN `val (tail_len:int64) < 16` ASSUME_TAC THENL
  [ EXPAND_TAC "tail_len" THEN
    REWRITE_TAC[ARITH_RULE `0xf = 2 EXP 4 - 1`] THEN
    REWRITE_TAC[VAL_WORD_AND_MASK_WORD] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    SIMP_TAC[MOD_LT_EQ] THEN
    CONV_TAC NUM_REDUCE_CONV
  ; ALL_TAC] THEN

  (* relationship between variables *)
  SUBGOAL_THEN `val (len_full_blocks:int64) <= val (len:int64)` ASSUME_TAC THENL
  [ EXPAND_TAC "len_full_blocks" THEN SIMP_TAC[NUM_BLOCKS_LT_LEN_THM]; ALL_TAC] THEN

  SUBGOAL_THEN `val (num_5blocks:int64) * 0x50 <= val (len_full_blocks:int64)` ASSUME_TAC THENL
  [ EXPAND_TAC "num_5blocks" THEN
    REWRITE_TAC [VAL_WORD; DIMINDEX_64] THEN
    UNDISCH_TAC `val (len_full_blocks:int64) <= 0x2 EXP 0x18` THEN
    ARITH_TAC; ALL_TAC] THEN

  (* Prove more properties about len_full_blocks and num_5blocks *)
  SUBGOAL_THEN `val (len_full_blocks:int64) DIV 0x50 = val (num_5blocks:int64)` ASSUME_TAC THENL
  [ EXPAND_TAC "num_5blocks" THEN
    IMP_REWRITE_TAC[VAL_WORD; DIMINDEX_64; MOD_LT] THEN
    UNDISCH_TAC `val (len_full_blocks:int64) <= 0x2 EXP 0x18` THEN
    ARITH_TAC; ALL_TAC] THEN

  SUBGOAL_THEN `0x10 divides val (len_full_blocks:int64)` ASSUME_TAC THENL
  [ EXPAND_TAC "len_full_blocks" THEN
    REWRITE_TAC[NUM_BLOCKS_TO_VAL] THEN
    IMP_REWRITE_TAC[VAL_WORD; DIMINDEX_64; MOD_LT; DIVIDES_RMUL; DIVIDES_REFL] THEN
    ASM_ARITH_TAC; ALL_TAC] THEN

  (* If no tail, execute to the end *)
  ASM_CASES_TAC `val (tail_len:int64) = 0` THENL
  [
    ENSURES_INIT_TAC "s0" THEN
    ARM_ACCSTEPS_TAC AES256_XTS_ENCRYPT_EXEC [] (1--2) THEN (* tst x21, #0xf; b.eq .Lxts_enc_abort *)
    (* Discharge if condition *)
    SUBGOAL_THEN `val (word_and (tail_len:int64) (word 0xf)) = 0x0` MP_TAC THENL
    [ UNDISCH_TAC `val (tail_len:int64) = 0x0` THEN BITBLAST_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN

    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC NUM_REDUCE_CONV THEN

    SUBGOAL_THEN `val (word (acc_len (num_5blocks:int64) (len_full_blocks:int64)):int64) =
      acc_len num_5blocks len_full_blocks` ASSUME_TAC THENL
    [ IMP_REWRITE_TAC[VAL_WORD; DIMINDEX_64; MOD_LT] THEN
      MP_TAC (SPECL [`num_5blocks:int64`; `len_full_blocks:int64`; `2 EXP 64`]
        BOUND_OF_ACC_LEN) THEN
      ANTS_TAC THENL [ ASM_ARITH_TAC; ALL_TAC] THEN
      ANTS_TAC THENL [ ASM_SIMP_TAC[]; ALL_TAC] THEN
      ANTS_TAC THENL [ ASM_SIMP_TAC[]; ALL_TAC] THEN
      ANTS_TAC THENL [ ASM_ARITH_TAC; ALL_TAC] THEN
      SIMP_TAC[]; ALL_TAC] THEN
    POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN

    (* Prove that acc_len is equal to total len because there is no tail *)
    SUBGOAL_THEN `val (len:int64) =
      acc_len (num_5blocks:int64) (len_full_blocks:int64)` SUBST1_TAC THENL
    [ SUBGOAL_THEN `len = (len_full_blocks:int64)` SUBST1_TAC THENL
      [ EXPAND_TAC "len" THEN
        SUBGOAL_THEN `tail_len:int64 = word 0` ASSUME_TAC THENL
        [ REWRITE_TAC[GSYM VAL_EQ_0] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
        REWRITE_TAC[ASSUME `tail_len:int64 = word 0`; WORD_ADD_0]
        ; ALL_TAC] THEN
      REWRITE_TAC[acc_len] THEN
      REPEAT_N 4 (COND_CASES_TAC THENL[ASM_ARITH_TAC; ALL_TAC]) THEN

      CONV_TAC SYM_CONV THEN
      REWRITE_TAC[ARITH_RULE `!a. 0x50 * a = a * 0x50`] THEN
      MATCH_MP_TAC (SPECL [`val (len_full_blocks:int64)`; `val (num_5blocks:int64)`] DIVISION_BY_80_LEMMA) THEN
      REPEAT CONJ_TAC THENL
      [
        ASM_SIMP_TAC[];
        ASM_SIMP_TAC[];
        UNDISCH_TAC `~(val (num_5blocks:int64) * 0x50 + 0x10 = val (len_full_blocks:int64))` THEN ARITH_TAC;
        UNDISCH_TAC `~(val (num_5blocks:int64) * 0x50 + 0x20 = val (len_full_blocks:int64))` THEN ARITH_TAC;
        UNDISCH_TAC `~(val (num_5blocks:int64) * 0x50 + 0x30 = val (len_full_blocks:int64))` THEN ARITH_TAC;
        UNDISCH_TAC `~(val (num_5blocks:int64) * 0x50 + 0x40 = val (len_full_blocks:int64))` THEN ARITH_TAC ]
      ; ALL_TAC] THEN
    ASM_SIMP_TAC[]
  ; ALL_TAC
  ] THEN

  (* The cipher stealing branch; tail != 0 *)
  (* The byte-swap needs another invariant proof. *)
  (* In the following "l1" means "less 1 block". This is to differentiate it from the decrypt case
     where at the entry of cipher-stealing, we have one full block left to process and a tail, while
     in encrypt that full block was already processed and that's why we need to go back "less 1"
     to match the decrypt invariant. *)
  ABBREV_TAC `l1_curr_len = ((acc_len (num_5blocks:int64) (len_full_blocks:int64)) - 0x10):num` THEN
  ABBREV_TAC `l1_curr_blocks = ((acc_blocks (num_5blocks:int64) (len_full_blocks:int64) T) - 1):num` THEN

  SUBGOAL_THEN `l1_curr_len + 0x10 <= val (len:int64)` ASSUME_TAC THENL (* similar to decrypt *)
  [ EXPAND_TAC "l1_curr_len" THEN
    MP_TAC (SPECL [`num_5blocks:int64`; `len_full_blocks:int64`] VALUE_OF_ACC_LEN) THEN
    REPEAT_N 3 (ANTS_TAC THENL [ASM_ARITH_TAC ORELSE ASM_SIMP_TAC[]; ALL_TAC]) THEN
    ASM_ARITH_TAC; ALL_TAC ] THEN

  SUBGOAL_THEN `val ((word l1_curr_len):int64) = l1_curr_len` ASSUME_TAC THENL
  [ IMP_REWRITE_TAC[VAL_WORD; DIMINDEX_64; MOD_LT] THEN
    ASM_ARITH_TAC; ALL_TAC] THEN

  SUBGOAL_THEN `val ((word (l1_curr_len + 0x10)):int64) = l1_curr_len + 0x10` ASSUME_TAC THENL
  [ IMP_REWRITE_TAC[VAL_WORD; DIMINDEX_64; MOD_LT] THEN
    ASM_ARITH_TAC; ALL_TAC] THEN
(*
  SUBGOAL_THEN `l1_curr_len >= 0` ASSUME_TAC THENL
  [ REWRITE_TAC[GSYM (ASSUME `(acc_len num_5blocks len_full_blocks) - 0x10 = l1_curr_len`)] THEN
    MP_TAC (SPECL [`num_5blocks:int64`; `len_full_blocks:int64`] VALUE_OF_ACC_LEN) THEN
    REPEAT_N 3 (ANTS_TAC THENL [ASM_ARITH_TAC ORELSE ASM_SIMP_TAC[]; ALL_TAC]) THEN
    ASM_ARITH_TAC ; ALL_TAC ] THEN
*)
  SUBGOAL_THEN `16 * l1_curr_blocks = l1_curr_len` ASSUME_TAC THENL
  [ REWRITE_TAC[GSYM (ASSUME `(acc_len num_5blocks len_full_blocks) - 0x10 = l1_curr_len`)] THEN (* put in tips doc*)
    (* or UNDISCH_THEN `acc_len (num_5blocks:int64) (len_full_blocks:int64) = curr_len`
        (fun th -> REWRITE_TAC[GSYM th]) THEN *)
    EXPAND_TAC "l1_curr_blocks" THEN
    REWRITE_TAC[acc_len; acc_blocks] THEN
    REPEAT_N 4 (COND_CASES_TAC THENL [SIMP_TAC[] THEN ARITH_TAC; ALL_TAC] THEN SIMP_TAC[]) THEN
    ARITH_TAC; ALL_TAC ] THEN

  ABBREV_TAC `CC = aes256_xts_encrypt_round
    (bytes_to_int128 (SUB_LIST (l1_curr_len,0x10) (pt_in:byte list)))
    (calculate_tweak (l1_curr_blocks) (iv:int128) (key2_lst:int128 list))
    (key1_lst:int128 list)` THEN

  (* For address matching when symbolic simulation *)
  SUBGOAL_THEN `16 <= acc_len num_5blocks len_full_blocks` ASSUME_TAC THENL
  [ MP_TAC (SPECL [`num_5blocks:int64`; `len_full_blocks:int64`] VALUE_OF_ACC_LEN) THEN
    REPEAT_N 3 (ANTS_TAC THENL [ASM_ARITH_TAC ORELSE ASM_SIMP_TAC[]; ALL_TAC]) THEN
    ASM_ARITH_TAC; ALL_TAC ] THEN

  SUBGOAL_THEN ` acc_len num_5blocks len_full_blocks = l1_curr_len + 0x10` ASSUME_TAC THENL
  [ REWRITE_TAC[GSYM (ASSUME `(acc_len num_5blocks len_full_blocks) - 0x10 = l1_curr_len`)] THEN
    ASM_ARITH_TAC; ALL_TAC ] THEN

  SUBGOAL_THEN `1 <= acc_blocks (num_5blocks:int64) (len_full_blocks:int64) true` ASSUME_TAC THENL
  [ REWRITE_TAC[acc_blocks] THEN
    REPEAT_N 4 (COND_CASES_TAC THENL [SIMP_TAC[] THEN ARITH_TAC; ALL_TAC] THEN SIMP_TAC[]) THEN
    SUBGOAL_THEN `val (num_5blocks:int64) * 0x50 = val (len_full_blocks:int64)` ASSUME_TAC THENL
    [ MATCH_MP_TAC (SPECL [`val (len_full_blocks:int64)`; `val (num_5blocks:int64)`] DIVISION_BY_80_LEMMA) THEN
        REPEAT CONJ_TAC THENL
        [
          ASM_SIMP_TAC[];
          ASM_SIMP_TAC[];
          UNDISCH_TAC `~(val (num_5blocks:int64) * 0x50 + 0x10 = val (len_full_blocks:int64))` THEN ARITH_TAC;
          UNDISCH_TAC `~(val (num_5blocks:int64) * 0x50 + 0x20 = val (len_full_blocks:int64))` THEN ARITH_TAC;
          UNDISCH_TAC `~(val (num_5blocks:int64) * 0x50 + 0x30 = val (len_full_blocks:int64))` THEN ARITH_TAC;
          UNDISCH_TAC `~(val (num_5blocks:int64) * 0x50 + 0x40 = val (len_full_blocks:int64))` THEN ARITH_TAC ]
        ; ALL_TAC] THEN
    SUBGOAL_THEN `0x10 <= val (num_5blocks:int64) * 0x50` ASSUME_TAC THENL
    [ ASM_ARITH_TAC; ALL_TAC ] THEN
    ASM_ARITH_TAC; ALL_TAC ] THEN

  SUBGOAL_THEN `l1_curr_len + 0x10 + val (tail_len:int64) = val (len:int64)` ASSUME_TAC THENL
  [ REWRITE_TAC[GSYM (ASSUME `acc_len num_5blocks len_full_blocks - 0x10 = l1_curr_len`)] THEN

    MP_TAC (SPECL [`num_5blocks:int64`; `len_full_blocks:int64`] VALUE_OF_ACC_LEN) THEN
    REPEAT_N 3 (ANTS_TAC THENL [ASM_ARITH_TAC ORELSE ASM_SIMP_TAC[]; ALL_TAC]) THEN
    SIMP_TAC[] THEN DISCH_TAC THEN

    ASM_SIMP_TAC[ADD_ASSOC; ARITH_RULE `~(val len_full_blocks < 0x10) ==> val len_full_blocks - 0x10 + 0x10
                                       = val len_full_blocks`] THEN (* add to tips doc, see My questions doc *)
    REWRITE_TAC[GSYM (ASSUME `word_add (tail_len:int64) len_full_blocks = len`)] THEN
    ASM_SIMP_TAC[VAL_WORD_ADD_CASES; DIMINDEX_64;
                 ARITH_RULE `val len_full_blocks <= 0x1000000 /\ val tail_len < 0x10 ==>
                 val tail_len + val len_full_blocks < 0x2 EXP 0x40`] THEN
    ASM_ARITH_TAC; ALL_TAC ] THEN

  SUBGOAL_THEN `word_add (ptxt_p:int64) (word (acc_len num_5blocks len_full_blocks)) =
    word_add ptxt_p (word (l1_curr_len + 0x10))` ASSUME_TAC THENL
  [ REPEAT AP_TERM_TAC THEN
    ASM_ARITH_TAC ; ALL_TAC ] THEN

  SUBGOAL_THEN `word_sub (word_add ctxt_p (word (acc_len num_5blocks len_full_blocks))) (word 0x10):int64 =
                word_add ctxt_p (word l1_curr_len)` ASSUME_TAC THENL
  [ REWRITE_TAC[GSYM (ASSUME `(acc_len num_5blocks len_full_blocks) - 0x10 = l1_curr_len`)] THEN
    ASM_SIMP_TAC[WORD_SUB] THEN
    CONV_TAC WORD_RULE; ALL_TAC] THEN

  SUBGOAL_THEN `word_sub (word_add ctxt_p (word (l1_curr_len + 0x10))) (word 0x10):int64 =
                word_add ctxt_p (word l1_curr_len)` ASSUME_TAC THENL
  [ REWRITE_TAC[GSYM (ASSUME `acc_len num_5blocks len_full_blocks = l1_curr_len + 0x10`)] THEN
    ASM_SIMP_TAC[] ; ALL_TAC] THEN

  (* Invariant proof for .composite_enc_loop *)
  (* Invariant:
    X0 points to tail of pt_in; Pm in specs
    X1 points to starting of last full block of ct_out; CC
    X13 points to tail of ct_out; will become Cm at the end of the loop
    X20 = X0, points to tail of pt_in; Pm
    X21 holds decreasing tail_len
    Q6 holds last tweak
    Q16 ... Q7 holds the key schedule for encryption

    Memory: ptxt_p points to the input
    Memory: Up to the last block, the output pointed to by ctxt_p matches the specification
    Memory: X13 points to tail location in the output, to which Cm is copyied byte by byte from where X1 points
    Memory: X1 (= X13 - 0x10) points to CC = [Cm | CP] will become PP = [Pm | CP] by copying Pm one byte at a time to override Cm
    Loop: bytes are copied in decreasing addresses, i.e. X21 is an offset to both X1 and X13
          decreasing from "tail" down to 0. The iterator i is the value of X21.
    Memory: For the last block, CC, pointed to by X1, for each byte
      [0,i) -- previous decryption result, Cm
      [i,tail_len) -- equal corresponding pt_in tail bytes, Pm
      [tail_len,16] -- previous decryption result, CP
    Memory: For the tail, Cm, pointed to by X13, for each byte
      [i,tail_len) -- copied over from Pm block
  *)

  ENSURES_WHILE_PADOWN_TAC
    `val (tail_len:int64)` (* counter begin number *)
    `0` (* counter end number *)
    `pc + 0x9f4` (* loop body start PC *)
    `pc + 0xa08` (* loop backedge branch PC *)
    `\i s.
        // loop invariant at the end of the loop iteration
        ( read X0 s = word_add ptxt_p (word (l1_curr_len + 0x10)) /\
          read X1 s = word_add ctxt_p (word l1_curr_len)  /\
          read X13 s = word_add ctxt_p (word (l1_curr_len + 0x10)) /\
          read X20 s = word_add ptxt_p (word (l1_curr_len + 0x10)) /\
          read X21 s = (word i):int64 /\
          read Q6 s = calculate_tweak (acc_blocks num_5blocks len_full_blocks true) iv key2_lst /\
          read Q16 s = k1_0 /\ read Q17 s = k1_1 /\ read Q12 s = k1_2 /\ read Q13 s = k1_3 /\
          read Q14 s = k1_4 /\ read Q15 s = k1_5 /\ read Q4 s = k1_6 /\ read Q5 s = k1_7 /\
          read Q18 s = k1_8 /\ read Q19 s = k1_9 /\ read Q20 s = k1_10 /\ read Q21 s = k1_11 /\
          read Q22 s = k1_12 /\ read Q23 s = k1_13 /\ read Q7 s = k1_14 /\
          byte_list_at pt_in ptxt_p len s /\
          // Encryption is correct up until l1_curr_len
          byte_list_at (aes256_xts_encrypt pt_in l1_curr_len iv key1_lst key2_lst)
                          ctxt_p (word l1_curr_len) s /\
          // Contents of CC at each i
          read (memory :> bytes128 (word_add ctxt_p (word l1_curr_len))) s =
            cipher_stealing_inv i l1_curr_len (val (tail_len:int64)) CC pt_in /\

          // bytes of Cm at offset i to (tail_len-i) in CC
          // are stored at their final location in ciphertext in the tail part
          // they're copied from CC before they're overwritten by bytes from Pm
          byte_list_at (SUB_LIST (i, val tail_len - i) (int128_to_bytes CC))
            (word_add ctxt_p (word (l1_curr_len + 0x10 + i)))
            (word ((val tail_len) - i)) s) /\
        // loop backedge condition
        (read ZF s <=> i = 0) /\
        (read NF s <=> ival ((word i):int64) < &0) /\
        (read VF s <=> ~(ival ((word (i + 1)):int64) - &1 = ival ((word i):int64)))` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
  [
    (* Subgoal1: 0 < val tail_len *)
    ASM_ARITH_TAC; (* 5 goals *)

    (* Subgoal2: invariant holds before entering loop *)
    REWRITE_TAC[byte_list_at] THEN
    UNDISCH_THEN `val ((word l1_curr_len):int64) = l1_curr_len`
        (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th]
        THEN ASSUME_TAC th) THEN (* put in tips doc: keep the assumption *)
    UNDISCH_THEN `val ((word (l1_curr_len + 0x10)):int64) = l1_curr_len + 0x10`
        (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th]
        THEN ASSUME_TAC th) THEN

    ENSURES_INIT_TAC "s0" THEN
    ARM_ACCSTEPS_TAC AES256_XTS_ENCRYPT_EXEC [] (1--2) THEN
    (* Discharge if condition *)
    SUBGOAL_THEN `~(val (word_and (tail_len:int64) (word 0xf)) = 0x0)` MP_TAC THENL
    [ UNDISCH_TAC `~(val (tail_len:int64) = 0x0)` THEN
      UNDISCH_TAC `val (tail_len:int64) < 16` THEN
      MP_TAC (SPEC `tail_len:int64` WORD_AND_MASK16_EQ_0) THEN
      SIMP_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN

    ARM_ACCSTEPS_TAC AES256_XTS_ENCRYPT_EXEC [] (3--5) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    (*
    `tail_len = word (val tail_len) /\
    (forall i.
          i < l1_curr_len
          ==> read (memory :> bytes8 (word_add ctxt_p (word i))) s5 =
              EL i (aes256_xts_encrypt pt_in l1_curr_len iv key1_lst key2_lst)) /\
    read (memory :> bytes128 (word_add ctxt_p (word l1_curr_len))) s5 =
    cipher_stealing_inv (val tail_len) l1_curr_len (val tail_len) CC pt_in /\
    (forall i.
          i < val (word 0x0)
          ==> read (memory :> bytes8 (word_add (word_add ctxt_p (word (l1_curr_len + 0x10 + val tail_len)))
                                              (word i))) s5 =
              EL i (SUB_LIST (val tail_len,0x0) (int128_to_bytes CC)))`. *)
    REPEAT CONJ_TAC THENL (* 4 subgoals (7 total) *)
    [
      (* `tail_len = word (val tail_len)` *)
      REWRITE_TAC[WORD_VAL];

    (*`forall i.
     i < l1_curr_len
     ==> read (memory :> bytes8 (word_add ctxt_p (word i))) s5 =
         EL i (aes256_xts_encrypt pt_in l1_curr_len iv key1_lst key2_lst)`. *)
      UNDISCH_TAC
      `forall i.
          i < l1_curr_len + 0x10
          ==> read (memory :> bytes8 (word_add (ctxt_p:int64) (word i))) s5 =
              EL i (aes256_xts_encrypt pt_in (l1_curr_len + 0x10) iv key1_lst key2_lst)` THEN
      REWRITE_TAC[GSYM (ASSUME `0x10 * l1_curr_blocks = l1_curr_len`)] THEN
      REWRITE_TAC[ARITH_RULE `0x10 * l1_curr_blocks + 0x10 = 0x10 * (l1_curr_blocks + 0x1)`] THEN
      MP_TAC (SPECL [`0x10 * (l1_curr_blocks + 0x1):num`; `ctxt_p:int64`;
                      `(aes256_xts_encrypt pt_in (0x10 * (l1_curr_blocks + 0x1)) iv key1_lst key2_lst):byte list`;
                      `s5:armstate`] BYTE_LIST_TO_NUM_THM) THEN
      ANTS_TAC THENL [
        REWRITE_TAC[LENGTH_OF_AES256_XTS_ENCRYPT_FULL_BLOCKS] THEN
        ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN (fun th -> REWRITE_TAC[th]) THEN

      MP_TAC (SPECL [`0x10 * l1_curr_blocks:num`; `ctxt_p:int64`;
                      `(aes256_xts_encrypt pt_in (0x10 * l1_curr_blocks) iv key1_lst key2_lst):byte list`;
                      `s5:armstate`] BYTE_LIST_TO_NUM_THM) THEN
      ANTS_TAC THENL [
        REWRITE_TAC[LENGTH_OF_AES256_XTS_ENCRYPT_FULL_BLOCKS] THEN
        ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN (fun th -> REWRITE_TAC[th]) THEN

      MP_TAC(SPECL [`l1_curr_blocks:num`; `pt_in:byte list`; `iv:int128`; `key1_lst:int128 list`; `key2_lst:int128 list`]
                    LENGTH_OF_AES256_XTS_ENCRYPT_FULL_BLOCKS) THEN
      MP_TAC(SPECL [`l1_curr_blocks + 0x1:num`; `pt_in:byte list`; `iv:int128`; `key1_lst:int128 list`; `key2_lst:int128 list`]
                    LENGTH_OF_AES256_XTS_ENCRYPT_FULL_BLOCKS) THEN
      IMP_REWRITE_TAC[SUB_LIST_LENGTH_IMPLIES] THEN
      IMP_REWRITE_TAC[ARITH_RULE `0x10 * (l1_curr_blocks + 0x1) = 0x10 * l1_curr_blocks + 0x10`] THEN
      DISCH_TAC THEN DISCH_TAC THEN
      (* `read (memory :> bytes (ctxt_p,0x10 * (l1_curr_blocks + 0x1))) s5 =
          num_of_bytelist (aes256_xts_encrypt pt_in (0x10 * (l1_curr_blocks + 0x1)) iv key1_lst key2_lst)
          ==> read (memory :> bytes (ctxt_p,l1_curr_len)) s5 =
              num_of_bytelist (aes256_xts_encrypt pt_in l1_curr_len iv key1_lst key2_lst)` *)

      DISCH_TAC THEN
      IMP_REWRITE_TAC[SPECL [`ctxt_p:int64`; `l1_curr_len:num`;
                             `(aes256_xts_encrypt pt_in (l1_curr_len + 0x10) iv key1_lst key2_lst):byte list`;
                             `s5:armstate`]  READ_BYTES_AND_BYTE128_MERGE] THEN
      EXISTS_TAC `iv:int128` THEN EXISTS_TAC `key1_lst:int128 list` THEN
      EXISTS_TAC `key2_lst:int128 list` THEN EXISTS_TAC `pt_in:byte list` THEN
      (* `num_of_bytelist (SUB_LIST (0x0,l1_curr_len)
               (aes256_xts_encrypt pt_in (l1_curr_len + 0x10) iv key1_lst key2_lst)) =
            num_of_bytelist (aes256_xts_encrypt pt_in l1_curr_len iv key1_lst key2_lst) /\
          l1_curr_len + 0x10 <=
          LENGTH (aes256_xts_encrypt pt_in (l1_curr_len + 0x10) iv key1_lst key2_lst) /\
          num_of_bytelist (aes256_xts_encrypt pt_in (l1_curr_len + 0x10) iv key1_lst key2_lst) =
            num_of_bytelist (SUB_LIST (0x0,l1_curr_len + 0x10)
                (aes256_xts_encrypt pt_in (l1_curr_len + 0x10) iv key1_lst key2_lst))`   *)
      REPEAT CONJ_TAC THENL [ (* 3 subgoals (8 total) *)
        AP_TERM_TAC THEN
        REWRITE_TAC[GSYM (ASSUME `0x10 * l1_curr_blocks = l1_curr_len`)] THEN
        IMP_REWRITE_TAC[SUB_LIST_OF_AES256_XTS_ENCRYPT_FULL_BLOCKS];

        ASM_ARITH_TAC;

        IMP_REWRITE_TAC[SUB_LIST_LENGTH_IMPLIES]
      ];

      (* `read (memory :> bytes128 (word_sub (word_add ctxt_p (word l1_curr_len)) (word 0x10))) s5
          = cipher_stealing_inv (val tail_len) l1_curr_len (val tail_len) CC pt_in`     *)
      REWRITE_TAC[cipher_stealing_inv; SUB_REFL] THEN
      SUBGOAL_THEN `SUB_LIST (val (tail_len:int64),0x0) (SUB_LIST (l1_curr_len + 0x10,val tail_len) (pt_in:byte list)) = []` SUBST1_TAC THENL
      [ REWRITE_TAC[SUB_LIST_CLAUSES]; ALL_TAC] THEN
      REWRITE_TAC[CONJUNCT1 APPEND] THEN
      SUBGOAL_THEN `APPEND (SUB_LIST (0x0,val (tail_len:int64)) (int128_to_bytes CC))
        (SUB_LIST (val tail_len,0x10 - val tail_len) (int128_to_bytes CC)) =
        (int128_to_bytes CC)` SUBST1_TAC THENL
      [ MP_TAC (ISPECL [`int128_to_bytes CC`; `val (tail_len:int64)`; `16 - val (tail_len:int64)`; `0`] (GSYM SUB_LIST_SPLIT)) THEN
        IMP_REWRITE_TAC[ADD_CLAUSES; ARITH_RULE `!x. x < 16 ==> x + 16 - x = 16`] THEN
        DISCH_TAC THEN
        IMP_REWRITE_TAC[SUB_LIST_LENGTH_IMPLIES; LENGTH_OF_INT128_TO_BYTES] ; ALL_TAC] THEN
      REWRITE_TAC[BYTES_TO_INT128_OF_INT128_TO_BYTES] THEN

      (* `read (memory :> bytes128 (word_sub (word_add ctxt_p (word curr_len)) (word 0x10))) s5  = CC` *)
      (* Apply READ_LAST_LEMMA with proper arguments *)
      MP_TAC (SPECL [`ctxt_p:int64`; `l1_curr_len:num`; `word (l1_curr_len+0x10):int64`;
        `aes256_xts_encrypt pt_in (l1_curr_len+0x10) iv key1_lst key2_lst:byte list`; `s5:armstate`] READ_LAST_LEMMA) THEN
      UNDISCH_THEN `val ((word (l1_curr_len + 0x10)):int64) = l1_curr_len + 0x10`
        (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th] THEN ASSUME_TAC th) THEN
      ASM_SIMP_TAC[] THEN
    (*  `(l1_curr_len + 0x10 <= l1_curr_len + 0x10 /\
          LENGTH (aes256_xts_encrypt pt_in (l1_curr_len + 0x10) iv key1_lst key2_lst) =
          l1_curr_len + 0x10
          ==> read (memory :> bytes128 (word_add ctxt_p (word l1_curr_len))) s5 =
              bytes_to_int128 (SUB_LIST (l1_curr_len,0x10)
                    (aes256_xts_encrypt pt_in (l1_curr_len + 0x10) iv key1_lst key2_lst)))
        ==> read (memory :> bytes128 (word_add ctxt_p (word l1_curr_len))) s5 = CC` *)
      ANTS_TAC THENL
      [ CONJ_TAC THENL
        [ ARITH_TAC;

         (* `LENGTH (aes256_xts_encrypt pt_in l1_curr_len iv key1_lst key2_lst) = l1_curr_len`*)
          REWRITE_TAC[GSYM (ASSUME `0x10 * l1_curr_blocks = l1_curr_len`);
                      ARITH_RULE `0x10 * l1_curr_blocks + 0x10 = 0x10 * (l1_curr_blocks + 0x1)`;
                      LENGTH_OF_AES256_XTS_ENCRYPT_FULL_BLOCKS]  ]
      ; ALL_TAC ] THEN

      DISCH_THEN (fun th -> REWRITE_TAC[th]) THEN

      (* `bytes_to_int128 (SUB_LIST (l1_curr_len,0x10)
              (aes256_xts_encrypt pt_in (l1_curr_len + 0x10) iv key1_lst key2_lst)) = CC` *)
      REWRITE_TAC[aes256_xts_encrypt] THEN
      SIMP_TAC[ARITH_RULE `~(l1_curr_len + 0x10 < 0x10)`] THEN
      REWRITE_TAC[GSYM (ASSUME `0x10 * l1_curr_blocks = l1_curr_len`)] THEN
      SIMP_TAC[ARITH_RULE `0x10 * l1_curr_blocks + 0x10 = 0x10 * (l1_curr_blocks + 0x1)`;
                MOD_MULT] THEN
      CONV_TAC (DEPTH_CONV let_CONV) THEN
      IMP_REWRITE_TAC[SUB_0; DIV_MULT] THEN

      COND_CASES_TAC THENL
      [ (* `l1_curr_blocks + 0x1 < 0x2` *)
        MP_TAC (SPECL [`0x0:num`; `0x0:num`; `pt_in:byte list`; `iv:int128`;
                       `key1_lst:int128 list`; `key2_lst:int128 list`]
               LENGTH_OF_AES256_XTS_ENCRYPT_TAIL) THEN
        CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN

        EXPAND_TAC "CC" THEN
        SUBGOAL_THEN `l1_curr_len = 0` SUBST1_TAC THENL
        [ UNDISCH_TAC `l1_curr_blocks + 0x1 < 2` THEN
          REWRITE_TAC[GSYM (ASSUME `0x10 * l1_curr_blocks = l1_curr_len`)] THEN
          ARITH_TAC ; ALL_TAC] THEN
        IMP_REWRITE_TAC[(ISPECL [`(aes256_xts_encrypt_tail 0x0 0x0 pt_in iv key1_lst key2_lst):byte list`;
            `0x10:num`] SUB_LIST_LENGTH_IMPLIES)] THEN
        REWRITE_TAC[AES256_XTS_ENCRYPT_TAIL_WHEN_1BLOCK] THEN
        SUBGOAL_THEN `l1_curr_blocks = 0` SUBST1_TAC THENL
        [ UNDISCH_TAC `l1_curr_blocks + 0x1 < 2` THEN ARITH_TAC ; ALL_TAC] THEN
        CONV_TAC NUM_REDUCE_CONV;

        (* ~(l1_curr_len DIV 0x10 < 0x2) *)
        CONV_TAC NUM_REDUCE_CONV THEN
        SUBGOAL_THEN `l1_curr_blocks >= 1` ASSUME_TAC THENL
        [ ASM_ARITH_TAC ; ALL_TAC ] THEN
        IMP_REWRITE_TAC[ARITH_RULE `l1_curr_blocks >= 0x1 ==> (l1_curr_blocks + 0x1) - 0x2 = l1_curr_blocks - 0x1`;
                        ARITH_RULE `l1_curr_blocks >= 0x1 ==> (l1_curr_blocks + 0x1) - 0x1 = l1_curr_blocks`] THEN

        MP_TAC (SPECL [`0`;`(l1_curr_blocks - 1):num`; `pt_in:byte list`; `iv:int128`;
                       `key1_lst:int128 list`; `key2_lst:int128 list`]
                LENGTH_OF_AES256_XTS_ENCRYPT_REC) THEN
        ASM_SIMP_TAC[ARITH_RULE `l1_curr_blocks >= 0x1 ==> ~(l1_curr_blocks - 0x1 < 0x0)`] THEN
        IMP_REWRITE_TAC[SUB_0; ARITH_RULE `l1_curr_blocks >= 0x1 ==> l1_curr_blocks - 1 + 1 = l1_curr_blocks`] THEN
        REWRITE_TAC[GSYM (ASSUME `0x10 * l1_curr_blocks = l1_curr_len`)] THEN
        IMP_REWRITE_TAC[SUB_LIST_APPEND_RIGHT_LEMMA] THEN
        DISCH_TAC THEN
         (* `bytes_to_int128 (SUB_LIST (0x0,0x10) (aes256_xts_encrypt_tail l1_curr_blocks 0x0 pt_in iv key1_lst key2_lst))
             = CC /\ l1_curr_blocks * 0x10 = l1_curr_len`*)
        MP_TAC (SPECL [`l1_curr_blocks:num`; `0x0:num`; `pt_in:byte list`; `iv:int128`;
                       `key1_lst:int128 list`; `key2_lst:int128 list`]
                LENGTH_OF_AES256_XTS_ENCRYPT_TAIL) THEN
        CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
        ASM_SIMP_TAC[SUB_LIST_LENGTH_IMPLIES] THEN
        REWRITE_TAC[AES256_XTS_ENCRYPT_TAIL_WHEN_1BLOCK] THEN
        EXPAND_TAC "CC" THEN
        REWRITE_TAC[GSYM (ASSUME `0x10 * l1_curr_blocks = l1_curr_len`); CONJUNCT1 MULT_AC]
      ];
    (* `forall i.
          i < val (word 0x0)
          ==> read (memory :> bytes8 (word_add (word_add ctxt_p (word (l1_curr_len + val tail_len)))
                                      (word i))) s5
              = EL i (SUB_LIST (val tail_len,0x0) (int128_to_bytes CC))`*)
      REWRITE_TAC[VAL_WORD_0] THEN ARITH_TAC
    ];

    (* Subgoal 3: inductive step *)
    REPEAT STRIP_TAC THEN

    (* For non-overlapping and MAYCHANGE address reasoning *)
    SUBGOAL_THEN `(l1_curr_len + 0x10) + i < val (len:int64)` ASSUME_TAC THENL
    [ REWRITE_TAC[GSYM (ASSUME `acc_len num_5blocks len_full_blocks - 0x10 = l1_curr_len`)] THEN
      MP_TAC (SPECL [`num_5blocks:int64`; `len_full_blocks:int64`] VALUE_OF_ACC_LEN) THEN
      REPEAT_N 3 (ANTS_TAC THENL [ASM_ARITH_TAC ORELSE ASM_SIMP_TAC[]; ALL_TAC]) THEN
      SIMP_TAC[] THEN DISCH_TAC THEN

      UNDISCH_TAC `word_add (tail_len:int64) (len_full_blocks:int64) = len` THEN
      UNDISCH_TAC `i < val (tail_len:int64)` THEN

      ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
      REWRITE_TAC[VAL_WORD_ADD;DIMINDEX_64] THEN
      IMP_REWRITE_TAC[MOD_LT] THEN
      ASM_ARITH_TAC
    ; ALL_TAC ] THEN

    MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN
    EXISTS_TAC `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
        MAYCHANGE [X19; X20; X21; X22],,
        MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15],,
        MAYCHANGE [memory :> bytes8 (word_add ctxt_p (word (l1_curr_len + 0x10 + i)))],,
        MAYCHANGE [memory :> bytes8 (word_add ctxt_p (word (l1_curr_len + i)))]` THEN
    REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    CONJ_TAC THENL [
      REPEAT (GEN_REWRITE_TAC ONCE_DEPTH_CONV [GSYM SEQ_ASSOC] THEN
              MATCH_MP_TAC SUBSUMED_SEQ THEN REWRITE_TAC[SUBSUMED_REFL]) THEN
      ABBREV_TAC `vallen = val (len:int64)` THEN
      SUBSUMED_MAYCHANGE_TAC; ALL_TAC] THEN

    REWRITE_TAC[byte_list_at] THEN
    UNDISCH_THEN `val ((word l1_curr_len):int64) = l1_curr_len`
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
    ; ALL_TAC ] THEN

    (* The symbolic simulation does not capture the LDR/STR at a byte level with i as the iterator, because it doesn't
      know which i. So the following steps are to break the cases for values of i *)
    (* Read a byte from Cm (at location l1_curr_len + i into w15 *)
    MP_TAC (SPECL [`(word_add ctxt_p (word l1_curr_len)):int64`; `word i:int64`; `s0:armstate`;
      `(cipher_stealing_inv (i + 0x1) l1_curr_len (val (tail_len:int64)) CC pt_in):int128`]
      SELECT_ONE_BYTE_FROM_BLOCK) THEN

    SUBGOAL_THEN `val ((word i):int64) < 0x10` ASSUME_TAC THENL
    [ UNDISCH_TAC `i < val (tail_len:int64)` THEN
      UNDISCH_TAC `val (tail_len:int64) < 0x10` THEN
      WORD_ARITH_TAC; ALL_TAC ] THEN
    ASM_SIMP_TAC[] THEN
    REPEAT STRIP_TAC THEN
    (* Added assumption
     69 [`read (memory :> bytes8 (word_add (word_add ctxt_p (word l1_curr_len)) (word i))) s0 =
           EL (val (word i)) (int128_to_bytes (cipher_stealing_inv (i + 0x1) l1_curr_len (val tail_len) CC pt_in))` *)

    (* Read a byte from Pm at location l1_curr_len + 16 + i into w14 *)
    MP_TAC (SPECL [`ptxt_p:int64`; `len:int64`; `(word_add (word (l1_curr_len + 0x10)) (word i)):int64`;
      `pt_in:byte list`; `s0:armstate`] SELECT_ONE_BYTE_FROM_FORALL) THEN

    SUBGOAL_THEN `val (word_add ((word (l1_curr_len+0x10)):int64) (word i)) < val (len:int64)` ASSUME_TAC THENL
    [ REWRITE_TAC[WORD_RULE `!a b. word_add ((word a):int64) (word b) = word (a + b)`] THEN
      IMP_REWRITE_TAC[VAL_WORD; DIMINDEX_64; MOD_LT] THEN
      ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN
    STRIP_TAC THEN
    (* Added assumption
       71 [`read (memory :> bytes8 (word_add ptxt_p (word_add (word (l1_curr_len + 0x10)) (word i)))) s0 =
            EL (val (word_add (word (l1_curr_len + 0x10)) (word i))) pt_in`] *)

    (* Break the assumption `read (memory :> bytes128 (word_add ctxt_p (word l1_curr_len))) s0``
      into bytes using BREAK_ONE_BLOCK_INTO_BYTES *)
    MP_TAC (SPECL [`(word_add ctxt_p (word l1_curr_len)):int64`; `s0:armstate`;
      `(cipher_stealing_inv (i + 0x1) l1_curr_len (val (tail_len:int64)) CC pt_in):int128`]
      BREAK_ONE_BLOCK_INTO_BYTES) THEN
    ASM_SIMP_TAC[] THEN REPEAT STRIP_TAC THEN

    (* For address matching when symbolic simulation *)

    (* From John, changed all addresses to canonical form where the pointer is the first operand of word_add *)
    CHANGED_TAC(RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV))) THEN

    SUBGOAL_THEN `word_add (ptxt_p:int64) (word_add (word (l1_curr_len+0x10)) (word i)) =
      word_add ptxt_p (word ((l1_curr_len + 16) + i))` ASSUME_TAC THENL
    [ REWRITE_TAC[WORD_RULE `!a b. word_add ((word a):int64) (word b) = word (a + b)`; ADD_ASSOC]
    ; ALL_TAC] THEN
    POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN

    SUBGOAL_THEN `val ((word i):int64) = i` MP_TAC THENL
    [ IMP_REWRITE_TAC[VAL_WORD; DIMINDEX_64; MOD_LT] THEN
      ASM_ARITH_TAC
    ; ALL_TAC] THEN
    DISCH_THEN(RULE_ASSUM_TAC o REWRITE_RULE o CONJUNCTS) THEN

    (* case analysis based on i = 0 ... 14, because symbolic execution
       needs to know which byte is being overwritten in pt_ptr to properly update the state. *)
    (* Case 0 needed its own tactic *)
    ASM_CASES_TAC `i:num = 0` THENL
    [ ENC_TAIL_SWAP_CASE_0_TAC; ALL_TAC ] THEN

    MP_TAC (SPECL [`0`; `i:num`] LE_LT) THEN
    ASM_SIMP_TAC[] THEN
    DISCH_TAC THEN
    MP_TAC (SPECL [`0`; `i:num`] LE_SUC_LT) THEN
    ASM_SIMP_TAC[] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    ASM_SIMP_TAC[] THEN
    DISCH_TAC THEN

    MAP_EVERY (fun i -> ENC_TAIL_SWAP_ASM_CASES_TAC (mk_numeral (num i))) (1--14) THEN
    UNDISCH_TAC `15 <= i` THEN
    UNDISCH_TAC `i < val (tail_len:int64)` THEN
    UNDISCH_TAC `val (tail_len:int64) < 16` THEN
    ARITH_TAC;

    (* Subgoal 4: Prove backedge is taken when i > 0 *)
    REPEAT STRIP_TAC THEN
    REWRITE_TAC[byte_list_at] THEN
    ENSURES_INIT_TAC "s0" THEN
    ARM_ACCSTEPS_TAC AES256_XTS_ENCRYPT_EXEC [] (1--1) THEN
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
    SUBGOAL_THEN `(SUB_LIST (0x0,val (tail_len:int64)) (SUB_LIST (l1_curr_len + 16,val tail_len) (pt_in:byte list))) =
      (SUB_LIST (l1_curr_len + 16,val tail_len) pt_in)` SUBST1_TAC THENL
    [ IMP_REWRITE_TAC[SUB_LIST_REFL] THEN
      ASM_REWRITE_TAC[LENGTH_SUB_LIST; MIN] THEN
      ASM_ARITH_TAC; ALL_TAC] THEN

    MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN
    EXISTS_TAC `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
        MAYCHANGE [X19; X20; X21; X22],,
        MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15],,
        MAYCHANGE [memory :> bytes128 (word_add ctxt_p (word l1_curr_len))]` THEN
    REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    CONJ_TAC THENL [
      REPEAT (GEN_REWRITE_TAC ONCE_DEPTH_CONV [GSYM SEQ_ASSOC] THEN
              MATCH_MP_TAC SUBSUMED_SEQ THEN REWRITE_TAC[SUBSUMED_REFL]) THEN
      ABBREV_TAC `vallen = val (len:int64)` THEN
      SUBSUMED_MAYCHANGE_TAC; ALL_TAC] THEN

    ABBREV_TAC `curr_blocks = (acc_blocks (num_5blocks:int64) (len_full_blocks:int64) T):num` THEN

    SUBGOAL_THEN `curr_blocks = l1_curr_blocks + 0x1` ASSUME_TAC THENL
    [ REWRITE_TAC[GSYM (ASSUME `curr_blocks - 0x1 = l1_curr_blocks`)] THEN
      EXPAND_TAC "curr_blocks" THEN
      ASM_ARITH_TAC; ALL_TAC ] THEN

    ENSURES_INIT_TAC "s0" THEN
    ARM_ACCSTEPS_TAC AES256_XTS_ENCRYPT_EXEC [] (1--32) THEN

    ABBREV_TAC `combinedCC = bytes_to_int128
                  (APPEND (SUB_LIST (l1_curr_len + 0x10,val (tail_len:int64)) (pt_in:byte list))
                  (SUB_LIST (val tail_len,0x10 - val tail_len)
                  (int128_to_bytes (CC:int128))))` THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `aes256_xts_encrypt_round combinedCC
      (calculate_tweak curr_blocks iv key2_lst) key1_lst` o  MATCH_MP (MESON[]
      `read (Q26:(armstate,int128)component) (s:armstate) = a ==> !a'. a = a' ==> read Q26 s = a'`)) THEN
    REWRITE_TAC[ASSUME `curr_blocks = l1_curr_blocks + 0x1`] THEN
    ANTS_TAC THENL
    [ EXPAND_TAC "key1_lst" THEN
      CONV_TAC (RAND_CONV (
      REWRITE_CONV [aes256_xts_encrypt_round] THENC
      DEPTH_CONV let_CONV)) THEN
      GEN_REWRITE_TAC LAND_CONV [WORD_XOR_SYM] THEN
      AP_THM_TAC THEN
      REWRITE_TAC [aes256_encrypt] THEN
      REWRITE_TAC EL_15_128_CLAUSES THEN
      REWRITE_TAC [aes256_encrypt_round; aese; aesmc] THEN
      CONV_TAC (TOP_DEPTH_CONV let_CONV) THEN
      AP_TERM_TAC THEN
      GEN_REWRITE_TAC LAND_CONV [WORD_XOR_SYM] THEN
      REPEAT (AP_THM_TAC ORELSE AP_TERM_TAC) THEN
      GEN_REWRITE_TAC LAND_CONV [WORD_XOR_SYM] THEN
      REFL_TAC; DISCH_TAC ] THEN

    ARM_ACCSTEPS_TAC AES256_XTS_ENCRYPT_EXEC [] (33--33) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_SIMP_TAC[] THEN

    UNDISCH_THEN `l1_curr_len + 16 + val (tail_len:int64) = val (len:int64)`
      (fun th -> SUBST1_TAC (GSYM th)) THEN
    REWRITE_TAC[GSYM (ASSUME `0x10 * l1_curr_blocks = l1_curr_len`)] THEN

    (* `forall i.
        i < 0x10 * l1_curr_blocks + 0x10 + val tail_len
        ==> read (memory :> bytes8 (word_add ctxt_p (word i))) s33 =
            EL i (aes256_xts_encrypt pt_in (0x10 * l1_curr_blocks + 0x10 + val tail_len) iv key1_lst key2_lst)`  *)
    MATCH_MP_TAC (SPECL [`0x10 * l1_curr_blocks:num`; `tail_len:int64`; `ctxt_p:int64`; `s33:armstate`]
                  BREAK_DATA_INTO_PARTS_ENCRYPT) THEN
    REPEAT CONJ_TAC THENL (* 4 subgoals *)
    [ (* 1.
          `0x10 * l1_curr_blocks + 0x10 + val tail_len <=
          LENGTH (aes256_xts_encrypt pt_in (0x10 * l1_curr_blocks + 0x10 + val tail_len) iv key1_lst key2_lst)`*)
      IMP_REWRITE_TAC[LENGTH_OF_AES256_XTS_ENCRYPT] THEN ARITH_TAC;

      (* 2.
         `forall i.
          i < 0x10 * l1_curr_blocks
          ==> read (memory :> bytes8 (word_add ctxt_p (word i))) s33 =
              EL i (aes256_xts_encrypt pt_in (0x10 * l1_curr_blocks + 0x10 + val tail_len) iv key1_lst key2_lst)` *)
      UNDISCH_TAC `forall i.
          i < l1_curr_len
          ==> read (memory :> bytes8 (word_add ctxt_p (word i))) s33 =
              EL i (aes256_xts_encrypt pt_in l1_curr_len iv key1_lst key2_lst)` THEN
      REWRITE_TAC[GSYM (ASSUME `0x10 * l1_curr_blocks = l1_curr_len`)] THEN
      MP_TAC (SPECL [`0x10 * l1_curr_blocks:num`; `ctxt_p:int64`;
                `(aes256_xts_encrypt pt_in (0x10 * l1_curr_blocks + 0x10 + val (tail_len:int64)) iv key1_lst key2_lst):byte list`;
                `s33:armstate`] BYTE_LIST_TO_NUM_THM) THEN
      ANTS_TAC THENL [
        IMP_REWRITE_TAC[LENGTH_OF_AES256_XTS_ENCRYPT] THEN
        ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN (fun th -> REWRITE_TAC[th]) THEN
      MP_TAC (SPECL [`0x10 * l1_curr_blocks:num`; `ctxt_p:int64`;
                      `(aes256_xts_encrypt pt_in (0x10 * l1_curr_blocks) iv key1_lst key2_lst):byte list`;
                      `s33:armstate`] BYTE_LIST_TO_NUM_THM) THEN
      ANTS_TAC THENL [
        IMP_REWRITE_TAC[LENGTH_OF_AES256_XTS_ENCRYPT_FULL_BLOCKS] THEN
        ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN (fun th -> REWRITE_TAC[th]) THEN

      DISCH_THEN (fun th -> REWRITE_TAC[th]) THEN
      AP_TERM_TAC THEN
      MP_TAC(SPECL [`l1_curr_blocks:num`; `pt_in:byte list`; `iv:int128`; `key1_lst:int128 list`; `key2_lst:int128 list`]
                    LENGTH_OF_AES256_XTS_ENCRYPT_FULL_BLOCKS) THEN
      DISCH_TAC THEN
      IMP_REWRITE_TAC[SUB_LIST_OF_AES256_XTS_ENCRYPT] THEN
      REWRITE_TAC[GSYM (ASSUME `0x10 * l1_curr_blocks = l1_curr_len`)] THEN
      ASM_SIMP_TAC[SUB_LIST_LENGTH_IMPLIES];

      (* 3.
         `forall i.
          i < 0x10
          ==> read (memory :> bytes8 (word_add (word_add ctxt_p (word (0x10 * l1_curr_blocks))) (word i)))
              s33 =  EL i (SUB_LIST (0x10 * l1_curr_blocks,0x10)
                            (aes256_xts_encrypt pt_in (0x10 * l1_curr_blocks + 0x10 + val tail_len) iv key1_lst key2_lst))` *)
      MP_TAC (SPECL [`0x10:num`; `(word_add ctxt_p (word (0x10 * l1_curr_blocks))):int64`;
                ` (SUB_LIST (0x10 * l1_curr_blocks,0x10)
                  (aes256_xts_encrypt pt_in (0x10 * l1_curr_blocks + 0x10 + val (tail_len:int64))
                   iv key1_lst key2_lst)):byte list`;
                `s33:armstate`] BYTE_LIST_TO_NUM_THM) THEN
      ANTS_TAC THENL [
        REWRITE_TAC[LENGTH_SUB_LIST] THEN
        IMP_REWRITE_TAC[LENGTH_OF_AES256_XTS_ENCRYPT] THEN
        ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[SUB_LIST_MIN_RIGHT; MIN] THEN
      DISCH_THEN (fun th -> REWRITE_TAC[th]) THEN

      REWRITE_TAC[READ_MEMORY_BYTES_BYTES128] THEN
      ASM_REWRITE_TAC[] THEN
      SIMP_TAC[ARITH_RULE `0x10 <= 0x10`] THEN
      REWRITE_TAC[aes256_xts_encrypt] THEN
      SIMP_TAC[ARITH_RULE `!x y. ~(x + 16 + y < 16)`] THEN
      REWRITE_TAC[GSYM (ASSUME `0x10 * l1_curr_blocks = l1_curr_len`);
                  ARITH_RULE `0x10 * l1_curr_blocks + 0x10 + val tail_len =
                      0x10 * (l1_curr_blocks + 1) + val tail_len`] THEN
      REWRITE_TAC[MOD_MULT_ADD] THEN
      ASM_SIMP_TAC[MOD_LT] THEN
      REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
      REWRITE_TAC[ARITH_RULE
        `((0x10 * (l1_curr_blocks + 0x1) + val tail_len) - val tail_len) DIV 0x10 =
         (0x10 * (l1_curr_blocks + 0x1)) DIV 0x10`] THEN
      IMP_REWRITE_TAC[DIV_MULT; ARITH_RULE `~(16 = 0)`] THEN
      COND_CASES_TAC THENL
      [ (* `l1_curr_blocks + 0x1 < 0x2` *)
        REWRITE_TAC[GSYM (ASSUME `0x10 * l1_curr_blocks = l1_curr_len`)] THEN
        SUBGOAL_THEN `l1_curr_blocks = 0` ASSUME_TAC THENL
        [ UNDISCH_TAC `l1_curr_blocks + 0x1 < 2` THEN ARITH_TAC ; ALL_TAC] THEN
        REWRITE_TAC[ASSUME `l1_curr_blocks = 0x0`] THEN
        EXPAND_TAC "combinedCC" THEN
        REWRITE_TAC[aes256_xts_encrypt_tail] THEN
        ASM_SIMP_TAC[LET_DEF; LET_END_DEF] THEN
        ASM_REWRITE_TAC[GSYM (ASSUME `0 = l1_curr_len`)] THEN
        CONV_TAC NUM_REDUCE_CONV THEN

        MP_TAC (SPECL [`(SUB_LIST (0,0x10) pt_in):byte list`;
          `(SUB_LIST (0x10,val (tail_len:int64)) pt_in):byte list`;
          `val (tail_len:int64)`; `iv:int128`; `0:num`; `key1_lst:int128 list`;
          `key2_lst:int128 list`] LENGTH_OF_FST_OF_ENC_CIPHER_STEALING) THEN
        DISCH_TAC THEN
        IMP_REWRITE_TAC[SUB_LIST_APPEND_LEFT; ARITH_RULE `16 <= 16`] THEN

        REWRITE_TAC[cipher_stealing_encrypt; LET_DEF; LET_END_DEF] THEN
        REWRITE_TAC[SUB_LIST_OF_INT128_TO_BYTES;
          NUM_OF_BYTELIST_OF_INT128_TO_BYTES; CALCULATE_TWEAK_EXPAND] THEN
        EXPAND_TAC "combinedCC" THEN
        EXPAND_TAC "CC" THEN
        REWRITE_TAC[GSYM (ASSUME `0x10 * l1_curr_blocks = l1_curr_len`); ASSUME `l1_curr_blocks = 0x0`] THEN
        CONV_TAC NUM_REDUCE_CONV;
        ALL_TAC
      ] THEN

      SUBGOAL_THEN `l1_curr_blocks >= 1` ASSUME_TAC THENL
      [ UNDISCH_TAC `~(l1_curr_blocks + 0x1 < 0x2)` THEN ARITH_TAC; ALL_TAC] THEN

      IMP_REWRITE_TAC[ADD_SUB; ARITH_RULE `((l1_curr_blocks + 0x1) - 0x2) = l1_curr_blocks - 1`] THEN

      MP_TAC (SPECL [`0:num`; `(l1_curr_blocks - 1):num`; `pt_in:byte list`; `iv:int128`;
        `key1_lst:int128 list`; `key2_lst:int128 list`] LENGTH_OF_AES256_XTS_ENCRYPT_REC) THEN
      ASM_SIMP_TAC[ARITH_RULE `l1_curr_blocks >= 1 ==> ~(l1_curr_blocks - 1 < 0)`] THEN
      IMP_REWRITE_TAC[SUB_0; ARITH_RULE `l1_curr_blocks >= 1 ==> l1_curr_blocks - 1 + 1 = l1_curr_blocks`] THEN
      ONCE_REWRITE_TAC[ARITH_RULE `l1_curr_blocks * 16 = 16 * l1_curr_blocks`] THEN
      DISCH_TAC THEN
      IMP_REWRITE_TAC[SUB_LIST_APPEND_RIGHT_LEMMA] THEN

      REWRITE_TAC[aes256_xts_encrypt_tail] THEN
      ASM_SIMP_TAC[LET_DEF; LET_END_DEF] THEN

      MP_TAC (SPECL [`(SUB_LIST (l1_curr_blocks * 0x10,0x10) pt_in):byte list`;
        `(SUB_LIST ((l1_curr_blocks + 0x1) * 0x10,val (tail_len:int64)) pt_in):byte list`;
        `val (tail_len:int64)`; `iv:int128`; `l1_curr_blocks:num`; `key1_lst:int128 list`;
        `key2_lst:int128 list`] LENGTH_OF_FST_OF_ENC_CIPHER_STEALING) THEN
      DISCH_TAC THEN
      IMP_REWRITE_TAC[SUB_LIST_APPEND_LEFT; ARITH_RULE `16 <= 16`] THEN

      REWRITE_TAC[cipher_stealing_encrypt; LET_DEF; LET_END_DEF] THEN
      REWRITE_TAC[SUB_LIST_OF_INT128_TO_BYTES;
        NUM_OF_BYTELIST_OF_INT128_TO_BYTES; CALCULATE_TWEAK_EXPAND;
        ARITH_RULE `l1_curr_blocks * 16 = 16 * l1_curr_blocks`;
        ARITH_RULE `0x10 * (l1_curr_blocks + 0x1) = 16 * l1_curr_blocks + 16`] THEN
      EXPAND_TAC "combinedCC" THEN
      EXPAND_TAC "CC" THEN
      REWRITE_TAC[GSYM (ASSUME `0x10 * l1_curr_blocks = l1_curr_len`)];

      (* 4. Proving tail is correct
      `forall i.
     i < val tail_len
     ==> read (memory :> bytes8 (word_add (word_add ctxt_p (word (0x10 * l1_curr_blocks + 0x10)))
          (word i))) s33 =
         EL i (SUB_LIST (0x10 * l1_curr_blocks + 0x10,val tail_len)
           (aes256_xts_encrypt pt_in (0x10 * l1_curr_blocks + 0x10 + val tail_len) iv key1_lst key2_lst))` *)
      UNDISCH_TAC
        `forall i. i < val (tail_len:int64)
                  ==> read (memory :> bytes8 (word_add (word_add ctxt_p (word (l1_curr_len + 0x10)))
                                              (word i))) s33 =
                  EL i (SUB_LIST (0x0,val tail_len) (int128_to_bytes CC))` THEN
      REWRITE_TAC[GSYM (ASSUME `0x10 * l1_curr_blocks = l1_curr_len`)] THEN

      MP_TAC (SPECL [`val (tail_len:int64):num`; `(word_add ctxt_p (word (0x10 * l1_curr_blocks + 0x10))):int64`;
        `(SUB_LIST (0x0,val (tail_len:int64)) (int128_to_bytes CC)):byte list`;
        `s33:armstate`] BYTE_LIST_TO_NUM_THM) THEN
      ANTS_TAC THENL[
        REWRITE_TAC[LENGTH_SUB_LIST; LENGTH_OF_INT128_TO_BYTES] THEN
        CONV_TAC NUM_REDUCE_CONV THEN
        UNDISCH_TAC `val (tail_len:int64) < 0x10` THEN
        ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN (fun th -> REWRITE_TAC[th]) THEN
      MP_TAC (SPECL [`val (tail_len:int64):num`; `(word_add ctxt_p (word (0x10 * l1_curr_blocks + 0x10))):int64`;
        `(SUB_LIST (0x10 * l1_curr_blocks + 0x10,val (tail_len:int64))
            (aes256_xts_encrypt pt_in (0x10 * l1_curr_blocks + 0x10 + val tail_len) iv key1_lst key2_lst)):byte list`;
        `s33:armstate`] BYTE_LIST_TO_NUM_THM) THEN
      ANTS_TAC THENL[
        REWRITE_TAC[LENGTH_SUB_LIST] THEN
        IMP_REWRITE_TAC[LENGTH_OF_AES256_XTS_ENCRYPT] THEN
        ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN (fun th -> REWRITE_TAC[th]) THEN

      DISCH_THEN (fun th -> REWRITE_TAC[th]) THEN
      AP_TERM_TAC THEN
      REWRITE_TAC[SUB_LIST_IDEMPOTENT] THEN
      REWRITE_TAC[SUB_LIST_MIN_RIGHT; MIN; LE_REFL] THEN

      REWRITE_TAC[aes256_xts_encrypt;
        ARITH_RULE `~(0x10 * l1_curr_blocks + 0x10 + val (tail_len:int64) < 0x10)`] THEN
      REWRITE_TAC[ARITH_RULE `0x10 * l1_curr_blocks + 0x10 + val tail_len =
                      0x10 * (l1_curr_blocks + 1) + val tail_len`] THEN
      REWRITE_TAC[MOD_MULT_ADD] THEN
      ASM_SIMP_TAC[MOD_LT] THEN
      REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
      REWRITE_TAC[ARITH_RULE
        `((0x10 * (l1_curr_blocks + 0x1) + val tail_len) - val tail_len) DIV 0x10 =
        (0x10 * (l1_curr_blocks + 0x1)) DIV 0x10`] THEN
      IMP_REWRITE_TAC[DIV_MULT; ARITH_RULE `~(16 = 0)`] THEN
      COND_CASES_TAC THENL
      [ (* `l1_curr_blocks + 0x1 < 0x2` *)
        SUBGOAL_THEN `l1_curr_blocks = 0` SUBST_ALL_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
        REWRITE_TAC[aes256_xts_encrypt_tail] THEN
        ASM_SIMP_TAC[LET_DEF; LET_END_DEF] THEN
        CONV_TAC NUM_REDUCE_CONV THEN

        MP_TAC (SPECL [`(SUB_LIST (0,0x10) pt_in):byte list`;
          `(SUB_LIST (0x10,val (tail_len:int64)) pt_in):byte list`;
          `val (tail_len:int64)`; `iv:int128`; `0:num`; `key1_lst:int128 list`;
          `key2_lst:int128 list`] LENGTH_OF_FST_OF_ENC_CIPHER_STEALING) THEN
        REWRITE_TAC[GSYM (ASSUME `0x10 * 0x0 = l1_curr_len`)] THEN
        DISCH_TAC THEN
        IMP_REWRITE_TAC[SUB_LIST_APPEND_RIGHT_LEMMA; ARITH_RULE `16 <= 16`] THEN

        REWRITE_TAC[cipher_stealing_encrypt; LET_DEF; LET_END_DEF; SUB_LIST_IDEMPOTENT] THEN
        EXPAND_TAC "CC" THEN
        REWRITE_TAC[GSYM (ASSUME `0x10 * 0x0 = l1_curr_len`)] THEN
        CONV_TAC NUM_REDUCE_CONV;
        ALL_TAC
      ] THEN

      SUBGOAL_THEN `l1_curr_blocks >= 1` ASSUME_TAC THENL
      [ UNDISCH_TAC `~(l1_curr_blocks + 0x1 < 0x2)` THEN ARITH_TAC; ALL_TAC] THEN

      IMP_REWRITE_TAC[ADD_SUB; ARITH_RULE `((l1_curr_blocks + 0x1) - 0x2) = l1_curr_blocks - 1`] THEN
      REWRITE_TAC[GSYM (ASSUME `0x10 * l1_curr_blocks = l1_curr_len`)] THEN

      MP_TAC (ISPECL [`(aes256_xts_encrypt_rec 0x0 (l1_curr_blocks - 0x1) pt_in iv key1_lst key2_lst):byte list`;
        `(aes256_xts_encrypt_tail l1_curr_blocks (val (tail_len:int64)) pt_in iv key1_lst key2_lst):byte list`;
        `0x10 * l1_curr_blocks + 0x10:num`; `val (tail_len:int64)`; `0x10 * l1_curr_blocks:num`
        ] SUB_LIST_APPEND_RIGHT_GENERAL) THEN
      ANTS_TAC THENL
      [ REWRITE_TAC[LENGTH_OF_AES256_XTS_ENCRYPT_REC] THEN
        UNDISCH_TAC `l1_curr_blocks >= 1` THEN
        ARITH_TAC; ALL_TAC] THEN
      ANTS_TAC THENL [ ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN (fun th -> REWRITE_TAC[th]) THEN

      REWRITE_TAC[ARITH_RULE `(0x10 * l1_curr_blocks + 0x10) - 0x10 * l1_curr_blocks = 0x10`] THEN
      REWRITE_TAC[aes256_xts_encrypt_tail] THEN
      ASM_SIMP_TAC[LET_DEF; LET_END_DEF] THEN

      MP_TAC (SPECL [`(SUB_LIST (l1_curr_blocks * 0x10,0x10) pt_in):byte list`;
        `(SUB_LIST ((l1_curr_blocks + 0x1) * 0x10,val (tail_len:int64)) pt_in):byte list`;
        `val (tail_len:int64)`; `iv:int128`; `l1_curr_blocks:num`; `key1_lst:int128 list`;
        `key2_lst:int128 list`] LENGTH_OF_FST_OF_ENC_CIPHER_STEALING) THEN
      DISCH_TAC THEN
      IMP_REWRITE_TAC[SUB_LIST_APPEND_RIGHT_LEMMA; ARITH_RULE `16 <= 16`] THEN

      REWRITE_TAC[cipher_stealing_encrypt; LET_DEF; LET_END_DEF; SUB_LIST_IDEMPOTENT] THEN
      EXPAND_TAC "CC" THEN
      REWRITE_TAC[GSYM (ASSUME `0x10 * l1_curr_blocks = l1_curr_len`)] THEN
      REWRITE_TAC[ARITH_RULE `l1_curr_blocks * 0x10 = 0x10 * l1_curr_blocks`]
    ]
  ] (* end of loop invariant proof. *)
);;


(* Proof: Less than 2 blocks *)
let AES_XTS_ENCRYPT_LT_2BLOCK_CORRECT = time prove(
  `!ptxt_p ctxt_p len key1_p key2_p iv_p
    pt_in iv
    k1_0 k1_1 k1_2 k1_3 k1_4 k1_5 k1_6 k1_7 k1_8 k1_9 k1_10 k1_11 k1_12 k1_13 k1_14
    k2_0 k2_1 k2_2 k2_3 k2_4 k2_5 k2_6 k2_7 k2_8 k2_9 k2_10 k2_11 k2_12 k2_13 k2_14
    pc.
    PAIRWISE nonoverlapping
    [(word pc, LENGTH aes256_xts_encrypt_mc);
    (ptxt_p, val len);
    (ctxt_p, val len);
    (key1_p, 244);
    (key2_p, 244)] /\
    val len >= 16 /\ val len < 0x20 /\ LENGTH pt_in = val len /\
    [k1_0; k1_1; k1_2; k1_3; k1_4; k1_5; k1_6; k1_7; k1_8; k1_9; k1_10;
       k1_11; k1_12; k1_13; k1_14] = key1_lst /\
    [k2_0; k2_1; k2_2; k2_3; k2_4; k2_5; k2_6; k2_7; k2_8; k2_9; k2_10;
       k2_11; k2_12; k2_13; k2_14] = key2_lst
    ==> ensures arm
    (\s. aligned_bytes_loaded s (word pc) aes256_xts_encrypt_mc /\
         read PC s = word (pc + 0x1c) /\
         C_ARGUMENTS [ptxt_p; ctxt_p; len; key1_p; key2_p; iv_p] s /\
         byte_list_at pt_in ptxt_p len s /\
           read(memory :> bytes128 iv_p) s = iv /\
           set_key_schedule s key1_p k1_0 k1_1 k1_2 k1_3 k1_4 k1_5 k1_6 k1_7 k1_8 k1_9 k1_10 k1_11 k1_12 k1_13 k1_14 /\
           set_key_schedule s key2_p k2_0 k2_1 k2_2 k2_3 k2_4 k2_5 k2_6 k2_7 k2_8 k2_9 k2_10 k2_11 k2_12 k2_13 k2_14)
      (\s. read PC s = word (pc + 0xa8c) /\ //LENGTH aes256_xts_encrypt_mc - 8*4 = 0xaac - 0x8 * 0x4
           byte_list_at (aes256_xts_encrypt pt_in (val len) iv key1_lst key2_lst) ctxt_p len s
      )
    (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI,,
     MAYCHANGE [X19; X20; X21; X22],,
     MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15],,
     MAYCHANGE [memory :> bytes(ctxt_p, val len)])
    `,
  REWRITE_TAC [(REWRITE_CONV [aes256_xts_encrypt_mc] THENC LENGTH_CONV) `LENGTH aes256_xts_encrypt_mc`] THEN
  REWRITE_TAC[set_key_schedule; byte_list_at; C_ARGUMENTS; SOME_FLAGS; PAIRWISE; ALL;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REPEAT STRIP_TAC THEN

  SUBGOAL_THEN `word_add (word_and len (word 0xf))
    (word_and len (word 0xfffffffffffffff0)) = len:int64` ASSUME_TAC THENL
  [REWRITE_TAC[word_split_lemma]; ALL_TAC] THEN
  ABBREV_TAC `len_full_blocks:int64 = word_and len (word 0xfffffffffffffff0)` THEN
  ABBREV_TAC `tail_len:int64 = word_and len (word 0xf)` THEN
  ABBREV_TAC `num_5blocks = (word (val (len_full_blocks:int64) DIV 0x50)):int64` THEN

  SUBGOAL_THEN `val (len_full_blocks:int64) = 16` ASSUME_TAC THENL
  [ EXPAND_TAC "len_full_blocks" THEN
    REWRITE_TAC[NUM_BLOCKS_TO_VAL] THEN
    IMP_REWRITE_TAC[VAL_WORD; DIMINDEX_64; MOD_LT] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    SUBGOAL_THEN `val (len:int64) DIV 16 = 1` SUBST1_TAC THENL
    [ MATCH_MP_TAC(MESON[LE_ANTISYM] `m <= n /\ n <= m ==> m = n`) THEN
      CONJ_TAC THENL [ ASM_ARITH_TAC; ASM_ARITH_TAC];
      ALL_TAC] THEN
    ARITH_TAC; ALL_TAC] THEN

  (* Prove property until start of cipher stealing. *)
  ENSURES_SEQUENCE_TAC `pc + 0x9e0`
  `\s.
    read X0 s = word_add ptxt_p (word (acc_len num_5blocks len_full_blocks)) /\
    read X1 s = word_add ctxt_p (word (acc_len num_5blocks len_full_blocks)) /\
    read X3 s = key1_p /\
    read X21 s = tail_len /\
    read Q6 s = calculate_tweak (acc_blocks num_5blocks len_full_blocks T) iv key2_lst /\
    read X19 s = word 0x87 /\
    read Q16 s = k1_0 /\ read Q17 s = k1_1 /\ read Q12 s = k1_2 /\ read Q13 s = k1_3 /\
    read Q14 s = k1_4 /\ read Q15 s = k1_5 /\ read Q4 s = k1_6 /\ read Q5 s = k1_7 /\
    read Q18 s = k1_8 /\ read Q19 s = k1_9 /\ read Q20 s = k1_10 /\ read Q21 s = k1_11 /\
    read Q22 s = k1_12 /\ read Q23 s = k1_13 /\ read Q7 s = k1_14 /\
    byte_list_at pt_in ptxt_p len s /\
    byte_list_at (aes256_xts_encrypt pt_in (acc_len num_5blocks len_full_blocks) iv key1_lst key2_lst)
                ctxt_p (word (acc_len num_5blocks len_full_blocks)) s` THEN
  CONJ_TAC THENL
  [
    MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN
    EXISTS_TAC `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
      MAYCHANGE [X19; X20; X21; X22],,
      MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15],,
      MAYCHANGE [memory :> bytes128 ctxt_p]` THEN
    REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    CONJ_TAC THENL [
    REPEAT (GEN_REWRITE_TAC ONCE_DEPTH_CONV [GSYM SEQ_ASSOC] THEN
            MATCH_MP_TAC SUBSUMED_SEQ THEN REWRITE_TAC[SUBSUMED_REFL]) THEN
    ABBREV_TAC `vallen = val (len:int64)` THEN
    SUBSUMED_MAYCHANGE_TAC; ALL_TAC] THEN

    REWRITE_TAC[byte_list_at] THEN
    ENSURES_INIT_TAC "s0" THEN
    ARM_ACCSTEPS_TAC AES256_XTS_ENCRYPT_EXEC [] (1--2) THEN

    (* Discharge if condition *)
    SUBGOAL_THEN
      `ival (word_sub (len:int64) (word 0x10)) < &0x0
      <=> ~(ival (len:int64) - &0x10 = ival (word_sub (len:int64) (word 0x10)))` MP_TAC THENL
    [ MP_TAC (BITBLAST_RULE (* put in tips doc. Q: When to use it vs. ARITH_RULE? *)
        `val (len:int64) >= 0x10 ==> val len < 0x20 ==>
        ival (word_sub len (word 0x10)) >= &0x0`) THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC (BITBLAST_RULE
        `val (len:int64) >= 0x10 ==> val len < 0x20 ==>
         ival (len:int64) - &0x10 = ival (word_sub len (word 0x10))`) THEN
      ASM_REWRITE_TAC[] THEN
      ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN

    MP_TAC (SPECL [`ptxt_p:int64`; `len:int64`; `pt_in:byte list`; `s2:armstate`] READ_LT_2BLOCK) THEN
    ASM_SIMP_TAC[] THEN DISCH_TAC THEN

    ARM_ACCSTEPS_TAC AES256_XTS_ENCRYPT_EXEC [] (3--65) THEN
    (* Prove Q6 stores initial tweak *)
    FIRST_X_ASSUM(MP_TAC o SPEC `(calculate_tweak 0 iv key2_lst)`
      o  MATCH_MP (MESON[] `read Q6 s = a ==> !a'. a = a' ==> read Q6 s = a'`)) THEN
    ANTS_TAC THENL
    [ REWRITE_TAC[CONJUNCT1 calculate_tweak; xts_init_tweak] THEN
      EXPAND_TAC "key2_lst" THEN AESENC_TAC; DISCH_TAC] THEN

    (* Simulating until branching into tail1x *)
    ARM_ACCSTEPS_TAC AES256_XTS_ENCRYPT_EXEC [] (66--77) THEN
    (* Simulate AES-XTS encryption of block in Q0 *)
    ARM_ACCSTEPS_TAC AES256_XTS_ENCRYPT_EXEC [] (78--108) THEN
    XTSENC_TAC `Q0:(armstate,int128)component` `0` `0` THEN

    ARM_ACCSTEPS_TAC AES256_XTS_ENCRYPT_EXEC [] (109--118) THEN (* until b .Lxts_enc_done = arm_B (word 0x8) *)
    TWEAK_TAC `Q6:(armstate,int128)component` `1:num` `0:num` THEN

    SUBGOAL_THEN `val (num_5blocks:int64) = 0` ASSUME_TAC THENL
    [ EXPAND_TAC "num_5blocks" THEN
      UNDISCH_TAC `val (len_full_blocks:int64) = 0x10` THEN
      SIMP_TAC[] THEN DISCH_TAC THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC[VAL_WORD_0]; ALL_TAC ] THEN

    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    (* `word_add ptxt_p (word 0x10) = word_add ptxt_p (word (acc_len num_5blocks len_full_blocks)) /\
        word_add ctxt_p (word 0x10) = word_add ctxt_p (word (acc_len num_5blocks len_full_blocks)) /\
        calculate_tweak 0x1 iv key2_lst = calculate_tweak (acc_blocks num_5blocks len_full_blocks true) iv key2_lst /\
        (forall i.
              i < val (word (acc_len num_5blocks len_full_blocks))
              ==> read (memory :> bytes8 (word_add ctxt_p (word i))) s118 =
                  EL i  (aes256_xts_encrypt pt_in (acc_len num_5blocks len_full_blocks) iv  key1_lst key2_lst))` *)
    REPEAT CONJ_TAC THENL
    [
      ASM_REWRITE_TAC[acc_len] THEN CONV_TAC NUM_REDUCE_CONV;

      ASM_REWRITE_TAC[acc_len] THEN CONV_TAC NUM_REDUCE_CONV;

      ASM_REWRITE_TAC[acc_blocks] THEN CONV_TAC NUM_REDUCE_CONV;

      ASM_REWRITE_TAC[acc_len] THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      IMP_REWRITE_TAC[VAL_WORD; DIMINDEX_64; MOD_LT] THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      MP_TAC (SPECL [`0x10`; `ctxt_p:int64`; `(aes256_xts_encrypt pt_in 0x10 iv key1_lst key2_lst):byte list`;
                `s118:armstate`] BYTE_LIST_TO_NUM_THM) THEN
      ANTS_TAC THENL [
        MP_TAC (SPECL [`1`; `pt_in:byte list`; `iv:int128`; `key1_lst:int128 list`; `key2_lst:int128 list`]
                      LENGTH_OF_AES256_XTS_ENCRYPT_FULL_BLOCKS) THEN
        ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN (fun th -> REWRITE_TAC[th]) THEN
      IMP_REWRITE_TAC[READ_BYTES_EQ_READ_BYTE128_1BLOCK_ENC]
    ]
  ; ALL_TAC] THEN

  (* Reuse the cipher stealing proof *)
  MP_TAC CIPHER_STEALING_ENC_CORRECT THEN
  REWRITE_TAC [(REWRITE_CONV [aes256_xts_encrypt_mc] THENC LENGTH_CONV) `LENGTH aes256_xts_encrypt_mc`] THEN
  REWRITE_TAC[byte_list_at; PAIRWISE; ALL; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  ASM_SIMP_TAC[] THEN
  ASM_ARITH_TAC
);;

(* Proof: Less than 3 blocks *)
let AES_XTS_ENCRYPT_LT_3BLOCK_CORRECT = time prove(
  `!ptxt_p ctxt_p len key1_p key2_p iv_p
    pt_in iv
    k1_0 k1_1 k1_2 k1_3 k1_4 k1_5 k1_6 k1_7 k1_8 k1_9 k1_10 k1_11 k1_12 k1_13 k1_14
    k2_0 k2_1 k2_2 k2_3 k2_4 k2_5 k2_6 k2_7 k2_8 k2_9 k2_10 k2_11 k2_12 k2_13 k2_14
    pc.
    PAIRWISE nonoverlapping
    [(word pc, LENGTH aes256_xts_encrypt_mc);
    (ptxt_p, val len);
    (ctxt_p, val len);
    (key1_p, 244);
    (key2_p, 244)] /\
    ~(val len < 0x20) /\ val len < 0x30 /\ LENGTH pt_in = val len /\
    [k1_0; k1_1; k1_2; k1_3; k1_4; k1_5; k1_6; k1_7; k1_8; k1_9; k1_10;
       k1_11; k1_12; k1_13; k1_14] = key1_lst /\
    [k2_0; k2_1; k2_2; k2_3; k2_4; k2_5; k2_6; k2_7; k2_8; k2_9; k2_10;
       k2_11; k2_12; k2_13; k2_14] = key2_lst
    ==> ensures arm
    (\s. aligned_bytes_loaded s (word pc) aes256_xts_encrypt_mc /\
         read PC s = word (pc + 0x1c) /\
         C_ARGUMENTS [ptxt_p; ctxt_p; len; key1_p; key2_p; iv_p] s /\
         byte_list_at pt_in ptxt_p len s /\
           read(memory :> bytes128 iv_p) s = iv /\
           set_key_schedule s key1_p k1_0 k1_1 k1_2 k1_3 k1_4 k1_5 k1_6 k1_7 k1_8 k1_9 k1_10 k1_11 k1_12 k1_13 k1_14 /\
           set_key_schedule s key2_p k2_0 k2_1 k2_2 k2_3 k2_4 k2_5 k2_6 k2_7 k2_8 k2_9 k2_10 k2_11 k2_12 k2_13 k2_14)
      (\s. read PC s = word (pc + 0xa8c) /\ //LENGTH aes256_xts_encrypt_mc - 8*4 = 0xaac - 0x8 * 0x4
           byte_list_at (aes256_xts_encrypt pt_in (val len) iv key1_lst key2_lst) ctxt_p len s
      )
    (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI,,
     MAYCHANGE [X19; X20; X21; X22],,
     MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15],,
     MAYCHANGE [memory :> bytes(ctxt_p, val len)])
    `,
  REWRITE_TAC [(REWRITE_CONV [aes256_xts_encrypt_mc] THENC LENGTH_CONV) `LENGTH aes256_xts_encrypt_mc`] THEN
  REWRITE_TAC[set_key_schedule; byte_list_at; C_ARGUMENTS; SOME_FLAGS; PAIRWISE; ALL;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REPEAT STRIP_TAC THEN

  SUBGOAL_THEN `word_add (word_and len (word 0xf))
    (word_and len (word 0xfffffffffffffff0)) = len:int64` ASSUME_TAC THENL
  [REWRITE_TAC[word_split_lemma]; ALL_TAC] THEN
  ABBREV_TAC `len_full_blocks:int64 = word_and len (word 0xfffffffffffffff0)` THEN
  ABBREV_TAC `tail_len:int64 = word_and len (word 0xf)` THEN
  ABBREV_TAC `num_5blocks = (word (val (len_full_blocks:int64) DIV 0x50)):int64` THEN

  SUBGOAL_THEN `val (len_full_blocks:int64) = 0x20` ASSUME_TAC THENL
  [ EXPAND_TAC "len_full_blocks" THEN
    REWRITE_TAC[NUM_BLOCKS_TO_VAL] THEN
    IMP_REWRITE_TAC[VAL_WORD; DIMINDEX_64; MOD_LT] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    SUBGOAL_THEN `val (len:int64) DIV 16 = 2` SUBST1_TAC THENL
    [ MATCH_MP_TAC(MESON[LE_ANTISYM] `m <= n /\ n <= m ==> m = n`) THEN
      CONJ_TAC THENL [ ASM_ARITH_TAC; ASM_ARITH_TAC];
      ALL_TAC] THEN
    ARITH_TAC; ALL_TAC] THEN

  SUBGOAL_THEN `val (num_5blocks:int64) = 0` ASSUME_TAC THENL
  [ EXPAND_TAC "num_5blocks" THEN
    UNDISCH_TAC `val (len_full_blocks:int64) = 0x20` THEN
    SIMP_TAC[] THEN DISCH_TAC THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[VAL_WORD_0]; ALL_TAC ] THEN

  (* Prove property until start of cipher stealing. *)
  ENSURES_SEQUENCE_TAC `pc + 0x9e0`
  `\s.
    read X0 s = word_add ptxt_p (word (acc_len num_5blocks len_full_blocks)) /\
    read X1 s = word_add ctxt_p (word (acc_len num_5blocks len_full_blocks)) /\
    read X3 s = key1_p /\
    read X21 s = tail_len /\
    read Q6 s = calculate_tweak (acc_blocks num_5blocks len_full_blocks T) iv key2_lst /\
    read X19 s = word 0x87 /\
    read Q16 s = k1_0 /\ read Q17 s = k1_1 /\ read Q12 s = k1_2 /\ read Q13 s = k1_3 /\
    read Q14 s = k1_4 /\ read Q15 s = k1_5 /\ read Q4 s = k1_6 /\ read Q5 s = k1_7 /\
    read Q18 s = k1_8 /\ read Q19 s = k1_9 /\ read Q20 s = k1_10 /\ read Q21 s = k1_11 /\
    read Q22 s = k1_12 /\ read Q23 s = k1_13 /\ read Q7 s = k1_14 /\
    byte_list_at pt_in ptxt_p len s /\
    byte_list_at (aes256_xts_encrypt pt_in (acc_len num_5blocks len_full_blocks) iv key1_lst key2_lst)
                ctxt_p (word (acc_len num_5blocks len_full_blocks)) s` THEN
  CONJ_TAC THENL
  [
    MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN
    EXISTS_TAC `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
      MAYCHANGE [X19; X20; X21; X22],,
      MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15],,
      MAYCHANGE [memory :> bytes128 ctxt_p;
                 memory :> bytes128 (word_add ctxt_p (word 0x10))]` THEN
    REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    CONJ_TAC THENL [
    REPEAT (GEN_REWRITE_TAC ONCE_DEPTH_CONV [GSYM SEQ_ASSOC] THEN
            MATCH_MP_TAC SUBSUMED_SEQ THEN REWRITE_TAC[SUBSUMED_REFL]) THEN
    ABBREV_TAC `vallen = val (len:int64)` THEN
    SUBSUMED_MAYCHANGE_TAC; ALL_TAC] THEN

    REWRITE_TAC[byte_list_at] THEN
    ENSURES_INIT_TAC "s0" THEN
    ARM_ACCSTEPS_TAC AES256_XTS_ENCRYPT_EXEC [] (1--2) THEN

    (* Discharge if condition *)
    SUBGOAL_THEN
      `ival (word_sub (len:int64) (word 0x10)) < &0x0
      <=> ~(ival (len:int64) - &0x10 = ival (word_sub (len:int64) (word 0x10)))` MP_TAC THENL
    [ MP_TAC (BITBLAST_RULE (* put in tips doc. Q: When to use it vs. ARITH_RULE? *)
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

    MP_TAC (SPECL [`ptxt_p:int64`; `len:int64`; `pt_in:byte list`; `s2:armstate`] READ_LT_3BLOCK) THEN
    ASM_SIMP_TAC[] THEN  REPEAT STRIP_TAC THEN

    ARM_ACCSTEPS_TAC AES256_XTS_ENCRYPT_EXEC [] (3--65) THEN
    (* Prove Q6 stores initial tweak *)
    FIRST_X_ASSUM(MP_TAC o SPEC `(calculate_tweak 0 iv key2_lst)`
      o  MATCH_MP (MESON[] `read Q6 s = a ==> !a'. a = a' ==> read Q6 s = a'`)) THEN
    ANTS_TAC THENL
    [ REWRITE_TAC[CONJUNCT1 calculate_tweak; xts_init_tweak] THEN
      EXPAND_TAC "key2_lst" THEN AESENC_TAC; DISCH_TAC] THEN

    (* Simulating until branching into tail2x *)
    ARM_ACCSTEPS_TAC AES256_XTS_ENCRYPT_EXEC [] (66--87) THEN
    TWEAK_TAC `Q8:(armstate,int128)component` `1:num` `0:num` THEN
    (* Simulate AES-XTS encryption of blocks in Q0, Q1 *)
    ARM_ACCSTEPS_TAC AES256_XTS_ENCRYPT_EXEC [] (88--148) THEN
    XTSENC_TAC `Q0:(armstate,int128)component`    `0` `0` THEN
    XTSENC_TAC `Q1:(armstate,int128)component` `0x10` `1` THEN
    (* until b .Lxts_enc_done = arm_B (word xxx) *)
    ARM_ACCSTEPS_TAC AES256_XTS_ENCRYPT_EXEC [] (149--158) THEN
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
      MP_TAC (SPECL [`0x20`; `ctxt_p:int64`; `(aes256_xts_encrypt pt_in 0x20 iv key1_lst key2_lst):byte list`;
                `s158:armstate`] BYTE_LIST_TO_NUM_THM) THEN
      ANTS_TAC THENL [
        MP_TAC (SPECL [`2`; `pt_in:byte list`; `iv:int128`; `key1_lst:int128 list`; `key2_lst:int128 list`]
                      LENGTH_OF_AES256_XTS_ENCRYPT_FULL_BLOCKS) THEN
        ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN (fun th -> REWRITE_TAC[th]) THEN
      IMP_REWRITE_TAC[READ_BYTES_EQ_READ_BYTE128_2BLOCKS_ENC]
    ]
  ; ALL_TAC] THEN

  (* Reuse the cipher stealing proof *)
  MP_TAC CIPHER_STEALING_ENC_CORRECT THEN
  REWRITE_TAC [(REWRITE_CONV [aes256_xts_encrypt_mc] THENC LENGTH_CONV) `LENGTH aes256_xts_encrypt_mc`] THEN
  REWRITE_TAC[byte_list_at; PAIRWISE; ALL; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  ASM_SIMP_TAC[] THEN
  ASM_ARITH_TAC
);;

(* Proof: Less than 4 blocks *)
let AES_XTS_ENCRYPT_LT_4BLOCK_CORRECT = time prove(
  `!ptxt_p ctxt_p len key1_p key2_p iv_p
    pt_in iv
    k1_0 k1_1 k1_2 k1_3 k1_4 k1_5 k1_6 k1_7 k1_8 k1_9 k1_10 k1_11 k1_12 k1_13 k1_14
    k2_0 k2_1 k2_2 k2_3 k2_4 k2_5 k2_6 k2_7 k2_8 k2_9 k2_10 k2_11 k2_12 k2_13 k2_14
    pc.
    PAIRWISE nonoverlapping
    [(word pc, LENGTH aes256_xts_encrypt_mc);
    (ptxt_p, val len);
    (ctxt_p, val len);
    (key1_p, 244);
    (key2_p, 244)] /\
    ~(val len < 0x30) /\ val len < 0x40 /\ LENGTH pt_in = val len /\
    [k1_0; k1_1; k1_2; k1_3; k1_4; k1_5; k1_6; k1_7; k1_8; k1_9; k1_10;
       k1_11; k1_12; k1_13; k1_14] = key1_lst /\
    [k2_0; k2_1; k2_2; k2_3; k2_4; k2_5; k2_6; k2_7; k2_8; k2_9; k2_10;
       k2_11; k2_12; k2_13; k2_14] = key2_lst
    ==> ensures arm
    (\s. aligned_bytes_loaded s (word pc) aes256_xts_encrypt_mc /\
         read PC s = word (pc + 0x1c) /\
         C_ARGUMENTS [ptxt_p; ctxt_p; len; key1_p; key2_p; iv_p] s /\
         byte_list_at pt_in ptxt_p len s /\
           read(memory :> bytes128 iv_p) s = iv /\
           set_key_schedule s key1_p k1_0 k1_1 k1_2 k1_3 k1_4 k1_5 k1_6 k1_7 k1_8 k1_9 k1_10 k1_11 k1_12 k1_13 k1_14 /\
           set_key_schedule s key2_p k2_0 k2_1 k2_2 k2_3 k2_4 k2_5 k2_6 k2_7 k2_8 k2_9 k2_10 k2_11 k2_12 k2_13 k2_14)
      (\s. read PC s = word (pc + 0xa8c) /\ //LENGTH aes256_xts_encrypt_mc - 8*4 = 0xaac - 0x8 * 0x4
           byte_list_at (aes256_xts_encrypt pt_in (val len) iv key1_lst key2_lst) ctxt_p len s
      )
    (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI,,
     MAYCHANGE [X19; X20; X21; X22],,
     MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15],,
     MAYCHANGE [memory :> bytes(ctxt_p, val len)])
    `,
  REWRITE_TAC [(REWRITE_CONV [aes256_xts_encrypt_mc] THENC LENGTH_CONV) `LENGTH aes256_xts_encrypt_mc`] THEN
  REWRITE_TAC[set_key_schedule; byte_list_at; C_ARGUMENTS; SOME_FLAGS; PAIRWISE; ALL;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REPEAT STRIP_TAC THEN

  SUBGOAL_THEN `word_add (word_and len (word 0xf))
    (word_and len (word 0xfffffffffffffff0)) = len:int64` ASSUME_TAC THENL
  [REWRITE_TAC[word_split_lemma]; ALL_TAC] THEN
  ABBREV_TAC `len_full_blocks:int64 = word_and len (word 0xfffffffffffffff0)` THEN
  ABBREV_TAC `tail_len:int64 = word_and len (word 0xf)` THEN
  ABBREV_TAC `num_5blocks = (word (val (len_full_blocks:int64) DIV 0x50)):int64` THEN

  SUBGOAL_THEN `val (len_full_blocks:int64) = 0x30` ASSUME_TAC THENL
  [ EXPAND_TAC "len_full_blocks" THEN
    REWRITE_TAC[NUM_BLOCKS_TO_VAL] THEN
    IMP_REWRITE_TAC[VAL_WORD; DIMINDEX_64; MOD_LT] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    SUBGOAL_THEN `val (len:int64) DIV 16 = 3` SUBST1_TAC THENL
    [ MATCH_MP_TAC(MESON[LE_ANTISYM] `m <= n /\ n <= m ==> m = n`) THEN
      CONJ_TAC THENL [ ASM_ARITH_TAC; ASM_ARITH_TAC];
      ALL_TAC] THEN
    ARITH_TAC; ALL_TAC] THEN

  SUBGOAL_THEN `val (num_5blocks:int64) = 0` ASSUME_TAC THENL
  [ EXPAND_TAC "num_5blocks" THEN
    UNDISCH_TAC `val (len_full_blocks:int64) = 0x30` THEN
    SIMP_TAC[] THEN DISCH_TAC THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[VAL_WORD_0]; ALL_TAC ] THEN

  (* Prove property until start of cipher stealing. *)
  ENSURES_SEQUENCE_TAC `pc + 0x9e0`
  `\s.
    read X0 s = word_add ptxt_p (word (acc_len num_5blocks len_full_blocks)) /\
    read X1 s = word_add ctxt_p (word (acc_len num_5blocks len_full_blocks)) /\
    read X3 s = key1_p /\
    read X21 s = tail_len /\
    read Q6 s = calculate_tweak (acc_blocks num_5blocks len_full_blocks T) iv key2_lst /\
    read X19 s = word 0x87 /\
    read Q16 s = k1_0 /\ read Q17 s = k1_1 /\ read Q12 s = k1_2 /\ read Q13 s = k1_3 /\
    read Q14 s = k1_4 /\ read Q15 s = k1_5 /\ read Q4 s = k1_6 /\ read Q5 s = k1_7 /\
    read Q18 s = k1_8 /\ read Q19 s = k1_9 /\ read Q20 s = k1_10 /\ read Q21 s = k1_11 /\
    read Q22 s = k1_12 /\ read Q23 s = k1_13 /\ read Q7 s = k1_14 /\
    byte_list_at pt_in ptxt_p len s /\
    byte_list_at (aes256_xts_encrypt pt_in (acc_len num_5blocks len_full_blocks) iv key1_lst key2_lst)
                ctxt_p (word (acc_len num_5blocks len_full_blocks)) s` THEN
  CONJ_TAC THENL
  [
    MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN
    EXISTS_TAC `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
      MAYCHANGE [X19; X20; X21; X22],,
      MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15],,
      MAYCHANGE [memory :> bytes128 ctxt_p;
                 memory :> bytes128 (word_add ctxt_p (word 0x10));
                 memory :> bytes128 (word_add ctxt_p (word 0x20))]` THEN
    REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    CONJ_TAC THENL [
    REPEAT (GEN_REWRITE_TAC ONCE_DEPTH_CONV [GSYM SEQ_ASSOC] THEN
            MATCH_MP_TAC SUBSUMED_SEQ THEN REWRITE_TAC[SUBSUMED_REFL]) THEN
    ABBREV_TAC `vallen = val (len:int64)` THEN
    SUBSUMED_MAYCHANGE_TAC; ALL_TAC] THEN

    REWRITE_TAC[byte_list_at] THEN
    ENSURES_INIT_TAC "s0" THEN
    ARM_ACCSTEPS_TAC AES256_XTS_ENCRYPT_EXEC [] (1--2) THEN

    (* Discharge if condition *)
    SUBGOAL_THEN
      `ival (word_sub (len:int64) (word 0x10)) < &0x0
      <=> ~(ival (len:int64) - &0x10 = ival (word_sub (len:int64) (word 0x10)))` MP_TAC THENL
    [ MP_TAC (BITBLAST_RULE (* put in tips doc. Q: When to use it vs. ARITH_RULE? *)
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

    MP_TAC (SPECL [`ptxt_p:int64`; `len:int64`; `pt_in:byte list`; `s2:armstate`] READ_LT_4BLOCK) THEN
    ASM_SIMP_TAC[] THEN  REPEAT STRIP_TAC THEN

    ARM_ACCSTEPS_TAC AES256_XTS_ENCRYPT_EXEC [] (3--65) THEN
    (* Prove Q6 stores initial tweak *)
    FIRST_X_ASSUM(MP_TAC o SPEC `(calculate_tweak 0 iv key2_lst)`
      o  MATCH_MP (MESON[] `read Q6 s = a ==> !a'. a = a' ==> read Q6 s = a'`)) THEN
    ANTS_TAC THENL
    [ REWRITE_TAC[CONJUNCT1 calculate_tweak; xts_init_tweak] THEN
      EXPAND_TAC "key2_lst" THEN AESENC_TAC; DISCH_TAC] THEN

    (* Simulating until branching into tail3x *)
    ARM_ACCSTEPS_TAC AES256_XTS_ENCRYPT_EXEC [] (66--87) THEN
    TWEAK_TAC `Q8:(armstate,int128)component` `1:num` `0:num` THEN
    ARM_ACCSTEPS_TAC AES256_XTS_ENCRYPT_EXEC [] (88--95) THEN
    TWEAK_TAC `Q9:(armstate,int128)component` `2:num` `1:num` THEN
    (* Simulate AES-XTS encryption of block in Q0, Q1, Q24 *)
    ARM_ACCSTEPS_TAC AES256_XTS_ENCRYPT_EXEC [] (96--187) THEN
    XTSENC_TAC  `Q0:(armstate,int128)component`    `0` `0` THEN
    XTSENC_TAC  `Q1:(armstate,int128)component` `0x10` `1` THEN
    XTSENC_TAC `Q24:(armstate,int128)component` `0x20` `2` THEN
    (* until b .Lxts_enc_done = arm_B (word xxx) *)
    ARM_ACCSTEPS_TAC AES256_XTS_ENCRYPT_EXEC [] (188--198) THEN
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
      MP_TAC (SPECL [`0x30`; `ctxt_p:int64`; `(aes256_xts_encrypt pt_in 0x30 iv key1_lst key2_lst):byte list`;
                `s198:armstate`] BYTE_LIST_TO_NUM_THM) THEN
      ANTS_TAC THENL [
        MP_TAC (SPECL [`3`; `pt_in:byte list`; `iv:int128`; `key1_lst:int128 list`; `key2_lst:int128 list`]
                      LENGTH_OF_AES256_XTS_ENCRYPT_FULL_BLOCKS) THEN
        ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN (fun th -> REWRITE_TAC[th]) THEN
      IMP_REWRITE_TAC[READ_BYTES_EQ_READ_BYTE128_3BLOCKS_ENC]
    ]
  ; ALL_TAC] THEN

  (* Reuse the cipher stealing proof *)
  MP_TAC CIPHER_STEALING_ENC_CORRECT THEN
  REWRITE_TAC [(REWRITE_CONV [aes256_xts_encrypt_mc] THENC LENGTH_CONV) `LENGTH aes256_xts_encrypt_mc`] THEN
  REWRITE_TAC[byte_list_at; PAIRWISE; ALL; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  ASM_SIMP_TAC[] THEN
  ASM_ARITH_TAC
);;

(* Proof: Less than 5 blocks *)
let AES_XTS_ENCRYPT_LT_5BLOCK_CORRECT = time prove(
  `!ptxt_p ctxt_p len key1_p key2_p iv_p
    pt_in iv
    k1_0 k1_1 k1_2 k1_3 k1_4 k1_5 k1_6 k1_7 k1_8 k1_9 k1_10 k1_11 k1_12 k1_13 k1_14
    k2_0 k2_1 k2_2 k2_3 k2_4 k2_5 k2_6 k2_7 k2_8 k2_9 k2_10 k2_11 k2_12 k2_13 k2_14
    pc.
    PAIRWISE nonoverlapping
    [(word pc, LENGTH aes256_xts_encrypt_mc);
    (ptxt_p, val len);
    (ctxt_p, val len);
    (key1_p, 244);
    (key2_p, 244)] /\
    ~(val len < 0x40) /\ val len < 0x50 /\ LENGTH pt_in = val len /\
    [k1_0; k1_1; k1_2; k1_3; k1_4; k1_5; k1_6; k1_7; k1_8; k1_9; k1_10;
       k1_11; k1_12; k1_13; k1_14] = key1_lst /\
    [k2_0; k2_1; k2_2; k2_3; k2_4; k2_5; k2_6; k2_7; k2_8; k2_9; k2_10;
       k2_11; k2_12; k2_13; k2_14] = key2_lst
    ==> ensures arm
    (\s. aligned_bytes_loaded s (word pc) aes256_xts_encrypt_mc /\
         read PC s = word (pc + 0x1c) /\
         C_ARGUMENTS [ptxt_p; ctxt_p; len; key1_p; key2_p; iv_p] s /\
         byte_list_at pt_in ptxt_p len s /\
           read(memory :> bytes128 iv_p) s = iv /\
           set_key_schedule s key1_p k1_0 k1_1 k1_2 k1_3 k1_4 k1_5 k1_6 k1_7 k1_8 k1_9 k1_10 k1_11 k1_12 k1_13 k1_14 /\
           set_key_schedule s key2_p k2_0 k2_1 k2_2 k2_3 k2_4 k2_5 k2_6 k2_7 k2_8 k2_9 k2_10 k2_11 k2_12 k2_13 k2_14)
      (\s. read PC s = word (pc + 0xa8c) /\ //LENGTH aes256_xts_encrypt_mc - 8*4 = 0xaac - 0x8 * 0x4
           byte_list_at (aes256_xts_encrypt pt_in (val len) iv key1_lst key2_lst) ctxt_p len s
      )
    (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI,,
     MAYCHANGE [X19; X20; X21; X22],,
     MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15],,
     MAYCHANGE [memory :> bytes(ctxt_p, val len)])
    `,
  REWRITE_TAC [(REWRITE_CONV [aes256_xts_encrypt_mc] THENC LENGTH_CONV) `LENGTH aes256_xts_encrypt_mc`] THEN
  REWRITE_TAC[set_key_schedule; byte_list_at; C_ARGUMENTS; SOME_FLAGS; PAIRWISE; ALL;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REPEAT STRIP_TAC THEN

  SUBGOAL_THEN `word_add (word_and len (word 0xf))
    (word_and len (word 0xfffffffffffffff0)) = len:int64` ASSUME_TAC THENL
  [REWRITE_TAC[word_split_lemma]; ALL_TAC] THEN
  ABBREV_TAC `len_full_blocks:int64 = word_and len (word 0xfffffffffffffff0)` THEN
  ABBREV_TAC `tail_len:int64 = word_and len (word 0xf)` THEN
  ABBREV_TAC `num_5blocks = (word (val (len_full_blocks:int64) DIV 0x50)):int64` THEN

  SUBGOAL_THEN `val (len_full_blocks:int64) = 0x40` ASSUME_TAC THENL
  [ EXPAND_TAC "len_full_blocks" THEN
    REWRITE_TAC[NUM_BLOCKS_TO_VAL] THEN
    IMP_REWRITE_TAC[VAL_WORD; DIMINDEX_64; MOD_LT] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    SUBGOAL_THEN `val (len:int64) DIV 16 = 4` SUBST1_TAC THENL
    [ MATCH_MP_TAC(MESON[LE_ANTISYM] `m <= n /\ n <= m ==> m = n`) THEN
      CONJ_TAC THENL [ ASM_ARITH_TAC; ASM_ARITH_TAC];
      ALL_TAC] THEN
    ARITH_TAC; ALL_TAC] THEN

  SUBGOAL_THEN `val (num_5blocks:int64) = 0` ASSUME_TAC THENL
  [ EXPAND_TAC "num_5blocks" THEN
    UNDISCH_TAC `val (len_full_blocks:int64) = 0x40` THEN
    SIMP_TAC[] THEN DISCH_TAC THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[VAL_WORD_0]; ALL_TAC ] THEN

  (* Prove property until start of cipher stealing. *)
  ENSURES_SEQUENCE_TAC `pc + 0x9e0`
  `\s.
    read X0 s = word_add ptxt_p (word (acc_len num_5blocks len_full_blocks)) /\
    read X1 s = word_add ctxt_p (word (acc_len num_5blocks len_full_blocks)) /\
    read X3 s = key1_p /\
    read X21 s = tail_len /\
    read Q6 s = calculate_tweak (acc_blocks num_5blocks len_full_blocks T) iv key2_lst /\
    read X19 s = word 0x87 /\
    read Q16 s = k1_0 /\ read Q17 s = k1_1 /\ read Q12 s = k1_2 /\ read Q13 s = k1_3 /\
    read Q14 s = k1_4 /\ read Q15 s = k1_5 /\ read Q4 s = k1_6 /\ read Q5 s = k1_7 /\
    read Q18 s = k1_8 /\ read Q19 s = k1_9 /\ read Q20 s = k1_10 /\ read Q21 s = k1_11 /\
    read Q22 s = k1_12 /\ read Q23 s = k1_13 /\ read Q7 s = k1_14 /\
    byte_list_at pt_in ptxt_p len s /\
    byte_list_at (aes256_xts_encrypt pt_in (acc_len num_5blocks len_full_blocks) iv key1_lst key2_lst)
                ctxt_p (word (acc_len num_5blocks len_full_blocks)) s` THEN
  CONJ_TAC THENL
  [
    MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN
    EXISTS_TAC `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
      MAYCHANGE [X19; X20; X21; X22],,
      MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15],,
      MAYCHANGE [memory :> bytes128 ctxt_p;
                 memory :> bytes128 (word_add ctxt_p (word 0x10));
                 memory :> bytes128 (word_add ctxt_p (word 0x20));
                 memory :> bytes128 (word_add ctxt_p (word 0x30))]` THEN
    REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    CONJ_TAC THENL [
    REPEAT (GEN_REWRITE_TAC ONCE_DEPTH_CONV [GSYM SEQ_ASSOC] THEN
            MATCH_MP_TAC SUBSUMED_SEQ THEN REWRITE_TAC[SUBSUMED_REFL]) THEN
    ABBREV_TAC `vallen = val (len:int64)` THEN
    SUBSUMED_MAYCHANGE_TAC; ALL_TAC] THEN

    REWRITE_TAC[byte_list_at] THEN
    ENSURES_INIT_TAC "s0" THEN
    ARM_ACCSTEPS_TAC AES256_XTS_ENCRYPT_EXEC [] (1--2) THEN

    (* Discharge if condition *)
    SUBGOAL_THEN
      `ival (word_sub (len:int64) (word 0x10)) < &0x0
      <=> ~(ival (len:int64) - &0x10 = ival (word_sub (len:int64) (word 0x10)))` MP_TAC THENL
    [ MP_TAC (BITBLAST_RULE (* put in tips doc. Q: When to use it vs. ARITH_RULE? *)
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

    MP_TAC (SPECL [`ptxt_p:int64`; `len:int64`; `pt_in:byte list`; `s2:armstate`] READ_LT_5BLOCK) THEN
    ASM_SIMP_TAC[] THEN  REPEAT STRIP_TAC THEN

    ARM_ACCSTEPS_TAC AES256_XTS_ENCRYPT_EXEC [] (3--65) THEN
    (* Prove Q6 stores initial tweak *)
    FIRST_X_ASSUM(MP_TAC o SPEC `(calculate_tweak 0 iv key2_lst)`
      o  MATCH_MP (MESON[] `read Q6 s = a ==> !a'. a = a' ==> read Q6 s = a'`)) THEN
    ANTS_TAC THENL
    [ REWRITE_TAC[CONJUNCT1 calculate_tweak; xts_init_tweak] THEN
      EXPAND_TAC "key2_lst" THEN AESENC_TAC; DISCH_TAC] THEN

    (* Simulating until branching into tail4x *)
    ARM_ACCSTEPS_TAC AES256_XTS_ENCRYPT_EXEC [] (66--87) THEN
    TWEAK_TAC  `Q8:(armstate,int128)component` `1:num` `0:num` THEN
    ARM_ACCSTEPS_TAC AES256_XTS_ENCRYPT_EXEC [] (88--95) THEN
    TWEAK_TAC  `Q9:(armstate,int128)component` `2:num` `1:num` THEN
    ARM_ACCSTEPS_TAC AES256_XTS_ENCRYPT_EXEC [] (96--103) THEN
    TWEAK_TAC `Q10:(armstate,int128)component` `3:num` `2:num` THEN
    (* Simulate AES-XTS encryption of block in Q0, Q1, Q24, Q25 *)
    ARM_ACCSTEPS_TAC AES256_XTS_ENCRYPT_EXEC [] (104--227) THEN
    XTSENC_TAC  `Q0:(armstate,int128)component`    `0` `0` THEN
    XTSENC_TAC  `Q1:(armstate,int128)component` `0x10` `1` THEN
    XTSENC_TAC `Q24:(armstate,int128)component` `0x20` `2` THEN
    XTSENC_TAC `Q25:(armstate,int128)component` `0x30` `3` THEN
    (* until b .Lxts_enc_done = arm_B (word xxx) *)
    ARM_ACCSTEPS_TAC AES256_XTS_ENCRYPT_EXEC [] (228--238) THEN
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
      MP_TAC (SPECL [`0x40`; `ctxt_p:int64`; `(aes256_xts_encrypt pt_in 0x40 iv key1_lst key2_lst):byte list`;
                `s238:armstate`] BYTE_LIST_TO_NUM_THM) THEN
      ANTS_TAC THENL [
        MP_TAC (SPECL [`4`; `pt_in:byte list`; `iv:int128`; `key1_lst:int128 list`; `key2_lst:int128 list`]
                      LENGTH_OF_AES256_XTS_ENCRYPT_FULL_BLOCKS) THEN
        ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN (fun th -> REWRITE_TAC[th]) THEN
      IMP_REWRITE_TAC[READ_BYTES_EQ_READ_BYTE128_4BLOCKS_ENC]
    ]
  ; ALL_TAC] THEN

  (* Reuse the cipher stealing proof *)
  MP_TAC CIPHER_STEALING_ENC_CORRECT THEN
  REWRITE_TAC [(REWRITE_CONV [aes256_xts_encrypt_mc] THENC LENGTH_CONV) `LENGTH aes256_xts_encrypt_mc`] THEN
  REWRITE_TAC[byte_list_at; PAIRWISE; ALL; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  ASM_SIMP_TAC[] THEN
  ASM_ARITH_TAC
);;


(*
void aes_xts_encrypt(const uint8_t *in, uint8_t *out, size_t length,
                        const s2n_bignum_AES_KEY *key1, const s2n_bignum_AES_KEY *key2,
                        const uint8_t iv[16])
*)
let AES256_XTS_ENCRYPT_CORRECT = prove(
  `!ptxt_p ctxt_p len key1_p key2_p iv_p
    pt_in iv
    k1_0 k1_1 k1_2 k1_3 k1_4 k1_5 k1_6 k1_7 k1_8 k1_9 k1_10 k1_11 k1_12 k1_13 k1_14
    k2_0 k2_1 k2_2 k2_3 k2_4 k2_5 k2_6 k2_7 k2_8 k2_9 k2_10 k2_11 k2_12 k2_13 k2_14
    pc.
    PAIRWISE nonoverlapping
    [(word pc, LENGTH aes256_xts_encrypt_mc);
    (ptxt_p, val len);
    (ctxt_p, val len);
    (key1_p, 244);
    (key2_p, 244)] /\
    val len >= 16 /\ val len <= 2 EXP 24 /\ LENGTH pt_in = val len
  ==> ensures arm
      // precondition
      (\s. aligned_bytes_loaded s (word pc) aes256_xts_encrypt_mc /\
           read PC s = word (pc + 28) /\
           C_ARGUMENTS [ptxt_p; ctxt_p; len; key1_p; key2_p; iv_p] s /\
           byte_list_at pt_in ptxt_p len s /\
           read(memory :> bytes128 iv_p) s = iv /\
           set_key_schedule s key1_p k1_0 k1_1 k1_2 k1_3 k1_4 k1_5 k1_6 k1_7 k1_8 k1_9 k1_10 k1_11 k1_12 k1_13 k1_14 /\
           set_key_schedule s key2_p k2_0 k2_1 k2_2 k2_3 k2_4 k2_5 k2_6 k2_7 k2_8 k2_9 k2_10 k2_11 k2_12 k2_13 k2_14
      )
      // postcondition
      (\s. read PC s = word (pc + 0xa8c) /\ //LENGTH aes256_xts_encrypt_mc - 8*4 = 0xaac - 0x8 * 0x4
           byte_list_at (aes256_xts_encrypt pt_in (val len) iv
                [k1_0; k1_1; k1_2; k1_3; k1_4; k1_5; k1_6; k1_7; k1_8; k1_9; k1_10; k1_11; k1_12; k1_13; k1_14]
                [k2_0; k2_1; k2_2; k2_3; k2_4; k2_5; k2_6; k2_7; k2_8; k2_9; k2_10; k2_11; k2_12; k2_13; k2_14])
                ctxt_p len s
      )
    (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI,,
     MAYCHANGE [X19; X20; X21; X22],,
     MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15],,
     MAYCHANGE [memory :> bytes(ctxt_p, val len)])`,

  REWRITE_TAC [(REWRITE_CONV [aes256_xts_encrypt_mc] THENC LENGTH_CONV) `LENGTH aes256_xts_encrypt_mc`] THEN
  REWRITE_TAC[set_key_schedule; byte_list_at; C_ARGUMENTS; SOME_FLAGS; PAIRWISE; ALL;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REPEAT STRIP_TAC THEN

  (* Break len into full blocks and tail *)
  SUBGOAL_THEN `word_add (word_and len (word 0xf))
    (word_and len (word 0xfffffffffffffff0)) = len:int64` ASSUME_TAC THENL
  [REWRITE_TAC[word_split_lemma]; ALL_TAC] THEN
  ABBREV_TAC `len_full_blocks:int64 = word_and len (word 0xfffffffffffffff0)` THEN
  ABBREV_TAC `num_5blocks = (word (val (len_full_blocks:int64) DIV 0x50)):int64` THEN
  ABBREV_TAC `tail_len:int64 = word_and len (word 0xf)` THEN

  ABBREV_TAC `key1_lst:int128 list = [k1_0; k1_1; k1_2; k1_3; k1_4; k1_5; k1_6; k1_7; k1_8; k1_9; k1_10; k1_11; k1_12; k1_13; k1_14]` THEN
  ABBREV_TAC `key2_lst:int128 list = [k2_0; k2_1; k2_2; k2_3; k2_4; k2_5; k2_6; k2_7; k2_8; k2_9; k2_10; k2_11; k2_12; k2_13; k2_14]` THEN

  (* Case splits on length:
    len < 16 -- error case
    len < 32 -- one block, or one block and a tail
    len < 48 -- two blocks, or two blocks and a tail
    len < 64 -- three blocks, or three blocks and a tail
    len < 80 -- four blocks, or four blocks and a tail
    len >= 80 -- five blocks and up => at least one big loop iteration

    Note: for encrypt, in cipherstealing, the tail is directly processed since the last
          tweak is available from prior calculations. The order of the tweaks is not flipped,
          as in the case of decrypt, between the last block and the tail.
    *)
  ASM_CASES_TAC `val (len:int64) < 0x50` THENL [
    ASM_CASES_TAC `val (len:int64) < 0x20` THENL
    [
      MP_TAC AES_XTS_ENCRYPT_LT_2BLOCK_CORRECT THEN
      REWRITE_TAC [(REWRITE_CONV [aes256_xts_encrypt_mc] THENC LENGTH_CONV) `LENGTH aes256_xts_encrypt_mc`] THEN
      REWRITE_TAC[set_key_schedule; byte_list_at; C_ARGUMENTS; SOME_FLAGS; PAIRWISE; ALL;
                  MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
      DISCH_THEN MATCH_MP_TAC THEN
      ASM_SIMP_TAC[] ; ALL_TAC  ] THEN

    ASM_CASES_TAC `val (len:int64) < 0x30` THENL
    [
      MP_TAC AES_XTS_ENCRYPT_LT_3BLOCK_CORRECT THEN
      REWRITE_TAC [(REWRITE_CONV [aes256_xts_encrypt_mc] THENC LENGTH_CONV) `LENGTH aes256_xts_encrypt_mc`] THEN
      REWRITE_TAC[set_key_schedule; byte_list_at; C_ARGUMENTS; SOME_FLAGS; PAIRWISE; ALL;
                  MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
      DISCH_THEN MATCH_MP_TAC THEN
      ASM_SIMP_TAC[] ; ALL_TAC  ] THEN

    ASM_CASES_TAC `val (len:int64) < 0x40` THENL
    [
      MP_TAC AES_XTS_ENCRYPT_LT_4BLOCK_CORRECT THEN
      REWRITE_TAC [(REWRITE_CONV [aes256_xts_encrypt_mc] THENC LENGTH_CONV) `LENGTH aes256_xts_encrypt_mc`] THEN
      REWRITE_TAC[set_key_schedule; byte_list_at; C_ARGUMENTS; SOME_FLAGS; PAIRWISE; ALL;
                  MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
      DISCH_THEN MATCH_MP_TAC THEN
      ASM_SIMP_TAC[] ; ALL_TAC  ] THEN

    ASM_CASES_TAC `val (len:int64) < 0x50` THENL
    [
      MP_TAC AES_XTS_ENCRYPT_LT_5BLOCK_CORRECT THEN
      REWRITE_TAC [(REWRITE_CONV [aes256_xts_encrypt_mc] THENC LENGTH_CONV) `LENGTH aes256_xts_encrypt_mc`] THEN
      REWRITE_TAC[set_key_schedule; byte_list_at; C_ARGUMENTS; SOME_FLAGS; PAIRWISE; ALL;
                  MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
      DISCH_THEN MATCH_MP_TAC THEN
      ASM_SIMP_TAC[] ; ALL_TAC  ] THEN

    ASM_ARITH_TAC
  ; ALL_TAC] THEN

  (* Prove the bounds on len_full_blocks, num_5blocks and len and their relationships *)
  SUBGOAL_THEN `~(val (len_full_blocks:int64) < 0x50)` ASSUME_TAC THENL
  [ UNDISCH_TAC `~(val (len:int64) < 0x50)` THEN
    UNDISCH_TAC `word_and len (word 0xfffffffffffffff0) = (len_full_blocks:int64)` THEN
    MP_TAC (SPECL [`len:int64`; `len_full_blocks:int64`] LEN_FULL_BLOCKS_LO_BOUND_THM) THEN
    SIMP_TAC[]; ALL_TAC] THEN

  SUBGOAL_THEN `val (len_full_blocks:int64) <= 0x2 EXP 24` ASSUME_TAC THENL
  [ UNDISCH_TAC `val (len:int64) <= 0x2 EXP 24` THEN
    UNDISCH_TAC `word_and len (word 0xfffffffffffffff0) = (len_full_blocks:int64)` THEN
    MP_TAC (SPECL [`len:int64`; `len_full_blocks:int64`] NUM_BLOCKS_HI_BOUND_THM) THEN
    SIMP_TAC[]; ALL_TAC] THEN

  SUBGOAL_THEN `0 < val (num_5blocks:int64)` ASSUME_TAC THENL
  [ UNDISCH_TAC `word (val (len_full_blocks:int64) DIV 0x50) = (num_5blocks:int64)` THEN
    UNDISCH_TAC `~(val (len_full_blocks:int64) < 0x50)` THEN
    UNDISCH_TAC `val (len_full_blocks:int64) <= 0x2 EXP 24` THEN
    MP_TAC (SPECL [`len_full_blocks:int64`; `num_5blocks:int64`]
      NUM_5BLOCKS_LO_BOUND_THM) THEN SIMP_TAC[]
    ; ALL_TAC] THEN

  SUBGOAL_THEN `val (len_full_blocks:int64) <= val (len:int64)` ASSUME_TAC THENL
  [ EXPAND_TAC "len_full_blocks" THEN SIMP_TAC[NUM_BLOCKS_LT_LEN_THM]; ALL_TAC] THEN

  SUBGOAL_THEN `val (num_5blocks:int64) * 0x50 <= val (len_full_blocks:int64)` ASSUME_TAC THENL
  [ EXPAND_TAC "num_5blocks" THEN
    REWRITE_TAC [VAL_WORD; DIMINDEX_64] THEN
    UNDISCH_TAC `val (len_full_blocks:int64) <= 0x2 EXP 0x18` THEN
    ARITH_TAC; ALL_TAC] THEN

  (* Verify properties of the program until the beginning of the loop.
     This saves work in the second subgoal of the loop invariant and brings it here.
     Up to the loop:
     - First 5 tweaks are calculated from the iv
     - X2 contains len_full_blocks
     - X8 contains num_5blocks
     - key1 schedule is loaded in Q registers
     - X9 and X10 are not needed to be spelled out for the proof itself, but to be
       kept in the assumption list after the proof *)
  ENSURES_SEQUENCE_TAC
  `pc + 0x140`
  `\s.
      read X0 s = ptxt_p /\
      read X1 s = ctxt_p /\
      read X2 s = len_full_blocks /\
      read X3 s = key1_p /\
      read X21 s = tail_len /\
      read X8 s = num_5blocks /\
      read X9  s = word_zx (calculate_tweak 4 iv key2_lst) /\
      read X10 s = word_subword (calculate_tweak 4 iv key2_lst) (64,64) /\
      read Q6 s = calculate_tweak 0 iv key2_lst /\
      read Q8 s = calculate_tweak 1 iv key2_lst  /\
      read Q9 s = calculate_tweak 2 iv key2_lst  /\
      read Q10 s = calculate_tweak 3 iv key2_lst  /\
      read Q11 s = calculate_tweak 4 iv key2_lst  /\
      read X19 s = word 0x87 /\
      read Q16 s = k1_0 /\ read Q17 s = k1_1 /\ read Q12 s = k1_2 /\ read Q13 s = k1_3 /\
      read Q14 s = k1_4 /\ read Q15 s = k1_5 /\ read Q4 s = k1_6 /\ read Q5 s = k1_7 /\
      read Q18 s = k1_8 /\ read Q19 s = k1_9 /\ read Q20 s = k1_10 /\ read Q21 s = k1_11 /\
      read Q22 s = k1_12 /\ read Q23 s = k1_13 /\ read Q7 s = k1_14 /\
      byte_list_at pt_in ptxt_p len s /\
      byte_list_at (aes256_xts_encrypt pt_in 0 iv key1_lst key2_lst)
                   ctxt_p (word 0) s
  ` THEN
    CONJ_TAC THENL
    [
      (* ===> Symbolic Simulation: Start symbolic simulation*)
      ENSURES_INIT_TAC "s0" THEN
      ARM_ACCSTEPS_TAC AES256_XTS_ENCRYPT_EXEC [] (1--2) THEN

      (* Discharge if condition *)
      SUBGOAL_THEN
        `ival (word_sub (len:int64) (word 0x10)) < &0x0
          <=> ~(ival (len:int64) - &0x10 = ival (word_sub (len:int64) (word 0x10)))` MP_TAC THENL
      [ MP_TAC (BITBLAST_RULE
          `val (len:int64) >= 0x10 ==> val len <= 2 EXP 0x18 ==>
            ival (word_sub len (word 0x10)) >= &0x0`) THEN
        ASM_REWRITE_TAC[] THEN
        MP_TAC (BITBLAST_RULE
          `val (len:int64)  >= 0x10 ==> val len <= 2 EXP 0x18 ==>
            ival (len:int64) - &0x10 = ival (word_sub len (word 0x10))`) THEN
        ASM_REWRITE_TAC[] THEN
        ARITH_TAC;(* works on the goal; that's why we bring the assumptions we want as antecedants of the goal *)
        ALL_TAC
      ] THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_TAC THEN POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
      (* Try DISCH_THEN(RULE_ASSUM_TAC o REWRITE_RULE o CONJUNCTS) *)

      (* ===> Symbolic Simulation: Symbolic execution for initialization of tweak *)
      ARM_ACCSTEPS_TAC AES256_XTS_ENCRYPT_EXEC [] (3--65) THEN
      (* Prove Q6 stores initial tweak *)
      FIRST_X_ASSUM(MP_TAC o SPEC `(calculate_tweak 0 iv key2_lst)`
          o  MATCH_MP (MESON[] `read Q6 s = a ==> !a'. a = a' ==> read Q6 s = a'`)) THEN
        ANTS_TAC THENL
        [REWRITE_TAC[CONJUNCT1 calculate_tweak; xts_init_tweak] THEN
          EXPAND_TAC "key2_lst" THEN AESENC_TAC; DISCH_TAC] THEN

      (* ===> Symbolic Simulation: Symbolic simulating untill next branch:
                - iv for second block
                - load key schedule *)
      ARM_ACCSTEPS_TAC AES256_XTS_ENCRYPT_EXEC [] (66--77) THEN
      (* Branching on x2 *)
      (* Eliminate 1 block case *)
      SUBGOAL_THEN `~(val (len_full_blocks:int64) < 0x20)` MP_TAC THENL
      [ UNDISCH_TAC `~(val (len_full_blocks:int64) < 0x50)` THEN ARITH_TAC;
        DISCH_THEN(RULE_ASSUM_TAC o REWRITE_RULE o CONJUNCTS)] THEN

      (* Prove x9, x10 store lower and upper halves of tweak 1 and Q8 stores the full tweak 1 *)
      ARM_ACCSTEPS_TAC AES256_XTS_ENCRYPT_EXEC [] (78--87) THEN
      TWEAK_TAC `Q8:(armstate,int128)component` `1:num` `0:num` THEN

      (* Eliminate 2 blocks case *)
      SUBGOAL_THEN `~(val (len_full_blocks:int64) < 0x30)` MP_TAC THENL
      [ UNDISCH_TAC `~(val (len_full_blocks:int64) < 0x50)` THEN ARITH_TAC;
        DISCH_THEN(RULE_ASSUM_TAC o REWRITE_RULE o CONJUNCTS)] THEN
      (* prove Q9 stores tweak of 3rd block (index 2) *)
      ARM_ACCSTEPS_TAC AES256_XTS_ENCRYPT_EXEC [] (88--95) THEN (* TODO: How is the last parameter in TWEAK_TAC `0` in the upcoming ones? *)
      TWEAK_TAC `Q9:(armstate,int128)component` `2:num` `0:num` THEN
      (* Eliminate 3 blocks case *)
      SUBGOAL_THEN `~(val (len_full_blocks:int64) < 0x40)` MP_TAC THENL
      [ UNDISCH_TAC `~(val (len_full_blocks:int64) < 0x50)` THEN ARITH_TAC;
        DISCH_THEN(RULE_ASSUM_TAC o REWRITE_RULE o CONJUNCTS)] THEN
      (* prove Q10 stores tweak of 4th block (index 3) *)
      ARM_ACCSTEPS_TAC AES256_XTS_ENCRYPT_EXEC [] (96--103) THEN
      TWEAK_TAC `Q10:(armstate,int128)component` `3:num` `0:num` THEN
      (* Eliminate 4 blocks case, proven by the assumption ~(len_full_blocks < 0x50)*)
      (* prove Q11 stores tweak of 5th block (index 4) *)
      ARM_ACCSTEPS_TAC AES256_XTS_ENCRYPT_EXEC [] (105--110) THEN
      TWEAK_TAC `Q11:(armstate,int128)component` `4:num` `0:num` THEN

      (* Prove the optimized udiv is basically udiv *)
      ARM_ACCSTEPS_TAC AES256_XTS_ENCRYPT_EXEC [] (111--114) THEN
      SUBGOAL_THEN `word_ushr
          ((word ((val (len_full_blocks:int64) * 0xcccccccccccccccd) DIV 0x2 EXP 0x40)):int64)
          0x6 =
        word ((val len_full_blocks) DIV 0x50)` ASSUME_TAC THENL
      [ MP_TAC (BITBLAST_RULE `val (len_full_blocks:int64) < 2 EXP 64`) THEN
        REWRITE_TAC[word_ushr] THEN
        MP_TAC (SPECL [`val (len_full_blocks:int64)`] UDIV_OPT_THM) THEN SIMP_TAC[]
        ; ALL_TAC] THEN
      POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN

      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      REPEAT CONJ_TAC THENL
      [ ASM_REWRITE_TAC[byte_list_at];
        REWRITE_TAC[aes256_xts_encrypt] THEN
        CONV_TAC (DEPTH_CONV NUM_RED_CONV) THEN
        ASM_REWRITE_TAC[byte_list_at] THEN
        REWRITE_TAC[VAL_WORD_0] THEN ARITH_TAC ]
      ; ALL_TAC
  ] THEN

  (* Prove property until right before cipher stealing *)
  ENSURES_SEQUENCE_TAC `pc + 0x9e0`
  `\s.
      read X0 s = word_add ptxt_p (word (acc_len num_5blocks len_full_blocks)) /\
      read X1 s = word_add ctxt_p (word (acc_len num_5blocks len_full_blocks)) /\
      read X3 s = key1_p /\
      read X21 s = tail_len /\
      read Q6 s = calculate_tweak (acc_blocks num_5blocks len_full_blocks T) iv key2_lst /\
      read X19 s = word 0x87 /\
      read Q16 s = k1_0 /\ read Q17 s = k1_1 /\ read Q12 s = k1_2 /\ read Q13 s = k1_3 /\
      read Q14 s = k1_4 /\ read Q15 s = k1_5 /\ read Q4 s = k1_6 /\ read Q5 s = k1_7 /\
      read Q18 s = k1_8 /\ read Q19 s = k1_9 /\ read Q20 s = k1_10 /\ read Q21 s = k1_11 /\
      read Q22 s = k1_12 /\ read Q23 s = k1_13 /\ read Q7 s = k1_14 /\
      byte_list_at pt_in ptxt_p len s /\
      byte_list_at (aes256_xts_encrypt pt_in (acc_len num_5blocks len_full_blocks) iv key1_lst key2_lst)
                  ctxt_p (word (acc_len num_5blocks len_full_blocks)) s` THEN
  CONJ_TAC THENL
  [
    (* Loop invariant of main loop *)
    ENSURES_WHILE_PAUP_TAC
    `0` (* counter begin number *)
    `val (num_5blocks:int64)` (* counter end number *)
    `pc + 0x140` (* loop body start PC *)
    `pc + 0x430` (* loop backedge branch PC *)
    `\i s.
          // loop invariant at the end of the loop iteration
         (read X0  s = word_add ptxt_p (word_mul (word 0x50) (word i)) /\
          read X1  s = word_add ctxt_p (word_mul (word 0x50) (word i)) /\
          read X21 s = tail_len /\
          read X3 s = key1_p /\
          read X2  s = word_sub len_full_blocks (word_mul (word 0x50) (word i)) /\
          read X8  s = word_sub num_5blocks (word i) /\
          read X19 s = word 0x87 /\
          read X9  s = word_zx (calculate_tweak (i * 5 + 4) iv key2_lst) /\
          read X10 s = word_subword (calculate_tweak (i * 5 + 4) iv key2_lst) (64,64) /\
          read Q6  s = calculate_tweak (i * 5) iv key2_lst /\
          read Q8  s = calculate_tweak (i * 5 + 1) iv key2_lst /\
          read Q9  s = calculate_tweak (i * 5 + 2) iv key2_lst /\
          read Q10 s = calculate_tweak (i * 5 + 3) iv key2_lst /\
          read Q11 s = calculate_tweak (i * 5 + 4) iv key2_lst /\
          read Q16 s = k1_0 /\ read Q17 s = k1_1 /\ read Q12 s = k1_2 /\ read Q13 s = k1_3 /\
          read Q14 s = k1_4 /\ read Q15 s = k1_5 /\ read Q4 s = k1_6 /\ read Q5 s = k1_7 /\
          read Q18 s = k1_8 /\ read Q19 s = k1_9 /\ read Q20 s = k1_10 /\ read Q21 s = k1_11 /\
          read Q22 s = k1_12 /\ read Q23 s = k1_13 /\ read Q7 s = k1_14 /\
          byte_list_at pt_in ptxt_p len s /\
          byte_list_at (aes256_xts_encrypt pt_in (i * 0x50) iv key1_lst key2_lst)
                          ctxt_p (word (i * 0x50)) s) /\
          // loop backedge condition
          (read ZF s <=> i = val (num_5blocks:int64))` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
    [
      (* Subgoal 1.
        0 < `val (num_5blocks:int64)`
        automatically discharged by asm *)

      (* Subgoal 2. Invariant holds before entering the loop *)
      REWRITE_TAC[byte_list_at] THEN
      ENSURES_INIT_TAC "s0" THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      REPEAT CONJ_TAC THENL
      [ WORD_ARITH_TAC; WORD_ARITH_TAC; WORD_ARITH_TAC; WORD_ARITH_TAC;
        CONV_TAC NUM_REDUCE_CONV;
        CONV_TAC NUM_REDUCE_CONV;
        CONV_TAC NUM_REDUCE_CONV;
        CONV_TAC NUM_REDUCE_CONV;
        CONV_TAC NUM_REDUCE_CONV;
        CONV_TAC NUM_REDUCE_CONV;
        CONV_TAC NUM_REDUCE_CONV;
        CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[VAL_WORD_0] THEN ARITH_TAC ];

      (* Subgoal 3: inductive step in the loop body *)
      REPEAT STRIP_TAC THEN

      SUBGOAL_THEN `i * 0x50 + 0x50 <= val (len:int64)` ASSUME_TAC THENL
      [
        SUBGOAL_THEN `i + 1 <= val (num_5blocks:int64)` MP_TAC THENL
          [ ASM_ARITH_TAC; ALL_TAC ] THEN
        SUBGOAL_THEN `val (len_full_blocks:int64) <= val (len:int64)` ASSUME_TAC THENL
          [ EXPAND_TAC "len_full_blocks" THEN SIMP_TAC[NUM_BLOCKS_LT_LEN_THM]; ALL_TAC ] THEN
        SUBGOAL_THEN `val (num_5blocks:int64) * 0x50 <= val (len:int64)` ASSUME_TAC THENL
          [ EXPAND_TAC "num_5blocks" THEN
            REWRITE_TAC [VAL_WORD; DIMINDEX_64] THEN
            UNDISCH_TAC `val (len_full_blocks:int64) <= val (len:int64)` THEN
            ARITH_TAC; ALL_TAC ] THEN
        SUBGOAL_THEN `(i + 1) * 0x50 <= val (len:int64)` MP_TAC THENL
          [ ASM_ARITH_TAC; ALL_TAC ] THEN
        ARITH_TAC; ALL_TAC
      ] THEN

      MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN
      EXISTS_TAC `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
        MAYCHANGE [X19; X20; X21; X22],,
        MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15],,
        MAYCHANGE [memory :> bytes128 (word_add ctxt_p (word (0x50 * i)));
                   memory :> bytes128 (word_add ctxt_p (word (0x50 * i + 0x10)));
                   memory :> bytes128 (word_add ctxt_p (word (0x50 * i + 0x20)));
                   memory :> bytes128 (word_add ctxt_p (word (0x50 * i + 0x30)));
                   memory :> bytes128 (word_add ctxt_p (word (0x50 * i + 0x40)))]` THEN
      REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
      CONJ_TAC THENL[
        REPEAT (GEN_REWRITE_TAC ONCE_DEPTH_CONV [GSYM SEQ_ASSOC] THEN
                MATCH_MP_TAC SUBSUMED_SEQ THEN REWRITE_TAC[SUBSUMED_REFL]) THEN
        (* see https://hol-light.zulipchat.com/#narrow/channel/474190-s2n-bignum/topic/.E2.9C.94.20SUBSUMED_MAYCHANGE.20proof/near/541307474 *)
        ABBREV_TAC `vallen = val (len:int64)` THEN
        SUBSUMED_MAYCHANGE_TAC; ALL_TAC
      ] THEN

      (* ===> Symbolic Simulation: Start symbolic simulation*)
      ASM_REWRITE_TAC[byte_list_at] THEN
      ENSURES_INIT_TAC "s0" THEN

      (* List values for ptxt_p + [0 .. 0x40] *)
      MP_TAC (SPECL [`ptxt_p:int64`; `i:num`; `len:int64`; `pt_in:byte list`; `s0:armstate`] READ_BL_LEMMA) THEN
      ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
      (* Prove Q0, Q1, Q24, Q25, Q26 stores correct plaintext *)
      (* and prove Q6, Q8, Q9, Q10, Q11 stores correct tweak: *)
      (* Run simulation until after every ciphertext block and new tweak are calculated
         and prove they're correct in their registers *)
      ARM_ACCSTEPS_TAC AES256_XTS_ENCRYPT_EXEC [] (1--151) THEN
      XTSENC_TAC `Q0:(armstate,int128)component` `i * 0x50` `i * 0x5` THEN
      TWEAK_TAC `Q6:(armstate,int128)component` `i * 5 + 5` `i * 5 + 4` THEN

      ARM_ACCSTEPS_TAC AES256_XTS_ENCRYPT_EXEC [] (152--159) THEN
      XTSENC_TAC `Q1:(armstate,int128)component` `i * 0x50 + 0x10` `i * 0x5 + 0x1` THEN
      TWEAK_TAC `Q8:(armstate,int128)component` `i * 5 + 6` `i * 5 + 5` THEN

      ARM_ACCSTEPS_TAC AES256_XTS_ENCRYPT_EXEC [] (160--167) THEN
      XTSENC_TAC `Q24:(armstate,int128)component` `i * 0x50 + 0x20` `i * 0x5 + 0x2` THEN
      TWEAK_TAC `Q9:(armstate,int128)component` `i * 5 + 7` `i * 5 + 6` THEN

      ARM_ACCSTEPS_TAC AES256_XTS_ENCRYPT_EXEC [] (168--175) THEN
      XTSENC_TAC `Q25:(armstate,int128)component` `i * 0x50 + 0x30` `i * 0x5 + 0x3` THEN
      TWEAK_TAC `Q10:(armstate,int128)component` `i * 5 + 8` `i * 5 + 7` THEN

      ARM_ACCSTEPS_TAC AES256_XTS_ENCRYPT_EXEC [] (176--183) THEN
      XTSENC_TAC `Q26:(armstate,int128)component` `i * 0x50 + 0x40` `i * 0x5 + 0x4` THEN
      TWEAK_TAC `Q11:(armstate,int128)component` `i * 5 + 9` `i * 5 + 8` THEN

      (* The following lemmas are for NONSELFMODIFYING_STATE_UPDATE_TAC when store back to ctxt_p,
         and for the MAYCHANGE clauses *)
      RULE_ASSUM_TAC(REWRITE_RULE
        [WORD_RULE `word_mul (word 0x50) (word i):int64 = word(0x50 * i)`]) THEN

      (*
 38 [`forall i'.
          i' < val (word (i * 0x50)).  ====> becomes 0x50 * i
          ==> read (memory :> bytes8 (word_add ctxt_p (word i'))) s183 =
              EL i'
              (aes256_xts_encrypt pt_in (i * 0x50) iv key1_lst key2_lst)`]
 39 [`forall i'.
          i' < val len
          ==> read (memory :> bytes8 (word_add ptxt_p (word i'))) s183 =
              EL i' pt_in`]
      *)
      (* Rewrite to help reasoning about nonoverlapping
         so that the universally quantified assumption stays.
         See: https://hol-light.zulipchat.com/#narrow/channel/474190-s2n-bignum/topic/.E2.9C.94.20Symbolic.20simulation.20removed.20assumption/with/541554894 *)
      SUBGOAL_THEN `val ((word (i * 0x50)):int64) = 0x50 * i` MP_TAC THENL [
        IMP_REWRITE_TAC[VAL_WORD; DIMINDEX_64; MOD_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(RULE_ASSUM_TAC o REWRITE_RULE o CONJUNCTS) THEN

      (* Simulate until end of loop *)
      ARM_ACCSTEPS_TAC AES256_XTS_ENCRYPT_EXEC [] (184--188) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      REPEAT CONJ_TAC THENL
      (*
      val it : goalstack = 13 subgoals (16 total)

`word_add (word_add ptxt_p (word (0x50 * i))) (word 0x50) =
 word_add ptxt_p (word_mul (word 0x50) (word (i + 0x1))) /\
 word_add (word_add ctxt_p (word (0x50 * i))) (word 0x50) =
 word_add ctxt_p (word_mul (word 0x50) (word (i + 0x1))) /\
 word_sub (word_sub len_full_blocks (word (0x50 * i))) (word 0x50) =
 word_sub len_full_blocks (word_mul (word 0x50) (word (i + 0x1))) /\
 word_sub (word_sub num_5blocks (word i)) (word 0x1) =
 word_sub num_5blocks (word (i + 0x1)) /\
 word_zx (calculate_tweak (i * 0x5 + 0x9) iv key2_lst) =
 word_zx (calculate_tweak ((i + 0x1) * 0x5 + 0x4) iv key2_lst) /\
 word_subword (calculate_tweak (i * 0x5 + 0x9) iv key2_lst) (0x40,0x40) =
 word_subword (calculate_tweak ((i + 0x1) * 0x5 + 0x4) iv key2_lst)
 (0x40,0x40) /\
 calculate_tweak (i * 0x5 + 0x5) iv key2_lst =
 calculate_tweak ((i + 0x1) * 0x5) iv key2_lst /\
 calculate_tweak (i * 0x5 + 0x6) iv key2_lst =
 calculate_tweak ((i + 0x1) * 0x5 + 0x1) iv key2_lst /\
 calculate_tweak (i * 0x5 + 0x7) iv key2_lst =
 calculate_tweak ((i + 0x1) * 0x5 + 0x2) iv key2_lst /\
 calculate_tweak (i * 0x5 + 0x8) iv key2_lst =
 calculate_tweak ((i + 0x1) * 0x5 + 0x3) iv key2_lst /\
 calculate_tweak (i * 0x5 + 0x9) iv key2_lst =
 calculate_tweak ((i + 0x1) * 0x5 + 0x4) iv key2_lst /\
 (forall i'.
      i' < val (word ((i + 0x1) * 0x50))
      ==> read (memory :> bytes8 (word_add ctxt_p (word i'))) s188 =
          EL i'
          (aes256_xts_encrypt pt_in ((i + 0x1) * 0x50) iv key1_lst key2_lst)) /\
 (val (word_sub (word_sub num_5blocks (word i)) (word 0x1)) = 0x0 <=>
  i + 0x1 = val num_5blocks)`
      *)
      [ REWRITE_TAC[WORD_RULE `word_mul (word 0x50) (word (i + 1)):int64 = word_add (word(0x50 * i)) (word 0x50)`] THEN
        REWRITE_TAC[WORD_ADD_ASSOC];
        REWRITE_TAC[WORD_RULE `word_mul (word 0x50) (word (i + 1)):int64 = word_add (word(0x50 * i)) (word 0x50)`] THEN
        REWRITE_TAC[WORD_ADD_ASSOC];
        REWRITE_TAC[WORD_RULE `word_mul (word 0x50) (word (i + 1)):int64 = word_add (word(0x50 * i)) (word 0x50)`] THEN
        CONV_TAC WORD_RULE;
        CONV_TAC WORD_RULE;
        REWRITE_TAC[WORD_RULE `(i + 0x1) * 0x5 + 0x4 = i * 0x5 + 0x9`];
        REWRITE_TAC[WORD_RULE `(i + 0x1) * 0x5 + 0x4 = i * 0x5 + 0x9`];
        REWRITE_TAC[WORD_RULE `(i + 0x1) * 0x5 = i * 0x5 + 0x5`];
        REWRITE_TAC[WORD_RULE `(i + 0x1) * 0x5 + 0x1 = i * 0x5 + 0x6`];
        REWRITE_TAC[WORD_RULE `(i + 0x1) * 0x5 + 0x2 = i * 0x5 + 0x7`];
        REWRITE_TAC[WORD_RULE `(i + 0x1) * 0x5 + 0x3 = i * 0x5 + 0x8`];
        REWRITE_TAC[WORD_RULE `(i + 0x1) * 0x5 + 0x4 = i * 0x5 + 0x9`];

        (* The following is the main proof for inductive step *)
        REWRITE_TAC[ARITH_RULE `(i + 0x1) * 0x50 = 0x50 * i + 0x50`] THEN
        SUBGOAL_THEN `val ((word (0x50 * i + 0x50)):int64) = 0x50 * i + 0x50` ASSUME_TAC THENL [
          IMP_REWRITE_TAC[VAL_WORD; DIMINDEX_64; MOD_LT] THEN
          UNDISCH_TAC `i * 0x50 + 0x50 <= val (len:int64)` THEN
          UNDISCH_TAC `val (len:int64) <= 2 EXP 24` THEN
          ARITH_TAC; ALL_TAC] THEN
        ASM_REWRITE_TAC[] THEN

        (* Remove quantifier over reading one byte at a time, i'*)
        UNDISCH_TAC
        `forall i'.
          i' < 0x50 * i
          ==> read (memory :> bytes8 (word_add ctxt_p (word i'))) s188 =
              EL i' (aes256_xts_encrypt pt_in (i * 0x50) iv key1_lst key2_lst)` THEN
        MP_TAC (SPECL [`0x50 * i + 0x50:num`; `ctxt_p:int64`;
                       `(aes256_xts_encrypt pt_in (0x50 * i + 0x50) iv key1_lst key2_lst):byte list`;
                       `s188:armstate`] BYTE_LIST_TO_NUM_THM) THEN
        ANTS_TAC THENL[
          REWRITE_TAC[ARITH_RULE `0x50 * i + 0x50 = 0x10 * (5 * i + 5)`;
                      LENGTH_OF_AES256_XTS_ENCRYPT_FULL_BLOCKS] THEN
          ARITH_TAC
          ; ALL_TAC] THEN
        DISCH_THEN (fun th -> REWRITE_TAC[th]) THEN
        MP_TAC (SPECL [`0x50 * i:num`;  `ctxt_p:int64`;
                       `(aes256_xts_encrypt pt_in (i * 0x50) iv key1_lst key2_lst):byte list`;
                       `s188:armstate`] BYTE_LIST_TO_NUM_THM) THEN
        ANTS_TAC THENL[
          REWRITE_TAC[ARITH_RULE `i * 0x50 = 0x10 * 5 * i`;
                      LENGTH_OF_AES256_XTS_ENCRYPT_FULL_BLOCKS] THEN
          ARITH_TAC
          ; ALL_TAC] THEN
        DISCH_THEN (fun th -> REWRITE_TAC[th]) THEN
        DISCH_TAC THEN

        (* Prove one block equivalence and reduce proving the following:
           `read (memory :> bytes (ctxt_p,0x50 * i + 0x50)) s188 =
            num_of_bytelist
             (aes256_xts_encrypt pt_in (0x50 * i + 0x50) iv key1_lst key2_lst)`
           to:
          `read (memory :> bytes (ctxt_p, 0x50 * i + 0x40)) s188 =
           num_of_bytelist
            (aes256_xts_encrypt pt_in (0x50 * i + 0x40) iv key1_lst key2_lst)` *)
        IMP_REWRITE_TAC[ARITH_RULE `0x50 * i + 0x50 = (0x50 * i + 0x40) + 0x10`; READ_BYTES_AND_BYTE128_SPLIT] THEN
        EXISTS_TAC `(aes256_xts_encrypt pt_in (0x50 * i + 0x50) iv key1_lst key2_lst)` THEN
        REPEAT CONJ_TAC THENL [
          REWRITE_TAC [ARITH_RULE `(0x50 * i + 0x40) + 0x10 = 0x50 * i + 0x50`];

          MP_TAC (SPECL [`0x5 * i + 0x5:num`; `pt_in:byte list`; `iv:int128`; `key1_lst:int128 list`;
            `key2_lst:int128 list`] LENGTH_OF_AES256_XTS_ENCRYPT_FULL_BLOCKS) THEN
          REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_ASSOC; GSYM ADD_ASSOC] THEN
          CONV_TAC NUM_REDUCE_CONV THEN (* DISCH_TAC THEN
          IMP_REWRITE_TAC[SUB_LIST_LENGTH_IMPLIES] *)
          DISCH_THEN (fun th -> REWRITE_TAC[th]) THEN
          ARITH_TAC;

          (* Establish that one xts decrypt round is the same as
             selecting one block of bytes from calling the top-level function. *)
          REWRITE_TAC[aes256_xts_encrypt] THEN
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

          MP_TAC (SPECL [`0`;`5 * i + 3:num`; `pt_in:byte list`; `iv:int128`; `key1_lst:int128 list`; `key2_lst:int128 list`]
                  LENGTH_OF_AES256_XTS_ENCRYPT_REC) THEN
          SIMP_TAC[ARITH_RULE `~(5 * i + 3 < 0)`;
                   ARITH_RULE `((0x5 * i + 0x3) - 0x0 + 0x1) * 0x10 = 0x50 * i + 0x40`] THEN
          IMP_REWRITE_TAC[SUB_LIST_APPEND_RIGHT_LEMMA] THEN DISCH_TAC THEN

          MP_TAC (SPECL [`5 * i + 4:num`; `0x0:num`; `pt_in:byte list`; `iv:int128`;
                         `key1_lst:int128 list`; `key2_lst:int128 list`]
                  LENGTH_OF_AES256_XTS_ENCRYPT_TAIL) THEN
          CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[ADD_0] THEN DISCH_TAC THEN
          IMP_REWRITE_TAC[SUB_LIST_LENGTH_IMPLIES] THEN

          REWRITE_TAC[AES256_XTS_ENCRYPT_TAIL_WHEN_1BLOCK] THEN
          SIMP_TAC[ARITH_RULE `i * 0x50 + 0x40 = (i * 0x5 + 0x4) * 0x10`;
                   ARITH_RULE `i * 0x5 = 0x5 * i`];

          (* Proving that reading previous bytes is the same as the spec *)
          REWRITE_TAC[ARITH_RULE `0x50 * i + 0x40 = 0x10 * (5 * i + 4)`;
                      ARITH_RULE `0x50 * i + 0x50 = 0x10 * (5 * i + 4) + 0x10`] THEN
          REWRITE_TAC[SUB_LIST_OF_AES256_XTS_ENCRYPT_FULL_BLOCKS] THEN
          ASM_REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_ASSOC] THEN CONV_TAC NUM_REDUCE_CONV
        ] THEN

        (** Reduce the goal to contain 0x50 * i + 0x30 **)
        IMP_REWRITE_TAC[ARITH_RULE `0x50 * i + 0x40 = (0x50 * i + 0x30) + 0x10`; READ_BYTES_AND_BYTE128_SPLIT] THEN
        EXISTS_TAC `(aes256_xts_encrypt pt_in (0x50 * i + 0x40) iv key1_lst key2_lst)` THEN
        REPEAT CONJ_TAC THENL [
          REWRITE_TAC [ARITH_RULE `(0x50 * i + 0x30) + 0x10 = 0x50 * i + 0x40`] THEN
          MP_TAC (SPECL [`0x5 * i + 0x4:num`; `pt_in:byte list`; `iv:int128`; `key1_lst:int128 list`;
                         `key2_lst:int128 list`] LENGTH_OF_AES256_XTS_ENCRYPT_FULL_BLOCKS) THEN
          REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_ASSOC; GSYM ADD_ASSOC] THEN
          CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
          IMP_REWRITE_TAC[SUB_LIST_LENGTH_IMPLIES];

          MP_TAC (SPECL [`0x5 * i + 0x4:num`; `pt_in:byte list`; `iv:int128`; `key1_lst:int128 list`;
                         `key2_lst:int128 list`] LENGTH_OF_AES256_XTS_ENCRYPT_FULL_BLOCKS) THEN
          REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_ASSOC; GSYM ADD_ASSOC] THEN
          CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
          IMP_REWRITE_TAC[SUB_LIST_LENGTH_IMPLIES] THEN
          ARITH_TAC;

          (* Establish that one xts decrypt round is the same as
             selecting one block of bytes from calling the top-level function. *)
          REWRITE_TAC[aes256_xts_encrypt] THEN
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

          MP_TAC (SPECL [`0`;`5 * i + 2:num`; `pt_in:byte list`; `iv:int128`; `key1_lst:int128 list`; `key2_lst:int128 list`]
                  LENGTH_OF_AES256_XTS_ENCRYPT_REC) THEN
          SIMP_TAC[ARITH_RULE `~(5 * i + 2 < 0)`;
                   ARITH_RULE `((0x5 * i + 0x2) - 0x0 + 0x1) * 0x10 = 0x50 * i + 0x30`] THEN
          IMP_REWRITE_TAC[SUB_LIST_APPEND_RIGHT_LEMMA] THEN DISCH_TAC THEN

          MP_TAC (SPECL [`5 * i + 3:num`; `0x0:num`; `pt_in:byte list`; `iv:int128`;
                         `key1_lst:int128 list`; `key2_lst:int128 list`]
                  LENGTH_OF_AES256_XTS_ENCRYPT_TAIL) THEN
          CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[ADD_0] THEN DISCH_TAC THEN
          IMP_REWRITE_TAC[SUB_LIST_LENGTH_IMPLIES] THEN

          REWRITE_TAC[AES256_XTS_ENCRYPT_TAIL_WHEN_1BLOCK] THEN
          SIMP_TAC[ARITH_RULE `i * 0x50 + 0x30 = (i * 0x5 + 0x3) * 0x10`;
                   ARITH_RULE `i * 0x5 = 0x5 * i`];

          (* Proving that reading previous bytes is the same as the spec *)
          REWRITE_TAC[ARITH_RULE `0x50 * i + 0x30 = 0x10 * (5 * i + 3)`;
                      ARITH_RULE `0x50 * i + 0x40 = 0x10 * (5 * i + 3) + 0x10`] THEN
          REWRITE_TAC[SUB_LIST_OF_AES256_XTS_ENCRYPT_FULL_BLOCKS] THEN
          ASM_REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_ASSOC] THEN CONV_TAC NUM_REDUCE_CONV
        ] THEN

        (** Reduce the goal to contain 0x50 * i + 0x20 **)
        IMP_REWRITE_TAC[ARITH_RULE `0x50 * i + 0x30 = (0x50 * i + 0x20) + 0x10`; READ_BYTES_AND_BYTE128_SPLIT] THEN
        EXISTS_TAC `(aes256_xts_encrypt pt_in (0x50 * i + 0x30) iv key1_lst key2_lst)` THEN
        REPEAT CONJ_TAC THENL [
          REWRITE_TAC [ARITH_RULE `(0x50 * i + 0x20) + 0x10 = 0x50 * i + 0x30`] THEN
          MP_TAC (SPECL [`0x5 * i + 0x3:num`; `pt_in:byte list`; `iv:int128`; `key1_lst:int128 list`;
                         `key2_lst:int128 list`] LENGTH_OF_AES256_XTS_ENCRYPT_FULL_BLOCKS) THEN
          REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_ASSOC; GSYM ADD_ASSOC] THEN
          CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
          IMP_REWRITE_TAC[SUB_LIST_LENGTH_IMPLIES];

          MP_TAC (SPECL [`0x5 * i + 0x3:num`; `pt_in:byte list`; `iv:int128`; `key1_lst:int128 list`;
                         `key2_lst:int128 list`] LENGTH_OF_AES256_XTS_ENCRYPT_FULL_BLOCKS) THEN
          REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_ASSOC; GSYM ADD_ASSOC] THEN
          CONV_TAC NUM_REDUCE_CONV THEN
          DISCH_TAC THEN
          ASM_REWRITE_TAC[] THEN
          ARITH_TAC;

          (* Establish that one xts decrypt round is the same as
             selecting one block of bytes from calling the top-level function. *)
          REWRITE_TAC[aes256_xts_encrypt] THEN
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

          MP_TAC (SPECL [`0`;`5 * i + 1:num`; `pt_in:byte list`; `iv:int128`; `key1_lst:int128 list`; `key2_lst:int128 list`]
                  LENGTH_OF_AES256_XTS_ENCRYPT_REC) THEN
          SIMP_TAC[ARITH_RULE `~(5 * i + 1 < 0)`;
                   ARITH_RULE `((0x5 * i + 0x1) - 0x0 + 0x1) * 0x10 = 0x50 * i + 0x20`] THEN
          IMP_REWRITE_TAC[SUB_LIST_APPEND_RIGHT_LEMMA] THEN DISCH_TAC THEN

          MP_TAC (SPECL [`5 * i + 2:num`; `0x0:num`; `pt_in:byte list`; `iv:int128`;
                         `key1_lst:int128 list`; `key2_lst:int128 list`]
                  LENGTH_OF_AES256_XTS_ENCRYPT_TAIL) THEN
          CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[ADD_0] THEN DISCH_TAC THEN
          IMP_REWRITE_TAC[SUB_LIST_LENGTH_IMPLIES] THEN

          REWRITE_TAC[AES256_XTS_ENCRYPT_TAIL_WHEN_1BLOCK] THEN
          SIMP_TAC[ARITH_RULE `i * 0x50 + 0x20 = (i * 0x5 + 0x2) * 0x10`;
                   ARITH_RULE `i * 0x5 = 0x5 * i`];

          (* Proving that reading previous bytes is the same as the spec *)
          REWRITE_TAC[ARITH_RULE `0x50 * i + 0x20 = 0x10 * (5 * i + 2)`;
                      ARITH_RULE `0x50 * i + 0x30 = 0x10 * (5 * i + 2) + 0x10`] THEN
          REWRITE_TAC[SUB_LIST_OF_AES256_XTS_ENCRYPT_FULL_BLOCKS] THEN
          ASM_REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_ASSOC] THEN CONV_TAC NUM_REDUCE_CONV
        ] THEN

        (** Reduce the goal to contain 0x50 * i + 0x10 **)
        REWRITE_TAC[ARITH_RULE `0x50 * i + 0x20 = (0x50 * i + 0x10) + 0x10`] THEN
        (* Use SPECL to force IMP_REWRITE_TAC to apply once *)
        IMP_REWRITE_TAC[(SPECL [`ctxt_p:int64`; `(0x50 * i + 0x10):num`;
          `x:byte list`; `s188:armstate`] READ_BYTES_AND_BYTE128_SPLIT)] THEN
        EXISTS_TAC `(aes256_xts_encrypt pt_in (0x50 * i + 0x20) iv key1_lst key2_lst)` THEN
        REPEAT CONJ_TAC THENL [
          REWRITE_TAC [ARITH_RULE `(0x50 * i + 0x10) + 0x10 = 0x50 * i + 0x20`] THEN
          MP_TAC (SPECL [`0x5 * i + 0x2:num`; `pt_in:byte list`; `iv:int128`; `key1_lst:int128 list`;
                         `key2_lst:int128 list`] LENGTH_OF_AES256_XTS_ENCRYPT_FULL_BLOCKS) THEN
          REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_ASSOC; GSYM ADD_ASSOC] THEN
          CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
          IMP_REWRITE_TAC[SUB_LIST_LENGTH_IMPLIES];

          MP_TAC (SPECL [`0x5 * i + 0x2:num`; `pt_in:byte list`; `iv:int128`; `key1_lst:int128 list`;
                         `key2_lst:int128 list`] LENGTH_OF_AES256_XTS_ENCRYPT_FULL_BLOCKS) THEN
          REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_ASSOC; GSYM ADD_ASSOC] THEN
          CONV_TAC NUM_REDUCE_CONV THEN
          DISCH_TAC THEN
          ASM_REWRITE_TAC[] THEN
          ARITH_TAC;

          (* Establish that one xts decrypt round is the same as
             selecting one block of bytes from calling the top-level function. *)
          REWRITE_TAC[aes256_xts_encrypt] THEN
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

          MP_TAC (SPECL [`0`;`5 * i:num`; `pt_in:byte list`; `iv:int128`; `key1_lst:int128 list`; `key2_lst:int128 list`]
                  LENGTH_OF_AES256_XTS_ENCRYPT_REC) THEN
          SIMP_TAC[ARITH_RULE `~(5 * i < 0)`;
                   ARITH_RULE `((0x5 * i) - 0x0 + 0x1) * 0x10 = 0x50 * i + 0x10`] THEN
          IMP_REWRITE_TAC[SUB_LIST_APPEND_RIGHT_LEMMA] THEN DISCH_TAC THEN

          MP_TAC (SPECL [`5 * i + 1:num`; `0x0:num`; `pt_in:byte list`; `iv:int128`;
                         `key1_lst:int128 list`; `key2_lst:int128 list`]
                  LENGTH_OF_AES256_XTS_ENCRYPT_TAIL) THEN
          CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[ADD_0] THEN DISCH_TAC THEN
          IMP_REWRITE_TAC[SUB_LIST_LENGTH_IMPLIES] THEN

          REWRITE_TAC[AES256_XTS_ENCRYPT_TAIL_WHEN_1BLOCK] THEN
          SIMP_TAC[ARITH_RULE `i * 0x50 + 0x10 = (i * 0x5 + 0x1) * 0x10`;
                   ARITH_RULE `i * 0x5 = 0x5 * i`];

          (* Proving that reading previous bytes is the same as the spec *)
          REWRITE_TAC[ARITH_RULE `0x50 * i + 0x10 = 0x10 * (5 * i + 1)`;
                      ARITH_RULE `0x50 * i + 0x20 = 0x10 * (5 * i + 1) + 0x10`] THEN
          REWRITE_TAC[SUB_LIST_OF_AES256_XTS_ENCRYPT_FULL_BLOCKS] THEN
          ASM_REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_ASSOC] THEN CONV_TAC NUM_REDUCE_CONV
        ] THEN

        (** Reduce the goal to 0x50 * i **)
        (*
        `read (memory :> bytes (ctxt_p,0x50 * i + 0x10)) s188 =
          num_of_bytelist
          (aes256_xts_encrypt pt_in (0x50 * i + 0x10) iv key1_lst key2_lst)`
        *)
        (* Using SPECL with `x` does not yield a correct goal; it contains as one of the conjuctions:
           `num_of_bytelist
            (SUB_LIST (0x0,0x50 * i + 0x10)
            (aes256_xts_encrypt pt_in (i * 0x50) iv key1_lst key2_lst)) =
            num_of_bytelist
            (aes256_xts_encrypt pt_in (0x50 * i + 0x10) iv key1_lst key2_lst)
        *)
        IMP_REWRITE_TAC[(SPECL [`ctxt_p:int64`; `(0x50 * i):num`;
          `(aes256_xts_encrypt pt_in (0x50 * i + 0x10) iv key1_lst key2_lst):byte list`; `s188:armstate`]
          READ_BYTES_AND_BYTE128_SPLIT)] THEN
        EXISTS_TAC `iv:int128` THEN EXISTS_TAC `key1_lst:int128 list` THEN
        EXISTS_TAC `key2_lst:int128 list` THEN EXISTS_TAC `pt_in:byte list` THEN

        REPEAT CONJ_TAC THENL [
          MP_TAC (SPECL [`0x5 * i + 0x1:num`; `pt_in:byte list`; `iv:int128`; `key1_lst:int128 list`;
                         `key2_lst:int128 list`] LENGTH_OF_AES256_XTS_ENCRYPT_FULL_BLOCKS) THEN
          REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_ASSOC; GSYM ADD_ASSOC] THEN
          CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
          IMP_REWRITE_TAC[SUB_LIST_LENGTH_IMPLIES];

          MP_TAC (SPECL [`0x5 * i + 0x1:num`; `pt_in:byte list`; `iv:int128`; `key1_lst:int128 list`;
                         `key2_lst:int128 list`] LENGTH_OF_AES256_XTS_ENCRYPT_FULL_BLOCKS) THEN
          REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_ASSOC; GSYM ADD_ASSOC] THEN
          CONV_TAC NUM_REDUCE_CONV THEN
          DISCH_TAC THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;

          (* Establish that one xts decrypt round is the same as
             selecting one block of bytes from calling the top-level function. *)
          REWRITE_TAC[aes256_xts_encrypt] THEN
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

            MP_TAC (SPECL [`0:num`; `0x0:num`; `pt_in:byte list`; `iv:int128`; `key1_lst:int128 list`; `key2_lst:int128 list`]
                          LENGTH_OF_AES256_XTS_ENCRYPT_TAIL) THEN
            CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[ADD_0] THEN DISCH_TAC THEN
            IMP_REWRITE_TAC[(ISPECL [`(aes256_xts_encrypt_tail 0x0 0x0 pt_in iv key1_lst key2_lst):byte list`;
                                     `0x10:num`] SUB_LIST_LENGTH_IMPLIES)] THEN

            REWRITE_TAC[AES256_XTS_ENCRYPT_TAIL_WHEN_1BLOCK] THEN
            CONV_TAC NUM_REDUCE_CONV;

            (* i != 0 *)
            SIMP_TAC[ARITH_RULE `(0x5 * i + 0x1) - 0x2 = 0x5 * i - 0x1`;
                     ARITH_RULE `(0x5 * i + 0x1) - 0x1 = 0x5 * i`] THEN
            MP_TAC (SPECL [`0`;`5 * i - 1:num`; `pt_in:byte list`; `iv:int128`; `key1_lst:int128 list`; `key2_lst:int128 list`]
                    LENGTH_OF_AES256_XTS_ENCRYPT_REC) THEN
            SUBGOAL_THEN `~(0x5 * i - 0x1 < 0x0)` ASSUME_TAC THENL
            [ UNDISCH_TAC `~(0x5 * i + 0x1 < 0x2)` THEN ARITH_TAC; ALL_TAC ] THEN
            ASM_SIMP_TAC[] THEN
            IMP_REWRITE_TAC[ARITH_RULE `~(0x5 * i + 0x1 < 0x2) ==> (0x5 * i - 1 - 0x0 + 0x1) * 0x10 = 0x50 * i`] THEN
            IMP_REWRITE_TAC[SUB_LIST_APPEND_RIGHT_LEMMA] THEN DISCH_TAC THEN

            MP_TAC (SPECL [`5 * i:num`; `0x0:num`; `pt_in:byte list`; `iv:int128`;
                          `key1_lst:int128 list`; `key2_lst:int128 list`]
                          LENGTH_OF_AES256_XTS_ENCRYPT_TAIL) THEN
            CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[ADD_0] THEN DISCH_TAC THEN
            IMP_REWRITE_TAC[SUB_LIST_LENGTH_IMPLIES] THEN

            REWRITE_TAC[AES256_XTS_ENCRYPT_TAIL_WHEN_1BLOCK] THEN
            SIMP_TAC[ARITH_RULE `i * 0x50 = (i * 0x5) * 0x10`;
                     ARITH_RULE `i * 0x5 = 0x5 * i`]
          ];

          (* Proving that reading previous bytes is the same as the spec *)
          REWRITE_TAC[ARITH_RULE `i * 0x50 = 0x50 * i`;
                      ARITH_RULE `0x50 * i = 0x10 * 5 * i`;
                      ARITH_RULE `0x50 * i + 0x10 = 0x10 * 5 * i + 0x10`] THEN
          REWRITE_TAC[SUB_LIST_OF_AES256_XTS_ENCRYPT_FULL_BLOCKS] THEN
          IMP_REWRITE_TAC[SUB_LIST_LENGTH_IMPLIES] THEN
          REWRITE_TAC[LENGTH_OF_AES256_XTS_ENCRYPT_FULL_BLOCKS]
        ];

        (* 4 goals total from here *)
        SUBGOAL_THEN  `i + 1 < 2 EXP 64` ASSUME_TAC THENL
        [
          UNDISCH_TAC `i < val (num_5blocks:int64)` THEN
          EXPAND_TAC "num_5blocks" THEN
          UNDISCH_TAC `val (len_full_blocks:int64) <= 0x2 EXP 0x18` THEN
          REWRITE_TAC [VAL_WORD; DIMINDEX_64] THEN ARITH_TAC; ALL_TAC
        ] THEN
        EQ_TAC THENL
        [ REWRITE_TAC[WORD_RULE `!x:int64 a b. (word_sub (word_sub x a) b) = word_sub x (word_add a b)`] THEN
          ASM_SIMP_TAC[WORD_RULE `!a b. a + b < 2 EXP 64 ==> (word_add (word a) (word b)) = word (a + b)`] THEN
          REWRITE_TAC[VAL_EQ_0; WORD_SUB_EQ_0] THEN
          DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
          IMP_REWRITE_TAC[VAL_WORD; DIMINDEX_64; MOD_LT];
          REWRITE_TAC[WORD_RULE `!x:int64 a b. (word_sub (word_sub x a) b) = word_sub x (word_add a b)`] THEN
          ASM_SIMP_TAC[WORD_RULE `!a b. a + b < 2 EXP 64 ==> (word_add (word a) (word b)) = word (a + b)`] THEN
          REWRITE_TAC[VAL_EQ_0; WORD_SUB_EQ_0; WORD_VAL]
        ]
      ]; (* 3 goals total from here *)

      (** Subgoal 4 of main loop invariant:
         prove backedge is taken if i != val num_5blocks **)
      REPEAT STRIP_TAC THEN
      REWRITE_TAC[byte_list_at] THEN
      ENSURES_INIT_TAC "s0" THEN
      ARM_ACCSTEPS_TAC AES256_XTS_ENCRYPT_EXEC [] (1--1) THEN
      SUBGOAL_THEN `~(val (word_sub (num_5blocks:int64) (word i)) = 0x0)` ASSUME_TAC THENL
      [ UNDISCH_TAC `i < val (num_5blocks:int64)` THEN WORD_ARITH_TAC; ALL_TAC] THEN
      POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_SIMP_TAC[]; (* 2 goals total from here *)

      (** Subgoal 5: Prove the invariant implies post-condition
                    Backedge instruction is executed here **)
      REPEAT STRIP_TAC THEN
      REWRITE_TAC[byte_list_at] THEN
      SUBST_ALL_TAC (WORD_RULE `(word (val (num_5blocks:int64))):int64 = num_5blocks`) THEN

      MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN
      EXISTS_TAC `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
        MAYCHANGE [X19; X20; X21; X22],,
        MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15],,
        if val (num_5blocks:int64) * 0x50 + 0x40 = val (len_full_blocks:int64)
        then
        MAYCHANGE [memory :> bytes128 (word_add ctxt_p (word (0x50 * val (num_5blocks:int64))));
                    memory :> bytes128 (word_add ctxt_p (word (0x50 * val num_5blocks + 0x10)));
                    memory :> bytes128 (word_add ctxt_p (word (0x50 * val num_5blocks + 0x20)));
                    memory :> bytes128 (word_add ctxt_p (word (0x50 * val num_5blocks + 0x30)))]
        else
        (if val (num_5blocks:int64) * 0x50 + 0x30 = val (len_full_blocks:int64)
          then
          MAYCHANGE [memory :> bytes128 (word_add ctxt_p (word (0x50 * val (num_5blocks:int64))));
                    memory :> bytes128 (word_add ctxt_p (word (0x50 * val num_5blocks + 0x10)));
                    memory :> bytes128 (word_add ctxt_p (word (0x50 * val num_5blocks + 0x20)))]
          else
          (if val (num_5blocks:int64) * 0x50 + 0x20 = val (len_full_blocks:int64)
          then
          MAYCHANGE [memory :> bytes128 (word_add ctxt_p (word (0x50 * val (num_5blocks:int64))));
                      memory :> bytes128 (word_add ctxt_p (word (0x50 * val num_5blocks + 0x10)))]
          else
          (if val (num_5blocks:int64) * 0x50 + 0x10 = val (len_full_blocks:int64)
            then
            MAYCHANGE [memory :> bytes128 (word_add ctxt_p (word (0x50 * val (num_5blocks:int64))))]
            else
            MAYCHANGE [])))
            ` THEN
      REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
      CONJ_TAC THENL [
        REPEAT (GEN_REWRITE_TAC ONCE_DEPTH_CONV [GSYM SEQ_ASSOC] THEN
                MATCH_MP_TAC SUBSUMED_SEQ THEN REWRITE_TAC[SUBSUMED_REFL]) THEN
        REPEAT COND_CASES_TAC THENL
        [ SUBGOAL_THEN `0x50 * val (num_5blocks:int64) + 0x40 <= val (len:int64)` ASSUME_TAC THENL
          [ ASM_ARITH_TAC; ALL_TAC] THEN
          ABBREV_TAC `val5blocks = val (num_5blocks:int64)` THEN
          ABBREV_TAC `vallen = val (len:int64)` THEN
          SUBSUMED_MAYCHANGE_TAC;
          SUBGOAL_THEN `0x50 * val (num_5blocks:int64) + 0x30 <= val (len:int64)` ASSUME_TAC THENL
          [ ASM_ARITH_TAC; ALL_TAC] THEN
          ABBREV_TAC `val5blocks = val (num_5blocks:int64)` THEN
          ABBREV_TAC `vallen = val (len:int64)` THEN
          SUBSUMED_MAYCHANGE_TAC;
          SUBGOAL_THEN `0x50 * val (num_5blocks:int64) + 0x20 <= val (len:int64)` ASSUME_TAC THENL
          [ ASM_ARITH_TAC; ALL_TAC] THEN
          ABBREV_TAC `val5blocks = val (num_5blocks:int64)` THEN
          ABBREV_TAC `vallen = val (len:int64)` THEN
          SUBSUMED_MAYCHANGE_TAC;
          SUBGOAL_THEN `0x50 * val (num_5blocks:int64) + 0x10 <= val (len:int64)` ASSUME_TAC THENL
          [ ASM_ARITH_TAC; ALL_TAC] THEN
          ABBREV_TAC `val5blocks = val (num_5blocks:int64)` THEN
          ABBREV_TAC `vallen = val (len:int64)` THEN
          SUBSUMED_MAYCHANGE_TAC;
          SUBSUMED_MAYCHANGE_TAC]
        ; ALL_TAC
      ] THEN

      ENSURES_INIT_TAC "s0" THEN
      ARM_ACCSTEPS_TAC AES256_XTS_ENCRYPT_EXEC [] (1--3) THEN
      FIRST_X_ASSUM MP_TAC THEN

      (* Assumptions that help with reasoning about nonoverlapping
        so that the universally quantified assumption stays.
        See: https://hol-light.zulipchat.com/#narrow/channel/474190-s2n-bignum/topic/.E2.9C.94.20Symbolic.20simulation.20removed.20assumption/with/541554894 *)
      SUBGOAL_THEN `(val (num_5blocks:int64)) * 0x50 < 0x2 EXP 0x40` ASSUME_TAC THENL
      [ UNDISCH_TAC `val (num_5blocks:int64) * 0x50 <= val (len_full_blocks:int64)` THEN
        UNDISCH_TAC `val (len_full_blocks:int64) <= 0x2 EXP 0x18` THEN
        ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `val ((word (val (num_5blocks:int64) * 0x50)):int64) = 0x50 * val num_5blocks` ASSUME_TAC THENL [
        IMP_REWRITE_TAC[VAL_WORD; DIMINDEX_64; MOD_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
      POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN

      COND_CASES_TAC THENL
      [ (* Case: len % 0x50 = 0x40 *)
        DISCH_TAC THEN

        SUBGOAL_THEN `val (num_5blocks:int64) * 0x50 + 0x40 = val (len_full_blocks:int64)` ASSUME_TAC THENL
        [ UNDISCH_TAC `val (word_sub
            (word_sub (len_full_blocks:int64)
                      (word_mul (word 0x50) (num_5blocks:int64)))
            (word 0x40)) =
            0x0` THEN
          REWRITE_TAC [VAL_EQ_0; WORD_SUB_EQ_0] THEN
          REWRITE_TAC [WORD_RULE `!x:int64. word_mul (word 0x50) x = word(val x * 0x50)`] THEN
          REWRITE_TAC[GSYM VAL_EQ] THEN
          SUBGOAL_THEN `val (num_5blocks:int64) * 0x50 < 2 EXP 64` MP_TAC THENL
          [ UNDISCH_TAC `val (num_5blocks:int64) * 0x50 <= val (len_full_blocks:int64)` THEN
            UNDISCH_TAC `val (len_full_blocks:int64) <= 2 EXP 24` THEN
            ARITH_TAC; ALL_TAC] THEN
          REWRITE_TAC[VAL_WORD_SUB_CASES] THEN
          SIMP_TAC[VAL_WORD; DIMINDEX_64; MOD_LT] THEN
          UNDISCH_TAC `val (num_5blocks:int64) * 0x50 <= val (len_full_blocks:int64)` THEN
          NUM_REDUCE_TAC THEN ARITH_TAC
        ; ALL_TAC] THEN

        SUBGOAL_THEN `val (num_5blocks:int64) * 0x50 + 0x40 <= val (len:int64)` ASSUME_TAC THENL
        [ UNDISCH_TAC `val (num_5blocks:int64) * 0x50 + 0x40 = val (len_full_blocks:int64)` THEN
          UNDISCH_TAC `val (len_full_blocks:int64) <= val (len:int64)` THEN
          ARITH_TAC
        ; ALL_TAC] THEN
        MP_TAC (SPECL [`ptxt_p:int64`; `num_5blocks:int64`; `len:int64`; `pt_in:byte list`; `s3:armstate`] READ_TAIL4_LEMMA) THEN
        ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN

        ARM_ACCSTEPS_TAC AES256_XTS_ENCRYPT_EXEC [] (4--127) THEN
        XTSENC_TAC `Q0:(armstate,int128)component`
          `val (num_5blocks:int64) * 0x50` `val (num_5blocks:int64) * 0x5` THEN
        XTSENC_TAC `Q1:(armstate,int128)component`
          `val (num_5blocks:int64) * 0x50 + 0x10` `val (num_5blocks:int64) * 0x5 + 0x1` THEN
        XTSENC_TAC `Q24:(armstate,int128)component`
          `val (num_5blocks:int64) * 0x50 + 0x20` `val (num_5blocks:int64) * 0x5 + 0x2` THEN
        XTSENC_TAC `Q25:(armstate,int128)component`
          `val (num_5blocks:int64) * 0x50 + 0x30` `val (num_5blocks:int64) * 0x5 + 0x3` THEN

        (* The following lemmas are for NONSELFMODIFYING_STATE_UPDATE_TAC when store back to ctxt_p
           Otherwise symbolic simulation fails with
           Failure "could not prove that updates will not modify the program code" *)
        CHANGED_TAC (RULE_ASSUM_TAC(REWRITE_RULE
          [WORD_RULE `word_mul (word 0x50) num_5blocks:int64 = word(0x50 * val num_5blocks)`])) THEN
        CHANGED_TAC (RULE_ASSUM_TAC(REWRITE_RULE
          [WORD_RULE `!base m n. word_add (word_add base (word m)) (word n) = word_add base (word(m + n))`])) THEN

        ARM_ACCSTEPS_TAC AES256_XTS_ENCRYPT_EXEC [] (128--128) THEN (* Store 2 blocks in ctxt_p *)
        (* Need to simplify the expression for X1 after the first store instruction *)
        CHANGED_TAC (RULE_ASSUM_TAC(REWRITE_RULE
          [WORD_RULE `!base m n. word_add (word_add base (word m)) (word n) = word_add base (word(m + n))`])) THEN

        ARM_ACCSTEPS_TAC AES256_XTS_ENCRYPT_EXEC [] (129--137) THEN (* Store 2 blocks and calculate tweak *)
        TWEAK_TAC `Q6:(armstate,int128)component` `val (num_5blocks:int64) * 0x5 + 0x4` `val (num_5blocks:int64) * 0x5 + 0x3` THEN

        ARM_ACCSTEPS_TAC AES256_XTS_ENCRYPT_EXEC [] (138--138) THEN
        ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
        (*` word_add ptxt_p (word (0x50 * val num_5blocks + 0x40)) =
            word_add ptxt_p (word (acc_len num_5blocks len_full_blocks)) /\
            word_add (word_add ctxt_p (word (0x50 * val num_5blocks))) (word 0x40) =
            word_add ctxt_p (word (acc_len num_5blocks len_full_blocks)) /\
            calculate_tweak (val num_5blocks * 0x5 + 0x4) iv key2_lst =
            calculate_tweak (acc_blocks num_5blocks len_full_blocks true) iv key2_lst /\
            (forall i.
                  i < val (word (acc_len num_5blocks len_full_blocks))
                  ==> read (memory :> bytes8 (word_add ctxt_p (word i))) s138 =
                      EL i (aes256_xts_encrypt pt_in (acc_len num_5blocks len_full_blocks) iv key1_lst key2_lst))`  *)
        REPEAT CONJ_TAC THENL (* 4 subgoals (6 total) *)
        [
          REWRITE_TAC[acc_len] THEN ASM_SIMP_TAC[] THEN CONV_TAC WORD_RULE;
          REWRITE_TAC[acc_len] THEN ASM_SIMP_TAC[] THEN CONV_TAC WORD_RULE;
          REWRITE_TAC[acc_blocks] THEN ASM_SIMP_TAC[] THEN CONV_TAC WORD_RULE;

          REWRITE_TAC[acc_len] THEN ASM_SIMP_TAC[LE_REFL] THEN
          SUBGOAL_THEN `val ((word (0x50 * val (num_5blocks:int64) + 0x40)):int64) =
            0x50 * val num_5blocks + 0x40` ASSUME_TAC THENL
          [ IMP_REWRITE_TAC[VAL_WORD; MOD_LT; DIMINDEX_64] THEN
            UNDISCH_TAC `val (num_5blocks:int64) * 0x50 + 0x40 <= val (len:int64)` THEN
            UNDISCH_TAC `val (len:int64) <= 0x2 EXP 0x18` THEN
            ARITH_TAC; ALL_TAC] THEN
          CHANGED_TAC (POP_ASSUM(fun th -> REWRITE_TAC[th])) THEN
          (* `forall i.
              i < 0x50 * val num_5blocks + 0x40
              ==> read (memory :> bytes8 (word_add ctxt_p (word i))) s138 =
                  EL i  (aes256_xts_encrypt pt_in (0x50 * val num_5blocks + 0x40) iv key1_lst key2_lst)` *)

          (* Remove quantifier in conclusion then in antecedent of the goal:
           ==> (forall i.
          i < 0x50 * val num_5blocks
             ==> read (memory :> bytes8 (word_add ctxt_p (word i))) s138 =
              EL i (aes256_xts_encrypt pt_in (val num_5blocks * 0x50) iv key1_lst  key2_lst))
          ==> (forall i.
              i < 0x50 * val num_5blocks + 0x40
              ==> read (memory :> bytes8 (word_add ctxt_p (word i))) s138 =
                  EL i (aes256_xts_encrypt pt_in (0x50 * val num_5blocks + 0x40) iv key1_lst key2_lst))`  *)
          UNDISCH_TAC
          `forall i.
            i < 0x50 * val (num_5blocks:int64)
            ==> read (memory :> bytes8 (word_add ctxt_p (word i))) s138 =
                EL i (aes256_xts_encrypt pt_in (val num_5blocks * 0x50) iv key1_lst key2_lst)` THEN
          MP_TAC (SPECL [`0x50 * val (num_5blocks:int64) + 0x40:num`; `ctxt_p:int64`;
                         `(aes256_xts_encrypt pt_in (0x50 * val (num_5blocks:int64) + 0x40) iv key1_lst key2_lst):byte list`;
                         `s138:armstate`] BYTE_LIST_TO_NUM_THM) THEN
          ANTS_TAC THENL[
            REWRITE_TAC[ARITH_RULE `0x50 * i + 0x40 = 0x10 * (5 * i + 4)`;
                        LENGTH_OF_AES256_XTS_ENCRYPT_FULL_BLOCKS] THEN
            ARITH_TAC
            ; ALL_TAC] THEN
          DISCH_THEN (fun th -> REWRITE_TAC[th]) THEN

          MP_TAC (SPECL [`0x50 * val (num_5blocks:int64):num`; `ctxt_p:int64`;
                         `(aes256_xts_encrypt pt_in (val (num_5blocks:int64) * 0x50) iv key1_lst key2_lst):byte list`;
                         `s138:armstate`] BYTE_LIST_TO_NUM_THM) THEN
          ANTS_TAC THENL[
            REWRITE_TAC[ARITH_RULE `i * 0x50 = 0x10 * 5 * i`;
                        LENGTH_OF_AES256_XTS_ENCRYPT_FULL_BLOCKS] THEN
            ARITH_TAC
            ; ALL_TAC] THEN
          DISCH_THEN (fun th -> REWRITE_TAC[th]) THEN
(* `read (memory :> bytes (ctxt_p,0x50 * val num_5blocks)) s138 =
    num_of_bytelist
    (SUB_LIST (0x0,0x50 * val num_5blocks)
    (aes256_xts_encrypt pt_in (val num_5blocks * 0x50) iv key1_lst key2_lst))
    ==> read (memory :> bytes (ctxt_p,0x50 * val num_5blocks + 0x40)) s138 =
        num_of_bytelist
        (SUB_LIST (0x0,0x50 * val num_5blocks + 0x40)
        (aes256_xts_encrypt pt_in (0x50 * val num_5blocks + 0x40) iv key1_lst
        key2_lst))` *)
          DISCH_TAC THEN

          IMP_REWRITE_TAC[ARITH_RULE `0x50 * i + 0x40 = (0x50 * i + 0x30) + 0x10`; READ_BYTES_AND_BYTE128_SPLIT] THEN
          EXISTS_TAC `(aes256_xts_encrypt pt_in (0x50 * val (num_5blocks:int64) + 0x40) iv key1_lst key2_lst)` THEN
          (*`num_of_bytelist
            (SUB_LIST (0x0,(0x50 * val num_5blocks + 0x30) + 0x10)
            (aes256_xts_encrypt pt_in (0x50 * val num_5blocks + 0x40) iv key1_lst key2_lst)) =
            num_of_bytelist (SUB_LIST (0x0,(0x50 * val num_5blocks + 0x30) + 0x10)
            (aes256_xts_encrypt pt_in ((0x50 * val num_5blocks + 0x30) + 0x10) iv  key1_lst key2_lst)) /\
            (0x50 * val num_5blocks + 0x30) + 0x10 <=
              LENGTH (aes256_xts_encrypt pt_in (0x50 * val num_5blocks + 0x40) iv key1_lst key2_lst) /\
            read (memory :>  bytes128 (word_add ctxt_p (word (0x50 * val num_5blocks + 0x30)))) s138 =
            bytes_to_int128 (SUB_LIST (0x50 * val num_5blocks + 0x30,0x10)
            (aes256_xts_encrypt pt_in (0x50 * val num_5blocks + 0x40) iv key1_lst key2_lst)) /\
            read (memory :> bytes (ctxt_p,0x50 * val num_5blocks + 0x30)) s138 =
            num_of_bytelist (SUB_LIST (0x0,0x50 * val num_5blocks + 0x30)
            (aes256_xts_encrypt pt_in (0x50 * val num_5blocks + 0x40) iv key1_lst key2_lst))`*)
          REPEAT CONJ_TAC THENL [ (* 4 subgoals *)
            REWRITE_TAC [ARITH_RULE `(0x50 * i + 0x30) + 0x10 = 0x50 * i + 0x40`];
(* `(0x50 * val num_5blocks + 0x30) + 0x10 <=
   LENGTH (aes256_xts_encrypt pt_in (0x50 * val num_5blocks + 0x40) iv key1_lst key2_lst)` *)
            MP_TAC (SPECL [`0x5 * val (num_5blocks:int64) + 0x4:num`;
              `pt_in:byte list`; `iv:int128`; `key1_lst:int128 list`;
              `key2_lst:int128 list`] LENGTH_OF_AES256_XTS_ENCRYPT_FULL_BLOCKS) THEN
            REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_ASSOC; GSYM ADD_ASSOC] THEN
            CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
            ASM_REWRITE_TAC[] THEN ARITH_TAC;
(* `read (memory :>  bytes128 (word_add ctxt_p (word (0x50 * val num_5blocks + 0x30)))) s138 =
 bytes_to_int128 (SUB_LIST (0x50 * val num_5blocks + 0x30,0x10)
 (aes256_xts_encrypt pt_in (0x50 * val num_5blocks + 0x40) iv key1_lst key2_lst))` *)

           (* Establish that one xts encrypt round is the same as
               selecting one block of bytes from calling the top-level function. *)
          CHANGED_TAC(RULE_ASSUM_TAC(REWRITE_RULE
          [ARITH_RULE `(0x50 * val (num_5blocks:int64) + 0x20) + 0x10 = 0x50 * val num_5blocks + 0x30`])) THEN
          ASM_REWRITE_TAC[] THEN
(*
`aes256_xts_encrypt_round
 (bytes_to_int128 (SUB_LIST (val num_5blocks * 0x50 + 0x30,0x10) pt_in))
 (calculate_tweak (val num_5blocks * 0x5 + 0x3) iv key2_lst)
 key1_lst =
 bytes_to_int128
 (SUB_LIST (0x50 * val num_5blocks + 0x30,0x10)
 (aes256_xts_encrypt pt_in (0x50 * val num_5blocks + 0x40) iv key1_lst
 key2_lst))`
*)
            REWRITE_TAC[aes256_xts_encrypt] THEN
            SIMP_TAC[ARITH_RULE `~(0x50 * val (num_5blocks:int64) + 0x40 < 0x10)`] THEN
            SUBGOAL_THEN `(0x50 * val (num_5blocks:int64) + 0x40) MOD 0x10 = 0` SUBST1_TAC THENL
            [ REWRITE_TAC[ARITH_RULE `80 * i + 64 = 16 * (5 * i + 4)`] THEN
              REWRITE_TAC[MOD_MULT]
            ; ALL_TAC] THEN
            CONV_TAC (DEPTH_CONV let_CONV) THEN
            REWRITE_TAC[SUB_0; ARITH_RULE `(0x50 * i + 0x40) DIV 0x10 = 0x5 * i + 0x4`] THEN
            SIMP_TAC[ARITH_RULE `~(0x5 * i + 0x4 < 0x2)`;
                    ARITH_RULE `(0x5 * i + 0x4) - 0x2 = 0x5 * i + 0x2`;
                    ARITH_RULE `(0x5 * i + 0x4) - 0x1 = 0x5 * i + 0x3`] THEN
(*
`aes256_xts_encrypt_round
 (bytes_to_int128 (SUB_LIST (val num_5blocks * 0x50 + 0x30,0x10) pt_in))
 (calculate_tweak (val num_5blocks * 0x5 + 0x3) iv key2_lst)
 key1_lst =
 bytes_to_int128
 (SUB_LIST (0x50 * val num_5blocks + 0x30,0x10)
 (APPEND
  (aes256_xts_encrypt_rec 0x0 (0x5 * val num_5blocks + 0x2) pt_in iv key1_lst
  key2_lst)
 (aes256_xts_encrypt_tail (0x5 * val num_5blocks + 0x3) 0x0 pt_in iv key1_lst
 key2_lst)))`
*)
            MP_TAC (SPECL [`0`;`5 * val (num_5blocks:int64) + 2:num`; `pt_in:byte list`; `iv:int128`;
                          `key1_lst:int128 list`; `key2_lst:int128 list`]
                    LENGTH_OF_AES256_XTS_ENCRYPT_REC) THEN
            SIMP_TAC[ARITH_RULE `~(5 * i + 2 < 0)`;
                    ARITH_RULE `((0x5 * i + 0x2) - 0x0 + 0x1) * 0x10 = 0x50 * i + 0x30`] THEN
(*
`LENGTH
 (aes256_xts_encrypt_rec 0x0 (0x5 * val num_5blocks + 0x2) pt_in iv key1_lst
 key2_lst) =
 0x50 * val num_5blocks + 0x30
 ==> aes256_xts_encrypt_round
     (bytes_to_int128 (SUB_LIST (val num_5blocks * 0x50 + 0x30,0x10) pt_in))
     (calculate_tweak (val num_5blocks * 0x5 + 0x3) iv key2_lst)
     key1_lst =
     bytes_to_int128
     (SUB_LIST (0x50 * val num_5blocks + 0x30,0x10)
     (APPEND
      (aes256_xts_encrypt_rec 0x0 (0x5 * val num_5blocks + 0x2) pt_in iv
       key1_lst
      key2_lst)
     (aes256_xts_encrypt_tail (0x5 * val num_5blocks + 0x3) 0x0 pt_in iv
      key1_lst
     key2_lst)))`
*)
            IMP_REWRITE_TAC[SUB_LIST_APPEND_RIGHT_LEMMA] THEN DISCH_TAC THEN
(*
`aes256_xts_encrypt_round
 (bytes_to_int128 (SUB_LIST (val num_5blocks * 0x50 + 0x30,0x10) pt_in))
 (calculate_tweak (val num_5blocks * 0x5 + 0x3) iv key2_lst)
 key1_lst =
 bytes_to_int128
 (SUB_LIST (0x0,0x10)
 (aes256_xts_encrypt_tail (0x5 * val num_5blocks + 0x3) 0x0 pt_in iv key1_lst
 key2_lst))`
*)

            MP_TAC (SPECL [`5 * val (num_5blocks:int64) + 3:num`; `0x0:num`; `pt_in:byte list`; `iv:int128`;
                          `key1_lst:int128 list`; `key2_lst:int128 list`]
                    LENGTH_OF_AES256_XTS_ENCRYPT_TAIL) THEN
            CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[ADD_0] THEN DISCH_TAC THEN
(*
`aes256_xts_encrypt_round
 (bytes_to_int128 (SUB_LIST (val num_5blocks * 0x50 + 0x30,0x10) pt_in))
 (calculate_tweak (val num_5blocks * 0x5 + 0x3) iv key2_lst)
 key1_lst =
 bytes_to_int128
 (SUB_LIST (0x0,0x10)
 (aes256_xts_encrypt_tail (0x5 * val num_5blocks + 0x3) 0x0 pt_in iv key1_lst
 key2_lst))`
*)
            IMP_REWRITE_TAC[SUB_LIST_LENGTH_IMPLIES] THEN
(*
`aes256_xts_encrypt_round
 (bytes_to_int128 (SUB_LIST (val num_5blocks * 0x50 + 0x30,0x10) pt_in))
 (calculate_tweak (val num_5blocks * 0x5 + 0x3) iv key2_lst)
 key1_lst =
 bytes_to_int128
 (aes256_xts_encrypt_tail (0x5 * val num_5blocks + 0x3) 0x0 pt_in iv key1_lst
 key2_lst)`
*)
            REWRITE_TAC[AES256_XTS_ENCRYPT_TAIL_WHEN_1BLOCK] THEN
            ASM_SIMP_TAC[ARITH_RULE `(i * 0x5 + 0x3) * 0x10 = i * 0x50 + 0x30`;
                         ARITH_RULE `5 * i + 3 = i * 5 + 3`]; (* 3 total *)
(*`read (memory :> bytes (ctxt_p,0x50 * val num_5blocks + 0x30)) s138 =
   num_of_bytelist (SUB_LIST (0x0,0x50 * val num_5blocks + 0x30)
     (aes256_xts_encrypt pt_in (0x50 * val num_5blocks + 0x40) iv key1_lst key2_lst))` *)
            (* Proving that reading previous bytes is the same as the spec *)
            REWRITE_TAC[ARITH_RULE `0x50 * i + 0x30 = 0x10 * (5 * i + 3)`;
                        ARITH_RULE `0x50 * i + 0x40 = 0x10 * (5 * i + 3) + 0x10`] THEN
            REWRITE_TAC[SUB_LIST_OF_AES256_XTS_ENCRYPT_FULL_BLOCKS] THEN
            ASM_REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_ASSOC] THEN CONV_TAC NUM_REDUCE_CONV (* 3 total *)
          ] THEN

          IMP_REWRITE_TAC[ARITH_RULE `0x50 * i + 0x30 = (0x50 * i + 0x20) + 0x10`; READ_BYTES_AND_BYTE128_SPLIT] THEN
          EXISTS_TAC `(aes256_xts_encrypt pt_in (0x50 * val (num_5blocks:int64) + 0x30) iv key1_lst key2_lst)` THEN
          REPEAT CONJ_TAC THENL [
            MP_TAC (SPECL [`0x5 * val (num_5blocks:int64) + 0x3:num`;
              `pt_in:byte list`; `iv:int128`; `key1_lst:int128 list`;
              `key2_lst:int128 list`] LENGTH_OF_AES256_XTS_ENCRYPT_FULL_BLOCKS) THEN
            REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_ASSOC; GSYM ADD_ASSOC] THEN
            CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
            IMP_REWRITE_TAC[SUB_LIST_LENGTH_IMPLIES];

            REWRITE_TAC [ARITH_RULE `(0x50 * i + 0x20) + 0x10 = 0x50 * i + 0x30`] THEN
            MP_TAC (SPECL [`0x5 * val (num_5blocks:int64) + 0x3:num`;
              `pt_in:byte list`; `iv:int128`; `key1_lst:int128 list`;
              `key2_lst:int128 list`] LENGTH_OF_AES256_XTS_ENCRYPT_FULL_BLOCKS) THEN
            REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_ASSOC; GSYM ADD_ASSOC] THEN
            CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
            IMP_REWRITE_TAC[SUB_LIST_LENGTH_IMPLIES] THEN ARITH_TAC;

            (* Establish that one xts encrypt round is the same as
               selecting one block of bytes from calling the top-level function. *)
            REWRITE_TAC[aes256_xts_encrypt] THEN
            SIMP_TAC[ARITH_RULE `~(0x50 * i + 0x30 < 0x10)`] THEN
            SUBGOAL_THEN `(0x50 * val (num_5blocks:int64) + 0x30) MOD 0x10 = 0` SUBST1_TAC THENL
            [ REWRITE_TAC[ARITH_RULE `80 * i + 48 = 16 * (5 * i + 3)`] THEN
              REWRITE_TAC[MOD_MULT]
            ; ALL_TAC] THEN
            CONV_TAC (DEPTH_CONV let_CONV) THEN
            REWRITE_TAC[SUB_0; ARITH_RULE `(0x50 * i + 0x30) DIV 0x10 = 0x5 * i + 0x3`] THEN
            SIMP_TAC[ARITH_RULE `~(0x5 * i + 0x3 < 0x2)`;
                     ARITH_RULE `(0x5 * i + 0x3) - 0x2 = 0x5 * i + 0x1`;
                     ARITH_RULE `(0x5 * i + 0x3) - 0x1 = 0x5 * i + 0x2`] THEN

            MP_TAC (SPECL [`0`;`5 * val (num_5blocks:int64) + 1:num`; `pt_in:byte list`; `iv:int128`;
                          `key1_lst:int128 list`; `key2_lst:int128 list`]
                    LENGTH_OF_AES256_XTS_ENCRYPT_REC) THEN
            SIMP_TAC[ARITH_RULE `~(5 * i + 1 < 0)`] THEN
            REWRITE_TAC[ARITH_RULE `((0x5 * i + 0x1) - 0x0 + 0x1) * 0x10 = 0x50 * i + 0x20`] THEN
            IMP_REWRITE_TAC[SUB_LIST_APPEND_RIGHT_LEMMA] THEN DISCH_TAC THEN

            MP_TAC (SPECL [`5 * val (num_5blocks:int64) + 2:num`; `0x0:num`; `pt_in:byte list`; `iv:int128`;
                          `key1_lst:int128 list`; `key2_lst:int128 list`]
                    LENGTH_OF_AES256_XTS_ENCRYPT_TAIL) THEN
            CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[ADD_0] THEN DISCH_TAC THEN
            IMP_REWRITE_TAC[SUB_LIST_LENGTH_IMPLIES] THEN

            REWRITE_TAC[AES256_XTS_ENCRYPT_TAIL_WHEN_1BLOCK] THEN
            ASM_SIMP_TAC[ARITH_RULE `(i * 0x5 + 0x2) * 0x10 = i * 0x50 + 0x20`;
                         ARITH_RULE `5 * i + 2 = i * 5 + 2`];

            (* Proving that reading previous bytes is the same as the spec *)
            REWRITE_TAC[ARITH_RULE `0x50 * i + 0x20 = 0x10 * (5 * i + 2)`;
                        ARITH_RULE `0x50 * i + 0x30 = 0x10 * (5 * i + 2) + 0x10`] THEN
            REWRITE_TAC[SUB_LIST_OF_AES256_XTS_ENCRYPT_FULL_BLOCKS] THEN
            ASM_REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_ASSOC] THEN CONV_TAC NUM_REDUCE_CONV
          ] THEN

          REWRITE_TAC[ARITH_RULE `0x50 * i + 0x20 = (0x50 * i + 0x10) + 0x10`] THEN
          (* Use SPECL to force IMP_REWRITE_TAC to apply once once *)
          IMP_REWRITE_TAC[(SPECL [`ctxt_p:int64`; `(0x50 * val (num_5blocks:int64) + 0x10):num`;
            `x:byte list`; `s138:armstate`] READ_BYTES_AND_BYTE128_SPLIT)] THEN
          EXISTS_TAC `(aes256_xts_encrypt pt_in (0x50 * val (num_5blocks:int64) + 0x20) iv key1_lst key2_lst)` THEN
          REPEAT CONJ_TAC THENL [
            MP_TAC (SPECL [`0x5 * val (num_5blocks:int64) + 0x2:num`;
              `pt_in:byte list`; `iv:int128`; `key1_lst:int128 list`;
              `key2_lst:int128 list`] LENGTH_OF_AES256_XTS_ENCRYPT_FULL_BLOCKS) THEN
            REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_ASSOC; GSYM ADD_ASSOC] THEN
            CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
            IMP_REWRITE_TAC[SUB_LIST_LENGTH_IMPLIES] THEN ARITH_TAC;

            MP_TAC (SPECL [`0x5 * val (num_5blocks:int64) + 0x2:num`;
              `pt_in:byte list`; `iv:int128`; `key1_lst:int128 list`;
              `key2_lst:int128 list`] LENGTH_OF_AES256_XTS_ENCRYPT_FULL_BLOCKS) THEN
            REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_ASSOC; GSYM ADD_ASSOC] THEN
            CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
            IMP_REWRITE_TAC[SUB_LIST_LENGTH_IMPLIES] THEN ARITH_TAC;

            (* Establish that one xts encrypt round is the same as
               selecting one block of bytes from calling the top-level function. *)
            REWRITE_TAC[aes256_xts_encrypt] THEN
            SIMP_TAC[ARITH_RULE `~(0x50 * i + 0x20 < 0x10)`] THEN
            SUBGOAL_THEN `(0x50 * val (num_5blocks:int64) + 0x20) MOD 0x10 = 0` SUBST1_TAC THENL
            [ REWRITE_TAC[ARITH_RULE `80 * i + 32 = 16 * (5 * i + 2)`] THEN
              REWRITE_TAC[MOD_MULT]
            ; ALL_TAC] THEN
            CONV_TAC (DEPTH_CONV let_CONV) THEN
            REWRITE_TAC[SUB_0; ARITH_RULE `(0x50 * i + 0x20) DIV 0x10 = 0x5 * i + 0x2`] THEN
            SIMP_TAC[ARITH_RULE `~(0x5 * i + 0x2 < 0x2)`;
                     ARITH_RULE `(0x5 * i + 0x2) - 0x2 = 0x5 * i`;
                     ARITH_RULE `(0x5 * i + 0x2) - 0x1 = 0x5 * i + 0x1`] THEN

            MP_TAC (SPECL [`0`;`5 * val (num_5blocks:int64):num`;
              `pt_in:byte list`; `iv:int128`; `key1_lst:int128 list`; `key2_lst:int128 list`]
              LENGTH_OF_AES256_XTS_ENCRYPT_REC) THEN
            SIMP_TAC[ARITH_RULE `~(5 * i < 0)`;
                     ARITH_RULE `(0x5 * i - 0x0 + 0x1) * 0x10 = 0x50 * i + 0x10`] THEN
            IMP_REWRITE_TAC[SUB_LIST_APPEND_RIGHT_LEMMA] THEN DISCH_TAC THEN

            MP_TAC (SPECL [`5 * val (num_5blocks:int64) + 1:num`; `0x0:num`;
              `pt_in:byte list`; `iv:int128`; `key1_lst:int128 list`; `key2_lst:int128 list`]
              LENGTH_OF_AES256_XTS_ENCRYPT_TAIL) THEN
            CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[ADD_0] THEN DISCH_TAC THEN
            IMP_REWRITE_TAC[SUB_LIST_LENGTH_IMPLIES] THEN

            REWRITE_TAC[AES256_XTS_ENCRYPT_TAIL_WHEN_1BLOCK] THEN
            SIMP_TAC[ARITH_RULE `i * 0x50 + 0x10 = (i * 0x5 + 0x1) * 0x10`;
                     ARITH_RULE `i * 0x5 = 0x5 * i`];

            (* Proving that reading previous bytes is the same as the spec *)
            REWRITE_TAC[ARITH_RULE `0x50 * i + 0x10 = 0x10 * (5 * i + 1)`;
                        ARITH_RULE `0x50 * i + 0x20 = 0x10 * (5 * i + 1) + 0x10`] THEN
            REWRITE_TAC[SUB_LIST_OF_AES256_XTS_ENCRYPT_FULL_BLOCKS] THEN
            ASM_REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_ASSOC] THEN CONV_TAC NUM_REDUCE_CONV
          ] THEN

          IMP_REWRITE_TAC[(SPECL [`ctxt_p:int64`; `(0x50 * val (num_5blocks:int64)):num`;
            `(aes256_xts_encrypt pt_in (0x50 * val (num_5blocks:int64) + 0x10) iv key1_lst key2_lst):byte list`;
            `s138:armstate`]   READ_BYTES_AND_BYTE128_SPLIT)] THEN
          EXISTS_TAC `iv:int128` THEN EXISTS_TAC `key1_lst:int128 list` THEN
          EXISTS_TAC `key2_lst:int128 list` THEN EXISTS_TAC `pt_in:byte list` THEN
          REPEAT CONJ_TAC THENL [
            MP_TAC (SPECL [`0x5 * val (num_5blocks:int64) + 0x1:num`;
              `pt_in:byte list`; `iv:int128`; `key1_lst:int128 list`;
              `key2_lst:int128 list`] LENGTH_OF_AES256_XTS_ENCRYPT_FULL_BLOCKS) THEN
            REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_ASSOC; GSYM ADD_ASSOC] THEN
            CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
            IMP_REWRITE_TAC[SUB_LIST_LENGTH_IMPLIES] THEN ARITH_TAC;

            MP_TAC (SPECL [`0x5 * val (num_5blocks:int64) + 0x1:num`;
              `pt_in:byte list`; `iv:int128`; `key1_lst:int128 list`;
              `key2_lst:int128 list`] LENGTH_OF_AES256_XTS_ENCRYPT_FULL_BLOCKS) THEN
            REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_ASSOC; GSYM ADD_ASSOC] THEN
            CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
            IMP_REWRITE_TAC[SUB_LIST_LENGTH_IMPLIES] THEN ARITH_TAC;

            (* Establish that one xts encrypt round is the same as
               selecting one block of bytes from calling the top-level function. *)
            REWRITE_TAC[aes256_xts_encrypt] THEN
            SIMP_TAC[ARITH_RULE `~(0x50 * i + 0x10 < 0x10)`] THEN
            SUBGOAL_THEN `(0x50 * val (num_5blocks:int64) + 0x10) MOD 0x10 = 0` SUBST1_TAC THENL
            [ REWRITE_TAC[ARITH_RULE `80 * i + 16 = 16 * (5 * i + 1)`] THEN
              REWRITE_TAC[MOD_MULT]
            ; ALL_TAC] THEN
            CONV_TAC (DEPTH_CONV let_CONV) THEN
            REWRITE_TAC[SUB_0; ARITH_RULE `(0x50 * i + 0x10) DIV 0x10 = 0x5 * i + 0x1`] THEN
            (* Two cases: i = 0 then execute tail branch, else execute recursion branch *)
            COND_CASES_TAC THENL
            [ SUBGOAL_THEN `val (num_5blocks:int64) = 0` SUBST1_TAC THENL
              [ UNDISCH_TAC `5 * val (num_5blocks:int64) + 1 < 2` THEN
                UNDISCH_TAC `0 < val (num_5blocks:int64)` THEN
                ARITH_TAC
              ; ALL_TAC] THEN CONV_TAC NUM_REDUCE_CONV THEN

              MP_TAC (SPECL [`0x0:num`; `0x0:num`; `pt_in:byte list`; `iv:int128`; `key1_lst:int128 list`; `key2_lst:int128 list`]
                LENGTH_OF_AES256_XTS_ENCRYPT_TAIL) THEN
              CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[ADD_0] THEN DISCH_TAC THEN
              IMP_REWRITE_TAC[(ISPECL [`(aes256_xts_encrypt_tail 0x0 0x0 pt_in iv key1_lst key2_lst):byte list`;
                `0x10:num`] SUB_LIST_LENGTH_IMPLIES)] THEN

              REWRITE_TAC[AES256_XTS_ENCRYPT_TAIL_WHEN_1BLOCK] THEN
              CONV_TAC NUM_REDUCE_CONV;

              SIMP_TAC[ARITH_RULE `(0x5 * i + 0x1) - 0x2 = 0x5 * i - 0x1`;
                       ARITH_RULE `(0x5 * i + 0x1) - 0x1 = 0x5 * i`] THEN

              MP_TAC (SPECL [`0`;`5 * val (num_5blocks:int64) - 1:num`;
                `pt_in:byte list`; `iv:int128`; `key1_lst:int128 list`; `key2_lst:int128 list`]
                LENGTH_OF_AES256_XTS_ENCRYPT_REC) THEN
              SUBGOAL_THEN `~(0x5 * val (num_5blocks:int64) - 0x1 < 0x0)` ASSUME_TAC THENL
              [ UNDISCH_TAC `~(0x5 * val (num_5blocks:int64) + 0x1 < 0x2)` THEN ARITH_TAC; ALL_TAC ] THEN
              ASM_SIMP_TAC[] THEN
              IMP_REWRITE_TAC[ARITH_RULE `~(0x5 * i + 0x1 < 0x2) ==> (0x5 * i - 1 - 0x0 + 0x1) * 0x10 = 0x50 * i`] THEN
              IMP_REWRITE_TAC[SUB_LIST_APPEND_RIGHT_LEMMA] THEN DISCH_TAC THEN

              MP_TAC (SPECL [`5 * val (num_5blocks:int64):num`;
                `0x0:num`; `pt_in:byte list`; `iv:int128`; `key1_lst:int128 list`; `key2_lst:int128 list`]
                LENGTH_OF_AES256_XTS_ENCRYPT_TAIL) THEN
              CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[ADD_0] THEN DISCH_TAC THEN
              IMP_REWRITE_TAC[SUB_LIST_LENGTH_IMPLIES] THEN

              REWRITE_TAC[AES256_XTS_ENCRYPT_TAIL_WHEN_1BLOCK] THEN
              SIMP_TAC[ARITH_RULE `i * 0x50 = (i * 0x5) * 0x10`;
                       ARITH_RULE `i * 0x5 = 0x5 * i`]
            ];

          (* Proving that reading previous bytes is the same as the spec *)
          REWRITE_TAC[ARITH_RULE `i * 0x50 = 0x50 * i`;
                      ARITH_RULE `0x50 * i = 0x10 * 5 * i`;
                      ARITH_RULE `0x50 * i + 0x10 = 0x10 * 5 * i + 0x10`] THEN
          REWRITE_TAC[SUB_LIST_OF_AES256_XTS_ENCRYPT_FULL_BLOCKS] THEN
          IMP_REWRITE_TAC[SUB_LIST_LENGTH_IMPLIES] THEN
          REWRITE_TAC[LENGTH_OF_AES256_XTS_ENCRYPT_FULL_BLOCKS]
          ]
        ] ; ALL_TAC
      ] THEN (* 2 total *)

      DISCH_TAC THEN
      ARM_ACCSTEPS_TAC AES256_XTS_ENCRYPT_EXEC [] (4--5) THEN
      FIRST_X_ASSUM MP_TAC THEN
      COND_CASES_TAC THENL
      [ (* Case: len % 0x50 = 0x30 *)
        DISCH_TAC THEN
        SUBGOAL_THEN `val (num_5blocks:int64) * 0x50 + 0x30 = val (len_full_blocks:int64)` ASSUME_TAC THENL
        [ UNDISCH_TAC `val (word_sub
            (word_sub (len_full_blocks:int64)
                     (word_mul (word 0x50) (num_5blocks:int64)))
            (word 0x30)) =
            0x0` THEN
          REWRITE_TAC [VAL_EQ_0; WORD_SUB_EQ_0] THEN
          REWRITE_TAC [WORD_RULE `!x:int64. word_mul (word 0x50) x = word(val x * 0x50)`] THEN
          REWRITE_TAC[GSYM VAL_EQ] THEN
          SUBGOAL_THEN `val (num_5blocks:int64) * 0x50 < 2 EXP 64` MP_TAC THENL
          [ UNDISCH_TAC `val (num_5blocks:int64) * 0x50 <= val (len_full_blocks:int64)` THEN
            UNDISCH_TAC `val (len_full_blocks:int64) <= 2 EXP 24` THEN
            ARITH_TAC; ALL_TAC] THEN
          REWRITE_TAC[VAL_WORD_SUB_CASES] THEN
          SIMP_TAC[VAL_WORD; DIMINDEX_64; MOD_LT] THEN
          UNDISCH_TAC `val (num_5blocks:int64) * 0x50 <= val (len_full_blocks:int64)` THEN
          NUM_REDUCE_TAC THEN ARITH_TAC; ALL_TAC] THEN

        SUBGOAL_THEN `~(val (num_5blocks:int64) * 0x50 + 0x40 = val (len_full_blocks:int64))` ASSUME_TAC THENL
        [ UNDISCH_TAC `val (num_5blocks:int64) * 0x50 + 0x30 = val (len_full_blocks:int64)` THEN
          ARITH_TAC; ALL_TAC] THEN
        SUBGOAL_THEN `val (num_5blocks:int64) * 0x50 + 0x30 <= val (len:int64)` ASSUME_TAC THENL
        [ UNDISCH_TAC `val (num_5blocks:int64) * 0x50 + 0x30 = val (len_full_blocks:int64)` THEN
          UNDISCH_TAC `val (len_full_blocks:int64) <= val (len:int64)` THEN
          ARITH_TAC; ALL_TAC] THEN
        MP_TAC (SPECL [`ptxt_p:int64`; `num_5blocks:int64`; `len:int64`; `pt_in:byte list`; `s5:armstate`]
                      READ_TAIL3_LEMMA) THEN
        ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN

        ARM_ACCSTEPS_TAC AES256_XTS_ENCRYPT_EXEC [] (6--97) THEN
        XTSENC_TAC `Q0:(armstate,int128)component`
          `val (num_5blocks:int64) * 0x50` `val (num_5blocks:int64) * 0x5` THEN
        XTSENC_TAC `Q1:(armstate,int128)component`
          `val (num_5blocks:int64) * 0x50 + 0x10` `val (num_5blocks:int64) * 0x5 + 0x1` THEN
        XTSENC_TAC `Q24:(armstate,int128)component`
          `val (num_5blocks:int64) * 0x50 + 0x20` `val (num_5blocks:int64) * 0x5 + 0x2` THEN

        (* The following lemmas are for NONSELFMODIFYING_STATE_UPDATE_TAC when store back to ctxt_p *)
        RULE_ASSUM_TAC(REWRITE_RULE
          [WORD_RULE `word_mul (word 0x50) num_5blocks:int64 = word(0x50 * val num_5blocks)`]) THEN

        ARM_ACCSTEPS_TAC AES256_XTS_ENCRYPT_EXEC [] (98--108) THEN
        TWEAK_TAC `Q6:(armstate,int128)component` `val (num_5blocks:int64) * 0x5 + 0x3` `val (num_5blocks:int64) * 0x5 + 0x2` THEN

        ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
        REPEAT CONJ_TAC THENL
        [
          REWRITE_TAC[acc_len] THEN ASM_SIMP_TAC[] THEN CONV_TAC WORD_RULE;
          REWRITE_TAC[acc_len] THEN ASM_SIMP_TAC[] THEN CONV_TAC WORD_RULE;

          REWRITE_TAC[acc_blocks] THEN ASM_SIMP_TAC[] THEN CONV_TAC WORD_RULE; (* 3 total *)

          REWRITE_TAC[acc_len] THEN ASM_SIMP_TAC[LE_REFL] THEN
          SUBGOAL_THEN `val ((word (0x50 * val (num_5blocks:int64) + 0x30)):int64) =
            0x50 * val num_5blocks + 0x30` ASSUME_TAC THENL
          [ IMP_REWRITE_TAC[VAL_WORD; MOD_LT; DIMINDEX_64] THEN
            UNDISCH_TAC `val (num_5blocks:int64) * 0x50 + 0x30 <= val (len:int64)` THEN
            UNDISCH_TAC `val (len:int64) <= 0x2 EXP 0x18` THEN
            ARITH_TAC; ALL_TAC] THEN
          POP_ASSUM(fun th -> REWRITE_TAC[th]) THEN

          (* Remove quantifier *)
          UNDISCH_TAC
          `forall i.
            i < 0x50 * val (num_5blocks:int64)
            ==> read (memory :> bytes8 (word_add ctxt_p (word i))) s108 =
                EL i (aes256_xts_encrypt pt_in (val num_5blocks * 0x50) iv key1_lst key2_lst)` THEN
          MP_TAC (SPECL [`0x50 * val (num_5blocks:int64) + 0x30:num`; `ctxt_p:int64`;
                         `(aes256_xts_encrypt pt_in (0x50 * val (num_5blocks:int64) + 0x30) iv key1_lst key2_lst):byte list`;
                         `s108:armstate`] BYTE_LIST_TO_NUM_THM) THEN
          ANTS_TAC THENL[
            REWRITE_TAC[ARITH_RULE `0x50 * i + 0x30 = 0x10 * (5 * i + 3)`;
                        LENGTH_OF_AES256_XTS_ENCRYPT_FULL_BLOCKS] THEN
            ARITH_TAC
            ; ALL_TAC] THEN
          DISCH_THEN (fun th -> REWRITE_TAC[th]) THEN

          MP_TAC (SPECL [`0x50 * val (num_5blocks:int64):num`; `ctxt_p:int64`;
                         `(aes256_xts_encrypt pt_in (val (num_5blocks:int64) * 0x50) iv key1_lst key2_lst):byte list`;
                         `s108:armstate`] BYTE_LIST_TO_NUM_THM) THEN
          ANTS_TAC THENL[
            REWRITE_TAC[ARITH_RULE `i * 0x50 = 0x10 * 5 * i`;
                        LENGTH_OF_AES256_XTS_ENCRYPT_FULL_BLOCKS] THEN
            ARITH_TAC
            ; ALL_TAC] THEN
          DISCH_THEN (fun th -> REWRITE_TAC[th]) THEN
          DISCH_TAC THEN

          IMP_REWRITE_TAC[ARITH_RULE `0x50 * i + 0x30 = (0x50 * i + 0x20) + 0x10`; READ_BYTES_AND_BYTE128_SPLIT] THEN
          EXISTS_TAC `(aes256_xts_encrypt pt_in (0x50 * val (num_5blocks:int64) + 0x30) iv key1_lst key2_lst)` THEN
          REPEAT CONJ_TAC THENL [
            REWRITE_TAC [ARITH_RULE `(0x50 * i + 0x20) + 0x10 = 0x50 * i + 0x30`];

            MP_TAC (SPECL [`0x5 * val (num_5blocks:int64) + 0x3:num`;
              `pt_in:byte list`; `iv:int128`; `key1_lst:int128 list`;
              `key2_lst:int128 list`] LENGTH_OF_AES256_XTS_ENCRYPT_FULL_BLOCKS) THEN
            REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_ASSOC; GSYM ADD_ASSOC] THEN
            CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
            ASM_REWRITE_TAC[] THEN ARITH_TAC; (* 4 total *)
            (* IMP_REWRITE_TAC[SUB_LIST_LENGTH_IMPLIES]; *)
            (*
            REWRITE_TAC [ARITH_RULE `(0x50 * i + 0x20) + 0x10 = 0x50 * i + 0x30`] THEN
            MP_TAC (SPECL [`0x5 * val (num_5blocks:int64) + 0x3:num`;
              `pt_in:byte list`; `iv:int128`; `key1_lst:int128 list`;
              `key2_lst:int128 list`] LENGTH_OF_AES256_XTS_ENCRYPT_FULL_BLOCKS) THEN
            REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_ASSOC; GSYM ADD_ASSOC] THEN
            CONV_TAC NUM_REDUCE_CONV; (* THEN DISCH_TAC THEN
            IMP_REWRITE_TAC[SUB_LIST_LENGTH_IMPLIES] THEN ARITH_TAC; *)
            *)

            (* Establish that one xts encrypt round is the same as
               selecting one block of bytes from calling the top-level function. *)
            REWRITE_TAC[aes256_xts_encrypt] THEN
            SIMP_TAC[ARITH_RULE `~(0x50 * i + 0x30 < 0x10)`] THEN
            SUBGOAL_THEN `(0x50 * val (num_5blocks:int64) + 0x30) MOD 0x10 = 0` SUBST1_TAC THENL
            [ REWRITE_TAC[ARITH_RULE `80 * i + 48 = 16 * (5 * i + 3)`] THEN
              REWRITE_TAC[MOD_MULT]
            ; ALL_TAC] THEN
            CONV_TAC (DEPTH_CONV let_CONV) THEN
            REWRITE_TAC[SUB_0; ARITH_RULE `(0x50 * i + 0x30) DIV 0x10 = 0x5 * i + 0x3`] THEN
            SIMP_TAC[ARITH_RULE `~(0x5 * i + 0x3 < 0x2)`;
                     ARITH_RULE `(0x5 * i + 0x3) - 0x2 = 0x5 * i + 0x1`;
                     ARITH_RULE `(0x5 * i + 0x3) - 0x1 = 0x5 * i + 0x2`] THEN

            MP_TAC (SPECL [`0`;`5 * val (num_5blocks:int64) + 1:num`;
              `pt_in:byte list`; `iv:int128`; `key1_lst:int128 list`; `key2_lst:int128 list`]
              LENGTH_OF_AES256_XTS_ENCRYPT_REC) THEN
            SIMP_TAC[ARITH_RULE `~(5 * i + 1 < 0)`] THEN
            REWRITE_TAC[ARITH_RULE `((0x5 * i + 0x1) - 0x0 + 0x1) * 0x10 = 0x50 * i + 0x20`] THEN
            IMP_REWRITE_TAC[SUB_LIST_APPEND_RIGHT_LEMMA] THEN DISCH_TAC THEN

            MP_TAC (SPECL [`5 * val (num_5blocks:int64) + 2:num`; `0x0:num`;
              `pt_in:byte list`; `iv:int128`; `key1_lst:int128 list`; `key2_lst:int128 list`]
              LENGTH_OF_AES256_XTS_ENCRYPT_TAIL) THEN
            CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[ADD_0] THEN DISCH_TAC THEN
            IMP_REWRITE_TAC[SUB_LIST_LENGTH_IMPLIES] THEN

            REWRITE_TAC[AES256_XTS_ENCRYPT_TAIL_WHEN_1BLOCK] THEN
            ASM_SIMP_TAC[ARITH_RULE `(i * 0x5 + 0x2) * 0x10 = i * 0x50 + 0x20`;
                         ARITH_RULE `5 * i + 2 = i * 5 + 2`];

            (* Proving that reading previous bytes is the same as the spec *)
            REWRITE_TAC[ARITH_RULE `0x50 * i + 0x20 = 0x10 * (5 * i + 2)`;
                        ARITH_RULE `0x50 * i + 0x30 = 0x10 * (5 * i + 2) + 0x10`] THEN
            REWRITE_TAC[SUB_LIST_OF_AES256_XTS_ENCRYPT_FULL_BLOCKS] THEN
            ASM_REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_ASSOC] THEN CONV_TAC NUM_REDUCE_CONV (* 3 total *)
          ] THEN

          REWRITE_TAC[ARITH_RULE `0x50 * i + 0x20 = (0x50 * i + 0x10) + 0x10`] THEN
          (* Use SPECL to force IMP_REWRITE_TAC to apply once once *)
          IMP_REWRITE_TAC[(SPECL [`ctxt_p:int64`; `(0x50 * val (num_5blocks:int64) + 0x10):num`;
            `x:byte list`; `s108:armstate`] READ_BYTES_AND_BYTE128_SPLIT)] THEN
          EXISTS_TAC `(aes256_xts_encrypt pt_in (0x50 * val (num_5blocks:int64) + 0x20) iv key1_lst key2_lst)` THEN
          REPEAT CONJ_TAC THENL [
            MP_TAC (SPECL [`0x5 * val (num_5blocks:int64) + 0x2:num`;
              `pt_in:byte list`; `iv:int128`; `key1_lst:int128 list`;
              `key2_lst:int128 list`] LENGTH_OF_AES256_XTS_ENCRYPT_FULL_BLOCKS) THEN
            REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_ASSOC; GSYM ADD_ASSOC] THEN
            CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
            IMP_REWRITE_TAC[SUB_LIST_LENGTH_IMPLIES] THEN ARITH_TAC;

            MP_TAC (SPECL [`0x5 * val (num_5blocks:int64) + 0x2:num`;
              `pt_in:byte list`; `iv:int128`; `key1_lst:int128 list`;
              `key2_lst:int128 list`] LENGTH_OF_AES256_XTS_ENCRYPT_FULL_BLOCKS) THEN
            REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_ASSOC; GSYM ADD_ASSOC] THEN
            CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
            IMP_REWRITE_TAC[SUB_LIST_LENGTH_IMPLIES] THEN ARITH_TAC;

            (* Establish that one xts encrypt round is the same as
               selecting one block of bytes from calling the top-level function. *)
            REWRITE_TAC[aes256_xts_encrypt] THEN
            SIMP_TAC[ARITH_RULE `~(0x50 * i + 0x20 < 0x10)`] THEN
            SUBGOAL_THEN `(0x50 * val (num_5blocks:int64) + 0x20) MOD 0x10 = 0` SUBST1_TAC THENL
            [ REWRITE_TAC[ARITH_RULE `80 * i + 32 = 16 * (5 * i + 2)`] THEN
              REWRITE_TAC[MOD_MULT]
            ; ALL_TAC] THEN
            CONV_TAC (DEPTH_CONV let_CONV) THEN
            REWRITE_TAC[SUB_0; ARITH_RULE `(0x50 * i + 0x20) DIV 0x10 = 0x5 * i + 0x2`] THEN
            SIMP_TAC[ARITH_RULE `~(0x5 * i + 0x2 < 0x2)`;
                     ARITH_RULE `(0x5 * i + 0x2) - 0x2 = 0x5 * i`;
                     ARITH_RULE `(0x5 * i + 0x2) - 0x1 = 0x5 * i + 0x1`] THEN

            MP_TAC (SPECL [`0`;`5 * val (num_5blocks:int64):num`;
              `pt_in:byte list`; `iv:int128`; `key1_lst:int128 list`; `key2_lst:int128 list`]
              LENGTH_OF_AES256_XTS_ENCRYPT_REC) THEN
            SIMP_TAC[ARITH_RULE `~(5 * i < 0)`;
                     ARITH_RULE `(0x5 * i - 0x0 + 0x1) * 0x10 = 0x50 * i + 0x10`] THEN
            IMP_REWRITE_TAC[SUB_LIST_APPEND_RIGHT_LEMMA] THEN DISCH_TAC THEN

            MP_TAC (SPECL [`5 * val (num_5blocks:int64) + 1:num`; `0x0:num`;
              `pt_in:byte list`; `iv:int128`; `key1_lst:int128 list`; `key2_lst:int128 list`]
              LENGTH_OF_AES256_XTS_ENCRYPT_TAIL) THEN
            CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[ADD_0] THEN DISCH_TAC THEN
            IMP_REWRITE_TAC[SUB_LIST_LENGTH_IMPLIES] THEN

            REWRITE_TAC[AES256_XTS_ENCRYPT_TAIL_WHEN_1BLOCK] THEN
            SIMP_TAC[ARITH_RULE `i * 0x50 + 0x10 = (i * 0x5 + 0x1) * 0x10`;
                     ARITH_RULE `i * 0x5 = 0x5 * i`];

            (* Proving that reading previous bytes is the same as the spec *)
            REWRITE_TAC[ARITH_RULE `0x50 * i + 0x10 = 0x10 * (5 * i + 1)`;
                        ARITH_RULE `0x50 * i + 0x20 = 0x10 * (5 * i + 1) + 0x10`] THEN
            REWRITE_TAC[SUB_LIST_OF_AES256_XTS_ENCRYPT_FULL_BLOCKS] THEN
            ASM_REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_ASSOC] THEN CONV_TAC NUM_REDUCE_CONV
          ] THEN

          IMP_REWRITE_TAC[(SPECL [`ctxt_p:int64`; `(0x50 * val (num_5blocks:int64)):num`;
            `(aes256_xts_encrypt pt_in (0x50 * val (num_5blocks:int64) + 0x10) iv key1_lst key2_lst):byte list`;
            `s108:armstate`]   READ_BYTES_AND_BYTE128_SPLIT)] THEN
          EXISTS_TAC `iv:int128` THEN EXISTS_TAC `key1_lst:int128 list` THEN
          EXISTS_TAC `key2_lst:int128 list` THEN EXISTS_TAC `pt_in:byte list` THEN
          REPEAT CONJ_TAC THENL [
            MP_TAC (SPECL [`0x5 * val (num_5blocks:int64) + 0x1:num`;
              `pt_in:byte list`; `iv:int128`; `key1_lst:int128 list`;
              `key2_lst:int128 list`] LENGTH_OF_AES256_XTS_ENCRYPT_FULL_BLOCKS) THEN
            REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_ASSOC; GSYM ADD_ASSOC] THEN
            CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
            IMP_REWRITE_TAC[SUB_LIST_LENGTH_IMPLIES] THEN ARITH_TAC;

            MP_TAC (SPECL [`0x5 * val (num_5blocks:int64) + 0x1:num`;
              `pt_in:byte list`; `iv:int128`; `key1_lst:int128 list`;
              `key2_lst:int128 list`] LENGTH_OF_AES256_XTS_ENCRYPT_FULL_BLOCKS) THEN
            REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_ASSOC; GSYM ADD_ASSOC] THEN
            CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
            IMP_REWRITE_TAC[SUB_LIST_LENGTH_IMPLIES] THEN ARITH_TAC;

            (* Establish that one xts encrypt round is the same as
               selecting one block of bytes from calling the top-level function. *)
            REWRITE_TAC[aes256_xts_encrypt] THEN
            SIMP_TAC[ARITH_RULE `~(0x50 * i + 0x10 < 0x10)`] THEN
            SUBGOAL_THEN `(0x50 * val (num_5blocks:int64) + 0x10) MOD 0x10 = 0` SUBST1_TAC THENL
            [ REWRITE_TAC[ARITH_RULE `80 * i + 16 = 16 * (5 * i + 1)`] THEN
              REWRITE_TAC[MOD_MULT]
            ; ALL_TAC] THEN
            CONV_TAC (DEPTH_CONV let_CONV) THEN
            REWRITE_TAC[SUB_0; ARITH_RULE `(0x50 * i + 0x10) DIV 0x10 = 0x5 * i + 0x1`] THEN
            (* Two cases: i = 0 then execute tail branch, else execute recursion branch *)
            COND_CASES_TAC THENL
            [ SUBGOAL_THEN `val (num_5blocks:int64) = 0` SUBST1_TAC THENL
              [ UNDISCH_TAC `5 * val (num_5blocks:int64) + 1 < 2` THEN
                UNDISCH_TAC `0 < val (num_5blocks:int64)` THEN
                ARITH_TAC
              ; ALL_TAC] THEN CONV_TAC NUM_REDUCE_CONV THEN

              MP_TAC (SPECL [`0x0:num`; `0x0:num`; `pt_in:byte list`; `iv:int128`; `key1_lst:int128 list`; `key2_lst:int128 list`]
                LENGTH_OF_AES256_XTS_ENCRYPT_TAIL) THEN
              CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[ADD_0] THEN DISCH_TAC THEN
              IMP_REWRITE_TAC[(ISPECL [`(aes256_xts_encrypt_tail 0x0 0x0 pt_in iv key1_lst key2_lst):byte list`;
                `0x10:num`] SUB_LIST_LENGTH_IMPLIES)] THEN

              REWRITE_TAC[AES256_XTS_ENCRYPT_TAIL_WHEN_1BLOCK] THEN
              CONV_TAC NUM_REDUCE_CONV;

              SIMP_TAC[ARITH_RULE `(0x5 * i + 0x1) - 0x2 = 0x5 * i - 0x1`;
                       ARITH_RULE `(0x5 * i + 0x1) - 0x1 = 0x5 * i`] THEN

              MP_TAC (SPECL [`0`;`5 * val (num_5blocks:int64) - 1:num`;
                `pt_in:byte list`; `iv:int128`; `key1_lst:int128 list`; `key2_lst:int128 list`]
                LENGTH_OF_AES256_XTS_ENCRYPT_REC) THEN
              SUBGOAL_THEN `~(0x5 * val (num_5blocks:int64) - 0x1 < 0x0)` ASSUME_TAC THENL
              [ UNDISCH_TAC `~(0x5 * val (num_5blocks:int64) + 0x1 < 0x2)` THEN ARITH_TAC; ALL_TAC ] THEN
              ASM_SIMP_TAC[] THEN
              IMP_REWRITE_TAC[ARITH_RULE `~(0x5 * i + 0x1 < 0x2) ==> (0x5 * i - 1 - 0x0 + 0x1) * 0x10 = 0x50 * i`] THEN
              IMP_REWRITE_TAC[SUB_LIST_APPEND_RIGHT_LEMMA] THEN DISCH_TAC THEN

              MP_TAC (SPECL [`5 * val (num_5blocks:int64):num`;
                `0x0:num`; `pt_in:byte list`; `iv:int128`; `key1_lst:int128 list`; `key2_lst:int128 list`]
                LENGTH_OF_AES256_XTS_ENCRYPT_TAIL) THEN
              CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[ADD_0] THEN DISCH_TAC THEN
              IMP_REWRITE_TAC[SUB_LIST_LENGTH_IMPLIES] THEN

              REWRITE_TAC[AES256_XTS_ENCRYPT_TAIL_WHEN_1BLOCK] THEN
              SIMP_TAC[ARITH_RULE `i * 0x50 = (i * 0x5) * 0x10`;
                       ARITH_RULE `i * 0x5 = 0x5 * i`]
            ];

            (* Proving that reading previous bytes is the same as the spec *)
            REWRITE_TAC[ARITH_RULE `i * 0x50 = 0x50 * i`;
                        ARITH_RULE `0x50 * i = 0x10 * 5 * i`;
                        ARITH_RULE `0x50 * i + 0x10 = 0x10 * 5 * i + 0x10`] THEN
            REWRITE_TAC[SUB_LIST_OF_AES256_XTS_ENCRYPT_FULL_BLOCKS] THEN
            IMP_REWRITE_TAC[SUB_LIST_LENGTH_IMPLIES] THEN
            REWRITE_TAC[LENGTH_OF_AES256_XTS_ENCRYPT_FULL_BLOCKS]
          ]
        ] ; ALL_TAC (* 2 total *)
      ] THEN

      DISCH_TAC THEN
      ARM_ACCSTEPS_TAC AES256_XTS_ENCRYPT_EXEC [] (6--7) THEN
      FIRST_X_ASSUM MP_TAC THEN
      COND_CASES_TAC THENL
      [ (* Case: len % 0x50 = 0x20 *)
        DISCH_TAC THEN
        SUBGOAL_THEN `val (num_5blocks:int64) * 0x50 + 0x20 = val (len_full_blocks:int64)` ASSUME_TAC THENL
        [ UNDISCH_TAC `val (word_sub
            (word_sub (len_full_blocks:int64)
                     (word_mul (word 0x50) (num_5blocks:int64)))
            (word 0x20)) =
            0x0` THEN
          REWRITE_TAC [VAL_EQ_0; WORD_SUB_EQ_0] THEN
          REWRITE_TAC [WORD_RULE `!x:int64. word_mul (word 0x50) x = word(val x * 0x50)`] THEN
          REWRITE_TAC[GSYM VAL_EQ] THEN
          SUBGOAL_THEN `val (num_5blocks:int64) * 0x50 < 2 EXP 64` MP_TAC THENL
          [ UNDISCH_TAC `val (num_5blocks:int64) * 0x50 <= val (len_full_blocks:int64)` THEN
            UNDISCH_TAC `val (len_full_blocks:int64) <= 2 EXP 24` THEN
            ARITH_TAC; ALL_TAC] THEN
          REWRITE_TAC[VAL_WORD_SUB_CASES] THEN
          SIMP_TAC[VAL_WORD; DIMINDEX_64; MOD_LT] THEN
          UNDISCH_TAC `val (num_5blocks:int64) * 0x50 <= val (len_full_blocks:int64)` THEN
          NUM_REDUCE_TAC THEN ARITH_TAC; ALL_TAC] THEN

        SUBGOAL_THEN `~(val (num_5blocks:int64) * 0x50 + 0x40 = val (len_full_blocks:int64))` ASSUME_TAC THENL
        [ UNDISCH_TAC `val (num_5blocks:int64) * 0x50 + 0x20 = val (len_full_blocks:int64)` THEN
          ARITH_TAC; ALL_TAC] THEN
        SUBGOAL_THEN `~(val (num_5blocks:int64) * 0x50 + 0x30 = val (len_full_blocks:int64))` ASSUME_TAC THENL
        [ UNDISCH_TAC `val (num_5blocks:int64) * 0x50 + 0x20 = val (len_full_blocks:int64)` THEN
          ARITH_TAC; ALL_TAC] THEN

        SUBGOAL_THEN `val (num_5blocks:int64) * 0x50 + 0x20 <= val (len:int64)` ASSUME_TAC THENL
        [ UNDISCH_TAC `val (num_5blocks:int64) * 0x50 + 0x20 = val (len_full_blocks:int64)` THEN
          UNDISCH_TAC `val (len_full_blocks:int64) <= val (len:int64)` THEN
          ARITH_TAC; ALL_TAC] THEN
        MP_TAC (SPECL [`ptxt_p:int64`; `num_5blocks:int64`; `len:int64`; `pt_in:byte list`; `s7:armstate`]
                      READ_TAIL2_LEMMA) THEN
        ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN

        ARM_ACCSTEPS_TAC AES256_XTS_ENCRYPT_EXEC [] (8--68) THEN
        XTSENC_TAC `Q0:(armstate,int128)component`
          `val (num_5blocks:int64) * 0x50` `val (num_5blocks:int64) * 0x5` THEN
        XTSENC_TAC `Q1:(armstate,int128)component`
          `val (num_5blocks:int64) * 0x50 + 0x10` `val (num_5blocks:int64) * 0x5 + 0x1` THEN

        (* The following lemmas are for NONSELFMODIFYING_STATE_UPDATE_TAC when store back to ctxt_p *)
        RULE_ASSUM_TAC(REWRITE_RULE
          [WORD_RULE `word_mul (word 0x50) num_5blocks:int64 = word(0x50 * val num_5blocks)`]) THEN

        ARM_ACCSTEPS_TAC AES256_XTS_ENCRYPT_EXEC [] (69--78) THEN
        TWEAK_TAC `Q6:(armstate,int128)component` `val (num_5blocks:int64) * 0x5 + 0x2` `val (num_5blocks:int64) * 0x5 + 0x1` THEN

        ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
        REPEAT CONJ_TAC THENL
        [
          REWRITE_TAC[acc_len] THEN ASM_SIMP_TAC[] THEN CONV_TAC WORD_RULE;
          REWRITE_TAC[acc_len] THEN ASM_SIMP_TAC[] THEN CONV_TAC WORD_RULE;
          REWRITE_TAC[acc_blocks] THEN ASM_SIMP_TAC[] THEN CONV_TAC WORD_RULE; (* 3 total *)

          REWRITE_TAC[acc_len] THEN ASM_SIMP_TAC[LE_REFL] THEN
          SUBGOAL_THEN `val ((word (0x50 * val (num_5blocks:int64) + 0x20)):int64) =
            0x50 * val num_5blocks + 0x20` ASSUME_TAC THENL
          [ IMP_REWRITE_TAC[VAL_WORD; MOD_LT; DIMINDEX_64] THEN
            UNDISCH_TAC `val (num_5blocks:int64) * 0x50 + 0x20 <= val (len:int64)` THEN
            UNDISCH_TAC `val (len:int64) <= 0x2 EXP 0x18` THEN
            ARITH_TAC; ALL_TAC] THEN
          POP_ASSUM(fun th -> REWRITE_TAC[th]) THEN

          (* Remove quantifier *)
          UNDISCH_TAC
          `forall i.
            i < 0x50 * val (num_5blocks:int64)
            ==> read (memory :> bytes8 (word_add ctxt_p (word i))) s78 =
                EL i (aes256_xts_encrypt pt_in (val num_5blocks * 0x50) iv key1_lst key2_lst)` THEN
          MP_TAC (SPECL [`0x50 * val (num_5blocks:int64) + 0x20:num`; `ctxt_p:int64`;
                         `(aes256_xts_encrypt pt_in (0x50 * val (num_5blocks:int64) + 0x20) iv key1_lst key2_lst):byte list`;
                         `s78:armstate`] BYTE_LIST_TO_NUM_THM) THEN
          ANTS_TAC THENL[
            REWRITE_TAC[ARITH_RULE `0x50 * i + 0x20 = 0x10 * (5 * i + 2)`;
                        LENGTH_OF_AES256_XTS_ENCRYPT_FULL_BLOCKS] THEN
            ARITH_TAC
            ; ALL_TAC] THEN
          DISCH_THEN (fun th -> REWRITE_TAC[th]) THEN

          MP_TAC (SPECL [`0x50 * val (num_5blocks:int64):num`; `ctxt_p:int64`;
                         `(aes256_xts_encrypt pt_in (val (num_5blocks:int64) * 0x50) iv key1_lst key2_lst):byte list`;
                         `s78:armstate`] BYTE_LIST_TO_NUM_THM) THEN
          ANTS_TAC THENL[
            REWRITE_TAC[ARITH_RULE `0x50 * i = i * 0x50`;
                        ARITH_RULE `i * 0x50 = 0x10 * 5 * i`;
                        LENGTH_OF_AES256_XTS_ENCRYPT_FULL_BLOCKS] THEN
            ARITH_TAC
            ; ALL_TAC] THEN
          DISCH_THEN (fun th -> REWRITE_TAC[th]) THEN
          DISCH_TAC THEN

          REWRITE_TAC[ARITH_RULE `0x50 * i + 0x20 = (0x50 * i + 0x10) + 0x10`] THEN
          (* Use SPECL to force IMP_REWRITE_TAC to apply once once *)
          IMP_REWRITE_TAC[(SPECL [`ctxt_p:int64`; `(0x50 * val (num_5blocks:int64) + 0x10):num`;
            `x:byte list`; `s78:armstate`] READ_BYTES_AND_BYTE128_SPLIT)] THEN
          EXISTS_TAC `(aes256_xts_encrypt pt_in (0x50 * val (num_5blocks:int64) + 0x20) iv key1_lst key2_lst)` THEN
          REPEAT CONJ_TAC THENL [
            REWRITE_TAC [ARITH_RULE `(0x50 * i + 0x10) + 0x10 = 0x50 * i + 0x20`];

            MP_TAC (SPECL [`0x5 * val (num_5blocks:int64) + 0x2:num`;
              `pt_in:byte list`; `iv:int128`; `key1_lst:int128 list`;
              `key2_lst:int128 list`] LENGTH_OF_AES256_XTS_ENCRYPT_FULL_BLOCKS) THEN
            REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_ASSOC; GSYM ADD_ASSOC] THEN
            CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
            IMP_REWRITE_TAC[SUB_LIST_LENGTH_IMPLIES] THEN ARITH_TAC;

            (* Establish that one xts encrypt round is the same as
               selecting one block of bytes from calling the top-level function. *)
            REWRITE_TAC[aes256_xts_encrypt] THEN
            SIMP_TAC[ARITH_RULE `~(0x50 * i + 0x20 < 0x10)`] THEN
            SUBGOAL_THEN `(0x50 * val (num_5blocks:int64) + 0x20) MOD 0x10 = 0` SUBST1_TAC THENL
            [ REWRITE_TAC[ARITH_RULE `80 * i + 32 = 16 * (5 * i + 2)`] THEN
              REWRITE_TAC[MOD_MULT]
            ; ALL_TAC] THEN
            CONV_TAC (DEPTH_CONV let_CONV) THEN
            REWRITE_TAC[SUB_0; ARITH_RULE `(0x50 * i + 0x20) DIV 0x10 = 0x5 * i + 0x2`] THEN
            SIMP_TAC[ARITH_RULE `~(0x5 * i + 0x2 < 0x2)`;
                     ARITH_RULE `(0x5 * i + 0x2) - 0x2 = 0x5 * i`;
                     ARITH_RULE `(0x5 * i + 0x2) - 0x1 = 0x5 * i + 0x1`] THEN

            MP_TAC (SPECL [`0`;`5 * val (num_5blocks:int64):num`;
              `pt_in:byte list`; `iv:int128`; `key1_lst:int128 list`; `key2_lst:int128 list`]
              LENGTH_OF_AES256_XTS_ENCRYPT_REC) THEN
            SIMP_TAC[ARITH_RULE `~(5 * i < 0)`;
                     ARITH_RULE `(0x5 * i - 0x0 + 0x1) * 0x10 = 0x50 * i + 0x10`] THEN
            IMP_REWRITE_TAC[SUB_LIST_APPEND_RIGHT_LEMMA] THEN DISCH_TAC THEN

            MP_TAC (SPECL [`5 * val (num_5blocks:int64) + 1:num`; `0x0:num`;
              `pt_in:byte list`; `iv:int128`; `key1_lst:int128 list`; `key2_lst:int128 list`]
              LENGTH_OF_AES256_XTS_ENCRYPT_TAIL) THEN
            CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[ADD_0] THEN DISCH_TAC THEN
            IMP_REWRITE_TAC[SUB_LIST_LENGTH_IMPLIES] THEN

            REWRITE_TAC[AES256_XTS_ENCRYPT_TAIL_WHEN_1BLOCK] THEN
            SIMP_TAC[ARITH_RULE `i * 0x50 + 0x10 = (i * 0x5 + 0x1) * 0x10`;
                     ARITH_RULE `i * 0x5 = 0x5 * i`];

            (* Proving that reading previous bytes is the same as the spec *)
            REWRITE_TAC[ARITH_RULE `0x50 * i + 0x10 = 0x10 * (5 * i + 1)`;
                        ARITH_RULE `0x50 * i + 0x20 = 0x10 * (5 * i + 1) + 0x10`] THEN
            REWRITE_TAC[SUB_LIST_OF_AES256_XTS_ENCRYPT_FULL_BLOCKS] THEN
            ASM_REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_ASSOC] THEN CONV_TAC NUM_REDUCE_CONV
          ] THEN

          IMP_REWRITE_TAC[(SPECL [`ctxt_p:int64`; `(0x50 * val (num_5blocks:int64)):num`;
            `(aes256_xts_encrypt pt_in (0x50 * val (num_5blocks:int64) + 0x10) iv key1_lst key2_lst):byte list`;
            `s78:armstate`]   READ_BYTES_AND_BYTE128_SPLIT)] THEN
          EXISTS_TAC `iv:int128` THEN EXISTS_TAC `key1_lst:int128 list` THEN
          EXISTS_TAC `key2_lst:int128 list` THEN EXISTS_TAC `pt_in:byte list` THEN
          REPEAT CONJ_TAC THENL [
            MP_TAC (SPECL [`0x5 * val (num_5blocks:int64) + 0x1:num`;
              `pt_in:byte list`; `iv:int128`; `key1_lst:int128 list`;
              `key2_lst:int128 list`] LENGTH_OF_AES256_XTS_ENCRYPT_FULL_BLOCKS) THEN
            REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_ASSOC; GSYM ADD_ASSOC] THEN
            CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
            IMP_REWRITE_TAC[SUB_LIST_LENGTH_IMPLIES] THEN ARITH_TAC;

            MP_TAC (SPECL [`0x5 * val (num_5blocks:int64) + 0x1:num`;
              `pt_in:byte list`; `iv:int128`; `key1_lst:int128 list`;
              `key2_lst:int128 list`] LENGTH_OF_AES256_XTS_ENCRYPT_FULL_BLOCKS) THEN
            REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_ASSOC; GSYM ADD_ASSOC] THEN
            CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
            IMP_REWRITE_TAC[SUB_LIST_LENGTH_IMPLIES] THEN ARITH_TAC;

            (* Establish that one xts encrypt round is the same as
               selecting one block of bytes from calling the top-level function. *)
            REWRITE_TAC[aes256_xts_encrypt] THEN
            SIMP_TAC[ARITH_RULE `~(0x50 * i + 0x10 < 0x10)`] THEN
            SUBGOAL_THEN `(0x50 * val (num_5blocks:int64) + 0x10) MOD 0x10 = 0` SUBST1_TAC THENL
            [ REWRITE_TAC[ARITH_RULE `80 * i + 16 = 16 * (5 * i + 1)`] THEN
              REWRITE_TAC[MOD_MULT]
            ; ALL_TAC] THEN
            CONV_TAC (DEPTH_CONV let_CONV) THEN
            REWRITE_TAC[SUB_0; ARITH_RULE `(0x50 * i + 0x10) DIV 0x10 = 0x5 * i + 0x1`] THEN
            (* Two cases: i = 0 then execute tail branch, else execute recursion branch *)
            COND_CASES_TAC THENL
            [ SUBGOAL_THEN `val (num_5blocks:int64) = 0` SUBST1_TAC THENL
              [ UNDISCH_TAC `5 * val (num_5blocks:int64) + 1 < 2` THEN
                UNDISCH_TAC `0 < val (num_5blocks:int64)` THEN
                ARITH_TAC
              ; ALL_TAC] THEN CONV_TAC NUM_REDUCE_CONV THEN

              MP_TAC (SPECL [`0x0:num`; `0x0:num`; `pt_in:byte list`; `iv:int128`; `key1_lst:int128 list`; `key2_lst:int128 list`]
                LENGTH_OF_AES256_XTS_ENCRYPT_TAIL) THEN
              CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[ADD_0] THEN DISCH_TAC THEN
              IMP_REWRITE_TAC[(ISPECL [`(aes256_xts_encrypt_tail 0x0 0x0 pt_in iv key1_lst key2_lst):byte list`;
                `0x10:num`] SUB_LIST_LENGTH_IMPLIES)] THEN

              REWRITE_TAC[AES256_XTS_ENCRYPT_TAIL_WHEN_1BLOCK] THEN
              CONV_TAC NUM_REDUCE_CONV;

              SIMP_TAC[ARITH_RULE `(0x5 * i + 0x1) - 0x2 = 0x5 * i - 0x1`;
                       ARITH_RULE `(0x5 * i + 0x1) - 0x1 = 0x5 * i`] THEN

              MP_TAC (SPECL [`0`;`5 * val (num_5blocks:int64) - 1:num`;
                `pt_in:byte list`; `iv:int128`; `key1_lst:int128 list`; `key2_lst:int128 list`]
                LENGTH_OF_AES256_XTS_ENCRYPT_REC) THEN
              SUBGOAL_THEN `~(0x5 * val (num_5blocks:int64) - 0x1 < 0x0)` ASSUME_TAC THENL
              [ UNDISCH_TAC `~(0x5 * val (num_5blocks:int64) + 0x1 < 0x2)` THEN ARITH_TAC; ALL_TAC ] THEN
              ASM_SIMP_TAC[] THEN
              IMP_REWRITE_TAC[ARITH_RULE `~(0x5 * i + 0x1 < 0x2) ==> (0x5 * i - 1 - 0x0 + 0x1) * 0x10 = 0x50 * i`] THEN
              IMP_REWRITE_TAC[SUB_LIST_APPEND_RIGHT_LEMMA] THEN DISCH_TAC THEN

              MP_TAC (SPECL [`5 * val (num_5blocks:int64):num`;
                `0x0:num`; `pt_in:byte list`; `iv:int128`; `key1_lst:int128 list`; `key2_lst:int128 list`]
                LENGTH_OF_AES256_XTS_ENCRYPT_TAIL) THEN
              CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[ADD_0] THEN DISCH_TAC THEN
              IMP_REWRITE_TAC[SUB_LIST_LENGTH_IMPLIES] THEN

              REWRITE_TAC[AES256_XTS_ENCRYPT_TAIL_WHEN_1BLOCK] THEN
              SIMP_TAC[ARITH_RULE `i * 0x50 = (i * 0x5) * 0x10`;
                       ARITH_RULE `i * 0x5 = 0x5 * i`]
            ];

            (* Proving that reading previous bytes is the same as the spec *)
            REWRITE_TAC[ARITH_RULE `i * 0x50 = 0x50 * i`;
                        ARITH_RULE `0x50 * i = 0x10 * 5 * i`;
                        ARITH_RULE `0x50 * i + 0x10 = 0x10 * 5 * i + 0x10`] THEN
            REWRITE_TAC[SUB_LIST_OF_AES256_XTS_ENCRYPT_FULL_BLOCKS] THEN
            IMP_REWRITE_TAC[SUB_LIST_LENGTH_IMPLIES] THEN
            REWRITE_TAC[LENGTH_OF_AES256_XTS_ENCRYPT_FULL_BLOCKS]
          ]
        ] ; ALL_TAC (* 2 total *)
      ] THEN

      DISCH_TAC THEN
      ARM_ACCSTEPS_TAC AES256_XTS_ENCRYPT_EXEC [] (8--9) THEN
      FIRST_X_ASSUM MP_TAC THEN
      COND_CASES_TAC THENL (*?? *)
      [ (* Case: len % 0x50 = 0x10 *)
        DISCH_TAC THEN

        SUBGOAL_THEN `val (num_5blocks:int64) * 0x50 + 0x10 = val (len_full_blocks:int64)` ASSUME_TAC THENL
        [ UNDISCH_TAC `val (word_sub
            (word_sub (len_full_blocks:int64)
                     (word_mul (word 0x50) (num_5blocks:int64)))
            (word 0x10)) =
            0x0` THEN
          REWRITE_TAC [VAL_EQ_0; WORD_SUB_EQ_0] THEN
          REWRITE_TAC [WORD_RULE `!x:int64. word_mul (word 0x50) x = word(val x * 0x50)`] THEN
          REWRITE_TAC[GSYM VAL_EQ] THEN
          SUBGOAL_THEN `val (num_5blocks:int64) * 0x50 < 2 EXP 64` MP_TAC THENL
          [ UNDISCH_TAC `val (num_5blocks:int64) * 0x50 <= val (len_full_blocks:int64)` THEN
            UNDISCH_TAC `val (len_full_blocks:int64) <= 2 EXP 24` THEN
            ARITH_TAC; ALL_TAC] THEN
          REWRITE_TAC[VAL_WORD_SUB_CASES] THEN
          SIMP_TAC[VAL_WORD; DIMINDEX_64; MOD_LT] THEN
          UNDISCH_TAC `val (num_5blocks:int64) * 0x50 <= val (len_full_blocks:int64)` THEN
          NUM_REDUCE_TAC THEN ARITH_TAC; ALL_TAC] THEN

        SUBGOAL_THEN `~(val (num_5blocks:int64) * 0x50 + 0x40 = val (len_full_blocks:int64))` ASSUME_TAC THENL
        [ UNDISCH_TAC `val (num_5blocks:int64) * 0x50 + 0x10 = val (len_full_blocks:int64)` THEN
          ARITH_TAC; ALL_TAC] THEN
        SUBGOAL_THEN `~(val (num_5blocks:int64) * 0x50 + 0x30 = val (len_full_blocks:int64))` ASSUME_TAC THENL
        [ UNDISCH_TAC `val (num_5blocks:int64) * 0x50 + 0x10 = val (len_full_blocks:int64)` THEN
          ARITH_TAC; ALL_TAC] THEN
        SUBGOAL_THEN `~(val (num_5blocks:int64) * 0x50 + 0x20 = val (len_full_blocks:int64))` ASSUME_TAC THENL
        [ UNDISCH_TAC `val (num_5blocks:int64) * 0x50 + 0x10 = val (len_full_blocks:int64)` THEN
          ARITH_TAC; ALL_TAC] THEN

        SUBGOAL_THEN `val (num_5blocks:int64) * 0x50 + 0x10 <= val (len:int64)` ASSUME_TAC THENL
        [ UNDISCH_TAC `val (num_5blocks:int64) * 0x50 + 0x10 = val (len_full_blocks:int64)` THEN
          UNDISCH_TAC `val (len_full_blocks:int64) <= val (len:int64)` THEN
          ARITH_TAC; ALL_TAC] THEN
        MP_TAC (SPECL [`ptxt_p:int64`; `num_5blocks:int64`; `len:int64`; `pt_in:byte list`; `s9:armstate`]
                      READ_TAIL1_LEMMA) THEN
        ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN

        ARM_ACCSTEPS_TAC AES256_XTS_ENCRYPT_EXEC [] (10--40) THEN
        XTSENC_TAC `Q0:(armstate,int128)component`
          `val (num_5blocks:int64) * 0x50` `val (num_5blocks:int64) * 0x5` THEN

        (* The following lemmas are for NONSELFMODIFYING_STATE_UPDATE_TAC when store back to ctxt_p *)
        RULE_ASSUM_TAC(REWRITE_RULE
          [WORD_RULE `word_mul (word 0x50) num_5blocks:int64 = word(0x50 * val num_5blocks)`]) THEN

        ARM_ACCSTEPS_TAC AES256_XTS_ENCRYPT_EXEC [] (41--50) THEN
        TWEAK_TAC `Q6:(armstate,int128)component` `val (num_5blocks:int64) * 0x5 + 0x1` `val (num_5blocks:int64) * 0x5` THEN

        ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
        REPEAT CONJ_TAC THENL
        [
          REWRITE_TAC[acc_len] THEN ASM_SIMP_TAC[] THEN CONV_TAC WORD_RULE;
          REWRITE_TAC[acc_len] THEN ASM_SIMP_TAC[] THEN CONV_TAC WORD_RULE;
          REWRITE_TAC[acc_blocks] THEN ASM_SIMP_TAC[] THEN CONV_TAC WORD_RULE; (* 3 total *)

          REWRITE_TAC[acc_len] THEN ASM_SIMP_TAC[LE_REFL] THEN
          SUBGOAL_THEN `val ((word (0x50 * val (num_5blocks:int64) + 0x10)):int64) =
            0x50 * val num_5blocks + 0x10` ASSUME_TAC THENL
          [ IMP_REWRITE_TAC[VAL_WORD; MOD_LT; DIMINDEX_64] THEN
            UNDISCH_TAC `val (num_5blocks:int64) * 0x50 + 0x10 <= val (len:int64)` THEN
            UNDISCH_TAC `val (len:int64) <= 0x2 EXP 0x18` THEN
            ARITH_TAC; ALL_TAC] THEN
          POP_ASSUM(fun th -> REWRITE_TAC[th]) THEN

          (* Remove quantifier *)
          UNDISCH_TAC
          `forall i.
            i < 0x50 * val (num_5blocks:int64)
            ==> read (memory :> bytes8 (word_add ctxt_p (word i))) s50 =
                EL i (aes256_xts_encrypt pt_in (val num_5blocks * 0x50) iv key1_lst key2_lst)` THEN
          MP_TAC (SPECL [`0x50 * val (num_5blocks:int64) + 0x10:num`; `ctxt_p:int64`;
                         `(aes256_xts_encrypt pt_in (0x50 * val (num_5blocks:int64) + 0x10) iv key1_lst key2_lst):byte list`;
                         `s50:armstate`] BYTE_LIST_TO_NUM_THM) THEN
          ANTS_TAC THENL[
            REWRITE_TAC[ARITH_RULE `0x50 * i + 0x10 = 0x10 * (5 * i + 1)`;
                        LENGTH_OF_AES256_XTS_ENCRYPT_FULL_BLOCKS] THEN
            ARITH_TAC
            ; ALL_TAC] THEN
          DISCH_THEN (fun th -> REWRITE_TAC[th]) THEN

          MP_TAC (SPECL [`0x50 * val (num_5blocks:int64):num`; `ctxt_p:int64`;
                         `(aes256_xts_encrypt pt_in (val (num_5blocks:int64) * 0x50) iv key1_lst key2_lst):byte list`;
                         `s50:armstate`] BYTE_LIST_TO_NUM_THM) THEN
          ANTS_TAC THENL[
            REWRITE_TAC[ARITH_RULE `0x50 * i = i * 0x50`;
                        ARITH_RULE `i * 0x50 = 0x10 * 5 * i`;
                        LENGTH_OF_AES256_XTS_ENCRYPT_FULL_BLOCKS] THEN
            ARITH_TAC
            ; ALL_TAC] THEN
          DISCH_THEN (fun th -> REWRITE_TAC[th]) THEN
          DISCH_TAC THEN

          IMP_REWRITE_TAC[(SPECL [`ctxt_p:int64`; `(0x50 * val (num_5blocks:int64)):num`;
            `(aes256_xts_encrypt pt_in (0x50 * val (num_5blocks:int64) + 0x10) iv key1_lst key2_lst):byte list`;
            `s50:armstate`]   READ_BYTES_AND_BYTE128_SPLIT)] THEN
          EXISTS_TAC `iv:int128` THEN EXISTS_TAC `key1_lst:int128 list` THEN
          EXISTS_TAC `key2_lst:int128 list` THEN EXISTS_TAC `pt_in:byte list` THEN
          REPEAT CONJ_TAC THENL [
            REFL_TAC;

            MP_TAC (SPECL [`0x5 * val (num_5blocks:int64) + 0x1:num`;
              `pt_in:byte list`; `iv:int128`; `key1_lst:int128 list`;
              `key2_lst:int128 list`] LENGTH_OF_AES256_XTS_ENCRYPT_FULL_BLOCKS) THEN
            REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_ASSOC; GSYM ADD_ASSOC] THEN
            CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC;

            (* Establish that one xts encrypt round is the same as
               selecting one block of bytes from calling the top-level function. *)
            REWRITE_TAC[aes256_xts_encrypt] THEN
            SIMP_TAC[ARITH_RULE `~(0x50 * i + 0x10 < 0x10)`] THEN
            SUBGOAL_THEN `(0x50 * val (num_5blocks:int64) + 0x10) MOD 0x10 = 0` SUBST1_TAC THENL
            [ REWRITE_TAC[ARITH_RULE `80 * i + 16 = 16 * (5 * i + 1)`] THEN
              REWRITE_TAC[MOD_MULT]
            ; ALL_TAC] THEN
            CONV_TAC (DEPTH_CONV let_CONV) THEN
            REWRITE_TAC[SUB_0; ARITH_RULE `(0x50 * i + 0x10) DIV 0x10 = 0x5 * i + 0x1`] THEN
            (* Two cases: i = 0 then execute tail branch, else execute recursion branch *)
            COND_CASES_TAC THENL
            [ SUBGOAL_THEN `val (num_5blocks:int64) = 0` SUBST1_TAC THENL
              [ UNDISCH_TAC `5 * val (num_5blocks:int64) + 1 < 2` THEN
                UNDISCH_TAC `0 < val (num_5blocks:int64)` THEN
                ARITH_TAC
              ; ALL_TAC] THEN CONV_TAC NUM_REDUCE_CONV THEN

              MP_TAC (SPECL [`0x0:num`; `0x0:num`; `pt_in:byte list`; `iv:int128`; `key1_lst:int128 list`; `key2_lst:int128 list`]
                LENGTH_OF_AES256_XTS_ENCRYPT_TAIL) THEN
              CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[ADD_0] THEN DISCH_TAC THEN
              IMP_REWRITE_TAC[(ISPECL [`(aes256_xts_encrypt_tail 0x0 0x0 pt_in iv key1_lst key2_lst):byte list`;
                `0x10:num`] SUB_LIST_LENGTH_IMPLIES)] THEN

              REWRITE_TAC[AES256_XTS_ENCRYPT_TAIL_WHEN_1BLOCK] THEN
              CONV_TAC NUM_REDUCE_CONV;

              SIMP_TAC[ARITH_RULE `(0x5 * i + 0x1) - 0x2 = 0x5 * i - 0x1`;
                       ARITH_RULE `(0x5 * i + 0x1) - 0x1 = 0x5 * i`] THEN

              MP_TAC (SPECL [`0`;`5 * val (num_5blocks:int64) - 1:num`;
                `pt_in:byte list`; `iv:int128`; `key1_lst:int128 list`; `key2_lst:int128 list`]
                LENGTH_OF_AES256_XTS_ENCRYPT_REC) THEN
              SUBGOAL_THEN `~(0x5 * val (num_5blocks:int64) - 0x1 < 0x0)` ASSUME_TAC THENL
              [ UNDISCH_TAC `~(0x5 * val (num_5blocks:int64) + 0x1 < 0x2)` THEN ARITH_TAC; ALL_TAC ] THEN
              ASM_SIMP_TAC[] THEN
              IMP_REWRITE_TAC[ARITH_RULE `~(0x5 * i + 0x1 < 0x2) ==> (0x5 * i - 1 - 0x0 + 0x1) * 0x10 = 0x50 * i`] THEN
              IMP_REWRITE_TAC[SUB_LIST_APPEND_RIGHT_LEMMA] THEN DISCH_TAC THEN

              MP_TAC (SPECL [`5 * val (num_5blocks:int64):num`;
                `0x0:num`; `pt_in:byte list`; `iv:int128`; `key1_lst:int128 list`; `key2_lst:int128 list`]
                LENGTH_OF_AES256_XTS_ENCRYPT_TAIL) THEN
              CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[ADD_0] THEN DISCH_TAC THEN
              IMP_REWRITE_TAC[SUB_LIST_LENGTH_IMPLIES] THEN

              REWRITE_TAC[AES256_XTS_ENCRYPT_TAIL_WHEN_1BLOCK] THEN
              SIMP_TAC[ARITH_RULE `i * 0x50 = (i * 0x5) * 0x10`;
                       ARITH_RULE `i * 0x5 = 0x5 * i`]
            ];

            (* Proving that reading previous bytes is the same as the spec *)
            REWRITE_TAC[ARITH_RULE `i * 0x50 = 0x50 * i`;
                        ARITH_RULE `0x50 * i = 0x10 * 5 * i`;
                        ARITH_RULE `0x50 * i + 0x10 = 0x10 * 5 * i + 0x10`] THEN
            REWRITE_TAC[SUB_LIST_OF_AES256_XTS_ENCRYPT_FULL_BLOCKS] THEN
            IMP_REWRITE_TAC[SUB_LIST_LENGTH_IMPLIES] THEN
            REWRITE_TAC[LENGTH_OF_AES256_XTS_ENCRYPT_FULL_BLOCKS]
          ]
        ] ; ALL_TAC (* 2 total *)
      ] THEN

      (* Case: len % 0x50 = 0 *)
      DISCH_TAC THEN
      SUBGOAL_THEN `val (num_5blocks:int64) * 0x50 = val (len_full_blocks:int64)` ASSUME_TAC THENL
      [ MATCH_MP_TAC (SPECL [`val (len_full_blocks:int64)`; `val (num_5blocks:int64)`]
                            DIVISION_BY_80_LEMMA) THEN
        REPEAT CONJ_TAC THENL
        [
          EXPAND_TAC "num_5blocks" THEN
          IMP_REWRITE_TAC[VAL_WORD; DIMINDEX_64; MOD_LT] THEN
          UNDISCH_TAC `val (len_full_blocks:int64) <= 0x2 EXP 0x18` THEN
          ARITH_TAC;

          EXPAND_TAC "len_full_blocks" THEN
          REWRITE_TAC[NUM_BLOCKS_TO_VAL] THEN
          IMP_REWRITE_TAC[VAL_WORD; DIMINDEX_64; MOD_LT; DIVIDES_RMUL; DIVIDES_REFL] THEN
          UNDISCH_TAC `val (len:int64) <= 0x2 EXP 0x18` THEN
          ARITH_TAC;

          UNDISCH_TAC `~(val (word_sub
            (word_sub (len_full_blocks:int64)
              (word_mul (word 0x50) (num_5blocks:int64)))
            (word 0x10)) = 0x0)` THEN
          REWRITE_TAC[CONTRAPOS_THM] THEN
          REWRITE_TAC[VAL_WORD_SUB_EQ_0; VAL_WORD_MUL; VAL_WORD; DIMINDEX_64;
            ARITH_RULE `0x10 MOD 0x2 EXP 0x40 = 0x10`] THEN
          REWRITE_TAC[VAL_WORD_SUB; VAL_WORD_MUL; VAL_WORD; DIMINDEX_64;
            ARITH_RULE `0x50 MOD 0x2 EXP 0x40 = 0x50`] THEN

          SUBGOAL_THEN `0x50 * val (num_5blocks:int64) < 2 EXP 64` ASSUME_TAC THENL
          [ UNDISCH_TAC `val (num_5blocks:int64) * 0x50 <= val  (len_full_blocks:int64)` THEN
            UNDISCH_TAC `val (len_full_blocks:int64) <= 2 EXP 24` THEN
            ARITH_TAC; ALL_TAC] THEN
          MP_TAC (SPECL [`0x50 * val (num_5blocks:int64)`; `2 EXP 64`] MOD_LT) THEN
          ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
          SIMP_TAC[] THEN DISCH_TAC THEN

          MP_TAC (SPECL [`val (len_full_blocks:int64)`; `0x2 EXP 0x40`;
            `0x50 * val (num_5blocks:int64)`]
            (ARITH_RULE `!a b c. c <= a ==> c <= b ==> a + b - c = (a - c) + b`)) THEN
          ANTS_TAC THENL [
            UNDISCH_TAC `val (num_5blocks:int64) * 0x50 <= val (len_full_blocks:int64)` THEN
            SIMP_TAC[MULT_SYM]; ALL_TAC] THEN
          ANTS_TAC THENL [
            UNDISCH_TAC `0x50 * val (num_5blocks:int64) < 2 EXP 64` THEN
            ARITH_TAC; ALL_TAC] THEN
          ASM_SIMP_TAC[] THEN DISCH_TAC THEN

          MP_TAC (SPECL [`1`; `0x2 EXP 0x40`;
            `val (len_full_blocks:int64) - 0x50 * val (num_5blocks:int64)`]
            (CONJUNCT1 (CONJUNCT2 (CONJUNCT2 MOD_MULT_ADD)))) THEN
          REWRITE_TAC[ARITH_RULE `1 * 2 EXP 64 = 2 EXP 64`] THEN
          SIMP_TAC[] THEN DISCH_TAC THEN
          SIMP_TAC[MULT_SYM] THEN DISCH_TAC THEN
          CONV_TAC NUM_REDUCE_CONV;

          UNDISCH_TAC `~(val (word_sub
            (word_sub (len_full_blocks:int64)
              (word_mul (word 0x50) (num_5blocks:int64)))
            (word 0x20)) = 0x0)` THEN
          REWRITE_TAC[CONTRAPOS_THM] THEN
          REWRITE_TAC[VAL_WORD_SUB_EQ_0; VAL_WORD_MUL; VAL_WORD; DIMINDEX_64;
            ARITH_RULE `0x10 MOD 0x2 EXP 0x40 = 0x10`] THEN
          REWRITE_TAC[VAL_WORD_SUB; VAL_WORD_MUL; VAL_WORD; DIMINDEX_64;
            ARITH_RULE `0x50 MOD 0x2 EXP 0x40 = 0x50`] THEN

          SUBGOAL_THEN `0x50 * val (num_5blocks:int64) < 2 EXP 64` ASSUME_TAC THENL
          [ UNDISCH_TAC `val (num_5blocks:int64) * 0x50 <= val  (len_full_blocks:int64)` THEN
            UNDISCH_TAC `val (len_full_blocks:int64) <= 2 EXP 24` THEN
            ARITH_TAC; ALL_TAC] THEN
          MP_TAC (SPECL [`0x50 * val (num_5blocks:int64)`; `2 EXP 64`] MOD_LT) THEN
          ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
          SIMP_TAC[] THEN DISCH_TAC THEN

          MP_TAC (SPECL [`val (len_full_blocks:int64)`; `0x2 EXP 0x40`;
            `0x50 * val (num_5blocks:int64)`]
            (ARITH_RULE `!a b c. c <= a ==> c <= b ==> a + b - c = (a - c) + b`)) THEN
          ANTS_TAC THENL [
            UNDISCH_TAC `val (num_5blocks:int64) * 0x50 <= val (len_full_blocks:int64)` THEN
            SIMP_TAC[MULT_SYM]; ALL_TAC] THEN
          ANTS_TAC THENL [
            UNDISCH_TAC `0x50 * val (num_5blocks:int64) < 2 EXP 64` THEN
            ARITH_TAC; ALL_TAC] THEN
          ASM_SIMP_TAC[] THEN DISCH_TAC THEN

          MP_TAC (SPECL [`1`; `0x2 EXP 0x40`;
            `val (len_full_blocks:int64) - 0x50 * val (num_5blocks:int64)`]
            (CONJUNCT1 (CONJUNCT2 (CONJUNCT2 MOD_MULT_ADD)))) THEN
          REWRITE_TAC[ARITH_RULE `1 * 2 EXP 64 = 2 EXP 64`] THEN
          SIMP_TAC[] THEN DISCH_TAC THEN
          SIMP_TAC[MULT_SYM] THEN DISCH_TAC THEN
          CONV_TAC NUM_REDUCE_CONV;

          UNDISCH_TAC `~(val (word_sub
            (word_sub (len_full_blocks:int64)
              (word_mul (word 0x50) (num_5blocks:int64)))
            (word 0x30)) = 0x0)` THEN
          REWRITE_TAC[CONTRAPOS_THM] THEN
          REWRITE_TAC[VAL_WORD_SUB_EQ_0; VAL_WORD_MUL; VAL_WORD; DIMINDEX_64;
            ARITH_RULE `0x10 MOD 0x2 EXP 0x40 = 0x10`] THEN
          REWRITE_TAC[VAL_WORD_SUB; VAL_WORD_MUL; VAL_WORD; DIMINDEX_64;
            ARITH_RULE `0x50 MOD 0x2 EXP 0x40 = 0x50`] THEN

          SUBGOAL_THEN `0x50 * val (num_5blocks:int64) < 2 EXP 64` ASSUME_TAC THENL
          [ UNDISCH_TAC `val (num_5blocks:int64) * 0x50 <= val  (len_full_blocks:int64)` THEN
            UNDISCH_TAC `val (len_full_blocks:int64) <= 2 EXP 24` THEN
            ARITH_TAC; ALL_TAC] THEN
          MP_TAC (SPECL [`0x50 * val (num_5blocks:int64)`; `2 EXP 64`] MOD_LT) THEN
          ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
          SIMP_TAC[] THEN DISCH_TAC THEN

          MP_TAC (SPECL [`val (len_full_blocks:int64)`; `0x2 EXP 0x40`;
            `0x50 * val (num_5blocks:int64)`]
            (ARITH_RULE `!a b c. c <= a ==> c <= b ==> a + b - c = (a - c) + b`)) THEN
          ANTS_TAC THENL [
            UNDISCH_TAC `val (num_5blocks:int64) * 0x50 <= val (len_full_blocks:int64)` THEN
            SIMP_TAC[MULT_SYM]; ALL_TAC] THEN
          ANTS_TAC THENL [
            UNDISCH_TAC `0x50 * val (num_5blocks:int64) < 2 EXP 64` THEN
            ARITH_TAC; ALL_TAC] THEN
          ASM_SIMP_TAC[] THEN DISCH_TAC THEN

          MP_TAC (SPECL [`1`; `0x2 EXP 0x40`;
            `val (len_full_blocks:int64) - 0x50 * val (num_5blocks:int64)`]
            (CONJUNCT1 (CONJUNCT2 (CONJUNCT2 MOD_MULT_ADD)))) THEN
          REWRITE_TAC[ARITH_RULE `1 * 2 EXP 64 = 2 EXP 64`] THEN
          SIMP_TAC[] THEN DISCH_TAC THEN
          SIMP_TAC[MULT_SYM] THEN DISCH_TAC THEN
          CONV_TAC NUM_REDUCE_CONV;

          UNDISCH_TAC `~(val (word_sub
            (word_sub (len_full_blocks:int64)
              (word_mul (word 0x50) (num_5blocks:int64)))
            (word 0x40)) = 0x0)` THEN
          REWRITE_TAC[CONTRAPOS_THM] THEN
          REWRITE_TAC[VAL_WORD_SUB_EQ_0; VAL_WORD_MUL; VAL_WORD; DIMINDEX_64;
            ARITH_RULE `0x10 MOD 0x2 EXP 0x40 = 0x10`] THEN
          REWRITE_TAC[VAL_WORD_SUB; VAL_WORD_MUL; VAL_WORD; DIMINDEX_64;
            ARITH_RULE `0x50 MOD 0x2 EXP 0x40 = 0x50`] THEN

          SUBGOAL_THEN `0x50 * val (num_5blocks:int64) < 2 EXP 64` ASSUME_TAC THENL
          [ UNDISCH_TAC `val (num_5blocks:int64) * 0x50 <= val  (len_full_blocks:int64)` THEN
            UNDISCH_TAC `val (len_full_blocks:int64) <= 2 EXP 24` THEN
            ARITH_TAC; ALL_TAC] THEN
          MP_TAC (SPECL [`0x50 * val (num_5blocks:int64)`; `2 EXP 64`] MOD_LT) THEN
          ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
          SIMP_TAC[] THEN DISCH_TAC THEN

          MP_TAC (SPECL [`val (len_full_blocks:int64)`; `0x2 EXP 0x40`;
            `0x50 * val (num_5blocks:int64)`]
            (ARITH_RULE `!a b c. c <= a ==> c <= b ==> a + b - c = (a - c) + b`)) THEN
          ANTS_TAC THENL [
            UNDISCH_TAC `val (num_5blocks:int64) * 0x50 <= val (len_full_blocks:int64)` THEN
            SIMP_TAC[MULT_SYM]; ALL_TAC] THEN
          ANTS_TAC THENL [
            UNDISCH_TAC `0x50 * val (num_5blocks:int64) < 2 EXP 64` THEN
            ARITH_TAC; ALL_TAC] THEN
          ASM_SIMP_TAC[] THEN DISCH_TAC THEN

          MP_TAC (SPECL [`1`; `0x2 EXP 0x40`;
            `val (len_full_blocks:int64) - 0x50 * val (num_5blocks:int64)`]
            (CONJUNCT1 (CONJUNCT2 (CONJUNCT2 MOD_MULT_ADD)))) THEN
          REWRITE_TAC[ARITH_RULE `1 * 2 EXP 64 = 2 EXP 64`] THEN
          SIMP_TAC[] THEN DISCH_TAC THEN
          SIMP_TAC[MULT_SYM] THEN DISCH_TAC THEN
          CONV_TAC NUM_REDUCE_CONV;
        ] ; ALL_TAC
      ] THEN

      SUBGOAL_THEN `~(val (num_5blocks:int64) * 0x50 + 0x40 = val (len_full_blocks:int64))` ASSUME_TAC THENL
      [ UNDISCH_TAC `val (num_5blocks:int64) * 0x50 = val (len_full_blocks:int64)` THEN
        ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `~(val (num_5blocks:int64) * 0x50 + 0x30 = val (len_full_blocks:int64))` ASSUME_TAC THENL
      [ UNDISCH_TAC `val (num_5blocks:int64) * 0x50 = val (len_full_blocks:int64)` THEN
        ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `~(val (num_5blocks:int64) * 0x50 + 0x20 = val (len_full_blocks:int64))` ASSUME_TAC THENL
      [ UNDISCH_TAC `val (num_5blocks:int64) * 0x50 = val (len_full_blocks:int64)` THEN
        ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `~(val (num_5blocks:int64) * 0x50 + 0x10 = val (len_full_blocks:int64))` ASSUME_TAC THENL
      [ UNDISCH_TAC `val (num_5blocks:int64) * 0x50 = val (len_full_blocks:int64)` THEN
        ARITH_TAC; ALL_TAC] THEN

      ARM_ACCSTEPS_TAC AES256_XTS_ENCRYPT_EXEC [] (10--10) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      REPEAT CONJ_TAC THENL [
        REWRITE_TAC[acc_len] THEN ASM_SIMP_TAC[] THEN CONV_TAC WORD_RULE;
        REWRITE_TAC[acc_len] THEN ASM_SIMP_TAC[] THEN CONV_TAC WORD_RULE;
        REWRITE_TAC[acc_blocks] THEN ASM_SIMP_TAC[] THEN CONV_TAC WORD_RULE;

        REWRITE_TAC[acc_len] THEN ASM_SIMP_TAC[] THEN

              (* Rewrite to help reasoning about nonoverlapping
         so that the universally quantified assumption stays.
         See: https://hol-light.zulipchat.com/#narrow/channel/474190-s2n-bignum/topic/.E2.9C.94.20Symbolic.20simulation.20removed.20assumption/with/541554894 *)
      SUBGOAL_THEN `val (word (0x50 * val (num_5blocks:int64)):int64) = 0x50 * val num_5blocks` MP_TAC THENL [
        IMP_REWRITE_TAC[VAL_WORD; DIMINDEX_64; MOD_LT] THEN
        UNDISCH_TAC `val (num_5blocks:int64) * 0x50 < 0x2 EXP 0x40` THEN
        ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN (fun th -> REWRITE_TAC[th]) THEN

        UNDISCH_TAC
        `forall i.
          i < 0x50 * val (num_5blocks:int64)
          ==> read (memory :> bytes8 (word_add ctxt_p (word i))) s10 =
              EL i
              (aes256_xts_encrypt pt_in (val num_5blocks * 0x50) iv key1_lst
              key2_lst)` THEN
        REWRITE_TAC[ARITH_RULE `i * 0x50 = 0x50 * i`]
      ]
    ] (* End of loop invariant proof *)
    ; ALL_TAC
  ] THEN

  (* Reuse the cipher stealing proof *)
  MP_TAC CIPHER_STEALING_ENC_CORRECT THEN
  REWRITE_TAC [(REWRITE_CONV [aes256_xts_encrypt_mc] THENC LENGTH_CONV) `LENGTH aes256_xts_encrypt_mc`] THEN
  REWRITE_TAC[byte_list_at; PAIRWISE; ALL; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  ASM_SIMP_TAC[]
);;

let AES256_XTS_ENCRYPT_SUBROUTINE_CORRECT = prove(
  `!ptxt_p ctxt_p len key1_p key2_p iv_p
    pt_in iv
    k1_0 k1_1 k1_2 k1_3 k1_4 k1_5 k1_6 k1_7 k1_8 k1_9 k1_10 k1_11 k1_12 k1_13 k1_14
    k2_0 k2_1 k2_2 k2_3 k2_4 k2_5 k2_6 k2_7 k2_8 k2_9 k2_10 k2_11 k2_12 k2_13 k2_14
    pc stackpointer returnaddress.
    aligned 16 stackpointer /\
    PAIRWISE nonoverlapping
    [(word_sub stackpointer (word 96), 96);
     (word pc, LENGTH aes256_xts_encrypt_mc);
     (ptxt_p, val len);
     (ctxt_p, val len);
     (iv_p, 16);
     (key1_p, 244);
     (key2_p, 244)] /\
    val len >= 16 /\ val len <= 2 EXP 24 /\ LENGTH pt_in = val len
  ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) aes256_xts_encrypt_mc /\
           read PC s = word pc /\
           read SP s = stackpointer /\
           read X30 s = returnaddress /\
           C_ARGUMENTS [ptxt_p; ctxt_p; len; key1_p; key2_p; iv_p] s /\
           byte_list_at pt_in ptxt_p len s /\
           read(memory :> bytes128 iv_p) s = iv /\
           set_key_schedule s key1_p k1_0 k1_1 k1_2 k1_3 k1_4 k1_5 k1_6 k1_7 k1_8 k1_9 k1_10 k1_11 k1_12 k1_13 k1_14 /\
           set_key_schedule s key2_p k2_0 k2_1 k2_2 k2_3 k2_4 k2_5 k2_6 k2_7 k2_8 k2_9 k2_10 k2_11 k2_12 k2_13 k2_14 )
      (\s. read PC s = returnaddress /\
           byte_list_at (aes256_xts_encrypt pt_in (val len) iv
                [k1_0; k1_1; k1_2; k1_3; k1_4; k1_5; k1_6; k1_7; k1_8; k1_9; k1_10; k1_11; k1_12; k1_13; k1_14]
                [k2_0; k2_1; k2_2; k2_3; k2_4; k2_5; k2_6; k2_7; k2_8; k2_9; k2_10; k2_11; k2_12; k2_13; k2_14])
                ctxt_p len s )
    (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI,,
     MAYCHANGE [memory :> bytes(ctxt_p, val len);
                memory :> bytes(word_sub stackpointer (word 96), 96)])`,
  REWRITE_TAC[byte_list_at; set_key_schedule;
    fst AES256_XTS_ENCRYPT_EXEC] THEN
  (* ~pre_post_nsteps:(7,7): 7 instructions before and after program body
      for handling stack.
    96: the byte size occupied on stack for storing preserved registers *)
  ARM_ADD_RETURN_STACK_TAC
    ~pre_post_nsteps:(7,7) AES256_XTS_ENCRYPT_EXEC
    (REWRITE_RULE[byte_list_at; set_key_schedule;
      fst AES256_XTS_ENCRYPT_EXEC] AES256_XTS_ENCRYPT_CORRECT)
   `[X19; X20; X21; X22; D8; D9; D10; D11; D12; D13; D14; D15]` 96
  );;
