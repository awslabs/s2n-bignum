(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

use_file_raise_failure := true;;
arm_print_log := true;;
components_print_log := true;;

needs "arm/proofs/base.ml";;
needs "arm/proofs/aes_encrypt_spec.ml";;
needs "arm/proofs/aes_xts_encrypt_spec.ml";;

(* print_literal_from_elf "arm/aes-xts/aes-xts-armv8.o";; *)
(* save_literal_from_elf "arm/aes-xts/aes-xts-armv8.txt" "arm/aes-xts/aes-xts-armv8.o";; *)

(* let aes_xts_armv8 = define_assert_from_elf "aes_xts_armv8" "arm/aes-xts/aes-xts-armv8.o" ..*)

(* Missing instructions that were added in PR#211
4c4070a6   10: 4c4070a6      ld1.16b { v6 }, [x5]
4cdfa87c   5c: 4cdfa87c      ld1.4s  { v28, v29 }, [x3], #32
d503201f   f8: d503201f      nop
4cc87000   198: 4cc87000      ld1.16b { v0 }, [x0], x8
4c40a870   19c: 4c40a870      ld1.4s  { v16, v17 }, [x3]
3875682f   818: 3875682f      ldrb    w15, [x1, x21]
Also LDP/STP pre-index and post-index
*)

let aes256_xts_encrypt_mc = define_assert_from_elf "aes256_xts_encrypt_mc" "arm/aes-xts/aes-xts-armv8.o"
[
  0xd10183ff;       (* arm_SUB SP SP (rvalue (word 0x60)) *)
  0x6d0227e8;       (* arm_STP D8 D9 SP (Immediate_Offset (iword (&0x20))) *)
  0x6d032fea;       (* arm_STP D10 D11 SP (Immediate_Offset (iword (&0x30))) *)
  0x6d0437ec;       (* arm_STP D12 D13 SP (Immediate_Offset (iword (&0x40))) *)
  0x6d053fee;       (* arm_STP D14 D15 SP (Immediate_Offset (iword (&0x50))) *)
  0xa90053f3;       (* arm_STP X19 X20 SP (Immediate_Offset (iword (&0x0))) *)
  0xa9015bf5;       (* arm_STP X21 X22 SP (Immediate_Offset (iword (&0x10))) *)
  0xf100405f;       (* arm_CMP X2 (rvalue (word 0x10)) *)
  0x5400520b;       (* arm_BLT (word 0xa40) *)
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
  0xf100805f;       (* arm_CMP X2 (rvalue (word 0x20)) *)
  0x54004483;       (* arm_BCC (word 0x890) *)
  0x9e6600c9;       (* arm_FMOV_FtoI X9 Q6 0x0 0x40 *)
  0x9eae00ca;       (* arm_FMOV_FtoI X10 Q6 0x1 0x40 *)
  0x528010f3;       (* arm_MOV W19 (rvalue (word 0x87)) *)
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
  0xf2400ebf;       (* arm_TST X21 (rvalue (word 0xf)) *)
  0x540003e0;       (* arm_BEQ (word 0x7c) *)
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
  0xb940f066;       (* arm_LDR W6 X3 (Immediate_Offset (word 0xf0)) *)
  0x4cdf7060;       (* arm_LDR Q0 X3 (Postimmediate_Offset (word 0x10)) *)
  0x510008c6;       (* arm_SUB W6 W6 (rvalue (word 0x2)) *)
  0x4cdf7061;       (* arm_LDR Q1 X3 (Postimmediate_Offset (word 0x10)) *)
  0x4e28481a;       (* arm_AESE Q26 Q0 *)
  0x4e286b5a;       (* arm_AESMC Q26 Q26 *)
  0x4cdf7860;       (* arm_LDR Q0 X3 (Postimmediate_Offset (word 0x10)) *)
  0x710008c6;       (* arm_SUBS W6 W6 (rvalue (word 0x2)) *)
  0x4e28483a;       (* arm_AESE Q26 Q1 *)
  0x4e286b5a;       (* arm_AESMC Q26 Q26 *)
  0x4cdf7861;       (* arm_LDR Q1 X3 (Postimmediate_Offset (word 0x10)) *)
  0x54ffff2c;       (* arm_BGT (word 0x1fffe4) *)
  0x4e28481a;       (* arm_AESE Q26 Q0 *)
  0x4e286b5a;       (* arm_AESMC Q26 Q26 *)
  0x4c407860;       (* arm_LDR Q0 X3 No_Offset *)
  0x4e28483a;       (* arm_AESE Q26 Q1 *)
  0x6e201f5a;       (* arm_EOR_VEC Q26 Q26 Q0 0x80 *)
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

(** Definitions **)

(* same as in aes_xts_decrypt.ml *)
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

(*
void aes_hw_xts_encrypt(const uint8_t *in, uint8_t *out, size_t length,
                        const AES_KEY *key1, const AES_KEY *key2,
                        const uint8_t iv[16])
*)
(* for stack pointer alignment and nonoverlapping examples, I looked at shigoel's sha512_block_data_order_hw.ml
   and bignum_invsqrt_p25519_alt.ml *)
let AES256_ENCRYPT_ONE_BLOCK_CORRECT = prove(
  `! ptxt_p ctxt_p key1_p key2_p iv_p
     pt_in iv
     (k1_0:int128) k1_1 k1_2 k1_3 k1_4 k1_5 k1_6 k1_7 k1_8 k1_9 k1_10 k1_11 k1_12 k1_13 k1_14
     k2_0 k2_1 k2_2 k2_3 k2_4 k2_5 k2_6 k2_7 k2_8 k2_9 k2_10 k2_11 k2_12 k2_13 k2_14
     pc stackpointer.
     aligned 16 stackpointer /\
           PAIRWISE nonoverlapping
           [(stackpointer, 6*16);
            (word pc, LENGTH aes256_xts_encrypt_mc);
            (ctxt_p, 16);
            (key1_p, 244);
            (key2_p, 244)]
    ==> ensures arm
      // precondition
      (\s. aligned_bytes_loaded s (word pc) aes256_xts_encrypt_mc /\
           read PC s = word (pc + 28) /\
           read SP s = stackpointer /\
           C_ARGUMENTS [ptxt_p; ctxt_p; word 16; key1_p; key2_p; iv_p] s /\
           read(memory :> bytes128 ptxt_p) s = pt_in /\
           read(memory :> bytes128 iv_p) s = iv /\
           set_key_schedule s key1_p k1_0 k1_1 k1_2 k1_3 k1_4 k1_5 k1_6 k1_7 k1_8 k1_9 k1_10 k1_11 k1_12 k1_13 k1_14 /\
           set_key_schedule s key2_p k2_0 k2_1 k2_2 k2_3 k2_4 k2_5 k2_6 k2_7 k2_8 k2_9 k2_10 k2_11 k2_12 k2_13 k2_14
      )
      // postcondition
      (\s. read PC s = word (pc + LENGTH aes256_xts_encrypt_mc - 8*4) /\
           read(memory :> bytes128 ctxt_p) s =
              aes256_xts_encrypt_1block pt_in iv
                [k1_0; k1_1; k1_2; k1_3; k1_4; k1_5; k1_6; k1_7; k1_8; k1_9; k1_10; k1_11; k1_12; k1_13; k1_14]
                [k2_0; k2_1; k2_2; k2_3; k2_4; k2_5; k2_6; k2_7; k2_8; k2_9; k2_10; k2_11; k2_12; k2_13; k2_14]
      )
      (MAYCHANGE [PC;X0;X1;X2;X4;X6;X7;X8;X9;X10;X11;X19;X20;X21;X22],,
       MAYCHANGE [Q0;Q1;Q4;Q5;Q6;Q7;Q8;Q9;Q10;Q11;Q12;Q13;Q14;Q15;Q16;Q17;Q18;Q19;Q20;Q21;Q22;Q23;Q24;Q25;Q26],,
       MAYCHANGE SOME_FLAGS,, MAYCHANGE [memory :> bytes128 ctxt_p],,
       MAYCHANGE [events])`,
  REWRITE_TAC [(REWRITE_CONV [aes256_xts_encrypt_mc] THENC LENGTH_CONV) `LENGTH aes256_xts_encrypt_mc`] THEN
  REWRITE_TAC[set_key_schedule; NONOVERLAPPING_CLAUSES; C_ARGUMENTS; SOME_FLAGS; PAIRWISE; ALL] THEN
  REPEAT STRIP_TAC THEN
  (* Start symbolic simulation *)
  ENSURES_INIT_TAC "s0" THEN

  (* Simulate until the iv encryption and verify it against AES encryption spec *)
  ARM_STEPS_TAC AES256_XTS_ENCRYPT_EXEC (1--65) THEN

(*  FIRST_X_ASSUM(MP_TAC o MATCH_MP (MESON[] `read Q6 s = a ==> !a'. a = a' ==> read Q6 s = a'`)) THEN *)
  FIRST_X_ASSUM(MP_TAC o SPEC
    `(aes256_encrypt (iv:int128) [k2_0:int128; k2_1; k2_2; k2_3; k2_4; k2_5; k2_6; k2_7; k2_8; k2_9; k2_10; k2_11; k2_12; k2_13; k2_14]):int128`
    o  MATCH_MP (MESON[] `read Q6 s = a ==> !a'. a = a' ==> read Q6 s = a'`)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN AESENC_TAC; DISCH_TAC] THEN

  (* Simulate until the one-block input encryption until before XORing the iv with the output. *)
  ARM_STEPS_TAC AES256_XTS_ENCRYPT_EXEC (66--106) THEN

(*  FIRST_X_ASSUM(MP_TAC o MATCH_MP (MESON[] `read Q0 s = a ==> !a'. a = a' ==> read Q0 s = a'`)) THEN *)
  FIRST_X_ASSUM(MP_TAC o SPEC
    `(aes256_encrypt
       (word_xor
          (aes256_encrypt
             iv
             [k2_0; k2_1; k2_2; k2_3; k2_4; k2_5; k2_6; k2_7; k2_8;
              k2_9; k2_10; k2_11; k2_12; k2_13; k2_14])
          pt_in:int128)
       [k1_0:int128; k1_1; k1_2; k1_3; k1_4; k1_5; k1_6; k1_7; k1_8; k1_9; k1_10; k1_11; k1_12; k1_13; k1_14]):int128`
    o  MATCH_MP (MESON[] `read Q0 s = a ==> !a'. a = a' ==> read Q0 s = a'`)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN AESENC_TAC; DISCH_TAC] THEN

  (* XOR the tweak with the output in Q0 *)
  ARM_STEPS_TAC AES256_XTS_ENCRYPT_EXEC (107--107) THEN

  (* Write it to the ciphertext output *)
  ARM_STEPS_TAC AES256_XTS_ENCRYPT_EXEC (108--108) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC
    `(aes256_xts_encrypt_1block
        (pt_in:int128)
        (iv:int128)
        [k1_0:int128; k1_1; k1_2; k1_3; k1_4; k1_5; k1_6; k1_7; k1_8; k1_9; k1_10;
         k1_11; k1_12; k1_13; k1_14]
        [k2_0:int128; k2_1; k2_2; k2_3; k2_4; k2_5; k2_6; k2_7; k2_8; k2_9; k2_10;
         k2_11; k2_12; k2_13; k2_14]):int128`
      o MATCH_MP (MESON[] `read (memory :> bytes128 ctxt_p) s = a ==> !a'. a = a'
                               ==> read (memory :> bytes128 ctxt_p) s = a'`)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN AESXTS_ENC_ONE_BLOCK_TAC; DISCH_TAC] THEN

  ARM_STEPS_TAC AES256_XTS_ENCRYPT_EXEC (109--119) THEN

  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[] THEN
  ARITH_TAC
);;

(*******************************************)
(* Full proof *)

(* The following definitions that precede the proof are the same as
   the decrypt proof except where stated *)
let byte_list_at = define
  `byte_list_at (m : byte list) (m_p : int64) (len:int64) s =
    ! i. i < val len ==> read (memory :> bytes8(word_add m_p (word i))) s = EL i m`;;

let word_split_lemma = prove(
  `!len:int64. word_add (word_and len (word 0xf))
      (word_and len (word 0xfffffffffffffff0)) = len`,
  BITBLAST_TAC);;

let LEN_FULL_BLOCKS_LO_BOUND_THM = prove(
  `!(len:int64) len_full_blocks. word_and len (word 0xfffffffffffffff0) = len_full_blocks
   ==> ~(val len < 0x50)
   ==> ~(val len_full_blocks < 0x50)`,
   BITBLAST_TAC);;

let LEN_FULL_BLOCKS_HI_BOUND_THM = prove(
  `!(len:int64) len_full_blocks. word_and len (word 0xfffffffffffffff0) = len_full_blocks
   ==> val len <= 2 EXP 24
   ==> val len_full_blocks <= 2 EXP 24`,
   BITBLAST_TAC);;

let TAIL_LEN_BOUND_THM = prove(
  `!(len:int64) tail_len. word_and len (word 0xf) = tail_len
   ==> val tail_len < 0x10`,
   BITBLAST_TAC);;

let NUM_5BLOCKS_LO_BOUND_THM = prove(
  `!(len_full_blocks:int64) (num_5blocks:int64).
    val len_full_blocks <= 2 EXP 24
    ==> ~(val len_full_blocks < 0x50)
    ==> word (val len_full_blocks DIV 0x50) = num_5blocks
    ==> 0x0 < val num_5blocks`,
  REPEAT STRIP_TAC THEN
  EXPAND_TAC "num_5blocks" THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN
  UNDISCH_TAC `~(val (len_full_blocks:int64) < 0x50)` THEN
  ABBREV_TAC `n = val (len_full_blocks:int64)` THEN
  SUBGOAL_THEN `n DIV 0x50 < 2 EXP 64` ASSUME_TAC THENL
  [ ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[MOD_LT] THEN
  ARITH_TAC
);;

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

(* differs from the Decrypt definition in using key2_lst instead of key2 *)
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

(*
void aes_hw_xts_encrypt(const uint8_t *in, uint8_t *out, size_t length,
                        const AES_KEY *key1, const AES_KEY *key2,
                        const uint8_t iv[16])
*)

let AES256_XTS_ENCRYPT_CORRECT = prove(
  `!ptxt_p ctxt_p len key1_p key2_p iv_p
    pt_in iv
    k1_0 k1_1 k1_2 k1_3 k1_4 k1_5 k1_6 k1_7 k1_8 k1_9 k1_10 k1_11 k1_12 k1_13 k1_14
    k2_0 k2_1 k2_2 k2_3 k2_4 k2_5 k2_6 k2_7 k2_8 k2_9 k2_10 k2_11 k2_12 k2_13 k2_14
    pc stackpointer.
    aligned 16 stackpointer /\
    PAIRWISE nonoverlapping
    [(stackpointer, 6*16);
    (word pc, LENGTH aes256_xts_encrypt_mc);
    (ctxt_p, val len);
    (key1_p, 244);
    (key2_p, 244)] /\
    val len >= 16 /\ val len <= 2 EXP 24 /\ LENGTH pt_in = val len
  ==> ensures arm
      // precondition
      (\s. aligned_bytes_loaded s (word pc) aes256_xts_encrypt_mc /\
           read PC s = word (pc + 28) /\
           read SP s = stackpointer /\
           C_ARGUMENTS [ptxt_p; ctxt_p; len; key1_p; key2_p; iv_p] s /\
           byte_list_at pt_in ptxt_p len s /\
           read(memory :> bytes128 iv_p) s = iv /\
           set_key_schedule s key1_p k1_0 k1_1 k1_2 k1_3 k1_4 k1_5 k1_6 k1_7 k1_8 k1_9 k1_10 k1_11 k1_12 k1_13 k1_14 /\
           set_key_schedule s key2_p k2_0 k2_1 k2_2 k2_3 k2_4 k2_5 k2_6 k2_7 k2_8 k2_9 k2_10 k2_11 k2_12 k2_13 k2_14
      )
      // postcondition
      (\s. read PC s = word (pc + LENGTH aes256_xts_encrypt_mc - 8*4) /\
           byte_list_at (aes256_xts_encrypt pt_in (val len) iv
                [k1_0; k1_1; k1_2; k1_3; k1_4; k1_5; k1_6; k1_7; k1_8; k1_9; k1_10; k1_11; k1_12; k1_13; k1_14]
                [k2_0; k2_1; k2_2; k2_3; k2_4; k2_5; k2_6; k2_7; k2_8; k2_9; k2_10; k2_11; k2_12; k2_13; k2_14])
                ctxt_p len s
      )
      (MAYCHANGE [PC;X0;X1;X2;X4;X6;X7;X8;X9;X10;X11;X19;X20;X21;X22],,
       MAYCHANGE [Q0;Q1;Q4;Q5;Q6;Q7;Q8;Q9;Q10;Q11;Q12;Q13;Q14;Q15;Q16;Q17;Q18;Q19;Q20;Q21;Q22;Q23;Q24;Q25;Q26],,
       MAYCHANGE SOME_FLAGS,, MAYCHANGE [memory :> bytes128 ctxt_p],,
       MAYCHANGE [events])`,

  REWRITE_TAC [(REWRITE_CONV [aes256_xts_encrypt_mc] THENC LENGTH_CONV) `LENGTH aes256_xts_encrypt_mc`] THEN
  REWRITE_TAC[byte_list_at; set_key_schedule; NONOVERLAPPING_CLAUSES; C_ARGUMENTS; SOME_FLAGS; PAIRWISE; ALL] THEN
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
  ASM_CASES_TAC `val (len:int64) < 0x50` THENL [CHEAT_TAC; ALL_TAC] THEN

  SUBGOAL_THEN `~(val (len_full_blocks:int64) < 0x50)` ASSUME_TAC THENL
  [ UNDISCH_TAC `~(val (len:int64) < 0x50)` THEN
    UNDISCH_TAC `word_and len (word 0xfffffffffffffff0) = (len_full_blocks:int64)` THEN
    MP_TAC (SPECL [`len:int64`; `len_full_blocks:int64`] LEN_FULL_BLOCKS_LO_BOUND_THM) THEN
    SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `val (len_full_blocks:int64) <= 0x2 EXP 24` ASSUME_TAC THENL
  [ UNDISCH_TAC `val (len:int64) <= 0x2 EXP 24` THEN
    UNDISCH_TAC `word_and len (word 0xfffffffffffffff0) = (len_full_blocks:int64)` THEN
    MP_TAC (SPECL [`len:int64`; `len_full_blocks:int64`] LEN_FULL_BLOCKS_HI_BOUND_THM) THEN
    SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `0 < val (num_5blocks:int64)` ASSUME_TAC THENL
  [ UNDISCH_TAC `word (val (len_full_blocks:int64) DIV 0x50) = (num_5blocks:int64)` THEN
    UNDISCH_TAC `~(val (len_full_blocks:int64) < 0x50)` THEN
    UNDISCH_TAC `val (len_full_blocks:int64) <= 0x2 EXP 24` THEN
    MP_TAC (SPECL [`len_full_blocks:int64`; `num_5blocks:int64`]
      NUM_5BLOCKS_LO_BOUND_THM) THEN SIMP_TAC[]
    ; ALL_TAC] THEN

  (* Verify properties of the program until the beginning of the loop.
     This saves work in the second subgoal of the loop invariant and brings it here.
     Up to the loop:
     - First 5 tweaks are calculated from the iv
     - X2 contains len_full_blocks
     - X8 contains num_5_blocks
     - key1 schedule is loaded in Q registers
     - X9 and X10 are not needed to be spelled out for the proof itself, but to be
       kept in the assumption list after the proof *)
  ENSURES_SEQUENCE_TAC
  `pc + 0x140`
  `\s.
      read X0 s = ptxt_p /\
      read X1 s = ctxt_p /\
      read X2 s = len_full_blocks /\
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
      ARM_ACCSTEPS_TAC AES256_XTS_ENCRYPT_EXEC [] (66--76) THEN
      (* Branching on x2 *)
      (* Eliminate 1 block case *)
      SUBGOAL_THEN `~(val (len_full_blocks:int64) < 0x20)` MP_TAC THENL
      [ UNDISCH_TAC `~(val (len_full_blocks:int64) < 0x50)` THEN ARITH_TAC;
        DISCH_THEN(RULE_ASSUM_TAC o REWRITE_RULE o CONJUNCTS)] THEN

      (* Prove x9, x10 store lower and upper halves of tweak 1 and Q8 stores the full tweak 1 *)
      ARM_ACCSTEPS_TAC AES256_XTS_ENCRYPT_EXEC [] (77--85) THEN
      TWEAK_TAC `Q8:(armstate,int128)component` `1:num` `0:num` THEN

      (* Eliminate 2 blocks case *)
      ARM_ACCSTEPS_TAC AES256_XTS_ENCRYPT_EXEC [] (86--87) THEN
      SUBGOAL_THEN `~(val (len_full_blocks:int64) < 0x30)` MP_TAC THENL
      [ UNDISCH_TAC `~(val (len_full_blocks:int64) < 0x50)` THEN ARITH_TAC;
        DISCH_THEN(RULE_ASSUM_TAC o REWRITE_RULE o CONJUNCTS)] THEN
      (* prove Q9 stores tweak of 3rd block (index 2) *)
      ARM_ACCSTEPS_TAC AES256_XTS_ENCRYPT_EXEC [] (88--93) THEN
      TWEAK_TAC `Q9:(armstate,int128)component` `2:num` `0:num` THEN
      (* Eliminate 3 blocks case *)
      ARM_ACCSTEPS_TAC AES256_XTS_ENCRYPT_EXEC [] (94--95) THEN
      SUBGOAL_THEN `~(val (len_full_blocks:int64) < 0x40)` MP_TAC THENL
      [ UNDISCH_TAC `~(val (len_full_blocks:int64) < 0x50)` THEN ARITH_TAC;
        DISCH_THEN(RULE_ASSUM_TAC o REWRITE_RULE o CONJUNCTS)] THEN
      (* prove Q10 stores tweak of 4th block (index 3) *)
      ARM_ACCSTEPS_TAC AES256_XTS_ENCRYPT_EXEC [] (96--101) THEN
      TWEAK_TAC `Q10:(armstate,int128)component` `3:num` `0:num` THEN
      (* Eliminate 4 blocks case, proven by the assumption ~(len_full_blocks < 0x50)*)
      ARM_ACCSTEPS_TAC AES256_XTS_ENCRYPT_EXEC [] (102--103) THEN
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

  (* Loop invariant *)
  ENSURES_WHILE_PAUP_TAC
    `0` (* counter begin number *)
    `val (num_5blocks:int64)` (* counter end number *)
    `pc + 0x140` (* loop body start PC *)
    `pc + 0x430` (* loop backedge branch PC *)
    `\i s.
          // loop invariant at the end of the loop
         (read X0  s = word_add ptxt_p (word_mul (word 0x50) (word i)) /\
          read X1  s = word_add ctxt_p (word_mul (word 0x50) (word i)) /\
          read X21 s = tail_len /\
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
        ASM_REWRITE_TAC[]  ]
    ]

(*
# e(CONV_TAC NUM_REDUCE_CONV);;
val it : goalstack = 1 subgoal (4 total)

  0 [`aligned 0x10 stackpointer`]
  1 [`nonoverlapping_modulo (0x2 EXP 0x40) (val stackpointer,0x6 * 0x10)
      (pc,0xa80)`]
  2 [`nonoverlapping_modulo (0x2 EXP 0x40) (val stackpointer,0x6 * 0x10)
      (val ctxt_p,val len)`]
  3 [`nonoverlapping_modulo (0x2 EXP 0x40) (val stackpointer,0x6 * 0x10)
      (val key1_p,0xf4)`]
  4 [`nonoverlapping_modulo (0x2 EXP 0x40) (val stackpointer,0x6 * 0x10)
      (val key2_p,0xf4)`]
  5 [`nonoverlapping_modulo (0x2 EXP 0x40) (pc,0xa80) (val ctxt_p,val len)`]
  6 [`nonoverlapping_modulo (0x2 EXP 0x40) (pc,0xa80) (val key1_p,0xf4)`]
  7 [`nonoverlapping_modulo (0x2 EXP 0x40) (pc,0xa80) (val key2_p,0xf4)`]
  8 [`nonoverlapping_modulo (0x2 EXP 0x40) (val ctxt_p,val len)
      (val key1_p,0xf4)`]
  9 [`nonoverlapping_modulo (0x2 EXP 0x40) (val ctxt_p,val len)
      (val key2_p,0xf4)`]
 10 [`nonoverlapping_modulo (0x2 EXP 0x40) (val key1_p,0xf4)
      (val key2_p,0xf4)`]
 11 [`val len >= 0x10`]
 12 [`val len <= 0x2 EXP 0x18`]
 13 [`LENGTH pt_in = val len`]
 14 [`word_add tail_len len_full_blocks = len`]
 15 [`word_and len (word 0xfffffffffffffff0) = len_full_blocks`]
 16 [`word (val len_full_blocks DIV 0x50) = num_5blocks`]
 17 [`word_and len (word 0xf) = tail_len`]
 18 [`[k1_0; k1_1; k1_2; k1_3; k1_4; k1_5; k1_6; k1_7; k1_8; k1_9; k1_10;
       k1_11; k1_12; k1_13; k1_14] =
      key1_lst`]
 19 [`[k2_0; k2_1; k2_2; k2_3; k2_4; k2_5; k2_6; k2_7; k2_8; k2_9; k2_10;
       k2_11; k2_12; k2_13; k2_14] =
      key2_lst`]
 20 [`~(val len < 0x50)`]
 21 [`~(val len_full_blocks < 0x50)`]
 22 [`val len_full_blocks <= 0x2 EXP 0x18`]
 23 [`0x0 < val num_5blocks`]
 24 [`aligned_bytes_loaded s0 (word pc) aes256_xts_encrypt_mc`]
 25 [`read PC s0 = word (pc + 0x140)`]
 26 [`read X0 s0 = ptxt_p`]
 27 [`read X1 s0 = ctxt_p`]
 28 [`read X2 s0 = len_full_blocks`]
 29 [`read X21 s0 = tail_len`]
 30 [`read X8 s0 = num_5blocks`]
 31 [`read X9 s0 = word_zx (calculate_tweak 0x4 iv key2_lst)`]
 32 [`read X10 s0 =
      word_subword (calculate_tweak 0x4 iv key2_lst) (0x40,0x40)`]
 33 [`read Q6 s0 = calculate_tweak 0x0 iv key2_lst`]
 34 [`read Q8 s0 = calculate_tweak 0x1 iv key2_lst`]
 35 [`read Q9 s0 = calculate_tweak 0x2 iv key2_lst`]
 36 [`read Q10 s0 = calculate_tweak 0x3 iv key2_lst`]
 37 [`read Q11 s0 = calculate_tweak 0x4 iv key2_lst`]
 38 [`read X19 s0 = word 0x87`]
 39 [`read Q16 s0 = k1_0`]
 40 [`read Q17 s0 = k1_1`]
 41 [`read Q12 s0 = k1_2`]
 42 [`read Q13 s0 = k1_3`]
 43 [`read Q14 s0 = k1_4`]
 44 [`read Q15 s0 = k1_5`]
 45 [`read Q4 s0 = k1_6`]
 46 [`read Q5 s0 = k1_7`]
 47 [`read Q18 s0 = k1_8`]
 48 [`read Q19 s0 = k1_9`]
 49 [`read Q20 s0 = k1_10`]
 50 [`read Q21 s0 = k1_11`]
 51 [`read Q22 s0 = k1_12`]
 52 [`read Q23 s0 = k1_13`]
 53 [`read Q7 s0 = k1_14`]
 54 [`forall i.
          i < val len
          ==> read (memory :> bytes8 (word_add ptxt_p (word i))) s0 =
              EL i pt_in`]
 55 [`forall i.
          i < val (word 0x0)
          ==> read (memory :> bytes8 (word_add ctxt_p (word i))) s0 =
              EL i (aes256_xts_encrypt pt_in 0x0 iv key1_lst key2_lst)`]
 56 [`(MAYCHANGE:((armstate,?275580)component)list->armstate->armstate->bool)
      []
      s0
      s0`]

`forall i.
     i < val (word 0x0)
     ==> read (memory :> bytes8 (word_add ctxt_p (word i))) s0 =
         EL i (aes256_xts_encrypt pt_in 0x0 iv key1_lst key2_lst)`
*)
