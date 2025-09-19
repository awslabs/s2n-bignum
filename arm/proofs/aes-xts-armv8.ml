(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

use_file_raise_failure := true;;

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
  0xb202e7e8;       (* arm_MOV X8 (rvalue (word 0xcccccccccccccccc)) *)
  0xf29999a8;       (* arm_MOVK X8 (word 0xcccd) 0x0 *)
  0x9bc87c48;       (* arm_UMULH X8 X2 X8 *)
  0xd346fd08;       (* arm_LSR X8 X8 0x6 *)
  0xf100405f;       (* arm_CMP X2 (rvalue (word 0x10)) *)
  0x5400518b;       (* arm_BLT (word 0xa30) *)
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

  (* iv for second block *)
  (* pc + 0x90 *)
  0x9e6600c9;       (* arm_FMOV_FtoI X9 Q6 0x0 0x40 *)
  0x9eae00ca;       (* arm_FMOV_FtoI X10 Q6 0x1 0x40 *)
  0x528010f3;       (* arm_MOV W19 (rvalue (word 0x87)) *)
  0x93ca8156;       (* arm_ROR X22 X10 0x20 *)
  0x93c9fd4a;       (* arm_EXTR X10 X10 X9 0x3f *)
  0x0a967e6b;       (* arm_AND W11 W19 (Shiftedreg W22 ASR 0x1f) *)
  0xca090569;       (* arm_EOR X9 X11 (Shiftedreg X9 LSL 0x1) *)
  0x9e670128;       (* arm_FMOV_ItoF Q8 X9 0x0 *)
  0x9eaf0148;       (* arm_FMOV_ItoF Q8 X10 0x1 *)

  (* Load key schedule *)
  (* pc + 0xb4 *)
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
  (* pc + 0xd8 *)
  0xf100805f;       (* arm_CMP X2 (rvalue (word 0x20)) *)
  0x540042e3;       (* arm_BCC (word 0x85c) *) (* b.lo Lxts_enc_tail1x   // when input = 1 with tail *)

  0xf100c05f;       (* arm_CMP X2 (rvalue (word 0x30)) *)
  0x540039c3;       (* arm_BCC (word 0x738) *)
  0x93ca8156;       (* arm_ROR X22 X10 0x20 *)
  0x93c9fd4a;       (* arm_EXTR X10 X10 X9 0x3f *)
  0x0a967e6b;       (* arm_AND W11 W19 (Shiftedreg W22 ASR 0x1f) *)
  0xca090569;       (* arm_EOR X9 X11 (Shiftedreg X9 LSL 0x1) *)
  0x9e670129;       (* arm_FMOV_ItoF Q9 X9 0x0 *)
  0x9eaf0149;       (* arm_FMOV_ItoF Q9 X10 0x1 *)
  0xf101005f;       (* arm_CMP X2 (rvalue (word 0x40)) *)
  0x54002be3;       (* arm_BCC (word 0x57c) *)
  0x93ca8156;       (* arm_ROR X22 X10 0x20 *)
  0x93c9fd4a;       (* arm_EXTR X10 X10 X9 0x3f *)
  0x0a967e6b;       (* arm_AND W11 W19 (Shiftedreg W22 ASR 0x1f) *)
  0xca090569;       (* arm_EOR X9 X11 (Shiftedreg X9 LSL 0x1) *)
  0x9e67012a;       (* arm_FMOV_ItoF Q10 X9 0x0 *)
  0x9eaf014a;       (* arm_FMOV_ItoF Q10 X10 0x1 *)
  0xf101405f;       (* arm_CMP X2 (rvalue (word 0x50)) *)
  0x540019e3;       (* arm_BCC (word 0x33c) *)
  0x93ca8156;       (* arm_ROR X22 X10 0x20 *)
  0x93c9fd4a;       (* arm_EXTR X10 X10 X9 0x3f *)
  0x0a967e6b;       (* arm_AND W11 W19 (Shiftedreg W22 ASR 0x1f) *)
  0xca090569;       (* arm_EOR X9 X11 (Shiftedreg X9 LSL 0x1) *)
  0x9e67012b;       (* arm_FMOV_ItoF Q11 X9 0x0 *)
  0x9eaf014b;       (* arm_FMOV_ItoF Q11 X10 0x1 *)
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
  `! ptxt ctxt key1 key2 iv
     in_pt tweak
     k1_0 k1_1 k1_2 k1_3 k1_4 k1_5 k1_6 k1_7 k1_8 k1_9 k1_10 k1_11 k1_12 k1_13 k1_14
     k2_0 k2_1 k2_2 k2_3 k2_4 k2_5 k2_6 k2_7 k2_8 k2_9 k2_10 k2_11 k2_12 k2_13 k2_14
     pc stackpointer.
     aligned 16 stackpointer /\
           PAIRWISE nonoverlapping
           [(stackpointer, 6*16);
            (word pc, LENGTH aes256_xts_encrypt_mc);
            (ctxt, 16);
            (key1, 244);
            (key2, 244)]
    ==> ensures arm
      // precondition
      (\s. aligned_bytes_loaded s (word pc) aes256_xts_encrypt_mc /\
           read PC s = word (pc + 28) /\
           read SP s = stackpointer /\
           C_ARGUMENTS [ptxt; ctxt; word 16; key1; key2; iv] s /\
           read(memory :> bytes128 ptxt) s = in_pt /\
           read(memory :> bytes128 iv) s = tweak /\
           read(memory :> bytes32 (word_add key1 (word 240))) s = word 14 /\
           read(memory :> bytes128 key1) s = k1_0 /\
           read(memory :> bytes128 (word_add key1 (word 16))) s = k1_1 /\
           read(memory :> bytes128 (word_add key1 (word 32))) s = k1_2 /\
           read(memory :> bytes128 (word_add key1 (word 48))) s = k1_3 /\
           read(memory :> bytes128 (word_add key1 (word 64))) s = k1_4 /\
           read(memory :> bytes128 (word_add key1 (word 80))) s = k1_5 /\
           read(memory :> bytes128 (word_add key1 (word 96))) s = k1_6 /\
           read(memory :> bytes128 (word_add key1 (word 112))) s = k1_7 /\
           read(memory :> bytes128 (word_add key1 (word 128))) s = k1_8 /\
           read(memory :> bytes128 (word_add key1 (word 144))) s = k1_9 /\
           read(memory :> bytes128 (word_add key1 (word 160))) s = k1_10 /\
           read(memory :> bytes128 (word_add key1 (word 176))) s = k1_11 /\
           read(memory :> bytes128 (word_add key1 (word 192))) s = k1_12 /\
           read(memory :> bytes128 (word_add key1 (word 208))) s = k1_13 /\
           read(memory :> bytes128 (word_add key1 (word 224))) s = k1_14 /\
           read(memory :> bytes32 (word_add key2 (word 240))) s = word 14 /\
           read(memory :> bytes128 key2) s = k2_0 /\
           read(memory :> bytes128 (word_add key2 (word 16))) s = k2_1 /\
           read(memory :> bytes128 (word_add key2 (word 32))) s = k2_2 /\
           read(memory :> bytes128 (word_add key2 (word 48))) s = k2_3 /\
           read(memory :> bytes128 (word_add key2 (word 64))) s = k2_4 /\
           read(memory :> bytes128 (word_add key2 (word 80))) s = k2_5 /\
           read(memory :> bytes128 (word_add key2 (word 96))) s = k2_6 /\
           read(memory :> bytes128 (word_add key2 (word 112))) s = k2_7 /\
           read(memory :> bytes128 (word_add key2 (word 128))) s = k2_8 /\
           read(memory :> bytes128 (word_add key2 (word 144))) s = k2_9 /\
           read(memory :> bytes128 (word_add key2 (word 160))) s = k2_10 /\
           read(memory :> bytes128 (word_add key2 (word 176))) s = k2_11 /\
           read(memory :> bytes128 (word_add key2 (word 192))) s = k2_12 /\
           read(memory :> bytes128 (word_add key2 (word 208))) s = k2_13 /\
           read(memory :> bytes128 (word_add key2 (word 224))) s = k2_14
      )
      // postcondition
      (\s. read PC s = word (pc + LENGTH aes256_xts_encrypt_mc - 8*4) /\
           read(memory :> bytes128 ctxt) s =
              aes256_xts_encrypt_1block in_pt tweak
                [k1_0; k1_1; k1_2; k1_3; k1_4; k1_5; k1_6; k1_7; k1_8; k1_9; k1_10; k1_11; k1_12; k1_13; k1_14]
                [k2_0; k2_1; k2_2; k2_3; k2_4; k2_5; k2_6; k2_7; k2_8; k2_9; k2_10; k2_11; k2_12; k2_13; k2_14]
      )
      (MAYCHANGE [PC;X0;X1;X2;X4;X6;X7;X8;X9;X10;X11;X19;X20;X21;X22],,
       MAYCHANGE [Q0;Q1;Q4;Q5;Q6;Q7;Q8;Q9;Q10;Q11;Q12;Q13;Q14;Q15;Q16;Q17;Q18;Q19;Q20;Q21;Q22;Q23;Q24;Q25;Q26],,
       MAYCHANGE SOME_FLAGS,, MAYCHANGE [memory :> bytes128 ctxt],,
       MAYCHANGE [events])`
       (* ,,
       MAYCHANGE [memory :> bytes(stackpointer, 160) *),
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; C_ARGUMENTS; SOME_FLAGS; PAIRWISE; ALL] THEN
  REWRITE_TAC [(REWRITE_CONV [aes256_xts_encrypt_mc] THENC LENGTH_CONV) `LENGTH aes256_xts_encrypt_mc`] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN

  ARM_STEPS_TAC AES256_XTS_ENCRYPT_EXEC (1--1) THEN
  ARM_STEPS_TAC AES256_XTS_ENCRYPT_EXEC (2--2) THEN
  ARM_STEPS_TAC AES256_XTS_ENCRYPT_EXEC (3--3) THEN
  ARM_STEPS_TAC AES256_XTS_ENCRYPT_EXEC (4--4) THEN
  ARM_STEPS_TAC AES256_XTS_ENCRYPT_EXEC (5--6) THEN
  ARM_STEPS_TAC AES256_XTS_ENCRYPT_EXEC (7--25) THEN

  ARM_STEPS_TAC AES256_XTS_ENCRYPT_EXEC (26--56) THEN
  ARM_STEPS_TAC AES256_XTS_ENCRYPT_EXEC (57--69) THEN

(*  FIRST_X_ASSUM(MP_TAC o MATCH_MP (MESON[] `read Q6 s = a ==> !a'. a = a' ==> read Q6 s = a'`)) THEN *)
  FIRST_X_ASSUM(MP_TAC o SPEC
    `(aes256_encrypt (tweak:int128) [k2_0:int128; k2_1; k2_2; k2_3; k2_4; k2_5; k2_6; k2_7; k2_8; k2_9; k2_10; k2_11; k2_12; k2_13; k2_14]):int128`
    o  MATCH_MP (MESON[] `read Q6 s = a ==> !a'. a = a' ==> read Q6 s = a'`)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN AESENC_TAC; DISCH_TAC] THEN

   ARM_STEPS_TAC AES256_XTS_ENCRYPT_EXEC (70--70) THEN
  ARM_STEPS_TAC AES256_XTS_ENCRYPT_EXEC (71--78) THEN
  ARM_STEPS_TAC AES256_XTS_ENCRYPT_EXEC (79--87) THEN
  ARM_STEPS_TAC AES256_XTS_ENCRYPT_EXEC (88--89) THEN

  ARM_STEPS_TAC AES256_XTS_ENCRYPT_EXEC (90--90) THEN
  ARM_STEPS_TAC AES256_XTS_ENCRYPT_EXEC (91--119) THEN

(*  FIRST_X_ASSUM(MP_TAC o MATCH_MP (MESON[] `read Q0 s = a ==> !a'. a = a' ==> read Q0 s = a'`)) THEN *)
  FIRST_X_ASSUM(MP_TAC o SPEC
    `(aes256_encrypt
       (word_xor
          (aes256_encrypt
             tweak
             [k2_0; k2_1; k2_2; k2_3; k2_4; k2_5; k2_6; k2_7; k2_8;
              k2_9; k2_10; k2_11; k2_12; k2_13; k2_14])
          in_pt:int128)
       [k1_0:int128; k1_1; k1_2; k1_3; k1_4; k1_5; k1_6; k1_7; k1_8; k1_9; k1_10; k1_11; k1_12; k1_13; k1_14]):int128`
    o  MATCH_MP (MESON[] `read Q0 s = a ==> !a'. a = a' ==> read Q0 s = a'`)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN AESENC_TAC; DISCH_TAC] THEN

  ARM_STEPS_TAC AES256_XTS_ENCRYPT_EXEC (120--120) THEN

  ARM_STEPS_TAC AES256_XTS_ENCRYPT_EXEC (121--121) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC
    `(aes256_xts_encrypt_1block
        (in_pt:int128)
        (tweak:int128)
        [k1_0:int128; k1_1; k1_2; k1_3; k1_4; k1_5; k1_6; k1_7; k1_8; k1_9; k1_10;
         k1_11; k1_12; k1_13; k1_14]
        [k2_0:int128; k2_1; k2_2; k2_3; k2_4; k2_5; k2_6; k2_7; k2_8; k2_9; k2_10;
         k2_11; k2_12; k2_13; k2_14]):int128`
      o MATCH_MP (MESON[] `read (memory :> bytes128 ctxt) s = a ==> !a'. a = a'
                               ==> read (memory :> bytes128 ctxt) s = a'`)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN AESXTS_ENC_ONE_BLOCK_TAC; DISCH_TAC] THEN

  ARM_STEPS_TAC AES256_XTS_ENCRYPT_EXEC (122--126) THEN
  ARM_STEPS_TAC AES256_XTS_ENCRYPT_EXEC (127--132) THEN

  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[] THEN
  ARITH_TAC
);;



  (*
  `word_xor
 (aes256_encrypt
  (word_xor
   (aes256_encrypt tweak
   [k2_0; k2_1; k2_2; k2_3; k2_4; k2_5; k2_6; k2_7; k2_8; k2_9; k2_10; k2_11;
    k2_12; k2_13; k2_14])
  in_pt)
 [k1_0; k1_1; k1_2; k1_3; k1_4; k1_5; k1_6; k1_7; k1_8; k1_9; k1_10; k1_11;
  k1_12; k1_13; k1_14])
 (aes256_encrypt tweak
 [k2_0; k2_1; k2_2; k2_3; k2_4; k2_5; k2_6; k2_7; k2_8; k2_9; k2_10; k2_11;
  k2_12; k2_13; k2_14]) =
 word_xor
 (aes256_encrypt
  (word_xor in_pt
  (aes256_encrypt tweak
  [k2_0; k2_1; k2_2; k2_3; k2_4; k2_5; k2_6; k2_7; k2_8; k2_9; k2_10; k2_11;
   k2_12; k2_13; k2_14]))
 [k1_0; k1_1; k1_2; k1_3; k1_4; k1_5; k1_6; k1_7; k1_8; k1_9; k1_10; k1_11;
  k1_12; k1_13; k1_14])
 (aes256_encrypt tweak
 [k2_0; k2_1; k2_2; k2_3; k2_4; k2_5; k2_6; k2_7; k2_8; k2_9; k2_10; k2_11;
  k2_12; k2_13; k2_14])`

# e(AP_THM_TAC);;

  `word_xor
 (aes256_encrypt
  (word_xor
   (aes256_encrypt tweak
   [k2_0; k2_1; k2_2; k2_3; k2_4; k2_5; k2_6; k2_7; k2_8; k2_9; k2_10; k2_11;
    k2_12; k2_13; k2_14])
  in_pt)
 [k1_0; k1_1; k1_2; k1_3; k1_4; k1_5; k1_6; k1_7; k1_8; k1_9; k1_10; k1_11;
  k1_12; k1_13; k1_14]) =
 word_xor
 (aes256_encrypt
  (word_xor in_pt
  (aes256_encrypt tweak
  [k2_0; k2_1; k2_2; k2_3; k2_4; k2_5; k2_6; k2_7; k2_8; k2_9; k2_10; k2_11;
   k2_12; k2_13; k2_14]))
 [k1_0; k1_1; k1_2; k1_3; k1_4; k1_5; k1_6; k1_7; k1_8; k1_9; k1_10; k1_11;
  k1_12; k1_13; k1_14])`

# e(AP_TERM_TAC);;

`aes256_encrypt
 (word_xor
  (aes256_encrypt tweak
  [k2_0; k2_1; k2_2; k2_3; k2_4; k2_5; k2_6; k2_7; k2_8; k2_9; k2_10; k2_11;
   k2_12; k2_13; k2_14])
 in_pt)
 [k1_0; k1_1; k1_2; k1_3; k1_4; k1_5; k1_6; k1_7; k1_8; k1_9; k1_10; k1_11;
  k1_12; k1_13; k1_14] =
 aes256_encrypt
 (word_xor in_pt
 (aes256_encrypt tweak
 [k2_0; k2_1; k2_2; k2_3; k2_4; k2_5; k2_6; k2_7; k2_8; k2_9; k2_10; k2_11;
  k2_12; k2_13; k2_14]))
 [k1_0; k1_1; k1_2; k1_3; k1_4; k1_5; k1_6; k1_7; k1_8; k1_9; k1_10; k1_11;
  k1_12; k1_13; k1_14]`

# e(AP_THM_TAC);;
  `aes256_encrypt
 (word_xor
  (aes256_encrypt tweak
  [k2_0; k2_1; k2_2; k2_3; k2_4; k2_5; k2_6; k2_7; k2_8; k2_9; k2_10; k2_11;
   k2_12; k2_13; k2_14])
 in_pt) =
 aes256_encrypt
 (word_xor in_pt
 (aes256_encrypt tweak
 [k2_0; k2_1; k2_2; k2_3; k2_4; k2_5; k2_6; k2_7; k2_8; k2_9; k2_10; k2_11;
  k2_12; k2_13; k2_14]))`

# e(AP_TERM_TAC);;
`word_xor
 (aes256_encrypt tweak
 [k2_0; k2_1; k2_2; k2_3; k2_4; k2_5; k2_6; k2_7; k2_8; k2_9; k2_10; k2_11;
  k2_12; k2_13; k2_14])
 in_pt =
 word_xor in_pt
 (aes256_encrypt tweak
 [k2_0; k2_1; k2_2; k2_3; k2_4; k2_5; k2_6; k2_7; k2_8; k2_9; k2_10; k2_11;
  k2_12; k2_13; k2_14])`
*)


(*
If I don't make the second FIRST_X_ASSUM before XORING with the tweak,
How can I go within this term to do it later in the second argument of the
first xor to make it aes256_encrypt?

 83 [`read (memory :> bytes128 ctxt) s117 =
      word_xor
      (aes256_encrypt tweak
      [k2_0; k2_1; k2_2; k2_3; k2_4; k2_5; k2_6; k2_7; k2_8; k2_9; k2_10;
       k2_11; k2_12; k2_13; k2_14])
      (word_xor k1_14
      (aese
       (aesmc
       (aese
        (aesmc
        (aese
         (aesmc
         (aese
          (aesmc
          (aese
           (aesmc
           (aese
            (aesmc
            (aese
             (aesmc
             (aese
              (aesmc
              (aese
               (aesmc
               (aese
                (aesmc
                (aese
                 (aesmc
                 (aese
                  (aesmc
                  (aese
                   (aesmc
                   (aese
                    (word_xor
                     (aes256_encrypt tweak
                     [k2_0; k2_1; k2_2; k2_3; k2_4; k2_5; k2_6; k2_7; k2_8;
                      k2_9; k2_10; k2_11; k2_12; k2_13; k2_14])
                    in_pt)
                   k1_0))
                  k1_1))
                 k1_2))
                k1_3))
               k1_4))
              k1_5))
             k1_6))
            k1_7))
           k1_8))
          k1_9))
         k1_10))
        k1_11))
       k1_12))
      k1_13))`]


RULE_ASSUM_TAC(REWRITE_RULE[GSYM specth])

Why the REPEAT line in the following doesn't return back?
let AESXTS_ENC_ONE_BLOCK_TAC =
  REWRITE_TAC [aes256_xts_encrypt_one_block] THEN
  CONV_TAC (TOP_DEPTH_CONV let_CONV) THEN
  REPEAT (GEN_REWRITE_TAC LAND_CONV [WORD_XOR_SYM] ORELSE AP_THM_TAC ORELSE AP_TERM_TAC) THEN
  BITBLAST_TAC;;

  REWRITE_TAC may just repeat (without REPEAT) would arrive at a canonical form
  June: TARGET_REWRITE_TAC
*)
