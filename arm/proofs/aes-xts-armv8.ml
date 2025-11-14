(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

use_file_raise_failure := true;;

needs "arm/proofs/base.ml";;
needs "arm/proofs/aes_encrypt_spec.ml";;
needs "arm/proofs/aes_xts_encrypt_spec.ml";;

arm_print_log := true;;
components_print_log := true;;

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

let XTSENC_TAC reg ind ind_tweak =
  let tm = subst [ind, `ind:num`; ind_tweak, `ind_tweak:num`]
            `aes256_xts_encrypt_round (bytes_to_int128 (SUB_LIST (ind,0x10) (pt_in:byte list)))
              (calculate_tweak (ind_tweak) iv key2_lst) key1_lst` in
  let lemma = subst [reg, `reg:(armstate,int128)component`]
            `read (reg:(armstate,int128)component) (s:armstate) = a ==> !a'. a = a' ==> read reg s = a'` in
  let _ = print_term tm in
  let _ = print_term lemma in
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

let BYTE_LIST_AT_ADD_ASSUM_TAC new_pos bound =
  let rule = subst [new_pos, `new_pos:num`; bound, `bound:num`]
    `(pos:num) + bound <= LENGTH (bl:byte list) ==> new_pos < LENGTH bl` in
  let p = subst [new_pos, `new_pos:num`] `new_pos:num` in
  MP_TAC (ARITH_RULE rule) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN (LABEL_TAC "tmp") THEN
  FIRST_ASSUM(fun th -> MP_TAC(SPEC p th)) THEN
  USE_THEN "tmp" (fun th -> REWRITE_TAC[th]) THEN
  POP_ASSUM (K ALL_TAC);;

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

(* Copied from Decrypt proof without change because it can be instantiated for ptxt_p *)
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

(* Same as Decrypt but with "num_5blocks" replaced by "num_5blocks",
  which can still be used with Decrypt since it's universally quantified at the beginning of this lemma
  and the following ones *)
let READ_CT_TAIL4_LEMMA = prove(
  `!ct_ptr (num_5blocks:int64) (len:int64) (ct:byte list) s.
    (forall j. j < val len ==> read (memory :> bytes8 (word_add ct_ptr (word j))) s = EL j ct)
    /\ val num_5blocks * 0x50 + 0x40 <= val len
    /\ LENGTH ct = val len
    ==>
    read (memory :> bytes128 (word_add
      (word_add ct_ptr (word_mul (word 0x50) num_5blocks))
      (word 0x30))) s =
      bytes_to_int128 (SUB_LIST (val num_5blocks * 80 + 0x30, 16) ct) /\
    read (memory :> bytes128 (word_add
      (word_add ct_ptr (word_mul (word 0x50) num_5blocks))
      (word 0x20))) s =
      bytes_to_int128 (SUB_LIST (val num_5blocks * 80 + 0x20, 16) ct) /\
    read (memory :> bytes128 (word_add
      (word_add ct_ptr (word_mul (word 0x50) num_5blocks))
      (word 0x10))) s =
      bytes_to_int128 (SUB_LIST (val num_5blocks * 80 + 0x10, 16) ct) /\
    read (memory :> bytes128
      (word_add ct_ptr (word_mul (word 0x50) num_5blocks))) s =
      bytes_to_int128 (SUB_LIST (val num_5blocks * 80, 16) ct)
    `,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC [WORD_RULE `(word_mul (word 0x50) (num_5blocks:int64)) = word (val num_5blocks * 80)`] THEN
  MP_TAC
    (SPECL [`(val (num_5blocks:int64) * 80):num`; `ct:byte list`; `ct_ptr:int64`; `len:int64`; `s:armstate`]
     BYTE_LIST_AT_4BLOCKS) THEN
  REWRITE_TAC[byte_list_at] THEN ASM_SIMP_TAC[]
);;

let READ_CT_TAIL3_LEMMA = prove(
  `!ct_ptr (num_5blocks:int64) (len:int64) (ct:byte list) s.
    (forall j. j < val len ==> read (memory :> bytes8 (word_add ct_ptr (word j))) s = EL j ct)
    /\ val num_5blocks * 0x50 + 0x30 <= val len
    /\ LENGTH ct = val len
    ==>
    read (memory :> bytes128 (word_add
      (word_add ct_ptr (word_mul (word 0x50) num_5blocks))
      (word 0x20))) s =
      bytes_to_int128 (SUB_LIST (val num_5blocks * 80 + 0x20, 16) ct) /\
    read (memory :> bytes128 (word_add
      (word_add ct_ptr (word_mul (word 0x50) num_5blocks))
      (word 0x10))) s =
      bytes_to_int128 (SUB_LIST (val num_5blocks * 80 + 0x10, 16) ct) /\
    read (memory :> bytes128
      (word_add ct_ptr (word_mul (word 0x50) num_5blocks))) s =
      bytes_to_int128 (SUB_LIST (val num_5blocks * 80, 16) ct)
    `,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC [WORD_RULE `(word_mul (word 0x50) (num_5blocks:int64)) = word (val num_5blocks * 80)`] THEN
  MP_TAC
    (SPECL [`(val (num_5blocks:int64) * 80):num`; `ct:byte list`; `ct_ptr:int64`; `len:int64`; `s:armstate`]
     BYTE_LIST_AT_3BLOCKS) THEN
  REWRITE_TAC[byte_list_at] THEN ASM_SIMP_TAC[]
);;

let READ_CT_TAIL2_LEMMA = prove(
  `!ct_ptr (num_5blocks:int64) (len:int64) (ct:byte list) s.
    (forall j. j < val len ==> read (memory :> bytes8 (word_add ct_ptr (word j))) s = EL j ct)
    /\ val num_5blocks * 0x50 + 0x20 <= val len
    /\ LENGTH ct = val len
    ==>
    read (memory :> bytes128 (word_add
      (word_add ct_ptr (word_mul (word 0x50) num_5blocks))
      (word 0x10))) s =
      bytes_to_int128 (SUB_LIST (val num_5blocks * 80 + 0x10, 16) ct) /\
    read (memory :> bytes128
      (word_add ct_ptr (word_mul (word 0x50) num_5blocks))) s =
      bytes_to_int128 (SUB_LIST (val num_5blocks * 80, 16) ct)
    `,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC [WORD_RULE `(word_mul (word 0x50) (num_5blocks:int64)) = word (val num_5blocks * 80)`] THEN
  MP_TAC
    (SPECL [`(val (num_5blocks:int64) * 80):num`; `ct:byte list`; `ct_ptr:int64`; `len:int64`; `s:armstate`]
     BYTE_LIST_AT_2BLOCKS) THEN
  REWRITE_TAC[byte_list_at] THEN ASM_SIMP_TAC[]
);;

let READ_CT_TAIL1_LEMMA = prove(
  `!ct_ptr (num_5blocks:int64) (len:int64) (ct:byte list) s.
    (forall j. j < val len ==> read (memory :> bytes8 (word_add ct_ptr (word j))) s = EL j ct)
    /\ val num_5blocks * 0x50 + 0x10 <= val len
    /\ LENGTH ct = val len
    ==>
    read (memory :> bytes128
      (word_add ct_ptr (word_mul (word 0x50) num_5blocks))) s =
      bytes_to_int128 (SUB_LIST (val num_5blocks * 80, 16) ct)
    `,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC [WORD_RULE `(word_mul (word 0x50) (num_5blocks:int64)) = word (val num_5blocks * 80)`] THEN
  MP_TAC
    (SPECL [`(val (num_5blocks:int64) * 80):num`; `ct:byte list`; `ct_ptr:int64`; `len:int64`; `s:armstate`]
     BYTE_LIST_AT_1BLOCKS) THEN
  REWRITE_TAC[byte_list_at] THEN ASM_SIMP_TAC[]
);;

(* TODO: do I need this in encrypt? *)
let READ_CT_LAST_LEMMA = prove(
  `!ct_ptr (curr_len:num) (len:int64) (ct:byte list) s.
    (forall j. j < val len ==> read (memory :> bytes8 (word_add ct_ptr (word j))) s = EL j ct)
    /\ curr_len + 0x10 <= val len
    /\ LENGTH ct = val len
    ==>
    read (memory :> bytes128 (word_add ct_ptr (word curr_len))) s =
      bytes_to_int128 (SUB_LIST (curr_len, 16) ct)
    `,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC
    (SPECL [`curr_len:num`; `ct:byte list`; `ct_ptr:int64`; `len:int64`; `s:armstate`]
     BYTE_LIST_AT_1BLOCKS) THEN
  REWRITE_TAC[byte_list_at] THEN ASM_SIMP_TAC[]
);;

(* Different from decrypt in using len_full_blocks *)
let LEN_FULL_BLOCKS_LO_BOUND_THM = prove(
  `!(len:int64) len_full_blocks. word_and len (word 0xfffffffffffffff0) = len_full_blocks
   ==> ~(val len < 0x50)
   ==> ~(val len_full_blocks < 0x50)`,
   BITBLAST_TAC);;

let LEN_FULL_BLOCKS_LO_BOUND_1BLOCK_THM = prove(
  `!(len:int64) len_full_blocks. word_and len (word 0xfffffffffffffff0) = len_full_blocks
   ==> ~(val len < 0x10)
   ==> ~(val len_full_blocks < 0x10)`,
   BITBLAST_TAC);;

let LEN_FULL_BLOCKS_HI_BOUND_THM = prove(
  `!(len:int64) len_full_blocks. word_and len (word 0xfffffffffffffff0) = len_full_blocks
   ==> val len <= 2 EXP 24
   ==> val len_full_blocks <= 2 EXP 24`,
   BITBLAST_TAC);;

let LEN_FULL_BLOCKS_LT_LEN_THM = prove(
  `!(len:int64). val (word_and len (word 0xfffffffffffffff0)) <= val len`,
  BITBLAST_TAC
);;

let TAIL_LEN_BOUND_THM = prove(
  `!(len:int64) tail_len. word_and len (word 0xf) = tail_len
   ==> val tail_len < 0x10`,
   BITBLAST_TAC);;

(* Different from decrypt in using num_5blocks *)
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
(*
let len_full_blocks_LT_LEN_THM = prove(
  `!(len:int64) num_blocks.
    word_and len (word 0xfffffffffffffff0) = num_blocks
    ==> ~(val num_blocks < 0x60)
    ==> val (word_sub num_blocks (word 0x10)) <= val len`,
    BITBLAST_TAC
);;
*)
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

let INT128_TO_BYTES_OF_BYTES_TO_INT128 = prove(
  `!x. LENGTH x = 16 ==> int128_to_bytes (bytes_to_int128 x) = x`,
  REPEAT STRIP_TAC THEN
  MP_TAC ((GEN_REWRITE_CONV I [LENGTH_EQ_LIST_OF_SEQ] THENC
   RAND_CONV LIST_OF_SEQ_CONV) `LENGTH (x:byte list) = 16`) THEN
  ASM_SIMP_TAC[] THEN
  DISCH_THEN (fun th -> ONCE_REWRITE_TAC[th]) THEN
  REWRITE_TAC[bytes_to_int128] THEN
  REWRITE_TAC EL_16_8_CLAUSES THEN
  REWRITE_TAC[int128_to_bytes] THEN
  REWRITE_TAC[CONS_11] THEN
  REPEAT (CONJ_TAC THEN BITBLAST_TAC)
);;

let MEMORY_READ_SUBSET_LEMMA = prove
 (`!len (ptr:int64) (bl:byte list) s.
   (forall i.
          i < SUC len
          ==> read (memory :> bytes8 (word_add ptr (word i))) s = EL i bl) ==>
   (forall i.
           i < len
           ==> read (memory :> bytes8 (word_add ptr (word i))) s = EL i bl) /\
   read (memory :> bytes (word_add ptr (word len),1)) s =
    val(read (memory :> bytes8 (word_add ptr (word len))) s)
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
  MP_TAC (ISPECL [`(word_add (ptr:int64) (word len)):int64`; `1:num`; `(read memory s):int64->byte`] READ_BYTES_BOUND) THEN
  CONV_TAC NUM_REDUCE_CONV
);;

let BYTE_LIST_AT_SPLIT = prove(
  `!len (ptr:int64) (bl:byte list) s.
  SUC len <= LENGTH bl ==>
   ((forall i.
     i < SUC len
     ==> read (memory :> bytes8 (word_add ptr (word i))) s = EL i bl) <=>
   ((forall i.
     i < len
     ==> read (memory :> bytes8 (word_add ptr (word i))) s = EL i bl) /\
    read (memory :> bytes8 (word_add ptr (word len))) s = EL len bl))`,
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

let HD_SUB_LIST_CONS = prove
 (`!(h:A) (t:A list) n. 0 < n ==> HD (SUB_LIST (0,n) (CONS h t)) = h`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `n:num` num_CASES) THEN
  ASM_SIMP_TAC[ARITH_RULE `0 < n ==> ~(n = 0)`] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:num` SUBST_ALL_TAC) THEN
  REWRITE_TAC[SUB_LIST_CLAUSES; HD]);;

let HD_SUB_LIST_CONS_GENERAL = prove(
  `!p n (l:A list). p < LENGTH l /\ 0 < n ==> HD (SUB_LIST (p,n) l) = EL p l`,
  INDUCT_TAC THENL
  [
    GEN_TAC THEN
    LIST_INDUCT_TAC THENL
    [
      REWRITE_TAC[LENGTH] THEN ARITH_TAC;
      REPEAT STRIP_TAC THEN
      REWRITE_TAC[EL; HD] THEN
      MP_TAC (SPECL [`h:A`; `t:A list`; `n:num`] HD_SUB_LIST_CONS) THEN
      ASM_SIMP_TAC[]
    ]; ALL_TAC
  ] THEN
  GEN_TAC THEN
  LIST_INDUCT_TAC THENL
  [
    REWRITE_TAC[LENGTH] THEN ARITH_TAC;
    REPEAT STRIP_TAC THEN
    REWRITE_TAC[SUB_LIST_CLAUSES] THEN
    REWRITE_TAC[EL; TL] THEN
    FIRST_X_ASSUM (fun th -> MATCH_MP_TAC (SPECL [`n:num`; `t:A list`] th)) THEN
    ASM_SIMP_TAC[] THEN
    UNDISCH_TAC `SUC p < LENGTH (CONS h (t:A list))` THEN
    REWRITE_TAC[LENGTH] THEN
    ARITH_TAC
  ]
);;

let TL_SUB_LIST_CONS = prove
(`!(h:A) (t:A list) n. 0 < n ==> TL (SUB_LIST (0,n) (CONS h t)) = SUB_LIST (0, n - 1) t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `n:num` num_CASES) THEN
  ASM_SIMP_TAC[ARITH_RULE `0 < n ==> ~(n = 0)`] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:num` SUBST_ALL_TAC) THEN
  REWRITE_TAC[SUB_LIST_CLAUSES; TL] THEN
  REWRITE_TAC[ARITH_RULE `SUC m - 1 = m`]);;

let TL_SUB_LIST_CONS_GENERAL = prove(
  `!p n (l:A list). p < LENGTH l ==> 0 < n
    ==> TL (SUB_LIST (p, n) l) = SUB_LIST (p + 1, n - 1) l`,
  INDUCT_TAC THENL
  [
    GEN_TAC THEN
    LIST_INDUCT_TAC THENL
    [
      REWRITE_TAC[LENGTH] THEN ARITH_TAC;
      CONV_TAC NUM_REDUCE_CONV THEN
      REPEAT STRIP_TAC THEN
      MP_TAC (SPECL [`h:A`; `t:A list`; `n:num`] TL_SUB_LIST_CONS) THEN
      ASM_SIMP_TAC[num_CONV `1`; SUB_LIST_CLAUSES]
    ]; ALL_TAC
  ] THEN
  GEN_TAC THEN
  LIST_INDUCT_TAC THENL
  [
    REWRITE_TAC[LENGTH] THEN ARITH_TAC;
    REPEAT STRIP_TAC THEN
    REWRITE_TAC[ARITH_RULE `SUC p + 1 = SUC (p + 1)`] THEN
    REWRITE_TAC[SUB_LIST_CLAUSES] THEN
    FIRST_X_ASSUM (fun th -> MP_TAC (SPECL [`n:num`; `t:A list`] th)) THEN
    SUBGOAL_THEN `p < LENGTH (t:A list)` ASSUME_TAC THENL
    [ UNDISCH_TAC `SUC p < LENGTH (CONS h (t:A list))` THEN
      REWRITE_TAC[LENGTH] THEN ARITH_TAC
      ; ALL_TAC] THEN
    ASM_SIMP_TAC[]
  ]
);;

let EL_SUB_LIST = prove(
  `!(i:num) n (l:A list). i < n /\ n <= LENGTH l ==>
    EL i (SUB_LIST (0, n) l) = EL i l`,
  INDUCT_TAC THENL
  [ (* i = 0 *)
    ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
    LIST_INDUCT_TAC THENL
    [
      REPEAT STRIP_TAC THEN
      IMP_REWRITE_TAC[SUB_LIST_TRIVIAL] THEN
      REWRITE_TAC[LENGTH] THEN
      ARITH_TAC; ALL_TAC
    ] THEN
    REPEAT STRIP_TAC THEN
    IMP_REWRITE_TAC[EL; HD; HD_SUB_LIST_CONS];
    ALL_TAC
  ] THEN
  (* i != 0 *)
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
  LIST_INDUCT_TAC THENL
  [
    REPEAT STRIP_TAC THEN
    IMP_REWRITE_TAC[SUB_LIST_TRIVIAL] THEN
    REWRITE_TAC[LENGTH] THEN
    ARITH_TAC; ALL_TAC
  ] THEN
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[EL; TL] THEN
  IMP_REWRITE_TAC[TL_SUB_LIST_CONS] THEN
  REPEAT CONJ_TAC THENL
  [ ASM_SIMP_TAC[ARITH_RULE `SUC i < n ==> i < n - 1`];
    SUBGOAL_THEN `LENGTH (CONS h (t:A list)) = SUC (LENGTH t)` ASSUME_TAC THENL
    [ REWRITE_TAC[LENGTH]; ALL_TAC ] THEN
    ASM_ARITH_TAC;
    MP_TAC (ARITH_RULE `SUC i < n ==> 0 < n`) THEN
    ASM_SIMP_TAC[]
  ]
);;

let EL_SUB_LIST_SHIFT = prove(
  `!(i:num) p (l:A list) n. 0 < i /\ i < n /\ n <= LENGTH l - p ==>
    EL (i - 1) (SUB_LIST (p + 1, n - 1) l) = EL i (SUB_LIST (p, n) l)`,
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `EL i (SUB_LIST (p, n) (l:A list)) = EL (SUC (i - 1)) (SUB_LIST (p, SUC (n - 1)) l)` SUBST1_TAC THENL
    [ IMP_REWRITE_TAC[ARITH_RULE `0 < i ==> SUC (i - 1) = i`] THEN
      ASM_ARITH_TAC; ALL_TAC ] THEN
    DISJ_CASES_TAC (ISPEC `l:(A)list` list_CASES) THENL [
      FIRST_X_ASSUM SUBST_ALL_TAC THEN
      UNDISCH_TAC `n <= LENGTH ([]:A list) - p` THEN
      REWRITE_TAC[LENGTH] THEN
      ASM_ARITH_TAC; ALL_TAC
    ] THEN

    REPEAT_N 2 (FIRST_X_ASSUM CHOOSE_TAC) THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    REWRITE_TAC[EL; TL] THEN
    IMP_REWRITE_TAC[TL_SUB_LIST_CONS_GENERAL] THEN
    IMP_REWRITE_TAC[ARITH_RULE `0 < n ==> SUC (n - 1) = n`] THEN
    ASM_ARITH_TAC
  );;

let MEMORY_READ_BYTES_SUBSET_LEMMA = prove(
  `!len (ptr:int64) (bl:byte list) s.
   SUC len <= LENGTH bl ==>
   read (memory :> bytes (ptr,SUC len)) s =
      num_of_bytelist (SUB_LIST (0x0,SUC len) bl) ==>
   read (memory :> bytes (ptr,len)) s =
      num_of_bytelist (SUB_LIST (0x0,len) bl) /\
   read (memory :> bytes8 (word_add ptr (word len))) s = EL len bl`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `SUC len = len + 1` SUBST_ALL_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN
  SUBGOAL_THEN `len <= LENGTH (bl:byte list)` ASSUME_TAC THENL [ ASM_ARITH_TAC; ALL_TAC] THEN
  (* Use READ_BYTES_COMBINE to decompose the memory read *)
  MP_TAC(ISPECL [`ptr:int64`; `len:num`; `1:num`; `(read memory s):int64->byte`] READ_BYTES_COMBINE) THEN
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
  [ (* First part: read (memory :> bytes (ptr,len)) s = num_of_bytelist (SUB_LIST (0,len) bl) *)
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
  (* Second part: read (memory :> bytes8 (word_add ptr (word len))) s = EL len bl *)
  FIRST_X_ASSUM(MP_TAC o AP_TERM `\x. x DIV 2 EXP (8 * len)`) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(0x2 EXP (0x8 * len) = 0x0)` ASSUME_TAC THENL
  [ REWRITE_TAC[EXP_EQ_0; ARITH_EQ]; ALL_TAC] THEN
  IMP_REWRITE_TAC[DIV_MULT_ADD] THEN
  SUBGOAL_THEN `read (bytes (ptr,len)) (read memory s) < 0x2 EXP (0x8 * len)` ASSUME_TAC THENL
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
  `!len (ptr:int64) (bl:byte list) s.
    len <= LENGTH bl ==>
    ((forall i. i < len
      ==> read (memory :> bytes8 (word_add ptr (word i))) s = EL i bl) <=>
    (read (memory :> bytes (ptr, len)) s = num_of_bytelist (SUB_LIST (0, len) bl)))`,
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
    MP_TAC (SPECL [`len:num`; `ptr:int64`; `bl:byte list`; `s:armstate`] MEMORY_READ_SUBSET_LEMMA) THEN
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
  MP_TAC (SPECL [`len:num`; `ptr:int64`; `bl:byte list`; `s:armstate`] MEMORY_READ_BYTES_SUBSET_LEMMA) THEN
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

let SUB_LIST_IDEMPOTENT_P = prove(
  `!p n (l:(A)list). SUB_LIST (0,n) (SUB_LIST (p,n) l) = SUB_LIST (p,n) l`,
  INDUCT_TAC THENL[
    REWRITE_TAC[SUB_LIST_IDEMPOTENT];

    REPEAT STRIP_TAC THEN
    DISJ_CASES_TAC (ISPEC `l:(A)list` list_CASES) THENL [
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUB_LIST_CLAUSES];
      ALL_TAC
    ] THEN
    FIRST_X_ASSUM MP_TAC THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUB_LIST_CLAUSES] THEN
    ASM_REWRITE_TAC[]
  ]
);;


let SUB_LIST_MIN_RIGHT = prove(
  `!p (l:(A)list) (n:num) m. SUB_LIST (0,n) (SUB_LIST (p,m) l) = SUB_LIST (p, MIN n m) l`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `(m:num) <= n` THENL [
    FIRST_X_ASSUM MP_TAC THEN REWRITE_TAC[LE_EXISTS] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUB_LIST_SPLIT;ADD_CLAUSES;ARITH_RULE`MIN ((x:num)+y) x = x`] THEN
    REWRITE_TAC[SUB_LIST_IDEMPOTENT_P] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM APPEND_NIL] THEN
    AP_TERM_TAC THEN MATCH_MP_TAC SUB_LIST_TRIVIAL THEN
    REWRITE_TAC[LENGTH_SUB_LIST] THEN ARITH_TAC; ALL_TAC] THEN

  IMP_REWRITE_TAC[ARITH_RULE `~(m <= n) ==> MIN n m = n`] THEN
  FIRST_X_ASSUM MP_TAC THEN REWRITE_TAC[NOT_LE;LT_EXISTS] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[SUB_LIST_SPLIT;ADD_CLAUSES;ARITH_RULE`MIN (x:num) (x+y) = x`] THEN

  MP_TAC (ISPECL [`l:A list`; `p:num`; `n:num`] LENGTH_SUB_LIST) THEN
  ASM_CASES_TAC `n <= LENGTH (l:A list) - p` THENL [
    IMP_REWRITE_TAC[ARITH_RULE `!n m. n <= m ==> MIN n m = n`] THEN
    DISCH_TAC THEN
    IMP_REWRITE_TAC[SUB_LIST_APPEND_LEFT] THEN
    IMP_REWRITE_TAC[SUB_LIST_LENGTH_IMPLIES] THEN
    ARITH_TAC; ALL_TAC
  ] THEN

  IMP_REWRITE_TAC[ARITH_RULE `!n m. ~(n <= m) ==> MIN n m = m`] THEN
  SUBGOAL_THEN `SUB_LIST (p + n,SUC d) (l:A list) = []` SUBST1_TAC THENL
  [ MATCH_MP_TAC SUB_LIST_TRIVIAL THEN
    ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[APPEND_NIL] THEN
  REWRITE_TAC[SUB_LIST_IDEMPOTENT_P]
);;

let SUB_LIST_MIN_LEFT = prove(
  `!q (l:A list) n m.
    SUB_LIST (q,n) (SUB_LIST (0,m) l) = SUB_LIST (q, MIN n (m - q)) l`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `n <= m - q` THENL [
    IMP_REWRITE_TAC[ARITH_RULE `x <= y ==> MIN x y = x`] THEN
    UNDISCH_TAC `n <= m - q` THEN
    MAP_EVERY SPEC1_TAC [`n:num`; `l:A list`; `q:num`; `m:num`] THEN
    (* Induct over m *)
    INDUCT_TAC THENL
    [
      REPEAT STRIP_TAC THEN
      IMP_REWRITE_TAC[ARITH_RULE `n <= 0 - q ==> n = 0`] THEN
      REWRITE_TAC[SUB_LIST_CLAUSES];

      INDUCT_TAC THENL
      [
        REWRITE_TAC[SUB_0] THEN
        REPEAT STRIP_TAC THEN
        MP_TAC (SPECL [`0:num`; `l:A list`; `n:num`; `SUC m:num`] SUB_LIST_MIN_RIGHT) THEN
        IMP_REWRITE_TAC[ARITH_RULE `x <= y ==> MIN x y = x`];

        LIST_INDUCT_TAC THENL[
          REWRITE_TAC[SUB_LIST_CLAUSES];
          REWRITE_TAC[SUB_LIST_CLAUSES] THEN
          REPEAT STRIP_TAC THEN
          FIRST_X_ASSUM
            (fun th -> MP_TAC
              (SPECL [`q:num`; `t:A list`; `n:num`] th)) THEN
          ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
          SIMP_TAC[]
        ]
      ]
    ]; ALL_TAC
  ] THEN

  (* Case n > m - q*)
  IMP_REWRITE_TAC[ARITH_RULE `~(x <= y) ==> MIN x y = y`] THEN
  UNDISCH_TAC `~(n <= m - q)` THEN
  MAP_EVERY SPEC1_TAC [`n:num`; `l:A list`; `q:num`; `m:num`] THEN
  INDUCT_TAC THENL
  [
    REPEAT STRIP_TAC THEN
    REWRITE_TAC[ARITH_RULE `0 - q = 0`] THEN
    REWRITE_TAC[SUB_LIST_CLAUSES];

    INDUCT_TAC THENL
    [
      REWRITE_TAC[SUB_0] THEN
      REPEAT STRIP_TAC THEN
      MP_TAC (SPECL [`0:num`; `l:A list`; `n:num`; `SUC m:num`] SUB_LIST_MIN_RIGHT) THEN
      IMP_REWRITE_TAC[ARITH_RULE `~(x <= y) ==> MIN x y = y`];

      LIST_INDUCT_TAC THENL[
        REWRITE_TAC[SUB_LIST_CLAUSES];
        REWRITE_TAC[SUB_LIST_CLAUSES] THEN
        REPEAT STRIP_TAC THEN
        REWRITE_TAC[ARITH_RULE `SUC m - SUC q = m - q`] THEN
        FIRST_X_ASSUM
            (fun th -> MP_TAC
              (SPECL [`q:num`; `t:A list`; `n:num`] th)) THEN
        ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
        SIMP_TAC[]
      ]
    ]
  ]
);;

let SUB_LIST_MIN_GENERAL = prove(
  `!p q (l:(A)list) (n:num) m.
    SUB_LIST (q,n) (SUB_LIST (p,m) l) = SUB_LIST (p + q, MIN n (m - q)) l`,
  REPEAT STRIP_TAC THEN
  (* Case n <= m - q *)
  ASM_CASES_TAC `n <= m - q` THENL [
    IMP_REWRITE_TAC[ARITH_RULE `x <= y ==> MIN x y = x`] THEN
    (* Induct over p *)
    UNDISCH_TAC `n <= m - q` THEN
    MAP_EVERY SPEC1_TAC [`m:num`; `n:num`; `l:A list`; `q:num`; `p:num`] THEN
    INDUCT_TAC THENL
    [
      REWRITE_TAC[ADD] THEN
      REPEAT STRIP_TAC THEN
      MP_TAC (SPECL [`q:num`; `l:A list`; `n:num`; `m:num`] SUB_LIST_MIN_LEFT) THEN
      IMP_REWRITE_TAC[ARITH_RULE `x <= y ==> MIN x y = x`];
      ALL_TAC
    ] THEN

    ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
    LIST_INDUCT_TAC THENL[
      REWRITE_TAC[SUB_LIST_CLAUSES];
      REWRITE_TAC[ARITH_RULE `SUC p + q = SUC (p + q)`] THEN
      REWRITE_TAC[SUB_LIST_CLAUSES] THEN
      ASM_REWRITE_TAC[]
    ]; ALL_TAC
  ] THEN

  (* Case n > m - q*)
  IMP_REWRITE_TAC[ARITH_RULE `~(x <= y) ==> MIN x y = y`] THEN
  UNDISCH_TAC `~(n <= m - q)` THEN
  MAP_EVERY SPEC1_TAC [`m:num`; `n:num`; `l:A list`; `q:num`; `p:num`] THEN
  INDUCT_TAC THENL
  [
    REWRITE_TAC[ADD] THEN
    REPEAT STRIP_TAC THEN
    MP_TAC (SPECL [`q:num`; `l:A list`; `n:num`; `m:num`] SUB_LIST_MIN_LEFT) THEN
    IMP_REWRITE_TAC[ARITH_RULE `~(x <= y) ==> MIN x y = y`];
    ALL_TAC
  ] THEN

  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
  LIST_INDUCT_TAC THENL[
    REWRITE_TAC[SUB_LIST_CLAUSES];
    REWRITE_TAC[ARITH_RULE `SUC p + q = SUC (p + q)`] THEN
    REWRITE_TAC[SUB_LIST_CLAUSES] THEN
    ASM_REWRITE_TAC[]
  ]
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

let LENGTH_OF_INT128_TO_BYTES = prove(
  `!x. LENGTH(int128_to_bytes x) = 16`,
  STRIP_TAC THEN
  REWRITE_TAC[int128_to_bytes] THEN
  REWRITE_TAC[LENGTH] THEN
  CONV_TAC NUM_REDUCE_CONV
);;

let DIVISION_BY_80_LEMMA = prove(
  `!(a:num) b. a DIV 0x50 = b /\
    0x10 divides a /\
    ~(a - b * 0x50 = 0x10) /\
    ~(a - b * 0x50 = 0x20) /\
    ~(a - b * 0x50 = 0x30) /\
    ~(a - b * 0x50 = 0x40) ==>
    b * 0x50 = a`,
  REPEAT STRIP_TAC THEN
  (* Use the division theorem: a = b * 0x50 + (a MOD 0x50) *)
  MP_TAC (SPECL [`a:num`; `0x50`] DIVISION) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REPEAT STRIP_TAC THEN

  (* We have a = b * 0x50 + (a MOD 0x50) and a DIV 0x50 = b *)
  SUBGOAL_THEN `a = b * 0x50 + (a MOD 0x50)` ASSUME_TAC THENL [
    ASM_ARITH_TAC; ALL_TAC] THEN

  (* Show that a MOD 0x50 = 0 by case analysis *)
  SUBGOAL_THEN `a MOD 0x50 = 0` ASSUME_TAC THENL [
    (* Since 0x10 divides a, we know a = k * 0x10 for some k *)
    UNDISCH_TAC `0x10 divides a` THEN
    REWRITE_TAC[divides] THEN
    STRIP_TAC THEN

    (* The remainder a MOD 0x50 must be a multiple of 0x10 and < 0x50 *)
    (* So it's one of: 0, 0x10, 0x20, 0x30, 0x40 *)
    SUBGOAL_THEN `(a MOD 0x50 = 0) \/ (a MOD 0x50 = 0x10) \/
                  (a MOD 0x50 = 0x20) \/ (a MOD 0x50 = 0x30) \/
                  (a MOD 0x50 = 0x40)` ASSUME_TAC THENL
    [ ASM_REWRITE_TAC[] THEN

      SUBGOAL_THEN `(0x10 * x) MOD 0x50 = (x MOD 5) * 0x10` SUBST1_TAC THENL [
        SUBGOAL_THEN `0x50 = 5 * 0x10` SUBST1_TAC THENL [
          CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
        MP_TAC (SPECL [`0x10 * x`; `0x10`; `5`] MOD_MULT_MOD) THEN
        REWRITE_TAC[MOD_MULT; ADD_CLAUSES] THEN
        IMP_REWRITE_TAC[DIV_MULT] THEN
        CONV_TAC NUM_REDUCE_CONV THEN
        SIMP_TAC[] THEN DISCH_TAC THEN
        REWRITE_TAC[MULT_SYM]
        ; ALL_TAC] THEN

      SUBGOAL_THEN `x MOD 5 < 5` ASSUME_TAC THENL [
        REWRITE_TAC[MOD_LT_EQ] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
      SUBGOAL_THEN `x MOD 5 = 0 \/ x MOD 5 = 1 \/ x MOD 5 = 2 \/ x MOD 5 = 3 \/ x MOD 5 = 4` ASSUME_TAC THENL [
        UNDISCH_TAC `x MOD 0x5 < 0x5` THEN ARITH_TAC ; ALL_TAC] THEN

      REPEAT (FIRST_X_ASSUM DISJ_CASES_TAC) THENL
      [ ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
        ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
        ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
        ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
        ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV]
      ; ALL_TAC] THEN

    (* Now eliminate the non-zero cases using the assumptions *)
    SUBGOAL_THEN `~(a MOD 0x50 = 0x10)` ASSUME_TAC THENL
    [ UNDISCH_TAC `~(a - b * 0x50 = 0x10)` THEN
      UNDISCH_TAC `a = b * 0x50 + a MOD 0x50` THEN
      ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `~(a MOD 0x50 = 0x20)` ASSUME_TAC THENL
    [ UNDISCH_TAC `~(a - b * 0x50 = 0x20)` THEN
      UNDISCH_TAC `a = b * 0x50 + a MOD 0x50` THEN
      ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `~(a MOD 0x50 = 0x30)` ASSUME_TAC THENL
    [ UNDISCH_TAC `~(a - b * 0x50 = 0x30)` THEN
      UNDISCH_TAC `a = b * 0x50 + a MOD 0x50` THEN
      ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `~(a MOD 0x50 = 0x40)` ASSUME_TAC THENL
    [ UNDISCH_TAC `~(a - b * 0x50 = 0x40)` THEN
      UNDISCH_TAC `a = b * 0x50 + a MOD 0x50` THEN
      ARITH_TAC; ALL_TAC] THEN

    ASM_MESON_TAC[]; ALL_TAC
  ] THEN

  (* Finally conclude b * 0x50 = a *)
  ASM_ARITH_TAC
);;

let WORD_AND_MASK16 = prove(
  `word_and (len:int64) (word 0xfffffffffffffff0) = word_sub len (word_and len (word 0xf))`,
  BITBLAST_TAC
);;


let WORD_AND_MASK16_EQ_0 = prove(
  `!(x:int64). val x < 16 ==> ~(val x = 0x0) ==> ~(val (word_and x (word 0xf)) = 0x0)`,
  BITBLAST_TAC);;

(* Same as Decrypt proof with a different name *)
let LEN_FULL_BLOCKS_TO_VAL = prove(
  `!(len:int64). word_and len (word 0xfffffffffffffff0) = word (16 * (val len DIV 16))`,
  GEN_TAC THEN
  REWRITE_TAC[WORD_AND_MASK16] THEN
  REWRITE_TAC[GSYM VAL_EQ] THEN
  SUBGOAL_THEN `16 * val (len:int64) DIV 16 = val len - (val len MOD 16)` SUBST1_TAC THENL
  [REWRITE_TAC[DIVISION_SIMP] THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `0xf = 2 EXP 4 - 1`] THEN
  REWRITE_TAC[WORD_AND_MASK_WORD] THEN
  CONV_TAC NUM_REDUCE_CONV THEN

  REWRITE_TAC[VAL_WORD_SUB] THEN
  SUBGOAL_THEN `val (len:int64) >= val ((word (val len MOD 0x10)):int64)` ASSUME_TAC THENL [
    REWRITE_TAC[VAL_WORD; DIMINDEX_64; GE] THEN
    MP_TAC (SPECL [`val (len:int64) MOD 0x10`; `0x2 EXP 0x40`] MOD_LE) THEN
    ARITH_TAC;
    ALL_TAC
  ] THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN

  SUBGOAL_THEN `val (len:int64) MOD 0x10 < 0x2 EXP 0x40` ASSUME_TAC THENL
  [ TRANS_TAC LET_TRANS `val (len:int64)` THEN
    REWRITE_TAC[VAL_BOUND_64; MOD_LE]; ALL_TAC] THEN

  SUBGOAL_THEN `val (len:int64) MOD 0x10 MOD 0x2 EXP 0x40 = val len MOD 0x10` ASSUME_TAC THENL
  [ MP_TAC (SPECL [`val (len:int64) MOD 0x10`; `0x2 EXP 0x40`] MOD_LT) THEN
    ASM_SIMP_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN

  MP_TAC (SPECL [`val (len:int64)`; `0x2 EXP 0x40`; `val (len:int64) MOD 0x10`]
    (ARITH_RULE `!a b c. c <= a ==> c <= b ==> a + b - c = (a - c) + b`)) THEN
  ANTS_TAC THENL [ REWRITE_TAC[MOD_LE]; ALL_TAC] THEN
  ANTS_TAC THENL [ ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN DISCH_TAC THEN

  MP_TAC (SPECL [`1`; `0x2 EXP 0x40`; `val (len:int64) - val len MOD 0x10`]
    (CONJUNCT1 (CONJUNCT2 (CONJUNCT2 MOD_MULT_ADD)))) THEN
  CONV_TAC NUM_REDUCE_CONV
  );;

(* ********************************************************** *)
(* Properties that we prove about the specification functions *)
(* Similar to the Decrypt ones but specified for Encrypt *)

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

let LENGTH_OF_FST_OF_CIPHER_STEALING = prove(
  `!(block:byte list) (tail:byte list) (tail_len:num)
    (iv:int128) (i:num) (key1:int128 list) (key2:int128 list).
  LENGTH (FST (cipher_stealing_encrypt block tail tail_len iv i key1 key2)) = 16`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[cipher_stealing_encrypt] THEN
  ASM_REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  REWRITE_TAC[LENGTH_OF_INT128_TO_BYTES]
);;

let LENGTH_OF_SND_OF_CIPHER_STEALING = prove(
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
    REWRITE_TAC[LENGTH_OF_FST_OF_CIPHER_STEALING] THEN
    REWRITE_TAC[LENGTH_OF_SND_OF_CIPHER_STEALING]]
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

let BYTES_TO_INT128_OF_INT128_TO_BYTES = prove(
  `!x. bytes_to_int128 (int128_to_bytes x) = x`,
  GEN_TAC THEN
  REWRITE_TAC[int128_to_bytes; bytes_to_int128] THEN
  REWRITE_TAC EL_16_8_CLAUSES THEN
  BITBLAST_TAC
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


let acc_len = new_definition
`acc_len (i:int64) (len:int64) : num =
  if val i * 0x50 + 0x40 = val len then 0x50 * val i + 0x40
  else
    if val i * 0x50 + 0x30 = val len then 0x50 * val i + 0x30
    else
      if val i * 0x50 + 0x20 = val len then 0x50 * val i + 0x20
      else
        if val i * 0x50 + 0x10 = val len then 0x50 * val i + 0x10
        else 0x50 * val i`;;

let VALUE_OF_ACC_LEN = prove(
  `!(i:int64) (len:int64).
    val i * 0x50 <= val len ==>
    val len DIV 0x50 = val i ==>
    0x10 divides val len ==>
    acc_len i len = val len`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[acc_len] THEN
  REPEAT COND_CASES_TAC THENL
  [
    ASM_ARITH_TAC;
    ASM_ARITH_TAC;
    ASM_ARITH_TAC;
    ASM_ARITH_TAC;
    REWRITE_TAC[ARITH_RULE `!a. 0x50 * a = a * 0x50`] THEN
    SUBGOAL_THEN `val (i:int64) * 0x50 = val (len:int64)` ASSUME_TAC THENL
    [ MATCH_MP_TAC (SPECL [`val (len:int64)`; `val (i:int64)`] DIVISION_BY_80_LEMMA) THEN
      REPEAT CONJ_TAC THENL
      [
        ASM_SIMP_TAC[];
        ASM_SIMP_TAC[];
        UNDISCH_TAC `~(val (i:int64) * 0x50 + 0x10 = val (len:int64))` THEN
        UNDISCH_TAC `val (i:int64) * 0x50 <= val (len:int64)` THEN
        ARITH_TAC;
        UNDISCH_TAC `~(val (i:int64) * 0x50 + 0x20 = val (len:int64))` THEN
        UNDISCH_TAC `val (i:int64) * 0x50 <= val (len:int64)` THEN
        ARITH_TAC;
        UNDISCH_TAC `~(val (i:int64) * 0x50 + 0x30 = val (len:int64))` THEN
        UNDISCH_TAC `val (i:int64) * 0x50 <= val (len:int64)` THEN
        ARITH_TAC;
        UNDISCH_TAC `~(val (i:int64) * 0x50 + 0x40 = val (len:int64))` THEN
        UNDISCH_TAC `val (i:int64) * 0x50 <= val (len:int64)` THEN
        ARITH_TAC
      ]; ALL_TAC] THEN
    ASM_ARITH_TAC
  ]
);;

let BOUND_OF_ACC_LEN = prove(
  `!(i:int64) (len:int64) x.
      val i * 0x50 <= val len ==>
      val len DIV 0x50 = val i ==>
      0x10 divides val len ==>
      val len < x ==> acc_len i len < x`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `acc_len i len = val (len:int64)` ASSUME_TAC THENL
  [ MP_TAC (SPECL [`i:int64`; `len:int64`] VALUE_OF_ACC_LEN) THEN
    ASM_SIMP_TAC[]; ALL_TAC] THEN
  ASM_ARITH_TAC
);;

(* For X9 and X10, they stand for i * 0x5 + 4 when number of blocks is divisible by 5. TODO: check for enrypt *)
let acc_blocks = new_definition
`acc_blocks (i:int64) (len:int64) (last:bool) : num =
  if val i * 0x50 + 0x40 = val len then val i * 0x5 + 4
  else
    if val i * 0x50 + 0x30 = val len then val i * 0x5 + 3
    else
      if val i * 0x50 + 0x20 = val len then val i * 0x5 + 2
      else
        if val i * 0x50 + 0x10 = val len then val i * 0x5 + 1
        else
          if last then val i * 0x5 else val i * 0x5 + 4`;;

(* The cipher-stealing invariant is the block read at ctxt_p + curr_len where Cm is being replaced by Pm
   one byte at a time with a decreasing offset i from the beginning of the block.
   Differs from decrypt in that, there, it's curr_len + 16 *)
let cipher_stealing_enc_inv = new_definition
`cipher_stealing_enc_inv (i:num) (curr_len:num) (tail_len:num) (CC:int128) (pt:byte list): int128 =
  bytes_to_int128(
    APPEND (SUB_LIST (0, i) (int128_to_bytes CC))
      (APPEND (SUB_LIST (i, tail_len - i) (SUB_LIST (curr_len, tail_len) pt))
              (SUB_LIST (tail_len, 16 - tail_len) (int128_to_bytes CC))))`;;

(* In the cipher-stealing loop invariant, all bytes remain the same between iterations
   except the current byte i, which is from the corresponding location i in the tail of pt *)
let CIPHER_STEALING_ENC_BYTE_EQUAL = prove(
  `!(i:num) (curr_len:num) (tail_len:int64) (CC:int128) (pt:byte list).
  i < val tail_len /\ val tail_len < 16 ==>
  curr_len + val tail_len = LENGTH pt ==>
  let InvCC = cipher_stealing_enc_inv (i + 1) curr_len (val tail_len) CC pt
  and InvCC' = cipher_stealing_enc_inv i curr_len (val tail_len) CC pt in
  (!j. 0 <= j /\ j < 16 /\ ~(j = i) ==> EL j (int128_to_bytes InvCC) = EL j (int128_to_bytes InvCC')) /\
  EL i (int128_to_bytes InvCC') = word_zx (EL (curr_len + i) pt)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  CONJ_TAC THENL
  [
    REPEAT STRIP_TAC THEN
    REWRITE_TAC[cipher_stealing_enc_inv] THEN
    IMP_REWRITE_TAC[INT128_TO_BYTES_OF_BYTES_TO_INT128] THEN
    REPEAT CONJ_TAC THENL
    [
      (* Three cases: 0 <= j < i, i < j < val tail_len, val tail_len <= j < 16 *)
      ASM_CASES_TAC `j < i` THENL
      [
        SUBGOAL_THEN `j < LENGTH (SUB_LIST (0x0,i + 0x1) (int128_to_bytes CC))` ASSUME_TAC THENL
        [ REWRITE_TAC[LENGTH_SUB_LIST; LENGTH_OF_INT128_TO_BYTES] THEN
          ASM_ARITH_TAC; ALL_TAC] THEN
        SUBGOAL_THEN `j < LENGTH (SUB_LIST (0x0,i) (int128_to_bytes CC))` ASSUME_TAC THENL
        [ REWRITE_TAC[LENGTH_SUB_LIST; LENGTH_OF_INT128_TO_BYTES] THEN
          ASM_ARITH_TAC ; ALL_TAC] THEN
        REWRITE_TAC[EL_APPEND] THEN
        ASM_SIMP_TAC[] THEN
        MP_TAC (ISPECL [`j:num`; `i:num`; `(int128_to_bytes CC):byte list`] EL_SUB_LIST) THEN
        ANTS_TAC THENL
        [ REWRITE_TAC[LENGTH_OF_INT128_TO_BYTES] THEN
          ASM_ARITH_TAC; ALL_TAC ] THEN
        MP_TAC (ISPECL [`j:num`; `(i + 1):num`; `(int128_to_bytes CC):byte list`] EL_SUB_LIST) THEN
        ANTS_TAC THENL
        [ REWRITE_TAC[LENGTH_OF_INT128_TO_BYTES] THEN
          ASM_ARITH_TAC; ALL_TAC ] THEN
        SIMP_TAC[]; ALL_TAC
      ] THEN
      ASM_CASES_TAC `j < val (tail_len:int64)` THENL
      [
        SUBGOAL_THEN `j > i` ASSUME_TAC THENL[ASM_ARITH_TAC; ALL_TAC] THEN
        REWRITE_TAC[EL_APPEND] THEN
        SUBGOAL_THEN `LENGTH (SUB_LIST (0x0,i + 0x1) (int128_to_bytes CC)) = i + 1` SUBST1_TAC THENL
        [ REWRITE_TAC[LENGTH_SUB_LIST; LENGTH_OF_INT128_TO_BYTES] THEN
          ASM_ARITH_TAC; ALL_TAC] THEN
        SUBGOAL_THEN `LENGTH (SUB_LIST (0x0,i) (int128_to_bytes CC)) = i` SUBST1_TAC THENL
        [ REWRITE_TAC[LENGTH_SUB_LIST; LENGTH_OF_INT128_TO_BYTES] THEN
          ASM_ARITH_TAC; ALL_TAC] THEN
        SUBGOAL_THEN `LENGTH (SUB_LIST (i + 0x1,val (tail_len:int64) - (i + 0x1))
                                (SUB_LIST (curr_len,val tail_len) (pt:byte list)))
                        = val tail_len - (i + 1)` SUBST1_TAC THENL
        [ REWRITE_TAC[LENGTH_SUB_LIST; LENGTH_OF_INT128_TO_BYTES] THEN
          ASM_ARITH_TAC; ALL_TAC] THEN
        SUBGOAL_THEN `LENGTH (SUB_LIST (i,val (tail_len:int64) - i)
                              (SUB_LIST (curr_len,val tail_len) (pt:byte list)))
                        = val tail_len - i` SUBST1_TAC THENL
        [ REWRITE_TAC[LENGTH_SUB_LIST; LENGTH_OF_INT128_TO_BYTES] THEN
          ASM_ARITH_TAC; ALL_TAC] THEN
        SUBGOAL_THEN `~(j < i)` ASSUME_TAC THENL
        [ ASM_ARITH_TAC; ALL_TAC] THEN
        SUBGOAL_THEN `~(j < i + 1)` ASSUME_TAC THENL
        [ ASM_ARITH_TAC; ALL_TAC] THEN
        SUBGOAL_THEN `j - i < val (tail_len:int64) - i` ASSUME_TAC THENL
        [ ASM_ARITH_TAC; ALL_TAC] THEN
        SUBGOAL_THEN `j - (i + 1) < val (tail_len:int64) - (i + 1)` ASSUME_TAC THENL
        [ ASM_ARITH_TAC; ALL_TAC] THEN
        ASM_SIMP_TAC[] THEN
        MP_TAC (ISPECL [`(j - i):num`; `i:num`;
          `(SUB_LIST (curr_len,val (tail_len:int64)) (pt:byte list)):byte list`;
          `(val (tail_len:int64) - i):num`] EL_SUB_LIST_SHIFT) THEN
        ASM_SIMP_TAC[] THEN
        ANTS_TAC THENL [ REWRITE_TAC[LENGTH_SUB_LIST] THEN ASM_ARITH_TAC; ALL_TAC] THEN
        IMP_REWRITE_TAC[ARITH_RULE `!i j. j > i ==> j - i - 1 = j - (i + 1)`] THEN
        ASM_ARITH_TAC; ALL_TAC
      ] THEN
      (* j >= val tail_len *)
      REWRITE_TAC[EL_APPEND] THEN
      SUBGOAL_THEN `LENGTH (SUB_LIST (0x0,i + 0x1) (int128_to_bytes CC)) = i + 1` SUBST1_TAC THENL
      [ REWRITE_TAC[LENGTH_SUB_LIST; LENGTH_OF_INT128_TO_BYTES] THEN
        ASM_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `LENGTH (SUB_LIST (0x0,i) (int128_to_bytes CC)) = i` SUBST1_TAC THENL
      [ REWRITE_TAC[LENGTH_SUB_LIST; LENGTH_OF_INT128_TO_BYTES] THEN
        ASM_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `LENGTH (SUB_LIST (i + 0x1,val (tail_len:int64) - (i + 0x1))
                              (SUB_LIST (curr_len,val tail_len) (pt:byte list)))
                      = val tail_len - (i + 1)` SUBST1_TAC THENL
      [ REWRITE_TAC[LENGTH_SUB_LIST; LENGTH_OF_INT128_TO_BYTES] THEN
        ASM_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `LENGTH (SUB_LIST (i,val (tail_len:int64) - i)
                            (SUB_LIST (curr_len,val tail_len) (pt:byte list)))
                      = val tail_len - i` SUBST1_TAC THENL
      [ REWRITE_TAC[LENGTH_SUB_LIST; LENGTH_OF_INT128_TO_BYTES] THEN
        ASM_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `~(j < i)` ASSUME_TAC THENL
      [ ASM_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `~(j < i + 1)` ASSUME_TAC THENL
      [ ASM_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `~(j - i < val (tail_len:int64) - i)` ASSUME_TAC THENL
      [ ASM_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `~(j - (i + 1) < val (tail_len:int64) - (i + 1))` ASSUME_TAC THENL
      [ ASM_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[] THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN
      ASM_ARITH_TAC;

      REWRITE_TAC[LENGTH_APPEND] THEN
      REWRITE_TAC[LENGTH_SUB_LIST] THEN
      REWRITE_TAC[LENGTH_OF_INT128_TO_BYTES] THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      IMP_REWRITE_TAC[ARITH_RULE `i < 16 ==> MIN i 16 = i`] THEN
      SUBGOAL_THEN `LENGTH (pt:byte list) - (curr_len) = val (tail_len:int64)` SUBST1_TAC THENL
      [ ASM_ARITH_TAC; ALL_TAC ] THEN
      REWRITE_TAC[ARITH_RULE `!x. MIN x x = x`] THEN
      ASM_ARITH_TAC;

      REWRITE_TAC[LENGTH_APPEND] THEN
      REWRITE_TAC[LENGTH_SUB_LIST] THEN
      REWRITE_TAC[LENGTH_OF_INT128_TO_BYTES] THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      IMP_REWRITE_TAC[ARITH_RULE `i < 16 ==> MIN (i + 1) 16 = i + 1`] THEN
      SUBGOAL_THEN `LENGTH (pt:byte list) - (curr_len) = val (tail_len:int64)` SUBST1_TAC THENL
      [ ASM_ARITH_TAC; ALL_TAC ] THEN
      REWRITE_TAC[ARITH_RULE `!x. MIN x x = x`] THEN
      ASM_ARITH_TAC
    ] ; ALL_TAC
  ] THEN

  REWRITE_TAC[cipher_stealing_enc_inv] THEN
  IMP_REWRITE_TAC[INT128_TO_BYTES_OF_BYTES_TO_INT128] THEN
  CONJ_TAC THENL [
    REWRITE_TAC[EL_APPEND] THEN
    SUBGOAL_THEN `LENGTH (SUB_LIST (0x0,i) (int128_to_bytes CC)) = i` SUBST1_TAC THENL
    [ REWRITE_TAC[LENGTH_SUB_LIST; LENGTH_OF_INT128_TO_BYTES] THEN
      ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `LENGTH (SUB_LIST (i,val (tail_len:int64) - i)
                          (SUB_LIST (curr_len,val tail_len) (pt:byte list)))
                    = val tail_len - i` SUBST1_TAC THENL
    [ REWRITE_TAC[LENGTH_SUB_LIST; LENGTH_OF_INT128_TO_BYTES] THEN
      ASM_ARITH_TAC; ALL_TAC] THEN
    SIMP_TAC[ARITH_RULE `~(i < i)`; SUB_REFL] THEN
    SUBGOAL_THEN `0 < val (tail_len:int64) - i` ASSUME_TAC THENL
    [ ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN
    MP_TAC (ISPECL [`curr_len:num`; `i:num`; `pt:byte list`;
      `val (tail_len:int64) - i:num`; `val (tail_len:int64)`] SUB_LIST_MIN_GENERAL) THEN
    REWRITE_TAC[ARITH_RULE `!a. MIN a a = a`; GSYM ADD_ASSOC] THEN
    DISCH_THEN (fun th -> (REWRITE_TAC [th])) THEN
    REWRITE_TAC[WORD_ZX_TRIVIAL; EL] THEN
    MATCH_MP_TAC HD_SUB_LIST_CONS_GENERAL THEN
    ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[LENGTH_APPEND] THEN
  REWRITE_TAC[LENGTH_SUB_LIST] THEN
  REWRITE_TAC[LENGTH_OF_INT128_TO_BYTES] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ASM_ARITH_TAC
);;

let CIPHER_STEALING_ENC_INV_SELECT = prove(
 `!(i:num) (curr_len:num) (tail_len:int64) (CC:int128) (pt:byte list).
  i < val tail_len ==> val tail_len < 16 ==>
  curr_len + 16 + (val tail_len) = LENGTH pt ==>
  EL i (int128_to_bytes (cipher_stealing_enc_inv (i + 1) curr_len (val tail_len) CC pt)) =
  EL i (int128_to_bytes CC)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[cipher_stealing_enc_inv] THEN
  IMP_REWRITE_TAC[INT128_TO_BYTES_OF_BYTES_TO_INT128] THEN
  CONJ_TAC THENL [
    SUBGOAL_THEN `LENGTH (SUB_LIST (0x0,i + 1) (int128_to_bytes CC)) <= i + 1` ASSUME_TAC THENL
    [ REWRITE_TAC[LENGTH_SUB_LIST; LENGTH_OF_INT128_TO_BYTES] THEN
      ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[EL_APPEND] THEN
    SUBGOAL_THEN `i < LENGTH (SUB_LIST (0x0,i + 0x1) (int128_to_bytes CC))` ASSUME_TAC THENL
    [ REWRITE_TAC[LENGTH_SUB_LIST; LENGTH_OF_INT128_TO_BYTES] THEN
      ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC EL_SUB_LIST THEN
    REWRITE_TAC[LENGTH_OF_INT128_TO_BYTES] THEN
    ASM_ARITH_TAC; ALL_TAC
  ] THEN

  REWRITE_TAC[LENGTH_APPEND] THEN
  REWRITE_TAC[LENGTH_SUB_LIST] THEN
  REWRITE_TAC[LENGTH_OF_INT128_TO_BYTES] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  IMP_REWRITE_TAC[ARITH_RULE `i < 16 ==> MIN (i + 1) 16 = i + 1`] THEN
  SUBGOAL_THEN `LENGTH (pt:byte list) - (curr_len + 16) = val (tail_len:int64)` SUBST1_TAC THENL
  [ ASM_ARITH_TAC; ALL_TAC ] THEN
  REWRITE_TAC[ARITH_RULE `!x. MIN x x = x`] THEN
  ASM_ARITH_TAC
);;

let CIPHER_STEALING_ENC_INV_SIMP_TAC i =
  ( FIRST_ASSUM (fun th -> MATCH_MP_TAC(SPEC i th)) THEN CONV_TAC NUM_REDUCE_CONV) ORELSE
  ( ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[WORD_RULE `!a b. word_add ((word a):int64) (word b) = word (a + b)`] THEN
    REWRITE_TAC[GSYM ADD_ASSOC] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    IMP_REWRITE_TAC[WORD_ZX_ZX; WORD_ZX_TRIVIAL] THEN
    REWRITE_TAC[DIMINDEX_8; DIMINDEX_32; DIMINDEX_64] THEN
    IMP_REWRITE_TAC[VAL_WORD; DIMINDEX_64; MOD_LT] THEN
    ASM_ARITH_TAC);;

(* TODO: change to match encrypt *)
let TAIL_SWAP_CASE_TAC case =
  let c_tm = `case:num` in
  let v_tm = `v:num` in
  let v = rand (concl (NUM_RED_CONV (subst [case,c_tm] `0x10 + case`))) in
  let r1 = subst [case,c_tm; v,v_tm] `curr_len + 0x10 + case = curr_len + v` in
  let t1 = subst [case,c_tm] `(cipher_stealing_enc_inv case curr_len (val (tail_len:int64)) CC pt):int128` in
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

    MP_TAC (SPECL [case; `curr_len:num`; `tail_len:int64`; `CC:int128`; `pt:byte list`]
      CIPHER_STEALING_ENC_BYTE_EQUAL) THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    STRIP_TAC THEN

    MAP_EVERY (fun i -> CONJ_TAC THENL
      [CIPHER_STEALING_ENC_INV_SIMP_TAC (mk_numeral (num i)); ALL_TAC])
      (0--0xe) THEN
    CIPHER_STEALING_ENC_INV_SIMP_TAC `0xf:num`;

    MP_TAC (SPECL [`pt_ptr:int64`; case; `val (tail_len:int64)`;
      `curr_len:num`; `(int128_to_bytes CC):byte list`; `s5:armstate`]
      BYTE_LIST_AT_SPLIT_BACKWARDS) THEN
    REWRITE_TAC[LENGTH_OF_INT128_TO_BYTES] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    ASM_SIMP_TAC[] THEN
    ANTS_TAC THENL
    [ IMP_REWRITE_TAC[WORD_ZX_ZX] THEN
      REWRITE_TAC[DIMINDEX_8; DIMINDEX_32; DIMINDEX_64] THEN
      MP_TAC (SPECL [case; `curr_len:num`; `tail_len:int64`; `CC:int128`; `pt:byte list`]
        CIPHER_STEALING_ENC_INV_SELECT) THEN
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


let BREAK_DATA_INTO_PARTS = prove(
 `!curr_len (tail_len:int64) (pt_ptr:int64) (s:armstate).
 ((curr_len + 0x10 + val tail_len <= LENGTH bl) /\
  (forall i. i < curr_len
    ==> read (memory :> bytes8 (word_add pt_ptr (word i))) s = EL i bl) /\
  (forall i. i < 16
    ==> read (memory :> bytes8 (word_add (word_add pt_ptr (word curr_len)) (word i))) s =
        EL i (SUB_LIST (curr_len, 16 + val tail_len) bl)) /\
  (forall i. i < val tail_len
    ==> read (memory :> bytes8
          (word_add (word_add pt_ptr (word (curr_len + 0x10))) (word i))) s =
        EL i (SUB_LIST (curr_len + 16, val tail_len) bl))) ==>
  forall i.
     i < curr_len + 0x10 + val tail_len
     ==> read (memory :> bytes8 (word_add pt_ptr (word i))) s = EL i bl`,
  REPEAT GEN_TAC THEN
  DISCH_THEN (CONJUNCTS_THEN2 (LABEL_TAC "H")
    (CONJUNCTS_THEN2 (LABEL_TAC "H1")
      (CONJUNCTS_THEN2 (LABEL_TAC "H2") (LABEL_TAC "H3")))) THEN
  REPEAT STRIP_TAC THEN

  ASM_CASES_TAC `i < curr_len` THENL
  [
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC
  ] THEN

  ASM_CASES_TAC `i < curr_len + 16` THENL
  [
    USE_THEN "H2" (fun th -> MP_TAC (SPEC `i - curr_len` th)) THEN
    REMOVE_THEN "H2" (K ALL_TAC) THEN
    SUBGOAL_THEN `(word_add (word_add (pt_ptr:int64) (word curr_len)) (word (i - curr_len)))
      = (word_add pt_ptr (word i))` ASSUME_TAC THENL
    [ REWRITE_TAC[WORD_RULE `word_add (word_add a (word b)) (word c) = word_add a (word (b + c))`] THEN
      AP_TERM_TAC THEN AP_TERM_TAC THEN
      ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    ANTS_TAC THENL[ASM_ARITH_TAC; ALL_TAC] THEN
    SIMP_TAC[] THEN DISCH_TAC THEN
    IMP_REWRITE_TAC[EL_SUB_LIST_GENERAL] THEN
    ASM_ARITH_TAC;
    ALL_TAC
  ] THEN

  ASM_CASES_TAC `i < curr_len + 16 + val (tail_len:int64)` THENL
  [
    USE_THEN "H3" (fun th -> MP_TAC (SPEC `i - curr_len - 16` th)) THEN
    REMOVE_THEN "H3" (K ALL_TAC) THEN
    SUBGOAL_THEN `(word_add (word_add (pt_ptr:int64) (word (curr_len + 0x10)))
       (word (i - curr_len - 0x10))) = (word_add pt_ptr (word i))` ASSUME_TAC THENL
    [ REWRITE_TAC[WORD_RULE `word_add (word_add a (word b)) (word c) = word_add a (word (b + c))`] THEN
      AP_TERM_TAC THEN AP_TERM_TAC THEN
      ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    ANTS_TAC THENL[ASM_ARITH_TAC; ALL_TAC] THEN
    SIMP_TAC[] THEN DISCH_TAC THEN
    REWRITE_TAC[ARITH_RULE `i - curr_len - 16 = i - (curr_len + 16)`] THEN
    IMP_REWRITE_TAC[EL_SUB_LIST_GENERAL] THEN
    ASM_ARITH_TAC;
    ALL_TAC
  ] THEN

  ASM_ARITH_TAC
);;

(* ************************************** *)
(* Assembly proofs *)

(* Proof: Cipher stealing *)
let CIPHER_STEALING_ENC_CORRECT = time prove(
  `!ptxt_p ctxt_p len key1_p
    pt_in iv tail_len len_full_blocks num_5_blocks
    k1_0 k1_1 k1_2 k1_3 k1_4 k1_5 k1_6 k1_7 k1_8 k1_9 k1_10 k1_11 k1_12 k1_13 k1_14
    pc.
    PAIRWISE nonoverlapping
    [(word pc, LENGTH aes256_xts_encrypt_mc);
    (ptxt_p, val len);
    (ctxt_p, val len);
    (key1_p, 244)] /\
    val len >= 16 /\ val len <= 2 EXP 24 /\ LENGTH pt_in = val len /\
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
         // read X3 s = key1_p /\
         read X21 s = tail_len /\
         read Q6 s = calculate_tweak (acc_blocks num_5blocks len_full_blocks true) iv key2_lst /\
         read X19 s = word 0x87 /\
         read Q16 s = k1_0 /\ read Q17 s = k1_1 /\ read Q12 s = k1_2 /\ read Q13 s = k1_3 /\
         read Q14 s = k1_4 /\ read Q15 s = k1_5 /\ read Q4 s = k1_6 /\ read Q5 s = k1_7 /\
         read Q18 s = k1_8 /\ read Q19 s = k1_9 /\ read Q20 s = k1_10 /\ read Q21 s = k1_11 /\
         read Q22 s = k1_12 /\ read Q23 s = k1_13 /\ read Q7 s = k1_14 /\ byte_list_at pt_in ptxt_p len s /\
         byte_list_at pt_in ptxt_p len s /\
         byte_list_at (aes256_xts_encrypt pt_in (acc_len num_5blocks len_full_blocks) iv key1_lst key2_lst)
         ctxt_p (word (acc_len num_5blocks len_full_blocks)) s)
    (\s.
        read PC s = word (pc + LENGTH aes256_xts_encrypt_mc - 8*4) /\
        byte_list_at (aes256_xts_encrypt pt_in (val len) iv key1_lst key2_lst) ctxt_p len s )
    ( MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI,,
      MAYCHANGE [X19; X20; X21; X22] ,,
      MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
      MAYCHANGE [memory :> bytes (ctxt_p,val len)])
    `,
  REWRITE_TAC [(REWRITE_CONV [aes256_xts_encrypt_mc] THENC LENGTH_CONV) `LENGTH aes256_xts_encrypt_mc`] THEN
  REWRITE_TAC[byte_list_at; NONOVERLAPPING_CLAUSES; PAIRWISE; ALL;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REPEAT STRIP_TAC THEN

  (* Prove the bounds on len_full_blocks, num_5blocks and len and their relationships *)
  SUBGOAL_THEN `~(val (len_full_blocks:int64) < 0x10)` ASSUME_TAC THENL
  [ SUBGOAL_THEN `~(val (len:int64) < 0x10)` MP_TAC THENL
    [ASM_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `word_and len (word 0xfffffffffffffff0) = (len_full_blocks:int64)` THEN
    MP_TAC (SPECL [`len:int64`; `len_full_blocks:int64`] LEN_FULL_BLOCKS_LO_BOUND_1BLOCK_THM) THEN
    SIMP_TAC[]; ALL_TAC] THEN

  SUBGOAL_THEN `val (len_full_blocks:int64) <= 0x2 EXP 24` ASSUME_TAC THENL
  [ UNDISCH_TAC `val (len:int64) <= 0x2 EXP 24` THEN
    UNDISCH_TAC `word_and len (word 0xfffffffffffffff0) = (len_full_blocks:int64)` THEN
    MP_TAC (SPECL [`len:int64`; `len_full_blocks:int64`] LEN_FULL_BLOCKS_HI_BOUND_THM) THEN
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
  [ EXPAND_TAC "len_full_blocks" THEN SIMP_TAC[LEN_FULL_BLOCKS_LT_LEN_THM]; ALL_TAC] THEN

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
    REWRITE_TAC[LEN_FULL_BLOCKS_TO_VAL] THEN
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

  (* The cipher stealing branch *)
  (* The byte-swap needs another invariant proof. *)
  ABBREV_TAC `curr_len = (acc_len (num_5blocks:int64) (len_full_blocks:int64)):num` THEN
  ABBREV_TAC `curr_blocks = (acc_blocks (num_5blocks:int64) (len_full_blocks:int64) T):num` THEN

  SUBGOAL_THEN `curr_len <= val (len:int64)` ASSUME_TAC THENL (* differs from decrypt *)
  [ EXPAND_TAC "curr_len" THEN
    MP_TAC (SPECL [`num_5blocks:int64`; `len_full_blocks:int64`] VALUE_OF_ACC_LEN) THEN
    REPEAT_N 3 (ANTS_TAC THENL [ASM_ARITH_TAC ORELSE ASM_SIMP_TAC[]; ALL_TAC]) THEN
    SIMP_TAC[] THEN DISCH_TAC THEN
    ASM_SIMP_TAC[]; ALL_TAC ] THEN

  SUBGOAL_THEN `val ((word curr_len):int64) = curr_len` ASSUME_TAC THENL
  [ IMP_REWRITE_TAC[VAL_WORD; DIMINDEX_64; MOD_LT] THEN
    EXPAND_TAC "curr_len" THEN
    MP_TAC (SPECL [`num_5blocks:int64`; `len_full_blocks:int64`; `2 EXP 64`]
      BOUND_OF_ACC_LEN) THEN
    REPEAT_N 4 (ANTS_TAC THENL [ASM_ARITH_TAC ORELSE ASM_SIMP_TAC[]; ALL_TAC]) THEN
    SIMP_TAC[]; ALL_TAC] THEN

  SUBGOAL_THEN `curr_len >= 16` ASSUME_TAC THENL
  [ REWRITE_TAC[GSYM (ASSUME `acc_len num_5blocks len_full_blocks = curr_len`)] THEN
    MP_TAC (SPECL [`num_5blocks:int64`; `len_full_blocks:int64`] VALUE_OF_ACC_LEN) THEN
    REPEAT_N 3 (ANTS_TAC THENL [ASM_ARITH_TAC ORELSE ASM_SIMP_TAC[]; ALL_TAC]) THEN
    SIMP_TAC[] THEN DISCH_TAC THEN
    UNDISCH_TAC `word_add (tail_len:int64) (len_full_blocks:int64) = len` THEN
    ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
    REWRITE_TAC[VAL_WORD_ADD;DIMINDEX_64] THEN
    IMP_REWRITE_TAC[MOD_LT] THEN
    ASM_ARITH_TAC; ALL_TAC ] THEN

  SUBGOAL_THEN `16 * curr_blocks = curr_len` ASSUME_TAC THENL
  [ REWRITE_TAC[GSYM (ASSUME `acc_len num_5blocks len_full_blocks = curr_len`)] THEN (* put in tips doc*)
    (* or UNDISCH_THEN `acc_len (num_5blocks:int64) (len_full_blocks:int64) = curr_len`
        (fun th -> REWRITE_TAC[GSYM th]) THEN *)
    EXPAND_TAC "curr_blocks" THEN
    REWRITE_TAC[acc_len; acc_blocks] THEN
    REPEAT_N 4 (COND_CASES_TAC THENL [SIMP_TAC[] THEN ARITH_TAC; ALL_TAC] THEN SIMP_TAC[]) THEN
    ARITH_TAC; ALL_TAC ] THEN

  ABBREV_TAC `CC = aes256_xts_encrypt_round
    (bytes_to_int128 (SUB_LIST (curr_len-0x10,0x10) (pt_in:byte list)))
    (calculate_tweak (curr_blocks-0x1) (iv:int128) (key2_lst:int128 list))
    (key1_lst:int128 list)` THEN

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
        ( read X0 s = word_add ptxt_p (word curr_len) /\
          read X1 s = word_sub (word_add ctxt_p (word curr_len)) (word 0x10) /\
          read X13 s = word_add ctxt_p (word curr_len) /\
          read X20 s = word_add ptxt_p (word curr_len) /\
          read X21 s = (word i):int64 /\
          read Q6 s = calculate_tweak curr_blocks iv key2_lst /\
          read Q16 s = k1_0 /\ read Q17 s = k1_1 /\ read Q12 s = k1_2 /\ read Q13 s = k1_3 /\
          read Q14 s = k1_4 /\ read Q15 s = k1_5 /\ read Q4 s = k1_6 /\ read Q5 s = k1_7 /\
          read Q18 s = k1_8 /\ read Q19 s = k1_9 /\ read Q20 s = k1_10 /\ read Q21 s = k1_11 /\
          read Q22 s = k1_12 /\ read Q23 s = k1_13 /\ read Q7 s = k1_14 /\
          byte_list_at pt_in ptxt_p len s /\
          byte_list_at (aes256_xts_encrypt pt_in curr_len iv key1_lst key2_lst)
                          ctxt_p (word curr_len) s /\
          // Contents of CC at each i
          read (memory :> bytes128 (word_sub (word_add ctxt_p (word curr_len)) (word 0x10))) s =
            cipher_stealing_enc_inv i curr_len (val (tail_len:int64)) CC pt_in /\

          // bytes of Cm at offset i to (tail_len -i) in CC
          // are stored at their final location in ciphertext in the tail part
          // they're copied from CC before they're overwritten by bytes from Pm
          byte_list_at (SUB_LIST (i, val tail_len - i) (int128_to_bytes CC))
            (word_add ctxt_p (word (curr_len + i)))
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
    UNDISCH_THEN `val ((word curr_len):int64) = curr_len`
        (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th]
        THEN ASSUME_TAC th) THEN (* put in tips doc: keep the assumption *)

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
 read (memory :>  bytes128 (word_sub (word_add ctxt_p (word curr_len)) (word 0x10))) s5
 = cipher_stealing_enc_inv (val tail_len) curr_len (val tail_len) CC pt_in /\
 (forall i.
      i < val (word 0x0)
      ==> read (memory :> bytes8 (word_add (word_add ctxt_p (word (curr_len + val tail_len)))
                                           (word i))) s5
          =  EL i (SUB_LIST (val tail_len,0x0) (int128_to_bytes CC)))` *) (* 4 total *)
    REPEAT CONJ_TAC THENL
    [
      REWRITE_TAC[WORD_VAL];

   (* `read (memory :> bytes128 (word_sub (word_add ctxt_p (word curr_len)) (word 0x10))) s5
     = cipher_stealing_enc_inv (val tail_len) curr_len (val tail_len) CC pt_in` *)
      REWRITE_TAC[cipher_stealing_enc_inv; SUB_REFL] THEN
      SUBGOAL_THEN `SUB_LIST (val (tail_len:int64),0x0) (SUB_LIST (curr_len,val tail_len) (pt_in:byte list)) = []` SUBST1_TAC THENL
      [ REWRITE_TAC[SUB_LIST_CLAUSES]; ALL_TAC] THEN
      REWRITE_TAC[CONJUNCT1 APPEND] THEN
      SUBGOAL_THEN `APPEND (SUB_LIST (0x0,val (tail_len:int64)) (int128_to_bytes CC))
        (SUB_LIST (val tail_len,0x10 - val tail_len) (int128_to_bytes CC)) =
        (int128_to_bytes CC)` SUBST1_TAC THENL
      [ MP_TAC (ISPECL [`int128_to_bytes CC`; `val (tail_len:int64)`; `16 - val (tail_len:int64)`; `0`] (GSYM SUB_LIST_SPLIT)) THEN
        IMP_REWRITE_TAC[ADD_CLAUSES; ARITH_RULE `!x. x < 16 ==> x + 16 - x = 16`] THEN
        DISCH_TAC THEN
        IMP_REWRITE_TAC[SUB_LIST_LENGTH_IMPLIES; LENGTH_OF_INT128_TO_BYTES]
        ; ALL_TAC] THEN
      REWRITE_TAC[BYTES_TO_INT128_OF_INT128_TO_BYTES] THEN
    (* `read (memory :> bytes128 (word_sub (word_add ctxt_p (word curr_len)) (word 0x10))) s5
       = CC` *)
      (* Apply READ_CT_LAST_LEMMA with proper arguments *)
      MP_TAC (SPECL [`ctxt_p:int64`; `curr_len - 16:num`; `word curr_len:int64`;
        `aes256_xts_encrypt pt_in curr_len iv key1_lst key2_lst:byte list`; `s5:armstate`] READ_CT_LAST_LEMMA) THEN
      UNDISCH_THEN `val ((word curr_len):int64) = curr_len`
        (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th] THEN ASSUME_TAC th) THEN
      ASM_SIMP_TAC[] THEN
    (*  `(curr_len - 0x10 + 0x10 <= curr_len /\
          LENGTH (aes256_xts_encrypt pt_in curr_len iv key1_lst key2_lst) = curr_len
          ==> read (memory :> bytes128 (word_add ctxt_p (word (curr_len - 0x10)))) s5 =
              bytes_to_int128 (SUB_LIST (curr_len - 0x10,0x10)
                              (aes256_xts_encrypt pt_in curr_len iv key1_lst key2_lst)))
        ==> read (memory :> bytes128 (word_sub (word_add ctxt_p (word curr_len)) (word 0x10))) s5
            = CC` *)
      ANTS_TAC THENL (* 6 total *)
      [ CONJ_TAC THENL  (* 7 total *)
        [ UNDISCH_TAC `curr_len >= 0x10` THEN ARITH_TAC;

      (* `LENGTH (aes256_xts_encrypt pt_in curr_len iv key1_lst key2_lst) = curr_len`*)
          REWRITE_TAC[GSYM (ASSUME `0x10 * curr_blocks = curr_len`); LENGTH_OF_AES256_XTS_ENCRYPT_FULL_BLOCKS] ]
      ; ALL_TAC ] THEN

      SUBGOAL_THEN `(word_sub (word_add (ctxt_p:int64) (word curr_len)) (word 0x10))
                    = (word_add ctxt_p (word (curr_len - 0x10)))` SUBST1_TAC THENL
      [ REWRITE_TAC[WORD_SUB] THEN
        ASM_SIMP_TAC[ARITH_RULE `curr_len >= 0x10 ==> 0x10 <= curr_len`] THEN
        WORD_ARITH_TAC
      ; ALL_TAC] THEN
      DISCH_THEN (fun th -> REWRITE_TAC[th]) THEN
      (* `bytes_to_int128 (SUB_LIST (curr_len - 0x10,0x10)
                          (aes256_xts_encrypt pt_in curr_len iv key1_lst key2_lst))
          = CC`. *)
      (* Try proving the subgoal by expanding out aes256_xts_encrypt and then apply related LENGTH_OF_xxx and SUB_LIST_xxx lemmas *)
      REWRITE_TAC[aes256_xts_encrypt] THEN
      IMP_REWRITE_TAC[ARITH_RULE `curr_len >= 0x10 ==> ~(curr_len < 0x10)`] THEN
      SUBGOAL_THEN `curr_len MOD 0x10 = 0` SUBST1_TAC THENL
      [ REWRITE_TAC[GSYM (ASSUME `0x10 * curr_blocks = curr_len`); MOD_MULT] ; ALL_TAC ] THEN
      CONV_TAC (DEPTH_CONV let_CONV) THEN
      REWRITE_TAC[SUB_0] THEN
      COND_CASES_TAC THENL
      [ (* curr_len DIV 0x10 < 0x2 *)
        EXPAND_TAC "CC" THEN
        MP_TAC (SPECL [`0:num`; `0x0:num`; `pt_in:byte list`; `iv:int128`;
                         `key1_lst:int128 list`; `key2_lst:int128 list`]
                LENGTH_OF_AES256_XTS_ENCRYPT_TAIL) THEN
        CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN

        SUBGOAL_THEN `curr_len = 0x10` ASSUME_TAC THENL
        [ UNDISCH_TAC `curr_len >= 0x10` THEN
          UNDISCH_TAC `curr_len DIV 0x10 < 0x2` THEN
          REWRITE_TAC[GSYM (ASSUME `0x10 * curr_blocks = curr_len`)] THEN
          SIMP_TAC[ARITH_RULE `(0x10 * curr_blocks) DIV 0x10 = curr_blocks`] THEN
          (* or SIMP_TAC[DIV_MULT; ARITH] THEN *)
          ARITH_TAC
        ; ALL_TAC ] THEN
        REWRITE_TAC[ASSUME `curr_len = 0x10`; SUB_REFL] THEN

        SUBGOAL_THEN `curr_blocks = 0x1` ASSUME_TAC THENL
        [ UNDISCH_TAC `0x10 * curr_blocks = curr_len` THEN
          REWRITE_TAC[ASSUME `curr_len = 0x10`] THEN
          ARITH_TAC
        ; ALL_TAC ] THEN
        REWRITE_TAC[ASSUME `curr_blocks = 0x1`; SUB_REFL] THEN

        SIMP_TAC[ASSUME `LENGTH (aes256_xts_encrypt_tail 0x0 0x0 pt_in iv key1_lst key2_lst) = 0x10`;
                 SUB_LIST_LENGTH_IMPLIES] THEN

        REWRITE_TAC[AES256_XTS_ENCRYPT_TAIL_WHEN_1BLOCK] THEN
        SIMPLE_ARITH_TAC
      ; ALL_TAC ] THEN

      (* ~(curr_len DIV 0x10 < 0x2) *)
      SUBGOAL_THEN `curr_blocks >= 2` ASSUME_TAC THENL
      [ UNDISCH_TAC `~(curr_len DIV 0x10 < 0x2)` THEN
        UNDISCH_TAC `0x10 * curr_blocks = curr_len` THEN
        ARITH_TAC
      ; ALL_TAC] THEN
      SUBGOAL_THEN `curr_len DIV 0x10 = curr_blocks` ASSUME_TAC THENL
      [ UNDISCH_TAC `0x10 * curr_blocks = curr_len` THEN
        ARITH_TAC
      ; ALL_TAC] THEN
      POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th]) THEN

      MP_TAC (SPECL [`0`;`(curr_blocks - 2):num`; `pt_in:byte list`; `iv:int128`;
                     `key1_lst:int128 list`; `key2_lst:int128 list`]
              LENGTH_OF_AES256_XTS_ENCRYPT_REC) THEN
      ASM_SIMP_TAC[ARITH_RULE `curr_blocks >= 0x2 ==> ~(curr_blocks - 0x2 < 0x0)`] THEN
      IMP_REWRITE_TAC[SUB_0; ARITH_RULE `curr_blocks >= 0x2 ==> curr_blocks - 2 + 1 = curr_blocks -1`] THEN
      IMP_REWRITE_TAC[ARITH_RULE `0x10 * curr_blocks = curr_len ==> (curr_blocks - 0x1) * 0x10 = curr_len - 0x10`] THEN
      DISCH_TAC THEN
      IMP_REWRITE_TAC[SUB_LIST_APPEND_RIGHT_LEMMA] THEN
    (* `bytes_to_int128 (SUB_LIST (0x0,0x10) (aes256_xts_encrypt_tail (curr_blocks - 0x1) 0x0 pt_in iv key1_lst key2_lst))
        = CC`*)
      MP_TAC (SPECL [`(curr_blocks - 0x1):num`; `0x0:num`; `pt_in:byte list`; `iv:int128`;
                        `key1_lst:int128 list`; `key2_lst:int128 list`]
               LENGTH_OF_AES256_XTS_ENCRYPT_TAIL) THEN
      CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
      ASM_SIMP_TAC[SUB_LIST_LENGTH_IMPLIES] THEN
      REWRITE_TAC[AES256_XTS_ENCRYPT_TAIL_WHEN_1BLOCK] THEN
      EXPAND_TAC "CC" THEN
      IMP_REWRITE_TAC[ARITH_RULE `0x10 * curr_blocks = curr_len ==> (curr_blocks - 0x1) * 0x10 = curr_len - 0x10`];

    (* `forall i.
          i < val (word 0x0)
          ==> read (memory :> bytes8 (word_add (word_add ctxt_p (word (curr_len + val tail_len)))
                                      (word i))) s5
              = EL i (SUB_LIST (val tail_len,0x0) (int128_to_bytes CC))`*)
      REWRITE_TAC[VAL_WORD_0] THEN ARITH_TAC
    ];

    (* Subgoal 3: inductive step *)
    REPEAT STRIP_TAC THEN

    (* For non-overlapping and MAYCHANGE address reasoning *)
    SUBGOAL_THEN `curr_len + i < val (len:int64)` ASSUME_TAC THENL
    [ REWRITE_TAC[GSYM (ASSUME `acc_len num_5blocks len_full_blocks = curr_len`)] THEN
      MP_TAC (SPECL [`num_5blocks:int64`; `len_full_blocks:int64`] VALUE_OF_ACC_LEN) THEN
      REPEAT_N 3 (ANTS_TAC THENL [ASM_ARITH_TAC ORELSE ASM_SIMP_TAC[]; ALL_TAC]) THEN
      SIMP_TAC[] THEN DISCH_TAC THEN

      UNDISCH_TAC `word_add (tail_len:int64) (len_full_blocks:int64) = len` THEN
      UNDISCH_TAC `i < val (tail_len:int64)` THEN

      ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
      REWRITE_TAC[VAL_WORD_ADD;DIMINDEX_64] THEN
      IMP_REWRITE_TAC[MOD_LT] THEN
      ASM_ARITH_TAC ; ALL_TAC ] THEN


    SUBGOAL_THEN `curr_len >= 16` ASSUME_TAC THENL
    [
      REWRITE_TAC[GSYM (ASSUME `acc_len num_5blocks len_full_blocks = curr_len`)] THEN
      MP_TAC (SPECL [`num_5blocks:int64`; `len_full_blocks:int64`] VALUE_OF_ACC_LEN) THEN
      REPEAT_N 3 (ANTS_TAC THENL [ASM_ARITH_TAC ORELSE ASM_SIMP_TAC[]; ALL_TAC]) THEN
      SIMP_TAC[] THEN DISCH_TAC THEN
      UNDISCH_TAC `word_add (tail_len:int64) (len_full_blocks:int64) = len` THEN
      ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
      REWRITE_TAC[VAL_WORD_ADD;DIMINDEX_64] THEN
      IMP_REWRITE_TAC[MOD_LT] THEN
      ASM_ARITH_TAC; ALL TAC ] THEN

    SUBGOAL_THEN `(word_add (word_add (ctxt_p:int64) (word_sub (word curr_len) (word 0x10))) (word i)) =
      word_add (ctxt_p:int64) (word (curr_len - 0x10 + i))` ASSUME_TAC THEN
    REWRITE_TAC[GSYM WORD_ADD_ASSOC] THEN
    AP_TERM_TAC THEN
    REWRITE_TAC[WORD_ADD;WORD_SUB] THEN
    ASM_ARITH_TAC THEN


    MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN
    EXISTS_TAC `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
        MAYCHANGE [X19; X20; X21; X22],,
        MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15],,
        MAYCHANGE [memory :> bytes8 (word_add ctxt_p (word (curr_len - 0x10 + i)))],,
        MAYCHANGE [memory :> bytes8 (word_add ctxt_p (word (curr_len + i)))]` THEN
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



    ARM_ACCSTEPS_TAC AES256_XTS_ENCRYPT_EXEC [] (1--5) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
  ]

);;

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
       MAYCHANGE SOME_FLAGS,,
       MAYCHANGE [events],,
       MAYCHANGE [memory :> bytes(ctxt_p, val len)])`,

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

  (* Prove the bounds on len_full_blocks, num_5blocks and len and their relationships *)
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

  SUBGOAL_THEN `val (len_full_blocks:int64) <= val (len:int64)` ASSUME_TAC THENL
  [ EXPAND_TAC "len_full_blocks" THEN SIMP_TAC[LEN_FULL_BLOCKS_LT_LEN_THM]; ALL_TAC] THEN

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

  (* Prove property until right before cipher stealing *)
  ENSURES_SEQUENCE_TAC `pc + 0x9e0`
  `\s.
      read X0 s = word_add ptxt_p (word (acc_len num_5blocks len_full_blocks)) /\
      read X1 s = word_add ctxt_p (word (acc_len num_5blocks len_full_blocks)) /\
      read X21 s = tail_len /\
      read Q6 s = calculate_tweak (acc_blocks num_5blocks len_full_blocks T) iv key2_lst /\
      read X19 s = word 0x87 /\
      read X10 s = word_subword (calculate_tweak (acc_blocks num_5blocks len_full_blocks F) iv key2_lst) (64,64) /\
      read X9 s = word_zx (calculate_tweak (acc_blocks num_5blocks len_full_blocks F) iv key2_lst) /\
      read Q16 s = k1_0 /\ read Q17 s = k1_1 /\ read Q12 s = k1_2 /\ read Q13 s = k1_3 /\
      read Q14 s = k1_4 /\ read Q15 s = k1_5 /\ read Q4 s = k1_6 /\ read Q5 s = k1_7 /\
      read Q18 s = k1_8 /\ read Q19 s = k1_9 /\ read Q20 s = k1_10 /\ read Q21 s = k1_11 /\
      read Q22 s = k1_12 /\ read Q23 s = k1_13 /\ read Q7 s = k1_14 /\
      byte_list_at pt_in ptxt_p len s /\
      byte_list_at (aes256_xts_encrypt pt_in (acc_len num_5blocks len_full_blocks) iv key1_lst key2_lst)
                  ctxt_p (word (acc_len num_5blocks len_full_blocks)) s` THEN
  CONJ_TAC THENL
  [

  (* Main Loop invariant *)
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
          [ EXPAND_TAC "len_full_blocks" THEN SIMP_TAC[LEN_FULL_BLOCKS_LT_LEN_THM]; ALL_TAC ] THEN
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
      EXISTS_TAC `MAYCHANGE
          [PC; X0; X1; X2; X4; X6; X7; X8; X9; X10; X11; X19; X20; X21; X22] ,,
        MAYCHANGE [Q0; Q1; Q4; Q5; Q6; Q7; Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15; Q16; Q17;
          Q18; Q19; Q20; Q21; Q22; Q23; Q24; Q25; Q26] ,,
        MAYCHANGE [NF; ZF; CF; VF] ,,
        MAYCHANGE [events] ,,
        MAYCHANGE [memory :> bytes128 (word_add ctxt_p (word (0x50 * i)));
                    memory :> bytes128 (word_add ctxt_p (word (0x50 * i + 0x10)));
                    memory :> bytes128 (word_add ctxt_p (word (0x50 * i + 0x20)));
                    memory :> bytes128 (word_add ctxt_p (word (0x50 * i + 0x30)));
                    memory :> bytes128 (word_add ctxt_p (word (0x50 * i + 0x40)))]` THEN
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
      MP_TAC (SPECL [`ptxt_p:int64`; `i:num`; `len:int64`; `pt_in:byte list`; `s0:armstate`] READ_CT_LEMMA) THEN
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
      EXISTS_TAC `//MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
          //MAYCHANGE [X19; X20; X21; X22],,
          //MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15],,
          MAYCHANGE [PC; X0; X1; X2; X4; X6; X7; X8; X9; X10; X11; X19; X20; X21; X22] ,,
          MAYCHANGE [Q0; Q1; Q4; Q5; Q6; Q7; Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15; Q16; Q17;
                     Q18; Q19; Q20; Q21; Q22; Q23; Q24; Q25; Q26] ,,
          MAYCHANGE [NF; ZF; CF; VF] ,,
          MAYCHANGE [events] ,,
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
      (* REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN *)
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
        MP_TAC (SPECL [`ptxt_p:int64`; `num_5blocks:int64`; `len:int64`; `pt_in:byte list`; `s3:armstate`] READ_CT_TAIL4_LEMMA) THEN
        ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN

        (* Assumptions that help with reasoning about nonoverlapping
         so that the universally quantified assumption stays.
         See: https://hol-light.zulipchat.com/#narrow/channel/474190-s2n-bignum/topic/.E2.9C.94.20Symbolic.20simulation.20removed.20assumption/with/541554894 *)
        (*SUBGOAL_THEN `0x50 * (val (num_5blocks:int64)) < 0x2 EXP 0x40` ASSUME_TAC THENL
        [ UNDISCH_TAC `val (num_5blocks:int64) * 0x50 <= val (len_full_blocks:int64)` THEN
          UNDISCH_TAC `val (len_full_blocks:int64) <= 0x2 EXP 0x18` THEN
          ARITH_TAC; ALL_TAC] THEN
        SUBGOAL_THEN `val ((word (0x50 * val (num_5blocks:int64))):int64) = 0x50 * val num_5blocks` ASSUME_TAC THENL [
          IMP_REWRITE_TAC[VAL_WORD; DIMINDEX_64; MOD_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
        POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN *)

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

        ARM_ACCSTEPS_TAC AES256_XTS_ENCRYPT_EXEC [] (128--129) THEN (* Store 4 blocks in ctxt_p *)
        ARM_ACCSTEPS_TAC AES256_XTS_ENCRYPT_EXEC [] (130--137) THEN (* Calculate tweak *)
        TWEAK_TAC `Q6:(armstate,int128)component` `val (num_5blocks:int64) * 0x5 + 0x4` `val (num_5blocks:int64) * 0x5 + 0x3` THEN

        (* TODO: Still have the same problem *)
        ARM_ACCSTEPS_TAC AES256_XTS_ENCRYPT_EXEC [] (138--138) THEN
        ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
        REPEAT CONJ_TAC THENL (* 7 subgoals (9 total) *)
        [
          REWRITE_TAC[acc_len] THEN ASM_SIMP_TAC[] THEN CONV_TAC WORD_RULE;
          REWRITE_TAC[acc_len] THEN ASM_SIMP_TAC[] THEN CONV_TAC WORD_RULE;
          REWRITE_TAC[acc_blocks] THEN ASM_SIMP_TAC[] THEN CONV_TAC WORD_RULE;
          REWRITE_TAC[acc_blocks] THEN ASM_SIMP_TAC[] THEN CONV_TAC WORD_RULE;
          REWRITE_TAC[acc_blocks] THEN ASM_SIMP_TAC[] THEN CONV_TAC WORD_RULE; (* 4 total *)
(*
`forall i.
     i < val (word (acc_len num_5blocks len_full_blocks))
     ==> read (memory :> bytes8 (word_add ctxt_p (word i))) s138 =
         EL i
         (aes256_xts_encrypt pt_in (acc_len num_5blocks len_full_blocks) iv
          key1_lst
         key2_lst)`
*)
          REWRITE_TAC[acc_len] THEN ASM_SIMP_TAC[LE_REFL] THEN
          SUBGOAL_THEN `val ((word (0x50 * val (num_5blocks:int64) + 0x40)):int64) =
            0x50 * val num_5blocks + 0x40` ASSUME_TAC THENL
          [ IMP_REWRITE_TAC[VAL_WORD; MOD_LT; DIMINDEX_64] THEN
            UNDISCH_TAC `val (num_5blocks:int64) * 0x50 + 0x40 <= val (len:int64)` THEN
            UNDISCH_TAC `val (len:int64) <= 0x2 EXP 0x18` THEN
            ARITH_TAC; ALL_TAC] THEN
          CHANGED_TAC (POP_ASSUM(fun th -> REWRITE_TAC[th])) THEN
(*
`forall i.
     i < 0x50 * val num_5blocks + 0x40
     ==> read (memory :> bytes8 (word_add ctxt_p (word i))) s138 =
         EL i
         (aes256_xts_encrypt pt_in (0x50 * val num_5blocks + 0x40) iv
          key1_lst
         key2_lst)`
*)
          (* TODO: Manually add the assumption as a temporary fix to:
                    the symbolic simulation only contained results for 0th 1st and 3rd blocks,
                    but doesn't have 2nd *)
          SUBGOAL_THEN `read
          (memory :>
            bytes128
            (word_add (ctxt_p:int64) (word (0x50 * val (num_5blocks:int64) + 0x20))))
            s138 =
          aes256_xts_encrypt_round
            (bytes_to_int128
              (SUB_LIST (val num_5blocks * 0x50 + 0x20,0x10) pt_in))
            (calculate_tweak (val num_5blocks * 0x5 + 0x2) iv key2_lst)
            key1_lst` ASSUME_TAC THENL [CHEAT_TAC; ALL_TAC] THEN
          (* TODO: ??? *)
          CHANGED_TAC(RULE_ASSUM_TAC(REWRITE_RULE
          [WORD_RULE `(word_add (word_add ctxt_p (word (0x50 * val num_5blocks)))
              (word 0x30)) = (word_add (ctxt_p:int64) (word (0x50 * val (num_5blocks:int64) + 0x30)))`])) THEN

          (* Remove quantifier in conclusion then in antecedent of the goal:
           ==> (forall i.
          i < 0x50 * val num_5blocks
             ==> read (memory :> bytes8 (word_add ctxt_p (word i))) s138 =
              EL i
              (aes256_xts_encrypt pt_in (val num_5blocks * 0x50) iv key1_lst
              key2_lst))
          ==> (forall i.
              i < 0x50 * val num_5blocks + 0x40
              ==> read (memory :> bytes8 (word_add ctxt_p (word i))) s138 =
                  EL i
                  (aes256_xts_encrypt pt_in (0x50 * val num_5blocks + 0x40) iv
                  key1_lst
                  key2_lst))`
             *)
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
(*
`(forall i.
      i < 0x50 * val num_5blocks
      ==> read (memory :> bytes8 (word_add ctxt_p (word i))) s138 =
          EL i
          (aes256_xts_encrypt pt_in (val num_5blocks * 0x50) iv key1_lst
          key2_lst))
 ==> read (memory :> bytes (ctxt_p,0x50 * val num_5blocks + 0x40)) s138 =
     num_of_bytelist
     (SUB_LIST (0x0,0x50 * val num_5blocks + 0x40)
     (aes256_xts_encrypt pt_in (0x50 * val num_5blocks + 0x40) iv key1_lst
     key2_lst))`
*)
          MP_TAC (SPECL [`0x50 * val (num_5blocks:int64):num`; `ctxt_p:int64`;
                         `(aes256_xts_encrypt pt_in (val (num_5blocks:int64) * 0x50) iv key1_lst key2_lst):byte list`;
                         `s138:armstate`] BYTE_LIST_TO_NUM_THM) THEN
          ANTS_TAC THENL[
            REWRITE_TAC[ARITH_RULE `i * 0x50 = 0x10 * 5 * i`;
                        LENGTH_OF_AES256_XTS_ENCRYPT_FULL_BLOCKS] THEN
            ARITH_TAC
            ; ALL_TAC] THEN
          DISCH_THEN (fun th -> REWRITE_TAC[th]) THEN
(*
`read (memory :> bytes (ctxt_p,0x50 * val num_5blocks)) s138 =
 num_of_bytelist
 (SUB_LIST (0x0,0x50 * val num_5blocks)
 (aes256_xts_encrypt pt_in (val num_5blocks * 0x50) iv key1_lst key2_lst))
 ==> read (memory :> bytes (ctxt_p,0x50 * val num_5blocks + 0x40)) s138 =
     num_of_bytelist
     (SUB_LIST (0x0,0x50 * val num_5blocks + 0x40)
     (aes256_xts_encrypt pt_in (0x50 * val num_5blocks + 0x40) iv key1_lst
     key2_lst))`
*)
          DISCH_TAC THEN

          IMP_REWRITE_TAC[ARITH_RULE `0x50 * i + 0x40 = (0x50 * i + 0x30) + 0x10`; READ_BYTES_AND_BYTE128_SPLIT] THEN
          EXISTS_TAC `(aes256_xts_encrypt pt_in (0x50 * val (num_5blocks:int64) + 0x40) iv key1_lst key2_lst)` THEN
          REPEAT CONJ_TAC THENL [
            REWRITE_TAC [ARITH_RULE `(0x50 * i + 0x30) + 0x10 = 0x50 * i + 0x40`];
(*
`(0x50 * val num_5blocks + 0x30) + 0x10 <=
 LENGTH
 (aes256_xts_encrypt pt_in (0x50 * val num_5blocks + 0x40) iv key1_lst
 key2_lst)`
*)
            MP_TAC (SPECL [`0x5 * val (num_5blocks:int64) + 0x4:num`;
              `pt_in:byte list`; `iv:int128`; `key1_lst:int128 list`;
              `key2_lst:int128 list`] LENGTH_OF_AES256_XTS_ENCRYPT_FULL_BLOCKS) THEN
            REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_ASSOC; GSYM ADD_ASSOC] THEN
            CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
            ASM_REWRITE_TAC[] THEN ARITH_TAC; (* 4 total *)
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
           (* Establish that one xts encrypt round is the same as
               selecting one block of bytes from calling the top-level function. *)
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
(*
`read (memory :> bytes (ctxt_p,0x50 * val num_5blocks + 0x30)) s138 =
 num_of_bytelist
 (SUB_LIST (0x0,0x50 * val num_5blocks + 0x30)
 (aes256_xts_encrypt pt_in (0x50 * val num_5blocks + 0x40) iv key1_lst
 key2_lst))`
*)
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
                      READ_CT_TAIL3_LEMMA) THEN
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
          REWRITE_TAC[acc_blocks] THEN ASM_SIMP_TAC[] THEN CONV_TAC WORD_RULE;
          REWRITE_TAC[acc_blocks] THEN ASM_SIMP_TAC[] THEN CONV_TAC WORD_RULE;
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
        ] ; ALL_TAC
      ] THEN (* 2 total *)

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
                      READ_CT_TAIL2_LEMMA) THEN
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
          REWRITE_TAC[acc_blocks] THEN ASM_SIMP_TAC[] THEN CONV_TAC WORD_RULE;
          REWRITE_TAC[acc_blocks] THEN ASM_SIMP_TAC[] THEN CONV_TAC WORD_RULE;
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
        ] ; ALL_TAC
      ] THEN (* 2 total *)

      DISCH_TAC THEN
      ARM_ACCSTEPS_TAC AES256_XTS_ENCRYPT_EXEC [] (8--9) THEN
      FIRST_X_ASSUM MP_TAC THEN
      COND_CASES_TAC THENL
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
                      READ_CT_TAIL1_LEMMA) THEN
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
          REWRITE_TAC[acc_blocks] THEN ASM_SIMP_TAC[] THEN CONV_TAC WORD_RULE;
          REWRITE_TAC[acc_blocks] THEN ASM_SIMP_TAC[] THEN CONV_TAC WORD_RULE;
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
        ] ; ALL_TAC
      ] THEN (* 2 total *)

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
          REWRITE_TAC[LEN_FULL_BLOCKS_TO_VAL] THEN
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
        REWRITE_TAC[acc_blocks] THEN ASM_SIMP_TAC[] THEN CONV_TAC WORD_RULE;
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

);;


(*
val it : goalstack = 1 subgoal (1 total)

  0 [`nonoverlapping_modulo (0x2 EXP 0x40) (pc,0xaac) (val ptxt_p,val len)`]
  1 [`nonoverlapping_modulo (0x2 EXP 0x40) (pc,0xaac) (val ctxt_p,val len)`]
  2 [`nonoverlapping_modulo (0x2 EXP 0x40) (pc,0xaac) (val key1_p,0xf4)`]
  3 [`nonoverlapping_modulo (0x2 EXP 0x40) (pc,0xaac) (val key2_p,0xf4)`]
  4 [`nonoverlapping_modulo (0x2 EXP 0x40) (val ptxt_p,val len)
      (val ctxt_p,val len)`]
  5 [`nonoverlapping_modulo (0x2 EXP 0x40) (val ptxt_p,val len)
      (val key1_p,0xf4)`]
  6 [`nonoverlapping_modulo (0x2 EXP 0x40) (val ptxt_p,val len)
      (val key2_p,0xf4)`]
  7 [`nonoverlapping_modulo (0x2 EXP 0x40) (val ctxt_p,val len)
      (val key1_p,0xf4)`]
  8 [`nonoverlapping_modulo (0x2 EXP 0x40) (val ctxt_p,val len)
      (val key2_p,0xf4)`]
  9 [`nonoverlapping_modulo (0x2 EXP 0x40) (val key1_p,0xf4)
      (val key2_p,0xf4)`]
 10 [`val len >= 0x10`]
 11 [`val len <= 0x2 EXP 0x18`]
 12 [`LENGTH pt_in = val len`]
 13 [`word_add tail_len len_full_blocks = len`]
 14 [`word_and len (word 0xfffffffffffffff0) = len_full_blocks`]
 15 [`word (val len_full_blocks DIV 0x50) = num_5blocks`]
 16 [`word_and len (word 0xf) = tail_len`]
 17 [`[k1_0; k1_1; k1_2; k1_3; k1_4; k1_5; k1_6; k1_7; k1_8; k1_9; k1_10;
       k1_11; k1_12; k1_13; k1_14] =
      key1_lst`]
 18 [`[k2_0; k2_1; k2_2; k2_3; k2_4; k2_5; k2_6; k2_7; k2_8; k2_9; k2_10;
       k2_11; k2_12; k2_13; k2_14] =
      key2_lst`]
 19 [`~(val len < 0x50)`]
 20 [`~(val len_full_blocks < 0x50)`]
 21 [`val len_full_blocks <= 0x2 EXP 0x18`]
 22 [`0x0 < val num_5blocks`]
 23 [`val len_full_blocks <= val len`]
 24 [`val num_5blocks * 0x50 <= val len_full_blocks`]

`ensures arm
 (\s.
      aligned_bytes_loaded s (word pc) aes256_xts_encrypt_mc /\
      read PC s = word (pc + 0x9e0) /\
      read X0 s =
      word_add ptxt_p (word (acc_len num_5blocks len_full_blocks)) /\
      read X1 s =
      word_add ctxt_p (word (acc_len num_5blocks len_full_blocks)) /\
      read X21 s = tail_len /\
      read Q6 s =
      calculate_tweak (acc_blocks num_5blocks len_full_blocks true) iv
      key2_lst /\
      read X19 s = word 0x87 /\
      read X10 s =
      word_subword
      (calculate_tweak (acc_blocks num_5blocks len_full_blocks false) iv
      key2_lst)
      (0x40,0x40) /\
      read X9 s =
      word_zx
      (calculate_tweak (acc_blocks num_5blocks len_full_blocks false) iv
      key2_lst) /\
      read Q16 s = k1_0 /\
      read Q17 s = k1_1 /\
      read Q12 s = k1_2 /\
      read Q13 s = k1_3 /\
      read Q14 s = k1_4 /\
      read Q15 s = k1_5 /\
      read Q4 s = k1_6 /\
      read Q5 s = k1_7 /\
      read Q18 s = k1_8 /\
      read Q19 s = k1_9 /\
      read Q20 s = k1_10 /\
      read Q21 s = k1_11 /\
      read Q22 s = k1_12 /\
      read Q23 s = k1_13 /\
      read Q7 s = k1_14 /\
      byte_list_at pt_in ptxt_p len s /\
      byte_list_at
      (aes256_xts_encrypt pt_in (acc_len num_5blocks len_full_blocks) iv
       key1_lst
      key2_lst)
      ctxt_p
      (word (acc_len num_5blocks len_full_blocks))
      s)
 (\s.
      read PC s = word (pc + 0xaac - 0x8 * 0x4) /\
      (forall i.
           i < val len
           ==> read (memory :> bytes8 (word_add ctxt_p (word i))) s =
               EL i (aes256_xts_encrypt pt_in (val len) iv key1_lst key2_lst)))
 (MAYCHANGE
  [PC; X0; X1; X2; X4; X6; X7; X8; X9; X10; X11; X19; X20; X21; X22] ,,
  MAYCHANGE
  [Q0; Q1; Q4; Q5; Q6; Q7; Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15; Q16; Q17;
   Q18; Q19; Q20; Q21; Q22; Q23; Q24; Q25; Q26] ,,
  MAYCHANGE [NF; ZF; CF; VF] ,,
  MAYCHANGE [events] ,,
  MAYCHANGE [memory :> bytes (ctxt_p,val len)])`
*)
