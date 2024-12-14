(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Forward number theoretic transform.                                       *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "arm/proofs/utils/mlkem.ml";;

(**** print_coda_from_elf (-1) "arm/mlkem/mlkem_ntt.o";;
 ****)

let mlkem_ntt_mc,mlkem_ntt_data = define_coda_literal_from_elf
  "mlkem_ntt_mc" "mlkem_ntt_data" "arm/mlkem/mlkem_ntt.o"
[
  0xd10103ff;       (* arm_SUB SP SP (rvalue (word 64)) *)
  0x6d0027e8;       (* arm_STP D8 D9 SP (Immediate_Offset (iword (&0))) *)
  0x6d012fea;       (* arm_STP D10 D11 SP (Immediate_Offset (iword (&16))) *)
  0x6d0237ec;       (* arm_STP D12 D13 SP (Immediate_Offset (iword (&32))) *)
  0x6d033fee;       (* arm_STP D14 D15 SP (Immediate_Offset (iword (&48))) *)
  0x10002883;       (* arm_ADR X3 (word 1296) *)
  0x91000063;       (* arm_ADD X3 X3 (rvalue (word 0)) *)
  0x10002d44;       (* arm_ADR X4 (word 1448) *)
  0x91000084;       (* arm_ADD X4 X4 (rvalue (word 0)) *)
  0x10002785;       (* arm_ADR X5 (word 1264) *)
  0x4e020fe7;       (* arm_DUP_GEN Q7 XZR 16 128 *)
  0x5281a025;       (* arm_MOV W5 (rvalue (word 3329)) *)
  0x4e021ca7;       (* arm_INS_GEN Q7 W5 0 16 *)
  0x5289d7e5;       (* arm_MOV W5 (rvalue (word 20159)) *)
  0x4e061ca7;       (* arm_INS_GEN Q7 W5 16 16 *)
  0xaa0003e1;       (* arm_MOV X1 X0 *)
  0xd2800082;       (* arm_MOV X2 (rvalue (word 4)) *)
  0x3cc20460;       (* arm_LDR Q0 X3 (Postimmediate_Offset (iword (&32))) *)
  0x3cdf0061;       (* arm_LDR Q1 X3 (Immediate_Offset (iword (-- &16))) *)
  0x3dc00014;       (* arm_LDR Q20 X0 (Immediate_Offset (word 0)) *)
  0x3dc0101b;       (* arm_LDR Q27 X0 (Immediate_Offset (word 64)) *)
  0x3dc0200f;       (* arm_LDR Q15 X0 (Immediate_Offset (word 128)) *)
  0x3dc03015;       (* arm_LDR Q21 X0 (Immediate_Offset (word 192)) *)
  0x3dc04013;       (* arm_LDR Q19 X0 (Immediate_Offset (word 256)) *)
  0x3dc0701c;       (* arm_LDR Q28 X0 (Immediate_Offset (word 448)) *)
  0x4f408266;       (* arm_MULE_VEC Q6 Q19 Q0 16 128 0 *)
  0x3dc0501d;       (* arm_LDR Q29 X0 (Immediate_Offset (word 320)) *)
  0x4f408383;       (* arm_MULE_VEC Q3 Q28 Q0 16 128 0 *)
  0x3dc06002;       (* arm_LDR Q2 X0 (Immediate_Offset (word 384)) *)
  0xd1000442;       (* arm_SUB X2 X2 (rvalue (word 1)) *)
  0x4f50d27e;       (* arm_SQRDMULHE_VEC Q30 Q19 Q0 16 128 1 *)
  0x4f50d3b3;       (* arm_SQRDMULHE_VEC Q19 Q29 Q0 16 128 1 *)
  0x4f4083bd;       (* arm_MULE_VEC Q29 Q29 Q0 16 128 0 *)
  0x4f50d057;       (* arm_SQRDMULHE_VEC Q23 Q2 Q0 16 128 1 *)
  0x6f4743c6;       (* arm_MLS_VEC Q6 Q30 Q7 16 128 0 *)
  0x4f40805e;       (* arm_MULE_VEC Q30 Q2 Q0 16 128 0 *)
  0x6f47427d;       (* arm_MLS_VEC Q29 Q19 Q7 16 128 0 *)
  0x4f50d393;       (* arm_SQRDMULHE_VEC Q19 Q28 Q0 16 128 1 *)
  0x6e66869c;       (* arm_SUB_VEC Q28 Q20 Q6 16 128 *)
  0x6f4742fe;       (* arm_MLS_VEC Q30 Q23 Q7 16 128 0 *)
  0x6e7d8777;       (* arm_SUB_VEC Q23 Q27 Q29 16 128 *)
  0x4e7d877d;       (* arm_ADD_VEC Q29 Q27 Q29 16 128 *)
  0x4e668686;       (* arm_ADD_VEC Q6 Q20 Q6 16 128 *)
  0x6e7e85e2;       (* arm_SUB_VEC Q2 Q15 Q30 16 128 *)
  0x4e7e85fe;       (* arm_ADD_VEC Q30 Q15 Q30 16 128 *)
  0x6f474263;       (* arm_MLS_VEC Q3 Q19 Q7 16 128 0 *)
  0x4f50d853;       (* arm_SQRDMULHE_VEC Q19 Q2 Q0 16 128 5 *)
  0x4f408842;       (* arm_MULE_VEC Q2 Q2 Q0 16 128 4 *)
  0x4f70d3d4;       (* arm_SQRDMULHE_VEC Q20 Q30 Q0 16 128 3 *)
  0x6e6386bb;       (* arm_SUB_VEC Q27 Q21 Q3 16 128 *)
  0x4e6386a3;       (* arm_ADD_VEC Q3 Q21 Q3 16 128 *)
  0x6f474262;       (* arm_MLS_VEC Q2 Q19 Q7 16 128 0 *)
  0x4f50db73;       (* arm_SQRDMULHE_VEC Q19 Q27 Q0 16 128 5 *)
  0x4f408b7b;       (* arm_MULE_VEC Q27 Q27 Q0 16 128 4 *)
  0x4f6083de;       (* arm_MULE_VEC Q30 Q30 Q0 16 128 2 *)
  0x6e62878f;       (* arm_SUB_VEC Q15 Q28 Q2 16 128 *)
  0x4e62879c;       (* arm_ADD_VEC Q28 Q28 Q2 16 128 *)
  0x6f47427b;       (* arm_MLS_VEC Q27 Q19 Q7 16 128 0 *)
  0x4f70d073;       (* arm_SQRDMULHE_VEC Q19 Q3 Q0 16 128 3 *)
  0x4f608062;       (* arm_MULE_VEC Q2 Q3 Q0 16 128 2 *)
  0x6f47429e;       (* arm_MLS_VEC Q30 Q20 Q7 16 128 0 *)
  0x6e7b86e3;       (* arm_SUB_VEC Q3 Q23 Q27 16 128 *)
  0x4e7b86f7;       (* arm_ADD_VEC Q23 Q23 Q27 16 128 *)
  0x6f474262;       (* arm_MLS_VEC Q2 Q19 Q7 16 128 0 *)
  0x6e7e84d3;       (* arm_SUB_VEC Q19 Q6 Q30 16 128 *)
  0x4e7e84de;       (* arm_ADD_VEC Q30 Q6 Q30 16 128 *)
  0x4f71d2e6;       (* arm_SQRDMULHE_VEC Q6 Q23 Q1 16 128 3 *)
  0x6e6287b4;       (* arm_SUB_VEC Q20 Q29 Q2 16 128 *)
  0x4e6287bd;       (* arm_ADD_VEC Q29 Q29 Q2 16 128 *)
  0x4f6182f7;       (* arm_MULE_VEC Q23 Q23 Q1 16 128 2 *)
  0x4f51d282;       (* arm_SQRDMULHE_VEC Q2 Q20 Q1 16 128 1 *)
  0x4f70dbbb;       (* arm_SQRDMULHE_VEC Q27 Q29 Q0 16 128 7 *)
  0x4f608bbd;       (* arm_MULE_VEC Q29 Q29 Q0 16 128 6 *)
  0x4f418294;       (* arm_MULE_VEC Q20 Q20 Q1 16 128 0 *)
  0x6f4740d7;       (* arm_MLS_VEC Q23 Q6 Q7 16 128 0 *)
  0x4f51d866;       (* arm_SQRDMULHE_VEC Q6 Q3 Q1 16 128 5 *)
  0x6f47437d;       (* arm_MLS_VEC Q29 Q27 Q7 16 128 0 *)
  0x6f474054;       (* arm_MLS_VEC Q20 Q2 Q7 16 128 0 *)
  0x6e778782;       (* arm_SUB_VEC Q2 Q28 Q23 16 128 *)
  0x4e778797;       (* arm_ADD_VEC Q23 Q28 Q23 16 128 *)
  0x6e7d87dc;       (* arm_SUB_VEC Q28 Q30 Q29 16 128 *)
  0x4f418863;       (* arm_MULE_VEC Q3 Q3 Q1 16 128 4 *)
  0x4e7d87de;       (* arm_ADD_VEC Q30 Q30 Q29 16 128 *)
  0x6e74867d;       (* arm_SUB_VEC Q29 Q19 Q20 16 128 *)
  0x4e748673;       (* arm_ADD_VEC Q19 Q19 Q20 16 128 *)
  0x6f4740c3;       (* arm_MLS_VEC Q3 Q6 Q7 16 128 0 *)
  0x3c81041e;       (* arm_STR Q30 X0 (Postimmediate_Offset (iword (&16))) *)
  0x3dc00014;       (* arm_LDR Q20 X0 (Immediate_Offset (word 0)) *)
  0x6e6385fe;       (* arm_SUB_VEC Q30 Q15 Q3 16 128 *)
  0x4e6385e6;       (* arm_ADD_VEC Q6 Q15 Q3 16 128 *)
  0x3d800c1c;       (* arm_STR Q28 X0 (Immediate_Offset (word 48)) *)
  0x3dc0101b;       (* arm_LDR Q27 X0 (Immediate_Offset (word 64)) *)
  0x3d801c13;       (* arm_STR Q19 X0 (Immediate_Offset (word 112)) *)
  0x3dc0200f;       (* arm_LDR Q15 X0 (Immediate_Offset (word 128)) *)
  0x3d802c1d;       (* arm_STR Q29 X0 (Immediate_Offset (word 176)) *)
  0x3dc03015;       (* arm_LDR Q21 X0 (Immediate_Offset (word 192)) *)
  0x3d803c17;       (* arm_STR Q23 X0 (Immediate_Offset (word 240)) *)
  0x3dc04013;       (* arm_LDR Q19 X0 (Immediate_Offset (word 256)) *)
  0x3d804c02;       (* arm_STR Q2 X0 (Immediate_Offset (word 304)) *)
  0x3dc0501d;       (* arm_LDR Q29 X0 (Immediate_Offset (word 320)) *)
  0x3d805c06;       (* arm_STR Q6 X0 (Immediate_Offset (word 368)) *)
  0x4f408266;       (* arm_MULE_VEC Q6 Q19 Q0 16 128 0 *)
  0x3d806c1e;       (* arm_STR Q30 X0 (Immediate_Offset (word 432)) *)
  0x3dc0701c;       (* arm_LDR Q28 X0 (Immediate_Offset (word 448)) *)
  0x3dc06002;       (* arm_LDR Q2 X0 (Immediate_Offset (word 384)) *)
  0x4f408383;       (* arm_MULE_VEC Q3 Q28 Q0 16 128 0 *)
  0xd1000442;       (* arm_SUB X2 X2 (rvalue (word 1)) *)
  0xb5fff662;       (* arm_CBNZ X2 (word 2096844) *)
  0x4f50d397;       (* arm_SQRDMULHE_VEC Q23 Q28 Q0 16 128 1 *)
  0x4f50d05c;       (* arm_SQRDMULHE_VEC Q28 Q2 Q0 16 128 1 *)
  0x4f4083a5;       (* arm_MULE_VEC Q5 Q29 Q0 16 128 0 *)
  0x4f408042;       (* arm_MULE_VEC Q2 Q2 Q0 16 128 0 *)
  0x6f4742e3;       (* arm_MLS_VEC Q3 Q23 Q7 16 128 0 *)
  0x4f50d3ad;       (* arm_SQRDMULHE_VEC Q13 Q29 Q0 16 128 1 *)
  0x4f50d27e;       (* arm_SQRDMULHE_VEC Q30 Q19 Q0 16 128 1 *)
  0x6f474382;       (* arm_MLS_VEC Q2 Q28 Q7 16 128 0 *)
  0x6e6386b7;       (* arm_SUB_VEC Q23 Q21 Q3 16 128 *)
  0x6f4741a5;       (* arm_MLS_VEC Q5 Q13 Q7 16 128 0 *)
  0x6f4743c6;       (* arm_MLS_VEC Q6 Q30 Q7 16 128 0 *)
  0x4f408afd;       (* arm_MULE_VEC Q29 Q23 Q0 16 128 4 *)
  0x4f50dafe;       (* arm_SQRDMULHE_VEC Q30 Q23 Q0 16 128 5 *)
  0x4e6285e8;       (* arm_ADD_VEC Q8 Q15 Q2 16 128 *)
  0x6e6285f3;       (* arm_SUB_VEC Q19 Q15 Q2 16 128 *)
  0x6e658772;       (* arm_SUB_VEC Q18 Q27 Q5 16 128 *)
  0x6f4743dd;       (* arm_MLS_VEC Q29 Q30 Q7 16 128 0 *)
  0x4f408a62;       (* arm_MULE_VEC Q2 Q19 Q0 16 128 4 *)
  0x4f50da6d;       (* arm_SQRDMULHE_VEC Q13 Q19 Q0 16 128 5 *)
  0x4e66869f;       (* arm_ADD_VEC Q31 Q20 Q6 16 128 *)
  0x6e7d865e;       (* arm_SUB_VEC Q30 Q18 Q29 16 128 *)
  0x6e66868c;       (* arm_SUB_VEC Q12 Q20 Q6 16 128 *)
  0x4f70d117;       (* arm_SQRDMULHE_VEC Q23 Q8 Q0 16 128 3 *)
  0x4f51dbd3;       (* arm_SQRDMULHE_VEC Q19 Q30 Q1 16 128 5 *)
  0x4f418bdc;       (* arm_MULE_VEC Q28 Q30 Q1 16 128 4 *)
  0x6f4741a2;       (* arm_MLS_VEC Q2 Q13 Q7 16 128 0 *)
  0x4f60810f;       (* arm_MULE_VEC Q15 Q8 Q0 16 128 2 *)
  0x4e6386b8;       (* arm_ADD_VEC Q24 Q21 Q3 16 128 *)
  0x6f47427c;       (* arm_MLS_VEC Q28 Q19 Q7 16 128 0 *)
  0x6e628588;       (* arm_SUB_VEC Q8 Q12 Q2 16 128 *)
  0x6f4742ef;       (* arm_MLS_VEC Q15 Q23 Q7 16 128 0 *)
  0x4f70d30b;       (* arm_SQRDMULHE_VEC Q11 Q24 Q0 16 128 3 *)
  0x6e7c851e;       (* arm_SUB_VEC Q30 Q8 Q28 16 128 *)
  0x4f60830d;       (* arm_MULE_VEC Q13 Q24 Q0 16 128 2 *)
  0x6e6f87f4;       (* arm_SUB_VEC Q20 Q31 Q15 16 128 *)
  0x3d80701e;       (* arm_STR Q30 X0 (Immediate_Offset (word 448)) *)
  0x4e7c8518;       (* arm_ADD_VEC Q24 Q8 Q28 16 128 *)
  0x6f47416d;       (* arm_MLS_VEC Q13 Q11 Q7 16 128 0 *)
  0x4e658763;       (* arm_ADD_VEC Q3 Q27 Q5 16 128 *)
  0x3d806018;       (* arm_STR Q24 X0 (Immediate_Offset (word 384)) *)
  0x4e6f87e4;       (* arm_ADD_VEC Q4 Q31 Q15 16 128 *)
  0x6e6d846b;       (* arm_SUB_VEC Q11 Q3 Q13 16 128 *)
  0x4e6d8473;       (* arm_ADD_VEC Q19 Q3 Q13 16 128 *)
  0x4e7d864a;       (* arm_ADD_VEC Q10 Q18 Q29 16 128 *)
  0x4f51d17e;       (* arm_SQRDMULHE_VEC Q30 Q11 Q1 16 128 1 *)
  0x4f41816d;       (* arm_MULE_VEC Q13 Q11 Q1 16 128 0 *)
  0x4f608a66;       (* arm_MULE_VEC Q6 Q19 Q0 16 128 6 *)
  0x4f70da7a;       (* arm_SQRDMULHE_VEC Q26 Q19 Q0 16 128 7 *)
  0x4f618157;       (* arm_MULE_VEC Q23 Q10 Q1 16 128 2 *)
  0x6f4743cd;       (* arm_MLS_VEC Q13 Q30 Q7 16 128 0 *)
  0x4f71d153;       (* arm_SQRDMULHE_VEC Q19 Q10 Q1 16 128 3 *)
  0x6f474346;       (* arm_MLS_VEC Q6 Q26 Q7 16 128 0 *)
  0x4e628595;       (* arm_ADD_VEC Q21 Q12 Q2 16 128 *)
  0x4e6d869e;       (* arm_ADD_VEC Q30 Q20 Q13 16 128 *)
  0x6f474277;       (* arm_MLS_VEC Q23 Q19 Q7 16 128 0 *)
  0x6e6d869d;       (* arm_SUB_VEC Q29 Q20 Q13 16 128 *)
  0x3d80201e;       (* arm_STR Q30 X0 (Immediate_Offset (word 128)) *)
  0x4e668485;       (* arm_ADD_VEC Q5 Q4 Q6 16 128 *)
  0x3d80301d;       (* arm_STR Q29 X0 (Immediate_Offset (word 192)) *)
  0x6e668493;       (* arm_SUB_VEC Q19 Q4 Q6 16 128 *)
  0x3c810405;       (* arm_STR Q5 X0 (Postimmediate_Offset (iword (&16))) *)
  0x6e7786be;       (* arm_SUB_VEC Q30 Q21 Q23 16 128 *)
  0x3d800c13;       (* arm_STR Q19 X0 (Immediate_Offset (word 48)) *)
  0x4e7786a2;       (* arm_ADD_VEC Q2 Q21 Q23 16 128 *)
  0x3d804c1e;       (* arm_STR Q30 X0 (Immediate_Offset (word 304)) *)
  0x3d803c02;       (* arm_STR Q2 X0 (Immediate_Offset (word 240)) *)
  0xaa0103e0;       (* arm_MOV X0 X1 *)
  0xd2800102;       (* arm_MOV X2 (rvalue (word 8)) *)
  0x3dc00c13;       (* arm_LDR Q19 X0 (Immediate_Offset (word 48)) *)
  0x3cc10469;       (* arm_LDR Q9 X3 (Postimmediate_Offset (iword (&16))) *)
  0x3dc0080b;       (* arm_LDR Q11 X0 (Immediate_Offset (word 32)) *)
  0x4f59d27e;       (* arm_SQRDMULHE_VEC Q30 Q19 Q9 16 128 1 *)
  0x4f498264;       (* arm_MULE_VEC Q4 Q19 Q9 16 128 0 *)
  0x4f59d16c;       (* arm_SQRDMULHE_VEC Q12 Q11 Q9 16 128 1 *)
  0x3dc00892;       (* arm_LDR Q18 X4 (Immediate_Offset (word 32)) *)
  0x6f4743c4;       (* arm_MLS_VEC Q4 Q30 Q7 16 128 0 *)
  0x3dc01080;       (* arm_LDR Q0 X4 (Immediate_Offset (word 64)) *)
  0xd1000442;       (* arm_SUB X2 X2 (rvalue (word 1)) *)
  0x3dc00c94;       (* arm_LDR Q20 X4 (Immediate_Offset (word 48)) *)
  0x4f498178;       (* arm_MULE_VEC Q24 Q11 Q9 16 128 0 *)
  0x3dc00410;       (* arm_LDR Q16 X0 (Immediate_Offset (word 16)) *)
  0x3dc01491;       (* arm_LDR Q17 X4 (Immediate_Offset (word 80)) *)
  0x6e648601;       (* arm_SUB_VEC Q1 Q16 Q4 16 128 *)
  0x4e648617;       (* arm_ADD_VEC Q23 Q16 Q4 16 128 *)
  0x6f474198;       (* arm_MLS_VEC Q24 Q12 Q7 16 128 0 *)
  0x4f59d824;       (* arm_SQRDMULHE_VEC Q4 Q1 Q9 16 128 5 *)
  0x4f79d2fc;       (* arm_SQRDMULHE_VEC Q28 Q23 Q9 16 128 3 *)
  0x4f6982f6;       (* arm_MULE_VEC Q22 Q23 Q9 16 128 2 *)
  0x4f498825;       (* arm_MULE_VEC Q5 Q1 Q9 16 128 4 *)
  0x3dc00006;       (* arm_LDR Q6 X0 (Immediate_Offset (word 0)) *)
  0x6f474396;       (* arm_MLS_VEC Q22 Q28 Q7 16 128 0 *)
  0x6f474085;       (* arm_MLS_VEC Q5 Q4 Q7 16 128 0 *)
  0x3cc60484;       (* arm_LDR Q4 X4 (Postimmediate_Offset (iword (&96))) *)
  0x4e7884d0;       (* arm_ADD_VEC Q16 Q6 Q24 16 128 *)
  0x6e7884da;       (* arm_SUB_VEC Q26 Q6 Q24 16 128 *)
  0x3cdb008a;       (* arm_LDR Q10 X4 (Immediate_Offset (iword (-- &80))) *)
  0x6e768613;       (* arm_SUB_VEC Q19 Q16 Q22 16 128 *)
  0x4e768619;       (* arm_ADD_VEC Q25 Q16 Q22 16 128 *)
  0x6e65874e;       (* arm_SUB_VEC Q14 Q26 Q5 16 128 *)
  0x3dc01c08;       (* arm_LDR Q8 X0 (Immediate_Offset (word 112)) *)
  0x4e658742;       (* arm_ADD_VEC Q2 Q26 Q5 16 128 *)
  0x4e932b2c;       (* arm_TRN1 Q12 Q25 Q19 32 128 *)
  0x4e936b3a;       (* arm_TRN2 Q26 Q25 Q19 32 128 *)
  0x4e8e6845;       (* arm_TRN2 Q5 Q2 Q14 32 128 *)
  0x3cc10469;       (* arm_LDR Q9 X3 (Postimmediate_Offset (iword (&16))) *)
  0x4ec56b50;       (* arm_TRN2 Q16 Q26 Q5 64 128 *)
  0x4e8e285d;       (* arm_TRN1 Q29 Q2 Q14 32 128 *)
  0x4ec52b56;       (* arm_TRN1 Q22 Q26 Q5 64 128 *)
  0x4e649e18;       (* arm_MUL_VEC Q24 Q16 Q4 16 128 *)
  0x6e6ab605;       (* arm_SQRDMULH_VEC Q5 Q16 Q10 16 128 *)
  0x4edd6990;       (* arm_TRN2 Q16 Q12 Q29 64 128 *)
  0x4f59d11f;       (* arm_SQRDMULHE_VEC Q31 Q8 Q9 16 128 1 *)
  0x4e649e1a;       (* arm_MUL_VEC Q26 Q16 Q4 16 128 *)
  0x6e6ab604;       (* arm_SQRDMULH_VEC Q4 Q16 Q10 16 128 *)
  0x4edd2990;       (* arm_TRN1 Q16 Q12 Q29 64 128 *)
  0x6f4740b8;       (* arm_MLS_VEC Q24 Q5 Q7 16 128 0 *)
  0x3dc0180b;       (* arm_LDR Q11 X0 (Immediate_Offset (word 96)) *)
  0x6f47409a;       (* arm_MLS_VEC Q26 Q4 Q7 16 128 0 *)
  0x4e7886c5;       (* arm_ADD_VEC Q5 Q22 Q24 16 128 *)
  0x6e7886ce;       (* arm_SUB_VEC Q14 Q22 Q24 16 128 *)
  0x4f59d16c;       (* arm_SQRDMULHE_VEC Q12 Q11 Q9 16 128 1 *)
  0x6e74b4b9;       (* arm_SQRDMULH_VEC Q25 Q5 Q20 16 128 *)
  0x4e729caa;       (* arm_MUL_VEC Q10 Q5 Q18 16 128 *)
  0x4e7a8616;       (* arm_ADD_VEC Q22 Q16 Q26 16 128 *)
  0x6e71b5c4;       (* arm_SQRDMULH_VEC Q4 Q14 Q17 16 128 *)
  0x4e609dc5;       (* arm_MUL_VEC Q5 Q14 Q0 16 128 *)
  0x6f47432a;       (* arm_MLS_VEC Q10 Q25 Q7 16 128 0 *)
  0x3dc00892;       (* arm_LDR Q18 X4 (Immediate_Offset (word 32)) *)
  0x6e7a860d;       (* arm_SUB_VEC Q13 Q16 Q26 16 128 *)
  0x6f474085;       (* arm_MLS_VEC Q5 Q4 Q7 16 128 0 *)
  0x6e6a86d9;       (* arm_SUB_VEC Q25 Q22 Q10 16 128 *)
  0x4e6a86d8;       (* arm_ADD_VEC Q24 Q22 Q10 16 128 *)
  0x4f498104;       (* arm_MULE_VEC Q4 Q8 Q9 16 128 0 *)
  0x6e6585bb;       (* arm_SUB_VEC Q27 Q13 Q5 16 128 *)
  0x4e6585ba;       (* arm_ADD_VEC Q26 Q13 Q5 16 128 *)
  0x3dc01080;       (* arm_LDR Q0 X4 (Immediate_Offset (word 64)) *)
  0x4e993b17;       (* arm_ZIP1 Q23 Q24 Q25 32 128 *)
  0x4e997b19;       (* arm_ZIP2 Q25 Q24 Q25 32 128 *)
  0x4e9b3b58;       (* arm_ZIP1 Q24 Q26 Q27 32 128 *)
  0x4e9b7b5b;       (* arm_ZIP2 Q27 Q26 Q27 32 128 *)
  0x4ed83afa;       (* arm_ZIP1 Q26 Q23 Q24 64 128 *)
  0x4ed87af8;       (* arm_ZIP2 Q24 Q23 Q24 64 128 *)
  0xad00601a;       (* arm_STP Q26 Q24 X0 (Immediate_Offset (iword (&0))) *)
  0x4edb3b3a;       (* arm_ZIP1 Q26 Q25 Q27 64 128 *)
  0x4edb7b38;       (* arm_ZIP2 Q24 Q25 Q27 64 128 *)
  0xad01601a;       (* arm_STP Q26 Q24 X0 (Immediate_Offset (iword (&32))) *)
  0x91010000;       (* arm_ADD X0 X0 (rvalue (word 64)) *)
  0x6f4743e4;       (* arm_MLS_VEC Q4 Q31 Q7 16 128 0 *)
  0xd1000442;       (* arm_SUB X2 X2 (rvalue (word 1)) *)
  0xb5fff722;       (* arm_CBNZ X2 (word 2096868) *)
  0x3dc00417;       (* arm_LDR Q23 X0 (Immediate_Offset (word 16)) *)
  0x3dc00013;       (* arm_LDR Q19 X0 (Immediate_Offset (word 0)) *)
  0x6e6486fe;       (* arm_SUB_VEC Q30 Q23 Q4 16 128 *)
  0x4f49817c;       (* arm_MULE_VEC Q28 Q11 Q9 16 128 0 *)
  0x4e6486f7;       (* arm_ADD_VEC Q23 Q23 Q4 16 128 *)
  0x4f498bdd;       (* arm_MULE_VEC Q29 Q30 Q9 16 128 4 *)
  0x4f59dbde;       (* arm_SQRDMULHE_VEC Q30 Q30 Q9 16 128 5 *)
  0x6f47419c;       (* arm_MLS_VEC Q28 Q12 Q7 16 128 0 *)
  0x4f6982e6;       (* arm_MULE_VEC Q6 Q23 Q9 16 128 2 *)
  0x4f79d2e2;       (* arm_SQRDMULHE_VEC Q2 Q23 Q9 16 128 3 *)
  0x6f4743dd;       (* arm_MLS_VEC Q29 Q30 Q7 16 128 0 *)
  0x6e7c867e;       (* arm_SUB_VEC Q30 Q19 Q28 16 128 *)
  0x4e7c867c;       (* arm_ADD_VEC Q28 Q19 Q28 16 128 *)
  0x6f474046;       (* arm_MLS_VEC Q6 Q2 Q7 16 128 0 *)
  0x6e7d87d3;       (* arm_SUB_VEC Q19 Q30 Q29 16 128 *)
  0x4e7d87de;       (* arm_ADD_VEC Q30 Q30 Q29 16 128 *)
  0x3cc60494;       (* arm_LDR Q20 X4 (Postimmediate_Offset (iword (&96))) *)
  0x4e668797;       (* arm_ADD_VEC Q23 Q28 Q6 16 128 *)
  0x6e66879d;       (* arm_SUB_VEC Q29 Q28 Q6 16 128 *)
  0x4e932bc1;       (* arm_TRN1 Q1 Q30 Q19 32 128 *)
  0x4e936bc6;       (* arm_TRN2 Q6 Q30 Q19 32 128 *)
  0x4e9d6afc;       (* arm_TRN2 Q28 Q23 Q29 32 128 *)
  0x3cdb0082;       (* arm_LDR Q2 X4 (Immediate_Offset (iword (-- &80))) *)
  0x4ec66b9e;       (* arm_TRN2 Q30 Q28 Q6 64 128 *)
  0x4e9d2ae3;       (* arm_TRN1 Q3 Q23 Q29 32 128 *)
  0x6e62b7d3;       (* arm_SQRDMULH_VEC Q19 Q30 Q2 16 128 *)
  0x4e749fdd;       (* arm_MUL_VEC Q29 Q30 Q20 16 128 *)
  0x3cdd0089;       (* arm_LDR Q9 X4 (Immediate_Offset (iword (-- &48))) *)
  0x4ec1687e;       (* arm_TRN2 Q30 Q3 Q1 64 128 *)
  0x6f47427d;       (* arm_MLS_VEC Q29 Q19 Q7 16 128 0 *)
  0x6e62b7d7;       (* arm_SQRDMULH_VEC Q23 Q30 Q2 16 128 *)
  0x4ec62b82;       (* arm_TRN1 Q2 Q28 Q6 64 128 *)
  0x4e749fdc;       (* arm_MUL_VEC Q28 Q30 Q20 16 128 *)
  0x6e7d845e;       (* arm_SUB_VEC Q30 Q2 Q29 16 128 *)
  0x3cdf0094;       (* arm_LDR Q20 X4 (Immediate_Offset (iword (-- &16))) *)
  0x4e609fd3;       (* arm_MUL_VEC Q19 Q30 Q0 16 128 *)
  0x4e7d845d;       (* arm_ADD_VEC Q29 Q2 Q29 16 128 *)
  0x6e74b7de;       (* arm_SQRDMULH_VEC Q30 Q30 Q20 16 128 *)
  0x6f4742fc;       (* arm_MLS_VEC Q28 Q23 Q7 16 128 0 *)
  0x4e729fb7;       (* arm_MUL_VEC Q23 Q29 Q18 16 128 *)
  0x6e69b7bd;       (* arm_SQRDMULH_VEC Q29 Q29 Q9 16 128 *)
  0x4ec12866;       (* arm_TRN1 Q6 Q3 Q1 64 128 *)
  0x6f4743d3;       (* arm_MLS_VEC Q19 Q30 Q7 16 128 0 *)
  0x6e7c84de;       (* arm_SUB_VEC Q30 Q6 Q28 16 128 *)
  0x6f4743b7;       (* arm_MLS_VEC Q23 Q29 Q7 16 128 0 *)
  0x4e7c84dd;       (* arm_ADD_VEC Q29 Q6 Q28 16 128 *)
  0x4e7387d4;       (* arm_ADD_VEC Q20 Q30 Q19 16 128 *)
  0x6e7387d5;       (* arm_SUB_VEC Q21 Q30 Q19 16 128 *)
  0x4e7787b2;       (* arm_ADD_VEC Q18 Q29 Q23 16 128 *)
  0x6e7787b3;       (* arm_SUB_VEC Q19 Q29 Q23 16 128 *)
  0x4e933a57;       (* arm_ZIP1 Q23 Q18 Q19 32 128 *)
  0x4e937a53;       (* arm_ZIP2 Q19 Q18 Q19 32 128 *)
  0x4e953a92;       (* arm_ZIP1 Q18 Q20 Q21 32 128 *)
  0x4e957a95;       (* arm_ZIP2 Q21 Q20 Q21 32 128 *)
  0x4ed23af4;       (* arm_ZIP1 Q20 Q23 Q18 64 128 *)
  0x4ed27af2;       (* arm_ZIP2 Q18 Q23 Q18 64 128 *)
  0xad004814;       (* arm_STP Q20 Q18 X0 (Immediate_Offset (iword (&0))) *)
  0x4ed53a74;       (* arm_ZIP1 Q20 Q19 Q21 64 128 *)
  0x4ed57a72;       (* arm_ZIP2 Q18 Q19 Q21 64 128 *)
  0xad014814;       (* arm_STP Q20 Q18 X0 (Immediate_Offset (iword (&32))) *)
  0x91010000;       (* arm_ADD X0 X0 (rvalue (word 64)) *)
  0x6d4027e8;       (* arm_LDP D8 D9 SP (Immediate_Offset (iword (&0))) *)
  0x6d412fea;       (* arm_LDP D10 D11 SP (Immediate_Offset (iword (&16))) *)
  0x6d4237ec;       (* arm_LDP D12 D13 SP (Immediate_Offset (iword (&32))) *)
  0x6d433fee;       (* arm_LDP D14 D15 SP (Immediate_Offset (iword (&48))) *)
  0x910103ff;       (* arm_ADD SP SP (rvalue (word 64)) *)
  0xd65f03c0        (* arm_RET X30 *)
]
[1; 13; 191; 78; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 192; 249; 123; 194; 19;
 253; 51; 227; 216; 255; 118; 254; 81; 253; 150; 229; 118; 2; 57; 24; 104;
 250; 241; 200; 80; 3; 155; 32; 0; 0; 0; 0; 38; 4; 213; 40; 40; 1; 98; 11;
 142; 252; 22; 222; 0; 0; 0; 0; 126; 250; 201; 201; 59; 5; 124; 51; 196; 5;
 193; 56; 0; 0; 0; 0; 193; 0; 108; 7; 229; 254; 30; 245; 56; 0; 39; 2; 0; 0;
 0; 0; 29; 3; 165; 30; 191; 251; 33; 214; 53; 5; 65; 51; 0; 0; 0; 0; 225;
 253; 31; 235; 146; 5; 212; 54; 45; 251; 132; 208; 0; 0; 0; 0; 187; 255; 89;
 253; 23; 2; 146; 20; 65; 254; 208; 238; 0; 0; 0; 0; 57; 2; 225; 21; 88; 252;
 3; 220; 62; 254; 179; 238; 0; 0; 0; 0; 209; 249; 34; 195; 181; 250; 230;
 203; 53; 3; 145; 31; 0; 0; 0; 0; 33; 1; 33; 1; 75; 1; 75; 1; 180; 255; 180;
 255; 219; 249; 219; 249; 29; 11; 29; 11; 186; 12; 186; 12; 20; 253; 20; 253;
 133; 195; 133; 195; 17; 0; 17; 0; 71; 2; 71; 2; 101; 6; 101; 6; 239; 251;
 239; 251; 167; 0; 167; 0; 107; 22; 107; 22; 241; 62; 241; 62; 249; 215; 249;
 215; 200; 253; 200; 253; 88; 253; 88; 253; 211; 2; 211; 2; 76; 4; 76; 4; 41;
 234; 41; 234; 219; 229; 219; 229; 205; 27; 205; 27; 76; 42; 76; 42; 173; 4;
 173; 4; 255; 251; 255; 251; 228; 251; 228; 251; 6; 251; 6; 251; 6; 46; 6;
 46; 151; 216; 151; 216; 141; 215; 141; 215; 4; 207; 4; 207; 129; 5; 129; 5;
 208; 255; 208; 255; 244; 2; 244; 2; 198; 254; 198; 254; 45; 54; 45; 54; 40;
 254; 40; 254; 17; 29; 17; 29; 237; 243; 237; 243; 101; 253; 101; 253; 233;
 0; 233; 0; 107; 251; 107; 251; 233; 254; 233; 254; 91; 230; 91; 230; 245; 8;
 245; 8; 230; 210; 230; 210; 70; 245; 70; 245; 138; 2; 138; 2; 184; 250; 184;
 250; 208; 252; 208; 252; 120; 2; 120; 2; 254; 24; 254; 24; 4; 204; 4; 204;
 160; 224; 160; 224; 77; 24; 77; 24; 166; 249; 166; 249; 228; 253; 228; 253;
 54; 250; 54; 250; 181; 5; 181; 5; 123; 193; 123; 193; 61; 235; 61; 235; 4;
 199; 4; 199; 45; 56; 45; 56; 115; 6; 115; 6; 252; 249; 252; 249; 184; 3;
 184; 3; 126; 253; 126; 253; 123; 63; 123; 63; 201; 196; 201; 196; 155; 36;
 155; 36; 81; 231; 81; 231; 48; 254; 48; 254; 33; 0; 33; 0; 40; 5; 40; 5;
 122; 250; 122; 250; 41; 238; 41; 238; 69; 1; 69; 1; 193; 50; 193; 50; 162;
 201; 162; 201; 171; 3; 171; 3; 132; 252; 132; 252; 221; 2; 221; 2; 12; 1;
 12; 1; 27; 36; 27; 36; 180; 221; 180; 221; 47; 28; 47; 28; 78; 10; 78; 10;
 3; 252; 3; 252; 83; 252; 83; 252; 32; 252; 32; 252; 129; 2; 129; 2; 190;
 216; 190; 216; 210; 219; 210; 219; 220; 217; 220; 217; 165; 24; 165; 24; 14;
 252; 14; 252; 155; 5; 155; 5; 39; 3; 39; 3; 196; 1; 196; 1; 42; 217; 42;
 217; 45; 55; 45; 55; 7; 31; 7; 31; 97; 17; 97; 17; 48; 6; 48; 6; 244; 250;
 244; 250; 119; 1; 119; 1; 41; 251; 41; 251; 232; 60; 232; 60; 83; 206; 83;
 206; 107; 14; 107; 14; 92; 208; 92; 208; 249; 251; 249; 251; 147; 255; 147;
 255; 244; 252; 244; 252; 109; 6; 109; 6; 92; 216; 92; 216; 207; 251; 207;
 251; 2; 226; 2; 226; 64; 63; 64; 63; 158; 5; 158; 5; 51; 254; 51; 254; 254;
 5; 254; 5; 97; 252; 97; 252; 75; 55; 75; 55; 70; 238; 70; 238; 251; 58; 251;
 58; 91; 220; 91; 220; 39; 4; 39; 4; 212; 253; 212; 253; 50; 251; 50; 251;
 161; 252; 161; 252; 223; 40; 223; 40; 159; 234; 159; 234; 181; 208; 181;
 208; 209; 222; 209; 222; 63; 1; 63; 1; 245; 2; 245; 2; 49; 2; 49; 2; 33;
 253; 33; 253; 68; 12; 68; 12; 27; 29; 27; 29; 146; 21; 146; 21; 189; 227;
 189; 227; 86; 253; 86; 253; 56; 253; 56; 253; 201; 5; 201; 5; 136; 2; 136;
 2; 199; 229; 199; 229; 160; 228; 160; 228; 242; 56; 242; 56; 234; 24; 234;
 24; 243; 253; 243; 253; 147; 1; 147; 1; 119; 4; 119; 4; 214; 253; 214; 253;
 208; 235; 208; 235; 127; 15; 127; 15; 243; 43; 243; 43; 179; 234; 179; 234;
 68; 4; 68; 4; 2; 4; 2; 4; 101; 251; 101; 251; 118; 3; 118; 3; 253; 41; 253;
 41; 115; 39; 115; 39; 171; 210; 171; 210; 17; 34; 17; 34; 169; 252; 169;
 252; 37; 255; 37; 255; 203; 4; 203; 4; 142; 3; 142; 3; 32; 223; 32; 223;
 148; 247; 148; 247; 46; 47; 46; 47; 253; 34; 253; 34; 185; 249; 185; 249;
 81; 250; 81; 250; 61; 251; 61; 251; 117; 3; 117; 3; 54; 194; 54; 194; 14;
 200; 14; 200; 33; 209; 33; 209; 7; 34; 7; 34; 188; 4; 188; 4; 5; 4; 5; 4;
 118; 254; 118; 254; 105; 251; 105; 251; 154; 46; 154; 46; 145; 39; 145; 39;
 218; 240; 218; 240; 210; 210; 210; 210];;

let MLKEM_NTT_EXEC = ARM_MK_EXEC_RULE mlkem_ntt_mc;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let READ_MEMORY_MERGE_CONV =
  let baseconv =
    GEN_REWRITE_CONV I [READ_MEMORY_BYTESIZED_SPLIT] THENC
    LAND_CONV(LAND_CONV(RAND_CONV(RAND_CONV
     (TRY_CONV(GEN_REWRITE_CONV I [GSYM WORD_ADD_ASSOC] THENC
               RAND_CONV WORD_ADD_CONV))))) in
  let rec conv n tm =
    if n = 0 then REFL tm else
    (baseconv THENC BINOP_CONV (conv(n - 1))) tm in
  conv;;

let READ_MEMORY_SPLIT_CONV =
  let baseconv =
    GEN_REWRITE_CONV I [READ_MEMORY_BYTESIZED_UNSPLIT] THENC
    BINOP_CONV(LAND_CONV(LAND_CONV(RAND_CONV(RAND_CONV
     (TRY_CONV(GEN_REWRITE_CONV I [GSYM WORD_ADD_ASSOC] THENC
               RAND_CONV WORD_ADD_CONV)))))) in
  let rec conv n tm =
    if n = 0 then REFL tm else
    (baseconv THENC BINOP_CONV (conv(n - 1))) tm in
  conv;;

let SIMD_SIMPLIFY_CONV =
  TOP_DEPTH_CONV
   (REWR_CONV WORD_SUBWORD_AND ORELSEC WORD_SIMPLE_SUBWORD_CONV) THENC
  DEPTH_CONV WORD_NUM_RED_CONV THENC
  REWRITE_CONV[GSYM barred; GSYM barmul];;

let SIMD_SIMPLIFY_TAC =
  let simdable = can (term_match [] `read X (s:armstate):int128 = whatever`) in
  TRY(FIRST_X_ASSUM
   (ASSUME_TAC o
    CONV_RULE(RAND_CONV SIMD_SIMPLIFY_CONV) o
    check (simdable o concl)));;

let BYTES_LOADED_DATA = prove
 (`bytes_loaded s (word (pc + 0x514)) mlkem_ntt_data <=>
   read (memory :> bytes(word (pc + 0x514),944)) s =
   num_of_bytelist mlkem_ntt_data`,
  REWRITE_TAC[bytes_loaded; READ_BYTELIST_EQ_BYTES;
    CONV_RULE (RAND_CONV LENGTH_CONV)
     (AP_TERM `LENGTH:byte list->num` mlkem_ntt_data)]);;

let MLKEM_NTT_CORRECT = prove
 (`!a x pc.
      nonoverlapping (word pc,0x8c4) (a,512)
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc)
                  (APPEND mlkem_ntt_mc mlkem_ntt_data) /\
                read PC s = word (pc + 0x14) /\
                C_ARGUMENTS [a] s /\
                !i. i < 256
                    ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                        x i)
           (\s. read PC s = word(pc + 0x4fc) /\
                ((!i. i < 256 ==> abs(ival(x i)) <= &8191)
                 ==> !i. i < 256
                         ==> let zi =
                        read(memory :> bytes16(word_add a (word(2 * i)))) s in
                        (ival zi == forward_ntt (ival o x) i) (mod &3329) /\
                        abs(ival zi) <= &23594))
           (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
            MAYCHANGE [memory :> bytes(a,512)])`,
  MAP_EVERY X_GEN_TAC [`a:int64`; `x:num->int16`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** Fiddle around with the constant table stuff ***)

  REWRITE_TAC[ALIGNED_BYTES_LOADED_APPEND_CLAUSE] THEN
  REWRITE_TAC[fst MLKEM_NTT_EXEC] THEN REWRITE_TAC[BYTES_LOADED_DATA] THEN

  (*** Manually expand the cases in the hypotheses ***)

  CONV_TAC(RATOR_CONV(LAND_CONV(ONCE_DEPTH_CONV
   (EXPAND_CASES_CONV THENC ONCE_DEPTH_CONV NUM_MULT_CONV)))) THEN

  ENSURES_INIT_TAC "s0" THEN

  (*** Manually restructure to match the 128-bit loads. It would be nicer
   *** if the simulation machinery did this automatically.
   ***)

  MP_TAC(end_itlist CONJ (map (fun n -> READ_MEMORY_MERGE_CONV 3
            (subst[mk_small_numeral(16*n),`n:num`]
                  `read (memory :> bytes128(word_add a (word n))) s0`))
            (0--31))) THEN
  ASM_REWRITE_TAC[WORD_ADD_0] THEN
  DISCARD_MATCHING_ASSUMPTIONS [`read (memory :> bytes16 a) s = x`] THEN
  STRIP_TAC THEN

  (*** Palaver to address the precomputed tables via "wpc" ***)

  ASSUME_TAC(WORD_RULE
   `word(pc + 1316):int64 = word_add (word(pc + 0x514)) (word 16)`) THEN
  ASSUME_TAC(WORD_RULE
   `word(pc + 1348):int64 = word_add (word(pc + 0x514)) (word 48)`) THEN
  ASSUME_TAC(WORD_RULE
   `word(pc + 1476):int64 = word_add (word(pc + 0x514)) (word 176)`) THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM BYTES_LOADED_DATA]) THEN
  ABBREV_TAC `wpc:int64 = word(pc + 0x514)` THEN
  SUBST1_TAC(WORD_RULE `wpc:int64 = word(val wpc + 0)`) THEN
  REWRITE_TAC[mlkem_ntt_data] THEN CONV_TAC(LAND_CONV DATA64_CONV) THEN
  REWRITE_TAC[WORD_RULE `word(val x + n) = word_add x (word n)`] THEN
  REWRITE_TAC[bytes_loaded_nil] THEN STRIP_TAC THEN
  SUBGOAL_THEN `nonoverlapping (a:int64,512) (wpc:int64,944)` MP_TAC THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES] THENL
   [EXPAND_TAC "wpc" THEN NONOVERLAPPING_TAC;
    UNDISCH_THEN `word(pc + 0x514):int64 = wpc` (K ALL_TAC) THEN
    DISCH_TAC] THEN
  MP_TAC(end_itlist CONJ (map (fun n -> READ_MEMORY_MERGE_CONV 1
            (subst[mk_small_numeral(16*n),`n:num`]
                  `read (memory :> bytes128(word_add wpc (word n))) s0`))
            (0--60))) THEN
  ASM_REWRITE_TAC[WORD_ADD_0] THEN
  CONV_TAC(LAND_CONV(DEPTH_CONV WORD_NUM_RED_CONV)) THEN
  DISCARD_MATCHING_ASSUMPTIONS [`read (memory :> bytes64 a) s = x`] THEN
  STRIP_TAC THEN

  (*** Simulate all the way to the end, in effect unrolling loops ***)

  MAP_EVERY (fun n -> ARM_STEPS_TAC MLKEM_NTT_EXEC [n] THEN SIMD_SIMPLIFY_TAC)
            (1--902) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN

  (*** Reverse the restructuring by splitting the 128-bit words up ***)

  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o
  CONV_RULE SIMD_SIMPLIFY_CONV o
  CONV_RULE(READ_MEMORY_SPLIT_CONV 3) o
  check (can (term_match [] `read qqq s:int128 = xxx`) o concl))) THEN

  (*** Turn the conclusion into an explicit conjunction and split it up ***)

  DISCH_TAC THEN
  CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN REWRITE_TAC[INT_ABS_BOUNDS] THEN
  GEN_REWRITE_TAC (BINDER_CONV o RAND_CONV) [GSYM I_THM] THEN
  CONV_TAC(EXPAND_CASES_CONV THENC ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  ASM_REWRITE_TAC[I_THM; WORD_ADD_0] THEN DISCARD_STATE_TAC "s902" THEN

  (*** Get congruences and bounds for the result digits and finish ***)

  REPEAT(W(fun (asl,w) ->
     if length(conjuncts w) > 3 then CONJ_TAC else NO_TAC)) THEN
  FIRST_X_ASSUM(MP_TAC o CONV_RULE EXPAND_CASES_CONV) THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN
  DISCH_THEN(fun aboth ->
    W(MP_TAC o GEN_CONGBOUND_RULE (CONJUNCTS aboth) o
      rand o lhand o rator o lhand o snd)) THEN

  (MATCH_MP_TAC MONO_AND THEN CONJ_TAC THENL
     [MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] INT_CONG_TRANS) THEN
      CONV_TAC(ONCE_DEPTH_CONV FORWARD_NTT_CONV) THEN
      REWRITE_TAC[GSYM INT_REM_EQ; o_THM] THEN CONV_TAC INT_REM_DOWN_CONV THEN
      REWRITE_TAC[INT_REM_EQ] THEN
      REWRITE_TAC[REAL_INT_CONGRUENCE; INT_OF_NUM_EQ; ARITH_EQ] THEN
      REWRITE_TAC[GSYM REAL_OF_INT_CLAUSES] THEN
      CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN REAL_INTEGER_TAC;
      MATCH_MP_TAC(INT_ARITH
       `l':int <= l /\ u <= u'
        ==> l <= x /\ x <= u ==> l' <= x /\ x <= u'`) THEN
      CONV_TAC INT_REDUCE_CONV]));;

(*** Subroutine form, somewhat messy elaboration of the usual wrapper ***)

let MLKEM_NTT_SUBROUTINE_CORRECT = prove
 (`!a x pc stackpointer returnaddress.
      aligned 16 stackpointer /\
      ALL (nonoverlapping (word_sub stackpointer (word 64),64))
          [(word pc,0x8c4); (a,512)] /\
      nonoverlapping (word pc,0x8c4) (a,512)
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc)
                  (APPEND mlkem_ntt_mc mlkem_ntt_data) /\
                read PC s = word pc /\
                read SP s = stackpointer /\
                read X30 s = returnaddress /\
                C_ARGUMENTS [a] s /\
                !i. i < 256
                    ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                        x i)
           (\s. read PC s = returnaddress /\
                ((!i. i < 256 ==> abs(ival(x i)) <= &8191)
                 ==> !i. i < 256
                         ==> let zi =
                        read(memory :> bytes16(word_add a (word(2 * i)))) s in
                        (ival zi == forward_ntt (ival o x) i) (mod &3329) /\
                        abs(ival zi) <= &23594))
           (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [memory :> bytes(a,512);
                       memory :> bytes(word_sub stackpointer (word 64),64)])`,
  let TWEAK_CONV =
    ONCE_DEPTH_CONV let_CONV THENC
    ONCE_DEPTH_CONV EXPAND_CASES_CONV THENC
    ONCE_DEPTH_CONV NUM_MULT_CONV THENC
    PURE_REWRITE_CONV [WORD_ADD_0] in
  REWRITE_TAC[ALIGNED_BYTES_LOADED_APPEND_CLAUSE; BYTES_LOADED_DATA;
              fst MLKEM_NTT_EXEC] THEN
  CONV_TAC TWEAK_CONV THEN
  ARM_ADD_RETURN_STACK_TAC ~pre_post_nsteps:(5,5) MLKEM_NTT_EXEC
   (REWRITE_RULE[ALIGNED_BYTES_LOADED_APPEND_CLAUSE; BYTES_LOADED_DATA;
                 fst MLKEM_NTT_EXEC] (CONV_RULE TWEAK_CONV MLKEM_NTT_CORRECT))
    `[D8; D9; D10; D11; D12; D13; D14; D15]` 64);;
