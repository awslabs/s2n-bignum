(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Inverse number theoretic transform.                                       *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "arm/proofs/utils/mlkem.ml";;

(**** print_literal_from_elf "arm/mlkem/mlkem_intt.o";;
 ****)

let mlkem_intt_mc = define_assert_from_elf
 "mlkem_intt_mc" "arm/mlkem/mlkem_intt.o"
[
  0xd10103ff;       (* arm_SUB SP SP (rvalue (word 64)) *)
  0x6d0027e8;       (* arm_STP D8 D9 SP (Immediate_Offset (iword (&0))) *)
  0x6d012fea;       (* arm_STP D10 D11 SP (Immediate_Offset (iword (&16))) *)
  0x6d0237ec;       (* arm_STP D12 D13 SP (Immediate_Offset (iword (&32))) *)
  0x6d033fee;       (* arm_STP D14 D15 SP (Immediate_Offset (iword (&48))) *)
  0x5281a025;       (* arm_MOV W5 (rvalue (word 3329)) *)
  0x4e021ca7;       (* arm_INS_GEN Q7 W5 0 16 *)
  0x5289d7e5;       (* arm_MOV W5 (rvalue (word 20159)) *)
  0x4e061ca7;       (* arm_INS_GEN Q7 W5 16 16 *)
  0x52804005;       (* arm_MOV W5 (rvalue (word 512)) *)
  0x4e020cbd;       (* arm_DUP_GEN Q29 X5 16 128 *)
  0x52827605;       (* arm_MOV W5 (rvalue (word 5040)) *)
  0x4e020cbe;       (* arm_DUP_GEN Q30 X5 16 128 *)
  0xaa0003e3;       (* arm_MOV X3 X0 *)
  0xd2800104;       (* arm_MOV X4 (rvalue (word 8)) *)
  0x3dc00068;       (* arm_LDR Q8 X3 (Immediate_Offset (word 0)) *)
  0x3dc00469;       (* arm_LDR Q9 X3 (Immediate_Offset (word 16)) *)
  0x3dc0086a;       (* arm_LDR Q10 X3 (Immediate_Offset (word 32)) *)
  0x3dc00c6b;       (* arm_LDR Q11 X3 (Immediate_Offset (word 48)) *)
  0x6e7eb51b;       (* arm_SQRDMULH_VEC Q27 Q8 Q30 16 128 *)
  0x4e7d9d08;       (* arm_MUL_VEC Q8 Q8 Q29 16 128 *)
  0x6f474368;       (* arm_MLS_VEC Q8 Q27 (Q7 :> LANE_H 0) 16 128 *)
  0x6e7eb53b;       (* arm_SQRDMULH_VEC Q27 Q9 Q30 16 128 *)
  0x4e7d9d29;       (* arm_MUL_VEC Q9 Q9 Q29 16 128 *)
  0x6f474369;       (* arm_MLS_VEC Q9 Q27 (Q7 :> LANE_H 0) 16 128 *)
  0x6e7eb55b;       (* arm_SQRDMULH_VEC Q27 Q10 Q30 16 128 *)
  0x4e7d9d4a;       (* arm_MUL_VEC Q10 Q10 Q29 16 128 *)
  0x6f47436a;       (* arm_MLS_VEC Q10 Q27 (Q7 :> LANE_H 0) 16 128 *)
  0x6e7eb57b;       (* arm_SQRDMULH_VEC Q27 Q11 Q30 16 128 *)
  0x4e7d9d6b;       (* arm_MUL_VEC Q11 Q11 Q29 16 128 *)
  0x6f47436b;       (* arm_MLS_VEC Q11 Q27 (Q7 :> LANE_H 0) 16 128 *)
  0x3c840468;       (* arm_STR Q8 X3 (Postimmediate_Offset (word 64)) *)
  0x3c9d0069;       (* arm_STR Q9 X3 (Immediate_Offset (word 18446744073709551568)) *)
  0x3c9e006a;       (* arm_STR Q10 X3 (Immediate_Offset (word 18446744073709551584)) *)
  0x3c9f006b;       (* arm_STR Q11 X3 (Immediate_Offset (word 18446744073709551600)) *)
  0xf1000484;       (* arm_SUBS X4 X4 (rvalue (word 1)) *)
  0xb5fffd64;       (* arm_CBNZ X4 (word 2097068) *)
  0xaa0003e3;       (* arm_MOV X3 X0 *)
  0xd2800104;       (* arm_MOV X4 (rvalue (word 8)) *)
  0x3dc00c77;       (* arm_LDR Q23 X3 (Immediate_Offset (word 48)) *)
  0x3dc0087c;       (* arm_LDR Q28 X3 (Immediate_Offset (word 32)) *)
  0x3dc0046d;       (* arm_LDR Q13 X3 (Immediate_Offset (word 16)) *)
  0x3dc00064;       (* arm_LDR Q4 X3 (Immediate_Offset (word 0)) *)
  0x3dc00c59;       (* arm_LDR Q25 X2 (Immediate_Offset (word 48)) *)
  0x3dc01450;       (* arm_LDR Q16 X2 (Immediate_Offset (word 80)) *)
  0x3cc1042c;       (* arm_LDR Q12 X1 (Postimmediate_Offset (word 16)) *)
  0x4e976b96;       (* arm_TRN2 Q22 Q28 Q23 32 128 *)
  0x4e972b9d;       (* arm_TRN1 Q29 Q28 Q23 32 128 *)
  0x4e8d2886;       (* arm_TRN1 Q6 Q4 Q13 32 128 *)
  0x4e8d6892;       (* arm_TRN2 Q18 Q4 Q13 32 128 *)
  0x4edd68de;       (* arm_TRN2 Q30 Q6 Q29 64 128 *)
  0x4ed66a43;       (* arm_TRN2 Q3 Q18 Q22 64 128 *)
  0x4edd28c5;       (* arm_TRN1 Q5 Q6 Q29 64 128 *)
  0x3dc01049;       (* arm_LDR Q9 X2 (Immediate_Offset (word 64)) *)
  0x6e6387d4;       (* arm_SUB_VEC Q20 Q30 Q3 16 128 *)
  0x4ed62a5b;       (* arm_TRN1 Q27 Q18 Q22 64 128 *)
  0x4e6387c0;       (* arm_ADD_VEC Q0 Q30 Q3 16 128 *)
  0x6e70b68f;       (* arm_SQRDMULH_VEC Q15 Q20 Q16 16 128 *)
  0x4e7b84b6;       (* arm_ADD_VEC Q22 Q5 Q27 16 128 *)
  0x6e7b84b3;       (* arm_SUB_VEC Q19 Q5 Q27 16 128 *)
  0x4e699e9e;       (* arm_MUL_VEC Q30 Q20 Q9 16 128 *)
  0x3dc00851;       (* arm_LDR Q17 X2 (Immediate_Offset (word 32)) *)
  0x3cc60449;       (* arm_LDR Q9 X2 (Postimmediate_Offset (word 96)) *)
  0x6e79b665;       (* arm_SQRDMULH_VEC Q5 Q19 Q25 16 128 *)
  0x6e6086d2;       (* arm_SUB_VEC Q18 Q22 Q0 16 128 *)
  0x6f4741fe;       (* arm_MLS_VEC Q30 Q15 (Q7 :> LANE_H 0) 16 128 *)
  0x4e719e7a;       (* arm_MUL_VEC Q26 Q19 Q17 16 128 *)
  0x6f4740ba;       (* arm_MLS_VEC Q26 Q5 (Q7 :> LANE_H 0) 16 128 *)
  0x3cdb0045;       (* arm_LDR Q5 X2 (Immediate_Offset (word 18446744073709551536)) *)
  0x4e699e4e;       (* arm_MUL_VEC Q14 Q18 Q9 16 128 *)
  0x6e65b65c;       (* arm_SQRDMULH_VEC Q28 Q18 Q5 16 128 *)
  0x6e7e8751;       (* arm_SUB_VEC Q17 Q26 Q30 16 128 *)
  0x4e7e8755;       (* arm_ADD_VEC Q21 Q26 Q30 16 128 *)
  0x4e6086da;       (* arm_ADD_VEC Q26 Q22 Q0 16 128 *)
  0x6e65b625;       (* arm_SQRDMULH_VEC Q5 Q17 Q5 16 128 *)
  0x4e956b54;       (* arm_TRN2 Q20 Q26 Q21 32 128 *)
  0x6f47438e;       (* arm_MLS_VEC Q14 Q28 (Q7 :> LANE_H 0) 16 128 *)
  0x4e699e31;       (* arm_MUL_VEC Q17 Q17 Q9 16 128 *)
  0x6f4740b1;       (* arm_MLS_VEC Q17 Q5 (Q7 :> LANE_H 0) 16 128 *)
  0x4e952b52;       (* arm_TRN1 Q18 Q26 Q21 32 128 *)
  0x4e9169c5;       (* arm_TRN2 Q5 Q14 Q17 32 128 *)
  0x4e9129d0;       (* arm_TRN1 Q16 Q14 Q17 32 128 *)
  0x4ec56a9a;       (* arm_TRN2 Q26 Q20 Q5 64 128 *)
  0x4ed06a5e;       (* arm_TRN2 Q30 Q18 Q16 64 128 *)
  0x4ec52a9f;       (* arm_TRN1 Q31 Q20 Q5 64 128 *)
  0x4e7a87c8;       (* arm_ADD_VEC Q8 Q30 Q26 16 128 *)
  0x6e7a87d9;       (* arm_SUB_VEC Q25 Q30 Q26 16 128 *)
  0x4ed02a5a;       (* arm_TRN1 Q26 Q18 Q16 64 128 *)
  0x4f57c105;       (* arm_SQDMULH_VEC Q5 Q8 (Q7 :> LANE_H 1) 16 128 *)
  0x6e7f875d;       (* arm_SUB_VEC Q29 Q26 Q31 16 128 *)
  0x4e7f8756;       (* arm_ADD_VEC Q22 Q26 Q31 16 128 *)
  0x4f7cd3b4;       (* arm_SQRDMULH_VEC Q20 Q29 (Q12 :> LANE_H 3) 16 128 *)
  0x4f1524ad;       (* arm_SRSHR_VEC Q13 Q5 11 16 128 *)
  0x4f57c2df;       (* arm_SQDMULH_VEC Q31 Q22 (Q7 :> LANE_H 1) 16 128 *)
  0xd1000484;       (* arm_SUB X4 X4 (rvalue (word 1)) *)
  0x4f5cdb3c;       (* arm_SQRDMULH_VEC Q28 Q25 (Q12 :> LANE_H 5) 16 128 *)
  0x3dc00c58;       (* arm_LDR Q24 X2 (Immediate_Offset (word 48)) *)
  0x3dc01863;       (* arm_LDR Q3 X3 (Immediate_Offset (word 96)) *)
  0x3dc0144f;       (* arm_LDR Q15 X2 (Immediate_Offset (word 80)) *)
  0x3dc01c77;       (* arm_LDR Q23 X3 (Immediate_Offset (word 112)) *)
  0x4f4c8b2a;       (* arm_MUL_VEC Q10 Q25 (Q12 :> LANE_H 4) 16 128 *)
  0x3dc0106e;       (* arm_LDR Q14 X3 (Immediate_Offset (word 64)) *)
  0x3dc01464;       (* arm_LDR Q4 X3 (Immediate_Offset (word 80)) *)
  0x6f4741a8;       (* arm_MLS_VEC Q8 Q13 (Q7 :> LANE_H 0) 16 128 *)
  0x3dc0104d;       (* arm_LDR Q13 X2 (Immediate_Offset (word 64)) *)
  0x3cc60445;       (* arm_LDR Q5 X2 (Postimmediate_Offset (word 96)) *)
  0x4f1527f1;       (* arm_SRSHR_VEC Q17 Q31 11 16 128 *)
  0x4e972860;       (* arm_TRN1 Q0 Q3 Q23 32 128 *)
  0x4f6c83bb;       (* arm_MUL_VEC Q27 Q29 (Q12 :> LANE_H 2) 16 128 *)
  0x4e8429de;       (* arm_TRN1 Q30 Q14 Q4 32 128 *)
  0x4e8469da;       (* arm_TRN2 Q26 Q14 Q4 32 128 *)
  0x6f47429b;       (* arm_MLS_VEC Q27 Q20 (Q7 :> LANE_H 0) 16 128 *)
  0x4ec06bd5;       (* arm_TRN2 Q21 Q30 Q0 64 128 *)
  0x4e97686b;       (* arm_TRN2 Q11 Q3 Q23 32 128 *)
  0x6f47438a;       (* arm_MLS_VEC Q10 Q28 (Q7 :> LANE_H 0) 16 128 *)
  0x4ec02bd7;       (* arm_TRN1 Q23 Q30 Q0 64 128 *)
  0x3cdb0043;       (* arm_LDR Q3 X2 (Immediate_Offset (word 18446744073709551536)) *)
  0x6f474236;       (* arm_MLS_VEC Q22 Q17 (Q7 :> LANE_H 0) 16 128 *)
  0x4ecb2b5f;       (* arm_TRN1 Q31 Q26 Q11 64 128 *)
  0x4ecb6b50;       (* arm_TRN2 Q16 Q26 Q11 64 128 *)
  0x4e7f86ee;       (* arm_ADD_VEC Q14 Q23 Q31 16 128 *)
  0x4f57c364;       (* arm_SQDMULH_VEC Q4 Q27 (Q7 :> LANE_H 1) 16 128 *)
  0x3cdc005a;       (* arm_LDR Q26 X2 (Immediate_Offset (word 18446744073709551552)) *)
  0x4e7086bc;       (* arm_ADD_VEC Q28 Q21 Q16 16 128 *)
  0x6e7086b9;       (* arm_SUB_VEC Q25 Q21 Q16 16 128 *)
  0x4f57c155;       (* arm_SQDMULH_VEC Q21 Q10 (Q7 :> LANE_H 1) 16 128 *)
  0x6e7c85c1;       (* arm_SUB_VEC Q1 Q14 Q28 16 128 *)
  0x4e6d9f3d;       (* arm_MUL_VEC Q29 Q25 Q13 16 128 *)
  0x4e7c85c2;       (* arm_ADD_VEC Q2 Q14 Q28 16 128 *)
  0x4f152489;       (* arm_SRSHR_VEC Q9 Q4 11 16 128 *)
  0x6e7f86eb;       (* arm_SUB_VEC Q11 Q23 Q31 16 128 *)
  0x6e63b433;       (* arm_SQRDMULH_VEC Q19 Q1 Q3 16 128 *)
  0x4e6886df;       (* arm_ADD_VEC Q31 Q22 Q8 16 128 *)
  0x6e78b56d;       (* arm_SQRDMULH_VEC Q13 Q11 Q24 16 128 *)
  0x3c84047f;       (* arm_STR Q31 X3 (Postimmediate_Offset (word 64)) *)
  0x6e6fb73e;       (* arm_SQRDMULH_VEC Q30 Q25 Q15 16 128 *)
  0x4e7a9d60;       (* arm_MUL_VEC Q0 Q11 Q26 16 128 *)
  0x6f4741a0;       (* arm_MLS_VEC Q0 Q13 (Q7 :> LANE_H 0) 16 128 *)
  0x6e6886cd;       (* arm_SUB_VEC Q13 Q22 Q8 16 128 *)
  0x4f1526b6;       (* arm_SRSHR_VEC Q22 Q21 11 16 128 *)
  0x6f4743dd;       (* arm_MLS_VEC Q29 Q30 (Q7 :> LANE_H 0) 16 128 *)
  0x6f47413b;       (* arm_MLS_VEC Q27 Q9 (Q7 :> LANE_H 0) 16 128 *)
  0x6f4742ca;       (* arm_MLS_VEC Q10 Q22 (Q7 :> LANE_H 0) 16 128 *)
  0x4e659c29;       (* arm_MUL_VEC Q9 Q1 Q5 16 128 *)
  0x6e7d841c;       (* arm_SUB_VEC Q28 Q0 Q29 16 128 *)
  0x6e63b788;       (* arm_SQRDMULH_VEC Q8 Q28 Q3 16 128 *)
  0x4e6a877a;       (* arm_ADD_VEC Q26 Q27 Q10 16 128 *)
  0x4e659f94;       (* arm_MUL_VEC Q20 Q28 Q5 16 128 *)
  0x6e6a8771;       (* arm_SUB_VEC Q17 Q27 Q10 16 128 *)
  0x4e7d840a;       (* arm_ADD_VEC Q10 Q0 Q29 16 128 *)
  0x3c9d007a;       (* arm_STR Q26 X3 (Immediate_Offset (word 18446744073709551568)) *)
  0x6f474269;       (* arm_MLS_VEC Q9 Q19 (Q7 :> LANE_H 0) 16 128 *)
  0x6f474114;       (* arm_MLS_VEC Q20 Q8 (Q7 :> LANE_H 0) 16 128 *)
  0x4e8a6859;       (* arm_TRN2 Q25 Q2 Q10 32 128 *)
  0x4e8a2848;       (* arm_TRN1 Q8 Q2 Q10 32 128 *)
  0x4f5cd1a4;       (* arm_SQRDMULH_VEC Q4 Q13 (Q12 :> LANE_H 1) 16 128 *)
  0x4f4c81a0;       (* arm_MUL_VEC Q0 Q13 (Q12 :> LANE_H 0) 16 128 *)
  0x4e94292a;       (* arm_TRN1 Q10 Q9 Q20 32 128 *)
  0x4e94693a;       (* arm_TRN2 Q26 Q9 Q20 32 128 *)
  0x4f5cd22e;       (* arm_SQRDMULH_VEC Q14 Q17 (Q12 :> LANE_H 1) 16 128 *)
  0x4eca690b;       (* arm_TRN2 Q11 Q8 Q10 64 128 *)
  0x4f4c8222;       (* arm_MUL_VEC Q2 Q17 (Q12 :> LANE_H 0) 16 128 *)
  0x4eda2b3c;       (* arm_TRN1 Q28 Q25 Q26 64 128 *)
  0x3cc1042c;       (* arm_LDR Q12 X1 (Postimmediate_Offset (word 16)) *)
  0x4eda6b39;       (* arm_TRN2 Q25 Q25 Q26 64 128 *)
  0x4eca290a;       (* arm_TRN1 Q10 Q8 Q10 64 128 *)
  0x6f474080;       (* arm_MLS_VEC Q0 Q4 (Q7 :> LANE_H 0) 16 128 *)
  0x4e798568;       (* arm_ADD_VEC Q8 Q11 Q25 16 128 *)
  0x6f4741c2;       (* arm_MLS_VEC Q2 Q14 (Q7 :> LANE_H 0) 16 128 *)
  0x6e798579;       (* arm_SUB_VEC Q25 Q11 Q25 16 128 *)
  0x6e7c855d;       (* arm_SUB_VEC Q29 Q10 Q28 16 128 *)
  0x4e7c8556;       (* arm_ADD_VEC Q22 Q10 Q28 16 128 *)
  0x4f57c110;       (* arm_SQDMULH_VEC Q16 Q8 (Q7 :> LANE_H 1) 16 128 *)
  0x3c9e0060;       (* arm_STR Q0 X3 (Immediate_Offset (word 18446744073709551584)) *)
  0x4f7cd3b4;       (* arm_SQRDMULH_VEC Q20 Q29 (Q12 :> LANE_H 3) 16 128 *)
  0x3c9f0062;       (* arm_STR Q2 X3 (Immediate_Offset (word 18446744073709551600)) *)
  0x4f57c2df;       (* arm_SQDMULH_VEC Q31 Q22 (Q7 :> LANE_H 1) 16 128 *)
  0x4f15260d;       (* arm_SRSHR_VEC Q13 Q16 11 16 128 *)
  0xd1000484;       (* arm_SUB X4 X4 (rvalue (word 1)) *)
  0xb5fff584;       (* arm_CBNZ X4 (word 2096816) *)
  0x4f1527e6;       (* arm_SRSHR_VEC Q6 Q31 11 16 128 *)
  0x4f5cdb2b;       (* arm_SQRDMULH_VEC Q11 Q25 (Q12 :> LANE_H 5) 16 128 *)
  0x4f4c8b32;       (* arm_MUL_VEC Q18 Q25 (Q12 :> LANE_H 4) 16 128 *)
  0x4f6c83a5;       (* arm_MUL_VEC Q5 Q29 (Q12 :> LANE_H 2) 16 128 *)
  0x6f474172;       (* arm_MLS_VEC Q18 Q11 (Q7 :> LANE_H 0) 16 128 *)
  0x6f474285;       (* arm_MLS_VEC Q5 Q20 (Q7 :> LANE_H 0) 16 128 *)
  0x4f57c249;       (* arm_SQDMULH_VEC Q9 Q18 (Q7 :> LANE_H 1) 16 128 *)
  0x4f57c0a0;       (* arm_SQDMULH_VEC Q0 Q5 (Q7 :> LANE_H 1) 16 128 *)
  0x6f4740d6;       (* arm_MLS_VEC Q22 Q6 (Q7 :> LANE_H 0) 16 128 *)
  0x4f152539;       (* arm_SRSHR_VEC Q25 Q9 11 16 128 *)
  0x6f4741a8;       (* arm_MLS_VEC Q8 Q13 (Q7 :> LANE_H 0) 16 128 *)
  0x4f152414;       (* arm_SRSHR_VEC Q20 Q0 11 16 128 *)
  0x6f474332;       (* arm_MLS_VEC Q18 Q25 (Q7 :> LANE_H 0) 16 128 *)
  0x6f474285;       (* arm_MLS_VEC Q5 Q20 (Q7 :> LANE_H 0) 16 128 *)
  0x6e6886c2;       (* arm_SUB_VEC Q2 Q22 Q8 16 128 *)
  0x4e6886dd;       (* arm_ADD_VEC Q29 Q22 Q8 16 128 *)
  0x4f5cd05a;       (* arm_SQRDMULH_VEC Q26 Q2 (Q12 :> LANE_H 1) 16 128 *)
  0x3c84047d;       (* arm_STR Q29 X3 (Postimmediate_Offset (word 64)) *)
  0x4f4c8043;       (* arm_MUL_VEC Q3 Q2 (Q12 :> LANE_H 0) 16 128 *)
  0x6e7284a1;       (* arm_SUB_VEC Q1 Q5 Q18 16 128 *)
  0x4f5cd034;       (* arm_SQRDMULH_VEC Q20 Q1 (Q12 :> LANE_H 1) 16 128 *)
  0x4f4c802f;       (* arm_MUL_VEC Q15 Q1 (Q12 :> LANE_H 0) 16 128 *)
  0x6f474343;       (* arm_MLS_VEC Q3 Q26 (Q7 :> LANE_H 0) 16 128 *)
  0x6f47428f;       (* arm_MLS_VEC Q15 Q20 (Q7 :> LANE_H 0) 16 128 *)
  0x4e7284b8;       (* arm_ADD_VEC Q24 Q5 Q18 16 128 *)
  0x3c9e0063;       (* arm_STR Q3 X3 (Immediate_Offset (word 18446744073709551584)) *)
  0x3c9d0078;       (* arm_STR Q24 X3 (Immediate_Offset (word 18446744073709551568)) *)
  0x3c9f006f;       (* arm_STR Q15 X3 (Immediate_Offset (word 18446744073709551600)) *)
  0xd2800084;       (* arm_MOV X4 (rvalue (word 4)) *)
  0x3cc20420;       (* arm_LDR Q0 X1 (Postimmediate_Offset (word 32)) *)
  0x3cdf0021;       (* arm_LDR Q1 X1 (Immediate_Offset (word 18446744073709551600)) *)
  0x3dc0601c;       (* arm_LDR Q28 X0 (Immediate_Offset (word 384)) *)
  0x3dc0701a;       (* arm_LDR Q26 X0 (Immediate_Offset (word 448)) *)
  0x3dc05003;       (* arm_LDR Q3 X0 (Immediate_Offset (word 320)) *)
  0x3dc0400d;       (* arm_LDR Q13 X0 (Immediate_Offset (word 256)) *)
  0x6e7a8795;       (* arm_SUB_VEC Q21 Q28 Q26 16 128 *)
  0x4e7a8794;       (* arm_ADD_VEC Q20 Q28 Q26 16 128 *)
  0x6e6385ba;       (* arm_SUB_VEC Q26 Q13 Q3 16 128 *)
  0x4e6385a5;       (* arm_ADD_VEC Q5 Q13 Q3 16 128 *)
  0x4f51dabc;       (* arm_SQRDMULH_VEC Q28 Q21 (Q1 :> LANE_H 5) 16 128 *)
  0x6e7484a2;       (* arm_SUB_VEC Q2 Q5 Q20 16 128 *)
  0x4f61834b;       (* arm_MUL_VEC Q11 Q26 (Q1 :> LANE_H 2) 16 128 *)
  0x4f71d35a;       (* arm_SQRDMULH_VEC Q26 Q26 (Q1 :> LANE_H 3) 16 128 *)
  0x4f418aa4;       (* arm_MUL_VEC Q4 Q21 (Q1 :> LANE_H 4) 16 128 *)
  0x6f474384;       (* arm_MLS_VEC Q4 Q28 (Q7 :> LANE_H 0) 16 128 *)
  0x6f47434b;       (* arm_MLS_VEC Q11 Q26 (Q7 :> LANE_H 0) 16 128 *)
  0x4f50d85c;       (* arm_SQRDMULH_VEC Q28 Q2 (Q0 :> LANE_H 5) 16 128 *)
  0x6e648578;       (* arm_SUB_VEC Q24 Q11 Q4 16 128 *)
  0x4f408b06;       (* arm_MUL_VEC Q6 Q24 (Q0 :> LANE_H 4) 16 128 *)
  0xd1000484;       (* arm_SUB X4 X4 (rvalue (word 1)) *)
  0x4f50db18;       (* arm_SQRDMULH_VEC Q24 Q24 (Q0 :> LANE_H 5) 16 128 *)
  0x3dc0201d;       (* arm_LDR Q29 X0 (Immediate_Offset (word 128)) *)
  0x3dc03009;       (* arm_LDR Q9 X0 (Immediate_Offset (word 192)) *)
  0x3dc00013;       (* arm_LDR Q19 X0 (Immediate_Offset (word 0)) *)
  0x3dc01012;       (* arm_LDR Q18 X0 (Immediate_Offset (word 64)) *)
  0x4f408843;       (* arm_MUL_VEC Q3 Q2 (Q0 :> LANE_H 4) 16 128 *)
  0x4e7484b1;       (* arm_ADD_VEC Q17 Q5 Q20 16 128 *)
  0x6f474383;       (* arm_MLS_VEC Q3 Q28 (Q7 :> LANE_H 0) 16 128 *)
  0x4e6987a2;       (* arm_ADD_VEC Q2 Q29 Q9 16 128 *)
  0x6f474306;       (* arm_MLS_VEC Q6 Q24 (Q7 :> LANE_H 0) 16 128 *)
  0x6e728674;       (* arm_SUB_VEC Q20 Q19 Q18 16 128 *)
  0x4e728679;       (* arm_ADD_VEC Q25 Q19 Q18 16 128 *)
  0x6e6987b8;       (* arm_SUB_VEC Q24 Q29 Q9 16 128 *)
  0x4f608a8a;       (* arm_MUL_VEC Q10 Q20 (Q0 :> LANE_H 6) 16 128 *)
  0x6e62873b;       (* arm_SUB_VEC Q27 Q25 Q2 16 128 *)
  0x4e62872c;       (* arm_ADD_VEC Q12 Q25 Q2 16 128 *)
  0x4f70da93;       (* arm_SQRDMULH_VEC Q19 Q20 (Q0 :> LANE_H 7) 16 128 *)
  0x4e648575;       (* arm_ADD_VEC Q21 Q11 Q4 16 128 *)
  0x4f41830f;       (* arm_MUL_VEC Q15 Q24 (Q1 :> LANE_H 0) 16 128 *)
  0x6e718582;       (* arm_SUB_VEC Q2 Q12 Q17 16 128 *)
  0x4e718590;       (* arm_ADD_VEC Q16 Q12 Q17 16 128 *)
  0x4f608379;       (* arm_MUL_VEC Q25 Q27 (Q0 :> LANE_H 2) 16 128 *)
  0x4f51d318;       (* arm_SQRDMULH_VEC Q24 Q24 (Q1 :> LANE_H 1) 16 128 *)
  0x6f47426a;       (* arm_MLS_VEC Q10 Q19 (Q7 :> LANE_H 0) 16 128 *)
  0x4f50d045;       (* arm_SQRDMULH_VEC Q5 Q2 (Q0 :> LANE_H 1) 16 128 *)
  0x6f47430f;       (* arm_MLS_VEC Q15 Q24 (Q7 :> LANE_H 0) 16 128 *)
  0x3dc07418;       (* arm_LDR Q24 X0 (Immediate_Offset (word 464)) *)
  0x4f408044;       (* arm_MUL_VEC Q4 Q2 (Q0 :> LANE_H 0) 16 128 *)
  0x6f4740a4;       (* arm_MLS_VEC Q4 Q5 (Q7 :> LANE_H 0) 16 128 *)
  0x6e6f855c;       (* arm_SUB_VEC Q28 Q10 Q15 16 128 *)
  0x4f70d377;       (* arm_SQRDMULH_VEC Q23 Q27 (Q0 :> LANE_H 3) 16 128 *)
  0x4e6f855f;       (* arm_ADD_VEC Q31 Q10 Q15 16 128 *)
  0x6e7587f2;       (* arm_SUB_VEC Q18 Q31 Q21 16 128 *)
  0x4f60838a;       (* arm_MUL_VEC Q10 Q28 (Q0 :> LANE_H 2) 16 128 *)
  0x3d804004;       (* arm_STR Q4 X0 (Immediate_Offset (word 256)) *)
  0x3dc0640d;       (* arm_LDR Q13 X0 (Immediate_Offset (word 400)) *)
  0x4f50d24c;       (* arm_SQRDMULH_VEC Q12 Q18 (Q0 :> LANE_H 1) 16 128 *)
  0x3dc04411;       (* arm_LDR Q17 X0 (Immediate_Offset (word 272)) *)
  0x4e7587e9;       (* arm_ADD_VEC Q9 Q31 Q21 16 128 *)
  0x4f70d395;       (* arm_SQRDMULH_VEC Q21 Q28 (Q0 :> LANE_H 3) 16 128 *)
  0x3dc05404;       (* arm_LDR Q4 X0 (Immediate_Offset (word 336)) *)
  0x6f4742f9;       (* arm_MLS_VEC Q25 Q23 (Q7 :> LANE_H 0) 16 128 *)
  0x6e7885a8;       (* arm_SUB_VEC Q8 Q13 Q24 16 128 *)
  0x4f51d913;       (* arm_SQRDMULH_VEC Q19 Q8 (Q1 :> LANE_H 5) 16 128 *)
  0x6e64862e;       (* arm_SUB_VEC Q14 Q17 Q4 16 128 *)
  0x6f4742aa;       (* arm_MLS_VEC Q10 Q21 (Q7 :> LANE_H 0) 16 128 *)
  0x4e638737;       (* arm_ADD_VEC Q23 Q25 Q3 16 128 *)
  0x6e63873f;       (* arm_SUB_VEC Q31 Q25 Q3 16 128 *)
  0x4f6181cb;       (* arm_MUL_VEC Q11 Q14 (Q1 :> LANE_H 2) 16 128 *)
  0x4f50d3fb;       (* arm_SQRDMULH_VEC Q27 Q31 (Q0 :> LANE_H 1) 16 128 *)
  0x6e668542;       (* arm_SUB_VEC Q2 Q10 Q6 16 128 *)
  0x4e648625;       (* arm_ADD_VEC Q5 Q17 Q4 16 128 *)
  0x4f4083fd;       (* arm_MUL_VEC Q29 Q31 (Q0 :> LANE_H 0) 16 128 *)
  0x4e7885b4;       (* arm_ADD_VEC Q20 Q13 Q24 16 128 *)
  0x4e668555;       (* arm_ADD_VEC Q21 Q10 Q6 16 128 *)
  0x4f50d044;       (* arm_SQRDMULH_VEC Q4 Q2 (Q0 :> LANE_H 1) 16 128 *)
  0x4f408043;       (* arm_MUL_VEC Q3 Q2 (Q0 :> LANE_H 0) 16 128 *)
  0x6e7484a2;       (* arm_SUB_VEC Q2 Q5 Q20 16 128 *)
  0x4f71d1d8;       (* arm_SQRDMULH_VEC Q24 Q14 (Q1 :> LANE_H 3) 16 128 *)
  0x6f474083;       (* arm_MLS_VEC Q3 Q4 (Q7 :> LANE_H 0) 16 128 *)
  0x4f418904;       (* arm_MUL_VEC Q4 Q8 (Q1 :> LANE_H 4) 16 128 *)
  0x6f47430b;       (* arm_MLS_VEC Q11 Q24 (Q7 :> LANE_H 0) 16 128 *)
  0x6f47437d;       (* arm_MLS_VEC Q29 Q27 (Q7 :> LANE_H 0) 16 128 *)
  0x6f474264;       (* arm_MLS_VEC Q4 Q19 (Q7 :> LANE_H 0) 16 128 *)
  0x4f408251;       (* arm_MUL_VEC Q17 Q18 (Q0 :> LANE_H 0) 16 128 *)
  0x3d80601d;       (* arm_STR Q29 X0 (Immediate_Offset (word 384)) *)
  0x6f474191;       (* arm_MLS_VEC Q17 Q12 (Q7 :> LANE_H 0) 16 128 *)
  0x3d807003;       (* arm_STR Q3 X0 (Immediate_Offset (word 448)) *)
  0x3c810410;       (* arm_STR Q16 X0 (Postimmediate_Offset (word 16)) *)
  0x6e648578;       (* arm_SUB_VEC Q24 Q11 Q4 16 128 *)
  0x3d800c09;       (* arm_STR Q9 X0 (Immediate_Offset (word 48)) *)
  0x4f50d85c;       (* arm_SQRDMULH_VEC Q28 Q2 (Q0 :> LANE_H 5) 16 128 *)
  0x3d801c17;       (* arm_STR Q23 X0 (Immediate_Offset (word 112)) *)
  0x3d802c15;       (* arm_STR Q21 X0 (Immediate_Offset (word 176)) *)
  0x4f408b06;       (* arm_MUL_VEC Q6 Q24 (Q0 :> LANE_H 4) 16 128 *)
  0x3d804c11;       (* arm_STR Q17 X0 (Immediate_Offset (word 304)) *)
  0xd1000484;       (* arm_SUB X4 X4 (rvalue (word 1)) *)
  0xb5fff664;       (* arm_CBNZ X4 (word 2096844) *)
  0x3dc00009;       (* arm_LDR Q9 X0 (Immediate_Offset (word 0)) *)
  0x4f50db19;       (* arm_SQRDMULH_VEC Q25 Q24 (Q0 :> LANE_H 5) 16 128 *)
  0x3dc03015;       (* arm_LDR Q21 X0 (Immediate_Offset (word 192)) *)
  0x3dc01010;       (* arm_LDR Q16 X0 (Immediate_Offset (word 64)) *)
  0x4f40885e;       (* arm_MUL_VEC Q30 Q2 (Q0 :> LANE_H 4) 16 128 *)
  0x3dc02011;       (* arm_LDR Q17 X0 (Immediate_Offset (word 128)) *)
  0x6f47439e;       (* arm_MLS_VEC Q30 Q28 (Q7 :> LANE_H 0) 16 128 *)
  0x4e70852f;       (* arm_ADD_VEC Q15 Q9 Q16 16 128 *)
  0x6e758632;       (* arm_SUB_VEC Q18 Q17 Q21 16 128 *)
  0x6f474326;       (* arm_MLS_VEC Q6 Q25 (Q7 :> LANE_H 0) 16 128 *)
  0x4e758633;       (* arm_ADD_VEC Q19 Q17 Q21 16 128 *)
  0x6e70852e;       (* arm_SUB_VEC Q14 Q9 Q16 16 128 *)
  0x4f418248;       (* arm_MUL_VEC Q8 Q18 (Q1 :> LANE_H 0) 16 128 *)
  0x4e7385fb;       (* arm_ADD_VEC Q27 Q15 Q19 16 128 *)
  0x4f70d9d6;       (* arm_SQRDMULH_VEC Q22 Q14 (Q0 :> LANE_H 7) 16 128 *)
  0x4f51d243;       (* arm_SQRDMULH_VEC Q3 Q18 (Q1 :> LANE_H 1) 16 128 *)
  0x4e648570;       (* arm_ADD_VEC Q16 Q11 Q4 16 128 *)
  0x4f6089dd;       (* arm_MUL_VEC Q29 Q14 (Q0 :> LANE_H 6) 16 128 *)
  0x6f4742dd;       (* arm_MLS_VEC Q29 Q22 (Q7 :> LANE_H 0) 16 128 *)
  0x6e7385f6;       (* arm_SUB_VEC Q22 Q15 Q19 16 128 *)
  0x4e7484ba;       (* arm_ADD_VEC Q26 Q5 Q20 16 128 *)
  0x6f474068;       (* arm_MLS_VEC Q8 Q3 (Q7 :> LANE_H 0) 16 128 *)
  0x6e7a8775;       (* arm_SUB_VEC Q21 Q27 Q26 16 128 *)
  0x4e7a8778;       (* arm_ADD_VEC Q24 Q27 Q26 16 128 *)
  0x4f70d2d7;       (* arm_SQRDMULH_VEC Q23 Q22 (Q0 :> LANE_H 3) 16 128 *)
  0x3c810418;       (* arm_STR Q24 X0 (Postimmediate_Offset (word 16)) *)
  0x4f6082cd;       (* arm_MUL_VEC Q13 Q22 (Q0 :> LANE_H 2) 16 128 *)
  0x6e6887b9;       (* arm_SUB_VEC Q25 Q29 Q8 16 128 *)
  0x4e6887b2;       (* arm_ADD_VEC Q18 Q29 Q8 16 128 *)
  0x4f4082ae;       (* arm_MUL_VEC Q14 Q21 (Q0 :> LANE_H 0) 16 128 *)
  0x4e70865a;       (* arm_ADD_VEC Q26 Q18 Q16 16 128 *)
  0x4f70d33f;       (* arm_SQRDMULH_VEC Q31 Q25 (Q0 :> LANE_H 3) 16 128 *)
  0x6f4742ed;       (* arm_MLS_VEC Q13 Q23 (Q7 :> LANE_H 0) 16 128 *)
  0x3d800c1a;       (* arm_STR Q26 X0 (Immediate_Offset (word 48)) *)
  0x6e70864c;       (* arm_SUB_VEC Q12 Q18 Q16 16 128 *)
  0x4f608322;       (* arm_MUL_VEC Q2 Q25 (Q0 :> LANE_H 2) 16 128 *)
  0x6f4743e2;       (* arm_MLS_VEC Q2 Q31 (Q7 :> LANE_H 0) 16 128 *)
  0x4f40818a;       (* arm_MUL_VEC Q10 Q12 (Q0 :> LANE_H 0) 16 128 *)
  0x6e7e85a3;       (* arm_SUB_VEC Q3 Q13 Q30 16 128 *)
  0x4e7e85b3;       (* arm_ADD_VEC Q19 Q13 Q30 16 128 *)
  0x4f50d07c;       (* arm_SQRDMULH_VEC Q28 Q3 (Q0 :> LANE_H 1) 16 128 *)
  0x6e668452;       (* arm_SUB_VEC Q18 Q2 Q6 16 128 *)
  0x3d801c13;       (* arm_STR Q19 X0 (Immediate_Offset (word 112)) *)
  0x4f50d197;       (* arm_SQRDMULH_VEC Q23 Q12 (Q0 :> LANE_H 1) 16 128 *)
  0x4e66845a;       (* arm_ADD_VEC Q26 Q2 Q6 16 128 *)
  0x4f50d251;       (* arm_SQRDMULH_VEC Q17 Q18 (Q0 :> LANE_H 1) 16 128 *)
  0x4f50d2be;       (* arm_SQRDMULH_VEC Q30 Q21 (Q0 :> LANE_H 1) 16 128 *)
  0x6f4742ea;       (* arm_MLS_VEC Q10 Q23 (Q7 :> LANE_H 0) 16 128 *)
  0x4f408252;       (* arm_MUL_VEC Q18 Q18 (Q0 :> LANE_H 0) 16 128 *)
  0x3d802c1a;       (* arm_STR Q26 X0 (Immediate_Offset (word 176)) *)
  0x6f4743ce;       (* arm_MLS_VEC Q14 Q30 (Q7 :> LANE_H 0) 16 128 *)
  0x3d804c0a;       (* arm_STR Q10 X0 (Immediate_Offset (word 304)) *)
  0x6f474232;       (* arm_MLS_VEC Q18 Q17 (Q7 :> LANE_H 0) 16 128 *)
  0x4f408077;       (* arm_MUL_VEC Q23 Q3 (Q0 :> LANE_H 0) 16 128 *)
  0x3d803c0e;       (* arm_STR Q14 X0 (Immediate_Offset (word 240)) *)
  0x6f474397;       (* arm_MLS_VEC Q23 Q28 (Q7 :> LANE_H 0) 16 128 *)
  0x3d806c12;       (* arm_STR Q18 X0 (Immediate_Offset (word 432)) *)
  0x3d805c17;       (* arm_STR Q23 X0 (Immediate_Offset (word 368)) *)
  0x6d4027e8;       (* arm_LDP D8 D9 SP (Immediate_Offset (iword (&0))) *)
  0x6d412fea;       (* arm_LDP D10 D11 SP (Immediate_Offset (iword (&16))) *)
  0x6d4237ec;       (* arm_LDP D12 D13 SP (Immediate_Offset (iword (&32))) *)
  0x6d433fee;       (* arm_LDP D14 D15 SP (Immediate_Offset (iword (&48))) *)
  0x910103ff;       (* arm_ADD SP SP (rvalue (word 64)) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let MLKEM_INTT_EXEC = ARM_MK_EXEC_RULE mlkem_intt_mc;;

(* ------------------------------------------------------------------------- *)
(* Data tables that are assumed in the precondition.                         *)
(* ------------------------------------------------------------------------- *)

let intt_zetas_layer01234 = define
 `intt_zetas_layer01234:int list =
   [&1583; &15582; -- &821; -- &8081; &1355; &13338; &0; &0; -- &569; -- &5601;
    &450; &4429; &936; &9213; &0; &0; &69; &679; &447; &4400; -- &535;
    -- &5266; &0; &0; &543; &5345; &1235; &12156; -- &1426; -- &14036; &0;
    &0; -- &797; -- &7845; -- &1333; -- &13121; &1089; &10719; &0; &0;
    -- &193; -- &1900; -- &56; -- &551; &283; &2786; &0; &0; &1410; &13879;
    -- &1476; -- &14529; -- &1339; -- &13180; &0; &0; -- &1062; -- &10453;
    &882; &8682; -- &296; -- &2914; &0; &0; &1600; &15749; &40; &394;
    &749; &7373; -- &848; -- &8347; &1432; &14095; -- &630; -- &6201;
    &687; &6762; &0; &0]`;;

let intt_zetas_layer56 = define
 `intt_zetas_layer56:int list =
   [-- &910; -- &910; -- &1227; -- &1227; &219; &219; &855; &855; -- &8957;
    -- &8957; -- &12078; -- &12078; &2156; &2156; &8416; &8416; &1175;
    &1175; &394; &394; -- &1029; -- &1029; -- &1212; -- &1212; &11566;
    &11566; &3878; &3878; -- &10129; -- &10129; -- &11930; -- &11930;
    -- &885; -- &885; &1219; &1219; &1455; &1455; &1607; &1607; -- &8711;
    -- &8711; &11999; &11999; &14322; &14322; &15818; &15818; -- &648;
    -- &648; -- &1481; -- &1481; &712; &712; &682; &682; -- &6378; -- &6378;
    -- &14578; -- &14578; &7008; &7008; &6713; &6713; -- &886; -- &886;
    &1179; &1179; -- &1026; -- &1026; -- &1092; -- &1092; -- &8721;
    -- &8721; &11605; &11605; -- &10099; -- &10099; -- &10749; -- &10749;
    &554; &554; -- &1143; -- &1143; -- &403; -- &403; &525; &525; &5453;
    &5453; -- &11251; -- &11251; -- &3967; -- &3967; &5168; &5168; &927;
    &927; -- &1534; -- &1534; &461; &461; -- &1438; -- &1438; &9125;
    &9125; -- &15099; -- &15099; &4538; &4538; -- &14155; -- &14155; &735;
    &735; -- &561; -- &561; -- &757; -- &757; -- &319; -- &319; &7235;
    &7235; -- &5522; -- &5522; -- &7451; -- &7451; -- &3140; -- &3140;
    &863; &863; &1230; &1230; &556; &556; -- &1063; -- &1063; &8495;
    &8495; &12107; &12107; &5473; &5473; -- &10463; -- &10463; -- &452;
    -- &452; -- &807; -- &807; -- &1435; -- &1435; &1010; &1010; -- &4449;
    -- &4449; -- &7943; -- &7943; -- &14125; -- &14125; &9942; &9942;
    -- &1645; -- &1645; &780; &780; &109; &109; &1031; &1031; -- &16192;
    -- &16192; &7678; &7678; &1073; &1073; &10148; &10148; &1239; &1239;
    -- &375; -- &375; &1292; &1292; -- &1584; -- &1584; &12196; &12196;
    -- &3691; -- &3691; &12717; &12717; -- &15592; -- &15592; &1414; &1414;
    -- &1320; -- &1320; -- &33; -- &33; &464; &464; &13918; &13918;
    -- &12993; -- &12993; -- &325; -- &325; &4567; &4567; -- &641; -- &641;
    &992; &992; &941; &941; &1021; &1021; -- &6309; -- &6309; &9764;
    &9764; &9262; &9262; &10050; &10050; -- &268; -- &268; -- &733;
    -- &733; &892; &892; -- &939; -- &939; -- &2638; -- &2638; -- &7215;
    -- &7215; &8780; &8780; -- &9243; -- &9243; -- &632; -- &632; &816; &816;
    &1352; &1352; -- &650; -- &650; -- &6221; -- &6221; &8032; &8032;
    &13308; &13308; -- &6398; -- &6398; &642; &642; -- &952; -- &952;
    &1540; &1540; -- &1651; -- &1651; &6319; &6319; -- &9371; -- &9371;
    &15159; &15159; -- &16251; -- &16251; -- &1461; -- &1461; &1482;
    &1482; &540; &540; &1626; &1626; -- &14381; -- &14381; &14588; &14588;
    &5315; &5315; &16005; &16005; &1274; &1274; &1052; &1052; &1025;
    &1025; -- &1197; -- &1197; &12540; &12540; &10355; &10355; &10089;
    &10089; -- &11782; -- &11782; &279; &279; &1173; &1173; -- &233;
    -- &233; &667; &667; &2746; &2746; &11546; &11546; -- &2293; -- &2293;
    &6565; &6565; &314; &314; -- &756; -- &756; &48; &48; -- &1409;
    -- &1409; &3091; &3091; -- &7441; -- &7441; &472; &472; -- &13869;
    -- &13869; &1573; &1573; &76; &76; -- &331; -- &331; -- &289; -- &289;
    &15483; &15483; &748; &748; -- &3258; -- &3258; -- &2845; -- &2845;
    -- &1100; -- &1100; -- &723; -- &723; &680; &680; &568; &568; -- &10828;
    -- &10828; -- &7117; -- &7117; &6693; &6693; &5591; &5591; &1041;
    &1041; -- &1637; -- &1637; -- &583; -- &583; -- &17; -- &17; &10247;
    &10247; -- &16113; -- &16113; -- &5739; -- &5739; -- &167; -- &167]`;;

let intt_constants = define
 `intt_constants z_01234 z_56 s <=>
        (!i. i < 80
             ==> read(memory :> bytes16(word_add z_01234 (word(2 * i)))) s =
                 iword(EL i intt_zetas_layer01234)) /\
        (!i. i < 384
             ==> read(memory :> bytes16(word_add z_56 (word(2 * i)))) s =
                 iword(EL i intt_zetas_layer56))`;;

(* ------------------------------------------------------------------------- *)
(* Some convenient proof tools.                                              *)
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

let MEMORY_128_FROM_16_TAC =
  let a_tm = `a:int64` and n_tm = `n:num` and i64_ty = `:int64`
  and pat = `read (memory :> bytes128(word_add a (word n))) s0` in
  fun v n ->
    let pat' = subst[mk_var(v,i64_ty),a_tm] pat in
    let f i =
      let itm = mk_small_numeral(16*i) in
      READ_MEMORY_MERGE_CONV 3 (subst[itm,n_tm] pat') in
    MP_TAC(end_itlist CONJ (map f (0--(n-1))));;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let MLKEM_INTT_CORRECT = prove
 (`!a z_01234 z_56 x pc.
      ALL (nonoverlapping (a,512))
          [(word pc,0x5d0); (z_01234,160); (z_56,768)]
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) mlkem_intt_mc /\
                read PC s = word (pc + 0x14) /\
                C_ARGUMENTS [a; z_01234; z_56] s /\
                intt_constants z_01234 z_56 s /\
                !i. i < 256
                    ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                        x i)
           (\s. read PC s = word(pc + 0x5b8) /\
                !i. i < 256
                    ==> let zi =
                         read(memory :> bytes16(word_add a (word(2 * i)))) s in
                        (ival zi == inverse_ntt (ival o x) i) (mod &3329) /\
                        abs(ival zi) <= &26624)
           (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
            MAYCHANGE [memory :> bytes(a,512)])`,
  MAP_EVERY X_GEN_TAC
   [`a:int64`; `z_01234:int64`; `z_56:int64`; `x:num->int16`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; ALL] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** Manually expand the cases in the hypotheses ***)

  REWRITE_TAC[intt_constants] THEN
  CONV_TAC(RATOR_CONV(LAND_CONV(ONCE_DEPTH_CONV
   (EXPAND_CASES_CONV THENC ONCE_DEPTH_CONV NUM_MULT_CONV)))) THEN
  REWRITE_TAC[intt_zetas_layer01234; intt_zetas_layer56] THEN
  CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV WORD_IWORD_CONV) THEN REWRITE_TAC[WORD_ADD_0] THEN
  ENSURES_INIT_TAC "s0" THEN

  (*** Manually restructure to match the 128-bit loads. It would be nicer
   *** if the simulation machinery did this automatically.
   ***)

  MEMORY_128_FROM_16_TAC "a" 32 THEN
  MEMORY_128_FROM_16_TAC "z_01234" 10 THEN
  MEMORY_128_FROM_16_TAC "z_56" 48 THEN
  ASM_REWRITE_TAC[WORD_ADD_0] THEN CONV_TAC WORD_REDUCE_CONV THEN
  DISCARD_MATCHING_ASSUMPTIONS [`read (memory :> bytes16 a) s = x`] THEN
  REPEAT STRIP_TAC THEN

  (*** Ghost up initial contents of Q7 since it isn't fully initialized ***)

  ABBREV_TAC `v7_init:int128 = read Q7 s0` THEN

  (*** Simulate all the way to the end, in effect unrolling loops ***)

  MAP_EVERY (fun n -> ARM_STEPS_TAC MLKEM_INTT_EXEC [n] THEN SIMD_SIMPLIFY_TAC)
            (1--1181) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN

  (*** Reverse the restructuring by splitting the 128-bit words up ***)

  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o
   CONV_RULE SIMD_SIMPLIFY_CONV o
   CONV_RULE(READ_MEMORY_SPLIT_CONV 3) o
   check (can (term_match [] `read qqq s:int128 = xxx`) o concl))) THEN

  (*** Turn the conclusion into an explicit conjunction and split it up ***)

  CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN REWRITE_TAC[INT_ABS_BOUNDS] THEN
  GEN_REWRITE_TAC (BINDER_CONV o RAND_CONV) [GSYM I_THM] THEN
  CONV_TAC(EXPAND_CASES_CONV THENC ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  ASM_REWRITE_TAC[I_THM; WORD_ADD_0] THEN DISCARD_STATE_TAC "s1181" THEN
  REPEAT(W(fun (asl,w) ->
     if length(conjuncts w) > 3 then CONJ_TAC else NO_TAC)) THEN

  (*** Get congruences and bounds for the result digits and finish ***)

  (W(MP_TAC o CONGBOUND_RULE o rand o lhand o rator o lhand o snd) THEN
    MATCH_MP_TAC MONO_AND THEN CONJ_TAC THENL
     [MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] INT_CONG_TRANS) THEN
      CONV_TAC(ONCE_DEPTH_CONV INVERSE_NTT_CONV) THEN
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

let MLKEM_INTT_SUBROUTINE_CORRECT = prove
 (`!a z_01234 z_56 x pc stackpointer returnaddress.
      aligned 16 stackpointer /\
      ALLPAIRS nonoverlapping
       [(a,512); (word_sub stackpointer (word 64),64)]
       [(word pc,0x5d0); (z_01234,160); (z_56,768)] /\
      nonoverlapping (a,512) (word_sub stackpointer (word 64),64)
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) mlkem_intt_mc /\
                read PC s = word pc /\
                read SP s = stackpointer /\
                read X30 s = returnaddress /\
                C_ARGUMENTS [a; z_01234; z_56] s /\
                intt_constants z_01234 z_56 s /\
                !i. i < 256
                    ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                        x i)
           (\s. read PC s = returnaddress /\
                !i. i < 256
                    ==> let zi =
                         read(memory :> bytes16(word_add a (word(2 * i)))) s in
                        (ival zi == inverse_ntt (ival o x) i) (mod &3329) /\
                        abs(ival zi) <= &26624)
           (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [memory :> bytes(a,512);
                       memory :> bytes(word_sub stackpointer (word 64),64)])`,
  let TWEAK_CONV =
    REWRITE_CONV[intt_constants] THENC
    ONCE_DEPTH_CONV let_CONV THENC
    ONCE_DEPTH_CONV EXPAND_CASES_CONV THENC
    ONCE_DEPTH_CONV NUM_MULT_CONV THENC
    PURE_REWRITE_CONV [WORD_ADD_0] in
  REWRITE_TAC[fst MLKEM_INTT_EXEC] THEN
  CONV_TAC TWEAK_CONV THEN
  ARM_ADD_RETURN_STACK_TAC ~pre_post_nsteps:(5,5) MLKEM_INTT_EXEC
   (REWRITE_RULE[fst MLKEM_INTT_EXEC] (CONV_RULE TWEAK_CONV MLKEM_INTT_CORRECT))
    `[D8; D9; D10; D11; D12; D13; D14; D15]` 64);;
