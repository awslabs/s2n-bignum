(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Inverse number theoretic transform.                                       *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "arm/proofs/utils/mlkem.ml";;

(**** print_coda_from_elf (-1) "arm/mlkem/mlkem_intt.o";;
 ****)

let mlkem_intt_mc,mlkem_intt_data = define_coda_literal_from_elf
  "mlkem_intt_mc" "mlkem_intt_data" "arm/mlkem/mlkem_intt.o"
[
  0xd10103ff;       (* arm_SUB SP SP (rvalue (word 64)) *)
  0x6d0027e8;       (* arm_STP D8 D9 SP (Immediate_Offset (word 0)) *)
  0x6d012fea;       (* arm_STP D10 D11 SP (Immediate_Offset (word 16)) *)
  0x6d0237ec;       (* arm_STP D12 D13 SP (Immediate_Offset (word 32)) *)
  0x6d033fee;       (* arm_STP D14 D15 SP (Immediate_Offset (word 48)) *)
  0x10004641;       (* arm_ADR X1 (word 2248) *)
  0x10002e22;       (* arm_ADR X2 (word 1476) *)
  0x4e020fe7;       (* arm_DUP_GEN Q7 XZR 16 128 *)
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
  0x3dc0087b;       (* arm_LDR Q27 X3 (Immediate_Offset (word 32)) *)
  0x3dc00c6d;       (* arm_LDR Q13 X3 (Immediate_Offset (word 48)) *)
  0x3dc00062;       (* arm_LDR Q2 X3 (Immediate_Offset (word 0)) *)
  0x3dc0047c;       (* arm_LDR Q28 X3 (Immediate_Offset (word 16)) *)
  0x3dc00c49;       (* arm_LDR Q9 X2 (Immediate_Offset (word 48)) *)
  0x3dc00456;       (* arm_LDR Q22 X2 (Immediate_Offset (word 16)) *)
  0x3dc01051;       (* arm_LDR Q17 X2 (Immediate_Offset (word 64)) *)
  0x3dc0144e;       (* arm_LDR Q14 X2 (Immediate_Offset (word 80)) *)
  0x4e8d2b77;       (* arm_TRN1 Q23 Q27 Q13 32 128 *)
  0x4e8d6b7b;       (* arm_TRN2 Q27 Q27 Q13 32 128 *)
  0x4e9c284d;       (* arm_TRN1 Q13 Q2 Q28 32 128 *)
  0x4e9c6842;       (* arm_TRN2 Q2 Q2 Q28 32 128 *)
  0x3dc0085c;       (* arm_LDR Q28 X2 (Immediate_Offset (word 32)) *)
  0x3cc60444;       (* arm_LDR Q4 X2 (Postimmediate_Offset (word 96)) *)
  0x4ed769b8;       (* arm_TRN2 Q24 Q13 Q23 64 128 *)
  0x4edb684f;       (* arm_TRN2 Q15 Q2 Q27 64 128 *)
  0x4ed729ad;       (* arm_TRN1 Q13 Q13 Q23 64 128 *)
  0x4edb285b;       (* arm_TRN1 Q27 Q2 Q27 64 128 *)
  0x4e6f8702;       (* arm_ADD_VEC Q2 Q24 Q15 16 128 *)
  0x6e6f8717;       (* arm_SUB_VEC Q23 Q24 Q15 16 128 *)
  0x4e7b85b8;       (* arm_ADD_VEC Q24 Q13 Q27 16 128 *)
  0x6e7b85bb;       (* arm_SUB_VEC Q27 Q13 Q27 16 128 *)
  0x3cc1042f;       (* arm_LDR Q15 X1 (Postimmediate_Offset (word 16)) *)
  0x4e719ef1;       (* arm_MUL_VEC Q17 Q23 Q17 16 128 *)
  0x6e69b76d;       (* arm_SQRDMULH_VEC Q13 Q27 Q9 16 128 *)
  0x6e6eb6ee;       (* arm_SQRDMULH_VEC Q14 Q23 Q14 16 128 *)
  0x4e7c9f7b;       (* arm_MUL_VEC Q27 Q27 Q28 16 128 *)
  0x6f4741bb;       (* arm_MLS_VEC Q27 Q13 (Q7 :> LANE_H 0) 16 128 *)
  0x6e628709;       (* arm_SUB_VEC Q9 Q24 Q2 16 128 *)
  0x6f4741d1;       (* arm_MLS_VEC Q17 Q14 (Q7 :> LANE_H 0) 16 128 *)
  0x6e76b52d;       (* arm_SQRDMULH_VEC Q13 Q9 Q22 16 128 *)
  0x4e628702;       (* arm_ADD_VEC Q2 Q24 Q2 16 128 *)
  0x4e649d3c;       (* arm_MUL_VEC Q28 Q9 Q4 16 128 *)
  0x6e718769;       (* arm_SUB_VEC Q9 Q27 Q17 16 128 *)
  0x4e71877b;       (* arm_ADD_VEC Q27 Q27 Q17 16 128 *)
  0x6e76b536;       (* arm_SQRDMULH_VEC Q22 Q9 Q22 16 128 *)
  0x4e9b2851;       (* arm_TRN1 Q17 Q2 Q27 32 128 *)
  0x4e649d29;       (* arm_MUL_VEC Q9 Q9 Q4 16 128 *)
  0x4e9b684a;       (* arm_TRN2 Q10 Q2 Q27 32 128 *)
  0x6f4741bc;       (* arm_MLS_VEC Q28 Q13 (Q7 :> LANE_H 0) 16 128 *)
  0x6f4742c9;       (* arm_MLS_VEC Q9 Q22 (Q7 :> LANE_H 0) 16 128 *)
  0x4e896b82;       (* arm_TRN2 Q2 Q28 Q9 32 128 *)
  0x4e892b8d;       (* arm_TRN1 Q13 Q28 Q9 32 128 *)
  0x4ecd6a36;       (* arm_TRN2 Q22 Q17 Q13 64 128 *)
  0x4ec2695c;       (* arm_TRN2 Q28 Q10 Q2 64 128 *)
  0x4ecd2a29;       (* arm_TRN1 Q9 Q17 Q13 64 128 *)
  0x6e7c86db;       (* arm_SUB_VEC Q27 Q22 Q28 16 128 *)
  0x4ec22952;       (* arm_TRN1 Q18 Q10 Q2 64 128 *)
  0x4e7c86ce;       (* arm_ADD_VEC Q14 Q22 Q28 16 128 *)
  0x4f5fdb74;       (* arm_SQRDMULH_VEC Q20 Q27 (Q15 :> LANE_H 5) 16 128 *)
  0x4f4f8b75;       (* arm_MUL_VEC Q21 Q27 (Q15 :> LANE_H 4) 16 128 *)
  0xd1000484;       (* arm_SUB X4 X4 (rvalue (word 1)) *)
  0x4f57c1d7;       (* arm_SQDMULH_VEC Q23 Q14 (Q7 :> LANE_H 1) 16 128 *)
  0x6e72853a;       (* arm_SUB_VEC Q26 Q9 Q18 16 128 *)
  0x3dc01866;       (* arm_LDR Q6 X3 (Immediate_Offset (word 96)) *)
  0x3dc01c7c;       (* arm_LDR Q28 X3 (Immediate_Offset (word 112)) *)
  0x6f474295;       (* arm_MLS_VEC Q21 Q20 (Q7 :> LANE_H 0) 16 128 *)
  0x3dc0106b;       (* arm_LDR Q11 X3 (Immediate_Offset (word 64)) *)
  0x3dc01465;       (* arm_LDR Q5 X3 (Immediate_Offset (word 80)) *)
  0x3dc00459;       (* arm_LDR Q25 X2 (Immediate_Offset (word 16)) *)
  0x4e72852d;       (* arm_ADD_VEC Q13 Q9 Q18 16 128 *)
  0x4f7fd34a;       (* arm_SQRDMULH_VEC Q10 Q26 (Q15 :> LANE_H 3) 16 128 *)
  0x4e9c28dd;       (* arm_TRN1 Q29 Q6 Q28 32 128 *)
  0x3dc00c50;       (* arm_LDR Q16 X2 (Immediate_Offset (word 48)) *)
  0x4e9c68c1;       (* arm_TRN2 Q1 Q6 Q28 32 128 *)
  0x4f6f8351;       (* arm_MUL_VEC Q17 Q26 (Q15 :> LANE_H 2) 16 128 *)
  0x4e852972;       (* arm_TRN1 Q18 Q11 Q5 32 128 *)
  0x3dc01049;       (* arm_LDR Q9 X2 (Immediate_Offset (word 64)) *)
  0x4e85697e;       (* arm_TRN2 Q30 Q11 Q5 32 128 *)
  0x4f57c1b4;       (* arm_SQDMULH_VEC Q20 Q13 (Q7 :> LANE_H 1) 16 128 *)
  0x4edd6a5a;       (* arm_TRN2 Q26 Q18 Q29 64 128 *)
  0x3dc0145b;       (* arm_LDR Q27 X2 (Immediate_Offset (word 80)) *)
  0x6f474151;       (* arm_MLS_VEC Q17 Q10 (Q7 :> LANE_H 0) 16 128 *)
  0x4ec16bd8;       (* arm_TRN2 Q24 Q30 Q1 64 128 *)
  0x4edd2a5f;       (* arm_TRN1 Q31 Q18 Q29 64 128 *)
  0x3dc0084c;       (* arm_LDR Q12 X2 (Immediate_Offset (word 32)) *)
  0x6e788753;       (* arm_SUB_VEC Q19 Q26 Q24 16 128 *)
  0x4f57c2ab;       (* arm_SQDMULH_VEC Q11 Q21 (Q7 :> LANE_H 1) 16 128 *)
  0x4ec12bc0;       (* arm_TRN1 Q0 Q30 Q1 64 128 *)
  0x6e7bb666;       (* arm_SQRDMULH_VEC Q6 Q19 Q27 16 128 *)
  0x6e6087ea;       (* arm_SUB_VEC Q10 Q31 Q0 16 128 *)
  0x4f152682;       (* arm_SRSHR_VEC Q2 Q20 11 16 128 *)
  0x4f57c228;       (* arm_SQDMULH_VEC Q8 Q17 (Q7 :> LANE_H 1) 16 128 *)
  0x4e6087ff;       (* arm_ADD_VEC Q31 Q31 Q0 16 128 *)
  0x3cc60440;       (* arm_LDR Q0 X2 (Postimmediate_Offset (word 96)) *)
  0x6e70b55d;       (* arm_SQRDMULH_VEC Q29 Q10 Q16 16 128 *)
  0x4e78875b;       (* arm_ADD_VEC Q27 Q26 Q24 16 128 *)
  0x4f152563;       (* arm_SRSHR_VEC Q3 Q11 11 16 128 *)
  0x4e6c9d56;       (* arm_MUL_VEC Q22 Q10 Q12 16 128 *)
  0x6e7b87fc;       (* arm_SUB_VEC Q28 Q31 Q27 16 128 *)
  0x4e7b87e4;       (* arm_ADD_VEC Q4 Q31 Q27 16 128 *)
  0x4f152508;       (* arm_SRSHR_VEC Q8 Q8 11 16 128 *)
  0x6e79b78a;       (* arm_SQRDMULH_VEC Q10 Q28 Q25 16 128 *)
  0x4f1526ec;       (* arm_SRSHR_VEC Q12 Q23 11 16 128 *)
  0x6f4743b6;       (* arm_MLS_VEC Q22 Q29 (Q7 :> LANE_H 0) 16 128 *)
  0x6f474111;       (* arm_MLS_VEC Q17 Q8 (Q7 :> LANE_H 0) 16 128 *)
  0x6f474075;       (* arm_MLS_VEC Q21 Q3 (Q7 :> LANE_H 0) 16 128 *)
  0x4e699e7b;       (* arm_MUL_VEC Q27 Q19 Q9 16 128 *)
  0x6f4740db;       (* arm_MLS_VEC Q27 Q6 (Q7 :> LANE_H 0) 16 128 *)
  0x6f47404d;       (* arm_MLS_VEC Q13 Q2 (Q7 :> LANE_H 0) 16 128 *)
  0x6f47418e;       (* arm_MLS_VEC Q14 Q12 (Q7 :> LANE_H 0) 16 128 *)
  0x4e609f89;       (* arm_MUL_VEC Q9 Q28 Q0 16 128 *)
  0x6e7b86c8;       (* arm_SUB_VEC Q8 Q22 Q27 16 128 *)
  0x4e7b86d7;       (* arm_ADD_VEC Q23 Q22 Q27 16 128 *)
  0x6e79b505;       (* arm_SQRDMULH_VEC Q5 Q8 Q25 16 128 *)
  0x6e6e85a1;       (* arm_SUB_VEC Q1 Q13 Q14 16 128 *)
  0x4e609d19;       (* arm_MUL_VEC Q25 Q8 Q0 16 128 *)
  0x4e6e85a2;       (* arm_ADD_VEC Q2 Q13 Q14 16 128 *)
  0x4e972880;       (* arm_TRN1 Q0 Q4 Q23 32 128 *)
  0x6f474149;       (* arm_MLS_VEC Q9 Q10 (Q7 :> LANE_H 0) 16 128 *)
  0x4e97688a;       (* arm_TRN2 Q10 Q4 Q23 32 128 *)
  0x6f4740b9;       (* arm_MLS_VEC Q25 Q5 (Q7 :> LANE_H 0) 16 128 *)
  0x4f5fd033;       (* arm_SQRDMULH_VEC Q19 Q1 (Q15 :> LANE_H 1) 16 128 *)
  0x4f4f8030;       (* arm_MUL_VEC Q16 Q1 (Q15 :> LANE_H 0) 16 128 *)
  0x6e758626;       (* arm_SUB_VEC Q6 Q17 Q21 16 128 *)
  0x4e99293f;       (* arm_TRN1 Q31 Q9 Q25 32 128 *)
  0x4e996924;       (* arm_TRN2 Q4 Q9 Q25 32 128 *)
  0x4f5fd0cc;       (* arm_SQRDMULH_VEC Q12 Q6 (Q15 :> LANE_H 1) 16 128 *)
  0x4edf2809;       (* arm_TRN1 Q9 Q0 Q31 64 128 *)
  0x6f474270;       (* arm_MLS_VEC Q16 Q19 (Q7 :> LANE_H 0) 16 128 *)
  0x4ec46957;       (* arm_TRN2 Q23 Q10 Q4 64 128 *)
  0x4edf6808;       (* arm_TRN2 Q8 Q0 Q31 64 128 *)
  0x4f4f80db;       (* arm_MUL_VEC Q27 Q6 (Q15 :> LANE_H 0) 16 128 *)
  0x3cc1042f;       (* arm_LDR Q15 X1 (Postimmediate_Offset (word 16)) *)
  0x4ec42952;       (* arm_TRN1 Q18 Q10 Q4 64 128 *)
  0x6f47419b;       (* arm_MLS_VEC Q27 Q12 (Q7 :> LANE_H 0) 16 128 *)
  0x6e778506;       (* arm_SUB_VEC Q6 Q8 Q23 16 128 *)
  0x4e75862a;       (* arm_ADD_VEC Q10 Q17 Q21 16 128 *)
  0x3d800870;       (* arm_STR Q16 X3 (Immediate_Offset (word 32)) *)
  0x4e77850e;       (* arm_ADD_VEC Q14 Q8 Q23 16 128 *)
  0x4f5fd8d4;       (* arm_SQRDMULH_VEC Q20 Q6 (Q15 :> LANE_H 5) 16 128 *)
  0x3d80046a;       (* arm_STR Q10 X3 (Immediate_Offset (word 16)) *)
  0x3c840462;       (* arm_STR Q2 X3 (Postimmediate_Offset (word 64)) *)
  0x4f4f88d5;       (* arm_MUL_VEC Q21 Q6 (Q15 :> LANE_H 4) 16 128 *)
  0x3c9f007b;       (* arm_STR Q27 X3 (Immediate_Offset (word 18446744073709551600)) *)
  0xd1000484;       (* arm_SUB X4 X4 (rvalue (word 1)) *)
  0xb5fff584;       (* arm_CBNZ X4 (word 2096816) *)
  0x6f474295;       (* arm_MLS_VEC Q21 Q20 (Q7 :> LANE_H 0) 16 128 *)
  0x6e72853b;       (* arm_SUB_VEC Q27 Q9 Q18 16 128 *)
  0x4e72853e;       (* arm_ADD_VEC Q30 Q9 Q18 16 128 *)
  0x4f7fd36a;       (* arm_SQRDMULH_VEC Q10 Q27 (Q15 :> LANE_H 3) 16 128 *)
  0x4f6f837c;       (* arm_MUL_VEC Q28 Q27 (Q15 :> LANE_H 2) 16 128 *)
  0x4f57c1db;       (* arm_SQDMULH_VEC Q27 Q14 (Q7 :> LANE_H 1) 16 128 *)
  0x6f47415c;       (* arm_MLS_VEC Q28 Q10 (Q7 :> LANE_H 0) 16 128 *)
  0x4f57c3ca;       (* arm_SQDMULH_VEC Q10 Q30 (Q7 :> LANE_H 1) 16 128 *)
  0x4f15277b;       (* arm_SRSHR_VEC Q27 Q27 11 16 128 *)
  0x4f57c2ad;       (* arm_SQDMULH_VEC Q13 Q21 (Q7 :> LANE_H 1) 16 128 *)
  0x4f57c396;       (* arm_SQDMULH_VEC Q22 Q28 (Q7 :> LANE_H 1) 16 128 *)
  0x4f152559;       (* arm_SRSHR_VEC Q25 Q10 11 16 128 *)
  0x4f1525b8;       (* arm_SRSHR_VEC Q24 Q13 11 16 128 *)
  0x6f47436e;       (* arm_MLS_VEC Q14 Q27 (Q7 :> LANE_H 0) 16 128 *)
  0x6f47433e;       (* arm_MLS_VEC Q30 Q25 (Q7 :> LANE_H 0) 16 128 *)
  0x4f1526c2;       (* arm_SRSHR_VEC Q2 Q22 11 16 128 *)
  0x6f474315;       (* arm_MLS_VEC Q21 Q24 (Q7 :> LANE_H 0) 16 128 *)
  0x6f47405c;       (* arm_MLS_VEC Q28 Q2 (Q7 :> LANE_H 0) 16 128 *)
  0x6e6e87d9;       (* arm_SUB_VEC Q25 Q30 Q14 16 128 *)
  0x4e6e87db;       (* arm_ADD_VEC Q27 Q30 Q14 16 128 *)
  0x4f5fd323;       (* arm_SQRDMULH_VEC Q3 Q25 (Q15 :> LANE_H 1) 16 128 *)
  0x3c84047b;       (* arm_STR Q27 X3 (Postimmediate_Offset (word 64)) *)
  0x6e75879b;       (* arm_SUB_VEC Q27 Q28 Q21 16 128 *)
  0x4f4f832d;       (* arm_MUL_VEC Q13 Q25 (Q15 :> LANE_H 0) 16 128 *)
  0x4e758782;       (* arm_ADD_VEC Q2 Q28 Q21 16 128 *)
  0x4f5fd37f;       (* arm_SQRDMULH_VEC Q31 Q27 (Q15 :> LANE_H 1) 16 128 *)
  0x4f4f837b;       (* arm_MUL_VEC Q27 Q27 (Q15 :> LANE_H 0) 16 128 *)
  0x6f47406d;       (* arm_MLS_VEC Q13 Q3 (Q7 :> LANE_H 0) 16 128 *)
  0x6f4743fb;       (* arm_MLS_VEC Q27 Q31 (Q7 :> LANE_H 0) 16 128 *)
  0x3c9d0062;       (* arm_STR Q2 X3 (Immediate_Offset (word 18446744073709551568)) *)
  0x3c9e006d;       (* arm_STR Q13 X3 (Immediate_Offset (word 18446744073709551584)) *)
  0x3c9f007b;       (* arm_STR Q27 X3 (Immediate_Offset (word 18446744073709551600)) *)
  0xd2800084;       (* arm_MOV X4 (rvalue (word 4)) *)
  0x3cc20420;       (* arm_LDR Q0 X1 (Postimmediate_Offset (word 32)) *)
  0x3cdf0021;       (* arm_LDR Q1 X1 (Immediate_Offset (word 18446744073709551600)) *)
  0x3dc0700d;       (* arm_LDR Q13 X0 (Immediate_Offset (word 448)) *)
  0x3dc06002;       (* arm_LDR Q2 X0 (Immediate_Offset (word 384)) *)
  0x3dc03008;       (* arm_LDR Q8 X0 (Immediate_Offset (word 192)) *)
  0x3dc0400c;       (* arm_LDR Q12 X0 (Immediate_Offset (word 256)) *)
  0x3dc01017;       (* arm_LDR Q23 X0 (Immediate_Offset (word 64)) *)
  0x6e6d845a;       (* arm_SUB_VEC Q26 Q2 Q13 16 128 *)
  0x3dc0501b;       (* arm_LDR Q27 X0 (Immediate_Offset (word 320)) *)
  0x4e6d844d;       (* arm_ADD_VEC Q13 Q2 Q13 16 128 *)
  0x3dc00014;       (* arm_LDR Q20 X0 (Immediate_Offset (word 0)) *)
  0x4f51db5c;       (* arm_SQRDMULH_VEC Q28 Q26 (Q1 :> LANE_H 5) 16 128 *)
  0x3dc0200e;       (* arm_LDR Q14 X0 (Immediate_Offset (word 128)) *)
  0x4f418b52;       (* arm_MUL_VEC Q18 Q26 (Q1 :> LANE_H 4) 16 128 *)
  0x6e7b8582;       (* arm_SUB_VEC Q2 Q12 Q27 16 128 *)
  0x4e778683;       (* arm_ADD_VEC Q3 Q20 Q23 16 128 *)
  0x4e6885da;       (* arm_ADD_VEC Q26 Q14 Q8 16 128 *)
  0x4f71d05f;       (* arm_SQRDMULH_VEC Q31 Q2 (Q1 :> LANE_H 3) 16 128 *)
  0x6e7a846b;       (* arm_SUB_VEC Q11 Q3 Q26 16 128 *)
  0x6f474392;       (* arm_MLS_VEC Q18 Q28 (Q7 :> LANE_H 0) 16 128 *)
  0x4f61805d;       (* arm_MUL_VEC Q29 Q2 (Q1 :> LANE_H 2) 16 128 *)
  0x6f4743fd;       (* arm_MLS_VEC Q29 Q31 (Q7 :> LANE_H 0) 16 128 *)
  0x4f608176;       (* arm_MUL_VEC Q22 Q11 (Q0 :> LANE_H 2) 16 128 *)
  0x6e7287bf;       (* arm_SUB_VEC Q31 Q29 Q18 16 128 *)
  0x4f50dbfc;       (* arm_SQRDMULH_VEC Q28 Q31 (Q0 :> LANE_H 5) 16 128 *)
  0x4f408be4;       (* arm_MUL_VEC Q4 Q31 (Q0 :> LANE_H 4) 16 128 *)
  0xd1000484;       (* arm_SUB X4 X4 (rvalue (word 1)) *)
  0x4f70d16f;       (* arm_SQRDMULH_VEC Q15 Q11 (Q0 :> LANE_H 3) 16 128 *)
  0x6e77869f;       (* arm_SUB_VEC Q31 Q20 Q23 16 128 *)
  0x6e6885c2;       (* arm_SUB_VEC Q2 Q14 Q8 16 128 *)
  0x4f608be9;       (* arm_MUL_VEC Q9 Q31 (Q0 :> LANE_H 6) 16 128 *)
  0x3dc06418;       (* arm_LDR Q24 X0 (Immediate_Offset (word 400)) *)
  0x4e7b859e;       (* arm_ADD_VEC Q30 Q12 Q27 16 128 *)
  0x3dc07411;       (* arm_LDR Q17 X0 (Immediate_Offset (word 464)) *)
  0x4f51d04b;       (* arm_SQRDMULH_VEC Q11 Q2 (Q1 :> LANE_H 1) 16 128 *)
  0x4e6d87c6;       (* arm_ADD_VEC Q6 Q30 Q13 16 128 *)
  0x4e7a8479;       (* arm_ADD_VEC Q25 Q3 Q26 16 128 *)
  0x4f70dbfb;       (* arm_SQRDMULH_VEC Q27 Q31 (Q0 :> LANE_H 7) 16 128 *)
  0x3dc03408;       (* arm_LDR Q8 X0 (Immediate_Offset (word 208)) *)
  0x6e71870e;       (* arm_SUB_VEC Q14 Q24 Q17 16 128 *)
  0x4f418043;       (* arm_MUL_VEC Q3 Q2 (Q1 :> LANE_H 0) 16 128 *)
  0x6f474163;       (* arm_MLS_VEC Q3 Q11 (Q7 :> LANE_H 0) 16 128 *)
  0x6e668730;       (* arm_SUB_VEC Q16 Q25 Q6 16 128 *)
  0x6e6d87da;       (* arm_SUB_VEC Q26 Q30 Q13 16 128 *)
  0x6f474369;       (* arm_MLS_VEC Q9 Q27 (Q7 :> LANE_H 0) 16 128 *)
  0x3dc0541b;       (* arm_LDR Q27 X0 (Immediate_Offset (word 336)) *)
  0x4f40821e;       (* arm_MUL_VEC Q30 Q16 (Q0 :> LANE_H 0) 16 128 *)
  0x6f474384;       (* arm_MLS_VEC Q4 Q28 (Q7 :> LANE_H 0) 16 128 *)
  0x4e7287bc;       (* arm_ADD_VEC Q28 Q29 Q18 16 128 *)
  0x4e638533;       (* arm_ADD_VEC Q19 Q9 Q3 16 128 *)
  0x6e638523;       (* arm_SUB_VEC Q3 Q9 Q3 16 128 *)
  0x4f50d20d;       (* arm_SQRDMULH_VEC Q13 Q16 (Q0 :> LANE_H 1) 16 128 *)
  0x6e7c8677;       (* arm_SUB_VEC Q23 Q19 Q28 16 128 *)
  0x4e7c8670;       (* arm_ADD_VEC Q16 Q19 Q28 16 128 *)
  0x4f70d06c;       (* arm_SQRDMULH_VEC Q12 Q3 (Q0 :> LANE_H 3) 16 128 *)
  0x4f60806a;       (* arm_MUL_VEC Q10 Q3 (Q0 :> LANE_H 2) 16 128 *)
  0x3d801010;       (* arm_STR Q16 X0 (Immediate_Offset (word 64)) *)
  0x6f4741be;       (* arm_MLS_VEC Q30 Q13 (Q7 :> LANE_H 0) 16 128 *)
  0x6f47418a;       (* arm_MLS_VEC Q10 Q12 (Q7 :> LANE_H 0) 16 128 *)
  0x3dc0440c;       (* arm_LDR Q12 X0 (Immediate_Offset (word 272)) *)
  0x6f4741f6;       (* arm_MLS_VEC Q22 Q15 (Q7 :> LANE_H 0) 16 128 *)
  0x3d80401e;       (* arm_STR Q30 X0 (Immediate_Offset (word 256)) *)
  0x4f51d9c2;       (* arm_SQRDMULH_VEC Q2 Q14 (Q1 :> LANE_H 5) 16 128 *)
  0x6e7b858f;       (* arm_SUB_VEC Q15 Q12 Q27 16 128 *)
  0x4e66873e;       (* arm_ADD_VEC Q30 Q25 Q6 16 128 *)
  0x4e648559;       (* arm_ADD_VEC Q25 Q10 Q4 16 128 *)
  0x4f50db49;       (* arm_SQRDMULH_VEC Q9 Q26 (Q0 :> LANE_H 5) 16 128 *)
  0x6e64854d;       (* arm_SUB_VEC Q13 Q10 Q4 16 128 *)
  0x3d803019;       (* arm_STR Q25 X0 (Immediate_Offset (word 192)) *)
  0x4f4189d2;       (* arm_MUL_VEC Q18 Q14 (Q1 :> LANE_H 4) 16 128 *)
  0x4f4082ff;       (* arm_MUL_VEC Q31 Q23 (Q0 :> LANE_H 0) 16 128 *)
  0x4f50d2ea;       (* arm_SQRDMULH_VEC Q10 Q23 (Q0 :> LANE_H 1) 16 128 *)
  0x3dc01417;       (* arm_LDR Q23 X0 (Immediate_Offset (word 80)) *)
  0x4f50d1b4;       (* arm_SQRDMULH_VEC Q20 Q13 (Q0 :> LANE_H 1) 16 128 *)
  0x6f474052;       (* arm_MLS_VEC Q18 Q2 (Q7 :> LANE_H 0) 16 128 *)
  0x4f408b45;       (* arm_MUL_VEC Q5 Q26 (Q0 :> LANE_H 4) 16 128 *)
  0x4f4081ae;       (* arm_MUL_VEC Q14 Q13 (Q0 :> LANE_H 0) 16 128 *)
  0x6f47428e;       (* arm_MLS_VEC Q14 Q20 (Q7 :> LANE_H 0) 16 128 *)
  0x6f474125;       (* arm_MLS_VEC Q5 Q9 (Q7 :> LANE_H 0) 16 128 *)
  0x4f71d1e9;       (* arm_SQRDMULH_VEC Q9 Q15 (Q1 :> LANE_H 3) 16 128 *)
  0x3dc00414;       (* arm_LDR Q20 X0 (Immediate_Offset (word 16)) *)
  0x6f47415f;       (* arm_MLS_VEC Q31 Q10 (Q7 :> LANE_H 0) 16 128 *)
  0x3d80700e;       (* arm_STR Q14 X0 (Immediate_Offset (word 448)) *)
  0x3dc0240e;       (* arm_LDR Q14 X0 (Immediate_Offset (word 144)) *)
  0x6e6586ca;       (* arm_SUB_VEC Q10 Q22 Q5 16 128 *)
  0x4f6181fd;       (* arm_MUL_VEC Q29 Q15 (Q1 :> LANE_H 2) 16 128 *)
  0x4e6586cd;       (* arm_ADD_VEC Q13 Q22 Q5 16 128 *)
  0x3c81041e;       (* arm_STR Q30 X0 (Postimmediate_Offset (word 16)) *)
  0x6f47413d;       (* arm_MLS_VEC Q29 Q9 (Q7 :> LANE_H 0) 16 128 *)
  0x3d801c0d;       (* arm_STR Q13 X0 (Immediate_Offset (word 112)) *)
  0x3d804c1f;       (* arm_STR Q31 X0 (Immediate_Offset (word 304)) *)
  0x4e6885da;       (* arm_ADD_VEC Q26 Q14 Q8 16 128 *)
  0x4e778683;       (* arm_ADD_VEC Q3 Q20 Q23 16 128 *)
  0x4f50d15c;       (* arm_SQRDMULH_VEC Q28 Q10 (Q0 :> LANE_H 1) 16 128 *)
  0x4f408155;       (* arm_MUL_VEC Q21 Q10 (Q0 :> LANE_H 0) 16 128 *)
  0x6e7a846b;       (* arm_SUB_VEC Q11 Q3 Q26 16 128 *)
  0x6e7287ad;       (* arm_SUB_VEC Q13 Q29 Q18 16 128 *)
  0x4f608176;       (* arm_MUL_VEC Q22 Q11 (Q0 :> LANE_H 2) 16 128 *)
  0x6f474395;       (* arm_MLS_VEC Q21 Q28 (Q7 :> LANE_H 0) 16 128 *)
  0x4f50d9bc;       (* arm_SQRDMULH_VEC Q28 Q13 (Q0 :> LANE_H 5) 16 128 *)
  0x4f4089a4;       (* arm_MUL_VEC Q4 Q13 (Q0 :> LANE_H 4) 16 128 *)
  0x4e71870d;       (* arm_ADD_VEC Q13 Q24 Q17 16 128 *)
  0x3d805c15;       (* arm_STR Q21 X0 (Immediate_Offset (word 368)) *)
  0xd1000484;       (* arm_SUB X4 X4 (rvalue (word 1)) *)
  0xb5fff664;       (* arm_CBNZ X4 (word 2096844) *)
  0x4f70d162;       (* arm_SQRDMULH_VEC Q2 Q11 (Q0 :> LANE_H 3) 16 128 *)
  0x6e778689;       (* arm_SUB_VEC Q9 Q20 Q23 16 128 *)
  0x6e6885d1;       (* arm_SUB_VEC Q17 Q14 Q8 16 128 *)
  0x4e7b859b;       (* arm_ADD_VEC Q27 Q12 Q27 16 128 *)
  0x6f474384;       (* arm_MLS_VEC Q4 Q28 (Q7 :> LANE_H 0) 16 128 *)
  0x4e7a847c;       (* arm_ADD_VEC Q28 Q3 Q26 16 128 *)
  0x4e7287ae;       (* arm_ADD_VEC Q14 Q29 Q18 16 128 *)
  0x4f608937;       (* arm_MUL_VEC Q23 Q9 (Q0 :> LANE_H 6) 16 128 *)
  0x4e6d8778;       (* arm_ADD_VEC Q24 Q27 Q13 16 128 *)
  0x6e6d877b;       (* arm_SUB_VEC Q27 Q27 Q13 16 128 *)
  0x6f474056;       (* arm_MLS_VEC Q22 Q2 (Q7 :> LANE_H 0) 16 128 *)
  0x6e78878d;       (* arm_SUB_VEC Q13 Q28 Q24 16 128 *)
  0x4f70d922;       (* arm_SQRDMULH_VEC Q2 Q9 (Q0 :> LANE_H 7) 16 128 *)
  0x4e78879c;       (* arm_ADD_VEC Q28 Q28 Q24 16 128 *)
  0x3c81041c;       (* arm_STR Q28 X0 (Postimmediate_Offset (word 16)) *)
  0x4f51d23c;       (* arm_SQRDMULH_VEC Q28 Q17 (Q1 :> LANE_H 1) 16 128 *)
  0x4f418229;       (* arm_MUL_VEC Q9 Q17 (Q1 :> LANE_H 0) 16 128 *)
  0x4f4081b1;       (* arm_MUL_VEC Q17 Q13 (Q0 :> LANE_H 0) 16 128 *)
  0x6f474389;       (* arm_MLS_VEC Q9 Q28 (Q7 :> LANE_H 0) 16 128 *)
  0x6f474057;       (* arm_MLS_VEC Q23 Q2 (Q7 :> LANE_H 0) 16 128 *)
  0x4f50d1ad;       (* arm_SQRDMULH_VEC Q13 Q13 (Q0 :> LANE_H 1) 16 128 *)
  0x4f50db62;       (* arm_SQRDMULH_VEC Q2 Q27 (Q0 :> LANE_H 5) 16 128 *)
  0x4e6986fc;       (* arm_ADD_VEC Q28 Q23 Q9 16 128 *)
  0x4f408b7b;       (* arm_MUL_VEC Q27 Q27 (Q0 :> LANE_H 4) 16 128 *)
  0x6e6986e9;       (* arm_SUB_VEC Q9 Q23 Q9 16 128 *)
  0x6e6e8797;       (* arm_SUB_VEC Q23 Q28 Q14 16 128 *)
  0x4e6e879c;       (* arm_ADD_VEC Q28 Q28 Q14 16 128 *)
  0x4f70d12e;       (* arm_SQRDMULH_VEC Q14 Q9 (Q0 :> LANE_H 3) 16 128 *)
  0x6f47405b;       (* arm_MLS_VEC Q27 Q2 (Q7 :> LANE_H 0) 16 128 *)
  0x3d800c1c;       (* arm_STR Q28 X0 (Immediate_Offset (word 48)) *)
  0x4f608122;       (* arm_MUL_VEC Q2 Q9 (Q0 :> LANE_H 2) 16 128 *)
  0x6f4741c2;       (* arm_MLS_VEC Q2 Q14 (Q7 :> LANE_H 0) 16 128 *)
  0x6e7b86dc;       (* arm_SUB_VEC Q28 Q22 Q27 16 128 *)
  0x4e7b86db;       (* arm_ADD_VEC Q27 Q22 Q27 16 128 *)
  0x6f4741b1;       (* arm_MLS_VEC Q17 Q13 (Q7 :> LANE_H 0) 16 128 *)
  0x3d801c1b;       (* arm_STR Q27 X0 (Immediate_Offset (word 112)) *)
  0x4f4082fb;       (* arm_MUL_VEC Q27 Q23 (Q0 :> LANE_H 0) 16 128 *)
  0x4e64844d;       (* arm_ADD_VEC Q13 Q2 Q4 16 128 *)
  0x6e648442;       (* arm_SUB_VEC Q2 Q2 Q4 16 128 *)
  0x4f50d2e9;       (* arm_SQRDMULH_VEC Q9 Q23 (Q0 :> LANE_H 1) 16 128 *)
  0x3d803c11;       (* arm_STR Q17 X0 (Immediate_Offset (word 240)) *)
  0x3d802c0d;       (* arm_STR Q13 X0 (Immediate_Offset (word 176)) *)
  0x4f50d04d;       (* arm_SQRDMULH_VEC Q13 Q2 (Q0 :> LANE_H 1) 16 128 *)
  0x4f408042;       (* arm_MUL_VEC Q2 Q2 (Q0 :> LANE_H 0) 16 128 *)
  0x6f47413b;       (* arm_MLS_VEC Q27 Q9 (Q7 :> LANE_H 0) 16 128 *)
  0x4f50d389;       (* arm_SQRDMULH_VEC Q9 Q28 (Q0 :> LANE_H 1) 16 128 *)
  0x6f4741a2;       (* arm_MLS_VEC Q2 Q13 (Q7 :> LANE_H 0) 16 128 *)
  0x3d804c1b;       (* arm_STR Q27 X0 (Immediate_Offset (word 304)) *)
  0x4f40839b;       (* arm_MUL_VEC Q27 Q28 (Q0 :> LANE_H 0) 16 128 *)
  0x6f47413b;       (* arm_MLS_VEC Q27 Q9 (Q7 :> LANE_H 0) 16 128 *)
  0x3d806c02;       (* arm_STR Q2 X0 (Immediate_Offset (word 432)) *)
  0x3d805c1b;       (* arm_STR Q27 X0 (Immediate_Offset (word 368)) *)
  0x6d4027e8;       (* arm_LDP D8 D9 SP (Immediate_Offset (word 0)) *)
  0x6d412fea;       (* arm_LDP D10 D11 SP (Immediate_Offset (word 16)) *)
  0x6d4237ec;       (* arm_LDP D12 D13 SP (Immediate_Offset (word 32)) *)
  0x6d433fee;       (* arm_LDP D14 D15 SP (Immediate_Offset (word 48)) *)
  0x910103ff;       (* arm_ADD SP SP (rvalue (word 64)) *)
  0xd65f03c0        (* arm_RET X30 *)
]
[114; 252; 114; 252; 53; 251; 53; 251; 219; 0; 219; 0; 87; 3; 87; 3; 3; 221;
 3; 221; 210; 208; 210; 208; 108; 8; 108; 8; 224; 32; 224; 32; 151; 4; 151;
 4; 138; 1; 138; 1; 251; 251; 251; 251; 68; 251; 68; 251; 46; 45; 46; 45; 38;
 15; 38; 15; 111; 216; 111; 216; 102; 209; 102; 209; 139; 252; 139; 252; 195;
 4; 195; 4; 175; 5; 175; 5; 71; 6; 71; 6; 249; 221; 249; 221; 223; 46; 223;
 46; 242; 55; 242; 55; 202; 61; 202; 61; 120; 253; 120; 253; 55; 250; 55;
 250; 200; 2; 200; 2; 170; 2; 170; 2; 22; 231; 22; 231; 14; 199; 14; 199; 96;
 27; 96; 27; 57; 26; 57; 26; 138; 252; 138; 252; 155; 4; 155; 4; 254; 251;
 254; 251; 188; 251; 188; 251; 239; 221; 239; 221; 85; 45; 85; 45; 141; 216;
 141; 216; 3; 214; 3; 214; 42; 2; 42; 2; 137; 251; 137; 251; 109; 254; 109;
 254; 13; 2; 13; 2; 77; 21; 77; 21; 13; 212; 13; 212; 129; 240; 129; 240; 48;
 20; 48; 20; 159; 3; 159; 3; 2; 250; 2; 250; 205; 1; 205; 1; 98; 250; 98;
 250; 165; 35; 165; 35; 5; 197; 5; 197; 186; 17; 186; 17; 181; 200; 181; 200;
 223; 2; 223; 2; 207; 253; 207; 253; 11; 253; 11; 253; 193; 254; 193; 254;
 67; 28; 67; 28; 110; 234; 110; 234; 229; 226; 229; 226; 188; 243; 188; 243;
 95; 3; 95; 3; 206; 4; 206; 4; 44; 2; 44; 2; 217; 251; 217; 251; 47; 33; 47;
 33; 75; 47; 75; 47; 97; 21; 97; 21; 33; 215; 33; 215; 60; 254; 60; 254; 217;
 252; 217; 252; 101; 250; 101; 250; 242; 3; 242; 3; 159; 238; 159; 238; 249;
 224; 249; 224; 211; 200; 211; 200; 214; 38; 214; 38; 147; 249; 147; 249; 12;
 3; 12; 3; 109; 0; 109; 0; 7; 4; 7; 4; 192; 192; 192; 192; 254; 29; 254; 29;
 49; 4; 49; 4; 164; 39; 164; 39; 215; 4; 215; 4; 137; 254; 137; 254; 12; 5;
 12; 5; 208; 249; 208; 249; 164; 47; 164; 47; 149; 241; 149; 241; 173; 49;
 173; 49; 24; 195; 24; 195; 134; 5; 134; 5; 216; 250; 216; 250; 223; 255;
 223; 255; 208; 1; 208; 1; 94; 54; 94; 54; 63; 205; 63; 205; 187; 254; 187;
 254; 215; 17; 215; 17; 127; 253; 127; 253; 224; 3; 224; 3; 173; 3; 173; 3;
 253; 3; 253; 3; 91; 231; 91; 231; 36; 38; 36; 38; 46; 36; 46; 36; 66; 39;
 66; 39; 244; 254; 244; 254; 35; 253; 35; 253; 124; 3; 124; 3; 85; 252; 85;
 252; 178; 245; 178; 245; 209; 227; 209; 227; 76; 34; 76; 34; 229; 219; 229;
 219; 136; 253; 136; 253; 48; 3; 48; 3; 72; 5; 72; 5; 118; 253; 118; 253;
 179; 231; 179; 231; 96; 31; 96; 31; 252; 51; 252; 51; 2; 231; 2; 231; 130;
 2; 130; 2; 72; 252; 72; 252; 4; 6; 4; 6; 141; 249; 141; 249; 175; 24; 175;
 24; 101; 219; 101; 219; 55; 59; 55; 59; 133; 192; 133; 192; 75; 250; 75;
 250; 202; 5; 202; 5; 28; 2; 28; 2; 90; 6; 90; 6; 211; 199; 211; 199; 252;
 56; 252; 56; 195; 20; 195; 20; 133; 62; 133; 62; 250; 4; 250; 4; 28; 4; 28;
 4; 1; 4; 1; 4; 83; 251; 83; 251; 252; 48; 252; 48; 115; 40; 115; 40; 105;
 39; 105; 39; 250; 209; 250; 209; 23; 1; 23; 1; 149; 4; 149; 4; 23; 255; 23;
 255; 155; 2; 155; 2; 186; 10; 186; 10; 26; 45; 26; 45; 11; 247; 11; 247;
 165; 25; 165; 25; 58; 1; 58; 1; 12; 253; 12; 253; 48; 0; 48; 0; 127; 250;
 127; 250; 19; 12; 19; 12; 239; 226; 239; 226; 216; 1; 216; 1; 211; 201; 211;
 201; 37; 6; 37; 6; 76; 0; 76; 0; 181; 254; 181; 254; 223; 254; 223; 254;
 123; 60; 123; 60; 236; 2; 236; 2; 70; 243; 70; 243; 227; 244; 227; 244; 180;
 251; 180; 251; 45; 253; 45; 253; 168; 2; 168; 2; 56; 2; 56; 2; 180; 213;
 180; 213; 51; 228; 51; 228; 37; 26; 37; 26; 215; 21; 215; 21; 17; 4; 17; 4;
 155; 249; 155; 249; 185; 253; 185; 253; 239; 255; 239; 255; 7; 40; 7; 40;
 15; 193; 15; 193; 149; 233; 149; 233; 89; 255; 89; 255; 47; 6; 222; 60; 203;
 252; 111; 224; 75; 5; 26; 52; 0; 0; 0; 0; 199; 253; 31; 234; 194; 1; 77; 17;
 168; 3; 253; 35; 0; 0; 0; 0; 69; 0; 167; 2; 191; 1; 48; 17; 233; 253; 110;
 235; 0; 0; 0; 0; 31; 2; 225; 20; 211; 4; 124; 47; 110; 250; 44; 201; 0; 0;
 0; 0; 227; 252; 91; 225; 203; 250; 191; 204; 65; 4; 223; 41; 0; 0; 0; 0; 63;
 255; 148; 248; 200; 255; 217; 253; 27; 1; 226; 10; 0; 0; 0; 0; 130; 5; 55;
 54; 60; 250; 63; 199; 197; 250; 132; 204; 0; 0; 0; 0; 218; 251; 43; 215;
 114; 3; 234; 33; 216; 254; 158; 244; 0; 0; 0; 0; 64; 6; 133; 61; 40; 0; 138;
 1; 237; 2; 205; 28; 176; 252; 101; 223; 152; 5; 15; 55; 138; 253; 199; 231;
 175; 2; 106; 26; 0; 0; 0; 0];;

let MLKEM_INTT_EXEC = ARM_MK_EXEC_RULE mlkem_intt_mc;;

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
 (`bytes_loaded s (word (pc + 0x5dc)) mlkem_intt_data <=>
   read (memory :> bytes(word (pc + 0x5dc),928)) s =
   num_of_bytelist mlkem_intt_data`,
  REWRITE_TAC[bytes_loaded; READ_BYTELIST_EQ_BYTES;
    CONV_RULE (RAND_CONV LENGTH_CONV)
     (AP_TERM `LENGTH:byte list->num` mlkem_intt_data)]);;

let MLKEM_INTT_CORRECT = prove
 (`!a x pc.
      nonoverlapping (word pc,0x97c) (a,512)
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc)
                 (APPEND mlkem_intt_mc mlkem_intt_data) /\
                read PC s = word (pc + 0x14) /\
                C_ARGUMENTS [a] s /\
                !i. i < 256
                    ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                        x i)
           (\s. read PC s = word(pc + 0x5c4) /\
                !i. i < 256
                    ==> let zi =
                         read(memory :> bytes16(word_add a (word(2 * i)))) s in
                        (ival zi == inverse_ntt (ival o x) i) (mod &3329) /\
                        abs(ival zi) <= &26624)
           (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
            MAYCHANGE [memory :> bytes(a,512)])`,
  MAP_EVERY X_GEN_TAC [`a:int64`; `x:num->int16`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** Fiddle around with the constant table stuff ***)

  REWRITE_TAC[ALIGNED_BYTES_LOADED_APPEND_CLAUSE] THEN
  REWRITE_TAC[fst MLKEM_INTT_EXEC] THEN REWRITE_TAC[BYTES_LOADED_DATA] THEN

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
   `word(pc + 0x8dc):int64 = word_add (word(pc + 0x5dc)) (word 768)`) THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM BYTES_LOADED_DATA]) THEN
  ABBREV_TAC `wpc:int64 = word(pc + 0x5dc)` THEN
  SUBST1_TAC(WORD_RULE `wpc:int64 = word(val wpc + 0)`) THEN
  REWRITE_TAC[mlkem_intt_data] THEN CONV_TAC(LAND_CONV DATA64_CONV) THEN
  REWRITE_TAC[WORD_RULE `word(val x + n) = word_add x (word n)`] THEN
  REWRITE_TAC[bytes_loaded_nil] THEN STRIP_TAC THEN
  SUBGOAL_THEN `nonoverlapping (a:int64,512) (wpc:int64,928)` MP_TAC THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES] THENL
   [EXPAND_TAC "wpc" THEN NONOVERLAPPING_TAC;
    DISCH_TAC] THEN
  MP_TAC(end_itlist CONJ (map (fun n -> READ_MEMORY_MERGE_CONV 1
            (subst[mk_small_numeral(16*n),`n:num`]
                  `read (memory :> bytes128(word_add wpc (word n))) s0`))
            (0--57))) THEN
  ASM_REWRITE_TAC[WORD_ADD_0] THEN
  CONV_TAC(LAND_CONV(DEPTH_CONV WORD_NUM_RED_CONV)) THEN
  DISCARD_MATCHING_ASSUMPTIONS [`read (memory :> bytes64 a) s = x`] THEN
  STRIP_TAC THEN

  (*** Simulate all the way to the end, in effect unrolling loops ***)

  MAP_EVERY (fun n -> ARM_STEPS_TAC MLKEM_INTT_EXEC [n] THEN SIMD_SIMPLIFY_TAC)
            (1--1184) THEN
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
  ASM_REWRITE_TAC[I_THM; WORD_ADD_0] THEN DISCARD_STATE_TAC "s1184" THEN
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
 (`!a x pc stackpointer returnaddress.
      aligned 16 stackpointer /\
      ALL (nonoverlapping (word_sub stackpointer (word 64),64))
          [(word pc,0x97c); (a,512)] /\
      nonoverlapping (word pc,0x97c) (a,512)
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc)
                 (APPEND mlkem_intt_mc mlkem_intt_data) /\
                read PC s = word pc /\
                read SP s = stackpointer /\
                read X30 s = returnaddress /\
                C_ARGUMENTS [a] s /\
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
    ONCE_DEPTH_CONV let_CONV THENC
    ONCE_DEPTH_CONV EXPAND_CASES_CONV THENC
    ONCE_DEPTH_CONV NUM_MULT_CONV THENC
    PURE_REWRITE_CONV [WORD_ADD_0] in
  REWRITE_TAC[ALIGNED_BYTES_LOADED_APPEND_CLAUSE; BYTES_LOADED_DATA;
              fst MLKEM_INTT_EXEC] THEN
  CONV_TAC TWEAK_CONV THEN
  ARM_ADD_RETURN_STACK_TAC ~pre_post_nsteps:(5,5) MLKEM_INTT_EXEC
   (REWRITE_RULE[ALIGNED_BYTES_LOADED_APPEND_CLAUSE; BYTES_LOADED_DATA;
                 fst MLKEM_INTT_EXEC] (CONV_RULE TWEAK_CONV MLKEM_INTT_CORRECT))
    `[D8; D9; D10; D11; D12; D13; D14; D15]` 64);;
