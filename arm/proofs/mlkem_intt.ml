(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Inverse number theoretic transform.                                       *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "common/mlkem_mldsa.ml";;

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
  0x3dc00861;       (* arm_LDR Q1 X3 (Immediate_Offset (word 32)) *)
  0x3dc00c72;       (* arm_LDR Q18 X3 (Immediate_Offset (word 48)) *)
  0x3dc0006f;       (* arm_LDR Q15 X3 (Immediate_Offset (word 0)) *)
  0x3dc00475;       (* arm_LDR Q21 X3 (Immediate_Offset (word 16)) *)
  0x3cc60443;       (* arm_LDR Q3 X2 (Postimmediate_Offset (word 96)) *)
  0x3cdd0050;       (* arm_LDR Q16 X2 (Immediate_Offset (word 18446744073709551568)) *)
  0x3cc10424;       (* arm_LDR Q4 X1 (Postimmediate_Offset (word 16)) *)
  0x3cde005e;       (* arm_LDR Q30 X2 (Immediate_Offset (word 18446744073709551584)) *)
  0x4e92282b;       (* arm_TRN1 Q11 Q1 Q18 32 128 *)
  0x4e926832;       (* arm_TRN2 Q18 Q1 Q18 32 128 *)
  0x4e9529f4;       (* arm_TRN1 Q20 Q15 Q21 32 128 *)
  0x4e9569e1;       (* arm_TRN2 Q1 Q15 Q21 32 128 *)
  0x3cdf0040;       (* arm_LDR Q0 X2 (Immediate_Offset (word 18446744073709551600)) *)
  0x3cdb0056;       (* arm_LDR Q22 X2 (Immediate_Offset (word 18446744073709551536)) *)
  0x4ecb2a88;       (* arm_TRN1 Q8 Q20 Q11 64 128 *)
  0x4ed22826;       (* arm_TRN1 Q6 Q1 Q18 64 128 *)
  0x4ed26821;       (* arm_TRN2 Q1 Q1 Q18 64 128 *)
  0x4ecb6a95;       (* arm_TRN2 Q21 Q20 Q11 64 128 *)
  0x6e66850b;       (* arm_SUB_VEC Q11 Q8 Q6 16 128 *)
  0x4e668514;       (* arm_ADD_VEC Q20 Q8 Q6 16 128 *)
  0x4e6186ae;       (* arm_ADD_VEC Q14 Q21 Q1 16 128 *)
  0x6e6186af;       (* arm_SUB_VEC Q15 Q21 Q1 16 128 *)
  0x6e70b570;       (* arm_SQRDMULH_VEC Q16 Q11 Q16 16 128 *)
  0x3cdc0046;       (* arm_LDR Q6 X2 (Immediate_Offset (word 18446744073709551552)) *)
  0x6e6e8692;       (* arm_SUB_VEC Q18 Q20 Q14 16 128 *)
  0x4e6e8695;       (* arm_ADD_VEC Q21 Q20 Q14 16 128 *)
  0x6e60b5e0;       (* arm_SQRDMULH_VEC Q0 Q15 Q0 16 128 *)
  0x4e669d6b;       (* arm_MUL_VEC Q11 Q11 Q6 16 128 *)
  0x4e7e9de1;       (* arm_MUL_VEC Q1 Q15 Q30 16 128 *)
  0x6f47420b;       (* arm_MLS_VEC Q11 Q16 (Q7 :> LANE_H 0) 16 128 *)
  0x6f474001;       (* arm_MLS_VEC Q1 Q0 (Q7 :> LANE_H 0) 16 128 *)
  0x6e76b640;       (* arm_SQRDMULH_VEC Q0 Q18 Q22 16 128 *)
  0x4e639e50;       (* arm_MUL_VEC Q16 Q18 Q3 16 128 *)
  0x6e618572;       (* arm_SUB_VEC Q18 Q11 Q1 16 128 *)
  0x4e61856d;       (* arm_ADD_VEC Q13 Q11 Q1 16 128 *)
  0x6e76b64b;       (* arm_SQRDMULH_VEC Q11 Q18 Q22 16 128 *)
  0x4e8d2ab4;       (* arm_TRN1 Q20 Q21 Q13 32 128 *)
  0x4e8d6aa1;       (* arm_TRN2 Q1 Q21 Q13 32 128 *)
  0x6f474010;       (* arm_MLS_VEC Q16 Q0 (Q7 :> LANE_H 0) 16 128 *)
  0x4e639e43;       (* arm_MUL_VEC Q3 Q18 Q3 16 128 *)
  0x6f474163;       (* arm_MLS_VEC Q3 Q11 (Q7 :> LANE_H 0) 16 128 *)
  0x4e836a0b;       (* arm_TRN2 Q11 Q16 Q3 32 128 *)
  0x4e832a10;       (* arm_TRN1 Q16 Q16 Q3 32 128 *)
  0x4ecb6835;       (* arm_TRN2 Q21 Q1 Q11 64 128 *)
  0x4ed06a80;       (* arm_TRN2 Q0 Q20 Q16 64 128 *)
  0x4ecb2821;       (* arm_TRN1 Q1 Q1 Q11 64 128 *)
  0x4ed02a8b;       (* arm_TRN1 Q11 Q20 Q16 64 128 *)
  0x6e75840d;       (* arm_SUB_VEC Q13 Q0 Q21 16 128 *)
  0x4e75841d;       (* arm_ADD_VEC Q29 Q0 Q21 16 128 *)
  0x4e618569;       (* arm_ADD_VEC Q9 Q11 Q1 16 128 *)
  0x6e618577;       (* arm_SUB_VEC Q23 Q11 Q1 16 128 *)
  0x4f57c3a1;       (* arm_SQDMULH_VEC Q1 Q29 (Q7 :> LANE_H 1) 16 128 *)
  0x4f57c13b;       (* arm_SQDMULH_VEC Q27 Q9 (Q7 :> LANE_H 1) 16 128 *)
  0x4f54d9b0;       (* arm_SQRDMULH_VEC Q16 Q13 (Q4 :> LANE_H 5) 16 128 *)
  0x4f15242e;       (* arm_SRSHR_VEC Q14 Q1 11 16 128 *)
  0xd1000484;       (* arm_SUB X4 X4 (rvalue (word 1)) *)
  0x6f4741dd;       (* arm_MLS_VEC Q29 Q14 (Q7 :> LANE_H 0) 16 128 *)
  0x3dc01863;       (* arm_LDR Q3 X3 (Immediate_Offset (word 96)) *)
  0x3dc01c7e;       (* arm_LDR Q30 X3 (Immediate_Offset (word 112)) *)
  0x3dc00854;       (* arm_LDR Q20 X2 (Immediate_Offset (word 32)) *)
  0x4f6482e6;       (* arm_MUL_VEC Q6 Q23 (Q4 :> LANE_H 2) 16 128 *)
  0x3dc00458;       (* arm_LDR Q24 X2 (Immediate_Offset (word 16)) *)
  0x3dc01060;       (* arm_LDR Q0 X3 (Immediate_Offset (word 64)) *)
  0x3dc0146e;       (* arm_LDR Q14 X3 (Immediate_Offset (word 80)) *)
  0x4f152779;       (* arm_SRSHR_VEC Q25 Q27 11 16 128 *)
  0x4f4489af;       (* arm_MUL_VEC Q15 Q13 (Q4 :> LANE_H 4) 16 128 *)
  0x4e9e2872;       (* arm_TRN1 Q18 Q3 Q30 32 128 *)
  0x3cc6045c;       (* arm_LDR Q28 X2 (Postimmediate_Offset (word 96)) *)
  0x4e9e6865;       (* arm_TRN2 Q5 Q3 Q30 32 128 *)
  0x4f74d2f3;       (* arm_SQRDMULH_VEC Q19 Q23 (Q4 :> LANE_H 3) 16 128 *)
  0x4e8e681a;       (* arm_TRN2 Q26 Q0 Q14 32 128 *)
  0x4e8e280b;       (* arm_TRN1 Q11 Q0 Q14 32 128 *)
  0x6f474329;       (* arm_MLS_VEC Q9 Q25 (Q7 :> LANE_H 0) 16 128 *)
  0x4ec56b40;       (* arm_TRN2 Q0 Q26 Q5 64 128 *)
  0x3cdf0051;       (* arm_LDR Q17 X2 (Immediate_Offset (word 18446744073709551600)) *)
  0x6f47420f;       (* arm_MLS_VEC Q15 Q16 (Q7 :> LANE_H 0) 16 128 *)
  0x4ed26977;       (* arm_TRN2 Q23 Q11 Q18 64 128 *)
  0x4ec52b5e;       (* arm_TRN1 Q30 Q26 Q5 64 128 *)
  0x3cde0041;       (* arm_LDR Q1 X2 (Immediate_Offset (word 18446744073709551584)) *)
  0x6f474266;       (* arm_MLS_VEC Q6 Q19 (Q7 :> LANE_H 0) 16 128 *)
  0x6e6086ee;       (* arm_SUB_VEC Q14 Q23 Q0 16 128 *)
  0x4ed22973;       (* arm_TRN1 Q19 Q11 Q18 64 128 *)
  0x3cdd004a;       (* arm_LDR Q10 X2 (Immediate_Offset (word 18446744073709551568)) *)
  0x4e6086ff;       (* arm_ADD_VEC Q31 Q23 Q0 16 128 *)
  0x6e71b5db;       (* arm_SQRDMULH_VEC Q27 Q14 Q17 16 128 *)
  0x4e7e8672;       (* arm_ADD_VEC Q18 Q19 Q30 16 128 *)
  0x4e619dcd;       (* arm_MUL_VEC Q13 Q14 Q1 16 128 *)
  0x6e7e8676;       (* arm_SUB_VEC Q22 Q19 Q30 16 128 *)
  0x6e7f865a;       (* arm_SUB_VEC Q26 Q18 Q31 16 128 *)
  0x6e6ab6ca;       (* arm_SQRDMULH_VEC Q10 Q22 Q10 16 128 *)
  0x6e7d8539;       (* arm_SUB_VEC Q25 Q9 Q29 16 128 *)
  0x4e7d8529;       (* arm_ADD_VEC Q9 Q9 Q29 16 128 *)
  0x6f47436d;       (* arm_MLS_VEC Q13 Q27 (Q7 :> LANE_H 0) 16 128 *)
  0x4e7f8642;       (* arm_ADD_VEC Q2 Q18 Q31 16 128 *)
  0x3c840469;       (* arm_STR Q9 X3 (Postimmediate_Offset (word 64)) *)
  0x6e6f84d7;       (* arm_SUB_VEC Q23 Q6 Q15 16 128 *)
  0x4e6f84d5;       (* arm_ADD_VEC Q21 Q6 Q15 16 128 *)
  0x4e749ec3;       (* arm_MUL_VEC Q3 Q22 Q20 16 128 *)
  0x6f474143;       (* arm_MLS_VEC Q3 Q10 (Q7 :> LANE_H 0) 16 128 *)
  0x6e78b754;       (* arm_SQRDMULH_VEC Q20 Q26 Q24 16 128 *)
  0x4e7c9f56;       (* arm_MUL_VEC Q22 Q26 Q28 16 128 *)
  0x4e6d846c;       (* arm_ADD_VEC Q12 Q3 Q13 16 128 *)
  0x6e6d846f;       (* arm_SUB_VEC Q15 Q3 Q13 16 128 *)
  0x4f54d2ed;       (* arm_SQRDMULH_VEC Q13 Q23 (Q4 :> LANE_H 1) 16 128 *)
  0x6e78b5e0;       (* arm_SQRDMULH_VEC Q0 Q15 Q24 16 128 *)
  0x4e7c9dfb;       (* arm_MUL_VEC Q27 Q15 Q28 16 128 *)
  0x6f474296;       (* arm_MLS_VEC Q22 Q20 (Q7 :> LANE_H 0) 16 128 *)
  0x6f47401b;       (* arm_MLS_VEC Q27 Q0 (Q7 :> LANE_H 0) 16 128 *)
  0x4f57c2b3;       (* arm_SQDMULH_VEC Q19 Q21 (Q7 :> LANE_H 1) 16 128 *)
  0x4e8c285a;       (* arm_TRN1 Q26 Q2 Q12 32 128 *)
  0x4f4482ea;       (* arm_MUL_VEC Q10 Q23 (Q4 :> LANE_H 0) 16 128 *)
  0x4e8c6842;       (* arm_TRN2 Q2 Q2 Q12 32 128 *)
  0x4e9b6acc;       (* arm_TRN2 Q12 Q22 Q27 32 128 *)
  0x4e9b2ac8;       (* arm_TRN1 Q8 Q22 Q27 32 128 *)
  0x4f44833f;       (* arm_MUL_VEC Q31 Q25 (Q4 :> LANE_H 0) 16 128 *)
  0x4ecc6843;       (* arm_TRN2 Q3 Q2 Q12 64 128 *)
  0x4f54d32b;       (* arm_SQRDMULH_VEC Q11 Q25 (Q4 :> LANE_H 1) 16 128 *)
  0x4ec86b40;       (* arm_TRN2 Q0 Q26 Q8 64 128 *)
  0x4f152670;       (* arm_SRSHR_VEC Q16 Q19 11 16 128 *)
  0x3cc10424;       (* arm_LDR Q4 X1 (Postimmediate_Offset (word 16)) *)
  0x6f4741aa;       (* arm_MLS_VEC Q10 Q13 (Q7 :> LANE_H 0) 16 128 *)
  0x4e63841d;       (* arm_ADD_VEC Q29 Q0 Q3 16 128 *)
  0x4ec82b52;       (* arm_TRN1 Q18 Q26 Q8 64 128 *)
  0x4ecc2854;       (* arm_TRN1 Q20 Q2 Q12 64 128 *)
  0x4f57c3af;       (* arm_SQDMULH_VEC Q15 Q29 (Q7 :> LANE_H 1) 16 128 *)
  0x6e63840d;       (* arm_SUB_VEC Q13 Q0 Q3 16 128 *)
  0x6f474215;       (* arm_MLS_VEC Q21 Q16 (Q7 :> LANE_H 0) 16 128 *)
  0x4e748649;       (* arm_ADD_VEC Q9 Q18 Q20 16 128 *)
  0x3c9f006a;       (* arm_STR Q10 X3 (Immediate_Offset (word 18446744073709551600)) *)
  0x6e748657;       (* arm_SUB_VEC Q23 Q18 Q20 16 128 *)
  0x6f47417f;       (* arm_MLS_VEC Q31 Q11 (Q7 :> LANE_H 0) 16 128 *)
  0x4f1525ee;       (* arm_SRSHR_VEC Q14 Q15 11 16 128 *)
  0x4f54d9b0;       (* arm_SQRDMULH_VEC Q16 Q13 (Q4 :> LANE_H 5) 16 128 *)
  0x3c9d0075;       (* arm_STR Q21 X3 (Immediate_Offset (word 18446744073709551568)) *)
  0x4f57c13b;       (* arm_SQDMULH_VEC Q27 Q9 (Q7 :> LANE_H 1) 16 128 *)
  0x3c9e007f;       (* arm_STR Q31 X3 (Immediate_Offset (word 18446744073709551584)) *)
  0xd1000484;       (* arm_SUB X4 X4 (rvalue (word 1)) *)
  0xb5fff5e4;       (* arm_CBNZ X4 (word 2096828) *)
  0x6f4741dd;       (* arm_MLS_VEC Q29 Q14 (Q7 :> LANE_H 0) 16 128 *)
  0x4f152761;       (* arm_SRSHR_VEC Q1 Q27 11 16 128 *)
  0x4f4489ab;       (* arm_MUL_VEC Q11 Q13 (Q4 :> LANE_H 4) 16 128 *)
  0x6f474029;       (* arm_MLS_VEC Q9 Q1 (Q7 :> LANE_H 0) 16 128 *)
  0x4f74d2e1;       (* arm_SQRDMULH_VEC Q1 Q23 (Q4 :> LANE_H 3) 16 128 *)
  0x4f6482f4;       (* arm_MUL_VEC Q20 Q23 (Q4 :> LANE_H 2) 16 128 *)
  0x6e7d8535;       (* arm_SUB_VEC Q21 Q9 Q29 16 128 *)
  0x4e7d8520;       (* arm_ADD_VEC Q0 Q9 Q29 16 128 *)
  0x6f47420b;       (* arm_MLS_VEC Q11 Q16 (Q7 :> LANE_H 0) 16 128 *)
  0x6f474034;       (* arm_MLS_VEC Q20 Q1 (Q7 :> LANE_H 0) 16 128 *)
  0x3c840460;       (* arm_STR Q0 X3 (Postimmediate_Offset (word 64)) *)
  0x4f4482a1;       (* arm_MUL_VEC Q1 Q21 (Q4 :> LANE_H 0) 16 128 *)
  0x4f54d2b0;       (* arm_SQRDMULH_VEC Q16 Q21 (Q4 :> LANE_H 1) 16 128 *)
  0x4e6b8695;       (* arm_ADD_VEC Q21 Q20 Q11 16 128 *)
  0x6e6b868b;       (* arm_SUB_VEC Q11 Q20 Q11 16 128 *)
  0x4f57c2b4;       (* arm_SQDMULH_VEC Q20 Q21 (Q7 :> LANE_H 1) 16 128 *)
  0x4f54d160;       (* arm_SQRDMULH_VEC Q0 Q11 (Q4 :> LANE_H 1) 16 128 *)
  0x4f44816b;       (* arm_MUL_VEC Q11 Q11 (Q4 :> LANE_H 0) 16 128 *)
  0x4f152694;       (* arm_SRSHR_VEC Q20 Q20 11 16 128 *)
  0x6f474201;       (* arm_MLS_VEC Q1 Q16 (Q7 :> LANE_H 0) 16 128 *)
  0x6f47400b;       (* arm_MLS_VEC Q11 Q0 (Q7 :> LANE_H 0) 16 128 *)
  0x6f474295;       (* arm_MLS_VEC Q21 Q20 (Q7 :> LANE_H 0) 16 128 *)
  0x3c9e0061;       (* arm_STR Q1 X3 (Immediate_Offset (word 18446744073709551584)) *)
  0x3c9f006b;       (* arm_STR Q11 X3 (Immediate_Offset (word 18446744073709551600)) *)
  0x3c9d0075;       (* arm_STR Q21 X3 (Immediate_Offset (word 18446744073709551568)) *)
  0xd2800084;       (* arm_MOV X4 (rvalue (word 4)) *)
  0x3cc20420;       (* arm_LDR Q0 X1 (Postimmediate_Offset (word 32)) *)
  0x3cdf0021;       (* arm_LDR Q1 X1 (Immediate_Offset (word 18446744073709551600)) *)
  0x3dc01006;       (* arm_LDR Q6 X0 (Immediate_Offset (word 64)) *)
  0x3dc00010;       (* arm_LDR Q16 X0 (Immediate_Offset (word 0)) *)
  0x3dc03012;       (* arm_LDR Q18 X0 (Immediate_Offset (word 192)) *)
  0x3dc0201b;       (* arm_LDR Q27 X0 (Immediate_Offset (word 128)) *)
  0x3dc0501a;       (* arm_LDR Q26 X0 (Immediate_Offset (word 320)) *)
  0x3dc04005;       (* arm_LDR Q5 X0 (Immediate_Offset (word 256)) *)
  0x3dc07004;       (* arm_LDR Q4 X0 (Immediate_Offset (word 448)) *)
  0x3dc06002;       (* arm_LDR Q2 X0 (Immediate_Offset (word 384)) *)
  0x4e66860c;       (* arm_ADD_VEC Q12 Q16 Q6 16 128 *)
  0x6e66860b;       (* arm_SUB_VEC Q11 Q16 Q6 16 128 *)
  0x4e728763;       (* arm_ADD_VEC Q3 Q27 Q18 16 128 *)
  0x6e728775;       (* arm_SUB_VEC Q21 Q27 Q18 16 128 *)
  0x6e7a84b2;       (* arm_SUB_VEC Q18 Q5 Q26 16 128 *)
  0x4f60896a;       (* arm_MUL_VEC Q10 Q11 (Q0 :> LANE_H 6) 16 128 *)
  0x4e7a84b8;       (* arm_ADD_VEC Q24 Q5 Q26 16 128 *)
  0x4f71d25b;       (* arm_SQRDMULH_VEC Q27 Q18 (Q1 :> LANE_H 3) 16 128 *)
  0x6e638593;       (* arm_SUB_VEC Q19 Q12 Q3 16 128 *)
  0x4e63859d;       (* arm_ADD_VEC Q29 Q12 Q3 16 128 *)
  0x4f61824e;       (* arm_MUL_VEC Q14 Q18 (Q1 :> LANE_H 2) 16 128 *)
  0x6e64844d;       (* arm_SUB_VEC Q13 Q2 Q4 16 128 *)
  0x4f51d2bf;       (* arm_SQRDMULH_VEC Q31 Q21 (Q1 :> LANE_H 1) 16 128 *)
  0x4f70d97a;       (* arm_SQRDMULH_VEC Q26 Q11 (Q0 :> LANE_H 7) 16 128 *)
  0x4f4182b5;       (* arm_MUL_VEC Q21 Q21 (Q1 :> LANE_H 0) 16 128 *)
  0xd1000484;       (* arm_SUB X4 X4 (rvalue (word 1)) *)
  0x6f47436e;       (* arm_MLS_VEC Q14 Q27 (Q7 :> LANE_H 0) 16 128 *)
  0x3dc0040f;       (* arm_LDR Q15 X0 (Immediate_Offset (word 16)) *)
  0x3dc03409;       (* arm_LDR Q9 X0 (Immediate_Offset (word 208)) *)
  0x4e648452;       (* arm_ADD_VEC Q18 Q2 Q4 16 128 *)
  0x4f4189b1;       (* arm_MUL_VEC Q17 Q13 (Q1 :> LANE_H 4) 16 128 *)
  0x3dc01414;       (* arm_LDR Q20 X0 (Immediate_Offset (word 80)) *)
  0x3dc06402;       (* arm_LDR Q2 X0 (Immediate_Offset (word 400)) *)
  0x3dc04405;       (* arm_LDR Q5 X0 (Immediate_Offset (word 272)) *)
  0x6e72870b;       (* arm_SUB_VEC Q11 Q24 Q18 16 128 *)
  0x4f51d9a8;       (* arm_SQRDMULH_VEC Q8 Q13 (Q1 :> LANE_H 5) 16 128 *)
  0x3dc05417;       (* arm_LDR Q23 X0 (Immediate_Offset (word 336)) *)
  0x4f50d970;       (* arm_SQRDMULH_VEC Q16 Q11 (Q0 :> LANE_H 5) 16 128 *)
  0x6e7485ec;       (* arm_SUB_VEC Q12 Q15 Q20 16 128 *)
  0x3dc02403;       (* arm_LDR Q3 X0 (Immediate_Offset (word 144)) *)
  0x4e7485fc;       (* arm_ADD_VEC Q28 Q15 Q20 16 128 *)
  0x4e728704;       (* arm_ADD_VEC Q4 Q24 Q18 16 128 *)
  0x4f40897e;       (* arm_MUL_VEC Q30 Q11 (Q0 :> LANE_H 4) 16 128 *)
  0x6e7784b4;       (* arm_SUB_VEC Q20 Q5 Q23 16 128 *)
  0x4e7784b8;       (* arm_ADD_VEC Q24 Q5 Q23 16 128 *)
  0x6f474111;       (* arm_MLS_VEC Q17 Q8 (Q7 :> LANE_H 0) 16 128 *)
  0x6e6487ab;       (* arm_SUB_VEC Q11 Q29 Q4 16 128 *)
  0x6f47421e;       (* arm_MLS_VEC Q30 Q16 (Q7 :> LANE_H 0) 16 128 *)
  0x4f71d29b;       (* arm_SQRDMULH_VEC Q27 Q20 (Q1 :> LANE_H 3) 16 128 *)
  0x4e7185d0;       (* arm_ADD_VEC Q16 Q14 Q17 16 128 *)
  0x6e7185cd;       (* arm_SUB_VEC Q13 Q14 Q17 16 128 *)
  0x4f70d277;       (* arm_SQRDMULH_VEC Q23 Q19 (Q0 :> LANE_H 3) 16 128 *)
  0x6e698479;       (* arm_SUB_VEC Q25 Q3 Q9 16 128 *)
  0x4e698465;       (* arm_ADD_VEC Q5 Q3 Q9 16 128 *)
  0x4f608266;       (* arm_MUL_VEC Q6 Q19 (Q0 :> LANE_H 2) 16 128 *)
  0x4f408168;       (* arm_MUL_VEC Q8 Q11 (Q0 :> LANE_H 0) 16 128 *)
  0x6f47434a;       (* arm_MLS_VEC Q10 Q26 (Q7 :> LANE_H 0) 16 128 *)
  0x4f70d99a;       (* arm_SQRDMULH_VEC Q26 Q12 (Q0 :> LANE_H 7) 16 128 *)
  0x4f61828e;       (* arm_MUL_VEC Q14 Q20 (Q1 :> LANE_H 2) 16 128 *)
  0x4f4089b6;       (* arm_MUL_VEC Q22 Q13 (Q0 :> LANE_H 4) 16 128 *)
  0x6f4743f5;       (* arm_MLS_VEC Q21 Q31 (Q7 :> LANE_H 0) 16 128 *)
  0x4f50d169;       (* arm_SQRDMULH_VEC Q9 Q11 (Q0 :> LANE_H 1) 16 128 *)
  0x4f50d9b4;       (* arm_SQRDMULH_VEC Q20 Q13 (Q0 :> LANE_H 5) 16 128 *)
  0x6e75854d;       (* arm_SUB_VEC Q13 Q10 Q21 16 128 *)
  0x4e75854f;       (* arm_ADD_VEC Q15 Q10 Q21 16 128 *)
  0x4f51d33f;       (* arm_SQRDMULH_VEC Q31 Q25 (Q1 :> LANE_H 1) 16 128 *)
  0x4f70d1b5;       (* arm_SQRDMULH_VEC Q21 Q13 (Q0 :> LANE_H 3) 16 128 *)
  0x6e7085f2;       (* arm_SUB_VEC Q18 Q15 Q16 16 128 *)
  0x4e7085e3;       (* arm_ADD_VEC Q3 Q15 Q16 16 128 *)
  0x4e6487a4;       (* arm_ADD_VEC Q4 Q29 Q4 16 128 *)
  0x6f474296;       (* arm_MLS_VEC Q22 Q20 (Q7 :> LANE_H 0) 16 128 *)
  0x6e658793;       (* arm_SUB_VEC Q19 Q28 Q5 16 128 *)
  0x6f4742e6;       (* arm_MLS_VEC Q6 Q23 (Q7 :> LANE_H 0) 16 128 *)
  0x3c810404;       (* arm_STR Q4 X0 (Postimmediate_Offset (word 16)) *)
  0x4f6081bd;       (* arm_MUL_VEC Q29 Q13 (Q0 :> LANE_H 2) 16 128 *)
  0x6f4742bd;       (* arm_MLS_VEC Q29 Q21 (Q7 :> LANE_H 0) 16 128 *)
  0x4e7e84cb;       (* arm_ADD_VEC Q11 Q6 Q30 16 128 *)
  0x6f474128;       (* arm_MLS_VEC Q8 Q9 (Q7 :> LANE_H 0) 16 128 *)
  0x3d801c0b;       (* arm_STR Q11 X0 (Immediate_Offset (word 112)) *)
  0x6e7e84cb;       (* arm_SUB_VEC Q11 Q6 Q30 16 128 *)
  0x4f50d255;       (* arm_SQRDMULH_VEC Q21 Q18 (Q0 :> LANE_H 1) 16 128 *)
  0x4f50d164;       (* arm_SQRDMULH_VEC Q4 Q11 (Q0 :> LANE_H 1) 16 128 *)
  0x3d803c08;       (* arm_STR Q8 X0 (Immediate_Offset (word 240)) *)
  0x6e7687b0;       (* arm_SUB_VEC Q16 Q29 Q22 16 128 *)
  0x3d800c03;       (* arm_STR Q3 X0 (Immediate_Offset (word 48)) *)
  0x4f408174;       (* arm_MUL_VEC Q20 Q11 (Q0 :> LANE_H 0) 16 128 *)
  0x4f50d20b;       (* arm_SQRDMULH_VEC Q11 Q16 (Q0 :> LANE_H 1) 16 128 *)
  0x6f474094;       (* arm_MLS_VEC Q20 Q4 (Q7 :> LANE_H 0) 16 128 *)
  0x4f408217;       (* arm_MUL_VEC Q23 Q16 (Q0 :> LANE_H 0) 16 128 *)
  0x6f474177;       (* arm_MLS_VEC Q23 Q11 (Q7 :> LANE_H 0) 16 128 *)
  0x3d805c14;       (* arm_STR Q20 X0 (Immediate_Offset (word 368)) *)
  0x4f40824b;       (* arm_MUL_VEC Q11 Q18 (Q0 :> LANE_H 0) 16 128 *)
  0x6f4742ab;       (* arm_MLS_VEC Q11 Q21 (Q7 :> LANE_H 0) 16 128 *)
  0x3d806c17;       (* arm_STR Q23 X0 (Immediate_Offset (word 432)) *)
  0x3dc07004;       (* arm_LDR Q4 X0 (Immediate_Offset (word 448)) *)
  0x4f60898a;       (* arm_MUL_VEC Q10 Q12 (Q0 :> LANE_H 6) 16 128 *)
  0x4e7687ac;       (* arm_ADD_VEC Q12 Q29 Q22 16 128 *)
  0x4e65879d;       (* arm_ADD_VEC Q29 Q28 Q5 16 128 *)
  0x4f418335;       (* arm_MUL_VEC Q21 Q25 (Q1 :> LANE_H 0) 16 128 *)
  0x3d802c0c;       (* arm_STR Q12 X0 (Immediate_Offset (word 176)) *)
  0x3d804c0b;       (* arm_STR Q11 X0 (Immediate_Offset (word 304)) *)
  0x6e64844d;       (* arm_SUB_VEC Q13 Q2 Q4 16 128 *)
  0xd1000484;       (* arm_SUB X4 X4 (rvalue (word 1)) *)
  0xb5fff664;       (* arm_CBNZ X4 (word 2096844) *)
  0x6f4743f5;       (* arm_MLS_VEC Q21 Q31 (Q7 :> LANE_H 0) 16 128 *)
  0x4e648456;       (* arm_ADD_VEC Q22 Q2 Q4 16 128 *)
  0x4f51d9af;       (* arm_SQRDMULH_VEC Q15 Q13 (Q1 :> LANE_H 5) 16 128 *)
  0x4e768708;       (* arm_ADD_VEC Q8 Q24 Q22 16 128 *)
  0x6e6887b1;       (* arm_SUB_VEC Q17 Q29 Q8 16 128 *)
  0x4f4189bc;       (* arm_MUL_VEC Q28 Q13 (Q1 :> LANE_H 4) 16 128 *)
  0x4e6887bd;       (* arm_ADD_VEC Q29 Q29 Q8 16 128 *)
  0x6e76870d;       (* arm_SUB_VEC Q13 Q24 Q22 16 128 *)
  0x4f50d239;       (* arm_SQRDMULH_VEC Q25 Q17 (Q0 :> LANE_H 1) 16 128 *)
  0x3c81041d;       (* arm_STR Q29 X0 (Postimmediate_Offset (word 16)) *)
  0x6f4741fc;       (* arm_MLS_VEC Q28 Q15 (Q7 :> LANE_H 0) 16 128 *)
  0x6f47434a;       (* arm_MLS_VEC Q10 Q26 (Q7 :> LANE_H 0) 16 128 *)
  0x4f40823d;       (* arm_MUL_VEC Q29 Q17 (Q0 :> LANE_H 0) 16 128 *)
  0x6f47433d;       (* arm_MLS_VEC Q29 Q25 (Q7 :> LANE_H 0) 16 128 *)
  0x6f47436e;       (* arm_MLS_VEC Q14 Q27 (Q7 :> LANE_H 0) 16 128 *)
  0x4f50d9b4;       (* arm_SQRDMULH_VEC Q20 Q13 (Q0 :> LANE_H 5) 16 128 *)
  0x3d803c1d;       (* arm_STR Q29 X0 (Immediate_Offset (word 240)) *)
  0x4f4089a4;       (* arm_MUL_VEC Q4 Q13 (Q0 :> LANE_H 4) 16 128 *)
  0x4e75854c;       (* arm_ADD_VEC Q12 Q10 Q21 16 128 *)
  0x4e7c85d6;       (* arm_ADD_VEC Q22 Q14 Q28 16 128 *)
  0x6e758548;       (* arm_SUB_VEC Q8 Q10 Q21 16 128 *)
  0x4f70d26b;       (* arm_SQRDMULH_VEC Q11 Q19 (Q0 :> LANE_H 3) 16 128 *)
  0x4e768586;       (* arm_ADD_VEC Q6 Q12 Q22 16 128 *)
  0x6e7c85c3;       (* arm_SUB_VEC Q3 Q14 Q28 16 128 *)
  0x6f474284;       (* arm_MLS_VEC Q4 Q20 (Q7 :> LANE_H 0) 16 128 *)
  0x3d800c06;       (* arm_STR Q6 X0 (Immediate_Offset (word 48)) *)
  0x6e768590;       (* arm_SUB_VEC Q16 Q12 Q22 16 128 *)
  0x4f60826c;       (* arm_MUL_VEC Q12 Q19 (Q0 :> LANE_H 2) 16 128 *)
  0x4f40886e;       (* arm_MUL_VEC Q14 Q3 (Q0 :> LANE_H 4) 16 128 *)
  0x4f50d876;       (* arm_SQRDMULH_VEC Q22 Q3 (Q0 :> LANE_H 5) 16 128 *)
  0x6f47416c;       (* arm_MLS_VEC Q12 Q11 (Q7 :> LANE_H 0) 16 128 *)
  0x4f608114;       (* arm_MUL_VEC Q20 Q8 (Q0 :> LANE_H 2) 16 128 *)
  0x6f4742ce;       (* arm_MLS_VEC Q14 Q22 (Q7 :> LANE_H 0) 16 128 *)
  0x4e648585;       (* arm_ADD_VEC Q5 Q12 Q4 16 128 *)
  0x6e648595;       (* arm_SUB_VEC Q21 Q12 Q4 16 128 *)
  0x4f70d104;       (* arm_SQRDMULH_VEC Q4 Q8 (Q0 :> LANE_H 3) 16 128 *)
  0x3d801c05;       (* arm_STR Q5 X0 (Immediate_Offset (word 112)) *)
  0x4f50d2a9;       (* arm_SQRDMULH_VEC Q9 Q21 (Q0 :> LANE_H 1) 16 128 *)
  0x4f4082b3;       (* arm_MUL_VEC Q19 Q21 (Q0 :> LANE_H 0) 16 128 *)
  0x6f474094;       (* arm_MLS_VEC Q20 Q4 (Q7 :> LANE_H 0) 16 128 *)
  0x6f474133;       (* arm_MLS_VEC Q19 Q9 (Q7 :> LANE_H 0) 16 128 *)
  0x4f50d209;       (* arm_SQRDMULH_VEC Q9 Q16 (Q0 :> LANE_H 1) 16 128 *)
  0x6e6e8685;       (* arm_SUB_VEC Q5 Q20 Q14 16 128 *)
  0x4e6e8684;       (* arm_ADD_VEC Q4 Q20 Q14 16 128 *)
  0x4f408214;       (* arm_MUL_VEC Q20 Q16 (Q0 :> LANE_H 0) 16 128 *)
  0x3d802c04;       (* arm_STR Q4 X0 (Immediate_Offset (word 176)) *)
  0x4f50d0b2;       (* arm_SQRDMULH_VEC Q18 Q5 (Q0 :> LANE_H 1) 16 128 *)
  0x3d805c13;       (* arm_STR Q19 X0 (Immediate_Offset (word 368)) *)
  0x4f4080b7;       (* arm_MUL_VEC Q23 Q5 (Q0 :> LANE_H 0) 16 128 *)
  0x6f474134;       (* arm_MLS_VEC Q20 Q9 (Q7 :> LANE_H 0) 16 128 *)
  0x6f474257;       (* arm_MLS_VEC Q23 Q18 (Q7 :> LANE_H 0) 16 128 *)
  0x3d804c14;       (* arm_STR Q20 X0 (Immediate_Offset (word 304)) *)
  0x3d806c17;       (* arm_STR Q23 X0 (Immediate_Offset (word 432)) *)
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

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let MLKEM_INTT_CORRECT = prove
 (`!a z_01234 z_56 (zetas_01234:int16 list) (zetas_56:int16 list) x pc.
      ALL (nonoverlapping (a,512))
          [(word pc,0x5b8); (z_01234,160); (z_56,768)]
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) mlkem_intt_mc /\
                read PC s = word (pc + 0x14) /\
                C_ARGUMENTS [a; z_01234; z_56] s /\
                wordlist_from_memory(z_01234,80) s = zetas_01234 /\
                wordlist_from_memory(z_56,384) s = zetas_56 /\
                !i. i < 256
                    ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                        x i)
           (\s. read PC s = word(pc + 0x5a0) /\
                (zetas_01234 = MAP iword intt_zetas_layer01234 /\
                 zetas_56 = MAP iword intt_zetas_layer56
                 ==> !i. i < 256
                         ==> let zi =
                        read(memory :> bytes16(word_add a (word(2 * i)))) s in
                        (ival zi == inverse_ntt (ival o x) i) (mod &3329) /\
                         abs(ival zi) <= &26624))
           (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
            MAYCHANGE [memory :> bytes(a,512)])`,
  MAP_EVERY X_GEN_TAC
   [`a:int64`; `z_01234:int64`; `z_56:int64`; `zetas_01234:int16 list`;
    `zetas_56:int16 list`; `x:num->int16`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; ALL] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

 (*** Globalize the assumptions on zeta constants by case splitting ***)

  ASM_CASES_TAC
   `zetas_01234:int16 list = MAP iword intt_zetas_layer01234 /\
    zetas_56:int16 list = MAP iword intt_zetas_layer56` THEN
  ASM_REWRITE_TAC[] THENL
   [FIRST_X_ASSUM(CONJUNCTS_THEN SUBST1_TAC);
    ARM_QUICKSIM_TAC MLKEM_INTT_EXEC
     [`read X0 s = a`; `read X1 s = z`; `read X2 s = w`;
      `read X3 s = i`; `read X4 s = i`]
     (1--1157)] THEN

  (*** Manually expand the cases in the hypotheses ***)

  CONV_TAC(RATOR_CONV(LAND_CONV(ONCE_DEPTH_CONV
   (EXPAND_CASES_CONV THENC ONCE_DEPTH_CONV NUM_MULT_CONV)))) THEN
  CONV_TAC(ONCE_DEPTH_CONV WORDLIST_FROM_MEMORY_CONV) THEN
  REWRITE_TAC[intt_zetas_layer01234; intt_zetas_layer56] THEN
  REWRITE_TAC[MAP; CONS_11] THEN CONV_TAC(ONCE_DEPTH_CONV WORD_IWORD_CONV) THEN
  REWRITE_TAC[WORD_ADD_0] THEN ENSURES_INIT_TAC "s0" THEN

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

  MAP_EVERY (fun n -> ARM_STEPS_TAC MLKEM_INTT_EXEC [n] THEN
                      SIMD_SIMPLIFY_TAC[barred; barmul])
            (1--1157) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN

  (*** Reverse the restructuring by splitting the 128-bit words up ***)

  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o
   CONV_RULE(SIMD_SIMPLIFY_CONV[]) o
   CONV_RULE(READ_MEMORY_SPLIT_CONV 3) o
   check (can (term_match [] `read qqq s:int128 = xxx`) o concl))) THEN

  (*** Turn the conclusion into an explicit conjunction and split it up ***)

  CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN REWRITE_TAC[INT_ABS_BOUNDS] THEN
  GEN_REWRITE_TAC (BINDER_CONV o RAND_CONV) [GSYM I_THM] THEN
  CONV_TAC(EXPAND_CASES_CONV THENC ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  ASM_REWRITE_TAC[I_THM; WORD_ADD_0] THEN DISCARD_STATE_TAC "s1157" THEN
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
 (`!a z_01234 z_56 zetas_01234 zetas_56 x pc stackpointer returnaddress.
      aligned 16 stackpointer /\
      ALLPAIRS nonoverlapping
       [(a,512); (word_sub stackpointer (word 64),64)]
       [(word pc,0x5b8); (z_01234,160); (z_56,768)] /\
      nonoverlapping (a,512) (word_sub stackpointer (word 64),64)
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) mlkem_intt_mc /\
                read PC s = word pc /\
                read SP s = stackpointer /\
                read X30 s = returnaddress /\
                C_ARGUMENTS [a; z_01234; z_56] s /\
                wordlist_from_memory(z_01234,80) s:int16 list = zetas_01234 /\
                wordlist_from_memory(z_56,384) s:int16 list = zetas_56 /\
                !i. i < 256
                    ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                        x i)
           (\s. read PC s = returnaddress /\
                (zetas_01234 = MAP iword intt_zetas_layer01234 /\
                 zetas_56 = MAP iword intt_zetas_layer56
                 ==> !i. i < 256
                         ==> let zi =
                        read(memory :> bytes16(word_add a (word(2 * i)))) s in
                        (ival zi == inverse_ntt (ival o x) i) (mod &3329) /\
                         abs(ival zi) <= &26624))
           (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [memory :> bytes(a,512);
                       memory :> bytes(word_sub stackpointer (word 64),64)])`,
  let TWEAK_CONV =
    ONCE_DEPTH_CONV let_CONV THENC
    ONCE_DEPTH_CONV WORDLIST_FROM_MEMORY_CONV THENC
    ONCE_DEPTH_CONV EXPAND_CASES_CONV THENC
    ONCE_DEPTH_CONV NUM_MULT_CONV THENC
    PURE_REWRITE_CONV [WORD_ADD_0] in
  REWRITE_TAC[fst MLKEM_INTT_EXEC] THEN
  CONV_TAC TWEAK_CONV THEN
  ARM_ADD_RETURN_STACK_TAC ~pre_post_nsteps:(5,5) MLKEM_INTT_EXEC
   (REWRITE_RULE[fst MLKEM_INTT_EXEC] (CONV_RULE TWEAK_CONV MLKEM_INTT_CORRECT))
    `[D8; D9; D10; D11; D12; D13; D14; D15]` 64);;


(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let full_spec = mk_safety_spec
    (assoc "mlkem_intt" subroutine_signatures)
    MLKEM_INTT_SUBROUTINE_CORRECT
    MLKEM_INTT_EXEC;;

let MLKEM_INTT_SUBROUTINE_SAFE = time prove
 (`exists f_events.
       forall a z_01234 z_56 pc stackpointer returnaddress.
           aligned 16 stackpointer /\
           ALLPAIRS nonoverlapping
           [a,512; word_sub stackpointer (word 64),64]
           [word pc,1464; z_01234,160; z_56,768] /\
           nonoverlapping (a,512) (word_sub stackpointer (word 64),64)
           ==> ensures arm
               (\s.
                    aligned_bytes_loaded s (word pc) mlkem_intt_mc /\
                    read PC s = word pc /\
                    read X30 s = returnaddress /\
                    read SP s = stackpointer /\
                    C_ARGUMENTS [a; z_01234; z_56] s /\
                    read events s = e)
               (\s.
                    exists e2.
                        read PC s = returnaddress /\
                        read events s = APPEND e2 e /\
                        e2 =
                        f_events z_01234 z_56 a pc
                        (word_sub stackpointer (word 64))
                        returnaddress /\
                        memaccess_inbounds e2
                        [a,512; z_01234,160; z_56,768; a,512;
                         word_sub stackpointer (word 64),64]
                        [a,512; word_sub stackpointer (word 64),64])
               (\s s'. true)`,
  ASSERT_GOAL_TAC full_spec THEN
  PROVE_SAFETY_SPEC MLKEM_INTT_EXEC);;
