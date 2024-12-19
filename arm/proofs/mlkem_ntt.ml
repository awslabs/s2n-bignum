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
  0x6d0027e8;       (* arm_STP D8 D9 SP (Immediate_Offset (word 0)) *)
  0x6d012fea;       (* arm_STP D10 D11 SP (Immediate_Offset (word 16)) *)
  0x6d0237ec;       (* arm_STP D12 D13 SP (Immediate_Offset (word 32)) *)
  0x6d033fee;       (* arm_STP D14 D15 SP (Immediate_Offset (word 48)) *)
  0x10002821;       (* arm_ADR X1 (word 1284) *)
  0x91000021;       (* arm_ADD X1 X1 (rvalue (word 0)) *)
  0x10002ce2;       (* arm_ADR X2 (word 1436) *)
  0x91000042;       (* arm_ADD X2 X2 (rvalue (word 0)) *)
  0x4e020fe7;       (* arm_DUP_GEN Q7 XZR 16 128 *)
  0x5281a025;       (* arm_MOV W5 (rvalue (word 3329)) *)
  0x4e021ca7;       (* arm_INS_GEN Q7 W5 0 16 *)
  0x5289d7e5;       (* arm_MOV W5 (rvalue (word 20159)) *)
  0x4e061ca7;       (* arm_INS_GEN Q7 W5 16 16 *)
  0xaa0003e3;       (* arm_MOV X3 X0 *)
  0xd2800084;       (* arm_MOV X4 (rvalue (word 4)) *)
  0x3cc20420;       (* arm_LDR Q0 X1 (Postimmediate_Offset (word 32)) *)
  0x3cdf0021;       (* arm_LDR Q1 X1 (Immediate_Offset (word 18446744073709551600)) *)
  0x3dc06017;       (* arm_LDR Q23 X0 (Immediate_Offset (word 384)) *)
  0x3dc00019;       (* arm_LDR Q25 X0 (Immediate_Offset (word 0)) *)
  0x3dc0400f;       (* arm_LDR Q15 X0 (Immediate_Offset (word 256)) *)
  0x3dc03013;       (* arm_LDR Q19 X0 (Immediate_Offset (word 192)) *)
  0x3dc0701e;       (* arm_LDR Q30 X0 (Immediate_Offset (word 448)) *)
  0x3dc0201f;       (* arm_LDR Q31 X0 (Immediate_Offset (word 128)) *)
  0x3dc0500e;       (* arm_LDR Q14 X0 (Immediate_Offset (word 320)) *)
  0x3dc0100c;       (* arm_LDR Q12 X0 (Immediate_Offset (word 64)) *)
  0x4f50d2f2;       (* arm_SQRDMULH_VEC Q18 Q23 (Q0 :> LANE_H 1) 16 128 *)
  0x4f4082f7;       (* arm_MUL_VEC Q23 Q23 (Q0 :> LANE_H 0) 16 128 *)
  0x4f50d1e2;       (* arm_SQRDMULH_VEC Q2 Q15 (Q0 :> LANE_H 1) 16 128 *)
  0x4f4081e3;       (* arm_MUL_VEC Q3 Q15 (Q0 :> LANE_H 0) 16 128 *)
  0x4f50d3cf;       (* arm_SQRDMULH_VEC Q15 Q30 (Q0 :> LANE_H 1) 16 128 *)
  0x4f4083de;       (* arm_MUL_VEC Q30 Q30 (Q0 :> LANE_H 0) 16 128 *)
  0x6f474257;       (* arm_MLS_VEC Q23 Q18 (Q7 :> LANE_H 0) 16 128 *)
  0x6f4741fe;       (* arm_MLS_VEC Q30 Q15 (Q7 :> LANE_H 0) 16 128 *)
  0x4f4081c5;       (* arm_MUL_VEC Q5 Q14 (Q0 :> LANE_H 0) 16 128 *)
  0x4e7787e6;       (* arm_ADD_VEC Q6 Q31 Q23 16 128 *)
  0x6e7787ed;       (* arm_SUB_VEC Q13 Q31 Q23 16 128 *)
  0x4f50d1d7;       (* arm_SQRDMULH_VEC Q23 Q14 (Q0 :> LANE_H 1) 16 128 *)
  0x6e7e866f;       (* arm_SUB_VEC Q15 Q19 Q30 16 128 *)
  0x4e7e8678;       (* arm_ADD_VEC Q24 Q19 Q30 16 128 *)
  0x6f474043;       (* arm_MLS_VEC Q3 Q2 (Q7 :> LANE_H 0) 16 128 *)
  0x4f50d9f3;       (* arm_SQRDMULH_VEC Q19 Q15 (Q0 :> LANE_H 5) 16 128 *)
  0x6f4742e5;       (* arm_MLS_VEC Q5 Q23 (Q7 :> LANE_H 0) 16 128 *)
  0x4e63872e;       (* arm_ADD_VEC Q14 Q25 Q3 16 128 *)
  0x4f70d0ca;       (* arm_SQRDMULH_VEC Q10 Q6 (Q0 :> LANE_H 3) 16 128 *)
  0x4f4089ff;       (* arm_MUL_VEC Q31 Q15 (Q0 :> LANE_H 4) 16 128 *)
  0x6e658591;       (* arm_SUB_VEC Q17 Q12 Q5 16 128 *)
  0x6f47427f;       (* arm_MLS_VEC Q31 Q19 (Q7 :> LANE_H 0) 16 128 *)
  0x4f70d302;       (* arm_SQRDMULH_VEC Q2 Q24 (Q0 :> LANE_H 3) 16 128 *)
  0x4f4089ab;       (* arm_MUL_VEC Q11 Q13 (Q0 :> LANE_H 4) 16 128 *)
  0xd1000484;       (* arm_SUB X4 X4 (rvalue (word 1)) *)
  0x3dc06412;       (* arm_LDR Q18 X0 (Immediate_Offset (word 400)) *)
  0x4f6080d0;       (* arm_MUL_VEC Q16 Q6 (Q0 :> LANE_H 2) 16 128 *)
  0x6e63873c;       (* arm_SUB_VEC Q28 Q25 Q3 16 128 *)
  0x3dc00419;       (* arm_LDR Q25 X0 (Immediate_Offset (word 16)) *)
  0x6f474150;       (* arm_MLS_VEC Q16 Q10 (Q7 :> LANE_H 0) 16 128 *)
  0x3dc04417;       (* arm_LDR Q23 X0 (Immediate_Offset (word 272)) *)
  0x3dc03409;       (* arm_LDR Q9 X0 (Immediate_Offset (word 208)) *)
  0x3dc02413;       (* arm_LDR Q19 X0 (Immediate_Offset (word 144)) *)
  0x4e658588;       (* arm_ADD_VEC Q8 Q12 Q5 16 128 *)
  0x4f50d25d;       (* arm_SQRDMULH_VEC Q29 Q18 (Q0 :> LANE_H 1) 16 128 *)
  0x3dc07416;       (* arm_LDR Q22 X0 (Immediate_Offset (word 464)) *)
  0x4e7f862a;       (* arm_ADD_VEC Q10 Q17 Q31 16 128 *)
  0x3dc05404;       (* arm_LDR Q4 X0 (Immediate_Offset (word 336)) *)
  0x4f50d2ec;       (* arm_SQRDMULH_VEC Q12 Q23 (Q0 :> LANE_H 1) 16 128 *)
  0x4f4082e3;       (* arm_MUL_VEC Q3 Q23 (Q0 :> LANE_H 0) 16 128 *)
  0x4f408254;       (* arm_MUL_VEC Q20 Q18 (Q0 :> LANE_H 0) 16 128 *)
  0x6f4743b4;       (* arm_MLS_VEC Q20 Q29 (Q7 :> LANE_H 0) 16 128 *)
  0x4f50d2d2;       (* arm_SQRDMULH_VEC Q18 Q22 (Q0 :> LANE_H 1) 16 128 *)
  0x4f408085;       (* arm_MUL_VEC Q5 Q4 (Q0 :> LANE_H 0) 16 128 *)
  0x4f50d9a6;       (* arm_SQRDMULH_VEC Q6 Q13 (Q0 :> LANE_H 5) 16 128 *)
  0x4f608318;       (* arm_MUL_VEC Q24 Q24 (Q0 :> LANE_H 2) 16 128 *)
  0x6f474058;       (* arm_MLS_VEC Q24 Q2 (Q7 :> LANE_H 0) 16 128 *)
  0x4f4082da;       (* arm_MUL_VEC Q26 Q22 (Q0 :> LANE_H 0) 16 128 *)
  0x6f4740cb;       (* arm_MLS_VEC Q11 Q6 (Q7 :> LANE_H 0) 16 128 *)
  0x4e788502;       (* arm_ADD_VEC Q2 Q8 Q24 16 128 *)
  0x6f47425a;       (* arm_MLS_VEC Q26 Q18 (Q7 :> LANE_H 0) 16 128 *)
  0x4f60884d;       (* arm_MUL_VEC Q13 Q2 (Q0 :> LANE_H 6) 16 128 *)
  0x4e6b878f;       (* arm_ADD_VEC Q15 Q28 Q11 16 128 *)
  0x4f50d095;       (* arm_SQRDMULH_VEC Q21 Q4 (Q0 :> LANE_H 1) 16 128 *)
  0x6e6b878b;       (* arm_SUB_VEC Q11 Q28 Q11 16 128 *)
  0x6e7f8632;       (* arm_SUB_VEC Q18 Q17 Q31 16 128 *)
  0x4f61815f;       (* arm_MUL_VEC Q31 Q10 (Q1 :> LANE_H 2) 16 128 *)
  0x4f70d85b;       (* arm_SQRDMULH_VEC Q27 Q2 (Q0 :> LANE_H 7) 16 128 *)
  0x4f51da5c;       (* arm_SQRDMULH_VEC Q28 Q18 (Q1 :> LANE_H 5) 16 128 *)
  0x4f418a46;       (* arm_MUL_VEC Q6 Q18 (Q1 :> LANE_H 4) 16 128 *)
  0x6f47436d;       (* arm_MLS_VEC Q13 Q27 (Q7 :> LANE_H 0) 16 128 *)
  0x6f474386;       (* arm_MLS_VEC Q6 Q28 (Q7 :> LANE_H 0) 16 128 *)
  0x4f71d151;       (* arm_SQRDMULH_VEC Q17 Q10 (Q1 :> LANE_H 3) 16 128 *)
  0x6f474183;       (* arm_MLS_VEC Q3 Q12 (Q7 :> LANE_H 0) 16 128 *)
  0x4e66856a;       (* arm_ADD_VEC Q10 Q11 Q6 16 128 *)
  0x6e78851b;       (* arm_SUB_VEC Q27 Q8 Q24 16 128 *)
  0x6f4742a5;       (* arm_MLS_VEC Q5 Q21 (Q7 :> LANE_H 0) 16 128 *)
  0x3d80600a;       (* arm_STR Q10 X0 (Immediate_Offset (word 384)) *)
  0x4e7085ca;       (* arm_ADD_VEC Q10 Q14 Q16 16 128 *)
  0x4f51d368;       (* arm_SQRDMULH_VEC Q8 Q27 (Q1 :> LANE_H 1) 16 128 *)
  0x3dc0140c;       (* arm_LDR Q12 X0 (Immediate_Offset (word 80)) *)
  0x6e668562;       (* arm_SUB_VEC Q2 Q11 Q6 16 128 *)
  0x6f47423f;       (* arm_MLS_VEC Q31 Q17 (Q7 :> LANE_H 0) 16 128 *)
  0x4e6d854b;       (* arm_ADD_VEC Q11 Q10 Q13 16 128 *)
  0x6e6d854a;       (* arm_SUB_VEC Q10 Q10 Q13 16 128 *)
  0x3d807002;       (* arm_STR Q2 X0 (Immediate_Offset (word 448)) *)
  0x4f418375;       (* arm_MUL_VEC Q21 Q27 (Q1 :> LANE_H 0) 16 128 *)
  0x6e658591;       (* arm_SUB_VEC Q17 Q12 Q5 16 128 *)
  0x3d80100a;       (* arm_STR Q10 X0 (Immediate_Offset (word 64)) *)
  0x4e748666;       (* arm_ADD_VEC Q6 Q19 Q20 16 128 *)
  0x6f474115;       (* arm_MLS_VEC Q21 Q8 (Q7 :> LANE_H 0) 16 128 *)
  0x6e7a853d;       (* arm_SUB_VEC Q29 Q9 Q26 16 128 *)
  0x4e7f85e4;       (* arm_ADD_VEC Q4 Q15 Q31 16 128 *)
  0x6e7085d6;       (* arm_SUB_VEC Q22 Q14 Q16 16 128 *)
  0x4f50dbad;       (* arm_SQRDMULH_VEC Q13 Q29 (Q0 :> LANE_H 5) 16 128 *)
  0x3d804004;       (* arm_STR Q4 X0 (Immediate_Offset (word 256)) *)
  0x4e63872e;       (* arm_ADD_VEC Q14 Q25 Q3 16 128 *)
  0x4f70d0ca;       (* arm_SQRDMULH_VEC Q10 Q6 (Q0 :> LANE_H 3) 16 128 *)
  0x6e7586dc;       (* arm_SUB_VEC Q28 Q22 Q21 16 128 *)
  0x6e7f85fb;       (* arm_SUB_VEC Q27 Q15 Q31 16 128 *)
  0x4f408bbf;       (* arm_MUL_VEC Q31 Q29 (Q0 :> LANE_H 4) 16 128 *)
  0x4e7586de;       (* arm_ADD_VEC Q30 Q22 Q21 16 128 *)
  0x4e7a8538;       (* arm_ADD_VEC Q24 Q9 Q26 16 128 *)
  0x6f4741bf;       (* arm_MLS_VEC Q31 Q13 (Q7 :> LANE_H 0) 16 128 *)
  0x6e74866d;       (* arm_SUB_VEC Q13 Q19 Q20 16 128 *)
  0x3d80201e;       (* arm_STR Q30 X0 (Immediate_Offset (word 128)) *)
  0x3d80501b;       (* arm_STR Q27 X0 (Immediate_Offset (word 320)) *)
  0x4f70d302;       (* arm_SQRDMULH_VEC Q2 Q24 (Q0 :> LANE_H 3) 16 128 *)
  0x3d80301c;       (* arm_STR Q28 X0 (Immediate_Offset (word 192)) *)
  0x3c81040b;       (* arm_STR Q11 X0 (Postimmediate_Offset (word 16)) *)
  0x4f4089ab;       (* arm_MUL_VEC Q11 Q13 (Q0 :> LANE_H 4) 16 128 *)
  0xd1000484;       (* arm_SUB X4 X4 (rvalue (word 1)) *)
  0xb5fff664;       (* arm_CBNZ X4 (word 2096844) *)
  0x6e7f863d;       (* arm_SUB_VEC Q29 Q17 Q31 16 128 *)
  0x4f6080c4;       (* arm_MUL_VEC Q4 Q6 (Q0 :> LANE_H 2) 16 128 *)
  0x6e638733;       (* arm_SUB_VEC Q19 Q25 Q3 16 128 *)
  0x4e658596;       (* arm_ADD_VEC Q22 Q12 Q5 16 128 *)
  0x6f474144;       (* arm_MLS_VEC Q4 Q10 (Q7 :> LANE_H 0) 16 128 *)
  0x4f608315;       (* arm_MUL_VEC Q21 Q24 (Q0 :> LANE_H 2) 16 128 *)
  0x6f474055;       (* arm_MLS_VEC Q21 Q2 (Q7 :> LANE_H 0) 16 128 *)
  0x6e6485dc;       (* arm_SUB_VEC Q28 Q14 Q4 16 128 *)
  0x4f50d9a9;       (* arm_SQRDMULH_VEC Q9 Q13 (Q0 :> LANE_H 5) 16 128 *)
  0x4e6485d7;       (* arm_ADD_VEC Q23 Q14 Q4 16 128 *)
  0x4f51dba8;       (* arm_SQRDMULH_VEC Q8 Q29 (Q1 :> LANE_H 5) 16 128 *)
  0x4f418bb4;       (* arm_MUL_VEC Q20 Q29 (Q1 :> LANE_H 4) 16 128 *)
  0x4e7586c6;       (* arm_ADD_VEC Q6 Q22 Q21 16 128 *)
  0x4f70d8de;       (* arm_SQRDMULH_VEC Q30 Q6 (Q0 :> LANE_H 7) 16 128 *)
  0x6f474114;       (* arm_MLS_VEC Q20 Q8 (Q7 :> LANE_H 0) 16 128 *)
  0x4f6088c8;       (* arm_MUL_VEC Q8 Q6 (Q0 :> LANE_H 6) 16 128 *)
  0x4e7f8639;       (* arm_ADD_VEC Q25 Q17 Q31 16 128 *)
  0x6f4743c8;       (* arm_MLS_VEC Q8 Q30 (Q7 :> LANE_H 0) 16 128 *)
  0x4f71d33a;       (* arm_SQRDMULH_VEC Q26 Q25 (Q1 :> LANE_H 3) 16 128 *)
  0x6e7586c5;       (* arm_SUB_VEC Q5 Q22 Q21 16 128 *)
  0x6f47412b;       (* arm_MLS_VEC Q11 Q9 (Q7 :> LANE_H 0) 16 128 *)
  0x4e6886e9;       (* arm_ADD_VEC Q9 Q23 Q8 16 128 *)
  0x4f618323;       (* arm_MUL_VEC Q3 Q25 (Q1 :> LANE_H 2) 16 128 *)
  0x6e6886e6;       (* arm_SUB_VEC Q6 Q23 Q8 16 128 *)
  0x3c810409;       (* arm_STR Q9 X0 (Postimmediate_Offset (word 16)) *)
  0x3d800c06;       (* arm_STR Q6 X0 (Immediate_Offset (word 48)) *)
  0x4f51d0bf;       (* arm_SQRDMULH_VEC Q31 Q5 (Q1 :> LANE_H 1) 16 128 *)
  0x4e6b867b;       (* arm_ADD_VEC Q27 Q19 Q11 16 128 *)
  0x6f474343;       (* arm_MLS_VEC Q3 Q26 (Q7 :> LANE_H 0) 16 128 *)
  0x6e6b867a;       (* arm_SUB_VEC Q26 Q19 Q11 16 128 *)
  0x4f4180aa;       (* arm_MUL_VEC Q10 Q5 (Q1 :> LANE_H 0) 16 128 *)
  0x6e748749;       (* arm_SUB_VEC Q9 Q26 Q20 16 128 *)
  0x4e74874f;       (* arm_ADD_VEC Q15 Q26 Q20 16 128 *)
  0x6f4743ea;       (* arm_MLS_VEC Q10 Q31 (Q7 :> LANE_H 0) 16 128 *)
  0x3d806c09;       (* arm_STR Q9 X0 (Immediate_Offset (word 432)) *)
  0x4e63877d;       (* arm_ADD_VEC Q29 Q27 Q3 16 128 *)
  0x3d805c0f;       (* arm_STR Q15 X0 (Immediate_Offset (word 368)) *)
  0x3d803c1d;       (* arm_STR Q29 X0 (Immediate_Offset (word 240)) *)
  0x6e638764;       (* arm_SUB_VEC Q4 Q27 Q3 16 128 *)
  0x6e6a879a;       (* arm_SUB_VEC Q26 Q28 Q10 16 128 *)
  0x4e6a878f;       (* arm_ADD_VEC Q15 Q28 Q10 16 128 *)
  0x3d804c04;       (* arm_STR Q4 X0 (Immediate_Offset (word 304)) *)
  0x3d802c1a;       (* arm_STR Q26 X0 (Immediate_Offset (word 176)) *)
  0x3d801c0f;       (* arm_STR Q15 X0 (Immediate_Offset (word 112)) *)
  0xaa0303e0;       (* arm_MOV X0 X3 *)
  0xd2800104;       (* arm_MOV X4 (rvalue (word 8)) *)
  0x3dc00c10;       (* arm_LDR Q16 X0 (Immediate_Offset (word 48)) *)
  0x3cc10426;       (* arm_LDR Q6 X1 (Postimmediate_Offset (word 16)) *)
  0x3dc00014;       (* arm_LDR Q20 X0 (Immediate_Offset (word 0)) *)
  0x4f56d20d;       (* arm_SQRDMULH_VEC Q13 Q16 (Q6 :> LANE_H 1) 16 128 *)
  0x3dc0080a;       (* arm_LDR Q10 X0 (Immediate_Offset (word 32)) *)
  0x3dc0041d;       (* arm_LDR Q29 X0 (Immediate_Offset (word 16)) *)
  0x3dc00c52;       (* arm_LDR Q18 X2 (Immediate_Offset (word 48)) *)
  0x4f46821b;       (* arm_MUL_VEC Q27 Q16 (Q6 :> LANE_H 0) 16 128 *)
  0x3dc01045;       (* arm_LDR Q5 X2 (Immediate_Offset (word 64)) *)
  0x4f56d15a;       (* arm_SQRDMULH_VEC Q26 Q10 (Q6 :> LANE_H 1) 16 128 *)
  0x6f4741bb;       (* arm_MLS_VEC Q27 Q13 (Q7 :> LANE_H 0) 16 128 *)
  0x4f46814e;       (* arm_MUL_VEC Q14 Q10 (Q6 :> LANE_H 0) 16 128 *)
  0x6f47434e;       (* arm_MLS_VEC Q14 Q26 (Q7 :> LANE_H 0) 16 128 *)
  0x6e7b87ad;       (* arm_SUB_VEC Q13 Q29 Q27 16 128 *)
  0x4f56d9b6;       (* arm_SQRDMULH_VEC Q22 Q13 (Q6 :> LANE_H 5) 16 128 *)
  0x4e7b87b0;       (* arm_ADD_VEC Q16 Q29 Q27 16 128 *)
  0x4f4689be;       (* arm_MUL_VEC Q30 Q13 (Q6 :> LANE_H 4) 16 128 *)
  0x6e6e869f;       (* arm_SUB_VEC Q31 Q20 Q14 16 128 *)
  0x4f76d21a;       (* arm_SQRDMULH_VEC Q26 Q16 (Q6 :> LANE_H 3) 16 128 *)
  0x6f4742de;       (* arm_MLS_VEC Q30 Q22 (Q7 :> LANE_H 0) 16 128 *)
  0x4f66821d;       (* arm_MUL_VEC Q29 Q16 (Q6 :> LANE_H 2) 16 128 *)
  0x6f47435d;       (* arm_MLS_VEC Q29 Q26 (Q7 :> LANE_H 0) 16 128 *)
  0xd1000484;       (* arm_SUB X4 X4 (rvalue (word 1)) *)
  0x3dc01811;       (* arm_LDR Q17 X0 (Immediate_Offset (word 96)) *)
  0x3cc10428;       (* arm_LDR Q8 X1 (Postimmediate_Offset (word 16)) *)
  0x6e7e87f0;       (* arm_SUB_VEC Q16 Q31 Q30 16 128 *)
  0x4e7e87f7;       (* arm_ADD_VEC Q23 Q31 Q30 16 128 *)
  0x4e6e8683;       (* arm_ADD_VEC Q3 Q20 Q14 16 128 *)
  0x3dc01c09;       (* arm_LDR Q9 X0 (Immediate_Offset (word 112)) *)
  0x4e902aec;       (* arm_TRN1 Q12 Q23 Q16 32 128 *)
  0x3dc01014;       (* arm_LDR Q20 X0 (Immediate_Offset (word 64)) *)
  0x4f58d222;       (* arm_SQRDMULH_VEC Q2 Q17 (Q8 :> LANE_H 1) 16 128 *)
  0x6e7d847e;       (* arm_SUB_VEC Q30 Q3 Q29 16 128 *)
  0x3dc01404;       (* arm_LDR Q4 X0 (Immediate_Offset (word 80)) *)
  0x4e7d846b;       (* arm_ADD_VEC Q11 Q3 Q29 16 128 *)
  0x4e906ae3;       (* arm_TRN2 Q3 Q23 Q16 32 128 *)
  0x4f58d120;       (* arm_SQRDMULH_VEC Q0 Q9 (Q8 :> LANE_H 1) 16 128 *)
  0x3dc00457;       (* arm_LDR Q23 X2 (Immediate_Offset (word 16)) *)
  0x4e9e696e;       (* arm_TRN2 Q14 Q11 Q30 32 128 *)
  0x4e9e296d;       (* arm_TRN1 Q13 Q11 Q30 32 128 *)
  0x3cc60453;       (* arm_LDR Q19 X2 (Postimmediate_Offset (word 96)) *)
  0x4f48812a;       (* arm_MUL_VEC Q10 Q9 (Q8 :> LANE_H 0) 16 128 *)
  0x4ec369cf;       (* arm_TRN2 Q15 Q14 Q3 64 128 *)
  0x3cdf0049;       (* arm_LDR Q9 X2 (Immediate_Offset (word 18446744073709551600)) *)
  0x4ecc69be;       (* arm_TRN2 Q30 Q13 Q12 64 128 *)
  0x6e77b5ff;       (* arm_SQRDMULH_VEC Q31 Q15 Q23 16 128 *)
  0x4ecc29ac;       (* arm_TRN1 Q12 Q13 Q12 64 128 *)
  0x4e739de6;       (* arm_MUL_VEC Q6 Q15 Q19 16 128 *)
  0x6e77b7cf;       (* arm_SQRDMULH_VEC Q15 Q30 Q23 16 128 *)
  0x6f4743e6;       (* arm_MLS_VEC Q6 Q31 (Q7 :> LANE_H 0) 16 128 *)
  0x4ec329d7;       (* arm_TRN1 Q23 Q14 Q3 64 128 *)
  0x4e739fde;       (* arm_MUL_VEC Q30 Q30 Q19 16 128 *)
  0x6f4741fe;       (* arm_MLS_VEC Q30 Q15 (Q7 :> LANE_H 0) 16 128 *)
  0x3cdc0055;       (* arm_LDR Q21 X2 (Immediate_Offset (word 18446744073709551552)) *)
  0x6e6686f0;       (* arm_SUB_VEC Q16 Q23 Q6 16 128 *)
  0x6f47400a;       (* arm_MLS_VEC Q10 Q0 (Q7 :> LANE_H 0) 16 128 *)
  0x6e69b61d;       (* arm_SQRDMULH_VEC Q29 Q16 Q9 16 128 *)
  0x4e6686e9;       (* arm_ADD_VEC Q9 Q23 Q6 16 128 *)
  0x6e7e8583;       (* arm_SUB_VEC Q3 Q12 Q30 16 128 *)
  0x4e7e858f;       (* arm_ADD_VEC Q15 Q12 Q30 16 128 *)
  0x6e72b53e;       (* arm_SQRDMULH_VEC Q30 Q9 Q18 16 128 *)
  0x4e6a848b;       (* arm_ADD_VEC Q11 Q4 Q10 16 128 *)
  0x4e659e0d;       (* arm_MUL_VEC Q13 Q16 Q5 16 128 *)
  0x6f4743ad;       (* arm_MLS_VEC Q13 Q29 (Q7 :> LANE_H 0) 16 128 *)
  0x4e759d2c;       (* arm_MUL_VEC Q12 Q9 Q21 16 128 *)
  0x6f4743cc;       (* arm_MLS_VEC Q12 Q30 (Q7 :> LANE_H 0) 16 128 *)
  0x6e6d8461;       (* arm_SUB_VEC Q1 Q3 Q13 16 128 *)
  0x4f48822e;       (* arm_MUL_VEC Q14 Q17 (Q8 :> LANE_H 0) 16 128 *)
  0x4e6d847f;       (* arm_ADD_VEC Q31 Q3 Q13 16 128 *)
  0x6e6a8483;       (* arm_SUB_VEC Q3 Q4 Q10 16 128 *)
  0x6f47404e;       (* arm_MLS_VEC Q14 Q2 (Q7 :> LANE_H 0) 16 128 *)
  0x4e812bf3;       (* arm_TRN1 Q19 Q31 Q1 32 128 *)
  0x6e6c85fd;       (* arm_SUB_VEC Q29 Q15 Q12 16 128 *)
  0x4e6c85ec;       (* arm_ADD_VEC Q12 Q15 Q12 16 128 *)
  0x4f58d869;       (* arm_SQRDMULH_VEC Q9 Q3 (Q8 :> LANE_H 5) 16 128 *)
  0x4e816bf0;       (* arm_TRN2 Q16 Q31 Q1 32 128 *)
  0x4f78d17a;       (* arm_SQRDMULH_VEC Q26 Q11 (Q8 :> LANE_H 3) 16 128 *)
  0x4e9d698d;       (* arm_TRN2 Q13 Q12 Q29 32 128 *)
  0x4e9d298c;       (* arm_TRN1 Q12 Q12 Q29 32 128 *)
  0x3dc00c52;       (* arm_LDR Q18 X2 (Immediate_Offset (word 48)) *)
  0x4f48887e;       (* arm_MUL_VEC Q30 Q3 (Q8 :> LANE_H 4) 16 128 *)
  0x4ed069b7;       (* arm_TRN2 Q23 Q13 Q16 64 128 *)
  0x4ed029a0;       (* arm_TRN1 Q0 Q13 Q16 64 128 *)
  0x3dc01045;       (* arm_LDR Q5 X2 (Immediate_Offset (word 64)) *)
  0x6f47413e;       (* arm_MLS_VEC Q30 Q9 (Q7 :> LANE_H 0) 16 128 *)
  0x3d800c17;       (* arm_STR Q23 X0 (Immediate_Offset (word 48)) *)
  0x3d800400;       (* arm_STR Q0 X0 (Immediate_Offset (word 16)) *)
  0x4ed32996;       (* arm_TRN1 Q22 Q12 Q19 64 128 *)
  0x4f68817d;       (* arm_MUL_VEC Q29 Q11 (Q8 :> LANE_H 2) 16 128 *)
  0x4ed3698f;       (* arm_TRN2 Q15 Q12 Q19 64 128 *)
  0x3c840416;       (* arm_STR Q22 X0 (Postimmediate_Offset (word 64)) *)
  0x6e6e869f;       (* arm_SUB_VEC Q31 Q20 Q14 16 128 *)
  0x6f47435d;       (* arm_MLS_VEC Q29 Q26 (Q7 :> LANE_H 0) 16 128 *)
  0x3c9e000f;       (* arm_STR Q15 X0 (Immediate_Offset (word 18446744073709551584)) *)
  0xd1000484;       (* arm_SUB X4 X4 (rvalue (word 1)) *)
  0xb5fff704;       (* arm_CBNZ X4 (word 2096864) *)
  0x4e6e868f;       (* arm_ADD_VEC Q15 Q20 Q14 16 128 *)
  0x6e7e87f3;       (* arm_SUB_VEC Q19 Q31 Q30 16 128 *)
  0x4e7e87ec;       (* arm_ADD_VEC Q12 Q31 Q30 16 128 *)
  0x3dc01456;       (* arm_LDR Q22 X2 (Immediate_Offset (word 80)) *)
  0x4e7d85fa;       (* arm_ADD_VEC Q26 Q15 Q29 16 128 *)
  0x6e7d85ef;       (* arm_SUB_VEC Q15 Q15 Q29 16 128 *)
  0x4e936982;       (* arm_TRN2 Q2 Q12 Q19 32 128 *)
  0x4e932998;       (* arm_TRN1 Q24 Q12 Q19 32 128 *)
  0x4e8f6b40;       (* arm_TRN2 Q0 Q26 Q15 32 128 *)
  0x3dc0045e;       (* arm_LDR Q30 X2 (Immediate_Offset (word 16)) *)
  0x3cc6044a;       (* arm_LDR Q10 X2 (Postimmediate_Offset (word 96)) *)
  0x4e8f2b4e;       (* arm_TRN1 Q14 Q26 Q15 32 128 *)
  0x3cdc0057;       (* arm_LDR Q23 X2 (Immediate_Offset (word 18446744073709551552)) *)
  0x4ec26808;       (* arm_TRN2 Q8 Q0 Q2 64 128 *)
  0x4ed869df;       (* arm_TRN2 Q31 Q14 Q24 64 128 *)
  0x4ed829cc;       (* arm_TRN1 Q12 Q14 Q24 64 128 *)
  0x6e7eb50f;       (* arm_SQRDMULH_VEC Q15 Q8 Q30 16 128 *)
  0x4ec22813;       (* arm_TRN1 Q19 Q0 Q2 64 128 *)
  0x4e6a9d03;       (* arm_MUL_VEC Q3 Q8 Q10 16 128 *)
  0x6e7eb7fe;       (* arm_SQRDMULH_VEC Q30 Q31 Q30 16 128 *)
  0x6f4741e3;       (* arm_MLS_VEC Q3 Q15 (Q7 :> LANE_H 0) 16 128 *)
  0x4e6a9fef;       (* arm_MUL_VEC Q15 Q31 Q10 16 128 *)
  0x6f4743cf;       (* arm_MLS_VEC Q15 Q30 (Q7 :> LANE_H 0) 16 128 *)
  0x4e638666;       (* arm_ADD_VEC Q6 Q19 Q3 16 128 *)
  0x6e638663;       (* arm_SUB_VEC Q3 Q19 Q3 16 128 *)
  0x6e72b4de;       (* arm_SQRDMULH_VEC Q30 Q6 Q18 16 128 *)
  0x4e779cd3;       (* arm_MUL_VEC Q19 Q6 Q23 16 128 *)
  0x4e6f859f;       (* arm_ADD_VEC Q31 Q12 Q15 16 128 *)
  0x6e6f858b;       (* arm_SUB_VEC Q11 Q12 Q15 16 128 *)
  0x6e76b477;       (* arm_SQRDMULH_VEC Q23 Q3 Q22 16 128 *)
  0x6f4743d3;       (* arm_MLS_VEC Q19 Q30 (Q7 :> LANE_H 0) 16 128 *)
  0x4e659c60;       (* arm_MUL_VEC Q0 Q3 Q5 16 128 *)
  0x6f4742e0;       (* arm_MLS_VEC Q0 Q23 (Q7 :> LANE_H 0) 16 128 *)
  0x6e7387fe;       (* arm_SUB_VEC Q30 Q31 Q19 16 128 *)
  0x4e7387ef;       (* arm_ADD_VEC Q15 Q31 Q19 16 128 *)
  0x4e9e69f3;       (* arm_TRN2 Q19 Q15 Q30 32 128 *)
  0x4e9e29ef;       (* arm_TRN1 Q15 Q15 Q30 32 128 *)
  0x6e608577;       (* arm_SUB_VEC Q23 Q11 Q0 16 128 *)
  0x4e60856c;       (* arm_ADD_VEC Q12 Q11 Q0 16 128 *)
  0x4e972983;       (* arm_TRN1 Q3 Q12 Q23 32 128 *)
  0x4e97699d;       (* arm_TRN2 Q29 Q12 Q23 32 128 *)
  0x4ec329ed;       (* arm_TRN1 Q13 Q15 Q3 64 128 *)
  0x4edd6a6c;       (* arm_TRN2 Q12 Q19 Q29 64 128 *)
  0x4edd2a77;       (* arm_TRN1 Q23 Q19 Q29 64 128 *)
  0x4ec369ef;       (* arm_TRN2 Q15 Q15 Q3 64 128 *)
  0x3c84040d;       (* arm_STR Q13 X0 (Postimmediate_Offset (word 64)) *)
  0x3c9f000c;       (* arm_STR Q12 X0 (Immediate_Offset (word 18446744073709551600)) *)
  0x3c9e000f;       (* arm_STR Q15 X0 (Immediate_Offset (word 18446744073709551584)) *)
  0x3c9d0017;       (* arm_STR Q23 X0 (Immediate_Offset (word 18446744073709551568)) *)
  0x6d4027e8;       (* arm_LDP D8 D9 SP (Immediate_Offset (word 0)) *)
  0x6d412fea;       (* arm_LDP D10 D11 SP (Immediate_Offset (word 16)) *)
  0x6d4237ec;       (* arm_LDP D12 D13 SP (Immediate_Offset (word 32)) *)
  0x6d433fee;       (* arm_LDP D14 D15 SP (Immediate_Offset (word 48)) *)
  0x910103ff;       (* arm_ADD SP SP (rvalue (word 64)) *)
  0xd65f03c0        (* arm_RET X30 *)
]
[192; 249; 123; 194; 19; 253; 51; 227; 216; 255; 118; 254; 81; 253; 150; 229;
 118; 2; 57; 24; 104; 250; 241; 200; 80; 3; 155; 32; 0; 0; 0; 0; 38; 4; 213;
 40; 40; 1; 98; 11; 142; 252; 22; 222; 0; 0; 0; 0; 126; 250; 201; 201; 59; 5;
 124; 51; 196; 5; 193; 56; 0; 0; 0; 0; 193; 0; 108; 7; 229; 254; 30; 245; 56;
 0; 39; 2; 0; 0; 0; 0; 29; 3; 165; 30; 191; 251; 33; 214; 53; 5; 65; 51; 0;
 0; 0; 0; 225; 253; 31; 235; 146; 5; 212; 54; 45; 251; 132; 208; 0; 0; 0; 0;
 187; 255; 89; 253; 23; 2; 146; 20; 65; 254; 208; 238; 0; 0; 0; 0; 57; 2;
 225; 21; 88; 252; 3; 220; 62; 254; 179; 238; 0; 0; 0; 0; 209; 249; 34; 195;
 181; 250; 230; 203; 53; 3; 145; 31; 0; 0; 0; 0; 33; 1; 33; 1; 75; 1; 75; 1;
 180; 255; 180; 255; 219; 249; 219; 249; 29; 11; 29; 11; 186; 12; 186; 12;
 20; 253; 20; 253; 133; 195; 133; 195; 17; 0; 17; 0; 71; 2; 71; 2; 101; 6;
 101; 6; 239; 251; 239; 251; 167; 0; 167; 0; 107; 22; 107; 22; 241; 62; 241;
 62; 249; 215; 249; 215; 200; 253; 200; 253; 88; 253; 88; 253; 211; 2; 211;
 2; 76; 4; 76; 4; 41; 234; 41; 234; 219; 229; 219; 229; 205; 27; 205; 27; 76;
 42; 76; 42; 173; 4; 173; 4; 255; 251; 255; 251; 228; 251; 228; 251; 6; 251;
 6; 251; 6; 46; 6; 46; 151; 216; 151; 216; 141; 215; 141; 215; 4; 207; 4;
 207; 129; 5; 129; 5; 208; 255; 208; 255; 244; 2; 244; 2; 198; 254; 198; 254;
 45; 54; 45; 54; 40; 254; 40; 254; 17; 29; 17; 29; 237; 243; 237; 243; 101;
 253; 101; 253; 233; 0; 233; 0; 107; 251; 107; 251; 233; 254; 233; 254; 91;
 230; 91; 230; 245; 8; 245; 8; 230; 210; 230; 210; 70; 245; 70; 245; 138; 2;
 138; 2; 184; 250; 184; 250; 208; 252; 208; 252; 120; 2; 120; 2; 254; 24;
 254; 24; 4; 204; 4; 204; 160; 224; 160; 224; 77; 24; 77; 24; 166; 249; 166;
 249; 228; 253; 228; 253; 54; 250; 54; 250; 181; 5; 181; 5; 123; 193; 123;
 193; 61; 235; 61; 235; 4; 199; 4; 199; 45; 56; 45; 56; 115; 6; 115; 6; 252;
 249; 252; 249; 184; 3; 184; 3; 126; 253; 126; 253; 123; 63; 123; 63; 201;
 196; 201; 196; 155; 36; 155; 36; 81; 231; 81; 231; 48; 254; 48; 254; 33; 0;
 33; 0; 40; 5; 40; 5; 122; 250; 122; 250; 41; 238; 41; 238; 69; 1; 69; 1;
 193; 50; 193; 50; 162; 201; 162; 201; 171; 3; 171; 3; 132; 252; 132; 252;
 221; 2; 221; 2; 12; 1; 12; 1; 27; 36; 27; 36; 180; 221; 180; 221; 47; 28;
 47; 28; 78; 10; 78; 10; 3; 252; 3; 252; 83; 252; 83; 252; 32; 252; 32; 252;
 129; 2; 129; 2; 190; 216; 190; 216; 210; 219; 210; 219; 220; 217; 220; 217;
 165; 24; 165; 24; 14; 252; 14; 252; 155; 5; 155; 5; 39; 3; 39; 3; 196; 1;
 196; 1; 42; 217; 42; 217; 45; 55; 45; 55; 7; 31; 7; 31; 97; 17; 97; 17; 48;
 6; 48; 6; 244; 250; 244; 250; 119; 1; 119; 1; 41; 251; 41; 251; 232; 60;
 232; 60; 83; 206; 83; 206; 107; 14; 107; 14; 92; 208; 92; 208; 249; 251;
 249; 251; 147; 255; 147; 255; 244; 252; 244; 252; 109; 6; 109; 6; 92; 216;
 92; 216; 207; 251; 207; 251; 2; 226; 2; 226; 64; 63; 64; 63; 158; 5; 158; 5;
 51; 254; 51; 254; 254; 5; 254; 5; 97; 252; 97; 252; 75; 55; 75; 55; 70; 238;
 70; 238; 251; 58; 251; 58; 91; 220; 91; 220; 39; 4; 39; 4; 212; 253; 212;
 253; 50; 251; 50; 251; 161; 252; 161; 252; 223; 40; 223; 40; 159; 234; 159;
 234; 181; 208; 181; 208; 209; 222; 209; 222; 63; 1; 63; 1; 245; 2; 245; 2;
 49; 2; 49; 2; 33; 253; 33; 253; 68; 12; 68; 12; 27; 29; 27; 29; 146; 21;
 146; 21; 189; 227; 189; 227; 86; 253; 86; 253; 56; 253; 56; 253; 201; 5;
 201; 5; 136; 2; 136; 2; 199; 229; 199; 229; 160; 228; 160; 228; 242; 56;
 242; 56; 234; 24; 234; 24; 243; 253; 243; 253; 147; 1; 147; 1; 119; 4; 119;
 4; 214; 253; 214; 253; 208; 235; 208; 235; 127; 15; 127; 15; 243; 43; 243;
 43; 179; 234; 179; 234; 68; 4; 68; 4; 2; 4; 2; 4; 101; 251; 101; 251; 118;
 3; 118; 3; 253; 41; 253; 41; 115; 39; 115; 39; 171; 210; 171; 210; 17; 34;
 17; 34; 169; 252; 169; 252; 37; 255; 37; 255; 203; 4; 203; 4; 142; 3; 142;
 3; 32; 223; 32; 223; 148; 247; 148; 247; 46; 47; 46; 47; 253; 34; 253; 34;
 185; 249; 185; 249; 81; 250; 81; 250; 61; 251; 61; 251; 117; 3; 117; 3; 54;
 194; 54; 194; 14; 200; 14; 200; 33; 209; 33; 209; 7; 34; 7; 34; 188; 4; 188;
 4; 5; 4; 5; 4; 118; 254; 118; 254; 105; 251; 105; 251; 154; 46; 154; 46;
 145; 39; 145; 39; 218; 240; 218; 240; 210; 210; 210; 210];;

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
 (`bytes_loaded s (word (pc + 0x518)) mlkem_ntt_data <=>
   read (memory :> bytes(word (pc + 0x518),928)) s =
   num_of_bytelist mlkem_ntt_data`,
  REWRITE_TAC[bytes_loaded; READ_BYTELIST_EQ_BYTES;
    CONV_RULE (RAND_CONV LENGTH_CONV)
     (AP_TERM `LENGTH:byte list->num` mlkem_ntt_data)]);;

let MLKEM_NTT_CORRECT = prove
 (`!a x pc.
      nonoverlapping (word pc,0x8b8) (a,512)
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc)
                  (APPEND mlkem_ntt_mc mlkem_ntt_data) /\
                read PC s = word (pc + 0x14) /\
                C_ARGUMENTS [a] s /\
                !i. i < 256
                    ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                        x i)
           (\s. read PC s = word(pc + 0x500) /\
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
   `word(pc + 0x5b8):int64 = word_add (word(pc + 0x518)) (word 160)`) THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM BYTES_LOADED_DATA]) THEN
  ABBREV_TAC `wpc:int64 = word(pc + 0x518)` THEN
  SUBST1_TAC(WORD_RULE `wpc:int64 = word(val wpc + 0)`) THEN
  REWRITE_TAC[mlkem_ntt_data] THEN CONV_TAC(LAND_CONV DATA64_CONV) THEN
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

  MAP_EVERY (fun n -> ARM_STEPS_TAC MLKEM_NTT_EXEC [n] THEN SIMD_SIMPLIFY_TAC)
            (1--909) THEN
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
  ASM_REWRITE_TAC[I_THM; WORD_ADD_0] THEN DISCARD_STATE_TAC "s909" THEN
  REPEAT(W(fun (asl,w) ->
     if length(conjuncts w) > 3 then CONJ_TAC else NO_TAC)) THEN

  (*** Get congruences and bounds for the result digits and finish ***)

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
          [(word pc,0x8b8); (a,512)] /\
      nonoverlapping (word pc,0x8b8) (a,512)
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
