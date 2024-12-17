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
  0x100027e1;       (* arm_ADR X1 (word 1276) *)
  0x91000021;       (* arm_ADD X1 X1 (rvalue (word 0)) *)
  0x10002ca2;       (* arm_ADR X2 (word 1428) *)
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
  0x3dc04010;       (* arm_LDR Q16 X0 (Immediate_Offset (word 256)) *)
  0x3dc07004;       (* arm_LDR Q4 X0 (Immediate_Offset (word 448)) *)
  0x3dc0600a;       (* arm_LDR Q10 X0 (Immediate_Offset (word 384)) *)
  0x3dc01015;       (* arm_LDR Q21 X0 (Immediate_Offset (word 64)) *)
  0x3dc0201e;       (* arm_LDR Q30 X0 (Immediate_Offset (word 128)) *)
  0x3dc03009;       (* arm_LDR Q9 X0 (Immediate_Offset (word 192)) *)
  0x3dc0500c;       (* arm_LDR Q12 X0 (Immediate_Offset (word 320)) *)
  0x4f50d21a;       (* arm_SQRDMULH_VEC Q26 Q16 (Q0 :> LANE_H 1) 16 128 *)
  0x4f408206;       (* arm_MUL_VEC Q6 Q16 (Q0 :> LANE_H 0) 16 128 *)
  0x3dc00010;       (* arm_LDR Q16 X0 (Immediate_Offset (word 0)) *)
  0x4f50d18e;       (* arm_SQRDMULH_VEC Q14 Q12 (Q0 :> LANE_H 1) 16 128 *)
  0x6f474346;       (* arm_MLS_VEC Q6 Q26 (Q7 :> LANE_H 0) 16 128 *)
  0x4f408188;       (* arm_MUL_VEC Q8 Q12 (Q0 :> LANE_H 0) 16 128 *)
  0xd1000484;       (* arm_SUB X4 X4 (rvalue (word 1)) *)
  0x4e668603;       (* arm_ADD_VEC Q3 Q16 Q6 16 128 *)
  0x4f50d096;       (* arm_SQRDMULH_VEC Q22 Q4 (Q0 :> LANE_H 1) 16 128 *)
  0x3dc04402;       (* arm_LDR Q2 X0 (Immediate_Offset (word 272)) *)
  0x6e66860c;       (* arm_SUB_VEC Q12 Q16 Q6 16 128 *)
  0x4f408090;       (* arm_MUL_VEC Q16 Q4 (Q0 :> LANE_H 0) 16 128 *)
  0x3dc07404;       (* arm_LDR Q4 X0 (Immediate_Offset (word 464)) *)
  0x4f50d152;       (* arm_SQRDMULH_VEC Q18 Q10 (Q0 :> LANE_H 1) 16 128 *)
  0x6f4742d0;       (* arm_MLS_VEC Q16 Q22 (Q7 :> LANE_H 0) 16 128 *)
  0x4f40814b;       (* arm_MUL_VEC Q11 Q10 (Q0 :> LANE_H 0) 16 128 *)
  0x3dc0640a;       (* arm_LDR Q10 X0 (Immediate_Offset (word 400)) *)
  0x4f50d058;       (* arm_SQRDMULH_VEC Q24 Q2 (Q0 :> LANE_H 1) 16 128 *)
  0x6f47424b;       (* arm_MLS_VEC Q11 Q18 (Q7 :> LANE_H 0) 16 128 *)
  0x6e708533;       (* arm_SUB_VEC Q19 Q9 Q16 16 128 *)
  0x4e70852d;       (* arm_ADD_VEC Q13 Q9 Q16 16 128 *)
  0x6f4741c8;       (* arm_MLS_VEC Q8 Q14 (Q7 :> LANE_H 0) 16 128 *)
  0x4f6081ba;       (* arm_MUL_VEC Q26 Q13 (Q0 :> LANE_H 2) 16 128 *)
  0x4f70d1a6;       (* arm_SQRDMULH_VEC Q6 Q13 (Q0 :> LANE_H 3) 16 128 *)
  0x4e6b87db;       (* arm_ADD_VEC Q27 Q30 Q11 16 128 *)
  0x4f608377;       (* arm_MUL_VEC Q23 Q27 (Q0 :> LANE_H 2) 16 128 *)
  0x6e6b87cd;       (* arm_SUB_VEC Q13 Q30 Q11 16 128 *)
  0x4f50da6f;       (* arm_SQRDMULH_VEC Q15 Q19 (Q0 :> LANE_H 5) 16 128 *)
  0x4f50d9bd;       (* arm_SQRDMULH_VEC Q29 Q13 (Q0 :> LANE_H 5) 16 128 *)
  0x4f70d376;       (* arm_SQRDMULH_VEC Q22 Q27 (Q0 :> LANE_H 3) 16 128 *)
  0x4f4089a5;       (* arm_MUL_VEC Q5 Q13 (Q0 :> LANE_H 4) 16 128 *)
  0x6f4740da;       (* arm_MLS_VEC Q26 Q6 (Q7 :> LANE_H 0) 16 128 *)
  0x6f4742d7;       (* arm_MLS_VEC Q23 Q22 (Q7 :> LANE_H 0) 16 128 *)
  0x4e6886b6;       (* arm_ADD_VEC Q22 Q21 Q8 16 128 *)
  0x6e6886ae;       (* arm_SUB_VEC Q14 Q21 Q8 16 128 *)
  0x3dc01415;       (* arm_LDR Q21 X0 (Immediate_Offset (word 80)) *)
  0x6f4743a5;       (* arm_MLS_VEC Q5 Q29 (Q7 :> LANE_H 0) 16 128 *)
  0x3dc0241e;       (* arm_LDR Q30 X0 (Immediate_Offset (word 144)) *)
  0x3dc03409;       (* arm_LDR Q9 X0 (Immediate_Offset (word 208)) *)
  0x4f408a7f;       (* arm_MUL_VEC Q31 Q19 (Q0 :> LANE_H 4) 16 128 *)
  0x4e77847b;       (* arm_ADD_VEC Q27 Q3 Q23 16 128 *)
  0x6f4741ff;       (* arm_MLS_VEC Q31 Q15 (Q7 :> LANE_H 0) 16 128 *)
  0x6e7a86dc;       (* arm_SUB_VEC Q28 Q22 Q26 16 128 *)
  0x6e658592;       (* arm_SUB_VEC Q18 Q12 Q5 16 128 *)
  0x4e7a86cf;       (* arm_ADD_VEC Q15 Q22 Q26 16 128 *)
  0x4f51d38b;       (* arm_SQRDMULH_VEC Q11 Q28 (Q1 :> LANE_H 1) 16 128 *)
  0x4e658588;       (* arm_ADD_VEC Q8 Q12 Q5 16 128 *)
  0x4f70d9ec;       (* arm_SQRDMULH_VEC Q12 Q15 (Q0 :> LANE_H 7) 16 128 *)
  0x4f6089f1;       (* arm_MUL_VEC Q17 Q15 (Q0 :> LANE_H 6) 16 128 *)
  0x6e7f85d6;       (* arm_SUB_VEC Q22 Q14 Q31 16 128 *)
  0x4e7f85ce;       (* arm_ADD_VEC Q14 Q14 Q31 16 128 *)
  0x6e77846d;       (* arm_SUB_VEC Q13 Q3 Q23 16 128 *)
  0x4f51dad4;       (* arm_SQRDMULH_VEC Q20 Q22 (Q1 :> LANE_H 5) 16 128 *)
  0x6f474191;       (* arm_MLS_VEC Q17 Q12 (Q7 :> LANE_H 0) 16 128 *)
  0x4f418ad3;       (* arm_MUL_VEC Q19 Q22 (Q1 :> LANE_H 4) 16 128 *)
  0x4f71d1dd;       (* arm_SQRDMULH_VEC Q29 Q14 (Q1 :> LANE_H 3) 16 128 *)
  0x6e718777;       (* arm_SUB_VEC Q23 Q27 Q17 16 128 *)
  0x4f418396;       (* arm_MUL_VEC Q22 Q28 (Q1 :> LANE_H 0) 16 128 *)
  0x6f474176;       (* arm_MLS_VEC Q22 Q11 (Q7 :> LANE_H 0) 16 128 *)
  0x4f6181ce;       (* arm_MUL_VEC Q14 Q14 (Q1 :> LANE_H 2) 16 128 *)
  0x6f4743ae;       (* arm_MLS_VEC Q14 Q29 (Q7 :> LANE_H 0) 16 128 *)
  0x4e71877d;       (* arm_ADD_VEC Q29 Q27 Q17 16 128 *)
  0x6e7685bf;       (* arm_SUB_VEC Q31 Q13 Q22 16 128 *)
  0x3dc0541b;       (* arm_LDR Q27 X0 (Immediate_Offset (word 336)) *)
  0x6f474293;       (* arm_MLS_VEC Q19 Q20 (Q7 :> LANE_H 0) 16 128 *)
  0x3dc00410;       (* arm_LDR Q16 X0 (Immediate_Offset (word 16)) *)
  0x4e7685a3;       (* arm_ADD_VEC Q3 Q13 Q22 16 128 *)
  0x3c81041d;       (* arm_STR Q29 X0 (Postimmediate_Offset (word 16)) *)
  0x3d800c17;       (* arm_STR Q23 X0 (Immediate_Offset (word 48)) *)
  0x4f408046;       (* arm_MUL_VEC Q6 Q2 (Q0 :> LANE_H 0) 16 128 *)
  0x3d801c03;       (* arm_STR Q3 X0 (Immediate_Offset (word 112)) *)
  0x6e6e8516;       (* arm_SUB_VEC Q22 Q8 Q14 16 128 *)
  0x6f474306;       (* arm_MLS_VEC Q6 Q24 (Q7 :> LANE_H 0) 16 128 *)
  0x4e6e850b;       (* arm_ADD_VEC Q11 Q8 Q14 16 128 *)
  0x3d802c1f;       (* arm_STR Q31 X0 (Immediate_Offset (word 176)) *)
  0x4e738651;       (* arm_ADD_VEC Q17 Q18 Q19 16 128 *)
  0x3d803c0b;       (* arm_STR Q11 X0 (Immediate_Offset (word 240)) *)
  0x4f50d36e;       (* arm_SQRDMULH_VEC Q14 Q27 (Q0 :> LANE_H 1) 16 128 *)
  0x6e738643;       (* arm_SUB_VEC Q3 Q18 Q19 16 128 *)
  0x3d804c16;       (* arm_STR Q22 X0 (Immediate_Offset (word 304)) *)
  0x4f408368;       (* arm_MUL_VEC Q8 Q27 (Q0 :> LANE_H 0) 16 128 *)
  0x3d805c11;       (* arm_STR Q17 X0 (Immediate_Offset (word 368)) *)
  0x3d806c03;       (* arm_STR Q3 X0 (Immediate_Offset (word 432)) *)
  0xd1000484;       (* arm_SUB X4 X4 (rvalue (word 1)) *)
  0xb5fff664;       (* arm_CBNZ X4 (word 2096844) *)
  0x6e668605;       (* arm_SUB_VEC Q5 Q16 Q6 16 128 *)
  0x4f50d093;       (* arm_SQRDMULH_VEC Q19 Q4 (Q0 :> LANE_H 1) 16 128 *)
  0x4f50d152;       (* arm_SQRDMULH_VEC Q18 Q10 (Q0 :> LANE_H 1) 16 128 *)
  0x4f408096;       (* arm_MUL_VEC Q22 Q4 (Q0 :> LANE_H 0) 16 128 *)
  0x6f474276;       (* arm_MLS_VEC Q22 Q19 (Q7 :> LANE_H 0) 16 128 *)
  0x4f408158;       (* arm_MUL_VEC Q24 Q10 (Q0 :> LANE_H 0) 16 128 *)
  0x4e66860a;       (* arm_ADD_VEC Q10 Q16 Q6 16 128 *)
  0x6f474258;       (* arm_MLS_VEC Q24 Q18 (Q7 :> LANE_H 0) 16 128 *)
  0x4e768533;       (* arm_ADD_VEC Q19 Q9 Q22 16 128 *)
  0x6e76853a;       (* arm_SUB_VEC Q26 Q9 Q22 16 128 *)
  0x6f4741c8;       (* arm_MLS_VEC Q8 Q14 (Q7 :> LANE_H 0) 16 128 *)
  0x4f50db4c;       (* arm_SQRDMULH_VEC Q12 Q26 (Q0 :> LANE_H 5) 16 128 *)
  0x4e7887d4;       (* arm_ADD_VEC Q20 Q30 Q24 16 128 *)
  0x6e7887c2;       (* arm_SUB_VEC Q2 Q30 Q24 16 128 *)
  0x4f408b56;       (* arm_MUL_VEC Q22 Q26 (Q0 :> LANE_H 4) 16 128 *)
  0x4e6886b9;       (* arm_ADD_VEC Q25 Q21 Q8 16 128 *)
  0x6e6886bc;       (* arm_SUB_VEC Q28 Q21 Q8 16 128 *)
  0x4f70d290;       (* arm_SQRDMULH_VEC Q16 Q20 (Q0 :> LANE_H 3) 16 128 *)
  0x6f474196;       (* arm_MLS_VEC Q22 Q12 (Q7 :> LANE_H 0) 16 128 *)
  0x4f60828d;       (* arm_MUL_VEC Q13 Q20 (Q0 :> LANE_H 2) 16 128 *)
  0x6f47420d;       (* arm_MLS_VEC Q13 Q16 (Q7 :> LANE_H 0) 16 128 *)
  0x6e768790;       (* arm_SUB_VEC Q16 Q28 Q22 16 128 *)
  0x4e768783;       (* arm_ADD_VEC Q3 Q28 Q22 16 128 *)
  0x4f608276;       (* arm_MUL_VEC Q22 Q19 (Q0 :> LANE_H 2) 16 128 *)
  0x4f70d27d;       (* arm_SQRDMULH_VEC Q29 Q19 (Q0 :> LANE_H 3) 16 128 *)
  0x4e6d8553;       (* arm_ADD_VEC Q19 Q10 Q13 16 128 *)
  0x4f50d846;       (* arm_SQRDMULH_VEC Q6 Q2 (Q0 :> LANE_H 5) 16 128 *)
  0x4f418a1c;       (* arm_MUL_VEC Q28 Q16 (Q1 :> LANE_H 4) 16 128 *)
  0x6f4743b6;       (* arm_MLS_VEC Q22 Q29 (Q7 :> LANE_H 0) 16 128 *)
  0x4f51da18;       (* arm_SQRDMULH_VEC Q24 Q16 (Q1 :> LANE_H 5) 16 128 *)
  0x4f408857;       (* arm_MUL_VEC Q23 Q2 (Q0 :> LANE_H 4) 16 128 *)
  0x6e768730;       (* arm_SUB_VEC Q16 Q25 Q22 16 128 *)
  0x4e76873b;       (* arm_ADD_VEC Q27 Q25 Q22 16 128 *)
  0x6f4740d7;       (* arm_MLS_VEC Q23 Q6 (Q7 :> LANE_H 0) 16 128 *)
  0x6e6d8556;       (* arm_SUB_VEC Q22 Q10 Q13 16 128 *)
  0x6f47431c;       (* arm_MLS_VEC Q28 Q24 (Q7 :> LANE_H 0) 16 128 *)
  0x4f71d072;       (* arm_SQRDMULH_VEC Q18 Q3 (Q1 :> LANE_H 3) 16 128 *)
  0x6e7784a4;       (* arm_SUB_VEC Q4 Q5 Q23 16 128 *)
  0x4e7784a2;       (* arm_ADD_VEC Q2 Q5 Q23 16 128 *)
  0x4f418215;       (* arm_MUL_VEC Q21 Q16 (Q1 :> LANE_H 0) 16 128 *)
  0x6e7c848c;       (* arm_SUB_VEC Q12 Q4 Q28 16 128 *)
  0x4f61807e;       (* arm_MUL_VEC Q30 Q3 (Q1 :> LANE_H 2) 16 128 *)
  0x3d80700c;       (* arm_STR Q12 X0 (Immediate_Offset (word 448)) *)
  0x4f51d20c;       (* arm_SQRDMULH_VEC Q12 Q16 (Q1 :> LANE_H 1) 16 128 *)
  0x4e7c849a;       (* arm_ADD_VEC Q26 Q4 Q28 16 128 *)
  0x6f47425e;       (* arm_MLS_VEC Q30 Q18 (Q7 :> LANE_H 0) 16 128 *)
  0x4f70db66;       (* arm_SQRDMULH_VEC Q6 Q27 (Q0 :> LANE_H 7) 16 128 *)
  0x6f474195;       (* arm_MLS_VEC Q21 Q12 (Q7 :> LANE_H 0) 16 128 *)
  0x4f608b7f;       (* arm_MUL_VEC Q31 Q27 (Q0 :> LANE_H 6) 16 128 *)
  0x6f4740df;       (* arm_MLS_VEC Q31 Q6 (Q7 :> LANE_H 0) 16 128 *)
  0x4e7e8446;       (* arm_ADD_VEC Q6 Q2 Q30 16 128 *)
  0x4e7586cb;       (* arm_ADD_VEC Q11 Q22 Q21 16 128 *)
  0x3d804006;       (* arm_STR Q6 X0 (Immediate_Offset (word 256)) *)
  0x6e7e8446;       (* arm_SUB_VEC Q6 Q2 Q30 16 128 *)
  0x6e7586d6;       (* arm_SUB_VEC Q22 Q22 Q21 16 128 *)
  0x3d80200b;       (* arm_STR Q11 X0 (Immediate_Offset (word 128)) *)
  0x3d805006;       (* arm_STR Q6 X0 (Immediate_Offset (word 320)) *)
  0x6e7f8668;       (* arm_SUB_VEC Q8 Q19 Q31 16 128 *)
  0x4e7f8670;       (* arm_ADD_VEC Q16 Q19 Q31 16 128 *)
  0x3d80601a;       (* arm_STR Q26 X0 (Immediate_Offset (word 384)) *)
  0x3d803016;       (* arm_STR Q22 X0 (Immediate_Offset (word 192)) *)
  0x3d801008;       (* arm_STR Q8 X0 (Immediate_Offset (word 64)) *)
  0x3c810410;       (* arm_STR Q16 X0 (Postimmediate_Offset (word 16)) *)
  0xaa0303e0;       (* arm_MOV X0 X3 *)
  0xd2800104;       (* arm_MOV X4 (rvalue (word 8)) *)
  0x3dc00c04;       (* arm_LDR Q4 X0 (Immediate_Offset (word 48)) *)
  0x3cc10420;       (* arm_LDR Q0 X1 (Postimmediate_Offset (word 16)) *)
  0x3dc0080a;       (* arm_LDR Q10 X0 (Immediate_Offset (word 32)) *)
  0x3dc00013;       (* arm_LDR Q19 X0 (Immediate_Offset (word 0)) *)
  0x3dc0044e;       (* arm_LDR Q14 X2 (Immediate_Offset (word 16)) *)
  0x3dc0084b;       (* arm_LDR Q11 X2 (Immediate_Offset (word 32)) *)
  0x3dc00416;       (* arm_LDR Q22 X0 (Immediate_Offset (word 16)) *)
  0x4f50d090;       (* arm_SQRDMULH_VEC Q16 Q4 (Q0 :> LANE_H 1) 16 128 *)
  0x4f408099;       (* arm_MUL_VEC Q25 Q4 (Q0 :> LANE_H 0) 16 128 *)
  0x4f50d141;       (* arm_SQRDMULH_VEC Q1 Q10 (Q0 :> LANE_H 1) 16 128 *)
  0x6f474219;       (* arm_MLS_VEC Q25 Q16 (Q7 :> LANE_H 0) 16 128 *)
  0x4f40815a;       (* arm_MUL_VEC Q26 Q10 (Q0 :> LANE_H 0) 16 128 *)
  0x6f47403a;       (* arm_MLS_VEC Q26 Q1 (Q7 :> LANE_H 0) 16 128 *)
  0x4e7986db;       (* arm_ADD_VEC Q27 Q22 Q25 16 128 *)
  0x6e7986c3;       (* arm_SUB_VEC Q3 Q22 Q25 16 128 *)
  0x4f70d366;       (* arm_SQRDMULH_VEC Q6 Q27 (Q0 :> LANE_H 3) 16 128 *)
  0x4e7a8671;       (* arm_ADD_VEC Q17 Q19 Q26 16 128 *)
  0x4f60837b;       (* arm_MUL_VEC Q27 Q27 (Q0 :> LANE_H 2) 16 128 *)
  0x4f50d878;       (* arm_SQRDMULH_VEC Q24 Q3 (Q0 :> LANE_H 5) 16 128 *)
  0x6f4740db;       (* arm_MLS_VEC Q27 Q6 (Q7 :> LANE_H 0) 16 128 *)
  0x4f408866;       (* arm_MUL_VEC Q6 Q3 (Q0 :> LANE_H 4) 16 128 *)
  0x6e7a8660;       (* arm_SUB_VEC Q0 Q19 Q26 16 128 *)
  0x6f474306;       (* arm_MLS_VEC Q6 Q24 (Q7 :> LANE_H 0) 16 128 *)
  0x4e7b863e;       (* arm_ADD_VEC Q30 Q17 Q27 16 128 *)
  0x6e7b8630;       (* arm_SUB_VEC Q16 Q17 Q27 16 128 *)
  0x4e906bd7;       (* arm_TRN2 Q23 Q30 Q16 32 128 *)
  0x4e902bd2;       (* arm_TRN1 Q18 Q30 Q16 32 128 *)
  0x4e668416;       (* arm_ADD_VEC Q22 Q0 Q6 16 128 *)
  0x6e668413;       (* arm_SUB_VEC Q19 Q0 Q6 16 128 *)
  0x3cc6045e;       (* arm_LDR Q30 X2 (Postimmediate_Offset (word 96)) *)
  0x4e936acc;       (* arm_TRN2 Q12 Q22 Q19 32 128 *)
  0x4e932ad9;       (* arm_TRN1 Q25 Q22 Q19 32 128 *)
  0x4ecc6af0;       (* arm_TRN2 Q16 Q23 Q12 64 128 *)
  0x4ecc2aef;       (* arm_TRN1 Q15 Q23 Q12 64 128 *)
  0x4ed96a46;       (* arm_TRN2 Q6 Q18 Q25 64 128 *)
  0x4e7e9e14;       (* arm_MUL_VEC Q20 Q16 Q30 16 128 *)
  0x6e6eb4d6;       (* arm_SQRDMULH_VEC Q22 Q6 Q14 16 128 *)
  0x4e7e9cd7;       (* arm_MUL_VEC Q23 Q6 Q30 16 128 *)
  0x6e6eb611;       (* arm_SQRDMULH_VEC Q17 Q16 Q14 16 128 *)
  0xd1000484;       (* arm_SUB X4 X4 (rvalue (word 1)) *)
  0x3cdd004e;       (* arm_LDR Q14 X2 (Immediate_Offset (word 18446744073709551568)) *)
  0x3cc10422;       (* arm_LDR Q2 X1 (Postimmediate_Offset (word 16)) *)
  0x6f4742d7;       (* arm_MLS_VEC Q23 Q22 (Q7 :> LANE_H 0) 16 128 *)
  0x3dc01c03;       (* arm_LDR Q3 X0 (Immediate_Offset (word 112)) *)
  0x3cde005f;       (* arm_LDR Q31 X2 (Immediate_Offset (word 18446744073709551584)) *)
  0x3dc01013;       (* arm_LDR Q19 X0 (Immediate_Offset (word 64)) *)
  0x6f474234;       (* arm_MLS_VEC Q20 Q17 (Q7 :> LANE_H 0) 16 128 *)
  0x3cc6045e;       (* arm_LDR Q30 X2 (Postimmediate_Offset (word 96)) *)
  0x3cd9004a;       (* arm_LDR Q10 X2 (Immediate_Offset (word 18446744073709551504)) *)
  0x3dc01809;       (* arm_LDR Q9 X0 (Immediate_Offset (word 96)) *)
  0x4f52d060;       (* arm_SQRDMULH_VEC Q0 Q3 (Q2 :> LANE_H 1) 16 128 *)
  0x3dc0141b;       (* arm_LDR Q27 X0 (Immediate_Offset (word 80)) *)
  0x4f428075;       (* arm_MUL_VEC Q21 Q3 (Q2 :> LANE_H 0) 16 128 *)
  0x6e7485e4;       (* arm_SUB_VEC Q4 Q15 Q20 16 128 *)
  0x4f52d13d;       (* arm_SQRDMULH_VEC Q29 Q9 (Q2 :> LANE_H 1) 16 128 *)
  0x4ed92a50;       (* arm_TRN1 Q16 Q18 Q25 64 128 *)
  0x4e7485f6;       (* arm_ADD_VEC Q22 Q15 Q20 16 128 *)
  0x6f474015;       (* arm_MLS_VEC Q21 Q0 (Q7 :> LANE_H 0) 16 128 *)
  0x4e778600;       (* arm_ADD_VEC Q0 Q16 Q23 16 128 *)
  0x6e778601;       (* arm_SUB_VEC Q1 Q16 Q23 16 128 *)
  0x4f428138;       (* arm_MUL_VEC Q24 Q9 (Q2 :> LANE_H 0) 16 128 *)
  0x6f4743b8;       (* arm_MLS_VEC Q24 Q29 (Q7 :> LANE_H 0) 16 128 *)
  0x6e75877a;       (* arm_SUB_VEC Q26 Q27 Q21 16 128 *)
  0x6e6ab491;       (* arm_SQRDMULH_VEC Q17 Q4 Q10 16 128 *)
  0x4e758766;       (* arm_ADD_VEC Q6 Q27 Q21 16 128 *)
  0x4f72d0c9;       (* arm_SQRDMULH_VEC Q9 Q6 (Q2 :> LANE_H 3) 16 128 *)
  0x4e788665;       (* arm_ADD_VEC Q5 Q19 Q24 16 128 *)
  0x4f6280c8;       (* arm_MUL_VEC Q8 Q6 (Q2 :> LANE_H 2) 16 128 *)
  0x6e78867b;       (* arm_SUB_VEC Q27 Q19 Q24 16 128 *)
  0x3cdb0058;       (* arm_LDR Q24 X2 (Immediate_Offset (word 18446744073709551536)) *)
  0x4f52db4c;       (* arm_SQRDMULH_VEC Q12 Q26 (Q2 :> LANE_H 5) 16 128 *)
  0x6f474128;       (* arm_MLS_VEC Q8 Q9 (Q7 :> LANE_H 0) 16 128 *)
  0x4f428b4d;       (* arm_MUL_VEC Q13 Q26 (Q2 :> LANE_H 4) 16 128 *)
  0x6f47418d;       (* arm_MLS_VEC Q13 Q12 (Q7 :> LANE_H 0) 16 128 *)
  0x4e6884ac;       (* arm_ADD_VEC Q12 Q5 Q8 16 128 *)
  0x4e6b9ed3;       (* arm_MUL_VEC Q19 Q22 Q11 16 128 *)
  0x6e6884b0;       (* arm_SUB_VEC Q16 Q5 Q8 16 128 *)
  0x4e906982;       (* arm_TRN2 Q2 Q12 Q16 32 128 *)
  0x6e6eb6da;       (* arm_SQRDMULH_VEC Q26 Q22 Q14 16 128 *)
  0x6e6d876b;       (* arm_SUB_VEC Q11 Q27 Q13 16 128 *)
  0x4e7f9c8f;       (* arm_MUL_VEC Q15 Q4 Q31 16 128 *)
  0x4e6d8766;       (* arm_ADD_VEC Q6 Q27 Q13 16 128 *)
  0x4e902992;       (* arm_TRN1 Q18 Q12 Q16 32 128 *)
  0x4e8b28d9;       (* arm_TRN1 Q25 Q6 Q11 32 128 *)
  0x6f47422f;       (* arm_MLS_VEC Q15 Q17 (Q7 :> LANE_H 0) 16 128 *)
  0x4e8b68ca;       (* arm_TRN2 Q10 Q6 Q11 32 128 *)
  0x3cdc004b;       (* arm_LDR Q11 X2 (Immediate_Offset (word 18446744073709551552)) *)
  0x4ed96a44;       (* arm_TRN2 Q4 Q18 Q25 64 128 *)
  0x6f474353;       (* arm_MLS_VEC Q19 Q26 (Q7 :> LANE_H 0) 16 128 *)
  0x6e78b496;       (* arm_SQRDMULH_VEC Q22 Q4 Q24 16 128 *)
  0x4eca6850;       (* arm_TRN2 Q16 Q2 Q10 64 128 *)
  0x4e6f843c;       (* arm_ADD_VEC Q28 Q1 Q15 16 128 *)
  0x6e6f843d;       (* arm_SUB_VEC Q29 Q1 Q15 16 128 *)
  0x6e78b611;       (* arm_SQRDMULH_VEC Q17 Q16 Q24 16 128 *)
  0x4e73841a;       (* arm_ADD_VEC Q26 Q0 Q19 16 128 *)
  0x4e7e9e14;       (* arm_MUL_VEC Q20 Q16 Q30 16 128 *)
  0x6e73841b;       (* arm_SUB_VEC Q27 Q0 Q19 16 128 *)
  0x4eca284f;       (* arm_TRN1 Q15 Q2 Q10 64 128 *)
  0x4e7e9c97;       (* arm_MUL_VEC Q23 Q4 Q30 16 128 *)
  0x4e9b3b4e;       (* arm_ZIP1 Q14 Q26 Q27 32 128 *)
  0x4e9b7b5b;       (* arm_ZIP2 Q27 Q26 Q27 32 128 *)
  0x4e9d3b9a;       (* arm_ZIP1 Q26 Q28 Q29 32 128 *)
  0x4e9d7b9d;       (* arm_ZIP2 Q29 Q28 Q29 32 128 *)
  0x4eda39dc;       (* arm_ZIP1 Q28 Q14 Q26 64 128 *)
  0x4eda79da;       (* arm_ZIP2 Q26 Q14 Q26 64 128 *)
  0xad00681c;       (* arm_STP Q28 Q26 X0 (Immediate_Offset (word 0)) *)
  0x4edd3b7c;       (* arm_ZIP1 Q28 Q27 Q29 64 128 *)
  0x4edd7b7a;       (* arm_ZIP2 Q26 Q27 Q29 64 128 *)
  0xad01681c;       (* arm_STP Q28 Q26 X0 (Immediate_Offset (word 32)) *)
  0x91010000;       (* arm_ADD X0 X0 (rvalue (word 64)) *)
  0xd1000484;       (* arm_SUB X4 X4 (rvalue (word 1)) *)
  0xb5fff724;       (* arm_CBNZ X4 (word 2096868) *)
  0x3cdd005c;       (* arm_LDR Q28 X2 (Immediate_Offset (word 18446744073709551568)) *)
  0x6f474234;       (* arm_MLS_VEC Q20 Q17 (Q7 :> LANE_H 0) 16 128 *)
  0x3cdf0050;       (* arm_LDR Q16 X2 (Immediate_Offset (word 18446744073709551600)) *)
  0x4ed92a5a;       (* arm_TRN1 Q26 Q18 Q25 64 128 *)
  0x6f4742d7;       (* arm_MLS_VEC Q23 Q22 (Q7 :> LANE_H 0) 16 128 *)
  0x3cde0051;       (* arm_LDR Q17 X2 (Immediate_Offset (word 18446744073709551584)) *)
  0x4e7485fd;       (* arm_ADD_VEC Q29 Q15 Q20 16 128 *)
  0x6e7485e5;       (* arm_SUB_VEC Q5 Q15 Q20 16 128 *)
  0x6e7cb7a2;       (* arm_SQRDMULH_VEC Q2 Q29 Q28 16 128 *)
  0x6e778754;       (* arm_SUB_VEC Q20 Q26 Q23 16 128 *)
  0x4e77875c;       (* arm_ADD_VEC Q28 Q26 Q23 16 128 *)
  0x4e6b9faa;       (* arm_MUL_VEC Q10 Q29 Q11 16 128 *)
  0x6e70b4b3;       (* arm_SQRDMULH_VEC Q19 Q5 Q16 16 128 *)
  0x4e719ca9;       (* arm_MUL_VEC Q9 Q5 Q17 16 128 *)
  0x6f47404a;       (* arm_MLS_VEC Q10 Q2 (Q7 :> LANE_H 0) 16 128 *)
  0x6f474269;       (* arm_MLS_VEC Q9 Q19 (Q7 :> LANE_H 0) 16 128 *)
  0x4e6a8780;       (* arm_ADD_VEC Q0 Q28 Q10 16 128 *)
  0x6e6a8781;       (* arm_SUB_VEC Q1 Q28 Q10 16 128 *)
  0x4e698682;       (* arm_ADD_VEC Q2 Q20 Q9 16 128 *)
  0x6e698683;       (* arm_SUB_VEC Q3 Q20 Q9 16 128 *)
  0x4e813817;       (* arm_ZIP1 Q23 Q0 Q1 32 128 *)
  0x4e817801;       (* arm_ZIP2 Q1 Q0 Q1 32 128 *)
  0x4e833840;       (* arm_ZIP1 Q0 Q2 Q3 32 128 *)
  0x4e837843;       (* arm_ZIP2 Q3 Q2 Q3 32 128 *)
  0x4ec03ae2;       (* arm_ZIP1 Q2 Q23 Q0 64 128 *)
  0x4ec07ae0;       (* arm_ZIP2 Q0 Q23 Q0 64 128 *)
  0xad000002;       (* arm_STP Q2 Q0 X0 (Immediate_Offset (word 0)) *)
  0x4ec33822;       (* arm_ZIP1 Q2 Q1 Q3 64 128 *)
  0x4ec37820;       (* arm_ZIP2 Q0 Q1 Q3 64 128 *)
  0xad010002;       (* arm_STP Q2 Q0 X0 (Immediate_Offset (word 32)) *)
  0x91010000;       (* arm_ADD X0 X0 (rvalue (word 64)) *)
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
 (`bytes_loaded s (word (pc + 0x510)) mlkem_ntt_data <=>
   read (memory :> bytes(word (pc + 0x510),928)) s =
   num_of_bytelist mlkem_ntt_data`,
  REWRITE_TAC[bytes_loaded; READ_BYTELIST_EQ_BYTES;
    CONV_RULE (RAND_CONV LENGTH_CONV)
     (AP_TERM `LENGTH:byte list->num` mlkem_ntt_data)]);;

let MLKEM_NTT_CORRECT = prove
 (`!a x pc.
      nonoverlapping (word pc,0x8b0) (a,512)
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc)
                  (APPEND mlkem_ntt_mc mlkem_ntt_data) /\
                read PC s = word (pc + 0x14) /\
                C_ARGUMENTS [a] s /\
                !i. i < 256
                    ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                        x i)
           (\s. read PC s = word(pc + 0x4f8) /\
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
   `word(pc + 0x5b0):int64 = word_add (word(pc + 0x510)) (word 160)`) THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM BYTES_LOADED_DATA]) THEN
  ABBREV_TAC `wpc:int64 = word(pc + 0x510)` THEN
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
            (1--901) THEN
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
  ASM_REWRITE_TAC[I_THM; WORD_ADD_0] THEN DISCARD_STATE_TAC "s901" THEN
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
          [(word pc,0x8b0); (a,512)] /\
      nonoverlapping (word pc,0x8b0) (a,512)
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
