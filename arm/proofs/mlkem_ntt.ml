(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Forward number theoretic transform.                                       *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "common/mlkem_mldsa.ml";;

(**** print_literal_from_elf "arm/mlkem/mlkem_ntt.o";;
 ****)

let mlkem_ntt_mc = define_assert_from_elf
 "mlkem_ntt_mc" "arm/mlkem/mlkem_ntt.o"
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
  0xaa0003e3;       (* arm_MOV X3 X0 *)
  0xd2800084;       (* arm_MOV X4 (rvalue (word 4)) *)
  0x3cc20420;       (* arm_LDR Q0 X1 (Postimmediate_Offset (word 32)) *)
  0x3cdf0021;       (* arm_LDR Q1 X1 (Immediate_Offset (word 18446744073709551600)) *)
  0x3dc0601a;       (* arm_LDR Q26 X0 (Immediate_Offset (word 384)) *)
  0x3dc0400e;       (* arm_LDR Q14 X0 (Immediate_Offset (word 256)) *)
  0x3dc0100c;       (* arm_LDR Q12 X0 (Immediate_Offset (word 64)) *)
  0x3dc03004;       (* arm_LDR Q4 X0 (Immediate_Offset (word 192)) *)
  0x3dc0000b;       (* arm_LDR Q11 X0 (Immediate_Offset (word 0)) *)
  0x3dc05016;       (* arm_LDR Q22 X0 (Immediate_Offset (word 320)) *)
  0x3dc0700a;       (* arm_LDR Q10 X0 (Immediate_Offset (word 448)) *)
  0x3dc0201c;       (* arm_LDR Q28 X0 (Immediate_Offset (word 128)) *)
  0x4f50d357;       (* arm_SQRDMULH_VEC Q23 Q26 (Q0 :> LANE_H 1) 16 128 *)
  0x4f40835a;       (* arm_MUL_VEC Q26 Q26 (Q0 :> LANE_H 0) 16 128 *)
  0x4f50d1d8;       (* arm_SQRDMULH_VEC Q24 Q14 (Q0 :> LANE_H 1) 16 128 *)
  0x4f4081c9;       (* arm_MUL_VEC Q9 Q14 (Q0 :> LANE_H 0) 16 128 *)
  0x4f50d2ce;       (* arm_SQRDMULH_VEC Q14 Q22 (Q0 :> LANE_H 1) 16 128 *)
  0x4f4082d6;       (* arm_MUL_VEC Q22 Q22 (Q0 :> LANE_H 0) 16 128 *)
  0x4f50d15d;       (* arm_SQRDMULH_VEC Q29 Q10 (Q0 :> LANE_H 1) 16 128 *)
  0x6f4741d6;       (* arm_MLS_VEC Q22 Q14 (Q7 :> LANE_H 0) 16 128 *)
  0x6f4742fa;       (* arm_MLS_VEC Q26 Q23 (Q7 :> LANE_H 0) 16 128 *)
  0x4f40814e;       (* arm_MUL_VEC Q14 Q10 (Q0 :> LANE_H 0) 16 128 *)
  0x4e76858a;       (* arm_ADD_VEC Q10 Q12 Q22 16 128 *)
  0x6e76858c;       (* arm_SUB_VEC Q12 Q12 Q22 16 128 *)
  0x6f4743ae;       (* arm_MLS_VEC Q14 Q29 (Q7 :> LANE_H 0) 16 128 *)
  0x6e7a8796;       (* arm_SUB_VEC Q22 Q28 Q26 16 128 *)
  0x4e7a8797;       (* arm_ADD_VEC Q23 Q28 Q26 16 128 *)
  0x6f474309;       (* arm_MLS_VEC Q9 Q24 (Q7 :> LANE_H 0) 16 128 *)
  0x4f50dada;       (* arm_SQRDMULH_VEC Q26 Q22 (Q0 :> LANE_H 5) 16 128 *)
  0x6e6e849c;       (* arm_SUB_VEC Q28 Q4 Q14 16 128 *)
  0x4e6e848e;       (* arm_ADD_VEC Q14 Q4 Q14 16 128 *)
  0x4f408acd;       (* arm_MUL_VEC Q13 Q22 (Q0 :> LANE_H 4) 16 128 *)
  0x6e698572;       (* arm_SUB_VEC Q18 Q11 Q9 16 128 *)
  0x4f50db84;       (* arm_SQRDMULH_VEC Q4 Q28 (Q0 :> LANE_H 5) 16 128 *)
  0x4f70d1d6;       (* arm_SQRDMULH_VEC Q22 Q14 (Q0 :> LANE_H 3) 16 128 *)
  0x4f408b9c;       (* arm_MUL_VEC Q28 Q28 (Q0 :> LANE_H 4) 16 128 *)
  0x6f47409c;       (* arm_MLS_VEC Q28 Q4 (Q7 :> LANE_H 0) 16 128 *)
  0x4f6081ce;       (* arm_MUL_VEC Q14 Q14 (Q0 :> LANE_H 2) 16 128 *)
  0x6f4742ce;       (* arm_MLS_VEC Q14 Q22 (Q7 :> LANE_H 0) 16 128 *)
  0x4e7c8584;       (* arm_ADD_VEC Q4 Q12 Q28 16 128 *)
  0x6e7c858c;       (* arm_SUB_VEC Q12 Q12 Q28 16 128 *)
  0x6f47434d;       (* arm_MLS_VEC Q13 Q26 (Q7 :> LANE_H 0) 16 128 *)
  0x4f71d09a;       (* arm_SQRDMULH_VEC Q26 Q4 (Q1 :> LANE_H 3) 16 128 *)
  0x6e6e8556;       (* arm_SUB_VEC Q22 Q10 Q14 16 128 *)
  0x4e6e8553;       (* arm_ADD_VEC Q19 Q10 Q14 16 128 *)
  0x4f618083;       (* arm_MUL_VEC Q3 Q4 (Q1 :> LANE_H 2) 16 128 *)
  0x4f51d2ce;       (* arm_SQRDMULH_VEC Q14 Q22 (Q1 :> LANE_H 1) 16 128 *)
  0x4f4182dc;       (* arm_MUL_VEC Q28 Q22 (Q1 :> LANE_H 0) 16 128 *)
  0x6f474343;       (* arm_MLS_VEC Q3 Q26 (Q7 :> LANE_H 0) 16 128 *)
  0x6f4741dc;       (* arm_MLS_VEC Q28 Q14 (Q7 :> LANE_H 0) 16 128 *)
  0x4f51d98e;       (* arm_SQRDMULH_VEC Q14 Q12 (Q1 :> LANE_H 5) 16 128 *)
  0x4f41899a;       (* arm_MUL_VEC Q26 Q12 (Q1 :> LANE_H 4) 16 128 *)
  0x4f70da75;       (* arm_SQRDMULH_VEC Q21 Q19 (Q0 :> LANE_H 7) 16 128 *)
  0x6f4741da;       (* arm_MLS_VEC Q26 Q14 (Q7 :> LANE_H 0) 16 128 *)
  0xd1000484;       (* arm_SUB X4 X4 (rvalue (word 1)) *)
  0x3dc06411;       (* arm_LDR Q17 X0 (Immediate_Offset (word 400)) *)
  0x4f608a76;       (* arm_MUL_VEC Q22 Q19 (Q0 :> LANE_H 6) 16 128 *)
  0x3dc04418;       (* arm_LDR Q24 X0 (Immediate_Offset (word 272)) *)
  0x4e6d8653;       (* arm_ADD_VEC Q19 Q18 Q13 16 128 *)
  0x6f4742b6;       (* arm_MLS_VEC Q22 Q21 (Q7 :> LANE_H 0) 16 128 *)
  0x6e6d8655;       (* arm_SUB_VEC Q21 Q18 Q13 16 128 *)
  0x3dc0340d;       (* arm_LDR Q13 X0 (Immediate_Offset (word 208)) *)
  0x3dc01412;       (* arm_LDR Q18 X0 (Immediate_Offset (word 80)) *)
  0x4f50d22e;       (* arm_SQRDMULH_VEC Q14 Q17 (Q0 :> LANE_H 1) 16 128 *)
  0x3dc0541e;       (* arm_LDR Q30 X0 (Immediate_Offset (word 336)) *)
  0x3dc07404;       (* arm_LDR Q4 X0 (Immediate_Offset (word 464)) *)
  0x4e698562;       (* arm_ADD_VEC Q2 Q11 Q9 16 128 *)
  0x4f70d2fb;       (* arm_SQRDMULH_VEC Q27 Q23 (Q0 :> LANE_H 3) 16 128 *)
  0x3dc0040b;       (* arm_LDR Q11 X0 (Immediate_Offset (word 16)) *)
  0x6e7a86b0;       (* arm_SUB_VEC Q16 Q21 Q26 16 128 *)
  0x3dc02406;       (* arm_LDR Q6 X0 (Immediate_Offset (word 144)) *)
  0x6e63867d;       (* arm_SUB_VEC Q29 Q19 Q3 16 128 *)
  0x4f6082ef;       (* arm_MUL_VEC Q15 Q23 (Q0 :> LANE_H 2) 16 128 *)
  0x4e7a86ac;       (* arm_ADD_VEC Q12 Q21 Q26 16 128 *)
  0x4f50d3da;       (* arm_SQRDMULH_VEC Q26 Q30 (Q0 :> LANE_H 1) 16 128 *)
  0x4e638663;       (* arm_ADD_VEC Q3 Q19 Q3 16 128 *)
  0x3d80501d;       (* arm_STR Q29 X0 (Immediate_Offset (word 320)) *)
  0x6f47436f;       (* arm_MLS_VEC Q15 Q27 (Q7 :> LANE_H 0) 16 128 *)
  0x3d804003;       (* arm_STR Q3 X0 (Immediate_Offset (word 256)) *)
  0x3d80600c;       (* arm_STR Q12 X0 (Immediate_Offset (word 384)) *)
  0x4f40822a;       (* arm_MUL_VEC Q10 Q17 (Q0 :> LANE_H 0) 16 128 *)
  0x3d807010;       (* arm_STR Q16 X0 (Immediate_Offset (word 448)) *)
  0x6f4741ca;       (* arm_MLS_VEC Q10 Q14 (Q7 :> LANE_H 0) 16 128 *)
  0x6e6f8451;       (* arm_SUB_VEC Q17 Q2 Q15 16 128 *)
  0x4f4083cc;       (* arm_MUL_VEC Q12 Q30 (Q0 :> LANE_H 0) 16 128 *)
  0x6e7c8630;       (* arm_SUB_VEC Q16 Q17 Q28 16 128 *)
  0x6f47434c;       (* arm_MLS_VEC Q12 Q26 (Q7 :> LANE_H 0) 16 128 *)
  0x6e6a84d9;       (* arm_SUB_VEC Q25 Q6 Q10 16 128 *)
  0x3d803010;       (* arm_STR Q16 X0 (Immediate_Offset (word 192)) *)
  0x4f50d308;       (* arm_SQRDMULH_VEC Q8 Q24 (Q0 :> LANE_H 1) 16 128 *)
  0x4e6a84d7;       (* arm_ADD_VEC Q23 Q6 Q10 16 128 *)
  0x4f50d08e;       (* arm_SQRDMULH_VEC Q14 Q4 (Q0 :> LANE_H 1) 16 128 *)
  0x4e6c8650;       (* arm_ADD_VEC Q16 Q18 Q12 16 128 *)
  0x4f408309;       (* arm_MUL_VEC Q9 Q24 (Q0 :> LANE_H 0) 16 128 *)
  0x6e6c8645;       (* arm_SUB_VEC Q5 Q18 Q12 16 128 *)
  0x4e7c863a;       (* arm_ADD_VEC Q26 Q17 Q28 16 128 *)
  0x4f408095;       (* arm_MUL_VEC Q21 Q4 (Q0 :> LANE_H 0) 16 128 *)
  0x4e6f845b;       (* arm_ADD_VEC Q27 Q2 Q15 16 128 *)
  0x3d80201a;       (* arm_STR Q26 X0 (Immediate_Offset (word 128)) *)
  0x6f4741d5;       (* arm_MLS_VEC Q21 Q14 (Q7 :> LANE_H 0) 16 128 *)
  0x6e76876c;       (* arm_SUB_VEC Q12 Q27 Q22 16 128 *)
  0x4e76877d;       (* arm_ADD_VEC Q29 Q27 Q22 16 128 *)
  0x6f474109;       (* arm_MLS_VEC Q9 Q8 (Q7 :> LANE_H 0) 16 128 *)
  0x3d80100c;       (* arm_STR Q12 X0 (Immediate_Offset (word 64)) *)
  0x3c81041d;       (* arm_STR Q29 X0 (Postimmediate_Offset (word 16)) *)
  0x4f50db32;       (* arm_SQRDMULH_VEC Q18 Q25 (Q0 :> LANE_H 5) 16 128 *)
  0x6e7585ba;       (* arm_SUB_VEC Q26 Q13 Q21 16 128 *)
  0x4e7585b5;       (* arm_ADD_VEC Q21 Q13 Q21 16 128 *)
  0x4f408b2d;       (* arm_MUL_VEC Q13 Q25 (Q0 :> LANE_H 4) 16 128 *)
  0x4f50db5c;       (* arm_SQRDMULH_VEC Q28 Q26 (Q0 :> LANE_H 5) 16 128 *)
  0x4f70d2af;       (* arm_SQRDMULH_VEC Q15 Q21 (Q0 :> LANE_H 3) 16 128 *)
  0x4f408b5f;       (* arm_MUL_VEC Q31 Q26 (Q0 :> LANE_H 4) 16 128 *)
  0x6f47439f;       (* arm_MLS_VEC Q31 Q28 (Q7 :> LANE_H 0) 16 128 *)
  0x4f6082bb;       (* arm_MUL_VEC Q27 Q21 (Q0 :> LANE_H 2) 16 128 *)
  0x6f4741fb;       (* arm_MLS_VEC Q27 Q15 (Q7 :> LANE_H 0) 16 128 *)
  0x4e7f84aa;       (* arm_ADD_VEC Q10 Q5 Q31 16 128 *)
  0x6f47424d;       (* arm_MLS_VEC Q13 Q18 (Q7 :> LANE_H 0) 16 128 *)
  0x6e698572;       (* arm_SUB_VEC Q18 Q11 Q9 16 128 *)
  0x6e7f84ae;       (* arm_SUB_VEC Q14 Q5 Q31 16 128 *)
  0x4f71d159;       (* arm_SQRDMULH_VEC Q25 Q10 (Q1 :> LANE_H 3) 16 128 *)
  0x6e7b861a;       (* arm_SUB_VEC Q26 Q16 Q27 16 128 *)
  0x4e7b8613;       (* arm_ADD_VEC Q19 Q16 Q27 16 128 *)
  0x4f618143;       (* arm_MUL_VEC Q3 Q10 (Q1 :> LANE_H 2) 16 128 *)
  0x4f51d35d;       (* arm_SQRDMULH_VEC Q29 Q26 (Q1 :> LANE_H 1) 16 128 *)
  0x4f41835c;       (* arm_MUL_VEC Q28 Q26 (Q1 :> LANE_H 0) 16 128 *)
  0x6f474323;       (* arm_MLS_VEC Q3 Q25 (Q7 :> LANE_H 0) 16 128 *)
  0x6f4743bc;       (* arm_MLS_VEC Q28 Q29 (Q7 :> LANE_H 0) 16 128 *)
  0x4f51d9c4;       (* arm_SQRDMULH_VEC Q4 Q14 (Q1 :> LANE_H 5) 16 128 *)
  0x4f4189da;       (* arm_MUL_VEC Q26 Q14 (Q1 :> LANE_H 4) 16 128 *)
  0x4f70da75;       (* arm_SQRDMULH_VEC Q21 Q19 (Q0 :> LANE_H 7) 16 128 *)
  0x6f47409a;       (* arm_MLS_VEC Q26 Q4 (Q7 :> LANE_H 0) 16 128 *)
  0xd1000484;       (* arm_SUB X4 X4 (rvalue (word 1)) *)
  0xb5fff664;       (* arm_CBNZ X4 (word 2096844) *)
  0x4e6d8654;       (* arm_ADD_VEC Q20 Q18 Q13 16 128 *)
  0x4f70d2f0;       (* arm_SQRDMULH_VEC Q16 Q23 (Q0 :> LANE_H 3) 16 128 *)
  0x6e6d8648;       (* arm_SUB_VEC Q8 Q18 Q13 16 128 *)
  0x6e638685;       (* arm_SUB_VEC Q5 Q20 Q3 16 128 *)
  0x4f6082fb;       (* arm_MUL_VEC Q27 Q23 (Q0 :> LANE_H 2) 16 128 *)
  0x4e69857f;       (* arm_ADD_VEC Q31 Q11 Q9 16 128 *)
  0x4e7a850e;       (* arm_ADD_VEC Q14 Q8 Q26 16 128 *)
  0x6e7a851a;       (* arm_SUB_VEC Q26 Q8 Q26 16 128 *)
  0x3d805005;       (* arm_STR Q5 X0 (Immediate_Offset (word 320)) *)
  0x6f47421b;       (* arm_MLS_VEC Q27 Q16 (Q7 :> LANE_H 0) 16 128 *)
  0x3d80600e;       (* arm_STR Q14 X0 (Immediate_Offset (word 384)) *)
  0x4f608a79;       (* arm_MUL_VEC Q25 Q19 (Q0 :> LANE_H 6) 16 128 *)
  0x3d80701a;       (* arm_STR Q26 X0 (Immediate_Offset (word 448)) *)
  0x6f4742b9;       (* arm_MLS_VEC Q25 Q21 (Q7 :> LANE_H 0) 16 128 *)
  0x6e7b87fa;       (* arm_SUB_VEC Q26 Q31 Q27 16 128 *)
  0x4e63868f;       (* arm_ADD_VEC Q15 Q20 Q3 16 128 *)
  0x4e7b87fd;       (* arm_ADD_VEC Q29 Q31 Q27 16 128 *)
  0x6e7c8756;       (* arm_SUB_VEC Q22 Q26 Q28 16 128 *)
  0x3d80400f;       (* arm_STR Q15 X0 (Immediate_Offset (word 256)) *)
  0x4e7c875a;       (* arm_ADD_VEC Q26 Q26 Q28 16 128 *)
  0x6e7987bb;       (* arm_SUB_VEC Q27 Q29 Q25 16 128 *)
  0x4e7987b4;       (* arm_ADD_VEC Q20 Q29 Q25 16 128 *)
  0x3d80201a;       (* arm_STR Q26 X0 (Immediate_Offset (word 128)) *)
  0x3d803016;       (* arm_STR Q22 X0 (Immediate_Offset (word 192)) *)
  0x3d80101b;       (* arm_STR Q27 X0 (Immediate_Offset (word 64)) *)
  0x3c810414;       (* arm_STR Q20 X0 (Postimmediate_Offset (word 16)) *)
  0xaa0303e0;       (* arm_MOV X0 X3 *)
  0xd2800104;       (* arm_MOV X4 (rvalue (word 8)) *)
  0x3cc1042b;       (* arm_LDR Q11 X1 (Postimmediate_Offset (word 16)) *)
  0x3dc00c09;       (* arm_LDR Q9 X0 (Immediate_Offset (word 48)) *)
  0x3dc0081e;       (* arm_LDR Q30 X0 (Immediate_Offset (word 32)) *)
  0x3cc6044c;       (* arm_LDR Q12 X2 (Postimmediate_Offset (word 96)) *)
  0x3cdc0045;       (* arm_LDR Q5 X2 (Immediate_Offset (word 18446744073709551552)) *)
  0x4f5bd137;       (* arm_SQRDMULH_VEC Q23 Q9 (Q11 :> LANE_H 1) 16 128 *)
  0x3dc0000f;       (* arm_LDR Q15 X0 (Immediate_Offset (word 0)) *)
  0x4f4b8126;       (* arm_MUL_VEC Q6 Q9 (Q11 :> LANE_H 0) 16 128 *)
  0x3dc0041c;       (* arm_LDR Q28 X0 (Immediate_Offset (word 16)) *)
  0x4f5bd3ca;       (* arm_SQRDMULH_VEC Q10 Q30 (Q11 :> LANE_H 1) 16 128 *)
  0x6f4742e6;       (* arm_MLS_VEC Q6 Q23 (Q7 :> LANE_H 0) 16 128 *)
  0x4f4b83c0;       (* arm_MUL_VEC Q0 Q30 (Q11 :> LANE_H 0) 16 128 *)
  0x6f474140;       (* arm_MLS_VEC Q0 Q10 (Q7 :> LANE_H 0) 16 128 *)
  0x3cdd0055;       (* arm_LDR Q21 X2 (Immediate_Offset (word 18446744073709551568)) *)
  0x4e66879b;       (* arm_ADD_VEC Q27 Q28 Q6 16 128 *)
  0x6e668799;       (* arm_SUB_VEC Q25 Q28 Q6 16 128 *)
  0x4f6b8366;       (* arm_MUL_VEC Q6 Q27 (Q11 :> LANE_H 2) 16 128 *)
  0x4f7bd371;       (* arm_SQRDMULH_VEC Q17 Q27 (Q11 :> LANE_H 3) 16 128 *)
  0x4f5bdb33;       (* arm_SQRDMULH_VEC Q19 Q25 (Q11 :> LANE_H 5) 16 128 *)
  0x3cdb0052;       (* arm_LDR Q18 X2 (Immediate_Offset (word 18446744073709551536)) *)
  0x4f4b8b36;       (* arm_MUL_VEC Q22 Q25 (Q11 :> LANE_H 4) 16 128 *)
  0x6f474226;       (* arm_MLS_VEC Q6 Q17 (Q7 :> LANE_H 0) 16 128 *)
  0x6f474276;       (* arm_MLS_VEC Q22 Q19 (Q7 :> LANE_H 0) 16 128 *)
  0xd1000484;       (* arm_SUB X4 X4 (rvalue (word 1)) *)
  0x3dc01c1b;       (* arm_LDR Q27 X0 (Immediate_Offset (word 112)) *)
  0x3cc10424;       (* arm_LDR Q4 X1 (Postimmediate_Offset (word 16)) *)
  0x6e6085e1;       (* arm_SUB_VEC Q1 Q15 Q0 16 128 *)
  0x3dc0181e;       (* arm_LDR Q30 X0 (Immediate_Offset (word 96)) *)
  0x4e6085f7;       (* arm_ADD_VEC Q23 Q15 Q0 16 128 *)
  0x4e76842b;       (* arm_ADD_VEC Q11 Q1 Q22 16 128 *)
  0x3cdf004a;       (* arm_LDR Q10 X2 (Immediate_Offset (word 18446744073709551600)) *)
  0x6e6686f8;       (* arm_SUB_VEC Q24 Q23 Q6 16 128 *)
  0x4f54d379;       (* arm_SQRDMULH_VEC Q25 Q27 (Q4 :> LANE_H 1) 16 128 *)
  0x4e6686e9;       (* arm_ADD_VEC Q9 Q23 Q6 16 128 *)
  0x6e768430;       (* arm_SUB_VEC Q16 Q1 Q22 16 128 *)
  0x4f44837f;       (* arm_MUL_VEC Q31 Q27 (Q4 :> LANE_H 0) 16 128 *)
  0x4e98692e;       (* arm_TRN2 Q14 Q9 Q24 32 128 *)
  0x4f54d3c1;       (* arm_SQRDMULH_VEC Q1 Q30 (Q4 :> LANE_H 1) 16 128 *)
  0x4e906968;       (* arm_TRN2 Q8 Q11 Q16 32 128 *)
  0x4e90296b;       (* arm_TRN1 Q11 Q11 Q16 32 128 *)
  0x4ec869d3;       (* arm_TRN2 Q19 Q14 Q8 64 128 *)
  0x6f47433f;       (* arm_MLS_VEC Q31 Q25 (Q7 :> LANE_H 0) 16 128 *)
  0x3dc0140f;       (* arm_LDR Q15 X0 (Immediate_Offset (word 80)) *)
  0x4e982922;       (* arm_TRN1 Q2 Q9 Q24 32 128 *)
  0x6e72b671;       (* arm_SQRDMULH_VEC Q17 Q19 Q18 16 128 *)
  0x4ec829c9;       (* arm_TRN1 Q9 Q14 Q8 64 128 *)
  0x4e6c9e7d;       (* arm_MUL_VEC Q29 Q19 Q12 16 128 *)
  0x4ecb685b;       (* arm_TRN2 Q27 Q2 Q11 64 128 *)
  0x4e7f85e0;       (* arm_ADD_VEC Q0 Q15 Q31 16 128 *)
  0x6e7f85f0;       (* arm_SUB_VEC Q16 Q15 Q31 16 128 *)
  0x6e72b76d;       (* arm_SQRDMULH_VEC Q13 Q27 Q18 16 128 *)
  0x6f47423d;       (* arm_MLS_VEC Q29 Q17 (Q7 :> LANE_H 0) 16 128 *)
  0x3cde0051;       (* arm_LDR Q17 X2 (Immediate_Offset (word 18446744073709551584)) *)
  0x3dc0100f;       (* arm_LDR Q15 X0 (Immediate_Offset (word 64)) *)
  0x4e6c9f78;       (* arm_MUL_VEC Q24 Q27 Q12 16 128 *)
  0x4ecb2853;       (* arm_TRN1 Q19 Q2 Q11 64 128 *)
  0x3dc00452;       (* arm_LDR Q18 X2 (Immediate_Offset (word 16)) *)
  0x4f648006;       (* arm_MUL_VEC Q6 Q0 (Q4 :> LANE_H 2) 16 128 *)
  0x3cc6044c;       (* arm_LDR Q12 X2 (Postimmediate_Offset (word 96)) *)
  0x4e7d8539;       (* arm_ADD_VEC Q25 Q9 Q29 16 128 *)
  0x6f4741b8;       (* arm_MLS_VEC Q24 Q13 (Q7 :> LANE_H 0) 16 128 *)
  0x6e7d8534;       (* arm_SUB_VEC Q20 Q9 Q29 16 128 *)
  0x6e75b737;       (* arm_SQRDMULH_VEC Q23 Q25 Q21 16 128 *)
  0x4e659f23;       (* arm_MUL_VEC Q3 Q25 Q5 16 128 *)
  0x4e78866d;       (* arm_ADD_VEC Q13 Q19 Q24 16 128 *)
  0x6e6ab69b;       (* arm_SQRDMULH_VEC Q27 Q20 Q10 16 128 *)
  0x6f4742e3;       (* arm_MLS_VEC Q3 Q23 (Q7 :> LANE_H 0) 16 128 *)
  0x6e78867d;       (* arm_SUB_VEC Q29 Q19 Q24 16 128 *)
  0x4e719e9a;       (* arm_MUL_VEC Q26 Q20 Q17 16 128 *)
  0x6f47437a;       (* arm_MLS_VEC Q26 Q27 (Q7 :> LANE_H 0) 16 128 *)
  0x4e6385bb;       (* arm_ADD_VEC Q27 Q13 Q3 16 128 *)
  0x4f74d00e;       (* arm_SQRDMULH_VEC Q14 Q0 (Q4 :> LANE_H 3) 16 128 *)
  0x6e6385b3;       (* arm_SUB_VEC Q19 Q13 Q3 16 128 *)
  0x3cdc0045;       (* arm_LDR Q5 X2 (Immediate_Offset (word 18446744073709551552)) *)
  0x4f4483c0;       (* arm_MUL_VEC Q0 Q30 (Q4 :> LANE_H 0) 16 128 *)
  0x4e932b68;       (* arm_TRN1 Q8 Q27 Q19 32 128 *)
  0x6e7a87b5;       (* arm_SUB_VEC Q21 Q29 Q26 16 128 *)
  0x4e7a87ab;       (* arm_ADD_VEC Q11 Q29 Q26 16 128 *)
  0x4e936b7e;       (* arm_TRN2 Q30 Q27 Q19 32 128 *)
  0x4f54da13;       (* arm_SQRDMULH_VEC Q19 Q16 (Q4 :> LANE_H 5) 16 128 *)
  0x4e95696a;       (* arm_TRN2 Q10 Q11 Q21 32 128 *)
  0x4f448a16;       (* arm_MUL_VEC Q22 Q16 (Q4 :> LANE_H 4) 16 128 *)
  0x4e95297c;       (* arm_TRN1 Q28 Q11 Q21 32 128 *)
  0x4eca2bdd;       (* arm_TRN1 Q29 Q30 Q10 64 128 *)
  0x3cdd0055;       (* arm_LDR Q21 X2 (Immediate_Offset (word 18446744073709551568)) *)
  0x6f474020;       (* arm_MLS_VEC Q0 Q1 (Q7 :> LANE_H 0) 16 128 *)
  0x4edc6914;       (* arm_TRN2 Q20 Q8 Q28 64 128 *)
  0x4eca6bda;       (* arm_TRN2 Q26 Q30 Q10 64 128 *)
  0x3d80041d;       (* arm_STR Q29 X0 (Immediate_Offset (word 16)) *)
  0x4edc2903;       (* arm_TRN1 Q3 Q8 Q28 64 128 *)
  0x6f474276;       (* arm_MLS_VEC Q22 Q19 (Q7 :> LANE_H 0) 16 128 *)
  0x3d800814;       (* arm_STR Q20 X0 (Immediate_Offset (word 32)) *)
  0x3d800c1a;       (* arm_STR Q26 X0 (Immediate_Offset (word 48)) *)
  0x6f4741c6;       (* arm_MLS_VEC Q6 Q14 (Q7 :> LANE_H 0) 16 128 *)
  0x3c840403;       (* arm_STR Q3 X0 (Postimmediate_Offset (word 64)) *)
  0xd1000484;       (* arm_SUB X4 X4 (rvalue (word 1)) *)
  0xb5fff704;       (* arm_CBNZ X4 (word 2096864) *)
  0x4e6085e4;       (* arm_ADD_VEC Q4 Q15 Q0 16 128 *)
  0x6e6085ee;       (* arm_SUB_VEC Q14 Q15 Q0 16 128 *)
  0x3cdf005a;       (* arm_LDR Q26 X2 (Immediate_Offset (word 18446744073709551600)) *)
  0x4e7685c8;       (* arm_ADD_VEC Q8 Q14 Q22 16 128 *)
  0x6e7685db;       (* arm_SUB_VEC Q27 Q14 Q22 16 128 *)
  0x6e66848d;       (* arm_SUB_VEC Q13 Q4 Q6 16 128 *)
  0x4e66849d;       (* arm_ADD_VEC Q29 Q4 Q6 16 128 *)
  0x4e9b690b;       (* arm_TRN2 Q11 Q8 Q27 32 128 *)
  0x4e8d6ba1;       (* arm_TRN2 Q1 Q29 Q13 32 128 *)
  0x4e9b291b;       (* arm_TRN1 Q27 Q8 Q27 32 128 *)
  0x4e8d2bb1;       (* arm_TRN1 Q17 Q29 Q13 32 128 *)
  0x4ecb683c;       (* arm_TRN2 Q28 Q1 Q11 64 128 *)
  0x4ecb2830;       (* arm_TRN1 Q16 Q1 Q11 64 128 *)
  0x6e72b780;       (* arm_SQRDMULH_VEC Q0 Q28 Q18 16 128 *)
  0x4edb6a33;       (* arm_TRN2 Q19 Q17 Q27 64 128 *)
  0x4edb2a21;       (* arm_TRN1 Q1 Q17 Q27 64 128 *)
  0x4e6c9f9b;       (* arm_MUL_VEC Q27 Q28 Q12 16 128 *)
  0x6e72b669;       (* arm_SQRDMULH_VEC Q9 Q19 Q18 16 128 *)
  0x6f47401b;       (* arm_MLS_VEC Q27 Q0 (Q7 :> LANE_H 0) 16 128 *)
  0x4e6c9e74;       (* arm_MUL_VEC Q20 Q19 Q12 16 128 *)
  0x6f474134;       (* arm_MLS_VEC Q20 Q9 (Q7 :> LANE_H 0) 16 128 *)
  0x6e7b861e;       (* arm_SUB_VEC Q30 Q16 Q27 16 128 *)
  0x4e7b8619;       (* arm_ADD_VEC Q25 Q16 Q27 16 128 *)
  0x6e7ab7ce;       (* arm_SQRDMULH_VEC Q14 Q30 Q26 16 128 *)
  0x3cde005a;       (* arm_LDR Q26 X2 (Immediate_Offset (word 18446744073709551584)) *)
  0x6e75b73f;       (* arm_SQRDMULH_VEC Q31 Q25 Q21 16 128 *)
  0x4e74843b;       (* arm_ADD_VEC Q27 Q1 Q20 16 128 *)
  0x4e7a9fcf;       (* arm_MUL_VEC Q15 Q30 Q26 16 128 *)
  0x6f4741cf;       (* arm_MLS_VEC Q15 Q14 (Q7 :> LANE_H 0) 16 128 *)
  0x6e74843a;       (* arm_SUB_VEC Q26 Q1 Q20 16 128 *)
  0x4e659f2c;       (* arm_MUL_VEC Q12 Q25 Q5 16 128 *)
  0x6f4743ec;       (* arm_MLS_VEC Q12 Q31 (Q7 :> LANE_H 0) 16 128 *)
  0x6e6f8742;       (* arm_SUB_VEC Q2 Q26 Q15 16 128 *)
  0x4e6f8740;       (* arm_ADD_VEC Q0 Q26 Q15 16 128 *)
  0x4e82680e;       (* arm_TRN2 Q14 Q0 Q2 32 128 *)
  0x6e6c877a;       (* arm_SUB_VEC Q26 Q27 Q12 16 128 *)
  0x4e6c877b;       (* arm_ADD_VEC Q27 Q27 Q12 16 128 *)
  0x4e822811;       (* arm_TRN1 Q17 Q0 Q2 32 128 *)
  0x4e9a2b65;       (* arm_TRN1 Q5 Q27 Q26 32 128 *)
  0x4e9a6b7a;       (* arm_TRN2 Q26 Q27 Q26 32 128 *)
  0x4ece2b59;       (* arm_TRN1 Q25 Q26 Q14 64 128 *)
  0x4ed128a0;       (* arm_TRN1 Q0 Q5 Q17 64 128 *)
  0x4ece6b55;       (* arm_TRN2 Q21 Q26 Q14 64 128 *)
  0x4ed168ba;       (* arm_TRN2 Q26 Q5 Q17 64 128 *)
  0x3d800419;       (* arm_STR Q25 X0 (Immediate_Offset (word 16)) *)
  0x3c840400;       (* arm_STR Q0 X0 (Postimmediate_Offset (word 64)) *)
  0x3c9f0015;       (* arm_STR Q21 X0 (Immediate_Offset (word 18446744073709551600)) *)
  0x3c9e001a;       (* arm_STR Q26 X0 (Immediate_Offset (word 18446744073709551584)) *)
  0x6d4027e8;       (* arm_LDP D8 D9 SP (Immediate_Offset (iword (&0))) *)
  0x6d412fea;       (* arm_LDP D10 D11 SP (Immediate_Offset (iword (&16))) *)
  0x6d4237ec;       (* arm_LDP D12 D13 SP (Immediate_Offset (iword (&32))) *)
  0x6d433fee;       (* arm_LDP D14 D15 SP (Immediate_Offset (iword (&48))) *)
  0x910103ff;       (* arm_ADD SP SP (rvalue (word 64)) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let MLKEM_NTT_EXEC = ARM_MK_EXEC_RULE mlkem_ntt_mc;;

(* ------------------------------------------------------------------------- *)
(* Data tables that are assumed in the precondition.                         *)
(* ------------------------------------------------------------------------- *)

let ntt_zetas_layer01234 = define
 `ntt_zetas_layer01234:int list =
   [-- &1600; -- &15749; -- &749; -- &7373; -- &40; -- &394; -- &687; -- &6762;
    &630; &6201; -- &1432; -- &14095; &848; &8347; &0; &0; &1062; &10453; &296;
    &2914; -- &882; -- &8682; &0; &0; -- &1410; -- &13879; &1339; &13180; &1476;
    &14529; &0; &0; &193; &1900; -- &283; -- &2786; &56; &551; &0; &0; &797;
    &7845; -- &1089; -- &10719; &1333; &13121; &0; &0; -- &543; -- &5345;
    &1426; &14036; -- &1235; -- &12156; &0; &0; -- &69; -- &679; &535; &5266;
    -- &447; -- &4400; &0; &0; &569; &5601; -- &936; -- &9213; -- &450;
    -- &4429; &0; &0; -- &1583; -- &15582; -- &1355; -- &13338; &821;
    &8081; &0; &0]`;;

let ntt_zetas_layer56 = define
`ntt_zetas_layer56:int list =
  [&289; &289; &331; &331; -- &76; -- &76; -- &1573; -- &1573; &2845;
   &2845; &3258; &3258; -- &748; -- &748; -- &15483; -- &15483; &17; &17;
   &583; &583; &1637; &1637; -- &1041; -- &1041; &167; &167; &5739;
   &5739; &16113; &16113; -- &10247; -- &10247; -- &568; -- &568;
   -- &680; -- &680; &723; &723; &1100; &1100; -- &5591; -- &5591; -- &6693;
   -- &6693; &7117; &7117; &10828; &10828; &1197; &1197; -- &1025;
   -- &1025; -- &1052; -- &1052; -- &1274; -- &1274; &11782; &11782;
   -- &10089; -- &10089; -- &10355; -- &10355; -- &12540; -- &12540; &1409;
   &1409; -- &48; -- &48; &756; &756; -- &314; -- &314; &13869; &13869;
   -- &472; -- &472; &7441; &7441; -- &3091; -- &3091; -- &667; -- &667;
   &233; &233; -- &1173; -- &1173; -- &279; -- &279; -- &6565; -- &6565;
   &2293; &2293; -- &11546; -- &11546; -- &2746; -- &2746; &650; &650;
   -- &1352; -- &1352; -- &816; -- &816; &632; &632; &6398; &6398;
   -- &13308; -- &13308; -- &8032; -- &8032; &6221; &6221; -- &1626;
   -- &1626; -- &540; -- &540; -- &1482; -- &1482; &1461; &1461; -- &16005;
   -- &16005; -- &5315; -- &5315; -- &14588; -- &14588; &14381; &14381;
   &1651; &1651; -- &1540; -- &1540; &952; &952; -- &642; -- &642;
   &16251; &16251; -- &15159; -- &15159; &9371; &9371; -- &6319;
   -- &6319; -- &464; -- &464; &33; &33; &1320; &1320; -- &1414; -- &1414;
   -- &4567; -- &4567; &325; &325; &12993; &12993; -- &13918; -- &13918;
   &939; &939; -- &892; -- &892; &733; &733; &268; &268; &9243; &9243;
   -- &8780; -- &8780; &7215; &7215; &2638; &2638; -- &1021; -- &1021;
   -- &941; -- &941; -- &992; -- &992; &641; &641; -- &10050; -- &10050;
   -- &9262; -- &9262; -- &9764; -- &9764; &6309; &6309; -- &1010; -- &1010;
   &1435; &1435; &807; &807; &452; &452; -- &9942; -- &9942; &14125;
   &14125; &7943; &7943; &4449; &4449; &1584; &1584; -- &1292; -- &1292;
   &375; &375; -- &1239; -- &1239; &15592; &15592; -- &12717; -- &12717;
   &3691; &3691; -- &12196; -- &12196; -- &1031; -- &1031; -- &109;
   -- &109; -- &780; -- &780; &1645; &1645; -- &10148; -- &10148; -- &1073;
   -- &1073; -- &7678; -- &7678; &16192; &16192; &1438; &1438; -- &461;
   -- &461; &1534; &1534; -- &927; -- &927; &14155; &14155; -- &4538;
   -- &4538; &15099; &15099; -- &9125; -- &9125; &1063; &1063; -- &556;
   -- &556; -- &1230; -- &1230; -- &863; -- &863; &10463; &10463; -- &5473;
   -- &5473; -- &12107; -- &12107; -- &8495; -- &8495; &319; &319; &757;
   &757; &561; &561; -- &735; -- &735; &3140; &3140; &7451; &7451; &5522;
   &5522; -- &7235; -- &7235; -- &682; -- &682; -- &712; -- &712; &1481;
   &1481; &648; &648; -- &6713; -- &6713; -- &7008; -- &7008; &14578;
   &14578; &6378; &6378; -- &525; -- &525; &403; &403; &1143; &1143;
   -- &554; -- &554; -- &5168; -- &5168; &3967; &3967; &11251; &11251;
   -- &5453; -- &5453; &1092; &1092; &1026; &1026; -- &1179; -- &1179; &886;
   &886; &10749; &10749; &10099; &10099; -- &11605; -- &11605; &8721;
   &8721; -- &855; -- &855; -- &219; -- &219; &1227; &1227; &910; &910;
   -- &8416; -- &8416; -- &2156; -- &2156; &12078; &12078; &8957; &8957;
   -- &1607; -- &1607; -- &1455; -- &1455; -- &1219; -- &1219; &885;
   &885; -- &15818; -- &15818; -- &14322; -- &14322; -- &11999;
   -- &11999; &8711; &8711; &1212; &1212; &1029; &1029; -- &394; -- &394;
   -- &1175; -- &1175; &11930; &11930; &10129; &10129; -- &3878; -- &3878;
   -- &11566; -- &11566]`;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NTT_CORRECT = prove
 (`!a z_01234 z_56 (zetas_01234:int16 list) (zetas_56:int16 list) x pc.
      ALL (nonoverlapping (a,512))
          [(word pc,0x504); (z_01234,160); (z_56,768)]
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) mlkem_ntt_mc /\
                read PC s = word (pc + 0x14) /\
                C_ARGUMENTS [a; z_01234; z_56] s /\
                wordlist_from_memory(z_01234,80) s = zetas_01234 /\
                wordlist_from_memory(z_56,384) s = zetas_56 /\
                !i. i < 256
                    ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                        x i)
           (\s. read PC s = word(pc + 0x4ec) /\
                (zetas_01234 = MAP iword ntt_zetas_layer01234 /\
                 zetas_56 = MAP iword ntt_zetas_layer56 /\
                 (!i. i < 256 ==> abs(ival(x i)) <= &8191)
                 ==> !i. i < 256
                         ==> let zi =
                        read(memory :> bytes16(word_add a (word(2 * i)))) s in
                        (ival zi == forward_ntt (ival o x) i) (mod &3329) /\
                        abs(ival zi) <= &23594))
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
   `zetas_01234:int16 list = MAP iword ntt_zetas_layer01234 /\
    zetas_56:int16 list = MAP iword ntt_zetas_layer56` THEN
  ASM_REWRITE_TAC[CONJ_ASSOC] THEN REWRITE_TAC[GSYM CONJ_ASSOC] THENL
   [FIRST_X_ASSUM(CONJUNCTS_THEN SUBST1_TAC);
    ARM_QUICKSIM_TAC MLKEM_NTT_EXEC
     [`read X0 s = a`; `read X1 s = z`; `read X2 s = w`;
      `read X3 s = i`; `read X4 s = i`]
     (1--904)] THEN

  (*** Manually expand the cases in the hypotheses ***)

  CONV_TAC(RATOR_CONV(LAND_CONV(ONCE_DEPTH_CONV
   (EXPAND_CASES_CONV THENC ONCE_DEPTH_CONV NUM_MULT_CONV)))) THEN
  CONV_TAC(ONCE_DEPTH_CONV WORDLIST_FROM_MEMORY_CONV) THEN
  REWRITE_TAC[ntt_zetas_layer01234; ntt_zetas_layer56] THEN
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

  MAP_EVERY (fun n -> ARM_STEPS_TAC MLKEM_NTT_EXEC [n] THEN
                      SIMD_SIMPLIFY_TAC[barmul])
            (1--904) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN

  (*** Reverse the restructuring by splitting the 128-bit words up ***)

  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o
    CONV_RULE(SIMD_SIMPLIFY_CONV[]) o
    CONV_RULE(READ_MEMORY_SPLIT_CONV 3) o
    check (can (term_match [] `read qqq s:int128 = xxx`) o concl))) THEN

  (*** Turn the conclusion into an explicit conjunction and split it up ***)

  DISCH_TAC THEN
  CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN REWRITE_TAC[INT_ABS_BOUNDS] THEN
  GEN_REWRITE_TAC (BINDER_CONV o RAND_CONV) [GSYM I_THM] THEN
  CONV_TAC(EXPAND_CASES_CONV THENC ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  ASM_REWRITE_TAC[I_THM; WORD_ADD_0] THEN DISCARD_STATE_TAC "s904" THEN
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
 (`!a z_01234 z_56 zetas_01234 zetas_56 x pc stackpointer returnaddress.
      aligned 16 stackpointer /\
      ALLPAIRS nonoverlapping
       [(a,512); (word_sub stackpointer (word 64),64)]
       [(word pc,0x504); (z_01234,160); (z_56,768)] /\
      nonoverlapping (a,512) (word_sub stackpointer (word 64),64)
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) mlkem_ntt_mc /\
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
                (zetas_01234 = MAP iword ntt_zetas_layer01234 /\
                 zetas_56 = MAP iword ntt_zetas_layer56 /\
                 (!i. i < 256 ==> abs(ival(x i)) <= &8191)
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
    ONCE_DEPTH_CONV WORDLIST_FROM_MEMORY_CONV THENC
    ONCE_DEPTH_CONV EXPAND_CASES_CONV THENC
    ONCE_DEPTH_CONV NUM_MULT_CONV THENC
    PURE_REWRITE_CONV [WORD_ADD_0] in
  REWRITE_TAC[fst MLKEM_NTT_EXEC] THEN
  CONV_TAC TWEAK_CONV THEN
  ARM_ADD_RETURN_STACK_TAC ~pre_post_nsteps:(5,5) MLKEM_NTT_EXEC
   (REWRITE_RULE[fst MLKEM_NTT_EXEC] (CONV_RULE TWEAK_CONV MLKEM_NTT_CORRECT))
    `[D8; D9; D10; D11; D12; D13; D14; D15]` 64);;


(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let full_spec,public_vars = mk_safety_spec
    (assoc "mlkem_ntt" subroutine_signatures)
    MLKEM_NTT_SUBROUTINE_CORRECT
    MLKEM_NTT_EXEC;;

let MLKEM_NTT_SUBROUTINE_SAFE = time prove
 (`exists f_events.
       forall e a z_01234 z_56 pc stackpointer returnaddress.
           aligned 16 stackpointer /\
           ALLPAIRS nonoverlapping
           [a,512; word_sub stackpointer (word 64),64]
           [word pc,1284; z_01234,160; z_56,768] /\
           nonoverlapping (a,512) (word_sub stackpointer (word 64),64)
           ==> ensures arm
               (\s.
                    aligned_bytes_loaded s (word pc) mlkem_ntt_mc /\
                    read PC s = word pc /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [a; z_01234; z_56] s /\
                    read events s = e)
               (\s.
                    read PC s = returnaddress /\
                    exists e2.
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
  ASSERT_CONCL_TAC full_spec THEN
  PROVE_SAFETY_SPEC ~public_vars:public_vars MLKEM_NTT_EXEC);;
