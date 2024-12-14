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
  0x6d0027e8;       (* arm_STP D8 D9 SP (Immediate_Offset (iword (&0))) *)
  0x6d012fea;       (* arm_STP D10 D11 SP (Immediate_Offset (iword (&16))) *)
  0x6d0237ec;       (* arm_STP D12 D13 SP (Immediate_Offset (iword (&32))) *)
  0x6d033fee;       (* arm_STP D14 D15 SP (Immediate_Offset (iword (&48))) *)
  0x10004b43;       (* arm_ADR X3 (word 2408) *)
  0x91000063;       (* arm_ADD X3 X3 (rvalue (word 0)) *)
  0x10003304;       (* arm_ADR X4 (word 1632) *)
  0x91000084;       (* arm_ADD X4 X4 (rvalue (word 0)) *)
  0x10003145;       (* arm_ADR X5 (word 1576) *)
  0x4e020fe7;       (* arm_DUP_GEN Q7 XZR 16 128 *)
  0x5281a025;       (* arm_MOV W5 (rvalue (word 3329)) *)
  0x4e021ca7;       (* arm_INS_GEN Q7 W5 0 16 *)
  0x5289d7e5;       (* arm_MOV W5 (rvalue (word 20159)) *)
  0x4e061ca7;       (* arm_INS_GEN Q7 W5 16 16 *)
  0x10003105;       (* arm_ADR X5 (word 1568) *)
  0x52804005;       (* arm_MOV W5 (rvalue (word 512)) *)
  0x4e020cbd;       (* arm_DUP_GEN Q29 X5 16 128 *)
  0x10003125;       (* arm_ADR X5 (word 1572) *)
  0x52827605;       (* arm_MOV W5 (rvalue (word 5040)) *)
  0x4e020cbe;       (* arm_DUP_GEN Q30 X5 16 128 *)
  0xaa0003e1;       (* arm_MOV X1 X0 *)
  0xd2800102;       (* arm_MOV X2 (rvalue (word 8)) *)
  0x3dc0042c;       (* arm_LDR Q12 X1 (Immediate_Offset (word 16)) *)
  0x3dc0083f;       (* arm_LDR Q31 X1 (Immediate_Offset (word 32)) *)
  0x3dc00c26;       (* arm_LDR Q6 X1 (Immediate_Offset (word 48)) *)
  0xd1000442;       (* arm_SUB X2 X2 (rvalue (word 1)) *)
  0x3dc0002a;       (* arm_LDR Q10 X1 (Immediate_Offset (word 0)) *)
  0x6e7eb58d;       (* arm_SQRDMULH_VEC Q13 Q12 Q30 16 128 *)
  0x4e7d9d95;       (* arm_MUL_VEC Q21 Q12 Q29 16 128 *)
  0x6e7eb543;       (* arm_SQRDMULH_VEC Q3 Q10 Q30 16 128 *)
  0x4e7d9d4a;       (* arm_MUL_VEC Q10 Q10 Q29 16 128 *)
  0x6e7eb7ec;       (* arm_SQRDMULH_VEC Q12 Q31 Q30 16 128 *)
  0x6f4741b5;       (* arm_MLS_VEC Q21 Q13 Q7 16 128 0 *)
  0x4e7d9fed;       (* arm_MUL_VEC Q13 Q31 Q29 16 128 *)
  0x6f47406a;       (* arm_MLS_VEC Q10 Q3 Q7 16 128 0 *)
  0x6e7eb4c3;       (* arm_SQRDMULH_VEC Q3 Q6 Q30 16 128 *)
  0x4e7d9cc6;       (* arm_MUL_VEC Q6 Q6 Q29 16 128 *)
  0x6f47418d;       (* arm_MLS_VEC Q13 Q12 Q7 16 128 0 *)
  0x3c84042a;       (* arm_STR Q10 X1 (Postimmediate_Offset (iword (&64))) *)
  0x3dc0042c;       (* arm_LDR Q12 X1 (Immediate_Offset (word 16)) *)
  0x3c9d0035;       (* arm_STR Q21 X1 (Immediate_Offset (iword (-- &48))) *)
  0x6f474066;       (* arm_MLS_VEC Q6 Q3 Q7 16 128 0 *)
  0x3c9e002d;       (* arm_STR Q13 X1 (Immediate_Offset (iword (-- &32))) *)
  0x3dc0083f;       (* arm_LDR Q31 X1 (Immediate_Offset (word 32)) *)
  0x3c9f0026;       (* arm_STR Q6 X1 (Immediate_Offset (iword (-- &16))) *)
  0x3dc00c26;       (* arm_LDR Q6 X1 (Immediate_Offset (word 48)) *)
  0xd1000442;       (* arm_SUB X2 X2 (rvalue (word 1)) *)
  0xb5fffd62;       (* arm_CBNZ X2 (word 2097068) *)
  0x6e7eb4c0;       (* arm_SQRDMULH_VEC Q0 Q6 Q30 16 128 *)
  0x4e7d9ccd;       (* arm_MUL_VEC Q13 Q6 Q29 16 128 *)
  0x3dc0002a;       (* arm_LDR Q10 X1 (Immediate_Offset (word 0)) *)
  0x4e7d9ff7;       (* arm_MUL_VEC Q23 Q31 Q29 16 128 *)
  0x6f47400d;       (* arm_MLS_VEC Q13 Q0 Q7 16 128 0 *)
  0x6e7eb544;       (* arm_SQRDMULH_VEC Q4 Q10 Q30 16 128 *)
  0x4e7d9d52;       (* arm_MUL_VEC Q18 Q10 Q29 16 128 *)
  0x6e7eb58a;       (* arm_SQRDMULH_VEC Q10 Q12 Q30 16 128 *)
  0x4e7d9d95;       (* arm_MUL_VEC Q21 Q12 Q29 16 128 *)
  0x6e7eb7e0;       (* arm_SQRDMULH_VEC Q0 Q31 Q30 16 128 *)
  0x6f474092;       (* arm_MLS_VEC Q18 Q4 Q7 16 128 0 *)
  0x3d800c2d;       (* arm_STR Q13 X1 (Immediate_Offset (word 48)) *)
  0x6f474155;       (* arm_MLS_VEC Q21 Q10 Q7 16 128 0 *)
  0x6f474017;       (* arm_MLS_VEC Q23 Q0 Q7 16 128 0 *)
  0x3c840432;       (* arm_STR Q18 X1 (Postimmediate_Offset (iword (&64))) *)
  0x3c9d0035;       (* arm_STR Q21 X1 (Immediate_Offset (iword (-- &48))) *)
  0x3c9e0037;       (* arm_STR Q23 X1 (Immediate_Offset (iword (-- &32))) *)
  0xaa0003e1;       (* arm_MOV X1 X0 *)
  0xd2800102;       (* arm_MOV X2 (rvalue (word 8)) *)
  0x3dc0002a;       (* arm_LDR Q10 X1 (Immediate_Offset (word 0)) *)
  0x3dc00435;       (* arm_LDR Q21 X1 (Immediate_Offset (word 16)) *)
  0x3dc0083f;       (* arm_LDR Q31 X1 (Immediate_Offset (word 32)) *)
  0x3dc00c2c;       (* arm_LDR Q12 X1 (Immediate_Offset (word 48)) *)
  0x3cc60485;       (* arm_LDR Q5 X4 (Postimmediate_Offset (iword (&96))) *)
  0x4e8c2bfe;       (* arm_TRN1 Q30 Q31 Q12 32 128 *)
  0x3cdb0089;       (* arm_LDR Q9 X4 (Immediate_Offset (iword (-- &80))) *)
  0x3cdc008f;       (* arm_LDR Q15 X4 (Immediate_Offset (iword (-- &64))) *)
  0x3cdd0086;       (* arm_LDR Q6 X4 (Immediate_Offset (iword (-- &48))) *)
  0x3cde0099;       (* arm_LDR Q25 X4 (Immediate_Offset (iword (-- &32))) *)
  0x3cdf0094;       (* arm_LDR Q20 X4 (Immediate_Offset (iword (-- &16))) *)
  0xd1000442;       (* arm_SUB X2 X2 (rvalue (word 1)) *)
  0x4e95294d;       (* arm_TRN1 Q13 Q10 Q21 32 128 *)
  0x4e95694a;       (* arm_TRN2 Q10 Q10 Q21 32 128 *)
  0x4e8c6bf5;       (* arm_TRN2 Q21 Q31 Q12 32 128 *)
  0x4ede69a3;       (* arm_TRN2 Q3 Q13 Q30 64 128 *)
  0x4ede29ad;       (* arm_TRN1 Q13 Q13 Q30 64 128 *)
  0x4ed5694c;       (* arm_TRN2 Q12 Q10 Q21 64 128 *)
  0x4ed5294a;       (* arm_TRN1 Q10 Q10 Q21 64 128 *)
  0x6e6c8475;       (* arm_SUB_VEC Q21 Q3 Q12 16 128 *)
  0x4e6c8463;       (* arm_ADD_VEC Q3 Q3 Q12 16 128 *)
  0x6e6a85ac;       (* arm_SUB_VEC Q12 Q13 Q10 16 128 *)
  0x4e6a85ad;       (* arm_ADD_VEC Q13 Q13 Q10 16 128 *)
  0x6e74b6aa;       (* arm_SQRDMULH_VEC Q10 Q21 Q20 16 128 *)
  0x6e66b586;       (* arm_SQRDMULH_VEC Q6 Q12 Q6 16 128 *)
  0x4e6f9d8c;       (* arm_MUL_VEC Q12 Q12 Q15 16 128 *)
  0x4e799eb5;       (* arm_MUL_VEC Q21 Q21 Q25 16 128 *)
  0x6e6385be;       (* arm_SUB_VEC Q30 Q13 Q3 16 128 *)
  0x4e6385ad;       (* arm_ADD_VEC Q13 Q13 Q3 16 128 *)
  0x6f4740cc;       (* arm_MLS_VEC Q12 Q6 Q7 16 128 0 *)
  0x6f474155;       (* arm_MLS_VEC Q21 Q10 Q7 16 128 0 *)
  0x6e69b7ca;       (* arm_SQRDMULH_VEC Q10 Q30 Q9 16 128 *)
  0x4e659fc3;       (* arm_MUL_VEC Q3 Q30 Q5 16 128 *)
  0x3cc10466;       (* arm_LDR Q6 X3 (Postimmediate_Offset (iword (&16))) *)
  0x6e75859e;       (* arm_SUB_VEC Q30 Q12 Q21 16 128 *)
  0x6f474143;       (* arm_MLS_VEC Q3 Q10 Q7 16 128 0 *)
  0x4e75858a;       (* arm_ADD_VEC Q10 Q12 Q21 16 128 *)
  0x6e69b7d5;       (* arm_SQRDMULH_VEC Q21 Q30 Q9 16 128 *)
  0x4e659fcc;       (* arm_MUL_VEC Q12 Q30 Q5 16 128 *)
  0x4e8a29be;       (* arm_TRN1 Q30 Q13 Q10 32 128 *)
  0x4e8a69ad;       (* arm_TRN2 Q13 Q13 Q10 32 128 *)
  0x3dc0102a;       (* arm_LDR Q10 X1 (Immediate_Offset (word 64)) *)
  0x6f4742ac;       (* arm_MLS_VEC Q12 Q21 Q7 16 128 0 *)
  0x3dc01435;       (* arm_LDR Q21 X1 (Immediate_Offset (word 80)) *)
  0x3dc0183f;       (* arm_LDR Q31 X1 (Immediate_Offset (word 96)) *)
  0x4e8c2865;       (* arm_TRN1 Q5 Q3 Q12 32 128 *)
  0x4e8c6863;       (* arm_TRN2 Q3 Q3 Q12 32 128 *)
  0x3dc01c2c;       (* arm_LDR Q12 X1 (Immediate_Offset (word 112)) *)
  0x4ec56bc9;       (* arm_TRN2 Q9 Q30 Q5 64 128 *)
  0x4ec369af;       (* arm_TRN2 Q15 Q13 Q3 64 128 *)
  0x4ec52bde;       (* arm_TRN1 Q30 Q30 Q5 64 128 *)
  0x4ec329ad;       (* arm_TRN1 Q13 Q13 Q3 64 128 *)
  0x6e6f8523;       (* arm_SUB_VEC Q3 Q9 Q15 16 128 *)
  0x6e6d87c5;       (* arm_SUB_VEC Q5 Q30 Q13 16 128 *)
  0x4e6d87cd;       (* arm_ADD_VEC Q13 Q30 Q13 16 128 *)
  0x4f56d87e;       (* arm_SQRDMULHE_VEC Q30 Q3 Q6 16 128 5 *)
  0x4f76d0b9;       (* arm_SQRDMULHE_VEC Q25 Q5 Q6 16 128 3 *)
  0x4f6680a5;       (* arm_MULE_VEC Q5 Q5 Q6 16 128 2 *)
  0x4f468863;       (* arm_MULE_VEC Q3 Q3 Q6 16 128 4 *)
  0x4e6f8529;       (* arm_ADD_VEC Q9 Q9 Q15 16 128 *)
  0x4f57c1af;       (* arm_SQDMULH_VEC Q15 Q13 Q7 16 128 1 *)
  0x6f474325;       (* arm_MLS_VEC Q5 Q25 Q7 16 128 0 *)
  0x6f4743c3;       (* arm_MLS_VEC Q3 Q30 Q7 16 128 0 *)
  0x4f57c13e;       (* arm_SQDMULH_VEC Q30 Q9 Q7 16 128 1 *)
  0x4f1525ef;       (* arm_SRSHR_VEC Q15 Q15 11 16 128 *)
  0x4f57c0b9;       (* arm_SQDMULH_VEC Q25 Q5 Q7 16 128 1 *)
  0x4f57c074;       (* arm_SQDMULH_VEC Q20 Q3 Q7 16 128 1 *)
  0x6f4741ed;       (* arm_MLS_VEC Q13 Q15 Q7 16 128 0 *)
  0x4f1527de;       (* arm_SRSHR_VEC Q30 Q30 11 16 128 *)
  0x4f15272f;       (* arm_SRSHR_VEC Q15 Q25 11 16 128 *)
  0x4f152699;       (* arm_SRSHR_VEC Q25 Q20 11 16 128 *)
  0x6f4743c9;       (* arm_MLS_VEC Q9 Q30 Q7 16 128 0 *)
  0x6f4741e5;       (* arm_MLS_VEC Q5 Q15 Q7 16 128 0 *)
  0x6f474323;       (* arm_MLS_VEC Q3 Q25 Q7 16 128 0 *)
  0x4e8c2bfe;       (* arm_TRN1 Q30 Q31 Q12 32 128 *)
  0x6e6985af;       (* arm_SUB_VEC Q15 Q13 Q9 16 128 *)
  0x4e6985ad;       (* arm_ADD_VEC Q13 Q13 Q9 16 128 *)
  0x6e6384a9;       (* arm_SUB_VEC Q9 Q5 Q3 16 128 *)
  0x4f56d1f9;       (* arm_SQRDMULHE_VEC Q25 Q15 Q6 16 128 1 *)
  0x4f4681ef;       (* arm_MULE_VEC Q15 Q15 Q6 16 128 0 *)
  0x4f56d134;       (* arm_SQRDMULHE_VEC Q20 Q9 Q6 16 128 1 *)
  0x4f468126;       (* arm_MULE_VEC Q6 Q9 Q6 16 128 0 *)
  0x4e6384a3;       (* arm_ADD_VEC Q3 Q5 Q3 16 128 *)
  0x6f47432f;       (* arm_MLS_VEC Q15 Q25 Q7 16 128 0 *)
  0x3c84042d;       (* arm_STR Q13 X1 (Postimmediate_Offset (iword (&64))) *)
  0x6f474286;       (* arm_MLS_VEC Q6 Q20 Q7 16 128 0 *)
  0x3c9d0023;       (* arm_STR Q3 X1 (Immediate_Offset (iword (-- &48))) *)
  0x3cc60485;       (* arm_LDR Q5 X4 (Postimmediate_Offset (iword (&96))) *)
  0x3c9e002f;       (* arm_STR Q15 X1 (Immediate_Offset (iword (-- &32))) *)
  0x3cdb0089;       (* arm_LDR Q9 X4 (Immediate_Offset (iword (-- &80))) *)
  0x3c9f0026;       (* arm_STR Q6 X1 (Immediate_Offset (iword (-- &16))) *)
  0x3cdc008f;       (* arm_LDR Q15 X4 (Immediate_Offset (iword (-- &64))) *)
  0x3cdd0086;       (* arm_LDR Q6 X4 (Immediate_Offset (iword (-- &48))) *)
  0x3cde0099;       (* arm_LDR Q25 X4 (Immediate_Offset (iword (-- &32))) *)
  0x3cdf0094;       (* arm_LDR Q20 X4 (Immediate_Offset (iword (-- &16))) *)
  0xd1000442;       (* arm_SUB X2 X2 (rvalue (word 1)) *)
  0xb5fff582;       (* arm_CBNZ X2 (word 2096816) *)
  0x4e952943;       (* arm_TRN1 Q3 Q10 Q21 32 128 *)
  0x4e8c6bec;       (* arm_TRN2 Q12 Q31 Q12 32 128 *)
  0x4e95694d;       (* arm_TRN2 Q13 Q10 Q21 32 128 *)
  0x4ede287c;       (* arm_TRN1 Q28 Q3 Q30 64 128 *)
  0x4ede6861;       (* arm_TRN2 Q1 Q3 Q30 64 128 *)
  0x4ecc69bf;       (* arm_TRN2 Q31 Q13 Q12 64 128 *)
  0x4ecc29ac;       (* arm_TRN1 Q12 Q13 Q12 64 128 *)
  0x6e7f842a;       (* arm_SUB_VEC Q10 Q1 Q31 16 128 *)
  0x6e6c878d;       (* arm_SUB_VEC Q13 Q28 Q12 16 128 *)
  0x4e6c879e;       (* arm_ADD_VEC Q30 Q28 Q12 16 128 *)
  0x4e799d55;       (* arm_MUL_VEC Q21 Q10 Q25 16 128 *)
  0x4e6f9da3;       (* arm_MUL_VEC Q3 Q13 Q15 16 128 *)
  0x6e66b5ad;       (* arm_SQRDMULH_VEC Q13 Q13 Q6 16 128 *)
  0x6e74b54a;       (* arm_SQRDMULH_VEC Q10 Q10 Q20 16 128 *)
  0x4e7f843f;       (* arm_ADD_VEC Q31 Q1 Q31 16 128 *)
  0x6f4741a3;       (* arm_MLS_VEC Q3 Q13 Q7 16 128 0 *)
  0x6f474155;       (* arm_MLS_VEC Q21 Q10 Q7 16 128 0 *)
  0x6e7f87ca;       (* arm_SUB_VEC Q10 Q30 Q31 16 128 *)
  0x3cc1046f;       (* arm_LDR Q15 X3 (Postimmediate_Offset (iword (&16))) *)
  0x6e75846d;       (* arm_SUB_VEC Q13 Q3 Q21 16 128 *)
  0x6e69b546;       (* arm_SQRDMULH_VEC Q6 Q10 Q9 16 128 *)
  0x4e659d4c;       (* arm_MUL_VEC Q12 Q10 Q5 16 128 *)
  0x4e659daa;       (* arm_MUL_VEC Q10 Q13 Q5 16 128 *)
  0x6e69b5ad;       (* arm_SQRDMULH_VEC Q13 Q13 Q9 16 128 *)
  0x4e758463;       (* arm_ADD_VEC Q3 Q3 Q21 16 128 *)
  0x4e7f87df;       (* arm_ADD_VEC Q31 Q30 Q31 16 128 *)
  0x6f4740cc;       (* arm_MLS_VEC Q12 Q6 Q7 16 128 0 *)
  0x6f4741aa;       (* arm_MLS_VEC Q10 Q13 Q7 16 128 0 *)
  0x4e832bfe;       (* arm_TRN1 Q30 Q31 Q3 32 128 *)
  0x4e836bf5;       (* arm_TRN2 Q21 Q31 Q3 32 128 *)
  0x4e8a698d;       (* arm_TRN2 Q13 Q12 Q10 32 128 *)
  0x4e8a298a;       (* arm_TRN1 Q10 Q12 Q10 32 128 *)
  0x4ecd2aa6;       (* arm_TRN1 Q6 Q21 Q13 64 128 *)
  0x4ecd6aac;       (* arm_TRN2 Q12 Q21 Q13 64 128 *)
  0x4eca2bdf;       (* arm_TRN1 Q31 Q30 Q10 64 128 *)
  0x4eca6bde;       (* arm_TRN2 Q30 Q30 Q10 64 128 *)
  0x6e6687ed;       (* arm_SUB_VEC Q13 Q31 Q6 16 128 *)
  0x4e6687ff;       (* arm_ADD_VEC Q31 Q31 Q6 16 128 *)
  0x6e6c87d5;       (* arm_SUB_VEC Q21 Q30 Q12 16 128 *)
  0x4f7fd1ba;       (* arm_SQRDMULHE_VEC Q26 Q13 Q15 16 128 3 *)
  0x4f6f81a2;       (* arm_MULE_VEC Q2 Q13 Q15 16 128 2 *)
  0x4f4f8aa9;       (* arm_MULE_VEC Q9 Q21 Q15 16 128 4 *)
  0x4f5fdaaa;       (* arm_SQRDMULHE_VEC Q10 Q21 Q15 16 128 5 *)
  0x4f57c3e3;       (* arm_SQDMULH_VEC Q3 Q31 Q7 16 128 1 *)
  0x6f474342;       (* arm_MLS_VEC Q2 Q26 Q7 16 128 0 *)
  0x4e6c87cc;       (* arm_ADD_VEC Q12 Q30 Q12 16 128 *)
  0x6f474149;       (* arm_MLS_VEC Q9 Q10 Q7 16 128 0 *)
  0x4f152463;       (* arm_SRSHR_VEC Q3 Q3 11 16 128 *)
  0x4f57c18a;       (* arm_SQDMULH_VEC Q10 Q12 Q7 16 128 1 *)
  0x4f57c055;       (* arm_SQDMULH_VEC Q21 Q2 Q7 16 128 1 *)
  0x4f57c12d;       (* arm_SQDMULH_VEC Q13 Q9 Q7 16 128 1 *)
  0x6f47407f;       (* arm_MLS_VEC Q31 Q3 Q7 16 128 0 *)
  0x4f15254a;       (* arm_SRSHR_VEC Q10 Q10 11 16 128 *)
  0x4f1526b0;       (* arm_SRSHR_VEC Q16 Q21 11 16 128 *)
  0x4f1525ad;       (* arm_SRSHR_VEC Q13 Q13 11 16 128 *)
  0x6f47414c;       (* arm_MLS_VEC Q12 Q10 Q7 16 128 0 *)
  0x6f474202;       (* arm_MLS_VEC Q2 Q16 Q7 16 128 0 *)
  0x6f4741a9;       (* arm_MLS_VEC Q9 Q13 Q7 16 128 0 *)
  0x6e6c87ea;       (* arm_SUB_VEC Q10 Q31 Q12 16 128 *)
  0x4e6c87e6;       (* arm_ADD_VEC Q6 Q31 Q12 16 128 *)
  0x6e69844d;       (* arm_SUB_VEC Q13 Q2 Q9 16 128 *)
  0x4f4f8143;       (* arm_MULE_VEC Q3 Q10 Q15 16 128 0 *)
  0x4f5fd14c;       (* arm_SQRDMULHE_VEC Q12 Q10 Q15 16 128 1 *)
  0x4f4f81aa;       (* arm_MULE_VEC Q10 Q13 Q15 16 128 0 *)
  0x4f5fd1b5;       (* arm_SQRDMULHE_VEC Q21 Q13 Q15 16 128 1 *)
  0x4e69844d;       (* arm_ADD_VEC Q13 Q2 Q9 16 128 *)
  0x6f474183;       (* arm_MLS_VEC Q3 Q12 Q7 16 128 0 *)
  0x3c840426;       (* arm_STR Q6 X1 (Postimmediate_Offset (iword (&64))) *)
  0x6f4742aa;       (* arm_MLS_VEC Q10 Q21 Q7 16 128 0 *)
  0x3c9d002d;       (* arm_STR Q13 X1 (Immediate_Offset (iword (-- &48))) *)
  0x3c9e0023;       (* arm_STR Q3 X1 (Immediate_Offset (iword (-- &32))) *)
  0x3c9f002a;       (* arm_STR Q10 X1 (Immediate_Offset (iword (-- &16))) *)
  0xd2800082;       (* arm_MOV X2 (rvalue (word 4)) *)
  0x10003223;       (* arm_ADR X3 (word 1604) *)
  0x91000063;       (* arm_ADD X3 X3 (rvalue (word 0)) *)
  0x3cc20460;       (* arm_LDR Q0 X3 (Postimmediate_Offset (iword (&32))) *)
  0x3cdf0061;       (* arm_LDR Q1 X3 (Immediate_Offset (iword (-- &16))) *)
  0x3dc0401f;       (* arm_LDR Q31 X0 (Immediate_Offset (word 256)) *)
  0x3dc05005;       (* arm_LDR Q5 X0 (Immediate_Offset (word 320)) *)
  0x3dc0201e;       (* arm_LDR Q30 X0 (Immediate_Offset (word 128)) *)
  0x4e6587f9;       (* arm_ADD_VEC Q25 Q31 Q5 16 128 *)
  0x3dc06009;       (* arm_LDR Q9 X0 (Immediate_Offset (word 384)) *)
  0x3dc0700f;       (* arm_LDR Q15 X0 (Immediate_Offset (word 448)) *)
  0x3dc0300c;       (* arm_LDR Q12 X0 (Immediate_Offset (word 192)) *)
  0x4e6f8534;       (* arm_ADD_VEC Q20 Q9 Q15 16 128 *)
  0x3dc00003;       (* arm_LDR Q3 X0 (Immediate_Offset (word 0)) *)
  0x4e6c87db;       (* arm_ADD_VEC Q27 Q30 Q12 16 128 *)
  0x4e748738;       (* arm_ADD_VEC Q24 Q25 Q20 16 128 *)
  0x3dc01006;       (* arm_LDR Q6 X0 (Immediate_Offset (word 64)) *)
  0xd1000442;       (* arm_SUB X2 X2 (rvalue (word 1)) *)
  0x6e66846d;       (* arm_SUB_VEC Q13 Q3 Q6 16 128 *)
  0x4e66846a;       (* arm_ADD_VEC Q10 Q3 Q6 16 128 *)
  0x6e6c87d5;       (* arm_SUB_VEC Q21 Q30 Q12 16 128 *)
  0x4f70d9a3;       (* arm_SQRDMULHE_VEC Q3 Q13 Q0 16 128 7 *)
  0x4f6089ad;       (* arm_MULE_VEC Q13 Q13 Q0 16 128 6 *)
  0x6e7b854c;       (* arm_SUB_VEC Q12 Q10 Q27 16 128 *)
  0x4e7b854a;       (* arm_ADD_VEC Q10 Q10 Q27 16 128 *)
  0x4f51d2a6;       (* arm_SQRDMULHE_VEC Q6 Q21 Q1 16 128 1 *)
  0x4f4182b5;       (* arm_MULE_VEC Q21 Q21 Q1 16 128 0 *)
  0x6f47406d;       (* arm_MLS_VEC Q13 Q3 Q7 16 128 0 *)
  0x6e6587e3;       (* arm_SUB_VEC Q3 Q31 Q5 16 128 *)
  0x4f70d19e;       (* arm_SQRDMULHE_VEC Q30 Q12 Q0 16 128 3 *)
  0x4f60818c;       (* arm_MULE_VEC Q12 Q12 Q0 16 128 2 *)
  0x6e78855f;       (* arm_SUB_VEC Q31 Q10 Q24 16 128 *)
  0x4e78854a;       (* arm_ADD_VEC Q10 Q10 Q24 16 128 *)
  0x6f4740d5;       (* arm_MLS_VEC Q21 Q6 Q7 16 128 0 *)
  0x4f71d066;       (* arm_SQRDMULHE_VEC Q6 Q3 Q1 16 128 3 *)
  0x4f618063;       (* arm_MULE_VEC Q3 Q3 Q1 16 128 2 *)
  0x6e6f8525;       (* arm_SUB_VEC Q5 Q9 Q15 16 128 *)
  0x6e7585a9;       (* arm_SUB_VEC Q9 Q13 Q21 16 128 *)
  0x4e7585ad;       (* arm_ADD_VEC Q13 Q13 Q21 16 128 *)
  0x6f4740c3;       (* arm_MLS_VEC Q3 Q6 Q7 16 128 0 *)
  0x4f51d8b5;       (* arm_SQRDMULHE_VEC Q21 Q5 Q1 16 128 5 *)
  0x6f4743cc;       (* arm_MLS_VEC Q12 Q30 Q7 16 128 0 *)
  0x4f4188a6;       (* arm_MULE_VEC Q6 Q5 Q1 16 128 4 *)
  0x4f70d13e;       (* arm_SQRDMULHE_VEC Q30 Q9 Q0 16 128 3 *)
  0x4f608125;       (* arm_MULE_VEC Q5 Q9 Q0 16 128 2 *)
  0x4f50d3e9;       (* arm_SQRDMULHE_VEC Q9 Q31 Q0 16 128 1 *)
  0x4f4083ff;       (* arm_MULE_VEC Q31 Q31 Q0 16 128 0 *)
  0x3c81040a;       (* arm_STR Q10 X0 (Postimmediate_Offset (iword (&16))) *)
  0x6f4742a6;       (* arm_MLS_VEC Q6 Q21 Q7 16 128 0 *)
  0x6f4743c5;       (* arm_MLS_VEC Q5 Q30 Q7 16 128 0 *)
  0x6e74872a;       (* arm_SUB_VEC Q10 Q25 Q20 16 128 *)
  0x6f47413f;       (* arm_MLS_VEC Q31 Q9 Q7 16 128 0 *)
  0x6e668475;       (* arm_SUB_VEC Q21 Q3 Q6 16 128 *)
  0x4f50d95e;       (* arm_SQRDMULHE_VEC Q30 Q10 Q0 16 128 5 *)
  0x4f40894a;       (* arm_MULE_VEC Q10 Q10 Q0 16 128 4 *)
  0x4e668463;       (* arm_ADD_VEC Q3 Q3 Q6 16 128 *)
  0x4f50daa6;       (* arm_SQRDMULHE_VEC Q6 Q21 Q0 16 128 5 *)
  0x4f408ab5;       (* arm_MULE_VEC Q21 Q21 Q0 16 128 4 *)
  0x6f4743ca;       (* arm_MLS_VEC Q10 Q30 Q7 16 128 0 *)
  0x6e6385be;       (* arm_SUB_VEC Q30 Q13 Q3 16 128 *)
  0x4e6385ad;       (* arm_ADD_VEC Q13 Q13 Q3 16 128 *)
  0x6f4740d5;       (* arm_MLS_VEC Q21 Q6 Q7 16 128 0 *)
  0x4f50d3c3;       (* arm_SQRDMULHE_VEC Q3 Q30 Q0 16 128 1 *)
  0x4f4083c6;       (* arm_MULE_VEC Q6 Q30 Q0 16 128 0 *)
  0x6e6a859e;       (* arm_SUB_VEC Q30 Q12 Q10 16 128 *)
  0x4e6a858a;       (* arm_ADD_VEC Q10 Q12 Q10 16 128 *)
  0x6e7584ac;       (* arm_SUB_VEC Q12 Q5 Q21 16 128 *)
  0x6f474066;       (* arm_MLS_VEC Q6 Q3 Q7 16 128 0 *)
  0x4f50d3c3;       (* arm_SQRDMULHE_VEC Q3 Q30 Q0 16 128 1 *)
  0x4f4083de;       (* arm_MULE_VEC Q30 Q30 Q0 16 128 0 *)
  0x4e7584b5;       (* arm_ADD_VEC Q21 Q5 Q21 16 128 *)
  0x4f50d185;       (* arm_SQRDMULHE_VEC Q5 Q12 Q0 16 128 1 *)
  0x4f40818c;       (* arm_MULE_VEC Q12 Q12 Q0 16 128 0 *)
  0x6f47407e;       (* arm_MLS_VEC Q30 Q3 Q7 16 128 0 *)
  0x3d803c1f;       (* arm_STR Q31 X0 (Immediate_Offset (word 240)) *)
  0x3dc00003;       (* arm_LDR Q3 X0 (Immediate_Offset (word 0)) *)
  0x6f4740ac;       (* arm_MLS_VEC Q12 Q5 Q7 16 128 0 *)
  0x3d804c06;       (* arm_STR Q6 X0 (Immediate_Offset (word 304)) *)
  0x3dc01006;       (* arm_LDR Q6 X0 (Immediate_Offset (word 64)) *)
  0x3d805c1e;       (* arm_STR Q30 X0 (Immediate_Offset (word 368)) *)
  0x3dc0201e;       (* arm_LDR Q30 X0 (Immediate_Offset (word 128)) *)
  0x3d806c0c;       (* arm_STR Q12 X0 (Immediate_Offset (word 432)) *)
  0x3dc0300c;       (* arm_LDR Q12 X0 (Immediate_Offset (word 192)) *)
  0x3d800c0d;       (* arm_STR Q13 X0 (Immediate_Offset (word 48)) *)
  0x3dc0401f;       (* arm_LDR Q31 X0 (Immediate_Offset (word 256)) *)
  0x3dc05005;       (* arm_LDR Q5 X0 (Immediate_Offset (word 320)) *)
  0x3dc06009;       (* arm_LDR Q9 X0 (Immediate_Offset (word 384)) *)
  0x3dc0700f;       (* arm_LDR Q15 X0 (Immediate_Offset (word 448)) *)
  0x3d801c0a;       (* arm_STR Q10 X0 (Immediate_Offset (word 112)) *)
  0x4e6587f9;       (* arm_ADD_VEC Q25 Q31 Q5 16 128 *)
  0x4e6f8534;       (* arm_ADD_VEC Q20 Q9 Q15 16 128 *)
  0x3d802c15;       (* arm_STR Q21 X0 (Immediate_Offset (word 176)) *)
  0x4e6c87db;       (* arm_ADD_VEC Q27 Q30 Q12 16 128 *)
  0x4e748738;       (* arm_ADD_VEC Q24 Q25 Q20 16 128 *)
  0xd1000442;       (* arm_SUB X2 X2 (rvalue (word 1)) *)
  0xb5fff662;       (* arm_CBNZ X2 (word 2096844) *)
  0x4e66846e;       (* arm_ADD_VEC Q14 Q3 Q6 16 128 *)
  0x6e74872d;       (* arm_SUB_VEC Q13 Q25 Q20 16 128 *)
  0x6e668463;       (* arm_SUB_VEC Q3 Q3 Q6 16 128 *)
  0x6e7b85dd;       (* arm_SUB_VEC Q29 Q14 Q27 16 128 *)
  0x4f4089bc;       (* arm_MULE_VEC Q28 Q13 Q0 16 128 4 *)
  0x4f50d9aa;       (* arm_SQRDMULHE_VEC Q10 Q13 Q0 16 128 5 *)
  0x4f70d3ad;       (* arm_SQRDMULHE_VEC Q13 Q29 Q0 16 128 3 *)
  0x4f6083b4;       (* arm_MULE_VEC Q20 Q29 Q0 16 128 2 *)
  0x6e6c87d3;       (* arm_SUB_VEC Q19 Q30 Q12 16 128 *)
  0x4f70d87d;       (* arm_SQRDMULHE_VEC Q29 Q3 Q0 16 128 7 *)
  0x6f47415c;       (* arm_MLS_VEC Q28 Q10 Q7 16 128 0 *)
  0x6f4741b4;       (* arm_MLS_VEC Q20 Q13 Q7 16 128 0 *)
  0x4f51d276;       (* arm_SQRDMULHE_VEC Q22 Q19 Q1 16 128 1 *)
  0x4f418277;       (* arm_MULE_VEC Q23 Q19 Q1 16 128 0 *)
  0x4f608866;       (* arm_MULE_VEC Q6 Q3 Q0 16 128 6 *)
  0x6e7c868d;       (* arm_SUB_VEC Q13 Q20 Q28 16 128 *)
  0x6e6f852f;       (* arm_SUB_VEC Q15 Q9 Q15 16 128 *)
  0x6f4742d7;       (* arm_MLS_VEC Q23 Q22 Q7 16 128 0 *)
  0x4f50d1aa;       (* arm_SQRDMULHE_VEC Q10 Q13 Q0 16 128 1 *)
  0x4f4081ad;       (* arm_MULE_VEC Q13 Q13 Q0 16 128 0 *)
  0x6f4743a6;       (* arm_MLS_VEC Q6 Q29 Q7 16 128 0 *)
  0x4f51d9f5;       (* arm_SQRDMULHE_VEC Q21 Q15 Q1 16 128 5 *)
  0x4f4189ef;       (* arm_MULE_VEC Q15 Q15 Q1 16 128 4 *)
  0x6f47414d;       (* arm_MLS_VEC Q13 Q10 Q7 16 128 0 *)
  0x6e7784d0;       (* arm_SUB_VEC Q16 Q6 Q23 16 128 *)
  0x6e6587f9;       (* arm_SUB_VEC Q25 Q31 Q5 16 128 *)
  0x6f4742af;       (* arm_MLS_VEC Q15 Q21 Q7 16 128 0 *)
  0x4f60821e;       (* arm_MULE_VEC Q30 Q16 Q0 16 128 2 *)
  0x4f70d215;       (* arm_SQRDMULHE_VEC Q21 Q16 Q0 16 128 3 *)
  0x4f71d325;       (* arm_SQRDMULHE_VEC Q5 Q25 Q1 16 128 3 *)
  0x4e7b85db;       (* arm_ADD_VEC Q27 Q14 Q27 16 128 *)
  0x4f618339;       (* arm_MULE_VEC Q25 Q25 Q1 16 128 2 *)
  0x6f4742be;       (* arm_MLS_VEC Q30 Q21 Q7 16 128 0 *)
  0x6e788763;       (* arm_SUB_VEC Q3 Q27 Q24 16 128 *)
  0x3d80600d;       (* arm_STR Q13 X0 (Immediate_Offset (word 384)) *)
  0x6f4740b9;       (* arm_MLS_VEC Q25 Q5 Q7 16 128 0 *)
  0x4f50d06c;       (* arm_SQRDMULHE_VEC Q12 Q3 Q0 16 128 1 *)
  0x4f40807f;       (* arm_MULE_VEC Q31 Q3 Q0 16 128 0 *)
  0x4e7784c5;       (* arm_ADD_VEC Q5 Q6 Q23 16 128 *)
  0x4e6f872a;       (* arm_ADD_VEC Q10 Q25 Q15 16 128 *)
  0x6e6f8726;       (* arm_SUB_VEC Q6 Q25 Q15 16 128 *)
  0x6f47419f;       (* arm_MLS_VEC Q31 Q12 Q7 16 128 0 *)
  0x4e6a84a9;       (* arm_ADD_VEC Q9 Q5 Q10 16 128 *)
  0x4f4088d5;       (* arm_MULE_VEC Q21 Q6 Q0 16 128 4 *)
  0x4f50d8c6;       (* arm_SQRDMULHE_VEC Q6 Q6 Q0 16 128 5 *)
  0x3d80401f;       (* arm_STR Q31 X0 (Immediate_Offset (word 256)) *)
  0x6e6a84b6;       (* arm_SUB_VEC Q22 Q5 Q10 16 128 *)
  0x3d801009;       (* arm_STR Q9 X0 (Immediate_Offset (word 64)) *)
  0x6f4740d5;       (* arm_MLS_VEC Q21 Q6 Q7 16 128 0 *)
  0x4f50d2c6;       (* arm_SQRDMULHE_VEC Q6 Q22 Q0 16 128 1 *)
  0x4f4082c3;       (* arm_MULE_VEC Q3 Q22 Q0 16 128 0 *)
  0x4e7c868c;       (* arm_ADD_VEC Q12 Q20 Q28 16 128 *)
  0x6e7587cd;       (* arm_SUB_VEC Q13 Q30 Q21 16 128 *)
  0x4e7587d5;       (* arm_ADD_VEC Q21 Q30 Q21 16 128 *)
  0x6f4740c3;       (* arm_MLS_VEC Q3 Q6 Q7 16 128 0 *)
  0x4f50d1aa;       (* arm_SQRDMULHE_VEC Q10 Q13 Q0 16 128 1 *)
  0x4f4081ad;       (* arm_MULE_VEC Q13 Q13 Q0 16 128 0 *)
  0x3d803015;       (* arm_STR Q21 X0 (Immediate_Offset (word 192)) *)
  0x4e788766;       (* arm_ADD_VEC Q6 Q27 Q24 16 128 *)
  0x3d805003;       (* arm_STR Q3 X0 (Immediate_Offset (word 320)) *)
  0x6f47414d;       (* arm_MLS_VEC Q13 Q10 Q7 16 128 0 *)
  0x3c810406;       (* arm_STR Q6 X0 (Postimmediate_Offset (iword (&16))) *)
  0x3d801c0c;       (* arm_STR Q12 X0 (Immediate_Offset (word 112)) *)
  0x3d806c0d;       (* arm_STR Q13 X0 (Immediate_Offset (word 432)) *)
  0x6d4027e8;       (* arm_LDP D8 D9 SP (Immediate_Offset (iword (&0))) *)
  0x6d412fea;       (* arm_LDP D10 D11 SP (Immediate_Offset (iword (&16))) *)
  0x6d4237ec;       (* arm_LDP D12 D13 SP (Immediate_Offset (iword (&32))) *)
  0x6d433fee;       (* arm_LDP D14 D15 SP (Immediate_Offset (iword (&48))) *)
  0x910103ff;       (* arm_ADD SP SP (rvalue (word 64)) *)
  0xd65f03c0        (* arm_RET X30 *)
]
[1; 13; 191; 78; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 2; 0; 2; 0; 2; 0; 2;
 0; 2; 0; 2; 0; 2; 0; 2; 176; 19; 176; 19; 176; 19; 176; 19; 176; 19; 176;
 19; 176; 19; 176; 19; 114; 252; 114; 252; 53; 251; 53; 251; 219; 0; 219; 0;
 87; 3; 87; 3; 3; 221; 3; 221; 210; 208; 210; 208; 108; 8; 108; 8; 224; 32;
 224; 32; 151; 4; 151; 4; 138; 1; 138; 1; 251; 251; 251; 251; 68; 251; 68;
 251; 46; 45; 46; 45; 38; 15; 38; 15; 111; 216; 111; 216; 102; 209; 102; 209;
 139; 252; 139; 252; 195; 4; 195; 4; 175; 5; 175; 5; 71; 6; 71; 6; 249; 221;
 249; 221; 223; 46; 223; 46; 242; 55; 242; 55; 202; 61; 202; 61; 120; 253;
 120; 253; 55; 250; 55; 250; 200; 2; 200; 2; 170; 2; 170; 2; 22; 231; 22;
 231; 14; 199; 14; 199; 96; 27; 96; 27; 57; 26; 57; 26; 138; 252; 138; 252;
 155; 4; 155; 4; 254; 251; 254; 251; 188; 251; 188; 251; 239; 221; 239; 221;
 85; 45; 85; 45; 141; 216; 141; 216; 3; 214; 3; 214; 42; 2; 42; 2; 137; 251;
 137; 251; 109; 254; 109; 254; 13; 2; 13; 2; 77; 21; 77; 21; 13; 212; 13;
 212; 129; 240; 129; 240; 48; 20; 48; 20; 159; 3; 159; 3; 2; 250; 2; 250;
 205; 1; 205; 1; 98; 250; 98; 250; 165; 35; 165; 35; 5; 197; 5; 197; 186; 17;
 186; 17; 181; 200; 181; 200; 223; 2; 223; 2; 207; 253; 207; 253; 11; 253;
 11; 253; 193; 254; 193; 254; 67; 28; 67; 28; 110; 234; 110; 234; 229; 226;
 229; 226; 188; 243; 188; 243; 95; 3; 95; 3; 206; 4; 206; 4; 44; 2; 44; 2;
 217; 251; 217; 251; 47; 33; 47; 33; 75; 47; 75; 47; 97; 21; 97; 21; 33; 215;
 33; 215; 60; 254; 60; 254; 217; 252; 217; 252; 101; 250; 101; 250; 242; 3;
 242; 3; 159; 238; 159; 238; 249; 224; 249; 224; 211; 200; 211; 200; 214; 38;
 214; 38; 147; 249; 147; 249; 12; 3; 12; 3; 109; 0; 109; 0; 7; 4; 7; 4; 192;
 192; 192; 192; 254; 29; 254; 29; 49; 4; 49; 4; 164; 39; 164; 39; 215; 4;
 215; 4; 137; 254; 137; 254; 12; 5; 12; 5; 208; 249; 208; 249; 164; 47; 164;
 47; 149; 241; 149; 241; 173; 49; 173; 49; 24; 195; 24; 195; 134; 5; 134; 5;
 216; 250; 216; 250; 223; 255; 223; 255; 208; 1; 208; 1; 94; 54; 94; 54; 63;
 205; 63; 205; 187; 254; 187; 254; 215; 17; 215; 17; 127; 253; 127; 253; 224;
 3; 224; 3; 173; 3; 173; 3; 253; 3; 253; 3; 91; 231; 91; 231; 36; 38; 36; 38;
 46; 36; 46; 36; 66; 39; 66; 39; 244; 254; 244; 254; 35; 253; 35; 253; 124;
 3; 124; 3; 85; 252; 85; 252; 178; 245; 178; 245; 209; 227; 209; 227; 76; 34;
 76; 34; 229; 219; 229; 219; 136; 253; 136; 253; 48; 3; 48; 3; 72; 5; 72; 5;
 118; 253; 118; 253; 179; 231; 179; 231; 96; 31; 96; 31; 252; 51; 252; 51; 2;
 231; 2; 231; 130; 2; 130; 2; 72; 252; 72; 252; 4; 6; 4; 6; 141; 249; 141;
 249; 175; 24; 175; 24; 101; 219; 101; 219; 55; 59; 55; 59; 133; 192; 133;
 192; 75; 250; 75; 250; 202; 5; 202; 5; 28; 2; 28; 2; 90; 6; 90; 6; 211; 199;
 211; 199; 252; 56; 252; 56; 195; 20; 195; 20; 133; 62; 133; 62; 250; 4; 250;
 4; 28; 4; 28; 4; 1; 4; 1; 4; 83; 251; 83; 251; 252; 48; 252; 48; 115; 40;
 115; 40; 105; 39; 105; 39; 250; 209; 250; 209; 23; 1; 23; 1; 149; 4; 149; 4;
 23; 255; 23; 255; 155; 2; 155; 2; 186; 10; 186; 10; 26; 45; 26; 45; 11; 247;
 11; 247; 165; 25; 165; 25; 58; 1; 58; 1; 12; 253; 12; 253; 48; 0; 48; 0;
 127; 250; 127; 250; 19; 12; 19; 12; 239; 226; 239; 226; 216; 1; 216; 1; 211;
 201; 211; 201; 37; 6; 37; 6; 76; 0; 76; 0; 181; 254; 181; 254; 223; 254;
 223; 254; 123; 60; 123; 60; 236; 2; 236; 2; 70; 243; 70; 243; 227; 244; 227;
 244; 180; 251; 180; 251; 45; 253; 45; 253; 168; 2; 168; 2; 56; 2; 56; 2;
 180; 213; 180; 213; 51; 228; 51; 228; 37; 26; 37; 26; 215; 21; 215; 21; 17;
 4; 17; 4; 155; 249; 155; 249; 185; 253; 185; 253; 239; 255; 239; 255; 7; 40;
 7; 40; 15; 193; 15; 193; 149; 233; 149; 233; 89; 255; 89; 255; 47; 6; 222;
 60; 203; 252; 111; 224; 75; 5; 26; 52; 0; 0; 0; 0; 199; 253; 31; 234; 194;
 1; 77; 17; 168; 3; 253; 35; 0; 0; 0; 0; 69; 0; 167; 2; 191; 1; 48; 17; 233;
 253; 110; 235; 0; 0; 0; 0; 31; 2; 225; 20; 211; 4; 124; 47; 110; 250; 44;
 201; 0; 0; 0; 0; 227; 252; 91; 225; 203; 250; 191; 204; 65; 4; 223; 41; 0;
 0; 0; 0; 63; 255; 148; 248; 200; 255; 217; 253; 27; 1; 226; 10; 0; 0; 0; 0;
 130; 5; 55; 54; 60; 250; 63; 199; 197; 250; 132; 204; 0; 0; 0; 0; 218; 251;
 43; 215; 114; 3; 234; 33; 216; 254; 158; 244; 0; 0; 0; 0; 64; 6; 133; 61;
 40; 0; 138; 1; 237; 2; 205; 28; 176; 252; 101; 223; 152; 5; 15; 55; 138;
 253; 199; 231; 175; 2; 106; 26; 0; 0; 0; 0];;

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
 (`bytes_loaded s (word (pc + 0x64c)) mlkem_intt_data <=>
   read (memory :> bytes(word (pc + 0x64c),976)) s =
   num_of_bytelist mlkem_intt_data`,
  REWRITE_TAC[bytes_loaded; READ_BYTELIST_EQ_BYTES;
    CONV_RULE (RAND_CONV LENGTH_CONV)
     (AP_TERM `LENGTH:byte list->num` mlkem_intt_data)]);;

let MLKEM_INTT_CORRECT = prove
 (`!a x pc.
      nonoverlapping (word pc,0xa1c) (a,512)
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc)
                 (APPEND mlkem_intt_mc mlkem_intt_data) /\
                read PC s = word (pc + 0x14) /\
                C_ARGUMENTS [a] s /\
                !i. i < 256
                    ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                        x i)
           (\s. read PC s = word(pc + 0x634) /\
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
   `word(pc + 1660):int64 = word_add (word(pc + 0x64c)) (word 48)`) THEN
  ASSUME_TAC(WORD_RULE
   `word(pc + 2428):int64 = word_add (word(pc + 0x64c)) (word 816)`) THEN
  ASSUME_TAC(WORD_RULE
   `word(pc + 2556):int64 = word_add (word(pc + 0x64c)) (word 944)`) THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM BYTES_LOADED_DATA]) THEN
  ABBREV_TAC `wpc:int64 = word(pc + 0x64c)` THEN
  SUBST1_TAC(WORD_RULE `wpc:int64 = word(val wpc + 0)`) THEN
  REWRITE_TAC[mlkem_intt_data] THEN CONV_TAC(LAND_CONV DATA64_CONV) THEN
  REWRITE_TAC[WORD_RULE `word(val x + n) = word_add x (word n)`] THEN
  REWRITE_TAC[bytes_loaded_nil] THEN STRIP_TAC THEN
  SUBGOAL_THEN `nonoverlapping (a:int64,512) (wpc:int64,976)` MP_TAC THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES] THENL
   [EXPAND_TAC "wpc" THEN NONOVERLAPPING_TAC;
    UNDISCH_THEN `word(pc + 0x64c):int64 = wpc` (K ALL_TAC) THEN
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

  MAP_EVERY (fun n -> ARM_STEPS_TAC MLKEM_INTT_EXEC [n] THEN SIMD_SIMPLIFY_TAC)
            (1--1190) THEN
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
  ASM_REWRITE_TAC[I_THM; WORD_ADD_0] THEN DISCARD_STATE_TAC "s1190" THEN
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
          [(word pc,0xa1c); (a,512)] /\
      nonoverlapping (word pc,0xa1c) (a,512)
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
