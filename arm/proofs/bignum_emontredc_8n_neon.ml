(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC
 *)

(* ========================================================================= *)
(* Extended Montgomery reduction of arbitrary bignum.                        *)
(* ========================================================================= *)

(**** print_literal_from_elf "arm/fastmul/bignum_emontredc_8n_neon.o";;
 ****)

let bignum_emontredc_8n_neon_mc =
  define_assert_from_elf "bignum_emontredc_8n_neon_mc" "arm/fastmul/bignum_emontredc_8n_neon.o"
[
  0xa9bf53f3;       (* arm_STP X19 X20 SP (Preimmediate_Offset (iword (-- &16))) *)
  0xa9bf5bf5;       (* arm_STP X21 X22 SP (Preimmediate_Offset (iword (-- &16))) *)
  0xa9bf63f7;       (* arm_STP X23 X24 SP (Preimmediate_Offset (iword (-- &16))) *)
  0xa9bf6bf9;       (* arm_STP X25 X26 SP (Preimmediate_Offset (iword (-- &16))) *)
  0xa9bf73fb;       (* arm_STP X27 X28 SP (Preimmediate_Offset (iword (-- &16))) *)
  0xd342fc00;       (* arm_LSR X0 X0 2 *)
  0xaa0003fa;       (* arm_MOV X26 X0 *)
  0xf100040c;       (* arm_SUBS X12 X0 (rvalue (word 1)) *)
  0x54002843;       (* arm_BCC (word 1288) *)
  0xaa1f03fc;       (* arm_MOV X28 XZR *)
  0xd37be980;       (* arm_LSL X0 X12 5 *)
  0xa9404c31;       (* arm_LDP X17 X19 X1 (Immediate_Offset (iword (&0))) *)
  0xa9415434;       (* arm_LDP X20 X21 X1 (Immediate_Offset (iword (&16))) *)
  0xa9402448;       (* arm_LDP X8 X9 X2 (Immediate_Offset (iword (&0))) *)
  0x3dc00040;       (* arm_LDR Q0 X2 (Immediate_Offset (word 0)) *)
  0xa9412c4a;       (* arm_LDP X10 X11 X2 (Immediate_Offset (iword (&16))) *)
  0x3dc00441;       (* arm_LDR Q1 X2 (Immediate_Offset (word 16)) *)
  0x9b037e24;       (* arm_MUL X4 X17 X3 *)
  0x4e080c82;       (* arm_DUP Q2 X4 *)
  0x4e821804;       (* arm_UZIP1 Q4 Q0 Q2 32 *)
  0x4ea00806;       (* arm_REV64_VEC Q6 Q0 32 *)
  0x4e821847;       (* arm_UZIP1 Q7 Q2 Q2 32 *)
  0x4ea29cc5;       (* arm_MUL_VEC Q5 Q6 Q2 32 *)
  0x6ea028a6;       (* arm_UADDLP Q6 Q5 32 *)
  0x4f6054c6;       (* arm_SHL_VEC Q6 Q6 32 64 *)
  0x2ea480e6;       (* arm_UMLAL Q6 Q7 Q4 32 *)
  0x4e083ccc;       (* arm_UMOV X12 Q6 0 8 *)
  0xab0c0231;       (* arm_ADDS X17 X17 X12 *)
  0x4e183ccd;       (* arm_UMOV X13 Q6 1 8 *)
  0xba0d0273;       (* arm_ADCS X19 X19 X13 *)
  0x4e821824;       (* arm_UZIP1 Q4 Q1 Q2 32 *)
  0x4ea00826;       (* arm_REV64_VEC Q6 Q1 32 *)
  0x4e821847;       (* arm_UZIP1 Q7 Q2 Q2 32 *)
  0x4ea29cc5;       (* arm_MUL_VEC Q5 Q6 Q2 32 *)
  0x6ea028a6;       (* arm_UADDLP Q6 Q5 32 *)
  0x4f6054c6;       (* arm_SHL_VEC Q6 Q6 32 64 *)
  0x2ea480e6;       (* arm_UMLAL Q6 Q7 Q4 32 *)
  0x4e083cce;       (* arm_UMOV X14 Q6 0 8 *)
  0x4e183ccf;       (* arm_UMOV X15 Q6 1 8 *)
  0x9bc87c8c;       (* arm_UMULH X12 X4 X8 *)
  0x9bc97c8d;       (* arm_UMULH X13 X4 X9 *)
  0xba0e0294;       (* arm_ADCS X20 X20 X14 *)
  0x9bca7c8e;       (* arm_UMULH X14 X4 X10 *)
  0xba0f02b5;       (* arm_ADCS X21 X21 X15 *)
  0x9bcb7c8f;       (* arm_UMULH X15 X4 X11 *)
  0x9a1f03f6;       (* arm_ADC X22 XZR XZR *)
  0xab0c0273;       (* arm_ADDS X19 X19 X12 *)
  0xba0d0294;       (* arm_ADCS X20 X20 X13 *)
  0xba0e02b5;       (* arm_ADCS X21 X21 X14 *)
  0x9a0f02d6;       (* arm_ADC X22 X22 X15 *)
  0x9b037e65;       (* arm_MUL X5 X19 X3 *)
  0x4e080ca2;       (* arm_DUP Q2 X5 *)
  0x4e821804;       (* arm_UZIP1 Q4 Q0 Q2 32 *)
  0x4ea00806;       (* arm_REV64_VEC Q6 Q0 32 *)
  0x4e821847;       (* arm_UZIP1 Q7 Q2 Q2 32 *)
  0x4ea29cc5;       (* arm_MUL_VEC Q5 Q6 Q2 32 *)
  0x6ea028a6;       (* arm_UADDLP Q6 Q5 32 *)
  0x4f6054c6;       (* arm_SHL_VEC Q6 Q6 32 64 *)
  0x2ea480e6;       (* arm_UMLAL Q6 Q7 Q4 32 *)
  0x4e083ccc;       (* arm_UMOV X12 Q6 0 8 *)
  0x4e183ccd;       (* arm_UMOV X13 Q6 1 8 *)
  0x4e821824;       (* arm_UZIP1 Q4 Q1 Q2 32 *)
  0x4ea00826;       (* arm_REV64_VEC Q6 Q1 32 *)
  0x4e821847;       (* arm_UZIP1 Q7 Q2 Q2 32 *)
  0x4ea29cc5;       (* arm_MUL_VEC Q5 Q6 Q2 32 *)
  0x6ea028a6;       (* arm_UADDLP Q6 Q5 32 *)
  0x4f6054c6;       (* arm_SHL_VEC Q6 Q6 32 64 *)
  0x2ea480e6;       (* arm_UMLAL Q6 Q7 Q4 32 *)
  0x4e083cce;       (* arm_UMOV X14 Q6 0 8 *)
  0x4e183ccf;       (* arm_UMOV X15 Q6 1 8 *)
  0xab0c0273;       (* arm_ADDS X19 X19 X12 *)
  0x9bc87cac;       (* arm_UMULH X12 X5 X8 *)
  0xba0d0294;       (* arm_ADCS X20 X20 X13 *)
  0x9bc97cad;       (* arm_UMULH X13 X5 X9 *)
  0xba0e02b5;       (* arm_ADCS X21 X21 X14 *)
  0x9bca7cae;       (* arm_UMULH X14 X5 X10 *)
  0xba0f02d6;       (* arm_ADCS X22 X22 X15 *)
  0x9bcb7caf;       (* arm_UMULH X15 X5 X11 *)
  0x9a1f03f7;       (* arm_ADC X23 XZR XZR *)
  0xab0c0294;       (* arm_ADDS X20 X20 X12 *)
  0xba0d02b5;       (* arm_ADCS X21 X21 X13 *)
  0xba0e02d6;       (* arm_ADCS X22 X22 X14 *)
  0x9a0f02f7;       (* arm_ADC X23 X23 X15 *)
  0x9b037e86;       (* arm_MUL X6 X20 X3 *)
  0x4e080cc2;       (* arm_DUP Q2 X6 *)
  0x4e821804;       (* arm_UZIP1 Q4 Q0 Q2 32 *)
  0x4ea00806;       (* arm_REV64_VEC Q6 Q0 32 *)
  0x4e821847;       (* arm_UZIP1 Q7 Q2 Q2 32 *)
  0x4ea29cc5;       (* arm_MUL_VEC Q5 Q6 Q2 32 *)
  0x6ea028a6;       (* arm_UADDLP Q6 Q5 32 *)
  0x4f6054c6;       (* arm_SHL_VEC Q6 Q6 32 64 *)
  0x2ea480e6;       (* arm_UMLAL Q6 Q7 Q4 32 *)
  0x4e083ccc;       (* arm_UMOV X12 Q6 0 8 *)
  0x4e183ccd;       (* arm_UMOV X13 Q6 1 8 *)
  0x4e821824;       (* arm_UZIP1 Q4 Q1 Q2 32 *)
  0x4ea00826;       (* arm_REV64_VEC Q6 Q1 32 *)
  0x4e821847;       (* arm_UZIP1 Q7 Q2 Q2 32 *)
  0x4ea29cc5;       (* arm_MUL_VEC Q5 Q6 Q2 32 *)
  0x6ea028a6;       (* arm_UADDLP Q6 Q5 32 *)
  0x4f6054c6;       (* arm_SHL_VEC Q6 Q6 32 64 *)
  0x2ea480e6;       (* arm_UMLAL Q6 Q7 Q4 32 *)
  0x4e083cce;       (* arm_UMOV X14 Q6 0 8 *)
  0x4e183ccf;       (* arm_UMOV X15 Q6 1 8 *)
  0xab0c0294;       (* arm_ADDS X20 X20 X12 *)
  0x9bc87ccc;       (* arm_UMULH X12 X6 X8 *)
  0xba0d02b5;       (* arm_ADCS X21 X21 X13 *)
  0x9bc97ccd;       (* arm_UMULH X13 X6 X9 *)
  0xba0e02d6;       (* arm_ADCS X22 X22 X14 *)
  0x9bca7cce;       (* arm_UMULH X14 X6 X10 *)
  0xba0f02f7;       (* arm_ADCS X23 X23 X15 *)
  0x9bcb7ccf;       (* arm_UMULH X15 X6 X11 *)
  0x9a1f03f8;       (* arm_ADC X24 XZR XZR *)
  0xab0c02b5;       (* arm_ADDS X21 X21 X12 *)
  0xba0d02d6;       (* arm_ADCS X22 X22 X13 *)
  0xba0e02f7;       (* arm_ADCS X23 X23 X14 *)
  0x9a0f0318;       (* arm_ADC X24 X24 X15 *)
  0x9b037ea7;       (* arm_MUL X7 X21 X3 *)
  0x4e080ce2;       (* arm_DUP Q2 X7 *)
  0x4e821804;       (* arm_UZIP1 Q4 Q0 Q2 32 *)
  0x4ea00806;       (* arm_REV64_VEC Q6 Q0 32 *)
  0x4e821847;       (* arm_UZIP1 Q7 Q2 Q2 32 *)
  0x4ea29cc5;       (* arm_MUL_VEC Q5 Q6 Q2 32 *)
  0x6ea028a6;       (* arm_UADDLP Q6 Q5 32 *)
  0x4f6054c6;       (* arm_SHL_VEC Q6 Q6 32 64 *)
  0x2ea480e6;       (* arm_UMLAL Q6 Q7 Q4 32 *)
  0x4e083ccc;       (* arm_UMOV X12 Q6 0 8 *)
  0x4e183ccd;       (* arm_UMOV X13 Q6 1 8 *)
  0x4e821824;       (* arm_UZIP1 Q4 Q1 Q2 32 *)
  0x4ea00826;       (* arm_REV64_VEC Q6 Q1 32 *)
  0x4e821847;       (* arm_UZIP1 Q7 Q2 Q2 32 *)
  0x4ea29cc5;       (* arm_MUL_VEC Q5 Q6 Q2 32 *)
  0x6ea028a6;       (* arm_UADDLP Q6 Q5 32 *)
  0x4f6054c6;       (* arm_SHL_VEC Q6 Q6 32 64 *)
  0x2ea480e6;       (* arm_UMLAL Q6 Q7 Q4 32 *)
  0x4e083cce;       (* arm_UMOV X14 Q6 0 8 *)
  0x4e183ccf;       (* arm_UMOV X15 Q6 1 8 *)
  0xab0c02b5;       (* arm_ADDS X21 X21 X12 *)
  0x9bc87cec;       (* arm_UMULH X12 X7 X8 *)
  0xba0d02d6;       (* arm_ADCS X22 X22 X13 *)
  0x9bc97ced;       (* arm_UMULH X13 X7 X9 *)
  0xba0e02f7;       (* arm_ADCS X23 X23 X14 *)
  0x9bca7cee;       (* arm_UMULH X14 X7 X10 *)
  0xba0f0318;       (* arm_ADCS X24 X24 X15 *)
  0x9bcb7cef;       (* arm_UMULH X15 X7 X11 *)
  0x9a1f03f9;       (* arm_ADC X25 XZR XZR *)
  0xab0c02cc;       (* arm_ADDS X12 X22 X12 *)
  0xba0d02ed;       (* arm_ADCS X13 X23 X13 *)
  0xba0e030e;       (* arm_ADCS X14 X24 X14 *)
  0x9a0f032f;       (* arm_ADC X15 X25 X15 *)
  0xa9001424;       (* arm_STP X4 X5 X1 (Immediate_Offset (iword (&0))) *)
  0xa9011c26;       (* arm_STP X6 X7 X1 (Immediate_Offset (iword (&16))) *)
  0x3dc00020;       (* arm_LDR Q0 X1 (Immediate_Offset (word 0)) *)
  0x3dc00421;       (* arm_LDR Q1 X1 (Immediate_Offset (word 16)) *)
  0xb4001420;       (* arm_CBZ X0 (word 644) *)
  0xaa0003fb;       (* arm_MOV X27 X0 *)
  0x91008042;       (* arm_ADD X2 X2 (rvalue (word 32)) *)
  0x91008021;       (* arm_ADD X1 X1 (rvalue (word 32)) *)
  0xa9402448;       (* arm_LDP X8 X9 X2 (Immediate_Offset (iword (&0))) *)
  0xa9412c4a;       (* arm_LDP X10 X11 X2 (Immediate_Offset (iword (&16))) *)
  0x3dc00042;       (* arm_LDR Q2 X2 (Immediate_Offset (word 0)) *)
  0x3dc00443;       (* arm_LDR Q3 X2 (Immediate_Offset (word 16)) *)
  0x4e801844;       (* arm_UZIP1 Q4 Q2 Q0 32 *)
  0x4ea00846;       (* arm_REV64_VEC Q6 Q2 32 *)
  0x4e801807;       (* arm_UZIP1 Q7 Q0 Q0 32 *)
  0x4ea09cc5;       (* arm_MUL_VEC Q5 Q6 Q0 32 *)
  0x6ea028a6;       (* arm_UADDLP Q6 Q5 32 *)
  0x4f6054c6;       (* arm_SHL_VEC Q6 Q6 32 64 *)
  0x2ea480e6;       (* arm_UMLAL Q6 Q7 Q4 32 *)
  0x4e083cd1;       (* arm_UMOV X17 Q6 0 8 *)
  0x4e183cd6;       (* arm_UMOV X22 Q6 1 8 *)
  0x9bc87c90;       (* arm_UMULH X16 X4 X8 *)
  0x4e811864;       (* arm_UZIP1 Q4 Q3 Q1 32 *)
  0x4ea00866;       (* arm_REV64_VEC Q6 Q3 32 *)
  0x4e811827;       (* arm_UZIP1 Q7 Q1 Q1 32 *)
  0x4ea19cc5;       (* arm_MUL_VEC Q5 Q6 Q1 32 *)
  0x6ea028a6;       (* arm_UADDLP Q6 Q5 32 *)
  0x4f6054c6;       (* arm_SHL_VEC Q6 Q6 32 64 *)
  0x2ea480e6;       (* arm_UMLAL Q6 Q7 Q4 32 *)
  0x4e083cd7;       (* arm_UMOV X23 Q6 0 8 *)
  0x4e183cd8;       (* arm_UMOV X24 Q6 1 8 *)
  0xab1002d6;       (* arm_ADDS X22 X22 X16 *)
  0x9bc97cb0;       (* arm_UMULH X16 X5 X9 *)
  0xba1002f7;       (* arm_ADCS X23 X23 X16 *)
  0x9bca7cd0;       (* arm_UMULH X16 X6 X10 *)
  0xba100318;       (* arm_ADCS X24 X24 X16 *)
  0x9bcb7cf0;       (* arm_UMULH X16 X7 X11 *)
  0x9a1f0219;       (* arm_ADC X25 X16 XZR *)
  0xa9405434;       (* arm_LDP X20 X21 X1 (Immediate_Offset (iword (&0))) *)
  0xab14018c;       (* arm_ADDS X12 X12 X20 *)
  0xba1501ad;       (* arm_ADCS X13 X13 X21 *)
  0xa9415434;       (* arm_LDP X20 X21 X1 (Immediate_Offset (iword (&16))) *)
  0xba1401ce;       (* arm_ADCS X14 X14 X20 *)
  0xba1501ef;       (* arm_ADCS X15 X15 X21 *)
  0x9a1f03f0;       (* arm_ADC X16 XZR XZR *)
  0xab1102d3;       (* arm_ADDS X19 X22 X17 *)
  0xba1602f6;       (* arm_ADCS X22 X23 X22 *)
  0xba170317;       (* arm_ADCS X23 X24 X23 *)
  0xba180338;       (* arm_ADCS X24 X25 X24 *)
  0x9a1903f9;       (* arm_ADC X25 XZR X25 *)
  0xab1102d4;       (* arm_ADDS X20 X22 X17 *)
  0xba1302f5;       (* arm_ADCS X21 X23 X19 *)
  0xba160316;       (* arm_ADCS X22 X24 X22 *)
  0xba170337;       (* arm_ADCS X23 X25 X23 *)
  0xba1803f8;       (* arm_ADCS X24 XZR X24 *)
  0x9a1903f9;       (* arm_ADC X25 XZR X25 *)
  0xab0c0231;       (* arm_ADDS X17 X17 X12 *)
  0xba0d0273;       (* arm_ADCS X19 X19 X13 *)
  0xba0e0294;       (* arm_ADCS X20 X20 X14 *)
  0xba0f02b5;       (* arm_ADCS X21 X21 X15 *)
  0xba1002d6;       (* arm_ADCS X22 X22 X16 *)
  0xba1f02f7;       (* arm_ADCS X23 X23 XZR *)
  0xba1f0318;       (* arm_ADCS X24 X24 XZR *)
  0x9a1f0339;       (* arm_ADC X25 X25 XZR *)
  0xeb0700cf;       (* arm_SUBS X15 X6 X7 *)
  0xda8f25ef;       (* arm_CNEG X15 X15 Condition_CC *)
  0xda9f23ec;       (* arm_CSETM X12 Condition_CC *)
  0xeb0a016d;       (* arm_SUBS X13 X11 X10 *)
  0xda8d25ad;       (* arm_CNEG X13 X13 Condition_CC *)
  0x9b0d7dee;       (* arm_MUL X14 X15 X13 *)
  0x9bcd7ded;       (* arm_UMULH X13 X15 X13 *)
  0xda8c218c;       (* arm_CINV X12 X12 Condition_CC *)
  0xb100059f;       (* arm_CMN X12 (rvalue (word 1)) *)
  0xca0c01ce;       (* arm_EOR X14 X14 X12 *)
  0xba0e02f7;       (* arm_ADCS X23 X23 X14 *)
  0xca0c01ad;       (* arm_EOR X13 X13 X12 *)
  0xba0d0318;       (* arm_ADCS X24 X24 X13 *)
  0x9a0c0339;       (* arm_ADC X25 X25 X12 *)
  0xeb05008f;       (* arm_SUBS X15 X4 X5 *)
  0xda8f25ef;       (* arm_CNEG X15 X15 Condition_CC *)
  0xda9f23ec;       (* arm_CSETM X12 Condition_CC *)
  0xeb08012d;       (* arm_SUBS X13 X9 X8 *)
  0xda8d25ad;       (* arm_CNEG X13 X13 Condition_CC *)
  0x9b0d7dee;       (* arm_MUL X14 X15 X13 *)
  0x9bcd7ded;       (* arm_UMULH X13 X15 X13 *)
  0xda8c218c;       (* arm_CINV X12 X12 Condition_CC *)
  0xb100059f;       (* arm_CMN X12 (rvalue (word 1)) *)
  0xca0c01ce;       (* arm_EOR X14 X14 X12 *)
  0xba0e0273;       (* arm_ADCS X19 X19 X14 *)
  0xca0c01ad;       (* arm_EOR X13 X13 X12 *)
  0xba0d0294;       (* arm_ADCS X20 X20 X13 *)
  0xba0c02b5;       (* arm_ADCS X21 X21 X12 *)
  0xba0c02d6;       (* arm_ADCS X22 X22 X12 *)
  0xba0c02f7;       (* arm_ADCS X23 X23 X12 *)
  0xba0c0318;       (* arm_ADCS X24 X24 X12 *)
  0x9a0c0339;       (* arm_ADC X25 X25 X12 *)
  0xeb0700af;       (* arm_SUBS X15 X5 X7 *)
  0xda8f25ef;       (* arm_CNEG X15 X15 Condition_CC *)
  0xda9f23ec;       (* arm_CSETM X12 Condition_CC *)
  0xeb09016d;       (* arm_SUBS X13 X11 X9 *)
  0xda8d25ad;       (* arm_CNEG X13 X13 Condition_CC *)
  0x9b0d7dee;       (* arm_MUL X14 X15 X13 *)
  0x9bcd7ded;       (* arm_UMULH X13 X15 X13 *)
  0xda8c218c;       (* arm_CINV X12 X12 Condition_CC *)
  0xb100059f;       (* arm_CMN X12 (rvalue (word 1)) *)
  0xca0c01ce;       (* arm_EOR X14 X14 X12 *)
  0xba0e02d6;       (* arm_ADCS X22 X22 X14 *)
  0xca0c01ad;       (* arm_EOR X13 X13 X12 *)
  0xba0d02f7;       (* arm_ADCS X23 X23 X13 *)
  0xba0c0318;       (* arm_ADCS X24 X24 X12 *)
  0x9a0c0339;       (* arm_ADC X25 X25 X12 *)
  0xeb06008f;       (* arm_SUBS X15 X4 X6 *)
  0xda8f25ef;       (* arm_CNEG X15 X15 Condition_CC *)
  0xda9f23ec;       (* arm_CSETM X12 Condition_CC *)
  0xeb08014d;       (* arm_SUBS X13 X10 X8 *)
  0xda8d25ad;       (* arm_CNEG X13 X13 Condition_CC *)
  0x9b0d7dee;       (* arm_MUL X14 X15 X13 *)
  0x9bcd7ded;       (* arm_UMULH X13 X15 X13 *)
  0xda8c218c;       (* arm_CINV X12 X12 Condition_CC *)
  0xb100059f;       (* arm_CMN X12 (rvalue (word 1)) *)
  0xca0c01ce;       (* arm_EOR X14 X14 X12 *)
  0xba0e0294;       (* arm_ADCS X20 X20 X14 *)
  0xca0c01ad;       (* arm_EOR X13 X13 X12 *)
  0xba0d02b5;       (* arm_ADCS X21 X21 X13 *)
  0xba0c02d6;       (* arm_ADCS X22 X22 X12 *)
  0xba0c02f7;       (* arm_ADCS X23 X23 X12 *)
  0xba0c0318;       (* arm_ADCS X24 X24 X12 *)
  0x9a0c0339;       (* arm_ADC X25 X25 X12 *)
  0xeb07008f;       (* arm_SUBS X15 X4 X7 *)
  0xda8f25ef;       (* arm_CNEG X15 X15 Condition_CC *)
  0xda9f23ec;       (* arm_CSETM X12 Condition_CC *)
  0xeb08016d;       (* arm_SUBS X13 X11 X8 *)
  0xda8d25ad;       (* arm_CNEG X13 X13 Condition_CC *)
  0x9b0d7dee;       (* arm_MUL X14 X15 X13 *)
  0x9bcd7ded;       (* arm_UMULH X13 X15 X13 *)
  0xda8c218c;       (* arm_CINV X12 X12 Condition_CC *)
  0xb100059f;       (* arm_CMN X12 (rvalue (word 1)) *)
  0xca0c01ce;       (* arm_EOR X14 X14 X12 *)
  0xba0e02b5;       (* arm_ADCS X21 X21 X14 *)
  0xca0c01ad;       (* arm_EOR X13 X13 X12 *)
  0xba0d02d6;       (* arm_ADCS X22 X22 X13 *)
  0xba0c02f7;       (* arm_ADCS X23 X23 X12 *)
  0xba0c0318;       (* arm_ADCS X24 X24 X12 *)
  0x9a0c0339;       (* arm_ADC X25 X25 X12 *)
  0xeb0600af;       (* arm_SUBS X15 X5 X6 *)
  0xda8f25ef;       (* arm_CNEG X15 X15 Condition_CC *)
  0xda9f23ec;       (* arm_CSETM X12 Condition_CC *)
  0xeb09014d;       (* arm_SUBS X13 X10 X9 *)
  0xda8d25ad;       (* arm_CNEG X13 X13 Condition_CC *)
  0x9b0d7dee;       (* arm_MUL X14 X15 X13 *)
  0x9bcd7ded;       (* arm_UMULH X13 X15 X13 *)
  0xda8c218c;       (* arm_CINV X12 X12 Condition_CC *)
  0xb100059f;       (* arm_CMN X12 (rvalue (word 1)) *)
  0xca0c01ce;       (* arm_EOR X14 X14 X12 *)
  0xba0e02b5;       (* arm_ADCS X21 X21 X14 *)
  0xca0c01ad;       (* arm_EOR X13 X13 X12 *)
  0xba0d02d6;       (* arm_ADCS X22 X22 X13 *)
  0xba0c02ed;       (* arm_ADCS X13 X23 X12 *)
  0xba0c030e;       (* arm_ADCS X14 X24 X12 *)
  0x9a0c032f;       (* arm_ADC X15 X25 X12 *)
  0xaa1603ec;       (* arm_MOV X12 X22 *)
  0xa9004c31;       (* arm_STP X17 X19 X1 (Immediate_Offset (iword (&0))) *)
  0xa9015434;       (* arm_STP X20 X21 X1 (Immediate_Offset (iword (&16))) *)
  0xf100837b;       (* arm_SUBS X27 X27 (rvalue (word 32)) *)
  0x54ffec41;       (* arm_BNE (word 2096520) *)
  0xa9424c31;       (* arm_LDP X17 X19 X1 (Immediate_Offset (iword (&32))) *)
  0xa9435434;       (* arm_LDP X20 X21 X1 (Immediate_Offset (iword (&48))) *)
  0xab1c039f;       (* arm_CMN X28 X28 *)
  0xba0c0231;       (* arm_ADCS X17 X17 X12 *)
  0xba0d0273;       (* arm_ADCS X19 X19 X13 *)
  0xba0e0294;       (* arm_ADCS X20 X20 X14 *)
  0xba0f02b5;       (* arm_ADCS X21 X21 X15 *)
  0xda9f33fc;       (* arm_CSETM X28 Condition_CS *)
  0xa9024c31;       (* arm_STP X17 X19 X1 (Immediate_Offset (iword (&32))) *)
  0xa9035434;       (* arm_STP X20 X21 X1 (Immediate_Offset (iword (&48))) *)
  0xcb000021;       (* arm_SUB X1 X1 X0 *)
  0xcb000042;       (* arm_SUB X2 X2 X0 *)
  0x91008021;       (* arm_ADD X1 X1 (rvalue (word 32)) *)
  0xf100075a;       (* arm_SUBS X26 X26 (rvalue (word 1)) *)
  0x54ffd861;       (* arm_BNE (word 2095884) *)
  0xcb1c03e0;       (* arm_NEG X0 X28 *)
  0xa8c173fb;       (* arm_LDP X27 X28 SP (Postimmediate_Offset (iword (&16))) *)
  0xa8c16bf9;       (* arm_LDP X25 X26 SP (Postimmediate_Offset (iword (&16))) *)
  0xa8c163f7;       (* arm_LDP X23 X24 SP (Postimmediate_Offset (iword (&16))) *)
  0xa8c15bf5;       (* arm_LDP X21 X22 SP (Postimmediate_Offset (iword (&16))) *)
  0xa8c153f3;       (* arm_LDP X19 X20 SP (Postimmediate_Offset (iword (&16))) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_EMONTREDC_8N_NEON_EXEC = ARM_MK_EXEC_RULE bignum_emontredc_8n_neon_mc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

(*** Lemma to justify zeros in the Montgomery steps ***)

let montgomery_lemma = prove
 (`!w n.
    (n * w + 1 == 0) (mod (2 EXP 64))
    ==> !h l x.
            &2 pow 64 * &h + &l:real =
            &(val (word(x * w):int64)) *
            &(val(word(bigdigit n 0):int64))
            ==> !h' l'. &2 pow 64 * &h' + &(val l'):real = &x + &l
                        ==> val(l':int64) = 0`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN
  REWRITE_TAC[VAL_WORD_ZX_GEN; VAL_WORD; GSYM LOWDIGITS_1; lowdigits] THEN
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM VAL_MOD_REFL] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o AP_TERM `\x. x MOD 2 EXP 64`)) THEN
  REWRITE_TAC[MOD_MULT_ADD; DIMINDEX_128; DIMINDEX_64; MULT_CLAUSES] THEN
  REWRITE_TAC[MOD_MOD_EXP_MIN] THEN
  REWRITE_TAC[ARITH_RULE `MIN 64 64 = 64 /\ MIN 128 64 = 64`] THEN
  CONV_TAC MOD_DOWN_CONV THEN REWRITE_TAC[GSYM CONG; GSYM DIVIDES_MOD] THEN
  POP_ASSUM MP_TAC THEN SPEC_TAC(`2 EXP 64`,`p:num`) THEN
  CONV_TAC NUMBER_RULE);;

(*** Lemmas for the case splits in the ADK blocks ***)

let lemma1 = prove
 (`!(x0:num) x1 (y0:num) y1.
       (if y0 <= y1
        then if x1 <= x0 then word 0 else word 18446744073709551615
        else word_not
         (if x1 <= x0 then word 0 else word 18446744073709551615)):int64 =
   word_neg(word(bitval(y0 <= y1 <=> x0 < x1)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM NOT_LE] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES]) THEN
  CONV_TAC WORD_REDUCE_CONV);;

let lemma2 = prove
 (`!(x0:int64) (x1:int64) (y0:int64) (y1:int64).
        &(val(if val x1 <= val x0 then word_sub x0 x1
              else word_neg (word_sub x0 x1))) *
        &(val(if val y0 <= val y1 then word_sub y1 y0
              else word_neg (word_sub y1 y0))):real =
        --(&1) pow bitval(val y0 <= val y1 <=> val x0 < val x1) *
        (&(val x0) - &(val x1)) * (&(val y1) - &(val y0))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM NOT_LE; WORD_NEG_SUB] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES]) THEN
  REPEAT(FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP (ARITH_RULE
   `~(m:num <= n) ==> n <= m /\ ~(m <= n)`))) THEN
  ASM_SIMP_TAC[VAL_WORD_SUB_CASES; GSYM REAL_OF_NUM_SUB] THEN
  REAL_ARITH_TAC);;

(* A lemma that is useful for extracting a 32-bit field from a 128-bit word. *)
let WORD_128_SUBWORD_SUBWORD_32 = prove(`!y.
      word_subword (word_subword (y:(128)word) (0,64):(64)word) (0,32):(32)word =
        word_subword (y:(128)word) (0,32):(32)word /\
      word_subword (word_subword (y:(128)word) (64,64):(64)word) (0,32):(32)word =
        word_subword (y:(128)word) (64,32):(32)word /\
      word_subword (word_subword (y:(128)word) (0,64):(64)word) (32,32):(32)word =
        word_subword (y:(128)word) (32,32):(32)word /\
      word_subword (word_subword (y:(128)word) (64,64):(64)word) (32,32):(32)word =
        word_subword (y:(128)word) (96,32):(32)word`,
  CONV_TAC WORD_BLAST);;

(* A lemma that is useful for extracting a 32-bit field from a join of two 32-bit words. *)
let WORD_SUBWORD_JOIN_64 = prove(`!(x:(32)word) (y:(32)word).
    word_subword (word_join (x:(32)word) (y:(32)word): (64)word) (0,32) = y /\
    word_subword (word_join (x:(32)word) (y:(32)word): (64)word) (32,32) = x`,
  CONV_TAC WORD_BLAST);;

(* A lemma that is useful for extracting a 64-bit field from a join of two 64-bit words. *)
let WORD_SUBWORD_JOIN_128_64 = prove(`!(x:(64)word) (y:(64)word).
    word_subword (word_join (x:(64)word) (y:(64)word): (128)word) (0,64) = y /\
    word_subword (word_join (x:(64)word) (y:(64)word): (128)word) (64,64) = x`,
  CONV_TAC WORD_BLAST);;

(* A lemma that is useful for extracting a 32-bit field from a join of two 64-bit words. *)
let WORD_SUBWORD_JOIN_128_32 = prove(`!(x:(64)word) (y:(64)word).
    word_subword (word_join (x:(64)word) (y:(64)word): (128)word) (0,32):(32)word =
      word_subword (y:(64)word) (0,32):(32)word /\
    word_subword (word_join (x:(64)word) (y:(64)word): (128)word) (32,32):(32)word =
      word_subword (y:(64)word) (32,32):(32)word /\
    word_subword (word_join (x:(64)word) (y:(64)word): (128)word) (64,32):(32)word =
      word_subword (x:(64)word) (0,32):(32)word /\
    word_subword (word_join (x:(64)word) (y:(64)word): (128)word) (96,32):(32)word =
      word_subword (x:(64)word) (32,32):(32)word`,
  CONV_TAC WORD_BLAST);;

let lemma4 = prove(`!a b c.
    ((a + 2 EXP 32 * (b MOD 2 EXP 32 + c MOD 2 EXP 32)) DIV 2 EXP 32) MOD 2 EXP 32 =
    ((a + 2 EXP 32 * (b + c)) DIV 2 EXP 32) MOD 2 EXP 32`,
  REPEAT STRIP_TAC THEN
  MAP_EVERY (fun (thm, suffix) -> LABEL_TAC ("Ha_" ^ suffix) thm)
    (zip (CONJUNCTS ((MP
      (SPECL [`a:num`; `2 EXP 32:num`] DIVISION) (ARITH_RULE `~(2 EXP 32 = 0)`))))
      ["eq";"lt"]) THEN
  ABBREV_TAC `ahi = a DIV 2 EXP 32` THEN
  ABBREV_TAC `alo = a MOD 2 EXP 32` THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ARITH_RULE
    `(ahi * 2 EXP 32 + alo) + 2 EXP 32 * (b MOD 2 EXP 32 + c MOD 2 EXP 32) =
     (ahi + b MOD 2 EXP 32 + c MOD 2 EXP 32) * 2 EXP 32 + alo`] THEN
  REWRITE_TAC[ARITH_RULE
    `(ahi * 2 EXP 32 + alo) + 2 EXP 32 * (b + c) =
     (ahi + b + c) * 2 EXP 32 + alo`] THEN
  IMP_REWRITE_TAC[DIV_UNIQ] THEN (* (A * 2^32 + B) / 2^32 => A *)
  EXISTS_TAC `(ahi + b MOD 2 EXP 32 + c MOD 2 EXP 32)` THEN SIMP_TAC[] THEN
  EXISTS_TAC `(ahi + b + c)` THEN SIMP_TAC[] THEN
  CONV_TAC MOD_DOWN_CONV THEN SIMP_TAC[]);;

let WORD_MUL_64_DECOMPOSED_32 = prove(`!(x:(64)word) (y:(64)word).
  word_add
    (word_mul (word_zx (word_subword x (0,32):(32)word):(64)word)
              (word_zx (word_subword y (0,32):(32)word):(64)word))
    (word_shl
      (word_add
        (word_zx (word_mul (word_subword y (32,32):(32)word) (word_subword x (0,32):(32)word)))
        (word_zx (word_mul (word_subword y (0,32):(32)word) (word_subword x (32,32):(32)word))))
    32) =
  word_mul x y`,
  REPEAT GEN_TAC THEN
  (* word to num: step 1. x = y to val x = val y *)
  REWRITE_TAC[GSYM VAL_EQ] THEN
  (* step 2. remove all word_* *)
  REWRITE_TAC [VAL_WORD_ADD; VAL_WORD_MUL; VAL_WORD_ZX_GEN; VAL_WORD_SUBWORD;
               VAL_WORD; VAL_WORD_SHL] THEN
  (* step 3. add x, y < 2^64 *)
  ASSUME_TAC (ISPECL [`x:(64)word`] VAL_BOUND) THEN
  ASSUME_TAC (ISPECL [`y:(64)word`] VAL_BOUND) THEN
  RULE_ASSUM_TAC (REWRITE_RULE [DIMINDEX_64]) THEN
  (* step 4. eliminate dimindex (:N) and simplify *)
  REWRITE_TAC[DIMINDEX_32;DIMINDEX_64;DIMINDEX_128;DIV_1;MOD_MOD_REFL;
              MOD_MOD_EXP_MIN;ARITH_RULE `2 EXP 0 = 1`; DIV_1] THEN
  CONV_TAC(DEPTH_CONV NUM_MIN_CONV) THEN
  CONV_TAC MOD_DOWN_CONV THEN
  (* split x into [x0h, x0l], and divide y as well *)
  MAP_EVERY (fun (thm, suffix) -> LABEL_TAC ("Hx" ^ suffix) thm)
    (zip (CONJUNCTS ((MP (SPECL [`(val (x:(64)word)):num`; `2 EXP 32:num`] DIVISION)
      (ARITH_RULE `~(2 EXP 32 = 0)`)))) ["eq";"lt"]) THEN
  ABBREV_TAC `xhi = (val (x:(64)word)) DIV 2 EXP 32` THEN
  ABBREV_TAC `xlo = (val (x:(64)word)) MOD 2 EXP 32` THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY (fun (thm, suffix) -> LABEL_TAC ("Hy" ^ suffix) thm)
    (zip (CONJUNCTS ((MP (SPECL [`(val (y:(64)word)):num`; `2 EXP 32:num`] DIVISION)
      (ARITH_RULE `~(2 EXP 32 = 0)`)))) ["eq";"lt"]) THEN
  ABBREV_TAC `yhi = (val (y:(64)word)) DIV 2 EXP 32` THEN
  ABBREV_TAC `ylo = (val (y:(64)word)) MOD 2 EXP 32` THEN
  ASM_REWRITE_TAC[] THEN
  (* lhs *)
  REWRITE_TAC[LEFT_ADD_DISTRIB; RIGHT_ADD_DISTRIB] THEN
  REWRITE_TAC[
    ARITH_RULE `y1hi * x1hi * 2 EXP 32 = 2 EXP 32 * y1hi * x1hi`;
    ARITH_RULE `(y1hi * 2 EXP 32) * x1hi = 2 EXP 32 * y1hi * x1hi`] THEN
  REWRITE_TAC[MOD_MULT_ADD] THEN
  (* rhs *)
  REWRITE_TAC[MULT_ASSOC; ARITH_RULE `2 EXP 32 * 2 EXP 32 = 2 EXP 64`] THEN
  REWRITE_TAC[GSYM ADD_ASSOC; GSYM MULT_ASSOC] THEN
  REWRITE_TAC[MOD_MULT_ADD] THEN
  (* lhs = rhs *)
  REWRITE_TAC[ARITH_RULE `2 EXP 64 = 2 EXP 32 * 2 EXP 32`] THEN
  REWRITE_TAC[MOD_MULT_MOD] THEN
  REWRITE_TAC[ARITH_RULE `2 EXP 32 * p + 2 EXP 32 * q = 2 EXP 32 * (p + q)`; MOD_MULT_ADD] THEN
  REWRITE_TAC [lemma4] THEN
  REWRITE_TAC [ARITH_RULE
    `(xlo * ylo + 2 EXP 32 * (yhi * xlo + ylo * xhi)) DIV 2 EXP 32 =
      (2 EXP 32 * xhi * ylo + 2 EXP 32 * xlo * yhi + xlo * ylo) DIV 2 EXP 32`]);;

let simplify_128bit_words =
  RULE_ASSUM_TAC (REWRITE_RULE [
      WORD_128_SUBWORD_SUBWORD_32; WORD_SUBWORD_JOIN_64; 
      WORD_SUBWORD_JOIN_128_64; WORD_SUBWORD_JOIN_128_32;
      WORD_MUL_64_DECOMPOSED_32]);;

let simplify_128bit_words_and_preproc_accumulate =
  simplify_128bit_words THEN
  (* Rewrite word_mul x y into the pattern that ACCUMULATE_ARITH_TAC can recognize. *)
  RULE_ASSUM_TAC (REWRITE_RULE [WORD_RULE
      `word_mul (a:(64)word) (b:(64)word) =
       word (0 + val (a:(64)word) * val (b:(64)word))`]);;

let WORD_ADD_ASSOC_CONSTS = prove(
  `!(x:(N)word) n m.
    (word_add (word_add x (word n)) (word m)) = (word_add x (word (n+m)))`,
  CONV_TAC WORD_RULE);;

(* match terms of pattern `read (memory :> bytes64 _) ) = _`. *)
let is_read_memory_bytes64 t =
  if is_eq t
  then begin match lhs t with
    | Comb(Comb (
        Const ("read", _),
        Comb(
          Comb(Const (":>", _),Const("memory", _)),
          Comb(Const ("bytes64", _),_))),_) -> true
    | _ -> false end
  else false;;

let BYTES128_EQ_JOIN64_TAC lhs128 hi64 lo64 =
  let hilo = mk_comb (mk_comb
    (`word_join:(64)word->(64)word->(128)word`,hi64),lo64) in
  SUBGOAL_THEN (mk_eq (lhs128, hilo)) ASSUME_TAC THENL [
    EVERY_ASSUM (fun thm ->
      (*let _ = print_term (concl thm) in
      let t = is_read_memory_bytes64 (concl thm) in
      let _ = printf "  <is_read_bytes64: %b>\n" t in *)
      if is_read_memory_bytes64 (concl thm)
      then REWRITE_TAC[GSYM thm]
      else ALL_TAC) THEN
    REWRITE_TAC[READ_MEMORY_BYTESIZED_SPLIT; WORD_ADD_ASSOC_CONSTS] THEN
    ARITH_TAC;
    ALL_TAC
  ];;

let ARM_NEON_ACCSTEPS_TAC = ARM_GEN_ACCSTEPS_TAC
    (fun _ -> simplify_128bit_words_and_preproc_accumulate);;

let BIGNUM_EMONTREDC_8N_NEON_CORRECT = time prove
 (`!k z m w a n pc.
        nonoverlapping (word pc,1344) (z,8 * 2 * val k) /\
        nonoverlapping (m,8 * val k) (z,8 * 2 * val k)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_emontredc_8n_neon_mc /\
                read PC s = word(pc + 0x14) /\
                C_ARGUMENTS [k; z; m; w] s /\
                bignum_from_memory (z,2 * val k) s = a /\
                bignum_from_memory (m,val k) s = n)
           (\s. read PC s = word(pc + 1320) /\
                (8 divides val k /\
                 (n * val w + 1 == 0) (mod (2 EXP 64))
                 ==> n * bignum_from_memory (z,val k) s + a =
                     2 EXP (64 * val k) *
                     (2 EXP (64 * val k) * val(C_RETURN s) +
                      bignum_from_memory
                        (word_add z (word(8 * val k)),val k) s)))
            (MAYCHANGE [PC; X0; X1; X2; X4; X5; X6; X7; X8; X9; X10; X11;
                        X12; X13; X14; X15; X16; X17; X19; X20;
                        X21; X22; X23; X24; X25; X26; X27; X28] ,,
             MAYCHANGE [Q0; Q1; Q2; Q3; Q4; Q5; Q6; Q7] ,,
             MAYCHANGE [memory :> bytes(z,8 * 2 * val k)] ,,
             MAYCHANGE SOME_FLAGS)`,
  W64_GEN_TAC `k:num` THEN
  MAP_EVERY X_GEN_TAC [`z:int64`; `m:int64`] THEN
  W64_GEN_TAC `w:num` THEN
  MAP_EVERY X_GEN_TAC [`a:num`; `n:num`; `pc:num`] THEN
  REWRITE_TAC[ALL; ALLPAIRS; NONOVERLAPPING_CLAUSES] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  BIGNUM_TERMRANGE_TAC `2 * k` `a:num` THEN
  BIGNUM_TERMRANGE_TAC `k:num` `n:num` THEN
  ABBREV_TAC `k4 = k DIV 4` THEN

  (*** Degenerate k/4 = 0 case ***)

  ASM_CASES_TAC `k4 = 0` THENL
   [UNDISCH_THEN `k4 = 0` SUBST_ALL_TAC THEN
    ARM_SIM_TAC BIGNUM_EMONTREDC_8N_NEON_EXEC (1--4) THEN
    ASM_REWRITE_TAC[VAL_WORD_USHR; NUM_REDUCE_CONV `2 EXP 2`] THEN
    ASM_REWRITE_TAC[DIVIDES_DIV_MULT; MULT_CLAUSES; ARITH_RULE `0 < 1`;
                    DIV_0; ARITH_RULE `k DIV 8 = k DIV 4 DIV 2`] THEN
    ASM_CASES_TAC `k = 0` THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "a" THEN
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES; VAL_WORD_0] THEN
    ASM_REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES; BIGNUM_FROM_MEMORY_TRIVIAL];
    ALL_TAC] THEN

  (*** Restate things in terms of k' = k * k DIV 4 for naturalness ***)

  ABBREV_TAC `k' = 4 * k4` THEN
  ABBREV_TAC `a' = lowdigits a (2 * k')` THEN
  ABBREV_TAC `n' = lowdigits n k'` THEN

  ENSURES_SEQUENCE_TAC `pc + 0x24`
   `\s. read X12 s = word(k4 - 1) /\
        read X26 s = word k4 /\
        read X1 s = z /\
        read X2 s = m /\
        read X3 s = word w /\
        bignum_from_memory (z,2 * k') s = a' /\
        bignum_from_memory (m,k') s = n'` THEN
  CONJ_TAC THENL
   [ARM_SIM_TAC BIGNUM_EMONTREDC_8N_NEON_EXEC (1--4) THEN
    ASM_REWRITE_TAC[VAL_WORD_USHR; NUM_REDUCE_CONV `2 EXP 2`] THEN
    ASM_REWRITE_TAC[ARITH_RULE `n < 1 <=> n = 0`] THEN
    ASM_REWRITE_TAC[WORD_SUB; ARITH_RULE `1 <= n <=> ~(n = 0)`] THEN
    REWRITE_TAC[WORD_RULE `word_sub x z = word_sub y z <=> x = y`] THEN
    ASM_REWRITE_TAC[word_ushr; NUM_REDUCE_CONV `2 EXP 2`] THEN
    MAP_EVERY EXPAND_TAC ["a'"; "n'"; "a"; "n"] THEN
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
    REWRITE_TAC[LOWDIGITS_BIGNUM_FROM_MEMORY] THEN
    MAP_EVERY EXPAND_TAC ["k'"; "k4"] THEN
    CONJ_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
    ALL_TAC] THEN

    (* pc + 0x3e8 = pc + 1000: 250..! -> 330 *)
  ENSURES_SEQUENCE_TAC `pc + 1320`
   `\s. ((n' * w + 1 == 0) (mod (2 EXP 64))
         ==> n' * bignum_from_memory (z,k') s + a' =
           2 EXP (64 * k') *
           (2 EXP (64 * k') * val(read X0 s) +
            bignum_from_memory (word_add z (word (8 * k')),k') s))` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    ARM_SIM_TAC BIGNUM_EMONTREDC_8N_NEON_EXEC [] THEN REWRITE_TAC[IMP_CONJ] THEN
    DISCH_THEN(MP_TAC o SPEC `4` o MATCH_MP (NUMBER_RULE
     `y divides a ==> !x:num. x divides y ==> x divides a`)) THEN
    ANTS_TAC THENL [CONV_TAC DIVIDES_CONV; ALL_TAC] THEN
    ASM_REWRITE_TAC[ONCE_REWRITE_RULE[MULT_SYM] DIVIDES_DIV_MULT] THEN
    ASM_CASES_TAC `k':num = k` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_THEN `k':num = k` SUBST_ALL_TAC THEN
    MAP_EVERY UNDISCH_TAC
     [`lowdigits a (2 * k) = a'`; `lowdigits n k = n'`] THEN
    ASM_SIMP_TAC[LOWDIGITS_SELF]] THEN

  SUBGOAL_THEN
   `nonoverlapping (z,8 * 2 * k') (word pc,1344) /\
    nonoverlapping (z,8 * 2 * k') (m:int64,8 * k')`
  MP_TAC THEN REWRITE_TAC[NONOVERLAPPING_CLAUSES] THENL
   [MAP_EVERY EXPAND_TAC ["k'"; "k4"] THEN
    REPEAT CONJ_TAC THEN NONOVERLAPPING_TAC;
    STRIP_TAC] THEN

  MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN
  EXISTS_TAC
   `MAYCHANGE
     [PC; X0; X1; X2; X4; X5; X6; X7; X8; X9; X10; X11; X12; X13; X14; X15;
      X16; X17; X19; X20; X21; X22; X23; X24; X25; X26; X27; X28] ,,
    MAYCHANGE [Q0; Q1; Q2; Q3; Q4; Q5; Q6; Q7] ,,
    MAYCHANGE [memory :> bytes (z,8 * 2 * k')] ,,
    MAYCHANGE [NF; ZF; CF; VF]` THEN
  CONJ_TAC THENL
   [REPEAT(MATCH_MP_TAC SUBSUMED_SEQ THEN REWRITE_TAC[SUBSUMED_REFL]) THEN
    MAP_EVERY EXPAND_TAC ["k'"; "k4"] THEN SUBSUMED_MAYCHANGE_TAC;
    ALL_TAC] THEN

  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (free_in `a:num`) o concl)) THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (free_in `n:num`) o concl)) THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (free_in `k:num`) o concl)) THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o rev) THEN
  MAP_EVERY SPEC_TAC
    [(`a':num`,`a:num`); (`n':num`,`n:num`); (`k':num`,`k:num`)] THEN
  REPEAT STRIP_TAC THEN
  BIGNUM_TERMRANGE_TAC `2 * k` `a:num` THEN
  BIGNUM_TERMRANGE_TAC `k:num` `n:num` THEN

  (*** Get a basic bound on k and k4 from the nonoverlapping assumptions ***)

  SUBGOAL_THEN `~(k = 0)` ASSUME_TAC THENL
   [EXPAND_TAC "k" THEN REWRITE_TAC[MULT_EQ_0; ARITH_EQ] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN

  MP_TAC(ASSUME
   `nonoverlapping_modulo (2 EXP 64)
     (val(z:int64),8 * 2 * k) (val(m:int64),8 * k)`) THEN
  DISCH_THEN(MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ]
    NONOVERLAPPING_IMP_SMALL_2)) THEN
  ANTS_TAC THENL [UNDISCH_TAC `~(k = 0)` THEN ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `k4 < 2 EXP 58` ASSUME_TAC THENL
   [SIMPLE_ARITH_TAC; ALL_TAC] THEN

  (*** Main loop invariant for "outerloop" ***)

  (* 992 (0x3e0) -> 1312 *)
  ENSURES_WHILE_PUP_TAC `k4:num` `pc + 0x2c` `pc + 1312`
   `\i s. (read X2 s = m /\
           read X3 s = word w /\
           bignum_from_memory (m,k) s = n /\
           read X0 s = word(32 * (k4 - 1)) /\
           read X26 s = word(k4 - i) /\
           read X1 s = word_add z (word(8 * 4 * i)) /\
           bignum_from_memory(word_add z (word(8 * (k + 4 * i))),
                              2 * k - (k + 4 * i)) s =
           highdigits a (k + 4 * i) /\
           ((n * w + 1 == 0) (mod (2 EXP 64))
            ==> 2 EXP (64 * 4 * i) *
                (2 EXP (64 * k) * val(word_neg(read X28 s)) +
                 bignum_from_memory(word_add z (word(8 * 4 * i)),k) s) =
               bignum_from_memory(z,4 * i) s * n + lowdigits a (k + 4 * i))) /\
          (read ZF s <=> i = k4)` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
  [ REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
    MP_TAC(ISPECL [`z:int64`; `2 * k`; `k:num`; `s0:armstate`]
        HIGHDIGITS_BIGNUM_FROM_MEMORY) THEN
    MP_TAC(ISPECL [`z:int64`; `2 * k`; `k:num`; `s0:armstate`]
        LOWDIGITS_BIGNUM_FROM_MEMORY) THEN
    ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    REWRITE_TAC[ARITH_RULE `MIN (2 * k) k = k /\ 2 * k - k = k`] THEN
    REPLICATE_TAC 2 (DISCH_THEN(ASSUME_TAC o SYM)) THEN
    ARM_STEPS_TAC BIGNUM_EMONTREDC_8N_NEON_EXEC (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES; SUB_0; WORD_NEG_0] THEN
    REWRITE_TAC[WORD_ADD_0; MULT_CLAUSES; VAL_WORD_0; ADD_CLAUSES; EXP] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL] THEN
    ASM_REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES; ARITH_RULE `2 * k - k = k`] THEN
    ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN CONV_TAC WORD_RULE;
    ALL_TAC; (*** This is the main loop invariant: save for later ***)
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
    ARM_SIM_TAC BIGNUM_EMONTREDC_8N_NEON_EXEC [1];
    GHOST_INTRO_TAC `ncout:int64` `read X28` THEN
    ARM_SIM_TAC BIGNUM_EMONTREDC_8N_NEON_EXEC (1--2) THEN DISCH_TAC THEN
    ASM_SIMP_TAC[LOWDIGITS_SELF; GSYM MULT_2; WORD_SUB_LZERO] THEN
    REWRITE_TAC[MULT_SYM]] THEN

  (*** Start on the main outer loop invariant, rebase at z + 32 * i = rsi ***)

  X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
  REWRITE_TAC[WORD_RULE
   `word_add z (word (8 * (k + 4 * i))) =
    word_add (word_add z (word(8 * 4 * i))) (word(8 * k))`] THEN
  REWRITE_TAC[WORD_RULE
   `word_add z (word (8 * 4 * (i + 1))) =
    word_add (word_add z (word(8 * 4 * i))) (word(8 * 4))`] THEN
  ABBREV_TAC `z':int64 = word_add z (word (8 * 4 * i))` THEN
  REWRITE_TAC[WORD_RULE
   `word_add (word_add z (word (8 * 4))) (word (8 * k)) =
    word_add z (word (8 * (k + 4)))`] THEN
  REWRITE_TAC[ARITH_RULE `2 * k - (k  + i) = k - i`] THEN

  GHOST_INTRO_TAC `cout:num` `\s. val (word_neg (read X28 s))` THEN
  REWRITE_TAC[VAL_WORD_GALOIS; DIMINDEX_64] THEN
  REWRITE_TAC[WORD_RULE `word_neg x = y <=> x = word_neg y`] THEN

  SUBGOAL_THEN
   `!s. bignum_from_memory(z',k) s =
        lowdigits (bignum_from_memory(z',k+4) s) k`
   (fun th -> REWRITE_TAC[th])
  THENL
   [REWRITE_TAC[LOWDIGITS_BIGNUM_FROM_MEMORY] THEN
    REWRITE_TAC[ARITH_RULE `MIN (k + 4) k = k`];
    ALL_TAC] THEN

  SUBGOAL_THEN
   `!s. bignum_from_memory (z,4 * (i + 1)) s =
        2 EXP (64 * 4 * i) * bignum_from_memory(z',4) s +
        bignum_from_memory(z,4 * i) s`
   (fun th -> REWRITE_TAC[th])
  THENL
   [REWRITE_TAC[ARITH_RULE `4 * (i + 1) = 4 * i + 4`] THEN
    ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_SPLIT];
    ALL_TAC] THEN

  SUBGOAL_THEN
   `!s. bignum_from_memory (word_add z' (word (8 * k)),k - 4 * i) s =
        highdigits a (k + 4 * i) <=>
        highdigits (bignum_from_memory(z',k+4) s) k =
        lowdigits (highdigits a (k + 4 * i)) 4 /\
        bignum_from_memory
         (word_add z' (word (8 * (k + 4))),k - 4 * (i + 1)) s =
        highdigits a (k + 4 * (i + 1))`
   (fun th -> REWRITE_TAC[th])
  THENL
   [GEN_TAC THEN
    REWRITE_TAC[HIGHDIGITS_BIGNUM_FROM_MEMORY; ADD_SUB2] THEN
    SUBGOAL_THEN
     `k - 4 * i = 4 + (k - 4 * (i + 1))`
    SUBST1_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_SPLIT] THEN
    MP_TAC(SPECL [`highdigits a (k + 4 * i)`; `4`]
     (CONJUNCT1 HIGH_LOW_DIGITS)) THEN
    DISCH_THEN(fun th ->
      GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [GSYM th]) THEN
    SIMP_TAC[LEXICOGRAPHIC_EQ; BIGNUM_FROM_MEMORY_BOUND; LOWDIGITS_BOUND] THEN
    REWRITE_TAC[HIGHDIGITS_HIGHDIGITS] THEN
    REWRITE_TAC[ARITH_RULE `(k + 4 * i) + 4 = k + 4 * (i + 1)`] THEN
    REWRITE_TAC[WORD_RULE
     `word_add (word_add z (word (8 * k))) (word (8 * 4)) =
      word_add z (word (8 * (k + 4)))`] THEN
    MATCH_ACCEPT_TAC CONJ_SYM;
    ALL_TAC] THEN

  GHOST_INTRO_TAC `z1:num` `bignum_from_memory(z',k+4)` THEN
  BIGNUM_TERMRANGE_TAC `k + 4` `z1:num` THEN
  GHOST_INTRO_TAC `q1:num` `bignum_from_memory(z,4 * i)` THEN
  BIGNUM_TERMRANGE_TAC `4 * i` `q1:num` THEN
  GLOBALIZE_PRECONDITION_TAC THEN

  ENSURES_SEQUENCE_TAC `pc + 1312`
   `\s. read X2 s = m /\
        read X3 s = word w /\
        bignum_from_memory (m,k) s = n /\
        read X0 s = word (32 * (k4 - 1)) /\
        read X26 s = word (k4 - (i + 1)) /\
        (read ZF s <=> i + 1 = k4) /\
        read X1 s = word_add z' (word (8 * 4)) /\
        bignum_from_memory (word_add z' (word (8 * (k + 4))),k - 4 * (i + 1))
        s =
        highdigits a (k + 4 * (i + 1)) /\
        bignum_from_memory (z,4 * i) s = q1 /\
        ((n * w + 1 == 0) (mod (2 EXP 64))
         ==> 2 EXP (64 * 4) *
             (2 EXP (64 * k) *
              val(word_neg(read X28 s)) +
              bignum_from_memory(word_add z' (word(8 * 4)),k) s) =
             bignum_from_memory(z',4) s * n + 2 EXP (64 * k) * cout + z1)` THEN
  CONJ_TAC THENL
  [ALL_TAC;
    ARM_SIM_TAC BIGNUM_EMONTREDC_8N_NEON_EXEC [] THEN
    DISCH_THEN(fun th ->
     REPEAT(FIRST_X_ASSUM(ASSUME_TAC o C MATCH_MP th))) THEN
    REWRITE_TAC[EXP_ADD; ARITH_RULE
     `64 * 4 * (i + 1) = 64 * 4 * i + 64 * 4`] THEN
    ASM_REWRITE_TAC[GSYM MULT_ASSOC] THEN
    REWRITE_TAC[LEFT_ADD_DISTRIB; GSYM ADD_ASSOC; RIGHT_ADD_DISTRIB] THEN
    REWRITE_TAC[GSYM MULT_ASSOC; EQ_ADD_LCANCEL] THEN
    MP_TAC(SPECL [`z1:num`; `k:num`] (CONJUNCT1 HIGH_LOW_DIGITS)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    ASM_REWRITE_TAC[ARITH_RULE
     `ee * e * c + ee * (e * h + l):num =
      (ee * (e * c + l)) + (ee * e) * h`] THEN
    REWRITE_TAC[GSYM EXP_ADD; GSYM ADD_ASSOC; EQ_ADD_LCANCEL] THEN
    REWRITE_TAC[lowdigits; highdigits; LEFT_ADD_DISTRIB; ADD_ASSOC] THEN
    REWRITE_TAC[ARITH_RULE `64 * 4 * i + 64 * k = 64 * k + 64 * 4 * i`] THEN
    SPEC_TAC(`64 * k + 64 * 4 * i`,`j:num`) THEN
    REWRITE_TAC[EXP_ADD; MOD_MULT_MOD] THEN ARITH_TAC] THEN

  (*** Now discard no-longer-relevant things outside the window ***)

  MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN EXISTS_TAC
   `MAYCHANGE [PC; X0; X1; X2; X4; X5; X6; X7; X8; X9; X10; X11; X12; X13;
     X14; X15; X16; X17; X19; X20; X21; X22; X23; X24; X25; X26; X27; X28] ,,
    MAYCHANGE [Q0; Q1; Q2; Q3; Q4; Q5; Q6; Q7] ,,
    MAYCHANGE [memory :> bytes(z',8 * (k + 4))] ,,
    MAYCHANGE [NF; ZF; CF; VF]` THEN
  CONJ_TAC THENL
   [EXPAND_TAC "z'" THEN SUBSUMED_MAYCHANGE_TAC;
    ALL_TAC] THEN

  SUBGOAL_THEN
   `nonoverlapping (z':int64,8 * (k + 4)) (z,8 * 4 * i) /\
    nonoverlapping (z':int64,8 * (k + 4)) (word pc,1344) /\
    nonoverlapping (z':int64,8 * (k + 4)) (m,8 * k) /\
    nonoverlapping (z':int64,8 * (k + 4))
     (word_add z' (word (8 * (k + 4))),8 * (k - 4 * (i + 1)))`
  MP_TAC THEN REWRITE_TAC[NONOVERLAPPING_CLAUSES] THENL
   [EXPAND_TAC "z'" THEN REPEAT CONJ_TAC THEN NONOVERLAPPING_TAC;
    STRIP_TAC] THEN

  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
  ENSURES_FORGET_COMPONENTS_TAC
   [`memory :> bytes (z,8 * 4 * i)`;
    `memory :>
     bytes (word_add z' (word (8 * (k + 4))),8 * (k - 4 * (i + 1)))`] THEN

  (*** Get the cout < 2 before we forget too much context ***)

  SUBGOAL_THEN `(n * w + 1 == 0) (mod (2 EXP 64)) ==> cout < 2`
  ASSUME_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN
     `2 EXP (64 * 4 * i) * (2 EXP (64 * k) * cout + lowdigits z1 k) <
      2 EXP (64 * 4 * i) * 2 EXP (64 * k) * 2`
    MP_TAC THENL
     [ASM_SIMP_TAC[] THEN MATCH_MP_TAC (ARITH_RULE
       `x < d * e /\ y < e * d ==> x + y < d * e * 2`) THEN
      ASM_SIMP_TAC[LT_MULT2] THEN REWRITE_TAC[GSYM EXP_ADD] THEN
      REWRITE_TAC[LOWDIGITS_BOUND; GSYM LEFT_ADD_DISTRIB];
      DISCH_THEN(MP_TAC o MATCH_MP (ARITH_RULE
       `d * (e * c + l):num < x ==> d * e * c < x`)) THEN
      REWRITE_TAC[LT_MULT_LCANCEL; EXP_EQ_0; ARITH_EQ]];
    ALL_TAC] THEN

  (*** Now forget more things; back up a few steps and forget i as well ***)

  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (free_in `a:num`) o concl)) THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (free_in `z:int64`) o concl)) THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (free_in `q1:num`) o concl)) THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (free_in `r1:num`) o concl)) THEN

  (* 0x3d0 -> 1296 *)
  ENSURES_SEQUENCE_TAC `pc + 1296`
   `\s. read X2 s = word_add m (word(32 * (k4 - 1))) /\
        read X3 s = word w /\
        bignum_from_memory (m,k) s = n /\
        read X0 s = word (32 * (k4 - 1)) /\
        read X26 s = word (k4 - i) /\
        read X1 s = word_add z' (word(32 * (k4 - 1))) /\
        ((n * w + 1 == 0) (mod (2 EXP 64))
         ==> 2 EXP (64 * 4) *
             (2 EXP (64 * k) * val(word_neg (read X28 s)) +
              bignum_from_memory(word_add z' (word(8 * 4)),k) s) =
              bignum_from_memory(z',4) s * n +
              2 EXP (64 * k) * cout + z1)` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    ARM_SIM_TAC BIGNUM_EMONTREDC_8N_NEON_EXEC (1--4) THEN REPEAT CONJ_TAC THENL
     [CONV_TAC WORD_RULE;
      REWRITE_TAC[ARITH_RULE `k - (j + 1) = k - j - 1`] THEN
      GEN_REWRITE_TAC RAND_CONV [WORD_SUB] THEN
      ASM_REWRITE_TAC[ARITH_RULE `1 <= k - j <=> j < k`];
      VAL_INT64_TAC `k4 - i:num` THEN ASM_REWRITE_TAC[VAL_WORD_1] THEN
      UNDISCH_TAC `i:num < k4` THEN ARITH_TAC;
      CONV_TAC WORD_RULE]] THEN

  ABBREV_TAC `wouter:int64 = word (k4 - i)` THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (free_in `i:num`) o concl)) THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o rev) THEN
  MAP_EVERY SPEC_TAC
    [(`z1:num`,`a:num`); (`z':int64`,`z:int64`)] THEN
  REPEAT STRIP_TAC THEN

  SUBGOAL_THEN `4 <= k` ASSUME_TAC THENL
   [SUBST1_TAC(SYM(ASSUME `4 * k4 = k`)) THEN UNDISCH_TAC `~(k4 = 0)` THEN
    ARITH_TAC;
    ALL_TAC] THEN

  (*** The initial Montgomery 4-block ***)

  (* 0x164 -> 612 *)
  ENSURES_SEQUENCE_TAC `pc + 612`
   `\s. read X2 s = m /\
        read X3 s = word w /\
        bignum_from_memory(m,k) s = n /\
        read X0 s = word (32 * (k4 - 1)) /\
        read X26 s = wouter /\
        read X1 s = z /\
        read X28 s = word_neg(word cout) /\
        bignum_from_memory(word_add z (word (8 * 4)),k) s =
        highdigits a 4 /\
        read X4 s = word(bigdigit (bignum_from_memory(z,4) s) 0) /\
        read X5 s = word(bigdigit (bignum_from_memory(z,4) s) 1) /\
        read X6 s = word(bigdigit (bignum_from_memory(z,4) s) 2) /\
        read X7 s = word(bigdigit (bignum_from_memory(z,4) s) 3) /\
        read Q0 s = word_join
          (word(bigdigit (bignum_from_memory(z,4) s) 1):(64)word)
          (word(bigdigit (bignum_from_memory(z,4) s) 0):(64)word):(128)word /\
        read Q1 s = word_join
          (word(bigdigit (bignum_from_memory(z,4) s) 3):(64)word)
          (word(bigdigit (bignum_from_memory(z,4) s) 2):(64)word):(128)word /\
        ((n * w + 1 == 0) (mod (2 EXP 64))
         ==> 2 EXP (64 * 4) *
             bignum_of_wordlist
              [read X12 s; read X13 s; read X14 s; read X15 s] =
             bignum_from_memory(z,4) s * lowdigits n 4 + lowdigits a 4)` THEN
  CONJ_TAC THENL
  [ REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    ENSURES_INIT_TAC "s0" THEN
    SUBGOAL_THEN
     `highdigits (bignum_from_memory(z,k+4) s0) 4 = highdigits a 4`
    MP_TAC THENL
     [ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES]; ALL_TAC] THEN
    REWRITE_TAC[HIGHDIGITS_BIGNUM_FROM_MEMORY; ADD_SUB] THEN
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
    REWRITE_TAC[NUM_REDUCE_CONV `8 * 4`] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN
     `(!i. i < 4
           ==> bigdigit (bignum_from_memory(z,k+4) s0) i = bigdigit a i) /\
      (!i. i < 4
           ==> bigdigit (bignum_from_memory(m,k) s0) i = bigdigit n i)`
    MP_TAC THENL [ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES]; ALL_TAC] THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
     [BIGDIGIT_BIGNUM_FROM_MEMORY] THEN
    SUBGOAL_THEN `!i. i < 4 ==> i < k /\ i < k + 4` MP_TAC THENL
     [UNDISCH_TAC `4 <= k` THEN ARITH_TAC; SIMP_TAC[]] THEN
    DISCH_THEN(K ALL_TAC) THEN
    GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
     [VAL_WORD_GALOIS; DIMINDEX_64; BIGDIGIT_BOUND] THEN
    REWRITE_TAC[] THEN
    CONV_TAC(LAND_CONV(BINOP_CONV EXPAND_CASES_CONV)) THEN
    CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [WORD_ADD_0] THEN
    STRIP_TAC THEN
    (* 78 + 11 -> 151 = 140 + 11 *)
    BYTES128_EQ_JOIN64_TAC `read (memory :> bytes128 m) s0`
        `word (bigdigit n 1):(64)word` `word (bigdigit n 0):(64)word` THEN
    BYTES128_EQ_JOIN64_TAC `read (memory :> bytes128 (word_add m (word 16))) s0`
        `word (bigdigit n 3):(64)word` `word (bigdigit n 2):(64)word` THEN
    ARM_ACCSTEPS_TAC BIGNUM_EMONTREDC_8N_NEON_EXEC (1--7) (1--7) THEN
    ARM_NEON_ACCSTEPS_TAC BIGNUM_EMONTREDC_8N_NEON_EXEC [16] (8--16) THEN (* mov x12, v6.d[0] *)
    ARM_ACCSTEPS_TAC BIGNUM_EMONTREDC_8N_NEON_EXEC [17] (17--17) THEN
    ARM_NEON_ACCSTEPS_TAC BIGNUM_EMONTREDC_8N_NEON_EXEC [18] (18--18) THEN (* mov x13, v6.d[1] *)
    ARM_ACCSTEPS_TAC BIGNUM_EMONTREDC_8N_NEON_EXEC [19] (19--19) THEN
    ARM_NEON_ACCSTEPS_TAC BIGNUM_EMONTREDC_8N_NEON_EXEC [27;28] (20--28) THEN (* mov x14, v6.d[0]; mov x15, v6.d[1] *)
    ARM_ACCSTEPS_TAC BIGNUM_EMONTREDC_8N_NEON_EXEC (29--40) (29--40) THEN
    ARM_NEON_ACCSTEPS_TAC BIGNUM_EMONTREDC_8N_NEON_EXEC [49;50;58;59] (41--59) THEN
    ARM_ACCSTEPS_TAC BIGNUM_EMONTREDC_8N_NEON_EXEC (60--73) (60--73) THEN
    ARM_NEON_ACCSTEPS_TAC BIGNUM_EMONTREDC_8N_NEON_EXEC [82;83;91;92] (74--92) THEN
    ARM_ACCSTEPS_TAC BIGNUM_EMONTREDC_8N_NEON_EXEC (93--106) (93--106) THEN
    ARM_NEON_ACCSTEPS_TAC BIGNUM_EMONTREDC_8N_NEON_EXEC [115;116;124;125] (107--125) THEN
    ARM_ACCSTEPS_TAC BIGNUM_EMONTREDC_8N_NEON_EXEC (126--140) (126--140) THEN
    (* Prepare ldr q0/q1 *)
    BYTES128_EQ_JOIN64_TAC `read (memory :> bytes128 (word_add z (word 16))) s140`
        `word (0 + val (sum_s102:(64)word) * w):(64)word`
        `word (0 + val (sum_s69:(64)word) * w):(64)word` THEN
    BYTES128_EQ_JOIN64_TAC `read (memory :> bytes128 z) s140`
        `word (0 + val (sum_s36:(64)word) * w):(64)word`
        `word (0 + val (word (bigdigit a 0):(64)word) * w):(64)word` THEN
    ARM_ACCSTEPS_TAC BIGNUM_EMONTREDC_8N_NEON_EXEC (141--142) (141--142) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
    REWRITE_TAC[BIGDIGIT_BIGNUM_FROM_MEMORY] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_LT_CONV) THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
    ASM_REWRITE_TAC[WORD_VAL; WORD_ADD_0] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES]) THEN
    DISCH_TAC THEN CONV_TAC(ONCE_DEPTH_CONV BIGNUM_EXPAND_CONV) THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[RAND_CONV(TOP_DEPTH_CONV num_CONV) `lowdigits x 4`] THEN
    REWRITE_TAC[ADD1; LOWDIGITS_CLAUSES] THEN
    CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN REWRITE_TAC[bignum_of_wordlist] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP montgomery_lemma) THEN
    DISCH_THEN(fun ith ->
      EVERY_ASSUM(fun th ->
        try let th' = MATCH_MP ith th in
            EVERY_ASSUM(fun th'' ->
              try MP_TAC(MATCH_MP th' th'')
              with Failure _ -> ALL_TAC)
        with Failure _ -> ALL_TAC)) THEN
    REWRITE_TAC[IMP_IMP; GSYM CONJ_ASSOC] THEN
    DISCH_THEN(fun th -> ASSUME_TAC th THEN MP_TAC th) THEN
    DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN
     (MP_TAC o MATCH_MP (MESON[REAL_ADD_LID]
        `n = 0 ==> !x:real. &n + x = x`))) THEN
    REPEAT(DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))) THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    REWRITE_TAC[VAL_WORD_BIGDIGIT] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
  ALL_TAC] THEN

  (*** Shared tail to handle the final carry chaining in k4 = 1 too ***)

  GHOST_INTRO_TAC `q:num` `bignum_from_memory(z,4)` THEN
  BIGNUM_TERMRANGE_TAC `4` `q:num` THEN

  (*** Set up a version with the whole z buffer ***)

  (* 3a8 = 936 -> 1256 *)
  ENSURES_SEQUENCE_TAC `pc + 1256`
   `\s. read X1 s = word_add z (word (32 * (k4 - 1))) /\
        read X2 s = word_add m (word (32 * (k4 - 1))) /\
        read X3 s = word w /\
        bignum_from_memory(m,k) s = n /\
        read X0 s = word (32 * (k4 - 1)) /\
        read X26 s = wouter /\
        read X28 s = word_neg(word cout) /\
        bignum_from_memory (word_add z (word (8 * k)),4) s =
        highdigits a k /\
        bignum_from_memory (z,4) s = q /\
        ((n * w + 1 == 0) (mod (2 EXP 64))
         ==> 2 EXP (64 * k) *
             bignum_of_wordlist
              [read X12 s; read X13 s; read X14 s; read X15 s] +
             bignum_from_memory(z,k) s =
             q * n + lowdigits a k + q)` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    GHOST_INTRO_TAC `g8:int64` `read X12` THEN
    GHOST_INTRO_TAC `g9:int64` `read X13` THEN
    GHOST_INTRO_TAC `g10:int64` `read X14` THEN
    GHOST_INTRO_TAC `g11:int64` `read X15` THEN

    (*** Rebase once again to avoid indexing messiness a bit ***)

    ABBREV_TAC `z':int64 = word_add z (word (8 * k))` THEN
    MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN EXISTS_TAC
     `MAYCHANGE
       [PC; X0; X1; X2; X4; X5; X6; X7; X8; X9; X10; X11; X12; X13; X14; X15;
        X16; X17; X19; X20; X21; X22; X23; X24; X25; X26; X27; X28] ,,
      MAYCHANGE [Q0; Q1; Q2; Q3; Q4; Q5; Q6; Q7] ,,
      MAYCHANGE [memory :> bytes (z',8 * 4)] ,,
      MAYCHANGE [NF; ZF; CF; VF]` THEN
    CONJ_TAC THENL
     [REPEAT(MATCH_MP_TAC SUBSUMED_SEQ THEN REWRITE_TAC[SUBSUMED_REFL]) THEN
      MAP_EVERY EXPAND_TAC ["z'"] THEN SUBSUMED_MAYCHANGE_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `nonoverlapping (z':int64,8 * 4) (word pc,1344) /\
      nonoverlapping (z':int64,8 * 4) (m,8 * k) /\
      nonoverlapping (z':int64,8 * 4) (z,8 * 4) /\
      nonoverlapping (z':int64,8 * 4) (z,8 * k)`
    MP_TAC THEN REWRITE_TAC[NONOVERLAPPING_CLAUSES] THENL
     [MAP_EVERY EXPAND_TAC ["z'"] THEN
      REPEAT CONJ_TAC THEN NONOVERLAPPING_TAC;
      STRIP_TAC] THEN

    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
    SUBGOAL_THEN
     `!j. j < 4
          ==> bigdigit (bignum_from_memory(z',4) s0) j =
              bigdigit a (k + j)`
    MP_TAC THENL
     [ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; BIGDIGIT_HIGHDIGITS];
      SIMP_TAC[BIGDIGIT_BIGNUM_FROM_MEMORY]] THEN
    GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
     [VAL_WORD_GALOIS; DIMINDEX_64; BIGDIGIT_BOUND; GSYM WORD_ADD_ASSOC;
      GSYM WORD_ADD] THEN
    REWRITE_TAC[] THEN CONV_TAC(LAND_CONV EXPAND_CASES_CONV) THEN
    CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
    DISCH_THEN(STRIP_ASSUME_TAC o REWRITE_RULE[ADD_CLAUSES; WORD_ADD_0]) THEN
    SUBGOAL_THEN
     `word_add z (word (32 * (k4 - 1) + 32)):int64 = z' /\
      word_add z (word (32 * (k4 - 1) + 40)):int64 = word_add z' (word 8) /\
      word_add z (word (32 * (k4 - 1) + 48)):int64 = word_add z' (word 16) /\
      word_add z (word (32 * (k4 - 1) + 56)):int64 = word_add z' (word 24) /\
      word_add (word_add z (word (32 * (k4 - 1)))) (word 32):int64 =
      z' /\
      word_add (word_add z (word (32 * (k4 - 1)))) (word 48):int64 =
      word_add z' (word 16)`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[GSYM WORD_ADD; GSYM WORD_ADD_ASSOC] THEN
      SUBST1_TAC(SYM(ASSUME `word_add z (word (8 * k)):int64 = z'`)) THEN
      SUBGOAL_THEN `8 * k = 32 * (k4 - 1) + 32` SUBST1_TAC THENL
       [MAP_EVERY UNDISCH_TAC [`4 * k4 = k`; `~(k4 = 0)`] THEN ARITH_TAC;
        CONV_TAC WORD_RULE];
      ALL_TAC] THEN
    ARM_ACCSTEPS_TAC BIGNUM_EMONTREDC_8N_NEON_EXEC (4--7) (1--10) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN

    DISCH_THEN(fun th ->
      REPEAT(FIRST_X_ASSUM(ASSUME_TAC o C MATCH_MP th)) THEN
      ASSUME_TAC th) THEN
    ABBREV_TAC `bout <=> ~(word cout:int64 = word 0)` THEN
    SUBGOAL_THEN `cout = bitval bout` SUBST_ALL_TAC THENL
     [EXPAND_TAC "bout" THEN UNDISCH_TAC `cout < 2` THEN
      SPEC_TAC(`cout:num`,`c:num`) THEN
      CONV_TAC EXPAND_CASES_CONV THEN
      CONV_TAC WORD_REDUCE_CONV THEN REWRITE_TAC[BITVAL_CLAUSES];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `bitval
       (2 EXP 64 <=
        val (word_neg(word (bitval bout):int64)) +
        val (word_neg(word (bitval bout):int64))) =
      bitval bout`
    SUBST_ALL_TAC THENL
     [POP_ASSUM_LIST(K ALL_TAC) THEN AP_TERM_TAC THEN
      BOOL_CASES_TAC `bout:bool` THEN
      REWRITE_TAC[BITVAL_CLAUSES] THEN CONV_TAC WORD_REDUCE_CONV THEN
      CONV_TAC NUM_REDUCE_CONV;
      REWRITE_TAC[WORD_UNMASK_64; WORD_NEG_NEG; VAL_WORD_BITVAL]] THEN
    MP_TAC(SPECL [`a:num`; `k:num`] (CONJUNCT1 HIGH_LOW_DIGITS)) THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
     (ARITH_RULE
       `z = q * n + a + q
        ==> x + q = z + b + h
            ==> x = q * n + b + h + a`)) THEN
    SUBST1_TAC(SYM(ASSUME `read (memory :> bytes (z,8 * 4)) s10 = q`)) THEN
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
    REWRITE_TAC[LEFT_ADD_DISTRIB; GSYM ADD_ASSOC] THEN
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_SPLIT] THEN
    ONCE_REWRITE_TAC[MESON[ADD_SYM]
     `bignum_from_memory (z,4 + k) = bignum_from_memory (z,k + 4)`] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_SPLIT] THEN
    GEN_REWRITE_TAC RAND_CONV [ARITH_RULE `a + b + c:num = (a + c) + b`] THEN
    REWRITE_TAC[EQ_ADD_RCANCEL; ADD_ASSOC] THEN
    ONCE_REWRITE_TAC[ARITH_RULE `a * b * c:num = b * a * c`] THEN
    REWRITE_TAC[GSYM LEFT_ADD_DISTRIB; VAL_WORD_BITVAL] THEN
    AP_TERM_TAC THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_EXPAND_CONV) THEN
    ASM_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[WORD_ADD; WORD_ADD_ASSOC] THEN
    REPLICATE_TAC 4
     (GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [HIGHDIGITS_STEP]) THEN
    REWRITE_TAC[GSYM ADD_ASSOC] THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
    ASM_SIMP_TAC[HIGHDIGITS_ZERO] THEN
    REWRITE_TAC[bignum_of_wordlist] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    REWRITE_TAC[VAL_WORD_BIGDIGIT] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC] THEN

  (*** The semi-degenerate case where we skip the inner loop ***)

  ASM_CASES_TAC `k4 = 1` THENL
   [UNDISCH_THEN `k4 = 1` SUBST_ALL_TAC THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o MATCH_MP (ARITH_RULE
     `4 * 1 = k ==> k = 4`)) THEN
    ARM_SIM_TAC BIGNUM_EMONTREDC_8N_NEON_EXEC [1] THEN
    ASM_SIMP_TAC[LOWDIGITS_SELF] THEN REWRITE_TAC[GSYM ADD_ASSOC] THEN
    CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_RULE;
    ALL_TAC] THEN

  (*** Setup of the inner loop "maddloop" ***)

  (* 0x16c -> 620, 0x3a4 -> 1252 *)
  ENSURES_WHILE_PAUP_TAC `1` `k4:num` `pc + 620` `pc + 1252`
   `\i s. (read X1 s = word_sub (word_add z (word(32 * i))) (word 32) /\
           read X2 s = word_sub (word_add m (word(32 * i))) (word 32) /\
           read X3 s = word w /\
           bignum_from_memory(m,k) s = n /\
           read X0 s = word (32 * (k4 - 1)) /\
           read X26 s = wouter /\
           read X28 s = word_neg(word cout) /\
           bignum_from_memory (z,4) s = q /\
           read X4 s = word (bigdigit q 0) /\
           read X5 s = word (bigdigit q 1) /\
           read X6 s = word (bigdigit q 2) /\
           read X7 s = word (bigdigit q 3) /\
           read Q0 s = word_join
              (word (bigdigit q 1):(64)word)
              (word (bigdigit q 0):(64)word):(128)word /\
           read Q1 s = word_join
              (word (bigdigit q 3):(64)word)
              (word (bigdigit q 2):(64)word):(128)word /\
           read X27 s = word (32 * (k4 - i)) /\
           bignum_from_memory (word_add z (word (8 * 4 * i)),
                               (k + 4) - 4 * i) s =
           highdigits a (4 * i) /\
           ((n * w + 1 == 0) (mod (2 EXP 64))
            ==> 2 EXP (64 * 4 * i) *
                bignum_of_wordlist
                [read X12 s; read X13 s; read X14 s; read X15 s] +
                bignum_from_memory(z,4 * i) s =
                q * lowdigits n (4 * i) + lowdigits a (4 * i) + q)) /\
          (read ZF s <=> i = k4)` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[ARITH_RULE `1 < k <=> ~(k = 0) /\ ~(k = 1)`];

    SUBGOAL_THEN `~(val(word (32 * (k4 - 1)):int64) = 0)` ASSUME_TAC THENL
     [VAL_INT64_TAC `32 * (k4 - 1)` THEN ASM_REWRITE_TAC[] THEN
      MAP_EVERY UNDISCH_TAC [`~(k4 = 0)`; `~(k4 = 1)`] THEN ARITH_TAC;
      ALL_TAC] THEN
    ARM_SIM_TAC BIGNUM_EMONTREDC_8N_NEON_EXEC (1--2) THEN
    ASM_REWRITE_TAC[MULT_CLAUSES; ADD_SUB] THEN
    ASM_REWRITE_TAC[ADD_ASSOC; EQ_ADD_RCANCEL] THEN
    CONV_TAC WORD_RULE;

    ALL_TAC; (*** The main loop invariant preservation ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
    ARM_SIM_TAC BIGNUM_EMONTREDC_8N_NEON_EXEC [1];

    ARM_SIM_TAC BIGNUM_EMONTREDC_8N_NEON_EXEC [1] THEN
    ASM_SIMP_TAC[LOWDIGITS_SELF] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ADD_SUB2]) THEN
    ASM_REWRITE_TAC[] THEN

    REWRITE_TAC[LEFT_SUB_DISTRIB; WORD_SUB] THEN
    ASM_REWRITE_TAC[ARITH_RULE `32 * 1 <= 32 * k4 <=> ~(k4 = 0)`] THEN
    SUBST1_TAC(SYM(ASSUME `4 * k4 = k`)) THEN CONV_TAC WORD_RULE] THEN

 (*** launch into the inner loop, but for simplicity localize our window ***)

  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  SUBGOAL_THEN `4 * i < k` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`i:num < k4`; `4 * k4 = k`] THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `(k + 4) - 4 * (i + 1) = k - 4 * i`] THEN

  ABBREV_TAC `z':int64 = word_add z (word (32 * i))` THEN
  ABBREV_TAC `m':int64 = word_add m (word (32 * i))` THEN
  REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
  REWRITE_TAC[ARITH_RULE `4 * (i + 1) = 4 * i + 4`] THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_SPLIT] THEN
  REWRITE_TAC[ARITH_RULE `4 * i + 4 = 4 * (i + 1)`] THEN
  ASM_REWRITE_TAC[WORD_RULE
   `word_add z (word (8 * 4 * i)) = word_add z (word(32 * i))`] THEN

  SUBGOAL_THEN
   `ALL (nonoverlapping (z':int64,32))
        [(z,32); (z,8 * 4 * i); (m,8 * k); (word pc,1344);
         (m',32); (word_add z (word (32 * (i + 1))),8 * (k - 4 * i))]`
  MP_TAC THEN REWRITE_TAC[ALL; NONOVERLAPPING_CLAUSES] THENL
   [MAP_EVERY EXPAND_TAC ["z'"; "m'"] THEN
    REPEAT CONJ_TAC THEN NONOVERLAPPING_TAC;
    STRIP_TAC] THEN

  MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN EXISTS_TAC
   `MAYCHANGE
       [PC; X0; X1; X2; X4; X5; X6; X7; X8; X9; X10; X11; X12; X13; X14; X15;
        X16; X17; X19; X20; X21; X22; X23; X24; X25; X26; X27; X28] ,,
    MAYCHANGE [Q0; Q1; Q2; Q3; Q4; Q5; Q6; Q7] ,,
      MAYCHANGE [memory :> bytes (z',8 * 4)] ,,
      MAYCHANGE [NF; ZF; CF; VF]` THEN
  CONJ_TAC THENL
   [EXPAND_TAC "z'" THEN SUBSUMED_MAYCHANGE_TAC;
    ALL_TAC] THEN

  GHOST_INTRO_TAC `g8:int64` `read X12` THEN
  GHOST_INTRO_TAC `g9:int64` `read X13` THEN
  GHOST_INTRO_TAC `g10:int64` `read X14` THEN
  GHOST_INTRO_TAC `g11:int64` `read X15` THEN
  GHOST_INTRO_TAC `zlo:num` `bignum_from_memory (z,4 * i)` THEN

  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN

  ABBREV_TAC `z'':int64 = word_add z (word (32 * (i + 1)))` THEN

  SUBGOAL_THEN
   `bignum_from_memory(z'',k - 4 * i) s0 = highdigits a (4 * (i + 1))`
  MP_TAC THENL
   [EXPAND_TAC "z''" THEN REWRITE_TAC[WORD_RULE
     `word_add z (word (32 * (i + 1))) =
      word_add (word_add z (word(8 * 4 * i))) (word(8 * 4))`] THEN
    ASM_REWRITE_TAC[ARITH_RULE `8 * 4 * i = 32 * i`] THEN
    SUBGOAL_THEN `k - 4 * i = ((k + 4) - 4 * i) - 4` SUBST1_TAC THENL
     [UNDISCH_TAC `4 * i < k` THEN ARITH_TAC;
      ONCE_REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_DIV]] THEN
    ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    REWRITE_TAC[highdigits; DIV_DIV; GSYM EXP_ADD] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN DISCH_TAC] THEN

  SUBGOAL_THEN
   `(!j. j < 4
         ==> bigdigit (bignum_from_memory(z,4) s0) j = bigdigit q j) /\
    (!j. j < 4
         ==> bigdigit
              (bignum_from_memory(z',((k + 4) - 4 * i)) s0) j =
             bigdigit a (4 * i + j)) /\
    (!j. j < 4
         ==> bigdigit (highdigits (bignum_from_memory(m,k) s0) (4 * i)) j =
             bigdigit n (4 * i + j))`
  MP_TAC THENL
   [ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    REWRITE_TAC[BIGDIGIT_HIGHDIGITS];
    ALL_TAC] THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
   [HIGHDIGITS_BIGNUM_FROM_MEMORY; BIGDIGIT_BIGNUM_FROM_MEMORY] THEN
  SUBGOAL_THEN `!j. j < 4 ==> j < (k + 4) - 4 * i /\ j < k - 4 * i`
  MP_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`i:num < k4`; `4 * k4 = k`] THEN ARITH_TAC;
    SIMP_TAC[]] THEN
  DISCH_THEN(K ALL_TAC) THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
   [BIGDIGIT_HIGHDIGITS; VAL_WORD_GALOIS; DIMINDEX_64; BIGDIGIT_BOUND] THEN
  ASM_REWRITE_TAC[ARITH_RULE `8 * 4 * i = 32 * i`] THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV EXPAND_CASES_CONV)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [ADD_CLAUSES; WORD_ADD_0] THEN
  STRIP_TAC THEN

  ARM_STEPS_TAC BIGNUM_EMONTREDC_8N_NEON_EXEC (1--2) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
   `word_add (word_sub x (word 32)) (word 32) = x`]) THEN

  BYTES128_EQ_JOIN64_TAC `read (memory :> bytes128 m') s2`
    `word (bigdigit n (4 * i + 1)):(64)word`
    `word (bigdigit n (4 * i)):(64)word` THEN
  BYTES128_EQ_JOIN64_TAC `read (memory :> bytes128 (word_add m' (word 16))) s2`
    `word (bigdigit n (4 * i + 3)):(64)word`
    `word (bigdigit n (4 * i + 2)):(64)word` THEN

  ARM_ACCSTEPS_TAC BIGNUM_EMONTREDC_8N_NEON_EXEC [] (3--6) THEN
  ARM_NEON_ACCSTEPS_TAC BIGNUM_EMONTREDC_8N_NEON_EXEC [14;15] (7--15) THEN
  ARM_ACCSTEPS_TAC BIGNUM_EMONTREDC_8N_NEON_EXEC [] (16--16) THEN
  ARM_NEON_ACCSTEPS_TAC BIGNUM_EMONTREDC_8N_NEON_EXEC [24;25] (17--25) THEN
  ARM_ACCSTEPS_TAC BIGNUM_EMONTREDC_8N_NEON_EXEC
   ([26;28;30;32;34;35] @ (37--58) @
    [64;69;71;72;78;83] @ (85--90) @
    [96;101;103;104;105])
   (26--105) THEN
  ARM_ACCSTEPS_TAC BIGNUM_EMONTREDC_8N_NEON_EXEC
   ([111;116;118;119;120;121;122] @
    [128;133;135;136;137;138])
   (106--138) THEN
  ARM_ACCSTEPS_TAC BIGNUM_EMONTREDC_8N_NEON_EXEC
   ([144;149;151;152;153;154])
   (139--158) THEN

  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN

  CONJ_TAC THENL
   [SUBST1_TAC(SYM(ASSUME `word_add z (word (32 * (i + 1))):int64 = z''`)) THEN
    SUBST1_TAC(SYM(ASSUME `word_add z (word (32 * i)):int64 = z'`)) THEN
    CONV_TAC WORD_RULE;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [SUBST1_TAC(SYM(ASSUME `word_add m (word (32 * i)):int64 = m'`)) THEN
    CONV_TAC WORD_RULE;
    ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
   [REWRITE_TAC[WORD_RULE
     `word_sub (word(32 * x)) (word 32) =
      word_mul (word 32) (word_sub (word x) (word 1))`] THEN
    REWRITE_TAC[WORD_MUL] THEN AP_TERM_TAC THEN
    REWRITE_TAC[ARITH_RULE `k - (j + 1) = k - j - 1`] THEN
    GEN_REWRITE_TAC RAND_CONV [WORD_SUB] THEN
    ASM_REWRITE_TAC[ARITH_RULE `1 <= k - j <=> j < k`];
    DISCH_THEN SUBST1_TAC] THEN
  CONJ_TAC THENL
   [ALL_TAC;
    VAL_INT64_TAC `32 * (k4 - (i + 1))` THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC [`i:num < k4`; `4 * k4 = k`] THEN ARITH_TAC] THEN

  DISCH_THEN(fun th ->
   REPEAT(FIRST_X_ASSUM(ASSUME_TAC o C MATCH_MP th)) THEN
   ASSUME_TAC th) THEN

  SUBST1_TAC(ARITH_RULE `32 * i = 8 * 4 * i`) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(ONCE_DEPTH_CONV BIGNUM_EXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV)
   [ARITH_RULE `4 * (i + 1) = 4 * i + 1 + 1 + 1 + 1`] THEN
  REWRITE_TAC[ADD_ASSOC] THEN REWRITE_TAC[LOWDIGITS_CLAUSES] THEN
  GEN_REWRITE_TAC (RAND_CONV o LAND_CONV o LAND_CONV o TOP_DEPTH_CONV)
   [ADD_ASSOC] THEN
  GEN_REWRITE_TAC (RAND_CONV o LAND_CONV o RAND_CONV o TOP_DEPTH_CONV)
   [ADD_ASSOC] THEN
  GEN_REWRITE_TAC RAND_CONV
   [ARITH_RULE `(q * (x1 + l1) + (x2 + l2)) + q =
                (x1 * q + x2) + (q * l1 + l2 + q)`] THEN
  FIRST_X_ASSUM(fun th ->
    GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [SYM th]) THEN
  REWRITE_TAC[GSYM ADD_ASSOC] THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
  REWRITE_TAC[ADD_ASSOC; EQ_ADD_RCANCEL] THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; RIGHT_ADD_DISTRIB;
              EXP_ADD; GSYM MULT_ASSOC] THEN
  REWRITE_TAC[GSYM LEFT_ADD_DISTRIB] THEN AP_TERM_TAC THEN
  UNDISCH_TAC `read (memory :> bytes (z,8 * 4)) s158 = q` THEN (* s142 -> s158 *)
  CONV_TAC(LAND_CONV(LAND_CONV BIGNUM_EXPAND_CONV)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[bignum_of_wordlist] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV THEN

  ONCE_REWRITE_TAC[GSYM VAL_WORD_BIGDIGIT] THEN REWRITE_TAC[WORD_VAL] THEN
  MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
  MAP_EVERY EXISTS_TAC [`512`; `&0:real`] THEN
  REPLICATE_TAC 2 (CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC]) THEN
  CONJ_TAC THENL [REAL_INTEGER_TAC; ALL_TAC] THEN

  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN
  REWRITE_TAC[lemma1; lemma2] THEN REWRITE_TAC[WORD_XOR_MASK] THEN

  REPEAT(COND_CASES_TAC THEN
         ASM_REWRITE_TAC[BITVAL_CLAUSES; REAL_VAL_WORD_NOT]) THEN
  CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[BITVAL_CLAUSES; DIMINDEX_64] THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN DISCH_TAC THEN

  FIRST_ASSUM(MP_TAC o end_itlist CONJ o DESUM_RULE o CONJUNCTS) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[VAL_WORD_BIGDIGIT; ADD_CLAUSES; VAL_WORD_BITVAL] THEN
  CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN
  FIRST_ASSUM(MP_TAC o end_itlist CONJ o filter (is_ratconst o rand o concl) o
             DECARRY_RULE o CONJUNCTS) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

let BIGNUM_EMONTREDC_8N_NEON_SUBROUTINE_CORRECT = time prove
 (`!k z m w a n pc stackpointer returnaddress.
        aligned 16 stackpointer /\
        nonoverlapping (z,8 * 2 * val k)
                       (word_sub stackpointer (word 80),80) /\
        ALLPAIRS nonoverlapping
         [(z,8 * 2 * val k); (word_sub stackpointer (word 80),80)]
         [(word pc,1344); (m,8 * val k)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_emontredc_8n_neon_mc /\
                  read PC s = word pc /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [k; z; m; w] s /\
                  bignum_from_memory (z,2 * val k) s = a /\
                  bignum_from_memory (m,val k) s = n)
             (\s. read PC s = returnaddress /\
                  (8 divides val k /\
                   (n * val w + 1 == 0) (mod (2 EXP 64))
                   ==> n * bignum_from_memory (z,val k) s + a =
                       2 EXP (64 * val k) *
                       (2 EXP (64 * val k) * val(C_RETURN s) +
                        bignum_from_memory
                          (word_add z (word(8 * val k)),val k) s)))
            (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bytes(z,8 * 2 * val k);
                    memory :> bytes(word_sub stackpointer (word 80),80)])`,
  ARM_ADD_RETURN_STACK_TAC
    BIGNUM_EMONTREDC_8N_NEON_EXEC BIGNUM_EMONTREDC_8N_NEON_CORRECT
   `[X19; X20; X21; X22; X23; X24; X25; X26; X27; X28]` 80);;
