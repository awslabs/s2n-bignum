(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Extended Montgomery reduction of arbitrary bignum.                        *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

needs "arm/proofs/equiv.ml";;
needs "arm/proofs/neon_helper.ml";;

let maddloop_step2_full_ops:int list = [
  0x3cc20c4e;       (* arm_LDR Q14 X2 (Preimmediate_Offset (iword (&32))) *)
  0x3dc00459;       (* arm_LDR Q25 X2 (Immediate_Offset (word 16)) *)
  0x0ea129d5;       (* arm_XTN Q21 Q14 32 *)
  0x0ea12b3f;       (* arm_XTN Q31 Q25 32 *)
  0x4e995b38;       (* arm_UZP2 Q24 Q25 Q25 32 *)
  0x2ebec2a5;       (* arm_UMULL_VEC Q5 Q21 Q30 32 *)
  0x2eb2c3f0;       (* arm_UMULL_VEC Q16 Q31 Q18 32 *)
  0x2ebcc2ad;       (* arm_UMULL_VEC Q13 Q21 Q28 32 *)
  0x4e8e59ca;       (* arm_UZP2 Q10 Q14 Q14 32 *)
  0x2eb3c3e1;       (* arm_UMULL_VEC Q1 Q31 Q19 32 *)
  0x4eb99e86;       (* arm_MUL_VEC Q6 Q20 Q25 32 128 *)
  0x2eb2c300;       (* arm_UMULL_VEC Q0 Q24 Q18 32 *)
  0x6f6015a5;       (* arm_USRA_VEC Q5 Q13 32 64 128 *)
  0x2ebec142;       (* arm_UMULL_VEC Q2 Q10 Q30 32 *)
  0x6f601430;       (* arm_USRA_VEC Q16 Q1 32 64 128 *)
  0x6ea028cd;       (* arm_UADDLP Q13 Q6 32 *)
  0x4e3d1ca7;       (* arm_AND_VEC Q7 Q5 Q29 128 *)
  0x6f6014a2;       (* arm_USRA_VEC Q2 Q5 32 64 128 *)
  0x4e3d1e19;       (* arm_AND_VEC Q25 Q16 Q29 128 *)
  0x2ebc8147;       (* arm_UMLAL_VEC Q7 Q10 Q28 32 *)
  0x6f601600;       (* arm_USRA_VEC Q0 Q16 32 64 128 *)
  0x4f6055b0;       (* arm_SHL_VEC Q16 Q13 32 64 128 *)
  0x2eb38319;       (* arm_UMLAL_VEC Q25 Q24 Q19 32 *)
  0x6f6014e2;       (* arm_USRA_VEC Q2 Q7 32 64 128 *)
  0x2eb383f0;       (* arm_UMLAL_VEC Q16 Q31 Q19 32 *)
  0x4eae9e27;       (* arm_MUL_VEC Q7 Q17 Q14 32 128 *)
  0x6f601720;       (* arm_USRA_VEC Q0 Q25 32 64 128 *)
  0x6ea028ea;       (* arm_UADDLP Q10 Q7 32 *)
  0x4e183c43;       (* arm_UMOV X3 Q2 1 8 *)
  0x4e083c1a;       (* arm_UMOV X26 Q0 0 8 *)
  0xa94353e9;       (* arm_LDP X9 X20 SP (Immediate_Offset (iword (&48))) *)
  0x4f60554f;       (* arm_SHL_VEC Q15 Q10 32 64 128 *)
  0x2ebc82af;       (* arm_UMLAL_VEC Q15 Q21 Q28 32 *)
  0x4e083e11;       (* arm_UMOV X17 Q16 0 8 *)
  0x4e083c50;       (* arm_UMOV X16 Q2 0 8 *)
  0xa94217e6;       (* arm_LDP X6 X5 SP (Immediate_Offset (iword (&32))) *)
  0xa94167c7;       (* arm_LDP X7 X25 X30 (Immediate_Offset (iword (&16))) *)
  0x4e183df5;       (* arm_UMOV X21 Q15 1 8 *)
  0x4e183e17;       (* arm_UMOV X23 Q16 1 8 *)
  0xa8c62bd8;       (* arm_LDP X24 X10 X30 (Postimmediate_Offset (iword (&96))) *)
  0x9b077d36;       (* arm_MUL X22 X9 X7 *)
  0xca19028b;       (* arm_EOR X11 X20 X25 *)
  0xa9c27434;       (* arm_LDP X20 X29 X1 (Preimmediate_Offset (iword (&32))) *)
  0x9bc77d28;       (* arm_UMULH X8 X9 X7 *)
  0xca0a00b3;       (* arm_EOR X19 X5 X10 *)
  0xab1002b9;       (* arm_ADDS X25 X21 X16 *)
  0x4e183c10;       (* arm_UMOV X16 Q0 1 8 *)
  0xa9411c24;       (* arm_LDP X4 X7 X1 (Immediate_Offset (iword (&16))) *)
  0xba030235;       (* arm_ADCS X21 X17 X3 *)
  0xca0b02d6;       (* arm_EOR X22 X22 X11 *)
  0xba1a02f7;       (* arm_ADCS X23 X23 X26 *)
  0x9a1f0211;       (* arm_ADC X17 X16 XZR *)
  0xab140190;       (* arm_ADDS X16 X12 X20 *)
  0x9b187cc5;       (* arm_MUL X5 X6 X24 *)
  0xba1d01a9;       (* arm_ADCS X9 X13 X29 *)
  0x4e083dfd;       (* arm_UMOV X29 Q15 0 8 *)
  0xba0401c4;       (* arm_ADCS X4 X14 X4 *)
  0xa94737ea;       (* arm_LDP X10 X13 SP (Immediate_Offset (iword (&112))) *)
  0x9bd87cd4;       (* arm_UMULH X20 X6 X24 *)
  0xba0701f8;       (* arm_ADCS X24 X15 X7 *)
  0xa97f1fcc;       (* arm_LDP X12 X7 X30 (Immediate_Offset (iword (-- &16))) *)
  0x9a1f03e6;       (* arm_ADC X6 XZR XZR *)
  0xab1d032e;       (* arm_ADDS X14 X25 X29 *)
  0xca0b010f;       (* arm_EOR X15 X8 X11 *)
  0xba1902b9;       (* arm_ADCS X25 X21 X25 *)
  0xba1502e8;       (* arm_ADCS X8 X23 X21 *)
  0xca0701a7;       (* arm_EOR X7 X13 X7 *)
  0xba170237;       (* arm_ADCS X23 X17 X23 *)
  0xca1300b5;       (* arm_EOR X21 X5 X19 *)
  0x9a1103ed;       (* arm_ADC X13 XZR X17 *)
  0xab1d0331;       (* arm_ADDS X17 X25 X29 *)
  0xba0e0105;       (* arm_ADCS X5 X8 X14 *)
  0xba1902f9;       (* arm_ADCS X25 X23 X25 *)
  0xba0801a8;       (* arm_ADCS X8 X13 X8 *)
  0xba1703f7;       (* arm_ADCS X23 XZR X23 *)
  0x9a0d03ed;       (* arm_ADC X13 XZR X13 *)
  0xab1003bd;       (* arm_ADDS X29 X29 X16 *)
  0x9b0c7d50;       (* arm_MUL X16 X10 X12 *)
  0xba0901c9;       (* arm_ADCS X9 X14 X9 *)
  0xba040231;       (* arm_ADCS X17 X17 X4 *)
  0x9bcc7d4c;       (* arm_UMULH X12 X10 X12 *)
  0xba1800aa;       (* arm_ADCS X10 X5 X24 *)
  0xca070205;       (* arm_EOR X5 X16 X7 *)
  0xa97e3bd0;       (* arm_LDP X16 X14 X30 (Immediate_Offset (iword (-- &32))) *)
  0xba060326;       (* arm_ADCS X6 X25 X6 *)
  0xca130298;       (* arm_EOR X24 X20 X19 *)
  0xba1f0104;       (* arm_ADCS X4 X8 XZR *)
  0xa94667f4;       (* arm_LDP X20 X25 SP (Immediate_Offset (iword (&96))) *)
  0xba1f02f7;       (* arm_ADCS X23 X23 XZR *)
  0x9a1f01a8;       (* arm_ADC X8 X13 XZR *)
  0xb10004ff;       (* arm_CMN X7 (rvalue (word 1)) *)
  0xba050084;       (* arm_ADCS X4 X4 X5 *)
  0xca070185;       (* arm_EOR X5 X12 X7 *)
  0xba0502f7;       (* arm_ADCS X23 X23 X5 *)
  0x9b107e8c;       (* arm_MUL X12 X20 X16 *)
  0x9a070105;       (* arm_ADC X5 X8 X7 *)
  0xb100067f;       (* arm_CMN X19 (rvalue (word 1)) *)
  0xba150135;       (* arm_ADCS X21 X9 X21 *)
  0xca0e0328;       (* arm_EOR X8 X25 X14 *)
  0xba18022d;       (* arm_ADCS X13 X17 X24 *)
  0xa900543d;       (* arm_STP X29 X21 X1 (Immediate_Offset (iword (&0))) *)
  0x9bd07e94;       (* arm_UMULH X20 X20 X16 *)
  0xba130151;       (* arm_ADCS X17 X10 X19 *)
  0xa94463fd;       (* arm_LDP X29 X24 SP (Immediate_Offset (iword (&64))) *)
  0xba1300d9;       (* arm_ADCS X25 X6 X19 *)
  0xa97c57c6;       (* arm_LDP X6 X21 X30 (Immediate_Offset (iword (-- &64))) *)
  0xca08018a;       (* arm_EOR X10 X12 X8 *)
  0xba130089;       (* arm_ADCS X9 X4 X19 *)
  0xa97d43c4;       (* arm_LDP X4 X16 X30 (Immediate_Offset (iword (-- &48))) *)
  0xba1302ec;       (* arm_ADCS X12 X23 X19 *)
  0x9a1300a5;       (* arm_ADC X5 X5 X19 *)
  0xb100051f;       (* arm_CMN X8 (rvalue (word 1)) *)
  0xa9454fe7;       (* arm_LDP X7 X19 SP (Immediate_Offset (iword (&80))) *)
  0xba0a032e;       (* arm_ADCS X14 X25 X10 *)
  0x9b067fb9;       (* arm_MUL X25 X29 X6 *)
  0xca080294;       (* arm_EOR X20 X20 X8 *)
  0xba140137;       (* arm_ADCS X23 X9 X20 *)
  0xca150318;       (* arm_EOR X24 X24 X21 *)
  0xba08018c;       (* arm_ADCS X12 X12 X8 *)
  0x9a0800aa;       (* arm_ADC X10 X5 X8 *)
  0xb100057f;       (* arm_CMN X11 (rvalue (word 1)) *)
  0x9bc67fa5;       (* arm_UMULH X5 X29 X6 *)
  0xba1601a8;       (* arm_ADCS X8 X13 X22 *)
  0xca18032d;       (* arm_EOR X13 X25 X24 *)
  0xba0f023d;       (* arm_ADCS X29 X17 X15 *)
  0xba0b01d6;       (* arm_ADCS X22 X14 X11 *)
  0xba0b02f5;       (* arm_ADCS X21 X23 X11 *)
  0x9b047cf7;       (* arm_MUL X23 X7 X4 *)
  0xba0b018e;       (* arm_ADCS X14 X12 X11 *)
  0xca10026c;       (* arm_EOR X12 X19 X16 *)
  0x9a0b014f;       (* arm_ADC X15 X10 X11 *)
  0xb100071f;       (* arm_CMN X24 (rvalue (word 1)) *)
  0xca1800b3;       (* arm_EOR X19 X5 X24 *)
  0xba0d03ab;       (* arm_ADCS X11 X29 X13 *)
  0x9bc47cfd;       (* arm_UMULH X29 X7 X4 *)
  0xba1302cd;       (* arm_ADCS X13 X22 X19 *)
  0xba1802b3;       (* arm_ADCS X19 X21 X24 *)
  0xca0c02f6;       (* arm_EOR X22 X23 X12 *)
  0xba1801ce;       (* arm_ADCS X14 X14 X24 *)
  0x9a1801ef;       (* arm_ADC X15 X15 X24 *)
  0xb100059f;       (* arm_CMN X12 (rvalue (word 1)) *)
  0xba16016b;       (* arm_ADCS X11 X11 X22 *)
  0xca0c03a4;       (* arm_EOR X4 X29 X12 *)
  0xba0401a4;       (* arm_ADCS X4 X13 X4 *)
  0xa9012c28;       (* arm_STP X8 X11 X1 (Immediate_Offset (iword (&16))) *)
  0xba0c026d;       (* arm_ADCS X13 X19 X12 *)
  0xba0c01ce;       (* arm_ADCS X14 X14 X12 *)
  0x9a0c01ef;       (* arm_ADC X15 X15 X12 *)
  0xaa0403ec;       (* arm_MOV X12 X4 *)
  0xd100077b;       (* arm_SUB X27 X27 (rvalue (word 1)) *)
  0xb5ffed5b        (* arm_CBNZ X27 (word 2096552) *)
];;

let maddloop_step2_full_mc =
  let charlist = List.concat_map
    (fun op32 ->
      [Char.chr (Int.logand op32 255);
       Char.chr (Int.logand (Int.shift_right op32 8) 255);
       Char.chr (Int.logand (Int.shift_right op32 16) 255);
       Char.chr (Int.logand (Int.shift_right op32 24) 255)])
    maddloop_step2_full_ops in
  let byte_list = Bytes.init (List.length charlist) (fun i -> List.nth charlist i) in
  define_word_list "maddloop_step2_full_mc" (term_of_bytes byte_list);;

let MADDLOOP_STEP2_FULL_EXEC = ARM_MK_EXEC_RULE maddloop_step2_full_mc;;


let maddloop_step3_full_ops = [
  0x3cc20c4e;       (* arm_LDR Q14 X2 (Preimmediate_Offset (iword (&32))) *)
  0x3dc00459;       (* arm_LDR Q25 X2 (Immediate_Offset (word 16)) *)
  0x0ea129d5;       (* arm_XTN Q21 Q14 32 *)
  0x0ea12b3f;       (* arm_XTN Q31 Q25 32 *)
  0x4e995b38;       (* arm_UZP2 Q24 Q25 Q25 32 *)
  0x2ebec2a5;       (* arm_UMULL_VEC Q5 Q21 Q30 32 *)
  0x2eb2c3f0;       (* arm_UMULL_VEC Q16 Q31 Q18 32 *)
  0x2ebcc2ad;       (* arm_UMULL_VEC Q13 Q21 Q28 32 *)
  0x4e8e59ca;       (* arm_UZP2 Q10 Q14 Q14 32 *)
  0x2eb3c3e1;       (* arm_UMULL_VEC Q1 Q31 Q19 32 *)
  0x4eb99e86;       (* arm_MUL_VEC Q6 Q20 Q25 32 128 *)
  0x2eb2c300;       (* arm_UMULL_VEC Q0 Q24 Q18 32 *)
  0x6f6015a5;       (* arm_USRA_VEC Q5 Q13 32 64 128 *)
  0x2ebec142;       (* arm_UMULL_VEC Q2 Q10 Q30 32 *)
  0x6f601430;       (* arm_USRA_VEC Q16 Q1 32 64 128 *)
  0x6ea028cd;       (* arm_UADDLP Q13 Q6 32 *)
  0x4e3d1ca7;       (* arm_AND_VEC Q7 Q5 Q29 128 *)
  0x6f6014a2;       (* arm_USRA_VEC Q2 Q5 32 64 128 *)
  0x4e3d1e19;       (* arm_AND_VEC Q25 Q16 Q29 128 *)
  0x2ebc8147;       (* arm_UMLAL_VEC Q7 Q10 Q28 32 *)
  0x6f601600;       (* arm_USRA_VEC Q0 Q16 32 64 128 *)
  0x4f6055b0;       (* arm_SHL_VEC Q16 Q13 32 64 128 *)
  0x2eb38319;       (* arm_UMLAL_VEC Q25 Q24 Q19 32 *)
  0x6f6014e2;       (* arm_USRA_VEC Q2 Q7 32 64 128 *)
  0x2eb383f0;       (* arm_UMLAL_VEC Q16 Q31 Q19 32 *)
  0x4eae9e27;       (* arm_MUL_VEC Q7 Q17 Q14 32 128 *)
  0x6f601720;       (* arm_USRA_VEC Q0 Q25 32 64 128 *)
  0x6ea028ea;       (* arm_UADDLP Q10 Q7 32 *)
  0x4e183c43;       (* arm_UMOV X3 Q2 1 8 *)
  0x4e083c1a;       (* arm_UMOV X26 Q0 0 8 *)
  0xa94353e9;       (* arm_LDP X9 X20 SP (Immediate_Offset (iword (&48))) *)
  0x4f60554f;       (* arm_SHL_VEC Q15 Q10 32 64 128 *)
  0x2ebc82af;       (* arm_UMLAL_VEC Q15 Q21 Q28 32 *)
  0x4e083e11;       (* arm_UMOV X17 Q16 0 8 *)
  0x4e083c50;       (* arm_UMOV X16 Q2 0 8 *)
  0xa94217e6;       (* arm_LDP X6 X5 SP (Immediate_Offset (iword (&32))) *)
  0xa94167c7;       (* arm_LDP X7 X25 X30 (Immediate_Offset (iword (&16))) *)
  0x4e183df5;       (* arm_UMOV X21 Q15 1 8 *)
  0x4e183e17;       (* arm_UMOV X23 Q16 1 8 *)
  0xa8c62bd8;       (* arm_LDP X24 X10 X30 (Postimmediate_Offset (iword (&96))) *)
  0x9b077d36;       (* arm_MUL X22 X9 X7 *)
  0xca19028b;       (* arm_EOR X11 X20 X25 *)
  0xa9c27434;       (* arm_LDP X20 X29 X1 (Preimmediate_Offset (iword (&32))) *)
  0x9bc77d28;       (* arm_UMULH X8 X9 X7 *)
  0xca0a00b3;       (* arm_EOR X19 X5 X10 *)
  0xab1002b9;       (* arm_ADDS X25 X21 X16 *)
  0x4e183c10;       (* arm_UMOV X16 Q0 1 8 *)
  0xa9411c24;       (* arm_LDP X4 X7 X1 (Immediate_Offset (iword (&16))) *)
  0xba030235;       (* arm_ADCS X21 X17 X3 *)
  0xca0b02d6;       (* arm_EOR X22 X22 X11 *)
  0xba1a02f7;       (* arm_ADCS X23 X23 X26 *)
  0x9a1f0211;       (* arm_ADC X17 X16 XZR *)
  0xab140190;       (* arm_ADDS X16 X12 X20 *)
  0x9b187cc5;       (* arm_MUL X5 X6 X24 *)
  0xba1d01a9;       (* arm_ADCS X9 X13 X29 *)
  0x4e083dfd;       (* arm_UMOV X29 Q15 0 8 *)
  0xba0401c4;       (* arm_ADCS X4 X14 X4 *)
  0xa94737ea;       (* arm_LDP X10 X13 SP (Immediate_Offset (iword (&112))) *)
  0x9bd87cd4;       (* arm_UMULH X20 X6 X24 *)
  0xba0701f8;       (* arm_ADCS X24 X15 X7 *)
  0xa97f1fcc;       (* arm_LDP X12 X7 X30 (Immediate_Offset (iword (-- &16))) *)
  0x9a1f03e6;       (* arm_ADC X6 XZR XZR *)
  0xab1d032e;       (* arm_ADDS X14 X25 X29 *)
  0xca0b010f;       (* arm_EOR X15 X8 X11 *)
  0xba1902b9;       (* arm_ADCS X25 X21 X25 *)
  0xba1502e8;       (* arm_ADCS X8 X23 X21 *)
  0xca0701a7;       (* arm_EOR X7 X13 X7 *)
  0xba170237;       (* arm_ADCS X23 X17 X23 *)
  0xca1300b5;       (* arm_EOR X21 X5 X19 *)
  0x9a1103ed;       (* arm_ADC X13 XZR X17 *)
  0xab1d0331;       (* arm_ADDS X17 X25 X29 *)
  0xba0e0105;       (* arm_ADCS X5 X8 X14 *)
  0xba1902f9;       (* arm_ADCS X25 X23 X25 *)
  0xba0801a8;       (* arm_ADCS X8 X13 X8 *)
  0xba1703f7;       (* arm_ADCS X23 XZR X23 *)
  0x9a0d03ed;       (* arm_ADC X13 XZR X13 *)
  0xab1003bd;       (* arm_ADDS X29 X29 X16 *)
  0x9b0c7d50;       (* arm_MUL X16 X10 X12 *)
  0xba0901c9;       (* arm_ADCS X9 X14 X9 *)
  0xba040231;       (* arm_ADCS X17 X17 X4 *)
  0x9bcc7d4c;       (* arm_UMULH X12 X10 X12 *)
  0xba1800aa;       (* arm_ADCS X10 X5 X24 *)
  0xca070205;       (* arm_EOR X5 X16 X7 *)
  0xa97e3bd0;       (* arm_LDP X16 X14 X30 (Immediate_Offset (iword (-- &32))) *)
  0xba060326;       (* arm_ADCS X6 X25 X6 *)
  0xca130298;       (* arm_EOR X24 X20 X19 *)
  0xba1f0104;       (* arm_ADCS X4 X8 XZR *)
  0xa94667f4;       (* arm_LDP X20 X25 SP (Immediate_Offset (iword (&96))) *)
  0xba1f02f7;       (* arm_ADCS X23 X23 XZR *)
  0x9a1f01a8;       (* arm_ADC X8 X13 XZR *)
  0xb10004ff;       (* arm_CMN X7 (rvalue (word 1)) *)
  0xba050084;       (* arm_ADCS X4 X4 X5 *)
  0xca070185;       (* arm_EOR X5 X12 X7 *)
  0xba0502f7;       (* arm_ADCS X23 X23 X5 *)
  0x9b107e8c;       (* arm_MUL X12 X20 X16 *)
  0x9a070105;       (* arm_ADC X5 X8 X7 *)
  0xb100067f;       (* arm_CMN X19 (rvalue (word 1)) *)
  0xba150135;       (* arm_ADCS X21 X9 X21 *)
  0xca0e0328;       (* arm_EOR X8 X25 X14 *)
  0xba18022d;       (* arm_ADCS X13 X17 X24 *)
  0xa900543d;       (* arm_STP X29 X21 X1 (Immediate_Offset (iword (&0))) *)
  0x9bd07e94;       (* arm_UMULH X20 X20 X16 *)
  0xba130151;       (* arm_ADCS X17 X10 X19 *)
  0xa94463fd;       (* arm_LDP X29 X24 SP (Immediate_Offset (iword (&64))) *)
  0xba1300d9;       (* arm_ADCS X25 X6 X19 *)
  0xa97c57c6;       (* arm_LDP X6 X21 X30 (Immediate_Offset (iword (-- &64))) *)
  0xca08018a;       (* arm_EOR X10 X12 X8 *)
  0xba130089;       (* arm_ADCS X9 X4 X19 *)
  0xa97d43c4;       (* arm_LDP X4 X16 X30 (Immediate_Offset (iword (-- &48))) *)
  0xba1302ec;       (* arm_ADCS X12 X23 X19 *)
  0x9a1300a5;       (* arm_ADC X5 X5 X19 *)
  0xb100051f;       (* arm_CMN X8 (rvalue (word 1)) *)
  0xa9454fe7;       (* arm_LDP X7 X19 SP (Immediate_Offset (iword (&80))) *)
  0xba0a032e;       (* arm_ADCS X14 X25 X10 *)
  0x9b067fb9;       (* arm_MUL X25 X29 X6 *)
  0xca080294;       (* arm_EOR X20 X20 X8 *)
  0xba140137;       (* arm_ADCS X23 X9 X20 *)
  0xca150318;       (* arm_EOR X24 X24 X21 *)
  0xba08018c;       (* arm_ADCS X12 X12 X8 *)
  0x9a0800aa;       (* arm_ADC X10 X5 X8 *)
  0xb100057f;       (* arm_CMN X11 (rvalue (word 1)) *)
  0x9bc67fa5;       (* arm_UMULH X5 X29 X6 *)
  0xba1601a8;       (* arm_ADCS X8 X13 X22 *)
  0xca18032d;       (* arm_EOR X13 X25 X24 *)
  0xba0f023d;       (* arm_ADCS X29 X17 X15 *)
  0xba0b01d6;       (* arm_ADCS X22 X14 X11 *)
  0xba0b02f5;       (* arm_ADCS X21 X23 X11 *)
  0x9b047cf7;       (* arm_MUL X23 X7 X4 *)
  0xba0b018e;       (* arm_ADCS X14 X12 X11 *)
  0xca10026c;       (* arm_EOR X12 X19 X16 *)
  0x9a0b014f;       (* arm_ADC X15 X10 X11 *)
  0xb100071f;       (* arm_CMN X24 (rvalue (word 1)) *)
  0xca1800b3;       (* arm_EOR X19 X5 X24 *)
  0xba0d03ab;       (* arm_ADCS X11 X29 X13 *)
  0x9bc47cfd;       (* arm_UMULH X29 X7 X4 *)
  0xba1302cd;       (* arm_ADCS X13 X22 X19 *)
  0xba1802b3;       (* arm_ADCS X19 X21 X24 *)
  0xca0c02f6;       (* arm_EOR X22 X23 X12 *)
  0xba1801ce;       (* arm_ADCS X14 X14 X24 *)
  0x9a1801ef;       (* arm_ADC X15 X15 X24 *)
  0xb100059f;       (* arm_CMN X12 (rvalue (word 1)) *)
  0xba16016b;       (* arm_ADCS X11 X11 X22 *)
  0xca0c03a4;       (* arm_EOR X4 X29 X12 *)
  0xba0401a4;       (* arm_ADCS X4 X13 X4 *)
  0xa9012c28;       (* arm_STP X8 X11 X1 (Immediate_Offset (iword (&16))) *)
  0xba0c026d;       (* arm_ADCS X13 X19 X12 *)
  0xba0c01ce;       (* arm_ADCS X14 X14 X12 *)
  0x9a0c01ef;       (* arm_ADC X15 X15 X12 *)
  0xaa0403ec;       (* arm_MOV X12 X4 *)
  0x3cc20c4e;       (* arm_LDR Q14 X2 (Preimmediate_Offset (iword (&32))) *)
  0x3dc00459;       (* arm_LDR Q25 X2 (Immediate_Offset (word 16)) *)
  0x0ea129d5;       (* arm_XTN Q21 Q14 32 *)
  0x0ea12b3f;       (* arm_XTN Q31 Q25 32 *)
  0x4e995b38;       (* arm_UZP2 Q24 Q25 Q25 32 *)
  0x2ebec2a5;       (* arm_UMULL_VEC Q5 Q21 Q30 32 *)
  0x2eb2c3f0;       (* arm_UMULL_VEC Q16 Q31 Q18 32 *)
  0x2ebcc2ad;       (* arm_UMULL_VEC Q13 Q21 Q28 32 *)
  0x4e8e59ca;       (* arm_UZP2 Q10 Q14 Q14 32 *)
  0x2eb3c3e1;       (* arm_UMULL_VEC Q1 Q31 Q19 32 *)
  0x4eb99e86;       (* arm_MUL_VEC Q6 Q20 Q25 32 128 *)
  0x2eb2c300;       (* arm_UMULL_VEC Q0 Q24 Q18 32 *)
  0x6f6015a5;       (* arm_USRA_VEC Q5 Q13 32 64 128 *)
  0x2ebec142;       (* arm_UMULL_VEC Q2 Q10 Q30 32 *)
  0x6f601430;       (* arm_USRA_VEC Q16 Q1 32 64 128 *)
  0x6ea028cd;       (* arm_UADDLP Q13 Q6 32 *)
  0x4e3d1ca7;       (* arm_AND_VEC Q7 Q5 Q29 128 *)
  0x6f6014a2;       (* arm_USRA_VEC Q2 Q5 32 64 128 *)
  0x4e3d1e19;       (* arm_AND_VEC Q25 Q16 Q29 128 *)
  0x2ebc8147;       (* arm_UMLAL_VEC Q7 Q10 Q28 32 *)
  0x6f601600;       (* arm_USRA_VEC Q0 Q16 32 64 128 *)
  0x4f6055b0;       (* arm_SHL_VEC Q16 Q13 32 64 128 *)
  0x2eb38319;       (* arm_UMLAL_VEC Q25 Q24 Q19 32 *)
  0x6f6014e2;       (* arm_USRA_VEC Q2 Q7 32 64 128 *)
  0x2eb383f0;       (* arm_UMLAL_VEC Q16 Q31 Q19 32 *)
  0x4eae9e27;       (* arm_MUL_VEC Q7 Q17 Q14 32 128 *)
  0x6f601720;       (* arm_USRA_VEC Q0 Q25 32 64 128 *)
  0x6ea028ea;       (* arm_UADDLP Q10 Q7 32 *)
  0x4e183c43;       (* arm_UMOV X3 Q2 1 8 *)
  0x4e083c1a;       (* arm_UMOV X26 Q0 0 8 *)
  0xa94353e9;       (* arm_LDP X9 X20 SP (Immediate_Offset (iword (&48))) *)
  0x4f60554f;       (* arm_SHL_VEC Q15 Q10 32 64 128 *)
  0x2ebc82af;       (* arm_UMLAL_VEC Q15 Q21 Q28 32 *)
  0x4e083e11;       (* arm_UMOV X17 Q16 0 8 *)
  0x4e083c50;       (* arm_UMOV X16 Q2 0 8 *)
  0xa94217e6;       (* arm_LDP X6 X5 SP (Immediate_Offset (iword (&32))) *)
  0xa94167c7;       (* arm_LDP X7 X25 X30 (Immediate_Offset (iword (&16))) *)
  0x4e183df5;       (* arm_UMOV X21 Q15 1 8 *)
  0x4e183e17;       (* arm_UMOV X23 Q16 1 8 *)
  0xa8c62bd8;       (* arm_LDP X24 X10 X30 (Postimmediate_Offset (iword (&96))) *)
  0x9b077d36;       (* arm_MUL X22 X9 X7 *)
  0xca19028b;       (* arm_EOR X11 X20 X25 *)
  0xa9c27434;       (* arm_LDP X20 X29 X1 (Preimmediate_Offset (iword (&32))) *)
  0x9bc77d28;       (* arm_UMULH X8 X9 X7 *)
  0xd100077b;       (* arm_SUB X27 X27 (rvalue (word 1)) *)
  0xb5ffed5b;       (* arm_CBNZ X27 (word 2096552) *)
  0xca0a00b3;       (* arm_EOR X19 X5 X10 *)
  0xab1002b9;       (* arm_ADDS X25 X21 X16 *)
  0x4e183c10;       (* arm_UMOV X16 Q0 1 8 *)
  0xa9411c24;       (* arm_LDP X4 X7 X1 (Immediate_Offset (iword (&16))) *)
  0xba030235;       (* arm_ADCS X21 X17 X3 *)
  0xca0b02d6;       (* arm_EOR X22 X22 X11 *)
  0xba1a02f7;       (* arm_ADCS X23 X23 X26 *)
  0x9a1f0211;       (* arm_ADC X17 X16 XZR *)
  0xab140190;       (* arm_ADDS X16 X12 X20 *)
  0x9b187cc5;       (* arm_MUL X5 X6 X24 *)
  0xba1d01a9;       (* arm_ADCS X9 X13 X29 *)
  0x4e083dfd;       (* arm_UMOV X29 Q15 0 8 *)
  0xba0401c4;       (* arm_ADCS X4 X14 X4 *)
  0xa94737ea;       (* arm_LDP X10 X13 SP (Immediate_Offset (iword (&112))) *)
  0x9bd87cd4;       (* arm_UMULH X20 X6 X24 *)
  0xba0701f8;       (* arm_ADCS X24 X15 X7 *)
  0xa97f1fcc;       (* arm_LDP X12 X7 X30 (Immediate_Offset (iword (-- &16))) *)
  0x9a1f03e6;       (* arm_ADC X6 XZR XZR *)
  0xab1d032e;       (* arm_ADDS X14 X25 X29 *)
  0xca0b010f;       (* arm_EOR X15 X8 X11 *)
  0xba1902b9;       (* arm_ADCS X25 X21 X25 *)
  0xba1502e8;       (* arm_ADCS X8 X23 X21 *)
  0xca0701a7;       (* arm_EOR X7 X13 X7 *)
  0xba170237;       (* arm_ADCS X23 X17 X23 *)
  0xca1300b5;       (* arm_EOR X21 X5 X19 *)
  0x9a1103ed;       (* arm_ADC X13 XZR X17 *)
  0xab1d0331;       (* arm_ADDS X17 X25 X29 *)
  0xba0e0105;       (* arm_ADCS X5 X8 X14 *)
  0xba1902f9;       (* arm_ADCS X25 X23 X25 *)
  0xba0801a8;       (* arm_ADCS X8 X13 X8 *)
  0xba1703f7;       (* arm_ADCS X23 XZR X23 *)
  0x9a0d03ed;       (* arm_ADC X13 XZR X13 *)
  0xab1003bd;       (* arm_ADDS X29 X29 X16 *)
  0x9b0c7d50;       (* arm_MUL X16 X10 X12 *)
  0xba0901c9;       (* arm_ADCS X9 X14 X9 *)
  0xba040231;       (* arm_ADCS X17 X17 X4 *)
  0x9bcc7d4c;       (* arm_UMULH X12 X10 X12 *)
  0xba1800aa;       (* arm_ADCS X10 X5 X24 *)
  0xca070205;       (* arm_EOR X5 X16 X7 *)
  0xa97e3bd0;       (* arm_LDP X16 X14 X30 (Immediate_Offset (iword (-- &32))) *)
  0xba060326;       (* arm_ADCS X6 X25 X6 *)
  0xca130298;       (* arm_EOR X24 X20 X19 *)
  0xba1f0104;       (* arm_ADCS X4 X8 XZR *)
  0xa94667f4;       (* arm_LDP X20 X25 SP (Immediate_Offset (iword (&96))) *)
  0xba1f02f7;       (* arm_ADCS X23 X23 XZR *)
  0x9a1f01a8;       (* arm_ADC X8 X13 XZR *)
  0xb10004ff;       (* arm_CMN X7 (rvalue (word 1)) *)
  0xba050084;       (* arm_ADCS X4 X4 X5 *)
  0xca070185;       (* arm_EOR X5 X12 X7 *)
  0xba0502f7;       (* arm_ADCS X23 X23 X5 *)
  0x9b107e8c;       (* arm_MUL X12 X20 X16 *)
  0x9a070105;       (* arm_ADC X5 X8 X7 *)
  0xb100067f;       (* arm_CMN X19 (rvalue (word 1)) *)
  0xba150135;       (* arm_ADCS X21 X9 X21 *)
  0xca0e0328;       (* arm_EOR X8 X25 X14 *)
  0xba18022d;       (* arm_ADCS X13 X17 X24 *)
  0xa900543d;       (* arm_STP X29 X21 X1 (Immediate_Offset (iword (&0))) *)
  0x9bd07e94;       (* arm_UMULH X20 X20 X16 *)
  0xba130151;       (* arm_ADCS X17 X10 X19 *)
  0xa94463fd;       (* arm_LDP X29 X24 SP (Immediate_Offset (iword (&64))) *)
  0xba1300d9;       (* arm_ADCS X25 X6 X19 *)
  0xa97c57c6;       (* arm_LDP X6 X21 X30 (Immediate_Offset (iword (-- &64))) *)
  0xca08018a;       (* arm_EOR X10 X12 X8 *)
  0xba130089;       (* arm_ADCS X9 X4 X19 *)
  0xa97d43c4;       (* arm_LDP X4 X16 X30 (Immediate_Offset (iword (-- &48))) *)
  0xba1302ec;       (* arm_ADCS X12 X23 X19 *)
  0x9a1300a5;       (* arm_ADC X5 X5 X19 *)
  0xb100051f;       (* arm_CMN X8 (rvalue (word 1)) *)
  0xa9454fe7;       (* arm_LDP X7 X19 SP (Immediate_Offset (iword (&80))) *)
  0xba0a032e;       (* arm_ADCS X14 X25 X10 *)
  0x9b067fb9;       (* arm_MUL X25 X29 X6 *)
  0xca080294;       (* arm_EOR X20 X20 X8 *)
  0xba140137;       (* arm_ADCS X23 X9 X20 *)
  0xca150318;       (* arm_EOR X24 X24 X21 *)
  0xba08018c;       (* arm_ADCS X12 X12 X8 *)
  0x9a0800aa;       (* arm_ADC X10 X5 X8 *)
  0xb100057f;       (* arm_CMN X11 (rvalue (word 1)) *)
  0x9bc67fa5;       (* arm_UMULH X5 X29 X6 *)
  0xba1601a8;       (* arm_ADCS X8 X13 X22 *)
  0xca18032d;       (* arm_EOR X13 X25 X24 *)
  0xba0f023d;       (* arm_ADCS X29 X17 X15 *)
  0xba0b01d6;       (* arm_ADCS X22 X14 X11 *)
  0xba0b02f5;       (* arm_ADCS X21 X23 X11 *)
  0x9b047cf7;       (* arm_MUL X23 X7 X4 *)
  0xba0b018e;       (* arm_ADCS X14 X12 X11 *)
  0xca10026c;       (* arm_EOR X12 X19 X16 *)
  0x9a0b014f;       (* arm_ADC X15 X10 X11 *)
  0xb100071f;       (* arm_CMN X24 (rvalue (word 1)) *)
  0xca1800b3;       (* arm_EOR X19 X5 X24 *)
  0xba0d03ab;       (* arm_ADCS X11 X29 X13 *)
  0x9bc47cfd;       (* arm_UMULH X29 X7 X4 *)
  0xba1302cd;       (* arm_ADCS X13 X22 X19 *)
  0xba1802b3;       (* arm_ADCS X19 X21 X24 *)
  0xca0c02f6;       (* arm_EOR X22 X23 X12 *)
  0xba1801ce;       (* arm_ADCS X14 X14 X24 *)
  0x9a1801ef;       (* arm_ADC X15 X15 X24 *)
  0xb100059f;       (* arm_CMN X12 (rvalue (word 1)) *)
  0xba16016b;       (* arm_ADCS X11 X11 X22 *)
  0xca0c03a4;       (* arm_EOR X4 X29 X12 *)
  0xba0401a4;       (* arm_ADCS X4 X13 X4 *)
  0xa9012c28;       (* arm_STP X8 X11 X1 (Immediate_Offset (iword (&16))) *)
  0xba0c026d;       (* arm_ADCS X13 X19 X12 *)
  0xba0c01ce;       (* arm_ADCS X14 X14 X12 *)
  0x9a0c01ef;       (* arm_ADC X15 X15 X12 *)
  0xaa0403ec        (* arm_MOV X12 X4 *)
];;


let maddloop_step3_full_mc =
  let charlist = List.concat_map
    (fun op32 ->
      [Char.chr (Int.logand op32 255);
       Char.chr (Int.logand (Int.shift_right op32 8) 255);
       Char.chr (Int.logand (Int.shift_right op32 16) 255);
       Char.chr (Int.logand (Int.shift_right op32 24) 255)])
    maddloop_step3_full_ops in
  let byte_list = Bytes.init (List.length charlist) (fun i -> List.nth charlist i) in
  define_word_list "maddloop_step3_full_mc" (term_of_bytes byte_list);;

let MADDLOOP_STEP3_FULL_EXEC = ARM_MK_EXEC_RULE maddloop_step3_full_mc;;

let maddloop_step3_full_labels = [
  new_definition `maddloop_step3_label_maddloop_neon = 0xb0`;
  new_definition `maddloop_step3_label_innerloop_postamble = 0x30c`;  
];;

let in_regs, out_regs = approximate_input_output_regs (snd MADDLOOP_STEP3_FULL_EXEC) [(0xb0,0x308)];;
let in_xregs = filter (fun t -> type_of t = `:(armstate,int64)component`) in_regs;;
(* exclude pointers because they will explicitly appear in loop_rotate_eqin*)
let in_xregs = subtract in_xregs [`X27`;`X1`;`X2`;`SP`;`X30`];;
let in_qregs = filter (fun t -> type_of t = `:(armstate,int128)component`) in_regs;;
let eq_xregs = new_definition
  (mk_eq
    (`(loop_rotate_eq_xregs:armstate#armstate->bool) (s1,s1')`,
      list_mk_icomb "mk_equiv_regs"
      [mk_list (in_xregs,`:(armstate,int64)component`);`(s1:armstate,s1':armstate)`]));;
let eq_qregs = new_definition
  (mk_eq
    (`(loop_rotate_eq_qregs:armstate#armstate->bool) (s1,s1')`,
      list_mk_icomb "mk_equiv_regs"
      [mk_list (in_qregs,`:(armstate,int128)component`);`(s1:armstate,s1':armstate)`]));;

let out_xregs,out_regs2 = partition (fun t -> type_of t = `:(armstate,int64)component`) out_regs;;
let out_qregs,out_flags = partition (fun t -> type_of t = `:(armstate,int128)component`) out_regs2;;

let loop_rotate_eqin = new_definition
  `forall s1 s1' z m m_precalc sp k i.
  (loop_rotate_eqin:(armstate#armstate)->int64->int64->int64->int64->num->num->bool)
        (s1,s1') z m m_precalc sp k i <=>
   (read X27 s1 = word (i + 1) /\ read X27 s1' = word i /\
    read X1 s1 = word_add z (word 32) /\ read X1 s1' = word_add z (word 32) /\
    read X2 s1 = word_add m (word 32) /\ read X2 s1' = word_add m (word 32) /\
    read SP s1 = sp /\ read SP s1' = sp /\
    read X30 s1 = word_add m_precalc (word 96) /\
    read X30 s1' = word_add m_precalc (word 96) /\
    (exists a. bignum_from_memory (z,k) s1  = a /\ bignum_from_memory (z,k) s1' = a) /\
    (exists a. bignum_from_memory (m,k) s1  = a /\ bignum_from_memory (m,k) s1' = a) /\
    (exists a. bignum_from_memory (word_add sp (word 32),12) s1 = a /\
                bignum_from_memory (word_add sp (word 32),12) s1' = a) /\
    (exists a. bignum_from_memory (m_precalc,12*(k DIV 4 - 1)) s1 = a /\
                bignum_from_memory (m_precalc,12*(k DIV 4 - 1)) s1' = a) /\
    loop_rotate_eq_xregs(s1,s1') /\
    loop_rotate_eq_qregs(s1,s1'))`;;

let loop_rotate_eqout = new_definition
  `forall s1 s1' z m m_precalc sp k.
  (loop_rotate_eqout:(armstate#armstate)->int64->int64->int64->int64->num->bool)
        (s1,s1') z m m_precalc sp k <=>
   (read X1 s1 = word_add z (word (8 * (k - 4))) /\
    read X1 s1' = word_add z (word (8 * (k - 4))) /\
    read X2 s1 = word_add m (word (8 * (k - 4))) /\
    read X2 s1' = word_add m (word (8 * (k - 4))) /\
    read SP s1 = sp /\ read SP s1' = sp /\
    read X30 s1 = word_add m_precalc (word (8 * (12*(k DIV 4 - 1)))) /\
    read X30 s1' = word_add m_precalc (word (8 * (12*(k DIV 4 - 1)))) /\
    (exists a. bignum_from_memory (z,k) s1  = a /\ bignum_from_memory (z,k) s1' = a) /\
    (exists a. bignum_from_memory (m,k) s1  = a /\ bignum_from_memory (m,k) s1' = a) /\
    (exists a. bignum_from_memory (word_add sp (word 32),12) s1 = a /\
                bignum_from_memory (word_add sp (word 32),12) s1' = a) /\
    (exists a. bignum_from_memory (m_precalc,12*(k DIV 4 - 1)) s1 = a /\
                bignum_from_memory (m_precalc,12*(k DIV 4 - 1)) s1' = a) /\
    loop_rotate_eq_xregs(s1,s1') /\
    loop_rotate_eq_qregs(s1,s1'))`;;

let maychanges =
  end_itlist (fun x y -> mk_icomb (mk_icomb (`,,`,x),y))
    [mk_icomb (`MAYCHANGE`,mk_list (out_xregs, `:(armstate,int64)component`));
     mk_icomb (`MAYCHANGE`,mk_list (out_qregs, `:(armstate,int128)component`));
     mk_icomb (`MAYCHANGE`,mk_list (out_flags, `:(armstate,bool)component`));
     `MAYCHANGE [memory :> bytes (z:int64,8 * k)]`;
     `MAYCHANGE [PC]`];;

(* The new definition of equiv_goal1 is created by running the following statement and
   modifying the last argument of loop_rotate_eqin as "(k DIV 4 - 2)".
  mk_equiv_statement
    `ALL (nonoverlapping (z,8 * k))
     [word pc:int64,LENGTH maddloop_step2_full_mc; word pc2:int64,LENGTH maddloop_step3_full_mc;
      sp:int64,128; m:int64,8*k; m_precalc:int64,8*12*(k DIV 4 - 1)] /\
     aligned 16 (sp:int64) /\ 8 divides k /\ 12 <= k /\ k < 2 EXP 61`
    loop_rotate_eqin
    loop_rotate_eqout
    maddloop_step2_full_mc 0xb0 0xb0
    maychanges
    maddloop_step3_full_mc 0xb0 0x30c
    maychanges
    `\(s:armstate). 151 * (k DIV 4 - 2)` `\(s:armstate). 151 * (k DIV 4 - 2)`;;
*)

let equiv_goal1 = 
  `forall pc pc2 z m m_precalc sp k.
     ALL (nonoverlapping (z,8 * k))
     [word pc,LENGTH maddloop_step2_full_mc; word pc2,LENGTH maddloop_step3_full_mc;
      sp,128; m,8*k; m_precalc,8*12*(k DIV 4 - 1)] /\
     aligned 16 sp /\ 8 divides k /\ 12 <= k /\ k < 2 EXP 61
     ==> ensures2 arm
         (\(s,s2).
              aligned_bytes_loaded s (word pc) maddloop_step2_full_mc /\
              read PC s = word (pc + 176) /\
              aligned_bytes_loaded s2 (word pc2) maddloop_step3_full_mc /\
              read PC s2 = word (pc2 + 176) /\
              loop_rotate_eqin (s,s2) z m m_precalc sp k (k DIV 4 - 2))
         (\(s,s2).
              aligned_bytes_loaded s (word pc) maddloop_step2_full_mc /\
              read PC s = word (pc + 176) /\
              aligned_bytes_loaded s2 (word pc2) maddloop_step3_full_mc /\
              read PC s2 = word (pc2 + 780) /\
              loop_rotate_eqout (s,s2) z m m_precalc sp k)
         (\(s,s2) (s',s2').
              (MAYCHANGE
               [X19; X4; X13; X14; X15; X12; X2; X3; X26; X9; X17; X16; X5;
                X6; X25; X7; X21; X23; X30; X10; X24; X22; X11; X1; X29; X20;
                X8; X27] ,,
               MAYCHANGE
               [Q14; Q21; Q31; Q24; Q1; Q6; Q5; Q13; Q25; Q2; Q16; Q7; Q0;
                Q10; Q15] ,,
               MAYCHANGE [VF; CF; ZF; NF] ,,
               MAYCHANGE [memory :> bytes (z,8 * k)] ,,
               MAYCHANGE [PC])
              s
              s' /\
              (MAYCHANGE
               [X19; X4; X13; X14; X15; X12; X2; X3; X26; X9; X17; X16; X5;
                X6; X25; X7; X21; X23; X30; X10; X24; X22; X11; X1; X29; X20;
                X8; X27] ,,
               MAYCHANGE
               [Q14; Q21; Q31; Q24; Q1; Q6; Q5; Q13; Q25; Q2; Q16; Q7; Q0;
                Q10; Q15] ,,
               MAYCHANGE [VF; CF; ZF; NF] ,,
               MAYCHANGE [memory :> bytes (z,8 * k)] ,,
               MAYCHANGE [PC])
              s2
              s2')
         (\s. 151 * (k DIV 4 - 2))
         (\s. 151 * (k DIV 4 - 2))`;;

let DESTRUCT_EXISTS_ASSUMS_TAC =
  REPEAT (FIRST_X_ASSUM (fun th ->
    let cth = concl th in
    if is_exists cth then MP_TAC th THEN STRIP_TAC
    else NO_TAC));;

let FIND_ABBREV_THEN (varname:string) (ttac:thm_tactic): tactic =
  fun (asl,g) ->
    let _,the_th = find (fun (_,th) -> let c = concl th in
      is_eq c && is_var (rhs c) && name_of (rhs c) = varname)
      asl in
    ttac the_th (asl,g);;

let MADDLOOP_STEP2_STEP3_EQUIV = prove(equiv_goal1,
  REWRITE_TAC[MODIFIABLE_SIMD_REGS;SOME_FLAGS;
    ALLPAIRS;ALL;NONOVERLAPPING_CLAUSES;
    fst MADDLOOP_STEP2_FULL_EXEC; fst MADDLOOP_STEP3_FULL_EXEC] THEN
  REPEAT STRIP_TAC THEN

  ABBREV_TAC `k4 = k DIV 4` THEN
  SUBGOAL_THEN `k4 < 2 EXP 59` ASSUME_TAC THENL [ASM_ARITH_TAC;ALL_TAC]
  THEN
  SUBGOAL_THEN `4 * k4 = k` ASSUME_TAC THENL [
    UNDISCH_TAC `8 divides k` THEN
    REWRITE_TAC[DIVIDES_DIV_MULT;ARITH_RULE`k DIV 8 = k DIV (4*2)`;GSYM DIV_DIV] THEN
    ASM_ARITH_TAC;
    ALL_TAC
  ] THEN
  SUBGOAL_THEN `3 <= k4` ASSUME_TAC THENL [ ASM_ARITH_TAC; ALL_TAC ] THEN

  (* iterates 'k / 4 - 2' times, where k is the number of words in modulus *)
  ENSURES2_WHILE_PAUP_TAC `1` `k4 - 1:num` `pc+0xb0` `pc+0xb0` `pc2+0xb0` `pc2+0x308`
    `\(i:num) s1 s1'.
      // loop counter
      read X27 s1 = word (k4 - i) /\
      read X27 s1' = word (k4 - (i + 1)) /\
      // pointers
      read X1 s1 = word_add z (word (8 * 4 * i)) /\
      read X1 s1' = word_add z (word (8 * 4 * i)) /\
      read X2 s1 = word_add m (word (8 * 4 * i)) /\
      read X2 s1' = word_add m (word (8 * 4 * i)) /\
      read SP s1 = sp /\ read SP s1' = sp /\
      read X30 s1 = word_add m_precalc (word (8 * 12 * i)) /\
      read X30 s1' = word_add m_precalc (word (8 * 12 * i)) /\
      // equality
      (exists a. bignum_from_memory (z, k) s1  = a /\ bignum_from_memory (z,k) s1' = a) /\
      (exists a. bignum_from_memory (m,k) s1  = a /\ bignum_from_memory (m,k) s1' = a) /\
      (exists a. bignum_from_memory (word_add sp (word 32),12) s1 = a /\
                  bignum_from_memory (word_add sp (word 32),12) s1' = a) /\
      (exists a. bignum_from_memory (m_precalc,12*(k DIV 4 - 1)) s1 = a /\
                  bignum_from_memory (m_precalc,12*(k DIV 4 - 1)) s1' = a) /\
      loop_rotate_eq_xregs(s1,s1') /\
      loop_rotate_eq_qregs(s1,s1')`
    `\(i:num) (s:armstate). T` `\(i:num) (s:armstate). T`
    `\(i:num). 151` (* include backedge *)
    `\(i:num). 150`
    (* pre steps *)`0` `0`
    (* post steps *)`0` `1`
    (* num backedges *)`0` `1` THEN REPEAT CONJ_TAC THENL [
      (* loop count which is k4-1 > 0. *)
      FIRST_ASSUM (fun th -> MP_TAC (MATCH_MP DIVIDES_LE th)) THEN ASM_ARITH_TAC;

      (* precond to loop entrance *)
      REWRITE_TAC[loop_rotate_eqin; MULT_0; WORD_ADD_0; SUB_0] THEN
      MATCH_MP_TAC ENSURES2_TRIVIAL THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
      SUBGOAL_THEN `k4 - 2 + 1 = k4 - 1` SUBST_ALL_TAC THENL [ASM_ARITH_TAC;ALL_TAC] THEN
      CONJ_TAC THENL [
        CONV_TAC (ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN NO_TAC;
        REPEAT STRIP_TAC THENL [
          ASSUME_TAC (ISPECL [`p1:armstate`] MAYCHANGE_STARTER) THEN
          MONOTONE_MAYCHANGE_TAC;
          ASSUME_TAC (ISPECL [`p1:armstate`] MAYCHANGE_STARTER) THEN
          MONOTONE_MAYCHANGE_TAC;
        ]
      ];

      (* the loop body. lockstep simulation is needed. *)
      ALL_TAC;

      (* backedge. *)
      REPEAT STRIP_TAC THEN
      ENSURES2_INIT_TAC "s0" "s0'" THEN
      UNDISCH_THEN `k DIV 4 = k4` (fun th -> SUBST_ALL_TAC th THEN ASSUME_TAC th) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[eq_xregs;eq_qregs;mk_equiv_regs;BIGNUM_FROM_MEMORY_BYTES]) THEN
      REPEAT SPLIT_FIRST_CONJ_ASSUM_TAC THEN
      DESTRUCT_EXISTS_ASSUMS_TAC THEN
      ARM_STUTTER_RIGHT_TAC MADDLOOP_STEP3_FULL_EXEC [1] "'" None THEN
      REPEAT_N 2 ENSURES_FINAL_STATE'_TAC THEN
      SUBGOAL_THEN `~(val (word (k4 - (i + 1)):int64) = 0)` MP_TAC THENL [
        IMP_REWRITE_TAC[VAL_WORD_EQ;DIMINDEX_64] THEN ASM_ARITH_TAC;
        ALL_TAC
      ] THEN
      DISCH_THEN (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
      CONJ_TAC THENL [
        REPEAT_N 18 (CONJ_TAC THENL
          [FIRST_X_ASSUM MATCH_ACCEPT_TAC ORELSE ASM_MESON_TAC[BIGNUM_FROM_MEMORY_BYTES];
          ALL_TAC]) THEN
        CONJ_TAC THENL [
          REWRITE_TAC[eq_xregs;eq_qregs;mk_equiv_regs] THEN
          ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];

          REWRITE_TAC[eq_xregs;eq_qregs;mk_equiv_regs] THEN
          ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
        ];

        CONJ_TAC THENL [
          ASSUME_TAC (ISPECL [`p1:armstate`] MAYCHANGE_STARTER) THEN
          MONOTONE_MAYCHANGE_TAC;

          MONOTONE_MAYCHANGE_TAC
        ]
      ];

      (* postcond! *)
      REWRITE_TAC[loop_rotate_eqout;SUB_REFL;MULT_0] THEN
      ENSURES2_INIT_TAC "s0" "s0'" THEN
      UNDISCH_THEN `k DIV 4 = k4` (fun th -> SUBST_ALL_TAC th THEN ASSUME_TAC th) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[eq_xregs;eq_qregs;mk_equiv_regs;BIGNUM_FROM_MEMORY_BYTES]) THEN
      REPEAT SPLIT_FIRST_CONJ_ASSUM_TAC THEN
      DESTRUCT_EXISTS_ASSUMS_TAC THEN
      ARM_STUTTER_RIGHT_TAC MADDLOOP_STEP3_FULL_EXEC [1] "'" None THEN
      REPEAT_N 2 ENSURES_FINAL_STATE'_TAC THEN
      CONJ_TAC THENL [
        SUBGOAL_THEN `(val (word (k4 - (k4 - 1 + 1)):int64) = 0)` (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
        [ SUBGOAL_THEN `k4 - (k4 - 1 + 1)=0` SUBST_ALL_TAC THENL [ASM_ARITH_TAC;ALL_TAC] THEN REWRITE_TAC[VAL_WORD_0]; ALL_TAC ] THEN
        REPLICATE_TAC 4 (CONJ_TAC THENL [FIRST_X_ASSUM MATCH_ACCEPT_TAC; ALL_TAC]) THEN
        SUBGOAL_THEN `8 * (k-4) = 8 * 4 * (k4-1)` SUBST_ALL_TAC THENL
        [ ASM_ARITH_TAC; ALL_TAC ] THEN
        REPLICATE_TAC 8 (CONJ_TAC THENL
          [FIRST_X_ASSUM MATCH_ACCEPT_TAC; ALL_TAC]) THEN
        REPLICATE_TAC 4 (CONJ_TAC THENL
          [ASM_MESON_TAC[BIGNUM_FROM_MEMORY_BYTES]; ALL_TAC]) THEN
        CONJ_TAC THENL [
          REWRITE_TAC[eq_xregs;eq_qregs;mk_equiv_regs] THEN
          ASM_MESON_TAC[];
          REWRITE_TAC[eq_xregs;eq_qregs;mk_equiv_regs] THEN
          ASM_MESON_TAC[]
        ];

        CONJ_TAC THENL [
          ASSUME_TAC (ISPECL [`p1:armstate`] MAYCHANGE_STARTER) THEN
          MONOTONE_MAYCHANGE_TAC;

          MONOTONE_MAYCHANGE_TAC
        ]
      ];

      (* loop trip count, left prog *)
      REWRITE_TAC[ADD_0;SUB_0;MULT_0;ADD_CLAUSES;NSUM_CONST_NUMSEG] THEN
      ASM_ARITH_TAC;

      (* loop trip count, right prog *)
      REWRITE_TAC[ADD_0;SUB_0;MULT_0;ADD_CLAUSES;NSUM_CONST_NUMSEG] THEN
      ASM_ARITH_TAC
    ] THEN

    REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN
    (* To avoid appearance of 'i-1' in memory accesses in the upcoming goal states..
       create i', which starts from 0. *)
    ABBREV_TAC `i' = i - 1` THEN
    SUBGOAL_THEN `i = i' + 1` SUBST_ALL_TAC THENL [ ASM_ARITH_TAC; ALL_TAC ] THEN
    FIRST_X_ASSUM (K ALL_TAC) THEN
    (* also replace k DIV 4 with k4. *)
    FIND_ABBREV_THEN "k4" SUBST_ALL_TAC THEN
    FIND_ABBREV_THEN "k" (SUBST_ALL_TAC o GSYM) THEN

    (* split 'bignum_from_memory (z,k) s = bignum_from_memory (z,k) s2' into three parts:
       1. bignum_from_memory (z,4*(i'+1)) s = ..
       2. bignum_from_memory (z+4*(i'+1),4) s = ..
       3. bignum_from_memory (z+4*(i'+2),k-4*(i'+2)) s = .. *)
    SUBGOAL_THEN `!(s:armstate) (s2:armstate).
        (exists a. bignum_from_memory (z:int64,4*k4) s = a /\ bignum_from_memory (z,4*k4) s2 = a)
        <=>
        ((exists a1. bignum_from_memory (z,4*(i'+1)) s = a1 /\ bignum_from_memory (z,4*(i'+1)) s2 = a1) /\
         (exists a2. bignum_from_memory (word_add z (word (8*4*(i'+1))),4) s = a2 /\
                     bignum_from_memory (word_add z (word (8*4*(i'+1))),4) s2 = a2) /\
         (exists a3. bignum_from_memory (word_add z (word (8*4*(i'+2))),4*k4-4*(i'+2)) s = a3 /\
                     bignum_from_memory (word_add z (word (8*4*(i'+2))),4*k4-4*(i'+2)) s2 = a3))`
        MP_TAC THENL [
      REPEAT STRIP_TAC THEN EQ_TAC THENL [
        STRIP_TAC THEN REPEAT CONJ_TAC THENL [
          SUBGOAL_THEN `MIN (4*k4) (4 * (i' + 1)) = 4 * (i' + 1)` ASSUME_TAC
          THENL [ ASM_ARITH_TAC; ALL_TAC] THEN
          ASM_MESON_TAC[LOWDIGITS_BIGNUM_FROM_MEMORY];

          REPLICATE_TAC 2 (TARGET_REWRITE_TAC[ARITH_RULE`4 = 4 * (i' + 2) - 4 * (i' + 1)`]
            (GSYM HIGHDIGITS_BIGNUM_FROM_MEMORY)) THEN
          SUBGOAL_THEN `MIN (4*k4) (4 * (i' + 2)) = 4 * (i' + 2)` ASSUME_TAC
          THENL [ ASM_ARITH_TAC; ALL_TAC] THEN
          ASM_MESON_TAC[LOWDIGITS_BIGNUM_FROM_MEMORY];

          REWRITE_TAC[GSYM HIGHDIGITS_BIGNUM_FROM_MEMORY] THEN
          ASM_MESON_TAC[]
        ];

        REPEAT STRIP_TAC THEN
        SUBGOAL_THEN `4 * k4 = (4 * (i' + 1)) + 4 + (4 * k4 - 4 * (i'+2))` SUBST1_TAC THENL [
          ASM_ARITH_TAC; ALL_TAC
        ] THEN
        REWRITE_TAC[BIGNUM_FROM_MEMORY_SPLIT] THEN
        REWRITE_TAC[WORD_ADD_ASSOC_CONSTS;ARITH_RULE`8 * 4 * (i' + 1) + 8 * 4 = 8*4*(i'+2)`] THEN
        ASM_MESON_TAC[]
      ];

      ALL_TAC
    ] THEN

    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES;eq_xregs;eq_qregs;mk_equiv_regs] THEN
    DISCH_THEN (LABEL_TAC "HSPLITTER") (* the 3 part splitter *) THEN
    SUBGOAL_THEN `(i' + 1) + 1 = i' + 2` SUBST_ALL_TAC THENL [ARITH_TAC;ALL_TAC] THEN

    (* start *)
    ENSURES2_INIT_TAC "s0" "s0'" THEN

    (* split the large z buffer in assumption. *)
    USE_THEN "HSPLITTER" (fun th -> REWRITE_TAC[th]) THEN
    UNDISCH_THEN `exists a.
          read (memory :> bytes (z,8 * 4 * k4)) s0 = a /\
          read (memory :> bytes (z,8 * 4 * k4)) s0' = a`
    (fun th -> REMOVE_THEN "HSPLITTER" (fun splitterth ->
      MP_TAC (REWRITE_RULE[splitterth] th) THEN STRIP_TAC THEN ASSUME_TAC th)) THEN

    (* To aid symbolic simulators on memory ops, gather all 'variable' parts into
       one, e.g., z + (8 * 4 * (i' + 1)) -> (z + 8 * 4 * i') + 32. *)
    RULE_ASSUM_TAC(REWRITE_RULE[
      WORD_RULE
        `word_add p (word (a * b * (c + d))) =
         word_add (word_add p (word (a*b*c))) (word (a*b*d)):(N)word`]) THEN
    REWRITE_TAC[WORD_RULE
        `word_add p (word (a * b * (c + d))) =
         word_add (word_add p (word (a*b*c))) (word (a*b*d)):(N)word`] THEN
    ABBREV_TAC `zi' = word_add z (word (8 * 4 * i')):int64` THEN
    ABBREV_TAC `mi' = word_add m (word (8 * 4 * i')):int64` THEN
    ABBREV_TAC `m_precalci' = word_add m_precalc (word (8 * 12 * i')):int64` THEN
    SUBGOAL_THEN `ALL (nonoverlapping (word_add zi' (word 32):int64,64))
        [(word pc2:int64, LENGTH maddloop_step3_full_mc);(word pc, LENGTH maddloop_step2_full_mc);
         (sp:int64,128); (m:int64,8*4*k4); (m_precalc:int64,8*12*(k4 - 1));
         (word_add mi' (word 32):int64,64); (m_precalci':int64,128);
         (z:int64,8*4*(i'+1))]`
        MP_TAC THENL [
      MAP_EVERY EXPAND_TAC ["zi'";"mi'";"m_precalci'"] THEN

      REWRITE_TAC[ALL; NONOVERLAPPING_CLAUSES;fst MADDLOOP_STEP2_FULL_EXEC;
                  fst MADDLOOP_STEP3_FULL_EXEC] THEN
      REPEAT (CONJ_TAC THENL [NONOVERLAPPING_TAC; ALL_TAC]) THEN NONOVERLAPPING_TAC;

      DISCH_THEN (fun th -> MP_TAC (
        REWRITE_RULE[ALL; NONOVERLAPPING_CLAUSES;fst MADDLOOP_STEP2_FULL_EXEC;
                    fst MADDLOOP_STEP3_FULL_EXEC] th)) THEN
      STRIP_TAC
    ] THEN

    (* Prepare the loaded values of 64 bit words at locations that simulator will read *)
    SUBGOAL_THEN
      `forall j. j < 4 ==> exists a1.
          read (memory :> bytes64 (word_add zi' (word (8 * (j + 6))))) s0 = a1 /\
          read (memory :> bytes64 (word_add zi' (word (8 * (j + 6))))) s0' = a1`
    MP_TAC THENL [
      REPEAT STRIP_TAC THEN EXPAND_TAC "zi'" THEN
      REWRITE_TAC[WORD_ADD_ASSOC_CONSTS;LEFT_ADD_DISTRIB] THEN

      MAP_EVERY (fun state_term ->
        MP_TAC (GSYM (SPECL [`4*k4:num`;`z:int64`;state_term;`4 * i' + (j + 6)`]
            BIGDIGIT_BIGNUM_FROM_MEMORY)) THEN
        COND_CASES_TAC THENL [ALL_TAC;
          FIRST_X_ASSUM MP_TAC THEN
          EVERY_ASSUM (fun th ->
            let c = concl th in
            if can (find_term (fun t -> is_const t && mem (name_of t) ["read";"nonoverlapping_modulo";"word_add"])) c
            then ALL_TAC else
            if exists (fun t -> mem t [`j:num`;`i':num`;`k4:num`]) (frees c)
            then MP_TAC th else ALL_TAC) THEN ARITH_TAC] THEN
        DISCH_THEN (fun th ->
          MP_TAC (REWRITE_RULE[VAL_WORD_GALOIS; DIMINDEX_64; BIGDIGIT_BOUND; LEFT_ADD_DISTRIB] th)) THEN
        DISCH_THEN SUBST1_TAC) [`s0:armstate`;`s0':armstate`] THEN

      ASM_MESON_TAC[BIGNUM_FROM_MEMORY_BYTES];

      ALL_TAC
    ] THEN
    CONV_TAC (LAND_CONV (EXPAND_CASES_CONV THENC REWRITE_CONV[LEFT_ADD_DISTRIB] THENC ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
    STRIP_TAC THEN

    SUBGOAL_THEN
      `forall j. j < 8 ==> exists a2.
          read (memory :> bytes64 (word_add mi' (word (8 * (j + 4))))) s0 = a2 /\
          read (memory :> bytes64 (word_add mi' (word (8 * (j + 4))))) s0' = a2`
    MP_TAC THENL [
      REPEAT STRIP_TAC THEN EXPAND_TAC "mi'" THEN
      REWRITE_TAC[WORD_ADD_ASSOC_CONSTS;LEFT_ADD_DISTRIB] THEN

      MAP_EVERY (fun state_term ->
        MP_TAC (GSYM (SPECL [`4*k4:num`;`m:int64`;state_term;`4 * i' + (j + 4)`]
            BIGDIGIT_BIGNUM_FROM_MEMORY)) THEN
        COND_CASES_TAC THENL [ALL_TAC;
          FIRST_X_ASSUM MP_TAC THEN
          EVERY_ASSUM (fun th ->
            let c = concl th in
            if can (find_term (fun t -> is_const t && mem (name_of t) ["read";"nonoverlapping_modulo";"word_add"])) c
            then ALL_TAC else
            if exists (fun t -> mem t [`j:num`;`i':num`;`k4:num`]) (frees c)
            then MP_TAC th else ALL_TAC) THEN ARITH_TAC] THEN
        DISCH_THEN (fun th ->
          MP_TAC (REWRITE_RULE[VAL_WORD_GALOIS; DIMINDEX_64; BIGDIGIT_BOUND; LEFT_ADD_DISTRIB] th)) THEN
        DISCH_THEN SUBST1_TAC) [`s0:armstate`;`s0':armstate`] THEN

      ASM_MESON_TAC[BIGNUM_FROM_MEMORY_BYTES];

      ALL_TAC
    ] THEN
    CONV_TAC (LAND_CONV (EXPAND_CASES_CONV THENC REWRITE_CONV[LEFT_ADD_DISTRIB] THENC ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
    STRIP_TAC THEN

    (* combine loads from X2 to q !! *)
    COMBINE_READ_BYTES64_PAIRS_TAC ~base_ptr:`mi':int64` THEN

    SUBGOAL_THEN
      `forall j. j < 12 ==> exists a3.
          read (memory :> bytes64 (word_add sp (word (32 + 8 * j)))) s0 = a3 /\
          read (memory :> bytes64 (word_add sp (word (32 + 8 * j)))) s0' = a3`
    MP_TAC THENL [
      REPEAT STRIP_TAC THEN

      MP_TAC (GSYM (SPECL [`12`;`word_add sp (word 32):int64`;`s0:armstate`;`j:num`]
          BIGDIGIT_BIGNUM_FROM_MEMORY)) THEN
      REWRITE_TAC[ASSUME `j < 12`] THEN
      DISCH_THEN (fun th ->
        MP_TAC (REWRITE_RULE[VAL_WORD_GALOIS; DIMINDEX_64; BIGDIGIT_BOUND;
          WORD_ADD_ASSOC_CONSTS] th)) THEN
      DISCH_THEN SUBST1_TAC THEN

      MP_TAC (GSYM (SPECL [`12`;`word_add sp (word 32):int64`;`s0':armstate`;`j:num`]
          BIGDIGIT_BIGNUM_FROM_MEMORY)) THEN
      REWRITE_TAC[ASSUME `j < 12`] THEN
      DISCH_THEN (fun th ->
        MP_TAC (REWRITE_RULE[VAL_WORD_GALOIS; DIMINDEX_64; BIGDIGIT_BOUND;
          WORD_ADD_ASSOC_CONSTS] th)) THEN
      DISCH_THEN SUBST1_TAC THEN

      ASM_MESON_TAC[BIGNUM_FROM_MEMORY_BYTES];

      ALL_TAC
    ] THEN
    CONV_TAC (LAND_CONV (EXPAND_CASES_CONV THENC REWRITE_CONV[LEFT_ADD_DISTRIB] THENC ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
    STRIP_TAC THEN

    SUBGOAL_THEN
      `forall j. j < 12 ==> exists a4.
          read (memory :> bytes64 (word_add m_precalci' (word (8*(j+4)))))
               s0 = a4 /\
          read (memory :> bytes64 (word_add m_precalci' (word (8*(j+4)))))
               s0' = a4`
    MP_TAC THENL [
      REPEAT STRIP_TAC THEN EXPAND_TAC "m_precalci'" THEN
      REWRITE_TAC[WORD_ADD_ASSOC_CONSTS;LEFT_ADD_DISTRIB] THEN

      SUBGOAL_THEN `12 * i' + j + 4 < 12 * (k4 - 1)` (LABEL_TAC "H") THENL [
        TRANS_TAC LT_TRANS `12 * i' + 16` THEN
        CONJ_TAC THENL [UNDISCH_TAC `j<12` THEN ARITH_TAC; ALL_TAC] THEN
        UNDISCH_TAC `i' + 1 < k4 - 1` THEN UNDISCH_TAC `1 <= i' + 1` THEN ARITH_TAC;
        ALL_TAC
      ] THEN

      MP_TAC (GSYM (SPECL [`12 * (k4 - 1)`;`m_precalc:int64`;`s0:armstate`;`12*i'+(j+4):num`]
          BIGDIGIT_BIGNUM_FROM_MEMORY)) THEN
      USE_THEN "H" (fun th -> REWRITE_TAC[th]) THEN
      DISCH_THEN (fun th ->
        MP_TAC (REWRITE_RULE[VAL_WORD_GALOIS; DIMINDEX_64; BIGDIGIT_BOUND; LEFT_ADD_DISTRIB] th)) THEN
      REWRITE_TAC[LEFT_ADD_DISTRIB] THEN
      DISCH_THEN SUBST1_TAC THEN

      MP_TAC (GSYM (SPECL [`12 * (k4 - 1)`;`m_precalc:int64`;`s0':armstate`;`12*i'+(j+4):num`]
          BIGDIGIT_BIGNUM_FROM_MEMORY)) THEN
      USE_THEN "H" (fun th -> REWRITE_TAC[th]) THEN
      DISCH_THEN (fun th ->
        MP_TAC (REWRITE_RULE[VAL_WORD_GALOIS; DIMINDEX_64; BIGDIGIT_BOUND; LEFT_ADD_DISTRIB] th)) THEN
      REWRITE_TAC[LEFT_ADD_DISTRIB] THEN
      DISCH_THEN SUBST1_TAC THEN

      ASM_MESON_TAC[BIGNUM_FROM_MEMORY_BYTES];

      ALL_TAC
    ] THEN
    CONV_TAC (LAND_CONV (EXPAND_CASES_CONV THENC REWRITE_CONV[LEFT_ADD_DISTRIB] THENC ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
    STRIP_TAC THEN

    RULE_ASSUM_TAC(CONV_RULE (DEPTH_CONV NUM_MULT_CONV)) THEN
    CONV_TAC (DEPTH_CONV NUM_MULT_CONV) THEN
    DESTRUCT_EXISTS_ASSUMS_TAC THEN

    (* loop counter is larger than 0. *)
    SUBGOAL_THEN `1 <= (k4 - (i' + 2))` (LABEL_TAC "HBOUND") THENL [
      UNDISCH_TAC `i' + 1 < k4 - 1` THEN ARITH_TAC;
      ALL_TAC
    ] THEN

    (W (fun (asl,g) ->
      let zi'_abbrev = ref (TAUT `T`) in
      (* EQUIV_STEPS_TAC cleans up abbreviations. cache zi'. *)
      FIND_ABBREV_THEN "zi'" (fun th -> zi'_abbrev := th; ALL_TAC) THEN
      EQUIV_STEPS_TAC [("equal",0,105,0,105)] MADDLOOP_STEP2_FULL_EXEC MADDLOOP_STEP3_FULL_EXEC THEN
      (* backedge! *)
      ARM_STUTTER_LEFT_TAC MADDLOOP_STEP2_FULL_EXEC [106;107] None THEN
      SUBGOAL_THEN `~(val (word_sub (word (k4 - (i' + 1))) (word 1):int64) = 0)` MP_TAC THENL [
        REWRITE_TAC[VAL_EQ_0] THEN
        IMP_REWRITE_TAC[MESON [WORD_SUB] `y <= x ==> word_sub (word x) (word y):int64 = word (x - y)`] THEN
        IMP_REWRITE_TAC[WORD_EQ_0;DIMINDEX_64] THEN
        REPEAT CONJ_TAC THENL [
          USE_THEN "HBOUND" MP_TAC THEN ARITH_TAC;
          UNDISCH_TAC `k4 < 2 EXP 59` THEN ARITH_TAC;
          USE_THEN "HBOUND" MP_TAC THEN ARITH_TAC
        ];

        DISCH_THEN (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN LABEL_TAC "HVALBOUND" th)
      ] THEN
      EQUIV_STEPS_TAC
        [("replace",108,109,106,107) (* use 'replace' because ldr's pointer writeback should not be abbreviated *);
        ("equal",109,147,107,145);
        ("replace",147,148,145,146);
        ("equal",148,150,146,148);
        ("replace",150,151,148,149);
        ("equal",151,152,149,150)] MADDLOOP_STEP2_FULL_EXEC MADDLOOP_STEP3_FULL_EXEC THEN
      ARM_STUTTER_RIGHT_TAC MADDLOOP_STEP3_FULL_EXEC [151] "'" None THEN
      (fun (asl,g) -> ASSUME_TAC !zi'_abbrev (asl,g)))) THEN

    REPEAT_N 2 ENSURES_FINAL_STATE'_TAC THEN
    (* Prove remaining clauses from the postcondition *)
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MESON[]`forall (a:A). exists x. a = x`] THEN
    CONJ_TAC THENL [
      REPEAT CONJ_TAC THENL [
        IMP_REWRITE_TAC[MESON [WORD_SUB] `y <= x ==> word_sub (word x) (word y):int64 = word (x - y)`] THEN
        REWRITE_TAC[WORD_EQ;DIMINDEX_64;CONG] THEN
        IMP_REWRITE_TAC[MOD_LT] THEN UNDISCH_TAC `k4 < 2 EXP 59` THEN USE_THEN "HBOUND" MP_TAC THEN
        ARITH_TAC;

        IMP_REWRITE_TAC[MESON [WORD_SUB] `y <= x ==> word_sub (word x) (word y):int64 = word (x - y)`] THEN
        REWRITE_TAC[WORD_EQ;DIMINDEX_64;CONG] THEN
        IMP_REWRITE_TAC[MOD_LT] THEN UNDISCH_TAC `k4 < 2 EXP 59` THEN USE_THEN "HBOUND" MP_TAC THEN
        ARITH_TAC;

        (* updates in zi': splitting now! *)
        REWRITE_TAC[ARITH_RULE`32=8*4`; GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
        REPEAT (ONCE_REWRITE_TAC[BIGNUM_FROM_MEMORY_EXPAND] THEN
                CHANGED_TAC (CONV_TAC (ONCE_DEPTH_CONV NUM_REDUCE_CONV))) THEN
        REWRITE_TAC[WORD_ADD_ASSOC_CONSTS] THEN CONV_TAC (ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
        ASM_REWRITE_TAC[] THEN MESON_TAC[]
      ];

      CONJ_TAC THENL [
        DISCARD_ASSUMPTIONS_TAC (fun th -> free_in `s0':armstate` (concl th)) THEN
        FIND_ABBREV_THEN "zi'" (SUBST_ALL_TAC o GSYM) THEN
        RULE_ASSUM_TAC(REWRITE_RULE[WORD_ADD_ASSOC_CONSTS]) THEN
        MONOTONE_MAYCHANGE_TAC;

        DISCARD_ASSUMPTIONS_TAC (fun th -> free_in `s0:armstate` (concl th)) THEN
        FIND_ABBREV_THEN "zi'" (SUBST_ALL_TAC o GSYM) THEN
        RULE_ASSUM_TAC(REWRITE_RULE[WORD_ADD_ASSOC_CONSTS]) THEN
        MONOTONE_MAYCHANGE_TAC;
      ]
    ]);;
