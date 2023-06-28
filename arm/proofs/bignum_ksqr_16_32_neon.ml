(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC
 *)

(* ========================================================================= *)
(* 16x16 -> 32 squaring, using Karatsuba reduction.                          *)
(* ========================================================================= *)

(**** print_literal_from_elf "arm/fastmul/bignum_ksqr_16_32_neon.o";;
 ****)

let bignum_ksqr_16_32_neon_mc = define_assert_from_elf
    "bignum_ksqr_16_32_neon_mc" "arm/fastmul/bignum_ksqr_16_32_neon.o"
[
  0xa9bf53f3;       (* arm_STP X19 X20 SP (Preimmediate_Offset (iword (-- &16))) *)
  0xa9bf5bf5;       (* arm_STP X21 X22 SP (Preimmediate_Offset (iword (-- &16))) *)
  0xa9bf63f7;       (* arm_STP X23 X24 SP (Preimmediate_Offset (iword (-- &16))) *)
  0xa9bf7bf9;       (* arm_STP X25 X30 SP (Preimmediate_Offset (iword (-- &16))) *)
  0xaa0003f7;       (* arm_MOV X23 X0 *)
  0xaa0103f8;       (* arm_MOV X24 X1 *)
  0xaa0203f9;       (* arm_MOV X25 X2 *)
  0x940000a9;       (* arm_BL (word 676) *)
  0xa9402f0a;       (* arm_LDP X10 X11 X24 (Immediate_Offset (iword (&0))) *)
  0xa9442708;       (* arm_LDP X8 X9 X24 (Immediate_Offset (iword (&64))) *)
  0xeb08014a;       (* arm_SUBS X10 X10 X8 *)
  0xfa09016b;       (* arm_SBCS X11 X11 X9 *)
  0xa941370c;       (* arm_LDP X12 X13 X24 (Immediate_Offset (iword (&16))) *)
  0xa9452708;       (* arm_LDP X8 X9 X24 (Immediate_Offset (iword (&80))) *)
  0xfa08018c;       (* arm_SBCS X12 X12 X8 *)
  0xfa0901ad;       (* arm_SBCS X13 X13 X9 *)
  0xa9423f0e;       (* arm_LDP X14 X15 X24 (Immediate_Offset (iword (&32))) *)
  0xa9462708;       (* arm_LDP X8 X9 X24 (Immediate_Offset (iword (&96))) *)
  0xfa0801ce;       (* arm_SBCS X14 X14 X8 *)
  0xfa0901ef;       (* arm_SBCS X15 X15 X9 *)
  0xa9434710;       (* arm_LDP X16 X17 X24 (Immediate_Offset (iword (&48))) *)
  0xa9472708;       (* arm_LDP X8 X9 X24 (Immediate_Offset (iword (&112))) *)
  0xfa080210;       (* arm_SBCS X16 X16 X8 *)
  0xfa090231;       (* arm_SBCS X17 X17 X9 *)
  0xda9f23f3;       (* arm_CSETM X19 Condition_CC *)
  0xab13027f;       (* arm_CMN X19 X19 *)
  0xca13014a;       (* arm_EOR X10 X10 X19 *)
  0xba1f014a;       (* arm_ADCS X10 X10 XZR *)
  0xca13016b;       (* arm_EOR X11 X11 X19 *)
  0xba1f016b;       (* arm_ADCS X11 X11 XZR *)
  0xa9002f2a;       (* arm_STP X10 X11 X25 (Immediate_Offset (iword (&0))) *)
  0xca13018c;       (* arm_EOR X12 X12 X19 *)
  0xba1f018c;       (* arm_ADCS X12 X12 XZR *)
  0xca1301ad;       (* arm_EOR X13 X13 X19 *)
  0xba1f01ad;       (* arm_ADCS X13 X13 XZR *)
  0xa901372c;       (* arm_STP X12 X13 X25 (Immediate_Offset (iword (&16))) *)
  0xca1301ce;       (* arm_EOR X14 X14 X19 *)
  0xba1f01ce;       (* arm_ADCS X14 X14 XZR *)
  0xca1301ef;       (* arm_EOR X15 X15 X19 *)
  0xba1f01ef;       (* arm_ADCS X15 X15 XZR *)
  0xa9023f2e;       (* arm_STP X14 X15 X25 (Immediate_Offset (iword (&32))) *)
  0xca130210;       (* arm_EOR X16 X16 X19 *)
  0xba1f0210;       (* arm_ADCS X16 X16 XZR *)
  0xca130231;       (* arm_EOR X17 X17 X19 *)
  0xba1f0231;       (* arm_ADCS X17 X17 XZR *)
  0xa9034730;       (* arm_STP X16 X17 X25 (Immediate_Offset (iword (&48))) *)
  0x910202e0;       (* arm_ADD X0 X23 (rvalue (word 128)) *)
  0x91010301;       (* arm_ADD X1 X24 (rvalue (word 64)) *)
  0x94000080;       (* arm_BL (word 512) *)
  0xa9482eea;       (* arm_LDP X10 X11 X23 (Immediate_Offset (iword (&128))) *)
  0xa94436ec;       (* arm_LDP X12 X13 X23 (Immediate_Offset (iword (&64))) *)
  0xab0c014a;       (* arm_ADDS X10 X10 X12 *)
  0xba0d016b;       (* arm_ADCS X11 X11 X13 *)
  0xa9082eea;       (* arm_STP X10 X11 X23 (Immediate_Offset (iword (&128))) *)
  0xa9492eea;       (* arm_LDP X10 X11 X23 (Immediate_Offset (iword (&144))) *)
  0xa94536ec;       (* arm_LDP X12 X13 X23 (Immediate_Offset (iword (&80))) *)
  0xba0c014a;       (* arm_ADCS X10 X10 X12 *)
  0xba0d016b;       (* arm_ADCS X11 X11 X13 *)
  0xa9092eea;       (* arm_STP X10 X11 X23 (Immediate_Offset (iword (&144))) *)
  0xa94a2eea;       (* arm_LDP X10 X11 X23 (Immediate_Offset (iword (&160))) *)
  0xa94636ec;       (* arm_LDP X12 X13 X23 (Immediate_Offset (iword (&96))) *)
  0xba0c014a;       (* arm_ADCS X10 X10 X12 *)
  0xba0d016b;       (* arm_ADCS X11 X11 X13 *)
  0xa90a2eea;       (* arm_STP X10 X11 X23 (Immediate_Offset (iword (&160))) *)
  0xa94b2eea;       (* arm_LDP X10 X11 X23 (Immediate_Offset (iword (&176))) *)
  0xa94736ec;       (* arm_LDP X12 X13 X23 (Immediate_Offset (iword (&112))) *)
  0xba0c014a;       (* arm_ADCS X10 X10 X12 *)
  0xba0d016b;       (* arm_ADCS X11 X11 X13 *)
  0xa90b2eea;       (* arm_STP X10 X11 X23 (Immediate_Offset (iword (&176))) *)
  0xa94c2eea;       (* arm_LDP X10 X11 X23 (Immediate_Offset (iword (&192))) *)
  0xba1f014a;       (* arm_ADCS X10 X10 XZR *)
  0xba1f016b;       (* arm_ADCS X11 X11 XZR *)
  0xa90c2eea;       (* arm_STP X10 X11 X23 (Immediate_Offset (iword (&192))) *)
  0xa94d2eea;       (* arm_LDP X10 X11 X23 (Immediate_Offset (iword (&208))) *)
  0xba1f014a;       (* arm_ADCS X10 X10 XZR *)
  0xba1f016b;       (* arm_ADCS X11 X11 XZR *)
  0xa90d2eea;       (* arm_STP X10 X11 X23 (Immediate_Offset (iword (&208))) *)
  0xa94e2eea;       (* arm_LDP X10 X11 X23 (Immediate_Offset (iword (&224))) *)
  0xba1f014a;       (* arm_ADCS X10 X10 XZR *)
  0xba1f016b;       (* arm_ADCS X11 X11 XZR *)
  0xa90e2eea;       (* arm_STP X10 X11 X23 (Immediate_Offset (iword (&224))) *)
  0xa94f2eea;       (* arm_LDP X10 X11 X23 (Immediate_Offset (iword (&240))) *)
  0xba1f014a;       (* arm_ADCS X10 X10 XZR *)
  0xba1f016b;       (* arm_ADCS X11 X11 XZR *)
  0xa90f2eea;       (* arm_STP X10 X11 X23 (Immediate_Offset (iword (&240))) *)
  0x91010320;       (* arm_ADD X0 X25 (rvalue (word 64)) *)
  0xaa1903e1;       (* arm_MOV X1 X25 *)
  0x94000059;       (* arm_BL (word 356) *)
  0xa94006e0;       (* arm_LDP X0 X1 X23 (Immediate_Offset (iword (&0))) *)
  0xa94846f0;       (* arm_LDP X16 X17 X23 (Immediate_Offset (iword (&128))) *)
  0xab100000;       (* arm_ADDS X0 X0 X16 *)
  0xba110021;       (* arm_ADCS X1 X1 X17 *)
  0xa9410ee2;       (* arm_LDP X2 X3 X23 (Immediate_Offset (iword (&16))) *)
  0xa94946f0;       (* arm_LDP X16 X17 X23 (Immediate_Offset (iword (&144))) *)
  0xba100042;       (* arm_ADCS X2 X2 X16 *)
  0xba110063;       (* arm_ADCS X3 X3 X17 *)
  0xa94216e4;       (* arm_LDP X4 X5 X23 (Immediate_Offset (iword (&32))) *)
  0xa94a46f0;       (* arm_LDP X16 X17 X23 (Immediate_Offset (iword (&160))) *)
  0xba100084;       (* arm_ADCS X4 X4 X16 *)
  0xba1100a5;       (* arm_ADCS X5 X5 X17 *)
  0xa9431ee6;       (* arm_LDP X6 X7 X23 (Immediate_Offset (iword (&48))) *)
  0xa94b46f0;       (* arm_LDP X16 X17 X23 (Immediate_Offset (iword (&176))) *)
  0xba1000c6;       (* arm_ADCS X6 X6 X16 *)
  0xba1100e7;       (* arm_ADCS X7 X7 X17 *)
  0xa94826e8;       (* arm_LDP X8 X9 X23 (Immediate_Offset (iword (&128))) *)
  0xa94c46f0;       (* arm_LDP X16 X17 X23 (Immediate_Offset (iword (&192))) *)
  0xba100108;       (* arm_ADCS X8 X8 X16 *)
  0xba110129;       (* arm_ADCS X9 X9 X17 *)
  0xa9492eea;       (* arm_LDP X10 X11 X23 (Immediate_Offset (iword (&144))) *)
  0xa94d46f0;       (* arm_LDP X16 X17 X23 (Immediate_Offset (iword (&208))) *)
  0xba10014a;       (* arm_ADCS X10 X10 X16 *)
  0xba11016b;       (* arm_ADCS X11 X11 X17 *)
  0xa94a36ec;       (* arm_LDP X12 X13 X23 (Immediate_Offset (iword (&160))) *)
  0xa94e46f0;       (* arm_LDP X16 X17 X23 (Immediate_Offset (iword (&224))) *)
  0xba10018c;       (* arm_ADCS X12 X12 X16 *)
  0xba1101ad;       (* arm_ADCS X13 X13 X17 *)
  0xa94b3eee;       (* arm_LDP X14 X15 X23 (Immediate_Offset (iword (&176))) *)
  0xa94f46f0;       (* arm_LDP X16 X17 X23 (Immediate_Offset (iword (&240))) *)
  0xba1001ce;       (* arm_ADCS X14 X14 X16 *)
  0xba1101ef;       (* arm_ADCS X15 X15 X17 *)
  0x9a9f37f8;       (* arm_CSET X24 Condition_CS *)
  0xa9444730;       (* arm_LDP X16 X17 X25 (Immediate_Offset (iword (&64))) *)
  0xeb100000;       (* arm_SUBS X0 X0 X16 *)
  0xfa110021;       (* arm_SBCS X1 X1 X17 *)
  0xa90406e0;       (* arm_STP X0 X1 X23 (Immediate_Offset (iword (&64))) *)
  0xa9454730;       (* arm_LDP X16 X17 X25 (Immediate_Offset (iword (&80))) *)
  0xfa100042;       (* arm_SBCS X2 X2 X16 *)
  0xfa110063;       (* arm_SBCS X3 X3 X17 *)
  0xa9050ee2;       (* arm_STP X2 X3 X23 (Immediate_Offset (iword (&80))) *)
  0xa9464730;       (* arm_LDP X16 X17 X25 (Immediate_Offset (iword (&96))) *)
  0xfa100084;       (* arm_SBCS X4 X4 X16 *)
  0xfa1100a5;       (* arm_SBCS X5 X5 X17 *)
  0xa90616e4;       (* arm_STP X4 X5 X23 (Immediate_Offset (iword (&96))) *)
  0xa9474730;       (* arm_LDP X16 X17 X25 (Immediate_Offset (iword (&112))) *)
  0xfa1000c6;       (* arm_SBCS X6 X6 X16 *)
  0xfa1100e7;       (* arm_SBCS X7 X7 X17 *)
  0xa9071ee6;       (* arm_STP X6 X7 X23 (Immediate_Offset (iword (&112))) *)
  0xa9484730;       (* arm_LDP X16 X17 X25 (Immediate_Offset (iword (&128))) *)
  0xfa100108;       (* arm_SBCS X8 X8 X16 *)
  0xfa110129;       (* arm_SBCS X9 X9 X17 *)
  0xa90826e8;       (* arm_STP X8 X9 X23 (Immediate_Offset (iword (&128))) *)
  0xa9494730;       (* arm_LDP X16 X17 X25 (Immediate_Offset (iword (&144))) *)
  0xfa10014a;       (* arm_SBCS X10 X10 X16 *)
  0xfa11016b;       (* arm_SBCS X11 X11 X17 *)
  0xa9092eea;       (* arm_STP X10 X11 X23 (Immediate_Offset (iword (&144))) *)
  0xa94a4730;       (* arm_LDP X16 X17 X25 (Immediate_Offset (iword (&160))) *)
  0xfa10018c;       (* arm_SBCS X12 X12 X16 *)
  0xfa1101ad;       (* arm_SBCS X13 X13 X17 *)
  0xa90a36ec;       (* arm_STP X12 X13 X23 (Immediate_Offset (iword (&160))) *)
  0xa94b4730;       (* arm_LDP X16 X17 X25 (Immediate_Offset (iword (&176))) *)
  0xfa1001ce;       (* arm_SBCS X14 X14 X16 *)
  0xfa1101ef;       (* arm_SBCS X15 X15 X17 *)
  0xa90b3eee;       (* arm_STP X14 X15 X23 (Immediate_Offset (iword (&176))) *)
  0xfa1f0318;       (* arm_SBCS X24 X24 XZR *)
  0xda9f23f9;       (* arm_CSETM X25 Condition_CC *)
  0xa94c2eea;       (* arm_LDP X10 X11 X23 (Immediate_Offset (iword (&192))) *)
  0xab18014a;       (* arm_ADDS X10 X10 X24 *)
  0xba19016b;       (* arm_ADCS X11 X11 X25 *)
  0xa90c2eea;       (* arm_STP X10 X11 X23 (Immediate_Offset (iword (&192))) *)
  0xa94d2eea;       (* arm_LDP X10 X11 X23 (Immediate_Offset (iword (&208))) *)
  0xba19014a;       (* arm_ADCS X10 X10 X25 *)
  0xba19016b;       (* arm_ADCS X11 X11 X25 *)
  0xa90d2eea;       (* arm_STP X10 X11 X23 (Immediate_Offset (iword (&208))) *)
  0xa94e2eea;       (* arm_LDP X10 X11 X23 (Immediate_Offset (iword (&224))) *)
  0xba19014a;       (* arm_ADCS X10 X10 X25 *)
  0xba19016b;       (* arm_ADCS X11 X11 X25 *)
  0xa90e2eea;       (* arm_STP X10 X11 X23 (Immediate_Offset (iword (&224))) *)
  0xa94f2eea;       (* arm_LDP X10 X11 X23 (Immediate_Offset (iword (&240))) *)
  0xba19014a;       (* arm_ADCS X10 X10 X25 *)
  0xba19016b;       (* arm_ADCS X11 X11 X25 *)
  0xa90f2eea;       (* arm_STP X10 X11 X23 (Immediate_Offset (iword (&240))) *)
  0xa8c17bf9;       (* arm_LDP X25 X30 SP (Postimmediate_Offset (iword (&16))) *)
  0xa8c163f7;       (* arm_LDP X23 X24 SP (Postimmediate_Offset (iword (&16))) *)
  0xa8c15bf5;       (* arm_LDP X21 X22 SP (Postimmediate_Offset (iword (&16))) *)
  0xa8c153f3;       (* arm_LDP X19 X20 SP (Postimmediate_Offset (iword (&16))) *)
  0xd65f03c0;       (* arm_RET X30 *)
  0xa9400c22;       (* arm_LDP X2 X3 X1 (Immediate_Offset (iword (&0))) *)
  0xa9411424;       (* arm_LDP X4 X5 X1 (Immediate_Offset (iword (&16))) *)
  0xa9421c26;       (* arm_LDP X6 X7 X1 (Immediate_Offset (iword (&32))) *)
  0xa9432428;       (* arm_LDP X8 X9 X1 (Immediate_Offset (iword (&48))) *)
  0x3dc00020;       (* arm_LDR Q0 X1 (Immediate_Offset (word 0)) *)
  0x9b047c51;       (* arm_MUL X17 X2 X4 *)
  0x3dc00427;       (* arm_LDR Q7 X1 (Immediate_Offset (word 16)) *)
  0x9b057c6e;       (* arm_MUL X14 X3 X5 *)
  0x6f00e5e4;       (* arm_MOVI Q4 (word 4294967295) *)
  0x9bc47c54;       (* arm_UMULH X20 X2 X4 *)
  0x6e004001;       (* arm_EXT Q1 Q0 Q0 64 *)
  0xeb030055;       (* arm_SUBS X21 X2 X3 *)
  0xda9526b5;       (* arm_CNEG X21 X21 Condition_CC *)
  0xda9f23eb;       (* arm_CSETM X11 Condition_CC *)
  0xeb0400ac;       (* arm_SUBS X12 X5 X4 *)
  0xda8c258c;       (* arm_CNEG X12 X12 Condition_CC *)
  0x0f208402;       (* arm_SHRN Q2 Q0 32 32 *)
  0x9b0c7ead;       (* arm_MUL X13 X21 X12 *)
  0x0e813800;       (* arm_ZIP1 Q0 Q0 Q1 32 64 *)
  0x9bcc7eac;       (* arm_UMULH X12 X21 X12 *)
  0x2ea2c045;       (* arm_UMULL_VEC Q5 Q2 Q2 32 *)
  0xda8b216b;       (* arm_CINV X11 X11 Condition_CC *)
  0x2ea0c046;       (* arm_UMULL_VEC Q6 Q2 Q0 32 *)
  0xca0b01ad;       (* arm_EOR X13 X13 X11 *)
  0x2ea0c003;       (* arm_UMULL_VEC Q3 Q0 Q0 32 *)
  0xca0b018c;       (* arm_EOR X12 X12 X11 *)
  0xab140233;       (* arm_ADDS X19 X17 X20 *)
  0x9a1f0294;       (* arm_ADC X20 X20 XZR *)
  0x4ea61cc1;       (* arm_MOV_VEC Q1 Q6 128 *)
  0x9bc57c75;       (* arm_UMULH X21 X3 X5 *)
  0x6f601461;       (* arm_USRA_VEC Q1 Q3 32 64 128 *)
  0xab0e0273;       (* arm_ADDS X19 X19 X14 *)
  0x4e241c24;       (* arm_AND_VEC Q4 Q1 Q4 128 *)
  0xba150294;       (* arm_ADCS X20 X20 X21 *)
  0x4ee68484;       (* arm_ADD_VEC Q4 Q4 Q6 64 128 *)
  0x9a1f02b5;       (* arm_ADC X21 X21 XZR *)
  0x6f601485;       (* arm_USRA_VEC Q5 Q4 32 64 128 *)
  0xab0e0294;       (* arm_ADDS X20 X20 X14 *)
  0x6f605483;       (* arm_SLI_VEC Q3 Q4 32 64 *)
  0x9a1f02b5;       (* arm_ADC X21 X21 XZR *)
  0x6f601425;       (* arm_USRA_VEC Q5 Q1 32 64 128 *)
  0xb100057f;       (* arm_CMN X11 (rvalue (word 1)) *)
  0x6f00e5e4;       (* arm_MOVI Q4 (word 4294967295) *)
  0xba0d0273;       (* arm_ADCS X19 X19 X13 *)
  0x6e0740e1;       (* arm_EXT Q1 Q7 Q7 64 *)
  0xba0c0294;       (* arm_ADCS X20 X20 X12 *)
  0x0f2084e2;       (* arm_SHRN Q2 Q7 32 32 *)
  0x9a0b02b5;       (* arm_ADC X21 X21 X11 *)
  0x0e8138e0;       (* arm_ZIP1 Q0 Q7 Q1 32 64 *)
  0xab110231;       (* arm_ADDS X17 X17 X17 *)
  0xba130273;       (* arm_ADCS X19 X19 X19 *)
  0xba140294;       (* arm_ADCS X20 X20 X20 *)
  0xba1502b5;       (* arm_ADCS X21 X21 X21 *)
  0x9a1f03ea;       (* arm_ADC X10 XZR XZR *)
  0x4e083c6c;       (* arm_UMOV X12 Q3 0 8 *)
  0x4e083cab;       (* arm_UMOV X11 Q5 0 8 *)
  0x9b037c4f;       (* arm_MUL X15 X2 X3 *)
  0x4e183c6d;       (* arm_UMOV X13 Q3 1 8 *)
  0x9bc37c50;       (* arm_UMULH X16 X2 X3 *)
  0x4e183cae;       (* arm_UMOV X14 Q5 1 8 *)
  0xab0f016b;       (* arm_ADDS X11 X11 X15 *)
  0x2ea2c045;       (* arm_UMULL_VEC Q5 Q2 Q2 32 *)
  0xba1001ad;       (* arm_ADCS X13 X13 X16 *)
  0x2ea0c046;       (* arm_UMULL_VEC Q6 Q2 Q0 32 *)
  0x9a1f01ce;       (* arm_ADC X14 X14 XZR *)
  0x2ea0c003;       (* arm_UMULL_VEC Q3 Q0 Q0 32 *)
  0xab0f016b;       (* arm_ADDS X11 X11 X15 *)
  0x4ea61cc1;       (* arm_MOV_VEC Q1 Q6 128 *)
  0xba1001ad;       (* arm_ADCS X13 X13 X16 *)
  0x6f601461;       (* arm_USRA_VEC Q1 Q3 32 64 128 *)
  0x9a1f01ce;       (* arm_ADC X14 X14 XZR *)
  0x4e241c24;       (* arm_AND_VEC Q4 Q1 Q4 128 *)
  0xa9002c0c;       (* arm_STP X12 X11 X0 (Immediate_Offset (iword (&0))) *)
  0x4ee68484;       (* arm_ADD_VEC Q4 Q4 Q6 64 128 *)
  0xab0d0231;       (* arm_ADDS X17 X17 X13 *)
  0x6f601485;       (* arm_USRA_VEC Q5 Q4 32 64 128 *)
  0xba0e0273;       (* arm_ADCS X19 X19 X14 *)
  0x6f605483;       (* arm_SLI_VEC Q3 Q4 32 64 *)
  0xba1f0294;       (* arm_ADCS X20 X20 XZR *)
  0x6f601425;       (* arm_USRA_VEC Q5 Q1 32 64 128 *)
  0xba1f02b5;       (* arm_ADCS X21 X21 XZR *)
  0x4e083c6c;       (* arm_UMOV X12 Q3 0 8 *)
  0x9a1f014a;       (* arm_ADC X10 X10 XZR *)
  0x4e083cab;       (* arm_UMOV X11 Q5 0 8 *)
  0xa9014c11;       (* arm_STP X17 X19 X0 (Immediate_Offset (iword (&16))) *)
  0x4e183c6d;       (* arm_UMOV X13 Q3 1 8 *)
  0x9b057c8f;       (* arm_MUL X15 X4 X5 *)
  0x4e183cae;       (* arm_UMOV X14 Q5 1 8 *)
  0x9bc57c90;       (* arm_UMULH X16 X4 X5 *)
  0x3dc00820;       (* arm_LDR Q0 X1 (Immediate_Offset (word 32)) *)
  0xab0f016b;       (* arm_ADDS X11 X11 X15 *)
  0x3dc00c27;       (* arm_LDR Q7 X1 (Immediate_Offset (word 48)) *)
  0xba1001ad;       (* arm_ADCS X13 X13 X16 *)
  0x9a1f01ce;       (* arm_ADC X14 X14 XZR *)
  0xab0f016b;       (* arm_ADDS X11 X11 X15 *)
  0xba1001ad;       (* arm_ADCS X13 X13 X16 *)
  0x9a1f01ce;       (* arm_ADC X14 X14 XZR *)
  0xab14018c;       (* arm_ADDS X12 X12 X20 *)
  0xba15016b;       (* arm_ADCS X11 X11 X21 *)
  0xa9022c0c;       (* arm_STP X12 X11 X0 (Immediate_Offset (iword (&32))) *)
  0xba0a01ad;       (* arm_ADCS X13 X13 X10 *)
  0x9a1f01ce;       (* arm_ADC X14 X14 XZR *)
  0xa903380d;       (* arm_STP X13 X14 X0 (Immediate_Offset (iword (&48))) *)
  0x9b087cd1;       (* arm_MUL X17 X6 X8 *)
  0x9b097cee;       (* arm_MUL X14 X7 X9 *)
  0x6f00e5e4;       (* arm_MOVI Q4 (word 4294967295) *)
  0x9bc87cd4;       (* arm_UMULH X20 X6 X8 *)
  0x6e004001;       (* arm_EXT Q1 Q0 Q0 64 *)
  0xeb0700d5;       (* arm_SUBS X21 X6 X7 *)
  0xda9526b5;       (* arm_CNEG X21 X21 Condition_CC *)
  0xda9f23eb;       (* arm_CSETM X11 Condition_CC *)
  0xeb08012c;       (* arm_SUBS X12 X9 X8 *)
  0xda8c258c;       (* arm_CNEG X12 X12 Condition_CC *)
  0x0f208402;       (* arm_SHRN Q2 Q0 32 32 *)
  0x9b0c7ead;       (* arm_MUL X13 X21 X12 *)
  0x0e813800;       (* arm_ZIP1 Q0 Q0 Q1 32 64 *)
  0x9bcc7eac;       (* arm_UMULH X12 X21 X12 *)
  0x2ea2c045;       (* arm_UMULL_VEC Q5 Q2 Q2 32 *)
  0xda8b216b;       (* arm_CINV X11 X11 Condition_CC *)
  0x2ea0c046;       (* arm_UMULL_VEC Q6 Q2 Q0 32 *)
  0xca0b01ad;       (* arm_EOR X13 X13 X11 *)
  0x2ea0c003;       (* arm_UMULL_VEC Q3 Q0 Q0 32 *)
  0xca0b018c;       (* arm_EOR X12 X12 X11 *)
  0xab140233;       (* arm_ADDS X19 X17 X20 *)
  0x9a1f0294;       (* arm_ADC X20 X20 XZR *)
  0x4ea61cc1;       (* arm_MOV_VEC Q1 Q6 128 *)
  0x9bc97cf5;       (* arm_UMULH X21 X7 X9 *)
  0x6f601461;       (* arm_USRA_VEC Q1 Q3 32 64 128 *)
  0xab0e0273;       (* arm_ADDS X19 X19 X14 *)
  0x4e241c24;       (* arm_AND_VEC Q4 Q1 Q4 128 *)
  0xba150294;       (* arm_ADCS X20 X20 X21 *)
  0x4ee68484;       (* arm_ADD_VEC Q4 Q4 Q6 64 128 *)
  0x9a1f02b5;       (* arm_ADC X21 X21 XZR *)
  0x6f601485;       (* arm_USRA_VEC Q5 Q4 32 64 128 *)
  0xab0e0294;       (* arm_ADDS X20 X20 X14 *)
  0x6f605483;       (* arm_SLI_VEC Q3 Q4 32 64 *)
  0x9a1f02b5;       (* arm_ADC X21 X21 XZR *)
  0x6f601425;       (* arm_USRA_VEC Q5 Q1 32 64 128 *)
  0xb100057f;       (* arm_CMN X11 (rvalue (word 1)) *)
  0x6f00e5e4;       (* arm_MOVI Q4 (word 4294967295) *)
  0xba0d0273;       (* arm_ADCS X19 X19 X13 *)
  0x6e0740e1;       (* arm_EXT Q1 Q7 Q7 64 *)
  0xba0c0294;       (* arm_ADCS X20 X20 X12 *)
  0x0f2084e2;       (* arm_SHRN Q2 Q7 32 32 *)
  0x9a0b02b5;       (* arm_ADC X21 X21 X11 *)
  0x0e8138e0;       (* arm_ZIP1 Q0 Q7 Q1 32 64 *)
  0xab110231;       (* arm_ADDS X17 X17 X17 *)
  0xba130273;       (* arm_ADCS X19 X19 X19 *)
  0xba140294;       (* arm_ADCS X20 X20 X20 *)
  0xba1502b5;       (* arm_ADCS X21 X21 X21 *)
  0x9a1f03ea;       (* arm_ADC X10 XZR XZR *)
  0x4e083c6c;       (* arm_UMOV X12 Q3 0 8 *)
  0x4e083cab;       (* arm_UMOV X11 Q5 0 8 *)
  0x9b077ccf;       (* arm_MUL X15 X6 X7 *)
  0x4e183c6d;       (* arm_UMOV X13 Q3 1 8 *)
  0x9bc77cd0;       (* arm_UMULH X16 X6 X7 *)
  0x4e183cae;       (* arm_UMOV X14 Q5 1 8 *)
  0xab0f016b;       (* arm_ADDS X11 X11 X15 *)
  0x2ea2c045;       (* arm_UMULL_VEC Q5 Q2 Q2 32 *)
  0xba1001ad;       (* arm_ADCS X13 X13 X16 *)
  0x2ea0c046;       (* arm_UMULL_VEC Q6 Q2 Q0 32 *)
  0x9a1f01ce;       (* arm_ADC X14 X14 XZR *)
  0x2ea0c003;       (* arm_UMULL_VEC Q3 Q0 Q0 32 *)
  0xab0f016b;       (* arm_ADDS X11 X11 X15 *)
  0x4ea61cc1;       (* arm_MOV_VEC Q1 Q6 128 *)
  0xba1001ad;       (* arm_ADCS X13 X13 X16 *)
  0x6f601461;       (* arm_USRA_VEC Q1 Q3 32 64 128 *)
  0x9a1f01ce;       (* arm_ADC X14 X14 XZR *)
  0x4e241c24;       (* arm_AND_VEC Q4 Q1 Q4 128 *)
  0xa9042c0c;       (* arm_STP X12 X11 X0 (Immediate_Offset (iword (&64))) *)
  0x4ee68484;       (* arm_ADD_VEC Q4 Q4 Q6 64 128 *)
  0xab0d0231;       (* arm_ADDS X17 X17 X13 *)
  0x6f601485;       (* arm_USRA_VEC Q5 Q4 32 64 128 *)
  0xba0e0273;       (* arm_ADCS X19 X19 X14 *)
  0x6f605483;       (* arm_SLI_VEC Q3 Q4 32 64 *)
  0xba1f0294;       (* arm_ADCS X20 X20 XZR *)
  0x6f601425;       (* arm_USRA_VEC Q5 Q1 32 64 128 *)
  0xba1f02b5;       (* arm_ADCS X21 X21 XZR *)
  0x4e083c6c;       (* arm_UMOV X12 Q3 0 8 *)
  0x9a1f014a;       (* arm_ADC X10 X10 XZR *)
  0x4e083cab;       (* arm_UMOV X11 Q5 0 8 *)
  0xa9054c11;       (* arm_STP X17 X19 X0 (Immediate_Offset (iword (&80))) *)
  0x4e183c6d;       (* arm_UMOV X13 Q3 1 8 *)
  0x9b097d0f;       (* arm_MUL X15 X8 X9 *)
  0x4e183cae;       (* arm_UMOV X14 Q5 1 8 *)
  0x9bc97d10;       (* arm_UMULH X16 X8 X9 *)
  0xab0f016b;       (* arm_ADDS X11 X11 X15 *)
  0xba1001ad;       (* arm_ADCS X13 X13 X16 *)
  0x9a1f01ce;       (* arm_ADC X14 X14 XZR *)
  0xab0f016b;       (* arm_ADDS X11 X11 X15 *)
  0xba1001ad;       (* arm_ADCS X13 X13 X16 *)
  0x9a1f01ce;       (* arm_ADC X14 X14 XZR *)
  0xab14018c;       (* arm_ADDS X12 X12 X20 *)
  0xba15016b;       (* arm_ADCS X11 X11 X21 *)
  0xa9062c0c;       (* arm_STP X12 X11 X0 (Immediate_Offset (iword (&96))) *)
  0xba0a01ad;       (* arm_ADCS X13 X13 X10 *)
  0x9a1f01ce;       (* arm_ADC X14 X14 XZR *)
  0xa907380d;       (* arm_STP X13 X14 X0 (Immediate_Offset (iword (&112))) *)
  0x9b067c4a;       (* arm_MUL X10 X2 X6 *)
  0x9b077c6e;       (* arm_MUL X14 X3 X7 *)
  0x9b087c8f;       (* arm_MUL X15 X4 X8 *)
  0x9b097cb0;       (* arm_MUL X16 X5 X9 *)
  0x9bc67c51;       (* arm_UMULH X17 X2 X6 *)
  0xab1101ce;       (* arm_ADDS X14 X14 X17 *)
  0x9bc77c71;       (* arm_UMULH X17 X3 X7 *)
  0xba1101ef;       (* arm_ADCS X15 X15 X17 *)
  0x9bc87c91;       (* arm_UMULH X17 X4 X8 *)
  0xba110210;       (* arm_ADCS X16 X16 X17 *)
  0x9bc97cb1;       (* arm_UMULH X17 X5 X9 *)
  0x9a1f0231;       (* arm_ADC X17 X17 XZR *)
  0xab0a01cb;       (* arm_ADDS X11 X14 X10 *)
  0xba0e01ee;       (* arm_ADCS X14 X15 X14 *)
  0xba0f020f;       (* arm_ADCS X15 X16 X15 *)
  0xba100230;       (* arm_ADCS X16 X17 X16 *)
  0x9a1103f1;       (* arm_ADC X17 XZR X17 *)
  0xab0a01cc;       (* arm_ADDS X12 X14 X10 *)
  0xba0b01ed;       (* arm_ADCS X13 X15 X11 *)
  0xba0e020e;       (* arm_ADCS X14 X16 X14 *)
  0xba0f022f;       (* arm_ADCS X15 X17 X15 *)
  0xba1003f0;       (* arm_ADCS X16 XZR X16 *)
  0x9a1103f1;       (* arm_ADC X17 XZR X17 *)
  0xeb050096;       (* arm_SUBS X22 X4 X5 *)
  0xda9626d6;       (* arm_CNEG X22 X22 Condition_CC *)
  0xda9f23f3;       (* arm_CSETM X19 Condition_CC *)
  0xeb080134;       (* arm_SUBS X20 X9 X8 *)
  0xda942694;       (* arm_CNEG X20 X20 Condition_CC *)
  0x9b147ed5;       (* arm_MUL X21 X22 X20 *)
  0x9bd47ed4;       (* arm_UMULH X20 X22 X20 *)
  0xda932273;       (* arm_CINV X19 X19 Condition_CC *)
  0xb100067f;       (* arm_CMN X19 (rvalue (word 1)) *)
  0xca1302b5;       (* arm_EOR X21 X21 X19 *)
  0xba1501ef;       (* arm_ADCS X15 X15 X21 *)
  0xca130294;       (* arm_EOR X20 X20 X19 *)
  0xba140210;       (* arm_ADCS X16 X16 X20 *)
  0x9a130231;       (* arm_ADC X17 X17 X19 *)
  0xeb030056;       (* arm_SUBS X22 X2 X3 *)
  0xda9626d6;       (* arm_CNEG X22 X22 Condition_CC *)
  0xda9f23f3;       (* arm_CSETM X19 Condition_CC *)
  0xeb0600f4;       (* arm_SUBS X20 X7 X6 *)
  0xda942694;       (* arm_CNEG X20 X20 Condition_CC *)
  0x9b147ed5;       (* arm_MUL X21 X22 X20 *)
  0x9bd47ed4;       (* arm_UMULH X20 X22 X20 *)
  0xda932273;       (* arm_CINV X19 X19 Condition_CC *)
  0xb100067f;       (* arm_CMN X19 (rvalue (word 1)) *)
  0xca1302b5;       (* arm_EOR X21 X21 X19 *)
  0xba15016b;       (* arm_ADCS X11 X11 X21 *)
  0xca130294;       (* arm_EOR X20 X20 X19 *)
  0xba14018c;       (* arm_ADCS X12 X12 X20 *)
  0xba1301ad;       (* arm_ADCS X13 X13 X19 *)
  0xba1301ce;       (* arm_ADCS X14 X14 X19 *)
  0xba1301ef;       (* arm_ADCS X15 X15 X19 *)
  0xba130210;       (* arm_ADCS X16 X16 X19 *)
  0x9a130231;       (* arm_ADC X17 X17 X19 *)
  0xeb050076;       (* arm_SUBS X22 X3 X5 *)
  0xda9626d6;       (* arm_CNEG X22 X22 Condition_CC *)
  0xda9f23f3;       (* arm_CSETM X19 Condition_CC *)
  0xeb070134;       (* arm_SUBS X20 X9 X7 *)
  0xda942694;       (* arm_CNEG X20 X20 Condition_CC *)
  0x9b147ed5;       (* arm_MUL X21 X22 X20 *)
  0x9bd47ed4;       (* arm_UMULH X20 X22 X20 *)
  0xda932273;       (* arm_CINV X19 X19 Condition_CC *)
  0xb100067f;       (* arm_CMN X19 (rvalue (word 1)) *)
  0xca1302b5;       (* arm_EOR X21 X21 X19 *)
  0xba1501ce;       (* arm_ADCS X14 X14 X21 *)
  0xca130294;       (* arm_EOR X20 X20 X19 *)
  0xba1401ef;       (* arm_ADCS X15 X15 X20 *)
  0xba130210;       (* arm_ADCS X16 X16 X19 *)
  0x9a130231;       (* arm_ADC X17 X17 X19 *)
  0xeb040056;       (* arm_SUBS X22 X2 X4 *)
  0xda9626d6;       (* arm_CNEG X22 X22 Condition_CC *)
  0xda9f23f3;       (* arm_CSETM X19 Condition_CC *)
  0xeb060114;       (* arm_SUBS X20 X8 X6 *)
  0xda942694;       (* arm_CNEG X20 X20 Condition_CC *)
  0x9b147ed5;       (* arm_MUL X21 X22 X20 *)
  0x9bd47ed4;       (* arm_UMULH X20 X22 X20 *)
  0xda932273;       (* arm_CINV X19 X19 Condition_CC *)
  0xb100067f;       (* arm_CMN X19 (rvalue (word 1)) *)
  0xca1302b5;       (* arm_EOR X21 X21 X19 *)
  0xba15018c;       (* arm_ADCS X12 X12 X21 *)
  0xca130294;       (* arm_EOR X20 X20 X19 *)
  0xba1401ad;       (* arm_ADCS X13 X13 X20 *)
  0xba1301ce;       (* arm_ADCS X14 X14 X19 *)
  0xba1301ef;       (* arm_ADCS X15 X15 X19 *)
  0xba130210;       (* arm_ADCS X16 X16 X19 *)
  0x9a130231;       (* arm_ADC X17 X17 X19 *)
  0xeb050056;       (* arm_SUBS X22 X2 X5 *)
  0xda9626d6;       (* arm_CNEG X22 X22 Condition_CC *)
  0xda9f23f3;       (* arm_CSETM X19 Condition_CC *)
  0xeb060134;       (* arm_SUBS X20 X9 X6 *)
  0xda942694;       (* arm_CNEG X20 X20 Condition_CC *)
  0x9b147ed5;       (* arm_MUL X21 X22 X20 *)
  0x9bd47ed4;       (* arm_UMULH X20 X22 X20 *)
  0xda932273;       (* arm_CINV X19 X19 Condition_CC *)
  0xb100067f;       (* arm_CMN X19 (rvalue (word 1)) *)
  0xca1302b5;       (* arm_EOR X21 X21 X19 *)
  0xba1501ad;       (* arm_ADCS X13 X13 X21 *)
  0xca130294;       (* arm_EOR X20 X20 X19 *)
  0xba1401ce;       (* arm_ADCS X14 X14 X20 *)
  0xba1301ef;       (* arm_ADCS X15 X15 X19 *)
  0xba130210;       (* arm_ADCS X16 X16 X19 *)
  0x9a130231;       (* arm_ADC X17 X17 X19 *)
  0xeb040076;       (* arm_SUBS X22 X3 X4 *)
  0xda9626d6;       (* arm_CNEG X22 X22 Condition_CC *)
  0xda9f23f3;       (* arm_CSETM X19 Condition_CC *)
  0xeb070114;       (* arm_SUBS X20 X8 X7 *)
  0xda942694;       (* arm_CNEG X20 X20 Condition_CC *)
  0x9b147ed5;       (* arm_MUL X21 X22 X20 *)
  0x9bd47ed4;       (* arm_UMULH X20 X22 X20 *)
  0xda932273;       (* arm_CINV X19 X19 Condition_CC *)
  0xb100067f;       (* arm_CMN X19 (rvalue (word 1)) *)
  0xca1302b5;       (* arm_EOR X21 X21 X19 *)
  0xba1501ad;       (* arm_ADCS X13 X13 X21 *)
  0xca130294;       (* arm_EOR X20 X20 X19 *)
  0xba1401ce;       (* arm_ADCS X14 X14 X20 *)
  0xba1301ef;       (* arm_ADCS X15 X15 X19 *)
  0xba130210;       (* arm_ADCS X16 X16 X19 *)
  0x9a130231;       (* arm_ADC X17 X17 X19 *)
  0xab0a014a;       (* arm_ADDS X10 X10 X10 *)
  0xba0b016b;       (* arm_ADCS X11 X11 X11 *)
  0xba0c018c;       (* arm_ADCS X12 X12 X12 *)
  0xba0d01ad;       (* arm_ADCS X13 X13 X13 *)
  0xba0e01ce;       (* arm_ADCS X14 X14 X14 *)
  0xba0f01ef;       (* arm_ADCS X15 X15 X15 *)
  0xba100210;       (* arm_ADCS X16 X16 X16 *)
  0xba110231;       (* arm_ADCS X17 X17 X17 *)
  0x9a1f03f3;       (* arm_ADC X19 XZR XZR *)
  0xa9420c02;       (* arm_LDP X2 X3 X0 (Immediate_Offset (iword (&32))) *)
  0xab02014a;       (* arm_ADDS X10 X10 X2 *)
  0xba03016b;       (* arm_ADCS X11 X11 X3 *)
  0xa9022c0a;       (* arm_STP X10 X11 X0 (Immediate_Offset (iword (&32))) *)
  0xa9430c02;       (* arm_LDP X2 X3 X0 (Immediate_Offset (iword (&48))) *)
  0xba02018c;       (* arm_ADCS X12 X12 X2 *)
  0xba0301ad;       (* arm_ADCS X13 X13 X3 *)
  0xa903340c;       (* arm_STP X12 X13 X0 (Immediate_Offset (iword (&48))) *)
  0xa9440c02;       (* arm_LDP X2 X3 X0 (Immediate_Offset (iword (&64))) *)
  0xba0201ce;       (* arm_ADCS X14 X14 X2 *)
  0xba0301ef;       (* arm_ADCS X15 X15 X3 *)
  0xa9043c0e;       (* arm_STP X14 X15 X0 (Immediate_Offset (iword (&64))) *)
  0xa9450c02;       (* arm_LDP X2 X3 X0 (Immediate_Offset (iword (&80))) *)
  0xba020210;       (* arm_ADCS X16 X16 X2 *)
  0xba030231;       (* arm_ADCS X17 X17 X3 *)
  0xa9054410;       (* arm_STP X16 X17 X0 (Immediate_Offset (iword (&80))) *)
  0xa9460c02;       (* arm_LDP X2 X3 X0 (Immediate_Offset (iword (&96))) *)
  0xba130042;       (* arm_ADCS X2 X2 X19 *)
  0xba1f0063;       (* arm_ADCS X3 X3 XZR *)
  0xa9060c02;       (* arm_STP X2 X3 X0 (Immediate_Offset (iword (&96))) *)
  0xa9470c02;       (* arm_LDP X2 X3 X0 (Immediate_Offset (iword (&112))) *)
  0xba1f0042;       (* arm_ADCS X2 X2 XZR *)
  0x9a1f0063;       (* arm_ADC X3 X3 XZR *)
  0xa9070c02;       (* arm_STP X2 X3 X0 (Immediate_Offset (iword (&112))) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_KSQR_16_32_NEON_EXEC = ARM_MK_EXEC_RULE bignum_ksqr_16_32_neon_mc;;

(* ------------------------------------------------------------------------- *)
(* First of all the correctness lemma for the embedded bignum_sqr_8_16       *)
(* ------------------------------------------------------------------------- *)

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

let ADK_48_TAC =
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
  CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN
  FIRST_ASSUM(MP_TAC o end_itlist CONJ o filter (is_ratconst o rand o concl) o
             DECARRY_RULE o CONJUNCTS) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;;


let WORD_BITMANIP_SIMP_LEMMAS = prove(
  `!(x32:(32)word) (y32:(32)word) (x32_2:(32)word)
        (x64:(64)word) (y64:(64)word) (x64_2:(64)word) (y64_2:(64)word)
        (y128:(128)word).
    // word_subword
    word_subword (word_subword y128 (0,64):(64)word) (0,32):(32)word =
      word_subword y128 (0,32):(32)word /\
    word_subword (word_subword y128 (64,64):(64)word) (0,32):(32)word =
      word_subword y128 (64,32):(32)word /\
    word_subword (word_subword y128 (0,64):(64)word) (32,32):(32)word =
      word_subword y128 (32,32):(32)word /\
    word_subword (word_subword y128 (64,64):(64)word) (32,32):(32)word =
      word_subword y128 (96,32):(32)word /\
    word_subword
        (word 79228162495817593524129366015:(128)word) (64,64):(64)word =
      word 4294967295 /\
    word_subword
        (word 79228162495817593524129366015:(128)word) (0,64):(64)word =
      word 4294967295 /\
    // .. + word_join
    word_subword (word_join x32 y32: (64)word) (0,32) = y32 /\
    word_subword (word_join x32 y32: (64)word) (32,32) = x32 /\
    word_subword (word_join x64 y64: (128)word) (0,64) = y64 /\
    word_subword (word_join x64 y64: (128)word) (64,64) = x64 /\
    word_subword (word_join x64 y64: (128)word) (0,32):(32)word =
      word_subword y64 (0,32):(32)word /\
    word_subword (word_join x64 y64: (128)word) (32,32):(32)word =
      word_subword y64 (32,32):(32)word /\
    word_subword (word_join x64 y64: (128)word) (64,32):(32)word =
      word_subword x64 (0,32):(32)word /\
    word_subword (word_join x64 y64: (128)word) (96,32):(32)word =
      word_subword x64 (32,32):(32)word /\
    word_subword
      (word_join
        (word_join x64_2 x64: (128)word)
        (word_join y64_2 y64: (128)word): (256)word)
      (64,128):(128)word = word_join x64 y64_2 /\
    // .. + word_zx
    word_subword (word_zx x64:(128)word) (0,32):(32)word = word_subword x64 (0,32) /\
    word_subword (word_subword x64 (0,128):(128)word) (0,32):(32)word = word_subword x64 (0,32) /\
    word_subword (word_zx x64:(128)word) (32,32):(32)word = word_subword x64 (32,32) /\
    word_subword (word_subword x64 (0,128):(128)word) (32,32):(32)word = word_subword x64 (32,32) /\
    // .. + word_and
    word_subword (word_and y128 (word_join x64_2 x64:(128)word)) (64,64) =
      word_and (word_subword y128 (64,64):(64)word) x64_2 /\
    word_subword (word_and y128 (word_join x64_2 x64:(128)word)) (0,64) =
      word_and (word_subword y128 (0,64):(64)word) x64 /\
    // .. + word_ushr
    word_zx (word_subword (word_ushr x64 32) (0,32):(32)word):(64)word = word_ushr x64 32 /\
    word_ushr (word_join x32_2 x32:(64)word) 32 = word_zx x32_2`,
  CONV_TAC WORD_BLAST);;

let WORD_OR_ADD_DISJ = prove(`! (x:(64)word) (y:(64)word).
    word_or (word_shl x 32) (word_and y (word 4294967295)) =
    word_add (word_shl x 32) (word_and y (word 4294967295))`,
  REPEAT GEN_TAC THEN
  IMP_REWRITE_TAC[WORD_ADD_OR] THEN
  CONV_TAC WORD_BLAST);;

let WORD_OF_BITS_32BITMASK = prove(
  `word 4294967295 = word_of_bits {i | i < 32}`,
  REWRITE_TAC [WORD_OF_BITS_MASK; ARITH_RULE `4294967295 = 2 EXP 32 - 1`]);;

let ADD_MOD_MOD_REFL = prove(`!a b m.
    (a + b MOD m) MOD m = (a + b) MOD m /\
    (a MOD m + b) MOD m = (a + b) MOD m`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC [GSYM (SPECL [`a:num`; `b:num`] MOD_ADD_MOD)] THEN
  REWRITE_TAC [MOD_MOD_REFL]);;

let LT_MULT_ADD_MULT = prove(`!a b c m. 0 < m /\ a < m /\ b < m /\ c <= m ==> c * a + b < m * m`,
  REPEAT STRIP_TAC THEN
  TRANS_TAC LET_TRANS `m * a + b` THEN
  CONJ_TAC THENL [
    IMP_REWRITE_TAC[LE_ADD2] THEN
    CONJ_TAC THENL [
      IMP_REWRITE_TAC[LE_MULT2] THEN
      REWRITE_TAC[LE_REFL];
      REWRITE_TAC[LE_REFL]];
    REPEAT STRIP_TAC THEN
    DISJ_CASES_THEN (LABEL_TAC "mcases") (SPECL [`m:num`] num_CASES) THENL [
      (* m = 0 *) SUBST_ALL_TAC (ASSUME `m = 0`) THEN
      RULE_ASSUM_TAC (REWRITE_RULE [GSYM ONE]) THEN
      REWRITE_TAC [GSYM ONE] THEN
      ASM_ARITH_TAC;
      (* m = n + 1 *) REMOVE_THEN "mcases" (CHOOSE_THEN (LABEL_TAC "mcases'")) THEN
      SUBST_ALL_TAC (ASSUME `m = SUC n`) THEN
      RULE_ASSUM_TAC (REWRITE_RULE [ADD1]) THEN
      REWRITE_TAC [ADD1] THEN
      REWRITE_TAC [ARITH_RULE `(n + 1) * (n + 1) = (n + 1) * n + (n + 1)`] THEN
      SUBGOAL_THEN `a <= n` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC LET_ADD2 THEN
      REWRITE_TAC [LE_MULT_LCANCEL] THEN
      ASM_MESON_TAC[]
    ]]);;

let LT_ADD_MULT_MULT = prove(`!a b c m. 0 < m /\ a < m /\ b < m /\ c <= m ==> b + c * a < m * m`,
  REPEAT STRIP_TAC THEN
  TRANS_TAC LET_TRANS `c * a + b` THEN
  CONJ_TAC THENL
    [ARITH_TAC; ASM_MESON_TAC[LT_MULT_ADD_MULT]]);;


let SPLIT_WORD64_TO_HILO: tactic =
  SUBST1_TAC (WORD_BLAST `(x:(64)word) =
        word_join (word_subword x (32,32):(32)word) (word_subword x (0,32):(32)word)`) THEN
  ABBREV_TAC `xh = word_subword (x:(64)word) (32,32):(32)word` THEN
  ABBREV_TAC `xl = word_subword (x:(64)word) (0,32):(32)word` THEN
  ASSUME_TAC (REWRITE_RULE [DIMINDEX_32] (ISPECL [`xh:(32)word`] VAL_BOUND)) THEN
  ASSUME_TAC (REWRITE_RULE [DIMINDEX_32] (ISPECL [`xl:(32)word`] VAL_BOUND));;

let WORD_SQR64_LOW = prove(`! (x:(64)word). word_or
    (word_shl
      (word_add
      (word_and (word 4294967295)
      (word_add
        (word_mul (word_ushr x 32) (word_zx (word_subword x (0,32):(32)word)))
      (word_ushr
        (word_mul (word_zx (word_subword x (0,32):(32)word))
        (word_zx (word_subword x (0,32):(32)word)))
      32)))
      (word_mul (word_ushr x 32) (word_zx (word_subword x (0,32):(32)word))))
    32)
    (word_and
      (word_mul (word_zx (word_subword x (0,32):(32)word))
      (word_zx (word_subword x (0,32):(32)word)))
    (word 4294967295)) = word_mul x x`,
  REPEAT GEN_TAC THEN
  SPLIT_WORD64_TO_HILO THEN
  REWRITE_TAC[WORD_BITMANIP_SIMP_LEMMAS] THEN
  REWRITE_TAC [GSYM VAL_EQ] THEN
  let r = REWRITE_TAC [VAL_WORD_ADD; VAL_WORD_MUL; VAL_WORD_ZX_GEN;
      VAL_WORD_SUBWORD; VAL_WORD; VAL_WORD_SHL; WORD_OF_BITS_32BITMASK;
      VAL_WORD_AND_MASK; VAL_WORD_USHR; VAL_WORD_JOIN; WORD_OR_ADD_DISJ] in
    (r THEN ONCE_REWRITE_TAC [WORD_RULE `word_and x y = word_and y x`] THEN r)
    THEN
  REWRITE_TAC[DIMINDEX_64; DIMINDEX_32;
      ARITH_RULE `MIN 32 32 = 32 /\ MIN 32 64 = 32 /\ MIN 64 32 = 32`;
      ARITH_RULE `2 EXP 0 = 1`; DIV_1; MOD_MOD_EXP_MIN] THEN
  REWRITE_TAC[ARITH_RULE `2 EXP 64 = 2 EXP 32 * 2 EXP 32`] THEN
  (* Remove redundant MODs *)
  (* |- !m n. m < n ==> m MOD n = m *)
  IMP_REWRITE_TAC [SPECL [`val (t:(32)word)`; `2 EXP 32 * 2 EXP 32`] MOD_LT] THEN
  IMP_REWRITE_TAC [ARITH_RULE `x < 2 EXP 32 ==> x < 2 EXP 32 * 2 EXP 32`] THEN
  IMP_REWRITE_TAC [SPECL
      [`val (t1:(32)word) * val (t2:(32)word)`; `2 EXP 32 * 2 EXP 32`] MOD_LT] THEN
  IMP_REWRITE_TAC [LT_MULT2] THEN
  IMP_REWRITE_TAC [SPECL
      [`2 EXP 32 * val (t1:(32)word) + val (t2:(32)word)`; `2 EXP 32 * 2 EXP 32`] MOD_LT] THEN
  IMP_REWRITE_TAC [LT_MULT_ADD_MULT; ARITH_RULE `0 < 2 EXP 32`; LE_REFL] THEN
  IMP_REWRITE_TAC [SPECL
      [`x MOD 2 EXP 32 + val (t1:(32)word) * val (t2:(32)word)`; `2 EXP 32 * 2 EXP 32`] MOD_LT] THEN
  IMP_REWRITE_TAC [LT_ADD_MULT_MULT; MOD_LT_EQ_LT; ARITH_RULE `0 < 2 EXP 32`; LE_LT] THEN
  (* |- !m n p. m MOD (n * p) = n * (m DIV n) MOD p + m MOD n *)
  REWRITE_TAC [MOD_MULT_MOD] THEN
  (* |- !m n. (m * n) MOD m = 0 *)
  REWRITE_TAC[MOD_MULT] THEN
  IMP_REWRITE_TAC[DIV_MULT] THEN
  REWRITE_TAC[ARITH_RULE `~(2 EXP 32 = 0)`; ADD_0] THEN
  IMP_REWRITE_TAC[DIV_MULT_ADD; MOD_DIV_EQ_0; ARITH_RULE `~(2 EXP 32 = 0)`; ADD_0; MOD_MOD_REFL] THEN
  REWRITE_TAC[MOD_MULT_ADD; MOD_MOD_REFL] THEN
  (* Now rewrite RHS *)
  REWRITE_TAC [ARITH_RULE `(x + y) * (z + w) = x * z + x * w + y * z + y * w`] THEN
  REWRITE_TAC [ARITH_RULE `(2 EXP 32 * w) * z = 2 EXP 32 * (w * z)`] THEN
  REWRITE_TAC [ARITH_RULE `val (k:(32)word) * (2 EXP 32 * z) = 2 EXP 32 * (val k * z)`] THEN
  IMP_REWRITE_TAC [DIV_MULT_ADD; MOD_MULT_ADD; ARITH_RULE `~(2 EXP 32 = 0)`] THEN
  REWRITE_TAC [ADD_MOD_MOD_REFL] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  AP_TERM_TAC THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  ARITH_TAC);;

let ADD_DIV_MOD_SIMP_LEMMA = prove(`!x y m.
    ~(m = 0) ==> (x MOD m + y) DIV m + x DIV m = (x + y) DIV m`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM (fun thm -> ASSUME_TAC (MATCH_MP (SPECL [`x:num`; `m:num`] DIVMOD_EXIST) thm)) THEN
  FIRST_X_ASSUM (fun thm -> CHOOSE_THEN (CHOOSE_THEN ASSUME_TAC) thm) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM ADD_ASSOC] THEN
  ASM_SIMP_TAC[MOD_MULT_ADD;DIV_MULT_ADD;MOD_LT;DIV_LT] THEN
  ARITH_TAC);;

let WORD_SQR64_HI = prove(`!(x:(64)word). word_add
  (word_add (word_mul (word_ushr x 32) (word_ushr x 32))
  (word_ushr
    (word_add
      (word_and
        (word 4294967295)
        (word_add
          (word_mul (word_ushr x 32) (word_zx (word_subword x (0,32):(32)word)))
          (word_ushr
            (word_mul (word_zx (word_subword x (0,32):(32)word))
            (word_zx (word_subword x (0,32):(32)word)))
          32)))
      (word_mul (word_ushr x 32) (word_zx (word_subword x (0,32):(32)word))))
    32))
  (word_ushr
    (word_add
      (word_mul (word_ushr x 32) (word_zx (word_subword x (0,32):(32)word)))
      (word_ushr
        (word_mul
          (word_zx (word_subword x (0,32):(32)word))
          (word_zx (word_subword x (0,32):(32)word)))
        32))
    32) =
  word ((val x * val x) DIV 2 EXP 64)`,
  GEN_TAC THEN
  SPLIT_WORD64_TO_HILO THEN
  REWRITE_TAC[WORD_BITMANIP_SIMP_LEMMAS] THEN
  REWRITE_TAC [GSYM VAL_EQ] THEN
  let r = REWRITE_TAC [VAL_WORD_ADD; VAL_WORD_MUL; VAL_WORD_ZX_GEN; VAL_WORD_SUBWORD; VAL_WORD; VAL_WORD_SHL; WORD_OF_BITS_32BITMASK; VAL_WORD_AND_MASK; VAL_WORD_USHR; VAL_WORD_JOIN; WORD_OR_ADD_DISJ] in (r THEN ONCE_REWRITE_TAC [WORD_RULE `word_and x y = word_and y x`] THEN r) THEN
  REWRITE_TAC[DIMINDEX_64; DIMINDEX_32; ARITH_RULE `MIN 32 32 = 32 /\ MIN 32 64 = 32 /\ MIN 64 32 = 32`; ARITH_RULE `2 EXP 0 = 1`; DIV_1; MOD_MOD_EXP_MIN] THEN
  REWRITE_TAC[ARITH_RULE `2 EXP 64 = 2 EXP 32 * 2 EXP 32`] THEN
  IMP_REWRITE_TAC [SPECL [`val (t:(32)word)`; `2 EXP 32 * 2 EXP 32`] MOD_LT] THEN
  IMP_REWRITE_TAC [ARITH_RULE `x < 2 EXP 32 ==> x < 2 EXP 32 * 2 EXP 32`] THEN
  IMP_REWRITE_TAC [SPECL [`val (t1:(32)word) * val (t2:(32)word)`; `2 EXP 32 * 2 EXP 32`] MOD_LT] THEN
  IMP_REWRITE_TAC [LT_MULT2] THEN
  IMP_REWRITE_TAC [SPECL [`2 EXP 32 * val (t1:(32)word) + val (t2:(32)word)`; `2 EXP 32 * 2 EXP 32`] MOD_LT] THEN
  IMP_REWRITE_TAC [LT_MULT_ADD_MULT; ARITH_RULE `0 < 2 EXP 32`; LE_REFL] THEN
  IMP_REWRITE_TAC [SPECL [`x MOD 2 EXP 32 + val (t1:(32)word) * val (t2:(32)word)`; `2 EXP 32 * 2 EXP 32`] MOD_LT] THEN
  IMP_REWRITE_TAC [LT_ADD_MULT_MULT; MOD_LT_EQ_LT; ARITH_RULE `0 < 2 EXP 32`; LE_LT] THEN
  IMP_REWRITE_TAC [SPECL [`val (t1:(32)word) * val (t2:(32)word) + t DIV 2 EXP 32`; `2 EXP 32 * 2 EXP 32`] MOD_LT] THEN
  IMP_REWRITE_TAC [LT_MULT_ADD_MULT; ARITH_RULE `0 < 2 EXP 32`] THEN
  IMP_REWRITE_TAC[RDIV_LT_EQ; ARITH_RULE `~(2 EXP 32 = 0)`; LE_LT; LT_MULT2] THEN
  IMP_REWRITE_TAC[LT_ADD_MULT_MULT; LE_LT; MOD_LT_EQ; ARITH_RULE `~(2 EXP 32 = 0)`; ARITH_RULE `0 < 2 EXP 32`] THEN
  (* Remove the outermost MOD 2^32*2^32 *)
  AP_THM_TAC THEN AP_TERM_TAC THEN
  (* Rerwite RHS first *)
  REWRITE_TAC [ARITH_RULE `(x + y) * (z + w) = x * z + x * w + y * z + y * w`] THEN
  REWRITE_TAC [ARITH_RULE `(2 EXP 32 * w) * z = 2 EXP 32 * (w * z)`] THEN
  REWRITE_TAC [ARITH_RULE `val (k:(32)word) * (2 EXP 32 * z) = 2 EXP 32 * (val k * z)`] THEN
  REWRITE_TAC[GSYM DIV_DIV] THEN
  IMP_REWRITE_TAC[DIV_MULT_ADD; ARITH_RULE `~(2 EXP 32 = 0)`] THEN
  (* strip 'xh * xh + ...' *)
  REWRITE_TAC[GSYM ADD_ASSOC] THEN AP_TERM_TAC THEN
  IMP_REWRITE_TAC[ADD_DIV_MOD_SIMP_LEMMA; ARITH_RULE `~(2 EXP 32 = 0)`] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  ARITH_TAC);;

let simplify_128bit_words =
  RULE_ASSUM_TAC (REWRITE_RULE [WORD_BITMANIP_SIMP_LEMMAS; WORD_SQR64_HI; WORD_SQR64_LOW]);;

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


let BIGNUM_KSQR_16_32_NEON_LEMMA = prove
 (`!z x a pc returnaddress.
      ALL (nonoverlapping (z,8 * 16))
          [(word pc,2108); (x,8 * 8)]
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word(pc + 0x0)) bignum_ksqr_16_32_neon_mc /\
                read PC s = word(pc + 0x2c0) /\
                read X30 s = returnaddress /\
                C_ARGUMENTS [z; x] s /\
                bignum_from_memory (x,8) s = a)
           (\s. read PC s = returnaddress /\
                bignum_from_memory (z,16) s = a EXP 2)
           (MAYCHANGE [PC; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12;
                       X13; X14; X15; X16; X17; X19; X20; X21; X22] ,,
            MAYCHANGE [Q0; Q1; Q2; Q3; Q4; Q5; Q6; Q7] ,,
            MAYCHANGE [memory :> bytes(z,8 * 16)] ,,
            MAYCHANGE SOME_FLAGS)`,
  REWRITE_TAC[ADD_CLAUSES] THEN
  MAP_EVERY X_GEN_TAC [`z:int64`; `x:int64`; `a:num`; `pc:num`; `returnaddress:int64`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; ALL; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_INIT_TAC "s0" THEN
  BIGNUM_DIGITIZE_TAC "x_" `bignum_from_memory (x,8) s0` THEN
  BYTES128_EQ_JOIN64_TAC `read (memory :> bytes128 x) s0` `x_1:(64)word` `x_0:(64)word` THEN
  BYTES128_EQ_JOIN64_TAC `read (memory :> bytes128 (word_add x (word 16:(64)word))) s0`
    `x_3:(64)word` `x_2:(64)word` THEN
  BYTES128_EQ_JOIN64_TAC `read (memory :> bytes128 (word_add x (word 32:(64)word))) s0`
    `x_5:(64)word` `x_4:(64)word` THEN
  BYTES128_EQ_JOIN64_TAC `read (memory :> bytes128 (word_add x (word 48:(64)word))) s0`
    `x_7:(64)word` `x_6:(64)word` THEN

  (*** First nested mini-ADK 4x4 squaring block ***)

  ARM_ACCSTEPS_TAC BIGNUM_KSQR_16_32_NEON_EXEC
    [6;8;18;27;28;32;34;36;38;40;44;46;48;50;51;52;53;54] (1--54) THEN
  ARM_NEON_ACCSTEPS_TAC BIGNUM_KSQR_16_32_NEON_EXEC [55] (55--55) THEN
  ARM_NEON_ACCSTEPS_TAC BIGNUM_KSQR_16_32_NEON_EXEC [] (56--56) THEN (* mov x11, v5.d[0] *)
  ARM_ACCSTEPS_TAC BIGNUM_KSQR_16_32_NEON_EXEC [57] (57--57) THEN (* mul x15, x2, x3 *)
  ARM_NEON_ACCSTEPS_TAC BIGNUM_KSQR_16_32_NEON_EXEC [58] (58--58) THEN (* mov x13, v3.d[1] *)
  ARM_ACCSTEPS_TAC BIGNUM_KSQR_16_32_NEON_EXEC [] (59--59) THEN (* umulh x16, x2, x3 *)
  ARM_NEON_ACCSTEPS_TAC BIGNUM_KSQR_16_32_NEON_EXEC [] (60--60) THEN (* mov x14, v5.d[1] *)
  simplify_128bit_words THEN (* The mov at line 60 must be simplified to be used in scalar code later *)
  ARM_ACCSTEPS_TAC BIGNUM_KSQR_16_32_NEON_EXEC
    [61;63;65;67;69;71;75;77;79;81] (61--81) THEN

  ARM_NEON_ACCSTEPS_TAC BIGNUM_KSQR_16_32_NEON_EXEC [82] (82--82) THEN (* mov x12, v3.d[0] = mul x12, x4, x4 *)
  ARM_ACCSTEPS_TAC BIGNUM_KSQR_16_32_NEON_EXEC [83] (83--83) THEN
  ARM_NEON_ACCSTEPS_TAC BIGNUM_KSQR_16_32_NEON_EXEC [] (84--84) THEN (* mov x11, v5.d[0] = umulh x11, x4, x4 *)
  simplify_128bit_words THEN (* simplify 84 *)
  ARM_ACCSTEPS_TAC BIGNUM_KSQR_16_32_NEON_EXEC [] (85--85) THEN
  ARM_NEON_ACCSTEPS_TAC BIGNUM_KSQR_16_32_NEON_EXEC [86] (86--86) THEN (* mov x13, v3.d[1] = mul x13, x5, x5 *)
  ARM_ACCSTEPS_TAC BIGNUM_KSQR_16_32_NEON_EXEC [87] (87--87) THEN
  ARM_NEON_ACCSTEPS_TAC BIGNUM_KSQR_16_32_NEON_EXEC [] (88--88) THEN (* mov x14, v5.d[1] = umulh x14, x5, x5 *)
  simplify_128bit_words THEN (* simplify 88 *)
  ARM_ACCSTEPS_TAC BIGNUM_KSQR_16_32_NEON_EXEC [] (89--89) THEN

  ARM_ACCSTEPS_TAC BIGNUM_KSQR_16_32_NEON_EXEC [91;93;94;95;96;97;98;99;101;102] (90--103) THEN

  SUBGOAL_THEN
   `bignum_of_wordlist [x_0;x_1;x_2;x_3] EXP 2 =
    bignum_of_wordlist [mullo_s55; sum_s67; sum_s75; sum_s77;
                        sum_s98; sum_s99; sum_s101; sum_s102]`
  ASSUME_TAC THENL
   [REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES; VAL_WORD_BITVAL]) THEN
    ADK_48_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN
    DISCARD_MATCHING_ASSUMPTIONS [`word a = b`]] THEN

  (*** Second nested mini-ADK 4x4 squaring block ***)

  ARM_ACCSTEPS_TAC BIGNUM_KSQR_16_32_NEON_EXEC
    [104;105;115;124;125;129;131;133;135;137;141;143;145;147;148;149;150;151]
    (104--151) THEN

  ARM_NEON_ACCSTEPS_TAC BIGNUM_KSQR_16_32_NEON_EXEC [152] (152--152) THEN
  ARM_NEON_ACCSTEPS_TAC BIGNUM_KSQR_16_32_NEON_EXEC [] (153--153) THEN
  ARM_ACCSTEPS_TAC BIGNUM_KSQR_16_32_NEON_EXEC [154] (154--154) THEN
  ARM_NEON_ACCSTEPS_TAC BIGNUM_KSQR_16_32_NEON_EXEC [155] (155--155) THEN

  ARM_ACCSTEPS_TAC BIGNUM_KSQR_16_32_NEON_EXEC [156] (156--156) THEN
  ARM_NEON_ACCSTEPS_TAC BIGNUM_KSQR_16_32_NEON_EXEC [] (157--157) THEN
  simplify_128bit_words THEN (* simplify 157 *)

  ARM_ACCSTEPS_TAC BIGNUM_KSQR_16_32_NEON_EXEC [158;160;162;164;166;168;172;174;176;178] (158--178) THEN

  ARM_NEON_ACCSTEPS_TAC BIGNUM_KSQR_16_32_NEON_EXEC [179] (179--179) THEN
  ARM_ACCSTEPS_TAC BIGNUM_KSQR_16_32_NEON_EXEC [180] (180--180) THEN
  ARM_NEON_ACCSTEPS_TAC BIGNUM_KSQR_16_32_NEON_EXEC [] (181--181) THEN
  simplify_128bit_words THEN (* simplify 181 *)
  ARM_ACCSTEPS_TAC BIGNUM_KSQR_16_32_NEON_EXEC [] (182--182) THEN
  ARM_NEON_ACCSTEPS_TAC BIGNUM_KSQR_16_32_NEON_EXEC [183] (183--183) THEN
  ARM_ACCSTEPS_TAC BIGNUM_KSQR_16_32_NEON_EXEC [184] (184--184) THEN
  ARM_NEON_ACCSTEPS_TAC BIGNUM_KSQR_16_32_NEON_EXEC [] (185--185) THEN
  simplify_128bit_words THEN (* simplify 185 *)
  ARM_ACCSTEPS_TAC BIGNUM_KSQR_16_32_NEON_EXEC [187;188;189;190;191;192;193;194;196;197] (186--198) THEN

  SUBGOAL_THEN
   `bignum_of_wordlist [x_4;x_5;x_6;x_7] EXP 2 =
    bignum_of_wordlist [mullo_s152;sum_s164;sum_s172;sum_s174;
                        sum_s193;sum_s194;sum_s196;sum_s197]`
  ASSUME_TAC THENL
    [REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES; VAL_WORD_BITVAL]) THEN
    ADK_48_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN
    DISCARD_MATCHING_ASSUMPTIONS [`word a = b`]] THEN

  (*** Nested ADK 4x4 multiplication block ***)

  ARM_ACCSTEPS_TAC BIGNUM_KSQR_16_32_NEON_EXEC
   [199;200;201;202;204;206;208;210;211;212;213;214;215;216;217;218;219;220;221;227;232;234;235;241;246;248;249;250;251;252;253;259;264;266;267;268;274;279;281;282;283;284;285;291;296;298;299;300;301;307;312;314;315;316;317]
   (199--317) THEN

  SUBGOAL_THEN
   `bignum_of_wordlist [x_0;x_1;x_2;x_3] *
    bignum_of_wordlist [x_4;x_5;x_6;x_7] =
    bignum_of_wordlist
     [mullo_s199; sum_s246; sum_s279; sum_s312;
      sum_s314; sum_s315; sum_s316; sum_s317]`
  ASSUME_TAC THENL
   [REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES; VAL_WORD_BITVAL]) THEN
    ADK_48_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN
    DISCARD_MATCHING_ASSUMPTIONS [`word a = b`]] THEN

  (*** Final accumulation simulation and 16-digit focusing ***)

  ARM_ACCSTEPS_TAC BIGNUM_KSQR_16_32_NEON_EXEC (318--350) (318--351) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  DISCARD_STATE_TAC "s351" THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
  MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
  MAP_EVERY EXISTS_TAC [`1024`; `&0:real`] THEN
  CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN CONJ_TAC THENL
   [EXPAND_TAC "a" THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN BOUNDER_TAC[];
    REWRITE_TAC[INTEGER_CLOSED]] THEN

  (*** The core rearrangement we are using ***)

  SUBGOAL_THEN
   `(&a:real) pow 2 =
    &(bignum_of_wordlist [x_0;x_1;x_2;x_3] EXP 2) +
    &2 pow 512 * &(bignum_of_wordlist [x_4;x_5;x_6;x_7] EXP 2) +
    &2 pow 257 * &(bignum_of_wordlist [x_0;x_1;x_2;x_3] *
                   bignum_of_wordlist [x_4;x_5;x_6;x_7])`
  SUBST1_TAC THENL
   [EXPAND_TAC "a" THEN
    REWRITE_TAC[bignum_of_wordlist; REAL_OF_NUM_CLAUSES] THEN ARITH_TAC;
    ASM_REWRITE_TAC[]] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES; VAL_WORD_BITVAL]) THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

let BIGNUM_KSQR_16_32_NEON_LEMMA_TAC =
  ARM_SUBROUTINE_SIM_TAC
    (bignum_ksqr_16_32_neon_mc,BIGNUM_KSQR_16_32_NEON_EXEC,
     0x0,bignum_ksqr_16_32_neon_mc,BIGNUM_KSQR_16_32_NEON_LEMMA)
    [`read X0 s`; `read X1 s`;
     `bignum_from_memory (read X1 s,8) s`;
     `pc:num`; `read X30 s`];;

(* ------------------------------------------------------------------------- *)
(* Now the main proof.                                                       *)
(* ------------------------------------------------------------------------- *)

let BIGNUM_KSQR_16_32_NEON_CORRECT = prove
 (`!z x a t pc.
        nonoverlapping (z,8 * 32) (t,8 * 24) /\
        ALLPAIRS nonoverlapping
         [(z,8 * 32); (t,8 * 24)]
         [(word pc,2108); (x,8 * 16)]
        ==> ensures arm
              (\s. aligned_bytes_loaded s (word pc) bignum_ksqr_16_32_neon_mc /\
                   read PC s = word(pc + 0x10) /\
                   C_ARGUMENTS [z; x; t] s /\
                   bignum_from_memory (x,16) s = a)
              (\s. read PC s = word (pc + 0x2ac) /\
                   bignum_from_memory (z,32) s = a EXP 2)
              (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10;
                          X11; X12; X13; X14; X15; X16; X17; X19; X20; X21;
                          X22; X23; X24; X25; X30] ,,
               MAYCHANGE [Q0; Q1; Q2; Q3; Q4; Q5; Q6; Q7] ,,
               MAYCHANGE [memory :> bytes(z,8 * 32);
                          memory :> bytes(t,8 * 24)] ,,
               MAYCHANGE SOME_FLAGS)`,
  MAP_EVERY X_GEN_TAC
   [`z:int64`; `x:int64`; `a:num`; `t:int64`;`pc:num`] THEN
  REWRITE_TAC[ALLPAIRS; ALL; PAIRWISE] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_INIT_TAC "s0" THEN
  BIGNUM_LDIGITIZE_TAC "x_" `bignum_from_memory (x,16) s0` THEN

  (*** First nested 8x8 squaring block ***)

  ARM_STEPS_TAC BIGNUM_KSQR_16_32_NEON_EXEC (1--4) THEN
  BIGNUM_KSQR_16_32_NEON_LEMMA_TAC 5 THEN
  BIGNUM_LDIGITIZE_TAC "l_" `read (memory :> bytes (z,8 * 16)) s5` THEN
  FIRST_X_ASSUM
   (MP_TAC o check (can (term_match [] `x = y EXP 2`) o concl)) THEN
  CONV_TAC(LAND_CONV(RAND_CONV(LAND_CONV BIGNUM_LEXPAND_CONV))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o SYM) THEN

  (*** Absolute difference computation ***)

  ARM_ACCSTEPS_TAC BIGNUM_KSQR_16_32_NEON_EXEC
   [8;9;12;13;16;17;20;21; 25;27;30;32;35;37;40;42] (6--43) THEN
  SUBGOAL_THEN
   `&(bignum_from_memory(t,8) s43):real =
    abs(&(bignum_of_wordlist [x_0;x_1;x_2;x_3;x_4;x_5;x_6;x_7]) -
        &(bignum_of_wordlist [x_8;x_9;x_10;x_11;x_12;x_13;x_14;x_15]))`
  MP_TAC THENL
   [MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
    MAP_EVERY EXISTS_TAC [`64 * 8`; `&0:real`] THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_CLAUSES; LE_0; BIGNUM_FROM_MEMORY_BOUND];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[REAL_ABS_POS] THEN MATCH_MP_TAC(REAL_ARITH
       `&x < e /\ &y < e ==> abs(&x - &y):real < e`) THEN
      REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN CONJ_TAC THEN
      MATCH_MP_TAC BIGNUM_OF_WORDLIST_BOUND THEN
      REWRITE_TAC[LENGTH] THEN ARITH_TAC;
      REWRITE_TAC[INTEGER_CLOSED]] THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_EXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
    REWRITE_TAC[REAL_OF_NUM_LT; REAL_ARITH
     `abs(&x - &y):real = if &x < &y then &y - &x else &x - &y`] THEN
    SUBGOAL_THEN
     `carry_s21 <=>
      bignum_of_wordlist [x_0;x_1;x_2;x_3;x_4;x_5;x_6;x_7] <
      bignum_of_wordlist [x_8;x_9;x_10;x_11;x_12;x_13;x_14;x_15]`
    (SUBST_ALL_TAC o SYM) THENL
     [MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN EXISTS_TAC `512` THEN
      REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
      REWRITE_TAC[REAL_BITVAL_NOT; REAL_VAL_WORD_MASK; DIMINDEX_64] THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
      REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
      REWRITE_TAC[WORD_UNMASK_64; WORD_XOR_MASK] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
      CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
      ASM_REWRITE_TAC[BITVAL_CLAUSES; REAL_VAL_WORD_NOT; DIMINDEX_64] THEN
      DISCH_THEN(MP_TAC o end_itlist CONJ o DESUM_RULE o CONJUNCTS) THEN
      REWRITE_TAC[REAL_BITVAL_NOT; REAL_VAL_WORD_MASK; DIMINDEX_64] THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC];
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN
    CONV_TAC(LAND_CONV(LAND_CONV(RAND_CONV BIGNUM_LEXPAND_CONV))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o SYM)] THEN

  (*** Second nested squaring ***)

  ARM_STEPS_TAC BIGNUM_KSQR_16_32_NEON_EXEC (44--46) THEN
  BIGNUM_KSQR_16_32_NEON_LEMMA_TAC 47 THEN
  BIGNUM_LDIGITIZE_TAC "h_"
   `read (memory :> bytes (word_add z (word 128),8 * 16)) s47` THEN
  FIRST_X_ASSUM
   (MP_TAC o check (can (term_match [] `x = y EXP 2`) o concl)) THEN
  CONV_TAC(LAND_CONV(RAND_CONV(LAND_CONV BIGNUM_LEXPAND_CONV))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o SYM) THEN

  (*** Computation of H' = H + L_top ***)

  ARM_ACCSTEPS_TAC BIGNUM_KSQR_16_32_NEON_EXEC
   [50;51;55;56;60;61;65;66;69;70;73;74;77;78;81;82] (48--83) THEN
  SUBGOAL_THEN
   `bignum_from_memory(word_add z (word 128),16) s83 =
    bignum_of_wordlist
     [h_0;h_1;h_2;h_3;h_4;h_5;h_6;h_7;h_8;h_9;h_10;h_11;h_12;h_13;h_14;h_15] +
    bignum_of_wordlist[l_8;l_9;l_10;l_11;l_12;l_13;l_14;l_15]`
  MP_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
    MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
    MAP_EVERY EXISTS_TAC [`64 * 16`; `&0:real`] THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_CLAUSES; LE_0; BIGNUM_FROM_MEMORY_BOUND];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_CLAUSES; LE_0] THEN FIRST_X_ASSUM(fun th ->
        GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [SYM th]) THEN
      REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
      CONV_TAC NUM_REDUCE_CONV THEN BOUNDER_TAC[];
      REWRITE_TAC[INTEGER_CLOSED]] THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_EXPAND_CONV) THEN
    ASM_REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN
    CONV_TAC(LAND_CONV(LAND_CONV BIGNUM_LEXPAND_CONV)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC] THEN

  (*** Third and final nested squaring ***)

  ARM_STEPS_TAC BIGNUM_KSQR_16_32_NEON_EXEC (84--86) THEN
  BIGNUM_KSQR_16_32_NEON_LEMMA_TAC 87 THEN
  BIGNUM_LDIGITIZE_TAC "m_"
   `read (memory :> bytes (word_add t (word 64),8 * 16)) s87` THEN
  FIRST_X_ASSUM
   (MP_TAC o check (can (term_match [] `x = y EXP 2`) o concl)) THEN
  CONV_TAC(LAND_CONV(RAND_CONV(LAND_CONV BIGNUM_LEXPAND_CONV))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o SYM) THEN

  (*** All remaining accumulation of sub-results ***)

  ARM_ACCSTEPS_TAC BIGNUM_KSQR_16_32_NEON_EXEC
   [90;91;94;95;98;99;102;103;106;107;110;111;114;115;118;119;
    122;123;126;127;130;131;134;135;138;139;142;143;146;147;150;151; 153;
    156;157;160;161;164;165;168;169]
   (88--170) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
  MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
  MAP_EVERY EXISTS_TAC [`64 * 32`; `&0:real`] THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_CLAUSES; LE_0] THEN
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES; BIGNUM_FROM_MEMORY_BOUND];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_CLAUSES; LE_0] THEN EXPAND_TAC "a" THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    CONV_TAC NUM_REDUCE_CONV THEN BOUNDER_TAC[];
    REWRITE_TAC[INTEGER_CLOSED]] THEN
  SUBGOAL_THEN
   `(&a:real) pow 2 =
    (&(bignum_of_wordlist[l_0; l_1; l_2; l_3; l_4; l_5; l_6; l_7]) +
     &2 pow 512 *
     &(bignum_of_wordlist
       [sum_s50; sum_s51; sum_s55; sum_s56; sum_s60; sum_s61; sum_s65;
        sum_s66; sum_s69; sum_s70; sum_s73; sum_s74; sum_s77; sum_s78;
        sum_s81; sum_s82])) *
    (&2 pow 512 + &1) -
    &2 pow 512 *
    &(bignum_of_wordlist
      [m_0; m_1; m_2; m_3; m_4; m_5; m_6; m_7; m_8; m_9; m_10; m_11; m_12;
       m_13; m_14; m_15])`
  SUBST1_TAC THENL
   [ASM_REWRITE_TAC[] THEN REWRITE_TAC[REAL_OF_NUM_CLAUSES; ARITH_RULE
     `l + e * (h + m):num = (l + e * m) + e * h`] THEN
    REWRITE_TAC[GSYM(BIGNUM_OF_WORDLIST_SPLIT_RULE(8,8))] THEN
    REPEAT(FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP (ARITH_RULE
     `x EXP 2 = y ==> y = x EXP 2`))) THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
    FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP (MESON[]
     `abs x:real = y ==> y = abs x`)) THEN
    REWRITE_TAC[REAL_POW2_ABS] THEN
    EXPAND_TAC "a" THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
  REWRITE_TAC[WORD_UNMASK_64; REAL_VAL_WORD_MASK; DIMINDEX_64;
              COND_SWAP; GSYM WORD_BITVAL; VAL_WORD_BITVAL] THEN
  DISCH_THEN(MP_TAC o end_itlist CONJ o DESUM_RULE o CONJUNCTS) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

let BIGNUM_KSQR_16_32_NEON_SUBROUTINE_CORRECT = prove
 (`!z x a t pc stackpointer returnaddress.
        aligned 16 stackpointer /\
        PAIRWISE nonoverlapping
         [(z,8 * 32); (t,8 * 24); (word_sub stackpointer (word 64),64)] /\
        ALLPAIRS nonoverlapping
         [(z,8 * 32); (t,8 * 24); (word_sub stackpointer (word 64),64)]
         [(word pc,2108); (x,8 * 16)]
        ==> ensures arm
              (\s. aligned_bytes_loaded s (word pc) bignum_ksqr_16_32_neon_mc /\
                   read PC s = word pc /\
                   read SP s = stackpointer /\
                   read X30 s = returnaddress /\
                   C_ARGUMENTS [z; x; t] s /\
                   bignum_from_memory (x,16) s = a)
              (\s. read PC s = returnaddress /\
                   bignum_from_memory (z,32) s = a EXP 2)
              (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
               MAYCHANGE [memory :> bytes(z,8 * 32);
                          memory :> bytes(t,8 * 24);
                     memory :> bytes(word_sub stackpointer (word 64),64)])`,
  ARM_ADD_RETURN_STACK_TAC
   BIGNUM_KSQR_16_32_NEON_EXEC BIGNUM_KSQR_16_32_NEON_CORRECT
    `[X19;X20;X21;X22;X23;X24;X25;X30]` 64);;
