(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Reduction of a bignum modulo another bignum, z := x mod m.                *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

(**** print_literal_from_elf "arm/generic/bignum_mod.o";;
 ****)

let bignum_mod_mc =
  define_assert_from_elf "bignum_mod_mc" "arm/generic/bignum_mod.o"
[
  0xa9bf53f3;       (* arm_STP X19 X20 SP (Preimmediate_Offset (iword (-- &16))) *)
  0xa9bf5bf5;       (* arm_STP X21 X22 SP (Preimmediate_Offset (iword (-- &16))) *)
  0xa9bf63f7;       (* arm_STP X23 X24 SP (Preimmediate_Offset (iword (-- &16))) *)
  0xaa1f03f7;       (* arm_MOV X23 XZR *)
  0xaa1f03e8;       (* arm_MOV X8 XZR *)
  0xf828783f;       (* arm_STR XZR X1 (Shiftreg_Offset X8 3) *)
  0x91000508;       (* arm_ADD X8 X8 (rvalue (word 1)) *)
  0xeb08001f;       (* arm_CMP X0 X8 *)
  0x54ffffa8;       (* arm_BHI (word 2097140) *)
  0xeb1f005f;       (* arm_CMP X2 XZR *)
  0x54002040;       (* arm_BEQ (word 1032) *)
  0xaa1f03e5;       (* arm_MOV X5 XZR *)
  0xaa1f03e6;       (* arm_MOV X6 XZR *)
  0xaa1f03eb;       (* arm_MOV X11 XZR *)
  0xaa1f03ea;       (* arm_MOV X10 XZR *)
  0xaa1f03e8;       (* arm_MOV X8 XZR *)
  0xb4000140;       (* arm_CBZ X0 (word 40) *)
  0xf8687887;       (* arm_LDR X7 X4 (Shiftreg_Offset X8 3) *)
  0xeb1f00ff;       (* arm_CMP X7 XZR *)
  0x9a8510e5;       (* arm_CSEL X5 X7 X5 Condition_NE *)
  0x9a861146;       (* arm_CSEL X6 X10 X6 Condition_NE *)
  0x9a8b110b;       (* arm_CSEL X11 X8 X11 Condition_NE *)
  0xaa0703ea;       (* arm_MOV X10 X7 *)
  0x91000508;       (* arm_ADD X8 X8 (rvalue (word 1)) *)
  0xeb00011f;       (* arm_CMP X8 X0 *)
  0x54ffff03;       (* arm_BCC (word 2097120) *)
  0xdac010a7;       (* arm_CLZ X7 X5 *)
  0xd37ae574;       (* arm_LSL X20 X11 6 *)
  0x91010294;       (* arm_ADD X20 X20 (rvalue (word 64)) *)
  0xcb070294;       (* arm_SUB X20 X20 X7 *)
  0x9ac720a5;       (* arm_LSLV X5 X5 X7 *)
  0xcb0703e7;       (* arm_NEG X7 X7 *)
  0x9ac724c6;       (* arm_LSRV X6 X6 X7 *)
  0xaa0600a6;       (* arm_ORR X6 X5 X6 *)
  0xeb1f00ff;       (* arm_CMP X7 XZR *)
  0x9a8600a5;       (* arm_CSEL X5 X5 X6 Condition_EQ *)
  0xb10004a5;       (* arm_ADDS X5 X5 (rvalue (word 1)) *)
  0xda8510a5;       (* arm_CINV X5 X5 Condition_EQ *)
  0xd350fca9;       (* arm_LSR X9 X5 16 *)
  0xd240c126;       (* arm_EOR X6 X9 (rvalue (word 562949953421311)) *)
  0x91000529;       (* arm_ADD X9 X9 (rvalue (word 1)) *)
  0xd360fcc6;       (* arm_LSR X6 X6 32 *)
  0x9b06fd35;       (* arm_MNEG X21 X9 X6 *)
  0xd371feab;       (* arm_LSR X11 X21 49 *)
  0x9b0b7d6b;       (* arm_MUL X11 X11 X11 *)
  0xd362feb5;       (* arm_LSR X21 X21 34 *)
  0x8b150175;       (* arm_ADD X21 X11 X21 *)
  0xb262016b;       (* arm_ORR X11 X11 (rvalue (word 1073741824)) *)
  0x9b0b7eab;       (* arm_MUL X11 X21 X11 *)
  0xd35efd6b;       (* arm_LSR X11 X11 30 *)
  0xd36284d5;       (* arm_LSL X21 X6 30 *)
  0x9b0b54c6;       (* arm_MADD X6 X6 X11 X21 *)
  0xd35efcc6;       (* arm_LSR X6 X6 30 *)
  0x9b06fd35;       (* arm_MNEG X21 X9 X6 *)
  0xd358feb5;       (* arm_LSR X21 X21 24 *)
  0x9b067eb5;       (* arm_MUL X21 X21 X6 *)
  0xd370bcc6;       (* arm_LSL X6 X6 16 *)
  0xd358feb5;       (* arm_LSR X21 X21 24 *)
  0x8b1500c6;       (* arm_ADD X6 X6 X21 *)
  0x9b06fd35;       (* arm_MNEG X21 X9 X6 *)
  0xd360feb5;       (* arm_LSR X21 X21 32 *)
  0x9b067eb5;       (* arm_MUL X21 X21 X6 *)
  0xd36180c6;       (* arm_LSL X6 X6 31 *)
  0xd351feb5;       (* arm_LSR X21 X21 17 *)
  0x8b1500c6;       (* arm_ADD X6 X6 X21 *)
  0x9b067cab;       (* arm_MUL X11 X5 X6 *)
  0x9bc67cb5;       (* arm_UMULH X21 X5 X6 *)
  0x93cbf2ab;       (* arm_EXTR X11 X21 X11 60 *)
  0xd361fcd5;       (* arm_LSR X21 X6 33 *)
  0xaa2b03eb;       (* arm_MVN X11 X11 *)
  0x9b0b7eab;       (* arm_MUL X11 X21 X11 *)
  0xd37ff8c6;       (* arm_LSL X6 X6 1 *)
  0xd361fd6b;       (* arm_LSR X11 X11 33 *)
  0x8b0b00c6;       (* arm_ADD X6 X6 X11 *)
  0xb10004cb;       (* arm_ADDS X11 X6 (rvalue (word 1)) *)
  0xda8b116b;       (* arm_CINV X11 X11 Condition_EQ *)
  0x9bcb7cb5;       (* arm_UMULH X21 X5 X11 *)
  0xab0502b5;       (* arm_ADDS X21 X21 X5 *)
  0x9a8b20d5;       (* arm_CSEL X21 X6 X11 Condition_CS *)
  0xd2958225;       (* arm_MOV X5 (rvalue (word 44049)) *)
  0xf2b9b465;       (* arm_MOVK X5 (word 52643) 16 *)
  0xf2c29f65;       (* arm_MOVK X5 (word 5371) 32 *)
  0xf2e192e5;       (* arm_MOVK X5 (word 3223) 48 *)
  0x9bc27ca5;       (* arm_UMULH X5 X5 X2 *)
  0x8b0200a5;       (* arm_ADD X5 X5 X2 *)
  0xd28007a6;       (* arm_MOV X6 (rvalue (word 61)) *)
  0x9b067ca5;       (* arm_MUL X5 X5 X6 *)
  0xd100f4a6;       (* arm_SUB X6 X5 (rvalue (word 61)) *)
  0xf24014bf;       (* arm_TST X5 (rvalue (word 63)) *)
  0x9a8610b0;       (* arm_CSEL X16 X5 X6 Condition_NE *)
  0xd28007b1;       (* arm_MOV X17 (rvalue (word 61)) *)
  0x91000405;       (* arm_ADD X5 X0 (rvalue (word 1)) *)
  0x9100fe26;       (* arm_ADD X6 X17 (rvalue (word 63)) *)
  0xd346fcc6;       (* arm_LSR X6 X6 6 *)
  0xeb0600bf;       (* arm_CMP X5 X6 *)
  0x9a8630b3;       (* arm_CSEL X19 X5 X6 Condition_CC *)
  0xd1000447;       (* arm_SUB X7 X2 (rvalue (word 1)) *)
  0xf8677876;       (* arm_LDR X22 X3 (Shiftreg_Offset X7 3) *)
  0x9ad026d6;       (* arm_LSRV X22 X22 X16 *)
  0xf9000036;       (* arm_STR X22 X1 (Immediate_Offset (word 0)) *)
  0x9ad426cf;       (* arm_LSRV X15 X22 X20 *)
  0xf101029f;       (* arm_CMP X20 (rvalue (word 64)) *)
  0x9a9f31ef;       (* arm_CSEL X15 X15 XZR Condition_CC *)
  0xd346fe8c;       (* arm_LSR X12 X20 6 *)
  0x9100058c;       (* arm_ADD X12 X12 (rvalue (word 1)) *)
  0xd100f610;       (* arm_SUB X16 X16 (rvalue (word 61)) *)
  0xd346fe09;       (* arm_LSR X9 X16 6 *)
  0xf8697865;       (* arm_LDR X5 X3 (Shiftreg_Offset X9 3) *)
  0x9100052b;       (* arm_ADD X11 X9 (rvalue (word 1)) *)
  0xeb02017f;       (* arm_CMP X11 X2 *)
  0x9a89316b;       (* arm_CSEL X11 X11 X9 Condition_CC *)
  0xf86b7866;       (* arm_LDR X6 X3 (Shiftreg_Offset X11 3) *)
  0x92401609;       (* arm_AND X9 X16 (rvalue (word 63)) *)
  0xcb0903eb;       (* arm_NEG X11 X9 *)
  0x9ac924a5;       (* arm_LSRV X5 X5 X9 *)
  0x9acb20c6;       (* arm_LSLV X6 X6 X11 *)
  0xaa0500c6;       (* arm_ORR X6 X6 X5 *)
  0xeb1f013f;       (* arm_CMP X9 XZR *)
  0x9a8600b6;       (* arm_CSEL X22 X5 X6 Condition_EQ *)
  0x9bcf7ea5;       (* arm_UMULH X5 X21 X15 *)
  0x8b0f00af;       (* arm_ADD X15 X5 X15 *)
  0xaa1f03ee;       (* arm_MOV X14 XZR *)
  0xd37df2d6;       (* arm_LSL X22 X22 3 *)
  0xaa0f03e5;       (* arm_MOV X5 X15 *)
  0xaa1f03e8;       (* arm_MOV X8 XZR *)
  0xf100066b;       (* arm_SUBS X11 X19 (rvalue (word 1)) *)
  0x54000260;       (* arm_BEQ (word 76) *)
  0xf8687887;       (* arm_LDR X7 X4 (Shiftreg_Offset X8 3) *)
  0xaa2703e7;       (* arm_MVN X7 X7 *)
  0x9b077de6;       (* arm_MUL X6 X15 X7 *)
  0x9bc77de9;       (* arm_UMULH X9 X15 X7 *)
  0xf868782a;       (* arm_LDR X10 X1 (Shiftreg_Offset X8 3) *)
  0xab05014a;       (* arm_ADDS X10 X10 X5 *)
  0x9a9f37e7;       (* arm_CSET X7 Condition_CS *)
  0xab06014a;       (* arm_ADDS X10 X10 X6 *)
  0x9a0900e5;       (* arm_ADC X5 X7 X9 *)
  0x93d60d56;       (* arm_EXTR X22 X10 X22 3 *)
  0xf8287836;       (* arm_STR X22 X1 (Shiftreg_Offset X8 3) *)
  0xeb0c011f;       (* arm_CMP X8 X12 *)
  0x9a8d32cd;       (* arm_CSEL X13 X22 X13 Condition_CC *)
  0x9a8e02ce;       (* arm_CSEL X14 X22 X14 Condition_EQ *)
  0xaa0a03f6;       (* arm_MOV X22 X10 *)
  0x91000508;       (* arm_ADD X8 X8 (rvalue (word 1)) *)
  0xeb0b011f;       (* arm_CMP X8 X11 *)
  0x54fffde1;       (* arm_BNE (word 2097084) *)
  0xaa1f03e7;       (* arm_MOV X7 XZR *)
  0xeb00011f;       (* arm_CMP X8 X0 *)
  0x54000040;       (* arm_BEQ (word 8) *)
  0xf8687887;       (* arm_LDR X7 X4 (Shiftreg_Offset X8 3) *)
  0xaa2703e7;       (* arm_MVN X7 X7 *)
  0x9b077de6;       (* arm_MUL X6 X15 X7 *)
  0xeb00011f;       (* arm_CMP X8 X0 *)
  0x540000c1;       (* arm_BNE (word 24) *)
  0x8b0502ea;       (* arm_ADD X10 X23 X5 *)
  0x8b06014a;       (* arm_ADD X10 X10 X6 *)
  0x93d60d56;       (* arm_EXTR X22 X10 X22 3 *)
  0xaa1603f7;       (* arm_MOV X23 X22 *)
  0x14000006;       (* arm_B (word 24) *)
  0xf868782a;       (* arm_LDR X10 X1 (Shiftreg_Offset X8 3) *)
  0x8b05014a;       (* arm_ADD X10 X10 X5 *)
  0x8b06014a;       (* arm_ADD X10 X10 X6 *)
  0x93d60d56;       (* arm_EXTR X22 X10 X22 3 *)
  0xf8287836;       (* arm_STR X22 X1 (Shiftreg_Offset X8 3) *)
  0xeb0c011f;       (* arm_CMP X8 X12 *)
  0x9a8d32cd;       (* arm_CSEL X13 X22 X13 Condition_CC *)
  0x9a8e02ce;       (* arm_CSEL X14 X22 X14 Condition_EQ *)
  0x91000508;       (* arm_ADD X8 X8 (rvalue (word 1)) *)
  0x9100f631;       (* arm_ADD X17 X17 (rvalue (word 61)) *)
  0x91000405;       (* arm_ADD X5 X0 (rvalue (word 1)) *)
  0x9100fe26;       (* arm_ADD X6 X17 (rvalue (word 63)) *)
  0xd346fcc6;       (* arm_LSR X6 X6 6 *)
  0xeb0600bf;       (* arm_CMP X5 X6 *)
  0x9a8630b3;       (* arm_CSEL X19 X5 X6 Condition_CC *)
  0xeb13011f;       (* arm_CMP X8 X19 *)
  0x54000160;       (* arm_BEQ (word 44) *)
  0xd343fd56;       (* arm_LSR X22 X10 3 *)
  0xeb00011f;       (* arm_CMP X8 X0 *)
  0x54000061;       (* arm_BNE (word 12) *)
  0xaa1603f7;       (* arm_MOV X23 X22 *)
  0x14000002;       (* arm_B (word 8) *)
  0xf8287836;       (* arm_STR X22 X1 (Shiftreg_Offset X8 3) *)
  0xeb0c011f;       (* arm_CMP X8 X12 *)
  0x9a8d32cd;       (* arm_CSEL X13 X22 X13 Condition_CC *)
  0x9a8e02ce;       (* arm_CSEL X14 X22 X14 Condition_EQ *)
  0x91000508;       (* arm_ADD X8 X8 (rvalue (word 1)) *)
  0xeb0c011f;       (* arm_CMP X8 X12 *)
  0x9a9f21ad;       (* arm_CSEL X13 X13 XZR Condition_CS *)
  0x9a8d02cd;       (* arm_CSEL X13 X22 X13 Condition_EQ *)
  0x92401685;       (* arm_AND X5 X20 (rvalue (word 63)) *)
  0xcb0503e6;       (* arm_NEG X6 X5 *)
  0x9ac525ad;       (* arm_LSRV X13 X13 X5 *)
  0x9ac621ce;       (* arm_LSLV X14 X14 X6 *)
  0xaa0d01ce;       (* arm_ORR X14 X14 X13 *)
  0xf10000bf;       (* arm_CMP X5 (rvalue (word 0)) *)
  0x9a8e01af;       (* arm_CSEL X15 X13 X14 Condition_EQ *)
  0xb5fff4d0;       (* arm_CBNZ X16 (word 2096792) *)
  0x9bcf7ea5;       (* arm_UMULH X5 X21 X15 *)
  0x8b0f00af;       (* arm_ADD X15 X5 X15 *)
  0xaa0f03e5;       (* arm_MOV X5 X15 *)
  0xaa1f03e8;       (* arm_MOV X8 XZR *)
  0x91000e94;       (* arm_ADD X20 X20 (rvalue (word 3)) *)
  0xd346fe8c;       (* arm_LSR X12 X20 6 *)
  0xaa1f03ed;       (* arm_MOV X13 XZR *)
  0xaa1f03ee;       (* arm_MOV X14 XZR *)
  0xb4000220;       (* arm_CBZ X0 (word 68) *)
  0xf8687887;       (* arm_LDR X7 X4 (Shiftreg_Offset X8 3) *)
  0xaa2703e7;       (* arm_MVN X7 X7 *)
  0x9b077de6;       (* arm_MUL X6 X15 X7 *)
  0x9bc77de9;       (* arm_UMULH X9 X15 X7 *)
  0xf868782a;       (* arm_LDR X10 X1 (Shiftreg_Offset X8 3) *)
  0xab05014a;       (* arm_ADDS X10 X10 X5 *)
  0x9a9f37e7;       (* arm_CSET X7 Condition_CS *)
  0xab06014a;       (* arm_ADDS X10 X10 X6 *)
  0x9a0900e5;       (* arm_ADC X5 X7 X9 *)
  0xf828782a;       (* arm_STR X10 X1 (Shiftreg_Offset X8 3) *)
  0xeb0c011f;       (* arm_CMP X8 X12 *)
  0x9a8d314d;       (* arm_CSEL X13 X10 X13 Condition_CC *)
  0x9a8e014e;       (* arm_CSEL X14 X10 X14 Condition_EQ *)
  0x91000508;       (* arm_ADD X8 X8 (rvalue (word 1)) *)
  0xeb00011f;       (* arm_CMP X8 X0 *)
  0x54fffe21;       (* arm_BNE (word 2097092) *)
  0xcb0f00a5;       (* arm_SUB X5 X5 X15 *)
  0xaa1703ea;       (* arm_MOV X10 X23 *)
  0x8b05014a;       (* arm_ADD X10 X10 X5 *)
  0xaa0a03f7;       (* arm_MOV X23 X10 *)
  0xeb0c011f;       (* arm_CMP X8 X12 *)
  0x9a8d314d;       (* arm_CSEL X13 X10 X13 Condition_CC *)
  0x9a8e014e;       (* arm_CSEL X14 X10 X14 Condition_EQ *)
  0x92401685;       (* arm_AND X5 X20 (rvalue (word 63)) *)
  0xcb0503e6;       (* arm_NEG X6 X5 *)
  0x9ac525ad;       (* arm_LSRV X13 X13 X5 *)
  0x9ac621ce;       (* arm_LSLV X14 X14 X6 *)
  0xaa0d01ce;       (* arm_ORR X14 X14 X13 *)
  0xf10000bf;       (* arm_CMP X5 (rvalue (word 0)) *)
  0x9a8e01af;       (* arm_CSEL X15 X13 X14 Condition_EQ *)
  0x9bcf7ea5;       (* arm_UMULH X5 X21 X15 *)
  0x8b0f00af;       (* arm_ADD X15 X5 X15 *)
  0xd37dfdef;       (* arm_LSR X15 X15 61 *)
  0x910005ef;       (* arm_ADD X15 X15 (rvalue (word 1)) *)
  0xaa0f03e5;       (* arm_MOV X5 X15 *)
  0xab1f03e8;       (* arm_ADDS X8 XZR XZR *)
  0xb40001a0;       (* arm_CBZ X0 (word 52) *)
  0xf8687887;       (* arm_LDR X7 X4 (Shiftreg_Offset X8 3) *)
  0xaa2703e7;       (* arm_MVN X7 X7 *)
  0x9b077de6;       (* arm_MUL X6 X15 X7 *)
  0x9bc77de9;       (* arm_UMULH X9 X15 X7 *)
  0xf868782a;       (* arm_LDR X10 X1 (Shiftreg_Offset X8 3) *)
  0xba05014a;       (* arm_ADCS X10 X10 X5 *)
  0x9a1f0125;       (* arm_ADC X5 X9 XZR *)
  0xab06014a;       (* arm_ADDS X10 X10 X6 *)
  0xf828782a;       (* arm_STR X10 X1 (Shiftreg_Offset X8 3) *)
  0x91000508;       (* arm_ADD X8 X8 (rvalue (word 1)) *)
  0xcb000107;       (* arm_SUB X7 X8 X0 *)
  0xb5fffea7;       (* arm_CBNZ X7 (word 2097108) *)
  0xaa1703ea;       (* arm_MOV X10 X23 *)
  0x9a05014a;       (* arm_ADC X10 X10 X5 *)
  0xeb0f015f;       (* arm_CMP X10 X15 *)
  0xda9f23e9;       (* arm_CSETM X9 Condition_CC *)
  0xb4000140;       (* arm_CBZ X0 (word 40) *)
  0xab1f03e8;       (* arm_ADDS X8 XZR XZR *)
  0xf868782a;       (* arm_LDR X10 X1 (Shiftreg_Offset X8 3) *)
  0xf8687887;       (* arm_LDR X7 X4 (Shiftreg_Offset X8 3) *)
  0x8a0900e7;       (* arm_AND X7 X7 X9 *)
  0xba07014a;       (* arm_ADCS X10 X10 X7 *)
  0xf828782a;       (* arm_STR X10 X1 (Shiftreg_Offset X8 3) *)
  0x91000508;       (* arm_ADD X8 X8 (rvalue (word 1)) *)
  0xcb000107;       (* arm_SUB X7 X8 X0 *)
  0xb5ffff27;       (* arm_CBNZ X7 (word 2097124) *)
  0xa8c163f7;       (* arm_LDP X23 X24 SP (Postimmediate_Offset (iword (&16))) *)
  0xa8c15bf5;       (* arm_LDP X21 X22 SP (Postimmediate_Offset (iword (&16))) *)
  0xa8c153f3;       (* arm_LDP X19 X20 SP (Postimmediate_Offset (iword (&16))) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_MOD_EXEC = ARM_MK_EXEC_RULE bignum_mod_mc;;

(* ------------------------------------------------------------------------- *)
(* Bit-field extraction lemmas, for the various funnel shifts.               *)
(* ------------------------------------------------------------------------- *)

let BIGNUM_MOD_FIELD_NUM = prove
 (`!v c s. s < 64 /\ v < 2 EXP (64 * c + 64)
           ==> (2 EXP 64 * v) DIV 2 EXP (64 * c + s) =
               (if c = 0 then 0 else bigdigit v (c - 1)) DIV 2 EXP s +
               2 EXP (64 - s) * bigdigit v c`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `bigdigit v c = v DIV 2 EXP (64 * c)` SUBST1_TAC THENL
   [REWRITE_TAC[bigdigit] THEN MATCH_MP_TAC MOD_LT THEN
    ASM_SIMP_TAC[RDIV_LT_EQ; EXP_EQ_0; ARITH_EQ; GSYM EXP_ADD];
    ALL_TAC] THEN
  SUBGOAL_THEN `2 EXP 64 = 2 EXP s * 2 EXP (64 - s)` MP_TAC THENL
   [REWRITE_TAC[GSYM EXP_ADD] THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
    REWRITE_TAC[EXP_ADD; GSYM DIV_DIV]] THEN
  ASM_CASES_TAC `c = 0` THEN
  ASM_REWRITE_TAC[MULT_CLAUSES; EXP; DIV_1; DIV_0; ADD_CLAUSES] THEN
  DISCH_THEN SUBST1_TAC THENL
   [REWRITE_TAC[GSYM MULT_ASSOC] THEN SIMP_TAC[DIV_MULT; EXP_EQ_0; ARITH_EQ];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM MULT_ASSOC; GSYM DIV_DIV] THEN
  SUBGOAL_THEN
   `(2 EXP s * 2 EXP (64 - s) * v) DIV 2 EXP (64 * c) =
    2 EXP s * 2 EXP (64 - s) * v DIV 2 EXP (64 * c) + bigdigit v (c - 1)`
  SUBST1_TAC THENL
   [REWRITE_TAC[MULT_ASSOC; GSYM EXP_ADD] THEN
    ASM_SIMP_TAC[ARITH_RULE `s < 64 ==> s + 64 - s = 64`] THEN
    SUBGOAL_THEN `64 * c = 64 + 64 * (c - 1)` SUBST1_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[EXP_ADD; GSYM DIV_DIV] THEN
    SIMP_TAC[DIV_MULT; EXP_EQ_0; ARITH_EQ; bigdigit] THEN
    MP_TAC(SPECL [`v DIV 2 EXP (64 * (c - 1))`; `2 EXP 64`] DIVISION) THEN
    REWRITE_TAC[DIV_DIV; GSYM EXP_ADD; EXP_EQ_0; ARITH_EQ] THEN
    REWRITE_TAC[ARITH_RULE `64 * (c - 1) + 64 = 64 + 64 * (c - 1)`] THEN
    ARITH_TAC;
    SIMP_TAC[DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ] THEN ARITH_TAC]);;

let BIGNUM_MOD_FIELD = prove
 (`!v c r lf hf.
        lf = (if c = 0 then 0 else bigdigit v (c - 1)) /\
        hf = bigdigit v c
        ==> (if val(word_sub (word_and (word r) (word 63)) (word 0):int64) = 0
             then word_jushr (word lf) (word_and (word r) (word 63))
             else word_or
                   (word_jshl (word hf)
                              (word_sub (word 0) (word_and (word r) (word 63))))
                   (word_jushr (word lf) (word_and (word r) (word 63)))):int64 =
            word((2 EXP 64 * v) DIV 2 EXP (64 * c + r MOD 64))`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN
   `word((2 EXP 64 * v) DIV 2 EXP (64 * c + r MOD 64)):int64 =
    word((2 EXP 64 * lowdigits v (c + 1)) DIV 2 EXP (64 * c + r MOD 64))`
  SUBST1_TAC THENL
   [MP_TAC(SPECL [`v:num`; `c + 1`] (CONJUNCT1(CONJUNCT2 HIGH_LOW_DIGITS))) THEN
    DISCH_THEN(fun th -> GEN_REWRITE_TAC
     (LAND_CONV o RAND_CONV o LAND_CONV o RAND_CONV) [SYM th]) THEN
    SUBGOAL_THEN
     `2 EXP 64 *
      (lowdigits v (c + 1) + 2 EXP (64 * (c + 1)) * highdigits v (c + 1)) =
      2 EXP 64 * lowdigits v (c + 1) +
      2 EXP (64 * c + r MOD 64) *
      2 EXP 64 * 2 EXP (64 - r MOD 64) * highdigits v (c + 1)`
    SUBST1_TAC THENL
     [REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_ASSOC; GSYM EXP_ADD;
                  EQ_ADD_LCANCEL] THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
      MP_TAC(SPECL [`r:num`; `64`] MOD_LT_EQ) THEN ARITH_TAC;
      SIMP_TAC[DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ]] THEN
    REWRITE_TAC[GSYM VAL_EQ; VAL_WORD; DIMINDEX_64; GSYM MULT_ASSOC] THEN
    REWRITE_TAC[MOD_MULT_ADD];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(if c = 0 then 0 else bigdigit v (c - 1)) =
    (if c = 0 then 0 else bigdigit (lowdigits v (c + 1)) (c - 1)) /\
    bigdigit v c = bigdigit (lowdigits v (c + 1)) c`
  (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[BIGDIGIT_LOWDIGITS] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    MP_TAC(SPECL [`v:num`; `c + 1`] LOWDIGITS_BOUND) THEN
    REWRITE_TAC[ARITH_RULE `64 * (c + 1) = 64 * c + 64`] THEN
    SPEC_TAC(`lowdigits v (c + 1)`,`v:num`) THEN GEN_TAC THEN DISCH_TAC] THEN
  SUBGOAL_THEN `word_and (word r) (word 63):int64 = word(r MOD 64)`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM VAL_EQ; ARITH_RULE `63 = 2 EXP 6 - 1`;
                VAL_WORD_AND_MASK_WORD] THEN
    REWRITE_TAC[VAL_WORD; DIMINDEX_64; MOD_MOD_EXP_MIN] THEN
    CONV_TAC NUM_REDUCE_CONV THEN MATCH_MP_TAC(GSYM MOD_LT) THEN
    REWRITE_TAC[MOD_LT_EQ] THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`r:num`; `64`] MOD_LT_EQ) THEN REWRITE_TAC[ARITH_EQ] THEN
  SPEC_TAC(`r MOD 64`,`s:num`) THEN GEN_TAC THEN DISCH_TAC THEN STRIP_TAC THEN
  ASM_SIMP_TAC[BIGNUM_MOD_FIELD_NUM] THEN
  REWRITE_TAC[word_jushr; word_jshl; WORD_SUB_0; DIMINDEX_64] THEN
  ASM_SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; ARITH_RULE `s < 64 ==> s < 2 EXP 64`;
               MOD_LT] THEN
  MP_TAC(SPECL [`v:num`; `c:num`] BIGDIGIT_BOUND) THEN
  MP_TAC(SPECL [`v:num`; `c - 1`] BIGDIGIT_BOUND) THEN
  SPEC_TAC(`bigdigit v c`,`h:num`) THEN
  SPEC_TAC(`bigdigit v (c - 1)`,`l:num`) THEN
  REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  ABBREV_TAC `l' = if c = 0 then 0 else l` THEN
  SUBGOAL_THEN `l' < 2 EXP 64` ASSUME_TAC THENL
   [EXPAND_TAC "l'" THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `s = 0` THEN
  ASM_REWRITE_TAC[VAL_WORD_0; MOD_0; WORD_USHR_ZERO; EXP; DIV_1; SUB_0] THENL
   [REWRITE_TAC[GSYM VAL_EQ; VAL_WORD; DIMINDEX_64] THEN
    REWRITE_TAC[MOD_MULT_ADD];
    ALL_TAC] THEN
  SUBGOAL_THEN `val(word_sub (word 0) (word s):int64) MOD 64 = 64 - s`
  SUBST1_TAC THENL
   [REWRITE_TAC[WORD_SUB_LZERO; VAL_WORD_NEG_CASES; DIMINDEX_64] THEN
    ASM_SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; ARITH_RULE `s < 64 ==> s < 2 EXP 64`;
      ARITH_RULE
       `s < 64 ==> 2 EXP 64 - s = (2 EXP 58 - 1) * 64 + (64 - s)`] THEN
    REWRITE_TAC[MOD_MULT_ADD] THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand)
    (INST_TYPE [`:64`,`:N`] WORD_OR_SHL_USHR) o lhand o snd) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD_USHR; VAL_WORD_JOIN;
              VAL_WORD; DIMINDEX_64; DIMINDEX_128] THEN
  ASM_SIMP_TAC[MOD_LT] THEN
  SUBGOAL_THEN `2 EXP 64 * h + l' < 2 EXP 128`
   (fun th -> REWRITE_TAC[MATCH_MP MOD_LT th])
  THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `2 EXP 64 = 2 EXP s * 2 EXP (64 - s)` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM EXP_ADD] THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
    REWRITE_TAC[GSYM MULT_ASSOC] THEN
    SIMP_TAC[DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ] THEN REWRITE_TAC[ADD_SYM]]);;

let BIGNUM_MOD_WINDOW = prove
 (`!h l:int64.
        (val h = 0 ==> val l = 0)
        ==> (if val(word_sub (word_sub (word 0) (word(word_clz h)))
                             (word 0):int64) = 0
             then word_jshl h (word(word_clz h))
             else word_or
                   (word_jshl h (word(word_clz h)))
                   (word_jushr l (word_sub (word 0) (word(word_clz h))))) =
            word((2 EXP 64 * val h + val l) DIV 2 EXP (bitsize(val h)))`,
  REPEAT GEN_TAC THEN MP_TAC(ISPEC `h:int64` WORD_CLZ_BITSIZE) THEN
  REWRITE_TAC[DIMINDEX_64] THEN
  MP_TAC(SPECL [`val(h:int64)`; `64`] BITSIZE_LE) THEN
  MP_TAC(SPEC `val(h:int64)` BITSIZE_EQ_0) THEN REWRITE_TAC[VAL_BOUND_64] THEN
  SPEC_TAC(`bitsize(val(h:int64))`,`s:num`) THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[word_jshl; word_jushr; WORD_SUB_0; WORD_SUB_LZERO;
              DIMINDEX_64] THEN
  ASM_SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; ARITH_RULE `64 - s < 2 EXP 64`] THEN
  ASM_CASES_TAC `s = 0` THENL
   [SUBGOAL_THEN `h:int64 = word 0 /\ l:int64 = word 0`
     (CONJUNCTS_THEN SUBST1_TAC) THENL
     [REWRITE_TAC[GSYM VAL_EQ_0] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[VAL_WORD_0] THEN
    CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN CONV_TAC WORD_REDUCE_CONV THEN
    CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_REDUCE_CONV;
    ALL_TAC] THEN
  ASM_CASES_TAC `s = 64` THENL
   [ASM_REWRITE_TAC[SUB_REFL; WORD_NEG_0; VAL_WORD_0; MOD_0; WORD_SHL_ZERO] THEN
    REWRITE_TAC[GSYM VAL_EQ; VAL_WORD; DIMINDEX_64] THEN
    SIMP_TAC[DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ; DIV_LT; VAL_BOUND_64;
             ADD_CLAUSES] THEN
    SIMP_TAC[MOD_LT; VAL_BOUND_64];
    ALL_TAC] THEN
  SUBGOAL_THEN `val(word_neg(word(64 - s)):int64) = 2 EXP 64 - (64 - s)`
  SUBST1_TAC THENL
   [REWRITE_TAC[VAL_WORD_NEG_CASES; DIMINDEX_64] THEN
    ASM_SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; ARITH_RULE `64 - s < 2 EXP 64`] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `~(2 EXP 64 - (64 - s) = 0) /\ (2 EXP 64 - (64 - s)) MOD 64 = s /\
    (64 - s) MOD 64 = 64 - s`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `s <= 64` THEN ARITH_TAC;
      SUBGOAL_THEN `2 EXP 64 - (64 - s) = (2 EXP 58 - 1) * 64 + s`
      SUBST1_TAC THENL
       [UNDISCH_TAC `s <= 64` THEN ARITH_TAC; REWRITE_TAC[MOD_MULT_ADD]] THEN
      MATCH_MP_TAC MOD_LT THEN
      MAP_EVERY UNDISCH_TAC [`s <= 64`; `~(s = 64)`] THEN ARITH_TAC;
      MATCH_MP_TAC MOD_LT THEN UNDISCH_TAC `~(s = 0)` THEN ARITH_TAC];
    ASM_REWRITE_TAC[]] THEN
  W(MP_TAC o PART_MATCH (lhand o rand)
    (INST_TYPE [`:64`,`:N`] WORD_OR_SHL_USHR) o lhand o snd) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[DIMINDEX_64] THEN UNDISCH_TAC `s <= 64` THEN ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD_USHR; VAL_WORD_JOIN;
              VAL_WORD; DIMINDEX_64; DIMINDEX_128] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC MOD_LT THEN
  MP_TAC(ISPEC `h:int64` VAL_BOUND_64) THEN
  MP_TAC(ISPEC `l:int64` VAL_BOUND_64) THEN
  REWRITE_TAC[DIMINDEX_64] THEN ARITH_TAC);;

let BIGNUM_MOD_TOPDIGITS = prove
 (`!b h l.
        2 EXP 64 * h + l =
        (2 EXP 64 * b) DIV 2 EXP (64 * ((bitsize b - 1) DIV 64)) /\
        l < 2 EXP 64
        ==> 64 * ((bitsize b - 1) DIV 64) + bitsize h = bitsize b /\
            (h = 0 ==> l = 0) /\
            (2 EXP 64 * h + l) DIV 2 EXP (bitsize h) =
            (2 EXP 64 * b) DIV 2 EXP (bitsize b)`,
  REPEAT GEN_TAC THEN ABBREV_TAC `d = (bitsize b - 1) DIV 64` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `64 * d <= bitsize b /\ (bitsize b = 0 \/ 64 * d < bitsize b)`
  (CONJUNCTS_THEN ASSUME_TAC) THENL
   [EXPAND_TAC "d" THEN MP_TAC(SPECL [`bitsize b - 1`; `64`] DIVISION) THEN
    ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `h = b DIV 2 EXP (64 * d)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o AP_TERM `\x. x DIV 2 EXP 64` o
      check (free_in `l:num` o concl) o
      check (is_eq o concl)) THEN
    ASM_SIMP_TAC[DIV_MULT_ADD; DIV_LT; EXP_EQ_0; ARITH_EQ; ADD_CLAUSES] THEN
    DISCH_THEN(K ALL_TAC) THEN REWRITE_TAC[DIV_DIV] THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [MULT_SYM] THEN
    SIMP_TAC[DIV_MULT2; EXP_EQ_0; ARITH_EQ];
    ALL_TAC] THEN
  SUBGOAL_THEN `bitsize h = bitsize b - 64 * d` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[BITSIZE_DIV]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `64 * d <= bitsize b` THEN ARITH_TAC;
    DISCH_TAC THEN SUBGOAL_THEN `bitsize b = 0` ASSUME_TAC THENL
     [MP_TAC(ASSUME `bitsize h = bitsize b - 64 * d`) THEN
      MP_TAC(ASSUME `bitsize b = 0 \/ 64 * d < bitsize b`) THEN
      REWRITE_TAC[ASSUME `h = 0`; BITSIZE_0] THEN ARITH_TAC;
      RULE_ASSUM_TAC(REWRITE_RULE[BITSIZE_EQ_0])] THEN
    UNDISCH_TAC `2 EXP 64 * h + l = (2 EXP 64 * b) DIV 2 EXP (64 * d)` THEN
    ASM_REWRITE_TAC[MULT_CLAUSES; DIV_0; ADD_CLAUSES];
    UNDISCH_THEN
     `2 EXP 64 * h + l = (2 EXP 64 * b) DIV 2 EXP (64 * d)` SUBST1_TAC THEN
    ASM_REWRITE_TAC[DIV_DIV; GSYM EXP_ADD] THEN AP_TERM_TAC THEN
    AP_TERM_TAC THEN
    UNDISCH_TAC `64 * d <= bitsize b` THEN ARITH_TAC]);;

let BIGNUM_MOD_ROUNDUP = prove
 (`!t. t < 2 EXP 64
       ==> (if ~(val(word_add (word t) (word 1):int64) = 0)
            then word_add (word t) (word 1)
            else word_not(word_add (word t) (word 1))) =
           word(MIN (t + 1) (2 EXP 64 - 1)):int64`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM WORD_ADD] THEN
  ASM_CASES_TAC `t + 1 = 2 EXP 64` THEN
  ASM_REWRITE_TAC[VAL_WORD; DIMINDEX_64; MOD_REFL] THENL
   [CONV_TAC(DEPTH_CONV NUM_RED_CONV) THEN CONV_TAC WORD_REDUCE_CONV;
    SUBGOAL_THEN `t + 1 < 2 EXP 64` ASSUME_TAC THENL
     [UNDISCH_TAC `t < 2 EXP 64` THEN UNDISCH_TAC `~(t + 1 = 2 EXP 64)` THEN
      ARITH_TAC;
      ASM_SIMP_TAC[MOD_LT; ADD_EQ_0; ARITH_EQ] THEN AP_TERM_TAC THEN
      UNDISCH_TAC `t + 1 < 2 EXP 64` THEN ARITH_TAC]]);;

let BIGNUM_MOD_BLOCK = prove
 (`!a n i. a < 2 EXP (64 * n) /\ i + 61 <= 64 * n
           ==> word_shl
                (if val(word_sub (word_and (word i) (word 63))
                                 (word 0):int64) = 0
                 then word_jushr (word(bigdigit a (i DIV 64)))
                                 (word_and (word i) (word 63))
                 else word_or
                       (word_jshl
                         (word(bigdigit a (MIN (i DIV 64 + 1) (n - 1))))
                         (word_sub (word 0) (word_and (word i) (word 63))))
                       (word_jushr (word(bigdigit a (i DIV 64)))
                                   (word_and (word i) (word 63))))
                3:int64 =
               word(8 * (a DIV 2 EXP i) MOD 2 EXP 61)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`a + 2 EXP (64 * n) * bigdigit a (n - 1)`; `i DIV 64 + 1`;
                `i:num`; `bigdigit a (i DIV 64)`;
                `bigdigit a (MIN (i DIV 64 + 1) (n - 1))`]
         BIGNUM_MOD_FIELD) THEN
  REWRITE_TAC[ADD_EQ_0; ARITH_EQ; ADD_SUB] THEN ANTS_TAC THENL
   [SUBGOAL_THEN `i DIV 64 < n` ASSUME_TAC THENL
     [UNDISCH_TAC `i + 61 <= 64 * n` THEN ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[BIGDIGIT_ADD_LEFT] THEN
    ASM_CASES_TAC `i DIV 64 + 1 < n` THEN
    ASM_SIMP_TAC[BIGDIGIT_ADD_LEFT;
                 ARITH_RULE `j < n - 1 ==> MIN j (n - 1) = j`;
                 ARITH_RULE `j + 1 < n ==> MIN (j + 1) (n - 1) = j + 1`] THEN
    SUBGOAL_THEN `i DIV 64 + 1 = n` SUBST1_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`i DIV 64 < n`; `~(i DIV 64 + 1 < n)`] THEN
      ARITH_TAC;
      REWRITE_TAC[ARITH_RULE `MIN n (n - 1) = n - 1`]] THEN
    REWRITE_TAC[bigdigit] THEN SIMP_TAC[DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ] THEN
    ASM_SIMP_TAC[DIV_LT; ADD_CLAUSES] THEN
    REWRITE_TAC[GSYM bigdigit; MOD_MOD_REFL];
    DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN `64 * (i DIV 64 + 1) + i MOD 64 = 64 + i` SUBST1_TAC THENL
   [MP_TAC(SPECL [`i:num`; `64`] DIVISION) THEN ARITH_TAC; ALL_TAC] THEN
  SIMP_TAC[EXP_ADD; DIV_MULT2; EXP_EQ_0; ARITH_EQ] THEN
  SUBGOAL_THEN
   `2 EXP (64 * n) * bigdigit a (n - 1) =
    2 EXP i * 2 EXP 61 * 2 EXP (64 * n - i - 61) * bigdigit a (n - 1)`
  SUBST1_TAC THENL
   [REWRITE_TAC[MULT_ASSOC; GSYM EXP_ADD] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
    SIMP_TAC[DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ]] THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_SHL; VAL_WORD; DIMINDEX_64] THEN
  CONV_TAC MOD_DOWN_CONV THEN
  REWRITE_TAC[ARITH_RULE `2 EXP 64 = 2 EXP 3 * 2 EXP 61`; MOD_MULT2] THEN
  REWRITE_TAC[MOD_MULT_ADD] THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_LT THEN
  MP_TAC(SPECL [`a DIV 2 EXP i`; `2 EXP 61`] MOD_LT_EQ) THEN
  CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC);;

let BIGNUM_MOD_LOGSTEP = prove
 (`!v j e (c:int64) (lf:int64) (hf:int64).
        v < 2 EXP (64 * j) /\
        (e <= j ==> lf = word(if e = 0 then 0 else bigdigit v (e - 1))) /\
        hf = word(bigdigit v e)
        ==> (e <= j + 1
             ==> (if j < e then c else lf) =
                 word(if e = 0 then 0
                      else bigdigit (v + 2 EXP (64 * j) * val c) (e - 1))) /\
            (if j = e then c else hf) =
            word(bigdigit (v + 2 EXP (64 * j) * val c) e)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!i. bigdigit (v + 2 EXP (64 * j) * val(c:int64)) i =
        if i < j then bigdigit v i else if i = j then val c else 0`
  (fun th -> REWRITE_TAC[th]) THENL
   [X_GEN_TAC `i:num` THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC[BIGDIGIT_ADD_LEFT] THEN
    REWRITE_TAC[bigdigit] THEN
    SUBGOAL_THEN `64 * i = 64 * j + 64 * (i - j)` SUBST1_TAC THENL
     [UNDISCH_TAC `~(i < j)` THEN ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[EXP_ADD; GSYM DIV_DIV] THEN
    SIMP_TAC[DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ] THEN
    ASM_SIMP_TAC[DIV_LT; ADD_CLAUSES] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[SUB_REFL; MULT_CLAUSES; EXP; DIV_1] THEN
    SIMP_TAC[MOD_LT; VAL_BOUND_64] THEN
    MATCH_MP_TAC(MESON[MOD_0] `!x n. x = 0 ==> x MOD n = 0`) THEN
    MATCH_MP_TAC DIV_LT THEN
    TRANS_TAC LTE_TRANS `2 EXP 64` THEN
    REWRITE_TAC[VAL_BOUND_64; LE_EXP; ARITH_EQ] THEN
    MAP_EVERY UNDISCH_TAC [`~(i < j)`; `~(i:num = j)`] THEN ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [DISCH_TAC THEN ASM_CASES_TAC `e = 0` THENL
     [FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
      ASM_REWRITE_TAC[LT; LE_0];
      ALL_TAC] THEN
    ASM_CASES_TAC `j < e` THEN ASM_REWRITE_TAC[] THENL
     [SUBGOAL_THEN `e - 1 = j` SUBST1_TAC THENL
       [MAP_EVERY UNDISCH_TAC [`j < e`; `e <= j + 1`] THEN ARITH_TAC;
        REWRITE_TAC[LT_REFL; WORD_VAL]];
      SUBGOAL_THEN `e - 1 < j` (fun th -> REWRITE_TAC[th]) THENL
       [MAP_EVERY UNDISCH_TAC [`~(j < e)`; `~(e = 0)`] THEN ARITH_TAC;
        FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
        ASM_REWRITE_TAC[GSYM NOT_LT]]];
    ASM_CASES_TAC `j:num = e` THEN ASM_REWRITE_TAC[LT_REFL; WORD_VAL] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN
    MATCH_MP_TAC BIGDIGIT_ZERO THEN TRANS_TAC LTE_TRANS `2 EXP (64 * j)` THEN
    ASM_REWRITE_TAC[LE_EXP; ARITH_EQ] THEN ASM_ARITH_TAC]);;

let BIGNUM_MOD_EXTR = prove
 (`!(s:int64) (c:int64).
     val(word_subword (word_join s c:int128) (3,64):int64) +
     2 EXP 64 * val s DIV 8 =
     2 EXP 61 * val s + val c DIV 8`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[VAL_WORD_SUBWORD; VAL_WORD_JOIN; DIMINDEX_64; DIMINDEX_128] THEN
  MP_TAC(ISPEC `s:int64` VAL_BOUND_64) THEN
  MP_TAC(ISPEC `c:int64` VAL_BOUND_64) THEN
  SPEC_TAC(`val(s:int64)`,`x:num`) THEN SPEC_TAC(`val(c:int64)`,`y:num`) THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[ARITH_RULE `MIN 64 64 = 64`] THEN
  SUBGOAL_THEN `2 EXP 64 * x + y < 2 EXP 128`
   (fun th -> REWRITE_TAC[MATCH_MP MOD_LT th])
  THENL
   [MAP_EVERY UNDISCH_TAC [`x < 2 EXP 64`; `y < 2 EXP 64`] THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`x:num`; `8`] DIVISION) THEN REWRITE_TAC[ARITH_EQ] THEN
  SPEC_TAC(`x DIV 8`,`q:num`) THEN SPEC_TAC(`x MOD 8`,`r:num`) THEN
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC) THEN
  SUBGOAL_THEN
   `2 EXP 64 * (q * 8 + r) + y = 2 EXP 3 * (q * 2 EXP 64 + 2 EXP 61 * r) + y`
  SUBST1_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  SIMP_TAC[DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ; GSYM ADD_ASSOC; MOD_MULT_ADD] THEN
  SUBGOAL_THEN `2 EXP 61 * r + y DIV 2 EXP 3 < 2 EXP 64`
   (fun th -> REWRITE_TAC[MATCH_MP MOD_LT th])
  THENL
   [MAP_EVERY UNDISCH_TAC [`r < 8`; `y < 2 EXP 64`] THEN ARITH_TAC;
    CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The reciprocal calculation, a copy of the word_recip code.                *)
(* ------------------------------------------------------------------------- *)

let BIGNUM_MOD_RECIP_BLOCK = prove
 (`!a pc.
    ensures arm
      (\s. aligned_bytes_loaded s (word pc) bignum_mod_mc /\
           read PC s = word (pc + 0x98) /\
           read X5 s = a)
      (\s. read PC s = word(pc + 0x13c) /\
           (bit 63 a
            ==> &2 pow 64 + &(val(read X21 s)) < &2 pow 128 / &(val a) /\
                &2 pow 128 / &(val a) <= &2 pow 64 + &(val(read X21 s)) + &1))
      (MAYCHANGE [PC; X6; X9; X11; X21] ,,
       MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  X_GEN_TAC `a:int64` THEN X_GEN_TAC `pc:num` THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN

  (*** Globalize the top-bit-set assumption ***)

  ASM_CASES_TAC `bit 63 (a:int64)` THENL
   [ASM_REWRITE_TAC[] THEN ENSURES_INIT_TAC "s0";
    ARM_ACCSIM_TAC BIGNUM_MOD_EXEC (39--79) (39--79)] THEN

  (*** Handle the special case a = 2^63 explicitly ***)

  ASM_CASES_TAC `a:int64 = word(2 EXP 63)` THENL
   [UNDISCH_THEN `a:int64 = word(2 EXP 63)` SUBST_ALL_TAC THEN
    RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN
    ARM_STEPS_TAC BIGNUM_MOD_EXEC (39--79) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[DIMINDEX_64] THEN
    CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN

  (*** Establish initial range of the input ***)

  SUBGOAL_THEN
   `(&2:real) pow 63 + &1 <= &(val(a:int64)) /\
    &(val(a:int64)):real <= &2 pow 64 - &1`
  STRIP_ASSUME_TAC THENL
   [CONV_TAC REAL_RAT_REDUCE_CONV THEN MP_TAC(ISPEC `a:int64` MSB_VAL) THEN
    MP_TAC(SPEC `a:int64` VAL_BOUND_64) THEN
    REWRITE_TAC[DIMINDEX_64; REAL_OF_NUM_LE] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [GSYM VAL_EQ]) THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC WORD_REDUCE_CONV THEN ARITH_TAC;
    ALL_TAC] THEN

  (*** Initial switch to a shorter b, initial approximation x = z0 ***)

  ARM_STEPS_TAC BIGNUM_MOD_EXEC [39] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP APPROXIMATE_WORD_USHR) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`t1:int64`; `e1:real`] THEN
  STRIP_TAC THEN

  ARM_STEPS_TAC BIGNUM_MOD_EXEC [40] THEN
  MP_TAC(ISPECL [`49`; `t1:int64`] WORD_SUB_MASK_WORD) THEN
  CONV_TAC(LAND_CONV NUM_REDUCE_CONV) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[GSYM REAL_OF_NUM_LT] THEN ASM BOUNDER_TAC[];
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [WORD_XOR_SYM] THEN
    DISCH_THEN(SUBST_ALL_TAC o SYM)] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP APPROXIMATE_WORD_SUB) THEN
  CONV_TAC(LAND_CONV WORD_REDUCE_CONV) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM BOUNDER_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t2:int64` STRIP_ASSUME_TAC) THEN

  ARM_STEPS_TAC BIGNUM_MOD_EXEC [41] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP APPROXIMATE_WORD_ADD) THEN
  ASM_REWRITE_TAC[VAL_WORD_1] THEN
  ANTS_TAC THENL [ASM BOUNDER_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `b:int64`
   (CONJUNCTS_THEN2 STRIP_ASSUME_TAC (STRIP_ASSUME_TAC o GSYM))) THEN
  SUBGOAL_THEN
   `&2 pow 47 + &1 <= &(val(b:int64)) /\ &(val(b:int64)) <= &2 pow 48`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN SHARPEN_INEQ_TAC THEN
    POP_ASSUM(SUBST1_TAC o SYM) THEN ASM BOUNDER_TAC[];
    ALL_TAC] THEN

  ARM_STEPS_TAC BIGNUM_MOD_EXEC [42] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP APPROXIMATE_WORD_USHR) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`z0:int64`; `e4:real`] THEN
  ASM_REWRITE_TAC[REAL_ARITH
   `&562949953421311 - x = &2 pow 49 - (x + &1)`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC (STRIP_ASSUME_TAC o GSYM)) THEN

  SUBGOAL_THEN
   `&2 pow 15 <= &(val(z0:int64)) /\
    &(val(z0:int64)) <= &2 pow 16 + &2 pow 15 - &1`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN SHARPEN_INEQ_TAC THEN
    POP_ASSUM(SUBST1_TAC o SYM) THEN ASM BOUNDER_TAC[];
    ALL_TAC] THEN

  SUBGOAL_THEN
   `&2 pow 64 - &2 pow 62 - &2 pow 48  <= &(val(b:int64)) * &(val(z0:int64)) /\
    &(val(b:int64)) * &(val(z0:int64)) <= &2 pow 64`
  STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC
     (PAT_CONV `\z:real. l <= b * z /\ b * z <= u`) [SYM th]) THEN
    REWRITE_TAC[REAL_ARITH
     `b * ((&2 pow 49 - b) / &2 pow 32 - e) =
      &2 pow 64 - (&2 pow 48 - b) pow 2 / &2 pow 32 - b * e`] THEN
    ASM PURE_BOUNDER_TAC[];
    ALL_TAC] THEN

  (*** Computation of initial error d0 ***)

  ARM_STEPS_TAC BIGNUM_MOD_EXEC [43] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP APPROXIMATE_WORD_MNEG) THEN
  ANTS_TAC THENL [ASM BOUNDER_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d0:int64`
   (CONJUNCTS_THEN2 STRIP_ASSUME_TAC (STRIP_ASSUME_TAC o GSYM))) THEN
  W(fun (asl,w) ->
      FIRST_ASSUM (MP_TAC o BOUNDER_RULE (map snd asl) o lhand o concl)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN

  (*** Accumulation of the polynomial giving z1 ***)

  ARM_STEPS_TAC BIGNUM_MOD_EXEC [44] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP APPROXIMATE_WORD_USHR) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`t6:int64`; `e6:real`] THEN STRIP_TAC THEN

  ARM_STEPS_TAC BIGNUM_MOD_EXEC [45] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP APPROXIMATE_WORD_MUL) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM BOUNDER_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t7:int64` STRIP_ASSUME_TAC) THEN

  ARM_STEPS_TAC BIGNUM_MOD_EXEC [46] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP APPROXIMATE_WORD_USHR) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`t8:int64`; `e8:real`] THEN STRIP_TAC THEN

  ARM_STEPS_TAC BIGNUM_MOD_EXEC [47] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP APPROXIMATE_WORD_ADD) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM BOUNDER_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t9:int64` STRIP_ASSUME_TAC) THEN

  ARM_STEPS_TAC BIGNUM_MOD_EXEC [48] THEN
  MP_TAC(ISPECL [`t7:int64`; `word 1073741824:int64`] WORD_ADD_OR) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[WORD_AND_EQ_0] THEN CONV_TAC WORD_REDUCE_CONV THEN
    REWRITE_TAC[SET_RULE `DISJOINT s {a} <=> ~(a IN s)`] THEN
    REWRITE_TAC[IN_BITS_OF_WORD; BIT_VAL] THEN
    MATCH_MP_TAC(MESON[ODD; DIV_LT] `a < n ==> ~ODD(a DIV n)`) THEN
    ASM_REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN ASM BOUNDER_TAC[];
    DISCH_THEN(SUBST_ALL_TAC o SYM)] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP APPROXIMATE_WORD_ADD) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM BOUNDER_TAC[]; ALL_TAC] THEN
  CONV_TAC(LAND_CONV WORD_REDUCE_CONV) THEN
  DISCH_THEN(X_CHOOSE_THEN `t10:int64` STRIP_ASSUME_TAC) THEN

  ARM_STEPS_TAC BIGNUM_MOD_EXEC [49] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP APPROXIMATE_WORD_MUL) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM BOUNDER_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t11:int64` STRIP_ASSUME_TAC) THEN

  ARM_STEPS_TAC BIGNUM_MOD_EXEC [50] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP APPROXIMATE_WORD_USHR) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`t12:int64`; `e12:real`] THEN STRIP_TAC THEN

  ARM_STEPS_TAC BIGNUM_MOD_EXEC [51] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP APPROXIMATE_WORD_SHL) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM BOUNDER_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t13:int64` STRIP_ASSUME_TAC) THEN

  ARM_STEPS_TAC BIGNUM_MOD_EXEC [52] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP APPROXIMATE_WORD_MADD) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM BOUNDER_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t14:int64` STRIP_ASSUME_TAC) THEN

  ARM_STEPS_TAC BIGNUM_MOD_EXEC [53] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP APPROXIMATE_WORD_USHR) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`z1:int64`; `e15:real`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (STRIP_ASSUME_TAC o GSYM)) THEN

  (*** Accuracy of z1 then bounds on z1 and tidying up ***)

  SUBGOAL_THEN
   `&2 pow 64 - (&2 pow 54 + &2 pow 50) <= &(val(b:int64)) * &(val(z1:int64)) /\
    &(val(b:int64)) * &(val(z1:int64)) <= &2 pow 64`
  STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[REAL_ARITH
     `b * ((a * z + z * c) / &2 pow 30 - e:real) =
      (b * z) * (a + c) / &2 pow 30 - b * e`] THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP (REAL_ARITH
       `&2 pow 64 - b * z = d ==> b * z:real = &2 pow 64 - d`)) THEN
      ASM BOUNDER_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[REAL_ARITH `(x * x + x') * (x * x + a):real =
        a * x' + a * x * x + x' * x * x + x * x * x * x`] THEN
    REWRITE_TAC[REAL_ARITH
     `bz * (&2 pow 30 + x / &2 pow 30 - e) / &2 pow 30 - be <= u <=>
      bz * (&2 pow 60 + x) <= &2 pow 60 * (u + be + bz * e / &2 pow 30)`] THEN
    REWRITE_TAC[REAL_ARITH
     `(x - d) * (y - e):real = x * y - (d * y + e * (x - d)) /\
      (x - d) + (y - e):real = (x + y) - (d + e) /\
      &c * (x - y) = (&c * x - &c * y)`] THEN
    MATCH_MP_TAC(REAL_ARITH
     `bz * (&2 pow 60 + x) <= &2 pow 124 /\ &0 <= u /\ &0 <= bz * y
      ==> bz * (&2 pow 60 + x - y) <= &2 pow 60 * (&2 pow 64 + u)`) THEN
    REPEAT CONJ_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP (REAL_ARITH
       `&2 pow 64 - b * z = d ==> b * z:real = &2 pow 64 - d`)) THEN
      ASM BOUNDER_TAC[];
      ASM BOUNDER_TAC[];
      SUBGOAL_THEN
       `&(val(t6:int64)) <= &2 pow 15 /\ &(val(t8:int64)) <= &2 pow 30`
      STRIP_ASSUME_TAC THENL
       [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN ASM BOUNDER_TAC[]; ALL_TAC] THEN
      MAP_EVERY (C UNDISCH_THEN (SUBST_ALL_TAC o SYM))
       [`&(val(t6:int64)) = &(val(d0:int64)) / &2 pow 49 - e6`;
        `&(val(t8:int64)) = &(val(d0:int64)) / &2 pow 34 - e8`] THEN
      ASM BOUNDER_TAC[]];
    ALL_TAC] THEN

  SUBGOAL_THEN
   `&2 pow 15 <= &(val(z1:int64)) /\ &(val(z1:int64)) <= &130945`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN SHARPEN_INEQ_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THENL
     [ALL_TAC; ASM BOUNDER_TAC[]] THEN
    REWRITE_TAC[REAL_ARITH `(e * z + z * d):real = z * (e + d)`] THEN
    REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o MATCH_MP (REAL_ARITH
     `&(val x) = a ==> a = &(val x)`))) THEN
    ASM BOUNDER_TAC[];
    DISCARD_MATCHING_ASSUMPTIONS [`&(val x):real = a`]] THEN

  (*** First Newton step ***)

  ARM_STEPS_TAC BIGNUM_MOD_EXEC [54] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP APPROXIMATE_WORD_MNEG) THEN
  ANTS_TAC THENL [ASM BOUNDER_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:int64`
   (CONJUNCTS_THEN2 STRIP_ASSUME_TAC (STRIP_ASSUME_TAC o GSYM))) THEN
  W(fun (asl,w) ->
      FIRST_ASSUM (MP_TAC o BOUNDER_RULE (map snd asl) o lhand o concl)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN

  ARM_STEPS_TAC BIGNUM_MOD_EXEC [55] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP APPROXIMATE_WORD_USHR) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`t17:int64`; `e17:real`] THEN STRIP_TAC THEN

  ARM_STEPS_TAC BIGNUM_MOD_EXEC [56] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP APPROXIMATE_WORD_MUL) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM BOUNDER_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t18:int64` STRIP_ASSUME_TAC) THEN

  ARM_STEPS_TAC BIGNUM_MOD_EXEC [57] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP APPROXIMATE_WORD_SHL) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM BOUNDER_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t19:int64` STRIP_ASSUME_TAC) THEN

  ARM_STEPS_TAC BIGNUM_MOD_EXEC [58] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP APPROXIMATE_WORD_USHR) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`t20:int64`; `e20:real`] THEN STRIP_TAC THEN

  ARM_STEPS_TAC BIGNUM_MOD_EXEC [59] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP APPROXIMATE_WORD_ADD) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM BOUNDER_TAC[]; ALL_TAC] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
   [REAL_ARITH `e * z + (d * z) / f - g:real = z * (e + d / f) - g`] THEN
  DISCH_THEN(X_CHOOSE_THEN `z2:int64`
   (CONJUNCTS_THEN2 STRIP_ASSUME_TAC (STRIP_ASSUME_TAC o GSYM))) THEN

  SUBGOAL_THEN
   `&2 pow 80 - &5 / &4 * &2 pow 60 <= &(val(b:int64)) * &(val(z2:int64)) /\
    &(val(b:int64)) * &(val(z2:int64)) <= &2 pow 80`
  STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[REAL_ARITH `b * (z * d - e):real = (b * z) * d - b * e`] THEN
    FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP (REAL_ARITH
       `&2 pow 64 - b * z = d ==> b * z:real = &2 pow 64 - d`)) THEN
    CONJ_TAC THENL [ASM BOUNDER_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[REAL_ARITH
     `(&2 pow 64 - d) * (&2 pow 16 + (d / &2 pow 24 - e) / &2 pow 24) =
      (&2 pow 128 - d pow 2) / &2 pow 48 -
      (&2 pow 64 - d) * e / &2 pow 24`] THEN
    CONV_TAC(funpow 3 LAND_CONV REAL_POLY_CONV) THEN
    ASM PURE_BOUNDER_TAC[];
    ALL_TAC] THEN

  SUBGOAL_THEN
   `&2 pow 31 <= &(val(z2:int64)) /\ &(val(z2:int64)) <= &2 pow 33 - &1`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN SHARPEN_INEQ_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
      REWRITE_TAC[REAL_ARITH `(e * z + z * d):real = z * (e + d)`] THEN
      REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o MATCH_MP (REAL_ARITH
       `&(val x) = a ==> a = &(val x)`))) THEN
      ASM BOUNDER_TAC[];
      MATCH_MP_TAC REAL_LT_LCANCEL_IMP THEN EXISTS_TAC `&(val(b:int64))` THEN
      CONJ_TAC THENL [ASM BOUNDER_TAC[]; ALL_TAC] THEN
      GEN_REWRITE_TAC I [GSYM REAL_SUB_LT] THEN ASM PURE_BOUNDER_TAC[]];
    DISCARD_MATCHING_ASSUMPTIONS [`&(val x):real = a`]] THEN

  (*** Second Newton step ***)

  ARM_STEPS_TAC BIGNUM_MOD_EXEC [60] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP APPROXIMATE_WORD_IWORD) THEN
  DISCH_THEN(MP_TAC o SPEC
   `&2 pow 80 - &(val(b:int64)) * &(val(z2:int64)):int`) THEN
  REWRITE_TAC[int_le; int_lt; int_sub_th; int_mul_th;
                int_pow_th; int_of_num_th] THEN
  ANTS_TAC THENL
   [REPEAT(CONJ_TAC THENL [ASM PURE_BOUNDER_TAC[]; ALL_TAC]) THEN
    MATCH_MP_TAC(INTEGER_RULE
     `e divides n /\ (b == b') (mod e) /\ (z == z') (mod e)
      ==> (&0 - b * z:int == n - b' * z') (mod e)`) THEN
    REWRITE_TAC[REWRITE_RULE[DIMINDEX_64]
     (INST_TYPE [`:64`,`:N`]IVAL_VAL_CONG)] THEN
    MATCH_MP_TAC INT_DIVIDES_POW_LE_IMP THEN ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d2:int64`
   (CONJUNCTS_THEN2 STRIP_ASSUME_TAC (STRIP_ASSUME_TAC o GSYM))) THEN
  W(fun (asl,w) ->
      FIRST_ASSUM (MP_TAC o BOUNDER_RULE (map snd asl) o lhand o concl)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN

  ARM_STEPS_TAC BIGNUM_MOD_EXEC [61] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP APPROXIMATE_WORD_USHR) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`t23:int64`; `e23:real`] THEN STRIP_TAC THEN

  ARM_STEPS_TAC BIGNUM_MOD_EXEC [62] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP APPROXIMATE_WORD_MUL) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM BOUNDER_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t24:int64` STRIP_ASSUME_TAC) THEN

  ARM_STEPS_TAC BIGNUM_MOD_EXEC [63] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP APPROXIMATE_WORD_SHL) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM BOUNDER_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t25:int64` STRIP_ASSUME_TAC) THEN

  ARM_STEPS_TAC BIGNUM_MOD_EXEC [64] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP APPROXIMATE_WORD_USHR) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`t26:int64`; `e26:real`] THEN STRIP_TAC THEN

  ARM_STEPS_TAC BIGNUM_MOD_EXEC [65] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP APPROXIMATE_WORD_ADD) THEN
  ASM_REWRITE_TAC[REAL_ARITH
   `e * z + (d * z) / f - g:real = z * (e + d / f) - g`] THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC REAL_LT_LCANCEL_IMP THEN EXISTS_TAC `&(val(b:int64))` THEN
    CONJ_TAC THENL [ASM BOUNDER_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[REAL_ARITH `b * (z * d - e):real = (b * z) * d - b * e`] THEN
    FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP (REAL_ARITH
       `&2 pow 80 - b * z = d ==> b * z:real = &2 pow 80 - d`)) THEN
    GEN_REWRITE_TAC I [GSYM REAL_SUB_LT] THEN
    ASM BOUNDER_TAC[];
    ALL_TAC] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
   [REAL_ARITH `e * z + (d * z) / f - g:real = z * (e + d / f) - g`] THEN
  DISCH_THEN(X_CHOOSE_THEN `z3:int64`
   (CONJUNCTS_THEN2 STRIP_ASSUME_TAC (STRIP_ASSUME_TAC o GSYM))) THEN

  SUBGOAL_THEN
   `&2 pow 111 - &201 / &128 * &2 pow 71
    <= &(val(b:int64)) * &(val(z3:int64)) /\
    &(val(b:int64)) * &(val(z3:int64)) <= &2 pow 111`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN SHARPEN_INEQ_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[REAL_ARITH `b * (z * d - e):real = (b * z) * d - b * e`] THEN
    FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP (REAL_ARITH
       `&2 pow 80 - b * z = d ==> b * z:real = &2 pow 80 - d`))
    THENL [ASM BOUNDER_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[REAL_ARITH
     `(&2 pow 80 - d) * (&2 pow 31 + (d / &2 pow 32 - e) / &2 pow 17) =
      (&2 pow 160 - d pow 2) / &2 pow 49 -
      (&2 pow 80 - d) * e / &2 pow 17`] THEN
    CONV_TAC(funpow 3 LAND_CONV REAL_POLY_CONV) THEN
    ASM PURE_BOUNDER_TAC[];
    ALL_TAC] THEN

  SUBGOAL_THEN
   `&2 pow 62 <= &(val(z3:int64)) /\ &(val(z3:int64)) <= &2 pow 64 - &1`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ALL_TAC; BOUNDER_TAC[]] THEN
    SHARPEN_INEQ_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[REAL_ARITH `(e * z + z * d):real = z * (e + d)`] THEN
    REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o MATCH_MP (REAL_ARITH
     `&(val x) = a ==> a = &(val x)`))) THEN
    ASM BOUNDER_TAC[];
    DISCARD_MATCHING_ASSUMPTIONS [`&(val x):real = a`]] THEN

  (*** Transfer accuracy to original input a, throw away facts about b ***)

  SUBGOAL_THEN
   `&2 pow 127 - &2 pow 88 + &1 <= &(val(a:int64)) * &(val(z3:int64)) /\
    &(val(a:int64)) * &(val(z3:int64)) <= &2 pow 127`
  STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP (REAL_ARITH
     `a / &2 pow 16 - e + &1 = b ==> a = &2 pow 16 * (b + e - &1)`)) THEN
   REWRITE_TAC[REAL_ARITH `(c * (b + x)) * z:real = c * (b * z + x * z)`] THEN
   CONJ_TAC THEN ASM PURE_BOUNDER_TAC[];
   REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (vfree_in `b:int64` o concl)))] THEN

  (*** Observe this, which implies in particular the result is not exact ***)

  SUBGOAL_THEN `!w p. ~(val(a:int64) * w = 2 EXP p)` ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP
     (REWRITE_RULE[IMP_CONJ_ALT] PRIME_POWER_MULT)) THEN
    REWRITE_TAC[PRIME_2] THEN STRIP_TAC THEN
    SUBGOAL_THEN `2 EXP 63 < val(a:int64) /\ val a < 2 EXP 64` MP_TAC THENL
     [REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN ASM BOUNDER_TAC[];
      ASM_REWRITE_TAC[LT_EXP] THEN ARITH_TAC];
    ALL_TAC] THEN

  (*** The full-sized Newton step ***)

  ARM_ACCSTEPS_TAC BIGNUM_MOD_EXEC [66] (66--68) THEN

  ARM_STEPS_TAC BIGNUM_MOD_EXEC [69] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP APPROXIMATE_WORD_USHR) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`t31:int64`; `e31:real`] THEN STRIP_TAC THEN

  ARM_STEPS_TAC BIGNUM_MOD_EXEC [70] THEN
  REABBREV_TAC `bf = read X11 s70` THEN

  SUBGOAL_THEN
   `?e. &0 <= e /\ e <= &1 /\
        &(val(bf:int64)):real =
        (&2 pow 127 - &(val(a:int64)) * &(val(z3:int64))) / &2 pow 60 - e`
  (X_CHOOSE_THEN `e32:real` STRIP_ASSUME_TAC) THENL
   [MP_TAC(SPEC `&2 pow 127 - &(val(a:int64)) * &(val(z3:int64)):real`
          INTEGER_POS) THEN
    ANTS_TAC THENL [ASM BOUNDER_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o fst o EQ_IMP_RULE) THEN
    ANTS_TAC THENL [REAL_INTEGER_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_TAC `d3:num`) THEN
    SUBGOAL_THEN `&d3:real <= &2 pow 88 - &1` ASSUME_TAC THENL
     [FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV [SYM th]) THEN
      ASM BOUNDER_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `d3 < 2 EXP 88` ASSUME_TAC THENL
     [ASM BOUNDER_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `1 <= d3` ASSUME_TAC THENL
     [REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_EQ] THEN
      FIRST_X_ASSUM(fun th ->
        GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [SYM th]) THEN
      REWRITE_TAC[REAL_OF_NUM_CLAUSES; REAL_SUB_0] THEN
      DISCH_THEN(MP_TAC o SYM) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[GSYM int_of_num_th] THEN
    SUBGOAL_THEN `&(val(bf:int64)):int = &((d3 - 1) DIV 2 EXP 60)`
    SUBST1_TAC THENL
     [EXPAND_TAC "bf" THEN
      SIMP_TAC[GSYM WORD_SUBWORD_NOT; GSYM WORD_JOIN_NOT;
               DIMINDEX_64; DIMINDEX_128; ARITH] THEN
      SIMP_TAC[VAL_WORD_SUBWORD_JOIN; DIMINDEX_64; DIMINDEX_128;
               ARITH_LE; ARITH_LT] THEN
      REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES; GSYM INT_OF_NUM_REM;
                  GSYM INT_OF_NUM_DIV; INT_VAL_WORD_NOT; DIMINDEX_64] THEN
      REWRITE_TAC[INT_ARITH
        `e * (e - &1 - h) + e - &1 - l:int = e * e - &1 - (e * h + l)`] THEN
      SIMP_TAC[INT_DIV_REM; INT_POS; INT_POW_LE; GSYM INT_POW_ADD] THEN
      CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
      FIRST_ASSUM(MP_TAC o check (is_eq o concl)) THEN
      REWRITE_TAC[IMP_IMP; REAL_EQ_SUB_RADD] THEN
      GEN_REWRITE_TAC (LAND_CONV o DEPTH_CONV) [REAL_OF_NUM_CLAUSES] THEN
      GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
       [GSYM INT_OF_NUM_CLAUSES] THEN
      REWRITE_TAC[GSYM INT_EQ_SUB_RADD] THEN DISCH_THEN(fun th ->
        REWRITE_TAC[th; INT_ARITH
        `&2 pow 128 - &1 - x:int = (&2 pow 127 - &1) + &2 pow 127 - x`]) THEN
      SUBGOAL_THEN `(&2 pow 127 - &1 + &d3) rem &2 pow 124 = &(d3 - 1)`
      SUBST1_TAC THENL
       [ASM_SIMP_TAC[GSYM INT_OF_NUM_SUB] THEN MATCH_MP_TAC INT_REM_UNIQ THEN
        EXISTS_TAC `&8:int` THEN CONJ_TAC THENL [INT_ARITH_TAC; ALL_TAC] THEN
        REWRITE_TAC[INT_SUB_LE; INT_LT_SUB_RADD] THEN
        REWRITE_TAC[INT_OF_NUM_CLAUSES; INT_ABS_NUM] THEN
        REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN ASM BOUNDER_TAC[];
        REWRITE_TAC[INT_OF_NUM_DIV; INT_OF_NUM_CLAUSES] THEN ARITH_TAC];
      ASM_REWRITE_TAC[int_of_num_th]] THEN
    EXISTS_TAC `&((d3 - 1) MOD 2 EXP 60 + 1):real / &2 pow 60` THEN
    SIMP_TAC[REAL_LE_DIV; REAL_POW_LE; REAL_POS] THEN CONJ_TAC THENL
     [SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LT_POW2] THEN
      REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN ARITH_TAC;
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; REAL_OF_NUM_MOD] THEN
      ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB; LE_1] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN

  ARM_STEPS_TAC BIGNUM_MOD_EXEC [71] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP APPROXIMATE_WORD_MUL) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM PURE_BOUNDER_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t33:int64` STRIP_ASSUME_TAC) THEN

  ARM_STEPS_TAC BIGNUM_MOD_EXEC (72--73) THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP APPROXIMATE_WORD_USHR) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`t35:int64`; `e35:real`] THEN STRIP_TAC THEN

  ARM_STEPS_TAC BIGNUM_MOD_EXEC [74] THEN

  (*** Analysis of provisional result w before the final truncation ***)

  ABBREV_TAC `w = 2 * val(z3:int64) + val(t35:int64)` THEN
  SUBGOAL_THEN
   `&2 pow 128 - &2 pow 62 <= &(val(a:int64)) * &w + &(val a) /\
    &(val(a:int64)) * &w <= &2 pow 128`
  STRIP_ASSUME_TAC THENL
   [ABBREV_TAC `d3 = &2 pow 127 - &(val(a:int64)) * &(val(z3:int64))` THEN
    SUBGOAL_THEN `&0 <= d3 /\ d3:real <= &2 pow 88 - &1` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "d3" THEN ASM PURE_BOUNDER_TAC[]; ALL_TAC] THEN
    EXPAND_TAC "w" THEN REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
    ASM_REWRITE_TAC[REAL_ARITH
     `a * (&2 * z + ((z / &2 pow 33 - d) * c) / &2 pow 33 - f):real =
      (a * z) * (&2 + c / &2 pow 66) - d * c * a / &2 pow 33 - a * f`] THEN
    FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP (REAL_ARITH
       `&2 pow 127 - a * z = d ==> a * z:real = &2 pow 127 - d`)) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH
       `&0 <= a * (&1 - e) /\ l <= b - c
        ==> l:real <= b - c - a * e + a`) THEN
      CONJ_TAC THENL [ASM PURE_BOUNDER_TAC[]; ASM BOUNDER_TAC[]];
      REWRITE_TAC[REAL_ARITH
       `(&2 pow 127 - d) * (&2 + (d / &2 pow 60 - e) / &2 pow 66) =
        (&2 pow 254 - d pow 2) / &2 pow 126 -
        (&2 pow 127 - d) * e / &2 pow 66`] THEN
      SUBST1_TAC(SYM(ASSUME `&(val(bf:int64)) = d3 / &2 pow 60 - e32`)) THEN
      ASM PURE_BOUNDER_TAC[]];
    ALL_TAC] THEN

  (*** Now the computed result with implicit 1 bit ***)

  ABBREV_TAC `z:int64 = word_add (word_shl z3 1) t35` THEN
  SUBGOAL_THEN `&w:real = (&2 pow 64) + &(val(z:int64))` SUBST_ALL_TAC THENL
   [EXPAND_TAC "z" THEN REWRITE_TAC[VAL_WORD_ADD; VAL_WORD_SHL] THEN
    REWRITE_TAC[DIMINDEX_64; EXP_1] THEN CONV_TAC MOD_DOWN_CONV THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `2 EXP 64 <= w /\ w < 2 * 2 EXP 64` MP_TAC THENL
     [REWRITE_TAC[GSYM REAL_OF_NUM_LT; ARITH_RULE `a <= b <=> a < b + 1`];
      SIMP_TAC[GSYM NOT_LE; MOD_CASES; GSYM REAL_OF_NUM_SUB] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN REAL_ARITH_TAC] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN CONJ_TAC THEN
    (MATCH_MP_TAC REAL_LT_LCANCEL_IMP THEN EXISTS_TAC `&(val(a:int64))` THEN
     CONJ_TAC THENL [ASM BOUNDER_TAC[]; ALL_TAC])
    THENL
     [REWRITE_TAC[REAL_ARITH `a * (w + &1):real = a * w + a`] THEN
      TRANS_TAC REAL_LTE_TRANS `&2 pow 128 - &2 pow 62`;
      TRANS_TAC REAL_LET_TRANS `&2 pow 128`] THEN
    ASM_REWRITE_TAC[] THEN ASM BOUNDER_TAC[];
    ALL_TAC] THEN

  (*** In this non-trivial case the increment does not wrap ***)

  ARM_STEPS_TAC BIGNUM_MOD_EXEC (75--76) THEN
  REABBREV_TAC `z' = read X11 s76` THEN
  SUBGOAL_THEN `&(val(z':int64)):real = &(val(z:int64)) + &1` ASSUME_TAC THENL
   [EXPAND_TAC "z'" THEN
    SUBGOAL_THEN `val(z:int64) + 1 < 2 EXP 64` MP_TAC THENL
     [REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES];
      SIMP_TAC[VAL_WORD_ADD_CASES; DIMINDEX_64; VAL_WORD_1;
               ADD_EQ_0; ARITH_EQ] THEN
      REWRITE_TAC[REAL_OF_NUM_CLAUSES]] THEN
    MATCH_MP_TAC(REAL_ARITH
     `(&2 pow 63 + &1) * (&2 pow 64 + z) <= &2 pow 128
      ==> z + &1 < &2 pow 64`) THEN
    TRANS_TAC REAL_LE_TRANS
     `&(val(a:int64)) * (&2 pow 64 + &(val(z:int64)))` THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THEN ASM BOUNDER_TAC[];
    ALL_TAC] THEN

  (*** The final bounds check and selection ***)

  ARM_STEPS_TAC BIGNUM_MOD_EXEC (77--79) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[REAL_LT_RDIV_EQ; REAL_LE_LDIV_EQ;
               REAL_ARITH `&2 pow 63 + &1 <= a ==> &0 < a`] THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [REAL_MUL_SYM] THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [REAL_MUL_SYM] THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN
  SIMP_TAC[MOD_LT; VAL_BOUND_64; LT_MULT2;
           ARITH_RULE `a < 2 EXP 64 * 2 EXP 64 ==> a DIV 2 EXP 64 < 2 EXP 64`;
           ARITH_RULE `2 EXP 64 <= h DIV 2 EXP 64 + a <=>
                       2 EXP 128 <= 2 EXP 64 * a + h`] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
  REWRITE_TAC[REAL_OF_NUM_CLAUSES; LT_LE] THEN ASM_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Arithmetic of the quotient estimates and the accumulator updates.         *)
(* ------------------------------------------------------------------------- *)

let BIGNUM_MOD_QUOTIENT = prove
 (`!b e t d w h q.
        ~(b = 0) /\ b < e /\ e <= 2 * b /\
        t * e <= 2 EXP 64 * b /\ 2 EXP 64 * b < (t + 1) * e /\
        (d = t + 1 \/ d = t /\ t = 2 EXP 64 - 1) /\
        (2 EXP 64 + w) * d < 2 EXP 128 /\ 2 EXP 128 <= (2 EXP 64 + w + 1) * d /\
        h <= t /\ (w * h) DIV 2 EXP 64 + h = q
        ==> q < 2 EXP 64 /\ q * b <= h * e /\ h * e < (q + 2) * b + e`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN
   `q * 2 EXP 64 <= (2 EXP 64 + w) * h /\
    (2 EXP 64 + w) * h < (q + 1) * 2 EXP 64`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `q = ((2 EXP 64 + w) * h) DIV 2 EXP 64` SUBST1_TAC THENL
     [EXPAND_TAC "q" THEN
      REWRITE_TAC[ARITH_RULE `(e + w) * h = w * h + e * h`] THEN
      SIMP_TAC[DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ];
      MP_TAC(SPECL [`(2 EXP 64 + w) * h`; `2 EXP 64`] DIVISION) THEN
      ARITH_TAC];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [(*** No overflow in q ***)
    SUBGOAL_THEN `(2 EXP 64 + w) * h <= (2 EXP 64 + w) * t` MP_TAC THENL
     [ASM_REWRITE_TAC[LE_MULT_LCANCEL];
      FIRST_X_ASSUM(DISJ_CASES_THEN (REPEAT_TCL CONJUNCTS_THEN SUBST_ALL_TAC))
      THEN ASM_ARITH_TAC];

    (*** The upper bound q * b <= h * e, in the two cases for d ***)
    FIRST_X_ASSUM(DISJ_CASES_THEN (REPEAT_TCL CONJUNCTS_THEN SUBST_ALL_TAC))
    THENL
     [SUBGOAL_THEN
       `(q * 2 EXP 64) * (t + 1) <= ((2 EXP 64 + w) * h) * (t + 1) /\
        ((2 EXP 64 + w) * (t + 1)) * h <= 2 EXP 128 * h`
      STRIP_ASSUME_TAC THENL
       [CONJ_TAC THEN MATCH_MP_TAC LE_MULT2 THEN
        ASM_SIMP_TAC[LE_REFL; LT_IMP_LE];
        ALL_TAC] THEN
      SUBGOAL_THEN `q * (t + 1) <= 2 EXP 64 * h` ASSUME_TAC THENL
       [ASM_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `q * 2 EXP 64 * b <= q * (t + 1) * e /\
                    (q * (t + 1)) * e <= (2 EXP 64 * h) * e`
      STRIP_ASSUME_TAC THENL
       [CONJ_TAC THEN MATCH_MP_TAC LE_MULT2 THEN
        ASM_SIMP_TAC[LE_REFL; LT_IMP_LE];
        ASM_ARITH_TAC];
      SUBGOAL_THEN `w = 1` SUBST_ALL_TAC THENL
       [RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN ASM_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `q:num = h` SUBST1_TAC THENL
       [EXPAND_TAC "q" THEN REWRITE_TAC[MULT_CLAUSES] THEN
        MATCH_MP_TAC(ARITH_RULE `x = 0 ==> x + h = h`) THEN
        REWRITE_TAC[DIV_EQ_0] THEN ASM_ARITH_TAC;
        REWRITE_TAC[LE_MULT_LCANCEL] THEN ASM_ARITH_TAC]];

    (*** The lower bound h * e < (q + 2) * b + e ***)
    SUBGOAL_THEN `2 EXP 128 * h <= (t + 1) * ((q + 1) * 2 EXP 64 + h)`
    ASSUME_TAC THENL
     [SUBGOAL_THEN `2 EXP 128 * h <= ((2 EXP 64 + w + 1) * (t + 1)) * h /\
                    (t + 1) * (2 EXP 64 + w) * h <=
                    (t + 1) * (q + 1) * 2 EXP 64`
      MP_TAC THENL [ALL_TAC; ARITH_TAC] THEN
      CONJ_TAC THEN MATCH_MP_TAC LE_MULT2 THEN
      ASM_SIMP_TAC[LE_REFL; LT_IMP_LE] THEN
      TRANS_TAC LE_TRANS `(2 EXP 64 + w + 1) * d` THEN
      ASM_REWRITE_TAC[LE_MULT_LCANCEL] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `2 EXP 64 * h < (t + 1) * (q + 2)` ASSUME_TAC THENL
     [SUBGOAL_THEN `(t + 1) * h < (t + 1) * 2 EXP 64` MP_TAC THENL
       [REWRITE_TAC[LT_MULT_LCANCEL] THEN ASM_ARITH_TAC;
        UNDISCH_TAC `2 EXP 128 * h <= (t + 1) * ((q + 1) * 2 EXP 64 + h)` THEN
        ARITH_TAC];
      ALL_TAC] THEN
    MATCH_MP_TAC(MESON[LT_MULT_LCANCEL] `!m n e. e * m < e * n ==> m < n`) THEN
    EXISTS_TAC `t + 1` THEN
    SUBGOAL_THEN `h * t * e <= h * 2 EXP 64 * b /\
                  (2 EXP 64 * h) * b < ((t + 1) * (q + 2)) * b /\
                  h * e <= (t + 1) * e`
    MP_TAC THENL [ALL_TAC; ARITH_TAC] THEN
    ASM_REWRITE_TAC[LT_MULT_RCANCEL; LE_MULT_RCANCEL; LE_MULT_LCANCEL] THEN
    ASM_ARITH_TAC]);;

let BIGNUM_MOD_ESTIMATE = prove
 (`!b p u d w x h q.
     ~(b = 0) /\ b < 2 EXP p /\ 2 EXP p <= 2 * b /\
     u * 2 EXP p <= 2 EXP 64 * b /\ 2 EXP 64 * b < (u + 1) * 2 EXP p /\
     (d = u + 1 \/ d = u /\ u = 2 EXP 64 - 1) /\
     (2 EXP 64 + val(w:int64)) * d < 2 EXP 128 /\
     2 EXP 128 <= (2 EXP 64 + val w + 1) * d /\
     x < 2 EXP 64 * b /\ h = word(x DIV 2 EXP p) /\
     word_add (word((val w * val h) DIV 2 EXP 64)) h = q
     ==> val(q:int64) * b <= x /\ x < val q * b + 6 * b`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN FIRST_X_ASSUM SUBST1_TAC THEN
  ABBREV_TAC
   `r = (val(w:int64) * x DIV 2 EXP p) DIV 2 EXP 64 + x DIV 2 EXP p` THEN
  MP_TAC(SPECL [`b:num`; `2 EXP p`; `u:num`; `d:num`; `val(w:int64)`;
                `x DIV 2 EXP p`; `r:num`] BIGNUM_MOD_QUOTIENT) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [REWRITE_TAC[GSYM LT_SUC_LE; ADD1] THEN
    SUBGOAL_THEN `x DIV 2 EXP p * 2 EXP p < (u + 1) * 2 EXP p` MP_TAC THENL
     [MP_TAC(SPECL [`x:num`; `2 EXP p`] DIVISION) THEN
      REWRITE_TAC[EXP_EQ_0; ARITH_EQ] THEN
      MAP_EVERY UNDISCH_TAC
       [`x < 2 EXP 64 * b`; `2 EXP 64 * b < (u + 1) * 2 EXP p`] THEN
      ARITH_TAC;
      REWRITE_TAC[LT_MULT_RCANCEL; EXP_EQ_0; ARITH_EQ]];
    STRIP_TAC] THEN
  SUBGOAL_THEN
   `val(word_add
         (word((val(w:int64) * val(word(x DIV 2 EXP p):int64)) DIV 2 EXP 64))
         (word(x DIV 2 EXP p)):int64) = r`
  SUBST1_TAC THENL
   [SUBGOAL_THEN `x DIV 2 EXP p < 2 EXP 64` ASSUME_TAC THENL
     [UNDISCH_TAC `r < 2 EXP 64` THEN EXPAND_TAC "r" THEN ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[VAL_WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
    ASM_SIMP_TAC[MOD_LT] THEN CONV_TAC MOD_DOWN_CONV THEN ASM_SIMP_TAC[MOD_LT];
    ALL_TAC] THEN
  MP_TAC(SPECL [`x:num`; `2 EXP p`] DIVISION) THEN
  REWRITE_TAC[EXP_EQ_0; ARITH_EQ] THEN
  MAP_EVERY UNDISCH_TAC
   [`2 EXP p <= 2 * b`; `r * b <= x DIV 2 EXP p * 2 EXP p`;
    `x DIV 2 EXP p * 2 EXP p < (r + 2) * b + 2 EXP p`] THEN
  ARITH_TAC);;

let BIGNUM_MOD_START = prove
 (`!n. ~(n = 0) /\ n < 2 EXP 58
       ==> (if ~(val(word_and
                     (word(0 +
                           val(word_add
                                (word((0xc9714fbcda3ac11 * n) DIV 2 EXP 64))
                                (word n):int64) * 61))
                     (word 63):int64) = 0)
            then word(0 +
                      val(word_add (word((0xc9714fbcda3ac11 * n) DIV 2 EXP 64))
                                   (word n):int64) * 61)
            else word_sub
                  (word(0 +
                        val(word_add
                             (word((0xc9714fbcda3ac11 * n) DIV 2 EXP 64))
                             (word n):int64) * 61))
                  (word 61)):int64 =
           word(61 * ((64 * n + 60) DIV 61 - 1)) /\
           ~((64 * n + 60) DIV 61 - 1 = 0) /\
           61 * ((64 * n + 60) DIV 61 - 1) < 64 * n /\
           64 * n <= 61 * ((64 * n + 60) DIV 61 - 1) + 61`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `word_add (word((0xc9714fbcda3ac11 * n) DIV 2 EXP 64)) (word n):int64 =
    word((64 * n) DIV 61)`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM WORD_ADD] THEN AP_TERM_TAC THEN
    UNDISCH_TAC `n < 2 EXP 58` THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `val(word((64 * n) DIV 61):int64) = (64 * n) DIV 61`
  SUBST1_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    UNDISCH_TAC `n < 2 EXP 58` THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `63 = 2 EXP 6 - 1`; VAL_WORD_AND_MASK_WORD] THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_64; MOD_MOD_EXP_MIN; ADD_CLAUSES] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  MP_TAC(SPECL [`64 * n`; `61`] DIVISION) THEN REWRITE_TAC[ARITH_EQ] THEN
  ABBREV_TAC `q = (64 * n) DIV 61` THEN ABBREV_TAC `r = (64 * n) MOD 61` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `(64 * n + 60) DIV 61 = if r = 0 then q else q + 1`
  SUBST1_TAC THENL
   [COND_CASES_TAC THEN MATCH_MP_TAC DIV_UNIQ THENL
     [EXISTS_TAC `60` THEN ASM_ARITH_TAC;
      EXISTS_TAC `r - 1` THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(q * 61) MOD 64 = 0 <=> r = 0` SUBST1_TAC THENL
   [MATCH_MP_TAC(TAUT `(q ==> p) /\ (p ==> q) ==> (p <=> q)`) THEN
    CONJ_TAC THENL
     [DISCH_TAC THEN
      SUBGOAL_THEN `q * 61 = 64 * n` (fun th -> REWRITE_TAC[th]) THENL
       [ASM_ARITH_TAC; REWRITE_TAC[MOD_MULT]];
      DISCH_TAC THEN
      MP_TAC(SPECL [`q * 61`; `r:num`; `64`] MOD_ADD_MOD) THEN
      ASM_REWRITE_TAC[ADD_CLAUSES; MOD_MOD_REFL] THEN
      SUBGOAL_THEN `q * 61 + r = 64 * n` SUBST1_TAC THENL
       [ASM_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[MOD_MULT; ARITH_EQ; MOD_LT; ARITH_RULE `r < 61 ==> r < 64`]];
    ALL_TAC] THEN
  ASM_CASES_TAC `r = 0` THEN ASM_REWRITE_TAC[ADD_SUB] THENL
   [SUBGOAL_THEN `61 <= q * 61` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[ARITH_RULE `61 <= q * 61 ==> 61 * (q - 1) = q * 61 - 61`;
                 WORD_SUB] THEN
    ASM_ARITH_TAC;
    REWRITE_TAC[ARITH_RULE `61 * q = q * 61`] THEN ASM_ARITH_TAC]);;

let BIGNUM_MOD_QZERO = prove
 (`!q b z. q * b <= z /\ z < b ==> q = 0`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `q = 0` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(ARITH_RULE `b <= x ==> ~(x <= z /\ z < b)`) THEN
  GEN_REWRITE_TAC LAND_CONV [ARITH_RULE `b = 1 * b`] THEN
  REWRITE_TAC[LE_MULT_RCANCEL] THEN ASM_ARITH_TAC);;

let BIGNUM_MOD_TAIL = prove
 (`!W L x hh ss zw bw q cc lz lb r c.
     W < 2 EXP (64 * L) /\ ss < 2 EXP 64 /\ c < 2 EXP 64 /\ cc < 2 EXP 61 /\
     c + 2 EXP 64 * ss DIV 8 = 2 EXP 61 * ss + x DIV 8 /\
     &W + &2 pow (64 * L) * (&(x DIV 8) + &2 pow 61 * &hh) =
     &2 pow 61 * (&lz + &q * (&2 pow (64 * L) - &lb)) + &cc /\
     (ss == zw + hh + q * (2 EXP 64 - 1 - bw)) (mod (2 EXP 64)) /\
     bw < 2 EXP 64 /\
     lz + 2 EXP (64 * L) * zw = q * (lb + 2 EXP (64 * L) * bw) + r /\
     r < 2 EXP (64 * (L + 1))
     ==> W + 2 EXP (64 * L) * c + 2 EXP (64 * (L + 1)) * ss DIV 8 =
         2 EXP 61 * r + cc`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `t = (zw + hh + q * (2 EXP 64 - 1 - bw)) DIV 2 EXP 64` THEN
  SUBGOAL_THEN `zw + hh + q * (2 EXP 64 - 1 - bw) = 2 EXP 64 * t + ss`
  ASSUME_TAC THENL
   [UNDISCH_TAC
     `(ss == zw + hh + q * (2 EXP 64 - 1 - bw)) (mod (2 EXP 64))` THEN
    ASM_SIMP_TAC[CONG; MOD_LT] THEN DISCH_THEN SUBST1_TAC THEN
    EXPAND_TAC "t" THEN
    MP_TAC(SPECL [`zw + hh + q * (2 EXP 64 - 1 - bw)`;
                  `2 EXP 64`] DIVISION) THEN
    REWRITE_TAC[EXP_EQ_0; ARITH_EQ] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(W + 2 EXP (64 * L) * c + 2 EXP (64 * (L + 1)) * ss DIV 8) +
    2 EXP (64 * (L + 1) + 61) * t =
    (2 EXP 61 * r + cc) + 2 EXP (64 * (L + 1) + 61) * q`
  MP_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`c + 2 EXP 64 * ss DIV 8 = 2 EXP 61 * ss + x DIV 8`;
      `zw + hh + q * (2 EXP 64 - 1 - bw) = 2 EXP 64 * t + ss`;
      `lz + 2 EXP (64 * L) * zw = q * (lb + 2 EXP (64 * L) * bw) + r`;
      `&W + &2 pow (64 * L) * (&(x DIV 8) + &2 pow 61 * &hh) =
       &2 pow 61 * (&lz + &q * (&2 pow (64 * L) - &lb)) + &cc`] THEN
    ASM_SIMP_TAC[GSYM REAL_OF_NUM_EQ; GSYM REAL_OF_NUM_CLAUSES;
                 GSYM REAL_OF_NUM_SUB;
                 ARITH_RULE `b < 2 EXP 64 ==> b <= 2 EXP 64 - 1`;
                 ARITH_RULE `1 <= 2 EXP 64`] THEN
    REWRITE_TAC[ARITH_RULE `64 * (L + 1) + 61 = 64 * L + 125`;
                ARITH_RULE `64 * (L + 1) = 64 * L + 64`; REAL_POW_ADD] THEN
    CONV_TAC REAL_RING;
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (NUMBER_RULE
   `!a c m t q:num. a + m * t = c + m * q ==> (a == c) (mod m)`)) THEN
  DISCH_THEN(fun th -> MATCH_MP_TAC CONG_IMP_EQ THEN
    EXISTS_TAC `2 EXP (64 * (L + 1) + 61)` THEN REWRITE_TAC[th]) THEN
  REWRITE_TAC[ARITH_RULE `64 * (L + 1) + 61 = 64 * L + 125`;
              ARITH_RULE `64 * (L + 1) = 64 * L + 64`; EXP_ADD] THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN
     `2 EXP (64 * L) * c <= 2 EXP (64 * L) * (2 EXP 64 - 1) /\
      2 EXP (64 * L) * ss DIV 8 <= 2 EXP (64 * L) * (2 EXP 61 - 1)`
    MP_TAC THENL
     [REWRITE_TAC[LE_MULT_LCANCEL] THEN CONJ_TAC THEN DISJ2_TAC THEN
      MAP_EVERY UNDISCH_TAC [`c < 2 EXP 64`; `ss < 2 EXP 64`] THEN ARITH_TAC;
      UNDISCH_TAC `W < 2 EXP (64 * L)` THEN
      SPEC_TAC(`2 EXP (64 * L)`,`e:num`) THEN ARITH_TAC];
    UNDISCH_TAC `r < 2 EXP (64 * (L + 1))` THEN UNDISCH_TAC `cc < 2 EXP 61` THEN
    REWRITE_TAC[ARITH_RULE `64 * (L + 1) = 64 * L + 64`; EXP_ADD] THEN
    SPEC_TAC(`2 EXP (64 * L)`,`e:num`) THEN ARITH_TAC]);;

let BIGNUM_MOD_TOP = prove
 (`!W e zt hh q zm b r.
     W < e /\ q < 2 EXP 64 /\
     &W + &e * &hh = &zm + &q * (&e - &b) /\
     r + q * b = e * zt + zm /\ r < e * 2 EXP 64
     ==> W + e * (zt + hh + 2 EXP 64 - q) MOD 2 EXP 64 = r`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CONG_IMP_EQ THEN
  EXISTS_TAC `e * 2 EXP 64` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [SUBGOAL_THEN
     `e * (zt + hh + 2 EXP 64 - q) MOD 2 EXP 64 <= e * (2 EXP 64 - 1)`
    MP_TAC THENL
     [REWRITE_TAC[LE_MULT_LCANCEL] THEN DISJ2_TAC THEN
      REWRITE_TAC[ARITH_RULE `x <= 2 EXP 64 - 1 <=> x < 2 EXP 64`;
                  MOD_LT_EQ] THEN
      REWRITE_TAC[EXP_EQ_0; ARITH_EQ];
      UNDISCH_TAC `W < e` THEN ARITH_TAC];
    MATCH_MP_TAC CONG_TRANS THEN
    EXISTS_TAC `W + e * (zt + hh + 2 EXP 64 - q)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CONG_ADD THEN REWRITE_TAC[CONG_REFL] THEN
      REWRITE_TAC[CONG; MOD_MULT2; MOD_MOD_REFL];
      ALL_TAC] THEN
    SUBGOAL_THEN `W + e * (zt + hh + 2 EXP 64 - q) = r + e * 2 EXP 64`
    SUBST1_TAC THENL
     [UNDISCH_TAC `&W + &e * &hh = &zm + &q * (&e - &b):real` THEN
      UNDISCH_TAC `r + q * b = e * zt + zm` THEN
      UNDISCH_TAC `q < 2 EXP 64` THEN
      SIMP_TAC[GSYM REAL_OF_NUM_EQ; GSYM REAL_OF_NUM_CLAUSES;
               GSYM REAL_OF_NUM_SUB;
               ARITH_RULE `q < 2 EXP 64 ==> q <= 2 EXP 64`] THEN
      DISCH_THEN(K ALL_TAC) THEN CONV_TAC REAL_RING;
      CONV_TAC NUMBER_RULE]]);;

let BIGNUM_MOD_FINAL = prove
 (`!a b e r t q z.
     ~(b = 0) /\ b < e /\ r < e /\ q < 2 EXP 64 /\
     r + e * t + q * b = z + q * e /\
     q * b <= z + b /\ z < (q + 1) * b /\ (z == a) (mod b)
     ==> (t MOD 2 EXP 64 < q <=> z < q * b) /\
         r + bitval(z < q * b) * b = a MOD b + e * bitval(z < q * b)`,
  let LE_MULT_LMONO = MESON[LE_MULT_LCANCEL]
    `!x y. x <= y ==> !e:num. e * x <= e * y` in
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `z < q * b` THEN
  ASM_REWRITE_TAC[BITVAL_CLAUSES; MULT_CLAUSES; ADD_CLAUSES] THENL
   [SUBGOAL_THEN `t + 1 = q` ASSUME_TAC THENL
     [MATCH_MP_TAC(ARITH_RULE `~(q <= t) /\ ~(t + 2 <= q) ==> t + 1 = q`) THEN
      CONJ_TAC THEN
      DISCH_THEN(MP_TAC o SPEC `e:num` o MATCH_MP LE_MULT_LMONO) THEN
      MAP_EVERY UNDISCH_TAC
       [`r + e * t + q * b = z + q * e`; `z < q * b`; `q * b <= z + b`;
        `r < e`; `b < e`] THEN
      ARITH_TAC;
      ALL_TAC] THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN CONJ_TAC THENL
     [MATCH_MP_TAC(ARITH_RULE `x = t ==> x < t + 1`) THEN
      MATCH_MP_TAC MOD_LT THEN
      UNDISCH_TAC `t + 1 < 2 EXP 64` THEN ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `a MOD b = (z + b) - (t + 1) * b` SUBST1_TAC THENL
     [UNDISCH_TAC `(z == a) (mod b)` THEN REWRITE_TAC[CONG] THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC MOD_UNIQ THEN
      EXISTS_TAC `t:num` THEN
      MAP_EVERY UNDISCH_TAC [`z < (t + 1) * b`; `(t + 1) * b <= z + b`] THEN
      ARITH_TAC;
      MAP_EVERY UNDISCH_TAC
       [`r + e * t + (t + 1) * b = z + (t + 1) * e`; `z < (t + 1) * b`;
        `(t + 1) * b <= z + b`] THEN
      ARITH_TAC];
    SUBGOAL_THEN `t:num = q` ASSUME_TAC THENL
     [MATCH_MP_TAC(ARITH_RULE `~(q + 1 <= t) /\ ~(t + 1 <= q) ==> t = q`) THEN
      CONJ_TAC THEN
      DISCH_THEN(MP_TAC o SPEC `e:num` o MATCH_MP LE_MULT_LMONO) THEN
      MAP_EVERY UNDISCH_TAC
       [`r + e * t + q * b = z + q * e`; `~(z < q * b)`; `z < (q + 1) * b`;
        `r < e`; `b < e`] THEN
      ARITH_TAC;
      ALL_TAC] THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[MOD_LT; LT_REFL]; ALL_TAC] THEN
    UNDISCH_TAC `(z == a) (mod b)` THEN REWRITE_TAC[CONG] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC `q:num` THEN
    MAP_EVERY UNDISCH_TAC
     [`r + e * q + q * b = z + q * e`; `~(z < q * b)`; `z < (q + 1) * b`] THEN
    ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

(* Many facts only hold for a nonzero modulus b, and are kept in the form  *)
(* ~(b = 0) ==> P. Once ~(b = 0) is assumed, this turns them all into P.   *)

let BIGNUM_MOD_UNGUARD_TAC =
  REPEAT(FIRST_X_ASSUM(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC o
                       C MP (ASSUME `~(b = 0)`)));;

let BIGNUM_MOD_CORRECT = prove
 (`!k z n x m a b pc.
        ALLPAIRS nonoverlapping
          [(z,8 * val k)] [(word pc,0x440); (x,8 * val n); (m,8 * val k)] /\
        ~(val k = 0) /\ val k < 2 EXP 58 /\ val n < 2 EXP 58 - 1
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_mod_mc /\
                  read PC s = word (pc + 0xc) /\
                  C_ARGUMENTS [k;z;n;x;m] s /\
                  bignum_from_memory (x,val n) s = a /\
                  bignum_from_memory (m,val k) s = b)
             (\s. read PC s = word(pc + 0x430) /\
                  (~(b = 0) ==> bignum_from_memory (z,val k) s = a MOD b))
             (MAYCHANGE [PC; X5; X6; X7; X8; X9; X10; X11; X12;
                         X13; X14; X15; X16; X17; X19; X20; X21; X22; X23] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
              MAYCHANGE [memory :> bignum(z,val k)])`,
  W64_GEN_TAC `k:num` THEN X_GEN_TAC `z:int64` THEN W64_GEN_TAC `n:num` THEN
  MAP_EVERY X_GEN_TAC [`x:int64`; `m:int64`; `a:num`; `b:num`; `pc:num`] THEN
  REWRITE_TAC[ALLPAIRS; ALL; NONOVERLAPPING_CLAUSES; C_ARGUMENTS;
              SOME_FLAGS] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  BIGNUM_TERMRANGE_TAC `n:num` `a:num` THEN
  BIGNUM_TERMRANGE_TAC `k:num` `b:num` THEN

  (*** The initial zeroing of the output and the top word zt ***)

  ENSURES_SEQUENCE_TAC `pc + 0x24`
   `\s. read X0 s = word k /\ read X1 s = z /\ read X2 s = word n /\
        read X3 s = x /\ read X4 s = m /\ read X23 s = word 0 /\
        bignum_from_memory (x,n) s = a /\ bignum_from_memory (m,k) s = b /\
        bignum_from_memory (z,k) s = 0` THEN
  CONJ_TAC THENL
   [ENSURES_WHILE_UP_TAC `k:num` `pc + 0x14` `pc + 0x1c`
     `\i s. read X0 s = word k /\ read X1 s = z /\ read X2 s = word n /\
            read X3 s = x /\ read X4 s = m /\ read X23 s = word 0 /\
            read X8 s = word i /\
            bignum_from_memory (x,n) s = a /\ bignum_from_memory (m,k) s = b /\
            bignum_from_memory (z,i) s = 0` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ARM_SIM_TAC BIGNUM_MOD_EXEC (1--2) THEN
      REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES; BIGNUM_FROM_MEMORY_TRIVIAL];
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
      ARM_SIM_TAC BIGNUM_MOD_EXEC (1--2) THEN
      REWRITE_TAC[GSYM WORD_ADD; GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
      ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; VAL_WORD_0; MULT_CLAUSES;
                      ADD_CLAUSES];
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
      ARM_SIM_TAC BIGNUM_MOD_EXEC (1--2) THEN ASM_SIMP_TAC[LT_IMP_LE];
      ARM_SIM_TAC BIGNUM_MOD_EXEC (1--2)];
    ALL_TAC] THEN

  (*** The trivial case n = 0 ***)

  ASM_CASES_TAC `n = 0` THENL
   [UNDISCH_THEN `n = 0` SUBST_ALL_TAC THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o MATCH_MP (ARITH_RULE
     `a < 2 EXP (64 * 0) ==> a = 0`)) THEN
    ARM_SIM_TAC BIGNUM_MOD_EXEC (1--2) THEN REWRITE_TAC[MOD_0];
    ALL_TAC] THEN

  (*** Finding the top nonzero digit of m and the digit below it ***)

  ENSURES_SEQUENCE_TAC `pc + 0x68`
   `\s. read X0 s = word k /\ read X1 s = z /\ read X2 s = word n /\
        read X3 s = x /\ read X4 s = m /\ read X23 s = word 0 /\
        bignum_from_memory (x,n) s = a /\ bignum_from_memory (m,k) s = b /\
        bignum_from_memory (z,k) s = 0 /\
        read X11 s = word((bitsize b - 1) DIV 64) /\
        2 EXP 64 * val(read X5 s) + val(read X6 s) =
        (2 EXP 64 * b) DIV 2 EXP (64 * ((bitsize b - 1) DIV 64))` THEN
  CONJ_TAC THENL
   [ENSURES_WHILE_UP_TAC `k:num` `pc + 0x44` `pc + 0x60`
     `\i s. read X0 s = word k /\ read X1 s = z /\ read X2 s = word n /\
            read X3 s = x /\ read X4 s = m /\ read X23 s = word 0 /\
            read X8 s = word i /\
            bignum_from_memory (x,n) s = a /\ bignum_from_memory (m,k) s = b /\
            bignum_from_memory (z,k) s = 0 /\
            read X10 s = word(if i = 0 then 0 else bigdigit b (i - 1)) /\
            read X11 s = word((bitsize(lowdigits b i) - 1) DIV 64) /\
            2 EXP 64 * val(read X5 s) + val(read X6 s) =
            (2 EXP 64 * lowdigits b i) DIV
            2 EXP (64 * ((bitsize(lowdigits b i) - 1) DIV 64))` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [SUBGOAL_THEN `val(word_sub (word n) (word 0):int64) = n` ASSUME_TAC THENL
       [ASM_REWRITE_TAC[WORD_SUB_0]; ALL_TAC] THEN
      ARM_SIM_TAC BIGNUM_MOD_EXEC (1--8) THEN
      REWRITE_TAC[LOWDIGITS_0; BITSIZE_0; MULT_CLAUSES; DIV_0; VAL_WORD_0] THEN
      CONV_TAC NUM_REDUCE_CONV;
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
      GHOST_INTRO_TAC `hh:int64` `read X5` THEN
      GHOST_INTRO_TAC `ll:int64` `read X6` THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
      SUBGOAL_THEN
       `read(memory :> bytes64(word_add m (word(8 * i)))) s0 =
        word(bigdigit b i)`
      ASSUME_TAC THENL
       [EXPAND_TAC "b" THEN
        REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES;
                    BIGDIGIT_BIGNUM_FROM_MEMORY] THEN
        ASM_REWRITE_TAC[WORD_VAL];
        ALL_TAC] THEN
      ARM_STEPS_TAC BIGNUM_MOD_EXEC (1--7) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[GSYM WORD_ADD; ADD_EQ_0; ARITH_EQ; ADD_SUB; WORD_SUB_0] THEN
      SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] THEN
      REWRITE_TAC[LOWDIGITS_CLAUSES] THEN
      ASM_CASES_TAC `bigdigit b i = 0` THEN
      ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES] THEN
      MP_TAC(SPECL [`64 * i`; `bigdigit b i`; `lowdigits b i`]
        (CONJUNCT1 BITSIZE_MULT_ADD)) THEN
      ASM_REWRITE_TAC[LOWDIGITS_BOUND] THEN DISCH_THEN SUBST1_TAC THEN
      SUBGOAL_THEN `((64 * i + bitsize (bigdigit b i)) - 1) DIV 64 = i`
      SUBST1_TAC THENL
       [MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `bitsize(bigdigit b i) - 1` THEN
        MP_TAC(SPECL [`bigdigit b i`; `64`] BITSIZE_LE) THEN
        MP_TAC(SPEC `bigdigit b i` BITSIZE_EQ_0) THEN
        ASM_REWRITE_TAC[BIGDIGIT_BOUND] THEN ARITH_TAC;
        REWRITE_TAC[]] THEN
      ASM_CASES_TAC `i = 0` THEN
      ASM_REWRITE_TAC[MULT_CLAUSES; EXP; DIV_1; LOWDIGITS_0; ADD_CLAUSES;
                      VAL_WORD_0] THEN
      SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND] THEN
      REWRITE_TAC[ARITH_RULE
       `2 EXP 64 * (2 EXP (64 * i) * d + l) =
        2 EXP (64 * i) * 2 EXP 64 * d + 2 EXP 64 * l`] THEN
      SIMP_TAC[DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ; EQ_ADD_LCANCEL] THEN
      MP_TAC(SPECL [`lowdigits b i`; `i:num`; `0`] BIGNUM_MOD_FIELD_NUM) THEN
      ANTS_TAC THENL
       [REWRITE_TAC[ARITH_RULE `0 < 64`] THEN
        TRANS_TAC LTE_TRANS `2 EXP (64 * i)` THEN
        REWRITE_TAC[LOWDIGITS_BOUND; LE_EXP] THEN ARITH_TAC;
        REWRITE_TAC[ADD_CLAUSES; EXP; DIV_1; SUB_0] THEN
        DISCH_THEN SUBST1_TAC] THEN
      ASM_REWRITE_TAC[BIGDIGIT_LOWDIGITS; LT_REFL; MULT_CLAUSES;
                      ADD_CLAUSES] THEN
      ASM_SIMP_TAC[ARITH_RULE `~(i = 0) ==> i - 1 < i`];
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
      ARM_SIM_TAC BIGNUM_MOD_EXEC (1--2);
      ARM_SIM_TAC BIGNUM_MOD_EXEC (1--2) THEN
      ASM_SIMP_TAC[LOWDIGITS_SELF]];
    ALL_TAC] THEN

  (*** The bitsize p of m and the normalized top word of m, rounded up ***)

  ENSURES_SEQUENCE_TAC `pc + 0x98`
   `\s. read X0 s = word k /\ read X1 s = z /\ read X2 s = word n /\
        read X3 s = x /\ read X4 s = m /\ read X23 s = word 0 /\
        bignum_from_memory (x,n) s = a /\ bignum_from_memory (m,k) s = b /\
        bignum_from_memory (z,k) s = 0 /\
        read X20 s = word(bitsize b) /\
        read X5 s = word(MIN ((2 EXP 64 * b) DIV 2 EXP (bitsize b) + 1)
                             (2 EXP 64 - 1))` THEN
  CONJ_TAC THENL
   [GHOST_INTRO_TAC `hh:int64` `read X5` THEN
    GHOST_INTRO_TAC `ll:int64` `read X6` THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC BIGNUM_MOD_EXEC (1--12) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`b:num`; `val(hh:int64)`; `val(ll:int64)`]
      BIGNUM_MOD_TOPDIGITS) THEN
    ASM_REWRITE_TAC[VAL_BOUND_64; GSYM DIMINDEX_64] THEN
    REWRITE_TAC[DIMINDEX_64] THEN STRIP_TAC THEN CONJ_TAC THENL
     [REWRITE_TAC[WORD_CLZ_BITSIZE; DIMINDEX_64; WORD_SHL_WORD] THEN
      MP_TAC(SPECL [`val(hh:int64)`; `64`] BITSIZE_LE) THEN
      REWRITE_TAC[VAL_BOUND_64; GSYM DIMINDEX_64] THEN
      REWRITE_TAC[DIMINDEX_64] THEN DISCH_TAC THEN
      SUBGOAL_THEN
       `bitsize b =
        (2 EXP 6 * (bitsize b - 1) DIV 64 + 64) - (64 - bitsize(val(hh:int64)))`
       (fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [th])
      THENL
       [MAP_EVERY UNDISCH_TAC
         [`64 * (bitsize b - 1) DIV 64 + bitsize (val(hh:int64)) = bitsize b`;
          `bitsize(val(hh:int64)) <= 64`] THEN
        ARITH_TAC;
        REWRITE_TAC[WORD_SUB; GSYM WORD_ADD] THEN
        REWRITE_TAC[ARITH_RULE `64 - s <= x + 64`]];
      MP_TAC(SPECL [`hh:int64`; `ll:int64`] BIGNUM_MOD_WINDOW) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC BIGNUM_MOD_ROUNDUP THEN
      SIMP_TAC[RDIV_LT_EQ; EXP_EQ_0; ARITH_EQ] THEN
      GEN_REWRITE_TAC RAND_CONV [MULT_SYM] THEN
      REWRITE_TAC[LT_MULT_LCANCEL; EXP_EQ_0; ARITH_EQ; BITSIZE]];
    ALL_TAC] THEN
  ABBREV_TAC `p = bitsize b` THEN
  ABBREV_TAC `u = (2 EXP 64 * b) DIV 2 EXP p` THEN
  ABBREV_TAC `d = MIN (u + 1) (2 EXP 64 - 1)` THEN

  (*** The reciprocal w of d, as in the word_recip function ***)

  ENSURES_SEQUENCE_TAC `pc + 0x13c`
   `\s. read X0 s = word k /\ read X1 s = z /\ read X2 s = word n /\
        read X3 s = x /\ read X4 s = m /\ read X23 s = word 0 /\
        bignum_from_memory (x,n) s = a /\ bignum_from_memory (m,k) s = b /\
        bignum_from_memory (z,k) s = 0 /\ read X20 s = word p /\
        (~(b = 0)
         ==> &2 pow 64 + &(val(read X21 s)) < &2 pow 128 / &d /\
             &2 pow 128 / &d <= &2 pow 64 + &(val(read X21 s)) + &1)` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
    MP_TAC(REWRITE_RULE[SOME_FLAGS]
     (SPECL [`word d:int64`; `pc:num`] BIGNUM_MOD_RECIP_BLOCK)) THEN
    ARM_BIGSTEP_TAC BIGNUM_MOD_EXEC "s1" THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
    SUBGOAL_THEN `2 EXP 63 <= u /\ u < 2 EXP 64` STRIP_ASSUME_TAC THENL
     [MAP_EVERY EXPAND_TAC ["u"; "p"] THEN
      SIMP_TAC[LE_RDIV_EQ; RDIV_LT_EQ; EXP_EQ_0; ARITH_EQ] THEN
      MP_TAC(SPEC `b:num` BITSIZE_REV_ALT) THEN
      MP_TAC(SPEC `b:num` BITSIZE) THEN
      ASM_REWRITE_TAC[] THEN ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `bit 63 (word d:int64)` (fun th -> REWRITE_TAC[th]) THENL
     [MP_TAC(ISPEC `word d:int64` MSB_VAL) THEN REWRITE_TAC[DIMINDEX_64] THEN
      CONV_TAC NUM_REDUCE_CONV THEN DISCH_THEN SUBST1_TAC THEN
      SUBGOAL_THEN `val(word d:int64) = d` SUBST1_TAC THENL
       [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
        EXPAND_TAC "d" THEN ARITH_TAC;
        EXPAND_TAC "d" THEN UNDISCH_TAC `2 EXP 63 <= u` THEN ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `val(word d:int64) = d` SUBST1_TAC THENL
     [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
      EXPAND_TAC "d" THEN ARITH_TAC;
      REWRITE_TAC[]];
    ALL_TAC] THEN

  (*** Introduce w and the number N of 61-bit blocks below the top one ***)

  GHOST_INTRO_TAC `w:int64` `read X21` THEN GLOBALIZE_PRECONDITION_TAC THEN
  MP_TAC(SPEC `n:num` BIGNUM_MOD_START) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `n < 2 EXP 58 - 1` THEN ARITH_TAC;
    SPEC_TAC(`(64 * n + 60) DIV 61 - 1`,`N:num`) THEN GEN_TAC THEN
    STRIP_TAC] THEN

  (*** Collect the facts about b, p, u, d and w needed for the estimates ***)

  SUBGOAL_THEN `u < 2 EXP 64 /\ d < 2 EXP 64` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["d"; "u"; "p"] THEN
    SIMP_TAC[RDIV_LT_EQ; EXP_EQ_0; ARITH_EQ] THEN
    REWRITE_TAC[ARITH_RULE `MIN (u + 1) (2 EXP 64 - 1) < 2 EXP 64`] THEN
    MP_TAC(SPEC `b:num` BITSIZE) THEN
    GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [MULT_SYM] THEN
    REWRITE_TAC[LT_MULT_LCANCEL; EXP_EQ_0; ARITH_EQ];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `~(b = 0)
    ==> b < 2 EXP p /\ 2 EXP p <= 2 * b /\
        u * 2 EXP p <= 2 EXP 64 * b /\ 2 EXP 64 * b < (u + 1) * 2 EXP p /\
        (d = u + 1 \/ d = u /\ u = 2 EXP 64 - 1) /\
        (2 EXP 64 + val(w:int64)) * d < 2 EXP 128 /\
        2 EXP 128 <= (2 EXP 64 + val w + 1) * d`
  ASSUME_TAC THENL
   [DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0 < &d:real` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LT] THEN EXPAND_TAC "d" THEN ARITH_TAC;
      ASM_SIMP_TAC[REAL_LT_RDIV_EQ; REAL_LE_LDIV_EQ]] THEN
    REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "p" THEN
    ASM_SIMP_TAC[BITSIZE; BITSIZE_REV_ALT] THEN
    MP_TAC(SPECL [`2 EXP 64 * b`; `2 EXP p`] DIVISION) THEN
    ASM_REWRITE_TAC[EXP_EQ_0; ARITH_EQ] THEN
    UNDISCH_TAC `u < 2 EXP 64` THEN EXPAND_TAC "d" THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `p <= 64 * k` ASSUME_TAC THENL
   [EXPAND_TAC "p" THEN ASM_REWRITE_TAC[BITSIZE_LE]; ALL_TAC] THEN
  UNDISCH_THEN `MIN (u + 1) (2 EXP 64 - 1) = d` (K ALL_TAC) THEN

  (*** The main loop, one 61-bit block per iteration ***)

  ENSURES_WHILE_UP_TAC `N:num` `pc + 0x1a4` `pc + 0x30c`
   `\i s. read X0 s = word k /\ read X1 s = z /\ read X2 s = word n /\
          read X3 s = x /\ read X4 s = m /\
          read X12 s = word(p DIV 64 + 1) /\ read X20 s = word p /\
          read X21 s = w /\
          read X16 s = word(61 * (N - i)) /\ read X17 s = word(61 * (i + 1)) /\
          read X19 s = word(MIN (k + 1) ((61 * (i + 1) + 63) DIV 64)) /\
          bignum_from_memory (x,n) s = a /\ bignum_from_memory (m,k) s = b /\
          (~(b = 0)
           ==> (2 EXP (64 * k) * val(read X23 s) + bignum_from_memory (z,k) s ==
                a DIV 2 EXP (61 * (N - i))) (mod b) /\
               2 EXP (64 * k) * val(read X23 s) + bignum_from_memory (z,k) s
               < 2 EXP (61 * (i + 1)) /\
               2 EXP (64 * k) * val(read X23 s) + bignum_from_memory (z,k) s
               < 2 EXP 64 * b /\
               read X15 s =
               word((2 EXP (64 * k) * val(read X23 s) +
                     bignum_from_memory (z,k) s) DIV 2 EXP p))` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [(*** Initialization of the loop with the top block a DIV 2 EXP (61 * N) ***)

    REWRITE_TAC[SUB_0; ADD_CLAUSES; MULT_CLAUSES;
                ARITH_RULE `(61 + 63) DIV 64 = 1`] THEN
    ENSURES_INIT_TAC "s0" THEN
    UNDISCH_TAC `bignum_from_memory (z,k) s0 = 0` THEN
    GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [BIGNUM_FROM_MEMORY_EXPAND] THEN
    ASM_REWRITE_TAC[ADD_EQ_0; MULT_EQ_0; EXP_EQ_0; ARITH_EQ; VAL_EQ_0] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN
     `read(memory :> bytes64(word_add x (word(8 * (n - 1))))) s0 =
      word(bigdigit a (n - 1))`
    ASSUME_TAC THENL
     [UNDISCH_TAC `bignum_from_memory (x,n) s0 = a` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      REWRITE_TAC[BIGDIGIT_BIGNUM_FROM_MEMORY] THEN
      UNDISCH_TAC `~(n = 0)` THEN
      SIMP_TAC[WORD_VAL; ARITH_RULE `~(n = 0) ==> n - 1 < n`];
      ALL_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[BIGNUM_FROM_MEMORY_BYTES]) THEN
    SUBGOAL_THEN `word_sub (word n) (word 1):int64 = word(n - 1) /\
                  val(word(n - 1):int64) = n - 1`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [ASM_SIMP_TAC[WORD_SUB; ARITH_RULE `~(n = 0) ==> 1 <= n`];
        MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
        UNDISCH_TAC `n < 2 EXP 58 - 1` THEN ARITH_TAC];
      ALL_TAC] THEN
    ARM_STEPS_TAC BIGNUM_MOD_EXEC (1--26) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `a DIV 2 EXP (61 * N) < 2 EXP 61` ASSUME_TAC THENL
     [SIMP_TAC[RDIV_LT_EQ; EXP_EQ_0; ARITH_EQ; GSYM EXP_ADD] THEN
      TRANS_TAC LTE_TRANS `2 EXP (64 * n)` THEN ASM_REWRITE_TAC[LE_EXP] THEN
      UNDISCH_TAC `64 * n <= 61 * N + 61` THEN ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `word_jushr (word (bigdigit a (n - 1))) (word (61 * N)):int64 =
      word(a DIV 2 EXP (61 * N))`
    SUBST_ALL_TAC THENL
     [SUBGOAL_THEN `61 * N = 64 * (n - 1) + (61 * N - 64 * (n - 1)) /\
                    61 * N - 64 * (n - 1) < 64`
      STRIP_ASSUME_TAC THENL
       [MAP_EVERY UNDISCH_TAC [`61 * N < 64 * n`; `64 * n <= 61 * N + 61`] THEN
        ARITH_TAC;
        ALL_TAC] THEN
      ASM_SIMP_TAC[GSYM HIGHDIGITS_TOP; highdigits] THEN
      REWRITE_TAC[word_jushr; GSYM VAL_EQ; VAL_WORD_USHR; VAL_WORD;
                  DIMINDEX_64] THEN
      SUBGOAL_THEN
       `a DIV 2 EXP (64 * (n - 1)) < 2 EXP 64 /\ 61 * N < 2 EXP 64 /\
        a DIV 2 EXP (61 * N) < 2 EXP 64`
      STRIP_ASSUME_TAC THENL
       [SIMP_TAC[RDIV_LT_EQ; EXP_EQ_0; ARITH_EQ; GSYM EXP_ADD] THEN
        REPEAT CONJ_TAC THENL
         [ASM_SIMP_TAC[ARITH_RULE `~(n = 0) ==> 64 * (n - 1) + 64 = 64 * n`];
          UNDISCH_TAC `61 * N < 64 * n` THEN UNDISCH_TAC `n < 2 EXP 58 - 1` THEN
          ARITH_TAC;
          UNDISCH_TAC `a DIV 2 EXP (61 * N) < 2 EXP 61` THEN
          SIMP_TAC[RDIV_LT_EQ; EXP_EQ_0; ARITH_EQ; GSYM EXP_ADD] THEN
          MATCH_MP_TAC(ARITH_RULE `x <= y ==> a < x ==> a < y`) THEN
          REWRITE_TAC[LE_EXP] THEN ARITH_TAC];
        ALL_TAC] THEN
      ASM_SIMP_TAC[MOD_LT] THEN
      SUBGOAL_THEN `(61 * N) MOD 64 = 61 * N - 64 * (n - 1)` SUBST1_TAC THENL
       [MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC `n - 1` THEN
        MAP_EVERY UNDISCH_TAC [`61 * N < 64 * n`; `64 * n <= 61 * N + 61`] THEN
        ARITH_TAC;
        ALL_TAC] THEN
      REWRITE_TAC[DIV_DIV; GSYM EXP_ADD] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
      MAP_EVERY UNDISCH_TAC [`61 * N < 64 * n`; `64 * n <= 61 * N + 61`] THEN
      ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `bignum_from_memory (z,k) s26 = a DIV 2 EXP (61 * N)`
    SUBST1_TAC THENL
     [ONCE_REWRITE_TAC[BIGNUM_FROM_MEMORY_EXPAND] THEN
      ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; MULT_CLAUSES; ADD_CLAUSES] THEN
      MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
      UNDISCH_TAC `a DIV 2 EXP (61 * N) < 2 EXP 61` THEN ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; VAL_WORD_0; MULT_CLAUSES;
                ADD_CLAUSES] THEN
    ASM_REWRITE_TAC[CONG_REFL] THEN
    SUBGOAL_THEN
     `val(word p:int64) = p /\ val(word_add (word k) (word 1):int64) = k + 1`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[GSYM WORD_ADD] THEN CONJ_TAC THEN
      MATCH_MP_TAC VAL_WORD_EQ THEN
      REWRITE_TAC[DIMINDEX_64] THEN
      MAP_EVERY UNDISCH_TAC [`p <= 64 * k`; `k < 2 EXP 58`] THEN ARITH_TAC;
      ASM_REWRITE_TAC[ARITH_RULE `~(k + 1 < 1) /\ MIN (k + 1) 1 = 1`]] THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ADD; VAL_WORD_USHR] THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN
      CONV_TAC NUM_REDUCE_CONV;
      ALL_TAC] THEN
    DISCH_TAC THEN CONJ_TAC THENL
     [TRANS_TAC LTE_TRANS `2 EXP 61` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `~(b = 0)` THEN ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `a DIV 2 EXP (61 * N) < 2 EXP 64 /\
                  a DIV 2 EXP (61 * N) DIV 2 EXP p < 2 EXP 64`
    STRIP_ASSUME_TAC THENL
     [MATCH_MP_TAC(MESON[DIV_LE; LET_TRANS]
       `!x e f. x < e ==> x < e /\ x DIV f < e`) THEN
      UNDISCH_TAC `a DIV 2 EXP (61 * N) < 2 EXP 61` THEN ARITH_TAC;
      ALL_TAC] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[word_jushr; DIMINDEX_64] THENL
     [ASM_SIMP_TAC[MOD_LT] THEN
      REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_USHR; VAL_WORD; DIMINDEX_64] THEN
      ASM_SIMP_TAC[MOD_LT];
      AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
      SIMP_TAC[DIV_EQ_0; EXP_EQ_0; ARITH_EQ] THEN
      TRANS_TAC LTE_TRANS `2 EXP 61` THEN ASM_REWRITE_TAC[LE_EXP; ARITH_EQ] THEN
      UNDISCH_TAC `~(p < 64)` THEN ARITH_TAC];

    (*** The main loop body: ghost the state and name the key quantities ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    GHOST_INTRO_TAC `h:int64` `read X15` THEN
    GHOST_INTRO_TAC `zt:int64` `read X23` THEN
    GHOST_INTRO_TAC `zm:num` `bignum_from_memory (z,k)` THEN
    GLOBALIZE_PRECONDITION_TAC THEN BIGNUM_TERMRANGE_TAC `k:num` `zm:num` THEN
    ABBREV_TAC `Z = 2 EXP (64 * k) * val(zt:int64) + zm` THEN
    REWRITE_TAC[ARITH_RULE `(i + 1) + 1 = i + 2`] THEN
    ABBREV_TAC `ib = 61 * (N - (i + 1))` THEN
    SUBGOAL_THEN `61 * (N - i) = ib + 61 /\ ib + 61 < 64 * n`
    (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC) THENL
     [EXPAND_TAC "ib" THEN
      MAP_EVERY UNDISCH_TAC [`i < N`; `61 * N < 64 * n`] THEN ARITH_TAC;
      UNDISCH_THEN `61 * (N - (i + 1)) = ib` (K ALL_TAC)] THEN

    (*** The old and new lengths L + 1 and l' of the accumulator ***)

    SUBGOAL_THEN
     `?L l'. MIN (k + 1) ((61 * (i + 1) + 63) DIV 64) = L + 1 /\
             MIN (k + 1) ((61 * (i + 2) + 63) DIV 64) = l' /\
             (if k + 1 <
                 val(word_ushr
                      (word_add (word(61 * (i + 1))) (word 124)) 6:int64)
              then word(k + 1)
              else word_ushr
                    (word_add (word(61 * (i + 1))) (word 124)) 6):int64 =
             word l' /\
             L <= k /\ (L = k \/ 61 * (i + 1) <= 64 * (L + 1)) /\
             L + 1 <= l' /\ l' <= L + 2 /\ l' <= k + 1 /\
             (L = k ==> l' = k + 1) /\
             (l' = k + 1 \/ 61 * (i + 2) <= 64 * l')`
    (X_CHOOSE_THEN `L:num` (X_CHOOSE_THEN `l':num`
      (CONJUNCTS_THEN2 SUBST_ALL_TAC (CONJUNCTS_THEN2 SUBST_ALL_TAC
        (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC))))) THENL
     [EXISTS_TAC `MIN (k + 1) ((61 * (i + 1) + 63) DIV 64) - 1` THEN
      EXISTS_TAC `MIN (k + 1) ((61 * (i + 2) + 63) DIV 64)` THEN
      REWRITE_TAC[] THEN CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
      CONJ_TAC THENL [ALL_TAC; ARITH_TAC] THEN
      SUBGOAL_THEN `k + 1 < 2 EXP 64 /\ 61 * (i + 2) + 63 < 2 EXP 64`
      STRIP_ASSUME_TAC THENL
       [MAP_EVERY UNDISCH_TAC
         [`k < 2 EXP 58`; `i < N`; `61 * N < 64 * n`; `n < 2 EXP 58 - 1`] THEN
        ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN
       `word_ushr (word_add (word(61 * (i + 1))) (word 124)) 6:int64 =
        word((61 * (i + 2) + 63) DIV 64)`
      SUBST1_TAC THENL
       [REWRITE_TAC[GSYM WORD_ADD; GSYM VAL_EQ; VAL_WORD_USHR; VAL_WORD;
                    DIMINDEX_64] THEN
        REWRITE_TAC[ARITH_RULE `61 * (i + 1) + 124 = 61 * (i + 2) + 63`] THEN
        ASM_SIMP_TAC[MOD_LT;
                     ARITH_RULE `x < 2 EXP 64 ==> x DIV 64 < 2 EXP 64`] THEN
        CONV_TAC NUM_REDUCE_CONV;
        ASM_SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; ARITH_RULE
         `x < 2 EXP 64 ==> x DIV 64 < 2 EXP 64`] THEN
        COND_CASES_TAC THEN AP_TERM_TAC THEN POP_ASSUM MP_TAC THEN ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `word_add (word k) (word 1):int64 = word(k + 1) /\
                  val(word(k + 1):int64) = k + 1`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[GSYM WORD_ADD] THEN MATCH_MP_TAC VAL_WORD_EQ THEN
      REWRITE_TAC[DIMINDEX_64] THEN UNDISCH_TAC `k < 2 EXP 58` THEN ARITH_TAC;
      ALL_TAC] THEN

    (*** The block cc of a to be shifted in, and the quotient estimate qw ***)

    ABBREV_TAC `cc = (a DIV 2 EXP ib) MOD 2 EXP 61` THEN
    ABBREV_TAC
     `qw =
      word_add (word((val(w:int64) * val(h:int64)) DIV 2 EXP 64)) h:int64` THEN
    SUBGOAL_THEN `cc < 2 EXP 61 /\ val(word(8 * cc):int64) = 8 * cc`
    STRIP_ASSUME_TAC THENL
     [MATCH_MP_TAC(MESON[] `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
       [EXPAND_TAC "cc" THEN REWRITE_TAC[MOD_LT_EQ; EXP_EQ_0; ARITH_EQ];
        DISCH_TAC THEN MATCH_MP_TAC VAL_WORD_EQ THEN
        REWRITE_TAC[DIMINDEX_64] THEN
        POP_ASSUM MP_TAC THEN ARITH_TAC];
      ALL_TAC] THEN

    (*** Load the next block and compute the quotient estimate ***)

    ENSURES_SEQUENCE_TAC `pc + 0x1f4`
     `\s. read X0 s = word k /\ read X1 s = z /\ read X2 s = word n /\
          read X3 s = x /\ read X4 s = m /\
          read X12 s = word(p DIV 64 + 1) /\ read X20 s = word p /\
          read X21 s = w /\ read X16 s = word ib /\
          read X17 s = word(61 * (i + 1)) /\ read X19 s = word(L + 1) /\
          bignum_from_memory (x,n) s = a /\ bignum_from_memory (m,k) s = b /\
          read X23 s = zt /\ bignum_from_memory (z,k) s = zm /\
          read X15 s = qw /\ read X5 s = qw /\
          read X8 s = word 0 /\ read X14 s = word 0 /\
          read X22 s = word(8 * cc)` THEN
    CONJ_TAC THENL
     [ABBREV_TAC `j = ib DIV 64` THEN
      SUBGOAL_THEN
       `ib < 2 EXP 64 /\ j < n /\ j + 1 < 2 EXP 64` STRIP_ASSUME_TAC THENL
       [EXPAND_TAC "j" THEN
        MAP_EVERY UNDISCH_TAC [`ib + 61 < 64 * n`; `n < 2 EXP 58 - 1`] THEN
        ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN
       `word_sub (word (ib + 61)) (word 61):int64 = word ib /\
        word_ushr (word ib) 6:int64 = word j /\ val(word j:int64) = j /\
        (if val(word_add (word j) (word 1):int64) < n
         then word_add (word j) (word 1) else word j):int64 =
        word(MIN (j + 1) (n - 1)) /\
        val(word(MIN (j + 1) (n - 1)):int64) = MIN (j + 1) (n - 1)`
      STRIP_ASSUME_TAC THENL
       [REPEAT CONJ_TAC THENL
         [REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE;
          REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_USHR; VAL_WORD; DIMINDEX_64] THEN
          ASM_SIMP_TAC[MOD_LT; ARITH_RULE `j + 1 < e ==> j < e`] THEN
          EXPAND_TAC "j" THEN CONV_TAC NUM_REDUCE_CONV;
          MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
          UNDISCH_TAC `j + 1 < 2 EXP 64` THEN ARITH_TAC;
          REWRITE_TAC[GSYM WORD_ADD] THEN
          ASM_SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64] THEN
          COND_CASES_TAC THEN AP_TERM_TAC THEN
          MAP_EVERY UNDISCH_TAC [`j < n`] THEN POP_ASSUM MP_TAC THEN ARITH_TAC;
          MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
          UNDISCH_TAC `j + 1 < 2 EXP 64` THEN ARITH_TAC];
        ALL_TAC] THEN
      ENSURES_INIT_TAC "s0" THEN
      SUBGOAL_THEN
       `!j. j < n ==> read(memory :> bytes64(word_add x (word(8 * j)))) s0 =
                      word(bigdigit a j)`
      (fun th -> MP_TAC(SPEC `j:num` th) THEN
                 MP_TAC(SPEC `MIN (j + 1) (n - 1)` th)) THENL
       [X_GEN_TAC `j':num` THEN DISCH_TAC THEN
        UNDISCH_TAC `bignum_from_memory (x,n) s0 = a` THEN
        DISCH_THEN(SUBST1_TAC o SYM) THEN
        ASM_REWRITE_TAC[BIGDIGIT_BIGNUM_FROM_MEMORY; WORD_VAL];
        ASM_REWRITE_TAC[ARITH_RULE `MIN (j + 1) (n - 1) < n <=> ~(n = 0)`] THEN
        REPEAT DISCH_TAC] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[BIGNUM_FROM_MEMORY_BYTES]) THEN
      ARM_STEPS_TAC BIGNUM_MOD_EXEC (1--20) THEN
      ENSURES_FINAL_STATE_TAC THEN
      ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      EXPAND_TAC "cc" THEN SUBST1_TAC(SYM(ASSUME `ib DIV 64 = j`)) THEN
      MATCH_MP_TAC BIGNUM_MOD_BLOCK THEN
      ASM_REWRITE_TAC[] THEN UNDISCH_TAC `ib + 61 < 64 * n` THEN ARITH_TAC;
      ALL_TAC] THEN

    (*** The inner loop, processing words 0..L-1 (possibly none) ***)

    ENSURES_SEQUENCE_TAC `pc + 0x244`
     `\s. read X0 s = word k /\ read X1 s = z /\ read X2 s = word n /\
          read X3 s = x /\ read X4 s = m /\
          read X12 s = word(p DIV 64 + 1) /\ read X20 s = word p /\
          read X21 s = w /\ read X16 s = word ib /\
          read X17 s = word(61 * (i + 1)) /\ read X19 s = word(L + 1) /\
          bignum_from_memory (x,n) s = a /\ bignum_from_memory (m,k) s = b /\
          read X23 s = zt /\ read X15 s = qw /\ read X8 s = word L /\
          bignum_from_memory (word_add z (word(8 * L)),k - L) s =
          highdigits zm L /\
          &(bignum_from_memory(z,L) s) +
          &2 pow (64 * L) *
          (&(val(read X22 s) DIV 8) + &2 pow 61 * &(val(read X5 s))) =
          &2 pow 61 * (&(lowdigits zm L) +
                       &(val qw) *
                       (&2 pow (64 * L) - &(lowdigits b L))) + &cc /\
          read X14 s =
          word(bigdigit (bignum_from_memory(z,L) s) (p DIV 64 + 1)) /\
          (p DIV 64 + 1 <= L
           ==> read X13 s =
               word(bigdigit (bignum_from_memory(z,L) s) (p DIV 64)))` THEN
    CONJ_TAC THENL
     [ASM_CASES_TAC `L = 0` THENL
       [ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; WORD_ADD_0; SUB_0;
                        HIGHDIGITS_0;
                        BIGNUM_FROM_MEMORY_TRIVIAL; LOWDIGITS_0; BIGDIGIT_0;
                        ARITH_RULE `~(p + 1 <= 0)`] THEN
        ARM_SIM_TAC BIGNUM_MOD_EXEC (1--2) THEN
        REWRITE_TAC[ARITH_RULE `(8 * c) DIV 8 = c`] THEN REAL_ARITH_TAC;
        SUBGOAL_THEN
         `word_sub (word (L + 1)) (word 1):int64 = word L /\
          val(word L:int64) = L /\
          val(word(p DIV 64 + 1):int64) = p DIV 64 + 1`
        STRIP_ASSUME_TAC THENL
         [REPEAT CONJ_TAC THENL
           [REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE;
            MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
            MAP_EVERY UNDISCH_TAC [`L <= k`; `k < 2 EXP 58`] THEN ARITH_TAC;
            MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
            MAP_EVERY UNDISCH_TAC [`p <= 64 * k`; `k < 2 EXP 58`] THEN
            ARITH_TAC];
          ALL_TAC] THEN
        ENSURES_WHILE_UP_TAC `L:num` `pc + 0x1fc` `pc + 0x23c`
         `\j s. read X0 s = word k /\ read X1 s = z /\ read X2 s = word n /\
                read X3 s = x /\ read X4 s = m /\
                read X12 s = word(p DIV 64 + 1) /\ read X20 s = word p /\
                read X21 s = w /\ read X16 s = word ib /\
                read X17 s = word(61 * (i + 1)) /\ read X19 s = word(L + 1) /\
                bignum_from_memory (x,n) s = a /\
                bignum_from_memory (m,k) s = b /\
                read X23 s = zt /\ read X15 s = qw /\
                read X8 s = word j /\ read X11 s = word L /\
                bignum_from_memory (word_add z (word(8 * j)),k - j) s =
                highdigits zm j /\
                &(bignum_from_memory(z,j) s) +
                &2 pow (64 * j) *
                (&(val(read X22 s) DIV 8) + &2 pow 61 * &(val(read X5 s))) =
                &2 pow 61 * (&(lowdigits zm j) +
                             &(val qw) *
                             (&2 pow (64 * j) - &(lowdigits b j))) + &cc /\
                read X14 s =
                word(bigdigit (bignum_from_memory(z,j) s) (p DIV 64 + 1)) /\
                (p DIV 64 + 1 <= j
                 ==> read X13 s =
                     word(bigdigit (bignum_from_memory(z,j) s)
                                   (p DIV 64)))` THEN
        ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
         [REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0; SUB_0; HIGHDIGITS_0;
                      BIGNUM_FROM_MEMORY_TRIVIAL; LOWDIGITS_0; BIGDIGIT_0;
                      ARITH_RULE `~(p + 1 <= 0)`] THEN
          ARM_SIM_TAC BIGNUM_MOD_EXEC (1--2) THEN
          REWRITE_TAC[ARITH_RULE `(8 * c) DIV 8 = c`] THEN REAL_ARITH_TAC;
          X_GEN_TAC `j:num` THEN STRIP_TAC THEN
          GHOST_INTRO_TAC `hin:int64` `read X5` THEN
          GHOST_INTRO_TAC `cin:int64` `read X22` THEN
          GHOST_INTRO_TAC `lf:int64` `read X13` THEN
          GHOST_INTRO_TAC `hf:int64` `read X14` THEN
          GHOST_INTRO_TAC `zj:num` `bignum_from_memory (z,j)` THEN
          GLOBALIZE_PRECONDITION_TAC THEN
          SUBGOAL_THEN `j < k /\ val(word j:int64) = j` STRIP_ASSUME_TAC THENL
           [CONJ_TAC THENL
             [ALL_TAC;
              MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64]] THEN
            MAP_EVERY UNDISCH_TAC [`j < L`; `L <= k`; `k < 2 EXP 58`] THEN
            ARITH_TAC;
            ALL_TAC] THEN
          GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ONCE_DEPTH_CONV)
           [BIGNUM_FROM_MEMORY_OFFSET_EQ_HIGHDIGITS] THEN
          ASM_REWRITE_TAC[ARITH_RULE `k - j = 0 <=> ~(j < k)`] THEN
          REWRITE_TAC[ARITH_RULE `k - j - 1 = k - (j + 1)`] THEN
          REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP; BIGNUM_FROM_MEMORY_BYTES] THEN
          ENSURES_INIT_TAC "s0" THEN
          SUBGOAL_THEN
           `read(memory :> bytes64(word_add m (word(8 * j)))) s0 =
            word(bigdigit b j)`
          ASSUME_TAC THENL
           [UNDISCH_TAC `read (memory :> bytes (m,8 * k)) s0 = b` THEN
            DISCH_THEN(SUBST1_TAC o SYM) THEN
            REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES;
                        BIGDIGIT_BIGNUM_FROM_MEMORY] THEN
            ASM_REWRITE_TAC[WORD_VAL];
            ALL_TAC] THEN
          ARM_ACCSTEPS_TAC BIGNUM_MOD_EXEC [3;4;6;8;9] (1--16) THEN
          ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
          CONJ_TAC THENL [REWRITE_TAC[WORD_ADD]; ALL_TAC] THEN
          SUBGOAL_THEN `zj < 2 EXP (64 * j)` ASSUME_TAC THENL
           [UNDISCH_TAC `read (memory :> bytes (z,8 * j)) s16 = zj` THEN
            DISCH_THEN(SUBST1_TAC o SYM) THEN
            REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES;
                        BIGNUM_FROM_MEMORY_BOUND];
            ALL_TAC] THEN
          CONJ_TAC THENL
           [ALL_TAC;
            REWRITE_TAC[VAL_WORD_SUB_EQ_0] THEN ASM_REWRITE_TAC[] THEN
            MP_TAC(SPECL [`zj:num`; `j:num`; `p DIV 64 + 1`;
                          `word_subword
                            (word_join (sum_s8:int64) (cin:int64):int128)
                            (3,64):int64`;
                          `lf:int64`; `word(bigdigit zj (p DIV 64 + 1)):int64`]
                  BIGNUM_MOD_LOGSTEP) THEN
            REWRITE_TAC[ADD_EQ_0; ARITH_EQ; ADD_SUB] THEN
            ANTS_TAC THENL [ASM_REWRITE_TAC[]; MESON_TAC[]]] THEN
          SUBGOAL_THEN `~carry_s9` ASSUME_TAC THENL
           [DISCH_TAC THEN
            SUBGOAL_THEN
             `&(val(qw:int64)) * &(val(word_not(word(bigdigit b j)):int64)) <=
              (&2 pow 64 - &1) * (&2 pow 64 - &1):real`
            MP_TAC THENL
             [MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_POS] THEN
              REWRITE_TAC[REAL_ARITH
                           `x <= &2 pow 64 - &1 <=> x + &1 <= &2 pow 64`] THEN
              REWRITE_TAC[REAL_OF_NUM_CLAUSES;
                          ARITH_RULE `x + 1 <= y <=> x < y`] THEN
              REWRITE_TAC[VAL_BOUND_64];
              ALL_TAC] THEN
            MP_TAC(SPECL [`zm:num`; `j:num`] BIGDIGIT_BOUND) THEN
            MP_TAC(ISPEC `hin:int64` VAL_BOUND_64) THEN
            REWRITE_TAC[ARITH_RULE `x < 2 EXP 64 <=> x + 1 <= 2 EXP 64`] THEN
            MP_TAC(SPEC `val(sum_s8:int64)` REAL_POS) THEN
            MP_TAC(SPEC `val(sum_s9:int64)` REAL_POS) THEN
            ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
            ASM_CASES_TAC `carry_s6:bool` THEN
            ASM_REWRITE_TAC[BITVAL_CLAUSES; VAL_WORD_BIGDIGIT; VAL_WORD_0;
                            VAL_WORD_1;
                            REAL_VAL_WORD_NOT; DIMINDEX_64] THEN
            REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN REAL_ARITH_TAC;
            ALL_TAC] THEN
          MP_TAC(SPECL [`sum_s8:int64`; `cin:int64`] BIGNUM_MOD_EXTR) THEN
          FIRST_X_ASSUM(MP_TAC o check (free_in `&zj:real` o concl)) THEN
          ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
          ASM_CASES_TAC `carry_s6:bool` THEN
          ASM_REWRITE_TAC[BITVAL_CLAUSES; VAL_WORD_BIGDIGIT; VAL_WORD_0;
                          VAL_WORD_1;
                          REAL_VAL_WORD_NOT; DIMINDEX_64;
                          LOWDIGITS_CLAUSES] THEN
          REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES;
                      ARITH_RULE `64 * (j + 1) = 64 * j + 64`;
                      REAL_POW_ADD] THEN
          CONV_TAC REAL_RING;

          X_GEN_TAC `j:num` THEN STRIP_TAC THEN
          SUBGOAL_THEN `val(word j:int64) = j` ASSUME_TAC THENL
           [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
            MAP_EVERY UNDISCH_TAC [`j < L`; `L <= k`; `k < 2 EXP 58`] THEN
            ARITH_TAC;
            ARM_SIM_TAC BIGNUM_MOD_EXEC (1--2) THEN
            ASM_REWRITE_TAC[VAL_WORD_SUB_EQ_0]];
          ARM_SIM_TAC BIGNUM_MOD_EXEC (1--2)]];
      ALL_TAC] THEN

    (*** The mathematics of one iteration: the new accumulator value Z' ***)

    ABBREV_TAC `Z' = 2 EXP 61 * (Z - val(qw:int64) * b) + cc` THEN
    SUBGOAL_THEN
     `~(b = 0)
      ==> val(qw:int64) * b <= Z /\ Z < 2 EXP (64 * (L + 1)) /\
          val qw * lowdigits b (L + 1) = val qw * b /\
          Z' < 2 EXP 64 * b /\ Z' < 2 EXP (61 * (i + 2)) /\
          Z' < 2 EXP (64 * l') /\
          (Z' == a DIV 2 EXP ib) (mod b)`
    ASSUME_TAC THENL
     [DISCH_TAC THEN BIGNUM_MOD_UNGUARD_TAC THEN
      MP_TAC(SPECL [`b:num`; `p:num`; `u:num`; `d:num`; `w:int64`; `Z:num`;
                    `h:int64`; `qw:int64`] BIGNUM_MOD_ESTIMATE) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      SUBGOAL_THEN `Z < 2 EXP (64 * (L + 1))` ASSUME_TAC THENL
       [UNDISCH_THEN `L = k \/ 61 * (i + 1) <= 64 * (L + 1)`
         (DISJ_CASES_THEN ASSUME_TAC) THENL
         [TRANS_TAC LTE_TRANS `2 EXP 64 * b` THEN ASM_REWRITE_TAC[] THEN
          ASM_REWRITE_TAC[ARITH_RULE `64 * (k + 1) = 64 + 64 * k`; EXP_ADD;
                          LE_MULT_LCANCEL] THEN
          ASM_SIMP_TAC[LT_IMP_LE];
          TRANS_TAC LTE_TRANS `2 EXP (61 * (i + 1))` THEN
          ASM_REWRITE_TAC[LE_EXP] THEN
          ASM_REWRITE_TAC[ARITH_EQ]];
        ALL_TAC] THEN
      SUBGOAL_THEN `Z' < 2 EXP 64 * b /\ Z' < 2 EXP (61 * (i + 2))`
      STRIP_ASSUME_TAC THENL
       [EXPAND_TAC "Z'" THEN
        REWRITE_TAC[ARITH_RULE `61 * (i + 2) = 61 + 61 * (i + 1)`; EXP_ADD] THEN
        MAP_EVERY UNDISCH_TAC
         [`val(qw:int64) * b <= Z`; `Z < val(qw:int64) * b + 6 * b`;
          `Z < 2 EXP (61 * (i + 1))`; `cc < 2 EXP 61`] THEN
        SPEC_TAC(`2 EXP (61 * (i + 1))`,`e:num`) THEN ARITH_TAC;
        ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [ASM_CASES_TAC `b < 2 EXP (64 * (L + 1))` THEN
        ASM_SIMP_TAC[LOWDIGITS_SELF] THEN
        SUBGOAL_THEN
         `val(qw:int64) = 0` (fun th -> REWRITE_TAC[th; MULT_CLAUSES]) THEN
        MATCH_MP_TAC BIGNUM_MOD_QZERO THEN
        MAP_EVERY EXISTS_TAC [`b:num`; `Z:num`] THEN
        ASM_REWRITE_TAC[] THEN
        MAP_EVERY UNDISCH_TAC
         [`Z < 2 EXP (64 * (L + 1))`; `~(b < 2 EXP (64 * (L + 1)))`] THEN
        ARITH_TAC;
        UNDISCH_THEN `l' = k + 1 \/ 61 * (i + 2) <= 64 * l'`
         (DISJ_CASES_THEN ASSUME_TAC) THENL
         [TRANS_TAC LTE_TRANS `2 EXP 64 * b` THEN ASM_REWRITE_TAC[] THEN
          ASM_REWRITE_TAC[ARITH_RULE `64 * (k + 1) = 64 + 64 * k`; EXP_ADD;
                          LE_MULT_LCANCEL] THEN
          ASM_SIMP_TAC[LT_IMP_LE];
          TRANS_TAC LTE_TRANS `2 EXP (61 * (i + 2))` THEN
          ASM_REWRITE_TAC[LE_EXP] THEN
          ASM_REWRITE_TAC[ARITH_EQ]];
        SUBGOAL_THEN `a DIV 2 EXP ib = 2 EXP 61 * a DIV 2 EXP (ib + 61) + cc`
        SUBST1_TAC THENL
         [EXPAND_TAC "cc" THEN REWRITE_TAC[EXP_ADD; GSYM DIV_DIV] THEN
          MP_TAC(SPECL [`a DIV 2 EXP ib`; `2 EXP 61`] DIVISION) THEN
          REWRITE_TAC[EXP_EQ_0; ARITH_EQ] THEN ARITH_TAC;
          ALL_TAC] THEN
        SUBGOAL_THEN `Z' + 2 EXP 61 * (val(qw:int64) * b) = 2 EXP 61 * Z + cc`
        MP_TAC THENL
         [EXPAND_TAC "Z'" THEN UNDISCH_TAC `val(qw:int64) * b <= Z` THEN
          ARITH_TAC;
          UNDISCH_TAC `(Z == a DIV 2 EXP (ib + 61)) (mod b)` THEN
          CONV_TAC NUMBER_RULE]];
      ALL_TAC] THEN

    (*** The tail of the negadd-and-shift, merging at the noel label ***)

    ENSURES_SEQUENCE_TAC `pc + 0x2e4`
     `\s. read X0 s = word k /\ read X1 s = z /\ read X2 s = word n /\
          read X3 s = x /\ read X4 s = m /\
          read X12 s = word(p DIV 64 + 1) /\ read X20 s = word p /\
          read X21 s = w /\ read X16 s = word ib /\
          read X17 s = word(61 * (i + 2)) /\ read X19 s = word l' /\
          read X8 s = word l' /\
          bignum_from_memory (x,n) s = a /\ bignum_from_memory (m,k) s = b /\
          (~(b = 0)
           ==> 2 EXP (64 * k) * val(read X23 s) +
               bignum_from_memory (z,k) s = Z' /\
               read X22 s = word(bigdigit Z' (l' - 1)) /\
               read X14 s = word(bigdigit Z' (p DIV 64 + 1)) /\
               (p DIV 64 + 1 <= l'
                ==> read X13 s = word(bigdigit Z' (p DIV 64))))` THEN
    CONJ_TAC THENL
     [ALL_TAC;

      (*** The final selection of the new top word h of Z' ***)

      GHOST_INTRO_TAC `lf:int64` `read X13` THEN
      GHOST_INTRO_TAC `hf:int64` `read X14` THEN
      GHOST_INTRO_TAC `cw:int64` `read X22` THEN
      GHOST_INTRO_TAC `zt':int64` `read X23` THEN
      GHOST_INTRO_TAC `zm':num` `bignum_from_memory (z,k)` THEN
      GLOBALIZE_PRECONDITION_TAC THEN
      SUBGOAL_THEN `val(word l':int64) = l' /\
                    val(word(p DIV 64 + 1):int64) = p DIV 64 + 1`
      STRIP_ASSUME_TAC THENL
       [CONJ_TAC THEN MATCH_MP_TAC VAL_WORD_EQ THEN
        REWRITE_TAC[DIMINDEX_64] THEN
        MAP_EVERY UNDISCH_TAC [`l' <= k + 1`; `p <= 64 * k`;
                               `k < 2 EXP 58`] THEN
        ARITH_TAC;
        ALL_TAC] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
      ARM_STEPS_TAC BIGNUM_MOD_EXEC (1--10) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      DISCH_TAC THEN BIGNUM_MOD_UNGUARD_TAC THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN
       `(if val(word_sub (word l') (word (p DIV 64 + 1)):int64) = 0
         then word(bigdigit Z' (l' - 1))
         else if p DIV 64 + 1 <= l' then lf else word 0):int64 =
        word(bigdigit Z' (p DIV 64))`
      SUBST1_TAC THENL
       [ASM_REWRITE_TAC[VAL_WORD_SUB_EQ_0] THEN
        ASM_CASES_TAC `l' = p DIV 64 + 1` THEN
        ASM_REWRITE_TAC[ADD_SUB; LE_REFL] THEN
        COND_CASES_TAC THEN ASM_SIMP_TAC[] THEN
        AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC BIGDIGIT_ZERO THEN
        TRANS_TAC LTE_TRANS `2 EXP (64 * l')` THEN
        ASM_REWRITE_TAC[LE_EXP; ARITH_EQ] THEN
        MAP_EVERY UNDISCH_TAC [`~(p DIV 64 + 1 <= l')`] THEN ARITH_TAC;
        ALL_TAC] THEN
      MP_TAC(SPECL [`Z':num`; `p DIV 64 + 1`; `p:num`; `bigdigit Z' (p DIV 64)`;
                    `bigdigit Z' (p DIV 64 + 1)`] BIGNUM_MOD_FIELD) THEN
      REWRITE_TAC[ADD_EQ_0; ARITH_EQ; ADD_SUB] THEN DISCH_THEN SUBST1_TAC THEN
      AP_TERM_TAC THEN
      SUBGOAL_THEN `64 * (p DIV 64 + 1) + p MOD 64 = 64 + p` SUBST1_TAC THENL
       [MP_TAC(SPECL [`p:num`; `64`] DIVISION) THEN ARITH_TAC;
        SIMP_TAC[EXP_ADD; DIV_MULT2; EXP_EQ_0; ARITH_EQ]]] THEN

    (*** The last word of the negadd-and-shift, and possibly an extension ***)

    GHOST_INTRO_TAC `hh:int64` `read X5` THEN
    GHOST_INTRO_TAC `cin:int64` `read X22` THEN
    GHOST_INTRO_TAC `lf:int64` `read X13` THEN
    GHOST_INTRO_TAC `hf:int64` `read X14` THEN
    GHOST_INTRO_TAC `W:num` `bignum_from_memory (z,L)` THEN
    GLOBALIZE_PRECONDITION_TAC THEN
    SUBGOAL_THEN `val(word(p DIV 64 + 1):int64) = p DIV 64 + 1 /\
                  val(word L:int64) = L /\ val(word(L + 1):int64) = L + 1 /\
                  word_add (word L) (word 1):int64 = word(L + 1)`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[GSYM WORD_ADD] THEN
      REPEAT CONJ_TAC THEN MATCH_MP_TAC VAL_WORD_EQ THEN
      REWRITE_TAC[DIMINDEX_64] THEN
      MAP_EVERY UNDISCH_TAC [`L <= k`; `p <= 64 * k`; `k < 2 EXP 58`] THEN
      ARITH_TAC;
      ALL_TAC] THEN
    ASM_CASES_TAC `L:num = k` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN
      FIRST_X_ASSUM(SUBST_ALL_TAC o C MP (REFL `k:num`)) THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
      ARM_STEPS_TAC BIGNUM_MOD_EXEC (1--24) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL
       [REWRITE_TAC[GSYM WORD_ADD] THEN AP_TERM_TAC THEN ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `W < 2 EXP (64 * k)` ASSUME_TAC THENL
       [UNDISCH_TAC `read (memory :> bytes (z,8 * k)) s24 = W` THEN
        DISCH_THEN(SUBST1_TAC o SYM) THEN
        REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES; BIGNUM_FROM_MEMORY_BOUND];
        ALL_TAC] THEN
      DISCH_TAC THEN BIGNUM_MOD_UNGUARD_TAC THEN
      ABBREV_TAC
       `ss = word_add (word_add zt hh)
              (word (0 + val(qw:int64) * 18446744073709551615)):int64` THEN
      ABBREV_TAC `c' = word_subword (word_join (ss:int64) (cin:int64):int128)
                                    (3,64):int64` THEN
      MP_TAC(SPECL [`W:num`; `k:num`; `val(cin:int64)`; `val(hh:int64)`;
                    `val(ss:int64)`; `val(zt:int64)`; `0`; `val(qw:int64)`;
                    `cc:num`; `lowdigits zm k`; `lowdigits b k`;
                    `Z - val(qw:int64) * b`; `val(c':int64)`]
             BIGNUM_MOD_TAIL) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[VAL_BOUND_64] THEN REPEAT CONJ_TAC THENL
         [EXPAND_TAC "c'" THEN REWRITE_TAC[BIGNUM_MOD_EXTR];
          EXPAND_TAC "ss" THEN
          REWRITE_TAC[VAL_WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
          CONV_TAC MOD_DOWN_CONV THEN REWRITE_TAC[CONG_LMOD] THEN
          REWRITE_TAC[ADD_CLAUSES; SUB_0] THEN CONV_TAC NUM_REDUCE_CONV THEN
          REWRITE_TAC[CONG_REFL; ADD_ASSOC];
          CONV_TAC NUM_REDUCE_CONV;
          ASM_SIMP_TAC[LOWDIGITS_SELF; MULT_CLAUSES; ADD_CLAUSES] THEN
          MAP_EVERY UNDISCH_TAC
           [`val(qw:int64) * b <= Z`;
            `2 EXP (64 * k) * val(zt:int64) + zm = Z`] THEN
          ARITH_TAC;
          UNDISCH_TAC `Z < 2 EXP (64 * (k + 1))` THEN ARITH_TAC];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      SUBGOAL_THEN `val(ss:int64) DIV 8 = 0` ASSUME_TAC THENL
       [MATCH_MP_TAC BIGNUM_MOD_QZERO THEN
        MAP_EVERY EXISTS_TAC [`2 EXP (64 * (k + 1))`; `Z':num`] THEN
        ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `W + 2 EXP (64 * k) * val(c':int64) +
                     2 EXP (64 * (k + 1)) * val(ss:int64) DIV 8 = Z'` THEN
        ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `W + 2 EXP (64 * k) * val(c':int64) = Z'` ASSUME_TAC THENL
       [UNDISCH_TAC `W + 2 EXP (64 * k) * val(c':int64) +
                     2 EXP (64 * (k + 1)) * val(ss:int64) DIV 8 = Z'` THEN
        ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES];
        ALL_TAC] THEN
      CONJ_TAC THENL
       [ONCE_REWRITE_TAC[ADD_SYM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      UNDISCH_THEN
       `W + 2 EXP (64 * k) * val(c':int64) = Z'` (SUBST1_TAC o SYM) THEN
      MP_TAC(SPECL [`W:num`; `k:num`; `p DIV 64 + 1`; `c':int64`; `lf:int64`;
                    `word(bigdigit W (p DIV 64 + 1)):int64`]
             BIGNUM_MOD_LOGSTEP) THEN
      ASM_REWRITE_TAC[ADD_EQ_0; ARITH_EQ; ADD_SUB; VAL_WORD_SUB_EQ_0] THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
      REWRITE_TAC[bigdigit] THEN SIMP_TAC[DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ] THEN
      ASM_SIMP_TAC[DIV_LT; ADD_CLAUSES; MOD_LT; VAL_BOUND_64; WORD_VAL];
      ALL_TAC] THEN

    (*** The case L < k: the last word of the negadd is stored in memory ***)

    SUBGOAL_THEN `L < k` ASSUME_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`L <= k`; `~(L:num = k)`] THEN ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `~(b = 0) ==> val(zt:int64) = 0 /\ zm:num = Z` ASSUME_TAC THENL
     [DISCH_TAC THEN BIGNUM_MOD_UNGUARD_TAC THEN
      MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
       [MATCH_MP_TAC BIGNUM_MOD_QZERO THEN
        MAP_EVERY EXISTS_TAC [`2 EXP (64 * k)`; `Z:num`] THEN CONJ_TAC THENL
         [UNDISCH_TAC `2 EXP (64 * k) * val(zt:int64) + zm = Z` THEN ARITH_TAC;
          TRANS_TAC LTE_TRANS `2 EXP (64 * (L + 1))` THEN
          ASM_REWRITE_TAC[LE_EXP] THEN
          UNDISCH_TAC `L < k` THEN ARITH_TAC];
        DISCH_TAC THEN
        UNDISCH_TAC `2 EXP (64 * k) * val(zt:int64) + zm = Z` THEN
        ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES]];
      ALL_TAC] THEN
    ENSURES_SEQUENCE_TAC `pc + 0x29c`
     `\s. read X0 s = word k /\ read X1 s = z /\ read X2 s = word n /\
          read X3 s = x /\ read X4 s = m /\
          read X12 s = word(p DIV 64 + 1) /\ read X20 s = word p /\
          read X21 s = w /\ read X16 s = word ib /\
          read X17 s = word(61 * (i + 1)) /\ read X8 s = word(L + 1) /\
          bignum_from_memory (x,n) s = a /\ bignum_from_memory (m,k) s = b /\
          read X23 s = zt /\
          bignum_from_memory (word_add z (word(8 * (L + 1))),k - (L + 1)) s =
          highdigits zm (L + 1) /\
          read X22 s = word(bigdigit (bignum_from_memory(z,L + 1) s) L) /\
          read X14 s =
          word(bigdigit (bignum_from_memory(z,L + 1) s) (p DIV 64 + 1)) /\
          (p DIV 64 + 1 <= L + 1
           ==> read X13 s =
               word(bigdigit (bignum_from_memory(z,L + 1) s) (p DIV 64))) /\
          (~(b = 0)
           ==> bignum_from_memory(z,L + 1) s +
               2 EXP (64 * (L + 1)) * val(read X10 s) DIV 8 = Z')` THEN
    CONJ_TAC THENL
     [(*** The last word of the negadd, stored in memory ***)

      GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ONCE_DEPTH_CONV)
       [BIGNUM_FROM_MEMORY_OFFSET_EQ_HIGHDIGITS] THEN
      ASM_REWRITE_TAC[ARITH_RULE `k - L = 0 <=> ~(L < k)`] THEN
      REWRITE_TAC[ARITH_RULE `k - L - 1 = k - (L + 1)`] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP; BIGNUM_FROM_MEMORY_BYTES] THEN
      ENSURES_INIT_TAC "s0" THEN
      SUBGOAL_THEN
       `~(val(word_sub (word L) (word k):int64) = 0)` ASSUME_TAC THENL
       [ASM_REWRITE_TAC[VAL_WORD_SUB_EQ_0]; ALL_TAC] THEN
      SUBGOAL_THEN
       `read(memory :> bytes64(word_add m (word(8 * L)))) s0 =
        word(bigdigit b L)`
      ASSUME_TAC THENL
       [UNDISCH_TAC `read (memory :> bytes (m,8 * k)) s0 = b` THEN
        DISCH_THEN(SUBST1_TAC o SYM) THEN
        REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES;
                    BIGDIGIT_BIGNUM_FROM_MEMORY] THEN
        ASM_REWRITE_TAC[WORD_VAL];
        ALL_TAC] THEN
      SUBGOAL_THEN `W < 2 EXP (64 * L)` ASSUME_TAC THENL
       [UNDISCH_TAC `read (memory :> bytes (z,8 * L)) s0 = W` THEN
        DISCH_THEN(SUBST1_TAC o SYM) THEN
        REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES; BIGNUM_FROM_MEMORY_BOUND];
        ALL_TAC] THEN
      ARM_STEPS_TAC BIGNUM_MOD_EXEC (1--17) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      ABBREV_TAC
       `ss = word_add (word_add (word (bigdigit zm L)) hh)
              (word (0 + val(qw:int64) *
                         val(word_not(word(bigdigit b L)):int64))):int64` THEN
      ABBREV_TAC `c' = word_subword (word_join (ss:int64) (cin:int64):int128)
                                    (3,64):int64` THEN
      MP_TAC(SPECL [`W:num`; `L:num`; `p DIV 64 + 1`; `c':int64`; `lf:int64`;
                    `word(bigdigit W (p DIV 64 + 1)):int64`]
             BIGNUM_MOD_LOGSTEP) THEN
      ASM_REWRITE_TAC[ADD_EQ_0; ARITH_EQ; ADD_SUB; VAL_WORD_SUB_EQ_0] THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN CONJ_TAC THENL
       [REWRITE_TAC[bigdigit] THEN
        SIMP_TAC[DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ] THEN
        ASM_SIMP_TAC[DIV_LT; ADD_CLAUSES; MOD_LT; VAL_BOUND_64; WORD_VAL];
        ALL_TAC] THEN
      DISCH_TAC THEN BIGNUM_MOD_UNGUARD_TAC THEN
      UNDISCH_THEN `zm:num = Z` SUBST_ALL_TAC THEN
      MP_TAC(SPECL [`W:num`; `L:num`; `val(cin:int64)`; `val(hh:int64)`;
                    `val(ss:int64)`; `bigdigit Z L`; `bigdigit b L`;
                    `val(qw:int64)`; `cc:num`; `lowdigits Z L`; `lowdigits b L`;
                    `Z - val(qw:int64) * b`; `val(c':int64)`]
             BIGNUM_MOD_TAIL) THEN
      ASM_REWRITE_TAC[VAL_BOUND_64; BIGDIGIT_BOUND; ADD_ASSOC] THEN
      DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
       [EXPAND_TAC "c'" THEN REWRITE_TAC[BIGNUM_MOD_EXTR];
        EXPAND_TAC "ss" THEN
        REWRITE_TAC[VAL_WORD_ADD; VAL_WORD; DIMINDEX_64; VAL_WORD_NOT;
                    VAL_WORD_BIGDIGIT] THEN
        CONV_TAC MOD_DOWN_CONV THEN
        REWRITE_TAC[CONG_LMOD; ADD_CLAUSES; ADD_ASSOC; CONG_REFL];
        REWRITE_TAC[ARITH_RULE `l + e * d:num = e * d + l`;
                    GSYM LOWDIGITS_CLAUSES] THEN
        ASM_SIMP_TAC[LOWDIGITS_SELF] THEN
        UNDISCH_TAC `val(qw:int64) * b <= Z` THEN ARITH_TAC;
        UNDISCH_TAC `Z < 2 EXP (64 * (L + 1))` THEN ARITH_TAC];

      (*** Possibly an extension of the shifted result by one more word ***)

      GHOST_INTRO_TAC `lf1:int64` `read X13` THEN
      GHOST_INTRO_TAC `hf1:int64` `read X14` THEN
      GHOST_INTRO_TAC `cw:int64` `read X22` THEN
      GHOST_INTRO_TAC `sw:int64` `read X10` THEN
      GHOST_INTRO_TAC `zl:num` `bignum_from_memory (z,L + 1)` THEN
      GLOBALIZE_PRECONDITION_TAC THEN
      SUBGOAL_THEN `val(word l':int64) = l'` ASSUME_TAC THENL
       [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
        MAP_EVERY UNDISCH_TAC [`l' <= k + 1`; `k < 2 EXP 58`] THEN ARITH_TAC;
        ALL_TAC] THEN
      ASM_CASES_TAC `l':num = L + 1` THENL
       [FIRST_X_ASSUM SUBST_ALL_TAC THEN
        REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
        ARM_STEPS_TAC BIGNUM_MOD_EXEC (1--8) THEN
        ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
        CONJ_TAC THENL
         [REWRITE_TAC[GSYM WORD_ADD] THEN AP_TERM_TAC THEN ARITH_TAC;
          ALL_TAC] THEN
        DISCH_TAC THEN BIGNUM_MOD_UNGUARD_TAC THEN
        UNDISCH_THEN `zm:num = Z` SUBST_ALL_TAC THEN
        SUBGOAL_THEN `zl:num = Z'` SUBST_ALL_TAC THENL
         [SUBGOAL_THEN `val(sw:int64) DIV 8 = 0` ASSUME_TAC THENL
           [MATCH_MP_TAC BIGNUM_MOD_QZERO THEN
            MAP_EVERY EXISTS_TAC [`2 EXP (64 * (L + 1))`; `Z':num`] THEN
            ASM_REWRITE_TAC[] THEN
            UNDISCH_TAC
             `zl + 2 EXP (64 * (L + 1)) * val(sw:int64) DIV 8 = Z'` THEN
            ARITH_TAC;
            UNDISCH_TAC
             `zl + 2 EXP (64 * (L + 1)) * val(sw:int64) DIV 8 = Z'` THEN
            ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES]];
          ALL_TAC] THEN
        ASM_REWRITE_TAC[ADD_SUB] THEN
        SUBGOAL_THEN
         `read (memory :> bytes (z,8 * k)) s8 =
          2 EXP (64 * (L + 1)) * highdigits Z (L + 1) + Z'`
        SUBST1_TAC THENL
         [REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
          MP_TAC(SPECL [`z:int64`; `L + 1`; `k - (L + 1)`; `s8:armstate`]
            BIGNUM_FROM_MEMORY_SPLIT) THEN
          ASM_SIMP_TAC[ARITH_RULE `L < k ==> (L + 1) + (k - (L + 1)) = k`] THEN
          DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES];
          ALL_TAC] THEN
        SUBGOAL_THEN `highdigits Z (L + 1) = 0` SUBST1_TAC THENL
         [ASM_REWRITE_TAC[HIGHDIGITS_EQ_0];
          ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES]];
        ALL_TAC] THEN
      SUBGOAL_THEN `l' = L + 2` SUBST_ALL_TAC THENL
       [MAP_EVERY UNDISCH_TAC [`L + 1 <= l'`; `l' <= L + 2`;
                               `~(l' = L + 1)`] THEN
        ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN
       `val(word(L + 2):int64) = L + 2 /\
        word_add (word(L + 1)) (word 1):int64 = word(L + 2)`
      STRIP_ASSUME_TAC THENL
       [REWRITE_TAC[GSYM WORD_ADD; ARITH_RULE `(L + 1) + 1 = L + 2`] THEN
        MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
        MAP_EVERY UNDISCH_TAC [`L + 2 <= k + 1`; `k < 2 EXP 58`] THEN ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `~(val(word_sub (word(L + 1)) (word(L + 2)):int64) = 0)`
      ASSUME_TAC THENL
       [ASM_REWRITE_TAC[VAL_WORD_SUB_EQ_0] THEN ARITH_TAC; ALL_TAC] THEN
      ASM_CASES_TAC `L + 1 = k` THENL
       [(*** Extension into the top word zt ***)

        FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
        REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
        SUBGOAL_THEN `zl < 2 EXP (64 * (L + 1))` ASSUME_TAC THENL
         [UNDISCH_TAC `read (memory :> bytes (z,8 * (L + 1))) s0 = zl` THEN
          DISCH_THEN(SUBST1_TAC o SYM) THEN
          REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES; BIGNUM_FROM_MEMORY_BOUND];
          ALL_TAC] THEN
        ARM_STEPS_TAC BIGNUM_MOD_EXEC (1--17) THEN
        ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
        CONJ_TAC THENL
         [REWRITE_TAC[GSYM WORD_ADD] THEN AP_TERM_TAC THEN ARITH_TAC;
          ALL_TAC] THEN
        CONJ_TAC THENL [AP_TERM_TAC THEN ARITH_TAC; ALL_TAC] THEN
        DISCH_TAC THEN BIGNUM_MOD_UNGUARD_TAC THEN
        UNDISCH_THEN
         `zl + 2 EXP (64 * (L + 1)) * val(sw:int64) DIV 8 =
          Z'` (SUBST1_TAC o SYM) THEN
        GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [ADD_SYM];

        (*** Extension into memory ***)

        SUBGOAL_THEN
         `L + 1 < k /\ ~(val(word_sub (word(L + 1)) (word k):int64) = 0)`
        STRIP_ASSUME_TAC THENL
         [ASM_REWRITE_TAC[VAL_WORD_SUB_EQ_0] THEN
          MAP_EVERY UNDISCH_TAC [`L < k`; `~(L + 1 = k)`] THEN ARITH_TAC;
          ALL_TAC] THEN
        GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ONCE_DEPTH_CONV)
         [BIGNUM_FROM_MEMORY_OFFSET_EQ_HIGHDIGITS] THEN
        ASM_REWRITE_TAC[ARITH_RULE `k - (L + 1) = 0 <=> ~(L + 1 < k)`] THEN
        REWRITE_TAC[ARITH_RULE `k - (L + 1) - 1 = k - (L + 2)`;
                    ARITH_RULE `(L + 1) + 1 = L + 2`] THEN
        REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
        SUBGOAL_THEN `zl < 2 EXP (64 * (L + 1))` ASSUME_TAC THENL
         [UNDISCH_TAC `read (memory :> bytes (z,8 * (L + 1))) s0 = zl` THEN
          DISCH_THEN(SUBST1_TAC o SYM) THEN
          REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES; BIGNUM_FROM_MEMORY_BOUND];
          ALL_TAC] THEN
        ARM_STEPS_TAC BIGNUM_MOD_EXEC (1--16) THEN
        ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
        CONJ_TAC THENL
         [REWRITE_TAC[GSYM WORD_ADD] THEN AP_TERM_TAC THEN ARITH_TAC;
          ALL_TAC] THEN
        DISCH_TAC THEN BIGNUM_MOD_UNGUARD_TAC THEN
        UNDISCH_THEN `zm:num = Z` SUBST_ALL_TAC THEN
        SUBGOAL_THEN
         `read (memory :> bytes (z,8 * k)) s16 =
          2 EXP (64 * (L + 2)) * highdigits Z (L + 2) +
          zl + 2 EXP (64 * (L + 1)) * val(word_ushr sw 3:int64)`
        SUBST1_TAC THENL
         [REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
          MP_TAC(SPECL [`z:int64`; `L + 2`; `k - (L + 2)`; `s16:armstate`]
            BIGNUM_FROM_MEMORY_SPLIT) THEN
          ASM_SIMP_TAC[ARITH_RULE
           `L + 1 < k ==> (L + 2) + (k - (L + 2)) = k`] THEN
          DISCH_THEN SUBST1_TAC THEN
          MP_TAC(SPECL [`L + 1`; `z:int64`; `s16:armstate`]
            BIGNUM_FROM_MEMORY_STEP) THEN
          REWRITE_TAC[ARITH_RULE `(L + 1) + 1 = L + 2`] THEN
          DISCH_THEN SUBST1_TAC THEN
          ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ARITH_TAC;
          ALL_TAC] THEN
        SUBGOAL_THEN `highdigits Z (L + 2) = 0` SUBST1_TAC THENL
         [REWRITE_TAC[HIGHDIGITS_EQ_0] THEN
          TRANS_TAC LTE_TRANS `2 EXP (64 * (L + 1))` THEN
          ASM_REWRITE_TAC[LE_EXP] THEN
          ARITH_TAC;
          ALL_TAC] THEN
        UNDISCH_THEN
         `zl + 2 EXP (64 * (L + 1)) * val(sw:int64) DIV 8 =
          Z'` (SUBST1_TAC o SYM) THEN
        ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES]] THEN

      (*** Common logging reasoning for both extension cases ***)

      MP_TAC(SPECL [`zl:num`; `L + 1`; `p DIV 64 + 1`; `word_ushr sw 3:int64`;
                    `lf1:int64`; `word(bigdigit zl (p DIV 64 + 1)):int64`]
            BIGNUM_MOD_LOGSTEP) THEN
      ASM_REWRITE_TAC[ADD_EQ_0; ARITH_EQ; ADD_SUB; VAL_WORD_SUB_EQ_0;
                      ARITH_RULE `(L + 1) + 1 = L + 2`] THEN
      REWRITE_TAC[VAL_WORD_USHR] THEN CONV_TAC NUM_REDUCE_CONV THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
      REWRITE_TAC[ARITH_RULE `(L + 2) - 1 = L + 1`] THEN
      REWRITE_TAC[bigdigit] THEN SIMP_TAC[DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ] THEN
      ASM_SIMP_TAC[DIV_LT; ADD_CLAUSES] THEN
      REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_USHR; VAL_WORD; DIMINDEX_64] THEN
      CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC MOD_DOWN_CONV THEN
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_LT THEN
      MP_TAC(ISPEC `sw:int64` VAL_BOUND_64) THEN ARITH_TAC];

    (*** The main loop back edge ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `val(word(61 * (N - i)):int64) = 61 * (N - i) /\ ~(61 * (N - i) = 0)`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64]; ALL_TAC] THEN
      MAP_EVERY UNDISCH_TAC [`i < N`; `61 * N < 64 * n`;
                             `n < 2 EXP 58 - 1`] THEN
      ARITH_TAC;
      ARM_SIM_TAC BIGNUM_MOD_EXEC [1]];

    ALL_TAC] THEN

  (*** After the loop: ghost the accumulator and name the quotient estimate ***)

  REWRITE_TAC[SUB_REFL; MULT_CLAUSES; EXP; DIV_1] THEN
  GHOST_INTRO_TAC `h:int64` `read X15` THEN
  GHOST_INTRO_TAC `zt:int64` `read X23` THEN
  GHOST_INTRO_TAC `zm:num` `bignum_from_memory (z,k)` THEN
  GLOBALIZE_PRECONDITION_TAC THEN BIGNUM_TERMRANGE_TAC `k:num` `zm:num` THEN
  ABBREV_TAC `Z = 2 EXP (64 * k) * val(zt:int64) + zm` THEN
  ABBREV_TAC
   `qw =
    word_add (word((val(w:int64) * val(h:int64)) DIV 2 EXP 64)) h:int64` THEN
  SUBGOAL_THEN
   `word_add (word p) (word 3):int64 = word(p + 3) /\
    word_ushr (word(p + 3)) 6:int64 = word((p + 3) DIV 64) /\
    val(word((p + 3) DIV 64):int64) = (p + 3) DIV 64 /\
    val(word(p + 3):int64) = p + 3 /\ (p + 3) DIV 64 <= k`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `p + 3 < 2 EXP 64` ASSUME_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`p <= 64 * k`; `k < 2 EXP 58`] THEN ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[GSYM WORD_ADD] THEN
    REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_USHR; VAL_WORD; DIMINDEX_64] THEN
    ASM_SIMP_TAC[MOD_LT; ARITH_RULE `x < 2 EXP 64 ==> x DIV 64 < 2 EXP 64`] THEN
    CONV_TAC NUM_REDUCE_CONV THEN UNDISCH_TAC `p <= 64 * k` THEN ARITH_TAC;
    ALL_TAC] THEN

  (*** The negadd loop computing Z - q * b, logging the top of the result ***)

  ENSURES_SEQUENCE_TAC `pc + 0x374`
   `\s. read X0 s = word k /\ read X1 s = z /\ read X4 s = m /\
        read X12 s = word((p + 3) DIV 64) /\ read X20 s = word(p + 3) /\
        read X21 s = w /\ read X15 s = qw /\ read X23 s = zt /\
        read X8 s = word k /\ bignum_from_memory (m,k) s = b /\
        zm < 2 EXP (64 * k) /\
        &(bignum_from_memory(z,k) s) + &2 pow (64 * k) * &(val(read X5 s)) =
        &zm + &(val qw) * (&2 pow (64 * k) - &b) /\
        read X14 s =
        word(bigdigit (bignum_from_memory(z,k) s) ((p + 3) DIV 64)) /\
        read X13 s = word(if (p + 3) DIV 64 = 0 then 0
                          else bigdigit (bignum_from_memory(z,k) s)
                                        ((p + 3) DIV 64 - 1))` THEN
  CONJ_TAC THENL
   [ENSURES_WHILE_UP_TAC `k:num` `pc + 0x334` `pc + 0x36c`
     `\j s. read X0 s = word k /\ read X1 s = z /\ read X4 s = m /\
            read X12 s = word((p + 3) DIV 64) /\ read X20 s = word(p + 3) /\
            read X21 s = w /\ read X15 s = qw /\ read X23 s = zt /\
            read X8 s = word j /\ bignum_from_memory (m,k) s = b /\
            bignum_from_memory (word_add z (word(8 * j)),k - j) s =
            highdigits zm j /\
            &(bignum_from_memory(z,j) s) + &2 pow (64 * j) * &(val(read X5 s)) =
            &(lowdigits zm j) +
            &(val qw) * (&2 pow (64 * j) - &(lowdigits b j)) /\
            read X14 s =
            word(bigdigit (bignum_from_memory(z,j) s) ((p + 3) DIV 64)) /\
            ((p + 3) DIV 64 <= j
             ==> read X13 s = word(if (p + 3) DIV 64 = 0 then 0
                                   else bigdigit (bignum_from_memory(z,j) s)
                                                 ((p + 3) DIV 64 - 1)))` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0; SUB_0; HIGHDIGITS_0;
                  BIGNUM_FROM_MEMORY_TRIVIAL; LOWDIGITS_0; BIGDIGIT_0; LE] THEN
      ARM_SIM_TAC BIGNUM_MOD_EXEC (1--10) THEN
      REWRITE_TAC[COND_ID] THEN REAL_ARITH_TAC;
      X_GEN_TAC `j:num` THEN STRIP_TAC THEN
      GHOST_INTRO_TAC `hin:int64` `read X5` THEN
      GHOST_INTRO_TAC `lf:int64` `read X13` THEN
      GHOST_INTRO_TAC `hf:int64` `read X14` THEN
      GHOST_INTRO_TAC `zj:num` `bignum_from_memory (z,j)` THEN
      GLOBALIZE_PRECONDITION_TAC THEN
      SUBGOAL_THEN `val(word j:int64) = j` ASSUME_TAC THENL
       [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
        MAP_EVERY UNDISCH_TAC [`j < k`; `k < 2 EXP 58`] THEN ARITH_TAC;
        ALL_TAC] THEN
      GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ONCE_DEPTH_CONV)
       [BIGNUM_FROM_MEMORY_OFFSET_EQ_HIGHDIGITS] THEN
      ASM_REWRITE_TAC[ARITH_RULE `k - j = 0 <=> ~(j < k)`] THEN
      REWRITE_TAC[ARITH_RULE `k - j - 1 = k - (j + 1)`] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP; BIGNUM_FROM_MEMORY_BYTES] THEN
      ENSURES_INIT_TAC "s0" THEN
      SUBGOAL_THEN
       `read(memory :> bytes64(word_add m (word(8 * j)))) s0 =
        word(bigdigit b j)`
      ASSUME_TAC THENL
       [UNDISCH_TAC `read (memory :> bytes (m,8 * k)) s0 = b` THEN
        DISCH_THEN(SUBST1_TAC o SYM) THEN
        REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES;
                    BIGDIGIT_BIGNUM_FROM_MEMORY] THEN
        ASM_REWRITE_TAC[WORD_VAL];
        ALL_TAC] THEN
      SUBGOAL_THEN `zj < 2 EXP (64 * j)` ASSUME_TAC THENL
       [UNDISCH_TAC `read (memory :> bytes (z,8 * j)) s0 = zj` THEN
        DISCH_THEN(SUBST1_TAC o SYM) THEN
        REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES; BIGNUM_FROM_MEMORY_BOUND];
        ALL_TAC] THEN
      ARM_ACCSTEPS_TAC BIGNUM_MOD_EXEC [3;4;6;8;9] (1--14) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [REWRITE_TAC[WORD_ADD]; ALL_TAC] THEN
      CONJ_TAC THENL
       [ALL_TAC;
        REWRITE_TAC[VAL_WORD_SUB_EQ_0] THEN ASM_REWRITE_TAC[] THEN
        MP_TAC(SPECL [`zj:num`; `j:num`; `(p + 3) DIV 64`; `sum_s8:int64`;
                      `lf:int64`; `word(bigdigit zj ((p + 3) DIV 64)):int64`]
              BIGNUM_MOD_LOGSTEP) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; MESON_TAC[]]] THEN
      SUBGOAL_THEN `~carry_s9` ASSUME_TAC THENL
       [DISCH_TAC THEN
        SUBGOAL_THEN
         `&(val(qw:int64)) * &(val(word_not(word(bigdigit b j)):int64)) <=
          (&2 pow 64 - &1) * (&2 pow 64 - &1):real`
        MP_TAC THENL
         [MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_POS] THEN
          REWRITE_TAC[REAL_ARITH
                       `x <= &2 pow 64 - &1 <=> x + &1 <= &2 pow 64`] THEN
          REWRITE_TAC[REAL_OF_NUM_CLAUSES;
                      ARITH_RULE `x + 1 <= y <=> x < y`] THEN
          REWRITE_TAC[VAL_BOUND_64];
          ALL_TAC] THEN
        MP_TAC(SPECL [`zm:num`; `j:num`] BIGDIGIT_BOUND) THEN
        MP_TAC(ISPEC `hin:int64` VAL_BOUND_64) THEN
        REWRITE_TAC[ARITH_RULE `x < 2 EXP 64 <=> x + 1 <= 2 EXP 64`] THEN
        MP_TAC(SPEC `val(sum_s8:int64)` REAL_POS) THEN
        MP_TAC(SPEC `val(sum_s9:int64)` REAL_POS) THEN
        ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
        ASM_CASES_TAC `carry_s6:bool` THEN
        ASM_REWRITE_TAC[BITVAL_CLAUSES; VAL_WORD_BIGDIGIT; VAL_WORD_0;
                        VAL_WORD_1;
                        REAL_VAL_WORD_NOT; DIMINDEX_64] THEN
        REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o check (free_in `&zj:real` o concl)) THEN
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
      ASM_CASES_TAC `carry_s6:bool` THEN
      ASM_REWRITE_TAC[BITVAL_CLAUSES; VAL_WORD_BIGDIGIT; VAL_WORD_0; VAL_WORD_1;
                      REAL_VAL_WORD_NOT; DIMINDEX_64; LOWDIGITS_CLAUSES] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES;
                  ARITH_RULE `64 * (j + 1) = 64 * j + 64`;
                  REAL_POW_ADD] THEN
      CONV_TAC REAL_RING;

      X_GEN_TAC `j:num` THEN STRIP_TAC THEN
      SUBGOAL_THEN `val(word j:int64) = j` ASSUME_TAC THENL
       [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
        MAP_EVERY UNDISCH_TAC [`j < k`; `k < 2 EXP 58`] THEN ARITH_TAC;
        ARM_SIM_TAC BIGNUM_MOD_EXEC (1--2) THEN
        ASM_REWRITE_TAC[VAL_WORD_SUB_EQ_0]];
      ARM_SIM_TAC BIGNUM_MOD_EXEC (1--2) THEN
      ASM_SIMP_TAC[LOWDIGITS_SELF; LE_REFL]];
    ALL_TAC] THEN

  (*** The top word of Z - q * b, and the final quotient estimate ***)

  GHOST_INTRO_TAC `hh:int64` `read X5` THEN
  GHOST_INTRO_TAC `lf:int64` `read X13` THEN
  GHOST_INTRO_TAC `hf:int64` `read X14` THEN
  GHOST_INTRO_TAC `zl:num` `bignum_from_memory (z,k)` THEN
  GLOBALIZE_PRECONDITION_TAC THEN
  ABBREV_TAC `Z1 = Z - val(qw:int64) * b` THEN
  ENSURES_SEQUENCE_TAC `pc + 0x3c0`
   `\s. read X0 s = word k /\ read X1 s = z /\ read X4 s = m /\
        bignum_from_memory (m,k) s = b /\ bignum_from_memory (z,k) s = zl /\
        read X5 s = read X15 s /\
        (~(b = 0)
         ==> 2 EXP (64 * k) * val(read X23 s) + zl = Z1 /\ (Z1 == a) (mod b) /\
             val(read X15 s) * b <= Z1 + b /\
             Z1 < (val(read X15 s) + 1) * b)` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
    SUBGOAL_THEN `zl < 2 EXP (64 * k)` ASSUME_TAC THENL
     [UNDISCH_TAC `read (memory :> bytes (z,8 * k)) s0 = zl` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES; BIGNUM_FROM_MEMORY_BOUND];
      ALL_TAC] THEN
    ARM_STEPS_TAC BIGNUM_MOD_EXEC (1--19) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN

    (*** The selection of the top 64 bits of Z1 via the logged words ***)

    ABBREV_TAC `zt' = word_add zt (word_sub hh qw):int64` THEN
    ABBREV_TAC `e1 = (p + 3) DIV 64` THEN
    SUBGOAL_THEN
     `(if val (word_sub (word k) (word e1):int64) = 0 then zt'
       else word (bigdigit zl e1)):int64 =
      word(bigdigit (zl + 2 EXP (64 * k) * val zt') e1) /\
      word(if e1 = 0 then 0 else bigdigit zl (e1 - 1)):int64 =
      word(if e1 = 0 then 0
           else bigdigit (zl + 2 EXP (64 * k) * val zt') (e1 - 1))`
    (CONJUNCTS_THEN SUBST1_TAC) THENL
     [CONJ_TAC THENL
       [MP_TAC(SPECL [`zl:num`; `k:num`; `e1:num`; `zt':int64`; `lf:int64`;
                      `word(bigdigit zl e1):int64`] BIGNUM_MOD_LOGSTEP) THEN
        ASM_REWRITE_TAC[VAL_WORD_SUB_EQ_0] THEN MESON_TAC[];
        COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN
        CONV_TAC SYM_CONV THEN MATCH_MP_TAC BIGDIGIT_ADD_LEFT THEN
        MAP_EVERY UNDISCH_TAC [`e1 <= k`; `~(e1 = 0)`] THEN ARITH_TAC];
      ALL_TAC] THEN
    MP_TAC(SPECL [`zl + 2 EXP (64 * k) * val(zt':int64)`; `e1:num`; `p + 3`;
                  `if e1 = 0 then 0
                   else bigdigit
                         (zl + 2 EXP (64 * k) * val(zt':int64)) (e1 - 1)`;
                  `bigdigit (zl + 2 EXP (64 * k) * val(zt':int64)) e1`]
           BIGNUM_MOD_FIELD) THEN
    REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    SUBGOAL_THEN `64 * e1 + (p + 3) MOD 64 = 3 + p` SUBST1_TAC THENL
     [EXPAND_TAC "e1" THEN MP_TAC(SPECL [`p + 3`; `64`] DIVISION) THEN
      ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[ARITH_RULE `2 EXP 64 * x = 2 EXP 3 * 2 EXP 61 * x`;
                EXP_ADD] THEN
    SIMP_TAC[DIV_MULT2; EXP_EQ_0; ARITH_EQ] THEN
    ABBREV_TAC `Z1' = zl + 2 EXP (64 * k) * val(zt':int64)` THEN

    (*** The mathematics, assuming the modulus is nonzero ***)

    DISCH_TAC THEN BIGNUM_MOD_UNGUARD_TAC THEN
    MP_TAC(SPECL [`b:num`; `p:num`; `u:num`; `d:num`; `w:int64`; `Z:num`;
                  `h:int64`; `qw:int64`] BIGNUM_MOD_ESTIMATE) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `Z1':num = Z1` SUBST_ALL_TAC THENL
     [EXPAND_TAC "Z1'" THEN EXPAND_TAC "zt'" THEN
      REWRITE_TAC[VAL_WORD_ADD; VAL_WORD_SUB; DIMINDEX_64] THEN
      CONV_TAC MOD_DOWN_CONV THEN
      MATCH_MP_TAC(SPECL [`zl:num`; `2 EXP (64 * k)`; `val(zt:int64)`;
                          `val(hh:int64)`; `val(qw:int64)`; `zm:num`; `b:num`;
                          `Z1:num`] BIGNUM_MOD_TOP) THEN
      ASM_REWRITE_TAC[VAL_BOUND_64] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_POW] THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL
       [EXPAND_TAC "Z1" THEN UNDISCH_TAC `val(qw:int64) * b <= Z` THEN
        ARITH_TAC;
        TRANS_TAC LTE_TRANS `6 * b` THEN CONJ_TAC THENL
         [EXPAND_TAC "Z1" THEN
          MAP_EVERY UNDISCH_TAC
           [`val(qw:int64) * b <= Z`; `Z < val(qw:int64) * b + 6 * b`] THEN
          ARITH_TAC;
          UNDISCH_TAC `b < 2 EXP (64 * k)` THEN
          SPEC_TAC(`2 EXP (64 * k)`,`e:num`) THEN ARITH_TAC]];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `zl + 2 EXP (64 * k) * val(zt':int64) = Z1` THEN ARITH_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `(Z == a) (mod b)` THEN
      SUBGOAL_THEN `Z = Z1 + val(qw:int64) * b` SUBST1_TAC THENL
       [SUBST1_TAC(SYM(ASSUME `Z - val(qw:int64) * b = Z1`)) THEN
        UNDISCH_TAC `val(qw:int64) * b <= Z` THEN ARITH_TAC;
        CONV_TAC NUMBER_RULE];
      ALL_TAC] THEN
    SUBGOAL_THEN `Z1 < 6 * b` ASSUME_TAC THENL
     [SUBST1_TAC(SYM(ASSUME `Z - val(qw:int64) * b = Z1`)) THEN
      MAP_EVERY UNDISCH_TAC
       [`val(qw:int64) * b <= Z`; `Z < val(qw:int64) * b + 6 * b`] THEN
      ARITH_TAC;
      ALL_TAC] THEN
    ABBREV_TAC `h1:int64 = word((2 EXP 61 * Z1) DIV 2 EXP p)` THEN
    ABBREV_TAC
     `Q = word_add (word((val(w:int64) * val(h1:int64)) DIV 2 EXP 64)) h1` THEN
    MP_TAC(SPECL [`b:num`; `p:num`; `u:num`; `d:num`; `w:int64`;
                  `2 EXP 61 * Z1`; `h1:int64`;
                  `Q:int64`] BIGNUM_MOD_ESTIMATE) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [UNDISCH_TAC `Z1 < 6 * b` THEN ARITH_TAC; STRIP_TAC] THEN
    SUBGOAL_THEN
     `val(word_add (word_ushr Q 61) (word 1):int64) = val Q DIV 2 EXP 61 + 1`
    SUBST1_TAC THENL
     [REWRITE_TAC[VAL_WORD_ADD; VAL_WORD_USHR; VAL_WORD_1; DIMINDEX_64] THEN
      MATCH_MP_TAC MOD_LT THEN MP_TAC(ISPEC `Q:int64` VAL_BOUND_64) THEN
      ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(SPECL [`val(Q:int64)`; `2 EXP 61`] DIVISION) THEN
    REWRITE_TAC[EXP_EQ_0; ARITH_EQ] THEN
    SPEC_TAC(`val(Q:int64) DIV 2 EXP 61`,`qq:num`) THEN
    SPEC_TAC(`val(Q:int64) MOD 2 EXP 61`,`rr:num`) THEN
    REPEAT GEN_TAC THEN
    DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC) THEN
    SUBGOAL_THEN `rr * b <= (2 EXP 61 - 1) * b` MP_TAC THENL
     [REWRITE_TAC[LE_MULT_RCANCEL] THEN UNDISCH_TAC `rr < 2 EXP 61` THEN
      ARITH_TAC;
      MAP_EVERY UNDISCH_TAC
       [`(qq * 2 EXP 61 + rr) * b <= 2 EXP 61 * Z1`;
        `2 EXP 61 * Z1 < (qq * 2 EXP 61 + rr) * b + 6 * b`] THEN
      ARITH_TAC];
    ALL_TAC] THEN

  (*** The second negadd loop computing Z1 - q2 * b with the carry in CF ***)

  GHOST_INTRO_TAC `q2:int64` `read X15` THEN
  GHOST_INTRO_TAC `zt1:int64` `read X23` THEN
  GLOBALIZE_PRECONDITION_TAC THEN
  ENSURES_SEQUENCE_TAC `pc + 0x3f8`
   `\s. read X0 s = word k /\ read X1 s = z /\ read X4 s = m /\
        read X15 s = q2 /\ read X23 s = zt1 /\ bignum_from_memory (m,k) s = b /\
        &(bignum_from_memory(z,k) s) +
        &2 pow (64 * k) * (&(val(read X5 s)) + &(bitval(read CF s))) =
        &zl + &(val q2) * (&2 pow (64 * k) - &b)` THEN
  CONJ_TAC THENL
   [ENSURES_WHILE_UP_TAC `k:num` `pc + 0x3c8` `pc + 0x3f0`
     `\j s. read X0 s = word k /\ read X1 s = z /\ read X4 s = m /\
            read X15 s = q2 /\ read X23 s = zt1 /\ read X8 s = word j /\
            bignum_from_memory (m,k) s = b /\
            bignum_from_memory (word_add z (word(8 * j)),k - j) s =
            highdigits zl j /\
            &(bignum_from_memory(z,j) s) +
            &2 pow (64 * j) * (&(val(read X5 s)) + &(bitval(read CF s))) =
            &(lowdigits zl j) +
            &(val q2) * (&2 pow (64 * j) - &(lowdigits b j))` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0; SUB_0; HIGHDIGITS_0;
                  BIGNUM_FROM_MEMORY_TRIVIAL; LOWDIGITS_0] THEN
      ARM_SIM_TAC BIGNUM_MOD_EXEC (1--2) THEN
      REWRITE_TAC[BITVAL_CLAUSES] THEN REAL_ARITH_TAC;
      X_GEN_TAC `j:num` THEN STRIP_TAC THEN
      GHOST_INTRO_TAC `hin:int64` `read X5` THEN
      GHOST_INTRO_TAC `cin:bool` `read CF` THEN
      GHOST_INTRO_TAC `zj:num` `bignum_from_memory (z,j)` THEN
      GLOBALIZE_PRECONDITION_TAC THEN
      SUBGOAL_THEN `val(word j:int64) = j` ASSUME_TAC THENL
       [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
        MAP_EVERY UNDISCH_TAC [`j < k`; `k < 2 EXP 58`] THEN ARITH_TAC;
        ALL_TAC] THEN
      GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ONCE_DEPTH_CONV)
       [BIGNUM_FROM_MEMORY_OFFSET_EQ_HIGHDIGITS] THEN
      ASM_REWRITE_TAC[ARITH_RULE `k - j = 0 <=> ~(j < k)`] THEN
      REWRITE_TAC[ARITH_RULE `k - j - 1 = k - (j + 1)`] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP; BIGNUM_FROM_MEMORY_BYTES] THEN
      ENSURES_INIT_TAC "s0" THEN
      SUBGOAL_THEN
       `read(memory :> bytes64(word_add m (word(8 * j)))) s0 =
        word(bigdigit b j)`
      ASSUME_TAC THENL
       [UNDISCH_TAC `read (memory :> bytes (m,8 * k)) s0 = b` THEN
        DISCH_THEN(SUBST1_TAC o SYM) THEN
        REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES;
                    BIGDIGIT_BIGNUM_FROM_MEMORY] THEN
        ASM_REWRITE_TAC[WORD_VAL];
        ALL_TAC] THEN
      ARM_ACCSTEPS_TAC BIGNUM_MOD_EXEC [3;4;6;7;8] (1--10) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [REWRITE_TAC[WORD_ADD]; ALL_TAC] THEN
      SUBGOAL_THEN `~carry_s7` ASSUME_TAC THENL
       [DISCH_TAC THEN
        SUBGOAL_THEN
         `&(val(q2:int64)) * &(val(word_not(word(bigdigit b j)):int64)) <=
          (&2 pow 64 - &1) * (&2 pow 64 - &1):real`
        MP_TAC THENL
         [MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_POS] THEN
          REWRITE_TAC[REAL_ARITH
                       `x <= &2 pow 64 - &1 <=> x + &1 <= &2 pow 64`] THEN
          REWRITE_TAC[REAL_OF_NUM_CLAUSES;
                      ARITH_RULE `x + 1 <= y <=> x < y`] THEN
          REWRITE_TAC[VAL_BOUND_64];
          ALL_TAC] THEN
        MP_TAC(SPEC `val(sum_s7:int64)` REAL_POS) THEN
        MP_TAC(SPEC `val(mullo_s3:int64)` REAL_POS) THEN
        ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
        ASM_CASES_TAC `carry_s6:bool` THEN
        ASM_REWRITE_TAC[BITVAL_CLAUSES; REAL_VAL_WORD_NOT; DIMINDEX_64;
                        VAL_WORD_BIGDIGIT] THEN
        REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o check (free_in `&zj:real` o concl)) THEN
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
      ASM_REWRITE_TAC[BITVAL_CLAUSES; VAL_WORD_BIGDIGIT; REAL_VAL_WORD_NOT;
                      DIMINDEX_64;
                      LOWDIGITS_CLAUSES] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES;
                  ARITH_RULE `64 * (j + 1) = 64 * j + 64`;
                  REAL_POW_ADD] THEN
      CONV_TAC REAL_RING;

      X_GEN_TAC `j:num` THEN STRIP_TAC THEN
      SUBGOAL_THEN `val(word j:int64) = j` ASSUME_TAC THENL
       [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
        MAP_EVERY UNDISCH_TAC [`j < k`; `k < 2 EXP 58`] THEN ARITH_TAC;
        ALL_TAC] THEN
      GHOST_INTRO_TAC `cin:bool` `read CF` THEN
      ARM_SIM_TAC BIGNUM_MOD_EXEC (1--2) THEN
      ASM_REWRITE_TAC[VAL_WORD_SUB_EQ_0];
      GHOST_INTRO_TAC `cin:bool` `read CF` THEN
      ARM_SIM_TAC BIGNUM_MOD_EXEC (1--2) THEN
      ASM_REWRITE_TAC[SUB_REFL; HIGHDIGITS_0] THEN
      SUBGOAL_THEN `zl < 2 EXP (64 * k)` ASSUME_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o check (free_in `highdigits zl k` o concl)) THEN
        REWRITE_TAC[SUB_REFL; GSYM BIGNUM_FROM_MEMORY_BYTES;
                    BIGNUM_FROM_MEMORY_TRIVIAL] THEN
        MESON_TAC[HIGHDIGITS_EQ_0];
        ASM_SIMP_TAC[LOWDIGITS_SELF]]];
    ALL_TAC] THEN

  (*** The final comparison giving the mask, and the optional addition of m ***)

  GHOST_INTRO_TAC `hh2:int64` `read X5` THEN
  GHOST_INTRO_TAC `c2:bool` `read CF` THEN
  GHOST_INTRO_TAC `r2:num` `bignum_from_memory (z,k)` THEN
  GLOBALIZE_PRECONDITION_TAC THEN
  BIGNUM_TERMRANGE_TAC `k:num` `r2:num` THEN
  ABBREV_TAC
   `mc <=> val(word_add (word_add zt1 hh2) (word(bitval c2)):int64) <
           val(q2:int64)` THEN
  SUBGOAL_THEN
   `~(b = 0) ==> r2 + bitval mc * b = a MOD b + 2 EXP (64 * k) * bitval mc`
  ASSUME_TAC THENL
   [DISCH_TAC THEN BIGNUM_MOD_UNGUARD_TAC THEN
    MP_TAC(SPECL [`a:num`; `b:num`; `2 EXP (64 * k)`; `r2:num`;
                  `val(zt1:int64) + val(hh2:int64) + bitval c2`;
                  `val(q2:int64)`; `Z1:num`] BIGNUM_MOD_FINAL) THEN
    ASM_REWRITE_TAC[VAL_BOUND_64] THEN ANTS_TAC THENL
     [SUBST1_TAC(SYM(ASSUME `2 EXP (64 * k) * val(zt1:int64) + zl = Z1`)) THEN
      FIRST_X_ASSUM(MP_TAC o check (free_in `&r2:real` o concl)) THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    EXPAND_TAC "mc" THEN
    REWRITE_TAC[VAL_WORD_ADD; VAL_WORD_BITVAL; DIMINDEX_64] THEN
    CONV_TAC MOD_DOWN_CONV THEN REWRITE_TAC[ADD_ASSOC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC ACCEPT_TAC);
    ALL_TAC] THEN
  ENSURES_WHILE_UP_TAC `k:num` `pc + 0x410` `pc + 0x428`
   `\j s. read X0 s = word k /\ read X1 s = z /\ read X4 s = m /\
          read X8 s = word j /\ read X9 s = word_neg(word(bitval mc)) /\
          bignum_from_memory (m,k) s = b /\
          bignum_from_memory (word_add z (word(8 * j)),k - j) s =
          highdigits r2 j /\
          &(bignum_from_memory(z,j) s) +
          &2 pow (64 * j) * &(bitval(read CF s)) =
          &(lowdigits r2 j) + &(bitval mc) * &(lowdigits b j)` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0; SUB_0; HIGHDIGITS_0;
                BIGNUM_FROM_MEMORY_TRIVIAL; LOWDIGITS_0] THEN
    ARM_SIM_TAC BIGNUM_MOD_EXEC (1--6) THEN
    REWRITE_TAC[BITVAL_CLAUSES; REAL_MUL_RZERO; REAL_ADD_LID] THEN
    EXPAND_TAC "mc" THEN REWRITE_TAC[GSYM NOT_LE] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
    CONV_TAC WORD_REDUCE_CONV;

    X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    GHOST_INTRO_TAC `cin:bool` `read CF` THEN
    GHOST_INTRO_TAC `zj:num` `bignum_from_memory (z,j)` THEN
    GLOBALIZE_PRECONDITION_TAC THEN
    SUBGOAL_THEN `val(word j:int64) = j` ASSUME_TAC THENL
     [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
      MAP_EVERY UNDISCH_TAC [`j < k`; `k < 2 EXP 58`] THEN ARITH_TAC;
      ALL_TAC] THEN
    GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ONCE_DEPTH_CONV)
     [BIGNUM_FROM_MEMORY_OFFSET_EQ_HIGHDIGITS] THEN
    ASM_REWRITE_TAC[ARITH_RULE `k - j = 0 <=> ~(j < k)`] THEN
    REWRITE_TAC[ARITH_RULE `k - j - 1 = k - (j + 1)`] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP; BIGNUM_FROM_MEMORY_BYTES] THEN
    ENSURES_INIT_TAC "s0" THEN
    SUBGOAL_THEN
     `read(memory :> bytes64(word_add m (word(8 * j)))) s0 = word(bigdigit b j)`
    ASSUME_TAC THENL
     [UNDISCH_TAC `read (memory :> bytes (m,8 * k)) s0 = b` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES;
                  BIGDIGIT_BIGNUM_FROM_MEMORY] THEN
      ASM_REWRITE_TAC[WORD_VAL];
      ALL_TAC] THEN
    ARM_ACCSTEPS_TAC BIGNUM_MOD_EXEC [4] (1--6) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [REWRITE_TAC[WORD_ADD]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o check (free_in `&zj:real` o concl)) THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
    REWRITE_TAC[WORD_AND_MASK] THEN BOOL_CASES_TAC `mc:bool` THEN
    REWRITE_TAC[BITVAL_CLAUSES; VAL_WORD_BIGDIGIT; VAL_WORD_0;
                LOWDIGITS_CLAUSES] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES;
                ARITH_RULE `64 * (j + 1) = 64 * j + 64`;
                REAL_POW_ADD] THEN
    CONV_TAC REAL_RING;

    X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `val(word j:int64) = j` ASSUME_TAC THENL
     [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
      MAP_EVERY UNDISCH_TAC [`j < k`; `k < 2 EXP 58`] THEN ARITH_TAC;
      ALL_TAC] THEN
    GHOST_INTRO_TAC `cin:bool` `read CF` THEN
    ARM_SIM_TAC BIGNUM_MOD_EXEC (1--2) THEN
    ASM_REWRITE_TAC[VAL_WORD_SUB_EQ_0];

    GHOST_INTRO_TAC `cin:bool` `read CF` THEN
    ARM_SIM_TAC BIGNUM_MOD_EXEC (1--2) THEN
    DISCH_TAC THEN BIGNUM_MOD_UNGUARD_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (free_in `lowdigits b k` o concl)) THEN
    ASM_SIMP_TAC[LOWDIGITS_SELF; REAL_OF_NUM_CLAUSES] THEN DISCH_TAC THEN
    MATCH_MP_TAC CONG_IMP_EQ THEN EXISTS_TAC `2 EXP (64 * k)` THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES; BIGNUM_FROM_MEMORY_BOUND];
      TRANS_TAC LT_TRANS `b:num` THEN ASM_REWRITE_TAC[MOD_LT_EQ];
      POP_ASSUM MP_TAC THEN CONV_TAC NUMBER_RULE]]);;

let BIGNUM_MOD_SUBROUTINE_CORRECT = prove
 (`!k z n x m a b pc stackpointer returnaddress.
        aligned 16 stackpointer /\
        nonoverlapping (z,8 * val k) (word_sub stackpointer (word 48),48) /\
        ALLPAIRS nonoverlapping
          [(z,8 * val k); (word_sub stackpointer (word 48),48)]
          [(word pc,0x440); (x,8 * val n); (m,8 * val k)] /\
        ~(val k = 0) /\ val k < 2 EXP 58 /\ val n < 2 EXP 58 - 1
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_mod_mc /\
                  read PC s = word pc /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [k;z;n;x;m] s /\
                  bignum_from_memory (x,val n) s = a /\
                  bignum_from_memory (m,val k) s = b)
             (\s. read PC s = returnaddress /\
                  (~(b = 0) ==> bignum_from_memory (z,val k) s = a MOD b))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bignum(z,val k);
                         memory :> bytes(word_sub stackpointer (word 48),48)])`,
  ARM_ADD_RETURN_STACK_TAC BIGNUM_MOD_EXEC BIGNUM_MOD_CORRECT
    `[X19;X20;X21;X22;X23;X24]` 48);;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let full_spec,public_vars = mk_safety_spec
    ~keep_maychanges:true
    (assoc "bignum_mod" subroutine_signatures)
    BIGNUM_MOD_CORRECT
    BIGNUM_MOD_EXEC;;

(* The block load at the start of iteration i of the main loop reads the
   words ib DIV 64 and MIN (ib DIV 64 + 1) (n - 1) of x, where
   ib = 61 * (N - (i + 1)). *)

let BIGNUM_MOD_SAFE_BLOCK = prove
 (`!n N i. ~(n = 0) /\ i < N /\ 61 * N < 64 * n /\ n < 2 EXP 58
           ==> word_sub (word (61 * (N - i))) (word 61):int64 =
               word(61 * (N - (i + 1))) /\
               word_ushr (word(61 * (N - (i + 1)))) 6:int64 =
               word((61 * (N - (i + 1))) DIV 64) /\
               val(word((61 * (N - (i + 1))) DIV 64):int64) =
               (61 * (N - (i + 1))) DIV 64 /\
               (if val(word_add (word((61 * (N - (i + 1))) DIV 64))
                                (word 1):int64) < n
                then word_add (word((61 * (N - (i + 1))) DIV 64)) (word 1)
                else word((61 * (N - (i + 1))) DIV 64)):int64 =
               word(MIN ((61 * (N - (i + 1))) DIV 64 + 1) (n - 1)) /\
               val(word(MIN ((61 * (N - (i + 1))) DIV 64 + 1) (n - 1)):int64) =
               MIN ((61 * (N - (i + 1))) DIV 64 + 1) (n - 1) /\
               (61 * (N - (i + 1))) DIV 64 < n /\
               MIN ((61 * (N - (i + 1))) DIV 64 + 1) (n - 1) < n`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `ib = 61 * (N - (i + 1))` THEN
  SUBGOAL_THEN
   `61 * (N - i) = ib + 61 /\ ib + 61 < 64 * n` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "ib" THEN
    MAP_EVERY UNDISCH_TAC [`i < N`; `61 * N < 64 * n`] THEN ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `j = ib DIV 64` THEN
  SUBGOAL_THEN
   `ib < 2 EXP 64 /\ j < n /\ j + 1 < 2 EXP 64` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "j" THEN
    MAP_EVERY UNDISCH_TAC [`ib + 61 < 64 * n`; `n < 2 EXP 58`] THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE;
    REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_USHR; VAL_WORD; DIMINDEX_64] THEN
    ASM_SIMP_TAC[MOD_LT; ARITH_RULE `j + 1 < e ==> j < e`] THEN
    EXPAND_TAC "j" THEN CONV_TAC NUM_REDUCE_CONV;
    MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    UNDISCH_TAC `j + 1 < 2 EXP 64` THEN ARITH_TAC;
    REWRITE_TAC[GSYM WORD_ADD] THEN
    ASM_SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64] THEN
    COND_CASES_TAC THEN AP_TERM_TAC THEN
    MAP_EVERY UNDISCH_TAC [`j < n`] THEN POP_ASSUM MP_TAC THEN ARITH_TAC;
    MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    UNDISCH_TAC `j + 1 < 2 EXP 64` THEN ARITH_TAC;
    UNDISCH_TAC `j < n` THEN ARITH_TAC]);;

(* The new length MIN (k + 1) ((61 * (i + 2) + 63) DIV 64) of the
   accumulator, computed by the CSEL at 0x2b0, and the fact that when the
   accumulator grows by a word its old length is at most k. *)

let BIGNUM_MOD_SAFE_NEWLEN = prove
 (`!k i. k < 2 EXP 58 /\ 61 * (i + 2) + 63 < 2 EXP 64
         ==> (if val(word_add (word k) (word 1):int64) <
                 val(word_ushr
                      (word_add (word(61 * (i + 2))) (word 63)) 6:int64)
              then word_add (word k) (word 1)
              else word_ushr
                    (word_add (word(61 * (i + 2))) (word 63)) 6):int64 =
             word(MIN (k + 1) ((61 * (i + 2) + 63) DIV 64))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `word_ushr (word_add (word(61 * (i + 2))) (word 63)) 6:int64 =
    word((61 * (i + 2) + 63) DIV 64) /\
    val(word((61 * (i + 2) + 63) DIV 64):int64) = (61 * (i + 2) + 63) DIV 64 /\
    word_add (word k) (word 1):int64 = word(k + 1) /\
    val(word(k + 1):int64) = k + 1`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REWRITE_TAC[GSYM WORD_ADD; GSYM VAL_EQ; VAL_WORD_USHR; VAL_WORD;
                  DIMINDEX_64] THEN
      ASM_SIMP_TAC[MOD_LT;
                   ARITH_RULE `x < 2 EXP 64 ==> x DIV 64 < 2 EXP 64`] THEN
      CONV_TAC NUM_REDUCE_CONV;
      MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
      UNDISCH_TAC `61 * (i + 2) + 63 < 2 EXP 64` THEN ARITH_TAC;
      REWRITE_TAC[WORD_ADD];
      MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
      UNDISCH_TAC `k < 2 EXP 58` THEN ARITH_TAC];
    ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN AP_TERM_TAC THEN
    POP_ASSUM MP_TAC THEN ARITH_TAC]);;

let BIGNUM_MOD_SAFE_EXTLEN = prove
 (`!k i. ~(MIN (k + 1) ((61 * (i + 2) + 63) DIV 64) =
           MIN (k + 1) ((61 * (i + 1) + 63) DIV 64))
         ==> MIN (k + 1) ((61 * (i + 1) + 63) DIV 64) <= k`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `(61 * (i + 1) + 63) DIV 64 <= (61 * (i + 2) + 63) DIV 64`
  MP_TAC THENL [MATCH_MP_TAC DIV_MONO THEN ARITH_TAC; ARITH_TAC]);;

(* The facts about N = (64 * n + 60) DIV 61 - 1 from BIGNUM_MOD_START. *)

let BIGNUM_MOD_SAFE_START_TAC =
  MP_TAC(SPEC `n:num` BIGNUM_MOD_START) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `n < 2 EXP 58 - 1` THEN ARITH_TAC;
    STRIP_TAC];;

(* The body of an up-counting loop of n instructions with index j in X8,
   whose backward branch tests j + 1 <> b. *)

let BIGNUM_MOD_SAFE_UPBODY_TAC (b:term) n =
  SAFETY_UPCOUNT_FACTS_TAC `j:num` `j:num` b b THEN
  SUBGOAL_THEN (mk_eq(mk_comb(`val:int64->num`,mk_comb(`word:num->int64`,b)),b))
  ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    UNDISCH_TAC `k < 2 EXP 58` THEN ARITH_TAC; ALL_TAC] THEN
  ARM_SAFETY_SIM_TAC BIGNUM_MOD_EXEC (1--n) THEN
  SUBGOAL_THEN (subst [b,`b:num`]
    `(~(val (word_sub (word (j + 1)) (word b):int64) = 0) <=> j + 1 < b)`)
  (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[VAL_WORD_SUB_EQ_0] THEN ASM_REWRITE_TAC[] THEN SIMPLE_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [GEN_REWRITE_TAC RAND_CONV [COND_RAND] THEN REFL_TAC; ALL_TAC] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

(* Facts for the code from 0x28c computing the new length of the accumulator
   and whether it grows by a word. *)

let BIGNUM_MOD_SAFE_NEWLEN_TAC =
  BIGNUM_MOD_SAFE_START_TAC THEN
  SUBGOAL_THEN `61 * (i + 2) + 63 < 2 EXP 64` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`i < (64 * n + 60) DIV 61 - 1`;
      `61 * ((64 * n + 60) DIV 61 - 1) < 64 * n`; `n < 2 EXP 58 - 1`] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`k:num`; `i:num`] BIGNUM_MOD_SAFE_NEWLEN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN
   `word_add (word (61 * (i + 1))) (word 61):int64 = word (61 * (i + 2))`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM WORD_ADD] THEN AP_TERM_TAC THEN ARITH_TAC; ALL_TAC];;

let BIGNUM_MOD_SAFE_GROW_TAC =
  BIGNUM_MOD_SAFE_NEWLEN_TAC THEN
  SUBGOAL_THEN
   `word_add (word (MIN (k + 1) ((61 * (i + 1) + 63) DIV 64) - 1))
             (word 1):int64 =
    word (MIN (k + 1) ((61 * (i + 1) + 63) DIV 64))`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM WORD_ADD] THEN AP_TERM_TAC THEN
    MATCH_MP_TAC(ARITH_RULE `1 <= x ==> x - 1 + 1 = x`) THEN
    REWRITE_TAC[ARITH_RULE `1 <= MIN a b <=> 1 <= a /\ 1 <= b`] THEN
    SIMP_TAC[LE_RDIV_EQ; ARITH_EQ] THEN ARITH_TAC;
    ALL_TAC];;

(* The skeleton follows the code: the loop zeroing z, the case n = 0, the
   loop finding the top word of m, the setup including the reciprocal, the
   main loop of N = (64 * n + 60) DIV 61 - 1 iterations and the three final
   loops over k words. In iteration i of the main loop the accumulator has
   L + 1 words, L + 1 = MIN (k + 1) ((61 * (i + 1) + 63) DIV 64); the inner
   loop over L words is skipped when L = 0, the last word is stored in z
   unless L = k, and the accumulator then grows by a word unless its new
   length MIN (k + 1) ((61 * (i + 2) + 63) DIV 64) is still L + 1, the new
   word being stored in z unless L + 1 = k. All these conditions only depend
   on k, n and i, so neither the branches nor the addresses depend on the
   data. *)

let BIGNUM_MOD_SAFE = prove
 (`exists f_events.
     forall e k z n x m pc.
        ALLPAIRS nonoverlapping
          [(z,8 * val k)] [(word pc,0x440); (x,8 * val n); (m,8 * val k)] /\
        ~(val k = 0) /\ val k < 2 EXP 58 /\ val n < 2 EXP 58 - 1
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_mod_mc /\
                  read PC s = word(pc + 0xc) /\
                  C_ARGUMENTS [k;z;n;x;m] s /\
                  read events s = e)
             (\s. read PC s = word(pc + 0x430) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events x m z k n pc /\
                     memaccess_inbounds e2
                       [x,val n * 8; m,val k * 8; z,val k * 8]
                       [z,val k * 8]))
             (MAYCHANGE [PC; X5; X6; X7; X8; X9; X10; X11; X12; X13; X14;
                         X15; X16; X17; X19; X20; X21; X22; X23] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
              MAYCHANGE [memory :> bignum(z,val k)])`,
  ASSERT_CONCL_TAC full_spec THEN
  ARM_SAFETY_SKELETON_TAC ~ths:[ALLPAIRS; ALL; NONOVERLAPPING_CLAUSES]
   ["k"; "n"]
   (Loop(`k:num`, `pc + 0x14`, `pc + 0x24`,
     `\i s. read X0 s = word k /\ read X1 s = z /\ read X2 s = word n /\
            read X3 s = x /\ read X4 s = m /\ read X8 s = word i`,
     Leg("start",
       REWRITE_TAC[ENUMERATEL_APPEND_ZERO] THEN
       ARM_SAFETY_SIM_TAC BIGNUM_MOD_EXEC (1--2) THEN
       DISCHARGE_SAFETY_PROPERTY_TAC),
     Leg("zero",
       SAFETY_UPCOUNT_FACTS_TAC `i:num` `i:num` `k:num` `k:num` THEN
       ARM_SAFETY_SIM_TAC BIGNUM_MOD_EXEC (1--4) THEN
       SUBGOAL_THEN
        `(i + 1 <= k /\ ~(val (word_sub (word k) (word (i + 1)):int64) = 0)) <=>
         i + 1 < k`
       (fun th -> REWRITE_TAC[th]) THENL
        [ASM_REWRITE_TAC[VAL_WORD_SUB_EQ_0] THEN ARITH_TAC; ALL_TAC] THEN
       CONJ_TAC THENL
        [GEN_REWRITE_TAC RAND_CONV [COND_RAND] THEN REFL_TAC; ALL_TAC] THEN
       DISCHARGE_SAFETY_PROPERTY_TAC),
     Cases(`n = 0`,
      Leg("n0",
        ARM_SAFETY_SIM_TAC BIGNUM_MOD_EXEC (1--2) THEN
        DISCHARGE_SAFETY_PROPERTY_TAC),
      Loop(`k:num`, `pc + 0x44`, `pc + 0x68`,
       `\i s. read X0 s = word k /\ read X1 s = z /\ read X2 s = word n /\
              read X3 s = x /\ read X4 s = m /\ read X8 s = word i`,
       Leg("fpre",
         REWRITE_TAC[ENUMERATEL_APPEND_ZERO] THEN
         SUBGOAL_THEN `~(val(word_sub (word n) (word 0):int64) = 0) /\
                       ~(val(word k:int64) = 0)` STRIP_ASSUME_TAC THENL
          [ASM_REWRITE_TAC[WORD_SUB_0]; ALL_TAC] THEN
         ARM_SAFETY_SIM_TAC BIGNUM_MOD_EXEC (1--8) THEN
         DISCHARGE_SAFETY_PROPERTY_TAC),
       Leg("find",
         SAFETY_UPCOUNT_FACTS_TAC `i:num` `i:num` `k:num` `k:num` THEN
         ARM_SAFETY_SIM_TAC BIGNUM_MOD_EXEC (1--9) THEN
         CONJ_TAC THENL
          [GEN_REWRITE_TAC RAND_CONV [COND_RAND] THEN REFL_TAC; ALL_TAC] THEN
         DISCHARGE_SAFETY_PROPERTY_TAC),
       Loop(`(64 * n + 60) DIV 61 - 1`, `pc + 0x1a4`, `pc + 0x310`,
        `\i s. read X0 s = word k /\ read X1 s = z /\ read X2 s = word n /\
               read X3 s = x /\ read X4 s = m /\
               read X16 s = word(61 * (((64 * n + 60) DIV 61 - 1) - i)) /\
               read X17 s = word(61 * (i + 1)) /\
               read X19 s = word(MIN (k + 1) ((61 * (i + 1) + 63) DIV 64))`,
        Leg("setup",
          REWRITE_TAC[ENUMERATEL_APPEND_ZERO; SUB_0; ADD_CLAUSES;
                      MULT_CLAUSES] THEN
          BIGNUM_MOD_SAFE_START_TAC THEN
          SUBGOAL_THEN `word_sub (word n) (word 1):int64 = word(n - 1) /\
                        val(word(n - 1):int64) = n - 1` STRIP_ASSUME_TAC THENL
           [CONJ_TAC THENL
             [ASM_SIMP_TAC[WORD_SUB; ARITH_RULE `~(n = 0) ==> 1 <= n`];
              MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
              UNDISCH_TAC `n < 2 EXP 58 - 1` THEN ARITH_TAC];
            ALL_TAC] THEN
          ARM_SAFETY_SIM_TAC BIGNUM_MOD_EXEC (1--79) THEN
          CONJ_TAC THENL
           [REWRITE_TAC[GSYM WORD_ADD] THEN CONV_TAC NUM_REDUCE_CONV THEN
            SUBGOAL_THEN `val(word(k + 1):int64) = k + 1` SUBST1_TAC THENL
             [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
              UNDISCH_TAC `k < 2 EXP 58` THEN ARITH_TAC;
              REWRITE_TAC[ARITH_RULE `~(k + 1 < 1)`;
                          ARITH_RULE `MIN (k + 1) 1 = 1`]];
            DISCHARGE_SAFETY_PROPERTY_TAC]),
        Seq(`pc + 0x1f4`,
         `\s. read X0 s = word k /\ read X1 s = z /\ read X2 s = word n /\
              read X3 s = x /\ read X4 s = m /\
              read X16 s = word(61 * (((64 * n + 60) DIV 61 - 1) - (i + 1))) /\
              read X17 s = word(61 * (i + 1)) /\
              read X19 s = word(MIN (k + 1) ((61 * (i + 1) + 63) DIV 64)) /\
              read X8 s = word 0`,
         Leg("block",
           BIGNUM_MOD_SAFE_START_TAC THEN
           MP_TAC(SPECL [`n:num`; `(64 * n + 60) DIV 61 - 1`; `i:num`]
             BIGNUM_MOD_SAFE_BLOCK) THEN
           ANTS_TAC THENL
            [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `n < 2 EXP 58 - 1` THEN
             ARITH_TAC;
             STRIP_TAC] THEN
           ARM_SAFETY_SIM_TAC BIGNUM_MOD_EXEC (1--20) THEN
           DISCHARGE_SAFETY_PROPERTY_TAC),
         Seq(`pc + 0x244`,
          `\s. read X0 s = word k /\ read X1 s = z /\ read X2 s = word n /\
               read X3 s = x /\ read X4 s = m /\
               read X16 s = word(61 * (((64 * n + 60) DIV 61 - 1) - (i + 1))) /\
               read X17 s = word(61 * (i + 1)) /\
               read X19 s = word(MIN (k + 1) ((61 * (i + 1) + 63) DIV 64)) /\
               read X8 s = word(MIN (k + 1) ((61 * (i + 1) + 63) DIV 64) - 1)`,
          Cases(`MIN (k + 1) ((61 * (i + 1) + 63) DIV 64) <= 1`,
           Leg("skip",
             SUBGOAL_THEN `MIN (k + 1) ((61 * (i + 1) + 63) DIV 64) = 1`
              (fun th -> REWRITE_TAC[th] THEN RULE_ASSUM_TAC(REWRITE_RULE[th]))
             THENL
              [MATCH_MP_TAC(ARITH_RULE `x <= 1 /\ 1 <= x ==> x = 1`) THEN
               ASM_REWRITE_TAC[] THEN
               REWRITE_TAC[ARITH_RULE `1 <= MIN a b <=> 1 <= a /\ 1 <= b`] THEN
               SIMP_TAC[LE_RDIV_EQ; ARITH_EQ] THEN ARITH_TAC;
               ALL_TAC] THEN
             ARM_SAFETY_SIM_TAC BIGNUM_MOD_EXEC (1--2) THEN
             DISCHARGE_SAFETY_PROPERTY_TAC),
           Loop(`MIN (k + 1) ((61 * (i + 1) + 63) DIV 64) - 1`,
                `pc + 0x1fc`, `pc + 0x244`,
            `\j s. read X0 s = word k /\ read X1 s = z /\ read X2 s = word n /\
                   read X3 s = x /\ read X4 s = m /\
                   read X16 s =
                   word(61 * (((64 * n + 60) DIV 61 - 1) - (i + 1))) /\
                   read X17 s = word(61 * (i + 1)) /\
                   read X19 s =
                   word(MIN (k + 1) ((61 * (i + 1) + 63) DIV 64)) /\
                   read X11 s =
                   word(MIN (k + 1) ((61 * (i + 1) + 63) DIV 64) - 1) /\
                   read X8 s = word j`,
            Leg("ipre",
              SUBGOAL_THEN
               `word_sub (word (MIN (k + 1) ((61 * (i + 1) + 63) DIV 64)))
                         (word 1):int64 =
                word (MIN (k + 1) ((61 * (i + 1) + 63) DIV 64) - 1) /\
                val(word (MIN (k + 1) ((61 * (i + 1) + 63) DIV 64) - 1):int64) =
                MIN (k + 1) ((61 * (i + 1) + 63) DIV 64) - 1 /\
                ~(MIN (k + 1) ((61 * (i + 1) + 63) DIV 64) - 1 = 0)`
              STRIP_ASSUME_TAC THENL
               [REPEAT CONJ_TAC THENL
                 [ASM_SIMP_TAC[WORD_SUB; ARITH_RULE `~(x <= 1) ==> 1 <= x`];
                  MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
                  UNDISCH_TAC `k < 2 EXP 58` THEN ARITH_TAC;
                  UNDISCH_TAC
                   `~(MIN (k + 1) ((61 * (i + 1) + 63) DIV 64) <= 1)` THEN
                  ARITH_TAC];
                ALL_TAC] THEN
              REWRITE_TAC[ENUMERATEL_APPEND_ZERO] THEN
              ARM_SAFETY_SIM_TAC BIGNUM_MOD_EXEC (1--2) THEN
              DISCHARGE_SAFETY_PROPERTY_TAC),
            Leg("inner",
              SUBGOAL_THEN `j < k` ASSUME_TAC THENL
               [UNDISCH_TAC
                 `j < MIN (k + 1) ((61 * (i + 1) + 63) DIV 64) - 1` THEN
                ARITH_TAC;
                ALL_TAC] THEN
              BIGNUM_MOD_SAFE_UPBODY_TAC
               `MIN (k + 1) ((61 * (i + 1) + 63) DIV 64) - 1` 18),
            Leg("ipost",
              ARM_SAFETY_SIM_TAC BIGNUM_MOD_EXEC [] THEN
              DISCHARGE_SAFETY_PROPERTY_TAC))),
          Seq(`pc + 0x28c`,
           `\s. read X0 s = word k /\ read X1 s = z /\ read X2 s = word n /\
                read X3 s = x /\ read X4 s = m /\
                read X16 s =
                word(61 * (((64 * n + 60) DIV 61 - 1) - (i + 1))) /\
                read X17 s = word(61 * (i + 1)) /\
                read X19 s = word(MIN (k + 1) ((61 * (i + 1) + 63) DIV 64)) /\
                read X8 s = word(MIN (k + 1) ((61 * (i + 1) + 63) DIV 64) - 1)`,
           Cases(`MIN (k + 1) ((61 * (i + 1) + 63) DIV 64) - 1 = k`,
            Leg("ltop",
              UNDISCH_THEN `MIN (k + 1) ((61 * (i + 1) + 63) DIV 64) - 1 = k`
               (fun th -> REWRITE_TAC[th] THEN ASSUME_TAC th) THEN
              ARM_SAFETY_SIM_TAC BIGNUM_MOD_EXEC (1--12) THEN
              DISCHARGE_SAFETY_PROPERTY_TAC),
            Leg("lmem",
              SUBGOAL_THEN
               `MIN (k + 1) ((61 * (i + 1) + 63) DIV 64) - 1 < k /\
                val(word(MIN (k + 1) ((61 * (i + 1) + 63) DIV 64) - 1):int64) =
                MIN (k + 1) ((61 * (i + 1) + 63) DIV 64) - 1`
              STRIP_ASSUME_TAC THENL
               [CONJ_TAC THENL
                 [UNDISCH_TAC
                   `~(MIN (k + 1) ((61 * (i + 1) + 63) DIV 64) - 1 = k)` THEN
                  ARITH_TAC;
                  MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
                  UNDISCH_TAC `k < 2 EXP 58` THEN ARITH_TAC];
                ALL_TAC] THEN
              SUBGOAL_THEN
               `~(val(word_sub
                       (word(MIN (k + 1) ((61 * (i + 1) + 63) DIV 64) - 1))
                       (word k):int64) = 0)`
              ASSUME_TAC THENL
               [ASM_REWRITE_TAC[VAL_WORD_SUB_EQ_0] THEN
                UNDISCH_TAC
                 `~(MIN (k + 1) ((61 * (i + 1) + 63) DIV 64) - 1 = k)` THEN
                ARITH_TAC;
                ALL_TAC] THEN
              ARM_SAFETY_SIM_TAC BIGNUM_MOD_EXEC (1--13) THEN
              DISCHARGE_SAFETY_PROPERTY_TAC)),
           Seq(`pc + 0x2e4`,
            `\s. read X0 s = word k /\ read X1 s = z /\ read X2 s = word n /\
                 read X3 s = x /\ read X4 s = m /\
                 read X16 s =
                 word(61 * (((64 * n + 60) DIV 61 - 1) - (i + 1))) /\
                 read X17 s = word(61 * (i + 2)) /\
                 read X19 s = word(MIN (k + 1) ((61 * (i + 2) + 63) DIV 64))`,
            Cases(`MIN (k + 1) ((61 * (i + 2) + 63) DIV 64) =
                   MIN (k + 1) ((61 * (i + 1) + 63) DIV 64)`,
             Leg("noext",
               BIGNUM_MOD_SAFE_GROW_TAC THEN
               ARM_SAFETY_SIM_TAC BIGNUM_MOD_EXEC (1--12) THEN
               DISCHARGE_SAFETY_PROPERTY_TAC),
             Cases(`MIN (k + 1) ((61 * (i + 1) + 63) DIV 64) = k`,
              Leg("extz",
                UNDISCH_THEN `MIN (k + 1) ((61 * (i + 1) + 63) DIV 64) = k`
                 (fun th -> REWRITE_TAC[th] THEN
                            RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN
                            ASSUME_TAC th) THEN
                BIGNUM_MOD_SAFE_NEWLEN_TAC THEN
                SUBGOAL_THEN
                 `word_add (word (k - 1)) (word 1):int64 = word k /\
                  val(word(MIN (k + 1) ((61 * (i + 2) + 63) DIV 64)):int64) =
                  MIN (k + 1) ((61 * (i + 2) + 63) DIV 64)`
                STRIP_ASSUME_TAC THENL
                 [CONJ_TAC THENL
                   [REWRITE_TAC[GSYM WORD_ADD] THEN AP_TERM_TAC THEN
                    UNDISCH_TAC `~(k = 0)` THEN ARITH_TAC;
                    MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
                    UNDISCH_TAC `k < 2 EXP 58` THEN ARITH_TAC];
                  ALL_TAC] THEN
                SUBGOAL_THEN
                 `~(val(word_sub (word k)
                     (word(MIN (k + 1) ((61 * (i + 2) + 63) DIV 64))):int64) =
                    0)`
                ASSUME_TAC THENL
                 [ASM_REWRITE_TAC[VAL_WORD_SUB_EQ_0]; ALL_TAC] THEN
                ARM_SAFETY_SIM_TAC BIGNUM_MOD_EXEC (1--21) THEN
                DISCHARGE_SAFETY_PROPERTY_TAC),
              Leg("extm",
                BIGNUM_MOD_SAFE_GROW_TAC THEN
                FIRST_ASSUM(ASSUME_TAC o MATCH_MP BIGNUM_MOD_SAFE_EXTLEN) THEN
                SUBGOAL_THEN
                 `MIN (k + 1) ((61 * (i + 1) + 63) DIV 64) < k /\
                  val(word(MIN (k + 1) ((61 * (i + 1) + 63) DIV 64)):int64) =
                  MIN (k + 1) ((61 * (i + 1) + 63) DIV 64) /\
                  val(word(MIN (k + 1) ((61 * (i + 2) + 63) DIV 64)):int64) =
                  MIN (k + 1) ((61 * (i + 2) + 63) DIV 64)`
                STRIP_ASSUME_TAC THENL
                 [CONJ_TAC THENL
                   [MAP_EVERY UNDISCH_TAC
                     [`MIN (k + 1) ((61 * (i + 1) + 63) DIV 64) <= k`;
                      `~(MIN (k + 1) ((61 * (i + 1) + 63) DIV 64) = k)`] THEN
                    ARITH_TAC;
                    CONJ_TAC THEN MATCH_MP_TAC VAL_WORD_EQ THEN
                    REWRITE_TAC[DIMINDEX_64] THEN
                    UNDISCH_TAC `k < 2 EXP 58` THEN ARITH_TAC];
                  ALL_TAC] THEN
                SUBGOAL_THEN
                 `~(val(word_sub
                       (word(MIN (k + 1) ((61 * (i + 1) + 63) DIV 64)))
                       (word(MIN (k + 1) ((61 * (i + 2) + 63) DIV 64))):int64) =
                    0) /\
                  ~(val(word_sub
                       (word(MIN (k + 1) ((61 * (i + 1) + 63) DIV 64)))
                       (word k):int64) = 0)`
                STRIP_ASSUME_TAC THENL
                 [ASM_REWRITE_TAC[VAL_WORD_SUB_EQ_0]; ALL_TAC] THEN
                ARM_SAFETY_SIM_TAC BIGNUM_MOD_EXEC (1--20) THEN
                DISCHARGE_SAFETY_PROPERTY_TAC))),
            Leg("back",
              REWRITE_TAC[ARITH_RULE `(i + 1) + 1 = i + 2`] THEN
              BIGNUM_MOD_SAFE_START_TAC THEN
              SUBGOAL_THEN
               `val(word(61 * ((64 * n + 60) DIV 61 - 1 - (i + 1))):int64) =
                61 * ((64 * n + 60) DIV 61 - 1 - (i + 1))` ASSUME_TAC THENL
               [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
                UNDISCH_TAC `61 * ((64 * n + 60) DIV 61 - 1) < 64 * n` THEN
                UNDISCH_TAC `n < 2 EXP 58 - 1` THEN ARITH_TAC;
                ALL_TAC] THEN
              ARM_SAFETY_SIM_TAC BIGNUM_MOD_EXEC (1--11) THEN
              SUBGOAL_THEN
               `(~(61 * ((64 * n + 60) DIV 61 - 1 - (i + 1)) = 0) <=>
                 i + 1 < (64 * n + 60) DIV 61 - 1)`
              (fun th -> REWRITE_TAC[th]) THENL
               [ARITH_TAC; ALL_TAC] THEN
              CONJ_TAC THENL
               [GEN_REWRITE_TAC RAND_CONV [COND_RAND] THEN REFL_TAC;
                ALL_TAC] THEN
              DISCHARGE_SAFETY_PROPERTY_TAC))))),
        Loop(`k:num`, `pc + 0x334`, `pc + 0x374`,
         `\j s. read X0 s = word k /\ read X1 s = z /\ read X4 s = m /\
                read X8 s = word j`,
         Leg("q1",
           REWRITE_TAC[ENUMERATEL_APPEND_ZERO] THEN
           SUBGOAL_THEN `~(val(word k:int64) = 0)` ASSUME_TAC THENL
            [ASM_REWRITE_TAC[]; ALL_TAC] THEN
           ARM_SAFETY_SIM_TAC BIGNUM_MOD_EXEC (1--9) THEN
           DISCHARGE_SAFETY_PROPERTY_TAC),
         Leg("neg1", BIGNUM_MOD_SAFE_UPBODY_TAC `k:num` 16),
         Loop(`k:num`, `pc + 0x3c8`, `pc + 0x3f8`,
          `\j s. read X0 s = word k /\ read X1 s = z /\ read X4 s = m /\
                 read X8 s = word j`,
          Leg("q2",
            REWRITE_TAC[ENUMERATEL_APPEND_ZERO] THEN
            SUBGOAL_THEN `~(val(word k:int64) = 0)` ASSUME_TAC THENL
             [ASM_REWRITE_TAC[]; ALL_TAC] THEN
            ARM_SAFETY_SIM_TAC BIGNUM_MOD_EXEC (1--21) THEN
            DISCHARGE_SAFETY_PROPERTY_TAC),
          Leg("neg2", BIGNUM_MOD_SAFE_UPBODY_TAC `k:num` 12),
          Loop(`k:num`, `pc + 0x410`, `pc + 0x430`,
           `\j s. read X0 s = word k /\ read X1 s = z /\ read X4 s = m /\
                  read X8 s = word j`,
           Leg("mask",
             REWRITE_TAC[ENUMERATEL_APPEND_ZERO] THEN
             SUBGOAL_THEN `~(val(word k:int64) = 0)` ASSUME_TAC THENL
              [ASM_REWRITE_TAC[]; ALL_TAC] THEN
             ARM_SAFETY_SIM_TAC BIGNUM_MOD_EXEC (1--6) THEN
             DISCHARGE_SAFETY_PROPERTY_TAC),
           Leg("add", BIGNUM_MOD_SAFE_UPBODY_TAC `k:num` 8),
           Leg("end",
             ARM_SAFETY_SIM_TAC BIGNUM_MOD_EXEC [] THEN
             DISCHARGE_SAFETY_PROPERTY_TAC))))))))));;

let BIGNUM_MOD_SUBROUTINE_SAFE = prove
 (`exists f_events.
     forall e k z n x m pc stackpointer returnaddress.
        aligned 16 stackpointer /\
        nonoverlapping (z,8 * val k) (word_sub stackpointer (word 48),48) /\
        ALLPAIRS nonoverlapping
          [(z,8 * val k); (word_sub stackpointer (word 48),48)]
          [(word pc,0x440); (x,8 * val n); (m,8 * val k)] /\
        ~(val k = 0) /\ val k < 2 EXP 58 /\ val n < 2 EXP 58 - 1
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) bignum_mod_mc /\
                  read PC s = word pc /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [k;z;n;x;m] s /\
                  read events s = e)
             (\s. read PC s = returnaddress /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events x m z k n pc
                            (word_sub stackpointer (word 48)) returnaddress /\
                     memaccess_inbounds e2
                       [x,val n * 8; m,val k * 8; z,val k * 8;
                        word_sub stackpointer (word 48),48]
                       [z,val k * 8; word_sub stackpointer (word 48),48]))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bignum(z,val k);
                         memory :> bytes(word_sub stackpointer (word 48),48)])`,
  ARM_ADD_RETURN_STACK_TAC BIGNUM_MOD_EXEC BIGNUM_MOD_SAFE
   `[X19;X20;X21;X22;X23;X24]` 48 THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;
