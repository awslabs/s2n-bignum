(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Keccak-f1600 scalar code.                                                 *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

(**** print_coda_from_elf (-1) "arm/mlkem/mlkem_keccak_f1600.o";;
 ****)

let mlkem_keccak_f1600_mc,mlkem_keccak_f1600_data =
  define_coda_literal_from_elf
  "mlkem_keccak_f1600_mc" "mlkem_keccak_f1600_data"
   "arm/mlkem/mlkem_keccak_f1600.o"
[
  0xd10203ff;       (* arm_SUB SP SP (rvalue (word 128)) *)
  0xa90253f3;       (* arm_STP X19 X20 SP (Immediate_Offset (iword (&32))) *)
  0xa9035bf5;       (* arm_STP X21 X22 SP (Immediate_Offset (iword (&48))) *)
  0xa90463f7;       (* arm_STP X23 X24 SP (Immediate_Offset (iword (&64))) *)
  0xa9056bf9;       (* arm_STP X25 X26 SP (Immediate_Offset (iword (&80))) *)
  0xa90673fb;       (* arm_STP X27 X28 SP (Immediate_Offset (iword (&96))) *)
  0xa9077bfd;       (* arm_STP X29 X30 SP (Immediate_Offset (iword (&112))) *)
  0x1000233a;       (* arm_ADR X26 (word 1124) *)
  0xf90007fa;       (* arm_STR X26 SP (Immediate_Offset (word 8)) *)
  0xa9401801;       (* arm_LDP X1 X6 X0 (Immediate_Offset (iword (&0))) *)
  0xa941400b;       (* arm_LDP X11 X16 X0 (Immediate_Offset (iword (&16))) *)
  0xa9420815;       (* arm_LDP X21 X2 X0 (Immediate_Offset (iword (&32))) *)
  0xa9433007;       (* arm_LDP X7 X12 X0 (Immediate_Offset (iword (&48))) *)
  0xa9445811;       (* arm_LDP X17 X22 X0 (Immediate_Offset (iword (&64))) *)
  0xa9452003;       (* arm_LDP X3 X8 X0 (Immediate_Offset (iword (&80))) *)
  0xa946700d;       (* arm_LDP X13 X28 X0 (Immediate_Offset (iword (&96))) *)
  0xa9471017;       (* arm_LDP X23 X4 X0 (Immediate_Offset (iword (&112))) *)
  0xa9483809;       (* arm_LDP X9 X14 X0 (Immediate_Offset (iword (&128))) *)
  0xa9496013;       (* arm_LDP X19 X24 X0 (Immediate_Offset (iword (&144))) *)
  0xa94a2805;       (* arm_LDP X5 X10 X0 (Immediate_Offset (iword (&160))) *)
  0xa94b500f;       (* arm_LDP X15 X20 X0 (Immediate_Offset (iword (&176))) *)
  0xf9406019;       (* arm_LDR X25 X0 (Immediate_Offset (word 192)) *)
  0xf90003e0;       (* arm_STR X0 SP (Immediate_Offset (word 0)) *)
  0xca19031e;       (* arm_EOR X30 X24 X25 *)
  0xca0a013b;       (* arm_EOR X27 X9 X10 *)
  0xca1503c0;       (* arm_EOR X0 X30 X21 *)
  0xca06037a;       (* arm_EOR X26 X27 X6 *)
  0xca07035b;       (* arm_EOR X27 X26 X7 *)
  0xca16001d;       (* arm_EOR X29 X0 X22 *)
  0xca1703ba;       (* arm_EOR X26 X29 X23 *)
  0xca05009d;       (* arm_EOR X29 X4 X5 *)
  0xca0103be;       (* arm_EOR X30 X29 X1 *)
  0xca080360;       (* arm_EOR X0 X27 X8 *)
  0xca0203dd;       (* arm_EOR X29 X30 X2 *)
  0xca14027e;       (* arm_EOR X30 X19 X20 *)
  0xca1003de;       (* arm_EOR X30 X30 X16 *)
  0xcac0ff5b;       (* arm_EOR X27 X26 (Shiftedreg X0 ROR 63) *)
  0xca1b0084;       (* arm_EOR X4 X4 X27 *)
  0xca1103de;       (* arm_EOR X30 X30 X17 *)
  0xca1c03de;       (* arm_EOR X30 X30 X28 *)
  0xca0303bd;       (* arm_EOR X29 X29 X3 *)
  0xcadefc00;       (* arm_EOR X0 X0 (Shiftedreg X30 ROR 63) *)
  0xcaddffde;       (* arm_EOR X30 X30 (Shiftedreg X29 ROR 63) *)
  0xca1e02d6;       (* arm_EOR X22 X22 X30 *)
  0xca1e02f7;       (* arm_EOR X23 X23 X30 *)
  0xf9000ff7;       (* arm_STR X23 SP (Immediate_Offset (word 24)) *)
  0xca0f01d7;       (* arm_EOR X23 X14 X15 *)
  0xca0001ce;       (* arm_EOR X14 X14 X0 *)
  0xca0b02f7;       (* arm_EOR X23 X23 X11 *)
  0xca0001ef;       (* arm_EOR X15 X15 X0 *)
  0xca1b0021;       (* arm_EOR X1 X1 X27 *)
  0xca0c02f7;       (* arm_EOR X23 X23 X12 *)
  0xca0d02f7;       (* arm_EOR X23 X23 X13 *)
  0xca00016b;       (* arm_EOR X11 X11 X0 *)
  0xcad7ffbd;       (* arm_EOR X29 X29 (Shiftedreg X23 ROR 63) *)
  0xcadafef7;       (* arm_EOR X23 X23 (Shiftedreg X26 ROR 63) *)
  0xca0001ba;       (* arm_EOR X26 X13 X0 *)
  0xca17038d;       (* arm_EOR X13 X28 X23 *)
  0xca1e031c;       (* arm_EOR X28 X24 X30 *)
  0xca170218;       (* arm_EOR X24 X16 X23 *)
  0xca1e02b0;       (* arm_EOR X16 X21 X30 *)
  0xca1e0335;       (* arm_EOR X21 X25 X30 *)
  0xca17027e;       (* arm_EOR X30 X19 X23 *)
  0xca170293;       (* arm_EOR X19 X20 X23 *)
  0xca170234;       (* arm_EOR X20 X17 X23 *)
  0xca000191;       (* arm_EOR X17 X12 X0 *)
  0xca1b0040;       (* arm_EOR X0 X2 X27 *)
  0xca1d00c2;       (* arm_EOR X2 X6 X29 *)
  0xca1d0106;       (* arm_EOR X6 X8 X29 *)
  0x8aedbf88;       (* arm_BIC X8 X28 (Shiftedreg X13 ROR 47) *)
  0xca1b006c;       (* arm_EOR X12 X3 X27 *)
  0x8af14da3;       (* arm_BIC X3 X13 (Shiftedreg X17 ROR 19) *)
  0xca1b00a5;       (* arm_EOR X5 X5 X27 *)
  0xf9400ffb;       (* arm_LDR X27 SP (Immediate_Offset (word 24)) *)
  0x8ae21639;       (* arm_BIC X25 X17 (Shiftedreg X2 ROR 5) *)
  0xca1d0129;       (* arm_EOR X9 X9 X29 *)
  0xcac5d337;       (* arm_EOR X23 X25 (Shiftedreg X5 ROR 52) *)
  0xcac26063;       (* arm_EOR X3 X3 (Shiftedreg X2 ROR 24) *)
  0xcad10908;       (* arm_EOR X8 X8 (Shiftedreg X17 ROR 2) *)
  0xca1d0151;       (* arm_EOR X17 X10 X29 *)
  0x8af6bd99;       (* arm_BIC X25 X12 (Shiftedreg X22 ROR 47) *)
  0xca1d00fd;       (* arm_EOR X29 X7 X29 *)
  0x8afb088a;       (* arm_BIC X10 X4 (Shiftedreg X27 ROR 2) *)
  0x8afc28a7;       (* arm_BIC X7 X5 (Shiftedreg X28 ROR 10) *)
  0xcad4c94a;       (* arm_EOR X10 X10 (Shiftedreg X20 ROR 50) *)
  0xcacde4ed;       (* arm_EOR X13 X7 (Shiftedreg X13 ROR 57) *)
  0x8ae5bc47;       (* arm_BIC X7 X2 (Shiftedreg X5 ROR 47) *)
  0xcad89f22;       (* arm_EOR X2 X25 (Shiftedreg X24 ROR 39) *)
  0x8aebe699;       (* arm_BIC X25 X20 (Shiftedreg X11 ROR 57) *)
  0x8ae46625;       (* arm_BIC X5 X17 (Shiftedreg X4 ROR 25) *)
  0xcad1d739;       (* arm_EOR X25 X25 (Shiftedreg X17 ROR 53) *)
  0x8af1f171;       (* arm_BIC X17 X11 (Shiftedreg X17 ROR 60) *)
  0xcadce4fc;       (* arm_EOR X28 X7 (Shiftedreg X28 ROR 57) *)
  0x8aeca927;       (* arm_BIC X7 X9 (Shiftedreg X12 ROR 42) *)
  0xcad664e7;       (* arm_EOR X7 X7 (Shiftedreg X22 ROR 25) *)
  0x8af8e2d6;       (* arm_BIC X22 X22 (Shiftedreg X24 ROR 56) *)
  0x8aef7f18;       (* arm_BIC X24 X24 (Shiftedreg X15 ROR 31) *)
  0xcacf5ed6;       (* arm_EOR X22 X22 (Shiftedreg X15 ROR 23) *)
  0x8af4c374;       (* arm_BIC X20 X27 (Shiftedreg X20 ROR 48) *)
  0x8ae941ef;       (* arm_BIC X15 X15 (Shiftedreg X9 ROR 16) *)
  0xcacce9ec;       (* arm_EOR X12 X15 (Shiftedreg X12 ROR 58) *)
  0xcadb6caf;       (* arm_EOR X15 X5 (Shiftedreg X27 ROR 27) *)
  0xcacba685;       (* arm_EOR X5 X20 (Shiftedreg X11 ROR 41) *)
  0xf94007eb;       (* arm_LDR X11 SP (Immediate_Offset (word 8)) *)
  0xcac45634;       (* arm_EOR X20 X17 (Shiftedreg X4 ROR 21) *)
  0xcac9bf11;       (* arm_EOR X17 X24 (Shiftedreg X9 ROR 47) *)
  0xd2800038;       (* arm_MOV X24 (rvalue (word 1)) *)
  0x8af02409;       (* arm_BIC X9 X0 (Shiftedreg X16 ROR 9) *)
  0xf9000bf8;       (* arm_STR X24 SP (Immediate_Offset (word 16)) *)
  0x8ae1b3b8;       (* arm_BIC X24 X29 (Shiftedreg X1 ROR 44) *)
  0x8af5c83b;       (* arm_BIC X27 X1 (Shiftedreg X21 ROR 50) *)
  0x8afdff44;       (* arm_BIC X4 X26 (Shiftedreg X29 ROR 63) *)
  0xcac45421;       (* arm_EOR X1 X1 (Shiftedreg X4 ROR 21) *)
  0xf940016b;       (* arm_LDR X11 X11 (Immediate_Offset (word 0)) *)
  0x8afee6a4;       (* arm_BIC X4 X21 (Shiftedreg X30 ROR 57) *)
  0xcad57b15;       (* arm_EOR X21 X24 (Shiftedreg X21 ROR 30) *)
  0xcad3b138;       (* arm_EOR X24 X9 (Shiftedreg X19 ROR 44) *)
  0x8ae615c9;       (* arm_BIC X9 X14 (Shiftedreg X6 ROR 5) *)
  0xcac0ad29;       (* arm_EOR X9 X9 (Shiftedreg X0 ROR 43) *)
  0x8ae098c0;       (* arm_BIC X0 X6 (Shiftedreg X0 ROR 38) *)
  0xca0b0021;       (* arm_EOR X1 X1 X11 *)
  0xcada8c8b;       (* arm_EOR X11 X4 (Shiftedreg X26 ROR 35) *)
  0xcad0bc04;       (* arm_EOR X4 X0 (Shiftedreg X16 ROR 47) *)
  0x8af38e00;       (* arm_BIC X0 X16 (Shiftedreg X19 ROR 35) *)
  0xcadeaf70;       (* arm_EOR X16 X27 (Shiftedreg X30 ROR 43) *)
  0x8afaabdb;       (* arm_BIC X27 X30 (Shiftedreg X26 ROR 42) *)
  0x8aeea67a;       (* arm_BIC X26 X19 (Shiftedreg X14 ROR 41) *)
  0xcace3013;       (* arm_EOR X19 X0 (Shiftedreg X14 ROR 12) *)
  0xcac6bb4e;       (* arm_EOR X14 X26 (Shiftedreg X6 ROR 46) *)
  0xcadda766;       (* arm_EOR X6 X27 (Shiftedreg X29 ROR 41) *)
  0xcacbd1e0;       (* arm_EOR X0 X15 (Shiftedreg X11 ROR 52) *)
  0xcacdc000;       (* arm_EOR X0 X0 (Shiftedreg X13 ROR 48) *)
  0xcac9e51a;       (* arm_EOR X26 X8 (Shiftedreg X9 ROR 57) *)
  0xcace281b;       (* arm_EOR X27 X0 (Shiftedreg X14 ROR 10) *)
  0xcadcfe1d;       (* arm_EOR X29 X16 (Shiftedreg X28 ROR 63) *)
  0xcac6cf5a;       (* arm_EOR X26 X26 (Shiftedreg X6 ROR 51) *)
  0xcad6cafe;       (* arm_EOR X30 X23 (Shiftedreg X22 ROR 50) *)
  0xcaca7f40;       (* arm_EOR X0 X26 (Shiftedreg X10 ROR 31) *)
  0xcad397bd;       (* arm_EOR X29 X29 (Shiftedreg X19 ROR 37) *)
  0xcacc177b;       (* arm_EOR X27 X27 (Shiftedreg X12 ROR 5) *)
  0xcad88bde;       (* arm_EOR X30 X30 (Shiftedreg X24 ROR 34) *)
  0xcac76c00;       (* arm_EOR X0 X0 (Shiftedreg X7 ROR 27) *)
  0xcad56bda;       (* arm_EOR X26 X30 (Shiftedreg X21 ROR 26) *)
  0xcad93f5a;       (* arm_EOR X26 X26 (Shiftedreg X25 ROR 15) *)
  0x93dbfb7e;       (* arm_ROR X30 X27 62 *)
  0xcadae7de;       (* arm_EOR X30 X30 (Shiftedreg X26 ROR 57) *)
  0x93daeb5a;       (* arm_ROR X26 X26 58 *)
  0xca1003d0;       (* arm_EOR X16 X30 X16 *)
  0xcadcffdc;       (* arm_EOR X28 X30 (Shiftedreg X28 ROR 63) *)
  0xf9000ffc;       (* arm_STR X28 SP (Immediate_Offset (word 24)) *)
  0xcad193bd;       (* arm_EOR X29 X29 (Shiftedreg X17 ROR 36) *)
  0xcac2f43c;       (* arm_EOR X28 X1 (Shiftedreg X2 ROR 61) *)
  0xcad397d3;       (* arm_EOR X19 X30 (Shiftedreg X19 ROR 37) *)
  0xcad40bbd;       (* arm_EOR X29 X29 (Shiftedreg X20 ROR 2) *)
  0xcac4db9c;       (* arm_EOR X28 X28 (Shiftedreg X4 ROR 54) *)
  0xcac0df5a;       (* arm_EOR X26 X26 (Shiftedreg X0 ROR 55) *)
  0xcac39f9c;       (* arm_EOR X28 X28 (Shiftedreg X3 ROR 39) *)
  0xcac5679c;       (* arm_EOR X28 X28 (Shiftedreg X5 ROR 25) *)
  0x93c0e000;       (* arm_ROR X0 X0 56 *)
  0xcaddfc00;       (* arm_EOR X0 X0 (Shiftedreg X29 ROR 63) *)
  0xcadbf79b;       (* arm_EOR X27 X28 (Shiftedreg X27 ROR 61) *)
  0xcacdb80d;       (* arm_EOR X13 X0 (Shiftedreg X13 ROR 46) *)
  0xcadcffbc;       (* arm_EOR X28 X29 (Shiftedreg X28 ROR 63) *)
  0xcad40bdd;       (* arm_EOR X29 X30 (Shiftedreg X20 ROR 2) *)
  0xcac39f54;       (* arm_EOR X20 X26 (Shiftedreg X3 ROR 39) *)
  0xcacbc80b;       (* arm_EOR X11 X0 (Shiftedreg X11 ROR 50) *)
  0xcad92799;       (* arm_EOR X25 X28 (Shiftedreg X25 ROR 9) *)
  0xcad55383;       (* arm_EOR X3 X28 (Shiftedreg X21 ROR 20) *)
  0xca010355;       (* arm_EOR X21 X26 X1 *)
  0xcac9c769;       (* arm_EOR X9 X27 (Shiftedreg X9 ROR 49) *)
  0xcad87398;       (* arm_EOR X24 X28 (Shiftedreg X24 ROR 28) *)
  0xcad193c1;       (* arm_EOR X1 X30 (Shiftedreg X17 ROR 36) *)
  0xcace200e;       (* arm_EOR X14 X0 (Shiftedreg X14 ROR 8) *)
  0xcad6b396;       (* arm_EOR X22 X28 (Shiftedreg X22 ROR 44) *)
  0xcac8e368;       (* arm_EOR X8 X27 (Shiftedreg X8 ROR 56) *)
  0xcac74f71;       (* arm_EOR X17 X27 (Shiftedreg X7 ROR 19) *)
  0xcacff80f;       (* arm_EOR X15 X0 (Shiftedreg X15 ROR 62) *)
  0x8af6be87;       (* arm_BIC X7 X20 (Shiftedreg X22 ROR 47) *)
  0xcac4db44;       (* arm_EOR X4 X26 (Shiftedreg X4 ROR 54) *)
  0xcacc0c00;       (* arm_EOR X0 X0 (Shiftedreg X12 ROR 3) *)
  0xcad7eb9c;       (* arm_EOR X28 X28 (Shiftedreg X23 ROR 58) *)
  0xcac2f757;       (* arm_EOR X23 X26 (Shiftedreg X2 ROR 61) *)
  0xcac5675a;       (* arm_EOR X26 X26 (Shiftedreg X5 ROR 25) *)
  0xcad09ce2;       (* arm_EOR X2 X7 (Shiftedreg X16 ROR 39) *)
  0x8af4a927;       (* arm_BIC X7 X9 (Shiftedreg X20 ROR 42) *)
  0x8ae941fe;       (* arm_BIC X30 X15 (Shiftedreg X9 ROR 16) *)
  0xcad664e7;       (* arm_EOR X7 X7 (Shiftedreg X22 ROR 25) *)
  0xcad4ebcc;       (* arm_EOR X12 X30 (Shiftedreg X20 ROR 58) *)
  0x8af0e2d4;       (* arm_BIC X20 X22 (Shiftedreg X16 ROR 56) *)
  0xcac6af7e;       (* arm_EOR X30 X27 (Shiftedreg X6 ROR 43) *)
  0xcacf5e96;       (* arm_EOR X22 X20 (Shiftedreg X15 ROR 23) *)
  0x8aedaa66;       (* arm_BIC X6 X19 (Shiftedreg X13 ROR 42) *)
  0xcad1a4c6;       (* arm_EOR X6 X6 (Shiftedreg X17 ROR 41) *)
  0x8af1fda5;       (* arm_BIC X5 X13 (Shiftedreg X17 ROR 63) *)
  0xcac556a5;       (* arm_EOR X5 X21 (Shiftedreg X5 ROR 21) *)
  0x8af5b231;       (* arm_BIC X17 X17 (Shiftedreg X21 ROR 44) *)
  0xcaca5f7b;       (* arm_EOR X27 X27 (Shiftedreg X10 ROR 23) *)
  0x8af9cab5;       (* arm_BIC X21 X21 (Shiftedreg X25 ROR 50) *)
  0x8ae46774;       (* arm_BIC X20 X27 (Shiftedreg X4 ROR 25) *)
  0x8aef7e0a;       (* arm_BIC X10 X16 (Shiftedreg X15 ROR 31) *)
  0xcad3aeb0;       (* arm_EOR X16 X21 (Shiftedreg X19 ROR 43) *)
  0xcad97a35;       (* arm_EOR X21 X17 (Shiftedreg X25 ROR 30) *)
  0x8af3e733;       (* arm_BIC X19 X25 (Shiftedreg X19 ROR 57) *)
  0xf9400bf9;       (* arm_LDR X25 SP (Immediate_Offset (word 16)) *)
  0xcac9bd51;       (* arm_EOR X17 X10 (Shiftedreg X9 ROR 47) *)
  0xf94007e9;       (* arm_LDR X9 SP (Immediate_Offset (word 8)) *)
  0xcadc6e8f;       (* arm_EOR X15 X20 (Shiftedreg X28 ROR 27) *)
  0x8afc0894;       (* arm_BIC X20 X4 (Shiftedreg X28 ROR 2) *)
  0xcac1ca8a;       (* arm_EOR X10 X20 (Shiftedreg X1 ROR 50) *)
  0x8afbf174;       (* arm_BIC X20 X11 (Shiftedreg X27 ROR 60) *)
  0xcac45694;       (* arm_EOR X20 X20 (Shiftedreg X4 ROR 21) *)
  0x8ae1c384;       (* arm_BIC X4 X28 (Shiftedreg X1 ROR 48) *)
  0x8aebe421;       (* arm_BIC X1 X1 (Shiftedreg X11 ROR 57) *)
  0xf879793c;       (* arm_LDR X28 X9 (Shiftreg_Offset X25 3) *)
  0xf9400fe9;       (* arm_LDR X9 SP (Immediate_Offset (word 24)) *)
  0x91000739;       (* arm_ADD X25 X25 (rvalue (word 1)) *)
  0xf9000bf9;       (* arm_STR X25 SP (Immediate_Offset (word 16)) *)
  0xf1005f3f;       (* arm_CMP X25 (rvalue (word 23)) *)
  0xcadbd439;       (* arm_EOR X25 X1 (Shiftedreg X27 ROR 53) *)
  0x8afabfdb;       (* arm_BIC X27 X30 (Shiftedreg X26 ROR 47) *)
  0xca1c00a1;       (* arm_EOR X1 X5 X28 *)
  0xcacba485;       (* arm_EOR X5 X4 (Shiftedreg X11 ROR 41) *)
  0xcacd8e6b;       (* arm_EOR X11 X19 (Shiftedreg X13 ROR 35) *)
  0x8af82b4d;       (* arm_BIC X13 X26 (Shiftedreg X24 ROR 10) *)
  0xcad8e77c;       (* arm_EOR X28 X27 (Shiftedreg X24 ROR 57) *)
  0x8ae9bf1b;       (* arm_BIC X27 X24 (Shiftedreg X9 ROR 47) *)
  0x8ae326f3;       (* arm_BIC X19 X23 (Shiftedreg X3 ROR 9) *)
  0x8aeea7a4;       (* arm_BIC X4 X29 (Shiftedreg X14 ROR 41) *)
  0xcaddb278;       (* arm_EOR X24 X19 (Shiftedreg X29 ROR 44) *)
  0x8afd8c7d;       (* arm_BIC X29 X3 (Shiftedreg X29 ROR 35) *)
  0xcac9e5ad;       (* arm_EOR X13 X13 (Shiftedreg X9 ROR 57) *)
  0xcace33b3;       (* arm_EOR X19 X29 (Shiftedreg X14 ROR 12) *)
  0x8ae04d3d;       (* arm_BIC X29 X9 (Shiftedreg X0 ROR 19) *)
  0x8ae815ce;       (* arm_BIC X14 X14 (Shiftedreg X8 ROR 5) *)
  0xcad7adc9;       (* arm_EOR X9 X14 (Shiftedreg X23 ROR 43) *)
  0xcac8b88e;       (* arm_EOR X14 X4 (Shiftedreg X8 ROR 46) *)
  0x8af79917;       (* arm_BIC X23 X8 (Shiftedreg X23 ROR 38) *)
  0xcac00b68;       (* arm_EOR X8 X27 (Shiftedreg X0 ROR 2) *)
  0xcac3bee4;       (* arm_EOR X4 X23 (Shiftedreg X3 ROR 47) *)
  0x8afe1403;       (* arm_BIC X3 X0 (Shiftedreg X30 ROR 5) *)
  0xcadad077;       (* arm_EOR X23 X3 (Shiftedreg X26 ROR 52) *)
  0xcade63a3;       (* arm_EOR X3 X29 (Shiftedreg X30 ROR 24) *)
  0x54fff20d;       (* arm_BLE (word 2096704) *)
  0x93c6acc6;       (* arm_ROR X6 X6 43 *)
  0x93cbc96b;       (* arm_ROR X11 X11 50 *)
  0x93d552b5;       (* arm_ROR X21 X21 20 *)
  0x93c2f442;       (* arm_ROR X2 X2 61 *)
  0x93c74ce7;       (* arm_ROR X7 X7 19 *)
  0x93cc0d8c;       (* arm_ROR X12 X12 3 *)
  0x93d19231;       (* arm_ROR X17 X17 36 *)
  0x93d6b2d6;       (* arm_ROR X22 X22 44 *)
  0x93c39c63;       (* arm_ROR X3 X3 39 *)
  0x93c8e108;       (* arm_ROR X8 X8 56 *)
  0x93cdb9ad;       (* arm_ROR X13 X13 46 *)
  0x93dcff9c;       (* arm_ROR X28 X28 63 *)
  0x93d7eaf7;       (* arm_ROR X23 X23 58 *)
  0x93c4d884;       (* arm_ROR X4 X4 54 *)
  0x93c9c529;       (* arm_ROR X9 X9 49 *)
  0x93ce21ce;       (* arm_ROR X14 X14 8 *)
  0x93d39673;       (* arm_ROR X19 X19 37 *)
  0x93d87318;       (* arm_ROR X24 X24 28 *)
  0x93c564a5;       (* arm_ROR X5 X5 25 *)
  0x93ca5d4a;       (* arm_ROR X10 X10 23 *)
  0x93cff9ef;       (* arm_ROR X15 X15 62 *)
  0x93d40a94;       (* arm_ROR X20 X20 2 *)
  0x93d92739;       (* arm_ROR X25 X25 9 *)
  0xf94003e0;       (* arm_LDR X0 SP (Immediate_Offset (word 0)) *)
  0xa9001801;       (* arm_STP X1 X6 X0 (Immediate_Offset (iword (&0))) *)
  0xa901400b;       (* arm_STP X11 X16 X0 (Immediate_Offset (iword (&16))) *)
  0xa9020815;       (* arm_STP X21 X2 X0 (Immediate_Offset (iword (&32))) *)
  0xa9033007;       (* arm_STP X7 X12 X0 (Immediate_Offset (iword (&48))) *)
  0xa9045811;       (* arm_STP X17 X22 X0 (Immediate_Offset (iword (&64))) *)
  0xa9052003;       (* arm_STP X3 X8 X0 (Immediate_Offset (iword (&80))) *)
  0xa906700d;       (* arm_STP X13 X28 X0 (Immediate_Offset (iword (&96))) *)
  0xa9071017;       (* arm_STP X23 X4 X0 (Immediate_Offset (iword (&112))) *)
  0xa9083809;       (* arm_STP X9 X14 X0 (Immediate_Offset (iword (&128))) *)
  0xa9096013;       (* arm_STP X19 X24 X0 (Immediate_Offset (iword (&144))) *)
  0xa90a2805;       (* arm_STP X5 X10 X0 (Immediate_Offset (iword (&160))) *)
  0xa90b500f;       (* arm_STP X15 X20 X0 (Immediate_Offset (iword (&176))) *)
  0xf9006019;       (* arm_STR X25 X0 (Immediate_Offset (word 192)) *)
  0xa94253f3;       (* arm_LDP X19 X20 SP (Immediate_Offset (iword (&32))) *)
  0xa9435bf5;       (* arm_LDP X21 X22 SP (Immediate_Offset (iword (&48))) *)
  0xa94463f7;       (* arm_LDP X23 X24 SP (Immediate_Offset (iword (&64))) *)
  0xa9456bf9;       (* arm_LDP X25 X26 SP (Immediate_Offset (iword (&80))) *)
  0xa94673fb;       (* arm_LDP X27 X28 SP (Immediate_Offset (iword (&96))) *)
  0xa9477bfd;       (* arm_LDP X29 X30 SP (Immediate_Offset (iword (&112))) *)
  0x910203ff;       (* arm_ADD SP SP (rvalue (word 128)) *)
  0xd65f03c0        (* arm_RET X30 *)
]
[1; 0; 0; 0; 0; 0; 0; 0; 130; 128; 0; 0; 0; 0; 0; 0; 138; 128; 0; 0; 0; 0; 0;
 128; 0; 128; 0; 128; 0; 0; 0; 128; 139; 128; 0; 0; 0; 0; 0; 0; 1; 0; 0; 128;
 0; 0; 0; 0; 129; 128; 0; 128; 0; 0; 0; 128; 9; 128; 0; 0; 0; 0; 0; 128; 138;
 0; 0; 0; 0; 0; 0; 0; 136; 0; 0; 0; 0; 0; 0; 0; 9; 128; 0; 128; 0; 0; 0; 0;
 10; 0; 0; 128; 0; 0; 0; 0; 139; 128; 0; 128; 0; 0; 0; 0; 139; 0; 0; 0; 0; 0;
 0; 128; 137; 128; 0; 0; 0; 0; 0; 128; 3; 128; 0; 0; 0; 0; 0; 128; 2; 128; 0;
 0; 0; 0; 0; 128; 128; 0; 0; 0; 0; 0; 0; 128; 10; 128; 0; 0; 0; 0; 0; 0; 10;
 0; 0; 128; 0; 0; 0; 128; 129; 128; 0; 128; 0; 0; 0; 128; 128; 128; 0; 0; 0;
 0; 0; 128; 1; 0; 0; 128; 0; 0; 0; 0; 8; 128; 0; 128; 0; 0; 0; 128];;

let MLKEM_KECCAK_F1600_EXEC = ARM_MK_EXEC_RULE mlkem_keccak_f1600_mc;;

(* ------------------------------------------------------------------------- *)
(* Specification and abbreviations.                                          *)
(* ------------------------------------------------------------------------- *)

parse_as_prefix "~~";;
override_interface("~~",`word_not:N word->N word`);;
parse_as_infix("&&",(13,"right"));;
override_interface("&&",`word_and:N word->N word->N word`);;
parse_as_infix("||",(13,"right"));;
override_interface("^^",`word_xor:N word->N word->N word`);;
parse_as_infix("^^",(13,"right"));;
override_interface("||",`word_or:N word->N word->N word`);;

(*** Keccak round constants RC[i] for i = 0..23 ***)

let round_constants = define
 `round_constants:int64 list =
   [word 0x0000000000000001;
    word 0x0000000000008082;
    word 0x800000000000808a;
    word 0x8000000080008000;
    word 0x000000000000808b;
    word 0x0000000080000001;
    word 0x8000000080008081;
    word 0x8000000000008009;
    word 0x000000000000008a;
    word 0x0000000000000088;
    word 0x0000000080008009;
    word 0x000000008000000a;
    word 0x000000008000808b;
    word 0x800000000000008b;
    word 0x8000000000008089;
    word 0x8000000000008003;
    word 0x8000000000008002;
    word 0x8000000000000080;
    word 0x000000000000800a;
    word 0x800000008000000a;
    word 0x8000000080008081;
    word 0x8000000000008080;
    word 0x0000000080000001;
    word 0x8000000080008008]`;;

(*** An individual round, with input and output lists in row-major order ***)

let keccak_round = define
 `(keccak_round:int64 -> int64 list->int64 list) RCi Alist =
  let A00 = EL  0 Alist
  and A10 = EL  1 Alist
  and A20 = EL  2 Alist
  and A30 = EL  3 Alist
  and A40 = EL  4 Alist
  and A01 = EL  5 Alist
  and A11 = EL  6 Alist
  and A21 = EL  7 Alist
  and A31 = EL  8 Alist
  and A41 = EL  9 Alist
  and A02 = EL 10 Alist
  and A12 = EL 11 Alist
  and A22 = EL 12 Alist
  and A32 = EL 13 Alist
  and A42 = EL 14 Alist
  and A03 = EL 15 Alist
  and A13 = EL 16 Alist
  and A23 = EL 17 Alist
  and A33 = EL 18 Alist
  and A43 = EL 19 Alist
  and A04 = EL 20 Alist
  and A14 = EL 21 Alist
  and A24 = EL 22 Alist
  and A34 = EL 23 Alist
  and A44 = EL 24 Alist in
  let C0 = A00 ^^ A01 ^^ A02 ^^ A03 ^^ A04
  and C1 = A10 ^^ A11 ^^ A12 ^^ A13 ^^ A14
  and C2 = A20 ^^ A21 ^^ A22 ^^ A23 ^^ A24
  and C3 = A30 ^^ A31 ^^ A32 ^^ A33 ^^ A34
  and C4 = A40 ^^ A41 ^^ A42 ^^ A43 ^^ A44 in
  let D0 = C4 ^^ word_rol C1 1
  and D1 = C0 ^^ word_rol C2 1
  and D2 = C1 ^^ word_rol C3 1
  and D3 = C2 ^^ word_rol C4 1
  and D4 = C3 ^^ word_rol C0 1 in
  let At00 = A00 ^^ D0
  and At01 = A01 ^^ D0
  and At02 = A02 ^^ D0
  and At03 = A03 ^^ D0
  and At04 = A04 ^^ D0
  and At10 = A10 ^^ D1
  and At11 = A11 ^^ D1
  and At12 = A12 ^^ D1
  and At13 = A13 ^^ D1
  and At14 = A14 ^^ D1
  and At20 = A20 ^^ D2
  and At21 = A21 ^^ D2
  and At22 = A22 ^^ D2
  and At23 = A23 ^^ D2
  and At24 = A24 ^^ D2
  and At30 = A30 ^^ D3
  and At31 = A31 ^^ D3
  and At32 = A32 ^^ D3
  and At33 = A33 ^^ D3
  and At34 = A34 ^^ D3
  and At40 = A40 ^^ D4
  and At41 = A41 ^^ D4
  and At42 = A42 ^^ D4
  and At43 = A43 ^^ D4
  and At44 = A44 ^^ D4 in
  let B00 = word_rol At00  0
  and B01 = word_rol At30 28
  and B02 = word_rol At10  1
  and B03 = word_rol At40 27
  and B04 = word_rol At20 62
  and B10 = word_rol At11 44
  and B11 = word_rol At41 20
  and B12 = word_rol At21  6
  and B13 = word_rol At01 36
  and B14 = word_rol At31 55
  and B20 = word_rol At22 43
  and B21 = word_rol At02  3
  and B22 = word_rol At32 25
  and B23 = word_rol At12 10
  and B24 = word_rol At42 39
  and B30 = word_rol At33 21
  and B31 = word_rol At13 45
  and B32 = word_rol At43  8
  and B33 = word_rol At23 15
  and B34 = word_rol At03 41
  and B40 = word_rol At44 14
  and B41 = word_rol At24 61
  and B42 = word_rol At04 18
  and B43 = word_rol At34 56
  and B44 = word_rol At14  2 in
  [(B00 ^^ (~~B10 && B20)) ^^ RCi;
   B10 ^^ (~~B20 && B30);
   B20 ^^ (~~B30 && B40);
   B30 ^^ (~~B40 && B00);
   B40 ^^ (~~B00 && B10);
   B01 ^^ (~~B11 && B21);
   B11 ^^ (~~B21 && B31);
   B21 ^^ (~~B31 && B41);
   B31 ^^ (~~B41 && B01);
   B41 ^^ (~~B01 && B11);
   B02 ^^ (~~B12 && B22);
   B12 ^^ (~~B22 && B32);
   B22 ^^ (~~B32 && B42);
   B32 ^^ (~~B42 && B02);
   B42 ^^ (~~B02 && B12);
   B03 ^^ (~~B13 && B23);
   B13 ^^ (~~B23 && B33);
   B23 ^^ (~~B33 && B43);
   B33 ^^ (~~B43 && B03);
   B43 ^^ (~~B03 && B13);
   B04 ^^ (~~B14 && B24);
   B14 ^^ (~~B24 && B34);
   B24 ^^ (~~B34 && B44);
   B34 ^^ (~~B44 && B04);
   B44 ^^ (~~B04 && B14)]`;;

(*** Hence a recursive definition of n rounds starting from l ***)

let keccak = define
 `keccak 0 l = l /\
  keccak (n + 1) l = keccak_round (EL n round_constants) (keccak n l)`;;

(* ------------------------------------------------------------------------- *)
(* Convenient constructs to state and prove correctness. Should possibly     *)
(* introduce a full state component for word lists eventually.               *)
(* ------------------------------------------------------------------------- *)

let wordlist_from_memory = define
 `wordlist_from_memory(a,0) s = [] /\
  wordlist_from_memory(a,SUC n) s =
  APPEND (wordlist_from_memory(a,n) s)
         [read (memory :> bytes64(word_add a (word(8 * n)))) s]`;;

(*** This is very naive and should be done more efficiently ***)

let WORDLIST_FROM_MEMORY_CONV =
  let uconv =
    (LAND_CONV(RAND_CONV num_CONV) THENC
     GEN_REWRITE_CONV I [CONJUNCT2 wordlist_from_memory]) ORELSEC
     GEN_REWRITE_CONV I [CONJUNCT1 wordlist_from_memory] in
  let conv =
    TOP_DEPTH_CONV uconv THENC
    ONCE_DEPTH_CONV NUM_MULT_CONV THENC
    GEN_REWRITE_CONV ONCE_DEPTH_CONV [WORD_ADD_0] THENC
    GEN_REWRITE_CONV TOP_DEPTH_CONV [APPEND]
  and filt = can (term_match [] `wordlist_from_memory(a,NUMERAL n) s`) in
  conv o check filt;;

(*** Evaluate EL in concrete instances ***)

let EL_CONV =
  let conv0 = GEN_REWRITE_CONV I [CONJUNCT1 EL] THENC GEN_REWRITE_CONV I [HD]
  and conv1 = GEN_REWRITE_CONV I [CONJUNCT2 EL]
  and convt = GEN_REWRITE_CONV I [TL] in
  let convs = LAND_CONV num_CONV THENC conv1 THENC RAND_CONV convt in
  let rec conv tm = (conv0 ORELSEC (convs THENC conv)) tm in
  conv;;

(*** Additional lazy/deferred rotations in the implementation, same order ***)

let deferred_rotates = define
 `deferred_rotates =
   [ 0; 21; 14;  0; 44;
     3; 45; 61; 28; 20;
    25;  8; 18;  1;  6;
    10; 15; 56; 27; 36;
    39; 41; 2; 62; 55]`;;

(*** Introduce ghost variables for the register reads in a list ***)

let GHOST_REGLIST_TAC =
  W(fun (asl,w) ->
        let regreads = map rator (dest_list(find_term is_list w)) in
        let regnames = map ((^) "init_" o name_of o rand) regreads in
        let ghostvars = map (C (curry mk_var) `:int64`) regnames in
        EVERY(map2 GHOST_INTRO_TAC ghostvars regreads));;

(*** Alternative forms of the constant tables ***)

let BYTES_LOADED_DATA = prove
 (`bytes_loaded s (word (pc + 0x480)) mlkem_keccak_f1600_data <=>
   read (memory :> bytes(word (pc + 0x480),192)) s =
   num_of_bytelist mlkem_keccak_f1600_data`,
  REWRITE_TAC[bytes_loaded; READ_BYTELIST_EQ_BYTES;
    CONV_RULE (RAND_CONV LENGTH_CONV)
     (AP_TERM `LENGTH:byte list->num` mlkem_keccak_f1600_data)]);;

(* ------------------------------------------------------------------------- *)
(* Correctness proof                                                         *)
(* ------------------------------------------------------------------------- *)

let MLKEM_KECCAK_F1600_CORRECT = prove
 (`!a A pc stackpointer.
      aligned 16 stackpointer /\
      nonoverlapping (word pc,0x540) (a,200) /\
      ALL (nonoverlapping (stackpointer,32)) [(word pc,0x540); (a,200)]
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc)
                  (APPEND mlkem_keccak_f1600_mc mlkem_keccak_f1600_data) /\
                read PC s = word (pc + 0x1c) /\
                read SP s = stackpointer /\
                C_ARGUMENTS [a] s /\
                wordlist_from_memory(a,25) s = A)
           (\s. read PC s = word(pc + 0x460) /\
                wordlist_from_memory(a,25) s = keccak 24 A)
           (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [X19; X20; X21; X22; X23; X24;
                       X25; X26; X27; X28; X29; X30] ,,
            MAYCHANGE [memory :> bytes(a,200);
                       memory :> bytes(stackpointer,32)])`,
  MAP_EVERY X_GEN_TAC
   [`a:int64`; `A:int64 list`; `pc:num`; `stackpointer:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** Separate out the code and data assumptions ***)

  REWRITE_TAC[ALIGNED_BYTES_LOADED_APPEND_CLAUSE] THEN
  REWRITE_TAC[fst MLKEM_KECCAK_F1600_EXEC] THEN
  REWRITE_TAC[BYTES_LOADED_DATA] THEN

  (*** Address the constant table using a distinct pointer wpc ***)

  ABBREV_TAC `wpc:int64 = word(pc + 0x480)` THEN
  SUBGOAL_THEN
   `nonoverlapping (a:int64,200) (wpc:int64,192) /\
    nonoverlapping (stackpointer,32) (wpc:int64,192)` MP_TAC THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES] THENL
   [EXPAND_TAC "wpc" THEN CONJ_TAC THEN NONOVERLAPPING_TAC;
    STRIP_TAC] THEN

  (*** Set up the loop invariant ***)

  ENSURES_WHILE_PAUP_TAC `1` `24` `pc + 0x208` `pc + 0x3c8`
   `\i s.
      (read SP s = stackpointer /\
       read (memory :> bytes (wpc,192)) s =
       num_of_bytelist mlkem_keccak_f1600_data /\
       read (memory :> bytes64 stackpointer) s = a /\
       read (memory :> bytes64(word_add stackpointer (word 8))) s = wpc /\
       read (memory :> bytes64(word_add stackpointer (word 16))) s = word i /\
       MAP2 word_rol
        [read X1 s; read X6 s; read X11 s; read X16 s; read X21 s;
         read X2 s; read X7 s; read X12 s; read X17 s; read X22 s;
         read X3 s; read X8 s; read X13 s; read X28 s; read X23 s;
         read X4 s; read X9 s; read X14 s; read X19 s; read X24 s;
         read X5 s; read X10 s; read X15 s; read X20 s; read X25 s]
        deferred_rotates = keccak i A) /\
     (condition_semantics Condition_LE s <=> i <= 23)` THEN
  REWRITE_TAC[condition_semantics] THEN REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** Initial holding of the invariant ***)

    ENSURES_INIT_TAC "s0" THEN
    BIGNUM_DIGITIZE_TAC "A_" `read (memory :> bytes (a,8 * 25)) s0` THEN
    FIRST_ASSUM(MP_TAC o CONV_RULE(LAND_CONV WORDLIST_FROM_MEMORY_CONV)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN

    MP_TAC(INST [`s0:armstate`,`s:armstate`] BYTES_LOADED_DATA) THEN
    ASM_REWRITE_TAC[] THEN
    GEN_REWRITE_TAC (LAND_CONV o LAND_CONV)
     [WORD_RULE `wpc:int64 = word(val wpc + 0)`] THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [mlkem_keccak_f1600_data] THEN
    CONV_TAC(LAND_CONV DATA64_CONV) THEN
    REWRITE_TAC[WORD_RULE `word(val x + n) = word_add x (word n)`] THEN
    REWRITE_TAC[bytes_loaded_nil; WORD_ADD_0] THEN STRIP_TAC THEN

    ARM_STEPS_TAC MLKEM_KECCAK_F1600_EXEC (1--123) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN

    EXPAND_TAC "A" THEN
    SUBST1_TAC(MESON[ADD_CLAUSES] `keccak 1 = keccak (0 + 1)`) THEN
    REWRITE_TAC[keccak; round_constants; EL; HD] THEN
    REWRITE_TAC[keccak_round] THEN CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    REWRITE_TAC[deferred_rotates; MAP2] THEN REWRITE_TAC[CONS_11] THEN
    REPEAT CONJ_TAC THEN BITBLAST_TAC;

    (*** Preservation of the invariant including end condition code ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
    GHOST_REGLIST_TAC THEN ENSURES_INIT_TAC "s0" THEN

    SUBGOAL_THEN
     `read (memory :> bytes64(word_add wpc (word(8 * i)))) s0 =
      EL i round_constants`
    ASSUME_TAC THENL
     [MP_TAC(INST [`s0:armstate`,`s:armstate`] BYTES_LOADED_DATA) THEN
      ASM_REWRITE_TAC[] THEN GEN_REWRITE_TAC (LAND_CONV o LAND_CONV)
       [WORD_RULE `wpc:int64 = word(val wpc + 0)`] THEN
      GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [mlkem_keccak_f1600_data] THEN
      CONV_TAC(LAND_CONV DATA64_CONV) THEN
      REWRITE_TAC[WORD_RULE `word(val x + n) = word_add x (word n)`] THEN
      REWRITE_TAC[bytes_loaded_nil; WORD_ADD_0] THEN STRIP_TAC THEN
      UNDISCH_TAC `i < 24` THEN SPEC_TAC(`i:num`,`i:num`) THEN
      CONV_TAC EXPAND_CASES_CONV THEN
      CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
      ASM_REWRITE_TAC[round_constants; WORD_ADD_0] THEN
      CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN REWRITE_TAC[];
      ALL_TAC] THEN

    ARM_STEPS_TAC MLKEM_KECCAK_F1600_EXEC (1--112) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [CONV_TAC WORD_ARITH; ALL_TAC] THEN CONJ_TAC THENL
     [ALL_TAC;
      UNDISCH_TAC `i < 24` THEN SPEC_TAC(`i:num`,`i:num`) THEN
      CONV_TAC EXPAND_CASES_CONV THEN
      CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV)] THEN

    REWRITE_TAC[keccak] THEN FIRST_X_ASSUM(fun th ->
      GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [SYM th]) THEN
    REWRITE_TAC[deferred_rotates; MAP2] THEN
    REWRITE_TAC[keccak_round] THEN CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    REWRITE_TAC[deferred_rotates; MAP2] THEN REWRITE_TAC[CONS_11] THEN
    REPEAT CONJ_TAC THEN BITBLAST_TAC;

    (*** The trivial loop-back goal ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    ARM_SIM_TAC MLKEM_KECCAK_F1600_EXEC [1] THEN
    ASM_REWRITE_TAC[ARITH_RULE `i <= 23 <=> i < 24`];

    (*** The tail of deferred rotations and writeback ***)

    GHOST_REGLIST_TAC THEN
    ARM_SIM_TAC MLKEM_KECCAK_F1600_EXEC (1--38) THEN
    CONV_TAC(LAND_CONV WORDLIST_FROM_MEMORY_CONV) THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
    REWRITE_TAC[deferred_rotates; MAP2; CONS_11] THEN
    REPEAT CONJ_TAC THEN BITBLAST_TAC]);;

let MLKEM_KECCAK_F1600_SUBROUTINE_CORRECT = prove
 (`!a A pc stackpointer returnaddress.
      aligned 16 stackpointer /\
      nonoverlapping (word pc,0x540) (a,200) /\
      ALL (nonoverlapping (word_sub stackpointer (word 128),128))
          [(word pc,0x540); (a,200)]
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc)
                  (APPEND mlkem_keccak_f1600_mc mlkem_keccak_f1600_data) /\
                read PC s = word pc /\
                read SP s = stackpointer /\
                read X30 s = returnaddress /\
                C_ARGUMENTS [a] s /\
                wordlist_from_memory(a,25) s = A)
           (\s. read PC s = returnaddress /\
                wordlist_from_memory(a,25) s = keccak 24 A)
           (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [memory :> bytes(a,200);
                       memory :> bytes(word_sub stackpointer (word 128),128)])`,
  let TWEAK_CONV = ONCE_DEPTH_CONV WORDLIST_FROM_MEMORY_CONV in
  REWRITE_TAC[ALIGNED_BYTES_LOADED_APPEND_CLAUSE; BYTES_LOADED_DATA;
              fst MLKEM_KECCAK_F1600_EXEC] THEN
  CONV_TAC TWEAK_CONV THEN
  ARM_ADD_RETURN_STACK_TAC ~pre_post_nsteps:(7,7) MLKEM_KECCAK_F1600_EXEC
   (REWRITE_RULE[ALIGNED_BYTES_LOADED_APPEND_CLAUSE; BYTES_LOADED_DATA;
                 fst MLKEM_KECCAK_F1600_EXEC]
        (CONV_RULE TWEAK_CONV MLKEM_KECCAK_F1600_CORRECT))
    `[X19; X20; X21; X22; X23; X24; X25; X26; X27; X28; X29; X30]` 128);;
