(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The x25519 function for curve25519 on standard basepoint 9 (byte args).   *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "arm/proofs/bignum_inv_p25519.ml";;
needs "common/ecencoding.ml";;

do_list hide_constant ["X1";"X2";"X3";"X4";"X5"];;
needs "EC/family25519.ml";;
needs "EC/exprojective.ml";;
needs "EC/x25519.ml";;
do_list unhide_constant ["X1";"X2";"X3";"X4";"X5"];;

prioritize_int();;
prioritize_real();;
prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* The code, and also the data table from the .rodata section.               *)
(* ------------------------------------------------------------------------- *)

(**** print_literal_relocs_from_elf "arm/curve25519/curve25519_x25519base_byte_alt.o";;
 ****)

let curve25519_x25519base_byte_alt_mc,const_data_list =
  define_assert_relocs_from_elf
    ~map_symbol_name:(function
      | "WHOLE_READONLY" | "ltmp1" (* MacOS *)
      | "curve25519_x25519base_byte_alt_constant"
        -> "curve25519_x25519base_byte_alt_constant_data"
      | s -> failwith ("unknown symbol: " ^ s))
    "curve25519_x25519base_byte_alt_mc"
    "arm/curve25519/curve25519_x25519base_byte_alt.o"
(fun w BL ADR ADRP ADD_rri64 -> [
  w 0xa9bf53f3;         (* arm_STP X19 X20 SP (Preimmediate_Offset (iword (-- &16))) *)
  w 0xa9bf5bf5;         (* arm_STP X21 X22 SP (Preimmediate_Offset (iword (-- &16))) *)
  w 0xa9bf63f7;         (* arm_STP X23 X24 SP (Preimmediate_Offset (iword (-- &16))) *)
  w 0xd10703ff;         (* arm_SUB SP SP (rvalue (word 448)) *)
  w 0xaa0003f7;         (* arm_MOV X23 X0 *)
  w 0x3940002a;         (* arm_LDRB W10 X1 (Immediate_Offset (word 0)) *)
  w 0x39400420;         (* arm_LDRB W0 X1 (Immediate_Offset (word 1)) *)
  w 0xaa00214a;         (* arm_ORR X10 X10 (Shiftedreg X0 LSL 8) *)
  w 0x39400820;         (* arm_LDRB W0 X1 (Immediate_Offset (word 2)) *)
  w 0xaa00414a;         (* arm_ORR X10 X10 (Shiftedreg X0 LSL 16) *)
  w 0x39400c20;         (* arm_LDRB W0 X1 (Immediate_Offset (word 3)) *)
  w 0xaa00614a;         (* arm_ORR X10 X10 (Shiftedreg X0 LSL 24) *)
  w 0x39401020;         (* arm_LDRB W0 X1 (Immediate_Offset (word 4)) *)
  w 0xaa00814a;         (* arm_ORR X10 X10 (Shiftedreg X0 LSL 32) *)
  w 0x39401420;         (* arm_LDRB W0 X1 (Immediate_Offset (word 5)) *)
  w 0xaa00a14a;         (* arm_ORR X10 X10 (Shiftedreg X0 LSL 40) *)
  w 0x39401820;         (* arm_LDRB W0 X1 (Immediate_Offset (word 6)) *)
  w 0xaa00c14a;         (* arm_ORR X10 X10 (Shiftedreg X0 LSL 48) *)
  w 0x39401c20;         (* arm_LDRB W0 X1 (Immediate_Offset (word 7)) *)
  w 0xaa00e14a;         (* arm_ORR X10 X10 (Shiftedreg X0 LSL 56) *)
  w 0x3940202b;         (* arm_LDRB W11 X1 (Immediate_Offset (word 8)) *)
  w 0x39402420;         (* arm_LDRB W0 X1 (Immediate_Offset (word 9)) *)
  w 0xaa00216b;         (* arm_ORR X11 X11 (Shiftedreg X0 LSL 8) *)
  w 0x39402820;         (* arm_LDRB W0 X1 (Immediate_Offset (word 10)) *)
  w 0xaa00416b;         (* arm_ORR X11 X11 (Shiftedreg X0 LSL 16) *)
  w 0x39402c20;         (* arm_LDRB W0 X1 (Immediate_Offset (word 11)) *)
  w 0xaa00616b;         (* arm_ORR X11 X11 (Shiftedreg X0 LSL 24) *)
  w 0x39403020;         (* arm_LDRB W0 X1 (Immediate_Offset (word 12)) *)
  w 0xaa00816b;         (* arm_ORR X11 X11 (Shiftedreg X0 LSL 32) *)
  w 0x39403420;         (* arm_LDRB W0 X1 (Immediate_Offset (word 13)) *)
  w 0xaa00a16b;         (* arm_ORR X11 X11 (Shiftedreg X0 LSL 40) *)
  w 0x39403820;         (* arm_LDRB W0 X1 (Immediate_Offset (word 14)) *)
  w 0xaa00c16b;         (* arm_ORR X11 X11 (Shiftedreg X0 LSL 48) *)
  w 0x39403c20;         (* arm_LDRB W0 X1 (Immediate_Offset (word 15)) *)
  w 0xaa00e16b;         (* arm_ORR X11 X11 (Shiftedreg X0 LSL 56) *)
  w 0xa9002fea;         (* arm_STP X10 X11 SP (Immediate_Offset (iword (&0))) *)
  w 0x3940402c;         (* arm_LDRB W12 X1 (Immediate_Offset (word 16)) *)
  w 0x39404420;         (* arm_LDRB W0 X1 (Immediate_Offset (word 17)) *)
  w 0xaa00218c;         (* arm_ORR X12 X12 (Shiftedreg X0 LSL 8) *)
  w 0x39404820;         (* arm_LDRB W0 X1 (Immediate_Offset (word 18)) *)
  w 0xaa00418c;         (* arm_ORR X12 X12 (Shiftedreg X0 LSL 16) *)
  w 0x39404c20;         (* arm_LDRB W0 X1 (Immediate_Offset (word 19)) *)
  w 0xaa00618c;         (* arm_ORR X12 X12 (Shiftedreg X0 LSL 24) *)
  w 0x39405020;         (* arm_LDRB W0 X1 (Immediate_Offset (word 20)) *)
  w 0xaa00818c;         (* arm_ORR X12 X12 (Shiftedreg X0 LSL 32) *)
  w 0x39405420;         (* arm_LDRB W0 X1 (Immediate_Offset (word 21)) *)
  w 0xaa00a18c;         (* arm_ORR X12 X12 (Shiftedreg X0 LSL 40) *)
  w 0x39405820;         (* arm_LDRB W0 X1 (Immediate_Offset (word 22)) *)
  w 0xaa00c18c;         (* arm_ORR X12 X12 (Shiftedreg X0 LSL 48) *)
  w 0x39405c20;         (* arm_LDRB W0 X1 (Immediate_Offset (word 23)) *)
  w 0xaa00e18c;         (* arm_ORR X12 X12 (Shiftedreg X0 LSL 56) *)
  w 0x3940602d;         (* arm_LDRB W13 X1 (Immediate_Offset (word 24)) *)
  w 0x39406420;         (* arm_LDRB W0 X1 (Immediate_Offset (word 25)) *)
  w 0xaa0021ad;         (* arm_ORR X13 X13 (Shiftedreg X0 LSL 8) *)
  w 0x39406820;         (* arm_LDRB W0 X1 (Immediate_Offset (word 26)) *)
  w 0xaa0041ad;         (* arm_ORR X13 X13 (Shiftedreg X0 LSL 16) *)
  w 0x39406c20;         (* arm_LDRB W0 X1 (Immediate_Offset (word 27)) *)
  w 0xaa0061ad;         (* arm_ORR X13 X13 (Shiftedreg X0 LSL 24) *)
  w 0x39407020;         (* arm_LDRB W0 X1 (Immediate_Offset (word 28)) *)
  w 0xaa0081ad;         (* arm_ORR X13 X13 (Shiftedreg X0 LSL 32) *)
  w 0x39407420;         (* arm_LDRB W0 X1 (Immediate_Offset (word 29)) *)
  w 0xaa00a1ad;         (* arm_ORR X13 X13 (Shiftedreg X0 LSL 40) *)
  w 0x39407820;         (* arm_LDRB W0 X1 (Immediate_Offset (word 30)) *)
  w 0xaa00c1ad;         (* arm_ORR X13 X13 (Shiftedreg X0 LSL 48) *)
  w 0x39407c20;         (* arm_LDRB W0 X1 (Immediate_Offset (word 31)) *)
  w 0xaa00e1ad;         (* arm_ORR X13 X13 (Shiftedreg X0 LSL 56) *)
  w 0x9240f5ad;         (* arm_AND X13 X13 (rvalue (word 4611686018427387903)) *)
  w 0xa90137ec;         (* arm_STP X12 X13 SP (Immediate_Offset (iword (&16))) *)
  w 0xf94003e0;         (* arm_LDR X0 SP (Immediate_Offset (word 0)) *)
  w 0xf27d001f;         (* arm_TST X0 (rvalue (word 8)) *)
  ADRP (mk_var("curve25519_x25519base_byte_alt_constant_data",`:num`),0,280,19);
  ADD_rri64 (mk_var("curve25519_x25519base_byte_alt_constant_data",`:num`),0,19,19);
  w 0xa9400660;         (* arm_LDP X0 X1 X19 (Immediate_Offset (iword (&0))) *)
  w 0xa9460e62;         (* arm_LDP X2 X3 X19 (Immediate_Offset (iword (&96))) *)
  w 0x9a820000;         (* arm_CSEL X0 X0 X2 Condition_EQ *)
  w 0x9a830021;         (* arm_CSEL X1 X1 X3 Condition_EQ *)
  w 0xa90807e0;         (* arm_STP X0 X1 SP (Immediate_Offset (iword (&128))) *)
  w 0xa9410660;         (* arm_LDP X0 X1 X19 (Immediate_Offset (iword (&16))) *)
  w 0xa9470e62;         (* arm_LDP X2 X3 X19 (Immediate_Offset (iword (&112))) *)
  w 0x9a820000;         (* arm_CSEL X0 X0 X2 Condition_EQ *)
  w 0x9a830021;         (* arm_CSEL X1 X1 X3 Condition_EQ *)
  w 0xa90907e0;         (* arm_STP X0 X1 SP (Immediate_Offset (iword (&144))) *)
  w 0xa9420660;         (* arm_LDP X0 X1 X19 (Immediate_Offset (iword (&32))) *)
  w 0xa9480e62;         (* arm_LDP X2 X3 X19 (Immediate_Offset (iword (&128))) *)
  w 0x9a820000;         (* arm_CSEL X0 X0 X2 Condition_EQ *)
  w 0x9a830021;         (* arm_CSEL X1 X1 X3 Condition_EQ *)
  w 0xa90a07e0;         (* arm_STP X0 X1 SP (Immediate_Offset (iword (&160))) *)
  w 0xa9430660;         (* arm_LDP X0 X1 X19 (Immediate_Offset (iword (&48))) *)
  w 0xa9490e62;         (* arm_LDP X2 X3 X19 (Immediate_Offset (iword (&144))) *)
  w 0x9a820000;         (* arm_CSEL X0 X0 X2 Condition_EQ *)
  w 0x9a830021;         (* arm_CSEL X1 X1 X3 Condition_EQ *)
  w 0xa90b07e0;         (* arm_STP X0 X1 SP (Immediate_Offset (iword (&176))) *)
  w 0xd2800020;         (* arm_MOV X0 (rvalue (word 1)) *)
  w 0xa90c7fe0;         (* arm_STP X0 XZR SP (Immediate_Offset (iword (&192))) *)
  w 0xa90d7fff;         (* arm_STP XZR XZR SP (Immediate_Offset (iword (&208))) *)
  w 0xa9440660;         (* arm_LDP X0 X1 X19 (Immediate_Offset (iword (&64))) *)
  w 0xa94a0e62;         (* arm_LDP X2 X3 X19 (Immediate_Offset (iword (&160))) *)
  w 0x9a820000;         (* arm_CSEL X0 X0 X2 Condition_EQ *)
  w 0x9a830021;         (* arm_CSEL X1 X1 X3 Condition_EQ *)
  w 0xa90e07e0;         (* arm_STP X0 X1 SP (Immediate_Offset (iword (&224))) *)
  w 0xa9450660;         (* arm_LDP X0 X1 X19 (Immediate_Offset (iword (&80))) *)
  w 0xa94b0e62;         (* arm_LDP X2 X3 X19 (Immediate_Offset (iword (&176))) *)
  w 0x9a820000;         (* arm_CSEL X0 X0 X2 Condition_EQ *)
  w 0x9a830021;         (* arm_CSEL X1 X1 X3 Condition_EQ *)
  w 0xa90f07e0;         (* arm_STP X0 X1 SP (Immediate_Offset (iword (&240))) *)
  w 0xd2800094;         (* arm_MOV X20 (rvalue (word 4)) *)
  w 0x91030273;         (* arm_ADD X19 X19 (rvalue (word 192)) *)
  w 0xaa1f03f5;         (* arm_MOV X21 XZR *)
  w 0xd346fe80;         (* arm_LSR X0 X20 6 *)
  w 0xf8607be2;         (* arm_LDR X2 SP (Shiftreg_Offset X0 3) *)
  w 0x9ad42442;         (* arm_LSRV X2 X2 X20 *)
  w 0x92400c42;         (* arm_AND X2 X2 (rvalue (word 15)) *)
  w 0x8b150056;         (* arm_ADD X22 X2 X21 *)
  w 0xf10026df;         (* arm_CMP X22 (rvalue (word 9)) *)
  w 0x9a9f37f5;         (* arm_CSET X21 Condition_CS *)
  w 0xd2800200;         (* arm_MOV X0 (rvalue (word 16)) *)
  w 0xcb160000;         (* arm_SUB X0 X0 X22 *)
  w 0xeb1f02bf;         (* arm_CMP X21 XZR *)
  w 0x9a961016;         (* arm_CSEL X22 X0 X22 Condition_NE *)
  w 0xd2800020;         (* arm_MOV X0 (rvalue (word 1)) *)
  w 0xaa1f03e1;         (* arm_MOV X1 XZR *)
  w 0xaa1f03e2;         (* arm_MOV X2 XZR *)
  w 0xaa1f03e3;         (* arm_MOV X3 XZR *)
  w 0xd2800024;         (* arm_MOV X4 (rvalue (word 1)) *)
  w 0xaa1f03e5;         (* arm_MOV X5 XZR *)
  w 0xaa1f03e6;         (* arm_MOV X6 XZR *)
  w 0xaa1f03e7;         (* arm_MOV X7 XZR *)
  w 0xaa1f03e8;         (* arm_MOV X8 XZR *)
  w 0xaa1f03e9;         (* arm_MOV X9 XZR *)
  w 0xaa1f03ea;         (* arm_MOV X10 XZR *)
  w 0xaa1f03eb;         (* arm_MOV X11 XZR *)
  w 0xf10006df;         (* arm_CMP X22 (rvalue (word 1)) *)
  w 0xa940366c;         (* arm_LDP X12 X13 X19 (Immediate_Offset (iword (&0))) *)
  w 0x9a8c1000;         (* arm_CSEL X0 X0 X12 Condition_NE *)
  w 0x9a8d1021;         (* arm_CSEL X1 X1 X13 Condition_NE *)
  w 0xa941366c;         (* arm_LDP X12 X13 X19 (Immediate_Offset (iword (&16))) *)
  w 0x9a8c1042;         (* arm_CSEL X2 X2 X12 Condition_NE *)
  w 0x9a8d1063;         (* arm_CSEL X3 X3 X13 Condition_NE *)
  w 0xa942366c;         (* arm_LDP X12 X13 X19 (Immediate_Offset (iword (&32))) *)
  w 0x9a8c1084;         (* arm_CSEL X4 X4 X12 Condition_NE *)
  w 0x9a8d10a5;         (* arm_CSEL X5 X5 X13 Condition_NE *)
  w 0xa943366c;         (* arm_LDP X12 X13 X19 (Immediate_Offset (iword (&48))) *)
  w 0x9a8c10c6;         (* arm_CSEL X6 X6 X12 Condition_NE *)
  w 0x9a8d10e7;         (* arm_CSEL X7 X7 X13 Condition_NE *)
  w 0xa944366c;         (* arm_LDP X12 X13 X19 (Immediate_Offset (iword (&64))) *)
  w 0x9a8c1108;         (* arm_CSEL X8 X8 X12 Condition_NE *)
  w 0x9a8d1129;         (* arm_CSEL X9 X9 X13 Condition_NE *)
  w 0xa945366c;         (* arm_LDP X12 X13 X19 (Immediate_Offset (iword (&80))) *)
  w 0x9a8c114a;         (* arm_CSEL X10 X10 X12 Condition_NE *)
  w 0x9a8d116b;         (* arm_CSEL X11 X11 X13 Condition_NE *)
  w 0x91018273;         (* arm_ADD X19 X19 (rvalue (word 96)) *)
  w 0xf1000adf;         (* arm_CMP X22 (rvalue (word 2)) *)
  w 0xa940366c;         (* arm_LDP X12 X13 X19 (Immediate_Offset (iword (&0))) *)
  w 0x9a8c1000;         (* arm_CSEL X0 X0 X12 Condition_NE *)
  w 0x9a8d1021;         (* arm_CSEL X1 X1 X13 Condition_NE *)
  w 0xa941366c;         (* arm_LDP X12 X13 X19 (Immediate_Offset (iword (&16))) *)
  w 0x9a8c1042;         (* arm_CSEL X2 X2 X12 Condition_NE *)
  w 0x9a8d1063;         (* arm_CSEL X3 X3 X13 Condition_NE *)
  w 0xa942366c;         (* arm_LDP X12 X13 X19 (Immediate_Offset (iword (&32))) *)
  w 0x9a8c1084;         (* arm_CSEL X4 X4 X12 Condition_NE *)
  w 0x9a8d10a5;         (* arm_CSEL X5 X5 X13 Condition_NE *)
  w 0xa943366c;         (* arm_LDP X12 X13 X19 (Immediate_Offset (iword (&48))) *)
  w 0x9a8c10c6;         (* arm_CSEL X6 X6 X12 Condition_NE *)
  w 0x9a8d10e7;         (* arm_CSEL X7 X7 X13 Condition_NE *)
  w 0xa944366c;         (* arm_LDP X12 X13 X19 (Immediate_Offset (iword (&64))) *)
  w 0x9a8c1108;         (* arm_CSEL X8 X8 X12 Condition_NE *)
  w 0x9a8d1129;         (* arm_CSEL X9 X9 X13 Condition_NE *)
  w 0xa945366c;         (* arm_LDP X12 X13 X19 (Immediate_Offset (iword (&80))) *)
  w 0x9a8c114a;         (* arm_CSEL X10 X10 X12 Condition_NE *)
  w 0x9a8d116b;         (* arm_CSEL X11 X11 X13 Condition_NE *)
  w 0x91018273;         (* arm_ADD X19 X19 (rvalue (word 96)) *)
  w 0xf1000edf;         (* arm_CMP X22 (rvalue (word 3)) *)
  w 0xa940366c;         (* arm_LDP X12 X13 X19 (Immediate_Offset (iword (&0))) *)
  w 0x9a8c1000;         (* arm_CSEL X0 X0 X12 Condition_NE *)
  w 0x9a8d1021;         (* arm_CSEL X1 X1 X13 Condition_NE *)
  w 0xa941366c;         (* arm_LDP X12 X13 X19 (Immediate_Offset (iword (&16))) *)
  w 0x9a8c1042;         (* arm_CSEL X2 X2 X12 Condition_NE *)
  w 0x9a8d1063;         (* arm_CSEL X3 X3 X13 Condition_NE *)
  w 0xa942366c;         (* arm_LDP X12 X13 X19 (Immediate_Offset (iword (&32))) *)
  w 0x9a8c1084;         (* arm_CSEL X4 X4 X12 Condition_NE *)
  w 0x9a8d10a5;         (* arm_CSEL X5 X5 X13 Condition_NE *)
  w 0xa943366c;         (* arm_LDP X12 X13 X19 (Immediate_Offset (iword (&48))) *)
  w 0x9a8c10c6;         (* arm_CSEL X6 X6 X12 Condition_NE *)
  w 0x9a8d10e7;         (* arm_CSEL X7 X7 X13 Condition_NE *)
  w 0xa944366c;         (* arm_LDP X12 X13 X19 (Immediate_Offset (iword (&64))) *)
  w 0x9a8c1108;         (* arm_CSEL X8 X8 X12 Condition_NE *)
  w 0x9a8d1129;         (* arm_CSEL X9 X9 X13 Condition_NE *)
  w 0xa945366c;         (* arm_LDP X12 X13 X19 (Immediate_Offset (iword (&80))) *)
  w 0x9a8c114a;         (* arm_CSEL X10 X10 X12 Condition_NE *)
  w 0x9a8d116b;         (* arm_CSEL X11 X11 X13 Condition_NE *)
  w 0x91018273;         (* arm_ADD X19 X19 (rvalue (word 96)) *)
  w 0xf10012df;         (* arm_CMP X22 (rvalue (word 4)) *)
  w 0xa940366c;         (* arm_LDP X12 X13 X19 (Immediate_Offset (iword (&0))) *)
  w 0x9a8c1000;         (* arm_CSEL X0 X0 X12 Condition_NE *)
  w 0x9a8d1021;         (* arm_CSEL X1 X1 X13 Condition_NE *)
  w 0xa941366c;         (* arm_LDP X12 X13 X19 (Immediate_Offset (iword (&16))) *)
  w 0x9a8c1042;         (* arm_CSEL X2 X2 X12 Condition_NE *)
  w 0x9a8d1063;         (* arm_CSEL X3 X3 X13 Condition_NE *)
  w 0xa942366c;         (* arm_LDP X12 X13 X19 (Immediate_Offset (iword (&32))) *)
  w 0x9a8c1084;         (* arm_CSEL X4 X4 X12 Condition_NE *)
  w 0x9a8d10a5;         (* arm_CSEL X5 X5 X13 Condition_NE *)
  w 0xa943366c;         (* arm_LDP X12 X13 X19 (Immediate_Offset (iword (&48))) *)
  w 0x9a8c10c6;         (* arm_CSEL X6 X6 X12 Condition_NE *)
  w 0x9a8d10e7;         (* arm_CSEL X7 X7 X13 Condition_NE *)
  w 0xa944366c;         (* arm_LDP X12 X13 X19 (Immediate_Offset (iword (&64))) *)
  w 0x9a8c1108;         (* arm_CSEL X8 X8 X12 Condition_NE *)
  w 0x9a8d1129;         (* arm_CSEL X9 X9 X13 Condition_NE *)
  w 0xa945366c;         (* arm_LDP X12 X13 X19 (Immediate_Offset (iword (&80))) *)
  w 0x9a8c114a;         (* arm_CSEL X10 X10 X12 Condition_NE *)
  w 0x9a8d116b;         (* arm_CSEL X11 X11 X13 Condition_NE *)
  w 0x91018273;         (* arm_ADD X19 X19 (rvalue (word 96)) *)
  w 0xf10016df;         (* arm_CMP X22 (rvalue (word 5)) *)
  w 0xa940366c;         (* arm_LDP X12 X13 X19 (Immediate_Offset (iword (&0))) *)
  w 0x9a8c1000;         (* arm_CSEL X0 X0 X12 Condition_NE *)
  w 0x9a8d1021;         (* arm_CSEL X1 X1 X13 Condition_NE *)
  w 0xa941366c;         (* arm_LDP X12 X13 X19 (Immediate_Offset (iword (&16))) *)
  w 0x9a8c1042;         (* arm_CSEL X2 X2 X12 Condition_NE *)
  w 0x9a8d1063;         (* arm_CSEL X3 X3 X13 Condition_NE *)
  w 0xa942366c;         (* arm_LDP X12 X13 X19 (Immediate_Offset (iword (&32))) *)
  w 0x9a8c1084;         (* arm_CSEL X4 X4 X12 Condition_NE *)
  w 0x9a8d10a5;         (* arm_CSEL X5 X5 X13 Condition_NE *)
  w 0xa943366c;         (* arm_LDP X12 X13 X19 (Immediate_Offset (iword (&48))) *)
  w 0x9a8c10c6;         (* arm_CSEL X6 X6 X12 Condition_NE *)
  w 0x9a8d10e7;         (* arm_CSEL X7 X7 X13 Condition_NE *)
  w 0xa944366c;         (* arm_LDP X12 X13 X19 (Immediate_Offset (iword (&64))) *)
  w 0x9a8c1108;         (* arm_CSEL X8 X8 X12 Condition_NE *)
  w 0x9a8d1129;         (* arm_CSEL X9 X9 X13 Condition_NE *)
  w 0xa945366c;         (* arm_LDP X12 X13 X19 (Immediate_Offset (iword (&80))) *)
  w 0x9a8c114a;         (* arm_CSEL X10 X10 X12 Condition_NE *)
  w 0x9a8d116b;         (* arm_CSEL X11 X11 X13 Condition_NE *)
  w 0x91018273;         (* arm_ADD X19 X19 (rvalue (word 96)) *)
  w 0xf1001adf;         (* arm_CMP X22 (rvalue (word 6)) *)
  w 0xa940366c;         (* arm_LDP X12 X13 X19 (Immediate_Offset (iword (&0))) *)
  w 0x9a8c1000;         (* arm_CSEL X0 X0 X12 Condition_NE *)
  w 0x9a8d1021;         (* arm_CSEL X1 X1 X13 Condition_NE *)
  w 0xa941366c;         (* arm_LDP X12 X13 X19 (Immediate_Offset (iword (&16))) *)
  w 0x9a8c1042;         (* arm_CSEL X2 X2 X12 Condition_NE *)
  w 0x9a8d1063;         (* arm_CSEL X3 X3 X13 Condition_NE *)
  w 0xa942366c;         (* arm_LDP X12 X13 X19 (Immediate_Offset (iword (&32))) *)
  w 0x9a8c1084;         (* arm_CSEL X4 X4 X12 Condition_NE *)
  w 0x9a8d10a5;         (* arm_CSEL X5 X5 X13 Condition_NE *)
  w 0xa943366c;         (* arm_LDP X12 X13 X19 (Immediate_Offset (iword (&48))) *)
  w 0x9a8c10c6;         (* arm_CSEL X6 X6 X12 Condition_NE *)
  w 0x9a8d10e7;         (* arm_CSEL X7 X7 X13 Condition_NE *)
  w 0xa944366c;         (* arm_LDP X12 X13 X19 (Immediate_Offset (iword (&64))) *)
  w 0x9a8c1108;         (* arm_CSEL X8 X8 X12 Condition_NE *)
  w 0x9a8d1129;         (* arm_CSEL X9 X9 X13 Condition_NE *)
  w 0xa945366c;         (* arm_LDP X12 X13 X19 (Immediate_Offset (iword (&80))) *)
  w 0x9a8c114a;         (* arm_CSEL X10 X10 X12 Condition_NE *)
  w 0x9a8d116b;         (* arm_CSEL X11 X11 X13 Condition_NE *)
  w 0x91018273;         (* arm_ADD X19 X19 (rvalue (word 96)) *)
  w 0xf1001edf;         (* arm_CMP X22 (rvalue (word 7)) *)
  w 0xa940366c;         (* arm_LDP X12 X13 X19 (Immediate_Offset (iword (&0))) *)
  w 0x9a8c1000;         (* arm_CSEL X0 X0 X12 Condition_NE *)
  w 0x9a8d1021;         (* arm_CSEL X1 X1 X13 Condition_NE *)
  w 0xa941366c;         (* arm_LDP X12 X13 X19 (Immediate_Offset (iword (&16))) *)
  w 0x9a8c1042;         (* arm_CSEL X2 X2 X12 Condition_NE *)
  w 0x9a8d1063;         (* arm_CSEL X3 X3 X13 Condition_NE *)
  w 0xa942366c;         (* arm_LDP X12 X13 X19 (Immediate_Offset (iword (&32))) *)
  w 0x9a8c1084;         (* arm_CSEL X4 X4 X12 Condition_NE *)
  w 0x9a8d10a5;         (* arm_CSEL X5 X5 X13 Condition_NE *)
  w 0xa943366c;         (* arm_LDP X12 X13 X19 (Immediate_Offset (iword (&48))) *)
  w 0x9a8c10c6;         (* arm_CSEL X6 X6 X12 Condition_NE *)
  w 0x9a8d10e7;         (* arm_CSEL X7 X7 X13 Condition_NE *)
  w 0xa944366c;         (* arm_LDP X12 X13 X19 (Immediate_Offset (iword (&64))) *)
  w 0x9a8c1108;         (* arm_CSEL X8 X8 X12 Condition_NE *)
  w 0x9a8d1129;         (* arm_CSEL X9 X9 X13 Condition_NE *)
  w 0xa945366c;         (* arm_LDP X12 X13 X19 (Immediate_Offset (iword (&80))) *)
  w 0x9a8c114a;         (* arm_CSEL X10 X10 X12 Condition_NE *)
  w 0x9a8d116b;         (* arm_CSEL X11 X11 X13 Condition_NE *)
  w 0x91018273;         (* arm_ADD X19 X19 (rvalue (word 96)) *)
  w 0xf10022df;         (* arm_CMP X22 (rvalue (word 8)) *)
  w 0xa940366c;         (* arm_LDP X12 X13 X19 (Immediate_Offset (iword (&0))) *)
  w 0x9a8c1000;         (* arm_CSEL X0 X0 X12 Condition_NE *)
  w 0x9a8d1021;         (* arm_CSEL X1 X1 X13 Condition_NE *)
  w 0xa941366c;         (* arm_LDP X12 X13 X19 (Immediate_Offset (iword (&16))) *)
  w 0x9a8c1042;         (* arm_CSEL X2 X2 X12 Condition_NE *)
  w 0x9a8d1063;         (* arm_CSEL X3 X3 X13 Condition_NE *)
  w 0xa942366c;         (* arm_LDP X12 X13 X19 (Immediate_Offset (iword (&32))) *)
  w 0x9a8c1084;         (* arm_CSEL X4 X4 X12 Condition_NE *)
  w 0x9a8d10a5;         (* arm_CSEL X5 X5 X13 Condition_NE *)
  w 0xa943366c;         (* arm_LDP X12 X13 X19 (Immediate_Offset (iword (&48))) *)
  w 0x9a8c10c6;         (* arm_CSEL X6 X6 X12 Condition_NE *)
  w 0x9a8d10e7;         (* arm_CSEL X7 X7 X13 Condition_NE *)
  w 0xa944366c;         (* arm_LDP X12 X13 X19 (Immediate_Offset (iword (&64))) *)
  w 0x9a8c1108;         (* arm_CSEL X8 X8 X12 Condition_NE *)
  w 0x9a8d1129;         (* arm_CSEL X9 X9 X13 Condition_NE *)
  w 0xa945366c;         (* arm_LDP X12 X13 X19 (Immediate_Offset (iword (&80))) *)
  w 0x9a8c114a;         (* arm_CSEL X10 X10 X12 Condition_NE *)
  w 0x9a8d116b;         (* arm_CSEL X11 X11 X13 Condition_NE *)
  w 0x91018273;         (* arm_ADD X19 X19 (rvalue (word 96)) *)
  w 0xf10002bf;         (* arm_CMP X21 (rvalue (word 0)) *)
  w 0x9a84000c;         (* arm_CSEL X12 X0 X4 Condition_EQ *)
  w 0x9a85002d;         (* arm_CSEL X13 X1 X5 Condition_EQ *)
  w 0x9a86004e;         (* arm_CSEL X14 X2 X6 Condition_EQ *)
  w 0x9a87006f;         (* arm_CSEL X15 X3 X7 Condition_EQ *)
  w 0xa90237ec;         (* arm_STP X12 X13 SP (Immediate_Offset (iword (&32))) *)
  w 0xa9033fee;         (* arm_STP X14 X15 SP (Immediate_Offset (iword (&48))) *)
  w 0x9a84100c;         (* arm_CSEL X12 X0 X4 Condition_NE *)
  w 0x9a85102d;         (* arm_CSEL X13 X1 X5 Condition_NE *)
  w 0x9a86104e;         (* arm_CSEL X14 X2 X6 Condition_NE *)
  w 0x9a87106f;         (* arm_CSEL X15 X3 X7 Condition_NE *)
  w 0xa90437ec;         (* arm_STP X12 X13 SP (Immediate_Offset (iword (&64))) *)
  w 0xa9053fee;         (* arm_STP X14 X15 SP (Immediate_Offset (iword (&80))) *)
  w 0x92800240;         (* arm_MOVN X0 (word 18) 0 *)
  w 0xeb080000;         (* arm_SUBS X0 X0 X8 *)
  w 0x92800002;         (* arm_MOVN X2 (word 0) 0 *)
  w 0xfa090041;         (* arm_SBCS X1 X2 X9 *)
  w 0xfa0a0042;         (* arm_SBCS X2 X2 X10 *)
  w 0x92f00003;         (* arm_MOVN X3 (word 32768) 48 *)
  w 0xda0b0063;         (* arm_SBC X3 X3 X11 *)
  w 0xeb1f02df;         (* arm_CMP X22 XZR *)
  w 0xfa5f12a4;         (* arm_CCMP X21 XZR (word 4) Condition_NE *)
  w 0x9a881000;         (* arm_CSEL X0 X0 X8 Condition_NE *)
  w 0x9a891021;         (* arm_CSEL X1 X1 X9 Condition_NE *)
  w 0xa90607e0;         (* arm_STP X0 X1 SP (Immediate_Offset (iword (&96))) *)
  w 0x9a8a1042;         (* arm_CSEL X2 X2 X10 Condition_NE *)
  w 0x9a8b1063;         (* arm_CSEL X3 X3 X11 Condition_NE *)
  w 0xa9070fe2;         (* arm_STP X2 X3 SP (Immediate_Offset (iword (&112))) *)
  w 0xa94c13e3;         (* arm_LDP X3 X4 SP (Immediate_Offset (iword (&192))) *)
  w 0xab030063;         (* arm_ADDS X3 X3 X3 *)
  w 0xba040084;         (* arm_ADCS X4 X4 X4 *)
  w 0xa94d1be5;         (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&208))) *)
  w 0xba0500a5;         (* arm_ADCS X5 X5 X5 *)
  w 0xba0600c6;         (* arm_ADCS X6 X6 X6 *)
  w 0xd28004c9;         (* arm_MOV X9 (rvalue (word 38)) *)
  w 0x9a9f2129;         (* arm_CSEL X9 X9 XZR Condition_CS *)
  w 0xab090063;         (* arm_ADDS X3 X3 X9 *)
  w 0xba1f0084;         (* arm_ADCS X4 X4 XZR *)
  w 0xba1f00a5;         (* arm_ADCS X5 X5 XZR *)
  w 0x9a1f00c6;         (* arm_ADC X6 X6 XZR *)
  w 0xa91013e3;         (* arm_STP X3 X4 SP (Immediate_Offset (iword (&256))) *)
  w 0xa9111be5;         (* arm_STP X5 X6 SP (Immediate_Offset (iword (&272))) *)
  w 0xa94a1be5;         (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&160))) *)
  w 0xa9480fe4;         (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&128))) *)
  w 0xeb0400a5;         (* arm_SUBS X5 X5 X4 *)
  w 0xfa0300c6;         (* arm_SBCS X6 X6 X3 *)
  w 0xa94b23e7;         (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&176))) *)
  w 0xa9490fe4;         (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&144))) *)
  w 0xfa0400e7;         (* arm_SBCS X7 X7 X4 *)
  w 0xfa030108;         (* arm_SBCS X8 X8 X3 *)
  w 0xd28004c4;         (* arm_MOV X4 (rvalue (word 38)) *)
  w 0x9a9f3083;         (* arm_CSEL X3 X4 XZR Condition_CC *)
  w 0xeb0300a5;         (* arm_SUBS X5 X5 X3 *)
  w 0xfa1f00c6;         (* arm_SBCS X6 X6 XZR *)
  w 0xfa1f00e7;         (* arm_SBCS X7 X7 XZR *)
  w 0xda1f0108;         (* arm_SBC X8 X8 XZR *)
  w 0xa9121be5;         (* arm_STP X5 X6 SP (Immediate_Offset (iword (&288))) *)
  w 0xa91323e7;         (* arm_STP X7 X8 SP (Immediate_Offset (iword (&304))) *)
  w 0xa94a13e3;         (* arm_LDP X3 X4 SP (Immediate_Offset (iword (&160))) *)
  w 0xa94823e7;         (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&128))) *)
  w 0xab070063;         (* arm_ADDS X3 X3 X7 *)
  w 0xba080084;         (* arm_ADCS X4 X4 X8 *)
  w 0xa94b1be5;         (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&176))) *)
  w 0xa94923e7;         (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&144))) *)
  w 0xba0700a5;         (* arm_ADCS X5 X5 X7 *)
  w 0xba0800c6;         (* arm_ADCS X6 X6 X8 *)
  w 0xd28004c9;         (* arm_MOV X9 (rvalue (word 38)) *)
  w 0x9a9f2129;         (* arm_CSEL X9 X9 XZR Condition_CS *)
  w 0xab090063;         (* arm_ADDS X3 X3 X9 *)
  w 0xba1f0084;         (* arm_ADCS X4 X4 XZR *)
  w 0xba1f00a5;         (* arm_ADCS X5 X5 XZR *)
  w 0x9a1f00c6;         (* arm_ADC X6 X6 XZR *)
  w 0xa91413e3;         (* arm_STP X3 X4 SP (Immediate_Offset (iword (&320))) *)
  w 0xa9151be5;         (* arm_STP X5 X6 SP (Immediate_Offset (iword (&336))) *)
  w 0xa94e13e3;         (* arm_LDP X3 X4 SP (Immediate_Offset (iword (&224))) *)
  w 0xa94623e7;         (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&96))) *)
  w 0x9b077c6c;         (* arm_MUL X12 X3 X7 *)
  w 0x9bc77c6d;         (* arm_UMULH X13 X3 X7 *)
  w 0x9b087c6b;         (* arm_MUL X11 X3 X8 *)
  w 0x9bc87c6e;         (* arm_UMULH X14 X3 X8 *)
  w 0xab0b01ad;         (* arm_ADDS X13 X13 X11 *)
  w 0xa9472be9;         (* arm_LDP X9 X10 SP (Immediate_Offset (iword (&112))) *)
  w 0x9b097c6b;         (* arm_MUL X11 X3 X9 *)
  w 0x9bc97c6f;         (* arm_UMULH X15 X3 X9 *)
  w 0xba0b01ce;         (* arm_ADCS X14 X14 X11 *)
  w 0x9b0a7c6b;         (* arm_MUL X11 X3 X10 *)
  w 0x9bca7c70;         (* arm_UMULH X16 X3 X10 *)
  w 0xba0b01ef;         (* arm_ADCS X15 X15 X11 *)
  w 0x9a1f0210;         (* arm_ADC X16 X16 XZR *)
  w 0xa94f1be5;         (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&240))) *)
  w 0x9b077c8b;         (* arm_MUL X11 X4 X7 *)
  w 0xab0b01ad;         (* arm_ADDS X13 X13 X11 *)
  w 0x9b087c8b;         (* arm_MUL X11 X4 X8 *)
  w 0xba0b01ce;         (* arm_ADCS X14 X14 X11 *)
  w 0x9b097c8b;         (* arm_MUL X11 X4 X9 *)
  w 0xba0b01ef;         (* arm_ADCS X15 X15 X11 *)
  w 0x9b0a7c8b;         (* arm_MUL X11 X4 X10 *)
  w 0xba0b0210;         (* arm_ADCS X16 X16 X11 *)
  w 0x9bca7c83;         (* arm_UMULH X3 X4 X10 *)
  w 0x9a1f0063;         (* arm_ADC X3 X3 XZR *)
  w 0x9bc77c8b;         (* arm_UMULH X11 X4 X7 *)
  w 0xab0b01ce;         (* arm_ADDS X14 X14 X11 *)
  w 0x9bc87c8b;         (* arm_UMULH X11 X4 X8 *)
  w 0xba0b01ef;         (* arm_ADCS X15 X15 X11 *)
  w 0x9bc97c8b;         (* arm_UMULH X11 X4 X9 *)
  w 0xba0b0210;         (* arm_ADCS X16 X16 X11 *)
  w 0x9a1f0063;         (* arm_ADC X3 X3 XZR *)
  w 0x9b077cab;         (* arm_MUL X11 X5 X7 *)
  w 0xab0b01ce;         (* arm_ADDS X14 X14 X11 *)
  w 0x9b087cab;         (* arm_MUL X11 X5 X8 *)
  w 0xba0b01ef;         (* arm_ADCS X15 X15 X11 *)
  w 0x9b097cab;         (* arm_MUL X11 X5 X9 *)
  w 0xba0b0210;         (* arm_ADCS X16 X16 X11 *)
  w 0x9b0a7cab;         (* arm_MUL X11 X5 X10 *)
  w 0xba0b0063;         (* arm_ADCS X3 X3 X11 *)
  w 0x9bca7ca4;         (* arm_UMULH X4 X5 X10 *)
  w 0x9a1f0084;         (* arm_ADC X4 X4 XZR *)
  w 0x9bc77cab;         (* arm_UMULH X11 X5 X7 *)
  w 0xab0b01ef;         (* arm_ADDS X15 X15 X11 *)
  w 0x9bc87cab;         (* arm_UMULH X11 X5 X8 *)
  w 0xba0b0210;         (* arm_ADCS X16 X16 X11 *)
  w 0x9bc97cab;         (* arm_UMULH X11 X5 X9 *)
  w 0xba0b0063;         (* arm_ADCS X3 X3 X11 *)
  w 0x9a1f0084;         (* arm_ADC X4 X4 XZR *)
  w 0x9b077ccb;         (* arm_MUL X11 X6 X7 *)
  w 0xab0b01ef;         (* arm_ADDS X15 X15 X11 *)
  w 0x9b087ccb;         (* arm_MUL X11 X6 X8 *)
  w 0xba0b0210;         (* arm_ADCS X16 X16 X11 *)
  w 0x9b097ccb;         (* arm_MUL X11 X6 X9 *)
  w 0xba0b0063;         (* arm_ADCS X3 X3 X11 *)
  w 0x9b0a7ccb;         (* arm_MUL X11 X6 X10 *)
  w 0xba0b0084;         (* arm_ADCS X4 X4 X11 *)
  w 0x9bca7cc5;         (* arm_UMULH X5 X6 X10 *)
  w 0x9a1f00a5;         (* arm_ADC X5 X5 XZR *)
  w 0x9bc77ccb;         (* arm_UMULH X11 X6 X7 *)
  w 0xab0b0210;         (* arm_ADDS X16 X16 X11 *)
  w 0x9bc87ccb;         (* arm_UMULH X11 X6 X8 *)
  w 0xba0b0063;         (* arm_ADCS X3 X3 X11 *)
  w 0x9bc97ccb;         (* arm_UMULH X11 X6 X9 *)
  w 0xba0b0084;         (* arm_ADCS X4 X4 X11 *)
  w 0x9a1f00a5;         (* arm_ADC X5 X5 XZR *)
  w 0xd28004c7;         (* arm_MOV X7 (rvalue (word 38)) *)
  w 0x9b107ceb;         (* arm_MUL X11 X7 X16 *)
  w 0x9bd07ce9;         (* arm_UMULH X9 X7 X16 *)
  w 0xab0b018c;         (* arm_ADDS X12 X12 X11 *)
  w 0x9b037ceb;         (* arm_MUL X11 X7 X3 *)
  w 0x9bc37ce3;         (* arm_UMULH X3 X7 X3 *)
  w 0xba0b01ad;         (* arm_ADCS X13 X13 X11 *)
  w 0x9b047ceb;         (* arm_MUL X11 X7 X4 *)
  w 0x9bc47ce4;         (* arm_UMULH X4 X7 X4 *)
  w 0xba0b01ce;         (* arm_ADCS X14 X14 X11 *)
  w 0x9b057ceb;         (* arm_MUL X11 X7 X5 *)
  w 0x9bc57ce5;         (* arm_UMULH X5 X7 X5 *)
  w 0xba0b01ef;         (* arm_ADCS X15 X15 X11 *)
  w 0x9a9f37f0;         (* arm_CSET X16 Condition_CS *)
  w 0xab0401ef;         (* arm_ADDS X15 X15 X4 *)
  w 0x9a050210;         (* arm_ADC X16 X16 X5 *)
  w 0xab0f01ff;         (* arm_CMN X15 X15 *)
  w 0x9240f9ef;         (* arm_AND X15 X15 (rvalue (word 9223372036854775807)) *)
  w 0x9a100208;         (* arm_ADC X8 X16 X16 *)
  w 0xd2800267;         (* arm_MOV X7 (rvalue (word 19)) *)
  w 0x9b087ceb;         (* arm_MUL X11 X7 X8 *)
  w 0xab0b018c;         (* arm_ADDS X12 X12 X11 *)
  w 0xba0901ad;         (* arm_ADCS X13 X13 X9 *)
  w 0xba0301ce;         (* arm_ADCS X14 X14 X3 *)
  w 0x9a1f01ef;         (* arm_ADC X15 X15 XZR *)
  w 0xa91637ec;         (* arm_STP X12 X13 SP (Immediate_Offset (iword (&352))) *)
  w 0xa9173fee;         (* arm_STP X14 X15 SP (Immediate_Offset (iword (&368))) *)
  w 0xa95213e3;         (* arm_LDP X3 X4 SP (Immediate_Offset (iword (&288))) *)
  w 0xa94223e7;         (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&32))) *)
  w 0x9b077c6c;         (* arm_MUL X12 X3 X7 *)
  w 0x9bc77c6d;         (* arm_UMULH X13 X3 X7 *)
  w 0x9b087c6b;         (* arm_MUL X11 X3 X8 *)
  w 0x9bc87c6e;         (* arm_UMULH X14 X3 X8 *)
  w 0xab0b01ad;         (* arm_ADDS X13 X13 X11 *)
  w 0xa9432be9;         (* arm_LDP X9 X10 SP (Immediate_Offset (iword (&48))) *)
  w 0x9b097c6b;         (* arm_MUL X11 X3 X9 *)
  w 0x9bc97c6f;         (* arm_UMULH X15 X3 X9 *)
  w 0xba0b01ce;         (* arm_ADCS X14 X14 X11 *)
  w 0x9b0a7c6b;         (* arm_MUL X11 X3 X10 *)
  w 0x9bca7c70;         (* arm_UMULH X16 X3 X10 *)
  w 0xba0b01ef;         (* arm_ADCS X15 X15 X11 *)
  w 0x9a1f0210;         (* arm_ADC X16 X16 XZR *)
  w 0xa9531be5;         (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&304))) *)
  w 0x9b077c8b;         (* arm_MUL X11 X4 X7 *)
  w 0xab0b01ad;         (* arm_ADDS X13 X13 X11 *)
  w 0x9b087c8b;         (* arm_MUL X11 X4 X8 *)
  w 0xba0b01ce;         (* arm_ADCS X14 X14 X11 *)
  w 0x9b097c8b;         (* arm_MUL X11 X4 X9 *)
  w 0xba0b01ef;         (* arm_ADCS X15 X15 X11 *)
  w 0x9b0a7c8b;         (* arm_MUL X11 X4 X10 *)
  w 0xba0b0210;         (* arm_ADCS X16 X16 X11 *)
  w 0x9bca7c83;         (* arm_UMULH X3 X4 X10 *)
  w 0x9a1f0063;         (* arm_ADC X3 X3 XZR *)
  w 0x9bc77c8b;         (* arm_UMULH X11 X4 X7 *)
  w 0xab0b01ce;         (* arm_ADDS X14 X14 X11 *)
  w 0x9bc87c8b;         (* arm_UMULH X11 X4 X8 *)
  w 0xba0b01ef;         (* arm_ADCS X15 X15 X11 *)
  w 0x9bc97c8b;         (* arm_UMULH X11 X4 X9 *)
  w 0xba0b0210;         (* arm_ADCS X16 X16 X11 *)
  w 0x9a1f0063;         (* arm_ADC X3 X3 XZR *)
  w 0x9b077cab;         (* arm_MUL X11 X5 X7 *)
  w 0xab0b01ce;         (* arm_ADDS X14 X14 X11 *)
  w 0x9b087cab;         (* arm_MUL X11 X5 X8 *)
  w 0xba0b01ef;         (* arm_ADCS X15 X15 X11 *)
  w 0x9b097cab;         (* arm_MUL X11 X5 X9 *)
  w 0xba0b0210;         (* arm_ADCS X16 X16 X11 *)
  w 0x9b0a7cab;         (* arm_MUL X11 X5 X10 *)
  w 0xba0b0063;         (* arm_ADCS X3 X3 X11 *)
  w 0x9bca7ca4;         (* arm_UMULH X4 X5 X10 *)
  w 0x9a1f0084;         (* arm_ADC X4 X4 XZR *)
  w 0x9bc77cab;         (* arm_UMULH X11 X5 X7 *)
  w 0xab0b01ef;         (* arm_ADDS X15 X15 X11 *)
  w 0x9bc87cab;         (* arm_UMULH X11 X5 X8 *)
  w 0xba0b0210;         (* arm_ADCS X16 X16 X11 *)
  w 0x9bc97cab;         (* arm_UMULH X11 X5 X9 *)
  w 0xba0b0063;         (* arm_ADCS X3 X3 X11 *)
  w 0x9a1f0084;         (* arm_ADC X4 X4 XZR *)
  w 0x9b077ccb;         (* arm_MUL X11 X6 X7 *)
  w 0xab0b01ef;         (* arm_ADDS X15 X15 X11 *)
  w 0x9b087ccb;         (* arm_MUL X11 X6 X8 *)
  w 0xba0b0210;         (* arm_ADCS X16 X16 X11 *)
  w 0x9b097ccb;         (* arm_MUL X11 X6 X9 *)
  w 0xba0b0063;         (* arm_ADCS X3 X3 X11 *)
  w 0x9b0a7ccb;         (* arm_MUL X11 X6 X10 *)
  w 0xba0b0084;         (* arm_ADCS X4 X4 X11 *)
  w 0x9bca7cc5;         (* arm_UMULH X5 X6 X10 *)
  w 0x9a1f00a5;         (* arm_ADC X5 X5 XZR *)
  w 0x9bc77ccb;         (* arm_UMULH X11 X6 X7 *)
  w 0xab0b0210;         (* arm_ADDS X16 X16 X11 *)
  w 0x9bc87ccb;         (* arm_UMULH X11 X6 X8 *)
  w 0xba0b0063;         (* arm_ADCS X3 X3 X11 *)
  w 0x9bc97ccb;         (* arm_UMULH X11 X6 X9 *)
  w 0xba0b0084;         (* arm_ADCS X4 X4 X11 *)
  w 0x9a1f00a5;         (* arm_ADC X5 X5 XZR *)
  w 0xd28004c7;         (* arm_MOV X7 (rvalue (word 38)) *)
  w 0x9b107ceb;         (* arm_MUL X11 X7 X16 *)
  w 0x9bd07ce9;         (* arm_UMULH X9 X7 X16 *)
  w 0xab0b018c;         (* arm_ADDS X12 X12 X11 *)
  w 0x9b037ceb;         (* arm_MUL X11 X7 X3 *)
  w 0x9bc37ce3;         (* arm_UMULH X3 X7 X3 *)
  w 0xba0b01ad;         (* arm_ADCS X13 X13 X11 *)
  w 0x9b047ceb;         (* arm_MUL X11 X7 X4 *)
  w 0x9bc47ce4;         (* arm_UMULH X4 X7 X4 *)
  w 0xba0b01ce;         (* arm_ADCS X14 X14 X11 *)
  w 0x9b057ceb;         (* arm_MUL X11 X7 X5 *)
  w 0x9bc57ce5;         (* arm_UMULH X5 X7 X5 *)
  w 0xba0b01ef;         (* arm_ADCS X15 X15 X11 *)
  w 0x9a9f37f0;         (* arm_CSET X16 Condition_CS *)
  w 0xab0401ef;         (* arm_ADDS X15 X15 X4 *)
  w 0x9a050210;         (* arm_ADC X16 X16 X5 *)
  w 0xab0f01ff;         (* arm_CMN X15 X15 *)
  w 0x9240f9ef;         (* arm_AND X15 X15 (rvalue (word 9223372036854775807)) *)
  w 0x9a100208;         (* arm_ADC X8 X16 X16 *)
  w 0xd2800267;         (* arm_MOV X7 (rvalue (word 19)) *)
  w 0x9b087ceb;         (* arm_MUL X11 X7 X8 *)
  w 0xab0b018c;         (* arm_ADDS X12 X12 X11 *)
  w 0xba0901ad;         (* arm_ADCS X13 X13 X9 *)
  w 0xba0301ce;         (* arm_ADCS X14 X14 X3 *)
  w 0x9a1f01ef;         (* arm_ADC X15 X15 XZR *)
  w 0xa91237ec;         (* arm_STP X12 X13 SP (Immediate_Offset (iword (&288))) *)
  w 0xa9133fee;         (* arm_STP X14 X15 SP (Immediate_Offset (iword (&304))) *)
  w 0xa95413e3;         (* arm_LDP X3 X4 SP (Immediate_Offset (iword (&320))) *)
  w 0xa94423e7;         (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&64))) *)
  w 0x9b077c6c;         (* arm_MUL X12 X3 X7 *)
  w 0x9bc77c6d;         (* arm_UMULH X13 X3 X7 *)
  w 0x9b087c6b;         (* arm_MUL X11 X3 X8 *)
  w 0x9bc87c6e;         (* arm_UMULH X14 X3 X8 *)
  w 0xab0b01ad;         (* arm_ADDS X13 X13 X11 *)
  w 0xa9452be9;         (* arm_LDP X9 X10 SP (Immediate_Offset (iword (&80))) *)
  w 0x9b097c6b;         (* arm_MUL X11 X3 X9 *)
  w 0x9bc97c6f;         (* arm_UMULH X15 X3 X9 *)
  w 0xba0b01ce;         (* arm_ADCS X14 X14 X11 *)
  w 0x9b0a7c6b;         (* arm_MUL X11 X3 X10 *)
  w 0x9bca7c70;         (* arm_UMULH X16 X3 X10 *)
  w 0xba0b01ef;         (* arm_ADCS X15 X15 X11 *)
  w 0x9a1f0210;         (* arm_ADC X16 X16 XZR *)
  w 0xa9551be5;         (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&336))) *)
  w 0x9b077c8b;         (* arm_MUL X11 X4 X7 *)
  w 0xab0b01ad;         (* arm_ADDS X13 X13 X11 *)
  w 0x9b087c8b;         (* arm_MUL X11 X4 X8 *)
  w 0xba0b01ce;         (* arm_ADCS X14 X14 X11 *)
  w 0x9b097c8b;         (* arm_MUL X11 X4 X9 *)
  w 0xba0b01ef;         (* arm_ADCS X15 X15 X11 *)
  w 0x9b0a7c8b;         (* arm_MUL X11 X4 X10 *)
  w 0xba0b0210;         (* arm_ADCS X16 X16 X11 *)
  w 0x9bca7c83;         (* arm_UMULH X3 X4 X10 *)
  w 0x9a1f0063;         (* arm_ADC X3 X3 XZR *)
  w 0x9bc77c8b;         (* arm_UMULH X11 X4 X7 *)
  w 0xab0b01ce;         (* arm_ADDS X14 X14 X11 *)
  w 0x9bc87c8b;         (* arm_UMULH X11 X4 X8 *)
  w 0xba0b01ef;         (* arm_ADCS X15 X15 X11 *)
  w 0x9bc97c8b;         (* arm_UMULH X11 X4 X9 *)
  w 0xba0b0210;         (* arm_ADCS X16 X16 X11 *)
  w 0x9a1f0063;         (* arm_ADC X3 X3 XZR *)
  w 0x9b077cab;         (* arm_MUL X11 X5 X7 *)
  w 0xab0b01ce;         (* arm_ADDS X14 X14 X11 *)
  w 0x9b087cab;         (* arm_MUL X11 X5 X8 *)
  w 0xba0b01ef;         (* arm_ADCS X15 X15 X11 *)
  w 0x9b097cab;         (* arm_MUL X11 X5 X9 *)
  w 0xba0b0210;         (* arm_ADCS X16 X16 X11 *)
  w 0x9b0a7cab;         (* arm_MUL X11 X5 X10 *)
  w 0xba0b0063;         (* arm_ADCS X3 X3 X11 *)
  w 0x9bca7ca4;         (* arm_UMULH X4 X5 X10 *)
  w 0x9a1f0084;         (* arm_ADC X4 X4 XZR *)
  w 0x9bc77cab;         (* arm_UMULH X11 X5 X7 *)
  w 0xab0b01ef;         (* arm_ADDS X15 X15 X11 *)
  w 0x9bc87cab;         (* arm_UMULH X11 X5 X8 *)
  w 0xba0b0210;         (* arm_ADCS X16 X16 X11 *)
  w 0x9bc97cab;         (* arm_UMULH X11 X5 X9 *)
  w 0xba0b0063;         (* arm_ADCS X3 X3 X11 *)
  w 0x9a1f0084;         (* arm_ADC X4 X4 XZR *)
  w 0x9b077ccb;         (* arm_MUL X11 X6 X7 *)
  w 0xab0b01ef;         (* arm_ADDS X15 X15 X11 *)
  w 0x9b087ccb;         (* arm_MUL X11 X6 X8 *)
  w 0xba0b0210;         (* arm_ADCS X16 X16 X11 *)
  w 0x9b097ccb;         (* arm_MUL X11 X6 X9 *)
  w 0xba0b0063;         (* arm_ADCS X3 X3 X11 *)
  w 0x9b0a7ccb;         (* arm_MUL X11 X6 X10 *)
  w 0xba0b0084;         (* arm_ADCS X4 X4 X11 *)
  w 0x9bca7cc5;         (* arm_UMULH X5 X6 X10 *)
  w 0x9a1f00a5;         (* arm_ADC X5 X5 XZR *)
  w 0x9bc77ccb;         (* arm_UMULH X11 X6 X7 *)
  w 0xab0b0210;         (* arm_ADDS X16 X16 X11 *)
  w 0x9bc87ccb;         (* arm_UMULH X11 X6 X8 *)
  w 0xba0b0063;         (* arm_ADCS X3 X3 X11 *)
  w 0x9bc97ccb;         (* arm_UMULH X11 X6 X9 *)
  w 0xba0b0084;         (* arm_ADCS X4 X4 X11 *)
  w 0x9a1f00a5;         (* arm_ADC X5 X5 XZR *)
  w 0xd28004c7;         (* arm_MOV X7 (rvalue (word 38)) *)
  w 0x9b107ceb;         (* arm_MUL X11 X7 X16 *)
  w 0x9bd07ce9;         (* arm_UMULH X9 X7 X16 *)
  w 0xab0b018c;         (* arm_ADDS X12 X12 X11 *)
  w 0x9b037ceb;         (* arm_MUL X11 X7 X3 *)
  w 0x9bc37ce3;         (* arm_UMULH X3 X7 X3 *)
  w 0xba0b01ad;         (* arm_ADCS X13 X13 X11 *)
  w 0x9b047ceb;         (* arm_MUL X11 X7 X4 *)
  w 0x9bc47ce4;         (* arm_UMULH X4 X7 X4 *)
  w 0xba0b01ce;         (* arm_ADCS X14 X14 X11 *)
  w 0x9b057ceb;         (* arm_MUL X11 X7 X5 *)
  w 0x9bc57ce5;         (* arm_UMULH X5 X7 X5 *)
  w 0xba0b01ef;         (* arm_ADCS X15 X15 X11 *)
  w 0x9a9f37f0;         (* arm_CSET X16 Condition_CS *)
  w 0xab0401ef;         (* arm_ADDS X15 X15 X4 *)
  w 0x9a050210;         (* arm_ADC X16 X16 X5 *)
  w 0xab0f01ff;         (* arm_CMN X15 X15 *)
  w 0x9240f9ef;         (* arm_AND X15 X15 (rvalue (word 9223372036854775807)) *)
  w 0x9a100208;         (* arm_ADC X8 X16 X16 *)
  w 0xd2800267;         (* arm_MOV X7 (rvalue (word 19)) *)
  w 0x9b087ceb;         (* arm_MUL X11 X7 X8 *)
  w 0xab0b018c;         (* arm_ADDS X12 X12 X11 *)
  w 0xba0901ad;         (* arm_ADCS X13 X13 X9 *)
  w 0xba0301ce;         (* arm_ADCS X14 X14 X3 *)
  w 0x9a1f01ef;         (* arm_ADC X15 X15 XZR *)
  w 0xa91437ec;         (* arm_STP X12 X13 SP (Immediate_Offset (iword (&320))) *)
  w 0xa9153fee;         (* arm_STP X14 X15 SP (Immediate_Offset (iword (&336))) *)
  w 0xa9501be5;         (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&256))) *)
  w 0xa9560fe4;         (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&352))) *)
  w 0xeb0400a5;         (* arm_SUBS X5 X5 X4 *)
  w 0xfa0300c6;         (* arm_SBCS X6 X6 X3 *)
  w 0xa95123e7;         (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&272))) *)
  w 0xa9570fe4;         (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&368))) *)
  w 0xfa0400e7;         (* arm_SBCS X7 X7 X4 *)
  w 0xfa030108;         (* arm_SBCS X8 X8 X3 *)
  w 0xd28004c4;         (* arm_MOV X4 (rvalue (word 38)) *)
  w 0x9a9f3083;         (* arm_CSEL X3 X4 XZR Condition_CC *)
  w 0xeb0300a5;         (* arm_SUBS X5 X5 X3 *)
  w 0xfa1f00c6;         (* arm_SBCS X6 X6 XZR *)
  w 0xfa1f00e7;         (* arm_SBCS X7 X7 XZR *)
  w 0xda1f0108;         (* arm_SBC X8 X8 XZR *)
  w 0xa9181be5;         (* arm_STP X5 X6 SP (Immediate_Offset (iword (&384))) *)
  w 0xa91923e7;         (* arm_STP X7 X8 SP (Immediate_Offset (iword (&400))) *)
  w 0xa95013e3;         (* arm_LDP X3 X4 SP (Immediate_Offset (iword (&256))) *)
  w 0xa95623e7;         (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&352))) *)
  w 0xab070063;         (* arm_ADDS X3 X3 X7 *)
  w 0xba080084;         (* arm_ADCS X4 X4 X8 *)
  w 0xa9511be5;         (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&272))) *)
  w 0xa95723e7;         (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&368))) *)
  w 0xba0700a5;         (* arm_ADCS X5 X5 X7 *)
  w 0xba0800c6;         (* arm_ADCS X6 X6 X8 *)
  w 0xd28004c9;         (* arm_MOV X9 (rvalue (word 38)) *)
  w 0x9a9f2129;         (* arm_CSEL X9 X9 XZR Condition_CS *)
  w 0xab090063;         (* arm_ADDS X3 X3 X9 *)
  w 0xba1f0084;         (* arm_ADCS X4 X4 XZR *)
  w 0xba1f00a5;         (* arm_ADCS X5 X5 XZR *)
  w 0x9a1f00c6;         (* arm_ADC X6 X6 XZR *)
  w 0xa91013e3;         (* arm_STP X3 X4 SP (Immediate_Offset (iword (&256))) *)
  w 0xa9111be5;         (* arm_STP X5 X6 SP (Immediate_Offset (iword (&272))) *)
  w 0xa9541be5;         (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&320))) *)
  w 0xa9520fe4;         (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&288))) *)
  w 0xeb0400a5;         (* arm_SUBS X5 X5 X4 *)
  w 0xfa0300c6;         (* arm_SBCS X6 X6 X3 *)
  w 0xa95523e7;         (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&336))) *)
  w 0xa9530fe4;         (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&304))) *)
  w 0xfa0400e7;         (* arm_SBCS X7 X7 X4 *)
  w 0xfa030108;         (* arm_SBCS X8 X8 X3 *)
  w 0xd28004c4;         (* arm_MOV X4 (rvalue (word 38)) *)
  w 0x9a9f3083;         (* arm_CSEL X3 X4 XZR Condition_CC *)
  w 0xeb0300a5;         (* arm_SUBS X5 X5 X3 *)
  w 0xfa1f00c6;         (* arm_SBCS X6 X6 XZR *)
  w 0xfa1f00e7;         (* arm_SBCS X7 X7 XZR *)
  w 0xda1f0108;         (* arm_SBC X8 X8 XZR *)
  w 0xa91a1be5;         (* arm_STP X5 X6 SP (Immediate_Offset (iword (&416))) *)
  w 0xa91b23e7;         (* arm_STP X7 X8 SP (Immediate_Offset (iword (&432))) *)
  w 0xa95413e3;         (* arm_LDP X3 X4 SP (Immediate_Offset (iword (&320))) *)
  w 0xa95223e7;         (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&288))) *)
  w 0xab070063;         (* arm_ADDS X3 X3 X7 *)
  w 0xba080084;         (* arm_ADCS X4 X4 X8 *)
  w 0xa9551be5;         (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&336))) *)
  w 0xa95323e7;         (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&304))) *)
  w 0xba0700a5;         (* arm_ADCS X5 X5 X7 *)
  w 0xba0800c6;         (* arm_ADCS X6 X6 X8 *)
  w 0xd28004c9;         (* arm_MOV X9 (rvalue (word 38)) *)
  w 0x9a9f2129;         (* arm_CSEL X9 X9 XZR Condition_CS *)
  w 0xab090063;         (* arm_ADDS X3 X3 X9 *)
  w 0xba1f0084;         (* arm_ADCS X4 X4 XZR *)
  w 0xba1f00a5;         (* arm_ADCS X5 X5 XZR *)
  w 0x9a1f00c6;         (* arm_ADC X6 X6 XZR *)
  w 0xa91213e3;         (* arm_STP X3 X4 SP (Immediate_Offset (iword (&288))) *)
  w 0xa9131be5;         (* arm_STP X5 X6 SP (Immediate_Offset (iword (&304))) *)
  w 0xa95813e3;         (* arm_LDP X3 X4 SP (Immediate_Offset (iword (&384))) *)
  w 0xa95023e7;         (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&256))) *)
  w 0x9b077c6c;         (* arm_MUL X12 X3 X7 *)
  w 0x9bc77c6d;         (* arm_UMULH X13 X3 X7 *)
  w 0x9b087c6b;         (* arm_MUL X11 X3 X8 *)
  w 0x9bc87c6e;         (* arm_UMULH X14 X3 X8 *)
  w 0xab0b01ad;         (* arm_ADDS X13 X13 X11 *)
  w 0xa9512be9;         (* arm_LDP X9 X10 SP (Immediate_Offset (iword (&272))) *)
  w 0x9b097c6b;         (* arm_MUL X11 X3 X9 *)
  w 0x9bc97c6f;         (* arm_UMULH X15 X3 X9 *)
  w 0xba0b01ce;         (* arm_ADCS X14 X14 X11 *)
  w 0x9b0a7c6b;         (* arm_MUL X11 X3 X10 *)
  w 0x9bca7c70;         (* arm_UMULH X16 X3 X10 *)
  w 0xba0b01ef;         (* arm_ADCS X15 X15 X11 *)
  w 0x9a1f0210;         (* arm_ADC X16 X16 XZR *)
  w 0xa9591be5;         (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&400))) *)
  w 0x9b077c8b;         (* arm_MUL X11 X4 X7 *)
  w 0xab0b01ad;         (* arm_ADDS X13 X13 X11 *)
  w 0x9b087c8b;         (* arm_MUL X11 X4 X8 *)
  w 0xba0b01ce;         (* arm_ADCS X14 X14 X11 *)
  w 0x9b097c8b;         (* arm_MUL X11 X4 X9 *)
  w 0xba0b01ef;         (* arm_ADCS X15 X15 X11 *)
  w 0x9b0a7c8b;         (* arm_MUL X11 X4 X10 *)
  w 0xba0b0210;         (* arm_ADCS X16 X16 X11 *)
  w 0x9bca7c83;         (* arm_UMULH X3 X4 X10 *)
  w 0x9a1f0063;         (* arm_ADC X3 X3 XZR *)
  w 0x9bc77c8b;         (* arm_UMULH X11 X4 X7 *)
  w 0xab0b01ce;         (* arm_ADDS X14 X14 X11 *)
  w 0x9bc87c8b;         (* arm_UMULH X11 X4 X8 *)
  w 0xba0b01ef;         (* arm_ADCS X15 X15 X11 *)
  w 0x9bc97c8b;         (* arm_UMULH X11 X4 X9 *)
  w 0xba0b0210;         (* arm_ADCS X16 X16 X11 *)
  w 0x9a1f0063;         (* arm_ADC X3 X3 XZR *)
  w 0x9b077cab;         (* arm_MUL X11 X5 X7 *)
  w 0xab0b01ce;         (* arm_ADDS X14 X14 X11 *)
  w 0x9b087cab;         (* arm_MUL X11 X5 X8 *)
  w 0xba0b01ef;         (* arm_ADCS X15 X15 X11 *)
  w 0x9b097cab;         (* arm_MUL X11 X5 X9 *)
  w 0xba0b0210;         (* arm_ADCS X16 X16 X11 *)
  w 0x9b0a7cab;         (* arm_MUL X11 X5 X10 *)
  w 0xba0b0063;         (* arm_ADCS X3 X3 X11 *)
  w 0x9bca7ca4;         (* arm_UMULH X4 X5 X10 *)
  w 0x9a1f0084;         (* arm_ADC X4 X4 XZR *)
  w 0x9bc77cab;         (* arm_UMULH X11 X5 X7 *)
  w 0xab0b01ef;         (* arm_ADDS X15 X15 X11 *)
  w 0x9bc87cab;         (* arm_UMULH X11 X5 X8 *)
  w 0xba0b0210;         (* arm_ADCS X16 X16 X11 *)
  w 0x9bc97cab;         (* arm_UMULH X11 X5 X9 *)
  w 0xba0b0063;         (* arm_ADCS X3 X3 X11 *)
  w 0x9a1f0084;         (* arm_ADC X4 X4 XZR *)
  w 0x9b077ccb;         (* arm_MUL X11 X6 X7 *)
  w 0xab0b01ef;         (* arm_ADDS X15 X15 X11 *)
  w 0x9b087ccb;         (* arm_MUL X11 X6 X8 *)
  w 0xba0b0210;         (* arm_ADCS X16 X16 X11 *)
  w 0x9b097ccb;         (* arm_MUL X11 X6 X9 *)
  w 0xba0b0063;         (* arm_ADCS X3 X3 X11 *)
  w 0x9b0a7ccb;         (* arm_MUL X11 X6 X10 *)
  w 0xba0b0084;         (* arm_ADCS X4 X4 X11 *)
  w 0x9bca7cc5;         (* arm_UMULH X5 X6 X10 *)
  w 0x9a1f00a5;         (* arm_ADC X5 X5 XZR *)
  w 0x9bc77ccb;         (* arm_UMULH X11 X6 X7 *)
  w 0xab0b0210;         (* arm_ADDS X16 X16 X11 *)
  w 0x9bc87ccb;         (* arm_UMULH X11 X6 X8 *)
  w 0xba0b0063;         (* arm_ADCS X3 X3 X11 *)
  w 0x9bc97ccb;         (* arm_UMULH X11 X6 X9 *)
  w 0xba0b0084;         (* arm_ADCS X4 X4 X11 *)
  w 0x9a1f00a5;         (* arm_ADC X5 X5 XZR *)
  w 0xd28004c7;         (* arm_MOV X7 (rvalue (word 38)) *)
  w 0x9b107ceb;         (* arm_MUL X11 X7 X16 *)
  w 0x9bd07ce9;         (* arm_UMULH X9 X7 X16 *)
  w 0xab0b018c;         (* arm_ADDS X12 X12 X11 *)
  w 0x9b037ceb;         (* arm_MUL X11 X7 X3 *)
  w 0x9bc37ce3;         (* arm_UMULH X3 X7 X3 *)
  w 0xba0b01ad;         (* arm_ADCS X13 X13 X11 *)
  w 0x9b047ceb;         (* arm_MUL X11 X7 X4 *)
  w 0x9bc47ce4;         (* arm_UMULH X4 X7 X4 *)
  w 0xba0b01ce;         (* arm_ADCS X14 X14 X11 *)
  w 0x9b057ceb;         (* arm_MUL X11 X7 X5 *)
  w 0x9bc57ce5;         (* arm_UMULH X5 X7 X5 *)
  w 0xba0b01ef;         (* arm_ADCS X15 X15 X11 *)
  w 0x9a9f37f0;         (* arm_CSET X16 Condition_CS *)
  w 0xab0401ef;         (* arm_ADDS X15 X15 X4 *)
  w 0x9a050210;         (* arm_ADC X16 X16 X5 *)
  w 0xab0f01ff;         (* arm_CMN X15 X15 *)
  w 0x9240f9ef;         (* arm_AND X15 X15 (rvalue (word 9223372036854775807)) *)
  w 0x9a100208;         (* arm_ADC X8 X16 X16 *)
  w 0xd2800267;         (* arm_MOV X7 (rvalue (word 19)) *)
  w 0x9b087ceb;         (* arm_MUL X11 X7 X8 *)
  w 0xab0b018c;         (* arm_ADDS X12 X12 X11 *)
  w 0xba0901ad;         (* arm_ADCS X13 X13 X9 *)
  w 0xba0301ce;         (* arm_ADCS X14 X14 X3 *)
  w 0x9a1f01ef;         (* arm_ADC X15 X15 XZR *)
  w 0xa90c37ec;         (* arm_STP X12 X13 SP (Immediate_Offset (iword (&192))) *)
  w 0xa90d3fee;         (* arm_STP X14 X15 SP (Immediate_Offset (iword (&208))) *)
  w 0xa95a13e3;         (* arm_LDP X3 X4 SP (Immediate_Offset (iword (&416))) *)
  w 0xa95823e7;         (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&384))) *)
  w 0x9b077c6c;         (* arm_MUL X12 X3 X7 *)
  w 0x9bc77c6d;         (* arm_UMULH X13 X3 X7 *)
  w 0x9b087c6b;         (* arm_MUL X11 X3 X8 *)
  w 0x9bc87c6e;         (* arm_UMULH X14 X3 X8 *)
  w 0xab0b01ad;         (* arm_ADDS X13 X13 X11 *)
  w 0xa9592be9;         (* arm_LDP X9 X10 SP (Immediate_Offset (iword (&400))) *)
  w 0x9b097c6b;         (* arm_MUL X11 X3 X9 *)
  w 0x9bc97c6f;         (* arm_UMULH X15 X3 X9 *)
  w 0xba0b01ce;         (* arm_ADCS X14 X14 X11 *)
  w 0x9b0a7c6b;         (* arm_MUL X11 X3 X10 *)
  w 0x9bca7c70;         (* arm_UMULH X16 X3 X10 *)
  w 0xba0b01ef;         (* arm_ADCS X15 X15 X11 *)
  w 0x9a1f0210;         (* arm_ADC X16 X16 XZR *)
  w 0xa95b1be5;         (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&432))) *)
  w 0x9b077c8b;         (* arm_MUL X11 X4 X7 *)
  w 0xab0b01ad;         (* arm_ADDS X13 X13 X11 *)
  w 0x9b087c8b;         (* arm_MUL X11 X4 X8 *)
  w 0xba0b01ce;         (* arm_ADCS X14 X14 X11 *)
  w 0x9b097c8b;         (* arm_MUL X11 X4 X9 *)
  w 0xba0b01ef;         (* arm_ADCS X15 X15 X11 *)
  w 0x9b0a7c8b;         (* arm_MUL X11 X4 X10 *)
  w 0xba0b0210;         (* arm_ADCS X16 X16 X11 *)
  w 0x9bca7c83;         (* arm_UMULH X3 X4 X10 *)
  w 0x9a1f0063;         (* arm_ADC X3 X3 XZR *)
  w 0x9bc77c8b;         (* arm_UMULH X11 X4 X7 *)
  w 0xab0b01ce;         (* arm_ADDS X14 X14 X11 *)
  w 0x9bc87c8b;         (* arm_UMULH X11 X4 X8 *)
  w 0xba0b01ef;         (* arm_ADCS X15 X15 X11 *)
  w 0x9bc97c8b;         (* arm_UMULH X11 X4 X9 *)
  w 0xba0b0210;         (* arm_ADCS X16 X16 X11 *)
  w 0x9a1f0063;         (* arm_ADC X3 X3 XZR *)
  w 0x9b077cab;         (* arm_MUL X11 X5 X7 *)
  w 0xab0b01ce;         (* arm_ADDS X14 X14 X11 *)
  w 0x9b087cab;         (* arm_MUL X11 X5 X8 *)
  w 0xba0b01ef;         (* arm_ADCS X15 X15 X11 *)
  w 0x9b097cab;         (* arm_MUL X11 X5 X9 *)
  w 0xba0b0210;         (* arm_ADCS X16 X16 X11 *)
  w 0x9b0a7cab;         (* arm_MUL X11 X5 X10 *)
  w 0xba0b0063;         (* arm_ADCS X3 X3 X11 *)
  w 0x9bca7ca4;         (* arm_UMULH X4 X5 X10 *)
  w 0x9a1f0084;         (* arm_ADC X4 X4 XZR *)
  w 0x9bc77cab;         (* arm_UMULH X11 X5 X7 *)
  w 0xab0b01ef;         (* arm_ADDS X15 X15 X11 *)
  w 0x9bc87cab;         (* arm_UMULH X11 X5 X8 *)
  w 0xba0b0210;         (* arm_ADCS X16 X16 X11 *)
  w 0x9bc97cab;         (* arm_UMULH X11 X5 X9 *)
  w 0xba0b0063;         (* arm_ADCS X3 X3 X11 *)
  w 0x9a1f0084;         (* arm_ADC X4 X4 XZR *)
  w 0x9b077ccb;         (* arm_MUL X11 X6 X7 *)
  w 0xab0b01ef;         (* arm_ADDS X15 X15 X11 *)
  w 0x9b087ccb;         (* arm_MUL X11 X6 X8 *)
  w 0xba0b0210;         (* arm_ADCS X16 X16 X11 *)
  w 0x9b097ccb;         (* arm_MUL X11 X6 X9 *)
  w 0xba0b0063;         (* arm_ADCS X3 X3 X11 *)
  w 0x9b0a7ccb;         (* arm_MUL X11 X6 X10 *)
  w 0xba0b0084;         (* arm_ADCS X4 X4 X11 *)
  w 0x9bca7cc5;         (* arm_UMULH X5 X6 X10 *)
  w 0x9a1f00a5;         (* arm_ADC X5 X5 XZR *)
  w 0x9bc77ccb;         (* arm_UMULH X11 X6 X7 *)
  w 0xab0b0210;         (* arm_ADDS X16 X16 X11 *)
  w 0x9bc87ccb;         (* arm_UMULH X11 X6 X8 *)
  w 0xba0b0063;         (* arm_ADCS X3 X3 X11 *)
  w 0x9bc97ccb;         (* arm_UMULH X11 X6 X9 *)
  w 0xba0b0084;         (* arm_ADCS X4 X4 X11 *)
  w 0x9a1f00a5;         (* arm_ADC X5 X5 XZR *)
  w 0xd28004c7;         (* arm_MOV X7 (rvalue (word 38)) *)
  w 0x9b107ceb;         (* arm_MUL X11 X7 X16 *)
  w 0x9bd07ce9;         (* arm_UMULH X9 X7 X16 *)
  w 0xab0b018c;         (* arm_ADDS X12 X12 X11 *)
  w 0x9b037ceb;         (* arm_MUL X11 X7 X3 *)
  w 0x9bc37ce3;         (* arm_UMULH X3 X7 X3 *)
  w 0xba0b01ad;         (* arm_ADCS X13 X13 X11 *)
  w 0x9b047ceb;         (* arm_MUL X11 X7 X4 *)
  w 0x9bc47ce4;         (* arm_UMULH X4 X7 X4 *)
  w 0xba0b01ce;         (* arm_ADCS X14 X14 X11 *)
  w 0x9b057ceb;         (* arm_MUL X11 X7 X5 *)
  w 0x9bc57ce5;         (* arm_UMULH X5 X7 X5 *)
  w 0xba0b01ef;         (* arm_ADCS X15 X15 X11 *)
  w 0x9a9f37f0;         (* arm_CSET X16 Condition_CS *)
  w 0xab0401ef;         (* arm_ADDS X15 X15 X4 *)
  w 0x9a050210;         (* arm_ADC X16 X16 X5 *)
  w 0xab0f01ff;         (* arm_CMN X15 X15 *)
  w 0x9240f9ef;         (* arm_AND X15 X15 (rvalue (word 9223372036854775807)) *)
  w 0x9a100208;         (* arm_ADC X8 X16 X16 *)
  w 0xd2800267;         (* arm_MOV X7 (rvalue (word 19)) *)
  w 0x9b087ceb;         (* arm_MUL X11 X7 X8 *)
  w 0xab0b018c;         (* arm_ADDS X12 X12 X11 *)
  w 0xba0901ad;         (* arm_ADCS X13 X13 X9 *)
  w 0xba0301ce;         (* arm_ADCS X14 X14 X3 *)
  w 0x9a1f01ef;         (* arm_ADC X15 X15 XZR *)
  w 0xa90837ec;         (* arm_STP X12 X13 SP (Immediate_Offset (iword (&128))) *)
  w 0xa9093fee;         (* arm_STP X14 X15 SP (Immediate_Offset (iword (&144))) *)
  w 0xa95013e3;         (* arm_LDP X3 X4 SP (Immediate_Offset (iword (&256))) *)
  w 0xa95223e7;         (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&288))) *)
  w 0x9b077c6c;         (* arm_MUL X12 X3 X7 *)
  w 0x9bc77c6d;         (* arm_UMULH X13 X3 X7 *)
  w 0x9b087c6b;         (* arm_MUL X11 X3 X8 *)
  w 0x9bc87c6e;         (* arm_UMULH X14 X3 X8 *)
  w 0xab0b01ad;         (* arm_ADDS X13 X13 X11 *)
  w 0xa9532be9;         (* arm_LDP X9 X10 SP (Immediate_Offset (iword (&304))) *)
  w 0x9b097c6b;         (* arm_MUL X11 X3 X9 *)
  w 0x9bc97c6f;         (* arm_UMULH X15 X3 X9 *)
  w 0xba0b01ce;         (* arm_ADCS X14 X14 X11 *)
  w 0x9b0a7c6b;         (* arm_MUL X11 X3 X10 *)
  w 0x9bca7c70;         (* arm_UMULH X16 X3 X10 *)
  w 0xba0b01ef;         (* arm_ADCS X15 X15 X11 *)
  w 0x9a1f0210;         (* arm_ADC X16 X16 XZR *)
  w 0xa9511be5;         (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&272))) *)
  w 0x9b077c8b;         (* arm_MUL X11 X4 X7 *)
  w 0xab0b01ad;         (* arm_ADDS X13 X13 X11 *)
  w 0x9b087c8b;         (* arm_MUL X11 X4 X8 *)
  w 0xba0b01ce;         (* arm_ADCS X14 X14 X11 *)
  w 0x9b097c8b;         (* arm_MUL X11 X4 X9 *)
  w 0xba0b01ef;         (* arm_ADCS X15 X15 X11 *)
  w 0x9b0a7c8b;         (* arm_MUL X11 X4 X10 *)
  w 0xba0b0210;         (* arm_ADCS X16 X16 X11 *)
  w 0x9bca7c83;         (* arm_UMULH X3 X4 X10 *)
  w 0x9a1f0063;         (* arm_ADC X3 X3 XZR *)
  w 0x9bc77c8b;         (* arm_UMULH X11 X4 X7 *)
  w 0xab0b01ce;         (* arm_ADDS X14 X14 X11 *)
  w 0x9bc87c8b;         (* arm_UMULH X11 X4 X8 *)
  w 0xba0b01ef;         (* arm_ADCS X15 X15 X11 *)
  w 0x9bc97c8b;         (* arm_UMULH X11 X4 X9 *)
  w 0xba0b0210;         (* arm_ADCS X16 X16 X11 *)
  w 0x9a1f0063;         (* arm_ADC X3 X3 XZR *)
  w 0x9b077cab;         (* arm_MUL X11 X5 X7 *)
  w 0xab0b01ce;         (* arm_ADDS X14 X14 X11 *)
  w 0x9b087cab;         (* arm_MUL X11 X5 X8 *)
  w 0xba0b01ef;         (* arm_ADCS X15 X15 X11 *)
  w 0x9b097cab;         (* arm_MUL X11 X5 X9 *)
  w 0xba0b0210;         (* arm_ADCS X16 X16 X11 *)
  w 0x9b0a7cab;         (* arm_MUL X11 X5 X10 *)
  w 0xba0b0063;         (* arm_ADCS X3 X3 X11 *)
  w 0x9bca7ca4;         (* arm_UMULH X4 X5 X10 *)
  w 0x9a1f0084;         (* arm_ADC X4 X4 XZR *)
  w 0x9bc77cab;         (* arm_UMULH X11 X5 X7 *)
  w 0xab0b01ef;         (* arm_ADDS X15 X15 X11 *)
  w 0x9bc87cab;         (* arm_UMULH X11 X5 X8 *)
  w 0xba0b0210;         (* arm_ADCS X16 X16 X11 *)
  w 0x9bc97cab;         (* arm_UMULH X11 X5 X9 *)
  w 0xba0b0063;         (* arm_ADCS X3 X3 X11 *)
  w 0x9a1f0084;         (* arm_ADC X4 X4 XZR *)
  w 0x9b077ccb;         (* arm_MUL X11 X6 X7 *)
  w 0xab0b01ef;         (* arm_ADDS X15 X15 X11 *)
  w 0x9b087ccb;         (* arm_MUL X11 X6 X8 *)
  w 0xba0b0210;         (* arm_ADCS X16 X16 X11 *)
  w 0x9b097ccb;         (* arm_MUL X11 X6 X9 *)
  w 0xba0b0063;         (* arm_ADCS X3 X3 X11 *)
  w 0x9b0a7ccb;         (* arm_MUL X11 X6 X10 *)
  w 0xba0b0084;         (* arm_ADCS X4 X4 X11 *)
  w 0x9bca7cc5;         (* arm_UMULH X5 X6 X10 *)
  w 0x9a1f00a5;         (* arm_ADC X5 X5 XZR *)
  w 0x9bc77ccb;         (* arm_UMULH X11 X6 X7 *)
  w 0xab0b0210;         (* arm_ADDS X16 X16 X11 *)
  w 0x9bc87ccb;         (* arm_UMULH X11 X6 X8 *)
  w 0xba0b0063;         (* arm_ADCS X3 X3 X11 *)
  w 0x9bc97ccb;         (* arm_UMULH X11 X6 X9 *)
  w 0xba0b0084;         (* arm_ADCS X4 X4 X11 *)
  w 0x9a1f00a5;         (* arm_ADC X5 X5 XZR *)
  w 0xd28004c7;         (* arm_MOV X7 (rvalue (word 38)) *)
  w 0x9b107ceb;         (* arm_MUL X11 X7 X16 *)
  w 0x9bd07ce9;         (* arm_UMULH X9 X7 X16 *)
  w 0xab0b018c;         (* arm_ADDS X12 X12 X11 *)
  w 0x9b037ceb;         (* arm_MUL X11 X7 X3 *)
  w 0x9bc37ce3;         (* arm_UMULH X3 X7 X3 *)
  w 0xba0b01ad;         (* arm_ADCS X13 X13 X11 *)
  w 0x9b047ceb;         (* arm_MUL X11 X7 X4 *)
  w 0x9bc47ce4;         (* arm_UMULH X4 X7 X4 *)
  w 0xba0b01ce;         (* arm_ADCS X14 X14 X11 *)
  w 0x9b057ceb;         (* arm_MUL X11 X7 X5 *)
  w 0x9bc57ce5;         (* arm_UMULH X5 X7 X5 *)
  w 0xba0b01ef;         (* arm_ADCS X15 X15 X11 *)
  w 0x9a9f37f0;         (* arm_CSET X16 Condition_CS *)
  w 0xab0401ef;         (* arm_ADDS X15 X15 X4 *)
  w 0x9a050210;         (* arm_ADC X16 X16 X5 *)
  w 0xab0f01ff;         (* arm_CMN X15 X15 *)
  w 0x9240f9ef;         (* arm_AND X15 X15 (rvalue (word 9223372036854775807)) *)
  w 0x9a100208;         (* arm_ADC X8 X16 X16 *)
  w 0xd2800267;         (* arm_MOV X7 (rvalue (word 19)) *)
  w 0x9b087ceb;         (* arm_MUL X11 X7 X8 *)
  w 0xab0b018c;         (* arm_ADDS X12 X12 X11 *)
  w 0xba0901ad;         (* arm_ADCS X13 X13 X9 *)
  w 0xba0301ce;         (* arm_ADCS X14 X14 X3 *)
  w 0x9a1f01ef;         (* arm_ADC X15 X15 XZR *)
  w 0xa90a37ec;         (* arm_STP X12 X13 SP (Immediate_Offset (iword (&160))) *)
  w 0xa90b3fee;         (* arm_STP X14 X15 SP (Immediate_Offset (iword (&176))) *)
  w 0xa95a13e3;         (* arm_LDP X3 X4 SP (Immediate_Offset (iword (&416))) *)
  w 0xa95223e7;         (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&288))) *)
  w 0x9b077c6c;         (* arm_MUL X12 X3 X7 *)
  w 0x9bc77c6d;         (* arm_UMULH X13 X3 X7 *)
  w 0x9b087c6b;         (* arm_MUL X11 X3 X8 *)
  w 0x9bc87c6e;         (* arm_UMULH X14 X3 X8 *)
  w 0xab0b01ad;         (* arm_ADDS X13 X13 X11 *)
  w 0xa9532be9;         (* arm_LDP X9 X10 SP (Immediate_Offset (iword (&304))) *)
  w 0x9b097c6b;         (* arm_MUL X11 X3 X9 *)
  w 0x9bc97c6f;         (* arm_UMULH X15 X3 X9 *)
  w 0xba0b01ce;         (* arm_ADCS X14 X14 X11 *)
  w 0x9b0a7c6b;         (* arm_MUL X11 X3 X10 *)
  w 0x9bca7c70;         (* arm_UMULH X16 X3 X10 *)
  w 0xba0b01ef;         (* arm_ADCS X15 X15 X11 *)
  w 0x9a1f0210;         (* arm_ADC X16 X16 XZR *)
  w 0xa95b1be5;         (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&432))) *)
  w 0x9b077c8b;         (* arm_MUL X11 X4 X7 *)
  w 0xab0b01ad;         (* arm_ADDS X13 X13 X11 *)
  w 0x9b087c8b;         (* arm_MUL X11 X4 X8 *)
  w 0xba0b01ce;         (* arm_ADCS X14 X14 X11 *)
  w 0x9b097c8b;         (* arm_MUL X11 X4 X9 *)
  w 0xba0b01ef;         (* arm_ADCS X15 X15 X11 *)
  w 0x9b0a7c8b;         (* arm_MUL X11 X4 X10 *)
  w 0xba0b0210;         (* arm_ADCS X16 X16 X11 *)
  w 0x9bca7c83;         (* arm_UMULH X3 X4 X10 *)
  w 0x9a1f0063;         (* arm_ADC X3 X3 XZR *)
  w 0x9bc77c8b;         (* arm_UMULH X11 X4 X7 *)
  w 0xab0b01ce;         (* arm_ADDS X14 X14 X11 *)
  w 0x9bc87c8b;         (* arm_UMULH X11 X4 X8 *)
  w 0xba0b01ef;         (* arm_ADCS X15 X15 X11 *)
  w 0x9bc97c8b;         (* arm_UMULH X11 X4 X9 *)
  w 0xba0b0210;         (* arm_ADCS X16 X16 X11 *)
  w 0x9a1f0063;         (* arm_ADC X3 X3 XZR *)
  w 0x9b077cab;         (* arm_MUL X11 X5 X7 *)
  w 0xab0b01ce;         (* arm_ADDS X14 X14 X11 *)
  w 0x9b087cab;         (* arm_MUL X11 X5 X8 *)
  w 0xba0b01ef;         (* arm_ADCS X15 X15 X11 *)
  w 0x9b097cab;         (* arm_MUL X11 X5 X9 *)
  w 0xba0b0210;         (* arm_ADCS X16 X16 X11 *)
  w 0x9b0a7cab;         (* arm_MUL X11 X5 X10 *)
  w 0xba0b0063;         (* arm_ADCS X3 X3 X11 *)
  w 0x9bca7ca4;         (* arm_UMULH X4 X5 X10 *)
  w 0x9a1f0084;         (* arm_ADC X4 X4 XZR *)
  w 0x9bc77cab;         (* arm_UMULH X11 X5 X7 *)
  w 0xab0b01ef;         (* arm_ADDS X15 X15 X11 *)
  w 0x9bc87cab;         (* arm_UMULH X11 X5 X8 *)
  w 0xba0b0210;         (* arm_ADCS X16 X16 X11 *)
  w 0x9bc97cab;         (* arm_UMULH X11 X5 X9 *)
  w 0xba0b0063;         (* arm_ADCS X3 X3 X11 *)
  w 0x9a1f0084;         (* arm_ADC X4 X4 XZR *)
  w 0x9b077ccb;         (* arm_MUL X11 X6 X7 *)
  w 0xab0b01ef;         (* arm_ADDS X15 X15 X11 *)
  w 0x9b087ccb;         (* arm_MUL X11 X6 X8 *)
  w 0xba0b0210;         (* arm_ADCS X16 X16 X11 *)
  w 0x9b097ccb;         (* arm_MUL X11 X6 X9 *)
  w 0xba0b0063;         (* arm_ADCS X3 X3 X11 *)
  w 0x9b0a7ccb;         (* arm_MUL X11 X6 X10 *)
  w 0xba0b0084;         (* arm_ADCS X4 X4 X11 *)
  w 0x9bca7cc5;         (* arm_UMULH X5 X6 X10 *)
  w 0x9a1f00a5;         (* arm_ADC X5 X5 XZR *)
  w 0x9bc77ccb;         (* arm_UMULH X11 X6 X7 *)
  w 0xab0b0210;         (* arm_ADDS X16 X16 X11 *)
  w 0x9bc87ccb;         (* arm_UMULH X11 X6 X8 *)
  w 0xba0b0063;         (* arm_ADCS X3 X3 X11 *)
  w 0x9bc97ccb;         (* arm_UMULH X11 X6 X9 *)
  w 0xba0b0084;         (* arm_ADCS X4 X4 X11 *)
  w 0x9a1f00a5;         (* arm_ADC X5 X5 XZR *)
  w 0xd28004c7;         (* arm_MOV X7 (rvalue (word 38)) *)
  w 0x9b107ceb;         (* arm_MUL X11 X7 X16 *)
  w 0x9bd07ce9;         (* arm_UMULH X9 X7 X16 *)
  w 0xab0b018c;         (* arm_ADDS X12 X12 X11 *)
  w 0x9b037ceb;         (* arm_MUL X11 X7 X3 *)
  w 0x9bc37ce3;         (* arm_UMULH X3 X7 X3 *)
  w 0xba0b01ad;         (* arm_ADCS X13 X13 X11 *)
  w 0x9b047ceb;         (* arm_MUL X11 X7 X4 *)
  w 0x9bc47ce4;         (* arm_UMULH X4 X7 X4 *)
  w 0xba0b01ce;         (* arm_ADCS X14 X14 X11 *)
  w 0x9b057ceb;         (* arm_MUL X11 X7 X5 *)
  w 0x9bc57ce5;         (* arm_UMULH X5 X7 X5 *)
  w 0xba0b01ef;         (* arm_ADCS X15 X15 X11 *)
  w 0x9a9f37f0;         (* arm_CSET X16 Condition_CS *)
  w 0xab0401ef;         (* arm_ADDS X15 X15 X4 *)
  w 0x9a050210;         (* arm_ADC X16 X16 X5 *)
  w 0xab0f01ff;         (* arm_CMN X15 X15 *)
  w 0x9240f9ef;         (* arm_AND X15 X15 (rvalue (word 9223372036854775807)) *)
  w 0x9a100208;         (* arm_ADC X8 X16 X16 *)
  w 0xd2800267;         (* arm_MOV X7 (rvalue (word 19)) *)
  w 0x9b087ceb;         (* arm_MUL X11 X7 X8 *)
  w 0xab0b018c;         (* arm_ADDS X12 X12 X11 *)
  w 0xba0901ad;         (* arm_ADCS X13 X13 X9 *)
  w 0xba0301ce;         (* arm_ADCS X14 X14 X3 *)
  w 0x9a1f01ef;         (* arm_ADC X15 X15 XZR *)
  w 0xa90e37ec;         (* arm_STP X12 X13 SP (Immediate_Offset (iword (&224))) *)
  w 0xa90f3fee;         (* arm_STP X14 X15 SP (Immediate_Offset (iword (&240))) *)
  w 0x91001294;         (* arm_ADD X20 X20 (rvalue (word 4)) *)
  w 0xf104029f;         (* arm_CMP X20 (rvalue (word 256)) *)
  w 0x54ff8563;         (* arm_BCC (word 2093228) *)
  w 0xa94813e3;         (* arm_LDP X3 X4 SP (Immediate_Offset (iword (&128))) *)
  w 0xa94e23e7;         (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&224))) *)
  w 0xab070063;         (* arm_ADDS X3 X3 X7 *)
  w 0xba080084;         (* arm_ADCS X4 X4 X8 *)
  w 0xa9491be5;         (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&144))) *)
  w 0xa94f23e7;         (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&240))) *)
  w 0xba0700a5;         (* arm_ADCS X5 X5 X7 *)
  w 0xba0800c6;         (* arm_ADCS X6 X6 X8 *)
  w 0xd28004c9;         (* arm_MOV X9 (rvalue (word 38)) *)
  w 0x9a9f2129;         (* arm_CSEL X9 X9 XZR Condition_CS *)
  w 0xab090063;         (* arm_ADDS X3 X3 X9 *)
  w 0xba1f0084;         (* arm_ADCS X4 X4 XZR *)
  w 0xba1f00a5;         (* arm_ADCS X5 X5 XZR *)
  w 0x9a1f00c6;         (* arm_ADC X6 X6 XZR *)
  w 0xa91213e3;         (* arm_STP X3 X4 SP (Immediate_Offset (iword (&288))) *)
  w 0xa9131be5;         (* arm_STP X5 X6 SP (Immediate_Offset (iword (&304))) *)
  w 0xa9481be5;         (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&128))) *)
  w 0xa94e0fe4;         (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&224))) *)
  w 0xeb0400a5;         (* arm_SUBS X5 X5 X4 *)
  w 0xfa0300c6;         (* arm_SBCS X6 X6 X3 *)
  w 0xa94923e7;         (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&144))) *)
  w 0xa94f0fe4;         (* arm_LDP X4 X3 SP (Immediate_Offset (iword (&240))) *)
  w 0xfa0400e7;         (* arm_SBCS X7 X7 X4 *)
  w 0xfa030108;         (* arm_SBCS X8 X8 X3 *)
  w 0xd28004c4;         (* arm_MOV X4 (rvalue (word 38)) *)
  w 0x9a9f3083;         (* arm_CSEL X3 X4 XZR Condition_CC *)
  w 0xeb0300a5;         (* arm_SUBS X5 X5 X3 *)
  w 0xfa1f00c6;         (* arm_SBCS X6 X6 XZR *)
  w 0xfa1f00e7;         (* arm_SBCS X7 X7 XZR *)
  w 0xda1f0108;         (* arm_SBC X8 X8 XZR *)
  w 0xa9141be5;         (* arm_STP X5 X6 SP (Immediate_Offset (iword (&320))) *)
  w 0xa91523e7;         (* arm_STP X7 X8 SP (Immediate_Offset (iword (&336))) *)
  w 0x910403e0;         (* arm_ADD X0 SP (rvalue (word 256)) *)
  w 0x910503e1;         (* arm_ADD X1 SP (rvalue (word 320)) *)
  w 0xaa0003f4;         (* arm_MOV X20 X0 *)
  w 0x9280024a;         (* arm_MOVN X10 (word 18) 0 *)
  w 0x9280000b;         (* arm_MOVN X11 (word 0) 0 *)
  w 0xa9002fea;         (* arm_STP X10 X11 SP (Immediate_Offset (iword (&0))) *)
  w 0x92f0000c;         (* arm_MOVN X12 (word 32768) 48 *)
  w 0xa90133eb;         (* arm_STP X11 X12 SP (Immediate_Offset (iword (&16))) *)
  w 0xa9400c22;         (* arm_LDP X2 X3 X1 (Immediate_Offset (iword (&0))) *)
  w 0xa9411424;         (* arm_LDP X4 X5 X1 (Immediate_Offset (iword (&16))) *)
  w 0xd2800267;         (* arm_MOV X7 (rvalue (word 19)) *)
  w 0xd37ffca6;         (* arm_LSR X6 X5 63 *)
  w 0x9b061ce6;         (* arm_MADD X6 X7 X6 X7 *)
  w 0xab060042;         (* arm_ADDS X2 X2 X6 *)
  w 0xba1f0063;         (* arm_ADCS X3 X3 XZR *)
  w 0xba1f0084;         (* arm_ADCS X4 X4 XZR *)
  w 0xb24100a5;         (* arm_ORR X5 X5 (rvalue (word 9223372036854775808)) *)
  w 0xba1f00a5;         (* arm_ADCS X5 X5 XZR *)
  w 0x9a9f30e6;         (* arm_CSEL X6 X7 XZR Condition_CC *)
  w 0xeb060042;         (* arm_SUBS X2 X2 X6 *)
  w 0xfa1f0063;         (* arm_SBCS X3 X3 XZR *)
  w 0xfa1f0084;         (* arm_SBCS X4 X4 XZR *)
  w 0xda1f00a5;         (* arm_SBC X5 X5 XZR *)
  w 0x9240f8a5;         (* arm_AND X5 X5 (rvalue (word 9223372036854775807)) *)
  w 0xa9020fe2;         (* arm_STP X2 X3 SP (Immediate_Offset (iword (&32))) *)
  w 0xa90317e4;         (* arm_STP X4 X5 SP (Immediate_Offset (iword (&48))) *)
  w 0xa9047fff;         (* arm_STP XZR XZR SP (Immediate_Offset (iword (&64))) *)
  w 0xa9057fff;         (* arm_STP XZR XZR SP (Immediate_Offset (iword (&80))) *)
  w 0xd284132a;         (* arm_MOV X10 (rvalue (word 8345)) *)
  w 0xf2aea04a;         (* arm_MOVK X10 (word 29954) 16 *)
  w 0xf2d3c46a;         (* arm_MOVK X10 (word 40483) 32 *)
  w 0xf2f41f2a;         (* arm_MOVK X10 (word 41209) 48 *)
  w 0xd284b2ab;         (* arm_MOV X11 (rvalue (word 9621)) *)
  w 0xf2a3a26b;         (* arm_MOVK X11 (word 7443) 16 *)
  w 0xf2d1e7eb;         (* arm_MOVK X11 (word 36671) 32 *)
  w 0xf2f518cb;         (* arm_MOVK X11 (word 43206) 48 *)
  w 0xd28a484c;         (* arm_MOV X12 (rvalue (word 21058)) *)
  w 0xf2a0b58c;         (* arm_MOVK X12 (word 1452) 16 *)
  w 0xf2d1270c;         (* arm_MOVK X12 (word 35128) 32 *)
  w 0xf2ed8d8c;         (* arm_MOVK X12 (word 27756) 48 *)
  w 0xd280c2ad;         (* arm_MOV X13 (rvalue (word 1557)) *)
  w 0xf2a82eed;         (* arm_MOVK X13 (word 16759) 16 *)
  w 0xf2c1164d;         (* arm_MOVK X13 (word 2226) 32 *)
  w 0xf2e4ecad;         (* arm_MOVK X13 (word 10085) 48 *)
  w 0xa9062fea;         (* arm_STP X10 X11 SP (Immediate_Offset (iword (&96))) *)
  w 0xa90737ec;         (* arm_STP X12 X13 SP (Immediate_Offset (iword (&112))) *)
  w 0xd2800155;         (* arm_MOV X21 (rvalue (word 10)) *)
  w 0xd2800036;         (* arm_MOV X22 (rvalue (word 1)) *)
  w 0x1400010b;         (* arm_B (word 1068) *)
  w 0xeb1f015f;         (* arm_CMP X10 XZR *)
  w 0xda9f53ee;         (* arm_CSETM X14 Condition_MI *)
  w 0xda8a554a;         (* arm_CNEG X10 X10 Condition_MI *)
  w 0xeb1f017f;         (* arm_CMP X11 XZR *)
  w 0xda9f53ef;         (* arm_CSETM X15 Condition_MI *)
  w 0xda8b556b;         (* arm_CNEG X11 X11 Condition_MI *)
  w 0xeb1f019f;         (* arm_CMP X12 XZR *)
  w 0xda9f53f0;         (* arm_CSETM X16 Condition_MI *)
  w 0xda8c558c;         (* arm_CNEG X12 X12 Condition_MI *)
  w 0xeb1f01bf;         (* arm_CMP X13 XZR *)
  w 0xda9f53f1;         (* arm_CSETM X17 Condition_MI *)
  w 0xda8d55ad;         (* arm_CNEG X13 X13 Condition_MI *)
  w 0x8a0e0140;         (* arm_AND X0 X10 X14 *)
  w 0x8a0f0161;         (* arm_AND X1 X11 X15 *)
  w 0x8b010009;         (* arm_ADD X9 X0 X1 *)
  w 0x8a100180;         (* arm_AND X0 X12 X16 *)
  w 0x8a1101a1;         (* arm_AND X1 X13 X17 *)
  w 0x8b010013;         (* arm_ADD X19 X0 X1 *)
  w 0xf94003e7;         (* arm_LDR X7 SP (Immediate_Offset (word 0)) *)
  w 0xca0e00e1;         (* arm_EOR X1 X7 X14 *)
  w 0x9b0a7c20;         (* arm_MUL X0 X1 X10 *)
  w 0x9bca7c21;         (* arm_UMULH X1 X1 X10 *)
  w 0xab000124;         (* arm_ADDS X4 X9 X0 *)
  w 0x9a0103e2;         (* arm_ADC X2 XZR X1 *)
  w 0xf94013e8;         (* arm_LDR X8 SP (Immediate_Offset (word 32)) *)
  w 0xca0f0101;         (* arm_EOR X1 X8 X15 *)
  w 0x9b0b7c20;         (* arm_MUL X0 X1 X11 *)
  w 0x9bcb7c21;         (* arm_UMULH X1 X1 X11 *)
  w 0xab000084;         (* arm_ADDS X4 X4 X0 *)
  w 0x9a010042;         (* arm_ADC X2 X2 X1 *)
  w 0xca1000e1;         (* arm_EOR X1 X7 X16 *)
  w 0x9b0c7c20;         (* arm_MUL X0 X1 X12 *)
  w 0x9bcc7c21;         (* arm_UMULH X1 X1 X12 *)
  w 0xab000265;         (* arm_ADDS X5 X19 X0 *)
  w 0x9a0103e3;         (* arm_ADC X3 XZR X1 *)
  w 0xca110101;         (* arm_EOR X1 X8 X17 *)
  w 0x9b0d7c20;         (* arm_MUL X0 X1 X13 *)
  w 0x9bcd7c21;         (* arm_UMULH X1 X1 X13 *)
  w 0xab0000a5;         (* arm_ADDS X5 X5 X0 *)
  w 0x9a010063;         (* arm_ADC X3 X3 X1 *)
  w 0xf94007e7;         (* arm_LDR X7 SP (Immediate_Offset (word 8)) *)
  w 0xca0e00e1;         (* arm_EOR X1 X7 X14 *)
  w 0x9b0a7c20;         (* arm_MUL X0 X1 X10 *)
  w 0x9bca7c21;         (* arm_UMULH X1 X1 X10 *)
  w 0xab000042;         (* arm_ADDS X2 X2 X0 *)
  w 0x9a0103e6;         (* arm_ADC X6 XZR X1 *)
  w 0xf94017e8;         (* arm_LDR X8 SP (Immediate_Offset (word 40)) *)
  w 0xca0f0101;         (* arm_EOR X1 X8 X15 *)
  w 0x9b0b7c20;         (* arm_MUL X0 X1 X11 *)
  w 0x9bcb7c21;         (* arm_UMULH X1 X1 X11 *)
  w 0xab000042;         (* arm_ADDS X2 X2 X0 *)
  w 0x9a0100c6;         (* arm_ADC X6 X6 X1 *)
  w 0x93c4ec44;         (* arm_EXTR X4 X2 X4 59 *)
  w 0xf90003e4;         (* arm_STR X4 SP (Immediate_Offset (word 0)) *)
  w 0xca1000e1;         (* arm_EOR X1 X7 X16 *)
  w 0x9b0c7c20;         (* arm_MUL X0 X1 X12 *)
  w 0x9bcc7c21;         (* arm_UMULH X1 X1 X12 *)
  w 0xab000063;         (* arm_ADDS X3 X3 X0 *)
  w 0x9a0103e4;         (* arm_ADC X4 XZR X1 *)
  w 0xca110101;         (* arm_EOR X1 X8 X17 *)
  w 0x9b0d7c20;         (* arm_MUL X0 X1 X13 *)
  w 0x9bcd7c21;         (* arm_UMULH X1 X1 X13 *)
  w 0xab000063;         (* arm_ADDS X3 X3 X0 *)
  w 0x9a010084;         (* arm_ADC X4 X4 X1 *)
  w 0x93c5ec65;         (* arm_EXTR X5 X3 X5 59 *)
  w 0xf90013e5;         (* arm_STR X5 SP (Immediate_Offset (word 32)) *)
  w 0xf9400be7;         (* arm_LDR X7 SP (Immediate_Offset (word 16)) *)
  w 0xca0e00e1;         (* arm_EOR X1 X7 X14 *)
  w 0x9b0a7c20;         (* arm_MUL X0 X1 X10 *)
  w 0x9bca7c21;         (* arm_UMULH X1 X1 X10 *)
  w 0xab0000c6;         (* arm_ADDS X6 X6 X0 *)
  w 0x9a0103e5;         (* arm_ADC X5 XZR X1 *)
  w 0xf9401be8;         (* arm_LDR X8 SP (Immediate_Offset (word 48)) *)
  w 0xca0f0101;         (* arm_EOR X1 X8 X15 *)
  w 0x9b0b7c20;         (* arm_MUL X0 X1 X11 *)
  w 0x9bcb7c21;         (* arm_UMULH X1 X1 X11 *)
  w 0xab0000c6;         (* arm_ADDS X6 X6 X0 *)
  w 0x9a0100a5;         (* arm_ADC X5 X5 X1 *)
  w 0x93c2ecc2;         (* arm_EXTR X2 X6 X2 59 *)
  w 0xf90007e2;         (* arm_STR X2 SP (Immediate_Offset (word 8)) *)
  w 0xca1000e1;         (* arm_EOR X1 X7 X16 *)
  w 0x9b0c7c20;         (* arm_MUL X0 X1 X12 *)
  w 0x9bcc7c21;         (* arm_UMULH X1 X1 X12 *)
  w 0xab000084;         (* arm_ADDS X4 X4 X0 *)
  w 0x9a0103e2;         (* arm_ADC X2 XZR X1 *)
  w 0xca110101;         (* arm_EOR X1 X8 X17 *)
  w 0x9b0d7c20;         (* arm_MUL X0 X1 X13 *)
  w 0x9bcd7c21;         (* arm_UMULH X1 X1 X13 *)
  w 0xab000084;         (* arm_ADDS X4 X4 X0 *)
  w 0x9a010042;         (* arm_ADC X2 X2 X1 *)
  w 0x93c3ec83;         (* arm_EXTR X3 X4 X3 59 *)
  w 0xf90017e3;         (* arm_STR X3 SP (Immediate_Offset (word 40)) *)
  w 0xf9400fe7;         (* arm_LDR X7 SP (Immediate_Offset (word 24)) *)
  w 0xca0e00e1;         (* arm_EOR X1 X7 X14 *)
  w 0x937ffc23;         (* arm_ASR X3 X1 63 *)
  w 0x8a0a0063;         (* arm_AND X3 X3 X10 *)
  w 0xcb0303e3;         (* arm_NEG X3 X3 *)
  w 0x9b0a7c20;         (* arm_MUL X0 X1 X10 *)
  w 0x9bca7c21;         (* arm_UMULH X1 X1 X10 *)
  w 0xab0000a5;         (* arm_ADDS X5 X5 X0 *)
  w 0x9a010063;         (* arm_ADC X3 X3 X1 *)
  w 0xf9401fe8;         (* arm_LDR X8 SP (Immediate_Offset (word 56)) *)
  w 0xca0f0101;         (* arm_EOR X1 X8 X15 *)
  w 0x937ffc20;         (* arm_ASR X0 X1 63 *)
  w 0x8a0b0000;         (* arm_AND X0 X0 X11 *)
  w 0xcb000063;         (* arm_SUB X3 X3 X0 *)
  w 0x9b0b7c20;         (* arm_MUL X0 X1 X11 *)
  w 0x9bcb7c21;         (* arm_UMULH X1 X1 X11 *)
  w 0xab0000a5;         (* arm_ADDS X5 X5 X0 *)
  w 0x9a010063;         (* arm_ADC X3 X3 X1 *)
  w 0x93c6eca6;         (* arm_EXTR X6 X5 X6 59 *)
  w 0xf9000be6;         (* arm_STR X6 SP (Immediate_Offset (word 16)) *)
  w 0x93c5ec65;         (* arm_EXTR X5 X3 X5 59 *)
  w 0xf9000fe5;         (* arm_STR X5 SP (Immediate_Offset (word 24)) *)
  w 0xca1000e1;         (* arm_EOR X1 X7 X16 *)
  w 0x937ffc25;         (* arm_ASR X5 X1 63 *)
  w 0x8a0c00a5;         (* arm_AND X5 X5 X12 *)
  w 0xcb0503e5;         (* arm_NEG X5 X5 *)
  w 0x9b0c7c20;         (* arm_MUL X0 X1 X12 *)
  w 0x9bcc7c21;         (* arm_UMULH X1 X1 X12 *)
  w 0xab000042;         (* arm_ADDS X2 X2 X0 *)
  w 0x9a0100a5;         (* arm_ADC X5 X5 X1 *)
  w 0xca110101;         (* arm_EOR X1 X8 X17 *)
  w 0x937ffc20;         (* arm_ASR X0 X1 63 *)
  w 0x8a0d0000;         (* arm_AND X0 X0 X13 *)
  w 0xcb0000a5;         (* arm_SUB X5 X5 X0 *)
  w 0x9b0d7c20;         (* arm_MUL X0 X1 X13 *)
  w 0x9bcd7c21;         (* arm_UMULH X1 X1 X13 *)
  w 0xab000042;         (* arm_ADDS X2 X2 X0 *)
  w 0x9a0100a5;         (* arm_ADC X5 X5 X1 *)
  w 0x93c4ec44;         (* arm_EXTR X4 X2 X4 59 *)
  w 0xf9001be4;         (* arm_STR X4 SP (Immediate_Offset (word 48)) *)
  w 0x93c2eca2;         (* arm_EXTR X2 X5 X2 59 *)
  w 0xf9001fe2;         (* arm_STR X2 SP (Immediate_Offset (word 56)) *)
  w 0xf94023e7;         (* arm_LDR X7 SP (Immediate_Offset (word 64)) *)
  w 0xca0e00e1;         (* arm_EOR X1 X7 X14 *)
  w 0x9b0a7c20;         (* arm_MUL X0 X1 X10 *)
  w 0x9bca7c21;         (* arm_UMULH X1 X1 X10 *)
  w 0xab000124;         (* arm_ADDS X4 X9 X0 *)
  w 0x9a0103e2;         (* arm_ADC X2 XZR X1 *)
  w 0xf94033e8;         (* arm_LDR X8 SP (Immediate_Offset (word 96)) *)
  w 0xca0f0101;         (* arm_EOR X1 X8 X15 *)
  w 0x9b0b7c20;         (* arm_MUL X0 X1 X11 *)
  w 0x9bcb7c21;         (* arm_UMULH X1 X1 X11 *)
  w 0xab000084;         (* arm_ADDS X4 X4 X0 *)
  w 0xf90023e4;         (* arm_STR X4 SP (Immediate_Offset (word 64)) *)
  w 0x9a010042;         (* arm_ADC X2 X2 X1 *)
  w 0xca1000e1;         (* arm_EOR X1 X7 X16 *)
  w 0x9b0c7c20;         (* arm_MUL X0 X1 X12 *)
  w 0x9bcc7c21;         (* arm_UMULH X1 X1 X12 *)
  w 0xab000265;         (* arm_ADDS X5 X19 X0 *)
  w 0x9a0103e3;         (* arm_ADC X3 XZR X1 *)
  w 0xca110101;         (* arm_EOR X1 X8 X17 *)
  w 0x9b0d7c20;         (* arm_MUL X0 X1 X13 *)
  w 0x9bcd7c21;         (* arm_UMULH X1 X1 X13 *)
  w 0xab0000a5;         (* arm_ADDS X5 X5 X0 *)
  w 0xf90033e5;         (* arm_STR X5 SP (Immediate_Offset (word 96)) *)
  w 0x9a010063;         (* arm_ADC X3 X3 X1 *)
  w 0xf94027e7;         (* arm_LDR X7 SP (Immediate_Offset (word 72)) *)
  w 0xca0e00e1;         (* arm_EOR X1 X7 X14 *)
  w 0x9b0a7c20;         (* arm_MUL X0 X1 X10 *)
  w 0x9bca7c21;         (* arm_UMULH X1 X1 X10 *)
  w 0xab000042;         (* arm_ADDS X2 X2 X0 *)
  w 0x9a0103e6;         (* arm_ADC X6 XZR X1 *)
  w 0xf94037e8;         (* arm_LDR X8 SP (Immediate_Offset (word 104)) *)
  w 0xca0f0101;         (* arm_EOR X1 X8 X15 *)
  w 0x9b0b7c20;         (* arm_MUL X0 X1 X11 *)
  w 0x9bcb7c21;         (* arm_UMULH X1 X1 X11 *)
  w 0xab000042;         (* arm_ADDS X2 X2 X0 *)
  w 0xf90027e2;         (* arm_STR X2 SP (Immediate_Offset (word 72)) *)
  w 0x9a0100c6;         (* arm_ADC X6 X6 X1 *)
  w 0xca1000e1;         (* arm_EOR X1 X7 X16 *)
  w 0x9b0c7c20;         (* arm_MUL X0 X1 X12 *)
  w 0x9bcc7c21;         (* arm_UMULH X1 X1 X12 *)
  w 0xab000063;         (* arm_ADDS X3 X3 X0 *)
  w 0x9a0103e4;         (* arm_ADC X4 XZR X1 *)
  w 0xca110101;         (* arm_EOR X1 X8 X17 *)
  w 0x9b0d7c20;         (* arm_MUL X0 X1 X13 *)
  w 0x9bcd7c21;         (* arm_UMULH X1 X1 X13 *)
  w 0xab000063;         (* arm_ADDS X3 X3 X0 *)
  w 0xf90037e3;         (* arm_STR X3 SP (Immediate_Offset (word 104)) *)
  w 0x9a010084;         (* arm_ADC X4 X4 X1 *)
  w 0xf9402be7;         (* arm_LDR X7 SP (Immediate_Offset (word 80)) *)
  w 0xca0e00e1;         (* arm_EOR X1 X7 X14 *)
  w 0x9b0a7c20;         (* arm_MUL X0 X1 X10 *)
  w 0x9bca7c21;         (* arm_UMULH X1 X1 X10 *)
  w 0xab0000c6;         (* arm_ADDS X6 X6 X0 *)
  w 0x9a0103e5;         (* arm_ADC X5 XZR X1 *)
  w 0xf9403be8;         (* arm_LDR X8 SP (Immediate_Offset (word 112)) *)
  w 0xca0f0101;         (* arm_EOR X1 X8 X15 *)
  w 0x9b0b7c20;         (* arm_MUL X0 X1 X11 *)
  w 0x9bcb7c21;         (* arm_UMULH X1 X1 X11 *)
  w 0xab0000c6;         (* arm_ADDS X6 X6 X0 *)
  w 0xf9002be6;         (* arm_STR X6 SP (Immediate_Offset (word 80)) *)
  w 0x9a0100a5;         (* arm_ADC X5 X5 X1 *)
  w 0xca1000e1;         (* arm_EOR X1 X7 X16 *)
  w 0x9b0c7c20;         (* arm_MUL X0 X1 X12 *)
  w 0x9bcc7c21;         (* arm_UMULH X1 X1 X12 *)
  w 0xab000084;         (* arm_ADDS X4 X4 X0 *)
  w 0x9a0103e2;         (* arm_ADC X2 XZR X1 *)
  w 0xca110101;         (* arm_EOR X1 X8 X17 *)
  w 0x9b0d7c20;         (* arm_MUL X0 X1 X13 *)
  w 0x9bcd7c21;         (* arm_UMULH X1 X1 X13 *)
  w 0xab000084;         (* arm_ADDS X4 X4 X0 *)
  w 0xf9003be4;         (* arm_STR X4 SP (Immediate_Offset (word 112)) *)
  w 0x9a010042;         (* arm_ADC X2 X2 X1 *)
  w 0xf9402fe7;         (* arm_LDR X7 SP (Immediate_Offset (word 88)) *)
  w 0xca0e00e1;         (* arm_EOR X1 X7 X14 *)
  w 0x8a0a01c3;         (* arm_AND X3 X14 X10 *)
  w 0xcb0303e3;         (* arm_NEG X3 X3 *)
  w 0x9b0a7c20;         (* arm_MUL X0 X1 X10 *)
  w 0x9bca7c21;         (* arm_UMULH X1 X1 X10 *)
  w 0xab0000a5;         (* arm_ADDS X5 X5 X0 *)
  w 0x9a010063;         (* arm_ADC X3 X3 X1 *)
  w 0xf9403fe8;         (* arm_LDR X8 SP (Immediate_Offset (word 120)) *)
  w 0xca0f0101;         (* arm_EOR X1 X8 X15 *)
  w 0x8a0b01e0;         (* arm_AND X0 X15 X11 *)
  w 0xcb000063;         (* arm_SUB X3 X3 X0 *)
  w 0x9b0b7c20;         (* arm_MUL X0 X1 X11 *)
  w 0x9bcb7c21;         (* arm_UMULH X1 X1 X11 *)
  w 0xab0000a5;         (* arm_ADDS X5 X5 X0 *)
  w 0x9a010063;         (* arm_ADC X3 X3 X1 *)
  w 0x93c5fc66;         (* arm_EXTR X6 X3 X5 63 *)
  w 0xa94407e0;         (* arm_LDP X0 X1 SP (Immediate_Offset (iword (&64))) *)
  w 0x8b83fcc6;         (* arm_ADD X6 X6 (Shiftedreg X3 ASR 63) *)
  w 0xd2800263;         (* arm_MOV X3 (rvalue (word 19)) *)
  w 0x9b037cc4;         (* arm_MUL X4 X6 X3 *)
  w 0x8b06fca5;         (* arm_ADD X5 X5 (Shiftedreg X6 LSL 63) *)
  w 0x9b437cc3;         (* arm_SMULH X3 X6 X3 *)
  w 0xf9402be6;         (* arm_LDR X6 SP (Immediate_Offset (word 80)) *)
  w 0xab040000;         (* arm_ADDS X0 X0 X4 *)
  w 0xba030021;         (* arm_ADCS X1 X1 X3 *)
  w 0x937ffc63;         (* arm_ASR X3 X3 63 *)
  w 0xba0300c6;         (* arm_ADCS X6 X6 X3 *)
  w 0x9a0300a5;         (* arm_ADC X5 X5 X3 *)
  w 0xa90407e0;         (* arm_STP X0 X1 SP (Immediate_Offset (iword (&64))) *)
  w 0xa90517e6;         (* arm_STP X6 X5 SP (Immediate_Offset (iword (&80))) *)
  w 0xca1000e1;         (* arm_EOR X1 X7 X16 *)
  w 0x8a0c0205;         (* arm_AND X5 X16 X12 *)
  w 0xcb0503e5;         (* arm_NEG X5 X5 *)
  w 0x9b0c7c20;         (* arm_MUL X0 X1 X12 *)
  w 0x9bcc7c21;         (* arm_UMULH X1 X1 X12 *)
  w 0xab000042;         (* arm_ADDS X2 X2 X0 *)
  w 0x9a0100a5;         (* arm_ADC X5 X5 X1 *)
  w 0xca110101;         (* arm_EOR X1 X8 X17 *)
  w 0x8a0d0220;         (* arm_AND X0 X17 X13 *)
  w 0xcb0000a5;         (* arm_SUB X5 X5 X0 *)
  w 0x9b0d7c20;         (* arm_MUL X0 X1 X13 *)
  w 0x9bcd7c21;         (* arm_UMULH X1 X1 X13 *)
  w 0xab000042;         (* arm_ADDS X2 X2 X0 *)
  w 0x9a0100a5;         (* arm_ADC X5 X5 X1 *)
  w 0x93c2fca6;         (* arm_EXTR X6 X5 X2 63 *)
  w 0xa94607e0;         (* arm_LDP X0 X1 SP (Immediate_Offset (iword (&96))) *)
  w 0x8b85fcc6;         (* arm_ADD X6 X6 (Shiftedreg X5 ASR 63) *)
  w 0xd2800265;         (* arm_MOV X5 (rvalue (word 19)) *)
  w 0x9b057cc4;         (* arm_MUL X4 X6 X5 *)
  w 0x8b06fc42;         (* arm_ADD X2 X2 (Shiftedreg X6 LSL 63) *)
  w 0x9b457cc5;         (* arm_SMULH X5 X6 X5 *)
  w 0xf9403be3;         (* arm_LDR X3 SP (Immediate_Offset (word 112)) *)
  w 0xab040000;         (* arm_ADDS X0 X0 X4 *)
  w 0xba050021;         (* arm_ADCS X1 X1 X5 *)
  w 0x937ffca5;         (* arm_ASR X5 X5 63 *)
  w 0xba050063;         (* arm_ADCS X3 X3 X5 *)
  w 0x9a050042;         (* arm_ADC X2 X2 X5 *)
  w 0xa90607e0;         (* arm_STP X0 X1 SP (Immediate_Offset (iword (&96))) *)
  w 0xa9070be3;         (* arm_STP X3 X2 SP (Immediate_Offset (iword (&112))) *)
  w 0xaa1603e1;         (* arm_MOV X1 X22 *)
  w 0xf94003e2;         (* arm_LDR X2 SP (Immediate_Offset (word 0)) *)
  w 0xf94013e3;         (* arm_LDR X3 SP (Immediate_Offset (word 32)) *)
  w 0x92404c44;         (* arm_AND X4 X2 (rvalue (word 1048575)) *)
  w 0xb2575884;         (* arm_ORR X4 X4 (rvalue (word 18446741874686296064)) *)
  w 0x92404c65;         (* arm_AND X5 X3 (rvalue (word 1048575)) *)
  w 0xb24204a5;         (* arm_ORR X5 X5 (rvalue (word 13835058055282163712)) *)
  w 0xf24000bf;         (* arm_TST X5 (rvalue (word 1)) *)
  w 0x9a9f1086;         (* arm_CSEL X6 X4 XZR Condition_NE *)
  w 0xfa5f1028;         (* arm_CCMP X1 XZR (word 8) Condition_NE *)
  w 0xda81b421;         (* arm_CNEG X1 X1 Condition_GE *)
  w 0xda86b4c6;         (* arm_CNEG X6 X6 Condition_GE *)
  w 0x9a84a0a4;         (* arm_CSEL X4 X5 X4 Condition_GE *)
  w 0x8b0600a5;         (* arm_ADD X5 X5 X6 *)
  w 0x91000821;         (* arm_ADD X1 X1 (rvalue (word 2)) *)
  w 0xf27f00bf;         (* arm_TST X5 (rvalue (word 2)) *)
  w 0x9341fca5;         (* arm_ASR X5 X5 1 *)
  w 0x9a9f1086;         (* arm_CSEL X6 X4 XZR Condition_NE *)
  w 0xfa5f1028;         (* arm_CCMP X1 XZR (word 8) Condition_NE *)
  w 0xda81b421;         (* arm_CNEG X1 X1 Condition_GE *)
  w 0xda86b4c6;         (* arm_CNEG X6 X6 Condition_GE *)
  w 0x9a84a0a4;         (* arm_CSEL X4 X5 X4 Condition_GE *)
  w 0x8b0600a5;         (* arm_ADD X5 X5 X6 *)
  w 0x91000821;         (* arm_ADD X1 X1 (rvalue (word 2)) *)
  w 0xf27f00bf;         (* arm_TST X5 (rvalue (word 2)) *)
  w 0x9341fca5;         (* arm_ASR X5 X5 1 *)
  w 0x9a9f1086;         (* arm_CSEL X6 X4 XZR Condition_NE *)
  w 0xfa5f1028;         (* arm_CCMP X1 XZR (word 8) Condition_NE *)
  w 0xda81b421;         (* arm_CNEG X1 X1 Condition_GE *)
  w 0xda86b4c6;         (* arm_CNEG X6 X6 Condition_GE *)
  w 0x9a84a0a4;         (* arm_CSEL X4 X5 X4 Condition_GE *)
  w 0x8b0600a5;         (* arm_ADD X5 X5 X6 *)
  w 0x91000821;         (* arm_ADD X1 X1 (rvalue (word 2)) *)
  w 0xf27f00bf;         (* arm_TST X5 (rvalue (word 2)) *)
  w 0x9341fca5;         (* arm_ASR X5 X5 1 *)
  w 0x9a9f1086;         (* arm_CSEL X6 X4 XZR Condition_NE *)
  w 0xfa5f1028;         (* arm_CCMP X1 XZR (word 8) Condition_NE *)
  w 0xda81b421;         (* arm_CNEG X1 X1 Condition_GE *)
  w 0xda86b4c6;         (* arm_CNEG X6 X6 Condition_GE *)
  w 0x9a84a0a4;         (* arm_CSEL X4 X5 X4 Condition_GE *)
  w 0x8b0600a5;         (* arm_ADD X5 X5 X6 *)
  w 0x91000821;         (* arm_ADD X1 X1 (rvalue (word 2)) *)
  w 0xf27f00bf;         (* arm_TST X5 (rvalue (word 2)) *)
  w 0x9341fca5;         (* arm_ASR X5 X5 1 *)
  w 0x9a9f1086;         (* arm_CSEL X6 X4 XZR Condition_NE *)
  w 0xfa5f1028;         (* arm_CCMP X1 XZR (word 8) Condition_NE *)
  w 0xda81b421;         (* arm_CNEG X1 X1 Condition_GE *)
  w 0xda86b4c6;         (* arm_CNEG X6 X6 Condition_GE *)
  w 0x9a84a0a4;         (* arm_CSEL X4 X5 X4 Condition_GE *)
  w 0x8b0600a5;         (* arm_ADD X5 X5 X6 *)
  w 0x91000821;         (* arm_ADD X1 X1 (rvalue (word 2)) *)
  w 0xf27f00bf;         (* arm_TST X5 (rvalue (word 2)) *)
  w 0x9341fca5;         (* arm_ASR X5 X5 1 *)
  w 0x9a9f1086;         (* arm_CSEL X6 X4 XZR Condition_NE *)
  w 0xfa5f1028;         (* arm_CCMP X1 XZR (word 8) Condition_NE *)
  w 0xda81b421;         (* arm_CNEG X1 X1 Condition_GE *)
  w 0xda86b4c6;         (* arm_CNEG X6 X6 Condition_GE *)
  w 0x9a84a0a4;         (* arm_CSEL X4 X5 X4 Condition_GE *)
  w 0x8b0600a5;         (* arm_ADD X5 X5 X6 *)
  w 0x91000821;         (* arm_ADD X1 X1 (rvalue (word 2)) *)
  w 0xf27f00bf;         (* arm_TST X5 (rvalue (word 2)) *)
  w 0x9341fca5;         (* arm_ASR X5 X5 1 *)
  w 0x9a9f1086;         (* arm_CSEL X6 X4 XZR Condition_NE *)
  w 0xfa5f1028;         (* arm_CCMP X1 XZR (word 8) Condition_NE *)
  w 0xda81b421;         (* arm_CNEG X1 X1 Condition_GE *)
  w 0xda86b4c6;         (* arm_CNEG X6 X6 Condition_GE *)
  w 0x9a84a0a4;         (* arm_CSEL X4 X5 X4 Condition_GE *)
  w 0x8b0600a5;         (* arm_ADD X5 X5 X6 *)
  w 0x91000821;         (* arm_ADD X1 X1 (rvalue (word 2)) *)
  w 0xf27f00bf;         (* arm_TST X5 (rvalue (word 2)) *)
  w 0x9341fca5;         (* arm_ASR X5 X5 1 *)
  w 0x9a9f1086;         (* arm_CSEL X6 X4 XZR Condition_NE *)
  w 0xfa5f1028;         (* arm_CCMP X1 XZR (word 8) Condition_NE *)
  w 0xda81b421;         (* arm_CNEG X1 X1 Condition_GE *)
  w 0xda86b4c6;         (* arm_CNEG X6 X6 Condition_GE *)
  w 0x9a84a0a4;         (* arm_CSEL X4 X5 X4 Condition_GE *)
  w 0x8b0600a5;         (* arm_ADD X5 X5 X6 *)
  w 0x91000821;         (* arm_ADD X1 X1 (rvalue (word 2)) *)
  w 0xf27f00bf;         (* arm_TST X5 (rvalue (word 2)) *)
  w 0x9341fca5;         (* arm_ASR X5 X5 1 *)
  w 0x9a9f1086;         (* arm_CSEL X6 X4 XZR Condition_NE *)
  w 0xfa5f1028;         (* arm_CCMP X1 XZR (word 8) Condition_NE *)
  w 0xda81b421;         (* arm_CNEG X1 X1 Condition_GE *)
  w 0xda86b4c6;         (* arm_CNEG X6 X6 Condition_GE *)
  w 0x9a84a0a4;         (* arm_CSEL X4 X5 X4 Condition_GE *)
  w 0x8b0600a5;         (* arm_ADD X5 X5 X6 *)
  w 0x91000821;         (* arm_ADD X1 X1 (rvalue (word 2)) *)
  w 0xf27f00bf;         (* arm_TST X5 (rvalue (word 2)) *)
  w 0x9341fca5;         (* arm_ASR X5 X5 1 *)
  w 0x9a9f1086;         (* arm_CSEL X6 X4 XZR Condition_NE *)
  w 0xfa5f1028;         (* arm_CCMP X1 XZR (word 8) Condition_NE *)
  w 0xda81b421;         (* arm_CNEG X1 X1 Condition_GE *)
  w 0xda86b4c6;         (* arm_CNEG X6 X6 Condition_GE *)
  w 0x9a84a0a4;         (* arm_CSEL X4 X5 X4 Condition_GE *)
  w 0x8b0600a5;         (* arm_ADD X5 X5 X6 *)
  w 0x91000821;         (* arm_ADD X1 X1 (rvalue (word 2)) *)
  w 0xf27f00bf;         (* arm_TST X5 (rvalue (word 2)) *)
  w 0x9341fca5;         (* arm_ASR X5 X5 1 *)
  w 0x9a9f1086;         (* arm_CSEL X6 X4 XZR Condition_NE *)
  w 0xfa5f1028;         (* arm_CCMP X1 XZR (word 8) Condition_NE *)
  w 0xda81b421;         (* arm_CNEG X1 X1 Condition_GE *)
  w 0xda86b4c6;         (* arm_CNEG X6 X6 Condition_GE *)
  w 0x9a84a0a4;         (* arm_CSEL X4 X5 X4 Condition_GE *)
  w 0x8b0600a5;         (* arm_ADD X5 X5 X6 *)
  w 0x91000821;         (* arm_ADD X1 X1 (rvalue (word 2)) *)
  w 0xf27f00bf;         (* arm_TST X5 (rvalue (word 2)) *)
  w 0x9341fca5;         (* arm_ASR X5 X5 1 *)
  w 0x9a9f1086;         (* arm_CSEL X6 X4 XZR Condition_NE *)
  w 0xfa5f1028;         (* arm_CCMP X1 XZR (word 8) Condition_NE *)
  w 0xda81b421;         (* arm_CNEG X1 X1 Condition_GE *)
  w 0xda86b4c6;         (* arm_CNEG X6 X6 Condition_GE *)
  w 0x9a84a0a4;         (* arm_CSEL X4 X5 X4 Condition_GE *)
  w 0x8b0600a5;         (* arm_ADD X5 X5 X6 *)
  w 0x91000821;         (* arm_ADD X1 X1 (rvalue (word 2)) *)
  w 0xf27f00bf;         (* arm_TST X5 (rvalue (word 2)) *)
  w 0x9341fca5;         (* arm_ASR X5 X5 1 *)
  w 0x9a9f1086;         (* arm_CSEL X6 X4 XZR Condition_NE *)
  w 0xfa5f1028;         (* arm_CCMP X1 XZR (word 8) Condition_NE *)
  w 0xda81b421;         (* arm_CNEG X1 X1 Condition_GE *)
  w 0xda86b4c6;         (* arm_CNEG X6 X6 Condition_GE *)
  w 0x9a84a0a4;         (* arm_CSEL X4 X5 X4 Condition_GE *)
  w 0x8b0600a5;         (* arm_ADD X5 X5 X6 *)
  w 0x91000821;         (* arm_ADD X1 X1 (rvalue (word 2)) *)
  w 0xf27f00bf;         (* arm_TST X5 (rvalue (word 2)) *)
  w 0x9341fca5;         (* arm_ASR X5 X5 1 *)
  w 0x9a9f1086;         (* arm_CSEL X6 X4 XZR Condition_NE *)
  w 0xfa5f1028;         (* arm_CCMP X1 XZR (word 8) Condition_NE *)
  w 0xda81b421;         (* arm_CNEG X1 X1 Condition_GE *)
  w 0xda86b4c6;         (* arm_CNEG X6 X6 Condition_GE *)
  w 0x9a84a0a4;         (* arm_CSEL X4 X5 X4 Condition_GE *)
  w 0x8b0600a5;         (* arm_ADD X5 X5 X6 *)
  w 0x91000821;         (* arm_ADD X1 X1 (rvalue (word 2)) *)
  w 0xf27f00bf;         (* arm_TST X5 (rvalue (word 2)) *)
  w 0x9341fca5;         (* arm_ASR X5 X5 1 *)
  w 0x9a9f1086;         (* arm_CSEL X6 X4 XZR Condition_NE *)
  w 0xfa5f1028;         (* arm_CCMP X1 XZR (word 8) Condition_NE *)
  w 0xda81b421;         (* arm_CNEG X1 X1 Condition_GE *)
  w 0xda86b4c6;         (* arm_CNEG X6 X6 Condition_GE *)
  w 0x9a84a0a4;         (* arm_CSEL X4 X5 X4 Condition_GE *)
  w 0x8b0600a5;         (* arm_ADD X5 X5 X6 *)
  w 0x91000821;         (* arm_ADD X1 X1 (rvalue (word 2)) *)
  w 0xf27f00bf;         (* arm_TST X5 (rvalue (word 2)) *)
  w 0x9341fca5;         (* arm_ASR X5 X5 1 *)
  w 0x9a9f1086;         (* arm_CSEL X6 X4 XZR Condition_NE *)
  w 0xfa5f1028;         (* arm_CCMP X1 XZR (word 8) Condition_NE *)
  w 0xda81b421;         (* arm_CNEG X1 X1 Condition_GE *)
  w 0xda86b4c6;         (* arm_CNEG X6 X6 Condition_GE *)
  w 0x9a84a0a4;         (* arm_CSEL X4 X5 X4 Condition_GE *)
  w 0x8b0600a5;         (* arm_ADD X5 X5 X6 *)
  w 0x91000821;         (* arm_ADD X1 X1 (rvalue (word 2)) *)
  w 0xf27f00bf;         (* arm_TST X5 (rvalue (word 2)) *)
  w 0x9341fca5;         (* arm_ASR X5 X5 1 *)
  w 0x9a9f1086;         (* arm_CSEL X6 X4 XZR Condition_NE *)
  w 0xfa5f1028;         (* arm_CCMP X1 XZR (word 8) Condition_NE *)
  w 0xda81b421;         (* arm_CNEG X1 X1 Condition_GE *)
  w 0xda86b4c6;         (* arm_CNEG X6 X6 Condition_GE *)
  w 0x9a84a0a4;         (* arm_CSEL X4 X5 X4 Condition_GE *)
  w 0x8b0600a5;         (* arm_ADD X5 X5 X6 *)
  w 0x91000821;         (* arm_ADD X1 X1 (rvalue (word 2)) *)
  w 0xf27f00bf;         (* arm_TST X5 (rvalue (word 2)) *)
  w 0x9341fca5;         (* arm_ASR X5 X5 1 *)
  w 0x9a9f1086;         (* arm_CSEL X6 X4 XZR Condition_NE *)
  w 0xfa5f1028;         (* arm_CCMP X1 XZR (word 8) Condition_NE *)
  w 0xda81b421;         (* arm_CNEG X1 X1 Condition_GE *)
  w 0xda86b4c6;         (* arm_CNEG X6 X6 Condition_GE *)
  w 0x9a84a0a4;         (* arm_CSEL X4 X5 X4 Condition_GE *)
  w 0x8b0600a5;         (* arm_ADD X5 X5 X6 *)
  w 0x91000821;         (* arm_ADD X1 X1 (rvalue (word 2)) *)
  w 0xf27f00bf;         (* arm_TST X5 (rvalue (word 2)) *)
  w 0x9341fca5;         (* arm_ASR X5 X5 1 *)
  w 0x9a9f1086;         (* arm_CSEL X6 X4 XZR Condition_NE *)
  w 0xfa5f1028;         (* arm_CCMP X1 XZR (word 8) Condition_NE *)
  w 0xda81b421;         (* arm_CNEG X1 X1 Condition_GE *)
  w 0xda86b4c6;         (* arm_CNEG X6 X6 Condition_GE *)
  w 0x9a84a0a4;         (* arm_CSEL X4 X5 X4 Condition_GE *)
  w 0x8b0600a5;         (* arm_ADD X5 X5 X6 *)
  w 0x91000821;         (* arm_ADD X1 X1 (rvalue (word 2)) *)
  w 0xf27f00bf;         (* arm_TST X5 (rvalue (word 2)) *)
  w 0x9341fca5;         (* arm_ASR X5 X5 1 *)
  w 0x9a9f1086;         (* arm_CSEL X6 X4 XZR Condition_NE *)
  w 0xfa5f1028;         (* arm_CCMP X1 XZR (word 8) Condition_NE *)
  w 0xda81b421;         (* arm_CNEG X1 X1 Condition_GE *)
  w 0xda86b4c6;         (* arm_CNEG X6 X6 Condition_GE *)
  w 0x9a84a0a4;         (* arm_CSEL X4 X5 X4 Condition_GE *)
  w 0x8b0600a5;         (* arm_ADD X5 X5 X6 *)
  w 0x91000821;         (* arm_ADD X1 X1 (rvalue (word 2)) *)
  w 0x9341fca5;         (* arm_ASR X5 X5 1 *)
  w 0x91440088;         (* arm_ADD X8 X4 (rvalue (word 1048576)) *)
  w 0x9355a508;         (* arm_SBFM X8 X8 21 41 *)
  w 0xd2a0020b;         (* arm_MOVZ X11 (word 16) 16 *)
  w 0x8b0b556b;         (* arm_ADD X11 X11 (Shiftedreg X11 LSL 21) *)
  w 0x8b0b0089;         (* arm_ADD X9 X4 X11 *)
  w 0x936afd29;         (* arm_ASR X9 X9 42 *)
  w 0x914400aa;         (* arm_ADD X10 X5 (rvalue (word 1048576)) *)
  w 0x9355a54a;         (* arm_SBFM X10 X10 21 41 *)
  w 0x8b0b00ab;         (* arm_ADD X11 X5 X11 *)
  w 0x936afd6b;         (* arm_ASR X11 X11 42 *)
  w 0x9b027d06;         (* arm_MUL X6 X8 X2 *)
  w 0x9b037d27;         (* arm_MUL X7 X9 X3 *)
  w 0x9b027d42;         (* arm_MUL X2 X10 X2 *)
  w 0x9b037d63;         (* arm_MUL X3 X11 X3 *)
  w 0x8b0700c4;         (* arm_ADD X4 X6 X7 *)
  w 0x8b030045;         (* arm_ADD X5 X2 X3 *)
  w 0x9354fc82;         (* arm_ASR X2 X4 20 *)
  w 0x9354fca3;         (* arm_ASR X3 X5 20 *)
  w 0x92404c44;         (* arm_AND X4 X2 (rvalue (word 1048575)) *)
  w 0xb2575884;         (* arm_ORR X4 X4 (rvalue (word 18446741874686296064)) *)
  w 0x92404c65;         (* arm_AND X5 X3 (rvalue (word 1048575)) *)
  w 0xb24204a5;         (* arm_ORR X5 X5 (rvalue (word 13835058055282163712)) *)
  w 0xf24000bf;         (* arm_TST X5 (rvalue (word 1)) *)
  w 0x9a9f1086;         (* arm_CSEL X6 X4 XZR Condition_NE *)
  w 0xfa5f1028;         (* arm_CCMP X1 XZR (word 8) Condition_NE *)
  w 0xda81b421;         (* arm_CNEG X1 X1 Condition_GE *)
  w 0xda86b4c6;         (* arm_CNEG X6 X6 Condition_GE *)
  w 0x9a84a0a4;         (* arm_CSEL X4 X5 X4 Condition_GE *)
  w 0x8b0600a5;         (* arm_ADD X5 X5 X6 *)
  w 0x91000821;         (* arm_ADD X1 X1 (rvalue (word 2)) *)
  w 0xf27f00bf;         (* arm_TST X5 (rvalue (word 2)) *)
  w 0x9341fca5;         (* arm_ASR X5 X5 1 *)
  w 0x9a9f1086;         (* arm_CSEL X6 X4 XZR Condition_NE *)
  w 0xfa5f1028;         (* arm_CCMP X1 XZR (word 8) Condition_NE *)
  w 0xda81b421;         (* arm_CNEG X1 X1 Condition_GE *)
  w 0xda86b4c6;         (* arm_CNEG X6 X6 Condition_GE *)
  w 0x9a84a0a4;         (* arm_CSEL X4 X5 X4 Condition_GE *)
  w 0x8b0600a5;         (* arm_ADD X5 X5 X6 *)
  w 0x91000821;         (* arm_ADD X1 X1 (rvalue (word 2)) *)
  w 0xf27f00bf;         (* arm_TST X5 (rvalue (word 2)) *)
  w 0x9341fca5;         (* arm_ASR X5 X5 1 *)
  w 0x9a9f1086;         (* arm_CSEL X6 X4 XZR Condition_NE *)
  w 0xfa5f1028;         (* arm_CCMP X1 XZR (word 8) Condition_NE *)
  w 0xda81b421;         (* arm_CNEG X1 X1 Condition_GE *)
  w 0xda86b4c6;         (* arm_CNEG X6 X6 Condition_GE *)
  w 0x9a84a0a4;         (* arm_CSEL X4 X5 X4 Condition_GE *)
  w 0x8b0600a5;         (* arm_ADD X5 X5 X6 *)
  w 0x91000821;         (* arm_ADD X1 X1 (rvalue (word 2)) *)
  w 0xf27f00bf;         (* arm_TST X5 (rvalue (word 2)) *)
  w 0x9341fca5;         (* arm_ASR X5 X5 1 *)
  w 0x9a9f1086;         (* arm_CSEL X6 X4 XZR Condition_NE *)
  w 0xfa5f1028;         (* arm_CCMP X1 XZR (word 8) Condition_NE *)
  w 0xda81b421;         (* arm_CNEG X1 X1 Condition_GE *)
  w 0xda86b4c6;         (* arm_CNEG X6 X6 Condition_GE *)
  w 0x9a84a0a4;         (* arm_CSEL X4 X5 X4 Condition_GE *)
  w 0x8b0600a5;         (* arm_ADD X5 X5 X6 *)
  w 0x91000821;         (* arm_ADD X1 X1 (rvalue (word 2)) *)
  w 0xf27f00bf;         (* arm_TST X5 (rvalue (word 2)) *)
  w 0x9341fca5;         (* arm_ASR X5 X5 1 *)
  w 0x9a9f1086;         (* arm_CSEL X6 X4 XZR Condition_NE *)
  w 0xfa5f1028;         (* arm_CCMP X1 XZR (word 8) Condition_NE *)
  w 0xda81b421;         (* arm_CNEG X1 X1 Condition_GE *)
  w 0xda86b4c6;         (* arm_CNEG X6 X6 Condition_GE *)
  w 0x9a84a0a4;         (* arm_CSEL X4 X5 X4 Condition_GE *)
  w 0x8b0600a5;         (* arm_ADD X5 X5 X6 *)
  w 0x91000821;         (* arm_ADD X1 X1 (rvalue (word 2)) *)
  w 0xf27f00bf;         (* arm_TST X5 (rvalue (word 2)) *)
  w 0x9341fca5;         (* arm_ASR X5 X5 1 *)
  w 0x9a9f1086;         (* arm_CSEL X6 X4 XZR Condition_NE *)
  w 0xfa5f1028;         (* arm_CCMP X1 XZR (word 8) Condition_NE *)
  w 0xda81b421;         (* arm_CNEG X1 X1 Condition_GE *)
  w 0xda86b4c6;         (* arm_CNEG X6 X6 Condition_GE *)
  w 0x9a84a0a4;         (* arm_CSEL X4 X5 X4 Condition_GE *)
  w 0x8b0600a5;         (* arm_ADD X5 X5 X6 *)
  w 0x91000821;         (* arm_ADD X1 X1 (rvalue (word 2)) *)
  w 0xf27f00bf;         (* arm_TST X5 (rvalue (word 2)) *)
  w 0x9341fca5;         (* arm_ASR X5 X5 1 *)
  w 0x9a9f1086;         (* arm_CSEL X6 X4 XZR Condition_NE *)
  w 0xfa5f1028;         (* arm_CCMP X1 XZR (word 8) Condition_NE *)
  w 0xda81b421;         (* arm_CNEG X1 X1 Condition_GE *)
  w 0xda86b4c6;         (* arm_CNEG X6 X6 Condition_GE *)
  w 0x9a84a0a4;         (* arm_CSEL X4 X5 X4 Condition_GE *)
  w 0x8b0600a5;         (* arm_ADD X5 X5 X6 *)
  w 0x91000821;         (* arm_ADD X1 X1 (rvalue (word 2)) *)
  w 0xf27f00bf;         (* arm_TST X5 (rvalue (word 2)) *)
  w 0x9341fca5;         (* arm_ASR X5 X5 1 *)
  w 0x9a9f1086;         (* arm_CSEL X6 X4 XZR Condition_NE *)
  w 0xfa5f1028;         (* arm_CCMP X1 XZR (word 8) Condition_NE *)
  w 0xda81b421;         (* arm_CNEG X1 X1 Condition_GE *)
  w 0xda86b4c6;         (* arm_CNEG X6 X6 Condition_GE *)
  w 0x9a84a0a4;         (* arm_CSEL X4 X5 X4 Condition_GE *)
  w 0x8b0600a5;         (* arm_ADD X5 X5 X6 *)
  w 0x91000821;         (* arm_ADD X1 X1 (rvalue (word 2)) *)
  w 0xf27f00bf;         (* arm_TST X5 (rvalue (word 2)) *)
  w 0x9341fca5;         (* arm_ASR X5 X5 1 *)
  w 0x9a9f1086;         (* arm_CSEL X6 X4 XZR Condition_NE *)
  w 0xfa5f1028;         (* arm_CCMP X1 XZR (word 8) Condition_NE *)
  w 0xda81b421;         (* arm_CNEG X1 X1 Condition_GE *)
  w 0xda86b4c6;         (* arm_CNEG X6 X6 Condition_GE *)
  w 0x9a84a0a4;         (* arm_CSEL X4 X5 X4 Condition_GE *)
  w 0x8b0600a5;         (* arm_ADD X5 X5 X6 *)
  w 0x91000821;         (* arm_ADD X1 X1 (rvalue (word 2)) *)
  w 0xf27f00bf;         (* arm_TST X5 (rvalue (word 2)) *)
  w 0x9341fca5;         (* arm_ASR X5 X5 1 *)
  w 0x9a9f1086;         (* arm_CSEL X6 X4 XZR Condition_NE *)
  w 0xfa5f1028;         (* arm_CCMP X1 XZR (word 8) Condition_NE *)
  w 0xda81b421;         (* arm_CNEG X1 X1 Condition_GE *)
  w 0xda86b4c6;         (* arm_CNEG X6 X6 Condition_GE *)
  w 0x9a84a0a4;         (* arm_CSEL X4 X5 X4 Condition_GE *)
  w 0x8b0600a5;         (* arm_ADD X5 X5 X6 *)
  w 0x91000821;         (* arm_ADD X1 X1 (rvalue (word 2)) *)
  w 0xf27f00bf;         (* arm_TST X5 (rvalue (word 2)) *)
  w 0x9341fca5;         (* arm_ASR X5 X5 1 *)
  w 0x9a9f1086;         (* arm_CSEL X6 X4 XZR Condition_NE *)
  w 0xfa5f1028;         (* arm_CCMP X1 XZR (word 8) Condition_NE *)
  w 0xda81b421;         (* arm_CNEG X1 X1 Condition_GE *)
  w 0xda86b4c6;         (* arm_CNEG X6 X6 Condition_GE *)
  w 0x9a84a0a4;         (* arm_CSEL X4 X5 X4 Condition_GE *)
  w 0x8b0600a5;         (* arm_ADD X5 X5 X6 *)
  w 0x91000821;         (* arm_ADD X1 X1 (rvalue (word 2)) *)
  w 0xf27f00bf;         (* arm_TST X5 (rvalue (word 2)) *)
  w 0x9341fca5;         (* arm_ASR X5 X5 1 *)
  w 0x9a9f1086;         (* arm_CSEL X6 X4 XZR Condition_NE *)
  w 0xfa5f1028;         (* arm_CCMP X1 XZR (word 8) Condition_NE *)
  w 0xda81b421;         (* arm_CNEG X1 X1 Condition_GE *)
  w 0xda86b4c6;         (* arm_CNEG X6 X6 Condition_GE *)
  w 0x9a84a0a4;         (* arm_CSEL X4 X5 X4 Condition_GE *)
  w 0x8b0600a5;         (* arm_ADD X5 X5 X6 *)
  w 0x91000821;         (* arm_ADD X1 X1 (rvalue (word 2)) *)
  w 0xf27f00bf;         (* arm_TST X5 (rvalue (word 2)) *)
  w 0x9341fca5;         (* arm_ASR X5 X5 1 *)
  w 0x9a9f1086;         (* arm_CSEL X6 X4 XZR Condition_NE *)
  w 0xfa5f1028;         (* arm_CCMP X1 XZR (word 8) Condition_NE *)
  w 0xda81b421;         (* arm_CNEG X1 X1 Condition_GE *)
  w 0xda86b4c6;         (* arm_CNEG X6 X6 Condition_GE *)
  w 0x9a84a0a4;         (* arm_CSEL X4 X5 X4 Condition_GE *)
  w 0x8b0600a5;         (* arm_ADD X5 X5 X6 *)
  w 0x91000821;         (* arm_ADD X1 X1 (rvalue (word 2)) *)
  w 0xf27f00bf;         (* arm_TST X5 (rvalue (word 2)) *)
  w 0x9341fca5;         (* arm_ASR X5 X5 1 *)
  w 0x9a9f1086;         (* arm_CSEL X6 X4 XZR Condition_NE *)
  w 0xfa5f1028;         (* arm_CCMP X1 XZR (word 8) Condition_NE *)
  w 0xda81b421;         (* arm_CNEG X1 X1 Condition_GE *)
  w 0xda86b4c6;         (* arm_CNEG X6 X6 Condition_GE *)
  w 0x9a84a0a4;         (* arm_CSEL X4 X5 X4 Condition_GE *)
  w 0x8b0600a5;         (* arm_ADD X5 X5 X6 *)
  w 0x91000821;         (* arm_ADD X1 X1 (rvalue (word 2)) *)
  w 0xf27f00bf;         (* arm_TST X5 (rvalue (word 2)) *)
  w 0x9341fca5;         (* arm_ASR X5 X5 1 *)
  w 0x9a9f1086;         (* arm_CSEL X6 X4 XZR Condition_NE *)
  w 0xfa5f1028;         (* arm_CCMP X1 XZR (word 8) Condition_NE *)
  w 0xda81b421;         (* arm_CNEG X1 X1 Condition_GE *)
  w 0xda86b4c6;         (* arm_CNEG X6 X6 Condition_GE *)
  w 0x9a84a0a4;         (* arm_CSEL X4 X5 X4 Condition_GE *)
  w 0x8b0600a5;         (* arm_ADD X5 X5 X6 *)
  w 0x91000821;         (* arm_ADD X1 X1 (rvalue (word 2)) *)
  w 0xf27f00bf;         (* arm_TST X5 (rvalue (word 2)) *)
  w 0x9341fca5;         (* arm_ASR X5 X5 1 *)
  w 0x9a9f1086;         (* arm_CSEL X6 X4 XZR Condition_NE *)
  w 0xfa5f1028;         (* arm_CCMP X1 XZR (word 8) Condition_NE *)
  w 0xda81b421;         (* arm_CNEG X1 X1 Condition_GE *)
  w 0xda86b4c6;         (* arm_CNEG X6 X6 Condition_GE *)
  w 0x9a84a0a4;         (* arm_CSEL X4 X5 X4 Condition_GE *)
  w 0x8b0600a5;         (* arm_ADD X5 X5 X6 *)
  w 0x91000821;         (* arm_ADD X1 X1 (rvalue (word 2)) *)
  w 0xf27f00bf;         (* arm_TST X5 (rvalue (word 2)) *)
  w 0x9341fca5;         (* arm_ASR X5 X5 1 *)
  w 0x9a9f1086;         (* arm_CSEL X6 X4 XZR Condition_NE *)
  w 0xfa5f1028;         (* arm_CCMP X1 XZR (word 8) Condition_NE *)
  w 0xda81b421;         (* arm_CNEG X1 X1 Condition_GE *)
  w 0xda86b4c6;         (* arm_CNEG X6 X6 Condition_GE *)
  w 0x9a84a0a4;         (* arm_CSEL X4 X5 X4 Condition_GE *)
  w 0x8b0600a5;         (* arm_ADD X5 X5 X6 *)
  w 0x91000821;         (* arm_ADD X1 X1 (rvalue (word 2)) *)
  w 0xf27f00bf;         (* arm_TST X5 (rvalue (word 2)) *)
  w 0x9341fca5;         (* arm_ASR X5 X5 1 *)
  w 0x9a9f1086;         (* arm_CSEL X6 X4 XZR Condition_NE *)
  w 0xfa5f1028;         (* arm_CCMP X1 XZR (word 8) Condition_NE *)
  w 0xda81b421;         (* arm_CNEG X1 X1 Condition_GE *)
  w 0xda86b4c6;         (* arm_CNEG X6 X6 Condition_GE *)
  w 0x9a84a0a4;         (* arm_CSEL X4 X5 X4 Condition_GE *)
  w 0x8b0600a5;         (* arm_ADD X5 X5 X6 *)
  w 0x91000821;         (* arm_ADD X1 X1 (rvalue (word 2)) *)
  w 0xf27f00bf;         (* arm_TST X5 (rvalue (word 2)) *)
  w 0x9341fca5;         (* arm_ASR X5 X5 1 *)
  w 0x9a9f1086;         (* arm_CSEL X6 X4 XZR Condition_NE *)
  w 0xfa5f1028;         (* arm_CCMP X1 XZR (word 8) Condition_NE *)
  w 0xda81b421;         (* arm_CNEG X1 X1 Condition_GE *)
  w 0xda86b4c6;         (* arm_CNEG X6 X6 Condition_GE *)
  w 0x9a84a0a4;         (* arm_CSEL X4 X5 X4 Condition_GE *)
  w 0x8b0600a5;         (* arm_ADD X5 X5 X6 *)
  w 0x91000821;         (* arm_ADD X1 X1 (rvalue (word 2)) *)
  w 0xf27f00bf;         (* arm_TST X5 (rvalue (word 2)) *)
  w 0x9341fca5;         (* arm_ASR X5 X5 1 *)
  w 0x9a9f1086;         (* arm_CSEL X6 X4 XZR Condition_NE *)
  w 0xfa5f1028;         (* arm_CCMP X1 XZR (word 8) Condition_NE *)
  w 0xda81b421;         (* arm_CNEG X1 X1 Condition_GE *)
  w 0xda86b4c6;         (* arm_CNEG X6 X6 Condition_GE *)
  w 0x9a84a0a4;         (* arm_CSEL X4 X5 X4 Condition_GE *)
  w 0x8b0600a5;         (* arm_ADD X5 X5 X6 *)
  w 0x91000821;         (* arm_ADD X1 X1 (rvalue (word 2)) *)
  w 0x9341fca5;         (* arm_ASR X5 X5 1 *)
  w 0x9144008c;         (* arm_ADD X12 X4 (rvalue (word 1048576)) *)
  w 0x9355a58c;         (* arm_SBFM X12 X12 21 41 *)
  w 0xd2a0020f;         (* arm_MOVZ X15 (word 16) 16 *)
  w 0x8b0f55ef;         (* arm_ADD X15 X15 (Shiftedreg X15 LSL 21) *)
  w 0x8b0f008d;         (* arm_ADD X13 X4 X15 *)
  w 0x936afdad;         (* arm_ASR X13 X13 42 *)
  w 0x914400ae;         (* arm_ADD X14 X5 (rvalue (word 1048576)) *)
  w 0x9355a5ce;         (* arm_SBFM X14 X14 21 41 *)
  w 0x8b0f00af;         (* arm_ADD X15 X5 X15 *)
  w 0x936afdef;         (* arm_ASR X15 X15 42 *)
  w 0x9b027d86;         (* arm_MUL X6 X12 X2 *)
  w 0x9b037da7;         (* arm_MUL X7 X13 X3 *)
  w 0x9b027dc2;         (* arm_MUL X2 X14 X2 *)
  w 0x9b037de3;         (* arm_MUL X3 X15 X3 *)
  w 0x8b0700c4;         (* arm_ADD X4 X6 X7 *)
  w 0x8b030045;         (* arm_ADD X5 X2 X3 *)
  w 0x9354fc82;         (* arm_ASR X2 X4 20 *)
  w 0x9354fca3;         (* arm_ASR X3 X5 20 *)
  w 0x92404c44;         (* arm_AND X4 X2 (rvalue (word 1048575)) *)
  w 0xb2575884;         (* arm_ORR X4 X4 (rvalue (word 18446741874686296064)) *)
  w 0x92404c65;         (* arm_AND X5 X3 (rvalue (word 1048575)) *)
  w 0xb24204a5;         (* arm_ORR X5 X5 (rvalue (word 13835058055282163712)) *)
  w 0xf24000bf;         (* arm_TST X5 (rvalue (word 1)) *)
  w 0x9a9f1086;         (* arm_CSEL X6 X4 XZR Condition_NE *)
  w 0xfa5f1028;         (* arm_CCMP X1 XZR (word 8) Condition_NE *)
  w 0xda81b421;         (* arm_CNEG X1 X1 Condition_GE *)
  w 0xda86b4c6;         (* arm_CNEG X6 X6 Condition_GE *)
  w 0x9a84a0a4;         (* arm_CSEL X4 X5 X4 Condition_GE *)
  w 0x8b0600a5;         (* arm_ADD X5 X5 X6 *)
  w 0x91000821;         (* arm_ADD X1 X1 (rvalue (word 2)) *)
  w 0xf27f00bf;         (* arm_TST X5 (rvalue (word 2)) *)
  w 0x9341fca5;         (* arm_ASR X5 X5 1 *)
  w 0x9a9f1086;         (* arm_CSEL X6 X4 XZR Condition_NE *)
  w 0xfa5f1028;         (* arm_CCMP X1 XZR (word 8) Condition_NE *)
  w 0xda81b421;         (* arm_CNEG X1 X1 Condition_GE *)
  w 0xda86b4c6;         (* arm_CNEG X6 X6 Condition_GE *)
  w 0x9a84a0a4;         (* arm_CSEL X4 X5 X4 Condition_GE *)
  w 0x8b0600a5;         (* arm_ADD X5 X5 X6 *)
  w 0x91000821;         (* arm_ADD X1 X1 (rvalue (word 2)) *)
  w 0xf27f00bf;         (* arm_TST X5 (rvalue (word 2)) *)
  w 0x9341fca5;         (* arm_ASR X5 X5 1 *)
  w 0x9a9f1086;         (* arm_CSEL X6 X4 XZR Condition_NE *)
  w 0xfa5f1028;         (* arm_CCMP X1 XZR (word 8) Condition_NE *)
  w 0xda81b421;         (* arm_CNEG X1 X1 Condition_GE *)
  w 0xda86b4c6;         (* arm_CNEG X6 X6 Condition_GE *)
  w 0x9a84a0a4;         (* arm_CSEL X4 X5 X4 Condition_GE *)
  w 0x8b0600a5;         (* arm_ADD X5 X5 X6 *)
  w 0x91000821;         (* arm_ADD X1 X1 (rvalue (word 2)) *)
  w 0xf27f00bf;         (* arm_TST X5 (rvalue (word 2)) *)
  w 0x9341fca5;         (* arm_ASR X5 X5 1 *)
  w 0x9a9f1086;         (* arm_CSEL X6 X4 XZR Condition_NE *)
  w 0xfa5f1028;         (* arm_CCMP X1 XZR (word 8) Condition_NE *)
  w 0xda81b421;         (* arm_CNEG X1 X1 Condition_GE *)
  w 0xda86b4c6;         (* arm_CNEG X6 X6 Condition_GE *)
  w 0x9a84a0a4;         (* arm_CSEL X4 X5 X4 Condition_GE *)
  w 0x8b0600a5;         (* arm_ADD X5 X5 X6 *)
  w 0x91000821;         (* arm_ADD X1 X1 (rvalue (word 2)) *)
  w 0xf27f00bf;         (* arm_TST X5 (rvalue (word 2)) *)
  w 0x9341fca5;         (* arm_ASR X5 X5 1 *)
  w 0x9a9f1086;         (* arm_CSEL X6 X4 XZR Condition_NE *)
  w 0xfa5f1028;         (* arm_CCMP X1 XZR (word 8) Condition_NE *)
  w 0xda81b421;         (* arm_CNEG X1 X1 Condition_GE *)
  w 0xda86b4c6;         (* arm_CNEG X6 X6 Condition_GE *)
  w 0x9a84a0a4;         (* arm_CSEL X4 X5 X4 Condition_GE *)
  w 0x8b0600a5;         (* arm_ADD X5 X5 X6 *)
  w 0x91000821;         (* arm_ADD X1 X1 (rvalue (word 2)) *)
  w 0xf27f00bf;         (* arm_TST X5 (rvalue (word 2)) *)
  w 0x9341fca5;         (* arm_ASR X5 X5 1 *)
  w 0x9a9f1086;         (* arm_CSEL X6 X4 XZR Condition_NE *)
  w 0xfa5f1028;         (* arm_CCMP X1 XZR (word 8) Condition_NE *)
  w 0xda81b421;         (* arm_CNEG X1 X1 Condition_GE *)
  w 0xda86b4c6;         (* arm_CNEG X6 X6 Condition_GE *)
  w 0x9a84a0a4;         (* arm_CSEL X4 X5 X4 Condition_GE *)
  w 0x8b0600a5;         (* arm_ADD X5 X5 X6 *)
  w 0x91000821;         (* arm_ADD X1 X1 (rvalue (word 2)) *)
  w 0xf27f00bf;         (* arm_TST X5 (rvalue (word 2)) *)
  w 0x9341fca5;         (* arm_ASR X5 X5 1 *)
  w 0x9a9f1086;         (* arm_CSEL X6 X4 XZR Condition_NE *)
  w 0xfa5f1028;         (* arm_CCMP X1 XZR (word 8) Condition_NE *)
  w 0xda81b421;         (* arm_CNEG X1 X1 Condition_GE *)
  w 0xda86b4c6;         (* arm_CNEG X6 X6 Condition_GE *)
  w 0x9a84a0a4;         (* arm_CSEL X4 X5 X4 Condition_GE *)
  w 0x8b0600a5;         (* arm_ADD X5 X5 X6 *)
  w 0x91000821;         (* arm_ADD X1 X1 (rvalue (word 2)) *)
  w 0xf27f00bf;         (* arm_TST X5 (rvalue (word 2)) *)
  w 0x9341fca5;         (* arm_ASR X5 X5 1 *)
  w 0x9a9f1086;         (* arm_CSEL X6 X4 XZR Condition_NE *)
  w 0xfa5f1028;         (* arm_CCMP X1 XZR (word 8) Condition_NE *)
  w 0xda81b421;         (* arm_CNEG X1 X1 Condition_GE *)
  w 0xda86b4c6;         (* arm_CNEG X6 X6 Condition_GE *)
  w 0x9a84a0a4;         (* arm_CSEL X4 X5 X4 Condition_GE *)
  w 0x8b0600a5;         (* arm_ADD X5 X5 X6 *)
  w 0x91000821;         (* arm_ADD X1 X1 (rvalue (word 2)) *)
  w 0xf27f00bf;         (* arm_TST X5 (rvalue (word 2)) *)
  w 0x9341fca5;         (* arm_ASR X5 X5 1 *)
  w 0x9a9f1086;         (* arm_CSEL X6 X4 XZR Condition_NE *)
  w 0xfa5f1028;         (* arm_CCMP X1 XZR (word 8) Condition_NE *)
  w 0xda81b421;         (* arm_CNEG X1 X1 Condition_GE *)
  w 0xda86b4c6;         (* arm_CNEG X6 X6 Condition_GE *)
  w 0x9a84a0a4;         (* arm_CSEL X4 X5 X4 Condition_GE *)
  w 0x8b0600a5;         (* arm_ADD X5 X5 X6 *)
  w 0x91000821;         (* arm_ADD X1 X1 (rvalue (word 2)) *)
  w 0xf27f00bf;         (* arm_TST X5 (rvalue (word 2)) *)
  w 0x9341fca5;         (* arm_ASR X5 X5 1 *)
  w 0x9a9f1086;         (* arm_CSEL X6 X4 XZR Condition_NE *)
  w 0xfa5f1028;         (* arm_CCMP X1 XZR (word 8) Condition_NE *)
  w 0xda81b421;         (* arm_CNEG X1 X1 Condition_GE *)
  w 0xda86b4c6;         (* arm_CNEG X6 X6 Condition_GE *)
  w 0x9a84a0a4;         (* arm_CSEL X4 X5 X4 Condition_GE *)
  w 0x8b0600a5;         (* arm_ADD X5 X5 X6 *)
  w 0x91000821;         (* arm_ADD X1 X1 (rvalue (word 2)) *)
  w 0xf27f00bf;         (* arm_TST X5 (rvalue (word 2)) *)
  w 0x9341fca5;         (* arm_ASR X5 X5 1 *)
  w 0x9b087d82;         (* arm_MUL X2 X12 X8 *)
  w 0x9b097d83;         (* arm_MUL X3 X12 X9 *)
  w 0x9b087dc6;         (* arm_MUL X6 X14 X8 *)
  w 0x9b097dc7;         (* arm_MUL X7 X14 X9 *)
  w 0x9b0a09a8;         (* arm_MADD X8 X13 X10 X2 *)
  w 0x9b0b0da9;         (* arm_MADD X9 X13 X11 X3 *)
  w 0x9b0a19f0;         (* arm_MADD X16 X15 X10 X6 *)
  w 0x9b0b1df1;         (* arm_MADD X17 X15 X11 X7 *)
  w 0x9a9f1086;         (* arm_CSEL X6 X4 XZR Condition_NE *)
  w 0xfa5f1028;         (* arm_CCMP X1 XZR (word 8) Condition_NE *)
  w 0xda81b421;         (* arm_CNEG X1 X1 Condition_GE *)
  w 0xda86b4c6;         (* arm_CNEG X6 X6 Condition_GE *)
  w 0x9a84a0a4;         (* arm_CSEL X4 X5 X4 Condition_GE *)
  w 0x8b0600a5;         (* arm_ADD X5 X5 X6 *)
  w 0x91000821;         (* arm_ADD X1 X1 (rvalue (word 2)) *)
  w 0xf27f00bf;         (* arm_TST X5 (rvalue (word 2)) *)
  w 0x9341fca5;         (* arm_ASR X5 X5 1 *)
  w 0x9a9f1086;         (* arm_CSEL X6 X4 XZR Condition_NE *)
  w 0xfa5f1028;         (* arm_CCMP X1 XZR (word 8) Condition_NE *)
  w 0xda81b421;         (* arm_CNEG X1 X1 Condition_GE *)
  w 0xda86b4c6;         (* arm_CNEG X6 X6 Condition_GE *)
  w 0x9a84a0a4;         (* arm_CSEL X4 X5 X4 Condition_GE *)
  w 0x8b0600a5;         (* arm_ADD X5 X5 X6 *)
  w 0x91000821;         (* arm_ADD X1 X1 (rvalue (word 2)) *)
  w 0xf27f00bf;         (* arm_TST X5 (rvalue (word 2)) *)
  w 0x9341fca5;         (* arm_ASR X5 X5 1 *)
  w 0x9a9f1086;         (* arm_CSEL X6 X4 XZR Condition_NE *)
  w 0xfa5f1028;         (* arm_CCMP X1 XZR (word 8) Condition_NE *)
  w 0xda81b421;         (* arm_CNEG X1 X1 Condition_GE *)
  w 0xda86b4c6;         (* arm_CNEG X6 X6 Condition_GE *)
  w 0x9a84a0a4;         (* arm_CSEL X4 X5 X4 Condition_GE *)
  w 0x8b0600a5;         (* arm_ADD X5 X5 X6 *)
  w 0x91000821;         (* arm_ADD X1 X1 (rvalue (word 2)) *)
  w 0xf27f00bf;         (* arm_TST X5 (rvalue (word 2)) *)
  w 0x9341fca5;         (* arm_ASR X5 X5 1 *)
  w 0x9a9f1086;         (* arm_CSEL X6 X4 XZR Condition_NE *)
  w 0xfa5f1028;         (* arm_CCMP X1 XZR (word 8) Condition_NE *)
  w 0xda81b421;         (* arm_CNEG X1 X1 Condition_GE *)
  w 0xda86b4c6;         (* arm_CNEG X6 X6 Condition_GE *)
  w 0x9a84a0a4;         (* arm_CSEL X4 X5 X4 Condition_GE *)
  w 0x8b0600a5;         (* arm_ADD X5 X5 X6 *)
  w 0x91000821;         (* arm_ADD X1 X1 (rvalue (word 2)) *)
  w 0xf27f00bf;         (* arm_TST X5 (rvalue (word 2)) *)
  w 0x9341fca5;         (* arm_ASR X5 X5 1 *)
  w 0x9a9f1086;         (* arm_CSEL X6 X4 XZR Condition_NE *)
  w 0xfa5f1028;         (* arm_CCMP X1 XZR (word 8) Condition_NE *)
  w 0xda81b421;         (* arm_CNEG X1 X1 Condition_GE *)
  w 0xda86b4c6;         (* arm_CNEG X6 X6 Condition_GE *)
  w 0x9a84a0a4;         (* arm_CSEL X4 X5 X4 Condition_GE *)
  w 0x8b0600a5;         (* arm_ADD X5 X5 X6 *)
  w 0x91000821;         (* arm_ADD X1 X1 (rvalue (word 2)) *)
  w 0xf27f00bf;         (* arm_TST X5 (rvalue (word 2)) *)
  w 0x9341fca5;         (* arm_ASR X5 X5 1 *)
  w 0x9a9f1086;         (* arm_CSEL X6 X4 XZR Condition_NE *)
  w 0xfa5f1028;         (* arm_CCMP X1 XZR (word 8) Condition_NE *)
  w 0xda81b421;         (* arm_CNEG X1 X1 Condition_GE *)
  w 0xda86b4c6;         (* arm_CNEG X6 X6 Condition_GE *)
  w 0x9a84a0a4;         (* arm_CSEL X4 X5 X4 Condition_GE *)
  w 0x8b0600a5;         (* arm_ADD X5 X5 X6 *)
  w 0x91000821;         (* arm_ADD X1 X1 (rvalue (word 2)) *)
  w 0xf27f00bf;         (* arm_TST X5 (rvalue (word 2)) *)
  w 0x9341fca5;         (* arm_ASR X5 X5 1 *)
  w 0x9a9f1086;         (* arm_CSEL X6 X4 XZR Condition_NE *)
  w 0xfa5f1028;         (* arm_CCMP X1 XZR (word 8) Condition_NE *)
  w 0xda81b421;         (* arm_CNEG X1 X1 Condition_GE *)
  w 0xda86b4c6;         (* arm_CNEG X6 X6 Condition_GE *)
  w 0x9a84a0a4;         (* arm_CSEL X4 X5 X4 Condition_GE *)
  w 0x8b0600a5;         (* arm_ADD X5 X5 X6 *)
  w 0x91000821;         (* arm_ADD X1 X1 (rvalue (word 2)) *)
  w 0xf27f00bf;         (* arm_TST X5 (rvalue (word 2)) *)
  w 0x9341fca5;         (* arm_ASR X5 X5 1 *)
  w 0x9a9f1086;         (* arm_CSEL X6 X4 XZR Condition_NE *)
  w 0xfa5f1028;         (* arm_CCMP X1 XZR (word 8) Condition_NE *)
  w 0xda81b421;         (* arm_CNEG X1 X1 Condition_GE *)
  w 0xda86b4c6;         (* arm_CNEG X6 X6 Condition_GE *)
  w 0x9a84a0a4;         (* arm_CSEL X4 X5 X4 Condition_GE *)
  w 0x8b0600a5;         (* arm_ADD X5 X5 X6 *)
  w 0x91000821;         (* arm_ADD X1 X1 (rvalue (word 2)) *)
  w 0xf27f00bf;         (* arm_TST X5 (rvalue (word 2)) *)
  w 0x9341fca5;         (* arm_ASR X5 X5 1 *)
  w 0x9a9f1086;         (* arm_CSEL X6 X4 XZR Condition_NE *)
  w 0xfa5f1028;         (* arm_CCMP X1 XZR (word 8) Condition_NE *)
  w 0xda81b421;         (* arm_CNEG X1 X1 Condition_GE *)
  w 0xda86b4c6;         (* arm_CNEG X6 X6 Condition_GE *)
  w 0x9a84a0a4;         (* arm_CSEL X4 X5 X4 Condition_GE *)
  w 0x8b0600a5;         (* arm_ADD X5 X5 X6 *)
  w 0x91000821;         (* arm_ADD X1 X1 (rvalue (word 2)) *)
  w 0x9341fca5;         (* arm_ASR X5 X5 1 *)
  w 0x9144008c;         (* arm_ADD X12 X4 (rvalue (word 1048576)) *)
  w 0x9356a98c;         (* arm_SBFM X12 X12 22 42 *)
  w 0xd2a0020f;         (* arm_MOVZ X15 (word 16) 16 *)
  w 0x8b0f55ef;         (* arm_ADD X15 X15 (Shiftedreg X15 LSL 21) *)
  w 0x8b0f008d;         (* arm_ADD X13 X4 X15 *)
  w 0x936bfdad;         (* arm_ASR X13 X13 43 *)
  w 0x914400ae;         (* arm_ADD X14 X5 (rvalue (word 1048576)) *)
  w 0x9356a9ce;         (* arm_SBFM X14 X14 22 42 *)
  w 0x8b0f00af;         (* arm_ADD X15 X5 X15 *)
  w 0x936bfdef;         (* arm_ASR X15 X15 43 *)
  w 0x9b08fd82;         (* arm_MNEG X2 X12 X8 *)
  w 0x9b09fd83;         (* arm_MNEG X3 X12 X9 *)
  w 0x9b08fdc4;         (* arm_MNEG X4 X14 X8 *)
  w 0x9b09fdc5;         (* arm_MNEG X5 X14 X9 *)
  w 0x9b1089aa;         (* arm_MSUB X10 X13 X16 X2 *)
  w 0x9b118dab;         (* arm_MSUB X11 X13 X17 X3 *)
  w 0x9b1091ec;         (* arm_MSUB X12 X15 X16 X4 *)
  w 0x9b1195ed;         (* arm_MSUB X13 X15 X17 X5 *)
  w 0xaa0103f6;         (* arm_MOV X22 X1 *)
  w 0xf10006b5;         (* arm_SUBS X21 X21 (rvalue (word 1)) *)
  w 0x54ff9281;         (* arm_BNE (word 2093648) *)
  w 0xf94003e0;         (* arm_LDR X0 SP (Immediate_Offset (word 0)) *)
  w 0xf94013e1;         (* arm_LDR X1 SP (Immediate_Offset (word 32)) *)
  w 0x9b0a7c00;         (* arm_MUL X0 X0 X10 *)
  w 0x9b0b0021;         (* arm_MADD X1 X1 X11 X0 *)
  w 0x937ffc20;         (* arm_ASR X0 X1 63 *)
  w 0xeb1f015f;         (* arm_CMP X10 XZR *)
  w 0xda9f53ee;         (* arm_CSETM X14 Condition_MI *)
  w 0xda8a554a;         (* arm_CNEG X10 X10 Condition_MI *)
  w 0xca0001ce;         (* arm_EOR X14 X14 X0 *)
  w 0xeb1f017f;         (* arm_CMP X11 XZR *)
  w 0xda9f53ef;         (* arm_CSETM X15 Condition_MI *)
  w 0xda8b556b;         (* arm_CNEG X11 X11 Condition_MI *)
  w 0xca0001ef;         (* arm_EOR X15 X15 X0 *)
  w 0xeb1f019f;         (* arm_CMP X12 XZR *)
  w 0xda9f53f0;         (* arm_CSETM X16 Condition_MI *)
  w 0xda8c558c;         (* arm_CNEG X12 X12 Condition_MI *)
  w 0xca000210;         (* arm_EOR X16 X16 X0 *)
  w 0xeb1f01bf;         (* arm_CMP X13 XZR *)
  w 0xda9f53f1;         (* arm_CSETM X17 Condition_MI *)
  w 0xda8d55ad;         (* arm_CNEG X13 X13 Condition_MI *)
  w 0xca000231;         (* arm_EOR X17 X17 X0 *)
  w 0x8a0e0140;         (* arm_AND X0 X10 X14 *)
  w 0x8a0f0161;         (* arm_AND X1 X11 X15 *)
  w 0x8b010009;         (* arm_ADD X9 X0 X1 *)
  w 0xf94023e7;         (* arm_LDR X7 SP (Immediate_Offset (word 64)) *)
  w 0xca0e00e1;         (* arm_EOR X1 X7 X14 *)
  w 0x9b0a7c20;         (* arm_MUL X0 X1 X10 *)
  w 0x9bca7c21;         (* arm_UMULH X1 X1 X10 *)
  w 0xab000124;         (* arm_ADDS X4 X9 X0 *)
  w 0x9a0103e2;         (* arm_ADC X2 XZR X1 *)
  w 0xf94033e8;         (* arm_LDR X8 SP (Immediate_Offset (word 96)) *)
  w 0xca0f0101;         (* arm_EOR X1 X8 X15 *)
  w 0x9b0b7c20;         (* arm_MUL X0 X1 X11 *)
  w 0x9bcb7c21;         (* arm_UMULH X1 X1 X11 *)
  w 0xab000084;         (* arm_ADDS X4 X4 X0 *)
  w 0xf90023e4;         (* arm_STR X4 SP (Immediate_Offset (word 64)) *)
  w 0x9a010042;         (* arm_ADC X2 X2 X1 *)
  w 0xf94027e7;         (* arm_LDR X7 SP (Immediate_Offset (word 72)) *)
  w 0xca0e00e1;         (* arm_EOR X1 X7 X14 *)
  w 0x9b0a7c20;         (* arm_MUL X0 X1 X10 *)
  w 0x9bca7c21;         (* arm_UMULH X1 X1 X10 *)
  w 0xab000042;         (* arm_ADDS X2 X2 X0 *)
  w 0x9a0103e6;         (* arm_ADC X6 XZR X1 *)
  w 0xf94037e8;         (* arm_LDR X8 SP (Immediate_Offset (word 104)) *)
  w 0xca0f0101;         (* arm_EOR X1 X8 X15 *)
  w 0x9b0b7c20;         (* arm_MUL X0 X1 X11 *)
  w 0x9bcb7c21;         (* arm_UMULH X1 X1 X11 *)
  w 0xab000042;         (* arm_ADDS X2 X2 X0 *)
  w 0xf90027e2;         (* arm_STR X2 SP (Immediate_Offset (word 72)) *)
  w 0x9a0100c6;         (* arm_ADC X6 X6 X1 *)
  w 0xf9402be7;         (* arm_LDR X7 SP (Immediate_Offset (word 80)) *)
  w 0xca0e00e1;         (* arm_EOR X1 X7 X14 *)
  w 0x9b0a7c20;         (* arm_MUL X0 X1 X10 *)
  w 0x9bca7c21;         (* arm_UMULH X1 X1 X10 *)
  w 0xab0000c6;         (* arm_ADDS X6 X6 X0 *)
  w 0x9a0103e5;         (* arm_ADC X5 XZR X1 *)
  w 0xf9403be8;         (* arm_LDR X8 SP (Immediate_Offset (word 112)) *)
  w 0xca0f0101;         (* arm_EOR X1 X8 X15 *)
  w 0x9b0b7c20;         (* arm_MUL X0 X1 X11 *)
  w 0x9bcb7c21;         (* arm_UMULH X1 X1 X11 *)
  w 0xab0000c6;         (* arm_ADDS X6 X6 X0 *)
  w 0xf9002be6;         (* arm_STR X6 SP (Immediate_Offset (word 80)) *)
  w 0x9a0100a5;         (* arm_ADC X5 X5 X1 *)
  w 0xf9402fe7;         (* arm_LDR X7 SP (Immediate_Offset (word 88)) *)
  w 0xca0e00e1;         (* arm_EOR X1 X7 X14 *)
  w 0x8a0a01c3;         (* arm_AND X3 X14 X10 *)
  w 0xcb0303e3;         (* arm_NEG X3 X3 *)
  w 0x9b0a7c20;         (* arm_MUL X0 X1 X10 *)
  w 0x9bca7c21;         (* arm_UMULH X1 X1 X10 *)
  w 0xab0000a5;         (* arm_ADDS X5 X5 X0 *)
  w 0x9a010063;         (* arm_ADC X3 X3 X1 *)
  w 0xf9403fe8;         (* arm_LDR X8 SP (Immediate_Offset (word 120)) *)
  w 0xca0f0101;         (* arm_EOR X1 X8 X15 *)
  w 0x8a0b01e0;         (* arm_AND X0 X15 X11 *)
  w 0xcb000063;         (* arm_SUB X3 X3 X0 *)
  w 0x9b0b7c20;         (* arm_MUL X0 X1 X11 *)
  w 0x9bcb7c21;         (* arm_UMULH X1 X1 X11 *)
  w 0xab0000a5;         (* arm_ADDS X5 X5 X0 *)
  w 0x9a010063;         (* arm_ADC X3 X3 X1 *)
  w 0x93c5fc66;         (* arm_EXTR X6 X3 X5 63 *)
  w 0xa94407e0;         (* arm_LDP X0 X1 SP (Immediate_Offset (iword (&64))) *)
  w 0xea03007f;         (* arm_TST X3 X3 *)
  w 0x9a8644c6;         (* arm_CINC X6 X6 Condition_PL *)
  w 0xd2800263;         (* arm_MOV X3 (rvalue (word 19)) *)
  w 0x9b037cc4;         (* arm_MUL X4 X6 X3 *)
  w 0x8b06fca5;         (* arm_ADD X5 X5 (Shiftedreg X6 LSL 63) *)
  w 0x9b437cc6;         (* arm_SMULH X6 X6 X3 *)
  w 0xf9402be2;         (* arm_LDR X2 SP (Immediate_Offset (word 80)) *)
  w 0xab040000;         (* arm_ADDS X0 X0 X4 *)
  w 0xba060021;         (* arm_ADCS X1 X1 X6 *)
  w 0x937ffcc6;         (* arm_ASR X6 X6 63 *)
  w 0xba060042;         (* arm_ADCS X2 X2 X6 *)
  w 0xba0600a5;         (* arm_ADCS X5 X5 X6 *)
  w 0x9a9f4063;         (* arm_CSEL X3 X3 XZR Condition_MI *)
  w 0xeb030000;         (* arm_SUBS X0 X0 X3 *)
  w 0xfa1f0021;         (* arm_SBCS X1 X1 XZR *)
  w 0xfa1f0042;         (* arm_SBCS X2 X2 XZR *)
  w 0xda1f00a5;         (* arm_SBC X5 X5 XZR *)
  w 0x9240f8a5;         (* arm_AND X5 X5 (rvalue (word 9223372036854775807)) *)
  w 0xaa1403e4;         (* arm_MOV X4 X20 *)
  w 0xa9000480;         (* arm_STP X0 X1 X4 (Immediate_Offset (iword (&0))) *)
  w 0xa9011482;         (* arm_STP X2 X5 X4 (Immediate_Offset (iword (&16))) *)
  w 0xa95213e3;         (* arm_LDP X3 X4 SP (Immediate_Offset (iword (&288))) *)
  w 0xa95023e7;         (* arm_LDP X7 X8 SP (Immediate_Offset (iword (&256))) *)
  w 0x9b077c6c;         (* arm_MUL X12 X3 X7 *)
  w 0x9bc77c6d;         (* arm_UMULH X13 X3 X7 *)
  w 0x9b087c6b;         (* arm_MUL X11 X3 X8 *)
  w 0x9bc87c6e;         (* arm_UMULH X14 X3 X8 *)
  w 0xab0b01ad;         (* arm_ADDS X13 X13 X11 *)
  w 0xa9512be9;         (* arm_LDP X9 X10 SP (Immediate_Offset (iword (&272))) *)
  w 0x9b097c6b;         (* arm_MUL X11 X3 X9 *)
  w 0x9bc97c6f;         (* arm_UMULH X15 X3 X9 *)
  w 0xba0b01ce;         (* arm_ADCS X14 X14 X11 *)
  w 0x9b0a7c6b;         (* arm_MUL X11 X3 X10 *)
  w 0x9bca7c70;         (* arm_UMULH X16 X3 X10 *)
  w 0xba0b01ef;         (* arm_ADCS X15 X15 X11 *)
  w 0x9a1f0210;         (* arm_ADC X16 X16 XZR *)
  w 0xa9531be5;         (* arm_LDP X5 X6 SP (Immediate_Offset (iword (&304))) *)
  w 0x9b077c8b;         (* arm_MUL X11 X4 X7 *)
  w 0xab0b01ad;         (* arm_ADDS X13 X13 X11 *)
  w 0x9b087c8b;         (* arm_MUL X11 X4 X8 *)
  w 0xba0b01ce;         (* arm_ADCS X14 X14 X11 *)
  w 0x9b097c8b;         (* arm_MUL X11 X4 X9 *)
  w 0xba0b01ef;         (* arm_ADCS X15 X15 X11 *)
  w 0x9b0a7c8b;         (* arm_MUL X11 X4 X10 *)
  w 0xba0b0210;         (* arm_ADCS X16 X16 X11 *)
  w 0x9bca7c83;         (* arm_UMULH X3 X4 X10 *)
  w 0x9a1f0063;         (* arm_ADC X3 X3 XZR *)
  w 0x9bc77c8b;         (* arm_UMULH X11 X4 X7 *)
  w 0xab0b01ce;         (* arm_ADDS X14 X14 X11 *)
  w 0x9bc87c8b;         (* arm_UMULH X11 X4 X8 *)
  w 0xba0b01ef;         (* arm_ADCS X15 X15 X11 *)
  w 0x9bc97c8b;         (* arm_UMULH X11 X4 X9 *)
  w 0xba0b0210;         (* arm_ADCS X16 X16 X11 *)
  w 0x9a1f0063;         (* arm_ADC X3 X3 XZR *)
  w 0x9b077cab;         (* arm_MUL X11 X5 X7 *)
  w 0xab0b01ce;         (* arm_ADDS X14 X14 X11 *)
  w 0x9b087cab;         (* arm_MUL X11 X5 X8 *)
  w 0xba0b01ef;         (* arm_ADCS X15 X15 X11 *)
  w 0x9b097cab;         (* arm_MUL X11 X5 X9 *)
  w 0xba0b0210;         (* arm_ADCS X16 X16 X11 *)
  w 0x9b0a7cab;         (* arm_MUL X11 X5 X10 *)
  w 0xba0b0063;         (* arm_ADCS X3 X3 X11 *)
  w 0x9bca7ca4;         (* arm_UMULH X4 X5 X10 *)
  w 0x9a1f0084;         (* arm_ADC X4 X4 XZR *)
  w 0x9bc77cab;         (* arm_UMULH X11 X5 X7 *)
  w 0xab0b01ef;         (* arm_ADDS X15 X15 X11 *)
  w 0x9bc87cab;         (* arm_UMULH X11 X5 X8 *)
  w 0xba0b0210;         (* arm_ADCS X16 X16 X11 *)
  w 0x9bc97cab;         (* arm_UMULH X11 X5 X9 *)
  w 0xba0b0063;         (* arm_ADCS X3 X3 X11 *)
  w 0x9a1f0084;         (* arm_ADC X4 X4 XZR *)
  w 0x9b077ccb;         (* arm_MUL X11 X6 X7 *)
  w 0xab0b01ef;         (* arm_ADDS X15 X15 X11 *)
  w 0x9b087ccb;         (* arm_MUL X11 X6 X8 *)
  w 0xba0b0210;         (* arm_ADCS X16 X16 X11 *)
  w 0x9b097ccb;         (* arm_MUL X11 X6 X9 *)
  w 0xba0b0063;         (* arm_ADCS X3 X3 X11 *)
  w 0x9b0a7ccb;         (* arm_MUL X11 X6 X10 *)
  w 0xba0b0084;         (* arm_ADCS X4 X4 X11 *)
  w 0x9bca7cc5;         (* arm_UMULH X5 X6 X10 *)
  w 0x9a1f00a5;         (* arm_ADC X5 X5 XZR *)
  w 0x9bc77ccb;         (* arm_UMULH X11 X6 X7 *)
  w 0xab0b0210;         (* arm_ADDS X16 X16 X11 *)
  w 0x9bc87ccb;         (* arm_UMULH X11 X6 X8 *)
  w 0xba0b0063;         (* arm_ADCS X3 X3 X11 *)
  w 0x9bc97ccb;         (* arm_UMULH X11 X6 X9 *)
  w 0xba0b0084;         (* arm_ADCS X4 X4 X11 *)
  w 0x9a1f00a5;         (* arm_ADC X5 X5 XZR *)
  w 0xd28004c7;         (* arm_MOV X7 (rvalue (word 38)) *)
  w 0x9b107ceb;         (* arm_MUL X11 X7 X16 *)
  w 0x9bd07ce9;         (* arm_UMULH X9 X7 X16 *)
  w 0xab0b018c;         (* arm_ADDS X12 X12 X11 *)
  w 0x9b037ceb;         (* arm_MUL X11 X7 X3 *)
  w 0x9bc37ce3;         (* arm_UMULH X3 X7 X3 *)
  w 0xba0b01ad;         (* arm_ADCS X13 X13 X11 *)
  w 0x9b047ceb;         (* arm_MUL X11 X7 X4 *)
  w 0x9bc47ce4;         (* arm_UMULH X4 X7 X4 *)
  w 0xba0b01ce;         (* arm_ADCS X14 X14 X11 *)
  w 0x9b057ceb;         (* arm_MUL X11 X7 X5 *)
  w 0x9bc57ce5;         (* arm_UMULH X5 X7 X5 *)
  w 0xba0b01ef;         (* arm_ADCS X15 X15 X11 *)
  w 0x9a9f37f0;         (* arm_CSET X16 Condition_CS *)
  w 0xab0401ef;         (* arm_ADDS X15 X15 X4 *)
  w 0x9a050210;         (* arm_ADC X16 X16 X5 *)
  w 0xab0f01ff;         (* arm_CMN X15 X15 *)
  w 0xb24101ef;         (* arm_ORR X15 X15 (rvalue (word 9223372036854775808)) *)
  w 0x9a100208;         (* arm_ADC X8 X16 X16 *)
  w 0xd2800267;         (* arm_MOV X7 (rvalue (word 19)) *)
  w 0x9b081ceb;         (* arm_MADD X11 X7 X8 X7 *)
  w 0xab0b018c;         (* arm_ADDS X12 X12 X11 *)
  w 0xba0901ad;         (* arm_ADCS X13 X13 X9 *)
  w 0xba0301ce;         (* arm_ADCS X14 X14 X3 *)
  w 0xba1f01ef;         (* arm_ADCS X15 X15 XZR *)
  w 0x9a9f30e7;         (* arm_CSEL X7 X7 XZR Condition_CC *)
  w 0xeb07018c;         (* arm_SUBS X12 X12 X7 *)
  w 0xfa1f01ad;         (* arm_SBCS X13 X13 XZR *)
  w 0xfa1f01ce;         (* arm_SBCS X14 X14 XZR *)
  w 0xda1f01ef;         (* arm_SBC X15 X15 XZR *)
  w 0x9240f9ef;         (* arm_AND X15 X15 (rvalue (word 9223372036854775807)) *)
  w 0xa90837ec;         (* arm_STP X12 X13 SP (Immediate_Offset (iword (&128))) *)
  w 0xa9093fee;         (* arm_STP X14 X15 SP (Immediate_Offset (iword (&144))) *)
  w 0xa9482fea;         (* arm_LDP X10 X11 SP (Immediate_Offset (iword (&128))) *)
  w 0x390002ea;         (* arm_STRB W10 X23 (Immediate_Offset (word 0)) *)
  w 0xd348fd4a;         (* arm_LSR X10 X10 8 *)
  w 0x390006ea;         (* arm_STRB W10 X23 (Immediate_Offset (word 1)) *)
  w 0xd348fd4a;         (* arm_LSR X10 X10 8 *)
  w 0x39000aea;         (* arm_STRB W10 X23 (Immediate_Offset (word 2)) *)
  w 0xd348fd4a;         (* arm_LSR X10 X10 8 *)
  w 0x39000eea;         (* arm_STRB W10 X23 (Immediate_Offset (word 3)) *)
  w 0xd348fd4a;         (* arm_LSR X10 X10 8 *)
  w 0x390012ea;         (* arm_STRB W10 X23 (Immediate_Offset (word 4)) *)
  w 0xd348fd4a;         (* arm_LSR X10 X10 8 *)
  w 0x390016ea;         (* arm_STRB W10 X23 (Immediate_Offset (word 5)) *)
  w 0xd348fd4a;         (* arm_LSR X10 X10 8 *)
  w 0x39001aea;         (* arm_STRB W10 X23 (Immediate_Offset (word 6)) *)
  w 0xd348fd4a;         (* arm_LSR X10 X10 8 *)
  w 0x39001eea;         (* arm_STRB W10 X23 (Immediate_Offset (word 7)) *)
  w 0x390022eb;         (* arm_STRB W11 X23 (Immediate_Offset (word 8)) *)
  w 0xd348fd6b;         (* arm_LSR X11 X11 8 *)
  w 0x390026eb;         (* arm_STRB W11 X23 (Immediate_Offset (word 9)) *)
  w 0xd348fd6b;         (* arm_LSR X11 X11 8 *)
  w 0x39002aeb;         (* arm_STRB W11 X23 (Immediate_Offset (word 10)) *)
  w 0xd348fd6b;         (* arm_LSR X11 X11 8 *)
  w 0x39002eeb;         (* arm_STRB W11 X23 (Immediate_Offset (word 11)) *)
  w 0xd348fd6b;         (* arm_LSR X11 X11 8 *)
  w 0x390032eb;         (* arm_STRB W11 X23 (Immediate_Offset (word 12)) *)
  w 0xd348fd6b;         (* arm_LSR X11 X11 8 *)
  w 0x390036eb;         (* arm_STRB W11 X23 (Immediate_Offset (word 13)) *)
  w 0xd348fd6b;         (* arm_LSR X11 X11 8 *)
  w 0x39003aeb;         (* arm_STRB W11 X23 (Immediate_Offset (word 14)) *)
  w 0xd348fd6b;         (* arm_LSR X11 X11 8 *)
  w 0x39003eeb;         (* arm_STRB W11 X23 (Immediate_Offset (word 15)) *)
  w 0xa94937ec;         (* arm_LDP X12 X13 SP (Immediate_Offset (iword (&144))) *)
  w 0x390042ec;         (* arm_STRB W12 X23 (Immediate_Offset (word 16)) *)
  w 0xd348fd8c;         (* arm_LSR X12 X12 8 *)
  w 0x390046ec;         (* arm_STRB W12 X23 (Immediate_Offset (word 17)) *)
  w 0xd348fd8c;         (* arm_LSR X12 X12 8 *)
  w 0x39004aec;         (* arm_STRB W12 X23 (Immediate_Offset (word 18)) *)
  w 0xd348fd8c;         (* arm_LSR X12 X12 8 *)
  w 0x39004eec;         (* arm_STRB W12 X23 (Immediate_Offset (word 19)) *)
  w 0xd348fd8c;         (* arm_LSR X12 X12 8 *)
  w 0x390052ec;         (* arm_STRB W12 X23 (Immediate_Offset (word 20)) *)
  w 0xd348fd8c;         (* arm_LSR X12 X12 8 *)
  w 0x390056ec;         (* arm_STRB W12 X23 (Immediate_Offset (word 21)) *)
  w 0xd348fd8c;         (* arm_LSR X12 X12 8 *)
  w 0x39005aec;         (* arm_STRB W12 X23 (Immediate_Offset (word 22)) *)
  w 0xd348fd8c;         (* arm_LSR X12 X12 8 *)
  w 0x39005eec;         (* arm_STRB W12 X23 (Immediate_Offset (word 23)) *)
  w 0x390062ed;         (* arm_STRB W13 X23 (Immediate_Offset (word 24)) *)
  w 0xd348fdad;         (* arm_LSR X13 X13 8 *)
  w 0x390066ed;         (* arm_STRB W13 X23 (Immediate_Offset (word 25)) *)
  w 0xd348fdad;         (* arm_LSR X13 X13 8 *)
  w 0x39006aed;         (* arm_STRB W13 X23 (Immediate_Offset (word 26)) *)
  w 0xd348fdad;         (* arm_LSR X13 X13 8 *)
  w 0x39006eed;         (* arm_STRB W13 X23 (Immediate_Offset (word 27)) *)
  w 0xd348fdad;         (* arm_LSR X13 X13 8 *)
  w 0x390072ed;         (* arm_STRB W13 X23 (Immediate_Offset (word 28)) *)
  w 0xd348fdad;         (* arm_LSR X13 X13 8 *)
  w 0x390076ed;         (* arm_STRB W13 X23 (Immediate_Offset (word 29)) *)
  w 0xd348fdad;         (* arm_LSR X13 X13 8 *)
  w 0x39007aed;         (* arm_STRB W13 X23 (Immediate_Offset (word 30)) *)
  w 0xd348fdad;         (* arm_LSR X13 X13 8 *)
  w 0x39007eed;         (* arm_STRB W13 X23 (Immediate_Offset (word 31)) *)
  w 0x910703ff;         (* arm_ADD SP SP (rvalue (word 448)) *)
  w 0xa8c163f7;         (* arm_LDP X23 X24 SP (Postimmediate_Offset (iword (&16))) *)
  w 0xa8c15bf5;         (* arm_LDP X21 X22 SP (Postimmediate_Offset (iword (&16))) *)
  w 0xa8c153f3;         (* arm_LDP X19 X20 SP (Postimmediate_Offset (iword (&16))) *)
  w 0xd65f03c0          (* arm_RET X30 *)
]);;

let curve25519_x25519base_byte_alt_constant_data = last const_data_list;;

let CURVE25519_X25519BASE_BYTE_ALT_EXEC =
  ARM_MK_EXEC_RULE curve25519_x25519base_byte_alt_mc;;

(* ------------------------------------------------------------------------- *)
(* Actually proving that the tables are correct.                             *)
(* ------------------------------------------------------------------------- *)

let edwards25519_exprojective = define
 `edwards25519_exprojective P (X,Y,Z,W) <=>
        exprojective (integer_mod_ring p_25519) P (&X,&Y,&Z,&W)`;;

let edwards25519_exprojective2 = define
 `edwards25519_exprojective2 P (X,Y,Z,W) <=>
        X < 2 * p_25519 /\ Y < 2 * p_25519 /\
        Z < 2 * p_25519 /\ W < 2 * p_25519 /\
        edwards25519_exprojective P
         (X MOD p_25519,Y MOD p_25519,Z MOD p_25519, W MOD p_25519)`;;

let edwards25519_epprojective = define
 `edwards25519_epprojective (x,y) (YMX,XPY,KXY) <=>
        x < &p_25519 /\ y < &p_25519 /\
        &YMX = (y - x) rem &p_25519 /\
        &XPY = (x + y) rem &p_25519 /\
        &KXY = (&2 * &d_25519 * x * y) rem &p_25519`;;

let EDWARDS25519_EXPROJECTIVE_IMP_EXPROJECTIVE2 = prove
 (`!P X Y Z W.
        edwards25519_exprojective P (X,Y,Z,W)
        ==> edwards25519_exprojective2 P (X,Y,Z,W)`,
  REWRITE_TAC[edwards25519_exprojective; edwards25519_exprojective2] THEN
  SIMP_TAC[EXPROJECTIVE_ALT; FORALL_PAIR_THM;
           FIELD_INTEGER_MOD_RING; PRIME_P25519] THEN
  REWRITE_TAC[INTEGER_MOD_RING_CLAUSES; IN_INTEGER_MOD_RING_CARRIER] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_REM; GSYM INT_OF_NUM_CLAUSES] THEN
  CONV_TAC INT_REM_DOWN_CONV THEN REWRITE_TAC[p_25519] THEN
  CONV_TAC INT_REDUCE_CONV THEN
  SIMP_TAC[INT_REM_LT; INT_POS] THEN INT_ARITH_TAC);;

let EDWARDS25519_EXPROJECTIVE_BOUND = prove
 (`!x y X Y Z W.
        edwards25519_exprojective (x,y) (X,Y,Z,W)
        ==> x < &p_25519 /\ y < &p_25519 /\
            X < p_25519 /\ Y < p_25519 /\ Z < p_25519 /\ W < p_25519`,
  REWRITE_TAC[edwards25519_exprojective; exprojective] THEN
  REWRITE_TAC[p_25519; IN_INTEGER_MOD_RING_CARRIER; INT_OF_NUM_CLAUSES] THEN
  CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[]);;

let GE25519_POW_1 = prove
 (`group_pow edwards25519_group E_25519 1 =
    (&15112221349535400772501151409588531511454012693041857206046113283949847762202,
     &46316835694926478169428394003475163141307993866256225615783033603165251855960)`,
  REWRITE_TAC[E_25519] THEN
  MATCH_MP_TAC GROUP_POW_1 THEN
  REWRITE_TAC[GSYM E_25519; GENERATOR_IN_GROUP_CARRIER_EDWARDS25519]);;

let GE25519_GROUPER =
  let pth = prove
   (`group_pow edwards25519_group E_25519 m = x /\
     group_pow edwards25519_group E_25519 n = y
     ==> group_pow edwards25519_group E_25519 (m + n) =
         group_mul edwards25519_group x y`,
    MESON_TAC[GROUP_POW_ADD; GROUP_POW; GENERATOR_IN_GROUP_CARRIER_EDWARDS25519]) in
  fun th1 th2 ->
    CONV_RULE
     (BINOP2_CONV (RAND_CONV NUM_ADD_CONV) ECGROUP_MUL_CONV)
     (MATCH_MP pth (CONJ th1 th2));;

let BYTES_LOADED_DATA = prove
 (`bytes_loaded s tab curve25519_x25519base_byte_alt_constant_data <=>
   read (memory :> bytes(tab,48576)) s =
   num_of_bytelist curve25519_x25519base_byte_alt_constant_data`,
  REWRITE_TAC[bytes_loaded; READ_BYTELIST_EQ_BYTES;
    CONV_RULE (RAND_CONV LENGTH_CONV)
     (AP_TERM `LENGTH:byte list->num` curve25519_x25519base_byte_alt_constant_data)]);;

let X25519BASE_TABLE_LEMMA = prove
 (`read (memory :> bytes(wpc,48576)) s =
   num_of_bytelist curve25519_x25519base_byte_alt_constant_data
   ==> edwards25519_exprojective
        (group_pow edwards25519_group E_25519 (2 EXP 254))
        (bignum_from_memory(wpc,4) s,
         bignum_from_memory(word_add wpc (word 0x20),4) s,
         1,
         bignum_from_memory(word_add wpc (word 0x40),4) s) /\
       edwards25519_exprojective
        (group_pow edwards25519_group E_25519 (2 EXP 254 + 8))
        (bignum_from_memory(word_add wpc (word 0x60),4) s,
         bignum_from_memory(word_add wpc (word 0x80),4) s,
         1,
         bignum_from_memory(word_add wpc (word 0xa0),4) s) /\
       !i. i < 63
           ==> !j. j < 8
                   ==> edwards25519_epprojective
                        (group_pow edwards25519_group E_25519
                           (2 EXP (4 * (i + 1)) * (j + 1)))
         (bignum_from_memory(word_add wpc (word(0xc0 + 768 * i + 96 * j)),4) s,
          bignum_from_memory(word_add wpc (word(0xc0 + 768 * i + 96 * j + 32)),4) s,
          bignum_from_memory(word_add wpc (word(0xc0 + 768 * i + 96 * j + 64)),4) s) /\
         ~(bignum_from_memory(word_add wpc (word(0xc0 + 768 * i + 96 * j + 64)),4) s =
           0)`,
  let GE25519_POWERS =
    end_itlist CONJ
     (funpow 63 (fun l -> let x = W GE25519_GROUPER (hd l) in
                        funpow 7 (fun l -> GE25519_GROUPER x (hd l)::l) (x::l))
                [funpow 3 (W GE25519_GROUPER) GE25519_POW_1]) in
  REWRITE_TAC[GSYM BYTES_LOADED_DATA; curve25519_x25519base_byte_alt_constant_data] THEN
  SUBST1_TAC(WORD_RULE `wpc:int64 = word(val wpc + 0)`) THEN
  SPEC_TAC(`val(wpc:int64)`,`pc:num`) THEN GEN_TAC THEN
  CONV_TAC(LAND_CONV DATA64_CONV) THEN
  REWRITE_TAC[GSYM WORD_ADD; ADD_CLAUSES; bytes_loaded_nil] THEN STRIP_TAC THEN
  CONV_TAC(funpow 2 RAND_CONV (BINDER_CONV (RAND_CONV EXPAND_CASES_CONV))) THEN
  CONV_TAC(funpow 2 RAND_CONV EXPAND_CASES_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[WORD_ADD] THEN
  CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN
  REWRITE_TAC[GSYM WORD_ADD] THEN ASM_REWRITE_TAC[] THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN REWRITE_TAC[bignum_of_wordlist] THEN
  CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
  REWRITE_TAC[GE25519_POWERS;
   GE25519_GROUPER (el 4 (CONJUNCTS GE25519_POWERS))
                   (last (CONJUNCTS GE25519_POWERS))] THEN
  REWRITE_TAC[p_25519; edwards25519_exprojective; edwards25519_epprojective;
              exprojective; d_25519] THEN
  CONV_TAC(DEPTH_CONV INTEGER_MOD_RING_RED_CONV) THEN
  REWRITE_TAC[IN_INTEGER_MOD_RING_CARRIER] THEN CONV_TAC INT_REDUCE_CONV);;

(* ------------------------------------------------------------------------- *)
(* Common lemmas and tactics for the component proofs.                       *)
(* ------------------------------------------------------------------------- *)

let lvs =
 ["resx",[`X23`;`0`];
  "scalar",[`SP`;`0`];
  "tabent",[`SP`;`32`];
  "ymx_2",[`SP`;`32`];
  "xpy_2",[`SP`;`64`];
  "kxy_2",[`SP`;`96`];
  "acc",[`SP`;`128`];
  "x_1",[`SP`;`128`];
  "y_1",[`SP`;`160`];
  "z_1",[`SP`;`192`];
  "w_1",[`SP`;`224`];
  "x_3",[`SP`;`128`];
  "y_3",[`SP`;`160`];
  "z_3",[`SP`;`192`];
  "w_3",[`SP`;`224`];
  "tmpspace",[`SP`;`256`];
  "t0",[`SP`;`256`];
  "t1",[`SP`;`288`];
  "t2",[`SP`;`320`];
  "t3",[`SP`;`352`];
  "t4",[`SP`;`384`];
  "t5",[`SP`;`416`]];;

(* ------------------------------------------------------------------------- *)
(* We will use this in macros and subroutines, with specific variables.      *)
(* ------------------------------------------------------------------------- *)

let curve25519_x25519base_byte_alt_mc' =
  SPECL [`pc:num`; `tables:num`] curve25519_x25519base_byte_alt_mc;;

(* ------------------------------------------------------------------------- *)
(* Instances of mul_p25519.                                                  *)
(* ------------------------------------------------------------------------- *)

let LOCAL_MUL_P25519_TAC =
  ARM_MACRO_SIM_ABBREV_TAC curve25519_x25519base_byte_alt_mc' 100 lvs
   `!(t:armstate) pcin pcout p3 n3 p1 n1 p2 n2.
      !m. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) t = m
      ==>
      !n. read(memory :> bytes(word_add (read p2 t) (word n2),8 * 4)) t = n
      ==>
      aligned 16 (read SP t) /\
      nonoverlapping (word pc,0x2434) (word_add (read p3 t) (word n3),8 * 4)
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) (curve25519_x25519base_byte_alt_mc pc tables) /\
                read PC s = pcin /\
                read SP s = read SP t /\
                read X23 s = read X23 t /\
                read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) s = m /\
                read(memory :> bytes(word_add (read p2 t) (word n2),8 * 4)) s = n)
           (\s. read PC s = pcout /\
                read(memory :> bytes(word_add (read p3 t) (word n3),8 * 4)) s =
                (m * n) MOD p_25519)
        (MAYCHANGE [PC; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12;
                    X13; X14; X15; X16] ,,
         MAYCHANGE [memory :> bytes(word_add (read p3 t) (word n3),8 * 4)] ,,
         MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`
 (REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(BIGNUM_LDIGITIZE_TAC "n_" o lhand o concl) THEN
  FIRST_ASSUM(BIGNUM_LDIGITIZE_TAC "m_" o lhand o concl) THEN

  (*** The initial multiply block, very similar to bignum_mul_4_8_alt ***)

  ARM_ACCSTEPS_TAC CURVE25519_X25519BASE_BYTE_ALT_EXEC (1--67) (1--67) THEN
  MAP_EVERY ABBREV_TAC
   [`l = bignum_of_wordlist[mullo_s3; sum_s18; sum_s35; sum_s52]`;
    `h = bignum_of_wordlist[sum_s62; sum_s64; sum_s66; sum_s67]`] THEN
  SUBGOAL_THEN `2 EXP 256 * h + l = m * n` (SUBST1_TAC o SYM) THENL
   [MAP_EVERY EXPAND_TAC ["h"; "l"; "m"; "n"] THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** The initial modular reduction of the high part ***)

  SUBGOAL_THEN
    `(2 EXP 256 * h + l) MOD p_25519 = (38 * h + l) MOD p_25519`
  SUBST1_TAC THENL
   [ONCE_REWRITE_TAC[GSYM MOD_ADD_MOD] THEN
    ONCE_REWRITE_TAC[GSYM MOD_MULT_LMOD] THEN
    REWRITE_TAC[p_25519] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN

  (*** Computation of quotient estimate with its explicit bounds ***)

  ARM_ACCSTEPS_TAC CURVE25519_X25519BASE_BYTE_ALT_EXEC (68--92) (68--92) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [COND_SWAP; GSYM WORD_BITVAL; VAL_WORD_BITVAL]) THEN
  SUBGOAL_THEN
   `(val(sum_s86:int64) + 1) * p_25519 <= (38 * h + l) + p_25519 /\
    (val(sum_s86:int64) + 1) <= 80 /\
    (val(sum_s86:int64) + 1) < 2 EXP 64 /\
    38 * h + l < (val(sum_s86:int64) + 1) * p_25519 + p_25519`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE `(s + 1) * p <= a + p <=> s * p <= a`] THEN
      TRANS_TAC LE_TRANS `2 EXP 255 * val(sum_s86:int64)` THEN CONJ_TAC THENL
       [REWRITE_TAC[p_25519] THEN ARITH_TAC; ALL_TAC] THEN
      TRANS_TAC LE_TRANS
       `2 EXP 192 * (2 EXP 64 * val(sum_s83:int64) + val(sum_s82:int64)) +
        2 EXP 64 * val(mulhi_s69:int64) +
        2 EXP 128 * val(mulhi_s72:int64)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC(ARITH_RULE `x:num <= y ==> x <= y + z`); ALL_TAC];
      ALL_TAC] THEN
    MAP_EVERY EXPAND_TAC ["h"; "l"] THEN
    REWRITE_TAC[bignum_of_wordlist; p_25519; GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
    ALL_TAC] THEN

  (*** The interleaved accumulation of (38 * h + l) - q * p_25519 ***)

  SUBGOAL_THEN
   `&(val(word(19 + 19 * val(sum_s86:int64)):int64)):real =
    &19 * (&(val(sum_s86:int64)) + &1)`
  SUBST_ALL_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_CLAUSES; VAL_WORD; DIMINDEX_64] THEN
    REWRITE_TAC[ARITH_RULE `19 * (x + 1) = 19 + 19 * x`] THEN
    MATCH_MP_TAC MOD_LT THEN
    UNDISCH_TAC `val(sum_s86:int64) + 1 <= 80` THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&(val(word_or sum_s82 (word 9223372036854775808:int64))):real =
    &2 pow 63 + &(val(sum_s84:int64)) / &2`
  SUBST_ALL_TAC THENL
   [ONCE_REWRITE_TAC[WORD_BITWISE_RULE
     `word_or x m = word_or m (word_and x (word_not m))`] THEN
    SIMP_TAC[VAL_WORD_OR_DISJOINT; WORD_BITWISE_RULE
     `word_and m (word_and x (word_not m)) = word 0`] THEN
    CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN AP_TERM_TAC THEN
    REWRITE_TAC[GSYM(NUM_REDUCE_CONV `2 EXP 63 - 1`)] THEN
    REWRITE_TAC[VAL_WORD_AND_MASK_WORD] THEN
    REWRITE_TAC[REAL_ARITH `x:real = z / &2 <=> &2 * x = z`] THEN
    REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN
    REWRITE_TAC[GSYM MOD_MULT2; GSYM(CONJUNCT2 EXP); ARITH_SUC] THEN
    SUBGOAL_THEN
     `2 EXP 64 * val(sum_s86:int64) + val(sum_s84:int64) =
      2 * (2 EXP 64 * val(sum_s83:int64) + val(sum_s82:int64))`
    MP_TAC THENL
     [REWRITE_TAC[bignum_of_wordlist; p_25519; GSYM REAL_OF_NUM_CLAUSES] THEN
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;
      DISCH_THEN(MP_TAC o AP_TERM `\x. x MOD 2 EXP 64` o SYM) THEN
      SIMP_TAC[MOD_MULT_ADD; MOD_LT; VAL_BOUND_64;
               ARITH_RULE `2 * (e * x + y) = e * 2 * x + 2 * y`]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&2 pow 256 * (&(bitval carry_s92) - &1:real) +
    &(bignum_of_wordlist[sum_s89; sum_s90; sum_s91; sum_s92]):real =
    &(38 * h + l) - &((val(sum_s86:int64) + 1) * p_25519)`
  MP_TAC THENL
   [MAP_EVERY EXPAND_TAC ["h"; "l"] THEN
    REWRITE_TAC[bignum_of_wordlist; p_25519; GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC) THEN DISCH_TAC] THEN

  (*** Final correction ***)

  ARM_ACCSTEPS_TAC CURVE25519_X25519BASE_BYTE_ALT_EXEC (93--100) (93--100) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV BIGNUM_EXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_UNIQ_BALANCED_REAL THEN
  MAP_EVERY EXISTS_TAC [`val(sum_s86:int64) + 1`; `255`] THEN
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [REWRITE_TAC[p_25519] THEN ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `38 * h + l < (val(sum_s86:int64) + 1) * p_25519 <=> ~carry_s92`
  SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN
    EXISTS_TAC `256` THEN ASM_REWRITE_TAC[REAL_BITVAL_NOT] THEN
    FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP (REAL_ARITH
     `&2 pow 256 * c + s:real = x - y ==> x - y = &2 pow 256 * c + s`)) THEN
    BOUNDER_TAC[];
    FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP (REAL_ARITH
     `&2 pow 256 * c + s:real = x - y ==> x = &2 pow 256 * c + s + y`)) THEN
    REWRITE_TAC[p_25519; bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[SYM(NUM_REDUCE_CONV `2 EXP 63 - 1`)] THEN
    REWRITE_TAC[VAL_WORD_AND_MASK_WORD] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; REAL_OF_NUM_MOD] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    ASM_CASES_TAC `carry_s92:bool` THEN
    ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN CONV_TAC WORD_REDUCE_CONV THEN
    REAL_INTEGER_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Instances of mul_4.                                                       *)
(* ------------------------------------------------------------------------- *)

let LOCAL_MUL_4_TAC =
  ARM_MACRO_SIM_ABBREV_TAC curve25519_x25519base_byte_alt_mc' 94 lvs
   `!(t:armstate) pcin pcout p3 n3 p1 n1 p2 n2.
      !m. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) t = m
      ==>
      !n. read(memory :> bytes(word_add (read p2 t) (word n2),8 * 4)) t = n
      ==>
      aligned 16 (read SP t) /\
      nonoverlapping (word pc,0x2434) (word_add (read p3 t) (word n3),8 * 4)
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) (curve25519_x25519base_byte_alt_mc pc tables) /\
                read PC s = pcin /\
                read SP s = read SP t /\
                read X23 s = read X23 t /\
                read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) s = m /\
                read(memory :> bytes(word_add (read p2 t) (word n2),8 * 4)) s = n)
           (\s. read PC s = pcout /\
                read(memory :> bytes(word_add (read p3 t) (word n3),8 * 4)) s
                < 2 * p_25519 /\
                (read(memory :> bytes(word_add (read p3 t) (word n3),8 * 4)) s ==
                 m * n) (mod p_25519))
        (MAYCHANGE [PC; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12;
                    X13; X14; X15; X16] ,,
         MAYCHANGE [memory :> bytes(word_add (read p3 t) (word n3),8 * 4)] ,,
         MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`
 (REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(BIGNUM_LDIGITIZE_TAC "n_" o lhand o concl) THEN
  FIRST_ASSUM(BIGNUM_LDIGITIZE_TAC "m_" o lhand o concl) THEN

  (*** The initial multiply block, very similar to bignum_mul_4_8_alt ***)

  ARM_ACCSTEPS_TAC CURVE25519_X25519BASE_BYTE_ALT_EXEC (1--67) (1--67) THEN
  MAP_EVERY ABBREV_TAC
   [`l = bignum_of_wordlist[mullo_s3; sum_s18; sum_s35; sum_s52]`;
    `h = bignum_of_wordlist[sum_s62; sum_s64; sum_s66; sum_s67]`] THEN
  SUBGOAL_THEN `2 EXP 256 * h + l = m * n` (SUBST1_TAC o SYM) THENL
   [MAP_EVERY EXPAND_TAC ["h"; "l"; "m"; "n"] THEN
    REWRITE_TAC[bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;
    ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

  (*** The initial modular reduction of the high part ***)

  REWRITE_TAC[CONG] THEN
  SUBGOAL_THEN
    `(2 EXP 256 * h + l) MOD p_25519 = (38 * h + l) MOD p_25519`
  SUBST1_TAC THENL
   [ONCE_REWRITE_TAC[GSYM MOD_ADD_MOD] THEN
    ONCE_REWRITE_TAC[GSYM MOD_MULT_LMOD] THEN
    REWRITE_TAC[p_25519] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN

  (*** Computation of quotient estimate with its explicit bounds ***)

  ARM_ACCSTEPS_TAC CURVE25519_X25519BASE_BYTE_ALT_EXEC (68--92) (68--94) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [COND_SWAP; GSYM WORD_BITVAL; VAL_WORD_BITVAL]) THEN
  SUBGOAL_THEN
   `(val(sum_s86:int64) + 1) * p_25519 <= (38 * h + l) + p_25519 /\
    (val(sum_s86:int64) + 1) <= 80 /\
    (val(sum_s86:int64) + 1) < 2 EXP 64 /\
    38 * h + l < (val(sum_s86:int64) + 1) * p_25519 + p_25519`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE `(s + 1) * p <= a + p <=> s * p <= a`] THEN
      TRANS_TAC LE_TRANS `2 EXP 255 * val(sum_s86:int64)` THEN CONJ_TAC THENL
       [REWRITE_TAC[p_25519] THEN ARITH_TAC; ALL_TAC] THEN
      TRANS_TAC LE_TRANS
       `2 EXP 192 * (2 EXP 64 * val(sum_s83:int64) + val(sum_s82:int64)) +
        2 EXP 64 * val(mulhi_s69:int64) +
        2 EXP 128 * val(mulhi_s72:int64)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC(ARITH_RULE `x:num <= y ==> x <= y + z`); ALL_TAC];
      ALL_TAC] THEN
    MAP_EVERY EXPAND_TAC ["h"; "l"] THEN
    REWRITE_TAC[bignum_of_wordlist; p_25519; GSYM REAL_OF_NUM_CLAUSES] THEN
    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
    ALL_TAC] THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN

  (*** The interleaved accumulation of (38 * h + l) - q * p_25519 ***)

  UNDISCH_TAC
   `&2 pow 64 * &(val(mulhi_s88:int64)) + &(val(mullo_s88:int64)) =
    &19 * &(val(sum_s86:int64))` THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP (ARITH_RULE `a + 1 <= 80 ==> a < 80`)) THEN
  DISCH_THEN(fun bth -> DISCH_THEN(fun th ->
        MP_TAC(end_itlist CONJ (GEN_DECARRY_RULE [bth] [th])))) THEN
  DISCH_THEN(SUBST_ALL_TAC o CONJUNCT2) THEN

  SUBGOAL_THEN
   `&(val(word_and sum_s82 (word 9223372036854775807:int64))):real =
    &(val(sum_s84:int64)) / &2`
  SUBST_ALL_TAC THENL
   [REWRITE_TAC[GSYM(NUM_REDUCE_CONV `2 EXP 63 - 1`)] THEN
    REWRITE_TAC[VAL_WORD_AND_MASK_WORD] THEN
    REWRITE_TAC[REAL_ARITH `x:real = z / &2 <=> &2 * x = z`] THEN
    REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN
    REWRITE_TAC[GSYM MOD_MULT2; GSYM(CONJUNCT2 EXP); ARITH_SUC] THEN
    SUBGOAL_THEN
     `2 EXP 64 * val(sum_s86:int64) + val(sum_s84:int64) =
      2 * (2 EXP 64 * val(sum_s83:int64) + val(sum_s82:int64))`
    MP_TAC THENL
     [REWRITE_TAC[bignum_of_wordlist; p_25519; GSYM REAL_OF_NUM_CLAUSES] THEN
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;
      DISCH_THEN(MP_TAC o AP_TERM `\x. x MOD 2 EXP 64` o SYM) THEN
      SIMP_TAC[MOD_MULT_ADD; MOD_LT; VAL_BOUND_64;
               ARITH_RULE `2 * (e * x + y) = e * 2 * x + 2 * y`]];
    ALL_TAC] THEN

  REWRITE_TAC[GSYM CONG; REAL_OF_NUM_CLAUSES] THEN
  REWRITE_TAC[num_congruent; GSYM INT_OF_NUM_CLAUSES] THEN
  MATCH_MP_TAC(MESON[]
   `!q. (ca - q * p == ca) (mod p) /\
        (&0 <= ca - q * p /\ ca - q * p < p2) /\
        (&0 <= ca - q * p /\ ca - q * p < p2 ==> x = ca - q * p)
        ==> x:int < p2 /\ (x == ca) (mod p)`) THEN
  EXISTS_TAC `&(val(sum_s86:int64)):int` THEN
  CONJ_TAC THENL [CONV_TAC INTEGER_RULE; ALL_TAC] THEN
  CONJ_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`(val(sum_s86:int64) + 1) * p_25519 <= (38 * h + l) + p_25519`;
      `38 * h + l < (val(sum_s86:int64) + 1) * p_25519 + p_25519`] THEN
    REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES] THEN INT_ARITH_TAC;
    STRIP_TAC] THEN
  MATCH_MP_TAC INT_CONG_IMP_EQ THEN EXISTS_TAC `(&2:int) pow 256` THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (INT_ARITH
     `y:int < p ==> &0 <= y /\ &0 <= p /\ p < e /\ &0 <= x /\ x < e
         ==> abs(x - y) < e`)) THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[INT_OF_NUM_CLAUSES; p_25519] THEN
    CONV_TAC NUM_REDUCE_CONV THEN BOUNDER_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES] THEN
  SIMP_TAC[REAL_INT_CONGRUENCE; INT_POW_EQ_0; INT_OF_NUM_EQ; ARITH_EQ] THEN
  REWRITE_TAC[int_of_num_th; int_sub_th; int_add_th;
              int_mul_th; int_pow_th] THEN
  MAP_EVERY EXPAND_TAC ["h"; "l"] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; bignum_of_wordlist] THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  REWRITE_TAC[REAL_OF_NUM_MOD; p_25519] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

(* ------------------------------------------------------------------------- *)
(* Instances of add_twice4 (slightly sharper disjunctive hypothesis).        *)
(* ------------------------------------------------------------------------- *)

let LOCAL_ADD_TWICE4_TAC =
  ARM_MACRO_SIM_ABBREV_TAC curve25519_x25519base_byte_alt_mc' 16 lvs
   `!(t:armstate) pcin pcout p3 n3 p1 n1 p2 n2.
      !m. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) t = m
      ==>
      !n. read(memory :> bytes(word_add (read p2 t) (word n2),8 * 4)) t = n
      ==>
      aligned 16 (read SP t) /\
      nonoverlapping (word pc,0x2434) (word_add (read p3 t) (word n3),8 * 4)
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) (curve25519_x25519base_byte_alt_mc pc tables) /\
                read PC s = pcin /\
                read SP s = read SP t /\
                read X23 s = read X23 t /\
                read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) s = m /\
                read(memory :> bytes(word_add (read p2 t) (word n2),8 * 4)) s = n)
           (\s. read PC s = pcout /\
                (m < 2 * p_25519 \/ n < 2 * p_25519
                 ==> (read(memory :> bytes(word_add (read p3 t) (word n3),8 * 4)) s ==
                      m + n) (mod p_25519)))
        (MAYCHANGE [PC; X3; X4; X5; X6; X7; X8; X9] ,,
         MAYCHANGE [memory :> bytes(word_add (read p3 t) (word n3),8 * 4)] ,,
         MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`
 (REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(BIGNUM_LDIGITIZE_TAC "n_" o lhand o concl) THEN
  FIRST_ASSUM(BIGNUM_LDIGITIZE_TAC "m_" o lhand o concl) THEN
  ARM_ACCSTEPS_TAC CURVE25519_X25519BASE_BYTE_ALT_EXEC (1--8) (1--8) THEN
  SUBGOAL_THEN `carry_s8 <=> 2 EXP 256 <= m + n` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC FLAG_FROM_CARRY_LE THEN EXISTS_TAC `256` THEN
    MAP_EVERY EXPAND_TAC ["m"; "n"] THEN REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_POW] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
    ALL_TAC] THEN
  ARM_ACCSTEPS_TAC CURVE25519_X25519BASE_BYTE_ALT_EXEC (11--14) (9--16) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REWRITE_TAC[num_congruent; GSYM INT_OF_NUM_ADD] THEN
  MATCH_MP_TAC(MESON[INT_OF_NUM_LT]
   `!x':int. (x' == a) (mod p) /\ x = x'
             ==> (x:int == a) (mod p)`) THEN
  EXISTS_TAC
   `if 2 EXP 256 <= m + n then (&m + &n) - &2 * &p_25519:int else &m + &n` THEN
  CONJ_TAC THENL [COND_CASES_TAC THEN CONV_TAC INTEGER_RULE; ALL_TAC] THEN
  CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[int_eq] THEN ONCE_REWRITE_TAC[COND_RAND] THEN
  REWRITE_TAC[int_of_num_th; int_sub_th; int_add_th; int_mul_th] THEN
  MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
  MAP_EVERY EXISTS_TAC [`256`; `&0:real`] THEN
  CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `2 EXP 256` o MATCH_MP (ARITH_RULE
     `m < p \/ n < p
      ==> !e:num. p < e /\ m < e /\ n < e ==> m + n < e + p`)) THEN
    ANTS_TAC THENL
     [MAP_EVERY EXPAND_TAC ["m"; "n"] THEN REWRITE_TAC[p_25519] THEN
      CONV_TAC NUM_REDUCE_CONV THEN BOUNDER_TAC[];
      REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES; p_25519] THEN
      CONV_TAC NUM_REDUCE_CONV THEN INT_ARITH_TAC];
    REWRITE_TAC[INTEGER_CLOSED]] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SYM(NUM_EXP_CONV `2 EXP 256`)]) THEN
  ABBREV_TAC `bb <=> 2 EXP 256 <= m + n` THEN MAP_EVERY EXPAND_TAC ["m"; "n"] THEN
  REWRITE_TAC[bignum_of_wordlist; p_25519; GSYM REAL_OF_NUM_CLAUSES] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
  CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

(* ------------------------------------------------------------------------- *)
(* Instances of double_twice4.                                               *)
(* ------------------------------------------------------------------------- *)

let LOCAL_DOUBLE_TWICE4_TAC =
  ARM_MACRO_SIM_ABBREV_TAC curve25519_x25519base_byte_alt_mc' 14 lvs
   `!(t:armstate) pcin pcout p3 n3 p1 n1.
      !n. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) t = n
      ==>
      aligned 16 (read SP t) /\
      nonoverlapping (word pc,0x2434) (word_add (read p3 t) (word n3),8 * 4)
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) (curve25519_x25519base_byte_alt_mc pc tables) /\
                read PC s = pcin /\
                read SP s = read SP t /\
                read X23 s = read X23 t /\
                read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) s = n)
           (\s. read PC s = pcout /\
                (n < 2 * p_25519
                 ==> (read(memory :> bytes(word_add (read p3 t) (word n3),8 * 4)) s ==
                      2 * n) (mod p_25519)))
        (MAYCHANGE [PC; X3; X4; X5; X6; X7; X8; X9] ,,
         MAYCHANGE [memory :> bytes(word_add (read p3 t) (word n3),8 * 4)] ,,
         MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`
 (REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(BIGNUM_LDIGITIZE_TAC "n_" o lhand o concl) THEN
  ARM_ACCSTEPS_TAC CURVE25519_X25519BASE_BYTE_ALT_EXEC (1--6) (1--6) THEN
  SUBGOAL_THEN `carry_s6 <=> 2 EXP 256 <= 2 * n` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC FLAG_FROM_CARRY_LE THEN EXISTS_TAC `256` THEN
    EXPAND_TAC "n" THEN REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_POW] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
    ALL_TAC] THEN
  ARM_ACCSTEPS_TAC CURVE25519_X25519BASE_BYTE_ALT_EXEC (9--12) (7--14) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REWRITE_TAC[num_congruent; GSYM INT_OF_NUM_ADD] THEN
  MATCH_MP_TAC(MESON[INT_OF_NUM_LT]
   `!x':int. (x' == a) (mod p) /\ x = x'
             ==> (x:int == a) (mod p)`) THEN
  EXISTS_TAC
   `if 2 EXP 256 <= 2 * n then (&2 * &n) - &2 * &p_25519:int else &2 * &n` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES] THEN
    COND_CASES_TAC THEN CONV_TAC INTEGER_RULE;
    ALL_TAC] THEN
  CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[int_eq] THEN ONCE_REWRITE_TAC[COND_RAND] THEN
  REWRITE_TAC[int_of_num_th; int_sub_th; int_add_th; int_mul_th] THEN
  MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
  MAP_EVERY EXISTS_TAC [`256`; `&0:real`] THEN
  CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN CONJ_TAC THENL
   [POP_ASSUM MP_TAC THEN
    REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES; p_25519] THEN
    CONV_TAC NUM_REDUCE_CONV THEN INT_ARITH_TAC;
    REWRITE_TAC[INTEGER_CLOSED]] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM NOT_LE; SYM(NUM_EXP_CONV `2 EXP 256`)]) THEN
  ABBREV_TAC `bb <=> 2 EXP 256 <= 2 * n` THEN EXPAND_TAC "n" THEN
  REWRITE_TAC[bignum_of_wordlist; p_25519; GSYM REAL_OF_NUM_CLAUSES] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
  CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

(* ------------------------------------------------------------------------- *)
(* Instances of sub_twice4 (slightly sharper hypothesis distinctions).       *)
(* ------------------------------------------------------------------------- *)

let LOCAL_SUB_TWICE4_TAC =
  ARM_MACRO_SIM_ABBREV_TAC curve25519_x25519base_byte_alt_mc' 16 lvs
   `!(t:armstate) pcin pcout p3 n3 p1 n1 p2 n2.
      !m. read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) t = m
      ==>
      !n. read(memory :> bytes(word_add (read p2 t) (word n2),8 * 4)) t = n
      ==>
      aligned 16 (read SP t) /\
      nonoverlapping (word pc,0x2434) (word_add (read p3 t) (word n3),8 * 4)
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) (curve25519_x25519base_byte_alt_mc pc tables) /\
                read PC s = pcin /\
                read SP s = read SP t /\
                read X23 s = read X23 t /\
                read(memory :> bytes(word_add (read p1 t) (word n1),8 * 4)) s = m /\
                read(memory :> bytes(word_add (read p2 t) (word n2),8 * 4)) s = n)
           (\s. read PC s = pcout /\
                (m < 2 * p_25519 /\ n < 2 * p_25519
                 ==> read(memory :> bytes(word_add (read p3 t) (word n3),8 * 4)) s
                     < 2 * p_25519) /\
                (n < 2 * p_25519
                 ==> (&(read(memory :> bytes
                         (word_add (read p3 t) (word n3),8 * 4)) s):int ==
                      &m - &n) (mod (&p_25519))))
        (MAYCHANGE [PC; X3; X4; X5; X6; X7; X8] ,,
         MAYCHANGE [memory :> bytes(word_add (read p3 t) (word n3),8 * 4)] ,,
         MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`
 (REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(BIGNUM_LDIGITIZE_TAC "n_" o lhand o concl) THEN
  FIRST_ASSUM(BIGNUM_LDIGITIZE_TAC "m_" o lhand o concl) THEN
  ARM_ACCSTEPS_TAC CURVE25519_X25519BASE_BYTE_ALT_EXEC (1--8) (1--8) THEN
  SUBGOAL_THEN `carry_s8 <=> m < n` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC FLAG_FROM_CARRY_LT THEN EXISTS_TAC `256` THEN
    MAP_EVERY EXPAND_TAC ["m"; "n"] THEN REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_POW] THEN
    ACCUMULATOR_ASSUM_LIST(MP_TAC o end_itlist CONJ o DECARRY_RULE) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BOUNDER_TAC[];
    ALL_TAC] THEN
  ARM_ACCSTEPS_TAC CURVE25519_X25519BASE_BYTE_ALT_EXEC (11--14) (9--16) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(MESON[INT_OF_NUM_LT]
   `!x':int. (x' == &m - &n) (mod p) /\
             (m < p2 /\ n < p2 ==> x' < &p2) /\
             (n < p2 ==> &x = x')
             ==> (m < p2 /\ n < p2 ==> x < p2) /\
                 (n:num < p2 ==> (&x:int == &m - &n) (mod p))`) THEN
  EXISTS_TAC `if m < n then &m - &n + &2 * &p_25519:int else &m - &n` THEN
  REPEAT CONJ_TAC THENL
   [COND_CASES_TAC THEN CONV_TAC INTEGER_RULE;
    REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES] THEN INT_ARITH_TAC;
    DISCH_TAC] THEN
  CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[int_eq] THEN ONCE_REWRITE_TAC[COND_RAND] THEN
  REWRITE_TAC[int_of_num_th; int_sub_th; int_add_th; int_mul_th] THEN
  MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
  MAP_EVERY EXISTS_TAC [`256`; `&0:real`] THEN
  CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC] THEN CONJ_TAC THENL
   [CONJ_TAC THENL
     [POP_ASSUM MP_TAC THEN
      REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES; p_25519] THEN
      CONV_TAC NUM_REDUCE_CONV THEN INT_ARITH_TAC;
      SUBGOAL_THEN `m < 2 EXP 256` MP_TAC THENL
       [EXPAND_TAC "m" THEN BOUNDER_TAC[];
        REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; p_25519] THEN REAL_ARITH_TAC]];
    REWRITE_TAC[INTEGER_CLOSED]] THEN
  ABBREV_TAC `bb <=> m:num < n` THEN MAP_EVERY EXPAND_TAC ["m"; "n"] THEN
  REWRITE_TAC[bignum_of_wordlist; p_25519; GSYM REAL_OF_NUM_CLAUSES] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
  CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC);;

(* ------------------------------------------------------------------------- *)
(* Instances of modular inverse inlining                                     *)
(* ------------------------------------------------------------------------- *)

let LOCAL_MODINV_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (curve25519_x25519base_byte_alt_mc',CURVE25519_X25519BASE_BYTE_ALT_EXEC,0x1190,
    (GEN_REWRITE_CONV RAND_CONV [bignum_inv_p25519_mc] THENC TRIM_LIST_CONV)
    `TRIM_LIST (12,16) bignum_inv_p25519_mc`,
    CORE_INV_P25519_CORRECT)
   [`read X0 s`; `read X1 s`;
    `read (memory :> bytes(read X1 s,8 * 4)) s`;
    `pc + 0x1190`; `stackpointer:int64`];;

(* ------------------------------------------------------------------------- *)
(* Overall point operation proof.                                            *)
(* ------------------------------------------------------------------------- *)

let CURVE25519_X25519BASE_BYTE_ALT_CORRECT = time prove
 (`!tables res scalar n pc stackpointer.
    aligned 16 stackpointer /\
    adrp_within_bounds (word tables) (word(pc + 0x118)) /\
    ALL (nonoverlapping (stackpointer,448))
        [(word pc,0x2434); (word tables,48576); (res,32); (scalar,32)] /\
    nonoverlapping (res,32) (word pc,0x2434)
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc)
                (curve25519_x25519base_byte_alt_mc pc tables) /\
              read PC s = word(pc + 0x10) /\
              bytes_loaded s (word tables)
                curve25519_x25519base_byte_alt_constant_data /\
              read SP s = stackpointer /\
              C_ARGUMENTS [res; scalar] s /\
              read (memory :> bytes(scalar,32)) s = n)
         (\s. read PC s = word (pc + 0x2420) /\
              read (memory :> bytes(res,32)) s = rfcx25519(n,9))
          (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10;
                      X11; X12; X13; X14; X15; X16; X17; X19; X20;
                      X21; X22; X23] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bytes(res,32);
                      memory :> bytes(stackpointer,448)])`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC
   [`tables:num`; `res:int64`; `scalar:int64`; `n_input:num`;
    `pc:num`; `stackpointer:int64`] THEN
  REWRITE_TAC[ALLPAIRS; ALL; NONOVERLAPPING_CLAUSES] THEN STRIP_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS] THEN

  REWRITE_TAC[ALIGNED_BYTES_LOADED_APPEND_CLAUSE] THEN
  REWRITE_TAC[fst CURVE25519_X25519BASE_BYTE_ALT_EXEC] THEN
  REWRITE_TAC[BYTES_LOADED_DATA] THEN

  (*** The modified forms of the inputs that get computed early on  ***)
  (*** The nn' is the computed value just modifying the top 2 bits ***)

  ABBREV_TAC `nn = 2 EXP 254 + n_input MOD 2 EXP 254 - n_input MOD 8` THEN
  ABBREV_TAC `nn' = n_input MOD 2 EXP 254` THEN
  ASM_REWRITE_TAC[rfcx25519] THEN CONV_TAC NUM_REDUCE_CONV THEN

  (*** Setup of the main loop ***)

  ENSURES_WHILE_AUP_TAC `1` `64` `pc + 0x1b0` `pc + 0x1100`
   `\i s.
      read (memory :> bytes(word tables,48576)) s =
      num_of_bytelist curve25519_x25519base_byte_alt_constant_data /\
      read SP s = stackpointer /\
      read X23 s = res /\
      read X19 s = word(tables + 0xc0 + 768 * (i - 1)) /\
      read X20 s = word (4 * i) /\
      val(read X21 s) <= 1 /\
      (i >= 64 ==> val(read X21 s) < 1) /\
      bignum_from_memory (stackpointer,4) s = nn' /\
      edwards25519_exprojective2
       (group_zpow edwards25519_group E_25519
         (&nn - &2 pow (4 * i) *
                (&(nn' DIV 2 EXP (4 * i)) + &(val(read X21 s)))))
       (bignum_from_memory(word_add stackpointer (word 128),4) s,
        bignum_from_memory(word_add stackpointer (word 160),4) s,
        bignum_from_memory(word_add stackpointer (word 192),4) s,
        bignum_from_memory(word_add stackpointer (word 224),4) s)` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** Initial setup and modification of the inputs ***)

    REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
    BYTES_DIGITIZE_TAC "nb_" `read (memory :> bytes (scalar,32)) s0` THEN

    FIRST_ASSUM(MP_TAC o MATCH_MP X25519BASE_TABLE_LEMMA) THEN

    GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [WORD_ADD] THEN
    ABBREV_TAC `wpc:int64 = word tables` THEN

    SUBGOAL_THEN
     `!c n. nonoverlapping_modulo (2 EXP 64) c (tables,n) <=>
            nonoverlapping_modulo (2 EXP 64) c (val(wpc:int64),n)`
    MP_TAC THENL
     [EXPAND_TAC "wpc" THEN
      REWRITE_TAC[FORALL_PAIR_THM; NONOVERLAPPING_CLAUSES];
      DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))] THEN

    REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    DISCH_THEN(K ALL_TAC) THEN
    BIGNUM_LDIGITIZE_TAC "x0_"
      `bignum_from_memory(wpc,4) s0` THEN
    BIGNUM_LDIGITIZE_TAC "y0_"
      `bignum_from_memory(word_add wpc (word 32),4) s0` THEN
    BIGNUM_LDIGITIZE_TAC "t0_"
      `bignum_from_memory(word_add wpc (word 64),4) s0` THEN
    BIGNUM_LDIGITIZE_TAC "x1_"
      `bignum_from_memory(word_add wpc (word 96),4) s0` THEN
    BIGNUM_LDIGITIZE_TAC "y1_"
      `bignum_from_memory(word_add wpc (word 128),4) s0` THEN
    BIGNUM_LDIGITIZE_TAC "t1_"
      `bignum_from_memory(word_add wpc (word 160),4) s0` THEN

    ARM_STEPS_TAC CURVE25519_X25519BASE_BYTE_ALT_EXEC (1--68) THEN

    FIRST_ASSUM(SUBST_ALL_TAC o MATCH_MP ADRP_ADD_FOLD) THEN

    ARM_STEPS_TAC CURVE25519_X25519BASE_BYTE_ALT_EXEC (69--104) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_THEN `word tables:int64 = wpc` (SUBST1_TAC o SYM) THEN
    ASM_REWRITE_TAC[] THEN

    REPLICATE_TAC 4
     (CONJ_TAC THENL
      [CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN CONV_TAC WORD_RULE;
       ALL_TAC]) THEN
    CONJ_TAC THENL
     [MAP_EVERY EXPAND_TAC ["nn'"; "n_input"] THEN MATCH_MP_TAC(ARITH_RULE
       `m + 2 EXP 254 * n DIV 2 EXP 254 = n
        ==> m = n MOD 2 EXP 254`) THEN
      SUBGOAL_THEN
       `n_input DIV 2 EXP 254 = val(nb_31:byte) DIV 2 EXP 6` MP_TAC THEN
      EXPAND_TAC "n_input" THENL
       [REWRITE_TAC[EXP_ADD; GSYM DIV_DIV; ARITH_RULE `254 = 248 + 6`] THEN
        REWRITE_TAC[ADD_ASSOC] THEN
        SIMP_TAC[DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ] THEN
        W(MP_TAC o PART_MATCH (lhand o rand) DIV_LT o
          funpow 3 lhand o snd) THEN
        ANTS_TAC THENL
         [CONV_TAC NUM_REDUCE_CONV THEN BOUNDER_TAC[];
          DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[ADD_CLAUSES]];
        DISCH_THEN SUBST1_TAC] THEN
      REWRITE_TAC[VAL_DIV; DIMINDEX_8] THEN
      REWRITE_TAC[ARITH_RULE `6 <= i /\ i < 8 <=> 6 <= i /\ i <= 7`] THEN
      REWRITE_TAC[bignum_of_wordlist; val_def] THEN
      REWRITE_TAC[DIMINDEX_8; ARITH_RULE `i < 8 <=> 0 <= i /\ i <= 7`] THEN
      REWRITE_TAC[DIMINDEX_64; ARITH_RULE `i < 64 <=> 0 <= i /\ i <= 63`] THEN
      REWRITE_TAC[GSYM IN_NUMSEG; IN_GSPEC] THEN CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC[BIT_WORD_OR; BIT_WORD_AND; BIT_WORD_SHL; BIT_WORD_ZX] THEN
      ONCE_REWRITE_TAC[BIT_GUARD] THEN
      REWRITE_TAC[DIMINDEX_8; DIMINDEX_32; DIMINDEX_64] THEN
      CONV_TAC(ONCE_DEPTH_CONV EXPAND_NSUM_CONV) THEN
      CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN ARITH_TAC;
      ALL_TAC] THEN

    MATCH_MP_TAC EDWARDS25519_EXPROJECTIVE_IMP_EXPROJECTIVE2 THEN
    REWRITE_TAC[VAL_WORD_0; INT_ADD_RID; MULT_CLAUSES] THEN
    SUBGOAL_THEN
     `&nn - &2 pow 4 * &(nn' DIV 2 EXP 4):int =
      &(2 EXP 254 + 8 * (n_input DIV 8) MOD 2)`
    SUBST1_TAC THENL
     [MAP_EVERY EXPAND_TAC ["nn"; "nn'"] THEN
      REWRITE_TAC[INT_EQ_SUB_RADD; INT_OF_NUM_CLAUSES] THEN
      REWRITE_TAC[GSYM ADD_ASSOC; EQ_ADD_LCANCEL] THEN
      MATCH_MP_TAC(ARITH_RULE
       `x MOD 2 EXP 4 = a + r ==> x - r = a + 2 EXP 4 * x DIV 2 EXP 4`) THEN
      REWRITE_TAC[MOD_MOD_EXP_MIN; ARITH_RULE `MIN 254 4 = 4`] THEN
      REWRITE_TAC[ARITH_RULE `2 EXP 4 = 8 * 2`; MOD_MULT_MOD];
      ALL_TAC] THEN
    REWRITE_TAC[VAL_WORD_AND_POW2; ARITH_RULE `8 = 2 EXP 3`] THEN
    REWRITE_TAC[BIT_WORD_OR; BIT_WORD_SHL; BIT_WORD_ZX] THEN
    REWRITE_TAC[DIMINDEX_32; DIMINDEX_64] THEN
    CONV_TAC(RAND_CONV(DEPTH_CONV WORD_NUM_RED_CONV)) THEN

    SUBGOAL_THEN `(n_input DIV 2 EXP 3) MOD 2 = bitval(bit 3 (nb_0:byte))`
    SUBST1_TAC THENL
     [REWRITE_TAC[DIV_MOD] THEN CONV_TAC NUM_REDUCE_CONV THEN
      SUBGOAL_THEN `n_input MOD 16 = val(nb_0:byte) MOD 16` SUBST1_TAC THENL
       [REWRITE_TAC[GSYM CONG] THEN EXPAND_TAC "n_input" THEN
        MATCH_MP_TAC(NUMBER_RULE
         `d divides n ==> (m + n:num == m) (mod d)`) THEN
        REPEAT(MATCH_MP_TAC DIVIDES_ADD THEN CONJ_TAC) THEN
        MATCH_MP_TAC DIVIDES_RMUL THEN CONV_TAC NUM_REDUCE_CONV THEN
        CONV_TAC DIVIDES_CONV;
        REWRITE_TAC[ARITH_RULE `16 = 8 * 2`; GSYM DIV_MOD]] THEN
      REWRITE_TAC[BIT_VAL; BITVAL_ODD] THEN
      CONV_TAC NUM_REDUCE_CONV;
      ALL_TAC] THEN
    REWRITE_TAC[GROUP_NPOW] THEN
    REWRITE_TAC[MULT_EQ_0; EXP_EQ_0; ARITH_EQ; BITVAL_EQ_0; COND_SWAP] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES; BITVAL_CLAUSES] THEN
    GEN_REWRITE_TAC (funpow 3 RAND_CONV o LAND_CONV o TOP_DEPTH_CONV)
     [bignum_of_wordlist; VAL_WORD_1; VAL_WORD_0;
      ADD_CLAUSES; MULT_CLAUSES] THEN
    ASM_REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES; ARITH_RULE `2 EXP 3 = 8`];

    (*** The main loop invariant for adding the next table entry ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    GHOST_INTRO_TAC `xn:num`
     `bignum_from_memory (word_add stackpointer (word 128),4)` THEN
    GHOST_INTRO_TAC `yn:num`
     `bignum_from_memory (word_add stackpointer (word 160),4)` THEN
    GHOST_INTRO_TAC `zn:num`
     `bignum_from_memory (word_add stackpointer (word 192),4)` THEN
    GHOST_INTRO_TAC `wn:num`
     `bignum_from_memory(word_add stackpointer (word 224),4)` THEN
    GHOST_INTRO_TAC `nbias:num` `\s. val(read X21 s)` THEN
    GLOBALIZE_PRECONDITION_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [NUM_AS_BITVAL]) THEN
    DISCH_THEN(X_CHOOSE_THEN `bias:bool` SUBST_ALL_TAC) THEN
    REWRITE_TAC[VAL_EQ_BITVAL] THEN

    REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
    FIRST_ASSUM(MP_TAC o last o CONJUNCTS o
      MATCH_MP X25519BASE_TABLE_LEMMA) THEN
    DISCH_THEN(MP_TAC o SPEC `i - 1`) THEN ASM_SIMP_TAC[SUB_ADD] THEN
    ASM_SIMP_TAC[ARITH_RULE `i < 64 ==> i - 1 < 63`] THEN
    REWRITE_TAC[GSYM WORD_ADD; ARITH_RULE
      `tables + off + 768 * (i - 1) + jre =
       (tables + off + 768 * (i - 1)) + jre`] THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [WORD_ADD] THEN
    ABBREV_TAC `tab:int64 = word(tables + 0xc0 + 768 * (i - 1))` THEN
    CONV_TAC(LAND_CONV EXPAND_CASES_CONV) THEN
    CONV_TAC(LAND_CONV NUM_REDUCE_CONV) THEN
    GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [WORD_ADD_0] THEN

    CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV)) THEN
    ABBREV_TAC `tab_0 = read (memory :> bytes64 tab) s0` THEN
    MAP_EVERY (fun i ->
        ABBREV_TAC(mk_eq(mk_var("tab_"^string_of_int i,`:int64`),
              vsubst [mk_small_numeral(8*i),`n:num`]
                     `read (memory :> bytes64 (word_add tab (word n))) s0`)))
        (1--95) THEN
    STRIP_TAC THEN

    SUBGOAL_THEN
     `read(memory :> bytes64(word_add stackpointer
       (word(8 * val(word_ushr (word (4 * i):int64) 6))))) s0 =
      word(nn' DIV (2 EXP (64 * (4 * i) DIV 64)) MOD 2 EXP (64 * 1))`
    ASSUME_TAC THENL
     [EXPAND_TAC "nn'" THEN REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_DIV; BIGNUM_FROM_MEMORY_MOD] THEN
      ASM_SIMP_TAC[ARITH_RULE `i < 64 ==> MIN (4 - (4 * i) DIV 64) 1 = 1`] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_SING; WORD_VAL] THEN
      AP_THM_TAC THEN REPLICATE_TAC 6 AP_TERM_TAC THEN
      REWRITE_TAC[VAL_WORD_USHR] THEN CONV_TAC NUM_REDUCE_CONV THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC VAL_WORD_EQ THEN
      REWRITE_TAC[DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
      ASM BOUNDER_TAC[];
      ALL_TAC] THEN

    ARM_STEPS_TAC CURVE25519_X25519BASE_BYTE_ALT_EXEC (1--5) THEN
    ABBREV_TAC `bf = (nn' DIV (2 EXP (4 * i))) MOD 16` THEN
    SUBGOAL_THEN
     `word_and
       (word_jushr
        (word ((nn' DIV 2 EXP (64 * (4 * i) DIV 64)) MOD 2 EXP 64))
       (word (4 * i)))
      (word 15):int64 = word bf`
    SUBST_ALL_TAC THENL
     [REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_AND_MASK_WORD;
                  ARITH_RULE `15 = 2 EXP 4 - 1`] THEN
      REWRITE_TAC[word_jushr; VAL_WORD_USHR; DIMINDEX_64; MOD_64_CLAUSES] THEN

      EXPAND_TAC "bf" THEN REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN
      REWRITE_TAC[MOD_MOD_EXP_MIN; ARITH_RULE `16 = 2 EXP 4`] THEN
      CONV_TAC(ONCE_DEPTH_CONV NUM_MIN_CONV) THEN
      REWRITE_TAC[DIV_MOD; MOD_MOD_EXP_MIN; GSYM EXP_ADD; DIV_DIV] THEN
      REWRITE_TAC[ARITH_RULE `64 * i DIV 64 + i MOD 64 = i`] THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[ARITH_RULE `64 = 4 * 16`] THEN
      SIMP_TAC[DIV_MULT2; MOD_MULT2; ARITH_EQ] THEN
      UNDISCH_TAC `i < 64` THEN ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `word_add (word bf) (word(bitval bias)):int64 =
      word(bf + bitval bias)`
    SUBST_ALL_TAC THENL [REWRITE_TAC[WORD_ADD]; ALL_TAC] THEN

    ARM_STEPS_TAC CURVE25519_X25519BASE_BYTE_ALT_EXEC (6--11) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[WORD_SUB_0]) THEN
    ABBREV_TAC `bias' <=> bf + bitval bias >= 9` THEN

    SUBGOAL_THEN
     `(if val(word(bf + bitval bias):int64) < 9
       then word 0:int64 else word 1):int64 = word(bitval bias')`
    SUBST_ALL_TAC THENL
     [EXPAND_TAC "bias'" THEN
      REWRITE_TAC[GE; GSYM NOT_LE; COND_SWAP; GSYM WORD_BITVAL] THEN
      AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
      MATCH_MP_TAC VAL_WORD_EQ THEN
      EXPAND_TAC "bf" THEN REWRITE_TAC[bitval; DIMINDEX_64] THEN ARITH_TAC;
      RULE_ASSUM_TAC(REWRITE_RULE
       [COND_SWAP; VAL_WORD_BITVAL; BITVAL_EQ_0])] THEN
    ABBREV_TAC
     `ix = if bias' then 16 - (bf + bitval bias) else bf + bitval bias` THEN
    SUBGOAL_THEN
     `(if bias'
       then word_sub (word 16) (word (bf + bitval bias))
       else word (bf + bitval bias)):int64 = word ix`
    SUBST_ALL_TAC THENL
     [EXPAND_TAC "ix" THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
      REWRITE_TAC[WORD_SUB] THEN
      MATCH_MP_TAC(MESON[] `p ==> x = if p then x else y`) THEN
      EXPAND_TAC "bf" THEN REWRITE_TAC[bitval] THEN ARITH_TAC;
      ALL_TAC] THEN

    ARM_STEPS_TAC CURVE25519_X25519BASE_BYTE_ALT_EXEC (12--183) THEN
    REABBREV_TAC `ymx_0 = read X0 s183` THEN
    REABBREV_TAC `ymx_1 = read X1 s183` THEN
    REABBREV_TAC `ymx_2 = read X2 s183` THEN
    REABBREV_TAC `ymx_3 = read X3 s183` THEN
    REABBREV_TAC `xpy_0 = read X4 s183` THEN
    REABBREV_TAC `xpy_1 = read X5 s183` THEN
    REABBREV_TAC `xpy_2 = read X6 s183` THEN
    REABBREV_TAC `xpy_3 = read X7 s183` THEN
    REABBREV_TAC `kxy_0 = read X8 s183` THEN
    REABBREV_TAC `kxy_1 = read X9 s183` THEN
    REABBREV_TAC `kxy_2 = read X10 s183` THEN
    REABBREV_TAC `kxy_3 = read X11 s183` THEN
    SUBGOAL_THEN `ix <= 8` ASSUME_TAC THENL
     [MAP_EVERY EXPAND_TAC ["ix"; "bias'"] THEN ARITH_TAC; ALL_TAC] THEN

    SUBGOAL_THEN
     `edwards25519_epprojective
        (group_pow edwards25519_group E_25519 (2 EXP (4 * i) * ix))
        (bignum_of_wordlist [ymx_0; ymx_1; ymx_2; ymx_3],
         bignum_of_wordlist [xpy_0; xpy_1; xpy_2; xpy_3],
         bignum_of_wordlist [kxy_0; kxy_1; kxy_2; kxy_3]) /\
      (1 <= ix ==> ~(bignum_of_wordlist [kxy_0; kxy_1; kxy_2; kxy_3] = 0))`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `ix <= 8` THEN
      REWRITE_TAC[ARITH_RULE `ix <= 8 <=> ix < 9`] THEN
      MAP_EVERY EXPAND_TAC
       ["ymx_0";"ymx_1";"ymx_2";"ymx_3";
        "xpy_0";"xpy_1";"xpy_2";"xpy_3";
        "kxy_0";"kxy_1";"kxy_2";"kxy_3"] THEN
      SPEC_TAC(`ix:num`,`ix:num`) THEN
      CONV_TAC EXPAND_CASES_CONV THEN
      CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[MULT_CLAUSES; group_pow] THEN
      REWRITE_TAC[EDWARDS25519_GROUP; edwards_0; bignum_of_wordlist] THEN
      CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
      REWRITE_TAC[edwards25519_epprojective; INTEGER_MOD_RING_CLAUSES] THEN
      REWRITE_TAC[p_25519] THEN CONV_TAC INT_REDUCE_CONV;
      ALL_TAC] THEN

    FIRST_X_ASSUM(MP_TAC o check(can
     (term_match [] `read X19 s = y`) o concl)) THEN
    EXPAND_TAC "tab" THEN
    GEN_REWRITE_TAC(LAND_CONV o ONCE_DEPTH_CONV) [GSYM WORD_ADD] THEN
    REPEAT(FIRST_X_ASSUM(K ALL_TAC o check
     (not o (=) [] o intersect
       (`tab:int64`::map (fun i -> mk_var("tab_"^string_of_int i,`:int64`))
                         (1--95)) o
      frees o concl))) THEN
    DISCH_TAC THEN

    ARM_ACCSTEPS_TAC CURVE25519_X25519BASE_BYTE_ALT_EXEC
     [198; 200; 201; 203] (184--211) THEN

    SUBGOAL_THEN
     `edwards25519_epprojective
        (group_zpow edwards25519_group E_25519
          (&2 pow (4 * i) *
          ((&bf + &(bitval(bias))) - &16 * &(bitval bias'))))
        (bignum_from_memory (word_add stackpointer (word 32),4) s211,
         bignum_from_memory (word_add stackpointer (word 64),4) s211,
         bignum_from_memory (word_add stackpointer (word 96),4) s211)`
    MP_TAC THENL
     [CONV_TAC(ONCE_DEPTH_CONV BIGNUM_LEXPAND_CONV) THEN
      ASM_REWRITE_TAC[WORD_SUB_0; WORD_EQ_0; VAL_WORD_BITVAL] THEN
      REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN
      ASM_SIMP_TAC[MOD_LT; ARITH_RULE `i <= 8 ==> i < 2 EXP 64`] THEN
      REWRITE_TAC[BITVAL_EQ_0; COND_SWAP] THEN
      REWRITE_TAC[TAUT `(if p then T else ~q) <=> q ==> p`] THEN
      UNDISCH_TAC
       `(if bias' then 16 - (bf + bitval bias)
         else bf + bitval bias) = ix` THEN
      ASM_CASES_TAC `bias':bool` THEN
      ASM_SIMP_TAC[INT_OF_NUM_CLAUSES; BITVAL_CLAUSES; MULT_CLAUSES;
                   INT_SUB_RZERO; GROUP_NPOW] THEN
      SUBGOAL_THEN `bf + bitval bias <= 16` MP_TAC THENL
       [EXPAND_TAC "bf" THEN REWRITE_TAC[bitval] THEN ARITH_TAC;
        SIMP_TAC[GSYM INT_OF_NUM_EQ; GSYM INT_OF_NUM_SUB] THEN
        DISCH_TAC] THEN
      DISCH_THEN(SUBST1_TAC o MATCH_MP (INT_ARITH
       `a - b:int = c ==> b - a = --c`)) THEN
      UNDISCH_TAC
       `edwards25519_epprojective
         (group_pow edwards25519_group E_25519 (2 EXP (4 * i) * ix))
         (bignum_of_wordlist [ymx_0; ymx_1; ymx_2; ymx_3],
          bignum_of_wordlist [xpy_0; xpy_1; xpy_2; xpy_3],
          bignum_of_wordlist [kxy_0; kxy_1; kxy_2; kxy_3])` THEN
      REWRITE_TAC[INT_OF_NUM_EQ] THEN COND_CASES_TAC THEN
      ASM_REWRITE_TAC[MULT_CLAUSES; INT_NEG_0; INT_MUL_RZERO; GROUP_NPOW] THENL
       [REWRITE_TAC[group_pow; EDWARDS25519_GROUP; edwards_0] THEN
        REWRITE_TAC[edwards25519_epprojective; INTEGER_MOD_RING_CLAUSES] THEN
        REWRITE_TAC[p_25519] THEN CONV_TAC INT_REDUCE_CONV THEN SIMP_TAC[];
        ALL_TAC] THEN
      REWRITE_TAC[INT_MUL_RNEG; INT_OF_NUM_CLAUSES; GROUP_ZPOW_POW] THEN
      SPEC_TAC(`group_pow edwards25519_group E_25519 (2 EXP (4 * i) * ix)`,
               `tp:int#int`) THEN
      REWRITE_TAC[FORALL_PAIR_THM; EDWARDS25519_GROUP; edwards_neg] THEN
      REWRITE_TAC[edwards25519_epprojective; INTEGER_MOD_RING_CLAUSES] THEN
      CONV_TAC INT_REM_DOWN_CONV THEN
      REWRITE_TAC[INT_MUL_LNEG; INT_MUL_RNEG] THEN
      MAP_EVERY X_GEN_TAC [`tx:int`; `ty:int`] THEN
      REWRITE_TAC[INT_ARITH `--x + y:int = y - x /\ y - -- x = x + y`] THEN
      SIMP_TAC[] THEN DISCH_THEN(ASSUME_TAC o SYM o last o CONJUNCTS) THEN
      REWRITE_TAC[INT_LT_REM_EQ; p_25519] THEN CONV_TAC INT_REDUCE_CONV THEN
      REWRITE_TAC[GSYM p_25519] THEN UNDISCH_TAC
       `1 <= ix ==> ~(bignum_of_wordlist[kxy_0; kxy_1; kxy_2; kxy_3] = 0)` THEN
      ASM_SIMP_TAC[LE_1; INT_REM_LNEG; GSYM INT_OF_NUM_EQ; INT_ABS_NUM] THEN
      DISCH_TAC THEN MATCH_MP_TAC INT_CONG_IMP_EQ THEN
      EXISTS_TAC `(&2:int) pow 256` THEN CONJ_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (INT_ARITH
         `y rem p = x
          ==> &0 <= p /\ p < e /\ &0 <= y rem p /\
              y rem p < p /\ &0 <= z /\ z < e
              ==> abs(z - (p - x)) < e`)) THEN
        REWRITE_TAC[INT_LT_REM_EQ; p_25519; INT_REM_POS_EQ] THEN
        CONV_TAC INT_REDUCE_CONV THEN BOUNDER_TAC[];
        REWRITE_TAC[REAL_INT_CONGRUENCE]] THEN
      REWRITE_TAC[INT_POW_EQ_0; INT_OF_NUM_EQ; ARITH_EQ] THEN
      REWRITE_TAC[int_sub_th; int_of_num_th; int_pow_th] THEN
      REWRITE_TAC[p_25519; bignum_of_wordlist; GSYM REAL_OF_NUM_CLAUSES] THEN
      ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o DESUM_RULE) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_INTEGER_TAC;
      ACCUMULATOR_POP_ASSUM_LIST(K ALL_TAC)] THEN

    DISCARD_MATCHING_ASSUMPTIONS [`edwards25519_epprojective a b`] THEN
    MAP_EVERY ABBREV_TAC
     [`ymx = bignum_from_memory (word_add stackpointer (word 32),4) s211`;
      `xpy = bignum_from_memory (word_add stackpointer (word 64),4) s211`;
      `kxy = bignum_from_memory (word_add stackpointer (word 96),4) s211`]
    THEN DISCH_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[BIGNUM_FROM_MEMORY_BYTES]) THEN

    LOCAL_DOUBLE_TWICE4_TAC 0 ["t0"; "z_1"] THEN
    LOCAL_SUB_TWICE4_TAC 0 ["t1"; "y_1"; "x_1"] THEN
    LOCAL_ADD_TWICE4_TAC 0 ["t2"; "y_1"; "x_1"] THEN
    LOCAL_MUL_4_TAC 0 ["t3"; "w_1"; "kxy_2"] THEN
    LOCAL_MUL_4_TAC 0 ["t1"; "t1"; "ymx_2"] THEN
    LOCAL_MUL_4_TAC 0 ["t2"; "t2"; "xpy_2"] THEN
    LOCAL_SUB_TWICE4_TAC 0 ["t4"; "t0"; "t3"] THEN
    LOCAL_ADD_TWICE4_TAC 0 ["t0"; "t0"; "t3"] THEN
    LOCAL_SUB_TWICE4_TAC 0 ["t5"; "t2"; "t1"] THEN
    LOCAL_ADD_TWICE4_TAC 0 ["t1"; "t2"; "t1"] THEN
    LOCAL_MUL_4_TAC 0 ["z_3"; "t4"; "t0"] THEN
    LOCAL_MUL_4_TAC 0 ["x_3"; "t5"; "t4"] THEN
    LOCAL_MUL_4_TAC 0 ["y_3"; "t0"; "t1"] THEN
    LOCAL_MUL_4_TAC 0 ["w_3"; "t5"; "t1"] THEN

    ARM_STEPS_TAC CURVE25519_X25519BASE_BYTE_ALT_EXEC [226] THEN

    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[VAL_WORD_BITVAL; BITVAL_BOUND] THEN CONJ_TAC THENL
     [AP_TERM_TAC THEN UNDISCH_TAC `1 <= i` THEN ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE `n < 1 <=> n = 0`; BITVAL_EQ_0] THEN
      ASM_SIMP_TAC[ARITH_RULE `i < 64 ==> (i + 1 >= 64 <=> i = 63)`] THEN
      DISCH_THEN SUBST_ALL_TAC THEN EXPAND_TAC "bias'" THEN
      MATCH_MP_TAC(ARITH_RULE `x < 8 /\ y <= 1 ==> ~(x + y >= 9)`) THEN
      REWRITE_TAC[BITVAL_BOUND] THEN EXPAND_TAC "bf" THEN
      MATCH_MP_TAC(MESON[LET_TRANS; MOD_LE] `x < b ==> x MOD n < b`) THEN
      SUBST1_TAC(SYM(ASSUME `n_input MOD 2 EXP 254 = nn'`)) THEN ARITH_TAC;
      ALL_TAC] THEN

    DISCARD_STATE_TAC "s226" THEN
    DISCARD_MATCHING_ASSUMPTIONS
     [`aligned a b`; `nonoverlapping_modulo a b c`] THEN

    SUBGOAL_THEN
     `(&nn:int) -
      &2 pow (4 * (i + 1)) *
      (&(nn' DIV 2 EXP (4 * (i + 1))) + &(bitval bias')) =
      (&nn - &2 pow (4 * i) * (&(nn' DIV 2 EXP (4 * i)) + &(bitval bias))) +
      (&2 pow (4 * i) * ((&bf + &(bitval bias)) - &16 * &(bitval bias')))`
    SUBST1_TAC THENL
     [REWRITE_TAC[ARITH_RULE `4 * (i + 1) = 4 * i + 4`] THEN
      REWRITE_TAC[EXP_ADD; INT_POW_ADD] THEN
      REWRITE_TAC[INT_ARITH `n - x:int = (n - y) + p * (a - b) <=>
                             p * b + y = p * a + x`] THEN
      EXPAND_TAC "bf" THEN REWRITE_TAC[INT_OF_NUM_CLAUSES; GSYM DIV_DIV] THEN
      REWRITE_TAC[GSYM LEFT_ADD_DISTRIB; GSYM MULT_ASSOC] THEN
      AP_TERM_TAC THEN ARITH_TAC;
      ALL_TAC] THEN

    FIRST_X_ASSUM(MP_TAC o check(can
       (term_match [] `edwards25519_epprojective p q`) o concl)) THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I
     [edwards25519_exprojective2]) THEN
    REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    SIMP_TAC[GROUP_ZPOW_ADD; GROUP_ZPOW;
             GENERATOR_IN_GROUP_CARRIER_EDWARDS25519] THEN
    MP_TAC(MATCH_MP GROUP_ZPOW GENERATOR_IN_GROUP_CARRIER_EDWARDS25519) THEN
    DISCH_THEN(fun th ->
     MAP_EVERY (MP_TAC o C SPEC th)
     [`&nn - &2 pow (4 * i) * (&(nn' DIV 2 EXP (4 * i)) + &(bitval bias)):int`;
      `&2 pow (4 * i) * ((&bf + &(bitval bias)) - &16 * &(bitval bias')):int`]
     ) THEN
    SPEC_TAC(`group_zpow edwards25519_group E_25519
               (&2 pow (4 * i) * ((&bf + &(bitval bias)) - &16 * &(bitval
              bias')))`,`P2:int#int`) THEN
    SPEC_TAC(`group_zpow edwards25519_group E_25519
               (&nn - &2 pow (4 * i) *
               (&(nn' DIV 2 EXP (4 * i)) + &(bitval bias)))`,`P1:int#int`) THEN
    REPEAT(FIRST_X_ASSUM(K ALL_TAC o check
     (not o (=) [] o intersect [`n_input:num`; `i:num`; `bf:num`; `ix:num`]) o
      frees o concl)) THEN
    REPEAT(FIRST_X_ASSUM(K ALL_TAC o check ((=) [] o frees o concl))) THEN
    REWRITE_TAC[FORALL_PAIR_THM] THEN

    MAP_EVERY X_GEN_TAC [`x1:int`; `y1:int`; `x2:int`; `y2:int`] THEN
    REWRITE_TAC[edwards25519_epprojective] THEN REPEAT STRIP_TAC THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o
      MATCH_MP EDWARDS25519_EXPROJECTIVE_BOUND) THEN

    REPEAT(FIRST_X_ASSUM(MP_TAC o check (is_imp o concl))) THEN
    REPEAT(ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN SIMPLE_ARITH_TAC; STRIP_TAC]) THEN
    DISCH_THEN(K ALL_TAC) THEN
    ASM_REWRITE_TAC[edwards25519_exprojective2] THEN
    REPEAT(FIRST_X_ASSUM(K ALL_TAC o GEN_REWRITE_RULE I [GSYM NOT_LE])) THEN

    RULE_ASSUM_TAC(REWRITE_RULE
     [num_congruent; GSYM INT_OF_NUM_CLAUSES; GSYM INT_OF_NUM_REM]) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM INT_REM_EQ]) THEN
    RULE_ASSUM_TAC(ONCE_REWRITE_RULE[GSYM INT_SUB_REM; GSYM INT_ADD_REM]) THEN
    RULE_ASSUM_TAC(ONCE_REWRITE_RULE[GSYM INT_POW_REM; GSYM INT_MUL_REM]) THEN

    MP_TAC(ISPECL
     [`integer_mod_ring p_25519`; `&e_25519:int`; `&d_25519:int`;
      `x1:int`; `y1:int`;
      `&xn rem &p_25519`; `&yn rem &p_25519`;
      `&zn rem &p_25519`; `&wn rem &p_25519`;
      `x2:int`; `y2:int`;
      `x2:int`; `y2:int`; `&1:int`; `(x2 * y2) rem &p_25519`]
     EDWARDS_EXPROJADD4) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[EDWARDS_NONSINGULAR_25519] THEN
      REPEAT(FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN])) THEN
      SIMP_TAC[EDWARDS25519_GROUP] THEN
      REWRITE_TAC[edwards_curve] THEN STRIP_TAC THEN STRIP_TAC THEN
      REWRITE_TAC[FIELD_INTEGER_MOD_RING; PRIME_P25519] THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I
       [edwards25519_exprojective]) THEN
      REWRITE_TAC[GSYM INT_OF_NUM_REM] THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
      ASM_REWRITE_TAC[exprojective] THEN
      REWRITE_TAC[INTEGER_MOD_RING_CHAR; IN_INTEGER_MOD_RING_CARRIER;
                  INTEGER_MOD_RING_CLAUSES] THEN
      REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES; p_25519; e_25519; d_25519] THEN
      REWRITE_TAC[INT_REM_POS_EQ; INT_LT_REM_EQ] THEN
      CONV_TAC INT_REDUCE_CONV THEN REWRITE_TAC[GSYM p_25519] THEN
      REPEAT CONJ_TAC THEN MATCH_MP_TAC(MESON[RING_DIV_1]
       `x IN ring_carrier f /\ y = ring_1 f ==> ring_div f x y = x`) THEN
      ASM_REWRITE_TAC[INTEGER_MOD_RING_CLAUSES; p_25519] THEN
      REWRITE_TAC[IN_INTEGER_MOD_RING_CARRIER] THEN
      REWRITE_TAC[INT_REM_POS_EQ; INT_LT_REM_EQ] THEN
      CONV_TAC INT_REDUCE_CONV;
      ALL_TAC] THEN

    REWRITE_TAC[edwards25519_exprojective; EDWARDS25519_GROUP] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
    ONCE_REWRITE_TAC[GSYM MOD_MULT_MOD2] THEN
    ASM_REWRITE_TAC[GSYM INT_OF_NUM_REM; GSYM INT_OF_NUM_CLAUSES] THEN
    REWRITE_TAC[edwards_exprojadd4; edwards_exprojadd; edwards25519;
                INTEGER_MOD_RING_CLAUSES] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    SUBGOAL_THEN `&e_25519 = (-- &1) rem &p_25519` SUBST_ALL_TAC THENL
     [REWRITE_TAC[e_25519; p_25519] THEN CONV_TAC INT_REDUCE_CONV;
      ALL_TAC] THEN
    CONV_TAC INT_REM_DOWN_CONV THEN
    REWRITE_TAC[PAIR_EQ] THEN CONV_TAC INT_REM_DOWN_CONV THEN
    REPEAT CONJ_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN INT_ARITH_TAC;

    (*** The trivial loop-back subgoal ***)

    REPEAT STRIP_TAC THEN
    ARM_SIM_TAC CURVE25519_X25519BASE_BYTE_ALT_EXEC (1--2) THEN
    ASM_SIMP_TAC[VAL_WORD_LT; ARITH_RULE `4 * i < 256 <=> i < 64`];

    ALL_TAC] THEN

  (*** Clean up ready for the final translation part ***)

  REWRITE_TAC[GE; LE_REFL; ARITH_RULE `a < 1 <=> a = 0`] THEN
  GHOST_INTRO_TAC `zerobias:num` `\s. val(read X21 s)` THEN
  ASM_CASES_TAC `zerobias = 0` THEN ASM_REWRITE_TAC[ENSURES_TRIVIAL] THEN
  EXPAND_TAC "nn'" THEN
  REWRITE_TAC[ARITH_RULE `(n MOD 2 EXP 254) DIV 2 EXP (4 * 64) = 0`] THEN
  REWRITE_TAC[INT_ADD_RID; INT_MUL_RZERO; INT_SUB_RZERO; GROUP_NPOW] THEN
  GHOST_INTRO_TAC `X:num`
   `bignum_from_memory (word_add stackpointer (word 128),4)` THEN
  GHOST_INTRO_TAC `Y:num`
   `bignum_from_memory (word_add stackpointer (word 160),4)` THEN
  GHOST_INTRO_TAC `Z:num`
   `bignum_from_memory (word_add stackpointer (word 192),4)` THEN
  GHOST_INTRO_TAC `W:num`
   `bignum_from_memory (word_add stackpointer (word 224),4)` THEN
  CONV_TAC NUM_REDUCE_CONV THEN

  REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN

  LOCAL_ADD_TWICE4_TAC 2 ["t1"; "x_3"; "w_3"] THEN
  LOCAL_SUB_TWICE4_TAC 0 ["t2"; "x_3"; "w_3"] THEN

  (*** The inlining of modular inverse ***)

  ARM_STEPS_TAC CURVE25519_X25519BASE_BYTE_ALT_EXEC (5--6) THEN
  LOCAL_MODINV_TAC 7 THEN
  FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP(MESON[PRIME_COPRIME_EQ; PRIME_P25519]
   `(bnx = if p_25519 divides n then 0 else inverse_mod p_25519 n)
    ==> coprime(p_25519,n) ==> bnx = inverse_mod p_25519 n`)) THEN
  ABBREV_TAC
   `t0 =
    read(memory :> bytes(word_add stackpointer (word 256),8 * 4)) s7` THEN

  (*** Final multiplication ***)

  LOCAL_MUL_P25519_TAC 0 ["x_1"; "t1"; "t0"] THEN

  (*** Bytewise store and finish of simulation ***)

  BIGNUM_LDIGITIZE_TAC "res_"
   `read(memory :> bytes(word_add stackpointer (word 128),8 * 4)) s8` THEN
  ARM_STEPS_TAC CURVE25519_X25519BASE_BYTE_ALT_EXEC (9--70) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  TRANS_TAC EQ_TRANS `x_1:num` THEN CONJ_TAC THENL
   [CONV_TAC(LAND_CONV BYTES_EXPAND_CONV) THEN EXPAND_TAC "x_1" THEN
    REWRITE_TAC[bignum_of_wordlist] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[bignum_of_wordlist; val_def] THEN
    REWRITE_TAC[DIMINDEX_8; ARITH_RULE `i < 8 <=> 0 <= i /\ i <= 7`] THEN
    REWRITE_TAC[DIMINDEX_64; ARITH_RULE `i < 64 <=> 0 <= i /\ i <= 63`] THEN
    REWRITE_TAC[GSYM IN_NUMSEG; IN_GSPEC] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[BIT_WORD_USHR; BIT_WORD_ZX] THEN
    REWRITE_TAC[DIMINDEX_8; DIMINDEX_32; DIMINDEX_64] THEN
    CONV_TAC(ONCE_DEPTH_CONV EXPAND_NSUM_CONV) THEN
    CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN ARITH_TAC;
    ASM_REWRITE_TAC[]] THEN

  (*** Basic mathematics mapping things to curve25519 ***)

  REWRITE_TAC[MOD_UNIQUE; PUREX25519_BOUND] THEN
  REWRITE_TAC[num_congruent; GSYM INT_REM_EQ] THEN
  MP_TAC(ISPECL
   [`integer_mod_ring p_25519`; `nn:num`; `9`; `C_25519`]
    PUREX25519) THEN
  REWRITE_TAC[CURVE25519X_CURVE25519_GROUP] THEN ANTS_TAC THENL
   [REWRITE_TAC[GENERATOR_IN_GROUP_CARRIER_CURVE25519] THEN
    REWRITE_TAC[FIELD_INTEGER_MOD_RING; PRIME_P25519] THEN
    REWRITE_TAC[INTEGER_MOD_RING_CHAR; C_25519; montgomery_xmap] THEN
    REWRITE_TAC[INTEGER_MOD_RING_CLAUSES; p_25519] THEN
    CONV_TAC INT_REDUCE_CONV;
    REWRITE_TAC[INTEGER_MOD_RING_OF_NUM] THEN
    DISCH_THEN(SUBST1_TAC o SYM)] THEN

  SUBGOAL_THEN
   `group_pow curve25519_group C_25519 nn =
    curve25519_of_edwards25519
     (group_pow edwards25519_group E_25519 nn)`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM EDWARDS25519_OF_CURVE25519_C25519] THEN
    MP_TAC GROUP_ISOMORPHISMS_EDWARDS25519_CURVE25519 THEN
    REWRITE_TAC[group_isomorphisms] THEN
    DISCH_THEN(CONJUNCTS_THEN2
      (MP_TAC o MATCH_MP GROUP_HOMOMORPHISM_POW) STRIP_ASSUME_TAC) THEN
    RULE_ASSUM_TAC(REWRITE_RULE
     [group_homomorphism; SUBSET; FORALL_IN_IMAGE]) THEN
    ASM_SIMP_TAC[GENERATOR_IN_GROUP_CARRIER_CURVE25519];
    ALL_TAC] THEN

  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I
     [edwards25519_exprojective2]) THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[edwards25519_exprojective] THEN

  REPEAT(FIRST_X_ASSUM(MP_TAC o check (is_imp o concl))) THEN
  REPEAT(ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN NO_TAC; DISCH_TAC]) THEN

  DISCH_TAC THEN REWRITE_TAC[exprojective] THEN
  MP_TAC(SPEC `nn:num`
   (MATCH_MP GROUP_POW GENERATOR_IN_GROUP_CARRIER_EDWARDS25519)) THEN
  SPEC_TAC(`group_pow edwards25519_group E_25519 nn`,`P:int#int`) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`xint:int`; `yint:int`] THEN
  SIMP_TAC[EXPROJECTIVE_ALT; FIELD_INTEGER_MOD_RING; PRIME_P25519] THEN
  REWRITE_TAC[curve25519_of_edwards25519; montgomery_of_edwards] THEN
  REWRITE_TAC[EDWARDS25519_GROUP] THEN GEN_REWRITE_TAC LAND_CONV [IN] THEN
  REWRITE_TAC[edwards_curve; INTEGER_MOD_RING_CLAUSES] THEN
  REWRITE_TAC[IN_INTEGER_MOD_RING_CARRIER] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_REM] THEN CONV_TAC INT_REM_DOWN_CONV THEN
  REWRITE_TAC[p_25519] THEN CONV_TAC INT_REDUCE_CONV THEN
  REWRITE_TAC[GSYM p_25519; GSYM CONJ_ASSOC] THEN
  GEN_REWRITE_TAC I [TAUT
   `p /\ p' /\ q /\ q' ==> r <=> p ==> q ==> p' /\ q' ==> r`] THEN
  MAP_EVERY (fun t -> SPEC_TAC(t,t)) [`yint:int`; `xint:int`] THEN
  REWRITE_TAC[RIGHT_FORALL_IMP_THM; GSYM INT_FORALL_POS] THEN
  MAP_EVERY X_GEN_TAC [`x:num`; `y:num`] THEN
  REWRITE_TAC[PAIR_EQ; INT_OF_NUM_CLAUSES; INT_OF_NUM_REM] THEN
  REWRITE_TAC[LE_0; p_25519] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[GSYM p_25519] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [GSYM CONG] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o MATCH_MP (NUMBER_RULE
   `(e * x + y == 1 + d * x * y) (mod p)
    ==> ((x == 0) (mod p) ==> (y == 1) (mod p)) /\
        ((y == 1) (mod p) ==> (d * x == e * x) (mod p))`)) THEN

  (*** Naive case-splits for degenerate cases, which in fact never happen ***)

  ASM_CASES_TAC `x = 0` THEN ASM_REWRITE_TAC[] THENL
   [UNDISCH_THEN `x = 0` SUBST1_TAC THEN
    REWRITE_TAC[EXP_ZERO; ARITH_EQ; CONG_REFL] THEN
    MP_TAC(SPECL [`p_25519`; `1`; `y:num`] CONG_SQUARE_1_PRIME_POWER) THEN
    REWRITE_TAC[PRIME_P25519] THEN ANTS_TAC THENL
     [REWRITE_TAC[p_25519; ARITH_EQ]; REWRITE_TAC[EXP_1]] THEN
    DISCH_THEN SUBST1_TAC THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN
    ASM_SIMP_TAC[CONG; MOD_LT] THEN
    REWRITE_TAC[p_25519] THEN CONV_TAC NUM_REDUCE_CONV THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_REWRITE_TAC[montgomery_xmap] THEN
    REWRITE_TAC[GSYM p_25519; INTEGER_MOD_RING_CLAUSES] THEN
    REWRITE_TAC[MULT_CLAUSES; MOD_0] THEN
    (ASM_CASES_TAC `X MOD p_25519 = 0` THEN ASM_REWRITE_TAC[]) THEN
    POP_ASSUM MP_TAC THEN
    REWRITE_TAC[INT_OF_NUM_CLAUSES; GSYM DIVIDES_MOD] THEN
    DISCH_TAC THEN REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    REWRITE_TAC[GSYM CONG] THEN DISCH_THEN(MP_TAC o MATCH_MP(NUMBER_RULE
     `(W * Z == X * Y) (mod p)
      ==> p divides X /\ coprime(p,Z) ==> (X + W == 0) (mod p)`)) THEN
    ASM_SIMP_TAC[PRIME_COPRIME_EQ; PRIME_P25519] THEN
    MATCH_MP_TAC(NUMBER_RULE
     `(y == x + w) (mod p) ==> (x + w == 0) (mod p) ==> p divides y * y'`) THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[montgomery_xmap]] THEN

  ASM_CASES_TAC `y = 1` THENL
   [UNDISCH_THEN `y = 1` SUBST1_TAC THEN DISCH_THEN(MP_TAC o CONJUNCT2) THEN
    REWRITE_TAC[EXP_ONE; CONG_REFL] THEN
    DISCH_THEN(MP_TAC o MATCH_MP (NUMBER_RULE
     `(d * x:num == e * x) (mod p)
      ==> coprime(p,x) ==> (d == e) (mod p)`)) THEN
    SIMP_TAC[PRIME_COPRIME_EQ; PRIME_P25519; PRIME_DIVEXP_EQ] THEN
    ASM_SIMP_TAC[DIVIDES_MOD; MOD_LT] THEN
    REWRITE_TAC[CONG; d_25519; e_25519; p_25519] THEN
    CONV_TAC NUM_REDUCE_CONV;
    DISCH_THEN(K ALL_TAC) THEN STRIP_TAC] THEN

  SUBGOAL_THEN
   `!f x y z:int.
        field f /\
        x IN ring_carrier f /\ y IN ring_carrier f /\ z IN ring_carrier f /\
        ring_mul f y z = x /\ ~(y = ring_0 f)
              ==> z = ring_div f x y`
  MATCH_MP_TAC THENL [POP_ASSUM_LIST(K ALL_TAC) THEN FIELD_TAC; ALL_TAC] THEN
  REWRITE_TAC[FIELD_INTEGER_MOD_RING; PRIME_P25519] THEN
  REWRITE_TAC[IN_INTEGER_MOD_RING_CARRIER] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_REM; INT_REM_POS_EQ; INT_LT_REM_EQ] THEN
  REWRITE_TAC[p_25519] THEN CONV_TAC INT_REDUCE_CONV THEN
  REWRITE_TAC[GSYM p_25519; INTEGER_MOD_RING_CLAUSES] THEN
  CONV_TAC INT_REM_DOWN_CONV THEN REWRITE_TAC[INT_REM_EQ_0; INT_REM_EQ] THEN
  REWRITE_TAC[INTEGER_RULE `p divides x - y <=> (y:int == x) (mod p)`] THEN
  REWRITE_TAC[GSYM INT_REM_EQ; p_25519] THEN CONV_TAC INT_REDUCE_CONV THEN
  ASM_REWRITE_TAC[GSYM p_25519] THEN
  ASM_SIMP_TAC[MOD_LT; INT_OF_NUM_REM; INT_OF_NUM_CLAUSES] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_REM; GSYM INT_OF_NUM_CLAUSES] THEN
  REWRITE_TAC[INT_REM_EQ] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM CONG; GSYM DIVIDES_MOD]) THEN

  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  MATCH_MP_TAC(TAUT `p /\ (p /\ q ==> r) ==> (p ==> q) ==> r`) THEN
  CONJ_TAC THENL
   [SIMP_TAC[PRIME_COPRIME_EQ; PRIME_P25519] THEN REWRITE_TAC[num_divides] THEN
    FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP INT_CONG_DIVIDES) THEN
    REWRITE_TAC[GSYM INT_CONG; GSYM num_congruent] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP (NUMBER_RULE
     `(W * Z == X * Y) (mod p) ==> (X == W) (mod p) /\ coprime(p,X)
      ==> (Z:num == Y) (mod p)`)) THEN
    ASM_REWRITE_TAC[NOT_IMP] THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (NUMBER_RULE
       `(x * Z:num == X) (mod p)
        ==> coprime(p,x) /\ coprime(p,Z) ==> coprime(p,X)`)) THEN
      ASM_SIMP_TAC[PRIME_COPRIME_EQ; PRIME_P25519] THEN
      ASM_SIMP_TAC[DIVIDES_MOD; MOD_LT];
      DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o MATCH_MP (NUMBER_RULE
       `(y * Z == Y) (mod p)
        ==> coprime(p,Z) /\ (Z == Y) (mod p) ==> (y == 1) (mod p)`)) THEN
      ASM_SIMP_TAC[PRIME_COPRIME_EQ; PRIME_P25519] THEN
      ASM_SIMP_TAC[CONG; MOD_LT] THEN REWRITE_TAC[p_25519] THEN
      CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[]];
    DISCH_THEN(MP_TAC o MATCH_MP (MESON[INVERSE_MOD_RMUL]
     `coprime(p,x) /\ y = inverse_mod p x ==> (x * y == 1) (mod p)`))] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [num_congruent])) THEN
  UNDISCH_TAC `(&t2:int == &X - &W) (mod &p_25519)` THEN
  UNDISCH_TAC `~(p_25519 divides Z)` THEN
  ASM_SIMP_TAC[GSYM PRIME_COPRIME_EQ; PRIME_P25519] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_CLAUSES; num_congruent; num_coprime] THEN
  CONV_TAC INTEGER_RULE);;

let CURVE25519_X25519BASE_BYTE_ALT_SUBROUTINE_CORRECT = time prove
 (`!tables res scalar n pc stackpointer returnaddress.
    aligned 16 stackpointer /\
    adrp_within_bounds (word tables) (word(pc + 0x118)) /\
    ALL (nonoverlapping (word_sub stackpointer (word 496),496))
        [(word pc,0x2434); (word tables,48576); (res,32); (scalar,32)] /\
    nonoverlapping (res,32) (word pc,0x2434)
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc)
                (curve25519_x25519base_byte_alt_mc pc tables) /\
              read PC s = word pc /\
              bytes_loaded s (word tables)
                curve25519_x25519base_byte_alt_constant_data /\
              read SP s = stackpointer /\
              read X30 s = returnaddress /\
              C_ARGUMENTS [res; scalar] s /\
              read (memory :> bytes(scalar,32)) s = n)
         (\s. read PC s = returnaddress /\
              read (memory :> bytes(res,32)) s = rfcx25519(n,9))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(res,32);
                      memory :> bytes(word_sub stackpointer (word 496),496)])`,
  REWRITE_TAC[BYTES_LOADED_DATA; fst CURVE25519_X25519BASE_BYTE_ALT_EXEC] THEN
  ARM_ADD_RETURN_STACK_TAC CURVE25519_X25519BASE_BYTE_ALT_EXEC
    (REWRITE_RULE[BYTES_LOADED_DATA; fst CURVE25519_X25519BASE_BYTE_ALT_EXEC]
     CURVE25519_X25519BASE_BYTE_ALT_CORRECT)
    `[X19; X20; X21; X22; X23; X24]` 496);;
