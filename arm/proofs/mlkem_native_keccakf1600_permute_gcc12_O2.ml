(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Keccak-f1600 permutation.                                                 *)
(* This is the code for mlkem_keccakf1600_permute from mlkem-native's        *)
(* portable C implementation compiled by gcc 12 with -O2 (see                *)
(* mlkem_native/README.md). Unlike the hand-written kernels, it reads its    *)
(* own table of round constants from the read-only data rather than taking   *)
(* it as an argument, and it does two rounds in each iteration of its loop.  *)
(* At the end, the theorem for the code in the whole image is also stated    *)
(* for the state as a 1600-bit word, with keccak_f1600 of common/fips202.ml. *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "arm/proofs/utils/keccak_spec.ml";;

(**** print_literal_relocs_from_elf
        ~map_symbol_name:(fun _ ->
          "mlkem_native_keccakf1600_permute_gcc12_O2_data")
        "arm/mlkem_native/mlkem_native_keccakf1600_permute_gcc12_O2.o";;
 ****)

let mlkem_native_keccakf1600_permute_gcc12_O2_mc,
    mlkem_native_keccakf1600_permute_gcc12_O2_data =
  define_assert_relocs_from_elf
    ~map_symbol_name:(function
      | "WHOLE_READONLY" | "ltmp1"
      | "mlkem_native_keccakf1600_permute_gcc12_O2_rc" ->
          "mlkem_native_keccakf1600_permute_gcc12_O2_data"
      | s -> failwith ("unknown symbol: " ^ s))
    "mlkem_native_keccakf1600_permute_gcc12_O2_mc"
    "arm/mlkem_native/mlkem_native_keccakf1600_permute_gcc12_O2.o"
(fun w BL ADR ADRP ADD_rri64 LDR_Q_rri -> [
  w 0xa9b453f3;         (* arm_STP X19 X20 SP (Preimmediate_Offset (iword
                           (-- &192))) *)
  ADRP (mk_var("mlkem_native_keccakf1600_permute_gcc12_O2_data",`:num`),0,4,1);
  ADD_rri64 (mk_var("mlkem_native_keccakf1600_permute_gcc12_O2_data",`:num`),
            0,1,1);
  w 0xa9439009;         (* arm_LDP X9 X4 X0 (Immediate_Offset (iword (&56))) *)
  w 0xf90033e1;         (* arm_STR X1 SP (Immediate_Offset (word 96)) *)
  w 0x91030021;         (* arm_ADD X1 X1 (rvalue (word 192)) *)
  w 0xf9005be1;         (* arm_STR X1 SP (Immediate_Offset (word 176)) *)
  w 0xf9400001;         (* arm_LDR X1 X0 (Immediate_Offset (word 0)) *)
  w 0xf90037e1;         (* arm_STR X1 SP (Immediate_Offset (word 104)) *)
  w 0xf9400801;         (* arm_LDR X1 X0 (Immediate_Offset (word 16)) *)
  w 0xf9003be4;         (* arm_STR X4 SP (Immediate_Offset (word 112)) *)
  w 0xf9403804;         (* arm_LDR X4 X0 (Immediate_Offset (word 112)) *)
  w 0xa9015bf5;         (* arm_STP X21 X22 SP (Immediate_Offset (iword
                           (&16))) *)
  w 0xaa0903f2;         (* arm_MOV X18 X9 *)
  w 0xf9400402;         (* arm_LDR X2 X0 (Immediate_Offset (word 8)) *)
  w 0xa90263f7;         (* arm_STP X23 X24 SP (Immediate_Offset (iword
                           (&32))) *)
  w 0xf9401403;         (* arm_LDR X3 X0 (Immediate_Offset (word 40)) *)
  w 0xa9036bf9;         (* arm_STP X25 X26 SP (Immediate_Offset (iword
                           (&48))) *)
  w 0xa941dc1a;         (* arm_LDP X26 X23 X0 (Immediate_Offset (iword
                           (&24))) *)
  w 0xa90473fb;         (* arm_STP X27 X28 SP (Immediate_Offset (iword
                           (&64))) *)
  w 0xa944d407;         (* arm_LDP X7 X21 X0 (Immediate_Offset (iword
                           (&72))) *)
  w 0xf9003fe4;         (* arm_STR X4 SP (Immediate_Offset (word 120)) *)
  w 0xa945c014;         (* arm_LDP X20 X16 X0 (Immediate_Offset (iword
                           (&88))) *)
  w 0xf90047e1;         (* arm_STR X1 SP (Immediate_Offset (word 136)) *)
  w 0xf9401801;         (* arm_LDR X1 X0 (Immediate_Offset (word 48)) *)
  w 0xaa1703fc;         (* arm_MOV X28 X23 *)
  w 0xf940340b;         (* arm_LDR X11 X0 (Immediate_Offset (word 104)) *)
  w 0xf9002bfe;         (* arm_STR X30 SP (Immediate_Offset (word 80)) *)
  w 0xa947b016;         (* arm_LDP X22 X12 X0 (Immediate_Offset (iword
                           (&120))) *)
  w 0xaa1403ee;         (* arm_MOV X14 X20 *)
  w 0xa94be404;         (* arm_LDP X4 X25 X0 (Immediate_Offset (iword
                           (&184))) *)
  w 0xaa1503f7;         (* arm_MOV X23 X21 *)
  w 0xa9489406;         (* arm_LDP X6 X5 X0 (Immediate_Offset (iword
                           (&136))) *)
  w 0xaa0203f4;         (* arm_MOV X20 X2 *)
  w 0xa949a80d;         (* arm_LDP X13 X10 X0 (Immediate_Offset (iword
                           (&152))) *)
  w 0xaa1603fe;         (* arm_MOV X30 X22 *)
  w 0xa94abc13;         (* arm_LDP X19 X15 X0 (Immediate_Offset (iword
                           (&168))) *)
  w 0xaa1903e9;         (* arm_MOV X9 X25 *)
  w 0xaa0b03fb;         (* arm_MOV X27 X11 *)
  w 0xaa0703f6;         (* arm_MOV X22 X7 *)
  w 0xaa0c03f1;         (* arm_MOV X17 X12 *)
  w 0xaa0303f9;         (* arm_MOV X25 X3 *)
  w 0xf90043fa;         (* arm_STR X26 SP (Immediate_Offset (word 128)) *)
  w 0xf9005fe0;         (* arm_STR X0 SP (Immediate_Offset (word 184)) *)
  w 0xa94863eb;         (* arm_LDP X11 X24 SP (Immediate_Offset (iword
                           (&128))) *)
  w 0xca06020c;         (* arm_EOR X12 X16 X6 *)
  w 0xa946d7e0;         (* arm_LDP X0 X21 SP (Immediate_Offset (iword
                           (&104))) *)
  w 0xca1e02e2;         (* arm_EOR X2 X23 X30 *)
  w 0xca1101da;         (* arm_EOR X26 X14 X17 *)
  w 0xca120307;         (* arm_EOR X7 X24 X18 *)
  w 0xca0c00e7;         (* arm_EOR X7 X7 X12 *)
  w 0xf9403fec;         (* arm_LDR X12 SP (Immediate_Offset (word 120)) *)
  w 0xca190003;         (* arm_EOR X3 X0 X25 *)
  w 0xca150168;         (* arm_EOR X8 X11 X21 *)
  w 0xca05036b;         (* arm_EOR X11 X27 X5 *)
  w 0xca010280;         (* arm_EOR X0 X20 X1 *)
  w 0xca020063;         (* arm_EOR X3 X3 X2 *)
  w 0xca0b0108;         (* arm_EOR X8 X8 X11 *)
  w 0xca0f00e7;         (* arm_EOR X7 X7 X15 *)
  w 0xca0a0063;         (* arm_EOR X3 X3 X10 *)
  w 0xca040108;         (* arm_EOR X8 X8 X4 *)
  w 0xca00035a;         (* arm_EOR X26 X26 X0 *)
  w 0xca160382;         (* arm_EOR X2 X28 X22 *)
  w 0xca0d0180;         (* arm_EOR X0 X12 X13 *)
  w 0xca13035a;         (* arm_EOR X26 X26 X19 *)
  w 0xca000042;         (* arm_EOR X2 X2 X0 *)
  w 0xcac7fc60;         (* arm_EOR X0 X3 (Shiftedreg X7 ROR 63) *)
  w 0xcac3fd03;         (* arm_EOR X3 X8 (Shiftedreg X3 ROR 63) *)
  w 0xcac8ff48;         (* arm_EOR X8 X26 (Shiftedreg X8 ROR 63) *)
  w 0xca090042;         (* arm_EOR X2 X2 X9 *)
  w 0xca010001;         (* arm_EOR X1 X0 X1 *)
  w 0xca140015;         (* arm_EOR X21 X0 X20 *)
  w 0xca110011;         (* arm_EOR X17 X0 X17 *)
  w 0xca120114;         (* arm_EOR X20 X8 X18 *)
  w 0xca0e000e;         (* arm_EOR X14 X0 X14 *)
  w 0xca130000;         (* arm_EOR X0 X0 X19 *)
  w 0xcadafc5a;         (* arm_EOR X26 X2 (Shiftedreg X26 ROR 63) *)
  w 0xa9474ff2;         (* arm_LDP X18 X19 SP (Immediate_Offset (iword
                           (&112))) *)
  w 0xcac2fce2;         (* arm_EOR X2 X7 (Shiftedreg X2 ROR 63) *)
  w 0xf94033e7;         (* arm_LDR X7 SP (Immediate_Offset (word 96)) *)
  w 0xca06010c;         (* arm_EOR X12 X8 X6 *)
  w 0xf94043e6;         (* arm_LDR X6 SP (Immediate_Offset (word 128)) *)
  w 0xca100110;         (* arm_EOR X16 X8 X16 *)
  w 0xca0f010f;         (* arm_EOR X15 X8 X15 *)
  w 0xca090069;         (* arm_EOR X9 X3 X9 *)
  w 0xca180108;         (* arm_EOR X8 X8 X24 *)
  w 0xca050045;         (* arm_EOR X5 X2 X5 *)
  w 0xf94000e7;         (* arm_LDR X7 X7 (Immediate_Offset (word 0)) *)
  w 0x93c9c929;         (* arm_ROR X9 X9 50 *)
  w 0xca0d006b;         (* arm_EOR X11 X3 X13 *)
  w 0x93c5aca5;         (* arm_ROR X5 X5 43 *)
  w 0xca1b004d;         (* arm_EOR X13 X2 X27 *)
  w 0xca040044;         (* arm_EOR X4 X2 X4 *)
  w 0xca060046;         (* arm_EOR X6 X2 X6 *)
  w 0xca120042;         (* arm_EOR X2 X2 X18 *)
  w 0x93c15032;         (* arm_ROR X18 X1 20 *)
  w 0x93c80901;         (* arm_ROR X1 X8 2 *)
  w 0xf94037e8;         (* arm_LDR X8 SP (Immediate_Offset (word 104)) *)
  w 0xf90037f2;         (* arm_STR X18 SP (Immediate_Offset (word 104)) *)
  w 0xca160076;         (* arm_EOR X22 X3 X22 *)
  w 0x93d05610;         (* arm_ROR X16 X16 21 *)
  w 0xa90887e7;         (* arm_STP X7 X1 SP (Immediate_Offset (iword
                           (&136))) *)
  w 0xca1c0067;         (* arm_EOR X7 X3 X28 *)
  w 0xca130063;         (* arm_EOR X3 X3 X19 *)
  w 0x8a250133;         (* arm_BIC X19 X9 X5 *)
  w 0xca170358;         (* arm_EOR X24 X26 X23 *)
  w 0xca1e0341;         (* arm_EOR X1 X26 X30 *)
  w 0x8a32021e;         (* arm_BIC X30 X16 X18 *)
  w 0x8a3000b2;         (* arm_BIC X18 X5 X16 *)
  w 0xca100270;         (* arm_EOR X16 X19 X16 *)
  w 0xf94037f3;         (* arm_LDR X19 SP (Immediate_Offset (word 104)) *)
  w 0x93d14e31;         (* arm_ROR X17 X17 19 *)
  w 0xca190357;         (* arm_EOR X23 X26 X25 *)
  w 0x93d8f718;         (* arm_ROR X24 X24 61 *)
  w 0xf94047f9;         (* arm_LDR X25 SP (Immediate_Offset (word 136)) *)
  w 0xca0a034a;         (* arm_EOR X10 X26 X10 *)
  w 0xca080348;         (* arm_EOR X8 X26 X8 *)
  w 0xca130253;         (* arm_EOR X19 X18 X19 *)
  w 0x93d6b2d6;         (* arm_ROR X22 X22 44 *)
  w 0x8a380232;         (* arm_BIC X18 X17 X24 *)
  w 0x93c690c6;         (* arm_ROR X6 X6 36 *)
  w 0x93cf0def;         (* arm_ROR X15 X15 3 *)
  w 0x93d4ea94;         (* arm_ROR X20 X20 58 *)
  w 0x93cd9dad;         (* arm_ROR X13 X13 39 *)
  w 0x93cbe16b;         (* arm_ROR X11 X11 56 *)
  w 0x8a36031b;         (* arm_BIC X27 X24 X22 *)
  w 0x93cab94a;         (* arm_ROR X10 X10 46 *)
  w 0xca160252;         (* arm_EOR X18 X18 X22 *)
  w 0x8a2602d6;         (* arm_BIC X22 X22 X6 *)
  w 0xf9003bf0;         (* arm_STR X16 SP (Immediate_Offset (word 112)) *)
  w 0x8a290110;         (* arm_BIC X16 X8 X9 *)
  w 0xca06037b;         (* arm_EOR X27 X27 X6 *)
  w 0x8a3401ba;         (* arm_BIC X26 X13 X20 *)
  w 0xca050210;         (* arm_EOR X16 X16 X5 *)
  w 0x93d5feb5;         (* arm_ROR X21 X21 63 *)
  w 0x8a3101e5;         (* arm_BIC X5 X15 X17 *)
  w 0xca19011c;         (* arm_EOR X28 X8 X25 *)
  w 0x8a2f00c6;         (* arm_BIC X6 X6 X15 *)
  w 0xca0f02d6;         (* arm_EOR X22 X22 X15 *)
  w 0x8a2b014f;         (* arm_BIC X15 X10 X11 *)
  w 0x93ced9ce;         (* arm_ROR X14 X14 54 *)
  w 0xca1c03dc;         (* arm_EOR X28 X30 X28 *)
  w 0x93d772f7;         (* arm_ROR X23 X23 28 *)
  w 0xca15035e;         (* arm_EOR X30 X26 X21 *)
  w 0xca0d01ef;         (* arm_EOR X15 X15 X13 *)
  w 0xca1800ba;         (* arm_EOR X26 X5 X24 *)
  w 0xca1100c5;         (* arm_EOR X5 X6 X17 *)
  w 0x8a2d0166;         (* arm_BIC X6 X11 X13 *)
  w 0x8a35028d;         (* arm_BIC X13 X20 X21 *)
  w 0x8a2a02b5;         (* arm_BIC X21 X21 X10 *)
  w 0x93c42084;         (* arm_ROR X4 X4 8 *)
  w 0x8a3701d9;         (* arm_BIC X25 X14 X23 *)
  w 0x93c794e7;         (* arm_ROR X7 X7 37 *)
  w 0xca0b02ab;         (* arm_EOR X11 X21 X11 *)
  w 0x93ccc58c;         (* arm_ROR X12 X12 49 *)
  w 0xca070339;         (* arm_EOR X25 X25 X7 *)
  w 0xa907afe5;         (* arm_STP X5 X11 SP (Immediate_Offset (iword
                           (&120))) *)
  w 0x8a2702eb;         (* arm_BIC X11 X23 X7 *)
  w 0x8a2400e7;         (* arm_BIC X7 X7 X4 *)
  w 0xca0a01aa;         (* arm_EOR X10 X13 X10 *)
  w 0x8a2c0085;         (* arm_BIC X5 X4 X12 *)
  w 0x8a2e018d;         (* arm_BIC X13 X12 X14 *)
  w 0xca0c00e7;         (* arm_EOR X7 X7 X12 *)
  w 0x93c36463;         (* arm_ROR X3 X3 25 *)
  w 0xf94037ec;         (* arm_LDR X12 SP (Immediate_Offset (word 104)) *)
  w 0x93c15c21;         (* arm_ROR X1 X1 23 *)
  w 0xf9404bf5;         (* arm_LDR X21 SP (Immediate_Offset (word 144)) *)
  w 0x93c0f800;         (* arm_ROR X0 X0 62 *)
  w 0xf90047ea;         (* arm_STR X10 SP (Immediate_Offset (word 136)) *)
  w 0x93c22442;         (* arm_ROR X2 X2 9 *)
  w 0x8a230038;         (* arm_BIC X24 X1 X3 *)
  w 0xca0e00a5;         (* arm_EOR X5 X5 X14 *)
  w 0x8a280188;         (* arm_BIC X8 X12 X8 *)
  w 0x8a21000e;         (* arm_BIC X14 X0 X1 *)
  w 0xf9403bec;         (* arm_LDR X12 SP (Immediate_Offset (word 112)) *)
  w 0xca020318;         (* arm_EOR X24 X24 X2 *)
  w 0x8a350051;         (* arm_BIC X17 X2 X21 *)
  w 0xca0301ce;         (* arm_EOR X14 X14 X3 *)
  w 0x8a22006a;         (* arm_BIC X10 X3 X2 *)
  w 0xca1701ad;         (* arm_EOR X13 X13 X23 *)
  w 0xa9480be3;         (* arm_LDP X3 X2 SP (Immediate_Offset (iword
                           (&128))) *)
  w 0xca0501f7;         (* arm_EOR X23 X15 X5 *)
  w 0xca1a018c;         (* arm_EOR X12 X12 X26 *)
  w 0xca090108;         (* arm_EOR X8 X8 X9 *)
  w 0xca170189;         (* arm_EOR X9 X12 X23 *)
  w 0xca1400c6;         (* arm_EOR X6 X6 X20 *)
  w 0xf9403ff7;         (* arm_LDR X23 SP (Immediate_Offset (word 120)) *)
  w 0xca1b0394;         (* arm_EOR X20 X28 X27 *)
  w 0xca000231;         (* arm_EOR X17 X17 X0 *)
  w 0xca04016b;         (* arm_EOR X11 X11 X4 *)
  w 0xca1903c4;         (* arm_EOR X4 X30 X25 *)
  w 0xca0e0129;         (* arm_EOR X9 X9 X14 *)
  w 0xca17020c;         (* arm_EOR X12 X16 X23 *)
  w 0xca040294;         (* arm_EOR X20 X20 X4 *)
  w 0xca0202d7;         (* arm_EOR X23 X22 X2 *)
  w 0xca15014a;         (* arm_EOR X10 X10 X21 *)
  w 0xca0d00c4;         (* arm_EOR X4 X6 X13 *)
  w 0xca110162;         (* arm_EOR X2 X11 X17 *)
  w 0x8a2002a0;         (* arm_BIC X0 X21 X0 *)
  w 0xca070063;         (* arm_EOR X3 X3 X7 *)
  w 0xca120275;         (* arm_EOR X21 X19 X18 *)
  w 0xca010000;         (* arm_EOR X0 X0 X1 *)
  w 0xca0402a4;         (* arm_EOR X4 X21 X4 *)
  w 0xca0a0281;         (* arm_EOR X1 X20 X10 *)
  w 0xca030183;         (* arm_EOR X3 X12 X3 *)
  w 0xca0202e2;         (* arm_EOR X2 X23 X2 *)
  w 0xcac9fc2c;         (* arm_EOR X12 X1 (Shiftedreg X9 ROR 63) *)
  w 0xca180084;         (* arm_EOR X4 X4 X24 *)
  w 0xca000063;         (* arm_EOR X3 X3 X0 *)
  w 0xca080042;         (* arm_EOR X2 X2 X8 *)
  w 0xca0c0275;         (* arm_EOR X21 X19 X12 *)
  w 0xca0c0252;         (* arm_EOR X18 X18 X12 *)
  w 0xca0c01ad;         (* arm_EOR X13 X13 X12 *)
  w 0xca0c00c6;         (* arm_EOR X6 X6 X12 *)
  w 0xca0c0318;         (* arm_EOR X24 X24 X12 *)
  w 0xcac1fc61;         (* arm_EOR X1 X3 (Shiftedreg X1 ROR 63) *)
  w 0xf9403bec;         (* arm_LDR X12 SP (Immediate_Offset (word 112)) *)
  w 0xcac3fc83;         (* arm_EOR X3 X4 (Shiftedreg X3 ROR 63) *)
  w 0xcac4fc44;         (* arm_EOR X4 X2 (Shiftedreg X4 ROR 63) *)
  w 0xcac2fd22;         (* arm_EOR X2 X9 (Shiftedreg X2 ROR 63) *)
  w 0xf94033e9;         (* arm_LDR X9 SP (Immediate_Offset (word 96)) *)
  w 0xca030353;         (* arm_EOR X19 X26 X3 *)
  w 0xca0301ef;         (* arm_EOR X15 X15 X3 *)
  w 0xca0301ce;         (* arm_EOR X14 X14 X3 *)
  w 0xca0300a5;         (* arm_EOR X5 X5 X3 *)
  w 0xca030183;         (* arm_EOR X3 X12 X3 *)
  w 0xf94047ec;         (* arm_LDR X12 SP (Immediate_Offset (word 136)) *)
  w 0xca020217;         (* arm_EOR X23 X16 X2 *)
  w 0xf9400534;         (* arm_LDR X20 X9 (Immediate_Offset (word 8)) *)
  w 0xca0102d6;         (* arm_EOR X22 X22 X1 *)
  w 0xf94043f0;         (* arm_LDR X16 SP (Immediate_Offset (word 128)) *)
  w 0xca010231;         (* arm_EOR X17 X17 X1 *)
  w 0xca01016b;         (* arm_EOR X11 X11 X1 *)
  w 0xca010108;         (* arm_EOR X8 X8 X1 *)
  w 0xf90037f4;         (* arm_STR X20 SP (Immediate_Offset (word 104)) *)
  w 0xca010194;         (* arm_EOR X20 X12 X1 *)
  w 0xca040321;         (* arm_EOR X1 X25 X4 *)
  w 0xca0200e7;         (* arm_EOR X7 X7 X2 *)
  w 0xf9403ff9;         (* arm_LDR X25 SP (Immediate_Offset (word 120)) *)
  w 0xca020000;         (* arm_EOR X0 X0 X2 *)
  w 0xca020210;         (* arm_EOR X16 X16 X2 *)
  w 0x93d4669a;         (* arm_ROR X26 X20 25 *)
  w 0xca020322;         (* arm_EOR X2 X25 X2 *)
  w 0x93c15c34;         (* arm_ROR X20 X1 23 *)
  w 0xf94037f9;         (* arm_LDR X25 SP (Immediate_Offset (word 104)) *)
  w 0x93c22441;         (* arm_ROR X1 X2 9 *)
  w 0x93d25252;         (* arm_ROR X18 X18 20 *)
  w 0x93d1ca31;         (* arm_ROR X17 X17 50 *)
  w 0x93c7ace7;         (* arm_ROR X7 X7 43 *)
  w 0xca0403c9;         (* arm_EOR X9 X30 X4 *)
  w 0x93cf55ef;         (* arm_ROR X15 X15 21 *)
  w 0xca04036c;         (* arm_EOR X12 X27 X4 *)
  w 0xca04014a;         (* arm_EOR X10 X10 X4 *)
  w 0xca040384;         (* arm_EOR X4 X28 X4 *)
  w 0xa90953e1;         (* arm_STP X1 X20 SP (Immediate_Offset (iword
                           (&144))) *)
  w 0x8a3201fe;         (* arm_BIC X30 X15 X18 *)
  w 0xf94033e1;         (* arm_LDR X1 SP (Immediate_Offset (word 96)) *)
  w 0xca190094;         (* arm_EOR X20 X4 X25 *)
  w 0x8a270239;         (* arm_BIC X25 X17 X7 *)
  w 0xf9003bf9;         (* arm_STR X25 SP (Immediate_Offset (word 112)) *)
  w 0x93ce0dce;         (* arm_ROR X14 X14 3 *)
  w 0x8a2f00fc;         (* arm_BIC X28 X7 X15 *)
  w 0x93d792f7;         (* arm_ROR X23 X23 36 *)
  w 0x8a24025b;         (* arm_BIC X27 X18 X4 *)
  w 0xca1403de;         (* arm_EOR X30 X30 X20 *)
  w 0x93d6b2d6;         (* arm_ROR X22 X22 44 *)
  w 0x93c9f529;         (* arm_ROR X9 X9 61 *)
  w 0x8a310084;         (* arm_BIC X4 X4 X17 *)
  w 0x93cd4dad;         (* arm_ROR X13 X13 19 *)
  w 0xca120394;         (* arm_EOR X20 X28 X18 *)
  w 0x91004021;         (* arm_ADD X1 X1 (rvalue (word 16)) *)
  w 0xca11037c;         (* arm_EOR X28 X27 X17 *)
  w 0xa9067be1;         (* arm_STP X1 X30 SP (Immediate_Offset (iword
                           (&96))) *)
  w 0x8a2e02fe;         (* arm_BIC X30 X23 X14 *)
  w 0xf9403bf1;         (* arm_LDR X17 SP (Immediate_Offset (word 112)) *)
  w 0xf9003ffe;         (* arm_STR X30 SP (Immediate_Offset (word 120)) *)
  w 0x93cbe16b;         (* arm_ROR X11 X11 56 *)
  w 0x8a3702c2;         (* arm_BIC X2 X22 X23 *)
  w 0x93d09e10;         (* arm_ROR X16 X16 39 *)
  w 0xca070084;         (* arm_EOR X4 X4 X7 *)
  w 0x8a2901a1;         (* arm_BIC X1 X13 X9 *)
  w 0x93d3ea73;         (* arm_ROR X19 X19 58 *)
  w 0x93cab94a;         (* arm_ROR X10 X10 46 *)
  w 0x93c02000;         (* arm_ROR X0 X0 8 *)
  w 0x8a360139;         (* arm_BIC X25 X9 X22 *)
  w 0x93c5c4a5;         (* arm_ROR X5 X5 49 *)
  w 0xca160021;         (* arm_EOR X1 X1 X22 *)
  w 0xca0e0056;         (* arm_EOR X22 X2 X14 *)
  w 0xf9403fe2;         (* arm_LDR X2 SP (Immediate_Offset (word 120)) *)
  w 0xf90043e4;         (* arm_STR X4 SP (Immediate_Offset (word 128)) *)
  w 0x8a300164;         (* arm_BIC X4 X11 X16 *)
  w 0x8a2d01d2;         (* arm_BIC X18 X14 X13 *)
  w 0xca0f022f;         (* arm_EOR X15 X17 X15 *)
  w 0xca13008e;         (* arm_EOR X14 X4 X19 *)
  w 0x8a2b0151;         (* arm_BIC X17 X10 X11 *)
  w 0x8a250004;         (* arm_BIC X4 X0 X5 *)
  w 0xa90a13f1;         (* arm_STP X17 X4 SP (Immediate_Offset (iword
                           (&160))) *)
  w 0xca0d004d;         (* arm_EOR X13 X2 X13 *)
  w 0x93d5feb5;         (* arm_ROR X21 X21 63 *)
  w 0xf94053e2;         (* arm_LDR X2 SP (Immediate_Offset (word 160)) *)
  w 0x8a33021b;         (* arm_BIC X27 X16 X19 *)
  w 0xf9404be4;         (* arm_LDR X4 SP (Immediate_Offset (word 144)) *)
  w 0xca100050;         (* arm_EOR X16 X2 X16 *)
  w 0xf94057e2;         (* arm_LDR X2 SP (Immediate_Offset (word 168)) *)
  w 0x8a350267;         (* arm_BIC X7 X19 X21 *)
  w 0x93c89508;         (* arm_ROR X8 X8 37 *)
  w 0x93cc718c;         (* arm_ROR X12 X12 28 *)
  w 0xca090252;         (* arm_EOR X18 X18 X9 *)
  w 0x93c6d8c6;         (* arm_ROR X6 X6 54 *)
  w 0xca0a00e9;         (* arm_EOR X9 X7 X10 *)
  w 0xa90727ed;         (* arm_STP X13 X9 SP (Immediate_Offset (iword
                           (&112))) *)
  w 0x8a28018d;         (* arm_BIC X13 X12 X8 *)
  w 0xf9404fe7;         (* arm_LDR X7 SP (Immediate_Offset (word 152)) *)
  w 0x8a2600b1;         (* arm_BIC X17 X5 X6 *)
  w 0x8a2c00de;         (* arm_BIC X30 X6 X12 *)
  w 0xca170339;         (* arm_EOR X25 X25 X23 *)
  w 0xca060046;         (* arm_EOR X6 X2 X6 *)
  w 0xca150377;         (* arm_EOR X23 X27 X21 *)
  w 0xf9405be2;         (* arm_LDR X2 SP (Immediate_Offset (word 176)) *)
  w 0xca0001ad;         (* arm_EOR X13 X13 X0 *)
  w 0xf90047ef;         (* arm_STR X15 SP (Immediate_Offset (word 136)) *)
  w 0x8a2a02af;         (* arm_BIC X15 X21 X10 *)
  w 0x8a200115;         (* arm_BIC X21 X8 X0 *)
  w 0x93d8fb18;         (* arm_ROR X24 X24 62 *)
  w 0xf94033e0;         (* arm_LDR X0 SP (Immediate_Offset (word 96)) *)
  w 0x93c30863;         (* arm_ROR X3 X3 2 *)
  w 0xca0b01fb;         (* arm_EOR X27 X15 X11 *)
  w 0xaa0403eb;         (* arm_MOV X11 X4 *)
  w 0x8a24034a;         (* arm_BIC X10 X26 X4 *)
  w 0x8a3a00f3;         (* arm_BIC X19 X7 X26 *)
  w 0x8a27030f;         (* arm_BIC X15 X24 X7 *)
  w 0x8a380064;         (* arm_BIC X4 X3 X24 *)
  w 0x8a230169;         (* arm_BIC X9 X11 X3 *)
  w 0xca0803de;         (* arm_EOR X30 X30 X8 *)
  w 0xca0c0231;         (* arm_EOR X17 X17 X12 *)
  w 0xca0502a5;         (* arm_EOR X5 X21 X5 *)
  w 0xca1a01ef;         (* arm_EOR X15 X15 X26 *)
  w 0xca03014a;         (* arm_EOR X10 X10 X3 *)
  w 0xca0b0273;         (* arm_EOR X19 X19 X11 *)
  w 0xca070084;         (* arm_EOR X4 X4 X7 *)
  w 0xca180129;         (* arm_EOR X9 X9 X24 *)
  w 0xeb00005f;         (* arm_CMP X2 X0 *)
  w 0x54ffdac1;         (* arm_BNE (word 2095960) *)
  w 0xf9405fe0;         (* arm_LDR X0 SP (Immediate_Offset (word 184)) *)
  w 0xaa1903e7;         (* arm_MOV X7 X25 *)
  w 0xf94037e2;         (* arm_LDR X2 SP (Immediate_Offset (word 104)) *)
  w 0xa9028407;         (* arm_STP X7 X1 X0 (Immediate_Offset (iword (&40))) *)
  w 0xf9403be1;         (* arm_LDR X1 SP (Immediate_Offset (word 112)) *)
  w 0xa9005002;         (* arm_STP X2 X20 X0 (Immediate_Offset (iword (&0))) *)
  w 0xf94043fa;         (* arm_LDR X26 SP (Immediate_Offset (word 128)) *)
  w 0xf9002001;         (* arm_STR X1 X0 (Immediate_Offset (word 64)) *)
  w 0xf9403fe1;         (* arm_LDR X1 SP (Immediate_Offset (word 120)) *)
  w 0xa901f01a;         (* arm_STP X26 X28 X0 (Immediate_Offset (iword
                           (&24))) *)
  w 0xf94047e2;         (* arm_LDR X2 SP (Immediate_Offset (word 136)) *)
  w 0xf9000802;         (* arm_STR X2 X0 (Immediate_Offset (word 16)) *)
  w 0xf9001c12;         (* arm_STR X18 X0 (Immediate_Offset (word 56)) *)
  w 0xa904dc16;         (* arm_STP X22 X23 X0 (Immediate_Offset (iword
                           (&72))) *)
  w 0xa905c00e;         (* arm_STP X14 X16 X0 (Immediate_Offset (iword
                           (&88))) *)
  w 0xf900341b;         (* arm_STR X27 X0 (Immediate_Offset (word 104)) *)
  w 0xf9003801;         (* arm_STR X1 X0 (Immediate_Offset (word 112)) *)
  w 0xa907c41e;         (* arm_STP X30 X17 X0 (Immediate_Offset (iword
                           (&120))) *)
  w 0xa9089406;         (* arm_STP X6 X5 X0 (Immediate_Offset (iword
                           (&136))) *)
  w 0xa909a80d;         (* arm_STP X13 X10 X0 (Immediate_Offset (iword
                           (&152))) *)
  w 0xa90abc13;         (* arm_STP X19 X15 X0 (Immediate_Offset (iword
                           (&168))) *)
  w 0xa90ba404;         (* arm_STP X4 X9 X0 (Immediate_Offset (iword
                           (&184))) *)
  w 0xa9415bf5;         (* arm_LDP X21 X22 SP (Immediate_Offset (iword
                           (&16))) *)
  w 0xa94263f7;         (* arm_LDP X23 X24 SP (Immediate_Offset (iword
                           (&32))) *)
  w 0xa9436bf9;         (* arm_LDP X25 X26 SP (Immediate_Offset (iword
                           (&48))) *)
  w 0xa94473fb;         (* arm_LDP X27 X28 SP (Immediate_Offset (iword
                           (&64))) *)
  w 0xf9402bfe;         (* arm_LDR X30 SP (Immediate_Offset (word 80)) *)
  w 0xa8cc53f3;         (* arm_LDP X19 X20 SP (Postimmediate_Offset (iword
                           (&192))) *)
  w 0xd65f03c0          (* arm_RET X30 *)
]);;

let MLKEM_NATIVE_KECCAKF1600_PERMUTE_GCC12_O2_EXEC =
  ARM_MK_EXEC_RULE mlkem_native_keccakf1600_permute_gcc12_O2_mc;;

(* ------------------------------------------------------------------------- *)
(* Reading the round constants from the table.                               *)
(* ------------------------------------------------------------------------- *)

let READ_MEMORY_BYTES64_NUM_OF_WORDLIST = prove
 (`!a:int64 (l:int64 list) n j s:armstate.
        read (memory :> bytes(a,8 * n)) s = num_of_wordlist l /\
        LENGTH l = n /\ j < n
        ==> read (memory :> bytes64(word_add a (word(8 * j)))) s = EL j l`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC STRIP_ASSUME_TAC) THEN
  ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
  MP_TAC(ISPECL [`l:int64 list`; `j:num`] NUM_OF_WORDLIST_EL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  FIRST_X_ASSUM(fun th ->
    if is_eq(concl th) && is_comb(lhs(concl th)) &&
       can (term_match [] `read c s`) (lhs(concl th))
    then REWRITE_TAC[GSYM th] else failwith "") THEN
  REWRITE_TAC[BYTES64_WBYTES; READ_COMPONENT_COMPOSE; VAL_READ_WBYTES] THEN
  REWRITE_TAC[DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[ARITH_RULE `64 * j = 8 * (8 * j)`;
              ARITH_RULE `18446744073709551616 = 2 EXP (8 * 8)`;
              READ_BYTES_DIV; READ_BYTES_MOD] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN ASM_ARITH_TAC);;

let KECCAK_RC_DATA = prove
 (`num_of_bytelist mlkem_native_keccakf1600_permute_gcc12_O2_data =
   num_of_wordlist round_constants`,
  REWRITE_TAC[hd mlkem_native_keccakf1600_permute_gcc12_O2_data;
              round_constants] THEN
  REWRITE_TAC[num_of_bytelist; num_of_wordlist] THEN
  CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN
  REWRITE_TAC[DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV);;

let KECCAK_RC_BYTES = prove
 (`!rc s.
        bytes_loaded s (word rc) mlkem_native_keccakf1600_permute_gcc12_O2_data
        ==> read (memory :> bytes(word rc,192)) s =
            num_of_wordlist round_constants`,
  REWRITE_TAC[bytes_loaded; READ_BYTELIST_EQ_BYTES; KECCAK_RC_DATA;
              CONV_RULE(RAND_CONV LENGTH_CONV)
               (AP_TERM `LENGTH:byte list->num`
                  (hd mlkem_native_keccakf1600_permute_gcc12_O2_data))]);;

let LENGTH_ROUND_CONSTANTS = prove
 (`LENGTH round_constants = 24`,
  REWRITE_TAC[round_constants; LENGTH] THEN CONV_TAC NUM_REDUCE_CONV);;

(* ------------------------------------------------------------------------- *)
(* Tactics for the loop body, which does two rounds. As each lane of the     *)
(* first round is computed, it is replaced by a variable E_j abbreviating    *)
(* the corresponding lane in the specification, so that the second round     *)
(* and the final checks are about one round only. The lanes are recognized   *)
(* by evaluating both sides at random values, before proving the equations   *)
(* with KECCAK_BITBLAST_TAC.                                                 *)
(* ------------------------------------------------------------------------- *)

(*** Introduce ghost variables for the state reads in a list ***)

let GHOST_STATELIST_TAC =
  W(fun (asl,w) ->
        let regreads = dest_list(find_term is_list w) in
        let ghostvars = make_args "Ai_" [] (map type_of regreads) in
        EVERY(map2 GHOST_INTRO_TAC ghostvars (map rator regreads)));;

(*** Evaluation of 64-bit word expressions, with random values for atoms ***)

let eval64 =
  let atom_vals = Hashtbl.create 100 and memo = Hashtbl.create 10000 in
  let rand64 () =
    Int64.logor (Int64.shift_left (Int64.of_int (Random.bits ())) 34)
     (Int64.logor (Int64.shift_left (Int64.of_int (Random.bits ())) 4)
                  (Int64.of_int (Random.bits () land 15))) in
  let atom_val t =
    try Hashtbl.find atom_vals t with Not_found ->
      let v = rand64 () in Hashtbl.add atom_vals t v; v in
  let ror64 x n =
    if n = 0 then x else
    Int64.logor (Int64.shift_right_logical x n)
                (Int64.shift_left x (64 - n)) in
  let int64_of_num n =
    let v = ref 0L in
    String.iter (fun c -> v := Int64.add (Int64.mul !v 10L)
                                (Int64.of_int (Char.code c - 48)))
                (string_of_num n);
    !v in
  let rec eval t =
    try Hashtbl.find memo t with Not_found ->
    let v = match t with
      Comb(Comb(Const("word_xor",_),x),y) -> Int64.logxor (eval x) (eval y)
    | Comb(Comb(Const("word_and",_),x),y) -> Int64.logand (eval x) (eval y)
    | Comb(Comb(Const("word_or",_),x),y) -> Int64.logor (eval x) (eval y)
    | Comb(Const("word_not",_),x) -> Int64.lognot (eval x)
    | Comb(Comb(Const("word_ror",_),x),n) ->
        ror64 (eval x) (dest_small_numeral n)
    | Comb(Comb(Const("word_rol",_),x),n) ->
        ror64 (eval x) ((64 - dest_small_numeral n) mod 64)
    | Comb(Comb(Const("word_subword",_),
                Comb(Comb(Const("word_join",_),x),y)),p)
        when dest_small_numeral(rand p) = 64 ->
        let pos = dest_small_numeral(lhand p) in
        if pos = 0 then eval y else
        Int64.logor (Int64.shift_right_logical (eval y) pos)
                    (Int64.shift_left (eval x) (64 - pos))
    | Comb(Const("word",_),n) when is_numeral n ->
        int64_of_num(dest_numeral n)
    | _ -> atom_val t in
    Hashtbl.add memo t v; v in
  eval;;

(*** Expansion of one round of the specification as an explicit list ***)

let keccak_spec_round_conv =
  REWRITE_CONV[keccak_round] THENC TOP_DEPTH_CONV let_CONV THENC
  ONCE_DEPTH_CONV EL_CONV;;

(*** The abbreviations E_j for the lanes after the first round ***)

let KECCAK_INTRO_ABBREVS_TAC =
  W(fun (asl,w) ->
    let ais = map (fun j -> mk_var("Ai_"^string_of_int j,`:int64`)) (0--24) in
    let tm = mk_comb(mk_comb(`keccak_round`,`EL (2 * i) round_constants`),
                     mk_list(ais,`:int64`)) in
    let specs = dest_list(rhs(concl(keccak_spec_round_conv tm))) in
    let evs = map (fun j -> mk_var("E_"^string_of_int j,`:int64`)) (0--24) in
    MAP_EVERY (fun (e,t) -> ABBREV_TAC(mk_eq(e,t))) (zip evs specs));;

let keccak_abbrevs asl =
  mapfilter (fun (_,th) ->
    let c = concl th in
    let v = rhs c in
    if is_var v && String.length (fst(dest_var v)) > 2 &&
       String.sub (fst(dest_var v)) 0 2 = "E_"
    then (v,lhs c) else failwith "") asl;;

(*** After a step, replace any value that is a lane of the first round ***)

let KECCAK_ABBREV_STEP_TAC =
  let int64_ty = `:int64` in
  W(fun (asl,w) ->
    let s = rand w in
    let evals = map (fun (e,sp) -> (eval64 sp,(e,sp))) (keccak_abbrevs asl) in
    let cands = mapfilter (fun (_,th) ->
       let c = concl th in
       if is_eq c && is_comb(lhs c) && rand(lhs c) = s &&
          type_of(rhs c) = int64_ty && not(is_var(rhs c))
       then let (e,sp) = assoc (eval64(rhs c)) evals in (c,e,sp)
       else failwith "") asl in
    MAP_EVERY (fun (c,e,sp) ->
       let eqth = TRANS (prove(mk_eq(rhs c,sp),KECCAK_BITBLAST_TAC))
                        (ASSUME(mk_eq(sp,e))) in
       FIRST_X_ASSUM(fun th -> if concl th = c then ASSUME_TAC(TRANS th eqth)
                               else failwith "")) cands);;

(*** The final check of the lanes, now in terms of the E_j ***)

let KECCAK_SECOND_ROUND_TAC =
  CONV_TAC(RAND_CONV(REWRITE_CONV
   [ARITH_RULE `2 * (i + 1) = (2 * i + 1) + 1`; keccak])) THEN
  FIRST_ASSUM(fun th ->
    if is_eq(concl th) && is_list(lhs(concl th))
    then CONV_TAC(RAND_CONV(REWRITE_CONV[GSYM th]))
    else failwith "") THEN
  CONV_TAC(RAND_CONV(RAND_CONV keccak_spec_round_conv)) THEN
  W(fun (asl,w) ->
    REWRITE_TAC(map (fun (e,sp) -> ASSUME(mk_eq(sp,e)))
                    (keccak_abbrevs asl))) THEN
  CONV_TAC(RAND_CONV keccak_spec_round_conv) THEN
  REWRITE_TAC[CONS_11] THEN REPEAT CONJ_TAC THEN KECCAK_BITBLAST_TAC;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof, for the whole subroutine since the register saves are  *)
(* mixed up with the main code by the compiler, as in the proof of           *)
(* sha3_keccak_f1600_alt2.                                                   *)
(* ------------------------------------------------------------------------- *)

(*** The lanes in row-major order at the head and the end of the loop ***)

let keccak_lanes_str =
 "[read (memory :> bytes64(word_add stackpointer (word 104))) s;
   read X20 s;
   read (memory :> bytes64(word_add stackpointer (word 136))) s;
   read (memory :> bytes64(word_add stackpointer (word 128))) s;
   read X28 s; read X25 s; read X1 s; read X18 s;
   read (memory :> bytes64(word_add stackpointer (word 112))) s;
   read X22 s; read X23 s; read X14 s; read X16 s; read X27 s;
   read (memory :> bytes64(word_add stackpointer (word 120))) s;
   read X30 s; read X17 s; read X6 s; read X5 s; read X13 s;
   read X10 s; read X19 s; read X15 s; read X4 s; read X9 s]";;

let keccak_inv = parse_term ("\\i s.
  (read SP s = stackpointer /\\
   read (memory :> bytes64(word_add stackpointer (word 80))) s =
   returnaddress /\\
   read (memory :> bytes64 stackpointer) s = x19_init /\\
   read (memory :> bytes64(word_add stackpointer (word 8))) s = x20_init /\\
   read (memory :> bytes64(word_add stackpointer (word 16))) s = x21_init /\\
   read (memory :> bytes64(word_add stackpointer (word 24))) s = x22_init /\\
   read (memory :> bytes64(word_add stackpointer (word 32))) s = x23_init /\\
   read (memory :> bytes64(word_add stackpointer (word 40))) s = x24_init /\\
   read (memory :> bytes64(word_add stackpointer (word 48))) s = x25_init /\\
   read (memory :> bytes64(word_add stackpointer (word 56))) s = x26_init /\\
   read (memory :> bytes64(word_add stackpointer (word 64))) s = x27_init /\\
   read (memory :> bytes64(word_add stackpointer (word 72))) s = x28_init /\\
   read (memory :> bytes64(word_add stackpointer (word 96))) s =
   word_add (word rc) (word(16 * i)) /\\
   read (memory :> bytes64(word_add stackpointer (word 176))) s =
   word_add (word rc) (word 192) /\\
   read (memory :> bytes64(word_add stackpointer (word 184))) s = a /\\
   read (memory :> bytes(word rc,192)) s = num_of_wordlist round_constants /\\
   " ^ keccak_lanes_str ^ " = keccak (2 * i) A) /\\
  (read ZF s <=> i = 12)");;

let MLKEM_NATIVE_KECCAKF1600_PERMUTE_GCC12_O2_SUBROUTINE_CORRECT = prove
 (`!a rc A pc stackpointer returnaddress.
        adrp_within_bounds (word rc) (word(pc + 0x4)) /\
        aligned 16 stackpointer /\
        ALL (nonoverlapping (word_sub stackpointer (word 192),192))
            [(word pc,0x5d0); (a,200); (word rc,192)] /\
        nonoverlapping (a,200) (word pc,0x5d0)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    (mlkem_native_keccakf1600_permute_gcc12_O2_mc pc rc) /\
                  read PC s = word pc /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [a] s /\
                  bytes_loaded s (word rc)
                    mlkem_native_keccakf1600_permute_gcc12_O2_data /\
                  wordlist_from_memory(a,25) s = A)
             (\s. read PC s = returnaddress /\
                  wordlist_from_memory(a,25) s = keccak 24 A)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
              MAYCHANGE
               [memory :> bytes(a,200);
                memory :> bytes(word_sub stackpointer (word 192),192)])`,
  MAP_EVERY X_GEN_TAC
   [`a:int64`; `rc:num`; `A:int64 list`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 192 THEN X_GEN_TAC `stackpointer:int64` THEN
  STRIP_TAC THEN
  REWRITE_TAC[fst MLKEM_NATIVE_KECCAKF1600_PERMUTE_GCC12_O2_EXEC] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** The register saves, mixed in with the main code ***)

  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  ENSURES_PRESERVED_TAC "x19_init" `X19` THEN
  ENSURES_PRESERVED_TAC "x20_init" `X20` THEN
  ENSURES_PRESERVED_TAC "x21_init" `X21` THEN
  ENSURES_PRESERVED_TAC "x22_init" `X22` THEN
  ENSURES_PRESERVED_TAC "x23_init" `X23` THEN
  ENSURES_PRESERVED_TAC "x24_init" `X24` THEN
  ENSURES_PRESERVED_TAC "x25_init" `X25` THEN
  ENSURES_PRESERVED_TAC "x26_init" `X26` THEN
  ENSURES_PRESERVED_TAC "x27_init" `X27` THEN
  ENSURES_PRESERVED_TAC "x28_init" `X28` THEN

  (*** The loop, with the test at the end, doing two rounds each time ***)

  ENSURES_WHILE_PUP_TAC `12` `pc + 0xb0` `pc + 0x558` keccak_inv THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** Initial holding of the invariant ***)

    ENSURES_INIT_TAC "s0" THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP KECCAK_RC_BYTES) THEN
    BIGNUM_DIGITIZE_TAC "A_" `read (memory :> bytes (a,8 * 25)) s0` THEN
    FIRST_ASSUM(MP_TAC o CONV_RULE(LAND_CONV WORDLIST_FROM_MEMORY_CONV)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_KECCAKF1600_PERMUTE_GCC12_O2_EXEC (1--3) THEN
    FIRST_ASSUM(SUBST_ALL_TAC o MATCH_MP ADRP_ADD_FOLD) THEN
    ARM_STEPS_TAC MLKEM_NATIVE_KECCAKF1600_PERMUTE_GCC12_O2_EXEC (4--44) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[keccak; MULT_CLAUSES; WORD_ADD_0];

    (*** Preservation of the invariant, including the loop test ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    GHOST_STATELIST_TAC THEN ENSURES_INIT_TAC "s0" THEN
    MP_TAC(ISPECL [`word rc:int64`; `round_constants`; `24`; `2 * i + 1`;
                   `s0:armstate`] READ_MEMORY_BYTES64_NUM_OF_WORDLIST) THEN
    MP_TAC(ISPECL [`word rc:int64`; `round_constants`; `24`; `2 * i`;
                   `s0:armstate`] READ_MEMORY_BYTES64_NUM_OF_WORDLIST) THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
    ASM_REWRITE_TAC[LENGTH_ROUND_CONSTANTS] THEN
    ASM_SIMP_TAC[ARITH_RULE `i < 12 ==> 2 * i < 24 /\ 2 * i + 1 < 24`] THEN
    REWRITE_TAC[ARITH_RULE
     `8 * (2 * i) = 16 * i /\ 8 * (2 * i + 1) = 16 * i + 8`] THEN
    REPEAT DISCH_TAC THEN
    KECCAK_INTRO_ABBREVS_TAC THEN
    MAP_EVERY (fun n ->
      ARM_STEPS_TAC MLKEM_NATIVE_KECCAKF1600_PERMUTE_GCC12_O2_EXEC [n] THEN
      KECCAK_ABBREV_STEP_TAC) (1--298) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCARD_STATE_TAC "s298" THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
      AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
      KECCAK_SECOND_ROUND_TAC;
      REWRITE_TAC[WORD_RULE
       `word_sub (word_add a x) (word_add (word_add a y) z):int64 =
        word_sub x (word_add y z)`] THEN
      REWRITE_TAC[VAL_WORD_SUB_EQ_0; GSYM WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      ASM_SIMP_TAC[MOD_LT; ARITH_RULE
       `i < 12 ==> 16 * i + 16 < 18446744073709551616`] THEN
      ASM_ARITH_TAC];

    (*** The trivial loop-back goal ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    ARM_SIM_TAC MLKEM_NATIVE_KECCAKF1600_PERMUTE_GCC12_O2_EXEC [1];

    (*** The writeback tail ***)

    GHOST_STATELIST_TAC THEN
    ARM_SIM_TAC MLKEM_NATIVE_KECCAKF1600_PERMUTE_GCC12_O2_EXEC (1--30) THEN
    CONV_TAC(LAND_CONV WORDLIST_FROM_MEMORY_CONV) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV]);;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

(*** Unlike sha3_keccak_f1600, this has just one argument, and the table ***)
(*** of round constants is a read-only object.                          ***)

let mlkem_native_keccakf1600_permute_signature =
  ([("a", "uint64_t[static 25]", "false")],
   "void",
   [("a", "25", 8)],
   [("a", "25", 8)],
   []);;

let full_spec,public_vars = mk_safety_spec
    ~readonly_objects:[`word rc:int64`,`192`]
    ~keep_maychanges:true
    mlkem_native_keccakf1600_permute_signature
    MLKEM_NATIVE_KECCAKF1600_PERMUTE_GCC12_O2_SUBROUTINE_CORRECT
    MLKEM_NATIVE_KECCAKF1600_PERMUTE_GCC12_O2_EXEC;;

(*** The whole execution is simulated, as for sha3_keccak_f1600_alt2. The ***)
(*** address of the table is folded, and the loop test compares pointers ***)
(*** into the table, so their differences are simplified in the steps.   ***)
(*** The theorem keeps the frame, as needed for the proofs of callers.   ***)
(*** Since the code saves and restores callee-saved registers, they are  ***)
(*** first added to the frame as for the correctness proof, with their   ***)
(*** initial values as extra (public) variables, and the result, with    ***)
(*** those variables universally quantified, is proved by simulation.    ***)

let SAFETY_PRESERVED_TAC pretac vs tac (asl,w) =
  let f,bod = dest_exists w in
  let xs,ibod = strip_forall bod in
  let h,ens = dest_imp ibod in
  let _,gls,_ = pretac ([],ens) in
  let ens' = snd(hd gls) in
  let lth = prove(mk_exists(f,list_mk_forall(xs @ vs,mk_imp(h,ens'))),tac) in
  X_CHOOSE_THEN f (fun th ->
    EXISTS_TAC f THEN REPEAT GEN_TAC THEN DISCH_TAC THEN pretac THEN
    MATCH_MP_TAC(SPEC_ALL th) THEN FIRST_ASSUM ACCEPT_TAC) lth (asl,w);;

let KECCAK_PRESERVED_TAC =
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  ENSURES_PRESERVED_TAC "x19_init" `X19` THEN
  ENSURES_PRESERVED_TAC "x20_init" `X20` THEN
  ENSURES_PRESERVED_TAC "x21_init" `X21` THEN
  ENSURES_PRESERVED_TAC "x22_init" `X22` THEN
  ENSURES_PRESERVED_TAC "x23_init" `X23` THEN
  ENSURES_PRESERVED_TAC "x24_init" `X24` THEN
  ENSURES_PRESERVED_TAC "x25_init" `X25` THEN
  ENSURES_PRESERVED_TAC "x26_init" `X26` THEN
  ENSURES_PRESERVED_TAC "x27_init" `X27` THEN
  ENSURES_PRESERVED_TAC "x28_init" `X28`;;

let keccak_saved_regs =
  [`x19_init:int64`; `x20_init:int64`; `x21_init:int64`; `x22_init:int64`;
   `x23_init:int64`; `x24_init:int64`; `x25_init:int64`; `x26_init:int64`;
   `x27_init:int64`; `x28_init:int64`];;

let keccak_extra_word_CONV_backup = !extra_word_CONV;;

extra_word_CONV :=
  (GEN_REWRITE_CONV I [WORD_RULE
    `word_sub (word_add a x) (word_add a y):int64 = word_sub x y`] THENC
   WORD_REDUCE_CONV) :: !extra_word_CONV;;

let MLKEM_NATIVE_KECCAKF1600_PERMUTE_GCC12_O2_SUBROUTINE_SAFE = time prove
 (`exists f_events.
       forall e a rc pc stackpointer returnaddress.
           adrp_within_bounds (word rc) (word (pc + 4)) /\
           aligned 16 stackpointer /\
           ALL (nonoverlapping (word_sub stackpointer (word 192),192))
           [word pc,1488; a,200; word rc,192] /\
           nonoverlapping (a,200) (word pc,1488)
           ==> ensures arm
               (\s.
                    aligned_bytes_loaded s (word pc)
                    (mlkem_native_keccakf1600_permute_gcc12_O2_mc pc rc) /\
                    read PC s = word pc /\
                    bytes_loaded s (word rc)
                    mlkem_native_keccakf1600_permute_gcc12_O2_data /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [a] s /\
                    read events s = e)
               (\s.
                    read PC s = returnaddress /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 =
                         f_events a rc pc (word_sub stackpointer (word 192))
                         returnaddress /\
                         memaccess_inbounds e2
                         [a,200; word_sub stackpointer (word 192),192;
                          word rc,192]
                         [a,200; word_sub stackpointer (word 192),192]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [X18] ,,
                MAYCHANGE
                [memory :> bytes (a,200);
                 memory :> bytes (word_sub stackpointer (word 192),192)])`,
  ASSERT_CONCL_TAC full_spec THEN
  SAFETY_PRESERVED_TAC KECCAK_PRESERVED_TAC keccak_saved_regs
   (GEN_PROVE_SAFETY_SPEC_TAC ~public_vars:(public_vars @ keccak_saved_regs)
      ~tac_before_maychange_simp:
        (TRY(FIRST_ASSUM(SUBST_ALL_TAC o MATCH_MP ADRP_ADD_FOLD)))
      MLKEM_NATIVE_KECCAKF1600_PERMUTE_GCC12_O2_EXEC
      [ALIGNED_BYTES_LOADED_APPEND_CLAUSE; MODIFIABLE_SIMD_REGS;
       MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI]
      ARM_SINGLE_STEP_TAC));;

extra_word_CONV := keccak_extra_word_CONV_backup;;

(* ------------------------------------------------------------------------- *)
(* The same code in the whole image, at address 0x2dd0 with the table of     *)
(* round constants at 0x62b0 (see mlkem_native_libmlkem_gcc12_O2.ml).        *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/mlkem_native_libmlkem_gcc12_O2.ml";;

let MLKEM_NATIVE_KECCAKF1600_PERMUTE_GCC12_O2_IN_IMAGE =
  MLKEM_NATIVE_IMAGE_CODE_RULE mlkem_native_keccakf1600_permute_gcc12_O2_mc
    0x2dd0 [0x62b0];;

let MLKEM_NATIVE_KECCAKF1600_PERMUTE_GCC12_O2_DATA_IN_IMAGE =
  MLKEM_NATIVE_IMAGE_DATA_RULE
    (hd mlkem_native_keccakf1600_permute_gcc12_O2_data) 0x62b0;;

let MLKEM_NATIVE_KECCAKF1600_PERMUTE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (`!a A pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + 0x6480 <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        ALL (nonoverlapping (word_sub stackpointer (word 192),192))
            [(word pc,0x6480); (a,200)] /\
        nonoverlapping (a,200) (word pc,0x6480)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                  read PC s = word (pc + 0x2dd0) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [a] s /\
                  wordlist_from_memory(a,25) s = A)
             (\s. read PC s = returnaddress /\
                  wordlist_from_memory(a,25) s = keccak 24 A)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
              MAYCHANGE
               [memory :> bytes(a,200);
                memory :> bytes(word_sub stackpointer (word 192),192)])`,
  MLKEM_NATIVE_IMAGE_TAC
   (INST [`pc + 0x2dd0`,`pc:num`; `pc + 0x62b0`,`rc:num`]
     (SPEC_ALL MLKEM_NATIVE_KECCAKF1600_PERMUTE_GCC12_O2_SUBROUTINE_CORRECT))
   [MLKEM_NATIVE_KECCAKF1600_PERMUTE_GCC12_O2_IN_IMAGE;
    MLKEM_NATIVE_KECCAKF1600_PERMUTE_GCC12_O2_DATA_IN_IMAGE]);;

let MLKEM_NATIVE_KECCAKF1600_PERMUTE_GCC12_O2_IMAGE_SUBROUTINE_SAFE = prove
 (`exists f_events.
       forall e a pc stackpointer returnaddress.
           aligned 4096 (word pc:int64) /\ pc + 0x6480 <= 2 EXP 64 /\
           aligned 16 stackpointer /\
           ALL (nonoverlapping (word_sub stackpointer (word 192),192))
           [word pc,0x6480; a,200] /\
           nonoverlapping (a,200) (word pc,0x6480)
           ==> ensures arm
               (\s.
                    aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                    read PC s = word (pc + 0x2dd0) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [a] s /\
                    read events s = e)
               (\s.
                    read PC s = returnaddress /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 =
                         f_events a pc (word_sub stackpointer (word 192))
                         returnaddress /\
                         memaccess_inbounds e2
                         [a,200; word_sub stackpointer (word 192),192;
                          word (pc + 0x62b0),192]
                         [a,200; word_sub stackpointer (word 192),192]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [X18] ,,
                MAYCHANGE
                [memory :> bytes (a,200);
                 memory :> bytes (word_sub stackpointer (word 192),192)])`,
  MLKEM_NATIVE_IMAGE_SAFE_TAC
   MLKEM_NATIVE_KECCAKF1600_PERMUTE_GCC12_O2_SUBROUTINE_SAFE
   [`pc + 0x2dd0`,`pc:num`; `pc + 0x62b0`,`rc:num`]
   [MLKEM_NATIVE_KECCAKF1600_PERMUTE_GCC12_O2_IN_IMAGE;
    MLKEM_NATIVE_KECCAKF1600_PERMUTE_GCC12_O2_DATA_IN_IMAGE]);;

(* ------------------------------------------------------------------------- *)
(* The same for the state as a 1600-bit word, read by wbytes, with the       *)
(* permutation keccak_f1600 of common/fips202.ml (see                        *)
(* utils/keccak_fips202.ml), and tactics for callers, which carry the state  *)
(* between calls as 200 bytes.                                               *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/utils/keccak_fips202.ml";;

let MLKEM_NATIVE_KECCAKF1600_PERMUTE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_F1600 =
  prove
 (`!a (S:1600 word) pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + 0x6480 <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        ALL (nonoverlapping (word_sub stackpointer (word 192),192))
            [(word pc,0x6480); (a,200)] /\
        nonoverlapping (a,200) (word pc,0x6480)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                  read PC s = word (pc + 0x2dd0) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [a] s /\
                  read (memory :> wbytes a) s = S)
             (\s. read PC s = returnaddress /\
                  read (memory :> wbytes a) s = keccak_f1600 S)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
              MAYCHANGE
               [memory :> bytes(a,200);
                memory :> bytes(word_sub stackpointer (word 192),192)])`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`a:int64`; `wordlist_of_num 25 (val(S:1600 word)):int64 list`;
                `pc:num`; `stackpointer:int64`; `returnaddress:int64`]
    MLKEM_NATIVE_KECCAKF1600_PERMUTE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MATCH_MP_TAC o MATCH_MP (MESON[ENSURES_PREPOSTCONDITION_THM]
   `ensures step P Q C
    ==> (!x. P' x ==> P x) /\ (!x. Q x ==> Q' x)
        ==> ensures step P' Q' C`)) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[READ_MEMORY_WBYTES_KECCAK] THEN SIMP_TAC[];
    MESON_TAC[KECCAK_F1600_MEMORY]]);;

(*** The state at a as a 1600-bit word, from it as 200 bytes ***)

let KECCAK_STATE_AT_TAC a =
  FIRST_ASSUM(fun th ->
    match concl th with
      Comb(Comb(Const("=",_),
                Comb(Comb(Const("read",_),
                          Comb(Comb(Const(":>",_),Const("memory",_)),
                               Comb(Const("bytes",_),aa))),_)),
           Comb(Const("val",_),_))
        when aa = mk_pair(a,`200`) ->
          ASSUME_TAC(REWRITE_RULE[GSYM READ_MEMORY_WBYTES_1600] th)
    | _ -> NO_TAC);;

(*** Apply ttac to the 1600-bit word for the state at a ***)

let KECCAK_STATE_THEN a (ttac:term->tactic) =
  FIRST_ASSUM(fun th ->
    match concl th with
      Comb(Comb(Const("=",_),
                Comb(Comb(Const("read",_),
                          Comb(Comb(Const(":>",_),Const("memory",_)),
                               Comb(Const("wbytes",_),aa))),_)),v)
        when aa = a -> ttac v
    | _ -> NO_TAC);;
