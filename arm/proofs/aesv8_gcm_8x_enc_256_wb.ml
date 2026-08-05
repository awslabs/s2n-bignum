(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* AES-256-GCM encryption kernel (8x-unrolled), WHOLE-BLOCKS-ONLY variant.    *)
(*                                                                           *)
(* Correctness proof for the aws-lc-derived 8x-unrolled AES-256-GCM encrypt  *)
(* kernel aesv8_gcm_8x_enc_256_wb.  This is the whole-blocks-only variant:    *)
(* the input bit length must be a nonzero multiple of 128 (a runtime guard   *)
(* tst x1,#127; b.ne returns 0 otherwise), and the partial-final-block        *)
(* masking machinery is removed (final block is a plain full block).  The    *)
(* proof re-anchors the aesv8_gcm_8x_enc_256 scripts to the +8-shifted PCs.   *)
(* This file freezes the machine code (via define_assert_from_elf) and builds *)
(* the execution rule.                                                        *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

needs "common/fips197.ml";;

needs "common/polyval_ghash.ml";;
needs "common/ghash_nist_bridge.ml";;
needs "common/karatsuba_pmul.ml";;

(* ------------------------------------------------------------------------- *)
(* The machine code.                                                         *)
(* ------------------------------------------------------------------------- *)

(* print_literal_from_elf "arm/aes_gcm/aesv8_gcm_8x_enc_256_wb.o";; *)

let aesv8_gcm_8x_enc_256_wb_mc =
  define_assert_from_elf "aesv8_gcm_8x_enc_256_wb_mc"
                         "arm/aes_gcm/aesv8_gcm_8x_enc_256_wb.o"
[
  0xb4008e01;       (* arm_CBZ X1 (word 4544) *)
  0xf240183f;       (* arm_TST X1 (rvalue (word 127)) *)
  0x54008dc1;       (* arm_BNE (word 4536) *)
  0xd10143ff;       (* arm_SUB SP SP (rvalue (word 80)) *)
  0x6d0027e8;       (* arm_STP D8 D9 SP (Immediate_Offset (iword (&0))) *)
  0xd343fc29;       (* arm_LSR X9 X1 3 *)
  0xaa0403f0;       (* arm_MOV X16 X4 *)
  0xaa0503eb;       (* arm_MOV X11 X5 *)
  0x6d012fea;       (* arm_STP D10 D11 SP (Immediate_Offset (iword (&16))) *)
  0x6d0237ec;       (* arm_STP D12 D13 SP (Immediate_Offset (iword (&32))) *)
  0x6d033fee;       (* arm_STP D14 D15 SP (Immediate_Offset (iword (&48))) *)
  0xd2f84005;       (* arm_MOVZ X5 (word 49664) 48 *)
  0xa9047fe5;       (* arm_STP X5 XZR SP (Immediate_Offset (iword (&64))) *)
  0x910103ea;       (* arm_ADD X10 SP (rvalue (word 64)) *)
  0x4c407200;       (* arm_LDR Q0 X16 No_Offset *)
  0xaa0903e5;       (* arm_MOV X5 X9 *)
  0xd2c0002f;       (* arm_MOVZ X15 (word 1) 32 *)
  0x4f00e41f;       (* arm_MOVI Q31 (word 0) *)
  0x4e181dff;       (* arm_INS_GEN Q31 X15 64 64 *)
  0xd10004a5;       (* arm_SUB X5 X5 (rvalue (word 1)) *)
  0x9279e0a5;       (* arm_AND X5 X5 (rvalue (word 18446744073709551488)) *)
  0x8b0000a5;       (* arm_ADD X5 X5 X0 *)
  0x6e20081e;       (* arm_REV32_VEC Q30 Q0 8 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0x6e200bc1;       (* arm_REV32_VEC Q1 Q30 8 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0x6e200bc2;       (* arm_REV32_VEC Q2 Q30 8 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0x6e200bc3;       (* arm_REV32_VEC Q3 Q30 8 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0x6e200bc4;       (* arm_REV32_VEC Q4 Q30 8 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0x6e200bc5;       (* arm_REV32_VEC Q5 Q30 8 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0xad406d7a;       (* arm_LDP Q26 Q27 X11 (Immediate_Offset (iword (&0))) *)
  0x6e200bc6;       (* arm_REV32_VEC Q6 Q30 8 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0x6e200bc7;       (* arm_REV32_VEC Q7 Q30 8 *)
  0x4e284b43;       (* arm_AESE Q3 Q26 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b44;       (* arm_AESE Q4 Q26 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b42;       (* arm_AESE Q2 Q26 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b41;       (* arm_AESE Q1 Q26 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b46;       (* arm_AESE Q6 Q26 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b45;       (* arm_AESE Q5 Q26 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b47;       (* arm_AESE Q7 Q26 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0xad41697c;       (* arm_LDP Q28 Q26 X11 (Immediate_Offset (iword (&32))) *)
  0x4e284b64;       (* arm_AESE Q4 Q27 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b61;       (* arm_AESE Q1 Q27 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b63;       (* arm_AESE Q3 Q27 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b66;       (* arm_AESE Q6 Q27 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b65;       (* arm_AESE Q5 Q27 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b62;       (* arm_AESE Q2 Q27 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b67;       (* arm_AESE Q7 Q27 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b82;       (* arm_AESE Q2 Q28 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b83;       (* arm_AESE Q3 Q28 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b60;       (* arm_AESE Q0 Q27 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b87;       (* arm_AESE Q7 Q28 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b86;       (* arm_AESE Q6 Q28 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b85;       (* arm_AESE Q5 Q28 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b84;       (* arm_AESE Q4 Q28 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b80;       (* arm_AESE Q0 Q28 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b81;       (* arm_AESE Q1 Q28 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b45;       (* arm_AESE Q5 Q26 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b43;       (* arm_AESE Q3 Q26 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0xad42717b;       (* arm_LDP Q27 Q28 X11 (Immediate_Offset (iword (&64))) *)
  0x4e284b44;       (* arm_AESE Q4 Q26 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b41;       (* arm_AESE Q1 Q26 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b46;       (* arm_AESE Q6 Q26 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b47;       (* arm_AESE Q7 Q26 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b42;       (* arm_AESE Q2 Q26 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b64;       (* arm_AESE Q4 Q27 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b66;       (* arm_AESE Q6 Q27 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b61;       (* arm_AESE Q1 Q27 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b62;       (* arm_AESE Q2 Q27 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b60;       (* arm_AESE Q0 Q27 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b63;       (* arm_AESE Q3 Q27 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b67;       (* arm_AESE Q7 Q27 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b65;       (* arm_AESE Q5 Q27 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b80;       (* arm_AESE Q0 Q28 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b82;       (* arm_AESE Q2 Q28 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0xad436d7a;       (* arm_LDP Q26 Q27 X11 (Immediate_Offset (iword (&96))) *)
  0x4e284b81;       (* arm_AESE Q1 Q28 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b84;       (* arm_AESE Q4 Q28 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b85;       (* arm_AESE Q5 Q28 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b83;       (* arm_AESE Q3 Q28 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b86;       (* arm_AESE Q6 Q28 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b87;       (* arm_AESE Q7 Q28 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b41;       (* arm_AESE Q1 Q26 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b45;       (* arm_AESE Q5 Q26 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b44;       (* arm_AESE Q4 Q26 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b42;       (* arm_AESE Q2 Q26 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b46;       (* arm_AESE Q6 Q26 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b47;       (* arm_AESE Q7 Q26 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b43;       (* arm_AESE Q3 Q26 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0xad44697c;       (* arm_LDP Q28 Q26 X11 (Immediate_Offset (iword (&128))) *)
  0x4e284b62;       (* arm_AESE Q2 Q27 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b60;       (* arm_AESE Q0 Q27 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b67;       (* arm_AESE Q7 Q27 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b66;       (* arm_AESE Q6 Q27 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b61;       (* arm_AESE Q1 Q27 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b65;       (* arm_AESE Q5 Q27 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b63;       (* arm_AESE Q3 Q27 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b64;       (* arm_AESE Q4 Q27 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b86;       (* arm_AESE Q6 Q28 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b81;       (* arm_AESE Q1 Q28 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b83;       (* arm_AESE Q3 Q28 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b80;       (* arm_AESE Q0 Q28 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b87;       (* arm_AESE Q7 Q28 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b85;       (* arm_AESE Q5 Q28 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b84;       (* arm_AESE Q4 Q28 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b82;       (* arm_AESE Q2 Q28 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4c407073;       (* arm_LDR Q19 X3 No_Offset *)
  0x6e134273;       (* arm_EXT Q19 Q19 Q19 64 *)
  0x4e200a73;       (* arm_REV64_VEC Q19 Q19 8 *)
  0xad45717b;       (* arm_LDP Q27 Q28 X11 (Immediate_Offset (iword (&160))) *)
  0x4e284b46;       (* arm_AESE Q6 Q26 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b47;       (* arm_AESE Q7 Q26 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b43;       (* arm_AESE Q3 Q26 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b44;       (* arm_AESE Q4 Q26 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b45;       (* arm_AESE Q5 Q26 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b42;       (* arm_AESE Q2 Q26 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b41;       (* arm_AESE Q1 Q26 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b67;       (* arm_AESE Q7 Q27 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b64;       (* arm_AESE Q4 Q27 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b61;       (* arm_AESE Q1 Q27 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b65;       (* arm_AESE Q5 Q27 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b63;       (* arm_AESE Q3 Q27 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b62;       (* arm_AESE Q2 Q27 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b60;       (* arm_AESE Q0 Q27 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b66;       (* arm_AESE Q6 Q27 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b84;       (* arm_AESE Q4 Q28 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0xad466d7a;       (* arm_LDP Q26 Q27 X11 (Immediate_Offset (iword (&192))) *)
  0x4e284b85;       (* arm_AESE Q5 Q28 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b82;       (* arm_AESE Q2 Q28 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b86;       (* arm_AESE Q6 Q28 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b81;       (* arm_AESE Q1 Q28 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b80;       (* arm_AESE Q0 Q28 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b83;       (* arm_AESE Q3 Q28 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b87;       (* arm_AESE Q7 Q28 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0x3dc0397c;       (* arm_LDR Q28 X11 (Immediate_Offset (word 224)) *)
  0x4e284b44;       (* arm_AESE Q4 Q26 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b42;       (* arm_AESE Q2 Q26 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b41;       (* arm_AESE Q1 Q26 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b45;       (* arm_AESE Q5 Q26 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b43;       (* arm_AESE Q3 Q26 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b62;       (* arm_AESE Q2 Q27 *)
  0x4e284b61;       (* arm_AESE Q1 Q27 *)
  0x4e284b64;       (* arm_AESE Q4 Q27 *)
  0x4e284b46;       (* arm_AESE Q6 Q26 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b47;       (* arm_AESE Q7 Q26 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b60;       (* arm_AESE Q0 Q27 *)
  0x4e284b65;       (* arm_AESE Q5 Q27 *)
  0x4e284b66;       (* arm_AESE Q6 Q27 *)
  0x4e284b67;       (* arm_AESE Q7 Q27 *)
  0x4e284b63;       (* arm_AESE Q3 Q27 *)
  0x8b410c04;       (* arm_ADD X4 X0 (Shiftedreg X1 LSR 3) *)
  0xeb05001f;       (* arm_CMP X0 X5 *)
  0x540054aa;       (* arm_BGE (word 2708) *)
  0xacc12408;       (* arm_LDP Q8 Q9 X0 (Postimmediate_Offset (iword (&32))) *)
  0xacc12c0a;       (* arm_LDP Q10 Q11 X0 (Postimmediate_Offset (iword (&32))) *)
  0xce007108;       (* arm_EOR3 Q8 Q8 Q0 Q28 *)
  0x6e200bc0;       (* arm_REV32_VEC Q0 Q30 8 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0xce017129;       (* arm_EOR3 Q9 Q9 Q1 Q28 *)
  0xce03716b;       (* arm_EOR3 Q11 Q11 Q3 Q28 *)
  0x6e200bc1;       (* arm_REV32_VEC Q1 Q30 8 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0xacc1340c;       (* arm_LDP Q12 Q13 X0 (Postimmediate_Offset (iword (&32))) *)
  0xacc13c0e;       (* arm_LDP Q14 Q15 X0 (Postimmediate_Offset (iword (&32))) *)
  0xce02714a;       (* arm_EOR3 Q10 Q10 Q2 Q28 *)
  0xeb05001f;       (* arm_CMP X0 X5 *)
  0x6e200bc2;       (* arm_REV32_VEC Q2 Q30 8 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0xac812448;       (* arm_STP Q8 Q9 X2 (Postimmediate_Offset (iword (&32))) *)
  0xac812c4a;       (* arm_STP Q10 Q11 X2 (Postimmediate_Offset (iword (&32))) *)
  0x6e200bc3;       (* arm_REV32_VEC Q3 Q30 8 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0xce04718c;       (* arm_EOR3 Q12 Q12 Q4 Q28 *)
  0xce0771ef;       (* arm_EOR3 Q15 Q15 Q7 Q28 *)
  0xce0671ce;       (* arm_EOR3 Q14 Q14 Q6 Q28 *)
  0xce0571ad;       (* arm_EOR3 Q13 Q13 Q5 Q28 *)
  0xac81344c;       (* arm_STP Q12 Q13 X2 (Postimmediate_Offset (iword (&32))) *)
  0x6e200bc4;       (* arm_REV32_VEC Q4 Q30 8 *)
  0xac813c4e;       (* arm_STP Q14 Q15 X2 (Postimmediate_Offset (iword (&32))) *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0x54002aaa;       (* arm_BGE (word 1364) *)
  0xad406d7a;       (* arm_LDP Q26 Q27 X11 (Immediate_Offset (iword (&0))) *)
  0x6e200bc5;       (* arm_REV32_VEC Q5 Q30 8 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0x3dc01cd5;       (* arm_LDR Q21 X6 (Immediate_Offset (word 112)) *)
  0x3dc028d8;       (* arm_LDR Q24 X6 (Immediate_Offset (word 160)) *)
  0x4e20096b;       (* arm_REV64_VEC Q11 Q11 8 *)
  0x3dc018d4;       (* arm_LDR Q20 X6 (Immediate_Offset (word 96)) *)
  0x3dc020d6;       (* arm_LDR Q22 X6 (Immediate_Offset (word 128)) *)
  0x4e200929;       (* arm_REV64_VEC Q9 Q9 8 *)
  0x6e200bc6;       (* arm_REV32_VEC Q6 Q30 8 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0x4e200908;       (* arm_REV64_VEC Q8 Q8 8 *)
  0x4e20098c;       (* arm_REV64_VEC Q12 Q12 8 *)
  0x6e134273;       (* arm_EXT Q19 Q19 Q19 64 *)
  0x3dc024d7;       (* arm_LDR Q23 X6 (Immediate_Offset (word 144)) *)
  0x3dc02cd9;       (* arm_LDR Q25 X6 (Immediate_Offset (word 176)) *)
  0x4e284b43;       (* arm_AESE Q3 Q26 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b45;       (* arm_AESE Q5 Q26 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x6e200bc7;       (* arm_REV32_VEC Q7 Q30 8 *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b41;       (* arm_AESE Q1 Q26 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b46;       (* arm_AESE Q6 Q26 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b47;       (* arm_AESE Q7 Q26 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b42;       (* arm_AESE Q2 Q26 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b44;       (* arm_AESE Q4 Q26 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0xad41697c;       (* arm_LDP Q28 Q26 X11 (Immediate_Offset (iword (&32))) *)
  0x6e331d08;       (* arm_EOR_VEC Q8 Q8 Q19 128 *)
  0x4e284b66;       (* arm_AESE Q6 Q27 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b62;       (* arm_AESE Q2 Q27 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b61;       (* arm_AESE Q1 Q27 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b60;       (* arm_AESE Q0 Q27 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b64;       (* arm_AESE Q4 Q27 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b63;       (* arm_AESE Q3 Q27 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b65;       (* arm_AESE Q5 Q27 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4ef9e111;       (* arm_PMULL2_VEC Q17 Q8 Q25 64 *)
  0x0ef9e113;       (* arm_PMULL_VEC Q19 Q8 Q25 64 *)
  0x4ef7e130;       (* arm_PMULL2_VEC Q16 Q9 Q23 64 *)
  0x4ec82932;       (* arm_TRN1 Q18 Q9 Q8 64 128 *)
  0x4ec86928;       (* arm_TRN2 Q8 Q9 Q8 64 128 *)
  0x4e284b67;       (* arm_AESE Q7 Q27 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b81;       (* arm_AESE Q1 Q28 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b85;       (* arm_AESE Q5 Q28 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b86;       (* arm_AESE Q6 Q28 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b82;       (* arm_AESE Q2 Q28 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x0ef7e137;       (* arm_PMULL_VEC Q23 Q9 Q23 64 *)
  0x4e284b84;       (* arm_AESE Q4 Q28 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b45;       (* arm_AESE Q5 Q26 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b46;       (* arm_AESE Q6 Q26 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b80;       (* arm_AESE Q0 Q28 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b41;       (* arm_AESE Q1 Q26 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b87;       (* arm_AESE Q7 Q28 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b83;       (* arm_AESE Q3 Q28 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b44;       (* arm_AESE Q4 Q26 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e2009ce;       (* arm_REV64_VEC Q14 Q14 8 *)
  0x4ef4e169;       (* arm_PMULL2_VEC Q9 Q11 Q20 64 *)
  0x4e284b43;       (* arm_AESE Q3 Q26 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0xad42717b;       (* arm_LDP Q27 Q28 X11 (Immediate_Offset (iword (&64))) *)
  0x4e20094a;       (* arm_REV64_VEC Q10 Q10 8 *)
  0x4e284b42;       (* arm_AESE Q2 Q26 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b47;       (* arm_AESE Q7 Q26 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x6e301e31;       (* arm_EOR_VEC Q17 Q17 Q16 128 *)
  0x4ef6e15d;       (* arm_PMULL2_VEC Q29 Q10 Q22 64 *)
  0x4e2009ad;       (* arm_REV64_VEC Q13 Q13 8 *)
  0x0ef4e174;       (* arm_PMULL_VEC Q20 Q11 Q20 64 *)
  0x6e371e73;       (* arm_EOR_VEC Q19 Q19 Q23 128 *)
  0x3dc00cd7;       (* arm_LDR Q23 X6 (Immediate_Offset (word 48)) *)
  0x3dc014d9;       (* arm_LDR Q25 X6 (Immediate_Offset (word 80)) *)
  0x4ecc29b0;       (* arm_TRN1 Q16 Q13 Q12 64 128 *)
  0xce1d2631;       (* arm_EOR3 Q17 Q17 Q29 Q9 *)
  0x0ef6e156;       (* arm_PMULL_VEC Q22 Q10 Q22 64 *)
  0x4e284b64;       (* arm_AESE Q4 Q27 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b61;       (* arm_AESE Q1 Q27 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b65;       (* arm_AESE Q5 Q27 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b67;       (* arm_AESE Q7 Q27 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b63;       (* arm_AESE Q3 Q27 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b62;       (* arm_AESE Q2 Q27 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4eca297d;       (* arm_TRN1 Q29 Q11 Q10 64 128 *)
  0x4e284b66;       (* arm_AESE Q6 Q27 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b60;       (* arm_AESE Q0 Q27 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4eca696a;       (* arm_TRN2 Q10 Q11 Q10 64 128 *)
  0x6e321d08;       (* arm_EOR_VEC Q8 Q8 Q18 128 *)
  0xad436d7a;       (* arm_LDP Q26 Q27 X11 (Immediate_Offset (iword (&96))) *)
  0x4e284b85;       (* arm_AESE Q5 Q28 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b87;       (* arm_AESE Q7 Q28 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b84;       (* arm_AESE Q4 Q28 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x6e3d1d4a;       (* arm_EOR_VEC Q10 Q10 Q29 128 *)
  0x4e284b82;       (* arm_AESE Q2 Q28 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e2009ef;       (* arm_REV64_VEC Q15 Q15 8 *)
  0x4e284b83;       (* arm_AESE Q3 Q28 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b86;       (* arm_AESE Q6 Q28 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b81;       (* arm_AESE Q1 Q28 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4ef5e15d;       (* arm_PMULL2_VEC Q29 Q10 Q21 64 *)
  0x4ef8e112;       (* arm_PMULL2_VEC Q18 Q8 Q24 64 *)
  0x4e284b80;       (* arm_AESE Q0 Q28 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x0ef8e118;       (* arm_PMULL_VEC Q24 Q8 Q24 64 *)
  0x4e284b44;       (* arm_AESE Q4 Q26 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b42;       (* arm_AESE Q2 Q26 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b46;       (* arm_AESE Q6 Q26 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b41;       (* arm_AESE Q1 Q26 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b47;       (* arm_AESE Q7 Q26 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x6e381e52;       (* arm_EOR_VEC Q18 Q18 Q24 128 *)
  0x0ef5e155;       (* arm_PMULL_VEC Q21 Q10 Q21 64 *)
  0x4e284b45;       (* arm_AESE Q5 Q26 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0xce165273;       (* arm_EOR3 Q19 Q19 Q22 Q20 *)
  0x4e284b43;       (* arm_AESE Q3 Q26 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0xad44697c;       (* arm_LDP Q28 Q26 X11 (Immediate_Offset (iword (&128))) *)
  0x4ef9e188;       (* arm_PMULL2_VEC Q8 Q12 Q25 64 *)
  0x4e284b65;       (* arm_AESE Q5 Q27 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x3dc000d4;       (* arm_LDR Q20 X6 (Immediate_Offset (word 0)) *)
  0x3dc008d6;       (* arm_LDR Q22 X6 (Immediate_Offset (word 32)) *)
  0x4e284b62;       (* arm_AESE Q2 Q27 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0xce157652;       (* arm_EOR3 Q18 Q18 Q21 Q29 *)
  0x3dc004d5;       (* arm_LDR Q21 X6 (Immediate_Offset (word 16)) *)
  0x3dc010d8;       (* arm_LDR Q24 X6 (Immediate_Offset (word 64)) *)
  0x4e284b66;       (* arm_AESE Q6 Q27 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b63;       (* arm_AESE Q3 Q27 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b60;       (* arm_AESE Q0 Q27 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b67;       (* arm_AESE Q7 Q27 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x0ef9e199;       (* arm_PMULL_VEC Q25 Q12 Q25 64 *)
  0x4ecc69ac;       (* arm_TRN2 Q12 Q13 Q12 64 128 *)
  0x4e284b64;       (* arm_AESE Q4 Q27 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b61;       (* arm_AESE Q1 Q27 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4ef7e1aa;       (* arm_PMULL2_VEC Q10 Q13 Q23 64 *)
  0x4e284b87;       (* arm_AESE Q7 Q28 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b80;       (* arm_AESE Q0 Q28 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x0ef7e1b7;       (* arm_PMULL_VEC Q23 Q13 Q23 64 *)
  0x4ece29ed;       (* arm_TRN1 Q13 Q15 Q14 64 128 *)
  0x6e301d8c;       (* arm_EOR_VEC Q12 Q12 Q16 128 *)
  0x4e284b83;       (* arm_AESE Q3 Q28 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b81;       (* arm_AESE Q1 Q28 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4ef8e190;       (* arm_PMULL2_VEC Q16 Q12 Q24 64 *)
  0x0ef8e198;       (* arm_PMULL_VEC Q24 Q12 Q24 64 *)
  0x4e284b82;       (* arm_AESE Q2 Q28 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b85;       (* arm_AESE Q5 Q28 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4ef6e1cb;       (* arm_PMULL2_VEC Q11 Q14 Q22 64 *)
  0x0ef6e1d6;       (* arm_PMULL_VEC Q22 Q14 Q22 64 *)
  0x4e284b86;       (* arm_AESE Q6 Q28 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4ece69ee;       (* arm_TRN2 Q14 Q15 Q14 64 128 *)
  0x4e284b84;       (* arm_AESE Q4 Q28 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0xce184252;       (* arm_EOR3 Q18 Q18 Q24 Q16 *)
  0x4e284b47;       (* arm_AESE Q7 Q26 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b45;       (* arm_AESE Q5 Q26 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x6e2d1dce;       (* arm_EOR_VEC Q14 Q14 Q13 128 *)
  0x4e284b46;       (* arm_AESE Q6 Q26 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b44;       (* arm_AESE Q4 Q26 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0xad45717b;       (* arm_LDP Q27 Q28 X11 (Immediate_Offset (iword (&160))) *)
  0x4e284b42;       (* arm_AESE Q2 Q26 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b43;       (* arm_AESE Q3 Q26 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4ef4e1ec;       (* arm_PMULL2_VEC Q12 Q15 Q20 64 *)
  0xce195e73;       (* arm_EOR3 Q19 Q19 Q25 Q23 *)
  0x0ef4e1f4;       (* arm_PMULL_VEC Q20 Q15 Q20 64 *)
  0xfd400150;       (* arm_LDR D16 X10 (Immediate_Offset (word 0)) *)
  0x4ef5e1cd;       (* arm_PMULL2_VEC Q13 Q14 Q21 64 *)
  0x0ef5e1d5;       (* arm_PMULL_VEC Q21 Q14 Q21 64 *)
  0x4e284b41;       (* arm_AESE Q1 Q26 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0xce153652;       (* arm_EOR3 Q18 Q18 Q21 Q13 *)
  0xce165273;       (* arm_EOR3 Q19 Q19 Q22 Q20 *)
  0xce082a31;       (* arm_EOR3 Q17 Q17 Q8 Q10 *)
  0x4e284b64;       (* arm_AESE Q4 Q27 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b63;       (* arm_AESE Q3 Q27 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b65;       (* arm_AESE Q5 Q27 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b60;       (* arm_AESE Q0 Q27 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b62;       (* arm_AESE Q2 Q27 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0x4e284b61;       (* arm_AESE Q1 Q27 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b67;       (* arm_AESE Q7 Q27 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b66;       (* arm_AESE Q6 Q27 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0xce0b3231;       (* arm_EOR3 Q17 Q17 Q11 Q12 *)
  0xad466d7a;       (* arm_LDP Q26 Q27 X11 (Immediate_Offset (iword (&192))) *)
  0x6e200bd4;       (* arm_REV32_VEC Q20 Q30 8 *)
  0x6e114235;       (* arm_EXT Q21 Q17 Q17 64 *)
  0xacc12408;       (* arm_LDP Q8 Q9 X0 (Postimmediate_Offset (iword (&32))) *)
  0x4e284b82;       (* arm_AESE Q2 Q28 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b86;       (* arm_AESE Q6 Q28 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0x4e284b83;       (* arm_AESE Q3 Q28 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b80;       (* arm_AESE Q0 Q28 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b87;       (* arm_AESE Q7 Q28 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x0ef0e23d;       (* arm_PMULL_VEC Q29 Q17 Q16 64 *)
  0x4e284b81;       (* arm_AESE Q1 Q28 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b47;       (* arm_AESE Q7 Q26 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b85;       (* arm_AESE Q5 Q28 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b43;       (* arm_AESE Q3 Q26 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b46;       (* arm_AESE Q6 Q26 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x6e200bd6;       (* arm_REV32_VEC Q22 Q30 8 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0x4e284b84;       (* arm_AESE Q4 Q28 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0xce114e52;       (* arm_EOR3 Q18 Q18 Q17 Q19 *)
  0x4e284b45;       (* arm_AESE Q5 Q26 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x3dc0397c;       (* arm_LDR Q28 X11 (Immediate_Offset (word 224)) *)
  0x4e284b67;       (* arm_AESE Q7 Q27 *)
  0xacc12c0a;       (* arm_LDP Q10 Q11 X0 (Postimmediate_Offset (iword (&32))) *)
  0x4e284b42;       (* arm_AESE Q2 Q26 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b44;       (* arm_AESE Q4 Q26 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0xce1d5652;       (* arm_EOR3 Q18 Q18 Q29 Q21 *)
  0x4e284b41;       (* arm_AESE Q1 Q26 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0xacc1340c;       (* arm_LDP Q12 Q13 X0 (Postimmediate_Offset (iword (&32))) *)
  0xacc13c0e;       (* arm_LDP Q14 Q15 X0 (Postimmediate_Offset (iword (&32))) *)
  0x4e284b62;       (* arm_AESE Q2 Q27 *)
  0x4e284b64;       (* arm_AESE Q4 Q27 *)
  0x6e200bd7;       (* arm_REV32_VEC Q23 Q30 8 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0x4e284b65;       (* arm_AESE Q5 Q27 *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b63;       (* arm_AESE Q3 Q27 *)
  0xeb05001f;       (* arm_CMP X0 X5 *)
  0xce02714a;       (* arm_EOR3 Q10 Q10 Q2 Q28 *)
  0x6e200bd9;       (* arm_REV32_VEC Q25 Q30 8 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0x4e284b60;       (* arm_AESE Q0 Q27 *)
  0x4e284b66;       (* arm_AESE Q6 Q27 *)
  0xce0571ad;       (* arm_EOR3 Q13 Q13 Q5 Q28 *)
  0x6e124255;       (* arm_EXT Q21 Q18 Q18 64 *)
  0x0ef0e251;       (* arm_PMULL_VEC Q17 Q18 Q16 64 *)
  0x4e284b61;       (* arm_AESE Q1 Q27 *)
  0xce04718c;       (* arm_EOR3 Q12 Q12 Q4 Q28 *)
  0x6e200bc4;       (* arm_REV32_VEC Q4 Q30 8 *)
  0xce03716b;       (* arm_EOR3 Q11 Q11 Q3 Q28 *)
  0x4eb91f23;       (* arm_MOV_VEC Q3 Q25 128 *)
  0xce017129;       (* arm_EOR3 Q9 Q9 Q1 Q28 *)
  0xce007108;       (* arm_EOR3 Q8 Q8 Q0 Q28 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0xac812448;       (* arm_STP Q8 Q9 X2 (Postimmediate_Offset (iword (&32))) *)
  0x4eb71ee2;       (* arm_MOV_VEC Q2 Q23 128 *)
  0xce0771ef;       (* arm_EOR3 Q15 Q15 Q7 Q28 *)
  0xce154673;       (* arm_EOR3 Q19 Q19 Q21 Q17 *)
  0xac812c4a;       (* arm_STP Q10 Q11 X2 (Postimmediate_Offset (iword (&32))) *)
  0xce0671ce;       (* arm_EOR3 Q14 Q14 Q6 Q28 *)
  0x4eb61ec1;       (* arm_MOV_VEC Q1 Q22 128 *)
  0xac81344c;       (* arm_STP Q12 Q13 X2 (Postimmediate_Offset (iword (&32))) *)
  0xac813c4e;       (* arm_STP Q14 Q15 X2 (Postimmediate_Offset (iword (&32))) *)
  0x4eb41e80;       (* arm_MOV_VEC Q0 Q20 128 *)
  0x54ffd5ab;       (* arm_BLT (word 2095796) *)
  0x6e200bc5;       (* arm_REV32_VEC Q5 Q30 8 *)
  0xad406d7a;       (* arm_LDP Q26 Q27 X11 (Immediate_Offset (iword (&0))) *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0x4e20094a;       (* arm_REV64_VEC Q10 Q10 8 *)
  0x6e200bc6;       (* arm_REV32_VEC Q6 Q30 8 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0x4e2009ad;       (* arm_REV64_VEC Q13 Q13 8 *)
  0x3dc01cd5;       (* arm_LDR Q21 X6 (Immediate_Offset (word 112)) *)
  0x3dc028d8;       (* arm_LDR Q24 X6 (Immediate_Offset (word 160)) *)
  0x6e200bc7;       (* arm_REV32_VEC Q7 Q30 8 *)
  0x4e284b46;       (* arm_AESE Q6 Q26 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b44;       (* arm_AESE Q4 Q26 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b41;       (* arm_AESE Q1 Q26 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b45;       (* arm_AESE Q5 Q26 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b42;       (* arm_AESE Q2 Q26 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b47;       (* arm_AESE Q7 Q26 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b43;       (* arm_AESE Q3 Q26 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x6e134273;       (* arm_EXT Q19 Q19 Q19 64 *)
  0x4e200908;       (* arm_REV64_VEC Q8 Q8 8 *)
  0x4e284b61;       (* arm_AESE Q1 Q27 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e200929;       (* arm_REV64_VEC Q9 Q9 8 *)
  0xad41697c;       (* arm_LDP Q28 Q26 X11 (Immediate_Offset (iword (&32))) *)
  0x4e284b63;       (* arm_AESE Q3 Q27 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x3dc024d7;       (* arm_LDR Q23 X6 (Immediate_Offset (word 144)) *)
  0x3dc02cd9;       (* arm_LDR Q25 X6 (Immediate_Offset (word 176)) *)
  0x4e284b62;       (* arm_AESE Q2 Q27 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x3dc018d4;       (* arm_LDR Q20 X6 (Immediate_Offset (word 96)) *)
  0x3dc020d6;       (* arm_LDR Q22 X6 (Immediate_Offset (word 128)) *)
  0x4e284b60;       (* arm_AESE Q0 Q27 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b65;       (* arm_AESE Q5 Q27 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b64;       (* arm_AESE Q4 Q27 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x6e331d08;       (* arm_EOR_VEC Q8 Q8 Q19 128 *)
  0x4e20096b;       (* arm_REV64_VEC Q11 Q11 8 *)
  0x4e284b66;       (* arm_AESE Q6 Q27 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b81;       (* arm_AESE Q1 Q28 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b82;       (* arm_AESE Q2 Q28 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b67;       (* arm_AESE Q7 Q27 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b84;       (* arm_AESE Q4 Q28 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b80;       (* arm_AESE Q0 Q28 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b86;       (* arm_AESE Q6 Q28 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b85;       (* arm_AESE Q5 Q28 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b87;       (* arm_AESE Q7 Q28 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b83;       (* arm_AESE Q3 Q28 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0xad42717b;       (* arm_LDP Q27 Q28 X11 (Immediate_Offset (iword (&64))) *)
  0x4ec82932;       (* arm_TRN1 Q18 Q9 Q8 64 128 *)
  0x4ef9e111;       (* arm_PMULL2_VEC Q17 Q8 Q25 64 *)
  0x4e2009ce;       (* arm_REV64_VEC Q14 Q14 8 *)
  0x4e284b44;       (* arm_AESE Q4 Q26 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4ef7e130;       (* arm_PMULL2_VEC Q16 Q9 Q23 64 *)
  0x4e284b47;       (* arm_AESE Q7 Q26 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x0ef9e113;       (* arm_PMULL_VEC Q19 Q8 Q25 64 *)
  0x4ec86928;       (* arm_TRN2 Q8 Q9 Q8 64 128 *)
  0x4ef6e15d;       (* arm_PMULL2_VEC Q29 Q10 Q22 64 *)
  0x4e284b46;       (* arm_AESE Q6 Q26 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b42;       (* arm_AESE Q2 Q26 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b43;       (* arm_AESE Q3 Q26 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x6e301e31;       (* arm_EOR_VEC Q17 Q17 Q16 128 *)
  0x0ef7e137;       (* arm_PMULL_VEC Q23 Q9 Q23 64 *)
  0x4ef4e169;       (* arm_PMULL2_VEC Q9 Q11 Q20 64 *)
  0x4e284b41;       (* arm_AESE Q1 Q26 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x6e321d08;       (* arm_EOR_VEC Q8 Q8 Q18 128 *)
  0x4e284b45;       (* arm_AESE Q5 Q26 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x0ef6e156;       (* arm_PMULL_VEC Q22 Q10 Q22 64 *)
  0x4e284b61;       (* arm_AESE Q1 Q27 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b66;       (* arm_AESE Q6 Q27 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b60;       (* arm_AESE Q0 Q27 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b62;       (* arm_AESE Q2 Q27 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b64;       (* arm_AESE Q4 Q27 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b86;       (* arm_AESE Q6 Q28 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4ef8e112;       (* arm_PMULL2_VEC Q18 Q8 Q24 64 *)
  0xce1d2631;       (* arm_EOR3 Q17 Q17 Q29 Q9 *)
  0x4e284b67;       (* arm_AESE Q7 Q27 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4eca297d;       (* arm_TRN1 Q29 Q11 Q10 64 128 *)
  0x4eca696a;       (* arm_TRN2 Q10 Q11 Q10 64 128 *)
  0x4e284b65;       (* arm_AESE Q5 Q27 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x6e371e73;       (* arm_EOR_VEC Q19 Q19 Q23 128 *)
  0x4e284b63;       (* arm_AESE Q3 Q27 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x0ef4e174;       (* arm_PMULL_VEC Q20 Q11 Q20 64 *)
  0x0ef8e118;       (* arm_PMULL_VEC Q24 Q8 Q24 64 *)
  0x6e3d1d4a;       (* arm_EOR_VEC Q10 Q10 Q29 128 *)
  0x4e20098c;       (* arm_REV64_VEC Q12 Q12 8 *)
  0x4e284b81;       (* arm_AESE Q1 Q28 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b80;       (* arm_AESE Q0 Q28 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b87;       (* arm_AESE Q7 Q28 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b84;       (* arm_AESE Q4 Q28 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0xad436d7a;       (* arm_LDP Q26 Q27 X11 (Immediate_Offset (iword (&96))) *)
  0x3dc00cd7;       (* arm_LDR Q23 X6 (Immediate_Offset (word 48)) *)
  0x3dc014d9;       (* arm_LDR Q25 X6 (Immediate_Offset (word 80)) *)
  0x4ef5e15d;       (* arm_PMULL2_VEC Q29 Q10 Q21 64 *)
  0x0ef5e155;       (* arm_PMULL_VEC Q21 Q10 Q21 64 *)
  0xce165273;       (* arm_EOR3 Q19 Q19 Q22 Q20 *)
  0x6e381e52;       (* arm_EOR_VEC Q18 Q18 Q24 128 *)
  0x4e284b85;       (* arm_AESE Q5 Q28 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e2009ef;       (* arm_REV64_VEC Q15 Q15 8 *)
  0x4ecc29b0;       (* arm_TRN1 Q16 Q13 Q12 64 128 *)
  0x4e284b83;       (* arm_AESE Q3 Q28 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b82;       (* arm_AESE Q2 Q28 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0xce157652;       (* arm_EOR3 Q18 Q18 Q21 Q29 *)
  0x4e284b47;       (* arm_AESE Q7 Q26 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b44;       (* arm_AESE Q4 Q26 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b46;       (* arm_AESE Q6 Q26 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x3dc004d5;       (* arm_LDR Q21 X6 (Immediate_Offset (word 16)) *)
  0x3dc010d8;       (* arm_LDR Q24 X6 (Immediate_Offset (word 64)) *)
  0x4e284b45;       (* arm_AESE Q5 Q26 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b43;       (* arm_AESE Q3 Q26 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b41;       (* arm_AESE Q1 Q26 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b42;       (* arm_AESE Q2 Q26 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4ef9e188;       (* arm_PMULL2_VEC Q8 Q12 Q25 64 *)
  0x0ef9e199;       (* arm_PMULL_VEC Q25 Q12 Q25 64 *)
  0x3dc000d4;       (* arm_LDR Q20 X6 (Immediate_Offset (word 0)) *)
  0x3dc008d6;       (* arm_LDR Q22 X6 (Immediate_Offset (word 32)) *)
  0xad44697c;       (* arm_LDP Q28 Q26 X11 (Immediate_Offset (iword (&128))) *)
  0x4e284b61;       (* arm_AESE Q1 Q27 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b64;       (* arm_AESE Q4 Q27 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4ef7e1aa;       (* arm_PMULL2_VEC Q10 Q13 Q23 64 *)
  0x4ecc69ac;       (* arm_TRN2 Q12 Q13 Q12 64 128 *)
  0x4e284b65;       (* arm_AESE Q5 Q27 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b66;       (* arm_AESE Q6 Q27 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x0ef7e1b7;       (* arm_PMULL_VEC Q23 Q13 Q23 64 *)
  0x4e284b67;       (* arm_AESE Q7 Q27 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b63;       (* arm_AESE Q3 Q27 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x6e301d8c;       (* arm_EOR_VEC Q12 Q12 Q16 128 *)
  0x4ef6e1cb;       (* arm_PMULL2_VEC Q11 Q14 Q22 64 *)
  0x0ef6e1d6;       (* arm_PMULL_VEC Q22 Q14 Q22 64 *)
  0x4e284b62;       (* arm_AESE Q2 Q27 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4ece29ed;       (* arm_TRN1 Q13 Q15 Q14 64 128 *)
  0x4ece69ee;       (* arm_TRN2 Q14 Q15 Q14 64 128 *)
  0x4e284b60;       (* arm_AESE Q0 Q27 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b87;       (* arm_AESE Q7 Q28 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0xce195e73;       (* arm_EOR3 Q19 Q19 Q25 Q23 *)
  0x4e284b82;       (* arm_AESE Q2 Q28 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b86;       (* arm_AESE Q6 Q28 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b84;       (* arm_AESE Q4 Q28 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b83;       (* arm_AESE Q3 Q28 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b85;       (* arm_AESE Q5 Q28 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x6e2d1dce;       (* arm_EOR_VEC Q14 Q14 Q13 128 *)
  0x4e284b80;       (* arm_AESE Q0 Q28 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4ef8e190;       (* arm_PMULL2_VEC Q16 Q12 Q24 64 *)
  0x0ef8e198;       (* arm_PMULL_VEC Q24 Q12 Q24 64 *)
  0x4e284b81;       (* arm_AESE Q1 Q28 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4ef4e1ec;       (* arm_PMULL2_VEC Q12 Q15 Q20 64 *)
  0x4ef5e1cd;       (* arm_PMULL2_VEC Q13 Q14 Q21 64 *)
  0x0ef5e1d5;       (* arm_PMULL_VEC Q21 Q14 Q21 64 *)
  0x0ef4e1f4;       (* arm_PMULL_VEC Q20 Q15 Q20 64 *)
  0xce184252;       (* arm_EOR3 Q18 Q18 Q24 Q16 *)
  0xce082a31;       (* arm_EOR3 Q17 Q17 Q8 Q10 *)
  0xad45717b;       (* arm_LDP Q27 Q28 X11 (Immediate_Offset (iword (&160))) *)
  0x4e284b41;       (* arm_AESE Q1 Q26 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0xce0b3231;       (* arm_EOR3 Q17 Q17 Q11 Q12 *)
  0xce153652;       (* arm_EOR3 Q18 Q18 Q21 Q13 *)
  0xfd400150;       (* arm_LDR D16 X10 (Immediate_Offset (word 0)) *)
  0xce165273;       (* arm_EOR3 Q19 Q19 Q22 Q20 *)
  0x4e284b43;       (* arm_AESE Q3 Q26 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b47;       (* arm_AESE Q7 Q26 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b45;       (* arm_AESE Q5 Q26 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b42;       (* arm_AESE Q2 Q26 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b46;       (* arm_AESE Q6 Q26 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b65;       (* arm_AESE Q5 Q27 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b61;       (* arm_AESE Q1 Q27 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b44;       (* arm_AESE Q4 Q26 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b67;       (* arm_AESE Q7 Q27 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b66;       (* arm_AESE Q6 Q27 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b63;       (* arm_AESE Q3 Q27 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b64;       (* arm_AESE Q4 Q27 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b60;       (* arm_AESE Q0 Q27 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b62;       (* arm_AESE Q2 Q27 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x0ef0e23d;       (* arm_PMULL_VEC Q29 Q17 Q16 64 *)
  0xce114e52;       (* arm_EOR3 Q18 Q18 Q17 Q19 *)
  0x4e284b87;       (* arm_AESE Q7 Q28 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0xad466d7a;       (* arm_LDP Q26 Q27 X11 (Immediate_Offset (iword (&192))) *)
  0x6e114235;       (* arm_EXT Q21 Q17 Q17 64 *)
  0x4e284b82;       (* arm_AESE Q2 Q28 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0xce1d5652;       (* arm_EOR3 Q18 Q18 Q29 Q21 *)
  0x4e284b81;       (* arm_AESE Q1 Q28 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b86;       (* arm_AESE Q6 Q28 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b80;       (* arm_AESE Q0 Q28 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b84;       (* arm_AESE Q4 Q28 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b85;       (* arm_AESE Q5 Q28 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x0ef0e251;       (* arm_PMULL_VEC Q17 Q18 Q16 64 *)
  0x4e284b83;       (* arm_AESE Q3 Q28 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x3dc0397c;       (* arm_LDR Q28 X11 (Immediate_Offset (word 224)) *)
  0x4e284b41;       (* arm_AESE Q1 Q26 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b42;       (* arm_AESE Q2 Q26 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b46;       (* arm_AESE Q6 Q26 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b45;       (* arm_AESE Q5 Q26 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x6e124255;       (* arm_EXT Q21 Q18 Q18 64 *)
  0x4e284b44;       (* arm_AESE Q4 Q26 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0x4e284b43;       (* arm_AESE Q3 Q26 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b47;       (* arm_AESE Q7 Q26 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b60;       (* arm_AESE Q0 Q27 *)
  0xce154673;       (* arm_EOR3 Q19 Q19 Q21 Q17 *)
  0x4e284b65;       (* arm_AESE Q5 Q27 *)
  0x4e284b61;       (* arm_AESE Q1 Q27 *)
  0x4e284b63;       (* arm_AESE Q3 Q27 *)
  0x4e284b64;       (* arm_AESE Q4 Q27 *)
  0x4e284b67;       (* arm_AESE Q7 Q27 *)
  0x4e284b62;       (* arm_AESE Q2 Q27 *)
  0x4e284b66;       (* arm_AESE Q6 Q27 *)
  0xad4564d8;       (* arm_LDP Q24 Q25 X6 (Immediate_Offset (iword (&160))) *)
  0xcb000085;       (* arm_SUB X5 X4 X0 *)
  0x3cc10408;       (* arm_LDR Q8 X0 (Postimmediate_Offset (word 16)) *)
  0xad4354d4;       (* arm_LDP Q20 Q21 X6 (Immediate_Offset (iword (&96))) *)
  0x6e134270;       (* arm_EXT Q16 Q19 Q19 64 *)
  0xad445cd6;       (* arm_LDP Q22 Q23 X6 (Immediate_Offset (iword (&128))) *)
  0x4ebc1f9d;       (* arm_MOV_VEC Q29 Q28 128 *)
  0xf101c0bf;       (* arm_CMP X5 (rvalue (word 112)) *)
  0xce007509;       (* arm_EOR3 Q9 Q8 Q0 Q29 *)
  0x540005ec;       (* arm_BGT (word 188) *)
  0x0f00e413;       (* arm_MOVI D19 (word 0) *)
  0x4ea61cc7;       (* arm_MOV_VEC Q7 Q6 128 *)
  0x0f00e411;       (* arm_MOVI D17 (word 0) *)
  0x4ea51ca6;       (* arm_MOV_VEC Q6 Q5 128 *)
  0x4ea41c85;       (* arm_MOV_VEC Q5 Q4 128 *)
  0x4ea31c64;       (* arm_MOV_VEC Q4 Q3 128 *)
  0x4ea21c43;       (* arm_MOV_VEC Q3 Q2 128 *)
  0x6ebf87de;       (* arm_SUB_VEC Q30 Q30 Q31 32 128 *)
  0x4ea11c22;       (* arm_MOV_VEC Q2 Q1 128 *)
  0x0f00e412;       (* arm_MOVI D18 (word 0) *)
  0xf10180bf;       (* arm_CMP X5 (rvalue (word 96)) *)
  0x540005ec;       (* arm_BGT (word 188) *)
  0x4ea61cc7;       (* arm_MOV_VEC Q7 Q6 128 *)
  0x4ea51ca6;       (* arm_MOV_VEC Q6 Q5 128 *)
  0xf10140bf;       (* arm_CMP X5 (rvalue (word 80)) *)
  0x4ea41c85;       (* arm_MOV_VEC Q5 Q4 128 *)
  0x4ea31c64;       (* arm_MOV_VEC Q4 Q3 128 *)
  0x4ea11c23;       (* arm_MOV_VEC Q3 Q1 128 *)
  0x6ebf87de;       (* arm_SUB_VEC Q30 Q30 Q31 32 128 *)
  0x540006ac;       (* arm_BGT (word 212) *)
  0x4ea61cc7;       (* arm_MOV_VEC Q7 Q6 128 *)
  0x6ebf87de;       (* arm_SUB_VEC Q30 Q30 Q31 32 128 *)
  0x4ea51ca6;       (* arm_MOV_VEC Q6 Q5 128 *)
  0x4ea41c85;       (* arm_MOV_VEC Q5 Q4 128 *)
  0xf10100bf;       (* arm_CMP X5 (rvalue (word 64)) *)
  0x4ea11c24;       (* arm_MOV_VEC Q4 Q1 128 *)
  0x540007ac;       (* arm_BGT (word 244) *)
  0xf100c0bf;       (* arm_CMP X5 (rvalue (word 48)) *)
  0x4ea61cc7;       (* arm_MOV_VEC Q7 Q6 128 *)
  0x4ea51ca6;       (* arm_MOV_VEC Q6 Q5 128 *)
  0x4ea11c25;       (* arm_MOV_VEC Q5 Q1 128 *)
  0x6ebf87de;       (* arm_SUB_VEC Q30 Q30 Q31 32 128 *)
  0x540008ac;       (* arm_BGT (word 276) *)
  0xf10080bf;       (* arm_CMP X5 (rvalue (word 32)) *)
  0x4ea61cc7;       (* arm_MOV_VEC Q7 Q6 128 *)
  0x3dc010d8;       (* arm_LDR Q24 X6 (Immediate_Offset (word 64)) *)
  0x4ea11c26;       (* arm_MOV_VEC Q6 Q1 128 *)
  0x6ebf87de;       (* arm_SUB_VEC Q30 Q30 Q31 32 128 *)
  0x54000a0c;       (* arm_BGT (word 320) *)
  0x4ea11c27;       (* arm_MOV_VEC Q7 Q1 128 *)
  0x6ebf87de;       (* arm_SUB_VEC Q30 Q30 Q31 32 128 *)
  0xf10040bf;       (* arm_CMP X5 (rvalue (word 16)) *)
  0x54000b6c;       (* arm_BGT (word 364) *)
  0x6ebf87de;       (* arm_SUB_VEC Q30 Q30 Q31 32 128 *)
  0x3dc004d5;       (* arm_LDR Q21 X6 (Immediate_Offset (word 16)) *)
  0x14000069;       (* arm_B (word 420) *)
  0x4c9f7049;       (* arm_STR Q9 X2 (Postimmediate_Offset (word 16)) *)
  0x4e200928;       (* arm_REV64_VEC Q8 Q9 8 *)
  0x6e301d08;       (* arm_EOR_VEC Q8 Q8 Q16 128 *)
  0x3cc10409;       (* arm_LDR Q9 X0 (Postimmediate_Offset (word 16)) *)
  0x4ef9e111;       (* arm_PMULL2_VEC Q17 Q8 Q25 64 *)
  0x6e08451b;       (* arm_INS Q27 Q8 0 64 64 128 *)
  0x6e084712;       (* arm_INS Q18 Q24 0 64 64 128 *)
  0x0f00e410;       (* arm_MOVI D16 (word 0) *)
  0x2e281f7b;       (* arm_EOR_VEC Q27 Q27 Q8 64 *)
  0xce017529;       (* arm_EOR3 Q9 Q9 Q1 Q29 *)
  0x0ef2e372;       (* arm_PMULL_VEC Q18 Q27 Q18 64 *)
  0x0ef9e113;       (* arm_PMULL_VEC Q19 Q8 Q25 64 *)
  0x4c9f7049;       (* arm_STR Q9 X2 (Postimmediate_Offset (word 16)) *)
  0x4e200928;       (* arm_REV64_VEC Q8 Q9 8 *)
  0x6e301d08;       (* arm_EOR_VEC Q8 Q8 Q16 128 *)
  0x0ef7e11a;       (* arm_PMULL_VEC Q26 Q8 Q23 64 *)
  0x6e08451b;       (* arm_INS Q27 Q8 0 64 64 128 *)
  0x4ef7e11c;       (* arm_PMULL2_VEC Q28 Q8 Q23 64 *)
  0x3cc10409;       (* arm_LDR Q9 X0 (Postimmediate_Offset (word 16)) *)
  0x6e3a1e73;       (* arm_EOR_VEC Q19 Q19 Q26 128 *)
  0x2e281f7b;       (* arm_EOR_VEC Q27 Q27 Q8 64 *)
  0x0ef8e37b;       (* arm_PMULL_VEC Q27 Q27 Q24 64 *)
  0xce027529;       (* arm_EOR3 Q9 Q9 Q2 Q29 *)
  0x0f00e410;       (* arm_MOVI D16 (word 0) *)
  0x6e3b1e52;       (* arm_EOR_VEC Q18 Q18 Q27 128 *)
  0x6e3c1e31;       (* arm_EOR_VEC Q17 Q17 Q28 128 *)
  0x4c9f7049;       (* arm_STR Q9 X2 (Postimmediate_Offset (word 16)) *)
  0x4e200928;       (* arm_REV64_VEC Q8 Q9 8 *)
  0x6e301d08;       (* arm_EOR_VEC Q8 Q8 Q16 128 *)
  0x6e08451b;       (* arm_INS Q27 Q8 0 64 64 128 *)
  0x4ef6e11c;       (* arm_PMULL2_VEC Q28 Q8 Q22 64 *)
  0x6e3c1e31;       (* arm_EOR_VEC Q17 Q17 Q28 128 *)
  0x2e281f7b;       (* arm_EOR_VEC Q27 Q27 Q8 64 *)
  0x6e18077b;       (* arm_INS Q27 Q27 64 0 64 64 *)
  0x3cc10409;       (* arm_LDR Q9 X0 (Postimmediate_Offset (word 16)) *)
  0x0ef6e11a;       (* arm_PMULL_VEC Q26 Q8 Q22 64 *)
  0x4ef5e37b;       (* arm_PMULL2_VEC Q27 Q27 Q21 64 *)
  0x0f00e410;       (* arm_MOVI D16 (word 0) *)
  0x6e3a1e73;       (* arm_EOR_VEC Q19 Q19 Q26 128 *)
  0x6e3b1e52;       (* arm_EOR_VEC Q18 Q18 Q27 128 *)
  0xce037529;       (* arm_EOR3 Q9 Q9 Q3 Q29 *)
  0x4c9f7049;       (* arm_STR Q9 X2 (Postimmediate_Offset (word 16)) *)
  0x4e200928;       (* arm_REV64_VEC Q8 Q9 8 *)
  0x3cc10409;       (* arm_LDR Q9 X0 (Postimmediate_Offset (word 16)) *)
  0x6e301d08;       (* arm_EOR_VEC Q8 Q8 Q16 128 *)
  0x6e08451b;       (* arm_INS Q27 Q8 0 64 64 128 *)
  0x4ef4e11c;       (* arm_PMULL2_VEC Q28 Q8 Q20 64 *)
  0xce047529;       (* arm_EOR3 Q9 Q9 Q4 Q29 *)
  0x0ef4e11a;       (* arm_PMULL_VEC Q26 Q8 Q20 64 *)
  0x2e281f7b;       (* arm_EOR_VEC Q27 Q27 Q8 64 *)
  0x6e3a1e73;       (* arm_EOR_VEC Q19 Q19 Q26 128 *)
  0x0ef5e37b;       (* arm_PMULL_VEC Q27 Q27 Q21 64 *)
  0x0f00e410;       (* arm_MOVI D16 (word 0) *)
  0x6e3b1e52;       (* arm_EOR_VEC Q18 Q18 Q27 128 *)
  0x6e3c1e31;       (* arm_EOR_VEC Q17 Q17 Q28 128 *)
  0x4c9f7049;       (* arm_STR Q9 X2 (Postimmediate_Offset (word 16)) *)
  0x3dc014d9;       (* arm_LDR Q25 X6 (Immediate_Offset (word 80)) *)
  0x4e200928;       (* arm_REV64_VEC Q8 Q9 8 *)
  0x6e301d08;       (* arm_EOR_VEC Q8 Q8 Q16 128 *)
  0x6e08451b;       (* arm_INS Q27 Q8 0 64 64 128 *)
  0x4ef9e11c;       (* arm_PMULL2_VEC Q28 Q8 Q25 64 *)
  0x6e3c1e31;       (* arm_EOR_VEC Q17 Q17 Q28 128 *)
  0x2e281f7b;       (* arm_EOR_VEC Q27 Q27 Q8 64 *)
  0x3dc010d8;       (* arm_LDR Q24 X6 (Immediate_Offset (word 64)) *)
  0x6e18077b;       (* arm_INS Q27 Q27 64 0 64 64 *)
  0x3cc10409;       (* arm_LDR Q9 X0 (Postimmediate_Offset (word 16)) *)
  0x4ef8e37b;       (* arm_PMULL2_VEC Q27 Q27 Q24 64 *)
  0x0ef9e11a;       (* arm_PMULL_VEC Q26 Q8 Q25 64 *)
  0xce057529;       (* arm_EOR3 Q9 Q9 Q5 Q29 *)
  0x0f00e410;       (* arm_MOVI D16 (word 0) *)
  0x6e3b1e52;       (* arm_EOR_VEC Q18 Q18 Q27 128 *)
  0x6e3a1e73;       (* arm_EOR_VEC Q19 Q19 Q26 128 *)
  0x3dc00cd7;       (* arm_LDR Q23 X6 (Immediate_Offset (word 48)) *)
  0x4c9f7049;       (* arm_STR Q9 X2 (Postimmediate_Offset (word 16)) *)
  0x4e200928;       (* arm_REV64_VEC Q8 Q9 8 *)
  0x3cc10409;       (* arm_LDR Q9 X0 (Postimmediate_Offset (word 16)) *)
  0x6e301d08;       (* arm_EOR_VEC Q8 Q8 Q16 128 *)
  0x6e08451b;       (* arm_INS Q27 Q8 0 64 64 128 *)
  0x0f00e410;       (* arm_MOVI D16 (word 0) *)
  0x4ef7e11c;       (* arm_PMULL2_VEC Q28 Q8 Q23 64 *)
  0xce067529;       (* arm_EOR3 Q9 Q9 Q6 Q29 *)
  0x2e281f7b;       (* arm_EOR_VEC Q27 Q27 Q8 64 *)
  0x6e3c1e31;       (* arm_EOR_VEC Q17 Q17 Q28 128 *)
  0x0ef8e37b;       (* arm_PMULL_VEC Q27 Q27 Q24 64 *)
  0x0ef7e11a;       (* arm_PMULL_VEC Q26 Q8 Q23 64 *)
  0x6e3b1e52;       (* arm_EOR_VEC Q18 Q18 Q27 128 *)
  0x6e3a1e73;       (* arm_EOR_VEC Q19 Q19 Q26 128 *)
  0x4c9f7049;       (* arm_STR Q9 X2 (Postimmediate_Offset (word 16)) *)
  0x3dc008d6;       (* arm_LDR Q22 X6 (Immediate_Offset (word 32)) *)
  0x4e200928;       (* arm_REV64_VEC Q8 Q9 8 *)
  0x3cc10409;       (* arm_LDR Q9 X0 (Postimmediate_Offset (word 16)) *)
  0x6e301d08;       (* arm_EOR_VEC Q8 Q8 Q16 128 *)
  0x0f00e410;       (* arm_MOVI D16 (word 0) *)
  0x6e08451b;       (* arm_INS Q27 Q8 0 64 64 128 *)
  0x4ef6e11c;       (* arm_PMULL2_VEC Q28 Q8 Q22 64 *)
  0xce077529;       (* arm_EOR3 Q9 Q9 Q7 Q29 *)
  0x6e3c1e31;       (* arm_EOR_VEC Q17 Q17 Q28 128 *)
  0x0ef6e11a;       (* arm_PMULL_VEC Q26 Q8 Q22 64 *)
  0x2e281f7b;       (* arm_EOR_VEC Q27 Q27 Q8 64 *)
  0x3dc004d5;       (* arm_LDR Q21 X6 (Immediate_Offset (word 16)) *)
  0x6e3a1e73;       (* arm_EOR_VEC Q19 Q19 Q26 128 *)
  0x6e18077b;       (* arm_INS Q27 Q27 64 0 64 64 *)
  0x4ef5e37b;       (* arm_PMULL2_VEC Q27 Q27 Q21 64 *)
  0x6e3b1e52;       (* arm_EOR_VEC Q18 Q18 Q27 128 *)
  0x3dc000d4;       (* arm_LDR Q20 X6 (Immediate_Offset (word 0)) *)
  0x4e200928;       (* arm_REV64_VEC Q8 Q9 8 *)
  0x6e200bde;       (* arm_REV32_VEC Q30 Q30 8 *)
  0x3d80021e;       (* arm_STR Q30 X16 (Immediate_Offset (word 0)) *)
  0x6e301d08;       (* arm_EOR_VEC Q8 Q8 Q16 128 *)
  0x4c007049;       (* arm_STR Q9 X2 No_Offset *)
  0x6e084510;       (* arm_INS Q16 Q8 0 64 64 128 *)
  0x4ef4e11c;       (* arm_PMULL2_VEC Q28 Q8 Q20 64 *)
  0x0ef4e11a;       (* arm_PMULL_VEC Q26 Q8 Q20 64 *)
  0x6e3c1e31;       (* arm_EOR_VEC Q17 Q17 Q28 128 *)
  0x6e3a1e73;       (* arm_EOR_VEC Q19 Q19 Q26 128 *)
  0x2e281e10;       (* arm_EOR_VEC Q16 Q16 Q8 64 *)
  0x0ef5e210;       (* arm_PMULL_VEC Q16 Q16 Q21 64 *)
  0x6e301e52;       (* arm_EOR_VEC Q18 Q18 Q16 128 *)
  0xfd400150;       (* arm_LDR D16 X10 (Immediate_Offset (word 0)) *)
  0x6e114235;       (* arm_EXT Q21 Q17 Q17 64 *)
  0xce114e52;       (* arm_EOR3 Q18 Q18 Q17 Q19 *)
  0x0ef0e23d;       (* arm_PMULL_VEC Q29 Q17 Q16 64 *)
  0xce1d5652;       (* arm_EOR3 Q18 Q18 Q29 Q21 *)
  0x0ef0e251;       (* arm_PMULL_VEC Q17 Q18 Q16 64 *)
  0x6e124255;       (* arm_EXT Q21 Q18 Q18 64 *)
  0xce115673;       (* arm_EOR3 Q19 Q19 Q17 Q21 *)
  0x6e134273;       (* arm_EXT Q19 Q19 Q19 64 *)
  0x4e200a73;       (* arm_REV64_VEC Q19 Q19 8 *)
  0x4c007073;       (* arm_STR Q19 X3 No_Offset *)
  0xaa0903e0;       (* arm_MOV X0 X9 *)
  0x6d412fea;       (* arm_LDP D10 D11 SP (Immediate_Offset (iword (&16))) *)
  0x6d4237ec;       (* arm_LDP D12 D13 SP (Immediate_Offset (iword (&32))) *)
  0x6d433fee;       (* arm_LDP D14 D15 SP (Immediate_Offset (iword (&48))) *)
  0x6d4027e8;       (* arm_LDP D8 D9 SP (Immediate_Offset (iword (&0))) *)
  0x910143ff;       (* arm_ADD SP SP (rvalue (word 80)) *)
  0xd65f03c0;       (* arm_RET X30 *)
  0x52800000;       (* arm_MOV W0 (rvalue (word 0)) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let AESV8_GCM_8X_ENC_256_WB_EXEC = ARM_MK_EXEC_RULE aesv8_gcm_8x_enc_256_wb_mc;;

(* ========================================================================= *)
(* P2 - Layer-1 specification glue for AES-256 CTR + GHASH.                   *)
(*                                                                           *)
(* These are the local CTR wrappers, Htable predicate, reversefields         *)
(* equivalences, hardware-primitive reconstruction lemmas and Karatsuba      *)
(* reduction lemmas needed by the correctness proof.  They mirror the x4     *)
(* AES-128-GCM kernel proofs (s2n-bignum-dev branch `gcm`,                    *)
(* arm/proofs/aes_gcm_enc_kernel_x4_reload_round_keys_full.ml), retargeted   *)
(* to AES-256 (15-entry key schedule / 14 aese/aesmc rounds) and to the 8x   *)
(* Htable layout (H^1..H^8, offsets 0..176).  Cipher-agnostic lemmas are     *)
(* ported verbatim.                                                          *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Some specification concepts.                                              *)
(* ------------------------------------------------------------------------- *)

let ctr_block = new_definition
 `ctr_block nonce ctr :int128 = word_join (nonce:96 word) (word ctr:int32)`;;

(**** This is the form that we actually XOR little-endian bytes with
 **** in the algorithm, so we switch back out of NIST big-endian
 ****)

let aes_ctr_block = new_definition
 `aes_ctr_block nonce rk i =
    word_reversefields 8 (aes256_cipher (ctr_block nonce (i + 2)) rk)`;;

(* The i-th ciphertext block: keystream XOR plaintext - little-endian *)

let cipher_block = new_definition
 `cipher_block nonce rk inblock i =
    word_xor (aes_ctr_block nonce rk i) (inblock i)`;;

(* The NIST convention is big-endian, however *)

let nist_cipher_block = new_definition
 `nist_cipher_block nonce rk inblock i =
        word_reversefields 8 (cipher_block nonce rk inblock i)`;;

(* Restricted Htable predicate for the 8x-unrolled kernel: the main loop
   uses H^1..H^8 and their Karatsuba mid terms (12 entries, offsets 0..176).
   This extends the x4 kernel's htable_mem_4 with the H^5..H^8 slots.
   NB the karatsuba_mid join order (high power in the high 64-bit lane)
   follows the x4 htable_mem_4 convention; it is reconciled against the
   actual x8 Htable loads in the main-loop phase (P5). *)

let htable_mem_8 = new_definition
 `htable_mem_8 (h:int128) (ptr:int64) (s:armstate) <=>
  read (memory :> bytes128 ptr) s =
    byteswap128(h_power h 0) /\
  read (memory :> bytes128 (word_add ptr (word 16))) s =
    word_join (karatsuba_mid(h_power h 1) : 64 word)
              (karatsuba_mid(h_power h 0) : 64 word) /\
  read (memory :> bytes128 (word_add ptr (word 32))) s =
    byteswap128(h_power h 1) /\
  read (memory :> bytes128 (word_add ptr (word 48))) s =
    byteswap128(h_power h 2) /\
  read (memory :> bytes128 (word_add ptr (word 64))) s =
    word_join (karatsuba_mid(h_power h 3) : 64 word)
              (karatsuba_mid(h_power h 2) : 64 word) /\
  read (memory :> bytes128 (word_add ptr (word 80))) s =
    byteswap128(h_power h 3) /\
  read (memory :> bytes128 (word_add ptr (word 96))) s =
    byteswap128(h_power h 4) /\
  read (memory :> bytes128 (word_add ptr (word 112))) s =
    word_join (karatsuba_mid(h_power h 5) : 64 word)
              (karatsuba_mid(h_power h 4) : 64 word) /\
  read (memory :> bytes128 (word_add ptr (word 128))) s =
    byteswap128(h_power h 5) /\
  read (memory :> bytes128 (word_add ptr (word 144))) s =
    byteswap128(h_power h 6) /\
  read (memory :> bytes128 (word_add ptr (word 160))) s =
    word_join (karatsuba_mid(h_power h 7) : 64 word)
              (karatsuba_mid(h_power h 6) : 64 word) /\
  read (memory :> bytes128 (word_add ptr (word 176))) s =
    byteswap128(h_power h 7)`;;

(* ------------------------------------------------------------------------- *)
(* Equivalences between the FIPS197 specs and the ARM hardware specs.        *)
(* ------------------------------------------------------------------------- *)

let WORD_SUBWORD_REVERSEFIELDS = prove
 (`word_subword (word_reversefields 8 x) (0,8):byte = word_subword x (120,8) /\
   word_subword (word_reversefields 8 x) (8,8):byte = word_subword x (112,8) /\
   word_subword (word_reversefields 8 x) (16,8):byte = word_subword x (104,8) /\
   word_subword (word_reversefields 8 x) (24,8):byte = word_subword x (96,8) /\
   word_subword (word_reversefields 8 x) (32,8):byte = word_subword x (88,8) /\
   word_subword (word_reversefields 8 x) (40,8):byte = word_subword x (80,8) /\
   word_subword (word_reversefields 8 x) (48,8):byte = word_subword x (72,8) /\
   word_subword (word_reversefields 8 x) (56,8):byte = word_subword x (64,8) /\
   word_subword (word_reversefields 8 x) (64,8):byte = word_subword x (56,8) /\
   word_subword (word_reversefields 8 x) (72,8):byte = word_subword x (48,8) /\
   word_subword (word_reversefields 8 x) (80,8):byte = word_subword x (40,8) /\
   word_subword (word_reversefields 8 x) (88,8):byte = word_subword x (32,8) /\
   word_subword (word_reversefields 8 x) (96,8):byte = word_subword x (24,8) /\
   word_subword (word_reversefields 8 x) (104,8):byte = word_subword x (16,8) /\
   word_subword (word_reversefields 8 x) (112,8):byte = word_subword x (8,8) /\
   word_subword (word_reversefields 8 x:int128) (120,8):byte =
   word_subword x (0,8)`,
  CONV_TAC WORD_BLAST);;

let AES_SUB_BYTES_SHIFT_ROWS = prove
 (`!x:int128. aes_sub_bytes joined_GF2 (aes_shift_rows x) =
              aes_shift_rows (aes_sub_bytes joined_GF2 x)`,
  REWRITE_TAC[aes_sub_bytes; aes_shift_rows; word_join_list_16_8] THEN
  CONV_TAC(TOP_DEPTH_CONV EL_CONV) THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[aes_sub_bytes_select; LET_DEF; LET_END_DEF] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[]);;

let WORD_XOR_REVERSEFIELDS = prove
 (`!x y:int128.
        word_xor (word_reversefields 8 x) (word_reversefields 8 y) =
        word_reversefields 8 (word_xor x y)`,
  CONV_TAC WORD_BLAST);;

let AES_SUB_BYTES_REVERSEFIELDS = prove
 (`!x:int128. aes_sub_bytes joined_GF2 (word_reversefields 8 x) =
              word_reversefields 8 (aes_sub_bytes joined_GF2 x)`,
  REWRITE_TAC[aes_sub_bytes; aes_sub_bytes_select; word_join_list_16_8] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
  REWRITE_TAC[WORD_SUBWORD_REVERSEFIELDS] THEN
  CONV_TAC WORD_BLAST);;

let FIPS197_EQ_SHIFT_ROWS = prove
 (`!x:int128.
        fips197_shift_rows x =
        word_reversefields 8 (aes_shift_rows (word_reversefields 8 x))`,
  REWRITE_TAC[fips197_shift_rows; aes_shift_rows; word_join_list_16_8] THEN
  CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
  REWRITE_TAC[WORD_SUBWORD_REVERSEFIELDS] THEN CONV_TAC WORD_BLAST);;

let FIPS197_EQ_MIX_COLUMNS = prove
 (`!x:int128.
        fips197_mix_columns x =
        word_reversefields 8 (aes_mix_columns  (word_reversefields 8 x))`,
  REWRITE_TAC[aes_mix_columns; fips197_mix_columns;
              word_join_list_16_8; aes_mix_word] THEN
  GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
  REWRITE_TAC[WORD_SUBWORD_REVERSEFIELDS] THEN CONV_TAC WORD_BLAST);;

(* ------------------------------------------------------------------------- *)
(* Reconstruction of high-level concepts from the computed expressions.      *)
(* ------------------------------------------------------------------------- *)

let WORD_JOIN_COMBINE_LEMMA = prove
 (`(!(x:N word) pos1 pos2.
        pos1 + 8 = pos2
        ==> word_join (word_subword x (pos2,8):byte)
                      (word_subword x (pos1,8):byte):int16 =
            word_subword x (pos1,16)) /\
   (!(x:N word) pos1 pos2.
        pos1 + 16 = pos2
        ==> word_join (word_subword x (pos2,16):int16)
                      (word_subword x (pos1,16):int16):int32 =
            word_subword x (pos1,32)) /\
   (!(x:N word) pos1 pos2.
        pos1 + 32 = pos2
        ==> word_join (word_subword x (pos2,32):int32)
                      (word_subword x (pos1,32):int32):int64 =
            word_subword x (pos1,64)) /\
   (!(x:N word) pos1 pos2.
        pos1 + 64 = pos2
        ==> word_join (word_subword x (pos2,64):int64)
                      (word_subword x (pos1,64):int64):int128 =
            word_subword x (pos1,128)) /\
   (!x:int128. word_subword x (0,128) = x)`,
  REWRITE_TAC[CONJ_ASSOC] THEN
  CONJ_TAC THENL [ALL_TAC; CONV_TAC WORD_BLAST] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; DIMINDEX_16; DIMINDEX_32;
              DIMINDEX_64; DIMINDEX_128] THEN
  CONV_TAC EXPAND_CASES_CONV THEN
  REWRITE_TAC[BIT_WORD_JOIN; BIT_WORD_SUBWORD;
        DIMINDEX_8; DIMINDEX_16; DIMINDEX_32; DIMINDEX_64; DIMINDEX_128] THEN
  REWRITE_TAC[GSYM ADD_ASSOC] THEN CONV_TAC NUM_REDUCE_CONV);;

let WORD_SUBWORD_REVERSEFIELDS_32 = prove
 (`word_subword (word_reversefields 32 x:int128) (0,32):int32 =
   word_subword x (96,32) /\
   word_subword (word_reversefields 32 x:int128) (32,32):int32 =
   word_subword x (64,32) /\
   word_subword (word_reversefields 32 x:int128) (64,32):int32 =
   word_subword x (32,32) /\
   word_subword (word_reversefields 32 x:int128) (96,32):int32 =
   word_subword x (0,32)`,
  CONV_TAC WORD_BLAST);;

let WORD_SUBWORD_BYTESWAP128 = prove
 (`(!x. word_subword (byteswap128 x) (0,64):int64 = word_subword x (64,64)) /\
   (!x. word_subword (byteswap128 x) (64,64):int64 = word_subword x (0,64))`,
  REWRITE_TAC[byteswap128] THEN CONV_TAC WORD_BLAST);;

(* ------------------------------------------------------------------------- *)
(* byteswap128 toolkit for the P6 Q19 GHASH fold (session 019).               *)
(*                                                                           *)
(* KEY STRUCTURAL FACT (objdump of the frozen .o, sessions 018/019): the x8   *)
(* main-loop body has NO trailing `ext v19` byteswap (last v19 write is the   *)
(* raw MODULO `eor3 v19,v19,v21,v17`@0x9c8, then `b.lt`@0x9e4; the            *)
(* `ext v19`@0x4cc is the NEXT loop-top's PRE).  So the body-end Q19 value is  *)
(* the RAW reduce, and the P6 body postcondition's Q19 residual (goal[0]) is   *)
(*     <raw reduce, word_xor-headed> = byteswap128(nist_ghash ... (8*i+8))     *)
(* whereas the x4 kernels DO have a trailing ext, so their fold's LHS is       *)
(* already byteswap-shaped and x4's opening `byteswap128;WORD_BLAST +          *)
(* MATCH_MP_TAC(strip)` applies.  On x8 that opener FAILS ("No match").        *)
(*                                                                           *)
(* These three lemmas move the RHS byteswap onto the LHS and cancel the        *)
(* ext/byteswap half-swaps, so the fold can then follow x4's ABBREV +          *)
(* RECONSTRUCT_POLYVAL_REDUCE_G2 + POLYVAL_REDUCE_G2 + GHASH_POLYVAL_ACC_      *)
(* BATCHED tail (reload_full 1043-1107, scaled 4->8).  BS_EXT is decisive:     *)
(* byteswap128 and the Karatsuba `ext` (word_subword(word_join x x)(64,128))    *)
(* are inverse half-swaps, so they cancel to the identity.                     *)
(* ------------------------------------------------------------------------- *)

let BS_INVOL = prove
 (`!x y:int128. byteswap128 x = y ==> x = byteswap128 y`,
  REWRITE_TAC[byteswap128] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(SUBST1_TAC o GSYM) THEN CONV_TAC WORD_BLAST);;

let BS_XOR = prove
 (`!a b:int128. byteswap128(word_xor a b) =
                word_xor (byteswap128 a) (byteswap128 b)`,
  REWRITE_TAC[byteswap128] THEN REPEAT GEN_TAC THEN CONV_TAC WORD_BLAST);;

let BS_EXT = prove
 (`!x:int128. byteswap128(word_subword (word_join x x:int256) (64,128)) = x`,
  REWRITE_TAC[byteswap128] THEN GEN_TAC THEN CONV_TAC WORD_BLAST);;

(* byteswap128 involution + injectivity (session 021).  Used to strip a         *)
(* byteswap128 from BOTH sides of an equation `byteswap128 x = byteswap128 y`.   *)
let BS_INVOL2 = prove
 (`!x:int128. byteswap128(byteswap128 x) = x`,
  REWRITE_TAC[byteswap128] THEN GEN_TAC THEN CONV_TAC WORD_BLAST);;

let BS_INJ = prove
 (`!x y:int128. (byteswap128 x = byteswap128 y) <=> (x = y)`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN(MP_TAC o AP_TERM `byteswap128`) THEN REWRITE_TAC[BS_INVOL2];
    DISCH_THEN SUBST1_TAC THEN REFL_TAC]);;

(* ------------------------------------------------------------------------- *)
(* SESSION 021 BREAKTHROUGH — how the x8 Q19 fold actually fires.             *)
(*                                                                           *)
(* Sessions 017-020 could not make ANY fold-back (GSYM ghash_reduce_raw or    *)
(* GSYM polyval_reduce_g2) fire on the real body-end Q19 residual, and the    *)
(* s020 recipe was validated only on a SYNTHETIC free-var `ghash_reduce_raw   *)
(* P1 P2 P3`.  Session 021 reconstructed the real residual and proved the     *)
(* fold-back genuinely fails on it — then root-caused WHY and found the fix:  *)
(*                                                                           *)
(* ROOT CAUSE: the body driver `NSTEP` applies WORD_SIMPLE_SUBWORD_CONV after *)
(* EVERY step.  The GHASH accumulators Q17/Q18/Q19 are word_join-headed        *)
(* (Karatsuba lane sums), and that conv pushes word_subword INTO the joins,   *)
(* collapsing `word_subword(word_join a b)(0,64)`->b etc.  This destroys the  *)
(* `LO p1`(=word_subword p1 (0,64)) and `ext p1`(=word_subword(word_join p1   *)
(* p1)(64,128)) patterns that `ghash_reduce_raw`'s definition needs, so       *)
(* GSYM ghash_reduce_raw can no longer first-order-match.  Confirmed by a     *)
(* decisive synthetic test: `ghash_reduce_raw` of word_join accumulators      *)
(* folds via GSYM BEFORE the conv, but stays word_xor-headed AFTER it.        *)
(*                                                                           *)
(* THE FIX (two parts):                                                       *)
(*  (1) A GUARDED NSTEP that SKIPS WORD_SIMPLE_SUBWORD_CONV on any assumption  *)
(*      whose read-component is Q17/Q18/Q19 (see NSTEP_G in the body proof),   *)
(*      preserving the accumulators' ext/LO structure so the final Q19 stays   *)
(*      ghash_reduce_raw-shaped (modulo eor3 XOR re-association).              *)
(*  (2) A one-line AC-swap                                                     *)
(*        word_xor (word_xor x e) p = word_xor (word_xor x p) e               *)
(*      (WORD_BITWISE_RULE; int128 atoms — cheap) to reorder the top XOR from  *)
(*      eor3's `(p3 (+) ext) (+) pmul` grouping to the def's `(p3 (+) pmul)    *)
(*      (+) ext`, after which GSYM ghash_reduce_raw FIRES (LHS 371k -> 69k,    *)
(*      head becomes ghash_reduce_raw).                                        *)
(*                                                                           *)
(* Then the s020 chain runs: GHASH_REDUCE_RAW_IS_POLYVAL_G2 (-> g2),           *)
(* MATCH_MP_TAC BS_INVOL, BYTESWAP128_G2_PROP3 (LHS -> byteswap128(prop3 A));  *)
(* RHS nist_ghash folds via NIST_GHASH_IS_POLYVAL + 8(i+1)=SUC^8 + list_of_seq *)
(* + APPEND + GHASH_ACC_APPEND, then the CONS-list SUC-form indices are        *)
(* normalised to +n form with REWRITE_TAC[ADD1;GSYM ADD_ASSOC]+NUM_ADD_CONV    *)
(* (else the batched ISPECL won't match), then GHASH_POLYVAL_ACC_BATCHED       *)
(* collapses it to prop3 B.  The remaining goal is                             *)
(*   `byteswap128(polyval_reduce_prop3 A) = polyval_reduce_prop3 B`            *)
(* where A (~197k, word_join of inlined g2 lanes) and B (~1.2k, clean          *)
(* cipherblock (x) h_power chain) differ by the store-order byteswap — the     *)
(* final lane-wise BITBLAST match (x4 reload_full CONJ1 territory) is the ONE  *)
(* remaining step (blocker A not yet closed as of session 021).               *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Two more building blocks for the P6 Q19 fold (session 020).                *)
(*                                                                           *)
(* Session 020 pinned down WHY the x4 Q19 fold opener does not transfer.  The *)
(* x4 acc conjunct is ALSO `byteswap128(nist_ghash ...)` (reload_full l.909), *)
(* and x4's opener (reload_full 1043-1051) rewrites `byteswap128` + the        *)
(* `word_subword(word_join h l)(64,128) = word_join(LO h)(HI l)` BLAST rule,   *)
(* which normalises BOTH the RHS byteswap AND x4's TRAILING-`ext` LHS into a   *)
(* `word_join(word_subword _)(word_subword _)` shape, then strips both joins   *)
(* with a MATCH_MP_TAC.  x8 has NO trailing `ext` (its last v19 write is the   *)
(* raw MODULO eor3@0x9c8), so its LHS stays `word_xor`-headed and the join     *)
(* strip fails "No match" (reproduced deterministically: STEP2 MATCH_MP_TAC    *)
(* No match).  The x8 route is instead: MATCH_MP_TAC BS_INVOL to flip the RHS  *)
(* byteswap onto the LHS, fold the LHS raw reduce to `ghash_reduce_raw` (whose *)
(* GSYM must be applied BEFORE the cheap-close subword blast destroys the      *)
(* `ext`/`word_pmul(LO _)` structure), bridge to `polyval_reduce_g2` via the   *)
(* proven GHASH_REDUCE_RAW_IS_POLYVAL_G2, rewrite to prop3 via the lemma just  *)
(* below, and match lane-wise against the batched-GHASH prop3.                 *)
(*                                                                           *)
(* EXT_TO_JOIN: the `ext` (Karatsuba half-take) written explicitly as a join. *)
(* BYTESWAP128_G2_PROP3: push byteswap128 through the g2->prop3 reduction so   *)
(* the fold can match byteswap128(prop3 W) on both sides (RHS byteswap128(NG)  *)
(* = byteswap128(prop3 chain) via GHASH_POLYVAL_ACC_BATCHED).                  *)
(* ------------------------------------------------------------------------- *)

let EXT_TO_JOIN = prove
 (`!x:int128. word_subword (word_join x x : int256) (64,128) =
   word_join (word_subword x (0,64):int64) (word_subword x (64,64):int64) : int128`,
  GEN_TAC THEN CONV_TAC WORD_BLAST);;

(* NB BYTESWAP128_G2_PROP3 needs POLYVAL_REDUCE_G2, so it is defined further     *)
(* below, right after PMUL_KARATSUBA_JOIN_ALT.                                   *)

let WORD_SUBWORD_CTR_BLOCK_32 = prove
 (`word_subword (ctr_block nonce cnt) (0,32):int32 = word cnt /\
   word_subword (ctr_block nonce cnt) (32,32):int32 =
     word_subword nonce (0,32) /\
   word_subword (ctr_block nonce cnt) (64,32):int32 =
     word_subword nonce (32,32) /\
   word_subword (ctr_block nonce cnt) (96,32):int32 =
     word_subword nonce (64,32)`,
  REWRITE_TAC[ctr_block] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[]);;

let CTR_BLOCK_RECONSTRUCT_REV8 = prove
 (`word_join
    (word_join (word_reversefields 8 (word ctr):int32)
               (word_reversefields 8 (word_subword nonce (0,32):int32)):int64)
    (word_join (word_reversefields 8 (word_subword nonce (32,32):int32))
               (word_reversefields 8 (word_subword nonce (64,32):int32)):int64)
    = word_reversefields 8 (ctr_block nonce ctr)`,
  REWRITE_TAC[ctr_block] THEN CONV_TAC WORD_BLAST);;

let CTR_BLOCK_RECONSTRUCT_REV32 = prove
 (`word_join
    (word_join (word ctr:int32)
               (word_subword nonce (0,32):int32):int64)
    (word_join (word_subword nonce (32,32):int32)
               (word_subword nonce (64,32):int32):int64) =
  word_reversefields 32 (ctr_block nonce ctr)`,
  REWRITE_TAC[ctr_block] THEN CONV_TAC WORD_BLAST);;

let AES_CTR_BLOCK_RECONSTRUCT = prove
 (`word_reversefields 8 (aes256_cipher (ctr_block nonce (i + 2)) rk) =
   aes_ctr_block nonce rk i /\
   word_reversefields 8 (aes256_cipher (ctr_block nonce (i + 3)) rk) =
   aes_ctr_block nonce rk (i + 1) /\
   word_reversefields 8 (aes256_cipher (ctr_block nonce (i + 4)) rk) =
   aes_ctr_block nonce rk (i + 2) /\
   word_reversefields 8 (aes256_cipher (ctr_block nonce (i + 5)) rk) =
   aes_ctr_block nonce rk (i + 3)`,
  REWRITE_TAC[aes_ctr_block; GSYM ADD_ASSOC] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let CIPHER_BLOCK_NIST = prove
 (`cipher_block nonce rk inblock i =
        word_reversefields 8 (nist_cipher_block nonce rk inblock i)`,
  REWRITE_TAC[nist_cipher_block; WORD_REVERSEFIELDS_REVERSEFIELDS]);;

(*** Direct implementation of AES256 using the hardware primitives.
 *** 14 aese (rk0..rk13), 13 interleaved aesmc, and a final word_xor rk14. ***)

let AES256_CIPHER_RECONSTRUCT = prove
 (`word_xor (aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc
    (aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc (aese
    (aesmc (aese (aesmc (aese (aesmc (aese plaintext rk0)) rk1)) rk2)) rk3))
    rk4)) rk5)) rk6)) rk7)) rk8)) rk9)) rk10)) rk11)) rk12)) rk13) rk14 =
   word_reversefields 8
    (aes256_cipher (word_reversefields 8 plaintext)
        (MAP (word_reversefields 8)
             [rk0; rk1; rk2; rk3; rk4; rk5; rk6; rk7; rk8; rk9; rk10;
              rk11; rk12; rk13; rk14]))`,
  REWRITE_TAC[aes256_cipher; LET_DEF; LET_END_DEF; MAP] THEN
  CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
  REWRITE_TAC[aesmc; aese; fips197_final_round; fips197_round] THEN
  REWRITE_TAC[AES_SUB_BYTES_SHIFT_ROWS] THEN
  REWRITE_TAC[FIPS197_EQ_SHIFT_ROWS; FIPS197_EQ_MIX_COLUMNS; fips197_sub_bytes;
              WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
  REWRITE_TAC[GSYM WORD_XOR_REVERSEFIELDS; WORD_REVERSEFIELDS_REVERSEFIELDS;
              GSYM AES_SUB_BYTES_REVERSEFIELDS]);;

(*** This is the sequence in the code, folding an XOR in sooner ***)

let XOR_AES256_CIPHER_RECONSTRUCT = prove
 (`word_xor (aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc
    (aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc (aese (aesmc (aese
    (aesmc (aese (aesmc (aese (aesmc (aese plaintext rk0)) rk1)) rk2)) rk3))
    rk4)) rk5)) rk6)) rk7)) rk8)) rk9)) rk10)) rk11)) rk12)) rk13)
   (word_xor rk14 inblock) =
   word_xor
    (word_reversefields 8
      (aes256_cipher (word_reversefields 8 plaintext)
         (MAP (word_reversefields 8)
              [rk0; rk1; rk2; rk3; rk4; rk5; rk6; rk7; rk8; rk9; rk10;
               rk11; rk12; rk13; rk14])))
    inblock`,
  REWRITE_TAC[WORD_XOR_ASSOC] THEN REWRITE_TAC[AES256_CIPHER_RECONSTRUCT]);;

(* aes256_cipher reads only EL 0..14 of its key list (see common/fips197.ml),  *)
(* so replacing the key argument by its explicit first-15 EL-projection is a    *)
(* no-op.  UNCONDITIONAL (no `LENGTH rk = 15` needed).  This closes the final   *)
(* residual left on each ciphertext out-block conjunct after                    *)
(* XOR_AES256_CIPHER_RECONSTRUCT + MAP + WORD_REVERSEFIELDS_REVERSEFIELDS: those *)
(* rewrites collapse the per-element `word_reversefields`, but leave the key as  *)
(* the explicit list `[EL 0 rk; ...; EL 14 rk]` rather than `rk`.  The x4 proof  *)
(* sidesteps this by `ASM_CASES_TAC \`LENGTH rk = 11\`` + `EXPAND_TAC "rk"` at    *)
(* the top of its _CORRECT (making `rk` a concrete cons-list); this lemma is     *)
(* the cleaner route for the x8 statement, which keeps `rk` a free variable.     *)
let AES256_CIPHER_KEYLIST = prove
 (`aes256_cipher p
     [EL 0 rk; EL 1 rk; EL 2 rk; EL 3 rk; EL 4 rk; EL 5 rk; EL 6 rk; EL 7 rk;
      EL 8 rk; EL 9 rk; EL 10 rk; EL 11 rk; EL 12 rk; EL 13 rk; EL 14 rk] =
   aes256_cipher p rk`,
  REWRITE_TAC[aes256_cipher] THEN
  CONV_TAC(DEPTH_CONV EL_CONV) THEN
  REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The reduction pattern that is used in the code (p1, p2, p3 are the        *)
(* Karatsuba subcomponents of an implicit 256-bit result).                   *)
(* ------------------------------------------------------------------------- *)

let polyval_reduce_g2 = new_definition
 `polyval_reduce_g2 p1 p2 p3 =
        let (HI:int128->int64) = \x. word_subword x (64,64)
        and (LO:int128->int64) = \x. word_subword x (0,64) in
        let ks = word_xor (word_xor p1 p2) p3 in
        let w1 = word_pmul (LO p1) (word 13979173243358019584 : int64) in
        let w2 = word_pmul
                 (word_xor (word_xor (LO w1) (HI p1))
                           (LO(word_xor (word_xor p1 p2) p3)))
                 (word 13979173243358019584 : int64) in
        word_xor
           (word_join
              (LO (word_xor (word_xor w1 (word_join (LO p1) (HI p1))) ks))
              (HI (word_xor (word_xor w1 (word_join (LO p1) (HI p1))) ks))
              : int128)
           (word_xor w2 p2 : int128)`;;

let RECONSTRUCT_POLYVAL_REDUCE_G2 =
  REWRITE_RULE[LET_DEF; LET_END_DEF] (GSYM polyval_reduce_g2);;

let POLYVAL_REDUCE_G2 = prove
 (`polyval_reduce_g2 p1 p2 p3 =
    polyval_reduce_prop3
      ((word_join : int128 -> int128 -> (256)word)
         (word_join (word_subword p2 (64,64):int64)
                    (word_xor (word_subword (word_xor (word_xor p1 p2) p3)
                                            (64,64):int64)
                              (word_subword p2 (0,64):int64)): int128)
         (word_join (word_xor (word_subword
          (word_xor (word_xor p1 p2) p3) (0,64):int64)
                    (word_subword p1 (64,64):int64))
                    (word_subword p1 (0,64):int64): int128))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[polyval_reduce_g2; polyval_reduce_prop3;
              LET_DEF; LET_END_DEF] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  ABBREV_TAC
   `w1 =  (word_pmul:int64->int64->int128)
      (word_subword (p1:int128) (0,64)) (word 13979173243358019584)` THEN
  ABBREV_TAC `ks:int128 = word_xor (word_xor p1 p2) p3` THEN
  REWRITE_TAC[WORD_SUBWORD_XOR] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  ABBREV_TAC
   `w2:int128 = word_pmul
     (word_xor (word_xor (word_subword (w1:int128) (0,64):int64)
                     (word_subword (p1:int128) (64,64):int64))
           (word_subword (ks:int128) (0,64):int64))
     (word 13979173243358019584:int64)` THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE (LAND_CONV o LAND_CONV)
   [WORD_BITWISE_RULE
    `word_xor (word_xor w1 p1) ks = word_xor (word_xor ks p1) w1`]) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN BITBLAST_TAC);;

(* ------------------------------------------------------------------------- *)
(* Variants of the existing Karatsuba lemmas better fitting the code.        *)
(* ------------------------------------------------------------------------- *)

let PMUL_KARATSUBA_JOIN = prove
 (`!(a:int128) (b:int128).
    (word_pmul a b : 256 word) =
    let p1 = word_pmul (word_subword a (0,64):int64)
                       (word_subword b (0,64):int64) : int128 in
    let p2 = word_pmul (word_subword a (64,64):int64)
                       (word_subword b (64,64):int64) : int128 in
    let p3 = word_pmul (word_xor (word_subword a (0,64):int64)
                                 (word_subword a (64,64):int64))
                       (word_xor (word_subword b (0,64):int64)
                                 (word_subword b (64,64):int64)) : int128 in
    let ks = word_xor (word_xor p1 p2) p3 in
    (word_join : int128 -> int128 -> 256 word)
      (word_join (word_subword p2 (64,64):int64)
                 (word_xor (word_subword ks (64,64):int64)
                           (word_subword p2 (0,64):int64)) : int128)
      (word_join (word_xor (word_subword ks (0,64):int64)
                           (word_subword p1 (64,64):int64))
                 (word_subword p1 (0,64):int64) : int128)`,
  REPEAT GEN_TAC THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[REWRITE_RULE[LET_DEF; LET_END_DEF] PMUL_KARATSUBA] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  CONV_TAC WORD_BLAST);;

let PMUL_KARATSUBA_JOIN_ALT = prove
 (`!(a:int128) (b:int128).
    (word_pmul a b : 256 word) =
    let p1 = word_pmul (word_subword a (0,64):int64)
                       (word_subword b (0,64):int64) : int128 in
    let p2 = word_pmul (word_subword a (64,64):int64)
                       (word_subword b (64,64):int64) : int128 in
    let p3 = word_pmul (word_xor (word_subword a (64,64):int64)
                                 (word_subword a (0,64):int64))
                       (word_xor (word_subword b (0,64):int64)
                                 (word_subword b (64,64):int64)) : int128 in
    let ks = word_xor (word_xor p1 p2) p3 in
    (word_join : int128 -> int128 -> 256 word)
      (word_join (word_subword p2 (64,64):int64)
                 (word_xor (word_subword ks (64,64):int64)
                           (word_subword p2 (0,64):int64)) : int128)
      (word_join (word_xor (word_subword ks (0,64):int64)
                           (word_subword p1 (64,64):int64))
                 (word_subword p1 (0,64):int64) : int128)`,
  REWRITE_TAC[PMUL_KARATSUBA_JOIN] THEN REWRITE_TAC[WORD_XOR_SYM]);;

(* Push byteswap128 through the g2 -> prop3 reduction (session 020; needs        *)
(* POLYVAL_REDUCE_G2, hence defined here).  Used by the P6 Q19 fold: after       *)
(* MATCH_MP_TAC BS_INVOL the goal is `byteswap128(<raw reduce>) = nist_ghash`;    *)
(* the raw reduce folds to `polyval_reduce_g2` (via GHASH_REDUCE_RAW_IS_POLYVAL_  *)
(* G2), this lemma rewrites `byteswap128(g2 ..)` to `byteswap128(prop3 W)`, and   *)
(* the RHS `byteswap128(nist_ghash ..)` becomes `byteswap128(prop3 chain)` via    *)
(* GHASH_POLYVAL_ACC_BATCHED — so the two match lane-wise under one BITBLAST.     *)
let BYTESWAP128_G2_PROP3 = prove
 (`!p1 p2 p3:int128.
     byteswap128(polyval_reduce_g2 p1 p2 p3) =
     byteswap128(polyval_reduce_prop3
      ((word_join : int128 -> int128 -> (256)word)
         (word_join (word_subword p2 (64,64):int64)
                    (word_xor (word_subword (word_xor (word_xor p1 p2) p3)
                                            (64,64):int64)
                              (word_subword p2 (0,64):int64)): int128)
         (word_join (word_xor (word_subword (word_xor (word_xor p1 p2) p3)
                                            (0,64):int64)
                    (word_subword p1 (64,64):int64))
                    (word_subword p1 (0,64):int64): int128)))`,
  REWRITE_TAC[POLYVAL_REDUCE_G2]);;

(* ========================================================================= *)
(* P3 - First register-only AES-256 block bridge.                            *)
(*                                                                           *)
(* Smallest meaningful contiguous computational unit of the kernel: the      *)
(* eight interleaved 14-round aese/aesmc chains that form the first AES-256  *)
(* counter-mode pass in the setup region (pc+0x90 .. pc+0x41c).  This is     *)
(* register-only: the eight counter blocks are taken as opaque inputs in     *)
(* Q0..Q7, the fifteen round keys rk0,rk1 come in Q26,Q27 and rk2..rk14 are  *)
(* reloaded in-region from the key schedule in memory at key_p (offsets      *)
(* 32..224).  The region ends at the round-13 aese of every block, just      *)
(* before the data-dependent tail branch; the final rk14 xor is folded into  *)
(* the subsequent eor3 with plaintext, so the raw Qi value here is exactly   *)
(* the pre-rk14-xor AES chain.  Each output therefore satisfies              *)
(* `word_xor (read Qi s) rk14 = word_reversefields 8 (aes256_cipher ...)`,   *)
(* i.e. AES256_CIPHER_RECONSTRUCT (proved in P2) applied verbatim.           *)
(*                                                                           *)
(* NB the eight blocks are FULLY INTERLEAVED instruction-by-instruction in   *)
(* the machine code (block3-r0, block4-r0, block2-r0, block0-r0, ...), so    *)
(* there is no shorter contiguous single-block range to carve out; the whole *)
(* 227-instruction region is the atomic AES unit.  It validates the AES      *)
(* bridge (14 aese / 13 aesmc + in-memory key reload) before any GHASH or    *)
(* ciphertext-memory complexity is added in later phases.                    *)
(* ========================================================================= *)

let AESV8_GCM_8X_ENC_256_WB_AES_SETUP = prove
 (`!b0 b1 b2 b3 b4 b5 b6 b7
     k0 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 k11 k12 k13 k14 key_p pc.
    ensures arm
      (\s. aligned_bytes_loaded s (word pc) aesv8_gcm_8x_enc_256_wb_mc /\
           read PC s = word (pc + 0x98) /\
           read X11 s = key_p /\
           read Q0 s = b0 /\ read Q1 s = b1 /\ read Q2 s = b2 /\
           read Q3 s = b3 /\ read Q4 s = b4 /\ read Q5 s = b5 /\
           read Q6 s = b6 /\ read Q7 s = b7 /\
           read Q26 s = k0 /\ read Q27 s = k1 /\
           read (memory :> bytes128 (word_add key_p (word 32)))  s = k2 /\
           read (memory :> bytes128 (word_add key_p (word 48)))  s = k3 /\
           read (memory :> bytes128 (word_add key_p (word 64)))  s = k4 /\
           read (memory :> bytes128 (word_add key_p (word 80)))  s = k5 /\
           read (memory :> bytes128 (word_add key_p (word 96)))  s = k6 /\
           read (memory :> bytes128 (word_add key_p (word 112))) s = k7 /\
           read (memory :> bytes128 (word_add key_p (word 128))) s = k8 /\
           read (memory :> bytes128 (word_add key_p (word 144))) s = k9 /\
           read (memory :> bytes128 (word_add key_p (word 160))) s = k10 /\
           read (memory :> bytes128 (word_add key_p (word 176))) s = k11 /\
           read (memory :> bytes128 (word_add key_p (word 192))) s = k12 /\
           read (memory :> bytes128 (word_add key_p (word 208))) s = k13 /\
           read (memory :> bytes128 (word_add key_p (word 224))) s = k14)
      (\s. read PC s = word (pc + 0x424) /\
           word_xor (read Q0 s) k14 =
           word_reversefields 8
            (aes256_cipher (word_reversefields 8 b0)
              (MAP (word_reversefields 8)
               [k0;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14])) /\
           word_xor (read Q1 s) k14 =
           word_reversefields 8
            (aes256_cipher (word_reversefields 8 b1)
              (MAP (word_reversefields 8)
               [k0;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14])) /\
           word_xor (read Q2 s) k14 =
           word_reversefields 8
            (aes256_cipher (word_reversefields 8 b2)
              (MAP (word_reversefields 8)
               [k0;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14])) /\
           word_xor (read Q3 s) k14 =
           word_reversefields 8
            (aes256_cipher (word_reversefields 8 b3)
              (MAP (word_reversefields 8)
               [k0;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14])) /\
           word_xor (read Q4 s) k14 =
           word_reversefields 8
            (aes256_cipher (word_reversefields 8 b4)
              (MAP (word_reversefields 8)
               [k0;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14])) /\
           word_xor (read Q5 s) k14 =
           word_reversefields 8
            (aes256_cipher (word_reversefields 8 b5)
              (MAP (word_reversefields 8)
               [k0;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14])) /\
           word_xor (read Q6 s) k14 =
           word_reversefields 8
            (aes256_cipher (word_reversefields 8 b6)
              (MAP (word_reversefields 8)
               [k0;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14])) /\
           word_xor (read Q7 s) k14 =
           word_reversefields 8
            (aes256_cipher (word_reversefields 8 b7)
              (MAP (word_reversefields 8)
               [k0;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14])))
      (MAYCHANGE [PC] ,,
       MAYCHANGE [Q0;Q1;Q2;Q3;Q4;Q5;Q6;Q7;Q19;Q26;Q27;Q28;Q30] ,,
       MAYCHANGE [events])`,
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC AESV8_GCM_8X_ENC_256_WB_EXEC (1--227) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[AES256_CIPHER_RECONSTRUCT]);;

(* ========================================================================= *)
(* P4 - GHASH single-fold / reduction bridge.                                *)
(*                                                                           *)
(* Structural finding (session 005, from objdump of the frozen .o):          *)
(* The x8 kernel is FULLY SOFTWARE-PIPELINED, exactly like its AES region:   *)
(* the GHASH pmull/pmull2/eor3/rev64 instructions are interleaved            *)
(* instruction-by-instruction with the AES aese/aesmc chain throughout the   *)
(* main loop (pc 0x498..0x9e4) AND the prepretail (0x9e8..0xeb4).  There is  *)
(* NO contiguous "one ghash block" PC range in those regions - the fold of   *)
(* the previous 8 blocks shares the same PC span as the AES of the next 8.   *)
(* The single-block GHASH folds do appear standalone in the TAIL cascade     *)
(* (.L256_enc_blocks_more_than_{7..1}), and the GF(2^128) MODULO reduction    *)
(* (Gueron prop-3, two pmull-by-0xC2..0) is a clean, contiguous, AES-free,    *)
(* register-in/register-out sequence that EVERY ghash path funnels through:  *)
(*                                                                           *)
(*   pc 0x11ac  ldr  d16,[x10]          ; load modulo const 0xC200..00        *)
(*   pc 0x11b0  ext  v21,v17,v17,#8                                           *)
(*   pc 0x11b4  eor3 v18,v18,v17,v19    ; MODULO - karatsuba tidy up          *)
(*   pc 0x11b8  pmull v29,v17.1d,v16.1d ; MODULO - top 64b align with mid     *)
(*   pc 0x11bc  eor3 v18,v18,v29,v21    ; MODULO - fold into mid              *)
(*   pc 0x11c0  pmull v17,v18.1d,v16.1d ; MODULO - mid 64b align with low     *)
(*   pc 0x11c4  ext  v21,v18,v18,#8                                           *)
(*   pc 0x11c8  eor3 v19,v19,v17,v21    ; MODULO - fold into low              *)
(*  (pc 0x11cc  ext  v19,v19,#8   +  0x11d0 rev64 v19  == byteswap128, the    *)
(*   store-order swap; excluded so the postcondition is reflection-free.)     *)
(*                                                                           *)
(* VERIFIED this session on server gcm8x: `ARM_STEPS_TAC EXEC (1--8)` over    *)
(* pc+0x11ac..pc+0x11cc runs clean in ~2s and yields, for accumulators       *)
(* p1=Q17(hi) p2=Q18(mid) p3=Q19(lo):                                        *)
(*   read Q19 = word_xor (word_xor p3 (word_pmul (LO Q18') w))               *)
(*                       (ext Q18')                                          *)
(*   where Q18' = p2 ^ p1 ^ p3 ^ word_pmul(LO p1) w ^ ext(p1),  w=0xC2..0,   *)
(*         ext x = word_subword (word_join x x) (64,128),                    *)
(*         LO x  = word_subword x (0,64).                                    *)
(* eor3 divergence handled transparently (opcode 0xce0.....; the stepper      *)
(* models it as a 3-way xor, no special tactic needed).                      *)
(*                                                                           *)
(* OPEN (deferred to P5/P6 with the loaded byteswap lemmas): this raw Q19 is  *)
(* NOT equal to `polyval_reduce_g2 p1 p2 p3` for ANY of the 6 argument        *)
(* permutations - CONFIRMED by a concrete-value BITBLAST oracle over all 6.   *)
(* Reason: the hardware Karatsuba accumulators entering the reduce are        *)
(* byte-reflected relative to the polyval convention (in x4 the operands are  *)
(* rev64'd GHASH blocks and the whole tag lives under `byteswap128`).  The    *)
(* clean identity therefore needs the reflection layer (byteswap128 /         *)
(* word_reversefields) threaded through, matching x4                          *)
(* aes_gcm_enc_kernel_x4_*.ml:1236-1291 where POLYVAL_REDUCE_G2 fires only    *)
(* after RECONSTRUCT_POLYVAL_REDUCE_G2 + a byteswap128 WORD_BLAST normaliser. *)
(* Once the reflection is pinned, close via                                  *)
(*   REWRITE_TAC[<swap-norm WORD_BLAST>] THEN                                 *)
(*   REWRITE_TAC[RECONSTRUCT_POLYVAL_REDUCE_G2] (after WORD_SUBWORD_XOR +     *)
(*     WORD_SIMPLE_SUBWORD_CONV normalisation) THEN REWRITE_TAC[POLYVAL_...]  *)
(* or, as a fallback, a single `CONV_TAC BITBLAST_RULE` on the reflection-    *)
(* corrected goal (x4 uses exactly this at reload_full.ml:1291; on the        *)
(* normalised 2KB goal it ran in ~4s this session).                          *)
(*                                                                           *)
(* The reduce region itself is proved outright below against ghash_reduce_raw; *)
(* only the ghash_reduce_raw -> polyval_reduce_g2 spec bridge (needing the      *)
(* reflection layer) is deferred to P5/P6.                                      *)
(* ========================================================================= *)

(* The exact register-out value the 8-step symbolic execution produces for    *)
(* Q19 (VERIFIED clean this session, before the store-order byteswap).  Stated *)
(* as its own definition so the ensures postcondition stays legible; p1/p2/p3  *)
(* are the incoming Q17(hi)/Q18(mid)/Q19(lo) Karatsuba accumulators, w=0xC2..0.*)
let ghash_reduce_raw = new_definition
 `ghash_reduce_raw p1 p2 p3 =
    let (LO:int128->int64) = \x. word_subword x (0,64) in
    let (ext:int128->int128) = \x. word_subword (word_join x x : int256) (64,128) in
    let w = word 13979173243358019584 : int64 in
    let q18 = word_xor (word_xor (word_xor (word_xor p2 p1) p3)
                                 (word_pmul (LO p1) w))
                       (ext p1) in
    word_xor (word_xor p3 (word_pmul (LO q18) w)) (ext q18) : int128`;;

(* The reduce region proved GENUINELY (no CHEAT) against its raw output          *)
(* `ghash_reduce_raw`, which is exactly what ARM_STEPS_TAC (1--8) emits for Q19.  *)
(* P5/P6 will bridge `ghash_reduce_raw p1 p2 p3` to `polyval_reduce_g2` under the *)
(* reflection layer (see the OPEN note above) once the byteswap relationship of   *)
(* the incoming accumulators is threaded in.                                      *)
let AESV8_GCM_8X_ENC_256_WB_GHASH_REDUCE = prove
 (`!p1 p2 p3 const_p pc.
    ensures arm
      (\s. aligned_bytes_loaded s (word pc) aesv8_gcm_8x_enc_256_wb_mc /\
           read PC s = word (pc + 0x1178) /\
           read X10 s = const_p /\
           read (memory :> bytes64 const_p) s = word 13979173243358019584 /\
           read Q17 s = p1 /\ read Q18 s = p2 /\ read Q19 s = p3)
      (\s. read PC s = word (pc + 0x1198) /\
           read Q19 s = ghash_reduce_raw p1 p2 p3)
      (MAYCHANGE [PC] ,,
       MAYCHANGE [Q16;Q17;Q18;Q19;Q21;Q29] ,,
       MAYCHANGE [events])`,
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC AESV8_GCM_8X_ENC_256_WB_EXEC (1--8) THEN
  ENSURES_FINAL_STATE_TAC THEN
  REWRITE_TAC[ghash_reduce_raw] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* P4 bridge (a): the reduce region's raw output IS the polyval reduction.   *)
(*                                                                           *)
(* CORRECTS the session-005 note above: `ghash_reduce_raw p1 p2 p3` is NOT   *)
(* reflection-entangled at the reduce boundary.  It equals the polyval       *)
(* reduction of the SAME accumulators with p2/p3 swapped:                    *)
(*                                                                           *)
(*     ghash_reduce_raw p1 p2 p3 = polyval_reduce_g2 p1 p3 p2                 *)
(*                                                                           *)
(* No byteswap128 / word_reversefields layer is required HERE (the store-    *)
(* order byteswap that session-005's oracle saw lives in the ext+rev64 at    *)
(* pc 0x11cc/0x11d0, which ghash_reduce_raw deliberately excludes).  The      *)
(* argument swap arises because the reduce loads Q17=hi, Q18=mid, Q19=lo,     *)
(* whereas polyval_reduce_g2's convention takes (p1,p2,p3) = (hi,lo,mid).     *)
(*                                                                           *)
(* A symbolic `CONV_TAC BITBLAST_RULE` on the bare identity FAILS because     *)
(* BITBLAST treats `word_pmul` opaquely and cannot see that the two outer     *)
(* pmul arguments are XOR-equal (they differ only by the associativity/order  *)
(* of a 5-term int64 XOR).  The fix is exactly POLYVAL_REDUCE_G2's own:       *)
(* abbreviate the inner pmul w1, push subwords through the XORs, then align   *)
(* the outer pmul argument with a WORD_BITWISE_RULE rewrite so it becomes a   *)
(* common subterm on both sides; WORD_BLAST then closes the rest.            *)
(* ------------------------------------------------------------------------- *)

let GHASH_REDUCE_RAW_IS_POLYVAL_G2 = prove
 (`!p1 p2 p3. ghash_reduce_raw p1 p2 p3 = polyval_reduce_g2 p1 p3 p2`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[ghash_reduce_raw; polyval_reduce_g2] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  ABBREV_TAC
   `w1 = (word_pmul:int64->int64->int128)
      (word_subword (p1:int128) (0,64)) (word 13979173243358019584)` THEN
  REWRITE_TAC[WORD_SUBWORD_XOR] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  ONCE_REWRITE_TAC[WORD_BITWISE_RULE
   `word_xor (word_xor (word_xor (word_xor (a:int64) b) c) d) e =
    word_xor (word_xor d e) (word_xor (word_xor b c) a)`] THEN
  CONV_TAC WORD_BLAST);;

(* ------------------------------------------------------------------------- *)
(* P4 bridge (b): the Karatsuba multiply-accumulate fold.                    *)
(*                                                                           *)
(* Given the three Karatsuba partial products of a single 128x128 carryless  *)
(* multiply  a * b  --  lo*lo, the cross term (a_lo^a_hi)*(b_lo^b_hi), and    *)
(* hi*hi -- feeding the reduce region in the Q17(hi)/Q18(mid)/Q19(lo) order   *)
(* the hardware uses (pmull -> lo lane, pmull2 -> hi lane, pmull of the       *)
(* eor'd halves -> cross/mid lane), the reduce computes exactly the polyval   *)
(* "dot" product  polyval_dot a b = prop3(pmul a b).                          *)
(*                                                                           *)
(*     ghash_reduce_raw <lo*lo> <cross> <hi*hi>  =  polyval_dot a b           *)
(*                                                                           *)
(* Proof chain: bridge (a) turns ghash_reduce_raw into polyval_reduce_g2      *)
(* (with the p2<->p3 swap that reorders cross/hi into g2's hi,lo,mid slots),  *)
(* POLYVAL_REDUCE_G2 rewrites that to polyval_reduce_prop3 of the reassembled *)
(* 256-bit product, and GSYM PMUL_KARATSUBA_JOIN collapses the three partial  *)
(* products back into the single word_pmul a b inside polyval_dot.  NB the    *)
(* two REWRITE_TAC calls must stay SEPARATE: folding POLYVAL_REDUCE_G2 into    *)
(* the bridge-(a) rewrite list makes it fire before the swap settles and the  *)
(* proof diverges.                                                           *)
(*                                                                           *)
(* This is the per-block fold primitive the main-loop / prepretail / tail     *)
(* bodies compose (P6): each GHASH block is `word_pmul (acc_xor_block)        *)
(* (h_power ...)`; the batched multi-block accumulation over v8..v15 then      *)
(* closes with the existing common/ lemma GHASH_POLYVAL_ACC_BATCHED (which    *)
(* already reduces `ghash_polyval_acc h a (CONS b bs)` to a prop3 of the      *)
(* pmul + ghash_wide sum), and NIST_DOT_IS_POLYVAL_DOT / nist_ghash bridge    *)
(* the polyval accumulator to the nist_ghash tag - exactly the x4 loop-body   *)
(* composition at reload_full.ml:1256-1275.                                   *)
(* ------------------------------------------------------------------------- *)

let GHASH_REDUCE_RAW_KARATSUBA_IS_DOT = prove
 (`!a b:int128.
    ghash_reduce_raw
      (word_pmul (word_subword a (0,64):int64)
                 (word_subword b (0,64):int64):int128)
      (word_pmul (word_xor (word_subword a (0,64):int64)
                           (word_subword a (64,64):int64))
                 (word_xor (word_subword b (0,64):int64)
                           (word_subword b (64,64):int64)):int128)
      (word_pmul (word_subword a (64,64):int64)
                 (word_subword b (64,64):int64):int128)
    = polyval_dot a b`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[GHASH_REDUCE_RAW_IS_POLYVAL_G2] THEN
  REWRITE_TAC[POLYVAL_REDUCE_G2; polyval_dot] THEN
  REWRITE_TAC[GSYM(REWRITE_RULE[LET_DEF;LET_END_DEF] PMUL_KARATSUBA_JOIN)]);;

(* ========================================================================= *)
(* P5 - Main-loop invariant (the software-pipelined core).                    *)
(*                                                                           *)
(* The x8 main loop (pc+0x498 .. back-edge b.lt pc+0x9e4 -> 0x498) is         *)
(* software-pipelined: iteration i GHASH-folds the PREVIOUS group of 8        *)
(* ciphertext blocks (blocks 8i..8i+7, held in v8..v15) while AES-producing   *)
(* and storing the NEXT group (blocks 8(i+1)..8(i+1)+7).  So at the loop TOP  *)
(* of iteration i the machine has STORED 8*(i+1) ciphertext blocks but only   *)
(* GHASHED 8*i of them - the lag the invariant must encode.                  *)
(*                                                                           *)
(* DIVERGENCE FROM x4 (session 007 direction call): the back-edge is a        *)
(* FLAG-CONDITIONAL pointer compare - `cmp x0,x5` (pc+0x978) sets the flags,  *)
(* `b.lt` (pc+0x9e4) branches back while x0 < x5 (signed).  x4 instead uses a *)
(* countdown register + `cbnz`, so it uses ENSURES_WHILE_UP_TAC.  Here we     *)
(* MUST use ENSURES_WHILE_PUP_TAC (the post-test "P" variant) and carry a     *)
(* flag-fact conjunct `q i s`.  On ARM `b.lt` is taken iff ~(NF <=> VF)       *)
(* (instruction.ml:568, Condition_LT), so the flag fact is                    *)
(*   (read NF s <=> read VF s) <=> (i = k)                                    *)
(* i.e. GE (fall through) exactly on the last iteration.  This is the ARM     *)
(* analogue of the x86 `(read ZF s <=> i = k)` PUP flag fact.                *)
(*                                                                           *)
(* This session (P5) proves init + back-edge + exit and CHEATs the 340-instr *)
(* body (P6).  Because this is a standalone loop lemma whose precondition IS  *)
(* the invariant at i=0 (at pc+0x498), the init subgoal is a reflexive        *)
(* 0-step ensures; the back-edge/exit subgoals only step the single b.lt      *)
(* (register/memory preserving) so every state conjunct passes through.       *)
(*                                                                           *)
(* SESSION 008 (P6, partial): stepped the full 339-instr body on server gcm8x  *)
(* with ghost values for v0..v15 and confirmed the invariant was INCOMPLETE.   *)
(* The loop is software-pipelined, so the SIMD blocks are loop-carried across  *)
(* the b.lt back-edge and MUST be pinned:                                      *)
(*   - v8..v15 = the PREVIOUS group's ciphertext (blocks 8i..8i+7), GHASH-folded *)
(*     this iteration; each is `word_xor (aes_ctr_block nonce rk (8i+j))         *)
(*     (inblock (8i+j))` (identical to the out-memory store form; store order    *)
(*     confirmed: stp q8,q9,[x2] puts q8 at 8(i+1)+0, ..., q15 at 8(i+1)+7).    *)
(*     Without these, `read Q19 s339` (the fold result the postcondition must    *)
(*     equal) is a word_pmul/word_xor over the UNPINNED ghosts q8,q9,... and the *)
(*     goal is unprovable.  NOW ADDED below (24 conjuncts: pre/inv/post).        *)
(*   - `8 * (k + 1) <= nb` antecedent ADDED: the 4 ciphertext stores            *)
(*     (stp q8..q15,[x2],#32 at 0x9bc..0x9dc) FAIL the stepper's                 *)
(*     "updates will not modify program code" check without a bound tying the   *)
(*     block count nb to the loop count k (max store byte = 128k+128 = 16*nb).  *)
(*     (This is the P9 nb-vs-k tie surfacing early.)                            *)
(* CONFIRMED-CORRECT invariant-at-(i+1) forms (goal conclusion matched verbatim *)
(* after stepping): X0/X2 128*((i+1)+1), Q30 index 8*(i+1)+13, Q19 byteswap128  *)
(* nist_ghash..(8*(i+1)), Q31, all key/htable/tag/ivec mem, out-forall bound,   *)
(* flag fact (NF<=>VF)<=>(i+1=k), PC pc+0x9e4.                                   *)
(* STILL TODO for the body (P6, next session): v0,v1,v2,v3,v4 are ALSO          *)
(* loop-carried (first body use is `aese vN,v26`, a READ) = pre-AES CTR         *)
(* keystream blocks for the group AES'd this iteration; v5,v6,v7 are computed   *)
(* fresh inside (first use `rev32 vN,v30`).  Their exact counter-index forms    *)
(* must be pinned (derive via XOR_AES256_CIPHER_RECONSTRUCT + the setup counter *)
(* bookkeeping) before the body's AES side can close.  init stays reflexive so  *)
(* adding them will not break it.                                              *)
(* ------------------------------------------------------------------------- *)
(* SESSION 011 body-stepping helpers.                                          *)
(*                                                                             *)
(* The main-loop body reloads 8 plaintext blocks with `ldp q_even,q_odd,       *)
(* [x0],#32` (steps 263/295/303/304).  Because X0 post-increments, the SECOND  *)
(* element of each later pair is read at `word_add (word_add in_p (word ...))  *)
(* (word 16)` where the offset arithmetic (e.g. `(128*(i+1)+64)+48`) is NOT    *)
(* reduced to the literal `128*(i+1)+112` that the input-block reads use.  The  *)
(* stepper's memory resolution needs a syntactic address match, so the load    *)
(* stays opaque (`read(memory..) s_prev`) and DISCARD_OLDSTATE drops the        *)
(* ciphertext-register fact.  (The very first ldp, blocks 0/1, resolves        *)
(* natively because X0 is the un-incremented base there.)                      *)
(*                                                                             *)
(* Fix, applied only at the incremented ldps (LDP_STEP4_TAC): re-derive the 8  *)
(* plaintext reads at the CURRENT state from the persistent quantified         *)
(* in-memory forall (INBLOCKS_TAC — the specific s0 facts get dropped, the     *)
(* forall does not), verbose-step (no auto-discard), FLATTEN the nested         *)
(* word_adds, NORMOFF the offset arithmetic to the literal form, resolve the   *)
(* now-matching memory reads, then discard old state.  NORMOFF_RULE reduces    *)
(* `word (a + c1 + c2 + ...)` offsets; is_inp_memfact selects the memory       *)
(* equations used to substitute the loads.  NSTEP is the ordinary per-step     *)
(* chain (flatten + NORMOFF + subword) for all other instructions.             *)
(* ------------------------------------------------------------------------- *)

let NORMOFF_RULE =
  CONV_RULE(ONCE_DEPTH_CONV(fun tm -> match tm with
      Comb(Const("word",_),_) ->
        (RAND_CONV(REWRITE_CONV[GSYM ADD_ASSOC] THENC DEPTH_CONV NUM_ADD_CONV)) tm
    | _ -> failwith "NORMOFF"));;

(* Selects ONLY the freshly re-derived input-block reads                       *)
(* (`read (memory :> bytesN ..) s = inblock <idx>`), which LDP_STEP4_TAC        *)
(* substitutes into the ldp 2nd-element load.  The RHS-variable-headed guard    *)
(* `is_var(fst(strip_comb rhs))` is essential: WITHOUT it this matched EVERY    *)
(* `read(memory..) s = v` fact, so REWRITE_RULE memfacts rewrote each READ-ONLY *)
(* key/mod/tag/ivec/htable fact BY ITSELF -> `v = v` -> `T`, silently deleting  *)
(* the ~30 read-only memory facts the postcondition needs (they are never       *)
(* regenerated, unlike the input reads which INBLOCKS_TAC re-asserts each call). *)
(* Input reads carry the abstract value `inblock j` (a var applied to args);    *)
(* all read-only facts carry constant-headed values (word_reversefields/word/…).*)
let is_inp_memfact th =
  match concl th with
    Comb(Comb(Const("=",_), Comb(Comb(Const("read",_),
      Comb(Comb(Const(":>",_),Const("memory",_)),_)), _)), rhs) ->
        is_var(fst(strip_comb rhs))
  | _ -> false;;

(* ------------------------------------------------------------------------- *)
(* REPLAY-PERFORMANCE (session 057): the per-step subword normalisation is     *)
(* O(n^2).  ASSUMPTION_STATE_UPDATE_TAC (common/components.ml:3341) re-stamps   *)
(* EVERY surviving assumption from s(n-1) to sN each step with its RHS          *)
(* UNCHANGED, so a fact already put in subword-normal form last step comes back *)
(* still-normal — yet the bare CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_    *)
(* CONV) below re-traverses all ~140 carried facts every step, rebuilding each  *)
(* as theorems, a redundant no-op.  Over a 139-step drive that is ~19k          *)
(* redundant deep-conv passes (the TAIL was ~2h; s057 STATE.md profiling).      *)
(*                                                                             *)
(* WORD_SIMPLE_SUBWORD_CONV (hol-light Library/words.ml:4566) can ONLY fire on  *)
(* a `word_subword _ (NUMERAL,NUMERAL)` subterm — its outer match failwith's    *)
(* otherwise.  So TOP_DEPTH_CONV of it on a term WITHOUT that shape returns      *)
(* REFL (CONV_RULE is then the identity).  SUBWORD_NORM_RULE guards the conv     *)
(* with a cheap short-circuiting find_term for exactly that shape: it is        *)
(* PROOF-PRESERVING — for every theorem `th` it returns exactly what            *)
(* `CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) th` returns (identical    *)
(* when the redex is present; th unchanged, = the conv's own no-op, when        *)
(* absent) — but it skips the expensive multi-rule traversal on the stable      *)
(* carried facts, restoring O(n).  Used by NSTEP / NSTEP_G / NSTEP_GP below.     *)
let has_word_subword_numpair =
  can (find_term (fun t -> match t with
      Comb(Comb(Const("word_subword",_),_),
           Comb(Comb(Const(",",_),Comb(Const("NUMERAL",_),_)),
                Comb(Const("NUMERAL",_),_))) -> true
    | _ -> false));;

let SUBWORD_NORM_RULE th =
  if has_word_subword_numpair (concl th)
  then CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) th
  else th;;

(* PERF (session 068): the same short-circuit idea as SUBWORD_NORM_RULE, applied to  *)
(* the word_add-nest flatten (WB_WADD_RULE / NSTEP_GP_WADD_RULE).  That REWRITE_RULE   *)
(* rewrites `word_add (word_add b (word m)) (word nn) -> word_add b (word(m+nn))`,     *)
(* which fires ONLY on a register-pointer fact carrying the doubly-nested word_add    *)
(* shape (produced by a post-increment ldr/str advancing X0/X2).  On EVERY other       *)
(* carried fact — the Q-register reads, the read-only key/mod/ivec/htable memory        *)
(* facts, the non-incrementing state facts — the redex is absent, so REWRITE_RULE       *)
(* still builds its net and TOP_DEPTH-traverses the whole term only to return it         *)
(* unchanged.  Guarding with a cheap short-circuiting find_term for exactly that redex   *)
(* is PROOF-PRESERVING (identical to the bare rule: unchanged when the shape is absent,  *)
(* the rule's own no-op; identical rewrite when present) yet skips the net-walk on the   *)
(* facts that can never match.  In the WB_TAIL drive the doubly-nested shape is present  *)
(* on ~0 of ~110 carried facts at any given step (X0/X2 offsets are normalised away by   *)
(* NORMOFF the same step), so this is nearly a full skip.  VALIDATED (session 068, warm   *)
(* s2n-wbtail): over the full WB_TAIL drive MAP_EVERY NSTEP_GP (10--136) from the SAME    *)
(* s9 set-point, old vs guarded give a BIT-IDENTICAL goal (sig len=4522863 hash=          *)
(* 151882239 both) and 127.3s->121.9s / 127.2s->122.1s (~4.2% / ~4.0%, ~5.2s), reproduced *)
(* twice.  Used by the guarded steppers below.                                            *)
let has_wadd_nest =
  can (find_term (fun t -> match t with
      Comb(Comb(Const("word_add",_),
             Comb(Comb(Const("word_add",_),_),
                  Comb(Const("word",_),_))),
           Comb(Const("word",_),_)) -> true
    | _ -> false));;

(* PERF (session 068): companion guard for NORMOFF_RULE, which is                        *)
(* CONV_RULE(ONCE_DEPTH_CONV ..) firing only on a `word (t)` subterm whose argument t is  *)
(* a sum (`_ + _`) it can renormalise — i.e. a not-yet-collapsed offset like              *)
(* `word (128 * (k+1) + 16 + 32)`.  On every fact WITHOUT such a `word(sum)` the           *)
(* ONCE_DEPTH_CONV still descends the whole term to find nothing.  has_word_of_sum is a    *)
(* cheap short-circuiting find_term for `word (_ + _)`; guarding NORMOFF with it is         *)
(* PROOF-PRESERVING (NORMOFF is a no-op on facts lacking `word(sum)`, exactly what the      *)
(* guard skips) and stacks on top of the has_wadd_nest guard.  VALIDATED (session 068,       *)
(* warm s2n-wbtail): guarding BOTH passes over the full (10--136) drive from the same s9     *)
(* set-point gives a BIT-IDENTICAL goal (sig len=4522863 hash=151882239) and 127.3s->121.2s /*)
(* 127.4s->121.4s (~4.8% / ~4.7%, ~6.1s), reproduced twice — ~0.9s beyond the WADD guard.   *)
let has_word_of_sum =
  can (find_term (fun t -> match t with
      Comb(Const("word",_), Comb(Comb(Const("+",_),_),_)) -> true
    | _ -> false));;

(* The word_add-nest flatten used by every per-step stepper (NSTEP/NSTEP_G/NSTEP_GP). *)
(* Lifted out so the guarded steppers can compose it with NORMOFF/SUBWORD in ONE       *)
(* RULE_ASSUM_TAC pass and skip it on the giant GHASH accumulators (see NSTEP_G).       *)
let WB_WADD_RULE = REWRITE_RULE[WORD_RULE
  `word_add (word_add b (word m)) (word nn):int64 = word_add b (word(m+nn))`];;

(* PERF (session 061): fold the three per-step RULE_ASSUM_TAC passes (word_add flatten,  *)
(* NORMOFF, SUBWORD_NORM) into ONE assumption-list traversal.  This is a pure refactor —  *)
(* the composed rule applied per fact is bit-identical to running the three rules in       *)
(* sequence — but it walks the assumption list once per step instead of three times.  No   *)
(* is_ghash_acc guard here: NSTEP drives SETUP, which carries NO large GHASH accumulators   *)
(* (measured: max fact ~1900 chars, <=2 Q19 facts through step 253), so there is nothing    *)
(* to skip; the win is purely the single traversal.  VALIDATED (session 061, warm           *)
(* s2n-wbtail): on the SAME SETUP state, old vs new NSTEP give a BIT-IDENTICAL goal over a   *)
(* block (41--120 hash=951408941 both), and block 41--200 21.9s->18.9s (~13.5%, ~3.0s),      *)
(* reproduced twice.                                                                         *)
let NSTEP n =
  ARM_STEPS_TAC AESV8_GCM_8X_ENC_256_WB_EXEC [n] THEN
  RULE_ASSUM_TAC(fun th -> SUBWORD_NORM_RULE (NORMOFF_RULE (WB_WADD_RULE th)));;

(* ------------------------------------------------------------------------- *)
(* GUARDED body stepper (session 021/022 — the Q19-fold breakthrough).        *)
(*                                                                           *)
(* NSTEP applies WORD_SIMPLE_SUBWORD_CONV after EVERY step.  The GHASH        *)
(* accumulators Q17/Q18/Q19 are word_join-headed Karatsuba lane sums, and     *)
(* that conv pushes word_subword INTO the joins, collapsing                   *)
(* `word_subword(word_join a b)(0,64)`->b etc.  This destroys the `LO p1` /   *)
(* `ext p1` structure `ghash_reduce_raw`'s definition needs, so the body-end  *)
(* Q19 residual can no longer be folded back to ghash_reduce_raw (the         *)
(* 5-session Q19 dead-end, sessions 017-021).                                 *)
(*                                                                           *)
(* NSTEP_G is NSTEP with the per-step subword conv SKIPPED on any assumption  *)
(* whose read-component is Q17/Q18/Q19, preserving the accumulators' ext/LO   *)
(* structure so the final Q19 stays ghash_reduce_raw-foldable.  The v0..v15   *)
(* counter/ciphertext facts (all other registers) are still normalised as     *)
(* before, so the cheap-close is unaffected.                                  *)
let is_ghash_acc th =
  let c = concl th in
  can (find_term (fun t -> match t with
      Comb(Const("read",_), r) ->
        (match r with
         | Const("Q17",_) | Const("Q18",_) | Const("Q19",_) -> true
         | _ -> false)
    | _ -> false)) c;;

(* PERF (session 061): same optimisation as NSTEP_GP — fold the three per-step        *)
(* RULE_ASSUM_TAC passes (word_add flatten, NORMOFF, SUBWORD_NORM) into ONE, and        *)
(* extend the is_ghash_acc (Q17/18/19) guard — previously on the subword pass only —    *)
(* to ALSO skip the word_add flatten and NORMOFF on the giant GHASH accumulators. Those *)
(* two passes are identity on the word_join/word_subword accumulator terms (word_add    *)
(* rule fires only on register-pointer shape; NORMOFF only on word(c1+c2+..) offsets),  *)
(* so skipping them there is proof-preserving while avoiding an O(term-size) traversal  *)
(* of the accumulator every step.  VALIDATED (session 061, warm s2n-wbtail): on the     *)
(* SAME MAIN_LOOP-body state, old vs new NSTEP_G give a BIT-IDENTICAL goal over a drive  *)
(* block (early block 41--55 hash=980081400 both; heavy block 260--274 hash=191483695   *)
(* both), and it is measurably faster — early block 41--70 7.42s->5.85s (~21%),          *)
(* heavy-accumulator block 260--289 14.35s->11.58s (~19%, 2.8s), each reproduced twice.  *)
(* MAIN_LOOP is the file's largest drive (1--339), so the whole-body speedup is ~19%.    *)
let NSTEP_G n =
  ARM_STEPS_TAC AESV8_GCM_8X_ENC_256_WB_EXEC [n] THEN
  RULE_ASSUM_TAC(fun th ->
    if is_ghash_acc th then th
    else SUBWORD_NORM_RULE (NORMOFF_RULE (WB_WADD_RULE th)));;

let INBLOCKS_TAC sname =
  let sv = mk_var(sname,`:armstate`) in
  let concl_tm = subst[sv,`s:armstate`]
   `read (memory :> bytes128 (word_add in_p (word (128 * (i + 1))))) s =
    inblock (8 * (i + 1)) /\
    read (memory :> bytes128 (word_add in_p (word (128 * (i + 1) + 16)))) s =
    inblock (8 * (i + 1) + 1) /\
    read (memory :> bytes128 (word_add in_p (word (128 * (i + 1) + 32)))) s =
    inblock (8 * (i + 1) + 2) /\
    read (memory :> bytes128 (word_add in_p (word (128 * (i + 1) + 48)))) s =
    inblock (8 * (i + 1) + 3) /\
    read (memory :> bytes128 (word_add in_p (word (128 * (i + 1) + 64)))) s =
    inblock (8 * (i + 1) + 4) /\
    read (memory :> bytes128 (word_add in_p (word (128 * (i + 1) + 80)))) s =
    inblock (8 * (i + 1) + 5) /\
    read (memory :> bytes128 (word_add in_p (word (128 * (i + 1) + 96)))) s =
    inblock (8 * (i + 1) + 6) /\
    read (memory :> bytes128 (word_add in_p (word (128 * (i + 1) + 112)))) s =
    inblock (8 * (i + 1) + 7)` in
  SUBGOAL_THEN concl_tm STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE
     `128 * (i + 1) + 16 = 16 * (8 * (i + 1) + 1) /\
      128 * (i + 1) + 32 = 16 * (8 * (i + 1) + 2) /\
      128 * (i + 1) + 48 = 16 * (8 * (i + 1) + 3) /\
      128 * (i + 1) + 64 = 16 * (8 * (i + 1) + 4) /\
      128 * (i + 1) + 80 = 16 * (8 * (i + 1) + 5) /\
      128 * (i + 1) + 96 = 16 * (8 * (i + 1) + 6) /\
      128 * (i + 1) + 112 = 16 * (8 * (i + 1) + 7)`] THEN
    REWRITE_TAC[ARITH_RULE `128 * a = 16 * 8 * a`] THEN
    REPEAT CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    (* PERF (session 074): the block-index obligation is `8*(i+1)+b < nb`, closed  *)
    (* by just {i < k, 8*(k+1) <= nb}.  ASM_ARITH_TAC here MP_TAC'd EVERY hyp into  *)
    (* the goal — at the LDP store steps (295/303/304) the assumption list carries  *)
    (* the ~163k-char Q17/Q18/Q19 GHASH accumulators, so each INBLOCKS call spent    *)
    (* ~24s dragging+scanning the giants (3 calls = ~76s, 36% of the body drive).    *)
    (* Targeted UNDISCH of exactly the two needed hyps + bare ARITH_TAC is the same  *)
    (* idiom the body's flag-close already uses (see the flag_arith note below); it  *)
    (* closes in ~1.2s (proof-preserving: goal signature bit-identical).  Whole      *)
    (* MAIN_LOOP 342s->270s (-21%), measured twice on warm s2n-wbtail.               *)
    UNDISCH_TAC `8 * (k + 1) <= nb` THEN UNDISCH_TAC `(i:num) < k` THEN ARITH_TAC;
    ALL_TAC];;

let LDP_STEP4_TAC n =
  let sprev = "s"^string_of_int (n-1) in
  let sn = "s"^string_of_int n in
  INBLOCKS_TAC sprev THEN
  ARM_VERBOSE_STEP_TAC AESV8_GCM_8X_ENC_256_WB_EXEC sn THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
    `word_add (word_add b (word m)) (word nn):int64 = word_add b (word(m+nn))`]) THEN
  RULE_ASSUM_TAC NORMOFF_RULE THEN
  (fun (asl,w as gl) ->
     let memfacts = filter is_inp_memfact (map snd asl) in
     RULE_ASSUM_TAC(REWRITE_RULE memfacts) gl) THEN
  RULE_ASSUM_TAC SUBWORD_NORM_RULE THEN
  DISCARD_OLDSTATE_TAC sn;;

(* ------------------------------------------------------------------------- *)
(* Flag-close lemmas for the main-loop body (blocker C, session 017).        *)
(*                                                                           *)
(* The loop back-edge is a signed pointer compare `cmp x0,x5; b.lt` at       *)
(* pc 0x978/0x9e4: X0 = in_p + 128*(i+2) (four `ldp [x0],#32` past the loop  *)
(* top), X5 = end_p.  After the cheap-close ASM_REWRITE, the invariant's     *)
(* flag conjunct q(i+1) has been reduced to the raw NF!=VF biconditional     *)
(* over `word_sub X0 end_p`.  BRIDGE_GE recognises that biconditional as the *)
(* signed GE `ival end_p <= ival X0`; IV_ADD linearises each additive ival   *)
(* under the buffer-end no-wrap bound `val in_p + 128*(k+1) < 2^63`; FLAG_LEM *)
(* then reduces the whole thing to `i + 1 = k` using the body hyp `i < k`.   *)
(* The no-wrap bound is supplied by MAIN_LOOP's new end_p antecedent.        *)

let BRIDGE_GE = prove
 (`!a c:int64.
     ((ival (word_sub a c) < &0) <=>
      ~(ival a - ival c = ival (word_sub a c))) <=> ival c <= ival a`,
  REPEAT GEN_TAC THEN BITBLAST_TAC);;

let IV_ADD = prove
 (`!(in_p:int64) off.
     val in_p + off < 2 EXP 63
     ==> ival(word_add in_p (word off)) = &(val in_p + off)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `val(word_add (in_p:int64) (word off)) = val in_p + off`
    ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
    CONV_TAC MOD_DOWN_CONV THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[INT_IVAL; DIMINDEX_64] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[INT_OF_NUM_POW; INT_OF_NUM_LT] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC);;

let FLAG_LEM = prove
 (`!(in_p:int64) i k.
     i < k /\ val in_p + 128 * (k + 1) < 2 EXP 63
     ==> ((ival (word_sub (word_add in_p (word (128 * (i + 1) + 128)))
                          (word_add in_p (word (128 * (k + 1))))) < &0
           <=> ~(ival (word_add in_p (word (128 * (i + 1) + 128))) -
                 ival (word_add in_p (word (128 * (k + 1)))) =
                 ival (word_sub (word_add in_p (word (128 * (i + 1) + 128)))
                                (word_add in_p (word (128 * (k + 1)))))))
          <=> (i + 1 = k))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[BRIDGE_GE] THEN
  MP_TAC(SPECL [`in_p:int64`; `128 * (i + 1) + 128`] IV_ADD) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(SPECL [`in_p:int64`; `128 * (k + 1)`] IV_ADD) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[INT_OF_NUM_LE] THEN ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* SETUP branch-discharge lemmas (P7, session 032).                          *)
(*                                                                           *)
(* The pipeline-fill setup has two `cmp x0,x5; b.ge` guards — the tail check *)
(* at 0x420/0x424 and the prepretail check at 0x458/0x494 — both comparing   *)
(* the running input pointer X0 against the loop-end pointer                  *)
(*   X5 = ((byte_len DIV 8) - 1) & ~127  +  in_p                             *)
(* (hardware: sub x5,x5,#1; and x5,x5,#0xffffffffffffff80; add x5,x5,x0 at    *)
(* 0x44/0x48/0x4c, with x5 initialised to x9 = word(byte_len DIV 8)).  Both   *)
(* guards must fall through (b.ge NOT taken) when k >= 1, i.e. when more than *)
(* one 8-block group remains.                                                 *)
(*                                                                           *)
(* X5_END_PTR: under block-aligned byte_len = 128*nb with nb = 8*(k+2), the   *)
(* round-down-to-128 mask collapses X5 to the loop-end pointer end_p =        *)
(* in_p + 128*(k+1) — the SAME end_p MAIN_LOOP's antecedent pins.  The key    *)
(* arithmetic: (16*nb - 1) & ~127 = 128*(k+1) because 16*nb = 128*(k+2) =     *)
(* 128*(k+1) + 128, so (128*(k+1)+127) rounds down to 128*(k+1).  This        *)
(* CONFIRMS the k = nb DIV 8 - 2 accounting (the last 8-group is drained by   *)
(* prepretail, hence -2 not -1). Proof via WORD_AND_NOT_MASK_WORD (the        *)
(* clear-low-7-bits lemma) + VAL_WORD_SUB_CASES.                              *)
let X5_END_PTR = prove
 (`!(in_p:int64) k.
     16 * (8 * (k + 2)) < 2 EXP 64
     ==> word_add
           (word_and (word_sub (word (16 * (8 * (k + 2)))) (word 1))
                     (word 18446744073709551488))
           in_p =
         word_add in_p (word (128 * (k + 1)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `val(word_sub (word (16 * (8 * (k + 2)))) (word 1):int64) = 128 * (k + 1) + 127`
   ASSUME_TAC THENL
   [SUBGOAL_THEN `val(word (16 * (8 * (k + 2))):int64) = 16 * (8 * (k + 2))`
      ASSUME_TAC THENL
     [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[VAL_WORD_SUB_CASES; VAL_WORD_1] THEN
    COND_CASES_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[WORD_ADD_SYM] THEN AP_TERM_TAC THEN
  SUBGOAL_THEN
   `word_and (word_sub (word (16 * (8 * (k + 2)))) (word 1))
             (word 18446744073709551488):int64 =
    word(2 EXP 7 * (val(word_sub (word (16 * (8 * (k + 2)))) (word 1):int64)
                    DIV 2 EXP 7))`
   SUBST1_TAC THENL
   [SUBGOAL_THEN `word 18446744073709551488:int64 = word_not(word(2 EXP 7 - 1))`
      SUBST1_TAC THENL
     [CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_BLAST; ALL_TAC] THEN
    REWRITE_TAC[WORD_AND_NOT_MASK_WORD];
    ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN
    REWRITE_TAC[ARITH_RULE `128 * (k + 1) + 127 = (k + 1) * 2 EXP 7 + 127`] THEN
    SIMP_TAC[DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC]);;

(* X5_END_PTR_GEN (session 082): the g-general round-down lemma.  For ANY     *)
(* nb>=1 the mask-off-low-7-bits of (16*nb - 1) yields 128 * groups where      *)
(* groups = (nb-1) DIV 8 — the last-full-8-group pointer.  Subsumes X5_END_PTR *)
(* (nb = 8*(k+2) => (nb-1) DIV 8 = k+1) and WB_X5_GROUPS0 (nb<=8 => groups=0).  *)
(* Needed by the loop_count>=1 reassembly leg where rem may be 1..8 (not just 8).*)
let X5_END_PTR_GEN = prove
 (`!(in_p:int64) nb.
     1 <= nb /\ 16 * nb < 2 EXP 64
     ==> word_add
           (word_and (word_sub (word ((128 * nb) DIV 8)) (word 1))
                     (word 18446744073709551488))
           in_p =
         word_add in_p (word (128 * ((nb - 1) DIV 8)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(128 * nb) DIV 8 = 16 * nb` SUBST1_TAC THENL
   [ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `val(word_sub (word (16 * nb)) (word 1):int64) = 16 * nb - 1`
   ASSUME_TAC THENL
   [SUBGOAL_THEN `val(word (16 * nb):int64) = 16 * nb` ASSUME_TAC THENL
     [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[VAL_WORD_SUB_CASES; VAL_WORD_1] THEN
    COND_CASES_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[WORD_ADD_SYM] THEN AP_TERM_TAC THEN
  SUBGOAL_THEN
   `word_and (word_sub (word (16 * nb)) (word 1))
             (word 18446744073709551488):int64 =
    word(2 EXP 7 * (val(word_sub (word (16 * nb)) (word 1):int64)
                    DIV 2 EXP 7))`
   SUBST1_TAC THENL
   [SUBGOAL_THEN `word 18446744073709551488:int64 = word_not(word(2 EXP 7 - 1))`
      SUBST1_TAC THENL
     [CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_BLAST; ALL_TAC] THEN
    REWRITE_TAC[WORD_AND_NOT_MASK_WORD];
    ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN
    REWRITE_TAC[ARITH_RULE `2 EXP 7 = 128`] THEN
    SUBGOAL_THEN `16 * nb - 1 = 128 * ((nb-1) DIV 8) + (16 * ((nb-1) MOD 8) + 15)`
      SUBST1_TAC THENL
     [MP_TAC(SPECL [`nb - 1`; `8`] DIVISION) THEN REWRITE_TAC[ARITH_EQ] THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `128 * ((nb-1) DIV 8) = ((nb-1) DIV 8) * 128` SUBST1_TAC THENL
     [ARITH_TAC; ALL_TAC] THEN
    SIMP_TAC[DIV_MULT_ADD; ARITH_EQ] THEN
    SUBGOAL_THEN `(16 * ((nb-1) MOD 8) + 15) DIV 128 = 0` SUBST1_TAC THENL
     [REWRITE_TAC[DIV_EQ_0; ARITH_EQ] THEN
      MP_TAC(SPECL [`nb - 1`; `8`] DIVISION) THEN ARITH_TAC;
      ARITH_TAC]]);;

(* end_p = in_p + 128*(k+1) is strictly ABOVE in_p (signed), since 128*(k+1)  *)
(* >= 128 > 0 and there is no signed wrap.  So the `cmp x0,x5; b.ge` with     *)
(* X0 = in_p (or in_p+128) at the guards does NOT take the branch.            *)
let SETUP_GE_FALSE = prove
 (`!(in_p:int64) k.
     val in_p + 128 * (k + 1) < 2 EXP 63
     ==> ~(ival (word_add in_p (word (128 * (k + 1)))) <= ival in_p)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`in_p:int64`; `128 * (k + 1)`] IV_ADD) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `ival(in_p:int64) = &(val in_p)` ASSUME_TAC THENL
   [REWRITE_TAC[INT_IVAL; DIMINDEX_64] THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN
    POP_ASSUM MP_TAC THEN REWRITE_TAC[INT_OF_NUM_POW; INT_OF_NUM_LT] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN SUBST_ALL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[INT_OF_NUM_LE]) THEN ASM_ARITH_TAC);;

(* Collapse the first-guard conditional (the exact NF!=VF biconditional the   *)
(* stepper emits for `cmp x0,x5; b.ge` with X0 = in_p) to F, so the           *)
(* conditional PC resolves to the fall-through.  X5 here is the raw hardware  *)
(* form ((128*nb DIV 8) - 1) & ~127 + in_p; the lemma normalises it to end_p  *)
(* via X5_END_PTR and finishes with BRIDGE_GE + SETUP_GE_FALSE.               *)
let SETUP_BRANCH_COND_FALSE = prove
 (`!(in_p:int64) k nb.
     8 * (k + 2) = nb /\
     val in_p + 128 * (k + 1) < 2 EXP 63
     ==> ((ival (word_sub in_p
                  (word_add
                    (word_and (word_sub (word ((128 * nb) DIV 8)) (word 1))
                              (word 18446744073709551488))
                    in_p)) < &0 <=>
           ~(ival in_p -
             ival (word_add
                    (word_and (word_sub (word ((128 * nb) DIV 8)) (word 1))
                              (word 18446744073709551488))
                    in_p) =
             ival (word_sub in_p
                    (word_add
                      (word_and (word_sub (word ((128 * nb) DIV 8)) (word 1))
                                (word 18446744073709551488))
                      in_p)))) <=> F)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `word_add
      (word_and (word_sub (word ((128 * nb) DIV 8)) (word 1))
                (word 18446744073709551488))
      in_p =
    word_add in_p (word (128 * (k + 1))):int64`
   SUBST1_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[ARITH_RULE `(128 * (8 * (k + 2))) DIV 8 = 16 * 8 * (k + 2)`] THEN
    MATCH_MP_TAC X5_END_PTR THEN
    MP_TAC(SPEC `in_p:int64` VAL_BOUND_64) THEN
    UNDISCH_TAC `val(in_p:int64) + 128 * (k + 1) < 2 EXP 63` THEN ARITH_TAC;
    REWRITE_TAC[BRIDGE_GE] THEN
    REWRITE_TAC[MATCH_MP SETUP_GE_FALSE (ASSUME
      `val(in_p:int64) + 128 * (k + 1) < 2 EXP 63`)]]);;

(* Second-guard variant (session 033): the prepretail-check b.ge@0x494 fires   *)
(* AFTER the 4 ldp[x0],#32 plaintext loads, so the running pointer is          *)
(* X0 = in_p + 128 (one 8-block group consumed) — NOT in_p.  end_p is strictly *)
(* above in_p+128 (signed) since 128*(k+1) > 128 for k>=1, so the branch again *)
(* falls through.  SETUP_GE_FALSE_2 is the in_p+128 analogue of SETUP_GE_FALSE;*)
(* SETUP_BRANCH_COND_FALSE_2 collapses the exact NF!=VF biconditional the       *)
(* stepper emits at step 282 to F.                                             *)
let SETUP_GE_FALSE_2 = prove
 (`!(in_p:int64) k.
     ~(k = 0) /\ val in_p + 128 * (k + 1) < 2 EXP 63
     ==> ~(ival (word_add in_p (word (128 * (k + 1)))) <=
           ival (word_add in_p (word 128)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`in_p:int64`; `128 * (k + 1)`] IV_ADD) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`in_p:int64`; `128`] IV_ADD) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN SUBST_ALL_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[INT_OF_NUM_LE]) THEN ASM_ARITH_TAC);;

let SETUP_BRANCH_COND_FALSE_2 = prove
 (`!(in_p:int64) k nb.
     ~(k = 0) /\ 8 * (k + 2) = nb /\
     val in_p + 128 * (k + 1) < 2 EXP 63
     ==> ((ival (word_sub (word_add in_p (word 128))
                  (word_add
                    (word_and (word_sub (word ((128 * nb) DIV 8)) (word 1))
                              (word 18446744073709551488))
                    in_p)) < &0 <=>
           ~(ival (word_add in_p (word 128)) -
             ival (word_add
                    (word_and (word_sub (word ((128 * nb) DIV 8)) (word 1))
                              (word 18446744073709551488))
                    in_p) =
             ival (word_sub (word_add in_p (word 128))
                    (word_add
                      (word_and (word_sub (word ((128 * nb) DIV 8)) (word 1))
                                (word 18446744073709551488))
                      in_p)))) <=> F)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `word_add
      (word_and (word_sub (word ((128 * nb) DIV 8)) (word 1))
                (word 18446744073709551488))
      in_p =
    word_add in_p (word (128 * (k + 1))):int64`
   SUBST1_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[ARITH_RULE `(128 * (8 * (k + 2))) DIV 8 = 16 * 8 * (k + 2)`] THEN
    MATCH_MP_TAC X5_END_PTR THEN
    MP_TAC(SPEC `in_p:int64` VAL_BOUND_64) THEN
    UNDISCH_TAC `val(in_p:int64) + 128 * (k + 1) < 2 EXP 63` THEN ARITH_TAC;
    REWRITE_TAC[BRIDGE_GE] THEN
    REWRITE_TAC[MATCH_MP SETUP_GE_FALSE_2 (CONJ (ASSUME `~(k = 0)`) (ASSUME
      `val(in_p:int64) + 128 * (k + 1) < 2 EXP 63`))]]);;

(* ------ g-general SETUP branch discharges (session 082) --------------------- *)
(* The g>=2 reassembly sub-leg reuses WB_SETUP's drive but with rem in 1..8      *)
(* (8*(k+1) < nb <= 8*(k+2)) instead of the rem=8-only 8*(k+2)=nb.  The two      *)
(* main-loop-skip guard discharges must then use groups=(nb-1)DIV8=k+1 (via      *)
(* X5_END_PTR_GEN) rather than the exact-multiple X5_END_PTR.  SETUP_X5_END_GEN   *)
(* is the round-down=end_p reduction; BRANCH_COND_FALSE{,_2}_GEN collapse the     *)
(* two b.ge biconditionals to F for the fall-through (groups>=2).                 *)
(* The generalized round-down = end_p reduction (verified interactively s082). *)
let SETUP_X5_END_GEN = prove
 (`!(in_p:int64) k nb.
     8 * (k + 1) < nb /\ nb <= 8 * (k + 2) /\
     val in_p + 128 * (k + 1) < 2 EXP 63
     ==> word_add
           (word_and (word_sub (word ((128 * nb) DIV 8)) (word 1))
                     (word 18446744073709551488)) in_p =
         word_add in_p (word (128 * (k + 1)):int64)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`in_p:int64`; `nb:num`] X5_END_PTR_GEN) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [ASM_ARITH_TAC;
      UNDISCH_TAC `nb <= 8 * (k + 2)` THEN
      UNDISCH_TAC `val(in_p:int64) + 128 * (k + 1) < 2 EXP 63` THEN ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(nb - 1) DIV 8 = k + 1` SUBST1_TAC THENL
   [ASM_ARITH_TAC; DISCH_THEN ACCEPT_TAC]);;

let SETUP_BRANCH_COND_FALSE_GEN = prove
 (`!(in_p:int64) k nb.
     8 * (k + 1) < nb /\ nb <= 8 * (k + 2) /\
     val in_p + 128 * (k + 1) < 2 EXP 63
     ==> ((ival (word_sub in_p
                  (word_add
                    (word_and (word_sub (word ((128 * nb) DIV 8)) (word 1))
                              (word 18446744073709551488))
                    in_p)) < &0 <=>
           ~(ival in_p -
             ival (word_add
                    (word_and (word_sub (word ((128 * nb) DIV 8)) (word 1))
                              (word 18446744073709551488))
                    in_p) =
             ival (word_sub in_p
                    (word_add
                      (word_and (word_sub (word ((128 * nb) DIV 8)) (word 1))
                                (word 18446744073709551488))
                      in_p)))) <=> F)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[SETUP_X5_END_GEN] THEN
  REWRITE_TAC[BRIDGE_GE] THEN
  REWRITE_TAC[MATCH_MP SETUP_GE_FALSE (ASSUME
    `val(in_p:int64) + 128 * (k + 1) < 2 EXP 63`)]);;

let SETUP_BRANCH_COND_FALSE_2_GEN = prove
 (`!(in_p:int64) k nb.
     ~(k = 0) /\ 8 * (k + 1) < nb /\ nb <= 8 * (k + 2) /\
     val in_p + 128 * (k + 1) < 2 EXP 63
     ==> ((ival (word_sub (word_add in_p (word 128))
                  (word_add
                    (word_and (word_sub (word ((128 * nb) DIV 8)) (word 1))
                              (word 18446744073709551488))
                    in_p)) < &0 <=>
           ~(ival (word_add in_p (word 128)) -
             ival (word_add
                    (word_and (word_sub (word ((128 * nb) DIV 8)) (word 1))
                              (word 18446744073709551488))
                    in_p) =
             ival (word_sub (word_add in_p (word 128))
                    (word_add
                      (word_and (word_sub (word ((128 * nb) DIV 8)) (word 1))
                                (word 18446744073709551488))
                      in_p)))) <=> F)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[SETUP_X5_END_GEN] THEN
  REWRITE_TAC[BRIDGE_GE] THEN
  REWRITE_TAC[MATCH_MP SETUP_GE_FALSE_2 (CONJ (ASSUME `~(k = 0)`) (ASSUME
    `val(in_p:int64) + 128 * (k + 1) < 2 EXP 63`))]);;

(* SETUP_BRANCH_COND_TRUE_2: the 2nd setup guard (b.ge@0x49c, cmp with        *)
(* X0 = word_add in_p (word 128) after consuming one 8-group) is TAKEN for    *)
(* groups=1 (k=0): round-down end_p = word_add in_p (word(128*(k+1))) =         *)
(* in_p+128 at k=0, so X0 = end_p and b.ge collapses to T -> PC = 0x9f0        *)
(* (PREPRETAIL).  Mirror of WB_BRANCH_COND_TRUE (1st guard) for the 2nd guard.  *)
let SETUP_BRANCH_COND_TRUE_2 = prove
 (`!(in_p:int64) k nb.
     k = 0 /\ 8 * (k + 1) < nb /\ nb <= 8 * (k + 2) /\
     val in_p + 128 * (k + 1) < 2 EXP 63
     ==> ((ival (word_sub (word_add in_p (word 128))
                  (word_add
                    (word_and (word_sub (word ((128 * nb) DIV 8)) (word 1))
                              (word 18446744073709551488))
                    in_p)) < &0 <=>
           ~(ival (word_add in_p (word 128)) -
             ival (word_add
                    (word_and (word_sub (word ((128 * nb) DIV 8)) (word 1))
                              (word 18446744073709551488))
                    in_p) =
             ival (word_sub (word_add in_p (word 128))
                    (word_add
                      (word_and (word_sub (word ((128 * nb) DIV 8)) (word 1))
                                (word 18446744073709551488))
                      in_p)))) <=> T)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[SETUP_X5_END_GEN] THEN
  ASM_REWRITE_TAC[ARITH_RULE `128 * (0 + 1) = 128`] THEN
  REWRITE_TAC[WORD_SUB_REFL; INT_SUB_REFL; IVAL_WORD_0] THEN
  INT_ARITH_TAC);;


(* SETUP-specific input-block re-derivation and ldp stepper.  In the setup    *)
(* the 8 plaintext blocks live at in_p + 16*j (j=0..7) — NOT the loop body's  *)
(* 128*(i+1)+off.  SETUP_INBLOCKS_TAC re-asserts all 8 reads at state `sname` *)
(* from the persistent quantified input-forall; LDP_SETUP_TAC is LDP_STEP4    *)
(* with that variant (needed for the post-incremented ldp [x0],#32 2nd loads).*)
let SETUP_INBLOCKS_TAC sname =
  let sv = mk_var(sname,`:armstate`) in
  let concl_tm = subst[sv,`s:armstate`]
   `read (memory :> bytes128 (word_add in_p (word (16 * 0)))) s = inblock 0 /\
    read (memory :> bytes128 (word_add in_p (word (16 * 1)))) s = inblock 1 /\
    read (memory :> bytes128 (word_add in_p (word (16 * 2)))) s = inblock 2 /\
    read (memory :> bytes128 (word_add in_p (word (16 * 3)))) s = inblock 3 /\
    read (memory :> bytes128 (word_add in_p (word (16 * 4)))) s = inblock 4 /\
    read (memory :> bytes128 (word_add in_p (word (16 * 5)))) s = inblock 5 /\
    read (memory :> bytes128 (word_add in_p (word (16 * 6)))) s = inblock 6 /\
    read (memory :> bytes128 (word_add in_p (word (16 * 7)))) s = inblock 7` in
  SUBGOAL_THEN concl_tm STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC];;

let LDP_SETUP_TAC n =
  let sprev = "s"^string_of_int (n-1) in
  let sn = "s"^string_of_int n in
  SETUP_INBLOCKS_TAC sprev THEN
  ARM_VERBOSE_STEP_TAC AESV8_GCM_8X_ENC_256_WB_EXEC sn THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
    `word_add (word_add b (word m)) (word nn):int64 = word_add b (word(m+nn))`]) THEN
  RULE_ASSUM_TAC NORMOFF_RULE THEN
  (fun (asl,w as gl) ->
     (* Normalize the SETUP input memfacts so their addresses MATCH the ldp     *)
     (* reads: reduce `16*j`->literal (NUM_MULT_CONV) and collapse              *)
     (* `word_add in_p (word 0)`->in_p (WORD_ADD_0).  Without this the block-0  *)
     (* ldp read (at BARE `in_p`) fails to match SETUP_INBLOCKS_TAC's memfact   *)
     (* address `word_add in_p (word (16*0))`, so that load stays opaque        *)
     (* (`read Q8 s = read(memory:>bytes128 in_p) s_prev`) and DISCARD_OLDSTATE *)
     (* drops the register fact.  SESSION 035: this LOAD-side mismatch (NOT the *)
     (* stp store, as s034 wrongly diagnosed) is why Q8..Q15 were lost — Q8 is  *)
     (* already absent at s255 (right after the first ldp@0x428), BEFORE any    *)
     (* store.  With the norm, all 8 ciphertext regs survive to s282 (validated *)
     (* /tmp/s035_probe4).                                                      *)
     let norm th =
       REWRITE_RULE[WORD_ADD_0]
         (try CONV_RULE(TOP_DEPTH_CONV NUM_MULT_CONV) th with _ -> th) in
     let memfacts = map norm (filter is_inp_memfact (map snd asl)) in
     RULE_ASSUM_TAC(REWRITE_RULE memfacts) gl) THEN
  RULE_ASSUM_TAC SUBWORD_NORM_RULE THEN
  DISCARD_OLDSTATE_TAC sn;;

(* ------------------------------------------------------------------------- *)
(* GF(2)-linearity (additivity over word_xor) of the reduction primitives.    *)
(*                                                                           *)
(* Both polyval_reduce_prop3 and ghash_reduce_raw are compositions of         *)
(* GF(2)-linear word ops (word_subword, word_pmul BY A CONSTANT, word_xor,    *)
(* word_join), hence additive.  These are the KEY lemmas (session 025,        *)
(* advisor-directed route) that let the pipelined-GHASH Q19 fold DISTRIBUTE   *)
(* the summed-lane hardware reduce over the 8 in-flight blocks, so each block *)
(* individually fires GHASH_REDUCE_RAW_KARATSUBA_IS_DOT — replacing the       *)
(* dead-end byteswap128(prop3 A) = prop3 B lane-match (sessions 020-024).      *)
(*                                                                           *)
(* PROOF RECIPE (the crux — prior sessions failed because WORD_BITWISE_RULE   *)
(* cannot crack opaque `word_pmul a w`): first distribute the opaque pmuls    *)
(* with `WORD_PMUL_XOR` (hol-light Library/words.ml) so every pmul atom is    *)
(* SHARED across both sides, then push word_xor into the word_join lanes and  *)
(* split into 64-bit lanes closed by WORD_BITWISE_RULE (pure XOR ring, NO     *)
(* bit-blasting of pmul).  A whole-goal WORD_BLAST does NOT terminate in      *)
(* practical time (it bit-blasts the pmuls); the lane-split is essential.     *)
(* ------------------------------------------------------------------------- *)

(* word_xor of two word_joins is the join of the xored lanes (64- and         *)
(* 128-bit-lane variants) + lane-split helpers.                               *)
let JOIN_XOR_LANE = WORD_BLAST
  `word_xor (word_join (a:int64) (b:int64):int128) (word_join c d) =
   word_join (word_xor a c) (word_xor b d)`;;

let JOIN_XOR_128 = WORD_BLAST
  `word_xor (word_join (a:int128) (b:int128):int256) (word_join c d) =
   word_join (word_xor a c) (word_xor b d)`;;

let JOIN_EQ_LANE = MESON[]
  `(a:int64) = c /\ (b:int64) = d ==> word_join a b:int128 = word_join c d`;;

let JOIN_EQ_128 = MESON[]
  `(a:int128) = c /\ (b:int128) = d ==> word_join a b:int256 = word_join c d`;;

(* polyval_reduce_prop3 distributes over word_xor. *)
let PROP3_XOR = prove
 (`!s t:256 word.
     polyval_reduce_prop3 (word_xor s t) =
     word_xor (polyval_reduce_prop3 s) (polyval_reduce_prop3 t)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[polyval_reduce_prop3] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[WORD_PMUL_XOR; WORD_SUBWORD_XOR] THEN
  REWRITE_TAC[JOIN_XOR_LANE] THEN
  MATCH_MP_TAC JOIN_EQ_LANE THEN CONJ_TAC THEN
  CONV_TAC WORD_BITWISE_RULE);;

(* ghash_reduce_raw is jointly additive in its three arguments.  Proved via   *)
(* the polyval_reduce_g2 bridge (so its two nested pmul layers become a single *)
(* prop3 of a linear argument) + PROP3_XOR + a 4-lane split.                   *)
let GHASH_REDUCE_RAW_XOR = prove
 (`!a1 a2 b1 b2 c1 c2:int128.
     ghash_reduce_raw (word_xor a1 a2) (word_xor b1 b2) (word_xor c1 c2) =
     word_xor (ghash_reduce_raw a1 b1 c1) (ghash_reduce_raw a2 b2 c2)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[GHASH_REDUCE_RAW_IS_POLYVAL_G2; POLYVAL_REDUCE_G2] THEN
  REWRITE_TAC[WORD_SUBWORD_XOR] THEN
  REWRITE_TAC[GSYM PROP3_XOR] THEN
  AP_TERM_TAC THEN
  REWRITE_TAC[JOIN_XOR_128; JOIN_XOR_LANE] THEN
  MATCH_MP_TAC JOIN_EQ_128 THEN CONJ_TAC THEN
  MATCH_MP_TAC JOIN_EQ_LANE THEN CONJ_TAC THEN
  CONV_TAC WORD_BITWISE_RULE);;

(* ------------------------------------------------------------------------- *)
(* Building blocks for the ALGEBRAIC Q19 fold (session 026).                  *)
(*                                                                           *)
(* These replace the dead-end g2 lane-match (byteswap128(prop3 A)=prop3 B,     *)
(* s020-024) with a per-block polyval_dot composition that never forms a       *)
(* byteswap-vs-reduce BITBLAST. The route (all validated on the real body-end  *)
(* q19_raw, session 026):                                                      *)
(*   RECON_GRR : raw reduce -> ghash_reduce_raw (Sum lolo)(Sum cross)(Sum hihi)*)
(*   EXT_BS    : collapse the accumulator ext(byteswap128 sofar) -> sofar      *)
(*               (WHOLE int128 — the s024 accumulator-byteswap obstruction     *)
(*               dissolves here, before any lane slicing; the loop-top         *)
(*               `ext v19@0x4cc` is exactly this un-byteswap).                 *)
(*   [reassemble cipherblocks + AC-normalise the 3 lanes to canonical order]   *)
(*   GHASH_REDUCE_RAW_DIST8 : summed lanes -> XOR_j polyval_dot a_j b_j        *)
(*   DOTSUM_IS_PROP3SUM     : -> prop3(XOR_j pmul a_j b_j) = the RHS batched B. *)
(* ------------------------------------------------------------------------- *)

(* ext o byteswap128 = id.  On the RAW body-end reduce the accumulator appears  *)
(* as word_subword(word_join(byteswap128 sofar)(byteswap128 sofar))(64,128) =   *)
(* ext(byteswap128 sofar); this collapses it to the plain sofar the RHS wants,  *)
(* as a WHOLE int128 (so no residual half-swap survives lane slicing).          *)
let EXT_BS = prove
 (`!x:int128.
     word_subword (word_join (byteswap128 x) (byteswap128 x):int256) (64,128) = x`,
  REWRITE_TAC[byteswap128] THEN GEN_TAC THEN CONV_TAC WORD_BLAST);;

(* The hardware's three summed Karatsuba lanes (in CANONICAL block order 0..7)  *)
(* reduce to the XOR-sum of the eight per-block polyval_dots.  GHASH_REDUCE_RAW_ *)
(* XOR (GF(2)-linearity) distributes the 3-arg sum into 8 aligned triples; each *)
(* fires GHASH_REDUCE_RAW_KARATSUBA_IS_DOT.  (The body lanes come out in order  *)
(* 1,0,2,3,4,5,6,7 across all three lanes — AC-normalise to canonical before    *)
(* applying this.)                                                              *)
let GHASH_REDUCE_RAW_DIST8 = prove
 (`!a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7:int128.
    ghash_reduce_raw
      (word_xor (word_pmul (word_subword a0 (0,64):int64) (word_subword b0 (0,64):int64):int128)
      (word_xor (word_pmul (word_subword a1 (0,64):int64) (word_subword b1 (0,64):int64):int128)
      (word_xor (word_pmul (word_subword a2 (0,64):int64) (word_subword b2 (0,64):int64):int128)
      (word_xor (word_pmul (word_subword a3 (0,64):int64) (word_subword b3 (0,64):int64):int128)
      (word_xor (word_pmul (word_subword a4 (0,64):int64) (word_subword b4 (0,64):int64):int128)
      (word_xor (word_pmul (word_subword a5 (0,64):int64) (word_subword b5 (0,64):int64):int128)
      (word_xor (word_pmul (word_subword a6 (0,64):int64) (word_subword b6 (0,64):int64):int128)
                (word_pmul (word_subword a7 (0,64):int64) (word_subword b7 (0,64):int64):int128))))))))
      (word_xor (word_pmul (word_xor (word_subword a0 (0,64):int64) (word_subword a0 (64,64):int64)) (word_xor (word_subword b0 (0,64):int64) (word_subword b0 (64,64):int64)):int128)
      (word_xor (word_pmul (word_xor (word_subword a1 (0,64):int64) (word_subword a1 (64,64):int64)) (word_xor (word_subword b1 (0,64):int64) (word_subword b1 (64,64):int64)):int128)
      (word_xor (word_pmul (word_xor (word_subword a2 (0,64):int64) (word_subword a2 (64,64):int64)) (word_xor (word_subword b2 (0,64):int64) (word_subword b2 (64,64):int64)):int128)
      (word_xor (word_pmul (word_xor (word_subword a3 (0,64):int64) (word_subword a3 (64,64):int64)) (word_xor (word_subword b3 (0,64):int64) (word_subword b3 (64,64):int64)):int128)
      (word_xor (word_pmul (word_xor (word_subword a4 (0,64):int64) (word_subword a4 (64,64):int64)) (word_xor (word_subword b4 (0,64):int64) (word_subword b4 (64,64):int64)):int128)
      (word_xor (word_pmul (word_xor (word_subword a5 (0,64):int64) (word_subword a5 (64,64):int64)) (word_xor (word_subword b5 (0,64):int64) (word_subword b5 (64,64):int64)):int128)
      (word_xor (word_pmul (word_xor (word_subword a6 (0,64):int64) (word_subword a6 (64,64):int64)) (word_xor (word_subword b6 (0,64):int64) (word_subword b6 (64,64):int64)):int128)
                (word_pmul (word_xor (word_subword a7 (0,64):int64) (word_subword a7 (64,64):int64)) (word_xor (word_subword b7 (0,64):int64) (word_subword b7 (64,64):int64)):int128))))))))
      (word_xor (word_pmul (word_subword a0 (64,64):int64) (word_subword b0 (64,64):int64):int128)
      (word_xor (word_pmul (word_subword a1 (64,64):int64) (word_subword b1 (64,64):int64):int128)
      (word_xor (word_pmul (word_subword a2 (64,64):int64) (word_subword b2 (64,64):int64):int128)
      (word_xor (word_pmul (word_subword a3 (64,64):int64) (word_subword b3 (64,64):int64):int128)
      (word_xor (word_pmul (word_subword a4 (64,64):int64) (word_subword b4 (64,64):int64):int128)
      (word_xor (word_pmul (word_subword a5 (64,64):int64) (word_subword b5 (64,64):int64):int128)
      (word_xor (word_pmul (word_subword a6 (64,64):int64) (word_subword b6 (64,64):int64):int128)
                (word_pmul (word_subword a7 (64,64):int64) (word_subword b7 (64,64):int64):int128))))))))
    = word_xor (polyval_dot a0 b0)
      (word_xor (polyval_dot a1 b1)
      (word_xor (polyval_dot a2 b2)
      (word_xor (polyval_dot a3 b3)
      (word_xor (polyval_dot a4 b4)
      (word_xor (polyval_dot a5 b5)
      (word_xor (polyval_dot a6 b6) (polyval_dot a7 b7)))))))`,
  REWRITE_TAC[GHASH_REDUCE_RAW_XOR] THEN
  REWRITE_TAC[GHASH_REDUCE_RAW_KARATSUBA_IS_DOT]);;

(* Collapse the per-block dot-sum to a single prop3 of the pmul-sum (via the    *)
(* proven additivity PROP3_XOR).  The RHS of the Q19 fold, after                *)
(* GHASH_POLYVAL_ACC_BATCHED, is exactly prop3 of this same pmul-sum with       *)
(* a_0 = word_xor sofar cb0 and b_j = h^{7-j}.                                   *)
let DOTSUM_IS_PROP3SUM = prove
 (`word_xor (polyval_dot a0 b0)
   (word_xor (polyval_dot a1 b1)
   (word_xor (polyval_dot a2 b2)
   (word_xor (polyval_dot a3 b3)
   (word_xor (polyval_dot a4 b4)
   (word_xor (polyval_dot a5 b5)
   (word_xor (polyval_dot a6 b6) (polyval_dot a7 b7))))))) =
   polyval_reduce_prop3
    (word_xor (word_pmul a0 b0)
    (word_xor (word_pmul a1 b1)
    (word_xor (word_pmul a2 b2)
    (word_xor (word_pmul a3 b3)
    (word_xor (word_pmul a4 b4)
    (word_xor (word_pmul a5 b5)
    (word_xor (word_pmul a6 b6) (word_pmul a7 b7:256 word))))))))`,
  REWRITE_TAC[polyval_dot; PROP3_XOR]);;

(* ------------------------------------------------------------------------- *)
(* Session 027: obstruction-3 building blocks — fire the summed-lane reduce   *)
(* in the EXACT hardware lane order the body-end residual presents.           *)
(*                                                                           *)
(* The reassembled body-end reduce (after RECON_GRR + EXT_BS + cipherblock    *)
(* reassembly) is `ghash_reduce_raw P0 P1 P2` where each Pl is an 8-term      *)
(* LEFT-associated word_xor sum of per-block Karatsuba pieces, but the three  *)
(* lanes DISAGREE on block order:                                             *)
(*   P0 (lo.lo)  block order [1;0;2;3;4;5;6;7], b-lane = subword(h^p)(0,64)   *)
(*   P1 (cross)  block order [1;0;3;2;5;4;7;6], b-lane = karatsuba_mid(h^p)   *)
(*   P2 (hi.hi)  block order [1;0;2;3;4;5;6;7], b-lane = subword(h^p)(64,64)  *)
(* (block j is paired with h-power h^{7-j}).  GHASH_REDUCE_RAW_DIST8 (session  *)
(* 026) assumes ONE canonical order across all three lanes, so it does not     *)
(* fire on this misaligned form.  GHASH_REDUCE_RAW_DIST8_HW below is proved in *)
(* the exact observed order by first AC-reordering the cross lane [1;0;3;2..] *)
(* -> [1;0;2;3..] (REORD_CROSS, pure word_xor ring so WORD_BITWISE_RULE) then  *)
(* the s026 GHASH_REDUCE_RAW_XOR + per-block KARATSUBA_IS_DOT_HW.              *)
(* ------------------------------------------------------------------------- *)

(* Per-block: the cross lane in the body uses `karatsuba_mid b` and an a-arg   *)
(* subword order (64,64),(0,64); normalise both to KARATSUBA_IS_DOT's form.    *)
let KARATSUBA_IS_DOT_HW = prove
 (`!a b:int128.
    ghash_reduce_raw
      (word_pmul (word_subword a (0,64):int64) (word_subword b (0,64):int64):int128)
      (word_pmul (word_xor (word_subword a (64,64):int64) (word_subword a (0,64):int64))
                 (karatsuba_mid b):int128)
      (word_pmul (word_subword a (64,64):int64) (word_subword b (64,64):int64):int128)
    = polyval_dot a b`,
  REPEAT GEN_TAC THEN REWRITE_TAC[karatsuba_mid] THEN
  ONCE_REWRITE_TAC[WORD_BITWISE_RULE
    `word_xor (word_subword (a:int128) (64,64):int64) (word_subword a (0,64))
     = word_xor (word_subword a (0,64):int64) (word_subword a (64,64))`] THEN
  REWRITE_TAC[GHASH_REDUCE_RAW_KARATSUBA_IS_DOT]);;

(* AC-reorder a LEFT-associated 8-term int128 word_xor from the cross-lane     *)
(* block order [1;0;3;2;5;4;7;6] to the shared order [1;0;2;3;4;5;6;7].        *)
let REORD_CROSS = prove
 (`word_xor (word_xor (word_xor (word_xor (word_xor (word_xor (word_xor
      (x1:int128) x0) x3) x2) x5) x4) x7) x6 =
   word_xor (word_xor (word_xor (word_xor (word_xor (word_xor (word_xor
      x1 x0) x2) x3) x4) x5) x6) x7`,
  CONV_TAC WORD_BITWISE_RULE);;

(* The summed hardware lanes in the EXACT observed order reduce to the         *)
(* XOR-sum of the eight per-block polyval_dots (canonical [0..7] on the RHS).  *)
let GHASH_REDUCE_RAW_DIST8_HW = prove
 (`!a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7:int128.
    ghash_reduce_raw
      (word_xor (word_xor (word_xor (word_xor (word_xor (word_xor (word_xor
        (word_pmul (word_subword a1 (0,64):int64) (word_subword b1 (0,64):int64):int128)
        (word_pmul (word_subword a0 (0,64):int64) (word_subword b0 (0,64):int64):int128))
        (word_pmul (word_subword a2 (0,64):int64) (word_subword b2 (0,64):int64):int128))
        (word_pmul (word_subword a3 (0,64):int64) (word_subword b3 (0,64):int64):int128))
        (word_pmul (word_subword a4 (0,64):int64) (word_subword b4 (0,64):int64):int128))
        (word_pmul (word_subword a5 (0,64):int64) (word_subword b5 (0,64):int64):int128))
        (word_pmul (word_subword a6 (0,64):int64) (word_subword b6 (0,64):int64):int128))
        (word_pmul (word_subword a7 (0,64):int64) (word_subword b7 (0,64):int64):int128))
      (word_xor (word_xor (word_xor (word_xor (word_xor (word_xor (word_xor
        (word_pmul (word_xor (word_subword a1 (64,64):int64) (word_subword a1 (0,64):int64)) (karatsuba_mid b1):int128)
        (word_pmul (word_xor (word_subword a0 (64,64):int64) (word_subword a0 (0,64):int64)) (karatsuba_mid b0):int128))
        (word_pmul (word_xor (word_subword a3 (64,64):int64) (word_subword a3 (0,64):int64)) (karatsuba_mid b3):int128))
        (word_pmul (word_xor (word_subword a2 (64,64):int64) (word_subword a2 (0,64):int64)) (karatsuba_mid b2):int128))
        (word_pmul (word_xor (word_subword a5 (64,64):int64) (word_subword a5 (0,64):int64)) (karatsuba_mid b5):int128))
        (word_pmul (word_xor (word_subword a4 (64,64):int64) (word_subword a4 (0,64):int64)) (karatsuba_mid b4):int128))
        (word_pmul (word_xor (word_subword a7 (64,64):int64) (word_subword a7 (0,64):int64)) (karatsuba_mid b7):int128))
        (word_pmul (word_xor (word_subword a6 (64,64):int64) (word_subword a6 (0,64):int64)) (karatsuba_mid b6):int128))
      (word_xor (word_xor (word_xor (word_xor (word_xor (word_xor (word_xor
        (word_pmul (word_subword a1 (64,64):int64) (word_subword b1 (64,64):int64):int128)
        (word_pmul (word_subword a0 (64,64):int64) (word_subword b0 (64,64):int64):int128))
        (word_pmul (word_subword a2 (64,64):int64) (word_subword b2 (64,64):int64):int128))
        (word_pmul (word_subword a3 (64,64):int64) (word_subword b3 (64,64):int64):int128))
        (word_pmul (word_subword a4 (64,64):int64) (word_subword b4 (64,64):int64):int128))
        (word_pmul (word_subword a5 (64,64):int64) (word_subword b5 (64,64):int64):int128))
        (word_pmul (word_subword a6 (64,64):int64) (word_subword b6 (64,64):int64):int128))
        (word_pmul (word_subword a7 (64,64):int64) (word_subword b7 (64,64):int64):int128))
    = word_xor (word_xor (word_xor (word_xor (word_xor (word_xor (word_xor
        (polyval_dot a0 b0) (polyval_dot a1 b1)) (polyval_dot a2 b2))
        (polyval_dot a3 b3)) (polyval_dot a4 b4)) (polyval_dot a5 b5))
        (polyval_dot a6 b6)) (polyval_dot a7 b7)`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o RATOR_CONV o RAND_CONV) [REORD_CROSS] THEN
  REWRITE_TAC[GHASH_REDUCE_RAW_XOR] THEN
  REWRITE_TAC[KARATSUBA_IS_DOT_HW] THEN
  CONV_TAC WORD_BITWISE_RULE);;

(* Block-0 accumulator lane fold: after EXT_BS the accumulator `sofar`         *)
(* enters the reduce with its two 64-bit halves SWAPPED relative to cb0 (the   *)
(* store-order byteswap), so the reduce's lo.lo/hi.hi lanes read              *)
(*   word_xor (subword sofar (64,64)) (subword cb0 (0,64))   [lo.lo]           *)
(*   word_xor (subword sofar (0,64))  (subword cb0 (64,64))  [hi.hi]           *)
(* These are exactly the (0,64)/(64,64) subwords of `word_xor (byteswap128     *)
(* sofar) cb0`, so folding them re-exposes a clean single-word accumulator     *)
(* a_0 = byteswap128 sofar (x) cb0 that KARATSUBA_IS_DOT_HW consumes.          *)
let A0_LO = prove
 (`word_xor (word_subword (sofar:int128) (64,64):int64) (word_subword (cb0:int128) (0,64):int64)
   = word_subword (word_xor (byteswap128 sofar) cb0) (0,64):int64`,
  REWRITE_TAC[byteswap128; WORD_SUBWORD_XOR] THEN CONV_TAC WORD_BLAST);;
let A0_HI = prove
 (`word_xor (word_subword (sofar:int128) (0,64):int64) (word_subword (cb0:int128) (64,64):int64)
   = word_subword (word_xor (byteswap128 sofar) cb0) (64,64):int64`,
  REWRITE_TAC[byteswap128; WORD_SUBWORD_XOR] THEN CONV_TAC WORD_BLAST);;

(* Per-block-0 reduce, in the EXACT raw swapped-lane form the body produces      *)
(* (sofar's two 64-bit halves crossed with cb0's — the store-order byteswap):    *)
(*   lo.lo  = word_xor (subword sofar (64,64)) (subword cb0 (0,64))              *)
(*   hi.hi  = word_xor (subword sofar (0,64))  (subword cb0 (64,64))             *)
(*   cross  = word_xor <hi-shape> <lo-shape>                                     *)
(* This reduces to polyval_dot (byteswap128 sofar (x) cb0) b.  The block-0       *)
(* accumulator byteswap is absorbed INSIDE this lemma (ABBREV byteswap128 sofar  *)
(* so the swap-lane rewrites do not re-fire on their own output), which is why   *)
(* the global fold A0_LO/A0_HI cannot be used directly on the body residual.     *)
let KDOT_B0 = prove
 (`!s c b:int128.
    ghash_reduce_raw
      (word_pmul (word_xor (word_subword s (64,64):int64) (word_subword c (0,64):int64))
                 (word_subword b (0,64):int64):int128)
      (word_pmul (word_xor (word_xor (word_subword s (0,64):int64) (word_subword c (64,64):int64))
                           (word_xor (word_subword s (64,64):int64) (word_subword c (0,64):int64)))
                 (karatsuba_mid b):int128)
      (word_pmul (word_xor (word_subword s (0,64):int64) (word_subword c (64,64):int64))
                 (word_subword b (64,64):int64):int128)
    = polyval_dot (word_xor (byteswap128 s) c) b`,
  REPEAT GEN_TAC THEN ABBREV_TAC `bs = byteswap128 (s:int128)` THEN
  SUBGOAL_THEN `word_subword (s:int128) (64,64):int64 = word_subword (bs:int128) (0,64) /\
                word_subword (s:int128) (0,64):int64 = word_subword (bs:int128) (64,64)`
    (fun th -> REWRITE_TAC[th]) THENL
   [EXPAND_TAC "bs" THEN REWRITE_TAC[byteswap128] THEN CONJ_TAC THEN CONV_TAC WORD_BLAST;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM WORD_SUBWORD_XOR] THEN REWRITE_TAC[KARATSUBA_IS_DOT_HW]);;

(* The full body-order 8-block distribution WITH block-0 in raw form: the three  *)
(* summed hardware lanes (block order [1;0;2;3;4;5;6;7] on lo.lo/hi.hi,          *)
(* [1;0;3;2;5;4;7;6] on cross) reduce to the canonical XOR-sum of the eight      *)
(* per-block polyval_dots, where block 0's dot argument carries the store-order  *)
(* byteswap `byteswap128 s (x) c`.  This is the lemma that FIRES on the real     *)
(* body-end residual (verified live: reassembled reduce -> this exact form).     *)
let GHASH_REDUCE_RAW_DIST8_B0 = prove
 (`!s c a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7:int128.
    ghash_reduce_raw
      (word_xor (word_xor (word_xor (word_xor (word_xor (word_xor (word_xor
        (word_pmul (word_subword a1 (0,64):int64) (word_subword b1 (0,64):int64):int128)
        (word_pmul (word_xor (word_subword s (64,64):int64) (word_subword c (0,64):int64)) (word_subword b0 (0,64):int64):int128))
        (word_pmul (word_subword a2 (0,64):int64) (word_subword b2 (0,64):int64):int128))
        (word_pmul (word_subword a3 (0,64):int64) (word_subword b3 (0,64):int64):int128))
        (word_pmul (word_subword a4 (0,64):int64) (word_subword b4 (0,64):int64):int128))
        (word_pmul (word_subword a5 (0,64):int64) (word_subword b5 (0,64):int64):int128))
        (word_pmul (word_subword a6 (0,64):int64) (word_subword b6 (0,64):int64):int128))
        (word_pmul (word_subword a7 (0,64):int64) (word_subword b7 (0,64):int64):int128))
      (word_xor (word_xor (word_xor (word_xor (word_xor (word_xor (word_xor
        (word_pmul (word_xor (word_subword a1 (64,64):int64) (word_subword a1 (0,64):int64)) (karatsuba_mid b1):int128)
        (word_pmul (word_xor (word_xor (word_subword s (0,64):int64) (word_subword c (64,64):int64)) (word_xor (word_subword s (64,64):int64) (word_subword c (0,64):int64))) (karatsuba_mid b0):int128))
        (word_pmul (word_xor (word_subword a3 (64,64):int64) (word_subword a3 (0,64):int64)) (karatsuba_mid b3):int128))
        (word_pmul (word_xor (word_subword a2 (64,64):int64) (word_subword a2 (0,64):int64)) (karatsuba_mid b2):int128))
        (word_pmul (word_xor (word_subword a5 (64,64):int64) (word_subword a5 (0,64):int64)) (karatsuba_mid b5):int128))
        (word_pmul (word_xor (word_subword a4 (64,64):int64) (word_subword a4 (0,64):int64)) (karatsuba_mid b4):int128))
        (word_pmul (word_xor (word_subword a7 (64,64):int64) (word_subword a7 (0,64):int64)) (karatsuba_mid b7):int128))
        (word_pmul (word_xor (word_subword a6 (64,64):int64) (word_subword a6 (0,64):int64)) (karatsuba_mid b6):int128))
      (word_xor (word_xor (word_xor (word_xor (word_xor (word_xor (word_xor
        (word_pmul (word_subword a1 (64,64):int64) (word_subword b1 (64,64):int64):int128)
        (word_pmul (word_xor (word_subword s (0,64):int64) (word_subword c (64,64):int64)) (word_subword b0 (64,64):int64):int128))
        (word_pmul (word_subword a2 (64,64):int64) (word_subword b2 (64,64):int64):int128))
        (word_pmul (word_subword a3 (64,64):int64) (word_subword b3 (64,64):int64):int128))
        (word_pmul (word_subword a4 (64,64):int64) (word_subword b4 (64,64):int64):int128))
        (word_pmul (word_subword a5 (64,64):int64) (word_subword b5 (64,64):int64):int128))
        (word_pmul (word_subword a6 (64,64):int64) (word_subword b6 (64,64):int64):int128))
        (word_pmul (word_subword a7 (64,64):int64) (word_subword b7 (64,64):int64):int128))
    = word_xor (word_xor (word_xor (word_xor (word_xor (word_xor (word_xor
        (polyval_dot (word_xor (byteswap128 s) c) b0) (polyval_dot a1 b1)) (polyval_dot a2 b2))
        (polyval_dot a3 b3)) (polyval_dot a4 b4)) (polyval_dot a5 b5))
        (polyval_dot a6 b6)) (polyval_dot a7 b7)`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o RATOR_CONV o RAND_CONV) [REORD_CROSS] THEN
  REWRITE_TAC[GHASH_REDUCE_RAW_XOR] THEN
  REWRITE_TAC[KDOT_B0; KARATSUBA_IS_DOT_HW] THEN
  CONV_TAC WORD_BITWISE_RULE);;

(* SESSION 029 (route c — HUMAN-directed re-examination of the x8 Q19 invariant): *)
(* the body-order 8-block distribution with ALL blocks in the CLEAN (non-crossed) *)
(* form — block order [1;0;2;3;4;5;6;7] on lo.lo/hi.hi, [1;0;3;2;5;4;7;6] on the *)
(* cross lane — reduces to the canonical XOR-sum of the eight per-block           *)
(* polyval_dots.  This is the PLAIN analogue of GHASH_REDUCE_RAW_DIST8_B0 (which  *)
(* carries the store-order byteswap on block 0): it FIRES on the body-end Q19     *)
(* residual once the Q19 loop-invariant conjunct is stated WITHOUT the            *)
(* `byteswap128` wrapper (`read Q19 s = nist_ghash..8i`, not                       *)
(* `byteswap128(nist_ghash..8i)`).  Session 029 established EMPIRICALLY (via a     *)
(* faithful re-derivation of the H2 body residual) that under the plain invariant *)
(* block 0 enters the reduce as the ordinary `nist_cipher_block (x) sofar`        *)
(* (NO store-order byteswap), so DIST8_B0's block-0 crossing is neither needed    *)
(* nor matched — this lemma is.  Same proof shape as DIST8_B0 minus KDOT_B0.       *)
let GHASH_REDUCE_RAW_DIST8_PLAIN = prove
 (`!a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7:int128.
    ghash_reduce_raw
      (word_xor (word_xor (word_xor (word_xor (word_xor (word_xor (word_xor
        (word_pmul (word_subword a1 (0,64):int64) (word_subword b1 (0,64):int64):int128)
        (word_pmul (word_subword a0 (0,64):int64) (word_subword b0 (0,64):int64):int128))
        (word_pmul (word_subword a2 (0,64):int64) (word_subword b2 (0,64):int64):int128))
        (word_pmul (word_subword a3 (0,64):int64) (word_subword b3 (0,64):int64):int128))
        (word_pmul (word_subword a4 (0,64):int64) (word_subword b4 (0,64):int64):int128))
        (word_pmul (word_subword a5 (0,64):int64) (word_subword b5 (0,64):int64):int128))
        (word_pmul (word_subword a6 (0,64):int64) (word_subword b6 (0,64):int64):int128))
        (word_pmul (word_subword a7 (0,64):int64) (word_subword b7 (0,64):int64):int128))
      (word_xor (word_xor (word_xor (word_xor (word_xor (word_xor (word_xor
        (word_pmul (word_xor (word_subword a1 (64,64):int64) (word_subword a1 (0,64):int64)) (karatsuba_mid b1):int128)
        (word_pmul (word_xor (word_subword a0 (64,64):int64) (word_subword a0 (0,64):int64)) (karatsuba_mid b0):int128))
        (word_pmul (word_xor (word_subword a3 (64,64):int64) (word_subword a3 (0,64):int64)) (karatsuba_mid b3):int128))
        (word_pmul (word_xor (word_subword a2 (64,64):int64) (word_subword a2 (0,64):int64)) (karatsuba_mid b2):int128))
        (word_pmul (word_xor (word_subword a5 (64,64):int64) (word_subword a5 (0,64):int64)) (karatsuba_mid b5):int128))
        (word_pmul (word_xor (word_subword a4 (64,64):int64) (word_subword a4 (0,64):int64)) (karatsuba_mid b4):int128))
        (word_pmul (word_xor (word_subword a7 (64,64):int64) (word_subword a7 (0,64):int64)) (karatsuba_mid b7):int128))
        (word_pmul (word_xor (word_subword a6 (64,64):int64) (word_subword a6 (0,64):int64)) (karatsuba_mid b6):int128))
      (word_xor (word_xor (word_xor (word_xor (word_xor (word_xor (word_xor
        (word_pmul (word_subword a1 (64,64):int64) (word_subword b1 (64,64):int64):int128)
        (word_pmul (word_subword a0 (64,64):int64) (word_subword b0 (64,64):int64):int128))
        (word_pmul (word_subword a2 (64,64):int64) (word_subword b2 (64,64):int64):int128))
        (word_pmul (word_subword a3 (64,64):int64) (word_subword b3 (64,64):int64):int128))
        (word_pmul (word_subword a4 (64,64):int64) (word_subword b4 (64,64):int64):int128))
        (word_pmul (word_subword a5 (64,64):int64) (word_subword b5 (64,64):int64):int128))
        (word_pmul (word_subword a6 (64,64):int64) (word_subword b6 (64,64):int64):int128))
        (word_pmul (word_subword a7 (64,64):int64) (word_subword b7 (64,64):int64):int128))
    = word_xor (word_xor (word_xor (word_xor (word_xor (word_xor (word_xor
        (polyval_dot a0 b0) (polyval_dot a1 b1)) (polyval_dot a2 b2))
        (polyval_dot a3 b3)) (polyval_dot a4 b4)) (polyval_dot a5 b5))
        (polyval_dot a6 b6)) (polyval_dot a7 b7)`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o RATOR_CONV o RAND_CONV) [REORD_CROSS] THEN
  REWRITE_TAC[GHASH_REDUCE_RAW_XOR] THEN
  REWRITE_TAC[KARATSUBA_IS_DOT_HW] THEN
  CONV_TAC WORD_BITWISE_RULE);;

(* ------------------------------------------------------------------------- *)
(* Q19 GHASH-fold tactic (blocker A — sessions 017-022).                      *)
(*                                                                           *)
(* Applied to the body-end Q19 residual conjunct                              *)
(*   `<raw ghash reduce of the 8 in-flight ciphertext blocks> =              *)
(*    byteswap128(nist_ghash H tag0 (list_of_seq nist_cipher_block (8i+8)))`  *)
(* AFTER splitting it off the raw post-FINAL_STATE conjunction but BEFORE the *)
(* cheap-close (whose WORD_SIMPLE_SUBWORD_CONV would destroy the foldable     *)
(* ext/LO structure — session 022 confirmed the fold FAILS post-cheap-close). *)
(* NSTEP_G (guarded stepper) is what keeps the accumulator foldable through   *)
(* the 339 body steps.                                                        *)
(*                                                                           *)
(* Chain (session 021/022, validated live end-to-end):                        *)
(*  1. AC-swap the eor3 top XOR into ghash_reduce_raw's grouping;             *)
(*  2. GSYM ghash_reduce_raw (RECON_GRR) — FIRES (LHS 186k->67k);             *)
(*  3. GHASH_REDUCE_RAW_IS_POLYVAL_G2 (-> polyval_reduce_g2 P1 P3 P2);        *)
(*  4. MATCH_MP_TAC BS_INVOL (flip the RHS byteswap onto the LHS);            *)
(*  5. fold the RHS nist_ghash to a prop3 chain: NIST_GHASH_IS_POLYVAL +      *)
(*     8(i+1)=SUC^8(8i) + list_of_seq + APPEND + GHASH_ACC_APPEND, then       *)
(*     normalise the CONS SUC-form indices to +n (ADD1;GSYM ADD_ASSOC;        *)
(*     NUM_ADD_CONV) so the batched ISPECL matches, then                      *)
(*     GHASH_POLYVAL_ACC_BATCHED collapses it to prop3 B.                     *)
(* The residual is the final lane-match                                       *)
(*   `byteswap128(polyval_reduce_prop3 A) = polyval_reduce_prop3 B`           *)
(* (A = the g2-Karatsuba lanes, B = the clean cipherblock (x) h_power chain,  *)
(* differing by the store-order byteswap).  That lane-identity is CHEAT'd     *)
(* here (the ONE remaining piece of blocker A — see the Q19_LANE_MATCH note   *)
(* in the body-close comment); everything ABOVE it is genuinely proved.       *)
let RECON_GRR = REWRITE_RULE[LET_DEF; LET_END_DEF] (GSYM ghash_reduce_raw);;

(* SESSION 029 — ROUTE (c), blocker A CLOSED (no CHEAT).  The 5-session Q19    *)
(* dead-end (s018-028) was caused by the P5 invariant stating the Q19          *)
(* accumulator conjunct WITH a `byteswap128` wrapper                            *)
(*   read Q19 s = byteswap128(nist_ghash..8i)                                   *)
(* whereas the x8 body PRESERVES the PLAIN form                                 *)
(*   read Q19 s = nist_ghash..8i.                                               *)
(* ROOT CAUSE of the divergence from x4: x4 has BOTH a leading `ext v17`        *)
(* AND a TRAILING `ext v11` at body-end (byteswap-parity 1); x8 has ONLY the    *)
(* leading `ext v19`@0x4cc and NO trailing ext (byteswap-parity 0).  Under the  *)
(* byteswapped invariant the body-end reduce (parity 0) could never match the   *)
(* byteswap-wrapped RHS (parity 1) — the odd-parity gap that BS_INVOL/BS_INJ    *)
(* only move side-to-side (s028).  With the PLAIN invariant the body-end reduce *)
(* (parity 0) matches the plain RHS (parity 0) and the fold closes cleanly via  *)
(* the flat 8-`polyval_dot`-sum route.  Established empirically (session 029)    *)
(* by re-deriving the H2 body residual: block 0 enters the reduce as the        *)
(* ordinary clean `nist_cipher_block (x) sofar` (no store-order byteswap), so    *)
(* the fold uses GHASH_REDUCE_RAW_DIST8_PLAIN (all blocks clean), NOT DIST8_B0.  *)
let Q19_FOLD_TAC =
  ONCE_REWRITE_TAC[WORD_BITWISE_RULE
    `word_xor (word_xor (x:int128) e) p = word_xor (word_xor x p) e`] THEN
  REWRITE_TAC[RECON_GRR] THEN
  (* Reassemble the 8 cipherblocks (no EXT_BS: the plain invariant leaves no    *)
  (* store-order byteswap on the accumulator to cancel).                        *)
  REWRITE_TAC[GSYM cipher_block] THEN REWRITE_TAC[CIPHER_BLOCK_NIST] THEN
  REWRITE_TAC[WORD_SUBWORD_REVERSEFIELDS] THEN
  SIMP_TAC[WORD_JOIN_COMBINE_LEMMA; ARITH] THEN
  REWRITE_TAC[WORD_SUBWORD_XOR] THEN REWRITE_TAC[WORD_SUBWORD_BYTESWAP128] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[WORD_SUBWORD_XOR] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  (* Re-fold the block-accumulator's distributed subwords                        *)
  (* (subword X (x) subword Y -> subword(X (x) Y)) so DIST8_PLAIN's lo.lo/hi.hi  *)
  (* lanes match, then distribute the reduce over the 8 clean blocks.            *)
  REWRITE_TAC[GSYM WORD_SUBWORD_XOR] THEN
  REWRITE_TAC[GHASH_REDUCE_RAW_DIST8_PLAIN] THEN
  (* RHS: fold nist_ghash..8(i+1) to prop3(pmul chain) — plain, no BS_INVOL.     *)
  REWRITE_TAC[NIST_GHASH_IS_POLYVAL] THEN
  REWRITE_TAC[ARITH_RULE
    `8 * (i + 1) = SUC(SUC(SUC(SUC(SUC(SUC(SUC(SUC(8 * i))))))))`] THEN
  REWRITE_TAC[list_of_seq] THEN REWRITE_TAC[GSYM APPEND_ASSOC] THEN
  REWRITE_TAC[APPEND] THEN
  REWRITE_TAC[GHASH_ACC_APPEND] THEN
  REWRITE_TAC[ADD1; GSYM ADD_ASSOC] THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
  MP_TAC(ISPECL
    [`ghash_twist (aes256_cipher (word 0) rk)`;
     `[nist_cipher_block nonce rk inblock (8*i+1);
       nist_cipher_block nonce rk inblock (8*i+2);
       nist_cipher_block nonce rk inblock (8*i+3);
       nist_cipher_block nonce rk inblock (8*i+4);
       nist_cipher_block nonce rk inblock (8*i+5);
       nist_cipher_block nonce rk inblock (8*i+6);
       nist_cipher_block nonce rk inblock (8*i+7)]:(int128)list`;
     `ghash_polyval_acc (ghash_twist (aes256_cipher (word 0) rk)) tag0
        (list_of_seq (nist_cipher_block nonce rk inblock) (8*i))`;
     `nist_cipher_block nonce rk inblock (8*i)`]
    GHASH_POLYVAL_ACC_BATCHED) THEN
  REWRITE_TAC[LENGTH; ghash_wide] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  (* Both sides are now the SAME 8-block field element, byteswap-free: collapse *)
  (* the LHS XOR-of-polyval_dot to a single prop3 (GF(2)-linearity, PROP3_XOR)  *)
  (* and match the pmul-sums by GF(2) XOR-AC.                                    *)
  REWRITE_TAC[ADD_0] THEN
  REWRITE_TAC[polyval_dot] THEN
  REWRITE_TAC[GSYM PROP3_XOR] THEN
  AP_TERM_TAC THEN CONV_TAC WORD_BITWISE_RULE;;

(* ---- historical note (blocker A resolution, sessions 018-029) --------------- *)
(* The comment below documents the DEAD routes so future sessions don't retry    *)
(* them.  Route (c) [drop the byteswap128 invariant wrapper] closed the fold.     *)
(* OLD (superseded) tactic tail, kept for the diagnosis it records:              *)
(*   ... MATCH_MP_TAC BS_INVOL ... then CHEAT'd the lane-match                    *)
(*   Final lane-match `byteswap128(prop3 A) = prop3 B` — CHEAT'd (the ONE      *)
  (* remaining piece of blocker A).  A = g2 Karatsuba lanes over the 8 in-     *)
  (* flight cipherblocks; B = the clean cipherblock (x) h_power chain; they    *)
  (* differ by the store-order byteswap.                                       *)
  (*                                                                           *)
  (* SESSION 023 DIAGNOSIS (decisive; redirects the s020-022 lane-split idea): *)
  (* the reduction to a "pure word_join/subword/xor identity over ~40 int128   *)
  (* vars" is NOT closable by BITBLAST after abstracting the pmul atoms to      *)
  (* fresh vars.  Verified end-to-end on the warm server (goal captured, all   *)
  (* stages measured):                                                         *)
  (*  - Reassemble the 8 cipherblocks (69329->7443 chars), strip the outer     *)
  (*    byteswap via GSYM BS_INVOL2+AP_TERM, ABBREV cb0..7/h0..7/sofar         *)
  (*    (-> 3060), REWRITE karatsuba_mid + align the mid-pmul arg order with   *)
  (*    the x4 WORD_XOR_SYM MESON rule (reload_full 1083-1085).                 *)
  (*  - Result: 24 pmul atoms per side; 21 of 24 MATCH; exactly 3 GENUINELY    *)
  (*    MISMATCH — the accumulator (cb0) block: LHS uses `byteswap128 sofar`   *)
  (*    (the hardware Q19 is stored byteswapped, invariant Q19 =               *)
  (*    byteswap128(nist_ghash..8i)) so its lo/hi lanes pair sofar_hi with     *)
  (*    cb0_lo; RHS uses plain `word_xor sofar cb0` (sofar_lo with cb0_lo).    *)
  (*  - Abstracting all pmul atoms then BITBLAST => `EQT_ELIM` (goal FALSE      *)
  (*    under free sofar): the accumulator's store-order byteswap is           *)
  (*    load-bearing, it is NOT a term-by-term pmul match.                     *)
  (*  - CONFIRMED prop3 does NOT commute with byteswap under ANY lane          *)
  (*    permutation of its 256-bit arg (half-swap and lane-reverse both        *)
  (*    disproved by a 0.3s BITBLAST over a free `t:256 word`).  So there is   *)
  (*    no `byteswap128(prop3 t) = prop3(perm t)` shortcut — the identity is   *)
  (*    a GF(2^128) REDUCTION fact (both sides = the same field element), not  *)
  (*    a lane shuffle.                                                        *)
  (* NEXT-SESSION ROUTE (algebraic, avoids the byteswap-vs-reduce BITBLAST):   *)
  (* DON'T reduce to a lane-match.  Compose at the polyval_dot / nist_ghash    *)
  (* level like x4 reload_full 1256-1275: bridge each per-block hardware       *)
  (* reduce to `polyval_dot (acc_block) (h_power)` via                         *)
  (* GHASH_REDUCE_RAW_KARATSUBA_IS_DOT (@~2017), accumulate via                *)
  (* GHASH_POLYVAL_ACC_BATCHED, and match the RHS byteswap128(nist_ghash)      *)
  (* through NIST_GHASH_IS_POLYVAL (accumulator passes UNCHANGED — verified).  *)
  (* CAVEAT: after RECON_GRR the LHS is `ghash_reduce_raw P0 P1 P2` where       *)
  (* P0/P1/P2 are word_xor SUMS of all 8 blocks' Karatsuba pieces, so          *)
  (* GHASH_REDUCE_RAW_KARATSUBA_IS_DOT (single a.b product) does NOT fire      *)
  (* directly on the summed lanes — the per-block dot must be established      *)
  (* BEFORE the lanes are summed (i.e. reorganise the fold so each block's     *)
  (* reduce is folded individually), OR find/prove the batched analogue        *)
  (* `ghash_reduce_raw <Sum lo.lo> <Sum cross> <Sum hi.hi> = Sum polyval_dot`. *)
  (*                                                                           *)
  (* SESSION 028 (advisor#2-directed two-sided-strip route) — FALSIFIED, and   *)
  (* the falsification is DECISIVE about the true residual.  Verified LIVE on  *)
  (* the real q19_raw (drivers /tmp/s028_probe.ml, s028_advisor_route.ml,      *)
  (* s028_parity_check.ml):                                                    *)
  (*  * After RECON_GRR + GHASH_REDUCE_RAW_IS_POLYVAL_G2 the goal is           *)
  (*      polyval_reduce_g2 P0 P2 P1  =  byteswap128(nist_ghash ..8(i+1))       *)
  (*    LHS outer head = polyval_reduce_g2 (byteswap-PARITY 0, NO outer        *)
  (*    byteswap); RHS outer head = byteswap128 (parity 1).                    *)
  (*  * Advisor's RHS fold (NIST_GHASH_IS_POLYVAL + GHASH_POLYVAL_ACC_BATCHED, *)
  (*    keeping the byteswap) gives RHS = byteswap128(polyval_reduce_prop3 W_R)*)
  (*    as predicted, BUT the LHS stays bare polyval_reduce_g2 (parity 0);     *)
  (*    BYTESWAP128_G2_PROP3 does NOT fire (its pattern needs                  *)
  (*    byteswap128(polyval_reduce_g2 ..)).  POLYVAL_REDUCE_G2 then gives      *)
  (*      polyval_reduce_prop3 W_L = byteswap128(polyval_reduce_prop3 W_R)      *)
  (*    = EXACTLY the s023 asymmetric "wound" prop3 A = byteswap128(prop3 B).   *)
  (*  * ROOT CAUSE of the parity gap: x4's LHS is byteswap-wrapped (parity 1)  *)
  (*    because x4 has a TRAILING `ext v11` at body-end; x8 has NO trailing    *)
  (*    `ext v19` (objdump s018/019).  x4's two-sided strip (reload_full       *)
  (*    1236-1245 / 1043-1052) REQUIRES both sides byteswap128(..) before      *)
  (*    REWRITE_TAC[byteswap128;..].  x8 cannot reach that: the odd            *)
  (*    byteswap-parity gap is not removable by BS_INVOL/BS_INJ/BS_INVOL2.     *)
  (*  * The true residual `prop3 W_L = byteswap128(prop3 W_R)` is NOT the naive *)
  (*    free-sofar shape: block-0 on the LHS carries (byteswap128 sofar (x)cb0) *)
  (*    while the RHS carries plain (sofar (x) cb0) (s027/s023).  It should be  *)
  (*    TRUE (invariant self-consistent: init/back-edge/exit close; advisor    *)
  (*    verified the invariant is char-identical to x4's working one; KATs     *)
  (*    pass) — the block-0 half-swap must compensate the outer byteswap.      *)
  (*  * BUT: unfolding polyval_reduce_prop3 + BITBLAST is INTRACTABLE (churns   *)
  (*    even on ONE free 256-word — the word_pmul-by-0xC2.. constant is opaque *)
  (*    to BITBLAST; confirmed s028, had to `holctl interrupt`).  And s023     *)
  (*    proved prop3 does NOT commute with byteswap128 under ANY lane perm.    *)
  (*    So neither a lane shuffle (s023 dead) nor a bit-blast closes it.       *)
  (*  * THIS IS THE 3rd advisor/route to hit the SAME byteswap-parity wall     *)
  (*    (lane-shuffle s020-023; flat-sum s025-027; two-sided-strip s028).      *)
  (*    ESCALATED to human (session-028 summary "Questions for human"): the    *)
  (*    remaining obligation is a GF(2^128) field identity                     *)
  (*      prop3(A[block0 = word_xor(byteswap128 sofar) cb0])                    *)
  (*        = byteswap128(prop3(B[block0 = word_xor sofar cb0]))                *)
  (*    where byteswap128 = 64-bit HALF-SWAP (def @polyval_ghash.ml:416, NOT   *)
  (*    a byte reversal).  Likely needs a NEW field-level lemma via            *)
  (*    POLYVAL_REDUCE_PROP3_CORRECT (prop3 t * x^128 == poly_of_word t mod Q) *)
  (*    giving byteswap128 (half-swap) a polynomial meaning — real math, not   *)
  (*    plumbing.  Do NOT open a 4th shortcut route without human direction.   *)
  (* SESSION 029 RESOLUTION (route c, human-directed): the human's diagnosis   *)
  (* was correct — the parity gap was NOT intrinsic; it was the invariant's    *)
  (* byteswap128 wrapper.  Dropping it (plain `read Q19 = nist_ghash..8i` in    *)
  (* pre/inv/post) makes the body-end reduce (parity 0) match the plain RHS     *)
  (* (parity 0), and the fold closes via GHASH_REDUCE_RAW_DIST8_PLAIN + the     *)
  (* flat-sum route with NO byteswap crossing.  See the new Q19_FOLD_TAC above. *)

let AESV8_GCM_8X_ENC_256_WB_MAIN_LOOP = prove
 (`!in_p out_p tag_p ivec_p key_p htable_p mod_p end_p
     tag0 nonce rk inblock nb k pc.
    ~(k = 0) /\
    8 * (k + 1) <= nb /\
    end_p = word_add in_p (word (128 * (k + 1))) /\
    val in_p + 128 * (k + 1) < 2 EXP 63 /\
    nonoverlapping (out_p, 16 * nb)
                   (word pc, LENGTH aesv8_gcm_8x_enc_256_wb_mc) /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * nb)]
      [(in_p, 16 * nb); (key_p, 240); (htable_p, 192);
       (tag_p, 16); (ivec_p, 16); (mod_p, 8)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) aesv8_gcm_8x_enc_256_wb_mc /\
           read PC s = word (pc + 0x4a0) /\
           read X0 s = word_add in_p (word (128 * (0 + 1))) /\
           read X2 s = word_add out_p (word (128 * (0 + 1))) /\
           read X3 s = tag_p /\
           read X4 s = word_add in_p (word (16 * nb)) /\
           read X16 s = ivec_p /\
           read X5 s = end_p /\
           read X6 s = htable_p /\
           read X10 s = mod_p /\
           read X11 s = key_p /\
           read (memory :> bytes64 mod_p) s = word 0xc200000000000000 /\
           read (memory :> bytes128 key_p) s = word_reversefields 8 (EL 0 rk) /\
           read (memory :> bytes128 (word_add key_p (word 16))) s =
             word_reversefields 8 (EL 1 rk) /\
           read (memory :> bytes128 (word_add key_p (word 32))) s =
             word_reversefields 8 (EL 2 rk) /\
           read (memory :> bytes128 (word_add key_p (word 48))) s =
             word_reversefields 8 (EL 3 rk) /\
           read (memory :> bytes128 (word_add key_p (word 64))) s =
             word_reversefields 8 (EL 4 rk) /\
           read (memory :> bytes128 (word_add key_p (word 80))) s =
             word_reversefields 8 (EL 5 rk) /\
           read (memory :> bytes128 (word_add key_p (word 96))) s =
             word_reversefields 8 (EL 6 rk) /\
           read (memory :> bytes128 (word_add key_p (word 112))) s =
             word_reversefields 8 (EL 7 rk) /\
           read (memory :> bytes128 (word_add key_p (word 128))) s =
             word_reversefields 8 (EL 8 rk) /\
           read (memory :> bytes128 (word_add key_p (word 144))) s =
             word_reversefields 8 (EL 9 rk) /\
           read (memory :> bytes128 (word_add key_p (word 160))) s =
             word_reversefields 8 (EL 10 rk) /\
           read (memory :> bytes128 (word_add key_p (word 176))) s =
             word_reversefields 8 (EL 11 rk) /\
           read (memory :> bytes128 (word_add key_p (word 192))) s =
             word_reversefields 8 (EL 12 rk) /\
           read (memory :> bytes128 (word_add key_p (word 208))) s =
             word_reversefields 8 (EL 13 rk) /\
           read (memory :> bytes128 (word_add key_p (word 224))) s =
             word_reversefields 8 (EL 14 rk) /\
           read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce 2) /\
           read Q30 s = word_reversefields 32 (ctr_block nonce (8 * 0 + 15)) /\
           read Q31 s = word 79228162514264337593543950336 /\
           read Q19 s =
             nist_ghash (aes256_cipher (word 0) rk) tag0
                 (list_of_seq (nist_cipher_block nonce rk inblock) (8 * 0)) /\
           read Q8 s = word_xor (aes_ctr_block nonce rk (8 * 0 + 0)) (inblock (8 * 0 + 0)) /\
           read Q9 s = word_xor (aes_ctr_block nonce rk (8 * 0 + 1)) (inblock (8 * 0 + 1)) /\
           read Q10 s = word_xor (aes_ctr_block nonce rk (8 * 0 + 2)) (inblock (8 * 0 + 2)) /\
           read Q11 s = word_xor (aes_ctr_block nonce rk (8 * 0 + 3)) (inblock (8 * 0 + 3)) /\
           read Q12 s = word_xor (aes_ctr_block nonce rk (8 * 0 + 4)) (inblock (8 * 0 + 4)) /\
           read Q13 s = word_xor (aes_ctr_block nonce rk (8 * 0 + 5)) (inblock (8 * 0 + 5)) /\
           read Q14 s = word_xor (aes_ctr_block nonce rk (8 * 0 + 6)) (inblock (8 * 0 + 6)) /\
           read Q15 s = word_xor (aes_ctr_block nonce rk (8 * 0 + 7)) (inblock (8 * 0 + 7)) /\
           read Q0 s = word_reversefields 8 (ctr_block nonce (8 * 0 + 10)) /\
           read Q1 s = word_reversefields 8 (ctr_block nonce (8 * 0 + 11)) /\
           read Q2 s = word_reversefields 8 (ctr_block nonce (8 * 0 + 12)) /\
           read Q3 s = word_reversefields 8 (ctr_block nonce (8 * 0 + 13)) /\
           read Q4 s = word_reversefields 8 (ctr_block nonce (8 * 0 + 14)) /\
           htable_mem_8 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j) /\
           (!j. j < 8 * (0 + 1)
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block nonce rk j) (inblock j)) /\
           ((read NF s <=> read VF s) <=> (0 = k)))
      (\s. aligned_bytes_loaded s (word pc) aesv8_gcm_8x_enc_256_wb_mc /\
           read PC s = word (pc + 0x9f0) /\
           read X0 s = word_add in_p (word (128 * (k + 1))) /\
           read X2 s = word_add out_p (word (128 * (k + 1))) /\
           read X3 s = tag_p /\
           read X4 s = word_add in_p (word (16 * nb)) /\
           read X16 s = ivec_p /\
           read X5 s = end_p /\
           read X6 s = htable_p /\
           read X10 s = mod_p /\
           read X11 s = key_p /\
           read (memory :> bytes64 mod_p) s = word 0xc200000000000000 /\
           read (memory :> bytes128 key_p) s = word_reversefields 8 (EL 0 rk) /\
           read (memory :> bytes128 (word_add key_p (word 16))) s =
             word_reversefields 8 (EL 1 rk) /\
           read (memory :> bytes128 (word_add key_p (word 32))) s =
             word_reversefields 8 (EL 2 rk) /\
           read (memory :> bytes128 (word_add key_p (word 48))) s =
             word_reversefields 8 (EL 3 rk) /\
           read (memory :> bytes128 (word_add key_p (word 64))) s =
             word_reversefields 8 (EL 4 rk) /\
           read (memory :> bytes128 (word_add key_p (word 80))) s =
             word_reversefields 8 (EL 5 rk) /\
           read (memory :> bytes128 (word_add key_p (word 96))) s =
             word_reversefields 8 (EL 6 rk) /\
           read (memory :> bytes128 (word_add key_p (word 112))) s =
             word_reversefields 8 (EL 7 rk) /\
           read (memory :> bytes128 (word_add key_p (word 128))) s =
             word_reversefields 8 (EL 8 rk) /\
           read (memory :> bytes128 (word_add key_p (word 144))) s =
             word_reversefields 8 (EL 9 rk) /\
           read (memory :> bytes128 (word_add key_p (word 160))) s =
             word_reversefields 8 (EL 10 rk) /\
           read (memory :> bytes128 (word_add key_p (word 176))) s =
             word_reversefields 8 (EL 11 rk) /\
           read (memory :> bytes128 (word_add key_p (word 192))) s =
             word_reversefields 8 (EL 12 rk) /\
           read (memory :> bytes128 (word_add key_p (word 208))) s =
             word_reversefields 8 (EL 13 rk) /\
           read (memory :> bytes128 (word_add key_p (word 224))) s =
             word_reversefields 8 (EL 14 rk) /\
           read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce 2) /\
           read Q30 s = word_reversefields 32 (ctr_block nonce (8 * k + 15)) /\
           read Q31 s = word 79228162514264337593543950336 /\
           read Q19 s =
             nist_ghash (aes256_cipher (word 0) rk) tag0
                 (list_of_seq (nist_cipher_block nonce rk inblock) (8 * k)) /\
           read Q8 s = word_xor (aes_ctr_block nonce rk (8 * k + 0)) (inblock (8 * k + 0)) /\
           read Q9 s = word_xor (aes_ctr_block nonce rk (8 * k + 1)) (inblock (8 * k + 1)) /\
           read Q10 s = word_xor (aes_ctr_block nonce rk (8 * k + 2)) (inblock (8 * k + 2)) /\
           read Q11 s = word_xor (aes_ctr_block nonce rk (8 * k + 3)) (inblock (8 * k + 3)) /\
           read Q12 s = word_xor (aes_ctr_block nonce rk (8 * k + 4)) (inblock (8 * k + 4)) /\
           read Q13 s = word_xor (aes_ctr_block nonce rk (8 * k + 5)) (inblock (8 * k + 5)) /\
           read Q14 s = word_xor (aes_ctr_block nonce rk (8 * k + 6)) (inblock (8 * k + 6)) /\
           read Q15 s = word_xor (aes_ctr_block nonce rk (8 * k + 7)) (inblock (8 * k + 7)) /\
           read Q0 s = word_reversefields 8 (ctr_block nonce (8 * k + 10)) /\
           read Q1 s = word_reversefields 8 (ctr_block nonce (8 * k + 11)) /\
           read Q2 s = word_reversefields 8 (ctr_block nonce (8 * k + 12)) /\
           read Q3 s = word_reversefields 8 (ctr_block nonce (8 * k + 13)) /\
           read Q4 s = word_reversefields 8 (ctr_block nonce (8 * k + 14)) /\
           htable_mem_8 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j) /\
           (!j. j < 8 * (k + 1)
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block nonce rk j) (inblock j)))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * nb)])`,
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; ALLPAIRS; ALL] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_WHILE_PUP_TAC `k:num` `pc + 0x4a0` `pc + 0x9ec`
    `\i s. (read X0 s = word_add in_p (word (128 * (i + 1))) /\
            read X2 s = word_add out_p (word (128 * (i + 1))) /\
            read X3 s = tag_p /\
            read X4 s = word_add in_p (word (16 * nb)) /\
            read X16 s = ivec_p /\
            read X5 s = end_p /\
            read X6 s = htable_p /\
            read X10 s = mod_p /\
            read X11 s = key_p /\
            read (memory :> bytes64 mod_p) s = word 0xc200000000000000 /\
            read (memory :> bytes128 key_p) s = word_reversefields 8 (EL 0 rk) /\
            read (memory :> bytes128 (word_add key_p (word 16))) s =
              word_reversefields 8 (EL 1 rk) /\
            read (memory :> bytes128 (word_add key_p (word 32))) s =
              word_reversefields 8 (EL 2 rk) /\
            read (memory :> bytes128 (word_add key_p (word 48))) s =
              word_reversefields 8 (EL 3 rk) /\
            read (memory :> bytes128 (word_add key_p (word 64))) s =
              word_reversefields 8 (EL 4 rk) /\
            read (memory :> bytes128 (word_add key_p (word 80))) s =
              word_reversefields 8 (EL 5 rk) /\
            read (memory :> bytes128 (word_add key_p (word 96))) s =
              word_reversefields 8 (EL 6 rk) /\
            read (memory :> bytes128 (word_add key_p (word 112))) s =
              word_reversefields 8 (EL 7 rk) /\
            read (memory :> bytes128 (word_add key_p (word 128))) s =
              word_reversefields 8 (EL 8 rk) /\
            read (memory :> bytes128 (word_add key_p (word 144))) s =
              word_reversefields 8 (EL 9 rk) /\
            read (memory :> bytes128 (word_add key_p (word 160))) s =
              word_reversefields 8 (EL 10 rk) /\
            read (memory :> bytes128 (word_add key_p (word 176))) s =
              word_reversefields 8 (EL 11 rk) /\
            read (memory :> bytes128 (word_add key_p (word 192))) s =
              word_reversefields 8 (EL 12 rk) /\
            read (memory :> bytes128 (word_add key_p (word 208))) s =
              word_reversefields 8 (EL 13 rk) /\
            read (memory :> bytes128 (word_add key_p (word 224))) s =
              word_reversefields 8 (EL 14 rk) /\
            read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
            read (memory :> bytes128 ivec_p) s =
              word_reversefields 8 (ctr_block nonce 2) /\
            read Q30 s = word_reversefields 32 (ctr_block nonce (8 * i + 15)) /\
            read Q31 s = word 79228162514264337593543950336 /\
            read Q19 s =
              nist_ghash (aes256_cipher (word 0) rk) tag0
                  (list_of_seq (nist_cipher_block nonce rk inblock) (8 * i)) /\
            read Q8 s = word_xor (aes_ctr_block nonce rk (8 * i + 0)) (inblock (8 * i + 0)) /\
            read Q9 s = word_xor (aes_ctr_block nonce rk (8 * i + 1)) (inblock (8 * i + 1)) /\
            read Q10 s = word_xor (aes_ctr_block nonce rk (8 * i + 2)) (inblock (8 * i + 2)) /\
            read Q11 s = word_xor (aes_ctr_block nonce rk (8 * i + 3)) (inblock (8 * i + 3)) /\
            read Q12 s = word_xor (aes_ctr_block nonce rk (8 * i + 4)) (inblock (8 * i + 4)) /\
            read Q13 s = word_xor (aes_ctr_block nonce rk (8 * i + 5)) (inblock (8 * i + 5)) /\
            read Q14 s = word_xor (aes_ctr_block nonce rk (8 * i + 6)) (inblock (8 * i + 6)) /\
            read Q15 s = word_xor (aes_ctr_block nonce rk (8 * i + 7)) (inblock (8 * i + 7)) /\
            read Q0 s = word_reversefields 8 (ctr_block nonce (8 * i + 10)) /\
            read Q1 s = word_reversefields 8 (ctr_block nonce (8 * i + 11)) /\
            read Q2 s = word_reversefields 8 (ctr_block nonce (8 * i + 12)) /\
            read Q3 s = word_reversefields 8 (ctr_block nonce (8 * i + 13)) /\
            read Q4 s = word_reversefields 8 (ctr_block nonce (8 * i + 14)) /\
            htable_mem_8 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s /\
            (!j. j < nb
                 ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                     inblock j) /\
            (!j. j < 8 * (i + 1)
                 ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                     word_xor (aes_ctr_block nonce rk j) (inblock j))) /\
           ((read NF s <=> read VF s) <=> (i = k))` THEN
  REWRITE_TAC[htable_mem_8] THEN
  REPEAT CONJ_TAC THENL
   [(* Subgoal 1: 0 < k *)
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;

    (* Subgoal 2: init -- reflexive 0-step (precondition = p 0 at pc+0x498) *)
    ENSURES_INIT_TAC "s0" THEN
    RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_8]) THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[];

    (* Subgoal 3: body -- 339-instr fused GHASH+AES pipeline.                     *)
    (* SESSION 011: the full body now STEPS THROUGH to ENSURES_FINAL_STATE_TAC     *)
    (* with ALL EIGHT ciphertext register facts (read Q8..Q15 s339) intact — the  *)
    (* long-standing "Q11..Q15 facts vanish" blocker is SOLVED (see the           *)
    (* LDP_STEP4_TAC helper above: the ldp 2nd-element read addresses needed a     *)
    (* word_add-flatten + offset-arithmetic reduction to match the input-block     *)
    (* reads, else DISCARD_OLDSTATE dropped them).  Step count is (1--339): the    *)
    (* b.lt@0x9e4 (step 340) is the PUP back-edge (subgoals 4&5), NOT the body.    *)
    (* The 4 plaintext reloads are ldp q,q,[x0],#32 at steps 263/295/303/304;      *)
    (* the first resolves natively, the 3 incremented ones use LDP_STEP4_TAC.      *)
    (*                                                                             *)
    (* SESSION 015: FIXED the +2 counter mismatch — the loop-carried register     *)
    (* counter pins (Q0..Q4, Q30) were off by +2 (empirically: v0 physically =     *)
    (* ctr_block nonce (8i+10) = block 8i+8, but the invariant pinned ctr(8i+8)).  *)
    (* Setup does 13 `add v30` increments; at loop entry v0=ctr(8i+10),..,          *)
    (* v4=ctr(8i+14), Q30=ctr(8i+15).  Pins shifted +2 in pre/inv/post; init/       *)
    (* back-edge/exit re-close (full file reloads clean).  The out-forall stays in  *)
    (* block-index aes_ctr_block form (matches proven x4) — it was correct.        *)
    (*                                                                             *)
    (* REMAINING (CHEAT below): TWO obligations.                                    *)
    (* (1) INCOMING OUT-FORALL preservation across the 4 ciphertext stores.        *)
    (*     `stp q,q,[x2],#32` at steps 330/334/337/338 (pc 0x9bc/9cc/9d8/9dc) write *)
    (*     NEW blocks 8i+8..8i+15.  The invariant-at-i out-forall (`!j.j<8*(i+1)==> *)
    (*     read(out+16j) s = word_xor(aes_ctr_block nonce rk j)(inblock j)`) is     *)
    (*     ADVANCED s->s' at every non-store step (like the input-forall, which     *)
    (*     survives all 339 steps to s339) but DROPPED at the first store: the      *)
    (*     stepper cannot advance a quantified read over the out_p buffer it writes *)
    (*     (per-j disjointness 16j != 128(i+1)+off for j<8i+8 is nonlinear, not     *)
    (*     auto-dischargeable under the !j binder), so DISCARD_OLDSTATE_TAC erases  *)
    (*     it (it still refs the OLD state s329).  CONFIRMED (session 015):         *)
    (*     ARM_VERBOSE_STEP_TAC "s330" (no auto-discard) PRESERVES it (count=1);    *)
    (*     it is DISCARD_OLDSTATE that drops it.  A pre-store SUBGOAL pin does NOT  *)
    (*     survive either (same mechanism).  FIX (LDP_STEP4_TAC analogue for the    *)
    (*     stp stores): at each store use ARM_VERBOSE_STEP_TAC, then ADVANCE the    *)
    (*     out-forall's read s_{n-1}->s_n under the !j binder via read-over-write   *)
    (*     orthogonality (COMPONENT_READ_OVER_WRITE_CONV / the bytes128 store       *)
    (*     component vs out_p+16j, supplying 16j<128(i+1) from j<8*(i+1) minus the  *)
    (*     8 new indices), re-ASSUME the advanced out-forall, THEN DISCARD_OLDSTATE.*)
    (*     The 8 NEW-block store facts survive concretely at s339 (verified) so     *)
    (*     new blocks close via the case-split; only OLD blocks need this.          *)
    (* (2) Q19 GHASH fold (~367k chars): x4 reload_full 1043-1107 scaled 4->8 —     *)
    (*     byteswap128 BITBLAST wrapper, MAP_EVERY ABBREV_TAC                        *)
    (*     sofar/cipherblock_0..7/h0..h7, TRANS_TAC EQ_TRANS to                     *)
    (*     polyval_reduce_prop3(<8-term pmul chain>), PMUL_KARATSUBA_JOIN_ALT +     *)
    (*     karatsuba_mid + POLYVAL_REDUCE_G2 + BITBLAST, then                       *)
    (*     GHASH_POLYVAL_ACC_BATCHED [cipherblock_1..7] + NIST_GHASH_IS_POLYVAL +   *)
    (*     list_of_seq (8*i+8 = SUC^8 (8*i)) + GHASH_ACC_APPEND.                    *)
    (* Cheap conjuncts (X-regs, keys/htable/tag/ivec mem, Q30/Q31, Q0..Q4 counter, *)
    (* Q8..Q15 ciphertext, NEW out-blocks, flag, PC) close via S014_CHEAP3         *)
    (* (/tmp/s014_cheap3.ml): case-split bound 8*((i+1)+1), eor3 WORD_BITWISE_RULE  *)
    (* AC-normalize, CTR_BLOCK_RECONSTRUCT_REV8/REV32 + WORD_SUBWORD_* +            *)
    (* XOR_AES256_CIPHER_RECONSTRUCT + AES_CTR_BLOCK_RECONSTRUCT + FIRST_ASSUM      *)
    (* MATCH + WORD_RULE/ARITH — re-validate against the +2-corrected goal.         *)
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    SUBGOAL_THEN
     `read (memory :> bytes128 (word_add in_p (word (128 * (i + 1))))) s0 =
      inblock (8 * (i + 1)) /\
      read (memory :> bytes128 (word_add in_p (word (128 * (i + 1) + 16)))) s0 =
      inblock (8 * (i + 1) + 1) /\
      read (memory :> bytes128 (word_add in_p (word (128 * (i + 1) + 32)))) s0 =
      inblock (8 * (i + 1) + 2) /\
      read (memory :> bytes128 (word_add in_p (word (128 * (i + 1) + 48)))) s0 =
      inblock (8 * (i + 1) + 3) /\
      read (memory :> bytes128 (word_add in_p (word (128 * (i + 1) + 64)))) s0 =
      inblock (8 * (i + 1) + 4) /\
      read (memory :> bytes128 (word_add in_p (word (128 * (i + 1) + 80)))) s0 =
      inblock (8 * (i + 1) + 5) /\
      read (memory :> bytes128 (word_add in_p (word (128 * (i + 1) + 96)))) s0 =
      inblock (8 * (i + 1) + 6) /\
      read (memory :> bytes128 (word_add in_p (word (128 * (i + 1) + 112)))) s0 =
      inblock (8 * (i + 1) + 7)`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[ARITH_RULE
       `128 * (i + 1) + 16 = 16 * (8 * (i + 1) + 1) /\
        128 * (i + 1) + 32 = 16 * (8 * (i + 1) + 2) /\
        128 * (i + 1) + 48 = 16 * (8 * (i + 1) + 3) /\
        128 * (i + 1) + 64 = 16 * (8 * (i + 1) + 4) /\
        128 * (i + 1) + 80 = 16 * (8 * (i + 1) + 5) /\
        128 * (i + 1) + 96 = 16 * (8 * (i + 1) + 6) /\
        128 * (i + 1) + 112 = 16 * (8 * (i + 1) + 7)`] THEN
      REWRITE_TAC[ARITH_RULE `128 * a = 16 * 8 * a`] THEN
      REPEAT CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[REWRITE_CONV[fst AESV8_GCM_8X_ENC_256_WB_EXEC]
      `LENGTH aesv8_gcm_8x_enc_256_wb_mc`]) THEN
    MAP_EVERY NSTEP_G (1--294) THEN
    LDP_STEP4_TAC 295 THEN
    MAP_EVERY NSTEP_G (296--302) THEN
    LDP_STEP4_TAC 303 THEN
    LDP_STEP4_TAC 304 THEN
    MAP_EVERY NSTEP_G (305--339) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    (* --- Cheap-conjunct close (session 016): validates the +2 counter fix.    *)
    (* The case-split bound is 8*((i+1)+1) (invariant out-forall at i is         *)
    (* j<8*(i+1), so at i+1 it is j<8*(i+2)); the eor3 3-way store XOR is        *)
    (* AC-normalized to the XOR_AES256_CIPHER_RECONSTRUCT shape; then            *)
    (* AES256_CIPHER_KEYLIST collapses the residual explicit key list            *)
    (* `[EL 0 rk;..;EL 14 rk]` back to `rk` (the piece prior sessions missed —   *)
    (* XOR_AES256_CIPHER_RECONSTRUCT + MAP leaves the list, not `rk`).           *)
    (* SESSION 022 RESTRUCTURE: split the RAW post-FINAL_STATE conjunction     *)
    (* FIRST (before the cheap-close), so the Q19 GHASH-fold conjunct can be    *)
    (* folded while its ext/LO structure is intact.  Session 022 CONFIRMED the  *)
    (* cheap-close's WORD_SIMPLE_SUBWORD_CONV DESTROYS Q19's foldability (the    *)
    (* GSYM ghash_reduce_raw fold-back fails post-cheap-close), so Q19 MUST be   *)
    (* peeled off before it runs.  `REPEAT CONJ_TAC` yields 20 atomic goals     *)
    (* (18 cheap + 1 Q19 + 1 flag); the per-goal dispatcher routes each:        *)
    (*   - Q19 (is_eq, RHS headed by byteswap128): Q19_FOLD_TAC (genuine down   *)
    (*     to the final lane-match, which is CHEAT'd inside Q19_FOLD_TAC);       *)
    (*   - everything else: the cheap-close rewrites (which also handle the      *)
    (*     out-forall case-split), then a nested split + flag-close / CHEAT for  *)
    (*     the out-forall (blocker B, advisor-gated).                           *)
    REPEAT CONJ_TAC THEN
    (fun (asl,w as gl) ->
      if is_eq w &&
         (try fst(dest_const(fst(strip_comb(rhs w)))) = "nist_ghash"
          with _ -> false)
      then Q19_FOLD_TAC gl
      else
       (REWRITE_TAC[ARITH_RULE `j < 8 * ((i + 1) + 1) <=>
                            j < 8 * (i+1) \/ j = 8*(i+1) \/ j = 8*(i+1) + 1 \/
                            j = 8*(i+1) + 2 \/ j = 8*(i+1) + 3 \/ j = 8*(i+1) + 4 \/
                            j = 8*(i+1) + 5 \/ j = 8*(i+1) + 6 \/ j = 8*(i+1) + 7`] THEN
        ASM_REWRITE_TAC[TAUT `p \/ q ==> r <=> (p ==> r) /\ (q ==> r)`] THEN
        REWRITE_TAC[FORALL_AND_THM; FORALL_UNWIND_THM2] THEN
        REWRITE_TAC[ARITH_RULE `16 * (8 * (i+1) + b) = 128 * (i+1) + 16 * b`] THEN
        REWRITE_TAC[ARITH_RULE `16 * 8 * (i+1) = 128 * (i+1)`] THEN
        CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[WORD_SUBWORD_REVERSEFIELDS_32; WORD_SUBWORD_CTR_BLOCK_32] THEN
        REWRITE_TAC[GSYM WORD_ADD; WORD_ADD_0] THEN
        REWRITE_TAC[CTR_BLOCK_RECONSTRUCT_REV8; CTR_BLOCK_RECONSTRUCT_REV32] THEN
        ONCE_REWRITE_TAC[WORD_BITWISE_RULE
          `word_xor (word_xor (inb:int128) ch) rk14 =
           word_xor ch (word_xor rk14 inb)`] THEN
        REWRITE_TAC[XOR_AES256_CIPHER_RECONSTRUCT] THEN
        ASM_REWRITE_TAC[MAP; WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
        REWRITE_TAC[aes_ctr_block; GSYM ADD_ASSOC] THEN
        CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[LEFT_ADD_DISTRIB; GSYM ADD_ASSOC] THEN
        CONV_TAC NUM_REDUCE_CONV THEN
        REWRITE_TAC[WORD_ADD; GSYM WORD_ADD_ASSOC] THEN
        ASM_SIMP_TAC[WORD_SUB; LT_IMP_LE; ARITH_RULE `i < l ==> i + 1 <= l`] THEN
        REWRITE_TAC[ADD_ASSOC; ARITH] THEN
        REWRITE_TAC[AES_CTR_BLOCK_RECONSTRUCT] THEN
        REWRITE_TAC[GSYM cipher_block] THEN
        REWRITE_TAC[CIPHER_BLOCK_NIST] THEN
        REWRITE_TAC[WORD_SUBWORD_REVERSEFIELDS] THEN
        SIMP_TAC[WORD_JOIN_COMBINE_LEMMA; ARITH] THEN
        REWRITE_TAC[WORD_SUBWORD_XOR] THEN
        REWRITE_TAC[WORD_SUBWORD_BYTESWAP128] THEN
        CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
        REWRITE_TAC[WORD_SUBWORD_XOR] THEN
        CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
        REPEAT(CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC]) THEN
        REWRITE_TAC[AES256_CIPHER_KEYLIST]) gl) THEN
    (* --- Remaining after the split-first dispatcher (session 022):             *)
    (* the ~18 cheap conjuncts + all 16 ciphertext out-blocks CLOSE (validating  *)
    (* the +2 counter fix end-to-end).  Three obligations remain, TWO now GONE:  *)
    (*   (A) Q19 GHASH fold: NOW WIRED via NSTEP_G + the split-first dispatcher   *)
    (*       + Q19_FOLD_TAC (above), which folds the raw body-end reduce all the  *)
    (*       way to the final lane-match `byteswap128(prop3 A)=prop3 B` — that    *)
    (*       ONE lane-identity is the sole remaining CHEAT of blocker A (inside   *)
    (*       Q19_FOLD_TAC).  Everything from the raw ghash reduce down to the     *)
    (*       lane-match is genuinely proved (5-session Q19 dead-end resolved).    *)
    (*   (B) OLD out-forall (!j. j<8*(i+1) ==> read(out+16j) s = ...): the        *)
    (*       incoming invariant out-forall is DROPPED by ASSUMPTION_STATE_UPDATE  *)
    (*       at the first ciphertext store (step 330).  ROOT CAUSE (session 016): *)
    (*       ASSUMPTION_STATE_UPDATE_TAC advances an assumption over a store via  *)
    (*       STATE_UPDATE_RULE -> COMPONENTS_READ_OVER_WRITE_ORTHOGONAL_CONV,     *)
    (*       which DOES descend under the !j binder AND collects the antecedent   *)
    (*       j<8*(i+1) into its context (components.ml:3203) — BUT it then needs  *)
    (*       ORTHOGONAL_COMPONENTS_RULE to discharge orthogonality of             *)
    (*       bytes128(out_p+16*j) vs the store at bytes128(out_p+128*(i+1)),      *)
    (*       which requires the NONLINEAR bound 16*(j+1)<=128*(i+1) from          *)
    (*       j<8*(i+1); the driver machinery does not derive it for a SYMBOLIC    *)
    (*       product offset, so the update fails and the forall is erased.  This  *)
    (*       is genuinely novel: every existing s2n proof (e.g. emontredc) that   *)
    (*       advances a quantified memory forall over a store uses a FIXED unroll *)
    (*       and EXPAND_CASES_CONV to concrete indices; the x8 out-forall bound   *)
    (*       8*(i+1) is symbolic in i and cannot be expanded.  Needs either a     *)
    (*       symbolic-index bytes128 orthogonality lemma fed to the conv, or a    *)
    (*       reformulation.  (verbose-step PRESERVES the s329-ref forall; it is   *)
    (*       the subsequent DISCARD_OLDSTATE of the following NSTEP that drops it.)*)
    (*   (C) FLAG/PC-branch fact: the invariant q(i+1) = ((NF<=>VF)<=>(i+1=k))    *)
    (*       cannot close because MAIN_LOOP's antecedent does NOT constrain        *)
    (*       end_p.  Derived (session 016) from the .S setup (0x34-0x4c) + the    *)
    (*       body cmp@0x978 (X0=in_p+128*(i+2) at the cmp): the missing hyp is    *)
    (*       `end_p = word_add in_p (word (128 * (k + 1)))` (+ a k bound for the  *)
    (*       signed cmp no-overflow).  word_sub cancels in_p, leaving a pure      *)
    (*       k-bounded word fact.  This is a real invariant-completeness gap      *)
    (*       (like s008's v8..v15 and s015's +2) — add the end_p antecedent and   *)
    (*       re-close init/back-edge/exit; reconcile with P7 setup / P9 (end_p    *)
    (*       is how the iteration count k is pinned).                             *)
    (* SESSION 017: (C) is now CLOSED.  Added the two end_p antecedents to        *)
    (* MAIN_LOOP (`end_p = word_add in_p (word (128*(k+1)))` and the no-wrap      *)
    (* bound `val in_p + 128*(k+1) < 2 EXP 63`) and the BRIDGE_GE/IV_ADD lemmas   *)
    (* above.  The residual is A /\ C /\ B (Q19 fold / flag / out-forall+frame),  *)
    (* split by REPEAT CONJ_TAC.  The cheap-close's WORD_ADD normalisation splits *)
    (* the flag offsets to `word_add (word (128*i)) (word 256)` (= X0 = in_p +    *)
    (* 128*(i+2)) and `word_add (word (128*k)) (word 128)` (= end_p, already      *)
    (* substituted by ASM_REWRITE), so the flag close does NOT match FLAG_LEM     *)
    (* syntactically — instead it rewrites BRIDGE_GE (the NF!=VF biconditional =  *)
    (* signed GE `ival end_p <= ival X0`), linearises both additive ivals with    *)
    (* IV_ADD under the no-wrap bound, and finishes by INT/ARITH using `i < k`.   *)
    (* FLAG_LEM (above) packages the same reasoning for the un-normalised shape   *)
    (* and is kept as documentation.  A (Q19 fold) and B (OLD out-forall) still   *)
    (* CHEAT (B advisor-gated).                                                   *)
    REPEAT CONJ_TAC THEN
    (* Guard: fire the flag close ONLY on the flag-shaped goal — the sole
       residual whose conclusion is `<flag biconditional> <=> (i + 1 = k)`
       (RHS = `i + 1 = k`).  This keeps BRIDGE_GE off the ~186k-char Q19 term  *)
    (* (resid A).  CRITICAL: the flag arithmetic uses targeted UNDISCH_TAC of   *)
    (* the two needed hyps (`i < k`, the no-wrap bound) + bare ARITH_TAC — NOT  *)
    (* ASM_ARITH_TAC, which would scan every hyp (incl. the giant ciphertext/   *)
    (* Q19 facts) and wedge the checker (see holctl-operational-gotchas).       *)
    (let flag_arith =
       UNDISCH_TAC `val(in_p:int64) + 128 * (k + 1) < 2 EXP 63` THEN
       UNDISCH_TAC `(i:num) < k` THEN ARITH_TAC in
     fun (asl,w as gl) ->
       (if (can (term_match [] `xxx:bool <=> (i:num) + 1 = k`) w)
        then
         (REWRITE_TAC[BRIDGE_GE] THEN
          MP_TAC(SPECL [`in_p:int64`; `128 * i + 256`] IV_ADD) THEN
          ANTS_TAC THENL [flag_arith; ALL_TAC] THEN
          MP_TAC(SPECL [`in_p:int64`; `128 * k + 128`] IV_ADD) THEN
          ANTS_TAC THENL [flag_arith; ALL_TAC] THEN
          REWRITE_TAC[GSYM WORD_ADD] THEN
          DISCH_THEN SUBST1_TAC THEN DISCH_THEN SUBST1_TAC THEN
          REWRITE_TAC[INT_OF_NUM_LE] THEN flag_arith)
        (* BLOCKER B RESOLVED (session 030): the sole residual reaching this
           branch is the MAYCHANGE FRAME-subsumption goal `(<accumulated>) s0
           s339` (NOT the out-forall — that closes in the first dispatcher's
           cheap-close, since it SURVIVES to s339: re-observed s030, the
           s015/016 "dropped at store 330" finding was stale).  The body
           physically clobbers the FULL Q8..Q15 (the in-flight ciphertext
           blocks), whose low 64 bits the ABI frame forbids (v8-v15 are
           callee-saved).  The MAIN_LOOP conclusion frame was therefore
           widened with `MAYCHANGE [Q8;..;Q15]` (mirroring the proved x4
           kernel aes_gcm_enc_kernel_x4_reload_round_keys_full.ml:764); the
           low-half writes are restored by the d8-d15 epilogue at the
           subroutine wrapper (P10).  With the widened frame,
           MONOTONE_MAYCHANGE_TAC discharges the subsumption (the 8 ciphertext
           stores bytes128(out_p+128*(i+1)+16m) <= bytes(out_p,16*nb) follow
           from the `8*(k+1)<=nb` antecedent via CONTAINED_TAC).  *)
        else MONOTONE_MAYCHANGE_TAC) gl);

    (* Subgoal 4: back-edge taken (0 < i < k => b.lt branches back) *)
    REPEAT STRIP_TAC THEN
    ARM_SIM_TAC AESV8_GCM_8X_ENC_256_WB_EXEC [1] THEN
    ASM_REWRITE_TAC[];

    (* Subgoal 5: exit fall-through (i = k => GE, b.lt not taken) *)
    REPEAT STRIP_TAC THEN
    ARM_SIM_TAC AESV8_GCM_8X_ENC_256_WB_EXEC [1] THEN
    ASM_REWRITE_TAC[]]);;

