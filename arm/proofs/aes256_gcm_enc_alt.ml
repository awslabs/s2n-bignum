(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* AES-256-GCM 8x whole-blocks encrypt kernel aes256_gcm_enc_alt.       *)
(*                                                                           *)
(* Correctness and safety proofs for the kernel derived from AWS-LC's        *)
(* aesv8_gcm_8x_enc_256.  The input bit length must be a multiple of 128     *)
(* (a runtime guard returns 0 otherwise), so there is no partial-final-block *)
(* masking.  Stated in the shared AES-GCM vocabulary of                      *)
(* arm/proofs/utils/aes_gcm_spec.ml.  The theorems are proved for the code   *)
(* without the BTI landing pad and lifted over it with ARM_ADD_IBT_RULE.     *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

needs "arm/proofs/utils/aes_gcm_common.ml";;

(* ------------------------------------------------------------------------- *)
(* The machine code.                                                         *)
(* ------------------------------------------------------------------------- *)

(* print_literal_from_elf "arm/aes_gcm/aes256_gcm_enc_alt.o";;          *)

let aes256_gcm_enc_alt_mc =
  define_assert_from_elf "aes256_gcm_enc_alt_mc"
                         "arm/aes_gcm/aes256_gcm_enc_alt.o"
[
  0xd503245f;       (* arm_BTI *)
  0xb4008b81;       (* arm_CBZ X1 (word 4464) *)
  0xf240183f;       (* arm_TST X1 (rvalue (word 127)) *)
  0x54008b41;       (* arm_BNE (word 4456) *)
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
  0xf101013f;       (* arm_CMP X9 (rvalue (word 64)) *)
  0x5400a4ad;       (* arm_BLE (word 5268) *)
  0x4ebf87fc;       (* arm_ADD_VEC Q28 Q31 Q31 32 128 *)
  0x4ebf878a;       (* arm_ADD_VEC Q10 Q28 Q31 32 128 *)
  0x4ebc878b;       (* arm_ADD_VEC Q11 Q28 Q28 32 128 *)
  0x4ebf856c;       (* arm_ADD_VEC Q12 Q11 Q31 32 128 *)
  0x4ebc856d;       (* arm_ADD_VEC Q13 Q11 Q28 32 128 *)
  0x4eaa856e;       (* arm_ADD_VEC Q14 Q11 Q10 32 128 *)
  0xd10004a5;       (* arm_SUB X5 X5 (rvalue (word 1)) *)
  0x9279e0a5;       (* arm_AND X5 X5 (rvalue (word 18446744073709551488)) *)
  0x8b0000a5;       (* arm_ADD X5 X5 X0 *)
  0x6e20081d;       (* arm_REV32_VEC Q29 Q0 8 *)
  0x4ebf87a8;       (* arm_ADD_VEC Q8 Q29 Q31 32 128 *)
  0x4ebc87a9;       (* arm_ADD_VEC Q9 Q29 Q28 32 128 *)
  0x4eaa87af;       (* arm_ADD_VEC Q15 Q29 Q10 32 128 *)
  0x4eab87b0;       (* arm_ADD_VEC Q16 Q29 Q11 32 128 *)
  0x4eac87b1;       (* arm_ADD_VEC Q17 Q29 Q12 32 128 *)
  0x4ead87b2;       (* arm_ADD_VEC Q18 Q29 Q13 32 128 *)
  0x4eae87be;       (* arm_ADD_VEC Q30 Q29 Q14 32 128 *)
  0x6e200901;       (* arm_REV32_VEC Q1 Q8 8 *)
  0x6e200922;       (* arm_REV32_VEC Q2 Q9 8 *)
  0x6e2009e3;       (* arm_REV32_VEC Q3 Q15 8 *)
  0x6e200a04;       (* arm_REV32_VEC Q4 Q16 8 *)
  0x6e200a25;       (* arm_REV32_VEC Q5 Q17 8 *)
  0x6e200a46;       (* arm_REV32_VEC Q6 Q18 8 *)
  0x6e200bc7;       (* arm_REV32_VEC Q7 Q30 8 *)
  0xad406d7a;       (* arm_LDP Q26 Q27 X11 (Immediate_Offset (iword (&0))) *)
  0x4c407073;       (* arm_LDR Q19 X3 No_Offset *)
  0x6e134273;       (* arm_EXT Q19 Q19 Q19 64 *)
  0x4e200a73;       (* arm_REV64_VEC Q19 Q19 8 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b41;       (* arm_AESE Q1 Q26 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b42;       (* arm_AESE Q2 Q26 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b43;       (* arm_AESE Q3 Q26 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b44;       (* arm_AESE Q4 Q26 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b45;       (* arm_AESE Q5 Q26 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b46;       (* arm_AESE Q6 Q26 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b47;       (* arm_AESE Q7 Q26 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0xad41697c;       (* arm_LDP Q28 Q26 X11 (Immediate_Offset (iword (&32))) *)
  0x4e284b60;       (* arm_AESE Q0 Q27 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b61;       (* arm_AESE Q1 Q27 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b62;       (* arm_AESE Q2 Q27 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b63;       (* arm_AESE Q3 Q27 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b64;       (* arm_AESE Q4 Q27 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b65;       (* arm_AESE Q5 Q27 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b66;       (* arm_AESE Q6 Q27 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b67;       (* arm_AESE Q7 Q27 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b80;       (* arm_AESE Q0 Q28 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b81;       (* arm_AESE Q1 Q28 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b82;       (* arm_AESE Q2 Q28 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b83;       (* arm_AESE Q3 Q28 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b84;       (* arm_AESE Q4 Q28 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b85;       (* arm_AESE Q5 Q28 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b86;       (* arm_AESE Q6 Q28 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b87;       (* arm_AESE Q7 Q28 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0xad42717b;       (* arm_LDP Q27 Q28 X11 (Immediate_Offset (iword (&64))) *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b41;       (* arm_AESE Q1 Q26 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b42;       (* arm_AESE Q2 Q26 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b43;       (* arm_AESE Q3 Q26 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b44;       (* arm_AESE Q4 Q26 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b45;       (* arm_AESE Q5 Q26 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b46;       (* arm_AESE Q6 Q26 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b47;       (* arm_AESE Q7 Q26 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b60;       (* arm_AESE Q0 Q27 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b61;       (* arm_AESE Q1 Q27 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b62;       (* arm_AESE Q2 Q27 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b63;       (* arm_AESE Q3 Q27 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b64;       (* arm_AESE Q4 Q27 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b65;       (* arm_AESE Q5 Q27 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b66;       (* arm_AESE Q6 Q27 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b67;       (* arm_AESE Q7 Q27 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0xad436d7a;       (* arm_LDP Q26 Q27 X11 (Immediate_Offset (iword (&96))) *)
  0x4e284b80;       (* arm_AESE Q0 Q28 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b81;       (* arm_AESE Q1 Q28 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b82;       (* arm_AESE Q2 Q28 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b83;       (* arm_AESE Q3 Q28 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b84;       (* arm_AESE Q4 Q28 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b85;       (* arm_AESE Q5 Q28 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b86;       (* arm_AESE Q6 Q28 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b87;       (* arm_AESE Q7 Q28 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b41;       (* arm_AESE Q1 Q26 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b42;       (* arm_AESE Q2 Q26 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b43;       (* arm_AESE Q3 Q26 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b44;       (* arm_AESE Q4 Q26 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b45;       (* arm_AESE Q5 Q26 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b46;       (* arm_AESE Q6 Q26 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b47;       (* arm_AESE Q7 Q26 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0xad44697c;       (* arm_LDP Q28 Q26 X11 (Immediate_Offset (iword (&128))) *)
  0x4e284b60;       (* arm_AESE Q0 Q27 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b61;       (* arm_AESE Q1 Q27 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b62;       (* arm_AESE Q2 Q27 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b63;       (* arm_AESE Q3 Q27 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b64;       (* arm_AESE Q4 Q27 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b65;       (* arm_AESE Q5 Q27 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b66;       (* arm_AESE Q6 Q27 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b67;       (* arm_AESE Q7 Q27 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b80;       (* arm_AESE Q0 Q28 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b81;       (* arm_AESE Q1 Q28 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b82;       (* arm_AESE Q2 Q28 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b83;       (* arm_AESE Q3 Q28 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b84;       (* arm_AESE Q4 Q28 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b85;       (* arm_AESE Q5 Q28 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b86;       (* arm_AESE Q6 Q28 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b87;       (* arm_AESE Q7 Q28 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0xad45717b;       (* arm_LDP Q27 Q28 X11 (Immediate_Offset (iword (&160))) *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b41;       (* arm_AESE Q1 Q26 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b42;       (* arm_AESE Q2 Q26 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b43;       (* arm_AESE Q3 Q26 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b44;       (* arm_AESE Q4 Q26 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b45;       (* arm_AESE Q5 Q26 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b46;       (* arm_AESE Q6 Q26 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b47;       (* arm_AESE Q7 Q26 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b60;       (* arm_AESE Q0 Q27 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b61;       (* arm_AESE Q1 Q27 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b62;       (* arm_AESE Q2 Q27 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b63;       (* arm_AESE Q3 Q27 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b64;       (* arm_AESE Q4 Q27 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b65;       (* arm_AESE Q5 Q27 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b66;       (* arm_AESE Q6 Q27 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b67;       (* arm_AESE Q7 Q27 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0xad466d7a;       (* arm_LDP Q26 Q27 X11 (Immediate_Offset (iword (&192))) *)
  0x4e284b80;       (* arm_AESE Q0 Q28 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b81;       (* arm_AESE Q1 Q28 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b82;       (* arm_AESE Q2 Q28 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b83;       (* arm_AESE Q3 Q28 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b84;       (* arm_AESE Q4 Q28 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b85;       (* arm_AESE Q5 Q28 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b86;       (* arm_AESE Q6 Q28 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b87;       (* arm_AESE Q7 Q28 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x3dc0397c;       (* arm_LDR Q28 X11 (Immediate_Offset (word 224)) *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b41;       (* arm_AESE Q1 Q26 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b42;       (* arm_AESE Q2 Q26 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b43;       (* arm_AESE Q3 Q26 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b44;       (* arm_AESE Q4 Q26 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b45;       (* arm_AESE Q5 Q26 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b46;       (* arm_AESE Q6 Q26 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b47;       (* arm_AESE Q7 Q26 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b60;       (* arm_AESE Q0 Q27 *)
  0x4e284b61;       (* arm_AESE Q1 Q27 *)
  0x4e284b62;       (* arm_AESE Q2 Q27 *)
  0x4e284b63;       (* arm_AESE Q3 Q27 *)
  0x4e284b64;       (* arm_AESE Q4 Q27 *)
  0x4e284b65;       (* arm_AESE Q5 Q27 *)
  0x4e284b66;       (* arm_AESE Q6 Q27 *)
  0x4e284b67;       (* arm_AESE Q7 Q27 *)
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
  0x14000148;       (* arm_B (word 1312) *)
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
  0x5400046c;       (* arm_BGT (word 140) *)
  0x4ea61cc7;       (* arm_MOV_VEC Q7 Q6 128 *)
  0x4ea51ca6;       (* arm_MOV_VEC Q6 Q5 128 *)
  0xf10140bf;       (* arm_CMP X5 (rvalue (word 80)) *)
  0x4ea41c85;       (* arm_MOV_VEC Q5 Q4 128 *)
  0x4ea31c64;       (* arm_MOV_VEC Q4 Q3 128 *)
  0x4ea11c23;       (* arm_MOV_VEC Q3 Q1 128 *)
  0x6ebf87de;       (* arm_SUB_VEC Q30 Q30 Q31 32 128 *)
  0x5400052c;       (* arm_BGT (word 164) *)
  0x4ea61cc7;       (* arm_MOV_VEC Q7 Q6 128 *)
  0x6ebf87de;       (* arm_SUB_VEC Q30 Q30 Q31 32 128 *)
  0x4ea51ca6;       (* arm_MOV_VEC Q6 Q5 128 *)
  0x4ea41c85;       (* arm_MOV_VEC Q5 Q4 128 *)
  0xf10100bf;       (* arm_CMP X5 (rvalue (word 64)) *)
  0x4ea11c24;       (* arm_MOV_VEC Q4 Q1 128 *)
  0x5400062c;       (* arm_BGT (word 196) *)
  0xf100c0bf;       (* arm_CMP X5 (rvalue (word 48)) *)
  0x4ea61cc7;       (* arm_MOV_VEC Q7 Q6 128 *)
  0x4ea51ca6;       (* arm_MOV_VEC Q6 Q5 128 *)
  0x4ea11c25;       (* arm_MOV_VEC Q5 Q1 128 *)
  0x6ebf87de;       (* arm_SUB_VEC Q30 Q30 Q31 32 128 *)
  0x54001d0c;       (* arm_BGT (word 928) *)
  0xf10080bf;       (* arm_CMP X5 (rvalue (word 32)) *)
  0x4ea61cc7;       (* arm_MOV_VEC Q7 Q6 128 *)
  0x3dc010d8;       (* arm_LDR Q24 X6 (Immediate_Offset (word 64)) *)
  0x4ea11c26;       (* arm_MOV_VEC Q6 Q1 128 *)
  0x6ebf87de;       (* arm_SUB_VEC Q30 Q30 Q31 32 128 *)
  0x5400068c;       (* arm_BGT (word 208) *)
  0x4ea11c27;       (* arm_MOV_VEC Q7 Q1 128 *)
  0x6ebf87de;       (* arm_SUB_VEC Q30 Q30 Q31 32 128 *)
  0xf10040bf;       (* arm_CMP X5 (rvalue (word 16)) *)
  0x540007ec;       (* arm_BGT (word 252) *)
  0x6ebf87de;       (* arm_SUB_VEC Q30 Q30 Q31 32 128 *)
  0x3dc004d5;       (* arm_LDR Q21 X6 (Immediate_Offset (word 16)) *)
  0x1400004d;       (* arm_B (word 308) *)
  0x4c9f7049;       (* arm_STR Q9 X2 (Postimmediate_Offset (word 16)) *)
  0x4e200928;       (* arm_REV64_VEC Q8 Q9 8 *)
  0x6e301d08;       (* arm_EOR_VEC Q8 Q8 Q16 128 *)
  0x0ef7e11a;       (* arm_PMULL_VEC Q26 Q8 Q23 64 *)
  0x6e08411b;       (* arm_EXT Q27 Q8 Q8 64 *)
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
  0x6e08411b;       (* arm_EXT Q27 Q8 Q8 64 *)
  0x4ef6e11c;       (* arm_PMULL2_VEC Q28 Q8 Q22 64 *)
  0x6e3c1e31;       (* arm_EOR_VEC Q17 Q17 Q28 128 *)
  0x2e281f7b;       (* arm_EOR_VEC Q27 Q27 Q8 64 *)
  0x6e1542ac;       (* arm_EXT Q12 Q21 Q21 64 *)
  0x3cc10409;       (* arm_LDR Q9 X0 (Postimmediate_Offset (word 16)) *)
  0x0ef6e11a;       (* arm_PMULL_VEC Q26 Q8 Q22 64 *)
  0x0eece37b;       (* arm_PMULL_VEC Q27 Q27 Q12 64 *)
  0x0f00e410;       (* arm_MOVI D16 (word 0) *)
  0x6e3a1e73;       (* arm_EOR_VEC Q19 Q19 Q26 128 *)
  0x6e3b1e52;       (* arm_EOR_VEC Q18 Q18 Q27 128 *)
  0xce037529;       (* arm_EOR3 Q9 Q9 Q3 Q29 *)
  0x4c9f7049;       (* arm_STR Q9 X2 (Postimmediate_Offset (word 16)) *)
  0x4e200928;       (* arm_REV64_VEC Q8 Q9 8 *)
  0x3cc10409;       (* arm_LDR Q9 X0 (Postimmediate_Offset (word 16)) *)
  0x6e301d08;       (* arm_EOR_VEC Q8 Q8 Q16 128 *)
  0x6e08411b;       (* arm_EXT Q27 Q8 Q8 64 *)
  0x4ef4e11c;       (* arm_PMULL2_VEC Q28 Q8 Q20 64 *)
  0xce047529;       (* arm_EOR3 Q9 Q9 Q4 Q29 *)
  0x0ef4e11a;       (* arm_PMULL_VEC Q26 Q8 Q20 64 *)
  0x2e281f7b;       (* arm_EOR_VEC Q27 Q27 Q8 64 *)
  0x6e3a1e73;       (* arm_EOR_VEC Q19 Q19 Q26 128 *)
  0x0ef5e37b;       (* arm_PMULL_VEC Q27 Q27 Q21 64 *)
  0x0f00e410;       (* arm_MOVI D16 (word 0) *)
  0x6e3b1e52;       (* arm_EOR_VEC Q18 Q18 Q27 128 *)
  0x6e3c1e31;       (* arm_EOR_VEC Q17 Q17 Q28 128 *)
  0x140000af;       (* arm_B (word 700) *)
  0x3dc00cd7;       (* arm_LDR Q23 X6 (Immediate_Offset (word 48)) *)
  0x4c9f7049;       (* arm_STR Q9 X2 (Postimmediate_Offset (word 16)) *)
  0x4e200928;       (* arm_REV64_VEC Q8 Q9 8 *)
  0x3cc10409;       (* arm_LDR Q9 X0 (Postimmediate_Offset (word 16)) *)
  0x6e301d08;       (* arm_EOR_VEC Q8 Q8 Q16 128 *)
  0x6e08411b;       (* arm_EXT Q27 Q8 Q8 64 *)
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
  0x6e08411b;       (* arm_EXT Q27 Q8 Q8 64 *)
  0x4ef6e11c;       (* arm_PMULL2_VEC Q28 Q8 Q22 64 *)
  0xce077529;       (* arm_EOR3 Q9 Q9 Q7 Q29 *)
  0x6e3c1e31;       (* arm_EOR_VEC Q17 Q17 Q28 128 *)
  0x0ef6e11a;       (* arm_PMULL_VEC Q26 Q8 Q22 64 *)
  0x2e281f7b;       (* arm_EOR_VEC Q27 Q27 Q8 64 *)
  0x3dc004d5;       (* arm_LDR Q21 X6 (Immediate_Offset (word 16)) *)
  0x6e1542aa;       (* arm_EXT Q10 Q21 Q21 64 *)
  0x6e3a1e73;       (* arm_EOR_VEC Q19 Q19 Q26 128 *)
  0x0eeae37b;       (* arm_PMULL_VEC Q27 Q27 Q10 64 *)
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
  0xd65f03c0;       (* arm_RET X30 *)
  0x4c9f7049;       (* arm_STR Q9 X2 (Postimmediate_Offset (word 16)) *)
  0x4e200928;       (* arm_REV64_VEC Q8 Q9 8 *)
  0x6e301d08;       (* arm_EOR_VEC Q8 Q8 Q16 128 *)
  0x3cc10409;       (* arm_LDR Q9 X0 (Postimmediate_Offset (word 16)) *)
  0x4ef9e111;       (* arm_PMULL2_VEC Q17 Q8 Q25 64 *)
  0x6e08411b;       (* arm_EXT Q27 Q8 Q8 64 *)
  0x6e084712;       (* arm_INS Q18 Q24 0 64 64 128 *)
  0x0f00e410;       (* arm_MOVI D16 (word 0) *)
  0x2e281f7b;       (* arm_EOR_VEC Q27 Q27 Q8 64 *)
  0xce017529;       (* arm_EOR3 Q9 Q9 Q1 Q29 *)
  0x0ef2e372;       (* arm_PMULL_VEC Q18 Q27 Q18 64 *)
  0x0ef9e113;       (* arm_PMULL_VEC Q19 Q8 Q25 64 *)
  0x4c9f7049;       (* arm_STR Q9 X2 (Postimmediate_Offset (word 16)) *)
  0x4e200928;       (* arm_REV64_VEC Q8 Q9 8 *)
  0x0ef7e10e;       (* arm_PMULL_VEC Q14 Q8 Q23 64 *)
  0x6e08411b;       (* arm_EXT Q27 Q8 Q8 64 *)
  0x4ef7e10d;       (* arm_PMULL2_VEC Q13 Q8 Q23 64 *)
  0x3cc10409;       (* arm_LDR Q9 X0 (Postimmediate_Offset (word 16)) *)
  0x2e281f7b;       (* arm_EOR_VEC Q27 Q27 Q8 64 *)
  0x0ef8e36f;       (* arm_PMULL_VEC Q15 Q27 Q24 64 *)
  0xce027529;       (* arm_EOR3 Q9 Q9 Q2 Q29 *)
  0x4c9f7049;       (* arm_STR Q9 X2 (Postimmediate_Offset (word 16)) *)
  0x4e200928;       (* arm_REV64_VEC Q8 Q9 8 *)
  0x6e08411b;       (* arm_EXT Q27 Q8 Q8 64 *)
  0x4ef6e11c;       (* arm_PMULL2_VEC Q28 Q8 Q22 64 *)
  0xce1c3631;       (* arm_EOR3 Q17 Q17 Q28 Q13 *)
  0x2e281f7b;       (* arm_EOR_VEC Q27 Q27 Q8 64 *)
  0x6e1542ac;       (* arm_EXT Q12 Q21 Q21 64 *)
  0x3cc10409;       (* arm_LDR Q9 X0 (Postimmediate_Offset (word 16)) *)
  0x0ef6e11a;       (* arm_PMULL_VEC Q26 Q8 Q22 64 *)
  0x0eece37b;       (* arm_PMULL_VEC Q27 Q27 Q12 64 *)
  0xce1a3a73;       (* arm_EOR3 Q19 Q19 Q26 Q14 *)
  0xce1b3e52;       (* arm_EOR3 Q18 Q18 Q27 Q15 *)
  0xce037529;       (* arm_EOR3 Q9 Q9 Q3 Q29 *)
  0x4c9f7049;       (* arm_STR Q9 X2 (Postimmediate_Offset (word 16)) *)
  0x4e200928;       (* arm_REV64_VEC Q8 Q9 8 *)
  0x3cc10409;       (* arm_LDR Q9 X0 (Postimmediate_Offset (word 16)) *)
  0x6e08411b;       (* arm_EXT Q27 Q8 Q8 64 *)
  0x4ef4e10d;       (* arm_PMULL2_VEC Q13 Q8 Q20 64 *)
  0xce047529;       (* arm_EOR3 Q9 Q9 Q4 Q29 *)
  0x0ef4e10e;       (* arm_PMULL_VEC Q14 Q8 Q20 64 *)
  0x2e281f7b;       (* arm_EOR_VEC Q27 Q27 Q8 64 *)
  0x0ef5e36f;       (* arm_PMULL_VEC Q15 Q27 Q21 64 *)
  0x4c9f7049;       (* arm_STR Q9 X2 (Postimmediate_Offset (word 16)) *)
  0x3dc014d9;       (* arm_LDR Q25 X6 (Immediate_Offset (word 80)) *)
  0x4e200928;       (* arm_REV64_VEC Q8 Q9 8 *)
  0x6e08411b;       (* arm_EXT Q27 Q8 Q8 64 *)
  0x4ef9e11c;       (* arm_PMULL2_VEC Q28 Q8 Q25 64 *)
  0xce1c3631;       (* arm_EOR3 Q17 Q17 Q28 Q13 *)
  0x2e281f7b;       (* arm_EOR_VEC Q27 Q27 Q8 64 *)
  0x3dc010d8;       (* arm_LDR Q24 X6 (Immediate_Offset (word 64)) *)
  0x6e18430b;       (* arm_EXT Q11 Q24 Q24 64 *)
  0x3cc10409;       (* arm_LDR Q9 X0 (Postimmediate_Offset (word 16)) *)
  0x0eebe37b;       (* arm_PMULL_VEC Q27 Q27 Q11 64 *)
  0x0ef9e11a;       (* arm_PMULL_VEC Q26 Q8 Q25 64 *)
  0xce057529;       (* arm_EOR3 Q9 Q9 Q5 Q29 *)
  0xce1b3e52;       (* arm_EOR3 Q18 Q18 Q27 Q15 *)
  0xce1a3a73;       (* arm_EOR3 Q19 Q19 Q26 Q14 *)
  0x3dc00cd7;       (* arm_LDR Q23 X6 (Immediate_Offset (word 48)) *)
  0x4c9f7049;       (* arm_STR Q9 X2 (Postimmediate_Offset (word 16)) *)
  0x4e200928;       (* arm_REV64_VEC Q8 Q9 8 *)
  0x3cc10409;       (* arm_LDR Q9 X0 (Postimmediate_Offset (word 16)) *)
  0x6e08411b;       (* arm_EXT Q27 Q8 Q8 64 *)
  0x4ef7e10d;       (* arm_PMULL2_VEC Q13 Q8 Q23 64 *)
  0xce067529;       (* arm_EOR3 Q9 Q9 Q6 Q29 *)
  0x2e281f7b;       (* arm_EOR_VEC Q27 Q27 Q8 64 *)
  0x0ef8e36f;       (* arm_PMULL_VEC Q15 Q27 Q24 64 *)
  0x0ef7e10e;       (* arm_PMULL_VEC Q14 Q8 Q23 64 *)
  0x4c9f7049;       (* arm_STR Q9 X2 (Postimmediate_Offset (word 16)) *)
  0x3dc008d6;       (* arm_LDR Q22 X6 (Immediate_Offset (word 32)) *)
  0x4e200928;       (* arm_REV64_VEC Q8 Q9 8 *)
  0x3cc10409;       (* arm_LDR Q9 X0 (Postimmediate_Offset (word 16)) *)
  0x6e08411b;       (* arm_EXT Q27 Q8 Q8 64 *)
  0x4ef6e11c;       (* arm_PMULL2_VEC Q28 Q8 Q22 64 *)
  0xce077529;       (* arm_EOR3 Q9 Q9 Q7 Q29 *)
  0xce1c3631;       (* arm_EOR3 Q17 Q17 Q28 Q13 *)
  0x0ef6e11a;       (* arm_PMULL_VEC Q26 Q8 Q22 64 *)
  0x2e281f7b;       (* arm_EOR_VEC Q27 Q27 Q8 64 *)
  0x3dc004d5;       (* arm_LDR Q21 X6 (Immediate_Offset (word 16)) *)
  0x6e1542aa;       (* arm_EXT Q10 Q21 Q21 64 *)
  0xce1a3a73;       (* arm_EOR3 Q19 Q19 Q26 Q14 *)
  0x0eeae37b;       (* arm_PMULL_VEC Q27 Q27 Q10 64 *)
  0xce1b3e52;       (* arm_EOR3 Q18 Q18 Q27 Q15 *)
  0x3dc000d4;       (* arm_LDR Q20 X6 (Immediate_Offset (word 0)) *)
  0x4e200928;       (* arm_REV64_VEC Q8 Q9 8 *)
  0x6e200bde;       (* arm_REV32_VEC Q30 Q30 8 *)
  0x3d80021e;       (* arm_STR Q30 X16 (Immediate_Offset (word 0)) *)
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
  0x17ffff8c;       (* arm_B (word 268434992) *)
  0x4c9f7049;       (* arm_STR Q9 X2 (Postimmediate_Offset (word 16)) *)
  0x3dc014d9;       (* arm_LDR Q25 X6 (Immediate_Offset (word 80)) *)
  0x4e200928;       (* arm_REV64_VEC Q8 Q9 8 *)
  0x6e301d08;       (* arm_EOR_VEC Q8 Q8 Q16 128 *)
  0x6e08411b;       (* arm_EXT Q27 Q8 Q8 64 *)
  0x4ef9e10d;       (* arm_PMULL2_VEC Q13 Q8 Q25 64 *)
  0x3dc010d8;       (* arm_LDR Q24 X6 (Immediate_Offset (word 64)) *)
  0x6e18430b;       (* arm_EXT Q11 Q24 Q24 64 *)
  0x2e281f7b;       (* arm_EOR_VEC Q27 Q27 Q8 64 *)
  0x3cc10409;       (* arm_LDR Q9 X0 (Postimmediate_Offset (word 16)) *)
  0x0eebe36f;       (* arm_PMULL_VEC Q15 Q27 Q11 64 *)
  0x0ef9e10e;       (* arm_PMULL_VEC Q14 Q8 Q25 64 *)
  0xce057529;       (* arm_EOR3 Q9 Q9 Q5 Q29 *)
  0x4c9f7049;       (* arm_STR Q9 X2 (Postimmediate_Offset (word 16)) *)
  0x3dc00cd7;       (* arm_LDR Q23 X6 (Immediate_Offset (word 48)) *)
  0x4e200928;       (* arm_REV64_VEC Q8 Q9 8 *)
  0x3cc10409;       (* arm_LDR Q9 X0 (Postimmediate_Offset (word 16)) *)
  0x6e08411b;       (* arm_EXT Q27 Q8 Q8 64 *)
  0x4ef7e11c;       (* arm_PMULL2_VEC Q28 Q8 Q23 64 *)
  0xce067529;       (* arm_EOR3 Q9 Q9 Q6 Q29 *)
  0x2e281f7b;       (* arm_EOR_VEC Q27 Q27 Q8 64 *)
  0x0ef7e11a;       (* arm_PMULL_VEC Q26 Q8 Q23 64 *)
  0x0ef8e37b;       (* arm_PMULL_VEC Q27 Q27 Q24 64 *)
  0xce1c3631;       (* arm_EOR3 Q17 Q17 Q28 Q13 *)
  0xce1a3a73;       (* arm_EOR3 Q19 Q19 Q26 Q14 *)
  0xce1b3e52;       (* arm_EOR3 Q18 Q18 Q27 Q15 *)
  0x4c9f7049;       (* arm_STR Q9 X2 (Postimmediate_Offset (word 16)) *)
  0x3dc008d6;       (* arm_LDR Q22 X6 (Immediate_Offset (word 32)) *)
  0x4e200928;       (* arm_REV64_VEC Q8 Q9 8 *)
  0x3cc10409;       (* arm_LDR Q9 X0 (Postimmediate_Offset (word 16)) *)
  0x6e08411b;       (* arm_EXT Q27 Q8 Q8 64 *)
  0x4ef6e10d;       (* arm_PMULL2_VEC Q13 Q8 Q22 64 *)
  0xce077529;       (* arm_EOR3 Q9 Q9 Q7 Q29 *)
  0x0ef6e10e;       (* arm_PMULL_VEC Q14 Q8 Q22 64 *)
  0x2e281f7b;       (* arm_EOR_VEC Q27 Q27 Q8 64 *)
  0x3dc004d5;       (* arm_LDR Q21 X6 (Immediate_Offset (word 16)) *)
  0x6e1542aa;       (* arm_EXT Q10 Q21 Q21 64 *)
  0x0eeae36f;       (* arm_PMULL_VEC Q15 Q27 Q10 64 *)
  0x3dc000d4;       (* arm_LDR Q20 X6 (Immediate_Offset (word 0)) *)
  0x4e200928;       (* arm_REV64_VEC Q8 Q9 8 *)
  0x6e200bde;       (* arm_REV32_VEC Q30 Q30 8 *)
  0x3d80021e;       (* arm_STR Q30 X16 (Immediate_Offset (word 0)) *)
  0x4c007049;       (* arm_STR Q9 X2 No_Offset *)
  0x6e084510;       (* arm_INS Q16 Q8 0 64 64 128 *)
  0x4ef4e11c;       (* arm_PMULL2_VEC Q28 Q8 Q20 64 *)
  0x0ef4e11a;       (* arm_PMULL_VEC Q26 Q8 Q20 64 *)
  0x2e281e10;       (* arm_EOR_VEC Q16 Q16 Q8 64 *)
  0x0ef5e210;       (* arm_PMULL_VEC Q16 Q16 Q21 64 *)
  0xce1c3631;       (* arm_EOR3 Q17 Q17 Q28 Q13 *)
  0xce1a3a73;       (* arm_EOR3 Q19 Q19 Q26 Q14 *)
  0xce103e52;       (* arm_EOR3 Q18 Q18 Q16 Q15 *)
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
  0x17ffff4d;       (* arm_B (word 268434740) *)
  0x54ffeaac;       (* arm_BGT (word 2096468) *)
  0xf10080bf;       (* arm_CMP X5 (rvalue (word 32)) *)
  0x54000040;       (* arm_BEQ (word 8) *)
  0x17fffeb6;       (* arm_B (word 268434136) *)
  0x6ebf87de;       (* arm_SUB_VEC Q30 Q30 Q31 32 128 *)
  0x3dc008d6;       (* arm_LDR Q22 X6 (Immediate_Offset (word 32)) *)
  0x6ebf87de;       (* arm_SUB_VEC Q30 Q30 Q31 32 128 *)
  0x3dc004d5;       (* arm_LDR Q21 X6 (Immediate_Offset (word 16)) *)
  0x6ebf87de;       (* arm_SUB_VEC Q30 Q30 Q31 32 128 *)
  0x3dc000d4;       (* arm_LDR Q20 X6 (Immediate_Offset (word 0)) *)
  0x6ebf87de;       (* arm_SUB_VEC Q30 Q30 Q31 32 128 *)
  0x4c9f7049;       (* arm_STR Q9 X2 (Postimmediate_Offset (word 16)) *)
  0x6ebf87de;       (* arm_SUB_VEC Q30 Q30 Q31 32 128 *)
  0x4e200928;       (* arm_REV64_VEC Q8 Q9 8 *)
  0x6ebf87de;       (* arm_SUB_VEC Q30 Q30 Q31 32 128 *)
  0x6e301d08;       (* arm_EOR_VEC Q8 Q8 Q16 128 *)
  0x3cc10409;       (* arm_LDR Q9 X0 (Postimmediate_Offset (word 16)) *)
  0x6e08411b;       (* arm_EXT Q27 Q8 Q8 64 *)
  0x6e1542aa;       (* arm_EXT Q10 Q21 Q21 64 *)
  0x4ef6e10d;       (* arm_PMULL2_VEC Q13 Q8 Q22 64 *)
  0x2e281f7b;       (* arm_EOR_VEC Q27 Q27 Q8 64 *)
  0x0ef6e10e;       (* arm_PMULL_VEC Q14 Q8 Q22 64 *)
  0xce017529;       (* arm_EOR3 Q9 Q9 Q1 Q29 *)
  0x0eeae36f;       (* arm_PMULL_VEC Q15 Q27 Q10 64 *)
  0x4c007049;       (* arm_STR Q9 X2 No_Offset *)
  0x4e200928;       (* arm_REV64_VEC Q8 Q9 8 *)
  0x6e084510;       (* arm_INS Q16 Q8 0 64 64 128 *)
  0x4ef4e11c;       (* arm_PMULL2_VEC Q28 Q8 Q20 64 *)
  0x0ef4e11a;       (* arm_PMULL_VEC Q26 Q8 Q20 64 *)
  0x2e281e10;       (* arm_EOR_VEC Q16 Q16 Q8 64 *)
  0x0ef5e210;       (* arm_PMULL_VEC Q16 Q16 Q21 64 *)
  0x6e3c1db1;       (* arm_EOR_VEC Q17 Q13 Q28 128 *)
  0x6e3a1dd3;       (* arm_EOR_VEC Q19 Q14 Q26 128 *)
  0x6e301df2;       (* arm_EOR_VEC Q18 Q15 Q16 128 *)
  0x6e200bde;       (* arm_REV32_VEC Q30 Q30 8 *)
  0x3d80021e;       (* arm_STR Q30 X16 (Immediate_Offset (word 0)) *)
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
  0x17ffff1d;       (* arm_B (word 268434548) *)
  0x6e20081d;       (* arm_REV32_VEC Q29 Q0 8 *)
  0xad406d7a;       (* arm_LDP Q26 Q27 X11 (Immediate_Offset (iword (&0))) *)
  0x4c407073;       (* arm_LDR Q19 X3 No_Offset *)
  0x6e134273;       (* arm_EXT Q19 Q19 Q19 64 *)
  0x4e200a73;       (* arm_REV64_VEC Q19 Q19 8 *)
  0x4ebf87fc;       (* arm_ADD_VEC Q28 Q31 Q31 32 128 *)
  0x4ebf878a;       (* arm_ADD_VEC Q10 Q28 Q31 32 128 *)
  0x4ebc878b;       (* arm_ADD_VEC Q11 Q28 Q28 32 128 *)
  0xd281c1e7;       (* arm_MOV X7 (rvalue (word 3599)) *)
  0xf2a181a7;       (* arm_MOVK X7 (word 3085) 16 *)
  0xf2c14167;       (* arm_MOVK X7 (word 2571) 32 *)
  0xf2e10127;       (* arm_MOVK X7 (word 2057) 48 *)
  0xd280c0e8;       (* arm_MOV X8 (rvalue (word 1543)) *)
  0xf2a080a8;       (* arm_MOVK X8 (word 1029) 16 *)
  0xf2c04068;       (* arm_MOVK X8 (word 515) 32 *)
  0xf2e00028;       (* arm_MOVK X8 (word 1) 48 *)
  0x9e6700ec;       (* arm_FMOV_ItoF Q12 X7 0 *)
  0x4e181d0c;       (* arm_INS_GEN Q12 X8 64 64 *)
  0xf100413f;       (* arm_CMP X9 (rvalue (word 16)) *)
  0x54001900;       (* arm_BEQ (word 800) *)
  0xf100813f;       (* arm_CMP X9 (rvalue (word 32)) *)
  0x540012e0;       (* arm_BEQ (word 604) *)
  0xf100c13f;       (* arm_CMP X9 (rvalue (word 48)) *)
  0x54000ac0;       (* arm_BEQ (word 344) *)
  0x4eab87be;       (* arm_ADD_VEC Q30 Q29 Q11 32 128 *)
  0x4ebf87a8;       (* arm_ADD_VEC Q8 Q29 Q31 32 128 *)
  0x6e200901;       (* arm_REV32_VEC Q1 Q8 8 *)
  0x4ebc87a9;       (* arm_ADD_VEC Q9 Q29 Q28 32 128 *)
  0x6e200922;       (* arm_REV32_VEC Q2 Q9 8 *)
  0x4eaa87af;       (* arm_ADD_VEC Q15 Q29 Q10 32 128 *)
  0x6e2009e3;       (* arm_REV32_VEC Q3 Q15 8 *)
  0xaa0b03ec;       (* arm_MOV X12 X11 *)
  0x528001ad;       (* arm_MOV W13 (rvalue (word 13)) *)
  0x4cdf719a;       (* arm_LDR Q26 X12 (Postimmediate_Offset (word 16)) *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b41;       (* arm_AESE Q1 Q26 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b42;       (* arm_AESE Q2 Q26 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b43;       (* arm_AESE Q3 Q26 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x710005ad;       (* arm_SUBS W13 W13 (rvalue (word 1)) *)
  0x54fffec1;       (* arm_BNE (word 2097112) *)
  0x4cdf719a;       (* arm_LDR Q26 X12 (Postimmediate_Offset (word 16)) *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e284b41;       (* arm_AESE Q1 Q26 *)
  0x4e284b42;       (* arm_AESE Q2 Q26 *)
  0x4e284b43;       (* arm_AESE Q3 Q26 *)
  0x3dc0019c;       (* arm_LDR Q28 X12 (Immediate_Offset (word 0)) *)
  0x3cc10408;       (* arm_LDR Q8 X0 (Postimmediate_Offset (word 16)) *)
  0x6e134270;       (* arm_EXT Q16 Q19 Q19 64 *)
  0x4ebc1f9d;       (* arm_MOV_VEC Q29 Q28 128 *)
  0x0f00e411;       (* arm_MOVI D17 (word 0) *)
  0x0f00e412;       (* arm_MOVI D18 (word 0) *)
  0x0f00e413;       (* arm_MOVI D19 (word 0) *)
  0xce007509;       (* arm_EOR3 Q9 Q8 Q0 Q29 *)
  0x4c9f7049;       (* arm_STR Q9 X2 (Postimmediate_Offset (word 16)) *)
  0x3dc014d9;       (* arm_LDR Q25 X6 (Immediate_Offset (word 80)) *)
  0x4e200928;       (* arm_REV64_VEC Q8 Q9 8 *)
  0x6e301d08;       (* arm_EOR_VEC Q8 Q8 Q16 128 *)
  0x6e08411b;       (* arm_EXT Q27 Q8 Q8 64 *)
  0x4ef9e10d;       (* arm_PMULL2_VEC Q13 Q8 Q25 64 *)
  0x3dc010d8;       (* arm_LDR Q24 X6 (Immediate_Offset (word 64)) *)
  0x6e18430b;       (* arm_EXT Q11 Q24 Q24 64 *)
  0x2e281f7b;       (* arm_EOR_VEC Q27 Q27 Q8 64 *)
  0x3cc10409;       (* arm_LDR Q9 X0 (Postimmediate_Offset (word 16)) *)
  0x0eebe36f;       (* arm_PMULL_VEC Q15 Q27 Q11 64 *)
  0x0ef9e10e;       (* arm_PMULL_VEC Q14 Q8 Q25 64 *)
  0xce017529;       (* arm_EOR3 Q9 Q9 Q1 Q29 *)
  0x4c9f7049;       (* arm_STR Q9 X2 (Postimmediate_Offset (word 16)) *)
  0x3dc00cd7;       (* arm_LDR Q23 X6 (Immediate_Offset (word 48)) *)
  0x4e200928;       (* arm_REV64_VEC Q8 Q9 8 *)
  0x3cc10409;       (* arm_LDR Q9 X0 (Postimmediate_Offset (word 16)) *)
  0x6e08411b;       (* arm_EXT Q27 Q8 Q8 64 *)
  0x4ef7e11c;       (* arm_PMULL2_VEC Q28 Q8 Q23 64 *)
  0xce027529;       (* arm_EOR3 Q9 Q9 Q2 Q29 *)
  0x2e281f7b;       (* arm_EOR_VEC Q27 Q27 Q8 64 *)
  0x0ef7e11a;       (* arm_PMULL_VEC Q26 Q8 Q23 64 *)
  0x0ef8e37b;       (* arm_PMULL_VEC Q27 Q27 Q24 64 *)
  0xce1c3631;       (* arm_EOR3 Q17 Q17 Q28 Q13 *)
  0xce1a3a73;       (* arm_EOR3 Q19 Q19 Q26 Q14 *)
  0xce1b3e52;       (* arm_EOR3 Q18 Q18 Q27 Q15 *)
  0x4c9f7049;       (* arm_STR Q9 X2 (Postimmediate_Offset (word 16)) *)
  0x3dc008d6;       (* arm_LDR Q22 X6 (Immediate_Offset (word 32)) *)
  0x4e200928;       (* arm_REV64_VEC Q8 Q9 8 *)
  0x3cc10409;       (* arm_LDR Q9 X0 (Postimmediate_Offset (word 16)) *)
  0x6e08411b;       (* arm_EXT Q27 Q8 Q8 64 *)
  0x4ef6e10d;       (* arm_PMULL2_VEC Q13 Q8 Q22 64 *)
  0xce037529;       (* arm_EOR3 Q9 Q9 Q3 Q29 *)
  0x0ef6e10e;       (* arm_PMULL_VEC Q14 Q8 Q22 64 *)
  0x2e281f7b;       (* arm_EOR_VEC Q27 Q27 Q8 64 *)
  0x3dc004d5;       (* arm_LDR Q21 X6 (Immediate_Offset (word 16)) *)
  0x6e1542aa;       (* arm_EXT Q10 Q21 Q21 64 *)
  0x0eeae36f;       (* arm_PMULL_VEC Q15 Q27 Q10 64 *)
  0x3dc000d4;       (* arm_LDR Q20 X6 (Immediate_Offset (word 0)) *)
  0x4e200928;       (* arm_REV64_VEC Q8 Q9 8 *)
  0x6e200bde;       (* arm_REV32_VEC Q30 Q30 8 *)
  0x3d80021e;       (* arm_STR Q30 X16 (Immediate_Offset (word 0)) *)
  0x4c007049;       (* arm_STR Q9 X2 No_Offset *)
  0x6e084510;       (* arm_INS Q16 Q8 0 64 64 128 *)
  0x4ef4e11c;       (* arm_PMULL2_VEC Q28 Q8 Q20 64 *)
  0x0ef4e11a;       (* arm_PMULL_VEC Q26 Q8 Q20 64 *)
  0x2e281e10;       (* arm_EOR_VEC Q16 Q16 Q8 64 *)
  0x0ef5e210;       (* arm_PMULL_VEC Q16 Q16 Q21 64 *)
  0xce1c3631;       (* arm_EOR3 Q17 Q17 Q28 Q13 *)
  0xce1a3a73;       (* arm_EOR3 Q19 Q19 Q26 Q14 *)
  0xce103e52;       (* arm_EOR3 Q18 Q18 Q16 Q15 *)
  0x1400008a;       (* arm_B (word 552) *)
  0x4eaa87be;       (* arm_ADD_VEC Q30 Q29 Q10 32 128 *)
  0x4ebf87a8;       (* arm_ADD_VEC Q8 Q29 Q31 32 128 *)
  0x6e200901;       (* arm_REV32_VEC Q1 Q8 8 *)
  0x4ebc87a9;       (* arm_ADD_VEC Q9 Q29 Q28 32 128 *)
  0x6e200922;       (* arm_REV32_VEC Q2 Q9 8 *)
  0xaa0b03ec;       (* arm_MOV X12 X11 *)
  0x528001ad;       (* arm_MOV W13 (rvalue (word 13)) *)
  0x4cdf719a;       (* arm_LDR Q26 X12 (Postimmediate_Offset (word 16)) *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b41;       (* arm_AESE Q1 Q26 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b42;       (* arm_AESE Q2 Q26 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x710005ad;       (* arm_SUBS W13 W13 (rvalue (word 1)) *)
  0x54ffff01;       (* arm_BNE (word 2097120) *)
  0x4cdf719a;       (* arm_LDR Q26 X12 (Postimmediate_Offset (word 16)) *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e284b41;       (* arm_AESE Q1 Q26 *)
  0x4e284b42;       (* arm_AESE Q2 Q26 *)
  0x3dc0019c;       (* arm_LDR Q28 X12 (Immediate_Offset (word 0)) *)
  0x3cc10408;       (* arm_LDR Q8 X0 (Postimmediate_Offset (word 16)) *)
  0x6e134270;       (* arm_EXT Q16 Q19 Q19 64 *)
  0x4ebc1f9d;       (* arm_MOV_VEC Q29 Q28 128 *)
  0xce007509;       (* arm_EOR3 Q9 Q8 Q0 Q29 *)
  0x4c9f7049;       (* arm_STR Q9 X2 (Postimmediate_Offset (word 16)) *)
  0x3dc00cd7;       (* arm_LDR Q23 X6 (Immediate_Offset (word 48)) *)
  0x4e200928;       (* arm_REV64_VEC Q8 Q9 8 *)
  0x6e301d08;       (* arm_EOR_VEC Q8 Q8 Q16 128 *)
  0x3dc010d8;       (* arm_LDR Q24 X6 (Immediate_Offset (word 64)) *)
  0x6e08411b;       (* arm_EXT Q27 Q8 Q8 64 *)
  0x4ef7e10d;       (* arm_PMULL2_VEC Q13 Q8 Q23 64 *)
  0x2e281f7b;       (* arm_EOR_VEC Q27 Q27 Q8 64 *)
  0x3cc10409;       (* arm_LDR Q9 X0 (Postimmediate_Offset (word 16)) *)
  0x0ef7e10e;       (* arm_PMULL_VEC Q14 Q8 Q23 64 *)
  0x0ef8e36f;       (* arm_PMULL_VEC Q15 Q27 Q24 64 *)
  0xce017529;       (* arm_EOR3 Q9 Q9 Q1 Q29 *)
  0x4c9f7049;       (* arm_STR Q9 X2 (Postimmediate_Offset (word 16)) *)
  0x3dc008d6;       (* arm_LDR Q22 X6 (Immediate_Offset (word 32)) *)
  0x4e200928;       (* arm_REV64_VEC Q8 Q9 8 *)
  0x3cc10409;       (* arm_LDR Q9 X0 (Postimmediate_Offset (word 16)) *)
  0x6e08411b;       (* arm_EXT Q27 Q8 Q8 64 *)
  0x4ef6e103;       (* arm_PMULL2_VEC Q3 Q8 Q22 64 *)
  0xce027529;       (* arm_EOR3 Q9 Q9 Q2 Q29 *)
  0x2e281f7b;       (* arm_EOR_VEC Q27 Q27 Q8 64 *)
  0x0ef6e104;       (* arm_PMULL_VEC Q4 Q8 Q22 64 *)
  0x3dc004d5;       (* arm_LDR Q21 X6 (Immediate_Offset (word 16)) *)
  0x6e1542aa;       (* arm_EXT Q10 Q21 Q21 64 *)
  0x0eeae365;       (* arm_PMULL_VEC Q5 Q27 Q10 64 *)
  0x3dc000d4;       (* arm_LDR Q20 X6 (Immediate_Offset (word 0)) *)
  0x4e200928;       (* arm_REV64_VEC Q8 Q9 8 *)
  0x6e200bde;       (* arm_REV32_VEC Q30 Q30 8 *)
  0x3d80021e;       (* arm_STR Q30 X16 (Immediate_Offset (word 0)) *)
  0x4c007049;       (* arm_STR Q9 X2 No_Offset *)
  0x6e084510;       (* arm_INS Q16 Q8 0 64 64 128 *)
  0x4ef4e11c;       (* arm_PMULL2_VEC Q28 Q8 Q20 64 *)
  0x0ef4e11a;       (* arm_PMULL_VEC Q26 Q8 Q20 64 *)
  0x2e281e10;       (* arm_EOR_VEC Q16 Q16 Q8 64 *)
  0x0ef5e210;       (* arm_PMULL_VEC Q16 Q16 Q21 64 *)
  0xce033791;       (* arm_EOR3 Q17 Q28 Q3 Q13 *)
  0xce043b53;       (* arm_EOR3 Q19 Q26 Q4 Q14 *)
  0xce053e12;       (* arm_EOR3 Q18 Q16 Q5 Q15 *)
  0x1400004b;       (* arm_B (word 300) *)
  0x4ebc87be;       (* arm_ADD_VEC Q30 Q29 Q28 32 128 *)
  0x4ebf87a8;       (* arm_ADD_VEC Q8 Q29 Q31 32 128 *)
  0x6e200901;       (* arm_REV32_VEC Q1 Q8 8 *)
  0xaa0b03ec;       (* arm_MOV X12 X11 *)
  0x528001ad;       (* arm_MOV W13 (rvalue (word 13)) *)
  0x4cdf719a;       (* arm_LDR Q26 X12 (Postimmediate_Offset (word 16)) *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b41;       (* arm_AESE Q1 Q26 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x710005ad;       (* arm_SUBS W13 W13 (rvalue (word 1)) *)
  0x54ffff41;       (* arm_BNE (word 2097128) *)
  0x4cdf719a;       (* arm_LDR Q26 X12 (Postimmediate_Offset (word 16)) *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e284b41;       (* arm_AESE Q1 Q26 *)
  0x3dc0019c;       (* arm_LDR Q28 X12 (Immediate_Offset (word 0)) *)
  0x3cc10408;       (* arm_LDR Q8 X0 (Postimmediate_Offset (word 16)) *)
  0x6e134270;       (* arm_EXT Q16 Q19 Q19 64 *)
  0x4ebc1f9d;       (* arm_MOV_VEC Q29 Q28 128 *)
  0xce007509;       (* arm_EOR3 Q9 Q8 Q0 Q29 *)
  0x3dc008d6;       (* arm_LDR Q22 X6 (Immediate_Offset (word 32)) *)
  0x3dc004d5;       (* arm_LDR Q21 X6 (Immediate_Offset (word 16)) *)
  0x3dc000d4;       (* arm_LDR Q20 X6 (Immediate_Offset (word 0)) *)
  0x4c9f7049;       (* arm_STR Q9 X2 (Postimmediate_Offset (word 16)) *)
  0x4e200928;       (* arm_REV64_VEC Q8 Q9 8 *)
  0x6e301d08;       (* arm_EOR_VEC Q8 Q8 Q16 128 *)
  0x3cc10409;       (* arm_LDR Q9 X0 (Postimmediate_Offset (word 16)) *)
  0x6e08411b;       (* arm_EXT Q27 Q8 Q8 64 *)
  0x6e1542aa;       (* arm_EXT Q10 Q21 Q21 64 *)
  0x4ef6e10d;       (* arm_PMULL2_VEC Q13 Q8 Q22 64 *)
  0x2e281f7b;       (* arm_EOR_VEC Q27 Q27 Q8 64 *)
  0x0ef6e10e;       (* arm_PMULL_VEC Q14 Q8 Q22 64 *)
  0xce017529;       (* arm_EOR3 Q9 Q9 Q1 Q29 *)
  0x0eeae36f;       (* arm_PMULL_VEC Q15 Q27 Q10 64 *)
  0x4c007049;       (* arm_STR Q9 X2 No_Offset *)
  0x4e200928;       (* arm_REV64_VEC Q8 Q9 8 *)
  0x6e084510;       (* arm_INS Q16 Q8 0 64 64 128 *)
  0x4ef4e11c;       (* arm_PMULL2_VEC Q28 Q8 Q20 64 *)
  0x0ef4e11a;       (* arm_PMULL_VEC Q26 Q8 Q20 64 *)
  0x2e281e10;       (* arm_EOR_VEC Q16 Q16 Q8 64 *)
  0x0ef5e210;       (* arm_PMULL_VEC Q16 Q16 Q21 64 *)
  0x6e3c1db1;       (* arm_EOR_VEC Q17 Q13 Q28 128 *)
  0x6e3a1dd3;       (* arm_EOR_VEC Q19 Q14 Q26 128 *)
  0x6e301df2;       (* arm_EOR_VEC Q18 Q15 Q16 128 *)
  0x6e200bde;       (* arm_REV32_VEC Q30 Q30 8 *)
  0x3d80021e;       (* arm_STR Q30 X16 (Immediate_Offset (word 0)) *)
  0x1400001c;       (* arm_B (word 112) *)
  0x4ebf87be;       (* arm_ADD_VEC Q30 Q29 Q31 32 128 *)
  0xaa0b03ec;       (* arm_MOV X12 X11 *)
  0x528001ad;       (* arm_MOV W13 (rvalue (word 13)) *)
  0x4cdf719a;       (* arm_LDR Q26 X12 (Postimmediate_Offset (word 16)) *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x710005ad;       (* arm_SUBS W13 W13 (rvalue (word 1)) *)
  0x54ffff81;       (* arm_BNE (word 2097136) *)
  0x4cdf719a;       (* arm_LDR Q26 X12 (Postimmediate_Offset (word 16)) *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x3dc0019c;       (* arm_LDR Q28 X12 (Immediate_Offset (word 0)) *)
  0x3dc00008;       (* arm_LDR Q8 X0 (Immediate_Offset (word 0)) *)
  0x6e134270;       (* arm_EXT Q16 Q19 Q19 64 *)
  0x4ebc1f9d;       (* arm_MOV_VEC Q29 Q28 128 *)
  0xce007509;       (* arm_EOR3 Q9 Q8 Q0 Q29 *)
  0x3dc000d4;       (* arm_LDR Q20 X6 (Immediate_Offset (word 0)) *)
  0x3dc004d5;       (* arm_LDR Q21 X6 (Immediate_Offset (word 16)) *)
  0x4e200928;       (* arm_REV64_VEC Q8 Q9 8 *)
  0x6e301d08;       (* arm_EOR_VEC Q8 Q8 Q16 128 *)
  0x4c007049;       (* arm_STR Q9 X2 No_Offset *)
  0x6e084510;       (* arm_INS Q16 Q8 0 64 64 128 *)
  0x4ef4e111;       (* arm_PMULL2_VEC Q17 Q8 Q20 64 *)
  0x0ef4e113;       (* arm_PMULL_VEC Q19 Q8 Q20 64 *)
  0x2e281e10;       (* arm_EOR_VEC Q16 Q16 Q8 64 *)
  0x0ef5e212;       (* arm_PMULL_VEC Q18 Q16 Q21 64 *)
  0x6e200bde;       (* arm_REV32_VEC Q30 Q30 8 *)
  0x3d80021e;       (* arm_STR Q30 X16 (Immediate_Offset (word 0)) *)
  0xfd400150;       (* arm_LDR D16 X10 (Immediate_Offset (word 0)) *)
  0x6e114235;       (* arm_EXT Q21 Q17 Q17 64 *)
  0xce114e52;       (* arm_EOR3 Q18 Q18 Q17 Q19 *)
  0x0ef0e23d;       (* arm_PMULL_VEC Q29 Q17 Q16 64 *)
  0xce1d5652;       (* arm_EOR3 Q18 Q18 Q29 Q21 *)
  0x0ef0e251;       (* arm_PMULL_VEC Q17 Q18 Q16 64 *)
  0x6e124255;       (* arm_EXT Q21 Q18 Q18 64 *)
  0xce115673;       (* arm_EOR3 Q19 Q19 Q17 Q21 *)
  0x4e0c0273;       (* arm_TBL Q19 [Q19] Q12 128 *)
  0x4c007073;       (* arm_STR Q19 X3 No_Offset *)
  0x17fffe1c        (* arm_B (word 268433520) *)
];;

(* The kernel's .text begins with the AARCH64_VALID_CALL_TARGET landing pad  *)
(* (`bti c`).  Following the x86 IBT convention, the proof runs against the  *)
(* TRIMMED code -- the pad removed -- and the default build's theorem is     *)
(* then derived from the -DNO_IBT one by ARM_ADD_IBT_RULE.                   *)

let aes256_gcm_enc_alt_tmc =
  define_trimmed "aes256_gcm_enc_alt_tmc" aes256_gcm_enc_alt_mc;;

let AES256_GCM_ENC_ALT_EXEC = ARM_MK_EXEC_RULE aes256_gcm_enc_alt_tmc;;

(* ========================================================================= *)
(* Local lemmas: reversefields equivalences, AES-256 and counter-block       *)
(* reconstruction, and the Karatsuba/GHASH reduction facts the 8x kernel     *)
(* needs on top of arm/proofs/utils/aes_gcm_common.ml.                       *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Reconstruction of high-level concepts from the computed expressions.      *)
(* ------------------------------------------------------------------------- *)

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

(* aes256_cipher reads only EL 0..14 of its key list (see                    *)
(* common/fips197.ml), so replacing the key argument by its explicit         *)
(* first-15 EL-projection is a no-op.  UNCONDITIONAL (no `LENGTH rk = 15`    *)
(* needed).  This closes the final residual left on each ciphertext          *)
(* out-block conjunct after XOR_AES256_CIPHER_RECONSTRUCT + MAP +            *)
(* WORD_REVERSEFIELDS_REVERSEFIELDS: those rewrites collapse the per-element *)
(* `word_reversefields`, but leave the key as the explicit list `[EL 0 rk;   *)
(* ...; EL 14 rk]` rather than `rk`; this lemma folds it back, so `rk`       *)
(* stays a free variable in the statement.                                   *)
let AES256_CIPHER_KEYLIST = prove
 (`aes256_cipher p
     [EL 0 rk; EL 1 rk; EL 2 rk; EL 3 rk; EL 4 rk; EL 5 rk; EL 6 rk; EL 7 rk;
      EL 8 rk; EL 9 rk; EL 10 rk; EL 11 rk; EL 12 rk; EL 13 rk; EL 14 rk] =
   aes256_cipher p rk`,
  REWRITE_TAC[aes256_cipher] THEN
  CONV_TAC(DEPTH_CONV EL_CONV) THEN
  REWRITE_TAC[]);;

(* ========================================================================= *)
(* GHASH: the kernel's two-pmull reduction and its POLYVAL meaning.          *)
(* ========================================================================= *)

let ghash_reduce_raw = new_definition
 `ghash_reduce_raw p1 p2 p3 =
    let (LO:int128->int64) = \x. word_subword x (0,64) in
    let (ext:int128->int128) = \x. word_subword (word_join x x : int256) (64,128) in
    let w = word 13979173243358019584 : int64 in
    let q18 = word_xor (word_xor (word_xor (word_xor p2 p1) p3)
                                 (word_pmul (LO p1) w))
                       (ext p1) in
    word_xor (word_xor p3 (word_pmul (LO q18) w)) (ext q18) : int128`;;

(* ghash_reduce_raw is kept as a fold target.  Its body is the term            *)
(* ARM_STEPS_TAC (1--8) emits for Q19, so RECON_GRR can fold that raw reduce   *)
(* back into a named form by GSYM, in the main loop, prepretail and the tail   *)
(* and fast arms.  The shared polyval_reduce_g2 arranges the same computation  *)
(* differently, so folding into it directly would first need the emitted term  *)
(* normalised.  GHASH_REDUCE_RAW_IS_POLYVAL_G2 relates the two                 *)
(* (ghash_reduce_raw p1 p2 p3 = polyval_reduce_g2 p1 p3 p2), and the per-block *)
(* folds reach polyval_dot through it, so no second GHASH semantics arises.    *)

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
(* Bridge (b): the Karatsuba multiply-accumulate fold.                       *)
(*                                                                           *)
(* Given the three Karatsuba partial products of a single 128x128 carryless  *)
(* multiply  a * b  --  lo*lo, the cross term (a_lo^a_hi)*(b_lo^b_hi), and   *)
(* hi*hi -- feeding the reduce region in the Q17(hi)/Q18(mid)/Q19(lo) order  *)
(* the hardware uses (pmull -> lo lane, pmull2 -> hi lane, pmull of the      *)
(* eor'd halves -> cross/mid lane), the reduce computes exactly the polyval  *)
(* "dot" product  polyval_dot a b = prop3(pmul a b).                         *)
(*                                                                           *)
(*        ghash_reduce_raw <lo*lo> <cross> <hi*hi>  =  polyval_dot a b       *)
(*                                                                           *)
(* Proof chain: bridge (a) turns ghash_reduce_raw into polyval_reduce_g2     *)
(* (with the p2<->p3 swap that reorders cross/hi into g2's hi,lo,mid slots), *)
(* POLYVAL_REDUCE_G2 rewrites that to polyval_reduce_prop3 of the            *)
(* reassembled 256-bit product, and GSYM PMUL_KARATSUBA_JOIN collapses the   *)
(* three partial products back into the single word_pmul a b inside          *)
(* polyval_dot.  NB the two REWRITE_TAC calls must stay SEPARATE: folding    *)
(* POLYVAL_REDUCE_G2 into the bridge-(a) rewrite list makes it fire before   *)
(* the swap settles and the proof diverges.                                  *)
(*                                                                           *)
(* This is the per-block fold primitive the main-loop / prepretail / tail    *)
(* bodies compose: each GHASH block is `word_pmul (acc_xor_block)            *)
(* (h_power ...)`; the batched multi-block accumulation over v8..v15 then    *)
(* closes with the existing common/ lemma GHASH_POLYVAL_ACC_BATCHED (which   *)
(* already reduces `ghash_polyval_acc h a (CONS b bs)` to a prop3 of the     *)
(* pmul + ghash_wide sum), and NIST_DOT_IS_POLYVAL_DOT / nist_ghash bridge   *)
(* the polyval accumulator to the nist_ghash tag.                            *)
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
(* Main-loop invariant (the software-pipelined core).                        *)
(*                                                                           *)
(* The x8 main loop (pc+0x4c0 .. back-edge b.lt pc+0xa0c -> 0x4c0) is        *)
(* software-pipelined: iteration i GHASH-folds the PREVIOUS group of 8       *)
(* ciphertext blocks (blocks 8i..8i+7, held in v8..v15) while AES-producing  *)
(* and storing the NEXT group (blocks 8(i+1)..8(i+1)+7).  So at the loop TOP *)
(* of iteration i the machine has STORED 8*(i+1) ciphertext blocks but only  *)
(* GHASHED 8*i of them - the lag the invariant must encode.                  *)
(*                                                                           *)
(* DIVERGENCE FROM x4: the back-edge is a                                    *)
(* FLAG-CONDITIONAL pointer compare - `cmp x0,x5` (pc+0x9a0) sets the flags, *)
(* `b.lt` (pc+0xa0c) branches back while x0 < x5 (signed).  x4 instead uses  *)
(* a countdown register + `cbnz`, so it uses ENSURES_WHILE_UP_TAC.  Here we  *)
(* MUST use ENSURES_WHILE_PUP_TAC (the post-test "P" variant) and carry a    *)
(* flag-fact conjunct `q i s`.  On ARM `b.lt` is taken iff ~(NF <=> VF)      *)
(* (instruction.ml:568, Condition_LT), so the flag fact is                   *)
(*      (read NF s <=> read VF s) <=> (i = k)                                *)
(* i.e. GE (fall through) exactly on the last iteration.  This is the ARM    *)
(* analogue of the x86 `(read ZF s <=> i = k)` PUP flag fact.                *)
(*                                                                           *)
(* Because this is a standalone loop lemma whose precondition IS the         *)
(* invariant at i=0 (at pc+0x4c0), the init subgoal is a reflexive 0-step    *)
(* ensures; the back-edge/exit subgoals only step the single b.lt            *)
(* (register/memory preserving) so every state conjunct passes through.      *)
(*                                                                           *)
(* The loop is software-pipelined, so the SIMD blocks are                    *)
(* loop-carried across the b.lt back-edge and MUST be pinned:                *)
(*      - v8..v15 = the PREVIOUS group's ciphertext (blocks 8i..8i+7),       *)
(*        GHASH-folded                                                       *)
(*        this iteration; each is `word_xor (aes_ctr_block aes256_cipher c nonce rk (    *)
(*          (8i+j)))                                                         *)
(*        (inblock (8i+j))` (identical to the out-memory store form; store   *)
(*          order                                                            *)
(*        confirmed: stp q8,q9,[x2] puts q8 at 8(i+1)+0, ..., q15 at         *)
(*          8(i+1)+7).                                                       *)
(*        Without these, `read Q19 s339` (the fold result the postcondition  *)
(*          must                                                             *)
(*        equal) is a word_pmul/word_xor over the UNPINNED ghosts q8,q9,...  *)
(*          and the                                                          *)
(*        goal is unprovable.  NOW ADDED below (24 conjuncts: pre/inv/post). *)
(*      - `8 * (k + 1) <= nb` antecedent ADDED: the 4 ciphertext stores      *)
(*        (stp q8..q15,[x2],#32 at 0x9e4..0xa04) FAIL the stepper's          *)
(*        "updates will not modify program code" check without a bound tying *)
(*          the                                                              *)
(*        block count nb to the loop count k (max store byte = 128k+128 =    *)
(*          16*nb).                                                          *)
(*        (This is the composition's nb-vs-k tie, surfacing early.)          *)
(* CONFIRMED-CORRECT invariant-at-(i+1) forms (goal conclusion matched       *)
(* verbatim after stepping): X0/X2 128*((i+1)+1), Q30 index 8*(i+1)+13, Q19  *)
(* byteswap128 nist_ghash..(8*(i+1)), Q31, all key/htable/tag/ivec mem,      *)
(* out-forall bound, flag fact (NF<=>VF)<=>(i+1=k), PC pc+0xa0c. Also        *)
(* loop-carried in the body: v0,v1,v2,v3,v4 are (first body use is `aese     *)
(* vN,v26`, a READ) = pre-AES CTR keystream blocks for the group AES'd this  *)
(* iteration; v5,v6,v7 are computed fresh inside (first use `rev32 vN,v30`). *)
(* Their exact counter-index forms must be pinned (derive via                *)
(* XOR_AES256_CIPHER_RECONSTRUCT + the setup counter bookkeeping) before the *)
(* body's AES side can close.  init stays reflexive so adding them will not  *)
(* break it.                                                                 *)
(* ------------------------------------------------------------------------- *)
(* body-stepping helpers.                                                    *)
(*                                                                           *)
(* The main-loop body reloads 8 plaintext blocks with `ldp q_even,q_odd,     *)
(* [x0],#32` (steps 263/295/303/304).  Because X0 post-increments, the       *)
(* SECOND element of each later pair is read at `word_add (word_add in_p     *)
(* (word ...)) (word 16)` where the offset arithmetic (e.g.                  *)
(* `(128*(i+1)+64)+48`) is NOT reduced to the literal `128*(i+1)+112` that   *)
(* the input-block reads use.  The stepper's memory resolution needs a       *)
(* syntactic address match, so the load stays opaque (`read(memory..)        *)
(* s_prev`) and DISCARD_OLDSTATE drops the ciphertext-register fact.  (The   *)
(* very first ldp, blocks 0/1, resolves natively because X0 is the           *)
(* un-incremented base there.)                                               *)
(*                                                                           *)
(* Fix, applied only at the incremented ldps (LDP_STEP4_TAC): re-derive the  *)
(* 8 plaintext reads at the CURRENT state from the persistent quantified     *)
(* in-memory forall (INBLOCKS_TAC - the specific s0 facts get dropped, the   *)
(* forall does not), verbose-step (no auto-discard), FLATTEN the nested      *)
(* word_adds, NORMOFF the offset arithmetic to the literal form, resolve the *)
(* now-matching memory reads, then discard old state.  NORMOFF_RULE reduces  *)
(* `word (a + c1 + c2 + ...)` offsets; is_inp_memfact selects the memory     *)
(* equations used to substitute the loads.  NSTEP is the ordinary per-step   *)
(* chain (flatten + NORMOFF + subword) for all other instructions.           *)
(* ------------------------------------------------------------------------- *)

let NORMOFF_RULE =
  CONV_RULE(ONCE_DEPTH_CONV(fun tm -> match tm with
      Comb(Const("word",_),_) ->
        (RAND_CONV(REWRITE_CONV[GSYM ADD_ASSOC] THENC DEPTH_CONV NUM_ADD_CONV)) tm
    | _ -> failwith "NORMOFF"));;

(* Selects ONLY the freshly re-derived input-block reads (`read (memory :>   *)
(* bytesN ..) s = inblock <idx>`), which LDP_STEP4_TAC substitutes into the  *)
(* ldp 2nd-element load.  The RHS-variable-headed guard                      *)
(* `is_var(fst(strip_comb rhs))` is essential: WITHOUT it this matched EVERY *)
(* `read(memory..) s = v` fact, so REWRITE_RULE memfacts rewrote each        *)
(* READ-ONLY key/mod/tag/ivec/htable fact BY ITSELF -> `v = v` -> `T`,       *)
(* silently deleting the ~30 read-only memory facts the postcondition needs  *)
(* (they are never regenerated, unlike the input reads which INBLOCKS_TAC    *)
(* re-asserts each call). Input reads carry the abstract value `inblock j`   *)
(* (a var applied to args); all read-only facts carry constant-headed values *)
(* (word_reversefields/word/...).                                            *)
let is_inp_memfact th =
  match concl th with
    Comb(Comb(Const("=",_), Comb(Comb(Const("read",_),
      Comb(Comb(Const(":>",_),Const("memory",_)),_)), _)), rhs) ->
        is_var(fst(strip_comb rhs))
  | _ -> false;;

(* ------------------------------------------------------------------------- *)
(* REPLAY-PERFORMANCE: the per-step subword normalisation is                 *)
(* O(n^2).  ASSUMPTION_STATE_UPDATE_TAC (common/components.ml:3341)          *)
(* re-stamps EVERY surviving assumption from s(n-1) to sN each step with its *)
(* RHS UNCHANGED, so a fact already put in subword-normal form last step     *)
(* comes back still-normal - yet the bare CONV_RULE(TOP_DEPTH_CONV           *)
(* WORD_SIMPLE_SUBWORD_ CONV) below re-traverses all ~140 carried facts      *)
(* every step, rebuilding each as theorems, a redundant no-op.  Over a       *)
(* 139-step drive, a redundant deep-conv pass per carried fact per step.     *)
(*                                                                           *)
(* WORD_SIMPLE_SUBWORD_CONV (hol-light Library/words.ml:4566) can ONLY fire  *)
(* on a `word_subword _ (NUMERAL,NUMERAL)` subterm - its outer match         *)
(* failwith's otherwise.  So TOP_DEPTH_CONV of it on a term WITHOUT that     *)
(* shape returns REFL (CONV_RULE is then the identity).  SUBWORD_NORM_RULE   *)
(* guards the conv with a cheap short-circuiting find_term for exactly that  *)
(* shape: it is PROOF-PRESERVING - for every theorem `th` it returns exactly *)
(* what `CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) th` returns      *)
(* (identical when the redex is present; th unchanged, = the conv's own      *)
(* no-op, when absent) - but it skips the expensive multi-rule traversal on  *)
(* the stable carried facts, restoring O(n).  Used by NSTEP / NSTEP_G /      *)
(* NSTEP_GP below.                                                           *)
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

(* PERF: the same short-circuit idea as SUBWORD_NORM_RULE,                   *)
(* applied to the word_add-nest flatten (WB_WADD_RULE / NSTEP_GP_WADD_RULE). *)
(* That REWRITE_RULE rewrites `word_add (word_add b (word m)) (word nn) ->   *)
(* word_add b (word(m+nn))`, which fires ONLY on a register-pointer fact     *)
(* carrying the doubly-nested word_add shape (produced by a post-increment   *)
(* ldr/str advancing X0/X2).  On EVERY other carried fact - the Q-register   *)
(* reads, the read-only key/mod/ivec/htable memory facts, the                *)
(* non-incrementing state facts - the redex is absent, so REWRITE_RULE still *)
(* builds its net and TOP_DEPTH-traverses the whole term only to return it   *)
(* unchanged.  Guarding with a cheap short-circuiting find_term for exactly  *)
(* that redex is PROOF-PRESERVING (identical to the bare rule: unchanged     *)
(* when the shape is absent, the rule's own no-op; identical rewrite when    *)
(* present) yet skips the net-walk on the facts that can never match.  In    *)
(* the tail drive the doubly-nested shape is present on ~0 of ~110           *)
(* carried facts at any given step (X0/X2 offsets are normalised away by     *)
(* NORMOFF the same step), so this is nearly a full skip.                    *)
(* Used by the guarded steppers below.                                       *)
let has_wadd_nest =
  can (find_term (fun t -> match t with
      Comb(Comb(Const("word_add",_),
             Comb(Comb(Const("word_add",_),_),
                  Comb(Const("word",_),_))),
           Comb(Const("word",_),_)) -> true
    | _ -> false));;

(* PERF: companion guard for NORMOFF_RULE, which is                          *)
(* CONV_RULE(ONCE_DEPTH_CONV ..) firing only on a `word (t)` subterm whose   *)
(* argument t is a sum (`_ + _`) it can renormalise - i.e. a                 *)
(* not-yet-collapsed offset like `word (128 * (k+1) + 16 + 32)`.  On every   *)
(* fact WITHOUT such a `word(sum)` the ONCE_DEPTH_CONV still descends the    *)
(* whole term to find nothing.  has_word_of_sum is a cheap short-circuiting  *)
(* find_term for `word (_ + _)`; guarding NORMOFF with it is                 *)
(* PROOF-PRESERVING (NORMOFF is a no-op on facts lacking `word(sum)`,        *)
(* exactly what the guard skips) and stacks on top of the has_wadd_nest      *)
(* guard.                                                                    *)
let has_word_of_sum =
  can (find_term (fun t -> match t with
      Comb(Const("word",_), Comb(Comb(Const("+",_),_),_)) -> true
    | _ -> false));;

(* The word_add-nest flatten used by every per-step stepper                  *)
(* (NSTEP/NSTEP_G/NSTEP_GP). Lifted out so the guarded steppers can compose  *)
(* it with NORMOFF/SUBWORD in ONE RULE_ASSUM_TAC pass and skip it on the     *)
(* giant GHASH accumulators (see NSTEP_G).                                   *)
let WB_WADD_RULE = REWRITE_RULE[WORD_RULE
  `word_add (word_add b (word m)) (word nn):int64 = word_add b (word(m+nn))`];;

(* PERF: fold the three per-step RULE_ASSUM_TAC passes                       *)
(* (word_add flatten, NORMOFF, SUBWORD_NORM) into ONE assumption-list        *)
(* traversal.  This is a pure refactor - the composed rule applied per fact  *)
(* is bit-identical to running the three rules in sequence - but it walks    *)
(* the assumption list once per step instead of three times.  No             *)
(* is_ghash_acc guard here: NSTEP drives SETUP, which carries NO large GHASH *)
(* accumulators (its facts stay small, at most a couple of Q19 facts live),  *)
(* so there is nothing to skip; the win is purely the single traversal.      *)
let NSTEP n =
  ARM_STEPS_TAC AES256_GCM_ENC_ALT_EXEC [n] THEN
  RULE_ASSUM_TAC(fun th -> SUBWORD_NORM_RULE (NORMOFF_RULE (WB_WADD_RULE th)));;

(* ------------------------------------------------------------------------- *)
(* GUARDED body stepper.                                                     *)
(*                                                                           *)
(* NSTEP applies WORD_SIMPLE_SUBWORD_CONV after EVERY step.  The GHASH       *)
(* accumulators Q17/Q18/Q19 are word_join-headed Karatsuba lane sums, and    *)
(* that conv pushes word_subword INTO the joins, collapsing                  *)
(* `word_subword(word_join a b)(0,64)`->b etc.  This destroys the `LO p1` /  *)
(* `ext p1` structure `ghash_reduce_raw`'s definition needs, so the body-end *)
(* Q19 residual can no longer be folded back to ghash_reduce_raw.            *)
(*                                                                           *)
(* NSTEP_G is NSTEP with the per-step subword conv SKIPPED on any assumption *)
(* whose read-component is Q17/Q18/Q19, preserving the accumulators' ext/LO  *)
(* structure so the final Q19 stays ghash_reduce_raw-foldable.  The v0..v15  *)
(* counter/ciphertext facts (all other registers) are still normalised as    *)
(* before, so the cheap-close is unaffected.                                 *)
let is_ghash_acc th =
  let c = concl th in
  can (find_term (fun t -> match t with
      Comb(Const("read",_), r) ->
        (match r with
         | Const("Q17",_) | Const("Q18",_) | Const("Q19",_) -> true
         | _ -> false)
    | _ -> false)) c;;

(* PERF: same optimisation as NSTEP_GP - fold the three                      *)
(* per-step RULE_ASSUM_TAC passes (word_add flatten, NORMOFF, SUBWORD_NORM)  *)
(* into ONE, and extend the is_ghash_acc (Q17/18/19) guard to ALSO skip the  *)
(* word_add flatten and NORMOFF on the giant GHASH accumulators. Those two   *)
(* passes are identity on the                                                *)
(* word_join/word_subword accumulator terms (word_add rule fires only on     *)
(* register-pointer shape; NORMOFF only on word(c1+c2+..) offsets), so       *)
(* skipping them there is proof-preserving while avoiding an O(term-size)    *)
(* traversal of the accumulator every step.                                  *)
let NSTEP_G n =
  ARM_STEPS_TAC AES256_GCM_ENC_ALT_EXEC [n] THEN
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
    (* PERF: the block-index obligation is `8*(i+1)+b < nb`, closed                *)
    (* by just {i < k, 8*(k+1) <= nb}.  Targeted UNDISCH of exactly the two          *)
    (* needed hyps + bare ARITH_TAC is the same idiom the body's flag-close          *)
    (* already uses (see the flag_arith note below); it is proof-preserving.         *)
    UNDISCH_TAC `8 * (k + 1) <= nb` THEN UNDISCH_TAC `(i:num) < k` THEN ARITH_TAC;
    ALL_TAC];;

let LDP_STEP4_TAC n =
  let sprev = "s"^string_of_int (n-1) in
  let sn = "s"^string_of_int n in
  INBLOCKS_TAC sprev THEN
  ARM_VERBOSE_STEP_TAC AES256_GCM_ENC_ALT_EXEC sn THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
    `word_add (word_add b (word m)) (word nn):int64 = word_add b (word(m+nn))`]) THEN
  RULE_ASSUM_TAC NORMOFF_RULE THEN
  (fun (asl,w as gl) ->
     let memfacts = filter is_inp_memfact (map snd asl) in
     RULE_ASSUM_TAC(REWRITE_RULE memfacts) gl) THEN
  RULE_ASSUM_TAC SUBWORD_NORM_RULE THEN
  DISCARD_OLDSTATE_TAC sn;;

(* ------------------------------------------------------------------------- *)
(* Flag-close lemmas for the main-loop body (blocker C).                     *)
(*                                                                           *)
(* The loop back-edge is a signed pointer compare `cmp x0,x5; b.lt` at pc    *)
(* 0x9a0/0xa0c: X0 = in_p + 128*(i+2) (four `ldp [x0],#32` past the loop     *)
(* top), X5 = end_p.  After the cheap-close ASM_REWRITE, the invariant's     *)
(* flag conjunct q(i+1) has been reduced to the raw NF!=VF biconditional     *)
(* over `word_sub X0 end_p`.  BRIDGE_GE recognises that biconditional as the *)
(* signed GE `ival end_p <= ival X0`; IV_ADD linearises each additive ival   *)
(* under the buffer-end no-wrap bound `val in_p + 128*(k+1) < 2^63`;         *)
(* INT/ARITH then reduces the whole thing to `i + 1 = k` using the body hyp  *)
(* `i < k`. The no-wrap bound is supplied by MAIN_LOOP's new end_p           *)
(* antecedent.                                                               *)

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

(* ------------------------------------------------------------------------- *)
(* SETUP branch-discharge lemmas.                                            *)
(*                                                                           *)
(* The pipeline-fill setup has two `cmp x0,x5; b.ge` guards - the tail check *)
(* at 0x448/0x44c and the prepretail check at 0x480/0x4bc - both comparing   *)
(* the running input pointer X0 against the loop-end pointer                 *)
(*      X5 = ((byte_len DIV 8) - 1) & ~127  +  in_p                          *)
(* (hardware: sub x5,x5,#1; and x5,x5,#0xffffffffffffff80; add x5,x5,x0 at   *)
(* 0x6c/0x70/0x74, with x5 initialised to x9 = word(byte_len DIV 8)).  Both  *)
(* guards must fall through (b.ge NOT taken) when k >= 1, i.e. when more     *)
(* than one 8-block group remains.                                           *)
(*                                                                           *)
(* X5_END_PTR: under block-aligned byte_len = 128*nb with nb = 8*(k+2), the  *)
(* round-down-to-128 mask collapses X5 to the loop-end pointer end_p = in_p  *)
(*   + 128*(k+1) - the SAME end_p MAIN_LOOP's antecedent pins.  The key      *)
(* arithmetic: (16*nb - 1) & ~127 = 128*(k+1) because 16*nb = 128*(k+2) =    *)
(* 128*(k+1) + 128, so (128*(k+1)+127) rounds down to 128*(k+1).  This       *)
(* CONFIRMS the k = nb DIV 8 - 2 accounting (the last 8-group is drained by  *)
(* prepretail, hence -2 not -1). Proof via WORD_AND_NOT_MASK_WORD (the       *)
(* clear-low-7-bits lemma) + VAL_WORD_SUB_CASES.                             *)
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

(* end_p = in_p + 128*(k+1) is strictly ABOVE in_p (signed), since 128*(k+1) *)
(* >= 128 > 0 and there is no signed wrap.  So the `cmp x0,x5; b.ge` with X0 *)
(* = in_p (or in_p+128) at the guards does NOT take the branch.              *)
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

(* Collapse the first-guard conditional (the exact NF!=VF biconditional the  *)
(* stepper emits for `cmp x0,x5; b.ge` with X0 = in_p) to F, so the          *)
(* conditional PC resolves to the fall-through.  X5 here is the raw hardware *)
(* form ((128*nb DIV 8) - 1) & ~127 + in_p; the lemma normalises it to end_p *)
(* via X5_END_PTR and finishes with BRIDGE_GE + SETUP_GE_FALSE.              *)
let DISPATCH_NOT_TAKEN = prove
 (`!nb:num. 128 * nb < 2 EXP 64 /\ ~(nb = 2)
    ==> (val (word_sub (word ((128 * nb) DIV 8):int64) (word 32)) = 0 <=> F)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(128 * nb) DIV 8 = 16 * nb` SUBST1_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `16 * nb < 2 EXP 64 /\ 32 < 2 EXP 64` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[VAL_EQ_0] THEN
  SUBGOAL_THEN
    `(word_sub (word (16 * nb):int64) (word 32) = word 0) <=> (word (16*nb):int64 = word 32)`
   SUBST1_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM VAL_EQ; VAL_WORD; DIMINDEX_64; MOD_LT] THEN
  ASM_ARITH_TAC);;

(* TAKEN twin of DISPATCH_NOT_TAKEN - for nb=2 the fast2 dispatch `cmp       *)
(* x9,#32; b.eq L256_enc_fast2` branches TAKEN (x9 = (128*2)DIV8 = 32).      *)
let DISPATCH_TAKEN = prove
 (`!nb:num. nb = 2
    ==> (val (word_sub (word ((128 * nb) DIV 8):int64) (word 32)) = 0 <=> T)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(128 * nb) DIV 8 = 32` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[WORD_RULE `word_sub (word 32:int64) (word 32) = word 0`] THEN
  REWRITE_TAC[VAL_WORD_0]);;

(* nb=4 (64B) selector: `cmp x9,#0x40; b.le L256_enc_small`@pc+0x4c/0x50     *)
(* routes nb<=4 to L256_enc_small, where small_1/2/3 `b.eq` fall through.    *)
(* (the SETUP legs + SETUP0/_TAIL, all reached only when nb!=2 already).  x9 *)
(* = word(16*nb).                                                            *)
let DISPATCH4_NOT_TAKEN = prove
 (`!nb:num. 128 * nb < 2 EXP 64 /\ ~(nb = 4)
    ==> (val (word_sub (word ((128 * nb) DIV 8):int64) (word 64)) = 0 <=> F)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(128 * nb) DIV 8 = 16 * nb` SUBST1_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `16 * nb < 2 EXP 64 /\ 64 < 2 EXP 64` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[VAL_EQ_0] THEN
  SUBGOAL_THEN
    `(word_sub (word (16 * nb):int64) (word 64) = word 0) <=> (word (16*nb):int64 = word 64)`
   SUBST1_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM VAL_EQ; VAL_WORD; DIMINDEX_64; MOD_LT] THEN
  ASM_ARITH_TAC);;

(* TAKEN twin - for nb=4 the fast4 dispatch branches TAKEN                   *)
(* (x9=(128*4)DIV8=64).                                                      *)
let DISPATCH4_TAKEN = prove
 (`!nb:num. nb = 4
    ==> (val (word_sub (word ((128 * nb) DIV 8):int64) (word 64)) = 0 <=> T)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(128 * nb) DIV 8 = 64` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[WORD_RULE `word_sub (word 64:int64) (word 64) = word 0`] THEN
  REWRITE_TAC[VAL_WORD_0]);;

(* nb=1 (16B) selector: `cmp x9,#0x10; b.eq L256_enc_small_1`@0x152c/0x1530  *)
(* (inside L256_enc_small).  NOT-taken twin for nb != 1; x9 =                *)
(* word(16*nb).                                                              *)
let DISPATCH1_NOT_TAKEN = prove
 (`!nb:num. 128 * nb < 2 EXP 64 /\ ~(nb = 1)
    ==> (val (word_sub (word ((128 * nb) DIV 8):int64) (word 16)) = 0 <=> F)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(128 * nb) DIV 8 = 16 * nb` SUBST1_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `16 * nb < 2 EXP 64 /\ 16 < 2 EXP 64` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[VAL_EQ_0] THEN
  SUBGOAL_THEN
    `(word_sub (word (16 * nb):int64) (word 16) = word 0) <=> (word (16*nb):int64 = word 16)`
   SUBST1_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM VAL_EQ; VAL_WORD; DIMINDEX_64; MOD_LT] THEN
  ASM_ARITH_TAC);;

let DISPATCH1_TAKEN = prove
 (`!nb:num. nb = 1
    ==> (val (word_sub (word ((128 * nb) DIV 8):int64) (word 16)) = 0 <=> T)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(128 * nb) DIV 8 = 16` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[WORD_RULE `word_sub (word 16:int64) (word 16) = word 0`] THEN
  REWRITE_TAC[VAL_WORD_0]);;

(* nb=3 (48B) selector: `cmp x9,#0x30; b.eq L256_enc_small_3`@0x153c/0x1540. *)
let DISPATCH3_NOT_TAKEN = prove
 (`!nb:num. 128 * nb < 2 EXP 64 /\ ~(nb = 3)
    ==> (val (word_sub (word ((128 * nb) DIV 8):int64) (word 48)) = 0 <=> F)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(128 * nb) DIV 8 = 16 * nb` SUBST1_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `16 * nb < 2 EXP 64 /\ 48 < 2 EXP 64` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[VAL_EQ_0] THEN
  SUBGOAL_THEN
    `(word_sub (word (16 * nb):int64) (word 48) = word 0) <=> (word (16*nb):int64 = word 48)`
   SUBST1_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM VAL_EQ; VAL_WORD; DIMINDEX_64; MOD_LT] THEN
  ASM_ARITH_TAC);;

let DISPATCH3_TAKEN = prove
 (`!nb:num. nb = 3
    ==> (val (word_sub (word ((128 * nb) DIV 8):int64) (word 48)) = 0 <=> T)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(128 * nb) DIV 8 = 48` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[WORD_RULE `word_sub (word 48:int64) (word 48) = word 0`] THEN
  REWRITE_TAC[VAL_WORD_0]);;

(* FUSED nb<=4: the single entry test `cmp x9,#64; b.le                      *)
(* L256_enc_small`. ARM_STEP emits the b.le condition as the full `ZF \/     *)
(* ~(NF<=>VF)`.  The ZF disjunct `val(word_sub(word((128*nb)DIV8))(word      *)
(* 64))=0` is resolved by the EXISTING DISPATCH4_{TAKEN,NOT_TAKEN} (same #64 *)
(* immediate).  These two lemmas resolve the remaining `~(NF<=>VF)`          *)
(* (signed-LT) disjunct.  Helpers first.                                     *)
let IVAL_WORD_SUB_SMALL = prove
 (`!a b. a < 2 EXP 63 /\ b < 2 EXP 63
     ==> ival(word_sub (word a) (word b):int64) = &a - &b`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[WORD_IWORD; GSYM IWORD_INT_SUB] THEN
  MATCH_MP_TAC IVAL_IWORD THEN
  REWRITE_TAC[DIMINDEX_64; ARITH_RULE `64 - 1 = 63`] THEN
  SUBGOAL_THEN `&a:int < &2 pow 63 /\ &b:int < &2 pow 63` MP_TAC THENL
   [REWRITE_TAC[GSYM INT_OF_NUM_POW; INT_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC `a:num` INT_POS) THEN MP_TAC(SPEC `b:num` INT_POS) THEN INT_ARITH_TAC);;

(* nb>=5 (x9=16*nb>=80>64): the signed-LT disjunct is FALSE -> b.le NOT      *)
(* taken (with DISPATCH4_NOT_TAKEN killing the ZF disjunct).  Used by        *)
(* SETUP*/SETUP0.                                                            *)
let DISPATCH_SMALL_NOT_TAKEN = prove
 (`!nb:num. 128 * nb < 2 EXP 64 /\ 5 <= nb
    ==> (~(ival (word_sub (word ((128 * nb) DIV 8):int64) (word 64)) < &0 <=>
           ~(ival (word ((128 * nb) DIV 8):int64) - &64 =
             ival (word_sub (word ((128 * nb) DIV 8):int64) (word 64)))) <=> F)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(128 * nb) DIV 8 = 16 * nb` SUBST1_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `64 <= 16 * nb` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `16 * nb < 2 EXP 63` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `16 * nb - 64 < 2 EXP 63` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `word_sub (word (16 * nb):int64) (word 64) = word (16 * nb - 64)` SUBST1_TAC THENL
   [ASM_SIMP_TAC[WORD_SUB]; ALL_TAC] THEN
  ASM_SIMP_TAC[IVAL_WORD_SMALL; INT_OF_NUM_SUB] THEN
  MP_TAC(ASSUME `64 <= 16 * nb`) THEN REWRITE_TAC[GSYM INT_OF_NUM_LE] THEN INT_ARITH_TAC);;

(* nb in {1,2,3} (x9=16*nb<64): the signed-LT disjunct is TRUE -> b.le taken *)
(* (with DISPATCH4_NOT_TAKEN, ZF disjunct F).  nb=4 taken via                *)
(* DISPATCH4_TAKEN alone.                                                    *)
let DISPATCH_SMALL_TAKEN = prove
 (`!nb:num. 1 <= nb /\ nb <= 3
    ==> (~(ival (word_sub (word ((128 * nb) DIV 8):int64) (word 64)) < &0 <=>
           ~(ival (word ((128 * nb) DIV 8):int64) - &64 =
             ival (word_sub (word ((128 * nb) DIV 8):int64) (word 64)))) <=> T)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(128 * nb) DIV 8 = 16 * nb` SUBST1_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `16 * nb < 64 /\ 16 * nb < 2 EXP 63 /\ 64 < 2 EXP 63` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[IVAL_WORD_SMALL; IVAL_WORD_SUB_SMALL] THEN
  MP_TAC(ASSUME `16 * nb < 64`) THEN REWRITE_TAC[GSYM INT_OF_NUM_LT] THEN INT_ARITH_TAC);;




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

(* SETUP_BRANCH_COND_TRUE_2: the 2nd setup guard (b.ge@0x4bc, cmp with X0 =  *)
(* word_add in_p (word 128) after consuming one 8-group) is TAKEN for        *)
(* groups=1 (k=0): round-down end_p = word_add in_p (word(128*(k+1))) =      *)
(* in_p+128 at k=0, so X0 = end_p and b.ge collapses to T -> PC = 0xa10      *)
(* (PREPRETAIL).  Mirror of WB_BRANCH_COND_TRUE (1st guard) for the 2nd      *)
(* guard.                                                                    *)
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


(* SETUP-specific input-block re-derivation and ldp stepper.  In the setup   *)
(* the 8 plaintext blocks live at in_p + 16*j (j=0..7) - NOT the loop body's *)
(* 128*(i+1)+off.  SETUP_INBLOCKS_TAC re-asserts all 8 reads at state        *)
(* `sname` from the persistent quantified input-forall; LDP_SETUP_TAC is     *)
(* LDP_STEP4 with that variant (needed for the post-incremented ldp [x0],#32 *)
(* 2nd loads).                                                               *)
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
   [(* PERF: after FIRST_ASSUM MATCH_MP_TAC each of the 8                     *)
    (* obligations is the trivial `b < nb` (b = literal 0..7), closed by      *)
(* just the bound `8 * (k + 1) <= nb` (b < 8 <= 8*(k+1) <= nb).  A bare      *)
(* ASM_ARITH_TAC here would drag ALL carried facts into the arith decision   *)
(* procedure (the dominant cost of the setup proof).  Targeted               *)
(* UNDISCH of exactly the one needed hyp + bare ARITH_TAC (the same idiom    *)
(* the body's INBLOCKS_TAC uses) closes each cheaply and is                  *)
(* proof-preserving (the resulting STRIP_ASSUME_TAC state is unchanged).     *)
(* All three setup legs that call it carry `8 * (k + 1) <= nb` verbatim.     *)
    REPEAT CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `8 * (k + 1) <= nb` THEN ARITH_TAC;
    ALL_TAC];;

let LDP_SETUP_TAC n =
  let sprev = "s"^string_of_int (n-1) in
  let sn = "s"^string_of_int n in
  SETUP_INBLOCKS_TAC sprev THEN
  ARM_VERBOSE_STEP_TAC AES256_GCM_ENC_ALT_EXEC sn THEN
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
     (* drops the register fact.  This LOAD-side mismatch (NOT the              *)
     (* stp store) is why Q8..Q15 were lost - Q8 is                             *)
     (* already absent at s255 (right after the first ldp@0x450), BEFORE any    *)
     (* store.  With the norm, all 8 ciphertext regs survive to s282.           *)
     let norm th =
       REWRITE_RULE[WORD_ADD_0]
         (try CONV_RULE(TOP_DEPTH_CONV NUM_MULT_CONV) th with _ -> th) in
     let memfacts = map norm (filter is_inp_memfact (map snd asl)) in
     RULE_ASSUM_TAC(REWRITE_RULE memfacts) gl) THEN
  RULE_ASSUM_TAC SUBWORD_NORM_RULE THEN
  DISCARD_OLDSTATE_TAC sn;;

(* ------------------------------------------------------------------------- *)
(* GF(2)-linearity (additivity over word_xor) of the reduction primitives.   *)
(*                                                                           *)
(* Both polyval_reduce_prop3 and ghash_reduce_raw are compositions of        *)
(* GF(2)-linear word ops (word_subword, word_pmul BY A CONSTANT, word_xor,   *)
(* word_join), hence additive.  These are the KEY lemmas                     *)
(* that let the pipelined-GHASH Q19 fold DISTRIBUTE                          *)
(* the summed-lane hardware reduce over the 8 in-flight blocks, so each      *)
(* block individually fires GHASH_REDUCE_RAW_KARATSUBA_IS_DOT - replacing    *)
(* the byteswap128(prop3 A) = prop3 B lane-match.                            *)
(*                                                                           *)
(* PROOF RECIPE (the crux - WORD_BITWISE_RULE alone fails because it         *)
(* cannot crack opaque `word_pmul a w`): first distribute the opaque pmuls   *)
(* with `WORD_PMUL_XOR` (hol-light Library/words.ml) so every pmul atom is   *)
(* SHARED across both sides, then push word_xor into the word_join lanes and *)
(* split into 64-bit lanes closed by WORD_BITWISE_RULE (pure XOR ring, NO    *)
(* bit-blasting of pmul).  A whole-goal WORD_BLAST does NOT terminate in     *)
(* practical time (it bit-blasts the pmuls); the lane-split is essential.    *)
(* ------------------------------------------------------------------------- *)

(* word_xor of two word_joins is the join of the xored lanes (64- and        *)
(* 128-bit-lane variants) + lane-split helpers.                              *)
let JOIN_XOR_LANE = WORD_BLAST
  `word_xor (word_join (a:int64) (b:int64):int128) (word_join c d) =
   word_join (word_xor a c) (word_xor b d)`;;

let JOIN_EQ_LANE = MESON[]
  `(a:int64) = c /\ (b:int64) = d ==> word_join a b:int128 = word_join c d`;;

let JOIN_EQ_128 = MESON[]
  `(a:int128) = c /\ (b:int128) = d ==> word_join a b:int256 = word_join c d`;;

(* polyval_reduce_prop3 distributes over word_xor.                           *)
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

(* ghash_reduce_raw is jointly additive in its three arguments.  Proved via  *)
(* the polyval_reduce_g2 bridge (so its two nested pmul layers become a      *)
(* single prop3 of a linear argument) + PROP3_XOR + a 4-lane split.          *)
let GHASH_REDUCE_RAW_XOR = prove
 (`!a1 a2 b1 b2 c1 c2:int128.
     ghash_reduce_raw (word_xor a1 a2) (word_xor b1 b2) (word_xor c1 c2) =
     word_xor (ghash_reduce_raw a1 b1 c1) (ghash_reduce_raw a2 b2 c2)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[GHASH_REDUCE_RAW_IS_POLYVAL_G2; POLYVAL_REDUCE_G2] THEN
  REWRITE_TAC[WORD_SUBWORD_XOR] THEN
  REWRITE_TAC[GSYM PROP3_XOR] THEN
  AP_TERM_TAC THEN
  REWRITE_TAC[JOIN_XOR_256; JOIN_XOR_LANE] THEN
  MATCH_MP_TAC JOIN_EQ_128 THEN CONJ_TAC THEN
  MATCH_MP_TAC JOIN_EQ_LANE THEN CONJ_TAC THEN
  CONV_TAC WORD_BITWISE_RULE);;

(* ------------------------------------------------------------------------- *)
(* Obstruction-3 building blocks - reduce the summed lanes in                *)
(* the EXACT hardware lane order the body-end residual presents.             *)
(*                                                                           *)
(* The reassembled body-end reduce is `ghash_reduce_raw P0 P1 P2` where each *)
(* Pl is an 8-term LEFT-associated word_xor sum of per-block Karatsuba       *)
(* pieces, but the three lanes DISAGREE on block order:                      *)
(*      P0 (lo.lo)  block order [1;0;2;3;4;5;6;7], b-lane =                  *)
(*        subword(h^p)(0,64)                                                 *)
(*      P1 (cross)  block order [1;0;3;2;5;4;7;6], b-lane =                  *)
(*        karatsuba_mid(h^p)                                                 *)
(*      P2 (hi.hi)  block order [1;0;2;3;4;5;6;7], b-lane =                  *)
(*        subword(h^p)(64,64)                                                *)
(* (block j is paired with h-power h^{7-j}).  KARATSUBA_IS_DOT_HW handles    *)
(* the per-block cross-lane form, and REORD_CROSS AC-reorders the cross lane *)
(* [1;0;3;2..] -> [1;0;2;3..] so the shared-order reduce fires - both        *)
(* consumed by GHASH_REDUCE_RAW_DIST8_PLAIN (the plain-invariant route).     *)
(* ------------------------------------------------------------------------- *)

(* Per-block: the cross lane in the body uses `karatsuba_mid b` and an a-arg *)
(* subword order (64,64),(0,64); normalise both to KARATSUBA_IS_DOT's form.  *)
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

(* AC-reorder a LEFT-associated 8-term int128 word_xor from the cross-lane   *)
(* block order [1;0;3;2;5;4;7;6] to the shared order [1;0;2;3;4;5;6;7].      *)
let REORD_CROSS = prove
 (`word_xor (word_xor (word_xor (word_xor (word_xor (word_xor (word_xor
      (x1:int128) x0) x3) x2) x5) x4) x7) x6 =
   word_xor (word_xor (word_xor (word_xor (word_xor (word_xor (word_xor
      x1 x0) x2) x3) x4) x5) x6) x7`,
  CONV_TAC WORD_BITWISE_RULE);;

(* Per-block-0 reduce, in the EXACT raw swapped-lane form the body produces  *)
(* (sofar's two 64-bit halves crossed with cb0's - the store-order           *)
(* byteswap):                                                                *)
(*      lo.lo  = word_xor (subword sofar (64,64)) (subword cb0 (0,64))       *)
(*      hi.hi  = word_xor (subword sofar (0,64))  (subword cb0 (64,64))      *)
(*      cross  = word_xor <hi-shape> <lo-shape>                              *)
(* This reduces to polyval_dot (byteswap128 sofar (x) cb0) b.  The block-0   *)
(* accumulator byteswap is absorbed INSIDE this lemma (ABBREV byteswap128    *)
(* sofar so the swap-lane rewrites do not re-fire on their own output): a    *)
(* global subword fold cannot be used directly on the body residual.         *)
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

(* Q19 fold: the body-order 8-block distribution with ALL blocks in the    *)
(* CLEAN (non-crossed) form - block order [1;0;2;3;4;5;6;7] on lo.lo/hi.hi,  *)
(* [1;0;3;2;5;4;7;6] on the cross lane - reduces to the canonical XOR-sum of *)
(* the eight per-block polyval_dots.  It FIRES on the body-end Q19 residual  *)
(* once the Q19 loop- invariant conjunct is stated WITHOUT the `byteswap128` *)
(* wrapper (`read Q19 s = nist_ghash..8i`, not                               *)
(* `byteswap128(nist_ghash..8i)`).  Testing established EMPIRICALLY (via     *)
(* a faithful re-derivation of the H2 body residual) that under the plain    *)
(* invariant block 0 enters the reduce as the ordinary `nist_cipher_block    *)
(* (x) sofar` (NO store-order byteswap), so no block-0 crossing is needed -  *)
(* this clean flat-sum form is what matches.                                 *)
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
(* Q19 GHASH-fold tactic                                                     *)
(*                                                                           *)
(* Applied to the body-end Q19 residual conjunct                             *)
(*      `<raw ghash reduce of the 8 in-flight ciphertext blocks> =           *)
(*       byteswap128(nist_ghash H tag0 (list_of_seq nist_cipher_block        *)
(*         (8i+8)))`                                                         *)
(* AFTER splitting it off the raw post-FINAL_STATE conjunction but BEFORE    *)
(* the cheap-close (whose WORD_SIMPLE_SUBWORD_CONV would destroy the         *)
(* foldable ext/LO structure - the fold FAILS                                *)
(* post-cheap-close). NSTEP_G (guarded stepper) is what keeps the            *)
(* accumulator foldable through the 339 body steps.                          *)
(*                                                                           *)
(* Chain:                                                                    *)
(*     1. AC-swap the eor3 top XOR into ghash_reduce_raw's grouping;         *)
(*     2. GSYM ghash_reduce_raw (RECON_GRR) - FIRES (LHS 186k->67k);         *)
(*     3. reassemble the 8 cipherblocks and distribute the reduce over the   *)
(*        8 clean blocks with GHASH_REDUCE_RAW_DIST8_PLAIN;                  *)
(*     4. fold the RHS nist_ghash to a prop3 chain: NIST_GHASH_IS_POLYVAL +  *)
(*        8(i+1)=SUC^8(8i) + list_of_seq + APPEND + GHASH_ACC_APPEND, then   *)
(*        normalise the CONS SUC-form indices to +n (ADD1;GSYM ADD_ASSOC;    *)
(*        NUM_ADD_CONV) so the batched ISPECL matches, then                  *)
(*        GHASH_POLYVAL_ACC_BATCHED collapses it to the same prop3 sum.      *)
(* See Q19_FOLD_TAC below.                                                   *)
let RECON_GRR = REWRITE_RULE[LET_DEF; LET_END_DEF] (GSYM ghash_reduce_raw);;

(* The invariant states the Q19 accumulator PLAIN, not wrapped in a          *)
(* `byteswap128`: read Q19 s = nist_ghash..8i, rather than                   *)
(* read Q19 s = byteswap128(nist_ghash..8i).  The x8 body has only a         *)
(* leading `ext v19`@0x4f4 and no trailing ext (byteswap-parity 0), unlike   *)
(* the x4 kernels, which have both a leading `ext v17` and a trailing        *)
(* `ext v11` at body-end (byteswap-parity 1).  With the plain invariant the  *)
(* body-end reduce (parity 0) matches the plain RHS (parity 0) and the fold  *)
(* closes via the flat 8-`polyval_dot`-sum route; a byteswap-wrapped         *)
(* invariant (parity 1) could not, since byteswap identities only move the   *)
(* wrapper side-to-side.  Block 0 enters the reduce as the ordinary clean    *)
(* `nist_cipher_block (x) sofar` (no store-order byteswap), so the fold uses *)
(* GHASH_REDUCE_RAW_DIST8_PLAIN (all blocks clean).                          *)
let Q19_FOLD_TAC =
  ONCE_REWRITE_TAC[WORD_BITWISE_RULE
    `word_xor (word_xor (x:int128) e) p = word_xor (word_xor x p) e`] THEN
  REWRITE_TAC[RECON_GRR] THEN
  (* Reassemble the 8 cipherblocks (the plain invariant leaves no               *)
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
  (* RHS: fold nist_ghash..8(i+1) to prop3(pmul chain) - plain, no byteswap.     *)
  REWRITE_TAC[NIST_GHASH_IS_POLYVAL] THEN
  REWRITE_TAC[ARITH_RULE
    `8 * (i + 1) = SUC(SUC(SUC(SUC(SUC(SUC(SUC(SUC(8 * i))))))))`] THEN
  REWRITE_TAC[list_of_seq] THEN REWRITE_TAC[GSYM APPEND_ASSOC] THEN
  REWRITE_TAC[APPEND] THEN
  REWRITE_TAC[GHASH_ACC_APPEND] THEN
  REWRITE_TAC[ADD1; GSYM ADD_ASSOC] THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
  MP_TAC(ISPECL
    [`ghash_twist (aes256_cipher (word 0) rk)`;
     `[nist_cipher_block aes256_cipher c nonce rk inblock (8*i+1);
       nist_cipher_block aes256_cipher c nonce rk inblock (8*i+2);
       nist_cipher_block aes256_cipher c nonce rk inblock (8*i+3);
       nist_cipher_block aes256_cipher c nonce rk inblock (8*i+4);
       nist_cipher_block aes256_cipher c nonce rk inblock (8*i+5);
       nist_cipher_block aes256_cipher c nonce rk inblock (8*i+6);
       nist_cipher_block aes256_cipher c nonce rk inblock (8*i+7)]:(int128)list`;
     `ghash_polyval_acc (ghash_twist (aes256_cipher (word 0) rk)) tag0
        (list_of_seq (nist_cipher_block aes256_cipher c nonce rk inblock) (8*i))`;
     `nist_cipher_block aes256_cipher c nonce rk inblock (8*i)`]
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

(* PERF: the body cheap-close dispatcher rewrites the                        *)
(* out-forall bound `j < 8*((i+1)+1)` into its 9-way disjunction split via   *)
(* an INLINE `ARITH_RULE` that was re-proven for each of the ~19 residual    *)
(* goals under `REPEAT CONJ_TAC`, which was essentially the ENTIRE           *)
(* post-drive close cost.  Hoist it to a single top-level theorem computed   *)
(* ONCE and REWRITE_TAC[..] with it per goal - byte-identical rewrite, hence *)
(* proof-preserving.                                                         *)
let MAIN_LOOP_OUT_DISJSPLIT = ARITH_RULE
  `j < 8 * ((i + 1) + 1) <=>
   j < 8 * (i+1) \/ j = 8*(i+1) \/ j = 8*(i+1) + 1 \/
   j = 8*(i+1) + 2 \/ j = 8*(i+1) + 3 \/ j = 8*(i+1) + 4 \/
   j = 8*(i+1) + 5 \/ j = 8*(i+1) + 6 \/ j = 8*(i+1) + 7`;;

let AES256_GCM_ENC_ALT_MAIN_LOOP = prove
 (`!in_p out_p tag_p ivec_p key_p htable_p mod_p end_p
     tag0 nonce c rk inblock nb k pc.
    ~(k = 0) /\
    8 * (k + 1) <= nb /\
    end_p = word_add in_p (word (128 * (k + 1))) /\
    val in_p + 128 * (k + 1) < 2 EXP 63 /\
    nonoverlapping (out_p, 16 * nb)
                   (word pc, LENGTH aes256_gcm_enc_alt_tmc) /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * nb)]
      [(in_p, 16 * nb); (key_p, 240); (htable_p, 192);
       (tag_p, 16); (ivec_p, 16); (mod_p, 8)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) aes256_gcm_enc_alt_tmc /\
           read PC s = word (pc + 0x4c0) /\
           read X0 s = word_add in_p (word (128 * (0 + 1))) /\
           read X2 s = word_add out_p (word (128 * (0 + 1))) /\
           read X3 s = tag_p /\
           read X9 s = word (16 * nb) /\
           read X4 s = word_add in_p (word (16 * nb)) /\
           read X16 s = ivec_p /\
           read X5 s = end_p /\
           read X6 s = htable_p /\
           read X10 s = mod_p /\
           read X11 s = key_p /\
           read (memory :> bytes64 mod_p) s = word 0xc200000000000000 /\
           wordlist_from_memory(key_p,15) s = MAP (word_reversefields 8) rk /\
           read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce c) /\
           read Q30 s = word_reversefields 32 (ctr_block nonce (8 * 0 + c + 13)) /\
           read Q31 s = word 79228162514264337593543950336 /\
           read Q19 s =
             nist_ghash (aes256_cipher (word 0) rk) tag0
                 (list_of_seq (nist_cipher_block aes256_cipher c nonce rk inblock) (8 * 0)) /\
           read Q8 s = word_xor (aes_ctr_block aes256_cipher c nonce rk ((8 * 0 + 0))) (inblock (8 * 0 + 0)) /\
           read Q9 s = word_xor (aes_ctr_block aes256_cipher c nonce rk ((8 * 0 + 1))) (inblock (8 * 0 + 1)) /\
           read Q10 s = word_xor (aes_ctr_block aes256_cipher c nonce rk ((8 * 0 + 2))) (inblock (8 * 0 + 2)) /\
           read Q11 s = word_xor (aes_ctr_block aes256_cipher c nonce rk ((8 * 0 + 3))) (inblock (8 * 0 + 3)) /\
           read Q12 s = word_xor (aes_ctr_block aes256_cipher c nonce rk ((8 * 0 + 4))) (inblock (8 * 0 + 4)) /\
           read Q13 s = word_xor (aes_ctr_block aes256_cipher c nonce rk ((8 * 0 + 5))) (inblock (8 * 0 + 5)) /\
           read Q14 s = word_xor (aes_ctr_block aes256_cipher c nonce rk ((8 * 0 + 6))) (inblock (8 * 0 + 6)) /\
           read Q15 s = word_xor (aes_ctr_block aes256_cipher c nonce rk ((8 * 0 + 7))) (inblock (8 * 0 + 7)) /\
           read Q0 s = word_reversefields 8 (ctr_block nonce (8 * 0 + c + 8)) /\
           read Q1 s = word_reversefields 8 (ctr_block nonce (8 * 0 + c + 9)) /\
           read Q2 s = word_reversefields 8 (ctr_block nonce (8 * 0 + c + 10)) /\
           read Q3 s = word_reversefields 8 (ctr_block nonce (8 * 0 + c + 11)) /\
           read Q4 s = word_reversefields 8 (ctr_block nonce (8 * 0 + c + 12)) /\
           htable_mem_8 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j) /\
           (!j. j < 8 * (0 + 1)
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block aes256_cipher c nonce rk (j)) (inblock j)) /\
           ((read NF s <=> read VF s) <=> (0 = k)))
      (\s. aligned_bytes_loaded s (word pc) aes256_gcm_enc_alt_tmc /\
           read PC s = word (pc + 0xa10) /\
           read X0 s = word_add in_p (word (128 * (k + 1))) /\
           read X2 s = word_add out_p (word (128 * (k + 1))) /\
           read X3 s = tag_p /\
           read X9 s = word (16 * nb) /\
           read X4 s = word_add in_p (word (16 * nb)) /\
           read X16 s = ivec_p /\
           read X5 s = end_p /\
           read X6 s = htable_p /\
           read X10 s = mod_p /\
           read X11 s = key_p /\
           read (memory :> bytes64 mod_p) s = word 0xc200000000000000 /\
           wordlist_from_memory(key_p,15) s = MAP (word_reversefields 8) rk /\
           read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce c) /\
           read Q30 s = word_reversefields 32 (ctr_block nonce (8 * k + c + 13)) /\
           read Q31 s = word 79228162514264337593543950336 /\
           read Q19 s =
             nist_ghash (aes256_cipher (word 0) rk) tag0
                 (list_of_seq (nist_cipher_block aes256_cipher c nonce rk inblock) (8 * k)) /\
           read Q8 s = word_xor (aes_ctr_block aes256_cipher c nonce rk ((8 * k + 0))) (inblock (8 * k + 0)) /\
           read Q9 s = word_xor (aes_ctr_block aes256_cipher c nonce rk ((8 * k + 1))) (inblock (8 * k + 1)) /\
           read Q10 s = word_xor (aes_ctr_block aes256_cipher c nonce rk ((8 * k + 2))) (inblock (8 * k + 2)) /\
           read Q11 s = word_xor (aes_ctr_block aes256_cipher c nonce rk ((8 * k + 3))) (inblock (8 * k + 3)) /\
           read Q12 s = word_xor (aes_ctr_block aes256_cipher c nonce rk ((8 * k + 4))) (inblock (8 * k + 4)) /\
           read Q13 s = word_xor (aes_ctr_block aes256_cipher c nonce rk ((8 * k + 5))) (inblock (8 * k + 5)) /\
           read Q14 s = word_xor (aes_ctr_block aes256_cipher c nonce rk ((8 * k + 6))) (inblock (8 * k + 6)) /\
           read Q15 s = word_xor (aes_ctr_block aes256_cipher c nonce rk ((8 * k + 7))) (inblock (8 * k + 7)) /\
           read Q0 s = word_reversefields 8 (ctr_block nonce (8 * k + c + 8)) /\
           read Q1 s = word_reversefields 8 (ctr_block nonce (8 * k + c + 9)) /\
           read Q2 s = word_reversefields 8 (ctr_block nonce (8 * k + c + 10)) /\
           read Q3 s = word_reversefields 8 (ctr_block nonce (8 * k + c + 11)) /\
           read Q4 s = word_reversefields 8 (ctr_block nonce (8 * k + c + 12)) /\
           htable_mem_8 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j) /\
           (!j. j < 8 * (k + 1)
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block aes256_cipher c nonce rk (j)) (inblock j)))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * nb)])`,
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; ALLPAIRS; ALL] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_WHILE_PUP_TAC `k:num` `pc + 0x4c0` `pc + 0xa0c`
    `\i s. (read X0 s = word_add in_p (word (128 * (i + 1))) /\
            read X2 s = word_add out_p (word (128 * (i + 1))) /\
            read X3 s = tag_p /\
            read X9 s = word (16 * nb) /\
            read X4 s = word_add in_p (word (16 * nb)) /\
            read X16 s = ivec_p /\
            read X5 s = end_p /\
            read X6 s = htable_p /\
            read X10 s = mod_p /\
            read X11 s = key_p /\
            read (memory :> bytes64 mod_p) s = word 0xc200000000000000 /\
            wordlist_from_memory(key_p,15) s = MAP (word_reversefields 8) rk /\
            read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
            read (memory :> bytes128 ivec_p) s =
              word_reversefields 8 (ctr_block nonce c) /\
            read Q30 s = word_reversefields 32 (ctr_block nonce (8 * i + c + 13)) /\
            read Q31 s = word 79228162514264337593543950336 /\
            read Q19 s =
              nist_ghash (aes256_cipher (word 0) rk) tag0
                  (list_of_seq (nist_cipher_block aes256_cipher c nonce rk inblock) (8 * i)) /\
            read Q8 s = word_xor (aes_ctr_block aes256_cipher c nonce rk ((8 * i + 0))) (inblock (8 * i + 0)) /\
            read Q9 s = word_xor (aes_ctr_block aes256_cipher c nonce rk ((8 * i + 1))) (inblock (8 * i + 1)) /\
            read Q10 s = word_xor (aes_ctr_block aes256_cipher c nonce rk ((8 * i + 2))) (inblock (8 * i + 2)) /\
            read Q11 s = word_xor (aes_ctr_block aes256_cipher c nonce rk ((8 * i + 3))) (inblock (8 * i + 3)) /\
            read Q12 s = word_xor (aes_ctr_block aes256_cipher c nonce rk ((8 * i + 4))) (inblock (8 * i + 4)) /\
            read Q13 s = word_xor (aes_ctr_block aes256_cipher c nonce rk ((8 * i + 5))) (inblock (8 * i + 5)) /\
            read Q14 s = word_xor (aes_ctr_block aes256_cipher c nonce rk ((8 * i + 6))) (inblock (8 * i + 6)) /\
            read Q15 s = word_xor (aes_ctr_block aes256_cipher c nonce rk ((8 * i + 7))) (inblock (8 * i + 7)) /\
            read Q0 s = word_reversefields 8 (ctr_block nonce (8 * i + c + 8)) /\
            read Q1 s = word_reversefields 8 (ctr_block nonce (8 * i + c + 9)) /\
            read Q2 s = word_reversefields 8 (ctr_block nonce (8 * i + c + 10)) /\
            read Q3 s = word_reversefields 8 (ctr_block nonce (8 * i + c + 11)) /\
            read Q4 s = word_reversefields 8 (ctr_block nonce (8 * i + c + 12)) /\
            htable_mem_8 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s /\
            (!j. j < nb
                 ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                     inblock j) /\
            (!j. j < 8 * (i + 1)
                 ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                     word_xor (aes_ctr_block aes256_cipher c nonce rk (j)) (inblock j))) /\
           ((read NF s <=> read VF s) <=> (i = k))` THEN
  REWRITE_TAC[htable_mem_8; htable_mem_4; KEY15_SPLIT] THEN
  REPEAT CONJ_TAC THENL
   [(* Subgoal 1: 0 < k *)
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;

    (* Subgoal 2: init -- reflexive 0-step (precondition = p 0 at pc+0x4c0) *)
    ENSURES_INIT_TAC "s0" THEN
    RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_8; htable_mem_4]) THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[];

    (* Subgoal 3: body -- 339-instr fused GHASH+AES pipeline.                     *)
    (* The body steps through to ENSURES_FINAL_STATE_TAC with all eight           *)
    (* ciphertext register facts (read Q8..Q15 s339) intact.  LDP_STEP4_TAC       *)
    (* (see the helper above) supplies the word_add-flatten + offset-arithmetic   *)
    (* reduction the ldp 2nd-element read addresses need to match the             *)
    (* input-block reads, else DISCARD_OLDSTATE drops them.  Step count is        *)
    (* (1--339): the b.lt@0xa0c (step 340) is the PUP back-edge (subgoals 4&5),   *)
    (* NOT the body.  The 4 plaintext reloads are ldp q,q,[x0],#32 at steps       *)
    (* 263/295/303/304; the first resolves natively, the 3 incremented ones use   *)
    (* LDP_STEP4_TAC.                                                             *)
    (*                                                                            *)
    (* Register counter pins: setup does 13 `add v30` increments, so at loop      *)
    (* entry v0..v4 = ctr_block nonce (8i+c+8..8i+c+12) and Q30 = ctr(8i+c+13); the*)
    (* invariant pins Q0..Q4/Q30 to those block-index values, and the             *)
    (* out-forall stays in block-index aes_ctr_block form (the proven x4 shape).  *)
    (*                                                                            *)
    (* Two obligations:                                                           *)
    (* (1) INCOMING OUT-FORALL preservation across the 4 ciphertext stores.       *)
    (*     `stp q,q,[x2],#32` at steps 330/334/337/338 (pc 0x9e4/9cc/9d8/9dc)     *)
    (*     write NEW blocks 8i+8..8i+15.  The invariant-at-i out-forall           *)
    (*     (`!j.j<8*(i+1)==> read(out+16j) s =                                    *)
    (*     word_xor(aes_ctr_block aes256_cipher c nonce rk (j))(inblock j)`) is   *)
    (*     ADVANCED s->s' at every non-store step (like the input-forall, which   *)
    (*     survives all 339 steps to s339) but DROPPED at the first store: the    *)
    (*     stepper cannot advance a quantified read over the out_p buffer it      *)
    (*     writes (per-j disjointness 16j != 128(i+1)+off for j<8i+8 is           *)
    (*     nonlinear, not auto-dischargeable under the !j binder), so             *)
    (*     DISCARD_OLDSTATE_TAC erases it.  FIX (LDP_STEP4_TAC analogue for the   *)
    (*     stp stores): at each store use ARM_VERBOSE_STEP_TAC, then ADVANCE the  *)
    (*     out-forall's read s_{n-1}->s_n under the !j binder via read-over-write *)
    (*     orthogonality (COMPONENT_READ_OVER_WRITE_CONV / the bytes128 store     *)
    (*     component vs out_p+16j, supplying 16j<128(i+1) from j<8*(i+1) minus    *)
    (*     the 8 new indices), re-ASSUME the advanced out-forall, THEN            *)
    (*     DISCARD_OLDSTATE.  The 8 NEW-block store facts survive concretely at   *)
    (*     s339 so new blocks close via the case-split; only OLD blocks need it.  *)
    (* (2) Q19 GHASH fold: byteswap128 BITBLAST wrapper, MAP_EVERY                *)
    (*     ABBREV_TAC sofar/cipherblock_0..7/h0..h7, TRANS_TAC EQ_TRANS to        *)
    (*     polyval_reduce_prop3(<8-term pmul chain>), PMUL_KARATSUBA_JOIN_ALT +   *)
    (*     karatsuba_mid + POLYVAL_REDUCE_G2 + BITBLAST, then                     *)
    (*     GHASH_POLYVAL_ACC_BATCHED [cipherblock_1..7] + NIST_GHASH_IS_POLYVAL + *)
    (*     list_of_seq (8*i+8 = SUC^8 (8*i)) + GHASH_ACC_APPEND.                  *)
    (* Cheap conjuncts (X-regs, keys/htable/tag/ivec mem, Q30/Q31, Q0..Q4         *)
    (* counter, Q8..Q15 ciphertext, NEW out-blocks, flag, PC) close via the       *)
    (* cheap-close case-split bound 8*((i+1)+1), eor3 WORD_BITWISE_RULE           *)
    (* AC-normalize, CTR_BLOCK_RECONSTRUCT_REV8/REV32 + WORD_SUBWORD_* +          *)
    (* XOR_AES256_CIPHER_RECONSTRUCT + aes_ctr_block/ADD_CLAUSES + FIRST_ASSUM    *)
    (* MATCH + WORD_RULE/ARITH.                                                   *)
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
    RULE_ASSUM_TAC(REWRITE_RULE[REWRITE_CONV[fst AES256_GCM_ENC_ALT_EXEC]
      `LENGTH aes256_gcm_enc_alt_tmc`]) THEN
    MAP_EVERY NSTEP_G (1--294) THEN
    LDP_STEP4_TAC 295 THEN
    MAP_EVERY NSTEP_G (296--302) THEN
    LDP_STEP4_TAC 303 THEN
    LDP_STEP4_TAC 304 THEN
    MAP_EVERY NSTEP_G (305--339) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    (* --- Cheap-conjunct close: validates the +2 counter fix.                  *)
    (* The case-split bound is 8*((i+1)+1) (invariant out-forall at i is         *)
    (* j<8*(i+1), so at i+1 it is j<8*(i+2)); the eor3 3-way store XOR is        *)
    (* AC-normalized to the XOR_AES256_CIPHER_RECONSTRUCT shape; then            *)
    (* AES256_CIPHER_KEYLIST collapses the residual explicit key list            *)
    (* `[EL 0 rk;..;EL 14 rk]` back to `rk` (needed because                      *)
    (* XOR_AES256_CIPHER_RECONSTRUCT + MAP leaves the list, not `rk`).           *)
    (* split the RAW post-FINAL_STATE conjunction                              *)
    (* FIRST (before the cheap-close), so the Q19 GHASH-fold conjunct can be    *)
    (* folded while its ext/LO structure is intact.  Testing CONFIRMED the      *)
    (* cheap-close's WORD_SIMPLE_SUBWORD_CONV DESTROYS Q19's foldability (the    *)
    (* GSYM ghash_reduce_raw fold-back fails post-cheap-close), so Q19 MUST be   *)
    (* peeled off before it runs.  `REPEAT CONJ_TAC` yields 20 atomic goals     *)
    (* (18 cheap + 1 Q19 + 1 flag); the per-goal dispatcher routes each:        *)
    (*   - Q19 (is_eq, RHS headed by byteswap128): Q19_FOLD_TAC (genuine down   *)
    (*     to the final lane-match, handled inside Q19_FOLD_TAC);               *)
    (*   - everything else: the cheap-close rewrites (which also handle the     *)
    (*     out-forall case-split), then a nested split + flag-close for the     *)
    (*     out-forall.                                                          *)
    REPEAT CONJ_TAC THEN
    (fun (asl,w as gl) ->
      if is_eq w &&
         (try fst(dest_const(fst(strip_comb(rhs w)))) = "nist_ghash"
          with _ -> false)
      then Q19_FOLD_TAC gl
      else if is_eq w &&
         (try fst(dest_const(fst(strip_comb(rhs w)))) = "word_reversefields"
          with _ -> false)
      then
       (* counter-register conjuncts (Q0..Q4 rev8 / Q30 rev32): reconstruct
          the lane word_joins to ctr_block form, then discharge the symbolic-c
          counter-index equality (arith-equal, not syntactically identical) by
          ARITH - the concrete proof combined the offsets via NUM_REDUCE. *)
       (REWRITE_TAC[WORD_SUBWORD_REVERSEFIELDS_32; WORD_SUBWORD_CTR_BLOCK_32] THEN
        REWRITE_TAC[GSYM WORD_ADD; WORD_ADD_0] THEN
        REWRITE_TAC[CTR_BLOCK_RECONSTRUCT_REV8; CTR_BLOCK_RECONSTRUCT_REV32] THEN
        AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC) gl
      else
       (REWRITE_TAC[MAIN_LOOP_OUT_DISJSPLIT] THEN
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
        (* collapse the explicit key list to rk BEFORE folding, then
           refold both sides to aes_ctr_block form.  A plain GSYM cipher_block
           fold is AMBIGUOUS under the c parameter (inblock/i higher-order
           match spuriously picks c := 8*i+c), so instead close the ciphertext
           identity directly at the aes_ctr_block level: peel the word_xor +
           aes_ctr_block by AP_THM/AP_TERM and discharge the arith-equal counter
           index by ARITH.  Pointer conjuncts fall to WORD_RULE. *)
        REWRITE_TAC[AES256_CIPHER_KEYLIST] THEN
        REWRITE_TAC[aes_ctr_block; ADD_CLAUSES] THEN
        REPEAT CONJ_TAC THEN
        TRY(CONV_TAC WORD_RULE) THEN
        REPEAT(AP_THM_TAC ORELSE AP_TERM_TAC) THEN
        TRY ARITH_TAC) gl) THEN
    (* --- Remaining after the split-first dispatcher: the ~18 cheap              *)
    (* conjuncts and all 16 ciphertext out-blocks close.  The remaining           *)
    (* obligations:                                                               *)
    (* (A) Q19 GHASH fold via NSTEP_G + the split-first dispatcher +              *)
    (*     Q19_FOLD_TAC (above): folds the raw body-end reduce to nist_ghash      *)
    (*     over the 8 new cipherblocks.                                           *)
    (* (B) OLD out-forall (!j. j<8*(i+1) ==> read(out+16j) s = ...):              *)
    (*     advancing the incoming out-forall over the 4 ciphertext stores is      *)
    (*     delicate.  ASSUMPTION_STATE_UPDATE_TAC advances an assumption over     *)
    (*     a store via STATE_UPDATE_RULE ->                                       *)
    (*     COMPONENTS_READ_OVER_WRITE_ORTHOGONAL_CONV, which descends under the   *)
    (*     !j binder and collects the antecedent j<8*(i+1) into its context       *)
    (*     (components.ml:3203), then needs ORTHOGONAL_COMPONENTS_RULE to         *)
    (*     discharge orthogonality of bytes128(out_p+16*j) against the store at   *)
    (*     bytes128(out_p+128*(i+1)), requiring the nonlinear bound               *)
    (*     16*(j+1)<=128*(i+1) from j<8*(i+1).  The driver does not derive that   *)
    (*     for a symbolic product offset, so the OLD blocks are carried across    *)
    (*     the stores while the 8 NEW blocks close from concrete store facts.     *)
    (* (C) FLAG/PC-branch fact q(i+1) = ((NF<=>VF)<=>(i+1=k)): MAIN_LOOP's two    *)
    (*     end_p antecedents (end_p = word_add in_p (word (128*(k+1))) and the    *)
    (*     no-wrap bound val in_p + 128*(k+1) < 2 EXP 63) pin the iteration       *)
    (*     count k; word_sub cancels in_p, leaving a pure k-bounded word fact.    *)
    (* The residual is A /\ C /\ B (Q19 fold / flag / out-forall+frame), split    *)
    (* by REPEAT CONJ_TAC.  The cheap-close's WORD_ADD normalisation splits the   *)
    (* flag offsets to word_add (word (128*i)) (word 256) (= X0 = in_p +          *)
    (* 128*(i+2)) and word_add (word (128*k)) (word 128) (= end_p, already        *)
    (* substituted by ASM_REWRITE), so the flag close is not syntactic; instead   *)
    (* it rewrites BRIDGE_GE (the NF!=VF biconditional = signed GE ival end_p <=  *)
    (* ival X0), linearises both additive ivals with IV_ADD under the no-wrap     *)
    (* bound, and finishes by INT/ARITH using i < k.                              *)
    REPEAT CONJ_TAC THEN
    (* Guard: fire the flag close ONLY on the flag-shaped goal - the sole
       residual whose conclusion is `<flag biconditional> <=> (i + 1 = k)`
       (RHS = `i + 1 = k`).  This keeps BRIDGE_GE off the giant Q19 term       *)
    (* (resid A).  CRITICAL: the flag arithmetic uses targeted UNDISCH_TAC of   *)
    (* the two needed hyps (`i < k`, the no-wrap bound) + bare ARITH_TAC - NOT  *)
    (* ASM_ARITH_TAC, which would scan every hyp (incl. the giant ciphertext/   *)
    (* Q19 facts) and wedge the checker.                                        *)
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
        (* BLOCKER B RESOLVED: the sole residual reaching this
           branch is the MAYCHANGE FRAME-subsumption goal `(<accumulated>) s0
           s339` (NOT the out-forall - that closes in the first dispatcher's
           cheap-close, since it SURVIVES to s339).  The body
           physically clobbers the FULL Q8..Q15 (the in-flight ciphertext
           blocks), whose low 64 bits the ABI frame forbids (v8-v15 are
           callee-saved).  The MAIN_LOOP conclusion frame was therefore
           widened with `MAYCHANGE [Q8;..;Q15]`, as in the 4-way kernels; the
           low-half writes are restored by the d8-d15 epilogue at the
           subroutine wrapper.  With the widened frame,
           MONOTONE_MAYCHANGE_TAC discharges the subsumption (the 8 ciphertext
           stores bytes128(out_p+128*(i+1)+16m) <= bytes(out_p,16*nb) follow
           from the `8*(k+1)<=nb` antecedent via CONTAINED_TAC).  *)
        else MONOTONE_MAYCHANGE_TAC) gl);

    (* Subgoal 4: back-edge taken (0 < i < k => b.lt branches back) *)
    REPEAT STRIP_TAC THEN
    ARM_SIM_TAC AES256_GCM_ENC_ALT_EXEC [1] THEN
    ASM_REWRITE_TAC[];

    (* Subgoal 5: exit fall-through (i = k => GE, b.lt not taken) *)
    REPEAT STRIP_TAC THEN
    ARM_SIM_TAC AES256_GCM_ENC_ALT_EXEC [1] THEN
    ASM_REWRITE_TAC[]]);;

(* the SETUP Q30 (rev32 next-group counter) reconstruction.  A               *)
(* monolithic `REWRITE_TAC[ctr_block] THEN WORD_BLAST` on the whole Q30      *)
(* word_join HANGS (ignores SIGINT) because it bit-blasts the                *)
(* symbolic 96-bit nonce whole.  Lane-decomposition is instant: each 32-bit  *)
(* lane shares the symbolic nonce structurally so WORD_BLAST matches it      *)
(* without blasting. Combine with CTR_BLOCK_RECONSTRUCT_REV32 to             *)
(* assemble the full word_reversefields 32 (ctr_block nonce (c+13)).         *)
let SETUP_Q30_LANES = prove
 (`(word_add (word_add
      (word_reversefields 8
        (word_subword (word_reversefields 8 (ctr_block nonce c)) (96,32):int32))
      (word 12)) (word 1):int32 = word (c + 13)) /\
   (word_add (word_reversefields 8
      (word_subword (word_reversefields 8 (ctr_block nonce c)) (64,32):int32)) (word 0):int32
    = word_subword nonce (0,32)) /\
   (word_add (word_reversefields 8
      (word_subword (word_reversefields 8 (ctr_block nonce c)) (32,32):int32)) (word 0):int32
    = word_subword nonce (32,32)) /\
   (word_add (word_reversefields 8
      (word_subword (word_reversefields 8 (ctr_block nonce c)) (0,32):int32)) (word 0):int32
    = word_subword nonce (64,32))`,
  SUBGOAL_THEN
    `word_reversefields 8
       (word_subword (word_reversefields 8 (ctr_block nonce c)) (96,32):int32) =
     word c:int32`
    ASSUME_TAC THENL
   [REWRITE_TAC[ctr_block] THEN
    SPEC_TAC(`word c:int32`,`wc:int32`) THEN GEN_TAC THEN CONV_TAC WORD_BLAST;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [CONV_TAC WORD_RULE;
    REWRITE_TAC[ctr_block] THEN
    SPEC_TAC(`word c:int32`,`wc:int32`) THEN GEN_TAC THEN CONV_TAC WORD_BLAST]);;

(* ------------------------------------------------------------------------- *)
(* SETUP FINAL_STATE reconstruction dispatcher.                              *)
(*                                                                           *)
(* After the SETUP drive reaches pc+0x4c0 and ENSURES_FINAL_STATE_TAC +      *)
(* ASM_REWRITE + REWRITE_TAC[htable_mem_8; htable_mem_4] + REPEAT CONJ_TAC splits the      *)
(* postcondition, the residual goals are dispatched by conclusion shape.     *)
(*                                                                           *)
(* CIPHER_ID_TAC: the AES-INPUT IDENTITY residual, block j (j=1..7):         *)
(*      word_xor (RF8 (aes256_cipher (RF8 <KS_j>) rk)) (inblock j) =         *)
(*      word_xor (RF8 (aes256_cipher (ctr_block nonce (c+j)) rk)) (inblock   *)
(*        j)                                                                 *)
(* where <KS_j> is SETUP's rev32-built next-group keystream counter.  Peel   *)
(* the outer word_xor(-)(inblock j) + RF8 + aes256_cipher(-)rk via AP_THM/   *)
(* AP_TERM, leaving RF8<KS_j> = ctr_block nonce (c+j), which ctr_block +     *)
(* WORD_BLAST closes DIRECTLY because on the fully-typed goal the         *)
(* symbolic 96-bit nonce appears identically on both sides, so WORD_BLAST *)
(* does not blast it.                                                     *)
(* symbolic-c counter-lane reduction lemmas, shared by CIPHER_CLOSE and
   CTR_CLOSE.  The counter field of the byte-reversed ctr_block double-reverses to
   the raw counter; the nonce lanes byte-reverse to the nonce sub-lanes.  Proved by
   abstracting `word c` to a fresh word (WORD_BLAST cannot blast `word c` for a
   symbolic num c). *)
let CTR_LANE_LOW = prove
 (`word_reversefields 8
     (word_subword (word_reversefields 8 (ctr_block nonce c)) (96,32):int32) =
   word c`,
  REWRITE_TAC[ctr_block] THEN
  SPEC_TAC(`word c:int32`,`wc:int32`) THEN GEN_TAC THEN CONV_TAC WORD_BLAST);;

let CTR_NONCE_LANES = prove
 (`(word_subword (word_reversefields 8 (ctr_block nonce c)) (64,32):int32 =
    word_reversefields 8 (word_subword nonce (0,32))) /\
   (word_subword (word_reversefields 8 (ctr_block nonce c)) (32,32):int32 =
    word_reversefields 8 (word_subword nonce (32,32))) /\
   (word_subword (word_reversefields 8 (ctr_block nonce c)) (0,32):int32 =
    word_reversefields 8 (word_subword nonce (64,32)))`,
  REWRITE_TAC[ctr_block] THEN
  SPEC_TAC(`word c:int32`,`wc:int32`) THEN GEN_TAC THEN CONV_TAC WORD_BLAST);;

let CIPHER_ID_TAC =
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[ctr_block] THEN CONV_TAC WORD_BLAST;;

(* CIPHER_CLOSE: the MAIN_LOOP body ciphertext chain (in                     *)
(* AES256_GCM_ENC_ALT_MAIN_LOOP) specialized to SETUP.  Reduces the raw      *)
(* eor3/aese form                                                            *)
(*      word_xor (word_xor (inblock j) (aese..aese..rk13)) rk14              *)
(* to the aes256_cipher form.  For block 0 (counter ctr_block nonce c, no    *)
(* rev32 rebuild) it closes outright; for the out-forall's j=1..7 it leaves  *)
(* the AES-INPUT IDENTITY residual that CIPHER_ID_TAC then peels.            *)
let CIPHER_CLOSE =
  ONCE_REWRITE_TAC[WORD_BITWISE_RULE
    `word_xor (word_xor (inb:int128) ch) rk14 =
     word_xor ch (word_xor rk14 inb)`] THEN
  REWRITE_TAC[XOR_AES256_CIPHER_RECONSTRUCT] THEN
  ASM_REWRITE_TAC[MAP; WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
  (* symbolic-c: the AES input is the raw rev8 counter-lane assembly for
     block K.  Reconstruct it to ctr_block nonce (c+K) (CTR_LANE_LOW + CTR_NONCE_LANES
     + GSYM WORD_ADD + CTR_BLOCK_RECONSTRUCT, then cancel the outer double reverse),
     collapse the keys, refold to aes_ctr_block, then peel word_xor + aes_ctr_block
     and discharge the arith-equal counter index by ARITH.  (A plain GSYM cipher_block
     fold is higher-order ambiguous under c.) *)
  REWRITE_TAC[CTR_LANE_LOW; CTR_NONCE_LANES] THEN
  REWRITE_TAC[GSYM WORD_ADD; WORD_ADD_0] THEN
  REWRITE_TAC[CTR_BLOCK_RECONSTRUCT_REV8; CTR_BLOCK_RECONSTRUCT_REV32] THEN
  REWRITE_TAC[WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
  REWRITE_TAC[AES256_CIPHER_KEYLIST] THEN
  REWRITE_TAC[aes_ctr_block; ADD_CLAUSES] THEN
  (* normalise 8*0+j indices so the block-0 special case (bare counter c
     and inblock 0 on the LHS vs c+8*0+0 / inblock (8*0+0) on the RHS) matches. *)
  REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES] THEN
  TRY(REFL_TAC) THEN
  TRY(REPEAT(AP_THM_TAC ORELSE AP_TERM_TAC) THEN ARITH_TAC);;

(* CTR_CLOSE: Q0..Q4 (rev8) + Q30 (rev32) fresh-counter reconstruction.
   symbolic-c: reduce each lane to the CTR_BLOCK_RECONSTRUCT_REV8/REV32
   pattern (SETUP_Q30_LANES for Q30; CTR_LANE_LOW + double-RF8 cancel + CTR_NONCE_LANES
   for Q0..Q4), combine the counter add (GSYM WORD_ADD), fold to ctr_block, then peel
   + ARITH the arith-equal counter index.  NO full-term WORD_BLAST (it is too slow /
   hangs on the 128-bit symbolic-c term). *)
let CTR_CLOSE =
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[SETUP_Q30_LANES; CTR_LANE_LOW] THEN
  REWRITE_TAC[WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
  REWRITE_TAC[CTR_NONCE_LANES] THEN
  REWRITE_TAC[GSYM WORD_ADD; WORD_ADD_0] THEN
  REWRITE_TAC[CTR_BLOCK_RECONSTRUCT_REV8; CTR_BLOCK_RECONSTRUCT_REV32] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;;

(* FLAG_CLOSE: the prepretail-check flag conjunct ((NF<=>VF)<=>(0=k)) at     *)
(* i=0. Rewrite the raw round-down X5 pointer to end_p (X5_END_PTR after the *)
(* DIV bridge), then discharge the signed compare with SETUP_GE_FALSE_2      *)
(* (k>=1).                                                                   *)
let FLAG_CLOSE_GEN =
  REWRITE_TAC[BRIDGE_GE] THEN
  SUBGOAL_THEN
    `word_add (word_and (word_sub (word ((128 * nb) DIV 8):int64) (word 1))
                        (word 18446744073709551488)) in_p =
     word_add in_p (word (128 * (k + 1)))`
    SUBST1_TAC THENL
   [MATCH_MP_TAC SETUP_X5_END_GEN THEN
    ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[MATCH_MP SETUP_GE_FALSE_2
      (CONJ (ASSUME `~(k = 0)`)
            (ASSUME `val(in_p:int64) + 128 * (k + 1) < 2 EXP 63`))]];;

(* SETUP_RECON_TAC_GEN = SETUP_RECON_TAC with (1) is_neg -> FLAG_CLOSE_GEN   *)
(* and (2) the word_add X5 branch's 3rd alternative ->                       *)
(* ASM_SIMP_TAC[SETUP_X5_END_GEN].                                           *)
let SETUP_RECON_TAC_GEN : tactic =
  fun (asl,w as gl) ->
    if is_neg w then FLAG_CLOSE_GEN gl
    else if is_forall w then
      (REWRITE_TAC[ARITH_RULE `j < 8 * (0 + 1) <=>
                     j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/
                     j = 4 \/ j = 5 \/ j = 6 \/ j = 7`] THEN
       REWRITE_TAC[TAUT `(p \/ q ==> r) <=> (p ==> r) /\ (q ==> r)`] THEN
       REWRITE_TAC[FORALL_AND_THM; FORALL_UNWIND_THM2] THEN
       CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN ASM_REWRITE_TAC[] THEN
       REWRITE_TAC[WORD_ADD_0] THEN
       REPEAT CONJ_TAC THEN CIPHER_CLOSE THEN TRY CIPHER_ID_TAC THEN
       TRY CIPHER_CLOSE) gl
    else if is_eq w then
      let l,r = dest_eq w in
      let rhd = try fst(dest_const(fst(strip_comb r))) with _ -> "?" in
      let lhd = try fst(dest_const(fst(strip_comb l))) with _ -> "?" in
      if rhd = "nist_ghash" then
        (CONV_TAC NUM_REDUCE_CONV THEN
         REWRITE_TAC[list_of_seq; NIST_GHASH_NIL] THEN CONV_TAC WORD_BLAST) gl
      else if lhd = "word_xor" && rhd = "word_xor" then
        (CIPHER_CLOSE THEN TRY CIPHER_ID_TAC THEN TRY CIPHER_CLOSE) gl
      else if lhd = "word_join" && rhd = "word_reversefields" then
        CTR_CLOSE gl
      else if lhd = "word_add" then
        FIRST
          [CONV_TAC WORD_RULE;
           (AP_TERM_TAC THEN REWRITE_TAC[word_ushr; VAL_WORD; DIMINDEX_64] THEN
            AP_TERM_TAC THEN ASM_SIMP_TAC[MOD_LT] THEN ARITH_TAC);
           (ASM_SIMP_TAC[SETUP_X5_END_GEN])] gl
      else (* read = ... : surviving read-only reads (keys/htable/ivec/tag/stack) *)
        (ASM_REWRITE_TAC[ARITH_RULE `(128 * nb) DIV 8 = 16 * nb`] THEN
         CONV_TAC NUM_REDUCE_CONV) gl
    else ASM_REWRITE_TAC[] gl;;

(* ========================================================================= *)
(* SETUP (pipeline fill).  Core entry pc+0x38 (just after the                *)
(* prologue's stack adjust + callee-save spills + mod-const store +          *)
(* X9/X16/X11/X10 remaps) through the pipeline-fill store to pc+0x4c0 (the   *)
(* main-loop top).                                                           *)
(*                                                                           *)
(* This region: 0x38-0xb4 builds the 8 CTR keystream inputs v0..v7 (rev32    *)
(* of the counter) + loads rk0/rk1; the tag is loaded into Q19 at 0xb8       *)
(* (ld1 v19; ext; rev64 => PLAIN tag0); 0xc8-0x440 runs the 14 AES rounds    *)
(* on v0..v7; 0x444 sets X4 = in_p + byte_len (tail end-ptr) and 0x44c       *)
(* does the b.ge tail check (NOT taken when k>=1); 0x450-0x4b8 loads the 8   *)
(* plaintext blocks (ldp q8..q15,[x0],#32 x4), eor3s them with the AES       *)
(* keystream + rk14 to ciphertext, rev32s the next-group counters into       *)
(* v0..v7, and stores the 8 ciphertext blocks (stp q8..q15,[x2],#32 x4);     *)
(* 0x4bc does the b.ge prepretail check (NOT taken when k>=1) and falls      *)
(* through to 0x4c0.                                                         *)
(*                                                                           *)
(* Establishes MAIN_LOOP's precondition at i=0.  Because the loop body reads *)
(* none of X4/X16 (only X0,X2,X5,X6,X10,X11), SETUP must produce X4 =        *)
(* in_p+16*nb (the scratch end-ptr, block-aligned byte_len = 16*nb) and X16  *)
(* = ivec_p (the saved ivec ptr for its `str q30,[x16]` writeback); these    *)
(* are the two conjuncts MAIN_LOOP's precondition requires.                  *)
(*                                                                           *)
(* mod_p is the on-stack modulo constant at stackpointer+0x40 (add x10,      *)
(* sp,#0x40 @0x34; the 0xc2..0 const was stored there @0x30).  We state the  *)
(* core with mod_p = word_add stackpointer (word 0x40); the subroutine       *)
(* wrapper ties stackpointer to the caller SP - 0x50.                        *)
(*                                                                           *)
(* The body is a 282-step symbolic execution plus counter/ciphertext/AES     *)
(* reconstruction, following the MAIN_LOOP body close                        *)
(* recipe.                                                                   *)
(*                                                                           *)
(* DE-RISKING (body proof recipe):                                           *)
(*     - INIT + a SETUP-specific input SUBGOAL for blocks 0..7 at            *)
(*       word_add in_p (word (16*j)) (NOT the loop body's 128*(i+1)+off)     *)
(*         proves                                                            *)
(*       by `REPEAT CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN              *)
(*         ASM_ARITH_TAC`.                                                   *)
(*     - `MAP_EVERY NSTEP (1--252)` steps CLEAN (counter build + 14-round    *)
(*       AES                                                                 *)
(*       +                                                                   *)
(*       tag load); reuse the file's NSTEP/NORMOFF/LDP_STEP4 machinery       *)
(*         verbatim.                                                         *)
(*       ldp[x0]#32 at steps 255/256/264/265 (256/264/265 need               *)
(*         LDP_STEP4-style);                                                 *)
(*       stp[x2]#32 at 270/271/278/280; apply the LENGTH->4604 rewrite.      *)
(*     - THE TWO BRANCH DISCHARGES (the real work): step 254 = b.ge@0x44c    *)
(*       (tail                                                               *)
(*       check) and step 282 = b.ge@0x4bc (prepretail check).  Each emits a  *)
(*       conditional PC `if in_p >=_s X5 then <skip> else <fall through>`    *)
(*         with                                                              *)
(*       X5 = in_p + ((16*nb-1) & ~127).  Discharge `in_p < end_p` via the   *)
(*       file's BRIDGE_GE + IV_ADD signed-ptr lemmas (as the MAIN_LOOP flag  *)
(*       close does).  KEY IDENTITY (why the premise `8*(k+2)=nb`): for      *)
(*         nb=8m,                                                            *)
(*       (16*nb-1)&~127 = 128*(m-1), so main-loop-end = in_p+128*(m-1) and   *)
(*         the                                                               *)
(*       LAST 8-group is drained by prepretail -> k+1 = m-1 -> k = nb DIV 8  *)
(*         -                                                                 *)
(*         2.                                                                *)
(*       (The `8*(k+2)=nb` premise is the hypothesis for this; VERIFY        *)
(*         it                                                                *)
(*       against the real branch + reconcile with the tail and the           *)
(*         assembly.)                                                        *)
(*     - FINAL_STATE reconstruction mirrors the MAIN_LOOP body cheap-close   *)
(*       (XOR_AES256_CIPHER_RECONSTRUCT + aes_ctr_block/ADD_CLAUSES +        *)
(*       AES256_CIPHER_KEYLIST for Q8..Q15; CTR_BLOCK_RECONSTRUCT_* for      *)
(*         Q0..Q4;                                                           *)
(*       plain Q19 = nist_ghash..(8*0) = tag0, proved trivially).            *)
(* ========================================================================= *)

let AES256_GCM_ENC_ALT_SETUP_GEN = prove
 (`!in_p out_p tag_p ivec_p key_p htable_p stackpointer bit_len end_p
     tag0 nonce c rk inblock nb k pc.
    ~(k = 0) /\
    8 * (k + 1) <= nb /\
    bit_len = 128 * nb /\
    8 * (k + 1) < nb /\ nb <= 8 * (k + 2) /\
    end_p = word_add in_p (word (128 * (k + 1))) /\
    val in_p + 128 * (k + 1) < 2 EXP 63 /\
    128 * nb < 2 EXP 64 /\
    nonoverlapping (out_p, 16 * nb)
                   (word pc, LENGTH aes256_gcm_enc_alt_tmc) /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * nb)]
      [(in_p, 16 * nb); (key_p, 240); (htable_p, 192);
       (tag_p, 16); (ivec_p, 16); (word_add stackpointer (word 0x40), 8)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) aes256_gcm_enc_alt_tmc /\
           read PC s = word (pc + 0x38) /\
           read X0 s = in_p /\
           read X1 s = word bit_len /\
           read X2 s = out_p /\
           read X3 s = tag_p /\
           read X16 s = ivec_p /\
           read X6 s = htable_p /\
           read X11 s = key_p /\
           read X9 s = word (bit_len DIV 8) /\
           read X10 s = word_add stackpointer (word 0x40) /\
           read (memory :> bytes64 (word_add stackpointer (word 0x40))) s =
             word 0xc200000000000000 /\
           wordlist_from_memory(key_p,15) s = MAP (word_reversefields 8) rk /\
           read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce c) /\
           htable_mem_8 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j))
      (\s. aligned_bytes_loaded s (word pc) aes256_gcm_enc_alt_tmc /\
           read PC s = word (pc + 0x4c0) /\
           read X0 s = word_add in_p (word (128 * (0 + 1))) /\
           read X2 s = word_add out_p (word (128 * (0 + 1))) /\
           read X3 s = tag_p /\
           read X9 s = word (16 * nb) /\
           read X4 s = word_add in_p (word (16 * nb)) /\
           read X16 s = ivec_p /\
           read X5 s = end_p /\
           read X6 s = htable_p /\
           read X10 s = word_add stackpointer (word 0x40) /\
           read X11 s = key_p /\
           read (memory :> bytes64 (word_add stackpointer (word 0x40))) s =
             word 0xc200000000000000 /\
           wordlist_from_memory(key_p,15) s = MAP (word_reversefields 8) rk /\
           read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce c) /\
           read Q30 s = word_reversefields 32 (ctr_block nonce (8 * 0 + c + 13)) /\
           read Q31 s = word 79228162514264337593543950336 /\
           read Q19 s =
             nist_ghash (aes256_cipher (word 0) rk) tag0
                 (list_of_seq (nist_cipher_block aes256_cipher c nonce rk inblock) (8 * 0)) /\
           read Q8 s = word_xor (aes_ctr_block aes256_cipher c nonce rk ((8 * 0 + 0))) (inblock (8 * 0 + 0)) /\
           read Q9 s = word_xor (aes_ctr_block aes256_cipher c nonce rk ((8 * 0 + 1))) (inblock (8 * 0 + 1)) /\
           read Q10 s = word_xor (aes_ctr_block aes256_cipher c nonce rk ((8 * 0 + 2))) (inblock (8 * 0 + 2)) /\
           read Q11 s = word_xor (aes_ctr_block aes256_cipher c nonce rk ((8 * 0 + 3))) (inblock (8 * 0 + 3)) /\
           read Q12 s = word_xor (aes_ctr_block aes256_cipher c nonce rk ((8 * 0 + 4))) (inblock (8 * 0 + 4)) /\
           read Q13 s = word_xor (aes_ctr_block aes256_cipher c nonce rk ((8 * 0 + 5))) (inblock (8 * 0 + 5)) /\
           read Q14 s = word_xor (aes_ctr_block aes256_cipher c nonce rk ((8 * 0 + 6))) (inblock (8 * 0 + 6)) /\
           read Q15 s = word_xor (aes_ctr_block aes256_cipher c nonce rk ((8 * 0 + 7))) (inblock (8 * 0 + 7)) /\
           read Q0 s = word_reversefields 8 (ctr_block nonce (8 * 0 + c + 8)) /\
           read Q1 s = word_reversefields 8 (ctr_block nonce (8 * 0 + c + 9)) /\
           read Q2 s = word_reversefields 8 (ctr_block nonce (8 * 0 + c + 10)) /\
           read Q3 s = word_reversefields 8 (ctr_block nonce (8 * 0 + c + 11)) /\
           read Q4 s = word_reversefields 8 (ctr_block nonce (8 * 0 + c + 12)) /\
           htable_mem_8 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j) /\
           (!j. j < 8 * (0 + 1)
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block aes256_cipher c nonce rk (j)) (inblock j)) /\
           ((read NF s <=> read VF s) <=> (0 = k)))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * nb)])`,
  REWRITE_TAC[KEY15_SPLIT] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; ALLPAIRS; ALL;
              NONOVERLAPPING_CLAUSES] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REWRITE_CONV[fst AES256_GCM_ENC_ALT_EXEC]
      `LENGTH aes256_gcm_enc_alt_tmc`]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_8; htable_mem_4]) THEN
  SUBGOAL_THEN `~(nb = 4)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `5 <= nb` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY NSTEP (1--5) THEN NSTEP 6 THEN NSTEP 7 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[
    MATCH_MP DISPATCH4_NOT_TAKEN (CONJ (ASSUME `128 * nb < 2 EXP 64`) (ASSUME `~(nb = 4)`));
    MATCH_MP DISPATCH_SMALL_NOT_TAKEN (CONJ (ASSUME `128 * nb < 2 EXP 64`) (ASSUME `5 <= nb`));
    COND_CLAUSES]) THEN
  MAP_EVERY NSTEP (8--36) THEN
  MAP_EVERY NSTEP (37--261) THEN NSTEP 262 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP SETUP_BRANCH_COND_FALSE_GEN
    (CONJ (ASSUME `8 * (k + 1) < nb`) (CONJ (ASSUME `nb <= 8 * (k + 2)`)
          (ASSUME `val (in_p:int64) + 128 * (k + 1) < 2 EXP 63`))); COND_CLAUSES]) THEN
  LDP_SETUP_TAC 263 THEN LDP_SETUP_TAC 264 THEN MAP_EVERY NSTEP (265--271) THEN
  LDP_SETUP_TAC 272 THEN LDP_SETUP_TAC 273 THEN MAP_EVERY NSTEP (274--289) THEN
  NSTEP 290 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP SETUP_BRANCH_COND_FALSE_2_GEN
    (CONJ (ASSUME `~(k = 0)`) (CONJ (ASSUME `8 * (k + 1) < nb`)
      (CONJ (ASSUME `nb <= 8 * (k + 2)`)
          (ASSUME `val (in_p:int64) + 128 * (k + 1) < 2 EXP 63`))));
    COND_CLAUSES]) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[htable_mem_8; htable_mem_4] THEN
  REPEAT CONJ_TAC THEN SETUP_RECON_TAC_GEN);;

(* ------------------------------------------------------------------------- *)
(* SETUP_G1: the g=1 (k=0) pipeline-fill setup leg.  IDENTICAL               *)
(* drive to SETUP_GEN EXCEPT: precond pins k=0 (so groups=1, nblocks         *)
(* 9..16); at step 282 the 2nd main-loop-skip guard (b.ge@0x4bc) is TAKEN    *)
(* (not fall- through) because end_p = in_p+128*(0+1) = in_p+128 = X0, so PC *)
(* jumps to pc+0xa10 (PREPRETAIL) NOT pc+0x4c0 (main loop top).  Discharge   *)
(* via SETUP_BRANCH_COND_TRUE_2 (vs FALSE_2_GEN).  Postcond =                *)
(* PREPRETAIL_GEN's precond at 0xa10 in the k=0 (8*0) form (flag conjunct    *)
(* dropped).  0-hyp.                                                         *)
(* ------------------------------------------------------------------------- *)
let AES256_GCM_ENC_ALT_SETUP_G1 = prove
 (`!in_p out_p tag_p ivec_p key_p htable_p stackpointer bit_len end_p
     tag0 nonce c rk inblock nb k pc.
    k = 0 /\
    8 * (k + 1) <= nb /\
    bit_len = 128 * nb /\
    8 * (k + 1) < nb /\ nb <= 8 * (k + 2) /\
    end_p = word_add in_p (word (128 * (k + 1))) /\
    val in_p + 128 * (k + 1) < 2 EXP 63 /\
    128 * nb < 2 EXP 64 /\
    nonoverlapping (out_p, 16 * nb)
                   (word pc, LENGTH aes256_gcm_enc_alt_tmc) /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * nb)]
      [(in_p, 16 * nb); (key_p, 240); (htable_p, 192);
       (tag_p, 16); (ivec_p, 16); (word_add stackpointer (word 0x40), 8)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) aes256_gcm_enc_alt_tmc /\
           read PC s = word (pc + 0x38) /\
           read X0 s = in_p /\
           read X1 s = word bit_len /\
           read X2 s = out_p /\
           read X3 s = tag_p /\
           read X16 s = ivec_p /\
           read X6 s = htable_p /\
           read X11 s = key_p /\
           read X9 s = word (bit_len DIV 8) /\
           read X10 s = word_add stackpointer (word 0x40) /\
           read (memory :> bytes64 (word_add stackpointer (word 0x40))) s =
             word 0xc200000000000000 /\
           wordlist_from_memory(key_p,15) s = MAP (word_reversefields 8) rk /\
           read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce c) /\
           htable_mem_8 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j))
      (\s. aligned_bytes_loaded s (word pc) aes256_gcm_enc_alt_tmc /\
           read PC s = word (pc + 0xa10) /\
           read X0 s = word_add in_p (word (128 * (0 + 1))) /\
           read X2 s = word_add out_p (word (128 * (0 + 1))) /\
           read X3 s = tag_p /\
           read X9 s = word (16 * nb) /\
           read X4 s = word_add in_p (word (16 * nb)) /\
           read X16 s = ivec_p /\
           read X5 s = end_p /\
           read X6 s = htable_p /\
           read X10 s = word_add stackpointer (word 0x40) /\
           read X11 s = key_p /\
           read (memory :> bytes64 (word_add stackpointer (word 0x40))) s =
             word 0xc200000000000000 /\
           wordlist_from_memory(key_p,15) s = MAP (word_reversefields 8) rk /\
           read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce c) /\
           read Q30 s = word_reversefields 32 (ctr_block nonce (8 * 0 + c + 13)) /\
           read Q31 s = word 79228162514264337593543950336 /\
           read Q19 s =
             nist_ghash (aes256_cipher (word 0) rk) tag0
                 (list_of_seq (nist_cipher_block aes256_cipher c nonce rk inblock) (8 * 0)) /\
           read Q8 s = word_xor (aes_ctr_block aes256_cipher c nonce rk ((8 * 0 + 0))) (inblock (8 * 0 + 0)) /\
           read Q9 s = word_xor (aes_ctr_block aes256_cipher c nonce rk ((8 * 0 + 1))) (inblock (8 * 0 + 1)) /\
           read Q10 s = word_xor (aes_ctr_block aes256_cipher c nonce rk ((8 * 0 + 2))) (inblock (8 * 0 + 2)) /\
           read Q11 s = word_xor (aes_ctr_block aes256_cipher c nonce rk ((8 * 0 + 3))) (inblock (8 * 0 + 3)) /\
           read Q12 s = word_xor (aes_ctr_block aes256_cipher c nonce rk ((8 * 0 + 4))) (inblock (8 * 0 + 4)) /\
           read Q13 s = word_xor (aes_ctr_block aes256_cipher c nonce rk ((8 * 0 + 5))) (inblock (8 * 0 + 5)) /\
           read Q14 s = word_xor (aes_ctr_block aes256_cipher c nonce rk ((8 * 0 + 6))) (inblock (8 * 0 + 6)) /\
           read Q15 s = word_xor (aes_ctr_block aes256_cipher c nonce rk ((8 * 0 + 7))) (inblock (8 * 0 + 7)) /\
           read Q0 s = word_reversefields 8 (ctr_block nonce (8 * 0 + c + 8)) /\
           read Q1 s = word_reversefields 8 (ctr_block nonce (8 * 0 + c + 9)) /\
           read Q2 s = word_reversefields 8 (ctr_block nonce (8 * 0 + c + 10)) /\
           read Q3 s = word_reversefields 8 (ctr_block nonce (8 * 0 + c + 11)) /\
           read Q4 s = word_reversefields 8 (ctr_block nonce (8 * 0 + c + 12)) /\
           htable_mem_8 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j) /\
           (!j. j < 8 * (0 + 1)
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block aes256_cipher c nonce rk (j)) (inblock j)))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * nb)])`,
  REWRITE_TAC[KEY15_SPLIT] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; ALLPAIRS; ALL;
              NONOVERLAPPING_CLAUSES] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REWRITE_CONV[fst AES256_GCM_ENC_ALT_EXEC]
      `LENGTH aes256_gcm_enc_alt_tmc`]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_8; htable_mem_4]) THEN
  SUBGOAL_THEN `~(nb = 4)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `5 <= nb` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY NSTEP (1--5) THEN NSTEP 6 THEN NSTEP 7 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[
    MATCH_MP DISPATCH4_NOT_TAKEN (CONJ (ASSUME `128 * nb < 2 EXP 64`) (ASSUME `~(nb = 4)`));
    MATCH_MP DISPATCH_SMALL_NOT_TAKEN (CONJ (ASSUME `128 * nb < 2 EXP 64`) (ASSUME `5 <= nb`));
    COND_CLAUSES]) THEN
  MAP_EVERY NSTEP (8--36) THEN
  MAP_EVERY NSTEP (37--261) THEN NSTEP 262 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP SETUP_BRANCH_COND_FALSE_GEN
    (CONJ (ASSUME `8 * (k + 1) < nb`) (CONJ (ASSUME `nb <= 8 * (k + 2)`)
          (ASSUME `val (in_p:int64) + 128 * (k + 1) < 2 EXP 63`))); COND_CLAUSES]) THEN
  LDP_SETUP_TAC 263 THEN LDP_SETUP_TAC 264 THEN MAP_EVERY NSTEP (265--271) THEN
  LDP_SETUP_TAC 272 THEN LDP_SETUP_TAC 273 THEN MAP_EVERY NSTEP (274--289) THEN
  NSTEP 290 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP SETUP_BRANCH_COND_TRUE_2
    (CONJ (ASSUME `k = 0`) (CONJ (ASSUME `8 * (k + 1) < nb`)
      (CONJ (ASSUME `nb <= 8 * (k + 2)`)
          (ASSUME `val (in_p:int64) + 128 * (k + 1) < 2 EXP 63`))));
    COND_CLAUSES]) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[htable_mem_8; htable_mem_4] THEN
  REPEAT CONJ_TAC THEN SETUP_RECON_TAC_GEN);;

(* ========================================================================= *)
(* PREPRETAIL (pipeline DRAIN):  pc+0xa10  ->  pc+0xee0                      *)
(* (.L256_enc_tail)                                                          *)
(*                                                                           *)
(* The software pipeline runs one 8-block GHASH group BEHIND the ciphertext  *)
(* stores.  At MAIN_LOOP exit (i = k) the last in-flight group (ciphertext   *)
(* blocks 8k..8k+7, held in v8..v15) has been STORED but NOT yet GHASHed;    *)
(* Q19 still holds nist_ghash..(8*k).  PREPRETAIL is the drain that folds    *)
(* that final group into Q19, advancing it to nist_ghash..(8*(k+1)), and     *)
(* finishes the AES of the NEXT 8 counter blocks (v0..v7, pre-rk14) that the *)
(* tail cascade will consume.  It performs NO ciphertext stores and NO       *)
(* plaintext loads (all `[x0]`/`[x2]` access is in the tail, >= 0xee0), and  *)
(* leaves every GPR (X0,X2,X3,X4,X5,X6,X10,X11,X16) UNCHANGED (objdump-      *)
(* verified: no add/sub/mov to those regs in 0xa10..0xedc).                  *)
(*                                                                           *)
(* The PREPRETAIL precondition is EXACTLY the MAIN_LOOP postcondition at i = *)
(* k (the state at pc+0xa10), plus aligned_bytes_loaded; they are bridged in *)
(* the composition by ENSURES_SEQUENCE_TAC.  The Q19 drain fold is          *)
(* STRUCTURALLY IDENTICAL                                                   *)
(* to the MAIN_LOOP body's (same leading `ext v19`@0x4f4 PRE- byteswap, same *)
(* pmull/pmull2/eor3 Karatsuba chain, same trailing raw MODULO `eor3         *)
(* v19,v19,v21,v17`@0xec0, NO trailing `ext v19`), so it closes via the      *)
(* ALREADY-PROVEN Q19_FOLD_TAC (route-c plain form).                         *)
(*                                                                           *)
(* - The accumulators do NOT drop                                            *)
(* mid-drive: probing register presence + concreteness                       *)
(* at s30/s150/s250/s301/s308 shows Q17/Q18/Q19 are all PRESENT and CONCRETE *)
(* (no old-state refs) through s308; the drive `MAP_EVERY NSTEP_GP (1--308)` *)
(* reaches pc+0xee0 with Q19 = the concrete sz365k raw fold.  FINAL_STATE +  *)
(* REPEAT CONJ_TAC leaves exactly 10 residuals: Q30 counter, Q19 GHASH fold, *)
(* and the 8 v0..v7 AES reconstructions (the rest close by ASM_REWRITE).     *)
(*                                                                           *)
(*      THE REAL (and only) OBSTRUCTION was that the drain's MODULO reduce   *)
(*        has                                                                *)
(*        a                                                                  *)
(*      DIFFERENT instruction schedule from the main-loop/standalone reduce. *)
(*        Its                                                                *)
(*      final `eor3 v19,v19,v21,v17`@0xec0 takes v21 = ext(v18)@0xe9c (->    *)
(*        Q21)                                                               *)
(*      and v17 = pmull(v18,w)@0xe64 (-> Q17).  The plain body stepper       *)
(*        NSTEP_G                                                            *)
(*      protects Q17/Q18/Q19 from WORD_SIMPLE_SUBWORD_CONV but NOT Q21, so   *)
(*        the                                                                *)
(*      SAME mid-accumulator v18 appeared UN-normalized inside the pmull     *)
(*        (via                                                               *)
(*        Q17)                                                               *)
(*      but NORMALIZED inside the ext (via Q21) - `ghash_reduce_raw`'s q18   *)
(*      requires the two identical, so RECON_GRR (GSYM ghash_reduce_raw)     *)
(*        could                                                              *)
(*        not                                                                *)
(*      higher-order match (verified: WORD_SIMPLE_SUBWORD_CONV on both makes *)
(*        them                                                               *)
(*      equal).  FIX = NSTEP_GP, an extended-guard stepper that ALSO         *)
(*        protects                                                           *)
(*      Q20/Q21 (the ext-scratch), keeping v18 un-normalized in both         *)
(*        positions.                                                         *)
(*      With NSTEP_GP the AC-swap + RECON_GRR fold-back FIRES (365k -> 69k)  *)
(*        and                                                                *)
(*      the k-indexed fold Q19_FOLD_TAC_K (= Q19_FOLD_TAC with i->k) closes  *)
(*        it                                                                 *)
(*      exactly as the main-loop body does.                                  *)
(*                                                                           *)
(* Exit forms VERIFIED on gate033b (drive to s308):                          *)
(*      PC = pc+0xee0; X0..X16 all preserved; Q31 preserved;                 *)
(*      Q28 = word_reversefields 8 (EL 14 rk)  (rk14, the tail's fused round *)
(*        key);                                                              *)
(*      Q30 exit = word_join lane-decomp of the +3-incremented counter =     *)
(*        word_reversefields 32 (ctr_block nonce (8*k+18))  (3 `add          *)
(*          v30`@0xa18/                                                      *)
(*         0xa24/0xea8; the high 32-lane gets +2+1);                         *)
(*      Q0..Q4 = 13-round aese/aesmc chain over word_reversefields 8         *)
(*        (ctr_block                                                         *)
(*        nonce (8*k+10+j))  (the pre-loaded counters, pre-rk14 AES state);  *)
(*      Q5..Q7 = same chain over the rev32 word_join decomp of ctr_block     *)
(*        nonce                                                              *)
(*        (8*k+15)  (freshly rev32'd from the incremented v30).              *)
(* The v0..v7 postcondition below states them as                             *)
(* XOR_AES256_CIPHER_RECONSTRUCT- reducible forms (word_xor (read Qj) rk14 = *)
(* word_reversefields 8 (aes256_ cipher ...)), matching the setup's          *)
(* convention and what the tail consumes (tail's first `eor3 v9,v8,v0,v28`   *)
(* XORs v0 with v28=rk14).                                                   *)
(* ========================================================================= *)

(* Extended-guard body stepper for the drain.  NSTEP_G protects Q17/Q18/Q19  *)
(* from the per-step WORD_SIMPLE_SUBWORD_CONV; the drain additionally needs  *)
(* Q20/Q21 protected because its reduce takes ext(v18)->Q21 and              *)
(* pmull(v18)->Q17 at DIFFERENT steps (0xe9c vs 0xe64), and if Q21's         *)
(* subwords are collapsed the two copies of the mid-accumulator v18 diverge  *)
(* and RECON_GRR can't match.                                                *)
let is_ghash_acc_pp th =
  let c = concl th in
  can (find_term (fun t -> match t with
      Comb(Const("read",_), r) ->
        (match r with
         | Const("Q17",_) | Const("Q18",_) | Const("Q19",_)
         | Const("Q20",_) | Const("Q21",_) -> true
         | _ -> false)
    | _ -> false)) c;;

(* PERF: fold the three per-step RULE_ASSUM_TAC passes into                  *)
(* ONE, and extend the is_ghash_acc_pp guard (already on the subword pass)   *)
(* to ALSO cover the word_add-nest REWRITE and NORMOFF passes.               *)
(* Rationale: those two passes are PROOF-PRESERVING no-ops on the giant      *)
(* Q17..Q21 GHASH accumulators - the word_add-nest rule fires only on        *)
(* `word_add(word_add _ (word _))(word _)` (register-pointer shape, absent   *)
(* from the word_join/word_subword accumulator folds) and NORMOFF only       *)
(* rewrites `word(c1+c2+..)` offsets (also absent) - yet REWRITE_RULE /      *)
(* CONV_RULE(ONCE_DEPTH) still fully TRAVERSE each giant accumulator every   *)
(* step (O(term-size) per fact per step).  Skipping the                      *)
(* accumulators entirely (all three sweeps are identity on them) makes       *)
(* per-step assumption cost FLAT in accumulator size instead of growing; on  *)
(* every OTHER fact the composed sweep is bit-identical to the three         *)
(* separate passes.                                                          *)
let NSTEP_GP_WADD_RULE = REWRITE_RULE[WORD_RULE
  `word_add (word_add b (word m)) (word nn):int64 = word_add b (word(m+nn))`];;

(* PERF: guard BOTH the word_add-nest flatten (has_wadd_nest)                *)
(* and the NORMOFF offset renormalisation (has_word_of_sum) with cheap       *)
(* short-circuiting find_terms, so each REWRITE_RULE / CONV_RULE net-walk    *)
(* runs only on facts that actually carry its redex.  Bit-identical to the   *)
(* bare passes per fact (each is a no-op on facts lacking its shape, exactly *)
(* what the guard skips), but avoids the traversal on the ~110 carried facts *)
(* that lack it.                                                             *)
let NSTEP_GP n =
  ARM_STEPS_TAC AES256_GCM_ENC_ALT_EXEC [n] THEN
  RULE_ASSUM_TAC(fun th ->
    if is_ghash_acc_pp th then th
    else
      let th1 = if has_wadd_nest (concl th) then NSTEP_GP_WADD_RULE th else th in
      let th2 = if has_word_of_sum (concl th1) then NORMOFF_RULE th1 else th1 in
      SUBWORD_NORM_RULE th2);;

(* The Q19 drain fold: Q19_FOLD_TAC with the accumulator index i -> k (the   *)
(* drain folds the last in-flight 8-block group at loop-bound k, advancing   *)
(* Q19 from nist_ghash..(8*k) to nist_ghash..(8*(k+1))).  Structurally       *)
(* identical to the main-loop body fold; see Q19_FOLD_TAC above for the full *)
(* route rationale.                                                          *)
let Q19_FOLD_TAC_K =
  ONCE_REWRITE_TAC[WORD_BITWISE_RULE
    `word_xor (word_xor (x:int128) e) p = word_xor (word_xor x p) e`] THEN
  REWRITE_TAC[RECON_GRR] THEN
  REWRITE_TAC[GSYM cipher_block] THEN REWRITE_TAC[CIPHER_BLOCK_NIST] THEN
  REWRITE_TAC[WORD_SUBWORD_REVERSEFIELDS] THEN
  SIMP_TAC[WORD_JOIN_COMBINE_LEMMA; ARITH] THEN
  REWRITE_TAC[WORD_SUBWORD_XOR] THEN REWRITE_TAC[WORD_SUBWORD_BYTESWAP128] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[WORD_SUBWORD_XOR] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[GSYM WORD_SUBWORD_XOR] THEN
  REWRITE_TAC[GHASH_REDUCE_RAW_DIST8_PLAIN] THEN
  REWRITE_TAC[NIST_GHASH_IS_POLYVAL] THEN
  REWRITE_TAC[ARITH_RULE
    `8 * (k + 1) = SUC(SUC(SUC(SUC(SUC(SUC(SUC(SUC(8 * k))))))))`] THEN
  REWRITE_TAC[list_of_seq] THEN REWRITE_TAC[GSYM APPEND_ASSOC] THEN
  REWRITE_TAC[APPEND] THEN
  REWRITE_TAC[GHASH_ACC_APPEND] THEN
  REWRITE_TAC[ADD1; GSYM ADD_ASSOC] THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
  MP_TAC(ISPECL
    [`ghash_twist (aes256_cipher (word 0) rk)`;
     `[nist_cipher_block aes256_cipher c nonce rk inblock (8*k+1);
       nist_cipher_block aes256_cipher c nonce rk inblock (8*k+2);
       nist_cipher_block aes256_cipher c nonce rk inblock (8*k+3);
       nist_cipher_block aes256_cipher c nonce rk inblock (8*k+4);
       nist_cipher_block aes256_cipher c nonce rk inblock (8*k+5);
       nist_cipher_block aes256_cipher c nonce rk inblock (8*k+6);
       nist_cipher_block aes256_cipher c nonce rk inblock (8*k+7)]:(int128)list`;
     `ghash_polyval_acc (ghash_twist (aes256_cipher (word 0) rk)) tag0
        (list_of_seq (nist_cipher_block aes256_cipher c nonce rk inblock) (8*k))`;
     `nist_cipher_block aes256_cipher c nonce rk inblock (8*k)`]
    GHASH_POLYVAL_ACC_BATCHED) THEN
  REWRITE_TAC[LENGTH; ghash_wide] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[ADD_0] THEN
  REWRITE_TAC[polyval_dot] THEN
  REWRITE_TAC[GSYM PROP3_XOR] THEN
  AP_TERM_TAC THEN CONV_TAC WORD_BITWISE_RULE;;

(* Q30 counter closer (drain does 3 `add v30`, so exit counter = 8*k+18).    *)
let PP_CTR_CLOSE =
  REWRITE_TAC[WORD_SUBWORD_REVERSEFIELDS_32; WORD_SUBWORD_CTR_BLOCK_32] THEN
  REWRITE_TAC[GSYM WORD_ADD; WORD_ADD_0] THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
  REWRITE_TAC[CTR_BLOCK_RECONSTRUCT_REV32] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;;

(* v0..v7 AES closer.  v0..v4 are pinned as word_reversefields 8 (ctr_block  *)
(* ..) so AES256_CIPHER_RECONSTRUCT + MAP + KEYLIST close directly.  v5..v7  *)
(* are freshly rev32'd from the incremented v30, so the AES reconstruct      *)
(* leaves a plaintext residual word_reversefields 8 (aes256_cipher           *)
(* <rev-lanes> rk) = ..(ctr_block ..) which the counter-lane reconstruct     *)
(* (WORD_SUBWORD_*32 + CTR_BLOCK_RECONSTRUCT_REV8 +                          *)
(* REVERSEFIELDS_REVERSEFIELDS) folds; the TRY makes it a no-op for v0..v4   *)
(* (already closed).                                                         *)
let PP_AES_CLOSE =
  ASM_REWRITE_TAC[AES256_CIPHER_RECONSTRUCT; MAP;
                  WORD_REVERSEFIELDS_REVERSEFIELDS; AES256_CIPHER_KEYLIST] THEN
  TRY(REWRITE_TAC[GSYM WORD_ADD] THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
      REWRITE_TAC[WORD_SUBWORD_REVERSEFIELDS_32; WORD_SUBWORD_CTR_BLOCK_32] THEN
      REWRITE_TAC[GSYM WORD_ADD] THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
      REWRITE_TAC[CTR_BLOCK_RECONSTRUCT_REV8] THEN
      REWRITE_TAC[WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
      REWRITE_TAC[GSYM ADD_ASSOC] THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
      REFL_TAC);;

(* Shape-routed per-goal dispatcher over the 10 post-FINAL_STATE residuals:  *)
(* nist_ghash-RHS -> Q19 fold; word_join=word_reversefields -> Q30 counter;  *)
(* the 8 v-register AES eqs -> PP_AES_CLOSE; anything else -> ASM_REWRITE.   *)
let PP_DISPATCH : tactic = fun (asl,w as gl) ->
  if is_eq w then
    let l,r = dest_eq w in
    let rhd = try fst(dest_const(fst(strip_comb r))) with _ -> "?" in
    let lhd = try fst(dest_const(fst(strip_comb l))) with _ -> "?" in
    if rhd = "nist_ghash" then Q19_FOLD_TAC_K gl
    else if lhd = "word_join" && rhd = "word_reversefields" then PP_CTR_CLOSE gl
    else PP_AES_CLOSE gl
  else ASM_REWRITE_TAC[] gl;;

(* ------------------------------------------------------------------------- *)
(* PREPRETAIL_GEN: the pipeline-drain (PREPRETAIL stage) theorem, with the   *)
(* VESTIGIAL `~(k = 0)` precond conjunct DROPPED, so it also covers k=0 (the *)
(* g=1 reassembly leg, nblocks 9..16, where the main loop runs 0 times and   *)
(* prepretail+tail do all the work).  The body is pure straight-line GHASH   *)
(* drain (REWRITE+STRIP+INIT + MAP_EVERY NSTEP_GP (1--308) + FINAL_STATE +   *)
(* PP_DISPATCH) with NO branch and ZERO uses of `~(k = 0)` (NSTEP_GP is      *)
(* k-independent; PP_DISPATCH/Q19_FOLD_TAC_K use 8*k symbolically but never  *)
(* case-split k=0).  It is the sole prepretail-stage theorem in the proof.   *)
(* ------------------------------------------------------------------------- *)
let AES256_GCM_ENC_ALT_PREPRETAIL_GEN = prove
 (`!in_p out_p tag_p ivec_p key_p htable_p mod_p end_p
     tag0 nonce c rk inblock nb k pc.
    8 * (k + 1) <= nb /\
    end_p = word_add in_p (word (128 * (k + 1))) /\
    val in_p + 128 * (k + 1) < 2 EXP 63 /\
    nonoverlapping (out_p, 16 * nb)
                   (word pc, LENGTH aes256_gcm_enc_alt_tmc) /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * nb)]
      [(in_p, 16 * nb); (key_p, 240); (htable_p, 192);
       (tag_p, 16); (ivec_p, 16); (mod_p, 8)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) aes256_gcm_enc_alt_tmc /\
           read PC s = word (pc + 0xa10) /\
           read X0 s = word_add in_p (word (128 * (k + 1))) /\
           read X2 s = word_add out_p (word (128 * (k + 1))) /\
           read X3 s = tag_p /\
           read X9 s = word (16 * nb) /\
           read X4 s = word_add in_p (word (16 * nb)) /\
           read X16 s = ivec_p /\
           read X5 s = end_p /\
           read X6 s = htable_p /\
           read X10 s = mod_p /\
           read X11 s = key_p /\
           read (memory :> bytes64 mod_p) s = word 0xc200000000000000 /\
           wordlist_from_memory(key_p,15) s = MAP (word_reversefields 8) rk /\
           read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce c) /\
           read Q30 s = word_reversefields 32 (ctr_block nonce (8 * k + c + 13)) /\
           read Q31 s = word 79228162514264337593543950336 /\
           read Q19 s =
             nist_ghash (aes256_cipher (word 0) rk) tag0
                 (list_of_seq (nist_cipher_block aes256_cipher c nonce rk inblock) (8 * k)) /\
           read Q8 s = word_xor (aes_ctr_block aes256_cipher c nonce rk ((8 * k + 0))) (inblock (8 * k + 0)) /\
           read Q9 s = word_xor (aes_ctr_block aes256_cipher c nonce rk ((8 * k + 1))) (inblock (8 * k + 1)) /\
           read Q10 s = word_xor (aes_ctr_block aes256_cipher c nonce rk ((8 * k + 2))) (inblock (8 * k + 2)) /\
           read Q11 s = word_xor (aes_ctr_block aes256_cipher c nonce rk ((8 * k + 3))) (inblock (8 * k + 3)) /\
           read Q12 s = word_xor (aes_ctr_block aes256_cipher c nonce rk ((8 * k + 4))) (inblock (8 * k + 4)) /\
           read Q13 s = word_xor (aes_ctr_block aes256_cipher c nonce rk ((8 * k + 5))) (inblock (8 * k + 5)) /\
           read Q14 s = word_xor (aes_ctr_block aes256_cipher c nonce rk ((8 * k + 6))) (inblock (8 * k + 6)) /\
           read Q15 s = word_xor (aes_ctr_block aes256_cipher c nonce rk ((8 * k + 7))) (inblock (8 * k + 7)) /\
           read Q0 s = word_reversefields 8 (ctr_block nonce (8 * k + c + 8)) /\
           read Q1 s = word_reversefields 8 (ctr_block nonce (8 * k + c + 9)) /\
           read Q2 s = word_reversefields 8 (ctr_block nonce (8 * k + c + 10)) /\
           read Q3 s = word_reversefields 8 (ctr_block nonce (8 * k + c + 11)) /\
           read Q4 s = word_reversefields 8 (ctr_block nonce (8 * k + c + 12)) /\
           htable_mem_8 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j) /\
           (!j. j < 8 * (k + 1)
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block aes256_cipher c nonce rk (j)) (inblock j)))
      (\s. aligned_bytes_loaded s (word pc) aes256_gcm_enc_alt_tmc /\
           read PC s = word (pc + 0xee0) /\
           read X0 s = word_add in_p (word (128 * (k + 1))) /\
           read X2 s = word_add out_p (word (128 * (k + 1))) /\
           read X3 s = tag_p /\
           read X9 s = word (16 * nb) /\
           read X4 s = word_add in_p (word (16 * nb)) /\
           read X16 s = ivec_p /\
           read X5 s = end_p /\
           read X6 s = htable_p /\
           read X10 s = mod_p /\
           read X11 s = key_p /\
           read (memory :> bytes64 mod_p) s = word 0xc200000000000000 /\
           wordlist_from_memory(key_p,15) s = MAP (word_reversefields 8) rk /\
           read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce c) /\
           read Q28 s = word_reversefields 8 (EL 14 rk) /\
           read Q30 s = word_reversefields 32 (ctr_block nonce (8 * k + c + 16)) /\
           read Q31 s = word 79228162514264337593543950336 /\
           read Q19 s =
             nist_ghash (aes256_cipher (word 0) rk) tag0
                 (list_of_seq (nist_cipher_block aes256_cipher c nonce rk inblock) (8 * (k + 1))) /\
           word_xor (read Q0 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * k + c + 8)) rk) /\
           word_xor (read Q1 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * k + c + 9)) rk) /\
           word_xor (read Q2 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * k + c + 10)) rk) /\
           word_xor (read Q3 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * k + c + 11)) rk) /\
           word_xor (read Q4 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * k + c + 12)) rk) /\
           word_xor (read Q5 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * k + c + 13)) rk) /\
           word_xor (read Q6 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * k + c + 14)) rk) /\
           word_xor (read Q7 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * k + c + 15)) rk) /\
           htable_mem_8 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j) /\
           (!j. j < 8 * (k + 1)
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block aes256_cipher c nonce rk (j)) (inblock j)))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * nb)])`,
  REWRITE_TAC[KEY15_SPLIT] THEN
  (* body CLOSED CHEAT-FREE.  Drive the 308-instr drain with the                *)
  (* extended-guard stepper NSTEP_GP (protects Q17..Q21 so the reduce's mid      *)
  (* accumulator v18 stays un-normalized in both the pmull and ext positions),   *)
  (* then FINAL_STATE + REPEAT CONJ_TAC + the shape-routed dispatcher            *)
  (* PP_DISPATCH (Q19 fold / Q30 counter / v0..v7 AES / ASM_REWRITE).            *)
  REWRITE_TAC[htable_mem_8; htable_mem_4; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              ALLPAIRS; ALL; NONOVERLAPPING_CLAUSES] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REWRITE_CONV[fst AES256_GCM_ENC_ALT_EXEC]
    `LENGTH aes256_gcm_enc_alt_tmc`]) THEN
  MAP_EVERY NSTEP_GP (1--308) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN PP_DISPATCH);;

(* ========================================================================= *)
(* TAIL cascade (WHOLE-BLOCKS variant, pc+0xee0 -> pc+0x1154).               *)
(*                                                                           *)
(* This is the pipeline EPILOGUE: it processes the FINAL in-flight 8-block   *)
(* group (keystreams pre-loaded in Q0..Q7 at prepretail exit, output blocks  *)
(* 8*(k+1)..8*(k+1)+7 = nb-8..nb-1) - storing their ciphertext and folding   *)
(* them into the GHASH accumulator Q19 - then does the final GF(2^128)       *)
(* MODULO reduce and the two memory writebacks:                              *)
(*      str q30,[x16]  -> ivec  = word_reversefields 8 (ctr_block            *)
(*        ..                                                                 *)
(*         nb+c)                                                             *)
(*      st1 {v19},[x3] -> tag   = word_reversefields 8 (nist_ghash           *)
(*        ..                                                                 *)
(*        nb)                                                                *)
(*                                                                           *)
(* SCOPE: block-aligned (nb = 8*(k+2)).  At tail entry the remaining-bytes   *)
(* register x5 = X4 - X0 = 16*nb - 128*(k+1) = 128, so the computed cascade  *)
(* `cmp x5,#0x70`@0xefc then `b.gt`@0x1424 takes exact8_drain (0x1178);      *)
(* the tail is a single straight-line drain, NOT the 8 partial cascade       *)
(* variants (which the whole-blocks .S never reaches for a whole multiple of *)
(* 8 blocks).  The final-block path has NO partial-block masking (no ld1     *)
(* overread / mvn/lsr/csel mask / and v9,v0 / bif - the final block is a     *)
(* plain full block).                                                        *)
(*                                                                           *)
(* The Q19 drain fold is STRUCTURALLY the SAME KIND as PREPRETAIL /          *)
(* MAIN_LOOP (pmull/pmull2/eor3 Karatsuba over the 8 fresh cipherblocks,     *)
(* reduce), so it reuses the main-loop machinery (NSTEP_GP / RECON_GRR /     *)
(* Q19_FOLD_TAC-style).                                                      *)
(*                                                                           *)
(* The precondition is PREPRETAIL's postcondition verbatim (pc+0xee0 state). *)
(* NB the return value X0 = X9 = byte_len (mov x0,x9@0x1154) is NOT asserted *)
(* in the postcondition (mirrors x4 fast_tail, whose _CORRECT/_SUBROUTINE    *)
(* both omit the X0 return value); the tail ends at pc+0x1154 just after the *)
(* last crypto store, and the wrapper handles the ldp epilogue + ret.        *)
(* ========================================================================= *)

(* Store-permutation lemmas (ported from x4 fast_tail @437/457):             *)
(* TAG_STORE_REV64 = the `ext v19;#8` + `rev64 v19` byte-permutation the     *)
(* tail applies before st1 [x3] equals word_reversefields 8;                 *)
(* IVEC_STORE_REV32 = the rev32 v30 permutation before str [x16].  Both pure *)
(* BITBLAST.                                                                 *)
let TAG_STORE_REV64 = prove
 (`!x:int128.
    word_join
     (word_join
      (word_join
       (word_join (word_subword x (0,8):byte) (word_subword x (8,8):byte):int16)
       (word_join (word_subword x (16,8):byte) (word_subword x (24,8):byte):int16):int32)
      (word_join
       (word_join (word_subword x (32,8):byte) (word_subword x (40,8):byte):int16)
       (word_join (word_subword x (48,8):byte) (word_subword x (56,8):byte):int16):int32):int64)
     (word_join
      (word_join
       (word_join (word_subword x (64,8):byte) (word_subword x (72,8):byte):int16)
       (word_join (word_subword x (80,8):byte) (word_subword x (88,8):byte):int16):int32)
      (word_join
       (word_join (word_subword x (96,8):byte) (word_subword x (104,8):byte):int16)
       (word_join (word_subword x (112,8):byte) (word_subword x (120,8):byte):int16):int32):int64):int128
    = word_reversefields 8 x`,
  CONV_TAC BITBLAST_RULE);;

(* tbl tail-format: the fast2 drain replaces the `ext v19;#8 ; rev64         *)
(* v19` 16-byte byte-reverse with a single `tbl v19.16b,{v19.16b},v25.16b`   *)
(* where v25 = the reverse index [15..0] = word                              *)
(* 0x000102030405060708090a0b0c0d0e0f. arm_TBL (datasize 128) yields         *)
(* `usimd16 (\x. word_subword Q19 (8*val x,8)) Q25`; with Q25 = that index   *)
(* this equals word_reversefields 8 Q19, so the drain closes EXACTLY as the  *)
(* ext+rev64 path (TAG_STORE_REV64) did.                                     *)

let IVEC_STORE_REV32 = prove
 (`!y:int128.
    word_join
     (word_join
      (word_reversefields 8 (word_subword (word_reversefields 32 y) (96,32):int32):int32)
      (word_reversefields 8 (word_subword (word_reversefields 32 y) (64,32):int32):int32):int64)
     (word_join
      (word_reversefields 8 (word_subword (word_reversefields 32 y) (32,32):int32):int32)
      (word_reversefields 8 (word_subword (word_reversefields 32 y) (0,32):int32):int32):int64):int128
    = word_reversefields 8 y`,
  CONV_TAC BITBLAST_RULE);;

(* x5 at the tail entry (sub x5,x4,x0@0xee4) = (in_p+16*nb) -                *)
(* (in_p+128*(k+1)) = 128 under block-aligned nb = 8*(k+2); once rewritten   *)
(* to `word 128` the NSTEP_GP over cmp x5,#0x70 ; b.gt@0x1424 resolves the   *)
(* branch to pc+0x1178 automatically (concrete flag), so NO separate         *)
(* branch-discharge lemma.                                                   *)
let KS_SOLVE = prove
 (`!a b c:int128. word_xor a b = c ==> a = word_xor c b`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  CONV_TAC WORD_BITWISE_RULE);;

(* Eta/beta collapse for the accumulator-block (block-0) artifact.  The      *)
(* batched fold's block-0 index 8*(k+1)+0 reduces to 8*(k+1), and            *)
(* higher-order matching in GHASH_POLYVAL_ACC_BATCHED leaves the `inblock`   *)
(* slot as a CONSTANT lambda `nist_cipher_block nonce rk (\x. inblock        *)
(* (8*(k+1))) (8*(k+1))` - beta-equal to the clean form but opaque to        *)
(* WORD_BITWISE_RULE (which can't see through nist_cipher_block).  ETA_CONV  *)
(* does NOT fire (the lambda is constant, not \x.f x) so a targeted          *)
(* beta-collapse lemma is needed before the final AP_TERM.                   *)
let NCB_ETA = prove
 (`nist_cipher_block aes256_cipher c nonce rk (\x:num. inb (m:num)) m =
   nist_cipher_block aes256_cipher c nonce rk inb m`,
  REWRITE_TAC[nist_cipher_block; cipher_block] THEN CONV_TAC(DEPTH_CONV BETA_CONV));;

(* The TAIL Q19 drain fold: folds the FINAL in-flight 8-block group          *)
(* 8*(k+1)..8*(k+1)+7, advancing Q19 from nist_ghash..(8*(k+1)) to           *)
(* nist_ghash..(8*(k+2)) = ..nb (one more GHASH_ACC_APPEND round than        *)
(* PREPRETAIL).                                                              *)
(*                                                                           *)
(* this is NOT Q19_FOLD_TAC_K verbatim.  Two hardware                        *)
(* divergences make the tail's reduce differ from PREPRETAIL's, both         *)
(* byte-verified via objdump:                                                *)
(*                                                                           *)
(* (1) OPERAND ORDER of the final reduce eor3.  PREPRETAIL@0x9d0 emits       *)
(*         `eor3 v19,v19,v21,v17` (ext,pmull) = `word_xor (word_xor p3 ext)  *)
(*           pmull`, so                                                      *)
(*         it needs a leading AC-swap to reach ghash_reduce_raw's            *)
(*           `word_xor(word_xor                                              *)
(*         p3 pmull) ext` shape.  The TAIL emits `eor3                       *)
(*           v19,v19,v17,v21`                                                *)
(*         (pmull,ext) = ALREADY in ghash_reduce_raw order - so the copied   *)
(*           leading                                                         *)
(*         acswap flips it OUT (RECON_GRR no-ops -> AP_TERM_TAC head         *)
(*           mismatch                                                        *)
(*           = the                                                           *)
(*         full-file-gate `Failure "AP_TERM_TAC"`).  FIX: DROP the leading   *)
(*           acswap.                                                         *)
(*                                                                           *)
(* (2) BLOCK PROVENANCE.  PREPRETAIL folds the INVARIANT-CLEAN v8..v15       *)
(* blocks                                                                    *)
(*         (`word_xor (aes_ctr_block J) (inblock J)`).  The TAIL recomputes  *)
(*           the last 8                                                      *)
(*         blocks fresh (eor3 v9,v8,v0,v28 + KS_SOLVE), so each block enters *)
(*           the reduce                                                      *)
(*         as the RAW form `word_xor (word_xor inblock (word_xor aes rk14))  *)
(*           rk14`                                                           *)
(*         (double-rk14, inblock-first, aes NOT folded to aes_ctr_block).    *)
(*           It                                                              *)
(*           must be                                                         *)
(*         normalised to the clean `cipher_block` shape BEFORE the proven    *)
(*           route:                                                          *)
(*           - blocknorm cancels the double rk14 (word_xor (word_xor i       *)
(*             (word_xor a r))                                               *)
(*             r = word_xor i a);                                            *)
(*           - WORD_REDUCE_CONV+WORD_XOR_0 clear a spurious                  *)
(*             word_subword(word                                             *)
(*             0)(64,64);                                                    *)
(*           - comm_ib flips inblock-first -> aes-first (word_xor i (rev8 a) *)
(*             =                                                             *)
(*             word_xor (rev8 a) i);                                         *)
(*           - the ctr index 8*k+(10+m) = (8*(k+1)+m)+2 lets GSYM            *)
(*             aes_ctr_block fold                                            *)
(*             rev8(aes256_cipher (ctr_block nonce (J+2)) rk) ->             *)
(*               aes_ctr_block                                               *)
(*               J, then                                                     *)
(*             GSYM cipher_block + CIPHER_BLOCK_NIST reach                   *)
(*               nist_cipher_block.                                          *)
(*                                                                           *)
(* After cleaning, the tail's three Karatsuba lanes are ALIGNED (block order *)
(* [7..0] paired with h^[0..7] uniformly across all lanes), so               *)
(* GHASH_REDUCE_RAW_XOR (order-agnostic linearity) + KARATSUBA_IS_DOT_HW     *)
(* fire DIRECTLY into 8 clean polyval_dots - no DIST8_PLAIN (which bakes in  *)
(* the body's misaligned [1;0;3;2..] cross order and thus no-ops on the      *)
(* tail).  The proven batched-fold continuation then closes, modulo the      *)
(* block-0 NCB_ETA cleanup above.                                            *)
let fold_q19_at lhstm cnt foldtac : tactic =
  RULE_ASSUM_TAC(fun th ->
    let c = concl th in
    if is_eq c && lhs c = lhstm
    then TRANS th (prove
      (mk_eq(rhs c,
        vsubst [cnt, `n_blocks_fold:num`]
          `nist_ghash (aes256_cipher (word 0) rk) tag0
             (list_of_seq (nist_cipher_block aes256_cipher c nonce rk inblock) n_blocks_fold)`),
       foldtac))
    else th);;

let DISCARD_REGS deadl : tactic =
  let reg_of th =
    try let c = concl th in
        if not(is_eq c) then "" else
        let f,args = strip_comb (lhs c) in
        if fst(dest_const f) = "read"
        then (match args with c::_ -> (try fst(dest_const c) with Failure _ -> "") | _ -> "")
        else ""
    with Failure _ -> "" in
  REPEAT(FIRST_X_ASSUM(fun th ->
    if List.mem (reg_of th) deadl then K ALL_TAC th else fail()));;

(* DISCARD_DEAD_REDUCE_SCRATCH drops the reduce-scratch Q-registers that die *)
(* during the tail drive, so ARM_STEPS_TAC stops re-stamping their large     *)
(* terms over the remaining steps.                                           *)
(* (1) Q27 is the tail's Karatsuba partial-product lane; its last read is at *)
(* drive step ~112, so it is dropped at s115 (the earliest point at which    *)
(* the drop is sound). This keeps ARM_STEPS_TAC from re-stamping its large   *)
(* term over the remaining drive steps 116..136. (2) After the Q19 fold      *)
(* every register except Q0..Q7 (the 8 out-block ciphertexts), Q19 (the      *)
(* folded compact tag) and Q30 (the ivec counter) is dead: none is read by   *)
(* steps 137..139 (ext/rev64/st1) nor referenced by the                      *)
(* postcondition/MAYCHANGE, so the post-fold drop covers all 21 dead         *)
(* Q-registers. Q27 is absent here (already dropped at s115). Q28/Q31 are    *)
(* dropped at tail entry (dead from entry; see DISCARD_DEAD_HTABLE / the     *)
(* body), so they are not in this post-fold list.                            *)
let DISCARD_DEAD_REDUCE_SCRATCH : tactic =
  DISCARD_REGS
    ["Q17"; "Q18"; "Q20"; "Q21"; "Q22"; "Q23"; "Q24"; "Q25"; "Q26";
     "Q29"; "Q16"; "Q8"; "Q9"; "Q10"; "Q11"; "Q12";
     "Q13"; "Q14"; "Q15"];;

(* PERF: DROP the 15 DEAD round-key memory facts at tail                     *)
(* entry. The precondition carries `read (memory :> bytes128 (word_add key_p *)
(* (word 16*i))) s = word_reversefields 8 (EL i rk)` for i=0..14 (the        *)
(* AES-256 expanded round keys in memory).  DISCARD_REGS only drops REGISTER *)
(* facts (its reg_of returns "" for a `memory :> ..` component), so these 15 *)
(* facts otherwise survive ALL ~127 drive steps, and ARM_STEPS_TAC re-stamps *)
(* each one every step (cost is per-CARRIED-FACT, not just per-term-size).   *)
(* But the tail is a streaming GHASH DRAIN: it runs NO AES rounds (the 8     *)
(* keystreams Q0..Q7 are already computed at tail entry - see the pre-       *)
(* condition `word_xor (read Qj) rk14 = word_reversefields 8 (aes256_cipher  *)
(* ..)`), so the round keys in memory are DEAD from tail entry onward - no   *)
(* instruction reads key_p memory, and neither the postcondition nor the     *)
(* MAYCHANGE frame mentions it. Dropping them right after the s1..9 prefix   *)
(* (before the 10--136 drive) is PROOF- PRESERVING (full tail proof still    *)
(* closes 0 subgoals) and removes 15 of ~101 carried facts from every        *)
(* subsequent ARM_STEPS re-stamp.  Complements the register discards (those  *)
(* shrink the reduce scratch; this drops the drive-long dead memory operands *)
(* the register-only reg_of never reached).                                  *)
let DISCARD_DEAD_KEYMEM : tactic =
  REPEAT(FIRST_X_ASSUM(fun th ->
    let c = concl th in
    if is_eq c &&
       can (find_term (fun t -> t = `key_p:int64`)) (lhs c) &&
       can (find_term (fun t -> match t with Const("memory",_) -> true | _ -> false))
           (lhs c)
    then K ALL_TAC th else fail()));;

(* PERF: DROP the 6 DEAD htable (H-power) memory facts at tail               *)
(* entry. htable_mem_8 (unfolded at INIT) contributes 12 `read (memory :>    *)
(* bytes128 (word_add htable_p (word off))) s = ..` facts, at offsets        *)
(* 0,16,..,176.  But the executed 8-block tail (0x1178..0x1324) loads x6     *)
(* (= htable_p) ONLY at the six low offsets {0,16,32,48,64,80} (ldr q25..q20 *)
(* in the drain) - the single-accumulator                                    *)
(* whole-blocks tail uses only H^1..H^4 + the low Karatsuba mids. The 6      *)
(* facts at offsets {96,112,128,144,160,176} (byteswap128(h_power 4..7) and  *)
(* the word_join karatsuba_mid pairs for h 4..7) are NEVER read by any tail  *)
(* instruction, and the postcondition mentions no htable memory - DEAD FROM  *)
(* ENTRY.  Like the round-key drop, dropping them right after the s1..9      *)
(* prefix removes 6 of the ~101 carried facts from every subsequent          *)
(* ARM_STEPS re-stamp.  PROOF-PRESERVING (full tail proof still closes 0     *)
(* subgoals).  DISCARD_DEAD_KEYMEM/DISCARD_REGS miss them (one keys on       *)
(* key_p, the other on register components).                                 *)
let dead_htable_offs = [96; 112; 128; 144; 160; 176];;
let DISCARD_DEAD_HTABLE : tactic =
  REPEAT(FIRST_X_ASSUM(fun th ->
    let c = concl th in
    if is_eq c &&
       can (find_term (fun t -> t = `htable_p:int64`)) (lhs c) &&
       can (find_term (fun t -> match t with Const("memory",_) -> true | _ -> false))
           (lhs c) &&
       can (find_term (fun t -> match t with
              Comb(Const("word",_), n) ->
                (try List.mem (dest_small_numeral n) dead_htable_offs
                 with Failure _ -> false)
            | _ -> false)) (lhs c)
    then K ALL_TAC th else fail()));;

let TAIL_X5_REM1 = prove
 (`!(in_p:int64) g.
     word_sub (word_add in_p (word (16 * (8 * g + 1))))
              (word_add in_p (word (128 * g))) = word 16:int64`,
  REPEAT STRIP_TAC THEN CONV_TAC WORD_RULE);;

(* Single-block Q19 fold (x4 fast_tail rem=1 route; front-end shared with    *)
(* TAIL_Q19_FOLD, single-block APPEND tail instead of GHASH_POLYVAL_ACC_     *)
(* BATCHED).  Proves the raw single-block ghash_reduce at s78 equals the     *)
(* compact nist_ghash..(8*g+1): RECON_GRR exposes ghash_reduce_raw, the      *)
(* block normalizes to nist_cipher_block(8*g), KARATSUBA_IS_DOT_HW collapses *)
(* the three Karatsuba pmulls to a single polyval_dot, and the one-element   *)
(* list_of_seq(SUC)/NIST_GHASH_APPEND/CONS + NIST_DOT_IS_POLYVAL_DOT +       *)
(* h_power 0 closes it.                                                      *)
let TAIL_Q19_FOLD_REM1 =
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
    [WORD_BITWISE_RULE
      `word_xor (word_xor (i:int128) (word_xor a r)) r = word_xor i a`] THEN
  REWRITE_TAC[RECON_GRR] THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV WORD_REDUCE_CONV)) THEN
  REWRITE_TAC[WORD_XOR_0] THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
    [WORD_BITWISE_RULE `word_xor (word 0:int128) x = x`] THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
    [WORD_BITWISE_RULE
      `word_xor (i:int128) (word_reversefields 8 a) =
       word_xor (word_reversefields 8 a) i`] THEN
  REWRITE_TAC[GSYM aes_ctr_block] THEN
  REWRITE_TAC[GSYM cipher_block] THEN REWRITE_TAC[CIPHER_BLOCK_NIST] THEN
  REWRITE_TAC[WORD_SUBWORD_REVERSEFIELDS] THEN
  SIMP_TAC[WORD_JOIN_COMBINE_LEMMA; ARITH] THEN
  REWRITE_TAC[WORD_SUBWORD_XOR] THEN REWRITE_TAC[WORD_SUBWORD_BYTESWAP128] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[WORD_SUBWORD_XOR] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[GSYM WORD_SUBWORD_XOR] THEN
  REWRITE_TAC[KARATSUBA_IS_DOT_HW] THEN
  REWRITE_TAC[ARITH_RULE `8 * g + 1 = SUC(8 * g)`;
              ARITH_RULE `1 + 8 * g = SUC(8 * g)`] THEN
  REWRITE_TAC[list_of_seq] THEN
  REWRITE_TAC[NIST_GHASH_APPEND] THEN
  REWRITE_TAC[NIST_GHASH_CONS; nist_ghash] THEN
  REWRITE_TAC[NIST_DOT_IS_POLYVAL_DOT] THEN
  REWRITE_TAC[CONJUNCT1 h_power];;

(* Fold `read Q19 s78` (raw single-block reduce) -> compact                  *)
(* nist_ghash..(8*g+1) in place, mirroring TAIL_REM8's Q19 fold.             *)
let FOLD_Q19_REM1 : tactic =
  fold_q19_at `read Q19 s82 : int128` `8 * g + 1` TAIL_Q19_FOLD_REM1;;

let AES256_GCM_ENC_ALT_TAIL_REM1 = prove
 (`!in_p out_p tag_p ivec_p key_p htable_p mod_p end_p
     tag0 nonce c rk inblock nb g pc.
    nb = 8 * g + 1 /\
    end_p = word_add in_p (word (128 * g)) /\
    val in_p + 16 * nb < 2 EXP 63 /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
      [(word pc, LENGTH aes256_gcm_enc_alt_tmc);
       (in_p, 16 * nb); (key_p, 240); (htable_p, 192); (mod_p, 8)] /\
    PAIRWISE nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) aes256_gcm_enc_alt_tmc /\
           read PC s = word (pc + 0xee0) /\
           read X0 s = word_add in_p (word (128 * g)) /\
           read X2 s = word_add out_p (word (128 * g)) /\
           read X3 s = tag_p /\
           read X9 s = word (16 * nb) /\
           read X4 s = word_add in_p (word (16 * nb)) /\
           read X16 s = ivec_p /\
           read X5 s = end_p /\
           read X6 s = htable_p /\
           read X10 s = mod_p /\
           read X11 s = key_p /\
           read (memory :> bytes64 mod_p) s = word 0xc200000000000000 /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce c) /\
           read Q28 s = word_reversefields 8 (EL 14 rk) /\
           read Q30 s = word_reversefields 32 (ctr_block nonce (8 * g + c + 8)) /\
           read Q31 s = word 79228162514264337593543950336 /\
           read Q19 s =
             nist_ghash (aes256_cipher (word 0) rk) tag0
                 (list_of_seq (nist_cipher_block aes256_cipher c nonce rk inblock) (8 * g)) /\
           word_xor (read Q0 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + c)) rk) /\
           htable_mem_8 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j) /\
           (!j. j < 8 * g
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block aes256_cipher c nonce rk (j)) (inblock j)))
      (\s. read PC s = word (pc + 0x1154) /\
           read X9 s = word (16 * nb) /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce (nb + c)) /\
           read (memory :> bytes128 tag_p) s =
             word_reversefields 8
               (nist_ghash (aes256_cipher (word 0) rk) tag0
                  (list_of_seq (nist_cipher_block aes256_cipher c nonce rk inblock) nb)) /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block aes256_cipher c nonce rk (j)) (inblock j)))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * nb);
                  memory :> bytes(tag_p, 16);
                  memory :> bytes(ivec_p, 16)])`,
  REWRITE_TAC[htable_mem_8; htable_mem_4; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REWRITE_CONV[fst AES256_GCM_ENC_ALT_EXEC]
    `LENGTH aes256_gcm_enc_alt_tmc`]) THEN
  (* Assert the single tail input block; WITHOUT this the plaintext load stays *)
  (* a raw memory read and the whole ciphertext/GHASH chain drops.             *)
  SUBGOAL_THEN
   `read (memory :> bytes128 (word_add in_p (word (128 * g)))) s0 =
    inblock (8 * g)`
  ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `128 * g = 16 * (8 * g)`] THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  (* Invert the keystream fact so the ciphertext eor3 output is state-indep. *)
  RULE_ASSUM_TAC(fun th -> try MATCH_MP KS_SOLVE th with Failure _ -> th) THEN
  (* Steps 1..9 to the computed cascade@0xee4; x5 -> word 16 resolves the arm  *)
  (* concretely to the rem=1 arm (-> less_than_1 @0x10f0).                     *)
  MAP_EVERY NSTEP_GP (1--9) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[TAIL_X5_REM1]) THEN
  (* Steps 10..82: cascade fall-through + single-block fold + reduce, up to    *)
  (* the final reduce eor3@0x1144 (s78: read Q19 = raw single-block fold).      *)
  MAP_EVERY NSTEP_GP (10--82) THEN
  (* Fold Q19 to compact nist_ghash..(8*g+1) BEFORE ext/rev64/store (else rev64 *)
  (* balloons), then drop the dead reduce scratch.                             *)
  FOLD_Q19_REM1 THEN
  DISCARD_DEAD_REDUCE_SCRATCH THEN
  (* Steps 83..85: ext@0x1148 ; rev64@0x114c ; st1@0x1150 (tag) ; exit@0x1154. *)
  MAP_EVERY NSTEP_GP (83--85) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  (* ivec store: 7 fall-through `sub v30` roll ctr 8g+c+8 -> 8g+c+1 = nb+c.    *)
  CONJ_TAC THENL
   [REWRITE_TAC[IVEC_STORE_REV32] THEN
    REWRITE_TAC[WORD_SUBWORD_REVERSEFIELDS_32; WORD_SUBWORD_CTR_BLOCK_32] THEN
    REWRITE_TAC[WORD_RULE `word_sub (x:int32) (word 0) = x`] THEN
    REWRITE_TAC[WORD_RULE
      `word_sub (word_sub (word_sub (word_sub (word_sub (word_sub (word_sub
        (word (8 * g + c + 8):int32) (word 1)) (word 1)) (word 1)) (word 1))
        (word 1)) (word 1)) (word 1) = word (8 * g + c + 1)`] THEN
    REWRITE_TAC[CTR_BLOCK_RECONSTRUCT_REV8] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  (* tag store: read(tag_p) = rev8(nist_ghash..nb) (Q19 already folded).       *)
  CONJ_TAC THENL
   [REWRITE_TAC[TAG_STORE_REV64] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    UNDISCH_TAC `nb = 8 * g + 1` THEN ARITH_TAC;
    ALL_TAC] THEN
  (* out-forall (j<nb): OLD blocks j<8*g via the incoming out-forall; the ONE  *)
  (* NEW block j=8*g via the retained ciphertext store + double-rk14 cancel.   *)
  REWRITE_TAC[ARITH_RULE `j < 8 * g + 1 <=> j < 8 * g \/ j = 8 * g`] THEN
  ASM_REWRITE_TAC[TAUT `p \/ q ==> r <=> (p ==> r) /\ (q ==> r)`] THEN
  REWRITE_TAC[FORALL_AND_THM; FORALL_UNWIND_THM2] THEN
  REWRITE_TAC[ARITH_RULE `16 * 8 * g = 128 * g`] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[aes_ctr_block] THEN REWRITE_TAC[ARITH_RULE `8 * g + c = c + 8 * g`] THEN
  CONV_TAC WORD_BITWISE_RULE);;



(* ========================================================================= *)
(* - TAIL CASCADE arm rem=2 (nblocks = 8*g+2), lands at 0x1434.              *)
(*                                                                           *)
(* The second remainder-cascade leg (after rem=1).  It folds TWO fresh       *)
(* blocks (8*g and 8*g+1) into the GHASH accumulator via a 2-block BATCHED   *)
(* reduce (GHASH_POLYVAL_ACC_BATCHED), vs rem=1's single-block APPEND.       *)
(*                                                                           *)
(* Like TAIL_REM8, the rem>=2 arms `movi v17/v18/v19,#0` reset the           *)
(* accumulator and rebuild it with a fresh pmull/eor reduce; the 0x1434 arm  *)
(* does an `eor v27.8b,v27.8b,v8.8b` PARTIAL-lane write on the               *)
(* UNINITIALIZED Q27, so Q27 MUST be pinned (q27_init) at entry or the       *)
(* reduce chain Q18/Q19/Q17/Q21 references dead state and DISCARD_OLDSTATE   *)
(* drops it (the TAIL_REM8 q27_init pin; Q18 is movi-zeroed so needs no      *)
(* pin here - this is why rem=1, whose less_than_1 arm never touches v27,    *)
(* needed NO reg pin, but rem>=2 does).                                      *)
(* ========================================================================= *)

(* x5 at the rem=2 tail entry: 16*nb - 128*g = 32 under nb=8*g+2; once       *)
(* rewritten to `word 32` the cmp/b.gt cascade resolves to the rem=2 arm     *)
(* (b.eq@0x142c -> 0x1434) automatically (concrete flags), no branch lemma.  *)
let TAIL_X5_REM2 = prove
 (`!(in_p:int64) g.
     word_sub (word_add in_p (word (16 * (8 * g + 2))))
              (word_add in_p (word (128 * g))) = word 32:int64`,
  REPEAT STRIP_TAC THEN CONV_TAC WORD_RULE);;

(* Two-block Q19 fold: RECON_GRR exposes the reduce; the 2 blocks normalize  *)
(* to nist_cipher_block(8*g),(8*g+1); GHASH_REDUCE_RAW_XOR + KARATSUBA_IS_   *)
(* DOT_HW + KDOT_B0 (block-0 = the accumulator, carries the store-order      *)
(* byteswap) collapse the summed lanes to                                    *)
(*      word_xor (polyval_dot cb(8*g+1) H^0) (polyval_dot (sofar (x)         *)
(*        cb(8*g))                                                           *)
(*        H^1)                                                               *)
(* which is exactly GHASH_POLYVAL_ACC_BATCHED with bs=[cb(8*g+1)],           *)
(* b=cb(8*g), a=sofar; the RHS nist_ghash..(8*g+2) unfolds to the same via   *)
(* NIST_GHASH_IS_ POLYVAL + list_of_seq/APPEND/GHASH_ACC_APPEND + the        *)
(* batched lemma.  Only block 8*g+1's ctr index (8*g+3) needs the (8*g+1)+2  *)
(* reindex; block 8*g's ctr (8*g+2) already parses as (8*g)+2 so folds       *)
(* directly (a bare 8*g+2 reindex would also corrupt the RHS list count      *)
(* 8*g+2 -> DON'T add it).                                                   *)
let TAIL_Q19_FOLD_REM2 =
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
    [WORD_BITWISE_RULE
      `word_xor (word_xor (i:int128) (word_xor a r)) r = word_xor i a`] THEN
  REWRITE_TAC[RECON_GRR] THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV WORD_REDUCE_CONV)) THEN
  REWRITE_TAC[WORD_XOR_0] THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
    [WORD_BITWISE_RULE `word_xor (word 0:int128) x = x`] THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
    [WORD_BITWISE_RULE
      `word_xor (i:int128) (word_reversefields 8 a) =
       word_xor (word_reversefields 8 a) i`] THEN
  REWRITE_TAC[ARITH_RULE `8 * g + c + 1 = (8 * g + 1) + c`] THEN
  REWRITE_TAC[GSYM aes_ctr_block] THEN
  REWRITE_TAC[GSYM cipher_block] THEN REWRITE_TAC[CIPHER_BLOCK_NIST] THEN
  REWRITE_TAC[WORD_SUBWORD_REVERSEFIELDS] THEN
  SIMP_TAC[WORD_JOIN_COMBINE_LEMMA; ARITH] THEN
  REWRITE_TAC[WORD_SUBWORD_XOR] THEN REWRITE_TAC[WORD_SUBWORD_BYTESWAP128] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[WORD_SUBWORD_XOR] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[GSYM WORD_SUBWORD_XOR] THEN
  REWRITE_TAC[GHASH_REDUCE_RAW_XOR] THEN
  REWRITE_TAC[KARATSUBA_IS_DOT_HW] THEN
  REWRITE_TAC[KDOT_B0] THEN
  REWRITE_TAC[NIST_GHASH_IS_POLYVAL] THEN
  REWRITE_TAC[ARITH_RULE `8 * g + 2 = SUC(SUC(8 * g))`;
              ARITH_RULE `2 + 8 * g = SUC(SUC(8 * g))`] THEN
  REWRITE_TAC[list_of_seq] THEN REWRITE_TAC[GSYM APPEND_ASSOC] THEN
  REWRITE_TAC[APPEND] THEN
  REWRITE_TAC[GHASH_ACC_APPEND] THEN
  REWRITE_TAC[ADD1; GSYM ADD_ASSOC] THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
  MP_TAC(ISPECL
    [`ghash_twist (aes256_cipher (word 0) rk)`;
     `[nist_cipher_block aes256_cipher c nonce rk inblock (8*g+1)]:(int128)list`;
     `ghash_polyval_acc (ghash_twist (aes256_cipher (word 0) rk)) tag0
        (list_of_seq (nist_cipher_block aes256_cipher c nonce rk inblock) (8*g))`;
     `nist_cipher_block aes256_cipher c nonce rk inblock (8*g)`]
    GHASH_POLYVAL_ACC_BATCHED) THEN
  REWRITE_TAC[LENGTH; ghash_wide] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[ADD_0] THEN
  REWRITE_TAC[polyval_dot] THEN
  REWRITE_TAC[GSYM PROP3_XOR] THEN
  REWRITE_TAC[NCB_ETA] THEN
  REWRITE_TAC[ARITH_RULE `1 + 8 * g = 8 * g + 1`] THEN
  AP_TERM_TAC THEN CONV_TAC WORD_BITWISE_RULE;;

(* Fold `read Q19 s92` (raw 2-block reduce) -> compact nist_ghash..(8*g+2)   *)
(* in place BEFORE ext/rev64/store (mirror FOLD_Q19_REM1).                   *)
let FOLD_Q19_REM2 : tactic =
  fold_q19_at `read Q19 s53 : int128` `8 * g + 2` TAIL_Q19_FOLD_REM2;;

let AES256_GCM_ENC_ALT_TAIL_REM2 = prove
 (`!q27_init in_p out_p tag_p ivec_p key_p htable_p mod_p end_p
     tag0 nonce c rk inblock nb g pc.
    nb = 8 * g + 2 /\
    end_p = word_add in_p (word (128 * g)) /\
    val in_p + 16 * nb < 2 EXP 63 /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
      [(word pc, LENGTH aes256_gcm_enc_alt_tmc);
       (in_p, 16 * nb); (key_p, 240); (htable_p, 192); (mod_p, 8)] /\
    PAIRWISE nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) aes256_gcm_enc_alt_tmc /\
           read PC s = word (pc + 0xee0) /\
           read X0 s = word_add in_p (word (128 * g)) /\
           read X2 s = word_add out_p (word (128 * g)) /\
           read X3 s = tag_p /\
           read X9 s = word (16 * nb) /\
           read X4 s = word_add in_p (word (16 * nb)) /\
           read X16 s = ivec_p /\
           read X5 s = end_p /\
           read X6 s = htable_p /\
           read X10 s = mod_p /\
           read X11 s = key_p /\
           read (memory :> bytes64 mod_p) s = word 0xc200000000000000 /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce c) /\
           read Q27 s = q27_init /\
           read Q28 s = word_reversefields 8 (EL 14 rk) /\
           read Q30 s = word_reversefields 32 (ctr_block nonce (8 * g + c + 8)) /\
           read Q31 s = word 79228162514264337593543950336 /\
           read Q19 s =
             nist_ghash (aes256_cipher (word 0) rk) tag0
                 (list_of_seq (nist_cipher_block aes256_cipher c nonce rk inblock) (8 * g)) /\
           word_xor (read Q0 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + c)) rk) /\
           word_xor (read Q1 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + c + 1)) rk) /\
           word_xor (read Q2 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + c + 2)) rk) /\
           word_xor (read Q3 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + c + 3)) rk) /\
           word_xor (read Q4 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + c + 4)) rk) /\
           word_xor (read Q5 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + c + 5)) rk) /\
           word_xor (read Q6 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + c + 6)) rk) /\
           word_xor (read Q7 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + c + 7)) rk) /\
           htable_mem_8 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j) /\
           (!j. j < 8 * g
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block aes256_cipher c nonce rk (j)) (inblock j)))
      (\s. read PC s = word (pc + 0x1154) /\
           read X9 s = word (16 * nb) /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce (nb + c)) /\
           read (memory :> bytes128 tag_p) s =
             word_reversefields 8
               (nist_ghash (aes256_cipher (word 0) rk) tag0
                  (list_of_seq (nist_cipher_block aes256_cipher c nonce rk inblock) nb)) /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block aes256_cipher c nonce rk (j)) (inblock j)))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * nb);
                  memory :> bytes(tag_p, 16);
                  memory :> bytes(ivec_p, 16)])`,
  REWRITE_TAC[htable_mem_8; htable_mem_4; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REWRITE_CONV[fst AES256_GCM_ENC_ALT_EXEC]
    `LENGTH aes256_gcm_enc_alt_tmc`]) THEN
  (* Assert the 2 tail input blocks; WITHOUT this the plaintext loads stay      *)
  (* raw memory reads and the ciphertext/GHASH chain drops.                     *)
  SUBGOAL_THEN
   `read (memory :> bytes128 (word_add in_p (word (128 * g)))) s0 =
    inblock (8 * g) /\
    read (memory :> bytes128 (word_add in_p (word (128 * g + 16)))) s0 =
    inblock (8 * g + 1)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `128 * g + 16 = 16 * (8 * g + 1)`] THEN
    REWRITE_TAC[ARITH_RULE `128 * g = 16 * (8 * g)`] THEN
    CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  (* Invert the keystream facts so the ciphertext eor3 outputs are state-indep. *)
  RULE_ASSUM_TAC(fun th -> try MATCH_MP KS_SOLVE th with Failure _ -> th) THEN
  (* Steps 1..9 to the computed cascade@0xee4; x5 -> word 32 resolves the arm  *)
  (* concretely to the rem=2 arm (b.eq@0x142c -> 0x1434).                      *)
  MAP_EVERY NSTEP_GP (1--9) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[TAIL_X5_REM2]) THEN
  (* Steps 10..53: cascade fall-through + 2-block fold + reduce, up to the      *)
  (* final reduce eor3@0x14d0 (s92: read Q19 = raw 2-block reduce).            *)
  MAP_EVERY NSTEP_GP (10--53) THEN
  (* Fold Q19 to compact nist_ghash..(8*g+2) BEFORE ext/rev64/store, then drop  *)
  (* the dead reduce scratch.                                                   *)
  FOLD_Q19_REM2 THEN
  DISCARD_DEAD_REDUCE_SCRATCH THEN
  (* Steps 54..57: ext@0x14d4 ; rev64@0x14d8 ; st1@0x14dc (tag) ; exit@0x14e0. *)
  MAP_EVERY NSTEP_GP (54--57) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  (* ivec store: 6 fall-through `sub v30` roll ctr 8g+c+8 -> 8g+c+2 = nb+c.    *)
  CONJ_TAC THENL
   [REWRITE_TAC[IVEC_STORE_REV32] THEN
    REWRITE_TAC[WORD_SUBWORD_REVERSEFIELDS_32; WORD_SUBWORD_CTR_BLOCK_32] THEN
    REWRITE_TAC[WORD_RULE `word_sub (x:int32) (word 0) = x`] THEN
    REWRITE_TAC[WORD_RULE
      `word_sub (word_sub (word_sub (word_sub (word_sub (word_sub
        (word (8 * g + c + 8):int32) (word 1)) (word 1)) (word 1)) (word 1))
        (word 1)) (word 1) = word (8 * g + c + 2)`] THEN
    REWRITE_TAC[CTR_BLOCK_RECONSTRUCT_REV8] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  (* tag store: read(tag_p) = rev8(nist_ghash..nb) (Q19 already folded).        *)
  CONJ_TAC THENL
   [REWRITE_TAC[TAG_STORE_REV64] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    UNDISCH_TAC `nb = 8 * g + 2` THEN ARITH_TAC;
    ALL_TAC] THEN
  (* out-forall (j<nb): OLD blocks j<8*g via the incoming out-forall; the 2 NEW *)
  (* blocks j=8*g, 8*g+1 via the retained ciphertext stores + double-rk14 cancel.*)
  REWRITE_TAC[ARITH_RULE `j < 8 * g + 2 <=>
                       j < 8 * g \/ j = 8 * g \/ j = 8 * g + 1`] THEN
  ASM_REWRITE_TAC[TAUT `p \/ q ==> r <=> (p ==> r) /\ (q ==> r)`] THEN
  REWRITE_TAC[FORALL_AND_THM; FORALL_UNWIND_THM2] THEN
  REWRITE_TAC[ARITH_RULE `16 * (8 * g + b) = 128 * g + 16 * b`] THEN
  REWRITE_TAC[ARITH_RULE `16 * 8 * g = 128 * g`] THEN
  CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM WORD_ADD; WORD_ADD_0] THEN
  ONCE_REWRITE_TAC[WORD_BITWISE_RULE
    `word_xor (word_xor (inb:int128) ch) rk14 = word_xor ch (word_xor rk14 inb)`] THEN
  REWRITE_TAC[XOR_AES256_CIPHER_RECONSTRUCT] THEN
  ASM_REWRITE_TAC[MAP; WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
  REWRITE_TAC[aes_ctr_block; GSYM ADD_ASSOC] THEN
  CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; GSYM ADD_ASSOC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[ARITH_RULE `8 * g + c = c + 8 * g`] THEN
  REWRITE_TAC[ADD_ASSOC] THEN
  REWRITE_TAC[ARITH_RULE `1 + c = c + 1`; ARITH_RULE `2 + c = c + 2`;
              ARITH_RULE `3 + c = c + 3`; ARITH_RULE `4 + c = c + 4`;
              ARITH_RULE `5 + c = c + 5`; ARITH_RULE `6 + c = c + 6`;
              ARITH_RULE `7 + c = c + 7`] THEN
  CONV_TAC WORD_BITWISE_RULE);;



(* ========================================================================= *)
let AES256_GCM_ENC_ALT_FAST2_TAIL = prove
 (`!in_p out_p tag_p ivec_p htable_p mod_p
     tag0 nonce c rk inblock nb g pc.
    nb = 8 * g + 2 /\
    val in_p + 16 * nb < 2 EXP 63 /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
      [(word pc, LENGTH aes256_gcm_enc_alt_tmc);
       (in_p, 16 * nb); (htable_p, 192); (mod_p, 8)] /\
    PAIRWISE nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) aes256_gcm_enc_alt_tmc /\
           read PC s = word (pc + 0x17d4) /\
           read X0 s = word_add in_p (word (128 * g)) /\
           read X2 s = word_add out_p (word (128 * g)) /\
           read X3 s = tag_p /\
           read X9 s = word (16 * nb) /\
           read X6 s = htable_p /\
           read X10 s = mod_p /\
           read X16 s = ivec_p /\
           read Q12 s = word 0x000102030405060708090a0b0c0d0e0f /\
           read (memory :> bytes64 mod_p) s = word 0xc200000000000000 /\
           word_xor (read Q0 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * g + c)) rk) /\
           word_xor (read Q1 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * g + c + 1)) rk) /\
           read Q19 s =
             nist_ghash (aes256_cipher (word 0) rk) tag0
                 (list_of_seq (nist_cipher_block aes256_cipher c nonce rk inblock) (8 * g)) /\
           read Q28 s = word_reversefields 8 (EL 14 rk) /\
           read Q30 s = word_reversefields 32 (ctr_block nonce (8 * g + c + 2)) /\
           read Q31 s = word 79228162514264337593543950336 /\
           htable_mem_8 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j) /\
           (!j. j < 8 * g
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block aes256_cipher c nonce rk (j)) (inblock j)))
      (\s. read PC s = word (pc + 0x1154) /\
           read X9 s = word (16 * nb) /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce (nb + c)) /\
           read (memory :> bytes128 tag_p) s =
             word_reversefields 8
               (nist_ghash (aes256_cipher (word 0) rk) tag0
                  (list_of_seq (nist_cipher_block aes256_cipher c nonce rk inblock) nb)) /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block aes256_cipher c nonce rk (j)) (inblock j)))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * nb);
                  memory :> bytes(tag_p, 16);
                  memory :> bytes(ivec_p, 16)])`,
  REWRITE_TAC[htable_mem_8; htable_mem_4; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REWRITE_CONV[fst AES256_GCM_ENC_ALT_EXEC]
    `LENGTH aes256_gcm_enc_alt_tmc`]) THEN
  SUBGOAL_THEN
   `read (memory :> bytes128 (word_add in_p (word (128 * g)))) s0 =
    inblock (8 * g) /\
    read (memory :> bytes128 (word_add in_p (word (128 * g + 16)))) s0 =
    inblock (8 * g + 1)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `128 * g + 16 = 16 * (8 * g + 1)`] THEN
    REWRITE_TAC[ARITH_RULE `128 * g = 16 * (8 * g)`] THEN
    CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  RULE_ASSUM_TAC(fun th -> try MATCH_MP KS_SOLVE th with Failure _ -> th) THEN
  MAP_EVERY NSTEP_GP (1--39) THEN
  fold_q19_at `read Q19 s39 : int128` `8 * g + 2` TAIL_Q19_FOLD_REM2 THEN
  (*Q25 is the LIVE tbl index here (not reduce-scratch) -> KEEP it so read Q25 propagates to the tbl step       *)
  DISCARD_REGS ["Q17";"Q18";"Q20";"Q21";"Q22";"Q23";"Q24";"Q25";"Q26";"Q29";"Q16";"Q8";"Q9";"Q10";"Q11";"Q13";"Q14";"Q15"] THEN
  MAP_EVERY NSTEP_GP (40--42) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[IVEC_STORE_REV32] THEN
    REWRITE_TAC[WORD_SUBWORD_REVERSEFIELDS_32; WORD_SUBWORD_CTR_BLOCK_32] THEN
    REWRITE_TAC[WORD_RULE `word_sub (x:int32) (word 0) = x`] THEN
    REWRITE_TAC[WORD_RULE
      `word_sub (word_sub (word_sub (word_sub (word_sub (word_sub
        (word (8 * g + 10):int32) (word 1)) (word 1)) (word 1)) (word 1))
        (word 1)) (word 1) = word (8 * g + 4)`] THEN
    REWRITE_TAC[CTR_BLOCK_RECONSTRUCT_REV8] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[TAG_STORE_REV64] THEN  (*tbl w/ concrete index expands to the SAME word_join byte-reversal as ext+rev64                                    *)
    AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    UNDISCH_TAC `nb = 8 * g + 2` THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `j < 8 * g + 2 <=>
                       j < 8 * g \/ j = 8 * g \/ j = 8 * g + 1`] THEN
  ASM_REWRITE_TAC[TAUT `p \/ q ==> r <=> (p ==> r) /\ (q ==> r)`] THEN
  REWRITE_TAC[FORALL_AND_THM; FORALL_UNWIND_THM2] THEN
  REWRITE_TAC[ARITH_RULE `16 * (8 * g + b) = 128 * g + 16 * b`] THEN
  REWRITE_TAC[ARITH_RULE `16 * 8 * g = 128 * g`] THEN
  CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM WORD_ADD; WORD_ADD_0] THEN
  ONCE_REWRITE_TAC[WORD_BITWISE_RULE
    `word_xor (word_xor (inb:int128) ch) rk14 = word_xor ch (word_xor rk14 inb)`] THEN
  REWRITE_TAC[XOR_AES256_CIPHER_RECONSTRUCT] THEN
  ASM_REWRITE_TAC[MAP; WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
  REWRITE_TAC[aes_ctr_block; GSYM ADD_ASSOC] THEN
  CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; GSYM ADD_ASSOC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[ARITH_RULE `8 * g + c = c + 8 * g`] THEN
  REWRITE_TAC[ADD_ASSOC] THEN
  REWRITE_TAC[ARITH_RULE `1 + c = c + 1`; ARITH_RULE `2 + c = c + 2`;
              ARITH_RULE `3 + c = c + 3`; ARITH_RULE `4 + c = c + 4`;
              ARITH_RULE `5 + c = c + 5`; ARITH_RULE `6 + c = c + 6`;
              ARITH_RULE `7 + c = c + 7`] THEN
  CONV_TAC WORD_BITWISE_RULE);;

(* ========================================================================= *)
(* FAST1_TAIL - the fast1 (nb=1, 16B) dedicated tail leg. Clone of           *)
(* FAST2_TAIL for ONE block (keystream Q0 only; ext+rev64 tag format so NO   *)
(* Q25 index).  Entry 0x187c (fast1 tail-setup start, ldr q8; ext v16; mov   *)
(* v29; eor3 v9), then the single-block drain.  Q30 enters as ctr(c+nb)      *)
(* (= 8g+c+1), built directly by the small_1 body.  Q19 folds at s24.        *)
(* ========================================================================= *)
let AES256_GCM_ENC_ALT_FAST1_TAIL = prove
 (`!in_p out_p tag_p ivec_p htable_p mod_p
     tag0 nonce c rk inblock nb g pc.
    nb = 8 * g + 1 /\
    val in_p + 16 * nb < 2 EXP 63 /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
      [(word pc, LENGTH aes256_gcm_enc_alt_tmc);
       (in_p, 16 * nb); (htable_p, 192); (mod_p, 8)] /\
    PAIRWISE nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) aes256_gcm_enc_alt_tmc /\
           read PC s = word (pc + 0x187c) /\
           read X0 s = word_add in_p (word (128 * g)) /\
           read X2 s = word_add out_p (word (128 * g)) /\
           read X3 s = tag_p /\
           read X9 s = word (16 * nb) /\
           read X6 s = htable_p /\
           read X10 s = mod_p /\
           read X16 s = ivec_p /\
           read Q12 s = word 0x000102030405060708090a0b0c0d0e0f /\
           read (memory :> bytes64 mod_p) s = word 0xc200000000000000 /\
           word_xor (read Q0 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * g + c)) rk) /\
           read Q19 s =
             nist_ghash (aes256_cipher (word 0) rk) tag0
                 (list_of_seq (nist_cipher_block aes256_cipher c nonce rk inblock) (8 * g)) /\
           read Q28 s = word_reversefields 8 (EL 14 rk) /\
           read Q30 s = word_reversefields 32 (ctr_block nonce (8 * g + c + 1)) /\
           read Q31 s = word 79228162514264337593543950336 /\
           htable_mem_8 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j) /\
           (!j. j < 8 * g
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block aes256_cipher c nonce rk (j)) (inblock j)))
      (\s. read PC s = word (pc + 0x1154) /\
           read X9 s = word (16 * nb) /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce (nb + c)) /\
           read (memory :> bytes128 tag_p) s =
             word_reversefields 8
               (nist_ghash (aes256_cipher (word 0) rk) tag0
                  (list_of_seq (nist_cipher_block aes256_cipher c nonce rk inblock) nb)) /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block aes256_cipher c nonce rk (j)) (inblock j)))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * nb);
                  memory :> bytes(tag_p, 16);
                  memory :> bytes(ivec_p, 16)])`,
  REWRITE_TAC[htable_mem_8; htable_mem_4; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REWRITE_CONV[fst AES256_GCM_ENC_ALT_EXEC]
    `LENGTH aes256_gcm_enc_alt_tmc`]) THEN
  SUBGOAL_THEN
   `read (memory :> bytes128 (word_add in_p (word (128 * g)))) s0 =
    inblock (8 * g)`
  ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `128 * g = 16 * (8 * g)`] THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  RULE_ASSUM_TAC(fun th -> try MATCH_MP KS_SOLVE th with Failure _ -> th) THEN
  MAP_EVERY NSTEP_GP (1--24) THEN
  fold_q19_at `read Q19 s24 : int128` `8 * g + 1` TAIL_Q19_FOLD_REM1 THEN
  DISCARD_REGS ["Q17";"Q18";"Q20";"Q21";"Q22";"Q23";"Q24";"Q25";"Q26";"Q29";"Q16";"Q8";"Q9";"Q10";"Q11";"Q13";"Q14";"Q15"] THEN
  MAP_EVERY NSTEP_GP (25--27) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[IVEC_STORE_REV32] THEN
    REWRITE_TAC[WORD_SUBWORD_REVERSEFIELDS_32; WORD_SUBWORD_CTR_BLOCK_32] THEN
    REWRITE_TAC[WORD_RULE `word_sub (x:int32) (word 0) = x`] THEN
    REWRITE_TAC[WORD_RULE
      `word_sub (word_sub (word_sub (word_sub (word_sub (word_sub (word_sub
        (word (8 * g + 10):int32) (word 1)) (word 1)) (word 1)) (word 1))
        (word 1)) (word 1)) (word 1) = word (8 * g + 3)`] THEN
    REWRITE_TAC[CTR_BLOCK_RECONSTRUCT_REV8] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[TAG_STORE_REV64] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    UNDISCH_TAC `nb = 8 * g + 1` THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `j < 8 * g + 1 <=>
                       j < 8 * g \/ j = 8 * g`] THEN
  ASM_REWRITE_TAC[TAUT `p \/ q ==> r <=> (p ==> r) /\ (q ==> r)`] THEN
  REWRITE_TAC[FORALL_AND_THM; FORALL_UNWIND_THM2] THEN
  REWRITE_TAC[ARITH_RULE `16 * (8 * g + b) = 128 * g + 16 * b`] THEN
  REWRITE_TAC[ARITH_RULE `16 * 8 * g = 128 * g`] THEN
  CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM WORD_ADD; WORD_ADD_0] THEN
  ONCE_REWRITE_TAC[WORD_BITWISE_RULE
    `word_xor (word_xor (inb:int128) ch) rk14 = word_xor ch (word_xor rk14 inb)`] THEN
  REWRITE_TAC[XOR_AES256_CIPHER_RECONSTRUCT] THEN
  ASM_REWRITE_TAC[MAP; WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
  REWRITE_TAC[aes_ctr_block; GSYM ADD_ASSOC] THEN
  CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; GSYM ADD_ASSOC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[ARITH_RULE `8 * g + c = c + 8 * g`] THEN
  REWRITE_TAC[ADD_ASSOC] THEN
  REWRITE_TAC[ARITH_RULE `1 + c = c + 1`; ARITH_RULE `2 + c = c + 2`;
              ARITH_RULE `3 + c = c + 3`; ARITH_RULE `4 + c = c + 4`;
              ARITH_RULE `5 + c = c + 5`; ARITH_RULE `6 + c = c + 6`;
              ARITH_RULE `7 + c = c + 7`] THEN
  CONV_TAC WORD_BITWISE_RULE);;



(* - TAIL CASCADE arm rem=3 (nblocks = 8*g+3).                               *)
(* 3-block batched Q19 fold; Q27 pinned (dead-lane partial write). 5         *)
(* `sub v30` decrements roll ctr 8g+c+8 -> 8g+c+3 = nb+c.                    *)
(* ========================================================================= *)

let TAIL_X5_REM3 = prove
 (`!(in_p:int64) g.
     word_sub (word_add in_p (word (16 * (8 * g + 3))))
              (word_add in_p (word (128 * g))) = word 48:int64`,
  REPEAT STRIP_TAC THEN CONV_TAC WORD_RULE);;

let TAIL_Q19_FOLD_REM3 =
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
    [WORD_BITWISE_RULE
      `word_xor (word_xor (i:int128) (word_xor a r)) r = word_xor i a`] THEN
  REWRITE_TAC[RECON_GRR] THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV WORD_REDUCE_CONV)) THEN
  REWRITE_TAC[WORD_XOR_0] THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
    [WORD_BITWISE_RULE `word_xor (word 0:int128) x = x`] THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
    [WORD_BITWISE_RULE
      `word_xor (i:int128) (word_reversefields 8 a) =
       word_xor (word_reversefields 8 a) i`] THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
    [ARITH_RULE `8 * g + c + 1 = (8 * g + 1) + c`;
     ARITH_RULE `8 * g + c + 2 = (8 * g + 2) + c`] THEN
  REWRITE_TAC[GSYM aes_ctr_block] THEN
  REWRITE_TAC[GSYM cipher_block] THEN REWRITE_TAC[CIPHER_BLOCK_NIST] THEN
  REWRITE_TAC[WORD_SUBWORD_REVERSEFIELDS] THEN
  SIMP_TAC[WORD_JOIN_COMBINE_LEMMA; ARITH] THEN
  REWRITE_TAC[WORD_SUBWORD_XOR] THEN REWRITE_TAC[WORD_SUBWORD_BYTESWAP128] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[WORD_SUBWORD_XOR] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[GSYM WORD_SUBWORD_XOR] THEN
  REWRITE_TAC[GHASH_REDUCE_RAW_XOR] THEN
  REWRITE_TAC[KARATSUBA_IS_DOT_HW] THEN
  REWRITE_TAC[KDOT_B0] THEN
  REWRITE_TAC[NIST_GHASH_IS_POLYVAL] THEN
  REWRITE_TAC[ARITH_RULE `8 * g + 3 = SUC(SUC(SUC(8 * g)))`;
              ARITH_RULE `3 + 8 * g = SUC(SUC(SUC(8 * g)))`] THEN
  REWRITE_TAC[list_of_seq] THEN REWRITE_TAC[GSYM APPEND_ASSOC] THEN
  REWRITE_TAC[APPEND] THEN
  REWRITE_TAC[GHASH_ACC_APPEND] THEN
  REWRITE_TAC[ADD1; GSYM ADD_ASSOC] THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
  MP_TAC(ISPECL
    [`ghash_twist (aes256_cipher (word 0) rk)`;
     `[nist_cipher_block aes256_cipher c nonce rk inblock (8*g+1);
       nist_cipher_block aes256_cipher c nonce rk inblock (8*g+2)]:(int128)list`;
     `ghash_polyval_acc (ghash_twist (aes256_cipher (word 0) rk)) tag0
        (list_of_seq (nist_cipher_block aes256_cipher c nonce rk inblock) (8*g))`;
     `nist_cipher_block aes256_cipher c nonce rk inblock (8*g)`]
    GHASH_POLYVAL_ACC_BATCHED) THEN
  REWRITE_TAC[LENGTH; ghash_wide] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[ADD_0] THEN
  REWRITE_TAC[polyval_dot] THEN
  REWRITE_TAC[GSYM PROP3_XOR] THEN
  REWRITE_TAC[NCB_ETA] THEN
  REWRITE_TAC[ARITH_RULE `1 + 8 * g = 8 * g + 1`; ARITH_RULE `2 + 8 * g = 8 * g + 2`] THEN
  AP_TERM_TAC THEN CONV_TAC WORD_BITWISE_RULE;;

let FOLD_Q19_REM3 : tactic =
  fold_q19_at `read Q19 s107 : int128` `8 * g + 3` TAIL_Q19_FOLD_REM3;;

let AES256_GCM_ENC_ALT_TAIL_REM3 = prove
 (`!q27_init in_p out_p tag_p ivec_p key_p htable_p mod_p end_p
     tag0 nonce c rk inblock nb g pc.
    nb = 8 * g + 3 /\
    end_p = word_add in_p (word (128 * g)) /\
    val in_p + 16 * nb < 2 EXP 63 /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
      [(word pc, LENGTH aes256_gcm_enc_alt_tmc);
       (in_p, 16 * nb); (key_p, 240); (htable_p, 192); (mod_p, 8)] /\
    PAIRWISE nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) aes256_gcm_enc_alt_tmc /\
           read PC s = word (pc + 0xee0) /\
           read X0 s = word_add in_p (word (128 * g)) /\
           read X2 s = word_add out_p (word (128 * g)) /\
           read X3 s = tag_p /\
           read X9 s = word (16 * nb) /\
           read X4 s = word_add in_p (word (16 * nb)) /\
           read X16 s = ivec_p /\
           read X5 s = end_p /\
           read X6 s = htable_p /\
           read X10 s = mod_p /\
           read X11 s = key_p /\
           read (memory :> bytes64 mod_p) s = word 0xc200000000000000 /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce c) /\
           read Q27 s = q27_init /\
           read Q28 s = word_reversefields 8 (EL 14 rk) /\
           read Q30 s = word_reversefields 32 (ctr_block nonce (8 * g + c + 8)) /\
           read Q31 s = word 79228162514264337593543950336 /\
           read Q19 s =
             nist_ghash (aes256_cipher (word 0) rk) tag0
                 (list_of_seq (nist_cipher_block aes256_cipher c nonce rk inblock) (8 * g)) /\
           word_xor (read Q0 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + c)) rk) /\
           word_xor (read Q1 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + c + 1)) rk) /\
           word_xor (read Q2 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + c + 2)) rk) /\
           word_xor (read Q3 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + c + 3)) rk) /\
           word_xor (read Q4 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + c + 4)) rk) /\
           word_xor (read Q5 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + c + 5)) rk) /\
           word_xor (read Q6 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + c + 6)) rk) /\
           word_xor (read Q7 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + c + 7)) rk) /\
           htable_mem_8 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j) /\
           (!j. j < 8 * g
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block aes256_cipher c nonce rk (j)) (inblock j)))
      (\s. read PC s = word (pc + 0x1154) /\
           read X9 s = word (16 * nb) /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce (nb + c)) /\
           read (memory :> bytes128 tag_p) s =
             word_reversefields 8
               (nist_ghash (aes256_cipher (word 0) rk) tag0
                  (list_of_seq (nist_cipher_block aes256_cipher c nonce rk inblock) nb)) /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block aes256_cipher c nonce rk (j)) (inblock j)))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * nb);
                  memory :> bytes(tag_p, 16);
                  memory :> bytes(ivec_p, 16)])`,
  REWRITE_TAC[htable_mem_8; htable_mem_4; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REWRITE_CONV[fst AES256_GCM_ENC_ALT_EXEC]
    `LENGTH aes256_gcm_enc_alt_tmc`]) THEN
  SUBGOAL_THEN
   `    read (memory :> bytes128 (word_add in_p (word (128 * g)))) s0 =
    inblock (8 * g) /\
    read (memory :> bytes128 (word_add in_p (word (128 * g + 16)))) s0 =
    inblock (8 * g + 1) /\
    read (memory :> bytes128 (word_add in_p (word (128 * g + 32)))) s0 =
    inblock (8 * g + 2)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `128 * g = 16 * (8 * g)`;
      ARITH_RULE `128 * g + 16 = 16 * (8 * g + 1)`;
      ARITH_RULE `128 * g + 32 = 16 * (8 * g + 2)`] THEN
    REPEAT CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  RULE_ASSUM_TAC(fun th -> try MATCH_MP KS_SOLVE th with Failure _ -> th) THEN
  MAP_EVERY NSTEP_GP (1--9) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[TAIL_X5_REM3]) THEN
  MAP_EVERY NSTEP_GP (10--107) THEN
  FOLD_Q19_REM3 THEN
  DISCARD_DEAD_REDUCE_SCRATCH THEN
  MAP_EVERY NSTEP_GP (108--110) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[IVEC_STORE_REV32] THEN
    REWRITE_TAC[WORD_SUBWORD_REVERSEFIELDS_32; WORD_SUBWORD_CTR_BLOCK_32] THEN
    REWRITE_TAC[WORD_RULE `word_sub (x:int32) (word 0) = x`] THEN
    REWRITE_TAC[WORD_RULE
      `word_sub (word_sub (word_sub (word_sub (word_sub (word (8 * g + c + 8):int32) (word 1)) (word 1)) (word 1)) (word 1)) (word 1) = word (8 * g + c + 3)`] THEN
    REWRITE_TAC[CTR_BLOCK_RECONSTRUCT_REV8] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[TAG_STORE_REV64] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    UNDISCH_TAC `nb = 8 * g + 3` THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `j < 8 * g + 3 <=>
                       j < 8 * g \/ j = 8 * g \/ j = 8 * g + 1 \/ j = 8 * g + 2`] THEN
  ASM_REWRITE_TAC[TAUT `p \/ q ==> r <=> (p ==> r) /\ (q ==> r)`] THEN
  REWRITE_TAC[FORALL_AND_THM; FORALL_UNWIND_THM2] THEN
  REWRITE_TAC[ARITH_RULE `16 * (8 * g + b) = 128 * g + 16 * b`] THEN
  REWRITE_TAC[ARITH_RULE `16 * 8 * g = 128 * g`] THEN
  CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM WORD_ADD; WORD_ADD_0] THEN
  ONCE_REWRITE_TAC[WORD_BITWISE_RULE
    `word_xor (word_xor (inb:int128) ch) rk14 = word_xor ch (word_xor rk14 inb)`] THEN
  REWRITE_TAC[XOR_AES256_CIPHER_RECONSTRUCT] THEN
  ASM_REWRITE_TAC[MAP; WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
  REWRITE_TAC[aes_ctr_block; GSYM ADD_ASSOC] THEN
  CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; GSYM ADD_ASSOC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[ARITH_RULE `8 * g + c = c + 8 * g`] THEN
  REWRITE_TAC[ADD_ASSOC] THEN
  REWRITE_TAC[ARITH_RULE `1 + c = c + 1`; ARITH_RULE `2 + c = c + 2`;
              ARITH_RULE `3 + c = c + 3`; ARITH_RULE `4 + c = c + 4`;
              ARITH_RULE `5 + c = c + 5`; ARITH_RULE `6 + c = c + 6`;
              ARITH_RULE `7 + c = c + 7`] THEN
  CONV_TAC WORD_BITWISE_RULE);;


(* ========================================================================= *)
(* - TAIL CASCADE arm rem=4 (nblocks = 8*g+4), lands at 0x1328.              *)
(* 4-block batched Q19 fold; Q27 pinned (dead-lane partial write). 4         *)
(* `sub v30` decrements roll ctr 8g+c+8 -> 8g+c+4 = nb+c.                    *)
(* ========================================================================= *)

let TAIL_X5_REM4 = prove
 (`!(in_p:int64) g.
     word_sub (word_add in_p (word (16 * (8 * g + 4))))
              (word_add in_p (word (128 * g))) = word 64:int64`,
  REPEAT STRIP_TAC THEN CONV_TAC WORD_RULE);;

let TAIL_Q19_FOLD_REM4 =
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
    [WORD_BITWISE_RULE
      `word_xor (word_xor (i:int128) (word_xor a r)) r = word_xor i a`] THEN
  REWRITE_TAC[RECON_GRR] THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV WORD_REDUCE_CONV)) THEN
  REWRITE_TAC[WORD_XOR_0] THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
    [WORD_BITWISE_RULE `word_xor (word 0:int128) x = x`] THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
    [WORD_BITWISE_RULE
      `word_xor (i:int128) (word_reversefields 8 a) =
       word_xor (word_reversefields 8 a) i`] THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
    [ARITH_RULE `8 * g + c + 1 = (8 * g + 1) + c`;
     ARITH_RULE `8 * g + c + 2 = (8 * g + 2) + c`;
     ARITH_RULE `8 * g + c + 3 = (8 * g + 3) + c`] THEN
  REWRITE_TAC[GSYM aes_ctr_block] THEN
  REWRITE_TAC[GSYM cipher_block] THEN REWRITE_TAC[CIPHER_BLOCK_NIST] THEN
  REWRITE_TAC[WORD_SUBWORD_REVERSEFIELDS] THEN
  SIMP_TAC[WORD_JOIN_COMBINE_LEMMA; ARITH] THEN
  REWRITE_TAC[WORD_SUBWORD_XOR] THEN REWRITE_TAC[WORD_SUBWORD_BYTESWAP128] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[WORD_SUBWORD_XOR] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[GSYM WORD_SUBWORD_XOR] THEN
  REWRITE_TAC[GHASH_REDUCE_RAW_XOR] THEN
  REWRITE_TAC[KARATSUBA_IS_DOT_HW] THEN
  REWRITE_TAC[KDOT_B0] THEN
  REWRITE_TAC[NIST_GHASH_IS_POLYVAL] THEN
  REWRITE_TAC[ARITH_RULE `8 * g + 4 = SUC(SUC(SUC(SUC(8 * g))))`;
              ARITH_RULE `4 + 8 * g = SUC(SUC(SUC(SUC(8 * g))))`] THEN
  REWRITE_TAC[list_of_seq] THEN REWRITE_TAC[GSYM APPEND_ASSOC] THEN
  REWRITE_TAC[APPEND] THEN
  REWRITE_TAC[GHASH_ACC_APPEND] THEN
  REWRITE_TAC[ADD1; GSYM ADD_ASSOC] THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
  MP_TAC(ISPECL
    [`ghash_twist (aes256_cipher (word 0) rk)`;
     `[nist_cipher_block aes256_cipher c nonce rk inblock (8*g+1);
       nist_cipher_block aes256_cipher c nonce rk inblock (8*g+2);
       nist_cipher_block aes256_cipher c nonce rk inblock (8*g+3)]:(int128)list`;
     `ghash_polyval_acc (ghash_twist (aes256_cipher (word 0) rk)) tag0
        (list_of_seq (nist_cipher_block aes256_cipher c nonce rk inblock) (8*g))`;
     `nist_cipher_block aes256_cipher c nonce rk inblock (8*g)`]
    GHASH_POLYVAL_ACC_BATCHED) THEN
  REWRITE_TAC[LENGTH; ghash_wide] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[ADD_0] THEN
  REWRITE_TAC[polyval_dot] THEN
  REWRITE_TAC[GSYM PROP3_XOR] THEN
  REWRITE_TAC[NCB_ETA] THEN
  REWRITE_TAC[ARITH_RULE `1 + 8 * g = 8 * g + 1`; ARITH_RULE `2 + 8 * g = 8 * g + 2`; ARITH_RULE `3 + 8 * g = 8 * g + 3`] THEN
  AP_TERM_TAC THEN CONV_TAC WORD_BITWISE_RULE;;

let FOLD_Q19_REM4 : tactic =
  fold_q19_at `read Q19 s106 : int128` `8 * g + 4` TAIL_Q19_FOLD_REM4;;

let AES256_GCM_ENC_ALT_TAIL_REM4 = prove
 (`!q27_init in_p out_p tag_p ivec_p key_p htable_p mod_p end_p
     tag0 nonce c rk inblock nb g pc.
    nb = 8 * g + 4 /\
    end_p = word_add in_p (word (128 * g)) /\
    val in_p + 16 * nb < 2 EXP 63 /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
      [(word pc, LENGTH aes256_gcm_enc_alt_tmc);
       (in_p, 16 * nb); (key_p, 240); (htable_p, 192); (mod_p, 8)] /\
    PAIRWISE nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) aes256_gcm_enc_alt_tmc /\
           read PC s = word (pc + 0xee0) /\
           read X0 s = word_add in_p (word (128 * g)) /\
           read X2 s = word_add out_p (word (128 * g)) /\
           read X3 s = tag_p /\
           read X9 s = word (16 * nb) /\
           read X4 s = word_add in_p (word (16 * nb)) /\
           read X16 s = ivec_p /\
           read X5 s = end_p /\
           read X6 s = htable_p /\
           read X10 s = mod_p /\
           read X11 s = key_p /\
           read (memory :> bytes64 mod_p) s = word 0xc200000000000000 /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce c) /\
           read Q27 s = q27_init /\
           read Q28 s = word_reversefields 8 (EL 14 rk) /\
           read Q30 s = word_reversefields 32 (ctr_block nonce (8 * g + c + 8)) /\
           read Q31 s = word 79228162514264337593543950336 /\
           read Q19 s =
             nist_ghash (aes256_cipher (word 0) rk) tag0
                 (list_of_seq (nist_cipher_block aes256_cipher c nonce rk inblock) (8 * g)) /\
           word_xor (read Q0 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + c)) rk) /\
           word_xor (read Q1 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + c + 1)) rk) /\
           word_xor (read Q2 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + c + 2)) rk) /\
           word_xor (read Q3 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + c + 3)) rk) /\
           word_xor (read Q4 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + c + 4)) rk) /\
           word_xor (read Q5 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + c + 5)) rk) /\
           word_xor (read Q6 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + c + 6)) rk) /\
           word_xor (read Q7 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + c + 7)) rk) /\
           htable_mem_8 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j) /\
           (!j. j < 8 * g
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block aes256_cipher c nonce rk (j)) (inblock j)))
      (\s. read PC s = word (pc + 0x1154) /\
           read X9 s = word (16 * nb) /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce (nb + c)) /\
           read (memory :> bytes128 tag_p) s =
             word_reversefields 8
               (nist_ghash (aes256_cipher (word 0) rk) tag0
                  (list_of_seq (nist_cipher_block aes256_cipher c nonce rk inblock) nb)) /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block aes256_cipher c nonce rk (j)) (inblock j)))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * nb);
                  memory :> bytes(tag_p, 16);
                  memory :> bytes(ivec_p, 16)])`,
  REWRITE_TAC[htable_mem_8; htable_mem_4; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REWRITE_CONV[fst AES256_GCM_ENC_ALT_EXEC]
    `LENGTH aes256_gcm_enc_alt_tmc`]) THEN
  SUBGOAL_THEN
   `    read (memory :> bytes128 (word_add in_p (word (128 * g)))) s0 =
    inblock (8 * g) /\
    read (memory :> bytes128 (word_add in_p (word (128 * g + 16)))) s0 =
    inblock (8 * g + 1) /\
    read (memory :> bytes128 (word_add in_p (word (128 * g + 32)))) s0 =
    inblock (8 * g + 2) /\
    read (memory :> bytes128 (word_add in_p (word (128 * g + 48)))) s0 =
    inblock (8 * g + 3)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `128 * g = 16 * (8 * g)`;
      ARITH_RULE `128 * g + 16 = 16 * (8 * g + 1)`;
      ARITH_RULE `128 * g + 32 = 16 * (8 * g + 2)`;
      ARITH_RULE `128 * g + 48 = 16 * (8 * g + 3)`] THEN
    REPEAT CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  RULE_ASSUM_TAC(fun th -> try MATCH_MP KS_SOLVE th with Failure _ -> th) THEN
  MAP_EVERY NSTEP_GP (1--9) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[TAIL_X5_REM4]) THEN
  MAP_EVERY NSTEP_GP (10--106) THEN
  FOLD_Q19_REM4 THEN
  DISCARD_DEAD_REDUCE_SCRATCH THEN
  MAP_EVERY NSTEP_GP (107--110) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[IVEC_STORE_REV32] THEN
    REWRITE_TAC[WORD_SUBWORD_REVERSEFIELDS_32; WORD_SUBWORD_CTR_BLOCK_32] THEN
    REWRITE_TAC[WORD_RULE `word_sub (x:int32) (word 0) = x`] THEN
    REWRITE_TAC[WORD_RULE
      `word_sub (word_sub (word_sub (word_sub (word (8 * g + c + 8):int32) (word 1)) (word 1)) (word 1)) (word 1) = word (8 * g + c + 4)`] THEN
    REWRITE_TAC[CTR_BLOCK_RECONSTRUCT_REV8] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[TAG_STORE_REV64] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    UNDISCH_TAC `nb = 8 * g + 4` THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `j < 8 * g + 4 <=>
                       j < 8 * g \/ j = 8 * g \/ j = 8 * g + 1 \/ j = 8 * g + 2 \/ j = 8 * g + 3`] THEN
  ASM_REWRITE_TAC[TAUT `p \/ q ==> r <=> (p ==> r) /\ (q ==> r)`] THEN
  REWRITE_TAC[FORALL_AND_THM; FORALL_UNWIND_THM2] THEN
  REWRITE_TAC[ARITH_RULE `16 * (8 * g + b) = 128 * g + 16 * b`] THEN
  REWRITE_TAC[ARITH_RULE `16 * 8 * g = 128 * g`] THEN
  CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM WORD_ADD; WORD_ADD_0] THEN
  ONCE_REWRITE_TAC[WORD_BITWISE_RULE
    `word_xor (word_xor (inb:int128) ch) rk14 = word_xor ch (word_xor rk14 inb)`] THEN
  REWRITE_TAC[XOR_AES256_CIPHER_RECONSTRUCT] THEN
  ASM_REWRITE_TAC[MAP; WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
  REWRITE_TAC[aes_ctr_block; GSYM ADD_ASSOC] THEN
  CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; GSYM ADD_ASSOC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[ARITH_RULE `8 * g + c = c + 8 * g`] THEN
  REWRITE_TAC[ADD_ASSOC] THEN
  REWRITE_TAC[ARITH_RULE `1 + c = c + 1`; ARITH_RULE `2 + c = c + 2`;
              ARITH_RULE `3 + c = c + 3`; ARITH_RULE `4 + c = c + 4`;
              ARITH_RULE `5 + c = c + 5`; ARITH_RULE `6 + c = c + 6`;
              ARITH_RULE `7 + c = c + 7`] THEN
  CONV_TAC WORD_BITWISE_RULE);;

(* ========================================================================= *)
(* FAST4_TAIL - the fast4 (nb=4, 64B) dedicated tail leg. Entry              *)
(* pc+0x15ac (fast4 tail-setup start) with 4 keystreams (Q0..Q3) as          *)
(* preconditions (fresh entry so the tail-setup eor3 block0-ct write is      *)
(* tracked, exactly like FAST2_TAIL); the tail-setup (block0 PT load + eor3  *)
(* ct write + acc reset) runs into the eor3-fused 4-block drain, ending      *)
(* pc+0x1154.  Q30 enters as ctr(c+nb) (= 8g+c+4), built directly by the     *)
(* small_4 body, so the counter closer reuses TAIL_REM4's verbatim.  Q19     *)
(* folds at s67.                                                             *)
(* ========================================================================= *)

let FOLD_Q19_REM4_FAST4 : tactic =
  fold_q19_at `read Q19 s67 : int128` `8 * g + 4` TAIL_Q19_FOLD_REM4;;

let AES256_GCM_ENC_ALT_FAST4_TAIL = prove
 (`!in_p out_p tag_p ivec_p htable_p mod_p
     tag0 nonce c rk inblock nb g pc.
    nb = 8 * g + 4 /\
    val in_p + 16 * nb < 2 EXP 63 /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
      [(word pc, LENGTH aes256_gcm_enc_alt_tmc);
       (in_p, 16 * nb); (htable_p, 192); (mod_p, 8)] /\
    PAIRWISE nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) aes256_gcm_enc_alt_tmc /\
           read PC s = word (pc + 0x15ac) /\
           read X0 s = word_add in_p (word (128 * g)) /\
           read X2 s = word_add out_p (word (128 * g)) /\
           read X3 s = tag_p /\
           read X9 s = word (16 * nb) /\
           read X6 s = htable_p /\
           read X10 s = mod_p /\
           read X16 s = ivec_p /\
           read Q12 s = word 0x000102030405060708090a0b0c0d0e0f /\
           read (memory :> bytes64 mod_p) s = word 0xc200000000000000 /\
           word_xor (read Q0 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * g + c)) rk) /\
           word_xor (read Q1 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * g + c + 1)) rk) /\
           word_xor (read Q2 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * g + c + 2)) rk) /\
           word_xor (read Q3 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * g + c + 3)) rk) /\
           read Q19 s =
             nist_ghash (aes256_cipher (word 0) rk) tag0
                 (list_of_seq (nist_cipher_block aes256_cipher c nonce rk inblock) (8 * g)) /\
           read Q28 s = word_reversefields 8 (EL 14 rk) /\
           read Q30 s = word_reversefields 32 (ctr_block nonce (8 * g + c + 4)) /\
           read Q31 s = word 79228162514264337593543950336 /\
           htable_mem_8 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j) /\
           (!j. j < 8 * g
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block aes256_cipher c nonce rk (j)) (inblock j)))
      (\s. read PC s = word (pc + 0x1154) /\
           read X9 s = word (16 * nb) /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce (nb + c)) /\
           read (memory :> bytes128 tag_p) s =
             word_reversefields 8
               (nist_ghash (aes256_cipher (word 0) rk) tag0
                  (list_of_seq (nist_cipher_block aes256_cipher c nonce rk inblock) nb)) /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block aes256_cipher c nonce rk (j)) (inblock j)))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * nb);
                  memory :> bytes(tag_p, 16);
                  memory :> bytes(ivec_p, 16)])`,
  REWRITE_TAC[htable_mem_8; htable_mem_4; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REWRITE_CONV[fst AES256_GCM_ENC_ALT_EXEC]
    `LENGTH aes256_gcm_enc_alt_tmc`]) THEN
  SUBGOAL_THEN
   `    read (memory :> bytes128 (word_add in_p (word (128 * g)))) s0 =
    inblock (8 * g) /\
    read (memory :> bytes128 (word_add in_p (word (128 * g + 16)))) s0 =
    inblock (8 * g + 1) /\
    read (memory :> bytes128 (word_add in_p (word (128 * g + 32)))) s0 =
    inblock (8 * g + 2) /\
    read (memory :> bytes128 (word_add in_p (word (128 * g + 48)))) s0 =
    inblock (8 * g + 3)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `128 * g = 16 * (8 * g)`;
      ARITH_RULE `128 * g + 16 = 16 * (8 * g + 1)`;
      ARITH_RULE `128 * g + 32 = 16 * (8 * g + 2)`;
      ARITH_RULE `128 * g + 48 = 16 * (8 * g + 3)`] THEN
    REPEAT CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  RULE_ASSUM_TAC(fun th -> try MATCH_MP KS_SOLVE th with Failure _ -> th) THEN
  MAP_EVERY NSTEP_GP (1--67) THEN
  FOLD_Q19_REM4_FAST4 THEN
  (* KEEP Q12 (live tbl index) -> explicit discard = DISCARD_DEAD_REDUCE_SCRATCH minus Q12*)
  DISCARD_REGS ["Q17"; "Q18"; "Q20"; "Q21"; "Q22"; "Q23"; "Q24"; "Q25"; "Q26";
     "Q29"; "Q16"; "Q8"; "Q9"; "Q10"; "Q11"; "Q13"; "Q14"; "Q15"] THEN
  MAP_EVERY NSTEP_GP (68--70) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[IVEC_STORE_REV32] THEN
    REWRITE_TAC[WORD_SUBWORD_REVERSEFIELDS_32; WORD_SUBWORD_CTR_BLOCK_32] THEN
    REWRITE_TAC[WORD_RULE `word_sub (x:int32) (word 0) = x`] THEN
    REWRITE_TAC[WORD_RULE
      `word_sub (word_sub (word_sub (word_sub (word (8 * g + 10):int32) (word 1)) (word 1)) (word 1)) (word 1) = word (8 * g + 6)`] THEN
    REWRITE_TAC[CTR_BLOCK_RECONSTRUCT_REV8] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[TAG_STORE_REV64] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    UNDISCH_TAC `nb = 8 * g + 4` THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `j < 8 * g + 4 <=>
                       j < 8 * g \/ j = 8 * g \/ j = 8 * g + 1 \/ j = 8 * g + 2 \/ j = 8 * g + 3`] THEN
  ASM_REWRITE_TAC[TAUT `p \/ q ==> r <=> (p ==> r) /\ (q ==> r)`] THEN
  REWRITE_TAC[FORALL_AND_THM; FORALL_UNWIND_THM2] THEN
  REWRITE_TAC[ARITH_RULE `16 * (8 * g + b) = 128 * g + 16 * b`] THEN
  REWRITE_TAC[ARITH_RULE `16 * 8 * g = 128 * g`] THEN
  CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM WORD_ADD; WORD_ADD_0] THEN
  ONCE_REWRITE_TAC[WORD_BITWISE_RULE
    `word_xor (word_xor (inb:int128) ch) rk14 = word_xor ch (word_xor rk14 inb)`] THEN
  REWRITE_TAC[XOR_AES256_CIPHER_RECONSTRUCT] THEN
  ASM_REWRITE_TAC[MAP; WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
  REWRITE_TAC[aes_ctr_block; GSYM ADD_ASSOC] THEN
  CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; GSYM ADD_ASSOC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[ARITH_RULE `8 * g + c = c + 8 * g`] THEN
  REWRITE_TAC[ADD_ASSOC] THEN
  REWRITE_TAC[ARITH_RULE `1 + c = c + 1`; ARITH_RULE `2 + c = c + 2`;
              ARITH_RULE `3 + c = c + 3`; ARITH_RULE `4 + c = c + 4`;
              ARITH_RULE `5 + c = c + 5`; ARITH_RULE `6 + c = c + 6`;
              ARITH_RULE `7 + c = c + 7`] THEN
  CONV_TAC WORD_BITWISE_RULE);;



(* ========================================================================= *)
(* FAST3_TAIL - the fast3 (nb=3, 48B) dedicated tail leg. Clone of           *)
(* FAST4_TAIL for THREE blocks (keystreams Q0,Q1,Q2; ext+rev64 tag format so *)
(* NO Q12 index).  Entry 0x16ec (fast3 tail-setup start), then the           *)
(* eor3-fused 3-block drain.  Q30 enters as ctr(c+nb) (= 8g+c+3), built      *)
(* directly by the small_3 body.  Q19 folds at s50 (cascade REM3 fold).      *)
(* ========================================================================= *)
let AES256_GCM_ENC_ALT_FAST3_TAIL = prove
 (`!in_p out_p tag_p ivec_p htable_p mod_p
     tag0 nonce c rk inblock nb g pc.
    nb = 8 * g + 3 /\
    val in_p + 16 * nb < 2 EXP 63 /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
      [(word pc, LENGTH aes256_gcm_enc_alt_tmc);
       (in_p, 16 * nb); (htable_p, 192); (mod_p, 8)] /\
    PAIRWISE nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) aes256_gcm_enc_alt_tmc /\
           read PC s = word (pc + 0x16ec) /\
           read X0 s = word_add in_p (word (128 * g)) /\
           read X2 s = word_add out_p (word (128 * g)) /\
           read X3 s = tag_p /\
           read X9 s = word (16 * nb) /\
           read X6 s = htable_p /\
           read X10 s = mod_p /\
           read X16 s = ivec_p /\
           read Q12 s = word 0x000102030405060708090a0b0c0d0e0f /\
           read (memory :> bytes64 mod_p) s = word 0xc200000000000000 /\
           word_xor (read Q0 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * g + c)) rk) /\
           word_xor (read Q1 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * g + c + 1)) rk) /\
           word_xor (read Q2 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * g + c + 2)) rk) /\
           read Q19 s =
             nist_ghash (aes256_cipher (word 0) rk) tag0
                 (list_of_seq (nist_cipher_block aes256_cipher c nonce rk inblock) (8 * g)) /\
           read Q28 s = word_reversefields 8 (EL 14 rk) /\
           read Q30 s = word_reversefields 32 (ctr_block nonce (8 * g + c + 3)) /\
           read Q31 s = word 79228162514264337593543950336 /\
           htable_mem_8 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j) /\
           (!j. j < 8 * g
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block aes256_cipher c nonce rk (j)) (inblock j)))
      (\s. read PC s = word (pc + 0x1154) /\
           read X9 s = word (16 * nb) /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce (nb + c)) /\
           read (memory :> bytes128 tag_p) s =
             word_reversefields 8
               (nist_ghash (aes256_cipher (word 0) rk) tag0
                  (list_of_seq (nist_cipher_block aes256_cipher c nonce rk inblock) nb)) /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block aes256_cipher c nonce rk (j)) (inblock j)))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * nb);
                  memory :> bytes(tag_p, 16);
                  memory :> bytes(ivec_p, 16)])`,
  REWRITE_TAC[htable_mem_8; htable_mem_4; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REWRITE_CONV[fst AES256_GCM_ENC_ALT_EXEC]
    `LENGTH aes256_gcm_enc_alt_tmc`]) THEN
  SUBGOAL_THEN
   `    read (memory :> bytes128 (word_add in_p (word (128 * g)))) s0 =
    inblock (8 * g) /\
    read (memory :> bytes128 (word_add in_p (word (128 * g + 16)))) s0 =
    inblock (8 * g + 1) /\
    read (memory :> bytes128 (word_add in_p (word (128 * g + 32)))) s0 =
    inblock (8 * g + 2)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `128 * g = 16 * (8 * g)`;
      ARITH_RULE `128 * g + 16 = 16 * (8 * g + 1)`;
      ARITH_RULE `128 * g + 32 = 16 * (8 * g + 2)`] THEN
    REPEAT CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  RULE_ASSUM_TAC(fun th -> try MATCH_MP KS_SOLVE th with Failure _ -> th) THEN
  MAP_EVERY NSTEP_GP (1--50) THEN
  fold_q19_at `read Q19 s50 : int128` `8 * g + 3` TAIL_Q19_FOLD_REM3 THEN
  DISCARD_REGS ["Q17"; "Q18"; "Q20"; "Q21"; "Q22"; "Q23"; "Q24"; "Q25"; "Q26";
     "Q29"; "Q16"; "Q8"; "Q9"; "Q10"; "Q11"; "Q13"; "Q14"; "Q15";
     "Q3"; "Q4"; "Q5"] THEN
  MAP_EVERY NSTEP_GP (51--53) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[IVEC_STORE_REV32] THEN
    REWRITE_TAC[WORD_SUBWORD_REVERSEFIELDS_32; WORD_SUBWORD_CTR_BLOCK_32] THEN
    REWRITE_TAC[WORD_RULE `word_sub (x:int32) (word 0) = x`] THEN
    REWRITE_TAC[WORD_RULE
      `word_sub (word_sub (word_sub (word_sub (word_sub
        (word (8 * g + 10):int32) (word 1)) (word 1)) (word 1)) (word 1))
        (word 1) = word (8 * g + 5)`] THEN
    REWRITE_TAC[CTR_BLOCK_RECONSTRUCT_REV8] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[TAG_STORE_REV64] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    UNDISCH_TAC `nb = 8 * g + 3` THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `j < 8 * g + 3 <=>
                       j < 8 * g \/ j = 8 * g \/ j = 8 * g + 1 \/ j = 8 * g + 2`] THEN
  ASM_REWRITE_TAC[TAUT `p \/ q ==> r <=> (p ==> r) /\ (q ==> r)`] THEN
  REWRITE_TAC[FORALL_AND_THM; FORALL_UNWIND_THM2] THEN
  REWRITE_TAC[ARITH_RULE `16 * (8 * g + b) = 128 * g + 16 * b`] THEN
  REWRITE_TAC[ARITH_RULE `16 * 8 * g = 128 * g`] THEN
  CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM WORD_ADD; WORD_ADD_0] THEN
  ONCE_REWRITE_TAC[WORD_BITWISE_RULE
    `word_xor (word_xor (inb:int128) ch) rk14 = word_xor ch (word_xor rk14 inb)`] THEN
  REWRITE_TAC[XOR_AES256_CIPHER_RECONSTRUCT] THEN
  ASM_REWRITE_TAC[MAP; WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
  REWRITE_TAC[aes_ctr_block; GSYM ADD_ASSOC] THEN
  CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; GSYM ADD_ASSOC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[ARITH_RULE `8 * g + c = c + 8 * g`] THEN
  REWRITE_TAC[ADD_ASSOC] THEN
  REWRITE_TAC[ARITH_RULE `1 + c = c + 1`; ARITH_RULE `2 + c = c + 2`;
              ARITH_RULE `3 + c = c + 3`; ARITH_RULE `4 + c = c + 4`;
              ARITH_RULE `5 + c = c + 5`; ARITH_RULE `6 + c = c + 6`;
              ARITH_RULE `7 + c = c + 7`] THEN
  CONV_TAC WORD_BITWISE_RULE);;


(* ========================================================================= *)
(* - TAIL CASCADE arm rem=5 (nblocks = 8*g+5), lands at 0x1034.              *)
(* 5-block batched Q19 fold; Q27 pinned (dead-lane partial write). 3         *)
(* `sub v30` decrements roll ctr 8g+c+8 -> 8g+c+5 = nb+c.                    *)
(* ========================================================================= *)

let TAIL_X5_REM5 = prove
 (`!(in_p:int64) g.
     word_sub (word_add in_p (word (16 * (8 * g + 5))))
              (word_add in_p (word (128 * g))) = word 80:int64`,
  REPEAT STRIP_TAC THEN CONV_TAC WORD_RULE);;

let TAIL_Q19_FOLD_REM5 =
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
    [WORD_BITWISE_RULE
      `word_xor (word_xor (i:int128) (word_xor a r)) r = word_xor i a`] THEN
  REWRITE_TAC[RECON_GRR] THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV WORD_REDUCE_CONV)) THEN
  REWRITE_TAC[WORD_XOR_0] THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
    [WORD_BITWISE_RULE `word_xor (word 0:int128) x = x`] THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
    [WORD_BITWISE_RULE
      `word_xor (i:int128) (word_reversefields 8 a) =
       word_xor (word_reversefields 8 a) i`] THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
    [ARITH_RULE `8 * g + c + 1 = (8 * g + 1) + c`;
     ARITH_RULE `8 * g + c + 2 = (8 * g + 2) + c`;
     ARITH_RULE `8 * g + c + 3 = (8 * g + 3) + c`;
     ARITH_RULE `8 * g + c + 4 = (8 * g + 4) + c`] THEN
  REWRITE_TAC[GSYM aes_ctr_block] THEN
  REWRITE_TAC[GSYM cipher_block] THEN REWRITE_TAC[CIPHER_BLOCK_NIST] THEN
  REWRITE_TAC[WORD_SUBWORD_REVERSEFIELDS] THEN
  SIMP_TAC[WORD_JOIN_COMBINE_LEMMA; ARITH] THEN
  REWRITE_TAC[WORD_SUBWORD_XOR] THEN REWRITE_TAC[WORD_SUBWORD_BYTESWAP128] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[WORD_SUBWORD_XOR] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[GSYM WORD_SUBWORD_XOR] THEN
  REWRITE_TAC[GHASH_REDUCE_RAW_XOR] THEN
  REWRITE_TAC[KARATSUBA_IS_DOT_HW] THEN
  REWRITE_TAC[KDOT_B0] THEN
  REWRITE_TAC[NIST_GHASH_IS_POLYVAL] THEN
  REWRITE_TAC[ARITH_RULE `8 * g + 5 = SUC(SUC(SUC(SUC(SUC(8 * g)))))`;
              ARITH_RULE `5 + 8 * g = SUC(SUC(SUC(SUC(SUC(8 * g)))))`] THEN
  REWRITE_TAC[list_of_seq] THEN REWRITE_TAC[GSYM APPEND_ASSOC] THEN
  REWRITE_TAC[APPEND] THEN
  REWRITE_TAC[GHASH_ACC_APPEND] THEN
  REWRITE_TAC[ADD1; GSYM ADD_ASSOC] THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
  MP_TAC(ISPECL
    [`ghash_twist (aes256_cipher (word 0) rk)`;
     `[nist_cipher_block aes256_cipher c nonce rk inblock (8*g+1);
       nist_cipher_block aes256_cipher c nonce rk inblock (8*g+2);
       nist_cipher_block aes256_cipher c nonce rk inblock (8*g+3);
       nist_cipher_block aes256_cipher c nonce rk inblock (8*g+4)]:(int128)list`;
     `ghash_polyval_acc (ghash_twist (aes256_cipher (word 0) rk)) tag0
        (list_of_seq (nist_cipher_block aes256_cipher c nonce rk inblock) (8*g))`;
     `nist_cipher_block aes256_cipher c nonce rk inblock (8*g)`]
    GHASH_POLYVAL_ACC_BATCHED) THEN
  REWRITE_TAC[LENGTH; ghash_wide] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[ADD_0] THEN
  REWRITE_TAC[polyval_dot] THEN
  REWRITE_TAC[GSYM PROP3_XOR] THEN
  REWRITE_TAC[NCB_ETA] THEN
  REWRITE_TAC[ARITH_RULE `1 + 8 * g = 8 * g + 1`; ARITH_RULE `2 + 8 * g = 8 * g + 2`; ARITH_RULE `3 + 8 * g = 8 * g + 3`; ARITH_RULE `4 + 8 * g = 8 * g + 4`] THEN
  AP_TERM_TAC THEN CONV_TAC WORD_BITWISE_RULE;;

let FOLD_Q19_REM5 : tactic =
  (* rem5 now finishes on the eor3-fused rem4_drain (mt3->rem4_drain redirect);
     fold state s126->s115 (drain entry step 57 + 58 to the MODULO low-fold @0x1410). *)
  fold_q19_at `read Q19 s115 : int128` `8 * g + 5` TAIL_Q19_FOLD_REM5;;

let AES256_GCM_ENC_ALT_TAIL_REM5 = prove
 (`!q27_init in_p out_p tag_p ivec_p key_p htable_p mod_p end_p
     tag0 nonce c rk inblock nb g pc.
    nb = 8 * g + 5 /\
    end_p = word_add in_p (word (128 * g)) /\
    val in_p + 16 * nb < 2 EXP 63 /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
      [(word pc, LENGTH aes256_gcm_enc_alt_tmc);
       (in_p, 16 * nb); (key_p, 240); (htable_p, 192); (mod_p, 8)] /\
    PAIRWISE nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) aes256_gcm_enc_alt_tmc /\
           read PC s = word (pc + 0xee0) /\
           read X0 s = word_add in_p (word (128 * g)) /\
           read X2 s = word_add out_p (word (128 * g)) /\
           read X3 s = tag_p /\
           read X9 s = word (16 * nb) /\
           read X4 s = word_add in_p (word (16 * nb)) /\
           read X16 s = ivec_p /\
           read X5 s = end_p /\
           read X6 s = htable_p /\
           read X10 s = mod_p /\
           read X11 s = key_p /\
           read (memory :> bytes64 mod_p) s = word 0xc200000000000000 /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce c) /\
           read Q27 s = q27_init /\
           read Q28 s = word_reversefields 8 (EL 14 rk) /\
           read Q30 s = word_reversefields 32 (ctr_block nonce (8 * g + c + 8)) /\
           read Q31 s = word 79228162514264337593543950336 /\
           read Q19 s =
             nist_ghash (aes256_cipher (word 0) rk) tag0
                 (list_of_seq (nist_cipher_block aes256_cipher c nonce rk inblock) (8 * g)) /\
           word_xor (read Q0 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + c)) rk) /\
           word_xor (read Q1 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + c + 1)) rk) /\
           word_xor (read Q2 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + c + 2)) rk) /\
           word_xor (read Q3 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + c + 3)) rk) /\
           word_xor (read Q4 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + c + 4)) rk) /\
           word_xor (read Q5 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + c + 5)) rk) /\
           word_xor (read Q6 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + c + 6)) rk) /\
           word_xor (read Q7 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + c + 7)) rk) /\
           htable_mem_8 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j) /\
           (!j. j < 8 * g
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block aes256_cipher c nonce rk (j)) (inblock j)))
      (\s. read PC s = word (pc + 0x1154) /\
           read X9 s = word (16 * nb) /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce (nb + c)) /\
           read (memory :> bytes128 tag_p) s =
             word_reversefields 8
               (nist_ghash (aes256_cipher (word 0) rk) tag0
                  (list_of_seq (nist_cipher_block aes256_cipher c nonce rk inblock) nb)) /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block aes256_cipher c nonce rk (j)) (inblock j)))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * nb);
                  memory :> bytes(tag_p, 16);
                  memory :> bytes(ivec_p, 16)])`,
  REWRITE_TAC[htable_mem_8; htable_mem_4; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REWRITE_CONV[fst AES256_GCM_ENC_ALT_EXEC]
    `LENGTH aes256_gcm_enc_alt_tmc`]) THEN
  SUBGOAL_THEN
   `    read (memory :> bytes128 (word_add in_p (word (128 * g)))) s0 =
    inblock (8 * g) /\
    read (memory :> bytes128 (word_add in_p (word (128 * g + 16)))) s0 =
    inblock (8 * g + 1) /\
    read (memory :> bytes128 (word_add in_p (word (128 * g + 32)))) s0 =
    inblock (8 * g + 2) /\
    read (memory :> bytes128 (word_add in_p (word (128 * g + 48)))) s0 =
    inblock (8 * g + 3) /\
    read (memory :> bytes128 (word_add in_p (word (128 * g + 64)))) s0 =
    inblock (8 * g + 4)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `128 * g = 16 * (8 * g)`;
      ARITH_RULE `128 * g + 16 = 16 * (8 * g + 1)`;
      ARITH_RULE `128 * g + 32 = 16 * (8 * g + 2)`;
      ARITH_RULE `128 * g + 48 = 16 * (8 * g + 3)`;
      ARITH_RULE `128 * g + 64 = 16 * (8 * g + 4)`] THEN
    REPEAT CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  RULE_ASSUM_TAC(fun th -> try MATCH_MP KS_SOLVE th with Failure _ -> th) THEN
  MAP_EVERY NSTEP_GP (1--9) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[TAIL_X5_REM5]) THEN
  MAP_EVERY NSTEP_GP (10--115) THEN
  FOLD_Q19_REM5 THEN
  DISCARD_DEAD_REDUCE_SCRATCH THEN
  MAP_EVERY NSTEP_GP (116--119) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[IVEC_STORE_REV32] THEN
    REWRITE_TAC[WORD_SUBWORD_REVERSEFIELDS_32; WORD_SUBWORD_CTR_BLOCK_32] THEN
    REWRITE_TAC[WORD_RULE `word_sub (x:int32) (word 0) = x`] THEN
    REWRITE_TAC[WORD_RULE
      `word_sub (word_sub (word_sub (word (8 * g + c + 8):int32) (word 1)) (word 1)) (word 1) = word (8 * g + c + 5)`] THEN
    REWRITE_TAC[CTR_BLOCK_RECONSTRUCT_REV8] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[TAG_STORE_REV64] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    UNDISCH_TAC `nb = 8 * g + 5` THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `j < 8 * g + 5 <=>
                       j < 8 * g \/ j = 8 * g \/ j = 8 * g + 1 \/ j = 8 * g + 2 \/ j = 8 * g + 3 \/ j = 8 * g + 4`] THEN
  ASM_REWRITE_TAC[TAUT `p \/ q ==> r <=> (p ==> r) /\ (q ==> r)`] THEN
  REWRITE_TAC[FORALL_AND_THM; FORALL_UNWIND_THM2] THEN
  REWRITE_TAC[ARITH_RULE `16 * (8 * g + b) = 128 * g + 16 * b`] THEN
  REWRITE_TAC[ARITH_RULE `16 * 8 * g = 128 * g`] THEN
  CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM WORD_ADD; WORD_ADD_0] THEN
  ONCE_REWRITE_TAC[WORD_BITWISE_RULE
    `word_xor (word_xor (inb:int128) ch) rk14 = word_xor ch (word_xor rk14 inb)`] THEN
  REWRITE_TAC[XOR_AES256_CIPHER_RECONSTRUCT] THEN
  ASM_REWRITE_TAC[MAP; WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
  REWRITE_TAC[aes_ctr_block; GSYM ADD_ASSOC] THEN
  CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; GSYM ADD_ASSOC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[ARITH_RULE `8 * g + c = c + 8 * g`] THEN
  REWRITE_TAC[ADD_ASSOC] THEN
  REWRITE_TAC[ARITH_RULE `1 + c = c + 1`; ARITH_RULE `2 + c = c + 2`;
              ARITH_RULE `3 + c = c + 3`; ARITH_RULE `4 + c = c + 4`;
              ARITH_RULE `5 + c = c + 5`; ARITH_RULE `6 + c = c + 6`;
              ARITH_RULE `7 + c = c + 7`] THEN
  CONV_TAC WORD_BITWISE_RULE);;



(* ========================================================================= *)
(* - TAIL CASCADE arm rem=6 (nblocks = 8*g+6), lands at 0xff8.              *)
(* 6-block batched Q19 fold; Q27 pinned (dead-lane partial write). 2         *)
(* `sub v30` decrements roll ctr 8g+c+8 -> 8g+c+6 = nb+c.                    *)
(* ========================================================================= *)

let TAIL_X5_REM6 = prove
 (`!(in_p:int64) g.
     word_sub (word_add in_p (word (16 * (8 * g + 6))))
              (word_add in_p (word (128 * g))) = word 96:int64`,
  REPEAT STRIP_TAC THEN CONV_TAC WORD_RULE);;

let TAIL_Q19_FOLD_REM6 =
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
    [WORD_BITWISE_RULE
      `word_xor (word_xor (i:int128) (word_xor a r)) r = word_xor i a`] THEN
  REWRITE_TAC[RECON_GRR] THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV WORD_REDUCE_CONV)) THEN
  REWRITE_TAC[WORD_XOR_0] THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
    [WORD_BITWISE_RULE `word_xor (word 0:int128) x = x`] THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
    [WORD_BITWISE_RULE
      `word_xor (i:int128) (word_reversefields 8 a) =
       word_xor (word_reversefields 8 a) i`] THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
    [ARITH_RULE `8 * g + c + 1 = (8 * g + 1) + c`;
     ARITH_RULE `8 * g + c + 2 = (8 * g + 2) + c`;
     ARITH_RULE `8 * g + c + 3 = (8 * g + 3) + c`;
     ARITH_RULE `8 * g + c + 4 = (8 * g + 4) + c`;
     ARITH_RULE `8 * g + c + 5 = (8 * g + 5) + c`] THEN
  REWRITE_TAC[GSYM aes_ctr_block] THEN
  REWRITE_TAC[GSYM cipher_block] THEN REWRITE_TAC[CIPHER_BLOCK_NIST] THEN
  REWRITE_TAC[WORD_SUBWORD_REVERSEFIELDS] THEN
  SIMP_TAC[WORD_JOIN_COMBINE_LEMMA; ARITH] THEN
  REWRITE_TAC[WORD_SUBWORD_XOR] THEN REWRITE_TAC[WORD_SUBWORD_BYTESWAP128] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[WORD_SUBWORD_XOR] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[GSYM WORD_SUBWORD_XOR] THEN
  REWRITE_TAC[GHASH_REDUCE_RAW_XOR] THEN
  REWRITE_TAC[KARATSUBA_IS_DOT_HW] THEN
  REWRITE_TAC[KDOT_B0] THEN
  REWRITE_TAC[NIST_GHASH_IS_POLYVAL] THEN
  REWRITE_TAC[ARITH_RULE `8 * g + 6 = SUC(SUC(SUC(SUC(SUC(SUC(8 * g))))))`;
              ARITH_RULE `6 + 8 * g = SUC(SUC(SUC(SUC(SUC(SUC(8 * g))))))`] THEN
  REWRITE_TAC[list_of_seq] THEN REWRITE_TAC[GSYM APPEND_ASSOC] THEN
  REWRITE_TAC[APPEND] THEN
  REWRITE_TAC[GHASH_ACC_APPEND] THEN
  REWRITE_TAC[ADD1; GSYM ADD_ASSOC] THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
  MP_TAC(ISPECL
    [`ghash_twist (aes256_cipher (word 0) rk)`;
     `[nist_cipher_block aes256_cipher c nonce rk inblock (8*g+1);
       nist_cipher_block aes256_cipher c nonce rk inblock (8*g+2);
       nist_cipher_block aes256_cipher c nonce rk inblock (8*g+3);
       nist_cipher_block aes256_cipher c nonce rk inblock (8*g+4);
       nist_cipher_block aes256_cipher c nonce rk inblock (8*g+5)]:(int128)list`;
     `ghash_polyval_acc (ghash_twist (aes256_cipher (word 0) rk)) tag0
        (list_of_seq (nist_cipher_block aes256_cipher c nonce rk inblock) (8*g))`;
     `nist_cipher_block aes256_cipher c nonce rk inblock (8*g)`]
    GHASH_POLYVAL_ACC_BATCHED) THEN
  REWRITE_TAC[LENGTH; ghash_wide] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[ADD_0] THEN
  REWRITE_TAC[polyval_dot] THEN
  REWRITE_TAC[GSYM PROP3_XOR] THEN
  REWRITE_TAC[NCB_ETA] THEN
  REWRITE_TAC[ARITH_RULE `1 + 8 * g = 8 * g + 1`; ARITH_RULE `2 + 8 * g = 8 * g + 2`; ARITH_RULE `3 + 8 * g = 8 * g + 3`; ARITH_RULE `4 + 8 * g = 8 * g + 4`; ARITH_RULE `5 + 8 * g = 8 * g + 5`] THEN
  AP_TERM_TAC THEN CONV_TAC WORD_BITWISE_RULE;;

let FOLD_Q19_REM6 : tactic =
  (* rem6 -> eor3-fused rem4_drain; fold s134->s123 (drain entry 65 + 58).        *)
  fold_q19_at `read Q19 s123 : int128` `8 * g + 6` TAIL_Q19_FOLD_REM6;;

let AES256_GCM_ENC_ALT_TAIL_REM6 = prove
 (`!q27_init in_p out_p tag_p ivec_p key_p htable_p mod_p end_p
     tag0 nonce c rk inblock nb g pc.
    nb = 8 * g + 6 /\
    end_p = word_add in_p (word (128 * g)) /\
    val in_p + 16 * nb < 2 EXP 63 /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
      [(word pc, LENGTH aes256_gcm_enc_alt_tmc);
       (in_p, 16 * nb); (key_p, 240); (htable_p, 192); (mod_p, 8)] /\
    PAIRWISE nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) aes256_gcm_enc_alt_tmc /\
           read PC s = word (pc + 0xee0) /\
           read X0 s = word_add in_p (word (128 * g)) /\
           read X2 s = word_add out_p (word (128 * g)) /\
           read X3 s = tag_p /\
           read X9 s = word (16 * nb) /\
           read X4 s = word_add in_p (word (16 * nb)) /\
           read X16 s = ivec_p /\
           read X5 s = end_p /\
           read X6 s = htable_p /\
           read X10 s = mod_p /\
           read X11 s = key_p /\
           read (memory :> bytes64 mod_p) s = word 0xc200000000000000 /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce c) /\
           read Q27 s = q27_init /\
           read Q28 s = word_reversefields 8 (EL 14 rk) /\
           read Q30 s = word_reversefields 32 (ctr_block nonce (8 * g + c + 8)) /\
           read Q31 s = word 79228162514264337593543950336 /\
           read Q19 s =
             nist_ghash (aes256_cipher (word 0) rk) tag0
                 (list_of_seq (nist_cipher_block aes256_cipher c nonce rk inblock) (8 * g)) /\
           word_xor (read Q0 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + c)) rk) /\
           word_xor (read Q1 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + c + 1)) rk) /\
           word_xor (read Q2 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + c + 2)) rk) /\
           word_xor (read Q3 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + c + 3)) rk) /\
           word_xor (read Q4 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + c + 4)) rk) /\
           word_xor (read Q5 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + c + 5)) rk) /\
           word_xor (read Q6 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + c + 6)) rk) /\
           word_xor (read Q7 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + c + 7)) rk) /\
           htable_mem_8 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j) /\
           (!j. j < 8 * g
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block aes256_cipher c nonce rk (j)) (inblock j)))
      (\s. read PC s = word (pc + 0x1154) /\
           read X9 s = word (16 * nb) /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce (nb + c)) /\
           read (memory :> bytes128 tag_p) s =
             word_reversefields 8
               (nist_ghash (aes256_cipher (word 0) rk) tag0
                  (list_of_seq (nist_cipher_block aes256_cipher c nonce rk inblock) nb)) /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block aes256_cipher c nonce rk (j)) (inblock j)))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * nb);
                  memory :> bytes(tag_p, 16);
                  memory :> bytes(ivec_p, 16)])`,
  REWRITE_TAC[htable_mem_8; htable_mem_4; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REWRITE_CONV[fst AES256_GCM_ENC_ALT_EXEC]
    `LENGTH aes256_gcm_enc_alt_tmc`]) THEN
  SUBGOAL_THEN
   `    read (memory :> bytes128 (word_add in_p (word (128 * g)))) s0 =
    inblock (8 * g) /\
    read (memory :> bytes128 (word_add in_p (word (128 * g + 16)))) s0 =
    inblock (8 * g + 1) /\
    read (memory :> bytes128 (word_add in_p (word (128 * g + 32)))) s0 =
    inblock (8 * g + 2) /\
    read (memory :> bytes128 (word_add in_p (word (128 * g + 48)))) s0 =
    inblock (8 * g + 3) /\
    read (memory :> bytes128 (word_add in_p (word (128 * g + 64)))) s0 =
    inblock (8 * g + 4) /\
    read (memory :> bytes128 (word_add in_p (word (128 * g + 80)))) s0 =
    inblock (8 * g + 5)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `128 * g = 16 * (8 * g)`;
      ARITH_RULE `128 * g + 16 = 16 * (8 * g + 1)`;
      ARITH_RULE `128 * g + 32 = 16 * (8 * g + 2)`;
      ARITH_RULE `128 * g + 48 = 16 * (8 * g + 3)`;
      ARITH_RULE `128 * g + 64 = 16 * (8 * g + 4)`;
      ARITH_RULE `128 * g + 80 = 16 * (8 * g + 5)`] THEN
    REPEAT CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  RULE_ASSUM_TAC(fun th -> try MATCH_MP KS_SOLVE th with Failure _ -> th) THEN
  MAP_EVERY NSTEP_GP (1--9) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[TAIL_X5_REM6]) THEN
  MAP_EVERY NSTEP_GP (10--123) THEN
  FOLD_Q19_REM6 THEN
  DISCARD_DEAD_REDUCE_SCRATCH THEN
  MAP_EVERY NSTEP_GP (124--127) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[IVEC_STORE_REV32] THEN
    REWRITE_TAC[WORD_SUBWORD_REVERSEFIELDS_32; WORD_SUBWORD_CTR_BLOCK_32] THEN
    REWRITE_TAC[WORD_RULE `word_sub (x:int32) (word 0) = x`] THEN
    REWRITE_TAC[WORD_RULE
      `word_sub (word_sub (word (8 * g + c + 8):int32) (word 1)) (word 1) = word (8 * g + c + 6)`] THEN
    REWRITE_TAC[CTR_BLOCK_RECONSTRUCT_REV8] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[TAG_STORE_REV64] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    UNDISCH_TAC `nb = 8 * g + 6` THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `j < 8 * g + 6 <=>
                       j < 8 * g \/ j = 8 * g \/ j = 8 * g + 1 \/ j = 8 * g + 2 \/ j = 8 * g + 3 \/ j = 8 * g + 4 \/ j = 8 * g + 5`] THEN
  ASM_REWRITE_TAC[TAUT `p \/ q ==> r <=> (p ==> r) /\ (q ==> r)`] THEN
  REWRITE_TAC[FORALL_AND_THM; FORALL_UNWIND_THM2] THEN
  REWRITE_TAC[ARITH_RULE `16 * (8 * g + b) = 128 * g + 16 * b`] THEN
  REWRITE_TAC[ARITH_RULE `16 * 8 * g = 128 * g`] THEN
  CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM WORD_ADD; WORD_ADD_0] THEN
  ONCE_REWRITE_TAC[WORD_BITWISE_RULE
    `word_xor (word_xor (inb:int128) ch) rk14 = word_xor ch (word_xor rk14 inb)`] THEN
  REWRITE_TAC[XOR_AES256_CIPHER_RECONSTRUCT] THEN
  ASM_REWRITE_TAC[MAP; WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
  REWRITE_TAC[aes_ctr_block; GSYM ADD_ASSOC] THEN
  CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; GSYM ADD_ASSOC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[ARITH_RULE `8 * g + c = c + 8 * g`] THEN
  REWRITE_TAC[ADD_ASSOC] THEN
  REWRITE_TAC[ARITH_RULE `1 + c = c + 1`; ARITH_RULE `2 + c = c + 2`;
              ARITH_RULE `3 + c = c + 3`; ARITH_RULE `4 + c = c + 4`;
              ARITH_RULE `5 + c = c + 5`; ARITH_RULE `6 + c = c + 6`;
              ARITH_RULE `7 + c = c + 7`] THEN
  CONV_TAC WORD_BITWISE_RULE);;



(* ========================================================================= *)
(* - TAIL CASCADE arm rem=7 (nblocks = 8*g+7), lands at 0xfc0.               *)
(* 7-block batched Q19 fold; Q27 pinned (dead-lane partial write). 1         *)
(* `sub v30` decrements roll ctr 8g+c+8 -> 8g+c+7 = nb+c.                    *)
(* ========================================================================= *)

let TAIL_X5_REM7 = prove
 (`!(in_p:int64) g.
     word_sub (word_add in_p (word (16 * (8 * g + 7))))
              (word_add in_p (word (128 * g))) = word 112:int64`,
  REPEAT STRIP_TAC THEN CONV_TAC WORD_RULE);;

let TAIL_Q19_FOLD_REM7 =
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
    [WORD_BITWISE_RULE
      `word_xor (word_xor (i:int128) (word_xor a r)) r = word_xor i a`] THEN
  REWRITE_TAC[RECON_GRR] THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV WORD_REDUCE_CONV)) THEN
  REWRITE_TAC[WORD_XOR_0] THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
    [WORD_BITWISE_RULE `word_xor (word 0:int128) x = x`] THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
    [WORD_BITWISE_RULE
      `word_xor (i:int128) (word_reversefields 8 a) =
       word_xor (word_reversefields 8 a) i`] THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
    [ARITH_RULE `8 * g + c + 1 = (8 * g + 1) + c`;
     ARITH_RULE `8 * g + c + 2 = (8 * g + 2) + c`;
     ARITH_RULE `8 * g + c + 3 = (8 * g + 3) + c`;
     ARITH_RULE `8 * g + c + 4 = (8 * g + 4) + c`;
     ARITH_RULE `8 * g + c + 5 = (8 * g + 5) + c`;
     ARITH_RULE `8 * g + c + 6 = (8 * g + 6) + c`] THEN
  REWRITE_TAC[GSYM aes_ctr_block] THEN
  REWRITE_TAC[GSYM cipher_block] THEN REWRITE_TAC[CIPHER_BLOCK_NIST] THEN
  REWRITE_TAC[WORD_SUBWORD_REVERSEFIELDS] THEN
  SIMP_TAC[WORD_JOIN_COMBINE_LEMMA; ARITH] THEN
  REWRITE_TAC[WORD_SUBWORD_XOR] THEN REWRITE_TAC[WORD_SUBWORD_BYTESWAP128] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[WORD_SUBWORD_XOR] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[GSYM WORD_SUBWORD_XOR] THEN
  REWRITE_TAC[GHASH_REDUCE_RAW_XOR] THEN
  REWRITE_TAC[KARATSUBA_IS_DOT_HW] THEN
  REWRITE_TAC[KDOT_B0] THEN
  REWRITE_TAC[NIST_GHASH_IS_POLYVAL] THEN
  REWRITE_TAC[ARITH_RULE `8 * g + 7 = SUC(SUC(SUC(SUC(SUC(SUC(SUC(8 * g)))))))`;
              ARITH_RULE `7 + 8 * g = SUC(SUC(SUC(SUC(SUC(SUC(SUC(8 * g)))))))`] THEN
  REWRITE_TAC[list_of_seq] THEN REWRITE_TAC[GSYM APPEND_ASSOC] THEN
  REWRITE_TAC[APPEND] THEN
  REWRITE_TAC[GHASH_ACC_APPEND] THEN
  REWRITE_TAC[ADD1; GSYM ADD_ASSOC] THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
  MP_TAC(ISPECL
    [`ghash_twist (aes256_cipher (word 0) rk)`;
     `[nist_cipher_block aes256_cipher c nonce rk inblock (8*g+1);
       nist_cipher_block aes256_cipher c nonce rk inblock (8*g+2);
       nist_cipher_block aes256_cipher c nonce rk inblock (8*g+3);
       nist_cipher_block aes256_cipher c nonce rk inblock (8*g+4);
       nist_cipher_block aes256_cipher c nonce rk inblock (8*g+5);
       nist_cipher_block aes256_cipher c nonce rk inblock (8*g+6)]:(int128)list`;
     `ghash_polyval_acc (ghash_twist (aes256_cipher (word 0) rk)) tag0
        (list_of_seq (nist_cipher_block aes256_cipher c nonce rk inblock) (8*g))`;
     `nist_cipher_block aes256_cipher c nonce rk inblock (8*g)`]
    GHASH_POLYVAL_ACC_BATCHED) THEN
  REWRITE_TAC[LENGTH; ghash_wide] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[ADD_0] THEN
  REWRITE_TAC[polyval_dot] THEN
  REWRITE_TAC[GSYM PROP3_XOR] THEN
  REWRITE_TAC[NCB_ETA] THEN
  REWRITE_TAC[ARITH_RULE `1 + 8 * g = 8 * g + 1`; ARITH_RULE `2 + 8 * g = 8 * g + 2`; ARITH_RULE `3 + 8 * g = 8 * g + 3`; ARITH_RULE `4 + 8 * g = 8 * g + 4`; ARITH_RULE `5 + 8 * g = 8 * g + 5`; ARITH_RULE `6 + 8 * g = 8 * g + 6`] THEN
  AP_TERM_TAC THEN CONV_TAC WORD_BITWISE_RULE;;

let FOLD_Q19_REM7 : tactic =
  (* rem7 -> eor3-fused rem4_drain; fold s140->s129 (drain entry 71 + 58).        *)
  fold_q19_at `read Q19 s129 : int128` `8 * g + 7` TAIL_Q19_FOLD_REM7;;

let AES256_GCM_ENC_ALT_TAIL_REM7 = prove
 (`!q27_init in_p out_p tag_p ivec_p key_p htable_p mod_p end_p
     tag0 nonce c rk inblock nb g pc.
    nb = 8 * g + 7 /\
    end_p = word_add in_p (word (128 * g)) /\
    val in_p + 16 * nb < 2 EXP 63 /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
      [(word pc, LENGTH aes256_gcm_enc_alt_tmc);
       (in_p, 16 * nb); (key_p, 240); (htable_p, 192); (mod_p, 8)] /\
    PAIRWISE nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) aes256_gcm_enc_alt_tmc /\
           read PC s = word (pc + 0xee0) /\
           read X0 s = word_add in_p (word (128 * g)) /\
           read X2 s = word_add out_p (word (128 * g)) /\
           read X3 s = tag_p /\
           read X9 s = word (16 * nb) /\
           read X4 s = word_add in_p (word (16 * nb)) /\
           read X16 s = ivec_p /\
           read X5 s = end_p /\
           read X6 s = htable_p /\
           read X10 s = mod_p /\
           read X11 s = key_p /\
           read (memory :> bytes64 mod_p) s = word 0xc200000000000000 /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce c) /\
           read Q27 s = q27_init /\
           read Q28 s = word_reversefields 8 (EL 14 rk) /\
           read Q30 s = word_reversefields 32 (ctr_block nonce (8 * g + c + 8)) /\
           read Q31 s = word 79228162514264337593543950336 /\
           read Q19 s =
             nist_ghash (aes256_cipher (word 0) rk) tag0
                 (list_of_seq (nist_cipher_block aes256_cipher c nonce rk inblock) (8 * g)) /\
           word_xor (read Q0 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + c)) rk) /\
           word_xor (read Q1 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + c + 1)) rk) /\
           word_xor (read Q2 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + c + 2)) rk) /\
           word_xor (read Q3 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + c + 3)) rk) /\
           word_xor (read Q4 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + c + 4)) rk) /\
           word_xor (read Q5 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + c + 5)) rk) /\
           word_xor (read Q6 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + c + 6)) rk) /\
           word_xor (read Q7 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + c + 7)) rk) /\
           htable_mem_8 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j) /\
           (!j. j < 8 * g
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block aes256_cipher c nonce rk (j)) (inblock j)))
      (\s. read PC s = word (pc + 0x1154) /\
           read X9 s = word (16 * nb) /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce (nb + c)) /\
           read (memory :> bytes128 tag_p) s =
             word_reversefields 8
               (nist_ghash (aes256_cipher (word 0) rk) tag0
                  (list_of_seq (nist_cipher_block aes256_cipher c nonce rk inblock) nb)) /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block aes256_cipher c nonce rk (j)) (inblock j)))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * nb);
                  memory :> bytes(tag_p, 16);
                  memory :> bytes(ivec_p, 16)])`,
  REWRITE_TAC[htable_mem_8; htable_mem_4; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REWRITE_CONV[fst AES256_GCM_ENC_ALT_EXEC]
    `LENGTH aes256_gcm_enc_alt_tmc`]) THEN
  SUBGOAL_THEN
   `    read (memory :> bytes128 (word_add in_p (word (128 * g)))) s0 =
    inblock (8 * g) /\
    read (memory :> bytes128 (word_add in_p (word (128 * g + 16)))) s0 =
    inblock (8 * g + 1) /\
    read (memory :> bytes128 (word_add in_p (word (128 * g + 32)))) s0 =
    inblock (8 * g + 2) /\
    read (memory :> bytes128 (word_add in_p (word (128 * g + 48)))) s0 =
    inblock (8 * g + 3) /\
    read (memory :> bytes128 (word_add in_p (word (128 * g + 64)))) s0 =
    inblock (8 * g + 4) /\
    read (memory :> bytes128 (word_add in_p (word (128 * g + 80)))) s0 =
    inblock (8 * g + 5) /\
    read (memory :> bytes128 (word_add in_p (word (128 * g + 96)))) s0 =
    inblock (8 * g + 6)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `128 * g = 16 * (8 * g)`;
      ARITH_RULE `128 * g + 16 = 16 * (8 * g + 1)`;
      ARITH_RULE `128 * g + 32 = 16 * (8 * g + 2)`;
      ARITH_RULE `128 * g + 48 = 16 * (8 * g + 3)`;
      ARITH_RULE `128 * g + 64 = 16 * (8 * g + 4)`;
      ARITH_RULE `128 * g + 80 = 16 * (8 * g + 5)`;
      ARITH_RULE `128 * g + 96 = 16 * (8 * g + 6)`] THEN
    REPEAT CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  RULE_ASSUM_TAC(fun th -> try MATCH_MP KS_SOLVE th with Failure _ -> th) THEN
  MAP_EVERY NSTEP_GP (1--9) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[TAIL_X5_REM7]) THEN
  MAP_EVERY NSTEP_GP (10--129) THEN
  FOLD_Q19_REM7 THEN
  DISCARD_DEAD_REDUCE_SCRATCH THEN
  MAP_EVERY NSTEP_GP (130--133) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[IVEC_STORE_REV32] THEN
    REWRITE_TAC[WORD_SUBWORD_REVERSEFIELDS_32; WORD_SUBWORD_CTR_BLOCK_32] THEN
    REWRITE_TAC[WORD_RULE `word_sub (x:int32) (word 0) = x`] THEN
    REWRITE_TAC[WORD_RULE
      `word_sub (word (8 * g + c + 8):int32) (word 1) = word (8 * g + c + 7)`] THEN
    REWRITE_TAC[CTR_BLOCK_RECONSTRUCT_REV8] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[TAG_STORE_REV64] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    UNDISCH_TAC `nb = 8 * g + 7` THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `j < 8 * g + 7 <=>
                       j < 8 * g \/ j = 8 * g \/ j = 8 * g + 1 \/ j = 8 * g + 2 \/ j = 8 * g + 3 \/ j = 8 * g + 4 \/ j = 8 * g + 5 \/ j = 8 * g + 6`] THEN
  ASM_REWRITE_TAC[TAUT `p \/ q ==> r <=> (p ==> r) /\ (q ==> r)`] THEN
  REWRITE_TAC[FORALL_AND_THM; FORALL_UNWIND_THM2] THEN
  REWRITE_TAC[ARITH_RULE `16 * (8 * g + b) = 128 * g + 16 * b`] THEN
  REWRITE_TAC[ARITH_RULE `16 * 8 * g = 128 * g`] THEN
  CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM WORD_ADD; WORD_ADD_0] THEN
  ONCE_REWRITE_TAC[WORD_BITWISE_RULE
    `word_xor (word_xor (inb:int128) ch) rk14 = word_xor ch (word_xor rk14 inb)`] THEN
  REWRITE_TAC[XOR_AES256_CIPHER_RECONSTRUCT] THEN
  ASM_REWRITE_TAC[MAP; WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
  REWRITE_TAC[aes_ctr_block; GSYM ADD_ASSOC] THEN
  CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; GSYM ADD_ASSOC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[ARITH_RULE `8 * g + c = c + 8 * g`] THEN
  REWRITE_TAC[ADD_ASSOC] THEN
  REWRITE_TAC[ARITH_RULE `1 + c = c + 1`; ARITH_RULE `2 + c = c + 2`;
              ARITH_RULE `3 + c = c + 3`; ARITH_RULE `4 + c = c + 4`;
              ARITH_RULE `5 + c = c + 5`; ARITH_RULE `6 + c = c + 6`;
              ARITH_RULE `7 + c = c + 7`] THEN
  CONV_TAC WORD_BITWISE_RULE);;
(* ========================================================================= *)
(* - TAIL CASCADE arm rem=8 (nblocks = 8*g+8), g-GENERAL.                    *)
(*                                                                           *)
(* The older rem=8 arm was stated with `~(k=0) /\ 8*(k+2)=nb`, i.e. groups   *)
(* = k+1 >= 2 (nblocks >= 24).  But the reassembly needs the rem=8 arm at    *)
(* g=0 (nblocks=8) and g=1 (nblocks=16) too (both hit rem=8 in the           *)
(* (nblocks-1)DIV8 decomposition).  This is that body reparametrized         *)
(* k+1 -> g so it holds for ALL g>=0; the drive is g-independent (x5=128     *)
(* regardless of g), so the proof transfers verbatim modulo two fixes:       *)
(*     - the fold reindex `8*g+8=(8*g+6)+2` must be LHS-scoped (else it eats *)
(*       the RHS list-count 8*g+8 before its SUC^8 expansion);              *)
(*     - block 8*g+6's keystream ctr 8*g+8 collapses to `nb` during the      *)
(*       drive                                                               *)
(*       (the 8*g+8=nb hyp rewrites 8*g+8->nb L->R), so re-expand nb->8*g+8  *)
(*         in                                                                *)
(*       ONLY the Q19 fact before the fold (leaving the 8*g+8=nb hyp for the *)
(*       tag/out closers); and the first new out-block (j=8*g) leaves a      *)
(*       constant-lambda inblock slot closed by unfold+BETA+rev-rev+BITWISE. *)
(* ========================================================================= *)

(* ========================================================================= *)
(* Helpers for the g-general rem=8 tail arm, TAIL_REM8: the X5 end pointer   *)
(* and the Q19 fold, for any group count g.                                  *)
(* ========================================================================= *)
let TAIL_X5_128_G = prove
 (`!(in_p:int64) nb g.
     8 * g + 8 = nb
     ==> word_sub (word_add in_p (word (16 * nb)))
                  (word_add in_p (word (128 * g))) = word 128:int64`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN CONV_TAC WORD_RULE);;

let TAIL_Q19_FOLD_G =
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
    [WORD_BITWISE_RULE
      `word_xor (word_xor (i:int128) (word_xor a r)) r = word_xor i a`] THEN
  REWRITE_TAC[RECON_GRR] THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV WORD_REDUCE_CONV)) THEN
  REWRITE_TAC[WORD_XOR_0] THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
    [WORD_BITWISE_RULE `word_xor (word 0:int128) x = x`] THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
    [WORD_BITWISE_RULE
      `word_xor (i:int128) (word_reversefields 8 a) =
       word_xor (word_reversefields 8 a) i`] THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
    [ARITH_RULE `8 * g + c + 1 = (8 * g + 1) + c`;
     ARITH_RULE `8 * g + c + 2 = (8 * g + 2) + c`;
     ARITH_RULE `8 * g + c + 3 = (8 * g + 3) + c`;
     ARITH_RULE `8 * g + c + 4 = (8 * g + 4) + c`;
     ARITH_RULE `8 * g + c + 5 = (8 * g + 5) + c`;
     ARITH_RULE `8 * g + c + 6 = (8 * g + 6) + c`;
     ARITH_RULE `8 * g + c + 7 = (8 * g + 7) + c`] THEN
  REWRITE_TAC[GSYM aes_ctr_block] THEN
  REWRITE_TAC[GSYM cipher_block] THEN REWRITE_TAC[CIPHER_BLOCK_NIST] THEN
  REWRITE_TAC[WORD_SUBWORD_REVERSEFIELDS] THEN
  SIMP_TAC[WORD_JOIN_COMBINE_LEMMA; ARITH] THEN
  REWRITE_TAC[WORD_SUBWORD_XOR] THEN REWRITE_TAC[WORD_SUBWORD_BYTESWAP128] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[WORD_SUBWORD_XOR] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[GSYM WORD_SUBWORD_XOR] THEN
  REWRITE_TAC[GHASH_REDUCE_RAW_XOR] THEN
  REWRITE_TAC[KARATSUBA_IS_DOT_HW] THEN
  REWRITE_TAC[NIST_GHASH_IS_POLYVAL] THEN
  REWRITE_TAC[ARITH_RULE
    `8 * g + 8 = SUC(SUC(SUC(SUC(SUC(SUC(SUC(SUC(8 * g))))))))`;
              ARITH_RULE `8 + 8 * g = SUC(SUC(SUC(SUC(SUC(SUC(SUC(SUC(8 * g))))))))`] THEN
  REWRITE_TAC[list_of_seq] THEN REWRITE_TAC[GSYM APPEND_ASSOC] THEN
  REWRITE_TAC[APPEND] THEN
  REWRITE_TAC[GHASH_ACC_APPEND] THEN
  REWRITE_TAC[ADD1; GSYM ADD_ASSOC] THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
  MP_TAC(ISPECL
    [`ghash_twist (aes256_cipher (word 0) rk)`;
     `[nist_cipher_block aes256_cipher c nonce rk inblock (8 * g+1);
       nist_cipher_block aes256_cipher c nonce rk inblock (8 * g+2);
       nist_cipher_block aes256_cipher c nonce rk inblock (8 * g+3);
       nist_cipher_block aes256_cipher c nonce rk inblock (8 * g+4);
       nist_cipher_block aes256_cipher c nonce rk inblock (8 * g+5);
       nist_cipher_block aes256_cipher c nonce rk inblock (8 * g+6);
       nist_cipher_block aes256_cipher c nonce rk inblock (8 * g+7)]:(int128)list`;
     `ghash_polyval_acc (ghash_twist (aes256_cipher (word 0) rk)) tag0
        (list_of_seq (nist_cipher_block aes256_cipher c nonce rk inblock) (8 * g))`;
     `nist_cipher_block aes256_cipher c nonce rk inblock (8 * g)`]
    GHASH_POLYVAL_ACC_BATCHED) THEN
  REWRITE_TAC[LENGTH; ghash_wide] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[ADD_0] THEN
  REWRITE_TAC[polyval_dot] THEN
  REWRITE_TAC[GSYM PROP3_XOR] THEN
  REWRITE_TAC[NCB_ETA] THEN
  REWRITE_TAC[ARITH_RULE `1 + 8 * g = 8 * g + 1`; ARITH_RULE `2 + 8 * g = 8 * g + 2`; ARITH_RULE `3 + 8 * g = 8 * g + 3`; ARITH_RULE `4 + 8 * g = 8 * g + 4`; ARITH_RULE `5 + 8 * g = 8 * g + 5`; ARITH_RULE `6 + 8 * g = 8 * g + 6`; ARITH_RULE `7 + 8 * g = 8 * g + 7`] THEN
  AP_TERM_TAC THEN CONV_TAC WORD_BITWISE_RULE;;

let FOLD_Q19_S114_G : tactic =
  fold_q19_at `read Q19 s115 : int128` `8 * g + 8` TAIL_Q19_FOLD_G;;

let AES256_GCM_ENC_ALT_TAIL_REM8 = prove
 (`!q18_init q27_init in_p out_p tag_p ivec_p key_p htable_p mod_p end_p
     tag0 nonce c rk inblock nb g pc.
    8 * g + 8 = nb /\
    end_p = word_add in_p (word (128 * g)) /\
    val in_p + 16 * nb < 2 EXP 63 /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
      [(word pc, LENGTH aes256_gcm_enc_alt_tmc);
       (in_p, 16 * nb); (key_p, 240); (htable_p, 192); (mod_p, 8)] /\
    PAIRWISE nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) aes256_gcm_enc_alt_tmc /\
           read PC s = word (pc + 0xee0) /\
           read Q18 s = q18_init /\
           read Q27 s = q27_init /\
           read X0 s = word_add in_p (word (128 * g)) /\
           read X2 s = word_add out_p (word (128 * g)) /\
           read X3 s = tag_p /\
           read X9 s = word (16 * nb) /\
           read X4 s = word_add in_p (word (16 * nb)) /\
           read X16 s = ivec_p /\
           read X5 s = end_p /\
           read X6 s = htable_p /\
           read X10 s = mod_p /\
           read X11 s = key_p /\
           read (memory :> bytes64 mod_p) s = word 0xc200000000000000 /\
           wordlist_from_memory(key_p,15) s = MAP (word_reversefields 8) rk /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce c) /\
           read Q28 s = word_reversefields 8 (EL 14 rk) /\
           read Q30 s = word_reversefields 32 (ctr_block nonce (8 * g + c + 8)) /\
           read Q31 s = word 79228162514264337593543950336 /\
           read Q19 s =
             nist_ghash (aes256_cipher (word 0) rk) tag0
                 (list_of_seq (nist_cipher_block aes256_cipher c nonce rk inblock)
                              (8 * g)) /\
           word_xor (read Q0 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * g + c)) rk) /\
           word_xor (read Q1 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * g + c + 1)) rk) /\
           word_xor (read Q2 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * g + c + 2)) rk) /\
           word_xor (read Q3 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * g + c + 3)) rk) /\
           word_xor (read Q4 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * g + c + 4)) rk) /\
           word_xor (read Q5 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * g + c + 5)) rk) /\
           word_xor (read Q6 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * g + c + 6)) rk) /\
           word_xor (read Q7 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * g + c + 7)) rk) /\
           htable_mem_8 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j) /\
           (!j. j < 8 * g
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block aes256_cipher c nonce rk (j)) (inblock j)))
      (\s. read PC s = word (pc + 0x1154) /\
           read X9 s = word (16 * nb) /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce (nb + c)) /\
           read (memory :> bytes128 tag_p) s =
             word_reversefields 8
               (nist_ghash (aes256_cipher (word 0) rk) tag0
                  (list_of_seq (nist_cipher_block aes256_cipher c nonce rk inblock) nb)) /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block aes256_cipher c nonce rk (j)) (inblock j)))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * nb);
                  memory :> bytes(tag_p, 16);
                  memory :> bytes(ivec_p, 16)])`,
  REWRITE_TAC[KEY15_SPLIT] THEN
  REWRITE_TAC[htable_mem_8; htable_mem_4; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REWRITE_CONV[fst AES256_GCM_ENC_ALT_EXEC]
    `LENGTH aes256_gcm_enc_alt_tmc`]) THEN
  SUBGOAL_THEN
   `read (memory :> bytes128 (word_add in_p (word (128 * g)))) s0 =
    inblock (8 * g) /\
    read (memory :> bytes128 (word_add in_p (word (128 * g + 16)))) s0 =
    inblock (8 * g + 1) /\
    read (memory :> bytes128 (word_add in_p (word (128 * g + 32)))) s0 =
    inblock (8 * g + 2) /\
    read (memory :> bytes128 (word_add in_p (word (128 * g + 48)))) s0 =
    inblock (8 * g + 3) /\
    read (memory :> bytes128 (word_add in_p (word (128 * g + 64)))) s0 =
    inblock (8 * g + 4) /\
    read (memory :> bytes128 (word_add in_p (word (128 * g + 80)))) s0 =
    inblock (8 * g + 5) /\
    read (memory :> bytes128 (word_add in_p (word (128 * g + 96)))) s0 =
    inblock (8 * g + 6) /\
    read (memory :> bytes128 (word_add in_p (word (128 * g + 112)))) s0 =
    inblock (8 * g + 7)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE
     `128 * g + 16 = 16 * (8 * g + 1) /\
      128 * g + 32 = 16 * (8 * g + 2) /\
      128 * g + 48 = 16 * (8 * g + 3) /\
      128 * g + 64 = 16 * (8 * g + 4) /\
      128 * g + 80 = 16 * (8 * g + 5) /\
      128 * g + 96 = 16 * (8 * g + 6) /\
      128 * g + 112 = 16 * (8 * g + 7)`] THEN
    REWRITE_TAC[ARITH_RULE `128 * a = 16 * 8 * a`] THEN
    REPEAT CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  RULE_ASSUM_TAC(fun th -> try MATCH_MP KS_SOLVE th with Failure _ -> th) THEN
  MAP_EVERY NSTEP_GP (1--9) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP TAIL_X5_128_G (ASSUME `8 * g + 8 = nb`)]) THEN
  DISCARD_DEAD_KEYMEM THEN
  DISCARD_DEAD_HTABLE THEN
  DISCARD_REGS ["Q31"; "Q28"] THEN
  (* eor3-fused drain (-9 instrs, drain 117->108) - same step-index shift as TAIL_REM8:     *)
  (* Q27 last-read s93 (drop after s96), final reduce s114 (was s123), writebacks s115..s118 *)
  (* (was s124..s127).                                                                       *)
  MAP_EVERY NSTEP_GP (10--97) THEN
  DISCARD_REGS ["Q27"] THEN
  MAP_EVERY NSTEP_GP (98--115) THEN
  (* block 8*g+6's keystream ctr 8*g+8 collapsed to nb during the drive (the 8*g+8=nb hyp   *)
  (* rewrites 8*g+8 -> nb L->R); re-expand nb -> 8*g+8 in ONLY the Q19 fact (leave the       *)
  (* 8*g+8=nb hyp intact for the tag/out closers) so the fold reindex fires on all 8 blocks. *)
  RULE_ASSUM_TAC(fun th ->
    if (try lhs(concl th) = `read Q19 s115:int128` with Failure _ -> false)
    then REWRITE_RULE[SYM(ASSUME `8 * g + 8 = nb`)] th else th) THEN
  FOLD_Q19_S114_G THEN
  DISCARD_DEAD_REDUCE_SCRATCH THEN
  MAP_EVERY NSTEP_GP (116--119) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [
    REWRITE_TAC[IVEC_STORE_REV32] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    UNDISCH_TAC `8 * g + 8 = nb` THEN ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [
    FIRST_X_ASSUM(fun th ->
      if concl th = `8 * g + 8 = nb` then SUBST_ALL_TAC(SYM th) else failwith "") THEN
    REWRITE_TAC[TAG_STORE_REV64] THEN AP_TERM_TAC THEN TAIL_Q19_FOLD_G;
    ALL_TAC] THEN
  FIRST_X_ASSUM(fun th ->
    if concl th = `8 * g + 8 = nb` then SUBST_ALL_TAC(SYM th) else failwith "") THEN
  REWRITE_TAC[ARITH_RULE `j < 8 * g + 8 <=>
                       j < 8 * g \/ j = 8 * g \/ j = 8 * g + 1 \/
                       j = 8 * g + 2 \/ j = 8 * g + 3 \/ j = 8 * g + 4 \/
                       j = 8 * g + 5 \/ j = 8 * g + 6 \/ j = 8 * g + 7`] THEN
  ASM_REWRITE_TAC[TAUT `p \/ q ==> r <=> (p ==> r) /\ (q ==> r)`] THEN
  REWRITE_TAC[FORALL_AND_THM; FORALL_UNWIND_THM2] THEN
  REWRITE_TAC[ARITH_RULE `16 * (8 * g + b) = 128 * g + 16 * b`] THEN
  REWRITE_TAC[ARITH_RULE `16 * 8 * g = 128 * g`] THEN
  CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[WORD_SUBWORD_REVERSEFIELDS_32; WORD_SUBWORD_CTR_BLOCK_32] THEN
  REWRITE_TAC[GSYM WORD_ADD; WORD_ADD_0] THEN
  REWRITE_TAC[CTR_BLOCK_RECONSTRUCT_REV8; CTR_BLOCK_RECONSTRUCT_REV32] THEN
  ONCE_REWRITE_TAC[WORD_BITWISE_RULE
    `word_xor (word_xor (inb:int128) ch) rk14 = word_xor ch (word_xor rk14 inb)`] THEN
  REWRITE_TAC[XOR_AES256_CIPHER_RECONSTRUCT] THEN
  ASM_REWRITE_TAC[MAP; WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
  REWRITE_TAC[aes_ctr_block; GSYM ADD_ASSOC] THEN
  CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; GSYM ADD_ASSOC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[WORD_ADD; GSYM WORD_ADD_ASSOC] THEN
  REWRITE_TAC[ADD_ASSOC; ARITH] THEN
  (* close the ciphertext identity at the aes_ctr_block level (TAIL pattern):
     a plain GSYM cipher_block fold is higher-order ambiguous under c. *)
  REWRITE_TAC[AES256_CIPHER_KEYLIST] THEN
  REWRITE_TAC[aes_ctr_block; ADD_CLAUSES] THEN
  REWRITE_TAC[ARITH_RULE `8 * g + c = c + 8 * g`] THEN
  REWRITE_TAC[ADD_ASSOC] THEN
  REWRITE_TAC[ARITH_RULE `(c + 8 * g) + 1 = (1 + 8 * g) + c`;
              ARITH_RULE `(c + 8 * g) + 2 = (2 + 8 * g) + c`;
              ARITH_RULE `(c + 8 * g) + 3 = (3 + 8 * g) + c`;
              ARITH_RULE `(c + 8 * g) + 4 = (4 + 8 * g) + c`;
              ARITH_RULE `(c + 8 * g) + 5 = (5 + 8 * g) + c`;
              ARITH_RULE `(c + 8 * g) + 6 = (6 + 8 * g) + c`;
              ARITH_RULE `(c + 8 * g) + 7 = (7 + 8 * g) + c`] THEN
  REPEAT CONJ_TAC THEN
  TRY(CONV_TAC WORD_RULE) THEN
  TRY(CONV_TAC WORD_BITWISE_RULE) THEN
  REPEAT(AP_THM_TAC ORELSE AP_TERM_TAC) THEN
  TRY ARITH_TAC);;

(* ========================================================================= *)
(* TAIL_REM (rem in 1..8, g>=0).                                             *)
(*                                                                           *)
(* One theorem covering the whole b.gt cascade at entry pc+0xee0, for any    *)
(* leftover-block count rem in 1..8 and any group count g>=0.  Body =        *)
(* DISJ_CASES on rem, each case weakening the (strongest) unified            *)
(* precondition to that arm's precondition via ENSURES_PRECONDITION_THM (the *)
(* arms REM1..7 need fewer register pins / keystreams; REM8 needs all) then  *)
(* dispatching to the matching TAIL_REM<rem>.  rem=8 uses the g-general      *)
(* TAIL_REM8, which is g-general.  The unified precondition pins             *)
(* q18_init/q27_init + all 8 keystreams + the 15 key-mem facts (REM8's       *)
(* precond); the weakening drops whatever each smaller arm omits.  BETA_TAC  *)
(* before STRIP_TAC is load-bearing (the precond is a lambda redex;          *)
(* STRIP-first stashes it unreduced).                                        *)
(* ========================================================================= *)

let AES256_GCM_ENC_ALT_TAIL_REM = prove
 (`!q18_init q27_init in_p out_p tag_p ivec_p key_p htable_p mod_p end_p
     tag0 nonce c rk inblock nb r g pc.
    nb = 8 * g + r /\
    1 <= r /\ r <= 8 /\
    end_p = word_add in_p (word (128 * g)) /\
    val in_p + 16 * nb < 2 EXP 63 /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
      [(word pc, LENGTH aes256_gcm_enc_alt_tmc);
       (in_p, 16 * nb); (key_p, 240); (htable_p, 192); (mod_p, 8)] /\
    PAIRWISE nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) aes256_gcm_enc_alt_tmc /\
           read PC s = word (pc + 0xee0) /\
           read Q18 s = q18_init /\
           read Q27 s = q27_init /\
           read X0 s = word_add in_p (word (128 * g)) /\
           read X2 s = word_add out_p (word (128 * g)) /\
           read X3 s = tag_p /\
           read X9 s = word (16 * nb) /\
           read X4 s = word_add in_p (word (16 * nb)) /\
           read X16 s = ivec_p /\
           read X5 s = end_p /\
           read X6 s = htable_p /\
           read X10 s = mod_p /\
           read X11 s = key_p /\
           read (memory :> bytes64 mod_p) s = word 0xc200000000000000 /\
           wordlist_from_memory(key_p,15) s = MAP (word_reversefields 8) rk /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce c) /\
           read Q28 s = word_reversefields 8 (EL 14 rk) /\
           read Q30 s = word_reversefields 32 (ctr_block nonce (8 * g + c + 8)) /\
           read Q31 s = word 79228162514264337593543950336 /\
           read Q19 s =
             nist_ghash (aes256_cipher (word 0) rk) tag0
                 (list_of_seq (nist_cipher_block aes256_cipher c nonce rk inblock)
                              (8 * g)) /\
           word_xor (read Q0 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * g + c)) rk) /\
           word_xor (read Q1 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * g + c + 1)) rk) /\
           word_xor (read Q2 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * g + c + 2)) rk) /\
           word_xor (read Q3 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * g + c + 3)) rk) /\
           word_xor (read Q4 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * g + c + 4)) rk) /\
           word_xor (read Q5 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * g + c + 5)) rk) /\
           word_xor (read Q6 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * g + c + 6)) rk) /\
           word_xor (read Q7 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * g + c + 7)) rk) /\
           htable_mem_8 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j) /\
           (!j. j < 8 * g
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block aes256_cipher c nonce rk (j)) (inblock j)))
      (\s. read PC s = word (pc + 0x1154) /\
           read X9 s = word (16 * nb) /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce (nb + c)) /\
           read (memory :> bytes128 tag_p) s =
             word_reversefields 8
               (nist_ghash (aes256_cipher (word 0) rk) tag0
                  (list_of_seq (nist_cipher_block aes256_cipher c nonce rk inblock) nb)) /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block aes256_cipher c nonce rk (j)) (inblock j)))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * nb);
                  memory :> bytes(tag_p, 16);
                  memory :> bytes(ivec_p, 16)])`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `r=1\/r=2\/r=3\/r=4\/r=5\/r=6\/r=7\/r=8` MP_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THENL
   [    (MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN EXISTS_TAC `(\s. aligned_bytes_loaded s (word pc) aes256_gcm_enc_alt_tmc /\
           read PC s = word (pc + 0xee0) /\
           read X0 s = word_add in_p (word (128 * g)) /\
           read X2 s = word_add out_p (word (128 * g)) /\
           read X3 s = tag_p /\
           read X9 s = word (16 * nb) /\
           read X4 s = word_add in_p (word (16 * nb)) /\
           read X16 s = ivec_p /\
           read X5 s = end_p /\
           read X6 s = htable_p /\
           read X10 s = mod_p /\
           read X11 s = key_p /\
           read (memory :> bytes64 mod_p) s = word 0xc200000000000000 /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce c) /\
           read Q28 s = word_reversefields 8 (EL 14 rk) /\
           read Q30 s = word_reversefields 32 (ctr_block nonce (8 * g + c + 8)) /\
           read Q31 s = word 79228162514264337593543950336 /\
           read Q19 s =
             nist_ghash (aes256_cipher (word 0) rk) tag0
                 (list_of_seq (nist_cipher_block aes256_cipher c nonce rk inblock) (8 * g)) /\
           word_xor (read Q0 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + c)) rk) /\
           htable_mem_8 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j) /\
           (!j. j < 8 * g
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block aes256_cipher c nonce rk (j)) (inblock j)))` THEN
     CONJ_TAC THENL
      [GEN_TAC THEN BETA_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
       MATCH_MP_TAC AES256_GCM_ENC_ALT_TAIL_REM1 THEN
       REPEAT CONJ_TAC THEN (ASM_ARITH_TAC ORELSE ASM_REWRITE_TAC[])]);
    (MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN EXISTS_TAC `(\s. aligned_bytes_loaded s (word pc) aes256_gcm_enc_alt_tmc /\
           read PC s = word (pc + 0xee0) /\
           read X0 s = word_add in_p (word (128 * g)) /\
           read X2 s = word_add out_p (word (128 * g)) /\
           read X3 s = tag_p /\
           read X9 s = word (16 * nb) /\
           read X4 s = word_add in_p (word (16 * nb)) /\
           read X16 s = ivec_p /\
           read X5 s = end_p /\
           read X6 s = htable_p /\
           read X10 s = mod_p /\
           read X11 s = key_p /\
           read (memory :> bytes64 mod_p) s = word 0xc200000000000000 /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce c) /\
           read Q27 s = q27_init /\
           read Q28 s = word_reversefields 8 (EL 14 rk) /\
           read Q30 s = word_reversefields 32 (ctr_block nonce (8 * g + c + 8)) /\
           read Q31 s = word 79228162514264337593543950336 /\
           read Q19 s =
             nist_ghash (aes256_cipher (word 0) rk) tag0
                 (list_of_seq (nist_cipher_block aes256_cipher c nonce rk inblock) (8 * g)) /\
           word_xor (read Q0 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + c)) rk) /\
           word_xor (read Q1 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + c + 1)) rk) /\
           word_xor (read Q2 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + c + 2)) rk) /\
           word_xor (read Q3 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + c + 3)) rk) /\
           word_xor (read Q4 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + c + 4)) rk) /\
           word_xor (read Q5 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + c + 5)) rk) /\
           word_xor (read Q6 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + c + 6)) rk) /\
           word_xor (read Q7 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + c + 7)) rk) /\
           htable_mem_8 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j) /\
           (!j. j < 8 * g
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block aes256_cipher c nonce rk (j)) (inblock j)))` THEN
     CONJ_TAC THENL
      [GEN_TAC THEN BETA_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
       MATCH_MP_TAC AES256_GCM_ENC_ALT_TAIL_REM2 THEN
       REPEAT CONJ_TAC THEN (ASM_ARITH_TAC ORELSE ASM_REWRITE_TAC[])]);
    (MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN EXISTS_TAC `(\s. aligned_bytes_loaded s (word pc) aes256_gcm_enc_alt_tmc /\
           read PC s = word (pc + 0xee0) /\
           read X0 s = word_add in_p (word (128 * g)) /\
           read X2 s = word_add out_p (word (128 * g)) /\
           read X3 s = tag_p /\
           read X9 s = word (16 * nb) /\
           read X4 s = word_add in_p (word (16 * nb)) /\
           read X16 s = ivec_p /\
           read X5 s = end_p /\
           read X6 s = htable_p /\
           read X10 s = mod_p /\
           read X11 s = key_p /\
           read (memory :> bytes64 mod_p) s = word 0xc200000000000000 /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce c) /\
           read Q27 s = q27_init /\
           read Q28 s = word_reversefields 8 (EL 14 rk) /\
           read Q30 s = word_reversefields 32 (ctr_block nonce (8 * g + c + 8)) /\
           read Q31 s = word 79228162514264337593543950336 /\
           read Q19 s =
             nist_ghash (aes256_cipher (word 0) rk) tag0
                 (list_of_seq (nist_cipher_block aes256_cipher c nonce rk inblock) (8 * g)) /\
           word_xor (read Q0 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + c)) rk) /\
           word_xor (read Q1 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + c + 1)) rk) /\
           word_xor (read Q2 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + c + 2)) rk) /\
           word_xor (read Q3 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + c + 3)) rk) /\
           word_xor (read Q4 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + c + 4)) rk) /\
           word_xor (read Q5 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + c + 5)) rk) /\
           word_xor (read Q6 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + c + 6)) rk) /\
           word_xor (read Q7 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + c + 7)) rk) /\
           htable_mem_8 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j) /\
           (!j. j < 8 * g
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block aes256_cipher c nonce rk (j)) (inblock j)))` THEN
     CONJ_TAC THENL
      [GEN_TAC THEN BETA_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
       MATCH_MP_TAC AES256_GCM_ENC_ALT_TAIL_REM3 THEN
       REPEAT CONJ_TAC THEN (ASM_ARITH_TAC ORELSE ASM_REWRITE_TAC[])]);
    (MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN EXISTS_TAC `(\s. aligned_bytes_loaded s (word pc) aes256_gcm_enc_alt_tmc /\
           read PC s = word (pc + 0xee0) /\
           read X0 s = word_add in_p (word (128 * g)) /\
           read X2 s = word_add out_p (word (128 * g)) /\
           read X3 s = tag_p /\
           read X9 s = word (16 * nb) /\
           read X4 s = word_add in_p (word (16 * nb)) /\
           read X16 s = ivec_p /\
           read X5 s = end_p /\
           read X6 s = htable_p /\
           read X10 s = mod_p /\
           read X11 s = key_p /\
           read (memory :> bytes64 mod_p) s = word 0xc200000000000000 /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce c) /\
           read Q27 s = q27_init /\
           read Q28 s = word_reversefields 8 (EL 14 rk) /\
           read Q30 s = word_reversefields 32 (ctr_block nonce (8 * g + c + 8)) /\
           read Q31 s = word 79228162514264337593543950336 /\
           read Q19 s =
             nist_ghash (aes256_cipher (word 0) rk) tag0
                 (list_of_seq (nist_cipher_block aes256_cipher c nonce rk inblock) (8 * g)) /\
           word_xor (read Q0 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + c)) rk) /\
           word_xor (read Q1 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + c + 1)) rk) /\
           word_xor (read Q2 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + c + 2)) rk) /\
           word_xor (read Q3 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + c + 3)) rk) /\
           word_xor (read Q4 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + c + 4)) rk) /\
           word_xor (read Q5 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + c + 5)) rk) /\
           word_xor (read Q6 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + c + 6)) rk) /\
           word_xor (read Q7 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + c + 7)) rk) /\
           htable_mem_8 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j) /\
           (!j. j < 8 * g
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block aes256_cipher c nonce rk (j)) (inblock j)))` THEN
     CONJ_TAC THENL
      [GEN_TAC THEN BETA_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
       MATCH_MP_TAC AES256_GCM_ENC_ALT_TAIL_REM4 THEN
       REPEAT CONJ_TAC THEN (ASM_ARITH_TAC ORELSE ASM_REWRITE_TAC[])]);
    (MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN EXISTS_TAC `(\s. aligned_bytes_loaded s (word pc) aes256_gcm_enc_alt_tmc /\
           read PC s = word (pc + 0xee0) /\
           read X0 s = word_add in_p (word (128 * g)) /\
           read X2 s = word_add out_p (word (128 * g)) /\
           read X3 s = tag_p /\
           read X9 s = word (16 * nb) /\
           read X4 s = word_add in_p (word (16 * nb)) /\
           read X16 s = ivec_p /\
           read X5 s = end_p /\
           read X6 s = htable_p /\
           read X10 s = mod_p /\
           read X11 s = key_p /\
           read (memory :> bytes64 mod_p) s = word 0xc200000000000000 /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce c) /\
           read Q27 s = q27_init /\
           read Q28 s = word_reversefields 8 (EL 14 rk) /\
           read Q30 s = word_reversefields 32 (ctr_block nonce (8 * g + c + 8)) /\
           read Q31 s = word 79228162514264337593543950336 /\
           read Q19 s =
             nist_ghash (aes256_cipher (word 0) rk) tag0
                 (list_of_seq (nist_cipher_block aes256_cipher c nonce rk inblock) (8 * g)) /\
           word_xor (read Q0 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + c)) rk) /\
           word_xor (read Q1 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + c + 1)) rk) /\
           word_xor (read Q2 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + c + 2)) rk) /\
           word_xor (read Q3 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + c + 3)) rk) /\
           word_xor (read Q4 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + c + 4)) rk) /\
           word_xor (read Q5 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + c + 5)) rk) /\
           word_xor (read Q6 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + c + 6)) rk) /\
           word_xor (read Q7 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + c + 7)) rk) /\
           htable_mem_8 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j) /\
           (!j. j < 8 * g
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block aes256_cipher c nonce rk (j)) (inblock j)))` THEN
     CONJ_TAC THENL
      [GEN_TAC THEN BETA_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
       MATCH_MP_TAC AES256_GCM_ENC_ALT_TAIL_REM5 THEN
       REPEAT CONJ_TAC THEN (ASM_ARITH_TAC ORELSE ASM_REWRITE_TAC[])]);
    (MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN EXISTS_TAC `(\s. aligned_bytes_loaded s (word pc) aes256_gcm_enc_alt_tmc /\
           read PC s = word (pc + 0xee0) /\
           read X0 s = word_add in_p (word (128 * g)) /\
           read X2 s = word_add out_p (word (128 * g)) /\
           read X3 s = tag_p /\
           read X9 s = word (16 * nb) /\
           read X4 s = word_add in_p (word (16 * nb)) /\
           read X16 s = ivec_p /\
           read X5 s = end_p /\
           read X6 s = htable_p /\
           read X10 s = mod_p /\
           read X11 s = key_p /\
           read (memory :> bytes64 mod_p) s = word 0xc200000000000000 /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce c) /\
           read Q27 s = q27_init /\
           read Q28 s = word_reversefields 8 (EL 14 rk) /\
           read Q30 s = word_reversefields 32 (ctr_block nonce (8 * g + c + 8)) /\
           read Q31 s = word 79228162514264337593543950336 /\
           read Q19 s =
             nist_ghash (aes256_cipher (word 0) rk) tag0
                 (list_of_seq (nist_cipher_block aes256_cipher c nonce rk inblock) (8 * g)) /\
           word_xor (read Q0 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + c)) rk) /\
           word_xor (read Q1 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + c + 1)) rk) /\
           word_xor (read Q2 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + c + 2)) rk) /\
           word_xor (read Q3 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + c + 3)) rk) /\
           word_xor (read Q4 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + c + 4)) rk) /\
           word_xor (read Q5 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + c + 5)) rk) /\
           word_xor (read Q6 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + c + 6)) rk) /\
           word_xor (read Q7 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + c + 7)) rk) /\
           htable_mem_8 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j) /\
           (!j. j < 8 * g
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block aes256_cipher c nonce rk (j)) (inblock j)))` THEN
     CONJ_TAC THENL
      [GEN_TAC THEN BETA_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
       MATCH_MP_TAC AES256_GCM_ENC_ALT_TAIL_REM6 THEN
       REPEAT CONJ_TAC THEN (ASM_ARITH_TAC ORELSE ASM_REWRITE_TAC[])]);
    (MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN EXISTS_TAC `(\s. aligned_bytes_loaded s (word pc) aes256_gcm_enc_alt_tmc /\
           read PC s = word (pc + 0xee0) /\
           read X0 s = word_add in_p (word (128 * g)) /\
           read X2 s = word_add out_p (word (128 * g)) /\
           read X3 s = tag_p /\
           read X9 s = word (16 * nb) /\
           read X4 s = word_add in_p (word (16 * nb)) /\
           read X16 s = ivec_p /\
           read X5 s = end_p /\
           read X6 s = htable_p /\
           read X10 s = mod_p /\
           read X11 s = key_p /\
           read (memory :> bytes64 mod_p) s = word 0xc200000000000000 /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce c) /\
           read Q27 s = q27_init /\
           read Q28 s = word_reversefields 8 (EL 14 rk) /\
           read Q30 s = word_reversefields 32 (ctr_block nonce (8 * g + c + 8)) /\
           read Q31 s = word 79228162514264337593543950336 /\
           read Q19 s =
             nist_ghash (aes256_cipher (word 0) rk) tag0
                 (list_of_seq (nist_cipher_block aes256_cipher c nonce rk inblock) (8 * g)) /\
           word_xor (read Q0 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + c)) rk) /\
           word_xor (read Q1 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + c + 1)) rk) /\
           word_xor (read Q2 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + c + 2)) rk) /\
           word_xor (read Q3 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + c + 3)) rk) /\
           word_xor (read Q4 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + c + 4)) rk) /\
           word_xor (read Q5 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + c + 5)) rk) /\
           word_xor (read Q6 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + c + 6)) rk) /\
           word_xor (read Q7 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8
               (aes256_cipher (ctr_block nonce (8 * g + c + 7)) rk) /\
           htable_mem_8 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j) /\
           (!j. j < 8 * g
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block aes256_cipher c nonce rk (j)) (inblock j)))` THEN
     CONJ_TAC THENL
      [GEN_TAC THEN BETA_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
       MATCH_MP_TAC AES256_GCM_ENC_ALT_TAIL_REM7 THEN
       REPEAT CONJ_TAC THEN (ASM_ARITH_TAC ORELSE ASM_REWRITE_TAC[])]);
    (MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN EXISTS_TAC `(\s. aligned_bytes_loaded s (word pc) aes256_gcm_enc_alt_tmc /\
           read PC s = word (pc + 0xee0) /\
           read Q18 s = q18_init /\
           read Q27 s = q27_init /\
           read X0 s = word_add in_p (word (128 * g)) /\
           read X2 s = word_add out_p (word (128 * g)) /\
           read X3 s = tag_p /\
           read X9 s = word (16 * nb) /\
           read X4 s = word_add in_p (word (16 * nb)) /\
           read X16 s = ivec_p /\
           read X5 s = end_p /\
           read X6 s = htable_p /\
           read X10 s = mod_p /\
           read X11 s = key_p /\
           read (memory :> bytes64 mod_p) s = word 0xc200000000000000 /\
           wordlist_from_memory(key_p,15) s = MAP (word_reversefields 8) rk /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce c) /\
           read Q28 s = word_reversefields 8 (EL 14 rk) /\
           read Q30 s = word_reversefields 32 (ctr_block nonce (8 * g + c + 8)) /\
           read Q31 s = word 79228162514264337593543950336 /\
           read Q19 s =
             nist_ghash (aes256_cipher (word 0) rk) tag0
                 (list_of_seq (nist_cipher_block aes256_cipher c nonce rk inblock)
                              (8 * g)) /\
           word_xor (read Q0 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * g + c)) rk) /\
           word_xor (read Q1 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * g + c + 1)) rk) /\
           word_xor (read Q2 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * g + c + 2)) rk) /\
           word_xor (read Q3 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * g + c + 3)) rk) /\
           word_xor (read Q4 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * g + c + 4)) rk) /\
           word_xor (read Q5 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * g + c + 5)) rk) /\
           word_xor (read Q6 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * g + c + 6)) rk) /\
           word_xor (read Q7 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * g + c + 7)) rk) /\
           htable_mem_8 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j) /\
           (!j. j < 8 * g
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block aes256_cipher c nonce rk (j)) (inblock j)))` THEN
     CONJ_TAC THENL
      [GEN_TAC THEN BETA_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
       MATCH_MP_TAC AES256_GCM_ENC_ALT_TAIL_REM8 THEN
       REPEAT CONJ_TAC THEN (ASM_ARITH_TAC ORELSE ASM_REWRITE_TAC[])])]);;



(* ========================================================================= *)
(* Full-body assembly: core entry pc+0x38 (SETUP) -> exit pc+0x1154 (TAIL).  *)
(*                                                                           *)
(* Assembly: 3 nested ENSURES_SEQUENCE_TAC at 0x4c0 / 0xa10 / 0xee0. Each    *)
(* first leg: frame-subsume the segment's MAYCHANGE into the whole frame     *)
(* (ENSURES_FRAME_SUBSUMED + SUBSUMED_MAYCHANGE_TAC), then apply the segment *)
(* thm via MP_TAC ... DISCH_THEN MATCH_MP_TAC (xts template in               *)
(* AES_XTS_ENCRYPT_LT_2BLOCK_CORRECT). The PREPRETAIL->TAIL join uses the    *)
(* EXISTENTIAL Q18/Q27 mid-state (option D): the mid predicate carries `?v18 *)
(* v27. read Q18 s=v18 /\ read Q27 s=v27 /\ <PP-post-body minus              *)
(* tag-in-mem>`; PP leg proves it by EXISTS_TAC (read Q18 s)/(read Q27 s);   *)
(* TAIL leg strips the ? and applies TAIL SPEC'd to those.                   *)
(* ========================================================================= *)

(* Frame note: SETUP/MAIN_LOOP/PREPRETAIL frames are subsets of the CORRECT  *)
(* frame (ABI ,, Q8..Q15 ,, mem[out_p;tag_p;ivec_p]).  SETUP frame writes    *)
(* only out_p mem (+ regs); PP writes out_p mem; TAIL writes out+tag+ivec.   *)

let LENGTH_WB_MC =
  (REWRITE_CONV [fst AES256_GCM_ENC_ALT_EXEC]) `LENGTH aes256_gcm_enc_alt_tmc`;;

(* Helper for the option-D TAIL leg: an ensures with an existential          *)
(* precondition follows from the ensures for every witness. Trivial from the *)
(* ensures def (the precondition ?v w. P is stripped, witnesses specialize   *)
(* the hypothesis).  Two-existential form matching the 0xee0 mid-state.      *)
let ENSURES_EXISTS2_PRECONDITION = prove
 (`!step (P:B->C->A->bool) Q Fr.
        (!v w. ensures step (\s. P v w s) Q Fr)
        ==> ensures step (\s. ?v w. P v w s) Q Fr`,
  REWRITE_TAC[ensures] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`v:B`; `w:C`]) THEN
  DISCH_THEN(MP_TAC o SPEC `s:A`) THEN ASM_REWRITE_TAC[]);;

let AES256_GCM_ENC_ALT_GEN_CORRECT = prove
 (`!in_p out_p tag_p ivec_p key_p htable_p stackpointer bit_len end_p
     tag0 nonce c rk inblock nb k pc.
    ~(k = 0) /\
    8 * (k + 1) <= nb /\
    bit_len = 128 * nb /\
    8 * (k + 1) < nb /\ nb <= 8 * (k + 2) /\
    val in_p + 16 * nb < 2 EXP 63 /\
    end_p = word_add in_p (word (128 * (k + 1))) /\
    val in_p + 128 * (k + 1) < 2 EXP 63 /\
    128 * nb < 2 EXP 64 /\
    nonoverlapping (out_p, 16 * nb)
                   (word pc, LENGTH aes256_gcm_enc_alt_tmc) /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
      [(word pc, LENGTH aes256_gcm_enc_alt_tmc);
       (in_p, 16 * nb); (key_p, 240); (htable_p, 192);
       (word_add stackpointer (word 0x40), 8)] /\
    PAIRWISE nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) aes256_gcm_enc_alt_tmc /\
           read PC s = word (pc + 0x38) /\
           read X0 s = in_p /\
           read X1 s = word bit_len /\
           read X2 s = out_p /\
           read X3 s = tag_p /\
           read X16 s = ivec_p /\
           read X6 s = htable_p /\
           read X11 s = key_p /\
           read X9 s = word (bit_len DIV 8) /\
           read X10 s = word_add stackpointer (word 0x40) /\
           read (memory :> bytes64 (word_add stackpointer (word 0x40))) s =
             word 0xc200000000000000 /\
           wordlist_from_memory(key_p,15) s = MAP (word_reversefields 8) rk /\
           read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce c) /\
           htable_mem_8 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j))
      (\s. read PC s = word (pc + 0x1154) /\
           read X9 s = word (16 * nb) /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce (nb + c)) /\
           read (memory :> bytes128 tag_p) s =
             word_reversefields 8
               (nist_ghash (aes256_cipher (word 0) rk) tag0
                  (list_of_seq (nist_cipher_block aes256_cipher c nonce rk inblock) nb)) /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block aes256_cipher c nonce rk (j)) (inblock j)))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * nb);
                  memory :> bytes(tag_p, 16);
                  memory :> bytes(ivec_p, 16)])`,
  (* NOTE:                                                               *)
  (* ENSURES_SEQUENCE_TAC AUTO-ADDS the `aligned_bytes_loaded` (program_decodes) *)
  (* and `read PC s = word pc'` conjuncts to BOTH legs' mid-state - so the `q`   *)
  (* arg must OMIT them (include ONLY the register/memory `Q s` remainder).      *)
  (* Also it fires MAYCHANGE_IDEMPOT_TAC internally, which DIES if the ABI macro *)
  (* is folded - so UNFOLD it first.                                             *)
  (* Expand the core CORRECT precondition's ALLPAIRS + PAIRWISE into individual *)
  (* nonoverlapping atoms BEFORE stripping, so each segment leg's antecedent     *)
  (* (out_p vs tag_p/ivec_p live in CORRECT's PAIRWISE) is available as an        *)
  (* assumption for ASM_SIMP/ASM_REWRITE.  (SETUP's precond needs out_p vs        *)
  (* tag_p & ivec_p, which are PAIRWISE facts in CORRECT, not in its ALLPAIRS.)    *)
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REWRITE_TAC[LENGTH_WB_MC; ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES] THEN
  REPEAT STRIP_TAC THEN

  (* ============ SEQUENCE 1: SETUP  pc+0x38 -> pc+0x4c0 ============ *)
  (* mid-state OMITS aligned_bytes_loaded + read PC (auto-added by the tactic). *)
  ENSURES_SEQUENCE_TAC `pc + 0x4c0`
   `\s. read X0 s = word_add in_p (word (128 * (0 + 1))) /\
        read X2 s = word_add out_p (word (128 * (0 + 1))) /\
        read X3 s = tag_p /\
        read X9 s = word (16 * nb) /\
        read X4 s = word_add in_p (word (16 * nb)) /\
        read X16 s = ivec_p /\
        read X5 s = end_p /\
        read X6 s = htable_p /\
        read X10 s = word_add stackpointer (word 0x40) /\
        read X11 s = key_p /\
        read (memory :> bytes64 (word_add stackpointer (word 0x40))) s =
          word 0xc200000000000000 /\
        wordlist_from_memory(key_p,15) s = MAP (word_reversefields 8) rk /\
        read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
        read (memory :> bytes128 ivec_p) s =
          word_reversefields 8 (ctr_block nonce c) /\
        read Q30 s = word_reversefields 32 (ctr_block nonce (8 * 0 + c + 13)) /\
        read Q31 s = word 79228162514264337593543950336 /\
        read Q19 s =
          nist_ghash (aes256_cipher (word 0) rk) tag0
              (list_of_seq (nist_cipher_block aes256_cipher c nonce rk inblock) (8 * 0)) /\
        read Q8 s = word_xor (aes_ctr_block aes256_cipher c nonce rk ((8 * 0 + 0))) (inblock (8 * 0 + 0)) /\
        read Q9 s = word_xor (aes_ctr_block aes256_cipher c nonce rk ((8 * 0 + 1))) (inblock (8 * 0 + 1)) /\
        read Q10 s = word_xor (aes_ctr_block aes256_cipher c nonce rk ((8 * 0 + 2))) (inblock (8 * 0 + 2)) /\
        read Q11 s = word_xor (aes_ctr_block aes256_cipher c nonce rk ((8 * 0 + 3))) (inblock (8 * 0 + 3)) /\
        read Q12 s = word_xor (aes_ctr_block aes256_cipher c nonce rk ((8 * 0 + 4))) (inblock (8 * 0 + 4)) /\
        read Q13 s = word_xor (aes_ctr_block aes256_cipher c nonce rk ((8 * 0 + 5))) (inblock (8 * 0 + 5)) /\
        read Q14 s = word_xor (aes_ctr_block aes256_cipher c nonce rk ((8 * 0 + 6))) (inblock (8 * 0 + 6)) /\
        read Q15 s = word_xor (aes_ctr_block aes256_cipher c nonce rk ((8 * 0 + 7))) (inblock (8 * 0 + 7)) /\
        read Q0 s = word_reversefields 8 (ctr_block nonce (8 * 0 + c + 8)) /\
        read Q1 s = word_reversefields 8 (ctr_block nonce (8 * 0 + c + 9)) /\
        read Q2 s = word_reversefields 8 (ctr_block nonce (8 * 0 + c + 10)) /\
        read Q3 s = word_reversefields 8 (ctr_block nonce (8 * 0 + c + 11)) /\
        read Q4 s = word_reversefields 8 (ctr_block nonce (8 * 0 + c + 12)) /\
        htable_mem_8 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s /\
        (!j. j < nb
             ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                 inblock j) /\
        (!j. j < 8 * (0 + 1)
             ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                 word_xor (aes_ctr_block aes256_cipher c nonce rk (j)) (inblock j)) /\
        ((read NF s <=> read VF s) <=> (0 = k))` THEN
  CONJ_TAC THENL
   [(* SETUP leg *)
    MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN
    EXISTS_TAC
     `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
      MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
      MAYCHANGE [memory :> bytes(out_p, 16 * nb)]` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
      REPEAT (GEN_REWRITE_TAC ONCE_DEPTH_CONV [GSYM SEQ_ASSOC] THEN
              MATCH_MP_TAC SUBSUMED_SEQ THEN REWRITE_TAC[SUBSUMED_REFL]) THEN
      SUBSUMED_MAYCHANGE_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL
     [`in_p:int64`; `out_p:int64`; `tag_p:int64`; `ivec_p:int64`;
      `key_p:int64`; `htable_p:int64`; `stackpointer:int64`; `bit_len:num`;
      `end_p:int64`; `tag0:int128`; `nonce:(96)word`; `c:num`; `rk:int128 list`;
      `inblock:num->int128`; `nb:num`; `k:num`; `pc:num`]
     AES256_GCM_ENC_ALT_SETUP_GEN) THEN
    REWRITE_TAC[LENGTH_WB_MC; ALLPAIRS; ALL; NONOVERLAPPING_CLAUSES] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[NONOVERLAPPING_CLAUSES] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN

  (* ============ SEQUENCE 2: MAIN_LOOP  pc+0x4c0 -> pc+0xa10 ============ *)
  (* mid-state = PREPRETAIL precondition (pc+0xa10), OMITTING aligned+PC,     *)
  (* with mod_p := stackpointer+0x40.  Written EXPLICITLY (copy of the        *)
  (* precondition of AES256_GCM_ENC_ALT_PREPRETAIL_GEN, dropping the          *)
  (* aligned_bytes_loaded + read PC lines).                                   *)
  ENSURES_SEQUENCE_TAC `pc + 0xa10`
   `\s. read X0 s = word_add in_p (word (128 * (k + 1))) /\
        read X2 s = word_add out_p (word (128 * (k + 1))) /\
        read X3 s = tag_p /\
        read X9 s = word (16 * nb) /\
        read X4 s = word_add in_p (word (16 * nb)) /\
        read X16 s = ivec_p /\
        read X5 s = end_p /\
        read X6 s = htable_p /\
        read X10 s = word_add stackpointer (word 0x40) /\
        read X11 s = key_p /\
        read (memory :> bytes64 (word_add stackpointer (word 0x40))) s =
          word 0xc200000000000000 /\
        wordlist_from_memory(key_p,15) s = MAP (word_reversefields 8) rk /\
        read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
        read (memory :> bytes128 ivec_p) s =
          word_reversefields 8 (ctr_block nonce c) /\
        read Q30 s = word_reversefields 32 (ctr_block nonce (8 * k + c + 13)) /\
        read Q31 s = word 79228162514264337593543950336 /\
        read Q19 s =
          nist_ghash (aes256_cipher (word 0) rk) tag0
              (list_of_seq (nist_cipher_block aes256_cipher c nonce rk inblock) (8 * k)) /\
        read Q8 s = word_xor (aes_ctr_block aes256_cipher c nonce rk ((8 * k + 0))) (inblock (8 * k + 0)) /\
        read Q9 s = word_xor (aes_ctr_block aes256_cipher c nonce rk ((8 * k + 1))) (inblock (8 * k + 1)) /\
        read Q10 s = word_xor (aes_ctr_block aes256_cipher c nonce rk ((8 * k + 2))) (inblock (8 * k + 2)) /\
        read Q11 s = word_xor (aes_ctr_block aes256_cipher c nonce rk ((8 * k + 3))) (inblock (8 * k + 3)) /\
        read Q12 s = word_xor (aes_ctr_block aes256_cipher c nonce rk ((8 * k + 4))) (inblock (8 * k + 4)) /\
        read Q13 s = word_xor (aes_ctr_block aes256_cipher c nonce rk ((8 * k + 5))) (inblock (8 * k + 5)) /\
        read Q14 s = word_xor (aes_ctr_block aes256_cipher c nonce rk ((8 * k + 6))) (inblock (8 * k + 6)) /\
        read Q15 s = word_xor (aes_ctr_block aes256_cipher c nonce rk ((8 * k + 7))) (inblock (8 * k + 7)) /\
        read Q0 s = word_reversefields 8 (ctr_block nonce (8 * k + c + 8)) /\
        read Q1 s = word_reversefields 8 (ctr_block nonce (8 * k + c + 9)) /\
        read Q2 s = word_reversefields 8 (ctr_block nonce (8 * k + c + 10)) /\
        read Q3 s = word_reversefields 8 (ctr_block nonce (8 * k + c + 11)) /\
        read Q4 s = word_reversefields 8 (ctr_block nonce (8 * k + c + 12)) /\
        htable_mem_8 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s /\
        (!j. j < nb
             ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                 inblock j) /\
        (!j. j < 8 * (k + 1)
             ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                 word_xor (aes_ctr_block aes256_cipher c nonce rk (j)) (inblock j))` THEN
  CONJ_TAC THENL
   [(* MAIN_LOOP leg *)
    MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN
    EXISTS_TAC
     `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
      MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
      MAYCHANGE [memory :> bytes(out_p, 16 * nb)]` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
      REPEAT (GEN_REWRITE_TAC ONCE_DEPTH_CONV [GSYM SEQ_ASSOC] THEN
              MATCH_MP_TAC SUBSUMED_SEQ THEN REWRITE_TAC[SUBSUMED_REFL]) THEN
      SUBSUMED_MAYCHANGE_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL
     [`in_p:int64`; `out_p:int64`; `tag_p:int64`; `ivec_p:int64`;
      `key_p:int64`; `htable_p:int64`; `word_add stackpointer (word 0x40):int64`;
      `end_p:int64`; `tag0:int128`; `nonce:(96)word`; `c:num`; `rk:int128 list`;
      `inblock:num->int128`; `nb:num`; `k:num`; `pc:num`]
     AES256_GCM_ENC_ALT_MAIN_LOOP) THEN
    REWRITE_TAC[LENGTH_WB_MC; ALLPAIRS; ALL; NONOVERLAPPING_CLAUSES] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[NONOVERLAPPING_CLAUSES] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN

  (* ============ SEQUENCE 3: PREPRETAIL  pc+0xa10 -> pc+0xee0 (option D) === *)
  (* mid-state = ?v18 v27. read Q18 = v18 /\ read Q27 = v27 /\ <PP-post-body>. *)
  (* Build the join predicate: PREPRETAIL's postcondition body (the           *)
  (* postcondition of AES256_GCM_ENC_ALT_PREPRETAIL_GEN, mod_p ->             *)
  (* stackpointer+0x40) wrapped in ?v18 v27 + the pins.                       *)
  (* mid-state OMITS aligned+PC (auto-added).  The existential wraps the pins   *)
  (* + the PP-post body (minus tag-in-mem).  For ENSURES_EXISTS2_PRECONDITION to *)
  (* match on the TAIL leg, the `?v18 v27.` must be the OUTERMOST structure of   *)
  (* the `Q s` remainder - but the tactic wraps it as `aligned /\ PC /\ (?..)`.  *)
  (* NOTE-live: the auto-added aligned+PC sit OUTSIDE the ?; so on the TAIL leg  *)
  (* the precondition is `\s. aligned s /\ read PC s=.. /\ (?v18 v27. ...)`, and *)
  (* ENSURES_EXISTS2_PRECONDITION won't match directly.  Handle by first        *)
  (* SWAPPING: pull the ? outward, OR strip aligned+PC into asms via            *)
  (* ENSURES_PRECONDITION + a lambda that moves ? out (?v w. aligned/\PC/\body). *)
  (* Simplest live fix: make the mid-state itself `\s. ?v18 v27. read Q18 s=v18  *)
  (* /\ ... /\ <body>` and rely on the tactic adding aligned/PC OUTSIDE, then on *)
  (* the TAIL leg do `REWRITE_TAC[RIGHT_EXISTS_AND_THM/LEFT_EXISTS_AND_THM] o.a. *)
  (* to hoist the ? to the top before MATCH_MP_TAC ENSURES_EXISTS2_PRECONDITION. *)
  ENSURES_SEQUENCE_TAC `pc + 0xee0`
   `\s. ?v18 v27.
        read Q18 s = v18 /\ read Q27 s = v27 /\
        read X0 s = word_add in_p (word (128 * (k + 1))) /\
        read X2 s = word_add out_p (word (128 * (k + 1))) /\
        read X3 s = tag_p /\
        read X9 s = word (16 * nb) /\
        read X4 s = word_add in_p (word (16 * nb)) /\
        read X16 s = ivec_p /\
        read X5 s = end_p /\
        read X6 s = htable_p /\
        read X10 s = word_add stackpointer (word 0x40) /\
        read X11 s = key_p /\
        read (memory :> bytes64 (word_add stackpointer (word 0x40))) s =
          word 0xc200000000000000 /\
        wordlist_from_memory(key_p,15) s = MAP (word_reversefields 8) rk /\
        read (memory :> bytes128 ivec_p) s =
          word_reversefields 8 (ctr_block nonce c) /\
        read Q28 s = word_reversefields 8 (EL 14 rk) /\
        read Q30 s = word_reversefields 32 (ctr_block nonce (8 * k + c + 16)) /\
        read Q31 s = word 79228162514264337593543950336 /\
        read Q19 s =
          nist_ghash (aes256_cipher (word 0) rk) tag0
              (list_of_seq (nist_cipher_block aes256_cipher c nonce rk inblock) (8 * (k + 1))) /\
        word_xor (read Q0 s) (word_reversefields 8 (EL 14 rk)) =
          word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * k + c + 8)) rk) /\
        word_xor (read Q1 s) (word_reversefields 8 (EL 14 rk)) =
          word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * k + c + 9)) rk) /\
        word_xor (read Q2 s) (word_reversefields 8 (EL 14 rk)) =
          word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * k + c + 10)) rk) /\
        word_xor (read Q3 s) (word_reversefields 8 (EL 14 rk)) =
          word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * k + c + 11)) rk) /\
        word_xor (read Q4 s) (word_reversefields 8 (EL 14 rk)) =
          word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * k + c + 12)) rk) /\
        word_xor (read Q5 s) (word_reversefields 8 (EL 14 rk)) =
          word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * k + c + 13)) rk) /\
        word_xor (read Q6 s) (word_reversefields 8 (EL 14 rk)) =
          word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * k + c + 14)) rk) /\
        word_xor (read Q7 s) (word_reversefields 8 (EL 14 rk)) =
          word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * k + c + 15)) rk) /\
        htable_mem_8 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s /\
        (!j. j < nb
             ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                 inblock j) /\
        (!j. j < 8 * (k + 1)
             ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                 word_xor (aes_ctr_block aes256_cipher c nonce rk (j)) (inblock j))` THEN
  CONJ_TAC THENL
   [(* PREPRETAIL leg: apply PREPRETAIL, then weaken its post to the           *)
    (* existential mid-state (EXISTS the actual Q18/Q27 reads).                *)
    MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN
    EXISTS_TAC
     `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
      MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
      MAYCHANGE [memory :> bytes(out_p, 16 * nb)]` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
      REPEAT (GEN_REWRITE_TAC ONCE_DEPTH_CONV [GSYM SEQ_ASSOC] THEN
              MATCH_MP_TAC SUBSUMED_SEQ THEN REWRITE_TAC[SUBSUMED_REFL]) THEN
      SUBSUMED_MAYCHANGE_TAC;
      ALL_TAC] THEN
    (* Weaken the GOAL's post from Q_mid (the ?-existential) to PREPRETAIL's    *)
    (* actual post via ENSURES_POSTCONDITION_TAC (canonical idiom, robust:      *)
    (* it MATCH_MP_TAC's ENSURES_POSTCONDITION_THM + EXISTS_TAC the given post). *)
    (* This leaves TWO subgoals: (1) the pointwise implication PP_post ==>       *)
    (* Q_mid (closed by EXISTS_TAC (read Q18/Q27 s) + ASM_REWRITE), and (2)      *)
    (* `ensures arm PP_pre PP_post frame` = PREPRETAIL applied.                  *)
    (* NB the PP_post lambda passed here must OMIT the aligned+PC (the tactic    *)
    (* handles PC via the ensures) - actually pass PREPRETAIL's FULL post        *)
    (* (the postcondition of AES256_GCM_ENC_ALT_PREPRETAIL_GEN: read PC .. /\    *)
    (* body), i.e. exactly PREPRETAIL's post.                                    *)
    ENSURES_POSTCONDITION_TAC
     `\s. aligned_bytes_loaded s (word pc) aes256_gcm_enc_alt_tmc /\
          read PC s = word (pc + 0xee0) /\
          read X0 s = word_add in_p (word (128 * (k + 1))) /\
          read X2 s = word_add out_p (word (128 * (k + 1))) /\
          read X3 s = tag_p /\ read X9 s = word (16 * nb) /\ read X4 s = word_add in_p (word (16 * nb)) /\
          read X16 s = ivec_p /\ read X5 s = end_p /\ read X6 s = htable_p /\
          read X10 s = word_add stackpointer (word 0x40) /\ read X11 s = key_p /\
          read (memory :> bytes64 (word_add stackpointer (word 0x40))) s =
            word 0xc200000000000000 /\
          wordlist_from_memory(key_p,15) s = MAP (word_reversefields 8) rk /\
          read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
          read (memory :> bytes128 ivec_p) s = word_reversefields 8 (ctr_block nonce c) /\
          read Q28 s = word_reversefields 8 (EL 14 rk) /\
          read Q30 s = word_reversefields 32 (ctr_block nonce (8 * k + c + 16)) /\
          read Q31 s = word 79228162514264337593543950336 /\
          read Q19 s = nist_ghash (aes256_cipher (word 0) rk) tag0
              (list_of_seq (nist_cipher_block aes256_cipher c nonce rk inblock) (8 * (k + 1))) /\
          word_xor (read Q0 s) (word_reversefields 8 (EL 14 rk)) =
            word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * k + c + 8)) rk) /\
          word_xor (read Q1 s) (word_reversefields 8 (EL 14 rk)) =
            word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * k + c + 9)) rk) /\
          word_xor (read Q2 s) (word_reversefields 8 (EL 14 rk)) =
            word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * k + c + 10)) rk) /\
          word_xor (read Q3 s) (word_reversefields 8 (EL 14 rk)) =
            word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * k + c + 11)) rk) /\
          word_xor (read Q4 s) (word_reversefields 8 (EL 14 rk)) =
            word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * k + c + 12)) rk) /\
          word_xor (read Q5 s) (word_reversefields 8 (EL 14 rk)) =
            word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * k + c + 13)) rk) /\
          word_xor (read Q6 s) (word_reversefields 8 (EL 14 rk)) =
            word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * k + c + 14)) rk) /\
          word_xor (read Q7 s) (word_reversefields 8 (EL 14 rk)) =
            word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * k + c + 15)) rk) /\
          htable_mem_8 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s /\
          (!j. j < nb ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s = inblock j) /\
          (!j. j < 8 * (k + 1) ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                 word_xor (aes_ctr_block aes256_cipher c nonce rk (j)) (inblock j))` THEN
    CONJ_TAC THENL
     [(* (1) PP_post(aug) ==> Q_mid.  PREPRETAIL is augmented with aligned in    *)
      (* its post, so ENSURES_POSTCONDITION_TAC's antecedent lambda (above) also  *)
      (* carries aligned.  X_GEN_TAC forces the state var to `s` (so the pin      *)
      (* witnesses match); BETA_TAC reduces BOTH the antecedent redex `(\s.OLD)s` *)
      (* and the consequent redex `(\s.MID)s` BEFORE STRIP_TAC - critical: if     *)
      (* STRIP runs first it stashes the antecedent as ONE unreduced redex and    *)
      (* aligned never lands in the asms.  Then REPEAT(CONJ_TAC ...) peels the     *)
      (* aligned + PC conjuncts (both now in asms) off the mid's conjunction and   *)
      (* EXISTS the actual Q18/Q27 reads on the residual existential.             *)
      X_GEN_TAC `s:armstate` THEN BETA_TAC THEN STRIP_TAC THEN
      REPEAT(CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC]) THEN
      EXISTS_TAC `read Q18 s:int128` THEN EXISTS_TAC `read Q27 s:int128` THEN
      ASM_REWRITE_TAC[];
      (* (2) ensures PP_pre PP_post frame = PREPRETAIL applied.                *)
      MP_TAC(ISPECL
       [`in_p:int64`; `out_p:int64`; `tag_p:int64`; `ivec_p:int64`;
        `key_p:int64`; `htable_p:int64`; `word_add stackpointer (word 0x40):int64`;
        `end_p:int64`; `tag0:int128`; `nonce:(96)word`; `c:num`; `rk:int128 list`;
        `inblock:num->int128`; `nb:num`; `k:num`; `pc:num`]
       AES256_GCM_ENC_ALT_PREPRETAIL_GEN) THEN
      REWRITE_TAC[LENGTH_WB_MC; ALLPAIRS; ALL; NONOVERLAPPING_CLAUSES] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[NONOVERLAPPING_CLAUSES] THEN ASM_ARITH_TAC];
    (* NOTE-live: ENSURES_POSTCONDITION_TAC's post lambda must MATCH PP's post   *)
    (* modulo the frame - PC-conjunct kept, aligned dropped (post has no aligned)*)
    (* If the tactic rejects the shape, fall back to MP_TAC PP + IMP_CONJ +      *)
    (* ENSURES_POSTCONDITION_THM as before.  Pins close by REFL (EXISTS read Qn).*)
    ALL_TAC] THEN

  (* ============ TAIL leg: pc+0xee0 -> pc+0x1154 ============ *)
  (* Precondition now carries ?v18 v27. Strip it via the helper, apply TAIL   *)
  (* SPEC'd to v18/v27.  MATCH_MP_TAC ENSURES_EXISTS2_PRECONDITION turns the   *)
  (* goal `ensures step (\s. ?v18 v27. read Q18 s=v18 /\ read Q27 s=v27 /\ B)  *)
  (* post frame` into `!v18 v27. ensures step (\s. read Q18=v18 /\ ... /\ B)`. *)
  (* NOTE the mid-state must be syntactically `\s. ?v18 v27. read Q18 s=v18 /\ *)
  (* read Q27 s=v27 /\ <body>` for the helper's `\s. ?v w. P v w s` to match   *)
  (* (P v w s = read Q18 s=v /\ read Q27 s=w /\ body).  It is (built above).   *)
  (* BUT ENSURES_SEQUENCE_TAC auto-wrapped the precondition as                 *)
  (*   `\s. aligned_bytes_loaded .. /\ read PC s = word(pc+0xee0) /\ (?v w. B)` *)
  (* so the `?` is NOT outermost.  Hoist it out FIRST with GSYM               *)
  (* RIGHT_EXISTS_AND_THM (`P /\ (?x. Q x)` -> `?x. P /\ Q x`), applied under   *)
  (* the \s. binder (REWRITE descends), so the precondition becomes            *)
  (*   `\s. ?v w. aligned .. /\ read PC .. /\ B` and the helper matches.        *)
  (* If the aligned/PC conjuncts don't fully hoist, also try LEFT_EXISTS_AND_  *)
  (* THM / GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV).                       *)
  REWRITE_TAC[GSYM RIGHT_EXISTS_AND_THM; GSYM LEFT_EXISTS_AND_THM] THEN
  MATCH_MP_TAC ENSURES_EXISTS2_PRECONDITION THEN
  MAP_EVERY X_GEN_TAC [`v18:int128`; `v27:int128`] THEN
  MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN
  EXISTS_TAC
   `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
    MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
    MAYCHANGE [memory :> bytes(out_p, 16 * nb);
               memory :> bytes(tag_p, 16);
               memory :> bytes(ivec_p, 16)]` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    REPEAT (GEN_REWRITE_TAC ONCE_DEPTH_CONV [GSYM SEQ_ASSOC] THEN
            MATCH_MP_TAC SUBSUMED_SEQ THEN REWRITE_TAC[SUBSUMED_REFL]) THEN
    SUBSUMED_MAYCHANGE_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`v18:int128`; `v27:int128`;
    `in_p:int64`; `out_p:int64`; `tag_p:int64`; `ivec_p:int64`;
    `key_p:int64`; `htable_p:int64`; `word_add stackpointer (word 0x40):int64`;
    `end_p:int64`; `tag0:int128`; `nonce:(96)word`; `c:num`; `rk:int128 list`;
    `inblock:num->int128`; `nb:num`; `nb - 8 * (k + 1)`; `k + 1`; `pc:num`]
   AES256_GCM_ENC_ALT_TAIL_REM) THEN
  REWRITE_TAC[LENGTH_WB_MC; ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES] THEN
  (* align TAIL_REM's ISPECL'd (g:=k+1) counters 8*(k+1)+c+M with the
     intermediate state's 8*k+c+(M+8) form: these c-carrying ARITH_RULEs
     rewrite 8*(k+1)+c+M to 8*k+c+(M+8) on the counters that carry c. *)
  REWRITE_TAC[ARITH_RULE `8 * (k + 1) + c = 8 * k + c + 8`;
              ARITH_RULE `8 * (k + 1) + c + 1 = 8 * k + c + 9`;
              ARITH_RULE `8 * (k + 1) + c + 2 = 8 * k + c + 10`;
              ARITH_RULE `8 * (k + 1) + c + 3 = 8 * k + c + 11`;
              ARITH_RULE `8 * (k + 1) + c + 4 = 8 * k + c + 12`;
              ARITH_RULE `8 * (k + 1) + c + 5 = 8 * k + c + 13`;
              ARITH_RULE `8 * (k + 1) + c + 6 = 8 * k + c + 14`;
              ARITH_RULE `8 * (k + 1) + c + 7 = 8 * k + c + 15`;
              ARITH_RULE `8 * (k + 1) + c + 8 = 8 * k + c + 16`] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[NONOVERLAPPING_CLAUSES] THEN ASM_ARITH_TAC);;

(* ========================================================================= *)
(* STEP 1c - AES256_GCM_ENC_ALT_FIXED_CORRECT_G1: the g=1                  *)
(* leg (loop_count = 0, i.e. nblocks 9..16).  At g=1 the main loop is        *)
(* SKIPPED (the 2nd setup guard b.ge@0x4bc is TAKEN, SETUP_G1 lands directly *)
(* at pc+0xa10 = PREPRETAIL).  So this is GEN_CORRECT's 4-leg compose        *)
(* MINUS the MAIN_LOOP SEQUENCE 2: SETUP_G1 -> PREPRETAIL_GEN(k=0) ->        *)
(* TAIL_REM (g = 0+1, r = nb-8).  SETUP_G1 post @0xa10 == GEN_CORRECT        *)
(* SEQ2-mid at k:=0 (boundary check), so all mids/ISPECL are written in      *)
(* literal-0 form.  Buffer bound `val in_p + 16*nb < 2 EXP 63` carried for   *)
(* TAIL_REM.                                                                 *)
(* ========================================================================= *)
let AES256_GCM_ENC_ALT_FIXED_CORRECT_G1 = prove
 (`!in_p out_p tag_p ivec_p key_p htable_p stackpointer bit_len end_p
     tag0 nonce c rk inblock nb k pc.
    k = 0 /\
    8 * (0 + 1) <= nb /\
    bit_len = 128 * nb /\
    8 * (0 + 1) < nb /\ nb <= 8 * (0 + 2) /\
    val in_p + 16 * nb < 2 EXP 63 /\
    end_p = word_add in_p (word (128 * (0 + 1))) /\
    val in_p + 128 * (0 + 1) < 2 EXP 63 /\
    128 * nb < 2 EXP 64 /\
    nonoverlapping (out_p, 16 * nb)
                   (word pc, LENGTH aes256_gcm_enc_alt_tmc) /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
      [(word pc, LENGTH aes256_gcm_enc_alt_tmc);
       (in_p, 16 * nb); (key_p, 240); (htable_p, 192);
       (word_add stackpointer (word 0x40), 8)] /\
    PAIRWISE nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) aes256_gcm_enc_alt_tmc /\
           read PC s = word (pc + 0x38) /\
           read X0 s = in_p /\
           read X1 s = word bit_len /\
           read X2 s = out_p /\
           read X3 s = tag_p /\
           read X16 s = ivec_p /\
           read X6 s = htable_p /\
           read X11 s = key_p /\
           read X9 s = word (bit_len DIV 8) /\
           read X10 s = word_add stackpointer (word 0x40) /\
           read (memory :> bytes64 (word_add stackpointer (word 0x40))) s =
             word 0xc200000000000000 /\
           wordlist_from_memory(key_p,15) s = MAP (word_reversefields 8) rk /\
           read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce c) /\
           htable_mem_8 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j))
      (\s. read PC s = word (pc + 0x1154) /\
           read X9 s = word (16 * nb) /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce (nb + c)) /\
           read (memory :> bytes128 tag_p) s =
             word_reversefields 8
               (nist_ghash (aes256_cipher (word 0) rk) tag0
                  (list_of_seq (nist_cipher_block aes256_cipher c nonce rk inblock) nb)) /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block aes256_cipher c nonce rk (j)) (inblock j)))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * nb);
                  memory :> bytes(tag_p, 16);
                  memory :> bytes(ivec_p, 16)])`,
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REWRITE_TAC[LENGTH_WB_MC; ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES] THEN
  REPEAT STRIP_TAC THEN

  (* ===== SEQUENCE 1: SETUP_G1  pc+0x38 -> pc+0xa10 (skips main loop) ===== *)
  ENSURES_SEQUENCE_TAC `pc + 0xa10`
   `\s. read X0 s = word_add in_p (word (128 * (0 + 1))) /\
        read X2 s = word_add out_p (word (128 * (0 + 1))) /\
        read X3 s = tag_p /\
        read X9 s = word (16 * nb) /\
        read X4 s = word_add in_p (word (16 * nb)) /\
        read X16 s = ivec_p /\
        read X5 s = end_p /\
        read X6 s = htable_p /\
        read X10 s = word_add stackpointer (word 0x40) /\
        read X11 s = key_p /\
        read (memory :> bytes64 (word_add stackpointer (word 0x40))) s =
          word 0xc200000000000000 /\
        wordlist_from_memory(key_p,15) s = MAP (word_reversefields 8) rk /\
        read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
        read (memory :> bytes128 ivec_p) s =
          word_reversefields 8 (ctr_block nonce c) /\
        read Q30 s = word_reversefields 32 (ctr_block nonce (8 * 0 + c + 13)) /\
        read Q31 s = word 79228162514264337593543950336 /\
        read Q19 s =
          nist_ghash (aes256_cipher (word 0) rk) tag0
              (list_of_seq (nist_cipher_block aes256_cipher c nonce rk inblock) (8 * 0)) /\
        read Q8 s = word_xor (aes_ctr_block aes256_cipher c nonce rk ((8 * 0 + 0))) (inblock (8 * 0 + 0)) /\
        read Q9 s = word_xor (aes_ctr_block aes256_cipher c nonce rk ((8 * 0 + 1))) (inblock (8 * 0 + 1)) /\
        read Q10 s = word_xor (aes_ctr_block aes256_cipher c nonce rk ((8 * 0 + 2))) (inblock (8 * 0 + 2)) /\
        read Q11 s = word_xor (aes_ctr_block aes256_cipher c nonce rk ((8 * 0 + 3))) (inblock (8 * 0 + 3)) /\
        read Q12 s = word_xor (aes_ctr_block aes256_cipher c nonce rk ((8 * 0 + 4))) (inblock (8 * 0 + 4)) /\
        read Q13 s = word_xor (aes_ctr_block aes256_cipher c nonce rk ((8 * 0 + 5))) (inblock (8 * 0 + 5)) /\
        read Q14 s = word_xor (aes_ctr_block aes256_cipher c nonce rk ((8 * 0 + 6))) (inblock (8 * 0 + 6)) /\
        read Q15 s = word_xor (aes_ctr_block aes256_cipher c nonce rk ((8 * 0 + 7))) (inblock (8 * 0 + 7)) /\
        read Q0 s = word_reversefields 8 (ctr_block nonce (8 * 0 + c + 8)) /\
        read Q1 s = word_reversefields 8 (ctr_block nonce (8 * 0 + c + 9)) /\
        read Q2 s = word_reversefields 8 (ctr_block nonce (8 * 0 + c + 10)) /\
        read Q3 s = word_reversefields 8 (ctr_block nonce (8 * 0 + c + 11)) /\
        read Q4 s = word_reversefields 8 (ctr_block nonce (8 * 0 + c + 12)) /\
        htable_mem_8 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s /\
        (!j. j < nb
             ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                 inblock j) /\
        (!j. j < 8 * (0 + 1)
             ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                 word_xor (aes_ctr_block aes256_cipher c nonce rk (j)) (inblock j))` THEN
  CONJ_TAC THENL
   [(* SETUP leg *)
    MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN
    EXISTS_TAC
     `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
      MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
      MAYCHANGE [memory :> bytes(out_p, 16 * nb)]` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
      REPEAT (GEN_REWRITE_TAC ONCE_DEPTH_CONV [GSYM SEQ_ASSOC] THEN
              MATCH_MP_TAC SUBSUMED_SEQ THEN REWRITE_TAC[SUBSUMED_REFL]) THEN
      SUBSUMED_MAYCHANGE_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL
     [`in_p:int64`; `out_p:int64`; `tag_p:int64`; `ivec_p:int64`;
      `key_p:int64`; `htable_p:int64`; `stackpointer:int64`; `bit_len:num`;
      `end_p:int64`; `tag0:int128`; `nonce:(96)word`; `c:num`; `rk:int128 list`;
      `inblock:num->int128`; `nb:num`; `0`; `pc:num`]
     AES256_GCM_ENC_ALT_SETUP_G1) THEN
    REWRITE_TAC[LENGTH_WB_MC; ALLPAIRS; ALL; NONOVERLAPPING_CLAUSES] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[NONOVERLAPPING_CLAUSES] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN

  (* ============ SEQUENCE 3: PREPRETAIL  pc+0xa10 -> pc+0xee0 (option D) === *)
  (* mid-state = ?v18 v27. read Q18 = v18 /\ read Q27 = v27 /\ <PP-post-body>. *)
  (* Build the join predicate: PREPRETAIL's postcondition body (the           *)
  (* postcondition of AES256_GCM_ENC_ALT_PREPRETAIL_GEN, mod_p ->             *)
  (* stackpointer+0x40) wrapped in ?v18 v27 + the pins.                       *)
  (* mid-state OMITS aligned+PC (auto-added).  The existential wraps the pins   *)
  (* + the PP-post body (minus tag-in-mem).  For ENSURES_EXISTS2_PRECONDITION to *)
  (* match on the TAIL leg, the `?v18 v27.` must be the OUTERMOST structure of   *)
  (* the `Q s` remainder - but the tactic wraps it as `aligned /\ PC /\ (?..)`.  *)
  (* NOTE-live: the auto-added aligned+PC sit OUTSIDE the ?; so on the TAIL leg  *)
  (* the precondition is `\s. aligned s /\ read PC s=.. /\ (?v18 v27. ...)`, and *)
  (* ENSURES_EXISTS2_PRECONDITION won't match directly.  Handle by first        *)
  (* SWAPPING: pull the ? outward, OR strip aligned+PC into asms via            *)
  (* ENSURES_PRECONDITION + a lambda that moves ? out (?v w. aligned/\PC/\body). *)
  (* Simplest live fix: make the mid-state itself `\s. ?v18 v27. read Q18 s=v18  *)
  (* /\ ... /\ <body>` and rely on the tactic adding aligned/PC OUTSIDE, then on *)
  (* the TAIL leg do `REWRITE_TAC[RIGHT_EXISTS_AND_THM/LEFT_EXISTS_AND_THM] o.a. *)
  (* to hoist the ? to the top before MATCH_MP_TAC ENSURES_EXISTS2_PRECONDITION. *)
  ENSURES_SEQUENCE_TAC `pc + 0xee0`
   `\s. ?v18 v27.
        read Q18 s = v18 /\ read Q27 s = v27 /\
        read X0 s = word_add in_p (word (128 * (0 + 1))) /\
        read X2 s = word_add out_p (word (128 * (0 + 1))) /\
        read X3 s = tag_p /\
        read X9 s = word (16 * nb) /\
        read X4 s = word_add in_p (word (16 * nb)) /\
        read X16 s = ivec_p /\
        read X5 s = end_p /\
        read X6 s = htable_p /\
        read X10 s = word_add stackpointer (word 0x40) /\
        read X11 s = key_p /\
        read (memory :> bytes64 (word_add stackpointer (word 0x40))) s =
          word 0xc200000000000000 /\
        wordlist_from_memory(key_p,15) s = MAP (word_reversefields 8) rk /\
        read (memory :> bytes128 ivec_p) s =
          word_reversefields 8 (ctr_block nonce c) /\
        read Q28 s = word_reversefields 8 (EL 14 rk) /\
        read Q30 s = word_reversefields 32 (ctr_block nonce (8 * 0 + c + 16)) /\
        read Q31 s = word 79228162514264337593543950336 /\
        read Q19 s =
          nist_ghash (aes256_cipher (word 0) rk) tag0
              (list_of_seq (nist_cipher_block aes256_cipher c nonce rk inblock) (8 * (0 + 1))) /\
        word_xor (read Q0 s) (word_reversefields 8 (EL 14 rk)) =
          word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * 0 + c + 8)) rk) /\
        word_xor (read Q1 s) (word_reversefields 8 (EL 14 rk)) =
          word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * 0 + c + 9)) rk) /\
        word_xor (read Q2 s) (word_reversefields 8 (EL 14 rk)) =
          word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * 0 + c + 10)) rk) /\
        word_xor (read Q3 s) (word_reversefields 8 (EL 14 rk)) =
          word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * 0 + c + 11)) rk) /\
        word_xor (read Q4 s) (word_reversefields 8 (EL 14 rk)) =
          word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * 0 + c + 12)) rk) /\
        word_xor (read Q5 s) (word_reversefields 8 (EL 14 rk)) =
          word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * 0 + c + 13)) rk) /\
        word_xor (read Q6 s) (word_reversefields 8 (EL 14 rk)) =
          word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * 0 + c + 14)) rk) /\
        word_xor (read Q7 s) (word_reversefields 8 (EL 14 rk)) =
          word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * 0 + c + 15)) rk) /\
        htable_mem_8 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s /\
        (!j. j < nb
             ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                 inblock j) /\
        (!j. j < 8 * (0 + 1)
             ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                 word_xor (aes_ctr_block aes256_cipher c nonce rk (j)) (inblock j))` THEN
  CONJ_TAC THENL
   [(* PREPRETAIL leg: apply PREPRETAIL, then weaken its post to the           *)
    (* existential mid-state (EXISTS the actual Q18/Q27 reads).                *)
    MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN
    EXISTS_TAC
     `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
      MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
      MAYCHANGE [memory :> bytes(out_p, 16 * nb)]` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
      REPEAT (GEN_REWRITE_TAC ONCE_DEPTH_CONV [GSYM SEQ_ASSOC] THEN
              MATCH_MP_TAC SUBSUMED_SEQ THEN REWRITE_TAC[SUBSUMED_REFL]) THEN
      SUBSUMED_MAYCHANGE_TAC;
      ALL_TAC] THEN
    (* Weaken the GOAL's post from Q_mid (the ?-existential) to PREPRETAIL's    *)
    (* actual post via ENSURES_POSTCONDITION_TAC (canonical idiom, robust:      *)
    (* it MATCH_MP_TAC's ENSURES_POSTCONDITION_THM + EXISTS_TAC the given post). *)
    (* This leaves TWO subgoals: (1) the pointwise implication PP_post ==>       *)
    (* Q_mid (closed by EXISTS_TAC (read Q18/Q27 s) + ASM_REWRITE), and (2)      *)
    (* `ensures arm PP_pre PP_post frame` = PREPRETAIL applied.                  *)
    (* NB the PP_post lambda passed here must OMIT the aligned+PC (the tactic    *)
    (* handles PC via the ensures) - actually pass PREPRETAIL's FULL post        *)
    (* (the postcondition of AES256_GCM_ENC_ALT_PREPRETAIL_GEN: read PC .. /\    *)
    (* body), i.e. exactly PREPRETAIL's post.                                    *)
    ENSURES_POSTCONDITION_TAC
     `\s. aligned_bytes_loaded s (word pc) aes256_gcm_enc_alt_tmc /\
          read PC s = word (pc + 0xee0) /\
          read X0 s = word_add in_p (word (128 * (0 + 1))) /\
          read X2 s = word_add out_p (word (128 * (0 + 1))) /\
          read X3 s = tag_p /\ read X9 s = word (16 * nb) /\ read X4 s = word_add in_p (word (16 * nb)) /\
          read X16 s = ivec_p /\ read X5 s = end_p /\ read X6 s = htable_p /\
          read X10 s = word_add stackpointer (word 0x40) /\ read X11 s = key_p /\
          read (memory :> bytes64 (word_add stackpointer (word 0x40))) s =
            word 0xc200000000000000 /\
          wordlist_from_memory(key_p,15) s = MAP (word_reversefields 8) rk /\
          read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
          read (memory :> bytes128 ivec_p) s = word_reversefields 8 (ctr_block nonce c) /\
          read Q28 s = word_reversefields 8 (EL 14 rk) /\
          read Q30 s = word_reversefields 32 (ctr_block nonce (8 * 0 + c + 16)) /\
          read Q31 s = word 79228162514264337593543950336 /\
          read Q19 s = nist_ghash (aes256_cipher (word 0) rk) tag0
              (list_of_seq (nist_cipher_block aes256_cipher c nonce rk inblock) (8 * (0 + 1))) /\
          word_xor (read Q0 s) (word_reversefields 8 (EL 14 rk)) =
            word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * 0 + c + 8)) rk) /\
          word_xor (read Q1 s) (word_reversefields 8 (EL 14 rk)) =
            word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * 0 + c + 9)) rk) /\
          word_xor (read Q2 s) (word_reversefields 8 (EL 14 rk)) =
            word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * 0 + c + 10)) rk) /\
          word_xor (read Q3 s) (word_reversefields 8 (EL 14 rk)) =
            word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * 0 + c + 11)) rk) /\
          word_xor (read Q4 s) (word_reversefields 8 (EL 14 rk)) =
            word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * 0 + c + 12)) rk) /\
          word_xor (read Q5 s) (word_reversefields 8 (EL 14 rk)) =
            word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * 0 + c + 13)) rk) /\
          word_xor (read Q6 s) (word_reversefields 8 (EL 14 rk)) =
            word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * 0 + c + 14)) rk) /\
          word_xor (read Q7 s) (word_reversefields 8 (EL 14 rk)) =
            word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * 0 + c + 15)) rk) /\
          htable_mem_8 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s /\
          (!j. j < nb ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s = inblock j) /\
          (!j. j < 8 * (0 + 1) ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                 word_xor (aes_ctr_block aes256_cipher c nonce rk (j)) (inblock j))` THEN
    CONJ_TAC THENL
     [(* (1) PP_post(aug) ==> Q_mid.  PREPRETAIL is augmented with aligned in    *)
      (* its post, so ENSURES_POSTCONDITION_TAC's antecedent lambda (above) also  *)
      (* carries aligned.  X_GEN_TAC forces the state var to `s` (so the pin      *)
      (* witnesses match); BETA_TAC reduces BOTH the antecedent redex `(\s.OLD)s` *)
      (* and the consequent redex `(\s.MID)s` BEFORE STRIP_TAC - critical: if     *)
      (* STRIP runs first it stashes the antecedent as ONE unreduced redex and    *)
      (* aligned never lands in the asms.  Then REPEAT(CONJ_TAC ...) peels the     *)
      (* aligned + PC conjuncts (both now in asms) off the mid's conjunction and   *)
      (* EXISTS the actual Q18/Q27 reads on the residual existential.             *)
      X_GEN_TAC `s:armstate` THEN BETA_TAC THEN STRIP_TAC THEN
      REPEAT(CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC]) THEN
      EXISTS_TAC `read Q18 s:int128` THEN EXISTS_TAC `read Q27 s:int128` THEN
      ASM_REWRITE_TAC[];
      (* (2) ensures PP_pre PP_post frame = PREPRETAIL applied.                *)
      MP_TAC(ISPECL
       [`in_p:int64`; `out_p:int64`; `tag_p:int64`; `ivec_p:int64`;
        `key_p:int64`; `htable_p:int64`; `word_add stackpointer (word 0x40):int64`;
        `end_p:int64`; `tag0:int128`; `nonce:(96)word`; `c:num`; `rk:int128 list`;
        `inblock:num->int128`; `nb:num`; `0`; `pc:num`]
       AES256_GCM_ENC_ALT_PREPRETAIL_GEN) THEN
      REWRITE_TAC[LENGTH_WB_MC; ALLPAIRS; ALL; NONOVERLAPPING_CLAUSES] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[NONOVERLAPPING_CLAUSES] THEN ASM_ARITH_TAC];
    (* NOTE-live: ENSURES_POSTCONDITION_TAC's post lambda must MATCH PP's post   *)
    (* modulo the frame - PC-conjunct kept, aligned dropped (post has no aligned)*)
    (* If the tactic rejects the shape, fall back to MP_TAC PP + IMP_CONJ +      *)
    (* ENSURES_POSTCONDITION_THM as before.  Pins close by REFL (EXISTS read Qn).*)
    ALL_TAC] THEN

  (* ============ TAIL leg: pc+0xee0 -> pc+0x1154 ============ *)
  (* Precondition now carries ?v18 v27. Strip it via the helper, apply TAIL   *)
  (* SPEC'd to v18/v27.  MATCH_MP_TAC ENSURES_EXISTS2_PRECONDITION turns the   *)
  (* goal `ensures step (\s. ?v18 v27. read Q18 s=v18 /\ read Q27 s=v27 /\ B)  *)
  (* post frame` into `!v18 v27. ensures step (\s. read Q18=v18 /\ ... /\ B)`. *)
  (* NOTE the mid-state must be syntactically `\s. ?v18 v27. read Q18 s=v18 /\ *)
  (* read Q27 s=v27 /\ <body>` for the helper's `\s. ?v w. P v w s` to match   *)
  (* (P v w s = read Q18 s=v /\ read Q27 s=w /\ body).  It is (built above).   *)
  (* BUT ENSURES_SEQUENCE_TAC auto-wrapped the precondition as                 *)
  (*   `\s. aligned_bytes_loaded .. /\ read PC s = word(pc+0xee0) /\ (?v w. B)` *)
  (* so the `?` is NOT outermost.  Hoist it out FIRST with GSYM               *)
  (* RIGHT_EXISTS_AND_THM (`P /\ (?x. Q x)` -> `?x. P /\ Q x`), applied under   *)
  (* the \s. binder (REWRITE descends), so the precondition becomes            *)
  (*   `\s. ?v w. aligned .. /\ read PC .. /\ B` and the helper matches.        *)
  (* If the aligned/PC conjuncts don't fully hoist, also try LEFT_EXISTS_AND_  *)
  (* THM / GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV).                       *)
  REWRITE_TAC[GSYM RIGHT_EXISTS_AND_THM; GSYM LEFT_EXISTS_AND_THM] THEN
  MATCH_MP_TAC ENSURES_EXISTS2_PRECONDITION THEN
  MAP_EVERY X_GEN_TAC [`v18:int128`; `v27:int128`] THEN
  MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN
  EXISTS_TAC
   `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
    MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
    MAYCHANGE [memory :> bytes(out_p, 16 * nb);
               memory :> bytes(tag_p, 16);
               memory :> bytes(ivec_p, 16)]` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    REPEAT (GEN_REWRITE_TAC ONCE_DEPTH_CONV [GSYM SEQ_ASSOC] THEN
            MATCH_MP_TAC SUBSUMED_SEQ THEN REWRITE_TAC[SUBSUMED_REFL]) THEN
    SUBSUMED_MAYCHANGE_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`v18:int128`; `v27:int128`;
    `in_p:int64`; `out_p:int64`; `tag_p:int64`; `ivec_p:int64`;
    `key_p:int64`; `htable_p:int64`; `word_add stackpointer (word 0x40):int64`;
    `end_p:int64`; `tag0:int128`; `nonce:(96)word`; `c:num`; `rk:int128 list`;
    `inblock:num->int128`; `nb:num`; `nb - 8 * (0 + 1)`; `0 + 1`; `pc:num`]
   AES256_GCM_ENC_ALT_TAIL_REM) THEN
  REWRITE_TAC[LENGTH_WB_MC; ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES] THEN
  (* c-form counter alignment (g:=0+1), as GEN_CORRECT: these c-carrying
     ARITH_RULEs rewrite 8*(0+1)+c+N to 8*0+c+(N+8). *)
  REWRITE_TAC[ARITH_RULE `8 * (0 + 1) + c = 8 * 0 + c + 8`;
              ARITH_RULE `8 * (0 + 1) + c + 1 = 8 * 0 + c + 9`;
              ARITH_RULE `8 * (0 + 1) + c + 2 = 8 * 0 + c + 10`;
              ARITH_RULE `8 * (0 + 1) + c + 3 = 8 * 0 + c + 11`;
              ARITH_RULE `8 * (0 + 1) + c + 4 = 8 * 0 + c + 12`;
              ARITH_RULE `8 * (0 + 1) + c + 5 = 8 * 0 + c + 13`;
              ARITH_RULE `8 * (0 + 1) + c + 6 = 8 * 0 + c + 14`;
              ARITH_RULE `8 * (0 + 1) + c + 7 = 8 * 0 + c + 15`;
              ARITH_RULE `8 * (0 + 1) + c + 8 = 8 * 0 + c + 16`] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[NONOVERLAPPING_CLAUSES] THEN ASM_ARITH_TAC);;

(* ========================================================================= *)
(* STEP 5b - AES256_GCM_ENC_ALT_NOIBT_SUBROUTINE_CORRECT.                  *)
(* The externally-used spec: lifts CORRECT through the 2 entry guards,       *)
(* the d8-d15 save/restore frame (80 bytes), and the final RET.              *)
(*                                                                           *)
(* Wrapper shape (disasm-verified against the object):                       *)
(*      PROLOGUE 0x00 cbz x1,0x1170 ; 0x04 tst x1,#0x7f ; 0x08 b.ne 0x1170 ; *)
(*        0x0c sub sp,#0x50 ; stp d8..d15 ; lsr x9,x1,#3 ; mov x16,x4 ;      *)
(*        mov x11,x5 ; mov x5,#0xc2..; stp x5,xzr,[sp,#64] ; add             *)
(*          x10,sp,#0x40;                                                    *)
(*        0x38 = CORE ENTRY (CORRECT).                                       *)
(*      EPILOGUE 0x1154 mov x0,x9 ; ldp d8..d15 ; add sp,#0x50 ; 0x116c ret. *)
(*      RETURN-0 0x1170 mov w0,#0 ; ret (NOT reached under the precond).     *)
(* Entry C-ABI: X0=in_p X1=bit_len X2=out_p X3=tag_p X4=ivec_p X5=key_p      *)
(*      X6=htable_p; prologue moves X4->X16, X5->X11, x9=X1>>3.              *)
(*                                                                           *)
(* Not a clean ARM_ADD_RETURN_STACK_TAC: its internal ARM_STEPS (1--pre_n)   *)
(* would hit the 2 CONDITIONAL guards (cbz/b.ne) and leave a conditional PC. *)
(* So it is HAND-ASSEMBLED (option i) - the guards fall through under the    *)
(* precond, discharged by WB_GUARD1/2_..._GEN below.                         *)
(* ========================================================================= *)

(* GUARD1: cbz x1 does NOT branch - X1 = word (128*nb) is nonzero, since nb  *)
(* = 8*(k+2) >= 16 > 0 and 128*nb < 2 EXP 64 (so val = 128*nb).              *)
let WB_X9_NORM = prove
 (`128 * nb < 2 EXP 64
   ==> word_ushr (word (128 * nb):int64) 3 = word ((128 * nb) DIV 8)`,
  STRIP_TAC THEN REWRITE_TAC[word_ushr] THEN AP_TERM_TAC THEN
  REWRITE_TAC[ARITH_RULE `2 EXP 3 = 8`] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC);;

(* ========================================================================= *)
(* GENERALIZATION - functional correctness over all whole-block counts       *)
(* nblocks >= 0.                                                             *)
(* ========================================================================= *)

(* ---- loop_count = 0 branch mechanics (nblocks in 1..8)                    *)
(* --------------------- When groups = (nb-1) DIV 8 = 0 (i.e. nb <= 8), the  *)
(* round-down end pointer x5 = in_p + ((16*nb - 1) AND ~0x7f) collapses to   *)
(* in_p, because 16*nb-1 <= 127 (< 128 = 2^7), so masking off the low 7 bits *)
(* gives 0.  Then `cmp x0,x5; b.ge`@0x44c (x0 = in_p) is TAKEN, skipping the *)
(* whole main loop and jumping straight to the tail cascade at pc+0xee0.     *)
(* These two lemmas are the analogues of SETUP_BRANCH_COND_FALSE /           *)
(* X5_END_PTR for the groups=0 leg - there the branch FALLS THROUGH          *)
(* (groups>=2); here it is TAKEN.                                            *)

(* x5 (rounded-down last-full-group ptr) = in_p for nb in 1..8.              *)
let WB_X5_GROUPS0 = prove
 (`!(in_p:int64) nb.
     1 <= nb /\ nb <= 8
     ==> word_add
           (word_and (word_sub (word ((128 * nb) DIV 8)) (word 1))
                     (word 18446744073709551488))
           in_p = in_p`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(128 * nb) DIV 8 = 16 * nb` SUBST1_TAC THENL
   [ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `word_sub (word (16 * nb)) (word 1):int64 = word (16 * nb - 1)`
    SUBST1_TAC THENL
   [REWRITE_TAC[WORD_SUB] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `word 18446744073709551488:int64 = word_not (word (2 EXP 7 - 1))`
    SUBST1_TAC THENL
   [CONV_TAC(RAND_CONV(RAND_CONV(RAND_CONV NUM_REDUCE_CONV))) THEN
    CONV_TAC WORD_BLAST; ALL_TAC] THEN
  REWRITE_TAC[WORD_AND_NOT_MASK_WORD] THEN
  SUBGOAL_THEN `val(word (16 * nb - 1):int64) DIV 2 EXP 7 = 0` SUBST1_TAC THENL
   [MATCH_MP_TAC DIV_LT THEN
    SUBGOAL_THEN `val(word (16 * nb - 1):int64) = 16 * nb - 1` SUBST1_TAC THENL
     [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC;
      ASM_ARITH_TAC];
    REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0]]);;

(* The b.ge@0x44c condition (the exact NF!=VF biconditional the stepper      *)
(* emits for `cmp x0,x5` with x0 = in_p) collapses to T for nb in 1..8, so   *)
(* the conditional PC resolves to the tail entry pc+0xee0.                   *)
let WB_BRANCH_COND_TRUE = prove
 (`!(in_p:int64) nb.
     1 <= nb /\ nb <= 8
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
                      in_p)))) <=> T)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[WB_X5_GROUPS0] THEN
  REWRITE_TAC[WORD_SUB_REFL; INT_SUB_REFL; IVAL_WORD_0] THEN
  INT_ARITH_TAC);;

(* ========================================================================= *)
(* GENERALIZATION ARC (nblocks>=0): SETUP0 - the loop_count=0 setup leg.     *)
(*                                                                           *)
(* For 1 <= nblocks <= 8 (groups = (nb-1) DIV 8 = 0) the b.ge@0x44c is TAKEN *)
(* (WB_BRANCH_COND_TRUE), so the main loop is SKIPPED: setup runs pc+0x38 -> *)
(* pc+0xee0 (the tail entry) building the 8 CTR keystreams Q0..Q7 (ctr idx   *)
(* 2..9), the next-group counter Q30 = ctr_block nonce 10, and Q19 = the     *)
(* untouched GHASH accumulator = nist_ghash..[] = tag0.  This is the branch- *)
(* TAKEN analogue of SETUP_GEN (which falls through to the main loop for     *)
(* groups>=2).  The postcondition is the tail's precondition reindexed to    *)
(* groups=0 (Q0..Q7 pre-rk14 keystreams, Q30=10, Q19=[], X5=in_p, out-forall *)
(* j<0 vacuous), so the generalized tail-cascade leg composes with it via    *)
(* ENSURES_SEQUENCE_TAC.                                                     *)
(*                                                                           *)
(* Drive = SETUP_GEN's drive truncated at the branch: NSTEP(1--253) + NSTEP  *)
(* 254 (the b.ge) + WB_BRANCH_COND_TRUE resolves PC to pc+0xee0.  Closers    *)
(* : keystreams via KSCLOSE (AES256_CIPHER_RECONSTRUCT +                     *)
(* CTR_BLOCK_RECONSTRUCT_REV8 + ctr_block/WORD_BLAST); Q30 via the index-10  *)
(* lane lemma SETUP_Q30_LANES_10 (the +7+1=8 analogue of SETUP_Q30_LANES) +  *)
(* CTR_BLOCK_RECONSTRUCT_REV32; Q19 via NIST_GHASH_NIL; X4 via the word_ushr *)
(* /MOD_LT bridge; X5 via WB_X5_GROUPS0.                                     *)
(* ========================================================================= *)

(* SETUP_Q30_LANES_10: the index-10 counter lane lemma (base+7+1=8 => nonce  *)
(* 10).                                                                      *)
let SETUP_Q30_LANES_10 = prove
 (`(word_add (word_add
      (word_reversefields 8
        (word_subword (word_reversefields 8 (ctr_block nonce c)) (96,32):int32))
      (word 7)) (word 1):int32 = word (c + 8)) /\
   (word_add (word_reversefields 8
      (word_subword (word_reversefields 8 (ctr_block nonce c)) (64,32):int32)) (word 0):int32
    = word_subword nonce (0,32)) /\
   (word_add (word_reversefields 8
      (word_subword (word_reversefields 8 (ctr_block nonce c)) (32,32):int32)) (word 0):int32
    = word_subword nonce (32,32)) /\
   (word_add (word_reversefields 8
      (word_subword (word_reversefields 8 (ctr_block nonce c)) (0,32):int32)) (word 0):int32
    = word_subword nonce (64,32))`,
  SUBGOAL_THEN
    `word_reversefields 8
       (word_subword (word_reversefields 8 (ctr_block nonce c)) (96,32):int32) =
     word c:int32`
    ASSUME_TAC THENL
   [REWRITE_TAC[ctr_block] THEN
    SPEC_TAC(`word c:int32`,`wc:int32`) THEN GEN_TAC THEN CONV_TAC WORD_BLAST;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [CONV_TAC WORD_RULE;
    REWRITE_TAC[ctr_block] THEN
    SPEC_TAC(`word c:int32`,`wc:int32`) THEN GEN_TAC THEN CONV_TAC WORD_BLAST]);;

(* Keystream closer (KSCLOSE): the pre-rk14 aese chain                       *)
(* register Qj, XORed with rk14, is rev8(aes256_cipher(ctr_block nonce       *)
(* (c+j)) rk).                                                               *)
(* symbolic-c: a direct `REWRITE_TAC[ctr_block] THEN CONV_TAC WORD_BLAST`
   blasts a full 128-bit symbolic-c counter term and is too expensive, so the closer
   instead mirrors the PROVEN CIPHER_CLOSE structural reconstruction (minus the
   input-XOR reorder, since the keystream register is not XORed with an input block):
   fold the aese chain to
   aes256_cipher, reconstruct the AES-input counter lanes to ctr_block nonce K
   (CTR_LANE_LOW + CTR_NONCE_LANES + GSYM WORD_ADD + CTR_BLOCK_RECONSTRUCT_REV8/32,
   then cancel the double reverse), refold both sides to aes_ctr_block, and discharge
   the arith-equal counter index K = c+j by ARITH. *)
let KSCLOSE =
  ASM_REWRITE_TAC[AES256_CIPHER_RECONSTRUCT; MAP;
                  WORD_REVERSEFIELDS_REVERSEFIELDS; AES256_CIPHER_KEYLIST] THEN
  REWRITE_TAC[CTR_LANE_LOW; CTR_NONCE_LANES] THEN
  REWRITE_TAC[GSYM WORD_ADD; WORD_ADD_0] THEN
  REWRITE_TAC[CTR_BLOCK_RECONSTRUCT_REV8; CTR_BLOCK_RECONSTRUCT_REV32] THEN
  REWRITE_TAC[WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
  REWRITE_TAC[AES256_CIPHER_KEYLIST] THEN
  REWRITE_TAC[aes_ctr_block; ADD_CLAUSES] THEN
  REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES] THEN
  TRY(REFL_TAC) THEN
  TRY(REPEAT(AP_THM_TAC ORELSE AP_TERM_TAC) THEN ARITH_TAC);;

(* Q30 counter closer (next-group counter, index c+8).                       *)
(* symbolic-c: identical to the PROVEN CTR_CLOSE (Q30 rev32 reconstruction)
   but with the index-(c+8) lane lemma SETUP_Q30_LANES_10 in place of SETUP_Q30_LANES.
   Reconstruct the counter lanes structurally, then AP-peel + ARITH the arith-equal
   index; NO full-term WORD_BLAST (which hangs on the symbolic-c 128-bit term). *)
let SETUP0_CTR_CLOSE =
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[SETUP_Q30_LANES_10; CTR_LANE_LOW] THEN
  REWRITE_TAC[WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
  REWRITE_TAC[CTR_NONCE_LANES] THEN
  REWRITE_TAC[GSYM WORD_ADD; WORD_ADD_0] THEN
  REWRITE_TAC[CTR_BLOCK_RECONSTRUCT_REV8; CTR_BLOCK_RECONSTRUCT_REV32] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;;

(* Q19 init closer: nist_ghash over the empty list = tag0.                   *)
let SETUP0_Q19_CLOSE =
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[list_of_seq; NIST_GHASH_NIL] THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC WORD_BLAST;;

(* Shape-routed dispatcher for the groups=0 setup postcond.                  *)
let SETUP0_DISPATCH : tactic = fun (asl,w as gl) ->
  if is_forall w then
    (* the input-forall (j<nb) and the vacuous out-forall (j<0) *)
    (REWRITE_TAC[ARITH_RULE `j < 8 * 0 <=> F`] THEN ASM_REWRITE_TAC[]) gl
  else if is_eq w then
    let l,r = dest_eq w in
    let rhd = try fst(dest_const(fst(strip_comb r))) with _ -> "?" in
    let lhd = try fst(dest_const(fst(strip_comb l))) with _ -> "?" in
    if rhd = "nist_ghash" then SETUP0_Q19_CLOSE gl
    else if lhd = "word_join" && rhd = "word_reversefields" then SETUP0_CTR_CLOSE gl
    else if lhd = "word_xor" then KSCLOSE gl
    else if lhd = "word_add" && rhd = "word_add" then
      (* X4: word_add in_p (word_ushr(word(128*nb))3) = word_add in_p (word(16*nb)). *)
      (AP_TERM_TAC THEN REWRITE_TAC[word_ushr; VAL_WORD; DIMINDEX_64] THEN
       AP_TERM_TAC THEN ASM_SIMP_TAC[MOD_LT] THEN ARITH_TAC) gl
    else if lhd = "word_add" then
      (* X5: word_add (round-down expr) in_p = in_p (via WB_X5_GROUPS0). *)
      ASM_SIMP_TAC[WB_X5_GROUPS0] gl
    else (* incl. the X9 count: word((128*nb) DIV 8) -> word(16*nb) *)
      ASM_REWRITE_TAC[ARITH_RULE `(128 * nb) DIV 8 = 16 * nb`] gl
  else ASM_REWRITE_TAC[] gl;;

let AES256_GCM_ENC_ALT_SETUP0 = prove
 (`!in_p out_p tag_p ivec_p key_p htable_p stackpointer bit_len
     tag0 nonce c rk inblock nb pc.
    1 <= nb /\ nb <= 8 /\ ~(nb = 2) /\ ~(nb = 4) /\ ~(nb = 1) /\ ~(nb = 3) /\
    bit_len = 128 * nb /\
    val in_p + 16 * nb < 2 EXP 63 /\
    128 * nb < 2 EXP 64 /\
    nonoverlapping (out_p, 16 * nb)
                   (word pc, LENGTH aes256_gcm_enc_alt_tmc) /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * nb)]
      [(in_p, 16 * nb); (key_p, 240); (htable_p, 192);
       (tag_p, 16); (ivec_p, 16); (word_add stackpointer (word 0x40), 8)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) aes256_gcm_enc_alt_tmc /\
           read PC s = word (pc + 0x38) /\
           read X0 s = in_p /\
           read X1 s = word bit_len /\
           read X2 s = out_p /\
           read X3 s = tag_p /\
           read X16 s = ivec_p /\
           read X6 s = htable_p /\
           read X11 s = key_p /\
           read X9 s = word (bit_len DIV 8) /\
           read X10 s = word_add stackpointer (word 0x40) /\
           read (memory :> bytes64 (word_add stackpointer (word 0x40))) s =
             word 0xc200000000000000 /\
           wordlist_from_memory(key_p,15) s = MAP (word_reversefields 8) rk /\
           read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce c) /\
           htable_mem_8 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j))
      (\s. aligned_bytes_loaded s (word pc) aes256_gcm_enc_alt_tmc /\
           read PC s = word (pc + 0xee0) /\
           read X0 s = in_p /\
           read X2 s = out_p /\
           read X3 s = tag_p /\
           read X9 s = word (16 * nb) /\
           read X4 s = word_add in_p (word (16 * nb)) /\
           read X16 s = ivec_p /\
           read X5 s = in_p /\
           read X6 s = htable_p /\
           read X10 s = word_add stackpointer (word 0x40) /\
           read X11 s = key_p /\
           read (memory :> bytes64 (word_add stackpointer (word 0x40))) s =
             word 0xc200000000000000 /\
           wordlist_from_memory(key_p,15) s = MAP (word_reversefields 8) rk /\
           read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce c) /\
           read Q28 s = word_reversefields 8 (EL 14 rk) /\
           read Q30 s = word_reversefields 32 (ctr_block nonce (c + 8)) /\
           read Q31 s = word 79228162514264337593543950336 /\
           read Q19 s =
             nist_ghash (aes256_cipher (word 0) rk) tag0
                 (list_of_seq (nist_cipher_block aes256_cipher c nonce rk inblock) 0) /\
           word_xor (read Q0 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce c) rk) /\
           word_xor (read Q1 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (c + 1)) rk) /\
           word_xor (read Q2 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (c + 2)) rk) /\
           word_xor (read Q3 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (c + 3)) rk) /\
           word_xor (read Q4 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (c + 4)) rk) /\
           word_xor (read Q5 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (c + 5)) rk) /\
           word_xor (read Q6 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (c + 6)) rk) /\
           word_xor (read Q7 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (c + 7)) rk) /\
           htable_mem_8 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j) /\
           (!j. j < 8 * 0
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block aes256_cipher c nonce rk (j)) (inblock j)))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * nb)])`,
  REWRITE_TAC[KEY15_SPLIT] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; ALLPAIRS; ALL;
              NONOVERLAPPING_CLAUSES] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REWRITE_CONV[fst AES256_GCM_ENC_ALT_EXEC]
      `LENGTH aes256_gcm_enc_alt_tmc`]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_8; htable_mem_4]) THEN
  SUBGOAL_THEN `~(nb = 4)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `5 <= nb` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY NSTEP (1--5) THEN NSTEP 6 THEN NSTEP 7 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[
    MATCH_MP DISPATCH4_NOT_TAKEN (CONJ (ASSUME `128 * nb < 2 EXP 64`) (ASSUME `~(nb = 4)`));
    MATCH_MP DISPATCH_SMALL_NOT_TAKEN (CONJ (ASSUME `128 * nb < 2 EXP 64`) (ASSUME `5 <= nb`));
    COND_CLAUSES]) THEN
  MAP_EVERY NSTEP (8--36) THEN
  MAP_EVERY NSTEP (37--261) THEN NSTEP 262 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP WB_BRANCH_COND_TRUE
     (CONJ (ASSUME `1 <= nb`) (ASSUME `nb <= 8`)); COND_CLAUSES]) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[htable_mem_8; htable_mem_4] THEN REPEAT CONJ_TAC THEN SETUP0_DISPATCH);;

(* ========================================================================= *)
(* loop_count=0 leg: compose SETUP0 (pc+0x38 -> pc+0xee0)                    *)
(* with TAIL_REM (rem=nblocks, g=0; pc+0xee0 -> pc+0x1154) via               *)
(* ENSURES_SEQUENCE_TAC at pc+0xee0.  Covers nblocks 1..8 (one full tail     *)
(* group, no main loop).  Q18/Q27 are unpinned at SETUP0's exit -> option-D  *)
(* existential mid-state (mirror of the core PREPRETAIL->TAIL leg).          *)
(* ========================================================================= *)
let AES256_GCM_ENC_ALT_SETUP0_TAIL = prove
 (`!in_p out_p tag_p ivec_p key_p htable_p stackpointer bit_len
     tag0 nonce c rk inblock nb pc.
    1 <= nb /\ nb <= 8 /\ ~(nb = 2) /\ ~(nb = 4) /\ ~(nb = 1) /\ ~(nb = 3) /\
    bit_len = 128 * nb /\
    val in_p + 16 * nb < 2 EXP 63 /\
    128 * nb < 2 EXP 64 /\
    nonoverlapping (out_p, 16 * nb)
                   (word pc, LENGTH aes256_gcm_enc_alt_tmc) /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
      [(word pc, LENGTH aes256_gcm_enc_alt_tmc);
       (in_p, 16 * nb); (key_p, 240); (htable_p, 192);
       (word_add stackpointer (word 0x40), 8)] /\
    PAIRWISE nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) aes256_gcm_enc_alt_tmc /\
           read PC s = word (pc + 0x38) /\
           read X0 s = in_p /\
           read X1 s = word bit_len /\
           read X2 s = out_p /\
           read X3 s = tag_p /\
           read X16 s = ivec_p /\
           read X6 s = htable_p /\
           read X11 s = key_p /\
           read X9 s = word (bit_len DIV 8) /\
           read X10 s = word_add stackpointer (word 0x40) /\
           read (memory :> bytes64 (word_add stackpointer (word 0x40))) s =
             word 0xc200000000000000 /\
           wordlist_from_memory(key_p,15) s = MAP (word_reversefields 8) rk /\
           read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce c) /\
           htable_mem_8 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j))
      (\s. read PC s = word (pc + 0x1154) /\
           read X9 s = word (16 * nb) /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce (nb + c)) /\
           read (memory :> bytes128 tag_p) s =
             word_reversefields 8
               (nist_ghash (aes256_cipher (word 0) rk) tag0
                  (list_of_seq (nist_cipher_block aes256_cipher c nonce rk inblock) nb)) /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block aes256_cipher c nonce rk (j)) (inblock j)))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * nb);
                  memory :> bytes(tag_p, 16);
                  memory :> bytes(ivec_p, 16)])`,
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REWRITE_TAC[LENGTH_WB_MC; ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES] THEN
  REPEAT STRIP_TAC THEN

  (* ===== SEQUENCE: SETUP0  pc+0x38 -> pc+0xee0 (option D) ===== *)
  ENSURES_SEQUENCE_TAC `pc + 0xee0`
   `\s. ?v18 v27.
        read Q18 s = v18 /\ read Q27 s = v27 /\
           read X0 s = word_add in_p (word (128 * 0)) /\
           read X2 s = word_add out_p (word (128 * 0)) /\
           read X3 s = tag_p /\
           read X9 s = word (16 * nb) /\
           read X4 s = word_add in_p (word (16 * nb)) /\
           read X16 s = ivec_p /\
           read X5 s = word_add in_p (word (128 * 0)) /\
           read X6 s = htable_p /\
           read X10 s = word_add stackpointer (word 0x40) /\
           read X11 s = key_p /\
           read (memory :> bytes64 (word_add stackpointer (word 0x40))) s = word 0xc200000000000000 /\
           wordlist_from_memory(key_p,15) s = MAP (word_reversefields 8) rk /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce c) /\
           read Q28 s = word_reversefields 8 (EL 14 rk) /\
           read Q30 s = word_reversefields 32 (ctr_block nonce (8 * 0 + c + 8)) /\
           read Q31 s = word 79228162514264337593543950336 /\
           read Q19 s =
             nist_ghash (aes256_cipher (word 0) rk) tag0
                 (list_of_seq (nist_cipher_block aes256_cipher c nonce rk inblock)
                              (8 * 0)) /\
           word_xor (read Q0 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * 0 + c)) rk) /\
           word_xor (read Q1 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * 0 + c + 1)) rk) /\
           word_xor (read Q2 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * 0 + c + 2)) rk) /\
           word_xor (read Q3 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * 0 + c + 3)) rk) /\
           word_xor (read Q4 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * 0 + c + 4)) rk) /\
           word_xor (read Q5 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * 0 + c + 5)) rk) /\
           word_xor (read Q6 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * 0 + c + 6)) rk) /\
           word_xor (read Q7 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * 0 + c + 7)) rk) /\
           htable_mem_8 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j) /\
           (!j. j < 8 * 0
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block aes256_cipher c nonce rk (j)) (inblock j))` THEN
  CONJ_TAC THENL
   [(* SETUP0 leg *)
    MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN
    EXISTS_TAC
     `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
      MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
      MAYCHANGE [memory :> bytes(out_p, 16 * nb)]` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
      REPEAT (GEN_REWRITE_TAC ONCE_DEPTH_CONV [GSYM SEQ_ASSOC] THEN
              MATCH_MP_TAC SUBSUMED_SEQ THEN REWRITE_TAC[SUBSUMED_REFL]) THEN
      SUBSUMED_MAYCHANGE_TAC;
      ALL_TAC] THEN
    ENSURES_POSTCONDITION_TAC
     `      (\s. aligned_bytes_loaded s (word pc) aes256_gcm_enc_alt_tmc /\
           read PC s = word (pc + 0xee0) /\
           read X0 s = in_p /\
           read X2 s = out_p /\
           read X3 s = tag_p /\
           read X9 s = word (16 * nb) /\
           read X4 s = word_add in_p (word (16 * nb)) /\
           read X16 s = ivec_p /\
           read X5 s = in_p /\
           read X6 s = htable_p /\
           read X10 s = word_add stackpointer (word 0x40) /\
           read X11 s = key_p /\
           read (memory :> bytes64 (word_add stackpointer (word 0x40))) s =
             word 0xc200000000000000 /\
           wordlist_from_memory(key_p,15) s = MAP (word_reversefields 8) rk /\
           read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce c) /\
           read Q28 s = word_reversefields 8 (EL 14 rk) /\
           read Q30 s = word_reversefields 32 (ctr_block nonce (c + 8)) /\
           read Q31 s = word 79228162514264337593543950336 /\
           read Q19 s =
             nist_ghash (aes256_cipher (word 0) rk) tag0
                 (list_of_seq (nist_cipher_block aes256_cipher c nonce rk inblock) 0) /\
           word_xor (read Q0 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce c) rk) /\
           word_xor (read Q1 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (c + 1)) rk) /\
           word_xor (read Q2 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (c + 2)) rk) /\
           word_xor (read Q3 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (c + 3)) rk) /\
           word_xor (read Q4 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (c + 4)) rk) /\
           word_xor (read Q5 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (c + 5)) rk) /\
           word_xor (read Q6 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (c + 6)) rk) /\
           word_xor (read Q7 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (c + 7)) rk) /\
           htable_mem_8 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j) /\
           (!j. j < 8 * 0
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block aes256_cipher c nonce rk (j)) (inblock j)))` THEN
    CONJ_TAC THENL
     [X_GEN_TAC `s:armstate` THEN BETA_TAC THEN STRIP_TAC THEN
      RULE_ASSUM_TAC(REWRITE_RULE[MULT_CLAUSES; ADD_CLAUSES; WORD_ADD_0]) THEN
      REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; WORD_ADD_0] THEN
      REPEAT(CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC]) THEN
      EXISTS_TAC `read Q18 s:int128` THEN EXISTS_TAC `read Q27 s:int128` THEN
      ASM_REWRITE_TAC[];
      MP_TAC(ISPECL
       [`in_p:int64`; `out_p:int64`; `tag_p:int64`; `ivec_p:int64`;
        `key_p:int64`; `htable_p:int64`; `stackpointer:int64`; `bit_len:num`;
        `tag0:int128`; `nonce:(96)word`; `c:num`; `rk:int128 list`;
        `inblock:num->int128`; `nb:num`; `pc:num`]
       AES256_GCM_ENC_ALT_SETUP0) THEN
      REWRITE_TAC[LENGTH_WB_MC; ALLPAIRS; ALL; NONOVERLAPPING_CLAUSES] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[NONOVERLAPPING_CLAUSES] THEN
      ASM_ARITH_TAC];
    ALL_TAC] THEN

  (* ===== TAIL leg: pc+0xee0 -> pc+0x1154 ===== *)
  REWRITE_TAC[GSYM RIGHT_EXISTS_AND_THM; GSYM LEFT_EXISTS_AND_THM] THEN
  MATCH_MP_TAC ENSURES_EXISTS2_PRECONDITION THEN
  MAP_EVERY X_GEN_TAC [`v18:int128`; `v27:int128`] THEN
  MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN
  EXISTS_TAC
   `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
    MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
    MAYCHANGE [memory :> bytes(out_p, 16 * nb);
               memory :> bytes(tag_p, 16);
               memory :> bytes(ivec_p, 16)]` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    REPEAT (GEN_REWRITE_TAC ONCE_DEPTH_CONV [GSYM SEQ_ASSOC] THEN
            MATCH_MP_TAC SUBSUMED_SEQ THEN REWRITE_TAC[SUBSUMED_REFL]) THEN
    SUBSUMED_MAYCHANGE_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`v18:int128`; `v27:int128`;
    `in_p:int64`; `out_p:int64`; `tag_p:int64`; `ivec_p:int64`;
    `key_p:int64`; `htable_p:int64`; `word_add stackpointer (word 0x40):int64`;
    `word_add in_p (word (128 * 0)):int64`;
    `tag0:int128`; `nonce:(96)word`; `c:num`; `rk:int128 list`;
    `inblock:num->int128`; `nb:num`; `nb:num`; `0`; `pc:num`]
   AES256_GCM_ENC_ALT_TAIL_REM) THEN
  REWRITE_TAC[LENGTH_WB_MC; ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[NONOVERLAPPING_CLAUSES] THEN
  ASM_ARITH_TAC);;




(* ========================================================================= *)
(* FAST2 leg (pc+0x38 -> pc+0x1154, nb=2) = the 32B early-dispatch           *)
(* fast path. ENSURES_SEQUENCE at 0x17d4: segment A = dispatch(DISPATCH_     *)
(* TAKEN)+2-block AES; segment B = FAST2_TAIL. Split at 0x17d4 (NOT 0x1538)  *)
(* so the tail-setup eor3 block-ct write is tracked (fresh entry).           *)
(* ========================================================================= *)
let FAST2_MID_D2 : tactic = fun (asl,w as gl) ->
  if is_forall w then
    ((GEN_TAC THEN DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC) ORELSE
     REWRITE_TAC[ARITH_RULE `8 * 0 = 0`; ARITH_RULE `!j:num. j < 0 <=> F`]) gl
  else if is_eq w then
    let l,r = dest_eq w in
    let rhd = try fst(dest_const(fst(strip_comb r))) with _ -> "?" in
    let lhd = try fst(dest_const(fst(strip_comb l))) with _ -> "?" in
    if lhd = "word_xor" then (FIRST_ASSUM ACCEPT_TAC ORELSE KSCLOSE) gl
    else
      (FIRST_ASSUM ACCEPT_TAC ORELSE
       (ASM_REWRITE_TAC[ARITH_RULE `(128 * nb) DIV 8 = 16 * nb`] THEN
        (if rhd = "nist_ghash" then SETUP0_Q19_CLOSE
         else if rhd = "word_reversefields" then SETUP0_CTR_CLOSE
         else if rhd = "word_add" then
            (REWRITE_TAC[ARITH_RULE `128 * 0 = 0`; WORD_ADD_0] THEN REFL_TAC)
         else (REFL_TAC ORELSE CONV_TAC WORD_BLAST)))) gl  (*Q25 index closer       *)
  else (REWRITE_TAC[htable_mem_8; htable_mem_4] THEN ASM_REWRITE_TAC[]) gl;;
let AES256_GCM_ENC_ALT_FAST2 = prove
 (`!in_p out_p tag_p ivec_p key_p htable_p stackpointer bit_len
     tag0 nonce c rk inblock nb pc.
    nb = 2 /\
    bit_len = 128 * nb /\
    val in_p + 16 * nb < 2 EXP 63 /\
    128 * nb < 2 EXP 64 /\
    nonoverlapping (out_p, 16 * nb)
                   (word pc, LENGTH aes256_gcm_enc_alt_tmc) /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
      [(word pc, LENGTH aes256_gcm_enc_alt_tmc);
       (in_p, 16 * nb); (key_p, 240); (htable_p, 192);
       (word_add stackpointer (word 0x40), 8)] /\
    PAIRWISE nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) aes256_gcm_enc_alt_tmc /\
           read PC s = word (pc + 0x38) /\
           read X0 s = in_p /\
           read X1 s = word bit_len /\
           read X2 s = out_p /\
           read X3 s = tag_p /\
           read X16 s = ivec_p /\
           read X6 s = htable_p /\
           read X11 s = key_p /\
           read X9 s = word (bit_len DIV 8) /\
           read X10 s = word_add stackpointer (word 0x40) /\
           read (memory :> bytes64 (word_add stackpointer (word 0x40))) s =
             word 0xc200000000000000 /\
           wordlist_from_memory(key_p,15) s = MAP (word_reversefields 8) rk /\
           read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce c) /\
           htable_mem_8 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j))
      (\s. read PC s = word (pc + 0x1154) /\
           read X9 s = word (16 * nb) /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce (nb + c)) /\
           read (memory :> bytes128 tag_p) s =
             word_reversefields 8
               (nist_ghash (aes256_cipher (word 0) rk) tag0
                  (list_of_seq (nist_cipher_block aes256_cipher c nonce rk inblock) nb)) /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block aes256_cipher c nonce rk (j)) (inblock j)))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * nb);
                  memory :> bytes(tag_p, 16);
                  memory :> bytes(ivec_p, 16)])`,
  REWRITE_TAC[KEY15_SPLIT] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REWRITE_TAC[LENGTH_WB_MC; htable_mem_8; htable_mem_4; ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_SEQUENCE_TAC `pc + 0x17d4`
   `\s. read X0 s = word_add in_p (word (128 * 0)) /\
           read X2 s = word_add out_p (word (128 * 0)) /\
           read X3 s = tag_p /\
           read X9 s = word (16 * nb) /\
           read X6 s = htable_p /\
           read X10 s = word_add stackpointer (word 0x40) /\
           read X16 s = ivec_p /\
           read Q12 s = word 0x000102030405060708090a0b0c0d0e0f /\
           read (memory :> bytes64 (word_add stackpointer (word 0x40))) s = word 0xc200000000000000 /\
           word_xor (read Q0 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * 0 + c)) rk) /\
           word_xor (read Q1 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * 0 + c + 1)) rk) /\
           read Q19 s =
             nist_ghash (aes256_cipher (word 0) rk) tag0
                 (list_of_seq (nist_cipher_block aes256_cipher c nonce rk inblock) (8 * 0)) /\
           read Q28 s = word_reversefields 8 (EL 14 rk) /\
           read Q30 s = word_reversefields 32 (ctr_block nonce (8 * 0 + c + 2)) /\
           read Q31 s = word 79228162514264337593543950336 /\
           htable_mem_8 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j) /\
           (!j. j < 8 * 0
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block aes256_cipher c nonce rk (j)) (inblock j))` THEN
  CONJ_TAC THENL
   [(* SEGMENT A: 0x38 -> 0x17d4 *)
    ENSURES_INIT_TAC "s0" THEN
    RULE_ASSUM_TAC(REWRITE_RULE[REWRITE_CONV[fst AES256_GCM_ENC_ALT_EXEC]
      `LENGTH aes256_gcm_enc_alt_tmc`]) THEN
    SUBGOAL_THEN `read (memory :> bytes128 (word_add in_p (word (16 * 0)))) s0 = inblock 0`
      ASSUME_TAC THENL [FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `read (memory :> bytes128 (word_add in_p (word (16 * 1)))) s0 = inblock 1`
      ASSUME_TAC THENL [FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `~(nb = 4)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
        SUBGOAL_THEN `1 <= nb` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `nb <= 3` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `~(nb = 1)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    MAP_EVERY NSTEP (1--5) THEN NSTEP 6 THEN NSTEP 7 THEN
    RULE_ASSUM_TAC(REWRITE_RULE[
      MATCH_MP DISPATCH4_NOT_TAKEN (CONJ (ASSUME `128 * nb < 2 EXP 64`) (ASSUME `~(nb = 4)`));
      MATCH_MP DISPATCH_SMALL_TAKEN (CONJ (ASSUME `1 <= nb`) (ASSUME `nb <= 3`)); COND_CLAUSES]) THEN
    MAP_EVERY NSTEP (8--25) THEN
    NSTEP 26 THEN NSTEP 27 THEN
    RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP DISPATCH1_NOT_TAKEN (CONJ (ASSUME `128 * nb < 2 EXP 64`) (ASSUME `~(nb = 1)`)); COND_CLAUSES]) THEN
    NSTEP 28 THEN NSTEP 29 THEN
    RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP DISPATCH_TAKEN (ASSUME `nb = 2`); COND_CLAUSES]) THEN
    MAP_EVERY NSTEP (30--129) THEN
    SUBGOAL_THEN `word_xor (read Q0 s129) (word_reversefields 8 (EL 14 rk)) =
      word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * 0 + c)) rk)`
      ASSUME_TAC THENL [KSCLOSE; ALL_TAC] THEN
    SUBGOAL_THEN `word_xor (read Q1 s129) (word_reversefields 8 (EL 14 rk)) =
      word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * 0 + c + 1)) rk)`
      ASSUME_TAC THENL [KSCLOSE; ALL_TAC] THEN
    ENSURES_FINAL_STATE_TAC THEN
    REPEAT CONJ_TAC THEN FAST2_MID_D2;
    (* SEGMENT B: 0x17d4 -> 0x1154 = FAST2_TAIL *)
    MP_TAC(ISPECL
     [`in_p:int64`; `out_p:int64`; `tag_p:int64`; `ivec_p:int64`;
      `htable_p:int64`; `word_add stackpointer (word 0x40):int64`;
      `tag0:int128`; `nonce:(96)word`; `c:num`; `rk:int128 list`; `inblock:num->int128`;
      `nb:num`; `0`; `pc:num`] AES256_GCM_ENC_ALT_FAST2_TAIL) THEN
    REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
                LENGTH_WB_MC; htable_mem_8; htable_mem_4; ALLPAIRS; PAIRWISE; ALL;
                NONOVERLAPPING_CLAUSES] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
    (FIRST_ASSUM ACCEPT_TAC ORELSE ASM_ARITH_TAC ORELSE CONV_TAC WORD_RULE ORELSE
     ASM_REWRITE_TAC[])]);;

(* ========================================================================= *)
(* FAST4 - the nb=4 (64B) early-dispatch leg, entry pc+0x38. Mirrors         *)
(* FAST2 but for 4 blocks: the small_1/2/3 `b.eq` tests fall through         *)
(* (nb<>1,2,3) to L256_enc_small_4 (nb=4) -> 4-block AES (blocks             *)
(* 0-3 only) at 0x1544, then ENSURES_SEQUENCE-splits at 0x15ac (the fast4    *)
(* tail-setup start, keystreams as preconds) into FAST4_TAIL.                *)
(* ========================================================================= *)
let AES256_GCM_ENC_ALT_FAST4 = prove
 (`!in_p out_p tag_p ivec_p key_p htable_p stackpointer bit_len
     tag0 nonce c rk inblock nb pc.
    nb = 4 /\
    bit_len = 128 * nb /\
    val in_p + 16 * nb < 2 EXP 63 /\
    128 * nb < 2 EXP 64 /\
    nonoverlapping (out_p, 16 * nb)
                   (word pc, LENGTH aes256_gcm_enc_alt_tmc) /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
      [(word pc, LENGTH aes256_gcm_enc_alt_tmc);
       (in_p, 16 * nb); (key_p, 240); (htable_p, 192);
       (word_add stackpointer (word 0x40), 8)] /\
    PAIRWISE nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) aes256_gcm_enc_alt_tmc /\
           read PC s = word (pc + 0x38) /\
           read X0 s = in_p /\
           read X1 s = word bit_len /\
           read X2 s = out_p /\
           read X3 s = tag_p /\
           read X16 s = ivec_p /\
           read X6 s = htable_p /\
           read X11 s = key_p /\
           read X9 s = word (bit_len DIV 8) /\
           read X10 s = word_add stackpointer (word 0x40) /\
           read (memory :> bytes64 (word_add stackpointer (word 0x40))) s =
             word 0xc200000000000000 /\
           wordlist_from_memory(key_p,15) s = MAP (word_reversefields 8) rk /\
           read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce c) /\
           htable_mem_8 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j))
      (\s. read PC s = word (pc + 0x1154) /\
           read X9 s = word (16 * nb) /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce (nb + c)) /\
           read (memory :> bytes128 tag_p) s =
             word_reversefields 8
               (nist_ghash (aes256_cipher (word 0) rk) tag0
                  (list_of_seq (nist_cipher_block aes256_cipher c nonce rk inblock) nb)) /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block aes256_cipher c nonce rk (j)) (inblock j)))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * nb);
                  memory :> bytes(tag_p, 16);
                  memory :> bytes(ivec_p, 16)])`,
  REWRITE_TAC[KEY15_SPLIT] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REWRITE_TAC[LENGTH_WB_MC; htable_mem_8; htable_mem_4; ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_SEQUENCE_TAC `pc + 0x15ac`
   `\s. read X0 s = word_add in_p (word (128 * 0)) /\
           read X2 s = word_add out_p (word (128 * 0)) /\
           read X3 s = tag_p /\
           read X9 s = word (16 * nb) /\
           read X6 s = htable_p /\
           read X10 s = word_add stackpointer (word 0x40) /\
           read X16 s = ivec_p /\
           read Q12 s = word 0x000102030405060708090a0b0c0d0e0f /\
           read (memory :> bytes64 (word_add stackpointer (word 0x40))) s = word 0xc200000000000000 /\
           word_xor (read Q0 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * 0 + c)) rk) /\
           word_xor (read Q1 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * 0 + c + 1)) rk) /\
           word_xor (read Q2 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * 0 + c + 2)) rk) /\
           word_xor (read Q3 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * 0 + c + 3)) rk) /\
           read Q19 s =
             nist_ghash (aes256_cipher (word 0) rk) tag0
                 (list_of_seq (nist_cipher_block aes256_cipher c nonce rk inblock) (8 * 0)) /\
           read Q28 s = word_reversefields 8 (EL 14 rk) /\
           read Q30 s = word_reversefields 32 (ctr_block nonce (8 * 0 + c + 4)) /\
           read Q31 s = word 79228162514264337593543950336 /\
           htable_mem_8 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j) /\
           (!j. j < 8 * 0
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block aes256_cipher c nonce rk (j)) (inblock j))` THEN
  CONJ_TAC THENL
   [(* SEGMENT A: 0x38 -> 0x15ac (dispatch + 4-block AES) *)
    ENSURES_INIT_TAC "s0" THEN
    RULE_ASSUM_TAC(REWRITE_RULE[REWRITE_CONV[fst AES256_GCM_ENC_ALT_EXEC]
      `LENGTH aes256_gcm_enc_alt_tmc`]) THEN
    SUBGOAL_THEN `~(nb = 2)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `read (memory :> bytes128 (word_add in_p (word (16 * 0)))) s0 = inblock 0`
      ASSUME_TAC THENL [FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `read (memory :> bytes128 (word_add in_p (word (16 * 1)))) s0 = inblock 1`
      ASSUME_TAC THENL [FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `~(nb = 1)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `~(nb = 3)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    MAP_EVERY NSTEP (1--5) THEN NSTEP 6 THEN NSTEP 7 THEN
    RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP DISPATCH4_TAKEN (ASSUME `nb = 4`); COND_CLAUSES]) THEN
    MAP_EVERY NSTEP (8--25) THEN
    NSTEP 26 THEN NSTEP 27 THEN
    RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP DISPATCH1_NOT_TAKEN (CONJ (ASSUME `128 * nb < 2 EXP 64`) (ASSUME `~(nb = 1)`)); COND_CLAUSES]) THEN
    NSTEP 28 THEN NSTEP 29 THEN
    RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP DISPATCH_NOT_TAKEN (CONJ (ASSUME `128 * nb < 2 EXP 64`) (ASSUME `~(nb = 2)`)); COND_CLAUSES]) THEN
    NSTEP 30 THEN NSTEP 31 THEN
    RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP DISPATCH3_NOT_TAKEN (CONJ (ASSUME `128 * nb < 2 EXP 64`) (ASSUME `~(nb = 3)`)); COND_CLAUSES]) THEN
    MAP_EVERY NSTEP (32--189) THEN
    SUBGOAL_THEN `word_xor (read Q0 s189) (word_reversefields 8 (EL 14 rk)) =
      word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * 0 + c)) rk)`
      ASSUME_TAC THENL [KSCLOSE; ALL_TAC] THEN
    SUBGOAL_THEN `word_xor (read Q1 s189) (word_reversefields 8 (EL 14 rk)) =
      word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * 0 + c + 1)) rk)`
      ASSUME_TAC THENL [KSCLOSE; ALL_TAC] THEN
    SUBGOAL_THEN `word_xor (read Q2 s189) (word_reversefields 8 (EL 14 rk)) =
      word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * 0 + c + 2)) rk)`
      ASSUME_TAC THENL [KSCLOSE; ALL_TAC] THEN
    SUBGOAL_THEN `word_xor (read Q3 s189) (word_reversefields 8 (EL 14 rk)) =
      word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * 0 + c + 3)) rk)`
      ASSUME_TAC THENL [KSCLOSE; ALL_TAC] THEN
    ENSURES_FINAL_STATE_TAC THEN
    REPEAT CONJ_TAC THEN FAST2_MID_D2;
    (* SEGMENT B: 0x15ac -> 0x1154 = FAST4_TAIL *)
    MP_TAC(ISPECL
     [`in_p:int64`; `out_p:int64`; `tag_p:int64`; `ivec_p:int64`;
      `htable_p:int64`; `word_add stackpointer (word 0x40):int64`;
      `tag0:int128`; `nonce:(96)word`; `c:num`; `rk:int128 list`; `inblock:num->int128`;
      `nb:num`; `0`; `pc:num`] AES256_GCM_ENC_ALT_FAST4_TAIL) THEN
    REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
                LENGTH_WB_MC; htable_mem_8; htable_mem_4; ALLPAIRS; PAIRWISE; ALL;
                NONOVERLAPPING_CLAUSES] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
    (FIRST_ASSUM ACCEPT_TAC ORELSE ASM_ARITH_TAC ORELSE CONV_TAC WORD_RULE ORELSE
     ASM_REWRITE_TAC[])]);;

(* ========================================================================= *)
(* FAST1 - the nb=1 (16B) early-dispatch leg, entry pc+0x38.                 *)
(* small_2/3/4 `b.eq` skipped (nb<>2,3,4); nb=1 `b.eq small_1`@0x1530        *)
(* is TAKEN (nb=1) -> 1-block AES (block 0 only), then ENSURES_              *)
(* SEQUENCE-splits at 0x187c (fast1 tail-setup start, keystream Q0 as        *)
(* precond) into FAST1_TAIL.                                                 *)
(* ========================================================================= *)
let AES256_GCM_ENC_ALT_FAST1 = prove
 (`!in_p out_p tag_p ivec_p key_p htable_p stackpointer bit_len
     tag0 nonce c rk inblock nb pc.
    nb = 1 /\
    bit_len = 128 * nb /\
    val in_p + 16 * nb < 2 EXP 63 /\
    128 * nb < 2 EXP 64 /\
    nonoverlapping (out_p, 16 * nb)
                   (word pc, LENGTH aes256_gcm_enc_alt_tmc) /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
      [(word pc, LENGTH aes256_gcm_enc_alt_tmc);
       (in_p, 16 * nb); (key_p, 240); (htable_p, 192);
       (word_add stackpointer (word 0x40), 8)] /\
    PAIRWISE nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) aes256_gcm_enc_alt_tmc /\
           read PC s = word (pc + 0x38) /\
           read X0 s = in_p /\
           read X1 s = word bit_len /\
           read X2 s = out_p /\
           read X3 s = tag_p /\
           read X16 s = ivec_p /\
           read X6 s = htable_p /\
           read X11 s = key_p /\
           read X9 s = word (bit_len DIV 8) /\
           read X10 s = word_add stackpointer (word 0x40) /\
           read (memory :> bytes64 (word_add stackpointer (word 0x40))) s =
             word 0xc200000000000000 /\
           wordlist_from_memory(key_p,15) s = MAP (word_reversefields 8) rk /\
           read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce c) /\
           htable_mem_8 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j))
      (\s. read PC s = word (pc + 0x1154) /\
           read X9 s = word (16 * nb) /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce (nb + c)) /\
           read (memory :> bytes128 tag_p) s =
             word_reversefields 8
               (nist_ghash (aes256_cipher (word 0) rk) tag0
                  (list_of_seq (nist_cipher_block aes256_cipher c nonce rk inblock) nb)) /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block aes256_cipher c nonce rk (j)) (inblock j)))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * nb);
                  memory :> bytes(tag_p, 16);
                  memory :> bytes(ivec_p, 16)])`,
  REWRITE_TAC[KEY15_SPLIT] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REWRITE_TAC[LENGTH_WB_MC; htable_mem_8; htable_mem_4; ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_SEQUENCE_TAC `pc + 0x187c`
   `\s. read X0 s = word_add in_p (word (128 * 0)) /\
           read X2 s = word_add out_p (word (128 * 0)) /\
           read X3 s = tag_p /\
           read X9 s = word (16 * nb) /\
           read X6 s = htable_p /\
           read X10 s = word_add stackpointer (word 0x40) /\
           read X16 s = ivec_p /\
           read Q12 s = word 0x000102030405060708090a0b0c0d0e0f /\
           read (memory :> bytes64 (word_add stackpointer (word 0x40))) s = word 0xc200000000000000 /\
           word_xor (read Q0 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * 0 + c)) rk) /\
           read Q19 s =
             nist_ghash (aes256_cipher (word 0) rk) tag0
                 (list_of_seq (nist_cipher_block aes256_cipher c nonce rk inblock) (8 * 0)) /\
           read Q28 s = word_reversefields 8 (EL 14 rk) /\
           read Q30 s = word_reversefields 32 (ctr_block nonce (8 * 0 + c + 1)) /\
           read Q31 s = word 79228162514264337593543950336 /\
           htable_mem_8 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j) /\
           (!j. j < 8 * 0
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block aes256_cipher c nonce rk (j)) (inblock j))` THEN
  CONJ_TAC THENL
   [(* SEGMENT A: 0x38 -> 0x187c (dispatch + 1-block AES) *)
    ENSURES_INIT_TAC "s0" THEN
    RULE_ASSUM_TAC(REWRITE_RULE[REWRITE_CONV[fst AES256_GCM_ENC_ALT_EXEC]
      `LENGTH aes256_gcm_enc_alt_tmc`]) THEN
    SUBGOAL_THEN `read (memory :> bytes128 (word_add in_p (word (16 * 0)))) s0 = inblock 0`
      ASSUME_TAC THENL [FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `~(nb = 2)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `~(nb = 4)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
        SUBGOAL_THEN `1 <= nb` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `nb <= 3` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    MAP_EVERY NSTEP (1--5) THEN NSTEP 6 THEN NSTEP 7 THEN
    RULE_ASSUM_TAC(REWRITE_RULE[
      MATCH_MP DISPATCH4_NOT_TAKEN (CONJ (ASSUME `128 * nb < 2 EXP 64`) (ASSUME `~(nb = 4)`));
      MATCH_MP DISPATCH_SMALL_TAKEN (CONJ (ASSUME `1 <= nb`) (ASSUME `nb <= 3`)); COND_CLAUSES]) THEN
    MAP_EVERY NSTEP (8--25) THEN
    NSTEP 26 THEN NSTEP 27 THEN
    RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP DISPATCH1_TAKEN (ASSUME `nb = 1`); COND_CLAUSES]) THEN
    MAP_EVERY NSTEP (28--98) THEN
    SUBGOAL_THEN `word_xor (read Q0 s98) (word_reversefields 8 (EL 14 rk)) =
      word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * 0 + c)) rk)`
      ASSUME_TAC THENL [KSCLOSE; ALL_TAC] THEN
    ENSURES_FINAL_STATE_TAC THEN
    REPEAT CONJ_TAC THEN FAST2_MID_D2;
    (* SEGMENT B: 0x187c -> FAST1_TAIL *)
    MP_TAC(ISPECL
     [`in_p:int64`; `out_p:int64`; `tag_p:int64`; `ivec_p:int64`;
      `htable_p:int64`; `word_add stackpointer (word 0x40):int64`;
      `tag0:int128`; `nonce:(96)word`; `c:num`; `rk:int128 list`; `inblock:num->int128`;
      `nb:num`; `0`; `pc:num`] AES256_GCM_ENC_ALT_FAST1_TAIL) THEN
    REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
                LENGTH_WB_MC; htable_mem_8; htable_mem_4; ALLPAIRS; PAIRWISE; ALL;
                NONOVERLAPPING_CLAUSES] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
    (FIRST_ASSUM ACCEPT_TAC ORELSE ASM_ARITH_TAC ORELSE CONV_TAC WORD_RULE ORELSE
     ASM_REWRITE_TAC[])]);;

(* ========================================================================= *)
(* FAST3 - the nb=3 (48B) early-dispatch leg, entry pc+0x38.                 *)
(* small_1/2/4 `b.eq` skipped (nb<>1,2,4); the small_3 dispatch              *)
(* `cmp x9,#0x30; b.eq L256_enc_small_3`@0x1540 (nb=3) -> 3-block AES, then  *)
(* ENSURES_SEQUENCE-splits at 0x16ec (fast3 tail-setup start, 3 keystreams   *)
(* as preconds) into FAST3_TAIL.                                             *)
(* ========================================================================= *)
let AES256_GCM_ENC_ALT_FAST3 = prove
 (`!in_p out_p tag_p ivec_p key_p htable_p stackpointer bit_len
     tag0 nonce c rk inblock nb pc.
    nb = 3 /\
    bit_len = 128 * nb /\
    val in_p + 16 * nb < 2 EXP 63 /\
    128 * nb < 2 EXP 64 /\
    nonoverlapping (out_p, 16 * nb)
                   (word pc, LENGTH aes256_gcm_enc_alt_tmc) /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
      [(word pc, LENGTH aes256_gcm_enc_alt_tmc);
       (in_p, 16 * nb); (key_p, 240); (htable_p, 192);
       (word_add stackpointer (word 0x40), 8)] /\
    PAIRWISE nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) aes256_gcm_enc_alt_tmc /\
           read PC s = word (pc + 0x38) /\
           read X0 s = in_p /\
           read X1 s = word bit_len /\
           read X2 s = out_p /\
           read X3 s = tag_p /\
           read X16 s = ivec_p /\
           read X6 s = htable_p /\
           read X11 s = key_p /\
           read X9 s = word (bit_len DIV 8) /\
           read X10 s = word_add stackpointer (word 0x40) /\
           read (memory :> bytes64 (word_add stackpointer (word 0x40))) s =
             word 0xc200000000000000 /\
           wordlist_from_memory(key_p,15) s = MAP (word_reversefields 8) rk /\
           read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce c) /\
           htable_mem_8 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j))
      (\s. read PC s = word (pc + 0x1154) /\
           read X9 s = word (16 * nb) /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce (nb + c)) /\
           read (memory :> bytes128 tag_p) s =
             word_reversefields 8
               (nist_ghash (aes256_cipher (word 0) rk) tag0
                  (list_of_seq (nist_cipher_block aes256_cipher c nonce rk inblock) nb)) /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block aes256_cipher c nonce rk (j)) (inblock j)))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * nb);
                  memory :> bytes(tag_p, 16);
                  memory :> bytes(ivec_p, 16)])`,
  REWRITE_TAC[KEY15_SPLIT] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REWRITE_TAC[LENGTH_WB_MC; htable_mem_8; htable_mem_4; ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_SEQUENCE_TAC `pc + 0x16ec`
   `\s. read X0 s = word_add in_p (word (128 * 0)) /\
           read X2 s = word_add out_p (word (128 * 0)) /\
           read X3 s = tag_p /\
           read X9 s = word (16 * nb) /\
           read X6 s = htable_p /\
           read X10 s = word_add stackpointer (word 0x40) /\
           read X16 s = ivec_p /\
           read Q12 s = word 0x000102030405060708090a0b0c0d0e0f /\
           read (memory :> bytes64 (word_add stackpointer (word 0x40))) s = word 0xc200000000000000 /\
           word_xor (read Q0 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * 0 + c)) rk) /\
           word_xor (read Q1 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * 0 + c + 1)) rk) /\
           word_xor (read Q2 s) (word_reversefields 8 (EL 14 rk)) =
             word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * 0 + c + 2)) rk) /\
           read Q19 s =
             nist_ghash (aes256_cipher (word 0) rk) tag0
                 (list_of_seq (nist_cipher_block aes256_cipher c nonce rk inblock) (8 * 0)) /\
           read Q28 s = word_reversefields 8 (EL 14 rk) /\
           read Q30 s = word_reversefields 32 (ctr_block nonce (8 * 0 + c + 3)) /\
           read Q31 s = word 79228162514264337593543950336 /\
           htable_mem_8 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j) /\
           (!j. j < 8 * 0
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block aes256_cipher c nonce rk (j)) (inblock j))` THEN
  CONJ_TAC THENL
   [(* SEGMENT A: 0x38 -> 0x16ec (dispatch + 3-block AES) *)
    ENSURES_INIT_TAC "s0" THEN
    RULE_ASSUM_TAC(REWRITE_RULE[REWRITE_CONV[fst AES256_GCM_ENC_ALT_EXEC]
      `LENGTH aes256_gcm_enc_alt_tmc`]) THEN
    SUBGOAL_THEN `read (memory :> bytes128 (word_add in_p (word (16 * 0)))) s0 = inblock 0`
      ASSUME_TAC THENL [FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `read (memory :> bytes128 (word_add in_p (word (16 * 1)))) s0 = inblock 1`
      ASSUME_TAC THENL [FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `read (memory :> bytes128 (word_add in_p (word (16 * 2)))) s0 = inblock 2`
      ASSUME_TAC THENL [FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `~(nb = 2)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `~(nb = 4)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `~(nb = 1)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
        SUBGOAL_THEN `1 <= nb` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `nb <= 3` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    MAP_EVERY NSTEP (1--5) THEN NSTEP 6 THEN NSTEP 7 THEN
    RULE_ASSUM_TAC(REWRITE_RULE[
      MATCH_MP DISPATCH4_NOT_TAKEN (CONJ (ASSUME `128 * nb < 2 EXP 64`) (ASSUME `~(nb = 4)`));
      MATCH_MP DISPATCH_SMALL_TAKEN (CONJ (ASSUME `1 <= nb`) (ASSUME `nb <= 3`)); COND_CLAUSES]) THEN
    MAP_EVERY NSTEP (8--25) THEN
    NSTEP 26 THEN NSTEP 27 THEN
    RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP DISPATCH1_NOT_TAKEN (CONJ (ASSUME `128 * nb < 2 EXP 64`) (ASSUME `~(nb = 1)`)); COND_CLAUSES]) THEN
    NSTEP 28 THEN NSTEP 29 THEN
    RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP DISPATCH_NOT_TAKEN (CONJ (ASSUME `128 * nb < 2 EXP 64`) (ASSUME `~(nb = 2)`)); COND_CLAUSES]) THEN
    NSTEP 30 THEN NSTEP 31 THEN
    RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP DISPATCH3_TAKEN (ASSUME `nb = 3`); COND_CLAUSES]) THEN
    MAP_EVERY NSTEP (32--160) THEN
    SUBGOAL_THEN `word_xor (read Q0 s160) (word_reversefields 8 (EL 14 rk)) =
      word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * 0 + c)) rk)`
      ASSUME_TAC THENL [KSCLOSE; ALL_TAC] THEN
    SUBGOAL_THEN `word_xor (read Q1 s160) (word_reversefields 8 (EL 14 rk)) =
      word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * 0 + c + 1)) rk)`
      ASSUME_TAC THENL [KSCLOSE; ALL_TAC] THEN
    SUBGOAL_THEN `word_xor (read Q2 s160) (word_reversefields 8 (EL 14 rk)) =
      word_reversefields 8 (aes256_cipher (ctr_block nonce (8 * 0 + c + 2)) rk)`
      ASSUME_TAC THENL [KSCLOSE; ALL_TAC] THEN
    ENSURES_FINAL_STATE_TAC THEN
    REPEAT CONJ_TAC THEN FAST2_MID_D2;
    (* SEGMENT B: 0x16ec -> FAST3_TAIL *)
    MP_TAC(ISPECL
     [`in_p:int64`; `out_p:int64`; `tag_p:int64`; `ivec_p:int64`;
      `htable_p:int64`; `word_add stackpointer (word 0x40):int64`;
      `tag0:int128`; `nonce:(96)word`; `c:num`; `rk:int128 list`; `inblock:num->int128`;
      `nb:num`; `0`; `pc:num`] AES256_GCM_ENC_ALT_FAST3_TAIL) THEN
    REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
                LENGTH_WB_MC; htable_mem_8; htable_mem_4; ALLPAIRS; PAIRWISE; ALL;
                NONOVERLAPPING_CLAUSES] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
    (FIRST_ASSUM ACCEPT_TAC ORELSE ASM_ARITH_TAC ORELSE CONV_TAC WORD_RULE ORELSE
     ASM_REWRITE_TAC[])]);;


let AES256_GCM_ENC_ALT_CORRECT = prove
 (`!in_p out_p tag_p ivec_p key_p htable_p stackpointer bit_len
     tag0 nonce c rk inblock nb pc.
    1 <= nb /\
    bit_len = 128 * nb /\
    val in_p + 16 * nb < 2 EXP 63 /\
    128 * nb < 2 EXP 64 /\
    nonoverlapping (out_p, 16 * nb)
                   (word pc, LENGTH aes256_gcm_enc_alt_tmc) /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
      [(word pc, LENGTH aes256_gcm_enc_alt_tmc);
       (in_p, 16 * nb); (key_p, 240); (htable_p, 192);
       (word_add stackpointer (word 0x40), 8)] /\
    PAIRWISE nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) aes256_gcm_enc_alt_tmc /\
           read PC s = word (pc + 0x38) /\
           read X0 s = in_p /\
           read X1 s = word bit_len /\
           read X2 s = out_p /\
           read X3 s = tag_p /\
           read X16 s = ivec_p /\
           read X6 s = htable_p /\
           read X11 s = key_p /\
           read X9 s = word (bit_len DIV 8) /\
           read X10 s = word_add stackpointer (word 0x40) /\
           read (memory :> bytes64 (word_add stackpointer (word 0x40))) s =
             word 0xc200000000000000 /\
           wordlist_from_memory(key_p,15) s = MAP (word_reversefields 8) rk /\
           read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce c) /\
           htable_mem_8 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j))
      (\s. read PC s = word (pc + 0x1154) /\
           read X9 s = word (16 * nb) /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce (nb + c)) /\
           read (memory :> bytes128 tag_p) s =
             word_reversefields 8
               (nist_ghash (aes256_cipher (word 0) rk) tag0
                  (list_of_seq (nist_cipher_block aes256_cipher c nonce rk inblock) nb)) /\
           (!j. j < nb
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block aes256_cipher c nonce rk (j)) (inblock j)))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * nb);
                  memory :> bytes(tag_p, 16);
                  memory :> bytes(ivec_p, 16)])`,
  REWRITE_TAC[ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES; LENGTH_WB_MC] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `nb <= 8 \/ (9 <= nb /\ nb <= 16) \/ 17 <= nb` MP_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THENL
   [(* ===== g = 0  (nb 1..8) ===== *)
    ASM_CASES_TAC `nb = 1` THENL
     [(* nb = 1 (16B): the fast1 early-dispatch path *)
      MP_TAC(ISPECL
       [`in_p:int64`; `out_p:int64`; `tag_p:int64`; `ivec_p:int64`;
        `key_p:int64`; `htable_p:int64`; `stackpointer:int64`; `bit_len:num`;
        `tag0:int128`; `nonce:(96)word`; `c:num`; `rk:int128 list`;
        `inblock:num->int128`; `nb:num`; `pc:num`]
       AES256_GCM_ENC_ALT_FAST1) THEN
      REWRITE_TAC[LENGTH_WB_MC; ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES] THEN
      DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THEN
      (NONOVERLAPPING_TAC ORELSE CONV_TAC WORD_RULE ORELSE ASM_ARITH_TAC ORELSE ASM_REWRITE_TAC[]);
    ASM_CASES_TAC `nb = 2` THENL
     [(* nb = 2 (32B): the fast2 early-dispatch path *)
      MP_TAC(ISPECL
       [`in_p:int64`; `out_p:int64`; `tag_p:int64`; `ivec_p:int64`;
        `key_p:int64`; `htable_p:int64`; `stackpointer:int64`; `bit_len:num`;
        `tag0:int128`; `nonce:(96)word`; `c:num`; `rk:int128 list`;
        `inblock:num->int128`; `nb:num`; `pc:num`]
       AES256_GCM_ENC_ALT_FAST2) THEN
      REWRITE_TAC[LENGTH_WB_MC; ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES] THEN
      DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THEN
      (NONOVERLAPPING_TAC ORELSE CONV_TAC WORD_RULE ORELSE ASM_ARITH_TAC ORELSE ASM_REWRITE_TAC[]);
      ASM_CASES_TAC `nb = 3` THENL
       [(* nb = 3 (48B): the fast3 early-dispatch path *)
        MP_TAC(ISPECL
         [`in_p:int64`; `out_p:int64`; `tag_p:int64`; `ivec_p:int64`;
          `key_p:int64`; `htable_p:int64`; `stackpointer:int64`; `bit_len:num`;
          `tag0:int128`; `nonce:(96)word`; `c:num`; `rk:int128 list`;
          `inblock:num->int128`; `nb:num`; `pc:num`]
         AES256_GCM_ENC_ALT_FAST3) THEN
        REWRITE_TAC[LENGTH_WB_MC; ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES] THEN
        DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THEN
        (NONOVERLAPPING_TAC ORELSE CONV_TAC WORD_RULE ORELSE ASM_ARITH_TAC ORELSE ASM_REWRITE_TAC[]);
      (* nb <> 3: split nb = 4 (fast4, 64B) vs nb not in {1,2,3,4} (SETUP0_TAIL) *)
      ASM_CASES_TAC `nb = 4` THENL
       [(* nb = 4 (64B): the fast4 early-dispatch path *)
        MP_TAC(ISPECL
         [`in_p:int64`; `out_p:int64`; `tag_p:int64`; `ivec_p:int64`;
          `key_p:int64`; `htable_p:int64`; `stackpointer:int64`; `bit_len:num`;
          `tag0:int128`; `nonce:(96)word`; `c:num`; `rk:int128 list`;
          `inblock:num->int128`; `nb:num`; `pc:num`]
         AES256_GCM_ENC_ALT_FAST4) THEN
        REWRITE_TAC[LENGTH_WB_MC; ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES] THEN
        DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THEN
        (NONOVERLAPPING_TAC ORELSE CONV_TAC WORD_RULE ORELSE ASM_ARITH_TAC ORELSE ASM_REWRITE_TAC[]);
        (* nb not in {1,2,3,4} but nb<=8, i.e. nb in {5,6,7,8}:
           fast5/6/7 are gone; ALL of {5,6,7,8} fall back to the generic 8-block
           wave via SETUP0_TAIL (generalized to nb in {5,6,7,8}). *)
        MP_TAC(ISPECL
         [`in_p:int64`; `out_p:int64`; `tag_p:int64`; `ivec_p:int64`;
          `key_p:int64`; `htable_p:int64`; `stackpointer:int64`; `bit_len:num`;
          `tag0:int128`; `nonce:(96)word`; `c:num`; `rk:int128 list`;
          `inblock:num->int128`; `nb:num`; `pc:num`]
         AES256_GCM_ENC_ALT_SETUP0_TAIL) THEN
        REWRITE_TAC[LENGTH_WB_MC; ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES] THEN
        DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THEN
        (NONOVERLAPPING_TAC ORELSE CONV_TAC WORD_RULE ORELSE ASM_ARITH_TAC ORELSE ASM_REWRITE_TAC[])]]]];
    (* ===== g = 1  (nb 9..16): FIXED_CORRECT_G1 (k=0) ===== *)
    MP_TAC(ISPECL
     [`in_p:int64`; `out_p:int64`; `tag_p:int64`; `ivec_p:int64`;
      `key_p:int64`; `htable_p:int64`; `stackpointer:int64`; `bit_len:num`;
      `word_add in_p (word (128 * (0 + 1))):int64`;
      `tag0:int128`; `nonce:(96)word`; `c:num`; `rk:int128 list`;
      `inblock:num->int128`; `nb:num`; `0`; `pc:num`]
     AES256_GCM_ENC_ALT_FIXED_CORRECT_G1) THEN
    REWRITE_TAC[LENGTH_WB_MC; ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES] THEN
    DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THEN
    (NONOVERLAPPING_TAC ORELSE CONV_TAC WORD_RULE ORELSE ASM_ARITH_TAC ORELSE ASM_REWRITE_TAC[]);
    (* ===== g >= 2  (nb >= 17): GEN_CORRECT (k = groups-1) =====    *)
    MP_TAC(ISPECL
     [`in_p:int64`; `out_p:int64`; `tag_p:int64`; `ivec_p:int64`;
      `key_p:int64`; `htable_p:int64`; `stackpointer:int64`; `bit_len:num`;
      `word_add in_p (word (128 * (((nb - 1) DIV 8 - 1) + 1))):int64`;
      `tag0:int128`; `nonce:(96)word`; `c:num`; `rk:int128 list`;
      `inblock:num->int128`; `nb:num`; `(nb - 1) DIV 8 - 1`; `pc:num`]
     AES256_GCM_ENC_ALT_GEN_CORRECT) THEN
    REWRITE_TAC[LENGTH_WB_MC; ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES] THEN
    DISCH_THEN MATCH_MP_TAC THEN MP_TAC(SPECL [`nb - 1`; `8`] DIVISION) THEN REWRITE_TAC[ARITH_EQ] THEN
    ABBREV_TAC `q = (nb - 1) DIV 8` THEN ABBREV_TAC `r = (nb - 1) MOD 8` THEN
    STRIP_TAC THEN REPEAT CONJ_TAC THEN
    (NONOVERLAPPING_TAC ORELSE CONV_TAC WORD_RULE ORELSE ASM_ARITH_TAC ORELSE ASM_REWRITE_TAC[])]);;


(* Generalized entry-guard lemmas for the general nblocks>=0                 *)
(* wrapper's nb>=1 leg: GUARD1 (cbz x1 does not branch, word(128*nb) nonzero *)
(* for nb>=1) and GUARD2 (tst x1,#0x7f falls through, 128 | 128*nb).  These  *)
(* hold for every nb >= 1.                                                   *)
let WB_GUARD1_NONZERO_GEN = prove
 (`!nb. 1 <= nb /\ 128 * nb < 2 EXP 64
        ==> ~(word (128 * nb):int64 = word 0) /\
            ~(val(word (128 * nb):int64) = 0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[GSYM VAL_EQ_0] THEN
  SUBGOAL_THEN `val(word(128 * nb):int64) = 128 * nb` SUBST1_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC;
    ASM_ARITH_TAC]);;

let WB_GUARD2_MASK_GEN = prove
 (`!nb. 1 <= nb /\ 128 * nb < 2 EXP 64
        ==> word_and (word (128 * nb):int64) (word 0x7f) = word 0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[ARITH_RULE `0x7f = 2 EXP 7 - 1`; WORD_AND_MASK_WORD] THEN
  SUBGOAL_THEN `val(word(128 * nb):int64) = 128 * nb` SUBST1_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC;
    AP_TERM_TAC THEN REWRITE_TAC[ARITH_RULE `2 EXP 7 = 128`] THEN
    MP_TAC(SPECL [`128`; `nb:num`] MOD_MULT) THEN ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The whole-block count actually processed, gcm_wb_blocks (shared, in      *)
(* aes_gcm_spec.ml), as a function of the bit length in X1.  The kernel has *)
(* two entry guards: `cbz x1` for a zero length and                          *)
(* `tst x1,#127` / `b.ne` for a length that is not a whole number of 128-bit  *)
(* blocks.  Both return 0 without touching memory.  Folding that into the     *)
(* block count keeps ONE postcondition for all three paths, because at zero   *)
(* blocks the GHASH input list is empty (so the tag is unchanged), the        *)
(* counter advances by 0, and the output forall is vacuous.                   *)
(* ------------------------------------------------------------------------- *)

(* `tst x1,#127` sets ZF exactly when the length is a whole block count.      *)

let WB_MASK7_EQ_MOD = prove
 (`!x:int64. word_and x (word 0x7f) = word 0 <=> val x MOD 128 = 0`,
  GEN_TAC THEN
  REWRITE_TAC[ARITH_RULE `0x7f = 2 EXP 7 - 1`; WORD_AND_MASK_WORD] THEN
  REWRITE_TAC[ARITH_RULE `2 EXP 7 = 128`; GSYM VAL_EQ_0] THEN
  SUBGOAL_THEN `val(word(val(x:int64) MOD 128):int64) = val x MOD 128`
  SUBST1_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ARITH_TAC;
    REFL_TAC]);;

(* On the whole-blocks path the bit length is 128 times the block count.      *)

let AES256_GCM_ENC_ALT_NOIBT_SUBROUTINE_CORRECT = prove
 (`!in_p out_p tag_p ivec_p key_p htable_p
     tag0 nonce c rk inblock len_bits pc stackpointer returnaddress.
    aligned 16 stackpointer /\
    val in_p + 16 * gcm_wb_blocks len_bits < 2 EXP 63 /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * gcm_wb_blocks len_bits); (tag_p, 16); (ivec_p, 16);
       (word_sub stackpointer (word 80), 80)]
      [(word pc, LENGTH aes256_gcm_enc_alt_tmc);
       (in_p, 16 * gcm_wb_blocks len_bits); (key_p, 240); (htable_p, 192)] /\
    PAIRWISE nonoverlapping
      [(out_p, 16 * gcm_wb_blocks len_bits); (tag_p, 16); (ivec_p, 16);
       (word_sub stackpointer (word 80), 80)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) aes256_gcm_enc_alt_tmc /\
           read PC s = word pc /\
           read SP s = stackpointer /\
           read X30 s = returnaddress /\
           C_ARGUMENTS
            [in_p; len_bits; out_p; tag_p; ivec_p; key_p; htable_p] s /\
           read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce c) /\
           wordlist_from_memory(key_p,15) s =
             MAP (word_reversefields 8) rk /\
           htable_mem_8 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s /\
           (!j. j < gcm_wb_blocks len_bits
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j))
      (\s. read PC s = returnaddress /\
           C_RETURN s = word (16 * gcm_wb_blocks len_bits) /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce (gcm_wb_blocks len_bits + c)) /\
           read (memory :> bytes128 tag_p) s =
             word_reversefields 8
               (nist_ghash (aes256_cipher (word 0) rk) tag0
                  (list_of_seq (nist_cipher_block aes256_cipher c nonce rk inblock)
                               (gcm_wb_blocks len_bits))) /\
           (!j. j < gcm_wb_blocks len_bits
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block aes256_cipher c nonce rk (j)) (inblock j)))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * gcm_wb_blocks len_bits);
                  memory :> bytes(tag_p, 16);
                  memory :> bytes(ivec_p, 16);
                  memory :> bytes(word_sub stackpointer (word 80), 80)])`,
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REWRITE_TAC[LENGTH_WB_MC; ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN
  (* Expand the compact round-key list, in place inside the precondition,                *)
  (* into the pointwise reads the interior legs consume.                       *)
  REWRITE_TAC[KEY15_SPLIT] THEN
  REPEAT STRIP_TAC THEN
  (* Abbreviate the block count.  This is not cosmetic: keeping `gcm_wb_blocks`   *)
  (* folded stops `val len_bits = 128 * nb` from looping as a rewrite, which  *)
  (* it would if gcm_wb_blocks unfolded to `val len_bits DIV 128` on the right.   *)
  ABBREV_TAC `nb = gcm_wb_blocks len_bits` THEN
  ASM_CASES_TAC `val(len_bits:int64) MOD 128 = 0` THENL
   [ALL_TAC;
    (* ================================================================== *)
    (* Path 3: length is not a whole number of blocks.  `cbz x1` falls     *)
    (* through (a non-multiple of 128 is nonzero), `tst x1,#127` leaves    *)
    (* ZF clear so `b.ne` is TAKEN, and L256_enc_ret returns 0.            *)
    (* ================================================================== *)
    SUBGOAL_THEN `nb = 0` SUBST_ALL_TAC THENL
     [EXPAND_TAC "nb" THEN REWRITE_TAC[gcm_wb_blocks] THEN
      ASM_REWRITE_TAC[COND_CLAUSES]; ALL_TAC] THEN
    (* The branch condition is phrased on `val len_bits`, so derive that form. *)
    SUBGOAL_THEN `~(val(len_bits:int64) = 0)` ASSUME_TAC THENL
     [DISCH_TAC THEN
      UNDISCH_TAC `~(val(len_bits:int64) MOD 128 = 0)` THEN
      ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
      ALL_TAC] THEN
    SUBGOAL_THEN `~(len_bits:int64 = word 0)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[GSYM VAL_EQ_0]; ALL_TAC] THEN
    (* `tst x1,#127` leaves ZF clear, so `b.ne` IS taken.  Both the word and  *)
    (* the val form of the mask fact are needed to resolve the flag.          *)
    SUBGOAL_THEN `~(word_and (len_bits:int64) (word 0x7f) = word 0)`
    ASSUME_TAC THENL [ASM_REWRITE_TAC[WB_MASK7_EQ_MOD]; ALL_TAC] THEN
    SUBGOAL_THEN `~(val(word_and (len_bits:int64) (word 0x7f)) = 0)`
    ASSUME_TAC THENL [ASM_REWRITE_TAC[VAL_EQ_0]; ALL_TAC] THEN
    REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES] THEN
    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC AES256_GCM_ENC_ALT_EXEC [1] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `~(val(len_bits:int64) = 0)`;
                               ASSUME `~(len_bits:int64 = word 0)`;
                               COND_CLAUSES]) THEN
    ARM_STEPS_TAC AES256_GCM_ENC_ALT_EXEC [2] THEN
    ARM_STEPS_TAC AES256_GCM_ENC_ALT_EXEC [3] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[
      ASSUME `~(word_and (len_bits:int64) (word 0x7f) = word 0)`;
      ASSUME `~(val(word_and (len_bits:int64) (word 0x7f)) = 0)`;
      COND_CLAUSES]) THEN
    ARM_STEPS_TAC AES256_GCM_ENC_ALT_EXEC [4;5] THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[list_of_seq; nist_ghash] THEN
    REWRITE_TAC[ARITH_RULE `j < 0 <=> F`]] THEN
  (* From here on the length IS a whole number of blocks.                    *)
  ASM_CASES_TAC `val(len_bits:int64) = 0` THENL
   [(* ================================================================== *)
    (* Path 1: zero length.  `cbz x1` is TAKEN straight to L256_enc_ret.   *)
    (* ================================================================== *)
    SUBGOAL_THEN `nb = 0` SUBST_ALL_TAC THENL
     [EXPAND_TAC "nb" THEN REWRITE_TAC[gcm_wb_blocks] THEN
      ASM_REWRITE_TAC[COND_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV;
      ALL_TAC] THEN
    SUBGOAL_THEN `len_bits:int64 = word 0` SUBST_ALL_TAC THENL
     [ASM_REWRITE_TAC[GSYM VAL_EQ_0]; ALL_TAC] THEN
    REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES] THEN
    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC AES256_GCM_ENC_ALT_EXEC [1;2;3] THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[list_of_seq; nist_ghash] THEN
    REWRITE_TAC[ARITH_RULE `j < 0 <=> F`];
    ALL_TAC] THEN
  (* ==================================================================== *)
  (* Path 2: a nonzero whole number of blocks.  Both guards fall through;  *)
  (* steps 1-14 are the prologue, the interior big step is _CORRECT, and   *)
  (* steps 16-22 are the epilogue (which sets X0 from X9).                 *)
  (* ==================================================================== *)
  SUBGOAL_THEN `1 <= nb` ASSUME_TAC THENL
   [EXPAND_TAC "nb" THEN REWRITE_TAC[gcm_wb_blocks] THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`val(len_bits:int64)`; `128`] (CONJUNCT2 DIVISION_SIMP)) THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `val(len_bits:int64) = 128 * nb` ASSUME_TAC THENL
   [EXPAND_TAC "nb" THEN ASM_SIMP_TAC[GCM_WB_BLOCKS_VALID]; ALL_TAC] THEN
  SUBGOAL_THEN `128 * nb < 2 EXP 64` ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    MP_TAC(ISPEC `len_bits:int64` VAL_BOUND) THEN
    REWRITE_TAC[DIMINDEX_64] THEN ARITH_TAC;
    ALL_TAC] THEN
  (* Put the length argument back into the CONSTRUCTED form `word (128 * nb)`. *)
  (* That is what WB_GUARD1_NONZERO_GEN and WB_GUARD2_MASK_GEN are stated      *)
  (* about, so the original guard reasoning below applies verbatim -- no new   *)
  (* facts about an opaque word, and no rewrite that can loop.                 *)
  SUBGOAL_THEN `len_bits:int64 = word (128 * nb)` SUBST_ALL_TAC THENL
   [FIRST_X_ASSUM(fun th ->
      if concl th = `val(len_bits:int64) = 128 * nb`
      then MP_TAC th else failwith "") THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[WORD_VAL];
    ALL_TAC] THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  MAP_EVERY (fun c -> ENSURES_PRESERVED_DREG_TAC ("init_"^fst(dest_const c)) c)
    [`D8`;`D9`;`D10`;`D11`;`D12`;`D13`;`D14`;`D15`] THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_8; htable_mem_4]) THEN
  RULE_ASSUM_TAC(CONV_RULE(TRY_CONV(
    EXPAND_CASES_CONV THENC ONCE_DEPTH_CONV NUM_MULT_CONV THENC
    REWRITE_CONV[WORD_ADD_0]))) THEN
  ARM_STEPS_TAC AES256_GCM_ENC_ALT_EXEC [1] THEN
  (* The `cbz x1` test reduces to the numeric form `128 * nb = 0` (the model    *)
  (* simplifies `val(word(128*nb))` via the `128*nb < 2^64` fact), which        *)
  (* WB_GUARD1_NONZERO_GEN's word/val-shaped conjuncts do not rewrite; discharge *)
  (* the numeric form directly from `1 <= nb` so the conditional PC collapses.   *)
  SUBGOAL_THEN `~(128 * nb = 0)` ASSUME_TAC THENL
   [UNDISCH_TAC `1 <= nb` THEN ARITH_TAC; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP WB_GUARD1_NONZERO_GEN
    (CONJ (ASSUME `1 <= nb`) (ASSUME `128 * nb < 2 EXP 64`));
    ASSUME `~(128 * nb = 0)`;
    COND_CLAUSES]) THEN
  ARM_STEPS_TAC AES256_GCM_ENC_ALT_EXEC [2] THEN
  ARM_STEPS_TAC AES256_GCM_ENC_ALT_EXEC [3] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP WB_GUARD2_MASK_GEN
    (CONJ (ASSUME `1 <= nb`) (ASSUME `128 * nb < 2 EXP 64`));
    VAL_WORD_0; COND_CLAUSES]) THEN
  ARM_STEPS_TAC AES256_GCM_ENC_ALT_EXEC (4--14) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP WB_X9_NORM
    (ASSUME `128 * nb < 2 EXP 64`)]) THEN
  MP_TAC(SPECL
   [`in_p:int64`; `out_p:int64`; `tag_p:int64`; `ivec_p:int64`;
    `key_p:int64`; `htable_p:int64`;
    `word_sub stackpointer (word 0x50):int64`;
    `128 * nb`;
    `tag0:int128`; `nonce:(96)word`; `c:num`;
    `rk:int128 list`;
    `inblock:num->int128`; `nb:num`; `pc:num`]
   (REWRITE_RULE[KEY15_SPLIT] AES256_GCM_ENC_ALT_CORRECT)) THEN
  REWRITE_TAC[LENGTH_WB_MC] THEN
  ANTS_TAC THENL
   [REWRITE_TAC[ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES] THEN
    REPEAT CONJ_TAC THEN
    (NONOVERLAPPING_TAC ORELSE ASM_ARITH_TAC ORELSE CONV_TAC WORD_RULE ORELSE
     ASM_REWRITE_TAC[WORD_REVERSEFIELDS_REVERSEFIELDS]);
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              MODIFIABLE_SIMD_REGS; MODIFIABLE_GPRS; MODIFIABLE_UPPER_SIMD_REGS;
              htable_mem_8; htable_mem_4] THEN
  ARM_BIGSTEP_TAC AES256_GCM_ENC_ALT_EXEC "s15" THEN
  ARM_STEPS_TAC AES256_GCM_ENC_ALT_EXEC (16--22) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SIMP_TAC[WORD_ZX_ZX; DIMINDEX_64; DIMINDEX_128; LE_REFL; ARITH] THEN
  CONV_TAC WORD_RULE);;

(* ------------------------------------------------------------------------- *)
(* The default build keeps the `bti c` landing pad, so its machine code is    *)
(* aes256_gcm_enc_alt_mc rather than the trimmed variant proved above.   *)
(* The statement is written out and discharged by ARM_ADD_IBT_RULE, matching  *)
(* the x86 convention (cf. x86/proofs/sha3_keccak_f1600.ml); nothing is       *)
(* re-proved.  `~extra` supplies htable_mem_8's definition, which the wrap    *)
(* theorem needs in order to see that writing PC leaves the precondition      *)
(* alone -- that cannot be done through an opaque state predicate.            *)
(* ------------------------------------------------------------------------- *)

let AES256_GCM_ENC_ALT_SUBROUTINE_CORRECT = prove
 (`!in_p out_p tag_p ivec_p key_p htable_p
     tag0 nonce c rk inblock len_bits pc stackpointer returnaddress.
    aligned 16 stackpointer /\
    val in_p + 16 * gcm_wb_blocks len_bits < 2 EXP 63 /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * gcm_wb_blocks len_bits); (tag_p, 16); (ivec_p, 16);
       (word_sub stackpointer (word 80), 80)]
      [(word pc, LENGTH aes256_gcm_enc_alt_mc);
       (in_p, 16 * gcm_wb_blocks len_bits); (key_p, 240); (htable_p, 192)] /\
    PAIRWISE nonoverlapping
      [(out_p, 16 * gcm_wb_blocks len_bits); (tag_p, 16); (ivec_p, 16);
       (word_sub stackpointer (word 80), 80)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) aes256_gcm_enc_alt_mc /\
           read PC s = word pc /\
           read SP s = stackpointer /\
           read X30 s = returnaddress /\
           C_ARGUMENTS
            [in_p; len_bits; out_p; tag_p; ivec_p; key_p; htable_p] s /\
           read (memory :> bytes128 tag_p) s = word_reversefields 8 tag0 /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce c) /\
           wordlist_from_memory(key_p,15) s =
             MAP (word_reversefields 8) rk /\
           htable_mem_8 (ghash_twist (aes256_cipher (word 0) rk)) htable_p s /\
           (!j. j < gcm_wb_blocks len_bits
                ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
                    inblock j))
      (\s. read PC s = returnaddress /\
           C_RETURN s = word (16 * gcm_wb_blocks len_bits) /\
           read (memory :> bytes128 ivec_p) s =
             word_reversefields 8 (ctr_block nonce (gcm_wb_blocks len_bits + c)) /\
           read (memory :> bytes128 tag_p) s =
             word_reversefields 8
               (nist_ghash (aes256_cipher (word 0) rk) tag0
                  (list_of_seq (nist_cipher_block aes256_cipher c nonce rk inblock)
                               (gcm_wb_blocks len_bits))) /\
           (!j. j < gcm_wb_blocks len_bits
                ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                    word_xor (aes_ctr_block aes256_cipher c nonce rk (j)) (inblock j)))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * gcm_wb_blocks len_bits);
                  memory :> bytes(tag_p, 16);
                  memory :> bytes(ivec_p, 16);
                  memory :> bytes(word_sub stackpointer (word 80), 80)])`,
  MATCH_ACCEPT_TAC(ARM_ADD_IBT_RULE ~extra:[htable_mem_8; htable_mem_4; wordlist_from_memory]
                     aes256_gcm_enc_alt_mc aes256_gcm_enc_alt_tmc
                     AES256_GCM_ENC_ALT_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* The exported theorem at the all-zero key.  With rk the FIPS-197 schedule  *)
(* of that key (AESAVS_ZERO_KEY_256_SCHEDULE, common/fips197.ml), the shared *)
(* HTABLE_MEM_8_KEY_CONV evaluates the key-table precondition of             *)
(* AES256_GCM_ENC_ALT_SUBROUTINE_CORRECT to the twelve 16-byte entries that  *)
(* gcm_init_v8 writes for the key, which are also the bytes the C test       *)
(* aes_gcm_htable checks.  So the table described by the exported statement  *)
(* itself, not only by the vocabulary it uses, is the real one: the load     *)
(* fails here unless the precondition evaluates and its first entry is that  *)
(* table's 0x5a9144292508410f7b2b80f144811313.  The decrypt kernel's         *)
(* AES256_GCM_DEC_ALT_ZERO_KEY_CORRECT is the same check.                    *)
(* ------------------------------------------------------------------------- *)

let AES256_GCM_ENC_ALT_ZERO_KEY_CORRECT =
  let th = CONV_RULE (ONCE_DEPTH_CONV
             (HTABLE_MEM_8_KEY_CONV aes256_cipher AESAVS_ZERO_KEY_256_SCHEDULE))
    (INST [`AESAVS_ZERO_KEY_256_SCHEDULE`,`rk:int128 list`]
      (SPEC_ALL AES256_GCM_ENC_ALT_SUBROUTINE_CORRECT)) in
  if can (find_term (fun t -> is_const t && fst(dest_const t) = "htable_mem_8"))
         (concl th) ||
     not (can (find_term ((=) `word 0x5a9144292508410f7b2b80f144811313:int128`))
              (concl th))
  then failwith "AES256_GCM_ENC_ALT_ZERO_KEY_CORRECT: table not the real one"
  else GEN_ALL th;;

(* ========================================================================= *)
(* SAFETY companions (constant-time + memory-safety).  Pure additions; the   *)
(* frozen correctness statements above are unchanged.  See arm/tutorial/      *)
(* safety.ml and bignum_emontredc_8n.ml for the recipe.                       *)
(* ========================================================================= *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

(* --- Core-level leg safety: FAST1..FAST4 (fixed nb, straight-line). ------- *)
(* Entry pc+0x38, exit pc+0x1154; MAYCHANGE frame (ABI, Q8..Q15, out/tag/     *)
(* ivec); f_events depends on the public pointers + stackpointer + pc.        *)

let AES256_GCM_ENC_ALT_FAST1_SAFE = prove
 (`exists f_events.
   !e in_p out_p tag_p ivec_p key_p htable_p stackpointer bit_len
     nb pc.
    nb = 1 /\
    bit_len = 128 * nb /\
    val in_p + 16 * nb < 2 EXP 63 /\
    128 * nb < 2 EXP 64 /\
    nonoverlapping (out_p, 16 * nb)
                   (word pc, LENGTH aes256_gcm_enc_alt_tmc) /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
      [(word pc, LENGTH aes256_gcm_enc_alt_tmc);
       (in_p, 16 * nb); (key_p, 240); (htable_p, 192);
       (word_add stackpointer (word 0x40), 8)] /\
    PAIRWISE nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) aes256_gcm_enc_alt_tmc /\
           read PC s = word (pc + 0x38) /\
           read X0 s = in_p /\
           read X1 s = word bit_len /\
           read X2 s = out_p /\
           read X3 s = tag_p /\
           read X16 s = ivec_p /\
           read X6 s = htable_p /\
           read X11 s = key_p /\
           read X9 s = word (bit_len DIV 8) /\
           read X10 s = word_add stackpointer (word 0x40) /\
           read events s = e)
      (\s. read PC s = word (pc + 0x1154) /\
           (exists e2.
              read events s = APPEND e2 e /\
              e2 = f_events in_p out_p tag_p ivec_p key_p htable_p
                     stackpointer pc /\
              memaccess_inbounds e2
                [in_p, 16 * nb; tag_p, 16; ivec_p, 16; key_p, 240;
                 htable_p, 192; word_add stackpointer (word 0x40), 8]
                [out_p, 16 * nb; tag_p, 16; ivec_p, 16]))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * nb);
                  memory :> bytes(tag_p, 16);
                  memory :> bytes(ivec_p, 16)])`,
  PROVE_SAFETY_SPEC_TAC AES256_GCM_ENC_ALT_EXEC);;

let AES256_GCM_ENC_ALT_FAST2_SAFE = prove
 (`exists f_events.
   !e in_p out_p tag_p ivec_p key_p htable_p stackpointer bit_len
     nb pc.
    nb = 2 /\
    bit_len = 128 * nb /\
    val in_p + 16 * nb < 2 EXP 63 /\
    128 * nb < 2 EXP 64 /\
    nonoverlapping (out_p, 16 * nb)
                   (word pc, LENGTH aes256_gcm_enc_alt_tmc) /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
      [(word pc, LENGTH aes256_gcm_enc_alt_tmc);
       (in_p, 16 * nb); (key_p, 240); (htable_p, 192);
       (word_add stackpointer (word 0x40), 8)] /\
    PAIRWISE nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) aes256_gcm_enc_alt_tmc /\
           read PC s = word (pc + 0x38) /\
           read X0 s = in_p /\
           read X1 s = word bit_len /\
           read X2 s = out_p /\
           read X3 s = tag_p /\
           read X16 s = ivec_p /\
           read X6 s = htable_p /\
           read X11 s = key_p /\
           read X9 s = word (bit_len DIV 8) /\
           read X10 s = word_add stackpointer (word 0x40) /\
           read events s = e)
      (\s. read PC s = word (pc + 0x1154) /\
           (exists e2.
              read events s = APPEND e2 e /\
              e2 = f_events in_p out_p tag_p ivec_p key_p htable_p
                     stackpointer pc /\
              memaccess_inbounds e2
                [in_p, 16 * nb; tag_p, 16; ivec_p, 16; key_p, 240;
                 htable_p, 192; word_add stackpointer (word 0x40), 8]
                [out_p, 16 * nb; tag_p, 16; ivec_p, 16]))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * nb);
                  memory :> bytes(tag_p, 16);
                  memory :> bytes(ivec_p, 16)])`,
  PROVE_SAFETY_SPEC_TAC AES256_GCM_ENC_ALT_EXEC);;

let AES256_GCM_ENC_ALT_FAST3_SAFE = prove
 (`exists f_events.
   !e in_p out_p tag_p ivec_p key_p htable_p stackpointer bit_len
     nb pc.
    nb = 3 /\
    bit_len = 128 * nb /\
    val in_p + 16 * nb < 2 EXP 63 /\
    128 * nb < 2 EXP 64 /\
    nonoverlapping (out_p, 16 * nb)
                   (word pc, LENGTH aes256_gcm_enc_alt_tmc) /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
      [(word pc, LENGTH aes256_gcm_enc_alt_tmc);
       (in_p, 16 * nb); (key_p, 240); (htable_p, 192);
       (word_add stackpointer (word 0x40), 8)] /\
    PAIRWISE nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) aes256_gcm_enc_alt_tmc /\
           read PC s = word (pc + 0x38) /\
           read X0 s = in_p /\
           read X1 s = word bit_len /\
           read X2 s = out_p /\
           read X3 s = tag_p /\
           read X16 s = ivec_p /\
           read X6 s = htable_p /\
           read X11 s = key_p /\
           read X9 s = word (bit_len DIV 8) /\
           read X10 s = word_add stackpointer (word 0x40) /\
           read events s = e)
      (\s. read PC s = word (pc + 0x1154) /\
           (exists e2.
              read events s = APPEND e2 e /\
              e2 = f_events in_p out_p tag_p ivec_p key_p htable_p
                     stackpointer pc /\
              memaccess_inbounds e2
                [in_p, 16 * nb; tag_p, 16; ivec_p, 16; key_p, 240;
                 htable_p, 192; word_add stackpointer (word 0x40), 8]
                [out_p, 16 * nb; tag_p, 16; ivec_p, 16]))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * nb);
                  memory :> bytes(tag_p, 16);
                  memory :> bytes(ivec_p, 16)])`,
  PROVE_SAFETY_SPEC_TAC AES256_GCM_ENC_ALT_EXEC);;

let AES256_GCM_ENC_ALT_FAST4_SAFE = prove
 (`exists f_events.
   !e in_p out_p tag_p ivec_p key_p htable_p stackpointer bit_len
     nb pc.
    nb = 4 /\
    bit_len = 128 * nb /\
    val in_p + 16 * nb < 2 EXP 63 /\
    128 * nb < 2 EXP 64 /\
    nonoverlapping (out_p, 16 * nb)
                   (word pc, LENGTH aes256_gcm_enc_alt_tmc) /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
      [(word pc, LENGTH aes256_gcm_enc_alt_tmc);
       (in_p, 16 * nb); (key_p, 240); (htable_p, 192);
       (word_add stackpointer (word 0x40), 8)] /\
    PAIRWISE nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) aes256_gcm_enc_alt_tmc /\
           read PC s = word (pc + 0x38) /\
           read X0 s = in_p /\
           read X1 s = word bit_len /\
           read X2 s = out_p /\
           read X3 s = tag_p /\
           read X16 s = ivec_p /\
           read X6 s = htable_p /\
           read X11 s = key_p /\
           read X9 s = word (bit_len DIV 8) /\
           read X10 s = word_add stackpointer (word 0x40) /\
           read events s = e)
      (\s. read PC s = word (pc + 0x1154) /\
           (exists e2.
              read events s = APPEND e2 e /\
              e2 = f_events in_p out_p tag_p ivec_p key_p htable_p
                     stackpointer pc /\
              memaccess_inbounds e2
                [in_p, 16 * nb; tag_p, 16; ivec_p, 16; key_p, 240;
                 htable_p, 192; word_add stackpointer (word 0x40), 8]
                [out_p, 16 * nb; tag_p, 16; ivec_p, 16]))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * nb);
                  memory :> bytes(tag_p, 16);
                  memory :> bytes(ivec_p, 16)])`,
  PROVE_SAFETY_SPEC_TAC AES256_GCM_ENC_ALT_EXEC);;


(* --- Setup segment safety: SETUP0_SAFE (nb in {5,6,7,8}, pc+0x38 ->      *)
(* pc+0xee0).  Mirrors AES256_GCM_ENC_ALT_SETUP0's stepping (NSTEP +      *)
(* DISPATCH4/SMALL_NOT_TAKEN + WB_BRANCH_COND_TRUE) but closes with the     *)
(* safety property.  Event trace is nb-independent over {5,6,7,8}.          *)
let AES256_GCM_ENC_ALT_SETUP0_SAFE = prove
 (`exists f_events.
   !e in_p out_p tag_p ivec_p key_p htable_p stackpointer bit_len
     nb pc.
    1 <= nb /\ nb <= 8 /\ ~(nb = 1) /\ ~(nb = 2) /\ ~(nb = 3) /\ ~(nb = 4) /\
    bit_len = 128 * nb /\
    val in_p + 16 * nb < 2 EXP 63 /\
    128 * nb < 2 EXP 64 /\
    nonoverlapping (out_p, 16 * nb)
                   (word pc, LENGTH aes256_gcm_enc_alt_tmc) /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
      [(word pc, LENGTH aes256_gcm_enc_alt_tmc);
       (in_p, 16 * nb); (key_p, 240); (htable_p, 192);
       (word_add stackpointer (word 0x40), 8)] /\
    PAIRWISE nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) aes256_gcm_enc_alt_tmc /\
           read PC s = word (pc + 0x38) /\
           read X0 s = in_p /\
           read X1 s = word bit_len /\
           read X2 s = out_p /\
           read X3 s = tag_p /\
           read X16 s = ivec_p /\
           read X6 s = htable_p /\
           read X11 s = key_p /\
           read X9 s = word (bit_len DIV 8) /\
           read X10 s = word_add stackpointer (word 0x40) /\
           read events s = e)
      (\s. read PC s = word (pc + 0xee0) /\
           read X0 s = in_p /\
           read X2 s = out_p /\
           read X3 s = tag_p /\
           read X9 s = word (16 * nb) /\
           read X4 s = word_add in_p (word (16 * nb)) /\
           read X16 s = ivec_p /\
           read X5 s = in_p /\
           read X6 s = htable_p /\
           read X10 s = word_add stackpointer (word 0x40) /\
           read X11 s = key_p /\
           (exists e2.
              read events s = APPEND e2 e /\
              e2 = f_events in_p out_p tag_p ivec_p key_p htable_p
                     stackpointer pc /\
              memaccess_inbounds e2
                [in_p, 16 * nb; tag_p, 16; ivec_p, 16; key_p, 240;
                 htable_p, 192; word_add stackpointer (word 0x40), 8]
                [out_p, 16 * nb; tag_p, 16; ivec_p, 16]))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * nb);
                  memory :> bytes(tag_p, 16);
                  memory :> bytes(ivec_p, 16)])`,
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; MODIFIABLE_SIMD_REGS;
              MODIFIABLE_GPRS; MODIFIABLE_UPPER_SIMD_REGS] THEN
  REWRITE_TAC[ALLPAIRS; ALL; NONOVERLAPPING_CLAUSES; LENGTH_WB_MC] THEN
  CONCRETIZE_F_EVENTS_TAC
    `\(in_p:int64) (out_p:int64) (tag_p:int64) (ivec_p:int64)
      (key_p:int64) (htable_p:int64) (stackpointer:int64) (pc:num).
       f_ev in_p out_p tag_p ivec_p key_p htable_p stackpointer pc
       :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  SUBGOAL_THEN `~(nb = 4)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `5 <= nb` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY NSTEP (1--5) THEN NSTEP 6 THEN NSTEP 7 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[
    MATCH_MP DISPATCH4_NOT_TAKEN (CONJ (ASSUME `128 * nb < 2 EXP 64`) (ASSUME `~(nb = 4)`));
    MATCH_MP DISPATCH_SMALL_NOT_TAKEN (CONJ (ASSUME `128 * nb < 2 EXP 64`) (ASSUME `5 <= nb`));
    COND_CLAUSES]) THEN
  MAP_EVERY NSTEP (8--36) THEN
  MAP_EVERY NSTEP (37--261) THEN NSTEP 262 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP WB_BRANCH_COND_TRUE
     (CONJ (ASSUME `1 <= nb`) (ASSUME `nb <= 8`)); COND_CLAUSES]) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN TRY SETUP0_DISPATCH THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

(* --- Tail-cascade leg safety: TAIL_REM1..8_SAFE (entry pc+0xee0, exit       *)
(* pc+0x1154).  Mirrors AES256_GCM_ENC_ALT_TAIL_REM<k>'s NSTEP_GP drive +    *)
(* TAIL_X5 branch resolution, but drops the functional Q19-fold/data closers   *)
(* (safety needs only PC+events+inbounds) and closes with the safety property. *)
(* Lean precondition: the key/htable/ivec/counter/inblock CONTENTS are dead    *)
(* for safety (only the ACCESS addresses matter), so only pointer registers    *)
(* are pinned.  nb = 8*g+k gives the rem=k arm; g symbolic.                    *)

let AES256_GCM_ENC_ALT_TAIL_REM1_SAFE = prove
 (`exists f_events.
   !e in_p out_p tag_p ivec_p key_p htable_p mod_p end_p nb g pc.
    nb = 8 * g + 1 /\
    end_p = word_add in_p (word (128 * g)) /\
    val in_p + 16 * nb < 2 EXP 63 /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
      [(word pc, LENGTH aes256_gcm_enc_alt_tmc);
       (in_p, 16 * nb); (key_p, 240); (htable_p, 192); (mod_p, 8)] /\
    PAIRWISE nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) aes256_gcm_enc_alt_tmc /\
           read PC s = word (pc + 0xee0) /\
           read X0 s = word_add in_p (word (128 * g)) /\
           read X2 s = word_add out_p (word (128 * g)) /\
           read X3 s = tag_p /\
           read X9 s = word (16 * nb) /\
           read X4 s = word_add in_p (word (16 * nb)) /\
           read X16 s = ivec_p /\
           read X5 s = end_p /\
           read X6 s = htable_p /\
           read X10 s = mod_p /\
           read X11 s = key_p /\
           read events s = e)
      (\s. read PC s = word (pc + 0x1154) /\
           (exists e2.
              read events s = APPEND e2 e /\
              e2 = f_events in_p out_p tag_p ivec_p key_p htable_p mod_p g pc /\
              memaccess_inbounds e2
                [in_p, 16 * nb; tag_p, 16; ivec_p, 16; key_p, 240;
                 htable_p, 192; mod_p, 8]
                [out_p, 16 * nb; tag_p, 16; ivec_p, 16]))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * nb);
                  memory :> bytes(tag_p, 16);
                  memory :> bytes(ivec_p, 16)])`,
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; MODIFIABLE_SIMD_REGS;
              MODIFIABLE_GPRS; MODIFIABLE_UPPER_SIMD_REGS] THEN
  REWRITE_TAC[ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES; LENGTH_WB_MC] THEN
  CONCRETIZE_F_EVENTS_TAC
    `\(in_p:int64) (out_p:int64) (tag_p:int64) (ivec_p:int64)
      (key_p:int64) (htable_p:int64) (mod_p:int64) (g:num) (pc:num).
       f_ev in_p out_p tag_p ivec_p key_p htable_p mod_p g pc
       :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  MAP_EVERY NSTEP_GP (1--9) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[TAIL_X5_REM1]) THEN
  MAP_EVERY NSTEP_GP (10--85) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

let AES256_GCM_ENC_ALT_TAIL_REM2_SAFE = prove
 (`exists f_events.
   !e in_p out_p tag_p ivec_p key_p htable_p mod_p end_p nb g pc.
    nb = 8 * g + 2 /\
    end_p = word_add in_p (word (128 * g)) /\
    val in_p + 16 * nb < 2 EXP 63 /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
      [(word pc, LENGTH aes256_gcm_enc_alt_tmc);
       (in_p, 16 * nb); (key_p, 240); (htable_p, 192); (mod_p, 8)] /\
    PAIRWISE nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) aes256_gcm_enc_alt_tmc /\
           read PC s = word (pc + 0xee0) /\
           read X0 s = word_add in_p (word (128 * g)) /\
           read X2 s = word_add out_p (word (128 * g)) /\
           read X3 s = tag_p /\
           read X9 s = word (16 * nb) /\
           read X4 s = word_add in_p (word (16 * nb)) /\
           read X16 s = ivec_p /\
           read X5 s = end_p /\
           read X6 s = htable_p /\
           read X10 s = mod_p /\
           read X11 s = key_p /\
           read events s = e)
      (\s. read PC s = word (pc + 0x1154) /\
           (exists e2.
              read events s = APPEND e2 e /\
              e2 = f_events in_p out_p tag_p ivec_p key_p htable_p mod_p g pc /\
              memaccess_inbounds e2
                [in_p, 16 * nb; tag_p, 16; ivec_p, 16; key_p, 240;
                 htable_p, 192; mod_p, 8]
                [out_p, 16 * nb; tag_p, 16; ivec_p, 16]))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * nb);
                  memory :> bytes(tag_p, 16);
                  memory :> bytes(ivec_p, 16)])`,
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; MODIFIABLE_SIMD_REGS;
              MODIFIABLE_GPRS; MODIFIABLE_UPPER_SIMD_REGS] THEN
  REWRITE_TAC[ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES; LENGTH_WB_MC] THEN
  CONCRETIZE_F_EVENTS_TAC
    `\(in_p:int64) (out_p:int64) (tag_p:int64) (ivec_p:int64)
      (key_p:int64) (htable_p:int64) (mod_p:int64) (g:num) (pc:num).
       f_ev in_p out_p tag_p ivec_p key_p htable_p mod_p g pc
       :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  MAP_EVERY NSTEP_GP (1--9) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[TAIL_X5_REM2]) THEN
  MAP_EVERY NSTEP_GP (10--57) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

let AES256_GCM_ENC_ALT_TAIL_REM3_SAFE = prove
 (`exists f_events.
   !e in_p out_p tag_p ivec_p key_p htable_p mod_p end_p nb g pc.
    nb = 8 * g + 3 /\
    end_p = word_add in_p (word (128 * g)) /\
    val in_p + 16 * nb < 2 EXP 63 /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
      [(word pc, LENGTH aes256_gcm_enc_alt_tmc);
       (in_p, 16 * nb); (key_p, 240); (htable_p, 192); (mod_p, 8)] /\
    PAIRWISE nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) aes256_gcm_enc_alt_tmc /\
           read PC s = word (pc + 0xee0) /\
           read X0 s = word_add in_p (word (128 * g)) /\
           read X2 s = word_add out_p (word (128 * g)) /\
           read X3 s = tag_p /\
           read X9 s = word (16 * nb) /\
           read X4 s = word_add in_p (word (16 * nb)) /\
           read X16 s = ivec_p /\
           read X5 s = end_p /\
           read X6 s = htable_p /\
           read X10 s = mod_p /\
           read X11 s = key_p /\
           read events s = e)
      (\s. read PC s = word (pc + 0x1154) /\
           (exists e2.
              read events s = APPEND e2 e /\
              e2 = f_events in_p out_p tag_p ivec_p key_p htable_p mod_p g pc /\
              memaccess_inbounds e2
                [in_p, 16 * nb; tag_p, 16; ivec_p, 16; key_p, 240;
                 htable_p, 192; mod_p, 8]
                [out_p, 16 * nb; tag_p, 16; ivec_p, 16]))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * nb);
                  memory :> bytes(tag_p, 16);
                  memory :> bytes(ivec_p, 16)])`,
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; MODIFIABLE_SIMD_REGS;
              MODIFIABLE_GPRS; MODIFIABLE_UPPER_SIMD_REGS] THEN
  REWRITE_TAC[ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES; LENGTH_WB_MC] THEN
  CONCRETIZE_F_EVENTS_TAC
    `\(in_p:int64) (out_p:int64) (tag_p:int64) (ivec_p:int64)
      (key_p:int64) (htable_p:int64) (mod_p:int64) (g:num) (pc:num).
       f_ev in_p out_p tag_p ivec_p key_p htable_p mod_p g pc
       :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  MAP_EVERY NSTEP_GP (1--9) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[TAIL_X5_REM3]) THEN
  MAP_EVERY NSTEP_GP (10--110) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

let AES256_GCM_ENC_ALT_TAIL_REM4_SAFE = prove
 (`exists f_events.
   !e in_p out_p tag_p ivec_p key_p htable_p mod_p end_p nb g pc.
    nb = 8 * g + 4 /\
    end_p = word_add in_p (word (128 * g)) /\
    val in_p + 16 * nb < 2 EXP 63 /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
      [(word pc, LENGTH aes256_gcm_enc_alt_tmc);
       (in_p, 16 * nb); (key_p, 240); (htable_p, 192); (mod_p, 8)] /\
    PAIRWISE nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) aes256_gcm_enc_alt_tmc /\
           read PC s = word (pc + 0xee0) /\
           read X0 s = word_add in_p (word (128 * g)) /\
           read X2 s = word_add out_p (word (128 * g)) /\
           read X3 s = tag_p /\
           read X9 s = word (16 * nb) /\
           read X4 s = word_add in_p (word (16 * nb)) /\
           read X16 s = ivec_p /\
           read X5 s = end_p /\
           read X6 s = htable_p /\
           read X10 s = mod_p /\
           read X11 s = key_p /\
           read events s = e)
      (\s. read PC s = word (pc + 0x1154) /\
           (exists e2.
              read events s = APPEND e2 e /\
              e2 = f_events in_p out_p tag_p ivec_p key_p htable_p mod_p g pc /\
              memaccess_inbounds e2
                [in_p, 16 * nb; tag_p, 16; ivec_p, 16; key_p, 240;
                 htable_p, 192; mod_p, 8]
                [out_p, 16 * nb; tag_p, 16; ivec_p, 16]))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * nb);
                  memory :> bytes(tag_p, 16);
                  memory :> bytes(ivec_p, 16)])`,
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; MODIFIABLE_SIMD_REGS;
              MODIFIABLE_GPRS; MODIFIABLE_UPPER_SIMD_REGS] THEN
  REWRITE_TAC[ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES; LENGTH_WB_MC] THEN
  CONCRETIZE_F_EVENTS_TAC
    `\(in_p:int64) (out_p:int64) (tag_p:int64) (ivec_p:int64)
      (key_p:int64) (htable_p:int64) (mod_p:int64) (g:num) (pc:num).
       f_ev in_p out_p tag_p ivec_p key_p htable_p mod_p g pc
       :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  MAP_EVERY NSTEP_GP (1--9) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[TAIL_X5_REM4]) THEN
  MAP_EVERY NSTEP_GP (10--110) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

let AES256_GCM_ENC_ALT_TAIL_REM5_SAFE = prove
 (`exists f_events.
   !e in_p out_p tag_p ivec_p key_p htable_p mod_p end_p nb g pc.
    nb = 8 * g + 5 /\
    end_p = word_add in_p (word (128 * g)) /\
    val in_p + 16 * nb < 2 EXP 63 /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
      [(word pc, LENGTH aes256_gcm_enc_alt_tmc);
       (in_p, 16 * nb); (key_p, 240); (htable_p, 192); (mod_p, 8)] /\
    PAIRWISE nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) aes256_gcm_enc_alt_tmc /\
           read PC s = word (pc + 0xee0) /\
           read X0 s = word_add in_p (word (128 * g)) /\
           read X2 s = word_add out_p (word (128 * g)) /\
           read X3 s = tag_p /\
           read X9 s = word (16 * nb) /\
           read X4 s = word_add in_p (word (16 * nb)) /\
           read X16 s = ivec_p /\
           read X5 s = end_p /\
           read X6 s = htable_p /\
           read X10 s = mod_p /\
           read X11 s = key_p /\
           read events s = e)
      (\s. read PC s = word (pc + 0x1154) /\
           (exists e2.
              read events s = APPEND e2 e /\
              e2 = f_events in_p out_p tag_p ivec_p key_p htable_p mod_p g pc /\
              memaccess_inbounds e2
                [in_p, 16 * nb; tag_p, 16; ivec_p, 16; key_p, 240;
                 htable_p, 192; mod_p, 8]
                [out_p, 16 * nb; tag_p, 16; ivec_p, 16]))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * nb);
                  memory :> bytes(tag_p, 16);
                  memory :> bytes(ivec_p, 16)])`,
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; MODIFIABLE_SIMD_REGS;
              MODIFIABLE_GPRS; MODIFIABLE_UPPER_SIMD_REGS] THEN
  REWRITE_TAC[ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES; LENGTH_WB_MC] THEN
  CONCRETIZE_F_EVENTS_TAC
    `\(in_p:int64) (out_p:int64) (tag_p:int64) (ivec_p:int64)
      (key_p:int64) (htable_p:int64) (mod_p:int64) (g:num) (pc:num).
       f_ev in_p out_p tag_p ivec_p key_p htable_p mod_p g pc
       :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  MAP_EVERY NSTEP_GP (1--9) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[TAIL_X5_REM5]) THEN
  MAP_EVERY NSTEP_GP (10--119) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

let AES256_GCM_ENC_ALT_TAIL_REM6_SAFE = prove
 (`exists f_events.
   !e in_p out_p tag_p ivec_p key_p htable_p mod_p end_p nb g pc.
    nb = 8 * g + 6 /\
    end_p = word_add in_p (word (128 * g)) /\
    val in_p + 16 * nb < 2 EXP 63 /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
      [(word pc, LENGTH aes256_gcm_enc_alt_tmc);
       (in_p, 16 * nb); (key_p, 240); (htable_p, 192); (mod_p, 8)] /\
    PAIRWISE nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) aes256_gcm_enc_alt_tmc /\
           read PC s = word (pc + 0xee0) /\
           read X0 s = word_add in_p (word (128 * g)) /\
           read X2 s = word_add out_p (word (128 * g)) /\
           read X3 s = tag_p /\
           read X9 s = word (16 * nb) /\
           read X4 s = word_add in_p (word (16 * nb)) /\
           read X16 s = ivec_p /\
           read X5 s = end_p /\
           read X6 s = htable_p /\
           read X10 s = mod_p /\
           read X11 s = key_p /\
           read events s = e)
      (\s. read PC s = word (pc + 0x1154) /\
           (exists e2.
              read events s = APPEND e2 e /\
              e2 = f_events in_p out_p tag_p ivec_p key_p htable_p mod_p g pc /\
              memaccess_inbounds e2
                [in_p, 16 * nb; tag_p, 16; ivec_p, 16; key_p, 240;
                 htable_p, 192; mod_p, 8]
                [out_p, 16 * nb; tag_p, 16; ivec_p, 16]))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * nb);
                  memory :> bytes(tag_p, 16);
                  memory :> bytes(ivec_p, 16)])`,
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; MODIFIABLE_SIMD_REGS;
              MODIFIABLE_GPRS; MODIFIABLE_UPPER_SIMD_REGS] THEN
  REWRITE_TAC[ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES; LENGTH_WB_MC] THEN
  CONCRETIZE_F_EVENTS_TAC
    `\(in_p:int64) (out_p:int64) (tag_p:int64) (ivec_p:int64)
      (key_p:int64) (htable_p:int64) (mod_p:int64) (g:num) (pc:num).
       f_ev in_p out_p tag_p ivec_p key_p htable_p mod_p g pc
       :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  MAP_EVERY NSTEP_GP (1--9) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[TAIL_X5_REM6]) THEN
  MAP_EVERY NSTEP_GP (10--127) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

let AES256_GCM_ENC_ALT_TAIL_REM7_SAFE = prove
 (`exists f_events.
   !e in_p out_p tag_p ivec_p key_p htable_p mod_p end_p nb g pc.
    nb = 8 * g + 7 /\
    end_p = word_add in_p (word (128 * g)) /\
    val in_p + 16 * nb < 2 EXP 63 /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
      [(word pc, LENGTH aes256_gcm_enc_alt_tmc);
       (in_p, 16 * nb); (key_p, 240); (htable_p, 192); (mod_p, 8)] /\
    PAIRWISE nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) aes256_gcm_enc_alt_tmc /\
           read PC s = word (pc + 0xee0) /\
           read X0 s = word_add in_p (word (128 * g)) /\
           read X2 s = word_add out_p (word (128 * g)) /\
           read X3 s = tag_p /\
           read X9 s = word (16 * nb) /\
           read X4 s = word_add in_p (word (16 * nb)) /\
           read X16 s = ivec_p /\
           read X5 s = end_p /\
           read X6 s = htable_p /\
           read X10 s = mod_p /\
           read X11 s = key_p /\
           read events s = e)
      (\s. read PC s = word (pc + 0x1154) /\
           (exists e2.
              read events s = APPEND e2 e /\
              e2 = f_events in_p out_p tag_p ivec_p key_p htable_p mod_p g pc /\
              memaccess_inbounds e2
                [in_p, 16 * nb; tag_p, 16; ivec_p, 16; key_p, 240;
                 htable_p, 192; mod_p, 8]
                [out_p, 16 * nb; tag_p, 16; ivec_p, 16]))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * nb);
                  memory :> bytes(tag_p, 16);
                  memory :> bytes(ivec_p, 16)])`,
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; MODIFIABLE_SIMD_REGS;
              MODIFIABLE_GPRS; MODIFIABLE_UPPER_SIMD_REGS] THEN
  REWRITE_TAC[ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES; LENGTH_WB_MC] THEN
  CONCRETIZE_F_EVENTS_TAC
    `\(in_p:int64) (out_p:int64) (tag_p:int64) (ivec_p:int64)
      (key_p:int64) (htable_p:int64) (mod_p:int64) (g:num) (pc:num).
       f_ev in_p out_p tag_p ivec_p key_p htable_p mod_p g pc
       :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  MAP_EVERY NSTEP_GP (1--9) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[TAIL_X5_REM7]) THEN
  MAP_EVERY NSTEP_GP (10--133) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

let AES256_GCM_ENC_ALT_TAIL_REM8_SAFE = prove
 (`exists f_events.
   !e in_p out_p tag_p ivec_p key_p htable_p mod_p end_p nb g pc.
    8 * g + 8 = nb /\
    end_p = word_add in_p (word (128 * g)) /\
    val in_p + 16 * nb < 2 EXP 63 /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
      [(word pc, LENGTH aes256_gcm_enc_alt_tmc);
       (in_p, 16 * nb); (key_p, 240); (htable_p, 192); (mod_p, 8)] /\
    PAIRWISE nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) aes256_gcm_enc_alt_tmc /\
           read PC s = word (pc + 0xee0) /\
           read X0 s = word_add in_p (word (128 * g)) /\
           read X2 s = word_add out_p (word (128 * g)) /\
           read X3 s = tag_p /\
           read X9 s = word (16 * nb) /\
           read X4 s = word_add in_p (word (16 * nb)) /\
           read X16 s = ivec_p /\
           read X5 s = end_p /\
           read X6 s = htable_p /\
           read X10 s = mod_p /\
           read X11 s = key_p /\
           read events s = e)
      (\s. read PC s = word (pc + 0x1154) /\
           (exists e2.
              read events s = APPEND e2 e /\
              e2 = f_events in_p out_p tag_p ivec_p key_p htable_p mod_p g pc /\
              memaccess_inbounds e2
                [in_p, 16 * nb; tag_p, 16; ivec_p, 16; key_p, 240;
                 htable_p, 192; mod_p, 8]
                [out_p, 16 * nb; tag_p, 16; ivec_p, 16]))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * nb);
                  memory :> bytes(tag_p, 16);
                  memory :> bytes(ivec_p, 16)])`,
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; MODIFIABLE_SIMD_REGS;
              MODIFIABLE_GPRS; MODIFIABLE_UPPER_SIMD_REGS] THEN
  REWRITE_TAC[ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES; LENGTH_WB_MC] THEN
  CONCRETIZE_F_EVENTS_TAC
    `\(in_p:int64) (out_p:int64) (tag_p:int64) (ivec_p:int64)
      (key_p:int64) (htable_p:int64) (mod_p:int64) (g:num) (pc:num).
       f_ev in_p out_p tag_p ivec_p key_p htable_p mod_p g pc
       :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  MAP_EVERY NSTEP_GP (1--9) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP TAIL_X5_128_G (ASSUME `8 * g + 8 = nb`)]) THEN
  MAP_EVERY NSTEP_GP (10--119) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;


(* --- Tail dispatch safety: TAIL_REM_SAFE (rem in 1..8, g>=0).  Mirrors       *)
(* AES256_GCM_ENC_ALT_TAIL_REM's r=1\/..\/r=8 case split: X_CHOOSE each      *)
(* arm's event-trace witness, provide the explicit r-indexed dispatch function *)
(* as f_events, then close each branch by the matching TAIL_REM<k>_SAFE.       *)

let AES256_GCM_ENC_ALT_TAIL_REM_SAFE = prove
 (`exists f_events.
   !e in_p out_p tag_p ivec_p key_p htable_p mod_p end_p nb r g pc.
    nb = 8 * g + r /\ 1 <= r /\ r <= 8 /\
    end_p = word_add in_p (word (128 * g)) /\
    val in_p + 16 * nb < 2 EXP 63 /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
      [(word pc, LENGTH aes256_gcm_enc_alt_tmc);
       (in_p, 16 * nb); (key_p, 240); (htable_p, 192); (mod_p, 8)] /\
    PAIRWISE nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) aes256_gcm_enc_alt_tmc /\
           read PC s = word (pc + 0xee0) /\
           read X0 s = word_add in_p (word (128 * g)) /\
           read X2 s = word_add out_p (word (128 * g)) /\
           read X3 s = tag_p /\
           read X9 s = word (16 * nb) /\
           read X4 s = word_add in_p (word (16 * nb)) /\
           read X16 s = ivec_p /\
           read X5 s = end_p /\
           read X6 s = htable_p /\
           read X10 s = mod_p /\
           read X11 s = key_p /\
           read events s = e)
      (\s. read PC s = word (pc + 0x1154) /\
           (exists e2.
              read events s = APPEND e2 e /\
              e2 = f_events r in_p out_p tag_p ivec_p key_p htable_p mod_p g pc /\
              memaccess_inbounds e2
                [in_p, 16 * nb; tag_p, 16; ivec_p, 16; key_p, 240;
                 htable_p, 192; mod_p, 8]
                [out_p, 16 * nb; tag_p, 16; ivec_p, 16]))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * nb);
                  memory :> bytes(tag_p, 16);
                  memory :> bytes(ivec_p, 16)])`,
  X_CHOOSE_TAC `w1:int64->int64->int64->int64->int64->int64->int64->num->num->(uarch_event)list` AES256_GCM_ENC_ALT_TAIL_REM1_SAFE THEN
  X_CHOOSE_TAC `w2:int64->int64->int64->int64->int64->int64->int64->num->num->(uarch_event)list` AES256_GCM_ENC_ALT_TAIL_REM2_SAFE THEN
  X_CHOOSE_TAC `w3:int64->int64->int64->int64->int64->int64->int64->num->num->(uarch_event)list` AES256_GCM_ENC_ALT_TAIL_REM3_SAFE THEN
  X_CHOOSE_TAC `w4:int64->int64->int64->int64->int64->int64->int64->num->num->(uarch_event)list` AES256_GCM_ENC_ALT_TAIL_REM4_SAFE THEN
  X_CHOOSE_TAC `w5:int64->int64->int64->int64->int64->int64->int64->num->num->(uarch_event)list` AES256_GCM_ENC_ALT_TAIL_REM5_SAFE THEN
  X_CHOOSE_TAC `w6:int64->int64->int64->int64->int64->int64->int64->num->num->(uarch_event)list` AES256_GCM_ENC_ALT_TAIL_REM6_SAFE THEN
  X_CHOOSE_TAC `w7:int64->int64->int64->int64->int64->int64->int64->num->num->(uarch_event)list` AES256_GCM_ENC_ALT_TAIL_REM7_SAFE THEN
  X_CHOOSE_TAC `w8:int64->int64->int64->int64->int64->int64->int64->num->num->(uarch_event)list` AES256_GCM_ENC_ALT_TAIL_REM8_SAFE THEN
  EXISTS_TAC
   `\(r:num) (in_p:int64) (out_p:int64) (tag_p:int64) (ivec_p:int64)
     (key_p:int64) (htable_p:int64) (mod_p:int64) (g:num) (pc:num).
      if r = 1 then w1 in_p out_p tag_p ivec_p key_p htable_p mod_p g pc
      else if r = 2 then w2 in_p out_p tag_p ivec_p key_p htable_p mod_p g pc
      else if r = 3 then w3 in_p out_p tag_p ivec_p key_p htable_p mod_p g pc
      else if r = 4 then w4 in_p out_p tag_p ivec_p key_p htable_p mod_p g pc
      else if r = 5 then w5 in_p out_p tag_p ivec_p key_p htable_p mod_p g pc
      else if r = 6 then w6 in_p out_p tag_p ivec_p key_p htable_p mod_p g pc
      else if r = 7 then w7 in_p out_p tag_p ivec_p key_p htable_p mod_p g pc
      else w8 in_p out_p tag_p ivec_p key_p htable_p mod_p g pc
      :(uarch_event)list` THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `in_p:int64`; `out_p:int64`; `tag_p:int64`;
    `ivec_p:int64`; `key_p:int64`; `htable_p:int64`; `mod_p:int64`;
    `end_p:int64`; `nb:num`; `r:num`; `g:num`; `pc:num`] THEN
  STRIP_TAC THEN
  BETA_TAC THEN
  SUBGOAL_THEN `r = 1 \/ r = 2 \/ r = 3 \/ r = 4 \/ r = 5 \/ r = 6 \/ r = 7 \/ r = 8`
  MP_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(fun th ->
    if is_eq(concl th) && lhs(concl th) = `r:num`
    then SUBST_ALL_TAC th else failwith "not r-eq") THEN
  REWRITE_TAC[ARITH_EQ; COND_CLAUSES] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  REPEAT CONJ_TAC THEN
  (FIRST_ASSUM ACCEPT_TAC ORELSE ASM_ARITH_TAC ORELSE
   (REWRITE_TAC[ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES] THEN
    ASM_REWRITE_TAC[]) ORELSE
   CONV_TAC WORD_RULE));;

(* --- Whole-core safety for nb in {5,6,7,8}: SETUP0_TAIL_SAFE (pc+0x38 ->     *)
(* pc+0x1154).  Composes the strengthened SETUP0_SAFE (nb-independent setup     *)
(* segment, tail-entry registers in its post) with TAIL_REM_SAFE (g=0, r=nb)    *)
(* by a DOUBLE ABSTRACT BIGSTEP: bigstep SETUP0_SAFE with e_tail=[] (its trace  *)
(* stays the abstract f_events_callee), then bigstep TAIL_REM_SAFE with e_tail  *)
(* = that abstract setup trace (a single term -> no CONS blowup).  f_events     *)
(* takes nb because the tail's event trace depends on nb (= r).                 *)
let AES256_GCM_ENC_ALT_SETUP0_TAIL_SAFE = prove
 (`exists f_events.
   !e in_p out_p tag_p ivec_p key_p htable_p stackpointer bit_len
     nb pc.
    1 <= nb /\ nb <= 8 /\ ~(nb = 1) /\ ~(nb = 2) /\ ~(nb = 3) /\ ~(nb = 4) /\
    bit_len = 128 * nb /\
    val in_p + 16 * nb < 2 EXP 63 /\
    128 * nb < 2 EXP 64 /\
    nonoverlapping (out_p, 16 * nb)
                   (word pc, LENGTH aes256_gcm_enc_alt_tmc) /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
      [(word pc, LENGTH aes256_gcm_enc_alt_tmc);
       (in_p, 16 * nb); (key_p, 240); (htable_p, 192);
       (word_add stackpointer (word 0x40), 8)] /\
    PAIRWISE nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) aes256_gcm_enc_alt_tmc /\
           read PC s = word (pc + 0x38) /\
           read X0 s = in_p /\
           read X1 s = word bit_len /\
           read X2 s = out_p /\
           read X3 s = tag_p /\
           read X16 s = ivec_p /\
           read X6 s = htable_p /\
           read X11 s = key_p /\
           read X9 s = word (bit_len DIV 8) /\
           read X10 s = word_add stackpointer (word 0x40) /\
           read events s = e)
      (\s. read PC s = word (pc + 0x1154) /\
           (exists e2.
              read events s = APPEND e2 e /\
              e2 = f_events nb in_p out_p tag_p ivec_p key_p htable_p
                     stackpointer pc /\
              memaccess_inbounds e2
                [in_p, 16 * nb; tag_p, 16; ivec_p, 16; key_p, 240;
                 htable_p, 192; word_add stackpointer (word 0x40), 8]
                [out_p, 16 * nb; tag_p, 16; ivec_p, 16]))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * nb);
                  memory :> bytes(tag_p, 16);
                  memory :> bytes(ivec_p, 16)])`,
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; MODIFIABLE_SIMD_REGS;
              MODIFIABLE_GPRS; MODIFIABLE_UPPER_SIMD_REGS] THEN
  REWRITE_TAC[ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES; LENGTH_WB_MC] THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC AES256_GCM_ENC_ALT_TAIL_REM_SAFE "H_TAIL" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC AES256_GCM_ENC_ALT_SETUP0_SAFE "H_SETUP0" THEN
  CONCRETIZE_F_EVENTS_TAC
    `\(nb:num) (in_p:int64) (out_p:int64) (tag_p:int64) (ivec_p:int64)
      (key_p:int64) (htable_p:int64) (stackpointer:int64) (pc:num).
       APPEND
         (f_ev_tail nb in_p out_p tag_p ivec_p key_p htable_p stackpointer pc)
         (f_ev_setup in_p out_p tag_p ivec_p key_p htable_p stackpointer pc)
       :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
    MODIFIABLE_SIMD_REGS; MODIFIABLE_GPRS; MODIFIABLE_UPPER_SIMD_REGS]) THEN
  (* ===== BIGSTEP 1: SETUP0 (pc+0x38 -> pc+0xee0), e_tail = [] ===== *)
  USE_THEN "H_SETUP0" (fun th ->
    MP_TAC (REWRITE_RULE[APPEND]
      (SPECL [`e:(uarch_event)list`; `in_p:int64`; `out_p:int64`; `tag_p:int64`;
              `ivec_p:int64`; `key_p:int64`; `htable_p:int64`; `stackpointer:int64`;
              `bit_len:num`; `nb:num`; `pc:num`; `[]:(uarch_event)list`] th))) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES; LENGTH_WB_MC] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ARM_BIGSTEP_TAC AES256_GCM_ENC_ALT_EXEC "s1" THEN
  (* ===== BIGSTEP 2: TAIL_REM (pc+0xee0 -> pc+0x1154), g=0, r=nb ===== *)
  USE_THEN "H_TAIL" (fun th ->
    MP_TAC (GEN_REWRITE_RULE I [RIGHT_FORALL_IMP_THM]
      (REWRITE_RULE[ARITH_RULE `128 * 0 = 0`; WORD_ADD_0]
        (SPECL [`e:(uarch_event)list`; `in_p:int64`; `out_p:int64`; `tag_p:int64`;
                `ivec_p:int64`; `key_p:int64`; `htable_p:int64`;
                `word_add stackpointer (word 0x40):int64`;
                `word_add in_p (word (128 * 0)):int64`;
                `nb:num`; `nb:num`; `0`; `pc:num`] th)))) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES; LENGTH_WB_MC] THEN
    REPEAT CONJ_TAC THEN
    (FIRST_ASSUM ACCEPT_TAC ORELSE ASM_ARITH_TAC ORELSE ASM_REWRITE_TAC[] ORELSE
     CONV_TAC WORD_RULE);
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[GSYM LEFT_EXISTS_IMP_THM] THEN
  META_EXISTS_TAC THEN
  ARM_BIGSTEP_TAC AES256_GCM_ENC_ALT_EXEC "s2" THENL [
    BINOP_TAC THENL [ UNIFY_REFL_TAC; REFL_TAC ] THEN NO_TAC;
    ALL_TAC ] THEN
  (* ===== CLOSE ===== *)
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SAFE_META_EXISTS_TAC allowed_vars_e THEN
  CONJ_TAC THENL [ EXISTS_E2_TAC allowed_vars_e; ALL_TAC ] THEN
  CONJ_TAC THENL
   [ BINOP_TAC THENL [ UNIFY_F_EVENTS_TAC; UNIFY_F_EVENTS_TAC ];
     DISCHARGE_MEMACCESS_INBOUNDS_TAC ])
;;

(* --- PREPRETAIL_GEN_SAFE (pc+0xa10 -> pc+0xee0): the shared prepretail        *)
(* segment (last full 8-block group's reduction) for nb >= 9.  Lean spec        *)
(* (pointer regs only; content facts dead for safety).  Pointer regs unchanged  *)
(* entry->exit; straight-line NSTEP_GP (1--308) drive.  f_events takes k         *)
(* (access addresses depend on the group index).                                *)
let AES256_GCM_ENC_ALT_PREPRETAIL_GEN_SAFE = prove
 (`exists f_events.
   !e in_p out_p tag_p ivec_p key_p htable_p mod_p end_p nb k pc.
    8 * (k + 1) <= nb /\
    end_p = word_add in_p (word (128 * (k + 1))) /\
    val in_p + 128 * (k + 1) < 2 EXP 63 /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
      [(word pc, LENGTH aes256_gcm_enc_alt_tmc);
       (in_p, 16 * nb); (key_p, 240); (htable_p, 192); (mod_p, 8)] /\
    PAIRWISE nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) aes256_gcm_enc_alt_tmc /\
           read PC s = word (pc + 0xa10) /\
           read X0 s = word_add in_p (word (128 * (k + 1))) /\
           read X2 s = word_add out_p (word (128 * (k + 1))) /\
           read X3 s = tag_p /\
           read X9 s = word (16 * nb) /\
           read X4 s = word_add in_p (word (16 * nb)) /\
           read X16 s = ivec_p /\
           read X5 s = end_p /\
           read X6 s = htable_p /\
           read X10 s = mod_p /\
           read X11 s = key_p /\
           read events s = e)
      (\s. read PC s = word (pc + 0xee0) /\
           read X0 s = word_add in_p (word (128 * (k + 1))) /\
           read X2 s = word_add out_p (word (128 * (k + 1))) /\
           read X3 s = tag_p /\
           read X9 s = word (16 * nb) /\
           read X4 s = word_add in_p (word (16 * nb)) /\
           read X16 s = ivec_p /\
           read X5 s = end_p /\
           read X6 s = htable_p /\
           read X10 s = mod_p /\
           read X11 s = key_p /\
           (exists e2.
              read events s = APPEND e2 e /\
              e2 = f_events in_p out_p tag_p ivec_p key_p htable_p mod_p k pc /\
              memaccess_inbounds e2
                [in_p, 16 * nb; tag_p, 16; ivec_p, 16; key_p, 240;
                 htable_p, 192; mod_p, 8]
                [out_p, 16 * nb; tag_p, 16; ivec_p, 16]))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * nb);
                  memory :> bytes(tag_p, 16);
                  memory :> bytes(ivec_p, 16)])`,
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; MODIFIABLE_SIMD_REGS;
              MODIFIABLE_GPRS; MODIFIABLE_UPPER_SIMD_REGS] THEN
  REWRITE_TAC[ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES; LENGTH_WB_MC] THEN
  CONCRETIZE_F_EVENTS_TAC
    `\(in_p:int64) (out_p:int64) (tag_p:int64) (ivec_p:int64)
      (key_p:int64) (htable_p:int64) (mod_p:int64) (k:num) (pc:num).
       f_ev in_p out_p tag_p ivec_p key_p htable_p mod_p k pc
       :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  MAP_EVERY NSTEP_GP (1--308) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC)
;;

(* --- SETUP_G1_SAFE (pc+0x38 -> pc+0xa10, k=0, nb 9-16): setup for the         *)
(* single-full-group case.  Mirrors SETUP_G1's NSTEP/LDP_SETUP drive + the      *)
(* SETUP_BRANCH_COND_FALSE_GEN / _TRUE_2 guard rewrites; post strengthened with *)
(* the PREPRETAIL_GEN entry registers, closed via SETUP_RECON_TAC_GEN.          *)
let AES256_GCM_ENC_ALT_SETUP_G1_SAFE = prove
 (`exists f_events.
   !e in_p out_p tag_p ivec_p key_p htable_p stackpointer bit_len end_p
     nb k pc.
    k = 0 /\
    8 * (k + 1) <= nb /\
    bit_len = 128 * nb /\
    8 * (k + 1) < nb /\ nb <= 8 * (k + 2) /\
    end_p = word_add in_p (word (128 * (k + 1))) /\
    val in_p + 128 * (k + 1) < 2 EXP 63 /\
    128 * nb < 2 EXP 64 /\
    nonoverlapping (out_p, 16 * nb)
                   (word pc, LENGTH aes256_gcm_enc_alt_tmc) /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
      [(word pc, LENGTH aes256_gcm_enc_alt_tmc);
       (in_p, 16 * nb); (key_p, 240); (htable_p, 192);
       (word_add stackpointer (word 0x40), 8)] /\
    PAIRWISE nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) aes256_gcm_enc_alt_tmc /\
           read PC s = word (pc + 0x38) /\
           read X0 s = in_p /\
           read X1 s = word bit_len /\
           read X2 s = out_p /\
           read X3 s = tag_p /\
           read X16 s = ivec_p /\
           read X6 s = htable_p /\
           read X11 s = key_p /\
           read X9 s = word (bit_len DIV 8) /\
           read X10 s = word_add stackpointer (word 0x40) /\
           read events s = e)
      (\s. read PC s = word (pc + 0xa10) /\
           read X0 s = word_add in_p (word (128 * (0 + 1))) /\
           read X2 s = word_add out_p (word (128 * (0 + 1))) /\
           read X3 s = tag_p /\
           read X9 s = word (16 * nb) /\
           read X4 s = word_add in_p (word (16 * nb)) /\
           read X16 s = ivec_p /\
           read X5 s = end_p /\
           read X6 s = htable_p /\
           read X10 s = word_add stackpointer (word 0x40) /\
           read X11 s = key_p /\
           (exists e2.
              read events s = APPEND e2 e /\
              e2 = f_events in_p out_p tag_p ivec_p key_p htable_p
                     stackpointer pc /\
              memaccess_inbounds e2
                [in_p, 16 * nb; tag_p, 16; ivec_p, 16; key_p, 240;
                 htable_p, 192; word_add stackpointer (word 0x40), 8]
                [out_p, 16 * nb; tag_p, 16; ivec_p, 16]))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * nb);
                  memory :> bytes(tag_p, 16);
                  memory :> bytes(ivec_p, 16)])`,
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; MODIFIABLE_SIMD_REGS;
              MODIFIABLE_GPRS; MODIFIABLE_UPPER_SIMD_REGS] THEN
  REWRITE_TAC[ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES; LENGTH_WB_MC] THEN
  CONCRETIZE_F_EVENTS_TAC
    `\(in_p:int64) (out_p:int64) (tag_p:int64) (ivec_p:int64)
      (key_p:int64) (htable_p:int64) (stackpointer:int64) (pc:num).
       f_ev in_p out_p tag_p ivec_p key_p htable_p stackpointer pc
       :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  SUBGOAL_THEN
   `?inblock. !j. j < nb
      ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s0 =
          inblock j`
   (CHOOSE_THEN ASSUME_TAC) THENL
   [EXISTS_TAC
      `\j. read (memory :> bytes128 (word_add in_p (word (16 * j)))) s0` THEN
    REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~(nb = 4)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `5 <= nb` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY NSTEP (1--5) THEN NSTEP 6 THEN NSTEP 7 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[
    MATCH_MP DISPATCH4_NOT_TAKEN (CONJ (ASSUME `128 * nb < 2 EXP 64`) (ASSUME `~(nb = 4)`));
    MATCH_MP DISPATCH_SMALL_NOT_TAKEN (CONJ (ASSUME `128 * nb < 2 EXP 64`) (ASSUME `5 <= nb`));
    COND_CLAUSES]) THEN
  MAP_EVERY NSTEP (8--36) THEN
  MAP_EVERY NSTEP (37--261) THEN NSTEP 262 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP SETUP_BRANCH_COND_FALSE_GEN
    (CONJ (ASSUME `8 * (k + 1) < nb`) (CONJ (ASSUME `nb <= 8 * (k + 2)`)
          (ASSUME `val (in_p:int64) + 128 * (k + 1) < 2 EXP 63`))); COND_CLAUSES]) THEN
  LDP_SETUP_TAC 263 THEN LDP_SETUP_TAC 264 THEN MAP_EVERY NSTEP (265--271) THEN
  LDP_SETUP_TAC 272 THEN LDP_SETUP_TAC 273 THEN MAP_EVERY NSTEP (274--289) THEN
  NSTEP 290 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP SETUP_BRANCH_COND_TRUE_2
    (CONJ (ASSUME `k = 0`) (CONJ (ASSUME `8 * (k + 1) < nb`)
      (CONJ (ASSUME `nb <= 8 * (k + 2)`)
          (ASSUME `val (in_p:int64) + 128 * (k + 1) < 2 EXP 63`))));
    COND_CLAUSES]) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN TRY SETUP_RECON_TAC_GEN THEN
  DISCHARGE_SAFETY_PROPERTY_TAC)
;;

(* --- PREPRETAIL_TAIL_SAFE (pc+0xa10 -> pc+0x1154): reusable last-group +      *)
(* tail composite (PREPRETAIL_GEN_SAFE o TAIL_REM_SAFE, g=k+1, r=nb-8*(k+1)),   *)
(* general k.  Double abstract bigstep; f_events takes nb,k.                     *)
let AES256_GCM_ENC_ALT_PREPRETAIL_TAIL_SAFE = prove
 (`exists f_events.
   !e in_p out_p tag_p ivec_p key_p htable_p mod_p end_p nb k pc.
    8 * (k + 1) <= nb /\
    8 * (k + 1) < nb /\ nb <= 8 * (k + 2) /\
    end_p = word_add in_p (word (128 * (k + 1))) /\
    val in_p + 128 * (k + 1) < 2 EXP 63 /\
    val in_p + 16 * nb < 2 EXP 63 /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
      [(word pc, LENGTH aes256_gcm_enc_alt_tmc);
       (in_p, 16 * nb); (key_p, 240); (htable_p, 192); (mod_p, 8)] /\
    PAIRWISE nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) aes256_gcm_enc_alt_tmc /\
           read PC s = word (pc + 0xa10) /\
           read X0 s = word_add in_p (word (128 * (k + 1))) /\
           read X2 s = word_add out_p (word (128 * (k + 1))) /\
           read X3 s = tag_p /\
           read X9 s = word (16 * nb) /\
           read X4 s = word_add in_p (word (16 * nb)) /\
           read X16 s = ivec_p /\
           read X5 s = end_p /\
           read X6 s = htable_p /\
           read X10 s = mod_p /\
           read X11 s = key_p /\
           read events s = e)
      (\s. read PC s = word (pc + 0x1154) /\
           (exists e2.
              read events s = APPEND e2 e /\
              e2 = f_events in_p out_p tag_p ivec_p key_p htable_p mod_p nb k pc /\
              memaccess_inbounds e2
                [in_p, 16 * nb; tag_p, 16; ivec_p, 16; key_p, 240;
                 htable_p, 192; mod_p, 8]
                [out_p, 16 * nb; tag_p, 16; ivec_p, 16]))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * nb);
                  memory :> bytes(tag_p, 16);
                  memory :> bytes(ivec_p, 16)])`,
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; MODIFIABLE_SIMD_REGS;
              MODIFIABLE_GPRS; MODIFIABLE_UPPER_SIMD_REGS] THEN
  REWRITE_TAC[ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES; LENGTH_WB_MC] THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC AES256_GCM_ENC_ALT_TAIL_REM_SAFE "H_TAIL" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC AES256_GCM_ENC_ALT_PREPRETAIL_GEN_SAFE "H_PP" THEN
  CONCRETIZE_F_EVENTS_TAC
    `\(in_p:int64) (out_p:int64) (tag_p:int64) (ivec_p:int64)
      (key_p:int64) (htable_p:int64) (mod_p:int64) (nb:num) (k:num) (pc:num).
       APPEND
         (f_ev_tail in_p out_p tag_p ivec_p key_p htable_p mod_p nb k pc)
         (f_ev_pp in_p out_p tag_p ivec_p key_p htable_p mod_p nb k pc)
       :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
    MODIFIABLE_SIMD_REGS; MODIFIABLE_GPRS; MODIFIABLE_UPPER_SIMD_REGS]) THEN
  (* ===== BIGSTEP 1: PREPRETAIL_GEN (pc+0xa10 -> pc+0xee0), e_tail = [] ===== *)
  USE_THEN "H_PP" (fun th ->
    MP_TAC (REWRITE_RULE[APPEND]
      (SPECL [`e:(uarch_event)list`; `in_p:int64`; `out_p:int64`; `tag_p:int64`;
              `ivec_p:int64`; `key_p:int64`; `htable_p:int64`; `mod_p:int64`;
              `end_p:int64`; `nb:num`; `k:num`; `pc:num`;
              `[]:(uarch_event)list`] th))) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES; LENGTH_WB_MC] THEN
    REPEAT CONJ_TAC THEN
    (FIRST_ASSUM ACCEPT_TAC ORELSE ASM_ARITH_TAC ORELSE ASM_REWRITE_TAC[] ORELSE
     CONV_TAC WORD_RULE);
    ALL_TAC] THEN
  ARM_BIGSTEP_TAC AES256_GCM_ENC_ALT_EXEC "s1" THEN
  (* ===== BIGSTEP 2: TAIL_REM (pc+0xee0 -> pc+0x1154), g=k+1, r=nb-8*(k+1) ===== *)
  USE_THEN "H_TAIL" (fun th ->
    MP_TAC (GEN_REWRITE_RULE I [RIGHT_FORALL_IMP_THM]
      (SPECL [`e:(uarch_event)list`; `in_p:int64`; `out_p:int64`; `tag_p:int64`;
              `ivec_p:int64`; `key_p:int64`; `htable_p:int64`; `mod_p:int64`;
              `end_p:int64`;
              `nb:num`; `nb - 8 * (k + 1)`; `k + 1`; `pc:num`] th))) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES; LENGTH_WB_MC] THEN
    REPEAT CONJ_TAC THEN
    (FIRST_ASSUM ACCEPT_TAC ORELSE ASM_ARITH_TAC ORELSE ASM_REWRITE_TAC[] ORELSE
     CONV_TAC WORD_RULE);
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[GSYM LEFT_EXISTS_IMP_THM] THEN
  META_EXISTS_TAC THEN
  ARM_BIGSTEP_TAC AES256_GCM_ENC_ALT_EXEC "s2" THENL [
    BINOP_TAC THENL [ UNIFY_REFL_TAC; REFL_TAC ] THEN NO_TAC;
    ALL_TAC ] THEN
  (* ===== CLOSE ===== *)
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SAFE_META_EXISTS_TAC allowed_vars_e THEN
  CONJ_TAC THENL [ EXISTS_E2_TAC allowed_vars_e; ALL_TAC ] THEN
  CONJ_TAC THENL
   [ BINOP_TAC THENL [ UNIFY_F_EVENTS_TAC; UNIFY_F_EVENTS_TAC ];
     DISCHARGE_MEMACCESS_INBOUNDS_TAC ])
;;

(* --- Whole-core safety for nb 9-16: FIXED_CORRECT_G1_SAFE (pc+0x38 ->         *)
(* pc+0x1154, k=0).  SETUP_G1_SAFE o PREPRETAIL_TAIL_SAFE (double bigstep).      *)
(* f_events takes nb.                                                           *)
let AES256_GCM_ENC_ALT_FIXED_CORRECT_G1_SAFE = prove
 (`exists f_events.
   !e in_p out_p tag_p ivec_p key_p htable_p stackpointer bit_len end_p
     nb k pc.
    k = 0 /\
    8 * (k + 1) <= nb /\
    bit_len = 128 * nb /\
    8 * (k + 1) < nb /\ nb <= 8 * (k + 2) /\
    val in_p + 16 * nb < 2 EXP 63 /\
    end_p = word_add in_p (word (128 * (k + 1))) /\
    val in_p + 128 * (k + 1) < 2 EXP 63 /\
    128 * nb < 2 EXP 64 /\
    nonoverlapping (out_p, 16 * nb)
                   (word pc, LENGTH aes256_gcm_enc_alt_tmc) /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
      [(word pc, LENGTH aes256_gcm_enc_alt_tmc);
       (in_p, 16 * nb); (key_p, 240); (htable_p, 192);
       (word_add stackpointer (word 0x40), 8)] /\
    PAIRWISE nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) aes256_gcm_enc_alt_tmc /\
           read PC s = word (pc + 0x38) /\
           read X0 s = in_p /\
           read X1 s = word bit_len /\
           read X2 s = out_p /\
           read X3 s = tag_p /\
           read X16 s = ivec_p /\
           read X6 s = htable_p /\
           read X11 s = key_p /\
           read X9 s = word (bit_len DIV 8) /\
           read X10 s = word_add stackpointer (word 0x40) /\
           read events s = e)
      (\s. read PC s = word (pc + 0x1154) /\
           (exists e2.
              read events s = APPEND e2 e /\
              e2 = f_events nb in_p out_p tag_p ivec_p key_p htable_p
                     stackpointer pc /\
              memaccess_inbounds e2
                [in_p, 16 * nb; tag_p, 16; ivec_p, 16; key_p, 240;
                 htable_p, 192; word_add stackpointer (word 0x40), 8]
                [out_p, 16 * nb; tag_p, 16; ivec_p, 16]))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * nb);
                  memory :> bytes(tag_p, 16);
                  memory :> bytes(ivec_p, 16)])`,
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; MODIFIABLE_SIMD_REGS;
              MODIFIABLE_GPRS; MODIFIABLE_UPPER_SIMD_REGS] THEN
  REWRITE_TAC[ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES; LENGTH_WB_MC] THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC AES256_GCM_ENC_ALT_PREPRETAIL_TAIL_SAFE "H_PT" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC AES256_GCM_ENC_ALT_SETUP_G1_SAFE "H_SETUP" THEN
  CONCRETIZE_F_EVENTS_TAC
    `\(nb:num) (in_p:int64) (out_p:int64) (tag_p:int64) (ivec_p:int64)
      (key_p:int64) (htable_p:int64) (stackpointer:int64) (pc:num).
       APPEND
         (f_ev_pt nb in_p out_p tag_p ivec_p key_p htable_p stackpointer pc)
         (f_ev_setup nb in_p out_p tag_p ivec_p key_p htable_p stackpointer pc)
       :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
    MODIFIABLE_SIMD_REGS; MODIFIABLE_GPRS; MODIFIABLE_UPPER_SIMD_REGS]) THEN
  (* ===== BIGSTEP 1: SETUP_G1 (pc+0x38 -> pc+0xa10), e_tail = [] ===== *)
  USE_THEN "H_SETUP" (fun th ->
    MP_TAC (REWRITE_RULE[APPEND]
      (SPECL [`e:(uarch_event)list`; `in_p:int64`; `out_p:int64`; `tag_p:int64`;
              `ivec_p:int64`; `key_p:int64`; `htable_p:int64`; `stackpointer:int64`;
              `bit_len:num`; `end_p:int64`; `nb:num`; `k:num`;
              `pc:num`; `[]:(uarch_event)list`] th))) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES; LENGTH_WB_MC] THEN
    REPEAT CONJ_TAC THEN
    (FIRST_ASSUM ACCEPT_TAC ORELSE ASM_ARITH_TAC ORELSE ASM_REWRITE_TAC[] ORELSE
     CONV_TAC WORD_RULE);
    ALL_TAC] THEN
  ARM_BIGSTEP_TAC AES256_GCM_ENC_ALT_EXEC "s1" THEN
  (* ===== BIGSTEP 2: PREPRETAIL_TAIL (pc+0xa10 -> pc+0x1154), k=0 ===== *)
  USE_THEN "H_PT" (fun th ->
    MP_TAC (GEN_REWRITE_RULE I [RIGHT_FORALL_IMP_THM]
      (SPECL [`e:(uarch_event)list`; `in_p:int64`; `out_p:int64`; `tag_p:int64`;
              `ivec_p:int64`; `key_p:int64`; `htable_p:int64`;
              `word_add stackpointer (word 0x40):int64`; `end_p:int64`;
              `nb:num`; `0`; `pc:num`] th))) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES; LENGTH_WB_MC] THEN
    REPEAT CONJ_TAC THEN
    (FIRST_ASSUM ACCEPT_TAC ORELSE ASM_ARITH_TAC ORELSE ASM_REWRITE_TAC[] ORELSE
     CONV_TAC WORD_RULE);
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[GSYM LEFT_EXISTS_IMP_THM] THEN
  META_EXISTS_TAC THEN
  ARM_BIGSTEP_TAC AES256_GCM_ENC_ALT_EXEC "s2" THENL [
    BINOP_TAC THENL [ UNIFY_REFL_TAC; REFL_TAC ] THEN NO_TAC;
    ALL_TAC ] THEN
  (* ===== CLOSE ===== *)
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SAFE_META_EXISTS_TAC allowed_vars_e THEN
  CONJ_TAC THENL [ EXISTS_E2_TAC allowed_vars_e; ALL_TAC ] THEN
  CONJ_TAC THENL
   [ BINOP_TAC THENL [ UNIFY_F_EVENTS_TAC; UNIFY_F_EVENTS_TAC ];
     DISCHARGE_MEMACCESS_INBOUNDS_TAC ])
;;

(* --- SETUP_GEN_SAFE (pc+0x38 -> pc+0x4c0, k<>0, nb>=17): setup for the        *)
(* general (main-loop) case.  Identical to SETUP_G1_SAFE except the closing     *)
(* branch is SETUP_BRANCH_COND_FALSE_2_GEN (~(k=0): fall into the main loop at   *)
(* pc+0x4c0 rather than skip to prepretail).  Post = MAIN_LOOP entry registers.  *)
let AES256_GCM_ENC_ALT_SETUP_GEN_SAFE = prove
 (`exists f_events.
   !e in_p out_p tag_p ivec_p key_p htable_p stackpointer bit_len end_p
     nb k pc.
    ~(k = 0) /\
    8 * (k + 1) <= nb /\
    bit_len = 128 * nb /\
    8 * (k + 1) < nb /\ nb <= 8 * (k + 2) /\
    end_p = word_add in_p (word (128 * (k + 1))) /\
    val in_p + 128 * (k + 1) < 2 EXP 63 /\
    128 * nb < 2 EXP 64 /\
    nonoverlapping (out_p, 16 * nb)
                   (word pc, LENGTH aes256_gcm_enc_alt_tmc) /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
      [(word pc, LENGTH aes256_gcm_enc_alt_tmc);
       (in_p, 16 * nb); (key_p, 240); (htable_p, 192);
       (word_add stackpointer (word 0x40), 8)] /\
    PAIRWISE nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) aes256_gcm_enc_alt_tmc /\
           read PC s = word (pc + 0x38) /\
           read X0 s = in_p /\
           read X1 s = word bit_len /\
           read X2 s = out_p /\
           read X3 s = tag_p /\
           read X16 s = ivec_p /\
           read X6 s = htable_p /\
           read X11 s = key_p /\
           read X9 s = word (bit_len DIV 8) /\
           read X10 s = word_add stackpointer (word 0x40) /\
           read events s = e)
      (\s. read PC s = word (pc + 0x4c0) /\
           read X0 s = word_add in_p (word (128 * (0 + 1))) /\
           read X2 s = word_add out_p (word (128 * (0 + 1))) /\
           read X3 s = tag_p /\
           read X9 s = word (16 * nb) /\
           read X4 s = word_add in_p (word (16 * nb)) /\
           read X16 s = ivec_p /\
           read X5 s = end_p /\
           read X6 s = htable_p /\
           read X10 s = word_add stackpointer (word 0x40) /\
           read X11 s = key_p /\
           (exists e2.
              read events s = APPEND e2 e /\
              e2 = f_events in_p out_p tag_p ivec_p key_p htable_p
                     stackpointer pc /\
              memaccess_inbounds e2
                [in_p, 16 * nb; tag_p, 16; ivec_p, 16; key_p, 240;
                 htable_p, 192; word_add stackpointer (word 0x40), 8]
                [out_p, 16 * nb; tag_p, 16; ivec_p, 16]))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * nb);
                  memory :> bytes(tag_p, 16);
                  memory :> bytes(ivec_p, 16)])`,
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; MODIFIABLE_SIMD_REGS;
              MODIFIABLE_GPRS; MODIFIABLE_UPPER_SIMD_REGS] THEN
  REWRITE_TAC[ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES; LENGTH_WB_MC] THEN
  CONCRETIZE_F_EVENTS_TAC
    `\(in_p:int64) (out_p:int64) (tag_p:int64) (ivec_p:int64)
      (key_p:int64) (htable_p:int64) (stackpointer:int64) (pc:num).
       f_ev in_p out_p tag_p ivec_p key_p htable_p stackpointer pc
       :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  SUBGOAL_THEN
   `?inblock. !j. j < nb
      ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s0 =
          inblock j`
   (CHOOSE_THEN ASSUME_TAC) THENL
   [EXISTS_TAC
      `\j. read (memory :> bytes128 (word_add in_p (word (16 * j)))) s0` THEN
    REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~(nb = 4)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `5 <= nb` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY NSTEP (1--5) THEN NSTEP 6 THEN NSTEP 7 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[
    MATCH_MP DISPATCH4_NOT_TAKEN (CONJ (ASSUME `128 * nb < 2 EXP 64`) (ASSUME `~(nb = 4)`));
    MATCH_MP DISPATCH_SMALL_NOT_TAKEN (CONJ (ASSUME `128 * nb < 2 EXP 64`) (ASSUME `5 <= nb`));
    COND_CLAUSES]) THEN
  MAP_EVERY NSTEP (8--36) THEN
  MAP_EVERY NSTEP (37--261) THEN NSTEP 262 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP SETUP_BRANCH_COND_FALSE_GEN
    (CONJ (ASSUME `8 * (k + 1) < nb`) (CONJ (ASSUME `nb <= 8 * (k + 2)`)
          (ASSUME `val (in_p:int64) + 128 * (k + 1) < 2 EXP 63`))); COND_CLAUSES]) THEN
  LDP_SETUP_TAC 263 THEN LDP_SETUP_TAC 264 THEN MAP_EVERY NSTEP (265--271) THEN
  LDP_SETUP_TAC 272 THEN LDP_SETUP_TAC 273 THEN MAP_EVERY NSTEP (274--289) THEN
  NSTEP 290 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP SETUP_BRANCH_COND_FALSE_2_GEN
    (CONJ (ASSUME `~(k = 0)`) (CONJ (ASSUME `8 * (k + 1) < nb`)
      (CONJ (ASSUME `nb <= 8 * (k + 2)`)
          (ASSUME `val (in_p:int64) + 128 * (k + 1) < 2 EXP 63`))));
    COND_CLAUSES]) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN TRY SETUP_RECON_TAC_GEN THEN
  DISCHARGE_SAFETY_PROPERTY_TAC)
;;

(* --- MAIN_LOOP_SAFE (pc+0x4c0 -> pc+0xa10, k iterations, nb>=17): the 8-block *)
(* main loop.  Lean invariant (pointer regs only); ENSURES_EVENTS_WHILE_UP2_TAC  *)
(* with pc2 = exit (pc+0xa10).  Body = the functional NSTEP_G drive with the     *)
(* ldp/stp at 295/303/304 handled by LDP_STEP4_LEAN (= LDP_STEP4_TAC minus the    *)
(* dead INBLOCKS content), + the b.gt at step 340; back-edge PC closed via        *)
(* BRIDGE_GE + IV_ADD (in_p cancels -> i+1<k), events via ENUMERATEL_ADD1.        *)
let LDP_STEP4_LEAN n =
  let sn = "s"^string_of_int n in
  ARM_VERBOSE_STEP_TAC AES256_GCM_ENC_ALT_EXEC sn THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
    `word_add (word_add b (word m)) (word nn):int64 = word_add b (word(m+nn))`]) THEN
  RULE_ASSUM_TAC NORMOFF_RULE THEN
  RULE_ASSUM_TAC SUBWORD_NORM_RULE THEN
  DISCARD_OLDSTATE_TAC sn;;

let AES256_GCM_ENC_ALT_MAIN_LOOP_SAFE = prove
 (`exists f_events.
   !e in_p out_p tag_p ivec_p key_p htable_p mod_p end_p nb k pc.
    ~(k = 0) /\
    8 * (k + 1) <= nb /\
    end_p = word_add in_p (word (128 * (k + 1))) /\
    val in_p + 128 * (k + 1) < 2 EXP 63 /\
    val in_p + 16 * nb < 2 EXP 63 /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
      [(word pc, LENGTH aes256_gcm_enc_alt_tmc);
       (in_p, 16 * nb); (key_p, 240); (htable_p, 192); (mod_p, 8)] /\
    PAIRWISE nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) aes256_gcm_enc_alt_tmc /\
           read PC s = word (pc + 0x4c0) /\
           read X0 s = word_add in_p (word (128 * (0 + 1))) /\
           read X2 s = word_add out_p (word (128 * (0 + 1))) /\
           read X3 s = tag_p /\
           read X9 s = word (16 * nb) /\
           read X4 s = word_add in_p (word (16 * nb)) /\
           read X16 s = ivec_p /\
           read X5 s = end_p /\
           read X6 s = htable_p /\
           read X10 s = mod_p /\
           read X11 s = key_p /\
           read events s = e)
      (\s. read PC s = word (pc + 0xa10) /\
           read X0 s = word_add in_p (word (128 * (k + 1))) /\
           read X2 s = word_add out_p (word (128 * (k + 1))) /\
           read X3 s = tag_p /\
           read X9 s = word (16 * nb) /\
           read X4 s = word_add in_p (word (16 * nb)) /\
           read X16 s = ivec_p /\
           read X5 s = end_p /\
           read X6 s = htable_p /\
           read X10 s = mod_p /\
           read X11 s = key_p /\
           (exists e2.
              read events s = APPEND e2 e /\
              e2 = f_events in_p out_p tag_p ivec_p key_p htable_p mod_p nb k pc /\
              memaccess_inbounds e2
                [in_p, 16 * nb; tag_p, 16; ivec_p, 16; key_p, 240;
                 htable_p, 192; mod_p, 8]
                [out_p, 16 * nb; tag_p, 16; ivec_p, 16]))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * nb);
                  memory :> bytes(tag_p, 16);
                  memory :> bytes(ivec_p, 16)])`,
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; MODIFIABLE_SIMD_REGS;
              MODIFIABLE_GPRS; MODIFIABLE_UPPER_SIMD_REGS] THEN
  REWRITE_TAC[ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES; LENGTH_WB_MC] THEN
  CONCRETIZE_F_EVENTS_TAC
    `\(in_p:int64) (out_p:int64) (tag_p:int64) (ivec_p:int64)
      (key_p:int64) (htable_p:int64) (mod_p:int64) (nb:num) (k:num) (pc:num).
       APPEND
         (f_ev_post in_p out_p tag_p ivec_p key_p htable_p mod_p nb k pc)
         (APPEND
           (ENUMERATEL k
             (\i. f_ev_loop in_p out_p tag_p ivec_p key_p htable_p mod_p nb k pc i))
           (f_ev_pre in_p out_p tag_p ivec_p key_p htable_p mod_p nb k pc))
       :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  REPEAT STRIP_TAC THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `k:num` `pc + 0x4c0` `pc + 0xa10`
    `\i s. read X0 s = word_add in_p (word (128 * (i + 1))) /\
           read X2 s = word_add out_p (word (128 * (i + 1))) /\
           read X3 s = tag_p /\
           read X9 s = word (16 * nb) /\
           read X4 s = word_add in_p (word (16 * nb)) /\
           read X16 s = ivec_p /\
           read X5 s = end_p /\
           read X6 s = htable_p /\
           read X10 s = mod_p /\
           read X11 s = key_p` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [(* init (0-step) *)
    ENSURES_INIT_TAC "s0" THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ENUMERATEL; APPEND] THEN DISCHARGE_SAFETY_PROPERTY_TAC;
    (* body *)
    ALL_TAC;
    (* exit (0-step, pc2 = post PC) *)
    ENSURES_INIT_TAC "s0" THEN STRIP_EXISTS_ASSUM_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[APPEND_NIL; APPEND] THEN DISCHARGE_SAFETY_PROPERTY_TAC] THEN
  (* ===== loop body: pc+0x4c0 -> b.gt@pc+0xa0c (340 steps incl branch) ===== *)
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN STRIP_EXISTS_ASSUM_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REWRITE_CONV[fst AES256_GCM_ENC_ALT_EXEC]
    `LENGTH aes256_gcm_enc_alt_tmc`]) THEN
  MAP_EVERY NSTEP_G (1--294) THEN
  LDP_STEP4_LEAN 295 THEN
  MAP_EVERY NSTEP_G (296--302) THEN
  LDP_STEP4_LEAN 303 THEN
  LDP_STEP4_LEAN 304 THEN
  MAP_EVERY NSTEP_G (305--340) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  (* PC branch: <b.gt cond> <=> i+1<k, via BRIDGE_GE + IV_ADD *)
  CONJ_TAC THENL
   [REWRITE_TAC[BRIDGE_GE] THEN
    SUBGOAL_THEN
      `ival(word_add in_p (word (128 * (k + 1)))) = &(val(in_p:int64) + 128 * (k + 1)) /\
       ival(word_add in_p (word (128 * (i + 1) + 128))) = &(val(in_p:int64) + (128 * (i + 1) + 128))`
      (CONJUNCTS_THEN SUBST1_TAC) THENL
     [CONJ_TAC THEN MATCH_MP_TAC IV_ADD THEN
      UNDISCH_TAC `val(in_p:int64) + 128 * (k + 1) < 2 EXP 63` THEN
      UNDISCH_TAC `(i:num) < k` THEN ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[INT_OF_NUM_LE] THEN
    GEN_REWRITE_TAC RAND_CONV [COND_RAND] THEN
    MATCH_MP_TAC (MESON[]
      `(p <=> q) ==> ((if p then (a:int64) else b) = (if q then a else b))`) THEN
    UNDISCH_TAC `(i:num) < k` THEN ARITH_TAC;
    ALL_TAC] THEN
  (* X0, X2 pointer advances *)
  CONJ_TAC THENL [ AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC; ALL_TAC ] THEN
  CONJ_TAC THENL [ AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC; ALL_TAC ] THEN
  (* events: e2 = ENUMERATEL (i+1) e_loop; unify f_ev_loop i := this iteration's trace *)
  SAFE_META_EXISTS_TAC allowed_vars_e THEN
  CONJ_TAC THENL [ EXISTS_E2_TAC allowed_vars_e; ALL_TAC ] THEN
  CONJ_TAC THENL
   [PURE_REWRITE_TAC[APPEND_NIL] THEN
    GEN_REWRITE_TAC RAND_CONV [ENUMERATEL_ADD1] THEN
    BETA_TAC THEN
    BINOP_TAC THENL [ UNIFY_F_EVENTS_TAC; REFL_TAC ];
    DISCHARGE_MEMACCESS_INBOUNDS_TAC])
;;

(* --- LOOP_TAIL_SAFE (pc+0x4c0 -> pc+0x1154): MAIN_LOOP_SAFE o                  *)
(* PREPRETAIL_TAIL_SAFE (double abstract bigstep, param k).  The loop+prepretail *)
(* +tail composite for nb>=17.                                                   *)
let AES256_GCM_ENC_ALT_LOOP_TAIL_SAFE = prove
 (`exists f_events.
   !e in_p out_p tag_p ivec_p key_p htable_p mod_p end_p nb k pc.
    ~(k = 0) /\
    8 * (k + 1) <= nb /\
    8 * (k + 1) < nb /\ nb <= 8 * (k + 2) /\
    end_p = word_add in_p (word (128 * (k + 1))) /\
    val in_p + 128 * (k + 1) < 2 EXP 63 /\
    val in_p + 16 * nb < 2 EXP 63 /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
      [(word pc, LENGTH aes256_gcm_enc_alt_tmc);
       (in_p, 16 * nb); (key_p, 240); (htable_p, 192); (mod_p, 8)] /\
    PAIRWISE nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) aes256_gcm_enc_alt_tmc /\
           read PC s = word (pc + 0x4c0) /\
           read X0 s = word_add in_p (word (128 * (0 + 1))) /\
           read X2 s = word_add out_p (word (128 * (0 + 1))) /\
           read X3 s = tag_p /\
           read X9 s = word (16 * nb) /\
           read X4 s = word_add in_p (word (16 * nb)) /\
           read X16 s = ivec_p /\
           read X5 s = end_p /\
           read X6 s = htable_p /\
           read X10 s = mod_p /\
           read X11 s = key_p /\
           read events s = e)
      (\s. read PC s = word (pc + 0x1154) /\
           (exists e2.
              read events s = APPEND e2 e /\
              e2 = f_events in_p out_p tag_p ivec_p key_p htable_p mod_p nb k pc /\
              memaccess_inbounds e2
                [in_p, 16 * nb; tag_p, 16; ivec_p, 16; key_p, 240;
                 htable_p, 192; mod_p, 8]
                [out_p, 16 * nb; tag_p, 16; ivec_p, 16]))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * nb);
                  memory :> bytes(tag_p, 16);
                  memory :> bytes(ivec_p, 16)])`,
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; MODIFIABLE_SIMD_REGS;
              MODIFIABLE_GPRS; MODIFIABLE_UPPER_SIMD_REGS] THEN
  REWRITE_TAC[ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES; LENGTH_WB_MC] THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC AES256_GCM_ENC_ALT_PREPRETAIL_TAIL_SAFE "H_PT" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC AES256_GCM_ENC_ALT_MAIN_LOOP_SAFE "H_ML" THEN
  CONCRETIZE_F_EVENTS_TAC
    `\(in_p:int64) (out_p:int64) (tag_p:int64) (ivec_p:int64)
      (key_p:int64) (htable_p:int64) (mod_p:int64) (nb:num) (k:num) (pc:num).
       APPEND
         (f_ev_pt in_p out_p tag_p ivec_p key_p htable_p mod_p nb k pc)
         (f_ev_ml in_p out_p tag_p ivec_p key_p htable_p mod_p nb k pc)
       :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
    MODIFIABLE_SIMD_REGS; MODIFIABLE_GPRS; MODIFIABLE_UPPER_SIMD_REGS]) THEN
  (* ===== BIGSTEP 1: MAIN_LOOP (pc+0x4c0 -> pc+0xa10), e_tail = [] ===== *)
  USE_THEN "H_ML" (fun th ->
    MP_TAC (REWRITE_RULE[APPEND]
      (SPECL [`e:(uarch_event)list`; `in_p:int64`; `out_p:int64`; `tag_p:int64`;
              `ivec_p:int64`; `key_p:int64`; `htable_p:int64`; `mod_p:int64`;
              `end_p:int64`; `nb:num`; `k:num`; `pc:num`;
              `[]:(uarch_event)list`] th))) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES; LENGTH_WB_MC] THEN
    REPEAT CONJ_TAC THEN
    (FIRST_ASSUM ACCEPT_TAC ORELSE ASM_ARITH_TAC ORELSE ASM_REWRITE_TAC[] ORELSE
     CONV_TAC WORD_RULE);
    ALL_TAC] THEN
  ARM_BIGSTEP_TAC AES256_GCM_ENC_ALT_EXEC "s1" THEN
  (* ===== BIGSTEP 2: PREPRETAIL_TAIL (pc+0xa10 -> pc+0x1154), param k ===== *)
  USE_THEN "H_PT" (fun th ->
    MP_TAC (GEN_REWRITE_RULE I [RIGHT_FORALL_IMP_THM]
      (SPECL [`e:(uarch_event)list`; `in_p:int64`; `out_p:int64`; `tag_p:int64`;
              `ivec_p:int64`; `key_p:int64`; `htable_p:int64`; `mod_p:int64`;
              `end_p:int64`; `nb:num`; `k:num`; `pc:num`] th))) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES; LENGTH_WB_MC] THEN
    REPEAT CONJ_TAC THEN
    (FIRST_ASSUM ACCEPT_TAC ORELSE ASM_ARITH_TAC ORELSE ASM_REWRITE_TAC[] ORELSE
     CONV_TAC WORD_RULE);
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[GSYM LEFT_EXISTS_IMP_THM] THEN
  META_EXISTS_TAC THEN
  ARM_BIGSTEP_TAC AES256_GCM_ENC_ALT_EXEC "s2" THENL [
    BINOP_TAC THENL [ UNIFY_REFL_TAC; REFL_TAC ] THEN NO_TAC;
    ALL_TAC ] THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SAFE_META_EXISTS_TAC allowed_vars_e THEN
  CONJ_TAC THENL [ EXISTS_E2_TAC allowed_vars_e; ALL_TAC ] THEN
  CONJ_TAC THENL
   [ BINOP_TAC THENL [ UNIFY_F_EVENTS_TAC; UNIFY_F_EVENTS_TAC ];
     DISCHARGE_MEMACCESS_INBOUNDS_TAC ])
;;

(* --- Whole-core safety for nb>=17: GEN_CORRECT_SAFE (pc+0x38 -> pc+0x1154,     *)
(* k>=1).  SETUP_GEN_SAFE o LOOP_TAIL_SAFE (double bigstep).  f_events takes      *)
(* nb,k.  Completes the nb>=17 core-safety leg; all 4 nb-legs now covered.        *)
let AES256_GCM_ENC_ALT_GEN_CORRECT_SAFE = prove
 (`exists f_events.
   !e in_p out_p tag_p ivec_p key_p htable_p stackpointer bit_len end_p
     nb k pc.
    ~(k = 0) /\
    8 * (k + 1) <= nb /\
    bit_len = 128 * nb /\
    8 * (k + 1) < nb /\ nb <= 8 * (k + 2) /\
    end_p = word_add in_p (word (128 * (k + 1))) /\
    val in_p + 128 * (k + 1) < 2 EXP 63 /\
    val in_p + 16 * nb < 2 EXP 63 /\
    128 * nb < 2 EXP 64 /\
    nonoverlapping (out_p, 16 * nb)
                   (word pc, LENGTH aes256_gcm_enc_alt_tmc) /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
      [(word pc, LENGTH aes256_gcm_enc_alt_tmc);
       (in_p, 16 * nb); (key_p, 240); (htable_p, 192);
       (word_add stackpointer (word 0x40), 8)] /\
    PAIRWISE nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) aes256_gcm_enc_alt_tmc /\
           read PC s = word (pc + 0x38) /\
           read X0 s = in_p /\
           read X1 s = word bit_len /\
           read X2 s = out_p /\
           read X3 s = tag_p /\
           read X16 s = ivec_p /\
           read X6 s = htable_p /\
           read X11 s = key_p /\
           read X9 s = word (bit_len DIV 8) /\
           read X10 s = word_add stackpointer (word 0x40) /\
           read events s = e)
      (\s. read PC s = word (pc + 0x1154) /\
           (exists e2.
              read events s = APPEND e2 e /\
              e2 = f_events nb k in_p out_p tag_p ivec_p key_p htable_p
                     stackpointer pc /\
              memaccess_inbounds e2
                [in_p, 16 * nb; tag_p, 16; ivec_p, 16; key_p, 240;
                 htable_p, 192; word_add stackpointer (word 0x40), 8]
                [out_p, 16 * nb; tag_p, 16; ivec_p, 16]))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * nb);
                  memory :> bytes(tag_p, 16);
                  memory :> bytes(ivec_p, 16)])`,
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; MODIFIABLE_SIMD_REGS;
              MODIFIABLE_GPRS; MODIFIABLE_UPPER_SIMD_REGS] THEN
  REWRITE_TAC[ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES; LENGTH_WB_MC] THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC AES256_GCM_ENC_ALT_LOOP_TAIL_SAFE "H_LT" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC AES256_GCM_ENC_ALT_SETUP_GEN_SAFE "H_SG" THEN
  CONCRETIZE_F_EVENTS_TAC
    `\(nb:num) (k:num) (in_p:int64) (out_p:int64) (tag_p:int64) (ivec_p:int64)
      (key_p:int64) (htable_p:int64) (stackpointer:int64) (pc:num).
       APPEND
         (f_ev_lt nb k in_p out_p tag_p ivec_p key_p htable_p stackpointer pc)
         (f_ev_sg nb k in_p out_p tag_p ivec_p key_p htable_p stackpointer pc)
       :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
    MODIFIABLE_SIMD_REGS; MODIFIABLE_GPRS; MODIFIABLE_UPPER_SIMD_REGS]) THEN
  (* ===== BIGSTEP 1: SETUP_GEN (pc+0x38 -> pc+0x4c0), e_tail = [] ===== *)
  USE_THEN "H_SG" (fun th ->
    MP_TAC (REWRITE_RULE[APPEND]
      (SPECL [`e:(uarch_event)list`; `in_p:int64`; `out_p:int64`; `tag_p:int64`;
              `ivec_p:int64`; `key_p:int64`; `htable_p:int64`; `stackpointer:int64`;
              `bit_len:num`; `end_p:int64`; `nb:num`; `k:num`;
              `pc:num`; `[]:(uarch_event)list`] th))) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES; LENGTH_WB_MC] THEN
    REPEAT CONJ_TAC THEN
    (FIRST_ASSUM ACCEPT_TAC ORELSE ASM_ARITH_TAC ORELSE ASM_REWRITE_TAC[] ORELSE
     CONV_TAC WORD_RULE);
    ALL_TAC] THEN
  ARM_BIGSTEP_TAC AES256_GCM_ENC_ALT_EXEC "s1" THEN
  (* ===== BIGSTEP 2: LOOP_TAIL (pc+0x4c0 -> pc+0x1154), param k ===== *)
  USE_THEN "H_LT" (fun th ->
    MP_TAC (GEN_REWRITE_RULE I [RIGHT_FORALL_IMP_THM]
      (SPECL [`e:(uarch_event)list`; `in_p:int64`; `out_p:int64`; `tag_p:int64`;
              `ivec_p:int64`; `key_p:int64`; `htable_p:int64`;
              `word_add stackpointer (word 0x40):int64`; `end_p:int64`;
              `nb:num`; `k:num`; `pc:num`] th))) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES; LENGTH_WB_MC] THEN
    REPEAT CONJ_TAC THEN
    (FIRST_ASSUM ACCEPT_TAC ORELSE ASM_ARITH_TAC ORELSE ASM_REWRITE_TAC[] ORELSE
     CONV_TAC WORD_RULE);
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[GSYM LEFT_EXISTS_IMP_THM] THEN
  META_EXISTS_TAC THEN
  ARM_BIGSTEP_TAC AES256_GCM_ENC_ALT_EXEC "s2" THENL [
    BINOP_TAC THENL [ UNIFY_REFL_TAC; REFL_TAC ] THEN NO_TAC;
    ALL_TAC ] THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SAFE_META_EXISTS_TAC allowed_vars_e THEN
  CONJ_TAC THENL [ EXISTS_E2_TAC allowed_vars_e; ALL_TAC ] THEN
  CONJ_TAC THENL
   [ BINOP_TAC THENL [ UNIFY_F_EVENTS_TAC; UNIFY_F_EVENTS_TAC ];
     DISCHARGE_MEMACCESS_INBOUNDS_TAC ])
;;

(* --- Whole-core safety (all nb): dispatch over the 4 nb-legs (FAST1-4,      *)
(* SETUP0_TAIL, FIXED_CORRECT_G1, GEN_CORRECT), mirroring                      *)
(* AES256_GCM_ENC_ALT_CORRECT's nb-tree.  Entry pc+0x38, exit pc+0x1154.     *)
let AES256_GCM_ENC_ALT_SAFE = prove
 (`exists f_events.
   !e in_p out_p tag_p ivec_p key_p htable_p stackpointer bit_len
     nb pc.
    1 <= nb /\
    bit_len = 128 * nb /\
    val in_p + 16 * nb < 2 EXP 63 /\
    128 * nb < 2 EXP 64 /\
    nonoverlapping (out_p, 16 * nb)
                   (word pc, LENGTH aes256_gcm_enc_alt_tmc) /\
    ALLPAIRS nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
      [(word pc, LENGTH aes256_gcm_enc_alt_tmc);
       (in_p, 16 * nb); (key_p, 240); (htable_p, 192);
       (word_add stackpointer (word 0x40), 8)] /\
    PAIRWISE nonoverlapping
      [(out_p, 16 * nb); (tag_p, 16); (ivec_p, 16)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) aes256_gcm_enc_alt_tmc /\
           read PC s = word (pc + 0x38) /\
           read X0 s = in_p /\
           read X1 s = word bit_len /\
           read X2 s = out_p /\
           read X3 s = tag_p /\
           read X16 s = ivec_p /\
           read X6 s = htable_p /\
           read X11 s = key_p /\
           read X9 s = word (bit_len DIV 8) /\
           read X10 s = word_add stackpointer (word 0x40) /\
           read events s = e)
      (\s. read PC s = word (pc + 0x1154) /\
           (exists e2.
              read events s = APPEND e2 e /\
              e2 = f_events nb in_p out_p tag_p ivec_p key_p htable_p
                     stackpointer pc /\
              memaccess_inbounds e2
                [in_p, 16 * nb; tag_p, 16; ivec_p, 16; key_p, 240;
                 htable_p, 192; word_add stackpointer (word 0x40), 8]
                [out_p, 16 * nb; tag_p, 16; ivec_p, 16]))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes(out_p, 16 * nb);
                  memory :> bytes(tag_p, 16);
                  memory :> bytes(ivec_p, 16)])`,
  X_CHOOSE_TAC `w1:int64->int64->int64->int64->int64->int64->int64->num->(uarch_event)list` AES256_GCM_ENC_ALT_FAST1_SAFE THEN
  X_CHOOSE_TAC `w2:int64->int64->int64->int64->int64->int64->int64->num->(uarch_event)list` AES256_GCM_ENC_ALT_FAST2_SAFE THEN
  X_CHOOSE_TAC `w3:int64->int64->int64->int64->int64->int64->int64->num->(uarch_event)list` AES256_GCM_ENC_ALT_FAST3_SAFE THEN
  X_CHOOSE_TAC `w4:int64->int64->int64->int64->int64->int64->int64->num->(uarch_event)list` AES256_GCM_ENC_ALT_FAST4_SAFE THEN
  X_CHOOSE_TAC `wst:num->int64->int64->int64->int64->int64->int64->int64->num->(uarch_event)list` AES256_GCM_ENC_ALT_SETUP0_TAIL_SAFE THEN
  X_CHOOSE_TAC `wg1:num->int64->int64->int64->int64->int64->int64->int64->num->(uarch_event)list` AES256_GCM_ENC_ALT_FIXED_CORRECT_G1_SAFE THEN
  X_CHOOSE_TAC `wgen:num->num->int64->int64->int64->int64->int64->int64->int64->num->(uarch_event)list` AES256_GCM_ENC_ALT_GEN_CORRECT_SAFE THEN
  EXISTS_TAC
   `\(nb:num) (in_p:int64) (out_p:int64) (tag_p:int64) (ivec_p:int64)
     (key_p:int64) (htable_p:int64) (stackpointer:int64) (pc:num).
      if nb = 1 then w1 in_p out_p tag_p ivec_p key_p htable_p stackpointer pc
      else if nb = 2 then w2 in_p out_p tag_p ivec_p key_p htable_p stackpointer pc
      else if nb = 3 then w3 in_p out_p tag_p ivec_p key_p htable_p stackpointer pc
      else if nb = 4 then w4 in_p out_p tag_p ivec_p key_p htable_p stackpointer pc
      else if nb <= 8 then wst nb in_p out_p tag_p ivec_p key_p htable_p stackpointer pc
      else if nb <= 16 then wg1 nb in_p out_p tag_p ivec_p key_p htable_p stackpointer pc
      else wgen nb ((nb - 1) DIV 8 - 1) in_p out_p tag_p ivec_p key_p htable_p stackpointer pc
      :(uarch_event)list` THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `in_p:int64`; `out_p:int64`; `tag_p:int64`;
    `ivec_p:int64`; `key_p:int64`; `htable_p:int64`; `stackpointer:int64`;
    `bit_len:num`; `nb:num`; `pc:num`] THEN
  STRIP_TAC THEN BETA_TAC THEN
  SUBGOAL_THEN `nb <= 8 \/ (9 <= nb /\ nb <= 16) \/ 17 <= nb` MP_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THENL
   [ASM_CASES_TAC `nb = 1` THENL
     [REWRITE_TAC[EQT_INTRO(ASSUME `nb = 1`); COND_CLAUSES] THEN
     FIRST_X_ASSUM MATCH_MP_TAC THEN REPEAT CONJ_TAC THEN
     (FIRST_ASSUM ACCEPT_TAC ORELSE ASM_ARITH_TAC ORELSE (REWRITE_TAC[ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES; LENGTH_WB_MC] THEN ASM_REWRITE_TAC[]) ORELSE CONV_TAC WORD_RULE);
      ALL_TAC] THEN
    ASM_CASES_TAC `nb = 2` THENL
     [REWRITE_TAC[EQF_INTRO(ASSUME `~(nb = 1)`); EQT_INTRO(ASSUME `nb = 2`); COND_CLAUSES] THEN
     FIRST_X_ASSUM MATCH_MP_TAC THEN REPEAT CONJ_TAC THEN
     (FIRST_ASSUM ACCEPT_TAC ORELSE ASM_ARITH_TAC ORELSE (REWRITE_TAC[ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES; LENGTH_WB_MC] THEN ASM_REWRITE_TAC[]) ORELSE CONV_TAC WORD_RULE);
      ALL_TAC] THEN
    ASM_CASES_TAC `nb = 3` THENL
     [REWRITE_TAC[EQF_INTRO(ASSUME `~(nb = 1)`); EQF_INTRO(ASSUME `~(nb = 2)`); EQT_INTRO(ASSUME `nb = 3`); COND_CLAUSES] THEN
     FIRST_X_ASSUM MATCH_MP_TAC THEN REPEAT CONJ_TAC THEN
     (FIRST_ASSUM ACCEPT_TAC ORELSE ASM_ARITH_TAC ORELSE (REWRITE_TAC[ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES; LENGTH_WB_MC] THEN ASM_REWRITE_TAC[]) ORELSE CONV_TAC WORD_RULE);
      ALL_TAC] THEN
    ASM_CASES_TAC `nb = 4` THENL
     [REWRITE_TAC[EQF_INTRO(ASSUME `~(nb = 1)`); EQF_INTRO(ASSUME `~(nb = 2)`); EQF_INTRO(ASSUME `~(nb = 3)`); EQT_INTRO(ASSUME `nb = 4`); COND_CLAUSES] THEN
     FIRST_X_ASSUM MATCH_MP_TAC THEN REPEAT CONJ_TAC THEN
     (FIRST_ASSUM ACCEPT_TAC ORELSE ASM_ARITH_TAC ORELSE (REWRITE_TAC[ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES; LENGTH_WB_MC] THEN ASM_REWRITE_TAC[]) ORELSE CONV_TAC WORD_RULE);
      ALL_TAC] THEN
    SUBGOAL_THEN `~(nb = 1) /\ ~(nb = 2) /\ ~(nb = 3) /\ ~(nb = 4)` STRIP_ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[EQF_INTRO(ASSUME `~(nb = 1)`); EQF_INTRO(ASSUME `~(nb = 2)`); EQF_INTRO(ASSUME `~(nb = 3)`); EQF_INTRO(ASSUME `~(nb = 4)`); EQT_INTRO(ASSUME `nb <= 8`); COND_CLAUSES] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN REPEAT CONJ_TAC THEN
    (FIRST_ASSUM ACCEPT_TAC ORELSE ASM_ARITH_TAC ORELSE (REWRITE_TAC[ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES; LENGTH_WB_MC] THEN ASM_REWRITE_TAC[]) ORELSE CONV_TAC WORD_RULE);
    SUBGOAL_THEN `~(nb = 1) /\ ~(nb = 2) /\ ~(nb = 3) /\ ~(nb = 4) /\ ~(nb <= 8)` STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[EQF_INTRO(ASSUME `~(nb = 1)`); EQF_INTRO(ASSUME `~(nb = 2)`); EQF_INTRO(ASSUME `~(nb = 3)`); EQF_INTRO(ASSUME `~(nb = 4)`); EQF_INTRO(ASSUME `~(nb <= 8)`); EQT_INTRO(ASSUME `nb <= 16`); COND_CLAUSES] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    EXISTS_TAC `word_add in_p (word (128 * (0 + 1))):int64` THEN EXISTS_TAC `0` THEN
    REPEAT CONJ_TAC THEN
    (FIRST_ASSUM ACCEPT_TAC ORELSE ASM_ARITH_TAC ORELSE (REWRITE_TAC[ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES; LENGTH_WB_MC] THEN ASM_REWRITE_TAC[]) ORELSE CONV_TAC WORD_RULE);
    SUBGOAL_THEN `~(nb = 1) /\ ~(nb = 2) /\ ~(nb = 3) /\ ~(nb = 4) /\ ~(nb <= 8) /\ ~(nb <= 16)` STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[EQF_INTRO(ASSUME `~(nb = 1)`); EQF_INTRO(ASSUME `~(nb = 2)`); EQF_INTRO(ASSUME `~(nb = 3)`); EQF_INTRO(ASSUME `~(nb = 4)`); EQF_INTRO(ASSUME `~(nb <= 8)`); EQF_INTRO(ASSUME `~(nb <= 16)`); COND_CLAUSES] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    EXISTS_TAC `word_add in_p (word (128 * (((nb - 1) DIV 8 - 1) + 1))):int64` THEN
    MP_TAC(SPECL [`nb - 1`; `8`] DIVISION) THEN REWRITE_TAC[ARITH_EQ] THEN
    ABBREV_TAC `q = (nb - 1) DIV 8` THEN ABBREV_TAC `r = (nb - 1) MOD 8` THEN
    STRIP_TAC THEN REPEAT CONJ_TAC THEN
    (FIRST_ASSUM ACCEPT_TAC ORELSE ASM_ARITH_TAC ORELSE (REWRITE_TAC[ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES; LENGTH_WB_MC] THEN ASM_REWRITE_TAC[]) ORELSE CONV_TAC WORD_RULE)])
;;

(* The two exported safety statements below are the terms mk_safety_spec       *)
(* generates from the correctness theorems and the C signature, pinned with     *)
(* ASSERT_CONCL_TAC so the load fails unless the written statement is exactly   *)
(* the generated one.  The bounds size in/out from len_bits/8, then tag 16,     *)
(* ivec 16, key 240, htable 24*8 = 192 and the 80-byte frame; apart from the    *)
(* loaded code they constrain no memory contents.  ~keep_maychanges keeps the   *)
(* correctness theorem's MAYCHANGE frame.                                       *)
let enc_safety_full_spec_tmc,enc_safety_public_vars_tmc = mk_safety_spec
    ~keep_maychanges:true
    (assoc "aes256_gcm_enc_alt" subroutine_signatures)
    AES256_GCM_ENC_ALT_NOIBT_SUBROUTINE_CORRECT
    AES256_GCM_ENC_ALT_EXEC;;

let enc_safety_full_spec,enc_safety_public_vars = mk_safety_spec
    ~keep_maychanges:true
    (assoc "aes256_gcm_enc_alt" subroutine_signatures)
    AES256_GCM_ENC_ALT_SUBROUTINE_CORRECT
    AES256_GCM_ENC_ALT_EXEC;;

(* --- NOIBT subroutine safety (REQUIRED): 3-path wrapper mirroring            *)
(* AES256_GCM_ENC_ALT_NOIBT_SUBROUTINE_CORRECT.  f_events dispatches on the   *)
(* public length guards (misaligned / zero / main); main = prologue + CORE_SAFE *)
(* callee bigstep (in-frame SP = word_sub sp 0x50) + epilogue.                  *)
(* The statement is the mk_safety_spec-generated enc_safety_full_spec_tmc.      *)
let AES256_GCM_ENC_ALT_NOIBT_SUBROUTINE_SAFE = prove
 (`exists f_events.
    forall e in_p out_p tag_p ivec_p key_p htable_p len_bits pc stackpointer returnaddress.
        aligned 16 stackpointer /\
        val in_p + 16 * gcm_wb_blocks len_bits < 2 EXP 63 /\
        ALLPAIRS nonoverlapping
        [out_p,16 * gcm_wb_blocks len_bits; tag_p,16; ivec_p,16;
         word_sub stackpointer (word 80),80]
        [word pc,LENGTH aes256_gcm_enc_alt_tmc;
         in_p,16 * gcm_wb_blocks len_bits; key_p,240; htable_p,192] /\
        PAIRWISE nonoverlapping
        [out_p,16 * gcm_wb_blocks len_bits; tag_p,16; ivec_p,16;
         word_sub stackpointer (word 80),80]
        ==> ensures arm
            (\s.
                 aligned_bytes_loaded s (word pc) aes256_gcm_enc_alt_tmc /\
                 read PC s = word pc /\
                 read SP s = stackpointer /\
                 read X30 s = returnaddress /\
                 C_ARGUMENTS
                 [in_p; len_bits; out_p; tag_p; ivec_p; key_p; htable_p]
                 s /\
                 read events s = e)
            (\s.
                 read PC s = returnaddress /\
                 (exists e2.
                      read events s = APPEND e2 e /\
                      e2 =
                      f_events in_p key_p htable_p out_p tag_p ivec_p
                      len_bits
                      pc
                      (word_sub stackpointer (word 80))
                      returnaddress /\
                      memaccess_inbounds e2
                      [in_p,val len_bits DIV 8 * 1; tag_p,16; ivec_p,16;
                       key_p,240; htable_p,192; out_p,val len_bits DIV 8 * 1;
                       word_sub stackpointer (word 80),80]
                      [out_p,val len_bits DIV 8 * 1; tag_p,16; ivec_p,16;
                       word_sub stackpointer (word 80),80]))
            (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE
             [memory :> bytes (out_p,16 * gcm_wb_blocks len_bits);
              memory :> bytes (tag_p,16); memory :> bytes (ivec_p,16);
              memory :> bytes (word_sub stackpointer (word 80),80)])`,
  ASSERT_CONCL_TAC enc_safety_full_spec_tmc THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC AES256_GCM_ENC_ALT_SAFE "H_CORE" THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; LENGTH_WB_MC; ALLPAIRS;
              PAIRWISE; ALL; NONOVERLAPPING_CLAUSES; C_ARGUMENTS; KEY15_SPLIT] THEN
  CONCRETIZE_F_EVENTS_TAC
    `\(in_p:int64) (key_p:int64) (htable_p:int64) (out_p:int64) (tag_p:int64)
      (ivec_p:int64) (len_bits:int64) (pc:num) (sp:int64) (retaddr:int64).
      if val len_bits MOD 128 = 0 then
        (if val len_bits = 0 then
           f_ev_zero len_bits in_p out_p tag_p ivec_p key_p htable_p pc sp retaddr
         else
           APPEND
             (f_ev_epi in_p out_p tag_p ivec_p key_p htable_p pc sp retaddr)
             (APPEND
               (f_ev_core (gcm_wb_blocks len_bits) in_p out_p tag_p ivec_p key_p htable_p sp pc)
               (f_ev_pro in_p out_p tag_p ivec_p key_p htable_p pc sp retaddr)))
       else
         f_ev_mis len_bits in_p out_p tag_p ivec_p key_p htable_p pc sp retaddr
      :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `nb = gcm_wb_blocks len_bits` THEN
  ASM_CASES_TAC `val(len_bits:int64) MOD 128 = 0` THENL
   [ALL_TAC;
    (* ===== PATH A: misaligned length ===== *)
    SUBGOAL_THEN `nb = 0` SUBST_ALL_TAC THENL
     [EXPAND_TAC "nb" THEN REWRITE_TAC[gcm_wb_blocks] THEN ASM_REWRITE_TAC[COND_CLAUSES]; ALL_TAC] THEN
    SUBGOAL_THEN `~(val(len_bits:int64) = 0)` ASSUME_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC `~(val(len_bits:int64) MOD 128 = 0)` THEN
      ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
    SUBGOAL_THEN `~(len_bits:int64 = word 0)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[GSYM VAL_EQ_0]; ALL_TAC] THEN
    SUBGOAL_THEN `~(word_and (len_bits:int64) (word 0x7f) = word 0)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[WB_MASK7_EQ_MOD]; ALL_TAC] THEN
    SUBGOAL_THEN `~(val(word_and (len_bits:int64) (word 0x7f)) = 0)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[VAL_EQ_0]; ALL_TAC] THEN
    REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES] THEN
    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC AES256_GCM_ENC_ALT_EXEC [1] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `~(val(len_bits:int64) = 0)`;
                               ASSUME `~(len_bits:int64 = word 0)`; COND_CLAUSES]) THEN
    ARM_STEPS_TAC AES256_GCM_ENC_ALT_EXEC [2] THEN
    ARM_STEPS_TAC AES256_GCM_ENC_ALT_EXEC [3] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[
      ASSUME `~(word_and (len_bits:int64) (word 0x7f) = word 0)`;
      ASSUME `~(val(word_and (len_bits:int64) (word 0x7f)) = 0)`; COND_CLAUSES]) THEN
    ARM_STEPS_TAC AES256_GCM_ENC_ALT_EXEC [4;5] THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[COND_CLAUSES] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC] THEN
  ASM_CASES_TAC `val(len_bits:int64) = 0` THENL
   [(* ===== PATH B: zero length ===== *)
    SUBGOAL_THEN `nb = 0` SUBST_ALL_TAC THENL
     [EXPAND_TAC "nb" THEN REWRITE_TAC[gcm_wb_blocks] THEN
      ASM_REWRITE_TAC[COND_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
    SUBGOAL_THEN `len_bits:int64 = word 0` SUBST_ALL_TAC THENL
     [ASM_REWRITE_TAC[GSYM VAL_EQ_0]; ALL_TAC] THEN
    REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES] THEN
    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC AES256_GCM_ENC_ALT_EXEC [1;2;3] THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[VAL_WORD_0; COND_CLAUSES] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;
    ALL_TAC] THEN
  (* ===== PATH C: main (nonzero whole blocks) ===== *)
  SUBGOAL_THEN `1 <= nb` ASSUME_TAC THENL
   [EXPAND_TAC "nb" THEN REWRITE_TAC[gcm_wb_blocks] THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`val(len_bits:int64)`; `128`] (CONJUNCT2 DIVISION_SIMP)) THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `val(len_bits:int64) = 128 * nb` ASSUME_TAC THENL
   [EXPAND_TAC "nb" THEN ASM_SIMP_TAC[GCM_WB_BLOCKS_VALID]; ALL_TAC] THEN
  SUBGOAL_THEN `128 * nb < 2 EXP 64` ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN MP_TAC(ISPEC `len_bits:int64` VAL_BOUND) THEN
    REWRITE_TAC[DIMINDEX_64] THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `val(word(128 * nb):int64) = 128 * nb` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `gcm_wb_blocks(word(128 * nb):int64) = nb` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[gcm_wb_blocks] THEN
    SIMP_TAC[DIV_MULT; MOD_MULT; ARITH_EQ] THEN REWRITE_TAC[COND_CLAUSES]; ALL_TAC] THEN
  SUBGOAL_THEN `len_bits:int64 = word (128 * nb)` SUBST_ALL_TAC THENL
   [FIRST_X_ASSUM(fun th -> if concl th = `val(len_bits:int64) = 128 * nb`
      then MP_TAC th else failwith "") THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[WORD_VAL]; ALL_TAC] THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  MAP_EVERY (fun c -> ENSURES_PRESERVED_DREG_TAC ("init_"^fst(dest_const c)) c)
    [`D8`;`D9`;`D10`;`D11`;`D12`;`D13`;`D14`;`D15`] THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(CONV_RULE(TRY_CONV(
    EXPAND_CASES_CONV THENC ONCE_DEPTH_CONV NUM_MULT_CONV THENC REWRITE_CONV[WORD_ADD_0]))) THEN
  ARM_STEPS_TAC AES256_GCM_ENC_ALT_EXEC [1] THEN
  SUBGOAL_THEN `~(128 * nb = 0)` ASSUME_TAC THENL
   [UNDISCH_TAC `1 <= nb` THEN ARITH_TAC; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP WB_GUARD1_NONZERO_GEN
    (CONJ (ASSUME `1 <= nb`) (ASSUME `128 * nb < 2 EXP 64`));
    ASSUME `~(128 * nb = 0)`; COND_CLAUSES]) THEN
  ARM_STEPS_TAC AES256_GCM_ENC_ALT_EXEC [2] THEN
  ARM_STEPS_TAC AES256_GCM_ENC_ALT_EXEC [3] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP WB_GUARD2_MASK_GEN
    (CONJ (ASSUME `1 <= nb`) (ASSUME `128 * nb < 2 EXP 64`));
    VAL_WORD_0; COND_CLAUSES]) THEN
  ARM_STEPS_TAC AES256_GCM_ENC_ALT_EXEC (4--14) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP WB_X9_NORM (ASSUME `128 * nb < 2 EXP 64`)]) THEN
  USE_THEN "H_CORE" (fun th0 ->
    let th = REWRITE_RULE[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
               MODIFIABLE_SIMD_REGS; MODIFIABLE_GPRS; MODIFIABLE_UPPER_SIMD_REGS] th0 in
    MP_TAC (GEN_REWRITE_RULE I [RIGHT_FORALL_IMP_THM]
      (SPECL [`e:(uarch_event)list`; `in_p:int64`; `out_p:int64`; `tag_p:int64`;
              `ivec_p:int64`; `key_p:int64`; `htable_p:int64`;
              `word_sub stackpointer (word 80):int64`; `128 * nb`;
              `nb:num`; `pc:num`] th))) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES; LENGTH_WB_MC] THEN
    REPEAT CONJ_TAC THEN
    (NONOVERLAPPING_TAC ORELSE ASM_ARITH_TAC ORELSE CONV_TAC WORD_RULE ORELSE
     ASM_REWRITE_TAC[WORD_REVERSEFIELDS_REVERSEFIELDS]); ALL_TAC] THEN
  ONCE_REWRITE_TAC[GSYM LEFT_EXISTS_IMP_THM] THEN
  META_EXISTS_TAC THEN
  ARM_BIGSTEP_TAC AES256_GCM_ENC_ALT_EXEC "s15" THENL
   [ CONV_TAC(LAND_CONV CONS_TO_APPEND_CONV) THEN AP_THM_TAC THEN AP_TERM_TAC THEN
     UNIFY_REFL_TAC; ALL_TAC ] THEN
  ARM_STEPS_TAC AES256_GCM_ENC_ALT_EXEC (16--22) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[COND_CLAUSES] THEN
  ABBREV_TAC `spoff:int64 = word_sub stackpointer (word 80)` THEN
  CONJ_TAC THENL [
    SAFE_META_EXISTS_TAC allowed_vars_e THEN
    CONJ_TAC THENL [ EXISTS_E2_TAC allowed_vars_e; ALL_TAC ] THEN
    CONJ_TAC THENL [
      REWRITE_TAC[APPEND_NIL] THEN
      BINOP_TAC THENL [
        UNIFY_F_EVENTS_TAC;
        BINOP_TAC THENL [
          ASM_REWRITE_TAC[] THEN UNIFY_F_EVENTS_TAC;
          UNIFY_F_EVENTS_TAC ] ];
      DISCHARGE_MEMACCESS_INBOUNDS_TAC ];
    EXPAND_TAC "spoff" THEN
    SIMP_TAC[WORD_ZX_ZX; DIMINDEX_64; DIMINDEX_128; LE_REFL; ARITH] THEN
    REPEAT CONJ_TAC THEN CONV_TAC WORD_RULE ]
);;

(* --- IBT subroutine safety (REQUIRED): derived from the NOIBT one by
   ARM_ADD_IBT_RULE, mirroring AES256_GCM_ENC_ALT_SUBROUTINE_CORRECT. --- *)
let AES256_GCM_ENC_ALT_SUBROUTINE_SAFE = prove
 (`exists f_events.
    forall e in_p out_p tag_p ivec_p key_p htable_p len_bits pc stackpointer returnaddress.
        aligned 16 stackpointer /\
        val in_p + 16 * gcm_wb_blocks len_bits < 2 EXP 63 /\
        ALLPAIRS nonoverlapping
        [out_p,16 * gcm_wb_blocks len_bits; tag_p,16; ivec_p,16;
         word_sub stackpointer (word 80),80]
        [word pc,LENGTH aes256_gcm_enc_alt_mc;
         in_p,16 * gcm_wb_blocks len_bits; key_p,240; htable_p,192] /\
        PAIRWISE nonoverlapping
        [out_p,16 * gcm_wb_blocks len_bits; tag_p,16; ivec_p,16;
         word_sub stackpointer (word 80),80]
        ==> ensures arm
            (\s.
                 aligned_bytes_loaded s (word pc) aes256_gcm_enc_alt_mc /\
                 read PC s = word pc /\
                 read SP s = stackpointer /\
                 read X30 s = returnaddress /\
                 C_ARGUMENTS
                 [in_p; len_bits; out_p; tag_p; ivec_p; key_p; htable_p]
                 s /\
                 read events s = e)
            (\s.
                 read PC s = returnaddress /\
                 (exists e2.
                      read events s = APPEND e2 e /\
                      e2 =
                      f_events in_p key_p htable_p out_p tag_p ivec_p
                      len_bits
                      pc
                      (word_sub stackpointer (word 80))
                      returnaddress /\
                      memaccess_inbounds e2
                      [in_p,val len_bits DIV 8 * 1; tag_p,16; ivec_p,16;
                       key_p,240; htable_p,192; out_p,val len_bits DIV 8 * 1;
                       word_sub stackpointer (word 80),80]
                      [out_p,val len_bits DIV 8 * 1; tag_p,16; ivec_p,16;
                       word_sub stackpointer (word 80),80]))
            (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE
             [memory :> bytes (out_p,16 * gcm_wb_blocks len_bits);
              memory :> bytes (tag_p,16); memory :> bytes (ivec_p,16);
              memory :> bytes (word_sub stackpointer (word 80),80)])`,
  ASSERT_CONCL_TAC enc_safety_full_spec THEN
  MATCH_ACCEPT_TAC(ARM_ADD_IBT_RULE
                     aes256_gcm_enc_alt_mc aes256_gcm_enc_alt_tmc
                     AES256_GCM_ENC_ALT_NOIBT_SUBROUTINE_SAFE));;

(* ------------------------------------------------------------------------- *)
(* No-access early-return guarantee (review round 3, item 3).                 *)
(*                                                                            *)
(* The exported CORRECT and SAFE theorems above still carry key/table/tag/    *)
(* counter, stack and separation premises even on a rejected call.  This      *)
(* extra pair exposes the guarantee that actually holds on the rejected path  *)
(* -- len_bits = 0, or not a whole number of 128-bit blocks: the routine      *)
(* returns 0 and performs no memory event (no load, store or stack access),   *)
(* assuming nothing about the data, key, table, counter, stack pointer or     *)
(* separation, and no 2^63 bound.  The guard decides from len_bits (in X1)    *)
(* alone -- `cbz x1` on zero, `tst x1,#0x7f; b.ne` on a non-multiple of 128   *)
(* -- and falls into the shared mov w0,#0 / ret, so only PC, X0, the flags    *)
(* and the (branch-only) event trace change; no memory region is touched.     *)
(* `memaccess_inbounds e2 [] []` over the newly appended events e2 states      *)
(* they contain no EventLoad/EventStore; the EventJump entries a branch emits  *)
(* are permitted.  (The direct `read events s = e` cannot be used: a taken     *)
(* branch appends an EventJump, so the trace grows even with no memory         *)
(* access; this follows the _SAFE specs' event idiom.)  These theorems are    *)
(* deliberately NOT named *_SUBROUTINE_CORRECT/_SAFE, so count-proofs.sh and  *)
(* arm/proofs/specifications.txt are unchanged.                               *)
(* ------------------------------------------------------------------------- *)

(* Supply the APPEND-prefix witness for the newly appended events from the    *)
(* simulated final trace (`read events s = CONS .. (CONS .. e)` reassociated  *)
(* as `APPEND e2 e`), so `memaccess_inbounds e2 [] []` can then be discharged  *)
(* for the jump-only trace.                                                   *)
let EVENTS_NOMEM_TAC:tactic =
  W(fun (asl,w) ->
     let _,bod = dest_exists w in
     let eqc = fst(dest_conj bod) in
     let tr = lhs eqc and appe = rhs eqc in
     let e_tm = rand appe in
     let rec pref tm = if tm = e_tm then []
                       else let c,t = dest_comb tm in (rand c)::pref t in
     let lst = pref tr in
     EXISTS_TAC (mk_list(lst,type_of(hd lst))));;

let AES256_GCM_ENC_ALT_NOIBT_REJECT_NOACCESS = prove
 (`!in_p out_p tag_p ivec_p key_p htable_p len_bits pc returnaddress e.
    val len_bits = 0 \/ ~(val len_bits MOD 128 = 0)
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) aes256_gcm_enc_alt_tmc /\
           read PC s = word pc /\
           read X30 s = returnaddress /\
           C_ARGUMENTS
            [in_p; len_bits; out_p; tag_p; ivec_p; key_p; htable_p] s /\
           read events s = e)
      (\s. read PC s = returnaddress /\
           C_RETURN s = word 0 /\
           (?e2. read events s = APPEND e2 e /\ memaccess_inbounds e2 [] []))
      (MAYCHANGE [PC; X0] ,, MAYCHANGE [events] ,, MAYCHANGE SOME_FLAGS)`,
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN
  REPEAT GEN_TAC THEN
  DISCH_THEN(DISJ_CASES_THEN ASSUME_TAC) THENL
   [(* Zero length: `cbz x1` is TAKEN straight to L256_enc_ret. *)
    SUBGOAL_THEN `len_bits:int64 = word 0` SUBST_ALL_TAC THENL
     [ASM_REWRITE_TAC[GSYM VAL_EQ_0]; ALL_TAC] THEN
    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC AES256_GCM_ENC_ALT_EXEC [1;2;3] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    EVENTS_NOMEM_TAC THEN
    REWRITE_TAC[APPEND; memaccess_inbounds; ALL; EX; FST; SND];
    (* Not a whole number of blocks: `cbz x1` falls through, `tst x1,#0x7f`    *)
    (* leaves ZF clear so `b.ne` is TAKEN, and L256_enc_ret returns 0.         *)
    SUBGOAL_THEN `~(val(len_bits:int64) = 0)` ASSUME_TAC THENL
     [DISCH_TAC THEN
      UNDISCH_TAC `~(val(len_bits:int64) MOD 128 = 0)` THEN
      ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
    SUBGOAL_THEN `~(len_bits:int64 = word 0)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[GSYM VAL_EQ_0]; ALL_TAC] THEN
    SUBGOAL_THEN `~(word_and (len_bits:int64) (word 0x7f) = word 0)`
    ASSUME_TAC THENL [ASM_REWRITE_TAC[WB_MASK7_EQ_MOD]; ALL_TAC] THEN
    SUBGOAL_THEN `~(val(word_and (len_bits:int64) (word 0x7f)) = 0)`
    ASSUME_TAC THENL [ASM_REWRITE_TAC[VAL_EQ_0]; ALL_TAC] THEN
    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC AES256_GCM_ENC_ALT_EXEC [1] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `~(val(len_bits:int64) = 0)`;
                               ASSUME `~(len_bits:int64 = word 0)`;
                               COND_CLAUSES]) THEN
    ARM_STEPS_TAC AES256_GCM_ENC_ALT_EXEC [2] THEN
    ARM_STEPS_TAC AES256_GCM_ENC_ALT_EXEC [3] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[
      ASSUME `~(word_and (len_bits:int64) (word 0x7f) = word 0)`;
      ASSUME `~(val(word_and (len_bits:int64) (word 0x7f)) = 0)`;
      COND_CLAUSES]) THEN
    ARM_STEPS_TAC AES256_GCM_ENC_ALT_EXEC [4;5] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    EVENTS_NOMEM_TAC THEN
    REWRITE_TAC[APPEND; memaccess_inbounds; ALL; EX; FST; SND]]);;

(* The default build keeps the `bti c` landing pad; reconstitute the padded   *)
(* statement for aes256_gcm_enc_alt_mc with ARM_ADD_IBT_RULE, as the exported *)
(* SAFE theorem does.  No `~extra` is needed: the precondition has no opaque   *)
(* state predicate.                                                           *)
let AES256_GCM_ENC_ALT_REJECT_NOACCESS = prove
 (`!in_p out_p tag_p ivec_p key_p htable_p len_bits pc returnaddress e.
    val len_bits = 0 \/ ~(val len_bits MOD 128 = 0)
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) aes256_gcm_enc_alt_mc /\
           read PC s = word pc /\
           read X30 s = returnaddress /\
           C_ARGUMENTS
            [in_p; len_bits; out_p; tag_p; ivec_p; key_p; htable_p] s /\
           read events s = e)
      (\s. read PC s = returnaddress /\
           C_RETURN s = word 0 /\
           (?e2. read events s = APPEND e2 e /\ memaccess_inbounds e2 [] []))
      (MAYCHANGE [PC; X0] ,, MAYCHANGE [events] ,, MAYCHANGE SOME_FLAGS)`,
  MATCH_ACCEPT_TAC(ARM_ADD_IBT_RULE
                     aes256_gcm_enc_alt_mc aes256_gcm_enc_alt_tmc
                     AES256_GCM_ENC_ALT_NOIBT_REJECT_NOACCESS));;

(* Load-time evidence the new theorems are the intended no-access guarantee    *)
(* (they are not manifest exports, so the .correct run never prints them).     *)
let () =
  let has_const th name =
    can (find_term (fun t -> is_const t && fst(dest_const t) = name)) (concl th) in
  let ok th codename =
    hyp th = [] && has_const th "memaccess_inbounds" && has_const th codename in
  if not (ok AES256_GCM_ENC_ALT_NOIBT_REJECT_NOACCESS "aes256_gcm_enc_alt_tmc")
  then failwith "AES256_GCM_ENC_ALT_NOIBT_REJECT_NOACCESS: unexpected shape";
  if not (ok AES256_GCM_ENC_ALT_REJECT_NOACCESS "aes256_gcm_enc_alt_mc")
  then failwith "AES256_GCM_ENC_ALT_REJECT_NOACCESS: unexpected shape";;
