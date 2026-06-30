(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* AES-256-GCM encrypt — the COMPLETE single binary (all length paths).      *)
(*                                                                           *)
(* This mirrors the upstream AES-XTS proof (arm/proofs/aes_xts_encrypt.ml):  *)
(* ONE machine-code blob (aes256_gcm_mc) handling every input length via its *)
(* internal length-dispatch cascade, with per-length-band correctness        *)
(* lemmas proved against that single binary and dispatched at the top.       *)
(*                                                                           *)
(* This file proves the 1-block case, taking the                             *)
(* .L256_enc_blocks_less_than_1 branch, exactly as the XTS LT_2BLOCK band    *)
(* lemma proves its short case against the one XTS binary.                   *)
(* ========================================================================= *)

needs "arm/proofs/utils/gcm_aesgcm_nblock_helpers.ml";;
needs "arm/proofs/utils/aes_encrypt_spec.ml";;

(* OCaml helper: int -> num (the tail-cascade threshold lemmas below use it  *)
(* to build numerals).  Note the core HOL `num_of_int` is a term constant,   *)
(* not this OCaml function.                                                  *)
let num_of_int n = Num.num_of_string (string_of_int n);;

(* The AES-256 keystream is computed by the upstream math-level              *)
(* aes256_encrypt; AES256_ENCRYPT_UNFOLD (arm/proofs/utils/                  *)
(* gcm_aesgcm_helpers.ml) rewrites it into the aese/aesmc instruction chain  *)
(* the simulator produces.                                                   *)

(* print_literal_from_elf "arm/aes-gcm/aes256_gcm.o";; *)
let aes256_gcm_mc = define_assert_from_elf
  "aes256_gcm_mc"
  "arm/aes-gcm/aes256_gcm.o"
[
  0xd503201f;       (* arm_NOP *)
  0xb4008f61;       (* arm_CBZ X1 (word 4588) *)
  0x6dbb27e8;       (* arm_STP D8 D9 SP (Preimmediate_Offset (iword (-- &80))) *)
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
  0x6e20081e;       (* arm_REV32_VEC Q30 Q0 8 128 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0x6e200bc1;       (* arm_REV32_VEC Q1 Q30 8 128 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0x6e200bc2;       (* arm_REV32_VEC Q2 Q30 8 128 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0x6e200bc3;       (* arm_REV32_VEC Q3 Q30 8 128 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0x6e200bc4;       (* arm_REV32_VEC Q4 Q30 8 128 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0x6e200bc5;       (* arm_REV32_VEC Q5 Q30 8 128 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0xad406d7a;       (* arm_LDP Q26 Q27 X11 (Immediate_Offset (iword (&0))) *)
  0x6e200bc6;       (* arm_REV32_VEC Q6 Q30 8 128 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0x6e200bc7;       (* arm_REV32_VEC Q7 Q30 8 128 *)
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
  0x6e200bc0;       (* arm_REV32_VEC Q0 Q30 8 128 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0xce017129;       (* arm_EOR3 Q9 Q9 Q1 Q28 *)
  0xce03716b;       (* arm_EOR3 Q11 Q11 Q3 Q28 *)
  0x6e200bc1;       (* arm_REV32_VEC Q1 Q30 8 128 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0xacc1340c;       (* arm_LDP Q12 Q13 X0 (Postimmediate_Offset (iword (&32))) *)
  0xacc13c0e;       (* arm_LDP Q14 Q15 X0 (Postimmediate_Offset (iword (&32))) *)
  0xce02714a;       (* arm_EOR3 Q10 Q10 Q2 Q28 *)
  0xeb05001f;       (* arm_CMP X0 X5 *)
  0x6e200bc2;       (* arm_REV32_VEC Q2 Q30 8 128 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0xac812448;       (* arm_STP Q8 Q9 X2 (Postimmediate_Offset (iword (&32))) *)
  0xac812c4a;       (* arm_STP Q10 Q11 X2 (Postimmediate_Offset (iword (&32))) *)
  0x6e200bc3;       (* arm_REV32_VEC Q3 Q30 8 128 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0xce04718c;       (* arm_EOR3 Q12 Q12 Q4 Q28 *)
  0xce0771ef;       (* arm_EOR3 Q15 Q15 Q7 Q28 *)
  0xce0671ce;       (* arm_EOR3 Q14 Q14 Q6 Q28 *)
  0xce0571ad;       (* arm_EOR3 Q13 Q13 Q5 Q28 *)
  0xac81344c;       (* arm_STP Q12 Q13 X2 (Postimmediate_Offset (iword (&32))) *)
  0x6e200bc4;       (* arm_REV32_VEC Q4 Q30 8 128 *)
  0xac813c4e;       (* arm_STP Q14 Q15 X2 (Postimmediate_Offset (iword (&32))) *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0x54002aaa;       (* arm_BGE (word 1364) *)
  0xad406d7a;       (* arm_LDP Q26 Q27 X11 (Immediate_Offset (iword (&0))) *)
  0x6e200bc5;       (* arm_REV32_VEC Q5 Q30 8 128 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0x3dc01cd5;       (* arm_LDR Q21 X6 (Immediate_Offset (word 112)) *)
  0x3dc028d8;       (* arm_LDR Q24 X6 (Immediate_Offset (word 160)) *)
  0x4e20096b;       (* arm_REV64_VEC Q11 Q11 8 *)
  0x3dc018d4;       (* arm_LDR Q20 X6 (Immediate_Offset (word 96)) *)
  0x3dc020d6;       (* arm_LDR Q22 X6 (Immediate_Offset (word 128)) *)
  0x4e200929;       (* arm_REV64_VEC Q9 Q9 8 *)
  0x6e200bc6;       (* arm_REV32_VEC Q6 Q30 8 128 *)
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
  0x6e200bc7;       (* arm_REV32_VEC Q7 Q30 8 128 *)
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
  0x4ef9e111;       (* arm_PMULL2 Q17 Q8 Q25 64 *)
  0x0ef9e113;       (* arm_PMULL Q19 Q8 Q25 64 *)
  0x4ef7e130;       (* arm_PMULL2 Q16 Q9 Q23 64 *)
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
  0x0ef7e137;       (* arm_PMULL Q23 Q9 Q23 64 *)
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
  0x4ef4e169;       (* arm_PMULL2 Q9 Q11 Q20 64 *)
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
  0x4ef6e15d;       (* arm_PMULL2 Q29 Q10 Q22 64 *)
  0x4e2009ad;       (* arm_REV64_VEC Q13 Q13 8 *)
  0x0ef4e174;       (* arm_PMULL Q20 Q11 Q20 64 *)
  0x6e371e73;       (* arm_EOR_VEC Q19 Q19 Q23 128 *)
  0x3dc00cd7;       (* arm_LDR Q23 X6 (Immediate_Offset (word 48)) *)
  0x3dc014d9;       (* arm_LDR Q25 X6 (Immediate_Offset (word 80)) *)
  0x4ecc29b0;       (* arm_TRN1 Q16 Q13 Q12 64 128 *)
  0xce1d2631;       (* arm_EOR3 Q17 Q17 Q29 Q9 *)
  0x0ef6e156;       (* arm_PMULL Q22 Q10 Q22 64 *)
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
  0x4ef5e15d;       (* arm_PMULL2 Q29 Q10 Q21 64 *)
  0x4ef8e112;       (* arm_PMULL2 Q18 Q8 Q24 64 *)
  0x4e284b80;       (* arm_AESE Q0 Q28 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x0ef8e118;       (* arm_PMULL Q24 Q8 Q24 64 *)
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
  0x0ef5e155;       (* arm_PMULL Q21 Q10 Q21 64 *)
  0x4e284b45;       (* arm_AESE Q5 Q26 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0xce165273;       (* arm_EOR3 Q19 Q19 Q22 Q20 *)
  0x4e284b43;       (* arm_AESE Q3 Q26 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0xad44697c;       (* arm_LDP Q28 Q26 X11 (Immediate_Offset (iword (&128))) *)
  0x4ef9e188;       (* arm_PMULL2 Q8 Q12 Q25 64 *)
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
  0x0ef9e199;       (* arm_PMULL Q25 Q12 Q25 64 *)
  0x4ecc69ac;       (* arm_TRN2 Q12 Q13 Q12 64 128 *)
  0x4e284b64;       (* arm_AESE Q4 Q27 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b61;       (* arm_AESE Q1 Q27 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4ef7e1aa;       (* arm_PMULL2 Q10 Q13 Q23 64 *)
  0x4e284b87;       (* arm_AESE Q7 Q28 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b80;       (* arm_AESE Q0 Q28 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x0ef7e1b7;       (* arm_PMULL Q23 Q13 Q23 64 *)
  0x4ece29ed;       (* arm_TRN1 Q13 Q15 Q14 64 128 *)
  0x6e301d8c;       (* arm_EOR_VEC Q12 Q12 Q16 128 *)
  0x4e284b83;       (* arm_AESE Q3 Q28 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b81;       (* arm_AESE Q1 Q28 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4ef8e190;       (* arm_PMULL2 Q16 Q12 Q24 64 *)
  0x0ef8e198;       (* arm_PMULL Q24 Q12 Q24 64 *)
  0x4e284b82;       (* arm_AESE Q2 Q28 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b85;       (* arm_AESE Q5 Q28 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4ef6e1cb;       (* arm_PMULL2 Q11 Q14 Q22 64 *)
  0x0ef6e1d6;       (* arm_PMULL Q22 Q14 Q22 64 *)
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
  0x4ef4e1ec;       (* arm_PMULL2 Q12 Q15 Q20 64 *)
  0xce195e73;       (* arm_EOR3 Q19 Q19 Q25 Q23 *)
  0x0ef4e1f4;       (* arm_PMULL Q20 Q15 Q20 64 *)
  0xfd400150;       (* arm_LDR D16 X10 (Immediate_Offset (word 0)) *)
  0x4ef5e1cd;       (* arm_PMULL2 Q13 Q14 Q21 64 *)
  0x0ef5e1d5;       (* arm_PMULL Q21 Q14 Q21 64 *)
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
  0x6e200bd4;       (* arm_REV32_VEC Q20 Q30 8 128 *)
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
  0x0ef0e23d;       (* arm_PMULL Q29 Q17 Q16 64 *)
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
  0x6e200bd6;       (* arm_REV32_VEC Q22 Q30 8 128 *)
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
  0x6e200bd7;       (* arm_REV32_VEC Q23 Q30 8 128 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0x4e284b65;       (* arm_AESE Q5 Q27 *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b63;       (* arm_AESE Q3 Q27 *)
  0xeb05001f;       (* arm_CMP X0 X5 *)
  0xce02714a;       (* arm_EOR3 Q10 Q10 Q2 Q28 *)
  0x6e200bd9;       (* arm_REV32_VEC Q25 Q30 8 128 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0x4e284b60;       (* arm_AESE Q0 Q27 *)
  0x4e284b66;       (* arm_AESE Q6 Q27 *)
  0xce0571ad;       (* arm_EOR3 Q13 Q13 Q5 Q28 *)
  0x6e124255;       (* arm_EXT Q21 Q18 Q18 64 *)
  0x0ef0e251;       (* arm_PMULL Q17 Q18 Q16 64 *)
  0x4e284b61;       (* arm_AESE Q1 Q27 *)
  0xce04718c;       (* arm_EOR3 Q12 Q12 Q4 Q28 *)
  0x6e200bc4;       (* arm_REV32_VEC Q4 Q30 8 128 *)
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
  0x6e200bc5;       (* arm_REV32_VEC Q5 Q30 8 128 *)
  0xad406d7a;       (* arm_LDP Q26 Q27 X11 (Immediate_Offset (iword (&0))) *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0x4e20094a;       (* arm_REV64_VEC Q10 Q10 8 *)
  0x6e200bc6;       (* arm_REV32_VEC Q6 Q30 8 128 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0x4e2009ad;       (* arm_REV64_VEC Q13 Q13 8 *)
  0x3dc01cd5;       (* arm_LDR Q21 X6 (Immediate_Offset (word 112)) *)
  0x3dc028d8;       (* arm_LDR Q24 X6 (Immediate_Offset (word 160)) *)
  0x6e200bc7;       (* arm_REV32_VEC Q7 Q30 8 128 *)
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
  0x4ef9e111;       (* arm_PMULL2 Q17 Q8 Q25 64 *)
  0x4e2009ce;       (* arm_REV64_VEC Q14 Q14 8 *)
  0x4e284b44;       (* arm_AESE Q4 Q26 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4ef7e130;       (* arm_PMULL2 Q16 Q9 Q23 64 *)
  0x4e284b47;       (* arm_AESE Q7 Q26 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x0ef9e113;       (* arm_PMULL Q19 Q8 Q25 64 *)
  0x4ec86928;       (* arm_TRN2 Q8 Q9 Q8 64 128 *)
  0x4ef6e15d;       (* arm_PMULL2 Q29 Q10 Q22 64 *)
  0x4e284b46;       (* arm_AESE Q6 Q26 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b42;       (* arm_AESE Q2 Q26 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b43;       (* arm_AESE Q3 Q26 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x6e301e31;       (* arm_EOR_VEC Q17 Q17 Q16 128 *)
  0x0ef7e137;       (* arm_PMULL Q23 Q9 Q23 64 *)
  0x4ef4e169;       (* arm_PMULL2 Q9 Q11 Q20 64 *)
  0x4e284b41;       (* arm_AESE Q1 Q26 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x6e321d08;       (* arm_EOR_VEC Q8 Q8 Q18 128 *)
  0x4e284b45;       (* arm_AESE Q5 Q26 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x0ef6e156;       (* arm_PMULL Q22 Q10 Q22 64 *)
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
  0x4ef8e112;       (* arm_PMULL2 Q18 Q8 Q24 64 *)
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
  0x0ef4e174;       (* arm_PMULL Q20 Q11 Q20 64 *)
  0x0ef8e118;       (* arm_PMULL Q24 Q8 Q24 64 *)
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
  0x4ef5e15d;       (* arm_PMULL2 Q29 Q10 Q21 64 *)
  0x0ef5e155;       (* arm_PMULL Q21 Q10 Q21 64 *)
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
  0x4ef9e188;       (* arm_PMULL2 Q8 Q12 Q25 64 *)
  0x0ef9e199;       (* arm_PMULL Q25 Q12 Q25 64 *)
  0x3dc000d4;       (* arm_LDR Q20 X6 (Immediate_Offset (word 0)) *)
  0x3dc008d6;       (* arm_LDR Q22 X6 (Immediate_Offset (word 32)) *)
  0xad44697c;       (* arm_LDP Q28 Q26 X11 (Immediate_Offset (iword (&128))) *)
  0x4e284b61;       (* arm_AESE Q1 Q27 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b64;       (* arm_AESE Q4 Q27 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4ef7e1aa;       (* arm_PMULL2 Q10 Q13 Q23 64 *)
  0x4ecc69ac;       (* arm_TRN2 Q12 Q13 Q12 64 128 *)
  0x4e284b65;       (* arm_AESE Q5 Q27 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b66;       (* arm_AESE Q6 Q27 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x0ef7e1b7;       (* arm_PMULL Q23 Q13 Q23 64 *)
  0x4e284b67;       (* arm_AESE Q7 Q27 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b63;       (* arm_AESE Q3 Q27 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x6e301d8c;       (* arm_EOR_VEC Q12 Q12 Q16 128 *)
  0x4ef6e1cb;       (* arm_PMULL2 Q11 Q14 Q22 64 *)
  0x0ef6e1d6;       (* arm_PMULL Q22 Q14 Q22 64 *)
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
  0x4ef8e190;       (* arm_PMULL2 Q16 Q12 Q24 64 *)
  0x0ef8e198;       (* arm_PMULL Q24 Q12 Q24 64 *)
  0x4e284b81;       (* arm_AESE Q1 Q28 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4ef4e1ec;       (* arm_PMULL2 Q12 Q15 Q20 64 *)
  0x4ef5e1cd;       (* arm_PMULL2 Q13 Q14 Q21 64 *)
  0x0ef5e1d5;       (* arm_PMULL Q21 Q14 Q21 64 *)
  0x0ef4e1f4;       (* arm_PMULL Q20 Q15 Q20 64 *)
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
  0x0ef0e23d;       (* arm_PMULL Q29 Q17 Q16 64 *)
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
  0x0ef0e251;       (* arm_PMULL Q17 Q18 Q16 64 *)
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
  0x4ef9e111;       (* arm_PMULL2 Q17 Q8 Q25 64 *)
  0x6e08451b;       (* arm_INS Q27 Q8 0 64 64 128 *)
  0x6e084712;       (* arm_INS Q18 Q24 0 64 64 128 *)
  0x0f00e410;       (* arm_MOVI D16 (word 0) *)
  0x2e281f7b;       (* arm_EOR_VEC Q27 Q27 Q8 64 *)
  0xce017529;       (* arm_EOR3 Q9 Q9 Q1 Q29 *)
  0x0ef2e372;       (* arm_PMULL Q18 Q27 Q18 64 *)
  0x0ef9e113;       (* arm_PMULL Q19 Q8 Q25 64 *)
  0x4c9f7049;       (* arm_STR Q9 X2 (Postimmediate_Offset (word 16)) *)
  0x4e200928;       (* arm_REV64_VEC Q8 Q9 8 *)
  0x6e301d08;       (* arm_EOR_VEC Q8 Q8 Q16 128 *)
  0x0ef7e11a;       (* arm_PMULL Q26 Q8 Q23 64 *)
  0x6e08451b;       (* arm_INS Q27 Q8 0 64 64 128 *)
  0x4ef7e11c;       (* arm_PMULL2 Q28 Q8 Q23 64 *)
  0x3cc10409;       (* arm_LDR Q9 X0 (Postimmediate_Offset (word 16)) *)
  0x6e3a1e73;       (* arm_EOR_VEC Q19 Q19 Q26 128 *)
  0x2e281f7b;       (* arm_EOR_VEC Q27 Q27 Q8 64 *)
  0x0ef8e37b;       (* arm_PMULL Q27 Q27 Q24 64 *)
  0xce027529;       (* arm_EOR3 Q9 Q9 Q2 Q29 *)
  0x0f00e410;       (* arm_MOVI D16 (word 0) *)
  0x6e3b1e52;       (* arm_EOR_VEC Q18 Q18 Q27 128 *)
  0x6e3c1e31;       (* arm_EOR_VEC Q17 Q17 Q28 128 *)
  0x4c9f7049;       (* arm_STR Q9 X2 (Postimmediate_Offset (word 16)) *)
  0x4e200928;       (* arm_REV64_VEC Q8 Q9 8 *)
  0x6e301d08;       (* arm_EOR_VEC Q8 Q8 Q16 128 *)
  0x6e08451b;       (* arm_INS Q27 Q8 0 64 64 128 *)
  0x4ef6e11c;       (* arm_PMULL2 Q28 Q8 Q22 64 *)
  0x6e3c1e31;       (* arm_EOR_VEC Q17 Q17 Q28 128 *)
  0x2e281f7b;       (* arm_EOR_VEC Q27 Q27 Q8 64 *)
  0x6e18077b;       (* arm_INS Q27 Q27 64 0 64 64 *)
  0x3cc10409;       (* arm_LDR Q9 X0 (Postimmediate_Offset (word 16)) *)
  0x0ef6e11a;       (* arm_PMULL Q26 Q8 Q22 64 *)
  0x4ef5e37b;       (* arm_PMULL2 Q27 Q27 Q21 64 *)
  0x0f00e410;       (* arm_MOVI D16 (word 0) *)
  0x6e3a1e73;       (* arm_EOR_VEC Q19 Q19 Q26 128 *)
  0x6e3b1e52;       (* arm_EOR_VEC Q18 Q18 Q27 128 *)
  0xce037529;       (* arm_EOR3 Q9 Q9 Q3 Q29 *)
  0x4c9f7049;       (* arm_STR Q9 X2 (Postimmediate_Offset (word 16)) *)
  0x4e200928;       (* arm_REV64_VEC Q8 Q9 8 *)
  0x3cc10409;       (* arm_LDR Q9 X0 (Postimmediate_Offset (word 16)) *)
  0x6e301d08;       (* arm_EOR_VEC Q8 Q8 Q16 128 *)
  0x6e08451b;       (* arm_INS Q27 Q8 0 64 64 128 *)
  0x4ef4e11c;       (* arm_PMULL2 Q28 Q8 Q20 64 *)
  0xce047529;       (* arm_EOR3 Q9 Q9 Q4 Q29 *)
  0x0ef4e11a;       (* arm_PMULL Q26 Q8 Q20 64 *)
  0x2e281f7b;       (* arm_EOR_VEC Q27 Q27 Q8 64 *)
  0x6e3a1e73;       (* arm_EOR_VEC Q19 Q19 Q26 128 *)
  0x0ef5e37b;       (* arm_PMULL Q27 Q27 Q21 64 *)
  0x0f00e410;       (* arm_MOVI D16 (word 0) *)
  0x6e3b1e52;       (* arm_EOR_VEC Q18 Q18 Q27 128 *)
  0x6e3c1e31;       (* arm_EOR_VEC Q17 Q17 Q28 128 *)
  0x4c9f7049;       (* arm_STR Q9 X2 (Postimmediate_Offset (word 16)) *)
  0x3dc014d9;       (* arm_LDR Q25 X6 (Immediate_Offset (word 80)) *)
  0x4e200928;       (* arm_REV64_VEC Q8 Q9 8 *)
  0x6e301d08;       (* arm_EOR_VEC Q8 Q8 Q16 128 *)
  0x6e08451b;       (* arm_INS Q27 Q8 0 64 64 128 *)
  0x4ef9e11c;       (* arm_PMULL2 Q28 Q8 Q25 64 *)
  0x6e3c1e31;       (* arm_EOR_VEC Q17 Q17 Q28 128 *)
  0x2e281f7b;       (* arm_EOR_VEC Q27 Q27 Q8 64 *)
  0x3dc010d8;       (* arm_LDR Q24 X6 (Immediate_Offset (word 64)) *)
  0x6e18077b;       (* arm_INS Q27 Q27 64 0 64 64 *)
  0x3cc10409;       (* arm_LDR Q9 X0 (Postimmediate_Offset (word 16)) *)
  0x4ef8e37b;       (* arm_PMULL2 Q27 Q27 Q24 64 *)
  0x0ef9e11a;       (* arm_PMULL Q26 Q8 Q25 64 *)
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
  0x4ef7e11c;       (* arm_PMULL2 Q28 Q8 Q23 64 *)
  0xce067529;       (* arm_EOR3 Q9 Q9 Q6 Q29 *)
  0x2e281f7b;       (* arm_EOR_VEC Q27 Q27 Q8 64 *)
  0x6e3c1e31;       (* arm_EOR_VEC Q17 Q17 Q28 128 *)
  0x0ef8e37b;       (* arm_PMULL Q27 Q27 Q24 64 *)
  0x0ef7e11a;       (* arm_PMULL Q26 Q8 Q23 64 *)
  0x6e3b1e52;       (* arm_EOR_VEC Q18 Q18 Q27 128 *)
  0x6e3a1e73;       (* arm_EOR_VEC Q19 Q19 Q26 128 *)
  0x4c9f7049;       (* arm_STR Q9 X2 (Postimmediate_Offset (word 16)) *)
  0x3dc008d6;       (* arm_LDR Q22 X6 (Immediate_Offset (word 32)) *)
  0x4e200928;       (* arm_REV64_VEC Q8 Q9 8 *)
  0x3cc10409;       (* arm_LDR Q9 X0 (Postimmediate_Offset (word 16)) *)
  0x6e301d08;       (* arm_EOR_VEC Q8 Q8 Q16 128 *)
  0x0f00e410;       (* arm_MOVI D16 (word 0) *)
  0x6e08451b;       (* arm_INS Q27 Q8 0 64 64 128 *)
  0x4ef6e11c;       (* arm_PMULL2 Q28 Q8 Q22 64 *)
  0xce077529;       (* arm_EOR3 Q9 Q9 Q7 Q29 *)
  0x6e3c1e31;       (* arm_EOR_VEC Q17 Q17 Q28 128 *)
  0x0ef6e11a;       (* arm_PMULL Q26 Q8 Q22 64 *)
  0x2e281f7b;       (* arm_EOR_VEC Q27 Q27 Q8 64 *)
  0x3dc004d5;       (* arm_LDR Q21 X6 (Immediate_Offset (word 16)) *)
  0x6e3a1e73;       (* arm_EOR_VEC Q19 Q19 Q26 128 *)
  0x6e18077b;       (* arm_INS Q27 Q27 64 0 64 64 *)
  0x4ef5e37b;       (* arm_PMULL2 Q27 Q27 Q21 64 *)
  0x6e3b1e52;       (* arm_EOR_VEC Q18 Q18 Q27 128 *)
  0x92401821;       (* arm_AND X1 X1 (rvalue (word 127)) *)
  0xd1020021;       (* arm_SUB X1 X1 (rvalue (word 128)) *)
  0xcb0103e1;       (* arm_NEG X1 X1 *)
  0xaa3f03e7;       (* arm_MVN X7 XZR *)
  0x92401821;       (* arm_AND X1 X1 (rvalue (word 127)) *)
  0x9ac124e7;       (* arm_LSRV X7 X7 X1 *)
  0xf101003f;       (* arm_CMP X1 (rvalue (word 64)) *)
  0xaa3f03e8;       (* arm_MVN X8 XZR *)
  0x9a9fb0ee;       (* arm_CSEL X14 X7 XZR Condition_LT *)
  0x9a87b10d;       (* arm_CSEL X13 X8 X7 Condition_LT *)
  0x4e081da0;       (* arm_INS_GEN Q0 X13 0 64 *)
  0x3dc000d4;       (* arm_LDR Q20 X6 (Immediate_Offset (word 0)) *)
  0x4c40705a;       (* arm_LDR Q26 X2 No_Offset *)
  0x4e181dc0;       (* arm_INS_GEN Q0 X14 64 64 *)
  0x4e201d29;       (* arm_AND_VEC Q9 Q9 Q0 128 *)
  0x4e200928;       (* arm_REV64_VEC Q8 Q9 8 *)
  0x6e200bde;       (* arm_REV32_VEC Q30 Q30 8 128 *)
  0x6ee01f49;       (* arm_BIF Q9 Q26 Q0 128 *)
  0x3d80021e;       (* arm_STR Q30 X16 (Immediate_Offset (word 0)) *)
  0x6e301d08;       (* arm_EOR_VEC Q8 Q8 Q16 128 *)
  0x4c007049;       (* arm_STR Q9 X2 No_Offset *)
  0x6e084510;       (* arm_INS Q16 Q8 0 64 64 128 *)
  0x4ef4e11c;       (* arm_PMULL2 Q28 Q8 Q20 64 *)
  0x0ef4e11a;       (* arm_PMULL Q26 Q8 Q20 64 *)
  0x6e3c1e31;       (* arm_EOR_VEC Q17 Q17 Q28 128 *)
  0x6e3a1e73;       (* arm_EOR_VEC Q19 Q19 Q26 128 *)
  0x2e281e10;       (* arm_EOR_VEC Q16 Q16 Q8 64 *)
  0x0ef5e210;       (* arm_PMULL Q16 Q16 Q21 64 *)
  0x6e301e52;       (* arm_EOR_VEC Q18 Q18 Q16 128 *)
  0xfd400150;       (* arm_LDR D16 X10 (Immediate_Offset (word 0)) *)
  0x6e114235;       (* arm_EXT Q21 Q17 Q17 64 *)
  0xce114e52;       (* arm_EOR3 Q18 Q18 Q17 Q19 *)
  0x0ef0e23d;       (* arm_PMULL Q29 Q17 Q16 64 *)
  0xce1d5652;       (* arm_EOR3 Q18 Q18 Q29 Q21 *)
  0x0ef0e251;       (* arm_PMULL Q17 Q18 Q16 64 *)
  0x6e124255;       (* arm_EXT Q21 Q18 Q18 64 *)
  0xce115673;       (* arm_EOR3 Q19 Q19 Q17 Q21 *)
  0x6e134273;       (* arm_EXT Q19 Q19 Q19 64 *)
  0x4e200a73;       (* arm_REV64_VEC Q19 Q19 8 *)
  0x4c007073;       (* arm_STR Q19 X3 No_Offset *)
  0xaa0903e0;       (* arm_MOV X0 X9 *)
  0x6d412fea;       (* arm_LDP D10 D11 SP (Immediate_Offset (iword (&16))) *)
  0x6d4237ec;       (* arm_LDP D12 D13 SP (Immediate_Offset (iword (&32))) *)
  0x6d433fee;       (* arm_LDP D14 D15 SP (Immediate_Offset (iword (&48))) *)
  0x6cc527e8;       (* arm_LDP D8 D9 SP (Postimmediate_Offset (iword (&80))) *)
  0xd65f03c0;       (* arm_RET X30 *)
  0x52800000;       (* arm_MOV W0 (rvalue (word 0)) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let AES256_GCM_EXEC = ARM_MK_EXEC_RULE aes256_gcm_mc;;

(* ========================================================================= *)
(* Shared simulation combinators for the length-band branch lemmas.          *)
(*                                                                           *)
(* In the spirit of the AES-XTS proof's named sub-tactics (AESENC_TAC,       *)
(* XTSENC_TAC, ...), these factor out the repeated "step + simplify" loops   *)
(* and length-bound discharges so each branch lemma reads declaratively.     *)
(* (Unlike XTS, GCM cannot share a tail sub-triple across bands: the band    *)
(* seam carries a half-finished Karatsuba accumulator, not a closed spec     *)
(* predicate, so each band re-simulates.)                                    *)
(* ========================================================================= *)

(* The length precondition `1 <= byte_len /\ byte_len <= 16`, reassembled    *)
(* from the two split assumptions for use with MATCH_MP.                     *)
let GCM_BOUNDS = CONJ (ASSUME `1 <= byte_len`) (ASSUME `byte_len <= 16`);;

(* Simulate steps a..b, simplifying the encryption state after each step.    *)
let GCM_RUN a b : tactic =
  MAP_EVERY (fun n -> ARM_STEPS_TAC AES256_GCM_EXEC [n] THEN GCM_ENC_SIMPLIFY_TAC) (a--b);;

(* Same as GCM_RUN but runs an extra tactic (e.g. a branch-cascade resolver) *)
(* after each step.                                                          *)
let GCM_RUN_THEN (extra:tactic) a b : tactic =
  MAP_EVERY (fun n ->
    ARM_STEPS_TAC AES256_GCM_EXEC [n] THEN GCM_ENC_SIMPLIFY_TAC THEN extra) (a--b);;

(* Discharge a length lemma `1 <= byte_len /\ byte_len <= 16 ==> P` into the *)
(* assumptions (used to collapse the cbz / in-loop guard conditionals).      *)
let GCM_BND lemma : tactic = RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP lemma GCM_BOUNDS]);;

(* Discharge an upper-bound-only lemma `byte_len <= 16 ==> P`.                *)
let GCM_BND16 lemma : tactic =
  RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP lemma (ASSUME `byte_len <= 16`)]);;

(* Entry boilerplate: unfold the triple, strip, init, run the nop + cbz x1   *)
(* (steps 1-2), and discharge the cbz guard with the given per-band lemma.   *)
let GCM_INIT_TAC cbz_lemma : tactic =
  REWRITE_TAC[C_ARGUMENTS; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              SOME_FLAGS; NONOVERLAPPING_CLAUSES; fst AES256_GCM_EXEC] THEN
  REPEAT STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC AES256_GCM_EXEC (1--2) THEN GCM_BND cbz_lemma;;

(* The shared prologue (steps 3-19): stack/frame setup, with the stack-ptr   *)
(* and constant-offset folding.  Identical in every length band.             *)
let GCM_PROLOGUE_TAC : tactic =
  ARM_STEPS_TAC AES256_GCM_EXEC (3--19) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[STACK_PTR_CANCEL; WORD_ADD_ASSOC_CONSTS]) THEN
  RULE_ASSUM_TAC(CONV_RULE(TRY_CONV(DEPTH_CONV NUM_ADD_CONV))) THEN
  GCM_ENC_SIMPLIFY_TAC;;

(* The in-loop guard: add x4 (264), collapse X5 to in_ptr with the given     *)
(* lemma so cmp x0,x5 (265) compares equal, then b.ge (266) into the tail.   *)
let GCM_INLOOP_GUARD_TAC x5_lemma : tactic =
  ARM_STEPS_TAC AES256_GCM_EXEC [264] THEN GCM_BND x5_lemma THEN
  ARM_STEPS_TAC AES256_GCM_EXEC [265] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[INT_SUB_REFL]) THEN
  ARM_STEPS_TAC AES256_GCM_EXEC [266];;

(* ========================================================================= *)
(* The 1-block case, taking the .L256_enc_blocks_less_than_1 branch.         *)
(*                                                                           *)
(* Mirrors the AES-XTS LT_kBLOCK band lemmas: a length-restricted (1 <=      *)
(* byte_len <= 16) correctness statement proved against the SINGLE full      *)
(* binary aes256_gcm_mc.  The 8-lane prologue runs in full; the in-loop      *)
(* guard (cmp x0,x5; b.ge) is taken into the tail; the tail length cascade   *)
(* (cmp x5,#0x70..#0x10) all falls through; the b .L256_enc_blocks_less_     *)
(* than_1 lands on the shared masked-store + GHASH + Barrett-reduce tail,    *)
(* which is byte-identical to the standalone one-block routine — so its      *)
(* GHASH/mask closers (GCM_1BLOCK_CT1_STEP_TAC, the GCM_1B_GHASH_CLOSE       *)
(* closer, and the ONE_BLOCK lemmas) apply verbatim.                         *)
(* ========================================================================= *)

(* All the GHASH / mask / cascade closers reused by the 1-, 2- and 3-block   *)
(* branch proofs below come from this shared file (pure algebra, no machine  *)
(* code), so we do not re-prove the per-N standalone correctness theorems.   *)
needs "arm/proofs/utils/gcm_one_block_closers.ml";;
needs "arm/proofs/utils/gcm_two_block_closers.ml";;
needs "arm/proofs/utils/gcm_three_block_closers.ml";;

(* --- arithmetic side-lemmas for the branch resolution -------------------- *)

(* cbz x1 at entry: bit_len = 8*byte_len is nonzero for byte_len >= 1. *)
let GCM_CBZ_LEMMA = prove
 (`1 <= byte_len /\ byte_len <= 16 ==> ~(val(word(8*byte_len):int64) = 0)`,
  STRIP_TAC THEN SUBGOAL_THEN `val(word(8*byte_len):int64) = 8*byte_len` SUBST1_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC;
    ASM_ARITH_TAC]);;

(* word_sub (word n) (word 1) = word (n-1) for 1 <= n <= 16. *)
let GCM_WSUB1 = prove
 (`1 <= n /\ n <= 16 ==> word_sub (word n:int64) (word 1) = word (n - 1)`,
  STRIP_TAC THEN REWRITE_TAC[WORD_SUB] THEN
  COND_CASES_TAC THENL
   [AP_TERM_TAC THEN ASM_ARITH_TAC; POP_ASSUM MP_TAC THEN ASM_ARITH_TAC]);;

(* word_and with the high mask (~0x7f) clears small values. *)
let GCM_ANDMASK0 = prove
 (`!m. m < 128 ==> word_and (word m:int64) (word 18446744073709551488) = word 0`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(word 18446744073709551488:int64) = word_not (word (2 EXP 7 - 1))` SUBST1_TAC THENL
   [CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN CONV_TAC WORD_BLAST; ALL_TAC] THEN
  REWRITE_TAC[WORD_AND_NOT_MASK_WORD] THEN
  SUBGOAL_THEN `val(word m:int64) = m` SUBST1_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `m DIV 2 EXP 7 = 0` SUBST1_TAC THENL
   [REWRITE_TAC[DIV_EQ_0] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[MULT_CLAUSES; WORD_VAL]);;

(* In-loop guard: X5 = in_ptr + ((byte_len-1) & ~0x7f) is the address where
    the full-128-byte-chunk region ends (the main-loop bound). For <= 16 bytes
    there are no full chunks, so the offset is 0 and X5 = in_ptr; then cmp x0,x5
    compares equal and the b.ge into the tail is taken. *)
(* MILA TODO:: RENAME GCM_LOOP_END_EQ_INPTR_1BLOCK *)
let GCM_X5_LEMMA = prove
 (`1 <= byte_len /\ byte_len <= 16 ==>
   word_add (word_and (word_sub (word_ushr (word (8*byte_len):int64) 3) (word 1))
                      (word 18446744073709551488)) in_ptr = in_ptr`,
  STRIP_TAC THEN
  SUBGOAL_THEN `word_ushr (word (8*byte_len):int64) 3 = word byte_len` SUBST1_TAC THENL
   [MATCH_MP_TAC NBLOCK_USHR_BYTELEN THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[GCM_WSUB1] THEN
  SUBGOAL_THEN `word_and (word (byte_len-1):int64) (word 18446744073709551488) = word 0` SUBST1_TAC THENL
   [MATCH_MP_TAC GCM_ANDMASK0 THEN ASM_ARITH_TAC; ALL_TAC] THEN
  CONV_TAC WORD_RULE);;

(* The tail length register X5 = (in_ptr + byte_len) - in_ptr = word byte_len. *)
let GCM_X5TAIL_LEMMA = prove
 (`byte_len <= 16 ==>
   word_sub (word_add in_ptr (word_ushr (word (8*byte_len):int64) 3)) in_ptr = word byte_len`,
  STRIP_TAC THEN
  SUBGOAL_THEN `word_ushr (word (8*byte_len):int64) 3 = word byte_len` SUBST1_TAC THENL
   [MATCH_MP_TAC NBLOCK_USHR_BYTELEN THEN ASM_ARITH_TAC; ALL_TAC] THEN
  CONV_TAC WORD_RULE);;

(* Each tail-cascade b.gt (cmp x5,#t for t in 16..112) is NOT taken when the
   tail length byte_len <= 16. *)
let GCM_CASC_FALSE = prove
 (`!byte_len t. byte_len <= 16 /\ 16 <= t /\ t <= 112 ==>
    ((~(val (word_sub (word byte_len:int64) (word t)) = 0) /\
      (ival (word_sub (word byte_len:int64) (word t)) < &0 <=>
       ~(ival (word byte_len:int64) - &t = ival (word_sub (word byte_len:int64) (word t)))))
     <=> F)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `ival(word byte_len:int64) = &byte_len` ASSUME_TAC THENL
   [MATCH_MP_TAC NBLOCK_IVAL_WORD_SMALL THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `word_sub (word byte_len:int64) (word t) = iword(&byte_len - &t)` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM IWORD_INT_SUB; WORD_IWORD]; ALL_TAC] THEN
  SUBGOAL_THEN `ival(iword(&byte_len - &t):int64) = &byte_len - &t` ASSUME_TAC THENL
   [MATCH_MP_TAC IVAL_IWORD THEN REWRITE_TAC[DIMINDEX_64] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_SUB_CONV) THEN
    SUBGOAL_THEN `&byte_len:int <= &16 /\ &16:int <= &t /\ &t:int <= &112` MP_TAC THENL
     [ASM_REWRITE_TAC[INT_OF_NUM_LE]; ALL_TAC] THEN
    INT_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[VAL_EQ_0; GSYM IVAL_EQ_0] THEN
  SUBGOAL_THEN `&byte_len:int <= &16 /\ &16:int <= &t` MP_TAC THENL
   [ASM_REWRITE_TAC[INT_OF_NUM_LE]; ALL_TAC] THEN
  INT_ARITH_TAC);;

(* Resolve any pending tail-cascade b.gt PC conditional (thresholds 16..112)
   to its fall-through by rewriting the signed-gt test to F. *)
let GCM_CASCADE_TAC : tactic =
  FIRST_X_ASSUM(fun bl16 -> if concl bl16 = `byte_len <= 16` then
    RULE_ASSUM_TAC(REWRITE_RULE(
      (map (fun t -> MATCH_MP GCM_CASC_FALSE (CONJ bl16
              (CONJ (ARITH_RULE(vsubst[mk_numeral(num_of_int t),`t:num`] `16 <= t`))
                    (ARITH_RULE(vsubst[mk_numeral(num_of_int t),`t:num`] `t <= 112`)))))
           [16;32;48;64;80;96;112]) @ [COND_CLAUSES])) THEN
    ASSUME_TAC bl16
  else NO_TAC);;

(* --- the 1-block correctness theorem ------------------------------------- *)

(* ============================================================              *)
(* 1-block GHASH final-closure helpers/tactics, in the SAME                  *)
(* GCM_NB_GHASH_CLOSE framework as bands 2-8, instantiated at N=1            *)
(* (0 full blocks + 1 partial; the single masked block sits in the           *)
(* block-1/xi-accumulator position with multiplier h, so qS=1,               *)
(* qB=4*1+1=5).  Routes through GHASH_POLYVAL_ACC_1 (centralized in          *)
(* gcm_aesgcm_helpers.ml with ACC_2..8) + the 1-block ACC Karatsuba          *)
(* bridge GHASH_1BLOCK_KARATSUBA_EQ_POLYVAL_ACC (in                          *)
(* gcm_one_block_closers.ml with the other per-length bridges).              *)
(* ============================================================              *)

let XI_HS_LO_1 = prove
 (`word_subword (word_reversefields 8 (word_join (word_subword (xi:(128)word) (64,64):(64)word) (word_subword xi (0,64):(64)word):(128)word)) (0,64):(64)word =
   word_subword (word_reversefields 8 xi) (0,64)`,
  REWRITE_TAC[GSYM REV8_JOIN_FOLD; REVERSEFIELDS8_SUBWORD_LO; REVERSEFIELDS8_SUBWORD_HI] THEN
  CONV_TAC WORD_BLAST);;
let XI_HS_HI_1 = prove
 (`word_subword (word_reversefields 8 (word_join (word_subword (xi:(128)word) (64,64):(64)word) (word_subword xi (0,64):(64)word):(128)word)) (64,64):(64)word =
   word_subword (word_reversefields 8 xi) (64,64)`,
  REWRITE_TAC[GSYM REV8_JOIN_FOLD; REVERSEFIELDS8_SUBWORD_LO; REVERSEFIELDS8_SUBWORD_HI] THEN
  CONV_TAC WORD_BLAST);;

(* Step 1+2: no full blocks to fold (N=1) — FOLD_SPEC_CTS is the identity. *)
let GCM_1B_FOLD_SPEC_CTS : tactic = ALL_TAC;;

(* Step 3: b0-general mask-register collapse over the assumptions. *)
let GCM_1B_MASK_COLLAPSE_ASMS : tactic =
  SUBGOAL_THEN `1 <= (byte_len:num) /\ byte_len <= 16` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(fun bth -> if concl bth = `1 <= (byte_len:num) /\ byte_len <= 16` then
    RULE_ASSUM_TAC(REWRITE_RULE[GEN `b0:int128` (MP (SPEC_ALL NBLOCK_MASK_REG) bth)]) else NO_TAC);;

(* Step 5: no separate KSk fold (the single block's counter is ivec, folded in
   TAIL_NOFINAL when ct = word_xor pt (aes ivec ...) is established). *)
let GCM_1B_KS1_FOLD : tactic = ALL_TAC;;

(* Closer tail: ctm abbrev + ct fold + ACC_1 bridge + atomic ABBREVs +
   inner pmul ABBREVs + z-vars + qS/qB — mirror GCM_2B_TAIL_NOFINAL for N=1
   (single block, in the block-1/xi-accumulator position, multiplier h). *)
let GCM_1B_TAIL_NOFINAL : tactic =
  REWRITE_TAC[GHASH_POLYVAL_ACC_1; GSYM WORD_REVERSEFIELDS_XOR_8_128] THEN
  ABBREV_TAC `mask = word (2 EXP (8 * byte_len) - 1):(128)word` THEN
  ABBREV_TAC `ctm = word_and (ct:(128)word) mask` THEN
  (* Fold the spec-side AES expression to the abbreviated ciphertext ct.     *)
  (* The postcondition uses the upstream aes256_encrypt; unfold it to the    *)
  (* aese/aesmc chain the simulator produced via AES256_ENCRYPT_UNFOLD.      *)
  SUBGOAL_THEN
    `word_xor pt (aes256_encrypt ivec
       [rk0;rk1;rk2;rk3;rk4;rk5;rk6;rk7;rk8;rk9;rk10;rk11;rk12;rk13;rk14]) = ct`
    (fun th -> REWRITE_TAC[th]) THENL [
    MAP_EVERY EXPAND_TAC ["ct"; "s13"] THEN
    REWRITE_TAC[AES256_ENCRYPT_UNFOLD; LET_DEF; LET_END_DEF; WORD_XOR_ASSOC]; ALL_TAC ] THEN
  SUBGOAL_THEN `word_and (mask:(128)word) (ct:(128)word) = ctm`
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th]) THENL [
    EXPAND_TAC "ctm" THEN CONV_TAC WORD_BITWISE_RULE; ALL_TAC ] THEN
  (* Apply the 1-block ACC Karatsuba bridge. *)
  FIRST_ASSUM(fun th ->
    if is_eq(concl th) && (try lhs(concl th) = `word_subword (h1k:(128)word) (0,64):(64)word` with _ -> false)
    then REWRITE_TAC[GSYM(MATCH_MP GHASH_1BLOCK_KARATSUBA_EQ_POLYVAL_ACC th)] else NO_TAC) THEN
  REWRITE_TAC[ghash_1block_karatsuba; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
  REWRITE_TAC[REV64_LOWER_LANE; REV64_UPPER_LANE; REV8_JOIN_FOLD] THEN
  MATCH_MP_TAC(MESON[]
    `x = y ==> word_reversefields 8 x = word_reversefields 8 y:(128)word`) THEN
  FIRST_ASSUM(fun th ->
    if is_eq(concl th) && rand(concl th) = `final_xi:(128)word` then SUBST1_TAC(SYM th) else NO_TAC) THEN
  REWRITE_TAC[WORD_INSERT_AS_JOIN_LO; WORD_INSERT_AS_JOIN_HI;
              KAR_SUBWORD_LEMMA; WORD_SWAP_HALVES_INVOLUTION;
              WORD_OR_REFL; WORD_XOR_ASSOC; WORD_SUBWORD_XOR;
              SWAPHALVES128_SUBWORD_LO; SWAPHALVES128_SUBWORD_HI] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[HALFSWAP_XOR; GSYM WORD_REVERSEFIELDS_XOR_8_128;
              WORD_XOR_0; WORD_XOR_ASSOC;
              REV8_JOIN_FOLD; REVERSEFIELDS8_SUBWORD_LO; REVERSEFIELDS8_SUBWORD_HI] THEN
  REWRITE_TAC[WORD_XOR_ASSOC; KAR_MID_BRIDGE; WORD_SUBWORD_0;
              WORD_XOR_0; WORD_XOR_0_LEFT] THEN
  REWRITE_TAC[GSYM WORD_SUBWORD_XOR; GSYM WORD_REVERSEFIELDS_XOR_8_128;
              WORD_XOR_ASSOC; WORD_XOR_0; WORD_XOR_0_LEFT] THEN
  REWRITE_TAC[karatsuba_mid; WORD_REVERSEFIELDS_XOR_8_128; WORD_SUBWORD_XOR] THEN
  (* atomic ABBREVs: 1 ct block (ctm) + xi + h.  Naming mirrors the framework
     (c1lo/c1hi for the masked block, xilo/xihi, hd0/hd1 for h). *)
  ABBREV_TAC `(c1lo:(64)word) = word_subword (word_reversefields 8 (ctm:(128)word)) (0,64)` THEN
  ABBREV_TAC `(c1hi:(64)word) = word_subword (word_reversefields 8 (ctm:(128)word)) (64,64)` THEN
  ABBREV_TAC `(xilo:(64)word) = word_subword (word_reversefields 8 (xi:(128)word)) (0,64)` THEN
  ABBREV_TAC `(xihi:(64)word) = word_subword (word_reversefields 8 (xi:(128)word)) (64,64)` THEN
  ABBREV_TAC `(hd0:(64)word) = word_subword (h:(128)word) (0,64)` THEN
  ABBREV_TAC `(hd1:(64)word) = word_subword (h:(128)word) (64,64)` THEN
  ASM_REWRITE_TAC[] THEN
  (* inner pmul ABBREVs (single block in the xi-accumulator position). *)
  ABBREV_TAC `(w1lo:(128)word) = word_pmul (word_xor (xilo:(64)word) (c1lo:(64)word)) (hd0:(64)word)` THEN
  ABBREV_TAC `(w1hi:(128)word) = word_pmul (word_xor (xihi:(64)word) (c1hi:(64)word)) (hd1:(64)word)` THEN
  ABBREV_TAC `(w1md:(128)word) = word_pmul (word_xor (word_xor (xihi:(64)word) (c1hi:(64)word)) (word_xor (xilo:(64)word) (c1lo:(64)word))) (word_xor (hd0:(64)word) (hd1:(64)word))` THEN
  REWRITE_TAC[DOUBLE_SUBWORD_JOIN; DOUBLE_SUBWORD_JOIN_HI; WORD_SUBWORD_XOR] THEN
  SUBGOAL_THEN
    `word_pmul (word_xor (xihi:(64)word) (word_xor (c1hi:(64)word) (word_xor (xilo:(64)word) (c1lo:(64)word)))) (word_xor (hd0:(64)word) (hd1:(64)word)):(128)word = w1md`
    (fun th -> REWRITE_TAC[th]) THENL
    [EXPAND_TAC "w1md" THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  (* z-vars. *)
  ABBREV_TAC `(w1lo_l:(64)word) = word_subword (w1lo:(128)word) (0,64)` THEN
  ABBREV_TAC `(w1lo_h:(64)word) = word_subword (w1lo:(128)word) (64,64)` THEN
  ABBREV_TAC `(w1hi_l:(64)word) = word_subword (w1hi:(128)word) (0,64)` THEN
  ABBREV_TAC `(w1hi_h:(64)word) = word_subword (w1hi:(128)word) (64,64)` THEN
  ABBREV_TAC `(w1md_l:(64)word) = word_subword (w1md:(128)word) (0,64)` THEN
  ABBREV_TAC `(w1md_h:(64)word) = word_subword (w1md:(128)word) (64,64)` THEN
  ASM_REWRITE_TAC[] THEN
  (* qS: small Barrett pmul (1 atom). *)
  ABBREV_TAC `(qS:(128)word) = word_pmul (w1lo_l:(64)word) (word 13979173243358019584:(64)word)` THEN
  ASM_REWRITE_TAC[] THEN
  (* qB: big Barrett pmul (4N+1 = 5 atoms). *)
  ABBREV_TAC `(qB:(128)word) = word_pmul
    (word_xor (w1md_l:(64)word) (word_xor w1lo_l (word_xor w1hi_l (word_xor (word_subword (qS:(128)word) (0,64)) w1lo_h)))) (word 13979173243358019584:(64)word)` THEN
  SUBGOAL_THEN
    `word_pmul (word_xor (w1lo_h:(64)word) (word_xor w1md_l (word_xor w1hi_l (word_xor w1lo_l (word_subword (qS:(128)word) (0,64)))))) (word 13979173243358019584:(64)word):(128)word = qB`
    (fun th -> REWRITE_TAC[th]) THENL
    [EXPAND_TAC "qB" THEN AP_THM_TAC THEN AP_TERM_TAC THEN
     CONV_TAC(BINOP_CONV bubble_sort_conv) THEN REFL_TAC; ALL_TAC];;

(* per-half XOR-AC closer — mirror GCM_2B_HALF_CLOSE (1 mid, qS 1, qB 5). *)
let GCM_1B_FOLD_MIDS_TAC : tactic =
  fun (asl,gg) ->
    let rec finds hd t acc = match t with
      | Comb(Comb(Const("word_pmul",_),a),x) when x = hd ->
          a :: (finds hd a (finds hd x acc))
      | Comb(l,r) -> finds hd l (finds hd r acc)
      | Abs(_,b) -> finds hd b acc | _ -> acc in
    let hdw = `word_xor (hd0:(64)word) hd1` in
    let mk tgt hd arg =
      SUBGOAL_THEN
        (mk_eq(list_mk_comb(`word_pmul:(64)word->(64)word->(128)word`,[arg;hd]),tgt))
        (fun th -> REWRITE_TAC[th]) THENL
       [EXPAND_TAC (fst(dest_var tgt)) THEN AP_THM_TAC THEN AP_TERM_TAC THEN
        CONV_TAC WORD_RULE; ALL_TAC] in
    (EVERY (map (mk `w1md:(128)word` hdw) (setify(finds hdw gg [])))) (asl,gg);;

let GCM_1B_FOLD_TO tgt natoms : tactic =
  let w64 = `word 13979173243358019584:(64)word` in
  fun (asl,gg) ->
    let rec finds t acc = match t with
      | Comb(Comb(Const("word_pmul",_),a),x) when x = w64 ->
          a :: (finds a (finds x acc))
      | Comb(l,r) -> finds l (finds r acc) | Abs(_,b) -> finds b acc | _ -> acc in
    let rec at t = match t with
      | Comb(Comb(Const("word_xor",_),x),y) -> at x @ at y | _ -> [t] in
    let args = List.filter (fun a -> List.length(at a) = natoms) (setify(finds gg [])) in
    (EVERY (map (fun a ->
       FIRST [SUBGOAL_THEN
                (mk_eq(list_mk_comb(`word_pmul:(64)word->(64)word->(128)word`,[a;w64]),tgt))
                (fun th -> REWRITE_TAC[th]) THENL
               [EXPAND_TAC (fst(dest_var tgt)) THEN AP_THM_TAC THEN AP_TERM_TAC THEN
                CONV_TAC(BINOP_CONV bubble_fix) THEN REFL_TAC; ALL_TAC];
              ALL_TAC]) args)) (asl,gg);;

let GCM_1B_HALF_CLOSE : tactic =
  GCM_1B_FOLD_MIDS_TAC THEN ASM_REWRITE_TAC[] THEN
  GCM_1B_FOLD_TO `qS:(128)word` 1 THEN ASM_REWRITE_TAC[] THEN
  GCM_1B_FOLD_TO `qB:(128)word` 5 THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(BINOP_CONV bubble_fix) THEN REFL_TAC;;

(* The full GHASH closer — mirror GCM_2B_GHASH_CLOSE exactly (N=1). *)
let GCM_1B_GHASH_CLOSE : tactic =
  GCM_1B_FOLD_SPEC_CTS THEN
  REWRITE_TAC[GHASH_POLYVAL_ACC_1; GSYM WORD_REVERSEFIELDS_XOR_8_128] THEN
  GCM_1B_MASK_COLLAPSE_ASMS THEN
  GCM_1B_KS1_FOLD THEN
  GCM_1B_TAIL_NOFINAL THEN
  REWRITE_TAC[XI_HS_LO_1; XI_HS_HI_1] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `word_pmul (word_xor (xihi:(64)word) (word_xor c1hi (word_xor xilo c1lo)))
              (word_xor (hd0:(64)word) hd1):(128)word = w1md`
   (fun th -> REWRITE_TAC[th]) THENL
   [EXPAND_TAC "w1md" THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  BINOP_TAC THENL [GCM_1B_HALF_CLOSE; GCM_1B_HALF_CLOSE];;

(* Keystream/ciphertext abbreviation for the single (masked) block: read the
   AES keystream from its register (the aese/aesmc chain, no rk14) and define
   s13 + ct, mirroring the register-grab idiom of the wider bands rather than a
   hand-written 28-deep aese literal.  (The block is masked, so there is no
   plain word_xor-store for abbrev_ct_from_store to read.) *)
let GCM_1B_ABBREV_CT : tactic =
  FIRST_ASSUM(fun th ->
    if can(term_match[]`read Q0 (s:armstate) = (x:int128)`)(concl th) &&
       (try fst(dest_const(repeat rator (rand(concl th)))) = "aese" with _ -> false)
    then ABBREV_TAC(mk_eq(mk_var("s13",`:(128)word`), rand(concl th)))
    else NO_TAC) THEN
  ABBREV_TAC `ct = word_xor (word_xor pt s13) rk14 :(128)word`;;

(* Named goal for the 1BLOCK band (shared spec lifted by the ABS layer). *)
let gcm_1b_goal =
 `!in_ptr out_ptr xi_ptr ivec_ptr key_ptr htable_ptr
    (pt:(128)word) (out0:(128)word) (ivec:(128)word)
    (rk0:(128)word) (rk1:(128)word) (rk2:(128)word) (rk3:(128)word)
    (rk4:(128)word) (rk5:(128)word) (rk6:(128)word) (rk7:(128)word)
    (rk8:(128)word) (rk9:(128)word) (rk10:(128)word) (rk11:(128)word)
    (rk12:(128)word) (rk13:(128)word) (rk14:(128)word)
    (xi:(128)word) (h:(128)word) (h1k:(128)word) byte_len stackptr pc.
    1 <= byte_len /\ byte_len <= 16 /\
    aligned 16 stackptr /\
    nonoverlapping (word pc,4600) (in_ptr:int64,16) /\
    nonoverlapping (word pc,4600) (out_ptr:int64,16) /\
    nonoverlapping (word pc,4600) (xi_ptr:int64,16) /\
    nonoverlapping (word pc,4600) (ivec_ptr:int64,16) /\
    nonoverlapping (word pc,4600) (key_ptr:int64,240) /\
    nonoverlapping (word pc,4600) (htable_ptr:int64,256) /\
    nonoverlapping (word pc,4600) (stackptr:int64,80) /\
    nonoverlapping (in_ptr,16) (out_ptr,16) /\
    nonoverlapping (in_ptr,16) (xi_ptr,16) /\
    nonoverlapping (in_ptr,16) (ivec_ptr,16) /\
    nonoverlapping (out_ptr,16) (xi_ptr,16) /\
    nonoverlapping (out_ptr,16) (ivec_ptr,16) /\
    nonoverlapping (xi_ptr,16) (ivec_ptr,16) /\
    nonoverlapping (key_ptr,240) (out_ptr,16) /\
    nonoverlapping (key_ptr,240) (xi_ptr,16) /\
    nonoverlapping (key_ptr,240) (ivec_ptr,16) /\
    nonoverlapping (htable_ptr,256) (out_ptr,16) /\
    nonoverlapping (htable_ptr,256) (xi_ptr,16) /\
    nonoverlapping (htable_ptr,256) (ivec_ptr,16) /\
    nonoverlapping (stackptr,80) (out_ptr,16) /\
    nonoverlapping (stackptr,80) (xi_ptr,16) /\
    nonoverlapping (stackptr,80) (ivec_ptr,16) /\
    nonoverlapping (stackptr,80) (in_ptr,16) /\
    nonoverlapping (stackptr,80) (key_ptr,240) /\
    nonoverlapping (stackptr,80) (htable_ptr,256) /\
    nonoverlapping (ivec_ptr,16) (word pc,4600) /\
    nonoverlapping (xi_ptr,16) (word pc,4600) /\
    nonoverlapping (out_ptr,16) (word pc,4600)
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) aes256_gcm_mc /\
           read PC s = word pc /\
           C_ARGUMENTS [in_ptr; word (8 * byte_len); out_ptr; xi_ptr;
                        ivec_ptr; key_ptr; htable_ptr] s /\
           read SP s = word_add stackptr (word 80) /\
           read (memory :> bytes128 in_ptr) s = pt /\
           read (memory :> bytes128 out_ptr) s = out0 /\
           read (memory :> bytes128 ivec_ptr) s = ivec /\
           read (memory :> bytes128 (word_add key_ptr (word 0))) s = rk0 /\
           read (memory :> bytes128 (word_add key_ptr (word 16))) s = rk1 /\
           read (memory :> bytes128 (word_add key_ptr (word 32))) s = rk2 /\
           read (memory :> bytes128 (word_add key_ptr (word 48))) s = rk3 /\
           read (memory :> bytes128 (word_add key_ptr (word 64))) s = rk4 /\
           read (memory :> bytes128 (word_add key_ptr (word 80))) s = rk5 /\
           read (memory :> bytes128 (word_add key_ptr (word 96))) s = rk6 /\
           read (memory :> bytes128 (word_add key_ptr (word 112))) s = rk7 /\
           read (memory :> bytes128 (word_add key_ptr (word 128))) s = rk8 /\
           read (memory :> bytes128 (word_add key_ptr (word 144))) s = rk9 /\
           read (memory :> bytes128 (word_add key_ptr (word 160))) s = rk10 /\
           read (memory :> bytes128 (word_add key_ptr (word 176))) s = rk11 /\
           read (memory :> bytes128 (word_add key_ptr (word 192))) s = rk12 /\
           read (memory :> bytes128 (word_add key_ptr (word 208))) s = rk13 /\
           read (memory :> bytes128 (word_add key_ptr (word 224))) s = rk14 /\
           read (memory :> bytes128 xi_ptr) s = xi /\
           read (memory :> bytes128 htable_ptr) s = word_swaphalves128 h /\
           read (memory :> bytes128 (word_add htable_ptr (word 16))) s = h1k /\
           word_subword h1k (0,64):(64)word = karatsuba_mid h)
      (\s. let ct = word_xor pt (aes256_encrypt ivec
                     [rk0;rk1;rk2;rk3;rk4;rk5;rk6;rk7;rk8;rk9;rk10;rk11;rk12;rk13;rk14]) in
           let mask = word (2 EXP (8 * byte_len) - 1):(128)word in
           let ctm = word_and ct mask in
           read PC s = word(pc + 4588) /\
           read X0 s = word byte_len /\
           read (memory :> bytes128 out_ptr) s =
             word_or ctm (word_and out0 (word_not mask)) /\
           read (memory :> bytes128 xi_ptr) s =
             word_reversefields 8
               (ghash_polyval_acc h (word_reversefields 8 xi)
                                    [word_reversefields 8 ctm]))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [memory :> bytes(out_ptr,16);
                  memory :> bytes(xi_ptr,16);
                  memory :> bytes(ivec_ptr,16)] ,,
       MAYCHANGE [SP] ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes64 stackptr;
                  memory :> bytes64 (word_add stackptr (word 8));
                  memory :> bytes64 (word_add stackptr (word 16));
                  memory :> bytes64 (word_add stackptr (word 24));
                  memory :> bytes64 (word_add stackptr (word 32));
                  memory :> bytes64 (word_add stackptr (word 40));
                  memory :> bytes64 (word_add stackptr (word 48));
                  memory :> bytes64 (word_add stackptr (word 56));
                  memory :> bytes64 (word_add stackptr (word 64));
                  memory :> bytes64 (word_add stackptr (word 72))])`;;

let AES256_GCM_ENCRYPT_LT_1BLOCK_CONCRETE = prove
 (gcm_1b_goal,
  (* Entry + nop/cbz (1-2): byte_len >= 1 so the cbz is not taken. *)
  GCM_INIT_TAC GCM_CBZ_LEMMA THEN

  (* Prologue (3-19) + 8-lane counter setup & AES rounds (20-263). *)
  GCM_PROLOGUE_TAC THEN
  GCM_RUN 20 263 THEN

  (* In-loop guard (264-266): X5 collapses to in_ptr so b.ge is taken. *)
  GCM_INLOOP_GUARD_TAC GCM_X5_LEMMA THEN

  (* Tail entry loads (267-272); collapse the tail length X5 = byte_len. *)
  GCM_RUN 267 272 THEN GCM_BND16 GCM_X5TAIL_LEMMA THEN

  (* Tail length cascade (273-321): every cmp x5,#0x70..#0x10; b.gt falls
     through for a single block. *)
  GCM_RUN_THEN GCM_CASCADE_TAC 273 321 THEN

  (* b .L256_enc_blocks_less_than_1 (322) -> the shared masked tail. *)
  ARM_STEPS_TAC AES256_GCM_EXEC [322] THEN GCM_ENC_SIMPLIFY_TAC THEN

  (* Abbreviate the block-0 AES output (`ct`/`s13`) so the shared one-block
     closures fold it back. *)
  GCM_1B_ABBREV_CT THEN

  (* Tail mask build (323-336); collapse the data-dependent mask register Q0
     to word (2^(8*byte_len) - 1). *)
  GCM_RUN 323 336 THEN
  SUBGOAL_THEN `1 <= byte_len /\ byte_len <= 16` MP_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP NBLOCK_MASK_REG th])) THEN

  (* AND_VEC, bif, masked store, GHASH Karatsuba up to the final EOR3 (337-359). *)
  GCM_RUN 337 359 THEN
  GCM_NBLOCK_POST_SIM_NORMALIZE_TAC THEN
  ABBREV_FINAL_XI_TAC THEN

  (* EXT, REV64, ST1, MOV, LDP*4 (360-367) — Q19 opaque.  Stop at RET (pc+4588). *)
  ARM_STEPS_TAC AES256_GCM_EXEC (360--367) THEN

  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_SIMP_TAC[ONE_BLOCK_USHR_BYTELEN; ONE_BLOCK_MASK_IDEM] THEN
  CONJ_TAC THENL
   [(* ciphertext-store branch: the goal's `ct` uses upstream aes256_encrypt
       (see gcm_1b_goal); unfold it to the aese/aesmc chain and close as the
       generic GCM_1BLOCK_CT1_STEP_TAC does. *)
    EXPAND_TAC "ct" THEN EXPAND_TAC "s13" THEN
    REWRITE_TAC[AES256_ENCRYPT_UNFOLD; LET_DEF; LET_END_DEF; WORD_XOR_ASSOC] THEN
    ASM_REWRITE_TAC[];
    GCM_1B_GHASH_CLOSE]);;

(* ========================================================================= *)
(* The L256_enc_blocks_more_than_1 branch (2-block: full block 1 + partial   *)
(* block 2) of this same single binary, proved as a standalone theorem and   *)
(* applied exactly as the XTS length-band lemmas are.  Reuses the two-block  *)
(* masked closers (TWOBLOCK_MASK_REG, TWOBLOCK_USHR, GHASH Karatsuba bridge) *)
(* at the tactic level.                                                      *)
(* ========================================================================= *)

(* --- 2-block-branch length/cascade helpers (thresholds over 16+byte_len) --- *)

let GCM_CBZ_LEMMA2 = prove
 (`1 <= byte_len /\ byte_len <= 16 ==> ~(val(word(128+8*byte_len):int64) = 0)`,
  STRIP_TAC THEN SUBGOAL_THEN `val(word(128+8*byte_len):int64) = 128+8*byte_len` SUBST1_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC;
    ASM_ARITH_TAC]);;

let GCM_WSUB2 = prove(`byte_len <= 16 ==> word_sub (word (16+byte_len):int64) (word 1) = word (15 + byte_len)`,
  CONV_TAC WORD_RULE);;

let GCM_X5_LEMMA2 = prove(
  `1 <= byte_len /\ byte_len <= 16 ==>
   word_add (word_and (word_sub (word_ushr (word (128+8*byte_len):int64) 3) (word 1))
                      (word 18446744073709551488)) in_ptr = in_ptr`,
  STRIP_TAC THEN
  SUBGOAL_THEN `word_ushr (word (128+8*byte_len):int64) 3 = word (16+byte_len)` SUBST1_TAC THENL
   [ASM_SIMP_TAC[TWOBLOCK_USHR]; ALL_TAC] THEN
  ASM_SIMP_TAC[GCM_WSUB2] THEN
  SUBGOAL_THEN `word_and (word (15+byte_len):int64) (word 18446744073709551488) = word 0` SUBST1_TAC THENL
   [MATCH_MP_TAC GCM_ANDMASK0 THEN ASM_ARITH_TAC; ALL_TAC] THEN
  CONV_TAC WORD_RULE);;

let GCM_X5TAIL_LEMMA2 = prove(
  `byte_len <= 16 ==>
   word_sub (word_add in_ptr (word_ushr (word (128+8*byte_len):int64) 3)) in_ptr = word (16+byte_len)`,
  ASM_SIMP_TAC[TWOBLOCK_USHR] THEN CONV_TAC WORD_RULE);;

let GCM_CASC2_FALSE = prove(
  `!byte_len t. byte_len <= 16 /\ 32 <= t /\ t <= 112 ==>
    ((~(val (word_sub (word (16+byte_len):int64) (word t)) = 0) /\
      (ival (word_sub (word (16+byte_len):int64) (word t)) < &0 <=>
       ~(ival (word (16+byte_len):int64) - &t = ival (word_sub (word (16+byte_len):int64) (word t)))))
     <=> F)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `ival(word (16+byte_len):int64) = &(16+byte_len)` ASSUME_TAC THENL
   [MATCH_MP_TAC NBLOCK_IVAL_WORD_SMALL THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `word_sub (word (16+byte_len):int64) (word t) = iword(&(16+byte_len) - &t)` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM IWORD_INT_SUB; WORD_IWORD]; ALL_TAC] THEN
  SUBGOAL_THEN `ival(iword(&(16+byte_len) - &t):int64) = &(16+byte_len) - &t` ASSUME_TAC THENL
   [MATCH_MP_TAC IVAL_IWORD THEN REWRITE_TAC[DIMINDEX_64] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_SUB_CONV) THEN
    SUBGOAL_THEN `&(16+byte_len):int <= &32 /\ &32:int <= &t /\ &t:int <= &112` MP_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN INT_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[VAL_EQ_0; GSYM IVAL_EQ_0] THEN
  SUBGOAL_THEN `&(16+byte_len):int <= &32 /\ &32:int <= &t` MP_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN INT_ARITH_TAC);;

let GCM_CASC2_TRUE = prove(
  `1 <= byte_len /\ byte_len <= 16 ==>
    ((~(val (word_sub (word (16+byte_len):int64) (word 16)) = 0) /\
      (ival (word_sub (word (16+byte_len):int64) (word 16)) < &0 <=>
       ~(ival (word (16+byte_len):int64) - &16 = ival (word_sub (word (16+byte_len):int64) (word 16)))))
     <=> T)`,
  STRIP_TAC THEN
  SUBGOAL_THEN `ival(word (16+byte_len):int64) = &(16+byte_len)` ASSUME_TAC THENL
   [MATCH_MP_TAC NBLOCK_IVAL_WORD_SMALL THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `word_sub (word (16+byte_len):int64) (word 16) = iword(&(16+byte_len) - &16)` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM IWORD_INT_SUB; WORD_IWORD]; ALL_TAC] THEN
  SUBGOAL_THEN `ival(iword(&(16+byte_len) - &16):int64) = &(16+byte_len) - &16` ASSUME_TAC THENL
   [MATCH_MP_TAC IVAL_IWORD THEN REWRITE_TAC[DIMINDEX_64] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_SUB_CONV) THEN
    SUBGOAL_THEN `&(16+byte_len):int <= &32` MP_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN INT_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[VAL_EQ_0; GSYM IVAL_EQ_0] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_ADD] THEN
  SUBGOAL_THEN `&1:int <= &byte_len` MP_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN INT_ARITH_TAC);;

let GCM_CASCADE2_TAC : tactic =
  FIRST_X_ASSUM(fun bl16 -> if concl bl16 = `byte_len <= 16` then
    FIRST_X_ASSUM(fun bl1 -> if concl bl1 = `1 <= byte_len` then
      RULE_ASSUM_TAC(REWRITE_RULE(
        (map (fun t -> MATCH_MP GCM_CASC2_FALSE (CONJ bl16
                (CONJ (ARITH_RULE(vsubst[mk_numeral(num_of_int t),`t:num`] `32 <= t`))
                      (ARITH_RULE(vsubst[mk_numeral(num_of_int t),`t:num`] `t <= 112`)))))
             [32;48;64;80;96;112]) @
        [MATCH_MP GCM_CASC2_TRUE (CONJ bl1 bl16); COND_CLAUSES])) THEN
      ASSUME_TAC bl1 THEN ASSUME_TAC bl16
    else NO_TAC)
  else NO_TAC);;

(* Store-based ct abbreviation (robust against the per-branch Q-register
   scramble): reads the keystream actually stored at out_ptr+off and
   abbreviates s13_N + ctN.  Defined here at its first use (the 2-block band)
   and shared verbatim by the 3/4/5/6/7/8-block branches below.
   Strict matcher: pins the EXACT store address AND the plaintext ptN (a loose
   `term_match` on `read (memory :> bytes128 out_ptr) s` unifies out_ptr with
   `word_add out_ptr (word N)` because out_ptr is free, which mis-attributed
   ct1=s13_2 at 7/8 blocks; pinning the address and ptN avoids that). *)
let abbrev_ct_from_store off nidx : tactic = fun (asl,w) ->
  let addr = if off=0 then `out_ptr:int64`
    else vsubst[mk_small_numeral off,`Z:num`] `word_add out_ptr (word Z):int64` in
  let ptn = mk_var("pt"^string_of_int nidx,`:(128)word`) in
  let store = tryfind (fun (_,th) -> let t=concl th in
    if is_eq t &&
       (try fst(dest_const(rator(rator(lhs t))))="read" with _->false) &&
       (try aconv (rand(rand(rand(rator(lhs t))))) addr with _->false) &&
       (try fst(dest_const(repeat rator (rand t)))="word_xor" with _->false) &&
       (try aconv (lhand(lhand(rand t))) ptn with _->false)
    then t else fail()) asl in
  let ks0 = rand(lhand(rand store)) in
  let ks =
    if (try fst(dest_const(rator(rator ks0)))="read" with _->false)
    then (try tryfind (fun (_,th) -> let t=concl th in
                if is_eq t && lhs t = ks0 then rand t else fail()) asl
          with _ -> ks0)
    else ks0 in
  let s13n = mk_var("s13_"^string_of_int nidx,`:(128)word`) in
  let ctn = mk_var("ct"^string_of_int nidx,`:(128)word`) in
  (ABBREV_TAC(mk_eq(s13n,ks)) THEN
   ABBREV_TAC(mk_eq(ctn,
     list_mk_comb(`word_xor:(128)word->(128)word->(128)word`,
       [list_mk_comb(`word_xor:(128)word->(128)word->(128)word`,[ptn;s13n]); `rk14:(128)word`]))))
  (asl,w);;

(* --- 2-block GHASH final-closure helpers/tactics, in the 5/6/7-block
   GCM_NB_GHASH_CLOSE framework (instantiated at N=2: 1 full + 1 partial).
   ct abbreviation is store-based (abbrev_ct_from_store), as in bands 5/6/7. --- *)

(* ============================================================              *)
(* NEW 5B-style 2-block GHASH closer (mirrors GCM_5B_* / N=4).               *)
(* N=2: 1 full block + 1 partial.                                            *)
(* ============================================================              *)

(* xi half-swap normalizers (defined inline; mirror XI_HS_LO_5/HI_5). *)
let XI_HS_LO_2 = prove
 (`word_subword (word_reversefields 8 (word_join (word_subword (xi:(128)word) (64,64):(64)word) (word_subword xi (0,64):(64)word):(128)word)) (0,64):(64)word =
   word_subword (word_reversefields 8 xi) (0,64)`,
  REWRITE_TAC[GSYM REV8_JOIN_FOLD; REVERSEFIELDS8_SUBWORD_LO; REVERSEFIELDS8_SUBWORD_HI] THEN
  CONV_TAC WORD_BLAST);;
let XI_HS_HI_2 = prove
 (`word_subword (word_reversefields 8 (word_join (word_subword (xi:(128)word) (64,64):(64)word) (word_subword xi (0,64):(64)word):(128)word)) (64,64):(64)word =
   word_subword (word_reversefields 8 xi) (64,64)`,
  REWRITE_TAC[GSYM REV8_JOIN_FOLD; REVERSEFIELDS8_SUBWORD_LO; REVERSEFIELDS8_SUBWORD_HI] THEN
  CONV_TAC WORD_BLAST);;

(* ct1 closer (counter = ivec, no inc) — mirror CT_CLOSE_5/4/3. *)
let CT_CLOSE_2 nidx =
  let s13n = "s13_"^string_of_int nidx and ctn = "ct"^string_of_int nidx in
  EXPAND_TAC ctn THEN EXPAND_TAC s13n THEN
  REWRITE_TAC[AES256_ENCRYPT_UNFOLD; LET_DEF; LET_END_DEF; WORD_XOR_ASSOC] THEN ASM_REWRITE_TAC[];;

(* Step 1+2: establish the single full-block spec-form ct fold F1 and fold it
   into the RHS ghash list — mirror GCM_5B_FOLD_SPEC_CTS (folds 4). *)
let GCM_2B_FOLD_SPEC_CTS : tactic =
  (* F1 *)
  SUBGOAL_THEN
   `word_xor pt1 (aes256_encrypt ivec [rk0;rk1;rk2;rk3;rk4;rk5;rk6;rk7;rk8;rk9;rk10;rk11;rk12;rk13;rk14]) = ct1`
   ASSUME_TAC THENL
   [EXPAND_TAC "ct1" THEN
    REWRITE_TAC[AES256_ENCRYPT_UNFOLD; LET_DEF; LET_END_DEF; WORD_XOR_ASSOC] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* fold the single full block into the RHS ghash list only. *)
  (fun (asl,w) ->
     let getf n = snd(find (fun (_,th) ->
       is_eq(concl th) && rand(concl th)=mk_var("ct"^string_of_int n,`:(128)word`) &&
       (let l=lhand(concl th) in
        (try fst(dest_const(rator(rator l)))="word_xor" with _->false) &&
        (try fst(dest_const(repeat rator (rand l)))="aes256_encrypt" with _->false))) asl) in
     GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [getf 1] (asl,w));;

(* Step 3: b0-general mask-register collapse over the assumptions. *)
let GCM_2B_MASK_COLLAPSE_ASMS : tactic =
  SUBGOAL_THEN `1 <= (byte_len:num) /\ byte_len <= 16` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(fun bth -> if concl bth = `1 <= (byte_len:num) /\ byte_len <= 16` then
    RULE_ASSUM_TAC(REWRITE_RULE[GEN `b0:int128` (MP (SPEC_ALL TWOBLOCK_MASK_REG) bth)]) else NO_TAC);;

(* Step 5: bridge the machine block-2 keystream (collapsed +1 counter, baked
   into final_xi) to the spec ct2 — mirror GCM_5B_KS5_FOLD (+4) / KS3 (+2). *)
let GCM_2B_KS2_FOLD : tactic = fun (asl,w) ->
  let substr sub s =
    let ls=String.length s and lb=String.length sub in
    let rec go i = if i+lb>ls then false
                   else if String.sub s i lb = sub then true else go(i+1) in go 0 in
  let fxidef = snd(find (fun (_,th) ->
    is_eq(concl th) && (try rand(concl th)=`final_xi:(128)word` with _->false)) asl) in
  let body = lhs(concl fxidef) in
  let best = ref None in
  let rec walk t =
    (try let s=string_of_term t in
      if substr "pt2" s && substr "aese" s && substr "rk14" s &&
         (try fst(dest_const(repeat rator t))="word_xor" with _->false) &&
         (match !best with None->true | Some b -> String.length s < String.length(string_of_term b))
      then best := Some t
     with _->());
    (match t with Comb(a,b)->walk a; walk b | Abs(_,b)->walk b | _->()) in
  walk body;
  let ks2 = (match !best with Some t->t | None->failwith "KS2_FOLD: ks2 not found") in
  (SUBGOAL_THEN (mk_eq(ks2, `ct2:(128)word`)) ASSUME_TAC THENL
    [CONV_TAC SYM_CONV THEN EXPAND_TAC "ct2" THEN
     REWRITE_TAC[AES256_ENCRYPT_UNFOLD] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
     REWRITE_TAC[WORD_XOR_ASSOC] THEN
     AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
     REPEAT(AP_THM_TAC ORELSE AP_TERM_TAC) THEN
     REWRITE_TAC[gcm_ctr_inc] THEN
     REWRITE_TAC[WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
     REWRITE_TAC[WORD_BLAST `!x:(32)word. word_reversefields 8 x = word_bytereverse x`] THEN
     REWRITE_TAC[GSYM CTR_WORD_INSERT] THEN
     REWRITE_TAC[BYTEREVERSE_JOIN_FOLD];
     ALL_TAC] THEN
   FIRST_ASSUM(fun th ->
     if is_eq(concl th) && rand(concl th)=`ct2:(128)word` &&
        (try fst(dest_const(repeat rator (lhs(concl th))))="word_xor" with _->false) &&
        String.length(string_of_term(lhs(concl th))) > 1000
     then RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th] else NO_TAC))
  (asl,w);;

(* Closer tail (ctm2 abbrev + bridge + atomic ABBREVs + qS/qB), minus the
   final BINOP — mirror GCM_5B_TAIL_NOFINAL for N=2.  No h^3 normalization
   (only h, h^2 appear). *)
let GCM_2B_TAIL_NOFINAL : tactic =
  ABBREV_TAC `mask = word (2 EXP (8 * byte_len) - 1):(128)word` THEN
  ABBREV_TAC `ctm2 = word_and (ct2:(128)word) mask` THEN
  SUBGOAL_THEN `word_and (mask:(128)word) (ct2:(128)word) = ctm2`
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th]) THENL [
    EXPAND_TAC "ctm2" THEN CONV_TAC WORD_BITWISE_RULE; ALL_TAC ] THEN
  (* Apply 2-block bridge. *)
  MP_TAC(SPECL
    [`word_reversefields 8 (word_xor xi ct1):int128`;
     `word_reversefields 8 ctm2:int128`;
     `h:int128`; `h1k:int128`;
     `word_join (word 0:(64)word) (word_subword (h1k:(128)word) (64,64):(64)word):(128)word`]
    GHASH_2BLOCK_KARATSUBA_EQ_POLYVAL_ACC) THEN
  SUBGOAL_THEN
    `word_subword (word_join (word 0:(64)word) (word_subword (h1k:(128)word) (64,64):(64)word):(128)word) (0,64):(64)word =
     karatsuba_mid (polyval_dot h h)`
    (fun th -> REWRITE_TAC[th]) THENL [
    SUBGOAL_THEN
      `word_subword (word_join (word 0:(64)word) (word_subword (h1k:(128)word) (64,64):(64)word):(128)word) (0,64):(64)word =
       word_subword (h1k:(128)word) (64,64):(64)word`
      (fun th -> REWRITE_TAC[th]) THENL [CONV_TAC WORD_BLAST; ASM_REWRITE_TAC[]]; ALL_TAC ] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN
  REWRITE_TAC[ghash_2block_karatsuba; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[SWAPHALVES128_SUBWORD_LO; SWAPHALVES128_SUBWORD_HI] THEN
  SUBGOAL_THEN
    `word_subword (word_join (word 0:(64)word) (karatsuba_mid (polyval_dot h h):(64)word):(128)word) (0,64):(64)word =
     karatsuba_mid (polyval_dot h h)`
    (fun th -> REWRITE_TAC[th]) THENL [CONV_TAC WORD_BLAST; ALL_TAC] THEN
  REWRITE_TAC[GSYM karatsuba_mid] THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
  CONV_TAC SYM_CONV THEN
  FIRST_ASSUM(fun th ->
    if is_eq(concl th) && rand(concl th) = `final_xi:(128)word` &&
       (try (let l = lhs(concl th) in is_comb l &&
             (let r = rator l in not(is_comb r && (try fst(dest_const(rator r)) = "read" with _ -> false))))
        with _ -> false)
    then SUBST1_TAC(SYM th) else NO_TAC) THEN
  REWRITE_TAC[REV64_LOWER_LANE; REV64_UPPER_LANE; REV8_JOIN_FOLD] THEN
  MATCH_MP_TAC(MESON[]
    `x = y ==> word_reversefields 8 x = word_reversefields 8 y:(128)word`) THEN
  REWRITE_TAC[WORD_SWAP_HALVES_INVOLUTION] THEN
  REWRITE_TAC[WORD_JOIN_SELF_MID] THEN
  CONV_TAC(LAND_CONV(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
  REWRITE_TAC[WORD_INSERT_AS_JOIN_LO; WORD_INSERT_AS_JOIN_HI;
              KAR_SUBWORD_LEMMA; WORD_SWAP_HALVES_INVOLUTION; WORD_JOIN_SELF_MID;
              WORD_OR_REFL; WORD_XOR_ASSOC; WORD_SUBWORD_XOR;
              SWAPHALVES128_SUBWORD_LO; SWAPHALVES128_SUBWORD_HI] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[HALFSWAP_XOR; GSYM WORD_REVERSEFIELDS_XOR_8_128;
              WORD_XOR_0; WORD_XOR_ASSOC;
              REV8_JOIN_FOLD; REVERSEFIELDS8_SUBWORD_LO; REVERSEFIELDS8_SUBWORD_HI] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  CONV_TAC(TOP_DEPTH_CONV PMUL_NORM_CONV) THEN
  SUBGOAL_THEN
    `word_subword (word 0:(128)word) (0,64):(64)word = word 0 /\
     word_subword (word 0:(128)word) (64,64):(64)word = word 0`
    (fun th -> REWRITE_TAC[th]) THENL [CONJ_TAC THEN CONV_TAC WORD_BLAST; ALL_TAC] THEN
  REWRITE_TAC[WORD_XOR_0; WORD_XOR_0_LEFT] THEN
  REWRITE_TAC[karatsuba_mid; WORD_REVERSEFIELDS_XOR_8_128; WORD_SUBWORD_XOR] THEN
  (* 10 atomic ABBREVs (c1lo..c2hi, xi, hd..he). *)
  ABBREV_TAC `(c1lo:(64)word) = word_subword (word_reversefields 8 (ct1:(128)word)) (0,64)` THEN
  ABBREV_TAC `(c1hi:(64)word) = word_subword (word_reversefields 8 (ct1:(128)word)) (64,64)` THEN
  ABBREV_TAC `(c2lo:(64)word) = word_subword (word_reversefields 8 (ctm2:(128)word)) (0,64)` THEN
  ABBREV_TAC `(c2hi:(64)word) = word_subword (word_reversefields 8 (ctm2:(128)word)) (64,64)` THEN
  ABBREV_TAC `(xilo:(64)word) = word_subword (word_reversefields 8 (xi:(128)word)) (0,64)` THEN
  ABBREV_TAC `(xihi:(64)word) = word_subword (word_reversefields 8 (xi:(128)word)) (64,64)` THEN
  ABBREV_TAC `(hd0:(64)word) = word_subword (h:(128)word) (0,64)` THEN
  ABBREV_TAC `(hd1:(64)word) = word_subword (h:(128)word) (64,64)` THEN
  ABBREV_TAC `(he0:(64)word) = word_subword ((polyval_dot h h):(128)word) (0,64)` THEN
  ABBREV_TAC `(he1:(64)word) = word_subword ((polyval_dot h h):(128)word) (64,64)` THEN
  ASM_REWRITE_TAC[] THEN
  (* 6 inner pmul ABBREVs (w1..w2). *)
  ABBREV_TAC `(w1lo:(128)word) = word_pmul (word_xor (xilo:(64)word) (c1lo:(64)word)) (he0:(64)word)` THEN
  ABBREV_TAC `(w1hi:(128)word) = word_pmul (word_xor (xihi:(64)word) (c1hi:(64)word)) (he1:(64)word)` THEN
  ABBREV_TAC `(w1md:(128)word) = word_pmul (word_xor (word_xor (xihi:(64)word) (c1hi:(64)word)) (word_xor (xilo:(64)word) (c1lo:(64)word))) (word_xor (he0:(64)word) (he1:(64)word))` THEN
  ABBREV_TAC `(w2lo:(128)word) = word_pmul (c2lo:(64)word) (hd0:(64)word)` THEN
  ABBREV_TAC `(w2hi:(128)word) = word_pmul (c2hi:(64)word) (hd1:(64)word)` THEN
  ABBREV_TAC `(w2md:(128)word) = word_pmul (word_xor (c2hi:(64)word) (c2lo:(64)word)) (word_xor (hd0:(64)word) (hd1:(64)word))` THEN
  REWRITE_TAC[DOUBLE_SUBWORD_JOIN; DOUBLE_SUBWORD_JOIN_HI; WORD_SUBWORD_XOR] THEN
  SUBGOAL_THEN
    `word_pmul (word_xor (xihi:(64)word) (word_xor (c1hi:(64)word) (word_xor (xilo:(64)word) (c1lo:(64)word)))) (word_xor (he0:(64)word) (he1:(64)word)):(128)word = w1md`
    (fun th -> REWRITE_TAC[th]) THENL
    [EXPAND_TAC "w1md" THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  (* 12 z-vars. *)
  ABBREV_TAC `(w1lo_l:(64)word) = word_subword (w1lo:(128)word) (0,64)` THEN
  ABBREV_TAC `(w1lo_h:(64)word) = word_subword (w1lo:(128)word) (64,64)` THEN
  ABBREV_TAC `(w1hi_l:(64)word) = word_subword (w1hi:(128)word) (0,64)` THEN
  ABBREV_TAC `(w1hi_h:(64)word) = word_subword (w1hi:(128)word) (64,64)` THEN
  ABBREV_TAC `(w1md_l:(64)word) = word_subword (w1md:(128)word) (0,64)` THEN
  ABBREV_TAC `(w1md_h:(64)word) = word_subword (w1md:(128)word) (64,64)` THEN
  ABBREV_TAC `(w2lo_l:(64)word) = word_subword (w2lo:(128)word) (0,64)` THEN
  ABBREV_TAC `(w2lo_h:(64)word) = word_subword (w2lo:(128)word) (64,64)` THEN
  ABBREV_TAC `(w2hi_l:(64)word) = word_subword (w2hi:(128)word) (0,64)` THEN
  ABBREV_TAC `(w2hi_h:(64)word) = word_subword (w2hi:(128)word) (64,64)` THEN
  ABBREV_TAC `(w2md_l:(64)word) = word_subword (w2md:(128)word) (0,64)` THEN
  ABBREV_TAC `(w2md_h:(64)word) = word_subword (w2md:(128)word) (64,64)` THEN
  ASM_REWRITE_TAC[] THEN
  (* Normalize LHS mid-pmuls to abbreviated w?md (swapped xor arg order). *)
  SUBGOAL_THEN `word_pmul (word_xor (c2lo:(64)word) (c2hi:(64)word)) (word_xor (hd0:(64)word) (hd1:(64)word)):(128)word = w2md`
    (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "w2md" THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  SUBGOAL_THEN `word_pmul (word_xor (xilo:(64)word) (word_xor (c1lo:(64)word) (word_xor (xihi:(64)word) (c1hi:(64)word)))) (word_xor (he0:(64)word) (he1:(64)word)):(128)word = w1md`
    (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "w1md" THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  (* qS: small Barrett pmul; fold both XOR orderings. *)
  ABBREV_TAC `(qS:(128)word) = word_pmul (word_xor (w2lo_l:(64)word) (w1lo_l)) (word 13979173243358019584:(64)word)` THEN
  SUBGOAL_THEN `word_pmul (word_xor (w1lo_l:(64)word) (w2lo_l)) (word 13979173243358019584:(64)word):(128)word = qS`
    (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "qS" THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  (* qB: big Barrett pmul; fold the LHS-order copy via bubble_sort_conv. *)
  ABBREV_TAC `(qB:(128)word) = word_pmul
    (word_xor (w2md_l:(64)word) (word_xor w1md_l (word_xor w2lo_l (word_xor w1lo_l (word_xor w2hi_l (word_xor w1hi_l (word_xor (word_subword (qS:(128)word) (0,64)) (word_xor w2lo_h (w1lo_h))))))))) (word 13979173243358019584:(64)word)` THEN
  SUBGOAL_THEN
    `word_pmul (word_xor (w1lo_h:(64)word) (word_xor w2lo_h (word_xor w1md_l (word_xor w2md_l (word_xor w1hi_l (word_xor w2hi_l (word_xor w1lo_l (word_xor w2lo_l ((word_subword (qS:(128)word) (0,64))))))))))) (word 13979173243358019584:(64)word):(128)word = qB`
    (fun th -> REWRITE_TAC[th]) THENL
    [EXPAND_TAC "qB" THEN AP_THM_TAC THEN AP_TERM_TAC THEN
     CONV_TAC(BINOP_CONV bubble_sort_conv) THEN REFL_TAC; ALL_TAC];;

(* per-half XOR-AC closer — mirror GCM_5B_HALF_CLOSE (2 mids, qS 2, qB 7). *)
let GCM_2B_FOLD_MIDS_TAC : tactic =
  fun (asl,gg) ->
    let rec finds hd t acc = match t with
      | Comb(Comb(Const("word_pmul",_),a),x) when x = hd ->
          a :: (finds hd a (finds hd x acc))
      | Comb(l,r) -> finds hd l (finds hd r acc)
      | Abs(_,b) -> finds hd b acc | _ -> acc in
    let hew = `word_xor (he0:(64)word) he1`
    and hdw = `word_xor (hd0:(64)word) hd1` in
    let mk tgt hd arg =
      SUBGOAL_THEN
        (mk_eq(list_mk_comb(`word_pmul:(64)word->(64)word->(128)word`,[arg;hd]),tgt))
        (fun th -> REWRITE_TAC[th]) THENL
       [EXPAND_TAC (fst(dest_var tgt)) THEN AP_THM_TAC THEN AP_TERM_TAC THEN
        CONV_TAC WORD_RULE; ALL_TAC] in
    (EVERY ((map (mk `w1md:(128)word` hew) (setify(finds hew gg [])))
          @ (map (mk `w2md:(128)word` hdw) (setify(finds hdw gg []))))) (asl,gg);;

let GCM_2B_FOLD_TO tgt natoms : tactic =
  let w64 = `word 13979173243358019584:(64)word` in
  fun (asl,gg) ->
    let rec finds t acc = match t with
      | Comb(Comb(Const("word_pmul",_),a),x) when x = w64 ->
          a :: (finds a (finds x acc))
      | Comb(l,r) -> finds l (finds r acc) | Abs(_,b) -> finds b acc | _ -> acc in
    let rec at t = match t with
      | Comb(Comb(Const("word_xor",_),x),y) -> at x @ at y | _ -> [t] in
    let args = List.filter (fun a -> List.length(at a) = natoms) (setify(finds gg [])) in
    (EVERY (map (fun a ->
       FIRST [SUBGOAL_THEN
                (mk_eq(list_mk_comb(`word_pmul:(64)word->(64)word->(128)word`,[a;w64]),tgt))
                (fun th -> REWRITE_TAC[th]) THENL
               [EXPAND_TAC (fst(dest_var tgt)) THEN AP_THM_TAC THEN AP_TERM_TAC THEN
                CONV_TAC(BINOP_CONV bubble_fix) THEN REFL_TAC; ALL_TAC];
              ALL_TAC]) args)) (asl,gg);;

let GCM_2B_HALF_CLOSE : tactic =
  GCM_2B_FOLD_MIDS_TAC THEN ASM_REWRITE_TAC[] THEN
  GCM_2B_FOLD_TO `qS:(128)word` 2 THEN ASM_REWRITE_TAC[] THEN
  GCM_2B_FOLD_TO `qB:(128)word` 9 THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(BINOP_CONV bubble_fix) THEN REFL_TAC;;

(* The full GHASH closer — mirror GCM_5B_GHASH_CLOSE. *)
let GCM_2B_GHASH_CLOSE : tactic =
  GCM_2B_FOLD_SPEC_CTS THEN
  REWRITE_TAC[GHASH_POLYVAL_ACC_2; GSYM WORD_REVERSEFIELDS_XOR_8_128] THEN
  GCM_2B_MASK_COLLAPSE_ASMS THEN
  GCM_2B_KS2_FOLD THEN
  GCM_2B_TAIL_NOFINAL THEN
  REWRITE_TAC[XI_HS_LO_2; XI_HS_HI_2] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `word_pmul (word_xor (xihi:(64)word) (word_xor c1hi (word_xor xilo c1lo)))
              (word_xor (he0:(64)word) he1):(128)word = w1md`
   (fun th -> REWRITE_TAC[th]) THENL
   [EXPAND_TAC "w1md" THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  BINOP_TAC THENL [GCM_2B_HALF_CLOSE; GCM_2B_HALF_CLOSE];;

(* masked-ct2 store conjunct closer — mirror GCM_5B_MASKED_CT5_CLOSE (+1). *)
let GCM_2B_MASKED_CT2_CLOSE : tactic =
  SUBGOAL_THEN `1 <= byte_len /\ byte_len <= 16` MP_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP TWOBLOCK_MASK_REG th]) THEN
  REWRITE_TAC[NBLOCK_MASK_IDEM] THEN
  MATCH_MP_TAC(MESON[] `x = y ==> word_or (word_and x m) r = word_or (word_and y m) r:(128)word`) THEN
  CONV_TAC SYM_CONV THEN REWRITE_TAC[AES256_ENCRYPT_UNFOLD] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[WORD_XOR_ASSOC] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REPEAT(AP_THM_TAC ORELSE AP_TERM_TAC) THEN
  REWRITE_TAC[gcm_ctr_inc] THEN
  REWRITE_TAC[WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
  REWRITE_TAC[WORD_BLAST `!x:(32)word. word_reversefields 8 x = word_bytereverse x`] THEN
  REWRITE_TAC[GSYM CTR_WORD_INSERT] THEN
  REWRITE_TAC[BYTEREVERSE_JOIN_FOLD];;

(* Named goal for the 2BLOCK band (shared spec lifted by the ABS layer). *)
let gcm_2b_goal =
 `!in_ptr out_ptr xi_ptr ivec_ptr key_ptr htable_ptr
    (pt1:(128)word) (pt2:(128)word) (out0:(128)word) (ivec:(128)word)
    (rk0:(128)word) (rk1:(128)word) (rk2:(128)word) (rk3:(128)word)
    (rk4:(128)word) (rk5:(128)word) (rk6:(128)word) (rk7:(128)word)
    (rk8:(128)word) (rk9:(128)word) (rk10:(128)word) (rk11:(128)word)
    (rk12:(128)word) (rk13:(128)word) (rk14:(128)word)
    (xi:(128)word) (h:(128)word) (h1k:(128)word) byte_len stackptr pc.
    1 <= byte_len /\ byte_len <= 16 /\
    aligned 16 stackptr /\
    nonoverlapping (word pc,4600) (in_ptr:int64,32) /\
    nonoverlapping (word pc,4600) (out_ptr:int64,32) /\
    nonoverlapping (word pc,4600) (xi_ptr:int64,16) /\
    nonoverlapping (word pc,4600) (ivec_ptr:int64,16) /\
    nonoverlapping (word pc,4600) (key_ptr:int64,240) /\
    nonoverlapping (word pc,4600) (htable_ptr:int64,256) /\
    nonoverlapping (word pc,4600) (stackptr:int64,80) /\
    nonoverlapping (in_ptr,32) (out_ptr,32) /\
    nonoverlapping (in_ptr,32) (xi_ptr,16) /\
    nonoverlapping (in_ptr,32) (ivec_ptr,16) /\
    nonoverlapping (out_ptr,32) (xi_ptr,16) /\
    nonoverlapping (out_ptr,32) (ivec_ptr,16) /\
    nonoverlapping (xi_ptr,16) (ivec_ptr,16) /\
    nonoverlapping (key_ptr,240) (out_ptr,32) /\
    nonoverlapping (key_ptr,240) (xi_ptr,16) /\
    nonoverlapping (key_ptr,240) (ivec_ptr,16) /\
    nonoverlapping (htable_ptr,256) (out_ptr,32) /\
    nonoverlapping (htable_ptr,256) (xi_ptr,16) /\
    nonoverlapping (htable_ptr,256) (ivec_ptr,16) /\
    nonoverlapping (stackptr,80) (out_ptr,32) /\
    nonoverlapping (stackptr,80) (xi_ptr,16) /\
    nonoverlapping (stackptr,80) (ivec_ptr,16) /\
    nonoverlapping (stackptr,80) (in_ptr,32) /\
    nonoverlapping (stackptr,80) (key_ptr,240) /\
    nonoverlapping (stackptr,80) (htable_ptr,256) /\
    nonoverlapping (ivec_ptr,16) (word pc,4600) /\
    nonoverlapping (xi_ptr,16) (word pc,4600) /\
    nonoverlapping (out_ptr,32) (word pc,4600)
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) aes256_gcm_mc /\
           read PC s = word pc /\
           C_ARGUMENTS [in_ptr; word (128 + 8 * byte_len); out_ptr; xi_ptr;
                        ivec_ptr; key_ptr; htable_ptr] s /\
           read SP s = word_add stackptr (word 80) /\
           read (memory :> bytes128 in_ptr) s = pt1 /\
           read (memory :> bytes128 (word_add in_ptr (word 16))) s = pt2 /\
           read (memory :> bytes128 (word_add out_ptr (word 16))) s = out0 /\
           read (memory :> bytes128 ivec_ptr) s = ivec /\
           read (memory :> bytes128 (word_add key_ptr (word 0))) s = rk0 /\
           read (memory :> bytes128 (word_add key_ptr (word 16))) s = rk1 /\
           read (memory :> bytes128 (word_add key_ptr (word 32))) s = rk2 /\
           read (memory :> bytes128 (word_add key_ptr (word 48))) s = rk3 /\
           read (memory :> bytes128 (word_add key_ptr (word 64))) s = rk4 /\
           read (memory :> bytes128 (word_add key_ptr (word 80))) s = rk5 /\
           read (memory :> bytes128 (word_add key_ptr (word 96))) s = rk6 /\
           read (memory :> bytes128 (word_add key_ptr (word 112))) s = rk7 /\
           read (memory :> bytes128 (word_add key_ptr (word 128))) s = rk8 /\
           read (memory :> bytes128 (word_add key_ptr (word 144))) s = rk9 /\
           read (memory :> bytes128 (word_add key_ptr (word 160))) s = rk10 /\
           read (memory :> bytes128 (word_add key_ptr (word 176))) s = rk11 /\
           read (memory :> bytes128 (word_add key_ptr (word 192))) s = rk12 /\
           read (memory :> bytes128 (word_add key_ptr (word 208))) s = rk13 /\
           read (memory :> bytes128 (word_add key_ptr (word 224))) s = rk14 /\
           read (memory :> bytes128 xi_ptr) s = xi /\
           read (memory :> bytes128 htable_ptr) s = word_swaphalves128 h /\
           read (memory :> bytes128 (word_add htable_ptr (word 16))) s = h1k /\
           read (memory :> bytes128 (word_add htable_ptr (word 32))) s =
             word_swaphalves128 (polyval_dot h h) /\
           word_subword h1k (0,64):(64)word = karatsuba_mid h /\
           word_subword h1k (64,64):(64)word = karatsuba_mid (polyval_dot h h))
      (\s. let ct1 =
             word_xor pt1
               (aes256_encrypt ivec [rk0;rk1;rk2;rk3;rk4;rk5;rk6;rk7;rk8;rk9;rk10;rk11;rk12;rk13;rk14]) in
           let ct2 =
             word_xor pt2
               (aes256_encrypt (gcm_ctr_inc ivec) [rk0;rk1;rk2;rk3;rk4;rk5;rk6;rk7;rk8;rk9;rk10;rk11;rk12;rk13;rk14]) in
           let mask = word (2 EXP (8 * byte_len) - 1):(128)word in
           let ctm2 = word_and ct2 mask in
           read PC s = word(pc + 4588) /\
           read X0 s = word (16 + byte_len) /\
           read (memory :> bytes128 out_ptr) s = ct1 /\
           read (memory :> bytes128 (word_add out_ptr (word 16))) s =
             word_or ctm2 (word_and out0 (word_not mask)) /\
           read (memory :> bytes128 xi_ptr) s =
             word_reversefields 8
               (ghash_polyval_acc h (word_reversefields 8 xi)
                                    [word_reversefields 8 ct1;
                                     word_reversefields 8 ctm2]))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [memory :> bytes(out_ptr,32);
                  memory :> bytes(xi_ptr,16);
                  memory :> bytes(ivec_ptr,16)] ,,
       MAYCHANGE [SP] ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes64 stackptr;
                  memory :> bytes64 (word_add stackptr (word 8));
                  memory :> bytes64 (word_add stackptr (word 16));
                  memory :> bytes64 (word_add stackptr (word 24));
                  memory :> bytes64 (word_add stackptr (word 32));
                  memory :> bytes64 (word_add stackptr (word 40));
                  memory :> bytes64 (word_add stackptr (word 48));
                  memory :> bytes64 (word_add stackptr (word 56));
                  memory :> bytes64 (word_add stackptr (word 64));
                  memory :> bytes64 (word_add stackptr (word 72))])`;;

let AES256_GCM_ENCRYPT_LT_2BLOCK_CONCRETE = prove
 (gcm_2b_goal,
  (* ---- symbolic simulation (store-based ct abbreviation) ---- *)
  GCM_INIT_TAC GCM_CBZ_LEMMA2 THEN GCM_PROLOGUE_TAC THEN GCM_RUN 20 263 THEN
  GCM_INLOOP_GUARD_TAC GCM_X5_LEMMA2 THEN GCM_RUN 267 272 THEN
  GCM_BND16 GCM_X5TAIL_LEMMA2 THEN
  GCM_RUN_THEN GCM_CASCADE2_TAC 273 321 THEN
  GCM_RUN 322 331 THEN abbrev_ct_from_store 0 1 THEN
  GCM_RUN 332 350 THEN
  SUBGOAL_THEN `1 <= byte_len /\ byte_len <= 16` MP_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP TWOBLOCK_MASK_REG th])) THEN
  GCM_RUN 351 374 THEN
  GCM_NBLOCK_POST_SIM_NORMALIZE_TAC THEN ABBREV_FINAL_XI_TAC THEN
  ARM_STEPS_TAC AES256_GCM_EXEC (375--381) THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ENSURES_FINAL_STATE_TAC THEN
  SUBGOAL_THEN `1 <= byte_len /\ byte_len <= 16` MP_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP TWOBLOCK_MASK_REG th]) THEN
  ASM_SIMP_TAC[TWOBLOCK_USHR] THEN
  (* ---- three conjuncts: ct1, masked-ct2, GHASH ---- *)
  CONJ_TAC THENL [CT_CLOSE_2 1; ALL_TAC] THEN
  CONJ_TAC THENL [GCM_2B_MASKED_CT2_CLOSE; ALL_TAC] THEN
  (* ---- ct2 abbreviation (spec form) so the closer's ctm2 works ---- *)
  ABBREV_TAC `ct2 = word_xor pt2
    (aes256_encrypt (gcm_ctr_inc ivec) [rk0;rk1;rk2;rk3;rk4;rk5;rk6;rk7;rk8;rk9;rk10;rk11;rk12;rk13;rk14]):(128)word` THEN
  (* ---- GHASH conjunct ---- *)
  GCM_2B_GHASH_CLOSE);;

(* ========================================================================= *)
(* The L256_enc_blocks_more_than_2 branch (3-block: full block 1 + full      *)
(* block 2 + partial block 3, total 33..48 bytes) of the same single binary, *)
(* proved as a standalone theorem and applied exactly as the XTS length-band *)
(* lemmas are.  The tail-dispatch cascade now takes the cmp x5,#0x20 / b.gt  *)
(* branch into .more_than_2, which stores block 1, falls into .more_than_1   *)
(* (block 2), then into .less_than_1 (masked partial block 3 + final GHASH). *)
(* Reuses the three-block masked closers (THREEBLOCK_MASK_REG/USHR, GHASH    *)
(* Karatsuba bridge) at the tactic level.                                    *)
(* ========================================================================= *)

(* --- 3-block-branch length/cascade helpers (thresholds over 32+byte_len) --- *)

let GCM_CBZ_LEMMA3 = prove
 (`1 <= byte_len /\ byte_len <= 16 ==> ~(val(word(256+8*byte_len):int64) = 0)`,
  STRIP_TAC THEN SUBGOAL_THEN `val(word(256+8*byte_len):int64) = 256+8*byte_len` SUBST1_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC;
    ASM_ARITH_TAC]);;

let GCM_WSUB3 = prove
 (`byte_len <= 16 ==> word_sub (word (32+byte_len):int64) (word 1) = word (31 + byte_len)`,
  CONV_TAC WORD_RULE);;

let GCM_X5_LEMMA3 = prove
 (`1 <= byte_len /\ byte_len <= 16 ==>
   word_add (word_and (word_sub (word_ushr (word (256+8*byte_len):int64) 3) (word 1))
                      (word 18446744073709551488)) in_ptr = in_ptr`,
  STRIP_TAC THEN
  SUBGOAL_THEN `word_ushr (word (256+8*byte_len):int64) 3 = word (32+byte_len)` SUBST1_TAC THENL
   [ASM_SIMP_TAC[THREEBLOCK_USHR]; ALL_TAC] THEN
  ASM_SIMP_TAC[GCM_WSUB3] THEN
  SUBGOAL_THEN `word_and (word (31+byte_len):int64) (word 18446744073709551488) = word 0` SUBST1_TAC THENL
   [MATCH_MP_TAC GCM_ANDMASK0 THEN ASM_ARITH_TAC; ALL_TAC] THEN
  CONV_TAC WORD_RULE);;

let GCM_X5TAIL_LEMMA3 = prove
 (`byte_len <= 16 ==>
   word_sub (word_add in_ptr (word_ushr (word (256+8*byte_len):int64) 3)) in_ptr = word (32+byte_len)`,
  ASM_SIMP_TAC[THREEBLOCK_USHR] THEN CONV_TAC WORD_RULE);;

let GCM_CASC3_FALSE = prove
 (`!byte_len t. byte_len <= 16 /\ 48 <= t /\ t <= 112 ==>
    ((~(val (word_sub (word (32+byte_len):int64) (word t)) = 0) /\
      (ival (word_sub (word (32+byte_len):int64) (word t)) < &0 <=>
       ~(ival (word (32+byte_len):int64) - &t = ival (word_sub (word (32+byte_len):int64) (word t)))))
     <=> F)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `ival(word (32+byte_len):int64) = &(32+byte_len)` ASSUME_TAC THENL
   [MATCH_MP_TAC NBLOCK_IVAL_WORD_SMALL THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `word_sub (word (32+byte_len):int64) (word t) = iword(&(32+byte_len) - &t)` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM IWORD_INT_SUB; WORD_IWORD]; ALL_TAC] THEN
  SUBGOAL_THEN `ival(iword(&(32+byte_len) - &t):int64) = &(32+byte_len) - &t` ASSUME_TAC THENL
   [MATCH_MP_TAC IVAL_IWORD THEN REWRITE_TAC[DIMINDEX_64] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_SUB_CONV) THEN
    SUBGOAL_THEN `&(32+byte_len):int <= &48 /\ &48:int <= &t /\ &t:int <= &112` MP_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN INT_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[VAL_EQ_0; GSYM IVAL_EQ_0] THEN
  SUBGOAL_THEN `&(32+byte_len):int <= &48 /\ &48:int <= &t` MP_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN INT_ARITH_TAC);;

let GCM_CASC3_TRUE = prove
 (`1 <= byte_len /\ byte_len <= 16 ==>
    ((~(val (word_sub (word (32+byte_len):int64) (word 32)) = 0) /\
      (ival (word_sub (word (32+byte_len):int64) (word 32)) < &0 <=>
       ~(ival (word (32+byte_len):int64) - &32 = ival (word_sub (word (32+byte_len):int64) (word 32)))))
     <=> T)`,
  STRIP_TAC THEN
  SUBGOAL_THEN `ival(word (32+byte_len):int64) = &(32+byte_len)` ASSUME_TAC THENL
   [MATCH_MP_TAC NBLOCK_IVAL_WORD_SMALL THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `word_sub (word (32+byte_len):int64) (word 32) = iword(&(32+byte_len) - &32)` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM IWORD_INT_SUB; WORD_IWORD]; ALL_TAC] THEN
  SUBGOAL_THEN `ival(iword(&(32+byte_len) - &32):int64) = &(32+byte_len) - &32` ASSUME_TAC THENL
   [MATCH_MP_TAC IVAL_IWORD THEN REWRITE_TAC[DIMINDEX_64] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_SUB_CONV) THEN
    SUBGOAL_THEN `&(32+byte_len):int <= &48` MP_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN INT_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[VAL_EQ_0; GSYM IVAL_EQ_0] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_ADD] THEN
  SUBGOAL_THEN `&1:int <= &byte_len` MP_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN INT_ARITH_TAC);;

(* Resolve a pending tail-cascade b.gt PC conditional for the 3-block path:
   thresholds 48..112 are not taken, threshold 32 is taken into .more_than_2. *)
let GCM_CASCADE3_TAC : tactic =
  FIRST_X_ASSUM(fun bl16 -> if concl bl16 = `byte_len <= 16` then
    FIRST_X_ASSUM(fun bl1 -> if concl bl1 = `1 <= byte_len` then
      RULE_ASSUM_TAC(REWRITE_RULE(
        (map (fun t -> MATCH_MP GCM_CASC3_FALSE (CONJ bl16
                (CONJ (ARITH_RULE(vsubst[mk_numeral(num_of_int t),`t:num`] `48 <= t`))
                      (ARITH_RULE(vsubst[mk_numeral(num_of_int t),`t:num`] `t <= 112`)))))
             [48;64;80;96;112]) @
        [MATCH_MP GCM_CASC3_TRUE (CONJ bl1 bl16); COND_CLAUSES])) THEN
      ASSUME_TAC bl1 THEN ASSUME_TAC bl16
    else NO_TAC)
  else NO_TAC);;

(* --- 3-block GHASH final-closure helpers/tactics, in the 5/6/7-block
   GCM_NB_GHASH_CLOSE framework (instantiated at N=3: 2 full + 1 partial).
   ct abbreviation is store-based (abbrev_ct_from_store), as in bands 5/6/7. --- *)

(* ============================================================              *)
(* NEW 5B-style 3-block GHASH closer (mirrors GCM_5B_* / N=4).               *)
(* N=3: 2 full blocks + 1 partial.                                           *)
(* ============================================================              *)

(* xi half-swap normalizers (defined inline; mirror XI_HS_LO_5/HI_5). *)
let XI_HS_LO_3 = prove
 (`word_subword (word_reversefields 8 (word_join (word_subword (xi:(128)word) (64,64):(64)word) (word_subword xi (0,64):(64)word):(128)word)) (0,64):(64)word =
   word_subword (word_reversefields 8 xi) (0,64)`,
  REWRITE_TAC[GSYM REV8_JOIN_FOLD; REVERSEFIELDS8_SUBWORD_LO; REVERSEFIELDS8_SUBWORD_HI] THEN
  CONV_TAC WORD_BLAST);;
let XI_HS_HI_3 = prove
 (`word_subword (word_reversefields 8 (word_join (word_subword (xi:(128)word) (64,64):(64)word) (word_subword xi (0,64):(64)word):(128)word)) (64,64):(64)word =
   word_subword (word_reversefields 8 xi) (64,64)`,
  REWRITE_TAC[GSYM REV8_JOIN_FOLD; REVERSEFIELDS8_SUBWORD_LO; REVERSEFIELDS8_SUBWORD_HI] THEN
  CONV_TAC WORD_BLAST);;

(* ct1 closer (counter = ivec, no inc) — mirror CT_CLOSE_5/CT_CLOSE_4. *)
let CT_CLOSE_3 nidx =
  let s13n = "s13_"^string_of_int nidx and ctn = "ct"^string_of_int nidx in
  EXPAND_TAC ctn THEN EXPAND_TAC s13n THEN
  REWRITE_TAC[AES256_ENCRYPT_UNFOLD; LET_DEF; LET_END_DEF; WORD_XOR_ASSOC] THEN ASM_REWRITE_TAC[];;

(* Step 1+2: establish the two full-block spec-form ct folds F1..F2 and fold
   them into the RHS ghash list — mirror GCM_5B_FOLD_SPEC_CTS (folds 4). *)
let GCM_3B_FOLD_SPEC_CTS : tactic =
  (* F1 *)
  SUBGOAL_THEN
   `word_xor pt1 (aes256_encrypt ivec [rk0;rk1;rk2;rk3;rk4;rk5;rk6;rk7;rk8;rk9;rk10;rk11;rk12;rk13;rk14]) = ct1`
   ASSUME_TAC THENL
   [EXPAND_TAC "ct1" THEN
    REWRITE_TAC[AES256_ENCRYPT_UNFOLD; LET_DEF; LET_END_DEF; WORD_XOR_ASSOC] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* F2 *)
  SUBGOAL_THEN
   `word_xor pt2 (aes256_encrypt (gcm_ctr_inc ivec) [rk0;rk1;rk2;rk3;rk4;rk5;rk6;rk7;rk8;rk9;rk10;rk11;rk12;rk13;rk14]) = ct2`
   ASSUME_TAC THENL
   [CONV_TAC SYM_CONV THEN GCM_3BLOCK_CT2_STEP_TAC; ALL_TAC] THEN
  (* fold the two full blocks into the RHS ghash list only. *)
  (fun (asl,w) ->
     let getf n = snd(find (fun (_,th) ->
       is_eq(concl th) && rand(concl th)=mk_var("ct"^string_of_int n,`:(128)word`) &&
       (let l=lhand(concl th) in
        (try fst(dest_const(rator(rator l)))="word_xor" with _->false) &&
        (try fst(dest_const(repeat rator (rand l)))="aes256_encrypt" with _->false))) asl) in
     GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [getf 1; getf 2] (asl,w));;

(* Step 3: b0-general mask-register collapse over the assumptions. *)
let GCM_3B_MASK_COLLAPSE_ASMS : tactic =
  SUBGOAL_THEN `1 <= (byte_len:num) /\ byte_len <= 16` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(fun bth -> if concl bth = `1 <= (byte_len:num) /\ byte_len <= 16` then
    RULE_ASSUM_TAC(REWRITE_RULE[GEN `b0:int128` (MP (SPEC_ALL THREEBLOCK_MASK_REG) bth)]) else NO_TAC);;

(* Step 5: bridge the machine block-3 keystream (collapsed +2 counter, baked
   into final_xi) to the spec ct3 — mirror GCM_5B_KS5_FOLD (+4) / KS4 (+3). *)
let GCM_3B_KS3_FOLD : tactic = fun (asl,w) ->
  let substr sub s =
    let ls=String.length s and lb=String.length sub in
    let rec go i = if i+lb>ls then false
                   else if String.sub s i lb = sub then true else go(i+1) in go 0 in
  let fxidef = snd(find (fun (_,th) ->
    is_eq(concl th) && (try rand(concl th)=`final_xi:(128)word` with _->false)) asl) in
  let body = lhs(concl fxidef) in
  let best = ref None in
  let rec walk t =
    (try let s=string_of_term t in
      if substr "pt3" s && substr "aese" s && substr "rk14" s &&
         (try fst(dest_const(repeat rator t))="word_xor" with _->false) &&
         (match !best with None->true | Some b -> String.length s < String.length(string_of_term b))
      then best := Some t
     with _->());
    (match t with Comb(a,b)->walk a; walk b | Abs(_,b)->walk b | _->()) in
  walk body;
  let ks3 = (match !best with Some t->t | None->failwith "KS3_FOLD: ks3 not found") in
  let bri = WORD_BLAST `word_bytereverse (word_bytereverse (x:(32)word)) = x` in
  let add2 = WORD_RULE `word_add (word_add (x:(32)word) (word 1)) (word 1) = word_add x (word 2)` in
  (SUBGOAL_THEN (mk_eq(ks3, `ct3:(128)word`)) ASSUME_TAC THENL
    [CONV_TAC SYM_CONV THEN EXPAND_TAC "ct3" THEN
     REWRITE_TAC[AES256_ENCRYPT_UNFOLD] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
     REWRITE_TAC[WORD_XOR_ASSOC] THEN
     AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
     REPEAT(AP_THM_TAC ORELSE AP_TERM_TAC) THEN
     REWRITE_TAC[gcm_ctr_inc] THEN
     REWRITE_TAC[WORD_REVERSEFIELDS_REVERSEFIELDS; WORD_REVERSEFIELDS_8_BYTEREVERSE_32] THEN
     REWRITE_TAC[INSERT_SUBWORD; INSERT_IDEM] THEN
     REWRITE_TAC[bri] THEN REWRITE_TAC[add2] THEN
     REWRITE_TAC[CTR_WORD_INSERT];
     ALL_TAC] THEN
   FIRST_ASSUM(fun th ->
     if is_eq(concl th) && rand(concl th)=`ct3:(128)word` &&
        (try fst(dest_const(repeat rator (lhs(concl th))))="word_xor" with _->false) &&
        String.length(string_of_term(lhs(concl th))) > 1000
     then RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th] else NO_TAC))
  (asl,w);;

(* Closer tail (ctm3 abbrev + h^3 norm + bridge + atomic ABBREVs + qS/qB),
   minus the final BINOP — mirror GCM_5B_TAIL_NOFINAL for N=3. *)
let GCM_3B_TAIL_NOFINAL : tactic =
  ABBREV_TAC `mask = word (2 EXP (8 * byte_len) - 1):(128)word` THEN
  ABBREV_TAC `ctm3 = word_and (ct3:(128)word) mask` THEN
  SUBGOAL_THEN `word_and (mask:(128)word) (ct3:(128)word) = ctm3`
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th]) THENL [
    EXPAND_TAC "ctm3" THEN CONV_TAC WORD_BITWISE_RULE; ALL_TAC ] THEN
  (* Normalize h^3 left-assoc -> symmetric (to match the 3-block bridge). *)
  SUBGOAL_THEN
    `polyval_dot (polyval_dot (h:int128) h) h = polyval_dot h (polyval_dot h h)`
    (fun th -> REWRITE_TAC[th]) THENL
    [REWRITE_TAC[polyval_dot] THEN REWRITE_TAC[WORD_PMUL_SYM]; ALL_TAC] THEN
  (* Apply 3-block bridge. *)
  MP_TAC(SPECL
    [`word_reversefields 8 (word_xor xi ct1):int128`;
     `word_reversefields 8 ct2:int128`; `word_reversefields 8 ctm3:int128`;
     `h:int128`; `h1k:int128`;
     `word_join (word 0:(64)word) (word_subword (h1k:(128)word) (64,64):(64)word):(128)word`;
     `h3k:int128`]
    GHASH_3BLOCK_KARATSUBA_EQ_POLYVAL_ACC) THEN
  SUBGOAL_THEN
    `word_subword (word_join (word 0:(64)word) (word_subword (h1k:(128)word) (64,64):(64)word):(128)word) (0,64):(64)word =
     karatsuba_mid (polyval_dot h h)`
    (fun th -> REWRITE_TAC[th]) THENL [
    SUBGOAL_THEN
      `word_subword (word_join (word 0:(64)word) (word_subword (h1k:(128)word) (64,64):(64)word):(128)word) (0,64):(64)word =
       word_subword (h1k:(128)word) (64,64):(64)word`
      (fun th -> REWRITE_TAC[th]) THENL [CONV_TAC WORD_BLAST; ASM_REWRITE_TAC[]]; ALL_TAC ] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN
  REWRITE_TAC[ghash_3block_karatsuba; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[SWAPHALVES128_SUBWORD_LO; SWAPHALVES128_SUBWORD_HI] THEN
  SUBGOAL_THEN
    `word_subword (word_join (word 0:(64)word) (karatsuba_mid (polyval_dot h h):(64)word):(128)word) (0,64):(64)word =
     karatsuba_mid (polyval_dot h h)`
    (fun th -> REWRITE_TAC[th]) THENL [CONV_TAC WORD_BLAST; ALL_TAC] THEN
  REWRITE_TAC[GSYM karatsuba_mid] THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
  CONV_TAC SYM_CONV THEN
  FIRST_ASSUM(fun th ->
    if is_eq(concl th) && rand(concl th) = `final_xi:(128)word` &&
       (try (let l = lhs(concl th) in is_comb l &&
             (let r = rator l in not(is_comb r && (try fst(dest_const(rator r)) = "read" with _ -> false))))
        with _ -> false)
    then SUBST1_TAC(SYM th) else NO_TAC) THEN
  REWRITE_TAC[REV64_LOWER_LANE; REV64_UPPER_LANE; REV8_JOIN_FOLD] THEN
  MATCH_MP_TAC(MESON[]
    `x = y ==> word_reversefields 8 x = word_reversefields 8 y:(128)word`) THEN
  REWRITE_TAC[WORD_SWAP_HALVES_INVOLUTION] THEN
  CONV_TAC(LAND_CONV(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
  REWRITE_TAC[WORD_INSERT_AS_JOIN_LO; WORD_INSERT_AS_JOIN_HI;
              KAR_SUBWORD_LEMMA; WORD_SWAP_HALVES_INVOLUTION;
              WORD_OR_REFL; WORD_XOR_ASSOC; WORD_SUBWORD_XOR;
              SWAPHALVES128_SUBWORD_LO; SWAPHALVES128_SUBWORD_HI] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[HALFSWAP_XOR; GSYM WORD_REVERSEFIELDS_XOR_8_128;
              WORD_XOR_0; WORD_XOR_ASSOC;
              REV8_JOIN_FOLD; REVERSEFIELDS8_SUBWORD_LO; REVERSEFIELDS8_SUBWORD_HI] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  CONV_TAC(TOP_DEPTH_CONV PMUL_NORM_CONV) THEN
  SUBGOAL_THEN
    `word_subword (word 0:(128)word) (0,64):(64)word = word 0 /\
     word_subword (word 0:(128)word) (64,64):(64)word = word 0`
    (fun th -> REWRITE_TAC[th]) THENL [CONJ_TAC THEN CONV_TAC WORD_BLAST; ALL_TAC] THEN
  REWRITE_TAC[WORD_XOR_0; WORD_XOR_0_LEFT] THEN
  REWRITE_TAC[karatsuba_mid; WORD_REVERSEFIELDS_XOR_8_128; WORD_SUBWORD_XOR] THEN
  (* 14 atomic ABBREVs (c1lo..c3hi, xi, hd..hf). *)
  ABBREV_TAC `(c1lo:(64)word) = word_subword (word_reversefields 8 (ct1:(128)word)) (0,64)` THEN
  ABBREV_TAC `(c1hi:(64)word) = word_subword (word_reversefields 8 (ct1:(128)word)) (64,64)` THEN
  ABBREV_TAC `(c2lo:(64)word) = word_subword (word_reversefields 8 (ct2:(128)word)) (0,64)` THEN
  ABBREV_TAC `(c2hi:(64)word) = word_subword (word_reversefields 8 (ct2:(128)word)) (64,64)` THEN
  ABBREV_TAC `(c3lo:(64)word) = word_subword (word_reversefields 8 (ctm3:(128)word)) (0,64)` THEN
  ABBREV_TAC `(c3hi:(64)word) = word_subword (word_reversefields 8 (ctm3:(128)word)) (64,64)` THEN
  ABBREV_TAC `(xilo:(64)word) = word_subword (word_reversefields 8 (xi:(128)word)) (0,64)` THEN
  ABBREV_TAC `(xihi:(64)word) = word_subword (word_reversefields 8 (xi:(128)word)) (64,64)` THEN
  ABBREV_TAC `(hd0:(64)word) = word_subword (h:(128)word) (0,64)` THEN
  ABBREV_TAC `(hd1:(64)word) = word_subword (h:(128)word) (64,64)` THEN
  ABBREV_TAC `(he0:(64)word) = word_subword ((polyval_dot h h):(128)word) (0,64)` THEN
  ABBREV_TAC `(he1:(64)word) = word_subword ((polyval_dot h h):(128)word) (64,64)` THEN
  ABBREV_TAC `(hf0:(64)word) = word_subword ((polyval_dot h (polyval_dot h h)):(128)word) (0,64)` THEN
  ABBREV_TAC `(hf1:(64)word) = word_subword ((polyval_dot h (polyval_dot h h)):(128)word) (64,64)` THEN
  ASM_REWRITE_TAC[] THEN
  (* 9 inner pmul ABBREVs (w1..w3). *)
  ABBREV_TAC `(w1lo:(128)word) = word_pmul (word_xor (xilo:(64)word) (c1lo:(64)word)) (hf0:(64)word)` THEN
  ABBREV_TAC `(w1hi:(128)word) = word_pmul (word_xor (xihi:(64)word) (c1hi:(64)word)) (hf1:(64)word)` THEN
  ABBREV_TAC `(w1md:(128)word) = word_pmul (word_xor (word_xor (xihi:(64)word) (c1hi:(64)word)) (word_xor (xilo:(64)word) (c1lo:(64)word))) (word_xor (hf0:(64)word) (hf1:(64)word))` THEN
  ABBREV_TAC `(w2lo:(128)word) = word_pmul (c2lo:(64)word) (he0:(64)word)` THEN
  ABBREV_TAC `(w2hi:(128)word) = word_pmul (c2hi:(64)word) (he1:(64)word)` THEN
  ABBREV_TAC `(w2md:(128)word) = word_pmul (word_xor (c2hi:(64)word) (c2lo:(64)word)) (word_xor (he0:(64)word) (he1:(64)word))` THEN
  ABBREV_TAC `(w3lo:(128)word) = word_pmul (c3lo:(64)word) (hd0:(64)word)` THEN
  ABBREV_TAC `(w3hi:(128)word) = word_pmul (c3hi:(64)word) (hd1:(64)word)` THEN
  ABBREV_TAC `(w3md:(128)word) = word_pmul (word_xor (c3hi:(64)word) (c3lo:(64)word)) (word_xor (hd0:(64)word) (hd1:(64)word))` THEN
  REWRITE_TAC[DOUBLE_SUBWORD_JOIN; DOUBLE_SUBWORD_JOIN_HI; WORD_SUBWORD_XOR] THEN
  SUBGOAL_THEN
    `word_pmul (word_xor (xihi:(64)word) (word_xor (c1hi:(64)word) (word_xor (xilo:(64)word) (c1lo:(64)word)))) (word_xor (hf0:(64)word) (hf1:(64)word)):(128)word = w1md`
    (fun th -> REWRITE_TAC[th]) THENL
    [EXPAND_TAC "w1md" THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  (* 18 z-vars. *)
  ABBREV_TAC `(w1lo_l:(64)word) = word_subword (w1lo:(128)word) (0,64)` THEN
  ABBREV_TAC `(w1lo_h:(64)word) = word_subword (w1lo:(128)word) (64,64)` THEN
  ABBREV_TAC `(w1hi_l:(64)word) = word_subword (w1hi:(128)word) (0,64)` THEN
  ABBREV_TAC `(w1hi_h:(64)word) = word_subword (w1hi:(128)word) (64,64)` THEN
  ABBREV_TAC `(w1md_l:(64)word) = word_subword (w1md:(128)word) (0,64)` THEN
  ABBREV_TAC `(w1md_h:(64)word) = word_subword (w1md:(128)word) (64,64)` THEN
  ABBREV_TAC `(w2lo_l:(64)word) = word_subword (w2lo:(128)word) (0,64)` THEN
  ABBREV_TAC `(w2lo_h:(64)word) = word_subword (w2lo:(128)word) (64,64)` THEN
  ABBREV_TAC `(w2hi_l:(64)word) = word_subword (w2hi:(128)word) (0,64)` THEN
  ABBREV_TAC `(w2hi_h:(64)word) = word_subword (w2hi:(128)word) (64,64)` THEN
  ABBREV_TAC `(w2md_l:(64)word) = word_subword (w2md:(128)word) (0,64)` THEN
  ABBREV_TAC `(w2md_h:(64)word) = word_subword (w2md:(128)word) (64,64)` THEN
  ABBREV_TAC `(w3lo_l:(64)word) = word_subword (w3lo:(128)word) (0,64)` THEN
  ABBREV_TAC `(w3lo_h:(64)word) = word_subword (w3lo:(128)word) (64,64)` THEN
  ABBREV_TAC `(w3hi_l:(64)word) = word_subword (w3hi:(128)word) (0,64)` THEN
  ABBREV_TAC `(w3hi_h:(64)word) = word_subword (w3hi:(128)word) (64,64)` THEN
  ABBREV_TAC `(w3md_l:(64)word) = word_subword (w3md:(128)word) (0,64)` THEN
  ABBREV_TAC `(w3md_h:(64)word) = word_subword (w3md:(128)word) (64,64)` THEN
  ASM_REWRITE_TAC[] THEN
  (* Normalize LHS mid-pmuls to abbreviated w?md (swapped xor arg order). *)
  SUBGOAL_THEN `word_pmul (word_xor (c2lo:(64)word) (c2hi:(64)word)) (word_xor (he0:(64)word) (he1:(64)word)):(128)word = w2md`
    (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "w2md" THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  SUBGOAL_THEN `word_pmul (word_xor (c3lo:(64)word) (c3hi:(64)word)) (word_xor (hd0:(64)word) (hd1:(64)word)):(128)word = w3md`
    (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "w3md" THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  SUBGOAL_THEN `word_pmul (word_xor (xilo:(64)word) (word_xor (c1lo:(64)word) (word_xor (xihi:(64)word) (c1hi:(64)word)))) (word_xor (hf0:(64)word) (hf1:(64)word)):(128)word = w1md`
    (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "w1md" THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  (* qS: small Barrett pmul; fold both XOR orderings. *)
  ABBREV_TAC `(qS:(128)word) = word_pmul (word_xor (w3lo_l:(64)word) (word_xor w2lo_l (w1lo_l))) (word 13979173243358019584:(64)word)` THEN
  SUBGOAL_THEN `word_pmul (word_xor (w1lo_l:(64)word) (word_xor w2lo_l (w3lo_l))) (word 13979173243358019584:(64)word):(128)word = qS`
    (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "qS" THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  (* qB: big Barrett pmul; fold the LHS-order copy via bubble_sort_conv. *)
  ABBREV_TAC `(qB:(128)word) = word_pmul
    (word_xor (w3md_l:(64)word) (word_xor w2md_l (word_xor w1md_l (word_xor w3lo_l (word_xor w2lo_l (word_xor w1lo_l (word_xor w3hi_l (word_xor w2hi_l (word_xor w1hi_l (word_xor (word_subword (qS:(128)word) (0,64)) (word_xor w3lo_h (word_xor w2lo_h (w1lo_h))))))))))))) (word 13979173243358019584:(64)word)` THEN
  SUBGOAL_THEN
    `word_pmul (word_xor (w1lo_h:(64)word) (word_xor w2lo_h (word_xor w3lo_h (word_xor w1md_l (word_xor w2md_l (word_xor w3md_l (word_xor w1hi_l (word_xor w2hi_l (word_xor w3hi_l (word_xor w1lo_l (word_xor w2lo_l (word_xor w3lo_l ((word_subword (qS:(128)word) (0,64))))))))))))))) (word 13979173243358019584:(64)word):(128)word = qB`
    (fun th -> REWRITE_TAC[th]) THENL
    [EXPAND_TAC "qB" THEN AP_THM_TAC THEN AP_TERM_TAC THEN
     CONV_TAC(BINOP_CONV bubble_sort_conv) THEN REFL_TAC; ALL_TAC];;

(* per-half XOR-AC closer — mirror GCM_5B_HALF_CLOSE (3 mids, qS 3, qB 13). *)
let GCM_3B_FOLD_MIDS_TAC : tactic =
  fun (asl,gg) ->
    let rec finds hd t acc = match t with
      | Comb(Comb(Const("word_pmul",_),a),x) when x = hd ->
          a :: (finds hd a (finds hd x acc))
      | Comb(l,r) -> finds hd l (finds hd r acc)
      | Abs(_,b) -> finds hd b acc | _ -> acc in
    let hfw = `word_xor (hf0:(64)word) hf1`
    and hew = `word_xor (he0:(64)word) he1`
    and hdw = `word_xor (hd0:(64)word) hd1` in
    let mk tgt hd arg =
      SUBGOAL_THEN
        (mk_eq(list_mk_comb(`word_pmul:(64)word->(64)word->(128)word`,[arg;hd]),tgt))
        (fun th -> REWRITE_TAC[th]) THENL
       [EXPAND_TAC (fst(dest_var tgt)) THEN AP_THM_TAC THEN AP_TERM_TAC THEN
        CONV_TAC WORD_RULE; ALL_TAC] in
    (EVERY ((map (mk `w1md:(128)word` hfw) (setify(finds hfw gg [])))
          @ (map (mk `w2md:(128)word` hew) (setify(finds hew gg [])))
          @ (map (mk `w3md:(128)word` hdw) (setify(finds hdw gg []))))) (asl,gg);;

let GCM_3B_FOLD_TO tgt natoms : tactic =
  let w64 = `word 13979173243358019584:(64)word` in
  fun (asl,gg) ->
    let rec finds t acc = match t with
      | Comb(Comb(Const("word_pmul",_),a),x) when x = w64 ->
          a :: (finds a (finds x acc))
      | Comb(l,r) -> finds l (finds r acc) | Abs(_,b) -> finds b acc | _ -> acc in
    let rec at t = match t with
      | Comb(Comb(Const("word_xor",_),x),y) -> at x @ at y | _ -> [t] in
    let args = List.filter (fun a -> List.length(at a) = natoms) (setify(finds gg [])) in
    (EVERY (map (fun a ->
       FIRST [SUBGOAL_THEN
                (mk_eq(list_mk_comb(`word_pmul:(64)word->(64)word->(128)word`,[a;w64]),tgt))
                (fun th -> REWRITE_TAC[th]) THENL
               [EXPAND_TAC (fst(dest_var tgt)) THEN AP_THM_TAC THEN AP_TERM_TAC THEN
                CONV_TAC(BINOP_CONV bubble_fix) THEN REFL_TAC; ALL_TAC];
              ALL_TAC]) args)) (asl,gg);;

let GCM_3B_HALF_CLOSE : tactic =
  GCM_3B_FOLD_MIDS_TAC THEN ASM_REWRITE_TAC[] THEN
  GCM_3B_FOLD_TO `qS:(128)word` 3 THEN ASM_REWRITE_TAC[] THEN
  GCM_3B_FOLD_TO `qB:(128)word` 13 THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(BINOP_CONV bubble_fix) THEN REFL_TAC;;

(* The full GHASH closer — mirror GCM_5B_GHASH_CLOSE. *)
let GCM_3B_GHASH_CLOSE : tactic =
  GCM_3B_FOLD_SPEC_CTS THEN
  REWRITE_TAC[GHASH_POLYVAL_ACC_3; POLYVAL_DOT_H3_EQ; GSYM WORD_REVERSEFIELDS_XOR_8_128] THEN
  GCM_3B_MASK_COLLAPSE_ASMS THEN
  GCM_3B_KS3_FOLD THEN
  GCM_3B_TAIL_NOFINAL THEN
  REWRITE_TAC[XI_HS_LO_3; XI_HS_HI_3] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `word_pmul (word_xor (xihi:(64)word) (word_xor c1hi (word_xor xilo c1lo)))
              (word_xor (hf0:(64)word) hf1):(128)word = w1md`
   (fun th -> REWRITE_TAC[th]) THENL
   [EXPAND_TAC "w1md" THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  BINOP_TAC THENL [GCM_3B_HALF_CLOSE; GCM_3B_HALF_CLOSE];;

(* masked-ct3 store conjunct closer — mirror GCM_5B_MASKED_CT5_CLOSE (+2). *)
let GCM_3B_MASKED_CT3_CLOSE : tactic =
  let bri = WORD_BLAST `word_bytereverse (word_bytereverse (x:(32)word)) = x` in
  let add2 = WORD_RULE `word_add (word_add (x:(32)word) (word 1)) (word 1) = word_add x (word 2)` in
  SUBGOAL_THEN `1 <= byte_len /\ byte_len <= 16` MP_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP THREEBLOCK_MASK_REG th]) THEN
  REWRITE_TAC[NBLOCK_MASK_IDEM] THEN
  MATCH_MP_TAC(MESON[] `x = y ==> word_or (word_and x m) r = word_or (word_and y m) r:(128)word`) THEN
  CONV_TAC SYM_CONV THEN REWRITE_TAC[AES256_ENCRYPT_UNFOLD] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[WORD_XOR_ASSOC] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REPEAT(AP_THM_TAC ORELSE AP_TERM_TAC) THEN
  REWRITE_TAC[gcm_ctr_inc] THEN
  REWRITE_TAC[WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
  REWRITE_TAC[WORD_REVERSEFIELDS_8_BYTEREVERSE_32] THEN
  REWRITE_TAC[INSERT_SUBWORD; INSERT_IDEM] THEN
  REWRITE_TAC[bri] THEN REWRITE_TAC[add2] THEN
  REWRITE_TAC[CTR_WORD_INSERT];;

(* Named goal for the 3BLOCK band (shared spec lifted by the ABS layer). *)
let gcm_3b_goal =
 `!in_ptr out_ptr xi_ptr ivec_ptr key_ptr htable_ptr
    (pt1:(128)word) (pt2:(128)word) (pt3:(128)word) (out0:(128)word) (ivec:(128)word)
    (rk0:(128)word) (rk1:(128)word) (rk2:(128)word) (rk3:(128)word)
    (rk4:(128)word) (rk5:(128)word) (rk6:(128)word) (rk7:(128)word)
    (rk8:(128)word) (rk9:(128)word) (rk10:(128)word) (rk11:(128)word)
    (rk12:(128)word) (rk13:(128)word) (rk14:(128)word)
    (xi:(128)word) (h:(128)word) (h1k:(128)word) (h3k:(128)word)
    byte_len stackptr pc.
    1 <= byte_len /\ byte_len <= 16 /\
    aligned 16 stackptr /\
    nonoverlapping (word pc,4600) (in_ptr:int64,48) /\
    nonoverlapping (word pc,4600) (out_ptr:int64,48) /\
    nonoverlapping (word pc,4600) (xi_ptr:int64,16) /\
    nonoverlapping (word pc,4600) (ivec_ptr:int64,16) /\
    nonoverlapping (word pc,4600) (key_ptr:int64,240) /\
    nonoverlapping (word pc,4600) (htable_ptr:int64,256) /\
    nonoverlapping (word pc,4600) (stackptr:int64,80) /\
    nonoverlapping (in_ptr,48) (out_ptr,48) /\
    nonoverlapping (in_ptr,48) (xi_ptr,16) /\
    nonoverlapping (in_ptr,48) (ivec_ptr,16) /\
    nonoverlapping (out_ptr,48) (xi_ptr,16) /\
    nonoverlapping (out_ptr,48) (ivec_ptr,16) /\
    nonoverlapping (xi_ptr,16) (ivec_ptr,16) /\
    nonoverlapping (key_ptr,240) (out_ptr,48) /\
    nonoverlapping (key_ptr,240) (xi_ptr,16) /\
    nonoverlapping (key_ptr,240) (ivec_ptr,16) /\
    nonoverlapping (htable_ptr,256) (out_ptr,48) /\
    nonoverlapping (htable_ptr,256) (xi_ptr,16) /\
    nonoverlapping (htable_ptr,256) (ivec_ptr,16) /\
    nonoverlapping (stackptr,80) (out_ptr,48) /\
    nonoverlapping (stackptr,80) (xi_ptr,16) /\
    nonoverlapping (stackptr,80) (ivec_ptr,16) /\
    nonoverlapping (stackptr,80) (in_ptr,48) /\
    nonoverlapping (stackptr,80) (key_ptr,240) /\
    nonoverlapping (stackptr,80) (htable_ptr,256) /\
    nonoverlapping (ivec_ptr,16) (word pc,4600) /\
    nonoverlapping (xi_ptr,16) (word pc,4600) /\
    nonoverlapping (out_ptr,48) (word pc,4600)
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) aes256_gcm_mc /\
           read PC s = word pc /\
           C_ARGUMENTS [in_ptr; word (256 + 8 * byte_len); out_ptr; xi_ptr;
                        ivec_ptr; key_ptr; htable_ptr] s /\
           read SP s = word_add stackptr (word 80) /\
           read (memory :> bytes128 in_ptr) s = pt1 /\
           read (memory :> bytes128 (word_add in_ptr (word 16))) s = pt2 /\
           read (memory :> bytes128 (word_add in_ptr (word 32))) s = pt3 /\
           read (memory :> bytes128 (word_add out_ptr (word 32))) s = out0 /\
           read (memory :> bytes128 ivec_ptr) s = ivec /\
           read (memory :> bytes128 (word_add key_ptr (word 0))) s = rk0 /\
           read (memory :> bytes128 (word_add key_ptr (word 16))) s = rk1 /\
           read (memory :> bytes128 (word_add key_ptr (word 32))) s = rk2 /\
           read (memory :> bytes128 (word_add key_ptr (word 48))) s = rk3 /\
           read (memory :> bytes128 (word_add key_ptr (word 64))) s = rk4 /\
           read (memory :> bytes128 (word_add key_ptr (word 80))) s = rk5 /\
           read (memory :> bytes128 (word_add key_ptr (word 96))) s = rk6 /\
           read (memory :> bytes128 (word_add key_ptr (word 112))) s = rk7 /\
           read (memory :> bytes128 (word_add key_ptr (word 128))) s = rk8 /\
           read (memory :> bytes128 (word_add key_ptr (word 144))) s = rk9 /\
           read (memory :> bytes128 (word_add key_ptr (word 160))) s = rk10 /\
           read (memory :> bytes128 (word_add key_ptr (word 176))) s = rk11 /\
           read (memory :> bytes128 (word_add key_ptr (word 192))) s = rk12 /\
           read (memory :> bytes128 (word_add key_ptr (word 208))) s = rk13 /\
           read (memory :> bytes128 (word_add key_ptr (word 224))) s = rk14 /\
           read (memory :> bytes128 xi_ptr) s = xi /\
           read (memory :> bytes128 htable_ptr) s = word_swaphalves128 h /\
           read (memory :> bytes128 (word_add htable_ptr (word 16))) s = h1k /\
           read (memory :> bytes128 (word_add htable_ptr (word 32))) s =
             word_swaphalves128 (polyval_dot h h) /\
           read (memory :> bytes128 (word_add htable_ptr (word 48))) s =
             word_swaphalves128 (polyval_dot h (polyval_dot h h)) /\
           read (memory :> bytes128 (word_add htable_ptr (word 64))) s = h3k /\
           word_subword h1k (0,64):(64)word = karatsuba_mid h /\
           word_subword h1k (64,64):(64)word = karatsuba_mid (polyval_dot h h) /\
           word_subword h3k (0,64):(64)word =
             karatsuba_mid (polyval_dot h (polyval_dot h h)))
      (\s. let ct1 =
             word_xor pt1
               (aes256_encrypt ivec [rk0;rk1;rk2;rk3;rk4;rk5;rk6;rk7;rk8;rk9;rk10;rk11;rk12;rk13;rk14]) in
           let ct2 =
             word_xor pt2
               (aes256_encrypt (gcm_ctr_inc ivec) [rk0;rk1;rk2;rk3;rk4;rk5;rk6;rk7;rk8;rk9;rk10;rk11;rk12;rk13;rk14]) in
           let ct3 =
             word_xor pt3
               (aes256_encrypt (gcm_ctr_inc (gcm_ctr_inc ivec)) [rk0;rk1;rk2;rk3;rk4;rk5;rk6;rk7;rk8;rk9;rk10;rk11;rk12;rk13;rk14]) in
           let mask = word (2 EXP (8 * byte_len) - 1):(128)word in
           let ctm3 = word_and ct3 mask in
           read PC s = word(pc + 4588) /\
           read X0 s = word (32 + byte_len) /\
           read (memory :> bytes128 out_ptr) s = ct1 /\
           read (memory :> bytes128 (word_add out_ptr (word 16))) s = ct2 /\
           read (memory :> bytes128 (word_add out_ptr (word 32))) s =
             word_or ctm3 (word_and out0 (word_not mask)) /\
           read (memory :> bytes128 xi_ptr) s =
             word_reversefields 8
               (ghash_polyval_acc h (word_reversefields 8 xi)
                                    [word_reversefields 8 ct1;
                                     word_reversefields 8 ct2;
                                     word_reversefields 8 ctm3]))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [memory :> bytes(out_ptr,48);
                  memory :> bytes(xi_ptr,16);
                  memory :> bytes(ivec_ptr,16)] ,,
       MAYCHANGE [SP] ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes64 stackptr;
                  memory :> bytes64 (word_add stackptr (word 8));
                  memory :> bytes64 (word_add stackptr (word 16));
                  memory :> bytes64 (word_add stackptr (word 24));
                  memory :> bytes64 (word_add stackptr (word 32));
                  memory :> bytes64 (word_add stackptr (word 40));
                  memory :> bytes64 (word_add stackptr (word 48));
                  memory :> bytes64 (word_add stackptr (word 56));
                  memory :> bytes64 (word_add stackptr (word 64));
                  memory :> bytes64 (word_add stackptr (word 72))])`;;

let AES256_GCM_ENCRYPT_LT_3BLOCK_CONCRETE = prove
 (gcm_3b_goal,
  (* ---- symbolic simulation (store-based ct abbreviation) ---- *)
  GCM_INIT_TAC GCM_CBZ_LEMMA3 THEN GCM_PROLOGUE_TAC THEN GCM_RUN 20 263 THEN
  GCM_INLOOP_GUARD_TAC GCM_X5_LEMMA3 THEN GCM_RUN 267 272 THEN
  GCM_BND16 GCM_X5TAIL_LEMMA3 THEN
  GCM_RUN_THEN GCM_CASCADE3_TAC 273 321 THEN
  GCM_RUN 322 346 THEN abbrev_ct_from_store 0 1 THEN abbrev_ct_from_store 16 2 THEN
  GCM_RUN 347 366 THEN
  SUBGOAL_THEN `1 <= byte_len /\ byte_len <= 16` MP_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP THREEBLOCK_MASK_REG th])) THEN
  GCM_RUN 367 374 THEN
  GCM_RUN 375 385 THEN
  GCM_NBLOCK_POST_SIM_NORMALIZE_TAC THEN ABBREV_FINAL_XI_TAC THEN
  ARM_STEPS_TAC AES256_GCM_EXEC (386--392) THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ENSURES_FINAL_STATE_TAC THEN
  SUBGOAL_THEN `1 <= byte_len /\ byte_len <= 16` MP_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP THREEBLOCK_MASK_REG th]) THEN
  ASM_SIMP_TAC[THREEBLOCK_USHR] THEN
  (* ---- four conjuncts: ct1, ct2, masked-ct3, GHASH ---- *)
  CONJ_TAC THENL [CT_CLOSE_3 1; ALL_TAC] THEN
  CONJ_TAC THENL [CONV_TAC SYM_CONV THEN GCM_3BLOCK_CT2_STEP_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [GCM_3B_MASKED_CT3_CLOSE; ALL_TAC] THEN
  (* ---- ct3 abbreviation (spec form) so the closer's ctm3 works ---- *)
  ABBREV_TAC `ct3 = word_xor pt3
    (aes256_encrypt (gcm_ctr_inc (gcm_ctr_inc ivec)) [rk0;rk1;rk2;rk3;rk4;rk5;rk6;rk7;rk8;rk9;rk10;rk11;rk12;rk13;rk14]):(128)word` THEN
  (* ---- GHASH conjunct ---- *)
  GCM_3B_GHASH_CLOSE);;

(* ========================================================================= *)
(* The L256_enc_blocks_more_than_3 branch (4-block: three full blocks +      *)
(* partial block 4, total 49..64 bytes) of the single binary, proved as a    *)
(* standalone theorem and applied exactly as the XTS length-band lemmas are. *)
(* Reuses the four-block masked closers from gcm_four_block_closers.ml.      *)
(* ========================================================================= *)

needs "arm/proofs/utils/gcm_four_block_closers.ml";;

(* --- 4-block-branch length/cascade helpers (thresholds over 48+byte_len) --- *)

let GCM_CBZ_LEMMA4 = prove
 (`1 <= byte_len /\ byte_len <= 16 ==> ~(val(word(384+8*byte_len):int64) = 0)`,
  STRIP_TAC THEN SUBGOAL_THEN `val(word(384+8*byte_len):int64) = 384+8*byte_len` SUBST1_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC;
    ASM_ARITH_TAC]);;

let GCM_WSUB4 = prove
 (`byte_len <= 16 ==> word_sub (word (48+byte_len):int64) (word 1) = word (47 + byte_len)`,
  CONV_TAC WORD_RULE);;

let GCM_X5_LEMMA4 = prove
 (`1 <= byte_len /\ byte_len <= 16 ==>
   word_add (word_and (word_sub (word_ushr (word (384+8*byte_len):int64) 3) (word 1))
                      (word 18446744073709551488)) in_ptr = in_ptr`,
  STRIP_TAC THEN
  SUBGOAL_THEN `word_ushr (word (384+8*byte_len):int64) 3 = word (48+byte_len)` SUBST1_TAC THENL
   [ASM_SIMP_TAC[FOURBLOCK_USHR]; ALL_TAC] THEN
  ASM_SIMP_TAC[GCM_WSUB4] THEN
  SUBGOAL_THEN `word_and (word (47+byte_len):int64) (word 18446744073709551488) = word 0` SUBST1_TAC THENL
   [MATCH_MP_TAC GCM_ANDMASK0 THEN ASM_ARITH_TAC; ALL_TAC] THEN
  CONV_TAC WORD_RULE);;

let GCM_X5TAIL_LEMMA4 = prove
 (`byte_len <= 16 ==>
   word_sub (word_add in_ptr (word_ushr (word (384+8*byte_len):int64) 3)) in_ptr = word (48+byte_len)`,
  ASM_SIMP_TAC[FOURBLOCK_USHR] THEN CONV_TAC WORD_RULE);;

let GCM_CASC4_FALSE = prove
 (`!byte_len t. byte_len <= 16 /\ 64 <= t /\ t <= 112 ==>
    ((~(val (word_sub (word (48+byte_len):int64) (word t)) = 0) /\
      (ival (word_sub (word (48+byte_len):int64) (word t)) < &0 <=>
       ~(ival (word (48+byte_len):int64) - &t = ival (word_sub (word (48+byte_len):int64) (word t)))))
     <=> F)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `ival(word (48+byte_len):int64) = &(48+byte_len)` ASSUME_TAC THENL
   [MATCH_MP_TAC NBLOCK_IVAL_WORD_SMALL THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `word_sub (word (48+byte_len):int64) (word t) = iword(&(48+byte_len) - &t)` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM IWORD_INT_SUB; WORD_IWORD]; ALL_TAC] THEN
  SUBGOAL_THEN `ival(iword(&(48+byte_len) - &t):int64) = &(48+byte_len) - &t` ASSUME_TAC THENL
   [MATCH_MP_TAC IVAL_IWORD THEN REWRITE_TAC[DIMINDEX_64] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_SUB_CONV) THEN
    SUBGOAL_THEN `&(48+byte_len):int <= &64 /\ &64:int <= &t /\ &t:int <= &112` MP_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN INT_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[VAL_EQ_0; GSYM IVAL_EQ_0] THEN
  SUBGOAL_THEN `&(48+byte_len):int <= &64 /\ &64:int <= &t` MP_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN INT_ARITH_TAC);;

let GCM_CASC4_TRUE = prove
 (`1 <= byte_len /\ byte_len <= 16 ==>
    ((~(val (word_sub (word (48+byte_len):int64) (word 48)) = 0) /\
      (ival (word_sub (word (48+byte_len):int64) (word 48)) < &0 <=>
       ~(ival (word (48+byte_len):int64) - &48 = ival (word_sub (word (48+byte_len):int64) (word 48)))))
     <=> T)`,
  STRIP_TAC THEN
  SUBGOAL_THEN `ival(word (48+byte_len):int64) = &(48+byte_len)` ASSUME_TAC THENL
   [MATCH_MP_TAC NBLOCK_IVAL_WORD_SMALL THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `word_sub (word (48+byte_len):int64) (word 48) = iword(&(48+byte_len) - &48)` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM IWORD_INT_SUB; WORD_IWORD]; ALL_TAC] THEN
  SUBGOAL_THEN `ival(iword(&(48+byte_len) - &48):int64) = &(48+byte_len) - &48` ASSUME_TAC THENL
   [MATCH_MP_TAC IVAL_IWORD THEN REWRITE_TAC[DIMINDEX_64] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_SUB_CONV) THEN
    SUBGOAL_THEN `&(48+byte_len):int <= &64` MP_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN INT_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[VAL_EQ_0; GSYM IVAL_EQ_0] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_ADD] THEN
  SUBGOAL_THEN `&1:int <= &byte_len` MP_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN INT_ARITH_TAC);;

let GCM_CASCADE4_TAC : tactic =
  FIRST_X_ASSUM(fun bl16 -> if concl bl16 = `byte_len <= 16` then
    FIRST_X_ASSUM(fun bl1 -> if concl bl1 = `1 <= byte_len` then
      RULE_ASSUM_TAC(REWRITE_RULE(
        (map (fun t -> MATCH_MP GCM_CASC4_FALSE (CONJ bl16
                (CONJ (ARITH_RULE(vsubst[mk_numeral(num_of_int t),`t:num`] `64 <= t`))
                      (ARITH_RULE(vsubst[mk_numeral(num_of_int t),`t:num`] `t <= 112`)))))
             [64;80;96;112]) @
        [MATCH_MP GCM_CASC4_TRUE (CONJ bl1 bl16); COND_CLAUSES])) THEN
      ASSUME_TAC bl1 THEN ASSUME_TAC bl16
    else NO_TAC)
  else NO_TAC);;

(* --- 4-block GHASH final-closure helpers/tactics, in the 5/6/7-block
   GCM_NB_GHASH_CLOSE framework (instantiated at N=4: 3 full + 1 partial). --- *)

(* GHASH-closure helper lemmas (xi half-swap normalization). *)
let XI_HS_LO = prove
 (`word_subword (word_reversefields 8 (word_join (word_subword (xi:(128)word) (64,64):(64)word) (word_subword xi (0,64):(64)word):(128)word)) (0,64):(64)word =
   word_subword (word_reversefields 8 xi) (0,64)`,
  REWRITE_TAC[GSYM REV8_JOIN_FOLD; REVERSEFIELDS8_SUBWORD_LO; REVERSEFIELDS8_SUBWORD_HI] THEN
  CONV_TAC WORD_BLAST);;
let XI_HS_HI = prove
 (`word_subword (word_reversefields 8 (word_join (word_subword (xi:(128)word) (64,64):(64)word) (word_subword xi (0,64):(64)word):(128)word)) (64,64):(64)word =
   word_subword (word_reversefields 8 xi) (64,64)`,
  REWRITE_TAC[GSYM REV8_JOIN_FOLD; REVERSEFIELDS8_SUBWORD_LO; REVERSEFIELDS8_SUBWORD_HI] THEN
  CONV_TAC WORD_BLAST);;

(* ============================================================              *)
(* 4-block GHASH closer (mirrors GCM_5B_* exactly).                          *)
(* ============================================================              *)

(* xi half-swap normalizers (same as XI_HS_LO/HI). *)
let XI_HS_LO_4 = XI_HS_LO;;
let XI_HS_HI_4 = XI_HS_HI;;

(* ct1 closer (counter = ivec, no inc) — mirror CT_CLOSE_5. *)
let CT_CLOSE_4 nidx =
  let s13n = "s13_"^string_of_int nidx and ctn = "ct"^string_of_int nidx in
  EXPAND_TAC ctn THEN EXPAND_TAC s13n THEN
  REWRITE_TAC[AES256_ENCRYPT_UNFOLD; LET_DEF; LET_END_DEF; WORD_XOR_ASSOC] THEN ASM_REWRITE_TAC[];;

(* Step 1+2: establish the three full-block spec-form ct folds F1..F3 and fold
   them into the RHS ghash list — mirror GCM_5B_FOLD_SPEC_CTS (which folds 4). *)
let GCM_4B_FOLD_SPEC_CTS : tactic =
  (* F1 *)
  SUBGOAL_THEN
   `word_xor pt1 (aes256_encrypt ivec [rk0;rk1;rk2;rk3;rk4;rk5;rk6;rk7;rk8;rk9;rk10;rk11;rk12;rk13;rk14]) = ct1`
   ASSUME_TAC THENL
   [EXPAND_TAC "ct1" THEN
    REWRITE_TAC[AES256_ENCRYPT_UNFOLD; LET_DEF; LET_END_DEF; WORD_XOR_ASSOC] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* F2 *)
  SUBGOAL_THEN
   `word_xor pt2 (aes256_encrypt (gcm_ctr_inc ivec) [rk0;rk1;rk2;rk3;rk4;rk5;rk6;rk7;rk8;rk9;rk10;rk11;rk12;rk13;rk14]) = ct2`
   ASSUME_TAC THENL
   [CONV_TAC SYM_CONV THEN GCM_4BLOCK_CT2_STEP_TAC; ALL_TAC] THEN
  (* F3 *)
  SUBGOAL_THEN
   `word_xor pt3 (aes256_encrypt (gcm_ctr_inc (gcm_ctr_inc ivec)) [rk0;rk1;rk2;rk3;rk4;rk5;rk6;rk7;rk8;rk9;rk10;rk11;rk12;rk13;rk14]) = ct3`
   ASSUME_TAC THENL
   [CONV_TAC SYM_CONV THEN GCM_4BLOCK_CT3_STEP_TAC; ALL_TAC] THEN
  (* fold the three full blocks into the RHS ghash list only. *)
  (fun (asl,w) ->
     let getf n = snd(find (fun (_,th) ->
       is_eq(concl th) && rand(concl th)=mk_var("ct"^string_of_int n,`:(128)word`) &&
       (let l=lhand(concl th) in
        (try fst(dest_const(rator(rator l)))="word_xor" with _->false) &&
        (try fst(dest_const(repeat rator (rand l)))="aes256_encrypt" with _->false))) asl) in
     GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [getf 1; getf 2; getf 3] (asl,w));;

(* Step 3: b0-general mask-register collapse over the assumptions. *)
let GCM_4B_MASK_COLLAPSE_ASMS : tactic =
  SUBGOAL_THEN `1 <= (byte_len:num) /\ byte_len <= 16` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(fun bth -> if concl bth = `1 <= (byte_len:num) /\ byte_len <= 16` then
    RULE_ASSUM_TAC(REWRITE_RULE[GEN `b0:int128` (MP (SPEC_ALL FOURBLOCK_MASK_REG) bth)]) else NO_TAC);;

(* Step 5: bridge the machine block-4 keystream (collapsed +3 counter, baked
   into final_xi) to the spec ct4 — mirror GCM_5B_KS5_FOLD (+4). *)
let GCM_4B_KS4_FOLD : tactic = fun (asl,w) ->
  let substr sub s =
    let ls=String.length s and lb=String.length sub in
    let rec go i = if i+lb>ls then false
                   else if String.sub s i lb = sub then true else go(i+1) in go 0 in
  let fxidef = snd(find (fun (_,th) ->
    is_eq(concl th) && (try rand(concl th)=`final_xi:(128)word` with _->false)) asl) in
  let body = lhs(concl fxidef) in
  let best = ref None in
  let rec walk t =
    (try let s=string_of_term t in
      if substr "pt4" s && substr "aese" s && substr "rk14" s &&
         (try fst(dest_const(repeat rator t))="word_xor" with _->false) &&
         (match !best with None->true | Some b -> String.length s < String.length(string_of_term b))
      then best := Some t
     with _->());
    (match t with Comb(a,b)->walk a; walk b | Abs(_,b)->walk b | _->()) in
  walk body;
  let ks4 = (match !best with Some t->t | None->failwith "KS4_FOLD: ks4 not found") in
  let bri = WORD_BLAST `word_bytereverse (word_bytereverse (x:(32)word)) = x` in
  let add3 = WORD_RULE `word_add (word_add (word_add (x:(32)word) (word 1)) (word 1)) (word 1) = word_add x (word 3)` in
  (SUBGOAL_THEN (mk_eq(ks4, `ct4:(128)word`)) ASSUME_TAC THENL
    [CONV_TAC SYM_CONV THEN EXPAND_TAC "ct4" THEN
     REWRITE_TAC[AES256_ENCRYPT_UNFOLD] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
     REWRITE_TAC[WORD_XOR_ASSOC] THEN
     AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
     REPEAT(AP_THM_TAC ORELSE AP_TERM_TAC) THEN
     REWRITE_TAC[gcm_ctr_inc] THEN
     REWRITE_TAC[WORD_REVERSEFIELDS_REVERSEFIELDS; WORD_REVERSEFIELDS_8_BYTEREVERSE_32] THEN
     REWRITE_TAC[INSERT_SUBWORD; INSERT_IDEM] THEN
     REWRITE_TAC[bri] THEN REWRITE_TAC[add3] THEN
     REWRITE_TAC[CTR_WORD_INSERT];
     ALL_TAC] THEN
   FIRST_ASSUM(fun th ->
     if is_eq(concl th) && rand(concl th)=`ct4:(128)word` &&
        (try fst(dest_const(repeat rator (lhs(concl th))))="word_xor" with _->false) &&
        String.length(string_of_term(lhs(concl th))) > 1000
     then RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th] else NO_TAC))
  (asl,w);;

(* Closer tail (ctm4 abbrev + h^3 norm + bridge + atomic ABBREVs + qS/qB),
   minus the final BINOP — mirror GCM_5B_TAIL_NOFINAL for N=4. *)
let GCM_4B_TAIL_NOFINAL : tactic =
  ABBREV_TAC `mask = word (2 EXP (8 * byte_len) - 1):(128)word` THEN
  ABBREV_TAC `ctm4 = word_and (ct4:(128)word) mask` THEN
  SUBGOAL_THEN `word_and (mask:(128)word) (ct4:(128)word) = ctm4`
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th]) THENL [
    EXPAND_TAC "ctm4" THEN CONV_TAC WORD_BITWISE_RULE; ALL_TAC ] THEN
  (* Normalize h^3 left-assoc -> symmetric (to match the 4-block bridge). *)
  SUBGOAL_THEN
    `polyval_dot (polyval_dot (h:int128) h) h = polyval_dot h (polyval_dot h h)`
    (fun th -> REWRITE_TAC[th]) THENL
    [REWRITE_TAC[polyval_dot] THEN REWRITE_TAC[WORD_PMUL_SYM]; ALL_TAC] THEN
  (* Apply 4-block bridge. *)
  MP_TAC(SPECL
    [`word_reversefields 8 (word_xor xi ct1):int128`;
     `word_reversefields 8 ct2:int128`; `word_reversefields 8 ct3:int128`;
     `word_reversefields 8 ctm4:int128`;
     `h:int128`; `h1k:int128`;
     `word_join (word 0:(64)word) (word_subword (h1k:(128)word) (64,64):(64)word):(128)word`;
     `h3k:int128`;
     `word_join (word 0:(64)word) (word_subword (h3k:(128)word) (64,64):(64)word):(128)word`]
    GHASH_4BLOCK_KARATSUBA_EQ_POLYVAL_ACC) THEN
  SUBGOAL_THEN
    `word_subword (word_join (word 0:(64)word) (word_subword (h1k:(128)word) (64,64):(64)word):(128)word) (0,64):(64)word =
     karatsuba_mid (polyval_dot h h)`
    (fun th -> REWRITE_TAC[th]) THENL [
    SUBGOAL_THEN
      `word_subword (word_join (word 0:(64)word) (word_subword (h1k:(128)word) (64,64):(64)word):(128)word) (0,64):(64)word =
       word_subword (h1k:(128)word) (64,64):(64)word`
      (fun th -> REWRITE_TAC[th]) THENL [CONV_TAC WORD_BLAST; ASM_REWRITE_TAC[]]; ALL_TAC ] THEN
  SUBGOAL_THEN
    `word_subword (word_join (word 0:(64)word) (word_subword (h3k:(128)word) (64,64):(64)word):(128)word) (0,64):(64)word =
     karatsuba_mid (polyval_dot (polyval_dot h h) (polyval_dot h h))`
    (fun th -> REWRITE_TAC[th]) THENL [
    SUBGOAL_THEN
      `word_subword (word_join (word 0:(64)word) (word_subword (h3k:(128)word) (64,64):(64)word):(128)word) (0,64):(64)word =
       word_subword (h3k:(128)word) (64,64):(64)word`
      (fun th -> REWRITE_TAC[th]) THENL [CONV_TAC WORD_BLAST; ASM_REWRITE_TAC[]]; ALL_TAC ] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN
  REWRITE_TAC[ghash_4block_karatsuba; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[SWAPHALVES128_SUBWORD_LO; SWAPHALVES128_SUBWORD_HI] THEN
  SUBGOAL_THEN
    `word_subword (word_join (word 0:(64)word) (karatsuba_mid (polyval_dot h h):(64)word):(128)word) (0,64):(64)word =
     karatsuba_mid (polyval_dot h h)`
    (fun th -> REWRITE_TAC[th]) THENL [CONV_TAC WORD_BLAST; ALL_TAC] THEN
  SUBGOAL_THEN
    `word_subword (word_join (word 0:(64)word) (karatsuba_mid (polyval_dot (polyval_dot h h) (polyval_dot h h)):(64)word):(128)word) (0,64):(64)word =
     karatsuba_mid (polyval_dot (polyval_dot h h) (polyval_dot h h))`
    (fun th -> REWRITE_TAC[th]) THENL [CONV_TAC WORD_BLAST; ALL_TAC] THEN
  REWRITE_TAC[GSYM karatsuba_mid] THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
  CONV_TAC SYM_CONV THEN
  FIRST_ASSUM(fun th ->
    if is_eq(concl th) && rand(concl th) = `final_xi:(128)word` &&
       (try (let l = lhs(concl th) in is_comb l &&
             (let r = rator l in not(is_comb r && (try fst(dest_const(rator r)) = "read" with _ -> false))))
        with _ -> false)
    then SUBST1_TAC(SYM th) else NO_TAC) THEN
  REWRITE_TAC[REV64_LOWER_LANE; REV64_UPPER_LANE; REV8_JOIN_FOLD] THEN
  MATCH_MP_TAC(MESON[]
    `x = y ==> word_reversefields 8 x = word_reversefields 8 y:(128)word`) THEN
  REWRITE_TAC[WORD_SWAP_HALVES_INVOLUTION] THEN
  CONV_TAC(LAND_CONV(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
  REWRITE_TAC[WORD_INSERT_AS_JOIN_LO; WORD_INSERT_AS_JOIN_HI;
              KAR_SUBWORD_LEMMA; WORD_SWAP_HALVES_INVOLUTION;
              WORD_OR_REFL; WORD_XOR_ASSOC; WORD_SUBWORD_XOR;
              SWAPHALVES128_SUBWORD_LO; SWAPHALVES128_SUBWORD_HI] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[HALFSWAP_XOR; GSYM WORD_REVERSEFIELDS_XOR_8_128;
              WORD_XOR_0; WORD_XOR_ASSOC;
              REV8_JOIN_FOLD; REVERSEFIELDS8_SUBWORD_LO; REVERSEFIELDS8_SUBWORD_HI] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  CONV_TAC(TOP_DEPTH_CONV PMUL_NORM_CONV) THEN
  SUBGOAL_THEN
    `word_subword (word 0:(128)word) (0,64):(64)word = word 0 /\
     word_subword (word 0:(128)word) (64,64):(64)word = word 0`
    (fun th -> REWRITE_TAC[th]) THENL [CONJ_TAC THEN CONV_TAC WORD_BLAST; ALL_TAC] THEN
  REWRITE_TAC[WORD_XOR_0; WORD_XOR_0_LEFT] THEN
  REWRITE_TAC[karatsuba_mid; WORD_REVERSEFIELDS_XOR_8_128; WORD_SUBWORD_XOR] THEN
  (* 18 atomic ABBREVs (c1lo..c4hi, xi, hd..hg). *)
  ABBREV_TAC `(c1lo:(64)word) = word_subword (word_reversefields 8 (ct1:(128)word)) (0,64)` THEN
  ABBREV_TAC `(c1hi:(64)word) = word_subword (word_reversefields 8 (ct1:(128)word)) (64,64)` THEN
  ABBREV_TAC `(c2lo:(64)word) = word_subword (word_reversefields 8 (ct2:(128)word)) (0,64)` THEN
  ABBREV_TAC `(c2hi:(64)word) = word_subword (word_reversefields 8 (ct2:(128)word)) (64,64)` THEN
  ABBREV_TAC `(c3lo:(64)word) = word_subword (word_reversefields 8 (ct3:(128)word)) (0,64)` THEN
  ABBREV_TAC `(c3hi:(64)word) = word_subword (word_reversefields 8 (ct3:(128)word)) (64,64)` THEN
  ABBREV_TAC `(c4lo:(64)word) = word_subword (word_reversefields 8 (ctm4:(128)word)) (0,64)` THEN
  ABBREV_TAC `(c4hi:(64)word) = word_subword (word_reversefields 8 (ctm4:(128)word)) (64,64)` THEN
  ABBREV_TAC `(xilo:(64)word) = word_subword (word_reversefields 8 (xi:(128)word)) (0,64)` THEN
  ABBREV_TAC `(xihi:(64)word) = word_subword (word_reversefields 8 (xi:(128)word)) (64,64)` THEN
  ABBREV_TAC `(hd0:(64)word) = word_subword (h:(128)word) (0,64)` THEN
  ABBREV_TAC `(hd1:(64)word) = word_subword (h:(128)word) (64,64)` THEN
  ABBREV_TAC `(he0:(64)word) = word_subword ((polyval_dot h h):(128)word) (0,64)` THEN
  ABBREV_TAC `(he1:(64)word) = word_subword ((polyval_dot h h):(128)word) (64,64)` THEN
  ABBREV_TAC `(hf0:(64)word) = word_subword ((polyval_dot h (polyval_dot h h)):(128)word) (0,64)` THEN
  ABBREV_TAC `(hf1:(64)word) = word_subword ((polyval_dot h (polyval_dot h h)):(128)word) (64,64)` THEN
  ABBREV_TAC `(hg0:(64)word) = word_subword ((polyval_dot (polyval_dot h h) (polyval_dot h h)):(128)word) (0,64)` THEN
  ABBREV_TAC `(hg1:(64)word) = word_subword ((polyval_dot (polyval_dot h h) (polyval_dot h h)):(128)word) (64,64)` THEN
  ASM_REWRITE_TAC[] THEN
  (* 12 inner pmul ABBREVs (w1..w4). *)
  ABBREV_TAC `(w1lo:(128)word) = word_pmul (word_xor (xilo:(64)word) (c1lo:(64)word)) (hg0:(64)word)` THEN
  ABBREV_TAC `(w1hi:(128)word) = word_pmul (word_xor (xihi:(64)word) (c1hi:(64)word)) (hg1:(64)word)` THEN
  ABBREV_TAC `(w1md:(128)word) = word_pmul (word_xor (word_xor (xihi:(64)word) (c1hi:(64)word)) (word_xor (xilo:(64)word) (c1lo:(64)word))) (word_xor (hg0:(64)word) (hg1:(64)word))` THEN
  ABBREV_TAC `(w2lo:(128)word) = word_pmul (c2lo:(64)word) (hf0:(64)word)` THEN
  ABBREV_TAC `(w2hi:(128)word) = word_pmul (c2hi:(64)word) (hf1:(64)word)` THEN
  ABBREV_TAC `(w2md:(128)word) = word_pmul (word_xor (c2hi:(64)word) (c2lo:(64)word)) (word_xor (hf0:(64)word) (hf1:(64)word))` THEN
  ABBREV_TAC `(w3lo:(128)word) = word_pmul (c3lo:(64)word) (he0:(64)word)` THEN
  ABBREV_TAC `(w3hi:(128)word) = word_pmul (c3hi:(64)word) (he1:(64)word)` THEN
  ABBREV_TAC `(w3md:(128)word) = word_pmul (word_xor (c3hi:(64)word) (c3lo:(64)word)) (word_xor (he0:(64)word) (he1:(64)word))` THEN
  ABBREV_TAC `(w4lo:(128)word) = word_pmul (c4lo:(64)word) (hd0:(64)word)` THEN
  ABBREV_TAC `(w4hi:(128)word) = word_pmul (c4hi:(64)word) (hd1:(64)word)` THEN
  ABBREV_TAC `(w4md:(128)word) = word_pmul (word_xor (c4hi:(64)word) (c4lo:(64)word)) (word_xor (hd0:(64)word) (hd1:(64)word))` THEN
  REWRITE_TAC[DOUBLE_SUBWORD_JOIN; DOUBLE_SUBWORD_JOIN_HI; WORD_SUBWORD_XOR] THEN
  SUBGOAL_THEN
    `word_pmul (word_xor (xihi:(64)word) (word_xor (c1hi:(64)word) (word_xor (xilo:(64)word) (c1lo:(64)word)))) (word_xor (hg0:(64)word) (hg1:(64)word)):(128)word = w1md`
    (fun th -> REWRITE_TAC[th]) THENL
    [EXPAND_TAC "w1md" THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  (* 24 z-vars. *)
  ABBREV_TAC `(w1lo_l:(64)word) = word_subword (w1lo:(128)word) (0,64)` THEN
  ABBREV_TAC `(w1lo_h:(64)word) = word_subword (w1lo:(128)word) (64,64)` THEN
  ABBREV_TAC `(w1hi_l:(64)word) = word_subword (w1hi:(128)word) (0,64)` THEN
  ABBREV_TAC `(w1hi_h:(64)word) = word_subword (w1hi:(128)word) (64,64)` THEN
  ABBREV_TAC `(w1md_l:(64)word) = word_subword (w1md:(128)word) (0,64)` THEN
  ABBREV_TAC `(w1md_h:(64)word) = word_subword (w1md:(128)word) (64,64)` THEN
  ABBREV_TAC `(w2lo_l:(64)word) = word_subword (w2lo:(128)word) (0,64)` THEN
  ABBREV_TAC `(w2lo_h:(64)word) = word_subword (w2lo:(128)word) (64,64)` THEN
  ABBREV_TAC `(w2hi_l:(64)word) = word_subword (w2hi:(128)word) (0,64)` THEN
  ABBREV_TAC `(w2hi_h:(64)word) = word_subword (w2hi:(128)word) (64,64)` THEN
  ABBREV_TAC `(w2md_l:(64)word) = word_subword (w2md:(128)word) (0,64)` THEN
  ABBREV_TAC `(w2md_h:(64)word) = word_subword (w2md:(128)word) (64,64)` THEN
  ABBREV_TAC `(w3lo_l:(64)word) = word_subword (w3lo:(128)word) (0,64)` THEN
  ABBREV_TAC `(w3lo_h:(64)word) = word_subword (w3lo:(128)word) (64,64)` THEN
  ABBREV_TAC `(w3hi_l:(64)word) = word_subword (w3hi:(128)word) (0,64)` THEN
  ABBREV_TAC `(w3hi_h:(64)word) = word_subword (w3hi:(128)word) (64,64)` THEN
  ABBREV_TAC `(w3md_l:(64)word) = word_subword (w3md:(128)word) (0,64)` THEN
  ABBREV_TAC `(w3md_h:(64)word) = word_subword (w3md:(128)word) (64,64)` THEN
  ABBREV_TAC `(w4lo_l:(64)word) = word_subword (w4lo:(128)word) (0,64)` THEN
  ABBREV_TAC `(w4lo_h:(64)word) = word_subword (w4lo:(128)word) (64,64)` THEN
  ABBREV_TAC `(w4hi_l:(64)word) = word_subword (w4hi:(128)word) (0,64)` THEN
  ABBREV_TAC `(w4hi_h:(64)word) = word_subword (w4hi:(128)word) (64,64)` THEN
  ABBREV_TAC `(w4md_l:(64)word) = word_subword (w4md:(128)word) (0,64)` THEN
  ABBREV_TAC `(w4md_h:(64)word) = word_subword (w4md:(128)word) (64,64)` THEN
  ASM_REWRITE_TAC[] THEN
  (* Normalize LHS mid-pmuls to the abbreviated w?md (swapped xor arg order). *)
  SUBGOAL_THEN `word_pmul (word_xor (c2lo:(64)word) (c2hi:(64)word)) (word_xor (hf0:(64)word) (hf1:(64)word)):(128)word = w2md`
    (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "w2md" THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  SUBGOAL_THEN `word_pmul (word_xor (c3lo:(64)word) (c3hi:(64)word)) (word_xor (he0:(64)word) (he1:(64)word)):(128)word = w3md`
    (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "w3md" THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  SUBGOAL_THEN `word_pmul (word_xor (c4lo:(64)word) (c4hi:(64)word)) (word_xor (hd0:(64)word) (hd1:(64)word)):(128)word = w4md`
    (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "w4md" THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  SUBGOAL_THEN `word_pmul (word_xor (xilo:(64)word) (word_xor (c1lo:(64)word) (word_xor (xihi:(64)word) (c1hi:(64)word)))) (word_xor (hg0:(64)word) (hg1:(64)word)):(128)word = w1md`
    (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "w1md" THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  (* qS: small Barrett pmul; fold both XOR orderings. *)
  ABBREV_TAC `(qS:(128)word) = word_pmul (word_xor (w4lo_l:(64)word) (word_xor w3lo_l (word_xor w2lo_l w1lo_l))) (word 13979173243358019584:(64)word)` THEN
  SUBGOAL_THEN `word_pmul (word_xor (w1lo_l:(64)word) (word_xor w2lo_l (word_xor w3lo_l w4lo_l))) (word 13979173243358019584:(64)word):(128)word = qS`
    (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "qS" THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  (* qB: big Barrett pmul; fold the LHS-order copy via bubble_sort_conv. *)
  ABBREV_TAC `(qB:(128)word) = word_pmul
    (word_xor (w4md_l:(64)word) (word_xor w3md_l (word_xor w2md_l (word_xor w1md_l (word_xor w4lo_l (word_xor w3lo_l (word_xor w2lo_l (word_xor w1lo_l (word_xor w4hi_l (word_xor w3hi_l (word_xor w2hi_l (word_xor w1hi_l (word_xor (word_subword (qS:(128)word) (0,64)) (word_xor w4lo_h (word_xor w3lo_h (word_xor w2lo_h w1lo_h)))))))))))))))) (word 13979173243358019584:(64)word)` THEN
  SUBGOAL_THEN
    `word_pmul (word_xor (w1lo_h:(64)word) (word_xor w2lo_h (word_xor w3lo_h (word_xor w4lo_h (word_xor w1md_l (word_xor w2md_l (word_xor w3md_l (word_xor w4md_l (word_xor w1hi_l (word_xor w2hi_l (word_xor w3hi_l (word_xor w4hi_l (word_xor w1lo_l (word_xor w2lo_l (word_xor w3lo_l (word_xor w4lo_l (word_subword (qS:(128)word) (0,64)))))))))))))))))) (word 13979173243358019584:(64)word):(128)word = qB`
    (fun th -> REWRITE_TAC[th]) THENL
    [EXPAND_TAC "qB" THEN AP_THM_TAC THEN AP_TERM_TAC THEN
     CONV_TAC(BINOP_CONV bubble_sort_conv) THEN REFL_TAC; ALL_TAC];;

(* per-half XOR-AC closer — mirror GCM_5B_HALF_CLOSE (4 mids, qS 4, qB 17). *)
let GCM_4B_FOLD_MIDS_TAC : tactic =
  fun (asl,gg) ->
    let rec finds hd t acc = match t with
      | Comb(Comb(Const("word_pmul",_),a),x) when x = hd ->
          a :: (finds hd a (finds hd x acc))
      | Comb(l,r) -> finds hd l (finds hd r acc)
      | Abs(_,b) -> finds hd b acc | _ -> acc in
    let hgw = `word_xor (hg0:(64)word) hg1`
    and hfw = `word_xor (hf0:(64)word) hf1`
    and hew = `word_xor (he0:(64)word) he1`
    and hdw = `word_xor (hd0:(64)word) hd1` in
    let mk tgt hd arg =
      SUBGOAL_THEN
        (mk_eq(list_mk_comb(`word_pmul:(64)word->(64)word->(128)word`,[arg;hd]),tgt))
        (fun th -> REWRITE_TAC[th]) THENL
       [EXPAND_TAC (fst(dest_var tgt)) THEN AP_THM_TAC THEN AP_TERM_TAC THEN
        CONV_TAC WORD_RULE; ALL_TAC] in
    (EVERY ((map (mk `w1md:(128)word` hgw) (setify(finds hgw gg [])))
          @ (map (mk `w2md:(128)word` hfw) (setify(finds hfw gg [])))
          @ (map (mk `w3md:(128)word` hew) (setify(finds hew gg [])))
          @ (map (mk `w4md:(128)word` hdw) (setify(finds hdw gg []))))) (asl,gg);;

let GCM_4B_FOLD_TO tgt natoms : tactic =
  let w64 = `word 13979173243358019584:(64)word` in
  fun (asl,gg) ->
    let rec finds t acc = match t with
      | Comb(Comb(Const("word_pmul",_),a),x) when x = w64 ->
          a :: (finds a (finds x acc))
      | Comb(l,r) -> finds l (finds r acc) | Abs(_,b) -> finds b acc | _ -> acc in
    let rec at t = match t with
      | Comb(Comb(Const("word_xor",_),x),y) -> at x @ at y | _ -> [t] in
    let args = List.filter (fun a -> List.length(at a) = natoms) (setify(finds gg [])) in
    (EVERY (map (fun a ->
       FIRST [SUBGOAL_THEN
                (mk_eq(list_mk_comb(`word_pmul:(64)word->(64)word->(128)word`,[a;w64]),tgt))
                (fun th -> REWRITE_TAC[th]) THENL
               [EXPAND_TAC (fst(dest_var tgt)) THEN AP_THM_TAC THEN AP_TERM_TAC THEN
                CONV_TAC(BINOP_CONV bubble_fix) THEN REFL_TAC; ALL_TAC];
              ALL_TAC]) args)) (asl,gg);;

let GCM_4B_HALF_CLOSE : tactic =
  GCM_4B_FOLD_MIDS_TAC THEN ASM_REWRITE_TAC[] THEN
  GCM_4B_FOLD_TO `qS:(128)word` 4 THEN ASM_REWRITE_TAC[] THEN
  GCM_4B_FOLD_TO `qB:(128)word` 17 THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(BINOP_CONV bubble_fix) THEN REFL_TAC;;

(* The full GHASH closer — mirror GCM_5B_GHASH_CLOSE. *)
let GCM_4B_GHASH_CLOSE : tactic =
  GCM_4B_FOLD_SPEC_CTS THEN
  REWRITE_TAC[GHASH_POLYVAL_ACC_4; POLYVAL_DOT_H4_EQ_LOCAL; GSYM WORD_REVERSEFIELDS_XOR_8_128] THEN
  GCM_4B_MASK_COLLAPSE_ASMS THEN
  GCM_4B_KS4_FOLD THEN
  GCM_4B_TAIL_NOFINAL THEN
  REWRITE_TAC[XI_HS_LO_4; XI_HS_HI_4] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `word_pmul (word_xor (xihi:(64)word) (word_xor c1hi (word_xor xilo c1lo)))
              (word_xor (hg0:(64)word) hg1):(128)word = w1md`
   (fun th -> REWRITE_TAC[th]) THENL
   [EXPAND_TAC "w1md" THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  BINOP_TAC THENL [GCM_4B_HALF_CLOSE; GCM_4B_HALF_CLOSE];;

(* masked-ct4 store conjunct closer — mirror GCM_5B_MASKED_CT5_CLOSE (+3). *)
let GCM_4B_MASKED_CT4_CLOSE : tactic =
  let bri = WORD_BLAST `word_bytereverse (word_bytereverse (x:(32)word)) = x` in
  let add3 = WORD_RULE `word_add (word_add (word_add (x:(32)word) (word 1)) (word 1)) (word 1) = word_add x (word 3)` in
  SUBGOAL_THEN `1 <= byte_len /\ byte_len <= 16` MP_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP FOURBLOCK_MASK_REG th]) THEN
  REWRITE_TAC[NBLOCK_MASK_IDEM] THEN
  MATCH_MP_TAC(MESON[] `x = y ==> word_or (word_and x m) r = word_or (word_and y m) r:(128)word`) THEN
  CONV_TAC SYM_CONV THEN REWRITE_TAC[AES256_ENCRYPT_UNFOLD] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[WORD_XOR_ASSOC] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REPEAT(AP_THM_TAC ORELSE AP_TERM_TAC) THEN
  REWRITE_TAC[gcm_ctr_inc] THEN
  REWRITE_TAC[WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
  REWRITE_TAC[WORD_REVERSEFIELDS_8_BYTEREVERSE_32] THEN
  REWRITE_TAC[INSERT_SUBWORD; INSERT_IDEM] THEN
  REWRITE_TAC[bri] THEN REWRITE_TAC[add3] THEN
  REWRITE_TAC[CTR_WORD_INSERT];;

(* The 4-block branch goal (three full + one partial block). *)
let gcm_4b_goal = `!in_ptr out_ptr xi_ptr ivec_ptr key_ptr htable_ptr
    (pt1:(128)word) (pt2:(128)word) (pt3:(128)word) (pt4:(128)word)
    (out0:(128)word)
    (ivec:(128)word)
    (rk0:(128)word) (rk1:(128)word) (rk2:(128)word) (rk3:(128)word)
    (rk4:(128)word) (rk5:(128)word) (rk6:(128)word) (rk7:(128)word)
    (rk8:(128)word) (rk9:(128)word) (rk10:(128)word) (rk11:(128)word)
    (rk12:(128)word) (rk13:(128)word) (rk14:(128)word)
    (xi:(128)word) (h:(128)word) (h1k:(128)word) (h3k:(128)word)
    byte_len stackptr pc.
    1 <= byte_len /\ byte_len <= 16 /\
    aligned 16 stackptr /\
    nonoverlapping (word pc,4600) (in_ptr:int64,64) /\
    nonoverlapping (word pc,4600) (out_ptr:int64,64) /\
    nonoverlapping (word pc,4600) (xi_ptr:int64,16) /\
    nonoverlapping (word pc,4600) (ivec_ptr:int64,16) /\
    nonoverlapping (word pc,4600) (key_ptr:int64,240) /\
    nonoverlapping (word pc,4600) (htable_ptr:int64,256) /\
    nonoverlapping (word pc,4600) (stackptr:int64,80) /\
    nonoverlapping (in_ptr,64) (out_ptr,64) /\
    nonoverlapping (in_ptr,64) (xi_ptr,16) /\
    nonoverlapping (in_ptr,64) (ivec_ptr,16) /\
    nonoverlapping (out_ptr,64) (xi_ptr,16) /\
    nonoverlapping (out_ptr,64) (ivec_ptr,16) /\
    nonoverlapping (xi_ptr,16) (ivec_ptr,16) /\
    nonoverlapping (key_ptr,240) (out_ptr,64) /\
    nonoverlapping (key_ptr,240) (xi_ptr,16) /\
    nonoverlapping (key_ptr,240) (ivec_ptr,16) /\
    nonoverlapping (htable_ptr,256) (out_ptr,64) /\
    nonoverlapping (htable_ptr,256) (xi_ptr,16) /\
    nonoverlapping (htable_ptr,256) (ivec_ptr,16) /\
    nonoverlapping (stackptr,80) (out_ptr,64) /\
    nonoverlapping (stackptr,80) (xi_ptr,16) /\
    nonoverlapping (stackptr,80) (ivec_ptr,16) /\
    nonoverlapping (stackptr,80) (in_ptr,64) /\
    nonoverlapping (stackptr,80) (key_ptr,240) /\
    nonoverlapping (stackptr,80) (htable_ptr,256) /\
    nonoverlapping (ivec_ptr,16) (word pc,4600) /\
    nonoverlapping (xi_ptr,16) (word pc,4600) /\
    nonoverlapping (out_ptr,64) (word pc,4600)
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) aes256_gcm_mc /\
           read PC s = word pc /\
           C_ARGUMENTS [in_ptr; word (384 + 8 * byte_len); out_ptr; xi_ptr;
                        ivec_ptr; key_ptr; htable_ptr] s /\
           read SP s = word_add stackptr (word 80) /\
           read (memory :> bytes128 in_ptr) s = pt1 /\
           read (memory :> bytes128 (word_add in_ptr (word 16))) s = pt2 /\
           read (memory :> bytes128 (word_add in_ptr (word 32))) s = pt3 /\
           read (memory :> bytes128 (word_add in_ptr (word 48))) s = pt4 /\
           read (memory :> bytes128 (word_add out_ptr (word 48))) s = out0 /\
           read (memory :> bytes128 ivec_ptr) s = ivec /\
           read (memory :> bytes128 (word_add key_ptr (word 0))) s = rk0 /\
           read (memory :> bytes128 (word_add key_ptr (word 16))) s = rk1 /\
           read (memory :> bytes128 (word_add key_ptr (word 32))) s = rk2 /\
           read (memory :> bytes128 (word_add key_ptr (word 48))) s = rk3 /\
           read (memory :> bytes128 (word_add key_ptr (word 64))) s = rk4 /\
           read (memory :> bytes128 (word_add key_ptr (word 80))) s = rk5 /\
           read (memory :> bytes128 (word_add key_ptr (word 96))) s = rk6 /\
           read (memory :> bytes128 (word_add key_ptr (word 112))) s = rk7 /\
           read (memory :> bytes128 (word_add key_ptr (word 128))) s = rk8 /\
           read (memory :> bytes128 (word_add key_ptr (word 144))) s = rk9 /\
           read (memory :> bytes128 (word_add key_ptr (word 160))) s = rk10 /\
           read (memory :> bytes128 (word_add key_ptr (word 176))) s = rk11 /\
           read (memory :> bytes128 (word_add key_ptr (word 192))) s = rk12 /\
           read (memory :> bytes128 (word_add key_ptr (word 208))) s = rk13 /\
           read (memory :> bytes128 (word_add key_ptr (word 224))) s = rk14 /\
           read (memory :> bytes128 xi_ptr) s = xi /\
           read (memory :> bytes128 htable_ptr) s = word_swaphalves128 h /\
           read (memory :> bytes128 (word_add htable_ptr (word 16))) s = h1k /\
           read (memory :> bytes128 (word_add htable_ptr (word 32))) s =
             word_swaphalves128 (polyval_dot h h) /\
           read (memory :> bytes128 (word_add htable_ptr (word 48))) s =
             word_swaphalves128 (polyval_dot h (polyval_dot h h)) /\
           read (memory :> bytes128 (word_add htable_ptr (word 64))) s = h3k /\
           read (memory :> bytes128 (word_add htable_ptr (word 80))) s =
             word_swaphalves128 (polyval_dot (polyval_dot h h) (polyval_dot h h)) /\
           word_subword h1k (0,64):(64)word = karatsuba_mid h /\
           word_subword h1k (64,64):(64)word =
             karatsuba_mid (polyval_dot h h) /\
           word_subword h3k (0,64):(64)word =
             karatsuba_mid (polyval_dot h (polyval_dot h h)) /\
           word_subword h3k (64,64):(64)word =
             karatsuba_mid (polyval_dot (polyval_dot h h) (polyval_dot h h)))
      (\s. let ct1 =
             word_xor pt1
               (aes256_encrypt ivec [rk0;rk1;rk2;rk3;rk4;rk5;rk6;rk7;rk8;rk9;rk10;rk11;rk12;rk13;rk14]) in
           let ct2 =
             word_xor pt2
               (aes256_encrypt (gcm_ctr_inc ivec) [rk0;rk1;rk2;rk3;rk4;rk5;rk6;rk7;rk8;rk9;rk10;rk11;rk12;rk13;rk14]) in
           let ct3 =
             word_xor pt3
               (aes256_encrypt (gcm_ctr_inc (gcm_ctr_inc ivec)) [rk0;rk1;rk2;rk3;rk4;rk5;rk6;rk7;rk8;rk9;rk10;rk11;rk12;rk13;rk14]) in
           let ct4 =
             word_xor pt4
               (aes256_encrypt (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ivec))) [rk0;rk1;rk2;rk3;rk4;rk5;rk6;rk7;rk8;rk9;rk10;rk11;rk12;rk13;rk14]) in
           let mask = word (2 EXP (8 * byte_len) - 1):(128)word in
           let ctm4 = word_and ct4 mask in
           read PC s = word(pc + 4588) /\
           read X0 s = word (48 + byte_len) /\
           read (memory :> bytes128 out_ptr) s = ct1 /\
           read (memory :> bytes128 (word_add out_ptr (word 16))) s = ct2 /\
           read (memory :> bytes128 (word_add out_ptr (word 32))) s = ct3 /\
           read (memory :> bytes128 (word_add out_ptr (word 48))) s =
             word_or ctm4 (word_and out0 (word_not mask)) /\
           read (memory :> bytes128 xi_ptr) s =
             word_reversefields 8
               (ghash_polyval_acc h (word_reversefields 8 xi)
                                    [word_reversefields 8 ct1;
                                     word_reversefields 8 ct2;
                                     word_reversefields 8 ct3;
                                     word_reversefields 8 ctm4]))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [memory :> bytes(out_ptr,64);
                  memory :> bytes(xi_ptr,16);
                  memory :> bytes(ivec_ptr,16)] ,,
       MAYCHANGE [SP] ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes64 stackptr;
                  memory :> bytes64 (word_add stackptr (word 8));
                  memory :> bytes64 (word_add stackptr (word 16));
                  memory :> bytes64 (word_add stackptr (word 24));
                  memory :> bytes64 (word_add stackptr (word 32));
                  memory :> bytes64 (word_add stackptr (word 40));
                  memory :> bytes64 (word_add stackptr (word 48));
                  memory :> bytes64 (word_add stackptr (word 56));
                  memory :> bytes64 (word_add stackptr (word 64));
                  memory :> bytes64 (word_add stackptr (word 72))])`;;

let AES256_GCM_ENCRYPT_LT_4BLOCK_CONCRETE = prove
 (gcm_4b_goal,
  (* ---- symbolic simulation (store-based ct abbreviation) ---- *)
  GCM_INIT_TAC GCM_CBZ_LEMMA4 THEN GCM_PROLOGUE_TAC THEN GCM_RUN 20 263 THEN
  GCM_INLOOP_GUARD_TAC GCM_X5_LEMMA4 THEN GCM_RUN 267 272 THEN
  GCM_BND16 GCM_X5TAIL_LEMMA4 THEN
  GCM_RUN_THEN GCM_CASCADE4_TAC 273 321 THEN
  abbrev_ct_from_store 0 1 THEN
  GCM_RUN 322 335 THEN abbrev_ct_from_store 16 2 THEN
  GCM_RUN 336 348 THEN abbrev_ct_from_store 32 3 THEN
  GCM_RUN 349 366 THEN
  SUBGOAL_THEN `1 <= (byte_len:num) /\ byte_len <= 16` MP_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP FOURBLOCK_MASK_REG th])) THEN
  GCM_RUN 367 379 THEN GCM_RUN 380 394 THEN ARM_STEPS_TAC AES256_GCM_EXEC (395--395) THEN
  GCM_NBLOCK_POST_SIM_NORMALIZE_TAC THEN ABBREV_FINAL_XI_TAC THEN
  ARM_STEPS_TAC AES256_GCM_EXEC (396--403) THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ENSURES_FINAL_STATE_TAC THEN
  SUBGOAL_THEN `1 <= (byte_len:num) /\ byte_len <= 16` MP_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP FOURBLOCK_MASK_REG th]) THEN
  ASM_SIMP_TAC[FOURBLOCK_USHR] THEN
  (* ---- five conjuncts: ct1..ct3, masked-ct4, GHASH ---- *)
  CONJ_TAC THENL [CT_CLOSE_4 1; ALL_TAC] THEN
  CONJ_TAC THENL [CONV_TAC SYM_CONV THEN GCM_4BLOCK_CT2_STEP_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [CONV_TAC SYM_CONV THEN GCM_4BLOCK_CT3_STEP_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [GCM_4B_MASKED_CT4_CLOSE; ALL_TAC] THEN
  (* ---- ct4 abbreviation (spec form) so the closer's ctm4 works ---- *)
  ABBREV_TAC `ct4 = word_xor pt4
    (aes256_encrypt (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ivec))) [rk0;rk1;rk2;rk3;rk4;rk5;rk6;rk7;rk8;rk9;rk10;rk11;rk12;rk13;rk14]):(128)word` THEN
  (* ---- GHASH conjunct ---- *)
  GCM_4B_GHASH_CLOSE);;

(* ========================================================================= *)
(* The L256_enc_blocks_more_than_4 branch (5-block: four full blocks +       *)
(* partial block 5, total 65..80 bytes) of the single binary, proved as a    *)
(* standalone theorem and applied exactly as the XTS length-band lemmas are. *)
(* Reuses the five-block masked closers from gcm_five_block_closers.ml.      *)
(* ========================================================================= *)

needs "arm/proofs/utils/gcm_five_block_closers.ml";;

(* --- 5-block-branch length/cascade helpers (thresholds over 64+byte_len) --- *)

let GCM_CBZ_LEMMA5 = prove
 (`1 <= byte_len /\ byte_len <= 16 ==> ~(val(word(512+8*byte_len):int64) = 0)`,
  STRIP_TAC THEN SUBGOAL_THEN `val(word(512+8*byte_len):int64) = 512+8*byte_len` SUBST1_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC;
    ASM_ARITH_TAC]);;

let GCM_WSUB5 = prove
 (`byte_len <= 16 ==> word_sub (word (64+byte_len):int64) (word 1) = word (63 + byte_len)`,
  CONV_TAC WORD_RULE);;

let GCM_X5_LEMMA5 = prove
 (`1 <= byte_len /\ byte_len <= 16 ==>
   word_add (word_and (word_sub (word_ushr (word (512+8*byte_len):int64) 3) (word 1))
                      (word 18446744073709551488)) in_ptr = in_ptr`,
  STRIP_TAC THEN
  SUBGOAL_THEN `word_ushr (word (512+8*byte_len):int64) 3 = word (64+byte_len)` SUBST1_TAC THENL
   [ASM_SIMP_TAC[FIVEBLOCK_USHR]; ALL_TAC] THEN
  ASM_SIMP_TAC[GCM_WSUB5] THEN
  SUBGOAL_THEN `word_and (word (63+byte_len):int64) (word 18446744073709551488) = word 0` SUBST1_TAC THENL
   [MATCH_MP_TAC GCM_ANDMASK0 THEN ASM_ARITH_TAC; ALL_TAC] THEN
  CONV_TAC WORD_RULE);;

let GCM_X5TAIL_LEMMA5 = prove
 (`byte_len <= 16 ==>
   word_sub (word_add in_ptr (word_ushr (word (512+8*byte_len):int64) 3)) in_ptr = word (64+byte_len)`,
  ASM_SIMP_TAC[FIVEBLOCK_USHR] THEN CONV_TAC WORD_RULE);;

let GCM_CASC5_FALSE = prove
 (`!byte_len t. byte_len <= 16 /\ 80 <= t /\ t <= 112 ==>
    ((~(val (word_sub (word (64+byte_len):int64) (word t)) = 0) /\
      (ival (word_sub (word (64+byte_len):int64) (word t)) < &0 <=>
       ~(ival (word (64+byte_len):int64) - &t = ival (word_sub (word (64+byte_len):int64) (word t)))))
     <=> F)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `ival(word (64+byte_len):int64) = &(64+byte_len)` ASSUME_TAC THENL
   [MATCH_MP_TAC NBLOCK_IVAL_WORD_SMALL THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `word_sub (word (64+byte_len):int64) (word t) = iword(&(64+byte_len) - &t)` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM IWORD_INT_SUB; WORD_IWORD]; ALL_TAC] THEN
  SUBGOAL_THEN `ival(iword(&(64+byte_len) - &t):int64) = &(64+byte_len) - &t` ASSUME_TAC THENL
   [MATCH_MP_TAC IVAL_IWORD THEN REWRITE_TAC[DIMINDEX_64] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_SUB_CONV) THEN
    SUBGOAL_THEN `&(64+byte_len):int <= &80 /\ &80:int <= &t /\ &t:int <= &112` MP_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN INT_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[VAL_EQ_0; GSYM IVAL_EQ_0] THEN
  SUBGOAL_THEN `&(64+byte_len):int <= &80 /\ &80:int <= &t` MP_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN INT_ARITH_TAC);;

let GCM_CASC5_TRUE = prove
 (`1 <= byte_len /\ byte_len <= 16 ==>
    ((~(val (word_sub (word (64+byte_len):int64) (word 64)) = 0) /\
      (ival (word_sub (word (64+byte_len):int64) (word 64)) < &0 <=>
       ~(ival (word (64+byte_len):int64) - &64 = ival (word_sub (word (64+byte_len):int64) (word 64)))))
     <=> T)`,
  STRIP_TAC THEN
  SUBGOAL_THEN `ival(word (64+byte_len):int64) = &(64+byte_len)` ASSUME_TAC THENL
   [MATCH_MP_TAC NBLOCK_IVAL_WORD_SMALL THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `word_sub (word (64+byte_len):int64) (word 64) = iword(&(64+byte_len) - &64)` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM IWORD_INT_SUB; WORD_IWORD]; ALL_TAC] THEN
  SUBGOAL_THEN `ival(iword(&(64+byte_len) - &64):int64) = &(64+byte_len) - &64` ASSUME_TAC THENL
   [MATCH_MP_TAC IVAL_IWORD THEN REWRITE_TAC[DIMINDEX_64] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_SUB_CONV) THEN
    SUBGOAL_THEN `&(64+byte_len):int <= &80` MP_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN INT_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[VAL_EQ_0; GSYM IVAL_EQ_0] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_ADD] THEN
  SUBGOAL_THEN `&1:int <= &byte_len` MP_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN INT_ARITH_TAC);;

let GCM_CASCADE5_TAC : tactic =
  FIRST_X_ASSUM(fun bl16 -> if concl bl16 = `byte_len <= 16` then
    FIRST_X_ASSUM(fun bl1 -> if concl bl1 = `1 <= byte_len` then
      RULE_ASSUM_TAC(REWRITE_RULE(
        (map (fun t -> MATCH_MP GCM_CASC5_FALSE (CONJ bl16
                (CONJ (ARITH_RULE(vsubst[mk_numeral(num_of_int t),`t:num`] `80 <= t`))
                      (ARITH_RULE(vsubst[mk_numeral(num_of_int t),`t:num`] `t <= 112`)))))
             [80;96;112]) @
        [MATCH_MP GCM_CASC5_TRUE (CONJ bl1 bl16); COND_CLAUSES])) THEN
      ASSUME_TAC bl1 THEN ASSUME_TAC bl16
    else NO_TAC)
  else NO_TAC);;

(* --- The 5-block branch goal (four full + one partial block). --- *)

let gcm_5b_goal = `!in_ptr out_ptr xi_ptr ivec_ptr key_ptr htable_ptr
    (pt1:(128)word) (pt2:(128)word) (pt3:(128)word) (pt4:(128)word) (pt5:(128)word)
    (out0:(128)word)
    (ivec:(128)word)
    (rk0:(128)word) (rk1:(128)word) (rk2:(128)word) (rk3:(128)word)
    (rk4:(128)word) (rk5:(128)word) (rk6:(128)word) (rk7:(128)word)
    (rk8:(128)word) (rk9:(128)word) (rk10:(128)word) (rk11:(128)word)
    (rk12:(128)word) (rk13:(128)word) (rk14:(128)word)
    (xi:(128)word) (h:(128)word) (h1k:(128)word) (h3k:(128)word) (h5k:(128)word)
    byte_len stackptr pc.
    1 <= byte_len /\ byte_len <= 16 /\
    aligned 16 stackptr /\
    nonoverlapping (word pc,4600) (in_ptr:int64,80) /\
    nonoverlapping (word pc,4600) (out_ptr:int64,80) /\
    nonoverlapping (word pc,4600) (xi_ptr:int64,16) /\
    nonoverlapping (word pc,4600) (ivec_ptr:int64,16) /\
    nonoverlapping (word pc,4600) (key_ptr:int64,240) /\
    nonoverlapping (word pc,4600) (htable_ptr:int64,256) /\
    nonoverlapping (word pc,4600) (stackptr:int64,80) /\
    nonoverlapping (in_ptr,80) (out_ptr,80) /\
    nonoverlapping (in_ptr,80) (xi_ptr,16) /\
    nonoverlapping (in_ptr,80) (ivec_ptr,16) /\
    nonoverlapping (out_ptr,80) (xi_ptr,16) /\
    nonoverlapping (out_ptr,80) (ivec_ptr,16) /\
    nonoverlapping (xi_ptr,16) (ivec_ptr,16) /\
    nonoverlapping (key_ptr,240) (out_ptr,80) /\
    nonoverlapping (key_ptr,240) (xi_ptr,16) /\
    nonoverlapping (key_ptr,240) (ivec_ptr,16) /\
    nonoverlapping (htable_ptr,256) (out_ptr,80) /\
    nonoverlapping (htable_ptr,256) (xi_ptr,16) /\
    nonoverlapping (htable_ptr,256) (ivec_ptr,16) /\
    nonoverlapping (stackptr,80) (out_ptr,80) /\
    nonoverlapping (stackptr,80) (xi_ptr,16) /\
    nonoverlapping (stackptr,80) (ivec_ptr,16) /\
    nonoverlapping (stackptr,80) (in_ptr,80) /\
    nonoverlapping (stackptr,80) (key_ptr,240) /\
    nonoverlapping (stackptr,80) (htable_ptr,256) /\
    nonoverlapping (ivec_ptr,16) (word pc,4600) /\
    nonoverlapping (xi_ptr,16) (word pc,4600) /\
    nonoverlapping (out_ptr,80) (word pc,4600)
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) aes256_gcm_mc /\
           read PC s = word pc /\
           C_ARGUMENTS [in_ptr; word (512 + 8 * byte_len); out_ptr; xi_ptr;
                        ivec_ptr; key_ptr; htable_ptr] s /\
           read SP s = word_add stackptr (word 80) /\
           read (memory :> bytes128 in_ptr) s = pt1 /\
           read (memory :> bytes128 (word_add in_ptr (word 16))) s = pt2 /\
           read (memory :> bytes128 (word_add in_ptr (word 32))) s = pt3 /\
           read (memory :> bytes128 (word_add in_ptr (word 48))) s = pt4 /\
           read (memory :> bytes128 (word_add in_ptr (word 64))) s = pt5 /\
           read (memory :> bytes128 (word_add out_ptr (word 64))) s = out0 /\
           read (memory :> bytes128 ivec_ptr) s = ivec /\
           read (memory :> bytes128 (word_add key_ptr (word 0))) s = rk0 /\
           read (memory :> bytes128 (word_add key_ptr (word 16))) s = rk1 /\
           read (memory :> bytes128 (word_add key_ptr (word 32))) s = rk2 /\
           read (memory :> bytes128 (word_add key_ptr (word 48))) s = rk3 /\
           read (memory :> bytes128 (word_add key_ptr (word 64))) s = rk4 /\
           read (memory :> bytes128 (word_add key_ptr (word 80))) s = rk5 /\
           read (memory :> bytes128 (word_add key_ptr (word 96))) s = rk6 /\
           read (memory :> bytes128 (word_add key_ptr (word 112))) s = rk7 /\
           read (memory :> bytes128 (word_add key_ptr (word 128))) s = rk8 /\
           read (memory :> bytes128 (word_add key_ptr (word 144))) s = rk9 /\
           read (memory :> bytes128 (word_add key_ptr (word 160))) s = rk10 /\
           read (memory :> bytes128 (word_add key_ptr (word 176))) s = rk11 /\
           read (memory :> bytes128 (word_add key_ptr (word 192))) s = rk12 /\
           read (memory :> bytes128 (word_add key_ptr (word 208))) s = rk13 /\
           read (memory :> bytes128 (word_add key_ptr (word 224))) s = rk14 /\
           read (memory :> bytes128 xi_ptr) s = xi /\
           read (memory :> bytes128 htable_ptr) s = word_swaphalves128 h /\
           read (memory :> bytes128 (word_add htable_ptr (word 16))) s = h1k /\
           read (memory :> bytes128 (word_add htable_ptr (word 32))) s =
             word_swaphalves128 (polyval_dot h h) /\
           read (memory :> bytes128 (word_add htable_ptr (word 48))) s =
             word_swaphalves128 (polyval_dot h (polyval_dot h h)) /\
           read (memory :> bytes128 (word_add htable_ptr (word 64))) s = h3k /\
           read (memory :> bytes128 (word_add htable_ptr (word 80))) s =
             word_swaphalves128 (polyval_dot (polyval_dot h h) (polyval_dot h h)) /\
           read (memory :> bytes128 (word_add htable_ptr (word 96))) s =
             word_swaphalves128 (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) /\
           read (memory :> bytes128 (word_add htable_ptr (word 112))) s = h5k /\
           word_subword h1k (0,64):(64)word = karatsuba_mid h /\
           word_subword h1k (64,64):(64)word =
             karatsuba_mid (polyval_dot h h) /\
           word_subword h3k (0,64):(64)word =
             karatsuba_mid (polyval_dot h (polyval_dot h h)) /\
           word_subword h3k (64,64):(64)word =
             karatsuba_mid (polyval_dot (polyval_dot h h) (polyval_dot h h)) /\
           word_subword h5k (0,64):(64)word =
             karatsuba_mid (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h))
      (\s. let ct1 =
             word_xor pt1
               (aes256_encrypt ivec [rk0;rk1;rk2;rk3;rk4;rk5;rk6;rk7;rk8;rk9;rk10;rk11;rk12;rk13;rk14]) in
           let ct2 =
             word_xor pt2
               (aes256_encrypt (gcm_ctr_inc ivec) [rk0;rk1;rk2;rk3;rk4;rk5;rk6;rk7;rk8;rk9;rk10;rk11;rk12;rk13;rk14]) in
           let ct3 =
             word_xor pt3
               (aes256_encrypt (gcm_ctr_inc (gcm_ctr_inc ivec)) [rk0;rk1;rk2;rk3;rk4;rk5;rk6;rk7;rk8;rk9;rk10;rk11;rk12;rk13;rk14]) in
           let ct4 =
             word_xor pt4
               (aes256_encrypt (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ivec))) [rk0;rk1;rk2;rk3;rk4;rk5;rk6;rk7;rk8;rk9;rk10;rk11;rk12;rk13;rk14]) in
           let ct5 =
             word_xor pt5
               (aes256_encrypt (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ivec)))) [rk0;rk1;rk2;rk3;rk4;rk5;rk6;rk7;rk8;rk9;rk10;rk11;rk12;rk13;rk14]) in
           let mask = word (2 EXP (8 * byte_len) - 1):(128)word in
           let ctm5 = word_and ct5 mask in
           read PC s = word(pc + 4588) /\
           read X0 s = word (64 + byte_len) /\
           read (memory :> bytes128 out_ptr) s = ct1 /\
           read (memory :> bytes128 (word_add out_ptr (word 16))) s = ct2 /\
           read (memory :> bytes128 (word_add out_ptr (word 32))) s = ct3 /\
           read (memory :> bytes128 (word_add out_ptr (word 48))) s = ct4 /\
           read (memory :> bytes128 (word_add out_ptr (word 64))) s =
             word_or ctm5 (word_and out0 (word_not mask)) /\
           read (memory :> bytes128 xi_ptr) s =
             word_reversefields 8
               (ghash_polyval_acc h (word_reversefields 8 xi)
                                    [word_reversefields 8 ct1;
                                     word_reversefields 8 ct2;
                                     word_reversefields 8 ct3;
                                     word_reversefields 8 ct4;
                                     word_reversefields 8 ctm5]))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [memory :> bytes(out_ptr,80);
                  memory :> bytes(xi_ptr,16);
                  memory :> bytes(ivec_ptr,16)] ,,
       MAYCHANGE [SP] ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes64 stackptr;
                  memory :> bytes64 (word_add stackptr (word 8));
                  memory :> bytes64 (word_add stackptr (word 16));
                  memory :> bytes64 (word_add stackptr (word 24));
                  memory :> bytes64 (word_add stackptr (word 32));
                  memory :> bytes64 (word_add stackptr (word 40));
                  memory :> bytes64 (word_add stackptr (word 48));
                  memory :> bytes64 (word_add stackptr (word 56));
                  memory :> bytes64 (word_add stackptr (word 64));
                  memory :> bytes64 (word_add stackptr (word 72))])`;;

(* --- Store-based ct abbreviation (robust against Q-register scramble). --- *)
(* `abbrev_ct_from_store` is now defined once in the 4-block GHASH-closer    *)
(* section above (its first use), and shared verbatim by the 5/6-block       *)
(* branches here.                                                            *)

(* --- 5-block GHASH final-closure helper tactics. --- *)

(* ========================================================================= *)
(* Self-contained 5-block GHASH conjunct closer for the single-binary        *)
(* aes256_gcm.ml more_than_4 (5-block) branch.  Reaches "No subgoals" from   *)
(* the final GHASH equality (machine word_join = spec word_reversefields).   *)
(* Mirrors the 4-block recipe; adds the ks5 +4-counter bridge and the in-asm *)
(* b0-general mask-register collapse that the 5-block sim leaves baked into  *)
(* final_xi.                                                                 *)
(* ========================================================================= *)

(* xi half-swap normalization (shared with 4-block, redefined locally). *)
let XI_HS_LO_5 = prove
 (`word_subword (word_reversefields 8 (word_join (word_subword (xi:(128)word) (64,64):(64)word) (word_subword xi (0,64):(64)word):(128)word)) (0,64):(64)word =
   word_subword (word_reversefields 8 xi) (0,64)`,
  REWRITE_TAC[GSYM REV8_JOIN_FOLD; REVERSEFIELDS8_SUBWORD_LO; REVERSEFIELDS8_SUBWORD_HI] THEN
  CONV_TAC WORD_BLAST);;

let XI_HS_HI_5 = prove
 (`word_subword (word_reversefields 8 (word_join (word_subword (xi:(128)word) (64,64):(64)word) (word_subword xi (0,64):(64)word):(128)word)) (64,64):(64)word =
   word_subword (word_reversefields 8 xi) (64,64)`,
  REWRITE_TAC[GSYM REV8_JOIN_FOLD; REVERSEFIELDS8_SUBWORD_LO; REVERSEFIELDS8_SUBWORD_HI] THEN
  CONV_TAC WORD_BLAST);;

(* Closer tail (ctm5 abbrev + bridge + atomic ABBREVs + qS/qB), minus the
   final BINOP. *)
let GCM_5B_TAIL_NOFINAL : tactic =
ABBREV_TAC `mask = word (2 EXP (8 * byte_len) - 1):(128)word` THEN
  ABBREV_TAC `ctm5 = word_and (ct5:(128)word) mask` THEN
  SUBGOAL_THEN `word_and (mask:(128)word) (ct5:(128)word) = ctm5`
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th]) THENL [
    EXPAND_TAC "ctm5" THEN CONV_TAC WORD_BITWISE_RULE; ALL_TAC ] THEN
  (* Normalize h^4 then h^3 left-assoc -> symmetric (to match the 5-block bridge). *)
  SUBGOAL_THEN
    `polyval_dot (polyval_dot (polyval_dot (h:int128) h) h) h =
     polyval_dot (polyval_dot h h) (polyval_dot h h)`
    (fun th -> REWRITE_TAC[th]) THENL
    [REWRITE_TAC[POLYVAL_DOT_H4_EQ_LOCAL]; ALL_TAC] THEN
  SUBGOAL_THEN
    `polyval_dot (polyval_dot (h:int128) h) h = polyval_dot h (polyval_dot h h)`
    (fun th -> REWRITE_TAC[th]) THENL
    [REWRITE_TAC[polyval_dot] THEN REWRITE_TAC[WORD_PMUL_SYM]; ALL_TAC] THEN
  (* Apply 5-block bridge. *)
  MP_TAC(SPECL
    [`word_reversefields 8 (word_xor xi ct1):int128`;
     `word_reversefields 8 ct2:int128`; `word_reversefields 8 ct3:int128`;
     `word_reversefields 8 ct4:int128`; `word_reversefields 8 ctm5:int128`;
     `h:int128`; `h1k:int128`;
     `word_join (word 0:(64)word) (word_subword (h1k:(128)word) (64,64):(64)word):(128)word`;
     `h3k:int128`;
     `word_join (word 0:(64)word) (word_subword (h3k:(128)word) (64,64):(64)word):(128)word`;
     `h5k:int128`]
    GHASH_5BLOCK_KARATSUBA_EQ_POLYVAL_ACC) THEN
  SUBGOAL_THEN
    `word_subword (word_join (word 0:(64)word) (word_subword (h1k:(128)word) (64,64):(64)word):(128)word) (0,64):(64)word =
     karatsuba_mid (polyval_dot h h)`
    (fun th -> REWRITE_TAC[th]) THENL [
    SUBGOAL_THEN
      `word_subword (word_join (word 0:(64)word) (word_subword (h1k:(128)word) (64,64):(64)word):(128)word) (0,64):(64)word =
       word_subword (h1k:(128)word) (64,64):(64)word`
      (fun th -> REWRITE_TAC[th]) THENL [CONV_TAC WORD_BLAST; ASM_REWRITE_TAC[]]; ALL_TAC ] THEN
  SUBGOAL_THEN
    `word_subword (word_join (word 0:(64)word) (word_subword (h3k:(128)word) (64,64):(64)word):(128)word) (0,64):(64)word =
     karatsuba_mid (polyval_dot (polyval_dot h h) (polyval_dot h h))`
    (fun th -> REWRITE_TAC[th]) THENL [
    SUBGOAL_THEN
      `word_subword (word_join (word 0:(64)word) (word_subword (h3k:(128)word) (64,64):(64)word):(128)word) (0,64):(64)word =
       word_subword (h3k:(128)word) (64,64):(64)word`
      (fun th -> REWRITE_TAC[th]) THENL [CONV_TAC WORD_BLAST; ASM_REWRITE_TAC[]]; ALL_TAC ] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN
  REWRITE_TAC[ghash_5block_karatsuba; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[SWAPHALVES128_SUBWORD_LO; SWAPHALVES128_SUBWORD_HI] THEN
  SUBGOAL_THEN
    `word_subword (word_join (word 0:(64)word) (karatsuba_mid (polyval_dot h h):(64)word):(128)word) (0,64):(64)word =
     karatsuba_mid (polyval_dot h h)`
    (fun th -> REWRITE_TAC[th]) THENL [CONV_TAC WORD_BLAST; ALL_TAC] THEN
  SUBGOAL_THEN
    `word_subword (word_join (word 0:(64)word) (karatsuba_mid (polyval_dot (polyval_dot h h) (polyval_dot h h)):(64)word):(128)word) (0,64):(64)word =
     karatsuba_mid (polyval_dot (polyval_dot h h) (polyval_dot h h))`
    (fun th -> REWRITE_TAC[th]) THENL [CONV_TAC WORD_BLAST; ALL_TAC] THEN
  REWRITE_TAC[GSYM karatsuba_mid] THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
  CONV_TAC SYM_CONV THEN
  FIRST_ASSUM(fun th ->
    if is_eq(concl th) && rand(concl th) = `final_xi:(128)word` &&
       (try (let l = lhs(concl th) in is_comb l &&
             (let r = rator l in not(is_comb r && (try fst(dest_const(rator r)) = "read" with _ -> false))))
        with _ -> false)
    then SUBST1_TAC(SYM th) else NO_TAC) THEN
  REWRITE_TAC[REV64_LOWER_LANE; REV64_UPPER_LANE; REV8_JOIN_FOLD] THEN
  MATCH_MP_TAC(MESON[]
    `x = y ==> word_reversefields 8 x = word_reversefields 8 y:(128)word`) THEN
  REWRITE_TAC[WORD_SWAP_HALVES_INVOLUTION] THEN
  CONV_TAC(LAND_CONV(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
  REWRITE_TAC[WORD_INSERT_AS_JOIN_LO; WORD_INSERT_AS_JOIN_HI;
              KAR_SUBWORD_LEMMA; WORD_SWAP_HALVES_INVOLUTION;
              WORD_OR_REFL; WORD_XOR_ASSOC; WORD_SUBWORD_XOR;
              SWAPHALVES128_SUBWORD_LO; SWAPHALVES128_SUBWORD_HI] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[HALFSWAP_XOR; GSYM WORD_REVERSEFIELDS_XOR_8_128;
              WORD_XOR_0; WORD_XOR_ASSOC;
              REV8_JOIN_FOLD; REVERSEFIELDS8_SUBWORD_LO; REVERSEFIELDS8_SUBWORD_HI] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  CONV_TAC(TOP_DEPTH_CONV PMUL_NORM_CONV) THEN
  SUBGOAL_THEN
    `word_subword (word 0:(128)word) (0,64):(64)word = word 0 /\
     word_subword (word 0:(128)word) (64,64):(64)word = word 0`
    (fun th -> REWRITE_TAC[th]) THENL [CONJ_TAC THEN CONV_TAC WORD_BLAST; ALL_TAC] THEN
  REWRITE_TAC[WORD_XOR_0; WORD_XOR_0_LEFT] THEN
  REWRITE_TAC[karatsuba_mid; WORD_REVERSEFIELDS_XOR_8_128; WORD_SUBWORD_XOR] THEN
  (* 22 atomic ABBREVs *)
  ABBREV_TAC `(c1lo:(64)word) = word_subword (word_reversefields 8 (ct1:(128)word)) (0,64)` THEN
  ABBREV_TAC `(c1hi:(64)word) = word_subword (word_reversefields 8 (ct1:(128)word)) (64,64)` THEN
  ABBREV_TAC `(c2lo:(64)word) = word_subword (word_reversefields 8 (ct2:(128)word)) (0,64)` THEN
  ABBREV_TAC `(c2hi:(64)word) = word_subword (word_reversefields 8 (ct2:(128)word)) (64,64)` THEN
  ABBREV_TAC `(c3lo:(64)word) = word_subword (word_reversefields 8 (ct3:(128)word)) (0,64)` THEN
  ABBREV_TAC `(c3hi:(64)word) = word_subword (word_reversefields 8 (ct3:(128)word)) (64,64)` THEN
  ABBREV_TAC `(c4lo:(64)word) = word_subword (word_reversefields 8 (ct4:(128)word)) (0,64)` THEN
  ABBREV_TAC `(c4hi:(64)word) = word_subword (word_reversefields 8 (ct4:(128)word)) (64,64)` THEN
  ABBREV_TAC `(c5lo:(64)word) = word_subword (word_reversefields 8 (ctm5:(128)word)) (0,64)` THEN
  ABBREV_TAC `(c5hi:(64)word) = word_subword (word_reversefields 8 (ctm5:(128)word)) (64,64)` THEN
  ABBREV_TAC `(xilo:(64)word) = word_subword (word_reversefields 8 (xi:(128)word)) (0,64)` THEN
  ABBREV_TAC `(xihi:(64)word) = word_subword (word_reversefields 8 (xi:(128)word)) (64,64)` THEN
  ABBREV_TAC `(hd0:(64)word) = word_subword (h:(128)word) (0,64)` THEN
  ABBREV_TAC `(hd1:(64)word) = word_subword (h:(128)word) (64,64)` THEN
  ABBREV_TAC `(he0:(64)word) = word_subword ((polyval_dot h h):(128)word) (0,64)` THEN
  ABBREV_TAC `(he1:(64)word) = word_subword ((polyval_dot h h):(128)word) (64,64)` THEN
  ABBREV_TAC `(hf0:(64)word) = word_subword ((polyval_dot h (polyval_dot h h)):(128)word) (0,64)` THEN
  ABBREV_TAC `(hf1:(64)word) = word_subword ((polyval_dot h (polyval_dot h h)):(128)word) (64,64)` THEN
  ABBREV_TAC `(hg0:(64)word) = word_subword ((polyval_dot (polyval_dot h h) (polyval_dot h h)):(128)word) (0,64)` THEN
  ABBREV_TAC `(hg1:(64)word) = word_subword ((polyval_dot (polyval_dot h h) (polyval_dot h h)):(128)word) (64,64)` THEN
  ABBREV_TAC `(hh0:(64)word) = word_subword ((polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h):(128)word) (0,64)` THEN
  ABBREV_TAC `(hh1:(64)word) = word_subword ((polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h):(128)word) (64,64)` THEN
  ASM_REWRITE_TAC[] THEN
  (* 15 inner pmul ABBREVs *)
  ABBREV_TAC `(w1lo:(128)word) = word_pmul (word_xor (xilo:(64)word) (c1lo:(64)word)) (hh0:(64)word)` THEN
  ABBREV_TAC `(w1hi:(128)word) = word_pmul (word_xor (xihi:(64)word) (c1hi:(64)word)) (hh1:(64)word)` THEN
  ABBREV_TAC `(w1md:(128)word) = word_pmul (word_xor (word_xor (xihi:(64)word) (c1hi:(64)word)) (word_xor (xilo:(64)word) (c1lo:(64)word))) (word_xor (hh0:(64)word) (hh1:(64)word))` THEN
  ABBREV_TAC `(w2lo:(128)word) = word_pmul (c2lo:(64)word) (hg0:(64)word)` THEN
  ABBREV_TAC `(w2hi:(128)word) = word_pmul (c2hi:(64)word) (hg1:(64)word)` THEN
  ABBREV_TAC `(w2md:(128)word) = word_pmul (word_xor (c2hi:(64)word) (c2lo:(64)word)) (word_xor (hg0:(64)word) (hg1:(64)word))` THEN
  ABBREV_TAC `(w3lo:(128)word) = word_pmul (c3lo:(64)word) (hf0:(64)word)` THEN
  ABBREV_TAC `(w3hi:(128)word) = word_pmul (c3hi:(64)word) (hf1:(64)word)` THEN
  ABBREV_TAC `(w3md:(128)word) = word_pmul (word_xor (c3hi:(64)word) (c3lo:(64)word)) (word_xor (hf0:(64)word) (hf1:(64)word))` THEN
  ABBREV_TAC `(w4lo:(128)word) = word_pmul (c4lo:(64)word) (he0:(64)word)` THEN
  ABBREV_TAC `(w4hi:(128)word) = word_pmul (c4hi:(64)word) (he1:(64)word)` THEN
  ABBREV_TAC `(w4md:(128)word) = word_pmul (word_xor (c4hi:(64)word) (c4lo:(64)word)) (word_xor (he0:(64)word) (he1:(64)word))` THEN
  ABBREV_TAC `(w5lo:(128)word) = word_pmul (c5lo:(64)word) (hd0:(64)word)` THEN
  ABBREV_TAC `(w5hi:(128)word) = word_pmul (c5hi:(64)word) (hd1:(64)word)` THEN
  ABBREV_TAC `(w5md:(128)word) = word_pmul (word_xor (c5hi:(64)word) (c5lo:(64)word)) (word_xor (hd0:(64)word) (hd1:(64)word))` THEN
  REWRITE_TAC[DOUBLE_SUBWORD_JOIN; DOUBLE_SUBWORD_JOIN_HI; WORD_SUBWORD_XOR] THEN
  SUBGOAL_THEN
    `word_pmul (word_xor (xihi:(64)word) (word_xor (c1hi:(64)word) (word_xor (xilo:(64)word) (c1lo:(64)word)))) (word_xor (hh0:(64)word) (hh1:(64)word)):(128)word = w1md`
    (fun th -> REWRITE_TAC[th]) THENL
    [EXPAND_TAC "w1md" THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  (* 30 z-vars *)
  ABBREV_TAC `(w1lo_l:(64)word) = word_subword (w1lo:(128)word) (0,64)` THEN
  ABBREV_TAC `(w1lo_h:(64)word) = word_subword (w1lo:(128)word) (64,64)` THEN
  ABBREV_TAC `(w1hi_l:(64)word) = word_subword (w1hi:(128)word) (0,64)` THEN
  ABBREV_TAC `(w1hi_h:(64)word) = word_subword (w1hi:(128)word) (64,64)` THEN
  ABBREV_TAC `(w1md_l:(64)word) = word_subword (w1md:(128)word) (0,64)` THEN
  ABBREV_TAC `(w1md_h:(64)word) = word_subword (w1md:(128)word) (64,64)` THEN
  ABBREV_TAC `(w2lo_l:(64)word) = word_subword (w2lo:(128)word) (0,64)` THEN
  ABBREV_TAC `(w2lo_h:(64)word) = word_subword (w2lo:(128)word) (64,64)` THEN
  ABBREV_TAC `(w2hi_l:(64)word) = word_subword (w2hi:(128)word) (0,64)` THEN
  ABBREV_TAC `(w2hi_h:(64)word) = word_subword (w2hi:(128)word) (64,64)` THEN
  ABBREV_TAC `(w2md_l:(64)word) = word_subword (w2md:(128)word) (0,64)` THEN
  ABBREV_TAC `(w2md_h:(64)word) = word_subword (w2md:(128)word) (64,64)` THEN
  ABBREV_TAC `(w3lo_l:(64)word) = word_subword (w3lo:(128)word) (0,64)` THEN
  ABBREV_TAC `(w3lo_h:(64)word) = word_subword (w3lo:(128)word) (64,64)` THEN
  ABBREV_TAC `(w3hi_l:(64)word) = word_subword (w3hi:(128)word) (0,64)` THEN
  ABBREV_TAC `(w3hi_h:(64)word) = word_subword (w3hi:(128)word) (64,64)` THEN
  ABBREV_TAC `(w3md_l:(64)word) = word_subword (w3md:(128)word) (0,64)` THEN
  ABBREV_TAC `(w3md_h:(64)word) = word_subword (w3md:(128)word) (64,64)` THEN
  ABBREV_TAC `(w4lo_l:(64)word) = word_subword (w4lo:(128)word) (0,64)` THEN
  ABBREV_TAC `(w4lo_h:(64)word) = word_subword (w4lo:(128)word) (64,64)` THEN
  ABBREV_TAC `(w4hi_l:(64)word) = word_subword (w4hi:(128)word) (0,64)` THEN
  ABBREV_TAC `(w4hi_h:(64)word) = word_subword (w4hi:(128)word) (64,64)` THEN
  ABBREV_TAC `(w4md_l:(64)word) = word_subword (w4md:(128)word) (0,64)` THEN
  ABBREV_TAC `(w4md_h:(64)word) = word_subword (w4md:(128)word) (64,64)` THEN
  ABBREV_TAC `(w5lo_l:(64)word) = word_subword (w5lo:(128)word) (0,64)` THEN
  ABBREV_TAC `(w5lo_h:(64)word) = word_subword (w5lo:(128)word) (64,64)` THEN
  ABBREV_TAC `(w5hi_l:(64)word) = word_subword (w5hi:(128)word) (0,64)` THEN
  ABBREV_TAC `(w5hi_h:(64)word) = word_subword (w5hi:(128)word) (64,64)` THEN
  ABBREV_TAC `(w5md_l:(64)word) = word_subword (w5md:(128)word) (0,64)` THEN
  ABBREV_TAC `(w5md_h:(64)word) = word_subword (w5md:(128)word) (64,64)` THEN
  ASM_REWRITE_TAC[] THEN
  (* Normalize LHS mid-pmuls to the abbreviated w?md (swapped xor arg order). *)
  SUBGOAL_THEN `word_pmul (word_xor (c2lo:(64)word) (c2hi:(64)word)) (word_xor (hg0:(64)word) (hg1:(64)word)):(128)word = w2md`
    (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "w2md" THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  SUBGOAL_THEN `word_pmul (word_xor (c3lo:(64)word) (c3hi:(64)word)) (word_xor (hf0:(64)word) (hf1:(64)word)):(128)word = w3md`
    (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "w3md" THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  SUBGOAL_THEN `word_pmul (word_xor (c4lo:(64)word) (c4hi:(64)word)) (word_xor (he0:(64)word) (he1:(64)word)):(128)word = w4md`
    (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "w4md" THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  SUBGOAL_THEN `word_pmul (word_xor (c5lo:(64)word) (c5hi:(64)word)) (word_xor (hd0:(64)word) (hd1:(64)word)):(128)word = w5md`
    (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "w5md" THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  SUBGOAL_THEN `word_pmul (word_xor (xilo:(64)word) (word_xor (c1lo:(64)word) (word_xor (xihi:(64)word) (c1hi:(64)word)))) (word_xor (hh0:(64)word) (hh1:(64)word)):(128)word = w1md`
    (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "w1md" THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  (* qS: small Barrett pmul; fold both XOR orderings. *)
  ABBREV_TAC `(qS:(128)word) = word_pmul (word_xor (w5lo_l:(64)word) (word_xor w4lo_l (word_xor w3lo_l (word_xor w2lo_l w1lo_l)))) (word 13979173243358019584:(64)word)` THEN
  SUBGOAL_THEN `word_pmul (word_xor (w1lo_l:(64)word) (word_xor w2lo_l (word_xor w3lo_l (word_xor w4lo_l w5lo_l)))) (word 13979173243358019584:(64)word):(128)word = qS`
    (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "qS" THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  (* qB: big Barrett pmul; fold the LHS-order copy via bubble_sort_conv. *)
  ABBREV_TAC `(qB:(128)word) = word_pmul
    (word_xor (w5md_l:(64)word) (word_xor w4md_l (word_xor w3md_l (word_xor w2md_l (word_xor w1md_l (word_xor w5lo_l (word_xor w4lo_l (word_xor w3lo_l (word_xor w2lo_l (word_xor w1lo_l (word_xor w5hi_l (word_xor w4hi_l (word_xor w3hi_l (word_xor w2hi_l (word_xor w1hi_l (word_xor (word_subword (qS:(128)word) (0,64)) (word_xor w5lo_h (word_xor w4lo_h (word_xor w3lo_h (word_xor w2lo_h (w1lo_h))))))))))))))))))))) (word 13979173243358019584:(64)word)` THEN
  SUBGOAL_THEN
    `word_pmul (word_xor (w1lo_h:(64)word) (word_xor w2lo_h (word_xor w3lo_h (word_xor w4lo_h (word_xor w5lo_h (word_xor w1md_l (word_xor w2md_l (word_xor w3md_l (word_xor w4md_l (word_xor w5md_l (word_xor w1hi_l (word_xor w2hi_l (word_xor w3hi_l (word_xor w4hi_l (word_xor w5hi_l (word_xor w1lo_l (word_xor w2lo_l (word_xor w3lo_l (word_xor w4lo_l (word_xor w5lo_l ((word_subword (qS:(128)word) (0,64))))))))))))))))))))))) (word 13979173243358019584:(64)word):(128)word = qB`
    (fun th -> REWRITE_TAC[th]) THENL
    [EXPAND_TAC "qB" THEN AP_THM_TAC THEN AP_TERM_TAC THEN
     CONV_TAC(BINOP_CONV bubble_sort_conv) THEN REFL_TAC; ALL_TAC];;

(* Step 1+2: establish the four spec-form ct folds F1..F4 and fold them into
   the RHS ghash list. *)
let GCM_5B_FOLD_SPEC_CTS : tactic =
  (* F1 *)
  SUBGOAL_THEN
   `word_xor pt1 (aes256_encrypt ivec [rk0;rk1;rk2;rk3;rk4;rk5;rk6;rk7;rk8;rk9;rk10;rk11;rk12;rk13;rk14]) = ct1`
   ASSUME_TAC THENL
   [EXPAND_TAC "ct1" THEN
    (* June base: ct1's def is left-assoc; left-associate the EXPAND output. *)
    REWRITE_TAC[AES256_ENCRYPT_UNFOLD; LET_DEF; LET_END_DEF; WORD_XOR_ASSOC] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* F2 *)
  SUBGOAL_THEN
   `word_xor pt2 (aes256_encrypt (gcm_ctr_inc ivec) [rk0;rk1;rk2;rk3;rk4;rk5;rk6;rk7;rk8;rk9;rk10;rk11;rk12;rk13;rk14]) = ct2`
   ASSUME_TAC THENL
   [CONV_TAC SYM_CONV THEN GCM_5BLOCK_CT2_STEP_TAC; ALL_TAC] THEN
  (* F3 *)
  SUBGOAL_THEN
   `word_xor pt3 (aes256_encrypt (gcm_ctr_inc (gcm_ctr_inc ivec)) [rk0;rk1;rk2;rk3;rk4;rk5;rk6;rk7;rk8;rk9;rk10;rk11;rk12;rk13;rk14]) = ct3`
   ASSUME_TAC THENL
   [CONV_TAC SYM_CONV THEN GCM_5BLOCK_CT3_STEP_TAC; ALL_TAC] THEN
  (* F4 *)
  SUBGOAL_THEN
   `word_xor pt4 (aes256_encrypt (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ivec))) [rk0;rk1;rk2;rk3;rk4;rk5;rk6;rk7;rk8;rk9;rk10;rk11;rk12;rk13;rk14]) = ct4`
   ASSUME_TAC THENL
   [CONV_TAC SYM_CONV THEN GCM_5BLOCK_CT4_STEP_TAC; ALL_TAC] THEN
  (* fold the four into the RHS ghash list only: pick the F-fact for each ctN
     (LHS = word_xor ptN (aes256_encrypt ...)) and GEN_REWRITE the RHS. *)
  (fun (asl,w) ->
     let getf n = snd(find (fun (_,th) ->
       is_eq(concl th) && rand(concl th)=mk_var("ct"^string_of_int n,`:(128)word`) &&
       (let l=lhand(concl th) in
        (try fst(dest_const(rator(rator l)))="word_xor" with _->false) &&
        (try fst(dest_const(repeat rator (rand l)))="aes256_encrypt" with _->false))) asl) in
     GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [getf 1; getf 2; getf 3; getf 4] (asl,w));;

(* Step 4: b0-general mask-register collapse, applied to ALL assumptions
   (the 5-block sim bakes the uncollapsed mask register into final_xi). *)
let GCM_5B_MASK_COLLAPSE_ASMS : tactic =
  SUBGOAL_THEN `1 <= (byte_len:num) /\ byte_len <= 16` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(fun bth -> if concl bth = `1 <= (byte_len:num) /\ byte_len <= 16` then
    RULE_ASSUM_TAC(REWRITE_RULE[GEN `b0:int128` (MP (SPEC_ALL FIVEBLOCK_MASK_REG) bth)]) else NO_TAC);;

(* Step 5: bridge the machine block-5 keystream (collapsed +4 counter, baked
   into final_xi) to the spec ct5.  Extract the machine keystream from the
   final_xi defining assumption and prove (machine ks5 = ct5), then fold it
   into every assumption (incl final_xi). *)
let GCM_5B_KS5_FOLD : tactic = fun (asl,w) ->
  let substr sub s =
    let ls=String.length s and lb=String.length sub in
    let rec go i = if i+lb>ls then false
                   else if String.sub s i lb = sub then true else go(i+1) in go 0 in
  let fxidef = snd(find (fun (_,th) ->
    is_eq(concl th) && (try rand(concl th)=`final_xi:(128)word` with _->false)) asl) in
  let body = lhs(concl fxidef) in
  (* June base: pick the SHORTEST pt5/aese word_xor that ALSO contains rk14 — i.e.
     the full block-5 keystream `word_xor pt5 (word_xor (aese..rk13) rk14)`.  The
     post-b9a430b normal form also exposes a shorter pre-whitening (no rk14)
     pt5/aese subterm; requiring rk14 avoids picking that wrong one. *)
  let best = ref None in
  let rec walk t =
    (try let s=string_of_term t in
      if substr "pt5" s && substr "aese" s && substr "rk14" s &&
         (try fst(dest_const(repeat rator t))="word_xor" with _->false) &&
         (match !best with None->true | Some b -> String.length s < String.length(string_of_term b))
      then best := Some t
     with _->());
    (match t with Comb(a,b)->walk a; walk b | Abs(_,b)->walk b | _->()) in
  walk body;
  let ks5 = (match !best with Some t->t | None->failwith "KS5_FOLD: ks5 not found") in
  let bri = WORD_BLAST `word_bytereverse (word_bytereverse (x:(32)word)) = x` in
  let add4 = WORD_RULE `word_add (word_add (word_add (word_add (x:(32)word) (word 1)) (word 1)) (word 1)) (word 1) = word_add x (word 4)` in
  (SUBGOAL_THEN (mk_eq(ks5, `ct5:(128)word`)) ASSUME_TAC THENL
    [(* mirror band-4 ct4 / GCM_5B_MASKED_CT5_CLOSE counter peel: orient spec,
        unfold AES, left-assoc, peel pt5/rk14, peel aese layers, bridge the
        collapsed +4 counter (rev∘rev=id, rev8→bytereverse, nested-insert
        collapse, double-bytereverse cancel, +1×4→+4, word_join→word_insert). *)
     CONV_TAC SYM_CONV THEN EXPAND_TAC "ct5" THEN
     REWRITE_TAC[AES256_ENCRYPT_UNFOLD] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
     REWRITE_TAC[WORD_XOR_ASSOC] THEN
     AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
     REPEAT(AP_THM_TAC ORELSE AP_TERM_TAC) THEN
     REWRITE_TAC[gcm_ctr_inc] THEN
     REWRITE_TAC[WORD_REVERSEFIELDS_REVERSEFIELDS; WORD_REVERSEFIELDS_8_BYTEREVERSE_32] THEN
     REWRITE_TAC[INSERT_SUBWORD; INSERT_IDEM] THEN
     REWRITE_TAC[bri] THEN REWRITE_TAC[add4] THEN
     REWRITE_TAC[CTR_WORD_INSERT];
     ALL_TAC] THEN
   FIRST_ASSUM(fun th ->
     if is_eq(concl th) && rand(concl th)=`ct5:(128)word` &&
        (try fst(dest_const(repeat rator (lhs(concl th))))="word_xor" with _->false) &&
        String.length(string_of_term(lhs(concl th))) > 1000
     then RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th] else NO_TAC))
  (asl,w);;

(* June-2026 base: the per-half XOR-AC closer, mirroring band-4's GCM_4B_HALF_CLOSE.
   Single-pass bubble_sort_conv cannot fully sort the 21-atom qB chain; fold the
   5 mids (w1md=hh, w2md=hg, w3md=hf, w4md=he, w5md=hd), then qS (5 atoms), then
   qB (21 atoms), each up-to-AC via bubble_fix, before the fixpoint sort.  bubble_fix
   is defined in gcm_three_block_closers.ml (loaded above). *)
let GCM_5B_FOLD_MIDS_TAC : tactic =
  fun (asl,gg) ->
    let rec finds hd t acc = match t with
      | Comb(Comb(Const("word_pmul",_),a),x) when x = hd ->
          a :: (finds hd a (finds hd x acc))
      | Comb(l,r) -> finds hd l (finds hd r acc)
      | Abs(_,b) -> finds hd b acc | _ -> acc in
    let hhw = `word_xor (hh0:(64)word) hh1`
    and hgw = `word_xor (hg0:(64)word) hg1`
    and hfw = `word_xor (hf0:(64)word) hf1`
    and hew = `word_xor (he0:(64)word) he1`
    and hdw = `word_xor (hd0:(64)word) hd1` in
    let mk tgt hd arg =
      SUBGOAL_THEN
        (mk_eq(list_mk_comb(`word_pmul:(64)word->(64)word->(128)word`,[arg;hd]),tgt))
        (fun th -> REWRITE_TAC[th]) THENL
       [EXPAND_TAC (fst(dest_var tgt)) THEN AP_THM_TAC THEN AP_TERM_TAC THEN
        CONV_TAC WORD_RULE; ALL_TAC] in
    (EVERY ((map (mk `w1md:(128)word` hhw) (setify(finds hhw gg [])))
          @ (map (mk `w2md:(128)word` hgw) (setify(finds hgw gg [])))
          @ (map (mk `w3md:(128)word` hfw) (setify(finds hfw gg [])))
          @ (map (mk `w4md:(128)word` hew) (setify(finds hew gg [])))
          @ (map (mk `w5md:(128)word` hdw) (setify(finds hdw gg []))))) (asl,gg);;
let GCM_5B_FOLD_TO tgt natoms : tactic =
  let w64 = `word 13979173243358019584:(64)word` in
  fun (asl,gg) ->
    let rec finds t acc = match t with
      | Comb(Comb(Const("word_pmul",_),a),x) when x = w64 ->
          a :: (finds a (finds x acc))
      | Comb(l,r) -> finds l (finds r acc) | Abs(_,b) -> finds b acc | _ -> acc in
    let rec at t = match t with
      | Comb(Comb(Const("word_xor",_),x),y) -> at x @ at y | _ -> [t] in
    let args = List.filter (fun a -> List.length(at a) = natoms) (setify(finds gg [])) in
    (EVERY (map (fun a ->
       FIRST [SUBGOAL_THEN
                (mk_eq(list_mk_comb(`word_pmul:(64)word->(64)word->(128)word`,[a;w64]),tgt))
                (fun th -> REWRITE_TAC[th]) THENL
               [EXPAND_TAC (fst(dest_var tgt)) THEN AP_THM_TAC THEN AP_TERM_TAC THEN
                CONV_TAC(BINOP_CONV bubble_fix) THEN REFL_TAC; ALL_TAC];
              ALL_TAC]) args)) (asl,gg);;
let GCM_5B_HALF_CLOSE : tactic =
  GCM_5B_FOLD_MIDS_TAC THEN ASM_REWRITE_TAC[] THEN
  GCM_5B_FOLD_TO `qS:(128)word` 5 THEN ASM_REWRITE_TAC[] THEN
  GCM_5B_FOLD_TO `qB:(128)word` 21 THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(BINOP_CONV bubble_fix) THEN REFL_TAC;;

(* The full GHASH closer: applied at the final GHASH conjunct. *)
let GCM_5B_GHASH_CLOSE : tactic =
  GCM_5B_FOLD_SPEC_CTS THEN
  REWRITE_TAC[GHASH_POLYVAL_ACC_5; POLYVAL_DOT_H5_EQ; GSYM WORD_REVERSEFIELDS_XOR_8_128] THEN
  GCM_5B_MASK_COLLAPSE_ASMS THEN
  GCM_5B_KS5_FOLD THEN
  GCM_5B_TAIL_NOFINAL THEN
  REWRITE_TAC[XI_HS_LO_5; XI_HS_HI_5] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `word_pmul (word_xor (xihi:(64)word) (word_xor c1hi (word_xor xilo c1lo)))
              (word_xor (hh0:(64)word) hh1):(128)word = w1md`
   (fun th -> REWRITE_TAC[th]) THENL
   [EXPAND_TAC "w1md" THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  BINOP_TAC THENL [GCM_5B_HALF_CLOSE; GCM_5B_HALF_CLOSE];;

(* --- The 5-block branch theorem. --- *)

(* Full assembled AES256_GCM_ENCRYPT_LT_5BLOCK_CORRECT proof (more_than_4),  *)
(* using the closers from gcm_five_block_closers.ml.                         *)

(* ct1 closer (counter = ivec, no inc). *)
let CT_CLOSE_5 nidx =
  let s13n = "s13_"^string_of_int nidx and ctn = "ct"^string_of_int nidx in
  EXPAND_TAC ctn THEN EXPAND_TAC s13n THEN
  REWRITE_TAC[AES256_ENCRYPT_UNFOLD; LET_DEF; LET_END_DEF; WORD_XOR_ASSOC] THEN ASM_REWRITE_TAC[];;

(* masked-ct5 store conjunct closer: collapse the mask reg in the goal, peel
   word_or/word_and/word_xor down to the counter identity (machine +4 form vs
   spec gcm_ctr_inc^4), and discharge it with the nested-insert collapse. *)
(* June-2026 base: mirror the band-4 ct4 counter peel.  The machine block-5
   keystream is `word_xor (word_xor pt5 aes) rk14` (left-assoc) over a collapsed
   +4 counter emitted as `word_reversefields 8` (not word_bytereverse), and the
   spec side is `word_xor pt5 (aes256_encrypt (gcm_ctr_inc^4 ivec) ...)`.
   Orient spec left, unfold AES, left-assoc, peel pt5/rk14, peel the aese/aesmc
   layers to the counter arg, then bridge gcm_ctr_inc^4 → the machine word_join
   form: rev∘rev = id, rev8→bytereverse, collapse nested inserts, cancel the
   double bytereverses, fold the four +1 into +4, and refold word_join→word_insert
   with CTR_WORD_INSERT. *)
let GCM_5B_MASKED_CT5_CLOSE : tactic =
  let bri = WORD_BLAST `word_bytereverse (word_bytereverse (x:(32)word)) = x` in
  let add4 = WORD_RULE `word_add (word_add (word_add (word_add (x:(32)word) (word 1)) (word 1)) (word 1)) (word 1) = word_add x (word 4)` in
  SUBGOAL_THEN `1 <= byte_len /\ byte_len <= 16` MP_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP FIVEBLOCK_MASK_REG th]) THEN
  REWRITE_TAC[NBLOCK_MASK_IDEM] THEN
  MATCH_MP_TAC(MESON[] `x = y ==> word_or (word_and x m) r = word_or (word_and y m) r:(128)word`) THEN
  CONV_TAC SYM_CONV THEN REWRITE_TAC[AES256_ENCRYPT_UNFOLD] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[WORD_XOR_ASSOC] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REPEAT(AP_THM_TAC ORELSE AP_TERM_TAC) THEN
  REWRITE_TAC[gcm_ctr_inc] THEN
  REWRITE_TAC[WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
  REWRITE_TAC[WORD_REVERSEFIELDS_8_BYTEREVERSE_32] THEN
  REWRITE_TAC[INSERT_SUBWORD; INSERT_IDEM] THEN
  REWRITE_TAC[bri] THEN REWRITE_TAC[add4] THEN
  REWRITE_TAC[CTR_WORD_INSERT];;

let AES256_GCM_ENCRYPT_LT_5BLOCK_CONCRETE = prove
 (gcm_5b_goal,
  (* ---- symbolic simulation (store-based ct abbreviation) ---- *)
  GCM_INIT_TAC GCM_CBZ_LEMMA5 THEN GCM_PROLOGUE_TAC THEN GCM_RUN 20 263 THEN
  GCM_INLOOP_GUARD_TAC GCM_X5_LEMMA5 THEN GCM_RUN 267 272 THEN
  GCM_BND16 GCM_X5TAIL_LEMMA5 THEN
  GCM_RUN_THEN GCM_CASCADE5_TAC 273 321 THEN
  abbrev_ct_from_store 0 1 THEN abbrev_ct_from_store 16 2 THEN
  GCM_RUN 322 348 THEN abbrev_ct_from_store 32 3 THEN
  GCM_RUN 349 362 THEN abbrev_ct_from_store 48 4 THEN
  SUBGOAL_THEN `1 <= byte_len /\ byte_len <= 16` MP_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP FIVEBLOCK_MASK_REG th])) THEN
  GCM_RUN 363 403 THEN
  GCM_NBLOCK_POST_SIM_NORMALIZE_TAC THEN ABBREV_FINAL_XI_TAC THEN
  ARM_STEPS_TAC AES256_GCM_EXEC (404--411) THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ENSURES_FINAL_STATE_TAC THEN
  SUBGOAL_THEN `1 <= byte_len /\ byte_len <= 16` MP_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP FIVEBLOCK_MASK_REG th]) THEN
  ASM_SIMP_TAC[FIVEBLOCK_USHR] THEN
  (* ---- six conjuncts: ct1..ct4, masked-ct5, GHASH ---- *)
  CONJ_TAC THENL [CT_CLOSE_5 1; ALL_TAC] THEN
  CONJ_TAC THENL [CONV_TAC SYM_CONV THEN GCM_5BLOCK_CT2_STEP_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [CONV_TAC SYM_CONV THEN GCM_5BLOCK_CT3_STEP_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [CONV_TAC SYM_CONV THEN GCM_5BLOCK_CT4_STEP_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [GCM_5B_MASKED_CT5_CLOSE; ALL_TAC] THEN
  (* ---- ct5 abbreviation (spec form) so the closer's ctm5 works ---- *)
  ABBREV_TAC `ct5 = word_xor pt5
    (aes256_encrypt (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ivec)))) [rk0;rk1;rk2;rk3;rk4;rk5;rk6;rk7;rk8;rk9;rk10;rk11;rk12;rk13;rk14]):(128)word` THEN
  (* ---- GHASH conjunct ---- *)
  GCM_5B_GHASH_CLOSE);;

(* ========================================================================= *)
(* The L256_enc_blocks_more_than_5 branch (6-block: five full blocks +       *)
(* partial block 6, total 81..96 bytes) of the single binary, proved as a    *)
(* standalone theorem and applied exactly as the XTS length-band lemmas are. *)
(* Reuses the six-block masked closers from gcm_six_block_closers.ml.        *)
(* ========================================================================= *)

needs "arm/proofs/utils/gcm_six_block_closers.ml";;

(* --- 6-block-branch length/cascade helpers (thresholds over 80+byte_len) --- *)

let GCM_CBZ_LEMMA6 = prove
 (`1 <= byte_len /\ byte_len <= 16 ==> ~(val(word(640+8*byte_len):int64) = 0)`,
  STRIP_TAC THEN SUBGOAL_THEN `val(word(640+8*byte_len):int64) = 640+8*byte_len` SUBST1_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC;
    ASM_ARITH_TAC]);;

let GCM_WSUB6 = prove
 (`byte_len <= 16 ==> word_sub (word (80+byte_len):int64) (word 1) = word (79 + byte_len)`,
  CONV_TAC WORD_RULE);;

let GCM_X6_LEMMA6 = prove
 (`1 <= byte_len /\ byte_len <= 16 ==>
   word_add (word_and (word_sub (word_ushr (word (640+8*byte_len):int64) 3) (word 1))
                      (word 18446744073709551488)) in_ptr = in_ptr`,
  STRIP_TAC THEN
  SUBGOAL_THEN `word_ushr (word (640+8*byte_len):int64) 3 = word (80+byte_len)` SUBST1_TAC THENL
   [ASM_SIMP_TAC[SIXBLOCK_USHR]; ALL_TAC] THEN
  ASM_SIMP_TAC[GCM_WSUB6] THEN
  SUBGOAL_THEN `word_and (word (79+byte_len):int64) (word 18446744073709551488) = word 0` SUBST1_TAC THENL
   [MATCH_MP_TAC GCM_ANDMASK0 THEN ASM_ARITH_TAC; ALL_TAC] THEN
  CONV_TAC WORD_RULE);;

let GCM_X6TAIL_LEMMA6 = prove
 (`byte_len <= 16 ==>
   word_sub (word_add in_ptr (word_ushr (word (640+8*byte_len):int64) 3)) in_ptr = word (80+byte_len)`,
  ASM_SIMP_TAC[SIXBLOCK_USHR] THEN CONV_TAC WORD_RULE);;

(* Cascade for more_than_5: total lanes = 80+byte_len (81..96).  The b.gt #112
   and #96 fall through (total <= 96), the b.gt #80 is taken (total >= 81) into
   .more_than_5.  FALSE thresholds = {96, 112}; TRUE threshold = 80. *)
let GCM_CASC6_FALSE = prove
 (`!byte_len t. byte_len <= 16 /\ 96 <= t /\ t <= 112 ==>
    ((~(val (word_sub (word (80+byte_len):int64) (word t)) = 0) /\
      (ival (word_sub (word (80+byte_len):int64) (word t)) < &0 <=>
       ~(ival (word (80+byte_len):int64) - &t = ival (word_sub (word (80+byte_len):int64) (word t)))))
     <=> F)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `ival(word (80+byte_len):int64) = &(80+byte_len)` ASSUME_TAC THENL
   [MATCH_MP_TAC NBLOCK_IVAL_WORD_SMALL THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `word_sub (word (80+byte_len):int64) (word t) = iword(&(80+byte_len) - &t)` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM IWORD_INT_SUB; WORD_IWORD]; ALL_TAC] THEN
  SUBGOAL_THEN `ival(iword(&(80+byte_len) - &t):int64) = &(80+byte_len) - &t` ASSUME_TAC THENL
   [MATCH_MP_TAC IVAL_IWORD THEN REWRITE_TAC[DIMINDEX_64] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_SUB_CONV) THEN
    SUBGOAL_THEN `&(80+byte_len):int <= &96 /\ &96:int <= &t /\ &t:int <= &112` MP_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN INT_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[VAL_EQ_0; GSYM IVAL_EQ_0] THEN
  SUBGOAL_THEN `&(80+byte_len):int <= &96 /\ &96:int <= &t` MP_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN INT_ARITH_TAC);;

let GCM_CASC6_TRUE = prove
 (`1 <= byte_len /\ byte_len <= 16 ==>
    ((~(val (word_sub (word (80+byte_len):int64) (word 80)) = 0) /\
      (ival (word_sub (word (80+byte_len):int64) (word 80)) < &0 <=>
       ~(ival (word (80+byte_len):int64) - &80 = ival (word_sub (word (80+byte_len):int64) (word 80)))))
     <=> T)`,
  STRIP_TAC THEN
  SUBGOAL_THEN `ival(word (80+byte_len):int64) = &(80+byte_len)` ASSUME_TAC THENL
   [MATCH_MP_TAC NBLOCK_IVAL_WORD_SMALL THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `word_sub (word (80+byte_len):int64) (word 80) = iword(&(80+byte_len) - &80)` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM IWORD_INT_SUB; WORD_IWORD]; ALL_TAC] THEN
  SUBGOAL_THEN `ival(iword(&(80+byte_len) - &80):int64) = &(80+byte_len) - &80` ASSUME_TAC THENL
   [MATCH_MP_TAC IVAL_IWORD THEN REWRITE_TAC[DIMINDEX_64] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_SUB_CONV) THEN
    SUBGOAL_THEN `&(80+byte_len):int <= &96` MP_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN INT_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[VAL_EQ_0; GSYM IVAL_EQ_0] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_ADD] THEN
  SUBGOAL_THEN `&1:int <= &byte_len` MP_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN INT_ARITH_TAC);;

let GCM_CASCADE6_TAC : tactic =
  FIRST_X_ASSUM(fun bl16 -> if concl bl16 = `byte_len <= 16` then
    FIRST_X_ASSUM(fun bl1 -> if concl bl1 = `1 <= byte_len` then
      RULE_ASSUM_TAC(REWRITE_RULE(
        (map (fun t -> MATCH_MP GCM_CASC6_FALSE (CONJ bl16
                (CONJ (ARITH_RULE(vsubst[mk_numeral(num_of_int t),`t:num`] `96 <= t`))
                      (ARITH_RULE(vsubst[mk_numeral(num_of_int t),`t:num`] `t <= 112`)))))
             [96;112]) @
        [MATCH_MP GCM_CASC6_TRUE (CONJ bl1 bl16); COND_CLAUSES])) THEN
      ASSUME_TAC bl1 THEN ASSUME_TAC bl16
    else NO_TAC)
  else NO_TAC);;

(* --- The 6-block branch goal (five full + one partial block). --- *)

let gcm_6b_goal = `!in_ptr out_ptr xi_ptr ivec_ptr key_ptr htable_ptr
    (pt1:(128)word) (pt2:(128)word) (pt3:(128)word) (pt4:(128)word) (pt5:(128)word) (pt6:(128)word)
    (out0:(128)word)
    (ivec:(128)word)
    (rk0:(128)word) (rk1:(128)word) (rk2:(128)word) (rk3:(128)word)
    (rk4:(128)word) (rk5:(128)word) (rk6:(128)word) (rk7:(128)word)
    (rk8:(128)word) (rk9:(128)word) (rk10:(128)word) (rk11:(128)word)
    (rk12:(128)word) (rk13:(128)word) (rk14:(128)word)
    (xi:(128)word) (h:(128)word) (h1k:(128)word) (h3k:(128)word) (h5k:(128)word)
    byte_len stackptr pc.
    1 <= byte_len /\ byte_len <= 16 /\
    aligned 16 stackptr /\
    nonoverlapping (word pc,4600) (in_ptr:int64,96) /\
    nonoverlapping (word pc,4600) (out_ptr:int64,96) /\
    nonoverlapping (word pc,4600) (xi_ptr:int64,16) /\
    nonoverlapping (word pc,4600) (ivec_ptr:int64,16) /\
    nonoverlapping (word pc,4600) (key_ptr:int64,240) /\
    nonoverlapping (word pc,4600) (htable_ptr:int64,256) /\
    nonoverlapping (word pc,4600) (stackptr:int64,80) /\
    nonoverlapping (in_ptr,96) (out_ptr,96) /\
    nonoverlapping (in_ptr,96) (xi_ptr,16) /\
    nonoverlapping (in_ptr,96) (ivec_ptr,16) /\
    nonoverlapping (out_ptr,96) (xi_ptr,16) /\
    nonoverlapping (out_ptr,96) (ivec_ptr,16) /\
    nonoverlapping (xi_ptr,16) (ivec_ptr,16) /\
    nonoverlapping (key_ptr,240) (out_ptr,96) /\
    nonoverlapping (key_ptr,240) (xi_ptr,16) /\
    nonoverlapping (key_ptr,240) (ivec_ptr,16) /\
    nonoverlapping (htable_ptr,256) (out_ptr,96) /\
    nonoverlapping (htable_ptr,256) (xi_ptr,16) /\
    nonoverlapping (htable_ptr,256) (ivec_ptr,16) /\
    nonoverlapping (stackptr,80) (out_ptr,96) /\
    nonoverlapping (stackptr,80) (xi_ptr,16) /\
    nonoverlapping (stackptr,80) (ivec_ptr,16) /\
    nonoverlapping (stackptr,80) (in_ptr,96) /\
    nonoverlapping (stackptr,80) (key_ptr,240) /\
    nonoverlapping (stackptr,80) (htable_ptr,256) /\
    nonoverlapping (ivec_ptr,16) (word pc,4600) /\
    nonoverlapping (xi_ptr,16) (word pc,4600) /\
    nonoverlapping (out_ptr,96) (word pc,4600)
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) aes256_gcm_mc /\
           read PC s = word pc /\
           C_ARGUMENTS [in_ptr; word (640 + 8 * byte_len); out_ptr; xi_ptr;
                        ivec_ptr; key_ptr; htable_ptr] s /\
           read SP s = word_add stackptr (word 80) /\
           read (memory :> bytes128 in_ptr) s = pt1 /\
           read (memory :> bytes128 (word_add in_ptr (word 16))) s = pt2 /\
           read (memory :> bytes128 (word_add in_ptr (word 32))) s = pt3 /\
           read (memory :> bytes128 (word_add in_ptr (word 48))) s = pt4 /\
           read (memory :> bytes128 (word_add in_ptr (word 64))) s = pt5 /\
           read (memory :> bytes128 (word_add in_ptr (word 80))) s = pt6 /\
           read (memory :> bytes128 (word_add out_ptr (word 80))) s = out0 /\
           read (memory :> bytes128 ivec_ptr) s = ivec /\
           read (memory :> bytes128 (word_add key_ptr (word 0))) s = rk0 /\
           read (memory :> bytes128 (word_add key_ptr (word 16))) s = rk1 /\
           read (memory :> bytes128 (word_add key_ptr (word 32))) s = rk2 /\
           read (memory :> bytes128 (word_add key_ptr (word 48))) s = rk3 /\
           read (memory :> bytes128 (word_add key_ptr (word 64))) s = rk4 /\
           read (memory :> bytes128 (word_add key_ptr (word 80))) s = rk5 /\
           read (memory :> bytes128 (word_add key_ptr (word 96))) s = rk6 /\
           read (memory :> bytes128 (word_add key_ptr (word 112))) s = rk7 /\
           read (memory :> bytes128 (word_add key_ptr (word 128))) s = rk8 /\
           read (memory :> bytes128 (word_add key_ptr (word 144))) s = rk9 /\
           read (memory :> bytes128 (word_add key_ptr (word 160))) s = rk10 /\
           read (memory :> bytes128 (word_add key_ptr (word 176))) s = rk11 /\
           read (memory :> bytes128 (word_add key_ptr (word 192))) s = rk12 /\
           read (memory :> bytes128 (word_add key_ptr (word 208))) s = rk13 /\
           read (memory :> bytes128 (word_add key_ptr (word 224))) s = rk14 /\
           read (memory :> bytes128 xi_ptr) s = xi /\
           read (memory :> bytes128 htable_ptr) s = word_swaphalves128 h /\
           read (memory :> bytes128 (word_add htable_ptr (word 16))) s = h1k /\
           read (memory :> bytes128 (word_add htable_ptr (word 32))) s =
             word_swaphalves128 (polyval_dot h h) /\
           read (memory :> bytes128 (word_add htable_ptr (word 48))) s =
             word_swaphalves128 (polyval_dot h (polyval_dot h h)) /\
           read (memory :> bytes128 (word_add htable_ptr (word 64))) s = h3k /\
           read (memory :> bytes128 (word_add htable_ptr (word 80))) s =
             word_swaphalves128 (polyval_dot (polyval_dot h h) (polyval_dot h h)) /\
           read (memory :> bytes128 (word_add htable_ptr (word 96))) s =
             word_swaphalves128 (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) /\
           read (memory :> bytes128 (word_add htable_ptr (word 112))) s = h5k /\
           read (memory :> bytes128 (word_add htable_ptr (word 128))) s =
             word_swaphalves128 (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) h) /\
           word_subword h1k (0,64):(64)word = karatsuba_mid h /\
           word_subword h1k (64,64):(64)word =
             karatsuba_mid (polyval_dot h h) /\
           word_subword h3k (0,64):(64)word =
             karatsuba_mid (polyval_dot h (polyval_dot h h)) /\
           word_subword h3k (64,64):(64)word =
             karatsuba_mid (polyval_dot (polyval_dot h h) (polyval_dot h h)) /\
           word_subword h5k (0,64):(64)word =
             karatsuba_mid (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) /\
           word_subword h5k (64,64):(64)word =
             karatsuba_mid (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) h))
      (\s. let ct1 =
             word_xor pt1
               (aes256_encrypt ivec [rk0;rk1;rk2;rk3;rk4;rk5;rk6;rk7;rk8;rk9;rk10;rk11;rk12;rk13;rk14]) in
           let ct2 =
             word_xor pt2
               (aes256_encrypt (gcm_ctr_inc ivec) [rk0;rk1;rk2;rk3;rk4;rk5;rk6;rk7;rk8;rk9;rk10;rk11;rk12;rk13;rk14]) in
           let ct3 =
             word_xor pt3
               (aes256_encrypt (gcm_ctr_inc (gcm_ctr_inc ivec)) [rk0;rk1;rk2;rk3;rk4;rk5;rk6;rk7;rk8;rk9;rk10;rk11;rk12;rk13;rk14]) in
           let ct4 =
             word_xor pt4
               (aes256_encrypt (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ivec))) [rk0;rk1;rk2;rk3;rk4;rk5;rk6;rk7;rk8;rk9;rk10;rk11;rk12;rk13;rk14]) in
           let ct5 =
             word_xor pt5
               (aes256_encrypt (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ivec)))) [rk0;rk1;rk2;rk3;rk4;rk5;rk6;rk7;rk8;rk9;rk10;rk11;rk12;rk13;rk14]) in
           let ct6 =
             word_xor pt6
               (aes256_encrypt (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ivec))))) [rk0;rk1;rk2;rk3;rk4;rk5;rk6;rk7;rk8;rk9;rk10;rk11;rk12;rk13;rk14]) in
           let mask = word (2 EXP (8 * byte_len) - 1):(128)word in
           let ctm6 = word_and ct6 mask in
           read PC s = word(pc + 4588) /\
           read X0 s = word (80 + byte_len) /\
           read (memory :> bytes128 out_ptr) s = ct1 /\
           read (memory :> bytes128 (word_add out_ptr (word 16))) s = ct2 /\
           read (memory :> bytes128 (word_add out_ptr (word 32))) s = ct3 /\
           read (memory :> bytes128 (word_add out_ptr (word 48))) s = ct4 /\
           read (memory :> bytes128 (word_add out_ptr (word 64))) s = ct5 /\
           read (memory :> bytes128 (word_add out_ptr (word 80))) s =
             word_or ctm6 (word_and out0 (word_not mask)) /\
           read (memory :> bytes128 xi_ptr) s =
             word_reversefields 8
               (ghash_polyval_acc h (word_reversefields 8 xi)
                                    [word_reversefields 8 ct1;
                                     word_reversefields 8 ct2;
                                     word_reversefields 8 ct3;
                                     word_reversefields 8 ct4;
                                     word_reversefields 8 ct5;
                                     word_reversefields 8 ctm6]))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [memory :> bytes(out_ptr,96);
                  memory :> bytes(xi_ptr,16);
                  memory :> bytes(ivec_ptr,16)] ,,
       MAYCHANGE [SP] ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes64 stackptr;
                  memory :> bytes64 (word_add stackptr (word 8));
                  memory :> bytes64 (word_add stackptr (word 16));
                  memory :> bytes64 (word_add stackptr (word 24));
                  memory :> bytes64 (word_add stackptr (word 32));
                  memory :> bytes64 (word_add stackptr (word 40));
                  memory :> bytes64 (word_add stackptr (word 48));
                  memory :> bytes64 (word_add stackptr (word 56));
                  memory :> bytes64 (word_add stackptr (word 64));
                  memory :> bytes64 (word_add stackptr (word 72))])`;;

(* --- 6-block GHASH final-closure helper tactics. --- *)

(* ========================================================================= *)
(* Self-contained 5-block GHASH conjunct closer for the single-binary        *)
(* aes256_gcm.ml more_than_4 (5-block) branch.  Reaches "No subgoals" from   *)
(* the final GHASH equality (machine word_join = spec word_reversefields).   *)
(* Mirrors the 4-block recipe; adds the ks5 +4-counter bridge and the in-asm *)
(* b0-general mask-register collapse that the 5-block sim leaves baked into  *)
(* final_xi.                                                                 *)
(* ========================================================================= *)

(* xi half-swap normalization (shared with 4-block, redefined locally). *)
let XI_HS_LO_6 = prove
 (`word_subword (word_reversefields 8 (word_join (word_subword (xi:(128)word) (64,64):(64)word) (word_subword xi (0,64):(64)word):(128)word)) (0,64):(64)word =
   word_subword (word_reversefields 8 xi) (0,64)`,
  REWRITE_TAC[GSYM REV8_JOIN_FOLD; REVERSEFIELDS8_SUBWORD_LO; REVERSEFIELDS8_SUBWORD_HI] THEN
  CONV_TAC WORD_BLAST);;

let XI_HS_HI_6 = prove
 (`word_subword (word_reversefields 8 (word_join (word_subword (xi:(128)word) (64,64):(64)word) (word_subword xi (0,64):(64)word):(128)word)) (64,64):(64)word =
   word_subword (word_reversefields 8 xi) (64,64)`,
  REWRITE_TAC[GSYM REV8_JOIN_FOLD; REVERSEFIELDS8_SUBWORD_LO; REVERSEFIELDS8_SUBWORD_HI] THEN
  CONV_TAC WORD_BLAST);;

let GCM_6B_TAIL_NOFINAL : tactic =
  ABBREV_TAC `mask = word (2 EXP (8 * byte_len) - 1):(128)word` THEN
  ABBREV_TAC `ctm6 = word_and (ct6:(128)word) mask` THEN
  SUBGOAL_THEN `word_and (mask:(128)word) (ct6:(128)word) = ctm6`
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th]) THENL [
    EXPAND_TAC "ctm6" THEN CONV_TAC WORD_BITWISE_RULE; ALL_TAC ] THEN
  (* Normalize h^4 and h^3 left-assoc -> symmetric (to match the bridge). *)
  SUBGOAL_THEN
    `polyval_dot (polyval_dot (polyval_dot (h:int128) h) h) h =
     polyval_dot (polyval_dot h h) (polyval_dot h h)`
    (fun th -> REWRITE_TAC[th]) THENL
    [REWRITE_TAC[POLYVAL_DOT_H4_EQ_LOCAL]; ALL_TAC] THEN
  SUBGOAL_THEN
    `polyval_dot (polyval_dot (h:int128) h) h = polyval_dot h (polyval_dot h h)`
    (fun th -> REWRITE_TAC[th]) THENL
    [REWRITE_TAC[polyval_dot] THEN REWRITE_TAC[WORD_PMUL_SYM]; ALL_TAC] THEN
  (* Apply 6-block bridge. *)
  MP_TAC(SPECL
    [`word_reversefields 8 (word_xor xi ct1):int128`;
     `word_reversefields 8 ct2:int128`; `word_reversefields 8 ct3:int128`;
     `word_reversefields 8 ct4:int128`; `word_reversefields 8 ct5:int128`;
     `word_reversefields 8 ctm6:int128`;
     `h:int128`; `h1k:int128`;
     `word_join (word 0:(64)word) (word_subword (h1k:(128)word) (64,64):(64)word):(128)word`;
     `h3k:int128`;
     `word_join (word 0:(64)word) (word_subword (h3k:(128)word) (64,64):(64)word):(128)word`;
     `h5k:int128`;
     `word_join (word 0:(64)word) (word_subword (h5k:(128)word) (64,64):(64)word):(128)word`]
    GHASH_6BLOCK_KARATSUBA_EQ_POLYVAL_ACC) THEN
  SUBGOAL_THEN
    `word_subword (word_join (word 0:(64)word) (word_subword (h1k:(128)word) (64,64):(64)word):(128)word) (0,64):(64)word =
     karatsuba_mid (polyval_dot h h)`
    (fun th -> REWRITE_TAC[th]) THENL [
    SUBGOAL_THEN
      `word_subword (word_join (word 0:(64)word) (word_subword (h1k:(128)word) (64,64):(64)word):(128)word) (0,64):(64)word =
       word_subword (h1k:(128)word) (64,64):(64)word`
      (fun th -> REWRITE_TAC[th]) THENL [CONV_TAC WORD_BLAST; ASM_REWRITE_TAC[]]; ALL_TAC ] THEN
  SUBGOAL_THEN
    `word_subword (word_join (word 0:(64)word) (word_subword (h3k:(128)word) (64,64):(64)word):(128)word) (0,64):(64)word =
     karatsuba_mid (polyval_dot (polyval_dot h h) (polyval_dot h h))`
    (fun th -> REWRITE_TAC[th]) THENL [
    SUBGOAL_THEN
      `word_subword (word_join (word 0:(64)word) (word_subword (h3k:(128)word) (64,64):(64)word):(128)word) (0,64):(64)word =
       word_subword (h3k:(128)word) (64,64):(64)word`
      (fun th -> REWRITE_TAC[th]) THENL [CONV_TAC WORD_BLAST; ASM_REWRITE_TAC[]]; ALL_TAC ] THEN
  SUBGOAL_THEN
    `word_subword (word_join (word 0:(64)word) (word_subword (h5k:(128)word) (64,64):(64)word):(128)word) (0,64):(64)word =
     karatsuba_mid (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) h)`
    (fun th -> REWRITE_TAC[th]) THENL [
    SUBGOAL_THEN
      `word_subword (word_join (word 0:(64)word) (word_subword (h5k:(128)word) (64,64):(64)word):(128)word) (0,64):(64)word =
       word_subword (h5k:(128)word) (64,64):(64)word`
      (fun th -> REWRITE_TAC[th]) THENL [CONV_TAC WORD_BLAST; ASM_REWRITE_TAC[]]; ALL_TAC ] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN
  REWRITE_TAC[ghash_6block_karatsuba; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[SWAPHALVES128_SUBWORD_LO; SWAPHALVES128_SUBWORD_HI] THEN
  SUBGOAL_THEN
    `word_subword (word_join (word 0:(64)word) (karatsuba_mid (polyval_dot h h):(64)word):(128)word) (0,64):(64)word =
     karatsuba_mid (polyval_dot h h)`
    (fun th -> REWRITE_TAC[th]) THENL [CONV_TAC WORD_BLAST; ALL_TAC] THEN
  SUBGOAL_THEN
    `word_subword (word_join (word 0:(64)word) (karatsuba_mid (polyval_dot (polyval_dot h h) (polyval_dot h h)):(64)word):(128)word) (0,64):(64)word =
     karatsuba_mid (polyval_dot (polyval_dot h h) (polyval_dot h h))`
    (fun th -> REWRITE_TAC[th]) THENL [CONV_TAC WORD_BLAST; ALL_TAC] THEN
  SUBGOAL_THEN
    `word_subword (word_join (word 0:(64)word) (karatsuba_mid (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) h):(64)word):(128)word) (0,64):(64)word =
     karatsuba_mid (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) h)`
    (fun th -> REWRITE_TAC[th]) THENL [CONV_TAC WORD_BLAST; ALL_TAC] THEN
  REWRITE_TAC[GSYM karatsuba_mid] THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
  CONV_TAC SYM_CONV THEN
  FIRST_ASSUM(fun th ->
    if is_eq(concl th) && rand(concl th) = `final_xi:(128)word` &&
       (try (let l = lhs(concl th) in is_comb l &&
             (let r = rator l in not(is_comb r && (try fst(dest_const(rator r)) = "read" with _ -> false))))
        with _ -> false)
    then SUBST1_TAC(SYM th) else NO_TAC) THEN
  REWRITE_TAC[REV64_LOWER_LANE; REV64_UPPER_LANE; REV8_JOIN_FOLD] THEN
  MATCH_MP_TAC(MESON[]
    `x = y ==> word_reversefields 8 x = word_reversefields 8 y:(128)word`) THEN
  REWRITE_TAC[WORD_SWAP_HALVES_INVOLUTION] THEN
  CONV_TAC(LAND_CONV(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
  REWRITE_TAC[WORD_INSERT_AS_JOIN_LO; WORD_INSERT_AS_JOIN_HI;
              KAR_SUBWORD_LEMMA; WORD_SWAP_HALVES_INVOLUTION;
              WORD_OR_REFL; WORD_XOR_ASSOC; WORD_SUBWORD_XOR;
              SWAPHALVES128_SUBWORD_LO; SWAPHALVES128_SUBWORD_HI] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[HALFSWAP_XOR; GSYM WORD_REVERSEFIELDS_XOR_8_128;
              WORD_XOR_0; WORD_XOR_ASSOC;
              REV8_JOIN_FOLD; REVERSEFIELDS8_SUBWORD_LO; REVERSEFIELDS8_SUBWORD_HI] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  CONV_TAC(TOP_DEPTH_CONV PMUL_NORM_CONV) THEN
  SUBGOAL_THEN
    `word_subword (word 0:(128)word) (0,64):(64)word = word 0 /\
     word_subword (word 0:(128)word) (64,64):(64)word = word 0`
    (fun th -> REWRITE_TAC[th]) THENL [CONJ_TAC THEN CONV_TAC WORD_BLAST; ALL_TAC] THEN
  REWRITE_TAC[WORD_XOR_0; WORD_XOR_0_LEFT] THEN
  REWRITE_TAC[karatsuba_mid; WORD_REVERSEFIELDS_XOR_8_128; WORD_SUBWORD_XOR] THEN
  (* 26 atomic ABBREVs *)
  ABBREV_TAC `(c1lo:(64)word) = word_subword (word_reversefields 8 (ct1:(128)word)) (0,64)` THEN
  ABBREV_TAC `(c1hi:(64)word) = word_subword (word_reversefields 8 (ct1:(128)word)) (64,64)` THEN
  ABBREV_TAC `(c2lo:(64)word) = word_subword (word_reversefields 8 (ct2:(128)word)) (0,64)` THEN
  ABBREV_TAC `(c2hi:(64)word) = word_subword (word_reversefields 8 (ct2:(128)word)) (64,64)` THEN
  ABBREV_TAC `(c3lo:(64)word) = word_subword (word_reversefields 8 (ct3:(128)word)) (0,64)` THEN
  ABBREV_TAC `(c3hi:(64)word) = word_subword (word_reversefields 8 (ct3:(128)word)) (64,64)` THEN
  ABBREV_TAC `(c4lo:(64)word) = word_subword (word_reversefields 8 (ct4:(128)word)) (0,64)` THEN
  ABBREV_TAC `(c4hi:(64)word) = word_subword (word_reversefields 8 (ct4:(128)word)) (64,64)` THEN
  ABBREV_TAC `(c5lo:(64)word) = word_subword (word_reversefields 8 (ct5:(128)word)) (0,64)` THEN
  ABBREV_TAC `(c5hi:(64)word) = word_subword (word_reversefields 8 (ct5:(128)word)) (64,64)` THEN
  ABBREV_TAC `(c6lo:(64)word) = word_subword (word_reversefields 8 (ctm6:(128)word)) (0,64)` THEN
  ABBREV_TAC `(c6hi:(64)word) = word_subword (word_reversefields 8 (ctm6:(128)word)) (64,64)` THEN
  ABBREV_TAC `(xilo:(64)word) = word_subword (word_reversefields 8 (xi:(128)word)) (0,64)` THEN
  ABBREV_TAC `(xihi:(64)word) = word_subword (word_reversefields 8 (xi:(128)word)) (64,64)` THEN
  ABBREV_TAC `(hd0:(64)word) = word_subword (h:(128)word) (0,64)` THEN
  ABBREV_TAC `(hd1:(64)word) = word_subword (h:(128)word) (64,64)` THEN
  ABBREV_TAC `(he0:(64)word) = word_subword ((polyval_dot h h):(128)word) (0,64)` THEN
  ABBREV_TAC `(he1:(64)word) = word_subword ((polyval_dot h h):(128)word) (64,64)` THEN
  ABBREV_TAC `(hf0:(64)word) = word_subword ((polyval_dot h (polyval_dot h h)):(128)word) (0,64)` THEN
  ABBREV_TAC `(hf1:(64)word) = word_subword ((polyval_dot h (polyval_dot h h)):(128)word) (64,64)` THEN
  ABBREV_TAC `(hg0:(64)word) = word_subword ((polyval_dot (polyval_dot h h) (polyval_dot h h)):(128)word) (0,64)` THEN
  ABBREV_TAC `(hg1:(64)word) = word_subword ((polyval_dot (polyval_dot h h) (polyval_dot h h)):(128)word) (64,64)` THEN
  ABBREV_TAC `(hh0:(64)word) = word_subword ((polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h):(128)word) (0,64)` THEN
  ABBREV_TAC `(hh1:(64)word) = word_subword ((polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h):(128)word) (64,64)` THEN
  ABBREV_TAC `(hj0:(64)word) = word_subword ((polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) h):(128)word) (0,64)` THEN
  ABBREV_TAC `(hj1:(64)word) = word_subword ((polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) h):(128)word) (64,64)` THEN
  ASM_REWRITE_TAC[] THEN
  (* 18 inner pmul ABBREVs *)
  ABBREV_TAC `(w1lo:(128)word) = word_pmul (word_xor (xilo:(64)word) (c1lo:(64)word)) (hj0:(64)word)` THEN
  ABBREV_TAC `(w1hi:(128)word) = word_pmul (word_xor (xihi:(64)word) (c1hi:(64)word)) (hj1:(64)word)` THEN
  ABBREV_TAC `(w1md:(128)word) = word_pmul (word_xor (word_xor (xihi:(64)word) (c1hi:(64)word)) (word_xor (xilo:(64)word) (c1lo:(64)word))) (word_xor (hj0:(64)word) (hj1:(64)word))` THEN
  ABBREV_TAC `(w2lo:(128)word) = word_pmul (c2lo:(64)word) (hh0:(64)word)` THEN
  ABBREV_TAC `(w2hi:(128)word) = word_pmul (c2hi:(64)word) (hh1:(64)word)` THEN
  ABBREV_TAC `(w2md:(128)word) = word_pmul (word_xor (c2hi:(64)word) (c2lo:(64)word)) (word_xor (hh0:(64)word) (hh1:(64)word))` THEN
  ABBREV_TAC `(w3lo:(128)word) = word_pmul (c3lo:(64)word) (hg0:(64)word)` THEN
  ABBREV_TAC `(w3hi:(128)word) = word_pmul (c3hi:(64)word) (hg1:(64)word)` THEN
  ABBREV_TAC `(w3md:(128)word) = word_pmul (word_xor (c3hi:(64)word) (c3lo:(64)word)) (word_xor (hg0:(64)word) (hg1:(64)word))` THEN
  ABBREV_TAC `(w4lo:(128)word) = word_pmul (c4lo:(64)word) (hf0:(64)word)` THEN
  ABBREV_TAC `(w4hi:(128)word) = word_pmul (c4hi:(64)word) (hf1:(64)word)` THEN
  ABBREV_TAC `(w4md:(128)word) = word_pmul (word_xor (c4hi:(64)word) (c4lo:(64)word)) (word_xor (hf0:(64)word) (hf1:(64)word))` THEN
  ABBREV_TAC `(w5lo:(128)word) = word_pmul (c5lo:(64)word) (he0:(64)word)` THEN
  ABBREV_TAC `(w5hi:(128)word) = word_pmul (c5hi:(64)word) (he1:(64)word)` THEN
  ABBREV_TAC `(w5md:(128)word) = word_pmul (word_xor (c5hi:(64)word) (c5lo:(64)word)) (word_xor (he0:(64)word) (he1:(64)word))` THEN
  ABBREV_TAC `(w6lo:(128)word) = word_pmul (c6lo:(64)word) (hd0:(64)word)` THEN
  ABBREV_TAC `(w6hi:(128)word) = word_pmul (c6hi:(64)word) (hd1:(64)word)` THEN
  ABBREV_TAC `(w6md:(128)word) = word_pmul (word_xor (c6hi:(64)word) (c6lo:(64)word)) (word_xor (hd0:(64)word) (hd1:(64)word))` THEN
  REWRITE_TAC[DOUBLE_SUBWORD_JOIN; DOUBLE_SUBWORD_JOIN_HI; WORD_SUBWORD_XOR] THEN
  SUBGOAL_THEN
    `word_pmul (word_xor (xihi:(64)word) (word_xor (c1hi:(64)word) (word_xor (xilo:(64)word) (c1lo:(64)word)))) (word_xor (hj0:(64)word) (hj1:(64)word)):(128)word = w1md`
    (fun th -> REWRITE_TAC[th]) THENL
    [EXPAND_TAC "w1md" THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  (* 36 z-vars *)
  ABBREV_TAC `(w1lo_l:(64)word) = word_subword (w1lo:(128)word) (0,64)` THEN
  ABBREV_TAC `(w1lo_h:(64)word) = word_subword (w1lo:(128)word) (64,64)` THEN
  ABBREV_TAC `(w1hi_l:(64)word) = word_subword (w1hi:(128)word) (0,64)` THEN
  ABBREV_TAC `(w1hi_h:(64)word) = word_subword (w1hi:(128)word) (64,64)` THEN
  ABBREV_TAC `(w1md_l:(64)word) = word_subword (w1md:(128)word) (0,64)` THEN
  ABBREV_TAC `(w1md_h:(64)word) = word_subword (w1md:(128)word) (64,64)` THEN
  ABBREV_TAC `(w2lo_l:(64)word) = word_subword (w2lo:(128)word) (0,64)` THEN
  ABBREV_TAC `(w2lo_h:(64)word) = word_subword (w2lo:(128)word) (64,64)` THEN
  ABBREV_TAC `(w2hi_l:(64)word) = word_subword (w2hi:(128)word) (0,64)` THEN
  ABBREV_TAC `(w2hi_h:(64)word) = word_subword (w2hi:(128)word) (64,64)` THEN
  ABBREV_TAC `(w2md_l:(64)word) = word_subword (w2md:(128)word) (0,64)` THEN
  ABBREV_TAC `(w2md_h:(64)word) = word_subword (w2md:(128)word) (64,64)` THEN
  ABBREV_TAC `(w3lo_l:(64)word) = word_subword (w3lo:(128)word) (0,64)` THEN
  ABBREV_TAC `(w3lo_h:(64)word) = word_subword (w3lo:(128)word) (64,64)` THEN
  ABBREV_TAC `(w3hi_l:(64)word) = word_subword (w3hi:(128)word) (0,64)` THEN
  ABBREV_TAC `(w3hi_h:(64)word) = word_subword (w3hi:(128)word) (64,64)` THEN
  ABBREV_TAC `(w3md_l:(64)word) = word_subword (w3md:(128)word) (0,64)` THEN
  ABBREV_TAC `(w3md_h:(64)word) = word_subword (w3md:(128)word) (64,64)` THEN
  ABBREV_TAC `(w4lo_l:(64)word) = word_subword (w4lo:(128)word) (0,64)` THEN
  ABBREV_TAC `(w4lo_h:(64)word) = word_subword (w4lo:(128)word) (64,64)` THEN
  ABBREV_TAC `(w4hi_l:(64)word) = word_subword (w4hi:(128)word) (0,64)` THEN
  ABBREV_TAC `(w4hi_h:(64)word) = word_subword (w4hi:(128)word) (64,64)` THEN
  ABBREV_TAC `(w4md_l:(64)word) = word_subword (w4md:(128)word) (0,64)` THEN
  ABBREV_TAC `(w4md_h:(64)word) = word_subword (w4md:(128)word) (64,64)` THEN
  ABBREV_TAC `(w5lo_l:(64)word) = word_subword (w5lo:(128)word) (0,64)` THEN
  ABBREV_TAC `(w5lo_h:(64)word) = word_subword (w5lo:(128)word) (64,64)` THEN
  ABBREV_TAC `(w5hi_l:(64)word) = word_subword (w5hi:(128)word) (0,64)` THEN
  ABBREV_TAC `(w5hi_h:(64)word) = word_subword (w5hi:(128)word) (64,64)` THEN
  ABBREV_TAC `(w5md_l:(64)word) = word_subword (w5md:(128)word) (0,64)` THEN
  ABBREV_TAC `(w5md_h:(64)word) = word_subword (w5md:(128)word) (64,64)` THEN
  ABBREV_TAC `(w6lo_l:(64)word) = word_subword (w6lo:(128)word) (0,64)` THEN
  ABBREV_TAC `(w6lo_h:(64)word) = word_subword (w6lo:(128)word) (64,64)` THEN
  ABBREV_TAC `(w6hi_l:(64)word) = word_subword (w6hi:(128)word) (0,64)` THEN
  ABBREV_TAC `(w6hi_h:(64)word) = word_subword (w6hi:(128)word) (64,64)` THEN
  ABBREV_TAC `(w6md_l:(64)word) = word_subword (w6md:(128)word) (0,64)` THEN
  ABBREV_TAC `(w6md_h:(64)word) = word_subword (w6md:(128)word) (64,64)` THEN
  ASM_REWRITE_TAC[] THEN
  (* Normalize LHS mid-pmuls to abbreviated w?md (swapped xor arg order). *)
  SUBGOAL_THEN `word_pmul (word_xor (c2lo:(64)word) (c2hi:(64)word)) (word_xor (hh0:(64)word) (hh1:(64)word)):(128)word = w2md`
    (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "w2md" THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  SUBGOAL_THEN `word_pmul (word_xor (c3lo:(64)word) (c3hi:(64)word)) (word_xor (hg0:(64)word) (hg1:(64)word)):(128)word = w3md`
    (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "w3md" THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  SUBGOAL_THEN `word_pmul (word_xor (c4lo:(64)word) (c4hi:(64)word)) (word_xor (hf0:(64)word) (hf1:(64)word)):(128)word = w4md`
    (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "w4md" THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  SUBGOAL_THEN `word_pmul (word_xor (c5lo:(64)word) (c5hi:(64)word)) (word_xor (he0:(64)word) (he1:(64)word)):(128)word = w5md`
    (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "w5md" THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  SUBGOAL_THEN `word_pmul (word_xor (c6lo:(64)word) (c6hi:(64)word)) (word_xor (hd0:(64)word) (hd1:(64)word)):(128)word = w6md`
    (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "w6md" THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  SUBGOAL_THEN `word_pmul (word_xor (xilo:(64)word) (word_xor (c1lo:(64)word) (word_xor (xihi:(64)word) (c1hi:(64)word)))) (word_xor (hj0:(64)word) (hj1:(64)word)):(128)word = w1md`
    (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "w1md" THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  (* qS: small Barrett pmul. *)
  ABBREV_TAC `(qS:(128)word) = word_pmul (word_xor (w6lo_l:(64)word) (word_xor w5lo_l (word_xor w4lo_l (word_xor w3lo_l (word_xor w2lo_l w1lo_l))))) (word 13979173243358019584:(64)word)` THEN
  SUBGOAL_THEN `word_pmul (word_xor (w1lo_l:(64)word) (word_xor w2lo_l (word_xor w3lo_l (word_xor w4lo_l (word_xor w5lo_l w6lo_l))))) (word 13979173243358019584:(64)word):(128)word = qS`
    (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "qS" THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  (* qB: big Barrett pmul; fold LHS-order copy via bubble_sort_conv. *)
  ABBREV_TAC `(qB:(128)word) = word_pmul
    (word_xor (w6md_l:(64)word) (word_xor w5md_l (word_xor w4md_l (word_xor w3md_l (word_xor w2md_l (word_xor w1md_l (word_xor w6lo_l (word_xor w5lo_l (word_xor w4lo_l (word_xor w3lo_l (word_xor w2lo_l (word_xor w1lo_l (word_xor w6hi_l (word_xor w5hi_l (word_xor w4hi_l (word_xor w3hi_l (word_xor w2hi_l (word_xor w1hi_l (word_xor (word_subword (qS:(128)word) (0,64)) (word_xor w6lo_h (word_xor w5lo_h (word_xor w4lo_h (word_xor w3lo_h (word_xor w2lo_h (w1lo_h))))))))))))))))))))))))) (word 13979173243358019584:(64)word)` THEN
  SUBGOAL_THEN
    `word_pmul (word_xor (w1lo_h:(64)word) (word_xor w2lo_h (word_xor w3lo_h (word_xor w4lo_h (word_xor w5lo_h (word_xor w6lo_h (word_xor w1md_l (word_xor w2md_l (word_xor w3md_l (word_xor w4md_l (word_xor w5md_l (word_xor w6md_l (word_xor w1hi_l (word_xor w2hi_l (word_xor w3hi_l (word_xor w4hi_l (word_xor w5hi_l (word_xor w6hi_l (word_xor w1lo_l (word_xor w2lo_l (word_xor w3lo_l (word_xor w4lo_l (word_xor w5lo_l (word_xor w6lo_l ((word_subword (qS:(128)word) (0,64))))))))))))))))))))))))))) (word 13979173243358019584:(64)word):(128)word = qB`
    (fun th -> REWRITE_TAC[th]) THENL
    [EXPAND_TAC "qB" THEN AP_THM_TAC THEN AP_TERM_TAC THEN
     CONV_TAC(BINOP_CONV bubble_sort_conv) THEN REFL_TAC; ALL_TAC];;

(* Step 1+2: establish the four spec-form ct folds F1..F4 and fold them into
   the RHS ghash list. *)
let GCM_6B_FOLD_SPEC_CTS : tactic =
  (* F1 *)
  SUBGOAL_THEN
   `word_xor pt1 (aes256_encrypt ivec [rk0;rk1;rk2;rk3;rk4;rk5;rk6;rk7;rk8;rk9;rk10;rk11;rk12;rk13;rk14]) = ct1`
   ASSUME_TAC THENL
   [EXPAND_TAC "ct1" THEN
    (* June base: ct1's def is left-assoc; left-associate the EXPAND output. *)
    REWRITE_TAC[AES256_ENCRYPT_UNFOLD; LET_DEF; LET_END_DEF; WORD_XOR_ASSOC] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* F2 *)
  SUBGOAL_THEN
   `word_xor pt2 (aes256_encrypt (gcm_ctr_inc ivec) [rk0;rk1;rk2;rk3;rk4;rk5;rk6;rk7;rk8;rk9;rk10;rk11;rk12;rk13;rk14]) = ct2`
   ASSUME_TAC THENL
   [CONV_TAC SYM_CONV THEN GCM_6BLOCK_CT2_STEP_TAC; ALL_TAC] THEN
  (* F3 *)
  SUBGOAL_THEN
   `word_xor pt3 (aes256_encrypt (gcm_ctr_inc (gcm_ctr_inc ivec)) [rk0;rk1;rk2;rk3;rk4;rk5;rk6;rk7;rk8;rk9;rk10;rk11;rk12;rk13;rk14]) = ct3`
   ASSUME_TAC THENL
   [CONV_TAC SYM_CONV THEN GCM_6BLOCK_CT3_STEP_TAC; ALL_TAC] THEN
  (* F4 *)
  SUBGOAL_THEN
   `word_xor pt4 (aes256_encrypt (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ivec))) [rk0;rk1;rk2;rk3;rk4;rk5;rk6;rk7;rk8;rk9;rk10;rk11;rk12;rk13;rk14]) = ct4`
   ASSUME_TAC THENL
   [CONV_TAC SYM_CONV THEN GCM_6BLOCK_CT4_STEP_TAC; ALL_TAC] THEN
  (* F5 *)
  SUBGOAL_THEN
   `word_xor pt5 (aes256_encrypt (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ivec)))) [rk0;rk1;rk2;rk3;rk4;rk5;rk6;rk7;rk8;rk9;rk10;rk11;rk12;rk13;rk14]) = ct5`
   ASSUME_TAC THENL
   [CONV_TAC SYM_CONV THEN GCM_6BLOCK_CT5_STEP_TAC; ALL_TAC] THEN
  (* fold the five into the RHS ghash list only: pick the F-fact for each ctN
     (LHS = word_xor ptN (aes256_encrypt ...)) and GEN_REWRITE the RHS. *)
  (fun (asl,w) ->
     let getf n = snd(find (fun (_,th) ->
       is_eq(concl th) && rand(concl th)=mk_var("ct"^string_of_int n,`:(128)word`) &&
       (let l=lhand(concl th) in
        (try fst(dest_const(rator(rator l)))="word_xor" with _->false) &&
        (try fst(dest_const(repeat rator (rand l)))="aes256_encrypt" with _->false))) asl) in
     GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [getf 1; getf 2; getf 3; getf 4; getf 5] (asl,w));;

(* Step 4: b0-general mask-register collapse, applied to ALL assumptions
   (the 5-block sim bakes the uncollapsed mask register into final_xi). *)
let GCM_6B_MASK_COLLAPSE_ASMS : tactic =
  SUBGOAL_THEN `1 <= (byte_len:num) /\ byte_len <= 16` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(fun bth -> if concl bth = `1 <= (byte_len:num) /\ byte_len <= 16` then
    RULE_ASSUM_TAC(REWRITE_RULE[GEN `b0:int128` (MP (SPEC_ALL SIXBLOCK_MASK_REG) bth)]) else NO_TAC);;

(* Step 5: bridge the machine block-5 keystream (collapsed +4 counter, baked
   into final_xi) to the spec ct5.  Extract the machine keystream from the
   final_xi defining assumption and prove (machine ks5 = ct5), then fold it
   into every assumption (incl final_xi). *)
let GCM_6B_KS6_FOLD : tactic = fun (asl,w) ->
  let substr sub s =
    let ls=String.length s and lb=String.length sub in
    let rec go i = if i+lb>ls then false
                   else if String.sub s i lb = sub then true else go(i+1) in go 0 in
  let fxidef = snd(find (fun (_,th) ->
    is_eq(concl th) && (try rand(concl th)=`final_xi:(128)word` with _->false)) asl) in
  let body = lhs(concl fxidef) in
  (* June base: require rk14 so the full keystream (not the pre-whitening subterm)
     is picked; mirror band-5 GCM_5B_KS5_FOLD. *)
  let best = ref None in
  let rec walk t =
    (try let s=string_of_term t in
      if substr "pt6" s && substr "aese" s && substr "rk14" s &&
         (try fst(dest_const(repeat rator t))="word_xor" with _->false) &&
         (match !best with None->true | Some b -> String.length s < String.length(string_of_term b))
      then best := Some t
     with _->());
    (match t with Comb(a,b)->walk a; walk b | Abs(_,b)->walk b | _->()) in
  walk body;
  let ks5 = (match !best with Some t->t | None->failwith "KS6_FOLD: ks6 not found") in
  let bri = WORD_BLAST `word_bytereverse (word_bytereverse (x:(32)word)) = x` in
  let add5 = WORD_RULE `word_add (word_add (word_add (word_add (word_add (x:(32)word) (word 1)) (word 1)) (word 1)) (word 1)) (word 1) = word_add x (word 5)` in
  (SUBGOAL_THEN (mk_eq(ks5, `ct6:(128)word`)) ASSUME_TAC THENL
    [(* band-4/5 counter peel: orient spec, unfold AES, left-assoc, peel pt6/rk14,
        peel aese layers, bridge the collapsed +5 counter. *)
     CONV_TAC SYM_CONV THEN EXPAND_TAC "ct6" THEN
     REWRITE_TAC[AES256_ENCRYPT_UNFOLD] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
     REWRITE_TAC[WORD_XOR_ASSOC] THEN
     AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
     REPEAT(AP_THM_TAC ORELSE AP_TERM_TAC) THEN
     REWRITE_TAC[gcm_ctr_inc] THEN
     REWRITE_TAC[WORD_REVERSEFIELDS_REVERSEFIELDS; WORD_REVERSEFIELDS_8_BYTEREVERSE_32] THEN
     REWRITE_TAC[INSERT_SUBWORD; INSERT_IDEM] THEN
     REWRITE_TAC[bri] THEN REWRITE_TAC[add5] THEN
     REWRITE_TAC[CTR_WORD_INSERT];
     ALL_TAC] THEN
   FIRST_ASSUM(fun th ->
     if is_eq(concl th) && rand(concl th)=`ct6:(128)word` &&
        (try fst(dest_const(repeat rator (lhs(concl th))))="word_xor" with _->false) &&
        String.length(string_of_term(lhs(concl th))) > 1000
     then RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th] else NO_TAC))
  (asl,w);;

(* June-2026 base: per-half XOR-AC closer, mirroring band-4/5.  6 mids
   (w1md=hj, w2md=hh, w3md=hg, w4md=hf, w5md=he, w6md=hd), qS=6 atoms, qB=25 atoms. *)
let GCM_6B_FOLD_MIDS_TAC : tactic =
  fun (asl,gg) ->
    let rec finds hd t acc = match t with
      | Comb(Comb(Const("word_pmul",_),a),x) when x = hd ->
          a :: (finds hd a (finds hd x acc))
      | Comb(l,r) -> finds hd l (finds hd r acc)
      | Abs(_,b) -> finds hd b acc | _ -> acc in
    let hjw = `word_xor (hj0:(64)word) hj1`
    and hhw = `word_xor (hh0:(64)word) hh1`
    and hgw = `word_xor (hg0:(64)word) hg1`
    and hfw = `word_xor (hf0:(64)word) hf1`
    and hew = `word_xor (he0:(64)word) he1`
    and hdw = `word_xor (hd0:(64)word) hd1` in
    let mk tgt hd arg =
      SUBGOAL_THEN
        (mk_eq(list_mk_comb(`word_pmul:(64)word->(64)word->(128)word`,[arg;hd]),tgt))
        (fun th -> REWRITE_TAC[th]) THENL
       [EXPAND_TAC (fst(dest_var tgt)) THEN AP_THM_TAC THEN AP_TERM_TAC THEN
        CONV_TAC WORD_RULE; ALL_TAC] in
    (EVERY ((map (mk `w1md:(128)word` hjw) (setify(finds hjw gg [])))
          @ (map (mk `w2md:(128)word` hhw) (setify(finds hhw gg [])))
          @ (map (mk `w3md:(128)word` hgw) (setify(finds hgw gg [])))
          @ (map (mk `w4md:(128)word` hfw) (setify(finds hfw gg [])))
          @ (map (mk `w5md:(128)word` hew) (setify(finds hew gg [])))
          @ (map (mk `w6md:(128)word` hdw) (setify(finds hdw gg []))))) (asl,gg);;
let GCM_6B_FOLD_TO tgt natoms : tactic =
  let w64 = `word 13979173243358019584:(64)word` in
  fun (asl,gg) ->
    let rec finds t acc = match t with
      | Comb(Comb(Const("word_pmul",_),a),x) when x = w64 ->
          a :: (finds a (finds x acc))
      | Comb(l,r) -> finds l (finds r acc) | Abs(_,b) -> finds b acc | _ -> acc in
    let rec at t = match t with
      | Comb(Comb(Const("word_xor",_),x),y) -> at x @ at y | _ -> [t] in
    let args = List.filter (fun a -> List.length(at a) = natoms) (setify(finds gg [])) in
    (EVERY (map (fun a ->
       FIRST [SUBGOAL_THEN
                (mk_eq(list_mk_comb(`word_pmul:(64)word->(64)word->(128)word`,[a;w64]),tgt))
                (fun th -> REWRITE_TAC[th]) THENL
               [EXPAND_TAC (fst(dest_var tgt)) THEN AP_THM_TAC THEN AP_TERM_TAC THEN
                CONV_TAC(BINOP_CONV bubble_fix) THEN REFL_TAC; ALL_TAC];
              ALL_TAC]) args)) (asl,gg);;
let GCM_6B_HALF_CLOSE : tactic =
  GCM_6B_FOLD_MIDS_TAC THEN ASM_REWRITE_TAC[] THEN
  GCM_6B_FOLD_TO `qS:(128)word` 6 THEN ASM_REWRITE_TAC[] THEN
  GCM_6B_FOLD_TO `qB:(128)word` 25 THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(BINOP_CONV bubble_fix) THEN REFL_TAC;;

(* The full GHASH closer: applied at the final GHASH conjunct. *)
let GCM_6B_GHASH_CLOSE : tactic =
  GCM_6B_FOLD_SPEC_CTS THEN
  REWRITE_TAC[GHASH_POLYVAL_ACC_6; POLYVAL_DOT_H6_EQ; POLYVAL_DOT_H5_EQ; GSYM WORD_REVERSEFIELDS_XOR_8_128] THEN
  GCM_6B_MASK_COLLAPSE_ASMS THEN
  GCM_6B_KS6_FOLD THEN
  GCM_6B_TAIL_NOFINAL THEN
  REWRITE_TAC[XI_HS_LO_6; XI_HS_HI_6] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `word_pmul (word_xor (xihi:(64)word) (word_xor c1hi (word_xor xilo c1lo)))
              (word_xor (hj0:(64)word) hj1):(128)word = w1md`
   (fun th -> REWRITE_TAC[th]) THENL
   [EXPAND_TAC "w1md" THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  BINOP_TAC THENL [GCM_6B_HALF_CLOSE; GCM_6B_HALF_CLOSE];;

(* --- The 6-block branch theorem. --- *)

(* Full assembled AES256_GCM_ENCRYPT_LT_6BLOCK_CORRECT proof (more_than_5),  *)
(* using the closers from gcm_six_block_closers.ml.                          *)

(* ct1 closer (counter = ivec, no inc). *)
let CT_CLOSE_6 nidx =
  let s13n = "s13_"^string_of_int nidx and ctn = "ct"^string_of_int nidx in
  EXPAND_TAC ctn THEN EXPAND_TAC s13n THEN
  REWRITE_TAC[AES256_ENCRYPT_UNFOLD; LET_DEF; LET_END_DEF; WORD_XOR_ASSOC] THEN ASM_REWRITE_TAC[];;

(* masked-ct6 store conjunct closer: collapse the mask reg, peel word_or/
   word_and/word_xor to the counter identity (machine +5 form vs spec
   gcm_ctr_inc^5), discharge with the nested-insert collapse. *)
let GCM_6B_MASKED_CT6_CLOSE : tactic =
  let bri = WORD_BLAST `word_bytereverse (word_bytereverse (x:(32)word)) = x` in
  let add5 = WORD_RULE `word_add (word_add (word_add (word_add (word_add (x:(32)word) (word 1)) (word 1)) (word 1)) (word 1)) (word 1) = word_add x (word 5)` in
  SUBGOAL_THEN `1 <= byte_len /\ byte_len <= 16` MP_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP SIXBLOCK_MASK_REG th]) THEN
  REWRITE_TAC[NBLOCK_MASK_IDEM] THEN
  MATCH_MP_TAC(MESON[] `x = y ==> word_or (word_and x m) r = word_or (word_and y m) r:(128)word`) THEN
  CONV_TAC SYM_CONV THEN REWRITE_TAC[AES256_ENCRYPT_UNFOLD] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[WORD_XOR_ASSOC] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REPEAT(AP_THM_TAC ORELSE AP_TERM_TAC) THEN
  REWRITE_TAC[gcm_ctr_inc] THEN
  REWRITE_TAC[WORD_REVERSEFIELDS_REVERSEFIELDS; WORD_REVERSEFIELDS_8_BYTEREVERSE_32] THEN
  REWRITE_TAC[INSERT_SUBWORD; INSERT_IDEM] THEN
  REWRITE_TAC[bri] THEN REWRITE_TAC[add5] THEN
  REWRITE_TAC[CTR_WORD_INSERT];;

let AES256_GCM_ENCRYPT_LT_6BLOCK_CONCRETE = prove
 (gcm_6b_goal,
  (* ---- symbolic simulation (store-based ct abbreviation) ---- *)
  GCM_INIT_TAC GCM_CBZ_LEMMA6 THEN GCM_PROLOGUE_TAC THEN GCM_RUN 20 263 THEN
  GCM_INLOOP_GUARD_TAC GCM_X6_LEMMA6 THEN GCM_RUN 267 272 THEN
  GCM_BND16 GCM_X6TAIL_LEMMA6 THEN
  GCM_RUN_THEN GCM_CASCADE6_TAC 273 321 THEN
  abbrev_ct_from_store 0 1 THEN abbrev_ct_from_store 16 2 THEN
  GCM_RUN 322 335 THEN abbrev_ct_from_store 32 3 THEN
  GCM_RUN 336 362 THEN abbrev_ct_from_store 48 4 THEN
  GCM_RUN 363 376 THEN abbrev_ct_from_store 64 5 THEN
  GCM_RUN 377 411 THEN
  SUBGOAL_THEN `1 <= byte_len /\ byte_len <= 16` MP_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP SIXBLOCK_MASK_REG th])) THEN
  GCM_NBLOCK_POST_SIM_NORMALIZE_TAC THEN ABBREV_FINAL_XI_TAC THEN
  ARM_STEPS_TAC AES256_GCM_EXEC (412--419) THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ENSURES_FINAL_STATE_TAC THEN
  SUBGOAL_THEN `1 <= byte_len /\ byte_len <= 16` MP_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP SIXBLOCK_MASK_REG th]) THEN
  ASM_SIMP_TAC[SIXBLOCK_USHR] THEN
  (* ---- seven conjuncts: ct1..ct5, masked-ct6, GHASH ---- *)
  CONJ_TAC THENL [CT_CLOSE_6 1; ALL_TAC] THEN
  CONJ_TAC THENL [CONV_TAC SYM_CONV THEN GCM_6BLOCK_CT2_STEP_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [CONV_TAC SYM_CONV THEN GCM_6BLOCK_CT3_STEP_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [CONV_TAC SYM_CONV THEN GCM_6BLOCK_CT4_STEP_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [CONV_TAC SYM_CONV THEN GCM_6BLOCK_CT5_STEP_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [GCM_6B_MASKED_CT6_CLOSE; ALL_TAC] THEN
  (* ---- ct6 abbreviation (spec form) so the closer's ctm6 works ---- *)
  ABBREV_TAC `ct6 = word_xor pt6
    (aes256_encrypt (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ivec))))) [rk0;rk1;rk2;rk3;rk4;rk5;rk6;rk7;rk8;rk9;rk10;rk11;rk12;rk13;rk14]):(128)word` THEN
  (* ---- GHASH conjunct ---- *)
  GCM_6B_GHASH_CLOSE);;

(* ========================================================================= *)
(* The L256_enc_blocks_more_than_6 branch (7-block: six full blocks +        *)
(* partial block 7, total 97..112 bytes) of the single binary, proved as a   *)
(* standalone theorem and applied exactly as the XTS length-band lemmas are. *)
(* Reuses the seven-block masked closers from gcm_seven_block_closers.ml.    *)
(* ========================================================================= *)

needs "arm/proofs/utils/gcm_seven_block_closers.ml";;

(* --- 7-block-branch length/cascade helpers (thresholds over 96+byte_len) --- *)

let GCM_CBZ_LEMMA7 = prove
 (`1 <= byte_len /\ byte_len <= 16 ==> ~(val(word(768+8*byte_len):int64) = 0)`,
  STRIP_TAC THEN SUBGOAL_THEN `val(word(768+8*byte_len):int64) = 768+8*byte_len` SUBST1_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC;
    ASM_ARITH_TAC]);;

let GCM_WSUB7 = prove
 (`byte_len <= 16 ==> word_sub (word (96+byte_len):int64) (word 1) = word (95 + byte_len)`,
  CONV_TAC WORD_RULE);;

let GCM_X7_LEMMA7 = prove
 (`1 <= byte_len /\ byte_len <= 16 ==>
   word_add (word_and (word_sub (word_ushr (word (768+8*byte_len):int64) 3) (word 1))
                      (word 18446744073709551488)) in_ptr = in_ptr`,
  STRIP_TAC THEN
  SUBGOAL_THEN `word_ushr (word (768+8*byte_len):int64) 3 = word (96+byte_len)` SUBST1_TAC THENL
   [ASM_SIMP_TAC[SEVENBLOCK_USHR]; ALL_TAC] THEN
  ASM_SIMP_TAC[GCM_WSUB7] THEN
  SUBGOAL_THEN `word_and (word (95+byte_len):int64) (word 18446744073709551488) = word 0` SUBST1_TAC THENL
   [MATCH_MP_TAC GCM_ANDMASK0 THEN ASM_ARITH_TAC; ALL_TAC] THEN
  CONV_TAC WORD_RULE);;

let GCM_X7TAIL_LEMMA7 = prove
 (`byte_len <= 16 ==>
   word_sub (word_add in_ptr (word_ushr (word (768+8*byte_len):int64) 3)) in_ptr = word (96+byte_len)`,
  ASM_SIMP_TAC[SEVENBLOCK_USHR] THEN CONV_TAC WORD_RULE);;

(* Cascade for more_than_6: total lanes = 96+byte_len (97..112).  The b.gt #112
   falls through (total <= 112), the b.gt #96 is taken (total >= 97) into
   .more_than_6.  FALSE threshold = {112}; TRUE threshold = 96. *)
let GCM_CASC7_FALSE = prove
 (`!byte_len t. byte_len <= 16 /\ 112 <= t /\ t <= 112 ==>
    ((~(val (word_sub (word (96+byte_len):int64) (word t)) = 0) /\
      (ival (word_sub (word (96+byte_len):int64) (word t)) < &0 <=>
       ~(ival (word (96+byte_len):int64) - &t = ival (word_sub (word (96+byte_len):int64) (word t)))))
     <=> F)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `ival(word (96+byte_len):int64) = &(96+byte_len)` ASSUME_TAC THENL
   [MATCH_MP_TAC NBLOCK_IVAL_WORD_SMALL THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `word_sub (word (96+byte_len):int64) (word t) = iword(&(96+byte_len) - &t)` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM IWORD_INT_SUB; WORD_IWORD]; ALL_TAC] THEN
  SUBGOAL_THEN `ival(iword(&(96+byte_len) - &t):int64) = &(96+byte_len) - &t` ASSUME_TAC THENL
   [MATCH_MP_TAC IVAL_IWORD THEN REWRITE_TAC[DIMINDEX_64] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_SUB_CONV) THEN
    SUBGOAL_THEN `&(96+byte_len):int <= &112 /\ &112:int <= &t /\ &t:int <= &112` MP_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN INT_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[VAL_EQ_0; GSYM IVAL_EQ_0] THEN
  SUBGOAL_THEN `&(96+byte_len):int <= &112 /\ &112:int <= &t` MP_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN INT_ARITH_TAC);;

let GCM_CASC7_TRUE = prove
 (`1 <= byte_len /\ byte_len <= 16 ==>
    ((~(val (word_sub (word (96+byte_len):int64) (word 96)) = 0) /\
      (ival (word_sub (word (96+byte_len):int64) (word 96)) < &0 <=>
       ~(ival (word (96+byte_len):int64) - &96 = ival (word_sub (word (96+byte_len):int64) (word 96)))))
     <=> T)`,
  STRIP_TAC THEN
  SUBGOAL_THEN `ival(word (96+byte_len):int64) = &(96+byte_len)` ASSUME_TAC THENL
   [MATCH_MP_TAC NBLOCK_IVAL_WORD_SMALL THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `word_sub (word (96+byte_len):int64) (word 96) = iword(&(96+byte_len) - &96)` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM IWORD_INT_SUB; WORD_IWORD]; ALL_TAC] THEN
  SUBGOAL_THEN `ival(iword(&(96+byte_len) - &96):int64) = &(96+byte_len) - &96` ASSUME_TAC THENL
   [MATCH_MP_TAC IVAL_IWORD THEN REWRITE_TAC[DIMINDEX_64] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_SUB_CONV) THEN
    SUBGOAL_THEN `&(96+byte_len):int <= &112` MP_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN INT_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[VAL_EQ_0; GSYM IVAL_EQ_0] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_ADD] THEN
  SUBGOAL_THEN `&1:int <= &byte_len` MP_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN INT_ARITH_TAC);;

let GCM_CASCADE7_TAC : tactic =
  FIRST_X_ASSUM(fun bl16 -> if concl bl16 = `byte_len <= 16` then
    FIRST_X_ASSUM(fun bl1 -> if concl bl1 = `1 <= byte_len` then
      RULE_ASSUM_TAC(REWRITE_RULE(
        (map (fun t -> MATCH_MP GCM_CASC7_FALSE (CONJ bl16
                (CONJ (ARITH_RULE(vsubst[mk_numeral(num_of_int t),`t:num`] `112 <= t`))
                      (ARITH_RULE(vsubst[mk_numeral(num_of_int t),`t:num`] `t <= 112`)))))
             [112]) @
        [MATCH_MP GCM_CASC7_TRUE (CONJ bl1 bl16); COND_CLAUSES])) THEN
      ASSUME_TAC bl1 THEN ASSUME_TAC bl16
    else NO_TAC)
  else NO_TAC);;

(* --- The 7-block branch goal (six full + one partial block). --- *)

let gcm_7b_goal = `!in_ptr out_ptr xi_ptr ivec_ptr key_ptr htable_ptr
    (pt1:(128)word) (pt2:(128)word) (pt3:(128)word) (pt4:(128)word) (pt5:(128)word) (pt6:(128)word) (pt7:(128)word)
    (out0:(128)word)
    (ivec:(128)word)
    (rk0:(128)word) (rk1:(128)word) (rk2:(128)word) (rk3:(128)word)
    (rk4:(128)word) (rk5:(128)word) (rk6:(128)word) (rk7:(128)word)
    (rk8:(128)word) (rk9:(128)word) (rk10:(128)word) (rk11:(128)word)
    (rk12:(128)word) (rk13:(128)word) (rk14:(128)word)
    (xi:(128)word) (h:(128)word) (h1k:(128)word) (h3k:(128)word) (h5k:(128)word) (h7k:(128)word)
    byte_len stackptr pc.
    1 <= byte_len /\ byte_len <= 16 /\
    aligned 16 stackptr /\
    nonoverlapping (word pc,4600) (in_ptr:int64,112) /\
    nonoverlapping (word pc,4600) (out_ptr:int64,112) /\
    nonoverlapping (word pc,4600) (xi_ptr:int64,16) /\
    nonoverlapping (word pc,4600) (ivec_ptr:int64,16) /\
    nonoverlapping (word pc,4600) (key_ptr:int64,240) /\
    nonoverlapping (word pc,4600) (htable_ptr:int64,256) /\
    nonoverlapping (word pc,4600) (stackptr:int64,80) /\
    nonoverlapping (in_ptr,112) (out_ptr,112) /\
    nonoverlapping (in_ptr,112) (xi_ptr,16) /\
    nonoverlapping (in_ptr,112) (ivec_ptr,16) /\
    nonoverlapping (out_ptr,112) (xi_ptr,16) /\
    nonoverlapping (out_ptr,112) (ivec_ptr,16) /\
    nonoverlapping (xi_ptr,16) (ivec_ptr,16) /\
    nonoverlapping (key_ptr,240) (out_ptr,112) /\
    nonoverlapping (key_ptr,240) (xi_ptr,16) /\
    nonoverlapping (key_ptr,240) (ivec_ptr,16) /\
    nonoverlapping (htable_ptr,256) (out_ptr,112) /\
    nonoverlapping (htable_ptr,256) (xi_ptr,16) /\
    nonoverlapping (htable_ptr,256) (ivec_ptr,16) /\
    nonoverlapping (stackptr,80) (out_ptr,112) /\
    nonoverlapping (stackptr,80) (xi_ptr,16) /\
    nonoverlapping (stackptr,80) (ivec_ptr,16) /\
    nonoverlapping (stackptr,80) (in_ptr,112) /\
    nonoverlapping (stackptr,80) (key_ptr,240) /\
    nonoverlapping (stackptr,80) (htable_ptr,256) /\
    nonoverlapping (ivec_ptr,16) (word pc,4600) /\
    nonoverlapping (xi_ptr,16) (word pc,4600) /\
    nonoverlapping (out_ptr,112) (word pc,4600)
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) aes256_gcm_mc /\
           read PC s = word pc /\
           C_ARGUMENTS [in_ptr; word (768 + 8 * byte_len); out_ptr; xi_ptr;
                        ivec_ptr; key_ptr; htable_ptr] s /\
           read SP s = word_add stackptr (word 80) /\
           read (memory :> bytes128 in_ptr) s = pt1 /\
           read (memory :> bytes128 (word_add in_ptr (word 16))) s = pt2 /\
           read (memory :> bytes128 (word_add in_ptr (word 32))) s = pt3 /\
           read (memory :> bytes128 (word_add in_ptr (word 48))) s = pt4 /\
           read (memory :> bytes128 (word_add in_ptr (word 64))) s = pt5 /\
           read (memory :> bytes128 (word_add in_ptr (word 80))) s = pt6 /\
           read (memory :> bytes128 (word_add in_ptr (word 96))) s = pt7 /\
           read (memory :> bytes128 (word_add out_ptr (word 96))) s = out0 /\
           read (memory :> bytes128 ivec_ptr) s = ivec /\
           read (memory :> bytes128 (word_add key_ptr (word 0))) s = rk0 /\
           read (memory :> bytes128 (word_add key_ptr (word 16))) s = rk1 /\
           read (memory :> bytes128 (word_add key_ptr (word 32))) s = rk2 /\
           read (memory :> bytes128 (word_add key_ptr (word 48))) s = rk3 /\
           read (memory :> bytes128 (word_add key_ptr (word 64))) s = rk4 /\
           read (memory :> bytes128 (word_add key_ptr (word 80))) s = rk5 /\
           read (memory :> bytes128 (word_add key_ptr (word 96))) s = rk6 /\
           read (memory :> bytes128 (word_add key_ptr (word 112))) s = rk7 /\
           read (memory :> bytes128 (word_add key_ptr (word 128))) s = rk8 /\
           read (memory :> bytes128 (word_add key_ptr (word 144))) s = rk9 /\
           read (memory :> bytes128 (word_add key_ptr (word 160))) s = rk10 /\
           read (memory :> bytes128 (word_add key_ptr (word 176))) s = rk11 /\
           read (memory :> bytes128 (word_add key_ptr (word 192))) s = rk12 /\
           read (memory :> bytes128 (word_add key_ptr (word 208))) s = rk13 /\
           read (memory :> bytes128 (word_add key_ptr (word 224))) s = rk14 /\
           read (memory :> bytes128 xi_ptr) s = xi /\
           read (memory :> bytes128 htable_ptr) s = word_swaphalves128 h /\
           read (memory :> bytes128 (word_add htable_ptr (word 16))) s = h1k /\
           read (memory :> bytes128 (word_add htable_ptr (word 32))) s =
             word_swaphalves128 (polyval_dot h h) /\
           read (memory :> bytes128 (word_add htable_ptr (word 48))) s =
             word_swaphalves128 (polyval_dot h (polyval_dot h h)) /\
           read (memory :> bytes128 (word_add htable_ptr (word 64))) s = h3k /\
           read (memory :> bytes128 (word_add htable_ptr (word 80))) s =
             word_swaphalves128 (polyval_dot (polyval_dot h h) (polyval_dot h h)) /\
           read (memory :> bytes128 (word_add htable_ptr (word 96))) s =
             word_swaphalves128 (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) /\
           read (memory :> bytes128 (word_add htable_ptr (word 112))) s = h5k /\
           read (memory :> bytes128 (word_add htable_ptr (word 128))) s =
             word_swaphalves128 (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) h) /\
           read (memory :> bytes128 (word_add htable_ptr (word 144))) s =
             word_swaphalves128 (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) h) h) /\
           read (memory :> bytes128 (word_add htable_ptr (word 160))) s = h7k /\
           word_subword h1k (0,64):(64)word = karatsuba_mid h /\
           word_subword h1k (64,64):(64)word =
             karatsuba_mid (polyval_dot h h) /\
           word_subword h3k (0,64):(64)word =
             karatsuba_mid (polyval_dot h (polyval_dot h h)) /\
           word_subword h3k (64,64):(64)word =
             karatsuba_mid (polyval_dot (polyval_dot h h) (polyval_dot h h)) /\
           word_subword h5k (0,64):(64)word =
             karatsuba_mid (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) /\
           word_subword h5k (64,64):(64)word =
             karatsuba_mid (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) h) /\
           word_subword h7k (0,64):(64)word =
             karatsuba_mid (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) h) h))
      (\s. let ct1 =
             word_xor pt1
               (aes256_encrypt ivec [rk0;rk1;rk2;rk3;rk4;rk5;rk6;rk7;rk8;rk9;rk10;rk11;rk12;rk13;rk14]) in
           let ct2 =
             word_xor pt2
               (aes256_encrypt (gcm_ctr_inc ivec) [rk0;rk1;rk2;rk3;rk4;rk5;rk6;rk7;rk8;rk9;rk10;rk11;rk12;rk13;rk14]) in
           let ct3 =
             word_xor pt3
               (aes256_encrypt (gcm_ctr_inc (gcm_ctr_inc ivec)) [rk0;rk1;rk2;rk3;rk4;rk5;rk6;rk7;rk8;rk9;rk10;rk11;rk12;rk13;rk14]) in
           let ct4 =
             word_xor pt4
               (aes256_encrypt (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ivec))) [rk0;rk1;rk2;rk3;rk4;rk5;rk6;rk7;rk8;rk9;rk10;rk11;rk12;rk13;rk14]) in
           let ct5 =
             word_xor pt5
               (aes256_encrypt (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ivec)))) [rk0;rk1;rk2;rk3;rk4;rk5;rk6;rk7;rk8;rk9;rk10;rk11;rk12;rk13;rk14]) in
           let ct6 =
             word_xor pt6
               (aes256_encrypt (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ivec))))) [rk0;rk1;rk2;rk3;rk4;rk5;rk6;rk7;rk8;rk9;rk10;rk11;rk12;rk13;rk14]) in
           let ct7 =
             word_xor pt7
               (aes256_encrypt (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ivec)))))) [rk0;rk1;rk2;rk3;rk4;rk5;rk6;rk7;rk8;rk9;rk10;rk11;rk12;rk13;rk14]) in
           let mask = word (2 EXP (8 * byte_len) - 1):(128)word in
           let ctm7 = word_and ct7 mask in
           read PC s = word(pc + 4588) /\
           read X0 s = word (96 + byte_len) /\
           read (memory :> bytes128 out_ptr) s = ct1 /\
           read (memory :> bytes128 (word_add out_ptr (word 16))) s = ct2 /\
           read (memory :> bytes128 (word_add out_ptr (word 32))) s = ct3 /\
           read (memory :> bytes128 (word_add out_ptr (word 48))) s = ct4 /\
           read (memory :> bytes128 (word_add out_ptr (word 64))) s = ct5 /\
           read (memory :> bytes128 (word_add out_ptr (word 80))) s = ct6 /\
           read (memory :> bytes128 (word_add out_ptr (word 96))) s =
             word_or ctm7 (word_and out0 (word_not mask)) /\
           read (memory :> bytes128 xi_ptr) s =
             word_reversefields 8
               (ghash_polyval_acc h (word_reversefields 8 xi)
                                    [word_reversefields 8 ct1;
                                     word_reversefields 8 ct2;
                                     word_reversefields 8 ct3;
                                     word_reversefields 8 ct4;
                                     word_reversefields 8 ct5;
                                     word_reversefields 8 ct6;
                                     word_reversefields 8 ctm7]))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [memory :> bytes(out_ptr,112);
                  memory :> bytes(xi_ptr,16);
                  memory :> bytes(ivec_ptr,16)] ,,
       MAYCHANGE [SP] ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes64 stackptr;
                  memory :> bytes64 (word_add stackptr (word 8));
                  memory :> bytes64 (word_add stackptr (word 16));
                  memory :> bytes64 (word_add stackptr (word 24));
                  memory :> bytes64 (word_add stackptr (word 32));
                  memory :> bytes64 (word_add stackptr (word 40));
                  memory :> bytes64 (word_add stackptr (word 48));
                  memory :> bytes64 (word_add stackptr (word 56));
                  memory :> bytes64 (word_add stackptr (word 64));
                  memory :> bytes64 (word_add stackptr (word 72))])`;;

(* --- 7-block store-based ct abbreviation + conjunct closers. --- *)

(* 7-block ct abbreviation uses the shared strict `abbrev_ct_from_store`
   (defined once near the 2-block band).  The earlier per-band `abbrev_ct7`
   was the prototype of that strict matcher and is now folded into the shared
   helper. *)

(* ct1 closer (counter = ivec). *)
let CT_CLOSE_7 nidx =
  let s13n = "s13_"^string_of_int nidx and ctn = "ct"^string_of_int nidx in
  EXPAND_TAC ctn THEN EXPAND_TAC s13n THEN
  REWRITE_TAC[AES256_ENCRYPT_UNFOLD; LET_DEF; LET_END_DEF; WORD_XOR_ASSOC] THEN ASM_REWRITE_TAC[];;

(* masked-ct7 store conjunct closer: block-7 = gcm_ctr_inc^6 -> "+6". *)
let GCM_7B_MASKED_CT7_CLOSE : tactic =
  let bri = WORD_BLAST `word_bytereverse (word_bytereverse (x:(32)word)) = x` in
  let add6 = WORD_RULE `word_add (word_add (word_add (word_add (word_add (word_add (x:(32)word) (word 1)) (word 1)) (word 1)) (word 1)) (word 1)) (word 1) = word_add x (word 6)` in
  REWRITE_TAC[NBLOCK_MASK_IDEM] THEN
  MATCH_MP_TAC(MESON[] `x = y ==> word_or (word_and x m) r = word_or (word_and y m) r:(128)word`) THEN
  CONV_TAC SYM_CONV THEN REWRITE_TAC[AES256_ENCRYPT_UNFOLD] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[WORD_XOR_ASSOC] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REPEAT(AP_THM_TAC ORELSE AP_TERM_TAC) THEN
  REWRITE_TAC[gcm_ctr_inc] THEN
  REWRITE_TAC[WORD_REVERSEFIELDS_REVERSEFIELDS; WORD_REVERSEFIELDS_8_BYTEREVERSE_32] THEN
  REWRITE_TAC[INSERT_SUBWORD; INSERT_IDEM] THEN
  REWRITE_TAC[bri] THEN REWRITE_TAC[add6] THEN
  REWRITE_TAC[CTR_WORD_INSERT];;

(* The GHASH conjunct closes via GCM_7B_GHASH_CLOSE (mirror of the 6-block   *)
(* GCM_6B_GHASH_CLOSE) defined in seven_ghash_closer.ml — its bridge MP_TAC  *)
(* uses the genuine htable h7k now present in the goal.                      *)

(* --- 7-block GHASH final-closure helper tactics (mirror 6-block). --- *)

(* ========================================================================= *)
(* Self-contained 7-block GHASH conjunct closer for the single-binary        *)
(* aes256_gcm.ml more_than_6 (7-block) branch.  Reaches "No subgoals" from   *)
(* the final GHASH equality (machine word_join = spec word_reversefields).   *)
(* Mirrors the 6-block recipe (GCM_6B_GHASH_CLOSE); adds the ks7 +6-counter  *)
(* bridge and the in-asm b0-general mask-register collapse that the 7-block  *)
(* sim leaves baked into final_xi.                                           *)
(* ========================================================================= *)

(* xi half-swap normalization (shared with 4-block, redefined locally). *)
let XI_HS_LO_7 = prove
 (`word_subword (word_reversefields 8 (word_join (word_subword (xi:(128)word) (64,64):(64)word) (word_subword xi (0,64):(64)word):(128)word)) (0,64):(64)word =
   word_subword (word_reversefields 8 xi) (0,64)`,
  REWRITE_TAC[GSYM REV8_JOIN_FOLD; REVERSEFIELDS8_SUBWORD_LO; REVERSEFIELDS8_SUBWORD_HI] THEN
  CONV_TAC WORD_BLAST);;

let XI_HS_HI_7 = prove
 (`word_subword (word_reversefields 8 (word_join (word_subword (xi:(128)word) (64,64):(64)word) (word_subword xi (0,64):(64)word):(128)word)) (64,64):(64)word =
   word_subword (word_reversefields 8 xi) (64,64)`,
  REWRITE_TAC[GSYM REV8_JOIN_FOLD; REVERSEFIELDS8_SUBWORD_LO; REVERSEFIELDS8_SUBWORD_HI] THEN
  CONV_TAC WORD_BLAST);;

let GCM_7B_TAIL_NOFINAL : tactic =
  ABBREV_TAC `mask = word (2 EXP (8 * byte_len) - 1):(128)word` THEN
  ABBREV_TAC `ctm7 = word_and (ct7:(128)word) mask` THEN
  SUBGOAL_THEN `word_and (mask:(128)word) (ct7:(128)word) = ctm7`
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th]) THENL [
    EXPAND_TAC "ctm7" THEN CONV_TAC WORD_BITWISE_RULE; ALL_TAC ] THEN
  SUBGOAL_THEN
    `polyval_dot (polyval_dot (polyval_dot (h:int128) h) h) h =
     polyval_dot (polyval_dot h h) (polyval_dot h h)`
    (fun th -> REWRITE_TAC[th]) THENL
    [REWRITE_TAC[POLYVAL_DOT_H4_EQ_LOCAL]; ALL_TAC] THEN
  SUBGOAL_THEN
    `polyval_dot (polyval_dot (h:int128) h) h = polyval_dot h (polyval_dot h h)`
    (fun th -> REWRITE_TAC[th]) THENL
    [REWRITE_TAC[polyval_dot] THEN REWRITE_TAC[WORD_PMUL_SYM]; ALL_TAC] THEN
  MP_TAC(SPECL
    [`word_reversefields 8 (word_xor xi ct1):int128`;
     `word_reversefields 8 ct2:int128`;
     `word_reversefields 8 ct3:int128`;
     `word_reversefields 8 ct4:int128`;
     `word_reversefields 8 ct5:int128`;
     `word_reversefields 8 ct6:int128`;
     `word_reversefields 8 ctm7:int128`;
     `h:int128`;
     `h1k:int128`;
     `word_join (word 0:(64)word) (word_subword (h1k:(128)word) (64,64):(64)word):(128)word`;
     `h3k:int128`;
     `word_join (word 0:(64)word) (word_subword (h3k:(128)word) (64,64):(64)word):(128)word`;
     `h5k:int128`;
     `word_join (word 0:(64)word) (word_subword (h5k:(128)word) (64,64):(64)word):(128)word`;
     `h7k:int128`]
    GHASH_7BLOCK_KARATSUBA_EQ_POLYVAL_ACC) THEN
  SUBGOAL_THEN
    `word_subword (word_join (word 0:(64)word) (word_subword (h1k:(128)word) (64,64):(64)word):(128)word) (0,64):(64)word =
     karatsuba_mid (polyval_dot h h)`
    (fun th -> REWRITE_TAC[th]) THENL [
    SUBGOAL_THEN
      `word_subword (word_join (word 0:(64)word) (word_subword (h1k:(128)word) (64,64):(64)word):(128)word) (0,64):(64)word =
       word_subword (h1k:(128)word) (64,64):(64)word`
      (fun th -> REWRITE_TAC[th]) THENL [CONV_TAC WORD_BLAST; ASM_REWRITE_TAC[]]; ALL_TAC ] THEN
  SUBGOAL_THEN
    `word_subword (word_join (word 0:(64)word) (word_subword (h3k:(128)word) (64,64):(64)word):(128)word) (0,64):(64)word =
     karatsuba_mid (polyval_dot (polyval_dot h h) (polyval_dot h h))`
    (fun th -> REWRITE_TAC[th]) THENL [
    SUBGOAL_THEN
      `word_subword (word_join (word 0:(64)word) (word_subword (h3k:(128)word) (64,64):(64)word):(128)word) (0,64):(64)word =
       word_subword (h3k:(128)word) (64,64):(64)word`
      (fun th -> REWRITE_TAC[th]) THENL [CONV_TAC WORD_BLAST; ASM_REWRITE_TAC[]]; ALL_TAC ] THEN
  SUBGOAL_THEN
    `word_subword (word_join (word 0:(64)word) (word_subword (h5k:(128)word) (64,64):(64)word):(128)word) (0,64):(64)word =
     karatsuba_mid (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) h)`
    (fun th -> REWRITE_TAC[th]) THENL [
    SUBGOAL_THEN
      `word_subword (word_join (word 0:(64)word) (word_subword (h5k:(128)word) (64,64):(64)word):(128)word) (0,64):(64)word =
       word_subword (h5k:(128)word) (64,64):(64)word`
      (fun th -> REWRITE_TAC[th]) THENL [CONV_TAC WORD_BLAST; ASM_REWRITE_TAC[]]; ALL_TAC ] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN
  REWRITE_TAC[ghash_7block_karatsuba; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[SWAPHALVES128_SUBWORD_LO; SWAPHALVES128_SUBWORD_HI] THEN
  SUBGOAL_THEN
    `word_subword (word_join (word 0:(64)word) (karatsuba_mid (polyval_dot h h):(64)word):(128)word) (0,64):(64)word =
     karatsuba_mid (polyval_dot h h)`
    (fun th -> REWRITE_TAC[th]) THENL [CONV_TAC WORD_BLAST; ALL_TAC] THEN
  SUBGOAL_THEN
    `word_subword (word_join (word 0:(64)word) (karatsuba_mid (polyval_dot (polyval_dot h h) (polyval_dot h h)):(64)word):(128)word) (0,64):(64)word =
     karatsuba_mid (polyval_dot (polyval_dot h h) (polyval_dot h h))`
    (fun th -> REWRITE_TAC[th]) THENL [CONV_TAC WORD_BLAST; ALL_TAC] THEN
  SUBGOAL_THEN
    `word_subword (word_join (word 0:(64)word) (karatsuba_mid (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) h):(64)word):(128)word) (0,64):(64)word =
     karatsuba_mid (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) h)`
    (fun th -> REWRITE_TAC[th]) THENL [CONV_TAC WORD_BLAST; ALL_TAC] THEN
  REWRITE_TAC[GSYM karatsuba_mid] THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
  CONV_TAC SYM_CONV THEN
  FIRST_ASSUM(fun th ->
    if is_eq(concl th) && rand(concl th) = `final_xi:(128)word` &&
       (try (let l = lhs(concl th) in is_comb l &&
             (let r = rator l in not(is_comb r && (try fst(dest_const(rator r)) = "read" with _ -> false))))
        with _ -> false)
    then SUBST1_TAC(SYM th) else NO_TAC) THEN
  REWRITE_TAC[REV64_LOWER_LANE; REV64_UPPER_LANE; REV8_JOIN_FOLD] THEN
  MATCH_MP_TAC(MESON[]
    `x = y ==> word_reversefields 8 x = word_reversefields 8 y:(128)word`) THEN
  REWRITE_TAC[WORD_SWAP_HALVES_INVOLUTION] THEN
  CONV_TAC(LAND_CONV(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
  REWRITE_TAC[WORD_INSERT_AS_JOIN_LO; WORD_INSERT_AS_JOIN_HI;
              KAR_SUBWORD_LEMMA; WORD_SWAP_HALVES_INVOLUTION;
              WORD_OR_REFL; WORD_XOR_ASSOC; WORD_SUBWORD_XOR;
              SWAPHALVES128_SUBWORD_LO; SWAPHALVES128_SUBWORD_HI] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[HALFSWAP_XOR; GSYM WORD_REVERSEFIELDS_XOR_8_128;
              WORD_XOR_0; WORD_XOR_ASSOC;
              REV8_JOIN_FOLD; REVERSEFIELDS8_SUBWORD_LO; REVERSEFIELDS8_SUBWORD_HI] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  CONV_TAC(TOP_DEPTH_CONV PMUL_NORM_CONV) THEN
  SUBGOAL_THEN
    `word_subword (word 0:(128)word) (0,64):(64)word = word 0 /\
     word_subword (word 0:(128)word) (64,64):(64)word = word 0`
    (fun th -> REWRITE_TAC[th]) THENL [CONJ_TAC THEN CONV_TAC WORD_BLAST; ALL_TAC] THEN
  REWRITE_TAC[WORD_XOR_0; WORD_XOR_0_LEFT] THEN
  REWRITE_TAC[karatsuba_mid; WORD_REVERSEFIELDS_XOR_8_128; WORD_SUBWORD_XOR] THEN
  (* 30 atomic ABBREVs *)
  ABBREV_TAC `(c1lo:(64)word) = word_subword (word_reversefields 8 (ct1:(128)word)) (0,64)` THEN
  ABBREV_TAC `(c1hi:(64)word) = word_subword (word_reversefields 8 (ct1:(128)word)) (64,64)` THEN
  ABBREV_TAC `(c2lo:(64)word) = word_subword (word_reversefields 8 (ct2:(128)word)) (0,64)` THEN
  ABBREV_TAC `(c2hi:(64)word) = word_subword (word_reversefields 8 (ct2:(128)word)) (64,64)` THEN
  ABBREV_TAC `(c3lo:(64)word) = word_subword (word_reversefields 8 (ct3:(128)word)) (0,64)` THEN
  ABBREV_TAC `(c3hi:(64)word) = word_subword (word_reversefields 8 (ct3:(128)word)) (64,64)` THEN
  ABBREV_TAC `(c4lo:(64)word) = word_subword (word_reversefields 8 (ct4:(128)word)) (0,64)` THEN
  ABBREV_TAC `(c4hi:(64)word) = word_subword (word_reversefields 8 (ct4:(128)word)) (64,64)` THEN
  ABBREV_TAC `(c5lo:(64)word) = word_subword (word_reversefields 8 (ct5:(128)word)) (0,64)` THEN
  ABBREV_TAC `(c5hi:(64)word) = word_subword (word_reversefields 8 (ct5:(128)word)) (64,64)` THEN
  ABBREV_TAC `(c6lo:(64)word) = word_subword (word_reversefields 8 (ct6:(128)word)) (0,64)` THEN
  ABBREV_TAC `(c6hi:(64)word) = word_subword (word_reversefields 8 (ct6:(128)word)) (64,64)` THEN
  ABBREV_TAC `(c7lo:(64)word) = word_subword (word_reversefields 8 (ctm7:(128)word)) (0,64)` THEN
  ABBREV_TAC `(c7hi:(64)word) = word_subword (word_reversefields 8 (ctm7:(128)word)) (64,64)` THEN
  ABBREV_TAC `(xilo:(64)word) = word_subword (word_reversefields 8 (xi:(128)word)) (0,64)` THEN
  ABBREV_TAC `(xihi:(64)word) = word_subword (word_reversefields 8 (xi:(128)word)) (64,64)` THEN
  ABBREV_TAC `(hd0:(64)word) = word_subword (h:(128)word) (0,64)` THEN
  ABBREV_TAC `(hd1:(64)word) = word_subword (h:(128)word) (64,64)` THEN
  ABBREV_TAC `(he0:(64)word) = word_subword ((polyval_dot h h):(128)word) (0,64)` THEN
  ABBREV_TAC `(he1:(64)word) = word_subword ((polyval_dot h h):(128)word) (64,64)` THEN
  ABBREV_TAC `(hf0:(64)word) = word_subword ((polyval_dot h (polyval_dot h h)):(128)word) (0,64)` THEN
  ABBREV_TAC `(hf1:(64)word) = word_subword ((polyval_dot h (polyval_dot h h)):(128)word) (64,64)` THEN
  ABBREV_TAC `(hg0:(64)word) = word_subword ((polyval_dot (polyval_dot h h) (polyval_dot h h)):(128)word) (0,64)` THEN
  ABBREV_TAC `(hg1:(64)word) = word_subword ((polyval_dot (polyval_dot h h) (polyval_dot h h)):(128)word) (64,64)` THEN
  ABBREV_TAC `(hh0:(64)word) = word_subword ((polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h):(128)word) (0,64)` THEN
  ABBREV_TAC `(hh1:(64)word) = word_subword ((polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h):(128)word) (64,64)` THEN
  ABBREV_TAC `(hj0:(64)word) = word_subword ((polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) h):(128)word) (0,64)` THEN
  ABBREV_TAC `(hj1:(64)word) = word_subword ((polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) h):(128)word) (64,64)` THEN
  ABBREV_TAC `(hm0:(64)word) = word_subword ((polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) h) h):(128)word) (0,64)` THEN
  ABBREV_TAC `(hm1:(64)word) = word_subword ((polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) h) h):(128)word) (64,64)` THEN
  ASM_REWRITE_TAC[] THEN
  (* 21 inner pmul ABBREVs *)
  ABBREV_TAC `(w1lo:(128)word) = word_pmul (word_xor (xilo:(64)word) (c1lo:(64)word)) (hm0:(64)word)` THEN
  ABBREV_TAC `(w1hi:(128)word) = word_pmul (word_xor (xihi:(64)word) (c1hi:(64)word)) (hm1:(64)word)` THEN
  ABBREV_TAC `(w1md:(128)word) = word_pmul (word_xor (word_xor (xihi:(64)word) (c1hi:(64)word)) (word_xor (xilo:(64)word) (c1lo:(64)word))) (word_xor (hm0:(64)word) (hm1:(64)word))` THEN
  ABBREV_TAC `(w2lo:(128)word) = word_pmul (c2lo:(64)word) (hj0:(64)word)` THEN
  ABBREV_TAC `(w2hi:(128)word) = word_pmul (c2hi:(64)word) (hj1:(64)word)` THEN
  ABBREV_TAC `(w2md:(128)word) = word_pmul (word_xor (c2hi:(64)word) (c2lo:(64)word)) (word_xor (hj0:(64)word) (hj1:(64)word))` THEN
  ABBREV_TAC `(w3lo:(128)word) = word_pmul (c3lo:(64)word) (hh0:(64)word)` THEN
  ABBREV_TAC `(w3hi:(128)word) = word_pmul (c3hi:(64)word) (hh1:(64)word)` THEN
  ABBREV_TAC `(w3md:(128)word) = word_pmul (word_xor (c3hi:(64)word) (c3lo:(64)word)) (word_xor (hh0:(64)word) (hh1:(64)word))` THEN
  ABBREV_TAC `(w4lo:(128)word) = word_pmul (c4lo:(64)word) (hg0:(64)word)` THEN
  ABBREV_TAC `(w4hi:(128)word) = word_pmul (c4hi:(64)word) (hg1:(64)word)` THEN
  ABBREV_TAC `(w4md:(128)word) = word_pmul (word_xor (c4hi:(64)word) (c4lo:(64)word)) (word_xor (hg0:(64)word) (hg1:(64)word))` THEN
  ABBREV_TAC `(w5lo:(128)word) = word_pmul (c5lo:(64)word) (hf0:(64)word)` THEN
  ABBREV_TAC `(w5hi:(128)word) = word_pmul (c5hi:(64)word) (hf1:(64)word)` THEN
  ABBREV_TAC `(w5md:(128)word) = word_pmul (word_xor (c5hi:(64)word) (c5lo:(64)word)) (word_xor (hf0:(64)word) (hf1:(64)word))` THEN
  ABBREV_TAC `(w6lo:(128)word) = word_pmul (c6lo:(64)word) (he0:(64)word)` THEN
  ABBREV_TAC `(w6hi:(128)word) = word_pmul (c6hi:(64)word) (he1:(64)word)` THEN
  ABBREV_TAC `(w6md:(128)word) = word_pmul (word_xor (c6hi:(64)word) (c6lo:(64)word)) (word_xor (he0:(64)word) (he1:(64)word))` THEN
  ABBREV_TAC `(w7lo:(128)word) = word_pmul (c7lo:(64)word) (hd0:(64)word)` THEN
  ABBREV_TAC `(w7hi:(128)word) = word_pmul (c7hi:(64)word) (hd1:(64)word)` THEN
  ABBREV_TAC `(w7md:(128)word) = word_pmul (word_xor (c7hi:(64)word) (c7lo:(64)word)) (word_xor (hd0:(64)word) (hd1:(64)word))` THEN
  REWRITE_TAC[DOUBLE_SUBWORD_JOIN; DOUBLE_SUBWORD_JOIN_HI; WORD_SUBWORD_XOR] THEN
  SUBGOAL_THEN
    `word_pmul (word_xor (xihi:(64)word) (word_xor (c1hi:(64)word) (word_xor (xilo:(64)word) (c1lo:(64)word)))) (word_xor (hm0:(64)word) (hm1:(64)word)):(128)word = w1md`
    (fun th -> REWRITE_TAC[th]) THENL
    [EXPAND_TAC "w1md" THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  (* 42 z-vars *)
  ABBREV_TAC `(w1lo_l:(64)word) = word_subword (w1lo:(128)word) (0,64)` THEN
  ABBREV_TAC `(w1lo_h:(64)word) = word_subword (w1lo:(128)word) (64,64)` THEN
  ABBREV_TAC `(w1hi_l:(64)word) = word_subword (w1hi:(128)word) (0,64)` THEN
  ABBREV_TAC `(w1hi_h:(64)word) = word_subword (w1hi:(128)word) (64,64)` THEN
  ABBREV_TAC `(w1md_l:(64)word) = word_subword (w1md:(128)word) (0,64)` THEN
  ABBREV_TAC `(w1md_h:(64)word) = word_subword (w1md:(128)word) (64,64)` THEN
  ABBREV_TAC `(w2lo_l:(64)word) = word_subword (w2lo:(128)word) (0,64)` THEN
  ABBREV_TAC `(w2lo_h:(64)word) = word_subword (w2lo:(128)word) (64,64)` THEN
  ABBREV_TAC `(w2hi_l:(64)word) = word_subword (w2hi:(128)word) (0,64)` THEN
  ABBREV_TAC `(w2hi_h:(64)word) = word_subword (w2hi:(128)word) (64,64)` THEN
  ABBREV_TAC `(w2md_l:(64)word) = word_subword (w2md:(128)word) (0,64)` THEN
  ABBREV_TAC `(w2md_h:(64)word) = word_subword (w2md:(128)word) (64,64)` THEN
  ABBREV_TAC `(w3lo_l:(64)word) = word_subword (w3lo:(128)word) (0,64)` THEN
  ABBREV_TAC `(w3lo_h:(64)word) = word_subword (w3lo:(128)word) (64,64)` THEN
  ABBREV_TAC `(w3hi_l:(64)word) = word_subword (w3hi:(128)word) (0,64)` THEN
  ABBREV_TAC `(w3hi_h:(64)word) = word_subword (w3hi:(128)word) (64,64)` THEN
  ABBREV_TAC `(w3md_l:(64)word) = word_subword (w3md:(128)word) (0,64)` THEN
  ABBREV_TAC `(w3md_h:(64)word) = word_subword (w3md:(128)word) (64,64)` THEN
  ABBREV_TAC `(w4lo_l:(64)word) = word_subword (w4lo:(128)word) (0,64)` THEN
  ABBREV_TAC `(w4lo_h:(64)word) = word_subword (w4lo:(128)word) (64,64)` THEN
  ABBREV_TAC `(w4hi_l:(64)word) = word_subword (w4hi:(128)word) (0,64)` THEN
  ABBREV_TAC `(w4hi_h:(64)word) = word_subword (w4hi:(128)word) (64,64)` THEN
  ABBREV_TAC `(w4md_l:(64)word) = word_subword (w4md:(128)word) (0,64)` THEN
  ABBREV_TAC `(w4md_h:(64)word) = word_subword (w4md:(128)word) (64,64)` THEN
  ABBREV_TAC `(w5lo_l:(64)word) = word_subword (w5lo:(128)word) (0,64)` THEN
  ABBREV_TAC `(w5lo_h:(64)word) = word_subword (w5lo:(128)word) (64,64)` THEN
  ABBREV_TAC `(w5hi_l:(64)word) = word_subword (w5hi:(128)word) (0,64)` THEN
  ABBREV_TAC `(w5hi_h:(64)word) = word_subword (w5hi:(128)word) (64,64)` THEN
  ABBREV_TAC `(w5md_l:(64)word) = word_subword (w5md:(128)word) (0,64)` THEN
  ABBREV_TAC `(w5md_h:(64)word) = word_subword (w5md:(128)word) (64,64)` THEN
  ABBREV_TAC `(w6lo_l:(64)word) = word_subword (w6lo:(128)word) (0,64)` THEN
  ABBREV_TAC `(w6lo_h:(64)word) = word_subword (w6lo:(128)word) (64,64)` THEN
  ABBREV_TAC `(w6hi_l:(64)word) = word_subword (w6hi:(128)word) (0,64)` THEN
  ABBREV_TAC `(w6hi_h:(64)word) = word_subword (w6hi:(128)word) (64,64)` THEN
  ABBREV_TAC `(w6md_l:(64)word) = word_subword (w6md:(128)word) (0,64)` THEN
  ABBREV_TAC `(w6md_h:(64)word) = word_subword (w6md:(128)word) (64,64)` THEN
  ABBREV_TAC `(w7lo_l:(64)word) = word_subword (w7lo:(128)word) (0,64)` THEN
  ABBREV_TAC `(w7lo_h:(64)word) = word_subword (w7lo:(128)word) (64,64)` THEN
  ABBREV_TAC `(w7hi_l:(64)word) = word_subword (w7hi:(128)word) (0,64)` THEN
  ABBREV_TAC `(w7hi_h:(64)word) = word_subword (w7hi:(128)word) (64,64)` THEN
  ABBREV_TAC `(w7md_l:(64)word) = word_subword (w7md:(128)word) (0,64)` THEN
  ABBREV_TAC `(w7md_h:(64)word) = word_subword (w7md:(128)word) (64,64)` THEN
  ASM_REWRITE_TAC[] THEN
  (* Normalize LHS mid-pmuls to abbreviated w?md. *)
  SUBGOAL_THEN `word_pmul (word_xor (c2lo:(64)word) (c2hi:(64)word)) (word_xor (hj0:(64)word) (hj1:(64)word)):(128)word = w2md`
    (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "w2md" THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  SUBGOAL_THEN `word_pmul (word_xor (c3lo:(64)word) (c3hi:(64)word)) (word_xor (hh0:(64)word) (hh1:(64)word)):(128)word = w3md`
    (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "w3md" THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  SUBGOAL_THEN `word_pmul (word_xor (c4lo:(64)word) (c4hi:(64)word)) (word_xor (hg0:(64)word) (hg1:(64)word)):(128)word = w4md`
    (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "w4md" THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  SUBGOAL_THEN `word_pmul (word_xor (c5lo:(64)word) (c5hi:(64)word)) (word_xor (hf0:(64)word) (hf1:(64)word)):(128)word = w5md`
    (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "w5md" THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  SUBGOAL_THEN `word_pmul (word_xor (c6lo:(64)word) (c6hi:(64)word)) (word_xor (he0:(64)word) (he1:(64)word)):(128)word = w6md`
    (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "w6md" THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  SUBGOAL_THEN `word_pmul (word_xor (c7lo:(64)word) (c7hi:(64)word)) (word_xor (hd0:(64)word) (hd1:(64)word)):(128)word = w7md`
    (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "w7md" THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  SUBGOAL_THEN `word_pmul (word_xor (xilo:(64)word) (word_xor (c1lo:(64)word) (word_xor (xihi:(64)word) (c1hi:(64)word)))) (word_xor (hm0:(64)word) (hm1:(64)word)):(128)word = w1md`
    (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "w1md" THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  (* qS: small Barrett pmul. *)
  ABBREV_TAC `(qS:(128)word) = word_pmul (word_xor (w7lo_l:(64)word) (word_xor w6lo_l (word_xor w5lo_l (word_xor w4lo_l (word_xor w3lo_l (word_xor w2lo_l (w1lo_l))))))) (word 13979173243358019584:(64)word)` THEN
  SUBGOAL_THEN `word_pmul (word_xor (w1lo_l:(64)word) (word_xor w2lo_l (word_xor w3lo_l (word_xor w4lo_l (word_xor w5lo_l (word_xor w6lo_l (w7lo_l))))))) (word 13979173243358019584:(64)word):(128)word = qS`
    (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "qS" THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  (* qB: big Barrett pmul; fold LHS-order copy via bubble_sort_conv. *)
  ABBREV_TAC `(qB:(128)word) = word_pmul
    (word_xor (w7md_l:(64)word) (word_xor w6md_l (word_xor w5md_l (word_xor w4md_l (word_xor w3md_l (word_xor w2md_l (word_xor w1md_l (word_xor w7lo_l (word_xor w6lo_l (word_xor w5lo_l (word_xor w4lo_l (word_xor w3lo_l (word_xor w2lo_l (word_xor w1lo_l (word_xor w7hi_l (word_xor w6hi_l (word_xor w5hi_l (word_xor w4hi_l (word_xor w3hi_l (word_xor w2hi_l (word_xor w1hi_l (word_xor (word_subword (qS:(128)word) (0,64)) (word_xor w7lo_h (word_xor w6lo_h (word_xor w5lo_h (word_xor w4lo_h (word_xor w3lo_h (word_xor w2lo_h (w1lo_h))))))))))))))))))))))))))))) (word 13979173243358019584:(64)word)` THEN
  SUBGOAL_THEN
    `word_pmul (word_xor (w1lo_h:(64)word) (word_xor w2lo_h (word_xor w3lo_h (word_xor w4lo_h (word_xor w5lo_h (word_xor w6lo_h (word_xor w7lo_h (word_xor w1md_l (word_xor w2md_l (word_xor w3md_l (word_xor w4md_l (word_xor w5md_l (word_xor w6md_l (word_xor w7md_l (word_xor w1hi_l (word_xor w2hi_l (word_xor w3hi_l (word_xor w4hi_l (word_xor w5hi_l (word_xor w6hi_l (word_xor w7hi_l (word_xor w1lo_l (word_xor w2lo_l (word_xor w3lo_l (word_xor w4lo_l (word_xor w5lo_l (word_xor w6lo_l (word_xor w7lo_l ((word_subword (qS:(128)word) (0,64))))))))))))))))))))))))))))))) (word 13979173243358019584:(64)word):(128)word = qB`
    (fun th -> REWRITE_TAC[th]) THENL
    [EXPAND_TAC "qB" THEN AP_THM_TAC THEN AP_TERM_TAC THEN
     CONV_TAC(BINOP_CONV bubble_sort_conv) THEN REFL_TAC; ALL_TAC];;

(* Step 1+2: establish the four spec-form ct folds F1..F4 and fold them into
   the RHS ghash list. *)
let GCM_7B_FOLD_SPEC_CTS : tactic =
  (* F1 *)
  SUBGOAL_THEN
   `word_xor pt1 (aes256_encrypt ivec [rk0;rk1;rk2;rk3;rk4;rk5;rk6;rk7;rk8;rk9;rk10;rk11;rk12;rk13;rk14]) = ct1`
   ASSUME_TAC THENL
   [EXPAND_TAC "ct1" THEN
    (* June base: ct1's def is left-assoc; left-associate the EXPAND output. *)
    REWRITE_TAC[AES256_ENCRYPT_UNFOLD; LET_DEF; LET_END_DEF; WORD_XOR_ASSOC] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* F2 *)
  SUBGOAL_THEN
   `word_xor pt2 (aes256_encrypt (gcm_ctr_inc ivec) [rk0;rk1;rk2;rk3;rk4;rk5;rk6;rk7;rk8;rk9;rk10;rk11;rk12;rk13;rk14]) = ct2`
   ASSUME_TAC THENL
   [CONV_TAC SYM_CONV THEN GCM_7BLOCK_CT2_STEP_TAC; ALL_TAC] THEN
  (* F3 *)
  SUBGOAL_THEN
   `word_xor pt3 (aes256_encrypt (gcm_ctr_inc (gcm_ctr_inc ivec)) [rk0;rk1;rk2;rk3;rk4;rk5;rk6;rk7;rk8;rk9;rk10;rk11;rk12;rk13;rk14]) = ct3`
   ASSUME_TAC THENL
   [CONV_TAC SYM_CONV THEN GCM_7BLOCK_CT3_STEP_TAC; ALL_TAC] THEN
  (* F4 *)
  SUBGOAL_THEN
   `word_xor pt4 (aes256_encrypt (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ivec))) [rk0;rk1;rk2;rk3;rk4;rk5;rk6;rk7;rk8;rk9;rk10;rk11;rk12;rk13;rk14]) = ct4`
   ASSUME_TAC THENL
   [CONV_TAC SYM_CONV THEN GCM_7BLOCK_CT4_STEP_TAC; ALL_TAC] THEN
  (* F5 *)
  SUBGOAL_THEN
   `word_xor pt5 (aes256_encrypt (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ivec)))) [rk0;rk1;rk2;rk3;rk4;rk5;rk6;rk7;rk8;rk9;rk10;rk11;rk12;rk13;rk14]) = ct5`
   ASSUME_TAC THENL
   [CONV_TAC SYM_CONV THEN GCM_7BLOCK_CT5_STEP_TAC; ALL_TAC] THEN
  (* F6 *)
  SUBGOAL_THEN
   `word_xor pt6 (aes256_encrypt (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ivec))))) [rk0;rk1;rk2;rk3;rk4;rk5;rk6;rk7;rk8;rk9;rk10;rk11;rk12;rk13;rk14]) = ct6`
   ASSUME_TAC THENL
   [CONV_TAC SYM_CONV THEN GCM_7BLOCK_CT6_STEP_TAC; ALL_TAC] THEN
  (* fold the six into the RHS ghash list only: pick the F-fact for each ctN
     (LHS = word_xor ptN (aes256_encrypt ...)) and GEN_REWRITE the RHS. *)
  (fun (asl,w) ->
     let getf n = snd(find (fun (_,th) ->
       is_eq(concl th) && rand(concl th)=mk_var("ct"^string_of_int n,`:(128)word`) &&
       (let l=lhand(concl th) in
        (try fst(dest_const(rator(rator l)))="word_xor" with _->false) &&
        (try fst(dest_const(repeat rator (rand l)))="aes256_encrypt" with _->false))) asl) in
     GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [getf 1; getf 2; getf 3; getf 4; getf 5; getf 6] (asl,w));;

(* Step 4: b0-general mask-register collapse, applied to ALL assumptions
   (the 5-block sim bakes the uncollapsed mask register into final_xi). *)
let GCM_7B_MASK_COLLAPSE_ASMS : tactic =
  SUBGOAL_THEN `1 <= (byte_len:num) /\ byte_len <= 16` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(fun bth -> if concl bth = `1 <= (byte_len:num) /\ byte_len <= 16` then
    RULE_ASSUM_TAC(REWRITE_RULE[GEN `b0:int128` (MP (SPEC_ALL SEVENBLOCK_MASK_REG) bth)]) else NO_TAC);;

(* Step 5: bridge the machine block-5 keystream (collapsed +4 counter, baked
   into final_xi) to the spec ct5.  Extract the machine keystream from the
   final_xi defining assumption and prove (machine ks5 = ct5), then fold it
   into every assumption (incl final_xi). *)
let GCM_7B_KS7_FOLD : tactic = fun (asl,w) ->
  let substr sub s =
    let ls=String.length s and lb=String.length sub in
    let rec go i = if i+lb>ls then false
                   else if String.sub s i lb = sub then true else go(i+1) in go 0 in
  let fxidef = snd(find (fun (_,th) ->
    is_eq(concl th) && (try rand(concl th)=`final_xi:(128)word` with _->false)) asl) in
  let body = lhs(concl fxidef) in
  (* June base: require rk14 to pick the full keystream (mirror band-5/6). *)
  let best = ref None in
  let rec walk t =
    (try let s=string_of_term t in
      if substr "pt7" s && substr "aese" s && substr "rk14" s &&
         (try fst(dest_const(repeat rator t))="word_xor" with _->false) &&
         (match !best with None->true | Some b -> String.length s < String.length(string_of_term b))
      then best := Some t
     with _->());
    (match t with Comb(a,b)->walk a; walk b | Abs(_,b)->walk b | _->()) in
  walk body;
  let ks5 = (match !best with Some t->t | None->failwith "KS7_FOLD: ks7 not found") in
  let bri = WORD_BLAST `word_bytereverse (word_bytereverse (x:(32)word)) = x` in
  let add6 = WORD_RULE `word_add (word_add (word_add (word_add (word_add (word_add (x:(32)word) (word 1)) (word 1)) (word 1)) (word 1)) (word 1)) (word 1) = word_add x (word 6)` in
  (SUBGOAL_THEN (mk_eq(ks5, `ct7:(128)word`)) ASSUME_TAC THENL
    [(* band-4/5/6 counter peel for the collapsed +6 counter. *)
     CONV_TAC SYM_CONV THEN EXPAND_TAC "ct7" THEN
     REWRITE_TAC[AES256_ENCRYPT_UNFOLD] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
     REWRITE_TAC[WORD_XOR_ASSOC] THEN
     AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
     REPEAT(AP_THM_TAC ORELSE AP_TERM_TAC) THEN
     REWRITE_TAC[gcm_ctr_inc] THEN
     REWRITE_TAC[WORD_REVERSEFIELDS_REVERSEFIELDS; WORD_REVERSEFIELDS_8_BYTEREVERSE_32] THEN
     REWRITE_TAC[INSERT_SUBWORD; INSERT_IDEM] THEN
     REWRITE_TAC[bri] THEN REWRITE_TAC[add6] THEN
     REWRITE_TAC[CTR_WORD_INSERT];
     ALL_TAC] THEN
   FIRST_ASSUM(fun th ->
     if is_eq(concl th) && rand(concl th)=`ct7:(128)word` &&
        (try fst(dest_const(repeat rator (lhs(concl th))))="word_xor" with _->false) &&
        String.length(string_of_term(lhs(concl th))) > 1000
     then RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th] else NO_TAC))
  (asl,w);;

(* The full GHASH closer: applied at the final GHASH conjunct. *)
(* June-2026 base: per-half XOR-AC closer, mirroring band-4/5/6.  7 mids
   (w1md=hm, w2md=hj, w3md=hh, w4md=hg, w5md=hf, w6md=he, w7md=hd), qS=7, qB=29. *)
let GCM_7B_FOLD_MIDS_TAC : tactic =
  fun (asl,gg) ->
    let rec finds hd t acc = match t with
      | Comb(Comb(Const("word_pmul",_),a),x) when x = hd ->
          a :: (finds hd a (finds hd x acc))
      | Comb(l,r) -> finds hd l (finds hd r acc)
      | Abs(_,b) -> finds hd b acc | _ -> acc in
    let hmw = `word_xor (hm0:(64)word) hm1`
    and hjw = `word_xor (hj0:(64)word) hj1`
    and hhw = `word_xor (hh0:(64)word) hh1`
    and hgw = `word_xor (hg0:(64)word) hg1`
    and hfw = `word_xor (hf0:(64)word) hf1`
    and hew = `word_xor (he0:(64)word) he1`
    and hdw = `word_xor (hd0:(64)word) hd1` in
    let mk tgt hd arg =
      SUBGOAL_THEN
        (mk_eq(list_mk_comb(`word_pmul:(64)word->(64)word->(128)word`,[arg;hd]),tgt))
        (fun th -> REWRITE_TAC[th]) THENL
       [EXPAND_TAC (fst(dest_var tgt)) THEN AP_THM_TAC THEN AP_TERM_TAC THEN
        CONV_TAC WORD_RULE; ALL_TAC] in
    (EVERY ((map (mk `w1md:(128)word` hmw) (setify(finds hmw gg [])))
          @ (map (mk `w2md:(128)word` hjw) (setify(finds hjw gg [])))
          @ (map (mk `w3md:(128)word` hhw) (setify(finds hhw gg [])))
          @ (map (mk `w4md:(128)word` hgw) (setify(finds hgw gg [])))
          @ (map (mk `w5md:(128)word` hfw) (setify(finds hfw gg [])))
          @ (map (mk `w6md:(128)word` hew) (setify(finds hew gg [])))
          @ (map (mk `w7md:(128)word` hdw) (setify(finds hdw gg []))))) (asl,gg);;
let GCM_7B_FOLD_TO tgt natoms : tactic =
  let w64 = `word 13979173243358019584:(64)word` in
  fun (asl,gg) ->
    let rec finds t acc = match t with
      | Comb(Comb(Const("word_pmul",_),a),x) when x = w64 ->
          a :: (finds a (finds x acc))
      | Comb(l,r) -> finds l (finds r acc) | Abs(_,b) -> finds b acc | _ -> acc in
    let rec at t = match t with
      | Comb(Comb(Const("word_xor",_),x),y) -> at x @ at y | _ -> [t] in
    let args = List.filter (fun a -> List.length(at a) = natoms) (setify(finds gg [])) in
    (EVERY (map (fun a ->
       FIRST [SUBGOAL_THEN
                (mk_eq(list_mk_comb(`word_pmul:(64)word->(64)word->(128)word`,[a;w64]),tgt))
                (fun th -> REWRITE_TAC[th]) THENL
               [EXPAND_TAC (fst(dest_var tgt)) THEN AP_THM_TAC THEN AP_TERM_TAC THEN
                CONV_TAC(BINOP_CONV bubble_fix) THEN REFL_TAC; ALL_TAC];
              ALL_TAC]) args)) (asl,gg);;
let GCM_7B_HALF_CLOSE : tactic =
  GCM_7B_FOLD_MIDS_TAC THEN ASM_REWRITE_TAC[] THEN
  GCM_7B_FOLD_TO `qS:(128)word` 7 THEN ASM_REWRITE_TAC[] THEN
  GCM_7B_FOLD_TO `qB:(128)word` 29 THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(BINOP_CONV bubble_fix) THEN REFL_TAC;;

let GCM_7B_GHASH_CLOSE : tactic =
  GCM_7B_FOLD_SPEC_CTS THEN
  REWRITE_TAC[GHASH_POLYVAL_ACC_7; POLYVAL_DOT_H7_EQ; POLYVAL_DOT_H6_EQ; POLYVAL_DOT_H5_EQ; GSYM WORD_REVERSEFIELDS_XOR_8_128] THEN
  GCM_7B_MASK_COLLAPSE_ASMS THEN
  GCM_7B_KS7_FOLD THEN
  GCM_7B_TAIL_NOFINAL THEN
  REWRITE_TAC[XI_HS_LO_7; XI_HS_HI_7] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `word_pmul (word_xor (xihi:(64)word) (word_xor c1hi (word_xor xilo c1lo)))
              (word_xor (hm0:(64)word) hm1):(128)word = w1md`
   (fun th -> REWRITE_TAC[th]) THENL
   [EXPAND_TAC "w1md" THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  BINOP_TAC THENL [GCM_7B_HALF_CLOSE; GCM_7B_HALF_CLOSE];;

(* --- The 7-block branch theorem. --- *)

(* Full assembled AES256_GCM_ENCRYPT_LT_7BLOCK_CORRECT proof (more_than_6).
   Depends on (already loaded in session):
   gcm_seven_block_closers.ml, GCM_ANDMASK0, five_abbrev_ct.ml, seven_helpers.ml,
   sevengoal.ml (WITH h7k), seven_abbrev_ct7.ml (abbrev_ct7/CT_CLOSE_7/
   GCM_7B_MASKED_CT7_CLOSE), seven_ghash_closer.ml (GCM_7B_GHASH_CLOSE etc). *)

let AES256_GCM_ENCRYPT_LT_7BLOCK_CONCRETE = prove
 (gcm_7b_goal,
  (* ---- symbolic simulation (store-based ct abbreviation) ---- *)
  GCM_INIT_TAC GCM_CBZ_LEMMA7 THEN GCM_PROLOGUE_TAC THEN GCM_RUN 20 263 THEN
  GCM_INLOOP_GUARD_TAC GCM_X7_LEMMA7 THEN GCM_RUN 267 272 THEN
  GCM_BND16 GCM_X7TAIL_LEMMA7 THEN
  GCM_RUN_THEN GCM_CASCADE7_TAC 273 321 THEN
  abbrev_ct_from_store 0 1 THEN abbrev_ct_from_store 16 2 THEN abbrev_ct_from_store 32 3 THEN
  GCM_RUN 322 348 THEN abbrev_ct_from_store 48 4 THEN
  GCM_RUN 349 362 THEN abbrev_ct_from_store 64 5 THEN
  GCM_RUN 363 376 THEN abbrev_ct_from_store 80 6 THEN
  GCM_RUN 377 417 THEN
  SUBGOAL_THEN `1 <= byte_len /\ byte_len <= 16` MP_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP SEVENBLOCK_MASK_REG th])) THEN
  GCM_NBLOCK_POST_SIM_NORMALIZE_TAC THEN ABBREV_FINAL_XI_TAC THEN
  ARM_STEPS_TAC AES256_GCM_EXEC (418--425) THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ENSURES_FINAL_STATE_TAC THEN
  SUBGOAL_THEN `1 <= byte_len /\ byte_len <= 16` MP_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP SEVENBLOCK_MASK_REG th]) THEN
  ASM_SIMP_TAC[SEVENBLOCK_USHR] THEN
  (* ---- eight conjuncts: ct1..ct6, masked-ct7, GHASH ---- *)
  CONJ_TAC THENL [CT_CLOSE_7 1; ALL_TAC] THEN
  CONJ_TAC THENL [CONV_TAC SYM_CONV THEN GCM_7BLOCK_CT2_STEP_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [CONV_TAC SYM_CONV THEN GCM_7BLOCK_CT3_STEP_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [CONV_TAC SYM_CONV THEN GCM_7BLOCK_CT4_STEP_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [CONV_TAC SYM_CONV THEN GCM_7BLOCK_CT5_STEP_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [CONV_TAC SYM_CONV THEN GCM_7BLOCK_CT6_STEP_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [GCM_7B_MASKED_CT7_CLOSE; ALL_TAC] THEN
  (* ---- ct7 abbreviation (spec form) so the closer's ctm7 works ---- *)
  ABBREV_TAC `ct7 = word_xor pt7
    (aes256_encrypt (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ivec)))))) [rk0;rk1;rk2;rk3;rk4;rk5;rk6;rk7;rk8;rk9;rk10;rk11;rk12;rk13;rk14]):(128)word` THEN
  (* ---- GHASH conjunct ---- *)
  GCM_7B_GHASH_CLOSE);;

(* ========================================================================= *)
(* The L256_enc_blocks_more_than_7 branch (8-block: seven full blocks +      *)
(* partial block 8, total 113..128 bytes) of the single binary, proved as a  *)
(* standalone theorem and applied exactly as the XTS length-band lemmas are. *)
(* Reuses the eight-block masked closers from gcm_eight_block_closers.ml.    *)
(* more_than_7 is the highest dispatch branch; it reads scratch Q18 via an   *)
(* INS (mov v18.d[0]) before fully writing it, so the precondition pins      *)
(* read Q18 = q18i (its high lane is dead).                                  *)
(* ========================================================================= *)

needs "arm/proofs/utils/gcm_eight_block_closers.ml";;

(* --- 8-block-branch length/cascade helpers (thresholds over 112+byte_len) --- *)

let GCM_CBZ_LEMMA8 = prove
 (`1 <= byte_len /\ byte_len <= 16 ==> ~(val(word(896+8*byte_len):int64) = 0)`,
  STRIP_TAC THEN SUBGOAL_THEN `val(word(896+8*byte_len):int64) = 896+8*byte_len` SUBST1_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC;
    ASM_ARITH_TAC]);;

let GCM_WSUB8 = prove
 (`byte_len <= 16 ==> word_sub (word (112+byte_len):int64) (word 1) = word (111 + byte_len)`,
  CONV_TAC WORD_RULE);;

let GCM_X8_LEMMA8 = prove
 (`1 <= byte_len /\ byte_len <= 16 ==>
   word_add (word_and (word_sub (word_ushr (word (896+8*byte_len):int64) 3) (word 1))
                      (word 18446744073709551488)) in_ptr = in_ptr`,
  STRIP_TAC THEN
  SUBGOAL_THEN `word_ushr (word (896+8*byte_len):int64) 3 = word (112+byte_len)` SUBST1_TAC THENL
   [ASM_SIMP_TAC[EIGHTBLOCK_USHR]; ALL_TAC] THEN
  ASM_SIMP_TAC[GCM_WSUB8] THEN
  SUBGOAL_THEN `word_and (word (111+byte_len):int64) (word 18446744073709551488) = word 0` SUBST1_TAC THENL
   [MATCH_MP_TAC GCM_ANDMASK0 THEN ASM_ARITH_TAC; ALL_TAC] THEN
  CONV_TAC WORD_RULE);;

let GCM_X8TAIL_LEMMA8 = prove
 (`byte_len <= 16 ==>
   word_sub (word_add in_ptr (word_ushr (word (896+8*byte_len):int64) 3)) in_ptr = word (112+byte_len)`,
  ASM_SIMP_TAC[EIGHTBLOCK_USHR] THEN CONV_TAC WORD_RULE);;

(* Cascade for more_than_7: total lanes = 112+byte_len (113..128).  The b.gt #112
   is taken directly (total >= 113) into .more_than_7.  No FALSE thresholds;
   TRUE threshold = 112.  (more_than_7 is the highest/last dispatch branch.) *)
let GCM_CASC8_TRUE = prove
 (`1 <= byte_len /\ byte_len <= 16 ==>
    ((~(val (word_sub (word (112+byte_len):int64) (word 112)) = 0) /\
      (ival (word_sub (word (112+byte_len):int64) (word 112)) < &0 <=>
       ~(ival (word (112+byte_len):int64) - &112 = ival (word_sub (word (112+byte_len):int64) (word 112)))))
     <=> T)`,
  STRIP_TAC THEN
  SUBGOAL_THEN `ival(word (112+byte_len):int64) = &(112+byte_len)` ASSUME_TAC THENL
   [MATCH_MP_TAC NBLOCK_IVAL_WORD_SMALL THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `word_sub (word (112+byte_len):int64) (word 112) = iword(&(112+byte_len) - &112)` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM IWORD_INT_SUB; WORD_IWORD]; ALL_TAC] THEN
  SUBGOAL_THEN `ival(iword(&(112+byte_len) - &112):int64) = &(112+byte_len) - &112` ASSUME_TAC THENL
   [MATCH_MP_TAC IVAL_IWORD THEN REWRITE_TAC[DIMINDEX_64] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_SUB_CONV) THEN
    SUBGOAL_THEN `&(112+byte_len):int <= &128` MP_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN INT_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[VAL_EQ_0; GSYM IVAL_EQ_0] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_ADD] THEN
  SUBGOAL_THEN `&1:int <= &byte_len` MP_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN INT_ARITH_TAC);;

let GCM_CASCADE8_TAC : tactic =
  FIRST_X_ASSUM(fun bl16 -> if concl bl16 = `byte_len <= 16` then
    FIRST_X_ASSUM(fun bl1 -> if concl bl1 = `1 <= byte_len` then
      RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP GCM_CASC8_TRUE (CONJ bl1 bl16); COND_CLAUSES]) THEN
      ASSUME_TAC bl1 THEN ASSUME_TAC bl16
    else NO_TAC)
  else NO_TAC);;

(* --- The 8-block branch goal (seven full + one partial block). --- *)

let gcm_8b_goal = `!in_ptr out_ptr xi_ptr ivec_ptr key_ptr htable_ptr
    (pt1:(128)word) (pt2:(128)word) (pt3:(128)word) (pt4:(128)word) (pt5:(128)word) (pt6:(128)word) (pt7:(128)word) (pt8:(128)word)
    (out0:(128)word)
    (ivec:(128)word)
    (rk0:(128)word) (rk1:(128)word) (rk2:(128)word) (rk3:(128)word)
    (rk4:(128)word) (rk5:(128)word) (rk6:(128)word) (rk7:(128)word)
    (rk8:(128)word) (rk9:(128)word) (rk10:(128)word) (rk11:(128)word)
    (rk12:(128)word) (rk13:(128)word) (rk14:(128)word)
    (xi:(128)word) (h:(128)word) (h1k:(128)word) (h3k:(128)word) (h5k:(128)word) (h7k:(128)word)
    (q18i:(128)word)
    byte_len stackptr pc.
    1 <= byte_len /\ byte_len <= 16 /\
    aligned 16 stackptr /\
    nonoverlapping (word pc,4600) (in_ptr:int64,128) /\
    nonoverlapping (word pc,4600) (out_ptr:int64,128) /\
    nonoverlapping (word pc,4600) (xi_ptr:int64,16) /\
    nonoverlapping (word pc,4600) (ivec_ptr:int64,16) /\
    nonoverlapping (word pc,4600) (key_ptr:int64,240) /\
    nonoverlapping (word pc,4600) (htable_ptr:int64,256) /\
    nonoverlapping (word pc,4600) (stackptr:int64,80) /\
    nonoverlapping (in_ptr,128) (out_ptr,128) /\
    nonoverlapping (in_ptr,128) (xi_ptr,16) /\
    nonoverlapping (in_ptr,128) (ivec_ptr,16) /\
    nonoverlapping (out_ptr,128) (xi_ptr,16) /\
    nonoverlapping (out_ptr,128) (ivec_ptr,16) /\
    nonoverlapping (xi_ptr,16) (ivec_ptr,16) /\
    nonoverlapping (key_ptr,240) (out_ptr,128) /\
    nonoverlapping (key_ptr,240) (xi_ptr,16) /\
    nonoverlapping (key_ptr,240) (ivec_ptr,16) /\
    nonoverlapping (htable_ptr,256) (out_ptr,128) /\
    nonoverlapping (htable_ptr,256) (xi_ptr,16) /\
    nonoverlapping (htable_ptr,256) (ivec_ptr,16) /\
    nonoverlapping (stackptr,80) (out_ptr,128) /\
    nonoverlapping (stackptr,80) (xi_ptr,16) /\
    nonoverlapping (stackptr,80) (ivec_ptr,16) /\
    nonoverlapping (stackptr,80) (in_ptr,128) /\
    nonoverlapping (stackptr,80) (key_ptr,240) /\
    nonoverlapping (stackptr,80) (htable_ptr,256) /\
    nonoverlapping (ivec_ptr,16) (word pc,4600) /\
    nonoverlapping (xi_ptr,16) (word pc,4600) /\
    nonoverlapping (out_ptr,128) (word pc,4600)
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) aes256_gcm_mc /\
           read PC s = word pc /\
           C_ARGUMENTS [in_ptr; word (896 + 8 * byte_len); out_ptr; xi_ptr;
                        ivec_ptr; key_ptr; htable_ptr] s /\
           read SP s = word_add stackptr (word 80) /\
           read Q18 s = q18i /\
           read (memory :> bytes128 in_ptr) s = pt1 /\
           read (memory :> bytes128 (word_add in_ptr (word 16))) s = pt2 /\
           read (memory :> bytes128 (word_add in_ptr (word 32))) s = pt3 /\
           read (memory :> bytes128 (word_add in_ptr (word 48))) s = pt4 /\
           read (memory :> bytes128 (word_add in_ptr (word 64))) s = pt5 /\
           read (memory :> bytes128 (word_add in_ptr (word 80))) s = pt6 /\
           read (memory :> bytes128 (word_add in_ptr (word 96))) s = pt7 /\
           read (memory :> bytes128 (word_add in_ptr (word 112))) s = pt8 /\
           read (memory :> bytes128 (word_add out_ptr (word 112))) s = out0 /\
           read (memory :> bytes128 ivec_ptr) s = ivec /\
           read (memory :> bytes128 (word_add key_ptr (word 0))) s = rk0 /\
           read (memory :> bytes128 (word_add key_ptr (word 16))) s = rk1 /\
           read (memory :> bytes128 (word_add key_ptr (word 32))) s = rk2 /\
           read (memory :> bytes128 (word_add key_ptr (word 48))) s = rk3 /\
           read (memory :> bytes128 (word_add key_ptr (word 64))) s = rk4 /\
           read (memory :> bytes128 (word_add key_ptr (word 80))) s = rk5 /\
           read (memory :> bytes128 (word_add key_ptr (word 96))) s = rk6 /\
           read (memory :> bytes128 (word_add key_ptr (word 112))) s = rk7 /\
           read (memory :> bytes128 (word_add key_ptr (word 128))) s = rk8 /\
           read (memory :> bytes128 (word_add key_ptr (word 144))) s = rk9 /\
           read (memory :> bytes128 (word_add key_ptr (word 160))) s = rk10 /\
           read (memory :> bytes128 (word_add key_ptr (word 176))) s = rk11 /\
           read (memory :> bytes128 (word_add key_ptr (word 192))) s = rk12 /\
           read (memory :> bytes128 (word_add key_ptr (word 208))) s = rk13 /\
           read (memory :> bytes128 (word_add key_ptr (word 224))) s = rk14 /\
           read (memory :> bytes128 xi_ptr) s = xi /\
           read (memory :> bytes128 htable_ptr) s = word_swaphalves128 h /\
           read (memory :> bytes128 (word_add htable_ptr (word 16))) s = h1k /\
           read (memory :> bytes128 (word_add htable_ptr (word 32))) s =
             word_swaphalves128 (polyval_dot h h) /\
           read (memory :> bytes128 (word_add htable_ptr (word 48))) s =
             word_swaphalves128 (polyval_dot h (polyval_dot h h)) /\
           read (memory :> bytes128 (word_add htable_ptr (word 64))) s = h3k /\
           read (memory :> bytes128 (word_add htable_ptr (word 80))) s =
             word_swaphalves128 (polyval_dot (polyval_dot h h) (polyval_dot h h)) /\
           read (memory :> bytes128 (word_add htable_ptr (word 96))) s =
             word_swaphalves128 (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) /\
           read (memory :> bytes128 (word_add htable_ptr (word 112))) s = h5k /\
           read (memory :> bytes128 (word_add htable_ptr (word 128))) s =
             word_swaphalves128 (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) h) /\
           read (memory :> bytes128 (word_add htable_ptr (word 144))) s =
             word_swaphalves128 (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) h) h) /\
           read (memory :> bytes128 (word_add htable_ptr (word 160))) s = h7k /\
           read (memory :> bytes128 (word_add htable_ptr (word 176))) s =
             word_swaphalves128 (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) h) h) h) /\
           word_subword h1k (0,64):(64)word = karatsuba_mid h /\
           word_subword h1k (64,64):(64)word =
             karatsuba_mid (polyval_dot h h) /\
           word_subword h3k (0,64):(64)word =
             karatsuba_mid (polyval_dot h (polyval_dot h h)) /\
           word_subword h3k (64,64):(64)word =
             karatsuba_mid (polyval_dot (polyval_dot h h) (polyval_dot h h)) /\
           word_subword h5k (0,64):(64)word =
             karatsuba_mid (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) /\
           word_subword h5k (64,64):(64)word =
             karatsuba_mid (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) h) /\
           word_subword h7k (0,64):(64)word =
             karatsuba_mid (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) h) h) /\
           word_subword h7k (64,64):(64)word =
             karatsuba_mid (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) h) h) h))
      (\s.
           let ct1 =
             word_xor pt1
               (aes256_encrypt ivec [rk0;rk1;rk2;rk3;rk4;rk5;rk6;rk7;rk8;rk9;rk10;rk11;rk12;rk13;rk14]) in
           let ct2 =
             word_xor pt2
               (aes256_encrypt (gcm_ctr_inc ivec) [rk0;rk1;rk2;rk3;rk4;rk5;rk6;rk7;rk8;rk9;rk10;rk11;rk12;rk13;rk14]) in
           let ct3 =
             word_xor pt3
               (aes256_encrypt (gcm_ctr_inc (gcm_ctr_inc ivec)) [rk0;rk1;rk2;rk3;rk4;rk5;rk6;rk7;rk8;rk9;rk10;rk11;rk12;rk13;rk14]) in
           let ct4 =
             word_xor pt4
               (aes256_encrypt (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ivec))) [rk0;rk1;rk2;rk3;rk4;rk5;rk6;rk7;rk8;rk9;rk10;rk11;rk12;rk13;rk14]) in
           let ct5 =
             word_xor pt5
               (aes256_encrypt (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ivec)))) [rk0;rk1;rk2;rk3;rk4;rk5;rk6;rk7;rk8;rk9;rk10;rk11;rk12;rk13;rk14]) in
           let ct6 =
             word_xor pt6
               (aes256_encrypt (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ivec))))) [rk0;rk1;rk2;rk3;rk4;rk5;rk6;rk7;rk8;rk9;rk10;rk11;rk12;rk13;rk14]) in
           let ct7 =
             word_xor pt7
               (aes256_encrypt (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ivec)))))) [rk0;rk1;rk2;rk3;rk4;rk5;rk6;rk7;rk8;rk9;rk10;rk11;rk12;rk13;rk14]) in
           let ct8 =
             word_xor pt8
               (aes256_encrypt (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ivec))))))) [rk0;rk1;rk2;rk3;rk4;rk5;rk6;rk7;rk8;rk9;rk10;rk11;rk12;rk13;rk14]) in
           let mask = word (2 EXP (8 * byte_len) - 1):(128)word in
           let ctm8 = word_and ct8 mask in
           read PC s = word(pc + 4588) /\
           read X0 s = word (112 + byte_len) /\
           read (memory :> bytes128 out_ptr) s = ct1 /\
           read (memory :> bytes128 (word_add out_ptr (word 16))) s = ct2 /\
           read (memory :> bytes128 (word_add out_ptr (word 32))) s = ct3 /\
           read (memory :> bytes128 (word_add out_ptr (word 48))) s = ct4 /\
           read (memory :> bytes128 (word_add out_ptr (word 64))) s = ct5 /\
           read (memory :> bytes128 (word_add out_ptr (word 80))) s = ct6 /\
           read (memory :> bytes128 (word_add out_ptr (word 96))) s = ct7 /\
           read (memory :> bytes128 (word_add out_ptr (word 112))) s =
             word_or ctm8 (word_and out0 (word_not mask)) /\
           read (memory :> bytes128 xi_ptr) s =
             word_reversefields 8
               (ghash_polyval_acc h (word_reversefields 8 xi)
                                    [word_reversefields 8 ct1;
                                     word_reversefields 8 ct2;
                                     word_reversefields 8 ct3;
                                     word_reversefields 8 ct4;
                                     word_reversefields 8 ct5;
                                     word_reversefields 8 ct6;
                                     word_reversefields 8 ct7;
                                     word_reversefields 8 ctm8]))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [memory :> bytes(out_ptr,128);
                  memory :> bytes(xi_ptr,16);
                  memory :> bytes(ivec_ptr,16)] ,,
       MAYCHANGE [SP] ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes64 stackptr;
                  memory :> bytes64 (word_add stackptr (word 8));
                  memory :> bytes64 (word_add stackptr (word 16));
                  memory :> bytes64 (word_add stackptr (word 24));
                  memory :> bytes64 (word_add stackptr (word 32));
                  memory :> bytes64 (word_add stackptr (word 40));
                  memory :> bytes64 (word_add stackptr (word 48));
                  memory :> bytes64 (word_add stackptr (word 56));
                  memory :> bytes64 (word_add stackptr (word 64));
                  memory :> bytes64 (word_add stackptr (word 72))])`;;

(* --- 8-block store-based ct abbreviation + conjunct closers. --- *)

(* 8-block ct abbreviation uses the shared strict `abbrev_ct_from_store`
   (defined once near the 2-block band); the earlier per-band `abbrev_ct8`
   duplicate is now folded into that shared helper. *)

(* ct1 closer (counter = ivec). *)
let CT_CLOSE_8 nidx =
  let s13n = "s13_"^string_of_int nidx and ctn = "ct"^string_of_int nidx in
  EXPAND_TAC ctn THEN EXPAND_TAC s13n THEN
  REWRITE_TAC[AES256_ENCRYPT_UNFOLD; LET_DEF; LET_END_DEF; WORD_XOR_ASSOC] THEN ASM_REWRITE_TAC[];;

(* masked-ct8 store conjunct closer: block-8 = gcm_ctr_inc^7 -> "+7". *)
let GCM_8B_MASKED_CT8_CLOSE : tactic =
  let bri = WORD_BLAST `word_bytereverse (word_bytereverse (x:(32)word)) = x` in
  let add7 = WORD_RULE `word_add (word_add (word_add (word_add (word_add (word_add (word_add (x:(32)word) (word 1)) (word 1)) (word 1)) (word 1)) (word 1)) (word 1)) (word 1) = word_add x (word 7)` in
  REWRITE_TAC[NBLOCK_MASK_IDEM] THEN
  MATCH_MP_TAC(MESON[] `x = y ==> word_or (word_and x m) r = word_or (word_and y m) r:(128)word`) THEN
  CONV_TAC SYM_CONV THEN REWRITE_TAC[AES256_ENCRYPT_UNFOLD] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[WORD_XOR_ASSOC] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REPEAT(AP_THM_TAC ORELSE AP_TERM_TAC) THEN
  REWRITE_TAC[gcm_ctr_inc] THEN
  REWRITE_TAC[WORD_REVERSEFIELDS_REVERSEFIELDS; WORD_REVERSEFIELDS_8_BYTEREVERSE_32] THEN
  REWRITE_TAC[INSERT_SUBWORD; INSERT_IDEM] THEN
  REWRITE_TAC[bri] THEN REWRITE_TAC[add7] THEN
  REWRITE_TAC[CTR_WORD_INSERT];;

(* GHASH ct-fold (mirror GCM_7B_FOLD_SPEC_CTS, 7 full-block cts). *)
let GCM_8B_FOLD_SPEC_CTS : tactic =
  SUBGOAL_THEN
   `word_xor pt1 (aes256_encrypt ivec [rk0;rk1;rk2;rk3;rk4;rk5;rk6;rk7;rk8;rk9;rk10;rk11;rk12;rk13;rk14]) = ct1`
   ASSUME_TAC THENL
   [EXPAND_TAC "ct1" THEN
    (* June base: ct1's def is left-assoc; left-associate the EXPAND output. *)
    REWRITE_TAC[AES256_ENCRYPT_UNFOLD; LET_DEF; LET_END_DEF; WORD_XOR_ASSOC] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `word_xor pt2 (aes256_encrypt (gcm_ctr_inc ivec) [rk0;rk1;rk2;rk3;rk4;rk5;rk6;rk7;rk8;rk9;rk10;rk11;rk12;rk13;rk14]) = ct2`
   ASSUME_TAC THENL [CONV_TAC SYM_CONV THEN GCM_8BLOCK_CT2_STEP_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `word_xor pt3 (aes256_encrypt (gcm_ctr_inc (gcm_ctr_inc ivec)) [rk0;rk1;rk2;rk3;rk4;rk5;rk6;rk7;rk8;rk9;rk10;rk11;rk12;rk13;rk14]) = ct3`
   ASSUME_TAC THENL [CONV_TAC SYM_CONV THEN GCM_8BLOCK_CT3_STEP_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `word_xor pt4 (aes256_encrypt (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ivec))) [rk0;rk1;rk2;rk3;rk4;rk5;rk6;rk7;rk8;rk9;rk10;rk11;rk12;rk13;rk14]) = ct4`
   ASSUME_TAC THENL [CONV_TAC SYM_CONV THEN GCM_8BLOCK_CT4_STEP_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `word_xor pt5 (aes256_encrypt (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ivec)))) [rk0;rk1;rk2;rk3;rk4;rk5;rk6;rk7;rk8;rk9;rk10;rk11;rk12;rk13;rk14]) = ct5`
   ASSUME_TAC THENL [CONV_TAC SYM_CONV THEN GCM_8BLOCK_CT5_STEP_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `word_xor pt6 (aes256_encrypt (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ivec))))) [rk0;rk1;rk2;rk3;rk4;rk5;rk6;rk7;rk8;rk9;rk10;rk11;rk12;rk13;rk14]) = ct6`
   ASSUME_TAC THENL [CONV_TAC SYM_CONV THEN GCM_8BLOCK_CT6_STEP_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `word_xor pt7 (aes256_encrypt (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ivec)))))) [rk0;rk1;rk2;rk3;rk4;rk5;rk6;rk7;rk8;rk9;rk10;rk11;rk12;rk13;rk14]) = ct7`
   ASSUME_TAC THENL [CONV_TAC SYM_CONV THEN GCM_8BLOCK_CT7_STEP_TAC; ALL_TAC] THEN
  (fun (asl,w) ->
     let getf n = snd(find (fun (_,th) ->
       is_eq(concl th) && rand(concl th)=mk_var("ct"^string_of_int n,`:(128)word`) &&
       (let l=lhand(concl th) in
        (try fst(dest_const(rator(rator l)))="word_xor" with _->false) &&
        (try fst(dest_const(repeat rator (rand l)))="aes256_encrypt" with _->false))) asl) in
     GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [getf 1; getf 2; getf 3; getf 4; getf 5; getf 6; getf 7] (asl,w));;

(* --- 8-block GHASH final-closure helper tactics (mirror 7-block). --- *)

(* ========================================================================= *)
(* Self-contained 8-block GHASH conjunct closer for the single-binary        *)
(* aes256_gcm.ml more_than_7 (8-block) branch.  Reaches "No subgoals" from   *)
(* the final GHASH equality (machine word_join = spec word_reversefields).   *)
(* Mirrors the 7-block recipe (GCM_7B_GHASH_CLOSE); adds the ks8 +7-counter  *)
(* bridge and the in-asm b0-general mask-register collapse that the 8-block  *)
(* sim leaves baked into final_xi.                                           *)
(* ========================================================================= *)

let XI_HS_LO_8 = prove
 (`word_subword (word_reversefields 8 (word_join (word_subword (xi:(128)word) (64,64):(64)word) (word_subword xi (0,64):(64)word):(128)word)) (0,64):(64)word =
   word_subword (word_reversefields 8 xi) (0,64)`,
  REWRITE_TAC[GSYM REV8_JOIN_FOLD; REVERSEFIELDS8_SUBWORD_LO; REVERSEFIELDS8_SUBWORD_HI] THEN
  CONV_TAC WORD_BLAST);;

let XI_HS_HI_8 = prove
 (`word_subword (word_reversefields 8 (word_join (word_subword (xi:(128)word) (64,64):(64)word) (word_subword xi (0,64):(64)word):(128)word)) (64,64):(64)word =
   word_subword (word_reversefields 8 xi) (64,64)`,
  REWRITE_TAC[GSYM REV8_JOIN_FOLD; REVERSEFIELDS8_SUBWORD_LO; REVERSEFIELDS8_SUBWORD_HI] THEN
  CONV_TAC WORD_BLAST);;

let GCM_8B_TAIL_NOFINAL : tactic =
  ABBREV_TAC `mask = word (2 EXP (8 * byte_len) - 1):(128)word` THEN
  ABBREV_TAC `ctm8 = word_and (ct8:(128)word) mask` THEN
  SUBGOAL_THEN `word_and (mask:(128)word) (ct8:(128)word) = ctm8`
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th]) THENL [
    EXPAND_TAC "ctm8" THEN CONV_TAC WORD_BITWISE_RULE; ALL_TAC ] THEN
  SUBGOAL_THEN
    `polyval_dot (polyval_dot (polyval_dot (h:int128) h) h) h =
     polyval_dot (polyval_dot h h) (polyval_dot h h)`
    (fun th -> REWRITE_TAC[th]) THENL
    [REWRITE_TAC[POLYVAL_DOT_H4_EQ_LOCAL]; ALL_TAC] THEN
  SUBGOAL_THEN
    `polyval_dot (polyval_dot (h:int128) h) h = polyval_dot h (polyval_dot h h)`
    (fun th -> REWRITE_TAC[th]) THENL
    [REWRITE_TAC[polyval_dot] THEN REWRITE_TAC[WORD_PMUL_SYM]; ALL_TAC] THEN
  MP_TAC(SPECL
    [`word_reversefields 8 (word_xor xi ct1):int128`;
     `word_reversefields 8 ct2:int128`;
     `word_reversefields 8 ct3:int128`;
     `word_reversefields 8 ct4:int128`;
     `word_reversefields 8 ct5:int128`;
     `word_reversefields 8 ct6:int128`;
     `word_reversefields 8 ct7:int128`;
     `word_reversefields 8 ctm8:int128`;
     `h:int128`;
     `h1k:int128`;
     `word_join (word 0:(64)word) (word_subword (h1k:(128)word) (64,64):(64)word):(128)word`;
     `h3k:int128`;
     `word_join (word 0:(64)word) (word_subword (h3k:(128)word) (64,64):(64)word):(128)word`;
     `h5k:int128`;
     `word_join (word 0:(64)word) (word_subword (h5k:(128)word) (64,64):(64)word):(128)word`;
     `h7k:int128`;
     `word_join (word 0:(64)word) (word_subword (h7k:(128)word) (64,64):(64)word):(128)word`]
    GHASH_8BLOCK_KARATSUBA_EQ_POLYVAL_ACC) THEN
  SUBGOAL_THEN
    `word_subword (word_join (word 0:(64)word) (word_subword (h1k:(128)word) (64,64):(64)word):(128)word) (0,64):(64)word =
     karatsuba_mid (polyval_dot h h)`
    (fun th -> REWRITE_TAC[th]) THENL [
    SUBGOAL_THEN
      `word_subword (word_join (word 0:(64)word) (word_subword (h1k:(128)word) (64,64):(64)word):(128)word) (0,64):(64)word =
       word_subword (h1k:(128)word) (64,64):(64)word`
      (fun th -> REWRITE_TAC[th]) THENL [CONV_TAC WORD_BLAST; ASM_REWRITE_TAC[]]; ALL_TAC ] THEN
  SUBGOAL_THEN
    `word_subword (word_join (word 0:(64)word) (word_subword (h3k:(128)word) (64,64):(64)word):(128)word) (0,64):(64)word =
     karatsuba_mid (polyval_dot (polyval_dot h h) (polyval_dot h h))`
    (fun th -> REWRITE_TAC[th]) THENL [
    SUBGOAL_THEN
      `word_subword (word_join (word 0:(64)word) (word_subword (h3k:(128)word) (64,64):(64)word):(128)word) (0,64):(64)word =
       word_subword (h3k:(128)word) (64,64):(64)word`
      (fun th -> REWRITE_TAC[th]) THENL [CONV_TAC WORD_BLAST; ASM_REWRITE_TAC[]]; ALL_TAC ] THEN
  SUBGOAL_THEN
    `word_subword (word_join (word 0:(64)word) (word_subword (h5k:(128)word) (64,64):(64)word):(128)word) (0,64):(64)word =
     karatsuba_mid (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) h)`
    (fun th -> REWRITE_TAC[th]) THENL [
    SUBGOAL_THEN
      `word_subword (word_join (word 0:(64)word) (word_subword (h5k:(128)word) (64,64):(64)word):(128)word) (0,64):(64)word =
       word_subword (h5k:(128)word) (64,64):(64)word`
      (fun th -> REWRITE_TAC[th]) THENL [CONV_TAC WORD_BLAST; ASM_REWRITE_TAC[]]; ALL_TAC ] THEN
  SUBGOAL_THEN
    `word_subword (word_join (word 0:(64)word) (word_subword (h7k:(128)word) (64,64):(64)word):(128)word) (0,64):(64)word =
     karatsuba_mid (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) h) h) h)`
    (fun th -> REWRITE_TAC[th]) THENL [
    SUBGOAL_THEN
      `word_subword (word_join (word 0:(64)word) (word_subword (h7k:(128)word) (64,64):(64)word):(128)word) (0,64):(64)word =
       word_subword (h7k:(128)word) (64,64):(64)word`
      (fun th -> REWRITE_TAC[th]) THENL [CONV_TAC WORD_BLAST; ASM_REWRITE_TAC[]]; ALL_TAC ] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN
  REWRITE_TAC[ghash_8block_karatsuba; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[SWAPHALVES128_SUBWORD_LO; SWAPHALVES128_SUBWORD_HI] THEN
  SUBGOAL_THEN
    `word_subword (word_join (word 0:(64)word) (karatsuba_mid (polyval_dot h h):(64)word):(128)word) (0,64):(64)word =
     karatsuba_mid (polyval_dot h h)`
    (fun th -> REWRITE_TAC[th]) THENL [CONV_TAC WORD_BLAST; ALL_TAC] THEN
  SUBGOAL_THEN
    `word_subword (word_join (word 0:(64)word) (karatsuba_mid (polyval_dot (polyval_dot h h) (polyval_dot h h)):(64)word):(128)word) (0,64):(64)word =
     karatsuba_mid (polyval_dot (polyval_dot h h) (polyval_dot h h))`
    (fun th -> REWRITE_TAC[th]) THENL [CONV_TAC WORD_BLAST; ALL_TAC] THEN
  SUBGOAL_THEN
    `word_subword (word_join (word 0:(64)word) (karatsuba_mid (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) h):(64)word):(128)word) (0,64):(64)word =
     karatsuba_mid (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) h)`
    (fun th -> REWRITE_TAC[th]) THENL [CONV_TAC WORD_BLAST; ALL_TAC] THEN
  SUBGOAL_THEN
    `word_subword (word_join (word 0:(64)word) (karatsuba_mid (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) h) h) h):(64)word):(128)word) (0,64):(64)word =
     karatsuba_mid (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) h) h) h)`
    (fun th -> REWRITE_TAC[th]) THENL [CONV_TAC WORD_BLAST; ALL_TAC] THEN
  REWRITE_TAC[GSYM karatsuba_mid] THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(LAND_CONV(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
  CONV_TAC SYM_CONV THEN
  FIRST_ASSUM(fun th ->
    if is_eq(concl th) && rand(concl th) = `final_xi:(128)word` &&
       (try (let l = lhs(concl th) in is_comb l &&
             (let r = rator l in not(is_comb r && (try fst(dest_const(rator r)) = "read" with _ -> false))))
        with _ -> false)
    then SUBST1_TAC(SYM th) else NO_TAC) THEN
  REWRITE_TAC[REV64_LOWER_LANE; REV64_UPPER_LANE; REV8_JOIN_FOLD] THEN
  MATCH_MP_TAC(MESON[]
    `x = y ==> word_reversefields 8 x = word_reversefields 8 y:(128)word`) THEN
  REWRITE_TAC[WORD_SWAP_HALVES_INVOLUTION] THEN
  CONV_TAC(LAND_CONV(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
  REWRITE_TAC[WORD_INSERT_AS_JOIN_LO; WORD_INSERT_AS_JOIN_HI;
              KAR_SUBWORD_LEMMA; WORD_SWAP_HALVES_INVOLUTION;
              WORD_OR_REFL; WORD_XOR_ASSOC; WORD_SUBWORD_XOR;
              SWAPHALVES128_SUBWORD_LO; SWAPHALVES128_SUBWORD_HI] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[HALFSWAP_XOR; GSYM WORD_REVERSEFIELDS_XOR_8_128;
              WORD_XOR_0; WORD_XOR_ASSOC;
              REV8_JOIN_FOLD; REVERSEFIELDS8_SUBWORD_LO; REVERSEFIELDS8_SUBWORD_HI] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  CONV_TAC(TOP_DEPTH_CONV PMUL_NORM_CONV) THEN
  SUBGOAL_THEN
    `word_subword (word 0:(128)word) (0,64):(64)word = word 0 /\
     word_subword (word 0:(128)word) (64,64):(64)word = word 0`
    (fun th -> REWRITE_TAC[th]) THENL [CONJ_TAC THEN CONV_TAC WORD_BLAST; ALL_TAC] THEN
  REWRITE_TAC[WORD_XOR_0; WORD_XOR_0_LEFT] THEN
  REWRITE_TAC[karatsuba_mid; WORD_REVERSEFIELDS_XOR_8_128; WORD_SUBWORD_XOR] THEN
  (* c-atom ABBREVs *)
  ABBREV_TAC `(c1lo:(64)word) = word_subword (word_reversefields 8 (ct1:(128)word)) (0,64)` THEN
  ABBREV_TAC `(c1hi:(64)word) = word_subword (word_reversefields 8 (ct1:(128)word)) (64,64)` THEN
  ABBREV_TAC `(c2lo:(64)word) = word_subword (word_reversefields 8 (ct2:(128)word)) (0,64)` THEN
  ABBREV_TAC `(c2hi:(64)word) = word_subword (word_reversefields 8 (ct2:(128)word)) (64,64)` THEN
  ABBREV_TAC `(c3lo:(64)word) = word_subword (word_reversefields 8 (ct3:(128)word)) (0,64)` THEN
  ABBREV_TAC `(c3hi:(64)word) = word_subword (word_reversefields 8 (ct3:(128)word)) (64,64)` THEN
  ABBREV_TAC `(c4lo:(64)word) = word_subword (word_reversefields 8 (ct4:(128)word)) (0,64)` THEN
  ABBREV_TAC `(c4hi:(64)word) = word_subword (word_reversefields 8 (ct4:(128)word)) (64,64)` THEN
  ABBREV_TAC `(c5lo:(64)word) = word_subword (word_reversefields 8 (ct5:(128)word)) (0,64)` THEN
  ABBREV_TAC `(c5hi:(64)word) = word_subword (word_reversefields 8 (ct5:(128)word)) (64,64)` THEN
  ABBREV_TAC `(c6lo:(64)word) = word_subword (word_reversefields 8 (ct6:(128)word)) (0,64)` THEN
  ABBREV_TAC `(c6hi:(64)word) = word_subword (word_reversefields 8 (ct6:(128)word)) (64,64)` THEN
  ABBREV_TAC `(c7lo:(64)word) = word_subword (word_reversefields 8 (ct7:(128)word)) (0,64)` THEN
  ABBREV_TAC `(c7hi:(64)word) = word_subword (word_reversefields 8 (ct7:(128)word)) (64,64)` THEN
  ABBREV_TAC `(c8lo:(64)word) = word_subword (word_reversefields 8 (ctm8:(128)word)) (0,64)` THEN
  ABBREV_TAC `(c8hi:(64)word) = word_subword (word_reversefields 8 (ctm8:(128)word)) (64,64)` THEN
  ABBREV_TAC `(xilo:(64)word) = word_subword (word_reversefields 8 (xi:(128)word)) (0,64)` THEN
  ABBREV_TAC `(xihi:(64)word) = word_subword (word_reversefields 8 (xi:(128)word)) (64,64)` THEN
  ABBREV_TAC `(hd0:(64)word) = word_subword (h:(128)word) (0,64)` THEN
  ABBREV_TAC `(hd1:(64)word) = word_subword (h:(128)word) (64,64)` THEN
  ABBREV_TAC `(he0:(64)word) = word_subword ((polyval_dot h h):(128)word) (0,64)` THEN
  ABBREV_TAC `(he1:(64)word) = word_subword ((polyval_dot h h):(128)word) (64,64)` THEN
  ABBREV_TAC `(hf0:(64)word) = word_subword ((polyval_dot h (polyval_dot h h)):(128)word) (0,64)` THEN
  ABBREV_TAC `(hf1:(64)word) = word_subword ((polyval_dot h (polyval_dot h h)):(128)word) (64,64)` THEN
  ABBREV_TAC `(hg0:(64)word) = word_subword ((polyval_dot (polyval_dot h h) (polyval_dot h h)):(128)word) (0,64)` THEN
  ABBREV_TAC `(hg1:(64)word) = word_subword ((polyval_dot (polyval_dot h h) (polyval_dot h h)):(128)word) (64,64)` THEN
  ABBREV_TAC `(hh0:(64)word) = word_subword ((polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h):(128)word) (0,64)` THEN
  ABBREV_TAC `(hh1:(64)word) = word_subword ((polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h):(128)word) (64,64)` THEN
  ABBREV_TAC `(hj0:(64)word) = word_subword ((polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) h):(128)word) (0,64)` THEN
  ABBREV_TAC `(hj1:(64)word) = word_subword ((polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) h):(128)word) (64,64)` THEN
  ABBREV_TAC `(hm0:(64)word) = word_subword ((polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) h) h):(128)word) (0,64)` THEN
  ABBREV_TAC `(hm1:(64)word) = word_subword ((polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) h) h):(128)word) (64,64)` THEN
  ABBREV_TAC `(hn0:(64)word) = word_subword ((polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) h) h) h):(128)word) (0,64)` THEN
  ABBREV_TAC `(hn1:(64)word) = word_subword ((polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) h) h) h):(128)word) (64,64)` THEN
  ASM_REWRITE_TAC[] THEN
  (* inner pmul ABBREVs *)
  ABBREV_TAC `(w1lo:(128)word) = word_pmul (word_xor (xilo:(64)word) (c1lo:(64)word)) (hn0:(64)word)` THEN
  ABBREV_TAC `(w1hi:(128)word) = word_pmul (word_xor (xihi:(64)word) (c1hi:(64)word)) (hn1:(64)word)` THEN
  ABBREV_TAC `(w1md:(128)word) = word_pmul (word_xor (word_xor (xihi:(64)word) (c1hi:(64)word)) (word_xor (xilo:(64)word) (c1lo:(64)word))) (word_xor (hn0:(64)word) (hn1:(64)word))` THEN
  ABBREV_TAC `(w2lo:(128)word) = word_pmul (c2lo:(64)word) (hm0:(64)word)` THEN
  ABBREV_TAC `(w2hi:(128)word) = word_pmul (c2hi:(64)word) (hm1:(64)word)` THEN
  ABBREV_TAC `(w2md:(128)word) = word_pmul (word_xor (c2hi:(64)word) (c2lo:(64)word)) (word_xor (hm0:(64)word) (hm1:(64)word))` THEN
  ABBREV_TAC `(w3lo:(128)word) = word_pmul (c3lo:(64)word) (hj0:(64)word)` THEN
  ABBREV_TAC `(w3hi:(128)word) = word_pmul (c3hi:(64)word) (hj1:(64)word)` THEN
  ABBREV_TAC `(w3md:(128)word) = word_pmul (word_xor (c3hi:(64)word) (c3lo:(64)word)) (word_xor (hj0:(64)word) (hj1:(64)word))` THEN
  ABBREV_TAC `(w4lo:(128)word) = word_pmul (c4lo:(64)word) (hh0:(64)word)` THEN
  ABBREV_TAC `(w4hi:(128)word) = word_pmul (c4hi:(64)word) (hh1:(64)word)` THEN
  ABBREV_TAC `(w4md:(128)word) = word_pmul (word_xor (c4hi:(64)word) (c4lo:(64)word)) (word_xor (hh0:(64)word) (hh1:(64)word))` THEN
  ABBREV_TAC `(w5lo:(128)word) = word_pmul (c5lo:(64)word) (hg0:(64)word)` THEN
  ABBREV_TAC `(w5hi:(128)word) = word_pmul (c5hi:(64)word) (hg1:(64)word)` THEN
  ABBREV_TAC `(w5md:(128)word) = word_pmul (word_xor (c5hi:(64)word) (c5lo:(64)word)) (word_xor (hg0:(64)word) (hg1:(64)word))` THEN
  ABBREV_TAC `(w6lo:(128)word) = word_pmul (c6lo:(64)word) (hf0:(64)word)` THEN
  ABBREV_TAC `(w6hi:(128)word) = word_pmul (c6hi:(64)word) (hf1:(64)word)` THEN
  ABBREV_TAC `(w6md:(128)word) = word_pmul (word_xor (c6hi:(64)word) (c6lo:(64)word)) (word_xor (hf0:(64)word) (hf1:(64)word))` THEN
  ABBREV_TAC `(w7lo:(128)word) = word_pmul (c7lo:(64)word) (he0:(64)word)` THEN
  ABBREV_TAC `(w7hi:(128)word) = word_pmul (c7hi:(64)word) (he1:(64)word)` THEN
  ABBREV_TAC `(w7md:(128)word) = word_pmul (word_xor (c7hi:(64)word) (c7lo:(64)word)) (word_xor (he0:(64)word) (he1:(64)word))` THEN
  ABBREV_TAC `(w8lo:(128)word) = word_pmul (c8lo:(64)word) (hd0:(64)word)` THEN
  ABBREV_TAC `(w8hi:(128)word) = word_pmul (c8hi:(64)word) (hd1:(64)word)` THEN
  ABBREV_TAC `(w8md:(128)word) = word_pmul (word_xor (c8hi:(64)word) (c8lo:(64)word)) (word_xor (hd0:(64)word) (hd1:(64)word))` THEN
  REWRITE_TAC[DOUBLE_SUBWORD_JOIN; DOUBLE_SUBWORD_JOIN_HI; WORD_SUBWORD_XOR] THEN
  SUBGOAL_THEN
    `word_pmul (word_xor (xihi:(64)word) (word_xor (c1hi:(64)word) (word_xor (xilo:(64)word) (c1lo:(64)word)))) (word_xor (hn0:(64)word) (hn1:(64)word)):(128)word = w1md`
    (fun th -> REWRITE_TAC[th]) THENL
    [EXPAND_TAC "w1md" THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  (* z-vars *)
  ABBREV_TAC `(w1lo_l:(64)word) = word_subword (w1lo:(128)word) (0,64)` THEN
  ABBREV_TAC `(w1lo_h:(64)word) = word_subword (w1lo:(128)word) (64,64)` THEN
  ABBREV_TAC `(w1hi_l:(64)word) = word_subword (w1hi:(128)word) (0,64)` THEN
  ABBREV_TAC `(w1hi_h:(64)word) = word_subword (w1hi:(128)word) (64,64)` THEN
  ABBREV_TAC `(w1md_l:(64)word) = word_subword (w1md:(128)word) (0,64)` THEN
  ABBREV_TAC `(w1md_h:(64)word) = word_subword (w1md:(128)word) (64,64)` THEN
  ABBREV_TAC `(w2lo_l:(64)word) = word_subword (w2lo:(128)word) (0,64)` THEN
  ABBREV_TAC `(w2lo_h:(64)word) = word_subword (w2lo:(128)word) (64,64)` THEN
  ABBREV_TAC `(w2hi_l:(64)word) = word_subword (w2hi:(128)word) (0,64)` THEN
  ABBREV_TAC `(w2hi_h:(64)word) = word_subword (w2hi:(128)word) (64,64)` THEN
  ABBREV_TAC `(w2md_l:(64)word) = word_subword (w2md:(128)word) (0,64)` THEN
  ABBREV_TAC `(w2md_h:(64)word) = word_subword (w2md:(128)word) (64,64)` THEN
  ABBREV_TAC `(w3lo_l:(64)word) = word_subword (w3lo:(128)word) (0,64)` THEN
  ABBREV_TAC `(w3lo_h:(64)word) = word_subword (w3lo:(128)word) (64,64)` THEN
  ABBREV_TAC `(w3hi_l:(64)word) = word_subword (w3hi:(128)word) (0,64)` THEN
  ABBREV_TAC `(w3hi_h:(64)word) = word_subword (w3hi:(128)word) (64,64)` THEN
  ABBREV_TAC `(w3md_l:(64)word) = word_subword (w3md:(128)word) (0,64)` THEN
  ABBREV_TAC `(w3md_h:(64)word) = word_subword (w3md:(128)word) (64,64)` THEN
  ABBREV_TAC `(w4lo_l:(64)word) = word_subword (w4lo:(128)word) (0,64)` THEN
  ABBREV_TAC `(w4lo_h:(64)word) = word_subword (w4lo:(128)word) (64,64)` THEN
  ABBREV_TAC `(w4hi_l:(64)word) = word_subword (w4hi:(128)word) (0,64)` THEN
  ABBREV_TAC `(w4hi_h:(64)word) = word_subword (w4hi:(128)word) (64,64)` THEN
  ABBREV_TAC `(w4md_l:(64)word) = word_subword (w4md:(128)word) (0,64)` THEN
  ABBREV_TAC `(w4md_h:(64)word) = word_subword (w4md:(128)word) (64,64)` THEN
  ABBREV_TAC `(w5lo_l:(64)word) = word_subword (w5lo:(128)word) (0,64)` THEN
  ABBREV_TAC `(w5lo_h:(64)word) = word_subword (w5lo:(128)word) (64,64)` THEN
  ABBREV_TAC `(w5hi_l:(64)word) = word_subword (w5hi:(128)word) (0,64)` THEN
  ABBREV_TAC `(w5hi_h:(64)word) = word_subword (w5hi:(128)word) (64,64)` THEN
  ABBREV_TAC `(w5md_l:(64)word) = word_subword (w5md:(128)word) (0,64)` THEN
  ABBREV_TAC `(w5md_h:(64)word) = word_subword (w5md:(128)word) (64,64)` THEN
  ABBREV_TAC `(w6lo_l:(64)word) = word_subword (w6lo:(128)word) (0,64)` THEN
  ABBREV_TAC `(w6lo_h:(64)word) = word_subword (w6lo:(128)word) (64,64)` THEN
  ABBREV_TAC `(w6hi_l:(64)word) = word_subword (w6hi:(128)word) (0,64)` THEN
  ABBREV_TAC `(w6hi_h:(64)word) = word_subword (w6hi:(128)word) (64,64)` THEN
  ABBREV_TAC `(w6md_l:(64)word) = word_subword (w6md:(128)word) (0,64)` THEN
  ABBREV_TAC `(w6md_h:(64)word) = word_subword (w6md:(128)word) (64,64)` THEN
  ABBREV_TAC `(w7lo_l:(64)word) = word_subword (w7lo:(128)word) (0,64)` THEN
  ABBREV_TAC `(w7lo_h:(64)word) = word_subword (w7lo:(128)word) (64,64)` THEN
  ABBREV_TAC `(w7hi_l:(64)word) = word_subword (w7hi:(128)word) (0,64)` THEN
  ABBREV_TAC `(w7hi_h:(64)word) = word_subword (w7hi:(128)word) (64,64)` THEN
  ABBREV_TAC `(w7md_l:(64)word) = word_subword (w7md:(128)word) (0,64)` THEN
  ABBREV_TAC `(w7md_h:(64)word) = word_subword (w7md:(128)word) (64,64)` THEN
  ABBREV_TAC `(w8lo_l:(64)word) = word_subword (w8lo:(128)word) (0,64)` THEN
  ABBREV_TAC `(w8lo_h:(64)word) = word_subword (w8lo:(128)word) (64,64)` THEN
  ABBREV_TAC `(w8hi_l:(64)word) = word_subword (w8hi:(128)word) (0,64)` THEN
  ABBREV_TAC `(w8hi_h:(64)word) = word_subword (w8hi:(128)word) (64,64)` THEN
  ABBREV_TAC `(w8md_l:(64)word) = word_subword (w8md:(128)word) (0,64)` THEN
  ABBREV_TAC `(w8md_h:(64)word) = word_subword (w8md:(128)word) (64,64)` THEN
  ASM_REWRITE_TAC[] THEN
  (* Normalize LHS mid-pmuls to abbreviated w?md (swapped xor arg order). *)
  SUBGOAL_THEN `word_pmul (word_xor (c2lo:(64)word) (c2hi:(64)word)) (word_xor (hm0:(64)word) (hm1:(64)word)):(128)word = w2md`
    (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "w2md" THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  SUBGOAL_THEN `word_pmul (word_xor (c3lo:(64)word) (c3hi:(64)word)) (word_xor (hj0:(64)word) (hj1:(64)word)):(128)word = w3md`
    (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "w3md" THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  SUBGOAL_THEN `word_pmul (word_xor (c4lo:(64)word) (c4hi:(64)word)) (word_xor (hh0:(64)word) (hh1:(64)word)):(128)word = w4md`
    (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "w4md" THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  SUBGOAL_THEN `word_pmul (word_xor (c5lo:(64)word) (c5hi:(64)word)) (word_xor (hg0:(64)word) (hg1:(64)word)):(128)word = w5md`
    (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "w5md" THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  SUBGOAL_THEN `word_pmul (word_xor (c6lo:(64)word) (c6hi:(64)word)) (word_xor (hf0:(64)word) (hf1:(64)word)):(128)word = w6md`
    (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "w6md" THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  SUBGOAL_THEN `word_pmul (word_xor (c7lo:(64)word) (c7hi:(64)word)) (word_xor (he0:(64)word) (he1:(64)word)):(128)word = w7md`
    (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "w7md" THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  SUBGOAL_THEN `word_pmul (word_xor (c8lo:(64)word) (c8hi:(64)word)) (word_xor (hd0:(64)word) (hd1:(64)word)):(128)word = w8md`
    (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "w8md" THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  SUBGOAL_THEN `word_pmul (word_xor (xilo:(64)word) (word_xor (c1lo:(64)word) (word_xor (xihi:(64)word) (c1hi:(64)word)))) (word_xor (hn0:(64)word) (hn1:(64)word)):(128)word = w1md`
    (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "w1md" THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  (* qS: small Barrett pmul. *)
  ABBREV_TAC `(qS:(128)word) = word_pmul (word_xor (w8lo_l:(64)word) (word_xor w7lo_l (word_xor w6lo_l (word_xor w5lo_l (word_xor w4lo_l (word_xor w3lo_l (word_xor w2lo_l (w1lo_l)))))))) (word 13979173243358019584:(64)word)` THEN
  SUBGOAL_THEN `word_pmul (word_xor (w1lo_l:(64)word) (word_xor w2lo_l (word_xor w3lo_l (word_xor w4lo_l (word_xor w5lo_l (word_xor w6lo_l (word_xor w7lo_l (w8lo_l)))))))) (word 13979173243358019584:(64)word):(128)word = qS`
    (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "qS" THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  (* qB: big Barrett pmul; fold LHS-order copy via bubble_sort_conv. *)
  ABBREV_TAC `(qB:(128)word) = word_pmul
    (word_xor (w8md_l:(64)word) (word_xor w7md_l (word_xor w6md_l (word_xor w5md_l (word_xor w4md_l (word_xor w3md_l (word_xor w2md_l (word_xor w1md_l (word_xor w8lo_l (word_xor w7lo_l (word_xor w6lo_l (word_xor w5lo_l (word_xor w4lo_l (word_xor w3lo_l (word_xor w2lo_l (word_xor w1lo_l (word_xor w8hi_l (word_xor w7hi_l (word_xor w6hi_l (word_xor w5hi_l (word_xor w4hi_l (word_xor w3hi_l (word_xor w2hi_l (word_xor w1hi_l (word_xor (word_subword (qS:(128)word) (0,64)) (word_xor w8lo_h (word_xor w7lo_h (word_xor w6lo_h (word_xor w5lo_h (word_xor w4lo_h (word_xor w3lo_h (word_xor w2lo_h (w1lo_h))))))))))))))))))))))))))))))))) (word 13979173243358019584:(64)word)` THEN
  SUBGOAL_THEN
    `word_pmul (word_xor (w1lo_h:(64)word) (word_xor w2lo_h (word_xor w3lo_h (word_xor w4lo_h (word_xor w5lo_h (word_xor w6lo_h (word_xor w7lo_h (word_xor w8lo_h (word_xor w1md_l (word_xor w2md_l (word_xor w3md_l (word_xor w4md_l (word_xor w5md_l (word_xor w6md_l (word_xor w7md_l (word_xor w8md_l (word_xor w1hi_l (word_xor w2hi_l (word_xor w3hi_l (word_xor w4hi_l (word_xor w5hi_l (word_xor w6hi_l (word_xor w7hi_l (word_xor w8hi_l (word_xor w1lo_l (word_xor w2lo_l (word_xor w3lo_l (word_xor w4lo_l (word_xor w5lo_l (word_xor w6lo_l (word_xor w7lo_l (word_xor w8lo_l ((word_subword (qS:(128)word) (0,64))))))))))))))))))))))))))))))))))) (word 13979173243358019584:(64)word):(128)word = qB`
    (fun th -> REWRITE_TAC[th]) THENL
    [EXPAND_TAC "qB" THEN AP_THM_TAC THEN AP_TERM_TAC THEN
     CONV_TAC(BINOP_CONV bubble_sort_conv) THEN REFL_TAC; ALL_TAC];;

(* Step 4: b0-general mask-register collapse, applied to ALL assumptions. *)
let GCM_8B_MASK_COLLAPSE_ASMS : tactic =
  SUBGOAL_THEN `1 <= (byte_len:num) /\ byte_len <= 16` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(fun bth -> if concl bth = `1 <= (byte_len:num) /\ byte_len <= 16` then
    RULE_ASSUM_TAC(REWRITE_RULE[GEN `b0:int128` (MP (SPEC_ALL EIGHTBLOCK_MASK_REG) bth)]) else NO_TAC);;

(* Step 5: bridge the machine block-8 keystream (collapsed +7 counter, baked
   into final_xi) to the spec ct8. *)
let GCM_8B_KS8_FOLD : tactic = fun (asl,w) ->
  let substr sub s =
    let ls=String.length s and lb=String.length sub in
    let rec go i = if i+lb>ls then false
                   else if String.sub s i lb = sub then true else go(i+1) in go 0 in
  let fxidef = snd(find (fun (_,th) ->
    is_eq(concl th) && (try rand(concl th)=`final_xi:(128)word` with _->false)) asl) in
  let body = lhs(concl fxidef) in
  (* June base: require rk14 to pick the full keystream (mirror band-5/6/7). *)
  let best = ref None in
  let rec walk t =
    (try let s=string_of_term t in
      if substr "pt8" s && substr "aese" s && substr "rk14" s &&
         (try fst(dest_const(repeat rator t))="word_xor" with _->false) &&
         (match !best with None->true | Some b -> String.length s < String.length(string_of_term b))
      then best := Some t
     with _->());
    (match t with Comb(a,b)->walk a; walk b | Abs(_,b)->walk b | _->()) in
  walk body;
  let ks8 = (match !best with Some t->t | None->failwith "KS8_FOLD: ks8 not found") in
  let bri = WORD_BLAST `word_bytereverse (word_bytereverse (x:(32)word)) = x` in
  let add7 = WORD_RULE `word_add (word_add (word_add (word_add (word_add (word_add (word_add (x:(32)word) (word 1)) (word 1)) (word 1)) (word 1)) (word 1)) (word 1)) (word 1) = word_add x (word 7)` in
  (SUBGOAL_THEN (mk_eq(ks8, `ct8:(128)word`)) ASSUME_TAC THENL
    [(* band-4/5/6/7 counter peel for the collapsed +7 counter. *)
     CONV_TAC SYM_CONV THEN EXPAND_TAC "ct8" THEN
     REWRITE_TAC[AES256_ENCRYPT_UNFOLD] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
     REWRITE_TAC[WORD_XOR_ASSOC] THEN
     AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
     REPEAT(AP_THM_TAC ORELSE AP_TERM_TAC) THEN
     REWRITE_TAC[gcm_ctr_inc] THEN
     REWRITE_TAC[WORD_REVERSEFIELDS_REVERSEFIELDS; WORD_REVERSEFIELDS_8_BYTEREVERSE_32] THEN
     REWRITE_TAC[INSERT_SUBWORD; INSERT_IDEM] THEN
     REWRITE_TAC[bri] THEN REWRITE_TAC[add7] THEN
     REWRITE_TAC[CTR_WORD_INSERT];
     ALL_TAC] THEN
   FIRST_ASSUM(fun th ->
     if is_eq(concl th) && rand(concl th)=`ct8:(128)word` &&
        (try fst(dest_const(repeat rator (lhs(concl th))))="word_xor" with _->false) &&
        String.length(string_of_term(lhs(concl th))) > 1000
     then RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th] else NO_TAC))
  (asl,w);;

(* June-2026 base: per-half XOR-AC closer, mirroring band-4..7.  8 mids
   (w1md=hn, w2md=hm, w3md=hj, w4md=hh, w5md=hg, w6md=hf, w7md=he, w8md=hd),
   qS=8, qB=33. *)
let GCM_8B_FOLD_MIDS_TAC : tactic =
  fun (asl,gg) ->
    let rec finds hd t acc = match t with
      | Comb(Comb(Const("word_pmul",_),a),x) when x = hd ->
          a :: (finds hd a (finds hd x acc))
      | Comb(l,r) -> finds hd l (finds hd r acc)
      | Abs(_,b) -> finds hd b acc | _ -> acc in
    let hnw = `word_xor (hn0:(64)word) hn1`
    and hmw = `word_xor (hm0:(64)word) hm1`
    and hjw = `word_xor (hj0:(64)word) hj1`
    and hhw = `word_xor (hh0:(64)word) hh1`
    and hgw = `word_xor (hg0:(64)word) hg1`
    and hfw = `word_xor (hf0:(64)word) hf1`
    and hew = `word_xor (he0:(64)word) he1`
    and hdw = `word_xor (hd0:(64)word) hd1` in
    let mk tgt hd arg =
      SUBGOAL_THEN
        (mk_eq(list_mk_comb(`word_pmul:(64)word->(64)word->(128)word`,[arg;hd]),tgt))
        (fun th -> REWRITE_TAC[th]) THENL
       [EXPAND_TAC (fst(dest_var tgt)) THEN AP_THM_TAC THEN AP_TERM_TAC THEN
        CONV_TAC WORD_RULE; ALL_TAC] in
    (EVERY ((map (mk `w1md:(128)word` hnw) (setify(finds hnw gg [])))
          @ (map (mk `w2md:(128)word` hmw) (setify(finds hmw gg [])))
          @ (map (mk `w3md:(128)word` hjw) (setify(finds hjw gg [])))
          @ (map (mk `w4md:(128)word` hhw) (setify(finds hhw gg [])))
          @ (map (mk `w5md:(128)word` hgw) (setify(finds hgw gg [])))
          @ (map (mk `w6md:(128)word` hfw) (setify(finds hfw gg [])))
          @ (map (mk `w7md:(128)word` hew) (setify(finds hew gg [])))
          @ (map (mk `w8md:(128)word` hdw) (setify(finds hdw gg []))))) (asl,gg);;
let GCM_8B_FOLD_TO tgt natoms : tactic =
  let w64 = `word 13979173243358019584:(64)word` in
  fun (asl,gg) ->
    let rec finds t acc = match t with
      | Comb(Comb(Const("word_pmul",_),a),x) when x = w64 ->
          a :: (finds a (finds x acc))
      | Comb(l,r) -> finds l (finds r acc) | Abs(_,b) -> finds b acc | _ -> acc in
    let rec at t = match t with
      | Comb(Comb(Const("word_xor",_),x),y) -> at x @ at y | _ -> [t] in
    let args = List.filter (fun a -> List.length(at a) = natoms) (setify(finds gg [])) in
    (EVERY (map (fun a ->
       FIRST [SUBGOAL_THEN
                (mk_eq(list_mk_comb(`word_pmul:(64)word->(64)word->(128)word`,[a;w64]),tgt))
                (fun th -> REWRITE_TAC[th]) THENL
               [EXPAND_TAC (fst(dest_var tgt)) THEN AP_THM_TAC THEN AP_TERM_TAC THEN
                CONV_TAC(BINOP_CONV bubble_fix) THEN REFL_TAC; ALL_TAC];
              ALL_TAC]) args)) (asl,gg);;
let GCM_8B_HALF_CLOSE : tactic =
  GCM_8B_FOLD_MIDS_TAC THEN ASM_REWRITE_TAC[] THEN
  GCM_8B_FOLD_TO `qS:(128)word` 8 THEN ASM_REWRITE_TAC[] THEN
  GCM_8B_FOLD_TO `qB:(128)word` 33 THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(BINOP_CONV bubble_fix) THEN REFL_TAC;;

(* The full GHASH closer: applied at the final GHASH conjunct. *)
let GCM_8B_GHASH_CLOSE : tactic =
  GCM_8B_FOLD_SPEC_CTS THEN
  REWRITE_TAC[GHASH_POLYVAL_ACC_8; POLYVAL_DOT_H8_EQ; POLYVAL_DOT_H7_EQ; POLYVAL_DOT_H6_EQ; POLYVAL_DOT_H5_EQ; GSYM WORD_REVERSEFIELDS_XOR_8_128] THEN
  GCM_8B_MASK_COLLAPSE_ASMS THEN
  GCM_8B_KS8_FOLD THEN
  GCM_8B_TAIL_NOFINAL THEN
  REWRITE_TAC[XI_HS_LO_8; XI_HS_HI_8] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `word_pmul (word_xor (xihi:(64)word) (word_xor c1hi (word_xor xilo c1lo)))
              (word_xor (hn0:(64)word) hn1):(128)word = w1md`
   (fun th -> REWRITE_TAC[th]) THENL
   [EXPAND_TAC "w1md" THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  BINOP_TAC THENL [GCM_8B_HALF_CLOSE; GCM_8B_HALF_CLOSE];;

(* --- The 8-block branch theorem. --- *)

(* Full assembled AES256_GCM_ENCRYPT_LT_8BLOCK_CORRECT proof (more_than_7).
   Mirrors the 7-block (more_than_6) recipe.  The more_than_7 path is the
   highest dispatch branch (b.gt #112 taken directly to the 8-wide GHASH at
   0xf98), which reads scratch register Q18 via an INS (mov v18.d[0]) before
   fully writing it; the precondition pins read Q18 = q18i (its high lane is
   dead, overwritten by the pmull that uses only the low lane). *)

let AES256_GCM_ENCRYPT_LT_8BLOCK_CONCRETE = prove
 (gcm_8b_goal,
  (* ---- symbolic simulation (store-based ct abbreviation) ---- *)
  GCM_INIT_TAC GCM_CBZ_LEMMA8 THEN GCM_PROLOGUE_TAC THEN GCM_RUN 20 263 THEN
  GCM_INLOOP_GUARD_TAC GCM_X8_LEMMA8 THEN GCM_RUN 267 272 THEN
  GCM_BND16 GCM_X8TAIL_LEMMA8 THEN
  GCM_RUN_THEN GCM_CASCADE8_TAC 273 276 THEN
  GCM_RUN 277 300 THEN
  abbrev_ct_from_store 0 1 THEN abbrev_ct_from_store 16 2 THEN
  GCM_RUN 301 340 THEN
  abbrev_ct_from_store 32 3 THEN abbrev_ct_from_store 48 4 THEN abbrev_ct_from_store 64 5 THEN
  GCM_RUN 341 370 THEN
  abbrev_ct_from_store 80 6 THEN abbrev_ct_from_store 96 7 THEN
  GCM_RUN 371 417 THEN
  SUBGOAL_THEN `1 <= byte_len /\ byte_len <= 16` MP_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP EIGHTBLOCK_MASK_REG th])) THEN
  GCM_NBLOCK_POST_SIM_NORMALIZE_TAC THEN ABBREV_FINAL_XI_TAC THEN
  ARM_STEPS_TAC AES256_GCM_EXEC (418--425) THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ENSURES_FINAL_STATE_TAC THEN
  SUBGOAL_THEN `1 <= byte_len /\ byte_len <= 16` MP_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP EIGHTBLOCK_MASK_REG th]) THEN
  ASM_SIMP_TAC[EIGHTBLOCK_USHR] THEN
  (* ---- nine conjuncts: ct1..ct7, masked-ct8, GHASH ---- *)
  CONJ_TAC THENL [CT_CLOSE_8 1; ALL_TAC] THEN
  CONJ_TAC THENL [CONV_TAC SYM_CONV THEN GCM_8BLOCK_CT2_STEP_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [CONV_TAC SYM_CONV THEN GCM_8BLOCK_CT3_STEP_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [CONV_TAC SYM_CONV THEN GCM_8BLOCK_CT4_STEP_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [CONV_TAC SYM_CONV THEN GCM_8BLOCK_CT5_STEP_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [CONV_TAC SYM_CONV THEN GCM_8BLOCK_CT6_STEP_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [CONV_TAC SYM_CONV THEN GCM_8BLOCK_CT7_STEP_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [GCM_8B_MASKED_CT8_CLOSE; ALL_TAC] THEN
  (* ---- ct8 abbreviation (spec form) so the closer's ctm8 works ---- *)
  ABBREV_TAC `ct8 = word_xor pt8
    (aes256_encrypt (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ivec))))))) [rk0;rk1;rk2;rk3;rk4;rk5;rk6;rk7;rk8;rk9;rk10;rk11;rk12;rk13;rk14]):(128)word` THEN
  (* ---- GHASH conjunct ---- *)
  GCM_8B_GHASH_CLOSE);;

(* ========================================================================= *)
(* The zero-input branch (byte_len = 0).  The length argument X1 = 0, so the *)
(* `cbz x1` at the entry (pc+4) is taken, jumping directly to the early exit *)
(* (`mov w0,#0` @ pc+4592; `ret` @ pc+4596).  Nothing is encrypted: the      *)
(* output and the GHASH accumulator xi are left unchanged and X0 = 0.        *)
(* ========================================================================= *)

let gcm_0b_goal = `!in_ptr out_ptr xi_ptr ivec_ptr key_ptr htable_ptr
    (out0:(128)word) (xi:(128)word)
    stackptr pc.
    aligned 16 stackptr /\
    nonoverlapping (word pc,4600) (out_ptr:int64,16) /\
    nonoverlapping (word pc,4600) (xi_ptr:int64,16) /\
    nonoverlapping (word pc,4600) (ivec_ptr:int64,16) /\
    nonoverlapping (out_ptr,16) (word pc,4600) /\
    nonoverlapping (xi_ptr,16) (word pc,4600)
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) aes256_gcm_mc /\
           read PC s = word pc /\
           C_ARGUMENTS [in_ptr; word 0; out_ptr; xi_ptr;
                        ivec_ptr; key_ptr; htable_ptr] s /\
           read SP s = word_add stackptr (word 80) /\
           read (memory :> bytes128 out_ptr) s = out0 /\
           read (memory :> bytes128 xi_ptr) s = xi)
      (\s. read PC s = word(pc + 4596) /\
           read X0 s = word 0 /\
           read (memory :> bytes128 out_ptr) s = out0 /\
           read (memory :> bytes128 xi_ptr) s = xi)
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [PC])`;;

let AES256_GCM_ENCRYPT_LT_0BLOCK_CONCRETE = prove
 (gcm_0b_goal,
  (* Entry + nop (1); cbz x1 (2) is TAKEN since X1 = 0, jumping to pc+4592;  *)
  (* mov w0,#0 (3) lands at the RET (pc+4596).                               *)
  REWRITE_TAC[C_ARGUMENTS; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              SOME_FLAGS; NONOVERLAPPING_CLAUSES; fst AES256_GCM_EXEC] THEN
  REPEAT STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC AES256_GCM_EXEC (1--3) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* COMBINED CORRECTNESS THEOREM (XTS-style dispatch over per-block bands).   *)
(*                                                                           *)
(* Recursive byte-list spec aes256_gcm_encrypt / gcm_final_xi + the bridge   *)
(* lemmas relating each band's concrete word-level postcondition to the      *)
(* abstract spec, then AES256_GCM_ENCRYPT_CORRECT dispatching by input       *)
(* length over the 0..8-block bands (val len <= 128).                        *)
(* ========================================================================= *)

(* ========================================================================= *)
(* Recursive AES-256-GCM encrypt specification over a plaintext byte list,   *)
(* mirroring the AES-XTS spec.  Reuses the mode-agnostic byte/word           *)
(* conversions and byte_list_at memory predicate, and the existing GCM       *)
(* per-block primitives (aes256_encrypt, gcm_ctr_inc, ghash_polyval_acc).    *)
(* ========================================================================= *)

(* --- byte<->word conversions + memory predicate (verbatim from XTS) --- *)
let bytes_to_int128 = define
  `bytes_to_int128 (bs : byte list) : int128 =
    word_join
      (word_join
        (word_join (word_join (EL 15 bs) (EL 14 bs) : int16) (word_join (EL 13 bs) (EL 12 bs) : int16) : int32)
        (word_join (word_join (EL 11 bs) (EL 10 bs) : int16) (word_join (EL 9 bs) (EL 8 bs) : int16) : int32) : int64)
      (word_join
        (word_join (word_join (EL 7 bs) (EL 6 bs) : int16) (word_join (EL 5 bs) (EL 4 bs) : int16) : int32)
        (word_join (word_join (EL 3 bs) (EL 2 bs) : int16) (word_join (EL 1 bs) (EL 0 bs) : int16) : int32) : int64)`;;

let int128_to_bytes = define
  `int128_to_bytes (w : int128) : byte list =
     [word_subword w (0, 8); word_subword w (8, 8); word_subword w (16, 8); word_subword w (24, 8);
      word_subword w (32, 8); word_subword w (40, 8); word_subword w (48, 8); word_subword w (56, 8);
      word_subword w (64, 8); word_subword w (72, 8); word_subword w (80, 8); word_subword w (88, 8);
      word_subword w (96, 8); word_subword w (104, 8); word_subword w (112, 8); word_subword w (120, 8)]`;;

let byte_list_at = define
  `byte_list_at (m : byte list) (m_p : int64) (len:int64) s =
    ! i. i < val len ==> read (memory :> bytes8(word_add m_p (word i))) s = EL i m`;;

(* --- GCM keystream: AES-CTR of (gcm_ctr_inc^i ivec) --- *)
let gcm_ctr_iter = new_recursive_definition num_RECURSION
  `gcm_ctr_iter 0 (ivec:(128)word) = ivec /\
   gcm_ctr_iter (SUC n) (ivec:(128)word) = gcm_ctr_inc (gcm_ctr_iter n ivec)`;;

let gcm_keystream = new_definition
  `gcm_keystream (i:num) (ivec:(128)word) (rks:int128 list) : (128)word =
     aes256_encrypt (gcm_ctr_iter i ivec) [(EL 0 rks);(EL 1 rks);(EL 2 rks);(EL 3 rks);(EL 4 rks);(EL 5 rks);(EL 6 rks);(EL 7 rks);(EL 8 rks);(EL 9 rks);(EL 10 rks);(EL 11 rks);(EL 12 rks);(EL 13 rks);(EL 14 rks)]`;;

(* --- recursive full-block ciphertext (int128 blocks) --- *)
let gcm_ct_rec = new_specification ["gcm_ct_rec"]
  (prove_general_recursive_function_exists
    `?gcm_ct_rec.
       ! (i:num) (nfull:num) (P:byte list) (ivec:(128)word) (rks:int128 list).
         gcm_ct_rec i nfull P ivec rks : (int128 list) =
           if nfull = 0 then []
           else
             let blk = bytes_to_int128 (SUB_LIST (i * 16, 16) P) in
             let ct = word_xor blk (gcm_keystream i ivec rks) in
             CONS ct (gcm_ct_rec (i + 1) (nfull - 1) P ivec rks)`);;

(* --- recursive full-block ciphertext (flat byte list) --- *)
let gcm_ct_bytes_rec = new_specification ["gcm_ct_bytes_rec"]
  (prove_general_recursive_function_exists
    `?gcm_ct_bytes_rec.
       ! (i:num) (nfull:num) (P:byte list) (ivec:(128)word) (rks:int128 list).
         gcm_ct_bytes_rec i nfull P ivec rks : (byte list) =
           if nfull = 0 then []
           else
             let blk = bytes_to_int128 (SUB_LIST (i * 16, 16) P) in
             let ct = word_xor blk (gcm_keystream i ivec rks) in
             APPEND (int128_to_bytes ct) (gcm_ct_bytes_rec (i + 1) (nfull - 1) P ivec rks)`);;

(* --- masked partial-tail ciphertext block: read the full 16-byte block     *)
(* then mask to `tail` bytes (the binary reads a full block and masks).      *)
let gcm_ctm_tail = new_definition
  `gcm_ctm_tail (i:num) (tail:num) (P:byte list) (ivec:(128)word) (rks:int128 list) : (128)word =
     let blk = bytes_to_int128 (SUB_LIST (i * 16, 16) P) in
     let ct = word_xor blk (gcm_keystream i ivec rks) in
     word_and ct (word (2 EXP (8 * tail) - 1))`;;

(* --- list of GHASH input blocks: full blocks ++ masked tail --- *)
let gcm_ghash_blocks = new_definition
  `gcm_ghash_blocks (len:num) (P:byte list) (ivec:(128)word) (rks:int128 list) : (int128 list) =
     let tail = len - 16 * ((len - 1) DIV 16) in
     let nfull = (len - 1) DIV 16 in
     APPEND (gcm_ct_rec 0 nfull P ivec rks)
            [gcm_ctm_tail nfull tail P ivec rks]`;;

(* --- the ciphertext byte list (output): full block bytes ++ first `tail`   *)
(* bytes of the masked partial block; [] for empty input.                    *)
let aes256_gcm_encrypt = new_definition
  `aes256_gcm_encrypt (len:num) (P:byte list) (ivec:(128)word) (rks:int128 list) : (byte list) =
     let tail = len - 16 * ((len - 1) DIV 16) in
     let nfull = (len - 1) DIV 16 in
     if len = 0 then []
     else APPEND (gcm_ct_bytes_rec 0 nfull P ivec rks)
                 (SUB_LIST (0, tail) (int128_to_bytes (gcm_ctm_tail nfull tail P ivec rks)))`;;

(* --- the final GHASH accumulator Xi; unchanged for empty input. --- *)
let gcm_final_xi = new_definition
  `gcm_final_xi (len:num) (P:byte list) (ivec:(128)word) (rks:int128 list)
                (xi:(128)word) (h:(128)word) : (128)word =
     if len = 0 then xi
     else word_reversefields 8
       (ghash_polyval_acc h (word_reversefields 8 xi)
          (MAP (\b. word_reversefields 8 b) (gcm_ghash_blocks len P ivec rks)))`;;

(* ========================================================================= *)
(* Bridge lemmas: concrete 1-block band postcondition <-> abstract spec.     *)
(* ========================================================================= *)

let EL_16_8_CLAUSES = (CONJUNCTS o prove)
 (`EL 0 [a0;a1;a2;a3;a4;a5;a6;a7;a8;a9;a10;a11;a12;a13;a14;a15] = a0 /\
   EL 1 [a0;a1;a2;a3;a4;a5;a6;a7;a8;a9;a10;a11;a12;a13;a14;a15] = a1 /\
   EL 2 [a0;a1;a2;a3;a4;a5;a6;a7;a8;a9;a10;a11;a12;a13;a14;a15] = a2 /\
   EL 3 [a0;a1;a2;a3;a4;a5;a6;a7;a8;a9;a10;a11;a12;a13;a14;a15] = a3 /\
   EL 4 [a0;a1;a2;a3;a4;a5;a6;a7;a8;a9;a10;a11;a12;a13;a14;a15] = a4 /\
   EL 5 [a0;a1;a2;a3;a4;a5;a6;a7;a8;a9;a10;a11;a12;a13;a14;a15] = a5 /\
   EL 6 [a0;a1;a2;a3;a4;a5;a6;a7;a8;a9;a10;a11;a12;a13;a14;a15] = a6 /\
   EL 7 [a0;a1;a2;a3;a4;a5;a6;a7;a8;a9;a10;a11;a12;a13;a14;a15] = a7 /\
   EL 8 [a0;a1;a2;a3;a4;a5;a6;a7;a8;a9;a10;a11;a12;a13;a14;a15] = a8 /\
   EL 9 [a0;a1;a2;a3;a4;a5;a6;a7;a8;a9;a10;a11;a12;a13;a14;a15] = a9 /\
   EL 10 [a0;a1;a2;a3;a4;a5;a6;a7;a8;a9;a10;a11;a12;a13;a14;a15] = a10 /\
   EL 11 [a0;a1;a2;a3;a4;a5;a6;a7;a8;a9;a10;a11;a12;a13;a14;a15] = a11 /\
   EL 12 [a0;a1;a2;a3;a4;a5;a6;a7;a8;a9;a10;a11;a12;a13;a14;a15] = a12 /\
   EL 13 [a0;a1;a2;a3;a4;a5;a6;a7;a8;a9;a10;a11;a12;a13;a14;a15] = a13 /\
   EL 14 [a0;a1;a2;a3;a4;a5;a6;a7;a8;a9;a10;a11;a12;a13;a14;a15] = a14 /\
   EL 15 [a0;a1;a2;a3;a4;a5;a6;a7;a8;a9;a10;a11;a12;a13;a14;a15] = a15`,
  REWRITE_TAC(map num_CONV [`15`;`14`;`13`;`12`;`11`;`10`;`9`;`8`;`7`;`6`;`5`;`4`;`3`;`2`;`1`]) THEN
  REWRITE_TAC[EL; HD; TL]);;

let BYTES128_TO_BYTES8_THM = prove(
  `!pos bl_ptr s.
    read (memory :> bytes128 (word_add bl_ptr (word pos))) s =
    bytes_to_int128
      [read (memory :> bytes8 (word_add bl_ptr (word (pos + 0x0)))) s;
       read (memory :> bytes8 (word_add bl_ptr (word (pos + 0x1)))) s;
       read (memory :> bytes8 (word_add bl_ptr (word (pos + 0x2)))) s;
       read (memory :> bytes8 (word_add bl_ptr (word (pos + 0x3)))) s;
       read (memory :> bytes8 (word_add bl_ptr (word (pos + 0x4)))) s;
       read (memory :> bytes8 (word_add bl_ptr (word (pos + 0x5)))) s;
       read (memory :> bytes8 (word_add bl_ptr (word (pos + 0x6)))) s;
       read (memory :> bytes8 (word_add bl_ptr (word (pos + 0x7)))) s;
       read (memory :> bytes8 (word_add bl_ptr (word (pos + 0x8)))) s;
       read (memory :> bytes8 (word_add bl_ptr (word (pos + 0x9)))) s;
       read (memory :> bytes8 (word_add bl_ptr (word (pos + 0xa)))) s;
       read (memory :> bytes8 (word_add bl_ptr (word (pos + 0xb)))) s;
       read (memory :> bytes8 (word_add bl_ptr (word (pos + 0xc)))) s;
       read (memory :> bytes8 (word_add bl_ptr (word (pos + 0xd)))) s;
       read (memory :> bytes8 (word_add bl_ptr (word (pos + 0xe)))) s;
       read (memory :> bytes8 (word_add bl_ptr (word (pos + 0xf)))) s]`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[bytes_to_int128] THEN REWRITE_TAC EL_16_8_CLAUSES THEN
  GEN_REWRITE_TAC TOP_DEPTH_CONV [READ_MEMORY_BYTESIZED_SPLIT; WORD_ADD_ASSOC_CONSTS] THEN
  CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
  ONCE_REWRITE_TAC [ARITH_RULE `pos + 0 = (pos:num)`] THEN REFL_TAC);;

let SUBWORD_BYTES_TO_INT128 = prove(
 `!b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 i. i < 16
   ==> word_subword (bytes_to_int128 [b0;b1;b2;b3;b4;b5;b6;b7;b8;b9;b10;b11;b12;b13;b14;b15]) (8*i,8):byte =
       EL i [b0;b1;b2;b3;b4;b5;b6;b7;b8;b9;b10;b11;b12;b13;b14;b15]`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  POP_ASSUM MP_TAC THEN SPEC_TAC(`i:num`,`i:num`) THEN
  CONV_TAC EXPAND_CASES_CONV THEN
  REWRITE_TAC[bytes_to_int128] THEN REWRITE_TAC EL_16_8_CLAUSES THEN
  CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN CONV_TAC WORD_BLAST);;

let BYTES128_TO_BYTES8_0 = REWRITE_RULE[ADD_CLAUSES; WORD_ADD_0] (SPEC `0` BYTES128_TO_BYTES8_THM);;

let BYTE8_OF_BYTES128 = prove(
 `!p s i. i < 16 ==> read (memory :> bytes8 (word_add p (word i))) s =
                     word_subword (read (memory :> bytes128 p) s) (8*i,8)`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [BYTES128_TO_BYTES8_0] THEN
  ASM_SIMP_TAC[SUBWORD_BYTES_TO_INT128] THEN
  POP_ASSUM MP_TAC THEN SPEC_TAC(`i:num`,`i:num`) THEN
  CONV_TAC EXPAND_CASES_CONV THEN
  REWRITE_TAC EL_16_8_CLAUSES THEN REWRITE_TAC[WORD_ADD_0]);;

let EL_SUB_LIST_0 = prove(
 `!(l:A list) n i. i < n ==> EL i (SUB_LIST(0,n) l) = EL i l`,
  LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THENL
   [REWRITE_TAC[SUB_LIST_CLAUSES];
    ASM_CASES_TAC `n = 0` THENL [ASM_MESON_TAC[LT]; ALL_TAC] THEN
    SUBGOAL_THEN `n = SUC(n-1)` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[SUB_LIST_CLAUSES] THEN
    ASM_CASES_TAC `i = 0` THEN ASM_REWRITE_TAC[EL; HD; TL] THEN
    SUBGOAL_THEN `i = SUC(i-1)` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[EL; TL] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]);;

let EL_INT128_TO_BYTES = prove(
 `!w i. i < 16 ==> EL i (int128_to_bytes w):byte = word_subword w (8*i,8)`,
  GEN_TAC THEN REWRITE_TAC[int128_to_bytes] THEN
  CONV_TAC EXPAND_CASES_CONV THEN REWRITE_TAC EL_16_8_CLAUSES THEN
  CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV));;

let MASK_BYTE_OUT = prove(
 `!(ct:int128) (out0:int128) (n:num) (i:num).
    i < n /\ n <= 16
    ==> word_subword (word_or (word_and ct (word (2 EXP (8*n) - 1):int128))
                              (word_and out0 (word_not (word (2 EXP (8*n) - 1):int128)))) (8*i,8):byte =
        word_subword ct (8*i,8)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_SUBWORD; BIT_WORD_OR; BIT_WORD_AND; BIT_WORD_NOT;
              BIT_MASK_WORD; DIMINDEX_8; DIMINDEX_128] THEN
  X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  SUBGOAL_THEN `8 * i + j < 128` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `8 * i + j < 8 * n` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[]);;

(* ===== N-block generic bridges ===== *)

let NFULL_LEMMA' = prove(
  `!nfull tail. 1 <= tail /\ tail <= 16
     ==> ((16 * nfull + tail) - 1) DIV 16 = nfull /\
         (16 * nfull + tail) - 16 * (((16 * nfull + tail) - 1) DIV 16) = tail`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `((16 * nfull + tail) - 1) DIV 16 = nfull` ASSUME_TAC THENL
   [SUBGOAL_THEN `(16 * nfull + tail) - 1 = nfull * 16 + (tail - 1)` SUBST1_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    SIMP_TAC[DIV_MULT_ADD; ARITH_EQ] THEN
    SUBGOAL_THEN `(tail - 1) DIV 16 = 0` SUBST1_TAC THENL
     [SIMP_TAC[DIV_EQ_0; ARITH_EQ] THEN ASM_ARITH_TAC; ARITH_TAC];
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]);;

(* --- EL of a SUB_LIST at general start offset --- *)
let EL_SUB_LIST_GEN = prove(
 `!m (l:A list) n i. m + n <= LENGTH l /\ i < n ==> EL i (SUB_LIST(m,n) l) = EL (m+i) l`,
  INDUCT_TAC THEN REWRITE_TAC[ADD_CLAUSES] THENL
   [MESON_TAC[EL_SUB_LIST_0]; ALL_TAC] THEN
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[LENGTH] THEN
  REPEAT STRIP_TAC THENL
   [UNDISCH_TAC `SUC (m + n) <= 0` THEN ARITH_TAC;
    REWRITE_TAC[SUB_LIST_CLAUSES; EL; TL] THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]);;

(* --- block-k input bridge: the k-th 128-bit block read = bytes_to_int128   *)
(* of the k-th 16-byte sublist of the plaintext byte list. ---               *)
let BYTE_LIST_AT_BLOCK = prove(
 `!pt_in in_ptr nblk k s.
    (!i. i < 16 * nblk ==> read (memory :> bytes8 (word_add in_ptr (word i))) s = EL i pt_in) /\
    LENGTH pt_in = 16 * nblk /\ k < nblk
    ==> read (memory :> bytes128 (word_add in_ptr (word (16 * k)))) s =
        bytes_to_int128 (SUB_LIST (16 * k, 16) pt_in)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[BYTES128_TO_BYTES8_THM] THEN
  REWRITE_TAC[bytes_to_int128] THEN
  CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
  SUBGOAL_THEN
   `!j. j < 16 ==> read (memory :> bytes8 (word_add in_ptr (word (16 * k + j)))) s =
                   EL j (SUB_LIST(16*k,16) (pt_in:byte list))`
   ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `16 * k + 16 <= LENGTH(pt_in:byte list)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[EL_SUB_LIST_GEN] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `16 * k + j`) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN REFL_TAC;
    REWRITE_TAC EL_16_8_CLAUSES THEN
    FIRST_X_ASSUM(fun th -> REWRITE_TAC(map (fun i ->
      MATCH_MP th (ARITH_RULE(vsubst[mk_small_numeral i,`j:num`]`j<16`)))
      [0;1;2;3;4;5;6;7;8;9;10;11;12;13;14;15])) THEN
    REWRITE_TAC[ADD_CLAUSES]]);;

(* --- one-step unfolds of the recursive ciphertext builders --- *)
let GCM_CT_REC_STEP = prove(
  `gcm_ct_rec i 0 P ivec rks = [] /\
   gcm_ct_rec i (SUC m) P ivec rks =
     CONS (word_xor (bytes_to_int128 (SUB_LIST(i*16,16) P)) (gcm_keystream i ivec rks))
          (gcm_ct_rec (i+1) m P ivec rks)`,
  CONJ_TAC THEN GEN_REWRITE_TAC LAND_CONV [gcm_ct_rec] THEN
  REWRITE_TAC[NOT_SUC; SUC_SUB1; LET_DEF; LET_END_DEF]);;

let GCM_CT_BYTES_REC_STEP = prove(
  `gcm_ct_bytes_rec i 0 P ivec rks = [] /\
   gcm_ct_bytes_rec i (SUC m) P ivec rks =
     APPEND (int128_to_bytes (word_xor (bytes_to_int128 (SUB_LIST(i*16,16) P)) (gcm_keystream i ivec rks)))
            (gcm_ct_bytes_rec (i+1) m P ivec rks)`,
  CONJ_TAC THEN GEN_REWRITE_TAC LAND_CONV [gcm_ct_bytes_rec] THEN
  REWRITE_TAC[NOT_SUC; SUC_SUB1; LET_DEF; LET_END_DEF]);;

(* --- keystream at iterate i in terms of gcm_ctr_iter --- *)
let KS_ITER = prove(
  `!i. gcm_keystream i ivec [rk0;rk1;rk2;rk3;rk4;rk5;rk6;rk7;rk8;rk9;rk10;rk11;rk12;rk13;rk14] =
       aes256_encrypt (gcm_ctr_iter i ivec) [rk0;rk1;rk2;rk3;rk4;rk5;rk6;rk7;rk8;rk9;rk10;rk11;rk12;rk13;rk14]`,
  GEN_TAC THEN REWRITE_TAC[gcm_keystream] THEN
  REWRITE_TAC(map num_CONV [`14`;`13`;`12`;`11`;`10`;`9`;`8`;`7`;`6`;`5`;`4`;`3`;`2`;`1`]) THEN
  REWRITE_TAC[EL; HD; TL]);;

let CTR_ITER_CLAUSES = (CONJUNCTS o prove)(
  `gcm_ctr_iter 0 ivec = ivec /\
   gcm_ctr_iter 1 ivec = gcm_ctr_inc ivec /\
   gcm_ctr_iter 2 ivec = gcm_ctr_inc (gcm_ctr_inc ivec) /\
   gcm_ctr_iter 3 ivec = gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ivec)) /\
   gcm_ctr_iter 4 ivec = gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ivec))) /\
   gcm_ctr_iter 5 ivec = gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ivec)))) /\
   gcm_ctr_iter 6 ivec = gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ivec))))) /\
   gcm_ctr_iter 7 ivec = gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ivec))))))`,
  REWRITE_TAC(map num_CONV [`7`;`6`;`5`;`4`;`3`;`2`;`1`]) THEN
  REWRITE_TAC[gcm_ctr_iter]);;

(* --- small DIV/MOD helpers for the recursive EL lemma --- *)
let ADD16_DIV = prove(`!j. (j + 16) DIV 16 = j DIV 16 + 1`,
  ARITH_TAC);;
let ADD16_MOD = prove(`!j. (j + 16) MOD 16 = j MOD 16`,
  GEN_TAC THEN REWRITE_TAC[ARITH_RULE `j + 16 = 1 * 16 + j`] THEN
  SIMP_TAC[MOD_MULT_ADD]);;

(* --- byte i of the recursive full-block ciphertext byte list --- *)
let EL_GCM_CT_BYTES_REC = prove(
 `!nfull base P ivec rks i.
    i < 16 * nfull
    ==> EL i (gcm_ct_bytes_rec base nfull P ivec rks) =
        word_subword (word_xor (bytes_to_int128 (SUB_LIST(16*(base + i DIV 16),16) P))
                               (gcm_keystream (base + i DIV 16) ivec rks))
                     (8 * (i MOD 16), 8)`,
  INDUCT_TAC THENL
   [ARITH_TAC;
    REPEAT GEN_TAC THEN DISCH_TAC THEN
    REWRITE_TAC[GCM_CT_BYTES_REC_STEP] THEN
    SUBGOAL_THEN `LENGTH(int128_to_bytes (word_xor (bytes_to_int128 (SUB_LIST(base*16,16) P)) (gcm_keystream base ivec rks))) = 16`
        ASSUME_TAC THENL [REWRITE_TAC[int128_to_bytes; LENGTH] THEN ARITH_TAC; ALL_TAC] THEN
    ASM_CASES_TAC `i < 16` THENL
     [SUBGOAL_THEN `i DIV 16 = 0 /\ i MOD 16 = i` (fun th -> REWRITE_TAC[th]) THENL
       [ASM_SIMP_TAC[DIV_LT; MOD_LT]; ALL_TAC] THEN
      REWRITE_TAC[ADD_CLAUSES] THEN
      ASM_SIMP_TAC[EL_APPEND] THEN
      ASM_SIMP_TAC[EL_INT128_TO_BYTES] THEN
      REWRITE_TAC[MULT_AC];
      ASM_SIMP_TAC[EL_APPEND] THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`base + 1`; `P:byte list`; `ivec:(128)word`; `rks:int128 list`; `i - 16`]) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN SUBST1_TAC THEN
      SUBGOAL_THEN `i = (i - 16) + 16` (fun th -> GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [th]) THENL
       [ASM_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[ADD16_DIV; ADD16_MOD] THEN
      REWRITE_TAC[ARITH_RULE `(base + 1) + j = base + (j + 1)`]]]);;

let LENGTH_GCM_CT_BYTES_REC = prove(
 `!nfull base P ivec rks. LENGTH(gcm_ct_bytes_rec base nfull P ivec rks) = 16 * nfull`,
  INDUCT_TAC THEN REWRITE_TAC[GCM_CT_BYTES_REC_STEP] THEN
  ASM_REWRITE_TAC[LENGTH_APPEND; int128_to_bytes; LENGTH] THEN ARITH_TAC);;

(* --- GENERIC OUTPUT BRIDGE: N-1 full ct stores + masked tail = byte_list_at spec --- *)
let OUT_BRIDGE_GEN = prove(
 `!nfull tail pt_in ivec rks out0 out_ptr (len:int64) s.
    1 <= tail /\ tail <= 16 /\ val len = 16 * nfull + tail /\
    (!k. k < nfull
         ==> read (memory :> bytes128 (word_add out_ptr (word (16 * k)))) s =
             word_xor (bytes_to_int128 (SUB_LIST(16*k,16) pt_in)) (gcm_keystream k ivec rks)) /\
    read (memory :> bytes128 (word_add out_ptr (word (16 * nfull)))) s =
      word_or (word_and (word_xor (bytes_to_int128 (SUB_LIST(16*nfull,16) pt_in)) (gcm_keystream nfull ivec rks))
                        (word (2 EXP (8 * tail) - 1)))
              (word_and out0 (word_not (word (2 EXP (8 * tail) - 1):int128)))
    ==> byte_list_at (aes256_gcm_encrypt (val len) pt_in ivec rks) out_ptr len s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[byte_list_at] THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  REWRITE_TAC[aes256_gcm_encrypt] THEN
  MP_TAC(SPECL [`nfull:num`;`tail:num`] NFULL_LEMMA') THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT1 th; CONJUNCT2 th]) THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  COND_CASES_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `i < 16 * nfull` THENL
   [(* full-block region *)
    SUBGOAL_THEN `EL i (APPEND (gcm_ct_bytes_rec 0 nfull pt_in ivec rks)
         (SUB_LIST (0,tail) (int128_to_bytes (gcm_ctm_tail nfull tail pt_in ivec rks)))) =
       EL i (gcm_ct_bytes_rec 0 nfull pt_in ivec rks)` SUBST1_TAC THENL
     [ASM_SIMP_TAC[EL_APPEND; LENGTH_GCM_CT_BYTES_REC]; ALL_TAC] THEN
    ASM_SIMP_TAC[EL_GCM_CT_BYTES_REC; ADD_CLAUSES] THEN
    SUBGOAL_THEN `word_add out_ptr (word i):int64 =
         word_add (word_add out_ptr (word (16 * (i DIV 16)))) (word (i MOD 16))`
       SUBST1_TAC THENL
     [SUBGOAL_THEN `i = 16 * (i DIV 16) + i MOD 16` (fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV) [th]) THENL
       [MESON_TAC[DIVISION_SIMP]; ALL_TAC] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
    MP_TAC(SPECL [`word_add out_ptr (word (16 * (i DIV 16))):int64`; `s:armstate`; `i MOD 16`] BYTE8_OF_BYTES128) THEN
    ANTS_TAC THENL [REWRITE_TAC[MOD_LT_EQ; ARITH_EQ]; ALL_TAC] THEN
    DISCH_THEN(fun th -> GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [th]) THEN
    SUBGOAL_THEN `i DIV 16 < nfull` ASSUME_TAC THENL
     [ASM_SIMP_TAC[RDIV_LT_EQ; ARITH_EQ] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(fun th -> if is_forall(concl th) then MP_TAC(SPEC `i DIV 16` th) else NO_TAC) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REFL_TAC;
    (* tail region *)
    SUBGOAL_THEN `LENGTH(gcm_ct_bytes_rec 0 nfull pt_in ivec rks) = 16 * nfull` ASSUME_TAC THENL
     [REWRITE_TAC[LENGTH_GCM_CT_BYTES_REC]; ALL_TAC] THEN
    SUBGOAL_THEN `EL i (APPEND (gcm_ct_bytes_rec 0 nfull pt_in ivec rks)
         (SUB_LIST (0,tail) (int128_to_bytes (gcm_ctm_tail nfull tail pt_in ivec rks)))) =
       EL (i - 16 * nfull) (SUB_LIST (0,tail) (int128_to_bytes (gcm_ctm_tail nfull tail pt_in ivec rks)))`
       SUBST1_TAC THENL
     [ASM_SIMP_TAC[EL_APPEND]; ALL_TAC] THEN
    ABBREV_TAC `j = i - 16 * nfull` THEN
    SUBGOAL_THEN `j < tail /\ j < 16 /\ i = 16 * nfull + j` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "j" THEN ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[EL_SUB_LIST_0; EL_INT128_TO_BYTES] THEN
    REWRITE_TAC[gcm_ctm_tail; LET_DEF; LET_END_DEF] THEN
    SUBGOAL_THEN `word_add out_ptr (word (16 * nfull + j)):int64 =
         word_add (word_add out_ptr (word (16 * nfull))) (word j)` SUBST1_TAC THENL
     [CONV_TAC WORD_RULE; ALL_TAC] THEN
    MP_TAC(SPECL [`word_add out_ptr (word (16 * nfull)):int64`; `s:armstate`; `j:num`] BYTE8_OF_BYTES128) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(fun th -> GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [th]) THEN
    ASM_REWRITE_TAC[] THEN
    GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [MULT_SYM] THEN
    ASM_SIMP_TAC[MASK_BYTE_OUT] THEN
    REWRITE_TAC[MULT_SYM] THEN
    REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_SUBWORD; BIT_WORD_AND; BIT_MASK_WORD; DIMINDEX_128] THEN
    X_GEN_TAC `b:num` THEN STRIP_TAC THEN EQ_TAC THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]);;

(* --- input block read directly from byte_list_at (for the pre-impl) --- *)
let INPUT_BLOCK_BL = prove(
 `!pt_in in_ptr nblk k s.
    byte_list_at pt_in in_ptr (word (16 * nblk)) s /\ LENGTH pt_in = 16 * nblk /\
    val(word(16 * nblk):int64) = 16 * nblk /\ k < nblk
    ==> read (memory :> bytes128 (word_add in_ptr (word (16 * k)))) s =
        bytes_to_int128 (SUB_LIST (16 * k, 16) pt_in)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC BYTE_LIST_AT_BLOCK THEN
  EXISTS_TAC `nblk:num` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(fun th -> if free_in `byte_list_at` (concl th) then
     MP_TAC(REWRITE_RULE[byte_list_at] th) else NO_TAC) THEN
  ASM_REWRITE_TAC[]);;

(* --- all 8 input-block reads from a 128-byte byte_list_at (for the dispatch pre-impl) --- *)
let INPUT_READS_128 = prove(
 `!pt_in in_ptr s.
    byte_list_at pt_in in_ptr (word 128) s /\ LENGTH pt_in = 128
   ==> read (memory :> bytes128 in_ptr) s = bytes_to_int128 (SUB_LIST (0,16) pt_in) /\
       read (memory :> bytes128 (word_add in_ptr (word 16))) s = bytes_to_int128 (SUB_LIST (16,16) pt_in) /\
       read (memory :> bytes128 (word_add in_ptr (word 32))) s = bytes_to_int128 (SUB_LIST (32,16) pt_in) /\
       read (memory :> bytes128 (word_add in_ptr (word 48))) s = bytes_to_int128 (SUB_LIST (48,16) pt_in) /\
       read (memory :> bytes128 (word_add in_ptr (word 64))) s = bytes_to_int128 (SUB_LIST (64,16) pt_in) /\
       read (memory :> bytes128 (word_add in_ptr (word 80))) s = bytes_to_int128 (SUB_LIST (80,16) pt_in) /\
       read (memory :> bytes128 (word_add in_ptr (word 96))) s = bytes_to_int128 (SUB_LIST (96,16) pt_in) /\
       read (memory :> bytes128 (word_add in_ptr (word 112))) s = bytes_to_int128 (SUB_LIST (112,16) pt_in)`,
  let INB k = (MP_TAC(ISPECL [`pt_in:byte list`;`in_ptr:int64`;`8`;mk_small_numeral k;`s:armstate`] INPUT_BLOCK_BL) THEN
               CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[WORD_ADD_0] THEN
               ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ARITH_TAC; DISCH_THEN ACCEPT_TAC]) in
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `val(word 128:int64) = 16 * 8` ASSUME_TAC THENL
   [CONV_TAC WORD_REDUCE_CONV THEN ARITH_TAC; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL [INB 0; INB 1; INB 2; INB 3; INB 4; INB 5; INB 6; INB 7]);;

(* --- gcm_final_xi unfold for nonempty input --- *)
let GCM_FINAL_XI_UNFOLD = prove(
 `!len pt_in ivec rks xi h. ~(len = 0)
   ==> gcm_final_xi len pt_in ivec rks xi h =
       word_reversefields 8
         (ghash_polyval_acc h (word_reversefields 8 xi)
            (MAP (\b. word_reversefields 8 b) (gcm_ghash_blocks len pt_in ivec rks)))`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[gcm_final_xi]);;

(* ===== N-block bridges already loaded from gcm_nblock_bridges content ===== *)

(* ===== GHASH_BLOCKS_1..8 ===== *)

let GHASH_BLOCKS_1 = prove(
  `!tail pt_in ivec rks. 1 <= tail /\ tail <= 16
    ==> gcm_ghash_blocks (16 * 0 + tail) pt_in ivec rks =
        [ word_and (word_xor (bytes_to_int128 (SUB_LIST(0,16) pt_in)) (gcm_keystream 0 ivec rks)) (word (2 EXP (8 * tail) - 1)) ]`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[gcm_ghash_blocks] THEN
  MP_TAC(SPECL [`0`;`tail:num`] NFULL_LEMMA') THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT1 th; CONJUNCT2 th]) THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  REWRITE_TAC[GCM_CT_REC_STEP] THEN
  REWRITE_TAC[gcm_ctm_tail; LET_DEF; LET_END_DEF; APPEND] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let GHASH_BLOCKS_2 = prove(
  `!tail pt_in ivec rks. 1 <= tail /\ tail <= 16
    ==> gcm_ghash_blocks (16 * 1 + tail) pt_in ivec rks =
        [ word_xor (bytes_to_int128 (SUB_LIST(0,16) pt_in)) (gcm_keystream 0 ivec rks);
          word_and (word_xor (bytes_to_int128 (SUB_LIST(16,16) pt_in)) (gcm_keystream 1 ivec rks)) (word (2 EXP (8 * tail) - 1)) ]`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[gcm_ghash_blocks] THEN
  MP_TAC(SPECL [`1`;`tail:num`] NFULL_LEMMA') THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT1 th; CONJUNCT2 th]) THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  REWRITE_TAC(map num_CONV [`1`]) THEN
  REWRITE_TAC[GCM_CT_REC_STEP] THEN
  REWRITE_TAC[gcm_ctm_tail; LET_DEF; LET_END_DEF; APPEND] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let GHASH_BLOCKS_3 = prove(
  `!tail pt_in ivec rks. 1 <= tail /\ tail <= 16
    ==> gcm_ghash_blocks (16 * 2 + tail) pt_in ivec rks =
        [ word_xor (bytes_to_int128 (SUB_LIST(0,16) pt_in)) (gcm_keystream 0 ivec rks);
          word_xor (bytes_to_int128 (SUB_LIST(16,16) pt_in)) (gcm_keystream 1 ivec rks);
          word_and (word_xor (bytes_to_int128 (SUB_LIST(32,16) pt_in)) (gcm_keystream 2 ivec rks)) (word (2 EXP (8 * tail) - 1)) ]`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[gcm_ghash_blocks] THEN
  MP_TAC(SPECL [`2`;`tail:num`] NFULL_LEMMA') THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT1 th; CONJUNCT2 th]) THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  REWRITE_TAC(map num_CONV [`2`;`1`]) THEN
  REWRITE_TAC[GCM_CT_REC_STEP] THEN
  REWRITE_TAC[gcm_ctm_tail; LET_DEF; LET_END_DEF; APPEND] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let GHASH_BLOCKS_4 = prove(
  `!tail pt_in ivec rks. 1 <= tail /\ tail <= 16
    ==> gcm_ghash_blocks (16 * 3 + tail) pt_in ivec rks =
        [ word_xor (bytes_to_int128 (SUB_LIST(0,16) pt_in)) (gcm_keystream 0 ivec rks);
          word_xor (bytes_to_int128 (SUB_LIST(16,16) pt_in)) (gcm_keystream 1 ivec rks);
          word_xor (bytes_to_int128 (SUB_LIST(32,16) pt_in)) (gcm_keystream 2 ivec rks);
          word_and (word_xor (bytes_to_int128 (SUB_LIST(48,16) pt_in)) (gcm_keystream 3 ivec rks)) (word (2 EXP (8 * tail) - 1)) ]`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[gcm_ghash_blocks] THEN
  MP_TAC(SPECL [`3`;`tail:num`] NFULL_LEMMA') THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT1 th; CONJUNCT2 th]) THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  REWRITE_TAC(map num_CONV [`3`;`2`;`1`]) THEN
  REWRITE_TAC[GCM_CT_REC_STEP] THEN
  REWRITE_TAC[gcm_ctm_tail; LET_DEF; LET_END_DEF; APPEND] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let GHASH_BLOCKS_5 = prove(
  `!tail pt_in ivec rks. 1 <= tail /\ tail <= 16
    ==> gcm_ghash_blocks (16 * 4 + tail) pt_in ivec rks =
        [ word_xor (bytes_to_int128 (SUB_LIST(0,16) pt_in)) (gcm_keystream 0 ivec rks);
          word_xor (bytes_to_int128 (SUB_LIST(16,16) pt_in)) (gcm_keystream 1 ivec rks);
          word_xor (bytes_to_int128 (SUB_LIST(32,16) pt_in)) (gcm_keystream 2 ivec rks);
          word_xor (bytes_to_int128 (SUB_LIST(48,16) pt_in)) (gcm_keystream 3 ivec rks);
          word_and (word_xor (bytes_to_int128 (SUB_LIST(64,16) pt_in)) (gcm_keystream 4 ivec rks)) (word (2 EXP (8 * tail) - 1)) ]`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[gcm_ghash_blocks] THEN
  MP_TAC(SPECL [`4`;`tail:num`] NFULL_LEMMA') THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT1 th; CONJUNCT2 th]) THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  REWRITE_TAC(map num_CONV [`4`;`3`;`2`;`1`]) THEN
  REWRITE_TAC[GCM_CT_REC_STEP] THEN
  REWRITE_TAC[gcm_ctm_tail; LET_DEF; LET_END_DEF; APPEND] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let GHASH_BLOCKS_6 = prove(
  `!tail pt_in ivec rks. 1 <= tail /\ tail <= 16
    ==> gcm_ghash_blocks (16 * 5 + tail) pt_in ivec rks =
        [ word_xor (bytes_to_int128 (SUB_LIST(0,16) pt_in)) (gcm_keystream 0 ivec rks);
          word_xor (bytes_to_int128 (SUB_LIST(16,16) pt_in)) (gcm_keystream 1 ivec rks);
          word_xor (bytes_to_int128 (SUB_LIST(32,16) pt_in)) (gcm_keystream 2 ivec rks);
          word_xor (bytes_to_int128 (SUB_LIST(48,16) pt_in)) (gcm_keystream 3 ivec rks);
          word_xor (bytes_to_int128 (SUB_LIST(64,16) pt_in)) (gcm_keystream 4 ivec rks);
          word_and (word_xor (bytes_to_int128 (SUB_LIST(80,16) pt_in)) (gcm_keystream 5 ivec rks)) (word (2 EXP (8 * tail) - 1)) ]`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[gcm_ghash_blocks] THEN
  MP_TAC(SPECL [`5`;`tail:num`] NFULL_LEMMA') THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT1 th; CONJUNCT2 th]) THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  REWRITE_TAC(map num_CONV [`5`;`4`;`3`;`2`;`1`]) THEN
  REWRITE_TAC[GCM_CT_REC_STEP] THEN
  REWRITE_TAC[gcm_ctm_tail; LET_DEF; LET_END_DEF; APPEND] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let GHASH_BLOCKS_7 = prove(
  `!tail pt_in ivec rks. 1 <= tail /\ tail <= 16
    ==> gcm_ghash_blocks (16 * 6 + tail) pt_in ivec rks =
        [ word_xor (bytes_to_int128 (SUB_LIST(0,16) pt_in)) (gcm_keystream 0 ivec rks);
          word_xor (bytes_to_int128 (SUB_LIST(16,16) pt_in)) (gcm_keystream 1 ivec rks);
          word_xor (bytes_to_int128 (SUB_LIST(32,16) pt_in)) (gcm_keystream 2 ivec rks);
          word_xor (bytes_to_int128 (SUB_LIST(48,16) pt_in)) (gcm_keystream 3 ivec rks);
          word_xor (bytes_to_int128 (SUB_LIST(64,16) pt_in)) (gcm_keystream 4 ivec rks);
          word_xor (bytes_to_int128 (SUB_LIST(80,16) pt_in)) (gcm_keystream 5 ivec rks);
          word_and (word_xor (bytes_to_int128 (SUB_LIST(96,16) pt_in)) (gcm_keystream 6 ivec rks)) (word (2 EXP (8 * tail) - 1)) ]`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[gcm_ghash_blocks] THEN
  MP_TAC(SPECL [`6`;`tail:num`] NFULL_LEMMA') THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT1 th; CONJUNCT2 th]) THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  REWRITE_TAC(map num_CONV [`6`;`5`;`4`;`3`;`2`;`1`]) THEN
  REWRITE_TAC[GCM_CT_REC_STEP] THEN
  REWRITE_TAC[gcm_ctm_tail; LET_DEF; LET_END_DEF; APPEND] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let GHASH_BLOCKS_8 = prove(
  `!tail pt_in ivec rks. 1 <= tail /\ tail <= 16
    ==> gcm_ghash_blocks (16 * 7 + tail) pt_in ivec rks =
        [ word_xor (bytes_to_int128 (SUB_LIST(0,16) pt_in)) (gcm_keystream 0 ivec rks);
          word_xor (bytes_to_int128 (SUB_LIST(16,16) pt_in)) (gcm_keystream 1 ivec rks);
          word_xor (bytes_to_int128 (SUB_LIST(32,16) pt_in)) (gcm_keystream 2 ivec rks);
          word_xor (bytes_to_int128 (SUB_LIST(48,16) pt_in)) (gcm_keystream 3 ivec rks);
          word_xor (bytes_to_int128 (SUB_LIST(64,16) pt_in)) (gcm_keystream 4 ivec rks);
          word_xor (bytes_to_int128 (SUB_LIST(80,16) pt_in)) (gcm_keystream 5 ivec rks);
          word_xor (bytes_to_int128 (SUB_LIST(96,16) pt_in)) (gcm_keystream 6 ivec rks);
          word_and (word_xor (bytes_to_int128 (SUB_LIST(112,16) pt_in)) (gcm_keystream 7 ivec rks)) (word (2 EXP (8 * tail) - 1)) ]`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[gcm_ghash_blocks] THEN
  MP_TAC(SPECL [`7`;`tail:num`] NFULL_LEMMA') THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT1 th; CONJUNCT2 th]) THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  REWRITE_TAC(map num_CONV [`7`;`6`;`5`;`4`;`3`;`2`;`1`]) THEN
  REWRITE_TAC[GCM_CT_REC_STEP] THEN
  REWRITE_TAC[gcm_ctm_tail; LET_DEF; LET_END_DEF; APPEND] THEN
  CONV_TAC NUM_REDUCE_CONV);;

(* ===== abstract band lemmas 0,1,2..8 ===== *)

let AES256_GCM_ENCRYPT_LT_0BLOCK_ABS = prove(
 `!in_ptr out_ptr xi_ptr ivec_ptr key_ptr htable_ptr (pt_in:byte list) (co0:(128)word) (co1:(128)word) (co2:(128)word) (co3:(128)word) (co4:(128)word) (co5:(128)word) (co6:(128)word) (co7:(128)word) (ivec:(128)word) (rk0:(128)word) (rk1:(128)word) (rk2:(128)word) (rk3:(128)word) (rk4:(128)word) (rk5:(128)word) (rk6:(128)word) (rk7:(128)word) (rk8:(128)word) (rk9:(128)word) (rk10:(128)word) (rk11:(128)word) (rk12:(128)word) (rk13:(128)word) (rk14:(128)word) (xi:(128)word) (h:(128)word) (h1k:(128)word) (h3k:(128)word) (h5k:(128)word) (h7k:(128)word) (q18i:(128)word) (len:int64) stackptr pc.
    val (len:int64) = 0 /\ LENGTH pt_in = 128 /\
    aligned 16 stackptr /\
    nonoverlapping (word pc,4600) (in_ptr:int64,128) /\
    nonoverlapping (word pc,4600) (out_ptr:int64,128) /\
    nonoverlapping (word pc,4600) (xi_ptr:int64,16) /\
    nonoverlapping (word pc,4600) (ivec_ptr:int64,16) /\
    nonoverlapping (word pc,4600) (key_ptr:int64,240) /\
    nonoverlapping (word pc,4600) (htable_ptr:int64,256) /\
    nonoverlapping (word pc,4600) (stackptr:int64,80) /\
    nonoverlapping (in_ptr,128) (out_ptr,128) /\
    nonoverlapping (in_ptr,128) (xi_ptr,16) /\
    nonoverlapping (in_ptr,128) (ivec_ptr,16) /\
    nonoverlapping (out_ptr,128) (xi_ptr,16) /\
    nonoverlapping (out_ptr,128) (ivec_ptr,16) /\
    nonoverlapping (xi_ptr,16) (ivec_ptr,16) /\
    nonoverlapping (key_ptr,240) (out_ptr,128) /\
    nonoverlapping (key_ptr,240) (xi_ptr,16) /\
    nonoverlapping (key_ptr,240) (ivec_ptr,16) /\
    nonoverlapping (htable_ptr,256) (out_ptr,128) /\
    nonoverlapping (htable_ptr,256) (xi_ptr,16) /\
    nonoverlapping (htable_ptr,256) (ivec_ptr,16) /\
    nonoverlapping (stackptr,80) (out_ptr,128) /\
    nonoverlapping (stackptr,80) (xi_ptr,16) /\
    nonoverlapping (stackptr,80) (ivec_ptr,16) /\
    nonoverlapping (stackptr,80) (in_ptr,128) /\
    nonoverlapping (stackptr,80) (key_ptr,240) /\
    nonoverlapping (stackptr,80) (htable_ptr,256) /\
    nonoverlapping (ivec_ptr,16) (word pc,4600) /\
    nonoverlapping (xi_ptr,16) (word pc,4600) /\
    nonoverlapping (out_ptr,128) (word pc,4600)
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) aes256_gcm_mc /\
           read PC s = word pc /\
           C_ARGUMENTS [in_ptr; word (8 * val len); out_ptr; xi_ptr;
                        ivec_ptr; key_ptr; htable_ptr] s /\
           read SP s = word_add stackptr (word 80) /\
           read Q18 s = q18i /\
           byte_list_at pt_in in_ptr (word 128) s /\
           read (memory :> bytes128 out_ptr) s = co0 /\
           read (memory :> bytes128 (word_add out_ptr (word 16))) s = co1 /\
           read (memory :> bytes128 (word_add out_ptr (word 32))) s = co2 /\
           read (memory :> bytes128 (word_add out_ptr (word 48))) s = co3 /\
           read (memory :> bytes128 (word_add out_ptr (word 64))) s = co4 /\
           read (memory :> bytes128 (word_add out_ptr (word 80))) s = co5 /\
           read (memory :> bytes128 (word_add out_ptr (word 96))) s = co6 /\
           read (memory :> bytes128 (word_add out_ptr (word 112))) s = co7 /\
           read (memory :> bytes128 ivec_ptr) s = ivec /\
           read (memory :> bytes128 (word_add key_ptr (word 0))) s = rk0 /\
           read (memory :> bytes128 (word_add key_ptr (word 16))) s = rk1 /\
           read (memory :> bytes128 (word_add key_ptr (word 32))) s = rk2 /\
           read (memory :> bytes128 (word_add key_ptr (word 48))) s = rk3 /\
           read (memory :> bytes128 (word_add key_ptr (word 64))) s = rk4 /\
           read (memory :> bytes128 (word_add key_ptr (word 80))) s = rk5 /\
           read (memory :> bytes128 (word_add key_ptr (word 96))) s = rk6 /\
           read (memory :> bytes128 (word_add key_ptr (word 112))) s = rk7 /\
           read (memory :> bytes128 (word_add key_ptr (word 128))) s = rk8 /\
           read (memory :> bytes128 (word_add key_ptr (word 144))) s = rk9 /\
           read (memory :> bytes128 (word_add key_ptr (word 160))) s = rk10 /\
           read (memory :> bytes128 (word_add key_ptr (word 176))) s = rk11 /\
           read (memory :> bytes128 (word_add key_ptr (word 192))) s = rk12 /\
           read (memory :> bytes128 (word_add key_ptr (word 208))) s = rk13 /\
           read (memory :> bytes128 (word_add key_ptr (word 224))) s = rk14 /\
           read (memory :> bytes128 xi_ptr) s = xi /\
           read (memory :> bytes128 htable_ptr) s = word_swaphalves128 h /\
           read (memory :> bytes128 (word_add htable_ptr (word 16))) s = h1k /\
           read (memory :> bytes128 (word_add htable_ptr (word 32))) s = word_swaphalves128 (polyval_dot h h) /\
           read (memory :> bytes128 (word_add htable_ptr (word 48))) s = word_swaphalves128 (polyval_dot h (polyval_dot h h)) /\
           read (memory :> bytes128 (word_add htable_ptr (word 64))) s = h3k /\
           read (memory :> bytes128 (word_add htable_ptr (word 80))) s = word_swaphalves128 (polyval_dot (polyval_dot h h) (polyval_dot h h)) /\
           read (memory :> bytes128 (word_add htable_ptr (word 96))) s = word_swaphalves128 (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) /\
           read (memory :> bytes128 (word_add htable_ptr (word 112))) s = h5k /\
           read (memory :> bytes128 (word_add htable_ptr (word 128))) s = word_swaphalves128 (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) h) /\
           read (memory :> bytes128 (word_add htable_ptr (word 144))) s = word_swaphalves128 (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) h) h) /\
           read (memory :> bytes128 (word_add htable_ptr (word 160))) s = h7k /\
           read (memory :> bytes128 (word_add htable_ptr (word 176))) s = word_swaphalves128 (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) h) h) h) /\
           word_subword h1k (0,64):(64)word = karatsuba_mid h /\
           word_subword h1k (64,64):(64)word = karatsuba_mid (polyval_dot h h) /\
           word_subword h3k (0,64):(64)word = karatsuba_mid (polyval_dot h (polyval_dot h h)) /\
           word_subword h3k (64,64):(64)word = karatsuba_mid (polyval_dot (polyval_dot h h) (polyval_dot h h)) /\
           word_subword h5k (0,64):(64)word = karatsuba_mid (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) /\
           word_subword h5k (64,64):(64)word = karatsuba_mid (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) h) /\
           word_subword h7k (0,64):(64)word = karatsuba_mid (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) h) h) /\
           word_subword h7k (64,64):(64)word = karatsuba_mid (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) h) h) h))
      (\s. read PC s = word(pc + (if val(len:int64) = 0 then 4596 else 4588)) /\
           read X0 s = len /\
           byte_list_at (aes256_gcm_encrypt (val len) pt_in ivec [rk0;rk1;rk2;rk3;rk4;rk5;rk6;rk7;rk8;rk9;rk10;rk11;rk12;rk13;rk14])
                        out_ptr len s /\
           read (memory :> bytes128 xi_ptr) s =
             gcm_final_xi (val len) pt_in ivec [rk0;rk1;rk2;rk3;rk4;rk5;rk6;rk7;rk8;rk9;rk10;rk11;rk12;rk13;rk14] xi h)
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [memory :> bytes(out_ptr,128);
                  memory :> bytes(xi_ptr,16);
                  memory :> bytes(ivec_ptr,16)] ,,
       MAYCHANGE [SP] ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes64 stackptr;
                  memory :> bytes64 (word_add stackptr (word 8));
                  memory :> bytes64 (word_add stackptr (word 16));
                  memory :> bytes64 (word_add stackptr (word 24));
                  memory :> bytes64 (word_add stackptr (word 32));
                  memory :> bytes64 (word_add stackptr (word 40));
                  memory :> bytes64 (word_add stackptr (word 48));
                  memory :> bytes64 (word_add stackptr (word 56));
                  memory :> bytes64 (word_add stackptr (word 64));
                  memory :> bytes64 (word_add stackptr (word 72))])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `len:int64 = word 0` SUBST_ALL_TAC THENL
   [REWRITE_TAC[GSYM VAL_EQ_0] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[VAL_WORD_0; aes256_gcm_encrypt; gcm_final_xi; byte_list_at; VAL_WORD_0;
              LET_DEF; LET_END_DEF] THEN
  MP_TAC(ISPECL
   [`in_ptr:int64`;`out_ptr:int64`;`xi_ptr:int64`;`ivec_ptr:int64`;`key_ptr:int64`;`htable_ptr:int64`;
    `co0:(128)word`;`xi:(128)word`;`stackptr:int64`;`pc:num`]
   AES256_GCM_ENCRYPT_LT_0BLOCK_CONCRETE) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST [NONOVERLAPPING_TAC; ASM_REWRITE_TAC[]]); ALL_TAC] THEN
  DISCH_THEN(fun band ->
    MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN
    EXISTS_TAC (rand(concl band)) THEN CONJ_TAC THENL
     [REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN SUBSUMED_MAYCHANGE_TAC; ALL_TAC] THEN
    MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN
    EXISTS_TAC (rand(rator(concl band))) THEN CONJ_TAC THENL
     [GEN_TAC THEN REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
      MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN
      EXISTS_TAC (rand(rator(rator(concl band)))) THEN CONJ_TAC THENL
       [GEN_TAC THEN REWRITE_TAC[] THEN STRIP_TAC THEN
        RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN ASM_REWRITE_TAC[];
        ACCEPT_TAC band]]));;

let AES256_GCM_ENCRYPT_LT_1BLOCK_ABS = prove(
 `!in_ptr out_ptr xi_ptr ivec_ptr key_ptr htable_ptr (pt_in:byte list) (co0:(128)word) (co1:(128)word) (co2:(128)word) (co3:(128)word) (co4:(128)word) (co5:(128)word) (co6:(128)word) (co7:(128)word) (ivec:(128)word) (rk0:(128)word) (rk1:(128)word) (rk2:(128)word) (rk3:(128)word) (rk4:(128)word) (rk5:(128)word) (rk6:(128)word) (rk7:(128)word) (rk8:(128)word) (rk9:(128)word) (rk10:(128)word) (rk11:(128)word) (rk12:(128)word) (rk13:(128)word) (rk14:(128)word) (xi:(128)word) (h:(128)word) (h1k:(128)word) (h3k:(128)word) (h5k:(128)word) (h7k:(128)word) (q18i:(128)word) (len:int64) stackptr pc.
    0 + 1 <= val len /\ val len <= 16 /\ LENGTH pt_in = 128 /\
    aligned 16 stackptr /\
    nonoverlapping (word pc,4600) (in_ptr:int64,128) /\
    nonoverlapping (word pc,4600) (out_ptr:int64,128) /\
    nonoverlapping (word pc,4600) (xi_ptr:int64,16) /\
    nonoverlapping (word pc,4600) (ivec_ptr:int64,16) /\
    nonoverlapping (word pc,4600) (key_ptr:int64,240) /\
    nonoverlapping (word pc,4600) (htable_ptr:int64,256) /\
    nonoverlapping (word pc,4600) (stackptr:int64,80) /\
    nonoverlapping (in_ptr,128) (out_ptr,128) /\
    nonoverlapping (in_ptr,128) (xi_ptr,16) /\
    nonoverlapping (in_ptr,128) (ivec_ptr,16) /\
    nonoverlapping (out_ptr,128) (xi_ptr,16) /\
    nonoverlapping (out_ptr,128) (ivec_ptr,16) /\
    nonoverlapping (xi_ptr,16) (ivec_ptr,16) /\
    nonoverlapping (key_ptr,240) (out_ptr,128) /\
    nonoverlapping (key_ptr,240) (xi_ptr,16) /\
    nonoverlapping (key_ptr,240) (ivec_ptr,16) /\
    nonoverlapping (htable_ptr,256) (out_ptr,128) /\
    nonoverlapping (htable_ptr,256) (xi_ptr,16) /\
    nonoverlapping (htable_ptr,256) (ivec_ptr,16) /\
    nonoverlapping (stackptr,80) (out_ptr,128) /\
    nonoverlapping (stackptr,80) (xi_ptr,16) /\
    nonoverlapping (stackptr,80) (ivec_ptr,16) /\
    nonoverlapping (stackptr,80) (in_ptr,128) /\
    nonoverlapping (stackptr,80) (key_ptr,240) /\
    nonoverlapping (stackptr,80) (htable_ptr,256) /\
    nonoverlapping (ivec_ptr,16) (word pc,4600) /\
    nonoverlapping (xi_ptr,16) (word pc,4600) /\
    nonoverlapping (out_ptr,128) (word pc,4600)
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) aes256_gcm_mc /\
           read PC s = word pc /\
           C_ARGUMENTS [in_ptr; word (8 * val len); out_ptr; xi_ptr;
                        ivec_ptr; key_ptr; htable_ptr] s /\
           read SP s = word_add stackptr (word 80) /\
           read Q18 s = q18i /\
           byte_list_at pt_in in_ptr (word 128) s /\
           read (memory :> bytes128 out_ptr) s = co0 /\
           read (memory :> bytes128 (word_add out_ptr (word 16))) s = co1 /\
           read (memory :> bytes128 (word_add out_ptr (word 32))) s = co2 /\
           read (memory :> bytes128 (word_add out_ptr (word 48))) s = co3 /\
           read (memory :> bytes128 (word_add out_ptr (word 64))) s = co4 /\
           read (memory :> bytes128 (word_add out_ptr (word 80))) s = co5 /\
           read (memory :> bytes128 (word_add out_ptr (word 96))) s = co6 /\
           read (memory :> bytes128 (word_add out_ptr (word 112))) s = co7 /\
           read (memory :> bytes128 ivec_ptr) s = ivec /\
           read (memory :> bytes128 (word_add key_ptr (word 0))) s = rk0 /\
           read (memory :> bytes128 (word_add key_ptr (word 16))) s = rk1 /\
           read (memory :> bytes128 (word_add key_ptr (word 32))) s = rk2 /\
           read (memory :> bytes128 (word_add key_ptr (word 48))) s = rk3 /\
           read (memory :> bytes128 (word_add key_ptr (word 64))) s = rk4 /\
           read (memory :> bytes128 (word_add key_ptr (word 80))) s = rk5 /\
           read (memory :> bytes128 (word_add key_ptr (word 96))) s = rk6 /\
           read (memory :> bytes128 (word_add key_ptr (word 112))) s = rk7 /\
           read (memory :> bytes128 (word_add key_ptr (word 128))) s = rk8 /\
           read (memory :> bytes128 (word_add key_ptr (word 144))) s = rk9 /\
           read (memory :> bytes128 (word_add key_ptr (word 160))) s = rk10 /\
           read (memory :> bytes128 (word_add key_ptr (word 176))) s = rk11 /\
           read (memory :> bytes128 (word_add key_ptr (word 192))) s = rk12 /\
           read (memory :> bytes128 (word_add key_ptr (word 208))) s = rk13 /\
           read (memory :> bytes128 (word_add key_ptr (word 224))) s = rk14 /\
           read (memory :> bytes128 xi_ptr) s = xi /\
           read (memory :> bytes128 htable_ptr) s = word_swaphalves128 h /\
           read (memory :> bytes128 (word_add htable_ptr (word 16))) s = h1k /\
           read (memory :> bytes128 (word_add htable_ptr (word 32))) s = word_swaphalves128 (polyval_dot h h) /\
           read (memory :> bytes128 (word_add htable_ptr (word 48))) s = word_swaphalves128 (polyval_dot h (polyval_dot h h)) /\
           read (memory :> bytes128 (word_add htable_ptr (word 64))) s = h3k /\
           read (memory :> bytes128 (word_add htable_ptr (word 80))) s = word_swaphalves128 (polyval_dot (polyval_dot h h) (polyval_dot h h)) /\
           read (memory :> bytes128 (word_add htable_ptr (word 96))) s = word_swaphalves128 (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) /\
           read (memory :> bytes128 (word_add htable_ptr (word 112))) s = h5k /\
           read (memory :> bytes128 (word_add htable_ptr (word 128))) s = word_swaphalves128 (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) h) /\
           read (memory :> bytes128 (word_add htable_ptr (word 144))) s = word_swaphalves128 (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) h) h) /\
           read (memory :> bytes128 (word_add htable_ptr (word 160))) s = h7k /\
           read (memory :> bytes128 (word_add htable_ptr (word 176))) s = word_swaphalves128 (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) h) h) h) /\
           word_subword h1k (0,64):(64)word = karatsuba_mid h /\
           word_subword h1k (64,64):(64)word = karatsuba_mid (polyval_dot h h) /\
           word_subword h3k (0,64):(64)word = karatsuba_mid (polyval_dot h (polyval_dot h h)) /\
           word_subword h3k (64,64):(64)word = karatsuba_mid (polyval_dot (polyval_dot h h) (polyval_dot h h)) /\
           word_subword h5k (0,64):(64)word = karatsuba_mid (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) /\
           word_subword h5k (64,64):(64)word = karatsuba_mid (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) h) /\
           word_subword h7k (0,64):(64)word = karatsuba_mid (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) h) h) /\
           word_subword h7k (64,64):(64)word = karatsuba_mid (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) h) h) h))
      (\s. read PC s = word(pc + (if val(len:int64) = 0 then 4596 else 4588)) /\
           read X0 s = len /\
           byte_list_at (aes256_gcm_encrypt (val len) pt_in ivec [rk0;rk1;rk2;rk3;rk4;rk5;rk6;rk7;rk8;rk9;rk10;rk11;rk12;rk13;rk14])
                        out_ptr len s /\
           read (memory :> bytes128 xi_ptr) s =
             gcm_final_xi (val len) pt_in ivec [rk0;rk1;rk2;rk3;rk4;rk5;rk6;rk7;rk8;rk9;rk10;rk11;rk12;rk13;rk14] xi h)
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [memory :> bytes(out_ptr,128);
                  memory :> bytes(xi_ptr,16);
                  memory :> bytes(ivec_ptr,16)] ,,
       MAYCHANGE [SP] ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes64 stackptr;
                  memory :> bytes64 (word_add stackptr (word 8));
                  memory :> bytes64 (word_add stackptr (word 16));
                  memory :> bytes64 (word_add stackptr (word 24));
                  memory :> bytes64 (word_add stackptr (word 32));
                  memory :> bytes64 (word_add stackptr (word 40));
                  memory :> bytes64 (word_add stackptr (word 48));
                  memory :> bytes64 (word_add stackptr (word 56));
                  memory :> bytes64 (word_add stackptr (word 64));
                  memory :> bytes64 (word_add stackptr (word 72))])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(val(len:int64) = 0) /\ val len = 16 * 0 + (val len - 0)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `byte_len = val(len:int64) - 0` THEN
  SUBGOAL_THEN `1 <= byte_len /\ byte_len <= 16` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "byte_len" THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(if val(len:int64)=0 then 4596 else 4588) = 4588` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `8 * val(len:int64) = 0 + 8 * byte_len` ASSUME_TAC THENL
   [EXPAND_TAC "byte_len" THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL
   [`in_ptr:int64`;
    `out_ptr:int64`;
    `xi_ptr:int64`;
    `ivec_ptr:int64`;
    `key_ptr:int64`;
    `htable_ptr:int64`;
    `bytes_to_int128 (SUB_LIST(0,16) pt_in)`;
    `co0:(128)word`;
    `ivec:(128)word`;
    `rk0:(128)word`;
    `rk1:(128)word`;
    `rk2:(128)word`;
    `rk3:(128)word`;
    `rk4:(128)word`;
    `rk5:(128)word`;
    `rk6:(128)word`;
    `rk7:(128)word`;
    `rk8:(128)word`;
    `rk9:(128)word`;
    `rk10:(128)word`;
    `rk11:(128)word`;
    `rk12:(128)word`;
    `rk13:(128)word`;
    `rk14:(128)word`;
    `xi:(128)word`;
    `h:(128)word`;
    `h1k:(128)word`;
    `byte_len:num`;
    `stackptr:int64`;
    `pc:num`]
   AES256_GCM_ENCRYPT_LT_1BLOCK_CONCRETE) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST [ASM_ARITH_TAC; NONOVERLAPPING_TAC; ASM_REWRITE_TAC[]]);
    ALL_TAC] THEN
  DISCH_THEN(fun band ->
    (* The CONCRETE postcondition is phrased with the upstream aes256_encrypt,
       matching the spec bridge (KS_ITER / OUT_BRIDGE_GEN, also aes256_encrypt-
       based) directly. *)
    MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN
    EXISTS_TAC (rand(concl band)) THEN CONJ_TAC THENL
     [REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN SUBSUMED_MAYCHANGE_TAC; ALL_TAC] THEN
    MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN
    EXISTS_TAC (rand(rator(concl band))) THEN CONJ_TAC THENL
     [GEN_TAC THEN REWRITE_TAC[] THEN CONV_TAC(LAND_CONV(TOP_DEPTH_CONV let_CONV)) THEN
      STRIP_TAC THEN REPEAT CONJ_TAC THENL
       [ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[] THEN SUBGOAL_THEN `byte_len = val(len:int64)` SUBST1_TAC THENL
         [EXPAND_TAC "byte_len" THEN ASM_ARITH_TAC; REWRITE_TAC[WORD_VAL]];
        MATCH_MP_TAC OUT_BRIDGE_GEN THEN
        MAP_EVERY EXISTS_TAC [`0`; `byte_len:num`; `co0:(128)word`] THEN
        REWRITE_TAC[KS_ITER] THEN REWRITE_TAC CTR_ITER_CLAUSES THEN
        REPEAT CONJ_TAC THENL
         [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]; EXPAND_TAC "byte_len" THEN ASM_ARITH_TAC;
          GEN_TAC THEN REWRITE_TAC[ARITH_RULE `~(k < 0)`];
          CONV_TAC NUM_REDUCE_CONV THEN
          REWRITE_TAC[WORD_ADD_0] THEN ASM_REWRITE_TAC[]];
        ASM_REWRITE_TAC[] THEN
        ASM_SIMP_TAC[GCM_FINAL_XI_UNFOLD; ARITH_RULE `1 <= byte_len ==> ~(16 * 0 + byte_len = 0)`] THEN
        MP_TAC(SPECL [`byte_len:num`;`pt_in:byte list`;`ivec:(128)word`;`[rk0;rk1;rk2;rk3;rk4;rk5;rk6;rk7;rk8;rk9;rk10;rk11;rk12;rk13;rk14]:int128 list`] GHASH_BLOCKS_1) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
        REWRITE_TAC[MAP] THEN REWRITE_TAC[KS_ITER] THEN REWRITE_TAC CTR_ITER_CLAUSES];
      MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN
      EXISTS_TAC (rand(rator(rator(concl band)))) THEN CONJ_TAC THENL
       [GEN_TAC THEN REWRITE_TAC[] THEN STRIP_TAC THEN
        SUBGOAL_THEN `8 * byte_len = 8 * val(len:int64)` SUBST1_TAC THENL
         [ASM_ARITH_TAC; ALL_TAC] THEN
        MP_TAC(ISPECL [`pt_in:byte list`;`in_ptr:int64`;`x:armstate`] INPUT_READS_128) THEN
        ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
        ACCEPT_TAC band]]));;

let AES256_GCM_ENCRYPT_LT_2BLOCK_ABS = prove(
 `!in_ptr out_ptr xi_ptr ivec_ptr key_ptr htable_ptr (pt_in:byte list) (co0:(128)word) (co1:(128)word) (co2:(128)word) (co3:(128)word) (co4:(128)word) (co5:(128)word) (co6:(128)word) (co7:(128)word) (ivec:(128)word) (rk0:(128)word) (rk1:(128)word) (rk2:(128)word) (rk3:(128)word) (rk4:(128)word) (rk5:(128)word) (rk6:(128)word) (rk7:(128)word) (rk8:(128)word) (rk9:(128)word) (rk10:(128)word) (rk11:(128)word) (rk12:(128)word) (rk13:(128)word) (rk14:(128)word) (xi:(128)word) (h:(128)word) (h1k:(128)word) (h3k:(128)word) (h5k:(128)word) (h7k:(128)word) (q18i:(128)word) (len:int64) stackptr pc.
    16 + 1 <= val len /\ val len <= 32 /\ LENGTH pt_in = 128 /\
    aligned 16 stackptr /\
    nonoverlapping (word pc,4600) (in_ptr:int64,128) /\
    nonoverlapping (word pc,4600) (out_ptr:int64,128) /\
    nonoverlapping (word pc,4600) (xi_ptr:int64,16) /\
    nonoverlapping (word pc,4600) (ivec_ptr:int64,16) /\
    nonoverlapping (word pc,4600) (key_ptr:int64,240) /\
    nonoverlapping (word pc,4600) (htable_ptr:int64,256) /\
    nonoverlapping (word pc,4600) (stackptr:int64,80) /\
    nonoverlapping (in_ptr,128) (out_ptr,128) /\
    nonoverlapping (in_ptr,128) (xi_ptr,16) /\
    nonoverlapping (in_ptr,128) (ivec_ptr,16) /\
    nonoverlapping (out_ptr,128) (xi_ptr,16) /\
    nonoverlapping (out_ptr,128) (ivec_ptr,16) /\
    nonoverlapping (xi_ptr,16) (ivec_ptr,16) /\
    nonoverlapping (key_ptr,240) (out_ptr,128) /\
    nonoverlapping (key_ptr,240) (xi_ptr,16) /\
    nonoverlapping (key_ptr,240) (ivec_ptr,16) /\
    nonoverlapping (htable_ptr,256) (out_ptr,128) /\
    nonoverlapping (htable_ptr,256) (xi_ptr,16) /\
    nonoverlapping (htable_ptr,256) (ivec_ptr,16) /\
    nonoverlapping (stackptr,80) (out_ptr,128) /\
    nonoverlapping (stackptr,80) (xi_ptr,16) /\
    nonoverlapping (stackptr,80) (ivec_ptr,16) /\
    nonoverlapping (stackptr,80) (in_ptr,128) /\
    nonoverlapping (stackptr,80) (key_ptr,240) /\
    nonoverlapping (stackptr,80) (htable_ptr,256) /\
    nonoverlapping (ivec_ptr,16) (word pc,4600) /\
    nonoverlapping (xi_ptr,16) (word pc,4600) /\
    nonoverlapping (out_ptr,128) (word pc,4600)
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) aes256_gcm_mc /\
           read PC s = word pc /\
           C_ARGUMENTS [in_ptr; word (8 * val len); out_ptr; xi_ptr;
                        ivec_ptr; key_ptr; htable_ptr] s /\
           read SP s = word_add stackptr (word 80) /\
           read Q18 s = q18i /\
           byte_list_at pt_in in_ptr (word 128) s /\
           read (memory :> bytes128 out_ptr) s = co0 /\
           read (memory :> bytes128 (word_add out_ptr (word 16))) s = co1 /\
           read (memory :> bytes128 (word_add out_ptr (word 32))) s = co2 /\
           read (memory :> bytes128 (word_add out_ptr (word 48))) s = co3 /\
           read (memory :> bytes128 (word_add out_ptr (word 64))) s = co4 /\
           read (memory :> bytes128 (word_add out_ptr (word 80))) s = co5 /\
           read (memory :> bytes128 (word_add out_ptr (word 96))) s = co6 /\
           read (memory :> bytes128 (word_add out_ptr (word 112))) s = co7 /\
           read (memory :> bytes128 ivec_ptr) s = ivec /\
           read (memory :> bytes128 (word_add key_ptr (word 0))) s = rk0 /\
           read (memory :> bytes128 (word_add key_ptr (word 16))) s = rk1 /\
           read (memory :> bytes128 (word_add key_ptr (word 32))) s = rk2 /\
           read (memory :> bytes128 (word_add key_ptr (word 48))) s = rk3 /\
           read (memory :> bytes128 (word_add key_ptr (word 64))) s = rk4 /\
           read (memory :> bytes128 (word_add key_ptr (word 80))) s = rk5 /\
           read (memory :> bytes128 (word_add key_ptr (word 96))) s = rk6 /\
           read (memory :> bytes128 (word_add key_ptr (word 112))) s = rk7 /\
           read (memory :> bytes128 (word_add key_ptr (word 128))) s = rk8 /\
           read (memory :> bytes128 (word_add key_ptr (word 144))) s = rk9 /\
           read (memory :> bytes128 (word_add key_ptr (word 160))) s = rk10 /\
           read (memory :> bytes128 (word_add key_ptr (word 176))) s = rk11 /\
           read (memory :> bytes128 (word_add key_ptr (word 192))) s = rk12 /\
           read (memory :> bytes128 (word_add key_ptr (word 208))) s = rk13 /\
           read (memory :> bytes128 (word_add key_ptr (word 224))) s = rk14 /\
           read (memory :> bytes128 xi_ptr) s = xi /\
           read (memory :> bytes128 htable_ptr) s = word_swaphalves128 h /\
           read (memory :> bytes128 (word_add htable_ptr (word 16))) s = h1k /\
           read (memory :> bytes128 (word_add htable_ptr (word 32))) s = word_swaphalves128 (polyval_dot h h) /\
           read (memory :> bytes128 (word_add htable_ptr (word 48))) s = word_swaphalves128 (polyval_dot h (polyval_dot h h)) /\
           read (memory :> bytes128 (word_add htable_ptr (word 64))) s = h3k /\
           read (memory :> bytes128 (word_add htable_ptr (word 80))) s = word_swaphalves128 (polyval_dot (polyval_dot h h) (polyval_dot h h)) /\
           read (memory :> bytes128 (word_add htable_ptr (word 96))) s = word_swaphalves128 (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) /\
           read (memory :> bytes128 (word_add htable_ptr (word 112))) s = h5k /\
           read (memory :> bytes128 (word_add htable_ptr (word 128))) s = word_swaphalves128 (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) h) /\
           read (memory :> bytes128 (word_add htable_ptr (word 144))) s = word_swaphalves128 (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) h) h) /\
           read (memory :> bytes128 (word_add htable_ptr (word 160))) s = h7k /\
           read (memory :> bytes128 (word_add htable_ptr (word 176))) s = word_swaphalves128 (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) h) h) h) /\
           word_subword h1k (0,64):(64)word = karatsuba_mid h /\
           word_subword h1k (64,64):(64)word = karatsuba_mid (polyval_dot h h) /\
           word_subword h3k (0,64):(64)word = karatsuba_mid (polyval_dot h (polyval_dot h h)) /\
           word_subword h3k (64,64):(64)word = karatsuba_mid (polyval_dot (polyval_dot h h) (polyval_dot h h)) /\
           word_subword h5k (0,64):(64)word = karatsuba_mid (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) /\
           word_subword h5k (64,64):(64)word = karatsuba_mid (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) h) /\
           word_subword h7k (0,64):(64)word = karatsuba_mid (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) h) h) /\
           word_subword h7k (64,64):(64)word = karatsuba_mid (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) h) h) h))
      (\s. read PC s = word(pc + (if val(len:int64) = 0 then 4596 else 4588)) /\
           read X0 s = len /\
           byte_list_at (aes256_gcm_encrypt (val len) pt_in ivec [rk0;rk1;rk2;rk3;rk4;rk5;rk6;rk7;rk8;rk9;rk10;rk11;rk12;rk13;rk14])
                        out_ptr len s /\
           read (memory :> bytes128 xi_ptr) s =
             gcm_final_xi (val len) pt_in ivec [rk0;rk1;rk2;rk3;rk4;rk5;rk6;rk7;rk8;rk9;rk10;rk11;rk12;rk13;rk14] xi h)
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [memory :> bytes(out_ptr,128);
                  memory :> bytes(xi_ptr,16);
                  memory :> bytes(ivec_ptr,16)] ,,
       MAYCHANGE [SP] ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes64 stackptr;
                  memory :> bytes64 (word_add stackptr (word 8));
                  memory :> bytes64 (word_add stackptr (word 16));
                  memory :> bytes64 (word_add stackptr (word 24));
                  memory :> bytes64 (word_add stackptr (word 32));
                  memory :> bytes64 (word_add stackptr (word 40));
                  memory :> bytes64 (word_add stackptr (word 48));
                  memory :> bytes64 (word_add stackptr (word 56));
                  memory :> bytes64 (word_add stackptr (word 64));
                  memory :> bytes64 (word_add stackptr (word 72))])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(val(len:int64) = 0) /\ val len = 16 * 1 + (val len - 16)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `byte_len = val(len:int64) - 16` THEN
  SUBGOAL_THEN `1 <= byte_len /\ byte_len <= 16` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "byte_len" THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(if val(len:int64)=0 then 4596 else 4588) = 4588` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `8 * val(len:int64) = 128 + 8 * byte_len` ASSUME_TAC THENL
   [EXPAND_TAC "byte_len" THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL
   [`in_ptr:int64`;
    `out_ptr:int64`;
    `xi_ptr:int64`;
    `ivec_ptr:int64`;
    `key_ptr:int64`;
    `htable_ptr:int64`;
    `bytes_to_int128 (SUB_LIST(0,16) pt_in)`;
    `bytes_to_int128 (SUB_LIST(16,16) pt_in)`;
    `co1:(128)word`;
    `ivec:(128)word`;
    `rk0:(128)word`;
    `rk1:(128)word`;
    `rk2:(128)word`;
    `rk3:(128)word`;
    `rk4:(128)word`;
    `rk5:(128)word`;
    `rk6:(128)word`;
    `rk7:(128)word`;
    `rk8:(128)word`;
    `rk9:(128)word`;
    `rk10:(128)word`;
    `rk11:(128)word`;
    `rk12:(128)word`;
    `rk13:(128)word`;
    `rk14:(128)word`;
    `xi:(128)word`;
    `h:(128)word`;
    `h1k:(128)word`;
    `byte_len:num`;
    `stackptr:int64`;
    `pc:num`]
   AES256_GCM_ENCRYPT_LT_2BLOCK_CONCRETE) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST [ASM_ARITH_TAC; NONOVERLAPPING_TAC; ASM_REWRITE_TAC[]]);
    ALL_TAC] THEN
  DISCH_THEN(fun band ->
    MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN
    EXISTS_TAC (rand(concl band)) THEN CONJ_TAC THENL
     [REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN SUBSUMED_MAYCHANGE_TAC; ALL_TAC] THEN
    MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN
    EXISTS_TAC (rand(rator(concl band))) THEN CONJ_TAC THENL
     [GEN_TAC THEN REWRITE_TAC[] THEN CONV_TAC(LAND_CONV(TOP_DEPTH_CONV let_CONV)) THEN
      STRIP_TAC THEN REPEAT CONJ_TAC THENL
       [ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[] THEN SUBGOAL_THEN `16 + byte_len = val(len:int64)` SUBST1_TAC THENL
         [EXPAND_TAC "byte_len" THEN ASM_ARITH_TAC; REWRITE_TAC[WORD_VAL]];
        MATCH_MP_TAC OUT_BRIDGE_GEN THEN
        MAP_EVERY EXISTS_TAC [`1`; `byte_len:num`; `co1:(128)word`] THEN
        REWRITE_TAC[KS_ITER] THEN REWRITE_TAC CTR_ITER_CLAUSES THEN
        REPEAT CONJ_TAC THENL
         [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]; EXPAND_TAC "byte_len" THEN ASM_ARITH_TAC;
          X_GEN_TAC `k:num` THEN REWRITE_TAC[ARITH_RULE `k < 1 <=> k = 0`] THEN
          DISCH_THEN SUBST1_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN
          REWRITE_TAC CTR_ITER_CLAUSES THEN REWRITE_TAC[WORD_ADD_0] THEN
          ASM_REWRITE_TAC[];
          CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC CTR_ITER_CLAUSES THEN
          ASM_REWRITE_TAC[]];
        ASM_REWRITE_TAC[] THEN
        ASM_SIMP_TAC[GCM_FINAL_XI_UNFOLD; ARITH_RULE `1 <= byte_len ==> ~(16 * 1 + byte_len = 0)`] THEN
        MP_TAC(SPECL [`byte_len:num`;`pt_in:byte list`;`ivec:(128)word`;`[rk0;rk1;rk2;rk3;rk4;rk5;rk6;rk7;rk8;rk9;rk10;rk11;rk12;rk13;rk14]:int128 list`] GHASH_BLOCKS_2) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
        REWRITE_TAC[MAP] THEN REWRITE_TAC[KS_ITER] THEN REWRITE_TAC CTR_ITER_CLAUSES];
      MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN
      EXISTS_TAC (rand(rator(rator(concl band)))) THEN CONJ_TAC THENL
       [GEN_TAC THEN REWRITE_TAC[] THEN STRIP_TAC THEN
        FIRST_ASSUM(fun th -> if concl th = `8 * val(len:int64) = 128 + 8 * byte_len`
                              then REWRITE_TAC[SYM th] else NO_TAC) THEN
        MP_TAC(ISPECL [`pt_in:byte list`;`in_ptr:int64`;`x:armstate`] INPUT_READS_128) THEN
        ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
        ACCEPT_TAC band]]));;

let AES256_GCM_ENCRYPT_LT_3BLOCK_ABS = prove(
 `!in_ptr out_ptr xi_ptr ivec_ptr key_ptr htable_ptr (pt_in:byte list) (co0:(128)word) (co1:(128)word) (co2:(128)word) (co3:(128)word) (co4:(128)word) (co5:(128)word) (co6:(128)word) (co7:(128)word) (ivec:(128)word) (rk0:(128)word) (rk1:(128)word) (rk2:(128)word) (rk3:(128)word) (rk4:(128)word) (rk5:(128)word) (rk6:(128)word) (rk7:(128)word) (rk8:(128)word) (rk9:(128)word) (rk10:(128)word) (rk11:(128)word) (rk12:(128)word) (rk13:(128)word) (rk14:(128)word) (xi:(128)word) (h:(128)word) (h1k:(128)word) (h3k:(128)word) (h5k:(128)word) (h7k:(128)word) (q18i:(128)word) (len:int64) stackptr pc.
    32 + 1 <= val len /\ val len <= 48 /\ LENGTH pt_in = 128 /\
    aligned 16 stackptr /\
    nonoverlapping (word pc,4600) (in_ptr:int64,128) /\
    nonoverlapping (word pc,4600) (out_ptr:int64,128) /\
    nonoverlapping (word pc,4600) (xi_ptr:int64,16) /\
    nonoverlapping (word pc,4600) (ivec_ptr:int64,16) /\
    nonoverlapping (word pc,4600) (key_ptr:int64,240) /\
    nonoverlapping (word pc,4600) (htable_ptr:int64,256) /\
    nonoverlapping (word pc,4600) (stackptr:int64,80) /\
    nonoverlapping (in_ptr,128) (out_ptr,128) /\
    nonoverlapping (in_ptr,128) (xi_ptr,16) /\
    nonoverlapping (in_ptr,128) (ivec_ptr,16) /\
    nonoverlapping (out_ptr,128) (xi_ptr,16) /\
    nonoverlapping (out_ptr,128) (ivec_ptr,16) /\
    nonoverlapping (xi_ptr,16) (ivec_ptr,16) /\
    nonoverlapping (key_ptr,240) (out_ptr,128) /\
    nonoverlapping (key_ptr,240) (xi_ptr,16) /\
    nonoverlapping (key_ptr,240) (ivec_ptr,16) /\
    nonoverlapping (htable_ptr,256) (out_ptr,128) /\
    nonoverlapping (htable_ptr,256) (xi_ptr,16) /\
    nonoverlapping (htable_ptr,256) (ivec_ptr,16) /\
    nonoverlapping (stackptr,80) (out_ptr,128) /\
    nonoverlapping (stackptr,80) (xi_ptr,16) /\
    nonoverlapping (stackptr,80) (ivec_ptr,16) /\
    nonoverlapping (stackptr,80) (in_ptr,128) /\
    nonoverlapping (stackptr,80) (key_ptr,240) /\
    nonoverlapping (stackptr,80) (htable_ptr,256) /\
    nonoverlapping (ivec_ptr,16) (word pc,4600) /\
    nonoverlapping (xi_ptr,16) (word pc,4600) /\
    nonoverlapping (out_ptr,128) (word pc,4600)
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) aes256_gcm_mc /\
           read PC s = word pc /\
           C_ARGUMENTS [in_ptr; word (8 * val len); out_ptr; xi_ptr;
                        ivec_ptr; key_ptr; htable_ptr] s /\
           read SP s = word_add stackptr (word 80) /\
           read Q18 s = q18i /\
           byte_list_at pt_in in_ptr (word 128) s /\
           read (memory :> bytes128 out_ptr) s = co0 /\
           read (memory :> bytes128 (word_add out_ptr (word 16))) s = co1 /\
           read (memory :> bytes128 (word_add out_ptr (word 32))) s = co2 /\
           read (memory :> bytes128 (word_add out_ptr (word 48))) s = co3 /\
           read (memory :> bytes128 (word_add out_ptr (word 64))) s = co4 /\
           read (memory :> bytes128 (word_add out_ptr (word 80))) s = co5 /\
           read (memory :> bytes128 (word_add out_ptr (word 96))) s = co6 /\
           read (memory :> bytes128 (word_add out_ptr (word 112))) s = co7 /\
           read (memory :> bytes128 ivec_ptr) s = ivec /\
           read (memory :> bytes128 (word_add key_ptr (word 0))) s = rk0 /\
           read (memory :> bytes128 (word_add key_ptr (word 16))) s = rk1 /\
           read (memory :> bytes128 (word_add key_ptr (word 32))) s = rk2 /\
           read (memory :> bytes128 (word_add key_ptr (word 48))) s = rk3 /\
           read (memory :> bytes128 (word_add key_ptr (word 64))) s = rk4 /\
           read (memory :> bytes128 (word_add key_ptr (word 80))) s = rk5 /\
           read (memory :> bytes128 (word_add key_ptr (word 96))) s = rk6 /\
           read (memory :> bytes128 (word_add key_ptr (word 112))) s = rk7 /\
           read (memory :> bytes128 (word_add key_ptr (word 128))) s = rk8 /\
           read (memory :> bytes128 (word_add key_ptr (word 144))) s = rk9 /\
           read (memory :> bytes128 (word_add key_ptr (word 160))) s = rk10 /\
           read (memory :> bytes128 (word_add key_ptr (word 176))) s = rk11 /\
           read (memory :> bytes128 (word_add key_ptr (word 192))) s = rk12 /\
           read (memory :> bytes128 (word_add key_ptr (word 208))) s = rk13 /\
           read (memory :> bytes128 (word_add key_ptr (word 224))) s = rk14 /\
           read (memory :> bytes128 xi_ptr) s = xi /\
           read (memory :> bytes128 htable_ptr) s = word_swaphalves128 h /\
           read (memory :> bytes128 (word_add htable_ptr (word 16))) s = h1k /\
           read (memory :> bytes128 (word_add htable_ptr (word 32))) s = word_swaphalves128 (polyval_dot h h) /\
           read (memory :> bytes128 (word_add htable_ptr (word 48))) s = word_swaphalves128 (polyval_dot h (polyval_dot h h)) /\
           read (memory :> bytes128 (word_add htable_ptr (word 64))) s = h3k /\
           read (memory :> bytes128 (word_add htable_ptr (word 80))) s = word_swaphalves128 (polyval_dot (polyval_dot h h) (polyval_dot h h)) /\
           read (memory :> bytes128 (word_add htable_ptr (word 96))) s = word_swaphalves128 (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) /\
           read (memory :> bytes128 (word_add htable_ptr (word 112))) s = h5k /\
           read (memory :> bytes128 (word_add htable_ptr (word 128))) s = word_swaphalves128 (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) h) /\
           read (memory :> bytes128 (word_add htable_ptr (word 144))) s = word_swaphalves128 (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) h) h) /\
           read (memory :> bytes128 (word_add htable_ptr (word 160))) s = h7k /\
           read (memory :> bytes128 (word_add htable_ptr (word 176))) s = word_swaphalves128 (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) h) h) h) /\
           word_subword h1k (0,64):(64)word = karatsuba_mid h /\
           word_subword h1k (64,64):(64)word = karatsuba_mid (polyval_dot h h) /\
           word_subword h3k (0,64):(64)word = karatsuba_mid (polyval_dot h (polyval_dot h h)) /\
           word_subword h3k (64,64):(64)word = karatsuba_mid (polyval_dot (polyval_dot h h) (polyval_dot h h)) /\
           word_subword h5k (0,64):(64)word = karatsuba_mid (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) /\
           word_subword h5k (64,64):(64)word = karatsuba_mid (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) h) /\
           word_subword h7k (0,64):(64)word = karatsuba_mid (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) h) h) /\
           word_subword h7k (64,64):(64)word = karatsuba_mid (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) h) h) h))
      (\s. read PC s = word(pc + (if val(len:int64) = 0 then 4596 else 4588)) /\
           read X0 s = len /\
           byte_list_at (aes256_gcm_encrypt (val len) pt_in ivec [rk0;rk1;rk2;rk3;rk4;rk5;rk6;rk7;rk8;rk9;rk10;rk11;rk12;rk13;rk14])
                        out_ptr len s /\
           read (memory :> bytes128 xi_ptr) s =
             gcm_final_xi (val len) pt_in ivec [rk0;rk1;rk2;rk3;rk4;rk5;rk6;rk7;rk8;rk9;rk10;rk11;rk12;rk13;rk14] xi h)
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [memory :> bytes(out_ptr,128);
                  memory :> bytes(xi_ptr,16);
                  memory :> bytes(ivec_ptr,16)] ,,
       MAYCHANGE [SP] ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes64 stackptr;
                  memory :> bytes64 (word_add stackptr (word 8));
                  memory :> bytes64 (word_add stackptr (word 16));
                  memory :> bytes64 (word_add stackptr (word 24));
                  memory :> bytes64 (word_add stackptr (word 32));
                  memory :> bytes64 (word_add stackptr (word 40));
                  memory :> bytes64 (word_add stackptr (word 48));
                  memory :> bytes64 (word_add stackptr (word 56));
                  memory :> bytes64 (word_add stackptr (word 64));
                  memory :> bytes64 (word_add stackptr (word 72))])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(val(len:int64) = 0) /\ val len = 16 * 2 + (val len - 32)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `byte_len = val(len:int64) - 32` THEN
  SUBGOAL_THEN `1 <= byte_len /\ byte_len <= 16` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "byte_len" THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(if val(len:int64)=0 then 4596 else 4588) = 4588` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `8 * val(len:int64) = 256 + 8 * byte_len` ASSUME_TAC THENL
   [EXPAND_TAC "byte_len" THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL
   [`in_ptr:int64`;
    `out_ptr:int64`;
    `xi_ptr:int64`;
    `ivec_ptr:int64`;
    `key_ptr:int64`;
    `htable_ptr:int64`;
    `bytes_to_int128 (SUB_LIST(0,16) pt_in)`;
    `bytes_to_int128 (SUB_LIST(16,16) pt_in)`;
    `bytes_to_int128 (SUB_LIST(32,16) pt_in)`;
    `co2:(128)word`;
    `ivec:(128)word`;
    `rk0:(128)word`;
    `rk1:(128)word`;
    `rk2:(128)word`;
    `rk3:(128)word`;
    `rk4:(128)word`;
    `rk5:(128)word`;
    `rk6:(128)word`;
    `rk7:(128)word`;
    `rk8:(128)word`;
    `rk9:(128)word`;
    `rk10:(128)word`;
    `rk11:(128)word`;
    `rk12:(128)word`;
    `rk13:(128)word`;
    `rk14:(128)word`;
    `xi:(128)word`;
    `h:(128)word`;
    `h1k:(128)word`;
    `h3k:(128)word`;
    `byte_len:num`;
    `stackptr:int64`;
    `pc:num`]
   AES256_GCM_ENCRYPT_LT_3BLOCK_CONCRETE) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST [ASM_ARITH_TAC; NONOVERLAPPING_TAC; ASM_REWRITE_TAC[]]);
    ALL_TAC] THEN
  DISCH_THEN(fun band ->
    MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN
    EXISTS_TAC (rand(concl band)) THEN CONJ_TAC THENL
     [REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN SUBSUMED_MAYCHANGE_TAC; ALL_TAC] THEN
    MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN
    EXISTS_TAC (rand(rator(concl band))) THEN CONJ_TAC THENL
     [GEN_TAC THEN REWRITE_TAC[] THEN CONV_TAC(LAND_CONV(TOP_DEPTH_CONV let_CONV)) THEN
      STRIP_TAC THEN REPEAT CONJ_TAC THENL
       [ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[] THEN SUBGOAL_THEN `32 + byte_len = val(len:int64)` SUBST1_TAC THENL
         [EXPAND_TAC "byte_len" THEN ASM_ARITH_TAC; REWRITE_TAC[WORD_VAL]];
        MATCH_MP_TAC OUT_BRIDGE_GEN THEN
        MAP_EVERY EXISTS_TAC [`2`; `byte_len:num`; `co2:(128)word`] THEN
        REWRITE_TAC[KS_ITER] THEN REWRITE_TAC CTR_ITER_CLAUSES THEN
        REPEAT CONJ_TAC THENL
         [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]; EXPAND_TAC "byte_len" THEN ASM_ARITH_TAC;
          X_GEN_TAC `k:num` THEN REWRITE_TAC[ARITH_RULE `k < 2 <=> k = 0 \/ k = 1`] THEN
          STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
          CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC CTR_ITER_CLAUSES THEN
          REWRITE_TAC[WORD_ADD_0] THEN ASM_REWRITE_TAC[];
          CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC CTR_ITER_CLAUSES THEN
          ASM_REWRITE_TAC[]];
        ASM_REWRITE_TAC[] THEN
        ASM_SIMP_TAC[GCM_FINAL_XI_UNFOLD; ARITH_RULE `1 <= byte_len ==> ~(16 * 2 + byte_len = 0)`] THEN
        MP_TAC(SPECL [`byte_len:num`;`pt_in:byte list`;`ivec:(128)word`;`[rk0;rk1;rk2;rk3;rk4;rk5;rk6;rk7;rk8;rk9;rk10;rk11;rk12;rk13;rk14]:int128 list`] GHASH_BLOCKS_3) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
        REWRITE_TAC[MAP] THEN REWRITE_TAC[KS_ITER] THEN REWRITE_TAC CTR_ITER_CLAUSES];
      MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN
      EXISTS_TAC (rand(rator(rator(concl band)))) THEN CONJ_TAC THENL
       [GEN_TAC THEN REWRITE_TAC[] THEN STRIP_TAC THEN
        FIRST_ASSUM(fun th -> if concl th = `8 * val(len:int64) = 256 + 8 * byte_len`
                              then REWRITE_TAC[SYM th] else NO_TAC) THEN
        MP_TAC(ISPECL [`pt_in:byte list`;`in_ptr:int64`;`x:armstate`] INPUT_READS_128) THEN
        ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
        ACCEPT_TAC band]]));;

let AES256_GCM_ENCRYPT_LT_4BLOCK_ABS = prove(
 `!in_ptr out_ptr xi_ptr ivec_ptr key_ptr htable_ptr (pt_in:byte list) (co0:(128)word) (co1:(128)word) (co2:(128)word) (co3:(128)word) (co4:(128)word) (co5:(128)word) (co6:(128)word) (co7:(128)word) (ivec:(128)word) (rk0:(128)word) (rk1:(128)word) (rk2:(128)word) (rk3:(128)word) (rk4:(128)word) (rk5:(128)word) (rk6:(128)word) (rk7:(128)word) (rk8:(128)word) (rk9:(128)word) (rk10:(128)word) (rk11:(128)word) (rk12:(128)word) (rk13:(128)word) (rk14:(128)word) (xi:(128)word) (h:(128)word) (h1k:(128)word) (h3k:(128)word) (h5k:(128)word) (h7k:(128)word) (q18i:(128)word) (len:int64) stackptr pc.
    48 + 1 <= val len /\ val len <= 64 /\ LENGTH pt_in = 128 /\
    aligned 16 stackptr /\
    nonoverlapping (word pc,4600) (in_ptr:int64,128) /\
    nonoverlapping (word pc,4600) (out_ptr:int64,128) /\
    nonoverlapping (word pc,4600) (xi_ptr:int64,16) /\
    nonoverlapping (word pc,4600) (ivec_ptr:int64,16) /\
    nonoverlapping (word pc,4600) (key_ptr:int64,240) /\
    nonoverlapping (word pc,4600) (htable_ptr:int64,256) /\
    nonoverlapping (word pc,4600) (stackptr:int64,80) /\
    nonoverlapping (in_ptr,128) (out_ptr,128) /\
    nonoverlapping (in_ptr,128) (xi_ptr,16) /\
    nonoverlapping (in_ptr,128) (ivec_ptr,16) /\
    nonoverlapping (out_ptr,128) (xi_ptr,16) /\
    nonoverlapping (out_ptr,128) (ivec_ptr,16) /\
    nonoverlapping (xi_ptr,16) (ivec_ptr,16) /\
    nonoverlapping (key_ptr,240) (out_ptr,128) /\
    nonoverlapping (key_ptr,240) (xi_ptr,16) /\
    nonoverlapping (key_ptr,240) (ivec_ptr,16) /\
    nonoverlapping (htable_ptr,256) (out_ptr,128) /\
    nonoverlapping (htable_ptr,256) (xi_ptr,16) /\
    nonoverlapping (htable_ptr,256) (ivec_ptr,16) /\
    nonoverlapping (stackptr,80) (out_ptr,128) /\
    nonoverlapping (stackptr,80) (xi_ptr,16) /\
    nonoverlapping (stackptr,80) (ivec_ptr,16) /\
    nonoverlapping (stackptr,80) (in_ptr,128) /\
    nonoverlapping (stackptr,80) (key_ptr,240) /\
    nonoverlapping (stackptr,80) (htable_ptr,256) /\
    nonoverlapping (ivec_ptr,16) (word pc,4600) /\
    nonoverlapping (xi_ptr,16) (word pc,4600) /\
    nonoverlapping (out_ptr,128) (word pc,4600)
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) aes256_gcm_mc /\
           read PC s = word pc /\
           C_ARGUMENTS [in_ptr; word (8 * val len); out_ptr; xi_ptr;
                        ivec_ptr; key_ptr; htable_ptr] s /\
           read SP s = word_add stackptr (word 80) /\
           read Q18 s = q18i /\
           byte_list_at pt_in in_ptr (word 128) s /\
           read (memory :> bytes128 out_ptr) s = co0 /\
           read (memory :> bytes128 (word_add out_ptr (word 16))) s = co1 /\
           read (memory :> bytes128 (word_add out_ptr (word 32))) s = co2 /\
           read (memory :> bytes128 (word_add out_ptr (word 48))) s = co3 /\
           read (memory :> bytes128 (word_add out_ptr (word 64))) s = co4 /\
           read (memory :> bytes128 (word_add out_ptr (word 80))) s = co5 /\
           read (memory :> bytes128 (word_add out_ptr (word 96))) s = co6 /\
           read (memory :> bytes128 (word_add out_ptr (word 112))) s = co7 /\
           read (memory :> bytes128 ivec_ptr) s = ivec /\
           read (memory :> bytes128 (word_add key_ptr (word 0))) s = rk0 /\
           read (memory :> bytes128 (word_add key_ptr (word 16))) s = rk1 /\
           read (memory :> bytes128 (word_add key_ptr (word 32))) s = rk2 /\
           read (memory :> bytes128 (word_add key_ptr (word 48))) s = rk3 /\
           read (memory :> bytes128 (word_add key_ptr (word 64))) s = rk4 /\
           read (memory :> bytes128 (word_add key_ptr (word 80))) s = rk5 /\
           read (memory :> bytes128 (word_add key_ptr (word 96))) s = rk6 /\
           read (memory :> bytes128 (word_add key_ptr (word 112))) s = rk7 /\
           read (memory :> bytes128 (word_add key_ptr (word 128))) s = rk8 /\
           read (memory :> bytes128 (word_add key_ptr (word 144))) s = rk9 /\
           read (memory :> bytes128 (word_add key_ptr (word 160))) s = rk10 /\
           read (memory :> bytes128 (word_add key_ptr (word 176))) s = rk11 /\
           read (memory :> bytes128 (word_add key_ptr (word 192))) s = rk12 /\
           read (memory :> bytes128 (word_add key_ptr (word 208))) s = rk13 /\
           read (memory :> bytes128 (word_add key_ptr (word 224))) s = rk14 /\
           read (memory :> bytes128 xi_ptr) s = xi /\
           read (memory :> bytes128 htable_ptr) s = word_swaphalves128 h /\
           read (memory :> bytes128 (word_add htable_ptr (word 16))) s = h1k /\
           read (memory :> bytes128 (word_add htable_ptr (word 32))) s = word_swaphalves128 (polyval_dot h h) /\
           read (memory :> bytes128 (word_add htable_ptr (word 48))) s = word_swaphalves128 (polyval_dot h (polyval_dot h h)) /\
           read (memory :> bytes128 (word_add htable_ptr (word 64))) s = h3k /\
           read (memory :> bytes128 (word_add htable_ptr (word 80))) s = word_swaphalves128 (polyval_dot (polyval_dot h h) (polyval_dot h h)) /\
           read (memory :> bytes128 (word_add htable_ptr (word 96))) s = word_swaphalves128 (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) /\
           read (memory :> bytes128 (word_add htable_ptr (word 112))) s = h5k /\
           read (memory :> bytes128 (word_add htable_ptr (word 128))) s = word_swaphalves128 (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) h) /\
           read (memory :> bytes128 (word_add htable_ptr (word 144))) s = word_swaphalves128 (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) h) h) /\
           read (memory :> bytes128 (word_add htable_ptr (word 160))) s = h7k /\
           read (memory :> bytes128 (word_add htable_ptr (word 176))) s = word_swaphalves128 (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) h) h) h) /\
           word_subword h1k (0,64):(64)word = karatsuba_mid h /\
           word_subword h1k (64,64):(64)word = karatsuba_mid (polyval_dot h h) /\
           word_subword h3k (0,64):(64)word = karatsuba_mid (polyval_dot h (polyval_dot h h)) /\
           word_subword h3k (64,64):(64)word = karatsuba_mid (polyval_dot (polyval_dot h h) (polyval_dot h h)) /\
           word_subword h5k (0,64):(64)word = karatsuba_mid (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) /\
           word_subword h5k (64,64):(64)word = karatsuba_mid (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) h) /\
           word_subword h7k (0,64):(64)word = karatsuba_mid (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) h) h) /\
           word_subword h7k (64,64):(64)word = karatsuba_mid (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) h) h) h))
      (\s. read PC s = word(pc + (if val(len:int64) = 0 then 4596 else 4588)) /\
           read X0 s = len /\
           byte_list_at (aes256_gcm_encrypt (val len) pt_in ivec [rk0;rk1;rk2;rk3;rk4;rk5;rk6;rk7;rk8;rk9;rk10;rk11;rk12;rk13;rk14])
                        out_ptr len s /\
           read (memory :> bytes128 xi_ptr) s =
             gcm_final_xi (val len) pt_in ivec [rk0;rk1;rk2;rk3;rk4;rk5;rk6;rk7;rk8;rk9;rk10;rk11;rk12;rk13;rk14] xi h)
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [memory :> bytes(out_ptr,128);
                  memory :> bytes(xi_ptr,16);
                  memory :> bytes(ivec_ptr,16)] ,,
       MAYCHANGE [SP] ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes64 stackptr;
                  memory :> bytes64 (word_add stackptr (word 8));
                  memory :> bytes64 (word_add stackptr (word 16));
                  memory :> bytes64 (word_add stackptr (word 24));
                  memory :> bytes64 (word_add stackptr (word 32));
                  memory :> bytes64 (word_add stackptr (word 40));
                  memory :> bytes64 (word_add stackptr (word 48));
                  memory :> bytes64 (word_add stackptr (word 56));
                  memory :> bytes64 (word_add stackptr (word 64));
                  memory :> bytes64 (word_add stackptr (word 72))])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(val(len:int64) = 0) /\ val len = 16 * 3 + (val len - 48)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `byte_len = val(len:int64) - 48` THEN
  SUBGOAL_THEN `1 <= byte_len /\ byte_len <= 16` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "byte_len" THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(if val(len:int64)=0 then 4596 else 4588) = 4588` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `8 * val(len:int64) = 384 + 8 * byte_len` ASSUME_TAC THENL
   [EXPAND_TAC "byte_len" THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL
   [`in_ptr:int64`;
    `out_ptr:int64`;
    `xi_ptr:int64`;
    `ivec_ptr:int64`;
    `key_ptr:int64`;
    `htable_ptr:int64`;
    `bytes_to_int128 (SUB_LIST(0,16) pt_in)`;
    `bytes_to_int128 (SUB_LIST(16,16) pt_in)`;
    `bytes_to_int128 (SUB_LIST(32,16) pt_in)`;
    `bytes_to_int128 (SUB_LIST(48,16) pt_in)`;
    `co3:(128)word`;
    `ivec:(128)word`;
    `rk0:(128)word`;
    `rk1:(128)word`;
    `rk2:(128)word`;
    `rk3:(128)word`;
    `rk4:(128)word`;
    `rk5:(128)word`;
    `rk6:(128)word`;
    `rk7:(128)word`;
    `rk8:(128)word`;
    `rk9:(128)word`;
    `rk10:(128)word`;
    `rk11:(128)word`;
    `rk12:(128)word`;
    `rk13:(128)word`;
    `rk14:(128)word`;
    `xi:(128)word`;
    `h:(128)word`;
    `h1k:(128)word`;
    `h3k:(128)word`;
    `byte_len:num`;
    `stackptr:int64`;
    `pc:num`]
   AES256_GCM_ENCRYPT_LT_4BLOCK_CONCRETE) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST [ASM_ARITH_TAC; NONOVERLAPPING_TAC; ASM_REWRITE_TAC[]]);
    ALL_TAC] THEN
  DISCH_THEN(fun band ->
    MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN
    EXISTS_TAC (rand(concl band)) THEN CONJ_TAC THENL
     [REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN SUBSUMED_MAYCHANGE_TAC; ALL_TAC] THEN
    MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN
    EXISTS_TAC (rand(rator(concl band))) THEN CONJ_TAC THENL
     [GEN_TAC THEN REWRITE_TAC[] THEN CONV_TAC(LAND_CONV(TOP_DEPTH_CONV let_CONV)) THEN
      STRIP_TAC THEN REPEAT CONJ_TAC THENL
       [ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[] THEN SUBGOAL_THEN `48 + byte_len = val(len:int64)` SUBST1_TAC THENL
         [EXPAND_TAC "byte_len" THEN ASM_ARITH_TAC; REWRITE_TAC[WORD_VAL]];
        MATCH_MP_TAC OUT_BRIDGE_GEN THEN
        MAP_EVERY EXISTS_TAC [`3`; `byte_len:num`; `co3:(128)word`] THEN
        REWRITE_TAC[KS_ITER] THEN REWRITE_TAC CTR_ITER_CLAUSES THEN
        REPEAT CONJ_TAC THENL
         [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]; EXPAND_TAC "byte_len" THEN ASM_ARITH_TAC;
          X_GEN_TAC `k:num` THEN REWRITE_TAC[ARITH_RULE `k < 3 <=> k = 0 \/ k = 1 \/ k = 2`] THEN
          STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
          CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC CTR_ITER_CLAUSES THEN
          REWRITE_TAC[WORD_ADD_0] THEN ASM_REWRITE_TAC[];
          CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC CTR_ITER_CLAUSES THEN
          ASM_REWRITE_TAC[]];
        ASM_REWRITE_TAC[] THEN
        ASM_SIMP_TAC[GCM_FINAL_XI_UNFOLD; ARITH_RULE `1 <= byte_len ==> ~(16 * 3 + byte_len = 0)`] THEN
        MP_TAC(SPECL [`byte_len:num`;`pt_in:byte list`;`ivec:(128)word`;`[rk0;rk1;rk2;rk3;rk4;rk5;rk6;rk7;rk8;rk9;rk10;rk11;rk12;rk13;rk14]:int128 list`] GHASH_BLOCKS_4) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
        REWRITE_TAC[MAP] THEN REWRITE_TAC[KS_ITER] THEN REWRITE_TAC CTR_ITER_CLAUSES];
      MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN
      EXISTS_TAC (rand(rator(rator(concl band)))) THEN CONJ_TAC THENL
       [GEN_TAC THEN REWRITE_TAC[] THEN STRIP_TAC THEN
        FIRST_ASSUM(fun th -> if concl th = `8 * val(len:int64) = 384 + 8 * byte_len`
                              then REWRITE_TAC[SYM th] else NO_TAC) THEN
        MP_TAC(ISPECL [`pt_in:byte list`;`in_ptr:int64`;`x:armstate`] INPUT_READS_128) THEN
        ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
        ACCEPT_TAC band]]));;

let AES256_GCM_ENCRYPT_LT_5BLOCK_ABS = prove(
 `!in_ptr out_ptr xi_ptr ivec_ptr key_ptr htable_ptr (pt_in:byte list) (co0:(128)word) (co1:(128)word) (co2:(128)word) (co3:(128)word) (co4:(128)word) (co5:(128)word) (co6:(128)word) (co7:(128)word) (ivec:(128)word) (rk0:(128)word) (rk1:(128)word) (rk2:(128)word) (rk3:(128)word) (rk4:(128)word) (rk5:(128)word) (rk6:(128)word) (rk7:(128)word) (rk8:(128)word) (rk9:(128)word) (rk10:(128)word) (rk11:(128)word) (rk12:(128)word) (rk13:(128)word) (rk14:(128)word) (xi:(128)word) (h:(128)word) (h1k:(128)word) (h3k:(128)word) (h5k:(128)word) (h7k:(128)word) (q18i:(128)word) (len:int64) stackptr pc.
    64 + 1 <= val len /\ val len <= 80 /\ LENGTH pt_in = 128 /\
    aligned 16 stackptr /\
    nonoverlapping (word pc,4600) (in_ptr:int64,128) /\
    nonoverlapping (word pc,4600) (out_ptr:int64,128) /\
    nonoverlapping (word pc,4600) (xi_ptr:int64,16) /\
    nonoverlapping (word pc,4600) (ivec_ptr:int64,16) /\
    nonoverlapping (word pc,4600) (key_ptr:int64,240) /\
    nonoverlapping (word pc,4600) (htable_ptr:int64,256) /\
    nonoverlapping (word pc,4600) (stackptr:int64,80) /\
    nonoverlapping (in_ptr,128) (out_ptr,128) /\
    nonoverlapping (in_ptr,128) (xi_ptr,16) /\
    nonoverlapping (in_ptr,128) (ivec_ptr,16) /\
    nonoverlapping (out_ptr,128) (xi_ptr,16) /\
    nonoverlapping (out_ptr,128) (ivec_ptr,16) /\
    nonoverlapping (xi_ptr,16) (ivec_ptr,16) /\
    nonoverlapping (key_ptr,240) (out_ptr,128) /\
    nonoverlapping (key_ptr,240) (xi_ptr,16) /\
    nonoverlapping (key_ptr,240) (ivec_ptr,16) /\
    nonoverlapping (htable_ptr,256) (out_ptr,128) /\
    nonoverlapping (htable_ptr,256) (xi_ptr,16) /\
    nonoverlapping (htable_ptr,256) (ivec_ptr,16) /\
    nonoverlapping (stackptr,80) (out_ptr,128) /\
    nonoverlapping (stackptr,80) (xi_ptr,16) /\
    nonoverlapping (stackptr,80) (ivec_ptr,16) /\
    nonoverlapping (stackptr,80) (in_ptr,128) /\
    nonoverlapping (stackptr,80) (key_ptr,240) /\
    nonoverlapping (stackptr,80) (htable_ptr,256) /\
    nonoverlapping (ivec_ptr,16) (word pc,4600) /\
    nonoverlapping (xi_ptr,16) (word pc,4600) /\
    nonoverlapping (out_ptr,128) (word pc,4600)
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) aes256_gcm_mc /\
           read PC s = word pc /\
           C_ARGUMENTS [in_ptr; word (8 * val len); out_ptr; xi_ptr;
                        ivec_ptr; key_ptr; htable_ptr] s /\
           read SP s = word_add stackptr (word 80) /\
           read Q18 s = q18i /\
           byte_list_at pt_in in_ptr (word 128) s /\
           read (memory :> bytes128 out_ptr) s = co0 /\
           read (memory :> bytes128 (word_add out_ptr (word 16))) s = co1 /\
           read (memory :> bytes128 (word_add out_ptr (word 32))) s = co2 /\
           read (memory :> bytes128 (word_add out_ptr (word 48))) s = co3 /\
           read (memory :> bytes128 (word_add out_ptr (word 64))) s = co4 /\
           read (memory :> bytes128 (word_add out_ptr (word 80))) s = co5 /\
           read (memory :> bytes128 (word_add out_ptr (word 96))) s = co6 /\
           read (memory :> bytes128 (word_add out_ptr (word 112))) s = co7 /\
           read (memory :> bytes128 ivec_ptr) s = ivec /\
           read (memory :> bytes128 (word_add key_ptr (word 0))) s = rk0 /\
           read (memory :> bytes128 (word_add key_ptr (word 16))) s = rk1 /\
           read (memory :> bytes128 (word_add key_ptr (word 32))) s = rk2 /\
           read (memory :> bytes128 (word_add key_ptr (word 48))) s = rk3 /\
           read (memory :> bytes128 (word_add key_ptr (word 64))) s = rk4 /\
           read (memory :> bytes128 (word_add key_ptr (word 80))) s = rk5 /\
           read (memory :> bytes128 (word_add key_ptr (word 96))) s = rk6 /\
           read (memory :> bytes128 (word_add key_ptr (word 112))) s = rk7 /\
           read (memory :> bytes128 (word_add key_ptr (word 128))) s = rk8 /\
           read (memory :> bytes128 (word_add key_ptr (word 144))) s = rk9 /\
           read (memory :> bytes128 (word_add key_ptr (word 160))) s = rk10 /\
           read (memory :> bytes128 (word_add key_ptr (word 176))) s = rk11 /\
           read (memory :> bytes128 (word_add key_ptr (word 192))) s = rk12 /\
           read (memory :> bytes128 (word_add key_ptr (word 208))) s = rk13 /\
           read (memory :> bytes128 (word_add key_ptr (word 224))) s = rk14 /\
           read (memory :> bytes128 xi_ptr) s = xi /\
           read (memory :> bytes128 htable_ptr) s = word_swaphalves128 h /\
           read (memory :> bytes128 (word_add htable_ptr (word 16))) s = h1k /\
           read (memory :> bytes128 (word_add htable_ptr (word 32))) s = word_swaphalves128 (polyval_dot h h) /\
           read (memory :> bytes128 (word_add htable_ptr (word 48))) s = word_swaphalves128 (polyval_dot h (polyval_dot h h)) /\
           read (memory :> bytes128 (word_add htable_ptr (word 64))) s = h3k /\
           read (memory :> bytes128 (word_add htable_ptr (word 80))) s = word_swaphalves128 (polyval_dot (polyval_dot h h) (polyval_dot h h)) /\
           read (memory :> bytes128 (word_add htable_ptr (word 96))) s = word_swaphalves128 (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) /\
           read (memory :> bytes128 (word_add htable_ptr (word 112))) s = h5k /\
           read (memory :> bytes128 (word_add htable_ptr (word 128))) s = word_swaphalves128 (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) h) /\
           read (memory :> bytes128 (word_add htable_ptr (word 144))) s = word_swaphalves128 (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) h) h) /\
           read (memory :> bytes128 (word_add htable_ptr (word 160))) s = h7k /\
           read (memory :> bytes128 (word_add htable_ptr (word 176))) s = word_swaphalves128 (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) h) h) h) /\
           word_subword h1k (0,64):(64)word = karatsuba_mid h /\
           word_subword h1k (64,64):(64)word = karatsuba_mid (polyval_dot h h) /\
           word_subword h3k (0,64):(64)word = karatsuba_mid (polyval_dot h (polyval_dot h h)) /\
           word_subword h3k (64,64):(64)word = karatsuba_mid (polyval_dot (polyval_dot h h) (polyval_dot h h)) /\
           word_subword h5k (0,64):(64)word = karatsuba_mid (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) /\
           word_subword h5k (64,64):(64)word = karatsuba_mid (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) h) /\
           word_subword h7k (0,64):(64)word = karatsuba_mid (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) h) h) /\
           word_subword h7k (64,64):(64)word = karatsuba_mid (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) h) h) h))
      (\s. read PC s = word(pc + (if val(len:int64) = 0 then 4596 else 4588)) /\
           read X0 s = len /\
           byte_list_at (aes256_gcm_encrypt (val len) pt_in ivec [rk0;rk1;rk2;rk3;rk4;rk5;rk6;rk7;rk8;rk9;rk10;rk11;rk12;rk13;rk14])
                        out_ptr len s /\
           read (memory :> bytes128 xi_ptr) s =
             gcm_final_xi (val len) pt_in ivec [rk0;rk1;rk2;rk3;rk4;rk5;rk6;rk7;rk8;rk9;rk10;rk11;rk12;rk13;rk14] xi h)
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [memory :> bytes(out_ptr,128);
                  memory :> bytes(xi_ptr,16);
                  memory :> bytes(ivec_ptr,16)] ,,
       MAYCHANGE [SP] ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes64 stackptr;
                  memory :> bytes64 (word_add stackptr (word 8));
                  memory :> bytes64 (word_add stackptr (word 16));
                  memory :> bytes64 (word_add stackptr (word 24));
                  memory :> bytes64 (word_add stackptr (word 32));
                  memory :> bytes64 (word_add stackptr (word 40));
                  memory :> bytes64 (word_add stackptr (word 48));
                  memory :> bytes64 (word_add stackptr (word 56));
                  memory :> bytes64 (word_add stackptr (word 64));
                  memory :> bytes64 (word_add stackptr (word 72))])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(val(len:int64) = 0) /\ val len = 16 * 4 + (val len - 64)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `byte_len = val(len:int64) - 64` THEN
  SUBGOAL_THEN `1 <= byte_len /\ byte_len <= 16` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "byte_len" THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(if val(len:int64)=0 then 4596 else 4588) = 4588` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `8 * val(len:int64) = 512 + 8 * byte_len` ASSUME_TAC THENL
   [EXPAND_TAC "byte_len" THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL
   [`in_ptr:int64`;
    `out_ptr:int64`;
    `xi_ptr:int64`;
    `ivec_ptr:int64`;
    `key_ptr:int64`;
    `htable_ptr:int64`;
    `bytes_to_int128 (SUB_LIST(0,16) pt_in)`;
    `bytes_to_int128 (SUB_LIST(16,16) pt_in)`;
    `bytes_to_int128 (SUB_LIST(32,16) pt_in)`;
    `bytes_to_int128 (SUB_LIST(48,16) pt_in)`;
    `bytes_to_int128 (SUB_LIST(64,16) pt_in)`;
    `co4:(128)word`;
    `ivec:(128)word`;
    `rk0:(128)word`;
    `rk1:(128)word`;
    `rk2:(128)word`;
    `rk3:(128)word`;
    `rk4:(128)word`;
    `rk5:(128)word`;
    `rk6:(128)word`;
    `rk7:(128)word`;
    `rk8:(128)word`;
    `rk9:(128)word`;
    `rk10:(128)word`;
    `rk11:(128)word`;
    `rk12:(128)word`;
    `rk13:(128)word`;
    `rk14:(128)word`;
    `xi:(128)word`;
    `h:(128)word`;
    `h1k:(128)word`;
    `h3k:(128)word`;
    `h5k:(128)word`;
    `byte_len:num`;
    `stackptr:int64`;
    `pc:num`]
   AES256_GCM_ENCRYPT_LT_5BLOCK_CONCRETE) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST [ASM_ARITH_TAC; NONOVERLAPPING_TAC; ASM_REWRITE_TAC[]]);
    ALL_TAC] THEN
  DISCH_THEN(fun band ->
    MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN
    EXISTS_TAC (rand(concl band)) THEN CONJ_TAC THENL
     [REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN SUBSUMED_MAYCHANGE_TAC; ALL_TAC] THEN
    MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN
    EXISTS_TAC (rand(rator(concl band))) THEN CONJ_TAC THENL
     [GEN_TAC THEN REWRITE_TAC[] THEN CONV_TAC(LAND_CONV(TOP_DEPTH_CONV let_CONV)) THEN
      STRIP_TAC THEN REPEAT CONJ_TAC THENL
       [ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[] THEN SUBGOAL_THEN `64 + byte_len = val(len:int64)` SUBST1_TAC THENL
         [EXPAND_TAC "byte_len" THEN ASM_ARITH_TAC; REWRITE_TAC[WORD_VAL]];
        MATCH_MP_TAC OUT_BRIDGE_GEN THEN
        MAP_EVERY EXISTS_TAC [`4`; `byte_len:num`; `co4:(128)word`] THEN
        REWRITE_TAC[KS_ITER] THEN REWRITE_TAC CTR_ITER_CLAUSES THEN
        REPEAT CONJ_TAC THENL
         [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]; EXPAND_TAC "byte_len" THEN ASM_ARITH_TAC;
          X_GEN_TAC `k:num` THEN REWRITE_TAC[ARITH_RULE `k < 4 <=> k = 0 \/ k = 1 \/ k = 2 \/ k = 3`] THEN
          STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
          CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC CTR_ITER_CLAUSES THEN
          REWRITE_TAC[WORD_ADD_0] THEN ASM_REWRITE_TAC[];
          CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC CTR_ITER_CLAUSES THEN
          ASM_REWRITE_TAC[]];
        ASM_REWRITE_TAC[] THEN
        ASM_SIMP_TAC[GCM_FINAL_XI_UNFOLD; ARITH_RULE `1 <= byte_len ==> ~(16 * 4 + byte_len = 0)`] THEN
        MP_TAC(SPECL [`byte_len:num`;`pt_in:byte list`;`ivec:(128)word`;`[rk0;rk1;rk2;rk3;rk4;rk5;rk6;rk7;rk8;rk9;rk10;rk11;rk12;rk13;rk14]:int128 list`] GHASH_BLOCKS_5) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
        REWRITE_TAC[MAP] THEN REWRITE_TAC[KS_ITER] THEN REWRITE_TAC CTR_ITER_CLAUSES];
      MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN
      EXISTS_TAC (rand(rator(rator(concl band)))) THEN CONJ_TAC THENL
       [GEN_TAC THEN REWRITE_TAC[] THEN STRIP_TAC THEN
        FIRST_ASSUM(fun th -> if concl th = `8 * val(len:int64) = 512 + 8 * byte_len`
                              then REWRITE_TAC[SYM th] else NO_TAC) THEN
        MP_TAC(ISPECL [`pt_in:byte list`;`in_ptr:int64`;`x:armstate`] INPUT_READS_128) THEN
        ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
        ACCEPT_TAC band]]));;

let AES256_GCM_ENCRYPT_LT_6BLOCK_ABS = prove(
 `!in_ptr out_ptr xi_ptr ivec_ptr key_ptr htable_ptr (pt_in:byte list) (co0:(128)word) (co1:(128)word) (co2:(128)word) (co3:(128)word) (co4:(128)word) (co5:(128)word) (co6:(128)word) (co7:(128)word) (ivec:(128)word) (rk0:(128)word) (rk1:(128)word) (rk2:(128)word) (rk3:(128)word) (rk4:(128)word) (rk5:(128)word) (rk6:(128)word) (rk7:(128)word) (rk8:(128)word) (rk9:(128)word) (rk10:(128)word) (rk11:(128)word) (rk12:(128)word) (rk13:(128)word) (rk14:(128)word) (xi:(128)word) (h:(128)word) (h1k:(128)word) (h3k:(128)word) (h5k:(128)word) (h7k:(128)word) (q18i:(128)word) (len:int64) stackptr pc.
    80 + 1 <= val len /\ val len <= 96 /\ LENGTH pt_in = 128 /\
    aligned 16 stackptr /\
    nonoverlapping (word pc,4600) (in_ptr:int64,128) /\
    nonoverlapping (word pc,4600) (out_ptr:int64,128) /\
    nonoverlapping (word pc,4600) (xi_ptr:int64,16) /\
    nonoverlapping (word pc,4600) (ivec_ptr:int64,16) /\
    nonoverlapping (word pc,4600) (key_ptr:int64,240) /\
    nonoverlapping (word pc,4600) (htable_ptr:int64,256) /\
    nonoverlapping (word pc,4600) (stackptr:int64,80) /\
    nonoverlapping (in_ptr,128) (out_ptr,128) /\
    nonoverlapping (in_ptr,128) (xi_ptr,16) /\
    nonoverlapping (in_ptr,128) (ivec_ptr,16) /\
    nonoverlapping (out_ptr,128) (xi_ptr,16) /\
    nonoverlapping (out_ptr,128) (ivec_ptr,16) /\
    nonoverlapping (xi_ptr,16) (ivec_ptr,16) /\
    nonoverlapping (key_ptr,240) (out_ptr,128) /\
    nonoverlapping (key_ptr,240) (xi_ptr,16) /\
    nonoverlapping (key_ptr,240) (ivec_ptr,16) /\
    nonoverlapping (htable_ptr,256) (out_ptr,128) /\
    nonoverlapping (htable_ptr,256) (xi_ptr,16) /\
    nonoverlapping (htable_ptr,256) (ivec_ptr,16) /\
    nonoverlapping (stackptr,80) (out_ptr,128) /\
    nonoverlapping (stackptr,80) (xi_ptr,16) /\
    nonoverlapping (stackptr,80) (ivec_ptr,16) /\
    nonoverlapping (stackptr,80) (in_ptr,128) /\
    nonoverlapping (stackptr,80) (key_ptr,240) /\
    nonoverlapping (stackptr,80) (htable_ptr,256) /\
    nonoverlapping (ivec_ptr,16) (word pc,4600) /\
    nonoverlapping (xi_ptr,16) (word pc,4600) /\
    nonoverlapping (out_ptr,128) (word pc,4600)
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) aes256_gcm_mc /\
           read PC s = word pc /\
           C_ARGUMENTS [in_ptr; word (8 * val len); out_ptr; xi_ptr;
                        ivec_ptr; key_ptr; htable_ptr] s /\
           read SP s = word_add stackptr (word 80) /\
           read Q18 s = q18i /\
           byte_list_at pt_in in_ptr (word 128) s /\
           read (memory :> bytes128 out_ptr) s = co0 /\
           read (memory :> bytes128 (word_add out_ptr (word 16))) s = co1 /\
           read (memory :> bytes128 (word_add out_ptr (word 32))) s = co2 /\
           read (memory :> bytes128 (word_add out_ptr (word 48))) s = co3 /\
           read (memory :> bytes128 (word_add out_ptr (word 64))) s = co4 /\
           read (memory :> bytes128 (word_add out_ptr (word 80))) s = co5 /\
           read (memory :> bytes128 (word_add out_ptr (word 96))) s = co6 /\
           read (memory :> bytes128 (word_add out_ptr (word 112))) s = co7 /\
           read (memory :> bytes128 ivec_ptr) s = ivec /\
           read (memory :> bytes128 (word_add key_ptr (word 0))) s = rk0 /\
           read (memory :> bytes128 (word_add key_ptr (word 16))) s = rk1 /\
           read (memory :> bytes128 (word_add key_ptr (word 32))) s = rk2 /\
           read (memory :> bytes128 (word_add key_ptr (word 48))) s = rk3 /\
           read (memory :> bytes128 (word_add key_ptr (word 64))) s = rk4 /\
           read (memory :> bytes128 (word_add key_ptr (word 80))) s = rk5 /\
           read (memory :> bytes128 (word_add key_ptr (word 96))) s = rk6 /\
           read (memory :> bytes128 (word_add key_ptr (word 112))) s = rk7 /\
           read (memory :> bytes128 (word_add key_ptr (word 128))) s = rk8 /\
           read (memory :> bytes128 (word_add key_ptr (word 144))) s = rk9 /\
           read (memory :> bytes128 (word_add key_ptr (word 160))) s = rk10 /\
           read (memory :> bytes128 (word_add key_ptr (word 176))) s = rk11 /\
           read (memory :> bytes128 (word_add key_ptr (word 192))) s = rk12 /\
           read (memory :> bytes128 (word_add key_ptr (word 208))) s = rk13 /\
           read (memory :> bytes128 (word_add key_ptr (word 224))) s = rk14 /\
           read (memory :> bytes128 xi_ptr) s = xi /\
           read (memory :> bytes128 htable_ptr) s = word_swaphalves128 h /\
           read (memory :> bytes128 (word_add htable_ptr (word 16))) s = h1k /\
           read (memory :> bytes128 (word_add htable_ptr (word 32))) s = word_swaphalves128 (polyval_dot h h) /\
           read (memory :> bytes128 (word_add htable_ptr (word 48))) s = word_swaphalves128 (polyval_dot h (polyval_dot h h)) /\
           read (memory :> bytes128 (word_add htable_ptr (word 64))) s = h3k /\
           read (memory :> bytes128 (word_add htable_ptr (word 80))) s = word_swaphalves128 (polyval_dot (polyval_dot h h) (polyval_dot h h)) /\
           read (memory :> bytes128 (word_add htable_ptr (word 96))) s = word_swaphalves128 (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) /\
           read (memory :> bytes128 (word_add htable_ptr (word 112))) s = h5k /\
           read (memory :> bytes128 (word_add htable_ptr (word 128))) s = word_swaphalves128 (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) h) /\
           read (memory :> bytes128 (word_add htable_ptr (word 144))) s = word_swaphalves128 (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) h) h) /\
           read (memory :> bytes128 (word_add htable_ptr (word 160))) s = h7k /\
           read (memory :> bytes128 (word_add htable_ptr (word 176))) s = word_swaphalves128 (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) h) h) h) /\
           word_subword h1k (0,64):(64)word = karatsuba_mid h /\
           word_subword h1k (64,64):(64)word = karatsuba_mid (polyval_dot h h) /\
           word_subword h3k (0,64):(64)word = karatsuba_mid (polyval_dot h (polyval_dot h h)) /\
           word_subword h3k (64,64):(64)word = karatsuba_mid (polyval_dot (polyval_dot h h) (polyval_dot h h)) /\
           word_subword h5k (0,64):(64)word = karatsuba_mid (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) /\
           word_subword h5k (64,64):(64)word = karatsuba_mid (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) h) /\
           word_subword h7k (0,64):(64)word = karatsuba_mid (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) h) h) /\
           word_subword h7k (64,64):(64)word = karatsuba_mid (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) h) h) h))
      (\s. read PC s = word(pc + (if val(len:int64) = 0 then 4596 else 4588)) /\
           read X0 s = len /\
           byte_list_at (aes256_gcm_encrypt (val len) pt_in ivec [rk0;rk1;rk2;rk3;rk4;rk5;rk6;rk7;rk8;rk9;rk10;rk11;rk12;rk13;rk14])
                        out_ptr len s /\
           read (memory :> bytes128 xi_ptr) s =
             gcm_final_xi (val len) pt_in ivec [rk0;rk1;rk2;rk3;rk4;rk5;rk6;rk7;rk8;rk9;rk10;rk11;rk12;rk13;rk14] xi h)
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [memory :> bytes(out_ptr,128);
                  memory :> bytes(xi_ptr,16);
                  memory :> bytes(ivec_ptr,16)] ,,
       MAYCHANGE [SP] ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes64 stackptr;
                  memory :> bytes64 (word_add stackptr (word 8));
                  memory :> bytes64 (word_add stackptr (word 16));
                  memory :> bytes64 (word_add stackptr (word 24));
                  memory :> bytes64 (word_add stackptr (word 32));
                  memory :> bytes64 (word_add stackptr (word 40));
                  memory :> bytes64 (word_add stackptr (word 48));
                  memory :> bytes64 (word_add stackptr (word 56));
                  memory :> bytes64 (word_add stackptr (word 64));
                  memory :> bytes64 (word_add stackptr (word 72))])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(val(len:int64) = 0) /\ val len = 16 * 5 + (val len - 80)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `byte_len = val(len:int64) - 80` THEN
  SUBGOAL_THEN `1 <= byte_len /\ byte_len <= 16` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "byte_len" THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(if val(len:int64)=0 then 4596 else 4588) = 4588` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `8 * val(len:int64) = 640 + 8 * byte_len` ASSUME_TAC THENL
   [EXPAND_TAC "byte_len" THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL
   [`in_ptr:int64`;
    `out_ptr:int64`;
    `xi_ptr:int64`;
    `ivec_ptr:int64`;
    `key_ptr:int64`;
    `htable_ptr:int64`;
    `bytes_to_int128 (SUB_LIST(0,16) pt_in)`;
    `bytes_to_int128 (SUB_LIST(16,16) pt_in)`;
    `bytes_to_int128 (SUB_LIST(32,16) pt_in)`;
    `bytes_to_int128 (SUB_LIST(48,16) pt_in)`;
    `bytes_to_int128 (SUB_LIST(64,16) pt_in)`;
    `bytes_to_int128 (SUB_LIST(80,16) pt_in)`;
    `co5:(128)word`;
    `ivec:(128)word`;
    `rk0:(128)word`;
    `rk1:(128)word`;
    `rk2:(128)word`;
    `rk3:(128)word`;
    `rk4:(128)word`;
    `rk5:(128)word`;
    `rk6:(128)word`;
    `rk7:(128)word`;
    `rk8:(128)word`;
    `rk9:(128)word`;
    `rk10:(128)word`;
    `rk11:(128)word`;
    `rk12:(128)word`;
    `rk13:(128)word`;
    `rk14:(128)word`;
    `xi:(128)word`;
    `h:(128)word`;
    `h1k:(128)word`;
    `h3k:(128)word`;
    `h5k:(128)word`;
    `byte_len:num`;
    `stackptr:int64`;
    `pc:num`]
   AES256_GCM_ENCRYPT_LT_6BLOCK_CONCRETE) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST [ASM_ARITH_TAC; NONOVERLAPPING_TAC; ASM_REWRITE_TAC[]]);
    ALL_TAC] THEN
  DISCH_THEN(fun band ->
    MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN
    EXISTS_TAC (rand(concl band)) THEN CONJ_TAC THENL
     [REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN SUBSUMED_MAYCHANGE_TAC; ALL_TAC] THEN
    MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN
    EXISTS_TAC (rand(rator(concl band))) THEN CONJ_TAC THENL
     [GEN_TAC THEN REWRITE_TAC[] THEN CONV_TAC(LAND_CONV(TOP_DEPTH_CONV let_CONV)) THEN
      STRIP_TAC THEN REPEAT CONJ_TAC THENL
       [ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[] THEN SUBGOAL_THEN `80 + byte_len = val(len:int64)` SUBST1_TAC THENL
         [EXPAND_TAC "byte_len" THEN ASM_ARITH_TAC; REWRITE_TAC[WORD_VAL]];
        MATCH_MP_TAC OUT_BRIDGE_GEN THEN
        MAP_EVERY EXISTS_TAC [`5`; `byte_len:num`; `co5:(128)word`] THEN
        REWRITE_TAC[KS_ITER] THEN REWRITE_TAC CTR_ITER_CLAUSES THEN
        REPEAT CONJ_TAC THENL
         [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]; EXPAND_TAC "byte_len" THEN ASM_ARITH_TAC;
          X_GEN_TAC `k:num` THEN REWRITE_TAC[ARITH_RULE `k < 5 <=> k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4`] THEN
          STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
          CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC CTR_ITER_CLAUSES THEN
          REWRITE_TAC[WORD_ADD_0] THEN ASM_REWRITE_TAC[];
          CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC CTR_ITER_CLAUSES THEN
          ASM_REWRITE_TAC[]];
        ASM_REWRITE_TAC[] THEN
        ASM_SIMP_TAC[GCM_FINAL_XI_UNFOLD; ARITH_RULE `1 <= byte_len ==> ~(16 * 5 + byte_len = 0)`] THEN
        MP_TAC(SPECL [`byte_len:num`;`pt_in:byte list`;`ivec:(128)word`;`[rk0;rk1;rk2;rk3;rk4;rk5;rk6;rk7;rk8;rk9;rk10;rk11;rk12;rk13;rk14]:int128 list`] GHASH_BLOCKS_6) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
        REWRITE_TAC[MAP] THEN REWRITE_TAC[KS_ITER] THEN REWRITE_TAC CTR_ITER_CLAUSES];
      MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN
      EXISTS_TAC (rand(rator(rator(concl band)))) THEN CONJ_TAC THENL
       [GEN_TAC THEN REWRITE_TAC[] THEN STRIP_TAC THEN
        FIRST_ASSUM(fun th -> if concl th = `8 * val(len:int64) = 640 + 8 * byte_len`
                              then REWRITE_TAC[SYM th] else NO_TAC) THEN
        MP_TAC(ISPECL [`pt_in:byte list`;`in_ptr:int64`;`x:armstate`] INPUT_READS_128) THEN
        ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
        ACCEPT_TAC band]]));;

let AES256_GCM_ENCRYPT_LT_7BLOCK_ABS = prove(
 `!in_ptr out_ptr xi_ptr ivec_ptr key_ptr htable_ptr (pt_in:byte list) (co0:(128)word) (co1:(128)word) (co2:(128)word) (co3:(128)word) (co4:(128)word) (co5:(128)word) (co6:(128)word) (co7:(128)word) (ivec:(128)word) (rk0:(128)word) (rk1:(128)word) (rk2:(128)word) (rk3:(128)word) (rk4:(128)word) (rk5:(128)word) (rk6:(128)word) (rk7:(128)word) (rk8:(128)word) (rk9:(128)word) (rk10:(128)word) (rk11:(128)word) (rk12:(128)word) (rk13:(128)word) (rk14:(128)word) (xi:(128)word) (h:(128)word) (h1k:(128)word) (h3k:(128)word) (h5k:(128)word) (h7k:(128)word) (q18i:(128)word) (len:int64) stackptr pc.
    96 + 1 <= val len /\ val len <= 112 /\ LENGTH pt_in = 128 /\
    aligned 16 stackptr /\
    nonoverlapping (word pc,4600) (in_ptr:int64,128) /\
    nonoverlapping (word pc,4600) (out_ptr:int64,128) /\
    nonoverlapping (word pc,4600) (xi_ptr:int64,16) /\
    nonoverlapping (word pc,4600) (ivec_ptr:int64,16) /\
    nonoverlapping (word pc,4600) (key_ptr:int64,240) /\
    nonoverlapping (word pc,4600) (htable_ptr:int64,256) /\
    nonoverlapping (word pc,4600) (stackptr:int64,80) /\
    nonoverlapping (in_ptr,128) (out_ptr,128) /\
    nonoverlapping (in_ptr,128) (xi_ptr,16) /\
    nonoverlapping (in_ptr,128) (ivec_ptr,16) /\
    nonoverlapping (out_ptr,128) (xi_ptr,16) /\
    nonoverlapping (out_ptr,128) (ivec_ptr,16) /\
    nonoverlapping (xi_ptr,16) (ivec_ptr,16) /\
    nonoverlapping (key_ptr,240) (out_ptr,128) /\
    nonoverlapping (key_ptr,240) (xi_ptr,16) /\
    nonoverlapping (key_ptr,240) (ivec_ptr,16) /\
    nonoverlapping (htable_ptr,256) (out_ptr,128) /\
    nonoverlapping (htable_ptr,256) (xi_ptr,16) /\
    nonoverlapping (htable_ptr,256) (ivec_ptr,16) /\
    nonoverlapping (stackptr,80) (out_ptr,128) /\
    nonoverlapping (stackptr,80) (xi_ptr,16) /\
    nonoverlapping (stackptr,80) (ivec_ptr,16) /\
    nonoverlapping (stackptr,80) (in_ptr,128) /\
    nonoverlapping (stackptr,80) (key_ptr,240) /\
    nonoverlapping (stackptr,80) (htable_ptr,256) /\
    nonoverlapping (ivec_ptr,16) (word pc,4600) /\
    nonoverlapping (xi_ptr,16) (word pc,4600) /\
    nonoverlapping (out_ptr,128) (word pc,4600)
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) aes256_gcm_mc /\
           read PC s = word pc /\
           C_ARGUMENTS [in_ptr; word (8 * val len); out_ptr; xi_ptr;
                        ivec_ptr; key_ptr; htable_ptr] s /\
           read SP s = word_add stackptr (word 80) /\
           read Q18 s = q18i /\
           byte_list_at pt_in in_ptr (word 128) s /\
           read (memory :> bytes128 out_ptr) s = co0 /\
           read (memory :> bytes128 (word_add out_ptr (word 16))) s = co1 /\
           read (memory :> bytes128 (word_add out_ptr (word 32))) s = co2 /\
           read (memory :> bytes128 (word_add out_ptr (word 48))) s = co3 /\
           read (memory :> bytes128 (word_add out_ptr (word 64))) s = co4 /\
           read (memory :> bytes128 (word_add out_ptr (word 80))) s = co5 /\
           read (memory :> bytes128 (word_add out_ptr (word 96))) s = co6 /\
           read (memory :> bytes128 (word_add out_ptr (word 112))) s = co7 /\
           read (memory :> bytes128 ivec_ptr) s = ivec /\
           read (memory :> bytes128 (word_add key_ptr (word 0))) s = rk0 /\
           read (memory :> bytes128 (word_add key_ptr (word 16))) s = rk1 /\
           read (memory :> bytes128 (word_add key_ptr (word 32))) s = rk2 /\
           read (memory :> bytes128 (word_add key_ptr (word 48))) s = rk3 /\
           read (memory :> bytes128 (word_add key_ptr (word 64))) s = rk4 /\
           read (memory :> bytes128 (word_add key_ptr (word 80))) s = rk5 /\
           read (memory :> bytes128 (word_add key_ptr (word 96))) s = rk6 /\
           read (memory :> bytes128 (word_add key_ptr (word 112))) s = rk7 /\
           read (memory :> bytes128 (word_add key_ptr (word 128))) s = rk8 /\
           read (memory :> bytes128 (word_add key_ptr (word 144))) s = rk9 /\
           read (memory :> bytes128 (word_add key_ptr (word 160))) s = rk10 /\
           read (memory :> bytes128 (word_add key_ptr (word 176))) s = rk11 /\
           read (memory :> bytes128 (word_add key_ptr (word 192))) s = rk12 /\
           read (memory :> bytes128 (word_add key_ptr (word 208))) s = rk13 /\
           read (memory :> bytes128 (word_add key_ptr (word 224))) s = rk14 /\
           read (memory :> bytes128 xi_ptr) s = xi /\
           read (memory :> bytes128 htable_ptr) s = word_swaphalves128 h /\
           read (memory :> bytes128 (word_add htable_ptr (word 16))) s = h1k /\
           read (memory :> bytes128 (word_add htable_ptr (word 32))) s = word_swaphalves128 (polyval_dot h h) /\
           read (memory :> bytes128 (word_add htable_ptr (word 48))) s = word_swaphalves128 (polyval_dot h (polyval_dot h h)) /\
           read (memory :> bytes128 (word_add htable_ptr (word 64))) s = h3k /\
           read (memory :> bytes128 (word_add htable_ptr (word 80))) s = word_swaphalves128 (polyval_dot (polyval_dot h h) (polyval_dot h h)) /\
           read (memory :> bytes128 (word_add htable_ptr (word 96))) s = word_swaphalves128 (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) /\
           read (memory :> bytes128 (word_add htable_ptr (word 112))) s = h5k /\
           read (memory :> bytes128 (word_add htable_ptr (word 128))) s = word_swaphalves128 (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) h) /\
           read (memory :> bytes128 (word_add htable_ptr (word 144))) s = word_swaphalves128 (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) h) h) /\
           read (memory :> bytes128 (word_add htable_ptr (word 160))) s = h7k /\
           read (memory :> bytes128 (word_add htable_ptr (word 176))) s = word_swaphalves128 (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) h) h) h) /\
           word_subword h1k (0,64):(64)word = karatsuba_mid h /\
           word_subword h1k (64,64):(64)word = karatsuba_mid (polyval_dot h h) /\
           word_subword h3k (0,64):(64)word = karatsuba_mid (polyval_dot h (polyval_dot h h)) /\
           word_subword h3k (64,64):(64)word = karatsuba_mid (polyval_dot (polyval_dot h h) (polyval_dot h h)) /\
           word_subword h5k (0,64):(64)word = karatsuba_mid (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) /\
           word_subword h5k (64,64):(64)word = karatsuba_mid (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) h) /\
           word_subword h7k (0,64):(64)word = karatsuba_mid (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) h) h) /\
           word_subword h7k (64,64):(64)word = karatsuba_mid (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) h) h) h))
      (\s. read PC s = word(pc + (if val(len:int64) = 0 then 4596 else 4588)) /\
           read X0 s = len /\
           byte_list_at (aes256_gcm_encrypt (val len) pt_in ivec [rk0;rk1;rk2;rk3;rk4;rk5;rk6;rk7;rk8;rk9;rk10;rk11;rk12;rk13;rk14])
                        out_ptr len s /\
           read (memory :> bytes128 xi_ptr) s =
             gcm_final_xi (val len) pt_in ivec [rk0;rk1;rk2;rk3;rk4;rk5;rk6;rk7;rk8;rk9;rk10;rk11;rk12;rk13;rk14] xi h)
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [memory :> bytes(out_ptr,128);
                  memory :> bytes(xi_ptr,16);
                  memory :> bytes(ivec_ptr,16)] ,,
       MAYCHANGE [SP] ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes64 stackptr;
                  memory :> bytes64 (word_add stackptr (word 8));
                  memory :> bytes64 (word_add stackptr (word 16));
                  memory :> bytes64 (word_add stackptr (word 24));
                  memory :> bytes64 (word_add stackptr (word 32));
                  memory :> bytes64 (word_add stackptr (word 40));
                  memory :> bytes64 (word_add stackptr (word 48));
                  memory :> bytes64 (word_add stackptr (word 56));
                  memory :> bytes64 (word_add stackptr (word 64));
                  memory :> bytes64 (word_add stackptr (word 72))])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(val(len:int64) = 0) /\ val len = 16 * 6 + (val len - 96)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `byte_len = val(len:int64) - 96` THEN
  SUBGOAL_THEN `1 <= byte_len /\ byte_len <= 16` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "byte_len" THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(if val(len:int64)=0 then 4596 else 4588) = 4588` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `8 * val(len:int64) = 768 + 8 * byte_len` ASSUME_TAC THENL
   [EXPAND_TAC "byte_len" THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL
   [`in_ptr:int64`;
    `out_ptr:int64`;
    `xi_ptr:int64`;
    `ivec_ptr:int64`;
    `key_ptr:int64`;
    `htable_ptr:int64`;
    `bytes_to_int128 (SUB_LIST(0,16) pt_in)`;
    `bytes_to_int128 (SUB_LIST(16,16) pt_in)`;
    `bytes_to_int128 (SUB_LIST(32,16) pt_in)`;
    `bytes_to_int128 (SUB_LIST(48,16) pt_in)`;
    `bytes_to_int128 (SUB_LIST(64,16) pt_in)`;
    `bytes_to_int128 (SUB_LIST(80,16) pt_in)`;
    `bytes_to_int128 (SUB_LIST(96,16) pt_in)`;
    `co6:(128)word`;
    `ivec:(128)word`;
    `rk0:(128)word`;
    `rk1:(128)word`;
    `rk2:(128)word`;
    `rk3:(128)word`;
    `rk4:(128)word`;
    `rk5:(128)word`;
    `rk6:(128)word`;
    `rk7:(128)word`;
    `rk8:(128)word`;
    `rk9:(128)word`;
    `rk10:(128)word`;
    `rk11:(128)word`;
    `rk12:(128)word`;
    `rk13:(128)word`;
    `rk14:(128)word`;
    `xi:(128)word`;
    `h:(128)word`;
    `h1k:(128)word`;
    `h3k:(128)word`;
    `h5k:(128)word`;
    `h7k:(128)word`;
    `byte_len:num`;
    `stackptr:int64`;
    `pc:num`]
   AES256_GCM_ENCRYPT_LT_7BLOCK_CONCRETE) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST [ASM_ARITH_TAC; NONOVERLAPPING_TAC; ASM_REWRITE_TAC[]]);
    ALL_TAC] THEN
  DISCH_THEN(fun band ->
    MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN
    EXISTS_TAC (rand(concl band)) THEN CONJ_TAC THENL
     [REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN SUBSUMED_MAYCHANGE_TAC; ALL_TAC] THEN
    MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN
    EXISTS_TAC (rand(rator(concl band))) THEN CONJ_TAC THENL
     [GEN_TAC THEN REWRITE_TAC[] THEN CONV_TAC(LAND_CONV(TOP_DEPTH_CONV let_CONV)) THEN
      STRIP_TAC THEN REPEAT CONJ_TAC THENL
       [ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[] THEN SUBGOAL_THEN `96 + byte_len = val(len:int64)` SUBST1_TAC THENL
         [EXPAND_TAC "byte_len" THEN ASM_ARITH_TAC; REWRITE_TAC[WORD_VAL]];
        MATCH_MP_TAC OUT_BRIDGE_GEN THEN
        MAP_EVERY EXISTS_TAC [`6`; `byte_len:num`; `co6:(128)word`] THEN
        REWRITE_TAC[KS_ITER] THEN REWRITE_TAC CTR_ITER_CLAUSES THEN
        REPEAT CONJ_TAC THENL
         [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]; EXPAND_TAC "byte_len" THEN ASM_ARITH_TAC;
          X_GEN_TAC `k:num` THEN REWRITE_TAC[ARITH_RULE `k < 6 <=> k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5`] THEN
          STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
          CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC CTR_ITER_CLAUSES THEN
          REWRITE_TAC[WORD_ADD_0] THEN ASM_REWRITE_TAC[];
          CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC CTR_ITER_CLAUSES THEN
          ASM_REWRITE_TAC[]];
        ASM_REWRITE_TAC[] THEN
        ASM_SIMP_TAC[GCM_FINAL_XI_UNFOLD; ARITH_RULE `1 <= byte_len ==> ~(16 * 6 + byte_len = 0)`] THEN
        MP_TAC(SPECL [`byte_len:num`;`pt_in:byte list`;`ivec:(128)word`;`[rk0;rk1;rk2;rk3;rk4;rk5;rk6;rk7;rk8;rk9;rk10;rk11;rk12;rk13;rk14]:int128 list`] GHASH_BLOCKS_7) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
        REWRITE_TAC[MAP] THEN REWRITE_TAC[KS_ITER] THEN REWRITE_TAC CTR_ITER_CLAUSES];
      MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN
      EXISTS_TAC (rand(rator(rator(concl band)))) THEN CONJ_TAC THENL
       [GEN_TAC THEN REWRITE_TAC[] THEN STRIP_TAC THEN
        FIRST_ASSUM(fun th -> if concl th = `8 * val(len:int64) = 768 + 8 * byte_len`
                              then REWRITE_TAC[SYM th] else NO_TAC) THEN
        MP_TAC(ISPECL [`pt_in:byte list`;`in_ptr:int64`;`x:armstate`] INPUT_READS_128) THEN
        ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
        ACCEPT_TAC band]]));;

let AES256_GCM_ENCRYPT_LT_8BLOCK_ABS = prove(
 `!in_ptr out_ptr xi_ptr ivec_ptr key_ptr htable_ptr (pt_in:byte list) (co0:(128)word) (co1:(128)word) (co2:(128)word) (co3:(128)word) (co4:(128)word) (co5:(128)word) (co6:(128)word) (co7:(128)word) (ivec:(128)word) (rk0:(128)word) (rk1:(128)word) (rk2:(128)word) (rk3:(128)word) (rk4:(128)word) (rk5:(128)word) (rk6:(128)word) (rk7:(128)word) (rk8:(128)word) (rk9:(128)word) (rk10:(128)word) (rk11:(128)word) (rk12:(128)word) (rk13:(128)word) (rk14:(128)word) (xi:(128)word) (h:(128)word) (h1k:(128)word) (h3k:(128)word) (h5k:(128)word) (h7k:(128)word) (q18i:(128)word) (len:int64) stackptr pc.
    112 + 1 <= val len /\ val len <= 128 /\ LENGTH pt_in = 128 /\
    aligned 16 stackptr /\
    nonoverlapping (word pc,4600) (in_ptr:int64,128) /\
    nonoverlapping (word pc,4600) (out_ptr:int64,128) /\
    nonoverlapping (word pc,4600) (xi_ptr:int64,16) /\
    nonoverlapping (word pc,4600) (ivec_ptr:int64,16) /\
    nonoverlapping (word pc,4600) (key_ptr:int64,240) /\
    nonoverlapping (word pc,4600) (htable_ptr:int64,256) /\
    nonoverlapping (word pc,4600) (stackptr:int64,80) /\
    nonoverlapping (in_ptr,128) (out_ptr,128) /\
    nonoverlapping (in_ptr,128) (xi_ptr,16) /\
    nonoverlapping (in_ptr,128) (ivec_ptr,16) /\
    nonoverlapping (out_ptr,128) (xi_ptr,16) /\
    nonoverlapping (out_ptr,128) (ivec_ptr,16) /\
    nonoverlapping (xi_ptr,16) (ivec_ptr,16) /\
    nonoverlapping (key_ptr,240) (out_ptr,128) /\
    nonoverlapping (key_ptr,240) (xi_ptr,16) /\
    nonoverlapping (key_ptr,240) (ivec_ptr,16) /\
    nonoverlapping (htable_ptr,256) (out_ptr,128) /\
    nonoverlapping (htable_ptr,256) (xi_ptr,16) /\
    nonoverlapping (htable_ptr,256) (ivec_ptr,16) /\
    nonoverlapping (stackptr,80) (out_ptr,128) /\
    nonoverlapping (stackptr,80) (xi_ptr,16) /\
    nonoverlapping (stackptr,80) (ivec_ptr,16) /\
    nonoverlapping (stackptr,80) (in_ptr,128) /\
    nonoverlapping (stackptr,80) (key_ptr,240) /\
    nonoverlapping (stackptr,80) (htable_ptr,256) /\
    nonoverlapping (ivec_ptr,16) (word pc,4600) /\
    nonoverlapping (xi_ptr,16) (word pc,4600) /\
    nonoverlapping (out_ptr,128) (word pc,4600)
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) aes256_gcm_mc /\
           read PC s = word pc /\
           C_ARGUMENTS [in_ptr; word (8 * val len); out_ptr; xi_ptr;
                        ivec_ptr; key_ptr; htable_ptr] s /\
           read SP s = word_add stackptr (word 80) /\
           read Q18 s = q18i /\
           byte_list_at pt_in in_ptr (word 128) s /\
           read (memory :> bytes128 out_ptr) s = co0 /\
           read (memory :> bytes128 (word_add out_ptr (word 16))) s = co1 /\
           read (memory :> bytes128 (word_add out_ptr (word 32))) s = co2 /\
           read (memory :> bytes128 (word_add out_ptr (word 48))) s = co3 /\
           read (memory :> bytes128 (word_add out_ptr (word 64))) s = co4 /\
           read (memory :> bytes128 (word_add out_ptr (word 80))) s = co5 /\
           read (memory :> bytes128 (word_add out_ptr (word 96))) s = co6 /\
           read (memory :> bytes128 (word_add out_ptr (word 112))) s = co7 /\
           read (memory :> bytes128 ivec_ptr) s = ivec /\
           read (memory :> bytes128 (word_add key_ptr (word 0))) s = rk0 /\
           read (memory :> bytes128 (word_add key_ptr (word 16))) s = rk1 /\
           read (memory :> bytes128 (word_add key_ptr (word 32))) s = rk2 /\
           read (memory :> bytes128 (word_add key_ptr (word 48))) s = rk3 /\
           read (memory :> bytes128 (word_add key_ptr (word 64))) s = rk4 /\
           read (memory :> bytes128 (word_add key_ptr (word 80))) s = rk5 /\
           read (memory :> bytes128 (word_add key_ptr (word 96))) s = rk6 /\
           read (memory :> bytes128 (word_add key_ptr (word 112))) s = rk7 /\
           read (memory :> bytes128 (word_add key_ptr (word 128))) s = rk8 /\
           read (memory :> bytes128 (word_add key_ptr (word 144))) s = rk9 /\
           read (memory :> bytes128 (word_add key_ptr (word 160))) s = rk10 /\
           read (memory :> bytes128 (word_add key_ptr (word 176))) s = rk11 /\
           read (memory :> bytes128 (word_add key_ptr (word 192))) s = rk12 /\
           read (memory :> bytes128 (word_add key_ptr (word 208))) s = rk13 /\
           read (memory :> bytes128 (word_add key_ptr (word 224))) s = rk14 /\
           read (memory :> bytes128 xi_ptr) s = xi /\
           read (memory :> bytes128 htable_ptr) s = word_swaphalves128 h /\
           read (memory :> bytes128 (word_add htable_ptr (word 16))) s = h1k /\
           read (memory :> bytes128 (word_add htable_ptr (word 32))) s = word_swaphalves128 (polyval_dot h h) /\
           read (memory :> bytes128 (word_add htable_ptr (word 48))) s = word_swaphalves128 (polyval_dot h (polyval_dot h h)) /\
           read (memory :> bytes128 (word_add htable_ptr (word 64))) s = h3k /\
           read (memory :> bytes128 (word_add htable_ptr (word 80))) s = word_swaphalves128 (polyval_dot (polyval_dot h h) (polyval_dot h h)) /\
           read (memory :> bytes128 (word_add htable_ptr (word 96))) s = word_swaphalves128 (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) /\
           read (memory :> bytes128 (word_add htable_ptr (word 112))) s = h5k /\
           read (memory :> bytes128 (word_add htable_ptr (word 128))) s = word_swaphalves128 (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) h) /\
           read (memory :> bytes128 (word_add htable_ptr (word 144))) s = word_swaphalves128 (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) h) h) /\
           read (memory :> bytes128 (word_add htable_ptr (word 160))) s = h7k /\
           read (memory :> bytes128 (word_add htable_ptr (word 176))) s = word_swaphalves128 (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) h) h) h) /\
           word_subword h1k (0,64):(64)word = karatsuba_mid h /\
           word_subword h1k (64,64):(64)word = karatsuba_mid (polyval_dot h h) /\
           word_subword h3k (0,64):(64)word = karatsuba_mid (polyval_dot h (polyval_dot h h)) /\
           word_subword h3k (64,64):(64)word = karatsuba_mid (polyval_dot (polyval_dot h h) (polyval_dot h h)) /\
           word_subword h5k (0,64):(64)word = karatsuba_mid (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) /\
           word_subword h5k (64,64):(64)word = karatsuba_mid (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) h) /\
           word_subword h7k (0,64):(64)word = karatsuba_mid (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) h) h) /\
           word_subword h7k (64,64):(64)word = karatsuba_mid (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) h) h) h))
      (\s. read PC s = word(pc + (if val(len:int64) = 0 then 4596 else 4588)) /\
           read X0 s = len /\
           byte_list_at (aes256_gcm_encrypt (val len) pt_in ivec [rk0;rk1;rk2;rk3;rk4;rk5;rk6;rk7;rk8;rk9;rk10;rk11;rk12;rk13;rk14])
                        out_ptr len s /\
           read (memory :> bytes128 xi_ptr) s =
             gcm_final_xi (val len) pt_in ivec [rk0;rk1;rk2;rk3;rk4;rk5;rk6;rk7;rk8;rk9;rk10;rk11;rk12;rk13;rk14] xi h)
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [memory :> bytes(out_ptr,128);
                  memory :> bytes(xi_ptr,16);
                  memory :> bytes(ivec_ptr,16)] ,,
       MAYCHANGE [SP] ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes64 stackptr;
                  memory :> bytes64 (word_add stackptr (word 8));
                  memory :> bytes64 (word_add stackptr (word 16));
                  memory :> bytes64 (word_add stackptr (word 24));
                  memory :> bytes64 (word_add stackptr (word 32));
                  memory :> bytes64 (word_add stackptr (word 40));
                  memory :> bytes64 (word_add stackptr (word 48));
                  memory :> bytes64 (word_add stackptr (word 56));
                  memory :> bytes64 (word_add stackptr (word 64));
                  memory :> bytes64 (word_add stackptr (word 72))])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(val(len:int64) = 0) /\ val len = 16 * 7 + (val len - 112)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `byte_len = val(len:int64) - 112` THEN
  SUBGOAL_THEN `1 <= byte_len /\ byte_len <= 16` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "byte_len" THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(if val(len:int64)=0 then 4596 else 4588) = 4588` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `8 * val(len:int64) = 896 + 8 * byte_len` ASSUME_TAC THENL
   [EXPAND_TAC "byte_len" THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL
   [`in_ptr:int64`;
    `out_ptr:int64`;
    `xi_ptr:int64`;
    `ivec_ptr:int64`;
    `key_ptr:int64`;
    `htable_ptr:int64`;
    `bytes_to_int128 (SUB_LIST(0,16) pt_in)`;
    `bytes_to_int128 (SUB_LIST(16,16) pt_in)`;
    `bytes_to_int128 (SUB_LIST(32,16) pt_in)`;
    `bytes_to_int128 (SUB_LIST(48,16) pt_in)`;
    `bytes_to_int128 (SUB_LIST(64,16) pt_in)`;
    `bytes_to_int128 (SUB_LIST(80,16) pt_in)`;
    `bytes_to_int128 (SUB_LIST(96,16) pt_in)`;
    `bytes_to_int128 (SUB_LIST(112,16) pt_in)`;
    `co7:(128)word`;
    `ivec:(128)word`;
    `rk0:(128)word`;
    `rk1:(128)word`;
    `rk2:(128)word`;
    `rk3:(128)word`;
    `rk4:(128)word`;
    `rk5:(128)word`;
    `rk6:(128)word`;
    `rk7:(128)word`;
    `rk8:(128)word`;
    `rk9:(128)word`;
    `rk10:(128)word`;
    `rk11:(128)word`;
    `rk12:(128)word`;
    `rk13:(128)word`;
    `rk14:(128)word`;
    `xi:(128)word`;
    `h:(128)word`;
    `h1k:(128)word`;
    `h3k:(128)word`;
    `h5k:(128)word`;
    `h7k:(128)word`;
    `q18i:(128)word`;
    `byte_len:num`;
    `stackptr:int64`;
    `pc:num`]
   AES256_GCM_ENCRYPT_LT_8BLOCK_CONCRETE) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST [ASM_ARITH_TAC; NONOVERLAPPING_TAC; ASM_REWRITE_TAC[]]);
    ALL_TAC] THEN
  DISCH_THEN(fun band ->
    MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN
    EXISTS_TAC (rand(concl band)) THEN CONJ_TAC THENL
     [REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN SUBSUMED_MAYCHANGE_TAC; ALL_TAC] THEN
    MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN
    EXISTS_TAC (rand(rator(concl band))) THEN CONJ_TAC THENL
     [GEN_TAC THEN REWRITE_TAC[] THEN CONV_TAC(LAND_CONV(TOP_DEPTH_CONV let_CONV)) THEN
      STRIP_TAC THEN REPEAT CONJ_TAC THENL
       [ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[] THEN SUBGOAL_THEN `112 + byte_len = val(len:int64)` SUBST1_TAC THENL
         [EXPAND_TAC "byte_len" THEN ASM_ARITH_TAC; REWRITE_TAC[WORD_VAL]];
        MATCH_MP_TAC OUT_BRIDGE_GEN THEN
        MAP_EVERY EXISTS_TAC [`7`; `byte_len:num`; `co7:(128)word`] THEN
        REWRITE_TAC[KS_ITER] THEN REWRITE_TAC CTR_ITER_CLAUSES THEN
        REPEAT CONJ_TAC THENL
         [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]; EXPAND_TAC "byte_len" THEN ASM_ARITH_TAC;
          X_GEN_TAC `k:num` THEN REWRITE_TAC[ARITH_RULE `k < 7 <=> k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6`] THEN
          STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
          CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC CTR_ITER_CLAUSES THEN
          REWRITE_TAC[WORD_ADD_0] THEN ASM_REWRITE_TAC[];
          CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC CTR_ITER_CLAUSES THEN
          ASM_REWRITE_TAC[]];
        ASM_REWRITE_TAC[] THEN
        ASM_SIMP_TAC[GCM_FINAL_XI_UNFOLD; ARITH_RULE `1 <= byte_len ==> ~(16 * 7 + byte_len = 0)`] THEN
        MP_TAC(SPECL [`byte_len:num`;`pt_in:byte list`;`ivec:(128)word`;`[rk0;rk1;rk2;rk3;rk4;rk5;rk6;rk7;rk8;rk9;rk10;rk11;rk12;rk13;rk14]:int128 list`] GHASH_BLOCKS_8) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
        REWRITE_TAC[MAP] THEN REWRITE_TAC[KS_ITER] THEN REWRITE_TAC CTR_ITER_CLAUSES];
      MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN
      EXISTS_TAC (rand(rator(rator(concl band)))) THEN CONJ_TAC THENL
       [GEN_TAC THEN REWRITE_TAC[] THEN STRIP_TAC THEN
        FIRST_ASSUM(fun th -> if concl th = `8 * val(len:int64) = 896 + 8 * byte_len`
                              then REWRITE_TAC[SYM th] else NO_TAC) THEN
        MP_TAC(ISPECL [`pt_in:byte list`;`in_ptr:int64`;`x:armstate`] INPUT_READS_128) THEN
        ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
        ACCEPT_TAC band]]));;

(* ===== combined dispatch ===== *)

let AES256_GCM_ENCRYPT_CORRECT = prove(
 `!in_ptr out_ptr xi_ptr ivec_ptr key_ptr htable_ptr (pt_in:byte list) (co0:(128)word) (co1:(128)word) (co2:(128)word) (co3:(128)word) (co4:(128)word) (co5:(128)word) (co6:(128)word) (co7:(128)word) (ivec:(128)word) (rk0:(128)word) (rk1:(128)word) (rk2:(128)word) (rk3:(128)word) (rk4:(128)word) (rk5:(128)word) (rk6:(128)word) (rk7:(128)word) (rk8:(128)word) (rk9:(128)word) (rk10:(128)word) (rk11:(128)word) (rk12:(128)word) (rk13:(128)word) (rk14:(128)word) (xi:(128)word) (h:(128)word) (h1k:(128)word) (h3k:(128)word) (h5k:(128)word) (h7k:(128)word) (q18i:(128)word) (len:int64) stackptr pc.
    val len <= 128 /\ LENGTH pt_in = 128 /\
    aligned 16 stackptr /\
    nonoverlapping (word pc,4600) (in_ptr:int64,128) /\
    nonoverlapping (word pc,4600) (out_ptr:int64,128) /\
    nonoverlapping (word pc,4600) (xi_ptr:int64,16) /\
    nonoverlapping (word pc,4600) (ivec_ptr:int64,16) /\
    nonoverlapping (word pc,4600) (key_ptr:int64,240) /\
    nonoverlapping (word pc,4600) (htable_ptr:int64,256) /\
    nonoverlapping (word pc,4600) (stackptr:int64,80) /\
    nonoverlapping (in_ptr,128) (out_ptr,128) /\
    nonoverlapping (in_ptr,128) (xi_ptr,16) /\
    nonoverlapping (in_ptr,128) (ivec_ptr,16) /\
    nonoverlapping (out_ptr,128) (xi_ptr,16) /\
    nonoverlapping (out_ptr,128) (ivec_ptr,16) /\
    nonoverlapping (xi_ptr,16) (ivec_ptr,16) /\
    nonoverlapping (key_ptr,240) (out_ptr,128) /\
    nonoverlapping (key_ptr,240) (xi_ptr,16) /\
    nonoverlapping (key_ptr,240) (ivec_ptr,16) /\
    nonoverlapping (htable_ptr,256) (out_ptr,128) /\
    nonoverlapping (htable_ptr,256) (xi_ptr,16) /\
    nonoverlapping (htable_ptr,256) (ivec_ptr,16) /\
    nonoverlapping (stackptr,80) (out_ptr,128) /\
    nonoverlapping (stackptr,80) (xi_ptr,16) /\
    nonoverlapping (stackptr,80) (ivec_ptr,16) /\
    nonoverlapping (stackptr,80) (in_ptr,128) /\
    nonoverlapping (stackptr,80) (key_ptr,240) /\
    nonoverlapping (stackptr,80) (htable_ptr,256) /\
    nonoverlapping (ivec_ptr,16) (word pc,4600) /\
    nonoverlapping (xi_ptr,16) (word pc,4600) /\
    nonoverlapping (out_ptr,128) (word pc,4600)
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) aes256_gcm_mc /\
           read PC s = word pc /\
           C_ARGUMENTS [in_ptr; word (8 * val len); out_ptr; xi_ptr;
                        ivec_ptr; key_ptr; htable_ptr] s /\
           read SP s = word_add stackptr (word 80) /\
           read Q18 s = q18i /\
           byte_list_at pt_in in_ptr (word 128) s /\
           read (memory :> bytes128 out_ptr) s = co0 /\
           read (memory :> bytes128 (word_add out_ptr (word 16))) s = co1 /\
           read (memory :> bytes128 (word_add out_ptr (word 32))) s = co2 /\
           read (memory :> bytes128 (word_add out_ptr (word 48))) s = co3 /\
           read (memory :> bytes128 (word_add out_ptr (word 64))) s = co4 /\
           read (memory :> bytes128 (word_add out_ptr (word 80))) s = co5 /\
           read (memory :> bytes128 (word_add out_ptr (word 96))) s = co6 /\
           read (memory :> bytes128 (word_add out_ptr (word 112))) s = co7 /\
           read (memory :> bytes128 ivec_ptr) s = ivec /\
           read (memory :> bytes128 (word_add key_ptr (word 0))) s = rk0 /\
           read (memory :> bytes128 (word_add key_ptr (word 16))) s = rk1 /\
           read (memory :> bytes128 (word_add key_ptr (word 32))) s = rk2 /\
           read (memory :> bytes128 (word_add key_ptr (word 48))) s = rk3 /\
           read (memory :> bytes128 (word_add key_ptr (word 64))) s = rk4 /\
           read (memory :> bytes128 (word_add key_ptr (word 80))) s = rk5 /\
           read (memory :> bytes128 (word_add key_ptr (word 96))) s = rk6 /\
           read (memory :> bytes128 (word_add key_ptr (word 112))) s = rk7 /\
           read (memory :> bytes128 (word_add key_ptr (word 128))) s = rk8 /\
           read (memory :> bytes128 (word_add key_ptr (word 144))) s = rk9 /\
           read (memory :> bytes128 (word_add key_ptr (word 160))) s = rk10 /\
           read (memory :> bytes128 (word_add key_ptr (word 176))) s = rk11 /\
           read (memory :> bytes128 (word_add key_ptr (word 192))) s = rk12 /\
           read (memory :> bytes128 (word_add key_ptr (word 208))) s = rk13 /\
           read (memory :> bytes128 (word_add key_ptr (word 224))) s = rk14 /\
           read (memory :> bytes128 xi_ptr) s = xi /\
           read (memory :> bytes128 htable_ptr) s = word_swaphalves128 h /\
           read (memory :> bytes128 (word_add htable_ptr (word 16))) s = h1k /\
           read (memory :> bytes128 (word_add htable_ptr (word 32))) s = word_swaphalves128 (polyval_dot h h) /\
           read (memory :> bytes128 (word_add htable_ptr (word 48))) s = word_swaphalves128 (polyval_dot h (polyval_dot h h)) /\
           read (memory :> bytes128 (word_add htable_ptr (word 64))) s = h3k /\
           read (memory :> bytes128 (word_add htable_ptr (word 80))) s = word_swaphalves128 (polyval_dot (polyval_dot h h) (polyval_dot h h)) /\
           read (memory :> bytes128 (word_add htable_ptr (word 96))) s = word_swaphalves128 (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) /\
           read (memory :> bytes128 (word_add htable_ptr (word 112))) s = h5k /\
           read (memory :> bytes128 (word_add htable_ptr (word 128))) s = word_swaphalves128 (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) h) /\
           read (memory :> bytes128 (word_add htable_ptr (word 144))) s = word_swaphalves128 (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) h) h) /\
           read (memory :> bytes128 (word_add htable_ptr (word 160))) s = h7k /\
           read (memory :> bytes128 (word_add htable_ptr (word 176))) s = word_swaphalves128 (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) h) h) h) /\
           word_subword h1k (0,64):(64)word = karatsuba_mid h /\
           word_subword h1k (64,64):(64)word = karatsuba_mid (polyval_dot h h) /\
           word_subword h3k (0,64):(64)word = karatsuba_mid (polyval_dot h (polyval_dot h h)) /\
           word_subword h3k (64,64):(64)word = karatsuba_mid (polyval_dot (polyval_dot h h) (polyval_dot h h)) /\
           word_subword h5k (0,64):(64)word = karatsuba_mid (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) /\
           word_subword h5k (64,64):(64)word = karatsuba_mid (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) h) /\
           word_subword h7k (0,64):(64)word = karatsuba_mid (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) h) h) /\
           word_subword h7k (64,64):(64)word = karatsuba_mid (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) h) h) h))
      (\s. (read PC s = word(pc + 4596) \/ read PC s = word(pc + 4588)) /\
           read X0 s = len /\
           byte_list_at (aes256_gcm_encrypt (val len) pt_in ivec [rk0;rk1;rk2;rk3;rk4;rk5;rk6;rk7;rk8;rk9;rk10;rk11;rk12;rk13;rk14])
                        out_ptr len s /\
           read (memory :> bytes128 xi_ptr) s =
             gcm_final_xi (val len) pt_in ivec [rk0;rk1;rk2;rk3;rk4;rk5;rk6;rk7;rk8;rk9;rk10;rk11;rk12;rk13;rk14] xi h)
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [memory :> bytes(out_ptr,128);
                  memory :> bytes(xi_ptr,16);
                  memory :> bytes(ivec_ptr,16)] ,,
       MAYCHANGE [SP] ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes64 stackptr;
                  memory :> bytes64 (word_add stackptr (word 8));
                  memory :> bytes64 (word_add stackptr (word 16));
                  memory :> bytes64 (word_add stackptr (word 24));
                  memory :> bytes64 (word_add stackptr (word 32));
                  memory :> bytes64 (word_add stackptr (word 40));
                  memory :> bytes64 (word_add stackptr (word 48));
                  memory :> bytes64 (word_add stackptr (word 56));
                  memory :> bytes64 (word_add stackptr (word 64));
                  memory :> bytes64 (word_add stackptr (word 72))])`,
  REPEAT STRIP_TAC THEN
  (* Weaken the conditional exit PC to the disjunction of the two ret sites,
     then run the per-length-band dispatch on the original concrete postcond. *)
  MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN
  EXISTS_TAC `(\s. read PC s = word(pc + (if val(len:int64) = 0 then 4596 else 4588)) /\
           read X0 s = len /\
           byte_list_at (aes256_gcm_encrypt (val len) pt_in ivec [rk0;rk1;rk2;rk3;rk4;rk5;rk6;rk7;rk8;rk9;rk10;rk11;rk12;rk13;rk14])
                        out_ptr len s /\
           read (memory :> bytes128 xi_ptr) s =
             gcm_final_xi (val len) pt_in ivec [rk0;rk1;rk2;rk3;rk4;rk5;rk6;rk7;rk8;rk9;rk10;rk11;rk12;rk13;rk14] xi h)` THEN
  CONJ_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    POP_ASSUM MP_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `val(len:int64) = 0` THENL
   [MP_TAC AES256_GCM_ENCRYPT_LT_0BLOCK_ABS THEN DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `val(len:int64) <= 16` THENL
   [MP_TAC AES256_GCM_ENCRYPT_LT_1BLOCK_ABS THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_SIMP_TAC[ARITH_RULE `~(n = 0) ==> 0 + 1 <= n`]; ALL_TAC] THEN
  ASM_CASES_TAC `val(len:int64) <= 32` THENL
   [MP_TAC AES256_GCM_ENCRYPT_LT_2BLOCK_ABS THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `val(len:int64) <= 48` THENL
   [MP_TAC AES256_GCM_ENCRYPT_LT_3BLOCK_ABS THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `val(len:int64) <= 64` THENL
   [MP_TAC AES256_GCM_ENCRYPT_LT_4BLOCK_ABS THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `val(len:int64) <= 80` THENL
   [MP_TAC AES256_GCM_ENCRYPT_LT_5BLOCK_ABS THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `val(len:int64) <= 96` THENL
   [MP_TAC AES256_GCM_ENCRYPT_LT_6BLOCK_ABS THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `val(len:int64) <= 112` THENL
   [MP_TAC AES256_GCM_ENCRYPT_LT_7BLOCK_ABS THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC AES256_GCM_ENCRYPT_LT_8BLOCK_ABS THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

(* ========================================================================= *)
(* Subroutine-level correctness (return-address / ABI form).                  *)
(*                                                                           *)
(* AES256_GCM_ENCRYPT_CORRECT lands at the routine's two ret sites (pc+4596   *)
(* for the val len = 0 cbz early-exit, pc+4588 for the framed path), stated   *)
(* as a disjunction of exit PCs (cf. BIGNUM_ADD_CORRECT).  The single NOSTACK *)
(* lift executes the ret (PC := X30 = returnaddress); byte_list_at is         *)
(* unfolded so the output equality transfers across the ret, and the 80-byte *)
(* frame is handled inside the core, so no stack reasoning is added.          *)
(* ========================================================================= *)

let AES256_GCM_ENCRYPT_SUBROUTINE_CORRECT = prove(
 `!in_ptr out_ptr xi_ptr ivec_ptr key_ptr htable_ptr (pt_in:byte list) (co0:(128)word) (co1:(128)word) (co2:(128)word) (co3:(128)word) (co4:(128)word) (co5:(128)word) (co6:(128)word) (co7:(128)word) (ivec:(128)word) (rk0:(128)word) (rk1:(128)word) (rk2:(128)word) (rk3:(128)word) (rk4:(128)word) (rk5:(128)word) (rk6:(128)word) (rk7:(128)word) (rk8:(128)word) (rk9:(128)word) (rk10:(128)word) (rk11:(128)word) (rk12:(128)word) (rk13:(128)word) (rk14:(128)word) (xi:(128)word) (h:(128)word) (h1k:(128)word) (h3k:(128)word) (h5k:(128)word) (h7k:(128)word) (q18i:(128)word) (len:int64) stackptr pc returnaddress.
    val len <= 128 /\ LENGTH pt_in = 128 /\
    aligned 16 stackptr /\
    nonoverlapping (word pc,4600) (in_ptr:int64,128) /\
    nonoverlapping (word pc,4600) (out_ptr:int64,128) /\
    nonoverlapping (word pc,4600) (xi_ptr:int64,16) /\
    nonoverlapping (word pc,4600) (ivec_ptr:int64,16) /\
    nonoverlapping (word pc,4600) (key_ptr:int64,240) /\
    nonoverlapping (word pc,4600) (htable_ptr:int64,256) /\
    nonoverlapping (word pc,4600) (stackptr:int64,80) /\
    nonoverlapping (in_ptr,128) (out_ptr,128) /\
    nonoverlapping (in_ptr,128) (xi_ptr,16) /\
    nonoverlapping (in_ptr,128) (ivec_ptr,16) /\
    nonoverlapping (out_ptr,128) (xi_ptr,16) /\
    nonoverlapping (out_ptr,128) (ivec_ptr,16) /\
    nonoverlapping (xi_ptr,16) (ivec_ptr,16) /\
    nonoverlapping (key_ptr,240) (out_ptr,128) /\
    nonoverlapping (key_ptr,240) (xi_ptr,16) /\
    nonoverlapping (key_ptr,240) (ivec_ptr,16) /\
    nonoverlapping (htable_ptr,256) (out_ptr,128) /\
    nonoverlapping (htable_ptr,256) (xi_ptr,16) /\
    nonoverlapping (htable_ptr,256) (ivec_ptr,16) /\
    nonoverlapping (stackptr,80) (out_ptr,128) /\
    nonoverlapping (stackptr,80) (xi_ptr,16) /\
    nonoverlapping (stackptr,80) (ivec_ptr,16) /\
    nonoverlapping (stackptr,80) (in_ptr,128) /\
    nonoverlapping (stackptr,80) (key_ptr,240) /\
    nonoverlapping (stackptr,80) (htable_ptr,256) /\
    nonoverlapping (ivec_ptr,16) (word pc,4600) /\
    nonoverlapping (xi_ptr,16) (word pc,4600) /\
    nonoverlapping (out_ptr,128) (word pc,4600)
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) aes256_gcm_mc /\
           read PC s = word pc /\
           C_ARGUMENTS [in_ptr; word (8 * val len); out_ptr; xi_ptr;
                        ivec_ptr; key_ptr; htable_ptr] s /\
           read SP s = word_add stackptr (word 80) /\
           read X30 s = returnaddress /\
           read Q18 s = q18i /\
           byte_list_at pt_in in_ptr (word 128) s /\
           read (memory :> bytes128 out_ptr) s = co0 /\
           read (memory :> bytes128 (word_add out_ptr (word 16))) s = co1 /\
           read (memory :> bytes128 (word_add out_ptr (word 32))) s = co2 /\
           read (memory :> bytes128 (word_add out_ptr (word 48))) s = co3 /\
           read (memory :> bytes128 (word_add out_ptr (word 64))) s = co4 /\
           read (memory :> bytes128 (word_add out_ptr (word 80))) s = co5 /\
           read (memory :> bytes128 (word_add out_ptr (word 96))) s = co6 /\
           read (memory :> bytes128 (word_add out_ptr (word 112))) s = co7 /\
           read (memory :> bytes128 ivec_ptr) s = ivec /\
           read (memory :> bytes128 (word_add key_ptr (word 0))) s = rk0 /\
           read (memory :> bytes128 (word_add key_ptr (word 16))) s = rk1 /\
           read (memory :> bytes128 (word_add key_ptr (word 32))) s = rk2 /\
           read (memory :> bytes128 (word_add key_ptr (word 48))) s = rk3 /\
           read (memory :> bytes128 (word_add key_ptr (word 64))) s = rk4 /\
           read (memory :> bytes128 (word_add key_ptr (word 80))) s = rk5 /\
           read (memory :> bytes128 (word_add key_ptr (word 96))) s = rk6 /\
           read (memory :> bytes128 (word_add key_ptr (word 112))) s = rk7 /\
           read (memory :> bytes128 (word_add key_ptr (word 128))) s = rk8 /\
           read (memory :> bytes128 (word_add key_ptr (word 144))) s = rk9 /\
           read (memory :> bytes128 (word_add key_ptr (word 160))) s = rk10 /\
           read (memory :> bytes128 (word_add key_ptr (word 176))) s = rk11 /\
           read (memory :> bytes128 (word_add key_ptr (word 192))) s = rk12 /\
           read (memory :> bytes128 (word_add key_ptr (word 208))) s = rk13 /\
           read (memory :> bytes128 (word_add key_ptr (word 224))) s = rk14 /\
           read (memory :> bytes128 xi_ptr) s = xi /\
           read (memory :> bytes128 htable_ptr) s = word_swaphalves128 h /\
           read (memory :> bytes128 (word_add htable_ptr (word 16))) s = h1k /\
           read (memory :> bytes128 (word_add htable_ptr (word 32))) s = word_swaphalves128 (polyval_dot h h) /\
           read (memory :> bytes128 (word_add htable_ptr (word 48))) s = word_swaphalves128 (polyval_dot h (polyval_dot h h)) /\
           read (memory :> bytes128 (word_add htable_ptr (word 64))) s = h3k /\
           read (memory :> bytes128 (word_add htable_ptr (word 80))) s = word_swaphalves128 (polyval_dot (polyval_dot h h) (polyval_dot h h)) /\
           read (memory :> bytes128 (word_add htable_ptr (word 96))) s = word_swaphalves128 (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) /\
           read (memory :> bytes128 (word_add htable_ptr (word 112))) s = h5k /\
           read (memory :> bytes128 (word_add htable_ptr (word 128))) s = word_swaphalves128 (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) h) /\
           read (memory :> bytes128 (word_add htable_ptr (word 144))) s = word_swaphalves128 (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) h) h) /\
           read (memory :> bytes128 (word_add htable_ptr (word 160))) s = h7k /\
           read (memory :> bytes128 (word_add htable_ptr (word 176))) s = word_swaphalves128 (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) h) h) h) /\
           word_subword h1k (0,64):(64)word = karatsuba_mid h /\
           word_subword h1k (64,64):(64)word = karatsuba_mid (polyval_dot h h) /\
           word_subword h3k (0,64):(64)word = karatsuba_mid (polyval_dot h (polyval_dot h h)) /\
           word_subword h3k (64,64):(64)word = karatsuba_mid (polyval_dot (polyval_dot h h) (polyval_dot h h)) /\
           word_subword h5k (0,64):(64)word = karatsuba_mid (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) /\
           word_subword h5k (64,64):(64)word = karatsuba_mid (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) h) /\
           word_subword h7k (0,64):(64)word = karatsuba_mid (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) h) h) /\
           word_subword h7k (64,64):(64)word = karatsuba_mid (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) (polyval_dot h h)) h) h) h) h))
      (\s. read PC s = returnaddress /\
           read X0 s = len /\
           byte_list_at (aes256_gcm_encrypt (val len) pt_in ivec [rk0;rk1;rk2;rk3;rk4;rk5;rk6;rk7;rk8;rk9;rk10;rk11;rk12;rk13;rk14])
                        out_ptr len s /\
           read (memory :> bytes128 xi_ptr) s =
             gcm_final_xi (val len) pt_in ivec [rk0;rk1;rk2;rk3;rk4;rk5;rk6;rk7;rk8;rk9;rk10;rk11;rk12;rk13;rk14] xi h)
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [memory :> bytes(out_ptr,128);
                  memory :> bytes(xi_ptr,16);
                  memory :> bytes(ivec_ptr,16)] ,,
       MAYCHANGE [SP] ,,
       MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
       MAYCHANGE [memory :> bytes64 stackptr;
                  memory :> bytes64 (word_add stackptr (word 8));
                  memory :> bytes64 (word_add stackptr (word 16));
                  memory :> bytes64 (word_add stackptr (word 24));
                  memory :> bytes64 (word_add stackptr (word 32));
                  memory :> bytes64 (word_add stackptr (word 40));
                  memory :> bytes64 (word_add stackptr (word 48));
                  memory :> bytes64 (word_add stackptr (word 56));
                  memory :> bytes64 (word_add stackptr (word 64));
                  memory :> bytes64 (word_add stackptr (word 72))])`,
  REWRITE_TAC[byte_list_at] THEN
  ARM_ADD_RETURN_NOSTACK_TAC AES256_GCM_EXEC
    (REWRITE_RULE[byte_list_at; fst AES256_GCM_EXEC] AES256_GCM_ENCRYPT_CORRECT));;
