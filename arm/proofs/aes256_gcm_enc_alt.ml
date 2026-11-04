(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* AES-256-GCM encryption, 8-way kernel aes256_gcm_enc_alt.                  *)
(*                                                                           *)
(* Correctness and safety proofs for the kernel derived from AWS-LC's        *)
(* aesv8_gcm_8x_enc_256, which processes 8 blocks per main-loop iteration.   *)
(*                                                                           *)
(* For a bit length len_bits in X1 the kernel encrypts the                   *)
(* nb = gcm_wb_blocks len_bits whole 16-byte blocks at in_p into out_p in    *)
(* CTR mode (block j with the counter block ctr_block nonce (c+j), the ivec  *)
(* holding ctr_block nonce c), updates the GHASH accumulator at tag_p over   *)
(* the ciphertext, writes the next counter block back to the ivec and        *)
(* returns 16*nb.  A zero length or one that is not a multiple of 128 gives  *)
(* nb = 0: it returns 0 without memory access, so there is no                *)
(* partial-final-block masking.                                              *)
(*                                                                           *)
(* Proof structure (offsets of the -DNO_IBT code).  The core theorem         *)
(* AES256_GCM_ENC_ALT_CORRECT, pc+0x38 (after the prologue) to pc+0x1154     *)
(* (L256_enc_epilogue), for nb >= 1, is assembled from legs by block count:  *)
(* - nb <= 4: FAST1..FAST4, the small path (b.le L256_enc_small at pc+0x50); *)
(* - 5 <= nb <= 8: SETUP0 (pc+0x38 -> pc+0xee0), then TAIL_REM;              *)
(* - 9 <= nb <= 16: SETUP_G1 (pc+0x38 -> pc+0xa10), PREPRETAIL_GEN           *)
(*   (pc+0xa10 -> pc+0xee0), then TAIL_REM;                                  *)
(* - nb >= 17: SETUP_GEN (pc+0x38 -> pc+0x4c0), MAIN_LOOP (pc+0x4c0 ->       *)
(*   pc+0xa10, k = (nb-1) DIV 8 - 1 iterations), PREPRETAIL_GEN,             *)
(*   then TAIL_REM.                                                          *)
(* TAIL_REM (pc+0xee0 -> pc+0x1154) does the last 1..8 blocks through the    *)
(* arms TAIL_REM1..TAIL_REM8.  AES256_GCM_ENC_ALT_NOIBT_SUBROUTINE_CORRECT   *)
(* adds the length guards, the prologue and the epilogue; the _SAFE theorems *)
(* prove constant-time and memory safety along the same structure.           *)
(*                                                                           *)
(* The statements use the shared AES-GCM vocabulary of                       *)
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
(* trimmed code (the pad removed), and the default build's theorem is then   *)
(* derived from the -DNO_IBT one by ARM_ADD_IBT_RULE.                        *)

let aes256_gcm_enc_alt_tmc =
  define_trimmed "aes256_gcm_enc_alt_tmc" aes256_gcm_enc_alt_mc;;

let AES256_GCM_ENC_ALT_EXEC = ARM_MK_EXEC_RULE aes256_gcm_enc_alt_tmc;;

(* ========================================================================= *)
(* Local lemmas: reversefields equivalences, AES-256 and counter-block       *)
(* reconstruction, and the Karatsuba/GHASH reduction facts this kernel needs *)
(* on top of arm/proofs/utils/aes_gcm_common.ml.                             *)
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
(* first-15 EL-projection is a no-op; this holds without a `LENGTH rk = 15`  *)
(* premise.  It closes the final residual left on each ciphertext out-block  *)
(* conjunct after XOR_AES256_CIPHER_RECONSTRUCT + MAP +                      *)
(* WORD_REVERSEFIELDS_REVERSEFIELDS: those rewrites collapse the per-element *)
(* `word_reversefields` but leave the key as the explicit list `[EL 0 rk;    *)
(* ...; EL 14 rk]` rather than `rk`; this lemma folds it back, so `rk` stays *)
(* a free variable in the statement.                                         *)
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

(* ghash_reduce_raw is kept as a fold target.  Its body is the term that     *)
(* symbolic execution of the kernel's 8-instruction reduction (ldr d16,[x10] *)
(* through the final eor3 into v19) produces for Q19, so RECON_GRR can fold  *)
(* that raw reduce back into a named form by GSYM, in the main loop, the     *)
(* prepretail and the tail and small-path arms.  The shared                  *)
(* polyval_reduce_g2 arranges the same computation differently, so folding   *)
(* into it directly would first need the emitted term normalised.            *)
(* GHASH_REDUCE_RAW_IS_POLYVAL_G2 relates the two (ghash_reduce_raw p1 p2 p3 *)
(* = polyval_reduce_g2 p1 p3 p2), and the per-block folds reach polyval_dot  *)
(* through it, so no second GHASH semantics arises.                          *)

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
(* The Karatsuba multiply-accumulate fold.                                   *)
(*                                                                           *)
(* Given the three Karatsuba partial products of a single 128x128 carryless  *)
(* multiply a * b -- lo*lo, the cross term (a_lo^a_hi)*(b_lo^b_hi), and      *)
(* hi*hi -- feeding the reduce in the Q17 (hi) / Q18 (mid) / Q19 (lo) order  *)
(* the hardware uses (pmull -> lo lane, pmull2 -> hi lane, pmull of the      *)
(* eor'd halves -> cross/mid lane), the reduce computes exactly the polyval  *)
(* "dot" product polyval_dot a b = prop3(pmul a b):                          *)
(*                                                                           *)
(*        ghash_reduce_raw <lo*lo> <cross> <hi*hi>  =  polyval_dot a b       *)
(*                                                                           *)
(* Proof chain: GHASH_REDUCE_RAW_IS_POLYVAL_G2 turns ghash_reduce_raw into   *)
(* polyval_reduce_g2 (with the p2<->p3 swap that reorders cross/hi into g2's *)
(* hi,lo,mid slots), POLYVAL_REDUCE_G2 rewrites that to polyval_reduce_prop3 *)
(* of the reassembled 256-bit product, and GSYM PMUL_KARATSUBA_JOIN          *)
(* collapses the three partial products back into the single word_pmul a b   *)
(* inside polyval_dot.  The two REWRITE_TAC calls must stay separate:        *)
(* putting POLYVAL_REDUCE_G2 into the first rewrite list makes it fire       *)
(* before the swap settles and the proof diverges.                           *)
(*                                                                           *)
(* This is the per-block fold primitive the main-loop, prepretail and tail   *)
(* folds compose: each GHASH block is `word_pmul (acc_xor_block) (h_power    *)
(* ...)`; the batched multi-block accumulation over v8..v15 then closes with *)
(* GHASH_POLYVAL_ACC_BATCHED from common/polyval_ghash.ml (which reduces     *)
(* `ghash_polyval_acc h a (CONS b bs)` to a prop3 of the pmul + ghash_wide   *)
(* sum), and NIST_DOT_IS_POLYVAL_DOT / NIST_GHASH_IS_POLYVAL bridge the      *)
(* polyval accumulator to the nist_ghash tag.                                *)
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

(* ------------------------------------------------------------------------- *)
(* Stepping helpers.                                                         *)
(*                                                                           *)
(* The main-loop body reloads 8 plaintext blocks with `ldp q_even,q_odd,     *)
(* [x0],#32` (steps 263/295/303/304).  Because X0 post-increments, the       *)
(* second element of each later pair is read at `word_add (word_add in_p     *)
(* (word ...)) (word 16)`, where the offset arithmetic (e.g.                 *)
(* `(128*(i+1)+64)+48`) is not reduced to the literal `128*(i+1)+112` that   *)
(* the input-block reads use.  The stepper's memory resolution needs a       *)
(* syntactic address match, so the load stays opaque (`read(memory..)        *)
(* s_prev`) and DISCARD_OLDSTATE drops the ciphertext-register fact.  (The   *)
(* first ldp, blocks 0/1, resolves directly because X0 is still the base     *)
(* address there.)                                                           *)
(*                                                                           *)
(* LDP_STEP4_TAC, used only at the incremented ldps, re-derives the 8        *)
(* plaintext reads at the current state from the persistent quantified       *)
(* in-memory forall (INBLOCKS_TAC: the specific s0 facts get dropped, the    *)
(* forall does not), steps verbosely (no automatic discard), flattens the    *)
(* nested word_adds, normalises the offset arithmetic to the literal form    *)
(* (NORMOFF_RULE), resolves the now-matching memory reads and then discards  *)
(* the old state.  NORMOFF_RULE reduces `word (a + c1 + c2 + ...)` offsets;  *)
(* is_inp_memfact selects the memory equations used to substitute the loads. *)
(* NSTEP_G is the ordinary per-step chain (flatten + NORMOFF + subword) for  *)
(* all other instructions.                                                   *)
(* ------------------------------------------------------------------------- *)

let NORMOFF_RULE =
  CONV_RULE(ONCE_DEPTH_CONV(fun tm -> match tm with
      Comb(Const("word",_),_) ->
        (RAND_CONV(REWRITE_CONV[GSYM ADD_ASSOC] THENC DEPTH_CONV NUM_ADD_CONV)) tm
    | _ -> failwith "NORMOFF"));;

(* Selects only the freshly re-derived input-block reads (`read (memory :>   *)
(* bytesN ..) s = inblock <idx>`), which LDP_STEP4_TAC substitutes into the  *)
(* ldp second-element load.  The guard `is_var(fst(strip_comb rhs))` on the  *)
(* right-hand side is essential: without it every `read(memory..) s = v`     *)
(* fact would be selected, and REWRITE_RULE memfacts would rewrite each      *)
(* read-only key/mod/tag/ivec/htable fact with itself to `T`, deleting the   *)
(* read-only memory facts the postcondition needs (they are never            *)
(* re-derived, unlike the input reads, which INBLOCKS_TAC re-asserts at each *)
(* call).  Input reads carry the abstract value `inblock j` (a variable      *)
(* applied to arguments); all read-only facts carry constant-headed values   *)
(* (word_reversefields/word/...).                                            *)
let is_inp_memfact th =
  match concl th with
    Comb(Comb(Const("=",_), Comb(Comb(Const("read",_),
      Comb(Comb(Const(":>",_),Const("memory",_)),_)), _)), rhs) ->
        is_var(fst(strip_comb rhs))
  | _ -> false;;

(* ------------------------------------------------------------------------- *)
(* ASSUMPTION_STATE_UPDATE_TAC re-stamps every surviving assumption from the *)
(* previous state to the new one at each step with its right-hand side       *)
(* unchanged, so a fact already in subword-normal form comes back still      *)
(* normal.  WORD_SIMPLE_SUBWORD_CONV can only fire on a `word_subword _      *)
(* (NUMERAL,NUMERAL)` subterm (its outer match fails otherwise), so on a     *)
(* term without that shape TOP_DEPTH_CONV of it returns REFL and CONV_RULE   *)
(* is the identity.  SUBWORD_NORM_RULE therefore guards the conversion with  *)
(* a short-circuiting find_term for exactly that shape: for every theorem th *)
(* it returns what `CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) th`   *)
(* returns, without re-traversing the stable carried facts at every step.    *)
(* Used by NSTEP, NSTEP_G and NSTEP_GP below.                                *)
(* ------------------------------------------------------------------------- *)
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

(* has_wadd_nest: the same kind of guard for the word_add-nest flatten in    *)
(* NSTEP_GP (NSTEP_GP_WADD_RULE).  That REWRITE_RULE rewrites `word_add      *)
(* (word_add b (word m)) (word nn) -> word_add b (word(m+nn))`, which only   *)
(* fires on a register-pointer fact with the doubly nested word_add shape    *)
(* left by a post-increment ldr/str advancing X0/X2; on every other fact it  *)
(* returns the theorem unchanged, so the guard skips the rewrite there.      *)
let has_wadd_nest =
  can (find_term (fun t -> match t with
      Comb(Comb(Const("word_add",_),
             Comb(Comb(Const("word_add",_),_),
                  Comb(Const("word",_),_))),
           Comb(Const("word",_),_)) -> true
    | _ -> false));;

(* has_word_of_sum: the corresponding guard for NORMOFF_RULE in NSTEP_GP.    *)
(* NORMOFF_RULE only rewrites a `word (t)` subterm whose argument t is a sum *)
(* (`_ + _`), i.e. an offset not yet collapsed to a literal such as `word    *)
(* (128 * (k+1) + 16 + 32)`; facts without such a subterm are                *)
(* returned unchanged.                                                       *)
let has_word_of_sum =
  can (find_term (fun t -> match t with
      Comb(Const("word",_), Comb(Comb(Const("+",_),_),_)) -> true
    | _ -> false));;

(* WB_WADD_RULE: the word_add-nest flatten applied after each step by NSTEP  *)
(* and NSTEP_G (NSTEP_GP applies the same rewrite as NSTEP_GP_WADD_RULE,     *)
(* guarded by has_wadd_nest).                                                *)
let WB_WADD_RULE = REWRITE_RULE[WORD_RULE
  `word_add (word_add b (word m)) (word nn):int64 = word_add b (word(m+nn))`];;

(* NSTEP steps one instruction and then applies the word_add flatten,        *)
(* NORMOFF_RULE and SUBWORD_NORM_RULE to every assumption in a single        *)
(* RULE_ASSUM_TAC pass.  It has no is_ghash_acc guard: it is used where no   *)
(* large GHASH accumulator is live (the setup legs and the dispatch and AES  *)
(* part of FAST1..FAST4).                                                    *)
let NSTEP n =
  ARM_STEPS_TAC AES256_GCM_ENC_ALT_EXEC [n] THEN
  RULE_ASSUM_TAC(fun th -> SUBWORD_NORM_RULE (NORMOFF_RULE (WB_WADD_RULE th)));;

(* ------------------------------------------------------------------------- *)
(* Guarded body stepper.                                                     *)
(*                                                                           *)
(* The GHASH accumulators Q17/Q18/Q19 are word_join-headed Karatsuba lane    *)
(* sums.  WORD_SIMPLE_SUBWORD_CONV pushes word_subword into the joins,       *)
(* collapsing `word_subword(word_join a b)(0,64)` -> b etc.  That would      *)
(* destroy the `LO p1` / `ext p1` structure of ghash_reduce_raw's            *)
(* definition, and the body-end Q19 residual could then not be folded back   *)
(* to ghash_reduce_raw.                                                      *)
(*                                                                           *)
(* NSTEP_G is NSTEP with all three per-step normalisations skipped on any    *)
(* assumption that mentions read Q17, Q18 or Q19 (is_ghash_acc).  The        *)
(* word_add flatten and NORMOFF are the identity on those word_join /        *)
(* word_subword terms anyway, and skipping the subword pass keeps their      *)
(* ext/LO structure, so the final Q19 stays foldable.  The v0..v15 counter   *)
(* and ciphertext facts (all other registers) are normalised as by NSTEP.    *)
(* ------------------------------------------------------------------------- *)
let is_ghash_acc th =
  let c = concl th in
  can (find_term (fun t -> match t with
      Comb(Const("read",_), r) ->
        (match r with
         | Const("Q17",_) | Const("Q18",_) | Const("Q19",_) -> true
         | _ -> false)
    | _ -> false)) c;;

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
    (* Each obligation 8*(i+1)+b < nb follows from i < k and 8*(k+1) <= nb   *)
    (* alone, so only those two hypotheses are undischarged before ARITH_TAC *)
    (* (the same idiom as flag_arith in the main-loop body).                 *)
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
(* Flag-close lemmas for the main-loop body.                                 *)
(*                                                                           *)
(* The loop back-edge is a signed pointer compare `cmp x0,x5; b.lt` at       *)
(* pc+0x9a0/0xa0c: X0 = in_p + 128*(i+2) (four `ldp [x0],#32` past the loop  *)
(* top), X5 = end_p.  After the cheap-close ASM_REWRITE, the invariant's     *)
(* flag conjunct q(i+1) has been reduced to the raw NF<>VF biconditional     *)
(* over `word_sub X0 end_p`.  BRIDGE_GE recognises that biconditional as the *)
(* signed GE `ival end_p <= ival X0`; IV_ADD linearises each additive ival   *)
(* under the buffer-end no-wrap bound `val in_p + 128*(k+1) < 2^63`;         *)
(* INT/ARITH then reduces the whole thing to `i + 1 = k` using the body      *)
(* hypothesis `i < k`.  The no-wrap bound is an antecedent of MAIN_LOOP.     *)
(* ------------------------------------------------------------------------- *)

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
(* The pipeline-fill setup has two `cmp x0,x5; b.ge` guards, the tail check  *)
(* at 0x448/0x44c and the prepretail check at 0x480/0x4bc, both comparing    *)
(* the running input pointer X0 against the loop-end pointer                 *)
(*      X5 = ((bit_len DIV 8) - 1) & ~127  +  in_p                           *)
(* (hardware: sub x5,x5,#1; and x5,x5,#0xffffffffffffff80; add x5,x5,x0 at   *)
(* 0x6c/0x70/0x74, with x5 initialised to x9 = word(bit_len DIV 8), the byte *)
(* length 16*nb).  The first guard falls through for nb > 8 and the second   *)
(* for nb > 16, i.e. when k >= 1 with k = (nb-1) DIV 8 - 1.                  *)
(*                                                                           *)
(* X5_END_PTR_GEN: for 1 <= nb (and 16*nb < 2^64) the round-down mask gives  *)
(* X5 = in_p + 128*((nb-1) DIV 8).  With 8*(k+1) < nb <= 8*(k+2) this is the *)
(* loop-end pointer end_p = in_p + 128*(k+1) that MAIN_LOOP's antecedent     *)
(* pins (SETUP_X5_END_GEN below): the last group of 1..8 blocks is not run   *)
(* by the main loop but drained by the prepretail and the tail.  Proof via   *)
(* WORD_AND_NOT_MASK_WORD (the clear-low-7-bits lemma) + VAL_WORD_SUB_CASES. *)
(* ------------------------------------------------------------------------- *)
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

(* end_p = in_p + 128*(k+1) is strictly above in_p (signed), since 128*(k+1) *)
(* >= 128 > 0 and there is no signed wrap.  So the first guard's `cmp x0,x5; *)
(* b.ge` with X0 = in_p does not take the branch.  The second guard (X0 =    *)
(* in_p+128) is SETUP_GE_FALSE_2 below, which needs ~(k = 0).                *)
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

(* nb = 2 selector: `cmp x9,#0x20; b.eq L256_enc_small_2` at 0x1534/0x1538   *)
(* (inside L256_enc_small; x9 = word(16*nb)) is not taken for nb <> 2.       *)
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

(* The taken twin of DISPATCH_NOT_TAKEN: for nb = 2 the `cmp x9,#0x20; b.eq  *)
(* L256_enc_small_2` at 0x1534/0x1538 is taken (x9 = (128*2) DIV 8 = 32).    *)
let DISPATCH_TAKEN = prove
 (`!nb:num. nb = 2
    ==> (val (word_sub (word ((128 * nb) DIV 8):int64) (word 32)) = 0 <=> T)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(128 * nb) DIV 8 = 32` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[WORD_RULE `word_sub (word 32:int64) (word 32) = word 0`] THEN
  REWRITE_TAC[VAL_WORD_0]);;

(* The nb <= 4 entry test `cmp x9,#0x40; b.le L256_enc_small` at             *)
(* pc+0x4c/0x50 (x9 = word(16*nb)).  DISPATCH4_NOT_TAKEN and DISPATCH4_TAKEN *)
(* resolve the ZF disjunct of its condition (x9 = 64 iff nb = 4);            *)
(* DISPATCH_SMALL_NOT_TAKEN / DISPATCH_SMALL_TAKEN below resolve the signed  *)
(* less-than disjunct.  For nb = 4 the b.le is taken and the three b.eq      *)
(* tests in L256_enc_small fall through to L256_enc_small_4.                 *)
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

(* The taken twin: for nb = 4 the ZF disjunct of the b.le at 0x50 holds (x9  *)
(* = (128*4) DIV 8 = 64).                                                    *)
let DISPATCH4_TAKEN = prove
 (`!nb:num. nb = 4
    ==> (val (word_sub (word ((128 * nb) DIV 8):int64) (word 64)) = 0 <=> T)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(128 * nb) DIV 8 = 64` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[WORD_RULE `word_sub (word 64:int64) (word 64) = word 0`] THEN
  REWRITE_TAC[VAL_WORD_0]);;

(* nb = 1 selector: `cmp x9,#0x10; b.eq L256_enc_small_1` at 0x152c/0x1530,  *)
(* the first test inside L256_enc_small: not taken for nb <> 1, taken for    *)
(* nb = 1 (DISPATCH1_TAKEN).  x9 = word(16*nb).                              *)
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

(* nb = 3 selector: `cmp x9,#0x30; b.eq L256_enc_small_3` at 0x153c/0x1540.  *)
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

(* The nb <= 4 entry test `cmp x9,#0x40; b.le L256_enc_small`: ARM_STEP      *)
(* emits the b.le condition as the full `ZF \/ ~(NF<=>VF)`.  The ZF disjunct *)
(* `val(word_sub(word((128*nb)DIV8))(word 64))=0` is resolved by             *)
(* DISPATCH4_TAKEN / DISPATCH4_NOT_TAKEN (same #0x40 immediate); the two     *)
(* lemmas below resolve the remaining `~(NF<=>VF)` (signed less-than)        *)
(* disjunct.  IVAL_WORD_SUB_SMALL is a helper.                               *)
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

(* nb >= 5 (x9 = 16*nb >= 80 > 64): the signed less-than disjunct is F, so   *)
(* with DISPATCH4_NOT_TAKEN killing the ZF disjunct the b.le is not taken.   *)
(* Used by the SETUP legs and SETUP0.                                        *)
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

(* nb in {1,2,3} (x9 = 16*nb < 64): the signed less-than disjunct is T, so   *)
(* the b.le is taken (DISPATCH4_NOT_TAKEN gives F for the ZF disjunct).      *)
(* nb = 4 is taken by DISPATCH4_TAKEN alone.                                 *)
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

(* SETUP_BRANCH_COND_FALSE_GEN collapses the first guard's condition (the    *)
(* exact NF<>VF biconditional the stepper emits for `cmp x0,x5; b.ge` at     *)
(* 0x448/0x44c with X0 = in_p) to F, so the conditional PC resolves to the   *)
(* fall-through.  X5 is still the raw hardware form ((128*nb) DIV 8 - 1) &   *)
(* ~127 + in_p; SETUP_X5_END_GEN normalises it to end_p, and BRIDGE_GE +     *)
(* SETUP_GE_FALSE finish.  SETUP_BRANCH_COND_FALSE_2_GEN is the same for the *)
(* second guard (0x480/0x4bc, X0 = in_p+128, k <> 0).                        *)
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

(* SETUP_BRANCH_COND_TRUE_2: the second setup guard (b.ge at 0x4bc, the cmp  *)
(* with X0 = word_add in_p (word 128) after consuming one 8-block group) is  *)
(* taken for groups = 1 (k = 0): the round-down end_p = word_add in_p        *)
(* (word(128*(k+1))) = in_p+128 at k = 0, so X0 = end_p and the b.ge         *)
(* condition collapses to T, giving PC = 0xa10 (PREPRETAIL).  The            *)
(* counterpart of WB_BRANCH_COND_TRUE (first guard) for the second guard.    *)
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
(* the 8 plaintext blocks live at in_p + 16*j (j = 0..7), not at the loop    *)
(* body's 128*(i+1)+off.  SETUP_INBLOCKS_TAC re-asserts all 8 reads at state *)
(* `sname` from the persistent quantified input-forall; LDP_SETUP_TAC is     *)
(* LDP_STEP4_TAC with that variant.  The setup legs use it at all four `ldp  *)
(* [x0],#32` (steps 263/264/272/273), including the first, whose block-0     *)
(* load at the bare in_p needs the address normalisation below.              *)
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
   [(* Each obligation is b < nb for a literal b = 0..7, which follows from  *)
    (* 8 * (k + 1) <= nb alone, so only that hypothesis is undischarged      *)
    (* before ARITH_TAC (ASM_ARITH_TAC would consider every carried fact).   *)
    (* All callers (SETUP_GEN, SETUP_G1 and their _SAFE versions) have       *)
    (* that hypothesis.                                                      *)
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
     (* Normalise the setup input memfacts so that their addresses match the *)
     (* ldp reads: reduce `16*j` to a literal (NUM_MULT_CONV) and collapse   *)
     (* `word_add in_p (word 0)` to in_p (WORD_ADD_0).  Without this the     *)
     (* block-0 ldp read (at the bare in_p) does not match                   *)
     (* SETUP_INBLOCKS_TAC's address `word_add in_p (word (16*0))`, so that  *)
     (* load stays opaque (`read Q8 s = read(memory:>bytes128 in_p) s_prev`) *)
     (* and DISCARD_OLDSTATE drops the register fact.                        *)
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
(* GF(2)-linear word operations (word_subword, word_pmul by a constant,      *)
(* word_xor, word_join), hence additive.  These lemmas let the pipelined     *)
(* GHASH Q19 fold distribute the summed-lane hardware reduce over the 8      *)
(* in-flight blocks, so that each block individually matches                 *)
(* GHASH_REDUCE_RAW_KARATSUBA_IS_DOT.                                        *)
(*                                                                           *)
(* Proof recipe: WORD_BITWISE_RULE alone fails because it cannot see into an *)
(* opaque `word_pmul a w`; first distribute the pmuls with WORD_PMUL_XOR     *)
(* (HOL Light Library/words.ml) so that every pmul atom is shared across     *)
(* both sides, then push word_xor into the word_join lanes and split into    *)
(* 64-bit lanes closed by WORD_BITWISE_RULE (pure XOR ring, no bit-blasting  *)
(* of pmul).  A whole-goal WORD_BLAST is not practical (it bit-blasts the    *)
(* pmuls); the lane split is essential.                                      *)
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
(* Lane-order lemmas: reduce the summed lanes in the exact hardware lane     *)
(* order of the body-end residual.                                           *)
(*                                                                           *)
(* The reassembled body-end reduce is `ghash_reduce_raw P0 P1 P2` where each *)
(* Pl is an 8-term left-associated word_xor sum of per-block Karatsuba       *)
(* pieces, but the three lanes disagree on block order:                      *)
(*      P0 (lo.lo): blocks [1;0;2;3;4;5;6;7], b-lane subword(h^p)(0,64)      *)
(*      P1 (cross): blocks [1;0;3;2;5;4;7;6], b-lane karatsuba_mid(h^p)      *)
(*      P2 (hi.hi): blocks [1;0;2;3;4;5;6;7], b-lane subword(h^p)(64,64)     *)
(* (block j is paired with h-power h^{7-j}).  KARATSUBA_IS_DOT_HW handles    *)
(* the per-block cross-lane form, and REORD_CROSS AC-reorders the cross lane *)
(* [1;0;3;2..] -> [1;0;2;3..] so that the shared-order reduce applies; both  *)
(* are used by GHASH_REDUCE_RAW_DIST8_PLAIN.                                 *)
(* ------------------------------------------------------------------------- *)

(* Per block: the cross lane in the body uses `karatsuba_mid b` and the      *)
(* a-argument subword order (64,64),(0,64); normalise both to the form of    *)
(* GHASH_REDUCE_RAW_KARATSUBA_IS_DOT.                                        *)
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

(* AC-reorder a left-associated 8-term int128 word_xor from the cross-lane   *)
(* block order [1;0;3;2;5;4;7;6] to the shared order [1;0;2;3;4;5;6;7].      *)
let REORD_CROSS = prove
 (`word_xor (word_xor (word_xor (word_xor (word_xor (word_xor (word_xor
      (x1:int128) x0) x3) x2) x5) x4) x7) x6 =
   word_xor (word_xor (word_xor (word_xor (word_xor (word_xor (word_xor
      x1 x0) x2) x3) x4) x5) x6) x7`,
  CONV_TAC WORD_BITWISE_RULE);;

(* The block-0 reduce in the raw swapped-lane form the rem = 2..7 tail arms  *)
(* produce (the accumulator's two 64-bit halves crossed with cb0's: the      *)
(* store-order byteswap):                                                    *)
(*      lo.lo  = word_xor (subword sofar (64,64)) (subword cb0 (0,64))       *)
(*      hi.hi  = word_xor (subword sofar (0,64))  (subword cb0 (64,64))      *)
(*      cross  = word_xor <hi-shape> <lo-shape>                              *)
(* This reduces to polyval_dot (byteswap128 sofar (x) cb0) b.  The block-0   *)
(* accumulator byteswap is absorbed inside this lemma (ABBREV byteswap128    *)
(* sofar, so that the swap-lane rewrites do not re-fire on their own         *)
(* output): a global subword fold cannot be used directly on                 *)
(* those residuals.                                                          *)
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

(* Q19 fold: the 8-block distribution in the body's lane order with all      *)
(* blocks in the clean (non-crossed) form - block order [1;0;2;3;4;5;6;7] on *)
(* lo.lo/hi.hi, [1;0;3;2;5;4;7;6] on the cross lane - reduces to the XOR-sum *)
(* of the eight per-block polyval_dots.  It applies to the body-end Q19      *)
(* residual because the loop invariant states Q19 without a `byteswap128`    *)
(* wrapper (`read Q19 s = nist_ghash..8i`): under that invariant block 0     *)
(* enters the reduce as the ordinary `nist_cipher_block (x) sofar` with no   *)
(* store-order byteswap, so no block-0 crossing (as in KDOT_B0) is needed.   *)
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
(* Q19 GHASH-fold tactic.                                                    *)
(*                                                                           *)
(* Applied to the body-end Q19 residual conjunct                             *)
(*      `<raw ghash reduce of the 8 in-flight ciphertext blocks> =           *)
(*       nist_ghash H tag0 (list_of_seq nist_cipher_block (8i+8))`           *)
(* after splitting it off the raw post-FINAL_STATE conjunction but before    *)
(* the cheap close, whose WORD_SIMPLE_SUBWORD_CONV would destroy the         *)
(* foldable ext/LO structure.  The guarded stepper NSTEP_G is what keeps the *)
(* accumulator foldable through the 339 body steps.                          *)
(*                                                                           *)
(* Chain:                                                                    *)
(*   1. AC-swap the eor3 top XOR into ghash_reduce_raw's grouping;           *)
(*   2. GSYM ghash_reduce_raw (RECON_GRR);                                   *)
(*   3. reassemble the 8 cipherblocks and distribute the reduce over the 8   *)
(*      clean blocks with GHASH_REDUCE_RAW_DIST8_PLAIN;                      *)
(*   4. fold the RHS nist_ghash to a prop3 chain: NIST_GHASH_IS_POLYVAL +    *)
(*      8(i+1)=SUC^8(8i) + list_of_seq + APPEND + GHASH_ACC_APPEND, then     *)
(*      normalise the CONS SUC-form indices to +n (ADD1; GSYM ADD_ASSOC;     *)
(*      NUM_ADD_CONV) so that the batched ISPECL matches, then               *)
(*      GHASH_POLYVAL_ACC_BATCHED collapses it to the same prop3 sum.        *)
(* ------------------------------------------------------------------------- *)
let RECON_GRR = REWRITE_RULE[LET_DEF; LET_END_DEF] (GSYM ghash_reduce_raw);;

(* The invariant states the Q19 accumulator plain, not wrapped in a          *)
(* `byteswap128`: read Q19 s = nist_ghash..8i, rather than read Q19 s =      *)
(* byteswap128(nist_ghash..8i).  This kernel's main-loop body has only a     *)
(* leading `ext v19` (at 0x4f4) and no trailing ext (byteswap parity 0).     *)
(* With the plain invariant the body-end reduce (parity 0) matches the plain *)
(* RHS (parity 0) and the fold closes via the flat 8-`polyval_dot`-sum       *)
(* route; a byteswap-wrapped invariant (parity 1) could not, since byteswap  *)
(* identities only move the wrapper from side to side.  Block 0 enters the   *)
(* reduce as the ordinary clean `nist_cipher_block (x) sofar` (no            *)
(* store-order byteswap), so the fold uses GHASH_REDUCE_RAW_DIST8_PLAIN (all *)
(* blocks clean).                                                            *)
let Q19_FOLD_TAC =
  ONCE_REWRITE_TAC[WORD_BITWISE_RULE
    `word_xor (word_xor (x:int128) e) p = word_xor (word_xor x p) e`] THEN
  REWRITE_TAC[RECON_GRR] THEN
  (* Reassemble the 8 cipherblocks (the plain invariant leaves no            *)
  (* store-order byteswap on the accumulator to cancel).                     *)
  REWRITE_TAC[GSYM cipher_block] THEN REWRITE_TAC[CIPHER_BLOCK_NIST] THEN
  REWRITE_TAC[WORD_SUBWORD_REVERSEFIELDS] THEN
  SIMP_TAC[WORD_JOIN_COMBINE_LEMMA; ARITH] THEN
  REWRITE_TAC[WORD_SUBWORD_XOR] THEN REWRITE_TAC[WORD_SUBWORD_BYTESWAP128] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  REWRITE_TAC[WORD_SUBWORD_XOR] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  (* Re-fold the block-accumulator's distributed subwords (subword X (x)     *)
  (* subword Y -> subword(X (x) Y)) so that DIST8_PLAIN's lo.lo/hi.hi lanes  *)
  (* match, then distribute the reduce over the 8 clean blocks.              *)
  REWRITE_TAC[GSYM WORD_SUBWORD_XOR] THEN
  REWRITE_TAC[GHASH_REDUCE_RAW_DIST8_PLAIN] THEN
  (* RHS: fold nist_ghash..8(i+1) to prop3(pmul chain), plain, no byteswap. *)
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
  (* Both sides are now the same 8-block field element, byteswap-free:       *)
  (* collapse the LHS XOR-of-polyval_dot to a single prop3 (GF(2)-linearity, *)
  (* PROP3_XOR) and match the pmul sums by GF(2) XOR-AC.                     *)
  REWRITE_TAC[ADD_0] THEN
  REWRITE_TAC[polyval_dot] THEN
  REWRITE_TAC[GSYM PROP3_XOR] THEN
  AP_TERM_TAC THEN CONV_TAC WORD_BITWISE_RULE;;

(* MAIN_LOOP_OUT_DISJSPLIT: the 9-way case split of the out-forall bound j < *)
(* 8*((i+1)+1), proved once and used by the body's cheap close for each      *)
(* residual goal.                                                            *)
let MAIN_LOOP_OUT_DISJSPLIT = ARITH_RULE
  `j < 8 * ((i + 1) + 1) <=>
   j < 8 * (i+1) \/ j = 8*(i+1) \/ j = 8*(i+1) + 1 \/
   j = 8*(i+1) + 2 \/ j = 8*(i+1) + 3 \/ j = 8*(i+1) + 4 \/
   j = 8*(i+1) + 5 \/ j = 8*(i+1) + 6 \/ j = 8*(i+1) + 7`;;

(* ========================================================================= *)
(* The main loop: pc+0x4c0 -> pc+0xa10, k iterations.                        *)
(*                                                                           *)
(* The loop body (pc+0x4c0 .. the back-edge b.lt at pc+0xa0c) is             *)
(* software-pipelined: iteration i GHASH-folds the previous group of 8       *)
(* ciphertext blocks (blocks 8i..8i+7, held in v8..v15) while it encrypts    *)
(* and stores the next group (blocks 8(i+1)..8(i+1)+7).  So at the top of    *)
(* iteration i the machine has stored 8*(i+1) ciphertext blocks but GHASHed  *)
(* only 8*i of them; the invariant records this lag.                         *)
(*                                                                           *)
(* Unlike the 4-way kernels, whose loops count down a register and close     *)
(* with cbnz (ENSURES_WHILE_UP_TAC), the back-edge here is a                 *)
(* flag-conditional pointer compare: `cmp x0,x5` (pc+0x9a0) sets the flags   *)
(* and `b.lt` (pc+0xa0c) branches back while x0 < x5 (signed).  So the proof *)
(* uses ENSURES_WHILE_PUP_TAC (the post-test variant) with a flag conjunct   *)
(* `q i s`.  On ARM `b.lt` is taken iff ~(NF <=> VF) (Condition_LT in        *)
(* arm/proofs/instruction.ml), so the flag fact is                           *)
(*      (read NF s <=> read VF s) <=> (i = k)                                *)
(* i.e. GE (fall through) exactly on the last iteration, the ARM analogue of *)
(* the x86 `(read ZF s <=> i = k)` flag fact.                                *)
(*                                                                           *)
(* The precondition is the invariant at i = 0 (at pc+0x4c0), so the init     *)
(* subgoal is a reflexive 0-step ensures; the back-edge and exit subgoals    *)
(* step only the b.lt, which preserves every state conjunct.                 *)
(*                                                                           *)
(* Loop-carried SIMD state pinned by the invariant:                          *)
(* - v8..v15 = the previous group's ciphertext blocks 8i..8i+7, each         *)
(*   `word_xor (aes_ctr_block aes256_cipher c nonce rk (8i+j)) (inblock      *)
(*   (8i+j))`, the same form as the stored out-blocks (in iteration i the    *)
(*   stores `stp q8,q9,[x2],#32` .. write q8..q15 to blocks 8(i+1)+0 ..      *)
(*   8(i+1)+7); without them Q19 at the body end would be a GHASH of         *)
(*   unconstrained values;                                                   *)
(* - v0..v4 = rev8 (ctr_block nonce (8i+c+8 .. 8i+c+12)), the counter blocks *)
(*   encrypted in this iteration (the body's first use of each is an         *)
(*   `aese vN,v26`); v5..v7 are recomputed in the body with `rev32 vN,v30`;  *)
(* - Q30 = rev32 (ctr_block nonce (8i+c+13)), the next counter;              *)
(* - Q19 = nist_ghash .. (8*i), the GHASH of the blocks hashed so far.       *)
(*                                                                           *)
(* The antecedent 8 * (k + 1) <= nb keeps the four ciphertext stores (stp    *)
(* q8..q15,[x2],#32 at 0x9e4..0xa04) inside out_p, which the stepper needs   *)
(* in order to show that they do not modify the code.                        *)
(* ========================================================================= *)

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

    (* Subgoal 3: the body, a 339-instruction fused GHASH+AES pipeline.      *)
    (*                                                                       *)
    (* The body is stepped to ENSURES_FINAL_STATE_TAC with all eight         *)
    (* ciphertext register facts (read Q8..Q15 s339) intact.  Steps 1--339   *)
    (* are the body; the b.lt at 0xa0c (step 340) is the back-edge, handled  *)
    (* in subgoals 4 and 5.  The four plaintext reloads `ldp q,q,[x0],#32`   *)
    (* are steps 263/295/303/304: the first resolves directly, the three     *)
    (* post-incremented ones use LDP_STEP4_TAC, which supplies the word_add  *)
    (* flatten and offset normalisation their second-element addresses need  *)
    (* to match the input-block reads (otherwise DISCARD_OLDSTATE            *)
    (* drops them).                                                          *)
    (*                                                                       *)
    (* Counter pins: the setup advances the counter by 13, so at loop entry  *)
    (* v0..v4 = ctr_block nonce (8i+c+8 .. 8i+c+12) and Q30 = ctr(8i+c+13);  *)
    (* the invariant pins Q0..Q4/Q30 to those block-index values, and the    *)
    (* out-forall is stated in block-index aes_ctr_block form.               *)
    (*                                                                       *)
    (* The stores `stp q,q,[x2],#32` at steps 330/334/337/338 (pc            *)
    (* 0x9e4/0x9f4/0xa00/0xa04) write the new blocks 8i+8..8i+15.  The       *)
    (* incoming out-forall is carried across them by the ordinary stepper    *)
    (* and survives to s339; the 8 new blocks close from the concrete store  *)
    (* facts.  The Q19 GHASH fold is Q19_FOLD_TAC (above).  The other        *)
    (* conjuncts (X registers, key/htable/tag/ivec memory, Q30/Q31, the      *)
    (* Q0..Q4 counters, the Q8..Q15 ciphertext, the new out-blocks, flag,    *)
    (* PC) close in the cheap close: the case split on the bound             *)
    (* 8*((i+1)+1), eor3 AC-normalisation by WORD_BITWISE_RULE,              *)
    (* CTR_BLOCK_RECONSTRUCT_REV8/REV32 + WORD_SUBWORD_* +                   *)
    (* XOR_AES256_CIPHER_RECONSTRUCT + aes_ctr_block/ADD_CLAUSES, then       *)
    (* WORD_RULE, AP_THM/AP_TERM peeling and ARITH.                          *)
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
    (* Cheap-conjunct close.  The case-split bound is 8*((i+1)+1) (the       *)
    (* invariant's out-forall at i is j < 8*(i+1), so at i+1 it is           *)
    (* j < 8*(i+2)); the eor3 3-way store XOR is AC-normalised to the        *)
    (* XOR_AES256_CIPHER_RECONSTRUCT shape; then AES256_CIPHER_KEYLIST       *)
    (* collapses the residual explicit key list `[EL 0 rk;..;EL 14 rk]` back *)
    (* to `rk` (XOR_AES256_CIPHER_RECONSTRUCT + MAP leaves the list,         *)
    (* not `rk`).                                                            *)
    (*                                                                       *)
    (* The raw post-FINAL_STATE conjunction is split first, before the cheap *)
    (* close, so that the Q19 conjunct is folded while its ext/LO structure  *)
    (* is intact: the cheap close's WORD_SIMPLE_SUBWORD_CONV would destroy   *)
    (* it.  The per-goal dispatcher routes each conjunct:                    *)
    (* - Q19 (RHS headed by nist_ghash): Q19_FOLD_TAC;                       *)
    (* - the counter registers Q0..Q4 / Q30 (RHS headed by                   *)
    (*   word_reversefields): lane reconstruction + ARITH;                   *)
    (* - everything else: the cheap-close rewrites, which also do the        *)
    (*   out-forall case split.                                              *)
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
          the lane word_joins to ctr_block form, then discharge the
          counter-index equality (equal by arithmetic, not syntactically
          identical) by ARITH. *)
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
        (* collapse the explicit key list to rk before folding, then refold
           both sides to aes_ctr_block form.  A plain GSYM cipher_block fold
           is ambiguous under the c parameter (the inblock/i higher-order
           match spuriously picks c := 8*i+c), so instead close the
           ciphertext identity directly at the aes_ctr_block level: peel the
           word_xor and aes_ctr_block by AP_THM/AP_TERM and discharge the
           counter-index equality by ARITH.  Pointer conjuncts fall
           to WORD_RULE. *)
        REWRITE_TAC[AES256_CIPHER_KEYLIST] THEN
        REWRITE_TAC[aes_ctr_block; ADD_CLAUSES] THEN
        REPEAT CONJ_TAC THEN
        TRY(CONV_TAC WORD_RULE) THEN
        REPEAT(AP_THM_TAC ORELSE AP_TERM_TAC) THEN
        TRY ARITH_TAC) gl) THEN
    (* What remains after the dispatcher is the flag conjunct q(i+1) =       *)
    (* ((NF<=>VF) <=> (i+1 = k)) and the MAYCHANGE frame-subsumption goal,   *)
    (* split by REPEAT CONJ_TAC.  MAIN_LOOP's two end_p antecedents (end_p = *)
    (* word_add in_p (word (128*(k+1))) and the no-wrap bound val in_p +     *)
    (* 128*(k+1) < 2 EXP 63) pin the iteration count k.  The cheap close's   *)
    (* WORD_ADD normalisation splits the flag offsets to word_add (word      *)
    (* (128*i)) (word 256) (= X0 = in_p + 128*(i+2)) and word_add (word      *)
    (* (128*k)) (word 128) (= end_p, already substituted by ASM_REWRITE), so *)
    (* the flag close is not syntactic: it rewrites with BRIDGE_GE (the      *)
    (* NF<>VF biconditional = signed GE ival end_p <= ival X0), linearises   *)
    (* both additive ivals with IV_ADD under the no-wrap bound, and finishes *)
    (* by arithmetic using i < k.                                            *)
    REPEAT CONJ_TAC THEN
    (* Fire the flag close only on the flag-shaped goal, the one whose
       conclusion is `<flag biconditional> <=> (i + 1 = k)`; this keeps
       BRIDGE_GE off the large Q19 term.  flag_arith undischarges only the
       two needed hypotheses (`i < k` and the no-wrap bound) before a bare
       ARITH_TAC; ASM_ARITH_TAC would have to consider every hypothesis,
       including the large ciphertext and Q19 terms. *)
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
        (* the only residual reaching this branch is the MAYCHANGE
           frame-subsumption goal `(<accumulated>) s0 s339`.  The body
           overwrites all of Q8..Q15 (the in-flight ciphertext blocks),
           whose low 64 bits the ABI frame does not allow to change (d8-d15
           are callee-saved); so the MAIN_LOOP frame includes `MAYCHANGE
           [Q8;..;Q15]`, as in the 4-way kernels, and the subroutine's
           d8-d15 epilogue restores the low halves.  MONOTONE_MAYCHANGE_TAC
           discharges the subsumption (the 8 ciphertext stores
           bytes128(out_p+128*(i+1)+16m) lie in bytes(out_p,16*nb) by the
           `8*(k+1)<=nb` antecedent). *)
        else MONOTONE_MAYCHANGE_TAC) gl);

    (* Subgoal 4: back-edge taken (0 < i < k => b.lt branches back) *)
    REPEAT STRIP_TAC THEN
    ARM_SIM_TAC AES256_GCM_ENC_ALT_EXEC [1] THEN
    ASM_REWRITE_TAC[];

    (* Subgoal 5: exit fall-through (i = k => GE, b.lt not taken) *)
    REPEAT STRIP_TAC THEN
    ARM_SIM_TAC AES256_GCM_ENC_ALT_EXEC [1] THEN
    ASM_REWRITE_TAC[]]);;

(* SETUP_Q30_LANES: the lanes of the SETUP exit counter Q30 = rev32          *)
(* (ctr_block nonce (c+13)).  A whole-term `REWRITE_TAC[ctr_block] THEN      *)
(* WORD_BLAST` on the Q30 word_join would bit-blast the symbolic 96-bit      *)
(* nonce; lane by lane, each 32-bit lane shares the nonce structurally, so   *)
(* WORD_BLAST matches it without blasting.  CTR_BLOCK_RECONSTRUCT_REV32 then *)
(* assembles the full word_reversefields 32 (ctr_block nonce (c+13)).        *)
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
(* SETUP final-state reconstruction.                                         *)
(*                                                                           *)
(* After the SETUP drive reaches its exit, ENSURES_FINAL_STATE_TAC +         *)
(* ASM_REWRITE + REWRITE_TAC[htable_mem_8; htable_mem_4] + REPEAT CONJ_TAC   *)
(* split the postcondition, and SETUP_RECON_TAC_GEN (below) dispatches the   *)
(* residual goals by conclusion shape to the closers defined here.           *)
(* ------------------------------------------------------------------------- *)

(* Counter-lane reduction lemmas, shared by CIPHER_CLOSE and CTR_CLOSE.  The
   counter field of the byte-reversed ctr_block double-reverses to the raw
   counter; the nonce lanes byte-reverse to the nonce sub-lanes.  Proved by
   abstracting `word c` to a fresh word (WORD_BLAST cannot blast `word c`
   for a symbolic num c). *)
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

(* CIPHER_ID_TAC: the AES-input identity residual for block j (j = 1..7):
        word_xor (RF8 (aes256_cipher (RF8 <KS_j>) rk)) (inblock j) =
        word_xor (RF8 (aes256_cipher (ctr_block nonce (c+j)) rk)) (inblock j)
   where <KS_j> is the counter block SETUP builds with add/rev32.  Peel the
   outer word_xor (-) (inblock j), RF8 and aes256_cipher (-) rk by
   AP_THM/AP_TERM, leaving RF8 <KS_j> = ctr_block nonce (c+j), which
   ctr_block + WORD_BLAST closes directly: on the fully typed goal the
   symbolic 96-bit nonce appears identically on both sides, so WORD_BLAST
   does not blast it. *)
let CIPHER_ID_TAC =
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[ctr_block] THEN CONV_TAC WORD_BLAST;;

(* CIPHER_CLOSE: the MAIN_LOOP body ciphertext chain (in                     *)
(* AES256_GCM_ENC_ALT_MAIN_LOOP) specialised to SETUP.  Reduces the raw      *)
(* eor3/aese form                                                            *)
(*      word_xor (word_xor (inblock j) (aese..aese..rk13)) rk14              *)
(* to the aes256_cipher form.  For block 0 (counter ctr_block nonce c, no    *)
(* rev32 rebuild) it closes outright; for the out-forall's j = 1..7 it       *)
(* leaves the AES-input identity residual that CIPHER_ID_TAC then peels.     *)
let CIPHER_CLOSE =
  ONCE_REWRITE_TAC[WORD_BITWISE_RULE
    `word_xor (word_xor (inb:int128) ch) rk14 =
     word_xor ch (word_xor rk14 inb)`] THEN
  REWRITE_TAC[XOR_AES256_CIPHER_RECONSTRUCT] THEN
  ASM_REWRITE_TAC[MAP; WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
  (* The AES input is the raw rev8 counter-lane assembly for block K.
     Reconstruct it to ctr_block nonce (c+K) (CTR_LANE_LOW + CTR_NONCE_LANES
     + GSYM WORD_ADD + CTR_BLOCK_RECONSTRUCT_REV8/REV32, then cancel the
     outer double reverse), collapse the keys, refold to aes_ctr_block, then
     peel word_xor + aes_ctr_block and discharge the counter-index equality
     by ARITH.  (A plain GSYM cipher_block fold is higher-order ambiguous
     under c.) *)
  REWRITE_TAC[CTR_LANE_LOW; CTR_NONCE_LANES] THEN
  REWRITE_TAC[GSYM WORD_ADD; WORD_ADD_0] THEN
  REWRITE_TAC[CTR_BLOCK_RECONSTRUCT_REV8; CTR_BLOCK_RECONSTRUCT_REV32] THEN
  REWRITE_TAC[WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
  REWRITE_TAC[AES256_CIPHER_KEYLIST] THEN
  REWRITE_TAC[aes_ctr_block; ADD_CLAUSES] THEN
  (* normalise the 8*0+j indices so that the block-0 special case (bare
     counter c and inblock 0 on the LHS vs c+8*0+0 / inblock (8*0+0) on the
     RHS) matches. *)
  REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES] THEN
  TRY(REFL_TAC) THEN
  TRY(REPEAT(AP_THM_TAC ORELSE AP_TERM_TAC) THEN ARITH_TAC);;

(* CTR_CLOSE: Q0..Q4 (rev8) + Q30 (rev32) fresh-counter reconstruction.
   Reduce each lane to the CTR_BLOCK_RECONSTRUCT_REV8/REV32 pattern
   (SETUP_Q30_LANES for Q30; CTR_LANE_LOW + double-RF8 cancel +
   CTR_NONCE_LANES for Q0..Q4), combine the counter add (GSYM WORD_ADD),
   fold to ctr_block, then peel and close the counter-index equality by
   ARITH.  No whole-term WORD_BLAST: it would have to bit-blast the 128-bit
   counter term. *)
let CTR_CLOSE =
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[SETUP_Q30_LANES; CTR_LANE_LOW] THEN
  REWRITE_TAC[WORD_REVERSEFIELDS_REVERSEFIELDS] THEN
  REWRITE_TAC[CTR_NONCE_LANES] THEN
  REWRITE_TAC[GSYM WORD_ADD; WORD_ADD_0] THEN
  REWRITE_TAC[CTR_BLOCK_RECONSTRUCT_REV8; CTR_BLOCK_RECONSTRUCT_REV32] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;;

(* FLAG_CLOSE_GEN: the prepretail-check flag conjunct ((NF<=>VF)<=>(0=k)) at *)
(* i = 0.  BRIDGE_GE turns it into a signed compare, SETUP_X5_END_GEN        *)
(* rewrites the raw round-down X5 pointer to end_p, and SETUP_GE_FALSE_2     *)
(* (k >= 1) discharges the compare.                                          *)
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

(* SETUP_RECON_TAC_GEN routes each SETUP residual by its shape: the negated  *)
(* flag conjunct -> FLAG_CLOSE_GEN; the out-forall -> 8-way case split +     *)
(* CIPHER_CLOSE / CIPHER_ID_TAC; a nist_ghash RHS (Q19 = tag0) ->            *)
(* NIST_GHASH_NIL; word_xor = word_xor (the ciphertext registers) ->         *)
(* CIPHER_CLOSE; word_join = word_reversefields (the counters) -> CTR_CLOSE; *)
(* word_add (the pointer registers) -> WORD_RULE, the X4 word_ushr bridge or *)
(* SETUP_X5_END_GEN; any other read (the surviving read-only facts)          *)
(* -> ASM_REWRITE.                                                           *)
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
      else (* surviving read-only reads (keys/htable/ivec/tag/stack) *)
        (ASM_REWRITE_TAC[ARITH_RULE `(128 * nb) DIV 8 = 16 * nb`] THEN
         CONV_TAC NUM_REDUCE_CONV) gl
    else ASM_REWRITE_TAC[] gl;;

(* ========================================================================= *)
(* SETUP (pipeline fill): pc+0x38 -> pc+0x4c0.                               *)
(*                                                                           *)
(* Core entry pc+0x38 is just after the prologue (stack adjust, d8-d15       *)
(* spills, modulus-constant store and the X9/X16/X11/X10 set-up).  This      *)
(* region: 0x38-0xb4 builds the 8 CTR keystream inputs v0..v7 (rev32 of the  *)
(* counter), tests nb <= 4 (cmp x9,#0x40 / b.le L256_enc_small at 0x4c/0x50, *)
(* steps 6-7, not taken for nb >= 5), computes the loop-end pointer X5       *)
(* (0x6c-0x74) and loads rk0/rk1; the tag is loaded into Q19 at 0xb8 (ld1    *)
(* v19; ext; rev64, giving tag0 itself); 0xc8-0x440 runs the 14 AES rounds   *)
(* on v0..v7; 0x444 sets X4 = in_p + byte_len (the input end pointer) and    *)
(* 0x44c does the b.ge tail check (not taken for nb >= 9); 0x450-0x4b8 loads *)
(* the 8 plaintext blocks (four ldp q,q,[x0],#32), eor3s them with the       *)
(* keystream and rk14 into ciphertext, rev32s the next counters into v0..v4  *)
(* and stores the 8 ciphertext blocks (four stp q,q,[x2],#32); 0x4bc does    *)
(* the b.ge prepretail check (not taken for nb >= 17) and falls through to   *)
(* the main-loop top 0x4c0.                                                  *)
(*                                                                           *)
(* SETUP_GEN establishes MAIN_LOOP's precondition at i = 0 for k >= 1, with  *)
(* 8*(k+1) < nb <= 8*(k+2), i.e. k = (nb-1) DIV 8 - 1.  The loop body uses   *)
(* only X0, X2, X5, X6, X10 and X11, so X4 = in_p+16*nb (the input end       *)
(* pointer, used by the tail) and X16 = ivec_p (for the final                *)
(* `str q30,[x16]` ivec writeback) are set up here and carried through the   *)
(* loop unchanged.                                                           *)
(*                                                                           *)
(* mod_p is the on-stack modulus constant at stackpointer+0x40               *)
(* (add x10,sp,#0x40 at 0x34; the 0xc2..0 constant is stored there at 0x30). *)
(* The core is stated with mod_p = word_add stackpointer (word 0x40); the    *)
(* subroutine wrapper ties stackpointer to the caller's SP - 0x50.           *)
(*                                                                           *)
(* The drive is 290 steps: NSTEP 1-7 (the b.le at step 7 resolved by         *)
(* DISPATCH4_NOT_TAKEN and DISPATCH_SMALL_NOT_TAKEN), 8-261, NSTEP 262 = the *)
(* b.ge at 0x44c (SETUP_BRANCH_COND_FALSE_GEN), LDP_SETUP_TAC at the four    *)
(* ldps (steps 263/264/272/273; the stps are steps 278/279/286/288), and     *)
(* NSTEP 290 = the b.ge at 0x4bc (SETUP_BRANCH_COND_FALSE_2_GEN).  The final *)
(* state is then closed by SETUP_RECON_TAC_GEN, like the MAIN_LOOP body's    *)
(* cheap close: XOR_AES256_CIPHER_RECONSTRUCT + aes_ctr_block/ADD_CLAUSES +  *)
(* AES256_CIPHER_KEYLIST for Q8..Q15, CTR_BLOCK_RECONSTRUCT_* for Q0..Q4 and *)
(* Q30, and Q19 = nist_ghash..(8*0) = tag0.                                  *)
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
(* SETUP_G1: the g = 1 (k = 0) pipeline-fill setup leg, nblocks 9..16.  Its  *)
(* drive is SETUP_GEN's except that at step 290 the second guard (b.ge at    *)
(* 0x4bc) is taken, because end_p = in_p+128*(0+1) = in_p+128 = X0, so the   *)
(* PC goes to pc+0xa10 (PREPRETAIL) instead of the main-loop top pc+0x4c0;   *)
(* SETUP_BRANCH_COND_TRUE_2 discharges it.  The postcondition is             *)
(* PREPRETAIL_GEN's precondition at pc+0xa10 in the k = 0 (8*0) form,        *)
(* without the flag conjunct.                                                *)
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
(* PREPRETAIL (pipeline drain): pc+0xa10 -> pc+0xee0 (L256_enc_tail).        *)
(*                                                                           *)
(* The software pipeline runs one 8-block GHASH group behind the ciphertext  *)
(* stores.  At MAIN_LOOP exit (i = k) the last in-flight group (ciphertext   *)
(* blocks 8k..8k+7, held in v8..v15) has been stored but not yet GHASHed;    *)
(* Q19 still holds nist_ghash..(8*k).  PREPRETAIL folds that group into Q19, *)
(* advancing it to nist_ghash..(8*(k+1)), and runs the AES rounds of the     *)
(* next 8 counter blocks (v0..v7, up to the final rk14 XOR) that the tail    *)
(* consumes.  It performs no ciphertext stores and no plaintext loads (all   *)
(* `[x0]`/`[x2]` accesses are in the tail, at or after 0xee0) and leaves     *)
(* every general-purpose register (X0, X2, X3, X4, X5, X6, X10, X11, X16)    *)
(* unchanged: no instruction in 0xa10..0xedc writes them.                    *)
(*                                                                           *)
(* The PREPRETAIL precondition is the MAIN_LOOP postcondition at i = k (the  *)
(* state at pc+0xa10), plus aligned_bytes_loaded; ENSURES_SEQUENCE_TAC joins *)
(* them in the composition.  The Q19 drain fold has the same structure as    *)
(* the MAIN_LOOP body's (a leading `ext v19`, at 0xa78 here, the same        *)
(* pmull/pmull2/eor3 Karatsuba chain, the final reduce                       *)
(* `eor3 v19,v19,v21,v17` at 0xec0, and no trailing `ext v19`), so it closes *)
(* by Q19_FOLD_TAC_K, which is Q19_FOLD_TAC with i -> k.  The drain's reduce *)
(* reads v18 through pmull (0xe64, into Q17) and through ext (0xe9c, into    *)
(* Q21); NSTEP_GP (below) also protects Q20/Q21 from the per-step subword    *)
(* normalisation, so both copies of v18 keep the same form and RECON_GRR can *)
(* fold the reduce.  With NSTEP_GP the accumulators Q17/Q18/Q19 stay         *)
(* concrete through the 308-step drive; after FINAL_STATE + REPEAT CONJ_TAC  *)
(* ten residuals remain: the Q30 counter, the Q19 fold and the eight v0..v7  *)
(* AES reconstructions (PP_DISPATCH; the rest close by ASM_REWRITE).         *)
(*                                                                           *)
(* Exit state (after the 308-step drive):                                    *)
(* - PC = pc+0xee0; X0..X16 and Q31 preserved;                               *)
(* - Q28 = word_reversefields 8 (EL 14 rk) (rk14, the tail's final           *)
(*   round key);                                                             *)
(* - Q30 = word_reversefields 32 (ctr_block nonce (8*k+c+16)): the three     *)
(*   `add v30` at 0xa18/0xa24/0xea8 each add 1 to the counter lane;          *)
(* - Q0..Q4 = the aese/aesmc chain with rk0..rk13 (the state before the      *)
(*   final rk14 XOR) over word_reversefields 8 (ctr_block nonce (8*k+c+8+j)) *)
(*   (the counter blocks pinned by the loop invariant);                      *)
(* - Q5..Q7 = the same chain over the counters 8*k+c+13 .. 8*k+c+15, built   *)
(*   with rev32 from the incremented v30.                                    *)
(* The postcondition states v0..v7 in forms XOR_AES256_CIPHER_RECONSTRUCT    *)
(* reduces (word_xor (read Qj) rk14 = word_reversefields 8 (aes256_cipher    *)
(* ...)), matching the setup's convention and what the tail consumes (the    *)
(* tail's first `eor3 v9,v8,v0,v29` XORs v0 with v29, a copy of v28 = rk14). *)
(* ========================================================================= *)

(* Extended-guard stepper for the drain.  NSTEP_G protects Q17/Q18/Q19 from  *)
(* the per-step WORD_SIMPLE_SUBWORD_CONV; the drain also needs Q20/Q21       *)
(* protected, because its reduce takes ext(v18) -> Q21 and pmull(v18) -> Q17 *)
(* at different steps (0xe9c and 0xe64): if Q21's subwords were collapsed,   *)
(* the two copies of the mid-accumulator v18 would differ and RECON_GRR      *)
(* could not match.                                                          *)
let is_ghash_acc_pp th =
  let c = concl th in
  can (find_term (fun t -> match t with
      Comb(Const("read",_), r) ->
        (match r with
         | Const("Q17",_) | Const("Q18",_) | Const("Q19",_)
         | Const("Q20",_) | Const("Q21",_) -> true
         | _ -> false)
    | _ -> false)) c;;

(* The word_add-nest flatten of NSTEP_GP (the same rewrite as WB_WADD_RULE). *)
let NSTEP_GP_WADD_RULE = REWRITE_RULE[WORD_RULE
  `word_add (word_add b (word m)) (word nn):int64 = word_add b (word(m+nn))`];;

(* NSTEP_GP: the stepper for the prepretail, the tail arms and the small     *)
(* path tails.  It skips all three per-step normalisations on assumptions    *)
(* that mention the accumulators Q17..Q21 (is_ghash_acc_pp): the word_add    *)
(* flatten and NORMOFF are the identity on them and the subword pass must    *)
(* not touch them.  On the other facts the word_add flatten and NORMOFF run  *)
(* only when has_wadd_nest / has_word_of_sum find their redex, since they    *)
(* are no-ops otherwise.                                                     *)
let NSTEP_GP n =
  ARM_STEPS_TAC AES256_GCM_ENC_ALT_EXEC [n] THEN
  RULE_ASSUM_TAC(fun th ->
    if is_ghash_acc_pp th then th
    else
      let th1 = if has_wadd_nest (concl th) then NSTEP_GP_WADD_RULE th else th in
      let th2 = if has_word_of_sum (concl th1) then NORMOFF_RULE th1 else th1 in
      SUBWORD_NORM_RULE th2);;

(* The Q19 drain fold: Q19_FOLD_TAC with the accumulator index i -> k (the   *)
(* drain folds the last in-flight 8-block group at loop bound k, advancing   *)
(* Q19 from nist_ghash..(8*k) to nist_ghash..(8*(k+1))).  The fold has the   *)
(* same structure as the main-loop body's; see Q19_FOLD_TAC for the route.   *)
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

(* Q30 counter closer (the drain does three `add v30`, so the exit counter   *)
(* is 8*k+c+16).                                                             *)
let PP_CTR_CLOSE =
  REWRITE_TAC[WORD_SUBWORD_REVERSEFIELDS_32; WORD_SUBWORD_CTR_BLOCK_32] THEN
  REWRITE_TAC[GSYM WORD_ADD; WORD_ADD_0] THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
  REWRITE_TAC[CTR_BLOCK_RECONSTRUCT_REV32] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;;

(* v0..v7 AES closer.  v0..v4 are pinned as word_reversefields 8 (ctr_block  *)
(* ..), so AES256_CIPHER_RECONSTRUCT + MAP + AES256_CIPHER_KEYLIST close     *)
(* them directly.  v5..v7 are freshly rev32'd from the incremented v30, so   *)
(* the AES reconstruction leaves a plaintext residual word_reversefields 8   *)
(* (aes256_cipher <rev-lanes> rk) = ..(ctr_block ..), which the counter-lane *)
(* reconstruction (WORD_SUBWORD_*32 + CTR_BLOCK_RECONSTRUCT_REV8 +           *)
(* WORD_REVERSEFIELDS_REVERSEFIELDS) folds; the TRY makes it a no-op for     *)
(* v0..v4 (already closed).                                                  *)
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
(* PREPRETAIL_GEN: the pipeline-drain theorem, for every k including k = 0   *)
(* (the g = 1 leg, nblocks 9..16, where the main loop runs zero times and    *)
(* the prepretail and the tail do all the work).  The proof is a             *)
(* straight-line drive, MAP_EVERY NSTEP_GP (1--308), then FINAL_STATE and    *)
(* PP_DISPATCH; nothing in it depends on k beyond the symbolic 8*k.          *)
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
  (* Drive the 308-instruction drain with the extended-guard stepper         *)
  (* NSTEP_GP (it protects Q17..Q21, so the reduce's mid accumulator v18     *)
  (* stays unnormalised in both the pmull and the ext position), then        *)
  (* FINAL_STATE + REPEAT CONJ_TAC + the shape-routed dispatcher PP_DISPATCH *)
  (* (Q19 fold / Q30 counter / v0..v7 AES / ASM_REWRITE).                    *)
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
(* TAIL cascade: pc+0xee0 -> pc+0x1154.                                      *)
(*                                                                           *)
(* The tail handles the last r = nb - 8*g blocks (1 <= r <= 8), where 8*g    *)
(* blocks have been stored and GHASHed before it (g = k+1 after the          *)
(* prepretail, g = 0 after SETUP0).  Their keystreams are in Q0..Q7 at entry *)
(* (all AES rounds but the final rk14 XOR).  It loads, encrypts and stores   *)
(* the r blocks, folds them into the GHASH accumulator Q19, does the final   *)
(* GF(2^128) reduce and the two memory writebacks:                           *)
(*      str q30,[x16]  -> ivec = word_reversefields 8 (ctr_block .. (nb+c))  *)
(*      st1 {v19},[x3] -> tag  = word_reversefields 8 (nist_ghash .. nb)     *)
(*                                                                           *)
(* At entry the remaining-bytes register x5 = X4 - X0 (sub x5,x4,x0 at       *)
(* 0xee4) is 16*r.  The cascade selects the arm: `cmp x5,#0x70` at 0xefc and *)
(* `b.gt` at 0x1424 take L256_enc_exact8_drain (0x1178) for r = 8, the       *)
(* `b.eq` at 0x142c takes L256_enc_rem2_drain (0x1434) for r = 2, and the    *)
(* other r slide through the cmp/b.gt chain from L256_enc_tail_slides        *)
(* (0xf08) to their entry: L256_enc_blocks_more_than_6/5/4 for r = 7/6/5,    *)
(* L256_enc_rem4_drain for r = 4, L256_enc_blocks_more_than_2 for r = 3 and  *)
(* L256_enc_blocks_less_than_1 for r = 1; r = 5..7 then finish on            *)
(* L256_enc_rem4_drain.  TAIL_REM1..TAIL_REM8 prove the arms and TAIL_REM    *)
(* combines them.  Every block is a full block: there is no                  *)
(* partial-block masking.                                                    *)
(*                                                                           *)
(* The Q19 fold is of the same kind as in PREPRETAIL and MAIN_LOOP           *)
(* (pmull/pmull2/eor3 Karatsuba over the fresh cipherblocks, then the        *)
(* reduce), so it reuses that machinery (NSTEP_GP, RECON_GRR, a              *)
(* Q19_FOLD_TAC-style fold).                                                 *)
(*                                                                           *)
(* The return value X0 = X9 = 16*nb (mov x0,x9 at 0x1154) is set by the      *)
(* epilogue: the tail ends at pc+0x1154 with X9 = word (16*nb), and the      *)
(* subroutine theorem, which also covers the epilogue, asserts the           *)
(* return value.                                                             *)
(* ========================================================================= *)

(* Store-permutation lemmas: TAG_STORE_REV64 is the `ext v19,#8` + `rev64    *)
(* v19` byte permutation the tail applies before `st1 {v19},[x3]`, equal to  *)
(* word_reversefields 8; IVEC_STORE_REV32 is the rev32 v30 permutation       *)
(* before `str q30,[x16]`.  Both by BITBLAST.                                *)
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

(* The small paths (FAST1..FAST4) end in the shared L256_enc_small_reduce,   *)
(* which replaces the `ext v19,#8; rev64 v19` byte reverse with a single     *)
(* `tbl v19.16b,{v19.16b},v12.16b` (at 0x18dc), v12 holding the reverse      *)
(* index word 0x000102030405060708090a0b0c0d0e0f.  arm_TBL (datasize 128)    *)
(* yields `usimd16 (\x. word_subword Q19 (8*val x,8)) Q12`; with that index  *)
(* in Q12 this equals word_reversefields 8 Q19, so these tails close with    *)
(* TAG_STORE_REV64 like the ext+rev64 path.                                  *)

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

(* KS_SOLVE inverts a keystream fact `word_xor (read Qj s) rk14 = ks` into   *)
(* `read Qj s = word_xor ks rk14`, so that the ciphertext eor3 outputs are   *)
(* state-independent.                                                        *)
let KS_SOLVE = prove
 (`!a b c:int128. word_xor a b = c ==> a = word_xor c b`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  CONV_TAC WORD_BITWISE_RULE);;

(* Eta/beta collapse for the accumulator-block (block-0) artifact.  The      *)
(* batched fold's block-0 index 8*g+0 reduces to 8*g, and higher-order       *)
(* matching in GHASH_POLYVAL_ACC_BATCHED leaves the `inblock` slot as a      *)
(* constant lambda `nist_cipher_block nonce rk (\x. inblock (8*g)) (8*g)`,   *)
(* beta-equal to the clean form but opaque to WORD_BITWISE_RULE (which       *)
(* cannot see through nist_cipher_block).  ETA_CONV does not apply (the      *)
(* lambda is constant, not \x. f x), so this targeted beta-collapse lemma is *)
(* used before the final AP_TERM.                                            *)
let NCB_ETA = prove
 (`nist_cipher_block aes256_cipher c nonce rk (\x:num. inb (m:num)) m =
   nist_cipher_block aes256_cipher c nonce rk inb m`,
  REWRITE_TAC[nist_cipher_block; cipher_block] THEN CONV_TAC(DEPTH_CONV BETA_CONV));;

(* fold_q19_at lhs n tac: replace the assumption `lhs = <raw reduce>` by     *)
(* `lhs = nist_ghash .. (list_of_seq .. n)`, proving the equation between    *)
(* the two right-hand sides with tac (the arm's Q19 fold tactic).            *)
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

(* DISCARD_DEAD_REDUCE_SCRATCH, used in each tail arm right after the Q19    *)
(* fold, drops the Q-registers that are dead from there on: every register   *)
(* except Q0..Q7 (the keystreams), Q19 (the folded tag) and Q30 (the ivec    *)
(* counter) is neither read by the remaining ext/rev64/st1 steps nor         *)
(* mentioned by the postcondition or the frame, so ARM_STEPS_TAC need not    *)
(* re-stamp their large terms.  The list has 19 registers (Q8..Q18,          *)
(* Q20..Q26, Q29); Q27, Q28 and Q31 are not in it (TAIL_REM8 drops them      *)
(* separately where they die).                                               *)
let DISCARD_DEAD_REDUCE_SCRATCH : tactic =
  DISCARD_REGS
    ["Q17"; "Q18"; "Q20"; "Q21"; "Q22"; "Q23"; "Q24"; "Q25"; "Q26";
     "Q29"; "Q16"; "Q8"; "Q9"; "Q10"; "Q11"; "Q12";
     "Q13"; "Q14"; "Q15"];;

(* DISCARD_DEAD_KEYMEM drops the round-key memory facts `read (memory :>     *)
(* bytes128 (word_add key_p (word (16*i)))) s = word_reversefields 8 (EL i   *)
(* rk)`, i = 0..14, which DISCARD_REGS does not touch (its reg_of returns "" *)
(* for a `memory :> ..` component).  The tail runs no AES rounds: the        *)
(* keystreams Q0..Q7 are already computed at entry (the precondition's       *)
(* `word_xor (read Qj) rk14 = word_reversefields 8 (aes256_cipher ..)`), no  *)
(* instruction in 0xee0..0x14e0 uses x11, and neither the postcondition nor  *)
(* the frame mentions key_p memory.  TAIL_REM8 drops these facts right after *)
(* the 9-step prefix, so that they are not carried through the rest of       *)
(* the drive.                                                                *)
let DISCARD_DEAD_KEYMEM : tactic =
  REPEAT(FIRST_X_ASSUM(fun th ->
    let c = concl th in
    if is_eq c &&
       can (find_term (fun t -> t = `key_p:int64`)) (lhs c) &&
       can (find_term (fun t -> match t with Const("memory",_) -> true | _ -> false))
           (lhs c)
    then K ALL_TAC th else fail()));;

(* DISCARD_DEAD_HTABLE drops the six htable facts at offsets 96..176         *)
(* (byteswap128 (h_power h 4..7) and the karatsuba_mid pairs for h_power     *)
(* 4..7) of the 12 that htable_mem_8 contributes (offsets 0, 16, .., 176).   *)
(* The 9-step tail prefix loads those offsets into q20..q25 (the ldps at     *)
(* 0xee0/0xeec/0xef4); after it no instruction reads them (the drains reload *)
(* only offsets 0..80) and the postcondition mentions no htable memory, so   *)
(* TAIL_REM8 drops them right after the prefix.  DISCARD_DEAD_KEYMEM and     *)
(* DISCARD_REGS miss them (one keys on key_p, the other on                   *)
(* register components).                                                     *)
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

(* ========================================================================= *)
(* Tail cascade arm rem=1 (nblocks = 8*g+1), lands at 0x10f0                 *)
(* (L256_enc_blocks_less_than_1).                                            *)
(*                                                                           *)
(* One fresh block (8*g) is folded into the GHASH accumulator with a         *)
(* single-block APPEND (no batched reduce).  rem = 1 needs no Q18/Q27 pin.   *)
(*                                                                           *)
(* At the tail entry x5 = X4 - X0 = (in_p+16*nb) - (in_p+128*g) = 16*r       *)
(* (TAIL_X5_REM1..TAIL_X5_REM7, TAIL_X5_128_G); once it is rewritten to the  *)
(* literal, the stepper resolves the cmp/b.gt/b.eq cascade to the r arm with *)
(* concrete flags, so no separate branch-discharge lemma is needed.          *)
(* ========================================================================= *)

let TAIL_X5_REM1 = prove
 (`!(in_p:int64) g.
     word_sub (word_add in_p (word (16 * (8 * g + 1))))
              (word_add in_p (word (128 * g))) = word 16:int64`,
  REPEAT STRIP_TAC THEN CONV_TAC WORD_RULE);;

(* Single-block Q19 fold (the front end is shared with TAIL_Q19_FOLD_G, with *)
(* a single-block APPEND instead of GHASH_POLYVAL_ACC_BATCHED).  Proves that *)
(* the raw single-block ghash_reduce at s82 equals the compact               *)
(* nist_ghash..(8*g+1): RECON_GRR exposes ghash_reduce_raw, the block        *)
(* normalises to nist_cipher_block(8*g), KARATSUBA_IS_DOT_HW collapses the   *)
(* three Karatsuba pmulls to a single polyval_dot, and the one-element       *)
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

(* Fold `read Q19 s82` (the raw single-block reduce) to the compact          *)
(* nist_ghash..(8*g+1) in place, as TAIL_REM8's Q19 fold does.               *)
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
  (* Assert the single tail input block; without this the plaintext load     *)
  (* stays a raw memory read and the whole ciphertext/GHASH chain drops.     *)
  SUBGOAL_THEN
   `read (memory :> bytes128 (word_add in_p (word (128 * g)))) s0 =
    inblock (8 * g)`
  ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `128 * g = 16 * (8 * g)`] THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  (* Invert the keystream fact so that the ciphertext eor3 output is         *)
  (* state-independent.                                                      *)
  RULE_ASSUM_TAC(fun th -> try MATCH_MP KS_SOLVE th with Failure _ -> th) THEN
  (* Steps 1..9: the tail prefix (x5 = X4 - X0 at 0xee4); rewriting x5 to    *)
  (* word 16 lets the cascade resolve concretely to the rem = 1 arm          *)
  (* (L256_enc_blocks_less_than_1 at 0x10f0).                                *)
  MAP_EVERY NSTEP_GP (1--9) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[TAIL_X5_REM1]) THEN
  (* Steps 10..82: the cascade fall-through, the single-block fold and the   *)
  (* reduce, up to the final reduce eor3 at 0x1144 (s82: read Q19 = the raw  *)
  (* single-block reduce).                                                   *)
  MAP_EVERY NSTEP_GP (10--82) THEN
  (* Fold Q19 to the compact nist_ghash..(8*g+1) before ext/rev64/store      *)
  (* (otherwise the rev64 of the raw reduce grows very large), then drop the *)
  (* dead reduce scratch.                                                    *)
  FOLD_Q19_REM1 THEN
  DISCARD_DEAD_REDUCE_SCRATCH THEN
  (* Steps 83..85: ext, rev64 and st1 (tag) at 0x1148/0x114c/0x1150; the PC  *)
  (* is then pc+0x1154.                                                      *)
  MAP_EVERY NSTEP_GP (83--85) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  (* ivec store: 7 `sub v30` in the cascade take 8g+c+8 to 8g+c+1 = nb+c. *)
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
  (* tag store: read(tag_p) = rev8 (nist_ghash..nb), Q19 being folded. *)
  CONJ_TAC THENL
   [REWRITE_TAC[TAG_STORE_REV64] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    UNDISCH_TAC `nb = 8 * g + 1` THEN ARITH_TAC;
    ALL_TAC] THEN
  (* out-forall (j < nb): the old blocks j < 8*g via the incoming            *)
  (* out-forall; the one new block j = 8*g via the retained ciphertext store *)
  (* and the double-rk14 cancellation.                                       *)
  REWRITE_TAC[ARITH_RULE `j < 8 * g + 1 <=> j < 8 * g \/ j = 8 * g`] THEN
  ASM_REWRITE_TAC[TAUT `p \/ q ==> r <=> (p ==> r) /\ (q ==> r)`] THEN
  REWRITE_TAC[FORALL_AND_THM; FORALL_UNWIND_THM2] THEN
  REWRITE_TAC[ARITH_RULE `16 * 8 * g = 128 * g`] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[aes_ctr_block] THEN REWRITE_TAC[ARITH_RULE `8 * g + c = c + 8 * g`] THEN
  CONV_TAC WORD_BITWISE_RULE);;



(* ========================================================================= *)
(* Tail cascade arm rem=2 (nblocks = 8*g+2), lands at 0x1434                 *)
(* (L256_enc_rem2_drain).                                                    *)
(*                                                                           *)
(* The second remainder-cascade arm.  It folds two fresh blocks (8*g and     *)
(* 8*g+1) into the GHASH accumulator with a 2-block batched reduce           *)
(* (GHASH_POLYVAL_ACC_BATCHED), where rem = 1 uses a single-block APPEND.    *)
(* Like the arms for rem = 3..7, its precondition also pins the entry value  *)
(* of Q27 (q27_init).                                                        *)
(* ========================================================================= *)

(* x5 at the rem = 2 tail entry: 16*nb - 128*g = 32 for nb = 8*g+2; once it  *)
(* is rewritten to `word 32` the cascade resolves to the rem = 2 arm (b.eq   *)
(* at 0x142c -> 0x1434) with concrete flags.                                 *)
let TAIL_X5_REM2 = prove
 (`!(in_p:int64) g.
     word_sub (word_add in_p (word (16 * (8 * g + 2))))
              (word_add in_p (word (128 * g))) = word 32:int64`,
  REPEAT STRIP_TAC THEN CONV_TAC WORD_RULE);;
(* Two-block Q19 fold: RECON_GRR exposes the reduce; the 2 blocks normalise  *)
(* to nist_cipher_block(8*g),(8*g+1); GHASH_REDUCE_RAW_XOR +                 *)
(* KARATSUBA_IS_DOT_HW + KDOT_B0 (block 0 carries the accumulator, with the  *)
(* store-order byteswap) collapse the summed lanes to                        *)
(*      word_xor (polyval_dot cb(8*g+1) H^0)                                 *)
(*               (polyval_dot (sofar (x) cb(8*g)) H^1)                       *)
(* which is exactly GHASH_POLYVAL_ACC_BATCHED with bs = [cb(8*g+1)], b =     *)
(* cb(8*g), a = sofar; the RHS nist_ghash..(8*g+2) unfolds to the same via   *)
(* NIST_GHASH_IS_POLYVAL + list_of_seq/APPEND/GHASH_ACC_APPEND + the batched *)
(* lemma.  Only block 8*g+1's counter 8*g+c+1 needs reindexing to (8*g+1)+c; *)
(* block 8*g's counter 8*g+c already has that shape.                         *)
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

(* Fold `read Q19 s53` (the raw 2-block reduce) to the compact               *)
(* nist_ghash..(8*g+2) in place, before ext/rev64/store (as FOLD_Q19_REM1).  *)
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
  (* Assert the 2 tail input blocks; without this the plaintext loads stay   *)
  (* raw memory reads and the ciphertext/GHASH chain drops.                  *)
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
  (* Invert the keystream facts so that the ciphertext eor3 outputs are      *)
  (* state-independent.                                                      *)
  RULE_ASSUM_TAC(fun th -> try MATCH_MP KS_SOLVE th with Failure _ -> th) THEN
  (* Steps 1..9: the tail prefix; rewriting x5 to word 32 lets the cascade   *)
  (* resolve concretely to the rem = 2 arm (b.eq at 0x142c -> 0x1434).       *)
  MAP_EVERY NSTEP_GP (1--9) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[TAIL_X5_REM2]) THEN
  (* Steps 10..53: the dispatch and the 2-block drain, up to the final       *)
  (* reduce eor3 at 0x14d0 (s53: read Q19 = the raw 2-block reduce).         *)
  MAP_EVERY NSTEP_GP (10--53) THEN
  (* Fold Q19 to the compact nist_ghash..(8*g+2) before ext/rev64/store,     *)
  (* then drop the dead reduce scratch.                                      *)
  FOLD_Q19_REM2 THEN
  DISCARD_DEAD_REDUCE_SCRATCH THEN
  (* Steps 54..57: ext, rev64 and st1 (tag) at 0x14d4/0x14d8/0x14dc, then    *)
  (* the b at 0x14e0 to pc+0x1154.                                           *)
  MAP_EVERY NSTEP_GP (54--57) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  (* ivec store: 6 `sub v30` in the drain take 8g+c+8 to 8g+c+2 = nb+c. *)
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
  (* tag store: read(tag_p) = rev8 (nist_ghash..nb), Q19 being folded. *)
  CONJ_TAC THENL
   [REWRITE_TAC[TAG_STORE_REV64] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    UNDISCH_TAC `nb = 8 * g + 2` THEN ARITH_TAC;
    ALL_TAC] THEN
  (* out-forall (j < nb): the old blocks j < 8*g via the incoming            *)
  (* out-forall; the 2 new blocks j = 8*g, 8*g+1 via the retained ciphertext *)
  (* stores and the double-rk14 cancellation.                                *)
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
(* FAST2_TAIL: the nb = 2 (32-byte) small-path tail, from pc+0x17d4 (the     *)
(* small_2 tail start, after the L256_enc_small_2 AES loop and the rk14      *)
(* load) to pc+0x1154.  The two keystreams are in Q0/Q1 (up to the final     *)
(* rk14 XOR, with rk14 in Q28), Q12 holds the tbl byte-reverse index and Q30 *)
(* enters as ctr(c+nb) (= 8g+c+2).  The leg loads, encrypts and stores the   *)
(* two blocks, folds them into Q19 (at s39, with TAIL_Q19_FOLD_REM2) and     *)
(* finishes in L256_enc_small_reduce with the tbl/st1 tag store              *)
(* (steps 40-42).                                                            *)
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
  (* Q12 is the live tbl index here, not reduce scratch: keep it, so that    *)
  (* read Q12 reaches the tbl step.                                          *)
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
   (* With the concrete index in Q12, tbl expands to the same word_join byte *)
   (* reversal as ext+rev64, so TAG_STORE_REV64 applies.                     *)
   [REWRITE_TAC[TAG_STORE_REV64] THEN
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
(* FAST1_TAIL: the nb = 1 (16-byte) small-path tail, the one-block version   *)
(* of FAST2_TAIL (keystream Q0 only; the same tbl tag store, with Q12 the    *)
(* index).  Entry 0x187c (the small_1 tail start: ldr q8; ext v16; mov v29;  *)
(* eor3 v9), then the single-block drain and L256_enc_small_reduce.  Q30     *)
(* enters as ctr(c+nb) (= 8g+c+1), built directly by the small_1 code.  Q19  *)
(* folds at s24.                                                             *)
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



(* ========================================================================= *)
(* Tail cascade arm rem=3 (nblocks = 8*g+3), lands at 0x1070.                *)
(* 3-block batched Q19 fold; Q27 pinned (q27_init).  5 `sub v30` decrements  *)
(* roll the counter 8g+c+8 -> 8g+c+3 = nb+c.                                 *)
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
(* Tail cascade arm rem=4 (nblocks = 8*g+4), lands at 0x1328.                *)
(* 4-block batched Q19 fold; Q27 pinned (q27_init).  4 `sub v30` decrements  *)
(* roll the counter 8g+c+8 -> 8g+c+4 = nb+c.                                 *)
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
(* FAST4_TAIL: the nb = 4 (64-byte) small-path tail.  Entry pc+0x15ac (the   *)
(* small_4 tail start) with the 4 keystreams (Q0..Q3) as preconditions (a    *)
(* fresh entry, so that the tail's eor3 write of the block-0 ciphertext is   *)
(* tracked, as in FAST2_TAIL); the tail start (block-0 plaintext load, eor3  *)
(* ciphertext write, accumulator reset) runs into the eor3-fused 4-block     *)
(* drain and L256_enc_small_reduce, ending at pc+0x1154.  Q30 enters as      *)
(* ctr(c+nb) (= 8g+c+4), built directly by the small_4 code.  Q19 folds      *)
(* at s67.                                                                   *)
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
  (* Q12 is the live tbl index: discard DISCARD_DEAD_REDUCE_SCRATCH's        *)
  (* registers except Q12.                                                   *)
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
(* FAST3_TAIL: the nb = 3 (48-byte) small-path tail, the three-block version *)
(* of FAST4_TAIL (keystreams Q0, Q1, Q2; the same tbl tag store, with Q12    *)
(* the index).  Entry 0x16ec (the small_3 tail start), then the eor3-fused   *)
(* 3-block drain and L256_enc_small_reduce.  Q30 enters as ctr(c+nb) (=      *)
(* 8g+c+3), built directly by the small_3 code.  Q19 folds at s50 (with the  *)
(* cascade's TAIL_Q19_FOLD_REM3).                                            *)
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
(* Tail cascade arm rem=5 (nblocks = 8*g+5), lands at 0x1034.                *)
(* 5-block batched Q19 fold; Q27 pinned (q27_init).  3 `sub v30` decrements  *)
(* roll the counter 8g+c+8 -> 8g+c+5 = nb+c.                                 *)
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
  (* rem = 5 finishes on the eor3-fused rem4_drain, entered at step 57; its
     final reduce eor3 at 0x1410 is step 115 (57 + 58), so Q19 is folded
     at s115. *)
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
(* Tail cascade arm rem=6 (nblocks = 8*g+6), lands at 0xff8.                 *)
(* 6-block batched Q19 fold; Q27 pinned (q27_init).  2 `sub v30` decrements  *)
(* roll the counter 8g+c+8 -> 8g+c+6 = nb+c.                                 *)
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
  (* rem = 6 -> rem4_drain, entered at step 65: fold at s123 (65 + 58). *)
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
(* Tail cascade arm rem=7 (nblocks = 8*g+7), lands at 0xfc0.                 *)
(* 7-block batched Q19 fold; Q27 pinned (q27_init).  1 `sub v30` decrement   *)
(* rolls the counter 8g+c+8 -> 8g+c+7 = nb+c.                                *)
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
  (* rem = 7 -> rem4_drain, entered at step 71: fold at s129 (71 + 58). *)
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
(* Tail cascade arm rem=8 (nblocks = 8*g+8), lands at 0x1178                 *)
(* (L256_enc_exact8_drain), for every g >= 0.                                *)
(*                                                                           *)
(* TAIL_REM8 is stated for every group count g, including nblocks = 8 and    *)
(* 16, which the (nblocks-1) DIV 8 decomposition also routes here; its drive *)
(* does not depend on g (x5 = 128).  Its helpers are the x5 value            *)
(* TAIL_X5_128_G and the Q19 fold TAIL_Q19_FOLD_G.                           *)
(* ========================================================================= *)
let TAIL_X5_128_G = prove
 (`!(in_p:int64) nb g.
     8 * g + 8 = nb
     ==> word_sub (word_add in_p (word (16 * nb)))
                  (word_add in_p (word (128 * g))) = word 128:int64`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN CONV_TAC WORD_RULE);;

(* TAIL_Q19_FOLD_G: the rem = 8 fold, advancing Q19 from nist_ghash..(8*g)   *)
(* to nist_ghash..(8*g+8).  It is not Q19_FOLD_TAC_K, because the tail's     *)
(* reduce differs from the prepretail's in two ways.                         *)
(* (1) The operand order of the final reduce eor3.  The prepretail's         *)
(*     `eor3 v19,v19,v21,v17` (0xec0) is `word_xor (word_xor p3 ext) pmull`  *)
(*     and needs a leading AC-swap to reach ghash_reduce_raw's `word_xor     *)
(*     (word_xor p3 pmull) ext` shape; the tail's `eor3 v19,v19,v17,v21`     *)
(*     (0x1314) is already in ghash_reduce_raw order, so no AC-swap          *)
(*     is applied.                                                           *)
(* (2) The block provenance.  The prepretail folds the invariant-clean       *)
(*     v8..v15 blocks (`word_xor (aes_ctr_block J) (inblock J)`); the tail   *)
(*     computes its blocks fresh (eor3 v9,..,vN,v29 + KS_SOLVE), so each     *)
(*     block enters the reduce in the raw form `word_xor (word_xor inblock   *)
(*     (word_xor aes rk14)) rk14` (double rk14, inblock first, aes not       *)
(*     folded to aes_ctr_block).  The fold first normalises it: a            *)
(*     WORD_BITWISE_RULE rewrite cancels the double rk14, RECON_GRR exposes  *)
(*     ghash_reduce_raw, WORD_REDUCE_CONV + WORD_XOR_0 clear a spurious      *)
(*     word_subword (word 0) (64,64), a second rewrite puts the AES term     *)
(*     first, and the counter reindexing 8*g+c+j = (8*g+j)+c lets GSYM       *)
(*     aes_ctr_block fold rev8 (aes256_cipher (ctr_block nonce (J+c)) rk) to *)
(*     aes_ctr_block J, after which GSYM cipher_block + CIPHER_BLOCK_NIST    *)
(*     reach nist_cipher_block.                                              *)
(* After this cleaning the tail's three Karatsuba lanes are aligned (the     *)
(* same block order on all lanes), so GHASH_REDUCE_RAW_XOR (linearity in any *)
(* order) + KARATSUBA_IS_DOT_HW give 8 clean polyval_dots directly, without  *)
(* DIST8_PLAIN (which assumes the body's [1;0;3;2..] cross order); the       *)
(* batched fold then closes as in the main loop, with NCB_ETA for the        *)
(* block-0 lambda.                                                           *)
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
  (* Q27 is last read at step 94 (eor3 v18,v18,v27,v15 at 0x12c0), so it is  *)
  (* dropped after s97; the final reduce eor3 at 0x1314 is step 115, where   *)
  (* Q19 is folded; the writebacks are the str q30 at step 98 and the st1 at *)
  (* step 118.                                                               *)
  MAP_EVERY NSTEP_GP (10--97) THEN
  DISCARD_REGS ["Q27"] THEN
  MAP_EVERY NSTEP_GP (98--115) THEN
  (* Rewrite nb back to 8*g+8 in the Q19 fact only (the hypothesis           *)
  (* 8*g+8 = nb is still needed by the tag and out-block closers), so that   *)
  (* the fold sees all 8 block indices in the 8*g+j form.                    *)
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
(* TAIL_REM (rem in 1..8, g >= 0).                                           *)
(*                                                                           *)
(* One theorem for the whole cascade at entry pc+0xee0, for any leftover     *)
(* block count r in 1..8 and any group count g >= 0.  The proof splits on r; *)
(* each case weakens the unified (strongest) precondition to that arm's      *)
(* precondition with ENSURES_PRECONDITION_THM (the arms REM1..REM7 need      *)
(* fewer register pins and keystreams; REM8 needs all) and then applies the  *)
(* matching TAIL_REM<r>.  The unified precondition pins q18_init/q27_init,   *)
(* all 8 keystreams and the 15 round-key memory facts (REM8's precondition); *)
(* the weakening drops whatever each smaller arm omits.  BETA_TAC before     *)
(* STRIP_TAC is needed: the precondition is a lambda redex, and STRIP_TAC    *)
(* first would keep it unreduced.                                            *)
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
(* GEN_CORRECT (nb >= 17) nests three ENSURES_SEQUENCE_TACs, at 0x4c0, 0xa10 *)
(* and 0xee0.  The first leg of each frame-subsumes the segment's MAYCHANGE  *)
(* into the whole frame (ENSURES_FRAME_SUBSUMED + SUBSUMED_MAYCHANGE_TAC)    *)
(* and then applies the segment theorem by MP_TAC ... DISCH_THEN             *)
(* MATCH_MP_TAC (as in AES_XTS_ENCRYPT_LT_2BLOCK_CORRECT).  The PREPRETAIL   *)
(* -> TAIL join uses an existential Q18/Q27 mid-state: the mid predicate is  *)
(* `?v18 v27. read Q18 s = v18 /\ read Q27 s = v27 /\ <PREPRETAIL post       *)
(* without the tag memory>`; the PREPRETAIL leg proves it by EXISTS_TAC      *)
(* (read Q18 s) / (read Q27 s), and the TAIL leg strips the existential and  *)
(* applies AES256_GCM_ENC_ALT_TAIL_REM (g = k+1, r = nb - 8*(k+1)) to        *)
(* the witnesses.                                                            *)
(* ========================================================================= *)

(* Frame note: the SETUP/MAIN_LOOP/PREPRETAIL frames are subsets of the      *)
(* CORRECT frame (ABI ,, Q8..Q15 ,, mem[out_p;tag_p;ivec_p]).  SETUP writes  *)
(* only out_p memory (and registers); PREPRETAIL writes no memory (its frame *)
(* still lists out_p); the TAIL writes out_p, tag_p and ivec_p.              *)

let LENGTH_WB_MC =
  (REWRITE_CONV [fst AES256_GCM_ENC_ALT_EXEC]) `LENGTH aes256_gcm_enc_alt_tmc`;;

(* Helper for the TAIL leg's existential precondition: an ensures with an    *)
(* existential precondition follows from the ensures for every witness (from *)
(* the definition of ensures: the precondition ?v w. P is stripped and the   *)
(* witnesses specialise the hypothesis).  Two-existential form, matching the *)
(* 0xee0 mid-state.                                                          *)
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
  (* ENSURES_SEQUENCE_TAC adds the `aligned_bytes_loaded` (program_decodes)  *)
  (* and `read PC s = word pc'` conjuncts to both legs' mid-state, so the    *)
  (* mid-state argument omits them (only the register/memory remainder is    *)
  (* given).  It also runs MAYCHANGE_IDEMPOT_TAC internally, which fails if  *)
  (* the ABI macro is folded, so the macro is unfolded first.                *)
  (*                                                                         *)
  (* Expand the core precondition's ALLPAIRS + PAIRWISE into individual      *)
  (* nonoverlapping atoms before stripping, so that each segment leg's       *)
  (* antecedents are available as assumptions for ASM_SIMP/ASM_REWRITE       *)
  (* (SETUP's precondition needs out_p vs tag_p and ivec_p, which are        *)
  (* PAIRWISE facts of CORRECT, not ALLPAIRS ones).                          *)
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REWRITE_TAC[LENGTH_WB_MC; ALLPAIRS; PAIRWISE; ALL; NONOVERLAPPING_CLAUSES] THEN
  REPEAT STRIP_TAC THEN

  (* ============ SEQUENCE 1: SETUP  pc+0x38 -> pc+0x4c0 ============        *)
  (* mid-state: no aligned_bytes_loaded or read PC (the tactic adds them).   *)
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

  (* ============ SEQUENCE 2: MAIN_LOOP  pc+0x4c0 -> pc+0xa10 ============   *)
  (* mid-state = the PREPRETAIL_GEN precondition (pc+0xa10) without aligned  *)
  (* and PC, with mod_p := stackpointer+0x40, written out explicitly.        *)
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

  (* ============ SEQUENCE 3: PREPRETAIL  pc+0xa10 -> pc+0xee0 ============  *)
  (* mid-state = ?v18 v27. read Q18 s = v18 /\ read Q27 s = v27 /\ <the      *)
  (* PREPRETAIL_GEN postcondition, with mod_p -> stackpointer+0x40, without  *)
  (* the tag memory, aligned and PC>.  ENSURES_SEQUENCE_TAC adds             *)
  (* aligned_bytes_loaded and read PC outside the existential, so on the     *)
  (* TAIL leg the precondition is `\s. aligned .. /\ read PC s = .. /\ (?v18 *)
  (* v27. ...)`; the TAIL leg hoists the existential with GSYM               *)
  (* RIGHT_EXISTS_AND_THM / LEFT_EXISTS_AND_THM before                       *)
  (* ENSURES_EXISTS2_PRECONDITION.                                           *)
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
   [(* PREPRETAIL leg: apply PREPRETAIL_GEN, then weaken its post to the     *)
    (* existential mid-state (the witnesses are the actual Q18/Q27 reads).   *)
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
    (* Weaken the goal's post from Q_mid (the existential) to PREPRETAIL's   *)
    (* actual post with ENSURES_POSTCONDITION_TAC (MATCH_MP_TAC              *)
    (* ENSURES_POSTCONDITION_THM + EXISTS_TAC of the given post).  This      *)
    (* leaves two subgoals: (1) the pointwise implication PP_post ==> Q_mid  *)
    (* (closed by EXISTS_TAC (read Q18/Q27 s) + ASM_REWRITE), and (2)        *)
    (* `ensures arm PP_pre PP_post frame`, which is PREPRETAIL_GEN applied.  *)
    (* The post passed is PREPRETAIL_GEN's full postcondition, including     *)
    (* aligned_bytes_loaded and read PC.                                     *)
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
     [(* (1) PP_post ==> Q_mid.  PREPRETAIL_GEN's post includes              *)
      (* aligned_bytes_loaded, so the antecedent lambda given to             *)
      (* ENSURES_POSTCONDITION_TAC above does too.  X_GEN_TAC forces the     *)
      (* state variable to `s` (so that the pin witnesses match); BETA_TAC   *)
      (* reduces both the antecedent redex `(\s.OLD) s` and the consequent   *)
      (* redex `(\s.MID) s` before STRIP_TAC: if STRIP_TAC ran first it      *)
      (* would keep the antecedent as one unreduced redex and aligned would  *)
      (* never reach the assumptions.  Then REPEAT(CONJ_TAC ...) peels the   *)
      (* aligned and PC conjuncts (now assumptions) off the mid-state's      *)
      (* conjunction, and the actual Q18/Q27 reads witness the               *)
      (* remaining existential.                                              *)
      X_GEN_TAC `s:armstate` THEN BETA_TAC THEN STRIP_TAC THEN
      REPEAT(CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC]) THEN
      EXISTS_TAC `read Q18 s:int128` THEN EXISTS_TAC `read Q27 s:int128` THEN
      ASM_REWRITE_TAC[];
      (* (2) ensures PP_pre PP_post frame: PREPRETAIL_GEN applied. *)
      MP_TAC(ISPECL
       [`in_p:int64`; `out_p:int64`; `tag_p:int64`; `ivec_p:int64`;
        `key_p:int64`; `htable_p:int64`; `word_add stackpointer (word 0x40):int64`;
        `end_p:int64`; `tag0:int128`; `nonce:(96)word`; `c:num`; `rk:int128 list`;
        `inblock:num->int128`; `nb:num`; `k:num`; `pc:num`]
       AES256_GCM_ENC_ALT_PREPRETAIL_GEN) THEN
      REWRITE_TAC[LENGTH_WB_MC; ALLPAIRS; ALL; NONOVERLAPPING_CLAUSES] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[NONOVERLAPPING_CLAUSES] THEN ASM_ARITH_TAC];
    ALL_TAC] THEN

  (* ============ TAIL leg: pc+0xee0 -> pc+0x1154 ============               *)
  (* ENSURES_SEQUENCE_TAC wrapped the precondition as `\s.                   *)
  (* aligned_bytes_loaded .. /\ read PC s = word (pc+0xee0) /\ (?v18 v27.    *)
  (* ...)`, so the existential is not outermost.  GSYM RIGHT_EXISTS_AND_THM  *)
  (* / LEFT_EXISTS_AND_THM (`P /\ (?x. Q x)` -> `?x. P /\ Q x`), applied     *)
  (* under the \s. binder, hoist it to `\s. ?v18 v27. aligned .. /\ read PC  *)
  (* .. /\ read Q18 s = v18 /\ read Q27 s = v27 /\ B`, which matches         *)
  (* ENSURES_EXISTS2_PRECONDITION's `\s. ?v w. P v w s`.  MATCH_MP_TAC with  *)
  (* it turns the goal into `!v18 v27. ensures step (\s. ...) post frame`,   *)
  (* and AES256_GCM_ENC_ALT_TAIL_REM is applied (ISPECL'd) to v18/v27.       *)
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
(* AES256_GCM_ENC_ALT_FIXED_CORRECT_G1: the g = 1 leg (loop_count = 0, i.e.  *)
(* nblocks 9..16).  For g = 1 the main loop is skipped (the second setup     *)
(* guard, b.ge at 0x4bc, is taken and SETUP_G1 lands directly at pc+0xa10 =  *)
(* PREPRETAIL), so this is GEN_CORRECT's composition without the MAIN_LOOP   *)
(* sequence: SETUP_G1 -> PREPRETAIL_GEN (k = 0) -> TAIL_REM (g = 0+1, r =    *)
(* nb-8).  SETUP_G1's post at 0xa10 is GEN_CORRECT's second mid-state at     *)
(* k := 0, so all mid-states and ISPECLs are written in literal-0 form.  The *)
(* buffer bound `val in_p + 16*nb < 2 EXP 63` is carried for TAIL_REM.       *)
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

  (* ============ SEQUENCE 3: PREPRETAIL  pc+0xa10 -> pc+0xee0 ============  *)
  (* The same existential Q18/Q27 mid-state as in GEN_CORRECT.               *)
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
   [(* PREPRETAIL leg, as in GEN_CORRECT. *)
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
    (* As in GEN_CORRECT: weaken the post to PREPRETAIL_GEN's full post. *)
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
     [(* (1) PP_post ==> Q_mid, as in GEN_CORRECT. *)
      X_GEN_TAC `s:armstate` THEN BETA_TAC THEN STRIP_TAC THEN
      REPEAT(CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC]) THEN
      EXISTS_TAC `read Q18 s:int128` THEN EXISTS_TAC `read Q27 s:int128` THEN
      ASM_REWRITE_TAC[];
      (* (2) PREPRETAIL_GEN applied. *)
      MP_TAC(ISPECL
       [`in_p:int64`; `out_p:int64`; `tag_p:int64`; `ivec_p:int64`;
        `key_p:int64`; `htable_p:int64`; `word_add stackpointer (word 0x40):int64`;
        `end_p:int64`; `tag0:int128`; `nonce:(96)word`; `c:num`; `rk:int128 list`;
        `inblock:num->int128`; `nb:num`; `0`; `pc:num`]
       AES256_GCM_ENC_ALT_PREPRETAIL_GEN) THEN
      REWRITE_TAC[LENGTH_WB_MC; ALLPAIRS; ALL; NONOVERLAPPING_CLAUSES] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[NONOVERLAPPING_CLAUSES] THEN ASM_ARITH_TAC];
    ALL_TAC] THEN

  (* ============ TAIL leg: pc+0xee0 -> pc+0x1154 ============               *)
  (* As in GEN_CORRECT: hoist the existential, then apply TAIL_REM.          *)
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
  (* counter alignment (g := 0+1), as in GEN_CORRECT: these ARITH_RULEs
     rewrite 8*(0+1)+c+N to 8*0+c+(N+8). *)
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

(* WB_X9_NORM: the prologue's `lsr x9,x1,#3` gives word ((128*nb) DIV 8)     *)
(* when X1 = word (128*nb) and 128*nb < 2^64.                                *)
let WB_X9_NORM = prove
 (`128 * nb < 2 EXP 64
   ==> word_ushr (word (128 * nb):int64) 3 = word ((128 * nb) DIV 8)`,
  STRIP_TAC THEN REWRITE_TAC[word_ushr] THEN AP_TERM_TAC THEN
  REWRITE_TAC[ARITH_RULE `2 EXP 3 = 8`] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC);;

(* ========================================================================= *)
(* The legs for nb <= 8 (SETUP0_TAIL and FAST1..FAST4) and the core          *)
(* correctness theorem AES256_GCM_ENC_ALT_CORRECT for every nb >= 1.         *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* loop_count = 0 branch mechanics (nb in 1..8).                             *)
(* ------------------------------------------------------------------------- *)

(* When groups = (nb-1) DIV 8 = 0 (i.e. nb <= 8), the round-down end pointer *)
(* x5 = in_p + ((16*nb - 1) AND ~0x7f) collapses to in_p, because 16*nb-1 <= *)
(* 127 < 128 = 2^7, so masking off the low 7 bits gives 0.  Then `cmp x0,x5; *)
(* b.ge` at 0x44c (x0 = in_p) is taken, skipping the main loop and going     *)
(* straight to the tail cascade at pc+0xee0.  These two lemmas are the       *)
(* analogues of SETUP_BRANCH_COND_FALSE_GEN / SETUP_X5_END_GEN for the       *)
(* groups = 0 leg: there the branch falls through (groups >= 1), here it     *)
(* is taken.                                                                 *)

(* x5 (the rounded-down last-full-group pointer) = in_p for nb in 1..8. *)
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

(* The b.ge at 0x44c condition (the exact NF<>VF biconditional the stepper   *)
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
(* SETUP0: the setup leg for nb in {5,6,7,8}.                                *)
(*                                                                           *)
(* For these nb (groups = (nb-1) DIV 8 = 0; nb <= 4 take the b.le to         *)
(* L256_enc_small, FAST1..FAST4) the b.ge at 0x44c is taken                  *)
(* (WB_BRANCH_COND_TRUE), so the main loop is skipped: the setup runs        *)
(* pc+0x38 -> pc+0xee0 (the tail entry), building the 8 CTR keystreams       *)
(* Q0..Q7 (counters c..c+7), the next counter Q30 = ctr_block nonce (c+8)    *)
(* and Q19 = the untouched GHASH accumulator = nist_ghash..[] = tag0.  This  *)
(* is the branch-taken analogue of SETUP_GEN (which falls through to the     *)
(* main loop).  The postcondition is the tail's precondition for g = 0       *)
(* (Q0..Q7 pre-rk14 keystreams, Q30 = c+8, Q19 = tag0, X5 = in_p, the        *)
(* out-forall j < 0 vacuous), so TAIL_REM composes with it via               *)
(* ENSURES_SEQUENCE_TAC.                                                     *)
(*                                                                           *)
(* The drive is SETUP_GEN's up to the branch: NSTEP 1-7 (the b.le at step 7  *)
(* not taken), 8-261, then NSTEP 262 (the b.ge at 0x44c), which              *)
(* WB_BRANCH_COND_TRUE resolves to pc+0xee0.  Closers: the keystreams via    *)
(* KSCLOSE (AES256_CIPHER_RECONSTRUCT + the counter-lane reconstruction);    *)
(* Q30 via the lane lemma SETUP_Q30_LANES_10 + CTR_BLOCK_RECONSTRUCT_REV32;  *)
(* Q19 via NIST_GHASH_NIL; X4 via the word_ushr/MOD_LT bridge; X5 via        *)
(* WB_X5_GROUPS0.                                                            *)
(* ========================================================================= *)

(* SETUP_Q30_LANES_10: the lanes of the SETUP0 exit counter Q30 = ctr_block  *)
(* nonce (c+8) (base c, +7 at 0x94, then +1 at 0xc4); cf. SETUP_Q30_LANES    *)
(* for c+13.                                                                 *)
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

(* KSCLOSE: the keystream closer.  The pre-rk14 aese chain in register Qj,
   XORed with rk14, is rev8 (aes256_cipher (ctr_block nonce (c+j)) rk).  A
   direct `REWRITE_TAC[ctr_block] THEN CONV_TAC WORD_BLAST` would have to
   bit-blast the 128-bit counter term, so the closer follows CIPHER_CLOSE's
   structural reconstruction (without its input-XOR reordering, since the
   keystream register is not XORed with an input block): fold the aese chain
   to aes256_cipher, reconstruct the AES-input counter lanes to ctr_block
   nonce K (CTR_LANE_LOW + CTR_NONCE_LANES + GSYM WORD_ADD +
   CTR_BLOCK_RECONSTRUCT_REV8/32, then cancel the double reverse), refold
   both sides to aes_ctr_block, and discharge the counter-index equality
   K = c+j by ARITH. *)
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

(* Q30 counter closer (the next counter, index c+8): CTR_CLOSE with the lane
   lemma SETUP_Q30_LANES_10 in place of SETUP_Q30_LANES.  Reconstruct the
   counter lanes structurally, then peel and close the counter-index
   equality by ARITH; a whole-term WORD_BLAST would bit-blast the 128-bit
   counter term. *)
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

(* Shape-routed dispatcher for the SETUP0 (groups = 0) postcondition. *)
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
      (* X4: word_add in_p (word_ushr (word (128*nb)) 3) = in_p + 16*nb *)
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
(* SETUP0_TAIL: the leg for nb in {5,6,7,8}, SETUP0 (pc+0x38 -> pc+0xee0)    *)
(* composed with TAIL_REM (r = nb, g = 0; pc+0xee0 -> pc+0x1154) by          *)
(* ENSURES_SEQUENCE_TAC at pc+0xee0: one tail group and no main loop (nb     *)
(* 1..4 are FAST1..FAST4).  Q18/Q27 are unpinned at SETUP0's exit, so the    *)
(* join uses the existential Q18/Q27 mid-state, as in the PREPRETAIL -> TAIL *)
(* join of GEN_CORRECT.                                                      *)
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

  (* ===== SEQUENCE: SETUP0  pc+0x38 -> pc+0xee0 ===== *)
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



(* FAST2: the nb = 2 (32-byte) leg, pc+0x38 -> pc+0x1154, through the small  *)
(* path.  ENSURES_SEQUENCE at 0x17d4: segment A is the dispatch (the b.le at *)
(* 0x50 taken, the small_1 test falling through and the small_2 test at      *)
(* 0x1534/0x1538 taken, DISPATCH_TAKEN) and the 2-block AES; segment B is    *)
(* FAST2_TAIL.  The split is at 0x17d4, where the tail starts, so that the   *)
(* tail's eor3 write of the block-0 ciphertext is tracked from a             *)
(* fresh entry.                                                              *)
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
         (* Q12 index closer *)
         else (REFL_TAC ORELSE CONV_TAC WORD_BLAST)))) gl
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
   [(* Segment A: 0x38 -> 0x17d4 *)
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
    (* Segment B: 0x17d4 -> 0x1154 = FAST2_TAIL *)
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
(* FAST4: the nb = 4 (64-byte) leg, entry pc+0x38.  As FAST2 but for 4       *)
(* blocks: the b.le at 0x50 is taken (DISPATCH4_TAKEN) and the small_1/2/3   *)
(* `b.eq` tests fall through (nb <> 1,2,3) to L256_enc_small_4 (0x1544), the *)
(* 4-block AES (blocks 0-3); ENSURES_SEQUENCE splits at 0x15ac (the small_4  *)
(* tail start, with the keystreams as preconditions) into FAST4_TAIL.        *)
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
   [(* Segment A: 0x38 -> 0x15ac (dispatch + 4-block AES) *)
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
    (* Segment B: 0x15ac -> 0x1154 = FAST4_TAIL *)
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
(* FAST1: the nb = 1 (16-byte) leg, entry pc+0x38.  The b.le to              *)
(* L256_enc_small is taken (nb <= 4) and the first test there, `b.eq         *)
(* L256_enc_small_1` at 0x1530, is taken (nb = 1) -> 1-block AES (block 0    *)
(* only); ENSURES_SEQUENCE splits at 0x187c (the small_1 tail start, with    *)
(* the keystream Q0 as precondition) into FAST1_TAIL.                        *)
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
   [(* Segment A: 0x38 -> 0x187c (dispatch + 1-block AES) *)
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
    (* Segment B: 0x187c -> FAST1_TAIL *)
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
(* FAST3: the nb = 3 (48-byte) leg, entry pc+0x38.  The small_1 and small_2  *)
(* `b.eq` tests fall through (nb <> 1, 2) and the small_3 test `cmp          *)
(* x9,#0x30; b.eq L256_enc_small_3` at 0x153c/0x1540 is taken (nb = 3) ->    *)
(* 3-block AES; ENSURES_SEQUENCE splits at 0x16ec (the small_3 tail start,   *)
(* with the 3 keystreams as preconditions) into FAST3_TAIL.                  *)
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
   [(* Segment A: 0x38 -> 0x16ec (dispatch + 3-block AES) *)
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
    (* Segment B: 0x16ec -> FAST3_TAIL *)
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
      (* nb <> 3: nb = 4 (FAST4) or nb in {5,6,7,8} (SETUP0_TAIL) *)
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
        (* nb in {5,6,7,8}: the generic 8-block path via SETUP0_TAIL *)
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
    (* ===== g >= 2  (nb >= 17): GEN_CORRECT (k = groups-1) ===== *)
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


(* Entry-guard lemmas for nb >= 1: WB_GUARD1_NONZERO_GEN (`cbz x1` does not  *)
(* branch: word (128*nb) is nonzero) and WB_GUARD2_MASK_GEN (`tst x1,#0x7f`  *)
(* gives 0: 128 divides 128*nb).                                             *)
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
(* The whole-block count actually processed, gcm_wb_blocks (shared, in       *)
(* aes_gcm_spec.ml), as a function of the bit length in X1.  The kernel has  *)
(* two entry guards: `cbz x1` for a zero length and `tst x1,#127` / `b.ne`   *)
(* for a length that is not a whole number of 128-bit blocks.  Both return 0 *)
(* without touching memory.  Folding that into the block count keeps one     *)
(* postcondition for all three paths, because at zero blocks the GHASH input *)
(* list is empty (so the tag is unchanged), the counter advances by 0, and   *)
(* the output forall is vacuous.                                             *)
(* ------------------------------------------------------------------------- *)

(* `tst x1,#127` sets ZF exactly when the length is a whole block count. *)

let WB_MASK7_EQ_MOD = prove
 (`!x:int64. word_and x (word 0x7f) = word 0 <=> val x MOD 128 = 0`,
  GEN_TAC THEN
  REWRITE_TAC[ARITH_RULE `0x7f = 2 EXP 7 - 1`; WORD_AND_MASK_WORD] THEN
  REWRITE_TAC[ARITH_RULE `2 EXP 7 = 128`; GSYM VAL_EQ_0] THEN
  SUBGOAL_THEN `val(word(val(x:int64) MOD 128):int64) = val x MOD 128`
  SUBST1_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ARITH_TAC;
    REFL_TAC]);;

(* ------------------------------------------------------------------------- *)
(* AES256_GCM_ENC_ALT_NOIBT_SUBROUTINE_CORRECT: the subroutine theorem, for  *)
(* every len_bits.  It lifts CORRECT through the two entry guards, the       *)
(* d8-d15 save/restore frame (80 bytes) and the final ret.                   *)
(*                                                                           *)
(* Wrapper shape:                                                            *)
(*   prologue 0x00 cbz x1,0x1170 ; 0x04 tst x1,#0x7f ; 0x08 b.ne 0x1170 ;    *)
(*     0x0c sub sp,sp,#0x50 ; stp d8,d9 ; lsr x9,x1,#3 ; mov x16,x4 ;        *)
(*     mov x11,x5 ; stp d10..d15 ; mov x5,#0xc2.. ; stp x5,xzr,[sp,#64] ;    *)
(*     add x10,sp,#0x40 ; 0x38 = the core entry (CORRECT);                   *)
(*   epilogue 0x1154 mov x0,x9 ; ldp d8..d15 ; add sp,sp,#0x50 ; 0x116c ret; *)
(*   reject 0x1170 mov w0,#0 ; ret (L256_enc_ret).                           *)
(* Entry C ABI: X0=in_p X1=bit_len X2=out_p X3=tag_p X4=ivec_p X5=key_p      *)
(* X6=htable_p; the prologue moves X4->X16 and X5->X11 and sets              *)
(* x9 = X1 >> 3.                                                             *)
(*                                                                           *)
(* The proof has three paths: a zero length (cbz x1 taken) and a length that *)
(* is not a multiple of 128 (tst/b.ne taken) both return 0 via L256_enc_ret; *)
(* only the main path, a nonzero whole number of blocks, falls through both  *)
(* guards (WB_GUARD1_NONZERO_GEN, WB_GUARD2_MASK_GEN) and runs CORRECT.      *)
(* ARM_ADD_RETURN_STACK_TAC is not used: its internal stepping of the        *)
(* prologue would meet the two conditional guards and leave a conditional    *)
(* PC, so the wrapper is assembled by hand.                                  *)
(* ------------------------------------------------------------------------- *)

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
  (* Expand the compact round-key list, in place inside the precondition,    *)
  (* into the pointwise reads the interior legs consume.                     *)
  REWRITE_TAC[KEY15_SPLIT] THEN
  REPEAT STRIP_TAC THEN
  (* Abbreviate the block count.  This is not cosmetic: keeping              *)
  (* `gcm_wb_blocks` folded stops `val len_bits = 128 * nb` from looping as  *)
  (* a rewrite, which it would if gcm_wb_blocks unfolded to `val len_bits    *)
  (* DIV 128` on the right.                                                  *)
  ABBREV_TAC `nb = gcm_wb_blocks len_bits` THEN
  ASM_CASES_TAC `val(len_bits:int64) MOD 128 = 0` THENL
   [ALL_TAC;
    (* ===================================================================== *)
    (* Path 3: the length is not a whole number of blocks.  `cbz x1` falls   *)
    (* through (a non-multiple of 128 is nonzero), `tst x1,#127` leaves ZF   *)
    (* clear so `b.ne` is taken, and L256_enc_ret returns 0.                 *)
    (* ===================================================================== *)
    SUBGOAL_THEN `nb = 0` SUBST_ALL_TAC THENL
     [EXPAND_TAC "nb" THEN REWRITE_TAC[gcm_wb_blocks] THEN
      ASM_REWRITE_TAC[COND_CLAUSES]; ALL_TAC] THEN
    (* The branch condition is phrased on `val len_bits`; derive that form. *)
    SUBGOAL_THEN `~(val(len_bits:int64) = 0)` ASSUME_TAC THENL
     [DISCH_TAC THEN
      UNDISCH_TAC `~(val(len_bits:int64) MOD 128 = 0)` THEN
      ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
      ALL_TAC] THEN
    SUBGOAL_THEN `~(len_bits:int64 = word 0)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[GSYM VAL_EQ_0]; ALL_TAC] THEN
    (* `tst x1,#127` leaves ZF clear, so `b.ne` is taken.  Both the word and *)
    (* the val form of the mask fact are needed to resolve the flag.         *)
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
  (* From here on the length is a whole number of blocks. *)
  ASM_CASES_TAC `val(len_bits:int64) = 0` THENL
   [(* ===================================================================== *)
    (* Path 1: zero length.  `cbz x1` is taken straight to L256_enc_ret.     *)
    (* ===================================================================== *)
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
  (* ======================================================================= *)
  (* Path 2: a nonzero whole number of blocks.  Both guards fall through;    *)
  (* steps 1-14 are the prologue, the interior big step is _CORRECT, and     *)
  (* steps 16-22 are the epilogue (which sets X0 from X9).                   *)
  (* ======================================================================= *)
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
  (* Put the length argument back into the constructed form `word (128 *     *)
  (* nb)`, the form WB_GUARD1_NONZERO_GEN and WB_GUARD2_MASK_GEN are stated  *)
  (* about, so that the guard lemmas apply directly, with no facts about an  *)
  (* opaque word and no rewrite that can loop.                               *)
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
  (* The `cbz x1` test reduces to the numeric form `128 * nb = 0` (the model *)
  (* simplifies `val(word(128*nb))` with the `128*nb < 2^64` fact), which    *)
  (* WB_GUARD1_NONZERO_GEN's word/val-shaped conjuncts do not rewrite;       *)
  (* discharge the numeric form directly from `1 <= nb` so that the          *)
  (* conditional PC collapses.                                               *)
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
(* The default build keeps the `bti c` landing pad, so its machine code is   *)
(* aes256_gcm_enc_alt_mc rather than the trimmed variant proved above.  The  *)
(* statement is written out and discharged by ARM_ADD_IBT_RULE, matching the *)
(* x86 convention (cf. x86/proofs/sha3_keccak_f1600.ml); nothing is          *)
(* re-proved.  `~extra` supplies htable_mem_8's definition, which the wrap   *)
(* theorem needs in order to see that writing PC leaves the precondition     *)
(* alone -- that cannot be done through an opaque state predicate.           *)
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
(* Safety companions (constant-time and memory safety).  See                 *)
(* arm/tutorial/safety.ml and arm/proofs/bignum_emontredc_8n.ml for          *)
(* the recipe.                                                               *)
(* ========================================================================= *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

(* --- Core-level leg safety: FAST1..FAST4 (fixed nb, a fixed-length drive). *)
(* Entry pc+0x38, exit pc+0x1154; MAYCHANGE frame (ABI, Q8..Q15,             *)
(* out/tag/ivec); f_events depends on the public pointers, stackpointer      *)
(* and pc.                                                                   *)

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


(* --- Setup segment safety: SETUP0_SAFE (nb in {5,6,7,8}, pc+0x38 ->        *)
(* pc+0xee0).  It follows AES256_GCM_ENC_ALT_SETUP0's stepping (NSTEP +      *)
(* DISPATCH4_NOT_TAKEN / DISPATCH_SMALL_NOT_TAKEN + WB_BRANCH_COND_TRUE) but *)
(* closes with the safety property.  The event trace is the same for every   *)
(* nb in {5,6,7,8}.                                                          *)
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

(* --- Tail-cascade leg safety: TAIL_REM1..8_SAFE (entry pc+0xee0, exit      *)
(* pc+0x1154).  They follow AES256_GCM_ENC_ALT_TAIL_REM<r>'s NSTEP_GP drive  *)
(* and TAIL_X5 branch resolution, but without the functional Q19-fold and    *)
(* data closers (safety needs only PC, events and inbounds), and close with  *)
(* the safety property.  Lean precondition: the key/htable/ivec/counter/     *)
(* inblock contents do not matter for safety (only the access addresses do), *)
(* so only the pointer registers are pinned.  nb = 8*g+r gives the rem = r   *)
(* arm; g is symbolic.                                                       *)

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


(* --- Tail dispatch safety: TAIL_REM_SAFE (rem in 1..8, g >= 0).  It        *)
(* follows AES256_GCM_ENC_ALT_TAIL_REM's r = 1 \/ .. \/ r = 8 case split:    *)
(* X_CHOOSE each arm's event-trace witness, give the explicit r-indexed      *)
(* dispatch function as f_events, then close each branch by the matching     *)
(* TAIL_REM<r>_SAFE.                                                         *)

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

(* --- Whole-core safety for nb in {5,6,7,8}: SETUP0_TAIL_SAFE (pc+0x38 ->   *)
(* pc+0x1154).  Composes the strengthened SETUP0_SAFE (nb-independent setup  *)
(* segment, tail-entry registers in its post) with TAIL_REM_SAFE (g = 0,     *)
(* r = nb) by a double abstract bigstep: bigstep SETUP0_SAFE with e_tail =   *)
(* [] (its trace stays the abstract f_events_callee), then bigstep           *)
(* TAIL_REM_SAFE with e_tail = that abstract setup trace (a single term, so  *)
(* no CONS blowup).  f_events takes nb because the tail's event trace        *)
(* depends on nb (= r).                                                      *)
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

(* --- PREPRETAIL_GEN_SAFE (pc+0xa10 -> pc+0xee0): the shared prepretail     *)
(* segment (the reduction of the last full 8-block group) for nb >= 9.  Lean *)
(* spec (pointer registers only; content facts do not matter for safety).    *)
(* The pointer registers are unchanged from entry to exit; straight-line     *)
(* NSTEP_GP (1--308) drive.  f_events takes k (the access addresses depend   *)
(* on the group index).                                                      *)
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

(* --- SETUP_G1_SAFE (pc+0x38 -> pc+0xa10, k = 0, nb 9..16): the setup for   *)
(* the single-full-group case.  It follows SETUP_G1's NSTEP/LDP_SETUP_TAC    *)
(* drive and the SETUP_BRANCH_COND_FALSE_GEN / _TRUE_2 guard rewrites; the   *)
(* post is strengthened with the PREPRETAIL_GEN entry registers and closed   *)
(* via SETUP_RECON_TAC_GEN.                                                  *)
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

(* --- PREPRETAIL_TAIL_SAFE (pc+0xa10 -> pc+0x1154): the reusable last-group *)
(* + tail composite (PREPRETAIL_GEN_SAFE o TAIL_REM_SAFE, g = k+1,           *)
(* r = nb-8*(k+1)) for general k.  Double abstract bigstep; f_events takes   *)
(* nb and k.                                                                 *)
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
  (* ===== BIGSTEP 1: PREPRETAIL_GEN (pc+0xa10 -> pc+0xee0), e_tail = [] *)
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
  (* ===== BIGSTEP 2: TAIL_REM (pc+0xee0 -> pc+0x1154), g=k+1, r=nb-8*(k+1) *)
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

(* --- Whole-core safety for nb 9..16: FIXED_CORRECT_G1_SAFE (pc+0x38 ->     *)
(* pc+0x1154, k = 0).  SETUP_G1_SAFE o PREPRETAIL_TAIL_SAFE (double          *)
(* bigstep).  f_events takes nb.                                             *)
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

(* --- SETUP_GEN_SAFE (pc+0x38 -> pc+0x4c0, k <> 0, nb >= 17): the setup for *)
(* the general (main-loop) case.  The same as SETUP_G1_SAFE except that the  *)
(* closing branch is SETUP_BRANCH_COND_FALSE_2_GEN (~(k = 0): fall into the  *)
(* main loop at pc+0x4c0 rather than skip to the prepretail).  The post is   *)
(* the MAIN_LOOP entry registers.                                            *)
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

(* --- MAIN_LOOP_SAFE (pc+0x4c0 -> pc+0xa10, k iterations, nb >= 17): the    *)
(* 8-block main loop.  Lean invariant (pointer registers only);              *)
(* ENSURES_EVENTS_WHILE_UP2_TAC with pc2 = the exit (pc+0xa10).  The body is *)
(* the functional NSTEP_G drive, with the incremented ldps at steps          *)
(* 295/303/304 handled by LDP_STEP4_LEAN (LDP_STEP4_TAC without the          *)
(* INBLOCKS_TAC re-derivation, which safety does not need) and the b.lt at   *)
(* step 340; the back-edge PC is closed via BRIDGE_GE + IV_ADD (in_p         *)
(* cancels, leaving i+1 < k), the events via ENUMERATEL_ADD1.                *)
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
  (* ===== loop body: pc+0x4c0 .. b.lt at pc+0xa0c (340 steps) ===== *)
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
  (* PC branch: <b.lt cond> <=> i+1<k, via BRIDGE_GE + IV_ADD *)
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
  (* events: e2 = ENUMERATEL (i+1) e_loop; unify f_ev_loop i := this         *)
  (* iteration's trace                                                       *)
  SAFE_META_EXISTS_TAC allowed_vars_e THEN
  CONJ_TAC THENL [ EXISTS_E2_TAC allowed_vars_e; ALL_TAC ] THEN
  CONJ_TAC THENL
   [PURE_REWRITE_TAC[APPEND_NIL] THEN
    GEN_REWRITE_TAC RAND_CONV [ENUMERATEL_ADD1] THEN
    BETA_TAC THEN
    BINOP_TAC THENL [ UNIFY_F_EVENTS_TAC; REFL_TAC ];
    DISCHARGE_MEMACCESS_INBOUNDS_TAC])
;;

(* --- LOOP_TAIL_SAFE (pc+0x4c0 -> pc+0x1154): MAIN_LOOP_SAFE o              *)
(* PREPRETAIL_TAIL_SAFE (double abstract bigstep, parameter k), the loop +   *)
(* prepretail + tail composite for nb >= 17.                                 *)
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

(* --- Whole-core safety for nb >= 17: GEN_CORRECT_SAFE (pc+0x38 ->          *)
(* pc+0x1154, k >= 1).  SETUP_GEN_SAFE o LOOP_TAIL_SAFE (double bigstep).    *)
(* f_events takes nb and k.                                                  *)
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

(* --- Whole-core safety (all nb): a dispatch over the four nb ranges        *)
(* (nb <= 4: FAST1..FAST4; 5..8: SETUP0_TAIL; 9..16: FIXED_CORRECT_G1;       *)
(* >= 17: GEN_CORRECT), following AES256_GCM_ENC_ALT_CORRECT's case tree.    *)
(* Entry pc+0x38, exit pc+0x1154.                                            *)
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

(* The two exported safety statements below are the terms mk_safety_spec     *)
(* generates from the correctness theorems and the C signature, pinned with  *)
(* ASSERT_CONCL_TAC so that the load fails unless the written statement is   *)
(* exactly the generated one.  The bounds size in/out from len_bits/8, then  *)
(* tag 16, ivec 16, key 240, htable 24*8 = 192 and the 80-byte frame; apart  *)
(* from the loaded code they constrain no memory contents.  ~keep_maychanges *)
(* keeps the correctness theorem's MAYCHANGE frame.                          *)
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

(* --- NOIBT subroutine safety: the 3-path wrapper corresponding to          *)
(* AES256_GCM_ENC_ALT_NOIBT_SUBROUTINE_CORRECT.  f_events dispatches on the  *)
(* public length guards (misaligned / zero / main); the main path is the     *)
(* prologue, a callee bigstep with AES256_GCM_ENC_ALT_SAFE (assumed as       *)
(* H_CORE; in-frame SP = word_sub sp 0x50) and the epilogue.  The statement  *)
(* is the mk_safety_spec-generated enc_safety_full_spec_tmc.                 *)
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
    (* ===== Path 3: misaligned length ===== *)
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
   [(* ===== Path 1: zero length ===== *)
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
  (* ===== Path 2: main (nonzero whole blocks) ===== *)
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

(* --- IBT subroutine safety: derived from the NOIBT one by
   ARM_ADD_IBT_RULE, as for AES256_GCM_ENC_ALT_SUBROUTINE_CORRECT. --- *)
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
(* No-access early-return guarantee.                                         *)
(*                                                                           *)
(* The exported CORRECT and SAFE theorems above still carry key/table/tag/   *)
(* counter, stack and separation premises even on a rejected call.  This     *)
(* extra pair exposes the guarantee that actually holds on the rejected path *)
(* -- len_bits = 0, or not a whole number of 128-bit blocks: the routine     *)
(* returns 0 and performs no memory event (no load, store or stack access),  *)
(* assuming nothing about the data, key, table, counter, stack pointer or    *)
(* separation, and no 2^63 bound.  The guard decides from len_bits (in X1)   *)
(* alone -- `cbz x1` on zero, `tst x1,#0x7f; b.ne` on a non-multiple of 128  *)
(* -- and falls into the shared mov w0,#0 / ret, so only PC, X0, the flags   *)
(* and the (branch-only) event trace change; no memory region is touched.    *)
(* `memaccess_inbounds e2 [] []` over the newly appended events e2 states    *)
(* that they contain no EventLoad/EventStore; the EventJump entries a branch *)
(* emits are permitted.  (The direct `read events s = e` cannot be used: a   *)
(* taken branch appends an EventJump, so the trace grows even with no memory *)
(* access; this follows the _SAFE specs' event idiom.)  The theorems are not *)
(* named *_SUBROUTINE_CORRECT/_SAFE, so tools/count-proofs.sh does not count *)
(* them and arm/proofs/specifications.txt does not list them.                *)
(* ------------------------------------------------------------------------- *)

(* Supply the APPEND-prefix witness for the newly appended events from the   *)
(* simulated final trace (`read events s = CONS .. (CONS .. e)` reassociated *)
(* as `APPEND e2 e`), so that `memaccess_inbounds e2 [] []` can then be      *)
(* discharged for the jump-only trace.                                       *)
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
   [(* Zero length: `cbz x1` is taken straight to L256_enc_ret. *)
    SUBGOAL_THEN `len_bits:int64 = word 0` SUBST_ALL_TAC THENL
     [ASM_REWRITE_TAC[GSYM VAL_EQ_0]; ALL_TAC] THEN
    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC AES256_GCM_ENC_ALT_EXEC [1;2;3] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    EVENTS_NOMEM_TAC THEN
    REWRITE_TAC[APPEND; memaccess_inbounds; ALL; EX; FST; SND];
    (* Not a whole number of blocks: `cbz x1` falls through, `tst x1,#0x7f`  *)
    (* leaves ZF clear so `b.ne` is taken, and L256_enc_ret returns 0.       *)
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

(* The default build keeps the `bti c` landing pad; reconstitute the padded  *)
(* statement for aes256_gcm_enc_alt_mc with ARM_ADD_IBT_RULE, as the         *)
(* exported SAFE theorem does.  No `~extra` is needed: the precondition has  *)
(* no opaque state predicate.                                                *)
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

(* Load-time check that the two REJECT_NOACCESS theorems have the intended   *)
(* shape: no hypotheses, a memaccess_inbounds conclusion and the right code  *)
(* constant.  They are not exported specifications, so nothing else          *)
(* checks them.                                                              *)
let () =
  let has_const th name =
    can (find_term (fun t -> is_const t && fst(dest_const t) = name)) (concl th) in
  let ok th codename =
    hyp th = [] && has_const th "memaccess_inbounds" && has_const th codename in
  if not (ok AES256_GCM_ENC_ALT_NOIBT_REJECT_NOACCESS "aes256_gcm_enc_alt_tmc")
  then failwith "AES256_GCM_ENC_ALT_NOIBT_REJECT_NOACCESS: unexpected shape";
  if not (ok AES256_GCM_ENC_ALT_REJECT_NOACCESS "aes256_gcm_enc_alt_mc")
  then failwith "AES256_GCM_ENC_ALT_REJECT_NOACCESS: unexpected shape";;
