(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Pointwise multiplication of polynomials in NTT domain for ML-DSA.         *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "common/mlkem_mldsa.ml";;

(**** print_literal_from_elf "arm/mldsa/mldsa_pointwise.o";;
 ****)

let mldsa_pointwise_mc = define_assert_from_elf
 "mldsa_pointwise_mc" "arm/mldsa/mldsa_pointwise.o"
[
  0x529c0023;       (* arm_MOV W3 (rvalue (word 57345)) *)
  0x72a00fe3;       (* arm_MOVK W3 (word 127) 16 *)
  0x4e040c60;       (* arm_DUP_GEN Q0 X3 32 128 *)
  0x52840023;       (* arm_MOV W3 (rvalue (word 8193)) *)
  0x72a07003;       (* arm_MOVK W3 (word 896) 16 *)
  0x4e040c61;       (* arm_DUP_GEN Q1 X3 32 128 *)
  0xd2800803;       (* arm_MOV X3 (rvalue (word 64)) *)
  0x3dc00431;       (* arm_LDR Q17 X1 (Immediate_Offset (word 16)) *)
  0x3dc00832;       (* arm_LDR Q18 X1 (Immediate_Offset (word 32)) *)
  0x3dc00c33;       (* arm_LDR Q19 X1 (Immediate_Offset (word 48)) *)
  0x3cc40430;       (* arm_LDR Q16 X1 (Postimmediate_Offset (word 64)) *)
  0x3dc00455;       (* arm_LDR Q21 X2 (Immediate_Offset (word 16)) *)
  0x3dc00856;       (* arm_LDR Q22 X2 (Immediate_Offset (word 32)) *)
  0x3dc00c57;       (* arm_LDR Q23 X2 (Immediate_Offset (word 48)) *)
  0x3cc40454;       (* arm_LDR Q20 X2 (Postimmediate_Offset (word 64)) *)
  0x0eb4c218;       (* arm_SMULL_VEC Q24 Q16 Q20 32 *)
  0x4eb4c219;       (* arm_SMULL2_VEC Q25 Q16 Q20 32 *)
  0x0eb5c23a;       (* arm_SMULL_VEC Q26 Q17 Q21 32 *)
  0x4eb5c23b;       (* arm_SMULL2_VEC Q27 Q17 Q21 32 *)
  0x0eb6c25c;       (* arm_SMULL_VEC Q28 Q18 Q22 32 *)
  0x4eb6c25d;       (* arm_SMULL2_VEC Q29 Q18 Q22 32 *)
  0x0eb7c27e;       (* arm_SMULL_VEC Q30 Q19 Q23 32 *)
  0x4eb7c27f;       (* arm_SMULL2_VEC Q31 Q19 Q23 32 *)
  0x4e991b10;       (* arm_UZP1 Q16 Q24 Q25 32 *)
  0x4ea19e10;       (* arm_MUL_VEC Q16 Q16 Q1 32 128 *)
  0x0ea0a218;       (* arm_SMLSL_VEC Q24 Q16 Q0 32 *)
  0x4ea0a219;       (* arm_SMLSL2_VEC Q25 Q16 Q0 32 *)
  0x4e995b10;       (* arm_UZP2 Q16 Q24 Q25 32 *)
  0x4e9b1b51;       (* arm_UZP1 Q17 Q26 Q27 32 *)
  0x4ea19e31;       (* arm_MUL_VEC Q17 Q17 Q1 32 128 *)
  0x0ea0a23a;       (* arm_SMLSL_VEC Q26 Q17 Q0 32 *)
  0x4ea0a23b;       (* arm_SMLSL2_VEC Q27 Q17 Q0 32 *)
  0x4e9b5b51;       (* arm_UZP2 Q17 Q26 Q27 32 *)
  0x4e9d1b92;       (* arm_UZP1 Q18 Q28 Q29 32 *)
  0x4ea19e52;       (* arm_MUL_VEC Q18 Q18 Q1 32 128 *)
  0x0ea0a25c;       (* arm_SMLSL_VEC Q28 Q18 Q0 32 *)
  0x4ea0a25d;       (* arm_SMLSL2_VEC Q29 Q18 Q0 32 *)
  0x4e9d5b92;       (* arm_UZP2 Q18 Q28 Q29 32 *)
  0x4e9f1bd3;       (* arm_UZP1 Q19 Q30 Q31 32 *)
  0x4ea19e73;       (* arm_MUL_VEC Q19 Q19 Q1 32 128 *)
  0x0ea0a27e;       (* arm_SMLSL_VEC Q30 Q19 Q0 32 *)
  0x4ea0a27f;       (* arm_SMLSL2_VEC Q31 Q19 Q0 32 *)
  0x4e9f5bd3;       (* arm_UZP2 Q19 Q30 Q31 32 *)
  0x3d800411;       (* arm_STR Q17 X0 (Immediate_Offset (word 16)) *)
  0x3d800812;       (* arm_STR Q18 X0 (Immediate_Offset (word 32)) *)
  0x3d800c13;       (* arm_STR Q19 X0 (Immediate_Offset (word 48)) *)
  0x3c840410;       (* arm_STR Q16 X0 (Postimmediate_Offset (word 64)) *)
  0xf1001063;       (* arm_SUBS X3 X3 (rvalue (word 4)) *)
  0xb5fffae3;       (* arm_CBNZ X3 (word 2096988) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let MLDSA_POINTWISE_EXEC = ARM_MK_EXEC_RULE mldsa_pointwise_mc;;