(* ========================================================================= *)
(* gcm_ghash_v8_s2n (AArch64, imported from aws-lc): GHASH over len = 16*n bytes. *)
(*                                                                           *)
(* Binary: arm/aes-gcm/gcm_ghash_v8_s2n.o  (305 instructions; the concatenation   *)
(* of aws-lc's gcm_ghash_v8_s2n and its fallthrough target gcm_ghash_v8_4x).      *)
(*                                                                           *)
(* Structure of the routine:                                                 *)
(*   leg A (0x000..0x16f)  len < 64: 2-blocks-per-pass .Loop_mod2x_v8 plus    *)
(*                         the .Lodd_tail_v8 single-block finisher.           *)
(*   leg B (0x170..0x4cc)  len >= 64: the 4-blocks-per-pass .Loop4x with its  *)
(*                         .Ltail4x / .Lone / .Ltwo / .Lthree cascade.        *)
(*                                                                           *)
(* NOTE (decode gap, leg B only -- RESOLVED): four of the 305 instruction     *)
(* words are 3-/4-register LD1 multiple-structure forms (0x4cdf6c34 @0x174,   *)
(* 0x4c406c3a @0x184, 0x4cdf2c44 @0x194+0x214, 0x4c406c44 @0x31c) that        *)
(* arm/proofs/decode.ml did not model; arm_LDP3/arm_LDP4 + arm_ldstp_3q/_4q   *)
(* were added on branch arm-ld1-multi-reg (merged at 5ef3e6289).  Both EXEC   *)
(* rules are built below: the leg-A SLICE (0, 0x170) that leg A is stated     *)
(* against, and the full-object GHASH_V8_EXEC that leg B needs.               *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "common/gmult_nblock_lemmas.ml";;
needs "common/ghash_nist_bridge.ml";;

(* ------------------------------------------------------------------------- *)
(* Machine code.  The literal is the full 305-word .text; the four           *)
(* unmodelled leg-B words carry a UNMODELLED-LD1-MULTI comment instead of an  *)
(* instruction (print_literal_from_elf itself raises on them).                *)
(* ------------------------------------------------------------------------- *)

let ghash_v8_mc = define_assert_from_elf "ghash_v8_mc"
  "arm/aes-gcm/gcm_ghash_v8_s2n.o"
[
  0xf101007f;       (* arm_CMP X3 (rvalue (word 64)) *)
  0x54000b62;       (* arm_BCS (word 364) *)
  0x4c407c00;       (* arm_LDR Q0 X0 No_Offset *)
  0xf1008063;       (* arm_SUBS X3 X3 (rvalue (word 32)) *)
  0xd280020c;       (* arm_MOV X12 (rvalue (word 16)) *)
  0x4cdfac34;       (* arm_LDP Q20 Q21 X1 (Postimmediate_Offset (word 32)) *)
  0x6e144294;       (* arm_EXT Q20 Q20 Q20 64 *)
  0x4f07e433;       (* arm_MOVI Q19 (word 16276538888567251425) *)
  0x4c407c36;       (* arm_LDR Q22 X1 No_Offset *)
  0x6e1642d6;       (* arm_EXT Q22 Q22 Q22 64 *)
  0x9a8c03ec;       (* arm_CSEL X12 XZR X12 Condition_EQ *)
  0x6e004000;       (* arm_EXT Q0 Q0 Q0 64 *)
  0x4cdf7c50;       (* arm_LDR Q16 X2 (Postimmediate_Offset (word 16)) *)
  0x4f795673;       (* arm_SHL_VEC Q19 Q19 57 64 128 *)
  0x4e200a10;       (* arm_REV64_VEC Q16 Q16 8 *)
  0x4e200800;       (* arm_REV64_VEC Q0 Q0 8 *)
  0x6e104203;       (* arm_EXT Q3 Q16 Q16 64 *)
  0x54000663;       (* arm_BCC (word 204) *)
  0x4ccc7c51;       (* arm_LDR Q17 X2 (Postreg_Offset X12) *)
  0x4e200a31;       (* arm_REV64_VEC Q17 Q17 8 *)
  0x6e114227;       (* arm_EXT Q7 Q17 Q17 64 *)
  0x6e201c63;       (* arm_EOR_VEC Q3 Q3 Q0 128 *)
  0x0ee7e284;       (* arm_PMULL_VEC Q4 Q20 Q7 64 *)
  0x6e271e31;       (* arm_EOR_VEC Q17 Q17 Q7 128 *)
  0x4ee7e286;       (* arm_PMULL2_VEC Q6 Q20 Q7 64 *)
  0x14000003;       (* arm_B (word 12) *)
  0xd503201f;       (* arm_NOP *)
  0xd503201f;       (* arm_NOP *)
  0x6e034072;       (* arm_EXT Q18 Q3 Q3 64 *)
  0xf1008063;       (* arm_SUBS X3 X3 (rvalue (word 32)) *)
  0x0ee3e2c0;       (* arm_PMULL_VEC Q0 Q22 Q3 64 *)
  0x9a8c33ec;       (* arm_CSEL X12 XZR X12 Condition_CC *)
  0x0ef1e2a5;       (* arm_PMULL_VEC Q5 Q21 Q17 64 *)
  0x6e231e52;       (* arm_EOR_VEC Q18 Q18 Q3 128 *)
  0x4ee3e2c2;       (* arm_PMULL2_VEC Q2 Q22 Q3 64 *)
  0x6e241c00;       (* arm_EOR_VEC Q0 Q0 Q4 128 *)
  0x4ef2e2a1;       (* arm_PMULL2_VEC Q1 Q21 Q18 64 *)
  0x4ccc7c50;       (* arm_LDR Q16 X2 (Postreg_Offset X12) *)
  0x6e261c42;       (* arm_EOR_VEC Q2 Q2 Q6 128 *)
  0x9a8c03ec;       (* arm_CSEL X12 XZR X12 Condition_EQ *)
  0x6e251c21;       (* arm_EOR_VEC Q1 Q1 Q5 128 *)
  0x6e024011;       (* arm_EXT Q17 Q0 Q2 64 *)
  0x6e221c12;       (* arm_EOR_VEC Q18 Q0 Q2 128 *)
  0x6e311c21;       (* arm_EOR_VEC Q1 Q1 Q17 128 *)
  0x4ccc7c51;       (* arm_LDR Q17 X2 (Postreg_Offset X12) *)
  0x4e200a10;       (* arm_REV64_VEC Q16 Q16 8 *)
  0x6e321c21;       (* arm_EOR_VEC Q1 Q1 Q18 128 *)
  0x0ef3e012;       (* arm_PMULL_VEC Q18 Q0 Q19 64 *)
  0x4e200a31;       (* arm_REV64_VEC Q17 Q17 8 *)
  0x6e084422;       (* arm_INS Q2 Q1 0 64 64 128 *)
  0x6e180401;       (* arm_INS Q1 Q0 64 0 64 64 *)
  0x6e114227;       (* arm_EXT Q7 Q17 Q17 64 *)
  0x6e104203;       (* arm_EXT Q3 Q16 Q16 64 *)
  0x6e321c20;       (* arm_EOR_VEC Q0 Q1 Q18 128 *)
  0x0ee7e284;       (* arm_PMULL_VEC Q4 Q20 Q7 64 *)
  0x6e221c63;       (* arm_EOR_VEC Q3 Q3 Q2 128 *)
  0x6e004012;       (* arm_EXT Q18 Q0 Q0 64 *)
  0x0ef3e000;       (* arm_PMULL_VEC Q0 Q0 Q19 64 *)
  0x6e321c63;       (* arm_EOR_VEC Q3 Q3 Q18 128 *)
  0x6e271e31;       (* arm_EOR_VEC Q17 Q17 Q7 128 *)
  0x6e201c63;       (* arm_EOR_VEC Q3 Q3 Q0 128 *)
  0x4ee7e286;       (* arm_PMULL2_VEC Q6 Q20 Q7 64 *)
  0x54fffbc2;       (* arm_BCS (word 2097016) *)
  0x6e321c42;       (* arm_EOR_VEC Q2 Q2 Q18 128 *)
  0x6e104203;       (* arm_EXT Q3 Q16 Q16 64 *)
  0xb1008063;       (* arm_ADDS X3 X3 (rvalue (word 32)) *)
  0x6e221c00;       (* arm_EOR_VEC Q0 Q0 Q2 128 *)
  0x54000280;       (* arm_BEQ (word 80) *)
  0x6e004012;       (* arm_EXT Q18 Q0 Q0 64 *)
  0x6e201c63;       (* arm_EOR_VEC Q3 Q3 Q0 128 *)
  0x6e321e11;       (* arm_EOR_VEC Q17 Q16 Q18 128 *)
  0x0ee3e280;       (* arm_PMULL_VEC Q0 Q20 Q3 64 *)
  0x6e231e31;       (* arm_EOR_VEC Q17 Q17 Q3 128 *)
  0x4ee3e282;       (* arm_PMULL2_VEC Q2 Q20 Q3 64 *)
  0x0ef1e2a1;       (* arm_PMULL_VEC Q1 Q21 Q17 64 *)
  0x6e024011;       (* arm_EXT Q17 Q0 Q2 64 *)
  0x6e221c12;       (* arm_EOR_VEC Q18 Q0 Q2 128 *)
  0x6e311c21;       (* arm_EOR_VEC Q1 Q1 Q17 128 *)
  0x6e321c21;       (* arm_EOR_VEC Q1 Q1 Q18 128 *)
  0x0ef3e012;       (* arm_PMULL_VEC Q18 Q0 Q19 64 *)
  0x6e084422;       (* arm_INS Q2 Q1 0 64 64 128 *)
  0x6e180401;       (* arm_INS Q1 Q0 64 0 64 64 *)
  0x6e321c20;       (* arm_EOR_VEC Q0 Q1 Q18 128 *)
  0x6e004012;       (* arm_EXT Q18 Q0 Q0 64 *)
  0x0ef3e000;       (* arm_PMULL_VEC Q0 Q0 Q19 64 *)
  0x6e221e52;       (* arm_EOR_VEC Q18 Q18 Q2 128 *)
  0x6e321c00;       (* arm_EOR_VEC Q0 Q0 Q18 128 *)
  0x4e200800;       (* arm_REV64_VEC Q0 Q0 8 *)
  0x6e004000;       (* arm_EXT Q0 Q0 Q0 64 *)
  0x4c007c00;       (* arm_STR Q0 X0 No_Offset *)
  0xd65f03c0;       (* arm_RET X30 *)
  0xd503201f;       (* arm_NOP *)
  0x4c407c00;       (* arm_LDR Q0 X0 No_Offset *)
  0x4cdf6c34;       (* UNMODELLED-LD1-MULTI *)
  0x6e144294;       (* arm_EXT Q20 Q20 Q20 64 *)
  0x6e1642d6;       (* arm_EXT Q22 Q22 Q22 64 *)
  0x4f07e433;       (* arm_MOVI Q19 (word 16276538888567251425) *)
  0x4c406c3a;       (* UNMODELLED-LD1-MULTI *)
  0x6e1a435a;       (* arm_EXT Q26 Q26 Q26 64 *)
  0x6e1c439c;       (* arm_EXT Q28 Q28 Q28 64 *)
  0x4f795673;       (* arm_SHL_VEC Q19 Q19 57 64 128 *)
  0x4cdf2c44;       (* UNMODELLED-LD1-MULTI *)
  0x4e200800;       (* arm_REV64_VEC Q0 Q0 8 *)
  0x4e2008a5;       (* arm_REV64_VEC Q5 Q5 8 *)
  0x4e2008c6;       (* arm_REV64_VEC Q6 Q6 8 *)
  0x4e2008e7;       (* arm_REV64_VEC Q7 Q7 8 *)
  0x4e200884;       (* arm_REV64_VEC Q4 Q4 8 *)
  0x6e0740f9;       (* arm_EXT Q25 Q7 Q7 64 *)
  0x6e0640d8;       (* arm_EXT Q24 Q6 Q6 64 *)
  0x6e0540b7;       (* arm_EXT Q23 Q5 Q5 64 *)
  0x0ef9e29d;       (* arm_PMULL_VEC Q29 Q20 Q25 64 *)
  0x6e391ce7;       (* arm_EOR_VEC Q7 Q7 Q25 128 *)
  0x4ef9e29f;       (* arm_PMULL2_VEC Q31 Q20 Q25 64 *)
  0x0ee7e2be;       (* arm_PMULL_VEC Q30 Q21 Q7 64 *)
  0x0ef8e2d0;       (* arm_PMULL_VEC Q16 Q22 Q24 64 *)
  0x6e381cc6;       (* arm_EOR_VEC Q6 Q6 Q24 128 *)
  0x4ef8e2d8;       (* arm_PMULL2_VEC Q24 Q22 Q24 64 *)
  0x4ee6e2a6;       (* arm_PMULL2_VEC Q6 Q21 Q6 64 *)
  0x6e301fbd;       (* arm_EOR_VEC Q29 Q29 Q16 128 *)
  0x6e381fff;       (* arm_EOR_VEC Q31 Q31 Q24 128 *)
  0x6e261fde;       (* arm_EOR_VEC Q30 Q30 Q6 128 *)
  0x0ef7e347;       (* arm_PMULL_VEC Q7 Q26 Q23 64 *)
  0x6e371ca5;       (* arm_EOR_VEC Q5 Q5 Q23 128 *)
  0x4ef7e357;       (* arm_PMULL2_VEC Q23 Q26 Q23 64 *)
  0x0ee5e365;       (* arm_PMULL_VEC Q5 Q27 Q5 64 *)
  0x6e271fbd;       (* arm_EOR_VEC Q29 Q29 Q7 128 *)
  0x6e371fff;       (* arm_EOR_VEC Q31 Q31 Q23 128 *)
  0x6e251fde;       (* arm_EOR_VEC Q30 Q30 Q5 128 *)
  0xf1020063;       (* arm_SUBS X3 X3 (rvalue (word 128)) *)
  0x540006a3;       (* arm_BCC (word 212) *)
  0x14000002;       (* arm_B (word 8) *)
  0xd503201f;       (* arm_NOP *)
  0x6e201c90;       (* arm_EOR_VEC Q16 Q4 Q0 128 *)
  0x4cdf2c44;       (* UNMODELLED-LD1-MULTI *)
  0x6e104203;       (* arm_EXT Q3 Q16 Q16 64 *)
  0x4e2008a5;       (* arm_REV64_VEC Q5 Q5 8 *)
  0x4e2008c6;       (* arm_REV64_VEC Q6 Q6 8 *)
  0x4e2008e7;       (* arm_REV64_VEC Q7 Q7 8 *)
  0x4e200884;       (* arm_REV64_VEC Q4 Q4 8 *)
  0x0ee3e380;       (* arm_PMULL_VEC Q0 Q28 Q3 64 *)
  0x6e231e10;       (* arm_EOR_VEC Q16 Q16 Q3 128 *)
  0x4ee3e382;       (* arm_PMULL2_VEC Q2 Q28 Q3 64 *)
  0x6e0740f9;       (* arm_EXT Q25 Q7 Q7 64 *)
  0x4ef0e361;       (* arm_PMULL2_VEC Q1 Q27 Q16 64 *)
  0x6e3d1c00;       (* arm_EOR_VEC Q0 Q0 Q29 128 *)
  0x6e3f1c42;       (* arm_EOR_VEC Q2 Q2 Q31 128 *)
  0x6e0640d8;       (* arm_EXT Q24 Q6 Q6 64 *)
  0x6e3e1c21;       (* arm_EOR_VEC Q1 Q1 Q30 128 *)
  0x6e0540b7;       (* arm_EXT Q23 Q5 Q5 64 *)
  0x6e024011;       (* arm_EXT Q17 Q0 Q2 64 *)
  0x6e221c12;       (* arm_EOR_VEC Q18 Q0 Q2 128 *)
  0x0ef9e29d;       (* arm_PMULL_VEC Q29 Q20 Q25 64 *)
  0x6e391ce7;       (* arm_EOR_VEC Q7 Q7 Q25 128 *)
  0x6e311c21;       (* arm_EOR_VEC Q1 Q1 Q17 128 *)
  0x4ef9e29f;       (* arm_PMULL2_VEC Q31 Q20 Q25 64 *)
  0x6e321c21;       (* arm_EOR_VEC Q1 Q1 Q18 128 *)
  0x0ee7e2be;       (* arm_PMULL_VEC Q30 Q21 Q7 64 *)
  0x0ef3e012;       (* arm_PMULL_VEC Q18 Q0 Q19 64 *)
  0x6e084422;       (* arm_INS Q2 Q1 0 64 64 128 *)
  0x6e180401;       (* arm_INS Q1 Q0 64 0 64 64 *)
  0x0ef8e2d0;       (* arm_PMULL_VEC Q16 Q22 Q24 64 *)
  0x6e381cc6;       (* arm_EOR_VEC Q6 Q6 Q24 128 *)
  0x4ef8e2d8;       (* arm_PMULL2_VEC Q24 Q22 Q24 64 *)
  0x6e321c20;       (* arm_EOR_VEC Q0 Q1 Q18 128 *)
  0x4ee6e2a6;       (* arm_PMULL2_VEC Q6 Q21 Q6 64 *)
  0x6e301fbd;       (* arm_EOR_VEC Q29 Q29 Q16 128 *)
  0x6e381fff;       (* arm_EOR_VEC Q31 Q31 Q24 128 *)
  0x6e261fde;       (* arm_EOR_VEC Q30 Q30 Q6 128 *)
  0x6e004012;       (* arm_EXT Q18 Q0 Q0 64 *)
  0x0ef3e000;       (* arm_PMULL_VEC Q0 Q0 Q19 64 *)
  0x0ef7e347;       (* arm_PMULL_VEC Q7 Q26 Q23 64 *)
  0x6e371ca5;       (* arm_EOR_VEC Q5 Q5 Q23 128 *)
  0x6e221e52;       (* arm_EOR_VEC Q18 Q18 Q2 128 *)
  0x4ef7e357;       (* arm_PMULL2_VEC Q23 Q26 Q23 64 *)
  0x0ee5e365;       (* arm_PMULL_VEC Q5 Q27 Q5 64 *)
  0x6e321c00;       (* arm_EOR_VEC Q0 Q0 Q18 128 *)
  0x6e271fbd;       (* arm_EOR_VEC Q29 Q29 Q7 128 *)
  0x6e371fff;       (* arm_EOR_VEC Q31 Q31 Q23 128 *)
  0x6e004000;       (* arm_EXT Q0 Q0 Q0 64 *)
  0x6e251fde;       (* arm_EOR_VEC Q30 Q30 Q5 128 *)
  0xf1010063;       (* arm_SUBS X3 X3 (rvalue (word 64)) *)
  0x54fff9e2;       (* arm_BCS (word 2096956) *)
  0x6e201c90;       (* arm_EOR_VEC Q16 Q4 Q0 128 *)
  0x6e104203;       (* arm_EXT Q3 Q16 Q16 64 *)
  0x0ee3e380;       (* arm_PMULL_VEC Q0 Q28 Q3 64 *)
  0x6e231e10;       (* arm_EOR_VEC Q16 Q16 Q3 128 *)
  0x4ee3e382;       (* arm_PMULL2_VEC Q2 Q28 Q3 64 *)
  0x4ef0e361;       (* arm_PMULL2_VEC Q1 Q27 Q16 64 *)
  0x6e3d1c00;       (* arm_EOR_VEC Q0 Q0 Q29 128 *)
  0x6e3f1c42;       (* arm_EOR_VEC Q2 Q2 Q31 128 *)
  0x6e3e1c21;       (* arm_EOR_VEC Q1 Q1 Q30 128 *)
  0xb1010063;       (* arm_ADDS X3 X3 (rvalue (word 64)) *)
  0x54000c20;       (* arm_BEQ (word 388) *)
  0xf100807f;       (* arm_CMP X3 (rvalue (word 32)) *)
  0x54000943;       (* arm_BCC (word 296) *)
  0x54000520;       (* arm_BEQ (word 164) *)
  0x6e024011;       (* arm_EXT Q17 Q0 Q2 64 *)
  0x6e221c12;       (* arm_EOR_VEC Q18 Q0 Q2 128 *)
  0x6e311c21;       (* arm_EOR_VEC Q1 Q1 Q17 128 *)
  0x4c406c44;       (* UNMODELLED-LD1-MULTI *)
  0x6e321c21;       (* arm_EOR_VEC Q1 Q1 Q18 128 *)
  0x4e2008a5;       (* arm_REV64_VEC Q5 Q5 8 *)
  0x4e2008c6;       (* arm_REV64_VEC Q6 Q6 8 *)
  0x4e200884;       (* arm_REV64_VEC Q4 Q4 8 *)
  0x0ef3e012;       (* arm_PMULL_VEC Q18 Q0 Q19 64 *)
  0x6e084422;       (* arm_INS Q2 Q1 0 64 64 128 *)
  0x6e180401;       (* arm_INS Q1 Q0 64 0 64 64 *)
  0x6e0640d8;       (* arm_EXT Q24 Q6 Q6 64 *)
  0x6e0540b7;       (* arm_EXT Q23 Q5 Q5 64 *)
  0x6e321c20;       (* arm_EOR_VEC Q0 Q1 Q18 128 *)
  0x0ef8e29d;       (* arm_PMULL_VEC Q29 Q20 Q24 64 *)
  0x6e381cc6;       (* arm_EOR_VEC Q6 Q6 Q24 128 *)
  0x6e004012;       (* arm_EXT Q18 Q0 Q0 64 *)
  0x0ef3e000;       (* arm_PMULL_VEC Q0 Q0 Q19 64 *)
  0x6e221e52;       (* arm_EOR_VEC Q18 Q18 Q2 128 *)
  0x4ef8e29f;       (* arm_PMULL2_VEC Q31 Q20 Q24 64 *)
  0x0ee6e2be;       (* arm_PMULL_VEC Q30 Q21 Q6 64 *)
  0x6e321c00;       (* arm_EOR_VEC Q0 Q0 Q18 128 *)
  0x0ef7e2c7;       (* arm_PMULL_VEC Q7 Q22 Q23 64 *)
  0x6e371ca5;       (* arm_EOR_VEC Q5 Q5 Q23 128 *)
  0x6e004000;       (* arm_EXT Q0 Q0 Q0 64 *)
  0x4ef7e2d7;       (* arm_PMULL2_VEC Q23 Q22 Q23 64 *)
  0x6e201c90;       (* arm_EOR_VEC Q16 Q4 Q0 128 *)
  0x4ee5e2a5;       (* arm_PMULL2_VEC Q5 Q21 Q5 64 *)
  0x6e104203;       (* arm_EXT Q3 Q16 Q16 64 *)
  0x6e271fbd;       (* arm_EOR_VEC Q29 Q29 Q7 128 *)
  0x6e371fff;       (* arm_EOR_VEC Q31 Q31 Q23 128 *)
  0x6e251fde;       (* arm_EOR_VEC Q30 Q30 Q5 128 *)
  0x0ee3e340;       (* arm_PMULL_VEC Q0 Q26 Q3 64 *)
  0x6e231e10;       (* arm_EOR_VEC Q16 Q16 Q3 128 *)
  0x4ee3e342;       (* arm_PMULL2_VEC Q2 Q26 Q3 64 *)
  0x0ef0e361;       (* arm_PMULL_VEC Q1 Q27 Q16 64 *)
  0x6e3d1c00;       (* arm_EOR_VEC Q0 Q0 Q29 128 *)
  0x6e3f1c42;       (* arm_EOR_VEC Q2 Q2 Q31 128 *)
  0x6e3e1c21;       (* arm_EOR_VEC Q1 Q1 Q30 128 *)
  0x14000036;       (* arm_B (word 216) *)
  0x6e024011;       (* arm_EXT Q17 Q0 Q2 64 *)
  0x6e221c12;       (* arm_EOR_VEC Q18 Q0 Q2 128 *)
  0x6e311c21;       (* arm_EOR_VEC Q1 Q1 Q17 128 *)
  0x4c40ac44;       (* arm_LDP Q4 Q5 X2 No_Offset *)
  0x6e321c21;       (* arm_EOR_VEC Q1 Q1 Q18 128 *)
  0x4e2008a5;       (* arm_REV64_VEC Q5 Q5 8 *)
  0x4e200884;       (* arm_REV64_VEC Q4 Q4 8 *)
  0x0ef3e012;       (* arm_PMULL_VEC Q18 Q0 Q19 64 *)
  0x6e084422;       (* arm_INS Q2 Q1 0 64 64 128 *)
  0x6e180401;       (* arm_INS Q1 Q0 64 0 64 64 *)
  0x6e0540b7;       (* arm_EXT Q23 Q5 Q5 64 *)
  0x6e321c20;       (* arm_EOR_VEC Q0 Q1 Q18 128 *)
  0x6e004012;       (* arm_EXT Q18 Q0 Q0 64 *)
  0x0ef3e000;       (* arm_PMULL_VEC Q0 Q0 Q19 64 *)
  0x6e221e52;       (* arm_EOR_VEC Q18 Q18 Q2 128 *)
  0x6e321c00;       (* arm_EOR_VEC Q0 Q0 Q18 128 *)
  0x6e004000;       (* arm_EXT Q0 Q0 Q0 64 *)
  0x0ef7e29d;       (* arm_PMULL_VEC Q29 Q20 Q23 64 *)
  0x6e371ca5;       (* arm_EOR_VEC Q5 Q5 Q23 128 *)
  0x6e201c90;       (* arm_EOR_VEC Q16 Q4 Q0 128 *)
  0x6e104203;       (* arm_EXT Q3 Q16 Q16 64 *)
  0x4ef7e29f;       (* arm_PMULL2_VEC Q31 Q20 Q23 64 *)
  0x0ee5e2be;       (* arm_PMULL_VEC Q30 Q21 Q5 64 *)
  0x0ee3e2c0;       (* arm_PMULL_VEC Q0 Q22 Q3 64 *)
  0x6e231e10;       (* arm_EOR_VEC Q16 Q16 Q3 128 *)
  0x4ee3e2c2;       (* arm_PMULL2_VEC Q2 Q22 Q3 64 *)
  0x4ef0e2a1;       (* arm_PMULL2_VEC Q1 Q21 Q16 64 *)
  0x6e3d1c00;       (* arm_EOR_VEC Q0 Q0 Q29 128 *)
  0x6e3f1c42;       (* arm_EOR_VEC Q2 Q2 Q31 128 *)
  0x6e3e1c21;       (* arm_EOR_VEC Q1 Q1 Q30 128 *)
  0x14000017;       (* arm_B (word 92) *)
  0xd503201f;       (* arm_NOP *)
  0x6e024011;       (* arm_EXT Q17 Q0 Q2 64 *)
  0x6e221c12;       (* arm_EOR_VEC Q18 Q0 Q2 128 *)
  0x6e311c21;       (* arm_EOR_VEC Q1 Q1 Q17 128 *)
  0x4c407c44;       (* arm_LDR Q4 X2 No_Offset *)
  0x6e321c21;       (* arm_EOR_VEC Q1 Q1 Q18 128 *)
  0x4e200884;       (* arm_REV64_VEC Q4 Q4 8 *)
  0x0ef3e012;       (* arm_PMULL_VEC Q18 Q0 Q19 64 *)
  0x6e084422;       (* arm_INS Q2 Q1 0 64 64 128 *)
  0x6e180401;       (* arm_INS Q1 Q0 64 0 64 64 *)
  0x6e321c20;       (* arm_EOR_VEC Q0 Q1 Q18 128 *)
  0x6e004012;       (* arm_EXT Q18 Q0 Q0 64 *)
  0x0ef3e000;       (* arm_PMULL_VEC Q0 Q0 Q19 64 *)
  0x6e221e52;       (* arm_EOR_VEC Q18 Q18 Q2 128 *)
  0x6e321c00;       (* arm_EOR_VEC Q0 Q0 Q18 128 *)
  0x6e004000;       (* arm_EXT Q0 Q0 Q0 64 *)
  0x6e201c90;       (* arm_EOR_VEC Q16 Q4 Q0 128 *)
  0x6e104203;       (* arm_EXT Q3 Q16 Q16 64 *)
  0x0ee3e280;       (* arm_PMULL_VEC Q0 Q20 Q3 64 *)
  0x6e231e10;       (* arm_EOR_VEC Q16 Q16 Q3 128 *)
  0x4ee3e282;       (* arm_PMULL2_VEC Q2 Q20 Q3 64 *)
  0x0ef0e2a1;       (* arm_PMULL_VEC Q1 Q21 Q16 64 *)
  0x6e024011;       (* arm_EXT Q17 Q0 Q2 64 *)
  0x6e221c12;       (* arm_EOR_VEC Q18 Q0 Q2 128 *)
  0x6e311c21;       (* arm_EOR_VEC Q1 Q1 Q17 128 *)
  0x6e321c21;       (* arm_EOR_VEC Q1 Q1 Q18 128 *)
  0x0ef3e012;       (* arm_PMULL_VEC Q18 Q0 Q19 64 *)
  0x6e084422;       (* arm_INS Q2 Q1 0 64 64 128 *)
  0x6e180401;       (* arm_INS Q1 Q0 64 0 64 64 *)
  0x6e321c20;       (* arm_EOR_VEC Q0 Q1 Q18 128 *)
  0x6e004012;       (* arm_EXT Q18 Q0 Q0 64 *)
  0x0ef3e000;       (* arm_PMULL_VEC Q0 Q0 Q19 64 *)
  0x6e221e52;       (* arm_EOR_VEC Q18 Q18 Q2 128 *)
  0x6e321c00;       (* arm_EOR_VEC Q0 Q0 Q18 128 *)
  0x6e004000;       (* arm_EXT Q0 Q0 Q0 64 *)
  0x4e200800;       (* arm_REV64_VEC Q0 Q0 8 *)
  0x4c007c00;       (* arm_STR Q0 X0 No_Offset *)
  0xd65f03c0;       (* arm_RET X30 *)
];;

(* Length of the full machine code, needed by mk_sublist_of_mc. *)
let GHASH_V8_LENGTH = prove
 (`LENGTH ghash_v8_mc = 1220`,
  REWRITE_TAC[ghash_v8_mc] THEN CONV_TAC(LAND_CONV LENGTH_CONV) THEN REFL_TAC);;

(* Leg-A slice: bytes [0, 0x170).  ARM_MK_EXEC_RULE succeeds here (all 92
   words decode), whereas it raises on the full list -- see the header note. *)
let ghash_v8_lega_mc_def, ghash_v8_lega_mc, GHASH_V8_LEGA_EXEC =
  mk_sublist_of_mc "ghash_v8_lega_mc" ghash_v8_mc (`0`,`0x170`)
    GHASH_V8_LENGTH;;

(* Full-object EXEC, for leg B (0x170..0x4cc).  This requires the 3-/4-register
   LD1/ST1 multiple-structure models added on branch arm-ld1-multi-reg
   (arm_LDP3/arm_LDP4 + arm_ldstp_3q/arm_ldstp_4q, decode.ml, merged at
   5ef3e6289); before that merge ARM_MK_EXEC_RULE RAISED on the full byte list.
   The leg-A slice above is KEPT: all of leg A is stated against it. *)
let GHASH_V8_EXEC = ARM_MK_EXEC_RULE ghash_v8_mc;;

(* ------------------------------------------------------------------------- *)
(* Spec vocabulary, lifted with provenance so this file's closure stays at    *)
(* base.ml + gmult_nblock_lemmas.ml + ghash_nist_bridge.ml (the 940 KB        *)
(* decrypt proof is deliberately NOT a dependency).                           *)
(* ------------------------------------------------------------------------- *)

(* From _docs/jargh_gcm/aes_gcm_enc_kernel_x4_ilp.ml:329, restricted to the 6
   slots this routine reads (Htable[0..5], 96 bytes).  h is the POLYVAL-side
   key; with h = ghash_twist H this is the x4 kernels' hypothesis shape. *)
let htable_mem_4 = new_definition
 `htable_mem_4 (h:int128) (ptr:int64) (s:armstate) <=>
  read (memory :> bytes128 ptr) s = byteswap128(h_power h 0) /\
  read (memory :> bytes128 (word_add ptr (word 16))) s =
    word_join (karatsuba_mid(h_power h 1) : 64 word)
              (karatsuba_mid(h_power h 0) : 64 word) /\
  read (memory :> bytes128 (word_add ptr (word 32))) s = byteswap128(h_power h 1) /\
  read (memory :> bytes128 (word_add ptr (word 48))) s = byteswap128(h_power h 2) /\
  read (memory :> bytes128 (word_add ptr (word 64))) s =
    word_join (karatsuba_mid(h_power h 3) : 64 word)
              (karatsuba_mid(h_power h 2) : 64 word) /\
  read (memory :> bytes128 (word_add ptr (word 80))) s = byteswap128(h_power h 3)`;;

(* From arm/proofs/aesv8_gcm_8x_dec_256_wb.ml:7622 / ~:7626. *)
let BREV_RF8_128 = prove
 (`word_bytereverse (x:int128) = word_reversefields 8 x`,
  REWRITE_TAC[REWRITE_RULE[FUN_EQ_THM] WORD_BYTEREVERSE_REVERSEFIELDS]);;

let BREV_RF8_INV_128 = prove
 (`!x:int128. word_bytereverse (word_reversefields 8 x) = x`,
  REWRITE_TAC[GSYM BREV_RF8_128; WORD_BYTEREVERSE_BYTEREVERSE]);;

(* NOTE: `nist_input_block` (decrypt file :7646) is deliberately NOT lifted here.
   Its body needs `bytes_to_int128`, which lives in arm/proofs/utils/aes_ctr_spec.ml
   -- outside this file's three-`needs` closure.  The band statements below quantify
   the input block as an `int128` read directly, so it is not needed until the
   byte-list-shaped export in Phase 10; lift it (with its substrate) there.
   Lifting it here made `new_definition` raise "term not closed: bytes_to_int128",
   which `loadt` swallows -- every definition after it silently vanished. *)

(* ------------------------------------------------------------------------- *)
(* Byte-order pipeline: rev64 (per-lane byte reverse) composed with ext #8    *)
(* (byteswap128, i.e. the 64-bit lane exchange) is a full 128-bit reversal.   *)
(* Mined from the stale probe branch ghash-v8-symbolic-sim:                   *)
(* arm/proofs/ghash_v8_sim.ml:111-140.  All feasible at 128 bits (< 0.3s).    *)
(* ------------------------------------------------------------------------- *)

let rev64_128 = new_definition
 `rev64_128 (x:int128) : int128 =
    word_join (word_bytereverse (word_subword x (64,64) : 64 word))
              (word_bytereverse (word_subword x (0,64) : 64 word))`;;

let REV64_EXT8_IS_BYTEREVERSE = prove
 (`!x:int128. byteswap128(rev64_128 x) = word_bytereverse x`,
  GEN_TAC THEN REWRITE_TAC[byteswap128; rev64_128] THEN BITBLAST_TAC);;

let EXT8_REV64_IS_BYTEREVERSE = prove
 (`!x:int128. rev64_128(byteswap128 x) = word_bytereverse x`,
  GEN_TAC THEN REWRITE_TAC[byteswap128; rev64_128] THEN BITBLAST_TAC);;

let BYTEREVERSE128_INVOLUTION = prove
 (`!x:int128. word_bytereverse(word_bytereverse x) = x`,
  GEN_TAC THEN BITBLAST_TAC);;

let BYTEREVERSE128_XOR = prove
 (`!x y:int128. word_bytereverse(word_xor x y) =
                word_xor (word_bytereverse x) (word_bytereverse y)`,
  REPEAT GEN_TAC THEN BITBLAST_TAC);;

(* The single-block GHASH core, once the byte-swaps have cancelled. *)
let GHASH_1BLOCK_CORRECT = prove
 (`!acc block h:int128.
     polyval_dot (word_xor acc block) h = ghash_polyval_acc h acc [block]`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ghash_polyval_acc; polyval_dot]);;

(* ------------------------------------------------------------------------- *)
(* Scalar rung lemmas: which branch each n takes.                            *)
(*   leg A -- n in {1,2,3}: n=1 takes b.lo at 0x044 (16 - 32 borrows),        *)
(*   n=2 exits via b.eq at 0x10c, n=3 falls through to .Lodd_tail_v8.         *)
(*   leg B -- n >= 4: k+1 full .Loop4x groups plus a remainder r < 4.         *)
(* ------------------------------------------------------------------------- *)

let LEGA_RUNG = prove
 (`!n. 1 <= n /\ n <= 3
       ==> (16 * n < 32 <=> n = 1) /\
           (16 * n = 32 <=> n = 2) /\
           (16 * n = 48 <=> n = 3)`,
  REPEAT STRIP_TAC THEN ASM_ARITH_TAC);;

let LEGB_RUNG = prove
 (`!n. 4 <= n ==> ?k r. r < 4 /\ n = 4 * (k + 1) + r`,
  REPEAT STRIP_TAC THEN
  EXISTS_TAC `(n - 4) DIV 4` THEN EXISTS_TAC `(n - 4) MOD 4` THEN
  MP_TAC(SPECL [`n - 4`; `4`] DIVISION) THEN ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Symbolic-simulation infrastructure for the leg-A bands.                    *)
(*                                                                           *)
(* CRITICAL ORDERING: EXT8_FOLD must be rewritten BEFORE                      *)
(* WORD_SIMPLE_SUBWORD_CONV.  The ARM `ext v,v,v,#8` emits                    *)
(* `word_subword (word_join x x : 256 word) (64,128)`; if the subword conv     *)
(* runs first it distributes that into a 256-bit byte tree, and any BITBLAST   *)
(* over such a tree exhausts memory and kills the HOL process.                *)
(* ------------------------------------------------------------------------- *)

let EXT8_FOLD = prove
 (`!x:int128. word_subword (word_join x x : 256 word) (64,128) = byteswap128 x`,
  GEN_TAC THEN REWRITE_TAC[byteswap128] THEN CONV_TAC WORD_BLAST);;

let BYTESWAP128_INVOLUTION = prove
 (`!x:int128. byteswap128(byteswap128 x) = x`,
  GEN_TAC THEN REWRITE_TAC[byteswap128] THEN CONV_TAC WORD_BLAST);;

(* The rev64 byte tree the stepper emits, folded back to `rev64_128`.  Built
   programmatically so the shape matches the stepper's output exactly. *)
let REV64_TREE_FOLD =
  let s8 x k = mk_comb(mk_comb(`word_subword:int128->num#num->8 word`,x),
                       mk_pair(mk_small_numeral k,`8`)) in
  let j16 a b = mk_comb(mk_comb(`word_join:8 word->8 word->16 word`,a),b) in
  let j32 a b = mk_comb(mk_comb(`word_join:16 word->16 word->32 word`,a),b) in
  let j64 a b = mk_comb(mk_comb(`word_join:32 word->32 word->64 word`,a),b) in
  let j128 a b = mk_comb(mk_comb(`word_join:64 word->64 word->128 word`,a),b) in
  let lane x b =
    j64 (j32 (j16 (s8 x b) (s8 x (b+8))) (j16 (s8 x (b+16)) (s8 x (b+24))))
        (j32 (j16 (s8 x (b+32)) (s8 x (b+40))) (j16 (s8 x (b+48)) (s8 x (b+56)))) in
  let revtree x = j128 (lane x 64) (lane x 0) in
  GEN_ALL(prove(mk_eq(revtree `x:int128`, `rev64_128 (x:int128)`),
    REWRITE_TAC[rev64_128] THEN CONV_TAC WORD_BLAST));;

(* Per-step normalizer.  It rewrites ONLY `read <reg> sN = <int128>`
   assumptions: a blanket RULE_ASSUM_TAC over every assumption mangles the
   `read PC sN = ...` fact, and the next ARM_STEPS_TAC then dies with
   "ARM_CONV: can't find `read PC .. = ..` from ths". *)
let Q128_NORM_TAC =
  let core = TOP_DEPTH_CONV(REWR_CONV EXT8_FOLD) THENC
             REWRITE_CONV[BYTESWAP128_INVOLUTION] THENC
             TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV THENC
             TOP_DEPTH_CONV(REWR_CONV EXT8_FOLD) THENC
             REWRITE_CONV[BYTESWAP128_INVOLUTION; REV64_TREE_FOLD;
                          REV64_EXT8_IS_BYTEREVERSE; EXT8_REV64_IS_BYTEREVERSE;
                          BYTEREVERSE128_INVOLUTION] in
  RULE_ASSUM_TAC(fun th ->
    let c = concl th in
    if is_eq c && type_of(rhs c) = `:int128` &&
       (try (let l = lhs c in is_comb l &&
             (let f = rator l in is_comb f &&
              fst(dest_const(fst(strip_comb f))) = "read")) with _ -> false)
    then CONV_RULE(RAND_CONV core) th else th);;

(* Cut-point for the store tails.  Every band ends `rev64 v0` + `ext` + `st1`,
   and `rev64` re-expands its operand into a 64-way byte tree, so that step's
   cost tracks the operand TERM SIZE, not the instruction count.  The
   accumulator arriving there is the last staged reduce -- 186 KB of term at
   n = 3 -- and the resulting blowup was, MEASURED (refiner session 163),
   766 s of GCM_GHASH_V8_LE3BLOCK's 805 s, 64 s of LEGB_TAIL3's 82 s and 48 s
   of LEGB_TAIL2's 60 s.  Abbreviating Q0 to an opaque atom across those steps
   makes them ~2 s.
   `UNABBREV_READ_TAC` then puts the term back for the algebra close, which
   does need it spelled out.  It must SUBST rather than `EXPAND_TAC`: the
   closes run `ASM_REWRITE_TAC`, which would otherwise use the surviving
   `<bigterm> = acc` assumption to fold the term straight back up.
   The two leg-B tails must ALSO re-fire `Q128_NORM_TAC` right after the
   restore: with the atom in place the normalizer never saw the byte tree, so
   `rev64_128 (byteswap128 X)` is still unfolded when the term comes back, the
   close's `REV64_AS_BSWAP_BREV` rewrite has nothing to match, and the failure
   surfaces much later as a bare `Failure "AP_TERM_TAC"`.  On LEGB_TAIL3 that
   was caught by the COLD gate AFTER the proof had passed twice warm -- a warm
   re-prove inherits rewrite state that hides it, so only a cold load is
   evidence for this edit. *)
let ABBREV_READ_TAC vname reg : tactic =
  fun ((asl,_) as g) ->
    let hit = find (fun c ->
        is_eq c &&
        (match strip_comb (lhs c) with
           (f,[r;_]) -> (try fst(dest_const f) = "read" with Failure _ -> false)
                        && r = reg
         | _ -> false))
      (map (concl o snd) asl) in
    ABBREV_TAC (mk_eq(mk_var(vname, type_of(rhs hit)), rhs hit)) g;;

let UNABBREV_READ_TAC vname : tactic =
  FIRST_X_ASSUM(fun th ->
    let c = concl th in
    if is_eq c && is_var(rhs c) && fst(dest_var(rhs c)) = vname
    then SUBST_ALL_TAC(SYM th) else failwith "UNABBREV_READ_TAC");;

(* ------------------------------------------------------------------------- *)
(* Algebra-close ingredients for the n = 1 band's GHASH postcondition.        *)
(*                                                                           *)
(* The value the assembly leaves in Q0 (and stores at xi_p) at s40 is         *)
(* `word_bytereverse (<byteform>)`, where <byteform> is a 3-summand XOR built *)
(* from exactly the atoms `build_GMULTn_fast 1` produces (the two `h_power h  *)
(* 0` lane pmulls, `karatsuba_mid (h_power h 0)`, and the reduce constant     *)
(* `word 13979173243358019584` = 0xC200000000000000).  The four lemmas below  *)
(* were measured against the LIVE s40 term and each fires; they are what the  *)
(* close needs beyond `build_GMULTn_fast 1` itself.                          *)
(*                                                                           *)
(* THE TYPE GOTCHA: `arm_INS` at 0x140/0x144 emits `word_insert` whose        *)
(* INSERTED argument is an `int128`, not a `64 word`.  A 64-bit-typed         *)
(* ins->join lemma silently fails to rewrite (`Failure "type_match"`), so     *)
(* BOTH width variants are needed.                                           *)
(* ------------------------------------------------------------------------- *)

let INS_TO_JOIN = prove
 (`!(x:int128) (y:64 word). word_insert x (0,64) y : int128 =
     word_join (word_subword x (64,64) : 64 word) y`,
  REPEAT GEN_TAC THEN CONV_TAC WORD_BLAST);;

let INS_HI_TO_JOIN = prove
 (`!(x:int128) (y:64 word). word_insert x (64,64) y : int128 =
     word_join y (word_subword x (0,64) : 64 word)`,
  REPEAT GEN_TAC THEN CONV_TAC WORD_BLAST);;

let INS128_TO_JOIN = prove
 (`!(x:int128) (y:int128). word_insert x (0,64) y : int128 =
     word_join (word_subword x (64,64) : 64 word) (word_subword y (0,64) : 64 word)`,
  REPEAT GEN_TAC THEN CONV_TAC WORD_BLAST);;

let INS128_HI_TO_JOIN = prove
 (`!(x:int128) (y:int128). word_insert x (64,64) y : int128 =
     word_join (word_subword y (0,64) : 64 word) (word_subword x (0,64) : 64 word)`,
  REPEAT GEN_TAC THEN CONV_TAC WORD_BLAST);;

(* The Karatsuba MID operand.  `eor v17,v16,v18` at 0x118 mixes the un-ext'd
   input register (rev64_128 blk0) with the ext'd accumulator, so the machine's
   mid input is NOT syntactically `karatsuba_mid`'s `lo XOR hi` shape.  This
   collapses it to exactly that shape (BITBLAST at 128 bits, ~2.2s). *)
let MID_FOLD = prove
 (`!(xi:int128) (blk0:int128).
     word_subword
       (word_xor (word_xor (word_bytereverse xi) (word_bytereverse blk0))
                 (word_xor (byteswap128 (word_bytereverse xi)) (rev64_128 blk0)))
       (0,64) : 64 word =
     word_xor
       (word_subword (word_xor (word_bytereverse xi) (word_bytereverse blk0))
                     (0,64) : 64 word)
       (word_subword (word_xor (word_bytereverse xi) (word_bytereverse blk0))
                     (64,64) : 64 word)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[byteswap128; rev64_128] THEN CONV_TAC WORD_BLAST);;

(* ------------------------------------------------------------------------- *)
(* The two lemmas that finish the n = 1 algebra close.                        *)
(*                                                                           *)
(* Both are stated over OPAQUE 128-bit atoms p1/p2/p3, which stand for the    *)
(* three Karatsuba partial products                                          *)
(*   p1 = pmul (mid H) (mid B),  p2 = pmul (lo H) (lo B),  p3 = pmul (hi H) (hi B)  *)
(* where H = h_power h 0 and B = xi' XOR blk0'.  Abstracting the pmuls is     *)
(* what makes these tractable: the raw machine-vs-spec diff is 4054 vs 3525   *)
(* chars, but over the abstracted atoms it is 397 vs 314, and `word_pmul` is  *)
(* opaque to BITBLAST anyway, so nothing is lost by hiding it.                *)
(*                                                                           *)
(* GHASH1_ARG_EQ: the two spellings of the reduce step's 64-bit argument agree. *)
(* (Named with the GHASH1_ prefix because bare `ARG_EQ` is a real HOL Light     *)
(* theorem name in Multivariate/transcendentals.ml -- outside this closure      *)
(* today, but a latent shadowing hazard upstream.)  The                         *)
(* machine builds it as `xor <wa> (join ...)` with a doubly-nested subword on *)
(* the low lane; build_GMULTn_fast states it as `xor (join ...) <wa>`.        *)
(* GHASH1_ALIGN: with that in hand, the whole 3-summand XOR aligns -- pure    *)
(* XOR/word_join/word_subword bookkeeping, ~1.7s at 128 bits.                 *)
(* ------------------------------------------------------------------------- *)

let GHASH1_ARG_EQ = prove
 (`!p1 p2 p3 p4:int128. ((word_subword ((word_xor (p4:(128)word) ((word_join 
     ((word_subword ((word_subword (p2:(128)word) (0,64)):(128)word) (0,64)):(64)word) 
     ((word_subword ((word_xor ((word_xor (p3:(128)word) (p2:(128)word)):(128)word) 
     ((word_xor ((word_subword ((word_join (p3:(128)word) (p2:(128)word)):(256)word) 
     (64,128)):(128)word) (p1:(128)word)):(128)word)):(128)word) (0,64)):(64)word)):(128)word)):(128)word) 
     (0,64)):(64)word) = ((word_subword ((word_xor ((word_join ((word_subword 
     (p2:(128)word) (0,64)):(64)word) ((word_xor ((word_subword (p2:(128)word) 
     (64,64)):(64)word) ((word_subword ((word_xor ((word_xor (p1:(128)word) 
     (p2:(128)word)):(128)word) (p3:(128)word)):(128)word) (0,64)):(64)word)):(64)word)):(128)word) 
     (p4:(128)word)):(128)word) (0,64)):(64)word)`,
  REPEAT GEN_TAC THEN BITBLAST_TAC);;

let GHASH1_ALIGN = prove
 (`!p1 p2 p3:int128. ((word_xor ((word_xor ((word_join ((word_subword (p3:(128)word) 
     (64,64)):(64)word) ((word_subword ((word_subword ((word_xor ((word_xor 
     (p3:(128)word) (p2:(128)word)):(128)word) ((word_xor ((word_subword 
     ((word_join (p3:(128)word) (p2:(128)word)):(256)word) (64,128)):(128)word) 
     (p1:(128)word)):(128)word)):(128)word) (64,64)):(128)word) (0,64)):(64)word)):(128)word) 
     (byteswap128 ((word_xor ((word_pmul ((word_subword (p2:(128)word) (0,64)):(64)word) 
     ((word 13979173243358019584):(64)word)):(128)word) ((word_join ((word_subword 
     ((word_subword (p2:(128)word) (0,64)):(128)word) (0,64)):(64)word) ((word_subword 
     ((word_xor ((word_xor (p3:(128)word) (p2:(128)word)):(128)word) ((word_xor 
     ((word_subword ((word_join (p3:(128)word) (p2:(128)word)):(256)word) 
     (64,128)):(128)word) (p1:(128)word)):(128)word)):(128)word) (0,64)):(64)word)):(128)word)):(128)word))):(128)word) 
     ((word_pmul ((word_subword ((word_xor ((word_pmul ((word_subword (p2:(128)word) 
     (0,64)):(64)word) ((word 13979173243358019584):(64)word)):(128)word) 
     ((word_join ((word_subword ((word_subword (p2:(128)word) (0,64)):(128)word) 
     (0,64)):(64)word) ((word_subword ((word_xor ((word_xor (p3:(128)word) 
     (p2:(128)word)):(128)word) ((word_xor ((word_subword ((word_join (p3:(128)word) 
     (p2:(128)word)):(256)word) (64,128)):(128)word) (p1:(128)word)):(128)word)):(128)word) 
     (0,64)):(64)word)):(128)word)):(128)word) (0,64)):(64)word) ((word 13979173243358019584):(64)word)):(128)word)):(128)word) 
     = ((word_xor ((word_pmul ((word_subword ((word_xor ((word_join ((word_subword 
     (p2:(128)word) (0,64)):(64)word) ((word_xor ((word_subword (p2:(128)word) 
     (64,64)):(64)word) ((word_subword ((word_xor ((word_xor (p1:(128)word) 
     (p2:(128)word)):(128)word) (p3:(128)word)):(128)word) (0,64)):(64)word)):(64)word)):(128)word) 
     ((word_pmul ((word_subword (p2:(128)word) (0,64)):(64)word) ((word 13979173243358019584):(64)word)):(128)word)):(128)word) 
     (0,64)):(64)word) ((word 13979173243358019584):(64)word)):(128)word) 
     ((word_xor (byteswap128 ((word_xor ((word_join ((word_subword (p2:(128)word) 
     (0,64)):(64)word) ((word_xor ((word_subword (p2:(128)word) (64,64)):(64)word) 
     ((word_subword ((word_xor ((word_xor (p1:(128)word) (p2:(128)word)):(128)word) 
     (p3:(128)word)):(128)word) (0,64)):(64)word)):(64)word)):(128)word) 
     ((word_pmul ((word_subword (p2:(128)word) (0,64)):(64)word) ((word 13979173243358019584):(64)word)):(128)word)):(128)word)) 
     ((word_join ((word_subword (p3:(128)word) (64,64)):(64)word) ((word_xor 
     ((word_subword (p3:(128)word) (0,64)):(64)word) ((word_subword ((word_xor 
     ((word_xor (p1:(128)word) (p2:(128)word)):(128)word) (p3:(128)word)):(128)word) 
     (64,64)):(64)word)):(64)word)):(128)word)):(128)word)):(128)word)`,
  REPEAT GEN_TAC THEN
  ABBREV_TAC `(p4:int128) = ((word_pmul ((word_subword (p2:(128)word) (0,64)):(64)word) ((word 13979173243358019584):(64)word)):(128)word)` THEN
  REWRITE_TAC[GHASH1_ARG_EQ] THEN
  ABBREV_TAC `(p5:int128) = ((word_pmul ((word_subword ((word_xor ((word_join ((word_subword (p2:(128)word) (0,64)):(64)word) ((word_xor ((word_subword (p2:(128)word) (64,64)):(64)word) ((word_subword ((word_xor ((word_xor (p1:(128)word) (p2:(128)word)):(128)word) (p3:(128)word)):(128)word) (0,64)):(64)word)):(64)word)):(128)word) (p4:(128)word)):(128)word) (0,64)):(64)word) ((word 13979173243358019584):(64)word)):(128)word)` THEN
  REWRITE_TAC[byteswap128] THEN BITBLAST_TAC);;

(* The spec-level chain, from the reduce output to the exported NIST vocabulary.
   `h_power h 0 = h` turns the reduce into `polyval_dot`, WORD_PMUL_SYM puts the
   accumulator on the left where `GHASH_1BLOCK_CORRECT` expects it, and
   `NIST_GHASH_IS_POLYVAL` (common/ghash_nist_bridge.ml) lands in `nist_ghash`. *)
let GHASH1_SPEC_CHAIN = prove
 (`!(H:int128) (h:int128) (xi:int128) (blk0:int128).
     h = ghash_twist H
     ==> polyval_reduce_prop3
           (word_pmul (h_power h 0)
                      (word_xor (word_bytereverse xi) (word_bytereverse blk0))) =
         nist_ghash H (word_bytereverse xi) [word_bytereverse blk0]`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[NIST_GHASH_IS_POLYVAL] THEN
  ASM_REWRITE_TAC[GSYM GHASH_1BLOCK_CORRECT] THEN
  REWRITE_TAC[polyval_dot; h_power] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [WORD_PMUL_SYM] THEN
  REFL_TAC);;

(* ------------------------------------------------------------------------- *)
(* Phase 2: the n = 1 (.Lodd_tail_v8) band, FULL nist_ghash postcondition.    *)
(*                                                                           *)
(* Control flow harvested from the live simulation (40 steps, hyps = 0):      *)
(*   s3  : `b.cs` @0x004 falls through (16 < 64).                             *)
(*   s18 : `b.lo` @0x044 IS taken -> PC = pc+0x110 = .Lodd_tail_v8, with      *)
(*         Q0 = word_bytereverse xi, Q3 = word_bytereverse blk0,              *)
(*         Q16 = rev64_128 blk0, Q20 = h_power h 0, Q22 = h_power h 1.        *)
(*   s26 : the Karatsuba triple is formed and separable --                    *)
(*         Q3 = xi' XOR blk0', Q0/Q2 = the lo/hi pmulls against h_power h 0.  *)
(*   s40 : PC = pc+0x168, the `ret`; Q0 and [xi_p] both hold the reduce.      *)
(*                                                                           *)
(* The close is: AP_TERM off the outer word_bytereverse, then the four ins->  *)
(* join folds + MID_FOLD + karatsuba_mid to reach the abstracted-atom shape,  *)
(* then GHASH1_ALIGN to match build_GMULTn_fast 1's LHS, then that theorem to *)
(* reach polyval_reduce_prop3 and GHASH1_SPEC_CHAIN to reach nist_ghash.      *)
(*                                                                           *)
(* Two constraints that are easy to rediscover the hard way:                  *)
(*  - C_ARGUMENTS MUST be expanded in the opening REWRITE_TAC.  Left folded,  *)
(*    `read X3 s = word 16` never reaches the goal, the `cmp x3,#0x40` at     *)
(*    0x000 cannot resolve, and step 2 dies with the misleading message       *)
(*    "ARM_CONV: can't find `read PC .. = ..` from ths".                      *)
(*  - the ABI-shaped MAYCHANGE frame is load-bearing; the narrower            *)
(*    per-register frame does NOT close (MONOTONE_MAYCHANGE_TAC fails on it). *)
(*    Tightening it is a Phase-11 concern -- leg A demonstrably touches only  *)
(*    Q0-Q7/Q16-Q22, so nothing is hidden, the theorem is merely weaker.      *)
(* ------------------------------------------------------------------------- *)

let GCM_GHASH_V8_LE1BLOCK = prove
 (`!xi_p htbl_p in_p pc H h xi blk0.
     h = ghash_twist H /\
     nonoverlapping (word pc, LENGTH ghash_v8_lega_mc) (xi_p,16) /\
     nonoverlapping (xi_p,16) (in_p,16) /\
     nonoverlapping (xi_p,16) (htbl_p,96)
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) ghash_v8_lega_mc /\
               read PC s = word pc /\
               C_ARGUMENTS [xi_p; htbl_p; in_p; word 16] s /\
               read (memory :> bytes128 xi_p) s = xi /\
               read (memory :> bytes128 in_p) s = blk0 /\
               htable_mem_4 h htbl_p s)
          (\s. read PC s = word (pc + 0x168) /\
               read (memory :> bytes128 xi_p) s =
               word_bytereverse
                 (nist_ghash H (word_bytereverse xi) [word_bytereverse blk0]))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(xi_p:int64,16)] ,,
           MAYCHANGE [Q0;Q1;Q2;Q3;Q4;Q5;Q6;Q7;
                      Q16;Q17;Q18;Q19;Q20;Q21;Q22;Q23;Q24;Q25;Q26;Q27;Q28;
                      Q29;Q30;Q31])`,
  REWRITE_TAC[C_ARGUMENTS; htable_mem_4; fst GHASH_V8_LEGA_EXEC;
              NONOVERLAPPING_CLAUSES] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC GHASH_V8_LEGA_EXEC (1--3) THEN
  MAP_EVERY (fun n -> ARM_STEPS_TAC GHASH_V8_LEGA_EXEC [n] THEN Q128_NORM_TAC)
            (4--37) THEN
  ABBREV_READ_TAC "acc1" `Q0` THEN
  MAP_EVERY (fun n -> ARM_STEPS_TAC GHASH_V8_LEGA_EXEC [n] THEN Q128_NORM_TAC)
            (38--40) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  EXPAND_TAC "acc1" THEN REPEAT CONJ_TAC THENL
   [AP_TERM_TAC THEN
    REWRITE_TAC[INS128_TO_JOIN; INS_TO_JOIN; INS128_HI_TO_JOIN;
                INS_HI_TO_JOIN; MID_FOLD; karatsuba_mid] THEN
    REWRITE_TAC[GHASH1_ALIGN] THEN
    REWRITE_TAC[snd(build_GMULTn_fast 1)] THEN
    MATCH_MP_TAC GHASH1_SPEC_CHAIN THEN REFL_TAC;
    REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    REPEAT CONJ_TAC THEN MONOTONE_MAYCHANGE_TAC THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Phase 3, part 1: the n = 2 band (one `.Loop_mod2x_v8` pass, exit via the   *)
(* `b.eq` at 0x10c straight to `.Ldone_v8`).                                  *)
(*                                                                           *)
(* Control flow (69 steps, machine-confirmed; exit pc + 0x168):               *)
(*   0x000..0x044  18 steps.  `b.cs` @0x004 falls through (32 < 64) and       *)
(*                 `b.cc` @0x044 ALSO falls through (32 - 32 does not borrow, *)
(*                 unlike n = 1 where 16 - 32 does), so the two-block loop is *)
(*                 entered instead of `.Lodd_tail_v8`.                        *)
(*   0x048..0x064   8 steps  (the loop preamble + the `b` at 0x064).          *)
(*   0x070..0x0f8  35 steps  (one `.Loop_mod2x_v8` pass).  The `b.hs`         *)
(*                 back-edge at 0x0f8 is NOT taken: x3 has reached 0 - 32,    *)
(*                 which borrows, so leg A really is three straight-line      *)
(*                 bands and needs no induction.                              *)
(*   0x0fc..0x10c   5 steps.  `adds x3,x3,#0x20` restores x3 to 0, so the     *)
(*                 `b.eq` at 0x10c IS taken -> `.Ldone_v8` (0x15c).           *)
(*   0x15c..0x164   3 steps  (rev64 + ext + st1), then `ret` at 0x168.        *)
(*                                                                           *)
(* Note the dead duplicate loads: `ld1 {v17.2d},[x2],x12` at 0x0b0 (and the   *)
(* 0x094 sibling) read at `in_p + 32` with x12 already zeroed by the `csel`   *)
(* chain, so the second read is at the SAME address as the first and no third *)
(* block is required to be readable.  That is why the precondition only needs *)
(* the two blocks at in_p and in_p + 16.                                      *)
(* ------------------------------------------------------------------------- *)

(* `rev64_128` and `byteswap128 o word_bytereverse` are the same map; used to
   put the machine's mid operands into `karatsuba_mid` shape below. *)
let REV64_AS_BSWAP_BREV = prove
 (`!x:int128. rev64_128 x = byteswap128 (word_bytereverse x)`,
  GEN_TAC THEN REWRITE_TAC[byteswap128; rev64_128] THEN CONV_TAC WORD_BLAST);;

(* Both lanes of `x XOR byteswap128 x` are `karatsuba_mid x`.  The n = 2 band
   needs BOTH: the block-1 mid is taken from lane 0 and the block-0 mid from
   lane 64 (MID_FOLD above covers only the n = 1 spelling). *)
let MID_FOLD_BSWAP_LO = prove
 (`!x:int128. word_subword (word_xor x (byteswap128 x)) (0,64) : 64 word =
              word_xor (word_subword x (0,64) : 64 word)
                       (word_subword x (64,64) : 64 word)`,
  GEN_TAC THEN REWRITE_TAC[byteswap128] THEN CONV_TAC WORD_BLAST);;

let MID_FOLD_BSWAP_HI = prove
 (`!x:int128. word_subword (word_xor x (byteswap128 x)) (64,64) : 64 word =
              word_xor (word_subword x (0,64) : 64 word)
                       (word_subword x (64,64) : 64 word)`,
  GEN_TAC THEN REWRITE_TAC[byteswap128] THEN CONV_TAC WORD_BLAST);;

(* THE KEY n = 2 ALGEBRA FINDING: no new BITBLAST is needed, and no `ARG_EQ`
   sibling for the mod2x reduce site either (session 152's reviewer expected
   one, because n = 2 reduces at 0xbc/0xe4 rather than n = 1's 0x13c/0x150).
   MEASURED via the s152 atom-abstraction method: after the ins->join and mid
   folds, the abstracted machine and spec terms are 575 vs 460 chars over 9
   `word_pmul` atoms, and the SIX block atoms enter ONLY through the three
   pairwise sums -- p2^p1 (the two Karatsuba mids), p4^p3 (the two lo products)
   and p6^p5 (the two hi products) -- exactly where n = 1 had three SINGLE
   atoms.  So the n = 2 alignment is `GHASH1_ALIGN` instantiated at those sums,
   modulo two XOR re-bracketings, and `GHASH1_ARG_EQ` travels inside it
   unchanged.

   The lemma is DERIVED as a rule rather than restated: the statement is a
   4.4 KB word tower, and deriving it keeps the two sides provably in step with
   GHASH1_ALIGN instead of duplicating it (an `aconv` check against the live
   goal was used to confirm the derivation lands on the right term). *)

let GHASH2_MID_UNCANON = prove
 (`!p1 p2 p3 p4 p5 p6:int128.
     word_xor (word_xor (word_xor p2 p1) (word_xor p4 p3)) (word_xor p6 p5) =
     word_xor (word_xor (word_xor p2 p4) p6) (word_xor (word_xor p1 p3) p5)`,
  REPEAT GEN_TAC THEN CONV_TAC WORD_RULE);;

let GHASH2_ALIGN =
  (* The three summed atoms, in the machine's order. *)
  let sums = [`word_xor (p2:int128) (p1:int128)`;
              `word_xor (p4:int128) (p3:int128)`;
              `word_xor (p6:int128) (p5:int128)`] in
  let base = SPECL sums GHASH1_ALIGN in
  (* LHS: the machine's outer XOR has the byteswap summand FIRST at n = 2. *)
  let l_fix = CONV_RULE (LAND_CONV(RATOR_CONV(RAND_CONV
                (REWR_CONV(CONJUNCT1 WORD_XOR_ACI))))) base in
  (* RHS: build_GMULTn_fast 2 states the mid accumulator as
     (m0+l0+h0) XOR (m1+l1+h1), not as the machine's summed-pair form. *)
  let r_fix = CONV_RULE (RAND_CONV(TOP_DEPTH_CONV
                (REWR_CONV GHASH2_MID_UNCANON))) l_fix in
  GENL [`p1:int128`;`p2:int128`;`p3:int128`;`p4:int128`;`p5:int128`;`p6:int128`]
       r_fix;;

(* The 2-block spec chain: the reduce of `H*blk1' + H^2*(xi'+blk0')` is
   `nist_ghash H xi' [blk0'; blk1']`, via GHASH_POLYVAL_ACC_2.  Note the
   summand order -- it is the order build_GMULTn_fast 2 produces (block 0 of
   its argument list is the HIGHEST H power in the assembly's numbering), so
   one WORD_XOR_ACI step is needed before WORD_PMUL_SYM. *)
let GHASH2_SPEC_CHAIN = prove
 (`!(H:int128) (h:int128) (xi:int128) (blk0:int128) (blk1:int128).
     h = ghash_twist H
     ==> polyval_reduce_prop3
           (word_xor
             (word_pmul (h_power h 0) (word_bytereverse blk1))
             (word_pmul (h_power h 1)
                        (word_xor (word_bytereverse xi) (word_bytereverse blk0)))) =
         nist_ghash H (word_bytereverse xi)
                      [word_bytereverse blk0; word_bytereverse blk1]`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[NIST_GHASH_IS_POLYVAL] THEN
  ASM_REWRITE_TAC[GHASH_POLYVAL_ACC_2] THEN
  REWRITE_TAC[h_power; ARITH_RULE `1 = SUC 0`; polyval_dot] THEN
  REWRITE_TAC[h_power] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [WORD_XOR_ACI] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [WORD_PMUL_SYM] THEN
  REFL_TAC);;

let GCM_GHASH_V8_LE2BLOCK = prove
 (`!xi_p htbl_p in_p pc H h xi blk0 blk1.
     h = ghash_twist H /\
     nonoverlapping (word pc, LENGTH ghash_v8_lega_mc) (xi_p,16) /\
     nonoverlapping (xi_p,16) (in_p,32) /\
     nonoverlapping (xi_p,16) (htbl_p,96)
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) ghash_v8_lega_mc /\
               read PC s = word pc /\
               C_ARGUMENTS [xi_p; htbl_p; in_p; word 32] s /\
               read (memory :> bytes128 xi_p) s = xi /\
               read (memory :> bytes128 in_p) s = blk0 /\
               read (memory :> bytes128 (word_add in_p (word 16))) s = blk1 /\
               htable_mem_4 h htbl_p s)
          (\s. read PC s = word (pc + 0x168) /\
               read (memory :> bytes128 xi_p) s =
               word_bytereverse
                 (nist_ghash H (word_bytereverse xi)
                    [word_bytereverse blk0; word_bytereverse blk1]))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(xi_p:int64,16)] ,,
           MAYCHANGE [Q0;Q1;Q2;Q3;Q4;Q5;Q6;Q7;
                      Q16;Q17;Q18;Q19;Q20;Q21;Q22;Q23;Q24;Q25;Q26;Q27;Q28;
                      Q29;Q30;Q31])`,
  REWRITE_TAC[C_ARGUMENTS; htable_mem_4; fst GHASH_V8_LEGA_EXEC;
              NONOVERLAPPING_CLAUSES] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC GHASH_V8_LEGA_EXEC (1--3) THEN
  MAP_EVERY (fun n -> ARM_STEPS_TAC GHASH_V8_LEGA_EXEC [n] THEN Q128_NORM_TAC)
            (4--66) THEN
  ABBREV_READ_TAC "acc2" `Q0` THEN
  MAP_EVERY (fun n -> ARM_STEPS_TAC GHASH_V8_LEGA_EXEC [n] THEN Q128_NORM_TAC)
            (67--69) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  EXPAND_TAC "acc2" THEN REPEAT CONJ_TAC THENL
   [AP_TERM_TAC THEN
    REWRITE_TAC[INS128_TO_JOIN; INS_TO_JOIN; INS128_HI_TO_JOIN;
                INS_HI_TO_JOIN; REV64_AS_BSWAP_BREV;
                MID_FOLD_BSWAP_LO; MID_FOLD_BSWAP_HI; karatsuba_mid] THEN
    REWRITE_TAC[GHASH2_ALIGN] THEN
    REWRITE_TAC[snd(build_GMULTn_fast 2)] THEN
    MATCH_MP_TAC GHASH2_SPEC_CHAIN THEN REFL_TAC;
    REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    REPEAT CONJ_TAC THEN MONOTONE_MAYCHANGE_TAC THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Phase 3, part 2: the n = 3 band.  One `.Loop_mod2x_v8` pass, then the      *)
(* `b.eq` at 0x10c is NOT taken (x3 was restored to 16, nonzero), so control  *)
(* FALLS THROUGH into `.Lodd_tail_v8` for the third block.                    *)
(*                                                                           *)
(* Control flow (88 steps, machine-confirmed; exit pc + 0x168):               *)
(*   0x000..0x044  18 steps.  Both `b.cs`@0x004 (48 < 64) and `b.cc`@0x044    *)
(*                 (48 - 32 does not borrow) fall through.                    *)
(*   0x048..0x064   8 steps  (loop preamble + the `b` at 0x064).              *)
(*   0x070..0x0f8  35 steps  (one `.Loop_mod2x_v8` pass; x3 reaches 16 - 32,  *)
(*                 which borrows, so the `b.hs` back-edge is NOT taken).      *)
(*   0x0fc..0x10c   5 steps.  `adds x3,x3,#0x20` restores x3 to 16, NONZERO,  *)
(*                 so `b.eq`@0x10c is NOT taken and we fall into the tail.    *)
(*   0x110..0x158  19 steps  (`.Lodd_tail_v8` -- the SECOND reduce).          *)
(*   0x15c..0x164   3 steps  (rev64 + ext + st1), then `ret` at 0x168.        *)
(*                                                                           *)
(* THE STRUCTURAL POINT (session 152's reviewer predicted it, session 153     *)
(* measured it): n = 3 is TWO STAGED REDUCES, not one.  The final term is a   *)
(* tail reduce whose accumulator argument is literally                        *)
(*   <loop-reduce output> XOR word_bytereverse blk2,                          *)
(* so a single `build_GMULTn_fast 3` is the wrong shape and                   *)
(* `GHASH_POLYVAL_ACC_3` (which states the single-reduce form) does not apply.*)
(*                                                                           *)
(* The close therefore CASCADES the two bands' align lemmas, innermost first: *)
(* `GHASH2_ALIGN` + `build_GMULTn_fast 2` collapse the inner (loop) reduce to *)
(* a `polyval_reduce_prop3`, which then sits as an opaque accumulator inside  *)
(* the outer reduce -- at which point `GHASH1_ALIGN` + `build_GMULTn_fast 1`  *)
(* collapse THAT.  No `ABBREV_TAC` of the accumulator is needed: rewriting    *)
(* the inner reduce first shrinks the term from 211 KB to under 400 chars, so *)
(* the outer stage runs at n = 1 size anyway.  Total algebra time: 0.6 s.     *)
(*                                                                           *)
(* Exactly ONE new BITBLAST is required beyond the n = 1 / n = 2 kit.         *)
(* ------------------------------------------------------------------------- *)

(* The tail's Karatsuba MID operand.  At n = 1 the accumulator entering
   `.Lodd_tail_v8` is `word_bytereverse xi`, so `MID_FOLD` matches its literal
   spelling.  At n = 3 the accumulator is the loop reduce's output and the
   `ext #8` has been DISTRIBUTED over the XOR by the per-step normalizer, giving
   `(x XOR y) XOR (byteswap128 x XOR byteswap128 y)`.  Neither `MID_FOLD` nor
   `MID_FOLD_BSWAP_LO` matches that, so state the distributed form directly.
   ~2 s at 128 bits. *)
let MID_FOLD_BSWAP_DIST = prove
 (`!x y:int128.
     word_subword (word_xor (word_xor x y)
                            (word_xor (byteswap128 x) (byteswap128 y)))
                  (0,64) : 64 word =
     word_xor (word_subword (word_xor x y) (0,64) : 64 word)
              (word_subword (word_xor x y) (64,64) : 64 word)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[byteswap128] THEN CONV_TAC WORD_BLAST);;

(* `GHASH1_SPEC_CHAIN` with an ARBITRARY accumulator rather than the
   `word_bytereverse xi` the n = 1 band happens to present.  The n = 3 tail
   consumes the loop reduce's output, which is not syntactically a
   `word_bytereverse`, so the chain has to be stated over a bare `acc`.  One
   `BYTEREVERSE128_INVOLUTION` is all it takes. *)
let GHASH1_SPEC_CHAIN_GEN = prove
 (`!(H:int128) (h:int128) (acc:int128) (blk:int128).
     h = ghash_twist H
     ==> polyval_reduce_prop3
           (word_pmul (h_power h 0) (word_xor acc (word_bytereverse blk))) =
         nist_ghash H acc [word_bytereverse blk]`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`H:int128`; `h:int128`; `word_bytereverse(acc:int128)`; `blk:int128`]
               GHASH1_SPEC_CHAIN) THEN
  ASM_REWRITE_TAC[BYTEREVERSE128_INVOLUTION]);;

(* The 3-block spec chain: the STAGED reduce equals `nist_ghash` over the
   three-element block list.  Stage 2 (the loop) is `GHASH2_SPEC_CHAIN`, stage 1
   (the tail) is `GHASH1_SPEC_CHAIN_GEN` at the accumulator stage 2 produced,
   and the two are glued by `NIST_GHASH_APPEND` at [b0;b1] ++ [b2] -- which is
   precisely the sense in which the machine's two reduces compose. *)
let GHASH3_SPEC_CHAIN = prove
 (`!(H:int128) (h:int128) (xi:int128) (blk0:int128) (blk1:int128) (blk2:int128).
     h = ghash_twist H
     ==> polyval_reduce_prop3
           (word_pmul (h_power h 0)
             (word_xor
               (polyval_reduce_prop3
                 (word_xor
                   (word_pmul (h_power h 0) (word_bytereverse blk1))
                   (word_pmul (h_power h 1)
                     (word_xor (word_bytereverse xi) (word_bytereverse blk0)))))
               (word_bytereverse blk2))) =
         nist_ghash H (word_bytereverse xi)
           [word_bytereverse blk0; word_bytereverse blk1; word_bytereverse blk2]`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`H:int128`;`h:int128`;`xi:int128`;`blk0:int128`;`blk1:int128`]
               GHASH2_SPEC_CHAIN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(SPECL [`H:int128`;`h:int128`;
                `nist_ghash H (word_bytereverse (xi:int128))
                   [word_bytereverse (blk0:int128); word_bytereverse (blk1:int128)]`;
                `blk2:int128`] GHASH1_SPEC_CHAIN_GEN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[GSYM(REWRITE_RULE[APPEND] (SPECL
     [`H:int128`; `[word_bytereverse (blk0:int128); word_bytereverse (blk1:int128)]`;
      `[word_bytereverse (blk2:int128)]`] NIST_GHASH_APPEND))]);;

let GCM_GHASH_V8_LE3BLOCK = prove
 (`!xi_p htbl_p in_p pc H h xi blk0 blk1 blk2.
     h = ghash_twist H /\
     nonoverlapping (word pc, LENGTH ghash_v8_lega_mc) (xi_p,16) /\
     nonoverlapping (xi_p,16) (in_p,48) /\
     nonoverlapping (xi_p,16) (htbl_p,96)
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) ghash_v8_lega_mc /\
               read PC s = word pc /\
               C_ARGUMENTS [xi_p; htbl_p; in_p; word 48] s /\
               read (memory :> bytes128 xi_p) s = xi /\
               read (memory :> bytes128 in_p) s = blk0 /\
               read (memory :> bytes128 (word_add in_p (word 16))) s = blk1 /\
               read (memory :> bytes128 (word_add in_p (word 32))) s = blk2 /\
               htable_mem_4 h htbl_p s)
          (\s. read PC s = word (pc + 0x168) /\
               read (memory :> bytes128 xi_p) s =
               word_bytereverse
                 (nist_ghash H (word_bytereverse xi)
                    [word_bytereverse blk0; word_bytereverse blk1;
                     word_bytereverse blk2]))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(xi_p:int64,16)] ,,
           MAYCHANGE [Q0;Q1;Q2;Q3;Q4;Q5;Q6;Q7;
                      Q16;Q17;Q18;Q19;Q20;Q21;Q22;Q23;Q24;Q25;Q26;Q27;Q28;
                      Q29;Q30;Q31])`,
  REWRITE_TAC[C_ARGUMENTS; htable_mem_4; fst GHASH_V8_LEGA_EXEC;
              NONOVERLAPPING_CLAUSES] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC GHASH_V8_LEGA_EXEC (1--3) THEN
  MAP_EVERY (fun n -> ARM_STEPS_TAC GHASH_V8_LEGA_EXEC [n] THEN Q128_NORM_TAC)
            (4--85) THEN
  ABBREV_READ_TAC "acc3" `Q0` THEN
  MAP_EVERY (fun n -> ARM_STEPS_TAC GHASH_V8_LEGA_EXEC [n] THEN Q128_NORM_TAC)
            (86--88) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  EXPAND_TAC "acc3" THEN REPEAT CONJ_TAC THENL
   [AP_TERM_TAC THEN
    REWRITE_TAC[INS128_TO_JOIN; INS_TO_JOIN; INS128_HI_TO_JOIN;
                INS_HI_TO_JOIN; REV64_AS_BSWAP_BREV;
                MID_FOLD_BSWAP_LO; MID_FOLD_BSWAP_HI; MID_FOLD;
                MID_FOLD_BSWAP_DIST; karatsuba_mid] THEN
    REWRITE_TAC[GHASH2_ALIGN] THEN
    REWRITE_TAC[snd(build_GMULTn_fast 2)] THEN
    REWRITE_TAC[GHASH1_ALIGN] THEN
    REWRITE_TAC[snd(build_GMULTn_fast 1)] THEN
    MATCH_MP_TAC GHASH3_SPEC_CHAIN THEN REFL_TAC;
    REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    REPEAT CONJ_TAC THEN MONOTONE_MAYCHANGE_TAC THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Phase 4: unify leg A.  ONE theorem for every length the routine accepts    *)
(* below 64 bytes, i.e. len = 16*n for n in {1,2,3}.                          *)
(*                                                                           *)
(* This is the first externally meaningful milestone and the place where the  *)
(* EXPORTED STATEMENT SHAPE is frozen, so leg B inherits it verbatim:         *)
(*  - the block count is a scalar `n` with `1 <= n /\ n <= 3` (leg B will     *)
(*    carry `4 <= n` instead; everything else is identical);                  *)
(*  - the input is a QUANTIFIED memory precondition                          *)
(*    `!i. i < n ==> read (memory :> bytes128 (in_p + 16*i)) s = blk i`       *)
(*    over an abstract `blk : num -> int128`, rather than n named variables;  *)
(*  - the postcondition is `word_bytereverse (nist_ghash H (word_bytereverse  *)
(*    xi) (MAP word_bytereverse (list_of_seq blk n)))` -- the same NIST       *)
(*    vocabulary the decrypt bands use, now indexed rather than spelled out;  *)
(*  - `nonoverlapping (xi_p,16) (in_p,16*n)`: only the `len` bytes actually   *)
(*    consumed need be readable (the duplicate `ld1 ...,[x2],x12` loads are   *)
(*    dead, x12 having been zeroed by the `csel` chain).                      *)
(*                                                                           *)
(* Each case reduces to the corresponding band theorem by pure bookkeeping.   *)
(* The one non-obvious step is the CONJ re-bracketing: expanding              *)
(* `!i. i < k ==> P i` into k conjuncts via FORALL_AND_THM produces a         *)
(* LEFT-nested `(P 0 /\ P 1) /\ rest`, while the band theorems state their    *)
(* preconditions right-nested.  MATCH_MP_TAC does not see through that, and   *)
(* a blanket `REWRITE_TAC[CONJ_ASSOC]` re-associates the WRONG way (it makes  *)
(* the mismatch worse, and the failure is the same opaque "MATCH_MP_TAC: No   *)
(* match" either way).  One `ONCE_DEPTH_CONV (REWR_CONV (GSYM CONJ_ASSOC))`   *)
(* per EXTRA block -- 0 at n = 1, 1 at n = 2, 2 at n = 3 -- fixes it exactly. *)
(* ------------------------------------------------------------------------- *)

let LEGA_CASE_TAC nrebrack blockthm =
  FIRST_X_ASSUM(fun th -> if is_eq(concl th) && lhs(concl th) = `n:num`
                          then SUBST_ALL_TAC th else NO_TAC) THEN
  RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN
  REWRITE_TAC[num_CONV `3`; num_CONV `2`; num_CONV `1`;
              list_of_seq; MAP; APPEND] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[ARITH_RULE `!i. i < 1 <=> i = 0`;
              ARITH_RULE `!i. i < 2 <=> i = 0 \/ i = 1`;
              ARITH_RULE `!i. i < 3 <=> i = 0 \/ i = 1 \/ i = 2`] THEN
  REWRITE_TAC[TAUT `(a \/ b ==> c) <=> (a ==> c) /\ (b ==> c)`;
              FORALL_AND_THM; FORALL_UNWIND_THM2] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN REWRITE_TAC[WORD_ADD_0] THEN
  REPLICATE_TAC nrebrack
    (CONV_TAC(ONCE_DEPTH_CONV(REWR_CONV(GSYM CONJ_ASSOC)))) THEN
  MATCH_MP_TAC blockthm THEN ASM_REWRITE_TAC[];;

let GCM_GHASH_V8_LEGA = prove
 (`!xi_p htbl_p in_p pc H h xi (blk:num->int128) n.
     h = ghash_twist H /\ 1 <= n /\ n <= 3 /\
     nonoverlapping (word pc, LENGTH ghash_v8_lega_mc) (xi_p,16) /\
     nonoverlapping (xi_p,16) (in_p,16 * n) /\
     nonoverlapping (xi_p,16) (htbl_p,96)
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) ghash_v8_lega_mc /\
               read PC s = word pc /\
               C_ARGUMENTS [xi_p; htbl_p; in_p; word (16 * n)] s /\
               read (memory :> bytes128 xi_p) s = xi /\
               (!i. i < n
                    ==> read (memory :> bytes128
                               (word_add in_p (word (16 * i)))) s = blk i) /\
               htable_mem_4 h htbl_p s)
          (\s. read PC s = word (pc + 0x168) /\
               read (memory :> bytes128 xi_p) s =
               word_bytereverse
                 (nist_ghash H (word_bytereverse xi)
                    (MAP word_bytereverse (list_of_seq blk n))))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(xi_p:int64,16)] ,,
           MAYCHANGE [Q0;Q1;Q2;Q3;Q4;Q5;Q6;Q7;
                      Q16;Q17;Q18;Q19;Q20;Q21;Q22;Q23;Q24;Q25;Q26;Q27;Q28;
                      Q29;Q30;Q31])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `n = 1 \/ n = 2 \/ n = 3` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC;
    LEGA_CASE_TAC 0 GCM_GHASH_V8_LE1BLOCK;
    LEGA_CASE_TAC 1 GCM_GHASH_V8_LE2BLOCK;
    LEGA_CASE_TAC 2 GCM_GHASH_V8_LE3BLOCK]);;

(* ------------------------------------------------------------------------- *)
(* Phase 5: the leg-B prologue (0x170 -> 0x200, 36 steps).                    *)
(*                                                                           *)
(* Leg B is entered by the `b.cs` at 0x004 when len >= 64.  The prologue      *)
(* loads Xi and the six H-table slots, loads the first four input blocks      *)
(* (x2 += 64), and computes the DEFERRED partial products                     *)
(*   Q29 = Sum pl,  Q31 = Sum ph,  Q30 = Sum pm                               *)
(* for H*I3 + H^2*I2 + H^3*I1, leaving H^4*(Xi + I0) to `.Loop4x` -- which is  *)
(* why Q0 = rev64 Xi and Q4 = rev64 I0 are still live and unmultiplied here.   *)
(* That staggering is what makes the `.Loop4x` invariant TWO-INDEXED (reduced  *)
(* accumulator at group i, deferred sums for group i+1).                       *)
(*                                                                           *)
(* This theorem stops one instruction BEFORE the `subs x3,x3,#0x80` at 0x200,  *)
(* so it is exactly the i = 0 invariant instance Phase 6 needs.                *)
(*                                                                           *)
(* SEAM STRENGTH: X3 is carried through as an opaque `c` and                   *)
(* `aligned_bytes_loaded` is re-asserted in the POSTcondition.  Both are       *)
(* needed to chain this band through `ENSURES_TRANS`.  The frame's             *)
(* `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI` covers `MODIFIABLE_GPRS`, hence *)
(* X3, so without the explicit conjunct nothing would be knowable about X3 at  *)
(* the 0x200 seam -- and X3 is exactly what the `subs`/`b.cc` there uses to    *)
(* decide `.Loop4x` vs `.Ltail4x` and how many iterations run.  The prologue   *)
(* itself never touches X3 (the `subs` is at 0x200, outside the band), so `c`  *)
(* passes through unchanged.                                                  *)
(*                                                                           *)
(* H-TABLE REGISTER MAP (the `ld1 ...,[x1],#48` at 0x174 post-increments x1,   *)
(* so the `ld1 ...,[x1]` at 0x184 reads htbl_p + 48/64/80):                    *)
(*   Q20 <- htbl_p+0   Q21 <- htbl_p+16 (mid pair, NOT ext'd)  Q22 <- +32      *)
(*   Q26 <- htbl_p+48  Q27 <- htbl_p+64 (mid pair, NOT ext'd)  Q28 <- +80      *)
(* The `ext #8` on Q20/Q22/Q26/Q28 cancels the `htable_mem_4` byteswap, which  *)
(* is why those four read as bare `h_power h k`.                               *)
(*                                                                           *)
(* Cost: the whole prologue sims in ~12s and the harvested register terms are  *)
(* only 300-360 chars -- two orders of magnitude cheaper than leg A's bands,   *)
(* because nothing has been reduced yet.  The Q30 close needs no new lemma:    *)
(* `REV64_AS_BSWAP_BREV` + `MID_FOLD_BSWAP_{LO,HI}` + `GSYM karatsuba_mid`     *)
(* folds both lanes of `x XOR rev64 x` to `karatsuba_mid (word_bytereverse b)`.*)
(*                                                                           *)
(* GOTCHA: the second `word_subword` argument of each `word_pmul` needs an     *)
(* explicit `: 64 word` annotation in the STATEMENT.  Without it HOL leaves    *)
(* the type generic and the conjunct fails to close against an otherwise       *)
(* character-identical simulated term.                                         *)
(* ------------------------------------------------------------------------- *)

let GCM_GHASH_V8_LEGB_PROLOGUE = prove
 (`!xi_p htbl_p in_p pc h xi b0 b1 b2 b3 c.
     nonoverlapping (word pc, LENGTH ghash_v8_mc) (xi_p,16)
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) ghash_v8_mc /\
               read PC s = word (pc + 0x170) /\
               read X0 s = xi_p /\ read X1 s = htbl_p /\ read X2 s = in_p /\
               read X3 s = c /\
               read (memory :> bytes128 xi_p) s = xi /\
               read (memory :> bytes128 in_p) s = b0 /\
               read (memory :> bytes128 (word_add in_p (word 16))) s = b1 /\
               read (memory :> bytes128 (word_add in_p (word 32))) s = b2 /\
               read (memory :> bytes128 (word_add in_p (word 48))) s = b3 /\
               htable_mem_4 h htbl_p s)
          (\s. aligned_bytes_loaded s (word pc) ghash_v8_mc /\
               read PC s = word (pc + 0x200) /\
               read X0 s = xi_p /\
               read X1 s = word_add htbl_p (word 48) /\
               read X2 s = word_add in_p (word 64) /\
               read X3 s = c /\
               read Q0 s = rev64_128 xi /\
               read Q4 s = rev64_128 b0 /\
               read Q19 s = word 257870231182273679357317742937744867328 /\
               read Q20 s = h_power h 0 /\
               read Q22 s = h_power h 1 /\
               read Q26 s = h_power h 2 /\
               read Q28 s = h_power h 3 /\
               read Q21 s = word_join (karatsuba_mid(h_power h 1) : 64 word)
                                      (karatsuba_mid(h_power h 0) : 64 word) /\
               read Q27 s = word_join (karatsuba_mid(h_power h 3) : 64 word)
                                      (karatsuba_mid(h_power h 2) : 64 word) /\
               read Q29 s =
                 word_xor
                   (word_pmul (word_subword (h_power h 2) (0,64) : 64 word)
                              (word_subword (word_bytereverse b1) (0,64) : 64 word))
                   (word_xor
                     (word_pmul (word_subword (h_power h 1) (0,64) : 64 word)
                                (word_subword (word_bytereverse b2) (0,64) : 64 word))
                     (word_pmul (word_subword (h_power h 0) (0,64) : 64 word)
                                (word_subword (word_bytereverse b3) (0,64) : 64 word))) /\
               read Q31 s =
                 word_xor
                   (word_pmul (word_subword (h_power h 2) (64,64) : 64 word)
                              (word_subword (word_bytereverse b1) (64,64) : 64 word))
                   (word_xor
                     (word_pmul (word_subword (h_power h 1) (64,64) : 64 word)
                                (word_subword (word_bytereverse b2) (64,64) : 64 word))
                     (word_pmul (word_subword (h_power h 0) (64,64) : 64 word)
                                (word_subword (word_bytereverse b3) (64,64) : 64 word))) /\
               read Q30 s =
                 word_xor
                   (word_pmul (karatsuba_mid (h_power h 2))
                              (karatsuba_mid (word_bytereverse b1)))
                   (word_xor
                     (word_pmul (karatsuba_mid (h_power h 1))
                                (karatsuba_mid (word_bytereverse b2)))
                     (word_pmul (karatsuba_mid (h_power h 0))
                                (karatsuba_mid (word_bytereverse b3)))))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [Q0;Q1;Q2;Q3;Q4;Q5;Q6;Q7;
                      Q16;Q17;Q18;Q19;Q20;Q21;Q22;Q23;Q24;Q25;Q26;Q27;Q28;
                      Q29;Q30;Q31])`,
  REWRITE_TAC[htable_mem_4; fst GHASH_V8_EXEC; NONOVERLAPPING_CLAUSES] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC GHASH_V8_EXEC (1--3) THEN
  MAP_EVERY (fun n -> ARM_STEPS_TAC GHASH_V8_EXEC [n] THEN Q128_NORM_TAC)
            (4--36) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  TRY(REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
      REPEAT CONJ_TAC THEN MONOTONE_MAYCHANGE_TAC THEN ASM_REWRITE_TAC[]) THEN
  TRY(REWRITE_TAC[REV64_AS_BSWAP_BREV; MID_FOLD_BSWAP_LO; MID_FOLD_BSWAP_HI;
                  GSYM karatsuba_mid] THEN REFL_TAC) THEN
  TRY(CONV_TAC WORD_RULE));;

(* ------------------------------------------------------------------------- *)
(* Phase 6: the `.Loop4x` invariant, bootstrapped and FROZEN.                 *)
(*                                                                           *)
(* The loop is 0x210..0x2d0 (49 instructions) plus the `b.cs 0x210` back-edge *)
(* at 0x2d4, i.e. 50 steps per iteration.  X3 counts DOWN, so this is a       *)
(* flag-conditional back-edge and the right tactic is ENSURES_WHILE_PUP_TAC   *)
(* with the CF fact as the "q" clause.                                        *)
(*                                                                           *)
(* LOOP COUNT.  `LEGB_RUNG` gives n = 4*(k+1) + r with r < 4.  X3 = 16n on    *)
(* entry at 0x170; `subs x3,#0x80` at 0x200 leaves 16n - 128, and the         *)
(* `b.cc 0x2d8` at 0x204 is taken iff 16n < 128 iff k = 0.  At the loop top   *)
(* with index i, X3 = 16n - 128 - 64i = 64*(k-i-1) + 16r, so the             *)
(* `subs x3,#0x40` at 0x2d0 sets CF (no borrow) iff i + 1 < k and the         *)
(* `b.cs` back-edge is taken exactly then.  Hence the loop runs EXACTLY k     *)
(* times and the "q" clause is `read CF s <=> i < k` -- note that at the      *)
(* exit instance i = k it reduces to `k < k`, i.e. false, which is what makes *)
(* the fall-through to `.Ltail4x` at 0x2d8 resolve.                           *)
(*                                                                           *)
(* THE INVARIANT IS TWO-INDEXED, and the assembly is what forces it: 0x214    *)
(* loads the NEXT group's four blocks into v4..v7 near the TOP of the body    *)
(* and the body rebuilds v29/v31/v30 from them.  So at the loop top with      *)
(* index i the machine holds                                                  *)
(*   Q0          the REDUCED accumulator over blocks 0..4i-1  (group i)       *)
(*   Q4          rev64 (blk (4i)), loaded but NOT yet multiplied              *)
(*   Q29/Q31/Q30 the DEFERRED Sum pl/ph/pm for blocks 4i+1, 4i+2, 4i+3        *)
(*               against h_power h 2 / 1 / 0  (group i+1's products)          *)
(* i.e. two clauses at DIFFERENT indices, exactly as the decrypt kernel's     *)
(* pipelined two-stream invariant.                                            *)
(*                                                                           *)
(* Every loop CONSTANT is re-asserted explicitly -- nothing is inherited      *)
(* across an ENSURES_WHILE step: the 0xc2 reduction constant in Q19, all six  *)
(* H-table registers in their post-`ext` form (Q20/Q22/Q26/Q28 and the two    *)
(* mid pairs Q21/Q27), X0/X1, the advanced input pointer X2, the counter X3,  *)
(* `aligned_bytes_loaded`, and the QUANTIFIED input-memory predicate.  The    *)
(* last one is the classic trap: it must be carried in the invariant, not     *)
(* rederived, because the body reads blocks 4i+4..4i+7 from it.               *)
(*                                                                           *)
(* The four helper definitions below exist so the invariant term stays        *)
(* readable and so the Phase-7 body proof can rewrite the deferred sums at    *)
(* index 4*(i+1) without re-typing 300-char word_pmul trees.                  *)
(* ------------------------------------------------------------------------- *)

let ghash_defer_lo = new_definition
 `ghash_defer_lo (h:int128) (blk:num->int128) (m:num) : int128 =
    word_xor
      (word_pmul (word_subword (h_power h 2) (0,64) : 64 word)
                 (word_subword (word_bytereverse (blk (m+1))) (0,64) : 64 word))
      (word_xor
        (word_pmul (word_subword (h_power h 1) (0,64) : 64 word)
                   (word_subword (word_bytereverse (blk (m+2))) (0,64) : 64 word))
        (word_pmul (word_subword (h_power h 0) (0,64) : 64 word)
                   (word_subword (word_bytereverse (blk (m+3))) (0,64) : 64 word)))`;;

let ghash_defer_hi = new_definition
 `ghash_defer_hi (h:int128) (blk:num->int128) (m:num) : int128 =
    word_xor
      (word_pmul (word_subword (h_power h 2) (64,64) : 64 word)
                 (word_subword (word_bytereverse (blk (m+1))) (64,64) : 64 word))
      (word_xor
        (word_pmul (word_subword (h_power h 1) (64,64) : 64 word)
                   (word_subword (word_bytereverse (blk (m+2))) (64,64) : 64 word))
        (word_pmul (word_subword (h_power h 0) (64,64) : 64 word)
                   (word_subword (word_bytereverse (blk (m+3))) (64,64) : 64 word)))`;;

let ghash_defer_mid = new_definition
 `ghash_defer_mid (h:int128) (blk:num->int128) (m:num) : int128 =
    word_xor
      (word_pmul (karatsuba_mid (h_power h 2))
                 (karatsuba_mid (word_bytereverse (blk (m+1)))))
      (word_xor
        (word_pmul (karatsuba_mid (h_power h 1))
                   (karatsuba_mid (word_bytereverse (blk (m+2)))))
        (word_pmul (karatsuba_mid (h_power h 0))
                   (karatsuba_mid (word_bytereverse (blk (m+3))))))`;;

(* The running accumulator, in the machine's rev64 register form.  Stated
   through the SAME `nist_ghash` vocabulary Phase 4 froze for leg A, so the
   Phase-9/10 recompose does not have to translate. *)
let ghash_acc_rev = new_definition
 `ghash_acc_rev (H:int128) (xi:int128) (blk:num->int128) (m:num) : int128 =
    rev64_128
      (word_bytereverse
        (nist_ghash H (word_bytereverse xi)
                      (MAP word_bytereverse (list_of_seq blk m))))`;;

let ghash_v8_loop4x_inv = new_definition
 `ghash_v8_loop4x_inv (pc:num) (xi_p:int64) (htbl_p:int64) (in_p:int64)
                      (H:int128) (h:int128) (xi:int128) (blk:num->int128)
                      (n:num) (i:num) (s:armstate) <=>
    aligned_bytes_loaded s (word pc) ghash_v8_mc /\
    read X0 s = xi_p /\
    read X1 s = word_add htbl_p (word 48) /\
    read X2 s = word_add in_p (word (64 * (i + 1))) /\
    read X3 s = word_sub (word (16 * n)) (word (128 + 64 * i)) /\
    (!j. j < n
         ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
             blk j) /\
    read Q19 s = word 257870231182273679357317742937744867328 /\
    read Q20 s = h_power h 0 /\
    read Q22 s = h_power h 1 /\
    read Q26 s = h_power h 2 /\
    read Q28 s = h_power h 3 /\
    read Q21 s = word_join (karatsuba_mid(h_power h 1) : 64 word)
                           (karatsuba_mid(h_power h 0) : 64 word) /\
    read Q27 s = word_join (karatsuba_mid(h_power h 3) : 64 word)
                           (karatsuba_mid(h_power h 2) : 64 word) /\
    read Q0 s = ghash_acc_rev H xi blk (4 * i) /\
    read Q4 s = rev64_128 (blk (4 * i)) /\
    read Q29 s = ghash_defer_lo h blk (4 * i) /\
    read Q31 s = ghash_defer_hi h blk (4 * i) /\
    read Q30 s = ghash_defer_mid h blk (4 * i)`;;

(* ------------------------------------------------------------------------- *)
(* The loop-ENTRY theorem: leg-B entry 0x170 -> the `.Loop4x` top 0x210.      *)
(*                                                                           *)
(* This is the Phase-5 prologue (36 steps) plus `subs x3,#0x80` @0x200, the   *)
(* NOT-taken `b.cc 0x2d8` @0x204, and the `b 0x210` @0x208 -- 39 steps.  It   *)
(* establishes the invariant at i = 0, so the Q0 clause degenerates:          *)
(* `ghash_acc_rev H xi blk 0` = `rev64_128 (word_bytereverse (nist_ghash H    *)
(* (word_bytereverse xi) []))` = `rev64_128 xi` by `nist_ghash`'s nil case    *)
(* plus `BYTEREVERSE128_INVOLUTION`, which is what the sim actually produces. *)
(*                                                                           *)
(* Resolving the `b.cc` needs the guard discharged BEFORE the branch step:    *)
(* the stepper emits `read PC s38 = if val (word (16*n)) < 128 then ... else`  *)
(* and `VAL_WORD_EQ` (under `16 * n < 2 EXP 64`) plus `128 <= 16 * n` (from   *)
(* `1 <= k`) fold it.  `RULE_ASSUM_TAC` with both facts collapses the         *)
(* conditional so step 39 decodes at the right offset.                        *)
(*                                                                           *)
(* The four input blocks must be specialized OUT of the quantified memory     *)
(* predicate before the `ld1 {v4-v7.2d},[x2],#64` at 0x194, via `FIRST_ASSUM` *)
(* (NOT `FIRST_X_ASSUM`) so the quantified form survives to the postcondition *)
(* -- the invariant re-asserts it.                                            *)
(* ------------------------------------------------------------------------- *)

let GCM_GHASH_V8_LEGB_ENTRY = prove
 (`!xi_p htbl_p in_p pc H h xi (blk:num->int128) n k r.
     h = ghash_twist H /\
     n = 4 * (k + 1) + r /\ r < 4 /\ 1 <= k /\ 16 * n < 2 EXP 64 /\
     nonoverlapping (word pc, LENGTH ghash_v8_mc) (xi_p,16) /\
     nonoverlapping (xi_p,16) (in_p,16 * n) /\
     nonoverlapping (xi_p,16) (htbl_p,96)
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) ghash_v8_mc /\
               read PC s = word (pc + 0x170) /\
               read X0 s = xi_p /\ read X1 s = htbl_p /\ read X2 s = in_p /\
               read X3 s = word (16 * n) /\
               read (memory :> bytes128 xi_p) s = xi /\
               (!j. j < n
                    ==> read (memory :> bytes128
                               (word_add in_p (word (16 * j)))) s = blk j) /\
               htable_mem_4 h htbl_p s)
          (\s. read PC s = word (pc + 0x210) /\
               ghash_v8_loop4x_inv pc xi_p htbl_p in_p H h xi blk n 0 s)
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [Q0;Q1;Q2;Q3;Q4;Q5;Q6;Q7;
                      Q16;Q17;Q18;Q19;Q20;Q21;Q22;Q23;Q24;Q25;Q26;Q27;Q28;
                      Q29;Q30;Q31])`,
  REWRITE_TAC[ghash_v8_loop4x_inv; ghash_acc_rev;
              ghash_defer_lo; ghash_defer_hi; ghash_defer_mid] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
  REWRITE_TAC[list_of_seq; MAP; nist_ghash; BYTEREVERSE128_INVOLUTION] THEN
  REWRITE_TAC[htable_mem_4; fst GHASH_V8_EXEC; NONOVERLAPPING_CLAUSES] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `128 <= 16 * n` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ENSURES_INIT_TAC "s0" THEN
  SUBGOAL_THEN
   `!j. j < 4
        ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s0 =
            blk j`
   (fun th -> MP_TAC(CONV_RULE (EXPAND_CASES_CONV THENC
                                ONCE_DEPTH_CONV NUM_MULT_CONV) th)) THENL
   [REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    REWRITE_TAC[WORD_ADD_0] THEN STRIP_TAC] THEN
  ARM_STEPS_TAC GHASH_V8_EXEC (1--3) THEN
  MAP_EVERY (fun m -> ARM_STEPS_TAC GHASH_V8_EXEC [m] THEN Q128_NORM_TAC)
            (4--36) THEN
  ARM_STEPS_TAC GHASH_V8_EXEC (37--38) THEN
  SUBGOAL_THEN
   `val (word (16 * (4 * (k + 1) + r)):int64) = 16 * (4 * (k + 1) + r)`
   ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(16 * (4 * (k + 1) + r) < 128)` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [ASSUME `val (word (16 * (4 * (k + 1) + r)):int64) = 16 * (4 * (k + 1) + r)`;
    ASSUME `~(16 * (4 * (k + 1) + r) < 128)`]) THEN
  ARM_STEPS_TAC GHASH_V8_EXEC [39] THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [GEN_REWRITE_TAC ONCE_DEPTH_CONV [GSYM(ASSUME `n = 4 * (k + 1) + r`)] THEN
    FIRST_X_ASSUM MATCH_ACCEPT_TAC;
    REWRITE_TAC[REV64_AS_BSWAP_BREV; MID_FOLD_BSWAP_LO; MID_FOLD_BSWAP_HI;
                GSYM karatsuba_mid] THEN REFL_TAC;
    REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    REPEAT CONJ_TAC THEN MONOTONE_MAYCHANGE_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Fire ENSURES_WHILE_PUP_TAC with the frozen invariant.  All FIVE subgoals   *)
(* are now proved: Phase 6 closed the four cheap ones and Phase 7 closed the  *)
(* body (i -> i+1), which is the third of the five.                           *)
(*                                                                           *)
(* TWO mechanical points that cost real time to find:                         *)
(*  1. `MAYCHANGE_IDEMPOT_TAC`, which every ENSURES_WHILE_* tactic fires as   *)
(*     its first conjunct, FAILS on `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_   *)
(*     ABI` because that constant is opaque (`ASSIGNS_SEQ_ABSORB_CONV` /      *)
(*     `EQ_MP` raise).  REWRITE it away BEFORE firing the loop tactic.  As a  *)
(*     consequence the four subgoals carry the EXPANDED frame, which is why   *)
(*     the entry theorem is transported in with the same rewrite applied.     *)
(*  2. The loop tactic's postcondition prepends `aligned_bytes_loaded` to the *)
(*     invariant, so the entry theorem (whose postcondition has it only       *)
(*     INSIDE the invariant) needs one `ENSURES_POSTCONDITION_THM` lift.      *)
(*     The implication is immediate from the invariant's own first conjunct.   *)
(*                                                                           *)
(* The back-edge and exit subgoals are each ONE step (the `b.cs` at 0x2d4,    *)
(* taken and not-taken respectively; the exit's guard resolves because the    *)
(* "q" clause at i = k reads `read CF s <=> k < k`, i.e. false, via LT_REFL). *)
(* Both then leave only the quantified-memory conjunct, which needs the       *)
(* `n = 4*(k+1)+r` substitution folded BACK (the sim carries the expanded     *)
(* bound) before `MATCH_ACCEPT_TAC` will take it.                             *)
(* ------------------------------------------------------------------------- *)

(* The entry theorem, transported to the exact shape the loop tactic's first
   subgoal wants: EXPANDED ABI frame, and `aligned_bytes_loaded` hoisted out of
   the invariant into the postcondition's leading conjunct.  Derived as an
   OCaml rule (no simulation) rather than restated, so the two can never
   drift. *)

let GCM_GHASH_V8_LEGB_ENTRY_ABL =
  let ent = REWRITE_RULE[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI]
   (SPECL [`xi_p:int64`;`htbl_p:int64`;`in_p:int64`;`pc:num`;`H:int128`;
           `h:int128`;`xi:int128`;`blk:num->int128`;`n:num`;`k:num`;`r:num`]
          GCM_GHASH_V8_LEGB_ENTRY) in
  let imp = prove
   (`!s. (read PC s = word (pc + 0x210) /\
          ghash_v8_loop4x_inv pc xi_p htbl_p in_p H h xi blk n 0 s)
         ==> aligned_bytes_loaded s (word pc) ghash_v8_mc /\
             read PC s = word (pc + 0x210) /\
             ghash_v8_loop4x_inv pc xi_p htbl_p in_p H h xi blk n 0 s`,
    GEN_TAC THEN REWRITE_TAC[ghash_v8_loop4x_inv] THEN MESON_TAC[]) in
  DISCH_ALL(MATCH_MP ENSURES_POSTCONDITION_THM (CONJ imp (UNDISCH ent)));;

(* ------------------------------------------------------------------------- *)
(* Phase 7 support: the counter/flag rung for the body's `subs x3,#0x40`.      *)
(*                                                                           *)
(* X3 enters the body as `word_sub (word (16*n)) (word (128 + 64*i))`; the    *)
(* `subs` at 0x2d0 subtracts another 0x40 and the `b.cs` reads its carry, so  *)
(* the body's flag obligation is exactly `64 <= val <that word> <=> i+1 < k`. *)
(* Both `word_sub`s collapse to a single `word (a - b)` because `128+64*i` is *)
(* genuinely <= `16*n` for `i < k` (from `n = 4*(k+1)+r`), which is what lets *)
(* `VAL_WORD_EQ` discharge the `val`.                                         *)
(* ------------------------------------------------------------------------- *)

let LOOP4X_CF = prove
 (`!k r i. i < k /\ r < 4 /\ 16 * (4 * (k + 1) + r) < 2 EXP 64
           ==> (64 <= val (word_sub (word (16 * (4 * (k + 1) + r)))
                                    (word (128 + 64 * i)) : int64) <=>
                i + 1 < k)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `word_sub (word (16 * (4 * (k + 1) + r))) (word (128 + 64 * i)) :int64 =
    word (16 * (4 * (k + 1) + r) - (128 + 64 * i))`
   SUBST1_TAC THENL
   [REWRITE_TAC[WORD_SUB] THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `val (word (16 * (4 * (k + 1) + r) - (128 + 64 * i)) : int64) =
    16 * (4 * (k + 1) + r) - (128 + 64 * i)` SUBST1_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Phase 7 support: the FOUR-block spec chain, i.e. the `.Loop4x` analogue of  *)
(* `GHASH2_SPEC_CHAIN` / `GHASH3_SPEC_CHAIN`.                                 *)
(*                                                                           *)
(* The body's single fused reduce absorbs four blocks at once against          *)
(* H^4/H^3/H^2/H, so `GHASH_POLYVAL_ACC_4` (the single-reduce four-block form) *)
(* is the right shape -- unlike n = 3 on leg A, which was two STAGED reduces   *)
(* and therefore needed the cascade instead.  Stated over an OPAQUE `acc` (not *)
(* `word_bytereverse xi`) so it applies at any loop index, which is what the   *)
(* symbolic-in-`i` accumulator needs.                                          *)
(*                                                                           *)
(* One spelling note: the final `WORD_PMUL_SYM` must be aimed at the RAND      *)
(* (the `ghash_polyval_acc` side, which writes the H-power SECOND), not the    *)
(* LAND as `GHASH2_SPEC_CHAIN` does -- at four blocks the LAND-directed        *)
(* version rewrites only the first product and `REFL_TAC` then fails.          *)
(* ------------------------------------------------------------------------- *)

let GHASH4_SPEC_CHAIN_GEN = prove
 (`!(H:int128) (h:int128) (acc:int128) b0 b1 b2 b3.
     h = ghash_twist H
     ==> polyval_reduce_prop3
           (word_xor
             (word_pmul (h_power h 3)
                        (word_xor acc (word_bytereverse b0)))
             (word_xor
               (word_pmul (h_power h 2) (word_bytereverse b1))
               (word_xor
                 (word_pmul (h_power h 1) (word_bytereverse b2))
                 (word_pmul (h_power h 0) (word_bytereverse b3))))) =
         nist_ghash H acc [word_bytereverse b0; word_bytereverse b1;
                           word_bytereverse b2; word_bytereverse b3]`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[NIST_GHASH_IS_POLYVAL] THEN
  ASM_REWRITE_TAC[GHASH_POLYVAL_ACC_4] THEN
  REWRITE_TAC[h_power; ARITH_RULE `1 = SUC 0`; ARITH_RULE `2 = SUC(SUC 0)`;
              ARITH_RULE `3 = SUC(SUC(SUC 0))`; polyval_dot] THEN
  REWRITE_TAC[h_power] THEN
  GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [WORD_PMUL_SYM] THEN
  REFL_TAC);;

(* The four-block unroll of `ghash_acc_rev`'s inner `nist_ghash`: index
   `m + 4` in terms of index `m`.  `list_of_seq` appends RIGHTWARD, so this is
   `NIST_GHASH_APPEND` applied four times; it is the lesson-4(a) vehicle for
   re-attaching the accumulator after the reduce close. *)

let LOOP4X_ACC_STEP4 = prove
 (`!H xi blk m.
     nist_ghash H (word_bytereverse xi)
       (MAP word_bytereverse (list_of_seq blk (m+4))) =
     nist_ghash H
       (nist_ghash H (word_bytereverse xi)
          (MAP word_bytereverse (list_of_seq blk m)))
       [word_bytereverse (blk m); word_bytereverse (blk (m+1));
        word_bytereverse (blk (m+2)); word_bytereverse (blk (m+3))]`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[ARITH_RULE `m+4 = SUC(SUC(SUC(SUC m)))`;
              ARITH_RULE `m+1 = SUC m`; ARITH_RULE `m+2 = SUC(SUC m)`;
              ARITH_RULE `m+3 = SUC(SUC(SUC m))`] THEN
  REWRITE_TAC[list_of_seq; MAP_APPEND; MAP] THEN
  REWRITE_TAC[GSYM APPEND_ASSOC] THEN
  REWRITE_TAC[NIST_GHASH_APPEND] THEN
  REWRITE_TAC[APPEND] THEN
  REWRITE_TAC[NIST_GHASH_CONS; nist_ghash]);;

(* ------------------------------------------------------------------------- *)
(* Phase 7 support: the four re-bracketings the accumulator close needs.       *)
(*                                                                           *)
(* All four are pure XOR-ACI (`WORD_RULE`, no BITBLAST).  They exist because  *)
(* the machine and `build_GMULTn_fast 4` accumulate the same four products in *)
(* different orders: the assembly XORs the DEFERRED sum (blocks 4i+1..4i+3,   *)
(* computed last iteration) with the FRESH H^4 product, so its block-0 term   *)
(* lands on the RIGHT, while the spec puts block 0 (the highest H power)       *)
(* leftmost and nests rightward.  `RESUM4` rotates the lo/hi sums; `MIDSUM4`  *)
(* does the same for the mid accumulator, which additionally interleaves the  *)
(* three per-block mid/lo/hi partials that Karatsuba subtracts.               *)
(*                                                                           *)
(* `XOR4_REASSOC_GEN` must be stated over `(N)word`, NOT `int128`: the reduce  *)
(* argument it re-brackets sits under a `word_join ... : 256 word`, so an      *)
(* int128-only version silently fails to match and `MATCH_MP_TAC` then reports *)
(* the opaque `No match`.                                                     *)
(* ------------------------------------------------------------------------- *)

let RESUM4 = prove
 (`!x0 x1 x2 x3:int128.
     word_xor (word_xor x1 (word_xor x2 x3)) x0 =
     word_xor x0 (word_xor x1 (word_xor x2 x3))`,
  REPEAT GEN_TAC THEN CONV_TAC WORD_RULE);;

let MIDSUM4 = prove
 (`!m0 m1 m2 m3 l0 l1 l2 l3 h0 h1 h2 h3:int128.
     word_xor
       (word_xor (word_xor (word_xor m1 (word_xor m2 m3)) m0)
                 (word_xor (word_xor l1 (word_xor l2 l3)) l0))
       (word_xor (word_xor h1 (word_xor h2 h3)) h0) =
     word_xor (word_xor (word_xor m0 l0) h0)
       (word_xor (word_xor (word_xor m1 l1) h1)
         (word_xor (word_xor (word_xor m2 l2) h2)
                   (word_xor (word_xor m3 l3) h3)))`,
  REPEAT GEN_TAC THEN CONV_TAC WORD_RULE);;

let XOR4_REASSOC_GEN = prove
 (`!a b c d:(N)word. word_xor (word_xor (word_xor a b) c) d =
                     word_xor a (word_xor b (word_xor c d))`,
  REPEAT GEN_TAC THEN CONV_TAC WORD_RULE);;

(* The machine's accumulator register carries `rev64_128` of the byte-reversed
   running value, and the body's `eor v16,v4,v0` XORs it with `rev64_128` of
   the raw block.  `rev64_128` distributes over XOR and is `byteswap128 o
   word_bytereverse`, so the pair collapses to `byteswap128` of the spec-side
   operand -- which is exactly what the reduce's `ext v0,v0,v0,#8` then undoes.
   One 128-bit BITBLAST. *)

let REV64_XOR_AS_BSWAP = prove
 (`!a b:int128. word_xor (rev64_128 (word_bytereverse a)) (rev64_128 b) =
                byteswap128 (word_xor a (word_bytereverse b))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[byteswap128; rev64_128] THEN BITBLAST_TAC);;

(* The three block indices the body's deferred-sum rebuild needs, so the
   `ghash_defer_*` clauses at `4*(i+1)` line up with what the sim produces
   for the newly-loaded blocks `4i+5 / 4i+6 / 4i+7`. *)

let LOOP4X_DEFER_IDX = ARITH_RULE
 `4 * (i + 1) + 1 = 4 * i + 5 /\
  4 * (i + 1) + 2 = 4 * i + 6 /\
  4 * (i + 1) + 3 = 4 * i + 7`;;

(* ------------------------------------------------------------------------- *)
(* Phase 7, part 1: the body's SIMULATION and nine of its ten postcondition   *)
(* conjuncts.                                                                *)
(*                                                                           *)
(* The `ld1 {v4.2d-v7.2d},[x2],#64` at 0x214 loads the NEXT group's four      *)
(* blocks, so four instances must be specialized out of the invariant's       *)
(* quantified input-memory predicate BEFORE that step -- via `FIRST_ASSUM`-   *)
(* style `SPEC`, never `FIRST_X_ASSUM`, because the quantified form has to    *)
(* survive to the postcondition (the invariant re-asserts it at i+1).         *)
(*                                                                           *)
(* CRITICAL and easy to get wrong: the 4-register `ld1` emits its three high  *)
(* addresses as a SINGLE `word_add in_p (word (64*(i+1) + 16))`, NOT as the   *)
(* nested `word_add (word_add in_p (word (64*(i+1)))) (word 16)` that the      *)
(* obvious spelling produces.  Supplying the nested form leaves Q5/Q6/Q7 as   *)
(* unresolved `read (memory :> ...) s1` facts, which `DISCARD_OLDSTATE_TAC`   *)
(* then ERASES on the next step -- silently, with no error, and the Q29/Q31/  *)
(* Q30 rebuild obligations become unprovable 40 steps later.  Spell the       *)
(* offsets FLAT.                                                             *)
(* ------------------------------------------------------------------------- *)

let LOOP4X_SETUP_BLK_TAC =
  SUBGOAL_THEN
   `read (memory :> bytes128 (word_add in_p (word (64 * (i+1))))) s1 =
      blk (4*i+4) /\
    read (memory :> bytes128 (word_add in_p (word (64 * (i+1) + 16)))) s1 =
      blk (4*i+5) /\
    read (memory :> bytes128 (word_add in_p (word (64 * (i+1) + 32)))) s1 =
      blk (4*i+6) /\
    read (memory :> bytes128 (word_add in_p (word (64 * (i+1) + 48)))) s1 =
      blk (4*i+7)`
   STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN
    (fun (asl,w) ->
       let jn = rand(rhs w) in
       (MP_TAC(SPEC jn (ASSUME
          `!j. j < n
               ==> read (memory :> bytes128
                          (word_add in_p (word (16 * j)))) s1 = blk j`)) THEN
        ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
        DISCH_THEN(SUBST1_TAC o SYM) THEN AP_THM_TAC THEN AP_TERM_TAC THEN
        AP_TERM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE) (asl,w));
    ALL_TAC];;

let GCM_GHASH_V8_LEGB_LOOP4X = prove
 (`!xi_p htbl_p in_p pc H h xi (blk:num->int128) n k r.
     h = ghash_twist H /\
     n = 4 * (k + 1) + r /\ r < 4 /\ 1 <= k /\ 16 * n < 2 EXP 64 /\
     nonoverlapping (word pc, LENGTH ghash_v8_mc) (xi_p,16) /\
     nonoverlapping (xi_p,16) (in_p,16 * n) /\
     nonoverlapping (xi_p,16) (htbl_p,96)
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) ghash_v8_mc /\
               read PC s = word (pc + 0x170) /\
               read X0 s = xi_p /\ read X1 s = htbl_p /\ read X2 s = in_p /\
               read X3 s = word (16 * n) /\
               read (memory :> bytes128 xi_p) s = xi /\
               (!j. j < n
                    ==> read (memory :> bytes128
                               (word_add in_p (word (16 * j)))) s = blk j) /\
               htable_mem_4 h htbl_p s)
          (\s. read PC s = word (pc + 0x2d8) /\
               ghash_v8_loop4x_inv pc xi_p htbl_p in_p H h xi blk n k s)
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [Q0;Q1;Q2;Q3;Q4;Q5;Q6;Q7;
                      Q16;Q17;Q18;Q19;Q20;Q21;Q22;Q23;Q24;Q25;Q26;Q27;Q28;
                      Q29;Q30;Q31])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  ENSURES_WHILE_PUP_TAC `k:num` `pc + 0x210` `pc + 0x2d4`
    `\i s. ghash_v8_loop4x_inv pc xi_p htbl_p in_p H h xi blk n i s /\
           (read CF s <=> i < k)` THEN
  REPEAT CONJ_TAC THENL
   [(* 1. k is nonzero *)
    ASM_ARITH_TAC;

    (* 2. loop ENTRY: 0x170 -> 0x210, from GCM_GHASH_V8_LEGB_ENTRY *)
    MATCH_MP_TAC GCM_GHASH_V8_LEGB_ENTRY_ABL THEN ASM_REWRITE_TAC[];

    (* 3. the BODY, i -> i+1: Phase 7.  49 instructions + the b.cs.
       Simulates in ~14 s (leg B's body has ONE reduce over ONE group, so
       nothing accumulates across i and the terms stay in the low thousands
       of chars rather than leg A's 205 KB).  After the final state and one
       `REPEAT CONJ_TAC` there are exactly NINE conjuncts -- see the note on
       the last branch: the skeleton already rewrote the opaque ABI constant
       away, so `ENSURES_FINAL_STATE_TAC` discharges the frame itself and
       there is no tenth MAYCHANGE branch.  The fourth of the nine is the
       GHASH accumulator, `read Q0 = ghash_acc_rev ... at 4*(i+1)`, which is
       BRIEF lesson 4's target and is closed in place below. *)
    REPEAT STRIP_TAC THEN
    REWRITE_TAC[ghash_v8_loop4x_inv] THEN
    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC GHASH_V8_EXEC [1] THEN
    LOOP4X_SETUP_BLK_TAC THEN
    MAP_EVERY (fun m -> ARM_STEPS_TAC GHASH_V8_EXEC [m] THEN Q128_NORM_TAC)
              (2--49) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ghash_v8_loop4x_inv] THEN REPEAT CONJ_TAC THENL
     [(* X2 advances one group *)
      CONV_TAC WORD_RULE;

      (* X3: the body's own `subs x3,#0x40` *)
      CONV_TAC WORD_RULE;

      (* the quantified input memory, with `n` folded back *)
      GEN_REWRITE_TAC ONCE_DEPTH_CONV [GSYM(ASSUME `n = 4 * (k + 1) + r`)] THEN
      FIRST_X_ASSUM MATCH_ACCEPT_TAC;

      (* THE GHASH ACCUMULATOR at 4*(i+1) -- BRIEF lesson 4, both halves.
         (a) re-attach: `LOOP4X_ACC_STEP4` peels the four blocks off the
             spec side and `ABBREV_TAC` makes the residual running value an
             OPAQUE `AC` (6029 -> 6204 chars), so the reduce close never sees
             the loop index.  `REV64_XOR_AS_BSWAP` then collapses the
             machine's `rev64` pair into `byteswap128` of the spec operand,
             and abbreviating the three deferred sums brings the goal to
             4290 chars -- at which point it is SHAPE-IDENTICAL to leg A's
             single-reduce close.
         (b) attach at the INPUT accumulators: `GHASH1_ALIGN` applies with
             its three variables instantiated at the three SUMS (exactly the
             n = 2 / n = 3 reuse), so NO new align lemma and no new BITBLAST
             at the reduce.  Expanding the deferred sums and rotating with
             MIDSUM4 / RESUM4 then makes the machine term `aconv`-IDENTICAL
             to `build_GMULTn_fast 4`'s LHS (verified: 12319 chars, both
             sides), and `GHASH4_SPEC_CHAIN_GEN` lands in `nist_ghash`.
         The only genuinely new algebra is four XOR-ACI re-bracketings. *)
      REWRITE_TAC[ARITH_RULE `4 * (i + 1) = 4 * i + 4`] THEN
      REWRITE_TAC[ghash_acc_rev] THEN
      REWRITE_TAC[LOOP4X_ACC_STEP4] THEN
      ABBREV_TAC `AC:int128 = nist_ghash H (word_bytereverse xi)
                    (MAP word_bytereverse (list_of_seq blk (4 * i)))` THEN
      REWRITE_TAC[REV64_XOR_AS_BSWAP; BYTESWAP128_INVOLUTION] THEN
      ABBREV_TAC `DL:int128 = ghash_defer_lo (ghash_twist H) blk (4 * i)` THEN
      ABBREV_TAC `DH:int128 = ghash_defer_hi (ghash_twist H) blk (4 * i)` THEN
      ABBREV_TAC `DM:int128 = ghash_defer_mid (ghash_twist H) blk (4 * i)` THEN
      GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [REV64_AS_BSWAP_BREV] THEN
      GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV)
                      [BYTEREVERSE128_INVOLUTION] THEN
      AP_TERM_TAC THEN
      REWRITE_TAC[INS128_TO_JOIN; INS_TO_JOIN; INS128_HI_TO_JOIN;
                  INS_HI_TO_JOIN; MID_FOLD_BSWAP_LO; MID_FOLD_BSWAP_HI;
                  karatsuba_mid] THEN
      REWRITE_TAC[GHASH1_ALIGN] THEN
      MAP_EVERY EXPAND_TAC ["DL"; "DH"; "DM"] THEN
      REWRITE_TAC[ghash_defer_lo; ghash_defer_hi; ghash_defer_mid;
                  karatsuba_mid] THEN
      CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
      GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [MIDSUM4] THEN
      GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [RESUM4] THEN
      REWRITE_TAC[snd(build_GMULTn_fast 4)] THEN
      REWRITE_TAC[XOR4_REASSOC_GEN] THEN
      MATCH_MP_TAC GHASH4_SPEC_CHAIN_GEN THEN REFL_TAC;

      (* Q4 = the new group's block 4(i+1) *)
      AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;

      (* Q29/Q31/Q30: the deferred sums rebuilt from the newly loaded
         v5/v6/v7.  Pre-reduce, so they close in folded vocabulary. *)
      ASM_REWRITE_TAC[ghash_defer_lo] THEN
      CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
      REWRITE_TAC[LOOP4X_DEFER_IDX] THEN REFL_TAC;

      ASM_REWRITE_TAC[ghash_defer_hi] THEN
      CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
      REWRITE_TAC[LOOP4X_DEFER_IDX] THEN REFL_TAC;

      ASM_REWRITE_TAC[ghash_defer_mid] THEN
      CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
      REWRITE_TAC[LOOP4X_DEFER_IDX] THEN
      REWRITE_TAC[REV64_AS_BSWAP_BREV; MID_FOLD_BSWAP_LO; MID_FOLD_BSWAP_HI;
                  GSYM karatsuba_mid] THEN REFL_TAC;

      (* the flag fact the back-edge reads.  NOTE there is no MAYCHANGE
         conjunct here: the skeleton already rewrote
         `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI` away before firing the
         loop tactic, so `ENSURES_FINAL_STATE_TAC` discharges the frame itself
         and this branch list has NINE entries, not ten.  (Developing the body
         as a standalone `ensures` with the OPAQUE ABI constant gives ten and
         then fails here with a spurious extra branch.) *)
      MATCH_MP_TAC LOOP4X_CF THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC];

    (* 4. the BACK-EDGE: b.cs @0x2d4, taken because CF holds for i < k *)
    REPEAT STRIP_TAC THEN
    REWRITE_TAC[ghash_v8_loop4x_inv] THEN
    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC GHASH_V8_EXEC [1] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    GEN_REWRITE_TAC ONCE_DEPTH_CONV [GSYM(ASSUME `n = 4 * (k + 1) + r`)] THEN
    FIRST_X_ASSUM MATCH_ACCEPT_TAC;

    (* 5. the EXIT: b.cs @0x2d4 falls through to .Ltail4x @0x2d8 *)
    REWRITE_TAC[LT_REFL; ghash_v8_loop4x_inv] THEN
    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC GHASH_V8_EXEC [1] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    GEN_REWRITE_TAC ONCE_DEPTH_CONV [GSYM(ASSUME `n = 4 * (k + 1) + r`)] THEN
    FIRST_X_ASSUM MATCH_ACCEPT_TAC]);;

(* ========================================================================= *)
(* PHASE 8: `.Ltail4x` + the .Lone/.Ltwo/.Lthree/.Ldone4x cascade.            *)
(*                                                                           *)
(* `.Loop4x` exits at i = k with X3 = word_sub (word (16*n)) (word (128+64*k)) *)
(* and X2 = in_p + 64*(k+1).  `.Ltail4x`'s `adds x3,x3,#0x40` @0x2fc leaves   *)
(* exactly `word (16*r)`, which makes the four-way dispatch arithmetic:       *)
(*                                                                           *)
(*   0x300  b.eq 0x484   16r = 0   -> r = 0, .Ldone4x  (single reduce)        *)
(*   0x304  cmp x3,#0x20                                                     *)
(*   0x308  b.cc 0x430   16r < 32  -> r = 1, .Lone     (staged)               *)
(*   0x30c  b.eq 0x3b0   16r = 32  -> r = 2, .Ltwo     (staged)               *)
(*   fallthru 0x310      16r = 48  -> r = 3, .Lthree   (staged)               *)
(*                                                                           *)
(* Only r = 0 is a single reduce; the other three do the group-k reduce INLINE *)
(* and hand it to `.Ldone4x` as the accumulator for a SECOND reduce over the  *)
(* r remaining blocks (leg A's n = 3 shape).  None of the three tails post-   *)
(* increments x2: they all read from [x2] = in_p + 64*(k+1).                  *)
(* ------------------------------------------------------------------------- *)

(* The r = 0 counter rung.  With n = 4*(k+1) the `adds` restores X3 to exactly
   zero, so the `b.eq` at 0x300 is taken and the whole band is 26 steps:
   9 (`.Ltail4x` head) + 1 (`adds`) + 1 (`b.eq`) + 15 (`.Ldone4x`). *)

let TAIL0_ZERO = prove
 (`!k. word_add (word_sub (word (16 * 4 * (k + 1))) (word (128 + 64 * k)))
                (word 64) : int64 = word 0`,
  GEN_TAC THEN REWRITE_TAC[ARITH_RULE `16 * 4 * (k+1) = 64 * k + 64`;
                           ARITH_RULE `128 + 64 * k = 64 * k + 128`] THEN
  CONV_TAC WORD_RULE);;

(* ------------------------------------------------------------------------- *)
(* Phase 8, r = 0: the `.Ltail4x` -> `.Ldone4x` band, 0x2d8 -> 0x4c0.         *)
(*                                                                           *)
(* This is the FIRST leg-B theorem whose frame contains a memory component:   *)
(* `st1 {v0.2d},[x0]` @0x4bc writes the 16 bytes at xi_p.                     *)
(*                                                                           *)
(* The algebra close is the Phase-7 accumulator close VERBATIM, with the loop *)
(* index specialized to k -- same abbreviations, same `GHASH1_ALIGN` reuse,    *)
(* same MIDSUM4/RESUM4 rotation, same `build_GMULTn_fast 4`.  That is expected:*)
(* `.Ltail4x`+`.Ldone4x` computes exactly what one `.Loop4x` body computes,    *)
(* minus the next group's load and the deferred-sum rebuild.  Measured: the    *)
(* goal shrinks 6106 -> 4283 chars under the abbreviations (Phase 7 saw 4290)  *)
(* and the machine LHS reaches 12319 chars, `aconv`-identical to Phase 7's.    *)
(*                                                                           *)
(* One new rung, `TAIL0_ZERO`: the sim leaves X3 as the un-normalized          *)
(* `word_add (word_sub ...) (word 64)` and the `b.eq` guard reads `val` of it, *)
(* so it must be folded to `word 0` (and `VAL_WORD_0` applied) BEFORE step 11  *)
(* or the branch does not resolve.                                            *)
(* ------------------------------------------------------------------------- *)

let GCM_GHASH_V8_LEGB_TAIL0 = prove
 (`!xi_p htbl_p in_p pc H h xi (blk:num->int128) n k.
     h = ghash_twist H /\
     n = 4 * (k + 1) /\ 16 * n < 2 EXP 64 /\
     nonoverlapping (word pc, LENGTH ghash_v8_mc) (xi_p,16) /\
     nonoverlapping (xi_p,16) (in_p,16 * n) /\
     nonoverlapping (xi_p,16) (htbl_p,96)
     ==> ensures arm
          (\s. read PC s = word (pc + 0x2d8) /\
               ghash_v8_loop4x_inv pc xi_p htbl_p in_p H h xi blk n k s)
          (\s. read PC s = word (pc + 0x4c0) /\
               read (memory :> bytes128 xi_p) s =
               word_bytereverse
                 (nist_ghash H (word_bytereverse xi)
                    (MAP word_bytereverse (list_of_seq blk n))))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(xi_p:int64,16)] ,,
           MAYCHANGE [Q0;Q1;Q2;Q3;Q4;Q5;Q6;Q7;
                      Q16;Q17;Q18;Q19;Q20;Q21;Q22;Q23;Q24;Q25;Q26;Q27;Q28;
                      Q29;Q30;Q31])`,
  REWRITE_TAC[ghash_v8_loop4x_inv; fst GHASH_V8_EXEC;
              NONOVERLAPPING_CLAUSES] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  MAP_EVERY (fun m -> ARM_STEPS_TAC GHASH_V8_EXEC [m] THEN Q128_NORM_TAC)
            (1--10) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[TAIL0_ZERO; VAL_WORD_0]) THEN
  ARM_STEPS_TAC GHASH_V8_EXEC [11] THEN
  MAP_EVERY (fun m -> ARM_STEPS_TAC GHASH_V8_EXEC [m] THEN Q128_NORM_TAC)
            (12--24) THEN
  ABBREV_READ_TAC "accT0" `Q0` THEN
  MAP_EVERY (fun m -> ARM_STEPS_TAC GHASH_V8_EXEC [m] THEN Q128_NORM_TAC)
            (25--26) THEN
  UNABBREV_READ_TAC "accT0" THEN Q128_NORM_TAC THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[ARITH_RULE `4 * (k + 1) = 4 * k + 4`] THEN
    REWRITE_TAC[ghash_acc_rev] THEN
    REWRITE_TAC[LOOP4X_ACC_STEP4] THEN
    ABBREV_TAC `AC:int128 = nist_ghash H (word_bytereverse xi)
                  (MAP word_bytereverse (list_of_seq blk (4 * k)))` THEN
    REWRITE_TAC[REV64_XOR_AS_BSWAP; BYTESWAP128_INVOLUTION] THEN
    ABBREV_TAC `DL:int128 = ghash_defer_lo (ghash_twist H) blk (4 * k)` THEN
    ABBREV_TAC `DH:int128 = ghash_defer_hi (ghash_twist H) blk (4 * k)` THEN
    ABBREV_TAC `DM:int128 = ghash_defer_mid (ghash_twist H) blk (4 * k)` THEN
    GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [REV64_AS_BSWAP_BREV] THEN
    GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV)
                    [BYTEREVERSE128_INVOLUTION] THEN
    AP_TERM_TAC THEN
    REWRITE_TAC[INS128_TO_JOIN; INS_TO_JOIN; INS128_HI_TO_JOIN;
                INS_HI_TO_JOIN; MID_FOLD_BSWAP_LO; MID_FOLD_BSWAP_HI;
                karatsuba_mid] THEN
    REWRITE_TAC[GHASH1_ALIGN] THEN
    MAP_EVERY EXPAND_TAC ["DL"; "DH"; "DM"] THEN
    REWRITE_TAC[ghash_defer_lo; ghash_defer_hi; ghash_defer_mid;
                karatsuba_mid] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
    GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [MIDSUM4] THEN
    GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [RESUM4] THEN
    REWRITE_TAC[snd(build_GMULTn_fast 4)] THEN
    REWRITE_TAC[XOR4_REASSOC_GEN] THEN
    MATCH_MP_TAC GHASH4_SPEC_CHAIN_GEN THEN REFL_TAC;

    REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    REPEAT CONJ_TAC THEN MONOTONE_MAYCHANGE_TAC THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Phase 8, r = 1: the `.Lone` -> `.Ldone4x` band, 0x2d8 -> 0x4c0.            *)
(*                                                                           *)
(* This is the first STAGED tail (leg A's n = 3 shape).  `.Lone` @0x430 does   *)
(* the group-k reduce INLINE at 0x448..0x468, then folds the ONE remaining     *)
(* block 4(k+1) against H and hands it to `.Ldone4x` for a SECOND reduce.      *)
(*                                                                           *)
(* THE STRUCTURAL KEY, and what makes this cheap: at s28 (offset 0x46c, right  *)
(* after `.Lone`'s `ext v0` @0x468) the machine's Q0 is EXACTLY                *)
(* `ghash_acc_rev H xi blk (4*(k+1))` -- the Phase-7 loop-body accumulator at  *)
(* index k+1.  So the stage-1 close is the Phase-7 close VERBATIM, asserted as *)
(* a cut-point SUBGOAL, after which the 6 KB raw byteform is DISCARDED and the *)
(* remaining 21 steps run over a 50-char accumulator.  Without that cut-point  *)
(* the two reduces compose into one term and the stage-2 align never matches.  *)
(*                                                                           *)
(* Stage 2 is then literally leg A's n = 1 close: `GHASH1_ALIGN` +             *)
(* `build_GMULTn_fast 1` + `GHASH1_SPEC_CHAIN_GEN` (the OPAQUE-accumulator     *)
(* form, which is why it applies at a symbolic index), glued to stage 1 by      *)
(* `NIST_GHASH_APPEND` over `list_of_seq`'s rightward append.                  *)
(*                                                                           *)
(* One spelling trap: after the two `ABBREV_TAC`s the goal mentions `4*k+4` on *)
(* one side and `4*(k+1)` on the other, and the abbreviation equation is       *)
(* stated at `4*(k+1)`.  Fold `4*k+4` BACK to `4*(k+1)` (GSYM the ARITH_RULE)  *)
(* before `ASM_REWRITE_TAC`, or the abbreviation does not fire and             *)
(* `MATCH_MP_TAC` reports the opaque `No match` on two terms that differ only  *)
(* in that numeral spelling.                                                   *)
(* ------------------------------------------------------------------------- *)

let TAIL1_X3 = prove
 (`!k. word_add (word_sub (word (16 * (4 * (k + 1) + 1))) (word (128 + 64 * k)))
                (word 64) : int64 = word 16`,
  GEN_TAC THEN
  REWRITE_TAC[ARITH_RULE `16 * (4 * (k+1) + 1) = (64 * k + 64) + 16`;
              ARITH_RULE `128 + 64 * k = 64 * k + 128`] THEN
  CONV_TAC WORD_RULE);;

let GCM_GHASH_V8_LEGB_TAIL1 = prove
 (`!xi_p htbl_p in_p pc H h xi (blk:num->int128) n k.
     h = ghash_twist H /\
     n = 4 * (k + 1) + 1 /\ 16 * n < 2 EXP 64 /\
     nonoverlapping (word pc, LENGTH ghash_v8_mc) (xi_p,16) /\
     nonoverlapping (xi_p,16) (in_p,16 * n) /\
     nonoverlapping (xi_p,16) (htbl_p,96)
     ==> ensures arm
          (\s. read PC s = word (pc + 0x2d8) /\
               ghash_v8_loop4x_inv pc xi_p htbl_p in_p H h xi blk n k s)
          (\s. read PC s = word (pc + 0x4c0) /\
               read (memory :> bytes128 xi_p) s =
               word_bytereverse
                 (nist_ghash H (word_bytereverse xi)
                    (MAP word_bytereverse (list_of_seq blk n))))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(xi_p:int64,16)] ,,
           MAYCHANGE [Q0;Q1;Q2;Q3;Q4;Q5;Q6;Q7;
                      Q16;Q17;Q18;Q19;Q20;Q21;Q22;Q23;Q24;Q25;Q26;Q27;Q28;
                      Q29;Q30;Q31])`,
  REWRITE_TAC[ghash_v8_loop4x_inv; fst GHASH_V8_EXEC;
              NONOVERLAPPING_CLAUSES] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  MAP_EVERY (fun m -> ARM_STEPS_TAC GHASH_V8_EXEC [m] THEN Q128_NORM_TAC)
            (1--10) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[TAIL1_X3]) THEN
  ARM_STEPS_TAC GHASH_V8_EXEC (11--13) THEN
  SUBGOAL_THEN
   `read (memory :> bytes128 (word_add in_p (word (64 * (k+1))))) s13 =
      blk (4*k+4)`
   ASSUME_TAC THENL
   [MP_TAC(SPEC `4*k+4` (ASSUME
       `!j. j < n
            ==> read (memory :> bytes128
                       (word_add in_p (word (16 * j)))) s13 = blk j`)) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE;
    ALL_TAC] THEN
  MAP_EVERY (fun m -> ARM_STEPS_TAC GHASH_V8_EXEC [m] THEN Q128_NORM_TAC)
            (14--28) THEN
  SUBGOAL_THEN `read Q0 s28 = ghash_acc_rev H xi blk (4 * (k+1))`
   ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ghash_acc_rev; ARITH_RULE `4 * (k + 1) = 4 * k + 4`] THEN
    REWRITE_TAC[LOOP4X_ACC_STEP4] THEN
    ABBREV_TAC `AC:int128 = nist_ghash H (word_bytereverse xi)
                  (MAP word_bytereverse (list_of_seq blk (4 * k)))` THEN
    REWRITE_TAC[GSYM REV64_AS_BSWAP_BREV] THEN
    REWRITE_TAC[REV64_XOR_AS_BSWAP; BYTESWAP128_INVOLUTION] THEN
    ABBREV_TAC `DL:int128 = ghash_defer_lo (ghash_twist H) blk (4 * k)` THEN
    ABBREV_TAC `DH:int128 = ghash_defer_hi (ghash_twist H) blk (4 * k)` THEN
    ABBREV_TAC `DM:int128 = ghash_defer_mid (ghash_twist H) blk (4 * k)` THEN
    GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [REV64_AS_BSWAP_BREV] THEN
    GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV)
                    [BYTEREVERSE128_INVOLUTION] THEN
    AP_TERM_TAC THEN
    REWRITE_TAC[INS128_TO_JOIN; INS_TO_JOIN; INS128_HI_TO_JOIN;
                INS_HI_TO_JOIN; MID_FOLD_BSWAP_LO; MID_FOLD_BSWAP_HI;
                karatsuba_mid] THEN
    REWRITE_TAC[GHASH1_ALIGN] THEN
    MAP_EVERY EXPAND_TAC ["DL"; "DH"; "DM"] THEN
    REWRITE_TAC[ghash_defer_lo; ghash_defer_hi; ghash_defer_mid;
                karatsuba_mid] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
    GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [MIDSUM4] THEN
    GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [RESUM4] THEN
    REWRITE_TAC[snd(build_GMULTn_fast 4)] THEN
    REWRITE_TAC[XOR4_REASSOC_GEN] THEN
    MATCH_MP_TAC GHASH4_SPEC_CHAIN_GEN THEN REFL_TAC;
    ALL_TAC] THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
    String.length(string_of_term(concl th)) > 400))) THEN
  MAP_EVERY (fun m -> ARM_STEPS_TAC GHASH_V8_EXEC [m] THEN Q128_NORM_TAC)
            (29--47) THEN
  ABBREV_READ_TAC "accT1" `Q0` THEN
  MAP_EVERY (fun m -> ARM_STEPS_TAC GHASH_V8_EXEC [m] THEN Q128_NORM_TAC)
            (48--49) THEN
  UNABBREV_READ_TAC "accT1" THEN Q128_NORM_TAC THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[ARITH_RULE `4 * (k + 1) + 1 = SUC (4 * (k+1))`] THEN
    REWRITE_TAC[list_of_seq; MAP_APPEND; MAP; NIST_GHASH_APPEND] THEN
    ABBREV_TAC `AC2:int128 = nist_ghash H (word_bytereverse xi)
                  (MAP word_bytereverse (list_of_seq blk (4 * (k+1))))` THEN
    REWRITE_TAC[ghash_acc_rev] THEN
    ABBREV_TAC `A2:int128 = nist_ghash H (word_bytereverse xi)
                  (MAP word_bytereverse (list_of_seq blk (4 * (k+1))))` THEN
    REWRITE_TAC[REV64_XOR_AS_BSWAP; BYTESWAP128_INVOLUTION] THEN
    GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [REV64_AS_BSWAP_BREV] THEN
    GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV)
                    [BYTEREVERSE128_INVOLUTION] THEN
    AP_TERM_TAC THEN
    REWRITE_TAC[INS128_TO_JOIN; INS_TO_JOIN; INS128_HI_TO_JOIN;
                INS_HI_TO_JOIN; MID_FOLD_BSWAP_LO; MID_FOLD_BSWAP_HI;
                karatsuba_mid] THEN
    REWRITE_TAC[GHASH1_ALIGN] THEN
    REWRITE_TAC[snd(build_GMULTn_fast 1)] THEN
    REWRITE_TAC[GSYM(ARITH_RULE `4 * (k + 1) = 4 * k + 4`)] THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC GHASH1_SPEC_CHAIN_GEN THEN REFL_TAC;

    REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    REPEAT CONJ_TAC THEN MONOTONE_MAYCHANGE_TAC THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Phase 8 shared support for the STAGED tails (r = 1,2,3).                   *)
(*                                                                           *)
(* `ACC_CUTPOINT_TAC st` asserts, at state `st`, that the machine's Q0 is      *)
(* EXACTLY `ghash_acc_rev H xi blk (4*(k+1))` -- i.e. that the inline group-k   *)
(* reduce each staged tail performs computes the same thing one `.Loop4x` body *)
(* iteration does.  It is the Phase-7 accumulator close verbatim.  Firing it   *)
(* mid-band and then DISCARDING every >400-char assumption is what keeps the   *)
(* remaining steps cheap: without the cut-point the two reduces compose into   *)
(* one term and the stage-2 align never matches.                              *)
(*                                                                           *)
(* `ACC_STEP2` / `ACC_STEP3` are the 2- and 3-block analogues of              *)
(* `LOOP4X_ACC_STEP4`: they peel r blocks off the spec-side `list_of_seq` fold *)
(* so the residual is a single opaque accumulator.  Stated at `m+r` in terms   *)
(* of `m` so the tail's `r` fresh blocks come out as an explicit r-element     *)
(* list, which is exactly what the r-block spec chain consumes.                *)
(*                                                                           *)
(* `GHASH2_SPEC_CHAIN_GEN` is `GHASH2_SPEC_CHAIN` over an OPAQUE accumulator   *)
(* (the same generalization `GHASH1_SPEC_CHAIN_GEN` is of `GHASH1_SPEC_CHAIN`) *)
(* -- required because a staged tail's stage-2 accumulator is the stage-1      *)
(* reduce output, not `word_bytereverse xi`.                                   *)
(*                                                                           *)
(* `GHASH2_ALIGN_NOFLIP` is `GHASH2_ALIGN` WITHOUT its `l_fix` outer-XOR flip. *)
(* THIS IS A REAL DISTINCTION, not redundancy: leg A's n = 2 band reduces at    *)
(* 0xbc/0xe4 and emits the byteswap summand FIRST, whereas `.Ltwo`'s reduce at  *)
(* 0x40c..0x424 emits it in the n = 1 order.  Measured by the v122 atom-        *)
(* abstraction diff: with the flipped version the abstracted goal and          *)
(* `build_GMULTn_fast 2`'s LHS are both 460 chars and STRUCTURALLY IDENTICAL,   *)
(* yet `term_match` fails -- the flip has to be absent.                        *)
(* ------------------------------------------------------------------------- *)

let ACC_STEP2 = prove
 (`!H xi blk m.
     nist_ghash H (word_bytereverse xi)
       (MAP word_bytereverse (list_of_seq blk (m+2))) =
     nist_ghash H
       (nist_ghash H (word_bytereverse xi)
          (MAP word_bytereverse (list_of_seq blk m)))
       [word_bytereverse (blk m); word_bytereverse (blk (m+1))]`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[ARITH_RULE `m+2 = SUC(SUC m)`; ARITH_RULE `m+1 = SUC m`] THEN
  REWRITE_TAC[list_of_seq; MAP_APPEND; MAP] THEN
  REWRITE_TAC[GSYM APPEND_ASSOC] THEN
  REWRITE_TAC[NIST_GHASH_APPEND] THEN
  REWRITE_TAC[APPEND] THEN
  REWRITE_TAC[NIST_GHASH_CONS; nist_ghash]);;

let ACC_STEP3 = prove
 (`!H xi blk m.
     nist_ghash H (word_bytereverse xi)
       (MAP word_bytereverse (list_of_seq blk (m+3))) =
     nist_ghash H
       (nist_ghash H (word_bytereverse xi)
          (MAP word_bytereverse (list_of_seq blk m)))
       [word_bytereverse (blk m); word_bytereverse (blk (m+1));
        word_bytereverse (blk (m+2))]`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[ARITH_RULE `m+3 = SUC(SUC(SUC m))`; ARITH_RULE `m+1 = SUC m`;
              ARITH_RULE `m+2 = SUC(SUC m)`] THEN
  REWRITE_TAC[list_of_seq; MAP_APPEND; MAP] THEN
  REWRITE_TAC[GSYM APPEND_ASSOC] THEN
  REWRITE_TAC[NIST_GHASH_APPEND] THEN
  REWRITE_TAC[APPEND] THEN
  REWRITE_TAC[NIST_GHASH_CONS; nist_ghash]);;

let GHASH2_SPEC_CHAIN_GEN = prove
 (`!(H:int128) (h:int128) (acc:int128) (blk0:int128) (blk1:int128).
     h = ghash_twist H
     ==> polyval_reduce_prop3
           (word_xor
             (word_pmul (h_power h 0) (word_bytereverse blk1))
             (word_pmul (h_power h 1)
                        (word_xor acc (word_bytereverse blk0)))) =
         nist_ghash H acc [word_bytereverse blk0; word_bytereverse blk1]`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`H:int128`; `h:int128`; `word_bytereverse(acc:int128)`;
                `blk0:int128`; `blk1:int128`] GHASH2_SPEC_CHAIN) THEN
  ASM_REWRITE_TAC[BYTEREVERSE128_INVOLUTION]);;

let GHASH2_ALIGN_NOFLIP =
  let sums = [`word_xor (p2:int128) (p1:int128)`;
              `word_xor (p4:int128) (p3:int128)`;
              `word_xor (p6:int128) (p5:int128)`] in
  let base = SPECL sums GHASH1_ALIGN in
  let r_fix = CONV_RULE (RAND_CONV(TOP_DEPTH_CONV
                (REWR_CONV GHASH2_MID_UNCANON))) base in
  GENL [`p1:int128`;`p2:int128`;`p3:int128`;`p4:int128`;`p5:int128`;`p6:int128`]
       r_fix;;

let ACC_CUTPOINT_TAC st =
  SUBGOAL_THEN (subst [mk_var(st,`:armstate`),`s:armstate`]
                 `read Q0 (s:armstate) = ghash_acc_rev H xi blk (4 * (k+1))`)
   ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ghash_acc_rev; ARITH_RULE `4 * (k + 1) = 4 * k + 4`] THEN
    REWRITE_TAC[LOOP4X_ACC_STEP4] THEN
    ABBREV_TAC `AC:int128 = nist_ghash H (word_bytereverse xi)
                  (MAP word_bytereverse (list_of_seq blk (4 * k)))` THEN
    REWRITE_TAC[GSYM REV64_AS_BSWAP_BREV] THEN
    REWRITE_TAC[REV64_XOR_AS_BSWAP; BYTESWAP128_INVOLUTION] THEN
    ABBREV_TAC `DL:int128 = ghash_defer_lo (ghash_twist H) blk (4 * k)` THEN
    ABBREV_TAC `DH:int128 = ghash_defer_hi (ghash_twist H) blk (4 * k)` THEN
    ABBREV_TAC `DM:int128 = ghash_defer_mid (ghash_twist H) blk (4 * k)` THEN
    GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [REV64_AS_BSWAP_BREV] THEN
    GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV)
                    [BYTEREVERSE128_INVOLUTION] THEN
    AP_TERM_TAC THEN
    REWRITE_TAC[INS128_TO_JOIN; INS_TO_JOIN; INS128_HI_TO_JOIN;
                INS_HI_TO_JOIN; MID_FOLD_BSWAP_LO; MID_FOLD_BSWAP_HI;
                karatsuba_mid] THEN
    REWRITE_TAC[GHASH1_ALIGN] THEN
    MAP_EVERY EXPAND_TAC ["DL"; "DH"; "DM"] THEN
    REWRITE_TAC[ghash_defer_lo; ghash_defer_hi; ghash_defer_mid;
                karatsuba_mid] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
    GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [MIDSUM4] THEN
    GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [RESUM4] THEN
    REWRITE_TAC[snd(build_GMULTn_fast 4)] THEN
    REWRITE_TAC[XOR4_REASSOC_GEN] THEN
    MATCH_MP_TAC GHASH4_SPEC_CHAIN_GEN THEN REFL_TAC;
    ALL_TAC];;

(* Specialize one input block out of the invariant's quantified memory
   predicate.  `off` is the FLAT byte offset from `in_p` (the s157 finding:
   multi-register `ld1` emits its high addresses with the offsets already
   summed, so a nested `word_add (word_add ..) ..` spelling does not match and
   the high registers are silently erased by DISCARD_OLDSTATE_TAC). *)

let SETUP_BLK_TAC st off idx =
  SUBGOAL_THEN
   (subst [mk_var(st,`:armstate`),`s:armstate`; off,`off:num`; idx,`idx:num`]
     `read (memory :> bytes128 (word_add in_p (word off))) (s:armstate) =
        (blk:num->int128) idx`)
   ASSUME_TAC THENL
   [MP_TAC(SPEC idx (ASSUME
       (subst [mk_var(st,`:armstate`),`s:armstate`]
         `!j. j < n
              ==> read (memory :> bytes128
                         (word_add in_p (word (16 * j)))) (s:armstate) =
                  (blk:num->int128) j`))) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE;
    ALL_TAC];;

(* ------------------------------------------------------------------------- *)
(* Phase 8, r = 2: the `.Ltwo` -> `.Ldone4x` band, 0x2d8 -> 0x4c0.            *)
(*                                                                           *)
(* Dispatch: `adds` leaves X3 = word 32, so `b.eq` @0x300 falls through,      *)
(* `cmp x3,#0x20` sets EQ, `b.cc` @0x308 falls through and `b.eq` @0x30c is   *)
(* TAKEN -> `.Ltwo` @0x3b0.  The 2-register `ld1 {v4.2d-v5.2d},[x2]` @0x3bc   *)
(* reads blocks 4k+4 and 4k+5 from `[x2] = in_p + 64*(k+1)` with NO post-     *)
(* increment, so both offsets are supplied FLAT.                              *)
(*                                                                           *)
(* The group-k reduce completes at s31 (offset 0x3f0's `ext v0`), which is    *)
(* the `ACC_CUTPOINT_TAC` site.  Stage 2 is then leg A's n = 2 close with     *)
(* `GHASH2_ALIGN_NOFLIP` (see its comment for why the flip must be absent)     *)
(* and `GHASH2_SPEC_CHAIN_GEN`.  Note `REV64_AS_BSWAP_BREV` MUST be in the    *)
(* ins->join rewrite list here, as leg A's n = 2 band has it: the block-1     *)
(* Karatsuba mid operand arrives as `word_xor (brev b) (rev64_128 b)` and     *)
(* `MID_FOLD_BSWAP_LO` only matches the `byteswap128`-spelled form.  Without  *)
(* it exactly ONE of the eight abstracted atoms differs and                    *)
(* `build_GMULTn_fast 2` silently does not fire.                              *)
(* ------------------------------------------------------------------------- *)

let TAIL2_X3 = prove
 (`!k. word_add (word_sub (word (16 * (4 * (k + 1) + 2))) (word (128 + 64 * k)))
                (word 64) : int64 = word 32`,
  GEN_TAC THEN
  REWRITE_TAC[ARITH_RULE `16 * (4 * (k+1) + 2) = (64 * k + 64) + 32`;
              ARITH_RULE `128 + 64 * k = 64 * k + 128`] THEN
  CONV_TAC WORD_RULE);;

let GCM_GHASH_V8_LEGB_TAIL2 = prove
 (`!xi_p htbl_p in_p pc H h xi (blk:num->int128) n k.
     h = ghash_twist H /\
     n = 4 * (k + 1) + 2 /\ 16 * n < 2 EXP 64 /\
     nonoverlapping (word pc, LENGTH ghash_v8_mc) (xi_p,16) /\
     nonoverlapping (xi_p,16) (in_p,16 * n) /\
     nonoverlapping (xi_p,16) (htbl_p,96)
     ==> ensures arm
          (\s. read PC s = word (pc + 0x2d8) /\
               ghash_v8_loop4x_inv pc xi_p htbl_p in_p H h xi blk n k s)
          (\s. read PC s = word (pc + 0x4c0) /\
               read (memory :> bytes128 xi_p) s =
               word_bytereverse
                 (nist_ghash H (word_bytereverse xi)
                    (MAP word_bytereverse (list_of_seq blk n))))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(xi_p:int64,16)] ,,
           MAYCHANGE [Q0;Q1;Q2;Q3;Q4;Q5;Q6;Q7;
                      Q16;Q17;Q18;Q19;Q20;Q21;Q22;Q23;Q24;Q25;Q26;Q27;Q28;
                      Q29;Q30;Q31])`,
  REWRITE_TAC[ghash_v8_loop4x_inv; fst GHASH_V8_EXEC;
              NONOVERLAPPING_CLAUSES] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  MAP_EVERY (fun m -> ARM_STEPS_TAC GHASH_V8_EXEC [m] THEN Q128_NORM_TAC)
            (1--10) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[TAIL2_X3]) THEN
  ARM_STEPS_TAC GHASH_V8_EXEC (11--13) THEN
  SETUP_BLK_TAC "s13" `64 * (k+1)` `4*k+4` THEN
  SETUP_BLK_TAC "s13" `64 * (k+1) + 16` `4*k+5` THEN
  MAP_EVERY (fun m -> ARM_STEPS_TAC GHASH_V8_EXEC [m] THEN Q128_NORM_TAC)
            (14--31) THEN
  ACC_CUTPOINT_TAC "s31" THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
    String.length(string_of_term(concl th)) > 400))) THEN
  MAP_EVERY (fun m -> ARM_STEPS_TAC GHASH_V8_EXEC [m] THEN Q128_NORM_TAC)
            (32--58) THEN
  ABBREV_READ_TAC "accT2" `Q0` THEN
  MAP_EVERY (fun m -> ARM_STEPS_TAC GHASH_V8_EXEC [m] THEN Q128_NORM_TAC)
            (59--60) THEN
  UNABBREV_READ_TAC "accT2" THEN Q128_NORM_TAC THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[ARITH_RULE `4 * (k + 1) + 2 = (4 * (k+1)) + 2`] THEN
    REWRITE_TAC[ACC_STEP2] THEN
    ABBREV_TAC `A2:int128 = nist_ghash H (word_bytereverse xi)
                  (MAP word_bytereverse (list_of_seq blk (4 * (k+1))))` THEN
    REWRITE_TAC[ghash_acc_rev] THEN
    ABBREV_TAC `A3:int128 = nist_ghash H (word_bytereverse xi)
                  (MAP word_bytereverse (list_of_seq blk (4 * (k+1))))` THEN
    REWRITE_TAC[REV64_XOR_AS_BSWAP; BYTESWAP128_INVOLUTION] THEN
    GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [REV64_AS_BSWAP_BREV] THEN
    GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV)
                    [BYTEREVERSE128_INVOLUTION] THEN
    AP_TERM_TAC THEN
    REWRITE_TAC[INS128_TO_JOIN; INS_TO_JOIN; INS128_HI_TO_JOIN;
                INS_HI_TO_JOIN; REV64_AS_BSWAP_BREV;
                MID_FOLD_BSWAP_LO; MID_FOLD_BSWAP_HI; karatsuba_mid] THEN
    REWRITE_TAC[GHASH2_ALIGN_NOFLIP] THEN
    REWRITE_TAC[snd(build_GMULTn_fast 2)] THEN
    REWRITE_TAC[ARITH_RULE `4 * (k + 1) + 1 = 4 * k + 5`;
                ARITH_RULE `4 * (k + 1) = 4 * k + 4`] THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC GHASH2_SPEC_CHAIN_GEN THEN REFL_TAC;

    REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    REPEAT CONJ_TAC THEN MONOTONE_MAYCHANGE_TAC THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Phase 8, r = 3: the `.Lthree` -> `.Ldone4x` band, 0x2d8 -> 0x4c0.          *)
(*                                                                           *)
(* Dispatch: `adds` leaves X3 = word 48, so all three of `b.eq` @0x300,       *)
(* `b.cc` @0x308 and `b.eq` @0x30c FALL THROUGH to `.Lthree` @0x310.  The     *)
(* 3-register `ld1 {v4.2d-v6.2d},[x2]` @0x31c reads blocks 4k+4, 4k+5, 4k+6   *)
(* from `[x2] = in_p + 64*(k+1)` with no post-increment, so all three offsets *)
(* are supplied FLAT (the s157 trap).                                        *)
(*                                                                           *)
(* The group-k reduce completes at s39 (offset 0x374's `ext v0`), the         *)
(* `ACC_CUTPOINT_TAC` site.  Unlike r = 1 and r = 2, `.Lthree` folds its      *)
(* three blocks against H^2/H/H^0 in ONE `.Ldone4x` reduce, so stage 2 is a   *)
(* single three-block close and `build_GMULTn_fast 3` is the right shape.     *)
(*                                                                           *)
(* THE DISCARD THRESHOLD MUST BE 5000, NOT the 400 that r = 1 / r = 2 use.    *)
(* `.Lthree` carries three fresh blocks, so at `>400` the blanket discard     *)
(* erases a LIVE pre-reduce register fact and step 40 dies `Failure           *)
(* "tryfind"`.  At `>5000` only the 6004-char raw Q0 goes.                    *)
(*                                                                           *)
(* THE ALIGN GAP IS TWO SEPARATE RE-NESTINGS, not one, and the ORDER matters. *)
(* `GHASH1_ALIGN` fires on the machine side with the three summed atoms       *)
(* LEFT-nested exactly as the assembly builds them -- do NOT try to pre-bake  *)
(* right-nested sums into its instantiation.  What differs from               *)
(* `build_GMULTn_fast 3` is then only summand ORDER, in two places:           *)
(*   (a) `MIDSUM3L` (the 3-block analogue of `MIDSUM4`) fixes the mid         *)
(*       accumulator's bracketing;                                           *)
(*   (b) `RESUM3_LO`/`RESUM3_HI` rotate the goal's lo and hi product sums so    *)
(*       the H^2 (accumulator) product comes FIRST, matching the spec -- the    *)
(*       assembly puts it LAST because the deferred H/H^0 products are          *)
(*       computed first and the fresh accumulator product is XORed in after.    *)
(* Measured: 12 differing subterms -> 4 after (a) -> 0 after (b), i.e.        *)
(* `aconv`-IDENTICAL at 9520 chars both sides.  That is the FIFTH time the    *)
(* v123 `aconv`-against-an-existing-align-lemma check has predicted the close *)
(* for free, and no new BITBLAST was needed here either.                      *)
(*                                                                           *)
(* One last shape note: after `build_GMULTn_fast 3` the reduce argument is    *)
(* LEFT-nested (`word_xor (word_xor P2 P1) P0`) while                         *)
(* `GHASH3_SPEC_CHAIN_GEN` states it right-nested, so one                     *)
(* `XOR3_RENEST_GEN` aimed at the LAND's RAND is required before              *)
(* `MATCH_MP_TAC` -- without it `MATCH_MP_TAC` reports an opaque `No match`.  *)
(* `XOR3_RENEST_GEN` must be over `(N)word` for the same reason               *)
(* `XOR4_REASSOC_GEN` is (the s158 finding).                                  *)
(* ------------------------------------------------------------------------- *)

let TAIL3_X3 = prove
 (`!k. word_add (word_sub (word (16 * (4 * (k + 1) + 3))) (word (128 + 64 * k)))
                (word 64) : int64 = word 48`,
  GEN_TAC THEN
  REWRITE_TAC[ARITH_RULE `16 * (4 * (k+1) + 3) = (64 * k + 64) + 48`;
              ARITH_RULE `128 + 64 * k = 64 * k + 128`] THEN
  CONV_TAC WORD_RULE);;

(* `GHASH3_SPEC_CHAIN` (above) states the STAGED two-reduce form and is the
   wrong shape for `.Lthree`, which reduces once over three blocks.  This is
   the `GHASH4_SPEC_CHAIN_GEN` mould at three blocks, over an OPAQUE `acc`.
   `WORD_PMUL_SYM` is aimed at the RAND as at four blocks (NOT the LAND as
   `GHASH2_SPEC_CHAIN` does), and at three blocks one extra explicit
   commutation of the H^2 power is needed because `polyval_dot` associates the
   two squarings the other way round. *)

let GHASH3_SPEC_CHAIN_GEN = prove
 (`!(H:int128) (h:int128) (acc:int128) b0 b1 b2.
     h = ghash_twist H
     ==> polyval_reduce_prop3
           (word_xor
             (word_pmul (h_power h 2)
                        (word_xor acc (word_bytereverse b0)))
             (word_xor
               (word_pmul (h_power h 1) (word_bytereverse b1))
               (word_pmul (h_power h 0) (word_bytereverse b2)))) =
         nist_ghash H acc [word_bytereverse b0; word_bytereverse b1;
                           word_bytereverse b2]`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[NIST_GHASH_IS_POLYVAL] THEN
  ASM_REWRITE_TAC[GHASH_POLYVAL_ACC_3] THEN
  REWRITE_TAC[h_power; ARITH_RULE `1 = SUC 0`; ARITH_RULE `2 = SUC(SUC 0)`;
              polyval_dot] THEN
  REWRITE_TAC[h_power] THEN
  GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [WORD_PMUL_SYM] THEN
  SUBGOAL_THEN
   `polyval_reduce_prop3
      (word_pmul
        (polyval_reduce_prop3 (word_pmul (ghash_twist H) (ghash_twist H)))
        (ghash_twist H)) =
    polyval_reduce_prop3
      (word_pmul (ghash_twist H)
        (polyval_reduce_prop3 (word_pmul (ghash_twist H) (ghash_twist H))))`
   SUBST1_TAC THENL
   [AP_TERM_TAC THEN MATCH_ACCEPT_TAC WORD_PMUL_SYM; ALL_TAC] THEN
  REFL_TAC);;

(* The 3-block analogue of `MIDSUM4`: the machine's mid accumulator XORs the
   two DEFERRED per-block mid partials first and the fresh accumulator mid
   partial last, where the spec brackets them per-block. Pure XOR-ACI. *)

let MIDSUM3L = prove
 (`!m0 m1 m2 l0 l1 l2 h0 h1 h2:int128.
     word_xor (word_xor (word_xor (word_xor m1 m2) m0)
                        (word_xor (word_xor l1 l2) l0))
              (word_xor (word_xor h1 h2) h0) =
     word_xor (word_xor (word_xor m0 l0) h0)
       (word_xor (word_xor (word_xor m1 l1) h1)
                 (word_xor (word_xor m2 l2) h2))`,
  REPEAT GEN_TAC THEN CONV_TAC WORD_RULE);;

(* The accumulator-last rotation of the lo and hi product sums, aimed at the
   GOAL's two sum sites.

   THE PATTERN MUST BE PINNED DOWN TO THE `word_subword` OPERANDS, and the lo
   and hi cases must be SEPARATE lemmas with their lane offsets baked in.  Every
   looser formulation over-fires and was measured to do so:
     - a bare `!a b c:(N)word. word_xor (word_xor a b) c = ...` under
       `TOP_DEPTH_CONV` re-nests the deep Karatsuba mid sums too (s159: diff
       9657 -> 10054 chars, the align stops matching entirely);
     - restricting to `word_pmul` operands is still too loose -- the mid sums
       are `word_pmul (karatsuba_mid ...) (word_subword ...)` applications and
       match as well;
     - pre-baking the rotation into `build_GMULTn_fast 3`'s LHS instead of the
       goal has the identical problem from the other side (LHS 5258 -> 5181
       chars, three extra sites).
   Requiring BOTH operands of every product to be `word_subword _ (o,64)` at a
   FIXED `o` is what finally isolates exactly the two sites: the mid sums'
   H-side operand is a `karatsuba_mid`, not a `word_subword`, and their two lane
   offsets are mixed.  A single lemma with `o` as a variable does not parse in
   the `word_subword` index position, hence the pair. *)

let RESUM3_LO = prove
 (`!(a2:int128) (x2:int128) (a1:int128) (x1:int128) (a0:int128) (x0:int128).
     word_xor
       (word_xor (word_pmul (word_subword a1 (0,64):int64)
                            (word_subword x1 (0,64):int64) :int128)
                 (word_pmul (word_subword a0 (0,64):int64)
                            (word_subword x0 (0,64):int64) :int128))
       (word_pmul (word_subword a2 (0,64):int64)
                  (word_subword x2 (0,64):int64) :int128) =
     word_xor
       (word_pmul (word_subword a2 (0,64):int64)
                  (word_subword x2 (0,64):int64) :int128)
       (word_xor (word_pmul (word_subword a1 (0,64):int64)
                            (word_subword x1 (0,64):int64) :int128)
                 (word_pmul (word_subword a0 (0,64):int64)
                            (word_subword x0 (0,64):int64) :int128))`,
  REPEAT GEN_TAC THEN CONV_TAC WORD_RULE);;

let RESUM3_HI = prove
 (`!(a2:int128) (x2:int128) (a1:int128) (x1:int128) (a0:int128) (x0:int128).
     word_xor
       (word_xor (word_pmul (word_subword a1 (64,64):int64)
                            (word_subword x1 (64,64):int64) :int128)
                 (word_pmul (word_subword a0 (64,64):int64)
                            (word_subword x0 (64,64):int64) :int128))
       (word_pmul (word_subword a2 (64,64):int64)
                  (word_subword x2 (64,64):int64) :int128) =
     word_xor
       (word_pmul (word_subword a2 (64,64):int64)
                  (word_subword x2 (64,64):int64) :int128)
       (word_xor (word_pmul (word_subword a1 (64,64):int64)
                            (word_subword x1 (64,64):int64) :int128)
                 (word_pmul (word_subword a0 (64,64):int64)
                            (word_subword x0 (64,64):int64) :int128))`,
  REPEAT GEN_TAC THEN CONV_TAC WORD_RULE);;

let XOR3_RENEST_GEN = prove
 (`!a b c:(N)word. word_xor (word_xor a b) c = word_xor a (word_xor b c)`,
  REPEAT GEN_TAC THEN CONV_TAC WORD_RULE);;

let GCM_GHASH_V8_LEGB_TAIL3 = prove
 (`!xi_p htbl_p in_p pc H h xi (blk:num->int128) n k.
     h = ghash_twist H /\
     n = 4 * (k + 1) + 3 /\ 16 * n < 2 EXP 64 /\
     nonoverlapping (word pc, LENGTH ghash_v8_mc) (xi_p,16) /\
     nonoverlapping (xi_p,16) (in_p,16 * n) /\
     nonoverlapping (xi_p,16) (htbl_p,96)
     ==> ensures arm
          (\s. read PC s = word (pc + 0x2d8) /\
               ghash_v8_loop4x_inv pc xi_p htbl_p in_p H h xi blk n k s)
          (\s. read PC s = word (pc + 0x4c0) /\
               read (memory :> bytes128 xi_p) s =
               word_bytereverse
                 (nist_ghash H (word_bytereverse xi)
                    (MAP word_bytereverse (list_of_seq blk n))))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(xi_p:int64,16)] ,,
           MAYCHANGE [Q0;Q1;Q2;Q3;Q4;Q5;Q6;Q7;
                      Q16;Q17;Q18;Q19;Q20;Q21;Q22;Q23;Q24;Q25;Q26;Q27;Q28;
                      Q29;Q30;Q31])`,
  REWRITE_TAC[ghash_v8_loop4x_inv; fst GHASH_V8_EXEC;
              NONOVERLAPPING_CLAUSES] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  MAP_EVERY (fun m -> ARM_STEPS_TAC GHASH_V8_EXEC [m] THEN Q128_NORM_TAC)
            (1--10) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[TAIL3_X3]) THEN
  ARM_STEPS_TAC GHASH_V8_EXEC (11--13) THEN
  SETUP_BLK_TAC "s13" `64 * (k+1)` `4*k+4` THEN
  SETUP_BLK_TAC "s13" `64 * (k+1) + 16` `4*k+5` THEN
  SETUP_BLK_TAC "s13" `64 * (k+1) + 32` `4*k+6` THEN
  MAP_EVERY (fun m -> ARM_STEPS_TAC GHASH_V8_EXEC [m] THEN Q128_NORM_TAC)
            (14--39) THEN
  ACC_CUTPOINT_TAC "s39" THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
    String.length(string_of_term(concl th)) > 5000))) THEN
  MAP_EVERY (fun m -> ARM_STEPS_TAC GHASH_V8_EXEC [m] THEN Q128_NORM_TAC)
            (40--67) THEN
  ABBREV_READ_TAC "accT3" `Q0` THEN
  MAP_EVERY (fun m -> ARM_STEPS_TAC GHASH_V8_EXEC [m] THEN Q128_NORM_TAC)
            (68--69) THEN
  UNABBREV_READ_TAC "accT3" THEN Q128_NORM_TAC THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[ARITH_RULE `4 * (k + 1) + 3 = (4 * (k+1)) + 3`] THEN
    REWRITE_TAC[ACC_STEP3] THEN
    ABBREV_TAC `A2:int128 = nist_ghash H (word_bytereverse xi)
                  (MAP word_bytereverse (list_of_seq blk (4 * (k+1))))` THEN
    REWRITE_TAC[ghash_acc_rev] THEN
    ABBREV_TAC `A3:int128 = nist_ghash H (word_bytereverse xi)
                  (MAP word_bytereverse (list_of_seq blk (4 * (k+1))))` THEN
    REWRITE_TAC[REV64_XOR_AS_BSWAP; BYTESWAP128_INVOLUTION] THEN
    GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [REV64_AS_BSWAP_BREV] THEN
    GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV)
                    [BYTEREVERSE128_INVOLUTION] THEN
    AP_TERM_TAC THEN
    REWRITE_TAC[INS128_TO_JOIN; INS_TO_JOIN; INS128_HI_TO_JOIN;
                INS_HI_TO_JOIN; REV64_AS_BSWAP_BREV;
                MID_FOLD_BSWAP_LO; MID_FOLD_BSWAP_HI; karatsuba_mid] THEN
    REWRITE_TAC[GHASH1_ALIGN] THEN
    GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [MIDSUM3L] THEN
    GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [RESUM3_LO; RESUM3_HI] THEN
    REWRITE_TAC[snd(build_GMULTn_fast 3)] THEN
    REWRITE_TAC[ARITH_RULE `4 * (k + 1) + 1 = 4 * k + 5`;
                ARITH_RULE `4 * (k + 1) + 2 = 4 * k + 6`;
                ARITH_RULE `4 * (k + 1) = 4 * k + 4`] THEN
    ASM_REWRITE_TAC[] THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o ONCE_DEPTH_CONV)
                    [XOR3_RENEST_GEN] THEN
    MATCH_MP_TAC GHASH3_SPEC_CHAIN_GEN THEN REFL_TAC;

    REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    REPEAT CONJ_TAC THEN MONOTONE_MAYCHANGE_TAC THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Phase 8, unification: one tail theorem for every r < 4.                    *)
(*                                                                           *)
(* Far cheaper than leg A's `LEGA_CASE_TAC`: the tails' precondition is the   *)
(* uniform `ghash_v8_loop4x_inv`, not an INDEXED memory predicate, so there   *)
(* is no `!i. i < k ==> P i` to expand and hence none of leg A's left-nested  *)
(* CONJ re-bracketing.  Each band matches by `MATCH_MP_TAC` directly.         *)
(*                                                                           *)
(* The one residue is r = 0, where `n = 4*(k+1) + 0` must be reconciled with  *)
(* `GCM_GHASH_V8_LEGB_TAIL0`'s `n = 4*(k+1)`: HOL does not reduce `+ 0`       *)
(* automatically here, so a trailing `ARITH_TAC` is required.  It is a no-op  *)
(* on the other three branches, which `ASM_REWRITE_TAC` has already closed.   *)
(* ------------------------------------------------------------------------- *)

let GCM_GHASH_V8_LEGB_TAIL = prove
 (`!xi_p htbl_p in_p pc H h xi (blk:num->int128) n k r.
     h = ghash_twist H /\
     n = 4 * (k + 1) + r /\ r < 4 /\ 16 * n < 2 EXP 64 /\
     nonoverlapping (word pc, LENGTH ghash_v8_mc) (xi_p,16) /\
     nonoverlapping (xi_p,16) (in_p,16 * n) /\
     nonoverlapping (xi_p,16) (htbl_p,96)
     ==> ensures arm
          (\s. read PC s = word (pc + 0x2d8) /\
               ghash_v8_loop4x_inv pc xi_p htbl_p in_p H h xi blk n k s)
          (\s. read PC s = word (pc + 0x4c0) /\
               read (memory :> bytes128 xi_p) s =
               word_bytereverse
                 (nist_ghash H (word_bytereverse xi)
                    (MAP word_bytereverse (list_of_seq blk n))))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(xi_p:int64,16)] ,,
           MAYCHANGE [Q0;Q1;Q2;Q3;Q4;Q5;Q6;Q7;
                      Q16;Q17;Q18;Q19;Q20;Q21;Q22;Q23;Q24;Q25;Q26;Q27;Q28;
                      Q29;Q30;Q31])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `r = 0 \/ r = 1 \/ r = 2 \/ r = 3` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC;
    MATCH_MP_TAC GCM_GHASH_V8_LEGB_TAIL0;
    MATCH_MP_TAC GCM_GHASH_V8_LEGB_TAIL1;
    MATCH_MP_TAC GCM_GHASH_V8_LEGB_TAIL2;
    MATCH_MP_TAC GCM_GHASH_V8_LEGB_TAIL3] THEN
  ASM_REWRITE_TAC[] THEN ARITH_TAC);;

(* ========================================================================= *)
(* PHASE 9: recompose leg B.  ENTRY ; LOOP4X ; TAIL  ->  GCM_GHASH_V8_LEGB    *)
(* for every len = 16*n with n >= 4.                                          *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* The k = 0 sibling entry: 0x170 -> 0x2d8 directly.                          *)
(*                                                                           *)
(* `GCM_GHASH_V8_LEGB_ENTRY` cannot cover k = 0.  At k = 0 the length         *)
(* `16*n = 16*(4+r)` is 64/80/96/112, all STRICTLY LESS than 128, so the      *)
(* `subs x3,x3,#0x80` at 0x200 leaves CF CLEAR and the `b.cc 0x2d8` at 0x204  *)
(* IS TAKEN -- control never reaches 0x210.  ENTRY's postcondition is         *)
(* `PC = pc + 0x210` and it assumes `1 <= k`, so it simply does not apply.    *)
(*                                                                           *)
(* Structurally this IS `GCM_GHASH_V8_LEGB_ENTRY` with the 0x204 guard        *)
(* resolved the OTHER way and with the `b 0x210` at 0x208 never executed:     *)
(* 38 steps instead of 39, and the two guard-folding facts become             *)
(* `16 * (4 + r) < 128` (positively) rather than its negation.  Everything    *)
(* else -- the four-block memory specialization, the 33 Q128_NORM_TAC steps,  *)
(* the `nist_ghash`-nil degeneration of the Q0 clause at i = 0, and the       *)
(* karatsuba_mid folds on Q30 -- is verbatim ENTRY.  38 steps, ~24 s.         *)
(*                                                                           *)
(* Note the postcondition is the SAME `ghash_v8_loop4x_inv ... n 0`, and      *)
(* `..._LEGB_TAIL`'s precondition is the invariant at index k -- which at     *)
(* k = 0 is exactly this.  So the k = 0 leg comes through the identical       *)
(* `.Ltail4x` seam with no adapter.                                           *)
(* ------------------------------------------------------------------------- *)

let GCM_GHASH_V8_LEGB_ENTRY0 = prove
 (`!xi_p htbl_p in_p pc H h xi (blk:num->int128) n r.
     h = ghash_twist H /\
     n = 4 + r /\ r < 4 /\ 16 * n < 2 EXP 64 /\
     nonoverlapping (word pc, LENGTH ghash_v8_mc) (xi_p,16) /\
     nonoverlapping (xi_p,16) (in_p,16 * n) /\
     nonoverlapping (xi_p,16) (htbl_p,96)
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) ghash_v8_mc /\
               read PC s = word (pc + 0x170) /\
               read X0 s = xi_p /\ read X1 s = htbl_p /\ read X2 s = in_p /\
               read X3 s = word (16 * n) /\
               read (memory :> bytes128 xi_p) s = xi /\
               (!j. j < n
                    ==> read (memory :> bytes128
                               (word_add in_p (word (16 * j)))) s = blk j) /\
               htable_mem_4 h htbl_p s)
          (\s. read PC s = word (pc + 0x2d8) /\
               ghash_v8_loop4x_inv pc xi_p htbl_p in_p H h xi blk n 0 s)
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [Q0;Q1;Q2;Q3;Q4;Q5;Q6;Q7;
                      Q16;Q17;Q18;Q19;Q20;Q21;Q22;Q23;Q24;Q25;Q26;Q27;Q28;
                      Q29;Q30;Q31])`,
  REWRITE_TAC[ghash_v8_loop4x_inv; ghash_acc_rev;
              ghash_defer_lo; ghash_defer_hi; ghash_defer_mid] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
  REWRITE_TAC[list_of_seq; MAP; nist_ghash; BYTEREVERSE128_INVOLUTION] THEN
  REWRITE_TAC[htable_mem_4; fst GHASH_V8_EXEC; NONOVERLAPPING_CLAUSES] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `16 * n < 128` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ENSURES_INIT_TAC "s0" THEN
  SUBGOAL_THEN
   `!j. j < 4
        ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s0 =
            blk j`
   (fun th -> MP_TAC(CONV_RULE (EXPAND_CASES_CONV THENC
                                ONCE_DEPTH_CONV NUM_MULT_CONV) th)) THENL
   [REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    REWRITE_TAC[WORD_ADD_0] THEN STRIP_TAC] THEN
  ARM_STEPS_TAC GHASH_V8_EXEC (1--3) THEN
  MAP_EVERY (fun m -> ARM_STEPS_TAC GHASH_V8_EXEC [m] THEN Q128_NORM_TAC)
            (4--36) THEN
  ARM_STEPS_TAC GHASH_V8_EXEC (37--38) THEN
  SUBGOAL_THEN `val (word (16 * (4 + r)):int64) = 16 * (4 + r)`
   ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `16 * (4 + r) < 128` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [ASSUME `val (word (16 * (4 + r)):int64) = 16 * (4 + r)`;
    ASSUME `16 * (4 + r) < 128`]) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [GEN_REWRITE_TAC ONCE_DEPTH_CONV [GSYM(ASSUME `n = 4 + r`)] THEN
    FIRST_X_ASSUM MATCH_ACCEPT_TAC;
    REWRITE_TAC[REV64_AS_BSWAP_BREV; MID_FOLD_BSWAP_LO; MID_FOLD_BSWAP_HI;
                GSYM karatsuba_mid] THEN REFL_TAC;
    REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    REPEAT CONJ_TAC THEN MONOTONE_MAYCHANGE_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Leg B, whole: 0x170 -> `ret` at 0x4c0, for every n >= 4.                    *)
(*                                                                           *)
(* `LEGB_RUNG` supplies the k/r decomposition (n = 4*(k+1) + r, r < 4) and    *)
(* the composition then glues in TWO pieces at the 0x2d8 seam:                 *)
(*                                                                           *)
(*   0x170 -> 0x2d8   establishing `ghash_v8_loop4x_inv ... n k`               *)
(*                     k = 0 : GCM_GHASH_V8_LEGB_ENTRY0 (the `b.cc` taken)     *)
(*                     k >= 1: GCM_GHASH_V8_LEGB_LOOP4X (entry + the loop)     *)
(*   0x2d8 -> 0x4c0   GCM_GHASH_V8_LEGB_TAIL (the four-way `.Ltail4x` cascade) *)
(*                                                                           *)
(* The seam needs NO adapter lemma in either leg: `LOOP4X`'s postcondition is  *)
(* LITERALLY `..._TAIL`'s precondition, `ENTRY0` was stated to the identical   *)
(* shape at index 0, `aligned_bytes_loaded` rides inside the invariant's first *)
(* conjunct, and `..._TAIL` does NOT assume `1 <= k`.                          *)
(*                                                                           *)
(* FRAME: the two 0x170->0x2d8 theorems carry regs+flags+Q0..Q31 with NO       *)
(* memory component (they write no memory), while `..._TAIL` additionally      *)
(* carries `MAYCHANGE [memory :> bytes(xi_p,16)]` (the `st1` at 0x4bc).  So    *)
(* the `ENSURES_FRAME_SUBSUMED` witness is the ASYMMETRIC pair                 *)
(* `<regs+Q> ,, <regs+mem+Q>`, not the usual doubled `F ,, F`.                 *)
(* `SUBSUMED_MAYCHANGE_TAC` discharges it in ~9 s after the ABI constant is    *)
(* rewritten away (it is opaque to the subsumption machinery, exactly as at    *)
(* `MAYCHANGE_IDEMPOT_TAC` -- see the note at the `.Loop4x` skeleton).         *)
(*                                                                           *)
(* SPELLING TRAP: `MATCH_MP_TAC` against `..._LOOP4X`/`..._TAIL`/`..._ENTRY0`  *)
(* leaves ONLY `r` existentially quantified, not `k` -- `k` is pinned by the   *)
(* invariant in the postcondition, so `MAP_EVERY EXISTS_TAC [k; r]` raises     *)
(* `EXISTS_TAC: Goal not existentially quantified` on the second.  One         *)
(* `EXISTS_TAC \`r:num\`` is what is wanted.                                    *)
(* ------------------------------------------------------------------------- *)

let GCM_GHASH_V8_LEGB = prove
 (`!xi_p htbl_p in_p pc H h xi (blk:num->int128) n.
     h = ghash_twist H /\ 4 <= n /\ 16 * n < 2 EXP 64 /\
     nonoverlapping (word pc, LENGTH ghash_v8_mc) (xi_p,16) /\
     nonoverlapping (xi_p,16) (in_p,16 * n) /\
     nonoverlapping (xi_p,16) (htbl_p,96)
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) ghash_v8_mc /\
               read PC s = word (pc + 0x170) /\
               read X0 s = xi_p /\ read X1 s = htbl_p /\ read X2 s = in_p /\
               read X3 s = word (16 * n) /\
               read (memory :> bytes128 xi_p) s = xi /\
               (!j. j < n
                    ==> read (memory :> bytes128
                               (word_add in_p (word (16 * j)))) s = blk j) /\
               htable_mem_4 h htbl_p s)
          (\s. read PC s = word (pc + 0x4c0) /\
               read (memory :> bytes128 xi_p) s =
               word_bytereverse
                 (nist_ghash H (word_bytereverse xi)
                    (MAP word_bytereverse (list_of_seq blk n))))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(xi_p:int64,16)] ,,
           MAYCHANGE [Q0;Q1;Q2;Q3;Q4;Q5;Q6;Q7;
                      Q16;Q17;Q18;Q19;Q20;Q21;Q22;Q23;Q24;Q25;Q26;Q27;Q28;
                      Q29;Q30;Q31])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(MATCH_MP LEGB_RUNG (ASSUME `4 <= n`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `r:num` STRIP_ASSUME_TAC)) THEN
  MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN
  EXISTS_TAC
   `(MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
     MAYCHANGE [Q0;Q1;Q2;Q3;Q4;Q5;Q6;Q7;
                Q16;Q17;Q18;Q19;Q20;Q21;Q22;Q23;Q24;Q25;Q26;Q27;Q28;
                Q29;Q30;Q31]) ,,
    (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
     MAYCHANGE [memory :> bytes(xi_p:int64,16)] ,,
     MAYCHANGE [Q0;Q1;Q2;Q3;Q4;Q5;Q6;Q7;
                Q16;Q17;Q18;Q19;Q20;Q21;Q22;Q23;Q24;Q25;Q26;Q27;Q28;
                Q29;Q30;Q31])` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    SUBSUMED_MAYCHANGE_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC ENSURES_TRANS THEN
  EXISTS_TAC
   `\s. read PC s = word (pc + 0x2d8) /\
        ghash_v8_loop4x_inv pc xi_p htbl_p in_p H h xi blk n k s` THEN
  CONJ_TAC THENL
   [ASM_CASES_TAC `k = 0` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN
      MATCH_MP_TAC GCM_GHASH_V8_LEGB_ENTRY0 THEN
      EXISTS_TAC `r:num` THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      MATCH_MP_TAC GCM_GHASH_V8_LEGB_LOOP4X THEN
      EXISTS_TAC `r:num` THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC];
    MATCH_MP_TAC GCM_GHASH_V8_LEGB_TAIL THEN
    EXISTS_TAC `r:num` THEN ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* PHASE 10: unify both legs.  One GCM_GHASH_V8_CORRECT for every n >= 1.      *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* The leg-B front prefix: the two dispatch instructions at 0x000/0x004.      *)
(*                                                                           *)
(*   0x000  cmp   x3, #0x40                                                   *)
(*   0x004  b.cs  0x170        TAKEN for 16*n >= 64, i.e. n >= 4              *)
(*                                                                           *)
(* Two steps, ~4 s.  The `cmp` writes only flags, so every input fact passes  *)
(* through untouched and the postcondition is the precondition of             *)
(* `GCM_GHASH_V8_LEGB` verbatim (X0..X3 spelled out rather than as            *)
(* `C_ARGUMENTS`, which is the same thing after the rewrite).                 *)
(*                                                                           *)
(* The guard folds exactly as in `..._LEGB_ENTRY0`: the stepper emits          *)
(* `read CF s1 <=> 64 <= val (word (16 * n))`, and `VAL_WORD_EQ` under         *)
(* `16 * n < 2 EXP 64` plus `64 <= 16 * n` (from `4 <= n`) collapses it        *)
(* before step 2 decodes.                                                     *)
(*                                                                           *)
(* `H` is deliberately absent from the statement: nothing in this band touches *)
(* the accumulator, so quantifying over it would only leave the composition    *)
(* with a spurious `?H'. ghash_twist H = ghash_twist H'` obligation.           *)
(* ------------------------------------------------------------------------- *)

let GCM_GHASH_V8_LEGB_FRONT = prove
 (`!xi_p htbl_p in_p pc h xi (blk:num->int128) n.
     4 <= n /\ 16 * n < 2 EXP 64 /\
     nonoverlapping (word pc, LENGTH ghash_v8_mc) (xi_p,16) /\
     nonoverlapping (xi_p,16) (in_p,16 * n) /\
     nonoverlapping (xi_p,16) (htbl_p,96)
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) ghash_v8_mc /\
               read PC s = word pc /\
               C_ARGUMENTS [xi_p; htbl_p; in_p; word (16 * n)] s /\
               read (memory :> bytes128 xi_p) s = xi /\
               (!j. j < n
                    ==> read (memory :> bytes128
                               (word_add in_p (word (16 * j)))) s = blk j) /\
               htable_mem_4 h htbl_p s)
          (\s. aligned_bytes_loaded s (word pc) ghash_v8_mc /\
               read PC s = word (pc + 0x170) /\
               read X0 s = xi_p /\ read X1 s = htbl_p /\ read X2 s = in_p /\
               read X3 s = word (16 * n) /\
               read (memory :> bytes128 xi_p) s = xi /\
               (!j. j < n
                    ==> read (memory :> bytes128
                               (word_add in_p (word (16 * j)))) s = blk j) /\
               htable_mem_4 h htbl_p s)
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [Q0;Q1;Q2;Q3;Q4;Q5;Q6;Q7;
                      Q16;Q17;Q18;Q19;Q20;Q21;Q22;Q23;Q24;Q25;Q26;Q27;Q28;
                      Q29;Q30;Q31])`,
  REWRITE_TAC[C_ARGUMENTS; htable_mem_4; fst GHASH_V8_EXEC;
              NONOVERLAPPING_CLAUSES] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `64 <= 16 * n` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC GHASH_V8_EXEC [1] THEN
  SUBGOAL_THEN `val (word (16 * n):int64) = 16 * n` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `val (word (16 * n):int64) = 16 * n`;
                             ASSUME `64 <= 16 * n`]) THEN
  ARM_STEPS_TAC GHASH_V8_EXEC [2] THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REPEAT CONJ_TAC THEN MONOTONE_MAYCHANGE_TAC);;

(* Leg B from the function ENTRY: FRONT ; LEGB, same asymmetric frame witness
   as Phase 9 (FRONT writes no memory).  Exits at the leg-B `ret`, 0x4c0. *)

let GCM_GHASH_V8_LEGB_FULL = prove
 (`!xi_p htbl_p in_p pc H h xi (blk:num->int128) n.
     h = ghash_twist H /\ 4 <= n /\ 16 * n < 2 EXP 64 /\
     nonoverlapping (word pc, LENGTH ghash_v8_mc) (xi_p,16) /\
     nonoverlapping (xi_p,16) (in_p,16 * n) /\
     nonoverlapping (xi_p,16) (htbl_p,96)
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) ghash_v8_mc /\
               read PC s = word pc /\
               C_ARGUMENTS [xi_p; htbl_p; in_p; word (16 * n)] s /\
               read (memory :> bytes128 xi_p) s = xi /\
               (!j. j < n
                    ==> read (memory :> bytes128
                               (word_add in_p (word (16 * j)))) s = blk j) /\
               htable_mem_4 h htbl_p s)
          (\s. read PC s = word (pc + 0x4c0) /\
               read (memory :> bytes128 xi_p) s =
               word_bytereverse
                 (nist_ghash H (word_bytereverse xi)
                    (MAP word_bytereverse (list_of_seq blk n))))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(xi_p:int64,16)] ,,
           MAYCHANGE [Q0;Q1;Q2;Q3;Q4;Q5;Q6;Q7;
                      Q16;Q17;Q18;Q19;Q20;Q21;Q22;Q23;Q24;Q25;Q26;Q27;Q28;
                      Q29;Q30;Q31])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN
  EXISTS_TAC
   `(MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
     MAYCHANGE [Q0;Q1;Q2;Q3;Q4;Q5;Q6;Q7;
                Q16;Q17;Q18;Q19;Q20;Q21;Q22;Q23;Q24;Q25;Q26;Q27;Q28;
                Q29;Q30;Q31]) ,,
    (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
     MAYCHANGE [memory :> bytes(xi_p:int64,16)] ,,
     MAYCHANGE [Q0;Q1;Q2;Q3;Q4;Q5;Q6;Q7;
                Q16;Q17;Q18;Q19;Q20;Q21;Q22;Q23;Q24;Q25;Q26;Q27;Q28;
                Q29;Q30;Q31])` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    SUBSUMED_MAYCHANGE_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC ENSURES_TRANS THEN
  EXISTS_TAC
   `\s. aligned_bytes_loaded s (word pc) ghash_v8_mc /\
        read PC s = word (pc + 0x170) /\
        read X0 s = xi_p /\ read X1 s = htbl_p /\ read X2 s = in_p /\
        read X3 s = word (16 * n) /\
        read (memory :> bytes128 xi_p) s = xi /\
        (!j. j < n
             ==> read (memory :> bytes128
                        (word_add in_p (word (16 * j)))) s = blk j) /\
        htable_mem_4 h htbl_p s` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC GCM_GHASH_V8_LEGB_FRONT THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC GCM_GHASH_V8_LEGB THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Leg A, transported from the 368-byte SLICE to the full 1220-byte object.    *)
(*                                                                           *)
(* All of leg A is stated against `ghash_v8_lega_mc = SUB_LIST (0,368)         *)
(* ghash_v8_mc` (the slice existed because `ARM_MK_EXEC_RULE` used to raise on *)
(* the full byte list -- see the header note).  The transport is a pure        *)
(* PRECONDITION WEAKENING, no simulation: the second conjunct of               *)
(* `ALIGNED_BYTES_LOADED_SUB_LIST` (arm/proofs/instruction.ml) gives            *)
(* `aligned_bytes_loaded s pc l ==> aligned_bytes_loaded s pc (SUB_LIST(0,n) l)`*)
(* at the SAME base address, so no `4 divides m` side condition arises.        *)
(*                                                                           *)
(* The only other obligation is `nonoverlapping (word pc, LENGTH              *)
(* ghash_v8_lega_mc)` from `nonoverlapping (word pc, LENGTH ghash_v8_mc)`,     *)
(* i.e. 368 from 1220.  `NONOVERLAPPING_TAC` does NOT do this (it raises       *)
(* `tryfind` -- it is for concrete disjointness, not for shrinking a region);  *)
(* what works is expanding `nonoverlapping_modulo` and one                     *)
(* `MESON_TAC[ARITH_RULE \`!i. i < 368 ==> i < 1220\`]`.                        *)
(* ------------------------------------------------------------------------- *)

let GHASH_V8_LEGA_LENGTH = prove
 (`LENGTH ghash_v8_lega_mc = 368`,
  REWRITE_TAC[ghash_v8_lega_mc_def] THEN
  MP_TAC GHASH_V8_LENGTH THEN SIMP_TAC[LENGTH_SUB_LIST] THEN ARITH_TAC);;

let GCM_GHASH_V8_LEGA_FULL = prove
 (`!xi_p htbl_p in_p pc H h xi (blk:num->int128) n.
     h = ghash_twist H /\ 1 <= n /\ n <= 3 /\
     nonoverlapping (word pc, LENGTH ghash_v8_mc) (xi_p,16) /\
     nonoverlapping (xi_p,16) (in_p,16 * n) /\
     nonoverlapping (xi_p,16) (htbl_p,96)
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) ghash_v8_mc /\
               read PC s = word pc /\
               C_ARGUMENTS [xi_p; htbl_p; in_p; word (16 * n)] s /\
               read (memory :> bytes128 xi_p) s = xi /\
               (!i. i < n
                    ==> read (memory :> bytes128
                               (word_add in_p (word (16 * i)))) s = blk i) /\
               htable_mem_4 h htbl_p s)
          (\s. read PC s = word (pc + 0x168) /\
               read (memory :> bytes128 xi_p) s =
               word_bytereverse
                 (nist_ghash H (word_bytereverse xi)
                    (MAP word_bytereverse (list_of_seq blk n))))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(xi_p:int64,16)] ,,
           MAYCHANGE [Q0;Q1;Q2;Q3;Q4;Q5;Q6;Q7;
                      Q16;Q17;Q18;Q19;Q20;Q21;Q22;Q23;Q24;Q25;Q26;Q27;Q28;
                      Q29;Q30;Q31])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN
  EXISTS_TAC
   `\s. aligned_bytes_loaded s (word pc) ghash_v8_lega_mc /\
        read PC s = word pc /\
        C_ARGUMENTS [xi_p; htbl_p; in_p; word (16 * n)] s /\
        read (memory :> bytes128 xi_p) s = xi /\
        (!i. i < n
             ==> read (memory :> bytes128
                        (word_add in_p (word (16 * i)))) s = blk i) /\
        htable_mem_4 h htbl_p s` THEN
  CONJ_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[ghash_v8_lega_mc_def] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(CONJUNCT2 ALIGNED_BYTES_LOADED_SUB_LIST) THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC GCM_GHASH_V8_LEGA THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ASSUME
      `nonoverlapping (word pc, LENGTH ghash_v8_mc) (xi_p:int64,16)`) THEN
    REWRITE_TAC[GHASH_V8_LENGTH; GHASH_V8_LEGA_LENGTH; NONOVERLAPPING_CLAUSES;
                nonoverlapping_modulo] THEN
    MESON_TAC[ARITH_RULE `!i. i < 368 ==> i < 1220`]]);;

(* ------------------------------------------------------------------------- *)
(* GCM_GHASH_V8_CORRECT: the whole routine, every len = 16*n with n >= 1.      *)
(*                                                                           *)
(* `ASM_CASES` on `n <= 3` and each leg is one `MATCH_MP_TAC`.  The routine    *)
(* has TWO `ret`s -- 0x168 (leg A, `.Ldone_v8`) and 0x4c0 (leg B,             *)
(* `.Ldone4x`) -- so the exit PC is stated as a DISJUNCTION, which is the      *)
(* standard s2n-bignum shape for a multiple-exit core theorem (cf.            *)
(* `BIGNUM_ADD_CORRECT`'s three disjuncts).  Each leg proves one disjunct and  *)
(* `ENSURES_POSTCONDITION_THM` weakens it to the disjunction; the resulting    *)
(* implication is one `MESON_TAC`.  Phase 11's `ARM_ADD_RETURN_NOSTACK_TAC`    *)
(* collapses both disjuncts to `read PC s = returnaddress` anyway, so nothing  *)
(* downstream has to case-split on which `ret` fired.                          *)
(*                                                                           *)
(* `16 * n < 2 EXP 64` is needed only by leg B (leg A's n <= 3 makes it        *)
(* vacuous), but it is carried uniformly so the statement is one clause.       *)
(* ------------------------------------------------------------------------- *)

let GCM_GHASH_V8_CORRECT = prove
 (`!xi_p htbl_p in_p pc H h xi (blk:num->int128) n.
     h = ghash_twist H /\ 1 <= n /\ 16 * n < 2 EXP 64 /\
     nonoverlapping (word pc, LENGTH ghash_v8_mc) (xi_p,16) /\
     nonoverlapping (xi_p,16) (in_p,16 * n) /\
     nonoverlapping (xi_p,16) (htbl_p,96)
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) ghash_v8_mc /\
               read PC s = word pc /\
               C_ARGUMENTS [xi_p; htbl_p; in_p; word (16 * n)] s /\
               read (memory :> bytes128 xi_p) s = xi /\
               (!i. i < n
                    ==> read (memory :> bytes128
                               (word_add in_p (word (16 * i)))) s = blk i) /\
               htable_mem_4 h htbl_p s)
          (\s. (read PC s = word (pc + 0x168) \/
                read PC s = word (pc + 0x4c0)) /\
               read (memory :> bytes128 xi_p) s =
               word_bytereverse
                 (nist_ghash H (word_bytereverse xi)
                    (MAP word_bytereverse (list_of_seq blk n))))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(xi_p:int64,16)] ,,
           MAYCHANGE [Q0;Q1;Q2;Q3;Q4;Q5;Q6;Q7;
                      Q16;Q17;Q18;Q19;Q20;Q21;Q22;Q23;Q24;Q25;Q26;Q27;Q28;
                      Q29;Q30;Q31])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `n <= 3` THENL
   [MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN
    EXISTS_TAC
     `\s. read PC s = word (pc + 0x168) /\
          read (memory :> bytes128 xi_p) s =
          word_bytereverse
            (nist_ghash H (word_bytereverse xi)
               (MAP word_bytereverse (list_of_seq blk n)))` THEN
    CONJ_TAC THENL
     [GEN_TAC THEN REWRITE_TAC[] THEN MESON_TAC[];
      MATCH_MP_TAC GCM_GHASH_V8_LEGA_FULL THEN ASM_REWRITE_TAC[]];
    MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN
    EXISTS_TAC
     `\s. read PC s = word (pc + 0x4c0) /\
          read (memory :> bytes128 xi_p) s =
          word_bytereverse
            (nist_ghash H (word_bytereverse xi)
               (MAP word_bytereverse (list_of_seq blk n)))` THEN
    CONJ_TAC THENL
     [GEN_TAC THEN REWRITE_TAC[] THEN MESON_TAC[];
      MATCH_MP_TAC GCM_GHASH_V8_LEGB_FULL THEN ASM_REWRITE_TAC[] THEN
      ASM_ARITH_TAC]]);;

(* ========================================================================= *)
(* PHASE 11: the leaf subroutine wrapper.                                     *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* `gcm_ghash_v8_s2n` is a LEAF with no stack frame and no callee-save spills, so  *)
(* `ARM_ADD_RETURN_NOSTACK_TAC` applies directly.  Two non-obvious points.     *)
(*                                                                           *)
(* 1. The Q FRAME MUST EXCLUDE Q8..Q15, and that is why every frame in this    *)
(*    file lists `Q0..Q7; Q16..Q31` rather than all of `Q0..Q31`.  The AArch64 *)
(*    PCS makes the LOW halves of v8..v15 callee-saved, so                     *)
(*    `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI` permits only                 *)
(*    `Q8 :> tophalf ... Q15 :> tophalf` for those eight -- a core frame       *)
(*    claiming the full `Q8..Q15` is NOT subsumed by the ABI frame, and the     *)
(*    wrapper's final `MONOTONE_MAYCHANGE_TAC` fails with a bare               *)
(*    `MATCH_MP_TAC: No match` that says nothing about which register is at     *)
(*    fault.  The routine in fact touches only v0..v7 and v16..v31 (checked     *)
(*    against `objdump`: no `v8`..`v15` operand appears anywhere in the 305    *)
(*    instructions), so the narrower frame is not a weakening of anything --   *)
(*    the wide frame was simply over-permissive.                               *)
(*                                                                           *)
(* 2. `LENGTH ghash_v8_mc` must be REWRITTEN to the literal 1220 in BOTH the   *)
(*    goal and the transported core theorem.  With the symbolic `LENGTH` the   *)
(*    tactic's own program-preservation check fails with                       *)
(*    `could not prove that updates will not modify the program code` -- it    *)
(*    cannot see that the store to `xi_p` misses the code region without a     *)
(*    concrete size.                                                           *)
(*                                                                           *)
(* The two exit disjuncts of `GCM_GHASH_V8_CORRECT` cost nothing here: the     *)
(* tactic steps the `ret` once per disjunct and both land on                    *)
(* `read PC s = returnaddress`.                                                *)
(* ------------------------------------------------------------------------- *)

let GCM_GHASH_V8_SUBROUTINE_CORRECT = prove
 (`!xi_p htbl_p in_p pc H h xi (blk:num->int128) n returnaddress.
     h = ghash_twist H /\ 1 <= n /\ 16 * n < 2 EXP 64 /\
     nonoverlapping (word pc, LENGTH ghash_v8_mc) (xi_p,16) /\
     nonoverlapping (xi_p,16) (in_p,16 * n) /\
     nonoverlapping (xi_p,16) (htbl_p,96)
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) ghash_v8_mc /\
               read PC s = word pc /\
               read X30 s = returnaddress /\
               C_ARGUMENTS [xi_p; htbl_p; in_p; word (16 * n)] s /\
               read (memory :> bytes128 xi_p) s = xi /\
               (!i. i < n
                    ==> read (memory :> bytes128
                               (word_add in_p (word (16 * i)))) s = blk i) /\
               htable_mem_4 h htbl_p s)
          (\s. read PC s = returnaddress /\
               read (memory :> bytes128 xi_p) s =
               word_bytereverse
                 (nist_ghash H (word_bytereverse xi)
                    (MAP word_bytereverse (list_of_seq blk n))))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(xi_p:int64,16)])`,
  REWRITE_TAC[fst GHASH_V8_EXEC] THEN
  ARM_ADD_RETURN_NOSTACK_TAC GHASH_V8_EXEC
    (REWRITE_RULE[fst GHASH_V8_EXEC] GCM_GHASH_V8_CORRECT));;
