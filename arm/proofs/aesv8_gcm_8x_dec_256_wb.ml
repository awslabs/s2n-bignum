(* ========================================================================= *)
(* WB AES-256-GCM decrypt main loop (nblk > 8): ENSURES_WHILE proof.          *)
(*                                                                            *)
(* Extends the proven <=8-block WB chain (inlined below) to the               *)
(* software-pipelined 8-blocks-per-iteration main loop .L256_dec_main_loop    *)
(* (0x4a0..0x9ec), the GHASH catch-up prepretail (0x9f0..0xec0), and the tail *)
(* cascade (0xec0), so correctness holds for arbitrary nblk >= 1.             *)
(*                                                                            *)
(* Binary: arm/aes-gcm/aesv8_gcm_8x_dec_256_wb.o                              *)
(*                                                                            *)
(* KEY PIPELINE FACT:                                                         *)
(*         GHASH lags stores by one 8-block group, so the ENSURES_WHILE       *)
(*         invariant is the TWO-STREAM form (store/counter stream at 8(i+1),  *)
(*         GHASH stream at 8i, bridged by raw ciphertext regs q8..q15), NOT   *)
(*         a lag-free single fold.                                            *)
(*                                                                            *)
(* This file holds, in phase order:                                          *)
(*   Sec 1. Scalar rung lemmas (nblk>8 generalizations; pure word/arith).     *)
(*   Sec 2. Symbolic counter layer (gcm_ctr_add; closed form at symbolic k).  *)
(*   [later] FRONT-N capture (WBN_FRONT_BUF), ENSURES_WHILE loop, prepretail, *)
(*           recomposition, subroutine wrapper.                               *)
(*                                                                            *)
(* All lemmas in sec 1-2 are proved (total < 2s).                             *)
(* ========================================================================= *)


(* ====================================================================== *)
(* CONSOLIDATED: the <=8-block WB chain, formerly a separate file pulled   *)
(* in by a needs directive, is inlined here verbatim, so decrypt is         *)
(* a single file (mirrors the encrypt proof layout) and the BUF/GEN2       *)
(* per-block tail sims become in-file dedup targets.                        *)
(* ====================================================================== *)

needs "arm/proofs/aesv8_gcm_8x_dec_256_lemmas.ml";;
needs "arm/proofs/utils/aes_gcm_dec_spec.ml";;
needs "common/ghash_nist_bridge.ml";;

(* ------------------------------------------------------------------------- *)
(* Machine code (print_literal_from_elf "arm/aes-gcm/aesv8_gcm_8x_dec_256_wb.o") *)
(* ------------------------------------------------------------------------- *)

let aesv8_gcm_8x_dec_256_wb_mc = define_assert_from_elf "aesv8_gcm_8x_dec_256_wb_mc"
  "arm/aes-gcm/aesv8_gcm_8x_dec_256_wb.o"
[
  0xd503201f;       (* arm_NOP *)
  0xb400b9e1;       (* arm_CBZ X1 (word 5948) *)
  0xf240183f;       (* arm_TST X1 (rvalue (word 127)) *)
  0x5400b9a1;       (* arm_BNE (word 5940) *)
  0x6dbb27e8;       (* arm_STP D8 D9 SP (Preimmediate_Offset (iword (-- &80))) *)
  0x6d012fea;       (* arm_STP D10 D11 SP (Immediate_Offset (iword (&16))) *)
  0x6d0237ec;       (* arm_STP D12 D13 SP (Immediate_Offset (iword (&32))) *)
  0x6d033fee;       (* arm_STP D14 D15 SP (Immediate_Offset (iword (&48))) *)
  0xd343fc29;       (* arm_LSR X9 X1 3 *)
  0xaa0403f0;       (* arm_MOV X16 X4 *)
  0xaa0503eb;       (* arm_MOV X11 X5 *)
  0xd2f84005;       (* arm_MOVZ X5 (word 49664) 48 *)
  0xa9047fe5;       (* arm_STP X5 XZR SP (Immediate_Offset (iword (&64))) *)
  0x910103ea;       (* arm_ADD X10 SP (rvalue (word 64)) *)
  0xf101013f;       (* arm_CMP X9 (rvalue (word 64)) *)
  0x5400996d;       (* arm_BLE (word 4908) *)
  0x4c407200;       (* arm_LDR Q0 X16 No_Offset *)
  0xd2c0002f;       (* arm_MOVZ X15 (word 1) 32 *)
  0x4f00e41f;       (* arm_MOVI Q31 (word 0) *)
  0x4e181dff;       (* arm_INS_GEN Q31 X15 64 64 *)
  0x4ebf87fc;       (* arm_ADD_VEC Q28 Q31 Q31 32 128 *)
  0x4ebf878a;       (* arm_ADD_VEC Q10 Q28 Q31 32 128 *)
  0x4ebc878b;       (* arm_ADD_VEC Q11 Q28 Q28 32 128 *)
  0x4ebf856c;       (* arm_ADD_VEC Q12 Q11 Q31 32 128 *)
  0x4ebc856d;       (* arm_ADD_VEC Q13 Q11 Q28 32 128 *)
  0x4eaa856e;       (* arm_ADD_VEC Q14 Q11 Q10 32 128 *)
  0xaa0903e5;       (* arm_MOV X5 X9 *)
  0xd10004a5;       (* arm_SUB X5 X5 (rvalue (word 1)) *)
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
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b41;       (* arm_AESE Q1 Q26 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b42;       (* arm_AESE Q2 Q26 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b44;       (* arm_AESE Q4 Q26 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b46;       (* arm_AESE Q6 Q26 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b45;       (* arm_AESE Q5 Q26 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b43;       (* arm_AESE Q3 Q26 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b47;       (* arm_AESE Q7 Q26 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0xad41697c;       (* arm_LDP Q28 Q26 X11 (Immediate_Offset (iword (&32))) *)
  0x4e284b66;       (* arm_AESE Q6 Q27 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b64;       (* arm_AESE Q4 Q27 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b60;       (* arm_AESE Q0 Q27 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b65;       (* arm_AESE Q5 Q27 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b67;       (* arm_AESE Q7 Q27 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b61;       (* arm_AESE Q1 Q27 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b62;       (* arm_AESE Q2 Q27 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b63;       (* arm_AESE Q3 Q27 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b83;       (* arm_AESE Q3 Q28 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b82;       (* arm_AESE Q2 Q28 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b86;       (* arm_AESE Q6 Q28 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b81;       (* arm_AESE Q1 Q28 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b87;       (* arm_AESE Q7 Q28 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b85;       (* arm_AESE Q5 Q28 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b80;       (* arm_AESE Q0 Q28 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b84;       (* arm_AESE Q4 Q28 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0xad42717b;       (* arm_LDP Q27 Q28 X11 (Immediate_Offset (iword (&64))) *)
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
  0x4e284b47;       (* arm_AESE Q7 Q26 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b46;       (* arm_AESE Q6 Q26 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b67;       (* arm_AESE Q7 Q27 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b63;       (* arm_AESE Q3 Q27 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b66;       (* arm_AESE Q6 Q27 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b62;       (* arm_AESE Q2 Q27 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b60;       (* arm_AESE Q0 Q27 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b64;       (* arm_AESE Q4 Q27 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b61;       (* arm_AESE Q1 Q27 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b65;       (* arm_AESE Q5 Q27 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b80;       (* arm_AESE Q0 Q28 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b86;       (* arm_AESE Q6 Q28 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0xad436d7a;       (* arm_LDP Q26 Q27 X11 (Immediate_Offset (iword (&96))) *)
  0x4e284b84;       (* arm_AESE Q4 Q28 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b87;       (* arm_AESE Q7 Q28 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b85;       (* arm_AESE Q5 Q28 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b82;       (* arm_AESE Q2 Q28 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b83;       (* arm_AESE Q3 Q28 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b81;       (* arm_AESE Q1 Q28 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b44;       (* arm_AESE Q4 Q26 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b43;       (* arm_AESE Q3 Q26 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b47;       (* arm_AESE Q7 Q26 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b46;       (* arm_AESE Q6 Q26 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b45;       (* arm_AESE Q5 Q26 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b42;       (* arm_AESE Q2 Q26 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b41;       (* arm_AESE Q1 Q26 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0xad44697c;       (* arm_LDP Q28 Q26 X11 (Immediate_Offset (iword (&128))) *)
  0x4e284b65;       (* arm_AESE Q5 Q27 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b60;       (* arm_AESE Q0 Q27 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b63;       (* arm_AESE Q3 Q27 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b62;       (* arm_AESE Q2 Q27 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b67;       (* arm_AESE Q7 Q27 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b64;       (* arm_AESE Q4 Q27 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b61;       (* arm_AESE Q1 Q27 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b66;       (* arm_AESE Q6 Q27 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x9279e0a5;       (* arm_AND X5 X5 (rvalue (word 18446744073709551488)) *)
  0x4e284b87;       (* arm_AESE Q7 Q28 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b85;       (* arm_AESE Q5 Q28 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b80;       (* arm_AESE Q0 Q28 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b81;       (* arm_AESE Q1 Q28 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b82;       (* arm_AESE Q2 Q28 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b84;       (* arm_AESE Q4 Q28 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b83;       (* arm_AESE Q3 Q28 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b86;       (* arm_AESE Q6 Q28 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b42;       (* arm_AESE Q2 Q26 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4c407073;       (* arm_LDR Q19 X3 No_Offset *)
  0x6e134273;       (* arm_EXT Q19 Q19 Q19 64 *)
  0x4e200a73;       (* arm_REV64_VEC Q19 Q19 8 *)
  0xad45717b;       (* arm_LDP Q27 Q28 X11 (Immediate_Offset (iword (&160))) *)
  0x8b410c04;       (* arm_ADD X4 X0 (Shiftedreg X1 LSR 3) *)
  0x8b0000a5;       (* arm_ADD X5 X5 X0 *)
  0x4e284b43;       (* arm_AESE Q3 Q26 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b46;       (* arm_AESE Q6 Q26 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b44;       (* arm_AESE Q4 Q26 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b45;       (* arm_AESE Q5 Q26 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b47;       (* arm_AESE Q7 Q26 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b41;       (* arm_AESE Q1 Q26 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b64;       (* arm_AESE Q4 Q27 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b67;       (* arm_AESE Q7 Q27 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b65;       (* arm_AESE Q5 Q27 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b61;       (* arm_AESE Q1 Q27 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b62;       (* arm_AESE Q2 Q27 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b60;       (* arm_AESE Q0 Q27 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b66;       (* arm_AESE Q6 Q27 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b63;       (* arm_AESE Q3 Q27 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0xad466d7a;       (* arm_LDP Q26 Q27 X11 (Immediate_Offset (iword (&192))) *)
  0x4e284b80;       (* arm_AESE Q0 Q28 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0x4e284b87;       (* arm_AESE Q7 Q28 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b83;       (* arm_AESE Q3 Q28 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b81;       (* arm_AESE Q1 Q28 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b85;       (* arm_AESE Q5 Q28 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b84;       (* arm_AESE Q4 Q28 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b82;       (* arm_AESE Q2 Q28 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b86;       (* arm_AESE Q6 Q28 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x3dc0397c;       (* arm_LDR Q28 X11 (Immediate_Offset (word 224)) *)
  0x4e284b41;       (* arm_AESE Q1 Q26 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b44;       (* arm_AESE Q4 Q26 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b45;       (* arm_AESE Q5 Q26 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0xeb05001f;       (* arm_CMP X0 X5 *)
  0x4e284b43;       (* arm_AESE Q3 Q26 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b42;       (* arm_AESE Q2 Q26 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b46;       (* arm_AESE Q6 Q26 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b47;       (* arm_AESE Q7 Q26 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b65;       (* arm_AESE Q5 Q27 *)
  0x4e284b61;       (* arm_AESE Q1 Q27 *)
  0x4e284b62;       (* arm_AESE Q2 Q27 *)
  0x4e284b60;       (* arm_AESE Q0 Q27 *)
  0x4e284b64;       (* arm_AESE Q4 Q27 *)
  0x4e284b66;       (* arm_AESE Q6 Q27 *)
  0x4e284b63;       (* arm_AESE Q3 Q27 *)
  0x4e284b67;       (* arm_AESE Q7 Q27 *)
  0x540054aa;       (* arm_BGE (word 2708) *)
  0xacc12408;       (* arm_LDP Q8 Q9 X0 (Postimmediate_Offset (iword (&32))) *)
  0xacc12c0a;       (* arm_LDP Q10 Q11 X0 (Postimmediate_Offset (iword (&32))) *)
  0xacc1340c;       (* arm_LDP Q12 Q13 X0 (Postimmediate_Offset (iword (&32))) *)
  0xacc13c0e;       (* arm_LDP Q14 Q15 X0 (Postimmediate_Offset (iword (&32))) *)
  0xeb05001f;       (* arm_CMP X0 X5 *)
  0xce017121;       (* arm_EOR3 Q1 Q9 Q1 Q28 *)
  0xce007100;       (* arm_EOR3 Q0 Q8 Q0 Q28 *)
  0xac810440;       (* arm_STP Q0 Q1 X2 (Postimmediate_Offset (iword (&32))) *)
  0x6e200bc0;       (* arm_REV32_VEC Q0 Q30 8 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0xce037163;       (* arm_EOR3 Q3 Q11 Q3 Q28 *)
  0xce0571a5;       (* arm_EOR3 Q5 Q13 Q5 Q28 *)
  0xce047184;       (* arm_EOR3 Q4 Q12 Q4 Q28 *)
  0x6e200bc1;       (* arm_REV32_VEC Q1 Q30 8 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0xce027142;       (* arm_EOR3 Q2 Q10 Q2 Q28 *)
  0xac810c42;       (* arm_STP Q2 Q3 X2 (Postimmediate_Offset (iword (&32))) *)
  0x6e200bc2;       (* arm_REV32_VEC Q2 Q30 8 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0xce0671c6;       (* arm_EOR3 Q6 Q14 Q6 Q28 *)
  0x6e200bc3;       (* arm_REV32_VEC Q3 Q30 8 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0xac811444;       (* arm_STP Q4 Q5 X2 (Postimmediate_Offset (iword (&32))) *)
  0xce0771e7;       (* arm_EOR3 Q7 Q15 Q7 Q28 *)
  0xac811c46;       (* arm_STP Q6 Q7 X2 (Postimmediate_Offset (iword (&32))) *)
  0x6e200bc4;       (* arm_REV32_VEC Q4 Q30 8 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0x54002aaa;       (* arm_BGE (word 1364) *)
  0x6e200bc5;       (* arm_REV32_VEC Q5 Q30 8 *)
  0xad406d7a;       (* arm_LDP Q26 Q27 X11 (Immediate_Offset (iword (&0))) *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0x4e200929;       (* arm_REV64_VEC Q9 Q9 8 *)
  0x3dc024d7;       (* arm_LDR Q23 X6 (Immediate_Offset (word 144)) *)
  0x3dc02cd9;       (* arm_LDR Q25 X6 (Immediate_Offset (word 176)) *)
  0x6e200bc6;       (* arm_REV32_VEC Q6 Q30 8 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0x4e200908;       (* arm_REV64_VEC Q8 Q8 8 *)
  0x6e134273;       (* arm_EXT Q19 Q19 Q19 64 *)
  0x4e20098c;       (* arm_REV64_VEC Q12 Q12 8 *)
  0x4e20096b;       (* arm_REV64_VEC Q11 Q11 8 *)
  0x6e200bc7;       (* arm_REV32_VEC Q7 Q30 8 *)
  0x4e2009ef;       (* arm_REV64_VEC Q15 Q15 8 *)
  0x4e284b43;       (* arm_AESE Q3 Q26 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b46;       (* arm_AESE Q6 Q26 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b42;       (* arm_AESE Q2 Q26 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b47;       (* arm_AESE Q7 Q26 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b45;       (* arm_AESE Q5 Q26 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b44;       (* arm_AESE Q4 Q26 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b41;       (* arm_AESE Q1 Q26 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0xad41697c;       (* arm_LDP Q28 Q26 X11 (Immediate_Offset (iword (&32))) *)
  0x6e331d08;       (* arm_EOR_VEC Q8 Q8 Q19 128 *)
  0x3dc018d4;       (* arm_LDR Q20 X6 (Immediate_Offset (word 96)) *)
  0x3dc020d6;       (* arm_LDR Q22 X6 (Immediate_Offset (word 128)) *)
  0x4e284b66;       (* arm_AESE Q6 Q27 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b64;       (* arm_AESE Q4 Q27 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e20094a;       (* arm_REV64_VEC Q10 Q10 8 *)
  0x4e284b63;       (* arm_AESE Q3 Q27 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b60;       (* arm_AESE Q0 Q27 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b65;       (* arm_AESE Q5 Q27 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b62;       (* arm_AESE Q2 Q27 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4ec82932;       (* arm_TRN1 Q18 Q9 Q8 64 128 *)
  0x4e284b67;       (* arm_AESE Q7 Q27 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b61;       (* arm_AESE Q1 Q27 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b84;       (* arm_AESE Q4 Q28 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b80;       (* arm_AESE Q0 Q28 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b83;       (* arm_AESE Q3 Q28 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b86;       (* arm_AESE Q6 Q28 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b87;       (* arm_AESE Q7 Q28 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x0ef9e113;       (* arm_PMULL_VEC Q19 Q8 Q25 64 *)
  0x4e284b85;       (* arm_AESE Q5 Q28 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b82;       (* arm_AESE Q2 Q28 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b81;       (* arm_AESE Q1 Q28 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0xad42717b;       (* arm_LDP Q27 Q28 X11 (Immediate_Offset (iword (&64))) *)
  0x4ef6e15d;       (* arm_PMULL2_VEC Q29 Q10 Q22 64 *)
  0x4e284b43;       (* arm_AESE Q3 Q26 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4ef7e130;       (* arm_PMULL2_VEC Q16 Q9 Q23 64 *)
  0x0ef7e137;       (* arm_PMULL_VEC Q23 Q9 Q23 64 *)
  0x4e284b45;       (* arm_AESE Q5 Q26 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b46;       (* arm_AESE Q6 Q26 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4ef9e111;       (* arm_PMULL2_VEC Q17 Q8 Q25 64 *)
  0x4e284b44;       (* arm_AESE Q4 Q26 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b41;       (* arm_AESE Q1 Q26 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4ec86928;       (* arm_TRN2 Q8 Q9 Q8 64 128 *)
  0x4ef4e169;       (* arm_PMULL2_VEC Q9 Q11 Q20 64 *)
  0x4e284b42;       (* arm_AESE Q2 Q26 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x6e301e31;       (* arm_EOR_VEC Q17 Q17 Q16 128 *)
  0x4e284b65;       (* arm_AESE Q5 Q27 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b47;       (* arm_AESE Q7 Q26 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b63;       (* arm_AESE Q3 Q27 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b62;       (* arm_AESE Q2 Q27 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b60;       (* arm_AESE Q0 Q27 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b61;       (* arm_AESE Q1 Q27 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b66;       (* arm_AESE Q6 Q27 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b67;       (* arm_AESE Q7 Q27 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b64;       (* arm_AESE Q4 Q27 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x3dc01cd5;       (* arm_LDR Q21 X6 (Immediate_Offset (word 112)) *)
  0x3dc028d8;       (* arm_LDR Q24 X6 (Immediate_Offset (word 160)) *)
  0x6e321d08;       (* arm_EOR_VEC Q8 Q8 Q18 128 *)
  0x0ef6e156;       (* arm_PMULL_VEC Q22 Q10 Q22 64 *)
  0xad436d7a;       (* arm_LDP Q26 Q27 X11 (Immediate_Offset (iword (&96))) *)
  0x4e284b85;       (* arm_AESE Q5 Q28 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x6e371e73;       (* arm_EOR_VEC Q19 Q19 Q23 128 *)
  0x4e284b80;       (* arm_AESE Q0 Q28 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b83;       (* arm_AESE Q3 Q28 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b87;       (* arm_AESE Q7 Q28 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b81;       (* arm_AESE Q1 Q28 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b82;       (* arm_AESE Q2 Q28 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b86;       (* arm_AESE Q6 Q28 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0xce1d2631;       (* arm_EOR3 Q17 Q17 Q29 Q9 *)
  0x4eca297d;       (* arm_TRN1 Q29 Q11 Q10 64 128 *)
  0x4e2009ad;       (* arm_REV64_VEC Q13 Q13 8 *)
  0x4ef8e112;       (* arm_PMULL2_VEC Q18 Q8 Q24 64 *)
  0x0ef8e118;       (* arm_PMULL_VEC Q24 Q8 Q24 64 *)
  0x4eca696a;       (* arm_TRN2 Q10 Q11 Q10 64 128 *)
  0x4e284b43;       (* arm_AESE Q3 Q26 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b84;       (* arm_AESE Q4 Q28 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4ecc29b0;       (* arm_TRN1 Q16 Q13 Q12 64 128 *)
  0x4e284b41;       (* arm_AESE Q1 Q26 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b46;       (* arm_AESE Q6 Q26 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x6e3d1d4a;       (* arm_EOR_VEC Q10 Q10 Q29 128 *)
  0x0ef4e174;       (* arm_PMULL_VEC Q20 Q11 Q20 64 *)
  0x4e284b44;       (* arm_AESE Q4 Q26 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b42;       (* arm_AESE Q2 Q26 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b45;       (* arm_AESE Q5 Q26 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b47;       (* arm_AESE Q7 Q26 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4ef5e15d;       (* arm_PMULL2_VEC Q29 Q10 Q21 64 *)
  0x0ef5e155;       (* arm_PMULL_VEC Q21 Q10 Q21 64 *)
  0xce165273;       (* arm_EOR3 Q19 Q19 Q22 Q20 *)
  0x3dc00cd7;       (* arm_LDR Q23 X6 (Immediate_Offset (word 48)) *)
  0x3dc014d9;       (* arm_LDR Q25 X6 (Immediate_Offset (word 80)) *)
  0x4e2009ce;       (* arm_REV64_VEC Q14 Q14 8 *)
  0x6e381e52;       (* arm_EOR_VEC Q18 Q18 Q24 128 *)
  0x4e284b62;       (* arm_AESE Q2 Q27 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b65;       (* arm_AESE Q5 Q27 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0xad44697c;       (* arm_LDP Q28 Q26 X11 (Immediate_Offset (iword (&128))) *)
  0x3dc000d4;       (* arm_LDR Q20 X6 (Immediate_Offset (word 0)) *)
  0x3dc008d6;       (* arm_LDR Q22 X6 (Immediate_Offset (word 32)) *)
  0xce157652;       (* arm_EOR3 Q18 Q18 Q21 Q29 *)
  0x4e284b67;       (* arm_AESE Q7 Q27 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b61;       (* arm_AESE Q1 Q27 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b63;       (* arm_AESE Q3 Q27 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b66;       (* arm_AESE Q6 Q27 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x3dc004d5;       (* arm_LDR Q21 X6 (Immediate_Offset (word 16)) *)
  0x3dc010d8;       (* arm_LDR Q24 X6 (Immediate_Offset (word 64)) *)
  0x4e284b60;       (* arm_AESE Q0 Q27 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b64;       (* arm_AESE Q4 Q27 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4ef9e188;       (* arm_PMULL2_VEC Q8 Q12 Q25 64 *)
  0x0ef9e199;       (* arm_PMULL_VEC Q25 Q12 Q25 64 *)
  0x4ecc69ac;       (* arm_TRN2 Q12 Q13 Q12 64 128 *)
  0x4e284b85;       (* arm_AESE Q5 Q28 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4ef7e1aa;       (* arm_PMULL2_VEC Q10 Q13 Q23 64 *)
  0x4e284b82;       (* arm_AESE Q2 Q28 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b86;       (* arm_AESE Q6 Q28 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x0ef7e1b7;       (* arm_PMULL_VEC Q23 Q13 Q23 64 *)
  0x4e284b81;       (* arm_AESE Q1 Q28 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b84;       (* arm_AESE Q4 Q28 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b80;       (* arm_AESE Q0 Q28 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4ef6e1cb;       (* arm_PMULL2_VEC Q11 Q14 Q22 64 *)
  0x4ece29ed;       (* arm_TRN1 Q13 Q15 Q14 64 128 *)
  0x4e284b83;       (* arm_AESE Q3 Q28 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b87;       (* arm_AESE Q7 Q28 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0xad45717b;       (* arm_LDP Q27 Q28 X11 (Immediate_Offset (iword (&160))) *)
  0x0ef6e1d6;       (* arm_PMULL_VEC Q22 Q14 Q22 64 *)
  0x4ece69ee;       (* arm_TRN2 Q14 Q15 Q14 64 128 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0xce082a31;       (* arm_EOR3 Q17 Q17 Q8 Q10 *)
  0x4e284b43;       (* arm_AESE Q3 Q26 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b46;       (* arm_AESE Q6 Q26 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x6e2d1dce;       (* arm_EOR_VEC Q14 Q14 Q13 128 *)
  0x4e284b45;       (* arm_AESE Q5 Q26 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0xacc12408;       (* arm_LDP Q8 Q9 X0 (Postimmediate_Offset (iword (&32))) *)
  0x6e301d8c;       (* arm_EOR_VEC Q12 Q12 Q16 128 *)
  0x4e284b47;       (* arm_AESE Q7 Q26 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4ef5e1cd;       (* arm_PMULL2_VEC Q13 Q14 Q21 64 *)
  0x4e284b42;       (* arm_AESE Q2 Q26 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b41;       (* arm_AESE Q1 Q26 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4ef8e190;       (* arm_PMULL2_VEC Q16 Q12 Q24 64 *)
  0x0ef8e198;       (* arm_PMULL_VEC Q24 Q12 Q24 64 *)
  0x4ef4e1ec;       (* arm_PMULL2_VEC Q12 Q15 Q20 64 *)
  0x0ef4e1f4;       (* arm_PMULL_VEC Q20 Q15 Q20 64 *)
  0x4e284b63;       (* arm_AESE Q3 Q27 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b66;       (* arm_AESE Q6 Q27 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x0ef5e1d5;       (* arm_PMULL_VEC Q21 Q14 Q21 64 *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0xce195e73;       (* arm_EOR3 Q19 Q19 Q25 Q23 *)
  0x4e284b44;       (* arm_AESE Q4 Q26 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0xce184252;       (* arm_EOR3 Q18 Q18 Q24 Q16 *)
  0xce0b3231;       (* arm_EOR3 Q17 Q17 Q11 Q12 *)
  0x4e284b62;       (* arm_AESE Q2 Q27 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b65;       (* arm_AESE Q5 Q27 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b67;       (* arm_AESE Q7 Q27 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b61;       (* arm_AESE Q1 Q27 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b60;       (* arm_AESE Q0 Q27 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b64;       (* arm_AESE Q4 Q27 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0xce165273;       (* arm_EOR3 Q19 Q19 Q22 Q20 *)
  0x6e200bd4;       (* arm_REV32_VEC Q20 Q30 8 *)
  0xfd400150;       (* arm_LDR D16 X10 (Immediate_Offset (word 0)) *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0x4e284b81;       (* arm_AESE Q1 Q28 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0xad466d7a;       (* arm_LDP Q26 Q27 X11 (Immediate_Offset (iword (&192))) *)
  0x4e284b80;       (* arm_AESE Q0 Q28 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b86;       (* arm_AESE Q6 Q28 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0xce153652;       (* arm_EOR3 Q18 Q18 Q21 Q13 *)
  0x6e200bd6;       (* arm_REV32_VEC Q22 Q30 8 *)
  0x4e284b82;       (* arm_AESE Q2 Q28 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0xacc12c0a;       (* arm_LDP Q10 Q11 X0 (Postimmediate_Offset (iword (&32))) *)
  0x4e284b87;       (* arm_AESE Q7 Q28 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x6e114235;       (* arm_EXT Q21 Q17 Q17 64 *)
  0x4e284b85;       (* arm_AESE Q5 Q28 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0x4e284b83;       (* arm_AESE Q3 Q28 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b42;       (* arm_AESE Q2 Q26 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b47;       (* arm_AESE Q7 Q26 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b46;       (* arm_AESE Q6 Q26 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x6e200bd7;       (* arm_REV32_VEC Q23 Q30 8 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0x0ef0e23d;       (* arm_PMULL_VEC Q29 Q17 Q16 64 *)
  0xce114e52;       (* arm_EOR3 Q18 Q18 Q17 Q19 *)
  0x4e284b41;       (* arm_AESE Q1 Q26 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b84;       (* arm_AESE Q4 Q28 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x3dc0397c;       (* arm_LDR Q28 X11 (Immediate_Offset (word 224)) *)
  0x4e284b45;       (* arm_AESE Q5 Q26 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b43;       (* arm_AESE Q3 Q26 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0xce1d5652;       (* arm_EOR3 Q18 Q18 Q29 Q21 *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b44;       (* arm_AESE Q4 Q26 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0xacc1340c;       (* arm_LDP Q12 Q13 X0 (Postimmediate_Offset (iword (&32))) *)
  0x4e284b61;       (* arm_AESE Q1 Q27 *)
  0x4e284b62;       (* arm_AESE Q2 Q27 *)
  0xacc13c0e;       (* arm_LDP Q14 Q15 X0 (Postimmediate_Offset (iword (&32))) *)
  0x4e284b60;       (* arm_AESE Q0 Q27 *)
  0x4e284b65;       (* arm_AESE Q5 Q27 *)
  0x6e200bd9;       (* arm_REV32_VEC Q25 Q30 8 *)
  0xce027142;       (* arm_EOR3 Q2 Q10 Q2 Q28 *)
  0xce017121;       (* arm_EOR3 Q1 Q9 Q1 Q28 *)
  0x6e124255;       (* arm_EXT Q21 Q18 Q18 64 *)
  0x4e284b67;       (* arm_AESE Q7 Q27 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0x0ef0e251;       (* arm_PMULL_VEC Q17 Q18 Q16 64 *)
  0x4e284b64;       (* arm_AESE Q4 Q27 *)
  0xce0571a5;       (* arm_EOR3 Q5 Q13 Q5 Q28 *)
  0xce007100;       (* arm_EOR3 Q0 Q8 Q0 Q28 *)
  0x4e284b63;       (* arm_AESE Q3 Q27 *)
  0xac810440;       (* arm_STP Q0 Q1 X2 (Postimmediate_Offset (iword (&32))) *)
  0x4eb41e80;       (* arm_MOV_VEC Q0 Q20 128 *)
  0xce047184;       (* arm_EOR3 Q4 Q12 Q4 Q28 *)
  0xce154673;       (* arm_EOR3 Q19 Q19 Q21 Q17 *)
  0xce037163;       (* arm_EOR3 Q3 Q11 Q3 Q28 *)
  0xac810c42;       (* arm_STP Q2 Q3 X2 (Postimmediate_Offset (iword (&32))) *)
  0x4eb91f23;       (* arm_MOV_VEC Q3 Q25 128 *)
  0x4eb71ee2;       (* arm_MOV_VEC Q2 Q23 128 *)
  0x4e284b66;       (* arm_AESE Q6 Q27 *)
  0x4eb61ec1;       (* arm_MOV_VEC Q1 Q22 128 *)
  0xac811444;       (* arm_STP Q4 Q5 X2 (Postimmediate_Offset (iword (&32))) *)
  0xce0771e7;       (* arm_EOR3 Q7 Q15 Q7 Q28 *)
  0xce0671c6;       (* arm_EOR3 Q6 Q14 Q6 Q28 *)
  0x6e200bc4;       (* arm_REV32_VEC Q4 Q30 8 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0xeb05001f;       (* arm_CMP X0 X5 *)
  0xac811c46;       (* arm_STP Q6 Q7 X2 (Postimmediate_Offset (iword (&32))) *)
  0x54ffd5ab;       (* arm_BLT (word 2095796) *)
  0xad406d7a;       (* arm_LDP Q26 Q27 X11 (Immediate_Offset (iword (&0))) *)
  0x6e200bc5;       (* arm_REV32_VEC Q5 Q30 8 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0x4e20098c;       (* arm_REV64_VEC Q12 Q12 8 *)
  0x3dc01cd5;       (* arm_LDR Q21 X6 (Immediate_Offset (word 112)) *)
  0x3dc028d8;       (* arm_LDR Q24 X6 (Immediate_Offset (word 160)) *)
  0x6e200bc6;       (* arm_REV32_VEC Q6 Q30 8 *)
  0x4e200908;       (* arm_REV64_VEC Q8 Q8 8 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0x6e134273;       (* arm_EXT Q19 Q19 Q19 64 *)
  0x3dc024d7;       (* arm_LDR Q23 X6 (Immediate_Offset (word 144)) *)
  0x3dc02cd9;       (* arm_LDR Q25 X6 (Immediate_Offset (word 176)) *)
  0x4e200929;       (* arm_REV64_VEC Q9 Q9 8 *)
  0x6e200bc7;       (* arm_REV32_VEC Q7 Q30 8 *)
  0x4e20094a;       (* arm_REV64_VEC Q10 Q10 8 *)
  0x3dc018d4;       (* arm_LDR Q20 X6 (Immediate_Offset (word 96)) *)
  0x3dc020d6;       (* arm_LDR Q22 X6 (Immediate_Offset (word 128)) *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b41;       (* arm_AESE Q1 Q26 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b44;       (* arm_AESE Q4 Q26 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b43;       (* arm_AESE Q3 Q26 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b45;       (* arm_AESE Q5 Q26 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b46;       (* arm_AESE Q6 Q26 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b64;       (* arm_AESE Q4 Q27 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b47;       (* arm_AESE Q7 Q26 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b42;       (* arm_AESE Q2 Q26 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0xad41697c;       (* arm_LDP Q28 Q26 X11 (Immediate_Offset (iword (&32))) *)
  0x4e284b60;       (* arm_AESE Q0 Q27 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x6e331d08;       (* arm_EOR_VEC Q8 Q8 Q19 128 *)
  0x4e284b67;       (* arm_AESE Q7 Q27 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b66;       (* arm_AESE Q6 Q27 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b62;       (* arm_AESE Q2 Q27 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b63;       (* arm_AESE Q3 Q27 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b61;       (* arm_AESE Q1 Q27 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b65;       (* arm_AESE Q5 Q27 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4ef7e130;       (* arm_PMULL2_VEC Q16 Q9 Q23 64 *)
  0x4ec82932;       (* arm_TRN1 Q18 Q9 Q8 64 128 *)
  0x0ef9e113;       (* arm_PMULL_VEC Q19 Q8 Q25 64 *)
  0x4e20096b;       (* arm_REV64_VEC Q11 Q11 8 *)
  0x0ef7e137;       (* arm_PMULL_VEC Q23 Q9 Q23 64 *)
  0x4e284b85;       (* arm_AESE Q5 Q28 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b87;       (* arm_AESE Q7 Q28 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b81;       (* arm_AESE Q1 Q28 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b83;       (* arm_AESE Q3 Q28 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b86;       (* arm_AESE Q6 Q28 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4ef9e111;       (* arm_PMULL2_VEC Q17 Q8 Q25 64 *)
  0x4e284b80;       (* arm_AESE Q0 Q28 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b47;       (* arm_AESE Q7 Q26 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b45;       (* arm_AESE Q5 Q26 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e2009ce;       (* arm_REV64_VEC Q14 Q14 8 *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b82;       (* arm_AESE Q2 Q28 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b46;       (* arm_AESE Q6 Q26 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4ef6e15d;       (* arm_PMULL2_VEC Q29 Q10 Q22 64 *)
  0x4ec86928;       (* arm_TRN2 Q8 Q9 Q8 64 128 *)
  0x4e284b84;       (* arm_AESE Q4 Q28 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0xad42717b;       (* arm_LDP Q27 Q28 X11 (Immediate_Offset (iword (&64))) *)
  0x4e284b41;       (* arm_AESE Q1 Q26 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4ef4e169;       (* arm_PMULL2_VEC Q9 Q11 Q20 64 *)
  0x4e284b42;       (* arm_AESE Q2 Q26 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x6e301e31;       (* arm_EOR_VEC Q17 Q17 Q16 128 *)
  0x6e321d08;       (* arm_EOR_VEC Q8 Q8 Q18 128 *)
  0x4e284b44;       (* arm_AESE Q4 Q26 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x0ef6e156;       (* arm_PMULL_VEC Q22 Q10 Q22 64 *)
  0x4e284b43;       (* arm_AESE Q3 Q26 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0xce1d2631;       (* arm_EOR3 Q17 Q17 Q29 Q9 *)
  0x4eca297d;       (* arm_TRN1 Q29 Q11 Q10 64 128 *)
  0x4eca696a;       (* arm_TRN2 Q10 Q11 Q10 64 128 *)
  0x4ef8e112;       (* arm_PMULL2_VEC Q18 Q8 Q24 64 *)
  0x0ef4e174;       (* arm_PMULL_VEC Q20 Q11 Q20 64 *)
  0x6e371e73;       (* arm_EOR_VEC Q19 Q19 Q23 128 *)
  0x0ef8e118;       (* arm_PMULL_VEC Q24 Q8 Q24 64 *)
  0x4e284b65;       (* arm_AESE Q5 Q27 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b60;       (* arm_AESE Q0 Q27 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0xce165273;       (* arm_EOR3 Q19 Q19 Q22 Q20 *)
  0x3dc000d4;       (* arm_LDR Q20 X6 (Immediate_Offset (word 0)) *)
  0x3dc008d6;       (* arm_LDR Q22 X6 (Immediate_Offset (word 32)) *)
  0x4e284b67;       (* arm_AESE Q7 Q27 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b62;       (* arm_AESE Q2 Q27 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b66;       (* arm_AESE Q6 Q27 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x6e381e52;       (* arm_EOR_VEC Q18 Q18 Q24 128 *)
  0x6e3d1d4a;       (* arm_EOR_VEC Q10 Q10 Q29 128 *)
  0x4e284b87;       (* arm_AESE Q7 Q28 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b61;       (* arm_AESE Q1 Q27 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b82;       (* arm_AESE Q2 Q28 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b63;       (* arm_AESE Q3 Q27 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b64;       (* arm_AESE Q4 Q27 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b81;       (* arm_AESE Q1 Q28 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4ef5e15d;       (* arm_PMULL2_VEC Q29 Q10 Q21 64 *)
  0x4e284b86;       (* arm_AESE Q6 Q28 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b84;       (* arm_AESE Q4 Q28 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b83;       (* arm_AESE Q3 Q28 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x0ef5e155;       (* arm_PMULL_VEC Q21 Q10 Q21 64 *)
  0x4e284b80;       (* arm_AESE Q0 Q28 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b85;       (* arm_AESE Q5 Q28 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0xad436d7a;       (* arm_LDP Q26 Q27 X11 (Immediate_Offset (iword (&96))) *)
  0x3dc00cd7;       (* arm_LDR Q23 X6 (Immediate_Offset (word 48)) *)
  0x3dc014d9;       (* arm_LDR Q25 X6 (Immediate_Offset (word 80)) *)
  0x4e2009ef;       (* arm_REV64_VEC Q15 Q15 8 *)
  0x4e2009ad;       (* arm_REV64_VEC Q13 Q13 8 *)
  0xce157652;       (* arm_EOR3 Q18 Q18 Q21 Q29 *)
  0x4ecc29b0;       (* arm_TRN1 Q16 Q13 Q12 64 128 *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x3dc004d5;       (* arm_LDR Q21 X6 (Immediate_Offset (word 16)) *)
  0x3dc010d8;       (* arm_LDR Q24 X6 (Immediate_Offset (word 64)) *)
  0x4e284b46;       (* arm_AESE Q6 Q26 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b45;       (* arm_AESE Q5 Q26 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b47;       (* arm_AESE Q7 Q26 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4ef9e188;       (* arm_PMULL2_VEC Q8 Q12 Q25 64 *)
  0x4ef7e1aa;       (* arm_PMULL2_VEC Q10 Q13 Q23 64 *)
  0x0ef9e199;       (* arm_PMULL_VEC Q25 Q12 Q25 64 *)
  0x4ecc69ac;       (* arm_TRN2 Q12 Q13 Q12 64 128 *)
  0x0ef7e1b7;       (* arm_PMULL_VEC Q23 Q13 Q23 64 *)
  0x4ece29ed;       (* arm_TRN1 Q13 Q15 Q14 64 128 *)
  0x4e284b67;       (* arm_AESE Q7 Q27 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4ef6e1cb;       (* arm_PMULL2_VEC Q11 Q14 Q22 64 *)
  0x4e284b41;       (* arm_AESE Q1 Q26 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b42;       (* arm_AESE Q2 Q26 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b43;       (* arm_AESE Q3 Q26 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b44;       (* arm_AESE Q4 Q26 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0xad44697c;       (* arm_LDP Q28 Q26 X11 (Immediate_Offset (iword (&128))) *)
  0x0ef6e1d6;       (* arm_PMULL_VEC Q22 Q14 Q22 64 *)
  0x4e284b65;       (* arm_AESE Q5 Q27 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b61;       (* arm_AESE Q1 Q27 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b64;       (* arm_AESE Q4 Q27 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b66;       (* arm_AESE Q6 Q27 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b62;       (* arm_AESE Q2 Q27 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0xce082a31;       (* arm_EOR3 Q17 Q17 Q8 Q10 *)
  0x4e284b60;       (* arm_AESE Q0 Q27 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4ece69ee;       (* arm_TRN2 Q14 Q15 Q14 64 128 *)
  0x4e284b63;       (* arm_AESE Q3 Q27 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b80;       (* arm_AESE Q0 Q28 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b87;       (* arm_AESE Q7 Q28 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b84;       (* arm_AESE Q4 Q28 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b81;       (* arm_AESE Q1 Q28 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b85;       (* arm_AESE Q5 Q28 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b86;       (* arm_AESE Q6 Q28 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b83;       (* arm_AESE Q3 Q28 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b44;       (* arm_AESE Q4 Q26 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x6e301d8c;       (* arm_EOR_VEC Q12 Q12 Q16 128 *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b41;       (* arm_AESE Q1 Q26 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x6e2d1dce;       (* arm_EOR_VEC Q14 Q14 Q13 128 *)
  0x4e284b46;       (* arm_AESE Q6 Q26 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b47;       (* arm_AESE Q7 Q26 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4ef8e190;       (* arm_PMULL2_VEC Q16 Q12 Q24 64 *)
  0x4e284b82;       (* arm_AESE Q2 Q28 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x0ef8e198;       (* arm_PMULL_VEC Q24 Q12 Q24 64 *)
  0x4ef4e1ec;       (* arm_PMULL2_VEC Q12 Q15 Q20 64 *)
  0x4ef5e1cd;       (* arm_PMULL2_VEC Q13 Q14 Q21 64 *)
  0x0ef5e1d5;       (* arm_PMULL_VEC Q21 Q14 Q21 64 *)
  0x0ef4e1f4;       (* arm_PMULL_VEC Q20 Q15 Q20 64 *)
  0xad45717b;       (* arm_LDP Q27 Q28 X11 (Immediate_Offset (iword (&160))) *)
  0xce195e73;       (* arm_EOR3 Q19 Q19 Q25 Q23 *)
  0xce184252;       (* arm_EOR3 Q18 Q18 Q24 Q16 *)
  0x4e284b42;       (* arm_AESE Q2 Q26 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b43;       (* arm_AESE Q3 Q26 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b45;       (* arm_AESE Q5 Q26 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0xce0b3231;       (* arm_EOR3 Q17 Q17 Q11 Q12 *)
  0xce165273;       (* arm_EOR3 Q19 Q19 Q22 Q20 *)
  0xfd400150;       (* arm_LDR D16 X10 (Immediate_Offset (word 0)) *)
  0xce153652;       (* arm_EOR3 Q18 Q18 Q21 Q13 *)
  0x4e284b64;       (* arm_AESE Q4 Q27 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b66;       (* arm_AESE Q6 Q27 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b65;       (* arm_AESE Q5 Q27 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b60;       (* arm_AESE Q0 Q27 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284b62;       (* arm_AESE Q2 Q27 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b63;       (* arm_AESE Q3 Q27 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0xce114e52;       (* arm_EOR3 Q18 Q18 Q17 Q19 *)
  0x4e284b67;       (* arm_AESE Q7 Q27 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b61;       (* arm_AESE Q1 Q27 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0xad466d7a;       (* arm_LDP Q26 Q27 X11 (Immediate_Offset (iword (&192))) *)
  0x6e114235;       (* arm_EXT Q21 Q17 Q17 64 *)
  0x4e284b82;       (* arm_AESE Q2 Q28 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b81;       (* arm_AESE Q1 Q28 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b80;       (* arm_AESE Q0 Q28 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x0ef0e23d;       (* arm_PMULL_VEC Q29 Q17 Q16 64 *)
  0x4e284b83;       (* arm_AESE Q3 Q28 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0x4e284b87;       (* arm_AESE Q7 Q28 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b86;       (* arm_AESE Q6 Q28 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x4e284b84;       (* arm_AESE Q4 Q28 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b85;       (* arm_AESE Q5 Q28 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b43;       (* arm_AESE Q3 Q26 *)
  0x4e286863;       (* arm_AESMC Q3 Q3 *)
  0xce1d5652;       (* arm_EOR3 Q18 Q18 Q29 Q21 *)
  0x4e284b63;       (* arm_AESE Q3 Q27 *)
  0x4e284b42;       (* arm_AESE Q2 Q26 *)
  0x4e286842;       (* arm_AESMC Q2 Q2 *)
  0x4e284b46;       (* arm_AESE Q6 Q26 *)
  0x4e2868c6;       (* arm_AESMC Q6 Q6 *)
  0x0ef0e251;       (* arm_PMULL_VEC Q17 Q18 Q16 64 *)
  0x4e284b44;       (* arm_AESE Q4 Q26 *)
  0x4e286884;       (* arm_AESMC Q4 Q4 *)
  0x4e284b47;       (* arm_AESE Q7 Q26 *)
  0x4e2868e7;       (* arm_AESMC Q7 Q7 *)
  0x4e284b40;       (* arm_AESE Q0 Q26 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x3dc0397c;       (* arm_LDR Q28 X11 (Immediate_Offset (word 224)) *)
  0x4e284b41;       (* arm_AESE Q1 Q26 *)
  0x4e286821;       (* arm_AESMC Q1 Q1 *)
  0x4e284b64;       (* arm_AESE Q4 Q27 *)
  0x6e124255;       (* arm_EXT Q21 Q18 Q18 64 *)
  0x4e284b45;       (* arm_AESE Q5 Q26 *)
  0x4e2868a5;       (* arm_AESMC Q5 Q5 *)
  0x4e284b66;       (* arm_AESE Q6 Q27 *)
  0x4e284b62;       (* arm_AESE Q2 Q27 *)
  0x4e284b61;       (* arm_AESE Q1 Q27 *)
  0x4e284b65;       (* arm_AESE Q5 Q27 *)
  0xce154673;       (* arm_EOR3 Q19 Q19 Q21 Q17 *)
  0x4ebf87de;       (* arm_ADD_VEC Q30 Q30 Q31 32 128 *)
  0x4e284b67;       (* arm_AESE Q7 Q27 *)
  0x4e284b60;       (* arm_AESE Q0 Q27 *)
  0x6e134270;       (* arm_EXT Q16 Q19 Q19 64 *)
  0xcb000085;       (* arm_SUB X5 X4 X0 *)
  0xf101c0bf;       (* arm_CMP X5 (rvalue (word 112)) *)
  0x3cc10409;       (* arm_LDR Q9 X0 (Postimmediate_Offset (word 16)) *)
  0xad4564d8;       (* arm_LDP Q24 Q25 X6 (Immediate_Offset (iword (&160))) *)
  0x4ebc1f9d;       (* arm_MOV_VEC Q29 Q28 128 *)
  0xad4354d4;       (* arm_LDP Q20 Q21 X6 (Immediate_Offset (iword (&96))) *)
  0xce00752c;       (* arm_EOR3 Q12 Q9 Q0 Q29 *)
  0xad445cd6;       (* arm_LDP Q22 Q23 X6 (Immediate_Offset (iword (&128))) *)
  0x5400172c;       (* arm_BGT (word 740) *)
  0x4ea61cc7;       (* arm_MOV_VEC Q7 Q6 128 *)
  0x6ebf87de;       (* arm_SUB_VEC Q30 Q30 Q31 32 128 *)
  0x4ea51ca6;       (* arm_MOV_VEC Q6 Q5 128 *)
  0x4ea41c85;       (* arm_MOV_VEC Q5 Q4 128 *)
  0x4ea31c64;       (* arm_MOV_VEC Q4 Q3 128 *)
  0x0f00e413;       (* arm_MOVI D19 (word 0) *)
  0x0f00e411;       (* arm_MOVI D17 (word 0) *)
  0x0f00e412;       (* arm_MOVI D18 (word 0) *)
  0x4ea21c43;       (* arm_MOV_VEC Q3 Q2 128 *)
  0xf10180bf;       (* arm_CMP X5 (rvalue (word 96)) *)
  0x4ea11c22;       (* arm_MOV_VEC Q2 Q1 128 *)
  0x540005ec;       (* arm_BGT (word 188) *)
  0x4ea61cc7;       (* arm_MOV_VEC Q7 Q6 128 *)
  0x4ea51ca6;       (* arm_MOV_VEC Q6 Q5 128 *)
  0x4ea41c85;       (* arm_MOV_VEC Q5 Q4 128 *)
  0xf10140bf;       (* arm_CMP X5 (rvalue (word 80)) *)
  0x6ebf87de;       (* arm_SUB_VEC Q30 Q30 Q31 32 128 *)
  0x4ea31c64;       (* arm_MOV_VEC Q4 Q3 128 *)
  0x4ea11c23;       (* arm_MOV_VEC Q3 Q1 128 *)
  0x540006ac;       (* arm_BGT (word 212) *)
  0xf10100bf;       (* arm_CMP X5 (rvalue (word 64)) *)
  0x4ea61cc7;       (* arm_MOV_VEC Q7 Q6 128 *)
  0x6ebf87de;       (* arm_SUB_VEC Q30 Q30 Q31 32 128 *)
  0x4ea51ca6;       (* arm_MOV_VEC Q6 Q5 128 *)
  0x4ea41c85;       (* arm_MOV_VEC Q5 Q4 128 *)
  0x4ea11c24;       (* arm_MOV_VEC Q4 Q1 128 *)
  0x540007ac;       (* arm_BGT (word 244) *)
  0x6ebf87de;       (* arm_SUB_VEC Q30 Q30 Q31 32 128 *)
  0x4ea61cc7;       (* arm_MOV_VEC Q7 Q6 128 *)
  0xf100c0bf;       (* arm_CMP X5 (rvalue (word 48)) *)
  0x4ea51ca6;       (* arm_MOV_VEC Q6 Q5 128 *)
  0x4ea11c25;       (* arm_MOV_VEC Q5 Q1 128 *)
  0x540008ac;       (* arm_BGT (word 276) *)
  0x3dc010d8;       (* arm_LDR Q24 X6 (Immediate_Offset (word 64)) *)
  0x6ebf87de;       (* arm_SUB_VEC Q30 Q30 Q31 32 128 *)
  0x4ea61cc7;       (* arm_MOV_VEC Q7 Q6 128 *)
  0xf10080bf;       (* arm_CMP X5 (rvalue (word 32)) *)
  0x4ea11c26;       (* arm_MOV_VEC Q6 Q1 128 *)
  0x54000a0c;       (* arm_BGT (word 320) *)
  0x6ebf87de;       (* arm_SUB_VEC Q30 Q30 Q31 32 128 *)
  0x4ea11c27;       (* arm_MOV_VEC Q7 Q1 128 *)
  0xf10040bf;       (* arm_CMP X5 (rvalue (word 16)) *)
  0x54000b6c;       (* arm_BGT (word 364) *)
  0x6ebf87de;       (* arm_SUB_VEC Q30 Q30 Q31 32 128 *)
  0x3dc004d5;       (* arm_LDR Q21 X6 (Immediate_Offset (word 16)) *)
  0x14000069;       (* arm_B (word 420) *)
  0x4e200928;       (* arm_REV64_VEC Q8 Q9 8 *)
  0x3cc10409;       (* arm_LDR Q9 X0 (Postimmediate_Offset (word 16)) *)
  0x4c9f704c;       (* arm_STR Q12 X2 (Postimmediate_Offset (word 16)) *)
  0x6e184312;       (* arm_EXT Q18 Q24 Q24 64 *)
  0x6e301d08;       (* arm_EOR_VEC Q8 Q8 Q16 128 *)
  0x6e08411b;       (* arm_EXT Q27 Q8 Q8 64 *)
  0xce01752c;       (* arm_EOR3 Q12 Q9 Q1 Q29 *)
  0x4ef9e111;       (* arm_PMULL2_VEC Q17 Q8 Q25 64 *)
  0x2e281f7b;       (* arm_EOR_VEC Q27 Q27 Q8 64 *)
  0x0f00e410;       (* arm_MOVI D16 (word 0) *)
  0x0ef9e113;       (* arm_PMULL_VEC Q19 Q8 Q25 64 *)
  0x0ef2e372;       (* arm_PMULL_VEC Q18 Q27 Q18 64 *)
  0x4e200928;       (* arm_REV64_VEC Q8 Q9 8 *)
  0x6e301d08;       (* arm_EOR_VEC Q8 Q8 Q16 128 *)
  0x3cc10409;       (* arm_LDR Q9 X0 (Postimmediate_Offset (word 16)) *)
  0x0f00e410;       (* arm_MOVI D16 (word 0) *)
  0x6e08411b;       (* arm_EXT Q27 Q8 Q8 64 *)
  0x4c9f704c;       (* arm_STR Q12 X2 (Postimmediate_Offset (word 16)) *)
  0x4ef7e11c;       (* arm_PMULL2_VEC Q28 Q8 Q23 64 *)
  0x0ef7e11a;       (* arm_PMULL_VEC Q26 Q8 Q23 64 *)
  0xce02752c;       (* arm_EOR3 Q12 Q9 Q2 Q29 *)
  0x6e3a1e73;       (* arm_EOR_VEC Q19 Q19 Q26 128 *)
  0x2e281f7b;       (* arm_EOR_VEC Q27 Q27 Q8 64 *)
  0x0ef8e37b;       (* arm_PMULL_VEC Q27 Q27 Q24 64 *)
  0x6e3b1e52;       (* arm_EOR_VEC Q18 Q18 Q27 128 *)
  0x6e3c1e31;       (* arm_EOR_VEC Q17 Q17 Q28 128 *)
  0x4e200928;       (* arm_REV64_VEC Q8 Q9 8 *)
  0x6e301d08;       (* arm_EOR_VEC Q8 Q8 Q16 128 *)
  0x4ef6e11c;       (* arm_PMULL2_VEC Q28 Q8 Q22 64 *)
  0x6e08411b;       (* arm_EXT Q27 Q8 Q8 64 *)
  0x3cc10409;       (* arm_LDR Q9 X0 (Postimmediate_Offset (word 16)) *)
  0x2e281f7b;       (* arm_EOR_VEC Q27 Q27 Q8 64 *)
  0x4c9f704c;       (* arm_STR Q12 X2 (Postimmediate_Offset (word 16)) *)
  0x0ef6e11a;       (* arm_PMULL_VEC Q26 Q8 Q22 64 *)
  0x6e1542aa;       (* arm_EXT Q10 Q21 Q21 64 *)
  0x0eeae37b;       (* arm_PMULL_VEC Q27 Q27 Q10 64 *)
  0x6e3c1e31;       (* arm_EOR_VEC Q17 Q17 Q28 128 *)
  0xce03752c;       (* arm_EOR3 Q12 Q9 Q3 Q29 *)
  0x6e3a1e73;       (* arm_EOR_VEC Q19 Q19 Q26 128 *)
  0x6e3b1e52;       (* arm_EOR_VEC Q18 Q18 Q27 128 *)
  0x0f00e410;       (* arm_MOVI D16 (word 0) *)
  0x4e200928;       (* arm_REV64_VEC Q8 Q9 8 *)
  0x6e301d08;       (* arm_EOR_VEC Q8 Q8 Q16 128 *)
  0x6e08411b;       (* arm_EXT Q27 Q8 Q8 64 *)
  0x3cc10409;       (* arm_LDR Q9 X0 (Postimmediate_Offset (word 16)) *)
  0x0f00e410;       (* arm_MOVI D16 (word 0) *)
  0x0ef4e11a;       (* arm_PMULL_VEC Q26 Q8 Q20 64 *)
  0x4ef4e11c;       (* arm_PMULL2_VEC Q28 Q8 Q20 64 *)
  0x2e281f7b;       (* arm_EOR_VEC Q27 Q27 Q8 64 *)
  0x6e3c1e31;       (* arm_EOR_VEC Q17 Q17 Q28 128 *)
  0x0ef5e37b;       (* arm_PMULL_VEC Q27 Q27 Q21 64 *)
  0x6e3a1e73;       (* arm_EOR_VEC Q19 Q19 Q26 128 *)
  0x4c9f704c;       (* arm_STR Q12 X2 (Postimmediate_Offset (word 16)) *)
  0x6e3b1e52;       (* arm_EOR_VEC Q18 Q18 Q27 128 *)
  0xce04752c;       (* arm_EOR3 Q12 Q9 Q4 Q29 *)
  0x3dc014d9;       (* arm_LDR Q25 X6 (Immediate_Offset (word 80)) *)
  0x4e200928;       (* arm_REV64_VEC Q8 Q9 8 *)
  0x6e301d08;       (* arm_EOR_VEC Q8 Q8 Q16 128 *)
  0x3cc10409;       (* arm_LDR Q9 X0 (Postimmediate_Offset (word 16)) *)
  0x3dc010d8;       (* arm_LDR Q24 X6 (Immediate_Offset (word 64)) *)
  0x6e08411b;       (* arm_EXT Q27 Q8 Q8 64 *)
  0x4c9f704c;       (* arm_STR Q12 X2 (Postimmediate_Offset (word 16)) *)
  0xce05752c;       (* arm_EOR3 Q12 Q9 Q5 Q29 *)
  0x2e281f7b;       (* arm_EOR_VEC Q27 Q27 Q8 64 *)
  0x6e18430b;       (* arm_EXT Q11 Q24 Q24 64 *)
  0x0ef9e11a;       (* arm_PMULL_VEC Q26 Q8 Q25 64 *)
  0x4ef9e11c;       (* arm_PMULL2_VEC Q28 Q8 Q25 64 *)
  0x0f00e410;       (* arm_MOVI D16 (word 0) *)
  0x0eebe37b;       (* arm_PMULL_VEC Q27 Q27 Q11 64 *)
  0x6e3a1e73;       (* arm_EOR_VEC Q19 Q19 Q26 128 *)
  0x6e3c1e31;       (* arm_EOR_VEC Q17 Q17 Q28 128 *)
  0x6e3b1e52;       (* arm_EOR_VEC Q18 Q18 Q27 128 *)
  0x4e200928;       (* arm_REV64_VEC Q8 Q9 8 *)
  0x3dc00cd7;       (* arm_LDR Q23 X6 (Immediate_Offset (word 48)) *)
  0x3cc10409;       (* arm_LDR Q9 X0 (Postimmediate_Offset (word 16)) *)
  0x6e301d08;       (* arm_EOR_VEC Q8 Q8 Q16 128 *)
  0x6e08411b;       (* arm_EXT Q27 Q8 Q8 64 *)
  0x0ef7e11a;       (* arm_PMULL_VEC Q26 Q8 Q23 64 *)
  0x4c9f704c;       (* arm_STR Q12 X2 (Postimmediate_Offset (word 16)) *)
  0xce06752c;       (* arm_EOR3 Q12 Q9 Q6 Q29 *)
  0x2e281f7b;       (* arm_EOR_VEC Q27 Q27 Q8 64 *)
  0x6e3a1e73;       (* arm_EOR_VEC Q19 Q19 Q26 128 *)
  0x0f00e410;       (* arm_MOVI D16 (word 0) *)
  0x0ef8e37b;       (* arm_PMULL_VEC Q27 Q27 Q24 64 *)
  0x4ef7e11c;       (* arm_PMULL2_VEC Q28 Q8 Q23 64 *)
  0x6e3b1e52;       (* arm_EOR_VEC Q18 Q18 Q27 128 *)
  0x6e3c1e31;       (* arm_EOR_VEC Q17 Q17 Q28 128 *)
  0x4e200928;       (* arm_REV64_VEC Q8 Q9 8 *)
  0x6e301d08;       (* arm_EOR_VEC Q8 Q8 Q16 128 *)
  0x6e08411b;       (* arm_EXT Q27 Q8 Q8 64 *)
  0x3dc008d6;       (* arm_LDR Q22 X6 (Immediate_Offset (word 32)) *)
  0x2e281f7b;       (* arm_EOR_VEC Q27 Q27 Q8 64 *)
  0x3cc10409;       (* arm_LDR Q9 X0 (Postimmediate_Offset (word 16)) *)
  0x4c9f704c;       (* arm_STR Q12 X2 (Postimmediate_Offset (word 16)) *)
  0x3dc004d5;       (* arm_LDR Q21 X6 (Immediate_Offset (word 16)) *)
  0x0ef6e11a;       (* arm_PMULL_VEC Q26 Q8 Q22 64 *)
  0x6e1542aa;       (* arm_EXT Q10 Q21 Q21 64 *)
  0x6e3a1e73;       (* arm_EOR_VEC Q19 Q19 Q26 128 *)
  0xce07752c;       (* arm_EOR3 Q12 Q9 Q7 Q29 *)
  0x4ef6e11c;       (* arm_PMULL2_VEC Q28 Q8 Q22 64 *)
  0x0eeae37b;       (* arm_PMULL_VEC Q27 Q27 Q10 64 *)
  0x0f00e410;       (* arm_MOVI D16 (word 0) *)
  0x6e3c1e31;       (* arm_EOR_VEC Q17 Q17 Q28 128 *)
  0x6e3b1e52;       (* arm_EOR_VEC Q18 Q18 Q27 128 *)
  0x6e200bde;       (* arm_REV32_VEC Q30 Q30 8 *)
  0x3d80021e;       (* arm_STR Q30 X16 (Immediate_Offset (word 0)) *)
  0x3dc000d4;       (* arm_LDR Q20 X6 (Immediate_Offset (word 0)) *)
  0x4e200928;       (* arm_REV64_VEC Q8 Q9 8 *)
  0x6e301d08;       (* arm_EOR_VEC Q8 Q8 Q16 128 *)
  0x6e084110;       (* arm_EXT Q16 Q8 Q8 64 *)
  0x4ef4e11c;       (* arm_PMULL2_VEC Q28 Q8 Q20 64 *)
  0x2e281e10;       (* arm_EOR_VEC Q16 Q16 Q8 64 *)
  0x0ef4e11a;       (* arm_PMULL_VEC Q26 Q8 Q20 64 *)
  0x6e3c1e31;       (* arm_EOR_VEC Q17 Q17 Q28 128 *)
  0x0ef5e210;       (* arm_PMULL_VEC Q16 Q16 Q21 64 *)
  0x6e301e52;       (* arm_EOR_VEC Q18 Q18 Q16 128 *)
  0xfd400150;       (* arm_LDR D16 X10 (Immediate_Offset (word 0)) *)
  0x6e3a1e73;       (* arm_EOR_VEC Q19 Q19 Q26 128 *)
  0x0ef0e235;       (* arm_PMULL_VEC Q21 Q17 Q16 64 *)
  0x6e331e2e;       (* arm_EOR_VEC Q14 Q17 Q19 128 *)
  0x6e114231;       (* arm_EXT Q17 Q17 Q17 64 *)
  0x4c00704c;       (* arm_STR Q12 X2 No_Offset *)
  0x6e2e1e52;       (* arm_EOR_VEC Q18 Q18 Q14 128 *)
  0x6e351e35;       (* arm_EOR_VEC Q21 Q17 Q21 128 *)
  0x6e351e52;       (* arm_EOR_VEC Q18 Q18 Q21 128 *)
  0x0ef0e251;       (* arm_PMULL_VEC Q17 Q18 Q16 64 *)
  0x6e124252;       (* arm_EXT Q18 Q18 Q18 64 *)
  0x6e311e73;       (* arm_EOR_VEC Q19 Q19 Q17 128 *)
  0x6e321e73;       (* arm_EOR_VEC Q19 Q19 Q18 128 *)
  0x6e134273;       (* arm_EXT Q19 Q19 Q19 64 *)
  0x4e200a73;       (* arm_REV64_VEC Q19 Q19 8 *)
  0x4c007073;       (* arm_STR Q19 X3 No_Offset *)
  0xaa0903e0;       (* arm_MOV X0 X9 *)
  0x6d412fea;       (* arm_LDP D10 D11 SP (Immediate_Offset (iword (&16))) *)
  0x6d4237ec;       (* arm_LDP D12 D13 SP (Immediate_Offset (iword (&32))) *)
  0x6d433fee;       (* arm_LDP D14 D15 SP (Immediate_Offset (iword (&48))) *)
  0x6cc527e8;       (* arm_LDP D8 D9 SP (Postimmediate_Offset (iword (&80))) *)
  0xd65f03c0;       (* arm_RET X30 *)
  0x4e200928;       (* arm_REV64_VEC Q8 Q9 8 *)
  0x3cc10409;       (* arm_LDR Q9 X0 (Postimmediate_Offset (word 16)) *)
  0x4c9f704c;       (* arm_STR Q12 X2 (Postimmediate_Offset (word 16)) *)
  0x6e184312;       (* arm_EXT Q18 Q24 Q24 64 *)
  0x6e301d08;       (* arm_EOR_VEC Q8 Q8 Q16 128 *)
  0x6e08411b;       (* arm_EXT Q27 Q8 Q8 64 *)
  0xce01752c;       (* arm_EOR3 Q12 Q9 Q1 Q29 *)
  0x4ef9e111;       (* arm_PMULL2_VEC Q17 Q8 Q25 64 *)
  0x2e281f7b;       (* arm_EOR_VEC Q27 Q27 Q8 64 *)
  0x0ef9e113;       (* arm_PMULL_VEC Q19 Q8 Q25 64 *)
  0x0ef2e372;       (* arm_PMULL_VEC Q18 Q27 Q18 64 *)
  0x4e200928;       (* arm_REV64_VEC Q8 Q9 8 *)
  0x3cc10409;       (* arm_LDR Q9 X0 (Postimmediate_Offset (word 16)) *)
  0x6e08411b;       (* arm_EXT Q27 Q8 Q8 64 *)
  0x4c9f704c;       (* arm_STR Q12 X2 (Postimmediate_Offset (word 16)) *)
  0x4ef7e10d;       (* arm_PMULL2_VEC Q13 Q8 Q23 64 *)
  0x0ef7e10e;       (* arm_PMULL_VEC Q14 Q8 Q23 64 *)
  0xce02752c;       (* arm_EOR3 Q12 Q9 Q2 Q29 *)
  0x2e281f7b;       (* arm_EOR_VEC Q27 Q27 Q8 64 *)
  0x0ef8e36f;       (* arm_PMULL_VEC Q15 Q27 Q24 64 *)
  0x4e200928;       (* arm_REV64_VEC Q8 Q9 8 *)
  0x4ef6e11c;       (* arm_PMULL2_VEC Q28 Q8 Q22 64 *)
  0x6e08411b;       (* arm_EXT Q27 Q8 Q8 64 *)
  0x3cc10409;       (* arm_LDR Q9 X0 (Postimmediate_Offset (word 16)) *)
  0x2e281f7b;       (* arm_EOR_VEC Q27 Q27 Q8 64 *)
  0x4c9f704c;       (* arm_STR Q12 X2 (Postimmediate_Offset (word 16)) *)
  0x0ef6e11a;       (* arm_PMULL_VEC Q26 Q8 Q22 64 *)
  0x6e1542aa;       (* arm_EXT Q10 Q21 Q21 64 *)
  0x0eeae37b;       (* arm_PMULL_VEC Q27 Q27 Q10 64 *)
  0xce1c3631;       (* arm_EOR3 Q17 Q17 Q28 Q13 *)
  0xce03752c;       (* arm_EOR3 Q12 Q9 Q3 Q29 *)
  0xce1a3a73;       (* arm_EOR3 Q19 Q19 Q26 Q14 *)
  0xce1b3e52;       (* arm_EOR3 Q18 Q18 Q27 Q15 *)
  0x4e200928;       (* arm_REV64_VEC Q8 Q9 8 *)
  0x6e08411b;       (* arm_EXT Q27 Q8 Q8 64 *)
  0x3cc10409;       (* arm_LDR Q9 X0 (Postimmediate_Offset (word 16)) *)
  0x0ef4e10e;       (* arm_PMULL_VEC Q14 Q8 Q20 64 *)
  0x4ef4e10d;       (* arm_PMULL2_VEC Q13 Q8 Q20 64 *)
  0x2e281f7b;       (* arm_EOR_VEC Q27 Q27 Q8 64 *)
  0x0ef5e36f;       (* arm_PMULL_VEC Q15 Q27 Q21 64 *)
  0x4c9f704c;       (* arm_STR Q12 X2 (Postimmediate_Offset (word 16)) *)
  0xce04752c;       (* arm_EOR3 Q12 Q9 Q4 Q29 *)
  0x3dc014d9;       (* arm_LDR Q25 X6 (Immediate_Offset (word 80)) *)
  0x4e200928;       (* arm_REV64_VEC Q8 Q9 8 *)
  0x3cc10409;       (* arm_LDR Q9 X0 (Postimmediate_Offset (word 16)) *)
  0x3dc010d8;       (* arm_LDR Q24 X6 (Immediate_Offset (word 64)) *)
  0x6e08411b;       (* arm_EXT Q27 Q8 Q8 64 *)
  0x4c9f704c;       (* arm_STR Q12 X2 (Postimmediate_Offset (word 16)) *)
  0xce05752c;       (* arm_EOR3 Q12 Q9 Q5 Q29 *)
  0x2e281f7b;       (* arm_EOR_VEC Q27 Q27 Q8 64 *)
  0x6e18430b;       (* arm_EXT Q11 Q24 Q24 64 *)
  0x0ef9e11a;       (* arm_PMULL_VEC Q26 Q8 Q25 64 *)
  0x4ef9e11c;       (* arm_PMULL2_VEC Q28 Q8 Q25 64 *)
  0x0eebe37b;       (* arm_PMULL_VEC Q27 Q27 Q11 64 *)
  0xce1a3a73;       (* arm_EOR3 Q19 Q19 Q26 Q14 *)
  0xce1c3631;       (* arm_EOR3 Q17 Q17 Q28 Q13 *)
  0xce1b3e52;       (* arm_EOR3 Q18 Q18 Q27 Q15 *)
  0x4e200928;       (* arm_REV64_VEC Q8 Q9 8 *)
  0x3dc00cd7;       (* arm_LDR Q23 X6 (Immediate_Offset (word 48)) *)
  0x3cc10409;       (* arm_LDR Q9 X0 (Postimmediate_Offset (word 16)) *)
  0x6e08411b;       (* arm_EXT Q27 Q8 Q8 64 *)
  0x0ef7e10e;       (* arm_PMULL_VEC Q14 Q8 Q23 64 *)
  0x4c9f704c;       (* arm_STR Q12 X2 (Postimmediate_Offset (word 16)) *)
  0xce06752c;       (* arm_EOR3 Q12 Q9 Q6 Q29 *)
  0x2e281f7b;       (* arm_EOR_VEC Q27 Q27 Q8 64 *)
  0x0ef8e36f;       (* arm_PMULL_VEC Q15 Q27 Q24 64 *)
  0x4ef7e10d;       (* arm_PMULL2_VEC Q13 Q8 Q23 64 *)
  0x4e200928;       (* arm_REV64_VEC Q8 Q9 8 *)
  0x6e08411b;       (* arm_EXT Q27 Q8 Q8 64 *)
  0x3dc008d6;       (* arm_LDR Q22 X6 (Immediate_Offset (word 32)) *)
  0x2e281f7b;       (* arm_EOR_VEC Q27 Q27 Q8 64 *)
  0x3cc10409;       (* arm_LDR Q9 X0 (Postimmediate_Offset (word 16)) *)
  0x4c9f704c;       (* arm_STR Q12 X2 (Postimmediate_Offset (word 16)) *)
  0x3dc004d5;       (* arm_LDR Q21 X6 (Immediate_Offset (word 16)) *)
  0x0ef6e11a;       (* arm_PMULL_VEC Q26 Q8 Q22 64 *)
  0x6e1542aa;       (* arm_EXT Q10 Q21 Q21 64 *)
  0xce1a3a73;       (* arm_EOR3 Q19 Q19 Q26 Q14 *)
  0xce07752c;       (* arm_EOR3 Q12 Q9 Q7 Q29 *)
  0x4ef6e11c;       (* arm_PMULL2_VEC Q28 Q8 Q22 64 *)
  0x0eeae37b;       (* arm_PMULL_VEC Q27 Q27 Q10 64 *)
  0xce1c3631;       (* arm_EOR3 Q17 Q17 Q28 Q13 *)
  0xce1b3e52;       (* arm_EOR3 Q18 Q18 Q27 Q15 *)
  0x6e200bde;       (* arm_REV32_VEC Q30 Q30 8 *)
  0x3d80021e;       (* arm_STR Q30 X16 (Immediate_Offset (word 0)) *)
  0x3dc000d4;       (* arm_LDR Q20 X6 (Immediate_Offset (word 0)) *)
  0x4e200928;       (* arm_REV64_VEC Q8 Q9 8 *)
  0x6e084110;       (* arm_EXT Q16 Q8 Q8 64 *)
  0x4ef4e11c;       (* arm_PMULL2_VEC Q28 Q8 Q20 64 *)
  0x2e281e10;       (* arm_EOR_VEC Q16 Q16 Q8 64 *)
  0x0ef4e11a;       (* arm_PMULL_VEC Q26 Q8 Q20 64 *)
  0x6e3c1e31;       (* arm_EOR_VEC Q17 Q17 Q28 128 *)
  0x0ef5e210;       (* arm_PMULL_VEC Q16 Q16 Q21 64 *)
  0x6e301e52;       (* arm_EOR_VEC Q18 Q18 Q16 128 *)
  0xfd400150;       (* arm_LDR D16 X10 (Immediate_Offset (word 0)) *)
  0x6e3a1e73;       (* arm_EOR_VEC Q19 Q19 Q26 128 *)
  0x17ffff8d;       (* arm_B (word 268434996) *)
  0x4c40721e;       (* arm_LDR Q30 X16 No_Offset *)
  0x4c407073;       (* arm_LDR Q19 X3 No_Offset *)
  0xd2c0002f;       (* arm_MOVZ X15 (word 1) 32 *)
  0x4f00e41f;       (* arm_MOVI Q31 (word 0) *)
  0x6e134273;       (* arm_EXT Q19 Q19 Q19 64 *)
  0x4e200a73;       (* arm_REV64_VEC Q19 Q19 8 *)
  0x4e181dff;       (* arm_INS_GEN Q31 X15 64 64 *)
  0x6e134270;       (* arm_EXT Q16 Q19 Q19 64 *)
  0x6e200bdd;       (* arm_REV32_VEC Q29 Q30 8 *)
  0xad400961;       (* arm_LDP Q1 Q2 X11 (Immediate_Offset (iword (&0))) *)
  0xad411163;       (* arm_LDP Q3 Q4 X11 (Immediate_Offset (iword (&32))) *)
  0xad421965;       (* arm_LDP Q5 Q6 X11 (Immediate_Offset (iword (&64))) *)
  0xad432167;       (* arm_LDP Q7 Q8 X11 (Immediate_Offset (iword (&96))) *)
  0xad442969;       (* arm_LDP Q9 Q10 X11 (Immediate_Offset (iword (&128))) *)
  0xad45316b;       (* arm_LDP Q11 Q12 X11 (Immediate_Offset (iword (&160))) *)
  0xad46396d;       (* arm_LDP Q13 Q14 X11 (Immediate_Offset (iword (&192))) *)
  0x3dc0396f;       (* arm_LDR Q15 X11 (Immediate_Offset (word 224)) *)
  0xf100813f;       (* arm_CMP X9 (rvalue (word 32)) *)
  0x5400008c;       (* arm_BGT (word 16) *)
  0xf100413f;       (* arm_CMP X9 (rvalue (word 16)) *)
  0x540003a0;       (* arm_BEQ (word 116) *)
  0x14000014;       (* arm_B (word 80) *)
  0xf100c13f;       (* arm_CMP X9 (rvalue (word 48)) *)
  0x54000140;       (* arm_BEQ (word 40) *)
  0x14000001;       (* arm_B (word 4) *)
  0x3dc014d8;       (* arm_LDR Q24 X6 (Immediate_Offset (word 80)) *)
  0xfd4024d9;       (* arm_LDR D25 X6 (Immediate_Offset (word 72)) *)
  0x6e104215;       (* arm_EXT Q21 Q16 Q16 64 *)
  0x2e301eb5;       (* arm_EOR_VEC Q21 Q21 Q16 64 *)
  0x4ef8e211;       (* arm_PMULL2_VEC Q17 Q16 Q24 64 *)
  0x0ef8e213;       (* arm_PMULL_VEC Q19 Q16 Q24 64 *)
  0x0ef9e2b2;       (* arm_PMULL_VEC Q18 Q21 Q25 64 *)
  0x14000019;       (* arm_B (word 100) *)
  0x3dc00cd8;       (* arm_LDR Q24 X6 (Immediate_Offset (word 48)) *)
  0xfd4020d9;       (* arm_LDR D25 X6 (Immediate_Offset (word 64)) *)
  0x6e104215;       (* arm_EXT Q21 Q16 Q16 64 *)
  0x2e301eb5;       (* arm_EOR_VEC Q21 Q21 Q16 64 *)
  0x4ef8e211;       (* arm_PMULL2_VEC Q17 Q16 Q24 64 *)
  0x0ef8e213;       (* arm_PMULL_VEC Q19 Q16 Q24 64 *)
  0x0ef9e2b2;       (* arm_PMULL_VEC Q18 Q21 Q25 64 *)
  0x1400003c;       (* arm_B (word 240) *)
  0x3dc008d8;       (* arm_LDR Q24 X6 (Immediate_Offset (word 32)) *)
  0xfd400cd9;       (* arm_LDR D25 X6 (Immediate_Offset (word 24)) *)
  0x6e104215;       (* arm_EXT Q21 Q16 Q16 64 *)
  0x2e301eb5;       (* arm_EOR_VEC Q21 Q21 Q16 64 *)
  0x4ef8e211;       (* arm_PMULL2_VEC Q17 Q16 Q24 64 *)
  0x0ef8e213;       (* arm_PMULL_VEC Q19 Q16 Q24 64 *)
  0x0ef9e2b2;       (* arm_PMULL_VEC Q18 Q21 Q25 64 *)
  0x1400005f;       (* arm_B (word 380) *)
  0x3dc000d8;       (* arm_LDR Q24 X6 (Immediate_Offset (word 0)) *)
  0xfd4008d9;       (* arm_LDR D25 X6 (Immediate_Offset (word 16)) *)
  0x6e104215;       (* arm_EXT Q21 Q16 Q16 64 *)
  0x2e301eb5;       (* arm_EOR_VEC Q21 Q21 Q16 64 *)
  0x4ef8e211;       (* arm_PMULL2_VEC Q17 Q16 Q24 64 *)
  0x0ef8e213;       (* arm_PMULL_VEC Q19 Q16 Q24 64 *)
  0x0ef9e2b2;       (* arm_PMULL_VEC Q18 Q21 Q25 64 *)
  0x14000082;       (* arm_B (word 520) *)
  0x3cc1041a;       (* arm_LDR Q26 X0 (Postimmediate_Offset (word 16)) *)
  0x6e200ba0;       (* arm_REV32_VEC Q0 Q29 8 *)
  0x4ebf87bd;       (* arm_ADD_VEC Q29 Q29 Q31 32 128 *)
  0x4e284820;       (* arm_AESE Q0 Q1 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x3dc014d8;       (* arm_LDR Q24 X6 (Immediate_Offset (word 80)) *)
  0xfd4024d9;       (* arm_LDR D25 X6 (Immediate_Offset (word 72)) *)
  0x4e200b54;       (* arm_REV64_VEC Q20 Q26 8 *)
  0x6e144295;       (* arm_EXT Q21 Q20 Q20 64 *)
  0x4e284840;       (* arm_AESE Q0 Q2 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284860;       (* arm_AESE Q0 Q3 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284880;       (* arm_AESE Q0 Q4 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e2848a0;       (* arm_AESE Q0 Q5 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x2e341eb5;       (* arm_EOR_VEC Q21 Q21 Q20 64 *)
  0x4ef8e296;       (* arm_PMULL2_VEC Q22 Q20 Q24 64 *)
  0x0ef8e297;       (* arm_PMULL_VEC Q23 Q20 Q24 64 *)
  0x0ef9e2be;       (* arm_PMULL_VEC Q30 Q21 Q25 64 *)
  0x4e2848c0;       (* arm_AESE Q0 Q6 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e2848e0;       (* arm_AESE Q0 Q7 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284900;       (* arm_AESE Q0 Q8 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284920;       (* arm_AESE Q0 Q9 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284940;       (* arm_AESE Q0 Q10 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x6e361e31;       (* arm_EOR_VEC Q17 Q17 Q22 128 *)
  0x6e371e73;       (* arm_EOR_VEC Q19 Q19 Q23 128 *)
  0x6e3e1e52;       (* arm_EOR_VEC Q18 Q18 Q30 128 *)
  0x4e284960;       (* arm_AESE Q0 Q11 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284980;       (* arm_AESE Q0 Q12 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e2849a0;       (* arm_AESE Q0 Q13 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e2849c0;       (* arm_AESE Q0 Q14 *)
  0xce003f40;       (* arm_EOR3 Q0 Q26 Q0 Q15 *)
  0x3c810440;       (* arm_STR Q0 X2 (Postimmediate_Offset (word 16)) *)
  0x3cc1041a;       (* arm_LDR Q26 X0 (Postimmediate_Offset (word 16)) *)
  0x6e200ba0;       (* arm_REV32_VEC Q0 Q29 8 *)
  0x4ebf87bd;       (* arm_ADD_VEC Q29 Q29 Q31 32 128 *)
  0x4e284820;       (* arm_AESE Q0 Q1 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x3dc00cd8;       (* arm_LDR Q24 X6 (Immediate_Offset (word 48)) *)
  0xfd4020d9;       (* arm_LDR D25 X6 (Immediate_Offset (word 64)) *)
  0x4e200b54;       (* arm_REV64_VEC Q20 Q26 8 *)
  0x6e144295;       (* arm_EXT Q21 Q20 Q20 64 *)
  0x4e284840;       (* arm_AESE Q0 Q2 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284860;       (* arm_AESE Q0 Q3 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284880;       (* arm_AESE Q0 Q4 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e2848a0;       (* arm_AESE Q0 Q5 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x2e341eb5;       (* arm_EOR_VEC Q21 Q21 Q20 64 *)
  0x4ef8e296;       (* arm_PMULL2_VEC Q22 Q20 Q24 64 *)
  0x0ef8e297;       (* arm_PMULL_VEC Q23 Q20 Q24 64 *)
  0x0ef9e2be;       (* arm_PMULL_VEC Q30 Q21 Q25 64 *)
  0x4e2848c0;       (* arm_AESE Q0 Q6 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e2848e0;       (* arm_AESE Q0 Q7 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284900;       (* arm_AESE Q0 Q8 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284920;       (* arm_AESE Q0 Q9 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284940;       (* arm_AESE Q0 Q10 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x6e361e31;       (* arm_EOR_VEC Q17 Q17 Q22 128 *)
  0x6e371e73;       (* arm_EOR_VEC Q19 Q19 Q23 128 *)
  0x6e3e1e52;       (* arm_EOR_VEC Q18 Q18 Q30 128 *)
  0x4e284960;       (* arm_AESE Q0 Q11 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284980;       (* arm_AESE Q0 Q12 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e2849a0;       (* arm_AESE Q0 Q13 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e2849c0;       (* arm_AESE Q0 Q14 *)
  0xce003f40;       (* arm_EOR3 Q0 Q26 Q0 Q15 *)
  0x3c810440;       (* arm_STR Q0 X2 (Postimmediate_Offset (word 16)) *)
  0x3cc1041a;       (* arm_LDR Q26 X0 (Postimmediate_Offset (word 16)) *)
  0x6e200ba0;       (* arm_REV32_VEC Q0 Q29 8 *)
  0x4ebf87bd;       (* arm_ADD_VEC Q29 Q29 Q31 32 128 *)
  0x4e284820;       (* arm_AESE Q0 Q1 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x3dc008d8;       (* arm_LDR Q24 X6 (Immediate_Offset (word 32)) *)
  0xfd400cd9;       (* arm_LDR D25 X6 (Immediate_Offset (word 24)) *)
  0x4e200b54;       (* arm_REV64_VEC Q20 Q26 8 *)
  0x6e144295;       (* arm_EXT Q21 Q20 Q20 64 *)
  0x4e284840;       (* arm_AESE Q0 Q2 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284860;       (* arm_AESE Q0 Q3 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284880;       (* arm_AESE Q0 Q4 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e2848a0;       (* arm_AESE Q0 Q5 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x2e341eb5;       (* arm_EOR_VEC Q21 Q21 Q20 64 *)
  0x4ef8e296;       (* arm_PMULL2_VEC Q22 Q20 Q24 64 *)
  0x0ef8e297;       (* arm_PMULL_VEC Q23 Q20 Q24 64 *)
  0x0ef9e2be;       (* arm_PMULL_VEC Q30 Q21 Q25 64 *)
  0x4e2848c0;       (* arm_AESE Q0 Q6 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e2848e0;       (* arm_AESE Q0 Q7 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284900;       (* arm_AESE Q0 Q8 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284920;       (* arm_AESE Q0 Q9 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284940;       (* arm_AESE Q0 Q10 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x6e361e31;       (* arm_EOR_VEC Q17 Q17 Q22 128 *)
  0x6e371e73;       (* arm_EOR_VEC Q19 Q19 Q23 128 *)
  0x6e3e1e52;       (* arm_EOR_VEC Q18 Q18 Q30 128 *)
  0x4e284960;       (* arm_AESE Q0 Q11 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284980;       (* arm_AESE Q0 Q12 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e2849a0;       (* arm_AESE Q0 Q13 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e2849c0;       (* arm_AESE Q0 Q14 *)
  0xce003f40;       (* arm_EOR3 Q0 Q26 Q0 Q15 *)
  0x3c810440;       (* arm_STR Q0 X2 (Postimmediate_Offset (word 16)) *)
  0x3cc1041a;       (* arm_LDR Q26 X0 (Postimmediate_Offset (word 16)) *)
  0x6e200ba0;       (* arm_REV32_VEC Q0 Q29 8 *)
  0x4ebf87bd;       (* arm_ADD_VEC Q29 Q29 Q31 32 128 *)
  0x4e284820;       (* arm_AESE Q0 Q1 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x3dc000d8;       (* arm_LDR Q24 X6 (Immediate_Offset (word 0)) *)
  0xfd4008d9;       (* arm_LDR D25 X6 (Immediate_Offset (word 16)) *)
  0x4e200b54;       (* arm_REV64_VEC Q20 Q26 8 *)
  0x6e144295;       (* arm_EXT Q21 Q20 Q20 64 *)
  0x4e284840;       (* arm_AESE Q0 Q2 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x2e341eb5;       (* arm_EOR_VEC Q21 Q21 Q20 64 *)
  0x4ef8e296;       (* arm_PMULL2_VEC Q22 Q20 Q24 64 *)
  0x0ef8e297;       (* arm_PMULL_VEC Q23 Q20 Q24 64 *)
  0x0ef9e2be;       (* arm_PMULL_VEC Q30 Q21 Q25 64 *)
  0x4e284860;       (* arm_AESE Q0 Q3 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e284880;       (* arm_AESE Q0 Q4 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x6e361e31;       (* arm_EOR_VEC Q17 Q17 Q22 128 *)
  0x6e371e73;       (* arm_EOR_VEC Q19 Q19 Q23 128 *)
  0x6e3e1e52;       (* arm_EOR_VEC Q18 Q18 Q30 128 *)
  0x4e2848a0;       (* arm_AESE Q0 Q5 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4e2848c0;       (* arm_AESE Q0 Q6 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0xfd400150;       (* arm_LDR D16 X10 (Immediate_Offset (word 0)) *)
  0x0ef0e236;       (* arm_PMULL_VEC Q22 Q17 Q16 64 *)
  0x4e2848e0;       (* arm_AESE Q0 Q7 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x6e331e37;       (* arm_EOR_VEC Q23 Q17 Q19 128 *)
  0x6e114231;       (* arm_EXT Q17 Q17 Q17 64 *)
  0x4e284900;       (* arm_AESE Q0 Q8 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x6e371e52;       (* arm_EOR_VEC Q18 Q18 Q23 128 *)
  0x6e361e36;       (* arm_EOR_VEC Q22 Q17 Q22 128 *)
  0x4e284920;       (* arm_AESE Q0 Q9 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x6e361e52;       (* arm_EOR_VEC Q18 Q18 Q22 128 *)
  0x0ef0e251;       (* arm_PMULL_VEC Q17 Q18 Q16 64 *)
  0x4e284940;       (* arm_AESE Q0 Q10 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x6e124252;       (* arm_EXT Q18 Q18 Q18 64 *)
  0x4e284960;       (* arm_AESE Q0 Q11 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x6e311e73;       (* arm_EOR_VEC Q19 Q19 Q17 128 *)
  0x6e321e73;       (* arm_EOR_VEC Q19 Q19 Q18 128 *)
  0x4e284980;       (* arm_AESE Q0 Q12 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x6e134273;       (* arm_EXT Q19 Q19 Q19 64 *)
  0x4e200a73;       (* arm_REV64_VEC Q19 Q19 8 *)
  0x4e2849a0;       (* arm_AESE Q0 Q13 *)
  0x4e286800;       (* arm_AESMC Q0 Q0 *)
  0x4c007073;       (* arm_STR Q19 X3 No_Offset *)
  0x6e200bbe;       (* arm_REV32_VEC Q30 Q29 8 *)
  0x4e2849c0;       (* arm_AESE Q0 Q14 *)
  0x3d80021e;       (* arm_STR Q30 X16 (Immediate_Offset (word 0)) *)
  0xce003f40;       (* arm_EOR3 Q0 Q26 Q0 Q15 *)
  0x3c810440;       (* arm_STR Q0 X2 (Postimmediate_Offset (word 16)) *)
  0x17fffea5;       (* arm_B (word 268434068) *)
  0x52800000;       (* arm_MOV W0 (rvalue (word 0)) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let AESV8_GCM_8X_DEC_256_WB_EXEC = ARM_MK_EXEC_RULE aesv8_gcm_8x_dec_256_wb_mc;;

(* `|- LENGTH aesv8_gcm_8x_dec_256_wb_mc = 4976`.  The code-region length in the
   nonoverlapping preconditions is spelled `LENGTH aesv8_gcm_8x_dec_256_wb_mc`
   (not the hardcoded 4976) so a future .text-size change needs no bookkeeping.
   But the ARM store-safety check (NONSELFMODIFYING_STATE_UPDATE_TAC ->
   ORTHOGONAL_COMPONENTS_RULE via NONOVERLAPPING_DRIVERS) does numeric arithmetic
   on that length, so each simulation init reduces it to the numeral first via
   RULE_ASSUM_TAC(REWRITE_RULE[WB_MC_LEN]).  Same idiom as aes_xts_decrypt.ml. *)
let WB_MC_LEN = fst AESV8_GCM_8X_DEC_256_WB_EXEC;;

(* ------------------------------------------------------------------------- *)
(* Shared statement/capture machinery.                                        *)
(* ------------------------------------------------------------------------- *)

(* AES256_XOR_ENCRYPT_RECONSTRUCT + aes13 (the AES128_CIPHER_RECONSTRUCT
   pattern) hoisted to the shared file so the NIST convergence layer and the
   future main-loop proof can use them without loading the wb chain. *)
needs "arm/proofs/utils/aes_gcm_reconstruct.ml";;

(* The 12-slot aws-lc htable layout as one predicate over the abstract GHASH
   input key h (slot values = the byteswapped polyval_dot towers + packed
   karatsuba mids, exactly the per-slot hypotheses of the masked-band chain).
   htable_mem_4 pattern.  EXPAND (REWRITE_TAC[htable_mem_dec] + let_CONV)
   BEFORE stepping so the htable loads resolve (fast_tail lesson). *)
let htable_mem_dec = new_definition
 `htable_mem_dec (h:int128) (ptr:int64) (s:armstate) <=>
    let hb = byteswap128 h in
    let h2 = byteswap128 (polyval_dot hb hb) in
    let h3 = byteswap128 (polyval_dot (polyval_dot hb hb) hb) in
    let h4 = byteswap128 (polyval_dot (polyval_dot (polyval_dot hb hb) hb) hb) in
    let h5 = byteswap128 (polyval_dot (polyval_dot (polyval_dot (polyval_dot hb hb) hb) hb) hb) in
    let h6 = byteswap128 (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot hb hb) hb) hb) hb) hb) in
    let h7 = byteswap128 (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot hb hb) hb) hb) hb) hb) hb) in
    let h8 = byteswap128 (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot hb hb) hb) hb) hb) hb) hb) hb) in
    read (memory :> bytes128 ptr) s = h /\
    read (memory :> bytes128 (word_add ptr (word 16))) s =
      word_join (karatsuba_mid h2) (karatsuba_mid h) /\
    read (memory :> bytes128 (word_add ptr (word 32))) s = h2 /\
    read (memory :> bytes128 (word_add ptr (word 48))) s = h3 /\
    read (memory :> bytes128 (word_add ptr (word 64))) s =
      word_join (karatsuba_mid h4) (karatsuba_mid h3) /\
    read (memory :> bytes128 (word_add ptr (word 80))) s = h4 /\
    read (memory :> bytes128 (word_add ptr (word 96))) s = h5 /\
    read (memory :> bytes128 (word_add ptr (word 112))) s =
      word_join (karatsuba_mid h6) (karatsuba_mid h5) /\
    read (memory :> bytes128 (word_add ptr (word 128))) s = h6 /\
    read (memory :> bytes128 (word_add ptr (word 144))) s = h7 /\
    read (memory :> bytes128 (word_add ptr (word 160))) s =
      word_join (karatsuba_mid h8) (karatsuba_mid h7) /\
    read (memory :> bytes128 (word_add ptr (word 176))) s = h8`;;

(* ------------------------------------------------------------------------- *)
(* Guard-abort theorem: the whole-blocks contract is enforced.  For nonzero    *)
(* bit_len not a multiple of 128 the function returns 0 via the entry guard    *)
(* (cbz/tst/b.ne -> mov w0,#0; ret), modifying no memory and no callee-saved   *)
(* state (the guard fires before the d8-d15 saves).                            *)
(* ------------------------------------------------------------------------- *)

let AESV8_GCM_8X_DEC_256_GUARD = prove
 (`!pc in_p bit_len out_p xi_p ivec_p key_p htbl_p returnaddress.
    ~(val bit_len = 0) /\ ~(val bit_len MOD 128 = 0)
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) aesv8_gcm_8x_dec_256_wb_mc /\
           read PC s = word pc /\
           read X30 s = returnaddress /\
           C_ARGUMENTS [in_p; bit_len; out_p; xi_p; ivec_p; key_p; htbl_p] s)
      (\s. read PC s = returnaddress /\
           C_RETURN s = word 0)
      MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  ENSURES_INIT_TAC "s0" THEN RULE_ASSUM_TAC(REWRITE_RULE[C_ARGUMENTS]) THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (1--2) THEN
  SUBGOAL_THEN `~(val (word_and (bit_len:int64) (word 127)) = 0)` ASSUME_TAC THENL
   [SUBGOAL_THEN `127 = 2 EXP 7 - 1` SUBST1_TAC THENL
     [CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
    REWRITE_TAC[VAL_WORD_AND_MASK_WORD] THEN
    ASM_REWRITE_TAC[ARITH_RULE `2 EXP 7 = 128`]; ALL_TAC] THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (3--6) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Shared band machinery (KEEPGH stepper + the Q19 byte-reversed-xi identity).*)
(* ------------------------------------------------------------------------- *)

(* ins->ext runtime opt (2026-08-11): the GHASH-tail Karatsuba mids now use
   `ext vD.16b,vN.16b,vN.16b,#8` in place of `ins vD.d[0],vN.d[1]` (a false-dep
   break; both consumed lane-0-only, values identical).  The stepper models
   `ext vD,vN,vN,#8` on a 128-bit register as
   `word_subword (word_join vN vN:256 word) (64,128):128 word` (a rot-by-64).
   The syntactic-form fix lives ONCE in the per-step normalizer
   GCM_SIMD_SIMPLIFY_CORE_TAC (aesv8_gcm_8x_dec_256_lemmas.ml): the lemma
   EXT8_LANE0_IS_SUBWORD_HI collapses the COMPOSED lane-0 projection
   `word_subword (<ext form>) (0,64)` (the only way any of the 9 sites consumes
   the ext register — via eor .8b / pmull .1d) back to `word_subword vN (64,64)`,
   exactly the plain lane the old `ins` form produced.  So every tail bridge sees
   pre-opt-identical operand shapes and ABBREV_INNER_PMULS's qq-numbering is
   preserved.  (This supersedes EXT_JOIN_NORM, which rewrote the whole
   ext REGISTER to a join-of-lanes form and thereby false-fired on the byteswap/
   REV64 register shape, regressing the 2-block band.)  AUTO_MERGE_MIDS_KM_TAC
   below is kept as a numbering-agnostic safety net for the N>=3 mid pairing. *)

(* KEEPGH stepper (copied from le8block.ml; the <=8-block chain does not load le8block) *)
let DISCARD_OLDSTATE_KEEPGH_TAC s =
  let v = mk_var(s,`:armstate`) in
  let rec unbound_statevars_of_read bound tm = match tm with
      Comb(Comb(Const("read",_),_),st) -> if mem st bound then [] else [st]
    | Comb(a,b) -> union (unbound_statevars_of_read bound a) (unbound_statevars_of_read bound b)
    | Abs(vv,t) -> unbound_statevars_of_read (vv::bound) t | _ -> [] in
  let rec mentions_ghreg t = match t with
      Comb(Comb(Const("read",_),cmp),_) ->
        (match cmp with Const(n,_) -> n="Q16"||n="Q17"||n="Q18"||n="Q19" | _ -> false)
    | Comb(a,b) -> mentions_ghreg a || mentions_ghreg b | Abs(_,t2) -> mentions_ghreg t2 | _ -> false in
  DISCARD_ASSUMPTIONS_TAC(fun thm ->
    if mentions_ghreg (concl thm) then false else
    let us = unbound_statevars_of_read [] (concl thm) in
    if us = [] || us = [v] then false else if not(mem v us) then true else true);;
(* refine-100: Q-scoped, FIXPOINT-MEMOIZED single-pass per-step normalizer for the tails'
   GHASH multiply/reduce stepper.  Two composed levers, both untried on this stepper before:
     (a) SINGLE-pass (GCM_SIMD_SIMPLIFY_CORE_TAC, one pass) rather than the double-pass
         GCM_SIMD_SIMPLIFY_TAC — the s084 lever (which single-passed the SIBLING
         ARM_STEPS_FOLD_Q18LATEST_TAC); pass2 changes the pile on only 2/40 KEEPGH steps in
         k=2 (block-boundary REV64 folds, re-done downstream by the Q19 bridge).
     (b) Q-SCOPE + fixpoint-MEMOIZE the pass — the s097/s099 levers.  The KEEPGH windows keep
         Q16-Q19 across ~7-40 steps; the per-step normalizer's rules can ONLY fire on
         `read Qn s = <tower>`, and re-fold Q-reads already at a fixpoint.  gcm_simd_kgh_tbl
         memoizes proven fixpoints; is_qreg_read guards the O(1) head before the rewrites.
   BIT-IDENTICAL to the full double-pass GCM_SIMD_SIMPLIFY_CORE_TAC applied per-asm: MEASURED
   0 mismatches / 40 KEEPGH steps in k=2 (pile compared by-position vs the full _CORE_TAC),
   and skipping a proven fixpoint yields exactly F's output BY CONSTRUCTION.  Cache reset per
   tail body via CLEAR_KEEPGH_MEMO_TAC in WB_PREP_TAC (each WB_TAIL_GEN2_k `prove` hermetic).
   Sole consumers = the 8 WB_TAIL_{1..8}_TAC (grep); the le8block.ml copy is a separate file.
   Measured warm twice: family 806s -> 763s (single-pass, -43s/-5.4%) -> 734s (+memo, -30s/-3.9%
   incremental); all 8 tails hyps=0. *)
let gcm_simd_kgh_tbl : (term,unit) Hashtbl.t = Hashtbl.create 4096;;
let CLEAR_KEEPGH_MEMO_TAC : tactic =
  fun (asl,w) -> Hashtbl.clear gcm_simd_kgh_tbl; ALL_TAC (asl,w);;
let GCM_SIMD_SIMPLIFY_KGH_TAC =
  let is_qreg_read c = match c with
    | Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),cmp),_)),_) ->
        (match cmp with Const(rn,_) ->
           String.length rn >= 2 && rn.[0]='Q' && rn.[1]>='0' && rn.[1]<='9'
         | _ -> false)
    | _ -> false in
  let apply_F th =
    let th1 = (try REWRITE_RULE SIMD_SIMPLIFY_RULES th with _ -> th) in
    let th2 = REWRITE_RULE [WORD_SWAP_HALVES_INVOLUTION; EXT8_LANE0_IS_SUBWORD_HI] th1 in
    (try CONV_RULE(RAND_CONV(REV32_LANE_SUBWORD_CONV)) th2 with _ -> th2) in
  RULE_ASSUM_TAC(fun th ->
    let c = concl th in
    if not(is_qreg_read c) then th
    else if Hashtbl.mem gcm_simd_kgh_tbl c then th
    else let th' = apply_F th in
         (if concl th' = c then Hashtbl.add gcm_simd_kgh_tbl c ());
         th');;
let ARM_STEPS_FOLD_KEEPGH_TAC exec snums =
  MAP_EVERY (fun s -> ARM_VERBOSE_STEP_TAC exec s THEN GCM_SIMD_SIMPLIFY_KGH_TAC THEN
              DISCARD_OLDSTATE_KEEPGH_TAC s THEN CLARIFY_TAC) (statenames "s" snums);;

(* The byte-reversed-xi identity: the machine's ldr/ext/rev64 (steps ~180-189)
   leave Q19 in word_join(reversefields lo)(reversefields hi) form; this equals
   word_bytereverse of the whole 128-bit xi.  Rewriting Q19 to this clean atom
   right after step 189 is what lets the tail's GHASH accumulator close against
   the postcondition's word_bytereverse xi. *)
let Q19_BREVXI = prove
 (`word_join (word_reversefields 8 (word_subword (xi:int128) (0,64):int64))
             (word_reversefields 8 (word_subword xi (64,64):int64)):int128 =
   word_bytereverse xi`,
  CONV_TAC WORD_BLAST);;

(* ------------------------------------------------------------------------- *)
(* AESV8_GCM_8X_DEC_256_1BLOCK: the whole-blocks dec variant, bit_len=128. *)
(* ------------------------------------------------------------------------- *)


(* ------------------------------------------------------------------------- *)
(*     Shared inter-band machinery (bridge closers, spec folds, steppers)    *)
(* ------------------------------------------------------------------------- *)



(* ------------------------------------------------------------------------- *)
(* The WB 2-block bridge close: DEC_2BLK_GMULT2_BRIDGE_TAC (core.ml) with
   karatsuba_mid unfolded first (htable_mem_dec presents the hk slot as
   word_join (karatsuba_mid h2) (karatsuba_mid h); the merge needs the
   expanded subword form to pair machine mids with spec mids). *)
let WB2_GMULT2_BRIDGE_TAC : tactic =
  let a0t = `word_xor (word_bytereverse xi) (word_bytereverse cph0):int128`
  and a1t = `word_bytereverse cph1:int128` in
  let gmult2_dec = REWRITE_RULE[LET_DEF;LET_END_DEF]
    (SPECL [a0t; `byteswap128 h2:int128`; a1t; `byteswap128 h:int128`] GMULT2_FULL_CORRECT_BA) in
  let r1def = `word_xor (word_xor (word_shl (word_zx (wal:64 word):128 word) 63) (word_shl (word_zx wal:128 word) 62)) (word_shl (word_zx wal:128 word) 57)` in
  let udef = `word_xor (word_subword (r1:128 word) (0,64):64 word) (word_xor (word_xor qq1h qq6h) (word_xor (word_xor qq0l (word_xor qq1l qq4l)) (word_xor qq5l (word_xor qq10l qq6l))))` in
  FIRST_ASSUM(fun th ->
    if (try lhs(concl th)=`byteswap128 h2` with _->false)
    then GEN_REWRITE_TAC RAND_CONV
           [REWRITE_RULE[GSYM gmult2_dec]
             (GEN_REWRITE_RULE (RAND_CONV o ONCE_DEPTH_CONV) [GSYM th]
               (SPECL [`byteswap128 h:int128`; `word_bytereverse xi:int128`;
                       `word_bytereverse cph0:int128`; `word_bytereverse cph1:int128`]
                 GHASH_POLYVAL_ACC_2))]
    else NO_TAC) THEN
  REWRITE_TAC[WORD_XOR_0; WORD_XOR_0_LEFT] THEN
  REWRITE_TAC[byteswap128] THEN
  REWRITE_TAC[WORD_BYTEREVERSE_REVERSEFIELDS] THEN
  REWRITE_TAC[WORD_INSERT_SUBWORD; WORD_SUBWORD_SUBWORD] THEN
  REWRITE_TAC[SUBWORD_XOR_JOIN_DIST] THEN
  REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES; RF8_SUBWORD] THEN
  REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES] THEN
  REWRITE_TAC[karatsuba_mid] THEN
  ABBREV_INNER_PMULS_TAC THEN MERGE_2BLK_TAC THEN
  REWRITE_TAC[PMUL_W_64_128] THEN REWRITE_TAC[JOINMID] THEN
  REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES; WORD_SUBWORD_XOR] THEN
  EVERY (map (fun a ->
    let av = mk_var(a,`:int128`) in
    ABBREV_TAC (mk_eq(mk_var(a^"l",`:64 word`), mk_comb(mk_comb(`word_subword:int128->num#num->64 word`, av), `(0,64)`))) THEN
    ABBREV_TAC (mk_eq(mk_var(a^"h",`:64 word`), mk_comb(mk_comb(`word_subword:int128->num#num->64 word`, av), `(64,64)`))))
    ["qq0";"qq1";"qq4";"qq5";"qq6";"qq10"]) THEN
  ABBREV_TAC `wal:64 word = word_xor qq1l qq6l` THEN
  REWRITE_TAC[DEC2_WXSYM] THEN
  FIRST_ASSUM(fun th -> if (try rhs(concl th)=`wal:64 word` && lhs(concl th)=`word_xor qq1l qq6l:64 word` with _->false) then REWRITE_TAC[th] else NO_TAC) THEN
  ABBREV_TAC (mk_eq(`r1:128 word`, r1def)) THEN
  SUBGOAL_THEN
   `word_xor (word_xor (word_subword (word_shl (word_zx (wal:64 word):128 word) 63) (0,64):64 word) (word_subword (word_shl (word_zx wal:128 word) 62) (0,64):64 word)) (word_subword (word_shl (word_zx wal:128 word) 57) (0,64):64 word) = word_subword (r1:128 word) (0,64):64 word`
   (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "r1" THEN CONV_TAC WORD_BLAST; ALL_TAC] THEN
  SUBGOAL_THEN
   `word_xor (word_xor (word_subword (word_shl (word_zx (wal:64 word):128 word) 63) (64,64):64 word) (word_subword (word_shl (word_zx wal:128 word) 62) (64,64):64 word)) (word_subword (word_shl (word_zx wal:128 word) 57) (64,64):64 word) = word_subword (r1:128 word) (64,64):64 word`
   (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "r1" THEN CONV_TAC WORD_BLAST; ALL_TAC] THEN
  SUBGOAL_THEN
   `word_xor (word_subword (word_shl (word_zx (wal:64 word):128 word) 57) (0,64):64 word) (word_xor (word_subword (word_shl (word_zx wal:128 word) 62) (0,64):64 word) (word_subword (word_shl (word_zx wal:128 word) 63) (0,64):64 word)) = word_subword (r1:128 word) (0,64):64 word`
   (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "r1" THEN CONV_TAC WORD_BLAST; ALL_TAC] THEN
  SUBGOAL_THEN
   `word_xor (word_subword (word_shl (word_zx (wal:64 word):128 word) 57) (64,64):64 word) (word_xor (word_subword (word_shl (word_zx wal:128 word) 62) (64,64):64 word) (word_subword (word_shl (word_zx wal:128 word) 63) (64,64):64 word)) = word_subword (r1:128 word) (64,64):64 word`
   (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "r1" THEN CONV_TAC WORD_BLAST; ALL_TAC] THEN
  ABBREV_TAC (mk_eq(`u:64 word`, udef)) THEN
  SUBGOAL_THEN
   `word_xor (word_xor (word_xor qq10l qq4l) (word_xor wal (word_xor qq0l qq5l))) (word_xor (word_xor qq1h qq6h) (word_subword (r1:128 word) (0,64):64 word)) = u`
   (fun th -> REWRITE_TAC[th]) THENL [MAP_EVERY EXPAND_TAC ["u";"wal"] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  SUBGOAL_THEN
   `word_xor (word_subword (r1:128 word) (0,64):64 word) (word_xor (word_xor qq1h qq6h) (word_xor (word_xor qq0l (word_xor qq1l qq4l)) (word_xor qq5l (word_xor qq10l qq6l)))) = u`
   (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "u" THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  ABBREV_TAC `us57:128 word = word_shl (word_zx (u:64 word):128 word) 57` THEN
  ABBREV_TAC `us62:128 word = word_shl (word_zx (u:64 word):128 word) 62` THEN
  ABBREV_TAC `us63:128 word = word_shl (word_zx (u:64 word):128 word) 63` THEN
  GEN_REWRITE_TAC ONCE_DEPTH_CONV [QQ0SPLIT] THEN
  REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES; WORD_SUBWORD_XOR] THEN
  REWRITE_TAC[JOIN_EQ_SPLIT] THEN CONJ_TAC THEN LANE_CLOSE_TAC;;

(* ------------------------------------------------------------------------- *)
(* AESV8_GCM_8X_DEC_256_2BLOCK: whole-blocks dec variant, bit_len=256.     *)
(* ------------------------------------------------------------------------- *)



(* ========================================================================= *)
(* WB_3BLOCK .. WB_8BLOCK: whole-blocks dec variant, bit_len = 128*N (N=3..8).*)
(* hyps=0, axioms=3, no cheats.                                               *)
(* Shared N>=3 band machinery (ported from le3block.ml) precedes the theorems.*)
(* ========================================================================= *)

(* ============================================================================
   WB_3BLOCK: PROVED interactively (hyps=0, axioms=3).  Full script below.

   CASCADE STEP MAP (from the b.gt chain disassembly; band N takes the
   #16*(N-1) branch; cascade always starts ARM_STEPS_RESOLVE_TAC (266--277)
   then (278--sEnd)):
     N=2: sEnd=313 -> pc+4348 (R1)   N=3: sEnd=309 -> pc+4288 (R2)
     N=4: sEnd=303 -> pc+4220 (R3)   N=5: sEnd=297 -> pc+4164 (R4)
     N=6: sEnd=290 -> pc+4104 (R5)   N=7: sEnd=282 -> pc+4048 (R6)
     N=8: sEnd=270 -> pc+4000 (R7)
   Front keystream discard lists: keep Q0..Q(N-1):
     per-step 6..30:  mk_discard2 [N..7]        (N=8: [])
     bulk windows:    mk_discard2 [N..7]@[30]   (N=8: [30])
     after 256-265:   mk_discard2 [N..7 minus the moved one]@[30] — for N=2 it
     was [2;3;4;5;6;30]; for N=3 [3;4;5;6;30]; pattern: drop 7 keep 30.
   Block-i keystream after cascade movs: block-0 in Q0, block-(N-1) in Q7,
   block-i (0<i<N-1) in Q(8-N+i).
   WB_3BLOCK tail map (entry s309=pc+4288 R2):
     310-315 KEEPGH; Q12 s315 = block-0 PT (reconstruct+WORD_RULE).
     s316 = str q12 (VSTEPS_FOLD ok here) + carry out_p readback + KEEPGH-discard.
     317-330 KEEPGH (317 = eor3 block-1 vs Q6); Q12 s330 capture via
       GCM_CTR_INC_LANES (do the capture at s330, right before its store).
     s331 = str block-1 (VSTEPS_FOLD ok) + carry out_p AND out_p+16 + discard.
     332-336 KEEPGH (336 = eor3 block-2 vs Q7); Q12 s336 capture via
       GCM_CTR_INC2_LANES.
     337-358 KEEPGH -> s358 pc+4484.
     s359 = str block-2 (PLAIN ARM_VSTEPS_TAC — FOLD chokes) + carry all 3
       out_p readbacks + KEEPGH-discard + 3x DISCH.
     360-366 KEEPGH -> s366 pc+4516 = BRIDGE (post eor v19,v19,v18).
     BRIDGE: SUBGOAL read Q19 s366 = ghash_polyval_acc .. [brev cph0;cph1;cph2],
       close = spec fold (spec_to_byteform_wb3 h2asm h3asm + GSYM gmult3_dec)
       THEN the WB2-style rewrites incl. REWRITE_TAC[karatsuba_mid] THEN
       ABBREV_INNER_PMULS_TAC THEN MERGE_2BLK_TAC THEN QQ8_FOLD_TAC THEN
       WA_UNIFY_TAC THEN WV_UNIFY_TAC THEN ABBREV_WAWV_TAC THEN
       subword/QQ0SPLIT/JOIN_EQ_SPLIT THEN CONJ_TAC THEN LANE_FINISH_TAC.
       (NO FOLD_MID_HPOW needed at N=3: QQ8_FOLD grabs the one H2-keyed mid;
       the H3-keyed karatsuba_mid h3 mid merged already because karatsuba_mid
       was unfolded.  For N>=4 expect FOLD_MID_HPOW "H<k>" for k=N-1..2 as in
       le4-8, called BETWEEN MERGE and WA_UNIFY.)
     367-368 ext/rev64 + Q19 s368 = brev gval (WORD_BLAST); 369 tag store
       (plain VSTEPS); DISCARD_COUNTER_ONLY; FINAL + MAYCHANGE as WB_2BLOCK.
   ============================================================================ *)

(* ---- shared N>=3 band machinery (ported from le3block.ml; wb chain does
   not load the le bands) ---- *)
let collect_pmuls p t = let rec collect t acc = let acc = if p t then t::acc else acc in
  match t with Comb(a,b)->collect a (collect b acc)|Abs(_,b)->collect b acc|_->acc in setify(collect t []);;
let isWpmul t = try fst(dest_const(repeat rator t))="word_pmul" && rand t=`word 13979173243358019584:64 word` with _->false;;
let SJ_COLLAPSE = prove
 (`!w:128 word. word_subword (word_subword (word_join w w:256 word) (64,128):128 word) (0,64):64 word
                = word_subword w (64,64)`,
  GEN_TAC THEN CONV_TAC WORD_BLAST);;
let SJ_COLLAPSE2 = prove
 (`!w:128 word. word_subword (word_subword (word_join w w:256 word) (64,128):128 word) (64,64):64 word
                = word_subword w (0,64)`,
  GEN_TAC THEN CONV_TAC WORD_BLAST);;
let word_xor_left_comm = WORD_RULE `word_xor (a:64 word) (word_xor b c) = word_xor b (word_xor a c)`;;
let xor_pair_comm = WORD_RULE `word_xor (a:64 word) b = word_xor b a`;;
let term_leq t1 t2 = String.compare (string_of_term t1) (string_of_term t2) <= 0;;
let rec bubble_conv tm = match tm with
  | Comb(Comb(Const("word_xor",_), a), b) ->
    (match b with
     | Comb(Comb(Const("word_xor",_), b1), _) ->
       if term_leq a b1 then AP_TERM (mk_comb(rator(rator tm), a)) (bubble_conv b)
       else let th1 = PART_MATCH lhs word_xor_left_comm tm in
         let new_rhs = rhs(concl th1) in TRANS th1 (AP_TERM (rator new_rhs) (bubble_conv (rand new_rhs)))
     | _ -> if term_leq a b then REFL tm else PART_MATCH lhs xor_pair_comm tm)
  | _ -> REFL tm;;
let rec bubble_sort_conv tm =
  let rec count_xors t = match t with Comb(Comb(Const("word_xor",_), _), r) -> 1 + count_xors r | _ -> 0 in
  let n = count_xors tm in
  let rec apply_n_times k acc = if k <= 0 then acc else apply_n_times (k-1) (TRANS acc (bubble_conv (rhs(concl acc)))) in
  apply_n_times n (REFL tm);;
let rec bubble_fix tm = let th = bubble_sort_conv tm in let r = rhs(concl th) in
  if r = tm then th else TRANS th (bubble_fix r);;
let LANE_FINISH_TAC : tactic =
  CONV_TAC(LAND_CONV(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
  CONV_TAC(RAND_CONV(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
  REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES; WORD_SUBWORD_XOR] THEN
  REWRITE_TAC[SJ_COLLAPSE; SJ_COLLAPSE2] THEN REWRITE_TAC[WORD_SUBWORD_XOR] THEN
  CONV_TAC(BINOP_CONV bubble_fix) THEN REFL_TAC;;
let WA_UNIFY_TAC : tactic = fun (asl,w) ->
  let l=lhs w and r=rhs w in
  let iswa t = isWpmul t && not(can (find_term (fun u->u<>t && isWpmul u)) (rand(rator t))) in
  let lwa=hd(collect_pmuls iswa l) and rwa=hd(collect_pmuls iswa r) in
  if lwa=rwa then ALL_TAC (asl,w) else
  let wa_eq = prove(mk_eq(rwa,lwa), MATCH_MP_TAC PMUL_CONG_128 THEN CONJ_TAC THEN CONV_TAC WORD_RULE) in
  GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [wa_eq] (asl,w);;
let WV_UNIFY_TAC : tactic = fun (asl,w) ->
  let l=lhs w and r=rhs w in
  let iswv t = isWpmul t && (can (find_term (fun u->u<>t && isWpmul u)) (rand(rator t))) in
  let lwv=hd(collect_pmuls iswv l) and rwv=hd(collect_pmuls iswv r) in
  if lwv=rwv then ALL_TAC (asl,w) else
  let in_eq = BITBLAST_RULE (mk_eq(rand(rator rwv), rand(rator lwv))) in
  let wv_eq = AP_THM (AP_TERM `word_pmul:64 word->64 word->128 word` in_eq) `word 13979173243358019584:64 word` in
  GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [wv_eq] (asl,w);;
let ABBREV_WAWV_TAC : tactic = fun (asl,w) ->
  let l=lhs w in
  let iswa t = isWpmul t && not(can (find_term (fun u->u<>t && isWpmul u)) (rand(rator t))) in
  let lwa=hd(collect_pmuls iswa l) in
  (ABBREV_TAC (mk_eq(`WAz:128 word`, lwa)) THEN
   (fun (asl,w) -> let l=lhs w in
     (match collect_pmuls isWpmul l with wv::_ -> ABBREV_TAC (mk_eq(`WVz:128 word`, wv)) | [] -> ALL_TAC) (asl,w)))
  (asl,w);;
let pmul_mult_hpow t =
  let m = rand t in
  if can(find_term(fun u->u=`h2:int128`)) m then "H2" else
  if can(find_term(fun u->u=`h3:int128`)) m then "H3" else
  if can(find_term(fun u->u=`h4:int128`)) m then "H4" else
  if can(find_term(fun u->u=`h5:int128`)) m then "H5" else
  if can(find_term(fun u->u=`h6:int128`)) m then "H6" else
  if can(find_term(fun u->u=`h7:int128`)) m then "H7" else
  if can(find_term(fun u->u=`h8:int128`)) m then "H8" else
  if can(find_term(fun u->u=`h:int128`)) m then "H1" else
  if can(find_term(fun u->u=`word 13979173243358019584:64 word`)) m then "W" else "?";;
let is_pmul128_tm t = try fst(dest_const(repeat rator t))="word_pmul" && type_of t = `:128 word` with _->false;;
let WB_MID_FIX = [WORD_SUBWORD_INSERT_INNER; WORD_SUBWORD_INSERT_OUTER; INSERT_SUBWORD_KILL;
                  WORD_INSERT_SUBWORD; JOINMID; JOIN_SUBWORD_RULES; RF8_SUBWORD;
                  WORD_SUBWORD_SUBWORD; WORD_SUBWORD_XOR];;
let FOLD_MID_HPOW hp : tactic = fun (asl,w) ->
  let l = lhs w in
  let mid = hd(List.filter (fun t -> pmul_mult_hpow t = hp) (setify(find_terms is_pmul128_tm l))) in
  let cands = List.filter (fun (_,th) ->
      try let r=rhs(concl th) and lft=lhs(concl th) in
          is_var r && (let n=fst(dest_var r) in String.length n>=2 && String.sub n 0 2="qq") &&
          is_pmul128_tm lft && pmul_mult_hpow lft = hp
      with _->false) asl in
  let try_qq (_,th) =
    let qq = rhs(concl th) in
    (SUBGOAL_THEN (mk_eq(mid,qq)) (fun e->REWRITE_TAC[e]) THENL
      [GEN_REWRITE_TAC RAND_CONV [GSYM th] THEN
       MATCH_MP_TAC PMUL_CONG_128 THEN CONJ_TAC THEN
       (CONV_TAC WORD_BLAST ORELSE (REWRITE_TAC WB_MID_FIX THEN CONV_TAC WORD_BLAST)); ALL_TAC]) in
  (FIRST (map try_qq cands)) (asl,w);;
let QQ8_FOLD_TAC : tactic = fun (asl,w) ->
  let l=lhs w in
  let ishpmul t=try fst(dest_const(repeat rator t))="word_pmul" && type_of t = `:128 word`
    && rand t <> `word 13979173243358019584:64 word`
    && can (find_term(fun u->u=`h2:int128`)) t && not(can (find_term(fun u->isWpmul u)) t) with _->false in
  let qq8th = snd(List.find(fun(_,th)->let c=concl th in is_eq c && (try rhs c=`qq8:128 word` with _->false)) asl) in
  (match collect_pmuls ishpmul l with
   | gp8t::_ -> (SUBGOAL_THEN (mk_eq(gp8t, `qq8:128 word`)) (fun th -> REWRITE_TAC[th]) THENL
      [GEN_REWRITE_TAC RAND_CONV [GSYM qq8th] THEN
       ((MATCH_MP_TAC PMUL_CONG_128 THEN CONJ_TAC THEN CONV_TAC WORD_BLAST) ORELSE
        (ONCE_REWRITE_TAC[WORD_PMUL_SYM] THEN MATCH_MP_TAC PMUL_CONG_128 THEN CONJ_TAC THEN CONV_TAC WORD_BLAST)); ALL_TAC])
   | [] -> ALL_TAC) (asl,w);;
let POLYVAL_DOT_SYM = prove
 (`!a b:int128. polyval_dot a b = polyval_dot b a`,
  REPEAT GEN_TAC THEN REWRITE_TAC[polyval_dot] THEN AP_TERM_TAC THEN
  REWRITE_TAC[WORD_PMUL_SYM]);;
let GCM_CTR_INC2_LANES = prove
 (mk_eq(`gcm_ctr_inc (gcm_ctr_inc ctr0)`,
        subst [`word 2:32 word`, `word 1:32 word`]
          (rhs(snd(strip_forall(concl GCM_CTR_INC_LANES))))),
  REWRITE_TAC[gcm_ctr_inc] THEN BITBLAST_TAC);;
let PACK3_ID, GMULT3_FULL_CORRECT_BA = build_GMULTn_fast 3;;
let spec_to_byteform_wb3 = prove
 (`byteswap128 h2 = polyval_dot (byteswap128 h) (byteswap128 h) /\
   byteswap128 h3 = polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h)
   ==> ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
        [word_bytereverse cph0; word_bytereverse cph1; word_bytereverse cph2] =
       polyval_reduce_prop3
        (word_xor
         (word_xor
          (word_pmul (word_xor (word_bytereverse xi) (word_bytereverse cph0)) (byteswap128 h3))
          (word_pmul (word_bytereverse cph1) (byteswap128 h2)))
         (word_pmul (word_bytereverse cph2) (byteswap128 h)))`,
  STRIP_TAC THEN
  REWRITE_TAC[REWRITE_RULE[LET_DEF;LET_END_DEF]
    (SPECL [`byteswap128 h:int128`; `word_bytereverse xi:int128`;
            `word_bytereverse cph0:int128`; `word_bytereverse cph1:int128`;
            `word_bytereverse cph2:int128`] GHASH_POLYVAL_ACC_3)] THEN
  SUBGOAL_THEN `polyval_dot (byteswap128 h) (polyval_dot (byteswap128 h) (byteswap128 h)) = byteswap128 h3`
    (fun th -> REWRITE_TAC[th]) THENL
  [ONCE_REWRITE_TAC[POLYVAL_DOT_SYM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE);;

(* ------------------------------------------------------------------------- *)
(* AESV8_GCM_8X_DEC_256_3BLOCK: whole-blocks dec variant, bit_len=384.     *)
(* ------------------------------------------------------------------------- *)
(* ---- shared merge machinery (originally introduced for the WB_8 bridge;
   moved up 2026-07-18 because the optimized WB_3..6 closes also use
   MERGE_ANY_TAC / MERGE_QQPAIR_KM_TAC).  See the WB_8 header note for the
   greedy-pairing story. ---- *)

let MERGE_ONE_ANY_TAC : tactic = fun (asl,w) ->
  let is_pmul t = try let (hd,a)=strip_comb t in fst(dest_const hd)="word_pmul" && List.length a=2 with _->false in
  let is_wordconst t = try is_comb t && fst(dest_const(rator t))="word" && is_numeral(rand t) with _->false in
  let is_keyvar n = String.length n>=2 && n.[0]='k' &&
                    (try let _ = int_of_string (String.sub n 1 (String.length n-1)) in true with _->false) in
  let goalvars = setify(map (fun t->fst(dest_var t))
    (find_terms (fun t->is_var t && type_of t=`:int128` &&
      (let n=fst(dest_var t) in String.length n>=2 && String.sub n 0 2="qq")) w)) in
  let defs = List.filter (fun (_,th)->let c=concl th in is_eq c && is_var(rhs c) &&
    is_pmul(lhs c) && mem (fst(dest_var(rhs c))) goalvars) asl in
  let fvnames t = sort (<) (List.filter (fun n -> not(is_keyvar n))
                              (map (fun v->fst(dest_var v)) (frees t))) in
  let lane_tag op2 =
    if is_comb op2 && is_comb(rator op2) &&
       (try fst(dest_const(rator(rator op2)))="word_subword" with _->false)
    then string_of_term(rand op2) else "X" in
  let info th =
    let p = lhs(concl th) in
    let (_,args) = strip_comb p in
    let op1 = el 0 args and op2 = el 1 args in
    (rhs(concl th), op2, (fvnames op1, fvnames op2, lane_tag op2)) in
  let items = map (fun (_,th)-> info th) defs in
  let rec allpairs_acc = function
    | [] -> []
    | (v,op2,sg)::rest ->
        let cands =
          if is_wordconst op2
          then List.filter (fun (v2,op2b,_)-> v2<>v && is_wordconst op2b && op2b=op2) rest
          else List.filter (fun (v2,op2b,sg2)-> v2<>v && not(is_wordconst op2b) && sg2=sg) rest in
        (map (fun (v2,_,_) -> (v,v2)) cands) @ allpairs_acc rest in
  let pairs = allpairs_acc items in
  if pairs = [] then failwith "MERGE_ONE_ANY_TAC: nothing to merge" else
  let close_op = FAST_OPERAND_TAC ORELSE CONV_TAC WORD_BLAST in
  let cand_tac (v1,v2) =
    SUBGOAL_THEN (mk_eq(v1,v2))
      (fun th -> REWRITE_TAC[th] THEN RULE_ASSUM_TAC(REWRITE_RULE[th]))
     THENL [EXPAND_TAC(fst(dest_var v1)) THEN EXPAND_TAC(fst(dest_var v2)) THEN
            ((MATCH_MP_TAC PMUL_CONG_128 THEN CONJ_TAC THEN close_op)
             ORELSE (GEN_REWRITE_TAC LAND_CONV [WORD_PMUL_SYM] THEN
                     MATCH_MP_TAC PMUL_CONG_128 THEN CONJ_TAC THEN close_op));
            ALL_TAC] in
  FIRST (map cand_tac pairs) (asl,w);;
let MERGE_ANY_TAC : tactic = REPEAT MERGE_ONE_ANY_TAC;;
let MERGE_QQPAIR_TAC (n1:string) (n2:string) : tactic =
  SUBGOAL_THEN (mk_eq(mk_var(n1,`:128 word`), mk_var(n2,`:128 word`)))
    (fun th -> REWRITE_TAC[th] THEN RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
  [EXPAND_TAC n1 THEN EXPAND_TAC n2 THEN
   ((MATCH_MP_TAC PMUL_CONG_128 THEN CONJ_TAC THEN
     (CONV_TAC WORD_BLAST ORELSE (REWRITE_TAC WB_MID_FIX THEN CONV_TAC WORD_BLAST)))
    ORELSE (GEN_REWRITE_TAC LAND_CONV [WORD_PMUL_SYM] THEN
            MATCH_MP_TAC PMUL_CONG_128 THEN CONJ_TAC THEN
            (CONV_TAC WORD_BLAST ORELSE (REWRITE_TAC WB_MID_FIX THEN CONV_TAC WORD_BLAST))));
   ALL_TAC];;

(* ---- WB_7/WB_8 stepping-optimization machinery (2026-07-18).
   The whole-blocks stores window used ARM_STEPS_FOLD_KEEPGH_TAC throughout,
   keeping all of Q16-Q19 alive across ~130 states: the per-step
   GCM_SIMD_SIMPLIFY pass rescans a linearly growing pile => O(n^2)
   (WB_7 1573s, WB_8 the worst; repeated 30GB OOM kills).  Fix mirrors
   le8block's KEEPQ18/midacc pattern + the per-step-discard memo:
   step the window keeping ONLY the LATEST read Q18 fact (the machine's
   carried GHASH mid; store readbacks self-propagate), atomize it as
   `midacc`, and let the bridge expand it once.  271-392: hundreds of
   seconds -> ~116s; whole WB_8 tail ~26min -> ~9min. ---- *)
let DISCARD_OLDSTATE_KEEPQ18_TAC s =
  let v = mk_var(s,`:armstate`) in
  let rec unbound_statevars_of_read bound tm = match tm with
      Comb(Comb(Const("read",_),_),st) -> if mem st bound then [] else [st]
    | Comb(a,b) -> union (unbound_statevars_of_read bound a) (unbound_statevars_of_read bound b)
    | Abs(vv,t) -> unbound_statevars_of_read (vv::bound) t | _ -> [] in
  let rec mentions_q18 t = match t with
      Comb(Comb(Const("read",_),cmp),_) ->
        (match cmp with Const(n,_) -> n="Q18" | _ -> false)
    | Comb(a,b) -> mentions_q18 a || mentions_q18 b | Abs(_,t2) -> mentions_q18 t2 | _ -> false in
  DISCARD_ASSUMPTIONS_TAC(fun thm ->
    if mentions_q18 (concl thm) then false else
    let us = unbound_statevars_of_read [] (concl thm) in
    if us = [] || us = [v] then false else true);;
let state_num_of_q18_fact th =
  try let c = concl th in
      if not(is_eq c) then None else
      match lhs c with
        Comb(Comb(Const("read",_),Const("Q18",_)),Var(sn,_)) when String.length sn > 1 && sn.[0]='s' ->
          Some(int_of_string(String.sub sn 1 (String.length sn - 1)))
      | _ -> None
  with _ -> None;;
let DISCARD_STALE_Q18_TAC : tactic = fun (asl,w) ->
  let nums = List.filter_map (fun (_,th) -> state_num_of_q18_fact th) asl in
  match nums with
  | [] | [_] -> ALL_TAC (asl,w)
  | _ -> let mx = List.fold_left max 0 nums in
         DISCARD_ASSUMPTIONS_TAC (fun th ->
           match state_num_of_q18_fact th with
           | Some k -> k < mx
           | None -> false) (asl,w);;
(* SPEED (refine-084): the per-step normalizer is GCM_SIMD_SIMPLIFY_CORE_TAC, NOT
   the double-pass GCM_SIMD_SIMPLIFY_TAC (= CORE THEN CORE).  The 2nd CORE pass is a
   full RULE_ASSUM traversal of the whole carried GHASH pile; on the tail sim it is a
   MEASURED no-op on 114/122 steps (it only folds the fresh REV64 byte-tree at the ~8
   block-boundary steps, and THAT fold is re-done downstream by the Q19 bridge's
   WORD_BYTEREVERSE_REVERSEFIELDS/RF8_SUBWORD rewrites).  Dropping it keeps every tail
   (WB_TAIL_3..8, the sole consumers) closing hyps=0 while cutting the pile-driven
   rescan: the per-step cost had GROWN 0.59->0.94s across 271-392 (pile-driven, not the
   position-invariant ARM_STEPS wall).  WB_TAIL_GEN2_8 179.8s->150.2s (-16.5%), GEN2_3
   also hyps=0.  Mirrors the KEEPDATA single-pass fix on this file's OTHER stepper;
   the tails' Q18LATEST stepper had never been converted.  If a future edit needs the
   fixpoint here, restore GCM_SIMD_SIMPLIFY_TAC. *)
let ARM_STEPS_FOLD_Q18LATEST_TAC exec snums =
  MAP_EVERY (fun s -> ARM_VERBOSE_STEP_TAC exec s THEN GCM_SIMD_SIMPLIFY_CORE_TAC THEN
              DISCARD_STALE_Q18_TAC THEN DISCARD_OLDSTATE_KEEPQ18_TAC s THEN CLARIFY_TAC)
    (statenames "s" snums);;
(* MERGE_QQPAIR / FOLD_MID_HPOW variants that unfold karatsuba_mid inside the
   closing WORD_BLAST: the midacc expansion exposes machine mids whose spec
   partners are karatsuba_mid-folded. *)
let MERGE_QQPAIR_KM_TAC (n1:string) (n2:string) : tactic =
  SUBGOAL_THEN (mk_eq(mk_var(n1,`:128 word`), mk_var(n2,`:128 word`)))
    (fun th -> REWRITE_TAC[th] THEN RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
  [EXPAND_TAC n1 THEN EXPAND_TAC n2 THEN REWRITE_TAC[karatsuba_mid] THEN
   ((MATCH_MP_TAC PMUL_CONG_128 THEN CONJ_TAC THEN
     (CONV_TAC WORD_BLAST ORELSE (REWRITE_TAC WB_MID_FIX THEN CONV_TAC WORD_BLAST)))
    ORELSE (GEN_REWRITE_TAC LAND_CONV [WORD_PMUL_SYM] THEN
            MATCH_MP_TAC PMUL_CONG_128 THEN CONJ_TAC THEN
            (CONV_TAC WORD_BLAST ORELSE (REWRITE_TAC WB_MID_FIX THEN CONV_TAC WORD_BLAST))));
   ALL_TAC];;
let FOLD_MID_HPOW_KM hp : tactic = fun (asl,w) ->
  let l = lhs w in
  let mid = hd(List.filter (fun t -> pmul_mult_hpow t = hp) (setify(find_terms is_pmul128_tm l))) in
  let cands = List.filter (fun (_,th) ->
      try let r=rhs(concl th) and lft=lhs(concl th) in
          is_var r && (let n=fst(dest_var r) in String.length n>=2 && String.sub n 0 2="qq") &&
          is_pmul128_tm lft && pmul_mult_hpow lft = hp
      with _->false) asl in
  let try_qq (_,th) =
    let qq = rhs(concl th) in
    (SUBGOAL_THEN (mk_eq(mid,qq)) (fun e->REWRITE_TAC[e]) THENL
      [GEN_REWRITE_TAC RAND_CONV [GSYM th] THEN REWRITE_TAC[karatsuba_mid] THEN
       MATCH_MP_TAC PMUL_CONG_128 THEN CONJ_TAC THEN
       (CONV_TAC WORD_BLAST ORELSE (REWRITE_TAC WB_MID_FIX THEN CONV_TAC WORD_BLAST)); ALL_TAC]) in
  (FIRST (map try_qq cands)) (asl,w);;
(* WA-unify via BITBLAST_RULE: stock WA_UNIFY_TAC's WORD_RULE stack-overflows
   on the ~1.1k-char wa inputs this state produces. *)
let WA_UNIFY_BB_TAC : tactic = fun (asl,w) ->
  let l=lhs w and r=rhs w in
  let iswa t = isWpmul t && not(can (find_term (fun u->u<>t && isWpmul u)) (rand(rator t))) in
  let lwa=hd(collect_pmuls iswa l) and rwa=hd(collect_pmuls iswa r) in
  if lwa=rwa then ALL_TAC (asl,w) else
  let in_eq = BITBLAST_RULE (mk_eq(rand(rator rwa), rand(rator lwa))) in
  let mult_eq = BITBLAST_RULE (mk_eq(rand rwa, rand lwa)) in
  let wa_eq = MATCH_MP (ISPECL [rand(rator rwa); rand rwa; rand(rator lwa); rand lwa] PMUL_CONG_128)
                (CONJ in_eq mult_eq) in
  GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [wa_eq] (asl,w);;

(* ins->ext runtime opt (2026-08-11): NAME-AGNOSTIC replacement for the per-band
   hardcoded `MERGE_QQPAIR_KM_TAC "qq4'" "qq9"` + `FOLD_MID_HPOW_KM [...]` lines.
   The per-step normalizer (GCM_SIMD_SIMPLIFY_CORE_TAC + EXT8_LANE0_IS_SUBWORD_HI)
   collapses the ext-form Karatsuba-mid lanes back to the ins-form lanes, but if
   ABBREV_INNER_PMULS ever assigns DIFFERENT qq numbers than the pre-opt proof the
   hardcoded qq-names no longer exist.  Instead of re-deriving names per band
   (fragile), this pairs the leftover mid pmuls by H-power (which keys off the KEY
   operand h2/h3/.., unaffected by the data-side ext form): after MERGE_ANY_TAC has
   merged everything it can, the only residual mismatch is a set of karatsuba-mid
   qq atoms UNIQUE to the LHS vs UNIQUE to the RHS; each LHS-unique qq merges with
   the RHS-unique qq of the SAME H-power (MERGE_QQPAIR_KM_TAC, closes by WORD_BLAST
   so it is form-insensitive).  A numbering-agnostic safety net robust across
   WB_TAIL_3..8 + prepretail regardless of the exact operand form. *)
let AUTO_MERGE_MIDS_KM_TAC : tactic = fun (asl,w) ->
  let rec xleaves t = match t with
    | Comb(Comb(Const("word_xor",_),a),b) -> xleaves a @ xleaves b | _ -> [t] in
  let qqs_in t = setify(map (fun v->fst(dest_var v))
     (List.filter (fun v-> let n=fst(dest_var v) in String.length n>=2 && String.sub n 0 2="qq")
        (frees t))) in
  let hpow n = try let (_,th)=List.find(fun(_,th)->let c=concl th in
       is_eq c && is_var(rhs c) && fst(dest_var(rhs c))=n) asl in pmul_mult_hpow(lhs(concl th))
     with _->"?" in
  let ll = xleaves(lhs w) and rl = xleaves(rhs w) in
  let dl = subtract (setify ll) (setify rl) and dr = subtract (setify rl) (setify ll) in
  let lqq = subtract (setify(List.concat_map qqs_in dl)) (setify(List.concat_map qqs_in dr)) in
  let rqq = subtract (setify(List.concat_map qqs_in dr)) (setify(List.concat_map qqs_in dl)) in
  let used = ref [] in
  let pairs = List.filter_map (fun ln ->
     let hp = hpow ln in
     try let rn = List.find (fun rn -> not(mem rn !used) && hpow rn = hp) rqq in
         used := rn :: !used; Some(ln,rn)
     with _ -> None) lqq in
  (EVERY (map (fun (a,b) -> MERGE_QQPAIR_KM_TAC a b) pairs)) (asl,w);;

(* OPTIMIZED STEPPING (2026-07-18): stores window 283-392 uses the Q18-latest
   per-step-discard stepper + midacc atomization instead of all-KEEPGH
   (proof 1573s -> ~470s cpu, peak heap ~2GB vs ~30GB).  Bridge expands midacc
   once, re-merges (KM tactic variants), folds H6..H2, WA-unify via BITBLAST.
   Same statement as before, only the tactic script changed. *)
(* WB_7/WB_8 midacc bridges leave a stray zero limb in each 64-bit lane
   (from the s392-carried mid entering the reduce as word 0 xor ...):
   collapse it before the bubble sort, then finish as LANE_FINISH_TAC. *)
let ZSUB0 = prove(`word_subword (word 0:int128) (0,64):64 word = word 0`, CONV_TAC WORD_BLAST);;
let ZSUB0b = prove(`word_subword (word 0:int128) (64,64):64 word = word 0`, CONV_TAC WORD_BLAST);;
let LANE_FINISH_Z_TAC : tactic =
  CONV_TAC(LAND_CONV(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
  CONV_TAC(RAND_CONV(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
  REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES; WORD_SUBWORD_XOR] THEN
  REWRITE_TAC[SJ_COLLAPSE; SJ_COLLAPSE2] THEN REWRITE_TAC[WORD_SUBWORD_XOR] THEN
  REWRITE_TAC[ZSUB0; ZSUB0b; WORD_XOR_0; WORD_XOR_0_LEFT] THEN
  CONV_TAC(BINOP_CONV bubble_fix) THEN REFL_TAC;;

(* OPTIMIZED STEPPING (2026-07-18): stores window uses the Q18-latest
   per-step-discard stepper + midacc atomization instead of all-KEEPGH
   (same pattern as WB_7/WB_8; ~1.5-3x faster, flat memory).  *)


(* ============================================================================
   WB_4BLOCK: PROVED interactively (hyps=0, axioms=3).
   Tail map (entry s303 = pc+4220 = more_than_3, R3):
     304-309 KEEPGH; Q12 s309 = block-0 PT capture; s310 = store block-0
       (VSTEPS_FOLD + carry out_p) + KEEPGH discard.
     311-326 KEEPGH -> s326 pc+4312; Q12 s326 = block-1 (INC lanes);
       s327 = store block-1 (VSTEPS_FOLD + carry out_p, out_p+16) + discard.
     328-341 KEEPGH -> s341 pc+4372; Q12 s341 = block-2 (INC2 lanes);
       s342 = store block-2 (VSTEPS_FOLD + carry 3 readbacks) + discard.
     343-347 KEEPGH -> s347 pc+4396 (Q9=cph3 already); Q12 s347 = block-3
       (INC3 lanes) — capture BEFORE the shared reduce.
     348-369 KEEPGH -> s369 pc+4484; s370 = final store (PLAIN VSTEPS)
       + carry ALL FOUR out_p readbacks + KEEPGH discard + 4x DISCH.
     371-377 KEEPGH -> s377 pc+4516 = BRIDGE.
     BRIDGE (GMULT4): gmult4_dec = SPECL [a0.h4; brev cph1.h3; brev cph2.h2;
       brev cph3.h] GMULT4_FULL_CORRECT_BA; spec fold via spec_to_byteform_wb4
       (h2,h3,h4 conjuncts, ALL LEFT-NESTED so plain ASM_REWRITE, no DOT_SYM);
       then rewrites + karatsuba_mid + ABBREV_INNER_PMULS + MERGE_2BLK
       (12 qq atoms remain incl 2 unmerged mids keyed H3,H2) THEN
       FOLD_MID_HPOW "H3" THEN FOLD_MID_HPOW "H2" THEN WA_UNIFY THEN WV_UNIFY
       THEN ABBREV_WAWV THEN QQ0SPLIT/JOIN_EQ_SPLIT THEN CONJ_TAC THEN
       LANE_FINISH_TAC.  (QQ8_FOLD not needed at N=4 — its job is subsumed by
       FOLD_MID_HPOW "H2"?  NO: at N=3 the one leftover mid was H2-keyed and
       QQ8_FOLD_TAC grabbed it; at N=4 there are two (H3,H2) so use
       FOLD_MID_HPOW for both.  GENERAL RULE for band N: after MERGE,
       FOLD_MID_HPOW "H<N-1>" .. "H2" (rev order), then WA/WV unify.)
     378-379 ext/rev64 + Q19 s379 = brev gval; 380 tag store; final as before.

   GENERAL WB BAND STRUCTURE (N=2..8) — states shift by band:
     entry sE:      N=2:313/pc4348  N=3:309/4288  N=4:303/4220  N=5:297/4164?
                    N=6:290/4104?   N=7:282/4048?  N=8:270/4000?
     (cascade sEnd from ARM_STEPS_RESOLVE (278--sEnd); discover live per band)
     per full round k=0..N-2: ~6-16 steps; block-k PT capture right before its
       str; final block N-1 capture at the eor3 right after last cascade ldr.
     final store at pc+4484 (str q12,[x2] No_Offset) = PLAIN VSTEPS.
     bridge at pc+4516; ext/rev64; tag store pc+4524; exit pc+4552.
   ============================================================================ *)

let GCM_CTR_INC3_LANES = prove
 (mk_eq(`gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ctr0))`,
        subst [`word 3:32 word`, `word 1:32 word`]
          (rhs(snd(strip_forall(concl GCM_CTR_INC_LANES))))),
  REWRITE_TAC[gcm_ctr_inc] THEN BITBLAST_TAC);;
let PACK4_ID, GMULT4_FULL_CORRECT_BA = build_GMULTn_fast 4;;
let spec_to_byteform_wb4 = prove
 (`byteswap128 h2 = polyval_dot (byteswap128 h) (byteswap128 h) /\
   byteswap128 h3 = polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h) /\
   byteswap128 h4 = polyval_dot (polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)
   ==> ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
        [word_bytereverse cph0; word_bytereverse cph1; word_bytereverse cph2; word_bytereverse cph3] =
       polyval_reduce_prop3
        (word_xor
         (word_xor
          (word_xor
           (word_pmul (word_xor (word_bytereverse xi) (word_bytereverse cph0)) (byteswap128 h4))
           (word_pmul (word_bytereverse cph1) (byteswap128 h3)))
          (word_pmul (word_bytereverse cph2) (byteswap128 h2)))
         (word_pmul (word_bytereverse cph3) (byteswap128 h)))`,
  STRIP_TAC THEN
  REWRITE_TAC[REWRITE_RULE[LET_DEF;LET_END_DEF]
    (SPECL [`byteswap128 h:int128`; `word_bytereverse xi:int128`;
            `word_bytereverse cph0:int128`; `word_bytereverse cph1:int128`;
            `word_bytereverse cph2:int128`; `word_bytereverse cph3:int128`] GHASH_POLYVAL_ACC_4)] THEN
  ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE);;

(* ============================================================================
   WB_5BLOCK PLAN (derived from disassembly, 2026-07-16).

   DISASSEMBLY FINDING: the cascade b.gt targets confirm the band entries:
   N=5 takes the #64 branch (b.gt at pc+3920, offset 244) -> entry pc+4164 =
   R4 region head (rev64 v8,v9 for the block-0 GHASH round vs h5=Q20).
   R4 = pc+4164..4216, exactly 14 instructions:
     rev64; eor v8,v16; ins v27; ldr q9(cph1); movi d16; pmull(q20);
     pmull2(q20); eor v27,v8; eor v17,v28; pmull v27(q21-mid); eor v19,v26;
     str q12 (BLOCK-0 STORE, 12th instr); eor v18,v27; eor3 v12,v9,v4,v29
     (BLOCK-1 PT, 14th instr; ks1 lives in Q4 = Q(8-N+1) for N=5).
   Then N=5 falls into the SHARED WB_4 tail at pc+4220: every WB_4 tail step
   s(304+k) = WB_5 step s(312+k), block indices shifted +1 (INC^k lanes).

   WB_5 TAIL MAP (entry s297 = pc+4164; Q12 = block-0 PT from the cascade
   preamble eor3 v12,v9,v0,v29 at pc+3804):
     298-308 KEEPGH (R4 round); Q12 s308 = block-0 capture (plain
       reconstruct+WORD_RULE — Q12 untouched since preamble); s309 = str
       q12,[x2],#16 block-0 store (VSTEPS_FOLD + carry out_p) + discard.
     310-317 KEEPGH (s311 = eor3 block-1 vs Q4); Q12 s317 = block-1 (INC
       lanes); s318 = store block-1 (VSTEPS_FOLD + carry out_p, out_p+16).
     319-334 KEEPGH (s319 = eor3 block-2 vs Q5); Q12 s334 = block-2 (INC2);
       s335 = store (VSTEPS_FOLD + carry 3 readbacks).
     336-349 KEEPGH (s...= eor3 block-3 vs Q6); Q12 s349 = block-3 (INC3);
       s350 = store (VSTEPS_FOLD + carry 4 readbacks).
     351-355 KEEPGH (eor3 block-4 vs Q7); Q12 s355 = block-4 (INC4 lanes) —
       capture BEFORE the shared reduce.
     356-377 KEEPGH -> s377 pc+4484; s378 = final store (PLAIN VSTEPS) +
       carry ALL FIVE out_p readbacks + KEEPGH discard + 5x DISCH.
     379-385 KEEPGH -> s385 pc+4516 = BRIDGE (GMULT5: spec_to_byteform_wb5
       + GSYM gmult5_dec pairs (a0,h5)(cph1,h4)(cph2,h3)(cph3,h2)(cph4,h);
       FOLD_MID_HPOW "H4" "H3" "H2").
     386-387 ext/rev64 + Q19 s387 = brev gval; 388 tag store; exit pc+4552.
   Front discards keep Q0..Q4: per-step 6..30 [5;6;7], bulk [5;6;7;30],
   after 256-265 [5;6;30].  Cascade (266--277) + (278--297).
   ============================================================================ *)

let GCM_CTR_INC4_LANES = prove
 (mk_eq(`gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ctr0)))`,
        subst [`word 4:32 word`, `word 1:32 word`]
          (rhs(snd(strip_forall(concl GCM_CTR_INC_LANES))))),
  REWRITE_TAC[gcm_ctr_inc] THEN BITBLAST_TAC);;
let PACK5_ID, GMULT5_FULL_CORRECT_BA = build_GMULTn_fast 5;;
let spec_to_byteform_wb5 = prove
 (`byteswap128 h2 = polyval_dot (byteswap128 h) (byteswap128 h) /\
   byteswap128 h3 = polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h) /\
   byteswap128 h4 = polyval_dot (polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h)) (byteswap128 h) /\
   byteswap128 h5 = polyval_dot (polyval_dot (polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)
   ==> ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
        [word_bytereverse cph0; word_bytereverse cph1; word_bytereverse cph2;
         word_bytereverse cph3; word_bytereverse cph4] =
       polyval_reduce_prop3
        (word_xor
         (word_xor
          (word_xor
           (word_xor
            (word_pmul (word_xor (word_bytereverse xi) (word_bytereverse cph0)) (byteswap128 h5))
            (word_pmul (word_bytereverse cph1) (byteswap128 h4)))
           (word_pmul (word_bytereverse cph2) (byteswap128 h3)))
          (word_pmul (word_bytereverse cph3) (byteswap128 h2)))
         (word_pmul (word_bytereverse cph4) (byteswap128 h)))`,
  STRIP_TAC THEN
  REWRITE_TAC[REWRITE_RULE[LET_DEF;LET_END_DEF]
    (SPECL [`byteswap128 h:int128`; `word_bytereverse xi:int128`;
            `word_bytereverse cph0:int128`; `word_bytereverse cph1:int128`;
            `word_bytereverse cph2:int128`; `word_bytereverse cph3:int128`;
            `word_bytereverse cph4:int128`] GHASH_POLYVAL_ACC_5)] THEN
  ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE);;
(* ------------------------------------------------------------------------- *)
(* AESV8_GCM_8X_DEC_256_4BLOCK: whole-blocks dec variant, bit_len=512.     *)
(* Script assembled from the interactively-validated tail map above.          *)
(* ------------------------------------------------------------------------- *)
(* OPTIMIZED STEPPING (2026-07-18): stores window uses the Q18-latest
   per-step-discard stepper + midacc atomization instead of all-KEEPGH
   (same pattern as WB_7/WB_8; ~1.5-3x faster, flat memory).  *)


(* ------------------------------------------------------------------------- *)
(* AESV8_GCM_8X_DEC_256_5BLOCK: whole-blocks dec variant, bit_len=640.     *)
(* PROVED INTERACTIVELY 2026-07-16 first-pass, no backtracking: the derived   *)
(* tail map (entry s297=pc+4164, captures s308/s317/s334/s349/s355, final     *)
(* store s378, bridge s385) was exactly right.                                *)
(* ------------------------------------------------------------------------- *)
(* OPTIMIZED STEPPING (2026-07-18): stores window uses the Q18-latest
   per-step-discard stepper + midacc atomization instead of all-KEEPGH
   (same pattern as WB_7/WB_8; ~1.5-3x faster, flat memory).  *)



(* ============================================================================
   WB_6BLOCK machinery.  GHASH_POLYVAL_ACC_6 does not exist in
   common/ghash_nblock_karatsuba.ml (only 2..5) — proved here from
   GHASH_POLYVAL_ACC_BATCHED with the same recipe; promote to common/ later.
   ============================================================================ *)
let GHASH_POLYVAL_ACC_6 = prove
 (`!(h:int128) (a:int128) (p:int128) (q:int128) (r:int128) (s:int128) (t:int128) (u:int128).
    ghash_polyval_acc h a [p:int128; q; r; s; t; u] =
    polyval_reduce_prop3
      (word_xor
        (word_pmul (word_xor a p) (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) h) h) h) h) : 256 word)
       (word_xor
        (word_pmul q (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) h) h) h) : 256 word)
       (word_xor
        (word_pmul r (polyval_dot (polyval_dot (polyval_dot h h) h) h) : 256 word)
       (word_xor
        (word_pmul s (polyval_dot (polyval_dot h h) h) : 256 word)
       (word_xor
        (word_pmul t (polyval_dot h h) : 256 word)
        (word_pmul u h : 256 word))))))`,
  REPEAT GEN_TAC THEN
  MP_TAC (SPECL [`h:int128`; `[q:int128; r; s; t; u]`; `a:int128`; `p:int128`]
                GHASH_POLYVAL_ACC_BATCHED) THEN
  REWRITE_TAC[LENGTH; ghash_wide; h_power; ARITH; SUB_0] THEN
  REWRITE_TAC[WORD_XOR_0] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[num_CONV `5`; num_CONV `4`; num_CONV `3`; num_CONV `2`; num_CONV `1`; h_power]);;
let GCM_CTR_INC5_LANES = prove
 (mk_eq(`gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ctr0))))`,
        subst [`word 5:32 word`, `word 1:32 word`]
          (rhs(snd(strip_forall(concl GCM_CTR_INC_LANES))))),
  REWRITE_TAC[gcm_ctr_inc] THEN BITBLAST_TAC);;
let PACK6_ID, GMULT6_FULL_CORRECT_BA = build_GMULTn_fast 6;;
let spec_to_byteform_wb6 = prove
 (`byteswap128 h2 = polyval_dot (byteswap128 h) (byteswap128 h) /\
   byteswap128 h3 = polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h) /\
   byteswap128 h4 = polyval_dot (polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h)) (byteswap128 h) /\
   byteswap128 h5 = polyval_dot (polyval_dot (polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)) (byteswap128 h) /\
   byteswap128 h6 = polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)
   ==> ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
        [word_bytereverse cph0; word_bytereverse cph1; word_bytereverse cph2;
         word_bytereverse cph3; word_bytereverse cph4; word_bytereverse cph5] =
       polyval_reduce_prop3
        (word_xor
         (word_xor
          (word_xor
           (word_xor
            (word_xor
             (word_pmul (word_xor (word_bytereverse xi) (word_bytereverse cph0)) (byteswap128 h6))
             (word_pmul (word_bytereverse cph1) (byteswap128 h5)))
            (word_pmul (word_bytereverse cph2) (byteswap128 h4)))
           (word_pmul (word_bytereverse cph3) (byteswap128 h3)))
          (word_pmul (word_bytereverse cph4) (byteswap128 h2)))
         (word_pmul (word_bytereverse cph5) (byteswap128 h)))`,
  STRIP_TAC THEN
  REWRITE_TAC[REWRITE_RULE[LET_DEF;LET_END_DEF]
    (SPECL [`byteswap128 h:int128`; `word_bytereverse xi:int128`;
            `word_bytereverse cph0:int128`; `word_bytereverse cph1:int128`;
            `word_bytereverse cph2:int128`; `word_bytereverse cph3:int128`;
            `word_bytereverse cph4:int128`; `word_bytereverse cph5:int128`] GHASH_POLYVAL_ACC_6)] THEN
  ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE);;

(* ------------------------------------------------------------------------- *)
(* AESV8_GCM_8X_DEC_256_6BLOCK: whole-blocks dec variant, bit_len=768.     *)
(* PROVED INTERACTIVELY 2026-07-16 first-pass.  Tail map: entry s290=pc+4104  *)
(* (R5 head, N=6 takes the #80 branch; cascade RESOLVE (278--290));           *)
(* R5 = 291-296 + capture s296 (block-0 vs h6, plain reconstruct) + store     *)
(* s297; R4 = 298-316 + capture s316 (INC lanes) + store s317; then the       *)
(* shared WB_5 tail shifted +8: captures s325/s342/s357 (INC2/INC3/INC4),     *)
(* stores s326/s343/s358; final eor3 in 359-363, capture s363 (INC5 lanes);   *)
(* reduce 364-385; final store s386 (PLAIN VSTEPS + 6 readback carries);      *)
(* 387-393 KEEPGH -> bridge s393 pc+4516 (GMULT6, FOLD_MID_HPOW H5..H2);      *)
(* ext/rev64 394-395; tag store 396; exit pc+4528.                            *)
(* ------------------------------------------------------------------------- *)
(* OPTIMIZED STEPPING (2026-07-18): stores window uses the Q18-latest
   per-step-discard stepper + midacc atomization instead of all-KEEPGH
   (same pattern as WB_7/WB_8; ~1.5-3x faster, flat memory).  *)


(* ============================================================================
   WB_7BLOCK machinery (ACC_7 proved from BATCHED like ACC_6 below).
   ============================================================================ *)
let GHASH_POLYVAL_ACC_7 = prove
 (`!(h:int128) (a:int128) (p:int128) (q:int128) (r:int128) (s:int128) (t:int128) (u:int128) (v:int128).
    ghash_polyval_acc h a [p:int128; q; r; s; t; u; v] =
    polyval_reduce_prop3
      (word_xor
        (word_pmul (word_xor a p) (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) h) h) h) h) h) : 256 word)
       (word_xor
        (word_pmul q (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) h) h) h) h) : 256 word)
       (word_xor
        (word_pmul r (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) h) h) h) : 256 word)
       (word_xor
        (word_pmul s (polyval_dot (polyval_dot (polyval_dot h h) h) h) : 256 word)
       (word_xor
        (word_pmul t (polyval_dot (polyval_dot h h) h) : 256 word)
       (word_xor
        (word_pmul u (polyval_dot h h) : 256 word)
        (word_pmul v h : 256 word)))))))`,
  REPEAT GEN_TAC THEN
  MP_TAC (SPECL [`h:int128`; `[q:int128; r; s; t; u; v]`; `a:int128`; `p:int128`]
                GHASH_POLYVAL_ACC_BATCHED) THEN
  REWRITE_TAC[LENGTH; ghash_wide; h_power; ARITH; SUB_0] THEN
  REWRITE_TAC[WORD_XOR_0] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[num_CONV `6`; num_CONV `5`; num_CONV `4`; num_CONV `3`; num_CONV `2`; num_CONV `1`; h_power]);;
let GCM_CTR_INC6_LANES = prove
 (mk_eq(`gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ctr0)))))`,
        subst [`word 6:32 word`, `word 1:32 word`]
          (rhs(snd(strip_forall(concl GCM_CTR_INC_LANES))))),
  REWRITE_TAC[gcm_ctr_inc] THEN BITBLAST_TAC);;
let PACK7_ID, GMULT7_FULL_CORRECT_BA = build_GMULTn_fast 7;;
let spec_to_byteform_wb7 = prove
 (`byteswap128 h2 = polyval_dot (byteswap128 h) (byteswap128 h) /\
   byteswap128 h3 = polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h) /\
   byteswap128 h4 = polyval_dot (polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h)) (byteswap128 h) /\
   byteswap128 h5 = polyval_dot (polyval_dot (polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)) (byteswap128 h) /\
   byteswap128 h6 = polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)) (byteswap128 h) /\
   byteswap128 h7 = polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)
   ==> ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
        [word_bytereverse cph0; word_bytereverse cph1; word_bytereverse cph2;
         word_bytereverse cph3; word_bytereverse cph4; word_bytereverse cph5;
         word_bytereverse cph6] =
       polyval_reduce_prop3
        (word_xor
         (word_xor
          (word_xor
           (word_xor
            (word_xor
             (word_xor
              (word_pmul (word_xor (word_bytereverse xi) (word_bytereverse cph0)) (byteswap128 h7))
              (word_pmul (word_bytereverse cph1) (byteswap128 h6)))
             (word_pmul (word_bytereverse cph2) (byteswap128 h5)))
            (word_pmul (word_bytereverse cph3) (byteswap128 h4)))
           (word_pmul (word_bytereverse cph4) (byteswap128 h3)))
          (word_pmul (word_bytereverse cph5) (byteswap128 h2)))
         (word_pmul (word_bytereverse cph6) (byteswap128 h)))`,
  STRIP_TAC THEN
  REWRITE_TAC[REWRITE_RULE[LET_DEF;LET_END_DEF]
    (SPECL [`byteswap128 h:int128`; `word_bytereverse xi:int128`;
            `word_bytereverse cph0:int128`; `word_bytereverse cph1:int128`;
            `word_bytereverse cph2:int128`; `word_bytereverse cph3:int128`;
            `word_bytereverse cph4:int128`; `word_bytereverse cph5:int128`;
            `word_bytereverse cph6:int128`] GHASH_POLYVAL_ACC_7)] THEN
  ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE);;

(* ------------------------------------------------------------------------- *)
(* AESV8_GCM_8X_DEC_256_7BLOCK: whole-blocks dec variant, bit_len=896.     *)
(* PROVED INTERACTIVELY 2026-07-16 first-pass.  Tail map: entry s282=pc+4048  *)
(* (R6 head; cascade RESOLVE (278--282)); R6 = 283-287 + capture s287         *)
(* (block-0 vs h7, plain reconstruct — NOTE only 5 KEEPGH steps then capture, *)
(* the eor3 for block-1 comes at pc+4028 BEFORE the R6 head so Q12 is         *)
(* block-0 all through) + store s288; R5 = 289-302 + capture s302 (INC) +     *)
(* store s303; then WB_6's map +6: captures s322/s331/s348/s363/s369          *)
(* (INC2..INC6), stores s323/332/349/364, final store s392 (PLAIN VSTEPS +    *)
(* 7 readback carries); 393-399 KEEPGH -> bridge s399 pc+4516 (GMULT7,        *)
(* FOLD_MID_HPOW H6..H2); ext/rev64 400-401; tag store 402; exit pc+4528.     *)
(* ------------------------------------------------------------------------- *)

(* ============================================================================
   WB_8BLOCK machinery + proof.

   N=8 SPECIFIC FINDINGS (2026-07-16):
   1. Cascade: X5=128 fails ALL the b.gt tests and falls through to pc+4000 =
      `b +420` -> the R7 head at pc+4004.  Cascade = RESOLVE (266--270) only
      (no mov-chain: all 8 keystreams already in Q0..Q7); s270 = pc+4000.
   2. R7 head: only TWO KEEPGH steps (271-272) then block-0 capture at s272 —
      the eor3 for block-1 sits at pc+4028 (later); Q12 is still the cascade
      preamble's block-0 eor3.  Store s273; R6 = 274-287 + capture s287 (INC)
      + store s288; then WB_7's tail map SHIFTED -14: captures
      s302/s322/s331/s348/s363/s369 (INC2..INC7), stores s303/323/332/349/364,
      final store s392 (PLAIN VSTEPS + 8 carries), bridge s399 = pc+4516,
      ext/rev64 400-401, tag store 402, exit pc+4552.
   3. MERGE BLOCKER: at N=8 the stock MERGE_2BLK_TAC (core.ml) mis-pairs the
      qq atoms — its find_pair takes the FIRST signature-compatible candidate
      and at N=8 that greedy choice pairs machine-lo with spec-hi atoms
      leaving 4 unmergeable leftovers; the WORD_RULE r1/u staging then fails.
      FIX = MERGE_ONE_ANY_TAC below: same pairing signature but tries ALL
      candidate pairs via FIRST (backtracking on the WORD_BLAST operand
      close), so a bad greedy pick self-corrects.  After MERGE_ANY_TAC two
      k13-garbage mids remain (qq37 vs qq28 keyed H7, qq42 vs qq41 keyed H8 —
      the le8block "k13-kill" pattern): close each with an explicit
      SUBGOAL merge using WB_MID_FIX + WORD_BLAST.  NO FOLD_MID_HPOW needed.
   ============================================================================ *)
let GHASH_POLYVAL_ACC_8 = prove
 (`!(h:int128) (a:int128) (p:int128) (q:int128) (r:int128) (s:int128) (t:int128) (u:int128) (v:int128) (w:int128).
    ghash_polyval_acc h a [p:int128; q; r; s; t; u; v; w] =
    polyval_reduce_prop3
      (word_xor
        (word_pmul (word_xor a p) (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) h) h) h) h) h) h) : 256 word)
       (word_xor
        (word_pmul q (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) h) h) h) h) h) : 256 word)
       (word_xor
        (word_pmul r (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) h) h) h) h) : 256 word)
       (word_xor
        (word_pmul s (polyval_dot (polyval_dot (polyval_dot (polyval_dot h h) h) h) h) : 256 word)
       (word_xor
        (word_pmul t (polyval_dot (polyval_dot (polyval_dot h h) h) h) : 256 word)
       (word_xor
        (word_pmul u (polyval_dot (polyval_dot h h) h) : 256 word)
       (word_xor
        (word_pmul v (polyval_dot h h) : 256 word)
        (word_pmul w h : 256 word))))))))`,
  REPEAT GEN_TAC THEN
  MP_TAC (SPECL [`h:int128`; `[q:int128; r; s; t; u; v; w]`; `a:int128`; `p:int128`]
                GHASH_POLYVAL_ACC_BATCHED) THEN
  REWRITE_TAC[LENGTH; ghash_wide; h_power; ARITH; SUB_0] THEN
  REWRITE_TAC[WORD_XOR_0] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[num_CONV `7`; num_CONV `6`; num_CONV `5`; num_CONV `4`; num_CONV `3`; num_CONV `2`; num_CONV `1`; h_power]);;
let GCM_CTR_INC7_LANES = prove
 (mk_eq(`gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ctr0))))))`,
        subst [`word 7:32 word`, `word 1:32 word`]
          (rhs(snd(strip_forall(concl GCM_CTR_INC_LANES))))),
  REWRITE_TAC[gcm_ctr_inc] THEN BITBLAST_TAC);;
let PACK8_ID, GMULT8_FULL_CORRECT_BA = build_GMULTn_fast 8;;
let spec_to_byteform_wb8 = prove
 (`byteswap128 h2 = polyval_dot (byteswap128 h) (byteswap128 h) /\
   byteswap128 h3 = polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h) /\
   byteswap128 h4 = polyval_dot (polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h)) (byteswap128 h) /\
   byteswap128 h5 = polyval_dot (polyval_dot (polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)) (byteswap128 h) /\
   byteswap128 h6 = polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)) (byteswap128 h) /\
   byteswap128 h7 = polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)) (byteswap128 h) /\
   byteswap128 h8 = polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)
   ==> ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
        [word_bytereverse cph0; word_bytereverse cph1; word_bytereverse cph2;
         word_bytereverse cph3; word_bytereverse cph4; word_bytereverse cph5;
         word_bytereverse cph6; word_bytereverse cph7] =
       polyval_reduce_prop3
        (word_xor
         (word_xor
          (word_xor
           (word_xor
            (word_xor
             (word_xor
              (word_xor
               (word_pmul (word_xor (word_bytereverse xi) (word_bytereverse cph0)) (byteswap128 h8))
               (word_pmul (word_bytereverse cph1) (byteswap128 h7)))
              (word_pmul (word_bytereverse cph2) (byteswap128 h6)))
             (word_pmul (word_bytereverse cph3) (byteswap128 h5)))
            (word_pmul (word_bytereverse cph4) (byteswap128 h4)))
           (word_pmul (word_bytereverse cph5) (byteswap128 h3)))
          (word_pmul (word_bytereverse cph6) (byteswap128 h2)))
         (word_pmul (word_bytereverse cph7) (byteswap128 h)))`,
  STRIP_TAC THEN
  REWRITE_TAC[REWRITE_RULE[LET_DEF;LET_END_DEF]
    (SPECL [`byteswap128 h:int128`; `word_bytereverse xi:int128`;
            `word_bytereverse cph0:int128`; `word_bytereverse cph1:int128`;
            `word_bytereverse cph2:int128`; `word_bytereverse cph3:int128`;
            `word_bytereverse cph4:int128`; `word_bytereverse cph5:int128`;
            `word_bytereverse cph6:int128`; `word_bytereverse cph7:int128`] GHASH_POLYVAL_ACC_8)] THEN
  ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE);;

(* ------------------------------------------------------------------------- *)
(* AESV8_GCM_8X_DEC_256_8BLOCK: whole-blocks dec variant, bit_len=1024.    *)
(* PROVED INTERACTIVELY 2026-07-16 (one bridge retry: stock MERGE_2BLK        *)
(* mis-pairs at N=8 — see the machinery header note; fix = MERGE_ANY_TAC +    *)
(* two explicit k13-mid merges qq37/qq28 (H7) and qq42/qq41 (H8)).            *)
(* ------------------------------------------------------------------------- *)




(* OPTIMIZED STEPPING (2026-07-18): same Q18-latest/midacc pattern as WB_7
   (proof was the OOM-killer at ~26min/30GB; now ~600s cpu/~2GB).  The three
   midacc-side mids merge as qq14'/qq28 (H7), qq15'/qq34 (H1), qq16'/qq39 (H8). *)




(* ------------------------------------------------------------------------- *)
(*    Per-band tail tactics (cascade + GHASH + bridge + stores from s265)    *)
(* ------------------------------------------------------------------------- *)


let WB_TAIL_1_TAC ivtac =
  ARM_STEPS_RESOLVE_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (266--277) THEN
  ARM_STEPS_RESOLVE_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (278--313) THEN
  (* === tail 314..333 (GHASH multiply; KEEPGH keeps Q16-Q19 alive) === *)
  ARM_STEPS_FOLD_KEEPGH_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (314--333) THEN
  (* plaintext capture: the whole aese/aesmc tower XOR = aes256_encrypt      *)
  SUBGOAL_THEN `read Q12 (s333:armstate) = word_xor cph (aes256_encrypt (ctr0:int128)
      [k0:int128;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14])`
    (fun th -> RULE_ASSUM_TAC(fun asm ->
       if (try lhs(concl asm) = `read Q12 s333` with _ -> false)
       then th else asm) THEN ASSUME_TAC th) THENL
  [FIRST_ASSUM(fun th ->
     if is_eq(concl th) && (try lhs(concl th) = `read Q12 s333` with _ -> false)
     then GEN_REWRITE_TAC LAND_CONV [th] else NO_TAC) THEN
   REWRITE_TAC[GSYM AES256_XOR_ENCRYPT_RECONSTRUCT] THEN CONV_TAC WORD_RULE;
   ALL_TAC] THEN
  (* 334 = str q12,[x2] (output store); carry the readback across the discard *)
  ARM_VSTEPS_FOLD_TAC AESV8_GCM_8X_DEC_256_WB_EXEC [334] THEN
  FIRST_X_ASSUM(fun th ->
    if (try lhs(concl th) = `read (memory :> bytes128 out_p) s334` with _ -> false)
    then MP_TAC th else NO_TAC) THEN
  DISCARD_OLDSTATE_TAC "s334" THEN DISCH_TAC THEN
  (* 335..341 GHASH reduce; KEEPGH keeps Q16-Q19 threaded (Q19 s341 closes to
     an ~8.2k term over word_bytereverse xi / cph / h, NO state refs). *)
  ARM_STEPS_FOLD_KEEPGH_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (335--341) THEN
  (* === GHASH bridge at s341 (pc+4516, post eor v19,v19,v18) === *)
  SUBGOAL_THEN
    `read Q19 (s341:armstate) =
     polyval_dot (word_xor (word_bytereverse xi) (word_bytereverse cph))
       (byteswap128 h)`
    (fun th -> RULE_ASSUM_TAC(fun asm ->
       if (try lhs(concl asm) = `read Q19 s341` with _ -> false)
       then th else asm) THEN ASSUME_TAC th) THENL
  [FIRST_ASSUM(fun th ->
     if is_eq(concl th) && (try lhs(concl th) = `read Q19 s341` with _ -> false)
     then GEN_REWRITE_TAC LAND_CONV [th] else NO_TAC) THEN
   GEN_REWRITE_TAC RAND_CONV
     [GSYM(REWRITE_RULE[LET_DEF; LET_END_DEF]
        (ISPECL [`word_xor (word_bytereverse xi) (word_bytereverse cph) : int128`;
          `byteswap128 h:int128`] GMULT_FULL_CORRECT_BA))] THEN
   REWRITE_TAC[byteswap128] THEN
   REWRITE_TAC[WORD_INSERT_SUBWORD; WORD_SUBWORD_SUBWORD] THEN
   REWRITE_TAC[SUBWORD_XOR_JOIN_DIST] THEN
   REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES] THEN
   ABBREV_INNER_PMULS_TAC THEN MERGE_PMUL_ATOMS_TAC THEN
   TRY(SUBGOAL_THEN `qq5:int128 = qq2` (fun th -> REWRITE_TAC[th]) THENL
    [EXPAND_TAC "qq5" THEN EXPAND_TAC "qq2" THEN REWRITE_TAC[karatsuba_mid] THEN
     ((MATCH_MP_TAC PMUL_CONG_128 THEN CONJ_TAC THEN CONV_TAC WORD_BLAST)
      ORELSE (GEN_REWRITE_TAC LAND_CONV [WORD_PMUL_SYM] THEN
              MATCH_MP_TAC PMUL_CONG_128 THEN CONJ_TAC THEN CONV_TAC WORD_BLAST));
     ALL_TAC]) THEN
   REWRITE_TAC[SUBWORD0_LEMMAS; WORD_XOR_0] THEN REWRITE_TAC[WORD_XOR_0] THEN
   REWRITE_TAC[PMUL_W_64_128] THEN
   REWRITE_TAC[JOINMID] THEN
   REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES; WORD_SUBWORD_XOR] THEN
   ABBREV_TAC `xll:64 word = word_subword (qq0:int128) (0,64)` THEN
   ABBREV_TAC `xlh:64 word = word_subword (qq0:int128) (64,64)` THEN
   ABBREV_TAC `xhl:64 word = word_subword (qq1:int128) (0,64)` THEN
   ABBREV_TAC `xhh:64 word = word_subword (qq1:int128) (64,64)` THEN
   ABBREV_TAC `xml:64 word = word_subword (qq2:int128) (0,64)` THEN
   ABBREV_TAC `xmh:64 word = word_subword (qq2:int128) (64,64)` THEN
   ABBREV_TAC
    `r1:(128)word = word_xor (word_xor (word_shl (word_zx (xhl:(64)word):(128)word) 63)
                                       (word_shl (word_zx xhl:(128)word) 62))
                             (word_shl (word_zx xhl:(128)word) 57)` THEN
   SUBGOAL_THEN
    `word_xor (word_xor (word_subword (word_shl (word_zx (xhl:(64)word):(128)word) 63) (0,64):(64)word)
                        (word_subword (word_shl (word_zx xhl:(128)word) 62) (0,64):(64)word))
              (word_subword (word_shl (word_zx xhl:(128)word) 57) (0,64):(64)word) =
     word_subword (r1:(128)word) (0,64):(64)word`
    (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "r1" THEN CONV_TAC WORD_BLAST; ALL_TAC] THEN
   SUBGOAL_THEN
    `word_xor (word_xor (word_subword (word_shl (word_zx (xhl:(64)word):(128)word) 63) (64,64):(64)word)
                        (word_subword (word_shl (word_zx xhl:(128)word) 62) (64,64):(64)word))
              (word_subword (word_shl (word_zx xhl:(128)word) 57) (64,64):(64)word) =
     word_subword (r1:(128)word) (64,64):(64)word`
    (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "r1" THEN CONV_TAC WORD_BLAST; ALL_TAC] THEN
   ABBREV_TAC `u:(64)word = word_xor (word_xor (word_subword (r1:128 word) (0,64)) (xhh:64 word)) (word_xor (word_xor (xll:64 word) (xhl:64 word)) (xml:64 word))` THEN
   SUBGOAL_THEN
    `word_xor (word_xor (xhh:64 word) (word_xor (word_xor (xml:64 word) (xhl:64 word)) (xll:64 word))) (word_subword (r1:128 word) (0,64)) = u`
    (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "u" THEN CONV_TAC WORD_BLAST; ALL_TAC] THEN
   ABBREV_TAC
    `r2:(128)word = word_xor (word_xor (word_shl (word_zx (u:(64)word):(128)word) 63)
                                       (word_shl (word_zx u:(128)word) 62))
                             (word_shl (word_zx u:(128)word) 57)` THEN
   SUBGOAL_THEN
    `word_xor (word_xor (word_subword (word_shl (word_zx (u:(64)word):(128)word) 63) (0,64):(64)word)
                        (word_subword (word_shl (word_zx u:(128)word) 62) (0,64):(64)word))
              (word_subword (word_shl (word_zx u:(128)word) 57) (0,64):(64)word) =
     word_subword (r2:(128)word) (0,64):(64)word`
    (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "r2" THEN CONV_TAC WORD_BLAST; ALL_TAC] THEN
   SUBGOAL_THEN
    `word_xor (word_xor (word_subword (word_shl (word_zx (u:(64)word):(128)word) 63) (64,64):(64)word)
                        (word_subword (word_shl (word_zx u:(128)word) 62) (64,64):(64)word))
              (word_subword (word_shl (word_zx u:(128)word) 57) (64,64):(64)word) =
     word_subword (r2:(128)word) (64,64):(64)word`
    (fun th -> REWRITE_TAC[th]) THENL [EXPAND_TAC "r2" THEN CONV_TAC WORD_BLAST; ALL_TAC] THEN
   TRY(SUBGOAL_THEN `qq0:int128 = word_join (xlh:64 word) (xll:64 word)`
    (fun th -> REWRITE_TAC[th]) THENL
    [EXPAND_TAC "xll" THEN EXPAND_TAC "xlh" THEN CONV_TAC WORD_BLAST; ALL_TAC]) THEN
   CONV_TAC WORD_BLAST;
   ALL_TAC] THEN
  ABBREV_TAC `gval:int128 = polyval_dot (word_xor (word_bytereverse xi)
    (word_bytereverse cph)) (byteswap128 h)` THEN
  (* 342 ext (half-swap), 343 rev64 -> Q19 = word_bytereverse gval *)
  ARM_VSTEPS_FOLD_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (342--343) THEN
  SUBGOAL_THEN `read Q19 (s343:armstate) = word_bytereverse (gval:int128)`
    (fun th -> RULE_ASSUM_TAC(fun asm ->
       if (try lhs(concl asm) = `read Q19 s343` with _ -> false)
       then th else asm) THEN ASSUME_TAC th) THENL
  [FIRST_ASSUM(fun th ->
     if is_eq(concl th) && (try lhs(concl th) = `read Q19 s343` with _ -> false)
     then GEN_REWRITE_TAC LAND_CONV [th] else NO_TAC) THEN CONV_TAC WORD_BLAST;
   ALL_TAC] THEN
  (* 344 = str q19,[x3] (tag store); exit at pc+4528 *)
  ARM_VSTEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC [344] THEN
  DISCARD_COUNTER_ONLY_TAC THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
  [CONJ_TAC THENL
    [EXPAND_TAC "gval" THEN AP_TERM_TAC THEN REWRITE_TAC[GHASH_1BLOCK_CORRECT];
     ivtac];
   REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
   REPEAT CONJ_TAC THEN MONOTONE_MAYCHANGE_TAC THEN ASM_REWRITE_TAC[]];;


let WB_TAIL_2_TAC ivtac =
  ARM_STEPS_RESOLVE_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (266--277) THEN
  ARM_STEPS_RESOLVE_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (278--313) THEN
  (* === more_than_1 block-0 GHASH round; capture block-0 PT at s319 === *)
  ARM_STEPS_FOLD_KEEPGH_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (314--319) THEN
  SUBGOAL_THEN `read Q12 (s319:armstate) = word_xor cph0 (aes256_encrypt (ctr0:int128)
      [k0:int128;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14])`
    (fun th -> RULE_ASSUM_TAC(fun asm ->
       if (try lhs(concl asm) = `read Q12 s319` with _ -> false)
       then th else asm) THEN ASSUME_TAC th) THENL
  [FIRST_ASSUM(fun th ->
     if is_eq(concl th) && (try lhs(concl th) = `read Q12 s319` with _ -> false)
     then GEN_REWRITE_TAC LAND_CONV [th] else NO_TAC) THEN
   REWRITE_TAC[GSYM AES256_XOR_ENCRYPT_RECONSTRUCT] THEN CONV_TAC WORD_RULE;
   ALL_TAC] THEN
  (* s320 = st1 v12,[x2],#16 (block-0 PT store); carry readback across discard *)
  ARM_VSTEPS_FOLD_TAC AESV8_GCM_8X_DEC_256_WB_EXEC [320] THEN
  FIRST_X_ASSUM(fun th ->
    if (try lhs(concl th) = `read (memory :> bytes128 out_p) s320` with _ -> false)
    then MP_TAC th else NO_TAC) THEN
  DISCARD_OLDSTATE_KEEPGH_TAC "s320" THEN DISCH_TAC THEN
  (* 321-325: block-1 PT lands in Q12 via eor3 v12,v9,v7,v29; capture with
     GCM_CTR_INC_LANES folding the keystream input to gcm_ctr_inc ctr0 *)
  ARM_STEPS_FOLD_KEEPGH_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (321--325) THEN
  SUBGOAL_THEN `read Q12 (s325:armstate) = word_xor cph1 (aes256_encrypt
      (gcm_ctr_inc ctr0:int128)
      [k0:int128;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14])`
    (fun th -> RULE_ASSUM_TAC(fun asm ->
       if (try lhs(concl asm) = `read Q12 s325` with _ -> false)
       then th else asm) THEN ASSUME_TAC th) THENL
  [FIRST_ASSUM(fun th ->
     if is_eq(concl th) && (try lhs(concl th) = `read Q12 s325` with _ -> false)
     then GEN_REWRITE_TAC LAND_CONV [th] else NO_TAC) THEN
   REWRITE_TAC[GSYM AES256_XOR_ENCRYPT_RECONSTRUCT] THEN CONV_TAC WORD_RULE;
   ALL_TAC] THEN
  (* 326-347: block-1 GHASH round + start of shared reduction *)
  ARM_STEPS_FOLD_KEEPGH_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (326--347) THEN
  (* s348 = str q12,[x2] (block-1 PT store).  Plain VSTEPS (the FOLD variant's
     simplifier chokes here); carry BOTH out_p readbacks across the discard. *)
  ARM_VSTEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC [348] THEN
  FIRST_X_ASSUM(fun th ->
    if (try lhs(concl th) = `read (memory :> bytes128 (word_add out_p (word 16))) s348` with _ -> false)
    then MP_TAC th else NO_TAC) THEN
  FIRST_X_ASSUM(fun th ->
    if (try lhs(concl th) = `read (memory :> bytes128 out_p) s348` with _ -> false)
    then MP_TAC th else NO_TAC) THEN
  DISCARD_OLDSTATE_KEEPGH_TAC "s348" THEN DISCH_TAC THEN DISCH_TAC THEN
  (* 349-355: single Prop3 reduction folding both blocks -> bridge at s355 *)
  ARM_STEPS_FOLD_KEEPGH_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (349--355) THEN
  (* === GMULT2 bridge at s355 (pc+4516, post eor v19,v19,v18) === *)
  SUBGOAL_THEN
    `read Q19 (s355:armstate) =
     ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
       [word_bytereverse cph0; word_bytereverse cph1]`
    (fun th -> RULE_ASSUM_TAC(fun asm ->
       if (try lhs(concl asm) = `read Q19 s355` with _ -> false)
       then th else asm) THEN ASSUME_TAC th) THENL
  [FIRST_ASSUM(fun th ->
     if is_eq(concl th) && (try lhs(concl th) = `read Q19 s355` with _ -> false)
     then GEN_REWRITE_TAC LAND_CONV [th] else NO_TAC) THEN
   WB2_GMULT2_BRIDGE_TAC;
   ALL_TAC] THEN
  ABBREV_TAC `gval:int128 = ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
      [word_bytereverse cph0; word_bytereverse cph1]` THEN
  (* 356 ext (half-swap), 357 rev64 -> Q19 = word_bytereverse gval *)
  ARM_VSTEPS_FOLD_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (356--357) THEN
  SUBGOAL_THEN `read Q19 (s357:armstate) = word_bytereverse (gval:int128)`
    (fun th -> RULE_ASSUM_TAC(fun asm ->
       if (try lhs(concl asm) = `read Q19 s357` with _ -> false)
       then th else asm) THEN ASSUME_TAC th) THENL
  [FIRST_ASSUM(fun th ->
     if is_eq(concl th) && (try lhs(concl th) = `read Q19 s357` with _ -> false)
     then GEN_REWRITE_TAC LAND_CONV [th] else NO_TAC) THEN CONV_TAC WORD_BLAST;
   ALL_TAC] THEN
  (* 358 = str q19,[x3] (tag store); exit at pc+4528 *)
  ARM_VSTEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC [358] THEN
  DISCARD_COUNTER_ONLY_TAC THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
  [ivtac;
   REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
   REPEAT CONJ_TAC THEN MONOTONE_MAYCHANGE_TAC THEN ASM_REWRITE_TAC[]];;


let WB_TAIL_3_TAC ivtac =
  ARM_STEPS_RESOLVE_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (266--277) THEN
  ARM_STEPS_RESOLVE_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (278--309)  THEN
  ARM_STEPS_FOLD_Q18LATEST_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (310--359) THEN
  ABBREV_TAC `midacc:int128 = read Q18 s359` THEN
  FIRST_X_ASSUM(fun th ->
    if (try lhs(concl th) = `midacc:int128` with _ -> false)
    then ASSUME_TAC (SYM th) else NO_TAC) THEN
  ARM_STEPS_FOLD_KEEPGH_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (360--366) THEN
  SUBGOAL_THEN
    `read Q19 (s366:armstate) =
     ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
       [word_bytereverse cph0; word_bytereverse cph1; word_bytereverse cph2]`
    (fun th -> RULE_ASSUM_TAC(fun asm ->
       if (try lhs(concl asm) = `read Q19 s366` with _ -> false)
       then th else asm) THEN ASSUME_TAC th) THENL
  [FIRST_ASSUM(fun th ->
     if is_eq(concl th) && (try lhs(concl th) = `read Q19 s366` with _ -> false)
     then GEN_REWRITE_TAC LAND_CONV [th] else NO_TAC) THEN
   (fun (asl,w) ->
     let gmult3_dec = REWRITE_RULE[LET_DEF;LET_END_DEF]
       (SPECL [`word_xor (word_bytereverse xi) (word_bytereverse cph0):int128`; `byteswap128 h3:int128`;
               `word_bytereverse cph1:int128`; `byteswap128 h2:int128`;
               `word_bytereverse cph2:int128`; `byteswap128 h:int128`] GMULT3_FULL_CORRECT_BA) in
     let h2asm = snd(List.find(fun(_,th)->try lhs(concl th)=`byteswap128 h2` with _->false) asl) in
     let h3asm = snd(List.find(fun(_,th)->try lhs(concl th)=`byteswap128 h3` with _->false) asl) in
     (GEN_REWRITE_TAC RAND_CONV
        [TRANS (MP spec_to_byteform_wb3 (CONJ h2asm h3asm)) (GSYM gmult3_dec)]) (asl,w)) THEN
   REWRITE_TAC[WORD_XOR_0; WORD_XOR_0_LEFT] THEN
   REWRITE_TAC[byteswap128] THEN REWRITE_TAC[WORD_BYTEREVERSE_REVERSEFIELDS] THEN
   REWRITE_TAC[WORD_INSERT_SUBWORD; WORD_SUBWORD_SUBWORD] THEN
   REWRITE_TAC[SUBWORD_XOR_JOIN_DIST] THEN
   REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES; RF8_SUBWORD] THEN
   REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES] THEN
   REWRITE_TAC[karatsuba_mid] THEN
   ABBREV_INNER_PMULS_TAC THEN MERGE_2BLK_TAC THEN MERGE_ANY_TAC THEN
   (fun (asl,w) ->
     let (_,th) = List.find (fun (_,th) ->
       try rand(concl th) = `midacc:int128` && is_eq(concl th) with _ -> false) asl in
     GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [SYM th] (asl,w)) THEN
   ABBREV_INNER_PMULS_TAC THEN MERGE_2BLK_TAC THEN (* MERGE_ANY dropped: AUTO_MERGE below subsumes it (refine-091) *)
   AUTO_MERGE_MIDS_KM_TAC THEN
   WA_UNIFY_BB_TAC THEN ABBREV_WAWV_TAC THEN
   REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES; WORD_SUBWORD_XOR] THEN
   GEN_REWRITE_TAC ONCE_DEPTH_CONV [QQ0SPLIT] THEN
   REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES; WORD_SUBWORD_XOR] THEN
   REWRITE_TAC[JOIN_EQ_SPLIT] THEN CONJ_TAC THEN LANE_FINISH_Z_TAC;
   ALL_TAC] THEN
  ABBREV_TAC `gval:int128 = ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
      [word_bytereverse cph0; word_bytereverse cph1; word_bytereverse cph2]` THEN
  ARM_VSTEPS_FOLD_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (367--368) THEN
  SUBGOAL_THEN `read Q19 (s368:armstate) = word_bytereverse (gval:int128)`
    (fun th -> RULE_ASSUM_TAC(fun asm ->
       if (try lhs(concl asm) = `read Q19 s368` with _ -> false)
       then th else asm) THEN ASSUME_TAC th) THENL
  [FIRST_ASSUM(fun th ->
     if is_eq(concl th) && (try lhs(concl th) = `read Q19 s368` with _ -> false)
     then GEN_REWRITE_TAC LAND_CONV [th] else NO_TAC) THEN CONV_TAC WORD_BLAST;
   ALL_TAC] THEN
  ARM_VSTEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC [369] THEN
  DISCARD_COUNTER_ONLY_TAC THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  TRY(ivtac THEN NO_TAC) THEN
  TRY(REWRITE_TAC[GSYM AES256_XOR_ENCRYPT_RECONSTRUCT] THEN CONV_TAC WORD_RULE THEN NO_TAC) THEN
  TRY(FIRST(map (fun lanes ->
        GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [lanes] THEN
        REWRITE_TAC[GSYM AES256_XOR_ENCRYPT_RECONSTRUCT] THEN CONV_TAC WORD_RULE THEN NO_TAC)
      [GCM_CTR_INC_LANES; GCM_CTR_INC2_LANES]) THEN NO_TAC) THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REPEAT CONJ_TAC THEN MONOTONE_MAYCHANGE_TAC THEN ASM_REWRITE_TAC[];;


let WB_TAIL_4_TAC ivtac =
  ARM_STEPS_RESOLVE_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (266--277) THEN
  ARM_STEPS_RESOLVE_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (278--303)  THEN
  ARM_STEPS_FOLD_Q18LATEST_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (304--370) THEN
  ABBREV_TAC `midacc:int128 = read Q18 s370` THEN
  FIRST_X_ASSUM(fun th ->
    if (try lhs(concl th) = `midacc:int128` with _ -> false)
    then ASSUME_TAC (SYM th) else NO_TAC) THEN
  ARM_STEPS_FOLD_KEEPGH_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (371--377) THEN
  SUBGOAL_THEN
    `read Q19 (s377:armstate) =
     ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
       [word_bytereverse cph0; word_bytereverse cph1;
        word_bytereverse cph2; word_bytereverse cph3]`
    (fun th -> RULE_ASSUM_TAC(fun asm ->
       if (try lhs(concl asm) = `read Q19 s377` with _ -> false)
       then th else asm) THEN ASSUME_TAC th) THENL
  [FIRST_ASSUM(fun th ->
     if is_eq(concl th) && (try lhs(concl th) = `read Q19 s377` with _ -> false)
     then GEN_REWRITE_TAC LAND_CONV [th] else NO_TAC) THEN
   (fun (asl,w) ->
     let gmult4_dec = REWRITE_RULE[LET_DEF;LET_END_DEF]
       (SPECL [`word_xor (word_bytereverse xi) (word_bytereverse cph0):int128`; `byteswap128 h4:int128`;
               `word_bytereverse cph1:int128`; `byteswap128 h3:int128`;
               `word_bytereverse cph2:int128`; `byteswap128 h2:int128`;
               `word_bytereverse cph3:int128`; `byteswap128 h:int128`] GMULT4_FULL_CORRECT_BA) in
     let h2asm = snd(List.find(fun(_,th)->try lhs(concl th)=`byteswap128 h2` with _->false) asl) in
     let h3asm = snd(List.find(fun(_,th)->try lhs(concl th)=`byteswap128 h3` with _->false) asl) in
     let h4asm = snd(List.find(fun(_,th)->try lhs(concl th)=`byteswap128 h4` with _->false) asl) in
     (GEN_REWRITE_TAC RAND_CONV
        [TRANS (MP spec_to_byteform_wb4 (CONJ h2asm (CONJ h3asm h4asm))) (GSYM gmult4_dec)]) (asl,w)) THEN
   REWRITE_TAC[WORD_XOR_0; WORD_XOR_0_LEFT] THEN
   REWRITE_TAC[byteswap128] THEN REWRITE_TAC[WORD_BYTEREVERSE_REVERSEFIELDS] THEN
   REWRITE_TAC[WORD_INSERT_SUBWORD; WORD_SUBWORD_SUBWORD] THEN
   REWRITE_TAC[SUBWORD_XOR_JOIN_DIST] THEN
   REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES; RF8_SUBWORD] THEN
   REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES] THEN
   REWRITE_TAC[karatsuba_mid] THEN
   ABBREV_INNER_PMULS_TAC THEN MERGE_2BLK_TAC THEN MERGE_ANY_TAC THEN
   (fun (asl,w) ->
     let (_,th) = List.find (fun (_,th) ->
       try rand(concl th) = `midacc:int128` && is_eq(concl th) with _ -> false) asl in
     GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [SYM th] (asl,w)) THEN
   ABBREV_INNER_PMULS_TAC THEN MERGE_2BLK_TAC THEN (* MERGE_ANY dropped: AUTO_MERGE below subsumes it (refine-091) *)
   AUTO_MERGE_MIDS_KM_TAC THEN
   WA_UNIFY_BB_TAC THEN ABBREV_WAWV_TAC THEN
   REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES; WORD_SUBWORD_XOR] THEN
   GEN_REWRITE_TAC ONCE_DEPTH_CONV [QQ0SPLIT] THEN
   REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES; WORD_SUBWORD_XOR] THEN
   REWRITE_TAC[JOIN_EQ_SPLIT] THEN CONJ_TAC THEN LANE_FINISH_Z_TAC;
   ALL_TAC] THEN
  ABBREV_TAC `gval:int128 = ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
      [word_bytereverse cph0; word_bytereverse cph1; word_bytereverse cph2;
       word_bytereverse cph3]` THEN
  ARM_VSTEPS_FOLD_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (378--379) THEN
  SUBGOAL_THEN `read Q19 (s379:armstate) = word_bytereverse (gval:int128)`
    (fun th -> RULE_ASSUM_TAC(fun asm ->
       if (try lhs(concl asm) = `read Q19 s379` with _ -> false)
       then th else asm) THEN ASSUME_TAC th) THENL
  [FIRST_ASSUM(fun th ->
     if is_eq(concl th) && (try lhs(concl th) = `read Q19 s379` with _ -> false)
     then GEN_REWRITE_TAC LAND_CONV [th] else NO_TAC) THEN CONV_TAC WORD_BLAST;
   ALL_TAC] THEN
  ARM_VSTEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC [380] THEN
  DISCARD_COUNTER_ONLY_TAC THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  TRY(ivtac THEN NO_TAC) THEN
  TRY(REWRITE_TAC[GSYM AES256_XOR_ENCRYPT_RECONSTRUCT] THEN CONV_TAC WORD_RULE THEN NO_TAC) THEN
  TRY(FIRST(map (fun lanes ->
        GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [lanes] THEN
        REWRITE_TAC[GSYM AES256_XOR_ENCRYPT_RECONSTRUCT] THEN CONV_TAC WORD_RULE THEN NO_TAC)
      [GCM_CTR_INC_LANES; GCM_CTR_INC2_LANES; GCM_CTR_INC3_LANES]) THEN NO_TAC) THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REPEAT CONJ_TAC THEN MONOTONE_MAYCHANGE_TAC THEN ASM_REWRITE_TAC[];;


let WB_TAIL_5_TAC ivtac =
  ARM_STEPS_RESOLVE_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (266--277) THEN
  ARM_STEPS_RESOLVE_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (278--297)  THEN
  ARM_STEPS_FOLD_Q18LATEST_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (298--378) THEN
  ABBREV_TAC `midacc:int128 = read Q18 s378` THEN
  FIRST_X_ASSUM(fun th ->
    if (try lhs(concl th) = `midacc:int128` with _ -> false)
    then ASSUME_TAC (SYM th) else NO_TAC) THEN
  ARM_STEPS_FOLD_KEEPGH_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (379--385) THEN
  SUBGOAL_THEN
    `read Q19 (s385:armstate) =
     ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
       [word_bytereverse cph0; word_bytereverse cph1;
        word_bytereverse cph2; word_bytereverse cph3; word_bytereverse cph4]`
    (fun th -> RULE_ASSUM_TAC(fun asm ->
       if (try lhs(concl asm) = `read Q19 s385` with _ -> false)
       then th else asm) THEN ASSUME_TAC th) THENL
  [FIRST_ASSUM(fun th ->
     if is_eq(concl th) && (try lhs(concl th) = `read Q19 s385` with _ -> false)
     then GEN_REWRITE_TAC LAND_CONV [th] else NO_TAC) THEN
   (fun (asl,w) ->
     let gmult5_dec = REWRITE_RULE[LET_DEF;LET_END_DEF]
       (SPECL [`word_xor (word_bytereverse xi) (word_bytereverse cph0):int128`; `byteswap128 h5:int128`;
               `word_bytereverse cph1:int128`; `byteswap128 h4:int128`;
               `word_bytereverse cph2:int128`; `byteswap128 h3:int128`;
               `word_bytereverse cph3:int128`; `byteswap128 h2:int128`;
               `word_bytereverse cph4:int128`; `byteswap128 h:int128`] GMULT5_FULL_CORRECT_BA) in
     let h2asm = snd(List.find(fun(_,th)->try lhs(concl th)=`byteswap128 h2` with _->false) asl) in
     let h3asm = snd(List.find(fun(_,th)->try lhs(concl th)=`byteswap128 h3` with _->false) asl) in
     let h4asm = snd(List.find(fun(_,th)->try lhs(concl th)=`byteswap128 h4` with _->false) asl) in
     let h5asm = snd(List.find(fun(_,th)->try lhs(concl th)=`byteswap128 h5` with _->false) asl) in
     (GEN_REWRITE_TAC RAND_CONV
        [TRANS (MP spec_to_byteform_wb5 (CONJ h2asm (CONJ h3asm (CONJ h4asm h5asm)))) (GSYM gmult5_dec)]) (asl,w)) THEN
   REWRITE_TAC[WORD_XOR_0; WORD_XOR_0_LEFT] THEN
   REWRITE_TAC[byteswap128] THEN REWRITE_TAC[WORD_BYTEREVERSE_REVERSEFIELDS] THEN
   REWRITE_TAC[WORD_INSERT_SUBWORD; WORD_SUBWORD_SUBWORD] THEN
   REWRITE_TAC[SUBWORD_XOR_JOIN_DIST] THEN
   REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES; RF8_SUBWORD] THEN
   REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES] THEN
   REWRITE_TAC[karatsuba_mid] THEN
   ABBREV_INNER_PMULS_TAC THEN MERGE_2BLK_TAC THEN MERGE_ANY_TAC THEN
   (fun (asl,w) ->
     let (_,th) = List.find (fun (_,th) ->
       try rand(concl th) = `midacc:int128` && is_eq(concl th) with _ -> false) asl in
     GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [SYM th] (asl,w)) THEN
   ABBREV_INNER_PMULS_TAC THEN MERGE_2BLK_TAC THEN (* MERGE_ANY dropped: AUTO_MERGE below subsumes it (refine-091) *)
   AUTO_MERGE_MIDS_KM_TAC THEN
   WA_UNIFY_BB_TAC THEN ABBREV_WAWV_TAC THEN
   REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES; WORD_SUBWORD_XOR] THEN
   GEN_REWRITE_TAC ONCE_DEPTH_CONV [QQ0SPLIT] THEN
   REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES; WORD_SUBWORD_XOR] THEN
   REWRITE_TAC[JOIN_EQ_SPLIT] THEN CONJ_TAC THEN LANE_FINISH_Z_TAC;
   ALL_TAC] THEN
  ABBREV_TAC `gval:int128 = ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
      [word_bytereverse cph0; word_bytereverse cph1; word_bytereverse cph2;
       word_bytereverse cph3; word_bytereverse cph4]` THEN
  ARM_VSTEPS_FOLD_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (386--387) THEN
  SUBGOAL_THEN `read Q19 (s387:armstate) = word_bytereverse (gval:int128)`
    (fun th -> RULE_ASSUM_TAC(fun asm ->
       if (try lhs(concl asm) = `read Q19 s387` with _ -> false)
       then th else asm) THEN ASSUME_TAC th) THENL
  [FIRST_ASSUM(fun th ->
     if is_eq(concl th) && (try lhs(concl th) = `read Q19 s387` with _ -> false)
     then GEN_REWRITE_TAC LAND_CONV [th] else NO_TAC) THEN CONV_TAC WORD_BLAST;
   ALL_TAC] THEN
  ARM_VSTEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC [388] THEN
  DISCARD_COUNTER_ONLY_TAC THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  TRY(ivtac THEN NO_TAC) THEN
  TRY(REWRITE_TAC[GSYM AES256_XOR_ENCRYPT_RECONSTRUCT] THEN CONV_TAC WORD_RULE THEN NO_TAC) THEN
  TRY(FIRST(map (fun lanes ->
        GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [lanes] THEN
        REWRITE_TAC[GSYM AES256_XOR_ENCRYPT_RECONSTRUCT] THEN CONV_TAC WORD_RULE THEN NO_TAC)
      [GCM_CTR_INC_LANES; GCM_CTR_INC2_LANES; GCM_CTR_INC3_LANES; GCM_CTR_INC4_LANES]) THEN NO_TAC) THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REPEAT CONJ_TAC THEN MONOTONE_MAYCHANGE_TAC THEN ASM_REWRITE_TAC[];;


let WB_TAIL_6_TAC ivtac =
  ARM_STEPS_RESOLVE_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (266--277) THEN
  ARM_STEPS_RESOLVE_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (278--290)  THEN
  ARM_STEPS_FOLD_Q18LATEST_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (291--386) THEN
  ABBREV_TAC `midacc:int128 = read Q18 s386` THEN
  FIRST_X_ASSUM(fun th ->
    if (try lhs(concl th) = `midacc:int128` with _ -> false)
    then ASSUME_TAC (SYM th) else NO_TAC) THEN
  ARM_STEPS_FOLD_KEEPGH_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (387--393) THEN
  SUBGOAL_THEN
    `read Q19 (s393:armstate) =
     ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
       [word_bytereverse cph0; word_bytereverse cph1; word_bytereverse cph2;
        word_bytereverse cph3; word_bytereverse cph4; word_bytereverse cph5]`
    (fun th -> RULE_ASSUM_TAC(fun asm ->
       if (try lhs(concl asm) = `read Q19 s393` with _ -> false)
       then th else asm) THEN ASSUME_TAC th) THENL
  [FIRST_ASSUM(fun th ->
     if is_eq(concl th) && (try lhs(concl th) = `read Q19 s393` with _ -> false)
     then GEN_REWRITE_TAC LAND_CONV [th] else NO_TAC) THEN
   (fun (asl,w) ->
     let gmult6_dec = REWRITE_RULE[LET_DEF;LET_END_DEF]
       (SPECL [`word_xor (word_bytereverse xi) (word_bytereverse cph0):int128`; `byteswap128 h6:int128`;
               `word_bytereverse cph1:int128`; `byteswap128 h5:int128`;
               `word_bytereverse cph2:int128`; `byteswap128 h4:int128`;
               `word_bytereverse cph3:int128`; `byteswap128 h3:int128`;
               `word_bytereverse cph4:int128`; `byteswap128 h2:int128`;
               `word_bytereverse cph5:int128`; `byteswap128 h:int128`] GMULT6_FULL_CORRECT_BA) in
     let h2asm = snd(List.find(fun(_,th)->try lhs(concl th)=`byteswap128 h2` with _->false) asl) in
     let h3asm = snd(List.find(fun(_,th)->try lhs(concl th)=`byteswap128 h3` with _->false) asl) in
     let h4asm = snd(List.find(fun(_,th)->try lhs(concl th)=`byteswap128 h4` with _->false) asl) in
     let h5asm = snd(List.find(fun(_,th)->try lhs(concl th)=`byteswap128 h5` with _->false) asl) in
     let h6asm = snd(List.find(fun(_,th)->try lhs(concl th)=`byteswap128 h6` with _->false) asl) in
     (GEN_REWRITE_TAC RAND_CONV
        [TRANS (MP spec_to_byteform_wb6 (CONJ h2asm (CONJ h3asm (CONJ h4asm (CONJ h5asm h6asm))))) (GSYM gmult6_dec)]) (asl,w)) THEN
   REWRITE_TAC[WORD_XOR_0; WORD_XOR_0_LEFT] THEN
   REWRITE_TAC[byteswap128] THEN REWRITE_TAC[WORD_BYTEREVERSE_REVERSEFIELDS] THEN
   REWRITE_TAC[WORD_INSERT_SUBWORD; WORD_SUBWORD_SUBWORD] THEN
   REWRITE_TAC[SUBWORD_XOR_JOIN_DIST] THEN
   REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES; RF8_SUBWORD] THEN
   REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES] THEN
   REWRITE_TAC[karatsuba_mid] THEN
   ABBREV_INNER_PMULS_TAC THEN MERGE_2BLK_TAC THEN MERGE_ANY_TAC THEN
   (fun (asl,w) ->
     let (_,th) = List.find (fun (_,th) ->
       try rand(concl th) = `midacc:int128` && is_eq(concl th) with _ -> false) asl in
     GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [SYM th] (asl,w)) THEN
   ABBREV_INNER_PMULS_TAC THEN MERGE_2BLK_TAC THEN (* MERGE_ANY dropped: AUTO_MERGE below subsumes it (refine-091) *)
   AUTO_MERGE_MIDS_KM_TAC THEN
   WA_UNIFY_BB_TAC THEN ABBREV_WAWV_TAC THEN
   REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES; WORD_SUBWORD_XOR] THEN
   GEN_REWRITE_TAC ONCE_DEPTH_CONV [QQ0SPLIT] THEN
   REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES; WORD_SUBWORD_XOR] THEN
   REWRITE_TAC[JOIN_EQ_SPLIT] THEN CONJ_TAC THEN LANE_FINISH_Z_TAC;
   ALL_TAC] THEN
  ABBREV_TAC `gval:int128 = ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
      [word_bytereverse cph0; word_bytereverse cph1; word_bytereverse cph2;
       word_bytereverse cph3; word_bytereverse cph4; word_bytereverse cph5]` THEN
  ARM_VSTEPS_FOLD_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (394--395) THEN
  SUBGOAL_THEN `read Q19 (s395:armstate) = word_bytereverse (gval:int128)`
    (fun th -> RULE_ASSUM_TAC(fun asm ->
       if (try lhs(concl asm) = `read Q19 s395` with _ -> false)
       then th else asm) THEN ASSUME_TAC th) THENL
  [FIRST_ASSUM(fun th ->
     if is_eq(concl th) && (try lhs(concl th) = `read Q19 s395` with _ -> false)
     then GEN_REWRITE_TAC LAND_CONV [th] else NO_TAC) THEN CONV_TAC WORD_BLAST;
   ALL_TAC] THEN
  ARM_VSTEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC [396] THEN
  DISCARD_COUNTER_ONLY_TAC THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  TRY(ivtac THEN NO_TAC) THEN
  TRY(REWRITE_TAC[GSYM AES256_XOR_ENCRYPT_RECONSTRUCT] THEN CONV_TAC WORD_RULE THEN NO_TAC) THEN
  TRY(FIRST(map (fun lanes ->
        GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [lanes] THEN
        REWRITE_TAC[GSYM AES256_XOR_ENCRYPT_RECONSTRUCT] THEN CONV_TAC WORD_RULE THEN NO_TAC)
      [GCM_CTR_INC_LANES; GCM_CTR_INC2_LANES; GCM_CTR_INC3_LANES; GCM_CTR_INC4_LANES;
       GCM_CTR_INC5_LANES]) THEN NO_TAC) THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REPEAT CONJ_TAC THEN MONOTONE_MAYCHANGE_TAC THEN ASM_REWRITE_TAC[];;


let WB_TAIL_7_TAC ivtac =
  ARM_STEPS_RESOLVE_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (266--277) THEN
  ARM_STEPS_RESOLVE_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (278--282)  THEN
  ARM_STEPS_FOLD_Q18LATEST_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (283--392) THEN
  ABBREV_TAC `midacc:int128 = read Q18 s392` THEN
  FIRST_X_ASSUM(fun th ->
    if (try lhs(concl th) = `midacc:int128` with _ -> false)
    then ASSUME_TAC (SYM th) else NO_TAC) THEN
  ARM_STEPS_FOLD_KEEPGH_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (393--399) THEN
  SUBGOAL_THEN
    `read Q19 (s399:armstate) =
     ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
       [word_bytereverse cph0; word_bytereverse cph1; word_bytereverse cph2;
        word_bytereverse cph3; word_bytereverse cph4; word_bytereverse cph5;
        word_bytereverse cph6]`
    (fun th -> RULE_ASSUM_TAC(fun asm ->
       if (try lhs(concl asm) = `read Q19 s399` with _ -> false)
       then th else asm) THEN ASSUME_TAC th) THENL
  [FIRST_ASSUM(fun th ->
     if is_eq(concl th) && (try lhs(concl th) = `read Q19 s399` with _ -> false)
     then GEN_REWRITE_TAC LAND_CONV [th] else NO_TAC) THEN
   (fun (asl,w) ->
     let gmult7_dec = REWRITE_RULE[LET_DEF;LET_END_DEF]
       (SPECL [`word_xor (word_bytereverse xi) (word_bytereverse cph0):int128`; `byteswap128 h7:int128`;
               `word_bytereverse cph1:int128`; `byteswap128 h6:int128`;
               `word_bytereverse cph2:int128`; `byteswap128 h5:int128`;
               `word_bytereverse cph3:int128`; `byteswap128 h4:int128`;
               `word_bytereverse cph4:int128`; `byteswap128 h3:int128`;
               `word_bytereverse cph5:int128`; `byteswap128 h2:int128`;
               `word_bytereverse cph6:int128`; `byteswap128 h:int128`] GMULT7_FULL_CORRECT_BA) in
     let h2asm = snd(List.find(fun(_,th)->try lhs(concl th)=`byteswap128 h2` with _->false) asl) in
     let h3asm = snd(List.find(fun(_,th)->try lhs(concl th)=`byteswap128 h3` with _->false) asl) in
     let h4asm = snd(List.find(fun(_,th)->try lhs(concl th)=`byteswap128 h4` with _->false) asl) in
     let h5asm = snd(List.find(fun(_,th)->try lhs(concl th)=`byteswap128 h5` with _->false) asl) in
     let h6asm = snd(List.find(fun(_,th)->try lhs(concl th)=`byteswap128 h6` with _->false) asl) in
     let h7asm = snd(List.find(fun(_,th)->try lhs(concl th)=`byteswap128 h7` with _->false) asl) in
     (GEN_REWRITE_TAC RAND_CONV
        [TRANS (MP spec_to_byteform_wb7 (CONJ h2asm (CONJ h3asm (CONJ h4asm (CONJ h5asm (CONJ h6asm h7asm)))))) (GSYM gmult7_dec)]) (asl,w)) THEN
   REWRITE_TAC[WORD_XOR_0; WORD_XOR_0_LEFT] THEN
   REWRITE_TAC[byteswap128] THEN REWRITE_TAC[WORD_BYTEREVERSE_REVERSEFIELDS] THEN
   REWRITE_TAC[WORD_INSERT_SUBWORD; WORD_SUBWORD_SUBWORD] THEN
   REWRITE_TAC[SUBWORD_XOR_JOIN_DIST] THEN
   REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES; RF8_SUBWORD] THEN
   REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES] THEN
   REWRITE_TAC[karatsuba_mid] THEN
   ABBREV_INNER_PMULS_TAC THEN MERGE_2BLK_TAC THEN MERGE_ANY_TAC THEN
   (fun (asl,w) ->
     let (_,th) = List.find (fun (_,th) ->
       try rand(concl th) = `midacc:int128` && is_eq(concl th) with _ -> false) asl in
     GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [SYM th] (asl,w)) THEN
   ABBREV_INNER_PMULS_TAC THEN MERGE_2BLK_TAC THEN (* MERGE_ANY dropped: AUTO_MERGE below subsumes it (refine-091) *)
   AUTO_MERGE_MIDS_KM_TAC THEN
   WA_UNIFY_BB_TAC THEN ABBREV_WAWV_TAC THEN
   REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES; WORD_SUBWORD_XOR] THEN
   GEN_REWRITE_TAC ONCE_DEPTH_CONV [QQ0SPLIT] THEN
   REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES; WORD_SUBWORD_XOR] THEN
   REWRITE_TAC[JOIN_EQ_SPLIT] THEN CONJ_TAC THEN LANE_FINISH_Z_TAC;
   ALL_TAC] THEN
  ABBREV_TAC `gval:int128 = ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
      [word_bytereverse cph0; word_bytereverse cph1; word_bytereverse cph2;
       word_bytereverse cph3; word_bytereverse cph4; word_bytereverse cph5;
       word_bytereverse cph6]` THEN
  ARM_VSTEPS_FOLD_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (400--401) THEN
  SUBGOAL_THEN `read Q19 (s401:armstate) = word_bytereverse (gval:int128)`
    (fun th -> RULE_ASSUM_TAC(fun asm ->
       if (try lhs(concl asm) = `read Q19 s401` with _ -> false)
       then th else asm) THEN ASSUME_TAC th) THENL
  [FIRST_ASSUM(fun th ->
     if is_eq(concl th) && (try lhs(concl th) = `read Q19 s401` with _ -> false)
     then GEN_REWRITE_TAC LAND_CONV [th] else NO_TAC) THEN CONV_TAC WORD_BLAST;
   ALL_TAC] THEN
  ARM_VSTEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC [402] THEN
  DISCARD_COUNTER_ONLY_TAC THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  TRY(ivtac THEN NO_TAC) THEN
  TRY(REWRITE_TAC[GSYM AES256_XOR_ENCRYPT_RECONSTRUCT] THEN CONV_TAC WORD_RULE THEN NO_TAC) THEN
  TRY(FIRST(map (fun lanes ->
        GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [lanes] THEN
        REWRITE_TAC[GSYM AES256_XOR_ENCRYPT_RECONSTRUCT] THEN CONV_TAC WORD_RULE THEN NO_TAC)
      [GCM_CTR_INC_LANES; GCM_CTR_INC2_LANES; GCM_CTR_INC3_LANES; GCM_CTR_INC4_LANES;
       GCM_CTR_INC5_LANES; GCM_CTR_INC6_LANES]) THEN NO_TAC) THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REPEAT CONJ_TAC THEN MONOTONE_MAYCHANGE_TAC THEN ASM_REWRITE_TAC[];;


let WB_TAIL_8_TAC ivtac =
  (* r=8 takes the b.gt @0xee4 into the dedicated straight-line exact-8 GHASH
     drain (.L256_dec_exact8_drain @0x11c8), NOT the shared 8-way cascade
     (which is now reached only by remainders r=1..7).  The drain is the
     more_than_7 fall-through with 14 no-ops removed (7x movi v16,#0 + 7x
     eor v8,v8,v16, all dead when every block feeds), plus one `b` rejoin to
     the common modulo at 0x1178; net -13 simulated steps vs the shared cascade.
     [opt s103] eor3-FUSED the drain accumulate chains: 3 block-pairs
     (final-6,final-5)(final-4,final-3)(final-2,final-1) each defer the 1st
     block's 3 high/low/mid products to free regs v13/v14/v15, drop its 3
     pairwise accumulate eors, and fold them into the 2nd block's 3 accumulate
     eors via `eor3 acc,acc,prodB,prodA`.  Net -9 more simulated steps (all in
     the accumulate window), so every state numbering below shifts down a
     further 9 (s379->s370, s386->s377, s388->s379, s389->s380).  XOR is
     assoc/comm so the folded Q18/Q19 at the 0x1178 rejoin are byte-identical;
     the byteform close is unchanged.  RESOLVE (266--270) auto-retargets the
     b.gt. *)
  ARM_STEPS_RESOLVE_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (266--270)  THEN
  (* stores window: Q18-latest per-step discard; readbacks self-propagate *)
  ARM_STEPS_FOLD_Q18LATEST_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (271--370) THEN
  ABBREV_TAC `midacc:int128 = read Q18 s370` THEN
  (* orient the defn tree=midacc so steppers substitute TOWARD the atom *)
  FIRST_X_ASSUM(fun th ->
    if (try lhs(concl th) = `midacc:int128` with _ -> false)
    then ASSUME_TAC (SYM th) else NO_TAC) THEN
  ARM_STEPS_FOLD_KEEPGH_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (371--377) THEN
  SUBGOAL_THEN
    `read Q19 (s377:armstate) =
     ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
       [word_bytereverse cph0; word_bytereverse cph1; word_bytereverse cph2;
        word_bytereverse cph3; word_bytereverse cph4; word_bytereverse cph5;
        word_bytereverse cph6; word_bytereverse cph7]`
    (fun th -> RULE_ASSUM_TAC(fun asm ->
       if (try lhs(concl asm) = `read Q19 s377` with _ -> false)
       then th else asm) THEN ASSUME_TAC th) THENL
  [FIRST_ASSUM(fun th ->
     if is_eq(concl th) && (try lhs(concl th) = `read Q19 s377` with _ -> false)
     then GEN_REWRITE_TAC LAND_CONV [th] else NO_TAC) THEN
      (fun (asl,w) ->
     let gmult8_dec = REWRITE_RULE[LET_DEF;LET_END_DEF]
       (SPECL [`word_xor (word_bytereverse xi) (word_bytereverse cph0):int128`; `byteswap128 h8:int128`;
               `word_bytereverse cph1:int128`; `byteswap128 h7:int128`;
               `word_bytereverse cph2:int128`; `byteswap128 h6:int128`;
               `word_bytereverse cph3:int128`; `byteswap128 h5:int128`;
               `word_bytereverse cph4:int128`; `byteswap128 h4:int128`;
               `word_bytereverse cph5:int128`; `byteswap128 h3:int128`;
               `word_bytereverse cph6:int128`; `byteswap128 h2:int128`;
               `word_bytereverse cph7:int128`; `byteswap128 h:int128`] GMULT8_FULL_CORRECT_BA) in
     let h2asm = snd(List.find(fun(_,th)->try lhs(concl th)=`byteswap128 h2` with _->false) asl) in
     let h3asm = snd(List.find(fun(_,th)->try lhs(concl th)=`byteswap128 h3` with _->false) asl) in
     let h4asm = snd(List.find(fun(_,th)->try lhs(concl th)=`byteswap128 h4` with _->false) asl) in
     let h5asm = snd(List.find(fun(_,th)->try lhs(concl th)=`byteswap128 h5` with _->false) asl) in
     let h6asm = snd(List.find(fun(_,th)->try lhs(concl th)=`byteswap128 h6` with _->false) asl) in
     let h7asm = snd(List.find(fun(_,th)->try lhs(concl th)=`byteswap128 h7` with _->false) asl) in
     let h8asm = snd(List.find(fun(_,th)->try lhs(concl th)=`byteswap128 h8` with _->false) asl) in
     (GEN_REWRITE_TAC RAND_CONV
        [TRANS (MP spec_to_byteform_wb8 (CONJ h2asm (CONJ h3asm (CONJ h4asm (CONJ h5asm (CONJ h6asm (CONJ h7asm h8asm))))))) (GSYM gmult8_dec)]) (asl,w)) THEN
      REWRITE_TAC[WORD_XOR_0; WORD_XOR_0_LEFT] THEN
      REWRITE_TAC[byteswap128] THEN REWRITE_TAC[WORD_BYTEREVERSE_REVERSEFIELDS] THEN
      REWRITE_TAC[WORD_INSERT_SUBWORD; WORD_SUBWORD_SUBWORD] THEN
      REWRITE_TAC[SUBWORD_XOR_JOIN_DIST] THEN
      REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES; RF8_SUBWORD] THEN
      REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES] THEN
      REWRITE_TAC[karatsuba_mid] THEN
      ABBREV_INNER_PMULS_TAC THEN MERGE_2BLK_TAC THEN
      MERGE_ANY_TAC THEN
   (fun (asl,w) ->
     let (_,th) = List.find (fun (_,th) ->
       try rand(concl th) = `midacc:int128` && is_eq(concl th) with _ -> false) asl in
     GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [SYM th] (asl,w)) THEN
   ABBREV_INNER_PMULS_TAC THEN MERGE_2BLK_TAC THEN (* MERGE_ANY dropped: AUTO_MERGE below subsumes it (refine-091) *)
   AUTO_MERGE_MIDS_KM_TAC THEN
   WA_UNIFY_BB_TAC THEN ABBREV_WAWV_TAC THEN
   REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES; WORD_SUBWORD_XOR] THEN
   GEN_REWRITE_TAC ONCE_DEPTH_CONV [QQ0SPLIT] THEN
   REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES; WORD_SUBWORD_XOR] THEN
   REWRITE_TAC[JOIN_EQ_SPLIT] THEN CONJ_TAC THEN LANE_FINISH_TAC;
   ALL_TAC] THEN
  ABBREV_TAC `gval:int128 = ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
      [word_bytereverse cph0; word_bytereverse cph1; word_bytereverse cph2;
       word_bytereverse cph3; word_bytereverse cph4; word_bytereverse cph5;
       word_bytereverse cph6; word_bytereverse cph7]` THEN
  ARM_VSTEPS_FOLD_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (378--379) THEN
  SUBGOAL_THEN `read Q19 (s379:armstate) = word_bytereverse (gval:int128)`
    (fun th -> RULE_ASSUM_TAC(fun asm ->
       if (try lhs(concl asm) = `read Q19 s379` with _ -> false)
       then th else asm) THEN ASSUME_TAC th) THENL
  [FIRST_ASSUM(fun th ->
     if is_eq(concl th) && (try lhs(concl th) = `read Q19 s379` with _ -> false)
     then GEN_REWRITE_TAC LAND_CONV [th] else NO_TAC) THEN CONV_TAC WORD_BLAST;
   ALL_TAC] THEN
  ARM_VSTEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC [380] THEN
  DISCARD_COUNTER_ONLY_TAC THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  TRY(ivtac THEN NO_TAC) THEN
  TRY(REWRITE_TAC[GSYM AES256_XOR_ENCRYPT_RECONSTRUCT] THEN CONV_TAC WORD_RULE THEN NO_TAC) THEN
  TRY(FIRST(map (fun lanes ->
        GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [lanes] THEN
        REWRITE_TAC[GSYM AES256_XOR_ENCRYPT_RECONSTRUCT] THEN CONV_TAC WORD_RULE THEN NO_TAC)
      [GCM_CTR_INC_LANES; GCM_CTR_INC2_LANES; GCM_CTR_INC3_LANES; GCM_CTR_INC4_LANES;
       GCM_CTR_INC5_LANES; GCM_CTR_INC6_LANES; GCM_CTR_INC7_LANES]) THEN NO_TAC) THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REPEAT CONJ_TAC THEN MONOTONE_MAYCHANGE_TAC THEN ASM_REWRITE_TAC[];;



(* ------------------------------------------------------------------------- *)
(*         Shared front WB_FRONT_BUF + the 8 recomposed band theorems        *)
(* ------------------------------------------------------------------------- *)


(* ---- scalar N-folding lemmas (the two nblk-dependent scalar ops) ---------- *)
let USHR_128NBLK = prove
 (`!nblk. 1 <= nblk /\ nblk <= 8
        ==> word_ushr (word (128 * nblk):int64) 3 = word (16 * nblk)`,
  GEN_TAC THEN
  REWRITE_TAC[ARITH_RULE `1 <= n /\ n <= 8 <=>
    n = 1 \/ n = 2 \/ n = 3 \/ n = 4 \/ n = 5 \/ n = 6 \/ n = 7 \/ n = 8`] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN
  CONV_TAC WORD_REDUCE_CONV);;

let AND_MASK_16NBLK = prove
 (`!nblk. 1 <= nblk /\ nblk <= 8
        ==> word_and (word_sub (word (16 * nblk)) (word 1))
                     (word 18446744073709551488):int64 = word 0`,
  GEN_TAC THEN
  REWRITE_TAC[ARITH_RULE `1 <= n /\ n <= 8 <=>
    n = 1 \/ n = 2 \/ n = 3 \/ n = 4 \/ n = 5 \/ n = 6 \/ n = 7 \/ n = 8`] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN
  CONV_TAC WORD_REDUCE_CONV);;

(* ---- input-lane bridge (local re-proof of le3block's lemma; only needs
        READ_BYTES_AND_BYTE128_MERGE from aes_xts_common) -------------------- *)
let INPUT_BYTES_TO_BYTE128_LANES = prove
 (`!n (in_p:int64) (x:byte list) s.
    16 * n <= LENGTH x /\
    read (memory :> bytes (in_p, 16 * n)) s = num_of_bytelist (SUB_LIST (0, 16 * n) x)
    ==> !k. k < n ==> read (memory :> bytes128 (word_add in_p (word (16 * k)))) s =
                      bytes_to_int128 (SUB_LIST (16 * k, 16) x)`,
  INDUCT_TAC THENL [REWRITE_TAC[LT]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`in_p:int64`; `16 * n`; `x:byte list`; `s:armstate`] READ_BYTES_AND_BYTE128_MERGE) THEN
  ANTS_TAC THENL [REWRITE_TAC[ARITH_RULE `16 * n + 16 = 16 * SUC n`] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ANTS_TAC THENL [REWRITE_TAC[ARITH_RULE `16 * n + 16 = 16 * SUC n`] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  STRIP_TAC THEN
  X_GEN_TAC `k:num` THEN REWRITE_TAC[LT] THEN STRIP_TAC THENL
   [ASM_REWRITE_TAC[];
    FIRST_X_ASSUM(MP_TAC o SPECL [`in_p:int64`; `x:byte list`; `s:armstate`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `k:num`) THEN ASM_REWRITE_TAC[]]);;

(* ---- shared front tactics ------------------------------------------------- *)
(* Buffer prep: SUB_LIST length collapse, block-0 lane, the two scalar facts. *)
let WB_FRONT_PREP_BUF_TAC =
  SUBGOAL_THEN `SUB_LIST (0, 16 * nblk) (ibytes:byte list) = ibytes` ASSUME_TAC THENL
   [MATCH_MP_TAC SUB_LIST_LENGTH_IMPLIES THEN ASM_REWRITE_TAC[LE_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN `read (memory :> bytes128 in_p) s0 = bytes_to_int128 (SUB_LIST (0,16) ibytes)` ASSUME_TAC THENL
   [MP_TAC(SPECL [`nblk:num`; `in_p:int64`; `ibytes:byte list`; `s0:armstate`] INPUT_BYTES_TO_BYTE128_LANES) THEN
    ASM_REWRITE_TAC[LE_REFL] THEN DISCH_THEN(MP_TAC o SPEC `0`) THEN
    ASM_SIMP_TAC[LE_1; MULT_CLAUSES; WORD_ADD_0]; ALL_TAC] THEN
  SUBGOAL_THEN `word_ushr (word (128 * nblk):int64) 3 = word (16 * nblk)` ASSUME_TAC THENL
   [MATCH_MP_TAC USHR_128NBLK THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `word_and (word_sub (word (16 * nblk)) (word 1)) (word 18446744073709551488):int64 = word 0` ASSUME_TAC THENL
   [MATCH_MP_TAC AND_MASK_16NBLK THEN ASM_REWRITE_TAC[]; ALL_TAC];;

(* Union front steps 1..265: keeps ALL Q0..Q7 towers (discard only Q30 piles).
   The single b.ge (step 260) is nblk-independent (X5 collapses to in_p by s173
   via AND_MASK_16NBLK, so cmp@240 is in_p vs in_p). *)
let WB_FRONT_STEP_TAC =
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (1--5) THEN
  EVERY(map (fun i -> ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (i--i) THEN
             GCM_SIMD_SIMPLIFY_TAC) (6--30)) THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (31--84) THEN mk_discard2 [30] THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (85--173) THEN mk_discard2 [30] THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (174--177) THEN
  GCM_SIMD_SIMPLIFY_TAC THEN mk_discard2 [30] THEN
  ARM_VSTEPS_FOLD_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (178--189) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[Q19_BREVXI]) THEN mk_discard2 [30] THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (190--254) THEN
  mk_discard2 [30] THEN GCM_SIMD_SIMPLIFY_TAC THEN
  ARM_VSTEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC [255] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[INT_SUB_REFL; INT_OF_NUM_EQ]) THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (256--265) THEN
  GCM_SIMD_SIMPLIFY_TAC THEN mk_discard2 [30] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
    `word_sub (word_add in_p (word (16 * nblk))) in_p:int64 = word (16 * nblk)`]);;

(* ---- WB_FRONT_BUF construction (route A: harvest the s265 state) ----------
   The postcond has 8 raw 13-round aese/aesmc towers (~2666ch each) that cannot
   be hand-written, and the printed statement does NOT reparse (type annots
   lost).  So: run the front once against a MINIMAL postcond, harvest the s265
   assumptions into the real postcond term, assemble the goal, prove.  The
   front therefore simulates twice (once to harvest, once in the proof). ---- *)

let wb_front_pre_tm = `\s. aligned_bytes_loaded s (word pc) aesv8_gcm_8x_dec_256_wb_mc /\
          read PC s = word (pc + 0x20) /\ read SP s = stackpointer /\
          C_ARGUMENTS [in_p; word (128 * nblk); out_p; xi_p; ivec_p; key_p; htbl_p] s /\
          read (memory :> bytes (in_p, 16 * nblk)) s = num_of_bytelist ibytes /\
          read (memory :> bytes128 xi_p) s = xi /\
          read (memory :> bytes128 ivec_p) s = ctr0 /\
          read (memory :> bytes128 key_p) s = k0 /\
          read (memory :> bytes128 (word_add key_p (word 16))) s = k1 /\
          read (memory :> bytes128 (word_add key_p (word 32))) s = k2 /\
          read (memory :> bytes128 (word_add key_p (word 48))) s = k3 /\
          read (memory :> bytes128 (word_add key_p (word 64))) s = k4 /\
          read (memory :> bytes128 (word_add key_p (word 80))) s = k5 /\
          read (memory :> bytes128 (word_add key_p (word 96))) s = k6 /\
          read (memory :> bytes128 (word_add key_p (word 112))) s = k7 /\
          read (memory :> bytes128 (word_add key_p (word 128))) s = k8 /\
          read (memory :> bytes128 (word_add key_p (word 144))) s = k9 /\
          read (memory :> bytes128 (word_add key_p (word 160))) s = k10 /\
          read (memory :> bytes128 (word_add key_p (word 176))) s = k11 /\
          read (memory :> bytes128 (word_add key_p (word 192))) s = k12 /\
          read (memory :> bytes128 (word_add key_p (word 208))) s = k13 /\
          read (memory :> bytes128 (word_add key_p (word 224))) s = k14 /\
          htable_mem_dec h htbl_p s`;;

let wb_front_frame_tm = `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
      MAYCHANGE [memory :> bytes(out_p:int64, 16 * nblk); memory :> bytes(xi_p:int64, 16);
                 memory :> bytes(ivec_p:int64, 16); memory :> bytes(word_add stackpointer (word 64):int64, 16)] ,,
      MAYCHANGE [Q0;Q1;Q2;Q3;Q4;Q5;Q6;Q7;Q8;Q9;Q10;Q11;Q12;Q13;Q14;Q15;
                 Q16;Q17;Q18;Q19;Q20;Q21;Q22;Q23;Q24;Q25;Q26;Q27;Q28;Q29;Q30;Q31]`;;

(* FUSED SPLICE (STEP 4): 1<=nblk -> 5<=nblk.  WB_FRONT_BUF (built from this hyp
   set) is now consumed ONLY by prove_band 5..8 (bands 1..4 take the fused path
   via the step-8 b.le and are proved by the fused-band theorems).  The concrete
   bands supply nblk in {5,6,7,8} so 5<=nblk discharges by NUM_REDUCE; and the
   union-front derivation (wbn_front_hyps_uni_tm) already prepends 5<=nblk. *)
let wb_front_hyps_tm = `5 <= nblk /\ nblk <= 8 /\ LENGTH (ibytes:byte list) = 16 * nblk /\
    aligned 16 stackpointer /\
    nonoverlapping (word pc, LENGTH aesv8_gcm_8x_dec_256_wb_mc) (stackpointer:int64, 80) /\
    nonoverlapping (word pc, LENGTH aesv8_gcm_8x_dec_256_wb_mc) (out_p:int64, 16 * nblk) /\
    nonoverlapping (word pc, LENGTH aesv8_gcm_8x_dec_256_wb_mc) (xi_p:int64, 16) /\
    nonoverlapping (word pc, LENGTH aesv8_gcm_8x_dec_256_wb_mc) (ivec_p:int64, 16) /\
    nonoverlapping (ivec_p, 16) (in_p:int64, 16 * nblk) /\
    nonoverlapping (ivec_p, 16) (key_p:int64, 240) /\
    nonoverlapping (ivec_p, 16) (htbl_p:int64, 192) /\
    nonoverlapping (in_p, 16 * nblk) (stackpointer, 80) /\
    nonoverlapping (key_p, 240) (stackpointer, 80) /\
    nonoverlapping (htbl_p, 192) (stackpointer, 80) /\
    nonoverlapping (ivec_p, 16) (stackpointer, 80) /\
    nonoverlapping (xi_p, 16) (in_p, 16 * nblk) /\
    nonoverlapping (xi_p, 16) (key_p, 240) /\
    nonoverlapping (xi_p, 16) (htbl_p, 192) /\
    nonoverlapping (xi_p, 16) (stackpointer, 80)`;;

let wb_front_vars = [`pc:num`;`stackpointer:int64`;`out_p:int64`;`xi_p:int64`;`ivec_p:int64`;
            `in_p:int64`;`key_p:int64`;`htbl_p:int64`;`nblk:num`;`ibytes:byte list`;
            `xi:int128`;`ctr0:int128`;`k0:int128`;`k1:int128`;`k2:int128`;`k3:int128`;
            `k4:int128`;`k5:int128`;`k6:int128`;`k7:int128`;`k8:int128`;`k9:int128`;
            `k10:int128`;`k11:int128`;`k12:int128`;`k13:int128`;`k14:int128`;`h:int128`];;

let mk_wb_front_goal postcond =
  let ens = subst [wb_front_pre_tm,`PPP:armstate->bool`; postcond,`QQQ:armstate->bool`;
                   wb_front_frame_tm,`CCC:armstate->armstate->bool`]
              `ensures arm PPP QQQ CCC` in
  list_mk_forall(wb_front_vars, mk_imp(wb_front_hyps_tm, ens));;

(* Harvest all `read _ s = _` facts PLUS the aligned_bytes_loaded conjunct
   (WITHOUT it the back-leg tails cannot step: "ARM_CONV: can't find
   aligned_bytes_loaded"). *)
let build_state_postcond_tms2 sname (asl:term list) =
  let sv = mk_var(sname,`:armstate`) in
  let s = mk_var("s",`:armstate`) in
  let keep c =
    (is_eq c && (match lhs c with
       | Comb(Comb(Const("read",_),_),st) -> st = sv | _ -> false))
    || (match c with
        | Comb(Comb(Comb(Const("aligned_bytes_loaded",_),st),_),_) -> st = sv
        | _ -> false) in
  let kept = filter keep asl in
  let albl,reads = partition (fun c -> not(is_eq c)) kept in
  mk_abs(s, vsubst [s,sv] (end_itlist (curry mk_conj) (albl @ reads)));;

let wb_front_init_tac =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS] THEN ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WB_MC_LEN]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[C_ARGUMENTS]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_dec]) THEN
  RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV let_CONV)) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o check(is_conj o concl)) THEN
  WB_FRONT_PREP_BUF_TAC THEN WB_FRONT_STEP_TAC;;

(* The s265 postcondition, embedded as a fully-type-annotated literal so the
   front simulates ONCE (in the WB_FRONT_BUF proof) instead of twice (the old
   harvest pass re-ran the same 265-step sim, ~232s wasted per cold load).
   COMPACT FORM: the 8 in-flight keystream towers are folded to
   aes13 (gcm_ctr_inc^i ctr0) k0..k13 (GSYM aes13 + GSYM GCM_CTR_INCi_LANES),
   which shrinks the raw harvested term from ~83k to ~19k chars and makes the
   Q-register conjuncts readable.  The WB_FRONT_BUF proof applies the same fold
   to the simulated assumptions (wb_front_fold_tac) before final-state matching.
   REGENERATION (if the front or its keep-profile changes): re-enable the
   harvest pass below, fold with
     (REWRITE_CONV[GSYM aes13] THENC REWRITE_CONV(map GSYM wb_ctr_lanes_thms)),
   then print with print_types_of_subterms := 2 and replace every
   "(&:num->int)" with "(int_of_num:num->int)" (the bare & does not reparse);
   verify aconv against the folded harvested term.
     let wb_front_postcond_harvested =
       let min_goal = mk_wb_front_goal `\s:armstate. read PC s = word (pc + 3828)` in
       let _ = g min_goal in
       let _ = e wb_front_init_tac in
       let (asl265,_) = top_goal() in
       build_state_postcond_tms2 "s265" asl265;;  *)
let wb_ctr_lanes_thms =
  [GCM_CTR_INC_LANES; GCM_CTR_INC2_LANES; GCM_CTR_INC3_LANES; GCM_CTR_INC4_LANES;
   GCM_CTR_INC5_LANES; GCM_CTR_INC6_LANES; GCM_CTR_INC7_LANES];;
(* fold the raw simulated assumptions onto the compact postcondition shapes *)
let wb_front_fold_tac =
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM aes13]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE(map GSYM wb_ctr_lanes_thms));;
(* the RAW counter accumulator kept in v30 (HOISTED here so that
   the ivec M2 EDIT-0 Q30 conjunct in wb_front_postcond below can
   reference it -- it was formerly in Sec 2).  byte-grouped rep with top 32-bit
   lane incremented by w.  The body's first instr `rev32 v5,v30` reads it, so the
   Sec-4 invariant pins Q30 = gcm_ctr_raw (word (8*i+13)) ctr0.  Its algebra
   lemmas (SUBW_RAW_*, GCM_CTR_RAW_INCR, REV32_FOLD_TAC) are body-only, Sec 9b.
   rev32(gcm_ctr_raw w ctr0) = gcm_ctr_add w ctr0 (the AES input for block w);
   word_add (gcm_ctr_raw w ctr0) (word 2^96) = gcm_ctr_raw (word_add w 1) ctr0. *)
let gcm_ctr_raw_def = new_definition
 `gcm_ctr_raw (w:32 word) (ctr0:int128) : int128 =
   word_join
    (word_join
      (word_add
        (word_join
          (word_join (word_subword ctr0 (96,8):8 word) (word_subword ctr0 (104,8):8 word):16 word)
          (word_join (word_subword ctr0 (112,8):8 word) (word_subword ctr0 (120,8):8 word):16 word):32 word)
        w)
      (word_join (word_join (word_subword ctr0 (64,8):8 word) (word_subword ctr0 (72,8):8 word):16 word)
        (word_join (word_subword ctr0 (80,8):8 word) (word_subword ctr0 (88,8):8 word):16 word):32 word):64 word)
    (word_join
      (word_join (word_join (word_subword ctr0 (32,8):8 word) (word_subword ctr0 (40,8):8 word):16 word)
        (word_join (word_subword ctr0 (48,8):8 word) (word_subword ctr0 (56,8):8 word):16 word):32 word)
      (word_join (word_join (word_subword ctr0 (0,8):8 word) (word_subword ctr0 (8,8):8 word):16 word)
        (word_join (word_subword ctr0 (16,8):8 word) (word_subword ctr0 (24,8):8 word):16 word):32 word):64 word):int128`;;

let wb_front_postcond = parse_term {|\(s:armstate).
    (aligned_bytes_loaded:armstate->(64)word->((8)word)list->bool)
    (s:armstate)
    ((word:num->(64)word) (pc:num))
    (aesv8_gcm_8x_dec_256_wb_mc:((8)word)list) /\
    (read:(armstate,(64)word)component->armstate->(64)word)
    (PC:(armstate,(64)word)component)
    (s:armstate) =
    (word:num->(64)word) ((pc:num) + 3828) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q24:(armstate,(128)word)component)
    (s:armstate) =
    (word_join:(64)word->(64)word->(128)word)
    ((karatsuba_mid:(128)word->(64)word)
    ((byteswap128:(128)word->(128)word)
    ((polyval_dot:(128)word->(128)word->(128)word)
     ((polyval_dot:(128)word->(128)word->(128)word)
      ((polyval_dot:(128)word->(128)word->(128)word)
       ((polyval_dot:(128)word->(128)word->(128)word)
        ((polyval_dot:(128)word->(128)word->(128)word)
         ((polyval_dot:(128)word->(128)word->(128)word)
          ((polyval_dot:(128)word->(128)word->(128)word)
           ((byteswap128:(128)word->(128)word) (h:(128)word))
          ((byteswap128:(128)word->(128)word) (h:(128)word)))
         ((byteswap128:(128)word->(128)word) (h:(128)word)))
        ((byteswap128:(128)word->(128)word) (h:(128)word)))
       ((byteswap128:(128)word->(128)word) (h:(128)word)))
      ((byteswap128:(128)word->(128)word) (h:(128)word)))
     ((byteswap128:(128)word->(128)word) (h:(128)word)))
    ((byteswap128:(128)word->(128)word) (h:(128)word)))))
    ((karatsuba_mid:(128)word->(64)word)
    ((byteswap128:(128)word->(128)word)
    ((polyval_dot:(128)word->(128)word->(128)word)
     ((polyval_dot:(128)word->(128)word->(128)word)
      ((polyval_dot:(128)word->(128)word->(128)word)
       ((polyval_dot:(128)word->(128)word->(128)word)
        ((polyval_dot:(128)word->(128)word->(128)word)
         ((polyval_dot:(128)word->(128)word->(128)word)
          ((byteswap128:(128)word->(128)word) (h:(128)word))
         ((byteswap128:(128)word->(128)word) (h:(128)word)))
        ((byteswap128:(128)word->(128)word) (h:(128)word)))
       ((byteswap128:(128)word->(128)word) (h:(128)word)))
      ((byteswap128:(128)word->(128)word) (h:(128)word)))
     ((byteswap128:(128)word->(128)word) (h:(128)word)))
    ((byteswap128:(128)word->(128)word) (h:(128)word))))) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q25:(armstate,(128)word)component)
    (s:armstate) =
    (byteswap128:(128)word->(128)word)
    ((polyval_dot:(128)word->(128)word->(128)word)
     ((polyval_dot:(128)word->(128)word->(128)word)
      ((polyval_dot:(128)word->(128)word->(128)word)
       ((polyval_dot:(128)word->(128)word->(128)word)
        ((polyval_dot:(128)word->(128)word->(128)word)
         ((polyval_dot:(128)word->(128)word->(128)word)
          ((polyval_dot:(128)word->(128)word->(128)word)
           ((byteswap128:(128)word->(128)word) (h:(128)word))
          ((byteswap128:(128)word->(128)word) (h:(128)word)))
         ((byteswap128:(128)word->(128)word) (h:(128)word)))
        ((byteswap128:(128)word->(128)word) (h:(128)word)))
       ((byteswap128:(128)word->(128)word) (h:(128)word)))
      ((byteswap128:(128)word->(128)word) (h:(128)word)))
     ((byteswap128:(128)word->(128)word) (h:(128)word)))
    ((byteswap128:(128)word->(128)word) (h:(128)word))) /\
    ((read:(armstate,bool)component->armstate->bool)
     (NF:(armstate,bool)component)
     (s:armstate) <=>
     (ival:(64)word->int)
     ((word_sub:(64)word->(64)word->(64)word)
      ((word:num->(64)word) (16 * (nblk:num)))
     ((word:num->(64)word) 112)) <
     (int_of_num:num->int)0) /\
    ((read:(armstate,bool)component->armstate->bool)
     (ZF:(armstate,bool)component)
     (s:armstate) <=>
     (val:(64)word->num)
     ((word_sub:(64)word->(64)word->(64)word)
      ((word:num->(64)word) (16 * (nblk:num)))
     ((word:num->(64)word) 112)) =
     0) /\
    ((read:(armstate,bool)component->armstate->bool)
     (CF:(armstate,bool)component)
     (s:armstate) <=>
     112 <= (val:(64)word->num) ((word:num->(64)word) (16 * (nblk:num)))) /\
    ((read:(armstate,bool)component->armstate->bool)
     (VF:(armstate,bool)component)
     (s:armstate) <=>
     ~((ival:(64)word->int) ((word:num->(64)word) (16 * (nblk:num))) -
       (int_of_num:num->int)112 =
       (ival:(64)word->int)
       ((word_sub:(64)word->(64)word->(64)word)
        ((word:num->(64)word) (16 * (nblk:num)))
       ((word:num->(64)word) 112)))) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q16:(armstate,(128)word)component)
    (s:armstate) =
    (word_subword:(256)word->num#num->(128)word)
    ((word_join:(128)word->(128)word->(256)word)
     ((word_bytereverse:(128)word->(128)word) (xi:(128)word))
    ((word_bytereverse:(128)word->(128)word) (xi:(128)word)))
    (64,128) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q7:(armstate,(128)word)component)
    (s:armstate) =
    (aes13:(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word)
    ((gcm_ctr_inc:(128)word->(128)word)
    ((gcm_ctr_inc:(128)word->(128)word)
    ((gcm_ctr_inc:(128)word->(128)word)
    ((gcm_ctr_inc:(128)word->(128)word)
    ((gcm_ctr_inc:(128)word->(128)word)
    ((gcm_ctr_inc:(128)word->(128)word)
    ((gcm_ctr_inc:(128)word->(128)word) (ctr0:(128)word))))))))
    (k0:(128)word)
    (k1:(128)word)
    (k2:(128)word)
    (k3:(128)word)
    (k4:(128)word)
    (k5:(128)word)
    (k6:(128)word)
    (k7:(128)word)
    (k8:(128)word)
    (k9:(128)word)
    (k10:(128)word)
    (k11:(128)word)
    (k12:(128)word)
    (k13:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q6:(armstate,(128)word)component)
    (s:armstate) =
    (aes13:(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word)
    ((gcm_ctr_inc:(128)word->(128)word)
    ((gcm_ctr_inc:(128)word->(128)word)
    ((gcm_ctr_inc:(128)word->(128)word)
    ((gcm_ctr_inc:(128)word->(128)word)
    ((gcm_ctr_inc:(128)word->(128)word)
    ((gcm_ctr_inc:(128)word->(128)word) (ctr0:(128)word)))))))
    (k0:(128)word)
    (k1:(128)word)
    (k2:(128)word)
    (k3:(128)word)
    (k4:(128)word)
    (k5:(128)word)
    (k6:(128)word)
    (k7:(128)word)
    (k8:(128)word)
    (k9:(128)word)
    (k10:(128)word)
    (k11:(128)word)
    (k12:(128)word)
    (k13:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q0:(armstate,(128)word)component)
    (s:armstate) =
    (aes13:(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word)
    (ctr0:(128)word)
    (k0:(128)word)
    (k1:(128)word)
    (k2:(128)word)
    (k3:(128)word)
    (k4:(128)word)
    (k5:(128)word)
    (k6:(128)word)
    (k7:(128)word)
    (k8:(128)word)
    (k9:(128)word)
    (k10:(128)word)
    (k11:(128)word)
    (k12:(128)word)
    (k13:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q1:(armstate,(128)word)component)
    (s:armstate) =
    (aes13:(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word)
    ((gcm_ctr_inc:(128)word->(128)word) (ctr0:(128)word))
    (k0:(128)word)
    (k1:(128)word)
    (k2:(128)word)
    (k3:(128)word)
    (k4:(128)word)
    (k5:(128)word)
    (k6:(128)word)
    (k7:(128)word)
    (k8:(128)word)
    (k9:(128)word)
    (k10:(128)word)
    (k11:(128)word)
    (k12:(128)word)
    (k13:(128)word) /\
    (read:(armstate,(64)word)component->armstate->(64)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes64:(64)word->((64)word->(8)word,(64)word)component)
     ((word_add:(64)word->(64)word->(64)word) (stackpointer:(64)word)
     ((word:num->(64)word) 64)))
    (s:armstate) =
    (word:num->(64)word) 13979173243358019584 /\
    (read:(armstate,(64)word)component->armstate->(64)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes64:(64)word->((64)word->(8)word,(64)word)component)
     ((word_add:(64)word->(64)word->(64)word) (stackpointer:(64)word)
     ((word:num->(64)word) 72)))
    (s:armstate) =
    (word:num->(64)word) 0 /\
    (read:(armstate,(64)word)component->armstate->(64)word)
    (X11:(armstate,(64)word)component)
    (s:armstate) =
    (key_p:(64)word) /\
    (read:(armstate,(64)word)component->armstate->(64)word)
    (X9:(armstate,(64)word)component)
    (s:armstate) =
    (word:num->(64)word) (16 * (nblk:num)) /\
    (read:(armstate,(64)word)component->armstate->(64)word)
    (SP:(armstate,(64)word)component)
    (s:armstate) =
    (stackpointer:(64)word) /\
    (read:(armstate,(64)word)component->armstate->(64)word)
    (X1:(armstate,(64)word)component)
    (s:armstate) =
    (word:num->(64)word) (128 * (nblk:num)) /\
    (read:(armstate,(64)word)component->armstate->(64)word)
    (X2:(armstate,(64)word)component)
    (s:armstate) =
    (out_p:(64)word) /\
    (read:(armstate,(64)word)component->armstate->(64)word)
    (X3:(armstate,(64)word)component)
    (s:armstate) =
    (xi_p:(64)word) /\
    (read:(armstate,(64)word)component->armstate->(64)word)
    (X6:(armstate,(64)word)component)
    (s:armstate) =
    (htbl_p:(64)word) /\
    (read:(armstate,num)component->armstate->num)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes:(64)word#num->((64)word->(8)word,num)component)
     ((in_p:(64)word),16 * (nblk:num)))
    (s:armstate) =
    (num_of_bytelist:((8)word)list->num) (ibytes:((8)word)list) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     (xi_p:(64)word))
    (s:armstate) =
    (xi:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     (ivec_p:(64)word))
    (s:armstate) =
    (ctr0:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     (key_p:(64)word))
    (s:armstate) =
    (k0:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (key_p:(64)word)
     ((word:num->(64)word) 16)))
    (s:armstate) =
    (k1:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (key_p:(64)word)
     ((word:num->(64)word) 32)))
    (s:armstate) =
    (k2:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (key_p:(64)word)
     ((word:num->(64)word) 48)))
    (s:armstate) =
    (k3:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (key_p:(64)word)
     ((word:num->(64)word) 64)))
    (s:armstate) =
    (k4:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (key_p:(64)word)
     ((word:num->(64)word) 80)))
    (s:armstate) =
    (k5:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (key_p:(64)word)
     ((word:num->(64)word) 96)))
    (s:armstate) =
    (k6:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (key_p:(64)word)
     ((word:num->(64)word) 112)))
    (s:armstate) =
    (k7:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (key_p:(64)word)
     ((word:num->(64)word) 128)))
    (s:armstate) =
    (k8:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (key_p:(64)word)
     ((word:num->(64)word) 144)))
    (s:armstate) =
    (k9:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (key_p:(64)word)
     ((word:num->(64)word) 160)))
    (s:armstate) =
    (k10:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (key_p:(64)word)
     ((word:num->(64)word) 176)))
    (s:armstate) =
    (k11:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (key_p:(64)word)
     ((word:num->(64)word) 192)))
    (s:armstate) =
    (k12:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (key_p:(64)word)
     ((word:num->(64)word) 208)))
    (s:armstate) =
    (k13:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (key_p:(64)word)
     ((word:num->(64)word) 224)))
    (s:armstate) =
    (k14:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     (htbl_p:(64)word))
    (s:armstate) =
    (h:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (htbl_p:(64)word)
     ((word:num->(64)word) 16)))
    (s:armstate) =
    (word_join:(64)word->(64)word->(128)word)
    ((karatsuba_mid:(128)word->(64)word)
    ((byteswap128:(128)word->(128)word)
    ((polyval_dot:(128)word->(128)word->(128)word)
     ((byteswap128:(128)word->(128)word) (h:(128)word))
    ((byteswap128:(128)word->(128)word) (h:(128)word)))))
    ((karatsuba_mid:(128)word->(64)word) (h:(128)word)) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (htbl_p:(64)word)
     ((word:num->(64)word) 32)))
    (s:armstate) =
    (byteswap128:(128)word->(128)word)
    ((polyval_dot:(128)word->(128)word->(128)word)
     ((byteswap128:(128)word->(128)word) (h:(128)word))
    ((byteswap128:(128)word->(128)word) (h:(128)word))) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (htbl_p:(64)word)
     ((word:num->(64)word) 48)))
    (s:armstate) =
    (byteswap128:(128)word->(128)word)
    ((polyval_dot:(128)word->(128)word->(128)word)
     ((polyval_dot:(128)word->(128)word->(128)word)
      ((byteswap128:(128)word->(128)word) (h:(128)word))
     ((byteswap128:(128)word->(128)word) (h:(128)word)))
    ((byteswap128:(128)word->(128)word) (h:(128)word))) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (htbl_p:(64)word)
     ((word:num->(64)word) 64)))
    (s:armstate) =
    (word_join:(64)word->(64)word->(128)word)
    ((karatsuba_mid:(128)word->(64)word)
    ((byteswap128:(128)word->(128)word)
    ((polyval_dot:(128)word->(128)word->(128)word)
     ((polyval_dot:(128)word->(128)word->(128)word)
      ((polyval_dot:(128)word->(128)word->(128)word)
       ((byteswap128:(128)word->(128)word) (h:(128)word))
      ((byteswap128:(128)word->(128)word) (h:(128)word)))
     ((byteswap128:(128)word->(128)word) (h:(128)word)))
    ((byteswap128:(128)word->(128)word) (h:(128)word)))))
    ((karatsuba_mid:(128)word->(64)word)
    ((byteswap128:(128)word->(128)word)
    ((polyval_dot:(128)word->(128)word->(128)word)
     ((polyval_dot:(128)word->(128)word->(128)word)
      ((byteswap128:(128)word->(128)word) (h:(128)word))
     ((byteswap128:(128)word->(128)word) (h:(128)word)))
    ((byteswap128:(128)word->(128)word) (h:(128)word))))) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (htbl_p:(64)word)
     ((word:num->(64)word) 80)))
    (s:armstate) =
    (byteswap128:(128)word->(128)word)
    ((polyval_dot:(128)word->(128)word->(128)word)
     ((polyval_dot:(128)word->(128)word->(128)word)
      ((polyval_dot:(128)word->(128)word->(128)word)
       ((byteswap128:(128)word->(128)word) (h:(128)word))
      ((byteswap128:(128)word->(128)word) (h:(128)word)))
     ((byteswap128:(128)word->(128)word) (h:(128)word)))
    ((byteswap128:(128)word->(128)word) (h:(128)word))) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (htbl_p:(64)word)
     ((word:num->(64)word) 96)))
    (s:armstate) =
    (byteswap128:(128)word->(128)word)
    ((polyval_dot:(128)word->(128)word->(128)word)
     ((polyval_dot:(128)word->(128)word->(128)word)
      ((polyval_dot:(128)word->(128)word->(128)word)
       ((polyval_dot:(128)word->(128)word->(128)word)
        ((byteswap128:(128)word->(128)word) (h:(128)word))
       ((byteswap128:(128)word->(128)word) (h:(128)word)))
      ((byteswap128:(128)word->(128)word) (h:(128)word)))
     ((byteswap128:(128)word->(128)word) (h:(128)word)))
    ((byteswap128:(128)word->(128)word) (h:(128)word))) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (htbl_p:(64)word)
     ((word:num->(64)word) 112)))
    (s:armstate) =
    (word_join:(64)word->(64)word->(128)word)
    ((karatsuba_mid:(128)word->(64)word)
    ((byteswap128:(128)word->(128)word)
    ((polyval_dot:(128)word->(128)word->(128)word)
     ((polyval_dot:(128)word->(128)word->(128)word)
      ((polyval_dot:(128)word->(128)word->(128)word)
       ((polyval_dot:(128)word->(128)word->(128)word)
        ((polyval_dot:(128)word->(128)word->(128)word)
         ((byteswap128:(128)word->(128)word) (h:(128)word))
        ((byteswap128:(128)word->(128)word) (h:(128)word)))
       ((byteswap128:(128)word->(128)word) (h:(128)word)))
      ((byteswap128:(128)word->(128)word) (h:(128)word)))
     ((byteswap128:(128)word->(128)word) (h:(128)word)))
    ((byteswap128:(128)word->(128)word) (h:(128)word)))))
    ((karatsuba_mid:(128)word->(64)word)
    ((byteswap128:(128)word->(128)word)
    ((polyval_dot:(128)word->(128)word->(128)word)
     ((polyval_dot:(128)word->(128)word->(128)word)
      ((polyval_dot:(128)word->(128)word->(128)word)
       ((polyval_dot:(128)word->(128)word->(128)word)
        ((byteswap128:(128)word->(128)word) (h:(128)word))
       ((byteswap128:(128)word->(128)word) (h:(128)word)))
      ((byteswap128:(128)word->(128)word) (h:(128)word)))
     ((byteswap128:(128)word->(128)word) (h:(128)word)))
    ((byteswap128:(128)word->(128)word) (h:(128)word))))) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (htbl_p:(64)word)
     ((word:num->(64)word) 128)))
    (s:armstate) =
    (byteswap128:(128)word->(128)word)
    ((polyval_dot:(128)word->(128)word->(128)word)
     ((polyval_dot:(128)word->(128)word->(128)word)
      ((polyval_dot:(128)word->(128)word->(128)word)
       ((polyval_dot:(128)word->(128)word->(128)word)
        ((polyval_dot:(128)word->(128)word->(128)word)
         ((byteswap128:(128)word->(128)word) (h:(128)word))
        ((byteswap128:(128)word->(128)word) (h:(128)word)))
       ((byteswap128:(128)word->(128)word) (h:(128)word)))
      ((byteswap128:(128)word->(128)word) (h:(128)word)))
     ((byteswap128:(128)word->(128)word) (h:(128)word)))
    ((byteswap128:(128)word->(128)word) (h:(128)word))) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (htbl_p:(64)word)
     ((word:num->(64)word) 144)))
    (s:armstate) =
    (byteswap128:(128)word->(128)word)
    ((polyval_dot:(128)word->(128)word->(128)word)
     ((polyval_dot:(128)word->(128)word->(128)word)
      ((polyval_dot:(128)word->(128)word->(128)word)
       ((polyval_dot:(128)word->(128)word->(128)word)
        ((polyval_dot:(128)word->(128)word->(128)word)
         ((polyval_dot:(128)word->(128)word->(128)word)
          ((byteswap128:(128)word->(128)word) (h:(128)word))
         ((byteswap128:(128)word->(128)word) (h:(128)word)))
        ((byteswap128:(128)word->(128)word) (h:(128)word)))
       ((byteswap128:(128)word->(128)word) (h:(128)word)))
      ((byteswap128:(128)word->(128)word) (h:(128)word)))
     ((byteswap128:(128)word->(128)word) (h:(128)word)))
    ((byteswap128:(128)word->(128)word) (h:(128)word))) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (htbl_p:(64)word)
     ((word:num->(64)word) 160)))
    (s:armstate) =
    (word_join:(64)word->(64)word->(128)word)
    ((karatsuba_mid:(128)word->(64)word)
    ((byteswap128:(128)word->(128)word)
    ((polyval_dot:(128)word->(128)word->(128)word)
     ((polyval_dot:(128)word->(128)word->(128)word)
      ((polyval_dot:(128)word->(128)word->(128)word)
       ((polyval_dot:(128)word->(128)word->(128)word)
        ((polyval_dot:(128)word->(128)word->(128)word)
         ((polyval_dot:(128)word->(128)word->(128)word)
          ((polyval_dot:(128)word->(128)word->(128)word)
           ((byteswap128:(128)word->(128)word) (h:(128)word))
          ((byteswap128:(128)word->(128)word) (h:(128)word)))
         ((byteswap128:(128)word->(128)word) (h:(128)word)))
        ((byteswap128:(128)word->(128)word) (h:(128)word)))
       ((byteswap128:(128)word->(128)word) (h:(128)word)))
      ((byteswap128:(128)word->(128)word) (h:(128)word)))
     ((byteswap128:(128)word->(128)word) (h:(128)word)))
    ((byteswap128:(128)word->(128)word) (h:(128)word)))))
    ((karatsuba_mid:(128)word->(64)word)
    ((byteswap128:(128)word->(128)word)
    ((polyval_dot:(128)word->(128)word->(128)word)
     ((polyval_dot:(128)word->(128)word->(128)word)
      ((polyval_dot:(128)word->(128)word->(128)word)
       ((polyval_dot:(128)word->(128)word->(128)word)
        ((polyval_dot:(128)word->(128)word->(128)word)
         ((polyval_dot:(128)word->(128)word->(128)word)
          ((byteswap128:(128)word->(128)word) (h:(128)word))
         ((byteswap128:(128)word->(128)word) (h:(128)word)))
        ((byteswap128:(128)word->(128)word) (h:(128)word)))
       ((byteswap128:(128)word->(128)word) (h:(128)word)))
      ((byteswap128:(128)word->(128)word) (h:(128)word)))
     ((byteswap128:(128)word->(128)word) (h:(128)word)))
    ((byteswap128:(128)word->(128)word) (h:(128)word))))) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (htbl_p:(64)word)
     ((word:num->(64)word) 176)))
    (s:armstate) =
    (byteswap128:(128)word->(128)word)
    ((polyval_dot:(128)word->(128)word->(128)word)
     ((polyval_dot:(128)word->(128)word->(128)word)
      ((polyval_dot:(128)word->(128)word->(128)word)
       ((polyval_dot:(128)word->(128)word->(128)word)
        ((polyval_dot:(128)word->(128)word->(128)word)
         ((polyval_dot:(128)word->(128)word->(128)word)
          ((polyval_dot:(128)word->(128)word->(128)word)
           ((byteswap128:(128)word->(128)word) (h:(128)word))
          ((byteswap128:(128)word->(128)word) (h:(128)word)))
         ((byteswap128:(128)word->(128)word) (h:(128)word)))
        ((byteswap128:(128)word->(128)word) (h:(128)word)))
       ((byteswap128:(128)word->(128)word) (h:(128)word)))
      ((byteswap128:(128)word->(128)word) (h:(128)word)))
     ((byteswap128:(128)word->(128)word) (h:(128)word)))
    ((byteswap128:(128)word->(128)word) (h:(128)word))) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     (in_p:(64)word))
    (s:armstate) =
    (bytes_to_int128:((8)word)list->(128)word)
    ((SUB_LIST:num#num->((8)word)list->((8)word)list) (0,16)
    (ibytes:((8)word)list)) /\
    (read:(armstate,(64)word)component->armstate->(64)word)
    (X16:(armstate,(64)word)component)
    (s:armstate) =
    (ivec_p:(64)word) /\
    (read:(armstate,(64)word)component->armstate->(64)word)
    (X10:(armstate,(64)word)component)
    (s:armstate) =
    (word_add:(64)word->(64)word->(64)word) (stackpointer:(64)word)
    ((word:num->(64)word) 64) /\
    (read:(armstate,(64)word)component->armstate->(64)word)
    (X15:(armstate,(64)word)component)
    (s:armstate) =
    (word:num->(64)word) 4294967296 /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q31:(armstate,(128)word)component)
    (s:armstate) =
    (word:num->(128)word) 79228162514264337593543950336 /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q19:(armstate,(128)word)component)
    (s:armstate) =
    (word_bytereverse:(128)word->(128)word) (xi:(128)word) /\
    (read:(armstate,(64)word)component->armstate->(64)word)
    (X4:(armstate,(64)word)component)
    (s:armstate) =
    (word_add:(64)word->(64)word->(64)word) (in_p:(64)word)
    ((word:num->(64)word) (16 * (nblk:num))) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q27:(armstate,(128)word)component)
    (s:armstate) =
    (k13:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q26:(armstate,(128)word)component)
    (s:armstate) =
    (k12:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q28:(armstate,(128)word)component)
    (s:armstate) =
    (k14:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q5:(armstate,(128)word)component)
    (s:armstate) =
    (aes13:(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word)
    ((gcm_ctr_inc:(128)word->(128)word)
    ((gcm_ctr_inc:(128)word->(128)word)
    ((gcm_ctr_inc:(128)word->(128)word)
    ((gcm_ctr_inc:(128)word->(128)word)
    ((gcm_ctr_inc:(128)word->(128)word) (ctr0:(128)word))))))
    (k0:(128)word)
    (k1:(128)word)
    (k2:(128)word)
    (k3:(128)word)
    (k4:(128)word)
    (k5:(128)word)
    (k6:(128)word)
    (k7:(128)word)
    (k8:(128)word)
    (k9:(128)word)
    (k10:(128)word)
    (k11:(128)word)
    (k12:(128)word)
    (k13:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q2:(armstate,(128)word)component)
    (s:armstate) =
    (aes13:(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word)
    ((gcm_ctr_inc:(128)word->(128)word)
    ((gcm_ctr_inc:(128)word->(128)word) (ctr0:(128)word)))
    (k0:(128)word)
    (k1:(128)word)
    (k2:(128)word)
    (k3:(128)word)
    (k4:(128)word)
    (k5:(128)word)
    (k6:(128)word)
    (k7:(128)word)
    (k8:(128)word)
    (k9:(128)word)
    (k10:(128)word)
    (k11:(128)word)
    (k12:(128)word)
    (k13:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q4:(armstate,(128)word)component)
    (s:armstate) =
    (aes13:(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word)
    ((gcm_ctr_inc:(128)word->(128)word)
    ((gcm_ctr_inc:(128)word->(128)word)
    ((gcm_ctr_inc:(128)word->(128)word)
    ((gcm_ctr_inc:(128)word->(128)word) (ctr0:(128)word)))))
    (k0:(128)word)
    (k1:(128)word)
    (k2:(128)word)
    (k3:(128)word)
    (k4:(128)word)
    (k5:(128)word)
    (k6:(128)word)
    (k7:(128)word)
    (k8:(128)word)
    (k9:(128)word)
    (k10:(128)word)
    (k11:(128)word)
    (k12:(128)word)
    (k13:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q3:(armstate,(128)word)component)
    (s:armstate) =
    (aes13:(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word)
    ((gcm_ctr_inc:(128)word->(128)word)
    ((gcm_ctr_inc:(128)word->(128)word)
    ((gcm_ctr_inc:(128)word->(128)word) (ctr0:(128)word))))
    (k0:(128)word)
    (k1:(128)word)
    (k2:(128)word)
    (k3:(128)word)
    (k4:(128)word)
    (k5:(128)word)
    (k6:(128)word)
    (k7:(128)word)
    (k8:(128)word)
    (k9:(128)word)
    (k10:(128)word)
    (k11:(128)word)
    (k12:(128)word)
    (k13:(128)word) /\
    (read:(armstate,(64)word)component->armstate->(64)word)
    (X5:(armstate,(64)word)component)
    (s:armstate) =
    (word:num->(64)word) (16 * (nblk:num)) /\
    (read:(armstate,(64)word)component->armstate->(64)word)
    (X0:(armstate,(64)word)component)
    (s:armstate) =
    (word_add:(64)word->(64)word->(64)word) (in_p:(64)word)
    ((word:num->(64)word) 16) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q9:(armstate,(128)word)component)
    (s:armstate) =
    (bytes_to_int128:((8)word)list->(128)word)
    ((SUB_LIST:num#num->((8)word)list->((8)word)list) (0,16)
    (ibytes:((8)word)list))|};;

(* ivec M2: carry the advanced raw counter Q30 in the front
   postcond so the <=8 DISPATCH bands + the shared WB_TAIL_GEN2_r (which prove
   FROM q_at k = this postcond) see Q30 concretely and can fold the ivec store.
   The front does 8 `add v30` (blocks 0-7) after the rev32 seed, so at the tail
   seam s265 (0x42c b.ge TAKEN for nblk<=8) Q30 = gcm_ctr_raw (word 8) ctr0.
   HARVESTED (top lane = word_add(word_add(ctr0 top bytes)(word 7))
   (word 1) = +8); the +8 count re-confirmed analytically. *)
let wb_front_postcond = mk_abs(`s:armstate`,
    mk_conj(snd(dest_abs wb_front_postcond),
            `read Q30 (s:armstate) = gcm_ctr_raw (word 8) ctr0`));;

(* ========================================================================= *)
(* SPEED REFACTOR -- the SHARED FRONT PREFIX (0x20 -> 0x428),                  *)
(* simulated ONCE across the <=8 front (WB_FRONT_BUF) AND the >=9 front        *)
(* (WBN_FRONT_PREFIX).  Extends the shared-prefix idiom by splitting at        *)
(* the EARLIER 0x42c b.ge (step 260) instead of 0x49c (step 288): steps 1..259 *)
(* (entry 0x20 -> the 0x42c b.ge, all straight-line, only round-key/counter    *)
(* loads, NO input-block reads) are byte-identical work in BOTH bands, so we   *)
(* factor them into WBN_FRONT_PREFIX_259 proved ONCE on the UNION band         *)
(* (1<=nblk /\ 128*nblk<2^62), keeping X5 general via the _ANY mask and KEEPING *)
(* the raw NF/VF/ZF/CF pre-branch flag facts.  Each consumer then chains a     *)
(* short post-branch leg via ENSURES_TRANS_SIMPLE (WB_FRONT_BUF: 0x42c TAKEN   *)
(* in the <=8 band -> 6 steps 260..265 to s265; WBN_FRONT_PREFIX: 0x42c FALLS  *)
(* THROUGH in the >=9 band -> 28 steps 260..287 to s287).  Both consumer       *)
(* STATEMENTS stay bit-identical.  Net: 2 full front sims (~504s) -> 1 shared  *)
(* 259-prefix (~225s) + 2 short tails.                                          *)
(* The four helpers below (state_num_of_read_q30/DISCARD_STALE_Q30_TAC and the  *)
(* _ANY mask lemmas) are HOISTED copies of definitions that also appear later   *)
(* (the >=9/916 front code re-binds the identical statements); the duplication  *)
(* is harmless (same theorems) and avoids relocating the later ge9 block.       *)
(* ------------------------------------------------------------------------- *)

(* hoisted from the >=9 front section: keep only the latest read Q30 fact *)
let state_num_of_read_q30 th =
  let c = concl th in
  try (match lhs c with
       | Comb(Comb(Const("read",_),q),st) when string_of_term q = "Q30" ->
           let s = fst(dest_var st) in
           if String.length s > 1 && s.[0] = 's'
           then int_of_string (String.sub s 1 (String.length s - 1)) else (-1)
       | _ -> (-1))
  with _ -> (-1);;
let DISCARD_STALE_Q30_TAC : tactic = fun (asl,w) ->
  let nums = List.filter (fun n -> n >= 0)
    (List.map (fun (_,th) -> state_num_of_read_q30 th) asl) in
  if nums = [] then ALL_TAC (asl,w) else
  let mx = itlist max nums (-1) in
  DISCARD_ASSUMPTIONS_TAC (fun th ->
    let n = state_num_of_read_q30 th in n >= 0 && n < mx) (asl,w);;

(* hoisted _ANY scalar rungs (nblk-general USHR/AND-mask; pure word/arith) *)
let USHR_128NBLK_ANY = prove
 (`!nblk. 128 * nblk < 2 EXP 64
        ==> word_ushr (word (128 * nblk):int64) 3 = word (16 * nblk)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[word_ushr] THEN
  ASM_SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64] THEN AP_TERM_TAC THEN ARITH_TAC);;
let AND_MASK_16NBLK_ANY = prove
 (`!nblk. 1 <= nblk /\ 16 * nblk < 2 EXP 64
        ==> word_and (word_sub (word (16 * nblk)) (word 1))
                     (word 18446744073709551488):int64 =
            word (128 * ((nblk - 1) DIV 8))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `word 18446744073709551488:int64 = word_not (word (2 EXP 7 - 1))`
    SUBST1_TAC THENL
   [CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN CONV_TAC WORD_REDUCE_CONV;
    ALL_TAC] THEN
  REWRITE_TAC[WORD_AND_NOT_MASK_WORD] THEN
  SUBGOAL_THEN `word_sub (word (16 * nblk)) (word 1):int64 = word (16 * nblk - 1)`
    SUBST1_TAC THENL
   [REWRITE_TAC[WORD_SUB] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `val (word (16 * nblk - 1):int64) = 16 * nblk - 1` SUBST1_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  AP_TERM_TAC THEN
  SUBGOAL_THEN `(16 * nblk - 1) DIV 2 EXP 7 = (nblk - 1) DIV 8` SUBST1_TAC THENL
   [ALL_TAC; ARITH_TAC] THEN
  MP_TAC(SPECL [`nblk - 1`; `8`] DIVISION) THEN
  ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `d = (nblk - 1) DIV 8` THEN ABBREV_TAC `m = (nblk - 1) MOD 8` THEN
  ASM_ARITH_TAC);;

(* d = 128*((nblk-1)DIV8) = 0 for 1<=nblk<=8 (the <=8 band takes the 0x42c b.ge) *)
let D_ZERO_LE8 = prove
 (`!nblk. 1 <= nblk /\ nblk <= 8 ==> 128 * ((nblk - 1) DIV 8) = 0`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(nblk - 1) DIV 8 = 0` (fun th -> REWRITE_TAC[th; MULT_CLAUSES]) THEN
  MATCH_MP_TAC DIV_LT THEN ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* FUSED SPLICE (STEP 4): the fused .o inserts an early guard                  *)
(*   cmp x9,#0x40 ; b.le .L256_dec_w5r_small                                   *)
(* at .S 0x38 (front-sim steps 7,8; x9 = word(16*nblk) from `lsr x9,x1,#3`).   *)
(* For the union front (nblk>=5) the b.le FALLS THROUGH (16*nblk>=80>64), so   *)
(* the small-message fused path is skipped and the front proceeds as before    *)
(* (only shifted +8 in address / +2 in step index; body [0x4c0,end) is         *)
(* byte-identical because the s138 .balign 16 absorbs the guard's +8).  The    *)
(* nblk<=4 case takes the b.le into the fused region and is proved by the       *)
(* four fused-band theorems that replace prove_band 1..4.                       *)
(*                                                                             *)
(* GUARD_LE_FALLTHRU resolves the b.le for 5<=nblk (pure arithmetic on         *)
(* word(16*nblk); no pointer facts, simpler than WB_LOOPENTER_FLAGS 42C/49C).   *)
(* Validated hyps=0 on the base MCP; see orchestrator/logs/session-144-work/    *)
(* guard_resolve_validated.ml.  Usage in the steppers: discharge it into the    *)
(* assumptions BEFORE ARM_STEPS_TAC (7--8) so the stepper folds the branch.     *)
let IVAL_WORD_SMALL_64 = prove
 (`!n. n < 2 EXP 63 ==> ival (word n:int64) = &n`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `val (word n:int64) = n` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[IVAL_EQ_VAL; DIMINDEX_64;
               ARITH_RULE `n < 2 EXP 63 ==> n < 2 EXP (64 - 1)`]);;

let GUARD_LE_FALLTHRU = prove
 (`!nblk. 5 <= nblk /\ 16 * nblk < 2 EXP 63
      ==> (~(~(val (word_sub (word (16 * nblk):int64) (word 64)) = 0) /\
             (ival (word_sub (word (16 * nblk):int64) (word 64)) < &0 <=>
              ~(ival (word (16 * nblk):int64) - &64 =
                ival (word_sub (word (16 * nblk):int64) (word 64))))) <=> F)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `word_sub (word (16 * nblk):int64) (word 64) = word(16 * nblk - 64)`
    SUBST1_TAC THENL
   [MP_TAC(SPECL [`16 * nblk`; `64`] (INST_TYPE[`:64`,`:N`] WORD_SUB)) THEN
    ASM_SIMP_TAC[ARITH_RULE `5 <= nblk ==> 64 <= 16 * nblk`] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REFL_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[IVAL_WORD_SMALL_64;
               ARITH_RULE `16 * nblk < 2 EXP 63 ==> 16 * nblk - 64 < 2 EXP 63`] THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN
  SUBGOAL_THEN `(16 * nblk - 64) MOD 2 EXP 64 = 16 * nblk - 64` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_ARITH_TAC);;

(* union band = the 17 hyps shared by <=8 (wb_front_hyps_tm) and >=9
   (wbn_front_hyps_ge9_tm) PLUS 5<=nblk PLUS 128*nblk<2^62.  Both bands imply it.
   FUSED SPLICE (STEP 4): strengthened 1<=nblk -> 5<=nblk.  The new guard b.le at
   step 8 falls through only for nblk>=5, so every consumer of the union front
   (readable bands 5..8 via WB_FRONT_BUF; the nblk>=9 chain) is on the 5<=nblk
   side; nblk in {1,2,3,4} takes the fused path and is proved by the fused bands.
   GUARD_LE_FALLTHRU discharges the guard from 5<=nblk (+ 16*nblk<2^63, which
   follows from the 128*nblk<2^62 conjunct here). *)
let wbn_front_hyps_uni_tm =
  let cs8 = conjuncts wb_front_hyps_tm in
  end_itlist (curry mk_conj)
    (`5 <= nblk`::`128 * nblk < 2 EXP 62`::
     (filter (fun c -> not(c = `5 <= nblk` || c = `1 <= nblk` || c = `nblk <= 8`)) cs8));;

(* FUSED SPLICE (STEP 4.1 fix, session-147): the union hyps now carry `5 <= nblk`
   and FILTER OUT `1 <= nblk` (wbn_front_hyps_uni_tm above), so `ASSUME `1 <= nblk``
   introduced a hypothesis absent from the goal -> the discharged theorem carried an
   alien `1 <= nblk` hyp and the enclosing SUBGOAL_THEN's justification raised
   `Failure "ABS"` at cold-load (the first true full front sim, gate2/s267 site).
   Use `5 <= nblk` (present) -- it implies every bound `1 <= nblk` supplied to
   USHR_128NBLK_ANY / AND_MASK_16NBLK_ANY / INPUT_BYTES_TO_BYTE128_LANES via ARITH. *)
let NBLK_ARITH_UNI_TAC =
  MP_TAC(ASSUME `5 <= nblk`) THEN MP_TAC(ASSUME `128 * nblk < 2 EXP 62`) THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN ARITH_TAC;;

let WBN_FRONT_PREP_BUF_UNI_TAC =
  SUBGOAL_THEN `SUB_LIST (0, 16 * nblk) (ibytes:byte list) = ibytes` ASSUME_TAC THENL
   [MATCH_MP_TAC SUB_LIST_LENGTH_IMPLIES THEN ASM_REWRITE_TAC[LE_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN `read (memory :> bytes128 in_p) s0 = bytes_to_int128 (SUB_LIST (0,16) ibytes)` ASSUME_TAC THENL
   [MP_TAC(SPECL [`nblk:num`; `in_p:int64`; `ibytes:byte list`; `s0:armstate`] INPUT_BYTES_TO_BYTE128_LANES) THEN
    ASM_REWRITE_TAC[LE_REFL] THEN DISCH_THEN(MP_TAC o SPEC `0`) THEN
    ANTS_TAC THENL [NBLK_ARITH_UNI_TAC; ALL_TAC] THEN
    REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]); ALL_TAC] THEN
  SUBGOAL_THEN `word_ushr (word (128 * nblk):int64) 3 = word (16 * nblk)` ASSUME_TAC THENL
   [MATCH_MP_TAC USHR_128NBLK_ANY THEN NBLK_ARITH_UNI_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `word_and (word_sub (word (16 * nblk)) (word 1)) (word 18446744073709551488):int64 = word (128 * ((nblk - 1) DIV 8))` ASSUME_TAC THENL
   [MATCH_MP_TAC AND_MASK_16NBLK_ANY THEN NBLK_ARITH_UNI_TAC; ALL_TAC];;

let wbn_init_uni_tac =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS] THEN ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WB_MC_LEN]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[C_ARGUMENTS]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_dec]) THEN
  RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV let_CONV)) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o check(is_conj o concl)) THEN
  WBN_FRONT_PREP_BUF_UNI_TAC;;

(* the shared prefix steps 1..267 (entry 0x20 -> the 0x44c b.ge at pc+1100),
   identical to WB_FRONT_STEP_TAC / WBN_FRONT_STEP_TAC modulo the Q30-discard
   flavor; stops BEFORE the band-dependent 0x44c branch so X5 stays general.
   (Was 1..259 / 0x42c / pc+1068 before the +6-instr counter flatten; then
   1..265 / 0x444 / pc+1092 pre-splice.) *)
(* SETUP-counter flatten (+6 instrs): the parallel depth-2 counter
   form REORDERS steps 16-58 (all counter SIMD first, then AES round-0/1) vs the
   old serial-interleaved 16-52, then RECONVERGES at ldp q28,q26 (new s59/old s53)
   with a UNIFORM +6 shift and every branch displacement unchanged.  The counter
   SIMD (offset-adds + base rev32 + block-adds + 7 rev32) now spans steps 19-41,
   so the per-step GCM_SIMD_SIMPLIFY loop is extended 6--30 -> 6--41; all later
   ranges are +6.  (Values at s265 are identical to the old s259 seam; only the
   dataflow differs.) *)
(* FUSED SPLICE (STEP 4, +2 instrs): the guard `cmp x9,#0x40 ; b.le` inserts as
   steps 7,8 (entry 0x20 = step 1; step 6 = add x10 @0x34 pre-guard; the first
   vector op ld1 @0x40 is now step 9, was step 7).  So the vector per-step loop
   shifts 6--41 -> 9--43 (add x10 @ step 6 stays in the plain (1--6) prefix) and
   every later range is +2.  The b.le FALLS THROUGH for the union band nblk>=5
   (16*nblk>=80>64), resolved by GUARD_LE_FALLTHRU discharged into the asms
   BEFORE stepping 7--8 so the stepper folds the branch to fall-through. *)
let WBN_FRONT_STEP259_TAC =
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (1--6) THEN
  MP_TAC(SPEC `nblk:num` GUARD_LE_FALLTHRU) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN DISCH_TAC THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (7--8) THEN
  EVERY(map (fun i -> ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (i--i) THEN
             GCM_SIMD_SIMPLIFY_TAC) (9--43)) THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (44--92) THEN DISCARD_STALE_Q30_TAC THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (93--181) THEN DISCARD_STALE_Q30_TAC THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (182--185) THEN
  GCM_SIMD_SIMPLIFY_TAC THEN DISCARD_STALE_Q30_TAC THEN
  (* s083 speed: 186-197 is the GHASH REV64 window (Q19 byte-tree fold).  The
     keep-everything ARM_VSTEPS_FOLD_TAC held a ~130k-char pile across all 12
     steps (~29s); ARM_STEPS_FOLD_DISCARD_TAC folds Q19 BEFORE discarding old
     states each step (the lemmas.ml "step and simplify as we go" idiom), so the
     pile stays flat (~6.5s).  No store read-back is needed in this window, so
     the per-step discard is safe -- proof still closes hyps=0.  Scoped to this
     _259 stepper only; the dead WBN_FRONT_STEP_TAC below is left unchanged.
     (Fused splice: window shifted 184--195 -> 186--197, +2.) *)
  ARM_STEPS_FOLD_DISCARD_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (186--197) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[Q19_BREVXI]) THEN DISCARD_STALE_Q30_TAC THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (198--262) THEN
  DISCARD_STALE_Q30_TAC THEN GCM_SIMD_SIMPLIFY_TAC THEN
  ARM_VSTEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC [263] THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (264--267);;

let WBN_FRONT_PREFIX259_TAC = wbn_init_uni_tac THEN WBN_FRONT_STEP259_TAC;;

(* prefix goal builder (union band, postcond @ PC 0x42c = pc+1068) *)
let mk_wbn_prefix259_goal postcond =
  let ens = subst [wb_front_pre_tm,`PPP:armstate->bool`; postcond,`QQQ:armstate->bool`;
                   wb_front_frame_tm,`CCC:armstate->armstate->bool`]
              `ensures arm PPP QQQ CCC` in
  list_mk_forall(wb_front_vars, mk_imp(wbn_front_hyps_uni_tm, ens));;

(* The s259 prefix postcond (state at the 0x42c b.ge, pre-branch), embedded as a
   fully type-annotated literal so the shared prefix simulates ONCE.  X5 is the
   general word_add(word(128*((nblk-1)DIV8)))in_p and ALL raw NF/VF/ZF/CF flag
   facts are KEPT (each consumer's post-branch leg resolves the branch in its band).
   REGENERATION (if the front or keep-profile changes): re-run
     let h = let mg = mk_wbn_prefix259_goal `\s:armstate. read PC s = word (pc + 0x444)` in
             let _ = g mg in let _ = e (WBN_FRONT_PREFIX259_TAC THEN wb_front_fold_tac) in
             let (asl,_) = top_goal() in let r = build_state_postcond_tms2 "s259" asl in
             let _ = b() in r;;
   then print with print_types_of_subterms := 2; verify reparse aconv h. *)
let wbn_front_prefix259_postcond = parse_term {|\(s:armstate).
    (aligned_bytes_loaded:armstate->(64)word->((8)word)list->bool)
    (s:armstate)
    ((word:num->(64)word) (pc:num))
    (aesv8_gcm_8x_dec_256_wb_mc:((8)word)list) /\
    (read:(armstate,(64)word)component->armstate->(64)word)
    (PC:(armstate,(64)word)component)
    (s:armstate) =
    (word:num->(64)word) ((pc:num) + 1100) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q7:(armstate,(128)word)component)
    (s:armstate) =
    (aes13:(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word)
    ((gcm_ctr_inc:(128)word->(128)word)
    ((gcm_ctr_inc:(128)word->(128)word)
    ((gcm_ctr_inc:(128)word->(128)word)
    ((gcm_ctr_inc:(128)word->(128)word)
    ((gcm_ctr_inc:(128)word->(128)word)
    ((gcm_ctr_inc:(128)word->(128)word)
    ((gcm_ctr_inc:(128)word->(128)word) (ctr0:(128)word))))))))
    (k0:(128)word)
    (k1:(128)word)
    (k2:(128)word)
    (k3:(128)word)
    (k4:(128)word)
    (k5:(128)word)
    (k6:(128)word)
    (k7:(128)word)
    (k8:(128)word)
    (k9:(128)word)
    (k10:(128)word)
    (k11:(128)word)
    (k12:(128)word)
    (k13:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q6:(armstate,(128)word)component)
    (s:armstate) =
    (aes13:(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word)
    ((gcm_ctr_inc:(128)word->(128)word)
    ((gcm_ctr_inc:(128)word->(128)word)
    ((gcm_ctr_inc:(128)word->(128)word)
    ((gcm_ctr_inc:(128)word->(128)word)
    ((gcm_ctr_inc:(128)word->(128)word)
    ((gcm_ctr_inc:(128)word->(128)word) (ctr0:(128)word)))))))
    (k0:(128)word)
    (k1:(128)word)
    (k2:(128)word)
    (k3:(128)word)
    (k4:(128)word)
    (k5:(128)word)
    (k6:(128)word)
    (k7:(128)word)
    (k8:(128)word)
    (k9:(128)word)
    (k10:(128)word)
    (k11:(128)word)
    (k12:(128)word)
    (k13:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q0:(armstate,(128)word)component)
    (s:armstate) =
    (aes13:(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word)
    (ctr0:(128)word)
    (k0:(128)word)
    (k1:(128)word)
    (k2:(128)word)
    (k3:(128)word)
    (k4:(128)word)
    (k5:(128)word)
    (k6:(128)word)
    (k7:(128)word)
    (k8:(128)word)
    (k9:(128)word)
    (k10:(128)word)
    (k11:(128)word)
    (k12:(128)word)
    (k13:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q1:(armstate,(128)word)component)
    (s:armstate) =
    (aes13:(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word)
    ((gcm_ctr_inc:(128)word->(128)word) (ctr0:(128)word))
    (k0:(128)word)
    (k1:(128)word)
    (k2:(128)word)
    (k3:(128)word)
    (k4:(128)word)
    (k5:(128)word)
    (k6:(128)word)
    (k7:(128)word)
    (k8:(128)word)
    (k9:(128)word)
    (k10:(128)word)
    (k11:(128)word)
    (k12:(128)word)
    (k13:(128)word) /\
    ((read:(armstate,bool)component->armstate->bool)
     (NF:(armstate,bool)component)
     (s:armstate) <=>
     (ival:(64)word->int)
     ((word_sub:(64)word->(64)word->(64)word) (in_p:(64)word)
     ((word_add:(64)word->(64)word->(64)word)
      ((word:num->(64)word) (128 * ((nblk:num) - 1) DIV 8))
     (in_p:(64)word))) <
     (int_of_num:num->int)0) /\
    ((read:(armstate,bool)component->armstate->bool)
     (ZF:(armstate,bool)component)
     (s:armstate) <=>
     (val:(64)word->num)
     ((word_sub:(64)word->(64)word->(64)word) (in_p:(64)word)
     ((word_add:(64)word->(64)word->(64)word)
      ((word:num->(64)word) (128 * ((nblk:num) - 1) DIV 8))
     (in_p:(64)word))) =
     0) /\
    ((read:(armstate,bool)component->armstate->bool)
     (CF:(armstate,bool)component)
     (s:armstate) <=>
     (val:(64)word->num)
     ((word_add:(64)word->(64)word->(64)word)
      ((word:num->(64)word) (128 * ((nblk:num) - 1) DIV 8))
     (in_p:(64)word)) <=
     (val:(64)word->num) (in_p:(64)word)) /\
    ((read:(armstate,bool)component->armstate->bool)
     (VF:(armstate,bool)component)
     (s:armstate) <=>
     ~((ival:(64)word->int) (in_p:(64)word) -
       (ival:(64)word->int)
       ((word_add:(64)word->(64)word->(64)word)
        ((word:num->(64)word) (128 * ((nblk:num) - 1) DIV 8))
       (in_p:(64)word)) =
       (ival:(64)word->int)
       ((word_sub:(64)word->(64)word->(64)word) (in_p:(64)word)
       ((word_add:(64)word->(64)word->(64)word)
        ((word:num->(64)word) (128 * ((nblk:num) - 1) DIV 8))
       (in_p:(64)word))))) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q30:(armstate,(128)word)component)
    (s:armstate) =
    (word_join:(64)word->(64)word->(128)word)
    ((word_join:(32)word->(32)word->(64)word)
     ((word_add:(32)word->(32)word->(32)word)
      ((word_add:(32)word->(32)word->(32)word)
       ((word_join:(16)word->(16)word->(32)word)
        ((word_join:(8)word->(8)word->(16)word)
         ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (96,8))
        ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (104,8)))
       ((word_join:(8)word->(8)word->(16)word)
        ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (112,8))
       ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (120,8))))
      ((word:num->(32)word) 7))
     ((word:num->(32)word) 1))
    ((word_add:(32)word->(32)word->(32)word)
     ((word_join:(16)word->(16)word->(32)word)
      ((word_join:(8)word->(8)word->(16)word)
       ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (64,8))
      ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (72,8)))
     ((word_join:(8)word->(8)word->(16)word)
      ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (80,8))
     ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (88,8))))
    ((word:num->(32)word) 0)))
    ((word_join:(32)word->(32)word->(64)word)
     ((word_add:(32)word->(32)word->(32)word)
      ((word_join:(16)word->(16)word->(32)word)
       ((word_join:(8)word->(8)word->(16)word)
        ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (32,8))
       ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (40,8)))
      ((word_join:(8)word->(8)word->(16)word)
       ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (48,8))
      ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (56,8))))
     ((word:num->(32)word) 0))
    ((word_add:(32)word->(32)word->(32)word)
     ((word_join:(16)word->(16)word->(32)word)
      ((word_join:(8)word->(8)word->(16)word)
       ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (0,8))
      ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (8,8)))
     ((word_join:(8)word->(8)word->(16)word)
      ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (16,8))
     ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (24,8))))
    ((word:num->(32)word) 0))) /\
    (read:(armstate,(64)word)component->armstate->(64)word)
    (X5:(armstate,(64)word)component)
    (s:armstate) =
    (word_add:(64)word->(64)word->(64)word)
    ((word:num->(64)word) (128 * ((nblk:num) - 1) DIV 8))
    (in_p:(64)word) /\
    (read:(armstate,(64)word)component->armstate->(64)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes64:(64)word->((64)word->(8)word,(64)word)component)
     ((word_add:(64)word->(64)word->(64)word) (stackpointer:(64)word)
     ((word:num->(64)word) 64)))
    (s:armstate) =
    (word:num->(64)word) 13979173243358019584 /\
    (read:(armstate,(64)word)component->armstate->(64)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes64:(64)word->((64)word->(8)word,(64)word)component)
     ((word_add:(64)word->(64)word->(64)word) (stackpointer:(64)word)
     ((word:num->(64)word) 72)))
    (s:armstate) =
    (word:num->(64)word) 0 /\
    (read:(armstate,(64)word)component->armstate->(64)word)
    (X11:(armstate,(64)word)component)
    (s:armstate) =
    (key_p:(64)word) /\
    (read:(armstate,(64)word)component->armstate->(64)word)
    (X9:(armstate,(64)word)component)
    (s:armstate) =
    (word:num->(64)word) (16 * (nblk:num)) /\
    (read:(armstate,(64)word)component->armstate->(64)word)
    (SP:(armstate,(64)word)component)
    (s:armstate) =
    (stackpointer:(64)word) /\
    (read:(armstate,(64)word)component->armstate->(64)word)
    (X0:(armstate,(64)word)component)
    (s:armstate) =
    (in_p:(64)word) /\
    (read:(armstate,(64)word)component->armstate->(64)word)
    (X1:(armstate,(64)word)component)
    (s:armstate) =
    (word:num->(64)word) (128 * (nblk:num)) /\
    (read:(armstate,(64)word)component->armstate->(64)word)
    (X2:(armstate,(64)word)component)
    (s:armstate) =
    (out_p:(64)word) /\
    (read:(armstate,(64)word)component->armstate->(64)word)
    (X3:(armstate,(64)word)component)
    (s:armstate) =
    (xi_p:(64)word) /\
    (read:(armstate,(64)word)component->armstate->(64)word)
    (X6:(armstate,(64)word)component)
    (s:armstate) =
    (htbl_p:(64)word) /\
    (read:(armstate,num)component->armstate->num)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes:(64)word#num->((64)word->(8)word,num)component)
     ((in_p:(64)word),16 * (nblk:num)))
    (s:armstate) =
    (num_of_bytelist:((8)word)list->num) (ibytes:((8)word)list) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     (xi_p:(64)word))
    (s:armstate) =
    (xi:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     (ivec_p:(64)word))
    (s:armstate) =
    (ctr0:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     (key_p:(64)word))
    (s:armstate) =
    (k0:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (key_p:(64)word)
     ((word:num->(64)word) 16)))
    (s:armstate) =
    (k1:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (key_p:(64)word)
     ((word:num->(64)word) 32)))
    (s:armstate) =
    (k2:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (key_p:(64)word)
     ((word:num->(64)word) 48)))
    (s:armstate) =
    (k3:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (key_p:(64)word)
     ((word:num->(64)word) 64)))
    (s:armstate) =
    (k4:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (key_p:(64)word)
     ((word:num->(64)word) 80)))
    (s:armstate) =
    (k5:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (key_p:(64)word)
     ((word:num->(64)word) 96)))
    (s:armstate) =
    (k6:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (key_p:(64)word)
     ((word:num->(64)word) 112)))
    (s:armstate) =
    (k7:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (key_p:(64)word)
     ((word:num->(64)word) 128)))
    (s:armstate) =
    (k8:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (key_p:(64)word)
     ((word:num->(64)word) 144)))
    (s:armstate) =
    (k9:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (key_p:(64)word)
     ((word:num->(64)word) 160)))
    (s:armstate) =
    (k10:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (key_p:(64)word)
     ((word:num->(64)word) 176)))
    (s:armstate) =
    (k11:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (key_p:(64)word)
     ((word:num->(64)word) 192)))
    (s:armstate) =
    (k12:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (key_p:(64)word)
     ((word:num->(64)word) 208)))
    (s:armstate) =
    (k13:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (key_p:(64)word)
     ((word:num->(64)word) 224)))
    (s:armstate) =
    (k14:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     (htbl_p:(64)word))
    (s:armstate) =
    (h:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (htbl_p:(64)word)
     ((word:num->(64)word) 16)))
    (s:armstate) =
    (word_join:(64)word->(64)word->(128)word)
    ((karatsuba_mid:(128)word->(64)word)
    ((byteswap128:(128)word->(128)word)
    ((polyval_dot:(128)word->(128)word->(128)word)
     ((byteswap128:(128)word->(128)word) (h:(128)word))
    ((byteswap128:(128)word->(128)word) (h:(128)word)))))
    ((karatsuba_mid:(128)word->(64)word) (h:(128)word)) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (htbl_p:(64)word)
     ((word:num->(64)word) 32)))
    (s:armstate) =
    (byteswap128:(128)word->(128)word)
    ((polyval_dot:(128)word->(128)word->(128)word)
     ((byteswap128:(128)word->(128)word) (h:(128)word))
    ((byteswap128:(128)word->(128)word) (h:(128)word))) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (htbl_p:(64)word)
     ((word:num->(64)word) 48)))
    (s:armstate) =
    (byteswap128:(128)word->(128)word)
    ((polyval_dot:(128)word->(128)word->(128)word)
     ((polyval_dot:(128)word->(128)word->(128)word)
      ((byteswap128:(128)word->(128)word) (h:(128)word))
     ((byteswap128:(128)word->(128)word) (h:(128)word)))
    ((byteswap128:(128)word->(128)word) (h:(128)word))) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (htbl_p:(64)word)
     ((word:num->(64)word) 64)))
    (s:armstate) =
    (word_join:(64)word->(64)word->(128)word)
    ((karatsuba_mid:(128)word->(64)word)
    ((byteswap128:(128)word->(128)word)
    ((polyval_dot:(128)word->(128)word->(128)word)
     ((polyval_dot:(128)word->(128)word->(128)word)
      ((polyval_dot:(128)word->(128)word->(128)word)
       ((byteswap128:(128)word->(128)word) (h:(128)word))
      ((byteswap128:(128)word->(128)word) (h:(128)word)))
     ((byteswap128:(128)word->(128)word) (h:(128)word)))
    ((byteswap128:(128)word->(128)word) (h:(128)word)))))
    ((karatsuba_mid:(128)word->(64)word)
    ((byteswap128:(128)word->(128)word)
    ((polyval_dot:(128)word->(128)word->(128)word)
     ((polyval_dot:(128)word->(128)word->(128)word)
      ((byteswap128:(128)word->(128)word) (h:(128)word))
     ((byteswap128:(128)word->(128)word) (h:(128)word)))
    ((byteswap128:(128)word->(128)word) (h:(128)word))))) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (htbl_p:(64)word)
     ((word:num->(64)word) 80)))
    (s:armstate) =
    (byteswap128:(128)word->(128)word)
    ((polyval_dot:(128)word->(128)word->(128)word)
     ((polyval_dot:(128)word->(128)word->(128)word)
      ((polyval_dot:(128)word->(128)word->(128)word)
       ((byteswap128:(128)word->(128)word) (h:(128)word))
      ((byteswap128:(128)word->(128)word) (h:(128)word)))
     ((byteswap128:(128)word->(128)word) (h:(128)word)))
    ((byteswap128:(128)word->(128)word) (h:(128)word))) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (htbl_p:(64)word)
     ((word:num->(64)word) 96)))
    (s:armstate) =
    (byteswap128:(128)word->(128)word)
    ((polyval_dot:(128)word->(128)word->(128)word)
     ((polyval_dot:(128)word->(128)word->(128)word)
      ((polyval_dot:(128)word->(128)word->(128)word)
       ((polyval_dot:(128)word->(128)word->(128)word)
        ((byteswap128:(128)word->(128)word) (h:(128)word))
       ((byteswap128:(128)word->(128)word) (h:(128)word)))
      ((byteswap128:(128)word->(128)word) (h:(128)word)))
     ((byteswap128:(128)word->(128)word) (h:(128)word)))
    ((byteswap128:(128)word->(128)word) (h:(128)word))) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (htbl_p:(64)word)
     ((word:num->(64)word) 112)))
    (s:armstate) =
    (word_join:(64)word->(64)word->(128)word)
    ((karatsuba_mid:(128)word->(64)word)
    ((byteswap128:(128)word->(128)word)
    ((polyval_dot:(128)word->(128)word->(128)word)
     ((polyval_dot:(128)word->(128)word->(128)word)
      ((polyval_dot:(128)word->(128)word->(128)word)
       ((polyval_dot:(128)word->(128)word->(128)word)
        ((polyval_dot:(128)word->(128)word->(128)word)
         ((byteswap128:(128)word->(128)word) (h:(128)word))
        ((byteswap128:(128)word->(128)word) (h:(128)word)))
       ((byteswap128:(128)word->(128)word) (h:(128)word)))
      ((byteswap128:(128)word->(128)word) (h:(128)word)))
     ((byteswap128:(128)word->(128)word) (h:(128)word)))
    ((byteswap128:(128)word->(128)word) (h:(128)word)))))
    ((karatsuba_mid:(128)word->(64)word)
    ((byteswap128:(128)word->(128)word)
    ((polyval_dot:(128)word->(128)word->(128)word)
     ((polyval_dot:(128)word->(128)word->(128)word)
      ((polyval_dot:(128)word->(128)word->(128)word)
       ((polyval_dot:(128)word->(128)word->(128)word)
        ((byteswap128:(128)word->(128)word) (h:(128)word))
       ((byteswap128:(128)word->(128)word) (h:(128)word)))
      ((byteswap128:(128)word->(128)word) (h:(128)word)))
     ((byteswap128:(128)word->(128)word) (h:(128)word)))
    ((byteswap128:(128)word->(128)word) (h:(128)word))))) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (htbl_p:(64)word)
     ((word:num->(64)word) 128)))
    (s:armstate) =
    (byteswap128:(128)word->(128)word)
    ((polyval_dot:(128)word->(128)word->(128)word)
     ((polyval_dot:(128)word->(128)word->(128)word)
      ((polyval_dot:(128)word->(128)word->(128)word)
       ((polyval_dot:(128)word->(128)word->(128)word)
        ((polyval_dot:(128)word->(128)word->(128)word)
         ((byteswap128:(128)word->(128)word) (h:(128)word))
        ((byteswap128:(128)word->(128)word) (h:(128)word)))
       ((byteswap128:(128)word->(128)word) (h:(128)word)))
      ((byteswap128:(128)word->(128)word) (h:(128)word)))
     ((byteswap128:(128)word->(128)word) (h:(128)word)))
    ((byteswap128:(128)word->(128)word) (h:(128)word))) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (htbl_p:(64)word)
     ((word:num->(64)word) 144)))
    (s:armstate) =
    (byteswap128:(128)word->(128)word)
    ((polyval_dot:(128)word->(128)word->(128)word)
     ((polyval_dot:(128)word->(128)word->(128)word)
      ((polyval_dot:(128)word->(128)word->(128)word)
       ((polyval_dot:(128)word->(128)word->(128)word)
        ((polyval_dot:(128)word->(128)word->(128)word)
         ((polyval_dot:(128)word->(128)word->(128)word)
          ((byteswap128:(128)word->(128)word) (h:(128)word))
         ((byteswap128:(128)word->(128)word) (h:(128)word)))
        ((byteswap128:(128)word->(128)word) (h:(128)word)))
       ((byteswap128:(128)word->(128)word) (h:(128)word)))
      ((byteswap128:(128)word->(128)word) (h:(128)word)))
     ((byteswap128:(128)word->(128)word) (h:(128)word)))
    ((byteswap128:(128)word->(128)word) (h:(128)word))) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (htbl_p:(64)word)
     ((word:num->(64)word) 160)))
    (s:armstate) =
    (word_join:(64)word->(64)word->(128)word)
    ((karatsuba_mid:(128)word->(64)word)
    ((byteswap128:(128)word->(128)word)
    ((polyval_dot:(128)word->(128)word->(128)word)
     ((polyval_dot:(128)word->(128)word->(128)word)
      ((polyval_dot:(128)word->(128)word->(128)word)
       ((polyval_dot:(128)word->(128)word->(128)word)
        ((polyval_dot:(128)word->(128)word->(128)word)
         ((polyval_dot:(128)word->(128)word->(128)word)
          ((polyval_dot:(128)word->(128)word->(128)word)
           ((byteswap128:(128)word->(128)word) (h:(128)word))
          ((byteswap128:(128)word->(128)word) (h:(128)word)))
         ((byteswap128:(128)word->(128)word) (h:(128)word)))
        ((byteswap128:(128)word->(128)word) (h:(128)word)))
       ((byteswap128:(128)word->(128)word) (h:(128)word)))
      ((byteswap128:(128)word->(128)word) (h:(128)word)))
     ((byteswap128:(128)word->(128)word) (h:(128)word)))
    ((byteswap128:(128)word->(128)word) (h:(128)word)))))
    ((karatsuba_mid:(128)word->(64)word)
    ((byteswap128:(128)word->(128)word)
    ((polyval_dot:(128)word->(128)word->(128)word)
     ((polyval_dot:(128)word->(128)word->(128)word)
      ((polyval_dot:(128)word->(128)word->(128)word)
       ((polyval_dot:(128)word->(128)word->(128)word)
        ((polyval_dot:(128)word->(128)word->(128)word)
         ((polyval_dot:(128)word->(128)word->(128)word)
          ((byteswap128:(128)word->(128)word) (h:(128)word))
         ((byteswap128:(128)word->(128)word) (h:(128)word)))
        ((byteswap128:(128)word->(128)word) (h:(128)word)))
       ((byteswap128:(128)word->(128)word) (h:(128)word)))
      ((byteswap128:(128)word->(128)word) (h:(128)word)))
     ((byteswap128:(128)word->(128)word) (h:(128)word)))
    ((byteswap128:(128)word->(128)word) (h:(128)word))))) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (htbl_p:(64)word)
     ((word:num->(64)word) 176)))
    (s:armstate) =
    (byteswap128:(128)word->(128)word)
    ((polyval_dot:(128)word->(128)word->(128)word)
     ((polyval_dot:(128)word->(128)word->(128)word)
      ((polyval_dot:(128)word->(128)word->(128)word)
       ((polyval_dot:(128)word->(128)word->(128)word)
        ((polyval_dot:(128)word->(128)word->(128)word)
         ((polyval_dot:(128)word->(128)word->(128)word)
          ((polyval_dot:(128)word->(128)word->(128)word)
           ((byteswap128:(128)word->(128)word) (h:(128)word))
          ((byteswap128:(128)word->(128)word) (h:(128)word)))
         ((byteswap128:(128)word->(128)word) (h:(128)word)))
        ((byteswap128:(128)word->(128)word) (h:(128)word)))
       ((byteswap128:(128)word->(128)word) (h:(128)word)))
      ((byteswap128:(128)word->(128)word) (h:(128)word)))
     ((byteswap128:(128)word->(128)word) (h:(128)word)))
    ((byteswap128:(128)word->(128)word) (h:(128)word))) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     (in_p:(64)word))
    (s:armstate) =
    (bytes_to_int128:((8)word)list->(128)word)
    ((SUB_LIST:num#num->((8)word)list->((8)word)list) (0,16)
    (ibytes:((8)word)list)) /\
    (read:(armstate,(64)word)component->armstate->(64)word)
    (X16:(armstate,(64)word)component)
    (s:armstate) =
    (ivec_p:(64)word) /\
    (read:(armstate,(64)word)component->armstate->(64)word)
    (X10:(armstate,(64)word)component)
    (s:armstate) =
    (word_add:(64)word->(64)word->(64)word) (stackpointer:(64)word)
    ((word:num->(64)word) 64) /\
    (read:(armstate,(64)word)component->armstate->(64)word)
    (X15:(armstate,(64)word)component)
    (s:armstate) =
    (word:num->(64)word) 4294967296 /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q31:(armstate,(128)word)component)
    (s:armstate) =
    (word:num->(128)word) 79228162514264337593543950336 /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q19:(armstate,(128)word)component)
    (s:armstate) =
    (word_bytereverse:(128)word->(128)word) (xi:(128)word) /\
    (read:(armstate,(64)word)component->armstate->(64)word)
    (X4:(armstate,(64)word)component)
    (s:armstate) =
    (word_add:(64)word->(64)word->(64)word) (in_p:(64)word)
    ((word:num->(64)word) (16 * (nblk:num))) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q27:(armstate,(128)word)component)
    (s:armstate) =
    (k13:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q26:(armstate,(128)word)component)
    (s:armstate) =
    (k12:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q28:(armstate,(128)word)component)
    (s:armstate) =
    (k14:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q5:(armstate,(128)word)component)
    (s:armstate) =
    (aes13:(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word)
    ((gcm_ctr_inc:(128)word->(128)word)
    ((gcm_ctr_inc:(128)word->(128)word)
    ((gcm_ctr_inc:(128)word->(128)word)
    ((gcm_ctr_inc:(128)word->(128)word)
    ((gcm_ctr_inc:(128)word->(128)word) (ctr0:(128)word))))))
    (k0:(128)word)
    (k1:(128)word)
    (k2:(128)word)
    (k3:(128)word)
    (k4:(128)word)
    (k5:(128)word)
    (k6:(128)word)
    (k7:(128)word)
    (k8:(128)word)
    (k9:(128)word)
    (k10:(128)word)
    (k11:(128)word)
    (k12:(128)word)
    (k13:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q2:(armstate,(128)word)component)
    (s:armstate) =
    (aes13:(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word)
    ((gcm_ctr_inc:(128)word->(128)word)
    ((gcm_ctr_inc:(128)word->(128)word) (ctr0:(128)word)))
    (k0:(128)word)
    (k1:(128)word)
    (k2:(128)word)
    (k3:(128)word)
    (k4:(128)word)
    (k5:(128)word)
    (k6:(128)word)
    (k7:(128)word)
    (k8:(128)word)
    (k9:(128)word)
    (k10:(128)word)
    (k11:(128)word)
    (k12:(128)word)
    (k13:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q4:(armstate,(128)word)component)
    (s:armstate) =
    (aes13:(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word)
    ((gcm_ctr_inc:(128)word->(128)word)
    ((gcm_ctr_inc:(128)word->(128)word)
    ((gcm_ctr_inc:(128)word->(128)word)
    ((gcm_ctr_inc:(128)word->(128)word) (ctr0:(128)word)))))
    (k0:(128)word)
    (k1:(128)word)
    (k2:(128)word)
    (k3:(128)word)
    (k4:(128)word)
    (k5:(128)word)
    (k6:(128)word)
    (k7:(128)word)
    (k8:(128)word)
    (k9:(128)word)
    (k10:(128)word)
    (k11:(128)word)
    (k12:(128)word)
    (k13:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q3:(armstate,(128)word)component)
    (s:armstate) =
    (aes13:(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word)
    ((gcm_ctr_inc:(128)word->(128)word)
    ((gcm_ctr_inc:(128)word->(128)word)
    ((gcm_ctr_inc:(128)word->(128)word) (ctr0:(128)word))))
    (k0:(128)word)
    (k1:(128)word)
    (k2:(128)word)
    (k3:(128)word)
    (k4:(128)word)
    (k5:(128)word)
    (k6:(128)word)
    (k7:(128)word)
    (k8:(128)word)
    (k9:(128)word)
    (k10:(128)word)
    (k11:(128)word)
    (k12:(128)word)
    (k13:(128)word)|};;

(* THE SHARED 259-PREFIX LEMMA (proved ONCE; ~225s sim). *)
let WBN_FRONT_PREFIX_259 = prove(mk_wbn_prefix259_goal wbn_front_prefix259_postcond,
  WBN_FRONT_PREFIX259_TAC THEN wb_front_fold_tac THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[WORD_ADD_0] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REPEAT CONJ_TAC THEN MONOTONE_MAYCHANGE_TAC);;

(* ivec M2: the front's 8 `add v30` land Q30's top lane as
   word_add(word_add(...)(word 7))(word 1); this folds the +7+1 to +8 so the
   raw tower matches the gcm_ctr_raw (word 8) ctr0 literal.  Precomputed `let`
   value -- inlining the WORD_RULE in the tactic throws "RAND_CONV: Not a
   combination". *)
let WB_FRONT_Q30_TOPLANE = WORD_RULE
  `word_add (word_add (x:32 word) (word 7)) (word 1) = word_add x (word 8)`;;

(* THE SHARED FRONT LEMMA (5<=nblk<=8 band): chain WBN_FRONT_PREFIX_259
   (0x20->0x44c) via ENSURES_TRANS_SIMPLE, then the 0x44c b.ge TAKEN (d=0 for
   nblk<=8 => X5=in_p => reflexive compare) + 6 steps 268..273 to s273 (pc+3820).
   FUSED SPLICE (STEP 4): prefix exit shifted 0x444->0x44c (pc+1092->pc+1100),
   the b.ge tail steps 266..271 -> 268..273 (+2 for the 2 guard steps).  Now
   consumed only by prove_band 5..8; nblk<=4 takes the fused path. *)
let WB_FRONT_BUF = prove(mk_wb_front_goal wb_front_postcond,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC ENSURES_TRANS_SIMPLE THEN
  EXISTS_TAC wbn_front_prefix259_postcond THEN
  CONJ_TAC THENL
   [REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN MAYCHANGE_IDEMPOT_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC WBN_FRONT_PREFIX_259 THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ENSURES_INIT_TAC "s267" THEN
    RULE_ASSUM_TAC(REWRITE_RULE[WB_MC_LEN]) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[MP (SPEC `nblk:num` D_ZERO_LE8)
       (CONJ (MATCH_MP (ARITH_RULE `5 <= nblk ==> 1 <= nblk`) (ASSUME `5 <= nblk`))
             (ASSUME `nblk <= 8`))]) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[WORD_ADD_0]) THEN
    SUBGOAL_THEN `ival (in_p:int64) - ival in_p = &0` ASSUME_TAC THENL
     [CONV_TAC INT_ARITH; ALL_TAC] THEN
    (* s139/s140: split the batched (268--273) into (268--272)+(273--273).
       The .balign-16 +8 shift makes s273 (=ldp q24,q25,[x6,#160]) force a
       per-step normalization that batched ARM_STEPS_TAC defers, raising
       "RAND_CONV: Not a combination"; single-stepping s273 avoids it.
       Same EXEC/stepper/statement -> identical resulting theorem.
       (Fused splice: 266..271 -> 268..273, +2 for the guard steps.) *)
    ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (268--272) THEN
    ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (273--273) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
      `word_sub (word_add in_p (word (16 * nblk))) in_p:int64 = word (16 * nblk)`]) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[WB_FRONT_Q30_TOPLANE] THEN REWRITE_TAC[gcm_ctr_raw_def] THEN
    REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    REPEAT CONJ_TAC THEN MONOTONE_MAYCHANGE_TAC]);;
(* --- mid-load heap compaction: bound GC cost across this large single-file *)
(*     load (after a front-BUF sim); mirrors the needs-boundary/ckpt Gc.compact). --- *)
Gc.compact();;

(* ---- buffer-form band statements ------------------------------------------ *)
let mk_cph i = subst [mk_small_numeral(16*i),`nnn:num`]
  `bytes_to_int128 (SUB_LIST (nnn,16) (ibytes:byte list))`;;
let mk_ctr i =
  let rec go n = if n = 0 then `ctr0:int128`
    else mk_comb(`gcm_ctr_inc`, go (n-1)) in go i;;
let mk_outp_read i =
  let addr = if i = 0 then `out_p:int64`
    else subst [mk_small_numeral(16*i),`nnn:num`] `word_add out_p (word nnn):int64` in
  subst [addr,`aaa:int64`] `read (memory :> bytes128 (aaa:int64)) s:int128`;;
let mk_out_conj i =
  mk_eq(mk_outp_read i,
    subst [mk_cph i,`ccc:int128`; mk_ctr i,`ttt:int128`]
      `word_xor (ccc:int128) (aes256_encrypt (ttt:int128)
        [k0:int128;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14])`);;
let mk_ghash_list k =
  mk_flist(map (fun i -> mk_comb(`word_bytereverse:int128->int128`, mk_cph i)) (0--(k-1)));;

(* ivec M2: the band-exit counter write-back conjunct, spine form
   read [ivec_p] = gcm_ctr_inc_iter k ctr0 (used by mk_band_goal + WB_TAIL close). *)
let mk_ivec_conj k = subst [mk_small_numeral k,`kkk:num`]
    `read (memory :> bytes128 ivec_p) s = gcm_ctr_inc_iter kkk ctr0`;;

let mk_band_goal k =
  let n16 = mk_small_numeral(16*k) and n128 = mk_small_numeral(128*k) in
  let hyps = subst [n16,`sss:num`]
    `LENGTH (ibytes:byte list) = sss /\
     aligned 16 stackpointer /\
     nonoverlapping (word pc, LENGTH aesv8_gcm_8x_dec_256_wb_mc) (stackpointer:int64, 80) /\
     nonoverlapping (word pc, LENGTH aesv8_gcm_8x_dec_256_wb_mc) (out_p:int64, sss) /\
     nonoverlapping (word pc, LENGTH aesv8_gcm_8x_dec_256_wb_mc) (xi_p:int64, 16) /\
     nonoverlapping (word pc, LENGTH aesv8_gcm_8x_dec_256_wb_mc) (ivec_p:int64, 16) /\
     nonoverlapping (out_p, sss) (xi_p, 16) /\
     nonoverlapping (out_p, sss) (ivec_p, 16) /\
     nonoverlapping (xi_p, 16) (ivec_p, 16) /\
     nonoverlapping (ivec_p, 16) (in_p:int64, sss) /\
     nonoverlapping (ivec_p, 16) (key_p:int64, 240) /\
     nonoverlapping (ivec_p, 16) (htbl_p:int64, 192) /\
     nonoverlapping (in_p, sss) (stackpointer, 80) /\
     nonoverlapping (key_p, 240) (stackpointer, 80) /\
     nonoverlapping (htbl_p, 192) (stackpointer, 80) /\
     nonoverlapping (ivec_p, 16) (stackpointer, 80) /\
     nonoverlapping (xi_p, 16) (in_p, sss) /\
     nonoverlapping (xi_p, 16) (key_p, 240) /\
     nonoverlapping (xi_p, 16) (htbl_p, 192) /\
     nonoverlapping (xi_p, 16) (stackpointer, 80) /\
     nonoverlapping (out_p, sss) (in_p, sss) /\
     nonoverlapping (out_p, sss) (key_p, 240) /\
     nonoverlapping (out_p, sss) (htbl_p, 192) /\
     nonoverlapping (out_p, sss) (stackpointer, 80)` in
  let pre = subst [n16,`sss:num`; n128,`bbb:num`]
    `\s. aligned_bytes_loaded s (word pc) aesv8_gcm_8x_dec_256_wb_mc /\
        read PC s = word (pc + 0x20) /\ read SP s = stackpointer /\
        C_ARGUMENTS [in_p; word bbb; out_p; xi_p; ivec_p; key_p; htbl_p] s /\
        read (memory :> bytes (in_p, sss)) s = num_of_bytelist ibytes /\
        read (memory :> bytes128 xi_p) s = xi /\
        read (memory :> bytes128 ivec_p) s = ctr0 /\
        read (memory :> bytes128 key_p) s = k0 /\
        read (memory :> bytes128 (word_add key_p (word 16))) s = k1 /\
        read (memory :> bytes128 (word_add key_p (word 32))) s = k2 /\
        read (memory :> bytes128 (word_add key_p (word 48))) s = k3 /\
        read (memory :> bytes128 (word_add key_p (word 64))) s = k4 /\
        read (memory :> bytes128 (word_add key_p (word 80))) s = k5 /\
        read (memory :> bytes128 (word_add key_p (word 96))) s = k6 /\
        read (memory :> bytes128 (word_add key_p (word 112))) s = k7 /\
        read (memory :> bytes128 (word_add key_p (word 128))) s = k8 /\
        read (memory :> bytes128 (word_add key_p (word 144))) s = k9 /\
        read (memory :> bytes128 (word_add key_p (word 160))) s = k10 /\
        read (memory :> bytes128 (word_add key_p (word 176))) s = k11 /\
        read (memory :> bytes128 (word_add key_p (word 192))) s = k12 /\
        read (memory :> bytes128 (word_add key_p (word 208))) s = k13 /\
        read (memory :> bytes128 (word_add key_p (word 224))) s = k14 /\
        htable_mem_dec h htbl_p s` in
  let pc_post = `read PC s = word (pc + 4560)` in
  let outs = map mk_out_conj (0--(k-1)) in
  let xi_post = subst [mk_ghash_list k,`lll:int128 list`]
    `read (memory :> bytes128 xi_p) s =
     word_bytereverse
       (ghash_polyval_acc (byteswap128 h) (word_bytereverse xi) (lll:int128 list))` in
  (* ivec M2: the counter write-back at band exit r.  Spine form
     gcm_ctr_inc_iter r ctr0 (= gcm_ctr_add (word r) ctr0); closed by
     WB_IVEC_CLOSE_TAC r in each WB_TAIL_r_TAC. *)
  let ivec_post = mk_ivec_conj k in
  let post = mk_abs(`s:armstate`, end_itlist (curry mk_conj) (pc_post :: outs @ [xi_post; ivec_post])) in
  let frame = subst [n16,`sss:num`]
    `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
     MAYCHANGE [memory :> bytes(out_p:int64, sss); memory :> bytes(xi_p:int64, 16);
                memory :> bytes(ivec_p:int64, 16);
                memory :> bytes(word_add stackpointer (word 64):int64, 16)] ,,
     MAYCHANGE [Q0;Q1;Q2;Q3;Q4;Q5;Q6;Q7;Q8;Q9;Q10;Q11;Q12;Q13;Q14;Q15;
                Q16;Q17;Q18;Q19;Q20;Q21;Q22;Q23;Q24;Q25;Q26;Q27;Q28;Q29;Q30;Q31]` in
  let ens = subst [pre,`PPP:armstate->bool`; post,`QQQ:armstate->bool`;
                   frame,`CCC:armstate->armstate->bool`] `ensures arm PPP QQQ CCC` in
  let vars = subtract wb_front_vars [`nblk:num`] in
  list_mk_forall(vars, mk_imp(hyps, ens));;

(* ---- recomposition machinery ---------------------------------------------- *)
let arith_16k k = ARITH_RULE(mk_eq(mk_binop `( * ):num->num->num` `16` (mk_small_numeral k),
                                   mk_small_numeral(16*k)));;
let arith_128k k = ARITH_RULE(mk_eq(mk_binop `( * ):num->num->num` `128` (mk_small_numeral k),
                                    mk_small_numeral(128*k)));;
(* front lemma instantiated at nblk:=k, arithmetic normalized *)
let wbf_at k = REWRITE_RULE[arith_16k k; arith_128k k]
  (SPECL [`pc:num`;`stackpointer:int64`;`out_p:int64`;`xi_p:int64`;`ivec_p:int64`;
          `in_p:int64`;`key_p:int64`;`htbl_p:int64`; mk_small_numeral k;
          `ibytes:byte list`;`xi:int128`;`ctr0:int128`;`k0:int128`;`k1:int128`;
          `k2:int128`;`k3:int128`;`k4:int128`;`k5:int128`;`k6:int128`;`k7:int128`;
          `k8:int128`;`k9:int128`;`k10:int128`;`k11:int128`;`k12:int128`;
          `k13:int128`;`k14:int128`;`h:int128`] WB_FRONT_BUF);;
(* intermediate assertion = WB_FRONT_BUF's postcond @ nblk:=k, normalized *)
let q_at k = rhs(concl(REWRITE_CONV[arith_16k k; arith_128k k]
  (vsubst [mk_small_numeral k,`nblk:num`] wb_front_postcond)));;
(* doubled frame for ENSURES_FRAME_SUBSUMED (F ,, F subsumes to F) *)
let fdbl_at k =
  let fs = subst [mk_small_numeral(16*k),`sss:num`]
    `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
     MAYCHANGE [memory :> bytes(out_p:int64, sss); memory :> bytes(xi_p:int64, 16);
                memory :> bytes(ivec_p:int64, 16); memory :> bytes(word_add stackpointer (word 64):int64, 16)] ,,
     MAYCHANGE [Q0;Q1;Q2;Q3;Q4;Q5;Q6;Q7;Q8;Q9;Q10;Q11;Q12;Q13;Q14;Q15;
                Q16;Q17;Q18;Q19;Q20;Q21;Q22;Q23;Q24;Q25;Q26;Q27;Q28;Q29;Q30;Q31]` in
  mk_binop `(,,):(armstate->armstate->bool)->(armstate->armstate->bool)->(armstate->armstate->bool)` fs fs;;

(* h-power towers: dot j = polyval_dot^(j-1) over byteswap128 h *)
let rec hdot j = if j = 1 then `byteswap128 h`
  else mk_comb(mk_comb(`polyval_dot:int128->int128->int128`, hdot (j-1)), `byteswap128 h`);;
let mk_habbrev j =
  let hv = mk_var("h"^string_of_int j, `:int128`) in
  ABBREV_TAC (mk_eq(hv, mk_comb(`byteswap128:int128->int128`, hdot j))) THEN
  SUBGOAL_THEN (mk_eq(mk_comb(`byteswap128:int128->int128`, hv), hdot j)) ASSUME_TAC THENL
  [EXPAND_TAC ("h"^string_of_int j) THEN REWRITE_TAC[BYTESWAP128_INVOLUTION]; ALL_TAC];;

(* Back-leg prep for band k: init at the s265 assertion, concretize the flags,
   derive input lanes 1..k-1, abbreviate cph names + h powers so the verbatim
   the <=8-block chain tails apply unchanged. *)
let WB_PREP_TAC k =
  let n16 = mk_small_numeral(16*k) in
  let lanes =
    if k = 1 then ALL_TAC else
    SUBGOAL_THEN (subst [mk_small_numeral k,`kkk:num`]
      `!i. i < kkk ==> read (memory :> bytes128 (word_add in_p (word (16 * i)))) s265 =
              bytes_to_int128 (SUB_LIST (16 * i, 16) (ibytes:byte list))`)
      MP_TAC THENL
    [MATCH_MP_TAC INPUT_BYTES_TO_BYTE128_LANES THEN
     SUBGOAL_THEN (subst [n16,`sss:num`] `SUB_LIST (0,sss) (ibytes:byte list) = ibytes`)
       (fun th -> ASM_REWRITE_TAC[th; LE_REFL;
          ARITH_RULE(mk_eq(mk_binop `( * ):num->num->num` `16` (mk_small_numeral k), n16))]) THEN
     MATCH_MP_TAC SUB_LIST_LENGTH_IMPLIES THEN ASM_REWRITE_TAC[LE_REFL];
     DISCH_THEN(fun lth ->
       EVERY(map (fun i ->
         ASSUME_TAC(CONV_RULE(DEPTH_CONV NUM_RED_CONV)
           (MP (SPEC (mk_small_numeral i) lth)
               (ARITH_RULE(mk_binop `(<):num->num->bool` (mk_small_numeral i) (mk_small_numeral k))))))
         (1--(k-1))))] in
  let cphs =
    if k = 1 then ABBREV_TAC (mk_eq(`cph:int128`, mk_cph 0))
    else EVERY(map (fun i ->
      ABBREV_TAC (mk_eq(mk_var("cph"^string_of_int i,`:int128`), mk_cph i))) (0--(k-1))) in
  let habbrevs = if k = 1 then ALL_TAC else EVERY(map mk_habbrev (2--k)) in
  CLEAR_KEEPGH_MEMO_TAC THEN  (* refine-100: reset the KEEPGH normalizer fixpoint cache per tail body *)
  REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS] THEN ENSURES_INIT_TAC "s265" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WB_MC_LEN]) THEN
  RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV WORD_REDUCE_CONV)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[]) THEN
  lanes THEN cphs THEN habbrevs;;

(* ========================================================================= *)
(* SPEED REFACTOR -- the shared per-block back-leg, proved ONCE.              *)
(*                                                                            *)
(* The back-leg sim `WB_PREP_TAC k THEN WB_TAIL_k_TAC` (init@s265 -> whole-   *)
(* function exit pc+4528) was previously run TWICE per k: once inside         *)
(* prove_band (from the full q_at k precond) and once as WB_TAIL_GEN2_k       *)
(* (from a strictly WEAKER precond, q_at k minus 6 objdump-dead cells).  The  *)
(* two goals share IDENTICAL post + frame (both via mk_band_goal k), so the   *)
(* WEAK-precond back-leg IMPLIES the full-precond one by conjunct-drop         *)
(* weakening (ENSURES_PRECONDITION_THM, no re-simulation).  We therefore      *)
(* prove the WEAK back-leg (WB_TAIL_GEN2_k) ONCE, HERE, and reuse it in both  *)
(* prove_band (below) and the nblk>8 recomposition (WBN_PREP_TO_END, later).  *)
(* Net: 8 per-block tail sims instead of 16 (~1,700s / ~28min off cold load). *)
(*                                                                            *)
(* The 6 dropped cells (sp+72, xi_p, ivec_p, in_p block-0, X1, X9) are        *)
(* objdump-confirmed never read by the tail range [0xed4,0x11b0); each        *)
(* WB_TAIL_GEN2_k proving hyps=0 from the weak precond IS the in-proof audit  *)
(* of that.  (These notes were formerly at the WB_TAIL_GEN2 site.)            *)
(* ------------------------------------------------------------------------- *)

(* the band goal split into (vars, hyps, pre, post, frame) *)
let wbn_dissect_band k =
  let g = mk_band_goal k in
  let vars, body = strip_forall g in
  let hyps, ens = dest_imp body in
  let _, args = strip_comb ens in
  (vars, hyps, el 1 args, el 2 args, el 3 args);;

(* the 4 seam cells EXT2 drops -- objdump-confirmed never read by the tail,  *)
(* re-confirmed in-proof by proving the back-leg from the precond without    *)
(* them.  [sp+72]=0 is a pinned artifact; xi_p/ivec_p are                    *)
(* consumed only via the pre-seeded Q19/Q16 and Q0..Q7; in_p block-0 arrives *)
(* pre-loaded in Q9 (WBN_Q9_SPEC).                                           *)
let wbn_tail_drop_lhs = [
  `read (memory :> bytes64 (word_add stackpointer (word 72))) (s:armstate)`;
  `read (memory :> bytes128 xi_p) (s:armstate)`;
  `read (memory :> bytes128 ivec_p) (s:armstate)`;
  `read (memory :> bytes128 in_p) (s:armstate)`];;

(* 6-cell drop: the 4 cells PLUS the dead X1,X9.                             *)
let wbn_tail_drop_lhs6 = wbn_tail_drop_lhs @
  [`read X1 (s:armstate)`; `read X9 (s:armstate)`];;
let wbn_weak_q_at6 k =
  let cs = conjuncts (snd(dest_abs (q_at k))) in
  let kept = filter (fun c -> not (is_eq c && mem (lhs c) wbn_tail_drop_lhs6)) cs in
  mk_abs(`s:armstate`, end_itlist (curry mk_conj) kept);;
let wbn_tail_backleg_goal6 r =
  let (vars, hyps, pre0, post, frame) = wbn_dissect_band r in
  ignore pre0;
  let ens = list_mk_comb(`ensures arm`, [wbn_weak_q_at6 r; post; frame]) in
  list_mk_forall(vars, mk_imp(hyps, ens));;
(* ======================================================================= *)
(* ivec M2: counter algebra HOISTED here (from Sec 2 @~6059 and               *)
(* Sec 9b @~9714) so WB_IVEC_CLOSE_TAC's deps (gcm_ctr_add, GCM_CTR_ADD_LANES, *)
(* GCM_CTR_INC_ITER_ADD, the SUBW_RAW lemmas) are in scope for the band tail   *)
(* ivec close below.  gcm_ctr_raw_def is already at ~3237 (s100 EDIT-0 hoist). *)
(* ======================================================================= *)
(* ------------------------------------------------------------------------- *)
(* 2. Symbolic counter layer: gcm_ctr_add w = "add w to the be-top-lane".    *)
(*    Gives the invariant a closed counter form at symbolic block index:     *)
(*    gcm_ctr_inc_iter k x = gcm_ctr_add (word k) x.                         *)
(*                                                                           *)
(*    OOM WARNING: do NOT prove GCM_CTR_ADD_LANES by direct BITBLAST -- the  *)
(*    symbolic 32-bit addend makes the BDD blow past 30GB.  The factoring    *)
(*    below keeps every BITBLAST wiring-only                                  *)
(*    (word_add never meets the BDD); whole layer proves in <1s.             *)
(* ------------------------------------------------------------------------- *)

let gcm_ctr_add = new_definition
 `gcm_ctr_add (w:32 word) (ivec:128 word) : 128 word =
   word_insert ivec (96,32)
     (word_bytereverse
        (word_add (word_bytereverse (word_subword ivec (96,32):(32)word)) w))`;;

let GCM_CTR_ADD_1 = prove
 (`gcm_ctr_add (word 1) = gcm_ctr_inc`,
  REWRITE_TAC[FUN_EQ_THM; gcm_ctr_add; gcm_ctr_inc]);;

(* wiring-only: byte decomposition of the byte-reversed top lane *)
let BREV_TOP_LANE = prove
 (`!ctr0:int128.
     word_bytereverse (word_subword ctr0 (96,32):32 word) =
     word_join
      (word_join (word_subword ctr0 (96,8):8 word) (word_subword ctr0 (104,8):8 word):16 word)
      (word_join (word_subword ctr0 (112,8):8 word) (word_subword ctr0 (120,8):8 word):16 word)`,
  GEN_TAC THEN BITBLAST_TAC);;

(* wiring-only: insert of brev s as the byte-join tower; s stays FREE so the
   abstract add never enters the BDD *)
let INSERT_BREV_WIRING = prove
 (`!(ctr0:int128) (s:32 word).
     word_insert ctr0 (96,32) (word_bytereverse s) : 128 word =
     word_join
      (word_join
       (word_join
        (word_join (word_subword s (0,8):8 word) (word_subword s (8,8):8 word):16 word)
        (word_join (word_subword s (16,8):8 word) (word_subword s (24,8):8 word):16 word)
        :32 word)
       (word_join
        (word_join (word_subword ctr0 (88,8):8 word) (word_subword ctr0 (80,8):8 word):16 word)
        (word_join (word_subword ctr0 (72,8):8 word) (word_subword ctr0 (64,8):8 word):16 word)
        :32 word) :64 word)
      (word_join
       (word_join
        (word_join (word_subword ctr0 (56,8):8 word) (word_subword ctr0 (48,8):8 word):16 word)
        (word_join (word_subword ctr0 (40,8):8 word) (word_subword ctr0 (32,8):8 word):16 word)
        :32 word)
       (word_join
        (word_join (word_subword ctr0 (24,8):8 word) (word_subword ctr0 (16,8):8 word):16 word)
        (word_join (word_subword ctr0 (8,8):8 word) (word_subword ctr0 (0,8):8 word):16 word)
        :32 word) :64 word)`,
  REPEAT GEN_TAC THEN BITBLAST_TAC);;

(* the generic-w lanes lemma: RHS built programmatically from
   GCM_CTR_INC_LANES with `w` for `word 1` (exactly the harvested Q-lane
   shape from the front sim); proof is pure rewriting *)
let GCM_CTR_ADD_LANES =
  let lanes_w = subst [`w:32 word`,`word 1:32 word`]
    (rhs(snd(strip_forall(concl GCM_CTR_INC_LANES)))) in
  let gl = list_mk_forall([`w:32 word`;`ctr0:int128`],
    mk_eq(list_mk_comb(`gcm_ctr_add`,[`w:32 word`;`ctr0:int128`]), lanes_w)) in
  prove(gl,
    REPEAT GEN_TAC THEN
    REWRITE_TAC[gcm_ctr_add; BREV_TOP_LANE; INSERT_BREV_WIRING]);;

(* algebra of the symbolic add *)
let SUBWORD_INSERT_TOP = prove
 (`!(x:int128) (v:32 word). word_subword (word_insert x (96,32) v : int128) (96,32) = v`,
  REPEAT GEN_TAC THEN BITBLAST_TAC);;

let INSERT_INSERT_TOP = prove
 (`!(x:int128) (u:32 word) (v:32 word).
     word_insert (word_insert x (96,32) (u:32 word) : int128) (96,32) (v:32 word) : int128 =
     word_insert x (96,32) v`,
  REPEAT GEN_TAC THEN BITBLAST_TAC);;

let BREV_BREV_32 = prove
 (`!s:32 word. word_bytereverse (word_bytereverse s) = s`,
  GEN_TAC THEN BITBLAST_TAC);;

let INSERT_SELF_TOP = prove
 (`!x:int128. word_insert x (96,32) (word_subword x (96,32):32 word) : int128 = x`,
  GEN_TAC THEN BITBLAST_TAC);;

let GCM_CTR_ADD_COMPOSE = prove
 (`!(u:32 word) (v:32 word) (x:int128).
     gcm_ctr_add v (gcm_ctr_add u x) = gcm_ctr_add (word_add u v) x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[gcm_ctr_add] THEN
  REWRITE_TAC[SUBWORD_INSERT_TOP; INSERT_INSERT_TOP; BREV_BREV_32] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE);;

let GCM_CTR_ADD_0 = prove
 (`!x:int128. gcm_ctr_add (word 0) x = x`,
  GEN_TAC THEN REWRITE_TAC[gcm_ctr_add; WORD_ADD_0; BREV_BREV_32; INSERT_SELF_TOP]);;

(* the closed form the ENSURES_WHILE invariant needs: counter at symbolic
   block index k *)
let GCM_CTR_INC_ITER_ADD = prove
 (`!k x:int128. gcm_ctr_inc_iter k x = gcm_ctr_add (word k) x`,
  INDUCT_TAC THEN GEN_TAC THENL
   [REWRITE_TAC[gcm_ctr_inc_iter; GCM_CTR_ADD_0];
    ASM_REWRITE_TAC[gcm_ctr_inc_iter] THEN
    REWRITE_TAC[GSYM GCM_CTR_ADD_1; GCM_CTR_ADD_COMPOSE] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[ADD1; GSYM WORD_ADD] THEN
    CONV_TAC WORD_RULE]);;

(* the 4 lane-extraction lemmas (used to prove GCM_CTR_RAW_INCR without a
   symbolic-w WORD_BLAST, which OOMs -- see Sec 2 AVOID note).  Each proves fast
   via WORD_SIMPLE_SUBWORD_CONV (extracts the lane) then WORD_BLAST (w appears
   only additively in the top lane, the addend never enters the BDD). *)
let SUBW_RAW_96 = prove
 (`word_subword (gcm_ctr_raw w ctr0) (96,32):32 word =
   word_add (word_join (word_join (word_subword ctr0 (96,8):8 word) (word_subword ctr0 (104,8):8 word):16 word)
     (word_join (word_subword ctr0 (112,8):8 word) (word_subword ctr0 (120,8):8 word):16 word):32 word) w`,
  REWRITE_TAC[gcm_ctr_raw_def] THEN CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN CONV_TAC WORD_BLAST);;
let SUBW_RAW_64 = prove
 (`word_subword (gcm_ctr_raw w ctr0) (64,32):32 word =
   word_join (word_join (word_subword ctr0 (64,8):8 word) (word_subword ctr0 (72,8):8 word):16 word)
     (word_join (word_subword ctr0 (80,8):8 word) (word_subword ctr0 (88,8):8 word):16 word):32 word`,
  REWRITE_TAC[gcm_ctr_raw_def] THEN CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN CONV_TAC WORD_BLAST);;
let SUBW_RAW_32 = prove
 (`word_subword (gcm_ctr_raw w ctr0) (32,32):32 word =
   word_join (word_join (word_subword ctr0 (32,8):8 word) (word_subword ctr0 (40,8):8 word):16 word)
     (word_join (word_subword ctr0 (48,8):8 word) (word_subword ctr0 (56,8):8 word):16 word):32 word`,
  REWRITE_TAC[gcm_ctr_raw_def] THEN CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN CONV_TAC WORD_BLAST);;
let SUBW_RAW_0 = prove
 (`word_subword (gcm_ctr_raw w ctr0) (0,32):32 word =
   word_join (word_join (word_subword ctr0 (0,8):8 word) (word_subword ctr0 (8,8):8 word):16 word)
     (word_join (word_subword ctr0 (16,8):8 word) (word_subword ctr0 (24,8):8 word):16 word):32 word`,
  REWRITE_TAC[gcm_ctr_raw_def] THEN CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN CONV_TAC WORD_BLAST);;

(* the increment: `add v30.4s,v30.4s,v31.4s` (v31 = word 2^96) is a lane-wise
   32-bit add; the model emits it as word_join of word_add(word_subword v30 lane)(word c)
   with c=1 on the top lane, 0 elsewhere.  This advances the raw counter by 1. *)
let GCM_CTR_RAW_INCR = prove
 (`word_join
    (word_join
     (word_add (word_subword (gcm_ctr_raw w ctr0) (96,32):32 word) (word 1))
     (word_add (word_subword (gcm_ctr_raw w ctr0) (64,32):32 word) (word 0)):64 word)
    (word_join
     (word_add (word_subword (gcm_ctr_raw w ctr0) (32,32):32 word) (word 0))
     (word_add (word_subword (gcm_ctr_raw w ctr0) (0,32):32 word) (word 0)):64 word):int128 =
    gcm_ctr_raw (word_add w (word 1)) ctr0`,
  REWRITE_TAC[SUBW_RAW_96; SUBW_RAW_64; SUBW_RAW_32; SUBW_RAW_0; WORD_ADD_0] THEN
  GEN_REWRITE_TAC RAND_CONV [gcm_ctr_raw_def] THEN
  REWRITE_TAC[WORD_RULE
    `!(x:32 word) w. word_add (word_add x w) (word 1) = word_add x (word_add w (word 1))`]);;

(* ------------------------------------------------------------------------- *)
(* ivec M2: the band-tail ivec write-back closer.                             *)
(*                                                                            *)
(* Each band r stores rev32(v30) to [ivec_p] (str q30,[x16], .S:1468 cascade /*)
(* :1698 drain).  With Q30 = gcm_ctr_raw (word 8) ctr0 carried in from the    *)
(* front postcond (s100 EDIT 0), the store value is Q30 after (8-r) `sub v30` *)
(* decrements -- gcm_ctr_raw (word 8) minus (8-r) = gcm_ctr_raw (word r), and *)
(* rev32 of that = gcm_ctr_add (word r) = gcm_ctr_inc_iter r ctr0.  The close  *)
(* runs entirely in 32-bit-lane algebra (SUBW_RAW_* pins the sub cascade to   *)
(* the top lane; GCM_CTR_ADD_LANES gives the rev target) so no 128-bit blast  *)
(* meets the symbolic counter.  Validated r=1,2,8 hyps=0.                     *)
(* (mk_ivec_conj is defined just above mk_band_goal, since mk_band_goal uses it.) *)
(* ------------------------------------------------------------------------- *)
let sub_chain c n =
  let rec build acc k = if k=0 then acc
    else build (mk_comb(mk_comb(`word_sub:32 word->32 word->32 word`,acc),
                        mk_comb(`word:num->32 word`,mk_small_numeral c))) (k-1) in
  let lh = build `x:32 word` n in
  WORD_RULE(mk_eq(lh, if c=0 then `x:32 word`
                       else mk_comb(mk_comb(`word_sub:32 word->32 word->32 word`,`x:32 word`),
                                    mk_comb(`word:num->32 word`,mk_small_numeral n))));;
let SUBW_NORM r = WORD_RULE(subst[mk_small_numeral(8-r),`d:num`; mk_small_numeral r,`rr:num`]
  `word_sub (word_add (x:32 word) (word 8)) (word d) = word_add x (word rr)`);;
let WB_IVEC_CLOSE_TAC r =
  REWRITE_TAC[GCM_CTR_INC_ITER_ADD] THEN
  REWRITE_TAC[sub_chain 1 (8-r); sub_chain 0 (8-r)] THEN
  REWRITE_TAC[gcm_ctr_raw_def; SUBW_RAW_96; SUBW_RAW_64; SUBW_RAW_32; SUBW_RAW_0] THEN
  REWRITE_TAC[SUBW_NORM r; WORD_SUB_0] THEN
  GEN_REWRITE_TAC RAND_CONV [GCM_CTR_ADD_LANES] THEN
  W(fun (_,gw) ->
     let atom = find_term (fun t -> match t with
       | Comb(Comb(Const("word_add",_),_),Comb(Const("word",_),_)) -> true | _ -> false) gw in
     SPEC_TAC(atom, `aa:32 word`)) THEN
  GEN_TAC THEN CONV_TAC WORD_BLAST;;

(* The 8 shared back-legs -- the ONLY per-block tail sims in the file now.    *)
(* Each ~130-315s; each hyps=0 IS the per-r X1/X9 dead-cell audit.            *)
let WB_TAIL_GEN2_1 = prove(wbn_tail_backleg_goal6 1,
  REPEAT GEN_TAC THEN STRIP_TAC THEN WB_PREP_TAC 1 THEN WB_TAIL_1_TAC (WB_IVEC_CLOSE_TAC 1));;
let WB_TAIL_GEN2_2 = prove(wbn_tail_backleg_goal6 2,
  REPEAT GEN_TAC THEN STRIP_TAC THEN WB_PREP_TAC 2 THEN WB_TAIL_2_TAC (WB_IVEC_CLOSE_TAC 2));;
let WB_TAIL_GEN2_3 = prove(wbn_tail_backleg_goal6 3,
  REPEAT GEN_TAC THEN STRIP_TAC THEN WB_PREP_TAC 3 THEN WB_TAIL_3_TAC (WB_IVEC_CLOSE_TAC 3));;
let WB_TAIL_GEN2_4 = prove(wbn_tail_backleg_goal6 4,
  REPEAT GEN_TAC THEN STRIP_TAC THEN WB_PREP_TAC 4 THEN WB_TAIL_4_TAC (WB_IVEC_CLOSE_TAC 4));;
let WB_TAIL_GEN2_5 = prove(wbn_tail_backleg_goal6 5,
  REPEAT GEN_TAC THEN STRIP_TAC THEN WB_PREP_TAC 5 THEN WB_TAIL_5_TAC (WB_IVEC_CLOSE_TAC 5));;
let WB_TAIL_GEN2_6 = prove(wbn_tail_backleg_goal6 6,
  REPEAT GEN_TAC THEN STRIP_TAC THEN WB_PREP_TAC 6 THEN WB_TAIL_6_TAC (WB_IVEC_CLOSE_TAC 6));;
let WB_TAIL_GEN2_7 = prove(wbn_tail_backleg_goal6 7,
  REPEAT GEN_TAC THEN STRIP_TAC THEN WB_PREP_TAC 7 THEN WB_TAIL_7_TAC (WB_IVEC_CLOSE_TAC 7));;
let WB_TAIL_GEN2_8 = prove(wbn_tail_backleg_goal6 8,
  REPEAT GEN_TAC THEN STRIP_TAC THEN WB_PREP_TAC 8 THEN WB_TAIL_8_TAC (WB_IVEC_CLOSE_TAC 8));;
(* --- mid-load heap compaction: bound GC cost after the 8 shared back-leg    *)
(*     sims (the file's heaviest per-block work); mirrors the ckpt Gc.compact. *)
Gc.compact();;

(* The band prover: split at pc+3796 via FRAME_SUBSUMED + TRANS
   (ENSURES_SEQUENCE_TAC throws MAYCHANGE_IDEMPOT on this frame), discharge
   the front leg with WB_FRONT_BUF; the back leg is then DISCHARGED (not
   re-simulated) from the pre-proved WB_TAIL_GEN2_k by precondition-weakening
   (q_at k ==> the 6-cell-dropped weak precond), the same ENSURES_PRECONDITION
   idiom used for the shifted tail feed later in the file. *)

(* >>> STEP 4.2 FUSED ARC BEGIN (session 146) <<< *)
(* ========================================================================= *)
(* FUSED SMALL-PATH ARC (STEP 4.2): the 4 fused block proofs (k=1..4) + the   *)
(* raw->band bridge, inlined from aes-gcm-fused-wip @ a311140b                *)
(* (fused-wip/session-{122,126,132,133}-work + fused-wip/fused_common.ml).    *)
(* Each WB_FUSED_kBLOCK pays a ~13-min prove-replay (finite).  BUF_{1..4}BLOCK *)
(* are then derived from them via ENSURES_PRECONDITION_THM (no re-sim), giving *)
(* exactly mk_band_goal k so prove_band 1..4 are REPLACED (they needed 5<=nblk).*)
(* ========================================================================= *)

(* ---- fused_common.ml helpers (inlined; needs-dropped) ---- *)
(* ============================================================================
   fused_common.ml — shared tactic library for the d5 fused small-path arc.

   Extracted (refine-094, MODE=elegance) from the four canonical fused block
   proofs, which each redefined these helpers verbatim (byte-identical, md5-
   confirmed) because each is loaded STANDALONE on the fused DMTCP checkpoint.
   Collapsing them here removes ~190 lines of cross-file duplication with no
   change to behaviour: the definitions below are copied verbatim from the
   canonical files.

   Load prereq: the fused checkpoint (hol-wb-dec-fused-rebased.ckpt), which
   supplies GCM_SIMD_SIMPLIFY_CORE_TAC, CLARIFY_TAC, ARM_VERBOSE_STEP_TAC,
   DISCARD_ASSUMPTIONS_TAC, WORD_PMUL_SYM, polyval_dot, etc.  Each fused block
   proof `needs "fused-wip/fused_common.ml"` at its top and drops its local
   copies.

   Contents:
     DISCARD_OLDSTATE_KEEPGHALL_TAC   (was in k=1,2,3,4)
     ARM_STEPS_FOLD_KEEPGHALL_TAC     (was in k=1,2,3,4)
     JOIN_IS_CTR0                     (was in k=1,2,3,4)
     INLINE_SELFCONTAINED             (was in k=2,3,4)
     POLYVAL_DOT_SYM                  (was in k=3,4)
   ============================================================================ *)

(* ---- state-discard helper that keeps the GHASH accumulator regs + htbl loads ---- *)
let DISCARD_OLDSTATE_KEEPGHALL_TAC s =
  let v = mk_var(s,`:armstate`) in
  let rec unbound_statevars_of_read bound tm = match tm with
      Comb(Comb(Const("read",_),_),st) -> if mem st bound then [] else [st]
    | Comb(a,b) -> union (unbound_statevars_of_read bound a) (unbound_statevars_of_read bound b)
    | Abs(vv,t) -> unbound_statevars_of_read (vv::bound) t | _ -> [] in
  let rec mentions_htbl t = match t with
      Var("htbl_p",_) -> true
    | Comb(a,b) -> mentions_htbl a || mentions_htbl b | Abs(_,t2) -> mentions_htbl t2 | _ -> false in
  let rec mentions_ghreg t = match t with
      Comb(Comb(Const("read",_),cmp),_) ->
        (match cmp with Const(n,_) -> n="Q16"||n="Q17"||n="Q18"||n="Q19"||n="Q20"||n="Q21"||n="Q22"||n="Q23"||n="Q24"||n="Q25"||n="Q26"||n="Q30" | _ -> false)
    | Comb(a,b) -> mentions_ghreg a || mentions_ghreg b | Abs(_,t2) -> mentions_ghreg t2 | _ -> false in
  DISCARD_ASSUMPTIONS_TAC(fun thm ->
    if mentions_ghreg (concl thm) then false else
    if (match concl thm with
        | Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),cmp),_)),_) -> mentions_htbl cmp
        | _ -> false) then false else
    let us = unbound_statevars_of_read [] (concl thm) in
    if us = [] || us = [v] then false else if not(mem v us) then true else true);;

(* ---- Q-scoped, FIXPOINT-MEMOIZED per-step SIMD normalizer (refine-097 + refine-099) ----
   Same three rewrite passes as the shared GCM_SIMD_SIMPLIFY_CORE_TAC (lemmas.ml),
   but applied ONLY to `read Qn s = ...` assumptions (refine-097 Q-scope).  In the
   KEEPGHALL windows the discard KEEPS the full multi-block GHASH accumulator history,
   so the pile grows to ~400-1000 assumptions of which ~215 are memory reads, ~22
   nonoverlapping and the rest non-Q / flags — none of which the SIMD rules (REV64 lanes
   / WORD_SWAP_HALVES / EXT8_LANE0 / REV32_LANE_SUBWORD) can EVER rewrite.  The Q-scope
   already skips those, but the surviving ~200-400 Q-reads are RE-WALKED every step even
   though the normalizer F leaves the vast majority UNCHANGED (refine-099 DIAG: 396/396
   Q-reads at s110 are no-ops; refine-097: F changes 0-1 asms on ~90% of steps) — the
   67s normalizer of refine-098's profile was almost entirely re-applying F to Q-reads
   it had already folded to a fixpoint.
   FIX (refine-099): F's action on an assumption is a PURE function of its conclusion,
   so if F once left a conclusion unchanged it always will.  Memoize the set of concl
   terms already proven to be F-fixpoints (`gcm_simd_fixpt_tbl`): for each Q-read asm,
   if its concl is a known fixpoint skip it (GUARANTEED no-op); else apply F and, if F
   leaves it unchanged, record the fixpoint.  This is BIT-IDENTICAL to always applying
   the Q-scoped F (skipping a proven fixpoint yields exactly F's output) — it satisfies
   the soundness invariant WITHOUT any current-state approximation.  The table
   accumulates across the 4 fused bodies (CLEAR_KEEPGHALL_MEMO_TAC resets it at each
   body start so every WB_FUSED_kBLOCK `prove` is hermetic); a stale fixpoint could only
   ever be a genuine no-op anyway, so carryover would also be bit-identical.
   Measured (refine-099, quiet_drive warm, twice): WB_FUSED_4BLOCK 362.82s -> 308.00s
   (-15.1%); all 4 fused close hyps=0 (k1 131.8 k2 123.0 k3 213.0 k4 306.0).
   Scoped to the fused arc (ARM_STEPS_FOLD_KEEPGHALL_TAC's sole users are
   WB_FUSED_1..4BLOCK); the shared _CORE_TAC is UNCHANGED for the tail/front/mainloop. *)
let gcm_simd_fixpt_tbl : (term,unit) Hashtbl.t = Hashtbl.create 8192;;
let CLEAR_KEEPGHALL_MEMO_TAC : tactic =
  fun (asl,w) -> Hashtbl.clear gcm_simd_fixpt_tbl; ALL_TAC (asl,w);;
let GCM_SIMD_SIMPLIFY_CORE_QSCOPED_TAC =
  let is_qreg_read c = match c with
    | Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),cmp),_)),_) ->
        (match cmp with Const(rn,_) ->
           String.length rn >= 2 && rn.[0]='Q' && rn.[1]>='0' && rn.[1]<='9'
         | _ -> false)
    | _ -> false in
  let apply_F th =
    let th1 = (try REWRITE_RULE SIMD_SIMPLIFY_RULES th with _ -> th) in
    let th2 = REWRITE_RULE [WORD_SWAP_HALVES_INVOLUTION; EXT8_LANE0_IS_SUBWORD_HI] th1 in
    (try CONV_RULE(RAND_CONV(REV32_LANE_SUBWORD_CONV)) th2 with _ -> th2) in
  RULE_ASSUM_TAC(fun th ->
    let c = concl th in
    if not(is_qreg_read c) then th
    else if Hashtbl.mem gcm_simd_fixpt_tbl c then th
    else let th' = apply_F th in
         (if concl th' = c then Hashtbl.add gcm_simd_fixpt_tbl c ());
         th');;

(* ---- per-window symbolic-execution stepper (single-pass GCM_SIMD, refine-093;
   Q-scoped normalizer, refine-097) ----
   MAP_EVERY over the step range: verbose-step, single-pass Q-scoped GCM_SIMD
   normalizer (the 2nd CORE pass of the old double-pass is a no-op except on
   block-boundary REV64 folds, which the bridge re-does downstream via RF8_SUBWORD),
   keep-GHALL discard, clarify.  Measured -18..-38% replay per k on the rebased fused
   ckpt (refine-093); the Q-scope cuts a further ~40-55% off the normalizer (refine-097). *)
let ARM_STEPS_FOLD_KEEPGHALL_TAC exec snums =
  MAP_EVERY (fun s -> ARM_VERBOSE_STEP_TAC exec s THEN GCM_SIMD_SIMPLIFY_CORE_QSCOPED_TAC THEN
              DISCARD_OLDSTATE_KEEPGHALL_TAC s THEN CLARIFY_TAC) (statenames "s" snums);;

(* ---- ctr0 rebuild: the byte-shuffled reconstruction of the 128-bit counter ---- *)
let JOIN_IS_CTR0 = prove(
 `word_join
    (word_join
     (word_join
      (word_join (word_subword (ctr0:int128) (120,8):8 word) (word_subword ctr0 (112,8):8 word):16 word)
      (word_join (word_subword ctr0 (104,8):8 word) (word_subword ctr0 (96,8):8 word):16 word):32 word)
     (word_join
      (word_join (word_subword ctr0 (88,8):8 word) (word_subword ctr0 (80,8):8 word):16 word)
      (word_join (word_subword ctr0 (72,8):8 word) (word_subword ctr0 (64,8):8 word):16 word):32 word):64 word)
    (word_join
     (word_join
      (word_join (word_subword ctr0 (56,8):8 word) (word_subword ctr0 (48,8):8 word):16 word)
      (word_join (word_subword ctr0 (40,8):8 word) (word_subword ctr0 (32,8):8 word):16 word):32 word)
     (word_join
      (word_join (word_subword ctr0 (24,8):8 word) (word_subword ctr0 (16,8):8 word):16 word)
      (word_join (word_subword ctr0 (8,8):8 word) (word_subword ctr0 (0,8):8 word):16 word):32 word):64 word):int128
  = ctr0`,
  CONV_TAC WORD_BLAST);;

(* ---- collapse a Q-register's accumulator chain self-contained at state st ---- *)
let INLINE_SELFCONTAINED reg st npass : tactic = fun (asl,w) ->
  let lhs_t = parse_term (Printf.sprintf "read %s %s" reg st) in
  let rec nonSt tm = match tm with
      Comb(Comb(Const("read",_),_),stv) ->
        (match stv with Var(n,_) when n<>st -> [stv] | _ -> [])
    | Comb(a,b) -> union (nonSt a) (nonSt b) | Abs(_,t) -> nonSt t | _ -> [] in
  let target_rhs aslx =
    try rhs(concl(snd(List.find (fun (_,th) -> try lhs(concl th)=lhs_t with _->false) aslx)))
    with Not_found -> `T` in
  let rec go n (asl,w) =
    if n <= 0 then ALL_TAC (asl,w)
    else if nonSt (target_rhs asl) = [] then ALL_TAC (asl,w)
    else
      let picks = mapfilter (fun (_,th) ->
        match concl th with
        | Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),_),stv)),_)
            when (match stv with Var(nm,_)->nm<>st|_->false) -> th
        | _ -> fail()) asl in
      (RULE_ASSUM_TAC(fun th ->
         if (try lhs(concl th) = lhs_t with _ -> false)
         then REWRITE_RULE picks th else th) THEN go (n-1)) (asl,w) in
  go npass (asl,w);;

(* ---- polyval_dot symmetry (was redefined in k=3,4) ---- *)
let POLYVAL_DOT_SYM = prove
 (`!a b:int128. polyval_dot a b = polyval_dot b a`,
  REPEAT GEN_TAC THEN REWRITE_TAC[polyval_dot] THEN AP_TERM_TAC THEN
  REWRITE_TAC[WORD_PMUL_SYM]);;

(* ---- parameterised route-b bridge close (was BRIDGE_CLOSE_{2,3,4}_CPH*_TAC) ----
   For k>=2 the three per-k bridge tactics were structurally identical (same prelude
   + finisher, md5-confirmed) and differed ONLY in the spec-equation `spec_eq` and the
   three karatsuba-mid qq-distribution identities the machine (LHS, DISTRIBUTED) needs
   to match the spec (RHS, GMULTk byteform, COMBINED).  Two of the three are "LAND-shape"
   (subword-level, CONJUNCT1 WORD_PMUL_XOR + WORD_XOR_ACI) and one is "MID-shape"
   (nested subword(join..) operands, GSYM CONJUNCT1 + PMUL_CONG_128 + WORD_BLAST).
   The caller passes sN, the pre-built spec_eq (from its own spec_to_byteform_wbK /
   dec_bridge_specl / GMULTk_FULL_CORRECT_BA + h-assumptions), and the (lo,hi,mid) triples. *)
let bridge_qq_land (a,b,c) : tactic =
  SUBGOAL_THEN (parse_term (Printf.sprintf "(%s:int128) = word_xor %s %s" a b c))
    (fun th -> REWRITE_TAC[th]) THENL
   [MAP_EVERY EXPAND_TAC [a;b;c] THEN
    GEN_REWRITE_TAC LAND_CONV [CONJUNCT1 WORD_PMUL_XOR] THEN
    REWRITE_TAC[WORD_XOR_ACI]; ALL_TAC];;

let bridge_qq_mid (a,b,c) : tactic =
  SUBGOAL_THEN (parse_term (Printf.sprintf "(%s:int128) = word_xor %s %s" a b c))
    (fun th -> REWRITE_TAC[th]) THENL
   [MAP_EVERY EXPAND_TAC [a;b;c] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM (CONJUNCT1 WORD_PMUL_XOR)] THEN
    MATCH_MP_TAC PMUL_CONG_128 THEN CONJ_TAC THEN CONV_TAC WORD_BLAST; ALL_TAC];;

let DEC_BRIDGE_ROUTEB_TAC sN spec_eq (lo_triple,hi_triple,mid_triple) : tactic =
  fun (asl,w) ->
  let q19asm = snd(List.find(fun(_,th)->
    try lhs(concl th)=parse_term(Printf.sprintf "read Q19 s%d" sN) with _->false) asl) in
  (GEN_REWRITE_TAC LAND_CONV [q19asm] THEN
   GEN_REWRITE_TAC RAND_CONV [spec_eq] THEN
   REWRITE_TAC[WORD_XOR_0; WORD_XOR_0_LEFT] THEN
   REWRITE_TAC[byteswap128] THEN REWRITE_TAC[WORD_BYTEREVERSE_REVERSEFIELDS] THEN
   REWRITE_TAC[WORD_INSERT_SUBWORD; WORD_SUBWORD_SUBWORD] THEN
   REWRITE_TAC[SUBWORD_XOR_JOIN_DIST] THEN
   REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES; RF8_SUBWORD] THEN
   REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES] THEN
   ABBREV_INNER_PMULS_TAC THEN MERGE_2BLK_TAC THEN
   bridge_qq_land lo_triple THEN
   bridge_qq_land hi_triple THEN
   bridge_qq_mid mid_triple THEN
   REWRITE_TAC[WORD_SUBWORD_XOR] THEN
   WA_UNIFY_TAC THEN WV_UNIFY_TAC THEN ABBREV_WAWV_TAC THEN
   REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES; WORD_SUBWORD_XOR] THEN
   GEN_REWRITE_TAC ONCE_DEPTH_CONV [QQ0SPLIT] THEN
   REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES; WORD_SUBWORD_XOR] THEN
   REWRITE_TAC[JOIN_EQ_SPLIT] THEN CONJ_TAC THEN LANE_FINISH_TAC)
  (asl,w);;

(* ==== k=1 fused body (session-122-work/wb_v42.ml) ==== *)
(* SESSION 122: WB_FUSED_1BLOCK (d5 fused nblk=1 fast path), PROVEN hyps=0 END-TO-END, NO CHEAT.
   Validated via /tmp/s108work/restore_fused.sh on hol-wb-dec-fused.ckpt:
   "WB_FUSED_1BLOCK v42 RESULT: hyps=0 axioms-clean", RESTORE_EXIT=0.
   Bridge = s121 BRIDGE_CLOSE_FULL_TAC (unchanged). Store tail = split bytes128 readbacks to bytes64
   halves before ENSURES_FINAL, then per-half AP_THM_TAC;AP_TERM_TAC + closer (out=JOIN_IS_CTR0+aes+
   WORD_RULE, xi=polyval_dot-def SUBST+GHASH_1BLOCK_CORRECT, ivec=GCM_CTR_INC_LANES, MAYCHANGE=MONOTONE).
   Load prereq: needs "arm/proofs/aesv8_gcm_8x_dec_256_lemmas.ml" (~117s). *)

(* Shared fused-arc helpers (DISCARD_OLDSTATE_KEEPGHALL_TAC, ARM_STEPS_FOLD_KEEPGHALL_TAC,
   JOIN_IS_CTR0, INLINE_SELFCONTAINED, POLYVAL_DOT_SYM) — refine-094 consolidation. *)

(* ---- prelude: the folds + bridge close from bridge_close_validated.ml ---- *)
let FOLD_LO = prove(
  `word_xor (word_pmul (word_subword (word_reversefields 8 (cph:int128)) (64,64):64 word)
                       (word_subword (h:int128) (0,64):64 word))
            (word_pmul (word_reversefields 8 (word_subword (xi:int128) (0,64):64 word))
                       (word_subword h (0,64):64 word)) : int128
   = word_pmul (word_subword h (0,64):64 word)
       (word_xor (word_reversefields 8 (word_subword xi (0,64):64 word))
                 (word_reversefields 8 (word_subword cph (0,64):64 word)))`,
  REWRITE_TAC[RF8_SUBWORD] THEN
  GEN_REWRITE_TAC RAND_CONV [CONJUNCT2 WORD_PMUL_XOR] THEN
  GEN_REWRITE_TAC (RAND_CONV o RATOR_CONV o RAND_CONV) [WORD_PMUL_SYM] THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [WORD_PMUL_SYM] THEN
  REWRITE_TAC[WORD_XOR_ACI]);;
let FOLD_HI = prove(
  `word_xor (word_pmul (word_subword (word_reversefields 8 (cph:int128)) (0,64):64 word)
                       (word_subword (h:int128) (64,64):64 word))
            (word_pmul (word_reversefields 8 (word_subword (xi:int128) (64,64):64 word))
                       (word_subword h (64,64):64 word)) : int128
   = word_pmul (word_subword h (64,64):64 word)
       (word_xor (word_reversefields 8 (word_subword xi (64,64):64 word))
                 (word_reversefields 8 (word_subword cph (64,64):64 word)))`,
  REWRITE_TAC[RF8_SUBWORD] THEN
  GEN_REWRITE_TAC RAND_CONV [CONJUNCT2 WORD_PMUL_XOR] THEN
  GEN_REWRITE_TAC (RAND_CONV o RATOR_CONV o RAND_CONV) [WORD_PMUL_SYM] THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [WORD_PMUL_SYM] THEN
  REWRITE_TAC[WORD_XOR_ACI]);;
let FOLD_LO_N = prove(
  `word_xor (word_pmul (word_reversefields 8 (word_subword (cph:int128) (0,64):64 word))
                       (word_subword (h:int128) (0,64):64 word))
            (word_pmul (word_reversefields 8 (word_subword (xi:int128) (0,64):64 word))
                       (word_subword h (0,64):64 word)) : int128
   = word_pmul (word_subword h (0,64):64 word)
       (word_xor (word_reversefields 8 (word_subword xi (0,64):64 word))
                 (word_reversefields 8 (word_subword cph (0,64):64 word)))`,
  GEN_REWRITE_TAC RAND_CONV [CONJUNCT2 WORD_PMUL_XOR] THEN
  GEN_REWRITE_TAC (RAND_CONV o RATOR_CONV o RAND_CONV) [WORD_PMUL_SYM] THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [WORD_PMUL_SYM] THEN
  REWRITE_TAC[WORD_XOR_ACI]);;
let FOLD_HI_N = prove(
  `word_xor (word_pmul (word_reversefields 8 (word_subword (cph:int128) (64,64):64 word))
                       (word_subword (h:int128) (64,64):64 word))
            (word_pmul (word_reversefields 8 (word_subword (xi:int128) (64,64):64 word))
                       (word_subword h (64,64):64 word)) : int128
   = word_pmul (word_subword h (64,64):64 word)
       (word_xor (word_reversefields 8 (word_subword xi (64,64):64 word))
                 (word_reversefields 8 (word_subword cph (64,64):64 word)))`,
  GEN_REWRITE_TAC RAND_CONV [CONJUNCT2 WORD_PMUL_XOR] THEN
  GEN_REWRITE_TAC (RAND_CONV o RATOR_CONV o RAND_CONV) [WORD_PMUL_SYM] THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [WORD_PMUL_SYM] THEN
  REWRITE_TAC[WORD_XOR_ACI]);;
let FOLD_MID = prove(
  `word_xor
    (word_pmul
      (word_subword
        (word_xor
          (word_subword (word_join (word_reversefields 8 (cph:int128)) (word_reversefields 8 cph):256 word) (64,128):128 word)
          (word_reversefields 8 cph)) (0,64):64 word)
      (word_xor (word_subword (h:int128) (0,64):64 word) (word_subword h (64,64):64 word)))
    (word_pmul
      (word_subword
        (word_xor
          (word_subword
            (word_join
              (word_join (word_reversefields 8 (word_subword (xi:int128) (0,64):64 word))
                         (word_reversefields 8 (word_subword xi (64,64):64 word)):128 word)
              (word_join (word_reversefields 8 (word_subword xi (0,64):64 word))
                         (word_reversefields 8 (word_subword xi (64,64):64 word)):128 word):256 word)
            (64,128):128 word)
          (word_join (word_reversefields 8 (word_subword xi (0,64):64 word))
                     (word_reversefields 8 (word_subword xi (64,64):64 word)):128 word)) (0,64):64 word)
      (word_xor (word_subword h (0,64):64 word) (word_subword h (64,64):64 word))) : int128
   = word_pmul (word_xor (word_subword h (64,64):64 word) (word_subword h (0,64):64 word))
       (word_xor
         (word_xor (word_reversefields 8 (word_subword xi (64,64):64 word))
                   (word_reversefields 8 (word_subword cph (64,64):64 word)))
         (word_xor (word_reversefields 8 (word_subword xi (0,64):64 word))
                   (word_reversefields 8 (word_subword cph (0,64):64 word))))`,
  REWRITE_TAC[JOINMID; JOIN_SUBWORD_RULES; WORD_SUBWORD_SUBWORD; RF8_SUBWORD] THEN
  REWRITE_TAC[SUBWORD_XOR_JOIN_DIST; JOIN_SUBWORD_RULES; WORD_SUBWORD_SUBWORD; RF8_SUBWORD] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM (CONJUNCT1 WORD_PMUL_XOR)] THEN
  GEN_REWRITE_TAC LAND_CONV [WORD_PMUL_SYM] THEN
  MATCH_MP_TAC PMUL_CONG_128 THEN CONJ_TAC THEN CONV_TAC WORD_BLAST);;
let FOLD_MID2 = prove(
  `word_xor
     (word_pmul
       (word_xor
         (word_subword
           (word_subword
             (word_join (word_reversefields 8 (cph:int128)) (word_reversefields 8 cph):256 word) (64,128):128 word)
            (0,64):64 word)
         (word_reversefields 8 (word_subword cph (64,64):64 word)))
       (word_xor (word_subword (h:int128) (0,64):64 word) (word_subword h (64,64):64 word)))
     (word_pmul
       (word_xor
         (word_subword
           (word_subword
             (word_join
               (word_join (word_reversefields 8 (word_subword (xi:int128) (0,64):64 word))
                          (word_reversefields 8 (word_subword xi (64,64):64 word)):128 word)
               (word_join (word_reversefields 8 (word_subword xi (0,64):64 word))
                          (word_reversefields 8 (word_subword xi (64,64):64 word)):128 word):256 word)
             (64,128):128 word)
            (0,64):64 word)
         (word_reversefields 8 (word_subword xi (64,64):64 word)))
       (word_xor (word_subword h (0,64):64 word) (word_subword h (64,64):64 word))) : int128
   = word_pmul (word_xor (word_subword h (64,64):64 word) (word_subword h (0,64):64 word))
       (word_xor
         (word_xor (word_reversefields 8 (word_subword xi (64,64):64 word))
                   (word_reversefields 8 (word_subword cph (64,64):64 word)))
         (word_xor (word_reversefields 8 (word_subword xi (0,64):64 word))
                   (word_reversefields 8 (word_subword cph (0,64):64 word))))`,
  REWRITE_TAC[JOINMID; JOIN_SUBWORD_RULES; WORD_SUBWORD_SUBWORD; RF8_SUBWORD] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM (CONJUNCT1 WORD_PMUL_XOR)] THEN
  GEN_REWRITE_TAC LAND_CONV [WORD_PMUL_SYM] THEN
  MATCH_MP_TAC PMUL_CONG_128 THEN CONJ_TAC THEN CONV_TAC WORD_BLAST);;

(* SPEED (refine-095): lane-split close for the k=1 fused bridge, replacing the
   monolithic 128-bit `FINISH_WV_TAC` (which ran CONV_TAC WORD_BLAST over a 128-bit
   word_pmul goal = 105.9s measured).  Same shape the k>=2 bridges already close via
   DEC_BRIDGE_ROUTEB_TAC's LANE_FINISH_TAC / JOIN_EQ_SPLIT: unify the two `word_pmul`
   towers (PMUL_CONG_128 on their 128-bit operands), then split the residual 128-bit
   word_join equality into two 64-bit lanes (QQ0SPLIT + JOIN_EQ_SPLIT) and blast each
   lane at 64-bit width.  Measured 105.9s -> 45.9s (twice, warm) on the k=1 entry goal;
   proof-preserving (closes hyps=0). *)
let FINISH_WV_LANE_TAC : tactic = fun (asl,w) ->
  let is_pmul_app t =
    try let (h,a) = strip_comb t in fst(dest_const h) = "word_pmul" && length a = 2
    with _ -> false in
  ((match setify(find_terms is_pmul_app w) with
    | [p0;p1] ->
       SUBGOAL_THEN (mk_eq(p0,p1)) (fun th -> REWRITE_TAC[th]) THENL
        [MATCH_MP_TAC PMUL_CONG_128 THEN CONJ_TAC THEN CONV_TAC WORD_BLAST; ALL_TAC]
    | _ -> ALL_TAC) THEN
   GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [QQ0SPLIT] THEN
   GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [QQ0SPLIT] THEN
   REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES; WORD_SUBWORD_XOR] THEN
   REWRITE_TAC[JOIN_EQ_SPLIT] THEN CONJ_TAC THEN CONV_TAC WORD_BLAST) (asl,w);;

let BRIDGE_CLOSE_FULL_TAC =
  GEN_REWRITE_TAC RAND_CONV
    [GSYM(REWRITE_RULE[LET_DEF; LET_END_DEF]
       (ISPECL [`word_xor (word_bytereverse xi) (word_bytereverse cph) : int128`;
         `byteswap128 h:int128`] GMULT_FULL_CORRECT_BA))] THEN
  REWRITE_TAC[byteswap128] THEN
  REWRITE_TAC[WORD_BYTEREVERSE_REVERSEFIELDS] THEN
  REWRITE_TAC[WORD_INSERT_SUBWORD; WORD_SUBWORD_SUBWORD] THEN
  REWRITE_TAC[SUBWORD_XOR_JOIN_DIST] THEN
  REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES; RF8_SUBWORD] THEN
  REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES] THEN
  REWRITE_TAC[GSYM (CONJUNCT1 SUBWORD_XOR_JOIN_DIST); GSYM (CONJUNCT2 SUBWORD_XOR_JOIN_DIST)] THEN
  REWRITE_TAC[FOLD_LO; FOLD_HI; FOLD_MID; FOLD_LO_N; FOLD_HI_N] THEN
  ABBREV_INNER_PMULS_TAC THEN
  SUBGOAL_THEN `word_xor (qq4:int128) qq3 = qq2` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["qq2";"qq3";"qq4"] THEN ACCEPT_TAC FOLD_MID2; ALL_TAC] THEN
  FIRST_X_ASSUM(fun th -> if concl th = `word_xor (qq4:int128) qq3 = qq2` then REWRITE_TAC[th] else NO_TAC) THEN
  ABBREV_INNER_PMULS_TAC THEN
  FINISH_WV_LANE_TAC;;

(* DISCARD_OLDSTATE_KEEPGHALL_TAC, ARM_STEPS_FOLD_KEEPGHALL_TAC, JOIN_IS_CTR0
   now come from fused-wip/fused_common.ml (needs above). *)

let WB_FUSED_1BLOCK = prove(
 `!pc stackpointer out_p xi_p ivec_p in_p key_p htbl_p
    cph xi ctr0 k0 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 k11 k12 k13 k14 h hk.
    aligned 16 stackpointer /\
    nonoverlapping (word pc, 5960) (stackpointer:int64, 80) /\
    nonoverlapping (word pc, 5960) (out_p:int64, 16) /\
    nonoverlapping (word pc, 5960) (xi_p:int64, 16) /\
    nonoverlapping (word pc, 5960) (ivec_p:int64, 16) /\
    nonoverlapping (out_p, 16) (xi_p, 16) /\
    nonoverlapping (out_p, 16) (ivec_p, 16) /\
    nonoverlapping (xi_p, 16) (ivec_p, 16) /\
    nonoverlapping (ivec_p, 16) (in_p:int64, 16) /\
    nonoverlapping (ivec_p, 16) (key_p:int64, 240) /\
    nonoverlapping (ivec_p, 16) (htbl_p:int64, 192) /\
    nonoverlapping (in_p, 16) (stackpointer, 80) /\
    nonoverlapping (key_p, 240) (stackpointer, 80) /\
    nonoverlapping (htbl_p, 192) (stackpointer, 80) /\
    nonoverlapping (ivec_p, 16) (stackpointer, 80) /\
    nonoverlapping (xi_p, 16) (in_p, 16) /\
    nonoverlapping (xi_p, 16) (key_p, 240) /\
    nonoverlapping (xi_p, 16) (htbl_p, 192) /\
    nonoverlapping (xi_p, 16) (stackpointer, 80) /\
    nonoverlapping (out_p, 16) (in_p, 16) /\
    nonoverlapping (out_p, 16) (key_p, 240) /\
    nonoverlapping (out_p, 16) (htbl_p, 192) /\
    nonoverlapping (out_p, 16) (stackpointer, 80) /\
    word_subword hk (0,64) :64 word =
      word_xor (word_subword h (0,64):64 word) (word_subword h (64,64):64 word)
    ==> ensures arm
     (\s. aligned_bytes_loaded s (word pc) aesv8_gcm_8x_dec_256_wb_mc /\
          read PC s = word (pc + 0x20) /\ read SP s = stackpointer /\
          C_ARGUMENTS [in_p; word 128; out_p; xi_p; ivec_p; key_p; htbl_p] s /\
          read (memory :> bytes128 in_p) s = cph /\
          read (memory :> bytes128 xi_p) s = xi /\
          read (memory :> bytes128 ivec_p) s = ctr0 /\
          read (memory :> bytes128 key_p) s = k0 /\
          read (memory :> bytes128 (word_add key_p (word 16))) s = k1 /\
          read (memory :> bytes128 (word_add key_p (word 32))) s = k2 /\
          read (memory :> bytes128 (word_add key_p (word 48))) s = k3 /\
          read (memory :> bytes128 (word_add key_p (word 64))) s = k4 /\
          read (memory :> bytes128 (word_add key_p (word 80))) s = k5 /\
          read (memory :> bytes128 (word_add key_p (word 96))) s = k6 /\
          read (memory :> bytes128 (word_add key_p (word 112))) s = k7 /\
          read (memory :> bytes128 (word_add key_p (word 128))) s = k8 /\
          read (memory :> bytes128 (word_add key_p (word 144))) s = k9 /\
          read (memory :> bytes128 (word_add key_p (word 160))) s = k10 /\
          read (memory :> bytes128 (word_add key_p (word 176))) s = k11 /\
          read (memory :> bytes128 (word_add key_p (word 192))) s = k12 /\
          read (memory :> bytes128 (word_add key_p (word 208))) s = k13 /\
          read (memory :> bytes128 (word_add key_p (word 224))) s = k14 /\
          read (memory :> bytes128 htbl_p) s = h /\
          read (memory :> bytes128 (word_add htbl_p (word 16))) s = hk)
     (\s. read PC s = word (pc + 0x11d0) /\
          read (memory :> bytes128 out_p) s =
          word_xor cph (aes256_encrypt ctr0
            [(k0:int128);k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14]) /\
          read (memory :> bytes128 xi_p) s =
          word_bytereverse
            (ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
              [word_bytereverse cph]) /\
          read (memory :> bytes128 ivec_p) s = gcm_ctr_inc_iter 1 ctr0)
     (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
      MAYCHANGE [memory :> bytes(out_p, 16); memory :> bytes(xi_p, 16);
                 memory :> bytes(ivec_p, 16);
                 memory :> bytes(word_add stackpointer (word 64):int64, 16)] ,,
      MAYCHANGE [Q0;Q1;Q2;Q3;Q4;Q5;Q6;Q7;Q8;Q9;Q10;Q11;Q12;Q13;Q14;Q15;
                 Q16;Q17;Q18;Q19;Q20;Q21;Q22;Q23;Q24;Q25;Q26;Q27;Q28;Q29;Q30;Q31])`,
  REPEAT GEN_TAC THEN REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS] THEN STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  CLEAR_KEEPGHALL_MEMO_TAC THEN  (* refine-099: reset the fused normalizer fixpoint cache *)
  FIRST_ASSUM(fun th ->
    if (try lhs(concl th) = `read (memory :> bytes128 (word_add htbl_p (word 16))) s0`
        with _ -> false)
    then (MP_TAC th THEN PURE_ONCE_REWRITE_TAC[el 1 (CONJUNCTS READ_MEMORY_BYTESIZED_UNSPLIT)] THEN
          STRIP_TAC)
    else NO_TAC) THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (1--33) THEN
  ARM_STEPS_FOLD_KEEPGHALL_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (34--84) THEN
  (fun (asl,w) ->
     let picks = mapfilter (fun (_,th) ->
       match concl th with
       | Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),_),st)),_)
           when (match st with Var(n,_)->n<>"s84"|_->false) -> th
       | _ -> fail()) asl in
     RULE_ASSUM_TAC(fun th ->
       if (try lhs(concl th) = `read Q19 s84` with _ -> false)
       then REWRITE_RULE picks th else th) (asl,w)) THEN
  DISCARD_OLDSTATE_TAC "s84" THEN
  SUBGOAL_THEN
    `read Q19 (s84:armstate) =
     polyval_dot (word_xor (word_bytereverse xi) (word_bytereverse cph))
       (byteswap128 h)`
    (fun th -> RULE_ASSUM_TAC(fun asm ->
       if can (find_term (fun t -> t = `read Q19 s84`)) (concl asm)
       then th else asm) THEN ASSUME_TAC th) THENL
  [FIRST_ASSUM(fun th ->
     if is_eq(concl th) && (try lhs(concl th) = `read Q19 s84` with _ -> false)
     then GEN_REWRITE_TAC LAND_CONV [th] else NO_TAC) THEN
   BRIDGE_CLOSE_FULL_TAC;
   ALL_TAC] THEN
  ABBREV_TAC `gval:int128 = polyval_dot (word_xor (word_bytereverse xi)
    (word_bytereverse cph)) (byteswap128 h)` THEN
  ARM_STEPS_FOLD_DISCARD_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (85--88) THEN
  SUBGOAL_THEN `read Q19 (s88:armstate) = word_bytereverse (gval:int128)`
    (fun th -> RULE_ASSUM_TAC(fun asm ->
       if can (find_term (fun t -> t = `read Q19 s88`)) (concl asm)
       then th else asm) THEN ASSUME_TAC th) THENL
  [FIRST_ASSUM(fun th ->
     if is_eq(concl th) && (try lhs(concl th) = `read Q19 s88` with _ -> false)
     then GEN_REWRITE_TAC LAND_CONV [th] else NO_TAC) THEN CONV_TAC WORD_BLAST;
   ALL_TAC] THEN
  ARM_STEPS_FOLD_DISCARD_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (89--97) THEN
  (* Split the 3 bytes128 machine store readbacks (out/xi/ivec) at s97 into bytes64 halves so
     ENSURES_FINAL's bytes64 half-goals get a matching `read bytes64 X s97 = word_subword MACHINE k`
     assumption. gval is LIVE and stays live through ENSURES_FINAL (v37-confirmed). *)
  RULE_ASSUM_TAC(fun th ->
    match concl th with
    | Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),
        Comb(Comb(Const(":>",_),Const("memory",_)),
             Comb(Const("bytes128",_),_))),st)),_)
        when (try fst(dest_var st)="s97" with _ -> false) ->
        (try CONV_RULE(READ_MEMORY_SPLIT_CONV 1) th with _ -> th)
    | _ -> th) THEN
  REPEAT(FIRST_X_ASSUM(fun th ->
    if is_conj(concl th) then STRIP_ASSUME_TAC th else NO_TAC)) THEN
  ENSURES_FINAL_STATE_TAC THEN
  (* Fold gval back to its polyval_dot definition in the GOAL's RHS via GSYM GHASH_1BLOCK_CORRECT so
     both sides speak polyval_dot; then ASM_REWRITE (which knows gval=def) + the machine closers. *)
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
  (* xi half: word_subword (word_bytereverse gval) k = word_subword (word_bytereverse (ghash..)) k *)
  TRY(AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o
        check (fun th -> try rhs(concl th) = `gval:int128` &&
                             (match lhs(concl th) with
                              | Comb(Comb(Const("polyval_dot",_),_),_) -> true | _ -> false)
                         with _ -> false)) THEN
      REWRITE_TAC[GHASH_1BLOCK_CORRECT] THEN NO_TAC) THEN
  (* ivec half *)
  TRY(AP_THM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[num_CONV `1`; gcm_ctr_inc_iter; GCM_CTR_INC_LANES] THEN NO_TAC) THEN
  (* out half *)
  TRY(AP_THM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[JOIN_IS_CTR0] THEN
      REWRITE_TAC[aes256_encrypt] THEN REWRITE_TAC EL_15_128_CLAUSES THEN
      REWRITE_TAC[aes256_encrypt_round; aese; aesmc] THEN
      CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
      REWRITE_TAC[aese; aesmc] THEN CONV_TAC WORD_RULE THEN NO_TAC) THEN
  (* MAYCHANGE frame *)
  TRY(REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
      REPEAT CONJ_TAC THEN MONOTONE_MAYCHANGE_TAC THEN NO_TAC));;

(* ==== k=2 fused body (session-126-work/wb2_v3_qq8fold.ml) ==== *)
(* SESSION 125: WB_FUSED_2BLOCK (k=2) ROUTE-B v2 — SIM SOLVED, bridge is the one remaining gap.
   =============================================================================================
   WHAT'S NEW vs s124 wb2_routeb.ml (both machine-confirmed this session, RESTORE_EXIT=0):
     FIX (1): address normalization after the hk UNSPLIT so the block-0 x H^2 folded-key load
              `ldr d25,[x6,#24]` (spelled word_add htbl_p (word 24)) resolves against the UNSPLIT
              high-half fact (spelled word_add (word_add htbl_p (word 16)) (word 8)). Without it,
              Q18 s81 dangles on read(bytes64 htbl_p+24)@s31/s44 and DISCARD drops the accumulator.
              (k=1 never needs +24; k>=2 block0 x H^2 does — see memory wb-dec-fused-2block-addr-fix-s125.)
     FIX (2): INLINE_SELFCONTAINED Q17/Q18/Q19 at s81 (iterated REWRITE_RULE picks) BEFORE
              DISCARD_OLDSTATE "s81" — collapses the block-0 accumulator chain so DISCARD keeps it.
   RESULT: read Q19 s128 SELF-CONTAINED (rhs_len 9086, refs=0). SIM done end-to-end.

   THE ONE REMAINING GAP — the bridge. BRIDGE_CLOSE_2_CPH1_TAC below is the PROVEN
   DEC_BRIDGE_CLOSE_TAC body at nblk=2 (NO FOLD_MID_HPOW: for nblk=2, top_fold=1, rev(2--1)=[] —
   that was the s123 hd bug), CPH1 (unmasked) specl, spec_to_byteform_2, LANE_FINISH_TAC finisher
   (fast — NOT the blast-heavy dec2_gmult2_bridge_tac, which ran >16min CPU without converging).
   It reaches LANE_FINISH_TAC but the final REFL_TAC fails on a residual lane XOR-grouping mismatch:
      word_xor (word_subword qq8 (0,64)) (word_subword qq3 (0,64)) =
      word_xor (word_subword qq3 (0,64)) (word_xor (word_subword qq1 (0,64)) (word_subword qq5 (0,64)))
   i.e. one machine pmul (qq8) = XOR of two spec pmuls (qq1,qq5) that MERGE_2BLK didn't combine.
   FIX (mirror v42's FOLD_MID2 step): insert an explicit `SUBGOAL_THEN <qq8 = word_xor qq1 qq5>`
   (proven EXPAND_TAC the 3 qq + PMUL_CONG_128/WORD_BLAST) then rewrite + re-ABBREV before
   LANE_FINISH_TAC. The exact qq identity is in orchestrator/logs/session-125-work/lanes probe
   output (QQDEF lines). See session-125-summary.md.
   ============================================================================================= *)

(* Shared fused-arc helpers (DISCARD_OLDSTATE_KEEPGHALL_TAC, ARM_STEPS_FOLD_KEEPGHALL_TAC,
   JOIN_IS_CTR0, INLINE_SELFCONTAINED, POLYVAL_DOT_SYM) — refine-094 consolidation. *)

(* PACK2_ID, GMULT2_FULL_CORRECT_BA reused from aesv8_gcm_8x_dec_256_lemmas.ml (chain) *)
let spec_to_byteform_2 = prove
 (`byteswap128 h2 = polyval_dot (byteswap128 h) (byteswap128 h)
   ==> ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
        [word_bytereverse cph0; word_bytereverse cph1] =
       polyval_reduce_prop3
        (word_xor
          (word_pmul (word_xor (word_bytereverse xi) (word_bytereverse cph0)) (byteswap128 h2))
          (word_pmul (word_bytereverse cph1) (byteswap128 h)))`,
  STRIP_TAC THEN
  REWRITE_TAC[REWRITE_RULE[LET_DEF;LET_END_DEF]
    (SPECL [`byteswap128 h:int128`; `word_bytereverse xi:int128`;
            `word_bytereverse cph0:int128`; `word_bytereverse cph1:int128`] GHASH_POLYVAL_ACC_2)] THEN
  ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE);;

let dec_bridge_specl_2_cph1 =
  [`word_xor (word_bytereverse xi) (word_bytereverse cph0):int128`; `byteswap128 h2:int128`;
   `word_bytereverse cph1:int128`; `byteswap128 h:int128`];;

(* BRIDGE_CLOSE_2_CPH1_TAC: nblk=2 (no FOLD_MID_HPOW), cph1 specl.  Thin wrapper over the
   shared DEC_BRIDGE_ROUTEB_TAC (fused_common.ml); builds spec_eq from the k=2-local
   spec_to_byteform_2 / dec_bridge_specl_2_cph1 / GMULT2_FULL_CORRECT_BA, and passes the k=2
   block-0 (H^2) karatsuba-mid distributions: qq8=qq1(+)qq5 (hi), qq7=qq0(+)qq4 (lo),
   qq12=qq9(+)qq10 (mid). *)
let BRIDGE_CLOSE_2_CPH1_TAC sN : tactic = fun (asl,w) ->
  let h2asm = snd(List.find(fun(_,th)->try lhs(concl th)=`byteswap128 h2` with _->false) asl) in
  let gmult_dec = REWRITE_RULE[LET_DEF;LET_END_DEF] (SPECL dec_bridge_specl_2_cph1 GMULT2_FULL_CORRECT_BA) in
  let spec_eq = TRANS (MP spec_to_byteform_2 h2asm) (GSYM gmult_dec) in
  DEC_BRIDGE_ROUTEB_TAC sN spec_eq
    (("qq8","qq1","qq5"),("qq7","qq0","qq4"),("qq12","qq9","qq10")) (asl,w);;

(* DISCARD_OLDSTATE_KEEPGHALL_TAC, ARM_STEPS_FOLD_KEEPGHALL_TAC, JOIN_IS_CTR0,
   INLINE_SELFCONTAINED now come from fused-wip/fused_common.ml (needs above). *)

let WB_FUSED_2BLOCK = prove(
 `!pc stackpointer out_p xi_p ivec_p in_p key_p htbl_p
    cph0 cph1 xi ctr0 k0 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 k11 k12 k13 k14 h hk h2.
    aligned 16 stackpointer /\
    nonoverlapping (word pc, 5960) (stackpointer:int64, 80) /\
    nonoverlapping (word pc, 5960) (out_p:int64, 32) /\
    nonoverlapping (word pc, 5960) (xi_p:int64, 16) /\
    nonoverlapping (word pc, 5960) (ivec_p:int64, 16) /\
    nonoverlapping (out_p, 32) (xi_p, 16) /\
    nonoverlapping (out_p, 32) (ivec_p, 16) /\
    nonoverlapping (xi_p, 16) (ivec_p, 16) /\
    nonoverlapping (ivec_p, 16) (in_p:int64, 32) /\
    nonoverlapping (ivec_p, 16) (key_p:int64, 240) /\
    nonoverlapping (ivec_p, 16) (htbl_p:int64, 192) /\
    nonoverlapping (in_p, 32) (stackpointer, 80) /\
    nonoverlapping (key_p, 240) (stackpointer, 80) /\
    nonoverlapping (htbl_p, 192) (stackpointer, 80) /\
    nonoverlapping (ivec_p, 16) (stackpointer, 80) /\
    nonoverlapping (xi_p, 16) (in_p, 32) /\
    nonoverlapping (xi_p, 16) (key_p, 240) /\
    nonoverlapping (xi_p, 16) (htbl_p, 192) /\
    nonoverlapping (xi_p, 16) (stackpointer, 80) /\
    nonoverlapping (out_p, 32) (in_p, 32) /\
    nonoverlapping (out_p, 32) (key_p, 240) /\
    nonoverlapping (out_p, 32) (htbl_p, 192) /\
    nonoverlapping (out_p, 32) (stackpointer, 80) /\
    word_subword hk (0,64) :64 word =
      word_xor (word_subword h (0,64):64 word) (word_subword h (64,64):64 word) /\
    word_subword hk (64,64) :64 word =
      word_xor (word_subword h2 (0,64):64 word) (word_subword h2 (64,64):64 word) /\
    byteswap128 h2 = polyval_dot (byteswap128 h) (byteswap128 h)
    ==> ensures arm
     (\s. aligned_bytes_loaded s (word pc) aesv8_gcm_8x_dec_256_wb_mc /\
          read PC s = word (pc + 0x20) /\ read SP s = stackpointer /\
          C_ARGUMENTS [in_p; word 256; out_p; xi_p; ivec_p; key_p; htbl_p] s /\
          read (memory :> bytes128 in_p) s = cph0 /\
          read (memory :> bytes128 (word_add in_p (word 16))) s = cph1 /\
          read (memory :> bytes128 xi_p) s = xi /\
          read (memory :> bytes128 ivec_p) s = ctr0 /\
          read (memory :> bytes128 key_p) s = k0 /\
          read (memory :> bytes128 (word_add key_p (word 16))) s = k1 /\
          read (memory :> bytes128 (word_add key_p (word 32))) s = k2 /\
          read (memory :> bytes128 (word_add key_p (word 48))) s = k3 /\
          read (memory :> bytes128 (word_add key_p (word 64))) s = k4 /\
          read (memory :> bytes128 (word_add key_p (word 80))) s = k5 /\
          read (memory :> bytes128 (word_add key_p (word 96))) s = k6 /\
          read (memory :> bytes128 (word_add key_p (word 112))) s = k7 /\
          read (memory :> bytes128 (word_add key_p (word 128))) s = k8 /\
          read (memory :> bytes128 (word_add key_p (word 144))) s = k9 /\
          read (memory :> bytes128 (word_add key_p (word 160))) s = k10 /\
          read (memory :> bytes128 (word_add key_p (word 176))) s = k11 /\
          read (memory :> bytes128 (word_add key_p (word 192))) s = k12 /\
          read (memory :> bytes128 (word_add key_p (word 208))) s = k13 /\
          read (memory :> bytes128 (word_add key_p (word 224))) s = k14 /\
          read (memory :> bytes128 htbl_p) s = h /\
          read (memory :> bytes128 (word_add htbl_p (word 16))) s = hk /\
          read (memory :> bytes128 (word_add htbl_p (word 32))) s = h2)
     (\s. read PC s = word (pc + 0x11d0) /\
          read (memory :> bytes128 out_p) s =
          word_xor cph0 (aes256_encrypt ctr0
            [(k0:int128);k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14]) /\
          read (memory :> bytes128 (word_add out_p (word 16))) s =
          word_xor cph1 (aes256_encrypt (gcm_ctr_inc ctr0)
            [(k0:int128);k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14]) /\
          read (memory :> bytes128 xi_p) s =
          word_bytereverse
            (ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
              [word_bytereverse cph0; word_bytereverse cph1]) /\
          read (memory :> bytes128 ivec_p) s = gcm_ctr_inc_iter 2 ctr0)
     (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
      MAYCHANGE [memory :> bytes(out_p, 32); memory :> bytes(xi_p, 16);
                 memory :> bytes(ivec_p, 16);
                 memory :> bytes(word_add stackpointer (word 64):int64, 16)] ,,
      MAYCHANGE [Q0;Q1;Q2;Q3;Q4;Q5;Q6;Q7;Q8;Q9;Q10;Q11;Q12;Q13;Q14;Q15;
                 Q16;Q17;Q18;Q19;Q20;Q21;Q22;Q23;Q24;Q25;Q26;Q27;Q28;Q29;Q30;Q31])`,
  REPEAT GEN_TAC THEN REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS] THEN STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  CLEAR_KEEPGHALL_MEMO_TAC THEN  (* refine-099: reset the fused normalizer fixpoint cache *)
  FIRST_ASSUM(fun th ->
    if (try lhs(concl th) = `read (memory :> bytes128 (word_add htbl_p (word 16))) s0`
        with _ -> false)
    then (MP_TAC th THEN PURE_ONCE_REWRITE_TAC[el 1 (CONJUNCTS READ_MEMORY_BYTESIZED_UNSPLIT)] THEN
          STRIP_TAC)
    else NO_TAC) THEN
  (* FIX (1): normalize hk-high address so ldr d25,[x6,#24] resolves *)
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
    `word_add (word_add (htbl_p:int64) (word 16)) (word 8) = word_add htbl_p (word 24)`]) THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (1--30) THEN
  ARM_STEPS_FOLD_KEEPGHALL_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (31--81) THEN
  SUBGOAL_THEN
    `read (memory :> bytes128 out_p) (s81:armstate) =
     word_xor cph0 (aes256_encrypt ctr0
       [(k0:int128);k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14])`
    ASSUME_TAC THENL
  [ASM_REWRITE_TAC[] THEN REWRITE_TAC[JOIN_IS_CTR0] THEN
   REWRITE_TAC[aes256_encrypt] THEN REWRITE_TAC EL_15_128_CLAUSES THEN
   REWRITE_TAC[aes256_encrypt_round; aese; aesmc] THEN
   CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   REWRITE_TAC[aese; aesmc] THEN CONV_TAC WORD_RULE;
   ALL_TAC] THEN
  (* FIX (2): collapse the block-0 accumulator chain self-contained at s81 *)
  INLINE_SELFCONTAINED "Q17" "s81" 24 THEN
  INLINE_SELFCONTAINED "Q18" "s81" 24 THEN
  INLINE_SELFCONTAINED "Q19" "s81" 24 THEN
  DISCARD_OLDSTATE_TAC "s81" THEN
  ARM_STEPS_FOLD_KEEPGHALL_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (82--128) THEN
  INLINE_SELFCONTAINED "Q19" "s128" 8 THEN
  DISCARD_OLDSTATE_TAC "s128" THEN
  SUBGOAL_THEN
    `read Q19 (s128:armstate) =
     ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
       [word_bytereverse cph0; word_bytereverse cph1]`
    (fun th -> RULE_ASSUM_TAC(fun asm ->
       if (try lhs(concl asm) = `read Q19 s128` with _ -> false)
       then th else asm) THEN ASSUME_TAC th) THENL
  [BRIDGE_CLOSE_2_CPH1_TAC 128;   (* <<< bridge: needs the residual-merge fix (see header) >>> *)
   ALL_TAC] THEN
  ABBREV_TAC `gval:int128 = ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
       [word_bytereverse cph0; word_bytereverse cph1]` THEN
  ARM_STEPS_FOLD_DISCARD_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (129--132) THEN
  SUBGOAL_THEN `read Q19 (s132:armstate) = word_bytereverse (gval:int128)`
    (fun th -> RULE_ASSUM_TAC(fun asm ->
       if (try lhs(concl asm) = `read Q19 s132` with _ -> false)
       then th else asm) THEN ASSUME_TAC th) THENL
  [FIRST_ASSUM(fun th ->
     if is_eq(concl th) && (try lhs(concl th) = `read Q19 s132` with _ -> false)
     then GEN_REWRITE_TAC LAND_CONV [th] else NO_TAC) THEN CONV_TAC WORD_BLAST;
   ALL_TAC] THEN
  ARM_STEPS_FOLD_DISCARD_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (133--141) THEN
  RULE_ASSUM_TAC(fun th ->
    match concl th with
    | Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),
        Comb(Comb(Const(":>",_),Const("memory",_)),
             Comb(Const("bytes128",_),_))),st)),_)
        when (try fst(dest_var st)="s141" with _ -> false) ->
        (try CONV_RULE(READ_MEMORY_SPLIT_CONV 1) th with _ -> th)
    | _ -> th) THEN
  REPEAT(FIRST_X_ASSUM(fun th ->
    if is_conj(concl th) then STRIP_ASSUME_TAC th else NO_TAC)) THEN
  (* Normalize the block-1 store hi-half address so the split readback assumption
     `read (bytes64 ((out_p+16)+8)) s141 = ...` matches the ENSURES_FINAL goal half:
     (out_p+16)+8 = out_p+24 (same htbl-address-spelling class as the s125 hk+24 fix). *)
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
    `word_add (word_add (out_p:int64) (word 16)) (word 8) = word_add out_p (word 24)`]) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[WORD_RULE
    `word_add (word_add (out_p:int64) (word 16)) (word 8) = word_add out_p (word 24)`] THEN
  REPEAT CONJ_TAC THEN
  (* xi half: word_subword(word_bytereverse gval) k = word_subword(word_bytereverse(ghash..)) k *)
  TRY(AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o
        check (fun th -> try rhs(concl th) = `gval:int128` &&
                             (match lhs(concl th) with
                              | Comb(Comb(Const("ghash_polyval_acc",_),_),_) -> true | _ -> false)
                         with _ -> false)) THEN
      REFL_TAC THEN NO_TAC) THEN
  (* ivec half: word_subword MACHINE k = word_subword (gcm_ctr_inc_iter 2 ctr0) k.  Unfold iter 2
     -> gcm_ctr_inc(gcm_ctr_inc ctr0) -> the +2 byte-tower (GCM_CTR_INC2_LANES), then both sides are
     the SAME tower (machine top lane = word_add (join ctr0[96..127]) (word 2)); close by WORD_BLAST. *)
  TRY(AP_THM_TAC THEN AP_TERM_TAC THEN
      SUBGOAL_THEN `gcm_ctr_inc_iter 2 ctr0 = gcm_ctr_inc (gcm_ctr_inc ctr0)`
        SUBST1_TAC THENL
       [REWRITE_TAC[num_CONV `2`; num_CONV `1`; gcm_ctr_inc_iter]; ALL_TAC] THEN
      GEN_REWRITE_TAC RAND_CONV [GCM_CTR_INC2_LANES] THEN
      REFL_TAC THEN NO_TAC) THEN
  (* out block-0 (out_p): word_xor cph0 (aes256_encrypt ctr0 keys) via JOIN_IS_CTR0.  Both halves. *)
  TRY(AP_THM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[JOIN_IS_CTR0] THEN
      REWRITE_TAC[aes256_encrypt] THEN REWRITE_TAC EL_15_128_CLAUSES THEN
      REWRITE_TAC[aes256_encrypt_round; aese; aesmc] THEN
      CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
      REWRITE_TAC[aese; aesmc] THEN CONV_TAC WORD_RULE THEN NO_TAC) THEN
  (* out block-1 (out_p+16): word_xor cph1 (aes256_encrypt (gcm_ctr_inc ctr0) keys).  Rewrite the
     spec counter gcm_ctr_inc ctr0 -> its +1 byte-tower (GCM_CTR_INC_LANES), expand aes, WORD_RULE;
     WORD_BLAST fallback for the hi (64,64) half which WORD_RULE alone left open. *)
  TRY(AP_THM_TAC THEN AP_TERM_TAC THEN
      GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [GCM_CTR_INC_LANES] THEN
      REWRITE_TAC[aes256_encrypt] THEN REWRITE_TAC EL_15_128_CLAUSES THEN
      REWRITE_TAC[aes256_encrypt_round; aese; aesmc] THEN
      CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
      REWRITE_TAC[aese; aesmc] THEN (CONV_TAC WORD_RULE ORELSE CONV_TAC WORD_BLAST) THEN NO_TAC) THEN
  TRY(REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
      REPEAT CONJ_TAC THEN MONOTONE_MAYCHANGE_TAC THEN NO_TAC));;

(* ==== k=3 fused body (session-132-work/WB_FUSED_3BLOCK_PROVEN.ml) ==== *)
(* SESSION 127: WB_FUSED_3BLOCK (k=3) FULL PROOF. Route-b, extended from the VALIDATED
   k=2 proof (session-126-work/wb2_v3_qq8fold.ml) using the s127 diagnostic (wb3_diag.ml,
   RESTORE_EXIT=0) which confirmed: SIM self-contains at s80/s123/s170; bridge = the SAME
   three block-0 (H^3) mid distributions as k=2 (index-shifted qq11=qq1⊕qq7, qq10=qq0⊕qq6,
   qq16=qq12⊕qq13); NO FOLD_MID_HPOW (ABBREV_INNER_PMULS folds the block1×H² mid combined).

   htable (le3block:600-604): htbl+0=h,+16=hk,+32=h2,+48=h3,+64=h3k.
   hk=[fold(h)@16, fold(h2)@24]; h3k=[fold(h3)@64, fold(h4)@72]. k=3 reads fold(h)@16,
   fold(h2)@24 (needs +24 norm), fold(h3)@64. UNSPLIT hk@16 AND h3k@64.
   SIM windows: (1--30); g3/blk0 KEEPGHALL (31--80),pt0@s80; g2/blk1 (81--123),pt1@s123;
   g1/blk2+reduce (124--170), bridge s170. Tail s170->s183: xi@s177,ivec@s180,pt2@s182. *)

(* Shared fused-arc helpers (DISCARD_OLDSTATE_KEEPGHALL_TAC, ARM_STEPS_FOLD_KEEPGHALL_TAC,
   JOIN_IS_CTR0, INLINE_SELFCONTAINED, POLYVAL_DOT_SYM) — refine-094 consolidation. *)

(* s130 CURE for the environmental MAYCHANGE spin (see wb-dec-fused-3block-s130.md): the real
   accumulated k=3 frame is aconv-identical to a term whose `frame subsumed goal` closes in ~5s in
   a CLEAN environment, but SUBSUMED_MAYCHANGE_TAC spins ~6min after the full fused SIM (env-degraded,
   closer-independent — both the discard and plain variants spin, s130 v7f/v10).  FIX: prove the exact
   subsumption as a lemma HERE, at file top BEFORE the SIM (clean env, ~5s), then at the MAYCHANGE goal
   apply it via MATCH_MP transport + ETA + ACCEPT (instant), never re-running SUBSUMED post-SIM.
   NB: pure frame algebra, NO fused deps — provable/checkable on the base polyval-aes MCP. *)
(* (WB3_MC_TRANSPORT removed refine-094: dead code — the frame is discharged via the
   pre-computed direct implication WB3_FRAME_IMP, never via a transport lemma.) *)

let WB3_FRAME_SUBSUMED = prove(
 `(MAYCHANGE [PC] ,, MAYCHANGE [X9] ,, MAYCHANGE [X16] ,, MAYCHANGE [X11] ,,
   MAYCHANGE [X5] ,, MAYCHANGE [memory :> bytes64 (word_add stackpointer (word 64))] ,,
   MAYCHANGE [memory :> bytes64 (word_add stackpointer (word 72))] ,, MAYCHANGE [events] ,,
   MAYCHANGE [X10] ,, MAYCHANGE [NF] ,, MAYCHANGE [ZF] ,, MAYCHANGE [CF] ,, MAYCHANGE [VF] ,,
   MAYCHANGE [Q30] ,, MAYCHANGE [Q19] ,, MAYCHANGE [X15] ,, MAYCHANGE [Q31] ,, MAYCHANGE [Q16] ,,
   MAYCHANGE [Q29] ,, MAYCHANGE [Q1] ,, MAYCHANGE [Q2] ,, MAYCHANGE [Q3] ,, MAYCHANGE [Q4] ,,
   MAYCHANGE [Q5] ,, MAYCHANGE [Q6] ,, MAYCHANGE [Q7] ,, MAYCHANGE [Q8] ,, MAYCHANGE [Q9] ,,
   MAYCHANGE [Q10] ,, MAYCHANGE [Q11] ,, MAYCHANGE [Q12] ,, MAYCHANGE [Q13] ,, MAYCHANGE [Q14] ,,
   MAYCHANGE [Q15] ,, MAYCHANGE [Q24] ,, MAYCHANGE [Q25] ,, MAYCHANGE [Q21] ,, MAYCHANGE [Q17] ,,
   MAYCHANGE [Q18] ,, MAYCHANGE [Q26] ,, MAYCHANGE [X0] ,, MAYCHANGE [Q0] ,, MAYCHANGE [Q20] ,,
   MAYCHANGE [Q22] ,, MAYCHANGE [Q23] ,, MAYCHANGE [memory :> bytes128 out_p] ,, MAYCHANGE [X2] ,,
   MAYCHANGE [memory :> bytes128 (word_add out_p (word 16))] ,, MAYCHANGE [memory :> bytes128 xi_p] ,,
   MAYCHANGE [memory :> bytes128 ivec_p] ,,
   MAYCHANGE [memory :> bytes128 (word_add out_p (word 32))]
   :armstate->armstate->bool) subsumed
  (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
   MAYCHANGE [memory :> bytes(out_p:int64, 48); memory :> bytes(xi_p:int64,16);
              memory :> bytes(ivec_p:int64,16);
              memory :> bytes(word_add stackpointer (word 64):int64, 16)] ,,
   MAYCHANGE [Q0;Q1;Q2;Q3;Q4;Q5;Q6;Q7;Q8;Q9;Q10;Q11;Q12;Q13;Q14;Q15;
              Q16;Q17;Q18;Q19;Q20;Q21;Q22;Q23;Q24;Q25;Q26;Q27;Q28;Q29;Q30;Q31])`,
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN SUBSUMED_MAYCHANGE_TAC);;

(* Pre-compute the DIRECT implication `frame s0 s183 ==> goal s0 s183` (clean env, at file top):
   REWRITE_RULE[subsumed] turns `frame subsumed goal` into `!x y. frame x y ==> goal x y`, then
   SPECL to the real states s0/s183.  RHS has NO eta-redex (goal applied directly), so the fused
   proof closes with a single MATCH_MP+ACCEPT — no REWRITE[ETA_AX] traversal (env-slow post-SIM). *)
let WB3_FRAME_IMP =
  SPECL [`s0:armstate`; `s183:armstate`] (REWRITE_RULE[subsumed] WB3_FRAME_SUBSUMED);;

(* ---- wb.ml-only deps (NOT in fused ckpt; ckpt loads only up to le4block) ----
   (POLYVAL_DOT_SYM now comes from fused-wip/fused_common.ml.) *)
(* spec_to_byteform_wb3 reused from earlier in wb.ml (identical) *)

(* unmasked cph2 last-block specl (mirror k=2's dec_bridge_specl_2_cph1) *)
let dec_bridge_specl_3_cph2 =
  [`word_xor (word_bytereverse xi) (word_bytereverse cph0):int128`; `byteswap128 h3:int128`;
   `word_bytereverse cph1:int128`; `byteswap128 h2:int128`;
   `word_bytereverse cph2:int128`; `byteswap128 h:int128`];;

(* BRIDGE_CLOSE_3_CPH2_TAC: nblk=3, cph2 unmasked, NO FOLD_MID_HPOW.  Thin wrapper over the
   shared DEC_BRIDGE_ROUTEB_TAC (fused_common.ml); the 3 block-0(H^3) mid distributions
   (s127 diagnostic): qq11=qq1(+)qq7 (hi), qq10=qq0(+)qq6 (lo), qq16=qq12(+)qq13 (mid). *)
let BRIDGE_CLOSE_3_CPH2_TAC sN : tactic = fun (asl,w) ->
  let h2asm = snd(List.find(fun(_,th)->try lhs(concl th)=`byteswap128 h2` with _->false) asl) in
  let h3asm = snd(List.find(fun(_,th)->try lhs(concl th)=`byteswap128 h3` with _->false) asl) in
  let gmult_dec = REWRITE_RULE[LET_DEF;LET_END_DEF] (SPECL dec_bridge_specl_3_cph2 GMULT3_FULL_CORRECT_BA) in
  let spec_eq = TRANS (MP spec_to_byteform_wb3 (CONJ h2asm h3asm)) (GSYM gmult_dec) in
  DEC_BRIDGE_ROUTEB_TAC sN spec_eq
    (("qq11","qq1","qq7"),("qq10","qq0","qq6"),("qq16","qq12","qq13")) (asl,w);;

(* ---- route-b SIM helpers now come from fused-wip/fused_common.ml (needs at file top):
   DISCARD_OLDSTATE_KEEPGHALL_TAC, ARM_STEPS_FOLD_KEEPGHALL_TAC, JOIN_IS_CTR0,
   INLINE_SELFCONTAINED. ---- *)

let WB_FUSED_3BLOCK = prove(
 `!pc stackpointer out_p xi_p ivec_p in_p key_p htbl_p
    cph0 cph1 cph2 xi ctr0 k0 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 k11 k12 k13 k14 h hk h2 h3 h3k.
    aligned 16 stackpointer /\
    nonoverlapping (word pc, 5960) (stackpointer:int64, 80) /\
    nonoverlapping (word pc, 5960) (out_p:int64, 48) /\
    nonoverlapping (word pc, 5960) (xi_p:int64, 16) /\
    nonoverlapping (word pc, 5960) (ivec_p:int64, 16) /\
    nonoverlapping (out_p, 48) (xi_p, 16) /\
    nonoverlapping (out_p, 48) (ivec_p, 16) /\
    nonoverlapping (xi_p, 16) (ivec_p, 16) /\
    nonoverlapping (ivec_p, 16) (in_p:int64, 48) /\
    nonoverlapping (ivec_p, 16) (key_p:int64, 240) /\
    nonoverlapping (ivec_p, 16) (htbl_p:int64, 192) /\
    nonoverlapping (in_p, 48) (stackpointer, 80) /\
    nonoverlapping (key_p, 240) (stackpointer, 80) /\
    nonoverlapping (htbl_p, 192) (stackpointer, 80) /\
    nonoverlapping (ivec_p, 16) (stackpointer, 80) /\
    nonoverlapping (xi_p, 16) (in_p, 48) /\
    nonoverlapping (xi_p, 16) (key_p, 240) /\
    nonoverlapping (xi_p, 16) (htbl_p, 192) /\
    nonoverlapping (xi_p, 16) (stackpointer, 80) /\
    nonoverlapping (out_p, 48) (in_p, 48) /\
    nonoverlapping (out_p, 48) (key_p, 240) /\
    nonoverlapping (out_p, 48) (htbl_p, 192) /\
    nonoverlapping (out_p, 48) (stackpointer, 80) /\
    word_subword hk (0,64) :64 word =
      word_xor (word_subword h (0,64):64 word) (word_subword h (64,64):64 word) /\
    word_subword hk (64,64) :64 word =
      word_xor (word_subword h2 (0,64):64 word) (word_subword h2 (64,64):64 word) /\
    word_subword h3k (0,64) :64 word =
      word_xor (word_subword h3 (0,64):64 word) (word_subword h3 (64,64):64 word) /\
    byteswap128 h2 = polyval_dot (byteswap128 h) (byteswap128 h) /\
    byteswap128 h3 = polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h)
    ==> ensures arm
     (\s. aligned_bytes_loaded s (word pc) aesv8_gcm_8x_dec_256_wb_mc /\
          read PC s = word (pc + 0x20) /\ read SP s = stackpointer /\
          C_ARGUMENTS [in_p; word 384; out_p; xi_p; ivec_p; key_p; htbl_p] s /\
          read (memory :> bytes128 in_p) s = cph0 /\
          read (memory :> bytes128 (word_add in_p (word 16))) s = cph1 /\
          read (memory :> bytes128 (word_add in_p (word 32))) s = cph2 /\
          read (memory :> bytes128 xi_p) s = xi /\
          read (memory :> bytes128 ivec_p) s = ctr0 /\
          read (memory :> bytes128 key_p) s = k0 /\
          read (memory :> bytes128 (word_add key_p (word 16))) s = k1 /\
          read (memory :> bytes128 (word_add key_p (word 32))) s = k2 /\
          read (memory :> bytes128 (word_add key_p (word 48))) s = k3 /\
          read (memory :> bytes128 (word_add key_p (word 64))) s = k4 /\
          read (memory :> bytes128 (word_add key_p (word 80))) s = k5 /\
          read (memory :> bytes128 (word_add key_p (word 96))) s = k6 /\
          read (memory :> bytes128 (word_add key_p (word 112))) s = k7 /\
          read (memory :> bytes128 (word_add key_p (word 128))) s = k8 /\
          read (memory :> bytes128 (word_add key_p (word 144))) s = k9 /\
          read (memory :> bytes128 (word_add key_p (word 160))) s = k10 /\
          read (memory :> bytes128 (word_add key_p (word 176))) s = k11 /\
          read (memory :> bytes128 (word_add key_p (word 192))) s = k12 /\
          read (memory :> bytes128 (word_add key_p (word 208))) s = k13 /\
          read (memory :> bytes128 (word_add key_p (word 224))) s = k14 /\
          read (memory :> bytes128 htbl_p) s = h /\
          read (memory :> bytes128 (word_add htbl_p (word 16))) s = hk /\
          read (memory :> bytes128 (word_add htbl_p (word 32))) s = h2 /\
          read (memory :> bytes128 (word_add htbl_p (word 48))) s = h3 /\
          read (memory :> bytes128 (word_add htbl_p (word 64))) s = h3k)
     (\s. read PC s = word (pc + 0x11d0) /\
          read (memory :> bytes128 out_p) s =
          word_xor cph0 (aes256_encrypt ctr0
            [(k0:int128);k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14]) /\
          read (memory :> bytes128 (word_add out_p (word 16))) s =
          word_xor cph1 (aes256_encrypt (gcm_ctr_inc ctr0)
            [(k0:int128);k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14]) /\
          read (memory :> bytes128 (word_add out_p (word 32))) s =
          word_xor cph2 (aes256_encrypt (gcm_ctr_inc (gcm_ctr_inc ctr0))
            [(k0:int128);k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14]) /\
          read (memory :> bytes128 xi_p) s =
          word_bytereverse
            (ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
              [word_bytereverse cph0; word_bytereverse cph1; word_bytereverse cph2]) /\
          read (memory :> bytes128 ivec_p) s = gcm_ctr_inc_iter 3 ctr0)
     (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
      MAYCHANGE [memory :> bytes(out_p, 48); memory :> bytes(xi_p, 16);
                 memory :> bytes(ivec_p, 16);
                 memory :> bytes(word_add stackpointer (word 64):int64, 16)] ,,
      MAYCHANGE [Q0;Q1;Q2;Q3;Q4;Q5;Q6;Q7;Q8;Q9;Q10;Q11;Q12;Q13;Q14;Q15;
                 Q16;Q17;Q18;Q19;Q20;Q21;Q22;Q23;Q24;Q25;Q26;Q27;Q28;Q29;Q30;Q31])`,
  REPEAT GEN_TAC THEN REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS] THEN STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  CLEAR_KEEPGHALL_MEMO_TAC THEN  (* refine-099: reset the fused normalizer fixpoint cache *)
  (* UNSPLIT hk (htbl+16): g1 fold(h)@16 lo + g2 fold(h2)@24 hi *)
  FIRST_ASSUM(fun th ->
    if (try lhs(concl th) = `read (memory :> bytes128 (word_add htbl_p (word 16))) s0`
        with _ -> false)
    then (MP_TAC th THEN PURE_ONCE_REWRITE_TAC[el 1 (CONJUNCTS READ_MEMORY_BYTESIZED_UNSPLIT)] THEN
          STRIP_TAC)
    else NO_TAC) THEN
  (* UNSPLIT h3k (htbl+64): g3 fold(h3)@64 lo *)
  FIRST_ASSUM(fun th ->
    if (try lhs(concl th) = `read (memory :> bytes128 (word_add htbl_p (word 64))) s0`
        with _ -> false)
    then (MP_TAC th THEN PURE_ONCE_REWRITE_TAC[el 1 (CONJUNCTS READ_MEMORY_BYTESIZED_UNSPLIT)] THEN
          STRIP_TAC)
    else NO_TAC) THEN
  (* normalize hk-high address so g2 ldr d25,[x6,#24] resolves *)
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
    `word_add (word_add (htbl_p:int64) (word 16)) (word 8) = word_add htbl_p (word 24)`]) THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (1--30) THEN
  (* g3 window (block0 x H^3): steps 31-80, pt0 store @ s80 *)
  ARM_STEPS_FOLD_KEEPGHALL_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (31--80) THEN
  SUBGOAL_THEN
    `read (memory :> bytes128 out_p) (s80:armstate) =
     word_xor cph0 (aes256_encrypt ctr0
       [(k0:int128);k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14])`
    ASSUME_TAC THENL
  [ASM_REWRITE_TAC[] THEN REWRITE_TAC[JOIN_IS_CTR0] THEN
   REWRITE_TAC[aes256_encrypt] THEN REWRITE_TAC EL_15_128_CLAUSES THEN
   REWRITE_TAC[aes256_encrypt_round; aese; aesmc] THEN
   CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   REWRITE_TAC[aese; aesmc] THEN CONV_TAC WORD_RULE;
   ALL_TAC] THEN
  INLINE_SELFCONTAINED "Q17" "s80" 30 THEN
  INLINE_SELFCONTAINED "Q18" "s80" 30 THEN
  INLINE_SELFCONTAINED "Q19" "s80" 30 THEN
  DISCARD_OLDSTATE_TAC "s80" THEN
  (* g2 window (block1 x H^2): steps 81-123, pt1 store @ s123.  Capture pt1 (counter
     gcm_ctr_inc ctr0) before DISCARD -- GCM_CTR_INC_LANES then the aes tower. *)
  ARM_STEPS_FOLD_KEEPGHALL_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (81--123) THEN
  SUBGOAL_THEN
    `read (memory :> bytes128 (word_add out_p (word 16))) (s123:armstate) =
     word_xor cph1 (aes256_encrypt (gcm_ctr_inc ctr0)
       [(k0:int128);k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14])`
    ASSUME_TAC THENL
  [ASM_REWRITE_TAC[] THEN
   GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [GCM_CTR_INC_LANES] THEN
   REWRITE_TAC[aes256_encrypt] THEN REWRITE_TAC EL_15_128_CLAUSES THEN
   REWRITE_TAC[aes256_encrypt_round; aese; aesmc] THEN
   CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   REWRITE_TAC[aese; aesmc] THEN (CONV_TAC WORD_RULE ORELSE CONV_TAC WORD_BLAST);
   ALL_TAC] THEN
  INLINE_SELFCONTAINED "Q17" "s123" 40 THEN
  INLINE_SELFCONTAINED "Q18" "s123" 40 THEN
  INLINE_SELFCONTAINED "Q19" "s123" 40 THEN
  DISCARD_OLDSTATE_TAC "s123" THEN
  (* g1 window (block2 x H + reduce): steps 124-170, bridge s170 *)
  ARM_STEPS_FOLD_KEEPGHALL_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (124--170) THEN
  INLINE_SELFCONTAINED "Q19" "s170" 12 THEN
  DISCARD_OLDSTATE_TAC "s170" THEN
  SUBGOAL_THEN
    `read Q19 (s170:armstate) =
     ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
       [word_bytereverse cph0; word_bytereverse cph1; word_bytereverse cph2]`
    (fun th -> RULE_ASSUM_TAC(fun asm ->
       if (try lhs(concl asm) = `read Q19 s170` with _ -> false)
       then th else asm) THEN ASSUME_TAC th) THENL
  [BRIDGE_CLOSE_3_CPH2_TAC 170;
   ALL_TAC] THEN
  ABBREV_TAC `gval:int128 = ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
       [word_bytereverse cph0; word_bytereverse cph1; word_bytereverse cph2]` THEN
  (* tail s170->s183: ext@s173, rev64 v19@s174 (=brev gval) *)
  ARM_STEPS_FOLD_DISCARD_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (171--174) THEN
  SUBGOAL_THEN `read Q19 (s174:armstate) = word_bytereverse (gval:int128)`
    (fun th -> RULE_ASSUM_TAC(fun asm ->
       if (try lhs(concl asm) = `read Q19 s174` with _ -> false)
       then th else asm) THEN ASSUME_TAC th) THENL
  [FIRST_ASSUM(fun th ->
     if is_eq(concl th) && (try lhs(concl th) = `read Q19 s174` with _ -> false)
     then GEN_REWRITE_TAC LAND_CONV [th] else NO_TAC) THEN CONV_TAC WORD_BLAST;
   ALL_TAC] THEN
  ARM_STEPS_FOLD_DISCARD_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (175--183) THEN
  (* split the s183 bytes128 store readbacks into bytes64 halves *)
  RULE_ASSUM_TAC(fun th ->
    match concl th with
    | Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),
        Comb(Comb(Const(":>",_),Const("memory",_)),
             Comb(Const("bytes128",_),_))),st)),_)
        when (try fst(dest_var st)="s183" with _ -> false) ->
        (try CONV_RULE(READ_MEMORY_SPLIT_CONV 1) th with _ -> th)
    | _ -> th) THEN
  REPEAT(FIRST_X_ASSUM(fun th ->
    if is_conj(concl th) then STRIP_ASSUME_TAC th else NO_TAC)) THEN
  (* normalize block-1/block-2 store hi-half addresses *)
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
    `word_add (word_add (out_p:int64) (word 16)) (word 8) = word_add out_p (word 24)`;
    WORD_RULE
    `word_add (word_add (out_p:int64) (word 32)) (word 8) = word_add out_p (word 40)`]) THEN
  (* Peel MAYCHANGE first (else REPEAT CONJ_TAC splits its ,, structure). *)
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[WORD_RULE
    `word_add (word_add (out_p:int64) (word 16)) (word 8) = word_add out_p (word 24)`;
    WORD_RULE
    `word_add (word_add (out_p:int64) (word 32)) (word 8) = word_add out_p (word 40)`] THEN
  (* s127 store-diag (wb3_stores_diag.ml): after ASM_REWRITE the block-1 (out_p+16, captured
     pt1@s123) and xi halves ALREADY CLOSE.  The 7 remaining conjuncts are: block-0 lo/hi
     (RHS aes256_encrypt ctr0), block-2 lo/hi (RHS aes256_encrypt (gcm_ctr_inc(gcm_ctr_inc ctr0))),
     ivec lo/hi (gcm_ctr_inc_iter 3), and MAYCHANGE.  The earlier full run HUNG because the
     block-0 closer (JOIN_IS_CTR0 + WORD_RULE, no blast) cross-fired on a block-2 conjunct and
     WORD_RULE spun on the un-normalized +2 tower.  FIX: guard each closer to its own RHS
     counter (bare ctr0 vs gcm_ctr_inc(gcm_ctr_inc)) so it never touches the wrong conjunct. *)
  (fun (asl,w) -> Printf.printf "POST-ENSURES-FINAL reached, goal-len=%d nasl=%d\n%!" (String.length(string_of_term w)) (length asl); ALL_TAC (asl,w)) THEN
  REPEAT CONJ_TAC THEN
  (fun (asl,w) -> Printf.printf "SUBGOAL len=%d\n%!" (String.length(string_of_term w)); ALL_TAC (asl,w)) THEN
  (* s128 ROOT CAUSE (localized via wb3_v4_probe ENTER/DONE timing on the fused ckpt): the STORE
     closers are FAST (blk0 0.01s, blk2 0.03s, ivec 0.00s).  The ~7-min spin was the block-0
     closer CROSS-FIRING onto the XI conjunct: xi's goal (word_bytereverse gval = word_bytereverse
     GPA) has NO gcm_ctr_inc, so the s127/v3 block-0 guard ("fail if gcm_ctr_inc") ACCEPTED it and
     ran AP_THM+JOIN_IS_CTR0+expand+WORD_BLAST on the ghash_polyval_acc poly => WORD_BLAST descended
     into the poly => spin.  FIX: POSITIVE, mutually-exclusive guards; run XI first; guard block-0
     POSITIVELY on aes256_encrypt (so it never touches the ghash goal). *)
  (* XI (RHS = word_bytereverse of ghash_polyval_acc / gval): strip word_bytereverse, then fold the
     goal's GPA back to gval via a TARGETED check-based SUBST of the gval ABBREV assumption (proven
     s122/v42 pattern) — NEVER EXPAND_TAC "gval" (it FIRST_X_ASSUM-scans, may hit read-Q19=gval asms
     over the 1242-asm context).  s129 instrumentation: XI-ENTER at guard, XI-CLOSED after body — if
     both print then spin, the spin is the final prove-replay (b), not the xi closer (a). *)
  TRY((fun (asl,w) ->
        if not(can (find_term (fun t -> try fst(dest_const(fst(strip_comb t)))="ghash_polyval_acc" with _->false)) w
              || can (find_term (fun t -> t = `gval:int128`)) w)
        then failwith "not-xi" else
        (Printf.printf "XI-ENTER len=%d\n%!" (String.length(string_of_term w));
         let r =
           (TRY(AP_THM_TAC THEN AP_TERM_TAC) THEN AP_TERM_TAC THEN
            FIRST_X_ASSUM(SUBST1_TAC o SYM o
              check (fun th -> try rhs(concl th) = `gval:int128` &&
                                   (match lhs(concl th) with
                                    | Comb(Comb(Const("ghash_polyval_acc",_),_),_) -> true | _ -> false)
                               with _ -> false)) THEN
            REFL_TAC) (asl,w) in
         Printf.printf "XI-CLOSED\n%!"; r))
      THEN NO_TAC) THEN
  (* ivec half (RHS = gcm_ctr_inc_iter 3) *)
  TRY((fun (asl,w) ->
        if not(can (find_term (fun t -> try fst(dest_const(fst(strip_comb t)))="gcm_ctr_inc_iter" with _->false)) w)
        then failwith "not-ivec" else
        (AP_THM_TAC THEN AP_TERM_TAC THEN
         SUBGOAL_THEN `gcm_ctr_inc_iter 3 ctr0 = gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ctr0))`
           SUBST1_TAC THENL
          [REWRITE_TAC[num_CONV `3`; num_CONV `2`; num_CONV `1`; gcm_ctr_inc_iter]; ALL_TAC] THEN
         GEN_REWRITE_TAC RAND_CONV [GCM_CTR_INC3_LANES] THEN REFL_TAC) (asl,w)) THEN NO_TAC) THEN
  (* out block-2 (out_p+32): RHS = aes256_encrypt (gcm_ctr_inc (gcm_ctr_inc ctr0)).  le4block
     WORD_XOR_ASSOC+WORD_BLAST closer (proven 0.03s in the probe). *)
  TRY((fun (asl,w) ->
        if not(can (find_term (fun t -> t = `gcm_ctr_inc (gcm_ctr_inc ctr0):int128`)) w)
        then failwith "not-blk2" else
        (AP_THM_TAC THEN AP_TERM_TAC THEN
         GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [GCM_CTR_INC2_LANES] THEN
         ONCE_REWRITE_TAC[WORD_XOR_ASSOC] THEN
         REWRITE_TAC[aes256_encrypt] THEN REWRITE_TAC EL_15_128_CLAUSES THEN
         REWRITE_TAC[aes256_encrypt_round; aese; aesmc] THEN
         CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
         REWRITE_TAC[WORD_XOR_ASSOC] THEN CONV_TAC WORD_BLAST) (asl,w)) THEN NO_TAC) THEN
  (* out block-0 (out_p, bare ctr0): POSITIVE guard = has aes256_encrypt AND NOT gcm_ctr_inc/ghash,
     so it fires ONLY on the two block-0 halves.  le4block WORD_XOR_ASSOC+WORD_BLAST (probe 0.01s). *)
  TRY((fun (asl,w) ->
        if not(can (find_term (fun t -> try fst(dest_const(fst(strip_comb t)))="aes256_encrypt" with _->false)) w)
           || can (find_term (fun t -> try fst(dest_const(fst(strip_comb t)))="gcm_ctr_inc" with _->false)) w
           || can (find_term (fun t -> try fst(dest_const(fst(strip_comb t)))="ghash_polyval_acc" with _->false)) w
        then failwith "not-blk0" else
        (AP_THM_TAC THEN AP_TERM_TAC THEN
         REWRITE_TAC[JOIN_IS_CTR0] THEN
         ONCE_REWRITE_TAC[WORD_XOR_ASSOC] THEN
         REWRITE_TAC[aes256_encrypt] THEN REWRITE_TAC EL_15_128_CLAUSES THEN
         REWRITE_TAC[aes256_encrypt_round; aese; aesmc] THEN
         CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
         REWRITE_TAC[WORD_XOR_ASSOC] THEN CONV_TAC WORD_BLAST) (asl,w)) THEN NO_TAC) THEN
  (* MAYCHANGE (len=377): s129 FINAL DIAGNOSIS. This is the SOLE remaining blocker — all store
     (blk0/blk1/blk2), xi and ivec closers work (all 7 SUBGOAL prints fire).  v7f proved with an
     MC-PRE-MONO probe: after DISCARD to nasl=1, `REWRITE[ABI] THEN REPEAT CONJ_TAC THEN MONOTONE`
     STILL SPINS 6min.  Yet the EXACT dumped frames (v8) reproduced on the base MCP close in 4.6s
     (nasl=1) / 8.4s (with 1241 junk asms) — WITH or WITHOUT discard, WITH or WITHOUT trailing
     ASM_REWRITE.  So the real accumulated MAYCHANGE assumption differs from the pretty-printed
     dump in a way that makes SUBSUMED_MAYCHANGE_TAC's SUBSUMED_SEQ_LEFT/RIGHT recursion explode
     (O(2^n) backtracking over the ~52 single-component `,,` chain).
     PROVEN CURE (next session): adopt le4block full_le4_tac_stores Q12-interleaved-respec
     (..._le4block.ml:246-281): respec plaintext reg Q12 -> opaque pt_i BEFORE each st1{v12} and
     DISCARD_OLDSTATE after each capture, so the accumulated frame stays MINIMAL and ORDERED the
     way le4block's proven closer (:353) handles — le4block closes THIS machine's MAYCHANGE. *)
  (* s130 CURE rev2: close via the PRE-COMPUTED direct implication WB3_FRAME_IMP (built at file
     top, clean env: `frame s0 s183 ==> goal s0 s183`, NO eta-redex since REWRITE_RULE[subsumed]
     specializes to the states directly).  rev1 (transport + REWRITE[ETA_AX]) spun AFTER
     MC-PRE-APPLY nasl=1 — the REWRITE[ETA_AX] traversal (or the transport MATCH_MP) is env-slow
     post-SIM.  rev2 removes REWRITE[ETA] entirely: discard to nasl=1, then one MATCH_MP+ACCEPT. *)
  (fun (asl,w) -> Printf.printf "MC-ENTER len=%d nasl=%d\n%!" (String.length(string_of_term w)) (length asl); ALL_TAC (asl,w)) THEN
  DISCARD_ASSUMPTIONS_TAC (fun th -> not(maychange_term(concl th))) THEN
  (fun (asl,w) -> Printf.printf "MC-PRE-APPLY nasl=%d\n%!" (length asl); ALL_TAC (asl,w)) THEN
  FIRST_X_ASSUM(fun th -> ACCEPT_TAC(MATCH_MP WB3_FRAME_IMP th)) THEN
  (fun (asl,w) -> Printf.printf "MC-DONE-LEMMA\n%!"; ALL_TAC (asl,w)));;
Printf.printf "ALL-SUBGOALS-DONE, entering prove-replay\n%!";;

(* ==== k=4 fused body (session-133-work/WB_FUSED_4BLOCK_PROVEN.ml) ==== *)
(* SESSION 133: WB_FUSED_4BLOCK (k=4) FINAL PROOF (prove()).
   SIM step-map + bridge distributions + all data closers VALIDATED by wb4_close.ml stage-2
   (RESTORE_EXIT=0, BRIDGE-CLOSED-s214 fired, POST-ENSURES-FINAL nasl=1303).
   Structure = WB_FUSED_3BLOCK_PROVEN.ml extended to 4 windows.
     plain (1--30); w0 blk0xH^4 KEEPGHALL (31--81) pt0@s81; w1 blk1xH^3 (82--124) pt1@s124;
     w2 blk2xH^2 (125--167) pt2@s167; w3 blk3xH+reduce (168--214) bridge@s214;
     brev@s218; tail VSTEPS (215--227): xi@s221, ivec@s224, blk3 store@s226, b@s227.
   Bridge: qq14=qq9(+)qq1 (hi), qq13=qq8(+)qq0 (lo), qq20=qq15(+)qq16 (mid).
   Closers THEN-chained (apply to ALL post-conjuncts): xi, ivec(iter4), blk3(inc^3), blk2(inc^2),
     blk1(inc^1), blk0(bare ctr0). MAYCHANGE via WB4_FRAME_IMP (built clean at file top). *)

(* Shared fused-arc helpers (DISCARD_OLDSTATE_KEEPGHALL_TAC, ARM_STEPS_FOLD_KEEPGHALL_TAC,
   JOIN_IS_CTR0, INLINE_SELFCONTAINED, POLYVAL_DOT_SYM) — refine-094 consolidation. *)

(* ---- MAYCHANGE frame lemma (clean env at file top; frame algebra, no fused deps) ---- *)
(* (WB4_MC_TRANSPORT removed refine-094: dead code — the frame is discharged via the
   pre-computed direct implication WB4_FRAME_IMP, never via a transport lemma.) *)

let WB4_FRAME_SUBSUMED = prove(
 `(MAYCHANGE [PC] ,, MAYCHANGE [X9] ,, MAYCHANGE [X16] ,, MAYCHANGE [X11] ,,
   MAYCHANGE [X5] ,, MAYCHANGE [memory :> bytes64 (word_add stackpointer (word 64))] ,,
   MAYCHANGE [memory :> bytes64 (word_add stackpointer (word 72))] ,, MAYCHANGE [events] ,,
   MAYCHANGE [X10] ,, MAYCHANGE [NF] ,, MAYCHANGE [ZF] ,, MAYCHANGE [CF] ,, MAYCHANGE [VF] ,,
   MAYCHANGE [Q30] ,, MAYCHANGE [Q19] ,, MAYCHANGE [X15] ,, MAYCHANGE [Q31] ,, MAYCHANGE [Q16] ,,
   MAYCHANGE [Q29] ,, MAYCHANGE [Q1] ,, MAYCHANGE [Q2] ,, MAYCHANGE [Q3] ,, MAYCHANGE [Q4] ,,
   MAYCHANGE [Q5] ,, MAYCHANGE [Q6] ,, MAYCHANGE [Q7] ,, MAYCHANGE [Q8] ,, MAYCHANGE [Q9] ,,
   MAYCHANGE [Q10] ,, MAYCHANGE [Q11] ,, MAYCHANGE [Q12] ,, MAYCHANGE [Q13] ,, MAYCHANGE [Q14] ,,
   MAYCHANGE [Q15] ,, MAYCHANGE [Q24] ,, MAYCHANGE [Q25] ,, MAYCHANGE [Q21] ,, MAYCHANGE [Q17] ,,
   MAYCHANGE [Q18] ,, MAYCHANGE [Q26] ,, MAYCHANGE [X0] ,, MAYCHANGE [Q0] ,, MAYCHANGE [Q20] ,,
   MAYCHANGE [Q22] ,, MAYCHANGE [Q23] ,, MAYCHANGE [memory :> bytes128 out_p] ,, MAYCHANGE [X2] ,,
   MAYCHANGE [memory :> bytes128 (word_add out_p (word 16))] ,,
   MAYCHANGE [memory :> bytes128 (word_add out_p (word 32))] ,,
   MAYCHANGE [memory :> bytes128 xi_p] ,,
   MAYCHANGE [memory :> bytes128 ivec_p] ,,
   MAYCHANGE [memory :> bytes128 (word_add out_p (word 48))]
   :armstate->armstate->bool) subsumed
  (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
   MAYCHANGE [memory :> bytes(out_p:int64, 64); memory :> bytes(xi_p:int64,16);
              memory :> bytes(ivec_p:int64,16);
              memory :> bytes(word_add stackpointer (word 64):int64, 16)] ,,
   MAYCHANGE [Q0;Q1;Q2;Q3;Q4;Q5;Q6;Q7;Q8;Q9;Q10;Q11;Q12;Q13;Q14;Q15;
              Q16;Q17;Q18;Q19;Q20;Q21;Q22;Q23;Q24;Q25;Q26;Q27;Q28;Q29;Q30;Q31])`,
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN SUBSUMED_MAYCHANGE_TAC);;

let WB4_FRAME_IMP =
  SPECL [`s0:armstate`; `s227:armstate`] (REWRITE_RULE[subsumed] WB4_FRAME_SUBSUMED);;

(* GCM_CTR_INC4_LANES is le5block-only -> define in-file (base GCM_CTR_INC_LANES is in ckpt) *)
(* GCM_CTR_INC4_LANES reused from earlier in wb.ml (identical) *)

(* ---- wb.ml-only deps ---- (POLYVAL_DOT_SYM now comes from fused-wip/fused_common.ml.) *)
(* spec_to_byteform_wb4 reused from earlier in wb.ml (identical) *)

let dec_bridge_specl_4_cph3 =
  [`word_xor (word_bytereverse xi) (word_bytereverse cph0):int128`; `byteswap128 h4:int128`;
   `word_bytereverse cph1:int128`; `byteswap128 h3:int128`;
   `word_bytereverse cph2:int128`; `byteswap128 h2:int128`;
   `word_bytereverse cph3:int128`; `byteswap128 h:int128`];;

(* BRIDGE_CLOSE_4_CPH3_TAC: nblk=4, cph3 unmasked.  Thin wrapper over the shared
   DEC_BRIDGE_ROUTEB_TAC (fused_common.ml); the 3 block-0(H^4) mid distributions:
   qq14=qq9(+)qq1 (hi), qq13=qq8(+)qq0 (lo), qq20=qq15(+)qq16 (mid). *)
let BRIDGE_CLOSE_4_CPH3_TAC sN : tactic = fun (asl,w) ->
  let h2asm = snd(List.find(fun(_,th)->try lhs(concl th)=`byteswap128 h2` with _->false) asl) in
  let h3asm = snd(List.find(fun(_,th)->try lhs(concl th)=`byteswap128 h3` with _->false) asl) in
  let h4asm = snd(List.find(fun(_,th)->try lhs(concl th)=`byteswap128 h4` with _->false) asl) in
  let gmult_dec = REWRITE_RULE[LET_DEF;LET_END_DEF] (SPECL dec_bridge_specl_4_cph3 GMULT4_FULL_CORRECT_BA) in
  let spec_eq = TRANS (MP spec_to_byteform_wb4 (CONJ h2asm (CONJ h3asm h4asm))) (GSYM gmult_dec) in
  DEC_BRIDGE_ROUTEB_TAC sN spec_eq
    (("qq14","qq9","qq1"),("qq13","qq8","qq0"),("qq20","qq15","qq16")) (asl,w);;

(* ---- route-b SIM helpers now come from fused-wip/fused_common.ml (needs at file top):
   DISCARD_OLDSTATE_KEEPGHALL_TAC, ARM_STEPS_FOLD_KEEPGHALL_TAC, JOIN_IS_CTR0,
   INLINE_SELFCONTAINED. ---- *)

let WB_FUSED_4BLOCK = prove(
 `!pc stackpointer out_p xi_p ivec_p in_p key_p htbl_p
    cph0 cph1 cph2 cph3 xi ctr0 k0 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 k11 k12 k13 k14 h hk h2 h3 h3k h4.
    aligned 16 stackpointer /\
    nonoverlapping (word pc, 5960) (stackpointer:int64, 80) /\
    nonoverlapping (word pc, 5960) (out_p:int64, 64) /\
    nonoverlapping (word pc, 5960) (xi_p:int64, 16) /\
    nonoverlapping (word pc, 5960) (ivec_p:int64, 16) /\
    nonoverlapping (out_p, 64) (xi_p, 16) /\
    nonoverlapping (out_p, 64) (ivec_p, 16) /\
    nonoverlapping (xi_p, 16) (ivec_p, 16) /\
    nonoverlapping (ivec_p, 16) (in_p:int64, 64) /\
    nonoverlapping (ivec_p, 16) (key_p:int64, 240) /\
    nonoverlapping (ivec_p, 16) (htbl_p:int64, 192) /\
    nonoverlapping (in_p, 64) (stackpointer, 80) /\
    nonoverlapping (key_p, 240) (stackpointer, 80) /\
    nonoverlapping (htbl_p, 192) (stackpointer, 80) /\
    nonoverlapping (ivec_p, 16) (stackpointer, 80) /\
    nonoverlapping (xi_p, 16) (in_p, 64) /\
    nonoverlapping (xi_p, 16) (key_p, 240) /\
    nonoverlapping (xi_p, 16) (htbl_p, 192) /\
    nonoverlapping (xi_p, 16) (stackpointer, 80) /\
    nonoverlapping (out_p, 64) (in_p, 64) /\
    nonoverlapping (out_p, 64) (key_p, 240) /\
    nonoverlapping (out_p, 64) (htbl_p, 192) /\
    nonoverlapping (out_p, 64) (stackpointer, 80) /\
    word_subword hk (0,64) :64 word =
      word_xor (word_subword h (0,64):64 word) (word_subword h (64,64):64 word) /\
    word_subword hk (64,64) :64 word =
      word_xor (word_subword h2 (0,64):64 word) (word_subword h2 (64,64):64 word) /\
    word_subword h3k (0,64) :64 word =
      word_xor (word_subword h3 (0,64):64 word) (word_subword h3 (64,64):64 word) /\
    word_subword h3k (64,64) :64 word =
      word_xor (word_subword h4 (0,64):64 word) (word_subword h4 (64,64):64 word) /\
    byteswap128 h2 = polyval_dot (byteswap128 h) (byteswap128 h) /\
    byteswap128 h3 = polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h) /\
    byteswap128 h4 = polyval_dot (polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h)) (byteswap128 h)
    ==> ensures arm
     (\s. aligned_bytes_loaded s (word pc) aesv8_gcm_8x_dec_256_wb_mc /\
          read PC s = word (pc + 0x20) /\ read SP s = stackpointer /\
          C_ARGUMENTS [in_p; word 512; out_p; xi_p; ivec_p; key_p; htbl_p] s /\
          read (memory :> bytes128 in_p) s = cph0 /\
          read (memory :> bytes128 (word_add in_p (word 16))) s = cph1 /\
          read (memory :> bytes128 (word_add in_p (word 32))) s = cph2 /\
          read (memory :> bytes128 (word_add in_p (word 48))) s = cph3 /\
          read (memory :> bytes128 xi_p) s = xi /\
          read (memory :> bytes128 ivec_p) s = ctr0 /\
          read (memory :> bytes128 key_p) s = k0 /\
          read (memory :> bytes128 (word_add key_p (word 16))) s = k1 /\
          read (memory :> bytes128 (word_add key_p (word 32))) s = k2 /\
          read (memory :> bytes128 (word_add key_p (word 48))) s = k3 /\
          read (memory :> bytes128 (word_add key_p (word 64))) s = k4 /\
          read (memory :> bytes128 (word_add key_p (word 80))) s = k5 /\
          read (memory :> bytes128 (word_add key_p (word 96))) s = k6 /\
          read (memory :> bytes128 (word_add key_p (word 112))) s = k7 /\
          read (memory :> bytes128 (word_add key_p (word 128))) s = k8 /\
          read (memory :> bytes128 (word_add key_p (word 144))) s = k9 /\
          read (memory :> bytes128 (word_add key_p (word 160))) s = k10 /\
          read (memory :> bytes128 (word_add key_p (word 176))) s = k11 /\
          read (memory :> bytes128 (word_add key_p (word 192))) s = k12 /\
          read (memory :> bytes128 (word_add key_p (word 208))) s = k13 /\
          read (memory :> bytes128 (word_add key_p (word 224))) s = k14 /\
          read (memory :> bytes128 htbl_p) s = h /\
          read (memory :> bytes128 (word_add htbl_p (word 16))) s = hk /\
          read (memory :> bytes128 (word_add htbl_p (word 32))) s = h2 /\
          read (memory :> bytes128 (word_add htbl_p (word 48))) s = h3 /\
          read (memory :> bytes128 (word_add htbl_p (word 64))) s = h3k /\
          read (memory :> bytes128 (word_add htbl_p (word 80))) s = h4)
     (\s. read PC s = word (pc + 0x11d0) /\
          read (memory :> bytes128 out_p) s =
          word_xor cph0 (aes256_encrypt ctr0
            [(k0:int128);k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14]) /\
          read (memory :> bytes128 (word_add out_p (word 16))) s =
          word_xor cph1 (aes256_encrypt (gcm_ctr_inc ctr0)
            [(k0:int128);k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14]) /\
          read (memory :> bytes128 (word_add out_p (word 32))) s =
          word_xor cph2 (aes256_encrypt (gcm_ctr_inc (gcm_ctr_inc ctr0))
            [(k0:int128);k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14]) /\
          read (memory :> bytes128 (word_add out_p (word 48))) s =
          word_xor cph3 (aes256_encrypt (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ctr0)))
            [(k0:int128);k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14]) /\
          read (memory :> bytes128 xi_p) s =
          word_bytereverse
            (ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
              [word_bytereverse cph0; word_bytereverse cph1; word_bytereverse cph2; word_bytereverse cph3]) /\
          read (memory :> bytes128 ivec_p) s = gcm_ctr_inc_iter 4 ctr0)
     (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
      MAYCHANGE [memory :> bytes(out_p, 64); memory :> bytes(xi_p, 16);
                 memory :> bytes(ivec_p, 16);
                 memory :> bytes(word_add stackpointer (word 64):int64, 16)] ,,
      MAYCHANGE [Q0;Q1;Q2;Q3;Q4;Q5;Q6;Q7;Q8;Q9;Q10;Q11;Q12;Q13;Q14;Q15;
                 Q16;Q17;Q18;Q19;Q20;Q21;Q22;Q23;Q24;Q25;Q26;Q27;Q28;Q29;Q30;Q31])`,
  REPEAT GEN_TAC THEN REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS] THEN STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  CLEAR_KEEPGHALL_MEMO_TAC THEN  (* refine-099: reset the fused normalizer fixpoint cache *)
  (* UNSPLIT hk (htbl+16): fold(h)@16 lo + fold(h2)@24 hi *)
  FIRST_ASSUM(fun th ->
    if (try lhs(concl th) = `read (memory :> bytes128 (word_add htbl_p (word 16))) s0` with _ -> false)
    then (MP_TAC th THEN PURE_ONCE_REWRITE_TAC[el 1 (CONJUNCTS READ_MEMORY_BYTESIZED_UNSPLIT)] THEN STRIP_TAC)
    else NO_TAC) THEN
  (* UNSPLIT h3k (htbl+64): fold(h3)@64 lo + fold(h4)@72 hi *)
  FIRST_ASSUM(fun th ->
    if (try lhs(concl th) = `read (memory :> bytes128 (word_add htbl_p (word 64))) s0` with _ -> false)
    then (MP_TAC th THEN PURE_ONCE_REWRITE_TAC[el 1 (CONJUNCTS READ_MEMORY_BYTESIZED_UNSPLIT)] THEN STRIP_TAC)
    else NO_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
    `word_add (word_add (htbl_p:int64) (word 16)) (word 8) = word_add htbl_p (word 24)`;
    WORD_RULE
    `word_add (word_add (htbl_p:int64) (word 64)) (word 8) = word_add htbl_p (word 72)`]) THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (1--30) THEN
  (* w0 (block0 x H^4): steps 31-81, pt0 store @ s81 *)
  ARM_STEPS_FOLD_KEEPGHALL_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (31--81) THEN
  SUBGOAL_THEN
    `read (memory :> bytes128 out_p) (s81:armstate) =
     word_xor cph0 (aes256_encrypt ctr0
       [(k0:int128);k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14])`
    ASSUME_TAC THENL
  [ASM_REWRITE_TAC[] THEN REWRITE_TAC[JOIN_IS_CTR0] THEN
   REWRITE_TAC[aes256_encrypt] THEN REWRITE_TAC EL_15_128_CLAUSES THEN
   REWRITE_TAC[aes256_encrypt_round; aese; aesmc] THEN
   CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   REWRITE_TAC[aese; aesmc] THEN CONV_TAC WORD_RULE;
   ALL_TAC] THEN
  INLINE_SELFCONTAINED "Q17" "s81" 30 THEN
  INLINE_SELFCONTAINED "Q18" "s81" 30 THEN
  INLINE_SELFCONTAINED "Q19" "s81" 30 THEN
  DISCARD_OLDSTATE_TAC "s81" THEN
  (* w1 (block1 x H^3): steps 82-124, pt1 store @ s124 *)
  ARM_STEPS_FOLD_KEEPGHALL_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (82--124) THEN
  SUBGOAL_THEN
    `read (memory :> bytes128 (word_add out_p (word 16))) (s124:armstate) =
     word_xor cph1 (aes256_encrypt (gcm_ctr_inc ctr0)
       [(k0:int128);k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14])`
    ASSUME_TAC THENL
  [ASM_REWRITE_TAC[] THEN
   GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [GCM_CTR_INC_LANES] THEN
   REWRITE_TAC[aes256_encrypt] THEN REWRITE_TAC EL_15_128_CLAUSES THEN
   REWRITE_TAC[aes256_encrypt_round; aese; aesmc] THEN
   CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   REWRITE_TAC[aese; aesmc] THEN (CONV_TAC WORD_RULE ORELSE CONV_TAC WORD_BLAST);
   ALL_TAC] THEN
  INLINE_SELFCONTAINED "Q17" "s124" 40 THEN
  INLINE_SELFCONTAINED "Q18" "s124" 40 THEN
  INLINE_SELFCONTAINED "Q19" "s124" 40 THEN
  DISCARD_OLDSTATE_TAC "s124" THEN
  (* w2 (block2 x H^2): steps 125-167, pt2 store @ s167 *)
  ARM_STEPS_FOLD_KEEPGHALL_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (125--167) THEN
  SUBGOAL_THEN
    `read (memory :> bytes128 (word_add out_p (word 32))) (s167:armstate) =
     word_xor cph2 (aes256_encrypt (gcm_ctr_inc (gcm_ctr_inc ctr0))
       [(k0:int128);k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14])`
    ASSUME_TAC THENL
  [ASM_REWRITE_TAC[] THEN
   GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [GCM_CTR_INC2_LANES] THEN
   REWRITE_TAC[aes256_encrypt] THEN REWRITE_TAC EL_15_128_CLAUSES THEN
   REWRITE_TAC[aes256_encrypt_round; aese; aesmc] THEN
   CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
   REWRITE_TAC[aese; aesmc] THEN (CONV_TAC WORD_RULE ORELSE CONV_TAC WORD_BLAST);
   ALL_TAC] THEN
  INLINE_SELFCONTAINED "Q17" "s167" 40 THEN
  INLINE_SELFCONTAINED "Q18" "s167" 40 THEN
  INLINE_SELFCONTAINED "Q19" "s167" 40 THEN
  DISCARD_OLDSTATE_TAC "s167" THEN
  (* w3 (block3 x H + reduce): steps 168-214, bridge s214 *)
  ARM_STEPS_FOLD_KEEPGHALL_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (168--214) THEN
  INLINE_SELFCONTAINED "Q19" "s214" 12 THEN
  DISCARD_OLDSTATE_TAC "s214" THEN
  SUBGOAL_THEN
    `read Q19 (s214:armstate) =
     ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
       [word_bytereverse cph0; word_bytereverse cph1; word_bytereverse cph2; word_bytereverse cph3]`
    (fun th -> RULE_ASSUM_TAC(fun asm ->
       if (try lhs(concl asm) = `read Q19 s214` with _ -> false)
       then th else asm) THEN ASSUME_TAC th) THENL
  [BRIDGE_CLOSE_4_CPH3_TAC 214;
   ALL_TAC] THEN
  ABBREV_TAC `gval:int128 = ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
       [word_bytereverse cph0; word_bytereverse cph1; word_bytereverse cph2; word_bytereverse cph3]` THEN
  (* tail s214->s227: rev64 v19@s218 (=brev gval) *)
  ARM_STEPS_FOLD_DISCARD_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (215--218) THEN
  SUBGOAL_THEN `read Q19 (s218:armstate) = word_bytereverse (gval:int128)`
    (fun th -> RULE_ASSUM_TAC(fun asm ->
       if (try lhs(concl asm) = `read Q19 s218` with _ -> false)
       then th else asm) THEN ASSUME_TAC th) THENL
  [FIRST_ASSUM(fun th ->
     if is_eq(concl th) && (try lhs(concl th) = `read Q19 s218` with _ -> false)
     then GEN_REWRITE_TAC LAND_CONV [th] else NO_TAC) THEN CONV_TAC WORD_BLAST;
   ALL_TAC] THEN
  ARM_STEPS_FOLD_DISCARD_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (219--227) THEN
  (* split the s227 bytes128 store readbacks into bytes64 halves *)
  RULE_ASSUM_TAC(fun th ->
    match concl th with
    | Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),
        Comb(Comb(Const(":>",_),Const("memory",_)),
             Comb(Const("bytes128",_),_))),st)),_)
        when (try fst(dest_var st)="s227" with _ -> false) ->
        (try CONV_RULE(READ_MEMORY_SPLIT_CONV 1) th with _ -> th)
    | _ -> th) THEN
  REPEAT(FIRST_X_ASSUM(fun th ->
    if is_conj(concl th) then STRIP_ASSUME_TAC th else NO_TAC)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
    `word_add (word_add (out_p:int64) (word 16)) (word 8) = word_add out_p (word 24)`;
    WORD_RULE
    `word_add (word_add (out_p:int64) (word 32)) (word 8) = word_add out_p (word 40)`;
    WORD_RULE
    `word_add (word_add (out_p:int64) (word 48)) (word 8) = word_add out_p (word 56)`]) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[WORD_RULE
    `word_add (word_add (out_p:int64) (word 16)) (word 8) = word_add out_p (word 24)`;
    WORD_RULE
    `word_add (word_add (out_p:int64) (word 32)) (word 8) = word_add out_p (word 40)`;
    WORD_RULE
    `word_add (word_add (out_p:int64) (word 48)) (word 8) = word_add out_p (word 56)`] THEN
  (fun (asl,w) -> Printf.printf "POST-ENSURES-FINAL goal-len=%d nasl=%d\n%!" (String.length(string_of_term w)) (length asl); ALL_TAC (asl,w)) THEN
  REPEAT CONJ_TAC THEN
  (* XI (RHS = word_bytereverse of ghash_polyval_acc / gval) *)
  TRY((fun (asl,w) ->
        if not(can (find_term (fun t -> try fst(dest_const(fst(strip_comb t)))="ghash_polyval_acc" with _->false)) w
              || can (find_term (fun t -> t = `gval:int128`)) w)
        then failwith "not-xi" else
        (TRY(AP_THM_TAC THEN AP_TERM_TAC) THEN AP_TERM_TAC THEN
         FIRST_X_ASSUM(SUBST1_TAC o SYM o
           check (fun th -> try rhs(concl th) = `gval:int128` &&
                                (match lhs(concl th) with
                                 | Comb(Comb(Const("ghash_polyval_acc",_),_),_) -> true | _ -> false)
                            with _ -> false)) THEN
         REFL_TAC) (asl,w)) THEN NO_TAC) THEN
  (* ivec half (RHS = gcm_ctr_inc_iter 4) *)
  TRY((fun (asl,w) ->
        if not(can (find_term (fun t -> try fst(dest_const(fst(strip_comb t)))="gcm_ctr_inc_iter" with _->false)) w)
        then failwith "not-ivec" else
        (AP_THM_TAC THEN AP_TERM_TAC THEN
         SUBGOAL_THEN `gcm_ctr_inc_iter 4 ctr0 = gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ctr0)))`
           SUBST1_TAC THENL
          [REWRITE_TAC[num_CONV `4`; num_CONV `3`; num_CONV `2`; num_CONV `1`; gcm_ctr_inc_iter]; ALL_TAC] THEN
         GEN_REWRITE_TAC RAND_CONV [GCM_CTR_INC4_LANES] THEN REFL_TAC) (asl,w)) THEN NO_TAC) THEN
  (* out block-3 (out_p+48): RHS = aes256_encrypt (gcm_ctr_inc^3 ctr0) *)
  TRY((fun (asl,w) ->
        if not(can (find_term (fun t -> t = `gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ctr0)):int128`)) w)
        then failwith "not-blk3" else
        (AP_THM_TAC THEN AP_TERM_TAC THEN
         GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [GCM_CTR_INC3_LANES] THEN
         ONCE_REWRITE_TAC[WORD_XOR_ASSOC] THEN
         REWRITE_TAC[aes256_encrypt] THEN REWRITE_TAC EL_15_128_CLAUSES THEN
         REWRITE_TAC[aes256_encrypt_round; aese; aesmc] THEN
         CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
         REWRITE_TAC[WORD_XOR_ASSOC] THEN CONV_TAC WORD_BLAST) (asl,w)) THEN NO_TAC) THEN
  (* out block-2 (out_p+32): RHS = aes256_encrypt (gcm_ctr_inc^2 ctr0). Guard: inc^2 AND NOT inc^3 *)
  TRY((fun (asl,w) ->
        if not(can (find_term (fun t -> t = `gcm_ctr_inc (gcm_ctr_inc ctr0):int128`)) w)
           || can (find_term (fun t -> t = `gcm_ctr_inc (gcm_ctr_inc (gcm_ctr_inc ctr0)):int128`)) w
        then failwith "not-blk2" else
        (AP_THM_TAC THEN AP_TERM_TAC THEN
         GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [GCM_CTR_INC2_LANES] THEN
         ONCE_REWRITE_TAC[WORD_XOR_ASSOC] THEN
         REWRITE_TAC[aes256_encrypt] THEN REWRITE_TAC EL_15_128_CLAUSES THEN
         REWRITE_TAC[aes256_encrypt_round; aese; aesmc] THEN
         CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
         REWRITE_TAC[WORD_XOR_ASSOC] THEN CONV_TAC WORD_BLAST) (asl,w)) THEN NO_TAC) THEN
  (* out block-1 (out_p+16): RHS = aes256_encrypt (gcm_ctr_inc ctr0). Guard: inc^1 AND NOT inc^2 *)
  TRY((fun (asl,w) ->
        if not(can (find_term (fun t -> t = `gcm_ctr_inc ctr0:int128`)) w)
           || can (find_term (fun t -> t = `gcm_ctr_inc (gcm_ctr_inc ctr0):int128`)) w
        then failwith "not-blk1" else
        (AP_THM_TAC THEN AP_TERM_TAC THEN
         GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [GCM_CTR_INC_LANES] THEN
         ONCE_REWRITE_TAC[WORD_XOR_ASSOC] THEN
         REWRITE_TAC[aes256_encrypt] THEN REWRITE_TAC EL_15_128_CLAUSES THEN
         REWRITE_TAC[aes256_encrypt_round; aese; aesmc] THEN
         CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
         REWRITE_TAC[WORD_XOR_ASSOC] THEN CONV_TAC WORD_BLAST) (asl,w)) THEN NO_TAC) THEN
  (* out block-0 (out_p, bare ctr0): POSITIVE guard = aes256_encrypt AND NOT gcm_ctr_inc/ghash *)
  TRY((fun (asl,w) ->
        if not(can (find_term (fun t -> try fst(dest_const(fst(strip_comb t)))="aes256_encrypt" with _->false)) w)
           || can (find_term (fun t -> try fst(dest_const(fst(strip_comb t)))="gcm_ctr_inc" with _->false)) w
           || can (find_term (fun t -> try fst(dest_const(fst(strip_comb t)))="ghash_polyval_acc" with _->false)) w
        then failwith "not-blk0" else
        (AP_THM_TAC THEN AP_TERM_TAC THEN
         REWRITE_TAC[JOIN_IS_CTR0] THEN
         ONCE_REWRITE_TAC[WORD_XOR_ASSOC] THEN
         REWRITE_TAC[aes256_encrypt] THEN REWRITE_TAC EL_15_128_CLAUSES THEN
         REWRITE_TAC[aes256_encrypt_round; aese; aesmc] THEN
         CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
         REWRITE_TAC[WORD_XOR_ASSOC] THEN CONV_TAC WORD_BLAST) (asl,w)) THEN NO_TAC) THEN
  (* MAYCHANGE: discard non-maychange to nasl=1, then MATCH_MP the pre-computed WB4_FRAME_IMP.
     Safety net: if MATCH_MP fails (frame ordering mismatch), DUMP the exact accumulated frame. *)
  (fun (asl,w) -> Printf.printf "MC-ENTER len=%d nasl=%d\n%!" (String.length(string_of_term w)) (length asl); ALL_TAC (asl,w)) THEN
  DISCARD_ASSUMPTIONS_TAC (fun th -> not(maychange_term(concl th))) THEN
  (fun (asl,w) -> Printf.printf "MC-PRE-APPLY nasl=%d\n%!" (length asl);
     (List.iter (fun (_,th) -> if maychange_term(concl th) then
        Printf.printf "=== ACTUAL-FRAME:\n%s\n%!" (string_of_term (concl th))) asl);
     ALL_TAC (asl,w)) THEN
  FIRST_X_ASSUM(fun th -> ACCEPT_TAC(MATCH_MP WB4_FRAME_IMP th)) THEN
  (fun (asl,w) -> Printf.printf "MC-DONE-LEMMA\n%!"; ALL_TAC (asl,w)));;

(* ========================================================================= *)
(* FUSED->BAND bridge (STEP 4.2): derive mk_band_goal k from WB_FUSED_kBLOCK   *)
(* via ENSURES_PRECONDITION_THM (no re-simulation).  The fused POST + frame   *)
(* already equal the band's under cph_i := bytes_to_int128(SUB_LIST(16i,16)    *)
(* ibytes); only the PRE differs (whole-buffer read vs per-lane; htable_mem_dec*)
(* vs explicit slots), bridged by INPUT_BYTES_TO_BYTE128_LANES + htable unfold.*)
(* The fused hk/h2../side-hyps discharge via HK_LOW/HI_IS_KARA + karatsuba_mid *)
(* + BYTESWAP128_INVOLUTION.  Validated hyps=0 warm for k=1..4 (session 146).   *)
(* ========================================================================= *)

let HK_LOW_IS_KARA = prove
 (`!a b:64 word. word_subword (word_join a b:int128) (0,64):64 word = b`,
  CONV_TAC WORD_BLAST);;
let HK_HI_IS_KARA = prove
 (`!a b:64 word. word_subword (word_join a b:int128) (64,64):64 word = a`,
  CONV_TAC WORD_BLAST);;

(* h-power tower matching htable_mem_dec's internal lets (hb=byteswap128 h;
   h2=byteswap128(polyval_dot hb hb); h3,h4 one more dot each). *)
let s42_hb_tm = `byteswap128 (h:int128)`;;
let rec s42_hdot_raw j =
  if j <= 1 then s42_hb_tm
  else mk_comb(mk_comb(`polyval_dot:int128->int128->int128`, s42_hdot_raw (j-1)), s42_hb_tm);;
let s42_hpow j = mk_comb(`byteswap128:int128->int128`, s42_hdot_raw j);;
let s42_km t = mk_comb(`karatsuba_mid`, t);;
let s42_mk_join a b = mk_comb(mk_comb(`word_join:(64)word->(64)word->int128`, a), b);;
let s42_hk_tm  = s42_mk_join (s42_km (s42_hpow 2)) (s42_km `h:int128`);;
let s42_h3k_tm = s42_mk_join (s42_km (s42_hpow 4)) (s42_km (s42_hpow 3));;
let s42_cph_tm i = subst [mk_small_numeral(16*i),`nnn:num`]
  `bytes_to_int128 (SUB_LIST (nnn,16) (ibytes:byte list))`;;
let s42_ptr_args = [`pc:num`;`stackpointer:int64`;`out_p:int64`;`xi_p:int64`;`ivec_p:int64`;
                `in_p:int64`;`key_p:int64`;`htbl_p:int64`];;
let s42_key_args = [`xi:int128`;`ctr0:int128`;`k0:int128`;`k1:int128`;`k2:int128`;`k3:int128`;`k4:int128`;
                `k5:int128`;`k6:int128`;`k7:int128`;`k8:int128`;`k9:int128`;`k10:int128`;`k11:int128`;
                `k12:int128`;`k13:int128`;`k14:int128`;`h:int128`];;
let s42_fused_specl_args k =
  let cphs = map s42_cph_tm (0--(k-1)) in
  let htail =
    if k = 1 then [s42_hk_tm]
    else if k = 2 then [s42_hk_tm; s42_hpow 2]
    else if k = 3 then [s42_hk_tm; s42_hpow 2; s42_hpow 3; s42_h3k_tm]
    else [s42_hk_tm; s42_hpow 2; s42_hpow 3; s42_h3k_tm; s42_hpow 4] in
  s42_ptr_args @ cphs @ s42_key_args @ htail;;
let s42_lane_discharge k =
  EVERY(map (fun i ->
    let ni = mk_small_numeral i and nk = mk_small_numeral k in
    MP_TAC(SPECL [nk; `in_p:int64`; `ibytes:byte list`; `x:armstate`] INPUT_BYTES_TO_BYTE128_LANES) THEN
    REWRITE_TAC[ARITH_RULE(mk_eq(mk_binop `( * ):num->num->num` `16` nk, mk_small_numeral(16*k)))] THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[LE_REFL]; ALL_TAC] THEN
    DISCH_THEN(fun lth -> MP_TAC(SPEC ni lth)) THEN
    REWRITE_TAC[ARITH_RULE(mk_binop `(<):num->num->bool` ni nk)] THEN
    (if i = 0 then REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0]
     else REWRITE_TAC[ARITH_RULE(mk_eq(mk_binop `( * ):num->num->num` `16` ni, mk_small_numeral(16*i)))]) THEN
    DISCH_TAC)
    (0--(k-1))) THEN
  ASM_REWRITE_TAC[];;
let mk_band_from_fused k fused_thm =
  let fused_inst = SPECL (s42_fused_specl_args k) fused_thm in
  let fused_pre = el 1 (snd(strip_comb(snd(dest_imp(concl fused_inst))))) in
  prove(mk_band_goal k,
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN EXISTS_TAC fused_pre THEN CONJ_TAC THENL
     [GEN_TAC THEN REWRITE_TAC[htable_mem_dec] THEN
      CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN (subst [mk_small_numeral(16*k),`sss:num`]
        `SUB_LIST (0,sss) (ibytes:byte list) = ibytes`) ASSUME_TAC THENL
       [MATCH_MP_TAC SUB_LIST_LENGTH_IMPLIES THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      s42_lane_discharge k;
      MP_TAC fused_inst THEN ANTS_TAC THENL
       [REWRITE_TAC[GSYM WB_MC_LEN] THEN ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[HK_LOW_IS_KARA; HK_HI_IS_KARA; karatsuba_mid] THEN
        REWRITE_TAC[BYTESWAP128_INVOLUTION];
        DISCH_THEN ACCEPT_TAC]]);;

(* >>> STEP 4.2 FUSED ARC END (session 146) <<< *)

let wbn_backlegs =
  [WB_TAIL_GEN2_1; WB_TAIL_GEN2_2; WB_TAIL_GEN2_3; WB_TAIL_GEN2_4;
   WB_TAIL_GEN2_5; WB_TAIL_GEN2_6; WB_TAIL_GEN2_7; WB_TAIL_GEN2_8];;
let prove_band k =
  prove(mk_band_goal k,
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN EXISTS_TAC (fdbl_at k) THEN
    CONJ_TAC THENL
     [REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN SUBSUMED_MAYCHANGE_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC ENSURES_TRANS THEN EXISTS_TAC (q_at k) THEN CONJ_TAC THENL
     [MATCH_MP_TAC (wbf_at k) THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
      ALL_TAC] THEN
    MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN EXISTS_TAC (wbn_weak_q_at6 k) THEN
    CONJ_TAC THENL
     [GEN_TAC THEN REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC (el (k-1) wbn_backlegs) THEN
      ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV]);;

(* ---- the 8 recomposed bands (sim-free: reuse the WB_TAIL_GEN2_k back-leg) - *)
(* Bands 1..4 take the FUSED small-path (STEP 4.2): derived from the proven
   WB_FUSED_kBLOCK via mk_band_from_fused (above), NOT prove_band (which routes
   the front through WB_FRONT_BUF and now requires 5<=nblk, unprovable for k<5). *)
let AESV8_GCM_8X_DEC_256_BUF_1BLOCK = mk_band_from_fused 1 WB_FUSED_1BLOCK;;
let AESV8_GCM_8X_DEC_256_BUF_2BLOCK = mk_band_from_fused 2 WB_FUSED_2BLOCK;;
let AESV8_GCM_8X_DEC_256_BUF_3BLOCK = mk_band_from_fused 3 WB_FUSED_3BLOCK;;
let AESV8_GCM_8X_DEC_256_BUF_4BLOCK = mk_band_from_fused 4 WB_FUSED_4BLOCK;;
let AESV8_GCM_8X_DEC_256_BUF_5BLOCK = prove_band 5;;
let AESV8_GCM_8X_DEC_256_BUF_6BLOCK = prove_band 6;;
let AESV8_GCM_8X_DEC_256_BUF_7BLOCK = prove_band 7;;
let AESV8_GCM_8X_DEC_256_BUF_8BLOCK = prove_band 8;;
(* --- mid-load heap compaction: bound GC cost across this large single-file *)
(*     load (after the sim-free BUF series); mirrors the needs-boundary/ckpt Gc.compact). --- *)
Gc.compact();;


(* ------------------------------------------------------------------------- *)
(* The readable band theorems + the <=8-block dispatch theorem.               *)
(* Sim-free from the BUF band theorems: only the input/output presentations   *)
(* change, discharged by ARM-free bridges via ENSURES_PRE/POSTCONDITION_THM.  *)
(* The bridges come in two internal layers (neither is a named spec):         *)
(*   1. byte_list_at plumbing (BYTE_LIST_AT_TO_READ_BYTES /                   *)
(*      BYTE_LIST_AT_WHOLE_CTR / prove_wb_wrapper): per-block stores +        *)
(*      explicit ghash_polyval_acc -> gcm_dec_pt_bytes / gcm_dec_final_xi.    *)
(*   2. NIST vocabulary (htable_mem_8 / GCM_DEC_FINAL_XI_NIST /              *)
(*      nist_input_block): twisted-key POLYVAL objects -> SP 800-38D nist_ghash*)
(*      under the free NIST hash key H with byteswap128 h = ghash_twist H.    *)
(* The eight AESV8_GCM_8X_DEC_256_WB_{1..8}BLOCK statements below are written *)
(* out literally -- they ARE the specification document.                      *)
(* Together with AESV8_GCM_8X_DEC_256_GUARD (above) this is the complete   *)
(* contract of the whole-blocks binary: valid bit_len = 128*nblk (1<=nblk<=8) *)
(* -> DISPATCH; invalid bit_len -> GUARD (ret 0, no memory).                  *)
(* ------------------------------------------------------------------------- *)

(* ---- step 1: input bridge (byte_list_at -> whole-buffer bytes read) -------- *)
let BYTE_LIST_AT_TO_READ_BYTES = prove
 (`!bl (ptr:int64) (len:int64) s.
    byte_list_at bl ptr len s /\ LENGTH bl = val len
    ==> read (memory :> bytes (ptr, val len)) s = num_of_bytelist bl`,
  REPEAT GEN_TAC THEN REWRITE_TAC[byte_list_at] THEN STRIP_TAC THEN
  SUBGOAL_THEN `num_of_bytelist (bl:byte list) = num_of_bytelist (SUB_LIST (0, val (len:int64)) bl)` SUBST1_TAC THENL
   [AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC SUB_LIST_LENGTH_IMPLIES THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL [`val (len:int64)`; `ptr:int64`; `bl:byte list`; `s:armstate`] BYTE_LIST_TO_NUM_THM) THEN
  ASM_REWRITE_TAC[LE_REFL] THEN DISCH_THEN(fun th -> ASM_REWRITE_TAC[GSYM th]));;

(* ---- step 2: whole-blocks output bridge (per-block stores -> byte_list_at).
   Whole-blocks analogue of BYTE_LIST_AT_NBLOCK_CTR: specialize at tail=16 via
   AES_CTR_FULL_TAIL_BYTES_WHOLE; the all-ones mask makes outprev irrelevant
   (word 0 witness). *)
let BYTE_LIST_AT_WHOLE_CTR = prove
 (`!ctr0 pts keys n out_p (len:int64) s.
    1 <= n /\ n = LENGTH pts /\ val len = 16 * n /\
    (!j. j < n ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                   EL j (aes_ctr ctr0 pts keys))
    ==> byte_list_at (aes_ctr_bytes ctr0 pts keys) out_p len s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `aes_ctr_bytes ctr0 pts keys = aes_ctr_full_tail_bytes ctr0 pts keys (n - 1) 16` SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC AES_CTR_FULL_TAIL_BYTES_WHOLE THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC BYTE_LIST_AT_NBLOCK_CTR THEN
  EXISTS_TAC `word 0:int128` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;
    ARITH_TAC;
    ASM_ARITH_TAC;
    ASM_ARITH_TAC;
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    REWRITE_TAC[WORD_AND_ALLONES_128] THEN
    REWRITE_TAC[WORD_RULE `word_xor x (word_and (word 0) y) = x`] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]);;

(* ---- step 3: per-band EL facts builder (generalizes the hand AES_CTR_k_EL). *)
let build_aes_ctr_el k =
  let pts = map (fun i -> mk_var("pt"^string_of_int i,`:int128`)) (0--(k-1)) in
  let plist = mk_flist pts in
  let rec ctr j = if j = 0 then `ctr0:int128` else mk_comb(`gcm_ctr_inc`, ctr (j-1)) in
  let conj_of j =
    mk_eq(list_mk_comb(`EL:num->(int128)list->int128`,
            [mk_small_numeral j;
             list_mk_comb(`aes_ctr`, [`ctr0:int128`; plist; `keys:int128 list`])]),
          list_mk_comb(`word_xor:int128->int128->int128`,
            [el j pts;
             list_mk_comb(`aes256_encrypt`, [ctr j; `keys:int128 list`])])) in
  let goal = list_mk_conj (map conj_of (0--(k-1))) in
  let sucs = map (fun i -> num_CONV (mk_small_numeral i)) (1--(k-1)) in
  prove(goal,
    REWRITE_TAC[aes_ctr; aes_ctr_rec; aes_ctr_output_block; gcm_ctr_inc_iter] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC(sucs @ [EL; HD; TL]) THEN
    REWRITE_TAC[gcm_ctr_inc_iter] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC(sucs @ [gcm_ctr_inc_iter]) THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC(sucs @ [gcm_ctr_inc_iter]));;

(* ---- step 4: wrapper goal builder + prover ---------------------------------
   Wrapper = BUF band statement with (a) the input buffer read replaced by
   byte_list_at ibytes, (b) the postcondition per-block stores + explicit GHASH
   replaced by gcm_dec_pt_bytes / gcm_dec_final_xi over the whole buffer.
   Sim-free: PRE via BYTE_LIST_AT_TO_READ_BYTES, POST via BYTE_LIST_AT_WHOLE_CTR
   + the per-band EL facts; the spec unfolds via GCM_DEC_*_WHOLE_k. *)
let wb_keys_tm = `[k0:int128;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14]`;;
let mk_wb_wrapper_goal k =
  let g = mk_band_goal k in
  let vars, body = strip_forall g in
  let hyps, ens = dest_imp body in
  let frame = rand ens and post = rand(rator ens) and pre = rand(rator(rator ens)) in
  let n16 = mk_small_numeral(16*k) in
  let sv = `s:armstate` in
  let oldread = subst [n16,`nnn:num`]
    `read (memory :> bytes (in_p,nnn)) s = num_of_bytelist (ibytes:byte list)` in
  let newread = subst [n16,`nnn:num`]
    `byte_list_at (ibytes:byte list) in_p (word nnn) s` in
  let pre_body = snd(dest_abs pre) in
  let pre' = mk_abs(sv, list_mk_conj
    (map (fun c -> if c = oldread then newread else c) (conjuncts pre_body))) in
  let post_body = snd(dest_abs post) in
  let pcc = hd(conjuncts post_body) in
  let outpost = subst [n16,`nnn:num`; wb_keys_tm,`kl:int128 list`]
    `byte_list_at (gcm_dec_pt_bytes nnn ibytes ctr0 (kl:int128 list)) out_p (word nnn) s` in
  let xipost = subst [n16,`nnn:num`]
    `read (memory :> bytes128 xi_p) s = gcm_dec_final_xi nnn ibytes xi h` in
  (* ivec M2: carry the band's counter write-back conjunct through
     the wrapper unchanged (spine form; not part of the byte-list vocab lift). *)
  let ivecpost = mk_ivec_conj k in
  let post' = mk_abs(sv, list_mk_conj [pcc; outpost; xipost; ivecpost]) in
  list_mk_forall(vars,
    mk_imp(hyps, list_mk_comb(rator(rator(rator ens)), [pre'; post'; frame])));;

let ghash_wholes = [GCM_DEC_GHASH_BLOCKS_WHOLE_1;GCM_DEC_GHASH_BLOCKS_WHOLE_2;
                    GCM_DEC_GHASH_BLOCKS_WHOLE_3;GCM_DEC_GHASH_BLOCKS_WHOLE_4;
                    GCM_DEC_GHASH_BLOCKS_WHOLE_5;GCM_DEC_GHASH_BLOCKS_WHOLE_6;
                    GCM_DEC_GHASH_BLOCKS_WHOLE_7;GCM_DEC_GHASH_BLOCKS_WHOLE_8];;
let pt_wholes = [GCM_DEC_PT_BYTES_WHOLE_1;GCM_DEC_PT_BYTES_WHOLE_2;
                 GCM_DEC_PT_BYTES_WHOLE_3;GCM_DEC_PT_BYTES_WHOLE_4;
                 GCM_DEC_PT_BYTES_WHOLE_5;GCM_DEC_PT_BYTES_WHOLE_6;
                 GCM_DEC_PT_BYTES_WHOLE_7;GCM_DEC_PT_BYTES_WHOLE_8];;
let prove_wb_wrapper k buf_thm =
  let n16 = mk_small_numeral(16*k) in
  let band = mk_band_goal k in
  let _, bbody = strip_forall band in
  let _, bens = dest_imp bbody in
  let pre_buf = rand(rator(rator bens)) and post_buf = rand(rator bens) in
  let el_facts = build_aes_ctr_el k in
  let inbridge = CONV_RULE (ONCE_DEPTH_CONV WORD_REDUCE_CONV)
    (SPECL [`ibytes:byte list`;`in_p:int64`; mk_comb(`word:num->int64`,n16); `s:armstate`]
       BYTE_LIST_AT_TO_READ_BYTES) in
  let jsplit = ARITH_RULE
    (mk_eq(subst [mk_small_numeral k,`kkk:num`] `j < kkk:num`,
           list_mk_disj (map (fun i -> mk_eq(`j:num`, mk_small_numeral i)) (0--(k-1))))) in
  prove(mk_wb_wrapper_goal k,
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    REWRITE_TAC[gcm_dec_final_xi; el (k-1) ghash_wholes; el (k-1) pt_wholes; MAP] THEN
    MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN
    EXISTS_TAC pre_buf THEN
    CONJ_TAC THENL
     [X_GEN_TAC `s:armstate` THEN BETA_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      MP_TAC inbridge THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN
      EXISTS_TAC post_buf THEN
      CONJ_TAC THENL
       [X_GEN_TAC `s:armstate` THEN BETA_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC BYTE_LIST_AT_WHOLE_CTR THEN
        EXISTS_TAC (mk_small_numeral k) THEN
        REPEAT CONJ_TAC THENL
         [ARITH_TAC;
          REWRITE_TAC[LENGTH] THEN ARITH_TAC;
          CONV_TAC WORD_REDUCE_CONV THEN ARITH_TAC;
          X_GEN_TAC `j:num` THEN REWRITE_TAC[jsplit] THEN
          STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
          CONV_TAC NUM_REDUCE_CONV THEN
          REWRITE_TAC[WORD_ADD_0; el_facts] THEN ASM_REWRITE_TAC[el_facts]];
        MATCH_MP_TAC buf_thm THEN ASM_REWRITE_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* NIST-vocabulary bridge layer (the x4-kernel statement shape).              *)
(*  - htable_mem_8: htable_mem_4-style named memory predicate over h_power    *)
(*    indexing, for the 12-slot aws-lc htable layout (packed karatsuba mids). *)
(*  - GCM_DEC_FINAL_XI_NIST: gcm_dec_final_xi = byte-reversed nist_ghash      *)
(*    under byteswap128 h = ghash_twist H (Gueron Prop 1 via                  *)
(*    NIST_GHASH_IS_POLYVAL from common/ghash_nist_bridge.ml).                *)
(*  - nist_input_block: the NIST (big-endian) view of input block i, with the *)
(*    LIST_OF_SEQ_NIST_INPUT bridges to gcm_dec_ghash_blocks.                 *)
(*  - wordlist_from_memory key condensation: KEY_READS_FROM_WORDLIST +        *)
(*    RK_ETA_15 relate the abstract rk list to the 15 bytes128 key reads.     *)
(* ------------------------------------------------------------------------- *)

(* ---- karatsuba_mid ignores the byteswap of its argument ------------------- *)
let KARATSUBA_MID_BYTESWAP = prove
 (`!x:int128. karatsuba_mid (byteswap128 x) = karatsuba_mid x`,
  GEN_TAC THEN REWRITE_TAC[karatsuba_mid; byteswap128] THEN
  CONV_TAC WORD_BLAST);;

(* ---- h_power 0..7 unfolded to the explicit left-nested dot chains --------- *)
let H_POWER_UNFOLD_7 = prove
 (`h_power (hb:int128) 0 = hb /\
   h_power hb 1 = polyval_dot hb hb /\
   h_power hb 2 = polyval_dot (polyval_dot hb hb) hb /\
   h_power hb 3 = polyval_dot (polyval_dot (polyval_dot hb hb) hb) hb /\
   h_power hb 4 = polyval_dot (polyval_dot (polyval_dot (polyval_dot hb hb) hb) hb) hb /\
   h_power hb 5 = polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot hb hb) hb) hb) hb) hb /\
   h_power hb 6 = polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot hb hb) hb) hb) hb) hb) hb /\
   h_power hb 7 = polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot (polyval_dot hb hb) hb) hb) hb) hb) hb) hb`,
  REWRITE_TAC[num_CONV `7`; num_CONV `6`; num_CONV `5`; num_CONV `4`;
              num_CONV `3`; num_CONV `2`; num_CONV `1`; h_power]);;

(* ---- htable_mem_dec in h_power form (kills the nested let-towers) --------- *)
let HTABLE_MEM_DEC_H_POWER = prove
 (`!(h:int128) (ptr:int64) (s:armstate).
     htable_mem_dec h ptr s <=>
     read (memory :> bytes128 ptr) s = byteswap128 (h_power (byteswap128 h) 0) /\
     read (memory :> bytes128 (word_add ptr (word 16))) s =
       word_join (karatsuba_mid (h_power (byteswap128 h) 1))
                 (karatsuba_mid (h_power (byteswap128 h) 0)) /\
     read (memory :> bytes128 (word_add ptr (word 32))) s = byteswap128 (h_power (byteswap128 h) 1) /\
     read (memory :> bytes128 (word_add ptr (word 48))) s = byteswap128 (h_power (byteswap128 h) 2) /\
     read (memory :> bytes128 (word_add ptr (word 64))) s =
       word_join (karatsuba_mid (h_power (byteswap128 h) 3))
                 (karatsuba_mid (h_power (byteswap128 h) 2)) /\
     read (memory :> bytes128 (word_add ptr (word 80))) s = byteswap128 (h_power (byteswap128 h) 3) /\
     read (memory :> bytes128 (word_add ptr (word 96))) s = byteswap128 (h_power (byteswap128 h) 4) /\
     read (memory :> bytes128 (word_add ptr (word 112))) s =
       word_join (karatsuba_mid (h_power (byteswap128 h) 5))
                 (karatsuba_mid (h_power (byteswap128 h) 4)) /\
     read (memory :> bytes128 (word_add ptr (word 128))) s = byteswap128 (h_power (byteswap128 h) 5) /\
     read (memory :> bytes128 (word_add ptr (word 144))) s = byteswap128 (h_power (byteswap128 h) 6) /\
     read (memory :> bytes128 (word_add ptr (word 160))) s =
       word_join (karatsuba_mid (h_power (byteswap128 h) 7))
                 (karatsuba_mid (h_power (byteswap128 h) 6)) /\
     read (memory :> bytes128 (word_add ptr (word 176))) s = byteswap128 (h_power (byteswap128 h) 7)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[htable_mem_dec] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[H_POWER_UNFOLD_7; KARATSUBA_MID_BYTESWAP; BYTESWAP128_INVOLUTION]);;

(* ---- the named htable predicate over the abstract key hk ----------------- *)
(* hk is the POLYVAL-side key (byteswap128 of the memory h slot); with
   hk = ghash_twist H this is the exact analogue of the x4 kernels'
   htable_mem_4 (ghash_twist ...) hypothesis, extended to 8 powers /
   12 slots (aws-lc layout with packed karatsuba mids). *)
let htable_mem_8 = new_definition
 `htable_mem_8 (hk:int128) (ptr:int64) (s:armstate) <=>
    read (memory :> bytes128 ptr) s = byteswap128 (h_power hk 0) /\
    read (memory :> bytes128 (word_add ptr (word 16))) s =
      word_join (karatsuba_mid (h_power hk 1)) (karatsuba_mid (h_power hk 0)) /\
    read (memory :> bytes128 (word_add ptr (word 32))) s = byteswap128 (h_power hk 1) /\
    read (memory :> bytes128 (word_add ptr (word 48))) s = byteswap128 (h_power hk 2) /\
    read (memory :> bytes128 (word_add ptr (word 64))) s =
      word_join (karatsuba_mid (h_power hk 3)) (karatsuba_mid (h_power hk 2)) /\
    read (memory :> bytes128 (word_add ptr (word 80))) s = byteswap128 (h_power hk 3) /\
    read (memory :> bytes128 (word_add ptr (word 96))) s = byteswap128 (h_power hk 4) /\
    read (memory :> bytes128 (word_add ptr (word 112))) s =
      word_join (karatsuba_mid (h_power hk 5)) (karatsuba_mid (h_power hk 4)) /\
    read (memory :> bytes128 (word_add ptr (word 128))) s = byteswap128 (h_power hk 5) /\
    read (memory :> bytes128 (word_add ptr (word 144))) s = byteswap128 (h_power hk 6) /\
    read (memory :> bytes128 (word_add ptr (word 160))) s =
      word_join (karatsuba_mid (h_power hk 7)) (karatsuba_mid (h_power hk 6)) /\
    read (memory :> bytes128 (word_add ptr (word 176))) s = byteswap128 (h_power hk 7)`;;

let HTABLE_MEM_DEC_IS_HTABLE_MEM_8 = prove
 (`!(h:int128) (ptr:int64) (s:armstate).
     htable_mem_dec h ptr s <=> htable_mem_8 (byteswap128 h) ptr s`,
  REWRITE_TAC[HTABLE_MEM_DEC_H_POWER; htable_mem_8]);;

(* ---- word_bytereverse = word_reversefields 8 at :128 ----------------------- *)
let BREV_RF8_128 = prove
 (`word_bytereverse (x:int128) = word_reversefields 8 x`,
  REWRITE_TAC[REWRITE_RULE[FUN_EQ_THM] WORD_BYTEREVERSE_REVERSEFIELDS]);;

let BREV_RF8_INV_128 = prove
 (`!x:int128. word_bytereverse (word_reversefields 8 x) = x`,
  REWRITE_TAC[GSYM BREV_RF8_128; WORD_BYTEREVERSE_BYTEREVERSE]);;

(* ---- the tag spec in nist_ghash vocabulary -------------------------------- *)
(* Our band statements quantify the raw htable h slot; the x4 kernels quantify the
   NIST key H with the twist applied in the hypothesis.  The two are related
   by byteswap128 h = ghash_twist H, under which gcm_dec_final_xi IS a
   byte-reversed nist_ghash (Gueron Prop 1 via NIST_GHASH_IS_POLYVAL). *)
let GCM_DEC_FINAL_XI_NIST = prove
 (`!(H:int128) (h:int128) len x xi.
     byteswap128 h = ghash_twist H
     ==> gcm_dec_final_xi len x xi h =
         word_bytereverse
           (nist_ghash H (word_bytereverse xi)
              (MAP word_bytereverse (gcm_dec_ghash_blocks len x)))`,
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[gcm_dec_final_xi; NIST_GHASH_IS_POLYVAL]);;

(* ---- the NIST (big-endian) view of input block i --------------------------- *)
let nist_input_block = new_definition
 `nist_input_block (x:byte list) (i:num) : int128 =
    word_reversefields 8 (bytes_to_int128 (SUB_LIST (16 * i, 16) x))`;;

(* list_of_seq (nist_input_block x) N = MAP word_bytereverse (gcm_dec_ghash_blocks (16*N) x) *)
let build_list_of_seq_nist n =
  let goal = list_mk_forall([`x:byte list`],
    mk_eq(list_mk_comb(`list_of_seq:(num->int128)->num->int128 list`,
            [mk_comb(`nist_input_block`,`x:byte list`); mk_small_numeral n]),
          mk_comb(`MAP (word_bytereverse:int128->int128)`,
            list_mk_comb(`gcm_dec_ghash_blocks`, [mk_small_numeral(16*n);`x:byte list`])))) in
  prove(goal,
    GEN_TAC THEN REWRITE_TAC[el (n-1) ghash_wholes; MAP] THEN
    REWRITE_TAC(map num_CONV (map mk_small_numeral (rev(1--n)))) THEN
    REWRITE_TAC[LIST_OF_SEQ; o_DEF; nist_input_block; BREV_RF8_128] THEN
    CONV_TAC NUM_REDUCE_CONV);;
let LIST_OF_SEQ_NIST_INPUT = map build_list_of_seq_nist (1--8);;

(* ---- key condensation: abstract rk list <-> the 15 bytes128 reads ---------- *)
let RK_ETA_15 = prove
 (`!rk:int128 list. LENGTH rk = 15
     ==> rk = [EL 0 rk; EL 1 rk; EL 2 rk; EL 3 rk; EL 4 rk; EL 5 rk; EL 6 rk;
               EL 7 rk; EL 8 rk; EL 9 rk; EL 10 rk; EL 11 rk; EL 12 rk;
               EL 13 rk; EL 14 rk]`,
  GEN_TAC THEN REWRITE_TAC[LENGTH_EQ_LIST_OF_SEQ] THEN
  DISCH_THEN(fun th -> GEN_REWRITE_TAC LAND_CONV [th]) THEN
  REWRITE_TAC(map num_CONV (map mk_small_numeral (rev(1--15)))) THEN
  REWRITE_TAC[LIST_OF_SEQ; o_DEF] THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV);;

let KEY_READS_FROM_WORDLIST = prove
 (`!(key_p:int64) (rk:int128 list) s.
     wordlist_from_memory (key_p,15) s = rk
     ==> read (memory :> bytes128 key_p) s = EL 0 rk /\
         read (memory :> bytes128 (word_add key_p (word 16))) s = EL 1 rk /\
         read (memory :> bytes128 (word_add key_p (word 32))) s = EL 2 rk /\
         read (memory :> bytes128 (word_add key_p (word 48))) s = EL 3 rk /\
         read (memory :> bytes128 (word_add key_p (word 64))) s = EL 4 rk /\
         read (memory :> bytes128 (word_add key_p (word 80))) s = EL 5 rk /\
         read (memory :> bytes128 (word_add key_p (word 96))) s = EL 6 rk /\
         read (memory :> bytes128 (word_add key_p (word 112))) s = EL 7 rk /\
         read (memory :> bytes128 (word_add key_p (word 128))) s = EL 8 rk /\
         read (memory :> bytes128 (word_add key_p (word 144))) s = EL 9 rk /\
         read (memory :> bytes128 (word_add key_p (word 160))) s = EL 10 rk /\
         read (memory :> bytes128 (word_add key_p (word 176))) s = EL 11 rk /\
         read (memory :> bytes128 (word_add key_p (word 192))) s = EL 12 rk /\
         read (memory :> bytes128 (word_add key_p (word 208))) s = EL 13 rk /\
         read (memory :> bytes128 (word_add key_p (word 224))) s = EL 14 rk`,
  REPEAT GEN_TAC THEN
  CONV_TAC(LAND_CONV(LAND_CONV WORDLIST_FROM_MEMORY_CONV)) THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC(map num_CONV (map mk_small_numeral (rev(1--14)))) THEN
  REWRITE_TAC[EL; HD; TL]);;

(* ---- the readable-band prover ----------------------------------------------
   For band k: (1) prove_wb_wrapper k buf_thm gives the internal byte-list
   wrapper over _BUF_kBLOCK; (2) instantiate it at ki := EL i rk,
   h := byteswap128 (ghash_twist H), xi := word_reversefields 8 tag0 and
   rewrite into NIST vocabulary; (3) close the literal statement:
   ALLPAIRS/PAIRWISE/ALL unfold + NONOVERLAPPING_SYM hit the wrapper's
   pairwise hypotheses, RK_ETA_15 folds the EL-list back to rk, and
   ENSURES_PRECONDITION_THM + KEY_READS_FROM_WORDLIST bridge the key reads. *)
let bsw_inv = SPEC `ghash_twist H` BYTESWAP128_INVOLUTION;;
let mk_wrapper_nist k wrapper_thm =
  let winst = SPECL ([`pc:num`;`stackpointer:int64`;`out_p:int64`;`xi_p:int64`;`ivec_p:int64`;
                      `in_p:int64`;`key_p:int64`;`htbl_p:int64`;`ibytes:byte list`;
                      `word_reversefields 8 (tag0:int128)`;`ctr0:int128`] @
                     map (fun i -> list_mk_comb(`EL:num->(int128)list->int128`,
                            [mk_small_numeral i; `rk:int128 list`])) (0--14) @
                     [`byteswap128 (ghash_twist H)`]) wrapper_thm in
  let xi_rw = MP (SPECL [`H:int128`; `byteswap128 (ghash_twist H)`;
                         mk_small_numeral(16*k); `ibytes:byte list`;
                         `word_reversefields 8 (tag0:int128)`] GCM_DEC_FINAL_XI_NIST)
                 bsw_inv in
  REWRITE_RULE[HTABLE_MEM_DEC_IS_HTABLE_MEM_8; BYTESWAP128_INVOLUTION; xi_rw;
               GSYM (el (k-1) LIST_OF_SEQ_NIST_INPUT); BREV_RF8_INV_128; BREV_RF8_128] winst;;

let wb_rk15_tm = `[EL 0 rk; EL 1 rk; EL 2 rk; EL 3 rk; EL 4 rk; EL 5 rk; EL 6 rk;
                   EL 7 rk; EL 8 rk; EL 9 rk; EL 10 rk; EL 11 rk; EL 12 rk;
                   EL 13 rk; EL 14 rk]:int128 list`;;
let WB_READABLE_TAC k buf_thm =
  let wn = mk_wrapper_nist k (prove_wb_wrapper k buf_thm) in
  REPEAT GEN_TAC THEN REWRITE_TAC[ALLPAIRS;PAIRWISE;ALL] THEN STRIP_TAC THEN
  MP_TAC wn THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
    ONCE_REWRITE_TAC[NONOVERLAPPING_SYM] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN (mk_eq(wb_rk15_tm,`rk:int128 list`)) SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC RK_ETA_15 THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_TAC THEN MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN
  FIRST_X_ASSUM(fun th ->
    EXISTS_TAC (rand(rator(rator(concl th)))) THEN MP_TAC th) THEN
  DISCH_TAC THEN CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[]] THEN
  X_GEN_TAC `s:armstate` THEN REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(fun th ->
    try MP_TAC(MATCH_MP KEY_READS_FROM_WORDLIST th)
    with Failure _ -> failwith "no wordlist assumption") THEN
  SIMP_TAC[];;

(* ------------------------------------------------------------------------- *)
(* THE eight readable band theorems (literal statements; the spec document).  *)
(* Reading guide for N blocks: under the standard ABI/nonoverlapping side     *)
(* conditions, decrypting N whole blocks writes to out_p the CTR keystream    *)
(* XORed onto the input bytes (gcm_dec_pt_bytes), and replaces the tag at     *)
(* xi_p with the standard SP 800-38D GHASH of the N raw ciphertext blocks     *)
(* folded onto tag0 under the NIST hash key H (both tag values stored         *)
(* little-endian-reversed, as the aws-lc caller keeps them).                  *)
(* ------------------------------------------------------------------------- *)

let AESV8_GCM_8X_DEC_256_1BLOCK = prove
 (`!pc stackpointer in_p out_p xi_p ivec_p key_p htbl_p
    ibytes (rk:int128 list) (H:int128) tag0 ctr0.
     LENGTH ibytes = 16 /\ LENGTH rk = 15 /\
     aligned 16 stackpointer /\
     ALLPAIRS nonoverlapping
       [out_p,16; xi_p,16; ivec_p,16]
       [word pc, LENGTH aesv8_gcm_8x_dec_256_wb_mc; in_p,16; key_p,240; htbl_p,192; stackpointer,80] /\
     PAIRWISE nonoverlapping [out_p,16; xi_p,16; ivec_p,16] /\
     ALL (nonoverlapping (stackpointer,80))
       [word pc, LENGTH aesv8_gcm_8x_dec_256_wb_mc; in_p,16; key_p,240; htbl_p,192]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) aesv8_gcm_8x_dec_256_wb_mc /\
               read PC s = word (pc + 0x20) /\
               read SP s = stackpointer /\
               C_ARGUMENTS [in_p; word 128; out_p; xi_p; ivec_p; key_p; htbl_p] s /\
               byte_list_at ibytes in_p (word 16) s /\
               read (memory :> bytes128 xi_p) s = word_reversefields 8 tag0 /\
               read (memory :> bytes128 ivec_p) s = ctr0 /\
               wordlist_from_memory (key_p,15) s = rk /\
               htable_mem_8 (ghash_twist H) htbl_p s)
          (\s. read PC s = word (pc + 4560) /\
               byte_list_at (gcm_dec_pt_bytes 16 ibytes ctr0 rk) out_p (word 16) s /\
               read (memory :> bytes128 xi_p) s =
               word_reversefields 8
                 (nist_ghash H tag0 (list_of_seq (nist_input_block ibytes) 1))
               /\
               read (memory :> bytes128 ivec_p) s = gcm_ctr_inc_iter 1 ctr0)
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(out_p,16); memory :> bytes(xi_p,16);
                      memory :> bytes(ivec_p,16);
                      memory :> bytes(word_add stackpointer (word 64),16)] ,,
           MAYCHANGE [Q0;Q1;Q2;Q3;Q4;Q5;Q6;Q7;Q8;Q9;Q10;Q11;Q12;Q13;Q14;Q15;
                      Q16;Q17;Q18;Q19;Q20;Q21;Q22;Q23;Q24;Q25;Q26;Q27;Q28;Q29;Q30;Q31])`,
  WB_READABLE_TAC 1 AESV8_GCM_8X_DEC_256_BUF_1BLOCK);;

let AESV8_GCM_8X_DEC_256_2BLOCK = prove
 (`!pc stackpointer in_p out_p xi_p ivec_p key_p htbl_p
    ibytes (rk:int128 list) (H:int128) tag0 ctr0.
     LENGTH ibytes = 32 /\ LENGTH rk = 15 /\
     aligned 16 stackpointer /\
     ALLPAIRS nonoverlapping
       [out_p,32; xi_p,16; ivec_p,16]
       [word pc, LENGTH aesv8_gcm_8x_dec_256_wb_mc; in_p,32; key_p,240; htbl_p,192; stackpointer,80] /\
     PAIRWISE nonoverlapping [out_p,32; xi_p,16; ivec_p,16] /\
     ALL (nonoverlapping (stackpointer,80))
       [word pc, LENGTH aesv8_gcm_8x_dec_256_wb_mc; in_p,32; key_p,240; htbl_p,192]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) aesv8_gcm_8x_dec_256_wb_mc /\
               read PC s = word (pc + 0x20) /\
               read SP s = stackpointer /\
               C_ARGUMENTS [in_p; word 256; out_p; xi_p; ivec_p; key_p; htbl_p] s /\
               byte_list_at ibytes in_p (word 32) s /\
               read (memory :> bytes128 xi_p) s = word_reversefields 8 tag0 /\
               read (memory :> bytes128 ivec_p) s = ctr0 /\
               wordlist_from_memory (key_p,15) s = rk /\
               htable_mem_8 (ghash_twist H) htbl_p s)
          (\s. read PC s = word (pc + 4560) /\
               byte_list_at (gcm_dec_pt_bytes 32 ibytes ctr0 rk) out_p (word 32) s /\
               read (memory :> bytes128 xi_p) s =
               word_reversefields 8
                 (nist_ghash H tag0 (list_of_seq (nist_input_block ibytes) 2))
               /\
               read (memory :> bytes128 ivec_p) s = gcm_ctr_inc_iter 2 ctr0)
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(out_p,32); memory :> bytes(xi_p,16);
                      memory :> bytes(ivec_p,16);
                      memory :> bytes(word_add stackpointer (word 64),16)] ,,
           MAYCHANGE [Q0;Q1;Q2;Q3;Q4;Q5;Q6;Q7;Q8;Q9;Q10;Q11;Q12;Q13;Q14;Q15;
                      Q16;Q17;Q18;Q19;Q20;Q21;Q22;Q23;Q24;Q25;Q26;Q27;Q28;Q29;Q30;Q31])`,
  WB_READABLE_TAC 2 AESV8_GCM_8X_DEC_256_BUF_2BLOCK);;

let AESV8_GCM_8X_DEC_256_3BLOCK = prove
 (`!pc stackpointer in_p out_p xi_p ivec_p key_p htbl_p
    ibytes (rk:int128 list) (H:int128) tag0 ctr0.
     LENGTH ibytes = 48 /\ LENGTH rk = 15 /\
     aligned 16 stackpointer /\
     ALLPAIRS nonoverlapping
       [out_p,48; xi_p,16; ivec_p,16]
       [word pc, LENGTH aesv8_gcm_8x_dec_256_wb_mc; in_p,48; key_p,240; htbl_p,192; stackpointer,80] /\
     PAIRWISE nonoverlapping [out_p,48; xi_p,16; ivec_p,16] /\
     ALL (nonoverlapping (stackpointer,80))
       [word pc, LENGTH aesv8_gcm_8x_dec_256_wb_mc; in_p,48; key_p,240; htbl_p,192]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) aesv8_gcm_8x_dec_256_wb_mc /\
               read PC s = word (pc + 0x20) /\
               read SP s = stackpointer /\
               C_ARGUMENTS [in_p; word 384; out_p; xi_p; ivec_p; key_p; htbl_p] s /\
               byte_list_at ibytes in_p (word 48) s /\
               read (memory :> bytes128 xi_p) s = word_reversefields 8 tag0 /\
               read (memory :> bytes128 ivec_p) s = ctr0 /\
               wordlist_from_memory (key_p,15) s = rk /\
               htable_mem_8 (ghash_twist H) htbl_p s)
          (\s. read PC s = word (pc + 4560) /\
               byte_list_at (gcm_dec_pt_bytes 48 ibytes ctr0 rk) out_p (word 48) s /\
               read (memory :> bytes128 xi_p) s =
               word_reversefields 8
                 (nist_ghash H tag0 (list_of_seq (nist_input_block ibytes) 3))
               /\
               read (memory :> bytes128 ivec_p) s = gcm_ctr_inc_iter 3 ctr0)
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(out_p,48); memory :> bytes(xi_p,16);
                      memory :> bytes(ivec_p,16);
                      memory :> bytes(word_add stackpointer (word 64),16)] ,,
           MAYCHANGE [Q0;Q1;Q2;Q3;Q4;Q5;Q6;Q7;Q8;Q9;Q10;Q11;Q12;Q13;Q14;Q15;
                      Q16;Q17;Q18;Q19;Q20;Q21;Q22;Q23;Q24;Q25;Q26;Q27;Q28;Q29;Q30;Q31])`,
  WB_READABLE_TAC 3 AESV8_GCM_8X_DEC_256_BUF_3BLOCK);;

let AESV8_GCM_8X_DEC_256_4BLOCK = prove
 (`!pc stackpointer in_p out_p xi_p ivec_p key_p htbl_p
    ibytes (rk:int128 list) (H:int128) tag0 ctr0.
     LENGTH ibytes = 64 /\ LENGTH rk = 15 /\
     aligned 16 stackpointer /\
     ALLPAIRS nonoverlapping
       [out_p,64; xi_p,16; ivec_p,16]
       [word pc, LENGTH aesv8_gcm_8x_dec_256_wb_mc; in_p,64; key_p,240; htbl_p,192; stackpointer,80] /\
     PAIRWISE nonoverlapping [out_p,64; xi_p,16; ivec_p,16] /\
     ALL (nonoverlapping (stackpointer,80))
       [word pc, LENGTH aesv8_gcm_8x_dec_256_wb_mc; in_p,64; key_p,240; htbl_p,192]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) aesv8_gcm_8x_dec_256_wb_mc /\
               read PC s = word (pc + 0x20) /\
               read SP s = stackpointer /\
               C_ARGUMENTS [in_p; word 512; out_p; xi_p; ivec_p; key_p; htbl_p] s /\
               byte_list_at ibytes in_p (word 64) s /\
               read (memory :> bytes128 xi_p) s = word_reversefields 8 tag0 /\
               read (memory :> bytes128 ivec_p) s = ctr0 /\
               wordlist_from_memory (key_p,15) s = rk /\
               htable_mem_8 (ghash_twist H) htbl_p s)
          (\s. read PC s = word (pc + 4560) /\
               byte_list_at (gcm_dec_pt_bytes 64 ibytes ctr0 rk) out_p (word 64) s /\
               read (memory :> bytes128 xi_p) s =
               word_reversefields 8
                 (nist_ghash H tag0 (list_of_seq (nist_input_block ibytes) 4))
               /\
               read (memory :> bytes128 ivec_p) s = gcm_ctr_inc_iter 4 ctr0)
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(out_p,64); memory :> bytes(xi_p,16);
                      memory :> bytes(ivec_p,16);
                      memory :> bytes(word_add stackpointer (word 64),16)] ,,
           MAYCHANGE [Q0;Q1;Q2;Q3;Q4;Q5;Q6;Q7;Q8;Q9;Q10;Q11;Q12;Q13;Q14;Q15;
                      Q16;Q17;Q18;Q19;Q20;Q21;Q22;Q23;Q24;Q25;Q26;Q27;Q28;Q29;Q30;Q31])`,
  WB_READABLE_TAC 4 AESV8_GCM_8X_DEC_256_BUF_4BLOCK);;

let AESV8_GCM_8X_DEC_256_5BLOCK = prove
 (`!pc stackpointer in_p out_p xi_p ivec_p key_p htbl_p
    ibytes (rk:int128 list) (H:int128) tag0 ctr0.
     LENGTH ibytes = 80 /\ LENGTH rk = 15 /\
     aligned 16 stackpointer /\
     ALLPAIRS nonoverlapping
       [out_p,80; xi_p,16; ivec_p,16]
       [word pc, LENGTH aesv8_gcm_8x_dec_256_wb_mc; in_p,80; key_p,240; htbl_p,192; stackpointer,80] /\
     PAIRWISE nonoverlapping [out_p,80; xi_p,16; ivec_p,16] /\
     ALL (nonoverlapping (stackpointer,80))
       [word pc, LENGTH aesv8_gcm_8x_dec_256_wb_mc; in_p,80; key_p,240; htbl_p,192]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) aesv8_gcm_8x_dec_256_wb_mc /\
               read PC s = word (pc + 0x20) /\
               read SP s = stackpointer /\
               C_ARGUMENTS [in_p; word 640; out_p; xi_p; ivec_p; key_p; htbl_p] s /\
               byte_list_at ibytes in_p (word 80) s /\
               read (memory :> bytes128 xi_p) s = word_reversefields 8 tag0 /\
               read (memory :> bytes128 ivec_p) s = ctr0 /\
               wordlist_from_memory (key_p,15) s = rk /\
               htable_mem_8 (ghash_twist H) htbl_p s)
          (\s. read PC s = word (pc + 4560) /\
               byte_list_at (gcm_dec_pt_bytes 80 ibytes ctr0 rk) out_p (word 80) s /\
               read (memory :> bytes128 xi_p) s =
               word_reversefields 8
                 (nist_ghash H tag0 (list_of_seq (nist_input_block ibytes) 5))
               /\
               read (memory :> bytes128 ivec_p) s = gcm_ctr_inc_iter 5 ctr0)
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(out_p,80); memory :> bytes(xi_p,16);
                      memory :> bytes(ivec_p,16);
                      memory :> bytes(word_add stackpointer (word 64),16)] ,,
           MAYCHANGE [Q0;Q1;Q2;Q3;Q4;Q5;Q6;Q7;Q8;Q9;Q10;Q11;Q12;Q13;Q14;Q15;
                      Q16;Q17;Q18;Q19;Q20;Q21;Q22;Q23;Q24;Q25;Q26;Q27;Q28;Q29;Q30;Q31])`,
  WB_READABLE_TAC 5 AESV8_GCM_8X_DEC_256_BUF_5BLOCK);;

let AESV8_GCM_8X_DEC_256_6BLOCK = prove
 (`!pc stackpointer in_p out_p xi_p ivec_p key_p htbl_p
    ibytes (rk:int128 list) (H:int128) tag0 ctr0.
     LENGTH ibytes = 96 /\ LENGTH rk = 15 /\
     aligned 16 stackpointer /\
     ALLPAIRS nonoverlapping
       [out_p,96; xi_p,16; ivec_p,16]
       [word pc, LENGTH aesv8_gcm_8x_dec_256_wb_mc; in_p,96; key_p,240; htbl_p,192; stackpointer,80] /\
     PAIRWISE nonoverlapping [out_p,96; xi_p,16; ivec_p,16] /\
     ALL (nonoverlapping (stackpointer,80))
       [word pc, LENGTH aesv8_gcm_8x_dec_256_wb_mc; in_p,96; key_p,240; htbl_p,192]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) aesv8_gcm_8x_dec_256_wb_mc /\
               read PC s = word (pc + 0x20) /\
               read SP s = stackpointer /\
               C_ARGUMENTS [in_p; word 768; out_p; xi_p; ivec_p; key_p; htbl_p] s /\
               byte_list_at ibytes in_p (word 96) s /\
               read (memory :> bytes128 xi_p) s = word_reversefields 8 tag0 /\
               read (memory :> bytes128 ivec_p) s = ctr0 /\
               wordlist_from_memory (key_p,15) s = rk /\
               htable_mem_8 (ghash_twist H) htbl_p s)
          (\s. read PC s = word (pc + 4560) /\
               byte_list_at (gcm_dec_pt_bytes 96 ibytes ctr0 rk) out_p (word 96) s /\
               read (memory :> bytes128 xi_p) s =
               word_reversefields 8
                 (nist_ghash H tag0 (list_of_seq (nist_input_block ibytes) 6))
               /\
               read (memory :> bytes128 ivec_p) s = gcm_ctr_inc_iter 6 ctr0)
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(out_p,96); memory :> bytes(xi_p,16);
                      memory :> bytes(ivec_p,16);
                      memory :> bytes(word_add stackpointer (word 64),16)] ,,
           MAYCHANGE [Q0;Q1;Q2;Q3;Q4;Q5;Q6;Q7;Q8;Q9;Q10;Q11;Q12;Q13;Q14;Q15;
                      Q16;Q17;Q18;Q19;Q20;Q21;Q22;Q23;Q24;Q25;Q26;Q27;Q28;Q29;Q30;Q31])`,
  WB_READABLE_TAC 6 AESV8_GCM_8X_DEC_256_BUF_6BLOCK);;

let AESV8_GCM_8X_DEC_256_7BLOCK = prove
 (`!pc stackpointer in_p out_p xi_p ivec_p key_p htbl_p
    ibytes (rk:int128 list) (H:int128) tag0 ctr0.
     LENGTH ibytes = 112 /\ LENGTH rk = 15 /\
     aligned 16 stackpointer /\
     ALLPAIRS nonoverlapping
       [out_p,112; xi_p,16; ivec_p,16]
       [word pc, LENGTH aesv8_gcm_8x_dec_256_wb_mc; in_p,112; key_p,240; htbl_p,192; stackpointer,80] /\
     PAIRWISE nonoverlapping [out_p,112; xi_p,16; ivec_p,16] /\
     ALL (nonoverlapping (stackpointer,80))
       [word pc, LENGTH aesv8_gcm_8x_dec_256_wb_mc; in_p,112; key_p,240; htbl_p,192]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) aesv8_gcm_8x_dec_256_wb_mc /\
               read PC s = word (pc + 0x20) /\
               read SP s = stackpointer /\
               C_ARGUMENTS [in_p; word 896; out_p; xi_p; ivec_p; key_p; htbl_p] s /\
               byte_list_at ibytes in_p (word 112) s /\
               read (memory :> bytes128 xi_p) s = word_reversefields 8 tag0 /\
               read (memory :> bytes128 ivec_p) s = ctr0 /\
               wordlist_from_memory (key_p,15) s = rk /\
               htable_mem_8 (ghash_twist H) htbl_p s)
          (\s. read PC s = word (pc + 4560) /\
               byte_list_at (gcm_dec_pt_bytes 112 ibytes ctr0 rk) out_p (word 112) s /\
               read (memory :> bytes128 xi_p) s =
               word_reversefields 8
                 (nist_ghash H tag0 (list_of_seq (nist_input_block ibytes) 7))
               /\
               read (memory :> bytes128 ivec_p) s = gcm_ctr_inc_iter 7 ctr0)
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(out_p,112); memory :> bytes(xi_p,16);
                      memory :> bytes(ivec_p,16);
                      memory :> bytes(word_add stackpointer (word 64),16)] ,,
           MAYCHANGE [Q0;Q1;Q2;Q3;Q4;Q5;Q6;Q7;Q8;Q9;Q10;Q11;Q12;Q13;Q14;Q15;
                      Q16;Q17;Q18;Q19;Q20;Q21;Q22;Q23;Q24;Q25;Q26;Q27;Q28;Q29;Q30;Q31])`,
  WB_READABLE_TAC 7 AESV8_GCM_8X_DEC_256_BUF_7BLOCK);;

let AESV8_GCM_8X_DEC_256_8BLOCK = prove
 (`!pc stackpointer in_p out_p xi_p ivec_p key_p htbl_p
    ibytes (rk:int128 list) (H:int128) tag0 ctr0.
     LENGTH ibytes = 128 /\ LENGTH rk = 15 /\
     aligned 16 stackpointer /\
     ALLPAIRS nonoverlapping
       [out_p,128; xi_p,16; ivec_p,16]
       [word pc, LENGTH aesv8_gcm_8x_dec_256_wb_mc; in_p,128; key_p,240; htbl_p,192; stackpointer,80] /\
     PAIRWISE nonoverlapping [out_p,128; xi_p,16; ivec_p,16] /\
     ALL (nonoverlapping (stackpointer,80))
       [word pc, LENGTH aesv8_gcm_8x_dec_256_wb_mc; in_p,128; key_p,240; htbl_p,192]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) aesv8_gcm_8x_dec_256_wb_mc /\
               read PC s = word (pc + 0x20) /\
               read SP s = stackpointer /\
               C_ARGUMENTS [in_p; word 1024; out_p; xi_p; ivec_p; key_p; htbl_p] s /\
               byte_list_at ibytes in_p (word 128) s /\
               read (memory :> bytes128 xi_p) s = word_reversefields 8 tag0 /\
               read (memory :> bytes128 ivec_p) s = ctr0 /\
               wordlist_from_memory (key_p,15) s = rk /\
               htable_mem_8 (ghash_twist H) htbl_p s)
          (\s. read PC s = word (pc + 4560) /\
               byte_list_at (gcm_dec_pt_bytes 128 ibytes ctr0 rk) out_p (word 128) s /\
               read (memory :> bytes128 xi_p) s =
               word_reversefields 8
                 (nist_ghash H tag0 (list_of_seq (nist_input_block ibytes) 8))
               /\
               read (memory :> bytes128 ivec_p) s = gcm_ctr_inc_iter 8 ctr0)
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(out_p,128); memory :> bytes(xi_p,16);
                      memory :> bytes(ivec_p,16);
                      memory :> bytes(word_add stackpointer (word 64),16)] ,,
           MAYCHANGE [Q0;Q1;Q2;Q3;Q4;Q5;Q6;Q7;Q8;Q9;Q10;Q11;Q12;Q13;Q14;Q15;
                      Q16;Q17;Q18;Q19;Q20;Q21;Q22;Q23;Q24;Q25;Q26;Q27;Q28;Q29;Q30;Q31])`,
  WB_READABLE_TAC 8 AESV8_GCM_8X_DEC_256_BUF_8BLOCK);;

(* ---- the <=8-block dispatch theorem ----------------------------------------
   ONE readable theorem for every valid whole-blocks call: symbolic nblk
   (1 <= nblk <= 8), bit_len C-argument = word (128*nblk), byte_list_at in/out
   over the whole 16*nblk-byte buffer, same NIST vocabulary as the bands.
   Proof: 8-way case split on nblk, each case reduces 16*k/128*k to numerals
   and MATCH_MP_TACs the band theorem.  Combined with
   AESV8_GCM_8X_DEC_256_GUARD (above) this is the complete contract of the
   whole-blocks binary. *)
let AESV8_GCM_8X_DEC_256_DISPATCH = prove
 (`!pc stackpointer in_p out_p xi_p ivec_p key_p htbl_p
    nblk ibytes (rk:int128 list) (H:int128) tag0 ctr0.
     1 <= nblk /\ nblk <= 8 /\
     LENGTH ibytes = 16 * nblk /\ LENGTH rk = 15 /\
     aligned 16 stackpointer /\
     ALLPAIRS nonoverlapping
       [out_p,16 * nblk; xi_p,16; ivec_p,16]
       [word pc, LENGTH aesv8_gcm_8x_dec_256_wb_mc; in_p,16 * nblk; key_p,240; htbl_p,192; stackpointer,80] /\
     PAIRWISE nonoverlapping [out_p,16 * nblk; xi_p,16; ivec_p,16] /\
     ALL (nonoverlapping (stackpointer,80))
       [word pc, LENGTH aesv8_gcm_8x_dec_256_wb_mc; in_p,16 * nblk; key_p,240; htbl_p,192]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) aesv8_gcm_8x_dec_256_wb_mc /\
               read PC s = word (pc + 0x20) /\
               read SP s = stackpointer /\
               C_ARGUMENTS [in_p; word (128 * nblk); out_p; xi_p; ivec_p; key_p; htbl_p] s /\
               byte_list_at ibytes in_p (word (16 * nblk)) s /\
               read (memory :> bytes128 xi_p) s = word_reversefields 8 tag0 /\
               read (memory :> bytes128 ivec_p) s = ctr0 /\
               wordlist_from_memory (key_p,15) s = rk /\
               htable_mem_8 (ghash_twist H) htbl_p s)
          (\s. read PC s = word (pc + 4560) /\
               byte_list_at (gcm_dec_pt_bytes (16 * nblk) ibytes ctr0 rk) out_p (word (16 * nblk)) s /\
               read (memory :> bytes128 xi_p) s =
               word_reversefields 8
                 (nist_ghash H tag0 (list_of_seq (nist_input_block ibytes) nblk))
               /\
               read (memory :> bytes128 ivec_p) s = gcm_ctr_inc_iter nblk ctr0)
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(out_p,16 * nblk); memory :> bytes(xi_p,16);
                      memory :> bytes(ivec_p,16);
                      memory :> bytes(word_add stackpointer (word 64),16)] ,,
           MAYCHANGE [Q0;Q1;Q2;Q3;Q4;Q5;Q6;Q7;Q8;Q9;Q10;Q11;Q12;Q13;Q14;Q15;
                      Q16;Q17;Q18;Q19;Q20;Q21;Q22;Q23;Q24;Q25;Q26;Q27;Q28;Q29;Q30;Q31])`,
  let bands = [AESV8_GCM_8X_DEC_256_1BLOCK;AESV8_GCM_8X_DEC_256_2BLOCK;
               AESV8_GCM_8X_DEC_256_3BLOCK;AESV8_GCM_8X_DEC_256_4BLOCK;
               AESV8_GCM_8X_DEC_256_5BLOCK;AESV8_GCM_8X_DEC_256_6BLOCK;
               AESV8_GCM_8X_DEC_256_7BLOCK;AESV8_GCM_8X_DEC_256_8BLOCK] in
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `nblk = 1 \/ nblk = 2 \/ nblk = 3 \/ nblk = 4 \/ nblk = 5 \/ nblk = 6 \/ nblk = 7 \/ nblk = 8`
    MP_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN
  FIRST (map (fun w -> MATCH_MP_TAC w THEN ASM_REWRITE_TAC[]) bands));;

(* sanity: no hypotheses, no new axioms *)
let () =
  let readable = [AESV8_GCM_8X_DEC_256_1BLOCK;AESV8_GCM_8X_DEC_256_2BLOCK;
                  AESV8_GCM_8X_DEC_256_3BLOCK;AESV8_GCM_8X_DEC_256_4BLOCK;
                  AESV8_GCM_8X_DEC_256_5BLOCK;AESV8_GCM_8X_DEC_256_6BLOCK;
                  AESV8_GCM_8X_DEC_256_7BLOCK;AESV8_GCM_8X_DEC_256_8BLOCK;
                  AESV8_GCM_8X_DEC_256_DISPATCH;
                  AESV8_GCM_8X_DEC_256_GUARD] in
  if exists (fun th -> hyp th <> []) readable then
    failwith "WB readable theorems: unexpected hypotheses"
  else if List.length (axioms()) <> 3 then
    failwith "unexpected axiom count"
  else Format.print_string "WB readable bands + dispatch + guard: hyps=0, axioms=3\n";;

(* ====================================================================== *)
(* END inlined <=8-block chain; below: the nblk>8 main-loop proof.          *)
(* --- mid-load heap compaction: bound GC cost across this large single-file *)
(*     load (at the former needs seam); mirrors the needs-boundary/ckpt Gc.compact). ---                              *)
Gc.compact();;
(* ====================================================================== *)

(* aes_xts_common: IVAL_WORD_LT.  gcm_ctr_helpers: gcm_ctr_inc / _iter, the
   GCM_CTR_INC*_LANES lemmas.  Both are no-ops if the <=8-block chain already pulled them. *)
needs "arm/proofs/utils/aes_xts_common.ml";;
needs "arm/proofs/utils/gcm_ctr_helpers.ml";;

(* ------------------------------------------------------------------------- *)
(* 1. Scalar rung lemmas (nblk > 8 generalizations of USHR_128NBLK /         *)
(*    AND_MASK_16NBLK).  All pure word/arith, no sim.                        *)
(*                                                                           *)
(* NOTE (signed pointer compares): the 0x42c/0x49c/0x9e4 cmp x0,x5 feed      *)
(* b.ge/b.lt = SIGNED conditions on pointers.  For nblk <= 8 x5 = in_p so    *)
(* the compare was reflexive; for nblk > 8 the exactness of                  *)
(* ival(x0) - ival(x5) needs the buffer to not straddle the 2^63 signed     *)
(* boundary: hypothesis WB_PTR_OK below (satisfied by all userspace bufs).   *)
(* ------------------------------------------------------------------------- *)

(* x9 := bit_len >> 3 = 16*nblk, now for ALL nblk with 128*nblk < 2^64 *)
let USHR_128NBLK_ANY = prove
 (`!nblk. 128 * nblk < 2 EXP 64
        ==> word_ushr (word (128 * nblk):int64) 3 = word (16 * nblk)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[word_ushr] THEN
  ASM_SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64] THEN AP_TERM_TAC THEN ARITH_TAC);;

(* the loop byte bound: (16*nblk - 1) AND ~127 = 128 * ((nblk-1) DIV 8) *)
let AND_MASK_16NBLK_ANY = prove
 (`!nblk. 1 <= nblk /\ 16 * nblk < 2 EXP 64
        ==> word_and (word_sub (word (16 * nblk)) (word 1))
                     (word 18446744073709551488):int64 =
            word (128 * ((nblk - 1) DIV 8))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `word 18446744073709551488:int64 = word_not (word (2 EXP 7 - 1))`
    SUBST1_TAC THENL
   [CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN CONV_TAC WORD_REDUCE_CONV;
    ALL_TAC] THEN
  REWRITE_TAC[WORD_AND_NOT_MASK_WORD] THEN
  SUBGOAL_THEN `word_sub (word (16 * nblk)) (word 1):int64 = word (16 * nblk - 1)`
    SUBST1_TAC THENL
   [REWRITE_TAC[WORD_SUB] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `val (word (16 * nblk - 1):int64) = 16 * nblk - 1` SUBST1_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  AP_TERM_TAC THEN
  SUBGOAL_THEN `(16 * nblk - 1) DIV 2 EXP 7 = (nblk - 1) DIV 8` SUBST1_TAC THENL
   [ALL_TAC; ARITH_TAC] THEN
  MP_TAC(SPECL [`nblk - 1`; `8`] DIVISION) THEN
  ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `d = (nblk - 1) DIV 8` THEN ABBREV_TAC `m = (nblk - 1) MOD 8` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `nblk = d * 8 + m + 1` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `16 * m + 15` THEN ASM_ARITH_TAC);;

(* exact ival of an in-range pointer offset (for the signed pointer compares
   cmp x0,x5 at 0x3e0/0x440/0x9e4 feeding b.ge/b.lt) *)
let IVAL_PTR_ADD = prove
 (`!(p:int64) a. val p + a < 2 EXP 63 ==> ival (word_add p (word a)) = &(val p + a)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `word_add p (word a):int64 = word (val p + a)` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
    CONV_TAC MOD_DOWN_CONV THEN REFL_TAC; ALL_TAC] THEN
  MATCH_MP_TAC IVAL_WORD_LT THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC);;

(* NOTE: ival(word_neg(word d)) needs d <= 2^63 *)
let IVAL_NEG_SMALL = prove
 (`!d. d <= 2 EXP 63 ==> ival (word_neg (word d):int64) = -- &d`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[WORD_IWORD] THEN
  REWRITE_TAC[GSYM IWORD_INT_NEG] THEN MATCH_MP_TAC IVAL_IWORD THEN
  REWRITE_TAC[DIMINDEX_64] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
  REWRITE_TAC[INT_ARITH `--(&9223372036854775808):int <= -- &d /\ -- &d < &9223372036854775808 <=> &d <= &9223372036854775808`] THEN
  ASM_REWRITE_TAC[INT_OF_NUM_LE] THEN ASM_ARITH_TAC);;

(* signed sub of two small words *)
let IVAL_WSUB_SMALL = prove
 (`!a d. a < 2 EXP 63 /\ d < 2 EXP 63
      ==> ival (word_sub (word a) (word d):int64) = &a - &d`,
  REPEAT STRIP_TAC THEN
  DISJ_CASES_TAC(ARITH_RULE `a < d \/ d <= a:num`) THENL
   [SUBGOAL_THEN `word_sub (word a) (word d):int64 = word_neg (word (d - a))` SUBST1_TAC THENL
     [GEN_REWRITE_TAC LAND_CONV [WORD_RULE `word_sub (word a) (word d):int64 = word_neg (word_sub (word d) (word a))`] THEN
      AP_TERM_TAC THEN REWRITE_TAC[WORD_SUB] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `ival (word_neg (word (d - a)):int64) = -- &(d - a)` SUBST1_TAC THENL
     [MATCH_MP_TAC IVAL_NEG_SMALL THEN ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&(d - a):int = &d - &a` SUBST1_TAC THENL
     [REWRITE_TAC[INT_OF_NUM_SUB] THEN ASM_ARITH_TAC; INT_ARITH_TAC];
    SUBGOAL_THEN `word_sub (word a) (word d):int64 = word (a - d)` SUBST1_TAC THENL
     [REWRITE_TAC[WORD_SUB] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `ival (word (a - d):int64) = &(a - d)` SUBST1_TAC THENL
     [MATCH_MP_TAC IVAL_WORD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&(a - d):int = &a - &d` SUBST1_TAC THENL
     [REWRITE_TAC[INT_OF_NUM_SUB] THEN ASM_ARITH_TAC; INT_ARITH_TAC]]);;

(* small pointer has exact ival *)
let IVAL_SMALL_PTR = prove
 (`!(p:int64). val p < 2 EXP 63 ==> ival p = &(val p)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[IVAL_VAL; DIMINDEX_64] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
  SUBGOAL_THEN `bit 63 (p:int64) <=> F` SUBST1_TAC THENL
   [MP_TAC(ISPEC `p:int64` MSB_VAL) THEN REWRITE_TAC[DIMINDEX_64] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
    DISCH_THEN SUBST1_TAC THEN ASM_ARITH_TAC;
    REWRITE_TAC[BITVAL_CLAUSES] THEN INT_ARITH_TAC]);;

(* the generic signed pointer-compare flag resolver:
   cmp x0,x5 with x0 = p + a, x5 = (word d) + p; b.ge/b.lt read NF<=>VF,
   which under no-2^63-straddle collapses to a < d *)
let WB_PTRCMP_FLAGS = prove
 (`!(in_p:int64) a d.
      val in_p + a < 2 EXP 63 /\ val in_p + d < 2 EXP 63
      ==> (ival (word_sub (word_add in_p (word a)) (word_add (word d) in_p)) < &0 <=> a < d) /\
          ((ival (word_add in_p (word a)) - ival (word_add (word d) in_p) =
            ival (word_sub (word_add in_p (word a)) (word_add (word d) in_p))) <=> T)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `word_add (word d) in_p:int64 = word_add in_p (word d)` SUBST1_TAC THENL
   [CONV_TAC WORD_RULE; ALL_TAC] THEN
  SUBGOAL_THEN `ival (word_add in_p (word a):int64) = &(val in_p + a) /\
                ival (word_add in_p (word d):int64) = &(val in_p + d)`
    (CONJUNCTS_THEN SUBST1_TAC) THENL
   [CONJ_TAC THEN MATCH_MP_TAC IVAL_PTR_ADD THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `word_sub (word_add in_p (word a)) (word_add in_p (word d)):int64 =
                word_sub (word a) (word d)` SUBST1_TAC THENL
   [CONV_TAC WORD_RULE; ALL_TAC] THEN
  SUBGOAL_THEN `ival (word_sub (word a) (word d):int64) = &a - &d` SUBST1_TAC THENL
   [MATCH_MP_TAC IVAL_WSUB_SMALL THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_ADD] THEN
  REWRITE_TAC[INT_ARITH `(&v + &a) - (&v + &d):int = &a - &d`] THEN
  REWRITE_TAC[INT_ARITH `&a - &d:int < &0 <=> &a:int < &d`; INT_OF_NUM_LT]);;

(* specialization for the 0x42c loop-entry b.ge with x0 = in_p (a = 0):
   in the nblk>8 regime the branch FALLS THROUGH (NF=T <=> VF=F test fails) *)
let WB_LOOPENTER_FLAGS = prove
 (`!(in_p:int64) nblk. 17 <= nblk /\ 128 * nblk < 2 EXP 62 /\
        val in_p + 16 * nblk < 2 EXP 63
    ==> (ival (word_sub in_p (word_add (word (128 * (nblk - 1) DIV 8)) in_p)) < &0 <=> T) /\
        (ival in_p - ival (word_add (word (128 * (nblk - 1) DIV 8)) in_p) =
         ival (word_sub in_p (word_add (word (128 * (nblk - 1) DIV 8)) in_p)) <=> T)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `d = 128 * (nblk - 1) DIV 8` THEN
  SUBGOAL_THEN `1 <= d /\ d <= 16 * nblk /\ d <= 2 EXP 63` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "d" THEN
    MP_TAC(SPECL [`nblk - 1`; `8`] DIVISION) THEN
    MP_TAC(ASSUME `17 <= nblk`) THEN MP_TAC(ASSUME `128 * nblk < 2 EXP 62`) THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN REPEAT STRIP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[WORD_RULE `word_sub p (word_add (word d) p):int64 = word_neg (word d)`] THEN
  ASM_SIMP_TAC[IVAL_NEG_SMALL] THEN
  SUBGOAL_THEN `word_add (word d) in_p:int64 = word_add in_p (word d)` SUBST1_TAC THENL
   [CONV_TAC WORD_RULE; ALL_TAC] THEN
  SUBGOAL_THEN `ival (word_add in_p (word d):int64) = &(val in_p + d)` SUBST1_TAC THENL
   [MATCH_MP_TAC IVAL_PTR_ADD THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `ival (in_p:int64) = &(val in_p)` SUBST1_TAC THENL
   [MATCH_MP_TAC IVAL_SMALL_PTR THEN ASM_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[INT_ARITH `--(&d):int < &0 <=> &0:int < &d`; INT_OF_NUM_LT] THEN
    ASM_ARITH_TAC;
    REWRITE_TAC[GSYM INT_OF_NUM_ADD] THEN INT_ARITH_TAC]);;

(* d = 128*((nblk-1) DIV 8) > 128 iff nblk >= 17 (drives the 0x49c skip) *)
let D_GT_128 = prove
 (`!nblk. 17 <= nblk ==> (128 < 128 * (nblk - 1) DIV 8 <=> T)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC(ARITH_RULE `2 <= q ==> 128 < 128 * q`) THEN
  SUBGOAL_THEN `16 <= nblk - 1` MP_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN DISCH_TAC THEN
  MP_TAC(SPECL [`nblk - 1`; `8`] DIVISION) THEN ASM_ARITH_TAC);;

(* (DIV128_16NBLK, a byte-level warm-up restatement kept "for the
   seam arithmetic", was never referenced -- deleted.) *)

(* (Sec 2 symbolic-counter block MOVED up to the band-tail region for the ivec
   M2 close.  gcm_ctr_add .. GCM_CTR_INC_ITER_ADD now precede
   WB_TAIL_GEN2_r.) *)

(* gcm_ctr_raw_def was HOISTED above wb_front_postcond: the ivec
   M2 EDIT 0 adds a `read Q30 s = gcm_ctr_raw (word 8) ctr0` conjunct to
   wb_front_postcond (Sec 3, earlier in the file), which forward-references
   gcm_ctr_raw -- so the definition now lives before that use.  Its body-only
   algebra lemmas (SUBW_RAW_*, GCM_CTR_RAW_INCR, REV32_FOLD_TAC) stay in Sec 9b. *)

(* ivec M2: the raw counter accumulator ABSORBS a prior gcm_ctr_add
   into its own offset.  gcm_ctr_raw v (gcm_ctr_add u x) = gcm_ctr_raw (word_add u v) x.
   Needed by INNER_TAIL_FEED_TAC to discharge the SHIFTED tail's Q30 (the shift sets
   ctr0 := gcm_ctr_add (word 8*(q+1)) ctr0) against the M1 seam's Q30, and by the
   FULL_r ivec reconcile.  Proved at 32-bit-LANE granularity so the symbolic 32-bit
   addend never enters a 128-bit BDD (a naive WORD_BLAST HANGS).
   gcm_ctr_raw reads only the 4 lanes of its arg; gcm_ctr_add rewrites only lane
   (96,32); so the low 3 lanes pass through and the top lane composes the two adds. *)
let BREV_LANE_64 = prove
 (`!ctr0:int128.
     word_join (word_join (word_subword ctr0 (64,8):8 word) (word_subword ctr0 (72,8):8 word):16 word)
       (word_join (word_subword ctr0 (80,8):8 word) (word_subword ctr0 (88,8):8 word):16 word) =
     word_bytereverse (word_subword ctr0 (64,32):32 word)`,
  GEN_TAC THEN BITBLAST_TAC);;

let BREV_LANE_32 = prove
 (`!ctr0:int128.
     word_join (word_join (word_subword ctr0 (32,8):8 word) (word_subword ctr0 (40,8):8 word):16 word)
       (word_join (word_subword ctr0 (48,8):8 word) (word_subword ctr0 (56,8):8 word):16 word) =
     word_bytereverse (word_subword ctr0 (32,32):32 word)`,
  GEN_TAC THEN BITBLAST_TAC);;

let BREV_LANE_0 = prove
 (`!ctr0:int128.
     word_join (word_join (word_subword ctr0 (0,8):8 word) (word_subword ctr0 (8,8):8 word):16 word)
       (word_join (word_subword ctr0 (16,8):8 word) (word_subword ctr0 (24,8):8 word):16 word) =
     word_bytereverse (word_subword ctr0 (0,32):32 word)`,
  GEN_TAC THEN BITBLAST_TAC);;

(* gcm_ctr_raw in 32-bit-lane form: top lane = word_add(brev of z top lane) w,
   the other three lanes = byte-reverse of z's lanes. *)
let GCM_CTR_RAW_LANEFORM = prove
 (`!w z:int128. gcm_ctr_raw w z =
    word_join
     (word_join (word_add (word_bytereverse (word_subword z (96,32):32 word)) w)
                (word_bytereverse (word_subword z (64,32):32 word)):64 word)
     (word_join (word_bytereverse (word_subword z (32,32):32 word))
                (word_bytereverse (word_subword z (0,32):32 word)):64 word):int128`,
  REWRITE_TAC[gcm_ctr_raw_def] THEN
  REWRITE_TAC[GSYM BREV_TOP_LANE; GSYM BREV_LANE_64; GSYM BREV_LANE_32; GSYM BREV_LANE_0]);;

(* 32-bit-lane insert passthrough: the low 3 lanes are unaffected by the top insert. *)
let SUBWORD_INSERT_LOW_LANE = prove
 (`!(x:int128) (nw:32 word).
     (word_subword (word_insert x (96,32) nw : int128) (0,32):32 word = word_subword x (0,32)) /\
     (word_subword (word_insert x (96,32) nw : int128) (32,32):32 word = word_subword x (32,32)) /\
     (word_subword (word_insert x (96,32) nw : int128) (64,32):32 word = word_subword x (64,32))`,
  REPEAT GEN_TAC THEN REPEAT CONJ_TAC THEN BITBLAST_TAC);;

let GCM_CTR_RAW_ABSORB = prove
 (`!(u:32 word) (v:32 word) (x:int128).
     gcm_ctr_raw v (gcm_ctr_add u x) = gcm_ctr_raw (word_add u v) x`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[GCM_CTR_RAW_LANEFORM] THEN
  REWRITE_TAC[gcm_ctr_add] THEN
  REWRITE_TAC[SUBWORD_INSERT_TOP; SUBWORD_INSERT_LOW_LANE; BREV_BREV_32] THEN
  REWRITE_TAC[GSYM WORD_ADD_ASSOC]);;

let GCM_CTR_RAW_ABSORB_NUM = prove
 (`!a b (x:int128).
     gcm_ctr_raw (word b) (gcm_ctr_add (word a) x) = gcm_ctr_raw (word (a + b)) x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GCM_CTR_RAW_ABSORB] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE);;

(* ------------------------------------------------------------------------- *)
(* 3. FRONT-N: capture the nblk>8 front (entry 0x20 -> loop head 0x4a0) as    *)
(*    WBN_FRONT_BUF.  Its harvested postcondition (state s288 at the loop     *)
(*    head) IS the i=0 instance of the ENSURES_WHILE loop invariant.          *)
(*                                                                            *)
(* Deltas vs the <=8-block WB_FRONT_BUF (entry 0x20 -> 0x42c tail):                         *)
(*  - hyps: 1<=nblk /\ nblk<=8  becomes  17<=nblk /\ 128*nblk<2^62 /\         *)
(*    val in_p + 16*nblk < 2^63 (the signed pointer-compare no-2^63-straddle).*)
(*  - prep uses the _ANY scalar rungs (X5 = word(128*((nblk-1)DIV8)) not 0).  *)
(*  - front steps 1..259 identical to WB_FRONT_STEP_TAC modulo mk_discard2[30]*)
(*    -> DISCARD_STALE_Q30_TAC, and STOPPING before the 0x42c branch (no <=8  *)
(*    INT_SUB_REFL / WORD_RULE collapse, since X5 != in_p here).              *)
(*  - the 0x42c b.ge (step 260) FALLS THROUGH via WB_LOOPENTER_FLAGS; then    *)
(*    bulk-8 segment 261..287; the 0x49c b.ge (step 288) FALLS THROUGH to     *)
(*    the loop head via WB_PTRCMP_FLAGS + D_GT_128.                           *)
(*                                                                            *)
(* Route A (as in the <=8-block WB_FRONT_BUF): the 8 in-flight keystream towers cannot      *)
(* be hand-written and the printed s288 term does not reparse, so we run the  *)
(* front once against a MINIMAL postcond, harvest the s288 assumptions with   *)
(* build_state_postcond_tms2 (folded to aes13 + gcm_ctr_inc^k lanes by        *)
(* wb_front_fold_tac), then prove.  The front therefore sims twice per cold   *)
(* load (once to harvest, once in the proof) -- the checkpoint hides this for *)
(* interactive work.                                                          *)
(* ------------------------------------------------------------------------- *)

(* nblk>8 front hypotheses: swap the (1<=nblk /\ nblk<=8) prefix of the <=8-block chain's
   wb_front_hyps_tm for the nblk>=17 regime, KEEP every nonoverlapping/aligned/
   length conjunct.
   : ALSO add nonoverlapping (out_p) (stackpointer,80).  the <=8-block chain's
   wb_front_hyps_tm omits it, but the nblk>8 front's FRONT-0 group (0x430..0x498)
   does four `stp q,q,[x2],#32` stores to out_p BEFORE the loop head 0x4a0.
   Without out_p-vs-stack disjointness the stepper cannot prove those stores miss
   [sp+64], so it DROPS the reduction-constant fact
   read (memory :> bytes64 (sp+64)) s = word 0xc200000000000000 (needed by the
   body GHASH reduce; see the invariant [sp+64] conjunct).
   VALIDATED: with this conjunct the fact survives the full front
   sim to s288 (=loop head 0x4a0) and is auto-harvested by
   build_state_postcond_tms2. *)
let wbn_front_hyps_tm =
  let _,rest1 = dest_conj wb_front_hyps_tm in
  let _,rest = dest_conj rest1 in
  mk_conj(`17 <= nblk /\ 128 * nblk < 2 EXP 62 /\ val (in_p:int64) + 16 * nblk < 2 EXP 63`,
          mk_conj(`nonoverlapping (out_p:int64,16 * nblk) (stackpointer:int64,80)`,
                  rest));;

let mk_wbn_front_goal postcond =
  let ens = subst [wb_front_pre_tm,`PPP:armstate->bool`; postcond,`QQQ:armstate->bool`;
                   wb_front_frame_tm,`CCC:armstate->armstate->bool`]
              `ensures arm PPP QQQ CCC` in
  list_mk_forall(wb_front_vars, mk_imp(wbn_front_hyps_tm, ens));;

(* pure-arith closer for the nblk>=17 side conditions *)
let NBLK_ARITH_TAC =
  MP_TAC(ASSUME `17 <= nblk`) THEN MP_TAC(ASSUME `128 * nblk < 2 EXP 62`) THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN ARITH_TAC;;

(* nblk>8 buffer prep: same shape as the <=8-block WB_FRONT_PREP_BUF_TAC but with the
   _ANY rungs and the nblk>=17 arithmetic for the block-0 lane. *)
let WBN_FRONT_PREP_BUF_TAC =
  SUBGOAL_THEN `SUB_LIST (0, 16 * nblk) (ibytes:byte list) = ibytes` ASSUME_TAC THENL
   [MATCH_MP_TAC SUB_LIST_LENGTH_IMPLIES THEN ASM_REWRITE_TAC[LE_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN `read (memory :> bytes128 in_p) s0 = bytes_to_int128 (SUB_LIST (0,16) ibytes)` ASSUME_TAC THENL
   [MP_TAC(SPECL [`nblk:num`; `in_p:int64`; `ibytes:byte list`; `s0:armstate`] INPUT_BYTES_TO_BYTE128_LANES) THEN
    ASM_REWRITE_TAC[LE_REFL] THEN DISCH_THEN(MP_TAC o SPEC `0`) THEN
    ANTS_TAC THENL [NBLK_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]); ALL_TAC] THEN
  SUBGOAL_THEN `word_ushr (word (128 * nblk):int64) 3 = word (16 * nblk)` ASSUME_TAC THENL
   [MATCH_MP_TAC USHR_128NBLK_ANY THEN NBLK_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `word_and (word_sub (word (16 * nblk)) (word 1)) (word 18446744073709551488):int64 = word (128 * ((nblk - 1) DIV 8))` ASSUME_TAC THENL
   [MATCH_MP_TAC AND_MASK_16NBLK_ANY THEN NBLK_ARITH_TAC; ALL_TAC];;

(* input lanes 0..7 for the bulk-8 ldp at 0x430 *)
let WBN_LANES_TAC =
  SUBGOAL_THEN
   `!k. k < 8 ==> read (memory :> bytes128 (word_add in_p (word (16 * k)))) s0 =
                  bytes_to_int128 (SUB_LIST (16 * k, 16) (ibytes:byte list))`
   MP_TAC THENL
   [MP_TAC(SPECL [`nblk:num`; `in_p:int64`; `ibytes:byte list`; `s0:armstate`]
      INPUT_BYTES_TO_BYTE128_LANES) THEN
    ASM_REWRITE_TAC[LE_REFL] THEN
    DISCH_THEN(fun lth -> X_GEN_TAC `k:num` THEN DISCH_TAC THEN
      MP_TAC(SPEC `k:num` lth) THEN ANTS_TAC THENL
       [MP_TAC(ASSUME `k < 8`) THEN NBLK_ARITH_TAC; REWRITE_TAC[]]);
    DISCH_THEN(fun lth ->
      EVERY(map (fun i ->
        ASSUME_TAC(CONV_RULE(DEPTH_CONV NUM_RED_CONV)
          (MP (SPEC (mk_small_numeral i) lth)
              (ARITH_RULE(mk_binop `(<):num->num->bool` (mk_small_numeral i) `8`)))))
        (0--7)))];;

let wbn_init_tac =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS] THEN ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WB_MC_LEN]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[C_ARGUMENTS]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_dec]) THEN
  RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV let_CONV)) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o check(is_conj o concl)) THEN
  WBN_FRONT_PREP_BUF_TAC;;

(* keep only the latest read Q30 fact (the rev32 counter accumulator grows a
   big tower each step; older ones are dead) *)
let state_num_of_read_q30 th =
  let c = concl th in
  try (match lhs c with
       | Comb(Comb(Const("read",_),q),st) when string_of_term q = "Q30" ->
           let s = fst(dest_var st) in
           if String.length s > 1 && s.[0] = 's'
           then int_of_string (String.sub s 1 (String.length s - 1)) else (-1)
       | _ -> (-1))
  with _ -> (-1);;
let DISCARD_STALE_Q30_TAC : tactic = fun (asl,w) ->
  let nums = List.filter (fun n -> n >= 0)
    (List.map (fun (_,th) -> state_num_of_read_q30 th) asl) in
  if nums = [] then ALL_TAC (asl,w) else
  let mx = itlist max nums (-1) in
  DISCARD_ASSUMPTIONS_TAC (fun th ->
    let n = state_num_of_read_q30 th in n >= 0 && n < mx) (asl,w);;

(* front steps 1..267 (up to but NOT including the 0x44c b.ge at step 268).
   SETUP-counter flatten: same +6 step shift + per-step loop extended
   6--30 -> 6--41 as WBN_FRONT_STEP259_TAC above (was 1..259 / step 260 / 0x42c).
   FUSED SPLICE (STEP 4, +2 instrs): identical guard-splice as WBN_FRONT_STEP259_TAC
   — insert guard steps 7,8 (b.le falls through for nblk>=5), shift the vector
   per-step loop 6--41 -> 9--43 and every later range +2. *)
let WBN_FRONT_STEP_TAC =
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (1--6) THEN
  MP_TAC(SPEC `nblk:num` GUARD_LE_FALLTHRU) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN DISCH_TAC THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (7--8) THEN
  EVERY(map (fun i -> ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (i--i) THEN
             GCM_SIMD_SIMPLIFY_TAC) (9--43)) THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (44--92) THEN DISCARD_STALE_Q30_TAC THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (93--181) THEN DISCARD_STALE_Q30_TAC THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (182--185) THEN
  GCM_SIMD_SIMPLIFY_TAC THEN DISCARD_STALE_Q30_TAC THEN
  ARM_VSTEPS_FOLD_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (186--197) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[Q19_BREVXI]) THEN DISCARD_STALE_Q30_TAC THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (198--262) THEN
  DISCARD_STALE_Q30_TAC THEN GCM_SIMD_SIMPLIFY_TAC THEN
  ARM_VSTEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC [263] THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (264--267);;

(* 0x42c b.ge (step 260): nblk>=17 => X0=in_p, X5=in_p+d, NF=T VF=F, FALLS THRU *)
let WBN_RESOLVE_42C_TAC : tactic =
  MP_TAC(SPECL [`in_p:int64`; `nblk:num`] WB_LOOPENTER_FLAGS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]));;

(* 0x49c b.ge (step 288): X0=in_p+128, X5=in_p+d, 128<d for nblk>=17 => NF=T
   VF=F, FALLS THROUGH to loop head 0x4a0 *)
let WBN_RESOLVE_49C_TAC : tactic = fun (asl,w) ->
  (MP_TAC(SPECL [`in_p:int64`; `128`; `128 * (nblk - 1) DIV 8`] WB_PTRCMP_FLAGS) THEN
   ANTS_TAC THENL
    [CONJ_TAC THENL
      [MP_TAC(ASSUME `val (in_p:int64) + 16 * nblk < 2 EXP 63`) THEN NBLK_ARITH_TAC;
       MP_TAC(ASSUME `val (in_p:int64) + 16 * nblk < 2 EXP 63`) THEN
       MP_TAC(SPECL [`nblk - 1`; `8`] DIVISION) THEN NBLK_ARITH_TAC];
     ALL_TAC] THEN
   DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
   MP_TAC(SPEC `nblk:num` D_GT_128) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
   DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))) (asl,w);;

(* the complete front sim entry 0x20 -> loop head 0x4c0 (ends at s296 = the
   0x4bc b.ge; the loop head 0x4c0 is the fall-through target).
   FUSED SPLICE (STEP 4): the 2 .balign-16 nops that were steps 295,296 in base
   are GONE (the guard's +8 consumes them), so the net front step count is
   UNCHANGED (guard +2, nops -2).  Step map: prefix -> s267 (0x440); b.ge@0x44c
   is step 268 (was 266); tail 269..295 (was 267..293); b.ge@0x4bc step 296
   (was 294, +2); loop head 0x4c0 is the fall-through, not stepped. *)
let WBN_FRONT_FULL_TAC =
  wbn_init_tac THEN WBN_LANES_TAC THEN WBN_FRONT_STEP_TAC THEN
  WBN_RESOLVE_42C_TAC THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (268--268) THEN
  EVERY(map (fun i -> ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (i--i) THEN
             GCM_SIMD_SIMPLIFY_TAC THEN DISCARD_STALE_Q30_TAC) (269--295)) THEN
  WBN_RESOLVE_49C_TAC THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (296--296);;

(* ------------------------------------------------------------------------- *)
(* SPEED REFACTOR -- the SHARED FRONT PREFIX, simulated ONCE.                  *)
(*                                                                            *)
(* WBN_FRONT_BUF (band 17<=nblk, -> loop head 0x4a0) and WBN_FRONT_TO_PREP_916 *)
(* (band 9<=nblk<=16, -> prepretail 0x9f0) previously ran the IDENTICAL 287-  *)
(* step front sim (entry 0x20 -> the 0x49c b.ge), diverging ONLY at step 288  *)
(* (the 0x49c branch: >=17 falls through to 0x4a0; 9..16 is taken to 0x9f0).  *)
(* The 0x42c b.ge (step 260) falls through in BOTH bands, so steps 1..287 are *)
(* byte-identical work (~265s of duplicated ARM_STEPS per cold load).          *)
(*                                                                            *)
(* Factor: prove the prefix (0x20 -> 0x49c) ONCE on the union band 9<=nblk    *)
(* (WBN_FRONT_PREFIX), harvesting the raw s287 state (incl. the NF/VF/ZF/CF   *)
(* facts the 0x49c b.ge reads).  Each consumer then chains a single step-288  *)
(* leg via ENSURES_TRANS_SIMPLE: init from the prefix postcond, resolve the   *)
(* branch IN ITS BAND, step to its exit, close.  Both consumer STATEMENTS stay *)
(* bit-identical (still prove(<original goal builder>, ...)), so downstream    *)
(* (WBN_FRONT_BUF_EXT @ concl-extraction, the 916 MATCH_MP_TAC) is untouched.  *)
(* ------------------------------------------------------------------------- *)

(* union band: wbn_front_hyps_tm with 17<=nblk relaxed to 9<=nblk *)
let wbn_front_hyps_ge9_tm =
  let rec repl t = match t with
    | Comb(Comb(Const("/\\",_),a),b) -> mk_conj(repl a, repl b)
    | _ -> if t = `17 <= nblk` then `9 <= nblk` else t in
  repl wbn_front_hyps_tm;;

(* 0x42c b.ge falls through whenever d=128*((nblk-1)DIV8) >= 1, i.e. nblk>=9.
   (union of WB_LOOPENTER_FLAGS's 17<= and WB_LOOPENTER_FLAGS_916's 9..16). *)
let WB_LOOPENTER_FLAGS_GE9 = prove
 (`!(in_p:int64) nblk. 9 <= nblk /\ 128 * nblk < 2 EXP 62 /\
        val in_p + 16 * nblk < 2 EXP 63
    ==> (ival (word_sub in_p (word_add (word (128 * (nblk - 1) DIV 8)) in_p)) < &0 <=> T) /\
        (ival in_p - ival (word_add (word (128 * (nblk - 1) DIV 8)) in_p) =
         ival (word_sub in_p (word_add (word (128 * (nblk - 1) DIV 8)) in_p)) <=> T)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `d = 128 * (nblk - 1) DIV 8` THEN
  SUBGOAL_THEN `1 <= d /\ d <= 16 * nblk /\ d <= 2 EXP 63` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "d" THEN
    MP_TAC(SPECL [`nblk - 1`; `8`] DIVISION) THEN
    MP_TAC(ASSUME `9 <= nblk`) THEN MP_TAC(ASSUME `128 * nblk < 2 EXP 62`) THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN REPEAT STRIP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[WORD_RULE `word_sub p (word_add (word d) p):int64 = word_neg (word d)`] THEN
  ASM_SIMP_TAC[IVAL_NEG_SMALL] THEN
  SUBGOAL_THEN `word_add (word d) in_p:int64 = word_add in_p (word d)` SUBST1_TAC THENL
   [CONV_TAC WORD_RULE; ALL_TAC] THEN
  SUBGOAL_THEN `ival (word_add in_p (word d):int64) = &(val in_p + d)` SUBST1_TAC THENL
   [MATCH_MP_TAC IVAL_PTR_ADD THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `ival (in_p:int64) = &(val in_p)` SUBST1_TAC THENL
   [MATCH_MP_TAC IVAL_SMALL_PTR THEN ASM_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[INT_ARITH `--(&d):int < &0 <=> &0:int < &d`; INT_OF_NUM_LT] THEN
    ASM_ARITH_TAC;
    REWRITE_TAC[GSYM INT_OF_NUM_ADD] THEN INT_ARITH_TAC]);;

(* pure-arith closer for the union-band side conditions *)
let NBLK_ARITH_GE9_TAC =
  MP_TAC(ASSUME `9 <= nblk`) THEN
  MP_TAC(ASSUME `128 * nblk < 2 EXP 62`) THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN ARITH_TAC;;

(* union-band variants of the front prefix/lane/init tactics (mirror the 17<=
   WBN_FRONT_PREP_BUF_TAC/WBN_LANES_TAC/wbn_init_tac with the 9<= arith). *)
let WBN_FRONT_PREP_BUF_GE9_TAC =
  SUBGOAL_THEN `SUB_LIST (0, 16 * nblk) (ibytes:byte list) = ibytes` ASSUME_TAC THENL
   [MATCH_MP_TAC SUB_LIST_LENGTH_IMPLIES THEN ASM_REWRITE_TAC[LE_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN `read (memory :> bytes128 in_p) s0 = bytes_to_int128 (SUB_LIST (0,16) ibytes)` ASSUME_TAC THENL
   [MP_TAC(SPECL [`nblk:num`; `in_p:int64`; `ibytes:byte list`; `s0:armstate`] INPUT_BYTES_TO_BYTE128_LANES) THEN
    ASM_REWRITE_TAC[LE_REFL] THEN DISCH_THEN(MP_TAC o SPEC `0`) THEN
    ANTS_TAC THENL [NBLK_ARITH_GE9_TAC; ALL_TAC] THEN
    REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]); ALL_TAC] THEN
  SUBGOAL_THEN `word_ushr (word (128 * nblk):int64) 3 = word (16 * nblk)` ASSUME_TAC THENL
   [MATCH_MP_TAC USHR_128NBLK_ANY THEN NBLK_ARITH_GE9_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `word_and (word_sub (word (16 * nblk)) (word 1)) (word 18446744073709551488):int64 = word (128 * ((nblk - 1) DIV 8))` ASSUME_TAC THENL
   [MATCH_MP_TAC AND_MASK_16NBLK_ANY THEN NBLK_ARITH_GE9_TAC; ALL_TAC];;

let WBN_LANES_GE9_TAC =
  SUBGOAL_THEN
   `!k. k < 8 ==> read (memory :> bytes128 (word_add in_p (word (16 * k)))) s0 =
                  bytes_to_int128 (SUB_LIST (16 * k, 16) (ibytes:byte list))`
   MP_TAC THENL
   [MP_TAC(SPECL [`nblk:num`; `in_p:int64`; `ibytes:byte list`; `s0:armstate`]
      INPUT_BYTES_TO_BYTE128_LANES) THEN
    ASM_REWRITE_TAC[LE_REFL] THEN
    DISCH_THEN(fun lth -> X_GEN_TAC `k:num` THEN DISCH_TAC THEN
      MP_TAC(SPEC `k:num` lth) THEN ANTS_TAC THENL
       [MP_TAC(ASSUME `k < 8`) THEN NBLK_ARITH_GE9_TAC; REWRITE_TAC[]]);
    DISCH_THEN(fun lth ->
      EVERY(map (fun i ->
        ASSUME_TAC(CONV_RULE(DEPTH_CONV NUM_RED_CONV)
          (MP (SPEC (mk_small_numeral i) lth)
              (ARITH_RULE(mk_binop `(<):num->num->bool` (mk_small_numeral i) `8`)))))
        (0--7)))];;

let wbn_init_ge9_tac =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS] THEN ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WB_MC_LEN]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[C_ARGUMENTS]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_dec]) THEN
  RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV let_CONV)) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o check(is_conj o concl)) THEN
  WBN_FRONT_PREP_BUF_GE9_TAC;;

(* 0x42c resolve (fall-through) via WB_LOOPENTER_FLAGS_GE9. *)
let WBN_RESOLVE_42C_GE9_TAC : tactic =
  MP_TAC(SPECL [`in_p:int64`; `nblk:num`] WB_LOOPENTER_FLAGS_GE9) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]));;

(* the shared prefix sim: entry 0x20 -> 0x4b8 (steps 1..295), NO step 296.
   Identical to WBN_FRONT_FULL_TAC's prefix (share WBN_FRONT_STEP_TAC verbatim),
   but on the union band and stopping BEFORE the band-dependent 0x4bc branch.
   FUSED SPLICE (STEP 4): b.ge@0x44c step 268 (was 266); tail 269..295 (was
   267..293); stops at 0x4b8 before the 0x4bc b.ge (step 296). *)
let WBN_FRONT_PREFIX_TAC =
  wbn_init_ge9_tac THEN WBN_LANES_GE9_TAC THEN WBN_FRONT_STEP_TAC THEN
  WBN_RESOLVE_42C_GE9_TAC THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (268--268) THEN
  EVERY(map (fun i -> ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (i--i) THEN
             GCM_SIMD_SIMPLIFY_TAC THEN DISCARD_STALE_Q30_TAC) (269--295));;

(* prefix goal builder (union band, postcond at PC 0x49c) *)
let mk_wbn_prefix_goal postcond =
  let ens = subst [wb_front_pre_tm,`PPP:armstate->bool`; postcond,`QQQ:armstate->bool`;
                   wb_front_frame_tm,`CCC:armstate->armstate->bool`]
              `ensures arm PPP QQQ CCC` in
  list_mk_forall(wb_front_vars, mk_imp(wbn_front_hyps_ge9_tm, ens));;

(* The s287 prefix postcondition (state at the 0x49c b.ge, pre-branch), embedded
   as a fully type-annotated literal so the shared front simulates ONCE.  Keeps
   ALL raw `read _ s287 = _` facts INCLUDING the NF/VF/ZF/CF flag facts the 0x49c
   b.ge reads (so each consumer's step-288 leg can resolve the branch in its band).
   REGENERATION (if the front or its keep-profile changes): re-run
     let wbn_front_prefix_postcond_harv =
       let mg = mk_wbn_prefix_goal `\s:armstate. read PC s = word (pc + 0x4b4)` in
       let _ = g mg in let _ = e (WBN_FRONT_PREFIX_TAC THEN wb_front_fold_tac) in
       let (asl287,_) = top_goal() in let _ = b() in
       build_state_postcond_tms2 "s287" asl287;;
   then print with print_types_of_subterms := 2 and replace "(&:num->int)" with
   "(int_of_num:num->int)" (bare & does not reparse); verify aconv to the harvest. *)
let wbn_front_prefix_postcond = parse_term {|\(s:armstate).
    (aligned_bytes_loaded:armstate->(64)word->((8)word)list->bool)
    (s:armstate)
    ((word:num->(64)word) (pc:num))
    (aesv8_gcm_8x_dec_256_wb_mc:((8)word)list) /\
    (read:(armstate,(64)word)component->armstate->(64)word)
    (PC:(armstate,(64)word)component)
    (s:armstate) =
    (word:num->(64)word) ((pc:num) + 1212) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q30:(armstate,(128)word)component)
    (s:armstate) =
    (word_join:(64)word->(64)word->(128)word)
    ((word_join:(32)word->(32)word->(64)word)
     ((word_add:(32)word->(32)word->(32)word)
      ((word_add:(32)word->(32)word->(32)word)
       ((word_join:(16)word->(16)word->(32)word)
        ((word_join:(8)word->(8)word->(16)word)
         ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (96,8))
        ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (104,8)))
       ((word_join:(8)word->(8)word->(16)word)
        ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (112,8))
       ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (120,8))))
      ((word:num->(32)word) 12))
     ((word:num->(32)word) 1))
    ((word_add:(32)word->(32)word->(32)word)
     ((word_join:(16)word->(16)word->(32)word)
      ((word_join:(8)word->(8)word->(16)word)
       ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (64,8))
      ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (72,8)))
     ((word_join:(8)word->(8)word->(16)word)
      ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (80,8))
     ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (88,8))))
    ((word:num->(32)word) 0)))
    ((word_join:(32)word->(32)word->(64)word)
     ((word_add:(32)word->(32)word->(32)word)
      ((word_join:(16)word->(16)word->(32)word)
       ((word_join:(8)word->(8)word->(16)word)
        ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (32,8))
       ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (40,8)))
      ((word_join:(8)word->(8)word->(16)word)
       ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (48,8))
      ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (56,8))))
     ((word:num->(32)word) 0))
    ((word_add:(32)word->(32)word->(32)word)
     ((word_join:(16)word->(16)word->(32)word)
      ((word_join:(8)word->(8)word->(16)word)
       ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (0,8))
      ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (8,8)))
     ((word_join:(8)word->(8)word->(16)word)
      ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (16,8))
     ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (24,8))))
    ((word:num->(32)word) 0))) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (out_p:(64)word)
     ((word:num->(64)word) 96)))
    (s:armstate) =
    (word_xor:(128)word->(128)word->(128)word)
    ((word_xor:(128)word->(128)word->(128)word)
     ((bytes_to_int128:((8)word)list->(128)word)
     ((SUB_LIST:num#num->((8)word)list->((8)word)list) (96,16)
     (ibytes:((8)word)list)))
    ((aes13:(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word)
     ((gcm_ctr_inc:(128)word->(128)word)
     ((gcm_ctr_inc:(128)word->(128)word)
     ((gcm_ctr_inc:(128)word->(128)word)
     ((gcm_ctr_inc:(128)word->(128)word)
     ((gcm_ctr_inc:(128)word->(128)word)
     ((gcm_ctr_inc:(128)word->(128)word) (ctr0:(128)word)))))))
     (k0:(128)word)
     (k1:(128)word)
     (k2:(128)word)
     (k3:(128)word)
     (k4:(128)word)
     (k5:(128)word)
     (k6:(128)word)
     (k7:(128)word)
     (k8:(128)word)
     (k9:(128)word)
     (k10:(128)word)
     (k11:(128)word)
     (k12:(128)word)
    (k13:(128)word)))
    (k14:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (out_p:(64)word)
     ((word:num->(64)word) 112)))
    (s:armstate) =
    (word_xor:(128)word->(128)word->(128)word)
    ((word_xor:(128)word->(128)word->(128)word)
     ((bytes_to_int128:((8)word)list->(128)word)
     ((SUB_LIST:num#num->((8)word)list->((8)word)list) (112,16)
     (ibytes:((8)word)list)))
    ((aes13:(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word)
     ((gcm_ctr_inc:(128)word->(128)word)
     ((gcm_ctr_inc:(128)word->(128)word)
     ((gcm_ctr_inc:(128)word->(128)word)
     ((gcm_ctr_inc:(128)word->(128)word)
     ((gcm_ctr_inc:(128)word->(128)word)
     ((gcm_ctr_inc:(128)word->(128)word)
     ((gcm_ctr_inc:(128)word->(128)word) (ctr0:(128)word))))))))
     (k0:(128)word)
     (k1:(128)word)
     (k2:(128)word)
     (k3:(128)word)
     (k4:(128)word)
     (k5:(128)word)
     (k6:(128)word)
     (k7:(128)word)
     (k8:(128)word)
     (k9:(128)word)
     (k10:(128)word)
     (k11:(128)word)
     (k12:(128)word)
    (k13:(128)word)))
    (k14:(128)word) /\
    (read:(armstate,(64)word)component->armstate->(64)word)
    (X2:(armstate,(64)word)component)
    (s:armstate) =
    (word_add:(64)word->(64)word->(64)word) (out_p:(64)word)
    ((word:num->(64)word) 128) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (out_p:(64)word)
     ((word:num->(64)word) 64)))
    (s:armstate) =
    (word_xor:(128)word->(128)word->(128)word)
    ((word_xor:(128)word->(128)word->(128)word)
     ((bytes_to_int128:((8)word)list->(128)word)
     ((SUB_LIST:num#num->((8)word)list->((8)word)list) (64,16)
     (ibytes:((8)word)list)))
    ((aes13:(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word)
     ((gcm_ctr_inc:(128)word->(128)word)
     ((gcm_ctr_inc:(128)word->(128)word)
     ((gcm_ctr_inc:(128)word->(128)word)
     ((gcm_ctr_inc:(128)word->(128)word) (ctr0:(128)word)))))
     (k0:(128)word)
     (k1:(128)word)
     (k2:(128)word)
     (k3:(128)word)
     (k4:(128)word)
     (k5:(128)word)
     (k6:(128)word)
     (k7:(128)word)
     (k8:(128)word)
     (k9:(128)word)
     (k10:(128)word)
     (k11:(128)word)
     (k12:(128)word)
    (k13:(128)word)))
    (k14:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (out_p:(64)word)
     ((word:num->(64)word) 80)))
    (s:armstate) =
    (word_xor:(128)word->(128)word->(128)word)
    ((word_xor:(128)word->(128)word->(128)word)
     ((bytes_to_int128:((8)word)list->(128)word)
     ((SUB_LIST:num#num->((8)word)list->((8)word)list) (80,16)
     (ibytes:((8)word)list)))
    ((aes13:(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word)
     ((gcm_ctr_inc:(128)word->(128)word)
     ((gcm_ctr_inc:(128)word->(128)word)
     ((gcm_ctr_inc:(128)word->(128)word)
     ((gcm_ctr_inc:(128)word->(128)word)
     ((gcm_ctr_inc:(128)word->(128)word) (ctr0:(128)word))))))
     (k0:(128)word)
     (k1:(128)word)
     (k2:(128)word)
     (k3:(128)word)
     (k4:(128)word)
     (k5:(128)word)
     (k6:(128)word)
     (k7:(128)word)
     (k8:(128)word)
     (k9:(128)word)
     (k10:(128)word)
     (k11:(128)word)
     (k12:(128)word)
    (k13:(128)word)))
    (k14:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q3:(armstate,(128)word)component)
    (s:armstate) =
    (word_join:(64)word->(64)word->(128)word)
    ((word_join:(32)word->(32)word->(64)word)
     ((word_join:(16)word->(16)word->(32)word)
      ((word_join:(8)word->(8)word->(16)word)
       ((word_subword:(32)word->num#num->(8)word)
        ((word_add:(32)word->(32)word->(32)word)
         ((word_join:(16)word->(16)word->(32)word)
          ((word_join:(8)word->(8)word->(16)word)
           ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word)
           (96,8))
          ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word)
          (104,8)))
         ((word_join:(8)word->(8)word->(16)word)
          ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word)
          (112,8))
         ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word)
         (120,8))))
        ((word:num->(32)word) 11))
       (0,8))
      ((word_subword:(32)word->num#num->(8)word)
       ((word_add:(32)word->(32)word->(32)word)
        ((word_join:(16)word->(16)word->(32)word)
         ((word_join:(8)word->(8)word->(16)word)
          ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word)
          (96,8))
         ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word)
         (104,8)))
        ((word_join:(8)word->(8)word->(16)word)
         ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word)
         (112,8))
        ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (120,8))))
       ((word:num->(32)word) 11))
      (8,8)))
     ((word_join:(8)word->(8)word->(16)word)
      ((word_subword:(32)word->num#num->(8)word)
       ((word_add:(32)word->(32)word->(32)word)
        ((word_join:(16)word->(16)word->(32)word)
         ((word_join:(8)word->(8)word->(16)word)
          ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word)
          (96,8))
         ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word)
         (104,8)))
        ((word_join:(8)word->(8)word->(16)word)
         ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word)
         (112,8))
        ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (120,8))))
       ((word:num->(32)word) 11))
      (16,8))
     ((word_subword:(32)word->num#num->(8)word)
      ((word_add:(32)word->(32)word->(32)word)
       ((word_join:(16)word->(16)word->(32)word)
        ((word_join:(8)word->(8)word->(16)word)
         ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (96,8))
        ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (104,8)))
       ((word_join:(8)word->(8)word->(16)word)
        ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (112,8))
       ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (120,8))))
      ((word:num->(32)word) 11))
     (24,8))))
    ((word_join:(16)word->(16)word->(32)word)
     ((word_join:(8)word->(8)word->(16)word)
      ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (88,8))
     ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (80,8)))
    ((word_join:(8)word->(8)word->(16)word)
     ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (72,8))
    ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (64,8)))))
    ((word_join:(32)word->(32)word->(64)word)
     ((word_join:(16)word->(16)word->(32)word)
      ((word_join:(8)word->(8)word->(16)word)
       ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (56,8))
      ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (48,8)))
     ((word_join:(8)word->(8)word->(16)word)
      ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (40,8))
     ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (32,8))))
    ((word_join:(16)word->(16)word->(32)word)
     ((word_join:(8)word->(8)word->(16)word)
      ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (24,8))
     ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (16,8)))
    ((word_join:(8)word->(8)word->(16)word)
     ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (8,8))
    ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (0,8))))) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (out_p:(64)word)
     ((word:num->(64)word) 32)))
    (s:armstate) =
    (word_xor:(128)word->(128)word->(128)word)
    ((word_xor:(128)word->(128)word->(128)word)
     ((bytes_to_int128:((8)word)list->(128)word)
     ((SUB_LIST:num#num->((8)word)list->((8)word)list) (32,16)
     (ibytes:((8)word)list)))
    ((aes13:(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word)
     ((gcm_ctr_inc:(128)word->(128)word)
     ((gcm_ctr_inc:(128)word->(128)word) (ctr0:(128)word)))
     (k0:(128)word)
     (k1:(128)word)
     (k2:(128)word)
     (k3:(128)word)
     (k4:(128)word)
     (k5:(128)word)
     (k6:(128)word)
     (k7:(128)word)
     (k8:(128)word)
     (k9:(128)word)
     (k10:(128)word)
     (k11:(128)word)
     (k12:(128)word)
    (k13:(128)word)))
    (k14:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (out_p:(64)word)
     ((word:num->(64)word) 48)))
    (s:armstate) =
    (word_xor:(128)word->(128)word->(128)word)
    ((word_xor:(128)word->(128)word->(128)word)
     ((bytes_to_int128:((8)word)list->(128)word)
     ((SUB_LIST:num#num->((8)word)list->((8)word)list) (48,16)
     (ibytes:((8)word)list)))
    ((aes13:(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word)
     ((gcm_ctr_inc:(128)word->(128)word)
     ((gcm_ctr_inc:(128)word->(128)word)
     ((gcm_ctr_inc:(128)word->(128)word) (ctr0:(128)word))))
     (k0:(128)word)
     (k1:(128)word)
     (k2:(128)word)
     (k3:(128)word)
     (k4:(128)word)
     (k5:(128)word)
     (k6:(128)word)
     (k7:(128)word)
     (k8:(128)word)
     (k9:(128)word)
     (k10:(128)word)
     (k11:(128)word)
     (k12:(128)word)
    (k13:(128)word)))
    (k14:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q0:(armstate,(128)word)component)
    (s:armstate) =
    (word_join:(64)word->(64)word->(128)word)
    ((word_join:(32)word->(32)word->(64)word)
     ((word_join:(16)word->(16)word->(32)word)
      ((word_join:(8)word->(8)word->(16)word)
       ((word_subword:(32)word->num#num->(8)word)
        ((word_add:(32)word->(32)word->(32)word)
         ((word_join:(16)word->(16)word->(32)word)
          ((word_join:(8)word->(8)word->(16)word)
           ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word)
           (96,8))
          ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word)
          (104,8)))
         ((word_join:(8)word->(8)word->(16)word)
          ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word)
          (112,8))
         ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word)
         (120,8))))
        ((word:num->(32)word) 8))
       (0,8))
      ((word_subword:(32)word->num#num->(8)word)
       ((word_add:(32)word->(32)word->(32)word)
        ((word_join:(16)word->(16)word->(32)word)
         ((word_join:(8)word->(8)word->(16)word)
          ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word)
          (96,8))
         ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word)
         (104,8)))
        ((word_join:(8)word->(8)word->(16)word)
         ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word)
         (112,8))
        ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (120,8))))
       ((word:num->(32)word) 8))
      (8,8)))
     ((word_join:(8)word->(8)word->(16)word)
      ((word_subword:(32)word->num#num->(8)word)
       ((word_add:(32)word->(32)word->(32)word)
        ((word_join:(16)word->(16)word->(32)word)
         ((word_join:(8)word->(8)word->(16)word)
          ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word)
          (96,8))
         ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word)
         (104,8)))
        ((word_join:(8)word->(8)word->(16)word)
         ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word)
         (112,8))
        ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (120,8))))
       ((word:num->(32)word) 8))
      (16,8))
     ((word_subword:(32)word->num#num->(8)word)
      ((word_add:(32)word->(32)word->(32)word)
       ((word_join:(16)word->(16)word->(32)word)
        ((word_join:(8)word->(8)word->(16)word)
         ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (96,8))
        ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (104,8)))
       ((word_join:(8)word->(8)word->(16)word)
        ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (112,8))
       ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (120,8))))
      ((word:num->(32)word) 8))
     (24,8))))
    ((word_join:(16)word->(16)word->(32)word)
     ((word_join:(8)word->(8)word->(16)word)
      ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (88,8))
     ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (80,8)))
    ((word_join:(8)word->(8)word->(16)word)
     ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (72,8))
    ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (64,8)))))
    ((word_join:(32)word->(32)word->(64)word)
     ((word_join:(16)word->(16)word->(32)word)
      ((word_join:(8)word->(8)word->(16)word)
       ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (56,8))
      ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (48,8)))
     ((word_join:(8)word->(8)word->(16)word)
      ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (40,8))
     ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (32,8))))
    ((word_join:(16)word->(16)word->(32)word)
     ((word_join:(8)word->(8)word->(16)word)
      ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (24,8))
     ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (16,8)))
    ((word_join:(8)word->(8)word->(16)word)
     ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (8,8))
    ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (0,8))))) /\
    ((read:(armstate,bool)component->armstate->bool)
     (NF:(armstate,bool)component)
     (s:armstate) <=>
     (ival:(64)word->int)
     ((word_sub:(64)word->(64)word->(64)word)
      ((word_add:(64)word->(64)word->(64)word) (in_p:(64)word)
      ((word:num->(64)word) 128))
     ((word_add:(64)word->(64)word->(64)word)
      ((word:num->(64)word) (128 * ((nblk:num) - 1) DIV 8))
     (in_p:(64)word))) <
     (int_of_num:num->int)0) /\
    ((read:(armstate,bool)component->armstate->bool)
     (ZF:(armstate,bool)component)
     (s:armstate) <=>
     (val:(64)word->num)
     ((word_sub:(64)word->(64)word->(64)word)
      ((word_add:(64)word->(64)word->(64)word) (in_p:(64)word)
      ((word:num->(64)word) 128))
     ((word_add:(64)word->(64)word->(64)word)
      ((word:num->(64)word) (128 * ((nblk:num) - 1) DIV 8))
     (in_p:(64)word))) =
     0) /\
    ((read:(armstate,bool)component->armstate->bool)
     (CF:(armstate,bool)component)
     (s:armstate) <=>
     (val:(64)word->num)
     ((word_add:(64)word->(64)word->(64)word)
      ((word:num->(64)word) (128 * ((nblk:num) - 1) DIV 8))
     (in_p:(64)word)) <=
     (val:(64)word->num)
     ((word_add:(64)word->(64)word->(64)word) (in_p:(64)word)
     ((word:num->(64)word) 128))) /\
    ((read:(armstate,bool)component->armstate->bool)
     (VF:(armstate,bool)component)
     (s:armstate) <=>
     ~((ival:(64)word->int)
       ((word_add:(64)word->(64)word->(64)word) (in_p:(64)word)
       ((word:num->(64)word) 128)) -
       (ival:(64)word->int)
       ((word_add:(64)word->(64)word->(64)word)
        ((word:num->(64)word) (128 * ((nblk:num) - 1) DIV 8))
       (in_p:(64)word)) =
       (ival:(64)word->int)
       ((word_sub:(64)word->(64)word->(64)word)
        ((word_add:(64)word->(64)word->(64)word) (in_p:(64)word)
        ((word:num->(64)word) 128))
       ((word_add:(64)word->(64)word->(64)word)
        ((word:num->(64)word) (128 * ((nblk:num) - 1) DIV 8))
       (in_p:(64)word))))) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q12:(armstate,(128)word)component)
    (s:armstate) =
    (bytes_to_int128:((8)word)list->(128)word)
    ((SUB_LIST:num#num->((8)word)list->((8)word)list) (64,16)
    (ibytes:((8)word)list)) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q13:(armstate,(128)word)component)
    (s:armstate) =
    (bytes_to_int128:((8)word)list->(128)word)
    ((SUB_LIST:num#num->((8)word)list->((8)word)list) (80,16)
    (ibytes:((8)word)list)) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q8:(armstate,(128)word)component)
    (s:armstate) =
    (bytes_to_int128:((8)word)list->(128)word)
    ((SUB_LIST:num#num->((8)word)list->((8)word)list) (0,16)
    (ibytes:((8)word)list)) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q9:(armstate,(128)word)component)
    (s:armstate) =
    (bytes_to_int128:((8)word)list->(128)word)
    ((SUB_LIST:num#num->((8)word)list->((8)word)list) (16,16)
    (ibytes:((8)word)list)) /\
    (read:(armstate,(64)word)component->armstate->(64)word)
    (X5:(armstate,(64)word)component)
    (s:armstate) =
    (word_add:(64)word->(64)word->(64)word)
    ((word:num->(64)word) (128 * ((nblk:num) - 1) DIV 8))
    (in_p:(64)word) /\
    (read:(armstate,(64)word)component->armstate->(64)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes64:(64)word->((64)word->(8)word,(64)word)component)
     ((word_add:(64)word->(64)word->(64)word) (stackpointer:(64)word)
     ((word:num->(64)word) 64)))
    (s:armstate) =
    (word:num->(64)word) 13979173243358019584 /\
    (read:(armstate,(64)word)component->armstate->(64)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes64:(64)word->((64)word->(8)word,(64)word)component)
     ((word_add:(64)word->(64)word->(64)word) (stackpointer:(64)word)
     ((word:num->(64)word) 72)))
    (s:armstate) =
    (word:num->(64)word) 0 /\
    (read:(armstate,(64)word)component->armstate->(64)word)
    (X11:(armstate,(64)word)component)
    (s:armstate) =
    (key_p:(64)word) /\
    (read:(armstate,(64)word)component->armstate->(64)word)
    (X9:(armstate,(64)word)component)
    (s:armstate) =
    (word:num->(64)word) (16 * (nblk:num)) /\
    (read:(armstate,(64)word)component->armstate->(64)word)
    (SP:(armstate,(64)word)component)
    (s:armstate) =
    (stackpointer:(64)word) /\
    (read:(armstate,(64)word)component->armstate->(64)word)
    (X1:(armstate,(64)word)component)
    (s:armstate) =
    (word:num->(64)word) (128 * (nblk:num)) /\
    (read:(armstate,(64)word)component->armstate->(64)word)
    (X3:(armstate,(64)word)component)
    (s:armstate) =
    (xi_p:(64)word) /\
    (read:(armstate,(64)word)component->armstate->(64)word)
    (X6:(armstate,(64)word)component)
    (s:armstate) =
    (htbl_p:(64)word) /\
    (read:(armstate,(64)word)component->armstate->(64)word)
    (X16:(armstate,(64)word)component)
    (s:armstate) =
    (ivec_p:(64)word) /\
    (read:(armstate,(64)word)component->armstate->(64)word)
    (X10:(armstate,(64)word)component)
    (s:armstate) =
    (word_add:(64)word->(64)word->(64)word) (stackpointer:(64)word)
    ((word:num->(64)word) 64) /\
    (read:(armstate,(64)word)component->armstate->(64)word)
    (X15:(armstate,(64)word)component)
    (s:armstate) =
    (word:num->(64)word) 4294967296 /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q31:(armstate,(128)word)component)
    (s:armstate) =
    (word:num->(128)word) 79228162514264337593543950336 /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q19:(armstate,(128)word)component)
    (s:armstate) =
    (word_bytereverse:(128)word->(128)word) (xi:(128)word) /\
    (read:(armstate,(64)word)component->armstate->(64)word)
    (X4:(armstate,(64)word)component)
    (s:armstate) =
    (word_add:(64)word->(64)word->(64)word) (in_p:(64)word)
    ((word:num->(64)word) (16 * (nblk:num))) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q27:(armstate,(128)word)component)
    (s:armstate) =
    (k13:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q26:(armstate,(128)word)component)
    (s:armstate) =
    (k12:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q28:(armstate,(128)word)component)
    (s:armstate) =
    (k14:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q11:(armstate,(128)word)component)
    (s:armstate) =
    (bytes_to_int128:((8)word)list->(128)word)
    ((SUB_LIST:num#num->((8)word)list->((8)word)list) (48,16)
    (ibytes:((8)word)list)) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q10:(armstate,(128)word)component)
    (s:armstate) =
    (bytes_to_int128:((8)word)list->(128)word)
    ((SUB_LIST:num#num->((8)word)list->((8)word)list) (32,16)
    (ibytes:((8)word)list)) /\
    (read:(armstate,(64)word)component->armstate->(64)word)
    (X0:(armstate,(64)word)component)
    (s:armstate) =
    (word_add:(64)word->(64)word->(64)word) (in_p:(64)word)
    ((word:num->(64)word) 128) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q15:(armstate,(128)word)component)
    (s:armstate) =
    (bytes_to_int128:((8)word)list->(128)word)
    ((SUB_LIST:num#num->((8)word)list->((8)word)list) (112,16)
    (ibytes:((8)word)list)) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q14:(armstate,(128)word)component)
    (s:armstate) =
    (bytes_to_int128:((8)word)list->(128)word)
    ((SUB_LIST:num#num->((8)word)list->((8)word)list) (96,16)
    (ibytes:((8)word)list)) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (out_p:(64)word)
     ((word:num->(64)word) 16)))
    (s:armstate) =
    (word_xor:(128)word->(128)word->(128)word)
    ((word_xor:(128)word->(128)word->(128)word)
     ((bytes_to_int128:((8)word)list->(128)word)
     ((SUB_LIST:num#num->((8)word)list->((8)word)list) (16,16)
     (ibytes:((8)word)list)))
    ((aes13:(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word)
     ((gcm_ctr_inc:(128)word->(128)word) (ctr0:(128)word))
     (k0:(128)word)
     (k1:(128)word)
     (k2:(128)word)
     (k3:(128)word)
     (k4:(128)word)
     (k5:(128)word)
     (k6:(128)word)
     (k7:(128)word)
     (k8:(128)word)
     (k9:(128)word)
     (k10:(128)word)
     (k11:(128)word)
     (k12:(128)word)
    (k13:(128)word)))
    (k14:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     (out_p:(64)word))
    (s:armstate) =
    (word_xor:(128)word->(128)word->(128)word)
    ((word_xor:(128)word->(128)word->(128)word)
     ((bytes_to_int128:((8)word)list->(128)word)
     ((SUB_LIST:num#num->((8)word)list->((8)word)list) (0,16)
     (ibytes:((8)word)list)))
    ((aes13:(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word)
     (ctr0:(128)word)
     (k0:(128)word)
     (k1:(128)word)
     (k2:(128)word)
     (k3:(128)word)
     (k4:(128)word)
     (k5:(128)word)
     (k6:(128)word)
     (k7:(128)word)
     (k8:(128)word)
     (k9:(128)word)
     (k10:(128)word)
     (k11:(128)word)
     (k12:(128)word)
    (k13:(128)word)))
    (k14:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q5:(armstate,(128)word)component)
    (s:armstate) =
    (word_xor:(128)word->(128)word->(128)word)
    ((word_xor:(128)word->(128)word->(128)word)
     ((bytes_to_int128:((8)word)list->(128)word)
     ((SUB_LIST:num#num->((8)word)list->((8)word)list) (80,16)
     (ibytes:((8)word)list)))
    ((aes13:(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word)
     ((gcm_ctr_inc:(128)word->(128)word)
     ((gcm_ctr_inc:(128)word->(128)word)
     ((gcm_ctr_inc:(128)word->(128)word)
     ((gcm_ctr_inc:(128)word->(128)word)
     ((gcm_ctr_inc:(128)word->(128)word) (ctr0:(128)word))))))
     (k0:(128)word)
     (k1:(128)word)
     (k2:(128)word)
     (k3:(128)word)
     (k4:(128)word)
     (k5:(128)word)
     (k6:(128)word)
     (k7:(128)word)
     (k8:(128)word)
     (k9:(128)word)
     (k10:(128)word)
     (k11:(128)word)
     (k12:(128)word)
    (k13:(128)word)))
    (k14:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q1:(armstate,(128)word)component)
    (s:armstate) =
    (word_join:(64)word->(64)word->(128)word)
    ((word_join:(32)word->(32)word->(64)word)
     ((word_join:(16)word->(16)word->(32)word)
      ((word_join:(8)word->(8)word->(16)word)
       ((word_subword:(32)word->num#num->(8)word)
        ((word_add:(32)word->(32)word->(32)word)
         ((word_join:(16)word->(16)word->(32)word)
          ((word_join:(8)word->(8)word->(16)word)
           ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word)
           (96,8))
          ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word)
          (104,8)))
         ((word_join:(8)word->(8)word->(16)word)
          ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word)
          (112,8))
         ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word)
         (120,8))))
        ((word:num->(32)word) 9))
       (0,8))
      ((word_subword:(32)word->num#num->(8)word)
       ((word_add:(32)word->(32)word->(32)word)
        ((word_join:(16)word->(16)word->(32)word)
         ((word_join:(8)word->(8)word->(16)word)
          ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word)
          (96,8))
         ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word)
         (104,8)))
        ((word_join:(8)word->(8)word->(16)word)
         ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word)
         (112,8))
        ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (120,8))))
       ((word:num->(32)word) 9))
      (8,8)))
     ((word_join:(8)word->(8)word->(16)word)
      ((word_subword:(32)word->num#num->(8)word)
       ((word_add:(32)word->(32)word->(32)word)
        ((word_join:(16)word->(16)word->(32)word)
         ((word_join:(8)word->(8)word->(16)word)
          ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word)
          (96,8))
         ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word)
         (104,8)))
        ((word_join:(8)word->(8)word->(16)word)
         ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word)
         (112,8))
        ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (120,8))))
       ((word:num->(32)word) 9))
      (16,8))
     ((word_subword:(32)word->num#num->(8)word)
      ((word_add:(32)word->(32)word->(32)word)
       ((word_join:(16)word->(16)word->(32)word)
        ((word_join:(8)word->(8)word->(16)word)
         ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (96,8))
        ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (104,8)))
       ((word_join:(8)word->(8)word->(16)word)
        ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (112,8))
       ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (120,8))))
      ((word:num->(32)word) 9))
     (24,8))))
    ((word_join:(16)word->(16)word->(32)word)
     ((word_join:(8)word->(8)word->(16)word)
      ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (88,8))
     ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (80,8)))
    ((word_join:(8)word->(8)word->(16)word)
     ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (72,8))
    ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (64,8)))))
    ((word_join:(32)word->(32)word->(64)word)
     ((word_join:(16)word->(16)word->(32)word)
      ((word_join:(8)word->(8)word->(16)word)
       ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (56,8))
      ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (48,8)))
     ((word_join:(8)word->(8)word->(16)word)
      ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (40,8))
     ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (32,8))))
    ((word_join:(16)word->(16)word->(32)word)
     ((word_join:(8)word->(8)word->(16)word)
      ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (24,8))
     ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (16,8)))
    ((word_join:(8)word->(8)word->(16)word)
     ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (8,8))
    ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (0,8))))) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q2:(armstate,(128)word)component)
    (s:armstate) =
    (word_join:(64)word->(64)word->(128)word)
    ((word_join:(32)word->(32)word->(64)word)
     ((word_join:(16)word->(16)word->(32)word)
      ((word_join:(8)word->(8)word->(16)word)
       ((word_subword:(32)word->num#num->(8)word)
        ((word_add:(32)word->(32)word->(32)word)
         ((word_join:(16)word->(16)word->(32)word)
          ((word_join:(8)word->(8)word->(16)word)
           ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word)
           (96,8))
          ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word)
          (104,8)))
         ((word_join:(8)word->(8)word->(16)word)
          ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word)
          (112,8))
         ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word)
         (120,8))))
        ((word:num->(32)word) 10))
       (0,8))
      ((word_subword:(32)word->num#num->(8)word)
       ((word_add:(32)word->(32)word->(32)word)
        ((word_join:(16)word->(16)word->(32)word)
         ((word_join:(8)word->(8)word->(16)word)
          ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word)
          (96,8))
         ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word)
         (104,8)))
        ((word_join:(8)word->(8)word->(16)word)
         ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word)
         (112,8))
        ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (120,8))))
       ((word:num->(32)word) 10))
      (8,8)))
     ((word_join:(8)word->(8)word->(16)word)
      ((word_subword:(32)word->num#num->(8)word)
       ((word_add:(32)word->(32)word->(32)word)
        ((word_join:(16)word->(16)word->(32)word)
         ((word_join:(8)word->(8)word->(16)word)
          ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word)
          (96,8))
         ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word)
         (104,8)))
        ((word_join:(8)word->(8)word->(16)word)
         ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word)
         (112,8))
        ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (120,8))))
       ((word:num->(32)word) 10))
      (16,8))
     ((word_subword:(32)word->num#num->(8)word)
      ((word_add:(32)word->(32)word->(32)word)
       ((word_join:(16)word->(16)word->(32)word)
        ((word_join:(8)word->(8)word->(16)word)
         ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (96,8))
        ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (104,8)))
       ((word_join:(8)word->(8)word->(16)word)
        ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (112,8))
       ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (120,8))))
      ((word:num->(32)word) 10))
     (24,8))))
    ((word_join:(16)word->(16)word->(32)word)
     ((word_join:(8)word->(8)word->(16)word)
      ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (88,8))
     ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (80,8)))
    ((word_join:(8)word->(8)word->(16)word)
     ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (72,8))
    ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (64,8)))))
    ((word_join:(32)word->(32)word->(64)word)
     ((word_join:(16)word->(16)word->(32)word)
      ((word_join:(8)word->(8)word->(16)word)
       ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (56,8))
      ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (48,8)))
     ((word_join:(8)word->(8)word->(16)word)
      ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (40,8))
     ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (32,8))))
    ((word_join:(16)word->(16)word->(32)word)
     ((word_join:(8)word->(8)word->(16)word)
      ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (24,8))
     ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (16,8)))
    ((word_join:(8)word->(8)word->(16)word)
     ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (8,8))
    ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (0,8))))) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q6:(armstate,(128)word)component)
    (s:armstate) =
    (word_xor:(128)word->(128)word->(128)word)
    ((word_xor:(128)word->(128)word->(128)word)
     ((bytes_to_int128:((8)word)list->(128)word)
     ((SUB_LIST:num#num->((8)word)list->((8)word)list) (96,16)
     (ibytes:((8)word)list)))
    ((aes13:(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word)
     ((gcm_ctr_inc:(128)word->(128)word)
     ((gcm_ctr_inc:(128)word->(128)word)
     ((gcm_ctr_inc:(128)word->(128)word)
     ((gcm_ctr_inc:(128)word->(128)word)
     ((gcm_ctr_inc:(128)word->(128)word)
     ((gcm_ctr_inc:(128)word->(128)word) (ctr0:(128)word)))))))
     (k0:(128)word)
     (k1:(128)word)
     (k2:(128)word)
     (k3:(128)word)
     (k4:(128)word)
     (k5:(128)word)
     (k6:(128)word)
     (k7:(128)word)
     (k8:(128)word)
     (k9:(128)word)
     (k10:(128)word)
     (k11:(128)word)
     (k12:(128)word)
    (k13:(128)word)))
    (k14:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q7:(armstate,(128)word)component)
    (s:armstate) =
    (word_xor:(128)word->(128)word->(128)word)
    ((word_xor:(128)word->(128)word->(128)word)
     ((bytes_to_int128:((8)word)list->(128)word)
     ((SUB_LIST:num#num->((8)word)list->((8)word)list) (112,16)
     (ibytes:((8)word)list)))
    ((aes13:(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word)
     ((gcm_ctr_inc:(128)word->(128)word)
     ((gcm_ctr_inc:(128)word->(128)word)
     ((gcm_ctr_inc:(128)word->(128)word)
     ((gcm_ctr_inc:(128)word->(128)word)
     ((gcm_ctr_inc:(128)word->(128)word)
     ((gcm_ctr_inc:(128)word->(128)word)
     ((gcm_ctr_inc:(128)word->(128)word) (ctr0:(128)word))))))))
     (k0:(128)word)
     (k1:(128)word)
     (k2:(128)word)
     (k3:(128)word)
     (k4:(128)word)
     (k5:(128)word)
     (k6:(128)word)
     (k7:(128)word)
     (k8:(128)word)
     (k9:(128)word)
     (k10:(128)word)
     (k11:(128)word)
     (k12:(128)word)
    (k13:(128)word)))
    (k14:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q4:(armstate,(128)word)component)
    (s:armstate) =
    (word_join:(64)word->(64)word->(128)word)
    ((word_join:(32)word->(32)word->(64)word)
     ((word_join:(16)word->(16)word->(32)word)
      ((word_join:(8)word->(8)word->(16)word)
       ((word_subword:(32)word->num#num->(8)word)
        ((word_add:(32)word->(32)word->(32)word)
         ((word_join:(16)word->(16)word->(32)word)
          ((word_join:(8)word->(8)word->(16)word)
           ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word)
           (96,8))
          ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word)
          (104,8)))
         ((word_join:(8)word->(8)word->(16)word)
          ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word)
          (112,8))
         ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word)
         (120,8))))
        ((word:num->(32)word) 12))
       (0,8))
      ((word_subword:(32)word->num#num->(8)word)
       ((word_add:(32)word->(32)word->(32)word)
        ((word_join:(16)word->(16)word->(32)word)
         ((word_join:(8)word->(8)word->(16)word)
          ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word)
          (96,8))
         ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word)
         (104,8)))
        ((word_join:(8)word->(8)word->(16)word)
         ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word)
         (112,8))
        ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (120,8))))
       ((word:num->(32)word) 12))
      (8,8)))
     ((word_join:(8)word->(8)word->(16)word)
      ((word_subword:(32)word->num#num->(8)word)
       ((word_add:(32)word->(32)word->(32)word)
        ((word_join:(16)word->(16)word->(32)word)
         ((word_join:(8)word->(8)word->(16)word)
          ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word)
          (96,8))
         ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word)
         (104,8)))
        ((word_join:(8)word->(8)word->(16)word)
         ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word)
         (112,8))
        ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (120,8))))
       ((word:num->(32)word) 12))
      (16,8))
     ((word_subword:(32)word->num#num->(8)word)
      ((word_add:(32)word->(32)word->(32)word)
       ((word_join:(16)word->(16)word->(32)word)
        ((word_join:(8)word->(8)word->(16)word)
         ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (96,8))
        ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (104,8)))
       ((word_join:(8)word->(8)word->(16)word)
        ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (112,8))
       ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (120,8))))
      ((word:num->(32)word) 12))
     (24,8))))
    ((word_join:(16)word->(16)word->(32)word)
     ((word_join:(8)word->(8)word->(16)word)
      ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (88,8))
     ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (80,8)))
    ((word_join:(8)word->(8)word->(16)word)
     ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (72,8))
    ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (64,8)))))
    ((word_join:(32)word->(32)word->(64)word)
     ((word_join:(16)word->(16)word->(32)word)
      ((word_join:(8)word->(8)word->(16)word)
       ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (56,8))
      ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (48,8)))
     ((word_join:(8)word->(8)word->(16)word)
      ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (40,8))
     ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (32,8))))
    ((word_join:(16)word->(16)word->(32)word)
     ((word_join:(8)word->(8)word->(16)word)
      ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (24,8))
     ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (16,8)))
    ((word_join:(8)word->(8)word->(16)word)
     ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (8,8))
    ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (0,8)))))|};;

(* input lanes 0..7 established at s267 (the >=9 post-branch leg reads blocks
   0..7 via the ldp q8-q15 at 0x448+); follows from the s267 input-memory fact.
   : state renamed s259->s265 (front prefix +6 after counter flatten), then
   FUSED SPLICE (STEP 4) shifted the prefix-end +2 further (s265->s267).  The
   consumer WBN_FRONT_PREFIX does ENSURES_INIT_TAC "s267"; the SPECL state MUST
   match it or ASM_REWRITE_TAC cannot discharge INPUT_BYTES_TO_BYTE128_LANES's
   input-memory antecedent, leaving `lth` an implication -> SPEC raises. *)
let WBN_LANES259_GE9_TAC =
  SUBGOAL_THEN `SUB_LIST (0, 16 * nblk) (ibytes:byte list) = ibytes` ASSUME_TAC THENL
   [MATCH_MP_TAC SUB_LIST_LENGTH_IMPLIES THEN ASM_REWRITE_TAC[LE_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!k. k < 8 ==> read (memory :> bytes128 (word_add in_p (word (16 * k)))) s267 =
                  bytes_to_int128 (SUB_LIST (16 * k, 16) (ibytes:byte list))`
   MP_TAC THENL
   [MP_TAC(SPECL [`nblk:num`; `in_p:int64`; `ibytes:byte list`; `s267:armstate`]
      INPUT_BYTES_TO_BYTE128_LANES) THEN
    ASM_REWRITE_TAC[LE_REFL] THEN
    DISCH_THEN(fun lth -> X_GEN_TAC `k:num` THEN DISCH_TAC THEN
      MP_TAC(SPEC `k:num` lth) THEN ANTS_TAC THENL
       [MP_TAC(ASSUME `k < 8`) THEN NBLK_ARITH_GE9_TAC; REWRITE_TAC[]]);
    DISCH_THEN(fun lth ->
      EVERY(map (fun i ->
        ASSUME_TAC(CONV_RULE(DEPTH_CONV NUM_RED_CONV)
          (MP (SPEC (mk_small_numeral i) lth)
              (ARITH_RULE(mk_binop `(<):num->num->bool` (mk_small_numeral i) `8`)))))
        (0--7)))];;

(* FRONT-PREFIX (>=9 band): chain the shared WBN_FRONT_PREFIX_259 (0x20->0x44c)
   via ENSURES_TRANS_SIMPLE, then the 0x44c b.ge FALLS THROUGH (nblk>=9, via
   WB_LOOPENTER_FLAGS_GE9) + steps 268..295 to s295 (pc+1212).
   FUSED SPLICE (STEP 4): prefix now ends at s267 (was s265); b.ge@0x44c step
   268 (was 266); tail 269..295 (was 267..293); pc+1204 -> pc+1212. *)
let WBN_FRONT_PREFIX = prove(mk_wbn_prefix_goal wbn_front_prefix_postcond,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC ENSURES_TRANS_SIMPLE THEN
  EXISTS_TAC wbn_front_prefix259_postcond THEN
  CONJ_TAC THENL
   [REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN MAYCHANGE_IDEMPOT_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC WBN_FRONT_PREFIX_259 THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ENSURES_INIT_TAC "s267" THEN RULE_ASSUM_TAC(REWRITE_RULE[WB_MC_LEN]) THEN
    WBN_LANES259_GE9_TAC THEN WBN_RESOLVE_42C_GE9_TAC THEN
    ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (268--268) THEN
    EVERY(map (fun i -> ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (i--i) THEN
               GCM_SIMD_SIMPLIFY_TAC THEN DISCARD_STALE_Q30_TAC) (269--295)) THEN
    wb_front_fold_tac THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[WORD_ADD_0] THEN
    REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    REPEAT CONJ_TAC THEN MONOTONE_MAYCHANGE_TAC]);;

(* The s288 postcondition (the i=0 loop invariant), embedded as a fully
   type-annotated literal so the front simulates ONCE (in the WBN_FRONT_BUF
   proof below) instead of TWICE.  The old harvest pass (kept in git history)
   re-ran the same 288-step front sim purely to compute this term, wasting
   ~250s per cold load -- exactly the <=8-block chain's wb_front_postcond optimisation
   applied here to the mainloop front.
   The literal is aconv-identical to the harvested term (verified:
   reparse + aconv + WBN_FRONT_BUF re-proved hyps=0 from it).
   REGENERATION (if the front or its keep-profile changes): re-enable the
   harvest below, then print the result with print_types_of_subterms := 2 and
   verify aconv against the folded harvested term (this postcond has no bare
   & integer literals, so no int_of_num substitution is needed):
     let wbn_front_postcond_i0 =
       let min_goal = mk_wbn_front_goal `\s:armstate. read PC s = word (pc + 0x4c0)` in
       let _ = g min_goal in
       let _ = e (WBN_FRONT_FULL_TAC THEN wb_front_fold_tac) in
       let (asl288,_) = top_goal() in
       let pc = build_state_postcond_tms2 "s288" asl288 in
       let _ = b() in pc;; *)
let wbn_front_postcond_i0 = parse_term {|\(s:armstate).
    (aligned_bytes_loaded:armstate->(64)word->((8)word)list->bool)
    (s:armstate)
    ((word:num->(64)word) (pc:num))
    (aesv8_gcm_8x_dec_256_wb_mc:((8)word)list) /\
    (read:(armstate,(64)word)component->armstate->(64)word)
    (PC:(armstate,(64)word)component)
    (s:armstate) =
    (word:num->(64)word) ((pc:num) + 1216) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q4:(armstate,(128)word)component)
    (s:armstate) =
    (word_join:(64)word->(64)word->(128)word)
    ((word_join:(32)word->(32)word->(64)word)
     ((word_join:(16)word->(16)word->(32)word)
      ((word_join:(8)word->(8)word->(16)word)
       ((word_subword:(32)word->num#num->(8)word)
        ((word_add:(32)word->(32)word->(32)word)
         ((word_join:(16)word->(16)word->(32)word)
          ((word_join:(8)word->(8)word->(16)word)
           ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word)
           (96,8))
          ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word)
          (104,8)))
         ((word_join:(8)word->(8)word->(16)word)
          ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word)
          (112,8))
         ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word)
         (120,8))))
        ((word:num->(32)word) 12))
       (0,8))
      ((word_subword:(32)word->num#num->(8)word)
       ((word_add:(32)word->(32)word->(32)word)
        ((word_join:(16)word->(16)word->(32)word)
         ((word_join:(8)word->(8)word->(16)word)
          ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word)
          (96,8))
         ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word)
         (104,8)))
        ((word_join:(8)word->(8)word->(16)word)
         ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word)
         (112,8))
        ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (120,8))))
       ((word:num->(32)word) 12))
      (8,8)))
     ((word_join:(8)word->(8)word->(16)word)
      ((word_subword:(32)word->num#num->(8)word)
       ((word_add:(32)word->(32)word->(32)word)
        ((word_join:(16)word->(16)word->(32)word)
         ((word_join:(8)word->(8)word->(16)word)
          ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word)
          (96,8))
         ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word)
         (104,8)))
        ((word_join:(8)word->(8)word->(16)word)
         ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word)
         (112,8))
        ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (120,8))))
       ((word:num->(32)word) 12))
      (16,8))
     ((word_subword:(32)word->num#num->(8)word)
      ((word_add:(32)word->(32)word->(32)word)
       ((word_join:(16)word->(16)word->(32)word)
        ((word_join:(8)word->(8)word->(16)word)
         ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (96,8))
        ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (104,8)))
       ((word_join:(8)word->(8)word->(16)word)
        ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (112,8))
       ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (120,8))))
      ((word:num->(32)word) 12))
     (24,8))))
    ((word_join:(16)word->(16)word->(32)word)
     ((word_join:(8)word->(8)word->(16)word)
      ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (88,8))
     ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (80,8)))
    ((word_join:(8)word->(8)word->(16)word)
     ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (72,8))
    ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (64,8)))))
    ((word_join:(32)word->(32)word->(64)word)
     ((word_join:(16)word->(16)word->(32)word)
      ((word_join:(8)word->(8)word->(16)word)
       ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (56,8))
      ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (48,8)))
     ((word_join:(8)word->(8)word->(16)word)
      ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (40,8))
     ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (32,8))))
    ((word_join:(16)word->(16)word->(32)word)
     ((word_join:(8)word->(8)word->(16)word)
      ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (24,8))
     ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (16,8)))
    ((word_join:(8)word->(8)word->(16)word)
     ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (8,8))
    ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (0,8))))) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q7:(armstate,(128)word)component)
    (s:armstate) =
    (word_xor:(128)word->(128)word->(128)word)
    ((word_xor:(128)word->(128)word->(128)word)
     ((bytes_to_int128:((8)word)list->(128)word)
     ((SUB_LIST:num#num->((8)word)list->((8)word)list) (112,16)
     (ibytes:((8)word)list)))
    ((aes13:(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word)
     ((gcm_ctr_inc:(128)word->(128)word)
     ((gcm_ctr_inc:(128)word->(128)word)
     ((gcm_ctr_inc:(128)word->(128)word)
     ((gcm_ctr_inc:(128)word->(128)word)
     ((gcm_ctr_inc:(128)word->(128)word)
     ((gcm_ctr_inc:(128)word->(128)word)
     ((gcm_ctr_inc:(128)word->(128)word) (ctr0:(128)word))))))))
     (k0:(128)word)
     (k1:(128)word)
     (k2:(128)word)
     (k3:(128)word)
     (k4:(128)word)
     (k5:(128)word)
     (k6:(128)word)
     (k7:(128)word)
     (k8:(128)word)
     (k9:(128)word)
     (k10:(128)word)
     (k11:(128)word)
     (k12:(128)word)
    (k13:(128)word)))
    (k14:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q6:(armstate,(128)word)component)
    (s:armstate) =
    (word_xor:(128)word->(128)word->(128)word)
    ((word_xor:(128)word->(128)word->(128)word)
     ((bytes_to_int128:((8)word)list->(128)word)
     ((SUB_LIST:num#num->((8)word)list->((8)word)list) (96,16)
     (ibytes:((8)word)list)))
    ((aes13:(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word)
     ((gcm_ctr_inc:(128)word->(128)word)
     ((gcm_ctr_inc:(128)word->(128)word)
     ((gcm_ctr_inc:(128)word->(128)word)
     ((gcm_ctr_inc:(128)word->(128)word)
     ((gcm_ctr_inc:(128)word->(128)word)
     ((gcm_ctr_inc:(128)word->(128)word) (ctr0:(128)word)))))))
     (k0:(128)word)
     (k1:(128)word)
     (k2:(128)word)
     (k3:(128)word)
     (k4:(128)word)
     (k5:(128)word)
     (k6:(128)word)
     (k7:(128)word)
     (k8:(128)word)
     (k9:(128)word)
     (k10:(128)word)
     (k11:(128)word)
     (k12:(128)word)
    (k13:(128)word)))
    (k14:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q2:(armstate,(128)word)component)
    (s:armstate) =
    (word_join:(64)word->(64)word->(128)word)
    ((word_join:(32)word->(32)word->(64)word)
     ((word_join:(16)word->(16)word->(32)word)
      ((word_join:(8)word->(8)word->(16)word)
       ((word_subword:(32)word->num#num->(8)word)
        ((word_add:(32)word->(32)word->(32)word)
         ((word_join:(16)word->(16)word->(32)word)
          ((word_join:(8)word->(8)word->(16)word)
           ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word)
           (96,8))
          ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word)
          (104,8)))
         ((word_join:(8)word->(8)word->(16)word)
          ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word)
          (112,8))
         ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word)
         (120,8))))
        ((word:num->(32)word) 10))
       (0,8))
      ((word_subword:(32)word->num#num->(8)word)
       ((word_add:(32)word->(32)word->(32)word)
        ((word_join:(16)word->(16)word->(32)word)
         ((word_join:(8)word->(8)word->(16)word)
          ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word)
          (96,8))
         ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word)
         (104,8)))
        ((word_join:(8)word->(8)word->(16)word)
         ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word)
         (112,8))
        ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (120,8))))
       ((word:num->(32)word) 10))
      (8,8)))
     ((word_join:(8)word->(8)word->(16)word)
      ((word_subword:(32)word->num#num->(8)word)
       ((word_add:(32)word->(32)word->(32)word)
        ((word_join:(16)word->(16)word->(32)word)
         ((word_join:(8)word->(8)word->(16)word)
          ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word)
          (96,8))
         ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word)
         (104,8)))
        ((word_join:(8)word->(8)word->(16)word)
         ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word)
         (112,8))
        ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (120,8))))
       ((word:num->(32)word) 10))
      (16,8))
     ((word_subword:(32)word->num#num->(8)word)
      ((word_add:(32)word->(32)word->(32)word)
       ((word_join:(16)word->(16)word->(32)word)
        ((word_join:(8)word->(8)word->(16)word)
         ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (96,8))
        ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (104,8)))
       ((word_join:(8)word->(8)word->(16)word)
        ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (112,8))
       ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (120,8))))
      ((word:num->(32)word) 10))
     (24,8))))
    ((word_join:(16)word->(16)word->(32)word)
     ((word_join:(8)word->(8)word->(16)word)
      ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (88,8))
     ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (80,8)))
    ((word_join:(8)word->(8)word->(16)word)
     ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (72,8))
    ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (64,8)))))
    ((word_join:(32)word->(32)word->(64)word)
     ((word_join:(16)word->(16)word->(32)word)
      ((word_join:(8)word->(8)word->(16)word)
       ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (56,8))
      ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (48,8)))
     ((word_join:(8)word->(8)word->(16)word)
      ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (40,8))
     ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (32,8))))
    ((word_join:(16)word->(16)word->(32)word)
     ((word_join:(8)word->(8)word->(16)word)
      ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (24,8))
     ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (16,8)))
    ((word_join:(8)word->(8)word->(16)word)
     ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (8,8))
    ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (0,8))))) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q1:(armstate,(128)word)component)
    (s:armstate) =
    (word_join:(64)word->(64)word->(128)word)
    ((word_join:(32)word->(32)word->(64)word)
     ((word_join:(16)word->(16)word->(32)word)
      ((word_join:(8)word->(8)word->(16)word)
       ((word_subword:(32)word->num#num->(8)word)
        ((word_add:(32)word->(32)word->(32)word)
         ((word_join:(16)word->(16)word->(32)word)
          ((word_join:(8)word->(8)word->(16)word)
           ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word)
           (96,8))
          ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word)
          (104,8)))
         ((word_join:(8)word->(8)word->(16)word)
          ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word)
          (112,8))
         ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word)
         (120,8))))
        ((word:num->(32)word) 9))
       (0,8))
      ((word_subword:(32)word->num#num->(8)word)
       ((word_add:(32)word->(32)word->(32)word)
        ((word_join:(16)word->(16)word->(32)word)
         ((word_join:(8)word->(8)word->(16)word)
          ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word)
          (96,8))
         ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word)
         (104,8)))
        ((word_join:(8)word->(8)word->(16)word)
         ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word)
         (112,8))
        ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (120,8))))
       ((word:num->(32)word) 9))
      (8,8)))
     ((word_join:(8)word->(8)word->(16)word)
      ((word_subword:(32)word->num#num->(8)word)
       ((word_add:(32)word->(32)word->(32)word)
        ((word_join:(16)word->(16)word->(32)word)
         ((word_join:(8)word->(8)word->(16)word)
          ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word)
          (96,8))
         ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word)
         (104,8)))
        ((word_join:(8)word->(8)word->(16)word)
         ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word)
         (112,8))
        ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (120,8))))
       ((word:num->(32)word) 9))
      (16,8))
     ((word_subword:(32)word->num#num->(8)word)
      ((word_add:(32)word->(32)word->(32)word)
       ((word_join:(16)word->(16)word->(32)word)
        ((word_join:(8)word->(8)word->(16)word)
         ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (96,8))
        ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (104,8)))
       ((word_join:(8)word->(8)word->(16)word)
        ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (112,8))
       ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (120,8))))
      ((word:num->(32)word) 9))
     (24,8))))
    ((word_join:(16)word->(16)word->(32)word)
     ((word_join:(8)word->(8)word->(16)word)
      ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (88,8))
     ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (80,8)))
    ((word_join:(8)word->(8)word->(16)word)
     ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (72,8))
    ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (64,8)))))
    ((word_join:(32)word->(32)word->(64)word)
     ((word_join:(16)word->(16)word->(32)word)
      ((word_join:(8)word->(8)word->(16)word)
       ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (56,8))
      ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (48,8)))
     ((word_join:(8)word->(8)word->(16)word)
      ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (40,8))
     ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (32,8))))
    ((word_join:(16)word->(16)word->(32)word)
     ((word_join:(8)word->(8)word->(16)word)
      ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (24,8))
     ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (16,8)))
    ((word_join:(8)word->(8)word->(16)word)
     ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (8,8))
    ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (0,8))))) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q5:(armstate,(128)word)component)
    (s:armstate) =
    (word_xor:(128)word->(128)word->(128)word)
    ((word_xor:(128)word->(128)word->(128)word)
     ((bytes_to_int128:((8)word)list->(128)word)
     ((SUB_LIST:num#num->((8)word)list->((8)word)list) (80,16)
     (ibytes:((8)word)list)))
    ((aes13:(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word)
     ((gcm_ctr_inc:(128)word->(128)word)
     ((gcm_ctr_inc:(128)word->(128)word)
     ((gcm_ctr_inc:(128)word->(128)word)
     ((gcm_ctr_inc:(128)word->(128)word)
     ((gcm_ctr_inc:(128)word->(128)word) (ctr0:(128)word))))))
     (k0:(128)word)
     (k1:(128)word)
     (k2:(128)word)
     (k3:(128)word)
     (k4:(128)word)
     (k5:(128)word)
     (k6:(128)word)
     (k7:(128)word)
     (k8:(128)word)
     (k9:(128)word)
     (k10:(128)word)
     (k11:(128)word)
     (k12:(128)word)
    (k13:(128)word)))
    (k14:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     (out_p:(64)word))
    (s:armstate) =
    (word_xor:(128)word->(128)word->(128)word)
    ((word_xor:(128)word->(128)word->(128)word)
     ((bytes_to_int128:((8)word)list->(128)word)
     ((SUB_LIST:num#num->((8)word)list->((8)word)list) (0,16)
     (ibytes:((8)word)list)))
    ((aes13:(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word)
     (ctr0:(128)word)
     (k0:(128)word)
     (k1:(128)word)
     (k2:(128)word)
     (k3:(128)word)
     (k4:(128)word)
     (k5:(128)word)
     (k6:(128)word)
     (k7:(128)word)
     (k8:(128)word)
     (k9:(128)word)
     (k10:(128)word)
     (k11:(128)word)
     (k12:(128)word)
    (k13:(128)word)))
    (k14:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (out_p:(64)word)
     ((word:num->(64)word) 16)))
    (s:armstate) =
    (word_xor:(128)word->(128)word->(128)word)
    ((word_xor:(128)word->(128)word->(128)word)
     ((bytes_to_int128:((8)word)list->(128)word)
     ((SUB_LIST:num#num->((8)word)list->((8)word)list) (16,16)
     (ibytes:((8)word)list)))
    ((aes13:(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word)
     ((gcm_ctr_inc:(128)word->(128)word) (ctr0:(128)word))
     (k0:(128)word)
     (k1:(128)word)
     (k2:(128)word)
     (k3:(128)word)
     (k4:(128)word)
     (k5:(128)word)
     (k6:(128)word)
     (k7:(128)word)
     (k8:(128)word)
     (k9:(128)word)
     (k10:(128)word)
     (k11:(128)word)
     (k12:(128)word)
    (k13:(128)word)))
    (k14:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q14:(armstate,(128)word)component)
    (s:armstate) =
    (bytes_to_int128:((8)word)list->(128)word)
    ((SUB_LIST:num#num->((8)word)list->((8)word)list) (96,16)
    (ibytes:((8)word)list)) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q15:(armstate,(128)word)component)
    (s:armstate) =
    (bytes_to_int128:((8)word)list->(128)word)
    ((SUB_LIST:num#num->((8)word)list->((8)word)list) (112,16)
    (ibytes:((8)word)list)) /\
    (read:(armstate,(64)word)component->armstate->(64)word)
    (X0:(armstate,(64)word)component)
    (s:armstate) =
    (word_add:(64)word->(64)word->(64)word) (in_p:(64)word)
    ((word:num->(64)word) 128) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q10:(armstate,(128)word)component)
    (s:armstate) =
    (bytes_to_int128:((8)word)list->(128)word)
    ((SUB_LIST:num#num->((8)word)list->((8)word)list) (32,16)
    (ibytes:((8)word)list)) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q11:(armstate,(128)word)component)
    (s:armstate) =
    (bytes_to_int128:((8)word)list->(128)word)
    ((SUB_LIST:num#num->((8)word)list->((8)word)list) (48,16)
    (ibytes:((8)word)list)) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q28:(armstate,(128)word)component)
    (s:armstate) =
    (k14:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q26:(armstate,(128)word)component)
    (s:armstate) =
    (k12:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q27:(armstate,(128)word)component)
    (s:armstate) =
    (k13:(128)word) /\
    (read:(armstate,(64)word)component->armstate->(64)word)
    (X4:(armstate,(64)word)component)
    (s:armstate) =
    (word_add:(64)word->(64)word->(64)word) (in_p:(64)word)
    ((word:num->(64)word) (16 * (nblk:num))) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q19:(armstate,(128)word)component)
    (s:armstate) =
    (word_bytereverse:(128)word->(128)word) (xi:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q31:(armstate,(128)word)component)
    (s:armstate) =
    (word:num->(128)word) 79228162514264337593543950336 /\
    (read:(armstate,(64)word)component->armstate->(64)word)
    (X15:(armstate,(64)word)component)
    (s:armstate) =
    (word:num->(64)word) 4294967296 /\
    (read:(armstate,(64)word)component->armstate->(64)word)
    (X10:(armstate,(64)word)component)
    (s:armstate) =
    (word_add:(64)word->(64)word->(64)word) (stackpointer:(64)word)
    ((word:num->(64)word) 64) /\
    (read:(armstate,(64)word)component->armstate->(64)word)
    (X16:(armstate,(64)word)component)
    (s:armstate) =
    (ivec_p:(64)word) /\
    (read:(armstate,(64)word)component->armstate->(64)word)
    (X6:(armstate,(64)word)component)
    (s:armstate) =
    (htbl_p:(64)word) /\
    (read:(armstate,(64)word)component->armstate->(64)word)
    (X3:(armstate,(64)word)component)
    (s:armstate) =
    (xi_p:(64)word) /\
    (read:(armstate,(64)word)component->armstate->(64)word)
    (X1:(armstate,(64)word)component)
    (s:armstate) =
    (word:num->(64)word) (128 * (nblk:num)) /\
    (read:(armstate,(64)word)component->armstate->(64)word)
    (SP:(armstate,(64)word)component)
    (s:armstate) =
    (stackpointer:(64)word) /\
    (read:(armstate,(64)word)component->armstate->(64)word)
    (X9:(armstate,(64)word)component)
    (s:armstate) =
    (word:num->(64)word) (16 * (nblk:num)) /\
    (read:(armstate,(64)word)component->armstate->(64)word)
    (X11:(armstate,(64)word)component)
    (s:armstate) =
    (key_p:(64)word) /\
    (read:(armstate,(64)word)component->armstate->(64)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes64:(64)word->((64)word->(8)word,(64)word)component)
     ((word_add:(64)word->(64)word->(64)word) (stackpointer:(64)word)
     ((word:num->(64)word) 72)))
    (s:armstate) =
    (word:num->(64)word) 0 /\
    (read:(armstate,(64)word)component->armstate->(64)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes64:(64)word->((64)word->(8)word,(64)word)component)
     ((word_add:(64)word->(64)word->(64)word) (stackpointer:(64)word)
     ((word:num->(64)word) 64)))
    (s:armstate) =
    (word:num->(64)word) 13979173243358019584 /\
    (read:(armstate,(64)word)component->armstate->(64)word)
    (X5:(armstate,(64)word)component)
    (s:armstate) =
    (word_add:(64)word->(64)word->(64)word)
    ((word:num->(64)word) (128 * ((nblk:num) - 1) DIV 8))
    (in_p:(64)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q9:(armstate,(128)word)component)
    (s:armstate) =
    (bytes_to_int128:((8)word)list->(128)word)
    ((SUB_LIST:num#num->((8)word)list->((8)word)list) (16,16)
    (ibytes:((8)word)list)) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q8:(armstate,(128)word)component)
    (s:armstate) =
    (bytes_to_int128:((8)word)list->(128)word)
    ((SUB_LIST:num#num->((8)word)list->((8)word)list) (0,16)
    (ibytes:((8)word)list)) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q13:(armstate,(128)word)component)
    (s:armstate) =
    (bytes_to_int128:((8)word)list->(128)word)
    ((SUB_LIST:num#num->((8)word)list->((8)word)list) (80,16)
    (ibytes:((8)word)list)) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q12:(armstate,(128)word)component)
    (s:armstate) =
    (bytes_to_int128:((8)word)list->(128)word)
    ((SUB_LIST:num#num->((8)word)list->((8)word)list) (64,16)
    (ibytes:((8)word)list)) /\
    ((read:(armstate,bool)component->armstate->bool)
     (CF:(armstate,bool)component)
     (s:armstate) <=>
     (val:(64)word->num)
     ((word_add:(64)word->(64)word->(64)word)
      ((word:num->(64)word) (128 * ((nblk:num) - 1) DIV 8))
     (in_p:(64)word)) <=
     (val:(64)word->num)
     ((word_add:(64)word->(64)word->(64)word) (in_p:(64)word)
     ((word:num->(64)word) 128))) /\
    ((read:(armstate,bool)component->armstate->bool)
     (ZF:(armstate,bool)component)
     (s:armstate) <=>
     (val:(64)word->num)
     ((word_sub:(64)word->(64)word->(64)word)
      ((word_add:(64)word->(64)word->(64)word) (in_p:(64)word)
      ((word:num->(64)word) 128))
     ((word_add:(64)word->(64)word->(64)word)
      ((word:num->(64)word) (128 * ((nblk:num) - 1) DIV 8))
     (in_p:(64)word))) =
     0) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q0:(armstate,(128)word)component)
    (s:armstate) =
    (word_join:(64)word->(64)word->(128)word)
    ((word_join:(32)word->(32)word->(64)word)
     ((word_join:(16)word->(16)word->(32)word)
      ((word_join:(8)word->(8)word->(16)word)
       ((word_subword:(32)word->num#num->(8)word)
        ((word_add:(32)word->(32)word->(32)word)
         ((word_join:(16)word->(16)word->(32)word)
          ((word_join:(8)word->(8)word->(16)word)
           ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word)
           (96,8))
          ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word)
          (104,8)))
         ((word_join:(8)word->(8)word->(16)word)
          ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word)
          (112,8))
         ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word)
         (120,8))))
        ((word:num->(32)word) 8))
       (0,8))
      ((word_subword:(32)word->num#num->(8)word)
       ((word_add:(32)word->(32)word->(32)word)
        ((word_join:(16)word->(16)word->(32)word)
         ((word_join:(8)word->(8)word->(16)word)
          ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word)
          (96,8))
         ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word)
         (104,8)))
        ((word_join:(8)word->(8)word->(16)word)
         ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word)
         (112,8))
        ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (120,8))))
       ((word:num->(32)word) 8))
      (8,8)))
     ((word_join:(8)word->(8)word->(16)word)
      ((word_subword:(32)word->num#num->(8)word)
       ((word_add:(32)word->(32)word->(32)word)
        ((word_join:(16)word->(16)word->(32)word)
         ((word_join:(8)word->(8)word->(16)word)
          ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word)
          (96,8))
         ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word)
         (104,8)))
        ((word_join:(8)word->(8)word->(16)word)
         ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word)
         (112,8))
        ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (120,8))))
       ((word:num->(32)word) 8))
      (16,8))
     ((word_subword:(32)word->num#num->(8)word)
      ((word_add:(32)word->(32)word->(32)word)
       ((word_join:(16)word->(16)word->(32)word)
        ((word_join:(8)word->(8)word->(16)word)
         ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (96,8))
        ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (104,8)))
       ((word_join:(8)word->(8)word->(16)word)
        ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (112,8))
       ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (120,8))))
      ((word:num->(32)word) 8))
     (24,8))))
    ((word_join:(16)word->(16)word->(32)word)
     ((word_join:(8)word->(8)word->(16)word)
      ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (88,8))
     ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (80,8)))
    ((word_join:(8)word->(8)word->(16)word)
     ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (72,8))
    ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (64,8)))))
    ((word_join:(32)word->(32)word->(64)word)
     ((word_join:(16)word->(16)word->(32)word)
      ((word_join:(8)word->(8)word->(16)word)
       ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (56,8))
      ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (48,8)))
     ((word_join:(8)word->(8)word->(16)word)
      ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (40,8))
     ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (32,8))))
    ((word_join:(16)word->(16)word->(32)word)
     ((word_join:(8)word->(8)word->(16)word)
      ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (24,8))
     ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (16,8)))
    ((word_join:(8)word->(8)word->(16)word)
     ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (8,8))
    ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (0,8))))) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (out_p:(64)word)
     ((word:num->(64)word) 48)))
    (s:armstate) =
    (word_xor:(128)word->(128)word->(128)word)
    ((word_xor:(128)word->(128)word->(128)word)
     ((bytes_to_int128:((8)word)list->(128)word)
     ((SUB_LIST:num#num->((8)word)list->((8)word)list) (48,16)
     (ibytes:((8)word)list)))
    ((aes13:(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word)
     ((gcm_ctr_inc:(128)word->(128)word)
     ((gcm_ctr_inc:(128)word->(128)word)
     ((gcm_ctr_inc:(128)word->(128)word) (ctr0:(128)word))))
     (k0:(128)word)
     (k1:(128)word)
     (k2:(128)word)
     (k3:(128)word)
     (k4:(128)word)
     (k5:(128)word)
     (k6:(128)word)
     (k7:(128)word)
     (k8:(128)word)
     (k9:(128)word)
     (k10:(128)word)
     (k11:(128)word)
     (k12:(128)word)
    (k13:(128)word)))
    (k14:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (out_p:(64)word)
     ((word:num->(64)word) 32)))
    (s:armstate) =
    (word_xor:(128)word->(128)word->(128)word)
    ((word_xor:(128)word->(128)word->(128)word)
     ((bytes_to_int128:((8)word)list->(128)word)
     ((SUB_LIST:num#num->((8)word)list->((8)word)list) (32,16)
     (ibytes:((8)word)list)))
    ((aes13:(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word)
     ((gcm_ctr_inc:(128)word->(128)word)
     ((gcm_ctr_inc:(128)word->(128)word) (ctr0:(128)word)))
     (k0:(128)word)
     (k1:(128)word)
     (k2:(128)word)
     (k3:(128)word)
     (k4:(128)word)
     (k5:(128)word)
     (k6:(128)word)
     (k7:(128)word)
     (k8:(128)word)
     (k9:(128)word)
     (k10:(128)word)
     (k11:(128)word)
     (k12:(128)word)
    (k13:(128)word)))
    (k14:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q3:(armstate,(128)word)component)
    (s:armstate) =
    (word_join:(64)word->(64)word->(128)word)
    ((word_join:(32)word->(32)word->(64)word)
     ((word_join:(16)word->(16)word->(32)word)
      ((word_join:(8)word->(8)word->(16)word)
       ((word_subword:(32)word->num#num->(8)word)
        ((word_add:(32)word->(32)word->(32)word)
         ((word_join:(16)word->(16)word->(32)word)
          ((word_join:(8)word->(8)word->(16)word)
           ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word)
           (96,8))
          ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word)
          (104,8)))
         ((word_join:(8)word->(8)word->(16)word)
          ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word)
          (112,8))
         ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word)
         (120,8))))
        ((word:num->(32)word) 11))
       (0,8))
      ((word_subword:(32)word->num#num->(8)word)
       ((word_add:(32)word->(32)word->(32)word)
        ((word_join:(16)word->(16)word->(32)word)
         ((word_join:(8)word->(8)word->(16)word)
          ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word)
          (96,8))
         ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word)
         (104,8)))
        ((word_join:(8)word->(8)word->(16)word)
         ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word)
         (112,8))
        ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (120,8))))
       ((word:num->(32)word) 11))
      (8,8)))
     ((word_join:(8)word->(8)word->(16)word)
      ((word_subword:(32)word->num#num->(8)word)
       ((word_add:(32)word->(32)word->(32)word)
        ((word_join:(16)word->(16)word->(32)word)
         ((word_join:(8)word->(8)word->(16)word)
          ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word)
          (96,8))
         ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word)
         (104,8)))
        ((word_join:(8)word->(8)word->(16)word)
         ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word)
         (112,8))
        ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (120,8))))
       ((word:num->(32)word) 11))
      (16,8))
     ((word_subword:(32)word->num#num->(8)word)
      ((word_add:(32)word->(32)word->(32)word)
       ((word_join:(16)word->(16)word->(32)word)
        ((word_join:(8)word->(8)word->(16)word)
         ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (96,8))
        ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (104,8)))
       ((word_join:(8)word->(8)word->(16)word)
        ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (112,8))
       ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (120,8))))
      ((word:num->(32)word) 11))
     (24,8))))
    ((word_join:(16)word->(16)word->(32)word)
     ((word_join:(8)word->(8)word->(16)word)
      ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (88,8))
     ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (80,8)))
    ((word_join:(8)word->(8)word->(16)word)
     ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (72,8))
    ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (64,8)))))
    ((word_join:(32)word->(32)word->(64)word)
     ((word_join:(16)word->(16)word->(32)word)
      ((word_join:(8)word->(8)word->(16)word)
       ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (56,8))
      ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (48,8)))
     ((word_join:(8)word->(8)word->(16)word)
      ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (40,8))
     ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (32,8))))
    ((word_join:(16)word->(16)word->(32)word)
     ((word_join:(8)word->(8)word->(16)word)
      ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (24,8))
     ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (16,8)))
    ((word_join:(8)word->(8)word->(16)word)
     ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (8,8))
    ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (0,8))))) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (out_p:(64)word)
     ((word:num->(64)word) 80)))
    (s:armstate) =
    (word_xor:(128)word->(128)word->(128)word)
    ((word_xor:(128)word->(128)word->(128)word)
     ((bytes_to_int128:((8)word)list->(128)word)
     ((SUB_LIST:num#num->((8)word)list->((8)word)list) (80,16)
     (ibytes:((8)word)list)))
    ((aes13:(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word)
     ((gcm_ctr_inc:(128)word->(128)word)
     ((gcm_ctr_inc:(128)word->(128)word)
     ((gcm_ctr_inc:(128)word->(128)word)
     ((gcm_ctr_inc:(128)word->(128)word)
     ((gcm_ctr_inc:(128)word->(128)word) (ctr0:(128)word))))))
     (k0:(128)word)
     (k1:(128)word)
     (k2:(128)word)
     (k3:(128)word)
     (k4:(128)word)
     (k5:(128)word)
     (k6:(128)word)
     (k7:(128)word)
     (k8:(128)word)
     (k9:(128)word)
     (k10:(128)word)
     (k11:(128)word)
     (k12:(128)word)
    (k13:(128)word)))
    (k14:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (out_p:(64)word)
     ((word:num->(64)word) 64)))
    (s:armstate) =
    (word_xor:(128)word->(128)word->(128)word)
    ((word_xor:(128)word->(128)word->(128)word)
     ((bytes_to_int128:((8)word)list->(128)word)
     ((SUB_LIST:num#num->((8)word)list->((8)word)list) (64,16)
     (ibytes:((8)word)list)))
    ((aes13:(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word)
     ((gcm_ctr_inc:(128)word->(128)word)
     ((gcm_ctr_inc:(128)word->(128)word)
     ((gcm_ctr_inc:(128)word->(128)word)
     ((gcm_ctr_inc:(128)word->(128)word) (ctr0:(128)word)))))
     (k0:(128)word)
     (k1:(128)word)
     (k2:(128)word)
     (k3:(128)word)
     (k4:(128)word)
     (k5:(128)word)
     (k6:(128)word)
     (k7:(128)word)
     (k8:(128)word)
     (k9:(128)word)
     (k10:(128)word)
     (k11:(128)word)
     (k12:(128)word)
    (k13:(128)word)))
    (k14:(128)word) /\
    (read:(armstate,(64)word)component->armstate->(64)word)
    (X2:(armstate,(64)word)component)
    (s:armstate) =
    (word_add:(64)word->(64)word->(64)word) (out_p:(64)word)
    ((word:num->(64)word) 128) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (out_p:(64)word)
     ((word:num->(64)word) 112)))
    (s:armstate) =
    (word_xor:(128)word->(128)word->(128)word)
    ((word_xor:(128)word->(128)word->(128)word)
     ((bytes_to_int128:((8)word)list->(128)word)
     ((SUB_LIST:num#num->((8)word)list->((8)word)list) (112,16)
     (ibytes:((8)word)list)))
    ((aes13:(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word)
     ((gcm_ctr_inc:(128)word->(128)word)
     ((gcm_ctr_inc:(128)word->(128)word)
     ((gcm_ctr_inc:(128)word->(128)word)
     ((gcm_ctr_inc:(128)word->(128)word)
     ((gcm_ctr_inc:(128)word->(128)word)
     ((gcm_ctr_inc:(128)word->(128)word)
     ((gcm_ctr_inc:(128)word->(128)word) (ctr0:(128)word))))))))
     (k0:(128)word)
     (k1:(128)word)
     (k2:(128)word)
     (k3:(128)word)
     (k4:(128)word)
     (k5:(128)word)
     (k6:(128)word)
     (k7:(128)word)
     (k8:(128)word)
     (k9:(128)word)
     (k10:(128)word)
     (k11:(128)word)
     (k12:(128)word)
    (k13:(128)word)))
    (k14:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (out_p:(64)word)
     ((word:num->(64)word) 96)))
    (s:armstate) =
    (word_xor:(128)word->(128)word->(128)word)
    ((word_xor:(128)word->(128)word->(128)word)
     ((bytes_to_int128:((8)word)list->(128)word)
     ((SUB_LIST:num#num->((8)word)list->((8)word)list) (96,16)
     (ibytes:((8)word)list)))
    ((aes13:(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word)
     ((gcm_ctr_inc:(128)word->(128)word)
     ((gcm_ctr_inc:(128)word->(128)word)
     ((gcm_ctr_inc:(128)word->(128)word)
     ((gcm_ctr_inc:(128)word->(128)word)
     ((gcm_ctr_inc:(128)word->(128)word)
     ((gcm_ctr_inc:(128)word->(128)word) (ctr0:(128)word)))))))
     (k0:(128)word)
     (k1:(128)word)
     (k2:(128)word)
     (k3:(128)word)
     (k4:(128)word)
     (k5:(128)word)
     (k6:(128)word)
     (k7:(128)word)
     (k8:(128)word)
     (k9:(128)word)
     (k10:(128)word)
     (k11:(128)word)
     (k12:(128)word)
    (k13:(128)word)))
    (k14:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q30:(armstate,(128)word)component)
    (s:armstate) =
    (word_join:(64)word->(64)word->(128)word)
    ((word_join:(32)word->(32)word->(64)word)
     ((word_add:(32)word->(32)word->(32)word)
      ((word_add:(32)word->(32)word->(32)word)
       ((word_join:(16)word->(16)word->(32)word)
        ((word_join:(8)word->(8)word->(16)word)
         ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (96,8))
        ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (104,8)))
       ((word_join:(8)word->(8)word->(16)word)
        ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (112,8))
       ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (120,8))))
      ((word:num->(32)word) 12))
     ((word:num->(32)word) 1))
    ((word_add:(32)word->(32)word->(32)word)
     ((word_join:(16)word->(16)word->(32)word)
      ((word_join:(8)word->(8)word->(16)word)
       ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (64,8))
      ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (72,8)))
     ((word_join:(8)word->(8)word->(16)word)
      ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (80,8))
     ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (88,8))))
    ((word:num->(32)word) 0)))
    ((word_join:(32)word->(32)word->(64)word)
     ((word_add:(32)word->(32)word->(32)word)
      ((word_join:(16)word->(16)word->(32)word)
       ((word_join:(8)word->(8)word->(16)word)
        ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (32,8))
       ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (40,8)))
      ((word_join:(8)word->(8)word->(16)word)
       ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (48,8))
      ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (56,8))))
     ((word:num->(32)word) 0))
    ((word_add:(32)word->(32)word->(32)word)
     ((word_join:(16)word->(16)word->(32)word)
      ((word_join:(8)word->(8)word->(16)word)
       ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (0,8))
      ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (8,8)))
     ((word_join:(8)word->(8)word->(16)word)
      ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (16,8))
     ((word_subword:(128)word->num#num->(8)word) (ctr0:(128)word) (24,8))))
    ((word:num->(32)word) 0)))|};;

(* WBN_FRONT_BUF: the FRONT-N theorem.  Its postcond = the i=0 loop invariant
   (two-stream pipelined form): q8..q15 = RAW ct blocks 0..7 pending fold,
   Q19 = word_bytereverse xi (GHASH acc over blocks 0..-1 = tag only), stores
   done for blocks 0..7, counters at 8..12, X0=in_p+128, X2=out_p+128.
   no longer runs the 287-step front sim -- reuses the shared
   WBN_FRONT_PREFIX (0x20->0x4b8) via ENSURES_TRANS_SIMPLE, then step 296
   (0x4bc b.ge FALLS THROUGH for 17<=nblk, via WBN_RESOLVE_49C_TAC) lands at
   the loop head 0x4c0 (fall-through target).
   FUSED SPLICE (STEP 4): prefix now ends at s295 (was s293); the 0x4bc b.ge is
   step 296 (was 0x4b4 step 294); the 2 .balign nops are GONE (guard absorbed
   them) so the loop head is reached with NO extra steps.  Loop head PC 0x4c0 =
   pc+1216 is UNCHANGED (balign-absorbed), so wbn_front_postcond_i0 is untouched.
   Close = the old WBN_FRONT_BUF final-state close (ASM_REWRITE + WORD_ADD_0). *)
let WBN_FRONT_BUF = prove(mk_wbn_front_goal wbn_front_postcond_i0,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC ENSURES_TRANS_SIMPLE THEN
  EXISTS_TAC wbn_front_prefix_postcond THEN
  CONJ_TAC THENL
   [REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN MAYCHANGE_IDEMPOT_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC WBN_FRONT_PREFIX THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ENSURES_INIT_TAC "s295" THEN
    RULE_ASSUM_TAC(REWRITE_RULE[WB_MC_LEN]) THEN
    WBN_RESOLVE_49C_TAC THEN
    ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (296--296) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[WORD_ADD_0] THEN
    REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    REPEAT CONJ_TAC THEN MONOTONE_MAYCHANGE_TAC]);;
(* --- mid-load heap compaction: bound GC cost across this large single-file *)
(*     load (after a front-BUF sim); mirrors the needs-boundary/ckpt Gc.compact). --- *)
Gc.compact();;

(* ------------------------------------------------------------------------- *)
(* 4. Phase 2: the TWO-STREAM ENSURES_WHILE loop invariant (FROZEN).          *)
(*                                                                            *)
(* Derived by generalizing WBN_FRONT_BUF's harvested s288                     *)
(* postcond to symbolic block index i.  The i=0 instance was VALIDATED to     *)
(* follow from WBN_FRONT_BUF: 44 of 47 conjuncts (all registers, counters,    *)
(* keystreams, GHASH acc, stores, pointers) close by                          *)
(*   CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN                                  *)
(*   RULE_ASSUM_TAC(REWRITE_RULE[GSYM GCM_CTR_ADD_LANES]) THEN                *)
(*   REWRITE_TAC[GCM_CTR_INC_ITER_ADD; GCM_CTR_ADD_1; GSYM GCM_CTR_ADD_LANES] *)
(*     THEN REWRITE_TAC[list_of_seq; MAP; ghash_polyval_acc] THEN             *)
(*   RULE_ASSUM_TAC(REWRITE_RULE[GCM_CTR_INC_LANES;..;GCM_CTR_INC7_LANES])    *)
(*     THEN RULE_ASSUM_TAC(REWRITE_RULE[GSYM GCM_CTR_ADD_LANES]) THEN         *)
(*   REWRITE_TAC[GCM_CTR_ADD_0] THEN CONV_TAC(ONCE_DEPTH_CONV EXPAND_CASES_   *)
(*     CONV) THEN CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN                     *)
(*   REWRITE_TAC[WORD_ADD_0] THEN ASM_REWRITE_TAC[].                          *)
(*                                                                            *)
(* GAP (documented, sound): the remaining 3 conjuncts                         *)
(*   read (memory :> bytes (in_p,16 * nblk)) s = num_of_bytelist ibytes       *)
(*   read (memory :> bytes128 key_p) s = k0                                   *)
(*   htable_mem_dec h htbl_p s                                                *)
(* are loop-CONSTANTS that hold at the loop head (they are in wb_front_pre_tm *)
(* and NOT in the front MAYCHANGE frame -> preserved) but are NOT in          *)
(* WBN_FRONT_BUF's harvested postcond (build_state_postcond_tms2 keeps only   *)
(* `read _ s = _` + aligned_bytes_loaded, so htable_mem_dec is dropped, and   *)
(* the in_p/key_p reads were s0 facts not re-stated at s288).  FIX: extend    *)
(* the front postcond to re-assert these 3, either in the harvest keep-filter *)
(* or by a strengthening step; WBN_FRONT_BUF then closes them from the        *)
(* precond (they are in the MAYCHANGE-preserved set).  With that the          *)
(* ENSURES_WHILE_UP_TAC entry subgoal (i=0) closes by MATCH_MP_TAC            *)
(* WBN_FRONT_BUF + the tactic above.  Done in Sec 7 as WBN_FRONT_BUF_EXT.     *)
(*                                                                            *)
(* Two-stream reading of the invariant (VERIFIED off the i=0 goal):           *)
(*  - store/counter stream AHEAD at 8(i+1): X0=in_p+128(i+1), X2=out_p+128(i+1)*)
(*    Q0..Q4 = gcm_ctr_add (word (8i+8..12)) ctr0 (next group's counters),    *)
(*    Q5..Q7 = plaintext blocks at 8i+5..7 (in-flight keystream XOR),         *)
(*    stores done for all j < 8(i+1).                                         *)
(*  - GHASH stream LAGS at 8i: Q19 = ghash_polyval_acc (byteswap128 h)        *)
(*    (word_bytereverse xi) over reversed raw ct blocks 0..8i-1;              *)
(*    q8..q15 = RAW ct blocks 8i..8i+7 pending fold (the bridge).             *)
(*                                                                            *)
(* STEP-CASE TODO (Phase 4, plan-rationale risk #2): the +8*i offset on the   *)
(* Q5..Q7 keystream indices (5,6,7 at i=0, all < 8) must be READ OFF the      *)
(* loop-body sim goal, not trusted from this generalization.                  *)
(* loop control flow (objdump): head pc1=pc+0x4a0; back-edge cmp x0,x5 @0x9e4 *)
(* + b.lt 0x4a0 @0x9ec (SIGNED, so a P-variant / WB_PTRCMP_FLAGS handles it); *)
(* exit fall-through @0x9f0.  count q = (nblk-9) DIV 8.                        *)
(*                                                                            *)
(* Q26/Q27/Q28 (=k12/k13/k14) DROPPED from the invariant below                *)
(* — objdump-verified dead live-ins (loop head 0x4a4 ldp q26,q27,[x11] +      *)
(* 0x518 ldp q28,q26,[x11,#32]; prepretail seam 0x9f0 ldp q26,q27,[x11] — all *)
(* reload before first aese v_,v26/28 uses at 0x4d8/0x570).  Removal gated by *)
(* the alpha-shadow wbn_loop_invariant_v2 (ENTRY_V2 re-proved to hyps=0).      *)
(* CAUTION: do NOT put (* *) comments or backticks INSIDE the term backquote   *)
(* below — HOL's in-term comment token is //, and (* *) / ` break the parse   *)
(* (fix: the in-term note broke the cold-load).                               *)
(* ------------------------------------------------------------------------- *)

let wbn_loop_invariant_raw = new_definition
 `wbn_loop_invariant_raw (pc:num) (ctr0:int128) (in_p:int64) (out_p:int64)
    (xi_p:int64) (ivec_p:int64) (key_p:int64) (htbl_p:int64) (stackpointer:int64)
    (nblk:num) (ibytes:byte list) (xi:int128) (h:int128)
    (k0:int128) k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 k11 k12 k13 (k14:int128) =
  \(i:num) (s:armstate).
    aligned_bytes_loaded s (word pc) aesv8_gcm_8x_dec_256_wb_mc /\
    read PC s = word (pc + 1216) /\
    read Q0 s = gcm_ctr_add (word (8 * i + 8)) ctr0 /\
    read Q1 s = gcm_ctr_add (word (8 * i + 9)) ctr0 /\
    read Q2 s = gcm_ctr_add (word (8 * i + 10)) ctr0 /\
    read Q3 s = gcm_ctr_add (word (8 * i + 11)) ctr0 /\
    read Q4 s = gcm_ctr_add (word (8 * i + 12)) ctr0 /\
    read Q5 s =
    word_xor
    (word_xor (bytes_to_int128 (SUB_LIST (16 * (8 * i + 5),16) ibytes))
    (aes13 (gcm_ctr_inc_iter (8 * i + 5) ctr0) k0 k1 k2 k3 k4 k5 k6 k7 k8 k9
     k10 k11 k12 k13)) k14 /\
    read Q6 s =
    word_xor
    (word_xor (bytes_to_int128 (SUB_LIST (16 * (8 * i + 6),16) ibytes))
    (aes13 (gcm_ctr_inc_iter (8 * i + 6) ctr0) k0 k1 k2 k3 k4 k5 k6 k7 k8 k9
     k10 k11 k12 k13)) k14 /\
    read Q7 s =
    word_xor
    (word_xor (bytes_to_int128 (SUB_LIST (16 * (8 * i + 7),16) ibytes))
    (aes13 (gcm_ctr_inc_iter (8 * i + 7) ctr0) k0 k1 k2 k3 k4 k5 k6 k7 k8 k9
     k10 k11 k12 k13)) k14 /\
    read Q8 s = bytes_to_int128 (SUB_LIST (16 * (8 * i + 0),16) ibytes) /\
    read Q9 s = bytes_to_int128 (SUB_LIST (16 * (8 * i + 1),16) ibytes) /\
    read Q10 s = bytes_to_int128 (SUB_LIST (16 * (8 * i + 2),16) ibytes) /\
    read Q11 s = bytes_to_int128 (SUB_LIST (16 * (8 * i + 3),16) ibytes) /\
    read Q12 s = bytes_to_int128 (SUB_LIST (16 * (8 * i + 4),16) ibytes) /\
    read Q13 s = bytes_to_int128 (SUB_LIST (16 * (8 * i + 5),16) ibytes) /\
    read Q14 s = bytes_to_int128 (SUB_LIST (16 * (8 * i + 6),16) ibytes) /\
    read Q15 s = bytes_to_int128 (SUB_LIST (16 * (8 * i + 7),16) ibytes) /\
    read Q19 s =
    ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
    (MAP word_bytereverse
    (list_of_seq (\k. bytes_to_int128 (SUB_LIST (16 * k,16) ibytes)) (8 * i))) /\
    read X0 s = word_add in_p (word (128 * (i + 1))) /\
    read X2 s = word_add out_p (word (128 * (i + 1))) /\
    read X4 s = word_add in_p (word (16 * nblk)) /\
    read X5 s = word_add (word (128 * (nblk - 1) DIV 8)) in_p /\
    read X9 s = word (16 * nblk) /\
    read X10 s = word_add stackpointer (word 64) /\
    read X1 s = word (128 * nblk) /\
    read X15 s = word 4294967296 /\
    read Q31 s = word 79228162514264337593543950336 /\
    read Q30 s = gcm_ctr_raw (word (8 * i + 13)) ctr0 /\
    read X16 s = ivec_p /\
    read X6 s = htbl_p /\
    read X3 s = xi_p /\
    read X11 s = key_p /\
    read SP s = stackpointer /\
    read (memory :> bytes64 (word_add stackpointer (word 64))) s =
    word 13979173243358019584 /\
    (!j. j < 8 * (i + 1)
         ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
             word_xor
             (word_xor (bytes_to_int128 (SUB_LIST (16 * j,16) ibytes))
             (aes13 (gcm_ctr_inc_iter j ctr0) k0 k1 k2 k3 k4 k5 k6 k7 k8 k9
              k10 k11 k12 k13)) k14) /\
    read (memory :> bytes (in_p,16 * nblk)) s = num_of_bytelist ibytes /\
    read (memory :> bytes128 key_p) s = k0 /\
    read (memory :> bytes128 (word_add key_p (word 16))) s = k1 /\
    read (memory :> bytes128 (word_add key_p (word 32))) s = k2 /\
    read (memory :> bytes128 (word_add key_p (word 48))) s = k3 /\
    read (memory :> bytes128 (word_add key_p (word 64))) s = k4 /\
    read (memory :> bytes128 (word_add key_p (word 80))) s = k5 /\
    read (memory :> bytes128 (word_add key_p (word 96))) s = k6 /\
    read (memory :> bytes128 (word_add key_p (word 112))) s = k7 /\
    read (memory :> bytes128 (word_add key_p (word 128))) s = k8 /\
    read (memory :> bytes128 (word_add key_p (word 144))) s = k9 /\
    read (memory :> bytes128 (word_add key_p (word 160))) s = k10 /\
    read (memory :> bytes128 (word_add key_p (word 176))) s = k11 /\
    read (memory :> bytes128 (word_add key_p (word 192))) s = k12 /\
    read (memory :> bytes128 (word_add key_p (word 208))) s = k13 /\
    read (memory :> bytes128 (word_add key_p (word 224))) s = k14 /\
    htable_mem_dec h htbl_p s`;;

(* ---- Entry-subgoal recipe (validated interactively, ) ----------
   The ENSURES_WHILE_UP_TAC entry subgoal is  pre ==> (PC=pc1 /\ inv 0 s).
   Given WBN_FRONT_BUF establishes pre ==> (PC=pc+0x4b8 /\ <postcond s>), the
   i=0 invariant  (wbn_loop_invariant_raw ... 0 s)  follows from <postcond s> PLUS
   the 3 loop-constants (in_p read-only, key_p=k0, htable_mem_dec) once those
   are added to WBN_FRONT_BUF's harvest.  The closing tactic (proves 44/47
   directly from the postcond hyps; the 3 come from the extended front):

     GEN_TAC THEN REWRITE_TAC[wbn_loop_invariant_raw] THEN
     CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN STRIP_TAC THEN
     CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN
     RULE_ASSUM_TAC(REWRITE_RULE[GSYM GCM_CTR_ADD_LANES]) THEN
     REWRITE_TAC[GCM_CTR_INC_ITER_ADD; GCM_CTR_ADD_1; GSYM GCM_CTR_ADD_LANES] THEN
     REWRITE_TAC[list_of_seq; MAP; ghash_polyval_acc] THEN
     RULE_ASSUM_TAC(REWRITE_RULE[GCM_CTR_INC_LANES; GCM_CTR_INC2_LANES;
        GCM_CTR_INC3_LANES; GCM_CTR_INC4_LANES; GCM_CTR_INC5_LANES;
        GCM_CTR_INC6_LANES; GCM_CTR_INC7_LANES]) THEN
     RULE_ASSUM_TAC(REWRITE_RULE[GSYM GCM_CTR_ADD_LANES]) THEN
     REWRITE_TAC[GCM_CTR_ADD_0] THEN
     CONV_TAC(ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN
     CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN
     REWRITE_TAC[WORD_ADD_0] THEN ASM_REWRITE_TAC[]

   With the RAW WBN_FRONT_BUF postcond as the assumption set this reduces the
   goal to EXACTLY the 3 loop-constant conjuncts.  When
   packaging as a standalone lemma with the postcond as a `\s.`-abstraction
   antecedent, watch the beta step: STRIP_TAC must see the antecedent already
   beta-reduced (do CONV_TAC(TOP_DEPTH_CONV BETA_CONV) on the WHOLE goal, incl.
   the antecedent, before STRIP_TAC) — a naive `(\s.P) s /\ (\s.Q) s ==> ...`
   left unreduced makes STRIP_TAC give conjunct hyps still wrapped.

   FIX for a clean entry (no extra hyps):
   extend WBN_FRONT_BUF so its postcond re-asserts the 3 loop-constants.  Either
   (a) widen build_state_postcond_tms2's keep-filter to also retain
       `htable_mem_dec _ _ s` and the input/key `read _ s = _` facts (they are
       preserved: NOT in wb_front_frame_tm's MAYCHANGE), re-run the front sim,
       or (b) prove WBN_FRONT_BUF_EXT = WBN_FRONT_BUF strengthened with the 3
       (they hold in wb_front_pre_tm and survive the frame), via a framing/
       ENSURES_TRANS wrapper avoiding a full re-sim.  Then the entry subgoal of
       ENSURES_WHILE_UP_TAC closes by MATCH_MP_TAC WBN_FRONT_BUF_EXT + the tactic
       above (no leftover conjuncts).
   Route (b) is the one taken; see Sec 7. *)

(* ------------------------------------------------------------------------- *)
(* 5. Phase 3: GHASH 8-block extension algebra (pure list/field, no sim).     *)
(*                                                                            *)
(* The invariant's Q19 GHASH accumulator is                                   *)
(*   ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)                  *)
(*     (MAP word_bytereverse (list_of_seq blk (8 * i)))                       *)
(* where blk k = bytes_to_int128 (SUB_LIST (16*k,16) ibytes) is the raw ct    *)
(* block k.  The step case (i -> i+1) must extend this fold from 8*i to       *)
(* 8*(i+1) blocks.  The loop body performs exactly 8 Horner steps (one        *)
(* polyval_dot per fresh ciphertext block, each byte-reversed then XORed into *)
(* the accumulator), so we need the fold over 8*(i+1) blocks to equal the     *)
(* fold over 8*i blocks continued by 8 explicit steps over blocks            *)
(* 8*i .. 8*i+7.  This is pure algebra over GHASH_ACC_APPEND                   *)
(* (common/polyval_ghash.ml:62) + list_of_seq, provable BEFORE any sim.       *)
(* ------------------------------------------------------------------------- *)

(* list_of_seq splits at any offset (APPEND-at-end recursion, induct on n) *)
let LIST_OF_SEQ_SPLIT = prove
 (`!(f:num->int128) m n. list_of_seq f (m + n) =
     APPEND (list_of_seq f m) (list_of_seq (\j. f (m + j)) n)`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[ADD_CLAUSES; list_of_seq; APPEND_NIL] THEN
  ASM_REWRITE_TAC[ADD_CLAUSES; list_of_seq; APPEND_ASSOC]);;

(* generic group-extension of the byte-reversed GHASH fold: split m+n *)
let GHASH_ACC_GROUP_EXTEND = prove
 (`!(g:num->int128) H acc m n.
    ghash_polyval_acc H acc (MAP word_bytereverse (list_of_seq g (m + n))) =
    ghash_polyval_acc H
      (ghash_polyval_acc H acc (MAP word_bytereverse (list_of_seq g m)))
      (MAP word_bytereverse (list_of_seq (\j. g (m + j)) n))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[LIST_OF_SEQ_SPLIT; MAP_APPEND; GHASH_ACC_APPEND]);;

(* clean 8-element unfold of list_of_seq (numerals, no SUC towers) *)
let LIST_OF_SEQ_8 = prove
 (`!f:num->int128. list_of_seq f 8 =
    [f 0; f 1; f 2; f 3; f 4; f 5; f 6; f 7]`,
  GEN_TAC THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[num_CONV `8`; num_CONV `7`; num_CONV `6`;
    num_CONV `5`; num_CONV `4`; num_CONV `3`; num_CONV `2`; num_CONV `1`;
    LIST_OF_SEQ])) THEN
  REWRITE_TAC[o_THM] THEN CONV_TAC(DEPTH_CONV NUM_SUC_CONV) THEN REWRITE_TAC[]);;

(* THE Phase-3 deliverable: extend the invariant's GHASH fold by one 8-block  *)
(* group.  RHS = the 8*i fold, continued by a fold over the 8 concrete new    *)
(* raw-ct blocks (8*i .. 8*i+7).  Instantiate blk := \k. bytes_to_int128      *)
(* (SUB_LIST (16*k,16) ibytes) in the body; REWRITE_TAC[MAP; ghash_polyval_acc]*)
(* then unfolds the RHS to the nested polyval_dot/word_xor Horner chain the    *)
(* 8 body GHASH instructions produce. *)
let GHASH_ACC_8BLOCK_EXTEND = prove
 (`!(blk:num->int128) H acc i.
    ghash_polyval_acc H acc
      (MAP word_bytereverse (list_of_seq blk (8 * (i + 1)))) =
    ghash_polyval_acc H
      (ghash_polyval_acc H acc (MAP word_bytereverse (list_of_seq blk (8 * i))))
      (MAP word_bytereverse
        [blk (8 * i); blk (8 * i + 1); blk (8 * i + 2); blk (8 * i + 3);
         blk (8 * i + 4); blk (8 * i + 5); blk (8 * i + 6); blk (8 * i + 7)])`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `8 * (i + 1) = 8 * i + 8` SUBST1_TAC THENL
   [ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GHASH_ACC_GROUP_EXTEND] THEN
  REWRITE_TAC[LIST_OF_SEQ_8] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[ADD_CLAUSES]);;

(* Body GHASH-close bridge: the generalization of the <=8-block chain's                       *)
(* spec_to_byteform_wb8 to an ARBITRARY incoming accumulator `acc` (the running *)
(* fold read Q19 at body entry) in place of the tail's hardwired                *)
(* `word_bytereverse xi`.  Same H-power hypotheses (supplied by the htable      *)
(* reduce steps during the sim), same machine byteform RHS.  Proof is verbatim  *)
(* the <=8-block chain's (STRIP; GHASH_POLYVAL_ACC_8; ASM_REWRITE; AP_TERM; WORD_RULE) —       *)
(* it never depended on the acc being xi.  Composes with GHASH_ACC_8BLOCK_EXTEND *)
(* (acc := the invariant's 8*i fold) to close the loop body's Q19.              *)
let SPEC_TO_BYTEFORM_WB8_ACC = prove
 (`byteswap128 h2 = polyval_dot (byteswap128 h) (byteswap128 h) /\
   byteswap128 h3 =
   polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h) /\
   byteswap128 h4 =
   polyval_dot
   (polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h))
   (byteswap128 h) /\
   byteswap128 h5 =
   polyval_dot
   (polyval_dot
    (polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h))
    (byteswap128 h))
   (byteswap128 h) /\
   byteswap128 h6 =
   polyval_dot
   (polyval_dot
    (polyval_dot
     (polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h))
     (byteswap128 h))
    (byteswap128 h))
   (byteswap128 h) /\
   byteswap128 h7 =
   polyval_dot
   (polyval_dot
    (polyval_dot
     (polyval_dot
      (polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h))
      (byteswap128 h))
     (byteswap128 h))
    (byteswap128 h))
   (byteswap128 h) /\
   byteswap128 h8 =
   polyval_dot
   (polyval_dot
    (polyval_dot
     (polyval_dot
      (polyval_dot
       (polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h))
       (byteswap128 h))
      (byteswap128 h))
     (byteswap128 h))
    (byteswap128 h))
   (byteswap128 h)
   ==> ghash_polyval_acc (byteswap128 h) (acc:int128)
       [word_bytereverse cph0; word_bytereverse cph1; word_bytereverse cph2;
        word_bytereverse cph3; word_bytereverse cph4; word_bytereverse cph5;
        word_bytereverse cph6; word_bytereverse cph7] =
       polyval_reduce_prop3
       (word_xor (word_xor (word_xor (word_xor (word_xor (word_xor (word_xor
        (word_pmul (word_xor acc (word_bytereverse cph0)) (byteswap128 h8))
        (word_pmul (word_bytereverse cph1) (byteswap128 h7)))
        (word_pmul (word_bytereverse cph2) (byteswap128 h6)))
        (word_pmul (word_bytereverse cph3) (byteswap128 h5)))
        (word_pmul (word_bytereverse cph4) (byteswap128 h4)))
        (word_pmul (word_bytereverse cph5) (byteswap128 h3)))
        (word_pmul (word_bytereverse cph6) (byteswap128 h2)))
       (word_pmul (word_bytereverse cph7) (byteswap128 h)))`,
  STRIP_TAC THEN REWRITE_TAC[GHASH_POLYVAL_ACC_8] THEN
  ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE);;

(* The COMPOSED body Q19-close: the invariant's Q19 conjunct at                  *)
(* i+1 equals the machine 8-block byteform, with the incoming accumulator being  *)
(* the invariant's OWN 8*i fold.  = GHASH_ACC_8BLOCK_EXTEND (split the 8*(i+1)   *)
(* fold into [8 fresh blocks] on the 8*i fold) then SPEC_TO_BYTEFORM_WB8_ACC     *)
(* (acc := that 8*i fold).  This is exactly what the loop body's Q19 SUBGOAL     *)
(* must match once the store/GHASH window is simulated with the raw reduce       *)
(* preserved (H-power hyps `byteswap128 h2..h8 = polyval_dot..` are produced by  *)
(* the htable reduce steps during the sim).  Proved to hyps=0: the whole GHASH   *)
(* algebra of the body close is settled here, sim-free.                          *)
let BODY_Q19_CLOSE_ALGEBRA = prove
 (`byteswap128 h2 = polyval_dot (byteswap128 h) (byteswap128 h) /\
   byteswap128 h3 =
   polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h) /\
   byteswap128 h4 =
   polyval_dot
   (polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h))
   (byteswap128 h) /\
   byteswap128 h5 =
   polyval_dot
   (polyval_dot
    (polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h))
    (byteswap128 h))
   (byteswap128 h) /\
   byteswap128 h6 =
   polyval_dot
   (polyval_dot
    (polyval_dot
     (polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h))
     (byteswap128 h))
    (byteswap128 h))
   (byteswap128 h) /\
   byteswap128 h7 =
   polyval_dot
   (polyval_dot
    (polyval_dot
     (polyval_dot
      (polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h))
      (byteswap128 h))
     (byteswap128 h))
    (byteswap128 h))
   (byteswap128 h) /\
   byteswap128 h8 =
   polyval_dot
   (polyval_dot
    (polyval_dot
     (polyval_dot
      (polyval_dot
       (polyval_dot (polyval_dot (byteswap128 h) (byteswap128 h)) (byteswap128 h))
       (byteswap128 h))
      (byteswap128 h))
     (byteswap128 h))
    (byteswap128 h))
   (byteswap128 h)
   ==> ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
        (MAP word_bytereverse
         (list_of_seq (\k. bytes_to_int128 (SUB_LIST (16 * k,16) ibytes))
          (8 * (i+1)))) =
        polyval_reduce_prop3
        (word_xor (word_xor (word_xor (word_xor (word_xor (word_xor (word_xor
         (word_pmul (word_xor (ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
           (MAP word_bytereverse
            (list_of_seq (\k. bytes_to_int128 (SUB_LIST (16 * k,16) ibytes)) (8 * i))))
           (word_bytereverse (bytes_to_int128 (SUB_LIST (16*(8*i+0),16) ibytes)))) (byteswap128 h8))
         (word_pmul (word_bytereverse (bytes_to_int128 (SUB_LIST (16*(8*i+1),16) ibytes))) (byteswap128 h7)))
         (word_pmul (word_bytereverse (bytes_to_int128 (SUB_LIST (16*(8*i+2),16) ibytes))) (byteswap128 h6)))
         (word_pmul (word_bytereverse (bytes_to_int128 (SUB_LIST (16*(8*i+3),16) ibytes))) (byteswap128 h5)))
         (word_pmul (word_bytereverse (bytes_to_int128 (SUB_LIST (16*(8*i+4),16) ibytes))) (byteswap128 h4)))
         (word_pmul (word_bytereverse (bytes_to_int128 (SUB_LIST (16*(8*i+5),16) ibytes))) (byteswap128 h3)))
         (word_pmul (word_bytereverse (bytes_to_int128 (SUB_LIST (16*(8*i+6),16) ibytes))) (byteswap128 h2)))
        (word_pmul (word_bytereverse (bytes_to_int128 (SUB_LIST (16*(8*i+7),16) ibytes))) (byteswap128 h)))`,
  STRIP_TAC THEN
  REWRITE_TAC[GHASH_ACC_8BLOCK_EXTEND; MAP] THEN
  REWRITE_TAC[ARITH_RULE `16 * 8 * i = 16 * (8*i+0)`] THEN
  MATCH_MP_TAC SPEC_TO_BYTEFORM_WB8_ACC THEN ASM_REWRITE_TAC[]);;

(* --------------------------------------------------------------------------- *)
(* THE REDUCE-DATAFLOW value-equality -- the algebraic core.  The body's GHASH  *)
(* reduce window (asm 0x924..0x9b4) reads three separable 128-bit accumulators  *)
(* at s289                                                                      *)
(*   PL = Q17 = Sum_k karatsuba_block_pl,  PH = Q19 = Sum_k karatsuba_block_ph,  *)
(*   PM = Q18 = Sum_k karatsuba_block_pm,  Barrett modulus raw in Q16,          *)
(* then runs the shared Barrett W-reduction, landing read Q19 s326 in EXACTLY   *)
(* the byteform LHS below (over OPAQUE PL/PH/PM — the sim keeps them abbreviated *)
(* so the reduce window stays small).  This lemma says that byteform is         *)
(* polyval_reduce_prop3 (pack_corrected PL PH PM) — the pre-byte-reversal prop3  *)
(* on the Karatsuba-corrected packed value.  It is the machine analogue of      *)
(* common/ghash_nblock_karatsuba.ml's KARATSUBA_REDUCE_AS_PROP3 (same reduce,    *)
(* proven the same way: KARATSUBA_LIMB_* to reduce the pack lanes, then two      *)
(* pmul abbreviations (wa/wv) so the residual is a pure opaque-atom bit identity *)
(* closed by WORD_BLAST).  Reconciles s056 (the s326 OUTPUT is byteform, NOT a   *)
(* karatsuba_reduce_shared instance) with R1' (the krs INPUT triple lives at     *)
(* s289): here the OUTPUT = prop3 ∘ pack_corrected of the INPUT triple, no outer *)
(* word_reversefields — exactly matching BODY_Q19_CLOSE_ALGEBRA's prop3 RHS.     *)
(* NOTE: the 4 KARATSUBA_LIMB_* must be listed individually — the bundled CONJ   *)
(* KARATSUBA_LIMBS does NOT rewrite via REWRITE_TAC (nested-CONJ matcher).       *)
let WBN_MACHINE_REDUCE_IS_PROP3_PACK = prove
 (`!PL PH PM:int128.
     word_xor
      (word_xor PH
       (word_subword
        (word_join
         (word_xor
          (word_xor (word_xor (word_xor PM PL) PH)
          (word_pmul (word_subword PL (0,64) :64 word) (word 13979173243358019584 :64 word)))
         (word_subword (word_join PL PL :256 word) (64,128)))
        (word_xor
         (word_xor (word_xor (word_xor PM PL) PH)
         (word_pmul (word_subword PL (0,64) :64 word) (word 13979173243358019584 :64 word)))
        (word_subword (word_join PL PL :256 word) (64,128))) :256 word)
       (64,128)))
      (word_pmul
       (word_subword
        (word_xor
         (word_xor (word_xor (word_xor PM PL) PH)
         (word_pmul (word_subword PL (0,64) :64 word) (word 13979173243358019584 :64 word)))
        (word_subword (word_join PL PL :256 word) (64,128)))
       (0,64) :64 word)
      (word 13979173243358019584 :64 word)) =
     polyval_reduce_prop3 (pack_corrected PL PH PM)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[pack_corrected; polyval_reduce_prop3; LET_DEF; LET_END_DEF] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  SUBGOAL_THEN
   `word_subword (word_join (PL:int128) (PL:int128) :256 word) (64,128) :128 word =
    word_join (word_subword PL (0,64):64 word) (word_subword PL (64,64):64 word)`
   SUBST1_TAC THENL [CONV_TAC WORD_BLAST; ALL_TAC] THEN
  REWRITE_TAC[KARATSUBA_LIMB_0_63; KARATSUBA_LIMB_64_127;
              KARATSUBA_LIMB_128_191; KARATSUBA_LIMB_192_255] THEN
  ABBREV_TAC `wa:int128 = word_pmul (word_subword (PL:int128) (0,64):64 word)
                                    (word 13979173243358019584:64 word)` THEN
  SUBGOAL_THEN
   `word_subword
      (word_xor (word_xor (word_xor (word_xor PM PL) PH) (wa:int128))
                (word_join (word_subword (PL:int128) (0,64):64 word)
                           (word_subword PL (64,64):64 word)))
      (0,64) :64 word =
    word_xor (word_xor (word_subword (PL:int128) (64,64):64 word)
                       (word_subword (word_xor (word_xor PL PH) PM) (0,64):64 word))
             (word_subword (wa:int128) (0,64):64 word)`
   SUBST1_TAC THENL [CONV_TAC WORD_BLAST; ALL_TAC] THEN
  ABBREV_TAC `wv:int128 = word_pmul
     (word_xor (word_xor (word_subword (PL:int128) (64,64):64 word)
                         (word_subword (word_xor (word_xor PL PH) PM) (0,64):64 word))
               (word_subword (wa:int128) (0,64):64 word))
     (word 13979173243358019584:64 word)` THEN
  (* SPEED: the old monolithic `CONV_TAC WORD_BLAST` here bit-blasted
     PL/PH/PM as full 128-bit free vars (~115s).  Instead reconstruct the LHS
     result as word_join of its two 64-bit lanes (QQ0SPLIT), split the resulting
     word_join=word_join with JOIN_EQ_SPLIT, and close each 64-bit lane with the
     proven WB_TAIL lane finisher (LANE_FINISH_Z_TAC = WORD_SIMPLE_SUBWORD_CONV +
     subword rewrites + WORD_RULE).  Same idiom as WB_TAIL_3..8's Q19 close.
     Measured standalone 114.6s -> 5.5s (needs-chain warm load), proof-preserving
     (hyps=0, statement unchanged -- SPECL consumers at build_q19_reduce_clean
     are untouched). *)
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [QQ0SPLIT] THEN
  REWRITE_TAC[WORD_SUBWORD_SUBWORD; JOIN_SUBWORD_RULES; WORD_SUBWORD_XOR] THEN
  REWRITE_TAC[JOIN_EQ_SPLIT] THEN CONJ_TAC THEN LANE_FINISH_Z_TAC);;

(* ------------------------------------------------------------------------- *)
(* BLOCK-ALGEBRA reconciliation                                               *)
(* facts.  These bridge the machine s289 accumulators (Q17/Q19/Q18 = the       *)
(* separable Sigma-PL/PH/PM triple, in raw word_reversefields/word_join/       *)
(* byteswap128-tower form) to the abstract kara_acc projection of an 8-quad    *)
(* list, so KARA_ACC_PACK_HELPER + KARATSUBA_BLOCK_PACKS_TO_PMUL_CLEAN can      *)
(* pack them to Sum_k word_pmul input_k h_k = BODY_Q19_CLOSE_ALGEBRA's prop3   *)
(* argument.  All are pure free-variable WORD_BLAST/WORD_RULE identities.      *)
(* --------------------------------------------------------------------------- *)

(* fact 1: the two byte-reversal spellings coincide (machine uses reversefields *)
(* 8, the spec/kara side uses word_bytereverse). *)
let WRF8_IS_BYTEREVERSE = prove
 (`!x:int128. word_reversefields 8 x = word_bytereverse x`,
  GEN_TAC THEN CONV_TAC WORD_BLAST);;

(* fact 2: karatsuba_mid is byteswap-invariant (it XORs the two 64-halves, and *)
(* byteswap128 swaps them).  Lets the htable mid cell `karatsuba_mid h` satisfy *)
(* KARATSUBA_BLOCK_PACKS_TO_PMUL_CLEAN's `subword hk (0,64) = karatsuba_mid     *)
(* (byteswap128 h)` precondition. *)
let KMID_BYTESWAP_INV = prove
 (`!h:int128. karatsuba_mid h = karatsuba_mid (byteswap128 h)`,
  GEN_TAC THEN REWRITE_TAC[karatsuba_mid; byteswap128] THEN CONV_TAC WORD_BLAST);;

(* fact 3 (block-0 SOFAR lane-collapse): block 0's operand enters via a rot64'd *)
(* word_join of the running accumulator SOFAR with the first ciphertext block.  *)
(* The reduce takes the (64,64) / (0,64) sub-lane of the XOR of the two joins,  *)
(* which collapses to the plain (0,64) / (64,64) sub-lane of `word_xor S X`.    *)
let LANE_COLLAPSE = prove
 (`(!S X:int128. word_subword (word_xor (word_subword (word_join S S:256 word) (64,128):128 word)
                            (word_subword (word_join X X:256 word) (64,128):128 word)) (64,64):64 word
    = word_subword (word_xor S X) (0,64):64 word) /\
   (!S X:int128. word_subword (word_xor (word_subword (word_join S S:256 word) (64,128):128 word)
                            (word_subword (word_join X X:256 word) (64,128):128 word)) (0,64):64 word
    = word_subword (word_xor S X) (64,64):64 word)`,
  CONJ_TAC THEN REPEAT GEN_TAC THEN CONV_TAC WORD_BLAST);;

(* fact 4 (pmull2/pmull PAIR mid-input lanes): the machine computes the PM mid  *)
(* products two blocks at a time (a pmull2 then pmull over the packed lanes of  *)
(* blocks A and B).  The (64,64)/(0,64) sub-lane of the XOR of the hi-join and  *)
(* lo-join recovers each single block's (lo XOR hi) mid-input. *)
(* The mid-input lane extractors used by the Q19 reduce.  Only the              *)
(* swapped-RHS PM_LANE_HI'/LO' variants below are consumed (build_q19_reduce_*  *)
(* at :1154/:1247): they spell the extracted mid-input in the (0,64)^(64,64)    *)
(* lane order that karatsuba_block_pm produces (word_pmul's first arg is atomic *)
(* to WORD_RULE, so the lane XOR must match SYNTACTICALLY, not up to comm).     *)
(* (the un-swapped PM_LANE_HI/LO were superseded by these and never              *)
(* referenced -- deleted.)                                                       *)
let PM_LANE_HI' = prove
 (`!A B:int128.
    word_subword (word_xor (word_join (word_subword (A:int128) (64,64):64 word) (word_subword (B:int128) (64,64):64 word):128 word)
                           (word_join (word_subword A (0,64):64 word) (word_subword B (0,64):64 word):128 word)) (64,64):64 word
    = word_xor (word_subword A (0,64):64 word) (word_subword A (64,64):64 word)`,
  REPEAT GEN_TAC THEN CONV_TAC WORD_BLAST);;

let PM_LANE_LO' = prove
 (`!A B:int128.
    word_subword (word_xor (word_join (word_subword (A:int128) (64,64):64 word) (word_subword (B:int128) (64,64):64 word):128 word)
                           (word_join (word_subword A (0,64):64 word) (word_subword B (0,64):64 word):128 word)) (0,64):64 word
    = word_xor (word_subword B (0,64):64 word) (word_subword B (64,64):64 word)`,
  REPEAT GEN_TAC THEN CONV_TAC WORD_BLAST);;

(* Block-0/block-1 SOFAR-pair PM mid-inputs.  The FIRST pmull2/                 *)
(* pmull PAIR folds in the running accumulator SOFAR, so block 0's operand      *)
(* enters as a rot64'd word_join of SOFAR with the first ciphertext block       *)
(* (not the plain packed pair the later blocks use).  These two lane lemmas     *)
(* recover the block-0 (outer (64,64), over word_xor SOFAR cph0) and block-1    *)
(* (outer (0,64), over cph1) mid-inputs, in karatsuba_block_pm's (0,64)^(64,64) *)
(* lane order.  Pure WORD_BLAST over free ss (=SOFAR), xx0 (=rev cph0), xx1     *)
(* (=rev cph1).  Together with PM_LANE'_HI/LO (the plain pairs {2,3}{4,5}{6,7}) *)
(* they reduce all 8 machine PM mid-inputs to kara form so PROJ_EQ PM closes.   *)
let LANE_COLLAPSE_PM_A = prove
 (`!ss xx0 xx1:int128.
    word_subword
     (word_xor
      (word_join
       (word_subword (word_xor (word_subword (word_join (ss:int128) ss:256 word) (64,128):128 word)
                               (word_subword (word_join (xx0:int128) xx0:256 word) (64,128):128 word)) (0,64):64 word)
       (word_subword xx1 (64,64):64 word):128 word)
      (word_join
       (word_subword (word_xor (word_subword (word_join (ss:int128) ss:256 word) (64,128):128 word)
                               (word_subword (word_join (xx0:int128) xx0:256 word) (64,128):128 word)) (64,64):64 word)
       (word_subword xx1 (0,64):64 word):128 word)) (64,64):64 word
    = word_xor (word_subword (word_xor ss xx0) (0,64):64 word)
               (word_subword (word_xor ss xx0) (64,64):64 word)`,
  REPEAT GEN_TAC THEN CONV_TAC WORD_BLAST);;

let LANE_COLLAPSE_PM_B = prove
 (`!ss xx0 xx1:int128.
    word_subword
     (word_xor
      (word_join
       (word_subword (word_xor (word_subword (word_join (ss:int128) ss:256 word) (64,128):128 word)
                               (word_subword (word_join (xx0:int128) xx0:256 word) (64,128):128 word)) (0,64):64 word)
       (word_subword xx1 (64,64):64 word):128 word)
      (word_join
       (word_subword (word_xor (word_subword (word_join (ss:int128) ss:256 word) (64,128):128 word)
                               (word_subword (word_join (xx0:int128) xx0:256 word) (64,128):128 word)) (64,64):64 word)
       (word_subword xx1 (0,64):64 word):128 word)) (0,64):64 word
    = word_xor (word_subword xx1 (0,64):64 word) (word_subword xx1 (64,64):64 word)`,
  REPEAT GEN_TAC THEN CONV_TAC WORD_BLAST);;

(* --------------------------------------------------------------------------- *)
(* Compose the value-equality + close the CHEAT.                                *)
(*                                                                             *)
(* build_q19_reduce_clean pl_t ph_t pm_t : given the three s289 accumulator     *)
(* terms (= read Q17/Q19/Q18 s289, over h/xi/ibytes/i), produces the CLEAN      *)
(* theorem  |- <machine reduce byteform> = ghash_polyval_acc (byteswap128 h)    *)
(*   (word_bytereverse xi) (MAP word_bytereverse (list_of_seq blk (8*(i+1))))   *)
(* hyps=0 — the invariant's Q19-at-(i+1) fold.  It chains:                      *)
(*   reduce_id  : byteform = polyval_reduce_prop3 (pack_corrected PL PH PM)     *)
(*                                        [WBN_MACHINE_REDUCE_IS_PROP3_PACK]     *)
(*   KARA_PACK_EQ (kqok): pack_corrected PL PH PM = SPEC_TOWERS                  *)
(*   body_ready2 : ghash..(8(i+1)) = polyval_reduce_prop3 SPEC_TOWERS           *)
(*                                        [BODY_Q19_CLOSE_ALGEBRA + involution]  *)
(* The 8 kqok side-conditions (subword hk_j (0,64) = karatsuba_mid ..) are      *)
(* discharged by choosing hk_j := word_join (word 0)(karatsuba_mid ..) so kqok  *)
(* holds unconditionally (SUBWORD_JOIN0 + KMID_BYTESWAP_INV) — a hyps-free      *)
(* lemma.  PROJ_PM is kept CONDITIONAL on kqok (hk free) then INST'd+MP'd — the *)
(* bake-hk-upfront variant fails PROJ_PM (subword(join 0 kmid) not plain kmid). *)
let SUBWORD_JOIN0 = prove
 (`!X:64 word. word_subword (word_join (word 0:64 word) X :128 word) (0,64):64 word = X`,
  GEN_TAC THEN CONV_TAC WORD_BLAST);;

let build_q19_reduce_clean pl_t ph_t pm_t =
  let bsh = `byteswap128 h` in
  let rec tower n = if n <= 1 then bsh else mk_comb(mk_comb(`polyval_dot`, tower(n-1)), bsh) in
  let inst_list = map (fun n -> (mk_comb(`byteswap128`, tower n), mk_var("h"^string_of_int n, `:int128`))) (2--8) in
  let body_inst2 = INST inst_list BODY_Q19_CLOSE_ALGEBRA in
  let body_ready2 = REWRITE_RULE[BYTESWAP128_INVOLUTION]
       (MP body_inst2 (prove(fst(dest_imp(concl body_inst2)), REWRITE_TAC[BYTESWAP128_INVOLUTION]))) in
  let spec_towers = rand(rhs(concl body_ready2)) in
  let rec strip_xor t = match t with Comb(Comb(Const("word_xor",_),a),b) -> strip_xor a @ strip_xor b | _ -> [t] in
  let spec_leaves = strip_xor spec_towers in
  let spec_input j = rand(rator (List.nth spec_leaves j)) in
  let mk_quadT j = let inp = spec_input j in let tw = tower(8-j) in
    mk_pair(inp, mk_pair(mk_comb(`byteswap128`, tw), mk_pair(mk_var("hk"^string_of_int j, `:int128`), tw))) in
  let quadsT = mk_list(map mk_quadT (0--7), `:int128#int128#int128#int128`) in
  let kqok_hyp j = mk_eq(mk_comb(mk_comb(`word_subword:int128->num#num->64 word`, mk_var("hk"^string_of_int j,`:int128`)), `(0,64)`),
                  mk_comb(`karatsuba_mid`, mk_comb(`byteswap128`, tower (8-j)))) in
  let kqok_hyps = map kqok_hyp (0--7) in
  let projtac = REWRITE_TAC[project_triples; kara_acc; karatsuba_block_pl; karatsuba_block_ph; karatsuba_block_pm] THEN
      CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[FST; SND] in
  let mk_proj sel concrete = mk_eq(mk_comb(sel, subst [quadsT, `QUADS:(int128#int128#int128#int128)list`]
              `kara_acc (project_triples QUADS) (word 0:int128) (word 0:int128) (word 0:int128)`), concrete) in
  let PROJ_PL = BETA_RULE(prove(mk_proj `FST:int128#int128#int128->int128` pl_t,
     projtac THEN REWRITE_TAC[WRF8_IS_BYTEREVERSE; LANE_COLLAPSE; BYTESWAP128_INVOLUTION] THEN CONV_TAC WORD_RULE)) in
  let PROJ_PH = BETA_RULE(prove(mk_proj `\t:int128#int128#int128. FST(SND t)` ph_t,
     projtac THEN REWRITE_TAC[WRF8_IS_BYTEREVERSE; LANE_COLLAPSE; BYTESWAP128_INVOLUTION] THEN CONV_TAC WORD_RULE)) in
  let PROJ_PM = BETA_RULE(prove(mk_imp(list_mk_conj kqok_hyps, mk_proj `\t:int128#int128#int128. SND(SND t)` pm_t),
     STRIP_TAC THEN projtac THEN ASM_REWRITE_TAC[] THEN
     REWRITE_TAC[WRF8_IS_BYTEREVERSE; LANE_COLLAPSE_PM_A; LANE_COLLAPSE_PM_B; PM_LANE_HI'; PM_LANE_LO'; BYTESWAP128_INVOLUTION] THEN CONV_TAC WORD_RULE)) in
  let kp = rand(lhs(concl PROJ_PL)) in
  let KARA_QUAD_OK_T = prove(mk_imp(list_mk_conj kqok_hyps, mk_comb(`kara_quad_ok`, quadsT)),
    STRIP_TAC THEN REWRITE_TAC[kara_quad_ok] THEN REPEAT CONJ_TAC THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC SYM_CONV THEN MATCH_ACCEPT_TAC KMID_BYTESWAP_INV) in
  let TESTQT = prove(mk_eq(subst [quadsT, `QUADS:(int128#int128#int128#int128)list`] `kara_quad_pmul QUADS (word 0:256 word)`, spec_towers),
    REWRITE_TAC[kara_quad_pmul; WORD_XOR_0_LEFT] THEN CONV_TAC WORD_RULE) in
  let helper = MP (SPECL [quadsT; `word 0:256 word`] KARA_ACC_PACK_HELPER)
                  (MP KARA_QUAD_OK_T (end_itlist CONJ (map ASSUME kqok_hyps))) in
  let KARA_PACK_EQ = prove(mk_imp(list_mk_conj kqok_hyps,
        mk_eq(list_mk_comb(`pack_corrected`, [pl_t; ph_t; pm_t]), spec_towers)),
    STRIP_TAC THEN
    (let pm_thm = MP PROJ_PM (end_itlist CONJ (map ASSUME kqok_hyps)) in
     let sndkp = mk_comb(`SND:int128#int128#int128->int128#int128`, kp) in
     let sndkp_eq = TRANS (GSYM(ISPEC sndkp PAIR)) (MK_COMB(AP_TERM `(,):int128->int128->int128#int128` PROJ_PH, pm_thm)) in
     let kp_triple = TRANS (GSYM(ISPEC kp PAIR)) (MK_COMB(AP_TERM `(,):int128->int128#int128->int128#int128#int128` PROJ_PL, sndkp_eq)) in
     REWRITE_TAC[GSYM TESTQT] THEN MP_TAC helper THEN
     REWRITE_TAC[LET_DEF; LET_END_DEF] THEN SUBST1_TAC kp_triple THEN
     CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[WORD_XOR_0_LEFT] THEN
     DISCH_THEN(SUBST1_TAC o SYM) THEN REFL_TAC)) in
  let reduce_id = SPECL [pl_t;ph_t;pm_t] WBN_MACHINE_REDUCE_IS_PROP3_PACK in
  let q19_final = TRANS (TRANS reduce_id (AP_TERM `polyval_reduce_prop3` (UNDISCH_ALL KARA_PACK_EQ))) (SYM body_ready2) in
  let q19_disch = itlist DISCH (hyp q19_final) q19_final in
  let hk_inst = map (fun j ->
     let kmid = mk_comb(`karatsuba_mid`, mk_comb(`byteswap128`, tower (8-j))) in
     (mk_comb(mk_comb(`word_join:64 word->64 word->128 word`, `word 0:64 word`), kmid),
      mk_var("hk"^string_of_int j, `:int128`))) (0--7) in
  let inst_thm = INST hk_inst q19_disch in
  MP inst_thm (prove(fst(dest_imp(concl inst_thm)),
     REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN CONV_TAC WORD_BLAST));;

(* Wire-in tactics.  The extract stashes pl/ph/pm@s289 into refs (before the      *)
(* ABBREV that makes the reduce window small); the close (run at the Q19 postcond  *)
(* conjunct) rebuilds the CLEAN thm from those refs and ACCEPTs it after mapping   *)
(* its concrete byteform LHS back to the goal's PL/PH/PM-abbreviated form + the    *)
(* 8*(i+1)=8*i+8 index normalization the postcond prep applied. *)
let wbn_q19_pl = ref `T` and wbn_q19_ph = ref `T` and wbn_q19_pm = ref `T`;;
let WBN_Q19_EXTRACT_ABBREV_TAC (sN:string) : tactic =
  fun (asl,w) ->
    let st = mk_var(sN,`:armstate`) in
    let get_rhs q =
      let c = find (fun c -> match c with
        | Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),qc),s)),_) when qc=q && s=st -> true
        | _ -> false) (map (concl o snd) asl) in
      rand c in
    wbn_q19_pl := get_rhs `Q17`;
    wbn_q19_ph := get_rhs `Q19`;
    wbn_q19_pm := get_rhs `Q18`;
    (ABBREV_TAC (mk_eq(`PL:int128`, !wbn_q19_pl)) THEN
     ABBREV_TAC (mk_eq(`PH:int128`, !wbn_q19_ph)) THEN
     ABBREV_TAC (mk_eq(`PM:int128`, !wbn_q19_pm))) (asl,w);;
let WBN_Q19_CLOSE_TAC : tactic =
  fun (asl,w) ->
    let clean = build_q19_reduce_clean (!wbn_q19_pl) (!wbn_q19_ph) (!wbn_q19_pm) in
    let defthms = filter (fun th -> match concl th with
      | Comb(Comb(Const("=",_),_),Var(("PL"|"PH"|"PM"),_)) -> true | _ -> false) (map snd asl) in
    let clean' = REWRITE_RULE (ARITH_RULE `8 * (i + 1) = 8 * i + 8` :: defthms) clean in
    ACCEPT_TAC clean' (asl,w);;

(* ------------------------------------------------------------------------- *)
(* The k-indexed variant of build_q19_reduce_clean, for the                   *)
(* PREPRETAIL Q19 close (index k = (nblk-9)DIV8, not the loop-body i).  The    *)
(* only delta is INST'ing BODY_Q19_CLOSE_ALGEBRA with i := idx first, so its   *)
(* spec fold reads ghash..(8*(idx+1)); everything else (the reduce identity    *)
(* + block algebra) is index-free.  The body could call this with `i:num`.     *)
let build_q19_reduce_clean_idx idx pl_t ph_t pm_t =
  let bsh = `byteswap128 h` in
  let rec tower n = if n <= 1 then bsh else mk_comb(mk_comb(`polyval_dot`, tower(n-1)), bsh) in
  let inst_list = map (fun n -> (mk_comb(`byteswap128`, tower n), mk_var("h"^string_of_int n, `:int128`))) (2--8) in
  let body_base = INST [idx, `i:num`] BODY_Q19_CLOSE_ALGEBRA in
  let body_inst2 = INST inst_list body_base in
  let body_ready2 = REWRITE_RULE[BYTESWAP128_INVOLUTION]
       (MP body_inst2 (prove(fst(dest_imp(concl body_inst2)), REWRITE_TAC[BYTESWAP128_INVOLUTION]))) in
  let spec_towers = rand(rhs(concl body_ready2)) in
  let rec strip_xor t = match t with Comb(Comb(Const("word_xor",_),a),b) -> strip_xor a @ strip_xor b | _ -> [t] in
  let spec_leaves = strip_xor spec_towers in
  let spec_input j = rand(rator (List.nth spec_leaves j)) in
  let mk_quadT j = let inp = spec_input j in let tw = tower(8-j) in
    mk_pair(inp, mk_pair(mk_comb(`byteswap128`, tw), mk_pair(mk_var("hk"^string_of_int j, `:int128`), tw))) in
  let quadsT = mk_list(map mk_quadT (0--7), `:int128#int128#int128#int128`) in
  let kqok_hyp j = mk_eq(mk_comb(mk_comb(`word_subword:int128->num#num->64 word`, mk_var("hk"^string_of_int j,`:int128`)), `(0,64)`),
                  mk_comb(`karatsuba_mid`, mk_comb(`byteswap128`, tower (8-j)))) in
  let kqok_hyps = map kqok_hyp (0--7) in
  let projtac = REWRITE_TAC[project_triples; kara_acc; karatsuba_block_pl; karatsuba_block_ph; karatsuba_block_pm] THEN
      CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[FST; SND] in
  let mk_proj sel concrete = mk_eq(mk_comb(sel, subst [quadsT, `QUADS:(int128#int128#int128#int128)list`]
              `kara_acc (project_triples QUADS) (word 0:int128) (word 0:int128) (word 0:int128)`), concrete) in
  let PROJ_PL = BETA_RULE(prove(mk_proj `FST:int128#int128#int128->int128` pl_t,
     projtac THEN REWRITE_TAC[WRF8_IS_BYTEREVERSE; LANE_COLLAPSE; BYTESWAP128_INVOLUTION] THEN CONV_TAC WORD_RULE)) in
  let PROJ_PH = BETA_RULE(prove(mk_proj `\t:int128#int128#int128. FST(SND t)` ph_t,
     projtac THEN REWRITE_TAC[WRF8_IS_BYTEREVERSE; LANE_COLLAPSE; BYTESWAP128_INVOLUTION] THEN CONV_TAC WORD_RULE)) in
  let PROJ_PM = BETA_RULE(prove(mk_imp(list_mk_conj kqok_hyps, mk_proj `\t:int128#int128#int128. SND(SND t)` pm_t),
     STRIP_TAC THEN projtac THEN ASM_REWRITE_TAC[] THEN
     REWRITE_TAC[WRF8_IS_BYTEREVERSE; LANE_COLLAPSE_PM_A; LANE_COLLAPSE_PM_B; PM_LANE_HI'; PM_LANE_LO'; BYTESWAP128_INVOLUTION] THEN CONV_TAC WORD_RULE)) in
  let kp = rand(lhs(concl PROJ_PL)) in
  let KARA_QUAD_OK_T = prove(mk_imp(list_mk_conj kqok_hyps, mk_comb(`kara_quad_ok`, quadsT)),
    STRIP_TAC THEN REWRITE_TAC[kara_quad_ok] THEN REPEAT CONJ_TAC THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC SYM_CONV THEN MATCH_ACCEPT_TAC KMID_BYTESWAP_INV) in
  let TESTQT = prove(mk_eq(subst [quadsT, `QUADS:(int128#int128#int128#int128)list`] `kara_quad_pmul QUADS (word 0:256 word)`, spec_towers),
    REWRITE_TAC[kara_quad_pmul; WORD_XOR_0_LEFT] THEN CONV_TAC WORD_RULE) in
  let helper = MP (SPECL [quadsT; `word 0:256 word`] KARA_ACC_PACK_HELPER)
                  (MP KARA_QUAD_OK_T (end_itlist CONJ (map ASSUME kqok_hyps))) in
  let KARA_PACK_EQ = prove(mk_imp(list_mk_conj kqok_hyps,
        mk_eq(list_mk_comb(`pack_corrected`, [pl_t; ph_t; pm_t]), spec_towers)),
    STRIP_TAC THEN
    (let pm_thm = MP PROJ_PM (end_itlist CONJ (map ASSUME kqok_hyps)) in
     let sndkp = mk_comb(`SND:int128#int128#int128->int128#int128`, kp) in
     let sndkp_eq = TRANS (GSYM(ISPEC sndkp PAIR)) (MK_COMB(AP_TERM `(,):int128->int128->int128#int128` PROJ_PH, pm_thm)) in
     let kp_triple = TRANS (GSYM(ISPEC kp PAIR)) (MK_COMB(AP_TERM `(,):int128->int128#int128->int128#int128#int128` PROJ_PL, sndkp_eq)) in
     REWRITE_TAC[GSYM TESTQT] THEN MP_TAC helper THEN
     REWRITE_TAC[LET_DEF; LET_END_DEF] THEN SUBST1_TAC kp_triple THEN
     CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[WORD_XOR_0_LEFT] THEN
     DISCH_THEN(SUBST1_TAC o SYM) THEN REFL_TAC)) in
  let reduce_id = SPECL [pl_t;ph_t;pm_t] WBN_MACHINE_REDUCE_IS_PROP3_PACK in
  let q19_final = TRANS (TRANS reduce_id (AP_TERM `polyval_reduce_prop3` (UNDISCH_ALL KARA_PACK_EQ))) (SYM body_ready2) in
  let q19_disch = itlist DISCH (hyp q19_final) q19_final in
  let hk_inst = map (fun j ->
     let kmid = mk_comb(`karatsuba_mid`, mk_comb(`byteswap128`, tower (8-j))) in
     (mk_comb(mk_comb(`word_join:64 word->64 word->128 word`, `word 0:64 word`), kmid),
      mk_var("hk"^string_of_int j, `:int128`))) (0--7) in
  let inst_thm = INST hk_inst q19_disch in
  MP inst_thm (prove(fst(dest_imp(concl inst_thm)),
     REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN CONV_TAC WORD_BLAST));;

(* WBN_Q19_PREPRETAIL_CLOSE_TAC idx : closes BOTH prepretail GHASH conjuncts     *)
(* (run per-conjunct after ENSURES_FINAL + REPEAT CONJ_TAC, guarded on           *)
(* ghash_polyval_acc).  idx = the prepretail index (`k:num`).  The Q19 conjunct  *)
(* (read Q19 = ghash..(8*(k+1))) and the Q16 staging conjunct                    *)
(* (read Q16 = word_subword(word_join <caught_up> <caught_up>)(64,128)) both     *)
(* reduce, after ASM_REWRITE substitutes the machine byteform + the CLEAN        *)
(* value-equality folds it to ghash..(8*k+8), to the pure index identity         *)
(* 8*k+8 = 8*(k+1), closed by ARITH + REFL.                                      *)
let WBN_Q19_PREPRETAIL_CLOSE_TAC (idx:term) : tactic =
  fun (asl,w) ->
    let clean = build_q19_reduce_clean_idx idx (!wbn_q19_pl) (!wbn_q19_ph) (!wbn_q19_pm) in
    let defthms = filter (fun th -> match concl th with
      | Comb(Comb(Const("=",_),_),Var(("PL"|"PH"|"PM"),_)) -> true | _ -> false) (map snd asl) in
    let clean' = REWRITE_RULE (ARITH_RULE `8 * (i + 1) = 8 * i + 8` :: defthms) clean in
    (ASM_REWRITE_TAC[] THEN REWRITE_TAC[clean'] THEN
     REWRITE_TAC[ARITH_RULE `8 * k + 8 = 8 * (k + 1)`] THEN
     TRY REFL_TAC) (asl,w);;

(* ------------------------------------------------------------------------- *)
(* 6. Route-(b) tool: strengthen an ensures postcondition with a frame-       *)
(*    PRESERVED fact, with NO re-simulation.  Pure ensures/eventually logic.  *)
(*                                                                            *)
(* This is the clean combinator for WBN_FRONT_BUF_EXT (and reusable in the    *)
(* Phase-6 recompose): given `ensures step P Q C` and that the frame C, from  *)
(* precondition P, preserves R (i.e. !s s'. P s /\ C s s' ==> R s'), we get   *)
(* `ensures step P (\s. Q s /\ R s) C` for free.                              *)
(*                                                                            *)
(* Usage for WBN_FRONT_BUF_EXT: take R s = (the 3 loop-constants at s:         *)
(*   read (memory :> bytes (in_p,16*nblk)) s = num_of_bytelist ibytes /\      *)
(*   read (memory :> bytes128 key_p) s = k0 /\ htable_mem_dec h htbl_p s).     *)
(* The preservation obligation !s s'. wb_front_pre_tm s /\ wb_front_frame_tm  *)
(* s s' ==> R s' holds because none of in_p's input bytes, key_p, or htbl_p   *)
(* memory is in wb_front_frame_tm's MAYCHANGE (only out_p/xi_p/ivec_p/stack + *)
(* Q-regs are).  Discharge it by: STRIP the frame (MAYCHANGE ... ,, ...),     *)
(* then for each read-conjunct use the nonoverlapping hyps + the fact the     *)
(* frame's memory writes miss those regions (the standard READ_OVER_WRITE /   *)
(* MAYCHANGE-preservation reasoning; htable_mem_dec unfolds to bytes128 reads *)
(* off htbl_p that are likewise disjoint).                                    *)
(* ------------------------------------------------------------------------- *)

let ENSURES_ADD_PRESERVED = prove
 (`!(step:A->A->bool) P Q R C.
    ensures step P Q C /\ (!s s'. P s /\ C s s' ==> R s')
    ==> ensures step P (\s. Q s /\ R s) C`,
  REWRITE_TAC[ensures] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  X_GEN_TAC `s0:A` THEN DISCH_TAC THEN
  SUBGOAL_THEN `!s':A. Q s' /\ C (s0:A) s' ==> (Q s' /\ R s') /\ C s0 s'`
    (MP_TAC o MATCH_MP EVENTUALLY_MONO) THENL
   [X_GEN_TAC `s1:A` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(fun th -> MP_TAC(SPECL [`s0:A`;`s1:A`] th)) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN ACCEPT_TAC];
    DISCH_THEN(MP_TAC o SPECL [`step:A->A->bool`; `s0:A`]) THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* 7. Phase 2 hyp-gap fix: WBN_FRONT_BUF_EXT.                                 *)
(*                                                                            *)
(* The i=0 invariant instance needs 3 loop-CONSTANTS at the loop head that    *)
(* WBN_FRONT_BUF's harvested postcond drops (GAP note above):                 *)
(*   read (memory :> bytes (in_p,16*nblk)) s = num_of_bytelist ibytes         *)
(*   read (memory :> bytes128 key_p) s = k0                                   *)
(*   htable_mem_dec h htbl_p s                                                *)
(* These are preserved by the front MAYCHANGE frame (which writes only        *)
(* out_p/xi_p/ivec_p/stack + Q-regs), PROVIDED out_p is disjoint from in_p/   *)
(* key_p/htbl_p.  wbn_front_hyps_tm was missing exactly those 3 out_p         *)
(* disjointness conjuncts (they ARE in the <=8-block band hyps).                                  *)
(*                                                                            *)
(* ROUTE (b) (ENSURES_ADD_PRESERVED), NOT route (a): we DON'T                 *)
(* re-run the front sim with widened hyps (the build_state_postcond_tms2      *)
(* re-harvest is the risky part).  Instead keep the proven                    *)
(* WBN_FRONT_BUF verbatim and STRENGTHEN its postcond with the 3 constants    *)
(* via ENSURES_ADD_PRESERVED: leg1 = WBN_FRONT_BUF (narrow hyps <= wide hyps, *)
(* closed by MATCH_MP_TAC + ASM_REWRITE), leg2 = the pure frame-preservation  *)
(* obligation (no sim).  Whole thing proves in ~4s.                           *)
(* ------------------------------------------------------------------------- *)

(* widened front hyps = wbn_front_hyps_tm + the 3 out_p disjointness conjuncts *)
let wbn_front_hyps_wide_tm =
  mk_conj(wbn_front_hyps_tm,
    `nonoverlapping (out_p:int64,16 * nblk) (in_p:int64,16 * nblk) /\
     nonoverlapping (out_p:int64,16 * nblk) (key_p:int64,240) /\
     nonoverlapping (out_p:int64,16 * nblk) (htbl_p:int64,192)`);;

(* the WBN_FRONT_BUF pieces (P = precond, Q0 = harvested postcond, C = frame) *)
let wbn_front_P_tm, wbn_front_Q0_tm, wbn_front_C_tm =
  let ens = snd(dest_imp(snd(strip_forall(concl WBN_FRONT_BUF)))) in
  rand(rator(rator ens)), rand(rator ens), rand ens;;

(* R = the 3 loop-constants, taken verbatim from WBN_FRONT_BUF's precond so
   they match wbn_loop_invariant_raw's conjuncts syntactically. *)
let wbn_front_R_tm =
  let sv = fst(dest_abs wbn_front_P_tm) in
  mk_abs(sv, list_mk_conj
    [`read (memory :> bytes (in_p:int64,16 * nblk)) s = num_of_bytelist ibytes`;
     `read (memory :> bytes128 (key_p:int64)) s = (k0:int128)`;
     `read (memory :> bytes128 (word_add key_p (word 16))) s = (k1:int128)`;
     `read (memory :> bytes128 (word_add key_p (word 32))) s = (k2:int128)`;
     `read (memory :> bytes128 (word_add key_p (word 48))) s = (k3:int128)`;
     `read (memory :> bytes128 (word_add key_p (word 64))) s = (k4:int128)`;
     `read (memory :> bytes128 (word_add key_p (word 80))) s = (k5:int128)`;
     `read (memory :> bytes128 (word_add key_p (word 96))) s = (k6:int128)`;
     `read (memory :> bytes128 (word_add key_p (word 112))) s = (k7:int128)`;
     `read (memory :> bytes128 (word_add key_p (word 128))) s = (k8:int128)`;
     `read (memory :> bytes128 (word_add key_p (word 144))) s = (k9:int128)`;
     `read (memory :> bytes128 (word_add key_p (word 160))) s = (k10:int128)`;
     `read (memory :> bytes128 (word_add key_p (word 176))) s = (k11:int128)`;
     `read (memory :> bytes128 (word_add key_p (word 192))) s = (k12:int128)`;
     `read (memory :> bytes128 (word_add key_p (word 208))) s = (k13:int128)`;
     `read (memory :> bytes128 (word_add key_p (word 224))) s = (k14:int128)`;
     `htable_mem_dec h (htbl_p:int64) s`]);;

(* EXT goal: wide hyps ==> ensures arm P (\s. Q0 s /\ R s) C *)
let wbn_front_ext_goal =
  let newQ = mk_abs(fst(dest_abs wbn_front_P_tm),
    mk_conj(rhs(concl(BETA_CONV(mk_comb(wbn_front_Q0_tm,fst(dest_abs wbn_front_P_tm))))),
            rhs(concl(BETA_CONV(mk_comb(wbn_front_R_tm,fst(dest_abs wbn_front_P_tm))))))) in
  let ens = list_mk_comb(`ensures arm`,[wbn_front_P_tm; newQ; wbn_front_C_tm]) in
  list_mk_forall(wb_front_vars, mk_imp(wbn_front_hyps_wide_tm, ens));;

(* leg2 helper: push a read through the whole MAYCHANGE write-chain to `read c s`
   using the goal's nonoverlapping assumptions (memory-vs-memory orthogonality),
   then close via the precond assumption `read c s = value`.  Uses the
   assumption-aware COMPONENTS_READ_OVER_WRITE_ORTHOGONAL_CONV (common/components).
   Applied once per R-conjunct (register writes fold away, memory writes need the
   nonoverlapping facts). *)
let WBN_PUSH_LHS_READ_TAC : tactic =
  W(fun (asl,w) ->
    let thl = map snd asl in
    let cxt = (NONOVERLAPPING_DRIVERS thl, FILTER_CANONIZE_ASSUMPTIONS thl) in
    CONV_TAC(LAND_CONV(COMPONENTS_READ_OVER_WRITE_ORTHOGONAL_CONV cxt))) THEN
  ASM_REWRITE_TAC[];;

let WBN_FRONT_BUF_EXT = prove(wbn_front_ext_goal,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC ENSURES_ADD_PRESERVED THEN CONJ_TAC THENL
   [MATCH_MP_TAC WBN_FRONT_BUF THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[htable_mem_dec] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; MAYCHANGE; SEQ_ID] THEN
    REWRITE_TAC[GSYM SEQ_ASSOC] THEN
    PURE_REWRITE_TAC[ASSIGNS_SEQ] THEN
    CONV_TAC(REDEPTH_CONV BETA_CONV) THEN
    REWRITE_TAC[ASSIGNS_THM] THEN
    CONV_TAC(REDEPTH_CONV BETA_CONV) THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o
      check (fun th -> is_eq(concl th) &&
        (match rhs(concl th) with Var("s'",_) -> true | _ -> false))) THEN
    WBN_PUSH_LHS_READ_TAC]);;

(* ------------------------------------------------------------------------- *)
(* WBN_FRONT_PREFIX_EXT -- the shared prefix strengthened with the              *)
(* R loop-constants (key schedule + input bytes + htable), so the 9..16 front  *)
(* leg (WBN_FRONT_TO_PREP_916, whose exit post wbn_core_applied 0 references    *)
(* the htable + key reads) can reuse the ONE prefix sim.  Mirror of             *)
(* WBN_FRONT_BUF_EXT: R is preserved through the front MAYCHANGE frame          *)
(* (ENSURES_ADD_PRESERVED).  Band = wbn_front_hyps_ge9_wide_tm (the WIDE hyps   *)
(* WBN_PUSH_LHS_READ_TAC needs to push R reads past the out_p stores); the 916  *)
(* band 9..16-WIDE discharges it by hyp-strengthening.  (WBN_FRONT_BUF's own    *)
(* i=0 post needs no R, so it reuses the plain WBN_FRONT_PREFIX directly.)      *)
(* ------------------------------------------------------------------------- *)
let wbn_front_hyps_ge9_wide_tm =
  let rec repl t = match t with
    | Comb(Comb(Const("/\\",_),a),b) -> mk_conj(repl a, repl b)
    | _ -> if t = `17 <= nblk` then `9 <= nblk` else t in
  repl wbn_front_hyps_wide_tm;;

let wbn_front_prefix_ext_goal =
  let sv = fst(dest_abs wbn_front_prefix_postcond) in
  let newQ = mk_abs(sv,
    mk_conj(rhs(concl(BETA_CONV(mk_comb(wbn_front_prefix_postcond,sv)))),
            rhs(concl(BETA_CONV(mk_comb(wbn_front_R_tm,sv)))))) in
  let ens = list_mk_comb(`ensures arm`,[wbn_front_P_tm; newQ; wbn_front_C_tm]) in
  list_mk_forall(wb_front_vars, mk_imp(wbn_front_hyps_ge9_wide_tm, ens));;

let WBN_FRONT_PREFIX_EXT = prove(wbn_front_prefix_ext_goal,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC ENSURES_ADD_PRESERVED THEN CONJ_TAC THENL
   [MATCH_MP_TAC WBN_FRONT_PREFIX THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[htable_mem_dec] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; MAYCHANGE; SEQ_ID] THEN
    REWRITE_TAC[GSYM SEQ_ASSOC] THEN
    PURE_REWRITE_TAC[ASSIGNS_SEQ] THEN
    CONV_TAC(REDEPTH_CONV BETA_CONV) THEN
    REWRITE_TAC[ASSIGNS_THM] THEN
    CONV_TAC(REDEPTH_CONV BETA_CONV) THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o
      check (fun th -> is_eq(concl th) &&
        (match rhs(concl th) with Var("s'",_) -> true | _ -> false))) THEN
    WBN_PUSH_LHS_READ_TAC]);;

(* the strengthened prefix postcond term (prefix_post /\ R), for the 916 TRANS. *)
let wbn_front_prefix_ext_post =
  rand(rator(snd(dest_imp(snd(strip_forall(concl WBN_FRONT_PREFIX_EXT))))));;

(* ------------------------------------------------------------------------- *)
(* 8. Phase 2 CLOSE: WBN_LOOP_INVARIANT_ENTRY_RAW.                                *)
(*                                                                            *)
(* THE entry subgoal that ENSURES_WHILE_UP_TAC produces for the main loop:    *)
(*   ensures arm (\s. decodes /\ PC = pc+0x20 /\ precondition s)              *)
(*               (\s. decodes /\ PC = pc+0x4a0 /\ wbn_loop_invariant_raw ... 0 s) *)
(*               frame                                                        *)
(* i.e. the front (entry -> loop head) establishes the i=0 invariant.  Proved *)
(* by weakening WBN_FRONT_BUF_EXT's postcond (Q0 /\ 3-loop-constants) down to *)
(* the i=0 invariant, via ENSURES_POSTCONDITION_THM.  The implication         *)
(* (Q0 s /\ R s) ==> inv 0 s is the Sec-4 closing recipe, PLUS a              *)
(* final numeral-normalization pass: after the recipe the goal                *)
(* is a conjunction of trivial `f (word n) = f (word (0+n))` /                 *)
(* `SUB_LIST(16*(0+k)..) = SUB_LIST(16*k..)` equalities + the j<8 store        *)
(* forall; ADD_CLAUSES + NUM_MULT_CONV + GCM_CTR_ADD_0 (block-0 = ctr0) close  *)
(* them against the postcond hyps.                                            *)
(* ------------------------------------------------------------------------- *)

(* i=0 invariant applied to all 27 loop params, as a (num->armstate->bool). *)
let wbn_inv_applied =
  list_mk_comb(`wbn_loop_invariant_raw`,
    [`pc:num`;`ctr0:int128`;`in_p:int64`;`out_p:int64`;`xi_p:int64`;`ivec_p:int64`;
     `key_p:int64`;`htbl_p:int64`;`stackpointer:int64`;`nblk:num`;`ibytes:byte list`;
     `xi:int128`;`h:int128`;`k0:int128`;`k1:int128`;`k2:int128`;`k3:int128`;`k4:int128`;
     `k5:int128`;`k6:int128`;`k7:int128`;`k8:int128`;`k9:int128`;`k10:int128`;`k11:int128`;
     `k12:int128`;`k13:int128`;`k14:int128`]);;

(* post = \s. decodes /\ PC = pc+0x4a0 /\ inv 0 s *)
let wbn_entry_post =
  subst [wbn_inv_applied,`INVAPP:num->armstate->bool`]
    `\s:armstate. aligned_bytes_loaded s (word pc) aesv8_gcm_8x_dec_256_wb_mc /\
                  read PC s = word (pc + 0x4c0) /\
                  INVAPP (0:num) s`;;

let wbn_entry_goal =
  let ens = list_mk_comb(`ensures arm`,[wbn_front_P_tm; wbn_entry_post; wbn_front_C_tm]) in
  list_mk_forall(wb_front_vars, mk_imp(wbn_front_hyps_wide_tm, ens));;

(* the Q to weaken from: WBN_FRONT_BUF_EXT's postcond = \s. Q0 s /\ R s *)
let wbn_extQ =
  let sv = fst(dest_abs wbn_front_P_tm) in
  mk_abs(sv, mk_conj(
    rhs(concl(BETA_CONV(mk_comb(wbn_front_Q0_tm,sv)))),
    rhs(concl(BETA_CONV(mk_comb(wbn_front_R_tm,sv)))))) ;;

let WBN_LOOP_INVARIANT_ENTRY_RAW = prove(wbn_entry_goal,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN
  EXISTS_TAC wbn_extQ THEN CONJ_TAC THENL
   [(* (Q0 x /\ R x) ==> decodes /\ PC=pc+0x4c0 /\ inv 0 x *)
    GEN_TAC THEN REWRITE_TAC[wbn_loop_invariant_raw] THEN
    CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN STRIP_TAC THEN
    CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM GCM_CTR_ADD_LANES]) THEN
    REWRITE_TAC[GCM_CTR_INC_ITER_ADD; GCM_CTR_ADD_1; GSYM GCM_CTR_ADD_LANES] THEN
    REWRITE_TAC[list_of_seq; MAP; ghash_polyval_acc] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[GCM_CTR_INC_LANES; GCM_CTR_INC2_LANES;
       GCM_CTR_INC3_LANES; GCM_CTR_INC4_LANES; GCM_CTR_INC5_LANES;
       GCM_CTR_INC6_LANES; GCM_CTR_INC7_LANES]) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM GCM_CTR_ADD_LANES]) THEN
    REWRITE_TAC[GCM_CTR_ADD_0] THEN
    CONV_TAC(ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN
    CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN
    REWRITE_TAC[WORD_ADD_0] THEN ASM_REWRITE_TAC[] THEN
    (* numeral-normalization tail: 0+n, 16*(0+k), block-0=ctr0             *)
    REWRITE_TAC[ADD_CLAUSES] THEN CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN
    CONV_TAC(ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN
    REWRITE_TAC[WORD_ADD_0; MULT_CLAUSES] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM GCM_CTR_ADD_LANES; GCM_CTR_ADD_0] THEN
    CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN ASM_REWRITE_TAC[GCM_CTR_ADD_0] THEN
    (* Q30 residual: the only conjunct the closer leaves
       open after the Q30 patch.  The i=0 raw tower (top lane += 12 then += 1)
       collapses to gcm_ctr_raw (word 13) ctr0 = the invariant's 8*0+13 value.
       VALIDATED. *)
    REWRITE_TAC[gcm_ctr_raw_def;
      WORD_RULE `word_add (word_add (x:32 word) (word 12)) (word 1) =
                 word_add x (word 13)`;
      WORD_ADD_0];
    (* the ensures = WBN_FRONT_BUF_EXT *)
    MATCH_MP_TAC WBN_FRONT_BUF_EXT THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* 9. Phase 4 launch: PC/decode-free CORE invariant + split.                  *)
(*                                                                            *)
(* wbn_loop_invariant_raw bakes in two conjuncts the ENSURES_WHILE tactics MUST   *)
(* own themselves:                                                            *)
(*   C1  aligned_bytes_loaded s (word pc) ...mc   (program_decodes)           *)
(*   C2  read PC s = word (pc + 1216)             (the loop-head PC)          *)
(* Every ENSURES_WHILE_* template threads `program_decodes` and `read PC =    *)
(* word pcX` around its OWN `loopinv i s`, applying loopinv at BOTH pc1 (head)*)
(* and pc2 (back-edge/exit).  A PC baked into the invariant is therefore      *)
(* redundant at pc1 and *contradictory* at pc2 (it would force PC=0x4a0 in a  *)
(* state whose PC is 0x9ec/0x9f0).  Standard s2n invariants (keccak,          *)
(* emontredc) are PC/decode-free for exactly this reason.                     *)
(*                                                                            *)
(* wbn_loop_inv_core_raw = wbn_loop_invariant_raw with C1,C2 removed (built by        *)
(* dropping the first two conjuncts, so it stays in sync with the frozen      *)
(* definition automatically).  WBN_INV_RAW_SPLIT is the bridge                    *)
(*   wbn_loop_invariant_raw ... i s <=>                                           *)
(*     aligned_bytes_loaded s (word pc) mc /\ read PC s = word (pc+1184) /\   *)
(*     wbn_loop_inv_core_raw ... i s                                              *)
(* so the ENTRY theorem (which yields the LHS at i=0) feeds any tactic that   *)
(* wants the RHS, and the loop body/exit can carry ONLY the core across the   *)
(* frame while the tactic supplies decode+PC.                                 *)
(* ------------------------------------------------------------------------- *)

let wbn_loop_inv_core_raw =
  let eqn = snd(strip_forall(concl wbn_loop_invariant_raw)) in
  let lhs_full, rhs_full = dest_eq eqn in
  let hd, params = strip_comb lhs_full in
  let ivars, body = strip_abs rhs_full in
  let cs = conjuncts body in
  (* C1 = aligned_bytes_loaded, C2 = read PC = word(pc+1184); drop both *)
  let core_body = list_mk_conj (List.tl (List.tl cs)) in
  let core_rhs = list_mk_abs(ivars, core_body) in
  let newhead = mk_var("wbn_loop_inv_core_raw", type_of hd) in
  new_definition (mk_eq(list_mk_comb(newhead, params), core_rhs));;

let wbn_inv_args =
  snd(strip_comb(fst(dest_eq(snd(strip_forall(concl wbn_loop_invariant_raw))))));;

let WBN_INV_RAW_SPLIT = prove
 (list_mk_forall(wbn_inv_args @ [`i:num`;`s:armstate`],
    mk_eq(
      list_mk_comb(`wbn_loop_invariant_raw`, wbn_inv_args @ [`i:num`;`s:armstate`]),
      list_mk_conj[
        `aligned_bytes_loaded s (word pc) aesv8_gcm_8x_dec_256_wb_mc`;
        `read PC s = word (pc + 1216)`;
        list_mk_comb(`wbn_loop_inv_core_raw`, wbn_inv_args @ [`i:num`;`s:armstate`])])),
  REWRITE_TAC[wbn_loop_invariant_raw; wbn_loop_inv_core_raw] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[CONJ_ACI]);;

(* ------------------------------------------------------------------------- *)
(* 9b. Phase 4 PREREQ: the RAW counter accumulator Q30.                        *)
(*                                                                            *)
(* CRITICAL FINDING: the frozen wbn_loop_invariant_raw (Sec 4) is                  *)
(* INCOMPLETE for the loop body.  The body's FIRST instruction                 *)
(*   0x4a0  rev32 v5, v30                                                       *)
(* reads Q30 -- the running CTR-block counter in its rev32-pending "raw" form  *)
(* -- but wbn_loop_invariant_raw has NO Q30 conjunct, so Q5 immediately goes       *)
(* symbolic in `read Q30 s0` and the body cannot close.  Static live-in        *)
(* analysis of the whole body (0x4a0..0x9ec) shows Q30 is the ONLY vector      *)
(* register whose first use is a READ and which the invariant fails to pin     *)
(* (Q0..Q4, Q19, Q31 are live-in AND already pinned).                          *)
(*                                                                            *)
(* WBN_FRONT_BUF DID harvest a Q30 conjunct (its postcond conjunct 46), as a   *)
(* raw bit-tower; Sec 4's generalization to symbolic i simply dropped it.      *)
(* The value at the loop head (iteration i) is gcm_ctr_raw (word (8*i+13)) ctr0*)
(* -- CONFIRMED: WBN_FRONT_BUF's conjunct-46 term = gcm_ctr_raw (word 13) ctr0 *)
(* at i=0 (proved via gcm_ctr_raw_def + WORD_RULE add-merge + WORD_ADD_0).      *)
(*                                                                            *)
(* gcm_ctr_raw w ctr0 is the counter in the "byte-grouped, top-lane += w"      *)
(* representation the hardware keeps in v30: its top 32-bit lane is            *)
(* word_add (<brev of ctr0[96:128] bytes>) w, the low 96 bits are ctr0's low   *)
(* lanes byte-grouped.  The body does rev32(v30) -> AES keystream input for    *)
(* block 8i+13, then add v30,v30,v31 (v31 = word 2^96) to advance to 8i+14.    *)
(*                                                                            *)
(* THE FIX (applied below): add a Q30 conjunct                                 *)
(*   read Q30 s = gcm_ctr_raw (word (8 * i + 13)) ctr0                          *)
(* to wbn_loop_invariant_raw (and thus wbn_loop_inv_core_raw auto-tracks it).  Then     *)
(* WBN_FRONT_BUF_EXT / WBN_LOOP_INVARIANT_ENTRY_RAW must re-establish it at i=0     *)
(* (from conjunct 46 via the gcm_ctr_raw (word 13) identity), and the step     *)
(* case advances it 8i+13 -> 8(i+1)+13 = 8i+21 over the 8 in-body increments.  *)
(* ------------------------------------------------------------------------- *)

(* gcm_ctr_raw_def moved to Sec 2: the Sec-4 invariant now pins
   Q30 = gcm_ctr_raw (word (8*i+13)) ctr0, so the definition must precede Sec 4.
   Its body-only algebra lemmas remain here. *)

(* (SUBW_RAW_* + GCM_CTR_RAW_INCR MOVED up to the band-tail region.)               *)

(* REV32 fold: `rev32 v_,v30` (esize=32) applied to gcm_ctr_raw w ctr0 yields
   gcm_ctr_add w ctr0 -- the proper AES keystream input for CTR block w.  The
   arm_REV32_VEC tower is auto-generated by the stepper (~8k chars, deterministic),
   so the reusable form is a TACTIC that folds `read Qd sN` after a rev32-of-v30 step.
   VALIDATED recipe (proves in ~2s):
     <capture the rev32 tower T = rhs of `read Qd sN`>, then prove `T = gcm_ctr_add w ctr0` by
       REWRITE_TAC[gcm_ctr_raw_def] THEN
       GEN_REWRITE_TAC RAND_CONV [GCM_CTR_ADD_LANES] THEN
       <SPEC_TAC the `word_add <topbytes> w` atom to a fresh 32-word> THEN
       GEN_TAC THEN CONV_TAC WORD_BLAST
   CRUCIAL: unfold gcm_ctr_raw EVERYWHERE (plain REWRITE_TAC[gcm_ctr_raw_def], NOT ONCE_DEPTH)
   and unfold the RHS via GCM_CTR_ADD_LANES so BOTH sides carry only the shared symbolic-add
   atom; THEN SPEC_TAC that atom away before WORD_BLAST (WORD_BLAST on a live symbolic
   `word_add _ w` OOMs -- see Sec 2 AVOID).  The GCM_SIMD_SIMPLIFY_TAC used per body step may
   already collapse part of the rev32 tower; adapt the captured-tower shape accordingly.

   REV32_FOLD_TAC qd sn wtm: rewrite the assumption `read qd sn = <rev32 tower>` so its
   rhs becomes `gcm_ctr_add wtm ctr0`.  Proves the fold equation on the fly via the recipe,
   generalizing over wtm so WORD_BLAST never meets the symbolic addend. *)
let REV32_FOLD_TAC (qd:string) (sn:string) (wtm:term) : tactic =
  fun (asl,gl) ->
    let tower = tryfind (fun (_,th) -> match concl th with
      | Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),c),st)),r)
          when string_of_term c = qd && (try fst(dest_var st)=sn with _ -> false) -> r
      | _ -> fail()) asl in
    (* generalize wtm -> a fresh w:32 word, prove the fold for symbolic w, then re-specialize *)
    let tower_gen = subst [`w:32 word`, wtm] tower in
    let fold_thm = prove(mk_eq(tower_gen, `gcm_ctr_add w ctr0`),
      REWRITE_TAC[gcm_ctr_raw_def] THEN
      GEN_REWRITE_TAC RAND_CONV [GCM_CTR_ADD_LANES] THEN
      W(fun (_,gw) ->
         let atom = find_term (fun t -> match t with
           | Comb(Comb(Const("word_add",_),_),Var("w",_)) -> true | _ -> false) gw in
         SPEC_TAC(atom, `aa:32 word`)) THEN
      GEN_TAC THEN CONV_TAC WORD_BLAST) in
    let fold_spec = INST [wtm,`w:32 word`] fold_thm in
    RULE_ASSUM_TAC(REWRITE_RULE[fold_spec]) (asl,gl);;

(* CTR_RAW_INCR_FOLD_TAC qd sn wtm: the increment counterpart of REV32_FOLD_TAC.
   After `add v30,v30,v31` @0x4a8/0x4bc/... + GCM_SIMD_SIMPLIFY_TAC, the assumption
   `read Qd sn = <single-add tower over gcm_ctr_raw wtm ctr0>` (top lane
   word_add (word_subword (gcm_ctr_raw wtm ctr0)(96,32))(word 1), others +0) folds
   to `read Qd sn = gcm_ctr_raw (word_add wtm (word 1)) ctr0` via GCM_CTR_RAW_INCR
   instantiated at w:=wtm.  Fold ONCE PER add (before the next add re-nests the
   +1s) so only the single-+1 GCM_CTR_RAW_INCR LHS is ever matched.
   VALIDATED (self-test proved; MATCH_ACCEPT on the exact simplified
   single-add shape). *)
let CTR_RAW_INCR_FOLD_TAC (qd:string) (sn:string) (wtm:term) : tactic =
  let incr_spec = INST [wtm,`w:32 word`] GCM_CTR_RAW_INCR in
  RULE_ASSUM_TAC(fun th ->
    match concl th with
    | Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),c),st)),_)
        when string_of_term c = qd && (try fst(dest_var st)=sn with _ -> false) ->
        REWRITE_RULE[incr_spec] th
    | _ -> th);;

(* ------------------------------------------------------------------------- *)
(* 10. Phase 4: fire the ENSURES_WHILE skeleton -> WBN_MAIN_LOOP_raw              *)
(*                                                                            *)
(* The back-edge of .L256_dec_main_loop is                                    *)
(*   cmp x0,x5 @0x9e4 ; stp q6,q7,[x2],#32 @0x9e8 ; b.lt 0x4a0 @0x9ec         *)
(* i.e. the SIGNED conditional branch b.lt is the LAST body instruction and   *)
(* its flag-setting cmp is two instructions earlier -- BOTH inside the body.  *)
(* That is the ENSURES_WHILE_UP2_TAC shape (branch folded into the body): the *)
(* body postcondition PC is word(if i+1<k then pc1 else pc2), the flag never  *)
(* crosses a frame boundary, and the exit lands at the fall-through pc2.       *)
(* Count k = (nblk-9) DIV 8; pc1 = pc+0x4a0 (head); pc2 = pc+0x9f0 (exit).     *)
(*                                                                            *)
(* PROBLEM: ENSURES_WHILE_UP2_TAC's internal `C ,, C = C` conjunct is         *)
(* discharged by MAYCHANGE_IDEMPOT_TAC, which THROWS ASSIGNS_SEQ_ABSORB_CONV  *)
(* on this 4-memory-region frame (the MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_  *)
(* ABI macro doesn't canonicalize into the ASSIGNS sequence ABSORB expects).  *)
(* FIX: expand the ABI macro FIRST, then MAYCHANGE_IDEMPOT_TAC succeeds (~2s). *)
(* up2_pth is a verbatim re-proof of ENSURES_WHILE_UP2_TAC's internal pth, and *)
(* UP2_ABI_TAC is the closure at common/relational.ml:2137 with the ABI       *)
(* expand spliced into the idempotence CONJ_TAC leg.                          *)
(* ------------------------------------------------------------------------- *)

(* the applied PC-free core, as a (num->armstate->bool) and as a \i s. abstr. *)
let wbn_core_applied =
  list_mk_comb(`wbn_loop_inv_core_raw`,
    [`pc:num`;`ctr0:int128`;`in_p:int64`;`out_p:int64`;`xi_p:int64`;`ivec_p:int64`;
     `key_p:int64`;`htbl_p:int64`;`stackpointer:int64`;`nblk:num`;`ibytes:byte list`;
     `xi:int128`;`h:int128`;`k0:int128`;`k1:int128`;`k2:int128`;`k3:int128`;`k4:int128`;
     `k5:int128`;`k6:int128`;`k7:int128`;`k8:int128`;`k9:int128`;`k10:int128`;`k11:int128`;
     `k12:int128`;`k13:int128`;`k14:int128`]);;

let wbn_core_iv = list_mk_abs([`i:num`;`s:armstate`],
  mk_comb(mk_comb(wbn_core_applied,`i:num`),`s:armstate`));;

(* ENSURES_WHILE_UP2_TAC's internal `pth` (common/relational.ml:1974), re-proved
   here so we can reach it with an ABI-aware idempotence discharge. *)
let up2_pth = prove(
  `forall k pc1 pc2 (loopinv:num->A->bool) C precond postcond
      (pcounter:(A,(N)word)component) step pc.
    C ,, C = C /\ ~(k = 0) /\
    ensures step
      (\s. program_decodes s /\ read pcounter s = word pc /\ precond s)
      (\s. program_decodes s /\ read pcounter s = word pc1 /\ loopinv 0 s)
      C /\
    (forall i. i < k /\ ~(i = k) /\ ~(k = 0) /\ 0 < k
      ==> ensures step
        (\s. program_decodes s /\ read pcounter s = word pc1 /\ loopinv i s)
        (\s. program_decodes s /\
             read pcounter s = word (if i + 1 < k then pc1 else pc2) /\
             loopinv (i + 1) s)
        C) /\
    ensures step
        (\s. program_decodes s /\ read pcounter s = word pc2 /\ loopinv k s)
        postcond C
    ==>
    ensures step
      (\s. program_decodes s /\ read pcounter s = word pc /\ precond s)
      postcond C`,
  REPEAT GEN_TAC THEN
  INTRO_TAC "HC HK HPRE HLOOP HPOST" THEN
  MATCH_MP_TAC ENSURES_TRANS_SIMPLE THEN
  USE_THEN "HC" (fun th -> REWRITE_TAC[th]) THEN
  META_EXISTS_TAC THEN CONJ_TAC THENL
  [ALL_TAC; USE_THEN "HPOST" (UNIFY_ACCEPT_TAC [`Q:A->bool`])] THEN
  REMOVE_THEN "HPOST" (K ALL_TAC) THEN
  MATCH_MP_TAC ENSURES_TRANS_SIMPLE THEN
  USE_THEN "HC" (fun th -> REWRITE_TAC[th]) THEN
  EXISTS_TAC `(\(s:A). program_decodes s /\
                       read pcounter s = (word pc1:(N)word) /\
                       loopinv (k - 1) s)` THEN
  CONJ_TAC THENL [
    ALL_TAC;
    USE_THEN "HLOOP" (fun th -> MP_TAC (SPEC `(k-1)` th)) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `k - 1 + 1 = k` SUBST_ALL_TAC THENL [ASM_ARITH_TAC; ALL_TAC]
    THEN REWRITE_TAC[LT_REFL]
  ] THEN
  SUBGOAL_THEN `k - 1 < k` MP_TAC THENL [ASM_ARITH_TAC;ALL_TAC] THEN
  SPEC_TAC (`k - 1`,`j:num`) THEN INDUCT_TAC THENL [
    ASM_REWRITE_TAC[] THEN NO_TAC;
    FIRST_X_ASSUM (fun th -> DISCH_TAC THEN MP_TAC th) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN (LABEL_TAC "HPREVLOOP") THEN
    MATCH_MP_TAC ENSURES_TRANS_SIMPLE THEN
    USE_THEN "HC" (fun th -> REWRITE_TAC[th]) THEN
    META_EXISTS_TAC THEN CONJ_TAC THENL
    [USE_THEN "HPREVLOOP" (UNIFY_ACCEPT_TAC [`Q:A->bool`]); ALL_TAC] THEN
    USE_THEN "HLOOP" (fun th -> MP_TAC (SPEC `j:num` th)) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[GSYM ADD1] THEN NO_TAC
  ]);;

(* ENSURES_WHILE_UP2_TAC caller with ABI-aware idempotence discharge. *)
let UP2_ABI_TAC k pc1 pc2 iv =
  MATCH_MP_TAC up2_pth THEN
  MAP_EVERY EXISTS_TAC [k; pc1; pc2; iv] THEN
  BETA_TAC THEN
  CONJ_TAC THENL
   [REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN MAYCHANGE_IDEMPOT_TAC;
    ALL_TAC];;

(* ---- body Q8..Q15 re-derivation ------------------------------------------- *)
(* The next raw-ct group (blocks 8(i+1)+0..8(i+1)+7) is loaded fresh in the body *)
(* (ldp q8,q9,[x0],#32 @0x810 etc, x0 = in_p+128(i+1)).  The finding             *)
(* is that the sim discards these read-facts — but they are RE-DERIVABLE at any  *)
(* body state from the surviving in_p loop-constant (read (memory :> bytes       *)
(* (in_p,16*nblk)) s = num_of_bytelist ibytes), which is preserved (in_p is      *)
(* read-only, out_p disjoint).  WBN_RAWCT_BOUND: the step-case bound i<(nblk-9)   *)
(* DIV 8 gives 8(i+1)+m < nblk for m<8.  WBN_RAWCT_READ: INPUT_BYTES_TO_BYTE128_ *)
(* LANES (from the <=8-block chain) specialized so each block reads at in_p+16*(8(i+1)+m) =     *)
(* bytes_to_int128(SUB_LIST(16*(8(i+1)+m),16) ibytes) — exactly the invariant's  *)
(* read Q8..Q15 (i+1) values.  Prefer this to preserving the reg facts through   *)
(* 300+ steps: re-derive rather than preserve.                                   *)
let WBN_RAWCT_BOUND = prove
 (`i < (nblk - 9) DIV 8 /\ 9 <= nblk ==> !m. m < 8 ==> 8 * (i+1) + m < nblk`,
  STRIP_TAC THEN X_GEN_TAC `m:num` THEN DISCH_TAC THEN
  MP_TAC(SPECL [`nblk - 9`; `8`] DIVISION) THEN ASM_ARITH_TAC);;

let WBN_RAWCT_READ = prove
 (`i < (nblk - 9) DIV 8 /\ 9 <= nblk /\
   LENGTH (ibytes:byte list) = 16 * nblk /\
   read (memory :> bytes (in_p:int64, 16 * nblk)) s = num_of_bytelist ibytes
   ==> !m. m < 8
       ==> read (memory :> bytes128 (word_add in_p (word (16 * (8*(i+1)+m))))) s =
           bytes_to_int128 (SUB_LIST (16 * (8*(i+1)+m), 16) ibytes)`,
  STRIP_TAC THEN
  MP_TAC(SPECL [`nblk:num`; `in_p:int64`; `ibytes:byte list`; `s:armstate`]
    INPUT_BYTES_TO_BYTE128_LANES) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[LE_REFL] THEN
    SUBGOAL_THEN `SUB_LIST (0, 16 * nblk) (ibytes:byte list) = ibytes` SUBST1_TAC THENL
     [MATCH_MP_TAC SUB_LIST_LENGTH_IMPLIES THEN ASM_REWRITE_TAC[LE_REFL]; ALL_TAC] THEN
    ASM_REWRITE_TAC[];
    DISCH_TAC THEN X_GEN_TAC `m:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    MP_TAC(SPEC_ALL WBN_RAWCT_BOUND) THEN ASM_SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* 10a. Phase 4 body-sim machinery.                                           *)
(*                                                                            *)
(* The loop body 0x4a0..0x9ec (340 instrs) is a software-pipelined 8-block     *)
(* group: 8 AES-256 keystreams (aese/aesmc towers), 8 GHASH Horner folds,      *)
(* the CTR-block counter advancing 8i+13 -> 8i+21 = 8(i+1)+13, 4 stp stores,   *)
(* next-group ldp loads, and the signed b.lt back-edge.  The sim is driven     *)
(* per-region (VALIDATED: s0..s340 all clean, terms kept flat):                *)
(*   - counter-input rev32 v_,v30 folds:  REV32_FOLD_TAC "Qd" "sN" `word(8i+c)`*)
(*   - counter-increment add v30 folds:   CTR_INCR_NORM_TAC "sN" c  (fold once *)
(*       per add, THEN normalize word_add(word(8i+c))(word 1) -> word(8i+c+1)) *)
(*   - AES/GHASH bulk 14..317:  ARM_STEPS_FOLD_Q18LATEST_TAC (keeps only the    *)
(*       latest Q18 GHASH partial) + DISCARD_STALE_Q19_TAC + GCM_SIMD_SIMPLIFY  *)
(*       (folds the rev64 ct byte-trees); pile stays ~5-6k chars.              *)
(*   - store window 318..340:  Q18LATEST stepper (store read-backs self-        *)
(*       propagate; do NOT blanket-VSTEPS - a 781-hyp pile makes the stepper    *)
(*       throw `mk_comb: types do not agree` on the stp).                       *)
(*   - back-edge b.lt @0x9ec:  resolve NF/VF via WB_PTRCMP_FLAGS (a=128*(i+2),  *)
(*       d=128*((nblk-1)DIV8)) as STANDALONE flag theorems rewritten into the   *)
(*       assumptions (NOT MP_TAC'd into the goal - that pollution breaks the    *)
(*       stp step).  PC lands at if 128*(i+2)<128*((nblk-1)DIV8) then 0x4a0     *)
(*       else 0x9f0, bridged to if i+1<(nblk-9)DIV8 ... by WBN_PC_BRIDGE.       *)
(* ------------------------------------------------------------------------- *)

(* fold add-v30 increment then normalize the counter to word(8*i+(c+1)) *)
let CTR_INCR_NORM_TAC (sn:string) (c:int) : tactic =
  let cur = mk_comb(`word:num->32 word`,
    mk_binop `(+):num->num->num` `8*i` (mk_small_numeral c)) in
  let nrm = WORD_RULE (mk_eq(
    mk_binop `word_add:32 word->32 word->32 word` cur `word 1:32 word`,
    mk_comb(`word:num->32 word`,
      mk_binop `(+):num->num->num` `8*i` (mk_small_numeral (c+1))))) in
  CTR_RAW_INCR_FOLD_TAC "Q30" sn cur THEN RULE_ASSUM_TAC(REWRITE_RULE[nrm]);;

(* discard all-but-latest read Q19 s_ facts (the GHASH accumulator grows a big
   partial tower each step; older states are dead).  Mirror of the <=8-block chain
   DISCARD_STALE_Q18_TAC. *)
let state_num_of_q19_fact th =
  try let c = concl th in if not(is_eq c) then None else
    (match lhs c with
       Comb(Comb(Const("read",_),Const("Q19",_)),Var(sn,_))
         when String.length sn>1 && sn.[0]='s' ->
           Some(int_of_string(String.sub sn 1 (String.length sn-1)))
     | _ -> None) with _ -> None;;
let DISCARD_STALE_Q19_TAC : tactic = fun (asl,w) ->
  let nums = List.filter_map (fun (_,th) -> state_num_of_q19_fact th) asl in
  match nums with [] | [_] -> ALL_TAC (asl,w)
  | _ -> let mx = List.fold_left max 0 nums in
         DISCARD_ASSUMPTIONS_TAC (fun th ->
           (match state_num_of_q19_fact th with Some k -> k<mx | None -> false)) (asl,w);;

(* ---- : body-close reduce-window infrastructure --------
   The final GHASH reduce (0x924..0x9b4) reloads Q16 = the [sp+64] modulus (now carried by
   the invariant) and feeds the pmull/eor3 chain via Q16/Q17/Q21/Q29.  Over that window we
   must KEEP Q16-Q19 (KEEPGH) yet not let their per-step towers pile up.  KEEPGH_LATEST =
   KEEPGH + keep only the LATEST read of each of Q16/Q17/Q18/Q19.  (KEEPGH lives in the <=8-block chain;
   this generalizes DISCARD_STALE_Q19_TAC to all four GHASH regs.)  VALIDATED
   to define+typecheck against the warm ckpt; the full-window behaviour is validated once
   the new invariant is cold-loaded (the body reaches this window only via wbn_loop_inv_core_raw,
   which the warm ckpt still bakes WITHOUT the [sp+64] conjunct). *)
let state_num_of_qreg qn th =
  try let c = concl th in if not(is_eq c) then None else
    (match lhs c with
       Comb(Comb(Const("read",_),Const(n,_)),Var(sn,_))
         when n=qn && String.length sn>1 && sn.[0]='s' ->
           Some(int_of_string(String.sub sn 1 (String.length sn-1)))
     | _ -> None) with _ -> None;;
let DISCARD_STALE_QREG_TAC qn : tactic = fun (asl,w) ->
  let nums = List.filter_map (fun (_,th) -> state_num_of_qreg qn th) asl in
  match nums with [] | [_] -> ALL_TAC (asl,w)
  | _ -> let mx = List.fold_left max 0 nums in
         DISCARD_ASSUMPTIONS_TAC (fun th ->
           (match state_num_of_qreg qn th with Some k -> k<mx | None -> false)) (asl,w);;
(* (the KEEPGH_LATEST stepper family -- DISCARD_OLDSTATE_KEEPGH_
   LATEST_TAC and ARM_STEPS_FOLD_KEEPGH_LATEST_TAC / _NOSIMP_TAC -- was an early
   body-sim variant superseded by the KEEPDATA family the live sims use; it was
   never referenced and has been deleted.) *)

(* WBN_NBLK_GE_9: moved here from below the back-edge cluster so
   RAWCT_LEMMA_AT (Sec 10b) can reference it — the cold-load regression the
   e2386b15 commit introduced (Unbound value at the RAWCT_LEMMA_AT let). Depends
   only on DIVISION + ARITH_TAC, so it is safe to hoist. *)
let WBN_NBLK_GE_9 = prove
 (`0 < (nblk - 9) DIV 8 ==> 9 <= nblk`,
  MP_TAC(SPECL [`nblk - 9`; `8`] DIVISION) THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* 10b. Phase-4 postcond-MATCH machinery.                                     *)
(*                                                                            *)
(*  finding: the 16 orthogonal postcond conjuncts (all but the                 *)
(* escalated Q19 [11]) close CHEAT-free once three sub-problems are solved.    *)
(* These tactics are VALIDATED live end-to-end (body sim reaches s340; the     *)
(* counter conjunct [0] closes standalone via CTR_ADD_CLOSE_TAC in 0.8s).      *)
(*                                                                            *)
(* (A) Q8..Q15 raw-ct [3-10]:                                                 *)
(*   right after each ldp (steps 221 src s220, 273 src s272, 306 src s305,     *)
(*   309 src s308), the machine gives read Qk sN = read(mem:>bytes128 ADDR)    *)
(*   s(N-1) — an OLD-STATE read that is un-closeable once s(N-1) is discarded.  *)
(*   FIX: RAWCT_LEMMA_AT "s(N-1)" registers the WBN_RAWCT_READ !m form at the   *)
(*   source state, then RESOLVE_QREG_A "Qk" "sN" m rewrites read Qk sN into     *)
(*   the SPEC form bytes_to_int128 (SUB_LIST (16*(8*(i+1)+m),16) ibytes).       *)
(*   The stepper then PROPAGATES this state-independent RHS forward at the      *)
(*   current state (validated: read Q8 s225 already clean spec form) — so it    *)
(*   survives every later discard.  m = 0..7 for Q8..Q15 in load order.         *)
(*                                                                            *)
(* (B) Reduce-window hang (the concrete-modulus blocker): since Q19 [11]        *)
(*   goes behind the scoped CHEAT, DISCARD Q16/Q17/Q18/Q19 BEFORE the reduce    *)
(*   window (before step 290).  The concrete [sp+64] modulus pmull that made    *)
(*   GCM_SIMD_SIMPLIFY stack-overflow is then gone — 290..305 steps in ~15s.    *)
(*   No midacc / Tier-2 machinery needed for the 16 conjuncts.                  *)
(*                                                                            *)
(* (C) Store window 310..340 + counter folds (PARTIAL):                        *)
(*   the AES keystream Q0..Q7 is consumed by eor3 (steps 313..335) to make the  *)
(*   plaintext; KEEPGH-style stepping discards it, so store read-backs dangle.  *)
(*   ARM_STEPS_DATA_NOSIMP_TAC keeps Q0..Q15 + ALL memory reads current (no      *)
(*   GCM_SIMD_SIMPLIFY — SIMPLIFY + kept Q0..Q15 explodes on the eor3 towers)    *)
(*   and DOES land the plaintext eor3 results current (Q5 s320 present).  BUT    *)
(*   the counter regs Q0..Q4 then arrive as RAW rev32/incr towers: the SMALL    *)
(*   one [0] closes via CTR_ADD_CLOSE_TAC standalone, but the compound ones      *)
(*   [1][2] (10k/51k chars, many un-folded nested adds) OOM WORD_BLAST.  SO the  *)
(*   counter regs MUST be REV32_FOLD/CTR_INCR_NORM-folded DURING the store       *)
(*   window (as the committed sim does: REV32_FOLD "Q25" s326, "Q4" s336,        *)
(*   CTR_INCR_NORM s335/s337).  A cleaner alternative would be a single store   *)
(*   window that keeps Q0..Q7 keystream + stores current AND folds Q0..Q4        *)
(*   counters per-step (hybrid of ARM_STEPS_DATA_NOSIMP_TAC + the fold points).  *)
(*                                                                            *)
(* (D) Verified trivial closers: [9][10] pointer advances = CONV_TAC WORD_RULE; *)
(*   [3-5] Q5-Q7 plaintext = GSYM AES256_XOR_ENCRYPT_RECONSTRUCT + GCM_CTR_INC* *)
(*   _LANES + WORD_RULE (tail closer, <=8-block chain); [store-forall] ASM_CASES         *)
(*   j<8*(i+1); [htable] REWRITE htable_mem_dec + let_CONV + ASM_REWRITE;        *)
(*   [MAYCHANGE] MONOTONE_MAYCHANGE_TAC.  [11] Q19 = scoped CHEAT (escalated).   *)
(* ------------------------------------------------------------------------- *)

(* RAWCT_LEMMA_AT sprev: register the WBN_RAWCT_READ !m raw-ct lemma at state
   sprev (needs 9<=nblk via WBN_NBLK_GE_9 + the in_p read-only loop-constant). *)
let RAWCT_LEMMA_AT sprev : tactic =
  SUBGOAL_THEN
    (subst[mk_var(sprev,`:armstate`),`s:armstate`]
      `!m. m < 8 ==> read (memory :> bytes128 (word_add in_p (word (16 * (8*(i+1)+m))))) s =
                     bytes_to_int128 (SUB_LIST (16 * (8*(i+1)+m), 16) ibytes)`)
    ASSUME_TAC THENL
   [MATCH_MP_TAC WBN_RAWCT_READ THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC WBN_NBLK_GE_9 THEN ASM_REWRITE_TAC[];
    ALL_TAC];;

(* RESOLVE_QREG_A qreg scur m: rewrite read qreg scur (currently = read(mem@ADDR)
   s_prev for some ADDR = in_p+16*(8*(i+1)+m)) into the spec form via the raw !m
   lemma already in the assumptions (from RAWCT_LEMMA_AT).  Robust to any ADDR
   syntactic form: proves ADDR = canonical by WORD_RULE then rewrites+accepts. *)
let RESOLVE_QREG_A (qreg:string) (scur:string) (m:int) : tactic =
  fun (asl,w) ->
    let mnum = mk_small_numeral m in
    let th,addr = tryfind (fun (_,th) -> match concl th with
        Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),Const(n,_)),Var(sn,_))),
             Comb(Comb(Const("read",_),Comb(Comb(Const(":>",_),Const("memory",_)),
               Comb(Const("bytes128",_),addr))),_))
          when n=qreg && sn=scur -> (th,addr)
      | _ -> fail()) asl in
    let raw = tryfind (fun (_,t) -> match concl t with
        Comb(Const("!",_),Abs(Var("m",_),Comb(Comb(Const("==>",_),_),
          Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),_),_)),
               Comb(Const("bytes_to_int128",_),_))))) -> t
      | _ -> fail()) asl in
    let canon = vsubst[mnum,`m:num`] `word_add in_p (word (16 * (8*(i+1)+m))):int64` in
    let addr_eq = WORD_RULE (mk_eq(addr,canon)) in
    let raw_inst = MATCH_MP raw (ARITH_RULE(mk_comb(mk_comb(`(<):num->num->bool`,mnum),`8`))) in
    let target = mk_eq((parse_term (Printf.sprintf "read %s %s :int128" qreg scur)),
      vsubst[mnum,`m:num`] `bytes_to_int128 (SUB_LIST (16 * (8*(i+1)+m), 16) ibytes)`) in
    (SUBGOAL_THEN target ASSUME_TAC THENL
      [GEN_REWRITE_TAC LAND_CONV [th] THEN REWRITE_TAC[addr_eq] THEN ACCEPT_TAC raw_inst;
       ALL_TAC]) (asl,w);;

(* DISCARD_KEEP_DATA_TAC / ARM_STEPS_DATA{,_NOSIMP}_TAC: store-window steppers that
   keep Q0..Q15 (data regs, incl. AES keystream) + ALL memory reads at the current
   state, discarding only stale/scratch old-state reads.  NOSIMP variant avoids the
   AES-tower explosion that GCM_SIMD_SIMPLIFY triggers when Q0..Q15 are kept. *)
let DISCARD_KEEP_DATA_TAC s =
  let v = mk_var(s,`:armstate`) in
  let rec unbound_statevars_of_read bound tm = match tm with
      Comb(Comb(Const("read",_),_),st) -> if mem st bound then [] else [st]
    | Comb(a,b) -> union (unbound_statevars_of_read bound a) (unbound_statevars_of_read bound b)
    | Abs(vv,t) -> unbound_statevars_of_read (vv::bound) t | _ -> [] in
  let rec is_mem_read t = match t with
      Comb(Comb(Const("read",_),Comb(Comb(Const(":>",_),Const("memory",_)),_)),_) -> true
    | Comb(a,b) -> is_mem_read a || is_mem_read b | Abs(_,t2) -> is_mem_read t2 | _ -> false in
  DISCARD_ASSUMPTIONS_TAC(fun thm ->
    if is_mem_read (concl thm) then false else
    let us = unbound_statevars_of_read [] (concl thm) in
    if us = [] || us = [v] then false else true);;
let ARM_STEPS_DATA_NOSIMP_TAC exec snums =
  MAP_EVERY (fun s -> ARM_VERBOSE_STEP_TAC exec s THEN
              DISCARD_KEEP_DATA_TAC s THEN CLARIFY_TAC) (statenames "s" snums);;

(* CTR_ADD_CLOSE_TAC: close a counter postcond conjunct whose LHS is the raw
   rev32-of-gcm_ctr_raw tower and RHS is gcm_ctr_add (word W) ctr0.  Same recipe
   as REV32_FOLD_TAC's fold proof.  VALIDATED on conjunct [0] (0.8s).  WARNING:
   only works when the LHS tower is SINGLE-rev32 (folded during stepping); a
   compound raw tower with many un-folded nested +1 adds OOMs WORD_BLAST — fold
   the counter DURING the store window instead. *)
let CTR_ADD_CLOSE_TAC : tactic =
  REWRITE_TAC[gcm_ctr_raw_def] THEN
  GEN_REWRITE_TAC RAND_CONV [GCM_CTR_ADD_LANES] THEN
  W(fun (_,gw) ->
    let atom = find_term (fun t -> match t with
      | Comb(Comb(Const("word_add",_),_),Comb(Const("word",_),Comb(Comb(Const("+",_),_),_))) -> true
      | _ -> false) gw in
    SPEC_TAC(atom, `aa:32 word`)) THEN
  GEN_TAC THEN CONV_TAC WORD_BLAST;;

(* ------------------------------------------------------------------------- *)
(* 10c. Phase-4 body-close machinery.                                         *)
(*                                                                            *)
(* the full body sim + 16-conjunct close, driven CHEAT-free                   *)
(* (only [11]/Q19 keeps its scoped CHEAT).  The committed sim (below) uses a   *)
(* KEEPDATA stepper that keeps Q0..Q19 latest (incl. the AES keystream Q0-Q7,  *)
(* which the old Q18LATEST/KEEPGH_LATEST steppers discarded — the             *)
(* keystream-survival blocker).  Resolve-at-load for Q8-Q15 is done with       *)
(* RESOLVE_LDP2_TAC, which fixes a RESOLVE_QREG_A latent bug: the ldp           *)
(* leaves  read Qk s(N) = read(mem@ADDR) s(N-1)  (memory read at the LOAD-INPUT *)
(* state s(N-1)), so the raw !m lemma must be matched AT s(N-1), not s(N).      *)
(* RESOLVE_QREG_C matches the raw lemma at the register-read's own memory-state *)
(* and uses PURE_ONCE_REWRITE (plain REWRITE collapses 8*(i+1)+0 -> 8*(i+1),    *)
(* breaking the m=0 ACCEPT).                                                    *)
(* ------------------------------------------------------------------------- *)

(* KEEPDATA steppers: keep the LATEST read of Q0..Q19 (data regs incl keystream)
   + all memory + loop constants; discard everything else old-state. *)
let wbn_datawords_0_19 =
  ["Q0";"Q1";"Q2";"Q3";"Q4";"Q5";"Q6";"Q7";"Q8";"Q9";
   "Q10";"Q11";"Q12";"Q13";"Q14";"Q15";"Q16";"Q17";"Q18";"Q19"];;
let DISCARD_OLDSTATE_KEEPDATA_TAC s =
  let v = mk_var(s,`:armstate`) in
  let rec unbound_statevars_of_read bound tm = match tm with
      Comb(Comb(Const("read",_),_),st) -> if mem st bound then [] else [st]
    | Comb(a,b) -> union (unbound_statevars_of_read bound a) (unbound_statevars_of_read bound b)
    | Abs(vv,t) -> unbound_statevars_of_read (vv::bound) t | _ -> [] in
  let rec mentions_data t = match t with
      Comb(Comb(Const("read",_),cmp),_) ->
        (match cmp with Const(n,_) -> List.mem n wbn_datawords_0_19 | _ -> false)
    | Comb(a,b) -> mentions_data a || mentions_data b | Abs(_,t2) -> mentions_data t2 | _ -> false in
  DISCARD_ASSUMPTIONS_TAC(fun thm ->
    if mentions_data (concl thm) then false else
    let us = unbound_statevars_of_read [] (concl thm) in
    if us = [] || us = [v] then false else true);;
let DISCARD_STALE_DATA_TAC = MAP_EVERY DISCARD_STALE_QREG_TAC wbn_datawords_0_19;;
(* SPEED: the per-step fold here uses ONE pass of
   GCM_SIMD_SIMPLIFY_CORE_TAC, not the shared double-pass GCM_SIMD_SIMPLIFY_TAC.  The
   2nd pass exists (in the lemmas file) to reach a REV64 fixpoint that a single pass
   can miss on ~6/278 steps -- but under KEEPDATA (which discards stale old-state reads
   after every step) the body sim reaches its self-contained cut-points WITHOUT that
   extra fold: WBN_MAIN_LOOP_raw and WBN_PREPRETAIL_EXT2 (the ONLY two KEEPDATA-SIMP users)
   both re-prove hyps=0 with a single core pass.  Measured on a warm dev-load:
   WBN_MAIN_LOOP_raw 188.2s->147.0s, WBN_PREPRETAIL 136.9s->103.5s (the 2nd pass was a
   full pile-traversal no-op on 272/278 steps).  KEEPGH (tails/fronts) and every other
   consumer keep the unchanged double-pass GCM_SIMD_SIMPLIFY_TAC. *)
(* refine-101: Q-scope + fixpoint-MEMOIZE the SIMP KEEPDATA normalizer (the last
   heavy KEEP-accumulator stepper never given the s097/s099/s100 treatment).  Even
   though KEEPDATA discards stale old-state reads each step (pile ~186, small vs the
   fused 400-1000), an instrumented profile of WBN_MAIN_LOOP_raw showed the normalizer
   leaves the WHOLE pile unchanged on 234/274 steps (85%) and costs ~30s of the 150s:
   the single GCM_SIMD_SIMPLIFY_CORE_TAC pass RE-walks every `read Qn s = <tower>`
   assumption every step though its rules (REV64 lanes / WORD_SWAP_HALVES / EXT8_LANE0
   / REV32_LANE_SUBWORD) can ONLY fire on a Q-read, and re-folds Q-reads already at a
   fixpoint.  FIX (mirror gcm_simd_fixpt_tbl s099 / gcm_simd_kgh_tbl s100): own table
   gcm_simd_kd_tbl; guard the O(1) `read Qn` head before the rewrites (Q-scope), skip a
   Q-read whose concl is a known F-fixpoint (memoize).  apply_F = the SAME 3 passes as
   GCM_SIMD_SIMPLIFY_CORE_TAC, so BIT-IDENTICAL by construction; MEASURED 0 mismatches
   over all 274 SIMP steps by-position vs the full _CORE_TAC.  Cache reset per body via
   CLEAR_KEEPDATA_MEMO_TAC (added after each ENSURES_INIT in the 2 consumers) so each
   `prove` is hermetic.  Warm A/B twice, both post-Gc.compact: WBN_MAIN_LOOP_raw
   150.5s->121.8s and 149.4s->121.6s (-18.6..-19.1% TWICE), hyps=0. *)
let gcm_simd_kd_tbl : (term,unit) Hashtbl.t = Hashtbl.create 8192;;
let CLEAR_KEEPDATA_MEMO_TAC : tactic =
  fun (asl,w) -> Hashtbl.clear gcm_simd_kd_tbl; ALL_TAC (asl,w);;
let GCM_SIMD_SIMPLIFY_KD_TAC =
  let is_qreg_read c = match c with
    | Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),cmp),_)),_) ->
        (match cmp with Const(rn,_) ->
           String.length rn >= 2 && rn.[0]='Q' && rn.[1]>='0' && rn.[1]<='9'
         | _ -> false)
    | _ -> false in
  let apply_F th =
    let th1 = (try REWRITE_RULE SIMD_SIMPLIFY_RULES th with _ -> th) in
    let th2 = REWRITE_RULE [WORD_SWAP_HALVES_INVOLUTION; EXT8_LANE0_IS_SUBWORD_HI] th1 in
    (try CONV_RULE(RAND_CONV(REV32_LANE_SUBWORD_CONV)) th2 with _ -> th2) in
  RULE_ASSUM_TAC(fun th ->
    let c = concl th in
    if not(is_qreg_read c) then th
    else if Hashtbl.mem gcm_simd_kd_tbl c then th
    else let th' = apply_F th in
         (if concl th' = c then Hashtbl.add gcm_simd_kd_tbl c ());
         th');;
let ARM_STEPS_FOLD_KEEPDATA_TAC exec snums =
  MAP_EVERY (fun s -> ARM_VERBOSE_STEP_TAC exec s THEN GCM_SIMD_SIMPLIFY_KD_TAC THEN
              DISCARD_STALE_DATA_TAC THEN DISCARD_OLDSTATE_KEEPDATA_TAC s THEN CLARIFY_TAC)
    (statenames "s" snums);;
(* NO-SIMPLIFY variant for the reduce + store windows: GCM_SIMD_SIMPLIFY on the
   concrete [sp+64] modulus pmull (reduce) or the kept eor3 keystream towers
   (store) explodes; step symbolic instead. *)
let ARM_STEPS_FOLD_KEEPDATA_NOSIMP_TAC exec snums =
  MAP_EVERY (fun s -> ARM_VERBOSE_STEP_TAC exec s THEN
              DISCARD_STALE_DATA_TAC THEN DISCARD_OLDSTATE_KEEPDATA_TAC s THEN CLARIFY_TAC)
    (statenames "s" snums);;
(* outright drop reads of the listed regs at ANY state (Q19 is CHEATed, so the
   whole GHASH cluster Q16..Q19 goes before the reduce window; dead scratch
   Q29/Q21 dropped before the store-forall close to shrink the pile). *)
let DISCARD_QREGS_TAC qns : tactic =
  DISCARD_ASSUMPTIONS_TAC(fun th -> match concl th with
      Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),Const(n,_)),Var(_,_))),_) -> List.mem n qns
    | _ -> false);;

(* RESOLVE_QREG_C qreg scur m: like RESOLVE_QREG_A but matches the raw !m lemma AT
   the state of the register-read's embedded memory read (sload = s(N-1) for an
   ldp), not any state; and PURE_ONCE_REWRITE (not REWRITE) so the m=0 index
   8*(i+1)+0 is not collapsed to 8*(i+1) before ACCEPT.  (the
   RESOLVE_QREG_A fails on a recorded/cold run because the ldp memory read stays
   at s(N-1) while the raw lemma advances to s(N).) *)
let RESOLVE_QREG_C (qreg:string) (scur:string) (m:int) : tactic =
  fun (asl,w) ->
    let mnum = mk_small_numeral m in
    let th,addr,sload = tryfind (fun (_,th) -> match concl th with
        Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),Const(n,_)),Var(sn,_))),
             Comb(Comb(Const("read",_),Comb(Comb(Const(":>",_),Const("memory",_)),
               Comb(Const("bytes128",_),addr))),Var(sl,_)))
          when n=qreg && sn=scur -> (th,addr,sl)
      | _ -> fail()) asl in
    let raw = tryfind (fun (_,t) -> match concl t with
        Comb(Const("!",_),Abs(Var("m",_),Comb(Comb(Const("==>",_),_),
          Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),_),Var(sl,_))),
               Comb(Const("bytes_to_int128",_),_))))) when sl=sload -> t
      | _ -> fail()) asl in
    let canon = vsubst[mnum,`m:num`] `word_add in_p (word (16 * (8*(i+1)+m))):int64` in
    let addr_eq = WORD_RULE (mk_eq(addr,canon)) in
    let raw_inst = MATCH_MP raw (ARITH_RULE(mk_comb(mk_comb(`(<):num->num->bool`,mnum),`8`))) in
    let target = mk_eq((parse_term (Printf.sprintf "read %s %s :int128" qreg scur)),
      vsubst[mnum,`m:num`] `bytes_to_int128 (SUB_LIST (16 * (8*(i+1)+m), 16) ibytes)`) in
    (SUBGOAL_THEN target ASSUME_TAC THENL
      [GEN_REWRITE_TAC LAND_CONV [th] THEN PURE_ONCE_REWRITE_TAC[addr_eq] THEN ACCEPT_TAC raw_inst;
       ALL_TAC]) (asl,w);;

(* RESOLVE_LDP2_TAC exec qa qb ma mb sload scur: resolve a pair of raw-ct regs
   loaded by one ldp.  At frontier sload register raw@sload, do a BARE verbose
   step to scur (no discard/clarify so raw@sload survives), resolve qa/qb, then
   drop the stale raw-form reads + old-state + clarify. *)
let RESOLVE_LDP2_TAC exec qa qb ma mb sload scur : tactic =
  RAWCT_LEMMA_AT sload THEN
  ARM_VERBOSE_STEP_TAC exec scur THEN
  RESOLVE_QREG_C qa scur ma THEN
  RESOLVE_QREG_C qb scur mb THEN
  DISCARD_ASSUMPTIONS_TAC(fun th -> match concl th with
     Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),Const(n,_)),_)),
          Comb(Comb(Const("read",_),Comb(Comb(Const(":>",_),Const("memory",_)),_)),_))
       -> n=qa || n=qb
   | _ -> false) THEN
  DISCARD_STALE_DATA_TAC THEN DISCARD_OLDSTATE_KEEPDATA_TAC scur THEN CLARIFY_TAC;;

(* NEWBLK_CLOSE_TAC: close one new-block leg of the store-forall (j = 8*(i+1)+m,
   0<=m<8).  Canonicalize block indices 8*(i+1)+m -> 8*i+(8+m), normalize both
   store-readback address forms (out_p+(128*(i+1)+16m) and (out_p+128*(i+1))+16m)
   to the flat goal form, fire the readback, then fold the plaintext
   (GSYM aes13 + GCM_CTR_INC_ITER_ADD) and bridge the SUB_LIST index. *)
let NEWBLK_CLOSE_TAC =
  let canon = [ARITH_RULE `16 * 8 * (i+1) = 128*(i+1)`;
    ARITH_RULE `8*(i+1)+0 = 8*i+8`; ARITH_RULE `8*(i+1)+1 = 8*i+9`;
    ARITH_RULE `8*(i+1)+2 = 8*i+10`; ARITH_RULE `8*(i+1)+3 = 8*i+11`;
    ARITH_RULE `8*(i+1)+4 = 8*i+12`; ARITH_RULE `8*(i+1)+5 = 8*i+13`;
    ARITH_RULE `8*(i+1)+6 = 8*i+14`; ARITH_RULE `8*(i+1)+7 = 8*i+15`;
    ARITH_RULE `8*(i+1) = 8*i+8`] in
  let subbr = [ARITH_RULE `128 * (i + 1) = 16 * (8 * i + 8)`;
    ARITH_RULE `128 * (i + 1) + 16 = 16 * (8 * i + 9)`;
    ARITH_RULE `128 * (i + 1) + 32 = 16 * (8 * i + 10)`;
    ARITH_RULE `128 * (i + 1) + 48 = 16 * (8 * i + 11)`;
    ARITH_RULE `128 * (i + 1) + 64 = 16 * (8 * i + 12)`;
    ARITH_RULE `128 * (i + 1) + 80 = 16 * (8 * i + 13)`;
    ARITH_RULE `128 * (i + 1) + 96 = 16 * (8 * i + 14)`;
    ARITH_RULE `128 * (i + 1) + 112 = 16 * (8 * i + 15)`] in
  let addrbr = map (fun m -> WORD_RULE(subst[mk_small_numeral(16*m),`OFF:num`; mk_small_numeral m,`M:num`]
      `word_add (word_add out_p (word (128*(i+1)))) (word OFF):int64 =
       word_add out_p (word (16*(8*(i+1)+M))):int64`)) (0--7) in
  RULE_ASSUM_TAC(REWRITE_RULE addrbr) THEN
  REWRITE_TAC canon THEN RULE_ASSUM_TAC(REWRITE_RULE (canon @ subbr)) THEN
  (*  FIX: fire the store-readback hyp (ASM_REWRITE) BEFORE folding
     the raw aese/aesmc tower.  The s027 order ran GSYM aes13 first, when the
     goal LHS was still `read(mem) s340` (tower not yet substituted), so the
     fold had nothing to match and REFL_TAC failed on the 8 new-block legs. *)
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM aes13] THEN REWRITE_TAC[GCM_CTR_INC_ITER_ADD] THEN
  REWRITE_TAC (canon @ subbr) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM aes13] THEN REWRITE_TAC[GCM_CTR_INC_ITER_ADD] THEN
  REWRITE_TAC (canon @ subbr) THEN REFL_TAC;;
(* fold the machine keystream tower to aes13 + bridge gcm_ctr_add/inc_iter, for
   the plaintext register conjuncts [0-2] (Q5,Q6,Q7). *)
let PLAINTEXT_CLOSE_TAC =
  REWRITE_TAC[GSYM aes13] THEN REWRITE_TAC[GCM_CTR_INC_ITER_ADD] THEN
  REWRITE_TAC[ARITH_RULE `(8*i+8)+5 = 8*i+13`; ARITH_RULE `(8*i+8)+6 = 8*i+14`;
              ARITH_RULE `(8*i+8)+7 = 8*i+15`] THEN
  REFL_TAC;;

(* (BSWAP_INVOL_MASSAGE_TAC, an h_k=byteswap128(...) involution
   bridge for an earlier BODY_Q19_CLOSE_ALGEBRA route, was never referenced --
   deleted.) *)

(* PC back-edge arithmetic bridge.               *)
let WBN_DIV_SHIFT = prove
 (`9 <= nblk ==> (nblk - 1) DIV 8 = (nblk - 9) DIV 8 + 1`,
  STRIP_TAC THEN
  SUBGOAL_THEN `nblk - 1 = (nblk - 9) + 1 * 8` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[DIV_ADD_MOD] THEN
  SIMP_TAC[DIV_MULT_ADD; ARITH_EQ] THEN ARITH_TAC);;

let WBN_PC_BRIDGE = prove
 (`9 <= nblk
   ==> ((128 * (i + 2) < 128 * (nblk - 1) DIV 8) <=> (i + 1 < (nblk - 9) DIV 8))`,
  DISCH_TAC THEN ASM_SIMP_TAC[WBN_DIV_SHIFT] THEN ARITH_TAC);;

(* WBN_NBLK_GE_9 moved above Sec 10b (load-order fix).             *)

(* premises of WB_PTRCMP_FLAGS at the back-edge: X0=in_p+128*(i+2) (a),
   X5=128*((nblk-1)DIV8)+in_p (d); both offsets < 2^63 from val in_p+16*nblk. *)
let WBN_PTRCMP_PREMS = prove
 (`val (in_p:int64) + 16 * nblk < 2 EXP 63 /\ i < (nblk - 9) DIV 8
   ==> val (in_p:int64) + 128 * (i + 2) < 2 EXP 63 /\
       val (in_p:int64) + 128 * (nblk - 1) DIV 8 < 2 EXP 63`,
  STRIP_TAC THEN
  MP_TAC(SPECL [`nblk - 1`; `8`] DIVISION) THEN
  MP_TAC(SPECL [`nblk - 9`; `8`] DIVISION) THEN ASM_ARITH_TAC);;

(* word distributes over the back-edge if *)
let WBN_PC_IF = prove
 (`(if b then word (pc + 1216) else word (pc + 2576)):int64 =
   word (if b then pc + 1216 else pc + 2576)`,
  COND_CASES_TAC THEN REWRITE_TAC[]);;

(* the LOOP theorem: PC=0x4a0 /\ core 0  ==>  PC=0x9f0 /\ core k, over the front
   MAYCHANGE frame.  Entry/exit are trivial reflexive ensures (pre=post at the
   respective PC); count<>0 is DIVISION arithmetic (17<=nblk => (nblk-9)DIV8>=1).
   Body = the Phase-4 step case, CHEAT_TAC for now (see the big TODO below). *)
let wbn_main_loop_goal =
  let kk = `(nblk - 9) DIV 8` in
  let loop_pre = mk_abs(`s:armstate`,
    list_mk_conj[
      `aligned_bytes_loaded s (word pc) aesv8_gcm_8x_dec_256_wb_mc`;
      `read PC s = word (pc + 0x4c0)`;
      mk_comb(mk_comb(wbn_core_applied,`0`),`s:armstate`)]) in
  let loop_post = mk_abs(`s:armstate`,
    list_mk_conj[
      `aligned_bytes_loaded s (word pc) aesv8_gcm_8x_dec_256_wb_mc`;
      `read PC s = word (pc + 0xa10)`;
      mk_comb(mk_comb(wbn_core_applied,kk),`s:armstate`)]) in
  let ens = list_mk_comb(`ensures arm`,[loop_pre; loop_post; wbn_front_C_tm]) in
  list_mk_forall(wb_front_vars, mk_imp(wbn_front_hyps_wide_tm, ens));;

let WBN_MAIN_LOOP_raw = prove(wbn_main_loop_goal,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UP2_ABI_TAC `(nblk - 9) DIV 8` `pc + 0x4c0` `pc + 0xa10` wbn_core_iv THEN
  REPEAT CONJ_TAC THENL
   [ (* 1. count <> 0 : 17<=nblk => (nblk-1) DIV 8 >= 2 > 0 *)
    SUBGOAL_THEN `1 <= nblk - 1` MP_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPECL [`nblk - 1`; `8`] DIVISION) THEN ASM_ARITH_TAC;
    (* 2. entry: PC=0x4a0 /\ core 0 -> same (0-step reflexive ensures) *)
    ENSURES_INIT_TAC "s0" THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    REPEAT CONJ_TAC THEN MONOTONE_MAYCHANGE_TAC;
    (* 3. ===================== PHASE 4 LOOP BODY (TODO) ===================== *)
    (* Goal after `REPEAT STRIP_TAC THEN REWRITE_TAC[wbn_loop_inv_core_raw] THEN   *)
    (* CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN ENSURES_INIT_TAC "s0"`:         *)
    (* state s0 at 0x4a0, iteration i, with (confirmed , risk #2):            *)
    (*   X0=in_p+128(i+1) X2=out_p+128(i+1) X4=in_p+16nblk                     *)
    (*   X5=128*((nblk-1)DIV8)+in_p X1=128nblk X9=16nblk X10=sp+64 X11=key_p   *)
    (*   X3=xi_p X6=htbl_p X16=ivec_p X15=word 4294967296 SP=stackpointer      *)
    (*   Q0..Q4 = gcm_ctr_add(8i+8..8i+12) ctr0   (store/counter stream ahead) *)
    (*   Q5,Q6,Q7 = plaintext(8i+5,8i+6,8i+7)     (+8i keystream, CONFIRMED)   *)
    (*   Q8..Q15 = raw ct blocks 8i+0..8i+7        (GHASH stream lags)         *)
    (*   Q19 = ghash_polyval_acc over blocks 0..8i-1                           *)
    (*   Q26=k12 Q27=k13 Q28=k14 Q31=word 79228162514264337593543950336        *)
    (*   Q30 = gcm_ctr_raw (word (8i+13)) ctr0  (patch; read by                 *)
    (*         the body's first instr rev32 v5,v30; advances 8i+13 -> 8i+21).   *)
    (* Sim decodes cleanly.  340 instrs, body 0x4a0..0x9ec.  Target: core(i+1)  *)
    (* at PC=if i+1<k then 0x4a0 else 0x9f0.                                    *)
    (*                                                                          *)
    (*  body-entry recon (VALIDATED interactively against the                   *)
    (* Q30-patched wbn_loop_inv_core_v2, s0..s10 stepped clean, 2.6s+3.5s):     *)
    (*  loop-head counter schedule (objdump 0x4a0..0x4d0), interleaved:         *)
    (*    0x4a0 rev32 v5,v30   : Q5  <- rev32(gcm_ctr_raw(8i+13)) = keystream   *)
    (*                            ctr @ 8i+13  [= block 8(i+1)+5 of the invt]   *)
    (*    0x4a8 add   v30,v31  : Q30 8i+13 -> 8i+14                             *)
    (*    0x4b8 rev32 v6,v30   : Q6  <- gcm_ctr_add(8i+14) [= 8(i+1)+6]          *)
    (*    0x4bc add   v30,v31  : Q30 8i+14 -> 8i+15                             *)
    (*    0x4d0 rev32 v7,v30   : Q7  <- gcm_ctr_add(8i+15) [= 8(i+1)+7]          *)
    (*  (further add v30 steps advance to 8i+21 = 8(i+1)+13 for the next head.) *)
    (*  Q8..Q15 get rev64'd (0x4ac,0x4c0,0x4c8,0x4cc,0x4d4,...) into byteswap   *)
    (*  towers -> the GHASH input stream (byteswap128 of the raw ct blocks).    *)
    (*                                                                          *)
    (*  TWO per-instruction folds are the crux (both keep terms flat):          *)
    (*  (a) COUNTER-INPUT rev32 v_,v30:  REV32_FOLD_TAC "Q<d>" "s<n>"           *)
    (*        `word (8*i+13+j):32 word`  (j=0,1,2,... per rev32).  VALIDATED:    *)
    (*        Q5@s5 folded 10466ch -> `gcm_ctr_add (word (8*i+13)) ctr0` in 1.9s.*)
    (*  (b) COUNTER INCREMENT add v30,v30,v31:  after GCM_SIMD_SIMPLIFY_TAC the  *)
    (*        stepper emits, on the TOP lane,                                   *)
    (*          word_add (word_add (word_subword (gcm_ctr_raw w ctr0)(96,32))    *)
    (*                             (word 1)) (word 1) ...   (N nested +1 for N   *)
    (*        adds since the last fold), NOT GCM_CTR_RAW_INCR's single-+1 LHS.   *)
    (*        => need a small INCR-fold tactic (REV32_FOLD_TAC-style): normalize *)
    (*        the k nested (word 1) to (word k), then apply GCM_CTR_RAW_INCR     *)
    (*        (generalized to +k, or iterated) to land Q30=gcm_ctr_raw(w+k).     *)
    (*        Simplest: fold Q30 back to gcm_ctr_raw ONCE PER add (before the    *)
    (*        next add re-nests), so only the single-+1 GCM_CTR_RAW_INCR fires.  *)
    (*                                                                          *)
    (* GHASH close via GHASH_ACC_8BLOCK_EXTEND (blk := \k. bytes_to_int128     *)
    (* (SUB_LIST(16*k,16) ibytes)).  Counter compose: GCM_CTR_ADD_COMPOSE /    *)
    (* GCM_CTR_INC_ITER_ADD.  Signed back-edge b.lt @0x9ec resolved inside the *)
    (* body by WB_PTRCMP_FLAGS (x0 vs x5).  Reach the body-init state via       *)
    (*   REPEAT STRIP_TAC THEN REWRITE_TAC[wbn_loop_inv_core_raw] THEN              *)
    (*   CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN ENSURES_INIT_TAC "s0"          *)
    (* (VALIDATED: yields hyps incl. read Q30 s0 = gcm_ctr_raw                  *)
    (* (word(8*i+13)) ctr0 at asm 58).  Use per-step GCM_SIMD_SIMPLIFY_TAC to   *)
    (* control term growth (see WBN_FRONT_STEP_TAC pattern, Sec 3).             *)
    (* full 340-instr sim below is VALIDATED end-to-end (s0..s340                *)
    (* clean, PC lands at if i+1<(nblk-9)DIV8 then 0x4a0 else 0x9f0 exactly).    *)
    (* Only the postcondition MATCH (27 conjuncts: 8 AES-reconstruct, GHASH Q19  *)
    (* close, store-forall) remains -> inner CHEAT_TAC (Phase-4 sub-split).      *)
    (* ===================================================================== *)
    (* the 340-instr body re-sim, VALIDATED end-to-end with the                *)
    (* [sp+64]-carrying invariant.  Replaces the broken                        *)
    (* Q18LATEST body (which discarded every read Qn sK, n<>18,                *)
    (* dropping the postcond facts — the root cause).  Recipe:                 *)
    (*  - htable unfold+split @s0 (s013): the H-power ldrs resolve, so Q17/18/  *)
    (*    19 stay self-contained.                                              *)
    (*  - front 1-13 (counter rev32/add folds) verbatim.                       *)
    (*  - Q18LATEST 14-212 (GHASH partial stays flat via keep-latest-Q18).     *)
    (*  - KEEPGH_LATEST 213-289 (keeps Q16-Q19; Q16 auto-resolves to the       *)
    (*    [sp+64] modulus word 13979173243358019584 the invariant now pins).   *)
    (*  - NO-SIMPLIFY KEEPGH_LATEST 290-326 (GCM_SIMD_SIMPLIFY on the CONCRETE  *)
    (*    Q16 pmull stack-overflows — s014); ABBREV midacc = read Q18 s301     *)
    (*    (last eor3 v18) so the reduce steps stay small.  RESULT: read Q19    *)
    (*    s326 is FULLY SELF-CONTAINED (len ~3786, no dangling reads) — the     *)
    (*    first time the body's GHASH acc closes (s014 breakthrough).          *)
    (*  - Then discard the DEAD reduce intermediates (Q16/Q17/Q29 + the giant  *)
    (*    midacc SYM tree) and fold Q25 to gcm_ctr_add(8i+19): this removes     *)
    (*    the concrete-modulus pmull that makes the store-window simplify hang. *)
    (*  - RESUME simplify (KEEPGH_LATEST) 327-337 with the Q30/Q4 counter folds *)
    (*    (fold Q30 at s335 for the skipped no-simplify add@317).              *)
    (*  - back-edge 338-340: WB_PTRCMP_FLAGS standalone-rewrite + WBN_PC_BRIDGE.*)
    (*    PC lands EXACTLY at if i+1<(nblk-9)DIV8 then pc+1184 else pc+2544.    *)
    (* ===================================================================== *)
    REPEAT STRIP_TAC THEN REWRITE_TAC[wbn_loop_inv_core_raw] THEN
    CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN ENSURES_INIT_TAC "s0" THEN
    CLEAR_KEEPDATA_MEMO_TAC THEN  (* refine-101: reset the KEEPDATA normalizer fixpoint cache *)
    RULE_ASSUM_TAC(REWRITE_RULE[WB_MC_LEN]) THEN
    (* htable unfold+split @s0 (s013): resolve the 13 H-power memory cells *)
    RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_dec]) THEN
    RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV let_CONV)) THEN
    FIRST_X_ASSUM(fun th ->
      let c = concl th in
      if can (find_term (fun t->match t with Const("byteswap128",_)->true|_->false)) c &&
         can (find_term (fun t->match t with Const("karatsuba_mid",_)->true|_->false)) c
      then STRIP_ASSUME_TAC th else NO_TAC) THEN
    (* ===================================================================== *)
    (* full body sim (KEEPDATA — keeps Q0..Q19 incl keystream) +                *)
    (* 16-conjunct close, CHEAT-free.  Only [11]/Q19 keeps its scoped CHEAT     *)
    (* (route DECIDED: tail FOLD_MID_HPOW port, separate follow-up).  Driven    *)
    (* end-to-end (s0..s340, PC exact; all 8/8 store-forall                     *)
    (* new-block legs + plaintext + pointers + htable + MAYCHANGE close).       *)
    (* Resolve-at-load via RESOLVE_LDP2_TAC (fixes a RESOLVE_QREG_A              *)
    (* state-subscript bug: the ldp memory read stays at the LOAD-INPUT state). *)
    (* --- counter setup 1..13 (rev32/add folds) --- *)
    ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (1--1) THEN
    REV32_FOLD_TAC "Q5" "s1" `word (8*i+13):32 word` THEN
    ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (2--3) THEN GCM_SIMD_SIMPLIFY_TAC THEN
    CTR_INCR_NORM_TAC "s3" 13 THEN
    ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (4--7) THEN GCM_SIMD_SIMPLIFY_TAC THEN
    REV32_FOLD_TAC "Q6" "s7" `word (8*i+14):32 word` THEN
    ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (8--8) THEN GCM_SIMD_SIMPLIFY_TAC THEN
    CTR_INCR_NORM_TAC "s8" 14 THEN
    ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (9--13) THEN GCM_SIMD_SIMPLIFY_TAC THEN
    REV32_FOLD_TAC "Q7" "s13" `word (8*i+15):32 word` THEN
    (* --- AES/GHASH bulk 14..212 (KEEPDATA keeps Q0..Q19 incl keystream) --- *)
    ARM_STEPS_FOLD_KEEPDATA_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (14--120) THEN
    ARM_STEPS_FOLD_KEEPDATA_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (121--211) THEN DISCARD_STALE_Q19_TAC THEN
    ARM_STEPS_FOLD_KEEPDATA_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (212--212) THEN DISCARD_STALE_Q19_TAC THEN
    CTR_INCR_NORM_TAC "s212" 15 THEN
    (* --- 213..289 KEEPDATA; ldp@221 loads Q8,Q9 (resolve-at-load), ctr folds --- *)
    ARM_STEPS_FOLD_KEEPDATA_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (213--220) THEN
    RESOLVE_LDP2_TAC AESV8_GCM_8X_DEC_256_WB_EXEC "Q8" "Q9" 0 1 "s220" "s221" THEN
    ARM_STEPS_FOLD_KEEPDATA_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (222--258) THEN
    ARM_STEPS_FOLD_KEEPDATA_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (259--259) THEN
    REV32_FOLD_TAC "Q20" "s259" `word (8*i+16):32 word` THEN
    ARM_STEPS_FOLD_KEEPDATA_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (260--261) THEN
    CTR_INCR_NORM_TAC "s261" 16 THEN
    ARM_STEPS_FOLD_KEEPDATA_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (262--270) THEN
    REV32_FOLD_TAC "Q22" "s270" `word (8*i+17):32 word` THEN
    ARM_STEPS_FOLD_KEEPDATA_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (271--272) THEN
    (* ldp@273 loads Q10,Q11 *)
    RESOLVE_LDP2_TAC AESV8_GCM_8X_DEC_256_WB_EXEC "Q10" "Q11" 2 3 "s272" "s273" THEN
    ARM_STEPS_FOLD_KEEPDATA_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (274--279) THEN
    CTR_INCR_NORM_TAC "s279" 17 THEN
    ARM_STEPS_FOLD_KEEPDATA_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (280--288) THEN
    REV32_FOLD_TAC "Q23" "s288" `word (8*i+18):32 word` THEN
    ARM_STEPS_FOLD_KEEPDATA_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (289--289) THEN
    CTR_INCR_NORM_TAC "s289" 18 THEN
    (* --- Q19 R1' WIRE-IN: instead of DISCARDing the GHASH cluster,               *)
    (*     ABBREV the three s289 accumulators (Q17/Q19/Q18 = PL/PH/PM) opaque so    *)
    (*     the reduce byteform stays small (629ch), then KEEP Q16-Q19 through the   *)
    (*     reduce (KEEPDATA_NOSIMP keeps Q0-Q19 incl keystream AND the abbreviated  *)
    (*     Q19).  read Q19 s326 lands = WBN_MACHINE_REDUCE_IS_PROP3_PACK's LHS[PL,   *)
    (*     PH,PM]; the postcond Q19 conjunct then closes via WBN_Q19_CLOSE_TAC.     *)
    WBN_Q19_EXTRACT_ABBREV_TAC "s289" THEN
    ARM_STEPS_FOLD_KEEPDATA_NOSIMP_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (290--305) THEN
    (* ldp@306 loads Q12,Q13 ; ldp@309 loads Q14,Q15 *)
    RESOLVE_LDP2_TAC AESV8_GCM_8X_DEC_256_WB_EXEC "Q12" "Q13" 4 5 "s305" "s306" THEN
    ARM_STEPS_FOLD_KEEPDATA_NOSIMP_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (307--308) THEN
    RESOLVE_LDP2_TAC AESV8_GCM_8X_DEC_256_WB_EXEC "Q14" "Q15" 6 7 "s308" "s309" THEN
    (* --- store window 310..337 NOSIMP (keeps keystream Q0-Q7 + stores current); *)
    (*     fold the mov-source counters Q25@326, Q4@336, Q30 incr @335/337. --- *)
    ARM_STEPS_FOLD_KEEPDATA_NOSIMP_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (310--326) THEN
    REV32_FOLD_TAC "Q25" "s326" `word (8*i+19):32 word` THEN
    ARM_STEPS_FOLD_KEEPDATA_NOSIMP_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (327--335) THEN
    CTR_INCR_NORM_TAC "s335" 19 THEN
    ARM_STEPS_FOLD_KEEPDATA_NOSIMP_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (336--336) THEN
    REV32_FOLD_TAC "Q4" "s336" `word (8*i+20):32 word` THEN
    ARM_STEPS_FOLD_KEEPDATA_NOSIMP_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (337--337) THEN
    CTR_INCR_NORM_TAC "s337" 20 THEN
    (* --- back-edge: normalize X0, cmp @338, resolve NF/VF, stp @339, b.lt @340 --- *)
    RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
      `word_add (word_add in_p (word (128 * (i + 1)))) (word 128):int64 =
       word_add in_p (word (128*(i+2)))`]) THEN
    ARM_STEPS_FOLD_KEEPDATA_NOSIMP_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (338--338) THEN
    SUBGOAL_THEN `9 <= nblk` ASSUME_TAC THENL
     [MATCH_MP_TAC WBN_NBLK_GE_9 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    (* derive NF/VF flag equivalences as standalone theorems, rewrite into asms.
       (MUST rewrite into assumptions - MP_TAC'ing the implication into the goal
       pollutes the state and breaks the subsequent stp step, .) *)
    (fun (asl,w) ->
       let prem = MATCH_MP WBN_PTRCMP_PREMS
         (CONJ (ASSUME `val (in_p:int64) + 16 * nblk < 2 EXP 63`)
               (ASSUME `i < (nblk - 9) DIV 8`)) in
       let flags = MATCH_MP (SPECL [`in_p:int64`; `128*(i+2)`; `128*((nblk-1) DIV 8)`]
                     WB_PTRCMP_FLAGS) prem in
       RULE_ASSUM_TAC(REWRITE_RULE[CONJUNCT1 flags; CONJUNCT2 flags]) (asl,w)) THEN
    ARM_STEPS_FOLD_KEEPDATA_NOSIMP_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (339--340) THEN
    FIRST_X_ASSUM(fun th -> if can (find_term (fun t -> t = `read PC s340`)) (concl th)
      then ASSUME_TAC(REWRITE_RULE[MATCH_MP WBN_PC_BRIDGE (ASSUME `9 <= nblk`)] th)
      else NO_TAC) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    (* postcondition match: PC (WBN_PC_IF), counter indices (8*(i+1)=8*i+8), then
       the plaintext + Q8-Q15 (already resolved) + Q19 (CHEAT) + store-forall. *)
    REWRITE_TAC[WBN_PC_IF] THEN
    REWRITE_TAC[ARITH_RULE `8 * (i + 1) = 8 * i + 8`] THEN
    REWRITE_TAC[ARITH_RULE `(8*i+8)+8 = 8*i+16`; ARITH_RULE `(8*i+8)+9 = 8*i+17`;
      ARITH_RULE `(8*i+8)+10 = 8*i+18`; ARITH_RULE `(8*i+8)+11 = 8*i+19`;
      ARITH_RULE `(8*i+8)+12 = 8*i+20`; ARITH_RULE `(8*i+8)+13 = 8*i+21`] THEN
    (* ASM_REWRITE closes the already-resolved conjuncts (Q0-Q4 counters, Q8-Q15
       raw-ct); split the residual and close each remaining conjunct.  Drop the
       dead GHASH reduce-scratch (Q16..Q25/Q29) first so the pile is small. *)
    DISCARD_QREGS_TAC ["Q16";"Q17";"Q18";"Q19";"Q20";"Q21";"Q22";"Q23";"Q24";"Q25";"Q29"] THEN
    REPEAT CONJ_TAC THENL
     [ (* [0-2] plaintext Q5,Q6,Q7 *)
       PLAINTEXT_CLOSE_TAC; PLAINTEXT_CLOSE_TAC; PLAINTEXT_CLOSE_TAC;
       (* [3] Q19 GHASH acc — R1' close (was CHEAT): the goal is
          <machine reduce byteform over PL/PH/PM> = ghash..(8*i+8), closed by the
          CLEAN value-equality WBN_Q19_CLOSE_TAC builds from the stashed s289
          accumulators (WBN_MACHINE_REDUCE_IS_PROP3_PACK + block-algebra). *)
       WBN_Q19_CLOSE_TAC;
       (* [4-5] X0/X2 pointer advances *)
       CONV_TAC WORD_RULE; CONV_TAC WORD_RULE;
       (* [6] store-forall: old (j<8*(i+1)) from the invariant's own store-forall
          (preserved); new (8*(i+1)<=j<8*(i+1)+8) via the 8-way NEWBLK close. *)
       X_GEN_TAC `j:num` THEN DISCH_TAC THEN
       ASM_CASES_TAC `j < 8 * (i + 1)` THENL
        [ FIRST_ASSUM(fun th -> match concl th with
            Comb(Const("!",_),Abs(Var("j",_),Comb(Comb(Const("==>",_),
              Comb(Comb(Const("<",_),_),Comb(Comb(Const("*",_),_),
                Comb(Comb(Const("+",_),_),_)))),_))) ->
              MP_TAC(SPEC `j:num` th) | _ -> NO_TAC) THEN
          ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN(fun th -> REWRITE_TAC[th])];
          MP_TAC(ARITH_RULE
            `~(j < 8 * (i + 1)) /\ j < 8 * i + 16
             ==> j = 8*(i+1) \/ j = 8*(i+1)+1 \/ j = 8*(i+1)+2 \/ j = 8*(i+1)+3 \/
                 j = 8*(i+1)+4 \/ j = 8*(i+1)+5 \/ j = 8*(i+1)+6 \/ j = 8*(i+1)+7`) THEN
          ASM_REWRITE_TAC[] THEN
          DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC) THEN
          NEWBLK_CLOSE_TAC ];
       (* [7] htable predicate *)
       REWRITE_TAC[htable_mem_dec] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
       ASM_REWRITE_TAC[];
       (* [8] MAYCHANGE frame *)
       REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
       REPEAT CONJ_TAC THEN MONOTONE_MAYCHANGE_TAC ];
    (* 4. exit: PC=0x9f0 /\ core k -> same (0-step reflexive ensures) *)
    ENSURES_INIT_TAC "s0" THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    REPEAT CONJ_TAC THEN MONOTONE_MAYCHANGE_TAC]);;
(* --- mid-load heap compaction after WBN_MAIN_LOOP_raw (loop-body induction). --- *)
Gc.compact();;

(* ========================================================================= *)
(* Section 11. PHASE 5 -- PREPRETAIL (0x9f0..0xed4 straight-line sim).         *)
(*                                                                            *)
(* The loop-exit state (WBN_MAIN_LOOP_raw postcond: PC=pc+0x9f0, wbn_loop_inv_core_raw *)
(* at k=(nblk-9)DIV8, GHASH lagging one 8-block group) is driven through the   *)
(* prepretail code (0x9f0..0xed4, 313 instrs) to the SHARED TAIL SEAM at       *)
(* pc+3796 (=0xed4), the exact state every <=8-block WB_TAIL_r_TAC consumes                  *)
(* (ENSURES_INIT_TAC "s265" on q_at r = the <=8-block chain's wb_front_postcond[nblk:=r]).   *)
(*                                                                            *)
(* SEAM CONTRACT (verified against the <=8-block chain + Explore):                 *)
(*  - The tail seam is at pc+3796 (0xed4), NOT 0xec0.  The prepretail sims     *)
(*    THROUGH 0xec0..0xed0 (ext v16; sub x5,x4,x0; cmp; ldr q9,[x0],#16; ldp   *)
(*    q24,q25,[x6,#160]) to set up the tail's Q9/Q24/Q25/X0/X5 registers.      *)
(*  - In the <=8 band the FRONT folds 0 GHASH blocks (Q19=word_bytereverse xi) *)
(*    and the TAIL folds all r.  The prepretail is the pipelined analogue: it  *)
(*    folds the FINAL in-flight 8-block group (blocks 8k..8k+7) into Q19       *)
(*    (catching the lagging GHASH stream up), and computes AES keystreams for  *)
(*    the tail's Q0..Q7.                                                       *)
(*  - RECOMPOSE SUBSTITUTION (fully determined off the s313                    *)
(*    harvest): the prepretail postcond = wb_front_postcond instantiated with  *)
(*      ctr0'   := gcm_ctr_add (word (8*(k+1))) ctr0   (tail's shifted counter) *)
(*      in_p'   := word_add in_p  (word (128*(k+1)))                            *)
(*      out_p'  := word_add out_p (word (128*(k+1)))                            *)
(*      nblk'   := r = nblk - 8*(k+1)   (1..8)                                  *)
(*      xi'     := the caught-up ghash acc over all 8*(k+1) processed blocks    *)
(*      ibytes' := the last r blocks of ibytes                                 *)
(*    Q0..Q7 reconcile via GCM_CTR_ADD_COMPOSE:                                 *)
(*      gcm_ctr_add(8k+8+i) ctr0 = gcm_ctr_inc^i (gcm_ctr_add(8(k+1)) ctr0).    *)
(*                                                                            *)
(* SIM RECIPE (VALIDATED end-to-end, no hang/OOM; reaches                      *)
(* read PC s313 = word(pc+3796) with the full state harvested):                *)
(*                                                                            *)
(*   REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[wbn_loop_inv_core_raw] THEN     *)
(*   CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN ENSURES_INIT_TAC "s0" THEN         *)
(*   RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_dec]) THEN                          *)
(*   RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV let_CONV)) THEN                    *)
(*   FIRST_X_ASSUM(fun th -> ... strip the byteswap128/karatsuba_mid conj) THEN *)
(*   ABBREV_TAC for k := (nblk - 9) DIV 8, THEN                                 *)
(*   [counter setup 1..14: rev32 v5@2/v6@7/v7@14, add v30@3/9]                  *)
(*   ARM_STEPS_TAC EXEC (1--1) THEN               [ldp q26,q27 = keys k0,k1]    *)
(*   ARM_STEPS_TAC EXEC (2--2) THEN GCM_SIMD_SIMPLIFY_TAC THEN                  *)
(*   REV32_FOLD_TAC "Q5" "s2" [word (8*k+13):32 word] THEN                      *)
(*   ARM_STEPS_TAC EXEC (3--3) THEN GCM_SIMD_SIMPLIFY_TAC THEN CTR_INCR_NORM_TAC "s3" 13 THEN *)
(*   ARM_STEPS_TAC EXEC (4--7) THEN GCM_SIMD_SIMPLIFY_TAC THEN                  *)
(*   REV32_FOLD_TAC "Q6" "s7" [word (8*k+14):32 word] THEN                      *)
(*   ARM_STEPS_TAC EXEC (8--9) THEN GCM_SIMD_SIMPLIFY_TAC THEN CTR_INCR_NORM_TAC "s9" 14 THEN *)
(*   ARM_STEPS_TAC EXEC (10--14) THEN GCM_SIMD_SIMPLIFY_TAC THEN                *)
(*   REV32_FOLD_TAC "Q7" "s14" [word (8*k+15):32 word] THEN                     *)
(*   (* AES/GHASH bulk 15..240, KEEPDATA keeps Q0..Q19 *)                       *)
(*   ARM_STEPS_FOLD_KEEPDATA_TAC EXEC (15--120) THEN                            *)
(*   ARM_STEPS_FOLD_KEEPDATA_TAC EXEC (121--211) THEN                           *)
(*   ARM_STEPS_FOLD_KEEPDATA_TAC EXEC (212--240) THEN                           *)
(*   (* discard the GHASH cluster before the [sp+64] modulus reduce (Q19        *)
(*      CHEATed -- kills the concrete-modulus hang) *)                          *)
(*   DISCARD_QREGS_TAC ["Q16";"Q17";"Q18";"Q19"] THEN                           *)
(*   ARM_STEPS_FOLD_KEEPDATA_NOSIMP_TAC EXEC (241--306) THEN                    *)
(*   (* tail setup 307..313 -> pc+3796 *)                                       *)
(*   ARM_STEPS_FOLD_KEEPDATA_NOSIMP_TAC EXEC (307--313) THEN                    *)
(*   ENSURES_FINAL_STATE_TAC THEN ...close per-conjunct...                      *)
(*                                                                            *)
(* Harvested s313 register facts (k=(nblk-9)DIV8; all CHEAT-free except Q19):   *)
(*   PC = pc+3796                                        [matches seam]         *)
(*   Q0..Q7 = aes13(gcm_ctr_add(8k+8..8k+15) ctr0) k0..k13   [ctr shift]        *)
(*   Q24 = karatsuba_mid h8 || karatsuba_mid h7 ; Q25 = h8   [reloaded @0xed0]  *)
(*   Q16/Q19 = GHASH acc staging   -> SCOPED CHEAT (= the [11] RINNER=LINNER)   *)
(*   X0 = in_p+128(k+1)+16 ; X2 = out_p+128(k+1) ; X4 = in_p+16nblk             *)
(*   X5 = (in_p+16nblk)-(in_p+128(k+1)) = word(16*r)                            *)
(*   X1=128nblk X9=16nblk X10=sp+64 X11=key_p X3=xi_p X6=htbl_p X16=ivec_p      *)
(*   X15=2^32 Q31=2^96 SP=stackpointer ; [sp+64]=0xC2..; keys k0..k14; htable;  *)
(*   store-forall j<8*(k+1); input buffer -- all preserved.                    *)
(*   NF/ZF/CF/VF on word_sub(in_p+16nblk)(in_p+128(k+1)) vs 112 [-> r=... calc] *)
(* ========================================================================= *)

(* Counter-shift identity: the prepretail
   produces AES keystreams Q0..Q7 at absolute block indices 8*(k+1)+i (i=0..7),
   i.e. gcm_ctr_add(word(8*k+8+i))ctr0.  The shifted-front tail seam expects
   Q0..Q7 = aes13(gcm_ctr_inc^i ctr0') k0..k13 with ctr0' = gcm_ctr_add(8*(k+1))ctr0.
   This bridges the two forms so the recompose consumes wb_front_postcond verbatim. *)
let WBN_CTR_SHIFT = prove
 (`!(k:num) (i:num) (ctr0:int128).
     gcm_ctr_add (word (8*k+8+i)) ctr0 =
     gcm_ctr_inc_iter i (gcm_ctr_add (word (8*(k+1))) ctr0)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[GCM_CTR_INC_ITER_ADD; GCM_CTR_ADD_COMPOSE; WORD_ADD] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[GSYM WORD_ADD] THEN
  AP_TERM_TAC THEN ARITH_TAC);;

(*  SOUNDNESS FIX: this raw harvested literal states Q16/Q19 at a FRESH
   unconstrained xi' (read Q19 s = word_bytereverse xi', Q16 = its staging).  As written
   that is FALSE (word_bytereverse is a bijection + the ARM model is deterministic, so
   `!xi'. hyps ==> ensures ... Q19 = word_bytereverse xi'` cannot hold) -- flagged by the
   s035 review.  It is kept verbatim as `_raw` only as the substitution source; the SOUND
   post `wbn_prepretail_post` below pins xi' to the real caught-up accumulator. *)
let wbn_prepretail_post_raw = parse_term {|\(s:armstate).
    (aligned_bytes_loaded:armstate->(64)word->((8)word)list->bool)
    (s:armstate)
    ((word:num->(64)word) (pc:num))
    (aesv8_gcm_8x_dec_256_wb_mc:((8)word)list) /\
    (read:(armstate,(64)word)component->armstate->(64)word)
    (PC:(armstate,(64)word)component)
    (s:armstate) =
    (word:num->(64)word) ((pc:num) + 3828) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q24:(armstate,(128)word)component)
    (s:armstate) =
    (word_join:(64)word->(64)word->(128)word)
    ((karatsuba_mid:(128)word->(64)word)
    ((byteswap128:(128)word->(128)word)
    ((polyval_dot:(128)word->(128)word->(128)word)
     ((polyval_dot:(128)word->(128)word->(128)word)
      ((polyval_dot:(128)word->(128)word->(128)word)
       ((polyval_dot:(128)word->(128)word->(128)word)
        ((polyval_dot:(128)word->(128)word->(128)word)
         ((polyval_dot:(128)word->(128)word->(128)word)
          ((polyval_dot:(128)word->(128)word->(128)word)
           ((byteswap128:(128)word->(128)word) (h:(128)word))
          ((byteswap128:(128)word->(128)word) (h:(128)word)))
         ((byteswap128:(128)word->(128)word) (h:(128)word)))
        ((byteswap128:(128)word->(128)word) (h:(128)word)))
       ((byteswap128:(128)word->(128)word) (h:(128)word)))
      ((byteswap128:(128)word->(128)word) (h:(128)word)))
     ((byteswap128:(128)word->(128)word) (h:(128)word)))
    ((byteswap128:(128)word->(128)word) (h:(128)word)))))
    ((karatsuba_mid:(128)word->(64)word)
    ((byteswap128:(128)word->(128)word)
    ((polyval_dot:(128)word->(128)word->(128)word)
     ((polyval_dot:(128)word->(128)word->(128)word)
      ((polyval_dot:(128)word->(128)word->(128)word)
       ((polyval_dot:(128)word->(128)word->(128)word)
        ((polyval_dot:(128)word->(128)word->(128)word)
         ((polyval_dot:(128)word->(128)word->(128)word)
          ((byteswap128:(128)word->(128)word) (h:(128)word))
         ((byteswap128:(128)word->(128)word) (h:(128)word)))
        ((byteswap128:(128)word->(128)word) (h:(128)word)))
       ((byteswap128:(128)word->(128)word) (h:(128)word)))
      ((byteswap128:(128)word->(128)word) (h:(128)word)))
     ((byteswap128:(128)word->(128)word) (h:(128)word)))
    ((byteswap128:(128)word->(128)word) (h:(128)word))))) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q25:(armstate,(128)word)component)
    (s:armstate) =
    (byteswap128:(128)word->(128)word)
    ((polyval_dot:(128)word->(128)word->(128)word)
     ((polyval_dot:(128)word->(128)word->(128)word)
      ((polyval_dot:(128)word->(128)word->(128)word)
       ((polyval_dot:(128)word->(128)word->(128)word)
        ((polyval_dot:(128)word->(128)word->(128)word)
         ((polyval_dot:(128)word->(128)word->(128)word)
          ((polyval_dot:(128)word->(128)word->(128)word)
           ((byteswap128:(128)word->(128)word) (h:(128)word))
          ((byteswap128:(128)word->(128)word) (h:(128)word)))
         ((byteswap128:(128)word->(128)word) (h:(128)word)))
        ((byteswap128:(128)word->(128)word) (h:(128)word)))
       ((byteswap128:(128)word->(128)word) (h:(128)word)))
      ((byteswap128:(128)word->(128)word) (h:(128)word)))
     ((byteswap128:(128)word->(128)word) (h:(128)word)))
    ((byteswap128:(128)word->(128)word) (h:(128)word))) /\
    ((read:(armstate,bool)component->armstate->bool)
     (NF:(armstate,bool)component)
     (s:armstate) <=>
     (ival:(64)word->int)
     ((word_sub:(64)word->(64)word->(64)word)
      ((word_sub:(64)word->(64)word->(64)word)
       ((word_add:(64)word->(64)word->(64)word) (in_p:(64)word)
       ((word:num->(64)word) (16 * (nblk:num))))
      ((word_add:(64)word->(64)word->(64)word) (in_p:(64)word)
      ((word:num->(64)word) (128 * (((nblk:num) - 9) DIV 8 + 1)))))
     ((word:num->(64)word) 112)) <
     (int_of_num:num->int)0) /\
    ((read:(armstate,bool)component->armstate->bool)
     (ZF:(armstate,bool)component)
     (s:armstate) <=>
     (val:(64)word->num)
     ((word_sub:(64)word->(64)word->(64)word)
      ((word_sub:(64)word->(64)word->(64)word)
       ((word_add:(64)word->(64)word->(64)word) (in_p:(64)word)
       ((word:num->(64)word) (16 * (nblk:num))))
      ((word_add:(64)word->(64)word->(64)word) (in_p:(64)word)
      ((word:num->(64)word) (128 * (((nblk:num) - 9) DIV 8 + 1)))))
     ((word:num->(64)word) 112)) =
     0) /\
    ((read:(armstate,bool)component->armstate->bool)
     (CF:(armstate,bool)component)
     (s:armstate) <=>
     112 <=
     (val:(64)word->num)
     ((word_sub:(64)word->(64)word->(64)word)
      ((word_add:(64)word->(64)word->(64)word) (in_p:(64)word)
      ((word:num->(64)word) (16 * (nblk:num))))
     ((word_add:(64)word->(64)word->(64)word) (in_p:(64)word)
     ((word:num->(64)word) (128 * (((nblk:num) - 9) DIV 8 + 1)))))) /\
    ((read:(armstate,bool)component->armstate->bool)
     (VF:(armstate,bool)component)
     (s:armstate) <=>
     ~((ival:(64)word->int)
       ((word_sub:(64)word->(64)word->(64)word)
        ((word_add:(64)word->(64)word->(64)word) (in_p:(64)word)
        ((word:num->(64)word) (16 * (nblk:num))))
       ((word_add:(64)word->(64)word->(64)word) (in_p:(64)word)
       ((word:num->(64)word) (128 * (((nblk:num) - 9) DIV 8 + 1))))) -
       (int_of_num:num->int)112 =
       (ival:(64)word->int)
       ((word_sub:(64)word->(64)word->(64)word)
        ((word_sub:(64)word->(64)word->(64)word)
         ((word_add:(64)word->(64)word->(64)word) (in_p:(64)word)
         ((word:num->(64)word) (16 * (nblk:num))))
        ((word_add:(64)word->(64)word->(64)word) (in_p:(64)word)
        ((word:num->(64)word) (128 * (((nblk:num) - 9) DIV 8 + 1)))))
       ((word:num->(64)word) 112)))) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q16:(armstate,(128)word)component)
    (s:armstate) =
    (word_subword:(256)word->num#num->(128)word)
    ((word_join:(128)word->(128)word->(256)word)
     ((word_bytereverse:(128)word->(128)word) (xi':(128)word))
    ((word_bytereverse:(128)word->(128)word) (xi':(128)word)))
    (64,128) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q7:(armstate,(128)word)component)
    (s:armstate) =
    (aes13:(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word)
    ((gcm_ctr_add:(32)word->(128)word->(128)word)
     ((word:num->(32)word) (8 * ((nblk:num) - 9) DIV 8 + 15))
    (ctr0:(128)word))
    (k0:(128)word)
    (k1:(128)word)
    (k2:(128)word)
    (k3:(128)word)
    (k4:(128)word)
    (k5:(128)word)
    (k6:(128)word)
    (k7:(128)word)
    (k8:(128)word)
    (k9:(128)word)
    (k10:(128)word)
    (k11:(128)word)
    (k12:(128)word)
    (k13:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q6:(armstate,(128)word)component)
    (s:armstate) =
    (aes13:(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word)
    ((gcm_ctr_add:(32)word->(128)word->(128)word)
     ((word:num->(32)word) (8 * ((nblk:num) - 9) DIV 8 + 14))
    (ctr0:(128)word))
    (k0:(128)word)
    (k1:(128)word)
    (k2:(128)word)
    (k3:(128)word)
    (k4:(128)word)
    (k5:(128)word)
    (k6:(128)word)
    (k7:(128)word)
    (k8:(128)word)
    (k9:(128)word)
    (k10:(128)word)
    (k11:(128)word)
    (k12:(128)word)
    (k13:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q0:(armstate,(128)word)component)
    (s:armstate) =
    (aes13:(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word)
    ((gcm_ctr_add:(32)word->(128)word->(128)word)
     ((word:num->(32)word) (8 * ((nblk:num) - 9) DIV 8 + 8))
    (ctr0:(128)word))
    (k0:(128)word)
    (k1:(128)word)
    (k2:(128)word)
    (k3:(128)word)
    (k4:(128)word)
    (k5:(128)word)
    (k6:(128)word)
    (k7:(128)word)
    (k8:(128)word)
    (k9:(128)word)
    (k10:(128)word)
    (k11:(128)word)
    (k12:(128)word)
    (k13:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q1:(armstate,(128)word)component)
    (s:armstate) =
    (aes13:(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word)
    ((gcm_ctr_add:(32)word->(128)word->(128)word)
     ((word:num->(32)word) (8 * ((nblk:num) - 9) DIV 8 + 9))
    (ctr0:(128)word))
    (k0:(128)word)
    (k1:(128)word)
    (k2:(128)word)
    (k3:(128)word)
    (k4:(128)word)
    (k5:(128)word)
    (k6:(128)word)
    (k7:(128)word)
    (k8:(128)word)
    (k9:(128)word)
    (k10:(128)word)
    (k11:(128)word)
    (k12:(128)word)
    (k13:(128)word) /\
    (read:(armstate,(64)word)component->armstate->(64)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes64:(64)word->((64)word->(8)word,(64)word)component)
     ((word_add:(64)word->(64)word->(64)word) (stackpointer:(64)word)
     ((word:num->(64)word) 64)))
    (s:armstate) =
    (word:num->(64)word) 13979173243358019584 /\
    (read:(armstate,(64)word)component->armstate->(64)word)
    (X11:(armstate,(64)word)component)
    (s:armstate) =
    (key_p:(64)word) /\
    (read:(armstate,(64)word)component->armstate->(64)word)
    (X9:(armstate,(64)word)component)
    (s:armstate) =
    (word:num->(64)word) (16 * (nblk:num)) /\
    (read:(armstate,(64)word)component->armstate->(64)word)
    (SP:(armstate,(64)word)component)
    (s:armstate) =
    (stackpointer:(64)word) /\
    (read:(armstate,(64)word)component->armstate->(64)word)
    (X1:(armstate,(64)word)component)
    (s:armstate) =
    (word:num->(64)word) (128 * (nblk:num)) /\
    (read:(armstate,(64)word)component->armstate->(64)word)
    (X2:(armstate,(64)word)component)
    (s:armstate) =
    (word_add:(64)word->(64)word->(64)word) (out_p:(64)word)
    ((word:num->(64)word) (128 * (((nblk:num) - 9) DIV 8 + 1))) /\
    (read:(armstate,(64)word)component->armstate->(64)word)
    (X3:(armstate,(64)word)component)
    (s:armstate) =
    (xi_p:(64)word) /\
    (read:(armstate,(64)word)component->armstate->(64)word)
    (X6:(armstate,(64)word)component)
    (s:armstate) =
    (htbl_p:(64)word) /\
    (read:(armstate,num)component->armstate->num)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes:(64)word#num->((64)word->(8)word,num)component)
     ((in_p:(64)word),16 * (nblk:num)))
    (s:armstate) =
    (num_of_bytelist:((8)word)list->num) (ibytes:((8)word)list) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     (key_p:(64)word))
    (s:armstate) =
    (k0:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (key_p:(64)word)
     ((word:num->(64)word) 16)))
    (s:armstate) =
    (k1:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (key_p:(64)word)
     ((word:num->(64)word) 32)))
    (s:armstate) =
    (k2:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (key_p:(64)word)
     ((word:num->(64)word) 48)))
    (s:armstate) =
    (k3:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (key_p:(64)word)
     ((word:num->(64)word) 64)))
    (s:armstate) =
    (k4:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (key_p:(64)word)
     ((word:num->(64)word) 80)))
    (s:armstate) =
    (k5:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (key_p:(64)word)
     ((word:num->(64)word) 96)))
    (s:armstate) =
    (k6:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (key_p:(64)word)
     ((word:num->(64)word) 112)))
    (s:armstate) =
    (k7:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (key_p:(64)word)
     ((word:num->(64)word) 128)))
    (s:armstate) =
    (k8:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (key_p:(64)word)
     ((word:num->(64)word) 144)))
    (s:armstate) =
    (k9:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (key_p:(64)word)
     ((word:num->(64)word) 160)))
    (s:armstate) =
    (k10:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (key_p:(64)word)
     ((word:num->(64)word) 176)))
    (s:armstate) =
    (k11:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (key_p:(64)word)
     ((word:num->(64)word) 192)))
    (s:armstate) =
    (k12:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (key_p:(64)word)
     ((word:num->(64)word) 208)))
    (s:armstate) =
    (k13:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (key_p:(64)word)
     ((word:num->(64)word) 224)))
    (s:armstate) =
    (k14:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     (htbl_p:(64)word))
    (s:armstate) =
    (h:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (htbl_p:(64)word)
     ((word:num->(64)word) 16)))
    (s:armstate) =
    (word_join:(64)word->(64)word->(128)word)
    ((karatsuba_mid:(128)word->(64)word)
    ((byteswap128:(128)word->(128)word)
    ((polyval_dot:(128)word->(128)word->(128)word)
     ((byteswap128:(128)word->(128)word) (h:(128)word))
    ((byteswap128:(128)word->(128)word) (h:(128)word)))))
    ((karatsuba_mid:(128)word->(64)word) (h:(128)word)) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (htbl_p:(64)word)
     ((word:num->(64)word) 32)))
    (s:armstate) =
    (byteswap128:(128)word->(128)word)
    ((polyval_dot:(128)word->(128)word->(128)word)
     ((byteswap128:(128)word->(128)word) (h:(128)word))
    ((byteswap128:(128)word->(128)word) (h:(128)word))) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (htbl_p:(64)word)
     ((word:num->(64)word) 48)))
    (s:armstate) =
    (byteswap128:(128)word->(128)word)
    ((polyval_dot:(128)word->(128)word->(128)word)
     ((polyval_dot:(128)word->(128)word->(128)word)
      ((byteswap128:(128)word->(128)word) (h:(128)word))
     ((byteswap128:(128)word->(128)word) (h:(128)word)))
    ((byteswap128:(128)word->(128)word) (h:(128)word))) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (htbl_p:(64)word)
     ((word:num->(64)word) 64)))
    (s:armstate) =
    (word_join:(64)word->(64)word->(128)word)
    ((karatsuba_mid:(128)word->(64)word)
    ((byteswap128:(128)word->(128)word)
    ((polyval_dot:(128)word->(128)word->(128)word)
     ((polyval_dot:(128)word->(128)word->(128)word)
      ((polyval_dot:(128)word->(128)word->(128)word)
       ((byteswap128:(128)word->(128)word) (h:(128)word))
      ((byteswap128:(128)word->(128)word) (h:(128)word)))
     ((byteswap128:(128)word->(128)word) (h:(128)word)))
    ((byteswap128:(128)word->(128)word) (h:(128)word)))))
    ((karatsuba_mid:(128)word->(64)word)
    ((byteswap128:(128)word->(128)word)
    ((polyval_dot:(128)word->(128)word->(128)word)
     ((polyval_dot:(128)word->(128)word->(128)word)
      ((byteswap128:(128)word->(128)word) (h:(128)word))
     ((byteswap128:(128)word->(128)word) (h:(128)word)))
    ((byteswap128:(128)word->(128)word) (h:(128)word))))) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (htbl_p:(64)word)
     ((word:num->(64)word) 80)))
    (s:armstate) =
    (byteswap128:(128)word->(128)word)
    ((polyval_dot:(128)word->(128)word->(128)word)
     ((polyval_dot:(128)word->(128)word->(128)word)
      ((polyval_dot:(128)word->(128)word->(128)word)
       ((byteswap128:(128)word->(128)word) (h:(128)word))
      ((byteswap128:(128)word->(128)word) (h:(128)word)))
     ((byteswap128:(128)word->(128)word) (h:(128)word)))
    ((byteswap128:(128)word->(128)word) (h:(128)word))) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (htbl_p:(64)word)
     ((word:num->(64)word) 96)))
    (s:armstate) =
    (byteswap128:(128)word->(128)word)
    ((polyval_dot:(128)word->(128)word->(128)word)
     ((polyval_dot:(128)word->(128)word->(128)word)
      ((polyval_dot:(128)word->(128)word->(128)word)
       ((polyval_dot:(128)word->(128)word->(128)word)
        ((byteswap128:(128)word->(128)word) (h:(128)word))
       ((byteswap128:(128)word->(128)word) (h:(128)word)))
      ((byteswap128:(128)word->(128)word) (h:(128)word)))
     ((byteswap128:(128)word->(128)word) (h:(128)word)))
    ((byteswap128:(128)word->(128)word) (h:(128)word))) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (htbl_p:(64)word)
     ((word:num->(64)word) 112)))
    (s:armstate) =
    (word_join:(64)word->(64)word->(128)word)
    ((karatsuba_mid:(128)word->(64)word)
    ((byteswap128:(128)word->(128)word)
    ((polyval_dot:(128)word->(128)word->(128)word)
     ((polyval_dot:(128)word->(128)word->(128)word)
      ((polyval_dot:(128)word->(128)word->(128)word)
       ((polyval_dot:(128)word->(128)word->(128)word)
        ((polyval_dot:(128)word->(128)word->(128)word)
         ((byteswap128:(128)word->(128)word) (h:(128)word))
        ((byteswap128:(128)word->(128)word) (h:(128)word)))
       ((byteswap128:(128)word->(128)word) (h:(128)word)))
      ((byteswap128:(128)word->(128)word) (h:(128)word)))
     ((byteswap128:(128)word->(128)word) (h:(128)word)))
    ((byteswap128:(128)word->(128)word) (h:(128)word)))))
    ((karatsuba_mid:(128)word->(64)word)
    ((byteswap128:(128)word->(128)word)
    ((polyval_dot:(128)word->(128)word->(128)word)
     ((polyval_dot:(128)word->(128)word->(128)word)
      ((polyval_dot:(128)word->(128)word->(128)word)
       ((polyval_dot:(128)word->(128)word->(128)word)
        ((byteswap128:(128)word->(128)word) (h:(128)word))
       ((byteswap128:(128)word->(128)word) (h:(128)word)))
      ((byteswap128:(128)word->(128)word) (h:(128)word)))
     ((byteswap128:(128)word->(128)word) (h:(128)word)))
    ((byteswap128:(128)word->(128)word) (h:(128)word))))) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (htbl_p:(64)word)
     ((word:num->(64)word) 128)))
    (s:armstate) =
    (byteswap128:(128)word->(128)word)
    ((polyval_dot:(128)word->(128)word->(128)word)
     ((polyval_dot:(128)word->(128)word->(128)word)
      ((polyval_dot:(128)word->(128)word->(128)word)
       ((polyval_dot:(128)word->(128)word->(128)word)
        ((polyval_dot:(128)word->(128)word->(128)word)
         ((byteswap128:(128)word->(128)word) (h:(128)word))
        ((byteswap128:(128)word->(128)word) (h:(128)word)))
       ((byteswap128:(128)word->(128)word) (h:(128)word)))
      ((byteswap128:(128)word->(128)word) (h:(128)word)))
     ((byteswap128:(128)word->(128)word) (h:(128)word)))
    ((byteswap128:(128)word->(128)word) (h:(128)word))) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (htbl_p:(64)word)
     ((word:num->(64)word) 144)))
    (s:armstate) =
    (byteswap128:(128)word->(128)word)
    ((polyval_dot:(128)word->(128)word->(128)word)
     ((polyval_dot:(128)word->(128)word->(128)word)
      ((polyval_dot:(128)word->(128)word->(128)word)
       ((polyval_dot:(128)word->(128)word->(128)word)
        ((polyval_dot:(128)word->(128)word->(128)word)
         ((polyval_dot:(128)word->(128)word->(128)word)
          ((byteswap128:(128)word->(128)word) (h:(128)word))
         ((byteswap128:(128)word->(128)word) (h:(128)word)))
        ((byteswap128:(128)word->(128)word) (h:(128)word)))
       ((byteswap128:(128)word->(128)word) (h:(128)word)))
      ((byteswap128:(128)word->(128)word) (h:(128)word)))
     ((byteswap128:(128)word->(128)word) (h:(128)word)))
    ((byteswap128:(128)word->(128)word) (h:(128)word))) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (htbl_p:(64)word)
     ((word:num->(64)word) 160)))
    (s:armstate) =
    (word_join:(64)word->(64)word->(128)word)
    ((karatsuba_mid:(128)word->(64)word)
    ((byteswap128:(128)word->(128)word)
    ((polyval_dot:(128)word->(128)word->(128)word)
     ((polyval_dot:(128)word->(128)word->(128)word)
      ((polyval_dot:(128)word->(128)word->(128)word)
       ((polyval_dot:(128)word->(128)word->(128)word)
        ((polyval_dot:(128)word->(128)word->(128)word)
         ((polyval_dot:(128)word->(128)word->(128)word)
          ((polyval_dot:(128)word->(128)word->(128)word)
           ((byteswap128:(128)word->(128)word) (h:(128)word))
          ((byteswap128:(128)word->(128)word) (h:(128)word)))
         ((byteswap128:(128)word->(128)word) (h:(128)word)))
        ((byteswap128:(128)word->(128)word) (h:(128)word)))
       ((byteswap128:(128)word->(128)word) (h:(128)word)))
      ((byteswap128:(128)word->(128)word) (h:(128)word)))
     ((byteswap128:(128)word->(128)word) (h:(128)word)))
    ((byteswap128:(128)word->(128)word) (h:(128)word)))))
    ((karatsuba_mid:(128)word->(64)word)
    ((byteswap128:(128)word->(128)word)
    ((polyval_dot:(128)word->(128)word->(128)word)
     ((polyval_dot:(128)word->(128)word->(128)word)
      ((polyval_dot:(128)word->(128)word->(128)word)
       ((polyval_dot:(128)word->(128)word->(128)word)
        ((polyval_dot:(128)word->(128)word->(128)word)
         ((polyval_dot:(128)word->(128)word->(128)word)
          ((byteswap128:(128)word->(128)word) (h:(128)word))
         ((byteswap128:(128)word->(128)word) (h:(128)word)))
        ((byteswap128:(128)word->(128)word) (h:(128)word)))
       ((byteswap128:(128)word->(128)word) (h:(128)word)))
      ((byteswap128:(128)word->(128)word) (h:(128)word)))
     ((byteswap128:(128)word->(128)word) (h:(128)word)))
    ((byteswap128:(128)word->(128)word) (h:(128)word))))) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    ((memory:(armstate,(64)word->(8)word)component) :>
     (bytes128:(64)word->((64)word->(8)word,(128)word)component)
     ((word_add:(64)word->(64)word->(64)word) (htbl_p:(64)word)
     ((word:num->(64)word) 176)))
    (s:armstate) =
    (byteswap128:(128)word->(128)word)
    ((polyval_dot:(128)word->(128)word->(128)word)
     ((polyval_dot:(128)word->(128)word->(128)word)
      ((polyval_dot:(128)word->(128)word->(128)word)
       ((polyval_dot:(128)word->(128)word->(128)word)
        ((polyval_dot:(128)word->(128)word->(128)word)
         ((polyval_dot:(128)word->(128)word->(128)word)
          ((polyval_dot:(128)word->(128)word->(128)word)
           ((byteswap128:(128)word->(128)word) (h:(128)word))
          ((byteswap128:(128)word->(128)word) (h:(128)word)))
         ((byteswap128:(128)word->(128)word) (h:(128)word)))
        ((byteswap128:(128)word->(128)word) (h:(128)word)))
       ((byteswap128:(128)word->(128)word) (h:(128)word)))
      ((byteswap128:(128)word->(128)word) (h:(128)word)))
     ((byteswap128:(128)word->(128)word) (h:(128)word)))
    ((byteswap128:(128)word->(128)word) (h:(128)word))) /\
    (read:(armstate,(64)word)component->armstate->(64)word)
    (X16:(armstate,(64)word)component)
    (s:armstate) =
    (ivec_p:(64)word) /\
    (read:(armstate,(64)word)component->armstate->(64)word)
    (X10:(armstate,(64)word)component)
    (s:armstate) =
    (word_add:(64)word->(64)word->(64)word) (stackpointer:(64)word)
    ((word:num->(64)word) 64) /\
    (read:(armstate,(64)word)component->armstate->(64)word)
    (X15:(armstate,(64)word)component)
    (s:armstate) =
    (word:num->(64)word) 4294967296 /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q31:(armstate,(128)word)component)
    (s:armstate) =
    (word:num->(128)word) 79228162514264337593543950336 /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q19:(armstate,(128)word)component)
    (s:armstate) =
    (word_bytereverse:(128)word->(128)word) (xi':(128)word) /\
    (read:(armstate,(64)word)component->armstate->(64)word)
    (X4:(armstate,(64)word)component)
    (s:armstate) =
    (word_add:(64)word->(64)word->(64)word) (in_p:(64)word)
    ((word:num->(64)word) (16 * (nblk:num))) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q27:(armstate,(128)word)component)
    (s:armstate) =
    (k13:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q26:(armstate,(128)word)component)
    (s:armstate) =
    (k12:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q28:(armstate,(128)word)component)
    (s:armstate) =
    (k14:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q5:(armstate,(128)word)component)
    (s:armstate) =
    (aes13:(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word)
    ((gcm_ctr_add:(32)word->(128)word->(128)word)
     ((word:num->(32)word) (8 * ((nblk:num) - 9) DIV 8 + 13))
    (ctr0:(128)word))
    (k0:(128)word)
    (k1:(128)word)
    (k2:(128)word)
    (k3:(128)word)
    (k4:(128)word)
    (k5:(128)word)
    (k6:(128)word)
    (k7:(128)word)
    (k8:(128)word)
    (k9:(128)word)
    (k10:(128)word)
    (k11:(128)word)
    (k12:(128)word)
    (k13:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q2:(armstate,(128)word)component)
    (s:armstate) =
    (aes13:(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word)
    ((gcm_ctr_add:(32)word->(128)word->(128)word)
     ((word:num->(32)word) (8 * ((nblk:num) - 9) DIV 8 + 10))
    (ctr0:(128)word))
    (k0:(128)word)
    (k1:(128)word)
    (k2:(128)word)
    (k3:(128)word)
    (k4:(128)word)
    (k5:(128)word)
    (k6:(128)word)
    (k7:(128)word)
    (k8:(128)word)
    (k9:(128)word)
    (k10:(128)word)
    (k11:(128)word)
    (k12:(128)word)
    (k13:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q4:(armstate,(128)word)component)
    (s:armstate) =
    (aes13:(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word)
    ((gcm_ctr_add:(32)word->(128)word->(128)word)
     ((word:num->(32)word) (8 * ((nblk:num) - 9) DIV 8 + 12))
    (ctr0:(128)word))
    (k0:(128)word)
    (k1:(128)word)
    (k2:(128)word)
    (k3:(128)word)
    (k4:(128)word)
    (k5:(128)word)
    (k6:(128)word)
    (k7:(128)word)
    (k8:(128)word)
    (k9:(128)word)
    (k10:(128)word)
    (k11:(128)word)
    (k12:(128)word)
    (k13:(128)word) /\
    (read:(armstate,(128)word)component->armstate->(128)word)
    (Q3:(armstate,(128)word)component)
    (s:armstate) =
    (aes13:(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word->(128)word)
    ((gcm_ctr_add:(32)word->(128)word->(128)word)
     ((word:num->(32)word) (8 * ((nblk:num) - 9) DIV 8 + 11))
    (ctr0:(128)word))
    (k0:(128)word)
    (k1:(128)word)
    (k2:(128)word)
    (k3:(128)word)
    (k4:(128)word)
    (k5:(128)word)
    (k6:(128)word)
    (k7:(128)word)
    (k8:(128)word)
    (k9:(128)word)
    (k10:(128)word)
    (k11:(128)word)
    (k12:(128)word)
    (k13:(128)word) /\
    (read:(armstate,(64)word)component->armstate->(64)word)
    (X5:(armstate,(64)word)component)
    (s:armstate) =
    (word_sub:(64)word->(64)word->(64)word)
    ((word_add:(64)word->(64)word->(64)word) (in_p:(64)word)
    ((word:num->(64)word) (16 * (nblk:num))))
    ((word_add:(64)word->(64)word->(64)word) (in_p:(64)word)
    ((word:num->(64)word) (128 * (((nblk:num) - 9) DIV 8 + 1)))) /\
    (read:(armstate,(64)word)component->armstate->(64)word)
    (X0:(armstate,(64)word)component)
    (s:armstate) =
    (word_add:(64)word->(64)word->(64)word)
    ((word_add:(64)word->(64)word->(64)word) (in_p:(64)word)
    ((word:num->(64)word) (128 * (((nblk:num) - 9) DIV 8 + 1))))
    ((word:num->(64)word) 16)|};;

(*  SOUNDNESS FIX.  The caught-up GHASH tag: the
   loop invariant's Q19 shape (Sec 4, :623) at index i := k+1 = (nblk-9)DIV8 + 1, i.e. the
   fold over ALL 8*(k+1) processed blocks.  This IS the true machine value of Q19 at the
   prepretail seam (the loop exits with the GHASH stream lagging 8 blocks; the prepretail
   folds the final in-flight 8-block group, catching it up to 8*(k+1)).  It is a FUNCTION of
   the pinned inputs (xi/h/ibytes/nblk from wb_front_vars), NOT a fresh unconstrained var, so
   the Q16/Q19 conjuncts below become the SAME true-but-unproven RINNER=LINNER identity as
   [11] (:2085) -- masked by the same scoped disclosed CHEAT, not a falsehood. *)
let wbn_caught_up = `ghash_polyval_acc (byteswap128 (h:int128)) (word_bytereverse (xi:int128))
    (MAP word_bytereverse
    (list_of_seq (\k. bytes_to_int128 (SUB_LIST (16 * k,16) (ibytes:byte list)))
                 (8 * (((nblk:num) - 9) DIV 8 + 1))))`;;

(* Replace the raw literal's fresh `word_bytereverse xi'` (which occurs ONLY in the Q16
   staging and Q19 conjuncts -- verified s036) with the caught-up accumulator.  This drops
   xi' entirely (so the post's frees are exactly wb_front_vars) and turns:
     Q19 = word_bytereverse xi'  -->  Q19 = wbn_caught_up   (matches the i:=k+1 invariant shape)
     Q16 = word_subword(word_join (word_bytereverse xi')(word_bytereverse xi'))(64,128)
        -->  Q16 = word_subword(word_join wbn_caught_up wbn_caught_up)(64,128)  (staging of Q19) *)
let wbn_prepretail_post =
  subst [wbn_caught_up, `word_bytereverse (xi':int128)`] wbn_prepretail_post_raw;;

(* the shifted-front prepretail postcondition (VALIDATED end-to-end).
   Built by harvesting the s313 state after the 313-instr sim + wb_front_fold_tac,
   with the two loop-un-tracked memory cells DROPPED (sound; see below) and the two
   GHASH staging regs Q16/Q19 stated at a fresh caught-up tag var xi'.
   Deltas vs a naive vsubst of the <=8-block chain's wb_front_postcond:
    - Q0..Q7 = aes13 (gcm_ctr_add (word (8*k+8+i)) ctr0) k0..k13 (i=0..7, k=(nblk-9)DIV8);
      the shifted-front form aes13 (gcm_ctr_inc^i ctr0') with ctr0'=gcm_ctr_add(8(k+1))ctr0
      is bridged by WBN_CTR_SHIFT for the Phase-6 recompose.
    - X0=in_p+128(k+1)+16, X2=out_p+128(k+1), X5/flags on word_sub(in_p+16nblk)(in_p+128(k+1)).
    - DROPPED (loop invariant does not track them; objdump 0xeec..0x11c8 shows the tail
      only STORES ivec_p (str q30,[x16]@0x1144) and xi_p (st1 v19,[x3]@0x11ac) at the very
      end and never READS their pre-values):
        read (memory :> bytes128 xi_p) s = xi     (front seed; tail uses Q19, not this)
        read (memory :> bytes128 ivec_p) s = ctr0
        read (memory :> bytes64 (sp+72)) s = word 0   (only [sp+64] is the reduce const)
        read (memory :> bytes128 in_p) s = <block0>   (Q9; the tail re-loads via ldr q9,[x0])
      Also DROPPED Q9 = <first tail block> (tail reloads it).  Phase 6 re-proves the tail
      leg (WB_TAIL_r) from this weaker post -- WB_TAIL_r_TAC never consumes the dropped
      facts (verified: no xi_p/ivec_p reads, and it re-loads Q9).
    - Q16/Q19 caught-up tag:  pins it to `wbn_caught_up` (the i:=k+1 invariant
      Q19 shape, a function of the pinned inputs) -- NOT a fresh xi'.  The s035-committed
      form used a fresh unconstrained xi' (Q19 = word_bytereverse xi'), which review
      found FALSE-as-written (bijection + determinism); s036 corrected it (see the SOUNDNESS
      FIX note above `wbn_caught_up`).  Q19 = wbn_caught_up, Q16 = its staging.  These two
      close behind the scoped disclosed CHEAT below (= the [11] RINNER=LINNER identity at
      :2085; the prepretail's own final in-flight GHASH fold is the SAME identity). *)

(* index bound for the first tail block lane (8*k+8 < nblk when nblk>=17). *)
let WBN_Q9_INDEX_LT = prove
 (`!nblk. 17 <= nblk /\ 128 * nblk < 2 EXP 62 ==> 8 * ((nblk - 9) DIV 8) + 8 < nblk`,
  GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL[`nblk - 9`;`8`] DIVISION) THEN ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `k = (nblk - 9) DIV 8` THEN ASM_ARITH_TAC);;

(* index bound for the first-tail-block lane, 9<= variant (8*k+8 < nblk, k=0 here).
   Proves the SAME conclusion as WBN_Q9_INDEX_LT from the weaker 9<=nblk band.
   hoisted here from its original spot down in the 9..16 section so
   the unified prepretail sim WBN_PREPRETAIL_EXT2_UNIFIED can consume it; also still
   used by the FRONT-916 / PREP_TO_END_916 chain below. *)
let WBN_Q9_INDEX_LT_9 = prove
 (`!nblk. 9 <= nblk /\ 128 * nblk < 2 EXP 62 ==> 8 * ((nblk - 9) DIV 8) + 8 < nblk`,
  GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL[`nblk - 9`;`8`] DIVISION) THEN ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `k = (nblk - 9) DIV 8` THEN ASM_ARITH_TAC);;

(* NOTE: the bare-post prepretail theorem
   WBN_PREPRETAIL (and its goal wbn_prepretail_goal) was fully superseded by the
   output-forall + Q9 augmented WBN_PREPRETAIL_EXT2 below (a full standalone
   re-sim, ~131s) and was never consumed by any live chain; it has been deleted
   (each cold load ran that ~131s prepretail sim three times -- bare / _EXT /
   _EXT2 -- only the last is used).  The base post term `wbn_prepretail_post` is
   retained: WBN_PREPRETAIL_EXT2's post is built from it (via
   wbn_prepretail_post_ext). *)

(* ------------------------------------------------------------------------- *)
(* Section 12. PHASE 6 -- recompose the nblk>8 chain.                         *)
(* ------------------------------------------------------------------------- *)

(* NOTE: the bare-post recompose theorems
   WBN_LOOP_PREP (LOOP;PREPRETAIL) and WBN_FRONT_TO_PREP (FRONT;LOOP;PREPRETAIL),
   plus their goals wbn_loop_prep_goal / wbn_front_to_prep_goal, were superseded
   by the EXT2 recompose (WBN_LOOP_PREP_EXT2 / WBN_FRONT_TO_PREP_EXT2 below, which
   _CORRECT actually uses) and were never consumed; deleted.  The ENSURES_TRANS_
   SIMPLE + ENSURES_PRECONDITION_THM route they documented survives verbatim in
   the EXT2 versions. *)

(* ------------------------------------------------------------------------- *)
(*  -- the OUTPUT-STORE-FORALL augmentation of the prepretail post.            *)
(*                                                                            *)
(* GAP: wbn_prepretail_post (64 conjuncts) DROPS the loop                     *)
(* invariant's quantified output-store conjunct                               *)
(*   !j. j < 8*((nblk-9)DIV8 + 1) ==>                                         *)
(*       read (memory :> bytes128 (word_add out_p (word (16*j)))) s =         *)
(*       word_xor (word_xor (bytes_to_int128 (SUB_LIST (16*j,16) ibytes))     *)
(*                (aes13 (gcm_ctr_inc_iter j ctr0) k0..k13)) k14              *)
(* (mainloop.ml:644).  Those are the first 8*(k+1) DECRYPTED output blocks.   *)
(* The Phase-6/7 final per-block output post needs stores for ALL nblk blocks;*)
(* the Phase-6 tail leg (WB_TAIL_r) produces only the last r = nblk-8*(k+1),   *)
(* so the first 8*(k+1) MUST be carried through the seam.  The prepretail      *)
(* region (0x9f0..0xed4) does ZERO output stores (objdump), so the forall      *)
(* passes through the KEEPDATA sim unchanged -- re-proving the prepretail with *)
(* the forall appended to its post closes it by ASM_REWRITE (a genuine         *)
(* preserved read-fact, NOT frame-preservation: ENSURES_ADD_PRESERVED cannot   *)
(* be used because the MAYCHANGE frame permits out_p writes).                  *)
(*                                                                            *)
(* wbn_out_forall = the invariant's output-store forall at i:=k, as a          *)
(* predicate on s (extracted from wbn_loop_inv_core_raw to guarantee it is the     *)
(* SAME term the sim preserves).  wbn_prepretail_post_ext = the 65-conjunct    *)
(* post = wbn_prepretail_post /\ wbn_out_forall.                               *)
(* ------------------------------------------------------------------------- *)

let wbn_out_forall =
  let full = list_mk_comb(wbn_core_applied, [`(nblk - 9) DIV 8`; `s:armstate`]) in
  let inv_cs = conjuncts (rhs(concl (REWRITE_CONV[wbn_loop_inv_core_raw] full))) in
  mk_abs(`s:armstate`, find is_forall inv_cs);;

let wbn_prepretail_post_ext =
  mk_abs(`s:armstate`,
    mk_conj(snd(dest_abs wbn_prepretail_post),
            snd(dest_abs wbn_out_forall)));;

(* NOTE: the EXT-post prepretail theorem
   WBN_PREPRETAIL_EXT (another full ~131s re-sim) and its EXT recompose
   WBN_LOOP_PREP_EXT / WBN_FRONT_TO_PREP_EXT (with goals wbn_prepretail_ext_goal /
   wbn_loop_prep_ext_goal / wbn_front_to_prep_ext_goal) were an intermediate step
   between the bare post and the EXT2 post; the EXT2 versions below carry a
   strictly larger post and are what _CORRECT uses, so the EXT theorems were never
   consumed and have been deleted.  The post term wbn_prepretail_post_ext (above)
   is KEPT -- WBN_PREPRETAIL_EXT2's post is wbn_prepretail_post_ext /\ <Q9>. *)

(* ------------------------------------------------------------------------- *)
(*  -- WBN_Q9_SPEC: the first-tail-block resolver for the seam.                *)
(*                                                                            *)
(* At the prepretail seam (pc+3796) the code has just executed                 *)
(*   ecc:  ldr q9, [x0], #16     (x0 = in_p + 128*(k+1) pre-increment)         *)
(* so the sim carries  read Q9 s313 = read (memory :> bytes128                 *)
(*   (word_add in_p (word (128*(k+1))))) s311  -- a RAW memory read.            *)
(* The tail's FIRST instruction eor3 v12,v9,v0,v29 @0xedc reads                 *)
(* this Q9 (objdump-confirmed: incoming Q9 is consumed BEFORE any tail reload   *)
(* at 0xfa4), so it MUST reach the tail seam in spec form.  This lemma resolves  *)
(* that raw read to bytes_to_int128 (SUB_LIST (16*8*(k+1),16) ibytes) = the      *)
(* first tail block (global block 8*(k+1)) via INPUT_BYTES_TO_BYTE128_LANES at    *)
(* lane 8*(k+1), given 8*(k+1) < nblk (WBN_Q9_INDEX_LT) and the preserved        *)
(* whole-buffer input-bytes fact.  hyps=0.                                       *)
(* USE: add read Q9 = <this RHS> to the prepretail post, resolve                 *)
(* it in the sim right before ENSURES_FINAL_STATE via                           *)
(*   MP_TAC(SPECL[...] WBN_Q9_SPEC) using the s313 input-bytes fact + the raw    *)
(*   Q9 read (bridge s311->s313 memory equality: no stores 0xecc..0xed4).         *)
(* ------------------------------------------------------------------------- *)
let WBN_Q9_SPEC = prove
 (`!(nblk:num) (in_p:int64) (ibytes:byte list) (k:num) (s:armstate).
     LENGTH ibytes = 16 * nblk /\
     8 * (k + 1) < nblk /\
     read (memory :> bytes (in_p,16 * nblk)) s = num_of_bytelist ibytes
     ==> read (memory :> bytes128 (word_add in_p (word (128 * (k + 1))))) s =
         bytes_to_int128 (SUB_LIST (16 * (8 * (k + 1)),16) ibytes)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`nblk:num`; `in_p:int64`; `ibytes:byte list`; `s:armstate`]
    INPUT_BYTES_TO_BYTE128_LANES) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [ASM_ARITH_TAC;
      SUBGOAL_THEN `SUB_LIST (0, 16 * nblk) (ibytes:byte list) = ibytes` SUBST1_TAC THENL
       [MATCH_MP_TAC SUB_LIST_LENGTH_IMPLIES THEN ASM_REWRITE_TAC[LE_REFL]; ALL_TAC] THEN
      ASM_REWRITE_TAC[]];
    DISCH_THEN(MP_TAC o SPEC `8 * (k + 1):num`) THEN
    ANTS_TAC THENL
     [ASM_ARITH_TAC;
      REWRITE_TAC[ARITH_RULE `16 * (8 * (k + 1)) = 128 * (k + 1)`] THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th])]]);;

(* ------------------------------------------------------------------------- *)
(*  -- EXT2: prepretail post carrying BOTH the output-store forall             *)
(* (from EXT) AND the incoming Q9 (first tail block, global block 8*(k+1)).    *)
(*                                                                            *)
(* GAP: besides the output forall (carried by EXT), the tail's                 *)
(* FIRST instruction eor3 v12,v9,v0,v29 @0xedc consumes the INCOMING Q9 BEFORE  *)
(* any tail reload (WBN_Q9_SPEC comment) -- so Q9 must reach the seam in spec   *)
(* form.  wbn_prepretail_post_ext2 = wbn_prepretail_post_ext /\ the Q9 conjunct *)
(* (read Q9 s = bytes_to_int128 (SUB_LIST (16 * 8 * ((nblk-9) DIV 8 + 1),16)    *)
(* ibytes), aconv WBN_Q9_SPEC at k := (nblk-9) DIV 8).                          *)
(*                                                                            *)
(* Proof route (the robust alternative):                                        *)
(* the ldr q9,[x0],#16 @0xecc (step 312) carries a RAW s311 memory read; the    *)
(* s311->s313 memory-equality bridge is awkward (no s311 MAYCHANGE -- the frame *)
(* is s0->s313 only).  Instead SPLIT the sim at s311 and resolve Q9 THERE: the  *)
(* whole-buffer input-bytes fact is live at s311 under KEEPDATA, x0@s311 =      *)
(* in_p+128*(k+1) confirmed, so MP_TAC'ing WBN_Q9_SPEC (ANTS by WBN_Q9_INDEX_LT *)
(* + ARITH) plants read(mem:>bytes128(in_p+128*(k+1))) s311 = <spec>; the ldr    *)
(* q9 then auto-resolves Q9 to that spec form via ASM_REWRITE.  Identical sim    *)
(* to WBN_PREPRETAIL_EXT (~131s) otherwise; same scoped Q16/Q19 CHEAT.  hyps=0.  *)
(* ------------------------------------------------------------------------- *)

(*  (ivec write-back, M1 keystone): the prepretail post now also
   carries the advanced CTR-block counter register Q30, so the ivec write-back
   conjunct `read (memory :> bytes128 ivec_p) s = word_bytereverse (ctr_block
   nonce (c + nblk))` can be threaded to the exported theorems downstream (M2).
   At the seam the counter has been incremented 3x past the loop-head value
   gcm_ctr_raw (word (8*k+13)) ctr0 (adds at .S 0x9f8/0xa10/0xeb4, k=(nblk-9)DIV8),
   landing at gcm_ctr_raw (word (8*k+16)) ctr0.  The third add is un-normalized in
   the NOSIMP reduce window; WBN_PREPRETAIL_EXT2_TAC folds it (CTR_RAW_INCR_FOLD at
   s311 + a WORD_RULE 8k+15+1->8k+16) before ENSURES_FINAL.  Load-safe in isolation:
   this conjunct only STRENGTHENS the seam precond that the downstream WBN_PREP_TO_END
   / LOOP_PREP / FRONT_TO_PREP legs consume (they ignore the extra assumption). *)
let wbn_prepretail_post_ext2 =
  mk_abs(`s:armstate`,
    mk_conj(snd(dest_abs wbn_prepretail_post_ext),
            mk_conj(
              `read Q9 (s:armstate) =
               bytes_to_int128 (SUB_LIST (16 * 8 * ((nblk - 9) DIV 8 + 1),16) ibytes)`,
              `read Q30 (s:armstate) =
               gcm_ctr_raw (word (8 * ((nblk - 9) DIV 8) + 16)) ctr0`)));;

let wbn_prepretail_ext2_goal =
  let kk = `(nblk - 9) DIV 8` in
  let pre = mk_abs(`s:armstate`,
    list_mk_conj[
      `aligned_bytes_loaded s (word pc) aesv8_gcm_8x_dec_256_wb_mc`;
      `read PC s = word (pc + 0xa10)`;
      mk_comb(mk_comb(wbn_core_applied,kk),`s:armstate`)]) in
  let ens = list_mk_comb(`ensures arm`,[pre; wbn_prepretail_post_ext2; wbn_front_C_tm]) in
  list_mk_forall(wb_front_vars, mk_imp(wbn_front_hyps_wide_tm, ens));;

(* The prepretail ext2 sim, parameterized by the first-tail-block index bound
   (idx_lt_thm : `... ==> 8 * ((nblk-9) DIV 8) + 8 < nblk`).  The 17<=nblk and
   9..16 legs (WBN_PREPRETAIL_EXT2 / _916) differ ONLY in that lemma
   (WBN_Q9_INDEX_LT vs WBN_Q9_INDEX_LT_9) and in their hyp band; every ARM step,
   fold, and close is identical, so the ~131s recipe lives here once.
   Recipe: init at the loop invariant (i:=k), counter folds 1..14, KEEPDATA bulk
   15..240; Q19 R1' wire-in (step to s242 where PL/PH/PM=Q17/Q19/Q18
   are complete -- PM's final eor3@0xdb4 is instr 242 -- ABBREV them opaque, then
   the reduce KEEPING Q16-Q19 so the byteform stays small); resolve the incoming
   Q9 at s311 (before ldr q9 @0xecc=step 312) to spec form via WBN_Q9_SPEC +
   idx_lt_thm; ENSURES_FINAL + ASM_REWRITE for the preserved/shifted conjuncts;
   the 2 GHASH conjuncts close via WBN_Q19_PREPRETAIL_CLOSE_TAC (R1' route,
   CHEAT-free since s065). *)
let WBN_PREPRETAIL_EXT2_TAC idx_lt_thm =
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[wbn_loop_inv_core_raw] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN ENSURES_INIT_TAC "s0" THEN
  CLEAR_KEEPDATA_MEMO_TAC THEN  (* refine-101: reset the KEEPDATA normalizer fixpoint cache *)
  RULE_ASSUM_TAC(REWRITE_RULE[WB_MC_LEN]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_dec]) THEN
  RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV let_CONV)) THEN
  FIRST_X_ASSUM(fun th ->
    let c = concl th in
    if can (find_term (fun t->match t with Const("byteswap128",_)->true|_->false)) c &&
       can (find_term (fun t->match t with Const("karatsuba_mid",_)->true|_->false)) c
    then STRIP_ASSUME_TAC th else NO_TAC) THEN
  ABBREV_TAC `k = (nblk - 9) DIV 8` THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (1--1) THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (2--2) THEN GCM_SIMD_SIMPLIFY_TAC THEN
  REV32_FOLD_TAC "Q5" "s2" `word (8*k+13):32 word` THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (3--3) THEN GCM_SIMD_SIMPLIFY_TAC THEN
  CTR_INCR_NORM_TAC "s3" 13 THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (4--7) THEN GCM_SIMD_SIMPLIFY_TAC THEN
  REV32_FOLD_TAC "Q6" "s7" `word (8*k+14):32 word` THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (8--9) THEN GCM_SIMD_SIMPLIFY_TAC THEN
  CTR_INCR_NORM_TAC "s9" 14 THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (10--14) THEN GCM_SIMD_SIMPLIFY_TAC THEN
  REV32_FOLD_TAC "Q7" "s14" `word (8*k+15):32 word` THEN
  ARM_STEPS_FOLD_KEEPDATA_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (15--120) THEN
  ARM_STEPS_FOLD_KEEPDATA_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (121--211) THEN
  ARM_STEPS_FOLD_KEEPDATA_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (212--240) THEN
  ARM_STEPS_FOLD_KEEPDATA_NOSIMP_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (241--242) THEN
  WBN_Q19_EXTRACT_ABBREV_TAC "s242" THEN
  ARM_STEPS_FOLD_KEEPDATA_NOSIMP_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (243--306) THEN
  ARM_STEPS_FOLD_KEEPDATA_NOSIMP_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (307--311) THEN
  (* fold the 3rd add-v30 counter increment (un-normalized in the
     NOSIMP window; the first two were folded by CTR_INCR_NORM at s3/s9).  The
     lane tower over gcm_ctr_raw (word (8*k+15)) ctr0 collapses to +1, then a
     WORD_RULE normalizes 8*k+15+1 -> 8*k+16 = the seam counter value.  No
     add-v30 occurs in steps 312-313 (ldr q9 / ldp q24,q25), so the folded fact
     carries to the seam state as the latest read Q30. *)
  CTR_RAW_INCR_FOLD_TAC "Q30" "s311" `word (8*k+15):32 word` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
    `word_add (word (8*k+15)) (word 1):32 word = word (8*k+16)`]) THEN
  MP_TAC(SPECL [`nblk:num`; `in_p:int64`; `ibytes:byte list`; `k:num`; `s311:armstate`]
    WBN_Q9_SPEC) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MP_TAC(SPEC `nblk:num` idx_lt_thm) THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    DISCH_TAC] THEN
  ARM_STEPS_FOLD_KEEPDATA_NOSIMP_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (312--313) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM aes13]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE(map GSYM wb_ctr_lanes_thms)) THEN
  ENSURES_FINAL_STATE_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REPEAT CONJ_TAC THEN
  TRY(W(fun (asl,w) ->
        if can (find_term (fun t -> is_const t && fst(dest_const t) = "ghash_polyval_acc")) w
        then WBN_Q19_PREPRETAIL_CLOSE_TAC `k:num` else NO_TAC)) THEN
  TRY MONOTONE_MAYCHANGE_TAC THEN
  TRY (ASM_REWRITE_TAC[]);;

(* SPEED: the prepretail EXT2 sim (~137s) was run TWICE per cold
   load -- here (17<=nblk) and again at WBN_PREPRETAIL_EXT2_916 (9..16) -- with
   IDENTICAL pre/post/sim, differing ONLY in the index lemma fed to the WBN_Q9_SPEC
   ANTS (WBN_Q9_INDEX_LT vs _9).  But WBN_Q9_INDEX_LT_9 proves that side condition
   (8*((nblk-9)DIV8)+8 < nblk) from the WEAKER 9<=nblk band, so a single sim on the
   unified 9<=nblk band is sound and covers both; each band theorem then follows by
   pure hyp-strengthening (MATCH_MP + ASM_ARITH, <0.1s, hyps=0).  This deletes one
   full ~137s sim from every cold load.  The unified band term is built with the
   file's own recursive-replace idiom (17<=nblk -> 9<=nblk), matching how
   wbn_front_hyps_916_tm is built. *)
let wbn_front_hyps_9_tm =
  let rec repl t = match t with
    | Comb(Comb(Const("/\\",_),a),b) -> mk_conj(repl a, repl b)
    | _ -> if t = `17 <= nblk` then `9 <= nblk` else t in
  repl wbn_front_hyps_wide_tm;;

let wbn_prepretail_ext2_uni_goal =
  let kk = `(nblk - 9) DIV 8` in
  let pre = mk_abs(`s:armstate`,
    list_mk_conj[
      `aligned_bytes_loaded s (word pc) aesv8_gcm_8x_dec_256_wb_mc`;
      `read PC s = word (pc + 0xa10)`;
      mk_comb(mk_comb(wbn_core_applied,kk),`s:armstate`)]) in
  let ens = list_mk_comb(`ensures arm`,[pre; wbn_prepretail_post_ext2; wbn_front_C_tm]) in
  list_mk_forall(wb_front_vars, mk_imp(wbn_front_hyps_9_tm, ens));;

(* The one and only prepretail EXT2 sim, on the unified 9<=nblk band. *)
let WBN_PREPRETAIL_EXT2_UNIFIED =
  prove(wbn_prepretail_ext2_uni_goal, WBN_PREPRETAIL_EXT2_TAC WBN_Q9_INDEX_LT_9);;

(* 17<=nblk band: statement-identical to the pre-069 WBN_PREPRETAIL_EXT2 (aconv
   verified); now a no-sim hyp-strengthening of the unified theorem. *)
let WBN_PREPRETAIL_EXT2 =
  prove(wbn_prepretail_ext2_goal,
    REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC WBN_PREPRETAIL_EXT2_UNIFIED THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

(* WBN_LOOP_PREP_EXT2 / WBN_FRONT_TO_PREP_EXT2: the EXT2-post analogues,          *)
(* chaining through WBN_PREPRETAIL_EXT2.  Same ENSURES_TRANS_SIMPLE /             *)
(* ENSURES_PRECONDITION_THM route as the EXT versions (incl. the two-rator       *)
(* peel that picks the PRE of WBN_LOOP_PREP_EXT2, not its post).  Both hyps=0.    *)
let wbn_loop_prep_ext2_goal =
  let loop_pre = mk_abs(`s:armstate`,
    list_mk_conj[
      `aligned_bytes_loaded s (word pc) aesv8_gcm_8x_dec_256_wb_mc`;
      `read PC s = word (pc + 0x4c0)`;
      mk_comb(mk_comb(wbn_core_applied,`0`),`s:armstate`)]) in
  let ens = list_mk_comb(`ensures arm`,[loop_pre; wbn_prepretail_post_ext2; wbn_front_C_tm]) in
  list_mk_forall(wb_front_vars, mk_imp(wbn_front_hyps_wide_tm, ens));;

let WBN_LOOP_PREP_EXT2 = prove(wbn_loop_prep_ext2_goal,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC ENSURES_TRANS_SIMPLE THEN
  EXISTS_TAC (rand(rator(snd(dest_imp(snd(strip_forall(concl WBN_MAIN_LOOP_raw))))))) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN MAYCHANGE_IDEMPOT_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MP_TAC(SPECL wb_front_vars WBN_MAIN_LOOP_raw) THEN
    ANTS_TAC THENL [FIRST_X_ASSUM ACCEPT_TAC; DISCH_THEN ACCEPT_TAC];
    MP_TAC(SPECL wb_front_vars WBN_PREPRETAIL_EXT2) THEN
    ANTS_TAC THENL [FIRST_X_ASSUM ACCEPT_TAC; DISCH_THEN ACCEPT_TAC]]);;

let wbn_front_to_prep_ext2_goal =
  let ens = list_mk_comb(`ensures arm`,
    [wbn_front_P_tm; wbn_prepretail_post_ext2; wbn_front_C_tm]) in
  list_mk_forall(wb_front_vars, mk_imp(wbn_front_hyps_wide_tm, ens));;

let WBN_FRONT_TO_PREP_EXT2 = prove(wbn_front_to_prep_ext2_goal,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC ENSURES_TRANS_SIMPLE THEN
  EXISTS_TAC wbn_entry_post THEN
  CONJ_TAC THENL
   [REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN MAYCHANGE_IDEMPOT_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MP_TAC(SPECL wb_front_vars WBN_LOOP_INVARIANT_ENTRY_RAW) THEN
    ANTS_TAC THENL [FIRST_X_ASSUM ACCEPT_TAC; DISCH_THEN ACCEPT_TAC];
    MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN
    EXISTS_TAC (rand(rator(rator(snd(dest_imp(snd(strip_forall(concl WBN_LOOP_PREP_EXT2)))))))) THEN
    CONJ_TAC THENL
     [GEN_TAC THEN REWRITE_TAC[WBN_INV_RAW_SPLIT] THEN
      CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
      REWRITE_TAC[ARITH_RULE `pc + 0x4c0 = pc + 1216`] THEN CONV_TAC TAUT;
      MP_TAC(SPECL wb_front_vars WBN_LOOP_PREP_EXT2) THEN
      ANTS_TAC THENL [FIRST_X_ASSUM ACCEPT_TAC; DISCH_THEN ACCEPT_TAC]]]);;

(* ========================================================================= *)
(*  -- PHASE 6 STEP 2: the tail leg (WBN_PREP_TO_END).                       *)
(*                                                                           *)
(* KEY STRUCTURAL FACT: the <=8-block chain's WB_TAIL_r_TAC tail proofs                    *)
(* already START at pc+3796 -- EXACTLY the EXT2 seam PC -- and drive to      *)
(* pc+4528 (the whole-function exit) CHEAT-FREE (they discharge the r-block  *)
(* GHASH via GMULT{r}_FULL_CORRECT_BA).  The shared per-block back-leg       *)
(* WB_TAIL_GEN2_r -- `ensures arm (weak q_at r) (band_post r) (band_frame r)`*)
(* -- is proved ONCE up front (refactor, at the prove_band site)             *)
(* and reused both by prove_band and here by the nblk>8 recomposition, which *)
(* feeds it by precondition-weakening (no re-simulation).  wbn_dissect_band, *)
(* wbn_tail_drop_lhs(6), wbn_weak_q_at6, wbn_tail_backleg_goal6 and the       *)
(* WB_TAIL_GEN2_1..8 theorems are all defined at that earlier site.          *)
(* ------------------------------------------------------------------------- *)

(* ========================================================================= *)
(*  -- PHASE 6 STEP 2b: WBN_PREP_TO_END assembly infrastructure.             *)
(*                                                                           *)
(* SOUNDNESS FIX to the (uncommitted) STEP-2b recipe.  That                  *)
(* recipe fed WB_TAIL_GEN_r (which keep X1,X9 in their weak precond) by      *)
(* ENSURES_PRECONDITION_THM from wbn_prepretail_post_ext2, claiming all 20   *)
(* non-aconv conjuncts reconcile "by pure ARITH".  In fact 2                 *)
(* of them are UNDERIVABLE, not ARITH:                                       *)
(*    ext2 delivers  read X1 s = word (128 * nblk),  read X9 s = word (16*nblk) *)
(*    but a SPECL'd tail (in_p:=in_p+128(k+1), nblk-role:=r) wants           *)
(*                    read X1 s = word (128 * r),    read X9 s = word (16*r).  *)
(* For nblk = 8*(k+1)+r >= 17 these differ, so ext2_post ==> shifted_weak_q_at_r *)
(* FAILS on X1/X9 exactly.  objdump: X1,X9 are DEAD in the tail range         *)
(* [0xed4,0x11b0) (0 reads), so the sound fix is to DROP X1,X9 from the tail  *)
(* precond too (6 dropped cells, not 4) and re-prove the tail leg from the    *)
(* 63-conjunct weak precond.  WB_TAIL_GEN2_1 below CONFIRMS the tail sim      *)
(* needs neither (hyps=0, ~133s, identical WB_PREP_TAC r THEN WB_TAIL_r_TAC). *)
(* ------------------------------------------------------------------------- *)

(* num_of_bytelist = num_of_wordlist on byte lists (needed by WBN_INPUT_SLICE). *)
let NUM_OF_BYTELIST_EQ_WORDLIST = prove
 (`!l:byte list. num_of_bytelist l = num_of_wordlist l`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[num_of_bytelist; num_of_wordlist; DIMINDEX_8] THEN ARITH_TAC);;

(* Input-read restriction: the whole-buffer read restricts to any 16-byte    *)
(* block boundary 128*(k+1).  This discharges the shifted tail precond's      *)
(* `read (memory :> bytes (in_p+128(k+1),16)) s = num_of_bytelist (SUB_LIST...)` *)
(* conjunct from ext2's `read (memory :> bytes (in_p,16*nblk)) s = ... ibytes`.  *)
(* (hyps=0).                                                                  *)
let WBN_INPUT_SLICE = prove
 (`!(nblk:num) (in_p:int64) (ibytes:byte list) (k:num) (s:armstate).
     LENGTH ibytes = 16 * nblk /\ 8 * (k + 1) < nblk /\
     read (memory :> bytes (in_p,16 * nblk)) s = num_of_bytelist ibytes
     ==> read (memory :> bytes (word_add in_p (word (128 * (k + 1))),16)) s =
         num_of_bytelist (SUB_LIST (128 * (k + 1),16) ibytes)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`in_p:int64`; `16 * nblk`; `128 * (k+1)`; `read memory (s:armstate)`]
    READ_BYTES_DIV) THEN
  REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `read (memory :> bytes (word_add in_p (word (128 * (k + 1))),16)) s =
     (read (memory :> bytes (word_add in_p (word (128 * (k + 1))),
                             16 * nblk - 128 * (k + 1))) s) MOD 2 EXP (8 * 16)`
   SUBST1_TAC THENL
   [MP_TAC(ISPECL [`word_add in_p (word (128 * (k+1))):int64`;
                   `16 * nblk - 128 * (k+1)`; `16`; `read memory (s:armstate)`]
       READ_BYTES_MOD) THEN
    REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN
    SUBGOAL_THEN `MIN (16 * nblk - 128 * (k + 1)) 16 = 16` SUBST1_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REFL_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[NUM_OF_BYTELIST_EQ_WORDLIST] THEN
  REWRITE_TAC[NUM_OF_WORDLIST_SUB_LIST; DIMINDEX_8] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC);;

(* Generalization of WBN_INPUT_SLICE to an arbitrary slice length              *)
(* m (= 16*r):  the r>1 shifted tail reads 16*r input bytes at 128*(k+1), not   *)
(* just 16.  Same proof, m kept symbolic under 128*(k+1)+m <= 16*nblk. hyps=0.  *)
let WBN_INPUT_SLICE_GEN = prove
 (`!(nblk:num) (in_p:int64) (ibytes:byte list) (k:num) (m:num) (s:armstate).
     LENGTH ibytes = 16 * nblk /\ 128 * (k + 1) + m <= 16 * nblk /\
     read (memory :> bytes (in_p,16 * nblk)) s = num_of_bytelist ibytes
     ==> read (memory :> bytes (word_add in_p (word (128 * (k + 1))),m)) s =
         num_of_bytelist (SUB_LIST (128 * (k + 1),m) ibytes)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`in_p:int64`; `16 * nblk`; `128 * (k+1)`; `read memory (s:armstate)`]
    READ_BYTES_DIV) THEN
  REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `read (memory :> bytes (word_add in_p (word (128 * (k + 1))),m)) s =
     (read (memory :> bytes (word_add in_p (word (128 * (k + 1))),
                             16 * nblk - 128 * (k + 1))) s) MOD 2 EXP (8 * m)`
   SUBST1_TAC THENL
   [MP_TAC(ISPECL [`word_add in_p (word (128 * (k+1))):int64`;
                   `16 * nblk - 128 * (k+1)`; `m:num`; `read memory (s:armstate)`]
       READ_BYTES_MOD) THEN
    REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN
    SUBGOAL_THEN `MIN (16 * nblk - 128 * (k + 1)) m = m` SUBST1_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REFL_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[NUM_OF_BYTELIST_EQ_WORDLIST] THEN
  REWRITE_TAC[NUM_OF_WORDLIST_SUB_LIST; DIMINDEX_8] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC);;

(* NOTE: the 6-cell-drop weak-precond builders                                  *)
(* (wbn_tail_drop_lhs6, wbn_weak_q_at6, wbn_tail_backleg_goal6) and the eight    *)
(* WB_TAIL_GEN2_1..8 back-leg theorems are now defined ONCE at the prove_band    *)
(* site, so the per-block tail sim runs 8x per load, not 16x.                    *)
(* prove_band reuses them by precondition-weakening; the nblk>8 recomposition    *)
(* below (INNER_TAIL_FEED_TAC / wbn_tail_gen2) references the same theorems.     *)

(* ------------------------------------------------------------------------- *)
(* WBN_PREP_TO_END_r recipe (VALIDATED for r=1 down to a full close: the       *)
(* reconciliation tactic below takes ext2_post ==>                            *)
(* shifted_weak_q_at6_1 to exactly its 4 trivial residuals -- 3 flags + the    *)
(* input-read -- all discharged by the helpers above + a per-subgoal           *)
(* WORD_RULE).                                                                *)
(*                                                                           *)
(* shift_vals r (SPECL order = wb_front_vars minus nblk, 27 terms):           *)
(*   [pc; stackpointer;                                                        *)
(*    word_add out_p (word (128*((nblk-9) DIV 8+1)));  xi_p; ivec_p;           *)
(*    word_add in_p (word (128*((nblk-9) DIV 8+1)));   key_p; htbl_p;          *)
(*    SUB_LIST (128*((nblk-9) DIV 8+1), 16*r) ibytes;             (:byte list) *)
(*    word_bytereverse wbn_caught_up;                             (:int128)    *)
(*    gcm_ctr_add (word (8*((nblk-9) DIV 8+1))) ctr0;             (:int128)    *)
(*    k0..k14; h]   -- annotate every ibytes/int128 or SPECL invents tyvars.   *)
(*                                                                           *)
(* WBN_PREP_TO_END_r : ensures arm wbn_prepretail_post_ext2                    *)
(*                       (shifted band_post r) wbn_front_C_tm                   *)
(*   under hyp  nblk = 8*((nblk-9) DIV 8 + 1) + r.  Build via:                  *)
(*   MATCH_MP_TAC ENSURES_FRAME_SUBSUMED (narrow tail frame -> wide ext2 frame  *)
(*     wbn_front_C_tm; SUBSUMED via SUBSUMED_ASSIGNS_BYTES on out_p sub-region  *)
(*     bytes(out_p+128(k+1),16) subsumed bytes(out_p,16*nblk))                  *)
(*   THEN MATCH_MP_TAC ENSURES_PRECONDITION_THM                                 *)
(*     EXISTS_TAC (shifted weak_q_at6 r) THEN CONJ_TAC THENL                     *)
(*     [ <the pre-implication, tactic below>;                                    *)
(*       MP_TAC(SPECL (shift_vals r) WB_TAIL_GEN2_r) THEN ANTS (nonoverlapping/  *)
(*         LENGTH from ext2 wide hyps; SUB_LIST_LENGTH + 16*r<=remaining) ].      *)
(*                                                                           *)
(* PRE-IMPLICATION tactic  (!s. ext2_post s ==> shifted_weak_q_at6_r s), r=1     *)
(* validated to 0 residuals with the helpers:                                   *)
(*   REPEAT GEN_TAC THEN STRIP_TAC THEN                                          *)
(*   ASM_REWRITE_TAC[WORD_BYTEREVERSE_BYTEREVERSE] THEN                          *)
(*   SUBGOAL_THEN `16 * nblk = 128 * ((nblk-9) DIV 8 + 1) + 16*r` ASSUME_TAC     *)
(*     THENL [UNDISCH_TAC `nblk = 8*((nblk-9) DIV 8+1)+r` THEN ARITH_TAC; ALL] THEN *)
(*   -- flags first, BEFORE any CONJ split, so the fact hits all of them:        *)
(*   SUBGOAL_THEN `word_sub (word_add in_p (word (128*((nblk-9)DIV8+1)+16*r)))    *)
(*      (word_add in_p (word (128*((nblk-9)DIV8+1)))):int64 = word (16*r)`        *)
(*     ASSUME_TAC THENL [CONV_TAC WORD_RULE; ALL] THEN  (* r=1: word 16 *)        *)
(*   REWRITE_TAC[GSYM GCM_CTR_ADD_1; GCM_CTR_ADD_COMPOSE] THEN                    *)
(*   REWRITE_TAC[SUB_LIST_MIN_RIGHT; ARITH_RULE `16*8*x=128*x`;                   *)
(*               ARITH_RULE `MIN 16 (16*r)=16` (r>=1)] THEN                       *)
(*   (for the input-read conjunct) MP_TAC(SPECL[...] WBN_INPUT_SLICE) + ANTS THEN *)
(*   UNDISCH `16*nblk=...` THEN DISCH_THEN(fun th->REWRITE_TAC[th]) THEN          *)
(*   ABBREV_TAC `q=(nblk-9) DIV 8` THEN                                          *)
(*   REWRITE_TAC[the `8*q+N=8*(q+1)+(N-8)` (N=8..15) + `((a+1)+..)=a+j` rules] THEN *)
(*   ASM_REWRITE_TAC[] THEN                                                       *)
(*   REPEAT CONJ_TAC THEN                                                         *)
(*   TRY(AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC) THEN      *)
(*   TRY(CONV_TAC WORD_RULE).                                                     *)
(*                                                                           *)
(* Then WBN_PREP_TO_END = 8-way case split on r = 1+(nblk-9) MOD 8 (VALIDATED    *)
(* r in 1..8 for nblk>=17); POST combines the shifted band_post (last r stores + *)
(* xi_p tag) with ext2's carried output forall [conjunct 64] and folds the tag   *)
(* caught_up ++ [last r blocks] = full-nblk GHASH via GHASH_ACC_APPEND           *)
(* (common/polyval_ghash.ml:62) -- the one genuinely NEW algebra step.  THEN     *)
(* chain onto WBN_FRONT_TO_PREP_EXT2 by ENSURES_TRANS_SIMPLE (EXISTS_TAC          *)
(* wbn_prepretail_post_ext2).                                                     *)
(* ------------------------------------------------------------------------- *)

(* ========================================================================= *)
(*  -- PHASE 6 STEP 2b: WBN_PREP_TO_END_r landed (r=1).                      *)
(*                                                                           *)
(* The seam post `wbn_prepretail_post_ext2` (the loop/prepretail EXT2 exit    *)
(* at pc+3796) feeds the shifted r-block tail WB_TAIL_GEN2_r by precondition- *)
(* weakening.  WBN_PREP_TO_END_r : ensures arm wbn_prepretail_post_ext2       *)
(* (shifted band_post r) wbn_front_C_tm, under the length hyp                 *)
(*   nblk = 8*((nblk-9) DIV 8 + 1) + r.                                       *)
(*                                                                           *)
(* SOUNDNESS: the r-block tail's own ANTS (NONOVERLAPPING_                    *)
(* TAC over the shifted out_p/xi_p/ivec_p regions) needs 3 disjointness       *)
(* clauses the ext2 wide hyps do NOT carry:                                   *)
(*    nonoverlapping (out_p,16*nblk) (xi_p,16)                                *)
(*    nonoverlapping (out_p,16*nblk) (ivec_p,16)                              *)
(*    nonoverlapping (xi_p,16)       (ivec_p,16)                              *)
(* These ARE genuine whole-function preconditions (the output buffer must be  *)
(* disjoint from the Xi accumulator and the ivec; xi_p disjoint from ivec_p)  *)
(* -- same class as the in_p/out_p gap and the (out_p)(sp,80) gap.  In        *)
(* the real band contract q_at r, xi_p (out_p,16*r) ivec_p at the size-16     *)
(* (=16*nblk when nblk=1) granularity are present; at the whole-length        *)
(* 16*nblk granularity dissect_band 1 shows only xi_p (ivec_p,16) literally,  *)
(* so all 3 are threaded as SIDE-CONDITIONS on WBN_PREP_TO_END_r              *)
(* (the alternative to widening wbn_front_hyps_wide_tm -- lighter, no         *)
(* chain re-prove).  They flow up to the final theorem's precond and are      *)
(* supplied by the guard/subroutine wrapper (the band contract has them).     *)
(* ------------------------------------------------------------------------- *)

(* SPECL order = wb_front_vars minus nblk, 27 terms; splices the OCaml value  *)
(* wbn_caught_up (NOT a backtick literal -- that would introduce a free var). *)
let shift_vals r =
  let rt = mk_small_numeral r in
  let slice = subst [rt, `r_:num`]
                `SUB_LIST (128 * ((nblk - 9) DIV 8 + 1), 16 * r_) (ibytes:byte list)` in
  let xi_shifted = mk_comb(`word_bytereverse:int128->int128`, wbn_caught_up) in
  [ `pc:num`; `stackpointer:int64`;
    `word_add out_p (word (128 * ((nblk - 9) DIV 8 + 1))):int64`;
    `xi_p:int64`; `ivec_p:int64`;
    `word_add in_p (word (128 * ((nblk - 9) DIV 8 + 1))):int64`;
    `key_p:int64`; `htbl_p:int64`;
    slice; xi_shifted;
    `gcm_ctr_add (word (8 * ((nblk - 9) DIV 8 + 1))) ctr0:int128`;
    `k0:int128`;`k1:int128`;`k2:int128`;`k3:int128`;`k4:int128`;`k5:int128`;`k6:int128`;`k7:int128`;
    `k8:int128`;`k9:int128`;`k10:int128`;`k11:int128`;`k12:int128`;`k13:int128`;`k14:int128`;`h:int128`];;

(* the 3 side-condition clauses (whole-length granularity). *)
let wbn_prep_to_end_extra_clauses =
  [`nonoverlapping (out_p:int64,16 * nblk) (xi_p:int64,16)`;
   `nonoverlapping (out_p:int64,16 * nblk) (ivec_p:int64,16)`;
   `nonoverlapping (xi_p:int64,16) (ivec_p:int64,16)`];;

(* NOTE: an earlier scaffold shipped a
   band-post-only seam family (wbn_prep_to_end_goal / WBN_PREP_TO_END_r_TAC /
   WBN_PREP_TO_END_1..8) that reconciled the ext2 seam post to the shifted
   band_post but dropped the first 8*(k+1) output stores.  It was fully
   superseded by the full-post WBN_PREP_TO_END_FULL_r family below (which folds
   those stores back in via ENSURES_ADD_PRESERVED and folds the tag via
   GHASH_ACC_APPEND) and was never consumed; it has been deleted.  Its inner
   ext2-post -> shifted-tail reconciliation lives on verbatim in
   INNER_TAIL_FEED_TAC below. *)

(* ========================================================================= *)
(*  -- PHASE 6 STEP 2b: tag-fold + output-forall algebra.                    *)
(*                                                                           *)
(* The per-r seam feed (INNER_TAIL_FEED_TAC + WB_TAIL_GEN2_r) lands a          *)
(* SHIFTED-band post:                                                          *)
(*   - PC = pc+4528 (whole-function exit)                                     *)
(*   - the LAST r output stores at out_p + 128*(k+1) + 16*i (i<r)             *)
(*   - the tag at xi_p = word_bytereverse (ghash_polyval_acc bh (brev xi)     *)
(*       (MAP brev (list_of_seq cph (8*(k+1)))))  APPENDED with the r new     *)
(*       blocks (double-brev'd running acc + r cph blocks).                    *)
(* They DROP the first 8*(k+1) output stores (the ext2 seam post carries them *)
(* as its conjunct [64] forall).  To get the full-nblk contract we must       *)
(*   (a) carry the ext2 output forall through the r-block tail (its narrow    *)
(*       output frame writes only bytes(out_p+128(k+1),16*r), disjoint from   *)
(*       the first 128*(k+1) bytes -> ENSURES_ADD_PRESERVED, sound), and      *)
(*   (b) fold the tag: caught_up ++ [r new blocks] = list_of_seq cph nblk     *)
(*       via GHASH_ACC_APPEND (the one genuinely NEW algebra step).           *)
(* These helper lemmas do the sim-free list/tag algebra for (b).             *)
(* ------------------------------------------------------------------------- *)

(* list_of_seq splits at any point into a prefix + a shifted suffix. *)
let LIST_OF_SEQ_ADD = prove
 (`!m (f:num->A) n. list_of_seq f (m + n) =
        APPEND (list_of_seq f m) (list_of_seq (\i. f (m + i)) n)`,
  INDUCT_TAC THEN REPEAT GEN_TAC THENL
   [REWRITE_TAC[ADD_CLAUSES; LIST_OF_SEQ; APPEND; ETA_AX];
    REWRITE_TAC[ADD_CLAUSES; LIST_OF_SEQ; APPEND] THEN
    AP_TERM_TAC THEN ASM_REWRITE_TAC[o_DEF]]);;

(* LIST_OF_SEQ_CLAUSES (in the base) only covers n=0..4; the r-block tag fold      *)
(* needs the explicit expansion up to n=8.  Each proved from the SUC recursion     *)
(* (num_CONV on the count down to a CLAUSES-known value, then APPEND).             *)
let LIST_OF_SEQ_CLAUSES_5_8 =
  let expand_los n =
    let suc_convs = map (fun k -> num_CONV (mk_small_numeral k)) (rev (5--n)) in
    prove(mk_forall(`f:num->A`,
       mk_eq(list_mk_comb(`list_of_seq:(num->A)->num->(A)list`,[`f:num->A`; mk_small_numeral n]),
             mk_list(map (fun i -> mk_comb(`f:num->A`, mk_small_numeral i)) (0--(n-1)), `:A`))),
      GEN_TAC THEN
      GEN_REWRITE_TAC TOP_DEPTH_CONV suc_convs THEN
      REWRITE_TAC[list_of_seq] THEN
      CONV_TAC(DEPTH_CONV NUM_SUC_CONV) THEN
      REWRITE_TAC[LIST_OF_SEQ_CLAUSES] THEN REWRITE_TAC[APPEND]) in
  end_itlist CONJ (map expand_los [5;6;7;8]);;

(* fold one gcm_ctr_inc into the running gcm_ctr_add offset (for the r>1 tail    *)
(* stores' inc^i towers in WBN_PREP_TO_END_FULL_r).                             *)
let GCM_CTR_INC_FOLD = prove
 (`!w x. gcm_ctr_inc (gcm_ctr_add w x) = gcm_ctr_add (word_add w (word 1)) x`,
  REWRITE_TAC[GSYM GCM_CTR_ADD_1; GCM_CTR_ADD_COMPOSE]);;

(* nesting: the shifted band's i-th cph block = the global (8*(k+1)+i)-th. *)
let WBN_SUBLIST_SHIFT = prove
 (`!(ibytes:byte list) k i r. i < r
   ==> SUB_LIST (16 * i,16) (SUB_LIST (128 * (k + 1),16 * r) ibytes) =
       SUB_LIST (16 * (8 * (k + 1) + i),16) ibytes`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SUB_LIST_MIN_GENERAL] THEN
  SUBGOAL_THEN `MIN 16 (16 * r - 16 * i) = 16` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `128 * (k + 1) + 16 * i = 16 * (8 * (k + 1) + i)` SUBST1_TAC THENL
   [ARITH_TAC; REFL_TAC]);;

(* ------------------------------------------------------------------------- *)
(* WBN_PREP_TO_END_FULL_r : the seam post fed to the shifted tail, delivering  *)
(* the FULL-nblk output/tag contract (not the r-block band_post).  Post =      *)
(* wbn_end_post: PC=pc+4528, the nblk-uniform output forall (aes13 XOR k14      *)
(* vocabulary, matching the ext2 seam's carried forall), the tag folded to      *)
(* list_of_seq cph nblk via GHASH_ACC_APPEND.                                   *)
(*                                                                             *)
(* Route: FRAME_SUBSUMED (narrow tail out-frame -> wide                         *)
(* wbn_front_C_tm), THEN ENSURES_POSTCONDITION_THM with the intermediate        *)
(*   inter_post_r = \s. (shifted band_post r) s /\ (ext2 first-8(k+1) forall) s  *)
(* splitting into: (1) inter_post_r ==> wbn_end_post [the tag-fold + store       *)
(* re-index math], and (2) ensures ext2post inter_post_r narrow_frame, closed    *)
(* by ENSURES_ADD_PRESERVED [narrow tail leg via INNER_TAIL_FEED_TAC + the       *)
(* first-blocks forall carried by read-over-write through the narrow frame,      *)
(* sound because the tail writes only bytes(out_p+128(k+1),16*r), disjoint       *)
(* from the first 128(k+1) output bytes].                                        *)
(* ------------------------------------------------------------------------- *)

(* the nblk-uniform end post (PC + output forall over nblk + folded tag). *)
let wbn_end_post =
  let end_forall = `forall j. j < nblk
    ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
        word_xor (word_xor (bytes_to_int128 (SUB_LIST (16 * j,16) ibytes))
        (aes13 (gcm_ctr_inc_iter j ctr0) k0 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 k11 k12 k13)) k14` in
  let tag = `read (memory :> bytes128 xi_p) s =
    word_bytereverse (ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
      (MAP word_bytereverse
        (list_of_seq (\k. bytes_to_int128 (SUB_LIST (16 * k,16) ibytes)) nblk)))` in
  (* ivec M2: the whole-buffer counter write-back, spine form
     gcm_ctr_inc_iter nblk ctr0.  FULL_r reconciles the shifted band's
     gcm_ctr_inc_iter r (gcm_ctr_add (word 8(q+1)) ctr0) to this via
     GCM_CTR_INC_ITER_ADD + GCM_CTR_ADD_COMPOSE (8(q+1)+r = nblk). *)
  let ivec = `read (memory :> bytes128 ivec_p) s = gcm_ctr_inc_iter nblk ctr0` in
  mk_abs(`s:armstate`,
    list_mk_conj [`read PC s = word (pc + 4560)`; end_forall; tag; ivec]);;

(* full-post goal for a given r *)
let wbn_prep_to_end_full_goal r =
  let nblk_eq = subst[mk_small_numeral r,`r_:num`]
                  `nblk = 8 * ((nblk - 9) DIV 8 + 1) + r_` in
  let hyps = end_itlist (curry mk_conj)
    (wbn_front_hyps_wide_tm :: nblk_eq :: wbn_prep_to_end_extra_clauses) in
  let ens = list_mk_comb(`ensures arm`,
    [wbn_prepretail_post_ext2; wbn_end_post; wbn_front_C_tm]) in
  list_mk_forall(wb_front_vars, mk_imp(hyps, ens));;

(* the narrow tail out-frame (writes only the last r output blocks) for shift r. *)
let wbn_tail_gen2 r =
  if r=1 then WB_TAIL_GEN2_1 else if r=2 then WB_TAIL_GEN2_2
  else if r=3 then WB_TAIL_GEN2_3 else if r=4 then WB_TAIL_GEN2_4
  else if r=5 then WB_TAIL_GEN2_5 else if r=6 then WB_TAIL_GEN2_6
  else if r=7 then WB_TAIL_GEN2_7 else WB_TAIL_GEN2_8;;
let wbn_narrow_frame r =
  el 3 (snd(strip_comb(snd(dest_imp(concl(SPECL (shift_vals r) (wbn_tail_gen2 r)))))));;

(* INNER_TAIL_FEED_TAC r tail_r: the post-FRAME_SUBSUMED inner half of           *)
(* WBN_PREP_TO_END_r_TAC (PRECONDITION_THM + feed the shifted tail); proves      *)
(* `ensures ext2post (shifted band_post r) narrow_frame` on its own.            *)
let INNER_TAIL_FEED_TAC r tail_r =
  let rt = mk_small_numeral r in
  let m16r = mk_binop `( * ):num->num->num` `16` rt in
  let mnum = mk_small_numeral (16 * r) in
  let sv = shift_vals r in
  let tail = SPECL sv tail_r in
  let _,targs = strip_comb (snd(dest_imp(concl tail))) in
  let tail_pre = el 1 targs in
  let slice_close =
    MP_TAC(SPECL [`nblk:num`;`in_p:int64`;`ibytes:byte list`;`q:num`;mnum;`x:armstate`]
             WBN_INPUT_SLICE_GEN) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      REWRITE_TAC[ARITH_RULE(mk_eq(m16r,mnum))] THEN DISCH_THEN ACCEPT_TAC] in
  let counter_close =
    REPLICATE_TAC 14 AP_THM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    CONV_TAC WORD_RULE in
  (* ivec M2: with the Q30 conjunct now carried in wbn_weak_q_at6 r,
     the shifted tail precond demands read Q30 = gcm_ctr_raw (word 8)
     (gcm_ctr_add (word (8*(q+1))) ctr0); the M1 seam (ext2post, ASM_REWRITE'd in
     above) gives gcm_ctr_raw (word (8*q+16)) ctr0.  Absorb the prior add into the
     counter offset via GCM_CTR_RAW_ABSORB_NUM (8*(q+1)+8 = 8*q+16). *)
  let q30_close =
    GEN_REWRITE_TAC RAND_CONV [GCM_CTR_RAW_ABSORB_NUM] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC in
  MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN EXISTS_TAC tail_pre THEN
  CONJ_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[WORD_BYTEREVERSE_BYTEREVERSE] THEN
    ABBREV_TAC `q = (nblk - 9) DIV 8` THEN
    SUBGOAL_THEN (subst[rt,`r_:num`] `16 * nblk = 128 * (q + 1) + 16 * r_`)
      ASSUME_TAC THENL
     [UNDISCH_TAC (subst[rt,`r_:num`] `nblk = 8 * (q + 1) + r_`) THEN ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[GSYM GCM_CTR_ADD_1; GCM_CTR_ADD_COMPOSE] THEN
    MP_TAC(SPECL [`nblk:num`;`in_p:int64`;`ibytes:byte list`;`q:num`;m16r;`x:armstate`]
      WBN_INPUT_SLICE_GEN) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      DISCH_THEN(fun th -> REWRITE_TAC[th])] THEN
    REWRITE_TAC[SUB_LIST_MIN_RIGHT; ARITH_RULE(subst[rt,`r_:num`] `MIN 16 (16 * r_) = 16`);
                ARITH_RULE `16 * 8 * (q + 1) = 128 * (q + 1)`] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN (subst[rt,`r_:num`]
      `word_sub (word_add in_p (word (128 * (q + 1) + 16 * r_)))
                (word_add in_p (word (128 * (q + 1)))):int64 = word (16 * r_)`)
      SUBST_ALL_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    REPEAT CONJ_TAC THEN
    FIRST [REFL_TAC; CONV_TAC WORD_RULE; counter_close; slice_close; q30_close];
    MP_TAC tail THEN ANTS_TAC THENL
     [CONJ_TAC THENL
        [REWRITE_TAC[LENGTH_SUB_LIST] THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
         ALL_TAC] THEN
      REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE NONOVERLAPPING_TAC);
      DISCH_THEN ACCEPT_TAC]];;

(* r=1 full-post: validated end-to-end interactively.               *)
let WBN_PREP_TO_END_FULL_1 = prove(wbn_prep_to_end_full_goal 1,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN
  EXISTS_TAC (wbn_narrow_frame 1) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN SUBSUMED_MAYCHANGE_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN
  EXISTS_TAC (mk_abs(`s:armstate`,
    mk_conj(snd(dest_abs(el 2 (snd(strip_comb(snd(dest_imp(concl(SPECL (shift_vals 1) WB_TAIL_GEN2_1)))))))),
            el 64 (conjuncts (snd(dest_abs wbn_prepretail_post_ext2)))))) THEN
  CONJ_TAC THENL
   [X_GEN_TAC `s:armstate` THEN REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN ABBREV_TAC `q = (nblk - 9) DIV 8` THEN
    CONJ_TAC THENL
     [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
      ASM_CASES_TAC `j < 8 * (q + 1)` THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN FIRST_X_ASSUM ACCEPT_TAC;
        SUBGOAL_THEN `j = 8 * (q + 1)` SUBST_ALL_TAC THENL
         [ASM_ARITH_TAC; ALL_TAC] THEN
        REWRITE_TAC[ARITH_RULE `16 * 8 * (q + 1) = 128 * (q + 1)`; GCM_CTR_INC_ITER_ADD] THEN
        FIRST_X_ASSUM(fun th -> if is_eq(concl th) &&
          (match lhs(concl th) with Comb(Comb(Const("read",_),_),_) ->
             (can (find_term (fun t -> t = `aes256_encrypt`)) (concl th)) | _ -> false)
          then SUBST1_TAC th else NO_TAC) THEN
        SUBGOAL_THEN `SUB_LIST (0,16) (SUB_LIST (128 * (q + 1),16 * 1) (ibytes:byte list)) =
                      SUB_LIST (128 * (q + 1),16) ibytes` SUBST1_TAC THENL
         [REWRITE_TAC[SUB_LIST_MIN_RIGHT] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
          AP_TERM_TAC THEN ARITH_TAC; ALL_TAC] THEN
        GEN_REWRITE_TAC LAND_CONV [GSYM AES256_XOR_ENCRYPT_RECONSTRUCT] THEN
        CONV_TAC WORD_RULE];
      CONJ_TAC THENL
       [REWRITE_TAC[WORD_BYTEREVERSE_BYTEREVERSE] THEN AP_TERM_TAC THEN
        SUBGOAL_THEN
          `list_of_seq (\k. bytes_to_int128 (SUB_LIST (16 * k,16) (ibytes:byte list))) nblk =
           list_of_seq (\k. bytes_to_int128 (SUB_LIST (16 * k,16) ibytes)) (8 * (q + 1) + 1)`
          SUBST1_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        REWRITE_TAC[LIST_OF_SEQ_ADD; MAP_APPEND; GHASH_ACC_APPEND] THEN AP_TERM_TAC THEN
        REWRITE_TAC[LIST_OF_SEQ_CLAUSES; MAP; MULT_CLAUSES; ADD_CLAUSES] THEN
        REWRITE_TAC[SUB_LIST_MIN_RIGHT; ARITH_RULE `MIN 16 16 = 16`;
                    ARITH_RULE `16 * 8 * (q + 1) = 128 * (q + 1)`];
        (* ivec M2: shifted band ivec = gcm_ctr_inc_iter 1
           (gcm_ctr_add (word (8*(q+1))) ctr0); reconcile to gcm_ctr_inc_iter nblk
           ctr0 via ITER_ADD + ADD_COMPOSE + nblk = 8*(q+1)+1. *)
        REWRITE_TAC[GCM_CTR_INC_ITER_ADD; GCM_CTR_ADD_COMPOSE] THEN
        AP_THM_TAC THEN AP_TERM_TAC THEN
        REWRITE_TAC[GSYM WORD_ADD] THEN AP_TERM_TAC THEN ASM_ARITH_TAC]];
    MATCH_MP_TAC ENSURES_ADD_PRESERVED THEN CONJ_TAC THENL
     [INNER_TAIL_FEED_TAC 1 WB_TAIL_GEN2_1;
      REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; MAYCHANGE; SEQ_ID] THEN
      REWRITE_TAC[GSYM SEQ_ASSOC] THEN PURE_REWRITE_TAC[ASSIGNS_SEQ] THEN
      CONV_TAC(REDEPTH_CONV BETA_CONV) THEN REWRITE_TAC[ASSIGNS_THM] THEN
      CONV_TAC(REDEPTH_CONV BETA_CONV) THEN REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
      REPEAT GEN_TAC THEN STRIP_TAC THEN
      X_GEN_TAC `j:num` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_eq(concl th) &&
        (match rhs(concl th) with Var("s'",_) -> true | _ -> false))) THEN
      SUBGOAL_THEN `nonoverlapping (word_add out_p (word (16 * j)):int64,16)
         (word_add out_p (word (128 * ((nblk - 9) DIV 8 + 1))),16)` ASSUME_TAC THENL
       [NONOVERLAPPING_TAC; ALL_TAC] THEN
      WBN_PUSH_LHS_READ_TAC THEN
      FIRST_ASSUM(fun th -> if is_forall(concl th) then MATCH_MP_TAC th else NO_TAC) THEN
      FIRST_X_ASSUM ACCEPT_TAC]]);;

(* ------------------------------------------------------------------------- *)
(*  -- r>1 generalization of WBN_PREP_TO_END_FULL_1, MECHANIZED.               *)
(*                                                                             *)
(* WBN_PREP_TO_END_FULL_r for r=2..8 has the IDENTICAL skeleton as FULL_1;     *)
(* the r-dependent hand-parts are packaged as OCaml `int -> tactic` closures   *)
(* below and driven by WBN_PREP_TO_END_FULL_r_TAC.  Validated r=2..8 hyps=0.   *)
(*                                                                             *)
(* KEY per-block algebra: for output block j = 8*(q+1)+i (0<=i<r), the         *)
(* seam-carried full-post value equals the r-block band store.  block_bridge   *)
(* proves that value identity STANDALONE (goal-form word_xor(word_xor cph      *)
(* aes13)k14 = store-form word_xor cph (aes256_encrypt ...)), reconciling:     *)
(*   - counter: gcm_ctr_inc_iter(8(q+1)+i) = gcm_ctr_add(word(8(q+1)+i)) =     *)
(*              gcm_ctr_inc^i (gcm_ctr_add(word 8(q+1)))  [GCM_CTR_INC_FOLD]    *)
(*   - cph slice: SUB_LIST(16*(8(q+1)+i),16) ibytes =                          *)
(*              SUB_LIST(16*i,16)(SUB_LIST(128(q+1),16*r) ibytes) [WBN_SUBLIST_SHIFT] *)
(*   - AES: GSYM AES256_XOR_ENCRYPT_RECONSTRUCT + WORD_RULE (XOR reassoc).     *)
(* block_close then reduces 16*i -> numeral (ARITH mul_red -- else the goal's  *)
(* SUB_LIST(16*i,..)/word(16*i) won't match the store's SUB_LIST(<16i>,..)/    *)
(* word <16i>) and reconciles the store address (i=0 flat, i>=1 nested).       *)
(* tag_fold folds the r-element explicit tag list to list_of_seq via           *)
(* LIST_OF_SEQ_ADD/GHASH_ACC_APPEND, closing each element by WBN_SUBLIST_SHIFT. *)
(* ------------------------------------------------------------------------- *)

(* the goal-side and store-side counter for output block i (0<=i<r). *)
let wbn_full_goal_ctr i =
  subst[mk_small_numeral i,`i_:num`]
    `gcm_ctr_add (word (8 * (q + 1) + i_)) ctr0 :int128`;;
let wbn_full_store_ctr i =
  funpow i (fun t -> mk_comb(`gcm_ctr_inc:int128->int128`, t))
    `gcm_ctr_add (word (8 * (q + 1))) ctr0 :int128`;;
(* the goal-side and store-side output addresses for block i. *)
let wbn_full_goal_addr i =
  subst[mk_small_numeral i,`i_:num`]
    `word_add out_p (word (16 * (8 * (q + 1) + i_))):int64`;;
let wbn_full_store_addr i =
  if i = 0 then `word_add out_p (word (128 * (q + 1))):int64`
  else mk_comb(mk_comb(`word_add:int64->int64->int64`,
                       `word_add out_p (word (128 * (q + 1))):int64`),
               mk_comb(`word:num->int64`, mk_small_numeral(16 * i)));;

(* the standalone per-block value bridge goal + tactic. *)
let wbn_block_bridge_goal r i =
  let it = mk_small_numeral i and rt = mk_small_numeral r in
  let gcph = subst[it,`i_:num`]
    `bytes_to_int128 (SUB_LIST (16 * (8 * (q + 1) + i_),16) (ibytes:byte list))` in
  let gval = list_mk_comb(`word_xor:int128->int128->int128`,
    [list_mk_comb(`word_xor:int128->int128->int128`,
       [gcph; list_mk_comb(`aes13`,[wbn_full_goal_ctr i;
          `k0:int128`;`k1:int128`;`k2:int128`;`k3:int128`;`k4:int128`;`k5:int128`;`k6:int128`;
          `k7:int128`;`k8:int128`;`k9:int128`;`k10:int128`;`k11:int128`;`k12:int128`;`k13:int128`])]);
     `k14:int128`]) in
  let scph = subst[it,`i_:num`;rt,`r_:num`]
    `bytes_to_int128 (SUB_LIST (16 * i_,16) (SUB_LIST (128 * (q + 1),16 * r_) (ibytes:byte list)))` in
  let sval = list_mk_comb(`word_xor:int128->int128->int128`,
    [scph; list_mk_comb(`aes256_encrypt`,
       [wbn_full_store_ctr i;
        `[k0;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14]:(int128)list`])]) in
  mk_forall(`q:num`, mk_imp(subst[it,`i_:num`;rt,`r_:num`] `i_ < r_`, mk_eq(gval,sval)));;

let wbn_block_bridge_tac r i =
  let it = mk_small_numeral i and rt = mk_small_numeral r in
  let sublist_inst = SPECL [`ibytes:byte list`;`q:num`;it;rt] WBN_SUBLIST_SHIFT in
  let ctr_eq = mk_eq(wbn_full_goal_ctr i, wbn_full_store_ctr i) in
  GEN_TAC THEN DISCH_TAC THEN
  (MP_TAC sublist_inst THEN ANTS_TAC THENL [ARITH_TAC; DISCH_THEN(SUBST1_TAC o SYM)]) THEN
  SUBGOAL_THEN ctr_eq SUBST1_TAC THENL
   [REWRITE_TAC[GCM_CTR_INC_FOLD] THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM AES256_XOR_ENCRYPT_RECONSTRUCT] THEN CONV_TAC WORD_RULE;;

(* close one output block j = 8*(q+1)+i in the case-2 forall of FULL_r. *)
let wbn_block_close_tac r i =
  let brg = SPEC `q:num` (prove(wbn_block_bridge_goal r i, wbn_block_bridge_tac r i)) in
  let it = mk_small_numeral i in
  let mul_red = ARITH_RULE (mk_eq(mk_binop `( * ):num->num->num` `16` it,
                                  mk_small_numeral(16 * i))) in
  let common = REWRITE_TAC[GCM_CTR_INC_ITER_ADD] THEN
    MP_TAC brg THEN (ANTS_TAC THENL [ARITH_TAC; ALL_TAC]) THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[mul_red] in
  if i = 0 then
    common THEN
    REWRITE_TAC[ARITH_RULE `16 * 8 * (q + 1) = 128 * (q + 1)`; MULT_CLAUSES; ADD_CLAUSES] THEN
    ASM_REWRITE_TAC[]
  else
    let addr_eq = mk_eq(wbn_full_goal_addr i, wbn_full_store_addr i) in
    let addr_arith = subst[it,`i_:num`]
      `16 * (8 * (q + 1) + i_) = 128 * (q + 1) + 16 * i_` in
    common THEN
    SUBGOAL_THEN addr_eq SUBST1_TAC THENL
     [REWRITE_TAC[ARITH_RULE addr_arith; mul_red] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
    FIRST_X_ASSUM ACCEPT_TAC;;

(* (A) the case-2 output forall for shift r. *)
let wbn_case2_forall_tac r =
  let one_block i =
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> match concl th with
      Comb(Comb(Const("=",_),Var("j",_)),_) -> true | _ -> false)) THEN
    wbn_block_close_tac r i in
  let disj = end_itlist (fun a b -> mk_disj(a,b))
    (map (fun i -> subst[mk_small_numeral i,`i_:num`] `j = 8 * (q + 1) + i_`) (0--(r-1))) in
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN ASM_CASES_TAC `j < 8 * (q + 1)` THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN FIRST_X_ASSUM ACCEPT_TAC;
    SUBGOAL_THEN disj STRIP_ASSUME_TAC THENL
     ((UNDISCH_TAC (subst[mk_small_numeral r,`r_:num`] `nblk = 8 * (q + 1) + r_`) THEN
       UNDISCH_TAC `~(j < 8 * (q + 1))` THEN UNDISCH_TAC `j < nblk` THEN ARITH_TAC) ::
      map one_block (0--(r-1)))];;

(* (B) the tag fold: r-element explicit tag list -> list_of_seq cph nblk. *)
let wbn_tag_elt_close r i =
  let mul_red = ARITH_RULE (mk_eq(mk_binop `( * ):num->num->num` `16` (mk_small_numeral i),
                                  mk_small_numeral(16 * i))) in
  MP_TAC(REWRITE_RULE[mul_red; MULT_CLAUSES]
           (SPECL [`ibytes:byte list`;`q:num`;mk_small_numeral i;mk_small_numeral r]
              WBN_SUBLIST_SHIFT)) THEN
  ANTS_TAC THENL [ARITH_TAC; DISCH_THEN MATCH_ACCEPT_TAC];;
let wbn_tag_fold_tac r =
  let rt = mk_small_numeral r in
  AP_TERM_TAC THEN
  SUBGOAL_THEN (subst[rt,`r_:num`]
     `list_of_seq (\k. bytes_to_int128 (SUB_LIST (16 * k,16) (ibytes:byte list))) nblk =
      list_of_seq (\k. bytes_to_int128 (SUB_LIST (16 * k,16) ibytes)) (8 * (q + 1) + r_)`)
    SUBST1_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[LIST_OF_SEQ_ADD; MAP_APPEND; GHASH_ACC_APPEND] THEN
  REWRITE_TAC[WORD_BYTEREVERSE_BYTEREVERSE] THEN AP_TERM_TAC THEN
  REWRITE_TAC[LIST_OF_SEQ_CLAUSES; LIST_OF_SEQ_CLAUSES_5_8; MAP; o_DEF] THEN
  REWRITE_TAC[CONS_11] THEN
  (if r = 1 then ALL_TAC else REPEAT CONJ_TAC) THEN
  FIRST (map (fun i -> AP_TERM_TAC THEN AP_TERM_TAC THEN wbn_tag_elt_close r i) (0--(r-1)));;

(* the full FULL_r tactic (r>=1): FRAME_SUBSUMED -> POSTCONDITION_THM with        *)
(* intermediate (shifted band_post /\ ext2 first-8(k+1) forall), split into        *)
(* [ (A) case-2 forall + (B) tag fold ] and [ ADD_PRESERVED: INNER_TAIL_FEED +     *)
(* carry the forall through the narrow tail writes ].                              *)
(* the intermediate post: shifted band_post r (of the SPECL'd tail) conjoined     *)
(* with the ext2 seam's first-8(k+1)-out-blocks forall (conjunct 64).             *)
let wbn_full_inter_post r =
  let band_post_r =
    el 2 (snd(strip_comb(snd(dest_imp(concl(SPECL (shift_vals r) (wbn_tail_gen2 r))))))) in
  mk_abs(`s:armstate`,
    mk_conj(snd(dest_abs band_post_r),
            el 64 (conjuncts (snd(dest_abs wbn_prepretail_post_ext2)))));;
let WBN_PREP_TO_END_FULL_r_TAC r =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN EXISTS_TAC (wbn_narrow_frame r) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN SUBSUMED_MAYCHANGE_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN
  EXISTS_TAC (wbn_full_inter_post r) THEN
  CONJ_TAC THENL
   [X_GEN_TAC `s:armstate` THEN REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN ABBREV_TAC `q = (nblk - 9) DIV 8` THEN
    CONJ_TAC THENL
     [wbn_case2_forall_tac r;
      CONJ_TAC THENL
       [wbn_tag_fold_tac r;
        (* ivec M2: shifted band ivec = gcm_ctr_inc_iter r
           (gcm_ctr_add (word (8*(q+1))) ctr0) -> gcm_ctr_inc_iter nblk ctr0
           via ITER_ADD + ADD_COMPOSE + nblk = 8*(q+1)+r. *)
        REWRITE_TAC[GCM_CTR_INC_ITER_ADD; GCM_CTR_ADD_COMPOSE] THEN
        AP_THM_TAC THEN AP_TERM_TAC THEN
        REWRITE_TAC[GSYM WORD_ADD] THEN AP_TERM_TAC THEN ASM_ARITH_TAC]];
    MATCH_MP_TAC ENSURES_ADD_PRESERVED THEN CONJ_TAC THENL
     [INNER_TAIL_FEED_TAC r (wbn_tail_gen2 r);
      REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; MAYCHANGE; SEQ_ID] THEN
      REWRITE_TAC[GSYM SEQ_ASSOC] THEN PURE_REWRITE_TAC[ASSIGNS_SEQ] THEN
      CONV_TAC(REDEPTH_CONV BETA_CONV) THEN REWRITE_TAC[ASSIGNS_THM] THEN
      CONV_TAC(REDEPTH_CONV BETA_CONV) THEN REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
      REPEAT GEN_TAC THEN STRIP_TAC THEN
      X_GEN_TAC `j:num` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_eq(concl th) &&
        (match rhs(concl th) with Var("s'",_) -> true | _ -> false))) THEN
      SUBGOAL_THEN (subst[mk_small_numeral r,`r_:num`]
        `nonoverlapping (word_add out_p (word (16 * j)):int64,16)
         (word_add out_p (word (128 * ((nblk - 9) DIV 8 + 1))),16 * r_)`) ASSUME_TAC THENL
       [NONOVERLAPPING_TAC; ALL_TAC] THEN
      WBN_PUSH_LHS_READ_TAC THEN
      FIRST_ASSUM(fun th -> if is_forall(concl th) then MATCH_MP_TAC th else NO_TAC) THEN
      FIRST_X_ASSUM ACCEPT_TAC]];;

(* ------------------------------------------------------------------------- *)
(* SPEED refactor: the r=2..8 suffix sim is BAND-AGNOSTIC                      *)
(* (WBN_PREP_TO_END_FULL_r_TAC uses no `17<=nblk`/`9<=nblk` literal and no      *)
(* band-specific lemma; it only ABBREVs q=(nblk-9)DIV 8 symbolically).  The    *)
(* two consumer families (FULL_r on `17<=nblk`, FULL_916_r on `9<=nblk/\       *)
(* nblk<=16`) therefore ran the SAME ~49s sim TWICE (14 sims total).  Prove it *)
(* ONCE on the strictly-weaker UNIFIED band `9<=nblk` (WBN_PREP_TO_END_FREE_r), *)
(* then derive both consumers by pure hyp-strengthening (statement bit-        *)
(* identical, so the dispatchers wbn_full_thm/wbn_full_916_thm are untouched).  *)
(* Mirrors WBN_PREPRETAIL_EXT2_916 (:below) and the GEN2 dedup.                 *)
(* Saves 7 sims (~343s).  ens is byte-identical across all three bands (only    *)
(* the front-hyps band conjunct differs), so MATCH_MP_TAC + ASM_ARITH closes.   *)
(* ------------------------------------------------------------------------- *)

(* wide front-hyps with the band conjunct `17<=nblk` weakened to `9<=nblk`. *)
let wbn_front_hyps_free_tm =
  let rec repl t = match t with
    | Comb(Comb(Const("/\\",_),a),b) -> mk_conj(repl a, repl b)
    | _ -> if t = `17 <= nblk` then `9 <= nblk` else t in
  repl wbn_front_hyps_wide_tm;;

(* the unified band-free (9<=nblk) full-post goal for a given r. *)
let wbn_prep_to_end_full_free_goal r =
  let nblk_eq = subst[mk_small_numeral r,`r_:num`]
                  `nblk = 8 * ((nblk - 9) DIV 8 + 1) + r_` in
  let hyps = end_itlist (curry mk_conj)
    (wbn_front_hyps_free_tm :: nblk_eq :: wbn_prep_to_end_extra_clauses) in
  let ens = list_mk_comb(`ensures arm`,
    [wbn_prepretail_post_ext2; wbn_end_post; wbn_front_C_tm]) in
  list_mk_forall(wb_front_vars, mk_imp(hyps, ens));;

(* r=2..8 on the unified 9<=nblk band -- the SINGLE sim per r (~49s each). *)
let WBN_PREP_TO_END_FREE_2 = prove(wbn_prep_to_end_full_free_goal 2, WBN_PREP_TO_END_FULL_r_TAC 2);;
let WBN_PREP_TO_END_FREE_3 = prove(wbn_prep_to_end_full_free_goal 3, WBN_PREP_TO_END_FULL_r_TAC 3);;
let WBN_PREP_TO_END_FREE_4 = prove(wbn_prep_to_end_full_free_goal 4, WBN_PREP_TO_END_FULL_r_TAC 4);;
let WBN_PREP_TO_END_FREE_5 = prove(wbn_prep_to_end_full_free_goal 5, WBN_PREP_TO_END_FULL_r_TAC 5);;
let WBN_PREP_TO_END_FREE_6 = prove(wbn_prep_to_end_full_free_goal 6, WBN_PREP_TO_END_FULL_r_TAC 6);;
let WBN_PREP_TO_END_FREE_7 = prove(wbn_prep_to_end_full_free_goal 7, WBN_PREP_TO_END_FULL_r_TAC 7);;
let WBN_PREP_TO_END_FREE_8 = prove(wbn_prep_to_end_full_free_goal 8, WBN_PREP_TO_END_FULL_r_TAC 8);;
(* --- Gc.compact after the 7 FREE suffix sims (this region's heavy sim cluster,
       now the sole copy of what used to run 14x); mirrors the file's post-sim
       compaction idiom (see the Gc.compact lines above). --- *)
Gc.compact();;

(* derive a banded consumer (wide OR 916) from the unified FREE_r by dropping the
   band down to 9<=nblk: MATCH_MP_TAC on the byte-identical ens, ASM_REWRITE the
   shared clauses, ASM_ARITH the band.  <0.1s, hyps=0.  Same idiom as
   WBN_PREPRETAIL_EXT2_916 below. *)
let wbn_prep_to_end_full_derive_tac free_thm =
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC free_thm THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;;

(* r=2..8 full-post legs, DERIVED from the unified FREE_r (no re-sim).
   r=1 is FULL_1 above.  Statement bit-identical. *)
let WBN_PREP_TO_END_FULL_2 = prove(wbn_prep_to_end_full_goal 2, wbn_prep_to_end_full_derive_tac WBN_PREP_TO_END_FREE_2);;
let WBN_PREP_TO_END_FULL_3 = prove(wbn_prep_to_end_full_goal 3, wbn_prep_to_end_full_derive_tac WBN_PREP_TO_END_FREE_3);;
let WBN_PREP_TO_END_FULL_4 = prove(wbn_prep_to_end_full_goal 4, wbn_prep_to_end_full_derive_tac WBN_PREP_TO_END_FREE_4);;
let WBN_PREP_TO_END_FULL_5 = prove(wbn_prep_to_end_full_goal 5, wbn_prep_to_end_full_derive_tac WBN_PREP_TO_END_FREE_5);;
let WBN_PREP_TO_END_FULL_6 = prove(wbn_prep_to_end_full_goal 6, wbn_prep_to_end_full_derive_tac WBN_PREP_TO_END_FREE_6);;
let WBN_PREP_TO_END_FULL_7 = prove(wbn_prep_to_end_full_goal 7, wbn_prep_to_end_full_derive_tac WBN_PREP_TO_END_FREE_7);;
let WBN_PREP_TO_END_FULL_8 = prove(wbn_prep_to_end_full_goal 8, wbn_prep_to_end_full_derive_tac WBN_PREP_TO_END_FREE_8);;

(* ------------------------------------------------------------------------- *)
(* WBN_PREP_TO_END: the 8-way case split on r = 1+(nblk-9) MOD 8.               *)
(* From the ext2 seam post to the full nblk-uniform wbn_end_post, under         *)
(* 9 <= nblk + the 3 side-conditions.  Each residue rr in {0..7} dispatches to   *)
(* WBN_PREP_TO_END_FULL_(rr+1); the per-branch length hyp                        *)
(* nblk = 8*((nblk-9)DIV 8 + 1) + (rr+1) follows by ARITH from the DIVISION      *)
(* identity + 9 <= nblk.                                                         *)
(* ------------------------------------------------------------------------- *)

let wbn_full_thm = Array.of_list
  [WBN_PREP_TO_END_FULL_1;  (* index 0 unused-ish; use r directly 1..8 *)
   WBN_PREP_TO_END_FULL_1; WBN_PREP_TO_END_FULL_2; WBN_PREP_TO_END_FULL_3;
   WBN_PREP_TO_END_FULL_4; WBN_PREP_TO_END_FULL_5; WBN_PREP_TO_END_FULL_6;
   WBN_PREP_TO_END_FULL_7; WBN_PREP_TO_END_FULL_8];;

let wbn_prep_to_end_goal_final =
  let hyps = end_itlist (curry mk_conj)
    (wbn_front_hyps_wide_tm :: `9 <= nblk` :: wbn_prep_to_end_extra_clauses) in
  let ens = list_mk_comb(`ensures arm`,
    [wbn_prepretail_post_ext2; wbn_end_post; wbn_front_C_tm]) in
  list_mk_forall(wb_front_vars, mk_imp(hyps, ens));;

let WBN_PREP_TO_END = prove(wbn_prep_to_end_goal_final,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `nblk - 9` (MATCH_MP DIVISION (ARITH_RULE `~(8 = 0)`))) THEN
  ABBREV_TAC `rr = (nblk - 9) MOD 8` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(fun th -> if concl th = `rr < 8` then MP_TAC th else NO_TAC) THEN
  REWRITE_TAC[ARITH_RULE
    `rr < 8 <=> rr = 0 \/ rr = 1 \/ rr = 2 \/ rr = 3 \/
                rr = 4 \/ rr = 5 \/ rr = 6 \/ rr = 7`] THEN
  STRIP_TAC THEN
  FIRST (map (fun r ->
    MATCH_MP_TAC wbn_full_thm.(r) THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `nblk - 9 = (nblk - 9) DIV 8 * 8 + rr` THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `9 <= nblk` THEN ARITH_TAC) (1--8)));;

(* ------------------------------------------------------------------------- *)
(* WBN_FRONT_TO_END: the full nblk>8 (nblk>=17) front->exit                     *)
(* chain, pc+0x20 -> pc+4528.  WBN_FRONT_TO_PREP_EXT2 ; WBN_PREP_TO_END via     *)
(* ENSURES_TRANS_SIMPLE (both share frame wbn_front_C_tm, and the seam post      *)
(* wbn_prepretail_post_ext2 is aconv between them).  Precond = wbn_front_P_tm    *)
(* (the PC-free front core), post = wbn_end_post (nblk-uniform output forall +   *)
(* GHASH_ACC_APPEND-folded tag over list_of_seq cph nblk).  The 3 side-conds     *)
(* ride the antecedent outward (WBN_PREP_TO_END needs them; the front leg does   *)
(* not); 9<=nblk from 17<=nblk by ARITH.  hyps=0, no new CHEAT (the 2 scoped     *)
(* Q19/Q16 identity CHEATs remain buried in the loop body + prepretail).        *)
(* ------------------------------------------------------------------------- *)

let wbn_front_to_end_goal =
  let hyps = end_itlist (curry mk_conj)
    (wbn_front_hyps_wide_tm :: wbn_prep_to_end_extra_clauses) in
  let ens = list_mk_comb(`ensures arm`,
    [wbn_front_P_tm; wbn_end_post; wbn_front_C_tm]) in
  list_mk_forall(wb_front_vars, mk_imp(hyps, ens));;

let WBN_FRONT_TO_END = prove(wbn_front_to_end_goal,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC ENSURES_TRANS_SIMPLE THEN
  EXISTS_TAC wbn_prepretail_post_ext2 THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN MAYCHANGE_IDEMPOT_TAC;
    MATCH_MP_TAC WBN_FRONT_TO_PREP_EXT2 THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC WBN_PREP_TO_END THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `17 <= nblk` THEN ARITH_TAC]);;

(* ========================================================================= *)
(*  -- the nblk 9..16 leg (the loop is NEVER entered).                        *)
(*                                                                           *)
(* For 9 <= nblk <= 16: q = (nblk-9) DIV 8 = 0, and d = 128*((nblk-1) DIV 8) *)
(* = 128 (CONSTANT, since (nblk-1) DIV 8 = 1 across 9..16).  So at the loop- *)
(* skip branch 0x49c (b.ge 0x9f0) we have X0 = in_p+128 == X5 = in_p+128, so *)
(* the b.ge is TAKEN -> control goes STRAIGHT to prepretail 0x9f0; the main   *)
(* loop body is never executed.  (For nblk>=17, d>=256 so X0<X5 and the b.ge  *)
(* falls through into the loop head 0x4a0 -- that is WBN_FRONT_TO_END's path.) *)
(*                                                                           *)
(* The 9..16 leg is therefore a pure straight-line chain:                     *)
(*   FRONT (0x20 -> 0x9f0, b.ge@0x49c TAKEN)  [WBN_FRONT_TO_PREP_916]          *)
(*   ; PREPRETAIL (0x9f0 -> pc+3796, k:=0)    [WBN_PREPRETAIL_EXT2_916]        *)
(*   ; PREP_TO_END (pc+3796 -> pc+4528)       [WBN_PREP_TO_END_916]            *)
(* The FRONT and PREPRETAIL sims are the SAME code as the >=17 versions, only  *)
(* the hyp band (17<=nblk -> 9<=nblk /\ nblk<=16) and the 0x49c branch         *)
(* resolution differ; every register/memory read is IDENTICAL (the branch     *)
(* only changes PC).  PREP_TO_END is symbolic in q (covers q=0).              *)
(* ------------------------------------------------------------------------- *)

(* the 9..16 hyp band: wbn_front_hyps_wide_tm with 17<=nblk -> 9<=nblk/\nblk<=16 *)
let wbn_front_hyps_916_tm =
  let rec repl t = match t with
    | Comb(Comb(Const("/\\",_),a),b) -> mk_conj(repl a, repl b)
    | _ -> if t = `17 <= nblk` then `9 <= nblk /\ nblk <= 16` else t in
  repl wbn_front_hyps_wide_tm;;

(* (nblk-1) DIV 8 = 1 for 9..16  ->  the loop-skip pointer d = 128*1 = 128. *)
let DIV8_916 = prove
 (`!nblk. 9 <= nblk /\ nblk <= 16 ==> (nblk - 1) DIV 8 = 1`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL[`nblk - 1`;`8`] DIVISION) THEN ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  ASM_ARITH_TAC);;

(* index bound for the first-tail-block lane, 9<= variant (8*k+8 < nblk, k=0 here).
   NOTE: hoisted up next to WBN_Q9_INDEX_LT (~line 3332) because the
   unified prepretail sim WBN_PREPRETAIL_EXT2_UNIFIED now consumes it. *)

(* 0x42c b.ge (loop-entry test, X0=in_p<X5): FALLS THROUGH for 9..16 too. *)
let WB_LOOPENTER_FLAGS_916 = prove
 (`!(in_p:int64) nblk. 9 <= nblk /\ nblk <= 16 /\ 128 * nblk < 2 EXP 62 /\
        val in_p + 16 * nblk < 2 EXP 63
    ==> (ival (word_sub in_p (word_add (word (128 * (nblk - 1) DIV 8)) in_p)) < &0 <=> T) /\
        (ival in_p - ival (word_add (word (128 * (nblk - 1) DIV 8)) in_p) =
         ival (word_sub in_p (word_add (word (128 * (nblk - 1) DIV 8)) in_p)) <=> T)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `nblk:num` DIV8_916) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[MULT_CLAUSES] THEN
  ABBREV_TAC `d = 128` THEN
  SUBGOAL_THEN `1 <= d /\ d <= 16 * nblk /\ d <= 2 EXP 63` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "d" THEN MP_TAC(ASSUME `9 <= nblk`) THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[WORD_RULE `word_sub p (word_add (word d) p):int64 = word_neg (word d)`] THEN
  ASM_SIMP_TAC[IVAL_NEG_SMALL] THEN
  SUBGOAL_THEN `word_add (word d) in_p:int64 = word_add in_p (word d)` SUBST1_TAC THENL
   [CONV_TAC WORD_RULE; ALL_TAC] THEN
  SUBGOAL_THEN `ival (word_add in_p (word d):int64) = &(val in_p + d)` SUBST1_TAC THENL
   [MATCH_MP_TAC IVAL_PTR_ADD THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `ival (in_p:int64) = &(val in_p)` SUBST1_TAC THENL
   [MATCH_MP_TAC IVAL_SMALL_PTR THEN ASM_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[INT_ARITH `--(&d):int < &0 <=> &0:int < &d`; INT_OF_NUM_LT] THEN
    ASM_ARITH_TAC;
    REWRITE_TAC[GSYM INT_OF_NUM_ADD] THEN INT_ARITH_TAC]);;

(* 9..16 versions of the front-prefix arith/lane tactics (NBLK_ARITH_TAC hardcodes
   17<=nblk; these mirror the shape with the 9..16 band). *)
let NBLK_ARITH_916_TAC =
  MP_TAC(ASSUME `9 <= nblk`) THEN MP_TAC(ASSUME `nblk <= 16`) THEN
  MP_TAC(ASSUME `128 * nblk < 2 EXP 62`) THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN ARITH_TAC;;

let WBN_FRONT_PREP_BUF_916_TAC =
  SUBGOAL_THEN `SUB_LIST (0, 16 * nblk) (ibytes:byte list) = ibytes` ASSUME_TAC THENL
   [MATCH_MP_TAC SUB_LIST_LENGTH_IMPLIES THEN ASM_REWRITE_TAC[LE_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN `read (memory :> bytes128 in_p) s0 = bytes_to_int128 (SUB_LIST (0,16) ibytes)` ASSUME_TAC THENL
   [MP_TAC(SPECL [`nblk:num`; `in_p:int64`; `ibytes:byte list`; `s0:armstate`] INPUT_BYTES_TO_BYTE128_LANES) THEN
    ASM_REWRITE_TAC[LE_REFL] THEN DISCH_THEN(MP_TAC o SPEC `0`) THEN
    ANTS_TAC THENL [NBLK_ARITH_916_TAC; ALL_TAC] THEN
    REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]); ALL_TAC] THEN
  SUBGOAL_THEN `word_ushr (word (128 * nblk):int64) 3 = word (16 * nblk)` ASSUME_TAC THENL
   [MATCH_MP_TAC USHR_128NBLK_ANY THEN NBLK_ARITH_916_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `word_and (word_sub (word (16 * nblk)) (word 1)) (word 18446744073709551488):int64 = word (128 * ((nblk - 1) DIV 8))` ASSUME_TAC THENL
   [MATCH_MP_TAC AND_MASK_16NBLK_ANY THEN NBLK_ARITH_916_TAC; ALL_TAC];;

let WBN_LANES_916_TAC =
  SUBGOAL_THEN
   `!k. k < 8 ==> read (memory :> bytes128 (word_add in_p (word (16 * k)))) s0 =
                  bytes_to_int128 (SUB_LIST (16 * k, 16) (ibytes:byte list))`
   MP_TAC THENL
   [MP_TAC(SPECL [`nblk:num`; `in_p:int64`; `ibytes:byte list`; `s0:armstate`]
      INPUT_BYTES_TO_BYTE128_LANES) THEN
    ASM_REWRITE_TAC[LE_REFL] THEN
    DISCH_THEN(fun lth -> X_GEN_TAC `k:num` THEN DISCH_TAC THEN
      MP_TAC(SPEC `k:num` lth) THEN ANTS_TAC THENL
       [MP_TAC(ASSUME `k < 8`) THEN NBLK_ARITH_916_TAC; REWRITE_TAC[]]);
    DISCH_THEN(fun lth ->
      EVERY(map (fun i ->
        ASSUME_TAC(CONV_RULE(DEPTH_CONV NUM_RED_CONV)
          (MP (SPEC (mk_small_numeral i) lth)
              (ARITH_RULE(mk_binop `(<):num->num->bool` (mk_small_numeral i) `8`)))))
        (0--7)))];;

let wbn_init_916_tac =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS] THEN ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WB_MC_LEN]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[C_ARGUMENTS]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_dec]) THEN
  RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV let_CONV)) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o check(is_conj o concl)) THEN
  WBN_FRONT_PREP_BUF_916_TAC;;

(* 0x42c resolve (fall-through) via WB_LOOPENTER_FLAGS_916. *)
let WBN_RESOLVE_42C_916_TAC : tactic =
  MP_TAC(SPECL [`in_p:int64`; `nblk:num`] WB_LOOPENTER_FLAGS_916) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]));;

(* 0x49c resolve (b.ge TAKEN, d=128): substitute (nblk-1)DIV8=1, then WB_PTRCMP_FLAGS
   with a=d=128 collapses 128<128 to F in the assumptions. *)
let WBN_RESOLVE_49C_916_TAC : tactic = fun (asl,w) ->
  (MP_TAC(SPEC `nblk:num` DIV8_916) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
   DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN
                        REWRITE_TAC[th] THEN ASSUME_TAC th) THEN
   MP_TAC(SPECL [`in_p:int64`; `128`; `128`] WB_PTRCMP_FLAGS) THEN
   ANTS_TAC THENL
    [CONJ_TAC THEN MP_TAC(ASSUME `val (in_p:int64) + 16 * nblk < 2 EXP 63`) THEN
     MP_TAC(ASSUME `9 <= nblk`) THEN ARITH_TAC;
     ALL_TAC] THEN
   DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
   RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE `(128 < 128) <=> F`;
                               ARITH_RULE `128 * 1 = 128`])) (asl,w);;

(* the full front-916 sim: prefix IDENTICAL to WBN_FRONT_FULL_TAC to s293, then
   0x4b4 resolved TAKEN, step 294 lands at 0xa10 (the b.ge target, post-.balign16).
   (Dead since the shared-prefix refactor; kept in sync for consistency.) *)
let WBN_FRONT_916_FULL_TAC =
  wbn_init_916_tac THEN WBN_LANES_916_TAC THEN WBN_FRONT_STEP_TAC THEN
  WBN_RESOLVE_42C_916_TAC THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (266--266) THEN
  EVERY(map (fun i -> ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (i--i) THEN
             GCM_SIMD_SIMPLIFY_TAC THEN DISCARD_STALE_Q30_TAC) (267--293)) THEN
  WBN_RESOLVE_49C_916_TAC THEN
  ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (294--294);;

(* invariant-establishment closer at s288 (mirror of WBN_LOOP_INVARIANT_ENTRY_RAW branch 1). *)
let ENTRY_CLOSER_916 =
  ENSURES_FINAL_STATE_TAC THEN
  REWRITE_TAC[wbn_loop_inv_core_raw] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM GCM_CTR_ADD_LANES]) THEN
  REWRITE_TAC[GCM_CTR_INC_ITER_ADD; GCM_CTR_ADD_1; GSYM GCM_CTR_ADD_LANES] THEN
  REWRITE_TAC[list_of_seq; MAP; ghash_polyval_acc] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GCM_CTR_INC_LANES; GCM_CTR_INC2_LANES;
     GCM_CTR_INC3_LANES; GCM_CTR_INC4_LANES; GCM_CTR_INC5_LANES;
     GCM_CTR_INC6_LANES; GCM_CTR_INC7_LANES]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM GCM_CTR_ADD_LANES]) THEN
  REWRITE_TAC[GCM_CTR_ADD_0] THEN
  CONV_TAC(ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN
  CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN
  REWRITE_TAC[WORD_ADD_0] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ADD_CLAUSES] THEN CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN
  REWRITE_TAC[WORD_ADD_0; MULT_CLAUSES] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM GCM_CTR_ADD_LANES; GCM_CTR_ADD_0] THEN
  CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN ASM_REWRITE_TAC[GCM_CTR_ADD_0] THEN
  REWRITE_TAC[gcm_ctr_raw_def;
    WORD_RULE `word_add (word_add (x:32 word) (word 12)) (word 1) =
               word_add x (word 13)`;
    WORD_ADD_0];;

(* postcond target for the front-916 leg = wbn_core_applied 0 at PC 0x9f0. *)
let wbn_entry_post_916 =
  mk_abs(`s:armstate`,
    list_mk_conj[
      `aligned_bytes_loaded s (word pc) aesv8_gcm_8x_dec_256_wb_mc`;
      `read PC s = word (pc + 0xa10)`;
      mk_comb(mk_comb(wbn_core_applied,`0:num`),`s:armstate`)]);;

let wbn_front_to_prep_916_goal =
  let ens = list_mk_comb(`ensures arm`,[wbn_front_P_tm; wbn_entry_post_916; wbn_front_C_tm]) in
  list_mk_forall(wb_front_vars, mk_imp(wbn_front_hyps_916_tm, ens));;

(* FRONT-916:  reuses the shared WBN_FRONT_PREFIX_EXT (0x20->0x4b8, with
   the R loop-constants preserved) via ENSURES_TRANS_SIMPLE, then a single step 296
   (0x4bc b.ge TAKEN for 9..16, via WBN_RESOLVE_49C_916_TAC) lands at 0xa10 =
   wbn_core_applied 0.  Close = the old ENTRY_CLOSER_916 + WB_PTRCMP tail.  htable is
   UNFOLDED into its reads right after init so they propagate through step 296 (the
   folded htable_mem_dec predicate is not tracked across steps by the stepper).
   FUSED SPLICE (STEP 4): prefix now ends at s295 (was s293); the 0x4bc b.ge is
   step 296 (was 0x4b4 step 294); its TAKEN target relocated 0xa08->0xa10. *)
let WBN_FRONT_TO_PREP_916 = prove(wbn_front_to_prep_916_goal,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC ENSURES_TRANS_SIMPLE THEN
  EXISTS_TAC wbn_front_prefix_ext_post THEN
  CONJ_TAC THENL
   [REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN MAYCHANGE_IDEMPOT_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC WBN_FRONT_PREFIX_EXT THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ENSURES_INIT_TAC "s295" THEN
    RULE_ASSUM_TAC(REWRITE_RULE[WB_MC_LEN]) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[htable_mem_dec]) THEN
    RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV let_CONV)) THEN
    WBN_RESOLVE_49C_916_TAC THEN
    ARM_STEPS_TAC AESV8_GCM_8X_DEC_256_WB_EXEC (296--296) THEN
    wb_front_fold_tac THEN
    ENTRY_CLOSER_916 THEN
    MP_TAC(SPECL [`in_p:int64`; `128`; `128`] WB_PTRCMP_FLAGS) THEN
    ANTS_TAC THENL
     [CONJ_TAC THEN MP_TAC(ASSUME `val (in_p:int64) + 16 * nblk < 2 EXP 63`) THEN
      MP_TAC(ASSUME `9 <= nblk`) THEN ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[ARITH_RULE `(128 < 128) <=> F`] THEN
    ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[htable_mem_dec] THEN ASM_REWRITE_TAC[] THEN
      CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[];
      REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
      REPEAT CONJ_TAC THEN MONOTONE_MAYCHANGE_TAC]]);;

(* PREPRETAIL-916: same statement as before (9..16 band), now derived (no sim)
   from WBN_PREPRETAIL_EXT2_UNIFIED by hyp-strengthening -- see the
   SPEED note at WBN_PREPRETAIL_EXT2_UNIFIED.  Statement-identical to the earlier
   full-sim version (aconv verified); the shared sim ran on the 9<=nblk band that
   already subsumes 9..16, so this is a pure MATCH_MP + ASM_ARITH close. *)
let wbn_prepretail_ext2_916_goal =
  let kk = `(nblk - 9) DIV 8` in
  let pre = mk_abs(`s:armstate`,
    list_mk_conj[
      `aligned_bytes_loaded s (word pc) aesv8_gcm_8x_dec_256_wb_mc`;
      `read PC s = word (pc + 0xa10)`;
      mk_comb(mk_comb(wbn_core_applied,kk),`s:armstate`)]) in
  let ens = list_mk_comb(`ensures arm`,[pre; wbn_prepretail_post_ext2; wbn_front_C_tm]) in
  list_mk_forall(wb_front_vars, mk_imp(wbn_front_hyps_916_tm, ens));;

let WBN_PREPRETAIL_EXT2_916 =
  prove(wbn_prepretail_ext2_916_goal,
    REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC WBN_PREPRETAIL_EXT2_UNIFIED THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

(* FRONT-916 ; PREPRETAIL-916 composed to the ext2 seam (pc+0x20 -> pc+3796).       *)
(* The PRECONDITION bridge collapses (nblk-9)DIV8 to 0 (q=0 for 9..16), matching     *)
(* the front-916 postcond (wbn_core_applied 0) to the prepretail-916 precond.        *)
let wbn_front_to_prep_ext2_916_goal =
  let ens = list_mk_comb(`ensures arm`,
    [wbn_front_P_tm; wbn_prepretail_post_ext2; wbn_front_C_tm]) in
  list_mk_forall(wb_front_vars, mk_imp(wbn_front_hyps_916_tm, ens));;

let WBN_FRONT_TO_PREP_EXT2_916 = prove(wbn_front_to_prep_ext2_916_goal,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC ENSURES_TRANS_SIMPLE THEN
  EXISTS_TAC wbn_entry_post_916 THEN
  CONJ_TAC THENL
   [REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN MAYCHANGE_IDEMPOT_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC WBN_FRONT_TO_PREP_916 THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN
    EXISTS_TAC (rand(rator(rator(snd(dest_imp(snd(strip_forall(concl WBN_PREPRETAIL_EXT2_916)))))))) THEN
    CONJ_TAC THENL
     [GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
      SUBGOAL_THEN `(nblk - 9) DIV 8 = 0` SUBST1_TAC THENL
       [MP_TAC(SPECL[`nblk - 9`;`8`] DIVISION) THEN ASM_ARITH_TAC;
        DISCH_THEN(fun th -> ACCEPT_TAC th)];
      MATCH_MP_TAC WBN_PREPRETAIL_EXT2_916 THEN ASM_REWRITE_TAC[]]]);;

(* WBN_PREP_TO_END_916: pc+3796 -> pc+4528 for the 9..16 band.  Same 8-way r split *)
(* as WBN_PREP_TO_END but with the 9..16 hyp band; dispatches to the FULL_916_r     *)
(* legs (r-block seam->band reconciliation, symbolic in q, q=0 here).               *)
(*                                                                                  *)
(* CLOSED CHEAT-FREE (hyps=0).  The "warm 16*1 reduce quirk" was a                 *)
(* MISDIAGNOSIS.  The real root cause: WBN_PREP_TO_END_FULL_r_TAC does NOT handle    *)
(* r=1 (it fails ACCEPT_TAC even on a COLD image) -- which is EXACTLY why the >=17    *)
(* build hand-writes WBN_PREP_TO_END_FULL_1 (:4011) and only applies the parametric  *)
(* tactic for r=2..8.  The 916 legs mirror that structure precisely:                 *)
(*   FULL_916_1 = the hand-written FULL_1 tactic body (band-agnostic: it works from  *)
(*     the nblk=8*(q+1)+1 equation + the ext2 seam post, not the 17<=/9<= band),      *)
(*   FULL_916_2..8 = WBN_PREP_TO_END_FULL_r_TAC r (unchanged; the band change is      *)
(*     confined to the goal hyps that STRIP_TAC consumes).                           *)
(* All 8 legs verified hyps=0; the dispatcher is the WBN_PREP_TO_END 8-way           *)
(* rr=(nblk-9)MOD 8 split over the FULL_916 array.                                    *)

(* 916-banded full-post goal (9..16 band; otherwise identical to *)
(* wbn_prep_to_end_full_goal). *)
let wbn_prep_to_end_full_916_goal r =
  let nblk_eq = subst[mk_small_numeral r,`r_:num`]
                  `nblk = 8 * ((nblk - 9) DIV 8 + 1) + r_` in
  let hyps = end_itlist (curry mk_conj)
    (wbn_front_hyps_916_tm :: nblk_eq :: wbn_prep_to_end_extra_clauses) in
  let ens = list_mk_comb(`ensures arm`,
    [wbn_prepretail_post_ext2; wbn_end_post; wbn_front_C_tm]) in
  list_mk_forall(wb_front_vars, mk_imp(hyps, ens));;

(* the r=1 leg tactic = body of WBN_PREP_TO_END_FULL_1 (:4011), hoisted as a named  *)
(* tactic.  Band-agnostic, so it serves both the >=17 and the 9..16 r=1 legs.  The  *)
(* parametric WBN_PREP_TO_END_FULL_r_TAC cannot do r=1 (case-2/tag close specialise *)
(* to r>=2 store re-indexing). *)
let WBN_PREP_TO_END_FULL_1_HAND_TAC =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN
  EXISTS_TAC (wbn_narrow_frame 1) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN SUBSUMED_MAYCHANGE_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN
  EXISTS_TAC (mk_abs(`s:armstate`,
    mk_conj(snd(dest_abs(el 2 (snd(strip_comb(snd(dest_imp(concl(SPECL (shift_vals 1) WB_TAIL_GEN2_1)))))))),
            el 64 (conjuncts (snd(dest_abs wbn_prepretail_post_ext2)))))) THEN
  CONJ_TAC THENL
   [X_GEN_TAC `s:armstate` THEN REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN ABBREV_TAC `q = (nblk - 9) DIV 8` THEN
    CONJ_TAC THENL
     [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
      ASM_CASES_TAC `j < 8 * (q + 1)` THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN FIRST_X_ASSUM ACCEPT_TAC;
        SUBGOAL_THEN `j = 8 * (q + 1)` SUBST_ALL_TAC THENL
         [ASM_ARITH_TAC; ALL_TAC] THEN
        REWRITE_TAC[ARITH_RULE `16 * 8 * (q + 1) = 128 * (q + 1)`; GCM_CTR_INC_ITER_ADD] THEN
        FIRST_X_ASSUM(fun th -> if is_eq(concl th) &&
          (match lhs(concl th) with Comb(Comb(Const("read",_),_),_) ->
             (can (find_term (fun t -> t = `aes256_encrypt`)) (concl th)) | _ -> false)
          then SUBST1_TAC th else NO_TAC) THEN
        SUBGOAL_THEN `SUB_LIST (0,16) (SUB_LIST (128 * (q + 1),16 * 1) (ibytes:byte list)) =
                      SUB_LIST (128 * (q + 1),16) ibytes` SUBST1_TAC THENL
         [REWRITE_TAC[SUB_LIST_MIN_RIGHT] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
          AP_TERM_TAC THEN ARITH_TAC; ALL_TAC] THEN
        GEN_REWRITE_TAC LAND_CONV [GSYM AES256_XOR_ENCRYPT_RECONSTRUCT] THEN
        CONV_TAC WORD_RULE];
      CONJ_TAC THENL
       [REWRITE_TAC[WORD_BYTEREVERSE_BYTEREVERSE] THEN AP_TERM_TAC THEN
        SUBGOAL_THEN
          `list_of_seq (\k. bytes_to_int128 (SUB_LIST (16 * k,16) (ibytes:byte list))) nblk =
           list_of_seq (\k. bytes_to_int128 (SUB_LIST (16 * k,16) ibytes)) (8 * (q + 1) + 1)`
          SUBST1_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        REWRITE_TAC[LIST_OF_SEQ_ADD; MAP_APPEND; GHASH_ACC_APPEND] THEN AP_TERM_TAC THEN
        REWRITE_TAC[LIST_OF_SEQ_CLAUSES; MAP; MULT_CLAUSES; ADD_CLAUSES] THEN
        REWRITE_TAC[SUB_LIST_MIN_RIGHT; ARITH_RULE `MIN 16 16 = 16`;
                    ARITH_RULE `16 * 8 * (q + 1) = 128 * (q + 1)`];
        (* ivec M2: shifted band ivec = gcm_ctr_inc_iter 1
           (gcm_ctr_add (word (8*(q+1))) ctr0); reconcile to gcm_ctr_inc_iter nblk
           ctr0 via ITER_ADD + ADD_COMPOSE + nblk = 8*(q+1)+1. *)
        REWRITE_TAC[GCM_CTR_INC_ITER_ADD; GCM_CTR_ADD_COMPOSE] THEN
        AP_THM_TAC THEN AP_TERM_TAC THEN
        REWRITE_TAC[GSYM WORD_ADD] THEN AP_TERM_TAC THEN ASM_ARITH_TAC]];
    MATCH_MP_TAC ENSURES_ADD_PRESERVED THEN CONJ_TAC THENL
     [INNER_TAIL_FEED_TAC 1 WB_TAIL_GEN2_1;
      REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; MAYCHANGE; SEQ_ID] THEN
      REWRITE_TAC[GSYM SEQ_ASSOC] THEN PURE_REWRITE_TAC[ASSIGNS_SEQ] THEN
      CONV_TAC(REDEPTH_CONV BETA_CONV) THEN REWRITE_TAC[ASSIGNS_THM] THEN
      CONV_TAC(REDEPTH_CONV BETA_CONV) THEN REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
      REPEAT GEN_TAC THEN STRIP_TAC THEN
      X_GEN_TAC `j:num` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_eq(concl th) &&
        (match rhs(concl th) with Var("s'",_) -> true | _ -> false))) THEN
      SUBGOAL_THEN `nonoverlapping (word_add out_p (word (16 * j)):int64,16)
         (word_add out_p (word (128 * ((nblk - 9) DIV 8 + 1))),16)` ASSUME_TAC THENL
       [NONOVERLAPPING_TAC; ALL_TAC] THEN
      WBN_PUSH_LHS_READ_TAC THEN
      FIRST_ASSUM(fun th -> if is_forall(concl th) then MATCH_MP_TAC th else NO_TAC) THEN
      FIRST_X_ASSUM ACCEPT_TAC]];;

(* r=1 keeps its hand tactic; r=2..8 DERIVE from the unified FREE_r sims proved
   once above (SPEED dedup), no re-simulation.  Statement bit-
   identical to the pre-072 full-sim version (9..16 band). *)
let WBN_PREP_TO_END_FULL_916_1 = prove(wbn_prep_to_end_full_916_goal 1, WBN_PREP_TO_END_FULL_1_HAND_TAC);;
let WBN_PREP_TO_END_FULL_916_2 = prove(wbn_prep_to_end_full_916_goal 2, wbn_prep_to_end_full_derive_tac WBN_PREP_TO_END_FREE_2);;
let WBN_PREP_TO_END_FULL_916_3 = prove(wbn_prep_to_end_full_916_goal 3, wbn_prep_to_end_full_derive_tac WBN_PREP_TO_END_FREE_3);;
let WBN_PREP_TO_END_FULL_916_4 = prove(wbn_prep_to_end_full_916_goal 4, wbn_prep_to_end_full_derive_tac WBN_PREP_TO_END_FREE_4);;
let WBN_PREP_TO_END_FULL_916_5 = prove(wbn_prep_to_end_full_916_goal 5, wbn_prep_to_end_full_derive_tac WBN_PREP_TO_END_FREE_5);;
let WBN_PREP_TO_END_FULL_916_6 = prove(wbn_prep_to_end_full_916_goal 6, wbn_prep_to_end_full_derive_tac WBN_PREP_TO_END_FREE_6);;
let WBN_PREP_TO_END_FULL_916_7 = prove(wbn_prep_to_end_full_916_goal 7, wbn_prep_to_end_full_derive_tac WBN_PREP_TO_END_FREE_7);;
let WBN_PREP_TO_END_FULL_916_8 = prove(wbn_prep_to_end_full_916_goal 8, wbn_prep_to_end_full_derive_tac WBN_PREP_TO_END_FREE_8);;

let wbn_full_916_thm = Array.of_list
  [WBN_PREP_TO_END_FULL_916_1;  (* index 0 unused; use r directly 1..8 *)
   WBN_PREP_TO_END_FULL_916_1; WBN_PREP_TO_END_FULL_916_2; WBN_PREP_TO_END_FULL_916_3;
   WBN_PREP_TO_END_FULL_916_4; WBN_PREP_TO_END_FULL_916_5; WBN_PREP_TO_END_FULL_916_6;
   WBN_PREP_TO_END_FULL_916_7; WBN_PREP_TO_END_FULL_916_8];;

let wbn_prep_to_end_916_goal =
  let hyps = end_itlist (curry mk_conj)
    (wbn_front_hyps_916_tm :: `9 <= nblk` :: wbn_prep_to_end_extra_clauses) in
  let ens = list_mk_comb(`ensures arm`,
    [wbn_prepretail_post_ext2; wbn_end_post; wbn_front_C_tm]) in
  list_mk_forall(wb_front_vars, mk_imp(hyps, ens));;

let WBN_PREP_TO_END_916 = prove(wbn_prep_to_end_916_goal,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `nblk - 9` (MATCH_MP DIVISION (ARITH_RULE `~(8 = 0)`))) THEN
  ABBREV_TAC `rr = (nblk - 9) MOD 8` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(fun th -> if concl th = `rr < 8` then MP_TAC th else NO_TAC) THEN
  REWRITE_TAC[ARITH_RULE
    `rr < 8 <=> rr = 0 \/ rr = 1 \/ rr = 2 \/ rr = 3 \/
                rr = 4 \/ rr = 5 \/ rr = 6 \/ rr = 7`] THEN
  STRIP_TAC THEN
  FIRST (map (fun r ->
    MATCH_MP_TAC wbn_full_916_thm.(r) THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `nblk - 9 = (nblk - 9) DIV 8 * 8 + rr` THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `9 <= nblk` THEN ARITH_TAC) (1--8)));;

(* WBN_FRONT_TO_END_916: the full 9..16 front->exit chain, pc+0x20 -> pc+4528. *)
(* FRONT_TO_PREP_EXT2_916 ; PREP_TO_END_916 via ENSURES_TRANS_SIMPLE.          *)
let wbn_front_to_end_916_goal =
  let hyps = end_itlist (curry mk_conj)
    (wbn_front_hyps_916_tm :: wbn_prep_to_end_extra_clauses) in
  let ens = list_mk_comb(`ensures arm`,
    [wbn_front_P_tm; wbn_end_post; wbn_front_C_tm]) in
  list_mk_forall(wb_front_vars, mk_imp(hyps, ens));;

let WBN_FRONT_TO_END_916 = prove(wbn_front_to_end_916_goal,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC ENSURES_TRANS_SIMPLE THEN
  EXISTS_TAC wbn_prepretail_post_ext2 THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN MAYCHANGE_IDEMPOT_TAC;
    MATCH_MP_TAC WBN_FRONT_TO_PREP_EXT2_916 THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC WBN_PREP_TO_END_916 THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* PHASE 6 IS COMPLETE: WBN_PREP_TO_END_916 is CHEAT-free, so                   *)
(* the WHOLE nblk>8 chain (WBN_FRONT_TO_END for >=17, WBN_FRONT_TO_END_916 for  *)
(* 9..16) is CHEAT-free.  The former scoped Q19/Q16 RINNER=LINNER identity (once *)
(* at the loop body + the 4 guarded prepretail sites) was CLOSED by the Q19 R1'  *)
(* route (WBN_MACHINE_REDUCE_IS_PROP3_PACK +                                     *)
(* WBN_BODY_Q19_REDUCE_CLEAN, wired in).  No CHEAT, no new_axiom anywhere.        *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* PHASE 7 tag-side bridge lemmas (sim-free, symbolic nblk).                   *)
(* These reconcile wbn_end_post's tag conjunct to the NIST nist_ghash form at   *)
(* symbolic nblk (the fixed-N LIST_OF_SEQ_NIST_INPUT in the <=8-block chain does not cover a   *)
(* symbolic count).  WBN_TAG_NIST_BRIDGE is the drop-in tag rewrite for the      *)
(* Phase-7 postcondition reconcile under the band identifications               *)
(* byteswap128 h = ghash_twist H and xi = word_reversefields 8 tag0.            *)
let MAP_LIST_OF_SEQ = prove
 (`!(g:A->B) f n. MAP g (list_of_seq f n) = list_of_seq (g o f) n`,
  GEN_TAC THEN ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN INDUCT_TAC THEN GEN_TAC THEN
  ASM_REWRITE_TAC[LIST_OF_SEQ; MAP; o_THM] THEN REWRITE_TAC[o_ASSOC]);;

let LIST_OF_SEQ_NIST_INPUT_SYM = prove
 (`!ibytes N.
     list_of_seq (nist_input_block ibytes) N =
     MAP word_bytereverse
       (list_of_seq (\k. bytes_to_int128 (SUB_LIST (16 * k,16) ibytes)) N)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MAP_LIST_OF_SEQ] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; o_THM; nist_input_block; BREV_RF8_128]);;

let WBN_TAG_NIST_BRIDGE = prove
 (`!(H:int128) h xi tag0 ibytes nblk.
     byteswap128 h = ghash_twist H /\ xi = word_reversefields 8 tag0
     ==> word_bytereverse
           (ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
             (MAP word_bytereverse
               (list_of_seq (\k. bytes_to_int128 (SUB_LIST (16 * k,16) ibytes)) nblk))) =
         word_reversefields 8
           (nist_ghash H tag0 (list_of_seq (nist_input_block ibytes) nblk))`,
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[NIST_GHASH_IS_POLYVAL; LIST_OF_SEQ_NIST_INPUT_SYM; BREV_RF8_128] THEN
  REWRITE_TAC[GSYM BREV_RF8_128; WORD_BYTEREVERSE_BYTEREVERSE]);;

(* ------------------------------------------------------------------------- *)
(* PHASE 7 output-side bridge lemmas (sim-free, symbolic nblk).                *)
(* These are the symbolic-nblk analogues of the fixed-N GCM_DEC_PT_BYTES_WHOLE_k*)
(* + BYTE_LIST_AT_WHOLE_CTR machinery in the <=8-block chain, reconciling wbn_end_post's      *)
(* nblk-uniform per-block output store forall to byte_list_at(gcm_dec_pt_bytes).*)

(* EL of gcm_dec_blocks_from at a symbolic index (analogue of build_aes_ctr_el).*)
let EL_GCM_DEC_BLOCKS_FROM = prove
 (`!m base i x. i < m
     ==> EL i (gcm_dec_blocks_from base m x) =
         bytes_to_int128 (SUB_LIST (16 * (base + i),16) x)`,
  INDUCT_TAC THEN REWRITE_TAC[LT] THEN
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC (SPEC `i:num` num_CASES) THEN
  REWRITE_TAC[GCM_DEC_BLOCKS_FROM_STEP; EL; HD; TL] THENL
   [REWRITE_TAC[ADD_CLAUSES];
    DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`base + 1`; `n:num`; `x:byte list`]) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN DISCH_THEN SUBST1_TAC THEN
    SUBGOAL_THEN `(base + 1) + n = base + SUC n` SUBST1_TAC THENL
     [ARITH_TAC; REFL_TAC]]);;

(* Whole-blocks (tail=16) collapse of gcm_dec_pt_bytes at symbolic nblk:        *)
(*   nfull=(16*nblk-1)DIV 16=nblk-1, tail=16, so aes_ctr_full_tail_bytes -> ctr. *)
let GCM_DEC_PT_BYTES_WHOLE_SYM = prove
 (`!nblk ibytes ctr0 rk. 1 <= nblk
     ==> gcm_dec_pt_bytes (16 * nblk) ibytes ctr0 rk =
         aes_ctr_bytes ctr0 (gcm_dec_blocks_from 0 nblk ibytes) rk`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[gcm_dec_pt_bytes] THEN
  SUBGOAL_THEN `(16 * nblk - 1) DIV 16 = nblk - 1` SUBST1_TAC THENL
   [ASM_SIMP_TAC[ARITH_RULE `1 <= nblk ==> 16 * nblk - 1 = 16 * (nblk - 1) + 15`] THEN
    SIMP_TAC[DIV_MULT_ADD; ARITH_EQ] THEN ARITH_TAC; ALL_TAC] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  SUBGOAL_THEN `nblk - 1 + 1 = nblk /\ 16 * nblk - 16 * (nblk - 1) = 16`
    (CONJUNCTS_THEN SUBST1_TAC) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC AES_CTR_FULL_TAIL_BYTES_WHOLE THEN
  REWRITE_TAC[LENGTH_GCM_DEC_BLOCKS_FROM] THEN ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* POINTWISE data-output support.                                              *)
(*                                                                             *)
(* WHY these exist: the exported data postcondition is otherwise ONLY the      *)
(* whole-buffer byte-list form byte_list_at(gcm_dec_pt_bytes(16*nblk)..).      *)
(* gcm_dec_pt_bytes INTERNALLY computes nfull=(len-1)DIV 16 and tail=len-16    *)
(* nfull -- partial-block machinery that is DEAD at whole-block lengths (it    *)
(* degenerates to nfull=nblk-1, tail=16, GCM_DEC_PT_BYTES_WHOLE_SYM).  A       *)
(* reviewer must re-derive that to see the routine only handles whole blocks;  *)
(* the statement reads as though arbitrary byte lengths are accepted (inherited*)
(* from the masked-partial chain).  The pointwise form                         *)
(*   !j. j<nblk ==> read(memory:>bytes128(out_p+16j)) s = EL j (aes_ctr ...)    *)
(* removes that ambiguity and matches the sibling AES-GCM proofs' shape.  Do   *)
(* NOT "simplify" it away by folding it back into the byte-list form.          *)

(* 16 bytes at offset 16*j of int128_list_to_bytes repack to EL j.  The reverse
   direction of the int128-list/byte-list correspondence; no such lemma existed. *)
let SUB_LIST_INT128_LIST_TO_BYTES_EL = prove
 (`!cts j. j < LENGTH cts
     ==> bytes_to_int128 (SUB_LIST (16 * j,16) (int128_list_to_bytes cts)) =
         EL j cts`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
    `SUB_LIST (16 * j,16) (int128_list_to_bytes (cts:int128 list)) =
     int128_to_bytes (EL j cts)`
   SUBST1_TAC THENL
   [REWRITE_TAC[LIST_EQ] THEN
    REWRITE_TAC[LENGTH_SUB_LIST; LENGTH_INT128_LIST_TO_BYTES;
                LENGTH_INT128_TO_BYTES] THEN
    CONJ_TAC THENL
     [ASM_SIMP_TAC[ARITH_RULE `j < n ==> MIN 16 (16 * n - 16 * j) = 16`];
      X_GEN_TAC `i:num` THEN REWRITE_TAC[LENGTH_INT128_TO_BYTES] THEN
      DISCH_TAC THEN
      MP_TAC(ISPECL [`16 * j`; `int128_list_to_bytes (cts:int128 list)`;
                     `16 * j + i`; `16`] EL_SUB_LIST_GENERAL) THEN
      REWRITE_TAC[LENGTH_INT128_LIST_TO_BYTES] THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `(16 * j + i) - 16 * j = i` SUBST1_TAC THENL
       [ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN SUBST1_TAC THEN
      MP_TAC(SPECL [`cts:int128 list`; `16 * j + i`] EL_INT128_LIST_TO_BYTES) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN SUBST1_TAC THEN
      SUBGOAL_THEN `(16 * j + i) DIV 16 = j /\ (16 * j + i) MOD 16 = i`
        (CONJUNCTS_THEN SUBST1_TAC) THENL
       [ASM_SIMP_TAC[DIV_MULT_ADD; MOD_MULT_ADD; ARITH_EQ; DIV_LT; MOD_LT] THEN
        REWRITE_TAC[ADD_CLAUSES];
        ALL_TAC] THEN
      ASM_SIMP_TAC[EL_INT128_TO_BYTES]];
    REWRITE_TAC[BYTES_TO_INT128_OF_INT128_TO_BYTES]]);;

(* byte_list_at(gcm_dec_pt_bytes ...) -> the per-block bytes128 reads.  At
   whole-block lengths the partial-block machinery in gcm_dec_pt_bytes is dead
   (GCM_DEC_PT_BYTES_WHOLE_SYM), so each 16-byte slice is exactly EL j of the
   counter-mode stream.  This is the "reverse" s078 believed did not exist:
   BYTE_LIST_AT_1BLOCKS gives byte_list_at -> per-block bytes128, and the repack
   lemma above closes the 16-byte slice back to EL j. *)
let WBN_OUTPUT_POINTWISE = prove
 (`!nblk ibytes ctr0 rk out_p s.
     1 <= nblk /\ 128 * nblk < 2 EXP 62 /\
     byte_list_at (gcm_dec_pt_bytes (16 * nblk) ibytes ctr0 rk)
                  out_p (word (16 * nblk)) s
     ==> !j. j < nblk
             ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                 EL j (aes_ctr ctr0 (gcm_dec_blocks_from 0 nblk ibytes) rk)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
    `byte_list_at (int128_list_to_bytes
        (aes_ctr ctr0 (gcm_dec_blocks_from 0 nblk ibytes) rk))
        out_p (word (16 * nblk)) s`
   ASSUME_TAC THENL
   [ASM_MESON_TAC[GCM_DEC_PT_BYTES_WHOLE_SYM; aes_ctr_bytes]; ALL_TAC] THEN
  SUBGOAL_THEN
    `LENGTH (int128_list_to_bytes
        (aes_ctr ctr0 (gcm_dec_blocks_from 0 nblk ibytes) rk)) =
     val (word (16 * nblk):int64)`
   ASSUME_TAC THENL
   [REWRITE_TAC[LENGTH_INT128_LIST_TO_BYTES; LENGTH_AES_CTR;
                LENGTH_GCM_DEC_BLOCKS_FROM] THEN
    CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    MP_TAC(ASSUME `128 * nblk < 2 EXP 62`) THEN ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`16 * j`; `int128_list_to_bytes
                   (aes_ctr ctr0 (gcm_dec_blocks_from 0 nblk ibytes) rk)`;
                 `out_p:int64`; `word (16 * nblk):int64`; `s:armstate`]
         BYTE_LIST_AT_1BLOCKS) THEN
  ASM_REWRITE_TAC[LENGTH_INT128_LIST_TO_BYTES; LENGTH_AES_CTR;
                  LENGTH_GCM_DEC_BLOCKS_FROM] THEN
  ANTS_TAC THENL
   [FIRST_X_ASSUM(fun th ->
      if is_eq(concl th) &&
         (try can (find_term (fun t -> t = `val (word (16 * nblk):int64)`))
                  (concl th) with _ -> false)
      then SUBST1_TAC(SYM th) else NO_TAC) THEN
    REWRITE_TAC[LENGTH_INT128_LIST_TO_BYTES; LENGTH_AES_CTR;
                LENGTH_GCM_DEC_BLOCKS_FROM] THEN
    MP_TAC(ASSUME `j < nblk`) THEN ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC SUB_LIST_INT128_LIST_TO_BYTES_EL THEN
  REWRITE_TAC[LENGTH_AES_CTR; LENGTH_GCM_DEC_BLOCKS_FROM] THEN
  MP_TAC(ASSUME `j < nblk`) THEN ARITH_TAC);;

(* Per-block value bridge: wbn_end_post's store form (word_xor(word_xor cph     *)
(* aes13..)k14) is exactly EL j of aes_ctr over the gcm_dec_blocks_from list     *)
(* with the 15-key list.  Standalone (keeps AES/counter algebra out of the       *)
(* ensures context) — analogue of the <=8-block chain build_aes_ctr_el, at symbolic j.        *)
let WBN_ENDBLOCK_IS_AES_CTR = prove
 (`!nblk ibytes ctr0 k0 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 k11 k12 k13 k14 j.
     j < nblk
     ==> word_xor
           (word_xor (bytes_to_int128 (SUB_LIST (16 * j,16) ibytes))
             (aes13 (gcm_ctr_inc_iter j ctr0) k0 k1 k2 k3 k4 k5 k6 k7 k8 k9
                    k10 k11 k12 k13))
           k14 =
         EL j (aes_ctr ctr0 (gcm_dec_blocks_from 0 nblk ibytes)
                 [k0;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14])`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`nblk:num`; `0`; `j:num`; `ibytes:byte list`]
    EL_GCM_DEC_BLOCKS_FROM) THEN
  ASM_REWRITE_TAC[ADD_CLAUSES] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`gcm_dec_blocks_from 0 nblk ibytes`; `ctr0:int128`;
    `[k0;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14]:int128 list`; `j:num`]
    EL_AES_CTR) THEN
  ASM_REWRITE_TAC[LENGTH_GCM_DEC_BLOCKS_FROM] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM AES256_XOR_ENCRYPT_RECONSTRUCT] THEN CONV_TAC WORD_RULE);;

(* The full L1 output bridge: wbn_end_post's per-block store forall            *)
(* (word_xor(word_xor cph aes13..)k14) collapses to                             *)
(* byte_list_at(gcm_dec_pt_bytes(16*nblk)..) over the whole buffer.  The        *)
(* symbolic-nblk analogue of prove_wb_wrapper's BYTE_LIST_AT_WHOLE_CTR leg.     *)
(* 128*nblk < 2 EXP 62 (from the chain hyps) gives val(word(16*nblk))=16*nblk.  *)
let WBN_END_OUTPUT_BYTE_LIST = prove
 (`!nblk ibytes ctr0 k0 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 k11 k12 k13 k14 out_p s.
     1 <= nblk /\ 128 * nblk < 2 EXP 62 /\
     (!j. j < nblk
          ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
              word_xor
              (word_xor (bytes_to_int128 (SUB_LIST (16 * j,16) ibytes))
              (aes13 (gcm_ctr_inc_iter j ctr0) k0 k1 k2 k3 k4 k5 k6 k7 k8 k9
               k10 k11 k12 k13))
              k14)
     ==> byte_list_at
           (gcm_dec_pt_bytes (16 * nblk) ibytes ctr0
              [k0;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14])
           out_p (word (16 * nblk)) s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_SIMP_TAC[GCM_DEC_PT_BYTES_WHOLE_SYM] THEN
  MATCH_MP_TAC BYTE_LIST_AT_WHOLE_CTR THEN EXISTS_TAC `nblk:num` THEN
  REWRITE_TAC[LENGTH_GCM_DEC_BLOCKS_FROM] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC;
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC WBN_ENDBLOCK_IS_AES_CTR THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Counter-model bridge to the NIST SP 800-38D nonce||counter form used by the *)
(* sibling AES-GCM proofs, wired into the exported theorems' nonce-named        *)
(* keystream.                                                                  *)
(*                                                                             *)
(* Our chain names counters via gcm_ctr_inc_iter j ctr0 (successor-iterated     *)
(* over an OPAQUE initial block ctr0).  The sibling proofs instead use          *)
(*   ctr_block nonce ctr = word_join (nonce:96 word) (word ctr:int32)          *)
(* (NIST big-endian: fixed 96-bit nonce, 32-bit big-endian counter).  These     *)
(* lemmas prove the two models COINCIDE: gcm_ctr_inc_iter is exactly NIST inc32 *)
(* iterated on the nonce||counter block (conjugated by the load-time byteswap), *)
(* UNCONDITIONALLY (the 32-bit wrap is the intended mod-2^32 rollover).          *)
(* GCM_CTR_INC_ITER_CTR_BLOCK + CTR0_AS_CTR_BLOCK are what let the exported      *)
(* _CORRECT/_SUBROUTINE_CORRECT NAME the nonce (via WBN_OUTPUT_POINTWISE_NONCE   *)
(* below).  ctr_block + aes_ctr_block are the SHARED NIST vocabulary, now        *)
(* defined in arm/proofs/utils/aes_ctr_spec.ml and reached through               *)
(* this file's needs-chain (lemmas.ml -> aes_gcm_dec_spec.ml -> aes_ctr_spec.ml).*)
(* ------------------------------------------------------------------------- *)

(* NIST inc32 on a nonce||counter block just increments the 32-bit counter --    *)
(* UNCONDITIONALLY (word (c+1):int32 = word_add (word c) (word 1), the wrap is    *)
(* the intended mod-2^32 counter rollover).                                      *)
let INC32_CTR_BLOCK = prove
 (`!(nonce:96 word) c. inc32 (ctr_block nonce c) = ctr_block nonce (c + 1)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[inc32; ctr_block] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[WORD_BLAST
    `word_subword (word_join (nonce:96 word) (wc:int32):int128) (0,32):32 word = wc`;
              WORD_BLAST
    `word_subword (word_join (nonce:96 word) (wc:int32):int128) (32,96):96 word = nonce`] THEN
  REWRITE_TAC[WORD_ADD] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC);;

(* ... iterated: j applications of inc32 advance the counter by j.               *)
let ITER_INC32_CTR_BLOCK = prove
 (`!j (nonce:96 word) c. ITER j inc32 (ctr_block nonce c) = ctr_block nonce (c + j)`,
  INDUCT_TAC THEN REPEAT GEN_TAC THEN REWRITE_TAC[ITER; ADD_CLAUSES] THEN
  ASM_REWRITE_TAC[INC32_CTR_BLOCK] THEN REWRITE_TAC[INC32_CTR_BLOCK] THEN
  AP_TERM_TAC THEN ARITH_TAC);;

(* THE BRIDGE: our gcm_ctr_inc_iter j ctr0 equals the NIST nonce||counter block  *)
(* advanced by j, provided the byteswapped ctr0 decomposes as nonce||c.  Via     *)
(* GCM_CTR_INC_ITER_INC32 (gcm_ctr_inc_iter = bytereverse . ITER inc32 .          *)
(* bytereverse, gcm_ctr_helpers.ml).                                             *)
let GCM_CTR_INC_ITER_CTR_BLOCK = prove
 (`!j (nonce:96 word) c ctr0.
     word_bytereverse ctr0 = ctr_block nonce c
     ==> gcm_ctr_inc_iter j ctr0 = word_bytereverse (ctr_block nonce (c + j))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GCM_CTR_INC_ITER_INC32] THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[ITER_INC32_CTR_BLOCK]);;

(* Any opaque ctr0 admits such a decomposition (nonce = top 96 bits of the        *)
(* byteswapped block, c = its low 32-bit counter), so the bridge always applies:  *)
(* the nonce IS extractable, it is simply not NAMED in the current postcondition.  *)
let CTR0_AS_CTR_BLOCK = prove
 (`!ctr0:int128. ?nonce c. c < 2 EXP 32 /\ word_bytereverse ctr0 = ctr_block nonce c`,
  GEN_TAC THEN
  EXISTS_TAC `word_subword (word_bytereverse ctr0:int128) (32,96):96 word` THEN
  EXISTS_TAC `val(word_subword (word_bytereverse ctr0:int128) (0,32):32 word)` THEN
  CONJ_TAC THENL
   [MP_TAC(ISPEC `word_subword (word_bytereverse ctr0:int128) (0,32):32 word` VAL_BOUND) THEN
    REWRITE_TAC[DIMINDEX_32];
    REWRITE_TAC[ctr_block; WORD_VAL] THEN CONV_TAC WORD_BLAST]);;

(* ========================================================================= *)
(* ROADMAP -- how to read the exported theorems below top-down.                *)
(*                                                                             *)
(* The whole-function contract is the PAIR                                     *)
(*   AESV8_GCM_8X_DEC_256_SUBROUTINE_CORRECT  (ABI wrapper, this file)       *)
(*   AESV8_GCM_8X_DEC_256_GUARD               (reject path, the <=8-block chain)           *)
(* with AESV8_GCM_8X_DEC_256_CORRECT the after-prologue core it wraps.  The  *)
(* two exported CORRECT theorems are DERIVED from two internal                  *)
(* H-free byte-list spines by pinning H + weakening the postcond (see their     *)
(* headers below for the vocabulary and the derivation):                        *)
(*   WBN_DEC_CORE_BYTELIST        (byte_list output, pc+0x20..pc+4528)          *)
(*   WBN_DEC_SUBROUTINE_BYTELIST  (byte_list output, ABI wrapper)               *)
(* The spines carry the full sim/chain proof; the exports are pure vocabulary   *)
(* lifts on top, so nothing large propagates and the sims are never re-run.     *)
(*                                                                             *)
(*   _SUBROUTINE_CORRECT / WBN_DEC_SUBROUTINE_BYTELIST  (Phase 8, below)        *)
(*     = prologue (guard fall-through + d8-d15 spills)                          *)
(*       ; WBN_DEC_CORE_BYTELIST                 <- the core, pc+0x20..pc+4528  *)
(*       ; epilogue (restore d8-d15 + ret)                                      *)
(*                                                                             *)
(*   WBN_DEC_CORE_BYTELIST   (Phase 7, below)  -- one core contract for ALL     *)
(*   nblk>=1, by a 3-way split on the block count (3 control-flow paths):       *)
(*     nblk <= 8   : AESV8_GCM_8X_DEC_256_DISPATCH   (the <=8-block chain; loop skipped)    *)
(*     9 <= nblk<=16: WBN_FRONT_TO_END_916             (loop entered 0 times)   *)
(*     nblk >= 17  : WBN_FRONT_TO_END                  (loop entered >=1 time)  *)
(*   WBN_CHAIN_TO_NIST_TAC bridges the two >8 chains (raw per-block vocab) to    *)
(*   the NIST DISPATCH vocab (see the PHASE 7 note just below).                  *)
(*                                                                             *)
(*   Each >8 chain factors, via ENSURES_TRANS_SIMPLE, into the four segments    *)
(*   the binary runs in sequence (entry pc+0x20 -> exit pc+4528):               *)
(*     FRONT       WBN_FRONT_BUF / _EXT / _EXT2      pc+0x20  -> loop head 0x4a0 *)
(*     LOOP        WBN_MAIN_LOOP_raw (ENSURES_WHILE)     0x4a0    -> 0x4a0 (per iter)*)
(*     PREPRETAIL  WBN_PREPRETAIL / _EXT / _EXT2     0x9f0    -> tail entry 3796 *)
(*     TAIL        WBN_PREP_TO_END(_FULL) / _916     3796     -> 4528            *)
(*   Composed as:  WBN_FRONT_TO_PREP(_EXT2)          = FRONT ; LOOP ; PREPRETAIL *)
(*                 WBN_FRONT_TO_END(_916)            = FRONT_TO_PREP ; TAIL      *)
(*   (the _916 spelling is the 9..16 leg where LOOP runs 0 times; the _EXT/     *)
(*    _EXT2 spellings widen the carried invariant/output vocab across seams).    *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* PHASE 7: WBN_DEC_CORE_BYTELIST -- all nblk >= 1 (H free,                    *)
(* byte-list output; the internal spine the exported _CORRECT is lifted from). *)
(* 3-way ASM_CASES: nblk<=8 -> existing DISPATCH (NIST vocab already); 9..16 -> *)
(* WBN_FRONT_TO_END_916; >=17 -> WBN_FRONT_TO_END.  Each >8 chain ends in       *)
(* wbn_end_post (RAW per-block ext2 vocab) and begins at wbn_front_P_tm (raw xi, *)
(* individual k0..k14 reads, htable_mem_dec h).  WBN_CHAIN_TO_NIST_TAC bridges   *)
(* the raw chain to the NIST DISPATCH vocab under the band identifications       *)
(*   ki := EL i rk,  h := byteswap128 (ghash_twist H),  xi := word_reversefields *)
(*   8 tag0                                                                      *)
(* via ENSURES_PRECONDITION_THM (NIST pre -> raw pre: KEY_READS_FROM_WORDLIST +  *)
(* HTABLE_MEM_DEC_IS_HTABLE_MEM_8 + BYTESWAP128_INVOLUTION + BYTE_LIST_AT_TO_    *)
(* READ_BYTES) and ENSURES_POSTCONDITION_THM (raw post -> NIST post: RK_ETA_15 + *)
(* WBN_END_OUTPUT_BYTE_LIST for output, WBN_TAG_NIST_BRIDGE for tag).  The chain *)
(* hyps flatten from the DISPATCH ALLPAIRS/PAIRWISE/ALL form.                    *)
(*                                                                             *)
(* The unified statement is the DISPATCH statement with the `nblk<=8` bound      *)
(* DROPPED (just 1<=nblk) and the two size bounds 128*nblk<2 EXP 62 /            *)
(* val in_p+16*nblk<2 EXP 63 ADDED to the antecedent (genuine preconditions the  *)
(* Phase-8 wrapper/guard supplies -- for nblk<=8 they follow from small nblk;    *)
(* for symbolic large nblk they must be assumed to avoid pointer/length          *)
(* overflow).  CHEAT-FREE (the former Q19/[11] RINNER=LINNER identity was closed  *)
(* by the R1' route); no new_axiom anywhere.                                     *)

(* The statement is spelled out literally (XTS style) so the
   reader sees the full pre/post/frame contract first.  It is the DISPATCH
   ensures-body verbatim, with the `nblk<=8` bound replaced by `1<=nblk` plus the
   two size bounds the Phase-8 wrapper/guard supplies (128*nblk<2 EXP 62 and
   val in_p+16*nblk<2 EXP 63 -- for nblk<=8 they follow from small nblk; for
   symbolic large nblk they rule out pointer/length overflow).  This spine keeps
   H free and the output as the whole-buffer byte list; the exported _CORRECT
   below pins H and restates the output pointwise.  The load-time soundness gate
   re-derives this spine statement from the frozen _DISPATCH by term surgery and
   asserts aconv-equality, so any drift of this literal fails the load (see the
   `let () = ...` gate at end of file). *)

let WBN_DEC_CORE_BYTELIST = prove
 (`!pc stackpointer in_p out_p xi_p ivec_p key_p htbl_p nblk ibytes rk H
    tag0 ctr0.
    1 <= nblk /\
    128 * nblk < 2 EXP 62 /\
    val in_p + 16 * nblk < 2 EXP 63 /\
    LENGTH ibytes = 16 * nblk /\
    LENGTH rk = 15 /\
    aligned 16 stackpointer /\
    ALLPAIRS nonoverlapping [out_p,16 * nblk; xi_p,16; ivec_p,16]
    [word pc, LENGTH aesv8_gcm_8x_dec_256_wb_mc; in_p,16 * nblk; key_p,240; htbl_p,192; stackpointer,80] /\
    PAIRWISE nonoverlapping [out_p,16 * nblk; xi_p,16; ivec_p,16] /\
    ALL (nonoverlapping (stackpointer,80))
    [word pc, LENGTH aesv8_gcm_8x_dec_256_wb_mc; in_p,16 * nblk; key_p,240; htbl_p,192]
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) aesv8_gcm_8x_dec_256_wb_mc /\
              read PC s = word (pc + 32) /\
              read SP s = stackpointer /\
              C_ARGUMENTS
              [in_p; word (128 * nblk); out_p; xi_p; ivec_p; key_p; htbl_p]
              s /\
              byte_list_at ibytes in_p (word (16 * nblk)) s /\
              read (memory :> bytes128 xi_p) s = word_reversefields 8 tag0 /\
              read (memory :> bytes128 ivec_p) s = ctr0 /\
              wordlist_from_memory (key_p,15) s = rk /\
              htable_mem_8 (ghash_twist H) htbl_p s)
         (\s. read PC s = word (pc + 4560) /\
              byte_list_at (gcm_dec_pt_bytes (16 * nblk) ibytes ctr0 rk) out_p
              (word (16 * nblk)) s /\
              read (memory :> bytes128 xi_p) s =
              word_reversefields 8
              (nist_ghash H tag0
              (list_of_seq (nist_input_block ibytes) nblk)) /\
              read (memory :> bytes128 ivec_p) s = gcm_ctr_inc_iter nblk ctr0)
         (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
          MAYCHANGE
          [memory :> bytes (out_p,16 * nblk); memory :> bytes (xi_p,16);
           memory :> bytes (ivec_p,16);
           memory :> bytes (word_add stackpointer (word 64),16)] ,,
          MAYCHANGE
          [Q0; Q1; Q2; Q3; Q4; Q5; Q6; Q7; Q8; Q9; Q10; Q11; Q12; Q13; Q14;
           Q15; Q16; Q17; Q18; Q19; Q20; Q21; Q22; Q23; Q24; Q25; Q26; Q27;
           Q28; Q29; Q30; Q31])`,
  (* The proof reconciles the raw per-block chain vocab with the NIST DISPATCH
     vocab; these helper lets are local to the proof (JH idiom). *)
  (* identification substitution: raw chain vars -> DISPATCH NIST vars *)
  let idsub =
    [`word_reversefields 8 (tag0:int128)`,`xi:int128`;
     `byteswap128 (ghash_twist H)`,`h:int128`] @
    (map (fun i -> mk_comb(mk_comb(`EL:num->(int128)list->int128`,mk_small_numeral i),
                           `rk:int128 list`),
                   mk_var("k"^string_of_int i,`:int128`)) (0--14)) in
  let raw_pre'  = subst idsub wbn_front_P_tm
  and raw_post' = subst idsub wbn_end_post in
  (* the shared reconcile tactic, parameterized by the chain theorem *)
  let WBN_CHAIN_TO_NIST_TAC chain_thm =
    MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN EXISTS_TAC raw_pre' THEN CONJ_TAC THENL
     [X_GEN_TAC `s:armstate` THEN BETA_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[HTABLE_MEM_DEC_IS_HTABLE_MEM_8; BYTESWAP128_INVOLUTION] THEN
      MP_TAC(SPECL [`key_p:int64`; `rk:int128 list`; `s:armstate`]
        KEY_READS_FROM_WORDLIST) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`ibytes:byte list`; `in_p:int64`; `word (16 * nblk):int64`;
        `s:armstate`] BYTE_LIST_AT_TO_READ_BYTES) THEN
      SUBGOAL_THEN `val (word (16 * nblk):int64) = 16 * nblk` ASSUME_TAC THENL
       [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC;
        ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN EXISTS_TAC raw_post' THEN
      CONJ_TAC THENL
       [X_GEN_TAC `s:armstate` THEN BETA_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
        CONJ_TAC THENL
         [SUBGOAL_THEN
           `gcm_dec_pt_bytes (16 * nblk) ibytes ctr0 rk =
            gcm_dec_pt_bytes (16 * nblk) ibytes ctr0
              [EL 0 rk;EL 1 rk;EL 2 rk;EL 3 rk;EL 4 rk;EL 5 rk;EL 6 rk;EL 7 rk;
               EL 8 rk;EL 9 rk;EL 10 rk;EL 11 rk;EL 12 rk;EL 13 rk;EL 14 rk]`
           SUBST1_TAC THENL
           [AP_TERM_TAC THEN MATCH_MP_TAC RK_ETA_15 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
          MATCH_MP_TAC WBN_END_OUTPUT_BYTE_LIST THEN ASM_REWRITE_TAC[];
          (* ivec M2: the spine ivec conjunct is IDENTICAL raw
             vs NIST (idsub touches neither ctr0 nor gcm_ctr_inc_iter), so the
             outer ASM_REWRITE_TAC[] already discharged it -- this leg is the tag
             ALONE.  s101 wrongly wrapped it in a CONJ_TAC, which threw on the
             single-conjunct goal (the gate's "CONJ_TAC" failure). *)
          MP_TAC(SPECL [`H:int128`; `byteswap128 (ghash_twist H)`;
            `word_reversefields 8 (tag0:int128)`; `tag0:int128`; `ibytes:byte list`;
            `nblk:num`] WBN_TAG_NIST_BRIDGE) THEN
          REWRITE_TAC[BYTESWAP128_INVOLUTION] THEN DISCH_THEN MATCH_ACCEPT_TAC];
        MATCH_MP_TAC chain_thm THEN
        RULE_ASSUM_TAC(REWRITE_RULE
          [ALLPAIRS; PAIRWISE; ALL; MAP; NONOVERLAPPING_CLAUSES]) THEN
        REWRITE_TAC[ALLPAIRS; PAIRWISE; ALL; MAP; NONOVERLAPPING_CLAUSES] THEN
        REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN TRY(ASM_ARITH_TAC) THEN
        ASM_MESON_TAC[NONOVERLAPPING_MODULO_SYM; nonoverlapping]]] in
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `nblk <= 8` THENL
   [ASM_MESON_TAC[AESV8_GCM_8X_DEC_256_DISPATCH]; ALL_TAC] THEN
  ASM_CASES_TAC `nblk <= 16` THENL
   [WBN_CHAIN_TO_NIST_TAC WBN_FRONT_TO_END_916;
    WBN_CHAIN_TO_NIST_TAC WBN_FRONT_TO_END]);;

(* ------------------------------------------------------------------------- *)
(* PHASE 8: WBN_DEC_SUBROUTINE_BYTELIST -- the ABI subroutine                  *)
(* wrapper spine (H free, byte_list output; the exported _SUBROUTINE_CORRECT   *)
(* is lifted from it below).                                                   *)
(* The ABI subroutine wrapper for the whole-blocks path (bit_len = 128*nblk,   *)
(* any nblk >= 0).  The nblk = 0 leg is folded in (the entry cbz x1            *)
(* is TAKEN, returns 0, empty output, tag unchanged) so this single theorem is  *)
(* the external whole-blocks contract, matching the encrypt _GEN shape.  The   *)
(* nblk >= 1 leg is unchanged (below); the guard fall-through and              *)
(* core-crossing machinery are exactly as before.                              *)
(* Binary                                                                       *)
(* layout (objdump): the entry GUARD (nop;cbz x1;ands zr,x1,#0x7f;b.ne, offs   *)
(* 0x0..0xc) precedes the d8-d15 callee-save spills (stp d8,d9,[sp,#-80]!;      *)
(* stp d10,d11;d12,d13;d14,d15, offs 0x10..0x1c); the core runs pc+0x20..pc+   *)
(* 0x11ac (= the core); the epilogue (mov x0,x9; ldp d10..d15; ldp d8,d9,[sp], *)
(* #80; ret, offs 0x11b0..0x11c4) restores.  X30 is NOT saved (returns via LR).*)
(*                                                                             *)
(* Stock ARM_ADD_RETURN_STACK_TAC does not apply: the guard's b.ne sits in the *)
(* prologue (its ARM_STEPS stalls on the symbolic conditional-PC) and the SP   *)
(* offset needs the core instantiated by hand.  So the wrapper is hand-rolled: *)
(*  - WB_CORE_INST = WBN_DEC_CORE_BYTELIST SPECL'd stackpointer := word_sub     *)
(*    stackpointer                                                              *)
(*    (word 80) (so the in-frame SP = the caller SP after the prologue's        *)
(*    stp ...,[sp,#-80]!);                                                      *)
(*  - WB_CORE_INST_UF2 unfolds the folded input mem predicates (byte_list_at /  *)
(*    wordlist_from_memory / htable_mem_8) AND concretizes val(word(16*nblk)) = *)
(*    16*nblk (from 128*nblk<2 EXP 62) so ARM_STEPS carries the quantified      *)
(*    input byte read past the disjoint stack stores (else it drops it);        *)
(*  - WB_GUARD_FALLTHROUGH_TAC injects the guard fall-through facts             *)
(*    (val(word(128*nblk))=128*nblk; ~(128*nblk=0); val(word_and .. 127)=0) so  *)
(*    the prologue steps clean; then ARM_STEPS 1--8 (guard+saves), ARM_BIGSTEP  *)
(*    s9 (crosses the core), ARM_STEPS 10--15 (epilogue), ENSURES_FINAL.        *)
(* The d8-d15 preservation now closes because the F1-narrowed core frame        *)
(* bytes(sp+64,16) is DISJOINT from the [sp,64) spill area.                     *)
(* Inherits _CORRECT's soundness: CHEAT-free, no new_axiom.                     *)
(* ------------------------------------------------------------------------- *)

let WBN_DEC_SUBROUTINE_BYTELIST = prove
   (`!pc stackpointer in_p out_p xi_p ivec_p key_p htbl_p nblk ibytes rk H
      tag0 ctr0 returnaddress.
      128 * nblk < 2 EXP 62 /\
      val in_p + 16 * nblk < 2 EXP 63 /\
      LENGTH ibytes = 16 * nblk /\
      LENGTH rk = 15 /\
      aligned 16 stackpointer /\
      ALLPAIRS nonoverlapping [out_p,16 * nblk; xi_p,16; ivec_p,16]
      [word pc, LENGTH aesv8_gcm_8x_dec_256_wb_mc; in_p,16 * nblk; key_p,240; htbl_p,192;
       word_sub stackpointer (word 80),80] /\
      PAIRWISE nonoverlapping [out_p,16 * nblk; xi_p,16; ivec_p,16] /\
      ALL (nonoverlapping (word_sub stackpointer (word 80),80))
      [word pc, LENGTH aesv8_gcm_8x_dec_256_wb_mc; in_p,16 * nblk; key_p,240; htbl_p,192]
      ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) aesv8_gcm_8x_dec_256_wb_mc /\
               read PC s = word pc /\
               read SP s = stackpointer /\
               read X30 s = returnaddress /\
               C_ARGUMENTS
               [in_p; word (128 * nblk); out_p; xi_p; ivec_p; key_p; htbl_p]
               s /\
               byte_list_at ibytes in_p (word (16 * nblk)) s /\
               read (memory :> bytes128 xi_p) s = word_reversefields 8 tag0 /\
               read (memory :> bytes128 ivec_p) s = ctr0 /\
               wordlist_from_memory (key_p,15) s = rk /\
               htable_mem_8 (ghash_twist H) htbl_p s)
          (\s. read PC s = returnaddress /\
               byte_list_at (gcm_dec_pt_bytes (16 * nblk) ibytes ctr0 rk) out_p
               (word (16 * nblk)) s /\
               read (memory :> bytes128 xi_p) s =
               word_reversefields 8
               (nist_ghash H tag0 (list_of_seq (nist_input_block ibytes) nblk)) /\
               read (memory :> bytes128 ivec_p) s = gcm_ctr_inc_iter nblk ctr0)
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE
           [memory :> bytes (out_p,16 * nblk); memory :> bytes (xi_p,16);
            memory :> bytes (ivec_p,16);
            memory :> bytes (word_sub stackpointer (word 80),80)])`,
  (* The wrapper is hand-rolled (see the PHASE 8 note above); these helper lets
     are local to the proof (JH idiom). *)
  let EXEC = AESV8_GCM_8X_DEC_256_WB_EXEC in
  (* the core, SP set to the post-prologue in-frame value *)
  let WB_CORE_INST =
    SPECL [`pc:num`; `word_sub stackpointer (word 80):int64`;
           `in_p:int64`; `out_p:int64`; `xi_p:int64`; `ivec_p:int64`;
           `key_p:int64`; `htbl_p:int64`; `nblk:num`; `ibytes:byte list`;
           `rk:int128 list`; `H:int128`; `tag0:int128`; `ctr0:int128`]
          WBN_DEC_CORE_BYTELIST in
  (* val(word(16*nblk))=16*nblk from 128*nblk<2 EXP 62 (so 16*nblk<2 EXP 64) *)
  let VAL16EQ = prove
   (`128 * nblk < 2 EXP 62 ==> val (word (16 * nblk):int64) = 16 * nblk`,
    DISCH_TAC THEN MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    ASM_ARITH_TAC) in
  (* unfold folded input mem preds + concretize the byte bound in the core *)
  let WB_CORE_INST_UF2 =
    REWRITE_RULE[byte_list_at; wordlist_from_memory; htable_mem_8; DIMINDEX_128;
                 fst EXEC; UNDISCH VAL16EQ] WB_CORE_INST in
  (* guard fall-through: cbz/b.ne both fall through for bit_len = 128*nblk *)
  let WB_GUARD_FALLTHROUGH_TAC =
    SUBGOAL_THEN `val (word (128 * nblk):int64) = 128 * nblk` ASSUME_TAC THENL
     [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `~(128 * nblk = 0)` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `val (word_and (word (128 * nblk):int64) (word 127)) = 0`
      ASSUME_TAC THENL
     [SUBGOAL_THEN `(127:num) = 2 EXP 7 - 1` SUBST1_TAC THENL
       [CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
      REWRITE_TAC[VAL_WORD_AND_MASK_WORD] THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `(2:num) EXP 7 = 128` SUBST1_TAC THENL
       [CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
      REWRITE_TAC[MOD_MULT];
      ALL_TAC] in
  REWRITE_TAC[byte_list_at; wordlist_from_memory; htable_mem_8; DIMINDEX_128;
                fst EXEC] THEN
    REWRITE_TAC[NONOVERLAPPING_CLAUSES; PAIRWISE; ALLPAIRS; ALL] THEN
    REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN
    REPEAT GEN_TAC THEN
    DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
    (* nblk = 0: the entry cbz x1 (0x4) is TAKEN before the prologue, so the
       function returns 0 in X0 touching no memory (mov w0,#0; ret @0x136c,
       moved to the end when the exact-8 drain was appended);
       d8-d15/SP are untouched (never spilled).  The output byte list is empty
       (byte_list_at over word 0 is vacuous) and the tag is unchanged
       (nist_ghash H tag0 [] = tag0).  Mirrors the encrypt nb=0 leg. *)
    ASM_CASES_TAC `nblk = 0` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN
      REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; ARITH_RULE `128 * 0 = 0`;
                  ARITH_RULE `16 * 0 = 0`] THEN
      REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; MODIFIABLE_SIMD_REGS;
        MODIFIABLE_GPRS; MODIFIABLE_UPPER_SIMD_REGS; fst EXEC] THEN
      ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC EXEC (1--4) THEN
      ENSURES_FINAL_STATE_TAC THEN
      ASM_REWRITE_TAC[byte_list_at; list_of_seq; nist_ghash; VAL_WORD_0;
                      ARITH_RULE `i < 0 <=> F`; gcm_ctr_inc_iter];
      ALL_TAC] THEN
    SUBGOAL_THEN `1 <= nblk` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `val (word (16 * nblk):int64) = 16 * nblk` ASSUME_TAC THENL
     [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC WB_CORE_INST_UF2 THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[NONOVERLAPPING_CLAUSES; PAIRWISE; ALLPAIRS; ALL] THEN
      REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
      MATCH_MP_TAC ALIGNED_WORD_SUB THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[aligned; WORD_VAL] THEN CONV_TAC WORD_REDUCE_CONV THEN
      REWRITE_TAC[DIMINDEX_64] THEN CONJ_TAC THEN CONV_TAC NUM_DIVIDES_CONV;
      ALL_TAC] THEN
    REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; MODIFIABLE_SIMD_REGS;
       MODIFIABLE_GPRS; MODIFIABLE_UPPER_SIMD_REGS; fst EXEC] THEN
    DISCH_THEN(fun th ->
      (ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
       MAP_EVERY (fun c -> ENSURES_PRESERVED_DREG_TAC ("init_"^fst(dest_const c)) c)
         [`D8`;`D9`;`D10`;`D11`;`D12`;`D13`;`D14`;`D15`]) THEN
      REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
      RULE_ASSUM_TAC(REWRITE_RULE[WB_MC_LEN]) THEN
      WB_GUARD_FALLTHROUGH_TAC THEN
      ARM_STEPS_TAC EXEC (1--8) THEN MP_TAC th) THEN
    ARM_BIGSTEP_TAC EXEC "s9" THENL
     [REWRITE_TAC[C_ARGUMENTS] THEN ASM_REWRITE_TAC[];
      REWRITE_TAC(!simulation_precanon_thms) THEN ARM_STEPS_TAC EXEC (10--15) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[WORD_BLAST `(word_zx:int128->int64)(word_zx(x:int64)) = x`] THEN
      CONV_TAC WORD_RULE]);;

(* ------------------------------------------------------------------------- *)
(* Bridge: the whole-buffer byte-list output collapses to the                   *)
(* per-block, NIST-nonce-named keystream form the two exported theorems below   *)
(* ship.  byte_list_at(gcm_dec_pt_bytes ..) -> !j<nblk. read bytes128(out+16j)  *)
(* = pt_j XOR E_K(nonce||(c+j)), given word_bytereverse ctr0 = ctr_block nonce  *)
(* c.  Combines WBN_OUTPUT_POINTWISE (byte_list -> EL j of aes_ctr, s079),       *)
(* EL_AES_CTR (element = pt XOR E_K(counter)) and GCM_CTR_INC_ITER_CTR_BLOCK    *)
(* (our gcm_ctr_inc_iter counter = the byte-reversed NIST nonce||(c+j) block).  *)
(* ------------------------------------------------------------------------- *)
let WBN_OUTPUT_POINTWISE_NONCE = prove
 (`!nblk ibytes ctr0 rk out_p s nonce c.
     1 <= nblk /\ 128 * nblk < 2 EXP 62 /\
     word_bytereverse ctr0 = ctr_block nonce c /\
     byte_list_at (gcm_dec_pt_bytes (16 * nblk) ibytes ctr0 rk)
                  out_p (word (16 * nblk)) s
     ==> !j. j < nblk
             ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
                 word_xor (EL j (gcm_dec_blocks_from 0 nblk ibytes))
                          (aes256_encrypt
                             (word_bytereverse (ctr_block nonce (c + j))) rk)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  MP_TAC(SPECL [`nblk:num`; `ibytes:byte list`; `ctr0:int128`; `rk:int128 list`;
               `out_p:int64`; `s:armstate`] WBN_OUTPUT_POINTWISE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `j:num`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(SPECL [`gcm_dec_blocks_from 0 nblk ibytes`; `ctr0:int128`;
               `rk:int128 list`; `j:num`] EL_AES_CTR) THEN
  REWRITE_TAC[LENGTH_GCM_DEC_BLOCKS_FROM] THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(SPECL [`j:num`; `nonce:96 word`; `c:num`; `ctr0:int128`]
    GCM_CTR_INC_ITER_CTR_BLOCK) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REFL_TAC);;

(* ------------------------------------------------------------------------- *)
(* ABSTRACT INDEXED-INPUT bridges: re-present the exported                     *)
(* contracts over an ABSTRACT input function `inblock : num -> int128` pinned   *)
(* by a per-block read hypothesis, matching the sibling AES-GCM proofs'         *)
(* shape (input abstract, pinned by hypothesis).  The internal byte-list spine  *)
(* is instantiated with the concrete witness                                    *)
(*   ibytes := int128_list_to_bytes (list_of_seq inblock nblk)                  *)
(* and these lemmas discharge the spine's byte_list_at precondition and rewrite *)
(* its EL/nist_input_block byte-list vocabulary back to `inblock`.  Sim-free.   *)
(* ------------------------------------------------------------------------- *)

(* pointwise list_of_seq congruence (only the values at i < n matter). *)
let LIST_OF_SEQ_EQ_PTWISE = prove
 (`!(f:num->B) g n. (!i. i < n ==> f i = g i) ==> list_of_seq f n = list_of_seq g n`,
  ONCE_REWRITE_TAC[MESON[] `(!f g n. P f g n) <=> (!n f g. P f g n)`] THEN
  INDUCT_TAC THEN REWRITE_TAC[LIST_OF_SEQ] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `(f:num->B) 0 = g 0` SUBST1_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
  AP_TERM_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o
    check (fun th -> is_forall(concl th))) THEN
  X_GEN_TAC `i:num` THEN REWRITE_TAC[o_THM] THEN DISCH_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC);;

(* INPUT ASSEMBLER: the per-block int128 reads (= inblock j) assemble into the  *)
(* byte_list_at precondition the spine expects, at ibytes = the flattened list. *)
(* The mirror of WBN_OUTPUT_POINTWISE (byte_list_at -> per-block reads); here    *)
(* per-block reads -> byte_list_at.                                             *)
let WBN_INPUT_ASSEMBLE = prove
 (`!inblock nblk in_p s.
     128 * nblk < 2 EXP 62 /\
     (!j. j < nblk
          ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s =
              inblock j)
     ==> byte_list_at (int128_list_to_bytes (list_of_seq inblock nblk)) in_p
                      (word (16 * nblk)) s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[byte_list_at] THEN
  SUBGOAL_THEN `val (word (16 * nblk):int64) = 16 * nblk` SUBST1_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    MP_TAC(ASSUME `128 * nblk < 2 EXP 62`) THEN ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `i DIV 16 < nblk` ASSUME_TAC THENL
   [SUBGOAL_THEN `i < 16 * nblk` MP_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SIMP_TAC[RDIV_LT_EQ; ARITH_EQ] THEN ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`list_of_seq (inblock:num->int128) nblk`; `i:num`]
    EL_INT128_LIST_TO_BYTES) THEN
  REWRITE_TAC[LENGTH_LIST_OF_SEQ] THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  ASM_SIMP_TAC[EL_LIST_OF_SEQ] THEN
  SUBGOAL_THEN
    `word_add in_p (word i):int64 =
     word_add (word_add in_p (word (16 * (i DIV 16)))) (word (i MOD 16))`
    SUBST1_TAC THENL
   [SUBGOAL_THEN `i = 16 * (i DIV 16) + i MOD 16`
      (fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV) [th]) THENL
     [MESON_TAC[DIVISION_SIMP]; ALL_TAC] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  MP_TAC(SPECL [`word_add in_p (word (16 * (i DIV 16))):int64`; `s:armstate`;
                `i MOD 16`] BYTE8_OF_BYTES128) THEN
  ANTS_TAC THENL [REWRITE_TAC[MOD_LT_EQ; ARITH_EQ]; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  FIRST_X_ASSUM(fun th ->
    if is_forall(concl th) then MP_TAC(SPEC `i DIV 16` th) else NO_TAC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REFL_TAC);;

(* identity A: input block j read off the assembled ibytes IS inblock j.        *)
let INBLOCK_OF_ASSEMBLED = prove
 (`!inblock nblk j. j < nblk
     ==> bytes_to_int128
           (SUB_LIST (16 * j,16)
             (int128_list_to_bytes (list_of_seq inblock nblk))) = inblock j`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`list_of_seq (inblock:num->int128) nblk`; `j:num`]
    SUB_LIST_INT128_LIST_TO_BYTES_EL) THEN
  REWRITE_TAC[LENGTH_LIST_OF_SEQ] THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC[EL_LIST_OF_SEQ]);;

(* identity A': gcm_dec_blocks_from over the assembled ibytes IS inblock.       *)
let GCM_DEC_BLOCKS_FROM_ASSEMBLED = prove
 (`!inblock nblk j. j < nblk
     ==> EL j (gcm_dec_blocks_from 0 nblk
                 (int128_list_to_bytes (list_of_seq inblock nblk))) = inblock j`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`nblk:num`; `0`; `j:num`;
                `int128_list_to_bytes (list_of_seq (inblock:num->int128) nblk)`]
         EL_GCM_DEC_BLOCKS_FROM) THEN
  ASM_REWRITE_TAC[ADD_CLAUSES] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_SIMP_TAC[INBLOCK_OF_ASSEMBLED]);;

(* identity B: the GHASH input list over the assembled ibytes IS the NIST       *)
(* (big-endian) view of inblock, i.e. word_bytereverse o inblock.  (For decrypt *)
(* GHASH runs over the CIPHERTEXT = the INPUT, so this is the input analogue of  *)
(* nist_cipher_block; nist_input_block is exactly that role.)                  *)
let NIST_INPUT_OF_ASSEMBLED = prove
 (`!inblock nblk.
     list_of_seq
       (nist_input_block (int128_list_to_bytes (list_of_seq inblock nblk))) nblk =
     list_of_seq (\i. word_bytereverse (inblock i)) nblk`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC LIST_OF_SEQ_EQ_PTWISE THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  REWRITE_TAC[nist_input_block] THEN
  MP_TAC(SPECL [`inblock:num->int128`; `nblk:num`; `i:num`] INBLOCK_OF_ASSEMBLED) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[GSYM BREV_RF8_128]);;


(* ------------------------------------------------------------------------- *)
(* Loop invariant in the shared NIST SP 800-38D vocabulary.                    *)
(*                                                                             *)
(* wbn_loop_invariant_raw (above) is stated in the raw per-register dialect the    *)
(* symbolic simulation produces (gcm_ctr_add/gcm_ctr_raw counters, aes13       *)
(* keystream towers, a ghash_polyval_acc accumulator over byte-reversed        *)
(* SUB_LIST inputs, htable_mem_dec, individual key slots k0..k14).             *)
(* wbn_loop_invariant below re-presents the SAME machine state in the     *)
(* vocabulary the sibling AES-GCM proofs use (ctr_block nonce / aes_ctr_block  *)
(* / nist_ghash / htable_mem_8 / EL n rk), and WBN_LOOP_INV_VOCAB proves the    *)
(* two coincide under the standard adapter hypotheses.  The GHASH accumulator  *)
(* is the PLAIN nist_ghash form (no byteswap128 wrapper): the loop accumulator *)
(* is the pre-tag-store value, and the tag store is where the outer            *)
(* byte-reversal enters, so WBN_TAG_NIST_BRIDGE's outer word_bytereverse       *)
(* strips off (WBN_LOOP_Q19_NIST).                                             *)
(* ------------------------------------------------------------------------- *)

(* counter register Q0..Q4: gcm_ctr_add is a byte-reversed NIST counter block. *)
let CTR_ADD_AS_CTR_BLOCK = prove
 (`!m (nonce:96 word) c ctr0.
     word_bytereverse ctr0 = ctr_block nonce c
     ==> gcm_ctr_add (word m) ctr0 = word_reversefields 8 (ctr_block nonce (c + m))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM GCM_CTR_INC_ITER_ADD] THEN
  MP_TAC(SPECL [`m:num`;`nonce:96 word`;`c:num`;`ctr0:int128`]
    GCM_CTR_INC_ITER_CTR_BLOCK) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[BREV_RF8_128]);;

(* raw counter register Q30: gcm_ctr_raw is a 32-field reverse of gcm_ctr_add. *)
let RAW_IS_RF32_BREV_ADD = prove
 (`!m ctr0. gcm_ctr_raw (word m) ctr0 =
            word_reversefields 32 (word_bytereverse (gcm_ctr_add (word m) ctr0))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[gcm_ctr_raw_def; gcm_ctr_add] THEN
  REWRITE_TAC[GSYM BREV_TOP_LANE] THEN
  ABBREV_TAC `t:32 word = word_bytereverse (word_subword (ctr0:int128) (96,32):32 word)` THEN
  ABBREV_TAC `p:32 word = word_add t (word m)` THEN
  CONV_TAC WORD_BLAST);;

let BREV_RF8_INV = prove
 (`!y:int128. word_bytereverse (word_reversefields 8 y) = y`,
  GEN_TAC THEN REWRITE_TAC[GSYM(REWRITE_RULE[FUN_EQ_THM] WORD_BYTEREVERSE_REVERSEFIELDS)] THEN
  REWRITE_TAC[WORD_BYTEREVERSE_BYTEREVERSE]);;

let Q30_TEMPLATE = prove
 (`!m ctr0 (kb:int128).
     gcm_ctr_add (word m) ctr0 = word_reversefields 8 kb
     ==> gcm_ctr_raw (word m) ctr0 = word_reversefields 32 kb`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[RAW_IS_RF32_BREV_ADD] THEN
  ASM_REWRITE_TAC[BREV_RF8_INV]);;

let CTR_RAW_AS_CTR_BLOCK = prove
 (`!m (nonce:96 word) c ctr0.
     word_bytereverse ctr0 = ctr_block nonce c
     ==> gcm_ctr_raw (word m) ctr0 = word_reversefields 32 (ctr_block nonce (c + m))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC Q30_TEMPLATE THEN
  MATCH_MP_TAC CTR_ADD_AS_CTR_BLOCK THEN ASM_REWRITE_TAC[]);;

(* Q19 accumulator: the plain nist_ghash form (WBN_TAG_NIST_BRIDGE stripped of  *)
(* its outer injective word_bytereverse).                                       *)
let WBN_LOOP_Q19_NIST = prove
 (`!(H:int128) h xi tag0 ibytes N.
     byteswap128 h = ghash_twist H /\ xi = word_reversefields 8 tag0
     ==> ghash_polyval_acc (byteswap128 h) (word_bytereverse xi)
           (MAP word_bytereverse
             (list_of_seq (\k. bytes_to_int128 (SUB_LIST (16 * k,16) ibytes)) N)) =
         nist_ghash H tag0 (list_of_seq (nist_input_block ibytes) N)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`H:int128`;`h:int128`;`xi:int128`;`tag0:int128`;
               `ibytes:byte list`;`N:num`] WBN_TAG_NIST_BRIDGE) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM BREV_RF8_128] THEN
  DISCH_THEN(MP_TAC o AP_TERM `word_bytereverse:int128->int128`) THEN
  REWRITE_TAC[WORD_BYTEREVERSE_BYTEREVERSE]);;

(* The shared-vocabulary loop invariant.  Same machine state as                *)
(* wbn_loop_invariant_raw; the parameters are the NIST ones (nonce, counter base c, *)
(* abstract indexed input `inblock`, initial tag `tag0`, round-key list `rk`)   *)
(* rather than the raw ctr0/ibytes/xi/h/k0..k14.  The two-stream pipeline lag   *)
(* (stores/counters at 8(i+1), GHASH at 8i) is preserved verbatim.              *)
let wbn_loop_invariant = new_definition
 `wbn_loop_invariant (pc:num) (nonce:96 word) (c:num) (in_p:int64) (out_p:int64)
    (xi_p:int64) (ivec_p:int64) (key_p:int64) (htbl_p:int64) (stackpointer:int64)
    (nblk:num) (inblock:num->int128) (tag0:int128) (rk:int128 list) =
  \(i:num) (s:armstate).
    aligned_bytes_loaded s (word pc) aesv8_gcm_8x_dec_256_wb_mc /\
    read PC s = word (pc + 1216) /\
    read Q0 s = word_reversefields 8 (ctr_block nonce (c + (8 * i + 8))) /\
    read Q1 s = word_reversefields 8 (ctr_block nonce (c + (8 * i + 9))) /\
    read Q2 s = word_reversefields 8 (ctr_block nonce (c + (8 * i + 10))) /\
    read Q3 s = word_reversefields 8 (ctr_block nonce (c + (8 * i + 11))) /\
    read Q4 s = word_reversefields 8 (ctr_block nonce (c + (8 * i + 12))) /\
    read Q5 s = word_xor (aes_ctr_block nonce rk (c + (8 * i + 5))) (inblock (8 * i + 5)) /\
    read Q6 s = word_xor (aes_ctr_block nonce rk (c + (8 * i + 6))) (inblock (8 * i + 6)) /\
    read Q7 s = word_xor (aes_ctr_block nonce rk (c + (8 * i + 7))) (inblock (8 * i + 7)) /\
    read Q8 s = inblock (8 * i + 0) /\
    read Q9 s = inblock (8 * i + 1) /\
    read Q10 s = inblock (8 * i + 2) /\
    read Q11 s = inblock (8 * i + 3) /\
    read Q12 s = inblock (8 * i + 4) /\
    read Q13 s = inblock (8 * i + 5) /\
    read Q14 s = inblock (8 * i + 6) /\
    read Q15 s = inblock (8 * i + 7) /\
    read Q19 s =
      nist_ghash (aes256_encrypt (word 0) rk) tag0
        (list_of_seq (\k. word_bytereverse (inblock k)) (8 * i)) /\
    read X0 s = word_add in_p (word (128 * (i + 1))) /\
    read X2 s = word_add out_p (word (128 * (i + 1))) /\
    read X4 s = word_add in_p (word (16 * nblk)) /\
    read X5 s = word_add (word (128 * (nblk - 1) DIV 8)) in_p /\
    read X9 s = word (16 * nblk) /\
    read X10 s = word_add stackpointer (word 64) /\
    read X1 s = word (128 * nblk) /\
    read X15 s = word 4294967296 /\
    read Q31 s = word 79228162514264337593543950336 /\
    read Q30 s = word_reversefields 32 (ctr_block nonce (c + (8 * i + 13))) /\
    read X16 s = ivec_p /\
    read X6 s = htbl_p /\
    read X3 s = xi_p /\
    read X11 s = key_p /\
    read SP s = stackpointer /\
    read (memory :> bytes64 (word_add stackpointer (word 64))) s =
      word 13979173243358019584 /\
    (!j. j < 8 * (i + 1)
         ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
             word_xor (aes_ctr_block nonce rk (c + j)) (inblock j)) /\
    (!j. j < nblk
         ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s = inblock j) /\
    read (memory :> bytes128 key_p) s = EL 0 rk /\
    read (memory :> bytes128 (word_add key_p (word 16))) s = EL 1 rk /\
    read (memory :> bytes128 (word_add key_p (word 32))) s = EL 2 rk /\
    read (memory :> bytes128 (word_add key_p (word 48))) s = EL 3 rk /\
    read (memory :> bytes128 (word_add key_p (word 64))) s = EL 4 rk /\
    read (memory :> bytes128 (word_add key_p (word 80))) s = EL 5 rk /\
    read (memory :> bytes128 (word_add key_p (word 96))) s = EL 6 rk /\
    read (memory :> bytes128 (word_add key_p (word 112))) s = EL 7 rk /\
    read (memory :> bytes128 (word_add key_p (word 128))) s = EL 8 rk /\
    read (memory :> bytes128 (word_add key_p (word 144))) s = EL 9 rk /\
    read (memory :> bytes128 (word_add key_p (word 160))) s = EL 10 rk /\
    read (memory :> bytes128 (word_add key_p (word 176))) s = EL 11 rk /\
    read (memory :> bytes128 (word_add key_p (word 192))) s = EL 12 rk /\
    read (memory :> bytes128 (word_add key_p (word 208))) s = EL 13 rk /\
    read (memory :> bytes128 (word_add key_p (word 224))) s = EL 14 rk /\
    htable_mem_8 (ghash_twist (aes256_encrypt (word 0) rk)) htbl_p s`;;

(* Per-block keystream: the raw aes13 store tower over the assembled input IS   *)
(* the NIST aes_ctr_block XOR the input block (rk the literal 15-key list).      *)
let KEYSTREAM_ENDBLOCK_NIST = prove
 (`!inblock nblk ctr0 (nonce:96 word) c k0 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 k11 k12 k13 k14 j.
     j < nblk /\
     word_bytereverse ctr0 = ctr_block nonce c
     ==> word_xor
           (word_xor (bytes_to_int128 (SUB_LIST (16 * j,16)
                        (int128_list_to_bytes (list_of_seq inblock nblk))))
             (aes13 (gcm_ctr_inc_iter j ctr0) k0 k1 k2 k3 k4 k5 k6 k7 k8 k9
                    k10 k11 k12 k13))
           k14 =
         word_xor
           (aes_ctr_block nonce [k0;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14]
              (c + j))
           (inblock j)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`nblk:num`;
               `int128_list_to_bytes (list_of_seq (inblock:num->int128) nblk)`;
               `ctr0:int128`;`k0:int128`;`k1:int128`;`k2:int128`;`k3:int128`;`k4:int128`;
               `k5:int128`;`k6:int128`;`k7:int128`;`k8:int128`;`k9:int128`;`k10:int128`;
               `k11:int128`;`k12:int128`;`k13:int128`;`k14:int128`;`j:num`]
    WBN_ENDBLOCK_IS_AES_CTR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(SPECL [`gcm_dec_blocks_from 0 nblk
                  (int128_list_to_bytes (list_of_seq (inblock:num->int128) nblk))`;
               `ctr0:int128`;
               `[k0;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14]:int128 list`;`j:num`]
    EL_AES_CTR) THEN
  REWRITE_TAC[LENGTH_GCM_DEC_BLOCKS_FROM] THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(SPECL [`inblock:num->int128`;`nblk:num`;`j:num`] GCM_DEC_BLOCKS_FROM_ASSEMBLED) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(SPECL [`j:num`;`nonce:96 word`;`c:num`;`ctr0:int128`]
    GCM_CTR_INC_ITER_CTR_BLOCK) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[aes_ctr_block] THEN CONV_TAC WORD_BITWISE_RULE);;

(* congruence lifting the per-block keystream identity under the store-forall.  *)
let STORE_FORALL_CONG_KS = prove
 (`!(A:num->int128) inblock nblk ctr0 (nonce:96 word) c
     k0 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 k11 k12 k13 k14 i.
     8 * (i + 1) <= nblk /\
     word_bytereverse ctr0 = ctr_block nonce c
     ==> ((!j. j < 8 * (i + 1)
              ==> A j =
                  word_xor
                    (word_xor (bytes_to_int128 (SUB_LIST (16 * j,16)
                        (int128_list_to_bytes (list_of_seq inblock nblk))))
                      (aes13 (gcm_ctr_inc_iter j ctr0) k0 k1 k2 k3 k4 k5 k6 k7 k8 k9
                             k10 k11 k12 k13))
                    k14) <=>
          (!j. j < 8 * (i + 1)
              ==> A j = word_xor
                          (aes_ctr_block nonce
                             [k0;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14]
                             (c + j))
                          (inblock j)))`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(MESON[] `(!j. j < K ==> (f j = g j)) ==>
     ((!j. j < K ==> A j = f j) <=> (!j. j < K ==> A j = g j))`) THEN
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  MATCH_MP_TAC KEYSTREAM_ENDBLOCK_NIST THEN ASM_REWRITE_TAC[] THEN
  ASM_ARITH_TAC);;

(* GHASH input list over the assembled input, prefix-N form. *)
let NIST_INPUT_OF_ASSEMBLED_PREFIX = prove
 (`!inblock nblk N. N <= nblk
     ==> list_of_seq
           (nist_input_block (int128_list_to_bytes (list_of_seq inblock nblk))) N =
         list_of_seq (\i. word_bytereverse (inblock i)) N`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LIST_OF_SEQ_EQ_PTWISE THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  REWRITE_TAC[nist_input_block] THEN
  MP_TAC(SPECL [`inblock:num->int128`;`nblk:num`;`i:num`] INBLOCK_OF_ASSEMBLED) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[GSYM BREV_RF8_128]);;

(* Q19 accumulator over the assembled input = nist_ghash, in the form the       *)
(* equivalence goal presents after the ghash_twist/word_reversefields adapters. *)
let Q19_NIST_ASSEMBLED = prove
 (`!(H:int128) tag0 inblock nblk N.
     N <= nblk
     ==> ghash_polyval_acc (ghash_twist H)
           (word_bytereverse (word_reversefields 8 tag0))
           (MAP word_bytereverse
             (list_of_seq (\k. bytes_to_int128 (SUB_LIST (16 * k,16)
                (int128_list_to_bytes (list_of_seq inblock nblk)))) N)) =
         nist_ghash H tag0 (list_of_seq (\i. word_bytereverse (inblock i)) N)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`H:int128`;
               `byteswap128 (ghash_twist H):int128`;
               `word_reversefields 8 (tag0:int128)`;
               `tag0:int128`;
               `int128_list_to_bytes (list_of_seq (inblock:num->int128) nblk):byte list`;
               `N:num`]
    WBN_LOOP_Q19_NIST) THEN
  REWRITE_TAC[BYTESWAP128_INVOLUTION] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_SIMP_TAC[NIST_INPUT_OF_ASSEMBLED_PREFIX]);;

(* input buffer: the whole-buffer byte read = the per-block bytes128 reads.      *)
let INPUT_FORALL_IFF = prove
 (`!inblock nblk in_p s.
     128 * nblk < 2 EXP 62
     ==> (read (memory :> bytes (in_p,16 * nblk)) s =
            num_of_bytelist (int128_list_to_bytes (list_of_seq inblock nblk)) <=>
          (!j. j < nblk
               ==> read (memory :> bytes128 (word_add in_p (word (16 * j)))) s = inblock j))`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(SPECL [`nblk:num`;`in_p:int64`;
                  `int128_list_to_bytes (list_of_seq (inblock:num->int128) nblk)`;
                  `s:armstate`] INPUT_BYTES_TO_BYTE128_LANES) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[LENGTH_INT128_LIST_TO_BYTES; LENGTH_LIST_OF_SEQ; LE_REFL] THEN
      SUBGOAL_THEN `SUB_LIST (0,16 * nblk)
         (int128_list_to_bytes (list_of_seq (inblock:num->int128) nblk)) =
         int128_list_to_bytes (list_of_seq inblock nblk)`
        (fun th -> ASM_REWRITE_TAC[th]) THEN
      MATCH_MP_TAC SUB_LIST_LENGTH_IMPLIES THEN
      REWRITE_TAC[LENGTH_INT128_LIST_TO_BYTES; LENGTH_LIST_OF_SEQ; LE_REFL];
      ALL_TAC] THEN
    DISCH_TAC THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `j:num`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC INBLOCK_OF_ASSEMBLED THEN ASM_REWRITE_TAC[];
    DISCH_TAC THEN
    MP_TAC(SPECL [`16 * nblk`;`in_p:int64`;
                  `int128_list_to_bytes (list_of_seq (inblock:num->int128) nblk)`;
                  `s:armstate`] BYTE_LIST_TO_NUM_THM) THEN
    REWRITE_TAC[LENGTH_INT128_LIST_TO_BYTES; LENGTH_LIST_OF_SEQ; LE_REFL] THEN
    SUBGOAL_THEN `SUB_LIST (0,16 * nblk)
       (int128_list_to_bytes (list_of_seq (inblock:num->int128) nblk)) =
       int128_list_to_bytes (list_of_seq inblock nblk)`
      SUBST1_TAC THENL
     [MATCH_MP_TAC SUB_LIST_LENGTH_IMPLIES THEN
      REWRITE_TAC[LENGTH_INT128_LIST_TO_BYTES; LENGTH_LIST_OF_SEQ; LE_REFL]; ALL_TAC] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN
    MP_TAC(SPECL [`inblock:num->int128`;`nblk:num`;`in_p:int64`;`s:armstate`]
      WBN_INPUT_ASSEMBLE) THEN
    ASM_REWRITE_TAC[byte_list_at] THEN
    SUBGOAL_THEN `val (word (16 * nblk):int64) = 16 * nblk` SUBST1_TAC THENL
     [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
      MP_TAC(ASSUME `128 * nblk < 2 EXP 62`) THEN ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[]]);;

(* The two invariants coincide under the standard adapter hypotheses plus the   *)
(* loop side-condition 8*(i+1) <= nblk (a theorem in the loop context, where     *)
(* i < (nblk-9) DIV 8).                                                          *)
let WBN_LOOP_INV_VOCAB = prove
 (`!pc ctr0 in_p out_p xi_p ivec_p key_p htbl_p stackpointer nblk ibytes xi h
     k0 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 k11 k12 k13 k14
     nonce c inblock tag0 rk i s.
     128 * nblk < 2 EXP 62 /\
     8 * (i + 1) <= nblk /\
     word_bytereverse ctr0 = ctr_block nonce c /\
     xi = word_reversefields 8 tag0 /\
     byteswap128 h = ghash_twist (aes256_encrypt (word 0) rk) /\
     rk = [k0;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14] /\
     ibytes = int128_list_to_bytes (list_of_seq inblock nblk)
     ==> (wbn_loop_invariant_raw pc ctr0 in_p out_p xi_p ivec_p key_p htbl_p stackpointer
            nblk ibytes xi h k0 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 k11 k12 k13 k14 i s <=>
          wbn_loop_invariant pc nonce c in_p out_p xi_p ivec_p key_p htbl_p
            stackpointer nblk inblock tag0 rk i s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check(fun th ->
    is_eq(concl th) && lhs(concl th) = `ibytes:byte list`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check(fun th ->
    is_eq(concl th) && lhs(concl th) = `rk:int128 list`)) THEN
  SUBGOAL_THEN `8 * i <= nblk` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
    `8*i+0<nblk /\ 8*i+1<nblk /\ 8*i+2<nblk /\ 8*i+3<nblk /\
     8*i+4<nblk /\ 8*i+5<nblk /\ 8*i+6<nblk /\ 8*i+7<nblk`
    STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[wbn_loop_invariant_raw; wbn_loop_invariant] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  ASM_SIMP_TAC[CTR_ADD_AS_CTR_BLOCK; CTR_RAW_AS_CTR_BLOCK;
               HTABLE_MEM_DEC_IS_HTABLE_MEM_8; INBLOCK_OF_ASSEMBLED;
               KEYSTREAM_ENDBLOCK_NIST; Q19_NIST_ASSEMBLED] THEN
  CONV_TAC(DEPTH_CONV EL_CONV) THEN
  ASM_SIMP_TAC[STORE_FORALL_CONG_KS; INPUT_FORALL_IFF] THEN
  REWRITE_TAC[]);;

(* Core (PC/decode-stripped) form of the vocabulary equivalence, the shape the  *)
(* recompose consumers thread (wbn_loop_inv_core_raw / wbn_core_applied).            *)
let wbn_loop_inv_core =
  let eqn = snd(strip_forall(concl wbn_loop_invariant)) in
  let lhs_full, rhs_full = dest_eq eqn in
  let hd, params = strip_comb lhs_full in
  let ivars, body = strip_abs rhs_full in
  let cs = conjuncts body in
  let core_body = list_mk_conj (List.tl (List.tl cs)) in
  let core_rhs = list_mk_abs(ivars, core_body) in
  let newhead = mk_var("wbn_loop_inv_core", type_of hd) in
  new_definition (mk_eq(list_mk_comb(newhead, params), core_rhs));;

let wbn_inv_nist_args =
  snd(strip_comb(fst(dest_eq(snd(strip_forall(concl wbn_loop_invariant))))));;

let WBN_INV_SPLIT = prove
 (list_mk_forall(wbn_inv_nist_args @ [`i:num`;`s:armstate`],
    mk_eq(
      list_mk_comb(`wbn_loop_invariant`, wbn_inv_nist_args @ [`i:num`;`s:armstate`]),
      list_mk_conj[
        `aligned_bytes_loaded s (word pc) aesv8_gcm_8x_dec_256_wb_mc`;
        `read PC s = word (pc + 1216)`;
        list_mk_comb(`wbn_loop_inv_core`, wbn_inv_nist_args @ [`i:num`;`s:armstate`])])),
  REWRITE_TAC[wbn_loop_invariant; wbn_loop_inv_core] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[CONJ_ACI]);;

(* wbn_loop_inv_core_raw <=> wbn_loop_inv_core under the same adapter hyps.  The *)
(* bridges act on the core conjuncts (no PC/aligned), so this is proved directly  *)
(* on the core defs — a full-invariant equivalence would not by itself entail a   *)
(* core one.                                                                      *)
let WBN_INV_CORE_VOCAB = prove
 (`!pc ctr0 in_p out_p xi_p ivec_p key_p htbl_p stackpointer nblk ibytes xi h
     k0 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 k11 k12 k13 k14
     nonce c inblock tag0 rk i s.
     128 * nblk < 2 EXP 62 /\
     8 * (i + 1) <= nblk /\
     word_bytereverse ctr0 = ctr_block nonce c /\
     xi = word_reversefields 8 tag0 /\
     byteswap128 h = ghash_twist (aes256_encrypt (word 0) rk) /\
     rk = [k0;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14] /\
     ibytes = int128_list_to_bytes (list_of_seq inblock nblk)
     ==> (wbn_loop_inv_core_raw pc ctr0 in_p out_p xi_p ivec_p key_p htbl_p stackpointer
            nblk ibytes xi h k0 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 k11 k12 k13 k14 i s <=>
          wbn_loop_inv_core pc nonce c in_p out_p xi_p ivec_p key_p htbl_p
            stackpointer nblk inblock tag0 rk i s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check(fun th ->
    is_eq(concl th) && lhs(concl th) = `ibytes:byte list`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check(fun th ->
    is_eq(concl th) && lhs(concl th) = `rk:int128 list`)) THEN
  SUBGOAL_THEN `8 * i <= nblk` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
    `8*i+0<nblk /\ 8*i+1<nblk /\ 8*i+2<nblk /\ 8*i+3<nblk /\
     8*i+4<nblk /\ 8*i+5<nblk /\ 8*i+6<nblk /\ 8*i+7<nblk`
    STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[wbn_loop_inv_core_raw; wbn_loop_inv_core] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  ASM_SIMP_TAC[CTR_ADD_AS_CTR_BLOCK; CTR_RAW_AS_CTR_BLOCK;
               HTABLE_MEM_DEC_IS_HTABLE_MEM_8; INBLOCK_OF_ASSEMBLED;
               KEYSTREAM_ENDBLOCK_NIST; Q19_NIST_ASSEMBLED] THEN
  CONV_TAC(DEPTH_CONV EL_CONV) THEN
  ASM_SIMP_TAC[STORE_FORALL_CONG_KS; INPUT_FORALL_IFF] THEN
  REWRITE_TAC[]);;


(* ------------------------------------------------------------------------- *)
(* The four named loop-invariant consumers, re-closed in the SHARED NIST      *)
(* vocabulary.  wbn_loop_inv_core (:above) and WBN_INV_SPLIT (:above) are      *)
(* already the shared derivations.  WBN_MAIN_LOOP and WBN_LOOP_INVARIANT_ENTRY *)
(* are transported from their _raw dialect proofs (WBN_MAIN_LOOP_raw,          *)
(* WBN_LOOP_INVARIANT_ENTRY_RAW) across the vocabulary equivalence: the body   *)
(* sim (which intrinsically produces dialect terms) is NOT re-run.  The        *)
(* transport supplies the standard adapter hypotheses (ctr0 is a byte-reversed *)
(* NIST counter block, xi/tag0 and h/H relate by the tag byte-reversal, rk is  *)
(* the concrete 15-key list, ibytes is the assembled input) and the loop       *)
(* side-condition 8*(i+1)<=nblk (a theorem in-loop, from 17<=nblk).            *)
(*                                                                             *)
(* WBN_INV_CORE_VOCAB (raw core <=> shared core) transports WBN_MAIN_LOOP;     *)
(* WBN_LOOP_INV_VOCAB (raw inv <=> shared inv) transports the ENTRY (whose     *)
(* postcondition carries the FULL invariant, not the PC/decode-stripped core). *)
(* ------------------------------------------------------------------------- *)

(* the shared PC/decode-free core applied to the 14 NIST params *)
let wbn_nist_core_applied =
  list_mk_comb(`wbn_loop_inv_core`,
    [`pc:num`;`nonce:96 word`;`c:num`;`in_p:int64`;`out_p:int64`;`xi_p:int64`;`ivec_p:int64`;
     `key_p:int64`;`htbl_p:int64`;`stackpointer:int64`;`nblk:num`;`inblock:num->int128`;
     `tag0:int128`;`rk:int128 list`]);;
(* the shared FULL invariant applied to the 14 NIST params *)
let wbn_nist_inv_applied =
  list_mk_comb(`wbn_loop_invariant`,
    [`pc:num`;`nonce:96 word`;`c:num`;`in_p:int64`;`out_p:int64`;`xi_p:int64`;`ivec_p:int64`;
     `key_p:int64`;`htbl_p:int64`;`stackpointer:int64`;`nblk:num`;`inblock:num->int128`;
     `tag0:int128`;`rk:int128 list`]);;

let wbn_transport_adapter_hyps =
 `word_bytereverse (ctr0:int128) = ctr_block nonce c /\
  (xi:int128) = word_reversefields 8 (tag0:int128) /\
  byteswap128 (h:int128) = ghash_twist (aes256_encrypt (word 0) rk) /\
  (rk:int128 list) = [k0;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11;k12;k13;k14] /\
  (ibytes:byte list) = int128_list_to_bytes (list_of_seq inblock nblk)`;;
let wbn_transport_vars = union wb_front_vars
  [`nonce:96 word`;`c:num`;`inblock:num->int128`;`tag0:int128`;`rk:int128 list`];;
let wbn_transport_sv = `s:armstate`;;

(* ---- WBN_MAIN_LOOP : shared-vocab loop theorem (core form) ---- *)
let wbn_main_loop_nist_goal =
  let ml_body = snd(dest_imp(snd(strip_forall(concl WBN_MAIN_LOOP_raw)))) in
  let ml_pre  = rand(rator(rator ml_body))
  and ml_post = rand(rator ml_body)
  and ml_C    = rand ml_body in
  let pre_conjs  = conjuncts(snd(dest_abs ml_pre))
  and post_conjs = conjuncts(snd(dest_abs ml_post)) in
  let kk = rand(rator (last post_conjs)) in
  let nist_pre = mk_abs(wbn_transport_sv, list_mk_conj
    [el 0 pre_conjs; el 1 pre_conjs;
     mk_comb(mk_comb(wbn_nist_core_applied,`0`),wbn_transport_sv)]) in
  let nist_post = mk_abs(wbn_transport_sv, list_mk_conj
    [el 0 post_conjs; el 1 post_conjs;
     mk_comb(mk_comb(wbn_nist_core_applied,kk),wbn_transport_sv)]) in
  let ens = list_mk_comb(`ensures arm`,[nist_pre; nist_post; ml_C]) in
  let ml_hyps = fst(dest_imp(snd(strip_forall(concl WBN_MAIN_LOOP_raw)))) in
  list_mk_forall(wbn_transport_vars,
    mk_imp(mk_conj(ml_hyps, wbn_transport_adapter_hyps), ens));;

let WBN_MAIN_LOOP = prove(wbn_main_loop_nist_goal,
  let kk = `(nblk - 9) DIV 8` in
  let eqv0 = mk_forall(wbn_transport_sv,
    mk_eq(mk_comb(mk_comb(wbn_core_applied,`0`),wbn_transport_sv),
          mk_comb(mk_comb(wbn_nist_core_applied,`0`),wbn_transport_sv))) in
  let eqvk = mk_forall(wbn_transport_sv,
    mk_eq(mk_comb(mk_comb(wbn_core_applied,kk),wbn_transport_sv),
          mk_comb(mk_comb(wbn_nist_core_applied,kk),wbn_transport_sv))) in
  let CORE_DISCHARGE =
    GEN_TAC THEN MATCH_MP_TAC WBN_INV_CORE_VOCAB THEN
    REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE ASM_ARITH_TAC) in
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `8 * (0 + 1) <= nblk` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `8 * ((nblk - 9) DIV 8 + 1) <= nblk` ASSUME_TAC THENL
   [MP_TAC(SPECL [`nblk - 9`; `8`] DIVISION) THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN eqv0 ASSUME_TAC THENL [CORE_DISCHARGE; ALL_TAC] THEN
  SUBGOAL_THEN eqvk ASSUME_TAC THENL [CORE_DISCHARGE; ALL_TAC] THEN
  PURE_ONCE_REWRITE_TAC[GSYM(ASSUME eqv0); GSYM(ASSUME eqvk)] THEN
  MP_TAC(SPECL wb_front_vars WBN_MAIN_LOOP_raw) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN ACCEPT_TAC]);;

(* ---- WBN_LOOP_INVARIANT_ENTRY : shared-vocab entry theorem (full inv) ---- *)
let wbn_entry_nist_goal =
  let en_body = snd(dest_imp(snd(strip_forall(concl WBN_LOOP_INVARIANT_ENTRY_RAW)))) in
  let en_P    = rand(rator(rator en_body))
  and en_post = rand(rator en_body)
  and en_C    = rand en_body in
  let post_conjs = conjuncts(snd(dest_abs en_post)) in
  let nist_post = mk_abs(wbn_transport_sv, list_mk_conj
    [el 0 post_conjs; el 1 post_conjs;
     mk_comb(mk_comb(wbn_nist_inv_applied,`0`),wbn_transport_sv)]) in
  let ens = list_mk_comb(`ensures arm`,[en_P; nist_post; en_C]) in
  let en_hyps = fst(dest_imp(snd(strip_forall(concl WBN_LOOP_INVARIANT_ENTRY_RAW)))) in
  list_mk_forall(wbn_transport_vars,
    mk_imp(mk_conj(en_hyps, wbn_transport_adapter_hyps), ens));;

let WBN_LOOP_INVARIANT_ENTRY = prove(wbn_entry_nist_goal,
  let eqinv0 = mk_forall(wbn_transport_sv,
    mk_eq(mk_comb(mk_comb(wbn_inv_applied,`0`),wbn_transport_sv),
          mk_comb(mk_comb(wbn_nist_inv_applied,`0`),wbn_transport_sv))) in
  let INV_DISCHARGE0 =
    GEN_TAC THEN MATCH_MP_TAC WBN_LOOP_INV_VOCAB THEN
    REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE ASM_ARITH_TAC) in
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `8 * (0 + 1) <= nblk` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN eqinv0 ASSUME_TAC THENL [INV_DISCHARGE0; ALL_TAC] THEN
  PURE_ONCE_REWRITE_TAC[GSYM(ASSUME eqinv0)] THEN
  MP_TAC(SPECL wb_front_vars WBN_LOOP_INVARIANT_ENTRY_RAW) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN ACCEPT_TAC]);;

(* ========================================================================= *)
(* THE EXPORTED CORE CONTRACT (consolidation; reshape).                         *)
(*                                                                             *)
(* After-prologue core correctness for the whole-blocks decrypt, in the         *)
(* reviewer-facing NIST SP 800-38D vocabulary matching the sibling AES-GCM       *)
(* proofs (the encrypt _GEN and the x4 kernels):                              *)
(*   - GHASH key NAMED as the GCM hash key H = aes256_encrypt (word 0) rk        *)
(*     (= E_K(0^128)).  aes256_encrypt (NOT aes256_cipher) is the house Arm      *)
(*     convention (AES-XTS bottoms out in it); the aes256_encrypt=aes256_cipher  *)
(*     FIPS-197 bridge is a separate upstream deliverable.  TODO: until it       *)
(*     lands, that identification is an argument, not a theorem here.            *)
(*   - NIST nonce NAMED by the hyp word_bytereverse ctr0 = ctr_block nonce c     *)
(*     (every ctr0 admits this, CTR0_AS_CTR_BLOCK), so block j's keystream is    *)
(*     E_K(nonce || (c + j)) -- the big-endian counter form.                     *)
(*   - INPUT abstract as an indexed function inblock : num -> int128, pinned by  *)
(*     the precondition read(bytes128(in_p+16j)) s = inblock j (matching the      *)
(*     sibling proofs' shape) -- no byte-list ibytes in the exported              *)
(*     statement.                                                                 *)
(*   - output POINTWISE over 16-byte blocks as                                    *)
(*       word_xor (aes_ctr_block nonce rk (c + j)) (inblock j)                    *)
(*     the SHARED per-block keystream term (aes_ctr_spec.ml).  CTR mode is its    *)
(*     own inverse, so this is the SAME TERM the encrypt contract exports; only   *)
(*     which side is supplied as inblock differs (ciphertext for decrypt,         *)
(*     plaintext for encrypt).  Manifests that the routine handles ONLY whole     *)
(*     blocks (gcm_dec_pt_bytes' partial-block nfull/tail machinery is dead).     *)
(*   - GHASH over the NIST (big-endian) view of the INPUT blocks                  *)
(*       list_of_seq (\i. word_bytereverse (inblock i)) nblk                      *)
(*     (for DECRYPT, GHASH runs over the ciphertext = the input; word_bytereverse *)
(*     = nist_input_block's role, restated over inblock).                         *)
(* Derived from the H-free byte-list spine WBN_DEC_CORE_BYTELIST by pinning H,    *)
(* instantiating ibytes := int128_list_to_bytes (list_of_seq inblock nblk), and   *)
(* discharging the spine's byte_list_at precondition via WBN_INPUT_ASSEMBLE +     *)
(* weakening the postcond (ENSURES_POSTCONDITION_THM + WBN_OUTPUT_POINTWISE_NONCE *)
(* + GCM_DEC_BLOCKS_FROM_ASSEMBLED + NIST_INPUT_OF_ASSEMBLED).  The proof         *)
(* interior never sees H expanded and no sim is re-run.                          *)
(*                                                                             *)
(* COUNTER GENERALITY (NIST SP 800-38D): c is the FREE absolute entry counter    *)
(* (no hardcoded +2).  The kernel does ld1 {v0.16b},[x16] and increments from    *)
(* whatever ivec holds; it is counter-agnostic, and aws-lc's                     *)
(* CRYPTO_gcm128_decrypt_ctr32 passes the RUNNING ctx->Yi mid-stream, so          *)
(* entry counters != 2 are real.  In SP 800-38D counter 1 is reserved for the     *)
(* tag mask, so the first data block is counter 2 -- c := 2 is exactly that NIST  *)
(* instance of this theorem, one instantiation away (the siblings hardcode +2).   *)
(*                                                                             *)
(* IVEC WRITEBACK: the post carries the advanced                                 *)
(* counter the kernel stores (rev32 v30; str q30,[x16]) at both exits, as          *)
(* read(bytes128 ivec_p) s = word_bytereverse (ctr_block nonce (c+nblk)) -- a       *)
(* fully streaming contract.  The advanced-counter fact (read Q30 = gcm_ctr_raw    *)
(* (word (8*i+13)) ctr0) was threaded from the loop invariant through the front    *)
(* postcond (Q30, s100 EDIT 0), the prepretail seam (M1, s097), the 8 band tails   *)
(* (WB_IVEC_CLOSE_TAC), the recompose spine (wbn_end_post, FULL_r reconcile) and    *)
(* the DISPATCH/wrapper/export layers, bridged to the NIST nonce via               *)
(* GCM_CTR_INC_ITER_CTR_BLOCK + the word_bytereverse ctr0 = ctr_block nonce c hyp.  *)
(*                                                                             *)
(* TODO(H-table provenance): htable_mem_8 states the H-power table layout the    *)
(*   kernel requires (an INPUT) at H = aes256_encrypt (word 0) rk.  Proving       *)
(*   gcm_init_v8 WRITES it is separate upstream work; the                        *)
(*   sibling AES-GCM proofs take the identical table as a precond.               *)
(* ========================================================================= *)

let AESV8_GCM_8X_DEC_256_CORRECT = prove
 (`!pc stackpointer in_p out_p xi_p ivec_p key_p htbl_p nblk inblock rk
    tag0 ctr0 nonce c.
    1 <= nblk /\
    128 * nblk < 2 EXP 62 /\
    val in_p + 16 * nblk < 2 EXP 63 /\
    LENGTH rk = 15 /\
    aligned 16 stackpointer /\
    word_bytereverse ctr0 = ctr_block nonce c /\
    ALLPAIRS nonoverlapping [out_p,16 * nblk; xi_p,16; ivec_p,16]
    [word pc, LENGTH aesv8_gcm_8x_dec_256_wb_mc; in_p,16 * nblk; key_p,240; htbl_p,192; stackpointer,80] /\
    PAIRWISE nonoverlapping [out_p,16 * nblk; xi_p,16; ivec_p,16] /\
    ALL (nonoverlapping (stackpointer,80))
    [word pc, LENGTH aesv8_gcm_8x_dec_256_wb_mc; in_p,16 * nblk; key_p,240; htbl_p,192]
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) aesv8_gcm_8x_dec_256_wb_mc /\
              read PC s = word (pc + 32) /\
              read SP s = stackpointer /\
              C_ARGUMENTS
              [in_p; word (128 * nblk); out_p; xi_p; ivec_p; key_p; htbl_p]
              s /\
              (!j. j < nblk
                   ==> read (memory :> bytes128
                              (word_add in_p (word (16 * j)))) s = inblock j) /\
              read (memory :> bytes128 xi_p) s = word_reversefields 8 tag0 /\
              read (memory :> bytes128 ivec_p) s = ctr0 /\
              wordlist_from_memory (key_p,15) s = rk /\
              htable_mem_8 (ghash_twist (aes256_encrypt (word 0) rk)) htbl_p s)
         (\s. read PC s = word (pc + 4560) /\
              (!j. j < nblk
                   ==> read (memory :> bytes128
                              (word_add out_p (word (16 * j)))) s =
                       word_xor (aes_ctr_block nonce rk (c + j)) (inblock j)) /\
              read (memory :> bytes128 xi_p) s =
              word_reversefields 8
              (nist_ghash (aes256_encrypt (word 0) rk) tag0
              (list_of_seq (\i. word_bytereverse (inblock i)) nblk)) /\
              read (memory :> bytes128 ivec_p) s = word_bytereverse (ctr_block nonce (c + nblk)))
         (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
          MAYCHANGE
          [memory :> bytes (out_p,16 * nblk); memory :> bytes (xi_p,16);
           memory :> bytes (ivec_p,16);
           memory :> bytes (word_add stackpointer (word 64),16)] ,,
          MAYCHANGE
          [Q0; Q1; Q2; Q3; Q4; Q5; Q6; Q7; Q8; Q9; Q10; Q11; Q12; Q13; Q14;
           Q15; Q16; Q17; Q18; Q19; Q20; Q21; Q22; Q23; Q24; Q25; Q26; Q27;
           Q28; Q29; Q30; Q31])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN
  EXISTS_TAC
    `\s. read PC s = word (pc + 4560) /\
         byte_list_at
           (gcm_dec_pt_bytes (16 * nblk)
              (int128_list_to_bytes (list_of_seq inblock nblk)) ctr0 rk) out_p
           (word (16 * nblk)) s /\
         read (memory :> bytes128 xi_p) s =
         word_reversefields 8
         (nist_ghash (aes256_encrypt (word 0) rk) tag0
           (list_of_seq
             (nist_input_block (int128_list_to_bytes (list_of_seq inblock nblk)))
             nblk)) /\
         read (memory :> bytes128 ivec_p) s = gcm_ctr_inc_iter nblk ctr0` THEN
  CONJ_TAC THENL
   [X_GEN_TAC `s:armstate` THEN BETA_TAC THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
      MP_TAC(SPECL [`nblk:num`;
                    `int128_list_to_bytes (list_of_seq (inblock:num->int128) nblk)`;
                    `ctr0:int128`; `rk:int128 list`; `out_p:int64`; `s:armstate`;
                    `nonce:96 word`; `c:num`] WBN_OUTPUT_POINTWISE_NONCE) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o SPEC `j:num`) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN SUBST1_TAC THEN
      ASM_SIMP_TAC[GCM_DEC_BLOCKS_FROM_ASSEMBLED] THEN
      REWRITE_TAC[aes_ctr_block] THEN CONV_TAC WORD_BITWISE_RULE;
      CONJ_TAC THENL
       [REWRITE_TAC[NIST_INPUT_OF_ASSEMBLED];
        (* ivec M2: bridge the spine counter to the NIST nonce||(c+nblk)
           block via GCM_CTR_INC_ITER_CTR_BLOCK + the nonce hypothesis. *)
        MP_TAC(SPECL [`nblk:num`; `nonce:96 word`; `c:num`; `ctr0:int128`]
          GCM_CTR_INC_ITER_CTR_BLOCK) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REFL_TAC]];
    (* the ensures leg: instantiate the byte-list spine at the assembled ibytes,
       discharge its top-level hyps, then bridge its byte_list_at PREcondition to
       our indexed-input precondition via WBN_INPUT_ASSEMBLE. *)
    MP_TAC(INST [`aes256_encrypt (word 0) rk`,`H:int128`;
                 `int128_list_to_bytes (list_of_seq (inblock:num->int128) nblk)`,
                 `ibytes:byte list`]
                (SPEC_ALL WBN_DEC_CORE_BYTELIST)) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[LENGTH_INT128_LIST_TO_BYTES; LENGTH_LIST_OF_SEQ]; ALL_TAC] THEN
    DISCH_THEN(fun sp ->
      MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN
      EXISTS_TAC (rand(rator(rator(concl sp)))) THEN
      CONJ_TAC THENL [ALL_TAC; ACCEPT_TAC sp]) THEN
    X_GEN_TAC `s:armstate` THEN BETA_TAC THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC WBN_INPUT_ASSEMBLE THEN
    ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* THE EXPORTED SUBROUTINE CONTRACT (consolidation;                             *)
(* reshape) -- headline.  The full AAPCS64 wrapper, same reviewer-facing         *)
(* vocabulary as the _CORRECT export above (H pinned, nonce named, ABSTRACT      *)
(* indexed input `inblock`, pointwise aes_ctr_block output, GHASH over           *)
(* word_bytereverse o inblock), for EVERY representable length nblk >= 0         *)
(* (nblk=0: entry cbz taken, returns 0; both the input-read hypothesis and the   *)
(* output pointwise conjunct are vacuous -- no j<0 -- tag unchanged).  Its       *)
(* bit_len = word (128*nblk) makes any invalid bit_len UNREPRESENTABLE (as       *)
(* the encrypt _GEN).  Derived from spine WBN_DEC_SUBROUTINE_BYTELIST like        *)
(* _CORRECT                                                                      *)
(* (INST + WBN_INPUT_ASSEMBLE + WBN_OUTPUT_POINTWISE_NONCE + the assembled        *)
(* identities).  The ivec writeback is now included (see the _CORRECT header).    *)
(* ========================================================================= *)

let AESV8_GCM_8X_DEC_256_SUBROUTINE_CORRECT = prove
 (`!pc stackpointer in_p out_p xi_p ivec_p key_p htbl_p nblk inblock rk
    tag0 ctr0 nonce c returnaddress.
    128 * nblk < 2 EXP 62 /\
    val in_p + 16 * nblk < 2 EXP 63 /\
    LENGTH rk = 15 /\
    aligned 16 stackpointer /\
    word_bytereverse ctr0 = ctr_block nonce c /\
    ALLPAIRS nonoverlapping [out_p,16 * nblk; xi_p,16; ivec_p,16]
    [word pc, LENGTH aesv8_gcm_8x_dec_256_wb_mc; in_p,16 * nblk; key_p,240; htbl_p,192;
     word_sub stackpointer (word 80),80] /\
    PAIRWISE nonoverlapping [out_p,16 * nblk; xi_p,16; ivec_p,16] /\
    ALL (nonoverlapping (word_sub stackpointer (word 80),80))
    [word pc, LENGTH aesv8_gcm_8x_dec_256_wb_mc; in_p,16 * nblk; key_p,240; htbl_p,192]
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) aesv8_gcm_8x_dec_256_wb_mc /\
              read PC s = word pc /\
              read SP s = stackpointer /\
              read X30 s = returnaddress /\
              C_ARGUMENTS
              [in_p; word (128 * nblk); out_p; xi_p; ivec_p; key_p; htbl_p]
              s /\
              (!j. j < nblk
                   ==> read (memory :> bytes128
                              (word_add in_p (word (16 * j)))) s = inblock j) /\
              read (memory :> bytes128 xi_p) s = word_reversefields 8 tag0 /\
              read (memory :> bytes128 ivec_p) s = ctr0 /\
              wordlist_from_memory (key_p,15) s = rk /\
              htable_mem_8 (ghash_twist (aes256_encrypt (word 0) rk)) htbl_p s)
         (\s. read PC s = returnaddress /\
              (!j. j < nblk
                   ==> read (memory :> bytes128
                              (word_add out_p (word (16 * j)))) s =
                       word_xor (aes_ctr_block nonce rk (c + j)) (inblock j)) /\
              read (memory :> bytes128 xi_p) s =
              word_reversefields 8
              (nist_ghash (aes256_encrypt (word 0) rk) tag0
              (list_of_seq (\i. word_bytereverse (inblock i)) nblk)) /\
              read (memory :> bytes128 ivec_p) s = word_bytereverse (ctr_block nonce (c + nblk)))
         (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
          MAYCHANGE
          [memory :> bytes (out_p,16 * nblk); memory :> bytes (xi_p,16);
           memory :> bytes (ivec_p,16);
           memory :> bytes (word_sub stackpointer (word 80),80)])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN
  EXISTS_TAC
    `\s. read PC s = returnaddress /\
         byte_list_at
           (gcm_dec_pt_bytes (16 * nblk)
              (int128_list_to_bytes (list_of_seq inblock nblk)) ctr0 rk) out_p
           (word (16 * nblk)) s /\
         read (memory :> bytes128 xi_p) s =
         word_reversefields 8
         (nist_ghash (aes256_encrypt (word 0) rk) tag0
           (list_of_seq
             (nist_input_block (int128_list_to_bytes (list_of_seq inblock nblk)))
             nblk)) /\
         read (memory :> bytes128 ivec_p) s = gcm_ctr_inc_iter nblk ctr0` THEN
  CONJ_TAC THENL
   [X_GEN_TAC `s:armstate` THEN BETA_TAC THEN STRIP_TAC THEN
    CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    CONJ_TAC THENL
     [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
      MP_TAC(SPECL [`nblk:num`;
                    `int128_list_to_bytes (list_of_seq (inblock:num->int128) nblk)`;
                    `ctr0:int128`; `rk:int128 list`; `out_p:int64`; `s:armstate`;
                    `nonce:96 word`; `c:num`] WBN_OUTPUT_POINTWISE_NONCE) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o SPEC `j:num`) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN SUBST1_TAC THEN
      ASM_SIMP_TAC[GCM_DEC_BLOCKS_FROM_ASSEMBLED] THEN
      REWRITE_TAC[aes_ctr_block] THEN CONV_TAC WORD_BITWISE_RULE;
      CONJ_TAC THENL
       [ASM_REWRITE_TAC[NIST_INPUT_OF_ASSEMBLED];
        (* ivec M2: bridge spine counter -> NIST nonce||(c+nblk).               *)
        MP_TAC(SPECL [`nblk:num`; `nonce:96 word`; `c:num`; `ctr0:int128`]
          GCM_CTR_INC_ITER_CTR_BLOCK) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REFL_TAC]];
    (* the ensures leg: instantiate the byte-list subroutine spine at the assembled
       ibytes, discharge its top-level hyps, then bridge its byte_list_at
       PREcondition to our indexed-input precondition via WBN_INPUT_ASSEMBLE. *)
    MP_TAC(INST [`aes256_encrypt (word 0) rk`,`H:int128`;
                 `int128_list_to_bytes (list_of_seq (inblock:num->int128) nblk)`,
                 `ibytes:byte list`]
                (SPEC_ALL WBN_DEC_SUBROUTINE_BYTELIST)) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[LENGTH_INT128_LIST_TO_BYTES; LENGTH_LIST_OF_SEQ]; ALL_TAC] THEN
    DISCH_THEN(fun sp ->
      MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN
      EXISTS_TAC (rand(rator(rator(concl sp)))) THEN
      CONJ_TAC THENL [ALL_TAC; ACCEPT_TAC sp]) THEN
    X_GEN_TAC `s:armstate` THEN BETA_TAC THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC WBN_INPUT_ASSEMBLE THEN
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* THE WHOLE-FUNCTION CONTRACT (headline result).                              *)
(*                                                                             *)
(* AESV8_GCM_8X_DEC_256_SUBROUTINE_CORRECT (above) IS the whole-function     *)
(* AAPCS64 subroutine contract; AESV8_GCM_8X_DEC_256_CORRECT is the           *)
(* after-prologue core it wraps.  These are the TWO exported CORRECT theorems    *)
(* (consolidated five near-identical variants into these two --                  *)
(* H pinned, nonce named, output pointwise -- so a reviewer sees ONE obvious     *)
(* contract each).  See their headers above for the full spec.                  *)
(*                                                                             *)
(* SECONDARY (entry-guard safety): AESV8_GCM_8X_DEC_256_GUARD                 *)
(* (the <=8-block chain) is NOT part of the headline contract              *)
(* -- it states something the CORRECT theorems cannot, over an ARBITRARY C        *)
(* bit_len (not the well-typed word (128*nblk)): for a bit_len that is set but    *)
(* not a whole number of 128-bit blocks (~(val bit_len = 0) /\                    *)
(* ~(val bit_len MOD 128 = 0)), the guard branch (tst x1,#0x7f; b.ne) rejects,    *)
(* returns 0 in X0, and touches no memory.  This is the safety argument that      *)
(* licensed deleting the partial-block masking (which had a 16-byte output        *)
(* over-read); it is retained for that provenance but is a secondary property,    *)
(* not the cryptographic spec.  (It mirrors the nblk<=8 DISPATCH+GUARD pairing    *)
(* in the <=8-block chain, where GUARD played the same secondary role.)              *)
(*                                                                             *)
(* Soundness gate: the exported theorems (SUBROUTINE_CORRECT for all nblk>=0,     *)
(* CORRECT for all nblk>=1, GUARD) plus the internal byte-list spines are         *)
(* hyps=0, and the file introduces NO new axiom -- the Q19/GHASH identity that    *)
(* was formerly scoped behind a CHEAT is closed (the R1' route).                 *)
(* ------------------------------------------------------------------------- *)

let () =
  let whole_fn = [AESV8_GCM_8X_DEC_256_CORRECT;
                  AESV8_GCM_8X_DEC_256_SUBROUTINE_CORRECT;
                  AESV8_GCM_8X_DEC_256_GUARD;
                  WBN_DEC_CORE_BYTELIST; WBN_DEC_SUBROUTINE_BYTELIST] in
  (* Drift gate, two layers: (1) the byte-list SPINES are aconv-anchored to the
     FROZEN _DISPATCH by term surgery; (2) the two
     EXPORTED theorems are aconv-anchored to the spines via `to_exported` (pin
     H := aes256_encrypt (word 0) rk; drop the ibytes var + its LENGTH hyp and
     add the abstract inblock var; add the nonce hyp + nonce/c vars; swap the
     input byte_list_at PREcondition for the indexed-read hyp; swap the byte-list
     data POSTcondition for the pointwise aes_ctr_block form; rewrite the GHASH
     input list to word_bytereverse o inblock).  Both anchors are
     built from proved theorems (spine + WBN_OUTPUT_POINTWISE_NONCE +
     WBN_INPUT_ASSEMBLE + NIST_INPUT_OF_ASSEMBLED), so no hand-typed literal can
     drift undetected. *)
  (* (1a) core spine anchor: the DISPATCH ensures-body, `nblk<=8` -> `1<=nblk` +
     the two size bounds. *)
  let core_bytelist_anchor =
    let dvars, dbody = strip_forall (concl AESV8_GCM_8X_DEC_256_DISPATCH) in
    let dhyps, dens = dest_imp dbody in
    let hyps0 = filter (fun c -> c <> `nblk <= 8`) (conjuncts dhyps) in
    let hyps' = `1 <= nblk` :: `128 * nblk < 2 EXP 62` ::
                `val (in_p:int64) + 16 * nblk < 2 EXP 63` ::
                (filter (fun c -> c <> `1 <= nblk`) hyps0) in
    list_mk_forall(dvars, mk_imp(list_mk_conj hyps', dens)) in
  (* (1b) subroutine spine anchor, from the core anchor: SP shifted to word_sub
     stackpointer (word 80), entry PC pc+32 -> pc, exit pc+4552 -> returnaddress,
     +read X30 s = returnaddress, +returnaddress var, `1<=nblk` dropped (nblk=0
     folded in), `,, MAYCHANGE [Q0..Q31]` dropped (subsumed by the ABI frame). *)
  let subr_bytelist_anchor =
    let cvars, cbody = strip_forall core_bytelist_anchor in
    let base = subst
      [`word pc:int64`,`word (pc + 32):int64`;
       `returnaddress:int64`,`word (pc + 4560):int64`;
       `word_sub stackpointer (word 80):int64,80`,`stackpointer:int64,80`;
       `word_sub stackpointer (word 80):int64,80`,
       `word_add stackpointer (word 64):int64,16`]
      cbody in
    let chyps, cens = dest_imp base in
    let eop, eargs = strip_comb cens in
    let sv, preb = dest_abs (el 1 eargs) and frame = el 3 eargs in
    let cs = conjuncts preb in
    let spc = find (fun c -> can (find_term (fun x -> x = `SP`)) c) cs in
    let x30c = subst [`X30`,`SP`; `returnaddress:int64`,`stackpointer:int64`] spc in
    let cs' = itlist (fun c acc -> if c = spc then c :: x30c :: acc else c :: acc)
                     cs [] in
    let pre' = mk_abs(sv, list_mk_conj cs') in
    let frame' = mk_comb(mk_comb(rator(rator frame), rand(rator frame)),
                         rand(rator(rand frame))) in
    let cens' = list_mk_comb(eop, [el 0 eargs; pre'; el 2 eargs; frame']) in
    let chyps' = list_mk_conj (filter (fun c -> c <> `1 <= nblk`)
                                      (conjuncts chyps)) in
    list_mk_forall(cvars @ [`returnaddress:int64`], mk_imp(chyps', cens')) in
  (* (2) the presentation transform to the exported statement.  All
     four presentation pieces are LIFTED from proved theorems so their typing is
     guaranteed to match the exported theorems' by construction:
       - nonce_hyp_tm  (word_bytereverse ctr0 = ctr_block nonce c)  from the
         nonce hypothesis of WBN_OUTPUT_POINTWISE_NONCE;
       - input_hyp_tm  (the indexed input-read hypothesis) from WBN_INPUT_ASSEMBLE;
       - out_data_tm   (the pointwise aes_ctr_block output conjunct) from the
         conclusion of WBN_OUTPUT_POINTWISE_NONCE's own consumer -- rebuilt from
         its keystream via aes_ctr_block; and
       - ghash_inner_tm (list_of_seq (\i. word_bytereverse (inblock i)) nblk) from
         the RHS of NIST_INPUT_OF_ASSEMBLED.
     The transform: pin H; DROP the LENGTH ibytes hyp and the ibytes var, ADD the
     inblock var (in ibytes' slot) + nonce/c vars; ADD the nonce hyp after aligned;
     SWAP the input byte_list_at PREcondition conjunct for input_hyp_tm; SWAP the
     byte-list data POSTcondition conjunct (index 1) for out_data_tm; and rewrite
     the GHASH input list from nist_input_block(assembled ibytes) to the clean
     word_bytereverse o inblock form.  ibytes := int128_list_to_bytes(list_of_seq
     inblock nblk) is the witness used in the actual derivation. *)
  let nonce_hyp_tm =
    el 2 (conjuncts (lhand (snd (strip_forall
             (concl WBN_OUTPUT_POINTWISE_NONCE))))) in
  let input_hyp_tm =
    el 1 (conjuncts (lhand (snd (strip_forall (concl WBN_INPUT_ASSEMBLE))))) in
  (* out_data_tm: the pointwise output conjunct in the exported keystream-first
     form word_xor (aes_ctr_block nonce rk (c+j)) (inblock j).  Built from the
     WBN_OUTPUT_POINTWISE_NONCE consumer shape by GSYM-ing its keystream to
     aes_ctr_block and commuting the xor; here we lift the literal (its constants
     -- aes_ctr_block, inblock, etc. -- are all proved/defined so typing is fixed). *)
  let out_data_tm =
    `!j. j < nblk
         ==> read (memory :> bytes128 (word_add out_p (word (16 * j)))) s =
             word_xor (aes_ctr_block nonce rk (c + j)) (inblock j)` in
  (* the clean GHASH input list list_of_seq (\i. word_bytereverse (inblock i)) nblk
     = the RHS of NIST_INPUT_OF_ASSEMBLED (whole application, not just the fn). *)
  let ghash_inner_tm =
    rhs(snd(strip_forall(concl NIST_INPUT_OF_ASSEMBLED))) in
  (* ivec M2: the spine post carries the counter write-back in the
     spine form gcm_ctr_inc_iter nblk ctr0; the exported statement re-presents it
     as the NIST nonce||(c+nblk) block (via GCM_CTR_INC_ITER_CTR_BLOCK + the nonce
     hyp in the proof).  Swap the spine ivec conjunct for the exported one. *)
  let ivec_from = `read (memory :> bytes128 ivec_p) s = gcm_ctr_inc_iter nblk ctr0` in
  let ivec_to =
    `read (memory :> bytes128 ivec_p) s = word_bytereverse (ctr_block nonce (c + nblk))` in
  let to_exported anchor =
    let vars, body = strip_forall anchor in
    let body = subst [`aes256_encrypt (word 0) rk`,`H:int128`] body in
    let hyps, ens = dest_imp body in
    let hcs = conjuncts hyps in
    (* drop LENGTH ibytes = 16*nblk (ibytes leaves the exported statement) *)
    let hcs = filter (fun c ->
      not (try is_eq c && fst(dest_const(fst(strip_comb(lhand c)))) = "LENGTH" &&
                rand(lhand c) = `ibytes:byte list` with Failure _ -> false)) hcs in
    let aligned_tm =
      find (fun c -> try fst(dest_const(fst(strip_comb c))) = "aligned"
                     with Failure _ -> false) hcs in
    let hyps' = itlist (fun cj acc -> if cj = aligned_tm
                                      then cj :: nonce_hyp_tm :: acc
                                      else cj :: acc) hcs [] in
    let eop, eargs = strip_comb ens in
    (* precondition: swap the input byte_list_at ibytes conjunct for the reads *)
    let pv, pbody = dest_abs (el 1 eargs) in
    let byte_in_tm = find (fun c -> try fst(dest_const(fst(strip_comb c))) =
                             "byte_list_at" with Failure _ -> false) (conjuncts pbody) in
    let pcs' = map (fun c -> if c = byte_in_tm then input_hyp_tm else c)
                   (conjuncts pbody) in
    let pre' = mk_abs(pv, list_mk_conj pcs') in
    (* postcondition: data conjunct -> out_data_tm; GHASH inner -> clean form *)
    let sv, qbody = dest_abs (el 2 eargs) in
    let ghash_from = `list_of_seq (nist_input_block (ibytes:byte list)) nblk` in
    (* the spine/exported ivec conjuncts, with the post's actual bound var. *)
    let ivec_from' = subst [sv,`s:armstate`] ivec_from in
    let ivec_to' = subst [sv,`s:armstate`] ivec_to in
    let qcs' = mapi (fun i cj -> if i = 1 then out_data_tm
                                 else if cj = ivec_from' then ivec_to'
                                 else subst [ghash_inner_tm, ghash_from] cj)
                    (conjuncts qbody) in
    let post' = mk_abs(sv, list_mk_conj qcs') in
    let ens' = list_mk_comb(eop, [el 0 eargs; pre'; post'; el 3 eargs]) in
    (* ibytes var -> inblock var in place; H dropped; nonce/c before returnaddress *)
    let vars0 = map (fun v -> if v = `ibytes:byte list` then `inblock:num->int128` else v)
                    (filter (fun v -> v <> `H:int128`) vars) in
    let vars' =
      if mem `returnaddress:int64` vars0
      then filter (fun v -> v <> `returnaddress:int64`) vars0 @
           [`nonce:96 word`; `c:num`; `returnaddress:int64`]
      else vars0 @ [`nonce:96 word`; `c:num`] in
    list_mk_forall(vars', mk_imp(list_mk_conj hyps', ens')) in
  if not (aconv (concl WBN_DEC_CORE_BYTELIST) core_bytelist_anchor) then
    failwith "WB dec core spine: literal drifted from the DISPATCH contract (aconv)"
  else if not (aconv (concl WBN_DEC_SUBROUTINE_BYTELIST) subr_bytelist_anchor) then
    failwith "WB dec subroutine spine: literal drifted from the core spine (aconv)"
  else if not (aconv (concl AESV8_GCM_8X_DEC_256_CORRECT)
                     (to_exported core_bytelist_anchor)) then
    failwith "WB dec _CORRECT: literal drifted from the core spine (aconv)"
  else if not (aconv (concl AESV8_GCM_8X_DEC_256_SUBROUTINE_CORRECT)
                     (to_exported subr_bytelist_anchor)) then
    failwith "WB dec _SUBROUTINE_CORRECT: literal drifted from the subroutine spine (aconv)"
  else if exists (fun th -> hyp th <> []) whole_fn then
    failwith "WB dec whole-function theorems: unexpected hypotheses"
  else if List.length (axioms()) <> 3 then
    failwith "WB dec whole-function: unexpected axiom count (new_axiom introduced?)"
  else Format.print_string
    ("WB dec whole-function: CORRECT + SUBROUTINE_CORRECT (H pinned, nonce named, "^
     "indexed inblock, pointwise aes_ctr_block; aconv spines) + spines (aconv "^
     "DISPATCH) + GUARD hyps=0, axioms=3\n");;

